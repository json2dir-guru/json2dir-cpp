// json2dir: create the directory tree a JSON document describes, in the current directory.
// Implements RFC J2D-1 (https://github.com/kitsunoff/awesome-json2dir/blob/main/spec/rfc-json2dir.md).
// C++20, standard library + POSIX only: hand-written UTF-8 check and JSON parser.
#include <algorithm>
#include <cerrno>
#include <cstring>
#include <filesystem>
#include <iostream>
#include <iterator>
#include <stdexcept>
#include <string>
#include <variant>
#include <vector>

#include <fcntl.h>
#include <sys/stat.h>
#include <unistd.h>

namespace fs = std::filesystem;

struct Error : std::runtime_error {
    using std::runtime_error::runtime_error;
};

struct Member;
struct Special {  // ["link", target] or ["script", content]
    bool link;
    std::string payload;
};
using Object = std::vector<Member>;
struct Node {
    std::variant<std::string, Special, Object> v;
};
struct Member {
    std::string name;
    Node value;
};

// §3: strict UTF-8 (no overlongs, no surrogates, nothing above U+10FFFF).
static bool valid_utf8(const std::string& s) {
    size_t i = 0, n = s.size();
    while (i < n) {
        unsigned char c = s[i];
        int len;
        unsigned cp;
        if (c < 0x80) { i++; continue; }
        else if ((c & 0xE0) == 0xC0) { len = 2; cp = c & 0x1F; }
        else if ((c & 0xF0) == 0xE0) { len = 3; cp = c & 0x0F; }
        else if ((c & 0xF8) == 0xF0) { len = 4; cp = c & 0x07; }
        else return false;
        if (i + len > n) return false;
        for (int k = 1; k < len; k++) {
            unsigned char d = s[i + k];
            if ((d & 0xC0) != 0x80) return false;
            cp = (cp << 6) | (d & 0x3F);
        }
        static const unsigned min[] = {0, 0, 0x80, 0x800, 0x10000};
        if (cp < min[len] || cp > 0x10FFFF || (cp >= 0xD800 && cp <= 0xDFFF)) return false;
        i += len;
    }
    return true;
}

static void put_utf8(std::string& out, unsigned cp) {
    if (cp < 0x80) out += char(cp);
    else if (cp < 0x800) { out += char(0xC0 | cp >> 6); out += char(0x80 | (cp & 0x3F)); }
    else if (cp < 0x10000) {
        out += char(0xE0 | cp >> 12); out += char(0x80 | ((cp >> 6) & 0x3F)); out += char(0x80 | (cp & 0x3F));
    } else {
        out += char(0xF0 | cp >> 18); out += char(0x80 | ((cp >> 12) & 0x3F));
        out += char(0x80 | ((cp >> 6) & 0x3F)); out += char(0x80 | (cp & 0x3F));
    }
}

// Strict JSON parser that also validates the json2dir scheme (§4) while it builds the tree.
class Parser {
    const std::string& s;
    size_t i = 0;

    [[noreturn]] void fail(const std::string& msg) { throw Error(msg + " at byte " + std::to_string(i)); }
    void ws() { while (i < s.size() && (s[i] == ' ' || s[i] == '\t' || s[i] == '\n' || s[i] == '\r')) i++; }
    char peek() { return i < s.size() ? s[i] : '\0'; }
    void expect(char c) {
        if (peek() != c) fail(std::string("expected '") + c + "'");
        i++;
    }

    unsigned hex4() {
        if (i + 4 > s.size()) fail("truncated \\u escape");
        unsigned v = 0;
        for (int k = 0; k < 4; k++) {
            char c = s[i++];
            v <<= 4;
            if (c >= '0' && c <= '9') v |= c - '0';
            else if (c >= 'a' && c <= 'f') v |= c - 'a' + 10;
            else if (c >= 'A' && c <= 'F') v |= c - 'A' + 10;
            else fail("bad \\u escape");
        }
        return v;
    }

    std::string string() {
        expect('"');
        std::string out;
        for (;;) {
            if (i >= s.size()) fail("unterminated string");
            unsigned char c = s[i++];
            if (c == '"') return out;
            if (c < 0x20) fail("control character in string");
            if (c != '\\') { out += char(c); continue; }
            if (i >= s.size()) fail("unterminated string");
            char e = s[i++];
            switch (e) {
                case '"': out += '"'; break;
                case '\\': out += '\\'; break;
                case '/': out += '/'; break;
                case 'b': out += '\b'; break;
                case 'f': out += '\f'; break;
                case 'n': out += '\n'; break;
                case 'r': out += '\r'; break;
                case 't': out += '\t'; break;
                case 'u': {
                    unsigned cp = hex4();
                    if (cp >= 0xDC00 && cp <= 0xDFFF) fail("unpaired surrogate");
                    if (cp >= 0xD800 && cp <= 0xDBFF) {
                        if (i + 2 > s.size() || s[i] != '\\' || s[i + 1] != 'u') fail("unpaired surrogate");
                        i += 2;
                        unsigned lo = hex4();
                        if (lo < 0xDC00 || lo > 0xDFFF) fail("unpaired surrogate");
                        cp = 0x10000 + ((cp - 0xD800) << 10) + (lo - 0xDC00);
                    }
                    put_utf8(out, cp);
                    break;
                }
                default: fail("bad escape");
            }
        }
    }

    Object object(int depth) {
        if (depth > 1000) fail("document nested too deeply");
        expect('{');
        Object obj;
        ws();
        if (peek() == '}') { i++; return obj; }
        for (;;) {
            ws();
            if (peek() != '"') fail("expected a member name");
            std::string name = string();
            if (name.empty() || name == "." || name == ".." || name.find('/') != std::string::npos ||
                name.find('\0') != std::string::npos)
                fail("invalid name");
            ws();
            expect(':');
            ws();
            Node value = this->value(depth);
            // §4.2: duplicate names - the last occurrence wins.
            auto it = std::find_if(obj.begin(), obj.end(), [&](const Member& m) { return m.name == name; });
            if (it != obj.end()) it->value = std::move(value);
            else obj.push_back({std::move(name), std::move(value)});
            ws();
            if (peek() == ',') { i++; continue; }
            expect('}');
            return obj;
        }
    }

    Special array() {
        expect('[');
        std::vector<std::string> items;
        ws();
        if (peek() != ']') {
            for (;;) {
                ws();
                if (peek() != '"') fail("an array must be [\"link\", target] or [\"script\", content]");
                items.push_back(string());
                ws();
                if (peek() == ',') { i++; continue; }
                break;
            }
        }
        expect(']');
        if (items.size() != 2 || (items[0] != "link" && items[0] != "script"))
            fail("an array must be [\"link\", target] or [\"script\", content]");
        bool link = items[0] == "link";
        if (link && items[1].find('\0') != std::string::npos) fail("a link target cannot contain NUL");
        return {link, std::move(items[1])};
    }

    Node value(int depth) {
        char c = peek();
        if (c == '{') return {object(depth + 1)};
        if (c == '[') return {array()};
        if (c == '"') return {string()};
        fail("numbers, true, false and null are not allowed");
    }

public:
    explicit Parser(const std::string& text) : s(text) {}

    Object document() {
        if (s.compare(0, 3, "\xEF\xBB\xBF") == 0) i = 3;  // §3: a leading BOM may be ignored
        ws();
        if (peek() != '{') fail("the root of the document must be an object");
        Object root = object(0);
        ws();
        if (i != s.size()) fail("trailing data after the JSON value");
        return root;
    }
};

[[noreturn]] static void sys_fail(const std::string& what) {
    throw Error(what + ": " + std::strerror(errno));
}

static void write_file(const fs::path& p, const std::string& content, bool executable) {
    // O_EXCL | O_NOFOLLOW: never writes through an entry that appeared after it was cleared.
    int fd = ::open(p.c_str(), O_WRONLY | O_CREAT | O_EXCL | O_NOFOLLOW | O_CLOEXEC, 0666);
    if (fd < 0) sys_fail(p.string());
    size_t off = 0;
    while (off < content.size()) {
        ssize_t w = ::write(fd, content.data() + off, content.size() - off);
        if (w < 0) {
            if (errno == EINTR) continue;
            int e = errno;
            ::close(fd);
            errno = e;
            sys_fail(p.string());
        }
        off += size_t(w);
    }
    if (executable) {
        struct stat st;
        if (::fstat(fd, &st) != 0 || ::fchmod(fd, (st.st_mode & 07777) | 0111) != 0) {
            int e = errno;
            ::close(fd);
            errno = e;
            sys_fail(p.string());
        }
    }
    if (::close(fd) != 0) sys_fail(p.string());
}

static void build_tree(const fs::path& dir, Object& tree) {
    // Ascending order of the UTF-8 bytes of the names, like the reference.
    std::sort(tree.begin(), tree.end(), [](const Member& a, const Member& b) { return a.name < b.name; });
    for (auto& m : tree) {
        fs::path p = dir / m.name;
        std::error_code ec;
        fs::file_status st = fs::symlink_status(p, ec);  // never follows a link
        if (ec && st.type() != fs::file_type::not_found) throw Error(p.string() + ": " + ec.message());
        bool exists = st.type() != fs::file_type::not_found;
        bool is_dir = st.type() == fs::file_type::directory;

        if (auto* obj = std::get_if<Object>(&m.value.v)) {
            if (!is_dir) {
                if (exists) fs::remove(p);  // a file or a symlink itself, never its target
                fs::create_directory(p);
            }
            build_tree(p, *obj);
            continue;
        }
        // §5.4: a directory in the way of a non-object is an error; §5.2: anything else is replaced.
        if (is_dir) throw Error(p.string() + ": a directory is in the way");
        if (exists) fs::remove(p);
        if (auto* str = std::get_if<std::string>(&m.value.v)) {
            write_file(p, *str, false);
        } else {
            auto& sp = std::get<Special>(m.value.v);
            if (sp.link) fs::create_symlink(sp.payload, p);
            else write_file(p, sp.payload, true);
        }
    }
}

int main(int argc, char**) {
    if (argc > 1) {
        std::cerr << "usage: json2dir < document.json\n";
        return 2;
    }
    try {
        std::string input((std::istreambuf_iterator<char>(std::cin)), std::istreambuf_iterator<char>());
        if (!valid_utf8(input)) throw Error("input is not valid UTF-8");
        Object root = Parser(input).document();  // parses and validates everything before writing
        build_tree(".", root);
        return 0;
    } catch (const std::exception& e) {
        std::cerr << "json2dir: " << e.what() << "\n";
        return 1;
    }
}
