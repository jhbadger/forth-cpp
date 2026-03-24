#include <algorithm>
#include <cassert>
#include <cstring>
#include <fstream>
#include <functional>
#include <iostream>
#include <sstream>
#include <stdexcept>
#include <string>
#include <sys/wait.h>
#include <termios.h>
#include <unistd.h>
#include <unordered_map>
#include <vector>

#ifdef USE_READLINE
#include <readline/history.h>
#include <readline/readline.h>
#endif

// - Instruction --------------------------------------------------------------
struct Ins {
  std::string op;
  int ival = 0;
  std::string sval;
  std::vector<std::string> names; // for locals-enter
};

static Ins make(std::string op) {
  Ins i;
  i.op = op;
  return i;
}
static Ins make(std::string op, int v) {
  Ins i;
  i.op = op;
  i.ival = v;
  return i;
}
static Ins make(std::string op, std::string s) {
  Ins i;
  i.op = op;
  i.sval = s;
  return i;
}
static Ins make(std::string op, int v, std::string s) {
  Ins i;
  i.op = op;
  i.ival = v;
  i.sval = s;
  return i;
}

// -- Dict entry ---------------------------------------------------------------
struct Entry {
  enum Kind { PRIM, WORD, DEFINING, CREATE } kind;
  std::function<void()> prim;
  std::vector<Ins> code;      // init code (WORD/DEFINING)
  std::vector<Ins> does_code; // DEFINING does> / CREATE body
  int body_addr = 0;          // CREATE
  bool is_immediate = false;
  int id = -1; // stable execution token (assigned at creation)
};

// -- Forth interpreter --------------------------------------------------------
class Forth {
public:
  int base_addr = 0;
  int state_addr;

  Forth() {
    // heap[0..3]  = BASE  (int, default 10)
    // heap[4..7]  = STATE (int, default 0)
    heap.resize(2 * cell, 0);
    int v = 10;
    memcpy(&heap[0], &v, cell);
    base_addr = 0;
    state_addr = cell;
  }

  void repl(int argc, char *argv[]);

private:
  static const int cell = sizeof(int);

  std::vector<int> stack;
  std::vector<int> rstack;
  std::vector<std::string> locals;
  std::vector<std::vector<int>> leave_stack;

  std::unordered_map<std::string, Entry> dict;

  // xt system: each Entry gets a unique integer id at creation.
  // id_to_name lets execute/compile, go from id back to the dict key.
  int next_id = 0;
  std::unordered_map<int, std::string> id_to_name;

  std::vector<std::string> string_table;
  std::string last_word;
  std::string current;
  std::vector<Ins> prog;
  std::vector<int> cstack;
  int does_pos = -1;

  std::vector<uint8_t> heap;
  std::unordered_map<std::string, std::string> help_db;

  // Locals frames live on a separate typed stack to keep rstack simple
  std::vector<std::vector<int>> lframes;

  // -- heap helpers ----------------------------------------------------------
  int heap_get(int addr) const {
    if (addr < 0 || addr + cell > (int)heap.size())
      throw std::runtime_error("heap_get: invalid address " +
                               std::to_string(addr));
    int v;
    memcpy(&v, &heap[addr], cell);
    return v;
  }
  void heap_set(int addr, int v) {
    if (addr + cell > (int)heap.size())
      heap.resize(addr + cell, 0);
    memcpy(&heap[addr], &v, cell);
  }
  int get_base() const {
    int v;
    memcpy(&v, &heap[base_addr], cell);
    return v;
  }
  int get_state() const {
    int v;
    memcpy(&v, &heap[state_addr], cell);
    return v;
  }
  void set_state(int v) { memcpy(&heap[state_addr], &v, cell); }

  // -- stack helpers ---------------------------------------------------------
  int pop() {
    if (stack.empty())
      throw std::runtime_error("Stack underflow");
    int v = stack.back();
    stack.pop_back();
    return v;
  }
  void push(int v) { stack.push_back(v); }

  int rpop() {
    if (rstack.empty())
      throw std::runtime_error("Return stack underflow");
    int v = rstack.back();
    rstack.pop_back();
    return v;
  }
  void rpush(int v) { rstack.push_back(v); }

  void emit_ins(Ins ins) { prog.push_back(ins); }

  // -- dict helpers ----------------------------------------------------------
  // Register a new entry and assign it a stable xt id.
  void register_entry(const std::string &name, Entry e) {
    e.id = next_id++;
    id_to_name[e.id] = name;
    dict[name] = std::move(e);
  }

  // Look up name by xt id.
  const std::string &xt_to_name(int id) const {
    auto it = id_to_name.find(id);
    if (it == id_to_name.end())
      throw std::runtime_error("execute: invalid execution token " +
                               std::to_string(id));
    return it->second;
  }

  // Get the xt (id) for a named word, registering it if needed.
  // (Entries created before the xt system was in place — e.g. via
  //  direct dict[] assignment — might have id == -1; this fixes them up.)
  int name_to_xt(const std::string &name) {
    auto it = dict.find(name);
    if (it == dict.end())
      throw std::runtime_error("name_to_xt: unknown word: " + name);
    if (it->second.id == -1) {
      it->second.id = next_id++;
      id_to_name[it->second.id] = name;
    }
    return it->second.id;
  }

  // -- number helpers --------------------------------------------------------
  std::string format_int(int n, int base) {
    if (n == 0)
      return "0";
    const char *digits = "0123456789abcdef";
    bool neg = n < 0;
    unsigned int u = neg ? (unsigned int)(-(n + 1)) + 1u : (unsigned int)n;
    std::string result;
    while (u > 0) {
      result = digits[u % base] + result;
      u /= base;
    }
    return neg ? "-" + result : result;
  }

  std::pair<bool, int> try_parse(const std::string &t) {
    int base = get_base();
    bool neg = !t.empty() && t[0] == '-';
    std::string s = neg ? t.substr(1) : t;
    if (s.empty())
      return {false, 0};
    int n = 0;
    for (char c : s) {
      const char *p = strchr("0123456789abcdef", std::tolower(c));
      if (!p)
        return {false, 0};
      int d = (int)(p - "0123456789abcdef");
      if (d >= base)
        return {false, 0};
      n = n * base + d;
    }
    return {true, neg ? -n : n};
  }

  void edit_file(std::string filename) {
    const char *editor = std::getenv("EDITOR");
    if (!editor)
      editor = "vi";
    pid_t pid = fork();
    if (pid == 0) {
      execlp(editor, editor, filename.c_str(), nullptr);
      _exit(1);
    } else if (pid > 0) {
      waitpid(pid, nullptr, 0);
    }
  }

  void load_help(const std::string &filename) {
    std::ifstream f(filename);
    if (!f) {
      std::cout << "Warning: could not open " << filename << "\n";
      return;
    }
    std::string line, current_word, current_body;
    auto flush = [&] {
      if (!current_word.empty())
        help_db[current_word] = current_body;
    };
    while (std::getline(f, line)) {
      if (trim(line).empty()) {
        flush();
        current_word.clear();
        current_body.clear();
        continue;
      }
      if (line[0] != ' ' && line[0] != '\t') {
        flush();
        current_word = lower(trim(line));
        current_body.clear();
      } else {
        current_body += trim(line) + "\n";
      }
    }
    flush();
  }

  void load_file(const std::string &filename) {
    std::ifstream f(filename);
    if (!f) {
      std::cout << "Cannot open " << filename << "\n";
      return;
    }
    std::string line, accumulated;
    while (std::getline(f, line)) {
      line = trim(line);
      if (line.empty() || (line.size() > 1 && line[0] == '#' && line[1] == '!'))
        continue;
      accumulated += (accumulated.empty() ? "" : " ") + line;
      int opens = 0;
      for (char c : accumulated)
        if (c == '"')
          opens++;
      if (opens % 2 == 0) {
        process(split(accumulated));
        accumulated.clear();
      }
    }
    if (!accumulated.empty())
      process(split(accumulated));
  }

  static std::string lower(std::string s) {
    std::transform(s.begin(), s.end(), s.begin(), ::tolower);
    return s;
  }
  static std::string trim(const std::string &s) {
    size_t a = s.find_first_not_of(" \t\r\n");
    if (a == std::string::npos)
      return "";
    size_t b = s.find_last_not_of(" \t\r\n");
    return s.substr(a, b - a + 1);
  }
  static std::vector<std::string> split(const std::string &s) {
    std::vector<std::string> out;
    std::istringstream ss(s);
    std::string tok;
    while (ss >> tok)
      out.push_back(tok);
    return out;
  }

  // -- bytecode runner -------------------------------------------------------
  void run(const std::vector<Ins> &code) {
    for (int pc = 0; pc < (int)code.size(); pc++) {
      const Ins &ins = code[pc];
      if (ins.op == "lit") {
        push(ins.ival);
      } else if (ins.op == "strlit") {
        std::cout << ins.sval;
      } else if (ins.op == "call") {
        run_word(ins.sval);
      } else if (ins.op == "branch") {
        pc = ins.ival - 1;
      } else if (ins.op == "0branch") {
        if (pop() == 0)
          pc = ins.ival - 1;
      } else if (ins.op == "exit") {
        return;
      } else if (ins.op == "push-str") {
        string_table.push_back(ins.sval);
        push((int)string_table.size() - 1);
      } else if (ins.op == "local@") {
        push(lframes.back()[ins.ival]);
      } else if (ins.op == "local!") {
        lframes.back()[ins.ival] = pop();
      } else if (ins.op == "locals-enter") {
        lframes.push_back(std::vector<int>(ins.ival, 0));
      } else if (ins.op == "locals-exit") {
        lframes.pop_back();
      } else if (ins.op == "(do)") {
        int start = pop(), limit = pop();
        rpush(limit);
        rpush(start);
      } else if (ins.op == "(loop)") {
        int idx = rstack.back();
        rstack.pop_back();
        int limit = rstack.back();
        idx++;
        if (idx < limit) {
          rpush(idx);
          pc = ins.ival - 1;
        } else {
          rstack.pop_back();
        }
      } else if (ins.op == "(+loop)") {
        int step = pop();
        int idx = rstack.back();
        rstack.pop_back();
        int limit = rstack.back();
        idx += step;
        if ((step > 0 && idx < limit) || (step < 0 && idx >= limit)) {
          rstack.back() = limit;
          rpush(idx);
          pc = ins.ival - 1;
        } else {
          rstack.pop_back();
        }
      }
    }
  }

  void run_word(const std::string &raw) {
    std::string w = lower(raw);
    auto it = dict.find(w);
    if (it != dict.end()) {
      Entry &e = it->second;
      switch (e.kind) {
      case Entry::PRIM:
        e.prim();
        break;
      case Entry::WORD:
        run(e.code);
        break;
      case Entry::CREATE:
        push(e.body_addr);
        if (!e.does_code.empty())
          run(e.does_code);
        break;
      case Entry::DEFINING:
        break; // only invoked via process()
      }
      return;
    }
    auto [ok, n] = try_parse(w);
    if (ok) {
      push(n);
      return;
    }
    throw std::runtime_error("Unknown word: " + w);
  }

  // -- primitives ------------------------------------------------------------
  void init_prims() {
    // Helper to register a primitive with a fresh xt id.
    auto prim = [&](std::string name, std::function<void()> fn) {
      Entry e;
      e.kind = Entry::PRIM;
      e.prim = fn;
      register_entry(name, e);
    };
    auto make_immediate = [&](const std::string &name) {
      dict[name].is_immediate = true;
    };

    // Arithmetic
    prim("+", [&] {
      int b = pop(), a = pop();
      push(a + b);
    });
    prim("-", [&] {
      int b = pop(), a = pop();
      push(a - b);
    });
    prim("*", [&] {
      int b = pop(), a = pop();
      push(a * b);
    });
    prim("/", [&] {
      int b = pop(), a = pop();
      if (b == 0)
        throw std::runtime_error("Division by zero");
      push(a / b);
    });
    prim("mod", [&] {
      int b = pop(), a = pop();
      if (b == 0)
        throw std::runtime_error("Division by zero");
      push(a % b);
    });
    prim("and", [&] {
      int b = pop(), a = pop();
      push(a & b);
    });
    prim("or", [&] {
      int b = pop(), a = pop();
      push(a | b);
    });
    prim("xor", [&] {
      int b = pop(), a = pop();
      push(a ^ b);
    });
    prim("invert", [&] { push(~pop()); });
    prim("lshift", [&] {
      int b = pop(), a = pop();
      push(a << b);
    });
    prim("rshift", [&] {
      int b = pop(), a = pop();
      push((int)((unsigned)a >> b));
    });

    // Return stack
    prim(">r", [&] { rpush(pop()); });
    prim("r>", [&] { push(rpop()); });
    prim("r@", [&] {
      if (rstack.empty())
        throw std::runtime_error("r@ : return stack empty");
      push(rstack.back());
    });

    // Stack ops
    prim("dup", [&] {
      if (stack.empty())
        throw std::runtime_error("dup: stack underflow");
      push(stack.back());
    });
    prim("drop", [&] { pop(); });
    prim("swap", [&] {
      int b = pop(), a = pop();
      push(b);
      push(a);
    });
    prim("over", [&] {
      if (stack.size() < 2)
        throw std::runtime_error("over: stack underflow");
      push(stack[stack.size() - 2]);
    });
    prim("rot", [&] {
      int c = pop(), b = pop(), a = pop();
      push(b);
      push(c);
      push(a);
    });
    prim("depth", [&] { push((int)stack.size()); });
    prim("pick", [&] {
      int n = pop();
      if (n < 0 || n >= (int)stack.size())
        throw std::runtime_error("pick: out of range");
      push(stack[stack.size() - 1 - n]);
    });

    // Comparisons — use -1 for true (ANS standard)
    prim("=", [&] {
      int b = pop(), a = pop();
      push(a == b ? -1 : 0);
    });
    prim("<", [&] {
      int b = pop(), a = pop();
      push(a < b ? -1 : 0);
    });
    prim(">", [&] {
      int b = pop(), a = pop();
      push(a > b ? -1 : 0);
    });
    prim("0=", [&] { push(pop() == 0 ? -1 : 0); });

    // Strings
    prim("type", [&] {
      int idx = pop();
      if (idx < 0 || idx >= (int)string_table.size())
        throw std::runtime_error("type: string index out of bounds: " +
                                 std::to_string(idx));
      std::cout << string_table[idx];
    });
    prim("s=", [&] {
      int b = pop(), a = pop();
      if (a < 0 || a >= (int)string_table.size() || b < 0 ||
          b >= (int)string_table.size())
        throw std::runtime_error("s=: invalid string index");
      push(string_table[a] == string_table[b] ? -1 : 0);
    });
    prim("s+", [&] {
      int b = pop(), a = pop();
      if (a < 0 || a >= (int)string_table.size() || b < 0 ||
          b >= (int)string_table.size())
        throw std::runtime_error("s+: invalid string index");
      string_table.push_back(string_table[a] + string_table[b]);
      push((int)string_table.size() - 1);
    });
    prim("s.clear", [&] { string_table.clear(); });
    prim("s.s", [&] {
      std::cout << "String Table (" << string_table.size() << " entries):\n";
      for (size_t i = 0; i < string_table.size(); ++i)
        std::cout << "[" << i << "] \"" << string_table[i] << "\"\n";
    });
    prim("accept", [&] {
      int max_len = pop();
      std::string line;
      std::getline(std::cin, line);
      if ((int)line.size() > max_len)
        line = line.substr(0, max_len);
      string_table.push_back(line);
      push((int)string_table.size() - 1);
    });
    prim("key", [&] {
      struct termios old_t, new_t;
      tcgetattr(STDIN_FILENO, &old_t);
      new_t = old_t;
      new_t.c_lflag &= ~(ICANON | ECHO);
      tcsetattr(STDIN_FILENO, TCSANOW, &new_t);
      char c;
      std::cin.get(c);
      tcsetattr(STDIN_FILENO, TCSANOW, &old_t);
      push((int)c);
    });

    // Bases — use heap_set so full int is written
    prim("base", [&] { push(base_addr); });
    prim("hex", [&] { heap_set(base_addr, 16); });
    prim("decimal", [&] { heap_set(base_addr, 10); });
    prim("octal", [&] { heap_set(base_addr, 8); });
    prim("binary", [&] { heap_set(base_addr, 2); });

    // Control flow (immediate)
    prim("if", [&] {
      emit_ins(make("0branch", 0));
      cstack.push_back((int)prog.size() - 1);
    });
    make_immediate("if");

    prim("else", [&] {
      emit_ins(make("branch", 0));
      int prev = cstack.back();
      cstack.pop_back();
      prog[prev].ival = (int)prog.size();
      cstack.push_back((int)prog.size() - 1);
    });
    make_immediate("else");

    prim("then", [&] {
      int prev = cstack.back();
      cstack.pop_back();
      prog[prev].ival = (int)prog.size();
    });
    make_immediate("then");

    prim("begin", [&] { cstack.push_back((int)prog.size()); });
    make_immediate("begin");

    prim("until", [&] {
      int target = cstack.back();
      cstack.pop_back();
      emit_ins(make("0branch", target));
    });
    make_immediate("until");

    prim("again", [&] {
      int target = cstack.back();
      cstack.pop_back();
      emit_ins(make("branch", target));
    });
    make_immediate("again");

    prim("while", [&] {
      emit_ins(make("0branch", 0));
      cstack.push_back((int)prog.size() - 1);
    });
    make_immediate("while");

    prim("repeat", [&] {
      int while_addr = cstack.back();
      cstack.pop_back();
      int begin_addr = cstack.back();
      cstack.pop_back();
      emit_ins(make("branch", begin_addr));
      prog[while_addr].ival = (int)prog.size();
    });
    make_immediate("repeat");

    prim("do", [&] {
      emit_ins(make("(do)"));
      cstack.push_back((int)prog.size());
      leave_stack.push_back({});
    });
    make_immediate("do");

    prim("loop", [&] {
      int addr = cstack.back();
      cstack.pop_back();
      emit_ins(make("(loop)", addr));
      int exit_addr = (int)prog.size();
      for (int p : leave_stack.back())
        prog[p].ival = exit_addr;
      leave_stack.pop_back();
    });
    make_immediate("loop");

    prim("+loop", [&] {
      int addr = cstack.back();
      cstack.pop_back();
      emit_ins(make("(+loop)", addr));
      int exit_addr = (int)prog.size();
      for (int p : leave_stack.back())
        prog[p].ival = exit_addr;
      leave_stack.pop_back();
    });
    make_immediate("+loop");

    prim("leave", [&] {
      if (leave_stack.empty())
        throw std::runtime_error("leave outside do-loop");
      emit_ins(make("branch", 0));
      leave_stack.back().push_back((int)prog.size() - 1);
    });
    make_immediate("leave");

    prim("i", [&] { push(rstack.back()); });
    prim("j", [&] {
      if (rstack.size() < 3)
        throw std::runtime_error("j used outside nested loop");
      push(rstack[rstack.size() - 3]);
    });
    prim("unloop", [&] {
      if (rstack.size() < 2)
        throw std::runtime_error("unloop outside loop");
      rstack.pop_back();
      rstack.pop_back();
    });

    prim("recurse", [&] { emit_ins(make("call", current)); });
    make_immediate("recurse");
    prim("exit", [&] {
      if (!locals.empty())
        emit_ins(make("locals-exit"));
      emit_ins(make("exit"));
    });
    make_immediate("exit");

    // Memory
    prim("@", [&] {
      int addr = pop();
      if (addr < 0 || addr + cell > (int)heap.size())
        throw std::runtime_error("@: invalid address " + std::to_string(addr));
      push(heap_get(addr));
    });
    prim("!", [&] {
      int addr = pop();
      int val = pop();
      heap_set(addr, val);
    });
    prim("c@", [&] {
      int addr = pop();
      if (addr < 0 || addr >= (int)heap.size())
        throw std::runtime_error("c@: invalid address " + std::to_string(addr));
      push(heap[addr]);
    });
    prim("c!", [&] {
      int addr = pop();
      int val = pop();
      if (addr < 0 || addr >= (int)heap.size())
        throw std::runtime_error("c!: invalid address " + std::to_string(addr));
      heap[addr] = (uint8_t)val;
    });
    prim("cell", [&] { push(cell); });
    prim("cell+", [&] { push(pop() + cell); });
    prim("cells", [&] { push(pop() * cell); });
    prim(",", [&] {
      int x = pop();
      int addr = (int)heap.size();
      heap.resize(addr + cell, 0);
      memcpy(&heap[addr], &x, cell);
    });
    prim("c,", [&] {
      int x = pop();
      heap.push_back((uint8_t)x);
    });
    prim("here", [&] { push((int)heap.size()); });
    prim("allot", [&] {
      int n = pop();
      if (n < 0)
        throw std::runtime_error("allot: negative count");
      heap.resize(heap.size() + n, 0);
    });
    prim("fill", [&] {
      int val = pop(), len = pop(), addr = pop();
      if (addr < 0 || addr + len > (int)heap.size())
        throw std::runtime_error("fill: invalid range");
      std::fill(heap.begin() + addr, heap.begin() + addr + len, (uint8_t)val);
    });
    prim("dump", [&] {
      int len = pop(), addr = pop();
      std::cout << addr << " :";
      for (int i = addr; i < addr + len; i++) {
        if (i < 0 || i >= (int)heap.size())
          throw std::runtime_error("dump: invalid address");
        std::cout << " " << (int)heap[i];
      }
      std::cout << "\n";
    });
    prim("create", [&] { /* no-op: handled at parser level */ });

    // Output
    prim(".", [&] { std::cout << format_int(pop(), get_base()) << " "; });
    prim("emit", [&] { std::cout << (char)pop(); });
    prim("cr", [&] { std::cout << "\n"; });
    prim("at-xy", [&] {
      int y = pop(), x = pop();
      std::cout << "\033[" << (y + 1) << ";" << (x + 1) << "H" << std::flush;
    });
    prim(".s", [&] {
      std::cout << "Stack: [";
      for (size_t i = 0; i < stack.size(); i++) {
        if (i)
          std::cout << ", ";
        std::cout << stack[i];
      }
      std::cout << "]\n";
    });

    // Compiling / execution tokens
    // ' is handled in process() because it needs to consume the next token.
    // execute and compile, use the xt id directly.
    prim("state", [&] { push(state_addr); });
    prim("immediate", [&] {
      if (!last_word.empty())
        dict[last_word].is_immediate = true;
    });

    // execute ( xt -- ) : run the word whose id is on the stack
    prim("execute", [&] {
      int id = pop();
      run_word(xt_to_name(id));
    });

    // compile, ( xt -- ) : compile a call to the word whose id is on the stack
    prim("compile,", [&] {
      int id = pop();
      emit_ins(make("call", xt_to_name(id)));
    });

    // Misc
    prim("help-set", [&] {
      int body_idx = pop(), name_idx = pop();
      if (name_idx < 0 || name_idx >= (int)string_table.size() ||
          body_idx < 0 || body_idx >= (int)string_table.size())
        throw std::runtime_error("help-set: invalid string index");
      help_db[lower(string_table[name_idx])] = string_table[body_idx] + "\n";
    });
    prim("bye", [&] { exit(0); });
    prim("words", [&] {
      std::vector<std::string> ws;
      for (auto &kv : dict)
        if (kv.first != "__anon__")
          ws.push_back(kv.first);
      std::sort(ws.begin(), ws.end());
      for (auto &n : ws)
        std::cout << n << " ";
      std::cout << "\n";
    });
  }

  // -- string literal collector ----------------------------------------------
  std::pair<std::string, int>
  collect_string(const std::vector<std::string> &tokens, int i, char delim) {
    std::string result;
    while (true) {
      i++;
      if (i >= (int)tokens.size())
        throw std::runtime_error("Unterminated string literal");
      if (tokens[i].back() == delim) {
        result += tokens[i].substr(0, tokens[i].size() - 1);
        return {result, i};
      }
      result += tokens[i] + " ";
    }
  }

  // -- SEE decompiler --------------------------------------------------------
  void see_code(const std::vector<Ins> &code) {
    for (auto &ins : code) {
      if (ins.op == "lit")
        std::cout << "  lit " << ins.ival << "\n";
      else if (ins.op == "strlit")
        std::cout << "  .\" " << ins.sval << "\"\n";
      else if (ins.op == "call")
        std::cout << "  " << ins.sval << "\n";
      else if (ins.op == "branch")
        std::cout << "  branch -> " << ins.ival << "\n";
      else if (ins.op == "0branch")
        std::cout << "  0branch -> " << ins.ival << "\n";
      else if (ins.op == "push-str")
        std::cout << "  s\" " << ins.sval << "\"\n";
      else if (ins.op == "(do)")
        std::cout << "  do\n";
      else if (ins.op == "(loop)")
        std::cout << "  loop -> " << ins.ival << "\n";
      else if (ins.op == "(+loop)")
        std::cout << "  +loop -> " << ins.ival << "\n";
      else if (ins.op == "exit")
        std::cout << "  exit\n";
      else if (ins.op == "locals-enter") {
        std::cout << "  { ";
        for (auto &n : ins.names)
          std::cout << n << " ";
        std::cout << "-- }\n";
      } else if (ins.op == "locals-exit") { /* nothing */
      } else if (ins.op == "local@")
        std::cout << "  " << ins.sval << "\n";
      else if (ins.op == "local!")
        std::cout << "  -> " << ins.sval << "\n";
      else
        std::cout << "  [unknown: " << ins.op << " " << ins.ival << " "
                  << ins.sval << "]\n";
    }
  }

  // -- token processor -------------------------------------------------------
  void process(const std::vector<std::string> &tokens) {
    for (int i = 0; i < (int)tokens.size(); i++) {
      std::string t = lower(tokens[i]);

      // Line comment
      if (t == "\\")
        break;

      // Block comment
      if (t == "(") {
        i++;
        while (i < (int)tokens.size() && tokens[i] != ")")
          i++;
        continue;
      }

      // s" -- works in both modes
      if (t == "s\"") {
        auto [s, ni] = collect_string(tokens, i, '"');
        i = ni;
        if (!get_state()) {
          string_table.push_back(s);
          push((int)string_table.size() - 1);
        } else {
          emit_ins(make("push-str", s));
        }
        continue;
      }

      // ." and .(  -- works in both modes
      if (t == ".\"" || t == ".(") {
        char delim = (t[1] == '(') ? ')' : '"';
        auto [s, ni] = collect_string(tokens, i, delim);
        i = ni;
        if (!get_state())
          std::cout << s;
        else
          emit_ins(make("strlit", s));
        continue;
      }

      // char / [char]
      if (t == "char" || t == "[char]") {
        std::string tok = tokens[++i];
        int val = (int)(unsigned char)tok[0];
        if (get_state())
          emit_ins(make("lit", val));
        else
          push(val);
        continue;
      }

      // postpone
      if (t == "postpone") {
        std::string name = lower(tokens[++i]);
        auto it = dict.find(name);
        if (it == dict.end())
          throw std::runtime_error("postpone: unknown word: " + name);
        if (it->second.is_immediate) {
          // Compile a call to the immediate word so it runs at the
          // enclosing word's compile time.
          emit_ins(make("call", name));
        } else {
          // Compile: lit <xt>, compile,
          // At runtime this pushes the xt and calls compile, to emit the call.
          emit_ins(make("lit", name_to_xt(name)));
          emit_ins(make("call", "compile,"));
        }
        continue;
      }

      // ' (tick) -- works in both modes
      if (t == "'") {
        std::string name = lower(tokens[++i]);
        int id = name_to_xt(name); // throws if not found
        if (get_state())
          emit_ins(make("lit", id));
        else
          push(id);
        continue;
      }

      // help -- works in both modes
      if (t == "help") {
        if (i + 1 >= (int)tokens.size() || tokens[i + 1] == ";") {
          std::vector<std::string> names;
          for (auto &kv : help_db)
            names.push_back(kv.first);
          std::sort(names.begin(), names.end());
          std::cout << "Words with help entries:\n  ";
          for (auto &n : names)
            std::cout << n << " ";
          std::cout << "\n";
        } else {
          std::string name = lower(tokens[++i]);
          auto it = help_db.find(name);
          if (it != help_db.end())
            std::cout << name << "\n" << it->second;
          else if (dict.count(name))
            std::cout << name << ": no help entry (word exists)\n";
          else
            std::cout << name << ": unknown word\n";
        }
        continue;
      }

      // see -- works in both modes
      if (t == "see") {
        std::string name = lower(tokens[++i]);
        auto it = dict.find(name);
        if (it == dict.end()) {
          std::cout << "Unknown word: " << name << "\n";
          continue;
        }
        Entry &e = it->second;
        switch (e.kind) {
        case Entry::PRIM:
          std::cout << name << " is a primitive (xt=" << e.id << ")\n";
          break;
        case Entry::WORD:
        case Entry::DEFINING:
          std::cout << ": " << name << "\n";
          see_code(e.code);
          if (e.kind == Entry::DEFINING) {
            std::cout << "does>\n";
            see_code(e.does_code);
          }
          std::cout << ";\n";
          break;
        case Entry::CREATE:
          std::cout << name << " is a created word, body addr=" << e.body_addr
                    << " (xt=" << e.id << ")\n";
          break;
        }
        continue;
      }

      // -- interpret mode ----------------------------------------------------
      if (!get_state()) {

        if (t == "include") {
          load_file(tokens[++i]);
          continue;
        }
        if (t == "edit") {
          edit_file(tokens[++i]);
          continue;
        }

        if (t == "create") {
          std::string new_name = lower(tokens[++i]);
          Entry ne;
          ne.kind = Entry::CREATE;
          ne.body_addr = (int)heap.size();
          register_entry(new_name, ne);
          continue;
        }

        if (t == ":") {
          current = lower(tokens[++i]);
          last_word = current;
          prog = {};
          does_pos = -1;
          set_state(1);
          continue;
        }

        // Defining word invocation (e.g. variable foo, constant bar)
        auto it = dict.find(t);
        if (it != dict.end() && it->second.kind == Entry::DEFINING) {
          std::string new_name = lower(tokens[++i]);
          int body_addr = (int)heap.size();
          Entry ne;
          ne.kind = Entry::CREATE;
          ne.body_addr = body_addr;
          ne.does_code = it->second.does_code;
          register_entry(new_name, ne);
          run(it->second.code);
          continue;
        }

        run_word(t);
        continue;
      }

      // -- compile mode ------------------------------------------------------

      if (t == ";") {
        if (!locals.empty())
          emit_ins(make("locals-exit"));
        emit_ins(make("exit"));
        locals.clear();
        Entry e;
        if (does_pos >= 0) {
          e.kind = Entry::DEFINING;
          e.code = std::vector<Ins>(prog.begin(), prog.begin() + does_pos);
          e.does_code = std::vector<Ins>(prog.begin() + does_pos, prog.end());
        } else {
          e.kind = Entry::WORD;
          e.code = prog;
        }
        register_entry(current, e);
        set_state(0);
        does_pos = -1;
        continue;
      }

      if (t == "does>") {
        does_pos = (int)prog.size();
        continue;
      }

      if (t == "create") {
        // Inside a defining word body: no-op at compile time;
        // child creation is handled when the defining word is invoked.
        continue;
      }

      if (t == "{") {
        std::vector<std::string> names;
        while (true) {
          i++;
          if (i >= (int)tokens.size() || tokens[i] == "}")
            break;
          if (tokens[i] == "--") {
            while (i < (int)tokens.size() && tokens[i] != "}")
              i++;
            break;
          }
          names.push_back(tokens[i]);
        }
        Ins ins = make("locals-enter", (int)names.size());
        ins.names = names;
        emit_ins(ins);
        for (int j = (int)names.size() - 1; j >= 0; j--)
          emit_ins(make("local!", j, names[j]));
        locals = names;
        continue;
      }

      // Local variable read
      {
        auto lit = std::find(locals.begin(), locals.end(), t);
        if (lit != locals.end()) {
          int idx = (int)(lit - locals.begin());
          emit_ins(make("local@", idx, t));
          continue;
        }
      }

      if (t == "->") {
        std::string lname = tokens[++i];
        auto lit = std::find(locals.begin(), locals.end(), lname);
        if (lit == locals.end())
          throw std::runtime_error("Unknown local: " + lname);
        int idx = (int)(lit - locals.begin());
        emit_ins(make("local!", idx, lname));
        continue;
      }

      auto [ok, n] = try_parse(t);
      if (ok) {
        emit_ins(make("lit", n));
        continue;
      }

      auto it = dict.find(t);
      if (it != dict.end()) {
        if (it->second.is_immediate)
          run_word(t);
        else
          emit_ins(make("call", t));
        continue;
      }
      throw std::runtime_error("Unknown word: " + t);
    }
  }
};

// -- REPL -------------------------------------------------------------------
void Forth::repl(int argc, char *argv[]) {
  init_prims();
  std::string dir = DIR;
  load_file(trim(dir) + "/stdlib.fs");
  load_help(trim(dir) + "/help.txt");
  if (argc > 1)
    load_file(argv[1]);
  std::cout << "BadgerForth 1.0\n";

  while (true) {
#ifdef USE_READLINE
    char *input = readline("> ");
    if (!input)
      break;
    std::string line(input);
    if (!line.empty())
      add_history(input);
    free(input);
#else
    std::cout << "> " << std::flush;
    std::string line;
    if (!std::getline(std::cin, line))
      break;
#endif

    line = trim(line);
    if (line.empty())
      continue;

    try {
      auto tokens = split(line);
      bool wrap = true;

      if (!tokens.empty()) {
        std::string first = lower(tokens[0]);
        if (first == ":" || first == "include" || first == "edit" ||
            first == "bye" || first == "help" || first == "see") {
          wrap = false;
        }
        auto it = dict.find(first);
        if (it != dict.end() && it->second.kind == Entry::DEFINING)
          wrap = false;
      }

      // If any token is "create" or ":", don't wrap
      if (wrap) {
        for (auto &tok : tokens) {
          std::string lt = lower(tok);
          if (lt == "create" || lt == ":") {
            wrap = false;
            break;
          }
        }
      }

      if (wrap) {
        process(split(": __anon__ " + line + " ; __anon__"));
      } else {
        process(tokens);
      }
      std::cout << " ok\n";
    } catch (std::exception &e) {
      std::cout << "Error: " << e.what() << "\n";
      stack.clear();
      rstack.clear();
      lframes.clear();
      cstack.clear();
      prog.clear();
      set_state(0);
      does_pos = -1;
    }
    dict.erase("__anon__");
  }
}

int main(int argc, char *argv[]) {
  Forth().repl(argc, argv);
  return 0;
}
