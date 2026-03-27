#include <algorithm>
#include <cassert>
#include <cstdint>
#include <cstring>
#include <deque>
#include <fstream>
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

enum class Op : uint8_t {
  Add,
  Sub,
  Mul,
  Div,
  Mod,
  Dup,
  Drop,
  Swap,
  Over,
  Rot,
  Eq,
  Lt,
  Gt,
  ZEq,
  ToR,
  RFrom,
  RAt,
  Fetch,
  Store,
  CFetch,
  CStore,
  Lit,
  StrLit,
  Call,
  CallDirect,
  CallPrim,
  Branch,
  ZBranch,
  Exit,
  PushStr,
  LocalGet,
  LocalSet,
  LocalsEnter,
  LocalsExit,
  Do,
  Loop,
  PlusLoop,
  ExecMarker, // carries sval_idx = name in Code::sv
};

// Compact 16-byte Ins. Hot fields: op(1)+pad(3)+ival(4)+ptr(8).
// String data lives in Code::sv, indexed by sval_idx (-1 = none).
struct Ins {
  Op op = Op::Lit;
  int ival = 0;
  void *ptr = nullptr;
  int sval_idx = -1;
};

// Code: instruction stream + parallel string side-table.
struct Code {
  std::vector<Ins> ins;
  std::vector<std::string> sv;
  bool empty() const { return ins.empty(); }
  int size() const { return (int)ins.size(); }
  void push(Ins i) { ins.push_back(i); }
  void push_s(Ins i, std::string s) {
    i.sval_idx = (int)sv.size();
    sv.push_back(std::move(s));
    ins.push_back(i);
  }
  void push_names(Ins i, const std::vector<std::string> &ns) {
    std::string enc;
    for (auto &n : ns) {
      enc += n;
      enc += '\0';
    }
    i.sval_idx = (int)sv.size();
    sv.push_back(std::move(enc));
    ins.push_back(i);
  }
  const std::string &sval(int idx) const { return sv[idx]; }
  static std::vector<std::string> decode_names(const std::string &enc) {
    std::vector<std::string> out;
    const char *p = enc.c_str(), *e = p + enc.size();
    while (p < e) {
      out.emplace_back(p);
      p += out.back().size() + 1;
    }
    return out;
  }
};

static Ins mki() {
  Ins i;
  return i;
}
static Ins mki(Op op) {
  Ins i;
  i.op = op;
  return i;
}
static Ins mki(Op op, int v) {
  Ins i;
  i.op = op;
  i.ival = v;
  return i;
}

class Forth;
using PrimFn = void (*)(Forth &);

struct Entry {
  enum Kind : uint8_t { PRIM, WORD, DEFINING, CREATE } kind = PRIM;
  std::string name;
  PrimFn prim_fn = nullptr;
  Code code;
  Code does_code;
  int body_addr = 0;
  bool is_immediate = false;
  int id = -1;
};

class Forth {
public:
  int base_addr = 0;
  int state_addr = 0;

  static constexpr int STACK_SIZE = 1024;
  static constexpr int CALL_DEPTH = 4096;

  int stack_buf[STACK_SIZE];
  int stack_top = 0;

  int rstack_buf[STACK_SIZE];
  int rstack_top = 0;

  Forth() {
    heap.resize(2 * CELL, 0);
    int v = 10;
    memcpy(&heap[0], &v, CELL);
    state_addr = CELL;
  }

  void repl(int argc, char *argv[]);

  __attribute__((always_inline)) int pop() {
    if (stack_top == 0)
      throw std::runtime_error("Stack underflow");
    return stack_buf[--stack_top];
  }
  __attribute__((always_inline)) void push(int v) {
    if (stack_top >= STACK_SIZE)
      throw std::runtime_error("Stack overflow");
    stack_buf[stack_top++] = v;
  }
  __attribute__((always_inline)) int rpop() {
    if (rstack_top == 0)
      throw std::runtime_error("Return stack underflow");
    return rstack_buf[--rstack_top];
  }
  __attribute__((always_inline)) void rpush(int v) {
    if (rstack_top >= STACK_SIZE)
      throw std::runtime_error("Return stack overflow");
    rstack_buf[rstack_top++] = v;
  }

private:
  static constexpr int CELL = sizeof(int);

  std::deque<Entry> entries;
  std::unordered_map<std::string, int> dict;
  std::unordered_map<int, int> id_to_idx;
  int next_id = 0;

  std::vector<std::string> locals;
  std::vector<std::vector<int>> leave_stack;
  std::vector<std::string> string_table;
  std::string last_word, current;
  Code prog;
  std::vector<int> cstack;
  int does_pos = -1;

  std::vector<uint8_t> heap;
  std::unordered_map<std::string, std::string> help_db;
  int pad_addr = 0; // set in init_prims after heap reserve
  std::vector<std::vector<int>> lframes;

  int heap_get(int a) const {
    if (a < 0 || a + CELL > (int)heap.size())
      throw std::runtime_error("@: bad addr " + std::to_string(a));
    int v;
    memcpy(&v, &heap[a], CELL);
    return v;
  }
  void heap_set(int a, int v) {
    if (a + CELL > (int)heap.size())
      heap.resize(a + CELL, 0);
    memcpy(&heap[a], &v, CELL);
  }
  int get_base() const {
    int v;
    memcpy(&v, &heap[base_addr], CELL);
    return v;
  }
  int get_state() const {
    int v;
    memcpy(&v, &heap[state_addr], CELL);
    return v;
  }
  void set_state(int v) { memcpy(&heap[state_addr], &v, CELL); }
  void emit(Ins i) { prog.push(i); }
  void emit_s(Ins i, std::string s) { prog.push_s(i, std::move(s)); }
  void emit_names(Ins i, const std::vector<std::string> &ns) {
    prog.push_names(i, ns);
  }

  int register_entry(const std::string &name, Entry e) {
    e.id = next_id++;
    e.name = name;
    auto it = dict.find(name);
    if (it != dict.end()) {
      int idx = it->second;
      id_to_idx[e.id] = idx;
      entries[idx] = std::move(e);
      return idx;
    }
    int idx = (int)entries.size();
    entries.push_back(std::move(e));
    dict[name] = idx;
    id_to_idx[entries[idx].id] = idx;
    return idx;
  }
  Entry &xt_to_entry(int id) {
    auto it = id_to_idx.find(id);
    if (it == id_to_idx.end())
      throw std::runtime_error("execute: bad xt " + std::to_string(id));
    return entries[it->second];
  }
  int name_to_idx(const std::string &n) const {
    auto it = dict.find(n);
    if (it == dict.end())
      throw std::runtime_error("Unknown word: " + n);
    return it->second;
  }
  int name_to_xt(const std::string &n) { return entries[name_to_idx(n)].id; }
  Entry *find(const std::string &n) {
    auto it = dict.find(n);
    return it == dict.end() ? nullptr : &entries[it->second];
  }
  const Entry *find(const std::string &n) const {
    auto it = dict.find(n);
    return it == dict.end() ? nullptr : &entries[it->second];
  }

  static const std::unordered_map<std::string, Op> &hot_ops() {
    static const std::unordered_map<std::string, Op> m{
        {"+", Op::Add},     {"-", Op::Sub},     {"*", Op::Mul},
        {"/", Op::Div},     {"mod", Op::Mod},   {"dup", Op::Dup},
        {"drop", Op::Drop}, {"swap", Op::Swap}, {"over", Op::Over},
        {"rot", Op::Rot},   {"=", Op::Eq},      {"<", Op::Lt},
        {">", Op::Gt},      {"0=", Op::ZEq},    {">r", Op::ToR},
        {"r>", Op::RFrom},  {"r@", Op::RAt},    {"@", Op::Fetch},
        {"!", Op::Store},   {"c@", Op::CFetch}, {"c!", Op::CStore},
    };
    return m;
  }

  void resolve_calls(Code &c) {
    auto &hm = hot_ops();
    for (auto &ins : c.ins) {
      if (ins.op != Op::Call || ins.sval_idx < 0)
        continue;
      const std::string &nm = c.sv[ins.sval_idx];
      auto hi = hm.find(nm);
      if (hi != hm.end()) {
        ins.op = hi->second;
        ins.sval_idx = -1;
        continue;
      }
      auto it = dict.find(nm);
      if (it != dict.end()) {
        Entry &e = entries[it->second];
        ins.op = (e.kind == Entry::PRIM) ? Op::CallPrim : Op::CallDirect;
        ins.ival = it->second;
        ins.ptr =
            &e; // direct pointer — valid because deque never moves elements
      }
    }
  }

  std::string format_int(int n, int base) const {
    if (!n)
      return "0";
    const char *d = "0123456789abcdef";
    bool neg = n < 0;
    unsigned u = neg ? (unsigned)(-(n + 1)) + 1u : (unsigned)n;
    std::string r;
    while (u) {
      r = d[u % base] + r;
      u /= base;
    }
    return neg ? "-" + r : r;
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

  struct Frame {
    const Code *code;
    int pc;
  };
  Frame call_stack[CALL_DEPTH];
  int call_depth = 0;

  void run(const Code &start) {
    Frame *cs = call_stack;
    int &cd = call_depth;
    cs[cd++] = Frame{&start, 0};
    while (cd > 0) {
      Frame &f = cs[cd - 1];
      if (f.pc >= f.code->size()) {
        --cd;
        continue;
      }
      const Ins &ins = f.code->ins[f.pc++];
      switch (ins.op) {
      case Op::Add: {
        int b = pop(), a = pop();
        push(a + b);
      } break;
      case Op::Sub: {
        int b = pop(), a = pop();
        push(a - b);
      } break;
      case Op::Mul: {
        int b = pop(), a = pop();
        push(a * b);
      } break;
      case Op::Div: {
        int b = pop(), a = pop();
        if (!b)
          throw std::runtime_error("Division by zero");
        push(a / b);
      } break;
      case Op::Mod: {
        int b = pop(), a = pop();
        if (!b)
          throw std::runtime_error("Division by zero");
        push(a % b);
      } break;
      case Op::Dup: {
        if (stack_top == 0)
          throw std::runtime_error("dup: underflow");
        push(stack_buf[stack_top - 1]);
      } break;
      case Op::Drop:
        pop();
        break;
      case Op::Swap: {
        int b = pop(), a = pop();
        push(b);
        push(a);
      } break;
      case Op::Over: {
        if (stack_top < 2)
          throw std::runtime_error("over: underflow");
        push(stack_buf[stack_top - 2]);
      } break;
      case Op::Rot: {
        int c = pop(), b = pop(), a = pop();
        push(b);
        push(c);
        push(a);
      } break;
      case Op::Eq: {
        int b = pop(), a = pop();
        push(a == b ? -1 : 0);
      } break;
      case Op::Lt: {
        int b = pop(), a = pop();
        push(a < b ? -1 : 0);
      } break;
      case Op::Gt: {
        int b = pop(), a = pop();
        push(a > b ? -1 : 0);
      } break;
      case Op::ZEq:
        push(pop() == 0 ? -1 : 0);
        break;
      case Op::ToR:
        rpush(pop());
        break;
      case Op::RFrom:
        push(rpop());
        break;
      case Op::RAt: {
        if (rstack_top == 0)
          throw std::runtime_error("r@: empty");
        push(rstack_buf[rstack_top - 1]);
      } break;
      case Op::Fetch: {
        int a = pop();
        if (a < 0 || a + CELL > (int)heap.size())
          throw std::runtime_error("@: bad addr");
        push(heap_get(a));
      } break;
      case Op::Store: {
        int a = pop(), v = pop();
        heap_set(a, v);
      } break;
      case Op::CFetch: {
        int a = pop();
        if (a < 0 || a >= (int)heap.size())
          throw std::runtime_error("c@: bad addr");
        push(heap[a]);
      } break;
      case Op::CStore: {
        int a = pop(), v = pop();
        if (a < 0 || a >= (int)heap.size())
          throw std::runtime_error("c!: bad addr");
        heap[a] = (uint8_t)v;
      } break;
      case Op::Lit:
        push(ins.ival);
        break;
      case Op::StrLit:
        std::cout << f.code->sval(ins.sval_idx);
        break;
      case Op::Call:
        dispatch_name(f.code->sval(ins.sval_idx), cs, cd);
        break;
      case Op::CallDirect: {
        Entry *e = static_cast<Entry *>(ins.ptr);
        // WORD is the common case — put it first
        if (e->kind == Entry::WORD) {
          if (!e->code.empty()) {
            if (cd >= CALL_DEPTH)
              throw std::runtime_error("Call stack overflow");
            cs[cd++] = Frame{&e->code, 0};
          }
        } else if (e->kind == Entry::CREATE) {
          push(e->body_addr);
          if (!e->does_code.empty()) {
            if (cd >= CALL_DEPTH)
              throw std::runtime_error("Call stack overflow");
            cs[cd++] = Frame{&e->does_code, 0};
          }
        }
      } break;
      case Op::CallPrim:
        static_cast<Entry *>(ins.ptr)->prim_fn(*this);
        break;
      case Op::Branch:
        f.pc = ins.ival;
        break;
      case Op::ZBranch:
        if (pop() == 0)
          f.pc = ins.ival;
        break;
      case Op::Exit:
        --cd;
        break;
      case Op::PushStr:
        string_table.push_back(f.code->sval(ins.sval_idx));
        push((int)string_table.size() - 1);
        break;
      case Op::LocalGet:
        push(lframes.back()[ins.ival]);
        break;
      case Op::LocalSet:
        lframes.back()[ins.ival] = pop();
        break;
      case Op::LocalsEnter:
        lframes.push_back(std::vector<int>(ins.ival, 0));
        break;
      case Op::LocalsExit:
        lframes.pop_back();
        break;
      case Op::ExecMarker: {
        const std::string &name = f.code->sval(ins.sval_idx);
        auto it = marker_snaps.find(name);
        if (it == marker_snaps.end())
          throw std::runtime_error("marker: snap not found: " + name);
        auto snap = it->second;
        // Remove dict entries added after snapshot
        for (int mi = snap.n_entries; mi < (int)entries.size(); mi++)
          dict.erase(entries[mi].name);
        // Truncate entries deque
        while ((int)entries.size() > snap.n_entries)
          entries.pop_back();
        // Truncate heap
        heap.resize(snap.heap_sz, 0);
        // Remove this and later markers from snaps
        marker_snaps.erase(name);
        --cd; // pop this frame
      } break;
      case Op::Do: {
        int s = pop(), l = pop();
        rpush(l);
        rpush(s);
      } break;
      case Op::Loop: {
        int idx = rstack_buf[--rstack_top];
        int lim = rstack_buf[rstack_top - 1];
        if (++idx < lim) {
          rpush(idx);
          f.pc = ins.ival;
        } else
          --rstack_top;
      } break;
      case Op::PlusLoop: {
        int step = pop(), idx = rstack_buf[--rstack_top];
        int lim = rstack_buf[rstack_top - 1];
        idx += step;
        if ((step > 0 && idx < lim) || (step < 0 && idx >= lim)) {
          rstack_buf[rstack_top - 1] = lim;
          rpush(idx);
          f.pc = ins.ival;
        } else
          --rstack_top;
      } break;
      }
    }
    // run() exits with cd back to its entry level
  }

  void dispatch_name(const std::string &name, Frame *cs, int &cd) {
    auto it = dict.find(name);
    if (it != dict.end()) {
      dispatch_entry(entries[it->second], cs, cd);
      return;
    }
    auto [ok, n] = try_parse(name);
    if (ok) {
      push(n);
      return;
    }
    throw std::runtime_error("Unknown word: " + name);
  }
  void dispatch_entry(Entry &e, Frame *cs, int &cd) {
    switch (e.kind) {
    case Entry::PRIM:
      e.prim_fn(*this);
      break;
    case Entry::WORD:
      if (!e.code.empty()) {
        if (cd >= CALL_DEPTH)
          throw std::runtime_error("Call stack overflow");
        cs[cd++] = Frame{&e.code, 0};
      }
      break;
    case Entry::CREATE:
      push(e.body_addr);
      if (!e.does_code.empty()) {
        if (cd >= CALL_DEPTH)
          throw std::runtime_error("Call stack overflow");
        cs[cd++] = Frame{&e.does_code, 0};
      }
      break;
    case Entry::DEFINING:
      break;
    }
  }
  void run_word(const std::string &raw) {
    std::string w = lower(raw);
    auto it = dict.find(w);
    if (it != dict.end()) {
      run_entry(entries[it->second]);
      return;
    }
    auto [ok, n] = try_parse(w);
    if (ok) {
      push(n);
      return;
    }
    throw std::runtime_error("Unknown word: " + w);
  }
  void run_entry(Entry &e) {
    switch (e.kind) {
    case Entry::PRIM:
      e.prim_fn(*this);
      break;
    case Entry::WORD:
      if (!e.code.empty())
        run(e.code);
      break;
    case Entry::CREATE:
      push(e.body_addr);
      if (!e.does_code.empty())
        run(e.does_code);
      break;
    case Entry::DEFINING:
      break;
    }
  }

  // Static primitives
  static void pf_and(Forth &f) {
    int b = f.pop(), a = f.pop();
    f.push(a & b);
  }
  static void pf_or(Forth &f) {
    int b = f.pop(), a = f.pop();
    f.push(a | b);
  }
  static void pf_xor(Forth &f) {
    int b = f.pop(), a = f.pop();
    f.push(a ^ b);
  }
  static void pf_invert(Forth &f) { f.push(~f.pop()); }
  static void pf_lshift(Forth &f) {
    int b = f.pop(), a = f.pop();
    f.push(a << b);
  }
  static void pf_rshift(Forth &f) {
    int b = f.pop(), a = f.pop();
    f.push((int)((unsigned)a >> b));
  }
  static void pf_depth(Forth &f) { f.push(f.stack_top); }
  static void pf_pick(Forth &f) {
    int n = f.pop();
    if (n < 0 || n >= f.stack_top)
      throw std::runtime_error("pick: range");
    f.push(f.stack_buf[f.stack_top - 1 - n]);
  }
  static void pf_dot(Forth &f) {
    std::cout << f.format_int(f.pop(), f.get_base()) << " ";
  }
  static void pf_emit(Forth &f) { std::cout << (char)f.pop(); }
  static void pf_cr(Forth &) { std::cout << "\n"; }
  static void pf_at_xy(Forth &f) {
    int y = f.pop(), x = f.pop();
    std::cout << "\033[" << (y + 1) << ";" << (x + 1) << "H" << std::flush;
  }
  static void pf_dots(Forth &f) {
    std::cout << "Stack: [";
    for (int i = 0; i < f.stack_top; i++) {
      if (i)
        std::cout << ", ";
      std::cout << f.stack_buf[i];
    }
    std::cout << "]\n";
  }
  static void pf_type(Forth &f) {
    int i = f.pop();
    if (i < 0 || i >= (int)f.string_table.size())
      throw std::runtime_error("type: bad idx");
    std::cout << f.string_table[i];
  }
  static void pf_seq(Forth &f) {
    int b = f.pop(), a = f.pop();
    if (a < 0 || a >= (int)f.string_table.size() || b < 0 ||
        b >= (int)f.string_table.size())
      throw std::runtime_error("s=: bad idx");
    f.push(f.string_table[a] == f.string_table[b] ? -1 : 0);
  }
  static void pf_splus(Forth &f) {
    int b = f.pop(), a = f.pop();
    if (a < 0 || a >= (int)f.string_table.size() || b < 0 ||
        b >= (int)f.string_table.size())
      throw std::runtime_error("s+: bad idx");
    f.string_table.push_back(f.string_table[a] + f.string_table[b]);
    f.push((int)f.string_table.size() - 1);
  }
  static void pf_sclear(Forth &f) { f.string_table.clear(); }
  static void pf_sds(Forth &f) {
    std::cout << "String Table (" << f.string_table.size() << "):\n";
    for (size_t i = 0; i < f.string_table.size(); i++)
      std::cout << "[" << i << "] \"" << f.string_table[i] << "\"\n";
  }
  static void pf_accept(Forth &f) {
    int mx = f.pop();
    std::string l;
    std::getline(std::cin, l);
    if ((int)l.size() > mx)
      l = l.substr(0, mx);
    f.string_table.push_back(l);
    f.push((int)f.string_table.size() - 1);
  }
  static void pf_key(Forth &f) {
    struct termios o, n;
    tcgetattr(STDIN_FILENO, &o);
    n = o;
    n.c_lflag &= ~(ICANON | ECHO);
    tcsetattr(STDIN_FILENO, TCSANOW, &n);
    char c;
    std::cin.get(c);
    tcsetattr(STDIN_FILENO, TCSANOW, &o);
    f.push((int)c);
  }
  static void pf_base(Forth &f) { f.push(f.base_addr); }
  static void pf_hex(Forth &f) { f.heap_set(f.base_addr, 16); }
  static void pf_dec(Forth &f) { f.heap_set(f.base_addr, 10); }
  static void pf_oct(Forth &f) { f.heap_set(f.base_addr, 8); }
  static void pf_bin(Forth &f) { f.heap_set(f.base_addr, 2); }
  static void pf_cell_sz(Forth &f) { f.push(CELL); }
  static void pf_cell_p(Forth &f) { f.push(f.pop() + CELL); }
  static void pf_cells(Forth &f) { f.push(f.pop() * CELL); }
  static void pf_comma(Forth &f) {
    int x = f.pop(), a = (int)f.heap.size();
    f.heap.resize(a + CELL, 0);
    memcpy(&f.heap[a], &x, CELL);
  }
  static void pf_ccomma(Forth &f) { f.heap.push_back((uint8_t)f.pop()); }
  static void pf_here(Forth &f) { f.push((int)f.heap.size()); }
  static void pf_allot(Forth &f) {
    int n = f.pop();
    if (n < 0)
      throw std::runtime_error("allot: negative");
    f.heap.resize(f.heap.size() + n, 0);
  }
  static void pf_fill(Forth &f) {
    int v = f.pop(), l = f.pop(), a = f.pop();
    if (a < 0 || a + l > (int)f.heap.size())
      throw std::runtime_error("fill: range");
    std::fill(f.heap.begin() + a, f.heap.begin() + a + l, (uint8_t)v);
  }
  static void pf_dump(Forth &f) {
    int l = f.pop(), a = f.pop();
    std::cout << a << " :";
    for (int i = a; i < a + l; i++) {
      if (i < 0 || i >= (int)f.heap.size())
        throw std::runtime_error("dump: range");
      std::cout << " " << (int)f.heap[i];
    }
    std::cout << "\n";
  }	
  static void pf_celldump(Forth &f) {
    int l = f.pop(), a = f.pop();
    std::cout << a << " :";
    for (int i = a; i < a + CELL*l; i+=CELL) {
      if (i < 0 || i >= (int)f.heap.size())
        throw std::runtime_error("dump: range");
      std::cout << " " << f.heap_get(i);
    }
    std::cout << "\n";
  }
  static void pf_create_nop(Forth &) {}
  static void pf_state(Forth &f) { f.push(f.state_addr); }
  static void pf_imm(Forth &f) {
    if (!f.last_word.empty()) {
      Entry *e = f.find(f.last_word);
      if (e)
        e->is_immediate = true;
    }
  }
  static void pf_execute(Forth &f) {
    int id = f.pop();
    Entry &e = f.xt_to_entry(id);
    switch (e.kind) {
    case Entry::PRIM:
      e.prim_fn(f);
      break;
    case Entry::WORD:
      if (!e.code.empty()) {
        if (f.call_depth >= CALL_DEPTH)
          throw std::runtime_error("Call stack overflow");
        f.call_stack[f.call_depth++] = {&e.code, 0};
      }
      break;
    case Entry::CREATE:
      f.push(e.body_addr);
      if (!e.does_code.empty()) {
        if (f.call_depth >= CALL_DEPTH)
          throw std::runtime_error("Call stack overflow");
        f.call_stack[f.call_depth++] = {&e.does_code, 0};
      }
      break;
    case Entry::DEFINING:
      break;
    }
  }
  static void pf_compile_comma(Forth &f) {
    int id = f.pop();
    Entry &e = f.xt_to_entry(id);
    int idx = f.id_to_idx[id];
    Ins ci = mki(e.kind == Entry::PRIM ? Op::CallPrim : Op::CallDirect);
    ci.ptr = &e;
    f.prog.push_s(ci, e.name);
  }
  static void pf_help_set(Forth &f) {
    int bi = f.pop(), ni = f.pop();
    if (ni < 0 || ni >= (int)f.string_table.size() || bi < 0 ||
        bi >= (int)f.string_table.size())
      throw std::runtime_error("help-set: bad idx");
    f.help_db[lower(f.string_table[ni])] = f.string_table[bi] + "\n";
  }
  static void pf_bye(Forth &) { exit(0); }
  static void pf_words(Forth &f) {
    std::vector<std::string> ws;
    for (auto &kv : f.dict)
      if (kv.first != "__anon__")
        ws.push_back(kv.first);
    std::sort(ws.begin(), ws.end());
    for (auto &n : ws)
      std::cout << n << " ";
    std::cout << "\n";
  }
  // -- Additional primitives ------------------------------------------------
  static void pf_slashmod(Forth &f) {
    int b = f.pop(), a = f.pop();
    if (!b)
      throw std::runtime_error("/mod: div by zero");
    f.push(a % b);
    f.push(a / b);
  }
  static void pf_starslash(Forth &f) {
    int c = f.pop(), b = f.pop(), a = f.pop();
    if (!c)
      throw std::runtime_error("*/: div by zero");
    f.push((int)((long long)a * b / c));
  }
  static void pf_starslashmod(Forth &f) {
    int c = f.pop(), b = f.pop(), a = f.pop();
    if (!c)
      throw std::runtime_error("*/mod: div by zero");
    long long p = (long long)a * b;
    f.push((int)(p % c));
    f.push((int)(p / c));
  }
  static void pf_roll(Forth &f) {
    int n = f.pop();
    if (n < 0 || n >= f.stack_top)
      throw std::runtime_error("roll: out of range");
    int val = f.stack_buf[f.stack_top - 1 - n];
    for (int i = f.stack_top - 1 - n; i < f.stack_top - 1; i++)
      f.stack_buf[i] = f.stack_buf[i + 1];
    f.stack_top--;
    f.push(val);
  }
  static void pf_lbracket(Forth &f) { f.set_state(0); }
  static void pf_rbracket(Forth &f) { f.set_state(1); }
  static void pf_catch(Forth &f) {
    int id = f.pop();
    int ss = f.stack_top, rs = f.rstack_top, cd = f.call_depth;
    try {
      f.run_entry(f.xt_to_entry(id));
      f.push(0);
    } catch (std::exception &e) {
      f.stack_top = ss;
      f.rstack_top = rs;
      f.call_depth = cd;
      f.string_table.push_back(e.what());
      f.push((int)f.string_table.size() - 1);
      f.push(-1);
    }
  }
  static void pf_throw(Forth &f) {
    int n = f.pop();
    if (n == 0)
      return;
    if (n == -1 && f.stack_top > 0) {
      int idx = f.pop();
      std::string msg = (idx >= 0 && idx < (int)f.string_table.size())
                            ? f.string_table[idx]
                            : "error";
      throw std::runtime_error(msg);
    }
    throw std::runtime_error("throw " + std::to_string(n));
  }
  static void pf_noop(Forth &) {}

  // -- ANS core words -------------------------------------------------------
  static void pf_2over(Forth &f) {
    if (f.stack_top < 4)
      throw std::runtime_error("2over: underflow");
    int b = f.stack_buf[f.stack_top - 4], a = f.stack_buf[f.stack_top - 3];
    f.push(b);
    f.push(a);
  }
  static void pf_lt0(Forth &f) { f.push(f.pop() < 0 ? -1 : 0); }
  static void pf_gt0(Forth &f) { f.push(f.pop() > 0 ? -1 : 0); }
  static void pf_ne0(Forth &f) { f.push(f.pop() != 0 ? -1 : 0); }
  static void pf_ne(Forth &f) {
    int b = f.pop(), a = f.pop();
    f.push(a != b ? -1 : 0);
  }
  static void pf_ult(Forth &f) {
    unsigned b = (unsigned)f.pop(), a = (unsigned)f.pop();
    f.push(a < b ? -1 : 0);
  }
  static void pf_ugt(Forth &f) {
    unsigned b = (unsigned)f.pop(), a = (unsigned)f.pop();
    f.push(a > b ? -1 : 0);
  }
  static void pf_charp(Forth &f) { f.push(f.pop() + 1); } // char+ : addr+1
  static void pf_chars(Forth &f) { /* chars: n chars = n bytes, already 1:1 */ }
  // count ( addr -- addr+1 n ) : counted string — addr[0] is length byte
  static void pf_count(Forth &f) {
    int a = f.pop();
    if (a < 0 || a >= (int)f.heap.size())
      throw std::runtime_error("count: bad addr");
    int n = f.heap[a];
    f.push(a + 1);
    f.push(n);
  }
  // move ( src dst n -- ) : copy n bytes, handles overlap
  static void pf_move(Forth &f) {
    int n = f.pop(), dst = f.pop(), src = f.pop();
    if (n < 0)
      throw std::runtime_error("move: negative count");
    if (n == 0)
      return;
    int need = std::max(src + n, dst + n);
    if (src < 0 || dst < 0 || need > (int)f.heap.size())
      throw std::runtime_error("move: bad range");
    std::memmove(&f.heap[dst], &f.heap[src], n);
  }
  // cmove ( src dst n -- ) : copy forward (non-overlapping safe)
  static void pf_cmove(Forth &f) {
    int n = f.pop(), dst = f.pop(), src = f.pop();
    if (n < 0)
      throw std::runtime_error("cmove: negative count");
    if (n == 0)
      return;
    int need = std::max(src + n, dst + n);
    if (src < 0 || dst < 0 || need > (int)f.heap.size())
      throw std::runtime_error("cmove: bad range");
    std::copy(&f.heap[src], &f.heap[src] + n, &f.heap[dst]);
  }
  // cmove> ( src dst n -- ) : copy backward (for overlapping upward moves)
  static void pf_cmovegt(Forth &f) {
    int n = f.pop(), dst = f.pop(), src = f.pop();
    if (n < 0)
      throw std::runtime_error("cmove>: negative count");
    if (n == 0)
      return;
    int need = std::max(src + n, dst + n);
    if (src < 0 || dst < 0 || need > (int)f.heap.size())
      throw std::runtime_error("cmove>: bad range");
    std::copy_backward(&f.heap[src], &f.heap[src] + n, &f.heap[dst] + n);
  }
  // s>d ( n -- d_lo d_hi ) : sign-extend single to double
  static void pf_s2d(Forth &f) {
    int n = f.pop();
    f.push(n);
    f.push(n < 0 ? -1 : 0);
  }
  // d>s ( d_lo d_hi -- n ) : take low cell of double
  static void pf_d2s(Forth &f) { f.pop(); } // discard high cell
  // um* ( u1 u2 -- ud_lo ud_hi ) : unsigned 32x32->64 multiply
  static void pf_umstar(Forth &f) {
    unsigned long long r =
        (unsigned long long)(unsigned)f.pop() * (unsigned)f.pop();
    f.push((int)(r & 0xffffffff));
    f.push((int)(r >> 32));
  }
  // um/mod ( ud_lo ud_hi u -- rem quot ) : unsigned 64/32->32 divide
  static void pf_umslashmod(Forth &f) {
    unsigned divisor = (unsigned)f.pop();
    unsigned long long ud =
        ((unsigned long long)(unsigned)f.pop() << 32) | (unsigned)f.pop();
    if (!divisor)
      throw std::runtime_error("um/mod: div by zero");
    f.push((int)(ud % divisor));
    f.push((int)(ud / divisor));
  }
  // sm/rem ( d_lo d_hi n -- rem quot ) : symmetric (truncated) signed 64/32
  static void pf_smrem(Forth &f) {
    long long divisor = f.pop();
    long long hi = f.pop(), lo = (unsigned)f.pop();
    long long d = (hi << 32) | lo;
    if (!divisor)
      throw std::runtime_error("sm/rem: div by zero");
    f.push((int)(d % divisor));
    f.push((int)(d / divisor));
  }
  // fm/mod ( d_lo d_hi n -- rem quot ) : floored signed 64/32
  static void pf_fmmod(Forth &f) {
    long long divisor = f.pop();
    long long hi = f.pop(), lo = (unsigned)f.pop();
    long long d = (hi << 32) | lo;
    if (!divisor)
      throw std::runtime_error("fm/mod: div by zero");
    long long q = d / divisor, r = d % divisor;
    if (r && ((r < 0) != (divisor < 0))) {
      q--;
      r += divisor;
    }
    f.push((int)r);
    f.push((int)q);
  }
  // evaluate ( str-idx -- ) : execute a string as Forth source
  static void pf_evaluate(Forth &f) {
    int idx = f.pop();
    if (idx < 0 || idx >= (int)f.string_table.size())
      throw std::runtime_error("evaluate: bad string index");
    f.process(f.split(f.string_table[idx]));
  }
  // 2>r ( a b -- ) (R: -- a b)
  static void pf_2tor(Forth &f) {
    int b = f.pop(), a = f.pop();
    f.rpush(a);
    f.rpush(b);
  }
  // 2r> ( -- a b ) (R: a b --)
  static void pf_2rfrom(Forth &f) {
    int b = f.rpop(), a = f.rpop();
    f.push(a);
    f.push(b);
  }
  // 2r@ ( -- a b ) (R: a b -- a b)
  static void pf_2rat(Forth &f) {
    if (f.rstack_top < 2)
      throw std::runtime_error("2r@: underflow");
    f.push(f.rstack_buf[f.rstack_top - 2]);
    f.push(f.rstack_buf[f.rstack_top - 1]);
  }

  // -- Output formatting ----------------------------------------------------
  // u. ( u -- ) print unsigned
  static void pf_udot(Forth &f) {
    unsigned u = (unsigned)f.pop();
    // format in current base
    int base = f.get_base();
    if (!u) {
      std::cout << "0 ";
      return;
    }
    const char *d = "0123456789abcdef";
    std::string r;
    unsigned v = u;
    while (v) {
      r = d[v % base] + r;
      v /= base;
    }
    std::cout << r << " ";
  }
  // .r ( n width -- ) print right-justified signed in field of width
  static void pf_dotr(Forth &f) {
    int w = f.pop(), n = f.pop();
    std::string s = f.format_int(n, f.get_base());
    int pad = (int)w - (int)s.size();
    while (pad-- > 0)
      std::cout << ' ';
    std::cout << s;
  }
  // u.r ( u width -- ) print right-justified unsigned
  static void pf_udotr(Forth &f) {
    int w = f.pop();
    unsigned u = (unsigned)f.pop();
    int base = f.get_base();
    std::string s;
    if (!u)
      s = "0";
    else {
      const char *d = "0123456789abcdef";
      unsigned v = u;
      while (v) {
        s = d[v % base] + s;
        v /= base;
      }
    }
    int pad = (int)w - (int)s.size();
    while (pad-- > 0)
      std::cout << ' ';
    std::cout << s;
  }
  // d. ( lo hi -- ) print double-cell signed
  static void pf_ddot(Forth &f) {
    long long hi = f.pop();
    long long lo = (unsigned)f.pop();
    long long d = (hi << 32) | lo;
    int base = f.get_base();
    if (!d) {
      std::cout << "0 ";
      return;
    }
    bool neg = d < 0;
    unsigned long long u = neg ? -(unsigned long long)d : (unsigned long long)d;
    const char *digs = "0123456789abcdef";
    std::string r;
    while (u) {
      r = digs[u % base] + r;
      u /= base;
    }
    std::cout << (neg ? "-" : "") << r << " ";
  }
  // d.r ( lo hi width -- ) right-justified double-cell
  static void pf_ddotr(Forth &f) {
    int w = f.pop();
    long long hi = f.pop();
    long long lo = (unsigned)f.pop();
    long long d = (hi << 32) | lo;
    int base = f.get_base();
    std::string s;
    if (!d)
      s = "0";
    else {
      bool neg = d < 0;
      unsigned long long u =
          neg ? -(unsigned long long)d : (unsigned long long)d;
      const char *digs = "0123456789abcdef";
      while (u) {
        s = digs[u % base] + s;
        u /= base;
      }
      if (neg)
        s = "-" + s;
    }
    int pad = w - (int)s.size();
    while (pad-- > 0)
      std::cout << ' ';
    std::cout << s;
  }
  // bl ( -- 32 )
  static void pf_bl(Forth &f) { f.push(32); }
  // space ( -- ) emit one space
  static void pf_space(Forth &f) { std::cout << ' '; }
  // spaces ( n -- ) emit n spaces
  static void pf_spaces(Forth &f) {
    int n = f.pop();
    while (n-- > 0)
      std::cout << ' ';
  }

  // -- Memory ----------------------------------------------------------------
  // erase ( addr n -- ) fill n bytes with zero
  static void pf_erase(Forth &f) {
    int n = f.pop(), a = f.pop();
    if (n < 0)
      throw std::runtime_error("erase: negative count");
    if (a < 0 || a + n > (int)f.heap.size())
      throw std::runtime_error("erase: bad range");
    std::fill(f.heap.begin() + a, f.heap.begin() + a + n, 0);
  }
  // blank ( addr n -- ) fill n bytes with spaces
  static void pf_blank(Forth &f) {
    int n = f.pop(), a = f.pop();
    if (n < 0)
      throw std::runtime_error("blank: negative count");
    if (a < 0 || a + n > (int)f.heap.size())
      throw std::runtime_error("blank: bad range");
    std::fill(f.heap.begin() + a, f.heap.begin() + a + n, (uint8_t)32);
  }
  // pad ( -- addr ) return address of scratch pad (64 bytes above here, fixed)
  static void pf_pad(Forth &f) {
    // We keep a fixed pad region at base of heap offset 8 (after base+state)
    // Actually simpler: allocate pad lazily as a fixed heap region
    f.push(f.pad_addr);
  }
  // unused ( -- n ) bytes available in heap (we use a generous fake)
  static void pf_unused(Forth &f) { f.push(1 << 20); }
  // compare ( addr1 n1 addr2 n2 -- -1|0|1 )
  static void pf_compare(Forth &f) {
    int n2 = f.pop(), a2 = f.pop(), n1 = f.pop(), a1 = f.pop();
    int n = std::min(n1, n2);
    for (int i = 0; i < n; i++) {
      uint8_t c1 = f.heap[a1 + i], c2 = f.heap[a2 + i];
      if (c1 < c2) {
        f.push(-1);
        return;
      }
      if (c1 > c2) {
        f.push(1);
        return;
      }
    }
    if (n1 < n2) {
      f.push(-1);
      return;
    }
    if (n1 > n2) {
      f.push(1);
      return;
    }
    f.push(0);
  }
  // within ( n lo hi -- flag ) lo <= n < hi
  static void pf_within(Forth &f) {
    int hi = f.pop(), lo = f.pop(), n = f.pop();
    f.push((n >= lo && n < hi) ? -1 : 0);
  }
  // bounds ( addr n -- addr+n addr ) for use in DO loop
  static void pf_bounds(Forth &f) {
    int n = f.pop(), a = f.pop();
    f.push(a + n);
    f.push(a);
  }
  // abort ( -- ) throw standard abort exception
  static void pf_abort(Forth &f) {
    (void)f;
    throw std::runtime_error("abort");
  }
  // abort" is handled in process() as a string-consuming immediate
  // quit ( -- ) restart interpreter (simplified: just throw)
  static void pf_quit(Forth &f) {
    (void)f;
    throw std::runtime_error("quit");
  }

  // -- Marker / forget -------------------------------------------------------
  // We store marker snapshots in a separate map keyed by name.
  // marker saves: entries.size(), dict snapshot, heap.size()
  // Forgetting a marker re-truncates entries and heap and rebuilds dict.
  struct MarkerSnap {
    int n_entries;
    int heap_sz;
  };
  std::unordered_map<std::string, MarkerSnap> marker_snaps;

  static void exec_marker(Forth &f, const std::string &name) {
    auto it = f.marker_snaps.find(name);
    if (it == f.marker_snaps.end())
      throw std::runtime_error("marker: snap not found for " + name);
    auto &snap = it->second;
    // remove dict entries added after snapshot
    for (int i = snap.n_entries; i < (int)f.entries.size(); i++)
      f.dict.erase(f.entries[i].name);
    // truncate entries deque
    while ((int)f.entries.size() > snap.n_entries)
      f.entries.pop_back();
    // truncate heap
    f.heap.resize(snap.heap_sz, 0);
    // remove this marker and all later markers
    f.marker_snaps.erase(name);
  }

  // action-of ( "name" -- xt ) get current xt of a deferred word
  // (handled at parse level, similar to ')
  static void pf_action_of_dummy(Forth &) {
  } // placeholder — real work in process()

  // body> ( body-addr -- xt ) inverse of >body: find Entry with this body_addr
  static void pf_bodyfrom(Forth &f) {
    int ba = f.pop();
    for (auto &e : f.entries) {
      if (e.kind == Entry::CREATE && e.body_addr == ba) {
        f.push(e.id);
        return;
      }
    }
    throw std::runtime_error("body>: no entry found for body addr " +
                             std::to_string(ba));
  }

  // ?dup ( n -- n n | 0 ) dup if non-zero
  static void pf_qdup(Forth &f) {
    if (f.stack_top == 0)
      throw std::runtime_error("?dup: underflow");
    if (f.stack_buf[f.stack_top - 1])
      f.push(f.stack_buf[f.stack_top - 1]);
  }

  // 2nip ( a b c d -- c d )
  static void pf_2nip(Forth &f) {
    if (f.stack_top < 4)
      throw std::runtime_error("2nip: underflow");
    f.stack_buf[f.stack_top - 4] = f.stack_buf[f.stack_top - 2];
    f.stack_buf[f.stack_top - 3] = f.stack_buf[f.stack_top - 1];
    f.stack_top -= 2;
  }

  // Pictured numeric output: <# # #s sign #>
  // We build the output string right-to-left in a pic_buf
  std::string pic_buf;
  // <# ( -- ) start pictured output
  static void pf_picstart(Forth &f) { f.pic_buf.clear(); }
  // # ( ud_lo ud_hi -- ud_lo' ud_hi' ) extract one digit
  static void pf_picdigit(Forth &f) {
    unsigned long long hi = (unsigned)f.pop(), lo = (unsigned)f.pop();
    unsigned long long ud = (hi << 32) | lo;
    int base = f.get_base();
    const char *digs = "0123456789abcdef";
    f.pic_buf = digs[ud % base] + f.pic_buf;
    ud /= base;
    f.push((int)(ud & 0xffffffff));
    f.push((int)(ud >> 32));
  }
  // #s ( ud_lo ud_hi -- 0 0 ) extract all remaining digits
  static void pf_picdigits(Forth &f) {
    unsigned long long hi = (unsigned)f.pop(), lo = (unsigned)f.pop();
    unsigned long long ud = (hi << 32) | lo;
    int base = f.get_base();
    const char *digs = "0123456789abcdef";
    do {
      f.pic_buf = digs[ud % base] + f.pic_buf;
      ud /= base;
    } while (ud);
    f.push(0);
    f.push(0);
  }
  // sign ( n -- ) prepend minus if n<0
  static void pf_picsign(Forth &f) {
    if (f.pop() < 0)
      f.pic_buf = "-" + f.pic_buf;
  }
  // hold ( char -- ) prepend char to picture
  static void pf_hold(Forth &f) { f.pic_buf = (char)f.pop() + f.pic_buf; }
  // holds ( str-idx -- ) prepend string to picture
  static void pf_holds(Forth &f) {
    int idx = f.pop();
    if (idx < 0 || idx >= (int)f.string_table.size())
      throw std::runtime_error("holds: bad idx");
    f.pic_buf = f.string_table[idx] + f.pic_buf;
  }
  // #> ( ud_lo ud_hi -- addr n ) end picture, push string as c-addr/len pair
  //    We push the result as a string-table entry + length for simplicity
  static void pf_picend(Forth &f) {
    f.pop();
    f.pop(); // discard remaining ud
    f.string_table.push_back(f.pic_buf);
    int idx = (int)f.string_table.size() - 1;
    f.pic_buf.clear();
    // push addr=idx, n=len — callers use TYPE to print
    // ANS: #> leaves c-addr u; we emulate with our string model
    // push the idx as a pseudo c-addr and the length separately
    f.push(idx);
    f.push((int)f.string_table[idx].size());
  }

  // sp@ ( -- addr ) stack pointer (index)
  static void pf_spat(Forth &f) { f.push(f.stack_top); }
  // sp! ( addr -- ) restore stack pointer
  static void pf_spstore(Forth &f) {
    int n = f.pop();
    if (n < 0 || n > STACK_SIZE)
      throw std::runtime_error("sp!: bad");
    f.stack_top = n;
  }

  static void pf_i(Forth &f) { f.push(f.rstack_buf[f.rstack_top - 1]); }
  static void pf_j(Forth &f) {
    if (f.rstack_top < 3)
      throw std::runtime_error("j: outside nested loop");
    f.push(f.rstack_buf[f.rstack_top - 3]);
  }
  static void pf_unloop(Forth &f) {
    if (f.rstack_top < 2)
      throw std::runtime_error("unloop: outside loop");
    --f.rstack_top;
    --f.rstack_top;
  }
  static void pf_if(Forth &f) {
    f.prog.push(mki(Op::ZBranch, 0));
    f.cstack.push_back((int)f.prog.ins.size() - 1);
  }
  static void pf_else(Forth &f) {
    f.prog.push(mki(Op::Branch, 0));
    int p = f.cstack.back();
    f.cstack.pop_back();
    f.prog.ins[p].ival = (int)f.prog.ins.size();
    f.cstack.push_back((int)f.prog.ins.size() - 1);
  }
  static void pf_then(Forth &f) {
    int p = f.cstack.back();
    f.cstack.pop_back();
    f.prog.ins[p].ival = (int)f.prog.ins.size();
  }
  static void pf_begin(Forth &f) { f.cstack.push_back((int)f.prog.ins.size()); }
  static void pf_until(Forth &f) {
    int t = f.cstack.back();
    f.cstack.pop_back();
    f.prog.push(mki(Op::ZBranch, t));
  }
  static void pf_again(Forth &f) {
    int t = f.cstack.back();
    f.cstack.pop_back();
    f.prog.push(mki(Op::Branch, t));
  }
  static void pf_while(Forth &f) {
    f.prog.push(mki(Op::ZBranch, 0));
    f.cstack.push_back((int)f.prog.ins.size() - 1);
  }
  static void pf_repeat(Forth &f) {
    int wa = f.cstack.back();
    f.cstack.pop_back();
    int ba = f.cstack.back();
    f.cstack.pop_back();
    f.prog.push(mki(Op::Branch, ba));
    f.prog.ins[wa].ival = (int)f.prog.ins.size();
  }
  static void pf_do(Forth &f) {
    f.prog.push(mki(Op::Do));
    f.cstack.push_back((int)f.prog.ins.size());
    f.leave_stack.push_back({});
  }
  static void pf_qdo(Forth &f) {
    f.prog.push(mki(Op::Over));
    f.prog.push(mki(Op::Over));
    f.prog.push(mki(Op::Eq));
    f.prog.push(mki(Op::ZBranch, 0));
    int zbr = (int)f.prog.ins.size() - 1;
    f.prog.push(mki(Op::Drop));
    f.prog.push(mki(Op::Drop));
    f.prog.push(mki(Op::Branch, 0));
    int skip = (int)f.prog.ins.size() - 1;
    f.prog.ins[zbr].ival = (int)f.prog.ins.size();
    f.prog.push(mki(Op::Do));
    f.cstack.push_back((int)f.prog.ins.size());
    f.leave_stack.push_back({skip});
  }
  static void pf_loop(Forth &f) {
    int a = f.cstack.back();
    f.cstack.pop_back();
    f.prog.push(mki(Op::Loop, a));
    int ea = (int)f.prog.ins.size();
    for (int p : f.leave_stack.back())
      f.prog.ins[p].ival = ea;
    f.leave_stack.pop_back();
  }
  static void pf_ploop(Forth &f) {
    int a = f.cstack.back();
    f.cstack.pop_back();
    f.prog.push(mki(Op::PlusLoop, a));
    int ea = (int)f.prog.ins.size();
    for (int p : f.leave_stack.back())
      f.prog.ins[p].ival = ea;
    f.leave_stack.pop_back();
  }
  static void pf_leave(Forth &f) {
    if (f.leave_stack.empty())
      throw std::runtime_error("leave: outside do-loop");
    f.prog.push(mki(Op::Branch, 0));
    f.leave_stack.back().push_back((int)f.prog.ins.size() - 1);
  }
  static void pf_recurse(Forth &f) { f.prog.push_s(mki(Op::Call), f.current); }
  static void pf_exit(Forth &f) {
    if (!f.locals.empty())
      f.prog.push(mki(Op::LocalsExit));
    f.prog.push(mki(Op::Exit));
  }

  void init_prims() {
    auto prim = [&](const char *name, PrimFn fn, bool imm = false) {
      Entry e;
      e.kind = Entry::PRIM;
      e.prim_fn = fn;
      int idx = register_entry(name, e);
      if (imm)
        entries[idx].is_immediate = true;
    };
    // Hot ops — also registered so run_entry/execute work via prim_fn
    prim("+", [](Forth &f) {
      int b = f.pop(), a = f.pop();
      f.push(a + b);
    });
    prim("-", [](Forth &f) {
      int b = f.pop(), a = f.pop();
      f.push(a - b);
    });
    prim("*", [](Forth &f) {
      int b = f.pop(), a = f.pop();
      f.push(a * b);
    });
    prim("/", [](Forth &f) {
      int b = f.pop(), a = f.pop();
      if (!b)
        throw std::runtime_error("Division by zero");
      f.push(a / b);
    });
    prim("mod", [](Forth &f) {
      int b = f.pop(), a = f.pop();
      if (!b)
        throw std::runtime_error("Division by zero");
      f.push(a % b);
    });
    prim("dup", [](Forth &f) {
      if (f.stack_top == 0)
        throw std::runtime_error("dup: underflow");
      f.push(f.stack_buf[f.stack_top - 1]);
    });
    prim("drop", [](Forth &f) { f.pop(); });
    prim("swap", [](Forth &f) {
      int b = f.pop(), a = f.pop();
      f.push(b);
      f.push(a);
    });
    prim("over", [](Forth &f) {
      if (f.stack_top < 2)
        throw std::runtime_error("over: underflow");
      f.push(f.stack_buf[f.stack_top - 2]);
    });
    prim("rot", [](Forth &f) {
      int c = f.pop(), b = f.pop(), a = f.pop();
      f.push(b);
      f.push(c);
      f.push(a);
    });
    prim("=", [](Forth &f) {
      int b = f.pop(), a = f.pop();
      f.push(a == b ? -1 : 0);
    });
    prim("<", [](Forth &f) {
      int b = f.pop(), a = f.pop();
      f.push(a < b ? -1 : 0);
    });
    prim(">", [](Forth &f) {
      int b = f.pop(), a = f.pop();
      f.push(a > b ? -1 : 0);
    });
    prim("0=", [](Forth &f) { f.push(f.pop() == 0 ? -1 : 0); });
    prim(">r", [](Forth &f) { f.rpush(f.pop()); });
    prim("r>", [](Forth &f) { f.push(f.rpop()); });
    prim("r@", [](Forth &f) {
      if (f.rstack_top == 0)
        throw std::runtime_error("r@: empty");
      f.push(f.rstack_buf[f.rstack_top - 1]);
    });
    prim("@", [](Forth &f) {
      int a = f.pop();
      if (a < 0 || a + CELL > (int)f.heap.size())
        throw std::runtime_error("@: bad addr");
      f.push(f.heap_get(a));
    });
    prim("!", [](Forth &f) {
      int a = f.pop(), v = f.pop();
      f.heap_set(a, v);
    });
    prim("c@", [](Forth &f) {
      int a = f.pop();
      if (a < 0 || a >= (int)f.heap.size())
        throw std::runtime_error("c@: bad addr");
      f.push(f.heap[a]);
    });
    prim("c!", [](Forth &f) {
      int a = f.pop(), v = f.pop();
      if (a < 0 || a >= (int)f.heap.size())
        throw std::runtime_error("c!: bad addr");
      f.heap[a] = (uint8_t)v;
    });
    // Other primitives
    prim("and", pf_and);
    prim("or", pf_or);
    prim("xor", pf_xor);
    prim("invert", pf_invert);
    prim("lshift", pf_lshift);
    prim("rshift", pf_rshift);
    prim("depth", pf_depth);
    prim("pick", pf_pick);
    prim(".", pf_dot);
    prim("emit", pf_emit);
    prim("cr", pf_cr);
    prim("at-xy", pf_at_xy);
    prim(".s", pf_dots);
    prim("type", pf_type);
    prim("s=", pf_seq);
    prim("s+", pf_splus);
    prim("s.clear", pf_sclear);
    prim("s.s", pf_sds);
    prim("accept", pf_accept);
    prim("key", pf_key);
    prim("base", pf_base);
    prim("hex", pf_hex);
    prim("decimal", pf_dec);
    prim("octal", pf_oct);
    prim("binary", pf_bin);
    prim("cell", pf_cell_sz);
    prim("cell+", pf_cell_p);
    prim("cells", pf_cells);
    prim(",", pf_comma);
    prim("c,", pf_ccomma);
    prim("here", pf_here);
    prim("allot", pf_allot);
    prim("fill", pf_fill);
    prim("dump", pf_dump);
		prim("celldump", pf_celldump);
    prim("create", pf_create_nop);
    prim("state", pf_state);
    prim("immediate", pf_imm);
    prim("execute", pf_execute);
    prim("compile,", pf_compile_comma);
    prim("help-set", pf_help_set);
    prim("bye", pf_bye);
    prim("words", pf_words);
    // >body ( xt -- body-addr ) : given xt, push body address of CREATE word
    prim(">body", [](Forth &f) {
      int id = f.pop();
      Entry &e = f.xt_to_entry(id);
      if (e.kind != Entry::CREATE)
        throw std::runtime_error(">body: not a CREATE word");
      f.push(e.body_addr);
    });
    prim("/mod", pf_slashmod);
    prim("*/", pf_starslash);
    prim("*/mod", pf_starslashmod);
    prim("roll", pf_roll);
    prim("[", pf_lbracket, true);
    prim("]", pf_rbracket);
    // literal: compile-time, pops TOS and emits as Lit
    prim("literal", [](Forth &f) { f.prog.push(mki(Op::Lit, f.pop())); }, true);
    prim("catch", pf_catch);
    prim("throw", pf_throw);
    prim("noop", pf_noop);
    prim("2over", pf_2over);
    prim("0<", pf_lt0);
    prim("0>", pf_gt0);
    prim("0<>", pf_ne0);
    prim("<>", pf_ne);
    prim("u<", pf_ult);
    prim("u>", pf_ugt);
    prim("char+", pf_charp);
    prim("chars", pf_chars);
    prim("count", pf_count);
    prim("move", pf_move);
    prim("cmove", pf_cmove);
    prim("cmove>", pf_cmovegt);
    prim("s>d", pf_s2d);
    prim("d>s", pf_d2s);
    prim("um*", pf_umstar);
    prim("um/mod", pf_umslashmod);
    prim("sm/rem", pf_smrem);
    prim("fm/mod", pf_fmmod);
    prim("evaluate", pf_evaluate);
    prim("2>r", pf_2tor);
    prim("2r>", pf_2rfrom);
    prim("2r@", pf_2rat);
    prim("u.", pf_udot);
    prim(".r", pf_dotr);
    prim("u.r", pf_udotr);
    prim("d.", pf_ddot);
    prim("d.r", pf_ddotr);
    prim("bl", pf_bl);
    prim("space", pf_space);
    prim("spaces", pf_spaces);
    prim("erase", pf_erase);
    prim("blank", pf_blank);
    prim("pad", pf_pad);
    prim("unused", pf_unused);
    prim("compare", pf_compare);
    prim("within", pf_within);
    prim("bounds", pf_bounds);
    prim("abort", pf_abort);
    prim("quit", pf_quit);
    prim("?dup", pf_qdup);
    prim("2nip", pf_2nip);
    prim("body>", pf_bodyfrom);
    prim("<#", pf_picstart);
    prim("#", pf_picdigit);
    prim("#s", pf_picdigits);
    prim("sign", pf_picsign);
    prim("hold", pf_hold);
    prim("holds", pf_holds);
    prim("#>", pf_picend);
    prim("sp@", pf_spat);
    prim("sp!", pf_spstore);
    // init pad: reserve 84 bytes above heap for pad scratch area
    pad_addr = (int)heap.size();
    heap.resize(pad_addr + 84, 0);
    prim("i", pf_i);
    prim("j", pf_j);
    prim("unloop", pf_unloop);
    prim("if", pf_if, true);
    prim("else", pf_else, true);
    prim("then", pf_then, true);
    prim("begin", pf_begin, true);
    prim("until", pf_until, true);
    prim("again", pf_again, true);
    prim("while", pf_while, true);
    prim("repeat", pf_repeat, true);
    prim("do", pf_do, true);
    prim("?do", pf_qdo, true);
    prim("loop", pf_loop, true);
    prim("+loop", pf_ploop, true);
    prim("leave", pf_leave, true);
    prim("recurse", pf_recurse, true);
    prim("exit", pf_exit, true);
  }

  std::pair<std::string, int>
  collect_string(const std::vector<std::string> &tok, int i, char d) {
    std::string r;
    while (true) {
      if (++i >= (int)tok.size())
        throw std::runtime_error("Unterminated string");
      if (tok[i].back() == d) {
        r += tok[i].substr(0, tok[i].size() - 1);
        return {r, i};
      }
      r += tok[i] + " ";
    }
  }

  void see_code(const Code &c) {
    static const std::unordered_map<int, std::string> op_names{
        {(int)Op::Add, "+"},     {(int)Op::Sub, "-"},
        {(int)Op::Mul, "*"},     {(int)Op::Div, "/"},
        {(int)Op::Mod, "mod"},   {(int)Op::Dup, "dup"},
        {(int)Op::Drop, "drop"}, {(int)Op::Swap, "swap"},
        {(int)Op::Over, "over"}, {(int)Op::Rot, "rot"},
        {(int)Op::Eq, "="},      {(int)Op::Lt, "<"},
        {(int)Op::Gt, ">"},      {(int)Op::ZEq, "0="},
        {(int)Op::ToR, ">r"},    {(int)Op::RFrom, "r>"},
        {(int)Op::RAt, "r@"},    {(int)Op::Fetch, "@"},
        {(int)Op::Store, "!"},   {(int)Op::CFetch, "c@"},
        {(int)Op::CStore, "c!"},
    };
    for (auto &ins : c.ins) {
      auto it = op_names.find((int)ins.op);
      if (it != op_names.end()) {
        std::cout << "  " << it->second << "\n";
        continue;
      }
      switch (ins.op) {
      case Op::Lit:
        std::cout << "  lit " << ins.ival << "\n";
        break;
      case Op::StrLit:
        std::cout << "  .\" " << (ins.sval_idx >= 0 ? c.sv[ins.sval_idx] : "?")
                  << "\"\n";
        break;
      case Op::Call:
      case Op::CallDirect:
      case Op::CallPrim:
        std::cout << "  " << (ins.sval_idx >= 0 ? c.sv[ins.sval_idx] : "?")
                  << "\n";
        break;
      case Op::Branch:
        std::cout << "  branch -> " << ins.ival << "\n";
        break;
      case Op::ZBranch:
        std::cout << "  0branch -> " << ins.ival << "\n";
        break;
      case Op::Exit:
        std::cout << "  exit\n";
        break;
      case Op::PushStr:
        std::cout << "  s\" " << (ins.sval_idx >= 0 ? c.sv[ins.sval_idx] : "?")
                  << "\"\n";
        break;
      case Op::LocalGet:
        std::cout << "  " << (ins.sval_idx >= 0 ? c.sv[ins.sval_idx] : "?")
                  << "\n";
        break;
      case Op::LocalSet:
        std::cout << "  -> " << (ins.sval_idx >= 0 ? c.sv[ins.sval_idx] : "?")
                  << "\n";
        break;
      case Op::LocalsEnter:
        if (ins.sval_idx >= 0) {
          std::cout << "  { ";
          for (auto &n : Code::decode_names(c.sv[ins.sval_idx]))
            std::cout << n << " ";
          std::cout << "-- }\n";
        }
        break;
      case Op::LocalsExit:
        break;
      case Op::ExecMarker:
        std::cout << "  [marker restore: "
                  << (ins.sval_idx >= 0 ? c.sv[ins.sval_idx] : "?") << "]\n";
        break;
      case Op::Do:
        std::cout << "  do\n";
        break;
      case Op::Loop:
        std::cout << "  loop -> " << ins.ival << "\n";
        break;
      case Op::PlusLoop:
        std::cout << "  +loop -> " << ins.ival << "\n";
        break;
      default:
        break;
      }
    }
  }

  void process(const std::vector<std::string> &tokens) {
    for (int i = 0; i < (int)tokens.size(); i++) {
      std::string t = lower(tokens[i]);
      if (t == "\\")
        break;
      if (t == "(") {
        i++;
        while (i < (int)tokens.size() && tokens[i] != ")")
          i++;
        continue;
      }
      if (t == "s\"") {
        auto [s, ni] = collect_string(tokens, i, '"');
        i = ni;
        if (!get_state()) {
          string_table.push_back(s);
          push((int)string_table.size() - 1);
        } else
          prog.push_s(mki(Op::PushStr), s);
        continue;
      }
      if (t == "abort\"") {
        auto [s, ni] = collect_string(tokens, i, '"');
        i = ni;
        if (!get_state()) {
          // interpret mode: if stack non-empty and nonzero, abort with message
          if (stack_top > 0 && pop() != 0)
            throw std::runtime_error(s);
        } else {
          // compile mode: compile (if TOS nonzero) throw message
          // emit: ZBranch over (throw StrLit)
          int skip_pos = (int)prog.ins.size();
          prog.push(mki(Op::ZBranch, 0));
          prog.push_s(mki(Op::PushStr), s);
          prog.push_s(mki(Op::Call), "throw-str");
          prog.ins[skip_pos].ival = (int)prog.ins.size();
        }
        continue;
      }
      if (t == ".\"" || t == ".(") {
        char d = (t[1] == '(') ? ')' : '"';
        auto [s, ni] = collect_string(tokens, i, d);
        i = ni;
        if (!get_state())
          std::cout << s;
        else
          prog.push_s(mki(Op::StrLit), s);
        continue;
      }
      if (t == "char" || t == "[char]") {
        std::string tok = tokens[++i];
        int val = (int)(unsigned char)tok[0];
        if (get_state())
          prog.push(mki(Op::Lit, val));
        else
          push(val);
        continue;
      }
      if (t == "postpone") {
        std::string name = lower(tokens[++i]);
        Entry *e = find(name);
        if (!e)
          throw std::runtime_error("postpone: unknown: " + name);
        if (e->is_immediate)
          prog.push_s(mki(Op::Call), name);
        else {
          prog.push(mki(Op::Lit, name_to_xt(name)));
          prog.push_s(mki(Op::Call), "compile,");
        }
        continue;
      }
      if (t == "'" || t == "[']") {
        std::string name = lower(tokens[++i]);
        int id = name_to_xt(name);
        if (get_state())
          prog.push(mki(Op::Lit, id));
        else
          push(id);
        continue;
      }
      if (t == "help") {
        if (i + 1 >= (int)tokens.size() || tokens[i + 1] == ";") {
          std::vector<std::string> ns;
          for (auto &kv : help_db)
            ns.push_back(kv.first);
          std::sort(ns.begin(), ns.end());
          std::cout << "Words with help entries:\n  ";
          for (auto &n : ns)
            std::cout << n << " ";
          std::cout << "\n";
        } else {
          std::string name = lower(tokens[++i]);
          auto it = help_db.find(name);
          if (it != help_db.end())
            std::cout << name << "\n" << it->second;
          else if (find(name))
            std::cout << name << ": no help entry (word exists)\n";
          else
            std::cout << name << ": unknown word\n";
        }
        continue;
      }
      if (t == "see") {
        std::string name = lower(tokens[++i]);
        Entry *e = find(name);
        if (!e) {
          std::cout << "Unknown word: " << name << "\n";
          continue;
        }
        switch (e->kind) {
        case Entry::PRIM:
          std::cout << name << " is a primitive (xt=" << e->id << ")\n";
          break;
        case Entry::WORD:
        case Entry::DEFINING:
          std::cout << ": " << name << "\n";
          see_code(e->code);
          if (e->kind == Entry::DEFINING) {
            std::cout << "does>\n";
            see_code(e->does_code);
          }
          std::cout << ";\n";
          break;
        case Entry::CREATE:
          std::cout << name << " is a created word, body addr=" << e->body_addr
                    << " (xt=" << e->id << ")\n";
          break;
        }
        continue;
      }
      if (!get_state()) {
        if (t == "marker") {
          std::string mname = lower(tokens[++i]);
          // Save snapshot
          marker_snaps[mname] = {static_cast<int>(entries.size()),
                                 static_cast<int>(heap.size())};
          // Build a Code that contains a single ExecMarker instruction
          Code mc;
          Ins mi;
          mi.op = Op::ExecMarker;
          mc.push_s(mi, mname);
          Ins ex;
          ex.op = Op::Exit;
          mc.push(ex);
          // Register as a WORD
          Entry me;
          me.kind = Entry::WORD;
          me.code = mc;
          register_entry(mname, me);
          continue;
        }
        if (t == "is") {
          int xt = pop();
          std::string name = lower(tokens[++i]);
          Entry *e = find(name);
          if (!e || e->kind != Entry::CREATE)
            throw std::runtime_error("is: " + name + " is not a deferred word");
          heap_set(e->body_addr, xt);
          continue;
        }
        if (t == "include") {
          load_file(tokens[++i]);
          continue;
        }
        if (t == "edit") {
          edit_file(tokens[++i]);
          continue;
        }
        if (t == "create") {
          Entry ne;
          ne.kind = Entry::CREATE;
          ne.body_addr = (int)heap.size();
          register_entry(lower(tokens[++i]), ne);
          continue;
        }
        if (t == ":") {
          current = lower(tokens[++i]);
          last_word = current;
          prog = Code{};
          does_pos = -1;
          set_state(1);
          continue;
        }
        {
          auto it = dict.find(t);
          if (it != dict.end() && entries[it->second].kind == Entry::DEFINING) {
            Entry &de = entries[it->second];
            Entry ne;
            ne.kind = Entry::CREATE;
            ne.body_addr = (int)heap.size();
            ne.does_code = de.does_code;
            register_entry(lower(tokens[++i]), ne);
            run(de.code);
            continue;
          }
        }
        run_word(t);
        continue;
      }
      if (t == ";") {
        if (!locals.empty())
          prog.push(mki(Op::LocalsExit));
        prog.push(mki(Op::Exit));
        locals.clear();
        Entry e;
        if (does_pos >= 0) {
          e.kind = Entry::DEFINING;
          e.code.ins =
              std::vector<Ins>(prog.ins.begin(), prog.ins.begin() + does_pos);
          e.code.sv = prog.sv;
          e.does_code.ins =
              std::vector<Ins>(prog.ins.begin() + does_pos, prog.ins.end());
          e.does_code.sv = prog.sv;
        } else {
          e.kind = Entry::WORD;
          e.code = prog;
        }
        int idx = register_entry(current, e);
        resolve_calls(entries[idx].code);
        resolve_calls(entries[idx].does_code);
        set_state(0);
        does_pos = -1;
        continue;
      }
      if (t == "does>") {
        does_pos = (int)prog.ins.size();
        continue;
      }
      if (t == "create") {
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
        prog.push_names(mki(Op::LocalsEnter, (int)names.size()), names);
        for (int j = (int)names.size() - 1; j >= 0; j--)
          prog.push_s(mki(Op::LocalSet, j), names[j]);
        locals = names;
        continue;
      }
      {
        auto lit = std::find(locals.begin(), locals.end(), t);
        if (lit != locals.end()) {
          prog.push_s(mki(Op::LocalGet, (int)(lit - locals.begin())), t);
          continue;
        }
      }
      if (t == "->") {
        std::string ln = tokens[++i];
        auto lit = std::find(locals.begin(), locals.end(), ln);
        if (lit == locals.end())
          throw std::runtime_error("Unknown local: " + ln);
        prog.push_s(mki(Op::LocalSet, (int)(lit - locals.begin())), ln);
        continue;
      }
      auto [ok, n] = try_parse(t);
      if (ok) {
        prog.push(mki(Op::Lit, n));
        continue;
      }
      {
        auto it = dict.find(t);
        if (it != dict.end()) {
          Entry &e = entries[it->second];
          if (e.is_immediate)
            run_entry(e);
          else
            prog.push_s(mki(Op::Call), t);
          continue;
        }
      }
      if (t == "is") {
        // immediate even in compile mode: xt is wordname
        int xt = pop();
        std::string name = lower(tokens[++i]);
        Entry *e = find(name);
        if (!e || e->kind != Entry::CREATE)
          throw std::runtime_error("is: " + name + " is not a deferred word");
        heap_set(e->body_addr, xt);
        continue;
      }
      if (t == current) {
        prog.push_s(mki(Op::Call), t);
        continue;
      }
      throw std::runtime_error("Unknown word: " + t);
    }
  }

  void edit_file(const std::string &fn) {
    const char *ed = std::getenv("EDITOR");
    if (!ed)
      ed = "vi";
    pid_t pid = fork();
    if (pid == 0) {
      execlp(ed, ed, fn.c_str(), nullptr);
      _exit(1);
    } else if (pid > 0)
      waitpid(pid, nullptr, 0);
  }
  void load_help(const std::string &fn) {
    std::ifstream f(fn);
    if (!f) {
      std::cout << "Warning: could not open " << fn << "\n";
      return;
    }
    std::string line, cw, cb;
    auto flush = [&] {
      if (!cw.empty())
        help_db[cw] = cb;
    };
    while (std::getline(f, line)) {
      if (trim(line).empty()) {
        flush();
        cw.clear();
        cb.clear();
        continue;
      }
      if (line[0] != ' ' && line[0] != '\t') {
        flush();
        cw = lower(trim(line));
        cb.clear();
      } else
        cb += trim(line) + "\n";
    }
    flush();
  }
  void load_file(const std::string &fn) {
    std::ifstream f(fn);
    if (!f) {
      std::cout << "Cannot open " << fn << "\n";
      return;
    }
    std::string line, acc;
    while (std::getline(f, line)) {
      line = trim(line);
      if (line.empty() || (line.size() > 1 && line[0] == '#' && line[1] == '!'))
        continue;
      acc += (acc.empty() ? "" : " ") + line;
      // Count quotes, ignoring \ line-comment portions
      int q = 0;
      {
        bool in_comment = false;
        for (int ci = 0; ci < (int)acc.size(); ci++) {
          if (acc[ci] == '\\' && ci + 1 < (int)acc.size() &&
              acc[ci + 1] == ' ') {
            in_comment = true;
          }
          if (acc[ci] == '\n')
            in_comment = false;
          if (!in_comment && acc[ci] == '"')
            q++;
        }
      }
      if (q % 2 == 0) {
        process(split(acc));
        acc.clear();
      }
    }
    if (!acc.empty())
      process(split(acc));
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
    std::vector<std::string> o;
    std::istringstream ss(s);
    std::string t;
    while (ss >> t)
      o.push_back(t);
    return o;
  }
};

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
            first == "bye" || first == "help" || first == "see")
          wrap = false;
        Entry *e = find(first);
        if (e && e->kind == Entry::DEFINING)
          wrap = false;
      }
      if (wrap) {
        for (auto &tok : tokens) {
          std::string lt = lower(tok);
          if (lt == "create" || lt == ":") {
            wrap = false;
            break;
          }
          Entry *e = find(lt);
          if (e && e->kind == Entry::DEFINING) {
            wrap = false;
            break;
          }
        }
      }
      if (wrap)
        process(split(": __anon__ " + line + " ; __anon__"));
      else
        process(tokens);
      std::cout << " ok\n";
    } catch (std::exception &e) {
      std::cout << "Error: " << e.what() << "\n";
      stack_top = 0;
      rstack_top = 0;
      call_depth = 0;
      lframes.clear();
      cstack.clear();
      prog = Code{};
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
