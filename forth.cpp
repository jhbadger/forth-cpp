#include <iostream>
#include <fstream>
#include <sstream>
#include <vector>
#include <cstring>
#include <string>
#include <unordered_map>
#include <functional>
#include <variant>
#include <stdexcept>
#include <algorithm>
#include <cassert>
#include <unistd.h>
#include <sys/wait.h>

// Stack cells can hold integers or strings (for future extension).
using Value = std::variant<int, std::string>;

static int as_int(const Value& v) {
	if (auto* p = std::get_if<int>(&v)) return *p;
	throw std::runtime_error("Expected integer on stack");
}

// - Instruction --------------------------------------------------------------
struct Ins {
	std::string op;
	int         ival  = 0;
	std::string sval;
	std::vector<std::string> names; // for locals-enter
};

static Ins make(std::string op)                        { Ins i; i.op=op; return i; }
static Ins make(std::string op, int v)                 { Ins i; i.op=op; i.ival=v; return i; }
static Ins make(std::string op, std::string s)         { Ins i; i.op=op; i.sval=s; return i; }
static Ins make(std::string op, int v, std::string s)  { Ins i; i.op=op; i.ival=v; i.sval=s; return i; }

// -- Dict entry ---------------------------------------------------------------
struct Entry {
	enum Kind { PRIM, WORD, DEFINING, CREATE } kind;
	std::function<void()>    prim;
	std::vector<Ins>         code;      // init code (WORD/DEFINING)
	std::vector<Ins>         does_code; // DEFINING does> / CREATE body
	int                      body_addr = 0; // CREATE
};

// -- Forth interpreter ---------------------------------------------------------
class Forth {
public:
	Forth() : heap(1, 10) {}  // heap[0] = BASE = 10

	void repl();

private:
	std::vector<Value>               stack;
	std::vector<Value>               rstack;    // holds int or vector<Value> (locals frame)
	std::vector<std::string>         locals;
	std::unordered_map<std::string, Entry> dict;

	bool        compiling = false;
	std::string current;
	std::vector<Ins> prog;
	std::vector<int> cstack;
	int         does_pos = -1;

	int              base_addr = 0;
	std::vector<int> heap;

	// Locals frames live on a separate typed stack to keep rstack simple
	std::vector<std::vector<int>> lframes;

	// -- stack helpers ------------------------------------------------------
	Value pop() {
		if (stack.empty()) throw std::runtime_error("Stack underflow");
		Value v = stack.back(); stack.pop_back(); return v;
	}
	int popi() { return as_int(pop()); }
	void push(Value v) { stack.push_back(v); }
	void push(int v)   { stack.push_back(v); }

	Value rpop() {
		if (rstack.empty()) throw std::runtime_error("Return stack underflow");
		Value v = rstack.back(); rstack.pop_back(); return v;
	}
	void rpush(Value v) { rstack.push_back(v); }

	void emit(Ins ins) { prog.push_back(ins); }

	// -- number helpers -----------------------------------------------------
	std::string format_int(int n, int base) {
		if (n == 0) return "0";
		const char* digits = "0123456789abcdef";
		bool neg = n < 0;
		if (neg) n = -n;
		std::string result;
		while (n > 0) { result = digits[n % base] + result; n /= base; }
		return neg ? "-" + result : result;
	}

	std::pair<bool,int> try_parse(const std::string& t) {
		int base = heap[base_addr];
		bool neg = !t.empty() && t[0] == '-';
		std::string s = neg ? t.substr(1) : t;
		if (s.empty()) return {false,0};
		int n = 0;
		for (char c : s) {
			const char* p = strchr("0123456789abcdef", std::tolower(c));
			if (!p) return {false,0};
			int d = (int)(p - "0123456789abcdef");
			if (d >= base) return {false,0};
			n = n * base + d;
		}
		return {true, neg ? -n : n};
	}

	void edit_file(std::string filename) {
    const char* editor = std::getenv("EDITOR");
    if (!editor) editor = "vi";
		
    pid_t pid = fork();
    if (pid == 0) {
			execlp(editor, editor, filename.c_str(), nullptr);
			_exit(1);
    } else if (pid > 0) {
			waitpid(pid, nullptr, 0);
    }
	}
        
	void load_file(std::string filename) {
		std::ifstream f(filename);
		if (!f) { std::cout << "Cannot open " << filename << "\n"; return; }
		std::string line;
		while (std::getline(f, line)) {
			line = trim(line);
			if (line.empty()) continue;
			process(split(line));
		}
	}
	
	static std::string lower(std::string s) {
		std::transform(s.begin(), s.end(), s.begin(), ::tolower);
		return s;
	}

	static std::string trim(const std::string& s) {
		size_t a = s.find_first_not_of(" \t\r\n");
		if (a == std::string::npos) return "";
		size_t b = s.find_last_not_of(" \t\r\n");
		return s.substr(a, b-a+1);
	}

	static std::vector<std::string> split(const std::string& s) {
		std::vector<std::string> out;
		std::istringstream ss(s);
		std::string tok;
		while (ss >> tok) out.push_back(tok);
		return out;
	}

	// -- bytecode runner ----------------------------------------------------
	void run(const std::vector<Ins>& code) {
		for (int pc = 0; pc < (int)code.size(); pc++) {
			const Ins& ins = code[pc];
			if (ins.op == "lit") {
				push(ins.ival);
			} else if (ins.op == "strlit") {
				std::cout << ins.sval;
			} else if (ins.op == "call") {
				run_word(ins.sval);
			} else if (ins.op == "branch") {
				pc = ins.ival - 1;
			} else if (ins.op == "0branch") {
				if (popi() == 0) pc = ins.ival - 1;
			} else if (ins.op == "exit") {
				return;
			} else if (ins.op == "local@") {
				push(lframes.back()[ins.ival]);
			} else if (ins.op == "local!") {
				lframes.back()[ins.ival] = popi();
			} else if (ins.op == "locals-enter") {
				lframes.push_back(std::vector<int>(ins.ival, 0));
			} else if (ins.op == "locals-exit") {
				lframes.pop_back();
			} else if (ins.op == "(do)") {
				int start = popi(), limit = popi();
				// encode do-frame as two ints on rstack (limit then index)
				rpush(limit); rpush(start);
			} else if (ins.op == "(loop)") {
				int idx   = as_int(rstack.back()); rstack.pop_back();
				int limit = as_int(rstack.back());
				idx++;
				if (idx < limit) {
					rstack.back() = limit;
					rpush(idx);
					pc = ins.ival - 1;
				} else {
					rstack.pop_back(); // remove limit
				}
			} else if (ins.op == "push-addr") {
				push(ins.ival);
			}
		}
	}

	void run_word(const std::string& raw) {
		std::string w = lower(raw);
		auto it = dict.find(w);
		if (it != dict.end()) {
			Entry& e = it->second;
			switch (e.kind) {
			case Entry::PRIM:     e.prim(); break;
			case Entry::WORD:     run(e.code); break;
			case Entry::CREATE:
				push(e.body_addr);
				if (!e.does_code.empty()) run(e.does_code);
				break;
			case Entry::DEFINING: break; // only invoked via process()
			}
			return;
		}
		auto [ok, n] = try_parse(w);
		if (ok) { push(n); return; }
		throw std::runtime_error("Unknown word: " + w);
	}

	// -- primitives ---------------------------------------------------------
	void init_prims() {
		auto prim = [&](std::string name, std::function<void()> fn) {
			Entry e; e.kind = Entry::PRIM; e.prim = fn;
			dict[name] = e;
		};

		// Arithmetic
		prim("+",   [&]{ int b=popi(),a=popi(); push(a+b); });
		prim("-",   [&]{ int b=popi(),a=popi(); push(a-b); });
		prim("*",   [&]{ int b=popi(),a=popi(); push(a*b); });
		prim("/",   [&]{ int b=popi(),a=popi(); push(a/b); });
		prim("mod", [&]{ int b=popi(),a=popi(); push(a%b); });

		// Return stack
		prim(">r",  [&]{ rpush(pop()); });
		prim("r>",  [&]{ push(rpop()); });

		// Stack ops
		prim("dup",  [&]{ push(stack.back()); });
		prim("drop", [&]{ pop(); });
		prim("swap", [&]{ Value b=pop(),a=pop(); push(b); push(a); });
		prim("over", [&]{ push(stack[stack.size()-2]); });
		prim("rot",  [&]{ Value c=pop(),b=pop(),a=pop(); push(b); push(c); push(a); });

		// Comparisons
		prim("=",  [&]{ int b=popi(),a=popi(); push(a==b?1:0); });
		prim("<",  [&]{ int b=popi(),a=popi(); push(a< b?1:0); });
		prim(">",  [&]{ int b=popi(),a=popi(); push(a> b?1:0); });
		prim("0=", [&]{ push(popi()==0?1:0); });

		// Bases
		prim("base",    [&]{ push(base_addr); });
		prim("hex",     [&]{ heap[base_addr]=16; });
		prim("decimal", [&]{ heap[base_addr]=10; });
		prim("octal",   [&]{ heap[base_addr]=8;  });
		prim("binary",  [&]{ heap[base_addr]=2;  });

		// Memory
		prim("@", [&]{
			int addr = popi();
			if (addr<0||addr>=(int)heap.size()) throw std::runtime_error("Invalid heap address "+std::to_string(addr));
			push(heap[addr]);
		});
		prim("!", [&]{
			int addr = popi();
			int val  = popi();
			if (addr<0||addr>=(int)heap.size()) throw std::runtime_error("Invalid heap address "+std::to_string(addr));
			heap[addr] = val;
		});

		prim("cell+", [&]{ push(popi()+1); });
    prim("cells", [&]{ /* no-op */ });
    prim(",",     [&]{ heap.push_back(popi()); });
		prim("here",  [&]{ push(heap.size()); });
		prim("c,",    [&]{ heap.push_back(popi()); });		 
    prim("create",[&]{ /* no-op */ });

    // Output
		prim(".",    [&]{ std::cout << format_int(popi(), heap[base_addr]) << " "; });
		prim("emit", [&]{ std::cout << (char)popi(); });
		prim("cr",   [&]{ std::cout << "\n"; });
		prim(".s",   [&]{
			std::cout << "Stack: [";
			for (size_t i=0;i<stack.size();i++) {
				if (i) std::cout << ", ";
				std::cout << as_int(stack[i]);
			}
			std::cout << "]\n";
		});

		// Loop index
		prim("i", [&]{
			// top of rstack is current index (pushed after limit)
			push(as_int(rstack.back()));
		});

		// Allot
		prim("allot", [&]{
			int n = popi();
			heap.resize(heap.size()+n, 0);
		});

		// Words
		prim("words", [&]{
			std::vector<std::string> names;
			for (auto& kv : dict) names.push_back(kv.first);
			std::sort(names.begin(), names.end());
			for (auto& n : names) std::cout << n << " ";
			std::cout << "\n";
		});
    // Misc
		prim("include", [&] { /* no-op just to add to words */ });
    prim("edit", [&] { /* no-op just to add to words */ });            
    prim("see", [&] { /* no-op just to add to words */ });
		prim("bye", [&]{ /* no-op just to add to words */ });                
	}

	// -- string literal collector -------------------------------------------
	// Returns {string, new_index}
	std::pair<std::string,int> collect_string(const std::vector<std::string>& tokens, int i, char delim) {
		std::string result;
		while (true) {
			i++;
			if (i >= (int)tokens.size())
				throw std::runtime_error("Unterminated .\" string");
			if (tokens[i].back() == delim) {
				result += tokens[i].substr(0, tokens[i].size()-1);
				return {result, i};
			}
			result += tokens[i] + " ";
		}
	}

	// -- SEE decompiler helper ----------------------------------------------
	void see_code(const std::vector<Ins>& code) {
		for (auto& ins : code) {
			if      (ins.op=="lit")          std::cout << "  lit " << ins.ival << "\n";
			else if (ins.op=="strlit")       std::cout << "  .\" " << ins.sval << "\"\n";
			else if (ins.op=="call")         std::cout << "  " << ins.sval << "\n";
			else if (ins.op=="branch")       std::cout << "  branch " << ins.ival << "\n";
			else if (ins.op=="0branch")      std::cout << "  0branch " << ins.ival << "\n";
			else if (ins.op=="(do)")         std::cout << "  do\n";
			else if (ins.op=="(loop)")       std::cout << "  loop\n";
			else if (ins.op=="exit")         std::cout << "  exit\n";
			else if (ins.op=="locals-enter") {
				std::cout << "  { ";
				for (auto& n : ins.names) std::cout << n << " ";
				std::cout << "-- }\n";
			}
			else if (ins.op=="locals-exit")  {}
			else if (ins.op=="local@")       std::cout << "  " << ins.sval << "\n";
			else if (ins.op=="local!")       std::cout << "  -> " << ins.sval << "\n";
			else                             std::cout << "  [" << ins.op << " " << ins.ival << " " << ins.sval << "]\n";
		}
	}

	// -- token processor ----------------------------------------------------
	void process(const std::vector<std::string>& tokens) {
		for (int i = 0; i < (int)tokens.size(); i++) {
			std::string t = lower(tokens[i]);

			// Line comment
			if (t == "\\") break;

			// Block comment
			if (t == "(") {
				i++;
				while (i < (int)tokens.size() && tokens[i] != ")") i++;
				continue;
			}

			// String literal
			if (t == ".\"" || t == ".(") {
				char delim = t[1];
        if (delim == '(') delim = ')'; // match parens 
				auto [s, ni] = collect_string(tokens, i, delim);
				i = ni;
				if (!compiling) std::cout << s;
				else            emit(make("strlit", s));
				continue;
			}

			if (!compiling) {
				if (t == "include") {
					std::string filename = tokens[++i];
          load_file(filename);          
					continue;
				}

				if (t == "edit") {
					std::string filename = tokens[++i];
					edit_file(filename);
					continue;
				}
				if (t == "see") {
					std::string name = lower(tokens[++i]);
					auto it = dict.find(name);
					if (it == dict.end()) { std::cout << "Unknown word: " << name << "\n"; continue; }
					Entry& e = it->second;
					switch (e.kind) {
					case Entry::PRIM:
						std::cout << name << " is a primitive\n"; break;
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
						std::cout << name << " is a created word, body addr=" << e.body_addr << "\n";
						break;
					}
					continue;
				}

				if (t == ":") {
					current   = lower(tokens[++i]);
					prog      = {};
					does_pos  = -1;
					compiling = true;
					continue;
				}

				// Defining word invocation
				auto it = dict.find(t);
				if (it != dict.end() && it->second.kind == Entry::DEFINING) {
					std::string new_name = lower(tokens[++i]); 
					int body_addr = (int)heap.size();
    
					// Create the new child word entry
					Entry ne;
					ne.kind      = Entry::CREATE;
					ne.body_addr = body_addr;
					ne.does_code = it->second.does_code; // Inherit the behavior after does>
					dict[new_name] = ne;

					run(it->second.code); 
					continue;
				}
				
				run_word(t);
				continue;
			}

			// -- compile mode ----------------------------------------------

			if (t == ";") {
				if (!locals.empty()) emit(make("locals-exit"));
				emit(make("exit"));
				locals.clear();

				Entry e;
				if (does_pos >= 0) {
					e.kind      = Entry::DEFINING;
					e.code      = std::vector<Ins>(prog.begin(), prog.begin()+does_pos);
					e.does_code = std::vector<Ins>(prog.begin()+does_pos, prog.end());
				} else {
					e.kind = Entry::WORD;
					e.code = prog;
				}
				dict[current] = e;
				compiling = false;
				does_pos  = -1;
				continue;
			}

			if (t == "does>") { does_pos = (int)prog.size(); continue; }
			
			if (t == "recurse") { emit(make("call", current)); continue; }

			if (t == "if")   { emit(make("0branch",0)); cstack.push_back((int)prog.size()-1); continue; }
			if (t == "else") {
				emit(make("branch",0));
				int prev = cstack.back(); cstack.pop_back();
				prog[prev].ival = (int)prog.size();
				cstack.push_back((int)prog.size()-1);
				continue;
			}
			if (t == "then") {
				int prev = cstack.back(); cstack.pop_back();
				prog[prev].ival = (int)prog.size();
				continue;
			}
			if (t == "do")   { emit(make("(do)")); cstack.push_back((int)prog.size()); continue; }
			if (t == "loop") {
				int addr = cstack.back(); cstack.pop_back();
				emit(make("(loop)", addr));
				continue;
			}

			if (t == "{") {
				std::vector<std::string> names;
				while (true) {
					i++;
					if (i>=(int)tokens.size() || tokens[i]=="}") break;
					if (tokens[i]=="--") {
						// skip everything after -- including }
						while (i < (int)tokens.size() && tokens[i] != "}") i++;
						break;
					}
					names.push_back(tokens[i]);
				}
				Ins ins = make("locals-enter", (int)names.size());
				ins.names = names;
				emit(ins);
				for (int j=(int)names.size()-1; j>=0; j--)
					emit(make("local!", j, names[j]));
				locals = names;
				continue;
			}

			// Local read
			{
				auto lit = std::find(locals.begin(), locals.end(), t);
				if (lit != locals.end()) {
					int idx = (int)(lit - locals.begin());
					emit(make("local@", idx, t));
					continue;
				}
			}

			if (t == "->") {
				std::string lname = tokens[++i];
				auto lit = std::find(locals.begin(), locals.end(), lname);
				if (lit == locals.end()) throw std::runtime_error("Unknown local: " + lname);
				int idx = (int)(lit - locals.begin());
				emit(make("local!", idx, lname));
				continue;
			}

			auto [ok, n] = try_parse(t);
			if (ok) { emit(make("lit", n)); continue; }
			emit(make("call", t));
		}
	}
};

// -- REPL ----------------------------------------------------------------------
void Forth::repl() {
	init_prims();
	std::cout << "Mini C++ Forth\n";
	std::string dir = DIR; // Access the preprocessor macro as a string
  	std::string filepath = trim(dir) + "/stdlib.fs";
	load_file(filepath);
	
	while (true) {
		std::cout << "> " << std::flush;
		std::string line;
		if (!std::getline(std::cin, line)) break;
		line = trim(line);
		if (line == "bye") break;
		if (line.empty()) continue;
		try {
			process(split(line));
			std::cout << " ok\n";
		} catch (std::exception& e) {
			std::cout << "Error: " << e.what() << "\n";
			stack.clear();
			rstack.clear();
			lframes.clear();
			cstack.clear();
			prog.clear();
			compiling = false;
			does_pos  = -1;
		}
	}
}

int main(int argc, char * argv[]) {
	Forth().repl();
	return 0;
}
