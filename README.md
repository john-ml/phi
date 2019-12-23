# phi

Taking advantage of the fact that SSA happens to look
[a lot like functional programming](https://www.cs.princeton.edu/~appel/papers/ssafun.pdf),
this is a simple functional language which essentially allows one to write programs directly
in LLVM IR. The programs are just dressed up in ML syntax and written as mutually recursive
functions to make it bearable for humans.

## TODO

- [x] Parser, typechecker, and code generator for integer arithmetic + recursive functions
- [ ] More aggressive basic block selection
- [x] Allocas
- [x] Load/store/functional update/GEP
- [x] Aggregates (structs, vectors, arrays)
- [x] Extern declarations
- [ ] Type aliases
- [ ] (Recursive) type declarations
- [ ] Infix parsing