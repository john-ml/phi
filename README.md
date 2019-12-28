# phi

A simple functional language which basically lets you write programs in LLVM IR.
The programs are just dressed up in ML syntax and written as mutually recursive
functions to make it bearable for humans.

## TODO

- [x] Parser, typechecker, and code generator for integer arithmetic + recursive functions
- [x] More aggressive basic block selection (or better tail calls)
- [x] Allocas
- [x] Load/store/functional update/GEP
- [x] Aggregates (structs, vectors, arrays)
- [x] Extern declarations
- [ ] Type aliases
- [ ] (Recursive) type declarations
- [ ] Infix parsing