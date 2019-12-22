# phi

LLVM has a surprising number of fancy features that would be nice to have in a high-level
language, such as
- [functional update of structures](https://llvm.org/docs/LangRef.html#i-insertvalue),
- [fixed size arrays that can be passed by value](https://llvm.org/docs/LangRef.html#array-type),
- [vector types supporting SIMD operations](https://llvm.org/docs/LangRef.html#vector-type), and
- [arbitrary bit width integers](https://llvm.org/docs/LangRef.html#integer-type).

Taking advantage of the fact that SSA happens to look
[a lot like functional programming](https://www.cs.princeton.edu/~appel/papers/ssafun.pdf),
this is a simple functional language which essentially allows one to write programs directly
in LLVM IR. The programs are just dressed up in ML syntax and written as mutually recursive
functions to make it bearable for humans.

Todo:
- [x] Parser, typechecker, and code generator for integer arithmetic + recursive functions
- [ ] More aggressive basic block selection
- [ ] Allocas
- [ ] Load/store/functional update/GEP
- [ ] Aggregates (structs, vectors, arrays)
- [ ] Extern declarations
- [ ] Type aliases
- [ ] (Recursive) type declarations
- [ ] Infix parsing