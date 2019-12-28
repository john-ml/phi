# Misc. 

## Type aliases / type declarations

Use
```elm
alias X = ...
```

to define a type alias (`X` is just another name for `...`) and
```elm
type X = ...
```
to define a new type.

`⟦ alias X = ... ⟧` ==> replace `X` with `⟦...⟧` from this point on while parsing

`⟦ type X = ... ⟧` ==> `%⟦X⟧ = type { ⟦...⟧ }`

# Targetting `phi`

## Evaluating away fancy features

- "Higher" stuff (inline):
    - Higher order functions
    - Higher rank polymorphism
    - Higher-kinded types
- Polymorphism (monomorphize + specialize typeclasses/traits)
    - Can be viewed as a special case of "inlining higher stuff"
- Closure stuff:
    - Currying (uncurry)
        - Best done after no polymorphism left. 
            Otherwise, really polymorphic functions are problematic;
            e.g. `forall a. a -> a` (what if `a := _ -> _`?).
    - Partial application (eta-expand)
        - Best done before uncurrying so every call is saturated
        - May not be necessary if getting rid of all higher order functions
    - Non-tail-recursive functions where the continuation of every recursive call is "constructor-like"
        (make tail calls using mutation + hole-passing)
    - Non-tail-recursive nested functions which capture variables (lambda lift)
        - Ideally, these functions can't escape upwards because of uncurrying/eta expansion
    - Explicit opt-in closures which get defunctionalized (e.g. dlist, nbe, lazy thunks)

## Mutable updates

It'd be nice to turn

```ocaml
let f(x: *i32): *i32 = new *x + 1
```

into

```ocaml
let f(x: *i32): *i32 =
  *x <- *x + 1;
  x
```

and

```ocaml
type L = *{i32, L}
let rec f(xs: L): L =
  match L {
    null => null,
    *{x, xs} => new {x + 1, f(xs)}
  }
```

into

```ocaml
let rec f(xs: L): L =
  match L {
    null => null,
    *{x, xs'} =>
      xs <- {x + 1, f(xs')};
      xs
  }
```

which are both possible if the argument to `f` is a unique pointer.

There may also be multiple modes of use; e.g.

```ocaml
let rec f(xs: L, ys: L): L =
  match xs, ys {
    null, _ => null,
    _, null => null,
    *{x, xs'}, *{y, ys'} => new {add(x, y), f(xs', ys')}
  }
```

could choose to mutate either `xs` or `ys`.

Maybe this can be done as follows:
- Want to use region-based memory management (with mini per-region gc if necessary)
    to allow for sharing and cycles
- At same time, try to infer which pointers are "Rust-like" i.e. basically are
    unique/owning pointer to a tree-like data structure where every substructure is
    also unique
- Instead of autofreeing when these pointers fall out of scope (region will handle
    freeing everything), can reuse for new values ==> effectively get mutable update