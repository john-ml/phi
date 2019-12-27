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
let f(x: *i32): *i32 = new (*x + 1)
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
    *{x, xs} =>
      x <- x + 1;
      f(xs)
  }
```