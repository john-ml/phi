# Type aliases / type declarations

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

# Partial evaluation / using `phi` as a target

Get rid of:
- Polymorphism (monomorphize + specialize typeclasses/traits)
- "Higher" stuff (inline):
    - Higher order functions
    - Higher rank polymorphism
    - Higher-kinded types
- Closure stuff:
    - Currying (uncurry)
        - Best done after no polymorphism left. 
            Otherwise, really polymorphic functions are problematic;
            e.g. `forall a. a -> a` (what if `a := _ -> _`?).
    - Partial application (eta-expand)
        - Best done before uncurrying so every call is saturated
        - Non-tail-recursive functions where the continuation of every recursive call is "constructor-like"
            (make tail calls using mutation + hole-passing)
        - Non-tail-recursive nested functions which capture variables (lambda lift)
            - Ideally, these functions can't escape upwards because of uncurrying/eta expansion