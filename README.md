# dtt experiments

Experimenting with Dependent Type Theory in Rust. The goal here is to
attempt to lower MLT Terms to an SSA IR.

The core is extremely simple and as such a number of things need to
be _encoded_.

[Dependent Products](https://math.stackexchange.com/a/673003):

```
Σ : Π A : U (A → U) → U′
Σ = λA : U . λB : A → U . Π C : U (Π x : A B(x) → C) → C

sigma = \A : U
```

Here are some examples:

```
N : Type 0
Z : N
S : forall _ : N -> N
three = \f : (forall _ : N -> N) => \x : N => (f (f (f x)))
check (three S)
check (three (three S))
eval ((three (three S)) Z)
```

running this code will produce:

```
(three S) : N -> N
(three (three S)) : N -> N
((three (three S)) Z)
    = (S (S (S (S (S (S (S (S (S Z)))))))))
    : N
```

## Irrelevance

Thought: If irrelevant terms are erased, we can extract functions that don't need dependent types for computation but
still benefit from type checking.

```ocaml
Vec T .n
val Vec : Π(x : Type 0) -> (.Π(l: C) -> Type 0)

val append : Vec T .n -> Vec T .m -> Vec T .(n + m)
append: Π(T: Type0) -> (
          .Π(n: Nat) -> (
            .Π(m: Nat) -> (
              Π(_:Vec T .n) -> (
                Π(_:Vec T .m) -> (
                  Vec T .(+ n m)
                )
              )
            )
          )
        )

val erased_Vec : Π(x : Type 0) -> Type 0
val erased_append : Vec T -> Vec T -> Vec T
erased_append : Π(T: Type0) -> (
                  Π(_:Vec T) -> (
                    Π(_:Vec T) -> (
                      Vec T
                    )
                  )
                )
```

### Erasing Π Types

```
Π(x : Type 0) -> (.Π(l: C) -> Type 0)
Π(x : Type 0) -> Type 0

.Π(x:X) -> T ==> .T, erroring if .T depends on x
```

### Erasing λ Expressions

```
.λ(x:X) => E ==> .E, erroring if .E depends on x
```

### Erasing Applications

```
((Vec T) .n)
(Vec T)

.(a b) ==> .a, erroring if .a requires a parameter
```

## References

* [How to implement dependent type theory I](http://math.andrej.com/2012/11/08/how-to-implement-dependent-type-theory-i/)
* [Practical Erasure in Dependently Typed Languages](https://eb.host.cs.st-andrews.ac.uk/drafts/dtp-erasure-draft.pdf)
* [From System F to Typed Assembly Language](https://www.cs.princeton.edu/~dpw/papers/tal-toplas.pdf)
* [Compiling with Dependent Types](https://www.williamjbowman.com/resources/wjb-dissertation.pdf)
* [The Implicit Calculus of Constructions as a Programming Language with Dependent Types](http://www.lix.polytechnique.fr/Labo/Bruno.Bernardo/writings/barras-bernardo-icc-fossacs08.pdf)
