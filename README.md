# dtt experiments

Experimenting with Dependent Type Theory in Rust. The goal here is to
attempt to lower MLT Terms to an SSA IR.

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

# References

* [Practical Erasure in Dependently Typed Languages](https://eb.host.cs.st-andrews.ac.uk/drafts/dtp-erasure-draft.pdf)
* [From System F to Typed Assembly Language](https://www.cs.princeton.edu/~dpw/papers/tal-toplas.pdf)
* [Compiling with Dependent Types](https://www.williamjbowman.com/resources/wjb-dissertation.pdf)
