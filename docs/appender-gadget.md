# A general two-contraction appender gadget

The appender used by the CTS encoding has a short, direct correctness
argument over native occurrence rewriting. It applies to arbitrary closed
S terms in every parameter, independently of the surrounding controller.

Write application left-associatively. Fix a terminal term `P` and cell
constructors `J1, ..., Jm`, and define:

```text
A([])       = P
A(J :: rest) = S (S A(rest)) J
U0          = U
Ui          = Ji U(i-1)             (1 <= i <= m)
Hi          = U(i-1) Ui
```

Here `U`, `P`, and every `Ji` are arbitrary finite closed S terms. In the
binary queue encoding, `P = S (S S)` and `Ji` is the live-cell constructor
for the corresponding bit.

## Exact occurrence-reduction lemma

Starting from `A([J1,...,Jm]) U`, contract the following sequence of
occurrence addresses, where `L` enters the left child:

```text
root, root, L, L, LL, LL, ..., L^(m-1), L^(m-1).
```

All `2m` contractions are legal and the result is exactly

```text
P Um Hm H(m-1) ... H1.
```

The empty list gives zero contractions and result `P U`.

### Proof

For arbitrary terms `N`, `J`, and `V`, two root contractions give:

```text
(S (S N) J) V
    -> (S N) V (J V)
    -> N (J V) (V (J V)).
```

Both steps are direct instances of `S x y z -> x z (y z)`. They require
no condition on the arguments and leave their internal occurrences untouched.

Induct on the constructor list. For the empty list the statement is the
definition of `A`. For `J1 :: rest`, the displayed pair changes the input to

```text
(A(rest) U1) H1.
```

Apply the induction hypothesis inside the left child. Its addresses gain
one leading `L`; its result is `P Um Hm ... H2`, while the outer argument
remains `H1`. This gives the stated result and address list. Thus every
finite constructor list satisfies the lemma.

## Histories, size and composition

The selected action retains one history argument per emitted cell, in
reverse emission order. Arbitrary redexes inside input cells and retained
histories do not affect this prescribed local sequence. The final term can
itself contain redexes; completed-action recognition uses its literal
`P` prefix and history arity.

With `N(T)` counting both application nodes and S leaves, one native
contraction at third argument `z` increases size by `N(z) - 1`.
Consequently appending `Ji` by the displayed pair increases the surrounding
tree size by exactly

```text
N(U(i-1)) + N(Ui) - 2.
```

Occurrence rewriting is closed under an arbitrary fixed tree context. The
same lemma therefore holds at any selected action-response address, with
that address prefixed to every listed contraction. This is the local
correctness fact used by the program-dependent appender rows; routing to
that occurrence is a separate controller obligation.

## Executable checks

```sh
python -m unittest discover -s tests -p test_appender_gadget.py -v
```

The tests instantiate the induction with binary words, unrelated redex-rich
parameters, arbitrary enclosing contexts and independent prefix-string
rewriting. They check every selected occurrence, exact final syntax, retained
history order and the per-pair size identity.

The appender construction follows Cinematic Strawberry's
[pinned AppenderFiniteRows definitions](https://github.com/cstrawberry/predictive-universe/blob/85a867988442fc423279341200f81634a1e65582/docs/paper/related/pure_s_universality/formalization/PureSFormal/Research/RootResetAppenderFiniteRows.lean).
The proof above is a direct derivation from the single S rule.
