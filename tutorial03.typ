#import "@preview/curryst:0.6.0": prooftree
#import "rules.typ": *

#set list(marker: none)

= Tutorial 03 Solutions
_Note: solution are examples, in many cases other solutions are possible_

=== Past exam questions

- (a) Satisfiable with $P : bot$ but not valid with counterexample $P : top$.
- (b) Not satisfiable. For $not S$ to hold we need $S : bot$. Then for $T -> S$ to be true, we also need $T : bot$. But now we have $not S -> T$ left which is not true under this assignment. Because we have shown finding a validation making all parts true is not possible, we conclude it is unsatisfiable.
- (c) Satisfiable e.g. with one witness for which $P$ holds but not valied with counterexample e.g. two states, one for which $P$ holds and another for which it does not.

=== 1.5.2
Solving with either a truth table or by rewriting gives (a) not equivalent and (b) equivalent.

=== LP 6.4.5
- (a) Derivable: 

  #hypos(
    [h1 : $not (not A or B)$],
    [h2 : $not A$],
  )

  #linebreak()

  #prooftree(
    impl-i([h1])(
      raa([h2])(
        not-e(
          th([h1])($not (not A or B)$),
          or-il(
            th([h2])($not A$),
            $not A or B$
          ),
          $bot$
        ),
        $A$
      ),
      $not (not A or B) -> A$
    )
  )

- (b) Not valid with counterexample $P : top$, $Q : bot$, $R : bot$

=== 2.4.8
We show a derivation for $forall x P(x) or forall x Q(x) tack.r forall x (P(x) or Q(x))$ and use soundness to conclude that $forall x P(x) or forall x Q(x) tack.double.r forall x (P(x) or Q(x))$ must also hold.

#hypos(
  [h1 : $forall x P(x) or forall x Q(x)$],
  [h2l : $forall x P(x)$],
  [h2r : $forall x Q(x)$],
)

#linebreak()

#prooftree(
  forall-i(
    or-e([h2])(
      th([h1])($forall x P(x) or forall x Q(x)$),
      or-il(
        forall-e(
          th([h2l])($forall x P(x)$),
          $P(a)$
        ),
        $P(a) or Q(a)$
      ),
      or-ir(
        forall-e(
          th([h2r])($forall x Q(x)$),
          $Q(a)$
        ),
        $P(a) or Q(a)$
      ),
      $P(a) or Q(a)$
    ),
    $forall x (P(x) or Q(x))$
  )
)

=== 2.4.10
$forall x (P(x) ∨ Q(x)) tack.double.r forall x P (x) ∨ forall x Q(x)$ is not a semantic entailment, as we can show a counterexample with two variables $a$ and $b$ such that only $P(a)$ and $Q(b)$ hold.

=== 2.4.7
// Assume a model $M$ that satisfies $forall x (not phi)$.
// We aim to show that $M$ satisfies $not exists x (phi)$ as well.
// As we know from the assumption, every variable in our universe satisfies $not phi$. 
// The existential quantifier applies to the same universe and because we know all variables have $not phi$ and cannot have both $phi$ and $not phi$, none must have $phi$, thus $not exists x (phi)$.

Assume a model $M$ that satisfies $forall x (not phi)$.
We aim to show that $M$ satisfies $not exists x (phi)$ as well.
Assume towards a contradiction $exists x (phi)$.
From this take an arbitrary witness for $x$ for which $phi$ holds.
Using the knowledge that $forall x (not phi)$ we conclude that $not phi$ must hold for this witness.
We have now shown that for the witness both $phi$ and $not phi$ hold and thus arrived at a contradiction.

=== 2.4.12(b)
We show a derivation for $tack.r exists y ((forall x P(x)) -> P(y))$. From showing this we can conclude by soundness that the formula is valid.

#hypos(
  [h1 : $forall x P(x)$]
)

#linebreak()

#prooftree(
  exists-i(
    impl-i([h1])(
      forall-e(
        th([h1])($forall x P(x)$),
        $P(a)$
      ),
      $(forall x P(x)) -> P(a)$
    ),
    $exists y ((forall x P(x)) -> P(y))$
  )
)

=== 2.5.1 (b)
Using the contrapositive of soundness we argue there exists no derivation for $forall x (P(x) -> R(x)), forall x (Q(x) → R(x)) tack.r exists x (P(x) and Q(x))$ by showing a countermodel.
A possible countermodel consists of just one variable for which none of the predicates hold.
