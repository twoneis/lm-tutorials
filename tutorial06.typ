#import "@preview/polylux:0.4.0": *
#import "@preview/curryst:0.6.0": prooftree, rule
#import "rules.typ": *

#set page(paper: "presentation-4-3")
#set text(size: 18pt)
#set align(center)

#let wrong = text.with(red)
#let alt = alternatives.with(repeat-last: true)


// Problem 1: Implication associativity


#slide[
  == What is wrong or missing?
  === Show a derivation for $R tack.r P -> Q -> R$
  #linebreak()

  #hypos(
    [h : $R$],
    [|],
    [#alt[1 : $P -> Q$][1 : #wrong[$P -> Q$]]],
  )

  #prooftree(
    impl-i([1])(
      th([h])(alt[$R$][#wrong[$R$]]),
      $P -> Q -> R$
    )
  )

  #uncover(2)[#wrong[Implication is right associative, the implicit parantheses are $P -> (Q -> R)$]]
]

#slide[
  == Correct solution
  === Show a derivation for $R tack.r P -> Q -> R$
  #linebreak()

  #hypos(
    [h : $R$],
    [|],
    [1 : $P$],
    [|],
    [2: $Q$],
  )

  #prooftree(
    impl-i([1])(
      impl-i([2])(
        th([h])($R$),
        $Q -> R$
      ),
      $P -> Q -> R$
    )
  )
]


// Problem 2: Exists elim on free variable


#slide[
  == What is wrong or missing?
  === Show a derivation for $forall x (Q(x)), exists x (Q(x) -> P(x)) tack.r exists x (P(x))$
  #linebreak()

  #hypos(
    [h1 : $forall x (Q(x))$],
    [|],
    [h2 : $exists x (Q(x) -> P(x))$],
    [|],
    [1 : #alt[$Q(a) -> P(a)$][#wrong[$Q(a) -> P(a)$]]]
  )
  
  #prooftree(
    exists-i(
      exists-e([1])(
        th([h2])($exists x (Q(x) -> P(x))$),
        impl-e(
          th([1])(alt[$Q(a) -> P(a)$][#wrong($Q(a) -> P(a)$)]),
          forall-e(
            th([h1])($forall x (Q(x))$),
            $Q(a)$
          ),
          alt[$P(a)$][$P(wrong(a))$]
        ),
        alt[$P(a)$][$P(wrong(a))$]
      ),
      $exists x (P(x))$
    ),
  )

  #uncover(2)[#wrong[In an existential elimination (and universal introduction) the new free variable may not already be in any hypothesis or goal]]
]

#slide[
  == Correct solution
  === Show a derivation for $forall x (Q(x)), exists x (Q(x) -> P(x)) tack.r exists x (P(x))$
  #linebreak()

  #hypos(
    [h1 : $forall x (Q(x))$],
    [|],
    [h2 : $exists x (Q(x) -> P(x))$],
    [|],
    [1 : $Q(a) -> P(a)$],
  )
  
  #prooftree(
    exists-e([1])(
      th([h2])($exists x (Q(x) -> P(x))$),
      exists-i(
        impl-e(
          th([1])($Q(a) -> P(a)$),
          forall-e(
            th([h1])($forall x (Q(x))$),
            $Q(a)$
          ),
          $P(a)$
        ),
        $exists x (P(x))$
      ),
      $exists x (P(x))$
    ),
  )
]


// Problem 3: Applying deduction rules not strictly matching rules


#slide[
  == What is wrong or missing?
  === Show a derivation for $exists x (P(x) or Q(x)) tack.r exists x (P(x)) or exists x (Q(x))$
  #linebreak()

  #hypos(
    [h1 : $exists x (P(x) or Q(x))$],
    [|],
    [1 : $P(a) or Q(a)$]
  )
  
  #prooftree(
    exists-e([1])(
      th([h1])($exists x (P(x) or Q(x))$),
      exists-i(
        exists-i(
          th([1])(alt[$P(a) or Q(a)$][#wrong[$P(a) or Q(a)$]],),
          alt[$P(a) or exists x (Q(x))$][#wrong[$P(a) or exists x (Q(x))$]],
        ),
        alt[$exists x (P(x)) or exists x (Q(x))$][$exists x (P(x)) wrong(or) exists x (Q(x))$],
      ),
      $exists x (P(x)) or exists x (Q(x))$
    )
  )

  #uncover(2)[#wrong[Natural deduction rules can only be applied if the pattern is precisely matched on the full expression. Applying the rules to subexpressions directly is not allowed.]]
]

#slide[
  == Correct solution
  === Show a derivation for $exists x (P(x) or Q(x)) tack.r exists x (P(x)) or exists x (Q(x))$
  #linebreak()

  #hypos(
    [h1 : $exists x (P(x) or Q(x))$],
    [|],
    [1 : $P(a) or Q(a)$],
    [|],
    [2l : $P(a)$],
    [|],
    [2r : $Q(a)$],
  )

  #prooftree(
    exists-e([1])(
      th([h1])($exists x (P(x) or Q(x))$),
      or-e([2])(
        th([1])($P(a) or Q(a)$),
        or-il(
          exists-i(
            th([2l])($P(a)$),
            $exists x (P(x))$
          ),
          $exists x (P(x)) or exists x (Q(x))$
        ),
        or-ir(
          exists-i(
            th([2r])($Q(a)$),
            $exists x (Q(x))$
          ),
          $exists x (P(x)) or exists x (Q(x))$
        ),
        $exists x (P(x)) or exists x (Q(x))$
      ),
      $exists x (P(x)) or exists x (Q(x))$
    )
  )
]


// Problem 4: Missing conclusion


#slide[
  == What is wrong or missing?
  === Show that $forall x (Q(x)) -> exists x (Q(x) -> P(x)) -> exists x (P(x))$ is valid
  #linebreak()

  #hypos(
    [1 : $forall x (Q(x))$],
    [|],
    [2 : $exists x (Q(x) -> P(x))$],
    [|],
    [3 : $Q(a) -> P(a)$],
  )
  
  #prooftree(
    impl-i([1])(
      impl-i([2])(
        exists-e([3])(
          th([h2])($exists x (Q(x) -> P(x))$),
          exists-i(
            impl-e(
              th([1])($Q(a) -> P(a)$),
              forall-e(
                th([h1])($forall x (Q(x))$),
                $Q(a)$
              ),
              $P(a)$
            ),
            $exists x (P(x))$
          ),
          $exists x (P(x))$
        ),
        $exists x (Q(x) -> P(x)) -> exists x (P(x))$,
      ),
      $forall x (Q(x)) -> exists x (Q(x) -> P(x)) -> exists x (P(x))$
    )
  )

  #uncover(2)[#wrong[For validity we need to show a semantic entailment ($tack.double.r$) but a derivation shows syntactic entailment ($tack.r$)]]
]

#slide[
  == Correct solution
  === Show that $forall x (Q(x)) -> exists x (Q(x) -> P(x)) -> exists x (P(x))$ is valid
  #linebreak()

  #hypos(
    [1 : $forall x (Q(x))$],
    [|],
    [2 : $exists x (Q(x) -> P(x))$],
    [|],
    [3 : $Q(a) -> P(a)$],
  )

  #prooftree(
    impl-i([1])(
      impl-i([2])(
        exists-e([3])(
          th([h2])($exists x (Q(x) -> P(x))$),
          exists-i(
            impl-e(
              th([1])($Q(a) -> P(a)$),
              forall-e(
                th([h1])($forall x (Q(x))$),
                $Q(a)$
              ),
              $P(a)$
            ),
            $exists x (P(x))$
          ),
          $exists x (P(x))$
        ),
        $exists x (Q(x) -> P(x)) -> exists x (P(x))$,
      ),
      $forall x (Q(x)) -> exists x (Q(x) -> P(x)) -> exists x (P(x))$
    )
  )

  #linebreak()

  Conclusion: We have shown that $tack.r forall x (Q(x)) -> exists x (Q(x) -> P(x)) -> exists x (P(x))$ with the derivation above. From this, we use soundness to conclude that $tack.double.r forall x (Q(x)) -> exists x (Q(x) -> P(x)) -> exists x (P(x))$ and the formula is valid.
]


// Problem 5: Semantic equivalence only in one direction


#slide[
  == What is wrong or missing?
  === Show $forall x (P(x)) and forall x (Q(x)) equiv forall x (P(x) and Q(x))$
  #linebreak()

  #hypos(
    [h : $forall x (P(x)) and forall x (Q(x))$],
  )
  
  #prooftree(
    forall-i(
      and-i(
        forall-e(
          and-el(
            th([h])($forall x (P(x)) and forall x (Q(x))$),
            $forall x (P(x))$
          ),
          $P(a)$
        ),
        forall-e(
          and-er(
            th([h])($forall x (P(x)) and forall x (Q(x))$),
            $forall x (Q(x))$
          ),
          $Q(a)$
        ),
        $P(a) and Q(a)$
      ),
      $forall x (P(x) and Q(x))$
    )
  )

  #linebreak()

  We show that  $forall x (P(x)) and forall x (Q(x)) tack.r forall x (P(x) and Q(x))$ by the derivation given above and use soundness to conclude that $forall x (P(x)) and forall x (Q(x)) equiv forall x (P(x) and Q(x))$ .

  #uncover(2)[#wrong[For $phi equiv psi$ we need to show $phi tack.double.r psi$ and $psi tack.double.r phi$ but we have only shown one direction here. This is not enough to conclude equivalence.]]
]

#slide[
  == Correct solution
  === Show $forall x (P(x)) and forall x (Q(x)) equiv forall x (P(x) and Q(x))$
  #linebreak()
  #hypos(
    [h : $forall x (P(x)) and forall x (Q(x))$],
  )
  
  #prooftree(
    forall-i(
      and-i(
        forall-e(
          and-el(
            th([h])($forall x (P(x)) and forall x (Q(x))$),
            $forall x (P(x))$
          ),
          $P(a)$
        ),
        forall-e(
          and-er(
            th([h])($forall x (P(x)) and forall x (Q(x))$),
            $forall x (Q(x))$
          ),
          $Q(a)$
        ),
        $P(a) and Q(a)$
      ),
      $forall x (P(x) and Q(x))$
    )
  )

  _continued on next page_

  #pagebreak()

  #hypos(
    [h : $forall x (P(x) and Q(x))$],
  )
  
  #prooftree(
    and-i(
      forall-i(
        and-el(
          forall-e(
            th([h])($forall x (P(x) and Q(x))$),
            $P(a) and Q(a)$
          ),
          $P(a)$
        ),
        $forall x (P(x))$
      ),
      forall-i(
        and-er(
          forall-e(
            th([h])($forall x (P(x) and Q(x))$),
            $P(a) and Q(a)$
          ),
          $Q(a)$
        ),
        $forall x (Q(x))$
      ),
      $forall x (P(x)) and forall x (Q(x))$
    )
  )

  We show that  $forall x (P(x)) and forall x (Q(x)) tack.r forall x (P(x) and Q(x))$ and $ forall x (P(x) and Q(x)) tack.r forall x (P(x)) and forall x (Q(x))$ by the derivations given above and use soundness to conclude that $forall x (P(x)) and forall x (Q(x)) equiv forall x (P(x) and Q(x))$ .
]

