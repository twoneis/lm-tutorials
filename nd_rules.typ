#import "@preview/curryst:0.6.0": prooftree, rule
#import "rules.typ": *

#set page(flipped: true, columns: 2)
 
#let hypo(hypo, premise, name) = {
  rule(
    stack(
      align(center)[#name : $hypo$],
      align(center)[$dot$],
      align(center)[$dot$],
      align(center)[$$],
      align(center)[$premise$]
    ),
  )
}

#let group = grid.with(columns: (1fr, 1fr), gutter: 20pt, align: (center+bottom))
#let heading = grid.cell.with(colspan: 2)

#group(
  heading[== Implication],
  grid.cell[
    #prooftree(
      impl-i([h])(
        hypo($A$, $B$, [h]),
        $A -> B$
      )
    )
  ],
  grid.cell[
    #prooftree(
      impl-e( 
        $A -> B$, $A$,
        $B$
      )
    )
  ],
)

#group(
  heading[== Negation],
  grid.cell[
    #prooftree(
      not-i([h])(
        hypo($A$, $bot$, [h]),
        $not A$
      )
    )
  ],
  grid.cell[
    #prooftree(
      not-e(
        $not A$, $A$,
        $bot$
      )
    )
  ]
)

#group(
  heading[== Contradiction],
  grid.cell(colspan: 2)[
    #prooftree(
      raa([h])(
        hypo($not A$, $bot$, [h]),
        $A$
      )
    )
  ],
)

#group(
  heading[== Truth and falsity],
  grid.cell[
    #prooftree(
      truth-i(
        $top$
      )
    )
  ],
  grid.cell[
    #prooftree(
      false-e(
        $bot$,
        $A$
      )
    )
  ],
)

#colbreak()

#group(
  heading[== Conjunction],
  grid.cell[
    #prooftree(
      and-el(
        $A and B$,
        $A$
      )
    )
  ],
  grid.cell[
    #prooftree(
      and-er(
        $A and B$,
        $B$
      )
    )
  ],
  grid.cell(colspan: 2)[
    #prooftree(
      and-i(
        $A$, $B$,
        $A and B$
      )
    )
  ],
)

#group(
  heading[== Disjunction],
  grid.cell[
    #prooftree(
      or-il(
        $A$,
        $A or B$
      )
    )
  ],
  grid.cell[
    #prooftree(
      or-ir(
        $B$,
        $A or B$
      )
    )
  ],
  grid.cell(colspan: 2)[
    #prooftree(
      or-e([h])(
        $A or B$, hypo($A$, $C$, [hl]), hypo($B$, $C$, [hr]),
        $C$
      )
    )
  ]
)

#group(
  heading[== Bi-Implication],
  grid.cell[
    #prooftree(
      bi-el(
        $A <-> B$, $A$,
        $B$
      )
    )
  ],
  grid.cell[
    #prooftree(
      bi-er(
        $A <-> B$, $B$,
        $A$
      )
    )
  ],
  grid.cell(colspan: 2)[
    #prooftree(
       bi-i([h])(
        hypo($B$, $A$, [hl]), hypo($A$, $B$, [hr]),
        $A <-> B$
      )
    )
  ],
)

#colbreak()

#group(
  align: (center+top),
  heading[== Universal Quantifier],
  grid.cell[
    #prooftree(
      forall-i(
        $A(a)$,
        $forall x A(x)$
      )
    )
    $a$ must not be free in any uncanceled hypothesis
  ],
  grid.cell[
    #prooftree(
      forall-e(
        $forall x A(x)$,
        $A(a)$
      )
    )
  ]
)

#group(
  align: (center+horizon),
  heading[== Existential Quantifier],
  grid.cell[
    #prooftree(
      exists-i(
        $A(a)$,
        $exists x, A(x)$
      )
    )
  ],
  grid.cell[
    #prooftree(
      exists-e([h])(
        $exists x A(x)$, hypo($A(a)$, $B$, [h]),
        $B$
      )
    )
    $a$ must not be free in B or any uncanceled hypothesis
  ]
)

#colbreak()

#group(
  heading[== Equality],
  grid.cell[
    #prooftree(
      refl(
        $t = t$
      )
    )
  ],
  grid.cell[
    #prooftree(
      symm(
        $t = s$,
        $s = t$
      )
    )
  ],
  grid.cell[
    #prooftree(
      trans(
        $r = s$, $s = t$,
        $r = t$
      )
    )
  ],
  grid.cell[
    #prooftree(
      subst-1(
        $s = t$,
        $P(s) = P(t)$
      )
    )
  ],
  grid.cell(colspan: 2)[
    #prooftree(
      subst-2(
        $s = t$, $P(s)$,
        $P(t)$
      )
    )
  ],
)
