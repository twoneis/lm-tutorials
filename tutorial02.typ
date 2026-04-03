#import "@preview/curryst:0.6.0": prooftree
#import "@preview/cetz:0.4.2": canvas, draw, tree
#import "rules.typ": *

#set list(marker: none)

= Tutorial 02 Solutions
=== 2.1.1 (a)
Mary admires every professor: 
$forall x (P(x) -> A(m, x))$


=== 2.1.3
Predicates:
- P(x) : x is a prize
- B(x) : x is a boy
- W(x,y) : x won y

- (a) Every prize was won by a boy: $forall x ( P(x) -> exists y (B(y) and W(y,x)))$
- (b) A boy won every prize : $exists x (B(x) and forall y (P(y) -> W(x,y)))$

=== 2.2.4
(b) Parse tree for $exists x (P(y,z) and (forall y (not Q(y,x) or P(y,z))))$ with bound variables highlighted in the same colour as their binding.

#canvas({
  import draw: *
  set-style(content: (padding: 0.5em))
  tree.tree(
    (text(blue)[$exists x$],
      ($and$,
        ($P$,
          $y$,
          $z$
        ),
        (text(red)[$forall y$],
          ($or$,
            ($not$, ($Q$, text(red)[$y$], text(blue)[$x$])),
            ($P$, text(red)[$y$], $z$)
          )
        ),
      )
    ))
})

(d)
- $phi[w slash x]$ = $exists x (P(y,z) and (forall y (not Q(y,x) or P(y,z))))$
- $phi[w slash y]$ = $exists x (P(w,z) and (forall y (not Q(y,x) or P(y,z))))$
- $phi[f(x) slash y]$ = $exists t (P(f(x),z) and (forall y (not Q(y,t) or P(y,z))))$
- $phi[g(y,z) slash z]$ = $exists x (y,g(y,z)) and (forall s (not Q(s,x) or P(s,g(y,z)))))$

#pagebreak()

=== 2.3.7
Derivation for $exists x forall y (P(x,y)) tack.r forall y exists x (P(x, y))$

#hypos(
  [h1 : $exists x forall y (P(x,y))$],
  [h2 : $forall y (P(a,y))$],
)

#prooftree(
  exists-e([h2])(
    th([h1])($exists x forall y (P(x,y))$),
    forall-i(
      exists-i(
        forall-e(
          th([h2])($forall y (P(a,y))$),
          $P(a,b)$
        ),
        $exists x (P(x,b))$
      ),
      $forall y exists x (P(x,y))$
    ),
    $forall y exists x (P(x, y))$
  )
)

=== 2.3.9 (a)
Derivation for $exists x (S -> Q(x)) tack.r S -> exists x (Q(x))$

#hypos(
  [h1 : $exists x (S -> Q(x))$],
  [h2: $S$],
  [h3: $S -> Q a$],
)

#prooftree(
  impl-i([h2])(
    exists-e([h3])(
      th([h1])($exists x (S -> Q(x))$),
      exists-i(
        impl-e(
          th([h2])($S$),
          th([h3])($S -> Q a$),
          $Q a$
        ),
        $exists x (Q(x))$
      ),
      $exists x (Q(x))$
    ),
    $S -> exists x (Q(x))$
  )
)

=== 2.3.9 (p)
Derivation for $not forall x (not P(x)) tack.r exists x (P(x))$

#hypos(
  [h1 : $not forall x (not P(x))$],
  [h2 : $not exists x (P(x))$],
  [h3 : $P(a)$],
)

#prooftree(
  raa([h2])(
    not-e(
      th([h1])($not forall x (not P(x))$),
      forall-i(
        not-i([h3])(
          not-e(
            th([h2])($not exists x (P(x))$),
            exists-i(
              th([h3])($P(a)$),
              $exists x (P(x))$
            ),
            $bot$
          ),
          $not P(a)$
        ),
        $forall x (not P(x))$
      ),
      $bot$
    ),
    $exists x (P(x))$
  ) 
)
