#import "@preview/curryst:0.6.0": prooftree
#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge
#import "rules.typ": *
#import "modal.typ": *

#set list(marker: none)

= Tutorial 04 Solutions
_Note: These solutions are examples, in many cases other solutions are possible._

=== Past exam questions
- (a) Have $a < b$, $b < c$ and $a < c$. For all other $x,y in U$ there is no relation $x < y$.

- (b) It is not a total order on $U$ as it violates the reflexivity property of a total order. This will be the case for any strict partial order picked in (a) as a property of such an order is irreflexivity. Other examples for (a) may also violate the totality property of a total order.

- (c) A possible example would be the relation where any even number is related to every even number and the same for every odd number.

=== Final exam 2025, Q3
(a)
- reflexive: $forall x, R(x, x)$
- anti-symmetric: $forall x forall y R(x, y) and R(y, x) -> x = y$
- transitive: $forall x forall y forall z R(x,y) and R(y, z) -> R(x,z)$
- maximal: $forall x R(a, x) -> a = x$
- greatest: $forall x R(x, a)$

(b)
We aim to show that for every $x$, if $x$ is related to $a$ then $a = x$.
Assume an arbitrary $b$ for $x$.
Then consider two cases:
- $not R(a, b)$: If $not R(a, b)$ then our goal trivially holds.
- $R(a, b)$: If $R(a, b)$, we aim to show $a = b$. For this purpose we use the _greatest_ property with $b$ as witness to show that R(b,a). Then using _anti-symmetry_ we can conclude that because both $R(a,b)$ and $R(b,a)$ hold, we must have that $a = b$, thus proving our goal.

(c)
#hypos(
  columns: 2,
  [reflexive: $forall x, R(x, x)$],
  [anti-symmetric: $forall x forall y R(x, y) and R(y, x) -> x = y$],
  [transitive: $forall x forall y forall z R(x,y) and R(y, z) -> R(x,z)$],
  [greatest: $forall x R(x, a)$],
  [h1 : $R(a, b)$]
)

#linebreak()

#prooftree(
  forall-i(
    impl-i([h1])(
      impl-e(
        forall-e(
          forall-e(
            th([anti-symmetric])($forall x forall y R(x, y) and R(y, x) -> x = y$),
            $forall y R(a, y) and R(y, a) -> a = y$
          ),
          $R(a, b) and R(b, a) -> a = b$
        ),
        and-i(
          th([h1])($R(a, b)$),
          forall-e(
            th([greatest])($forall x R(x, a)$),
            $R(b, a)$
          ),
          $R(a, b) and R(b, a)$
        ),
        $a = b$
      ),
      $R(a, b) -> a = b$
    ),
    $forall x R(a, x) -> a = x$
  )
)

#pagebreak()

=== Past exam question
(a)
- $M, w 1 tack.double.r.not box q$
- $M, w 2 tack.double.r box q$
- $M, w 3 tack.double.r.not box q$

(b)
- $M, w 1 tack.double.r q -> diamond diamond p$
- $M, w 2 tack.double.r q -> diamond diamond p$
- $M, w 3 tack.double.r q -> diamond diamond p$

=== HR 5.2.3
(a)

#diagram(
  node-stroke: .1em,
  world(0,0, $a$, $p$),
  edge((0,0), (1,1), "-|>"),
  edge((0,0), (0,2), "-|>", bend: -25deg),
  world(2,0, $b$, $p, q$),
  edge((2,0), (0,0), "-|>"),
  edge((2,0), (1,1), "-|>"),
  world(1,1, $c$, $p, q$),
  world(0,2, $e$, $$),
  edge((0,2), (0,0), "-|>", bend: -25deg),
  world(2,2, $d$, $q$),
  edge((2,2), (0,2), "-|>"),
)

(b)
- i. Satisfied in ${c}$
- ii. Satisfied in ${a, b}$
- iii. Satisfied in ${a,  b, e}$
- iv. Satisfied in ${a, b, e}$
- v. Satisfied in ${b, c, d, e}$
- vi. Satisfied in ${a, b, c, d, e}$

#pagebreak()

=== HR 5.2.5
(a) In this model, $w 1 tack.double.r box p$ but $w 1 tack.double.r.not box box p$.

#diagram(
  node-stroke: .1em,
  world(0, 0, $w 1$, $$),
  edge((0,0), (1,0), "-|>", bend: 25deg),
  edge((1,0), (0,0), "-|>", bend: 25deg),
  world(1, 0, $w 2$, $p$),
)

(d) In this model, $w 1 tack.double.r diamond p and diamond q$ but $w 1 tack.double.r.not diamond (p and q)$.

#diagram(
  node-stroke: .1em,
  world(0, .5, $w 1$, $$),
  edge((0,.5), (2,0), "-|>"),
  edge((0,.5), (2,1), "-|>"),
  world(2, 0, $w 2$, $p$),
  world(2, 1, $w 3$, $q$),
)

(e) In this model, $w 1 tack.double.r box (p or q)$ but $w 1 tack.double.r.not box p or box q$.

#diagram(
  node-stroke: .1em,
  world(0, .5, $w 1$, $$),
  edge((0,.5), (2,0), "-|>"),
  edge((0,.5), (2,1), "-|>"),
  world(2, 0, $w 2$, $p$),
  world(2, 1, $w 3$, $q$),
)
