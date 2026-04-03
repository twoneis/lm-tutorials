#import "@preview/curryst:0.6.0": *
#import "rules.typ": *

#set list(marker: none)

= Tutorial 01 Solutions
=== 1.1.1
(a) If the sun shines today, then it won't shine tomorrow.

Have propositional variables:
- $s$: The sun shines today
- $t$: The sun shines tomorrow

$s -> not t$

(g) If Smith has installed central heating, then he has sold his car or he has not paid his mortage.

Have propositional variables:
- $c$: He has installed central heating
- $s$: He has sold his car
- $m$: He has paid his mortage

$c -> s or not m$

_Note: Other solutions are possible_ 

=== 1.4.2 (a)
Truth table for $((p -> q) -> p) -> p$: 

#table(
  columns: (auto, auto, auto, auto, auto),
  table.header(
    $p$, $q$, $p -> q$, $(p -> q) -> p$, $((p -> q) -> p) -> p$
  ),
  $top$, $top$, $top$, $top$, $top$,
  $top$, $bot$, $bot$, $top$, $top$,
  $bot$, $top$, $top$, $bot$, $top$,
  $bot$, $bot$, $top$, $bot$, $top$,
)

=== 1.4.12 (c)
Show that $p -> (q -> r) tack.r p -> (r -> q)$ is not valid:
- Aim to find an assignment s.t. $p -> (q -> r)$ holds but $p -> (r -> q)$ does not
- If $p : bot$ , then both sides hold so $p : top$
- Find assignment s.t. $r -> q$ false, leads to $r : top$ and $q : bot$
- Verify assignment ($p : top$, $q : bot$, $r : top$) holds in $p -> (q -> r)$ but not $p -> (r -> q)$

=== 1.2.1 (r)
Derivation for $p -> q and r tack.r (p -> q) and (p -> r)$: 

#hypos(
  [h1 : $p -> q and r$],
  [h2 : $p$],
  [h3 : $p$],
)

#linebreak()

#prooftree(
  and-i(
    impl-i([h2])(
      and-el(
        impl-e(
          th([h2])($p$),
          th([h1])($p -> q and r$),
          $q and r$
        ),
        $q$
      ),
      $p -> q$,
    ),
    impl-i([h3])(
      and-er(
        impl-e(
          th([h3])($p$),
          th([h1])($p -> q and r$),
          $q and r$
        ),
        $r$
      ),
      $p -> r$
    ),
    $(p -> q) and (p -> r)$
  )
)

#pagebreak()

=== 1.2.1 (x)
Derivation for $p -> (q or r), q -> s, r -> s tack.r p -> s$: 

#hypos(
  [h1 : $p -> (q or r)$],
  [h2 : $q -> s$],
  [h3 : $r -> s$],
  [h4 : $p$],
  [h5l : $q$],
  [h5r : $r$],
)

#linebreak()

#prooftree(
  impl-i([h4])(
    or-e([h5])(
      impl-e(
        th([h4])($p$),
        th([h1])($p -> (q or r)$),
        $q or r$
      ),
      impl-e(
        th([h5l])($q$),
        th([h2])($q -> s$),
        $s$
      ),
      impl-e(
        th([h5r])($r$),
        th([h3])($r -> s$),
        $s$
      ),
      $s$
    ),
    $p -> s$
  )
)

=== 1.2.2 (b)
Derivation for $not p or not q tack.r not (p and q)$: 

#hypos(
  [h1 : $not p or not q$],
  [h2 : $p and q$],
  [h3l : $not p$],
  [h3r : $not q$],
)

#linebreak()

#prooftree(
  not-i([h2])(
    or-e([h3])(
      th([h1])($not p or not q$),
      not-e(
        th([h3l])($not p$),
        and-el(
          th([h2])($p and q$),
          $p$
        ),
        $bot$
      ),
      not-e(
        th([h3r])($not q$),
        and-er(
          th([h2])($p and q$),
          $q$
        ),
        $bot$
      ),
      $bot$
    ),
    $not (p and q)$
  )
)
