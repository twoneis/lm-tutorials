#import "@preview/fletcher:0.5.8" as fletcher: node

#let box = sym.ballot

#let world(x, y, name, has) = {
  node((x,y), radius: 1.5em)[#has]
  node((x, y - 0.45), stroke: none)[#name]
}
