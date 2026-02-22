// #import "@preview/polylux:0.4.0": *
#import "@preview/simplebnf:0.1.1": *
// #import "@preview/zebraw:0.5.0": *
// #show: zebraw
#import "@preview/curryst:0.6.0": rule, prooftree, rule-set
#import "@preview/xarrow:0.4.0": xarrow

= Формальная модель используемого языка

== Синтаксис

#h(10pt)

#bnf(
  Prod(
    `tag`,
    {
      Or[`Ref`][pass by reference]
      Or[`Value`][copy]
    }
  ),
  Prod(
    `value`,
    {
      Or[`Unit`][cell with some value]
      Or[`Bot`][spoiled cell]
    }
  ),
  Prod(
    `arg`,
    {
      Or[`RValue`][new value, no associated variable]
      Or[`LValue` $d$][value from some variable]
    }
  ),
  Prod(
    `stmt`,
    {
      Or[$f($`args`$)$][call function by id]
      Or[`write` $d$][write to variable]
      Or[`read` $d$][read from variable]
    }
  ),
  Prod(
    `body`,
    {
      Or[`body` `stmt`][with statement]
      Or[$epsilon$][empty body]
    }
  ),
  Prod(
    `fun_decl`,
    {
      Or[`body`][function body]
      Or[`tag` `fun_decl`][with argument pass strategy annotation]
    }
  ),
  Prod(
    `prog`,
    {
      Or[`fun_decl`][main function]
      Or[`fun_decl` `prog`][with supplimentary funcitons]
    }
  ),
)
#align(center, [$d, f in NN,$ `args` $in NN ast.basic$])

== Семантика статического интерпретатора

#h(10pt)

$V := {0, bot}$ - значения памяти

$L := NN$ - позиции в памяти

$X$ - можество переменных

$sigma : X -> L$ - позиции памяти, соответстующие переменным контекста

$mu : NN -> V$ - память

$l in NN$ - длина используемого фрагмента памяти

$M subset NN$ - множество испорченных ячеек памяти

#[

#let cl = $chevron.l$
#let cr = $chevron.r$

#align(center, grid(
  columns: 2,
  gutter: 5%,
  align(bottom, prooftree(
    vertical-spacing: 4pt,
    rule(
      name: [ spoil init],
      $mu =>^nothing mu$,
    )
  )),
  prooftree(
    vertical-spacing: 4pt,
    rule(
      name: [ spoil step],

      $mu =>^M gamma$,
      $mu =>^(M union {n}) gamma[n <- bot]$
    )
  ),
))

#h(10pt)

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ $f(x), space f := lambda a. e$],

    $cl [a -> sigma(x)], mu, l, nothing cr
     xarrow(e)
     cl sigma, mu', l', M' cr$,

    $mu' =>^M' gamma$,

    $cl sigma, mu, l, M cr
     xarrow(f(*x))
     cl sigma, gamma|_[0, l), l, M cr$,
  )
))

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ READ $x$],

    $mu(sigma(x)) != bot$,

    $cl sigma, mu, l, M cr
     xarrow("READ" x)
     cl sigma, mu, l, M cr$,
  )
))

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ WRITE $x$],

    $cl sigma, mu, l, M cr
     xarrow("WRITE" x)
     cl sigma, mu[x <- 0], l, M union {sigma(x)} cr$,
  )
))

]

== Пример аннтаций аргументов

#h(10pt)

#align(center, grid(
columns: 3,
gutter: 5%,
  ```
  def f(?fx x, ?fy y) {
    read(x);
    write(x);
    read(y);
  }
  def w(?wx x) {
    write(x);
  } 
  ```,
  ```
  def g(?gx x, ?gy y) {
    write(x);
    write(y);
    read(x);
    read(y);
  }
  def r(?rx x) {
    read(x);
  } 
  ```,
  ```
  def main(x, y, z, k) {
    w(x);
    r(x); // -> ?wx != ref
    f(x, y);
    r(y);
    g(z, k);
    w(z);
    f(y, z);
    r(k); // -> ?gy != ref
  }
  ```
))
```
-> ?fx = ref, ?fy = ref, ?wx = copy, ?gx = ref, ?gy = copy, ?rx = ref
...
-> ?fx = copy, ?fy = copy, ?wx = copy, ?gx = copy, ?gy = copy, ?rx = copy
```

