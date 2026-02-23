// #import "@preview/polylux:0.4.0": *
#import "@preview/simplebnf:0.1.1": *
// #import "@preview/zebraw:0.5.0": *
// #show: zebraw
#import "@preview/curryst:0.6.0": rule, prooftree, rule-set
#import "@preview/xarrow:0.4.0": xarrow, xarrowDashed

= Формальная модель используемого языка

== Синтаксис

#h(10pt)

#let tag = `tag`
#let value = `value`
#let stmt = `stmt`
#let decl = `decl`
#let prog = `prog`
#bnf(
  Prod(
    `tag`,
    {
      Or[$ast.basic$][pass by reference]
      Or[$!$][copy]
    }
  ),
  Prod(
    `value`,
    {
      Or[$0$][cell with some value]
      Or[$bot$][spoiled cell]
    }
  ),
  // Prod(
  //   `arg`,
  //   {
  //     Or[$0$][new value, no associated variable]
  //     Or[$ amp d$][value from some variable]
  //   }
  // ),
  Prod(
    `stmt`,
    {
      Or[`CALL` $f space overline(x)$][call function by id]
      Or[`WRITE` $x$][write to variable]
      Or[`READ` $x$][read from variable]
    }
  ),
  Prod(
    `decl`,
    {
      Or[ovreline(stmt)][function body]
      Or[$lambda #[`tag`] a.$ `decl`][with argument pass strategy annotation]
    }
  ),
  Prod(
    `prog`,
    {
      Or[`decl`][main function]
      Or[`decl` `prog`][with supplimentary funcitons]
    }
  ),
)
== Семантика статического интерпретатора

#h(10pt)

$V := value$ - значения памяти

$L := NN$ - позиции в памяти

$X$ - можество переменных

$sigma : X -> L$ - #[ позиции памяти, соответстующие переменным контекста,
                            частично определённая функция ]

$mu : NN -> V$ - память, частично определённая функция

$l in NN$ - длина используемого фрагмента памяти

$M subset NN$ - множество испорченных ячеек памяти

$DD : NN -> decl$ - определения функций, частично определённая функция

$d in decl, s in stmt, f in NN, x in X, a in NN$

$d space @ space overline(x)$ - запись применения функции (вида #decl) к аргументам

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

#align(center, line())

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ $(lambda ast.basic a. d) x$],

    $cl sigma, mu, l, M cr
     xarrowDashed(d space @ space overline(y))
     cl sigma, mu', l', M' cr$,

    $cl sigma, mu, l, M cr
     xarrowDashed((lambda ast.basic a. d) space @ space  x space overline(y))
     cl sigma, mu', l', M' cr$,
  )
))

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ $(lambda !a. d) x$],

    $cl sigma [a <- l], mu, l + 1, M cr
     xarrowDashed(d space @ space overline(y))
     cl sigma', mu', l', M' cr$,

    $cl sigma, mu, l, M cr
     xarrowDashed((lambda !a. d) space @ space x space overline(y))
     cl sigma', mu', l', M' cr$,
  )
))

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [decl body],

    $cl sigma, mu, l, M cr
     attach(stretch(->)^overline(s), tr: *)
     cl sigma', mu', l', M' cr$,

    $d = overline(s)$,

    $cl sigma, mu, l, M cr
     xarrowDashed(d space @)
     cl sigma', mu', l', M' cr$,
  )
))

#h(10pt)

#align(center, line())

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ CALL $f space overline(x)$],

    $cl [], mu, l, nothing cr
     xarrowDashed(d space @ space overline(x))
     cl sigma', mu', l', M' cr$,

    $mu' =>^M' gamma$,

    $DD(f) := d$,

    $cl sigma, mu, l, M cr
     xarrow("CALL" f space overline(x))
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
