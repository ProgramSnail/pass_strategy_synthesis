// #import "@preview/polylux:0.4.0": *
#import "@preview/simplebnf:0.1.1": *
// #import "@preview/zebraw:0.5.0": *
// #show: zebraw
#import "@preview/curryst:0.6.0": rule, prooftree, rule-set
#import "@preview/xarrow:0.4.0": xarrow, xarrowDashed

= Формальная модель используемого языка

*TODO: проблемы с добавлением if в будущем: как записать write and not write ?*

== Синтаксис

#h(10pt)

#let isCorrect = `isCorrect`

#let isRead = `isRead`
#let isWrite = `isWrite`
#let isRef = `isRef`
#let isCopy = `isCopy`
#let isIn = `isIn`
#let isOut = `isOut`

#let tag = `tag`
#let value = `value`
#let stmt = `stmt`
#let decl = `decl`
#let prog = `prog`
#bnf(
  Prod(`read`,
    { Or[Read][]
      Or[Not Read][] } ),
  Prod(`write`,
    { Or[Write][]
      Or[Not Write][] } ),
  Prod(`copy`,
    { Or[Ref][]
      Or[Value][] } ),
  Prod(`in`,
    { Or[In][]
      Or[Not In][] } ),
  Prod(`out`,
    { Or[Out][]
      Or[Not Out][] } ),
  Prod(
    `tag`,
    {
      Or[`read` #h(3pt) `write` #h(3pt) `copy` #h(3pt) `in` #h(3pt) `out`][]
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

*TODO: исправить с обычного интерпретатора*

#h(10pt)

$V := value$ - значения памяти

$L := NN$ - позиции в памяти

$X$ - можество переменных

*TODO: специфицировать доступ*

*TODO: формально описать isCorrect для tag-а*

*TODO: формально описать accessor-ы tag*

$sigma : X -> tag times L$ - #[ позиции памяти, соответстующие переменным контекста,
                               частично определённая функция ]

$mu : NN -> V$ - память, частично определённая функция

$l in NN$ - длина используемого фрагмента памяти

$DD : NN -> decl$ - определения функций, частично определённая функция

$d in decl, s in stmt, f in NN, x in X, a in NN$

$d space @ space overline(x)$ - запись применения функции (вида #decl) к аргументам

#let args = `args`

#[

#let ref = `ref`
#let copy = `copy`
#let read = `read`

#let cl = $chevron.l$
#let cr = $chevron.r$

// #align(center, grid(
//   columns: 3,
//   gutter: 5%,
//   align(bottom, prooftree(
//   ...
//   )),
//   align(bottom, prooftree(
//   ...
//   )),
//   align(bottom, prooftree(
//   ...
//   )),
// ))

// TODO: introduce spep env argument ??

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ is correct],
    $isOut tag -> isWrite tag$, // NOTE; strong requirment should write
    $isRead tag -> isIn tag$,
    $isWrite tag -> isWrite sigma(x)$, // NOTE: may tag => should sigma(x)
    $isRead tag -> mu (sigma(x)) != bot$, // NOTE: may tag -> ... 

    $isCorrect_(cl sigma, mu cr) (tag, x)$,
  )
))

#h(10pt)

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ spoil init],
    $mu stretch(=>)^nothing_(cl sigma, mu cr) mu$,
  )
))

#h(10pt)

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ spoil step],

    $mu stretch(=>)^args_sigma gamma$,

    $isWrite tag$, // NOTE: weak requirement: may write
    $not isCopy tag$,
    $not isOut tag$,

    $isCorrect_(cl sigma, mu cr) (tag, x)$,

    // mu
    $gamma stretch(=>)^((tag, x) : args)_sigma gamma[sigma(x) <- bot]$
  )
))

#h(10pt)

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ fix step],

    $mu stretch(=>)^args_sigma gamma$,

    $isWrite tag$, // NOTE: strong requirement: should write
    $isOut tag$,

    $isCorrect_(cl sigma, mu cr) (tag, x)$,

    // mu
    $gamma stretch(=>)^((tag, x) : args)_sigma gamma[sigma(x) <- 0]$
  )
))

#h(10pt)

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ skip step],

    $mu stretch(=>)^args_sigma gamma$,

    $not "spoil step"$,
    $not "fix step"$,

    $isCorrect_(cl sigma, mu cr) (tag, x)$,

    // mu
    $gamma stretch(=>)^((tag, x) : args)_sigma gamma$
  )
))


#h(10pt)

#align(center, line())

#h(10pt)

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ $(lambda tag a. d) x, ref + read$],

    $cl sigma, mu, l cr
     xarrowDashed(d space @ space overline(y))
     cl sigma, mu', l' cr$,

    $isRead tag$,
    $not isCopy tag$,

    // NOTE: correctness checked in CALL f

    $cl sigma, mu, l cr
     xarrowDashed((lambda tag a. d) space @ space  x space overline(y))
     cl sigma, mu', l' cr$,
  )
))

#h(10pt)

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ $(lambda tag a. d) x, ref - read$],

    $cl sigma, mu [sigma(x) <- bot], l cr
     xarrowDashed(d space @ space overline(y))
     cl sigma, mu', l' cr$,

    $not isRead tag$,
    $not isCopy tag$,

    // NOTE: correctness checked in CALL f

    $cl sigma, mu, l cr
     xarrowDashed((lambda tag a. d) space @ space  x space overline(y))
     cl sigma, mu', l' cr$,
  )
))

#h(10pt)

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ $(lambda tag a. d) x, copy + read$],

    $cl sigma [a <- l], mu [l <- 0], l + 1 cr
     xarrowDashed(d space @ space overline(y))
     cl sigma', mu', l' cr$,

    $isRead tag$,
    $isCopy tag$,

    // NOTE: correctness checked in CALL f

    $cl sigma, mu, l cr
     xarrowDashed((lambda tag a. d) space @ space x space overline(y))
     cl sigma', mu', l' cr$,
  )
))

#h(10pt)

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ $(lambda tag a. d) x, copy - read$],

    $cl sigma [a <- l], mu [l <- bot], l + 1 cr
     xarrowDashed(d space @ space overline(y))
     cl sigma', mu', l' cr$,

    $not isRead tag$,
    $isCopy tag$,

    // NOTE: correctness checked in CALL f

    $cl sigma, mu, l cr
     xarrowDashed((lambda tag a. d) space @ space x space overline(y))
     cl sigma', mu', l' cr$,
  )
))

#h(10pt)

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [decl body],

    $cl sigma, mu, l cr
     attach(stretch(->)^overline(s), tr: *)
     cl sigma', mu', l' cr$,

    $d = overline(s)$,

    $cl sigma, mu, l cr
     xarrowDashed(d space @)
     cl sigma', mu', l' cr$,
  )
))

#h(10pt)

#align(center, line())

#h(10pt)

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ CALL $f space overline(x)$],

    $cl [], mu, l cr
     xarrowDashed(d space @ space overline(x))
     cl sigma', mu', l' cr$,

    // TODO: FIXME define args in some way
    $mu attach(stretch(=>)^args_sigma, tr: *) gamma$,

    $DD(f) := d$,

    $cl sigma, mu, l cr
     xarrow("CALL" f space overline(x))
     cl sigma, gamma, l cr$,
  )
))

#h(10pt)

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ READ $x$],

    $mu(sigma(x)) != bot$,

    $cl sigma, mu, l cr
     xarrow("READ" x)
     cl sigma, mu, l cr$,
  )
))

#h(10pt)

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ WRITE $x$],

    $isWrite sigma(x)$,

    $cl sigma, mu, l cr
     xarrow("WRITE" x)
     cl sigma, mu[x <- 0], l union {sigma(x)} cr$,
  )
))

]
