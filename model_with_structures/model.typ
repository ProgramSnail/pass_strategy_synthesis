// #import "@preview/polylux:0.4.0": *
#import "@preview/simplebnf:0.1.1": *
// #import "@preview/zebraw:0.5.0": *
// #show: zebraw
#import "@preview/curryst:0.6.0": rule, prooftree, rule-set
#import "@preview/xarrow:0.4.0": xarrow, xarrowDashed

= Формальная модель используемого языка

*TODO: проверить, что всё нужное добавлено*
*TODO: добавить сложные структуры (типы) и работу с ними*
*TODO: добавить тип лямбд (тип с id сигнатуры)*
*TODO: добавить тип вызова поля структуры*
*TODO: добавить правльную работу со вложенными тегами, path-доступ к полям переменных, корректность пути*

Нужно будет добавить во write-flag модальности: `not write` | `may write` | `always write`

Добавление condition-исполнения - выбор из нескольких блоков. Варианты:
- & of | of & -вложенные блоки ?
- добавить несколько альтернативны тел функциям. Но тогда придётся при трансляции if-блоки выносить в функции

Лямбды - нужно тоже будет как-то находить лямбды и ля них тоже синтезировать атрибуты
вызов лямбд будет нужен в модели?
- lambda-аргумент - вложенные теги?, должна быть одна и та же сигнтура
можно ввести отдельные сигнатуры-определения?

проблема простой семантики: вызов лямбд: могут быть модифицируемые функции

== Синтаксис

#h(10pt)

#let isCorrect = `isCorrect`

#let isRead = `isRead`
#let isAlwaysWrite = `isAlwaysWrite`
#let isPossibleWrite = `isPossibleWrite`
#let isRef = `isRef`
#let isCopy = `isCopy`
#let isIn = `isIn`
#let isOut = `isOut`

#let tag = `tag`
#let value = `value`
#let stmt = `stmt`
#let decl = `decl`
#let prog = `prog`
#let path = `path`
#let argtype = `argtype`
#let argmem = `argmem`
#bnf(
  Prod(`read`,
    { Or[Read][read passed value]
      Or[Not Read][] } ),
  Prod(`write`,
    { Or[$square$ Write][in all cases there is a write to passed variable] // always write, requre at least one write in each flow variant
      Or[$diamond$ Write][in some cases there is a write to passed variable] // possible write, no requirements (?)
      Or[$not$ Write][] } ), // no write, require n owrites in all flow variants
  Prod(`copy`,
    { Or[Ref][pass reference to the value]
      Or[Value][pass copy of the value] } ),
  Prod(`in`,
    { Or[In][parameter value used as input]
      Or[Not In][] } ),
  Prod(`out`,
    { Or[Out][parametr value returned]
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
      Or[$0$][cell with some value (always)]
      Or[$X$][cell with possible value or $bot$]
      Or[$bot$][spoiled cell (always)]
    }
  ),
  Prod(
    `path`,
    {
      Or[$x$][fuction argument or variable itself]
      Or[$path . n$][access $n$-th cell of the tuple]
      Or[$path : n$][access $n$-th cell of the union] // TODO: another notation ??
    }
  ),
  Prod(
    `argtype`,
    {
      Or[$()$][simple type representing all primitive types] // `Unit`
      Or[\& #h(3pt) `tag` #h(3pt) `argtype`][reference to structure, contains copy / ref choice] // `Ref`
      Or[`argtype` $times$ `argtype`][pair type, allows to make tuples] // `Prod`
      // Or[`argtype` $+$ `argtype`][union type (important in some way ???)] // `Sum` // TODO ?
      Or[$F_x$][type of lambda or function pointer, defined by function declaration id] // `Fun`
    }
  ),
  Prod(
    `argmem`,
    {
      Or[$[m]$][memory id for simple type variable] // `Unit`
      Or[\& #h(3pt) `tag` #h(3pt) `argmem`][reference to structure, contains copy / ref choice] // `Ref`
      Or[`argmem` $times$ `argmem`][pair type, allows specify memory for tuples] // `Prod`
      // Or[`argmem` $+$ `argmem`][union type (important in some way ???)] // `Sum` // TODO ?
      Or[$F_m$][memory for lambda or function pointer, defined by function declaration id] // `Fun` // why separated ??
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
      Or[`CALL` $f space overline(path)$][call function by id]
      Or[`CALL_LAM` $path space overline(path)$][call lambda funciton (variable or funcitona argument field)]
      Or[`WRITE` $path$][write to variable]
      Or[`READ` $path$][read from variable]
      // TODO: or introduce block statement ?? // vars definiiton statment ??
      // (for example, for same named vars in nested spaces)
      Or[`CHOICE` #overline(`stmt`) #overline(`stmt`)][control flow operator, xecution of one of the blocks]
      // NOTE: var: replaced with arguments (use rvalue as init) (?)
      // Or[`VAR`][variables inside functions] // NOTE: no modifiers required, because it is in the new memory ?? // TODO: not required ??
      // NOTE: lambda: compile to call to the funciton with CHOICE between possible lambda bodies <- do this analysis inside synthesizer ?
    }
  ),
  Prod(
    `decl`,
    {
      Or[$overline(stmt)$][function body]
      Or[$lambda #[`argtype`] a.$ `decl`][argument with argument pass strategy annotation]
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

*TODO: специфицировать доступ*

*TODO: формально описать accessor-ы tag*

$sigma : X -> argmem$ - #[ позиции памяти, соответстующие переменным контекста,
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

// TODO: FIXME: define typeof operation
#let typeof = `typeof`

// TODO: FIXME: define access operation
// TODO: two versions: write with change & read
#let access = `access`

// TODO: FIXME: define argtag operation
#let argtag = `argtag`

// FIXME
#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ is correct],
    $isOut tag -> isAlwaysWrite tag$, // NOTE; strong requirment should write
    $isRead tag -> isIn tag$,
    $isPossibleWrite tag and (isOut tag or not isCopy tag) -> isAlwaysWrite argtag(sigma, x)$, // NOTE: may tag => should sigma(x)
    $isRead tag -> access(mu, sigma, x) != bot and access(mu, sigma, x) != X$,

    $isCorrect_(cl sigma, mu cr) (tag, x)$,
  )
))

#h(10pt)

// TODO: FIXME: define addpaths operation: ~>
// #align(center, prooftree(
//   vertical-spacing: 4pt,
//   rule(
//     name: [ add paths init],

//     $mu stretch(~>)^nothing_(cl sigma, mu cr) mu$,
//   )
// ))

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

    $isPossibleWrite tag$, // NOTE: weak requirement: may write
    $not isCopy tag$,
    $not isOut tag$,

    $isCorrect_(cl sigma, mu cr) (tag, x)$,

    // gamma - memory (as mu)
    $gamma stretch(=>)^((tag, x) : args)_sigma access(gamma, sigma, x) <- bot]$
  )
))

#h(10pt)

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ fix step],

    $mu stretch(=>)^args_sigma gamma$,

    $isAlwaysWrite tag$, // NOTE: strong requirement: should write
    $isOut tag$,

    $isCorrect_(cl sigma, mu cr) (tag, x)$,

    // gamma - memory (as mu)
    $gamma stretch(=>)^((tag, x) : args)_sigma access(gamma, sigma, x) <- 0]$
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
    name: [ $(lambda a. d) x$],

    $cl sigma, mu, l cr
     stretch(~>)^a
     cl sigma, mu', l' cr$,

    $cl sigma', mu', l' cr
     xarrowDashed(d space @ space overline(y))
     cl sigma'', mu'', l'' cr$,

    $isRead tag$,
    $not isCopy tag$,

    // NOTE: correctness checked in CALL f

    $cl sigma, mu, l cr
     xarrowDashed((lambda a. d) space @ space x space overline(y))
     cl sigma'', mu'', l'' cr$,
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
    name: [ CALL_LAM $y space overline(x)$],

    $typeof(y) = F_f$,

    $cl sigma, mu, l cr
     xarrow("CALL" f space overline(x))
     cl sigma, gamma, l cr$,

    $cl sigma, mu, l cr
     xarrow("CALL_LAM" y space overline(x))
     cl sigma, gamma, l cr$,
  )
))

#h(10pt)

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ READ $x$],

    $access(mu, sigma, x) != bot$,
    $access(mu, sigma, x) != X$,

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

    $isPossibleWrite sigma(x)$, // TODO: FIXME ?? always or possible ??

    $cl sigma, mu, l cr
     xarrow("WRITE" x)
     cl sigma, access(mu, sigma, x) <- 0, l cr$,
  )
))

#h(10pt)

#let combine = `combine`

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ CHOICE $overline(s)$ $overline(t)$],

    $cl sigma, mu, l cr
     attach(stretch(->)^overline(s), tr: *)
     cl sigma_s, mu_s, l_s cr$,

    $cl sigma, mu, l cr
     attach(stretch(->)^overline(t), tr: *)
     cl sigma_t, mu_t, l_t cr$,

    $l_t = l_s$,
    $sigma_s = sigma_t$,

    // TODO changes ?? two ways ??
    $cl sigma, mu, l cr
     xarrow("CHOICE" overline(s) space overline(t))
     cl sigma, combine(mu_s, mu_t), l cr$,
  )
))

#h(10pt)

$ combine(mu_1, mu_2)[i] = combine_e (mu_1[i], mu_2[i]) $
$ combine_e (bot, bot) = bot $
$ combine_e (0, 0) = 0 $
$ combine_e (\_, \_) = X $

]
