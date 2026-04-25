// #import "@preview/polylux:0.4.0": *
#import "@preview/simplebnf:0.1.1": *
// #import "@preview/zebraw:0.5.0": *
// #show: zebraw
#import "@preview/curryst:0.6.0": rule, prooftree, rule-set
#import "@preview/xarrow:0.4.0": xarrow, xarrowDashed, xarrowSquiggly

= Формальная модель используемого языка

#h(10pt)

// TODO: check correctnes for path, mem & type ??

== Syntax

#h(10pt)

#let rf = $\& #h(3pt)$

#let isCorrect = `isCorrect`

#let isRead = `isRead`
#let isAlwaysWrite = `isAlwaysWrite`
#let isPossibleWrite = `isPossibleWrite`
#let isRef = `isRef`
#let isCopy = `isCopy`

#let readTag = `read`
#let writeTag = `write`
#let copyTag = `copy`
#let inTag = `in`
#let outTag = `out`
#let mode = `mode`

#let Copy = `Copy`
#let Ref = `Ref`
#let MaybeWrite = [$diamond$ `Write`]
#let AlwaysWrite = [$square$ `Write`]
#let Read = `Read`
#let In = `In`
#let Out = `Out`

#let cl = $chevron.l$
#let cr = $chevron.r$

#let expr = `expr`
#let stmt = `stmt`
#let decl = `decl`
#let prog = `prog`
#let path = `path`
#let type = `type`
#let modedType = `modedtype`
#bnf(
  Prod(`read`,
    // NOTE: not three modalities for write, because read does not change value
    // => it is not important to observe rsult, no differenc between always and maybe
    { Or[Read][read passed value]
      Or[$not$ Read][] } ),
  Prod(`write`,
    { Or[$square$ Write][in all cases there is a write to the variable] // always write, requre at least one write in each flow variant
      Or[$diamond$ Write][in some cases there is a write to the variable] // possible write, no requirements (?)
      Or[$not$ Write][in none cases there is a write to the variable ] } ), // no write, require n owrites in all flow variants
  Prod(`copy`,
    { Or[Ref][pass reference to the value]
      Or[Value][pass copy of the value] } ),
  Prod(`in`,
    { Or[In][parameter value used as input]
      Or[$not$ In][] } ),
  Prod(`out`,
    { Or[Out][parameter value returned]
      Or[$not$ Out][] } ),
  Prod(
    `mode`,
    {
      Or[$inTag space outTag$][]
    }
  ),
  Prod(
    `path`,
    {
      // NOTE: global vars & local vars names could be used with one constructor
      // Or[$\#x$][funciton or global variable itself]
      Or[$@ X$][function argument or variable itself]
      Or[$* path$][reference insede path]
      Or[$path . n$][access $n$-th cell of the tuple]
      // Or[$path : n$][access $n$-th cell of the union] // TODO: another notation ??
    }
  ),
  Prod(
    `type`,
    {
      Or[$cl readTag, writeTag cr$][simple type representing all primitive types] // `Unit`
      Or[$rf copyTag type$][reference to structure, contains copy / ref choice] // `Ref`
      Or[$[type+]$][tuple type] // `Prod`
      // Or[`type` $times$ `type`][pair type, allows to make tuples] // `Prod`
      // Or[`type` $+$ `type`][union type (important in some way ???)] // `Sum` // TODO ?

      // NOTE: do not use names in type
      // Or[$lambda_((x type)+)$][type of lambda or function pointer, defined by function declaration] // `Fun`
      Or[$lambda (modedType)+$][type of lambda or function pointer, defined by function declaration] // `Fun`
    }
  ),
  Prod(
    `modedtype`,
    {
      Or[$mode type$][type woth in and out modifiers]
    }
  ),
  Prod(
    `expr`,
    {
      Or[$()$][value of simple type] // `Unit`
      Or[$path$][value from variable] // `Path`
      Or[$rf expr$][reference expr] // `Ref`
      Or[$[expr+]$][tuple expr] // `Prod`
    }
  ),
  Prod(
    `stmt`,
    {
      Or[`CALL` $path space expr+$][call function]
      Or[`WRITE` $path$][write to variable]
      Or[`READ` $path$][read from variable]
      Or[$stmt ; stmt$][control flow operator, xecution ]
      Or[$stmt | stmt$][control flow operator, excution of one statements]
    }
  ),
  Prod(
    `decl`,
    {
      // TODO: path not allowed ??
      Or[$"var" X : type = expr$][global variable declaration]
      Or[$"fun" X ((X : modedType)+) = stmt$][function declaration]
    }
  ),
  Prod(
    `prog`,
    {
      Or[$decl stmt$][declarations and executet statement]
    }
  ),
)

== Value Model

#let deepValue = `deepvalue`
#let value = `value`

#bnf(
  Prod(
    $deepValue$,
    {
      Or[$0$][valid value of simple type] // `Unit`
      Or[$\#$][valid or spoiled value of simple type] // `Unit`
      Or[$bot$][spoiled value of simple type] // `Unit`
      Or[$lambda$][function pointer value] // `Fun`
      Or[$rf deepValue$][reference value, contains label of the value in the memory] // `Ref`
      Or[$[deepValue+]$][tuple value] // `Prod`
    }
  ),
  Prod(
    $value_mu$,
    {
      Or[$0$][valid value of simple type] // `Unit`
      Or[$\#$][valid or spoiled value of simple type] // `Unit`
      Or[$bot$][spoiled value of simple type] // `Unit`
      Or[$lambda$][function pointer value] // `Fun`
      Or[$rf LL$][reference value, contains label of the value in the memory] // `Ref`
      Or[$[value+]$][tuple value] // `Prod`
    }
  ),
)

#deepValue - полное значение, #value - слой значения, привязан к конкретной памяти $mu$

Значения, могут лежать в переменных и передаваться как аргументы функций (то, во что вычисляется $expr$)

$v in value$ - произвольное значение

Получение #deepValue по #value:
- $rf l xarrowSquiggly(mu)_#[deep] rf mu[l]$
- $* xarrowSquiggly(mu)_#[deep] *$
где $*$ - произвольный конструктор значения, кроме $rf$

== Memory Model

#let mem = `mem`

- $LL$ - множество меток памяти
- $mem := LL -> value, space mu : mem$ - память, частично определённая функция
- $l in LL$ - новый тег памяти (ранее не использованный)
- `next` - получение следующей неиспользованной метки в памяти

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ add value to memory],

    $l = #[next] (mu)$,

    $cl mu cr xarrowSquiggly(v)_#[add] cl l, mu [l <- v] cr$,
  )
))

== Semantics

// $V := memelem$ - значения памяти

$X$ - можество переменных

// FIXME: TMP
#let valuemem = `valuemem`
#let memelem = `memelem`
#let pathenvmode = `pathenvmode`
#let pathenvval = `pathenvval`
#let pathenvmem = `pathenvmem`
#let pathenvtype = `pathenvtype`

#let vals = $Sigma$
#let types = $Gamma$
#let envv = $#[env]_Sigma$
#let envt = $#[env]_Gamma$
$sigma : envv := X -> LL, space vals : envv$ - #[ метки памяти перменных контекста, частично определённая функция ]
$sigma : envt := X -> type, space types : envt$ - #[ типы значений перменных контекста, частично определённая функция ]

// $DD : X -> decl$ - глобальные определения, частично определённая функция

// $d in decl, $
$s in stmt, f in X, x in X, a in X$

// FIXME ??
// $d space @ space overline(x)$ - запись применения функции (вида #decl) к аргументам

=== Path Accessors

Набор частично определённых фунций для работы с путями.
Для удобства значение, получаемое из текущего применением пути, будем называть полем.
// Все эти функции используются с префиксом `path.`.

#let eqmu = $attach(=, br: mu)$
#let arrmu = $attach(->, br: mu)$

#let arrpath = $xarrowSquiggly(mu)_path$

#let ttype = $attach(tack.r, br: type)$
#let tmode = $attach(tack.r, br: mode)$

#let val = `val`
#let label = `label`
#let tval = $attach(tack.r, br: val)$
#let tlabel = $attach(tack.r, br: label)$

// TODO: TMP, deprecated
// #let tetype = $attach(tack.r.double, br: type)$
// #let temode = $attach(tack.r.double, br: mode)$
// #let telabel = $attach(tack.r.double, br: label)$

#let teval = $attach(tack.r.double, br: val)$

// TODO: env mem label ??, env mem value ??

- #[ Конструирование путей по переменой
#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ variable path],

    $@x arrpath x$,
  )
))
#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ reference path],

    $p arrpath x$,
    $rf p arrpath x$,
  )
))
#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ tuple access path],

    $p arrpath x$,

    $p.i arrpath x$,
  )
))
]

- #[ Получение типа поля
#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ variable type access],

    $x : t_x in types$,
    $types ttype @x : t_x$,
  )
))
#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ reference type access],

    $types ttype p : rf mode t_p$,
    $types ttype *p : t_p$,
  )
))
#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ tuple type access],

    $types ttype p : [t_1, ... t_n]$,
    $types ttype p.i : t_i$,
  )
))
]

// TODO: not required (trivial) ??
// - #[ Получение read-write тега поля
// #align(center, prooftree(
//   vertical-spacing: 4pt,
//   rule(
//     name: [ rw tag access],

//     $types ttype p : cl r, w cr$,
//     $types tmode p -> cl r, w cr$,
//   )
// ))
// ]

- #[ Получение значения поля
#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ variable value access],

    $x -> l in vals$,
    $mu[l] = v$,
    $vals, mu tval x eqmu v$,
  )
))
#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ reference value access],

    $vals, mu tval p eqmu rf l$,
    $vals, mu tval *p eqmu mu[l]$,
  )
))
#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ tuple value access],

    $vals, mu tval p eqmu [v_1, ... v_n]$,
    $vals, mu tval p.i eqmu v_i$,
  )
))
]

// TODO: FIXME: not required (trivial) ??
// - #[ Получение метки поля
// #align(center, prooftree(
//   vertical-spacing: 4pt,
//   rule(
//     name: [ access],

//     $vals, mu tval p eqmu rf l$,
//     $vals, mu tmode p arrmu l$,
//   )
// ))
// ]

// TODO: not required (trivial) ??
// - #[ Получение read-write тега поля по окружению
// #align(center, prooftree(
//   vertical-spacing: 4pt,
//   rule(
//     name: [ access],

//     $x : types[x] tmode p -> cr r space w cl$,
//     $sigma temode p -> cr r space w cl$,
//   )
// ))
// ]

- #[ Получение значения поля по окружению
#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ access],

    $x eqmu vals[x] tval p eqmu v$,
    $types, vals, mu teval p eqmu x$,
  )
))
]

// FIXME: move to new mode model
// === Mode Correctness

// Функции проверки тегов, имеют тип $mode -> #[bool]$:

// #let modevar = $(r space w space c space i space o)$

// $ isRead modevar = r == "Read" $
// $ isAlwaysWrite modevar = w == square "Write" $
// $ isPossibleWrite modevar = w == diamond "Write" || w == square "Write" $
// $ isRef modevar = c == "Ref" $
// $ isCopy modevar = c == "Copy" $
// $ isIn modevar = i == "In" $
// $ isOut modevar = o == "Out" $

// Требования к тегам:

// $ isOut mode -> isAlwaysWrite mode $
// $ isRead mode -> isIn mode $

// TODO: rest conditions ??

=== Eval Rules

#let args = `args`

#[

#let ref = `ref`
#let copy = `copy`
#let read = `read`

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

=== Moded Type Correctness

#let tcorrect = $attach(tack.r, br: #[correct])$

// TODO: FIXME: well formatness for mode, extract
// TODO: FIXME: check for mode, is recursion required ??
// TODO: FIXME: check mode & access corectness in os correct

$ vals in envv, types in envt, space mu in mem, space m in mode,
  space c in copyTag, space r, r' in readTag, space w, w' in writeTag,
  space v in value, space t, t' in type $

#h(10pt)

// TODO: FIXME: complete rule check
// + add part about ref -> not copy later
#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ unit assignment tags correctness],

    $r = Read => m = (In, \_)$, 
    $m = (\_, Out) => w = AlwaysWrite$,
    // $sigma temode x -> cr r' space w' cl$, // NOTE: not required, value passed
    $(w = AlwaysWrite or w = MaybeWrite) and (m = (\_, Out) or c = Ref) => w' = AlwaysWrite$,

    // $sigma, mu teval x eqmu v$, // NOTE: not required, value passed
    $v in {0, \#, bot}$,
    $r = Read => v = 0$,

    $types, vals, mu, m, c tcorrect v : cl r', w' cr -> cl r, w cr$,
  )
))

#h(10pt)

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ function pointer tags correctness],

    $types, vals, mu, m, c tcorrect lambda : lambda space overline(t) -> lambda space overline(t)$,
  )
))

#h(10pt)

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ ref assignment tags correctness],

    $types, vals, mu, m, c_r tcorrect v : t -> t'$,

    // TODO: FIXME: which tag translations are correct ?? <- only assignee?
    $types, vals, mu, m, c tcorrect rf space v : rf c' space t -> rf c_r space t'$,
  )
))

#h(10pt)

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ tuple assignmenttags correctness],

    $types, vals, mu, m, c tcorrect v_1 : t_1 -> t'_1$,

    $...$,

    $types, vals, mu, m, c tcorrect v_n : t_n -> t'_n$,

    $types, vals, mu, m, c tcorrect [v_1, ... v_n] : [t_1, ..., t_n] -> [t'_1, ... t'_n]$,
  )
))

#h(10pt)

=== Value Construction

// TODO: FIXME:add ref / copy modes correctness check ??

#let new = `new`

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ new $0$ value],

    $cl 0, mu cr xarrowSquiggly(cl r\, w cr)_new cl 0, mu cr$,
  )
))

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ new $\#$ value],

    $cl \#, mu cr xarrowSquiggly(cl r\, w cr)_new cl \#, mu cr$,
  )
))

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ new $bot$ value],

    $cl bot, mu cr xarrowSquiggly(cl r\, w cr)_new cl bot, mu cr$,
  )
))

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ new funciton pointer value],

    $cl lambda overline(t) s, mu cr xarrowSquiggly(space)_new cl lambda overline(t) s, mu cr$,
  )
))

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ new reference ref value],

    // TODO: FIXME: recursive copy ?? (what heppens if ref field has copy substructure ??)
    // frbidden ??

    $cl rf l, mu cr xarrowSquiggly(rf Ref t)_new cl rf l, mu cr$,
  )
))

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ new reference copy value],

    $cl mu[l], mu cr xarrowSquiggly(t)_new cl v, mu_v cr$,

    $cl mu_v cr xarrowSquiggly(v)_#[add] cl l', mu_a cr$,

    $cl rf l, mu cr xarrowSquiggly(rf Copy t)_new cl rf l', mu_a cr$,
  )
))

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ new tuple value],

    $cl v_1, mu_0 cr xarrowSquiggly(t_1)_new cl lambda v'_1, mu_1 cr$,
    $...$,
    $cl v_n, mu_(n - 1) cr xarrowSquiggly(t_n)_new cl lambda v'_n, mu_n cr$,

    $cl [v_1, ... v_n], mu_0 cr xarrowSquiggly([t_1, ... t_n])_new cl [v'_1, ... v'_n], mu_n cr$,
  )
))

=== Value Update

#let modify = `modify`

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ modify trivial value],

    $v in {0, \#, bot}$,
    $cl v, mu cr xarrowSquiggly(cl \@ x \, b cr)_modify cl b, mu cr$,
  )
))

#h(10pt)

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ new reference copy value],

    $cl mu[l], mu cr xarrowSquiggly(cl p \, b cr)_modify cl v', mu' cr$,
    $cl rf l, mu cr xarrowSquiggly(cl *p \, b cr)_modify cl rf l, mu'[l <- v'] cr$,
  )
))

#h(10pt)

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ modify tuple value],

    $v in {0, \#, bot}$,
    $cl v_i, mu cr xarrowSquiggly(cl p \, b cr)_modify cl v'_i, mu', cr$,
    $cl [v_1, ... v_i, ... v_n], mu cr xarrowSquiggly(cl p.i \, b cr)_modify cl [v_1, ... v'_i, ... v_n], mu' cr$,
  )
))

#h(10pt)

=== Value Combination

#let combine = `combine`

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ combine trivial $0$ values],

    $cl mu_1, mu_2, mu cr xarrowSquiggly(cl 0 \, 0 cr)_combine cl 0, mu cr$
  )
))

#h(10pt)

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ combine trivial $bot$ values],

    $cl mu_1, mu_2, mu cr xarrowSquiggly(cl bot \, bot cr)_combine cl bot, mu cr$
  )
))

#h(10pt)

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ combine other trivial values],

    $v_1 in {0, \#, bot}$,
    $v_2 in {0, \#, bot}$,
    $v_1 != v_2$,
    $cl mu_1, mu_2, mu cr xarrowSquiggly(cl v_1 \, v_2 cr)_combine cl \#, mu cr$
  )
))

#h(10pt)

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ combine lambda values],

    $cl mu_1, mu_2, mu cr xarrowSquiggly(cl lambda \, lambda cr)_combine cl lambda, mu cr$
  )
))

#h(10pt)

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ combine reference values (inplace)],

    // NOTE: standalome version
    // $cl mu_1, mu_2, mu cr xarrowSquiggly(cl mu_1[l_1] \, mu_2[l_2] cr)_combine cl v', mu' cr$,
    // $mu' xarrowSquiggly(v')_#[add] cl rf l', mu'' cr$,
    // $cl mu_1, mu_2, mu cr xarrowSquiggly(cl rf l_1 \, rf l_2 cr)_combine cl rf l', mu'' cr$

    // NOTE: version to use with "combine all"
    $l_1 = l_2$,
    $cl mu_1, mu_2, mu cr xarrowSquiggly(cl rf l_1 \, rf l_2 cr)_combine cl rf l_1, mu cr$
  )
))

#h(10pt)

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ combine tuple values],

    $cl mu_1, mu_2, mu'_0 cr xarrowSquiggly(cl v^1_1 \, v^2_1 cr)_combine cl v'_1, mu'_1 cr$,
    $...$,
    $cl mu_1, mu_2, mu'_(n - 1) cr xarrowSquiggly(cl v^1_n \, v^2_n cr)_combine cl v'_n, mu'_n cr$,
    $cl mu_1, mu_2, mu'_0 cr xarrowSquiggly(cl [v^1_1, ... v^1_n] \, [v^2_1 ... v^2_n] cr)_combine cl [v'_1, ... v'_n], mu'_n cr$
  )
))

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ combine tuple values],

    $mu'_0 = nothing$,
    // NOTE: same labels required
    $mu_1 = {l_1 -> v^1_1, ... l_n -> v^1_n}$,
    $mu_2 = {l_1 -> v^2_1, ... l_n -> v^2_n}$,

    $cl mu_1, mu_2, mu'_0 cr xarrowSquiggly(cl v^1_1 \, v^2_1 cr)_combine cl v'_1, mu'_1 cr$,
    $...$,
    $cl mu_1, mu_2, mu'_(n - 1) cr xarrowSquiggly(cl v^1_n \, v^2_n cr)_combine cl v'_n, mu'_n cr$,

    $cl mu_1, mu_2 cr xarrowSquiggly(space)_#[combine all] mu'_n cr$
  )
))

#h(10pt)

=== Call Finalization

// FIXME: make connected to syntax
*TODO*

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

    $isPossibleWrite mode$, // NOTE: weak requirement: may write
    $not isCopy mode$,
    $mode = (\_, not Out)$,

    $isCorrect_(cl sigma, mu cr) (mode, x)$,

    // gamma - memory (as mu)
    $gamma stretch(=>)^((mode, x) : args)_sigma pathenvval(gamma, sigma, x) <- bot]$
  )
))

#h(10pt)

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ fix step],

    $mu stretch(=>)^args_sigma gamma$,

    $isAlwaysWrite mode$, // NOTE: strong requirement: should write
    $mode = (\_, not Out)$,

    $isCorrect_(cl sigma, mu cr) (mode, x)$,

    // gamma - memory (as mu)
    $gamma stretch(=>)^((mode, x) : args)_sigma pathenvval(gamma, sigma, x) <- 0]$
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

    $isCorrect_(cl sigma, mu cr) (mode, x)$,

    // mu
    $gamma stretch(=>)^((mode, x) : args)_sigma gamma$
  )
))


#h(10pt)

=== Function Evaluation

// FIXME: make connected to syntax
*TODO*

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ $(lambda a : t. d) m$],

    // TODO: verify that type of m is t ??

    $cl sigma [a <- (m, t)], mu, l cr
     xarrowSquiggly(t)
     cl sigma', mu', l' cr$,

    $cl sigma', mu', l' cr
     xarrowDashed(d space @ space overline(y))
     cl sigma'', mu'', l'' cr$,

    $isRead mode$,
    $not isCopy mode$,

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

=== Statement Evaluation

// FIXME: make connected to syntax
*TODO: check type of lambda?, args from type?*
#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ CALL $f space overline(p)$],

    $cl [], mu, l cr
     xarrowDashed(f space @ space overline(p))
     cl sigma', mu', l' cr$,

    // TODO: FIXME define args in some way
    $mu attach(stretch(=>)^args_sigma, tr: *) gamma$,

    $cl sigma, mu, l cr
     xarrow("CALL" f space overline(p))
     cl sigma, gamma, l cr$,
  )
))

#h(10pt)

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ READ $p$],

    $mu, types, vals teval p eqmu 0$,

    $cl types, vals, mu cr
     xarrow("READ" p)
     cl types, vals, mu cr$,
  )
))

#h(10pt)

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ WRITE $x$],

    $types ttype p : cl r, w cr$,
    $w = MaybeWrite or w = AlwaysWrite$,
    $p arrpath x$,
    $mu[x] xarrowSquiggly(p)_modify v'$,

    $cl types, vals, mu cr
     xarrow("WRITE" p)
     cl types, vals, mu[x <- v'] cr$,
  )
))

#h(10pt)

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ $s \; t$],

    $cl types, vals, mu cr
     stretch(->)^s
     cl types_s, vals_s, mu_s cr$,

    $cl types_s, vals_s, mu_s cr
     stretch(->)^t
     cl types_t, vals_t, mu_t cr$,

    $cl types, vals, mu, cr
     xarrow(s \; t)
     cl types_t, vals_t, mu_t cr$,
  )
))

#h(10pt)

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ $s | t$],

    $cl types, vals, mu cr
     stretch(->)^s
     cl types_s, vals_s, mu_s cr$,

    $cl types, vals, mu cr
     stretch(->)^t
     cl types_t, vals_t, mu_t cr$,

    $types_s = types_t$,
    $vals_s = vals_t$,
    $cl mu_s, mu_t cr xarrowSquiggly(space)_#[combine all] mu'$,

    // TODO changes ?? two ways ??
    $cl types, vals, mu cr
     xarrow(s | t)
     cl types_t, vals_t, mu' cr$,
  )
))

]
