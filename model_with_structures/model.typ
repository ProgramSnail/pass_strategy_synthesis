// #import "@preview/polylux:0.4.0": *
#import "@preview/simplebnf:0.1.1": *
// #import "@preview/zebraw:0.5.0": *
// #show: zebraw
#import "@preview/curryst:0.6.0": rule, prooftree, rule-set
#import "@preview/xarrow:0.4.0": xarrow, xarrowDashed, xarrowSquiggly

= Формальная модель используемого языка

#h(10pt)

// TODO: check correctness for path, mem & type ??

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
#let NotWrite = [$not$ `Write`]
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
      Or[$inTag outTag$][]
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
      // TODO FIXME: expand to support arbitrary paths (that do lead to lvalue)
      // add relation to calc lvalue / rvalue for each element ?
      Or[$rf X$][reference expr] // `Ref`
      Or[$[expr+]$][tuple expr] // `Prod`
    }
  ),
  Prod(
    `stmt`,
    {
      Or[`SKIP`][do nothing]
      Or[`CALL` $path expr+$][call function]
      Or[`WRITE` $path$][write to variable]
      Or[`READ` $path$][read from variable]
      Or[$stmt ; stmt$][sequence of two statements]
      Or[$stmt | stmt$][choice between the statements]
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
      Or[$decl+ space stmt$][declarations and executed statement]
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
      Or[$lambda space (X+ stmt)+$][function pointer value, set of possible values] // `Fun`
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
      Or[$lambda space (X+ stmt)+$][function pointer value, set of possible values] // `Fun`
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

    $mu xarrowSquiggly(v)_#[add] cl l, mu [l <- v] cr$,
  )
))

== Semantics

// TODO: FIXME: add vars & funcs from global context in the beginnning

// $V := memelem$ - значения памяти

$X$ - можество переменных


#let vals = $Sigma$
#let types = $Gamma$
#let envv = $#[env]_Sigma$
#let envt = $#[env]_Gamma$
$sigma : envv := X -> LL, space vals : envv$ - #[ метки памяти перменных контекста, частично определённая функция ]
$sigma : envt := X -> type, space types : envt$ - #[ типы значений перменных контекста, частично определённая функция ]

// $DD : X -> decl$ - глобальные определения, частично определённая функция

// $d in decl, $
$s in stmt, f in X, x in X, a in X$

=== Path Accessors

Набор частично определённых фунций для работы с путями.
Для удобства значение, получаемое из текущего применением пути, будем называть полем.
// Все эти функции используются с префиксом `path.`.

#let eqmu = $attach(=, br: mu)$
#let arrmu = $attach(->, br: mu)$

#let arrpath = $xarrowSquiggly(space)_path$

#let ttype = $attach(tack.r, br: type)$
#let tmode = $attach(tack.r, br: mode)$

#let val = `val`
#let tval = $attach(tack.r, br: val)$

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

=== Eval Rules

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

// --- >>> ---
// === Moded Type Correctness
// *NOTE: скорее всего не нужна в таком виде, перенесено в spoil*
// #let tcorrect = $attach(tack.r, br: #[correct])$
// $ vals in envv, types in envt, space mu in mem, space m in mode,
//   space c in copyTag, space r, r' in readTag, space w, w' in writeTag,
//   space v in value, space t, t' in type $
// #h(10pt)
// // TODO: FIXME: complete rule check
// // + add part about ref -> not copy later
// #align(center, prooftree(
//   vertical-spacing: 4pt,
//   rule(
//     name: [ unit assignment tags correctness],
//     $r = Read => m = (In, \_)$, 
//     $m = (\_, Out) => w = AlwaysWrite$,
//     // $sigma temode x -> cr r' space w' cl$, // NOTE: not required, value passed
//     $(w = AlwaysWrite or w = MaybeWrite) and (m = (\_, Out) or c = Ref) => w' = AlwaysWrite$,
//     // $sigma, mu teval x eqmu v$, // NOTE: not required, value passed
//     $v in {0, \#, bot}$,
//     $r = Read => v = 0$,
//     $types, vals, mu, m, c tcorrect v : cl r', w' cr -> cl r, w cr$,
//   )
// ))
// #h(10pt)
// #align(center, prooftree(
//   vertical-spacing: 4pt,
//   rule(
//     name: [ function pointer tags correctness],
//     $types, vals, mu, m, c tcorrect lambda : lambda space overline(t) -> lambda space overline(t)$,
//   )
// ))
// #h(10pt)
// #align(center, prooftree(
//   vertical-spacing: 4pt,
//   rule(
//     name: [ ref assignment tags correctness],
//     $types, vals, mu, m, c_r tcorrect v : t -> t'$,
//     // TODO: FIXME: which tag translations are correct ?? <- only assignee?
//     $types, vals, mu, m, c tcorrect rf space v : rf c' space t -> rf c_r space t'$,
//   )
// ))
// #h(10pt)
// #align(center, prooftree(
//   vertical-spacing: 4pt,
//   rule(
//     name: [ tuple assignmenttags correctness],
//     $types, vals, mu, m, c tcorrect v_1 : t_1 -> t'_1$,
//     $...$,
//     $types, vals, mu, m, c tcorrect v_n : t_n -> t'_n$,
//     $types, vals, mu, m, c tcorrect [v_1, ... v_n] : [t_1, ..., t_n] -> [t'_1, ... t'_n]$,
//   )
// ))
// #h(10pt)
// --- <<< ---

=== Value Construction

// TODO: FIXME:add ref / copy modes correctness check ??

#let new = `new`

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ new trivial read value],

    $v in {0, \#, bot}$,
    $cl v, mu cr xarrowSquiggly(cl Read \, w cr)_new cl v, mu cr$,
  )
))

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ new trivial $not$ read value],

    $v in {0, \#, bot}$,
    $cl v, mu cr xarrowSquiggly(cl not Read \, w cr)_new cl bot, mu cr$,
  )
))

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ new funciton pointer value],

    $cl lambda overline(t) s, mu cr xarrowSquiggly(lambda space c space overline(t))_new cl lambda overline(t) s, mu cr$,
  )
))

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ new reference ref value],

    // TODO: FIXME: recursive copy ?? (what heppens if ref field has copy substructure ??)
    // <- forbidden ??

    $cl rf l, mu cr xarrowSquiggly(rf Ref t)_new cl rf l, mu cr$,
  )
))

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ new reference copy value],

    $cl mu[l], mu cr xarrowSquiggly(t)_new cl v, mu_v cr$,

    $mu_v xarrowSquiggly(v)_#[add] cl l', mu_a cr$,

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

// #align(center, prooftree(
//   vertical-spacing: 4pt,
//   rule(
//     name: [ modify trivial value],

//     $v in {0, \#, bot}$,
//     $cl v, mu cr xarrowSquiggly(cl \@ x \, b cr)_modify cl b, mu cr$,
//   )
// ))

// TODO: add type check ??
#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ modify end value],

    // $v in {0, \#, bot}$,
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

    $cl v_i, mu cr xarrowSquiggly(cl p \, b cr)_modify cl v'_i, mu', cr$,
    $cl [v_1, ... v_i, ... v_n], mu cr xarrowSquiggly(cl p.i \, b cr)_modify cl [v_1, ... v'_i, ... v_n], mu' cr$,
  )
))

#h(10pt)

=== Value Combination

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ combine same trivial values],

    $v_1 in {0, \#, bot}$,
    $v_2 in {0, \#, bot}$,
    $v_1 = v_2$,
    $v_1 plus.o v_2 = v_1$
  )
))

#h(10pt)

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ combine different trivial values],

    $v_1 in {0, \#, bot}$,
    $v_2 in {0, \#, bot}$,
    $v_1 != v_2$,
    $v_1 plus.o v_2 = \#$
  )
))

#h(10pt)

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ combine lambda values],

    $overline(x_1) = overline(x_2)$,
    $s_1 = s_2$,
    $lambda space [overline(x^1_1) space s^1_1, ... overline(x^n_1) space s^n_1]
     plus.o lambda space [overline(x^1_2) space s^1_2, ... overline(x^m_2) space s^m_2]
     = lambda space [overline(x^1_1) space s^1_1, ... overline(x^n_1) space s^n_1,
                     overline(x^1_2) space s^1_2, ... overline(x^m_2) space s^m_2]$
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
    $rf l_1 plus.o rf l_2 = rf l_1$
  )
))

#h(10pt)

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ combine tuple values],

    $v^1_1 plus.o v^2_1 = v'_1$,
    $...$,
    $v^1_n plus.o v^2_n = v'_n$,
    $[v^1_1, ... v^1_n] plus.o [v^2_1 ... v^2_n] = [v'_1, ... v'_n]$
  )
))

#let dom = `dom`

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ combine memory],

    $dom mu_1 = dom mu_2$,

    $mu_1 plus.o mu_2 = l -> mu_1[l] plus.o mu_2[l]$
  )
))

#h(10pt)

=== Expression Evaluation

// TODO: check

#let eval = `eval`
#let texpre = $attach(tack.r.double, br: eval)$

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ unit expr value],

    $vals, mu texpre () eqmu 0$,
  )
))

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ path expr value],

    $vals, mu tval p eqmu v$,
    $vals, mu texpre p eqmu v$,
  )
))

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ ref expr value],

    $vals, mu texpre rf x eqmu rf vals[x]$,
  )
))

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ tuple expr value],

    $vals, mu texpre e_1 eqmu v_1$,
    $...$,
    $vals, mu texpre e_n eqmu v_n$,
    $vals, mu texpre [e_1, ... e_n] eqmu [v_1, ... v_n]$,
  )
))

=== Expresion Typing

// TODO: check

#let texprt = $attach(tack.r.double, br: type)$

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ unit value expr type],

    $types texprt () : cl Read, NotWrite cr$,
  )
))

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ path expr type],

    $types ttype p : t$,
    $types texprt p : t$,
  )
))

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ ref expr type],

    $types texprt rf x : rf Ref types[x]$,
  )
))

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ tuple expr type],

    $types texprt e_1 : t_1$,
    $...$,
    $types texprt e_n : t_n$,
    $types texprt [e_1, ... e_n] : [t_1, ... t_n]$,
  )
))

===  Context Initialization

#let init = `init`

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ add variable declaration],

    // NOTE: expr type expected to ~ match t (maybe except some automaticc modifiers)
    // expect well typed program

    $vals, mu texpre e eqmu v$,
    $cl v, mu cr xarrowSquiggly(t)_new cl v', mu' cr$, // TODO: FIXME check (required?)
    $mu' xarrowSquiggly(v')_#[add] cl l, mu'' cr$,

    $cl types, vals, mu cr xarrowSquiggly("var" x : t = e)_init cl types[x <- t], vals[x <- l], mu'' cr$
  )
))

#h(10pt)

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ add function declaration],

    $mu xarrowSquiggly(lambda space [[x_1, ... x_n] s])_#[add] cl l, mu' cr$,

    $cl types, vals, mu cr
     xarrowSquiggly("fun" f (x_1 space : space m_1 t_1, ... space x_n space : space m_n t_n) space = space s)_init
     cl types[f <- lambda space [t_1, ... t_n]], vals[f <- l], mu' cr$
  )
))

#h(10pt)

=== Call Values Spoil

#let spoil = `spoil`

// TODO: FIXME: complete rule check
#let tcorrectnew = $attach(tack.r.double, br: #[correct])$
#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ correctness],

    $r = Read => v = 0$,
    $r = Read => m = (In, \_)$, 
    $m = (\_, Out) => w = AlwaysWrite$,
    $(w = AlwaysWrite or w = MaybeWrite) and (m = (\_, Out) or c = Ref) => w' = AlwaysWrite$,

    $v in {0, \#, bot}$,

    $ tcorrectnew cl v, r, w, r', w', m, c cr $,
  )
))

// TODO: extract correctness

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ spoil step],

    $ tcorrectnew cl v, r, w, r', w', m, c cr $,

    $w = AlwaysWrite or w = MaybeWrite$,
    $v in {0, \#, bot}$,
    $cl v, mu cr xarrowSquiggly(cl r \, w cr \, cl r' \, w' cr \, (\_, not Out) \, not Copy)_spoil cl bot, mu cr$,
  )
))

#h(10pt)

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ fix step],

    $ tcorrectnew cl v, r, w, r', w', m, c cr $,

    $w = AlwaysWrite$,
    $v in {0, \#, bot}$,
    $cl v, mu cr xarrowSquiggly(cl r \, w cr \, cl r' \, w' cr \,  (\_, Out) \, c)_spoil cl 0, mu cr$,
  )
))

#h(10pt)

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ skip step],

    $ tcorrectnew cl v, r, w, r', w', m, c cr $,

    $not "spoil step"$,
    $not "fix step"$,
    $v in {0, \#, bot}$,
    $cl v, mu cr xarrowSquiggly(cl r \, w cr \, cl r' \, w' cr \, (\_, not Out) \, c)_spoil cl v, mu cr$,
  )
))

#h(10pt)

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ lambda step],

    $overline(t) = overline(t')$,
    $cl lambda, mu cr xarrowSquiggly(lambda overline(t) \, lambda overline(t') \, m \, c)_spoil cl lambda, mu cr$,
  )
))

#h(10pt)

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ reference step],

    $cl mu[l], mu cr xarrowSquiggly(t \, t' m \, c')_spoil cl v', mu' cr$,
    // NOTE: copy mode of assigned type is not important (c'')
    $cl rf l, mu cr xarrowSquiggly(rf c' space  t \, rf c'' space  t' \, m \, c)_spoil cl rf l, mu'[l <- v'] cr$,
  )
))

#h(10pt)


#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ tuple step],

    $cl v_1, mu_0 cr xarrowSquiggly(t_1 \, t'_1 \, m \, c)_spoil cl v'_1, mu_1 cr$,
    $...$,
    $cl v_n, mu_(n - 1) cr xarrowSquiggly(t_n \, t'_n \, m \, c)_spoil cl v'_n, mu_n cr$,
    $cl [v_1, ... v_n], mu_0 cr xarrowSquiggly([t_1, ... t_n] \, [t'_1, ... t'_n] \, m \, c)_spoil cl [v'_1, ... v'_n], mu_n cr$,
  )
))

#h(10pt)

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ full spoil for unit expr],

    $mu stretch(=>)^(m space cl r, w cr space ())_(cl vals, types cr) mu$,
  )
))

#h(10pt)

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ full spoil for path expr],

    $p : path$,
    $p arrpath x$,
    $l = vals[x]$,
    $vals, mu texpre p eqmu b$,
    $types ttype p : t'$,
    // TODO: FIXME: Ref or Copy ?? in root <- Ref ??, because otherwise there could not b any Refs
    // FIXME depends on parent ??
    $cl b, mu cr xarrowSquiggly(t \, t' \, m \, Ref)_spoil cl b', mu' cr$,
    $cl mu'[l], mu' cr xarrowSquiggly(cl p \, b' cr)_modify cl v'', mu'' cr$,

    $mu stretch(=>)^(m space t space p)_(cl vals, types cr) mu''[l <- v'']$,
  )
))

#h(10pt)

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ full spoil for tuple expr],

    // NOTE: x as path
    $mu stretch(=>)^(m space t space x)_(cl vals, types cr) mu'$,

    // TODO: FIXME: is c important ?
    $mu stretch(=>)^(m space rf c t space rf x_(cl vals, types cr) mu'$,
  )
))

#h(10pt)

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ full spoil for tuple expr],

    $mu_0 stretch(=>)^(m space t_1 space e_1)_(cl vals, types cr) mu_1$,
    $...$,
    $mu_(n - 1) stretch(=>)^(m space t_n space e_n)_(cl vals, types cr) mu_n$,

    $mu_0 stretch(=>)^(m space [t_1, ... t_n] space [e_1, ... e_n]_(cl vals, types cr) mu_n$,
  )
))

#h(10pt)

=== Function Argument Addition

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ add argument],

    $vals_#[ctx], mu texpre e eqmu v$,
    // $types ttype p : t'$, // TODO: not required if there is no check
    // TODO: check type compatibility for t and type for path p (?)
    // [*TODO: check t ~ t' in sme way (?)*],
    // <- programs considired to be well-typed
    $cl v, mu cr xarrowSquiggly(t)_new cl v', mu' cr$,
    $mu' xarrowSquiggly(v')_#[add] cl l, mu'' cr$,

    // TODO save type mode somewhere ?? // <- not needed because is described by other params <- ??
    $cl types, vals, mu cr
     xarrowDashed(x space t space e)_(vals_#[ctx])
     cl types[x <- t], vals[x <- l], mu'' cr$,
  )
))

#h(10pt)

=== Function Evaluation

#let tfunceval = $attach(tack.r.double, br: #[func eval])$
#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ new reference copy value],

    $types_0 = []$,
    $vals_0 = []$,

    // NOTE: dashed arrow to fill context
    $cl types_0, vals_0,  mu_0 cr
     xarrowDashed(x_1 space t_1 space e_1)_vals
     cl types', vals_1, mu_1 cr$,
    $...$,
    $cl types_(n - 1), vals_(n - 1),  mu_(n - 1) cr
     xarrowDashed(x_n space t_n space e_n)_vals
     cl types_n, vals_n, mu_n cr$,

    $cl types_n, vals_n,  mu_n cr
     xarrow(s)
     cl types', vals', mu' cr$,

    $cl vals, mu_0 cr tfunceval cl s, [x_1, .. x_n], [t_1, ... t_n], [e_1, ... e_n] cr$,
  )
))

#h(10pt)

=== Statement Evaluation

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ SKIP],

    $cl types, vals, mu cr
     xarrow("SKIP")
     cl types, vals, mu cr$,
  )
))

#h(10pt)

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ CALL $f space [e_1, ... e_n]$],

    $vals, mu_0 tval f eqmu lambda [overline(x)_1 space s_1, ... overline(x)_n space s_n]$,
    $types ttype f : lambda [m_1 t_1, ... m_n t_n] $,

    // NOTE: check that all the possible bodies are possible to eval
    $cl vals, mu_0 cr tfunceval cl s_1, overline(x)_1, [t_1, ... t_n], [e_1, ... e_n] cr$,
    $...$,
    $cl vals, mu_0 cr tfunceval cl s_n, overline(x)_n, [t_1, ... t_n], [e_1, ... e_n] cr$,

    // NOTE: thick arrow to "spoil" context
    $mu_0 stretch(=>)^(m_1 space t_1 space e_1)_(cl vals, types cr) mu_1$,
    $...$,
    $mu_(n - 1) stretch(=>)^(m_n space t_n space e_n)_(cl vals, types cr) mu_n$,

    $cl types, vals, mu_0 cr
     xarrow("CALL" f space [e_1, ... e_n])
     cl types, vals, mu_n cr$,
  )
))

#h(10pt)

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ READ $p$],

    $vals, mu tval p eqmu 0$,

    $cl types, vals, mu cr
     xarrow("READ" p)
     cl types, vals, mu cr$,
  )
))

#h(10pt)

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ WRITE $p$],

    $types ttype p : cl r, w cr$,
    $w = MaybeWrite or w = AlwaysWrite$,
    $p arrpath x$,
    $l = vals[x]$,
    $mu[l] xarrowSquiggly(cl p \, 0 cr)_modify v'$,

    $cl types, vals, mu cr
     xarrow("WRITE" p)
     cl types, vals, mu[l <- v'] cr$,
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

    $cl types, vals, mu cr
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
    $mu_s plus.o mu_t = mu'$,

    // TODO changes ?? two ways ??
    $cl types, vals, mu cr
     xarrow(s | t)
     cl types_t, vals_t, mu' cr$,
  )
))

]
