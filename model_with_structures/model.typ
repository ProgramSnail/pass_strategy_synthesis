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
#let isIn = `isIn`
#let isOut = `isOut`

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
    { Or[$square$ Write][in all cases there is a write to passed variable] // always write, requre at least one write in each flow variant
      Or[$diamond$ Write][in some cases there is a write to passed variable] // possible write, no requirements (?)
      Or[$not$ Write][] } ), // no write, require n owrites in all flow variants
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
      Or[$readTag writeTag ()$][simple type representing all primitive types] // `Unit`
      Or[$rf copyTag space type$][reference to structure, contains copy / ref choice] // `Ref`
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
      Or[$lambda type+ stmt$][function pointer value] // `Fun`
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
      Or[$lambda type+ stmt$][function pointer value] // `Fun`
      // FIXME: embed mode into value for simplification ??
      Or[$rf copyTag LL$][reference value, contains label of the value in the memory] // `Ref`
      Or[$[value+]$][tuple value] // `Prod`
    }
  ),
)

#deepValue - полное значение, #value - слой значения, привязан к конкретной памяти $mu$

Значения, могут лежать в переменных и передаваться как аргументы функций (то, во что вычисляется $expr$)

$v in value$ - произвольное значение

Получение #deepValue по #value:
- $rf c l xarrowSquiggly(mu)_#[deep] rf c mu[l]$
- $* xarrowSquiggly(mu)_#[deep] *$
где $*$ - произвольный конструктор значения, кроме $rf$

== Memory Model

#let cl = $chevron.l$
#let cr = $chevron.r$

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

#let env = `env`
$sigma : env := X -> LL times type, space sigma : env$ - #[ метки памяти и типы значений пеерменных контекста, частично определённая функция ]

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

#let ttype = $attach(tack.r, br: type)$
#let tpath = $attach(tack.r, br: path)$
#let tmode = $attach(tack.r, br: mode)$

#let val = `val`
#let label = `label`
#let tval = $attach(tack.r, br: val)$
#let tlabel = $attach(tack.r, br: label)$

#let tetype = $attach(tack.r.double, br: type)$
#let temode = $attach(tack.r.double, br: mode)$

#let teval = $attach(tack.r.double, br: val)$
#let telabel = $attach(tack.r.double, br: label)$

// TODO: env mem label ??, env mem value ??

// TODO: FIXME: backwards, deconstruction ??
- #[ Конструирование путей по переменой
#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ variable path],

    $x tpath @x$,
  )
))
#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ reference path],

    $x tpath p$,
    $x tpath rf p$,
  )
))
#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ tuple access path],

    $x tpath p$,

    $x tpath p.i$,
  )
))
]

- #[ Получение типа поля
#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ variable type access],

    $x : t_x ttype @x : t_x$,
  )
))
#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ reference type access],

    $x tpath p$,
    $x : t_x ttype p : rf mode t_p$,
    $x : t_x ttype *p : t_p$,
  )
))
#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ tuple type access],

    $x tpath p$,
    $x : t_x ttype p : [t_1, ... t_n]$,
    $x : t_x ttype p.i : t_i$,
  )
))
]

- #[ Получение read-write тега поля
#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ variable rw tag access],

    $t_x = r w ()$,
    $x : t_x tmode @x -> cr r w cl$,
  )
))
#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ reference rw tag access],

    $x tpath p$,
    $x : t_x tmode p -> cr r w cl$,
    $x : t_x tmode *p ->  cr r w cl$,
  )
))
#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ tuple rw tag access],

    $x tpath p$,
    $x : t_x tmode p ->  cr r w cl$,
    $x : t_x tmode p.i -> cr r w cl$,
  )
))
]

- #[ Получение значения поля
#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ variable value access],

    $x eqmu v_x tval @x eqmu v_x$,
  )
))
#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ reference value access],

    $x tpath p$,
    $x eqmu v_x tval p eqmu rf l$,
    $x eqmu v_x tval *p eqmu mu[l]$,
  )
))
#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ tuple value access],

    $x tpath p$,
    $x eqmu v_x tmode p eqmu [v_1, ... v_n]$,
    $x eqmu v_x tmode p.i eqmu v_i$,
  )
))
]

- #[ Получение метки поля
#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ access],

    $v_x = rf l$,
    $x eqmu v_x tval p eqmu rf l$,

    $x eqmu v_x tmode p arrmu l$,
  )
))
]

- #[ Получение типа поля по окружению
#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ access],

    $x tpath p$,
    $x : sigma[x].2 ttype p : t$,
    $sigma tetype p : t$,
  )
))
]

- #[ Получение read-write тега поля по окружению
#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ access],

    $x tpath p$,
    $x : sigma[x].2 tmode p -> cr r space w cl$,
    $sigma temode p -> cr r space w cl$,
  )
))
]

- #[ Получение значения поля по окружению
#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ access],

    $x tpath p$,
    $x eqmu sigma[x].1 tval p eqmu v$,
    $sigma, mu teval p eqmu x$,
  )
))
]

- #[ Получение метки поля по окружению
#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ access],

    $x tpath p$,
    $x eqmu sigma[x].1 tlabel p arrmu l$,
    $sigma, mu telabel p arrmu l$,
  )
))
]

=== Mode Accessors

#let modevar = $(i space o)$

$ isIn modevar = i == In $
$ isOut modevar = o == Out $

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

$ sigma in env, space mu in mem, space m in mode,
  space c in copyTag, space r, r' in readTag, space w, w' in writeTag,
  space v in value, space t, t' in type $

#h(10pt)

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ unit assignment tags correctness],

    $r = Read => isIn m$, 
    $isOut m => w = AlwaysWrite$,
    // $sigma temode x -> cr r' space w' cl$, // NOTE: not required, value passed
    $(w = AlwaysWrite or w = MaybeWrite) and (isOut m or c = Ref) => w' = AlwaysWrite$,

    // $sigma, mu teval x eqmu v$, // NOTE: not required, value passed
    $v in {0, \#, bot}$,
    $r = Read => v = 0$,

    $sigma, mu, m, c tcorrect v : r' space w' () -> r space w ()$,
  )
))

#h(10pt)

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ ref assignment tags correctness],

    $sigma, mu, m, c_r tcorrect v : t -> t'$,

    // TODO: FIXME: which tag translations are correct ?? <- only assignee?
    $sigma, mu, m, c tcorrect rf c_r space v : rf c' space t -> rf c_r space t'$,
  )
))

#h(10pt)

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ tuple assignmenttags correctness],

    $sigma, mu, m, c tcorrect v_1 : t_1 -> t'_1$,

    $...$,

    $sigma, mu, m, c tcorrect v_n : t_n -> t'_n$,

    $sigma, mu, m, c tcorrect [v_1, ... v_n] : [t_1, ..., t_n] -> [t'_1, t'_n]$,
  )
))

#h(10pt)

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ function pointer tags correctness],

    $sigma, mu, m, c tcorrect lambda space overline(t) space s : lambda space overline(t) -> lambda space overline(t)$,
  )
))

#h(10pt)

=== Value Construction

#let new = `new`

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ new $0$ value],

    // TODO: check that access is what required ??
    $cl 0, mu cr xarrowSquiggly(space)_new cl 0, mu cr$,
  )
))

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ new $\#$ value],

    // TODO: check that access is what required ??
    $cl \#, mu cr xarrowSquiggly(space)_new cl \#, mu cr$,
  )
))

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ new $bot$ value],

    $cl bot, mu cr xarrowSquiggly(space)_new cl bot, mu cr$,
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

    $cl rf Ref l, mu cr xarrowSquiggly(space)_new cl rf Ref l, mu cr$,
  )
))

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ new reference copy value],

    $cl mu[l], mu cr xarrowSquiggly(space)_new cl v, mu_v cr$,

    $cl mu_v cr xarrowSquiggly(v)_#[add] cl l', mu_a cr$,

    $cl rf Copy l, mu cr xarrowSquiggly(space)_new cl rf Copy l', mu_a cr$,
  )
))

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ new tuple value],

    $cl v_1, mu_0 cr xarrowSquiggly(space)_new cl lambda v'_1, mu_1 cr$,
    $...$,
    $cl v_n, mu_(n - 1) cr xarrowSquiggly(space)_new cl lambda v'_n, mu_n cr$,

    $cl [v_1, ... v_n], mu_0 cr xarrowSquiggly(space)_new cl [v'_1, ... v'_n], mu_n cr$,
  )
))

=== Value Update

#let write = `write`

*TODO: write to value*

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
    $not isOut mode$,

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
    $isOut mode$,

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

    $mu, sigma teval p eqmu 0$,

    $cl sigma, mu, l cr
     xarrow("READ" p)
     cl sigma, mu, l cr$,
  )
))

#h(10pt)

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ WRITE $x$],

    $sigma temode p -> cr r space w cl$,

    $w == MaybeWrite or w == AlwaysWrite$,

    $x tpath p$,

    $mu[x] xarrowSquiggly(p)_write v$,

    $cl sigma, mu cr
     xarrow("WRITE" p)
     cl sigma, mu[x <- v] cr$,
  )
))

#h(10pt)

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ $s \; t$],

    $cl sigma, mu cr
     stretch(->)^s
     cl sigma_s, mu_s cr$,

    $cl sigma, mu cr
     stretch(->)^t
     cl sigma_t, mu_t cr$,

    $cl sigma, mu, cr
     xarrow(s \; t)
     cl sigma_t, mu_t cr$,
  )
))

#h(10pt)

#let combine = `combine`

*TODO: combine replacement* // FIXME
#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ $s | t$],

    $cl sigma, mu, l cr
     stretch(->)^s
     cl sigma_s, mu_s, l_s cr$,

    $cl sigma, mu, l cr
     stretch(->)^t
     cl sigma_t, mu_t, l_t cr$,

    $sigma_s = sigma_t$,
    $mu' = combine(mu_s, mu_t)$,

    // TODO changes ?? two ways ??
    $cl sigma, mu cr
     xarrow(s | t)
     cl sigma_t, mu' cr$,
  )
))

#h(10pt)

=== Combination

*TODO: rewrite as rules, fix* // FIXME

$ combine(mu_1, mu_2)[i] = combine_e (mu_1[i], mu_2[i]) $
$ combine_e (bot, bot) = bot $
$ combine_e (0, 0) = 0 $
$ combine_e (\_, \_) = \# $
// FIXME: ref to combined memory
$ combine_e (rf c l_1, rf c' l_2) | c == c' = rf c combine_e(mu_1[l_1], mu_2[l_2])$
$ combine_e (v^1_1, ... v^1_n, v^2_1 ... v^2_n) = [combine_e(v^1_1, v^2_1), ..., combine_e(v^1_n, v^2_n)]$
$ combine_e (lambda space overline(t_1) space s_1, lambda space overline(t_2) space s_2) | overline(t_1) == overline(t_2)  = lambda space overline(t_1) space s_1 $
// TODO: FIXME: statemient in lambda is not important ??

]
