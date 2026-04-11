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

#let isCorrect = `isCorrect`

#let isRead = `isRead`
#let isAlwaysWrite = `isAlwaysWrite`
#let isPossibleWrite = `isPossibleWrite`
#let isRef = `isRef`
#let isCopy = `isCopy`
#let isIn = `isIn`
#let isOut = `isOut`

#let mode = `mode`
#let expr = `expr`
#let stmt = `stmt`
#let decl = `decl`
#let prog = `prog`
#let path = `path`
#let type = `type`
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
      Or[`read` #h(3pt) `write` #h(3pt) `copy` #h(3pt) `in` #h(3pt) `out`][]
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
      Or[$()$][simple type representing all primitive types] // `Unit`
      Or[\& #h(3pt) `mode` #h(3pt) `type`][reference to structure, contains copy / ref choice] // `Ref`
      Or[$[type+]$][tuple type] // `Prod`
      // Or[`type` $times$ `type`][pair type, allows to make tuples] // `Prod`
      // Or[`type` $+$ `type`][union type (important in some way ???)] // `Sum` // TODO ?

      // NOTE: do not use names in type
      // Or[$lambda_((x type)+)$][type of lambda or function pointer, defined by function declaration] // `Fun`
      Or[$lambda_(type+)$][type of lambda or function pointer, defined by function declaration] // `Fun`
    }
  ),
  // FIXME: replace with expr
  Prod(
    `expr`,
    {
      Or[$()$][value of simple type] // `Unit`
      Or[$path$][value from variable] // `Path`
      Or[$\& #h(3pt) expr$][reference expr] // `Ref`
      Or[$[expr+]$][tuple expr] // `Prod`
      // NOTE: replaced with simple path value
      // Or[$lambda_path$][function value from variable] // `Fun`
    }
  ),
  Prod(
    `stmt`,
    {
      Or[`CALL` $f space expr+$][call function]
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
      Or[$"fun" X ((X : type)+) = stmt$][function declaration]
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

// FIXME: check & add details
#let value = `value`
#bnf(
  Prod(
    `value`,
    {
      Or[$()$][value of simple type] // `Unit`
      Or[$lambda_X$][function pointer value] // `Fun`
      Or[$\& #h(3pt) value$][reference value] // `Ref`
      Or[$[value+]$][tuple value] // `Prod`
    }
  ),
)

$value$ - значения, которые могут лежать в переменных и передаваться как аргументы функций (то, во что вычисляется $expr$)

== Memory Model

// FIXME: check & add details
#let memelem = `memelem`
#let valuemem = `valuemem`
#bnf(
  Prod(
    `memelem`,
    {
      Or[$0$][cell with some value (always)]
      Or[$\#$][cell with possible value or $bot$]
      Or[$bot$][spoiled cell (always)]
    }
  ),
  Prod(
    `valuemem`,
    {
      Or[$()$][one unit of memory, for simple vars] // `Unit`
      Or[$lambda$][memory for lambda or function pointer, is not important in the memory model, 0 units] // `Fun`
      Or[$\& #h(3pt) LL valuemem$][reference to structure memory start] // `Ref`
      Or[$[valuemem+]$][memory specification for each tuple member] // `Prod`
    }
  ),
)

#let mem = `mem`
Память преставляется в виде стека из значений `memelem`:
- $LL = NN$ - множество меток памяти
- $mu : mem = LL -> V$ - память, частично определённая функция
- $l in LL$ - длина используемого фрагмента памяти

Каждому значению $value$ в соответствие ставится $valuemem$ - расположние этого значения в пaмяти

Соответствие:
- $() -> ()$
- $lambda_X -> lambda$
- $\& #h(3pt) value -> \& #h(3pt) LL valuemem$
- $[value+] -> [valuemem+]$

// TODO: move allocation semantics there ??

== Semantics

// $V := memelem$ - значения памяти

$X$ - можество переменных

#let env = `env`
$sigma : env = X -> valuemem times type$ - #[ позиции памяти, соответстующие переменным контекста, частично определённая функция ]

$DD : X -> decl$ - глобальные определения, частично определённая функция

$d in decl, s in stmt, f in X, x in X, a in X$

$d space @ space overline(x)$ - запись применения функции (вида #decl) к аргументам

=== Path Accessors

Набор частично определённых фунций для работы с путями.
Для удобства значение, получаемое из текущего применением пути, будем называть полем.
// Все эти функции используются с префиксом `path.`.

// FIXME: types & description for functios
#let pathtype = `path.type`
#let pathmem = `path.mem`
#let pathmode = `path.mode`
#let pathvar = `path.var`

#let pathsize = `path.memsize`
#let pathbasepos = `path.membasepos`
#let pathoffset = `path.memoffset`
#let pathpos = `path.mempos`

#let pathenvtype = `path.envtype`
#let pathenvmem = `path.envmem`
#let pathenvmode = `path.envmode`

#let pathenvpos = `path.envpos`
#let pathenvval = `path.envval`

- #[ Получение типа поля
$ pathtype : type -> path -> type $
$ pathtype(t, @x) = t $
$ pathtype(\& #h(3pt) mode #h(3pt) t, *p) = pathtype(t, p) $
$ pathtype([t_1, t_2, ..., t_n], p.i) = pathtype(t_i, p) $
]
- #[ Получение начала памяти поля (предусловие: $pathtype(t, p) = \& #h(3pt) ...$)
$ pathmem : valuemem -> path -> LL $
$ pathmem(\& #h(3pt) y m, @x) = y $ // NOTE: only memory for refsi in midel ?? // TODO: decide
$ pathmem(\& #h(3pt) y m, *p) = pathmem(m, p) $
$ pathmem([m_1, m_2, ..., m_n], p.i) = pathmem(m_i, p) $
]
- #[ Получения тега поля (предусловие: $pathtype(t, p) = \& #h(3pt) ...$)
$ pathmode : type -> path -> mode $
$ pathmode(\& #h(3pt) mode #h(3pt) t, @x) = mode $
$ pathmode(\& #h(3pt) mode #h(3pt) t, *p) = pathmode(t, p) $
$ pathmode([t_1, t_2, ..., t_n], p.i) = pathmode(t_i, p) $
]
- #[ Получение \"корневой\" переменной пути
$ pathvar : path -> X $
$ pathvar(@x) = x $
$ pathvar(* p) = pathvar(p) $
$ pathvar(p.i) = pathvar(p) $
]
- #[ Получение размера поля в памяти
$ pathsize : valuemem -> path -> LL $
$ pathsize((), @x) = 1 $
$ pathsize(lambda, @x) = 0 $
$ pathsize(\& #h(3pt) y m, @x) = 0 $ // TODO: FIXME ?? always disconnected location ??
$ pathsize([m_1, m_2, ..., m_n], @x) = pathsize(m_1, @x) + ... + pathsize(m_n, @x) $
$ pathsize(\& #h(3pt) y m, *p) = pathsize(m, p) $
$ pathsize([m_1, m_2, ..., m_n], p.i) = pathsize(m_i, p) $
]
// TODO: FIXME ??
- #[ Получение позиции последного ссылочного предка поля в пaмяти
$ pathbasepos : value -> path -> X $
// $ pathbasepos(m, @x) = bot $ // NOTE: trivial if not present ??
$ pathbasepos(\& #h(3pt) y m, *p) = pathbasepos(m, p) | y $
$ pathbasepos([m_1, m_2, ..., m_n], p.i) = pathbasepos(m_i, p) $
]
- #[ Получение смещения поля в последнем монолитном отрезке памяти
$ pathoffset : value -> path -> X $
$ pathoffset(m, @x) = 0 $
$ pathoffset(\& #h(3pt) y m, *p) = pathoffset(m, p) $
$ pathoffset([m_1, m_2, ..., m_n], p.i) = (i - 1) + pathoffset(m_i, p) $
]
- #[ Получение позиции поля в пaмяти
$ pathpos : value -> path -> X $
$ pathpos(m, p) = pathbasepos(m, p) + pathoffset(m, p)$
]
- #[ Получение типа поля по окружению
$ pathenvtype : env -> path -> type $
$ pathenvtype(sigma, p) = pathtype(sigma[pathvar(p)].2, p) $
]
- #[ Получение начала памяти поля по окружению (предусловие: $pathtype(t, p) = \& #h(3pt) ...$)
$ pathenvmem : env -> path -> LL $
$ pathenvmem(sigma, p) = pathmem(sigma[pathvar(p)].1, p) $
]
- #[ Получения тега поля по окружению (предусловие: $pathtype(t, p) = \& #h(3pt) ...$)
$ pathenvmode : env -> path -> mode $
$ pathenvmode(sigma, p) = pathmode(sigma[pathvar(p)].2, p) $
]
- #[ Получение позиции поля в пaмяти по окружению
$ pathenvpos : env -> path -> X $
$ pathenvpos(m, p) = pathpos(sigma[pathvar(p)].1, p)$
]
- #[ Получение поля в пaмяти
$ pathenvval : env -> mem -> path -> memelem $
$ pathenvval(sigma, mu, p) = mu[pathenvpos(sigma, p)]$
]

=== Mode Correctness

Функции проверки тегов, имеют тип $mode -> #[bool]$:

#let modevar = $(r space w space c space i space o)$

$ isRead modevar = r == "Read" $
$ isAlwaysWrite modevar = w == square "Write" $
$ isPossibleWrite modevar = w == diamond "Write" || w == square "Write" $
$ isRef modevar = c == "Ref" $
$ isCopy modevar = c == "Copy" $
$ isIn modevar = i == "In" $
$ isOut modevar = o == "Out" $

Требования к тегам:

$ isOut mode -> isAlwaysWrite mode $
$ isRead mode -> isIn mode $

// TODO: rest conditions ??

=== Eval Rules

// FIXME: make connected to syntax
*TODO*

#h(10pt)

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

#h(10pt)

=== Correctness

// TODO: FIXME: well formatness for mode, extract
// TODO: FIXME: check for mode, is recursion required ??
// TODO: FIXME: check mode & access corectness in os correct

// TODO: check all requirements
#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ is correct],
    $isOut mode -> isAlwaysWrite mode$, // NOTE; strong requirment should write
    $isRead mode -> isIn mode$,
    $isPossibleWrite mode and (isOut mode or not isCopy mode) -> isAlwaysWrite pathenvmode(sigma, x)$, // NOTE: may mode => should sigma(x)
    $isRead mode -> pathenvval(mu, sigma, x) != bot and pathenvval(mu, sigma, x) != X$,

    $isCorrect_(cl sigma, mu cr) (mode, x)$,
  )
))

#h(10pt)

=== Call Initialization

Отсутствующий нижний индекс ($ref$, $copy$) означает произвольный индекс.
Считается, что выбранный индекс одинаков в рамках одного правила.

// NOTE: no empty type
// #align(center, prooftree(
//   vertical-spacing: 4pt,
//   rule(
//     name: [ add paths init],

//     $cl sigma, mu, l cr stretch(~>)^nothing cl sigma, mu, l cr$,
//   )
// ))

// #h(10pt)

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ add paths field by copy],

    // TODO: check that access is what required ??
    $cl sigma, mu, l cr xarrowSquiggly(p : ())_copy cl pathenvmem(sigma, p) <- l, mu [l <- 0], l + 1 cr$,
  )
))

#h(10pt)

// NOTE: do nothing, ref init by default
#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ add paths field by reference],

    $cl sigma, mu, l cr xarrowSquiggly(p : ())_ref cl sigma, mu, l cr$,
  )
))

#h(10pt)

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ add paths ref],
    $cl sigma, mu, l cr xarrowSquiggly(*p : t)_ref cl sigma', mu', l' cr$,
    $isRef mode$,

    $cl sigma, mu, l cr xarrowSquiggly(p : \& mode t) cl sigma', mu', l' cr$,
  )
))

#h(10pt)

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ add paths ref],
    $cl sigma, mu, l cr xarrowSquiggly(*p : t)_copy cl sigma, mu, l cr$,
    $isCopy mode$,

    $cl sigma, mu, l cr xarrowSquiggly(p : \& mode t) cl sigma', mu', l' cr$,
  )
))

#h(10pt)

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ add paths tuple],
    $cl sigma, mu, l cr xarrowSquiggly(p.1 : t_1) cl sigma_1, mu_1, l_1 cr$,
    $...$,
    $cl sigma_(n - 1), mu_(n - 1), l_(n - 1) cr xarrowSquiggly(p.n : t_n) cl sigma_n, mu_n, l_n cr$,

    $cl sigma, mu, l cr xarrowSquiggly(p : [t_1, ... t_n]) cl sigma_n, mu_n, l_n cr$,
  )
))

#h(10pt)

#align(center, prooftree(
  vertical-spacing: 4pt,
  rule(
    name: [ add paths funciton pointer],

    $cl sigma, mu, l cr xarrowSquiggly(F_x) cl sigma, mu, l cr$,
  )
))

#h(10pt)

=== Call Finalization

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

    $pathenvtype(sigma, y) = F_f$,

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

    $pathenvval(mu, sigma, x) != bot$,
    $pathenvval(mu, sigma, x) != X$,

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

    $isPossibleWrite sigma(x)$,

    $cl sigma, mu, l cr
     xarrow("WRITE" x)
     cl sigma, pathenvval(mu, sigma, x) <- 0, l cr$,
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

=== Combination

$ combine(mu_1, mu_2)[i] = combine_e (mu_1[i], mu_2[i]) $
$ combine_e (bot, bot) = bot $
$ combine_e (0, 0) = 0 $
$ combine_e (\_, \_) = X $

]
