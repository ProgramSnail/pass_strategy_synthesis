open OCanren

type data = int

type tag = Ref | Value
type stmt = Call of data * data list | Read of data | Write of data

type body = stmt list

type arg = data * tag
type fun_decl = data * arg list * body

type prog = fun_decl list * body
