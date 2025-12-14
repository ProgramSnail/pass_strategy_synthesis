```prolog

/* TODO: arg_tags_eq: check by ndex in array */
/* TODO: arg_tags_neq: check by index in array */

not_in_list(I, []).
not_in_list(I, [X | XT]) : X != I, not_in_list(I, XT).

correct_body_on_arg_borrow(ARGT, B, [], I).
correct_body_on_arg_borrow(ARGT, B, [Write(I)|XT], I). /* overwrite */
correct_body_on_arg_borrow(ARGT, B, [Write(J)|XT], I) :-
  I != J, correct_body_on_arg_borrow(ARGT, B, XT, I).
correct_body_on_arg_borrow(ARGT, B, [Read(J)|XT], I) :-
  I != J, correct_body_on_arg_borrow(ARGT, B, XT, I).
/* read of I is incorrect */
correct_body_on_arg_borrow(ARGT, B, [Call(F, FARGT, ARGS)|XT], I) :-
  not_in_list(I, ARGS), correct_body_on_arg_borrow(ARGT, B, XT, I).
/* func call only correct in all args are not I */

correct_args_map(ARGT, B, [], []).
correct_args_map(ARGT, B, BT, [Ref|TS], [I|IS]) :-
  arg_tags_neq(ARGT, I, ConstRef),
  correct_body_on_arg_borrow(ARGT, B, BT, I),
  correct_args_map(ARGT, B, BT, TS, IS).
correct_args_map(ARGT, B, BT, [ConstRef|TS], [I|IS]) :-
  correct_args_map(ARGT, B, BT, TS, IS).
correct_args_map(ARGT, B, BT, [Copy|TS], [I|IS]) :-
  correct_args_map(ARGT, B, BT, TS, IS).

correct_body(ARGT, B, [Write(I)|XT]) :- arg_tags_neq(ARGT, I, ConstRef),
                                        correct_body(ARGT, B, XT).
correct_body(ARGT, B, [Read(I)|XT]) :- correct_body(ARGT, B, XT).
correct_body(ARGT, B, [Call(F, FARGT, ARGS)|XT]) :- correct_args_map(ARGT, B, BT, FARGT, ARGS),
                                                    correct_body(ARGT, B, XT).
/* FARGT - deduced in the program beforehand */

correct_func(P, func(ARGT, B)) :- correct_body(ARGT, B, B).

correct_all(P, []).
correct_all(P, [X | XT]) :- correct_func(P, X), correct_all(P, XT).

correct(prog(X)) :- correct_all(X, X).

```

