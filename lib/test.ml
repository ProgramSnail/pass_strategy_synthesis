open GT
open OCanren

module Tag = struct
  [@@@warning "-26-27-32-33-34-35-36-37-38-39-60-66-67"]
  ocanren type tag = Ref | Value

  module Test = struct
      @type answer = logic GT.list with show

      let _ =
        Printf.printf "%s" @@ show(answer) (Stream.take (run q (fun q -> ocanren {q === Ref})
                                                               (fun q -> q#reify reify)))
   end
end

module Stmt = struct
  ocanren type ('d, 'dl) stmt = Call of 'd * 'dl | Read of 'd | Write of 'd

  module Test = struct
    @type answer1 = Nat.ground List.ground GT.list with show
    @type answer  = (Nat.ground, Nat.ground List.ground) ground GT.list with show
    let _ = Printf.printf "%s\n" @@ show(answer1) (Stream.take (run q (fun q -> ocanren {Call (1, [2]) === Call (1, q)})
                                                  (fun q -> q#reify (List.prj_exn Nat.prj_exn))))

    let _ = Printf.printf "%s\n" @@ show(answer) (Stream.take (run q (fun q -> ocanren {Call (1, [2]) === q})
                                                                     (fun q -> q#reify (prj_exn Nat.prj_exn (List.prj_exn Nat.prj_exn)))))
  end
end
