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
