module type Interpreter = sig
  type term
  val scope_check : Syntax_tree.term -> term
  val pretty_term : term -> string
  val run : Logger.logger -> term -> term
end

module Runner (I: Interpreter) = struct
  let interpret (logger: Logger.logger) (t: Syntax_tree.term) =
      let code = I.scope_check t in
      let result = I.run logger code in
      I.pretty_term result
end

let interpreters: (string * (module Interpreter)) list  =
    [ "functional", (module Interpreters.Functional : Interpreter);
      "fully-lazy-functional", (module Interpreters.Fully_lazy_functional : Interpreter);
      "fully-lazy-functional-linked-env", (module Interpreters.Fully_lazy_functional_linked_env : Interpreter);
      "fully-lazy-functional-black-mark", (module Interpreters.Fully_lazy_functional_black_mark : Interpreter);
      "imperative", (module Interpreters.Imperative : Interpreter);
      "fully-lazy-imperative", (module Interpreters.Fully_lazy_imperative : Interpreter);
    ]

let loop (mode: string) (filename: string) () =
  let inx = Core.In_channel.create filename in
  let input = Core.In_channel.input_all inx in
  let res = Parser.run_parser Parser.parse_program input in
  match res with
    | Error err -> Printf.printf "%s\n" err
    | Ok tree -> 
         (try 
           let interpreter_module = List.assoc mode interpreters in
           let module I = (val interpreter_module : Interpreter) in
           let open Runner(I) in
           let logger = Logger.make_stdout_logger_all in
           Printf.printf "Interpreter %s, final result: %s\n" mode (interpret logger tree)
         with Not_found -> Printf.printf "Invalid mode.")
 

let () =
  Core.Command.basic_spec ~summary:"Parse and display λ-terms"
    Core.Command.Spec.(empty +> anon ("mode" %: string) +> anon ("filename" %: string))
    loop
  |> Command_unix.run


