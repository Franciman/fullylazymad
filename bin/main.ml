open Core
open Fullylazymad

let functional_interpret (t: Syntax_tree.term) =
  let ft = Functional.scope_check t in
  let res = Functional.run ft in
  Functional.pretty_term res

let imperative_interpret (t: Syntax_tree.term) =
  let it = Imperative.scope_check t in
  let res = Imperative.run it in
  Imperative.pretty_term res 

let fully_lazy_imperative_interpret (t: Syntax_tree.term) =
  let it = Fully_lazy_imperative.scope_check t in
  let res = Fully_lazy_imperative.run it in
  Fully_lazy_imperative.pretty_term res 


let loop filename () =
  let inx = In_channel.create filename in
  let input = In_channel.input_all inx in
  let res = Handwritten_parser.run_parser Handwritten_parser.parse_program input in
  match res with
    | Error err -> fprintf stdout "%s\n" err
    | Ok tree -> 
        (fprintf stdout "FUNCTIONAL RUN:\n";
         fprintf stdout "FINAL RESULT: %s\n" (functional_interpret tree);
         fprintf stdout "IMPERATIVE RUN:\n";
         fprintf stdout "FINAL RESULT: %s\n" (imperative_interpret tree);
         fprintf stdout "FULLY LAZY IMPERATIVE RUN:\n";
         fprintf stdout "FINAL RESULT: %s\n" (fully_lazy_imperative_interpret tree))
 

let () =
  Command.basic_spec ~summary:"Parse and display λ-terms"
    Command.Spec.(empty +> anon ("filename" %: string))
    loop
  |> Command_unix.run


