type log_type = EvalTrace | Skeleton | Summary | ChainCut

let log_type_bitmask = function
  | EvalTrace -> 1
  | Skeleton  -> 2
  | Summary   -> 4
  | ChainCut  -> 8

type logger = StdoutLogger of int
            | NoLogging
            
let make_stdout_logger log_types =
    let bitmask = List.fold_left (fun acc v -> Int.logor acc v) 0 (List.map log_type_bitmask log_types) in
    StdoutLogger bitmask
    
let make_stdout_logger_all = StdoutLogger Int.max_int

let log (logger: logger) (l: log_type) (msg: string Lazy.t) =
    match logger with
      | NoLogging -> ()
      | StdoutLogger allowedLog when Int.logand allowedLog (log_type_bitmask l) != 0 -> Printf.printf "%s\n" (Lazy.force msg)
      | StdoutLogger _ -> ()

