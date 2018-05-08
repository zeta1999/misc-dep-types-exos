module Run
open RBMap
open FStar.IO

module M = RBMap
module I = FStar.IO

let main =
   let ok = M.test_map_01 () in
   if ok = true then print_string "OK\n"
   else print_string "Failure\n"
