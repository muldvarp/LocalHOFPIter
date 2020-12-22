(*** The model checking example ***)

open HOFPIteration

let n = ref 2

let _ =
  n := (try
          int_of_string Sys.argv.(1)
        with _ -> 2);
  print_string ("Strictness analysis of function iter over domain " ^ string_of_int !n ^ "={0,..," ^ string_of_int (!n -1) ^ "}\n")

module FiniteLinearLattice =
  struct

    type t = int
    
    let equal = (=)

    let show = string_of_int

    let top _ = !n - 1
    
    let bot _ = 0 
    
    let size _ = !n
      
    let height _ = !n
    
    let p _ = Array.init !n (fun i -> i=0)  
    
    let first _ = 0

    let next i = if i = !n -1 then None else Some (i+1)
                   
    let disj = function [x;y] -> max x y
                      | _ -> failwith ("Unexpected number of arguments for function disj!")
    let conj = function [x;y] -> min x y
                      | _ -> failwith ("Unexpected number of arguments for function conj!")
                                       
    let base_funcs = [("\\/",disj); ("/\\", conj); ("bot", bot)]
  end
  
module PS = MakeHOLattice(FiniteLinearLattice)
          
let _ =
    let typ0 = grtype in
    let typ1 = FuncType([typ0]) in
    let typ2 = FuncType([typ1;typ0;typ0]) in

    
    let n = Var("n") in
    let n_t = (n,typ0) in
    let y_t = (Var("y"),typ0) in
    let g = Var("g") in
    let g_t = (g,typ1) in
    let reccall_t = (Appl(Var("iter"),[g_t; n_t; (Appl(g,[n_t]),typ0)]), typ0) in
    let fp = Mu("iter",typ2, Lamb(["g";"n";"y"], Appl(Base("/\\"),[n_t; (Appl(Base("\\/"),[y_t; reccall_t]),typ0)]))) in
    let b_t = (Base("bot"),typ0) in
    let fb_t = (Lamb(["x"],Base("bot")),typ1) in
    
    let phi = Appl(fp,[fb_t; b_t; b_t]) in
    PS.evaluate phi
