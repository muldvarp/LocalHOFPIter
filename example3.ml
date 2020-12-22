(*** The model checking example ***)

open HOFPIteration

let n = ref 2

let _ =
  n := (try
          int_of_string Sys.argv.(1)
        with _ -> 2);
  print_string ("Model checking HFL property on transition system with parameter " ^ string_of_int !n ^ "\n")

module PowerSetLattice =
  struct

    type t = bool array
    
    let equal = (=)

    let show set = 
       "{" ^ String.concat "," (List.filter (fun s -> s <> "") (Array.to_list (Array.mapi (fun i -> fun b -> if b then string_of_int i else "") set))) ^ "}"
    
    let top _ = Array.make !n true
    
    let bot _ = Array.make !n false
    
    let size _ =
      let rec exp = function 0 -> 1
                           | n -> 2*(exp (n-1))
      in
      exp !n
      
    let height _ = !n + 1
    
    let p _ = Array.init !n (fun i -> i=0)  
    
    let first = bot

    let next set = if set=(top ()) then None
                   else 
                     let change = ref true in
                     Some (Array.mapi (fun i -> fun b -> if !change then
                                                     begin
                                                       change := b;
                                                       not b
                                                     end
                                                   else
                                                     b) set)

    let map2 f x y = Array.init !n (fun i -> f x.(i) y.(i))
                   
    let disj = function [x;y] -> map2 (||) x y
                      | _     -> failwith ("ERROR: wrong number of arguments given to function `disj´!")

    let conj = function [x;y] -> map2 (&&) x y
                      | _     -> failwith ("ERROR: wrong number of arguments given to function `conj´!")
                        
    let neg = function [x] -> Array.map not x
                     | _   -> failwith ("ERROR: wrong number of arguments given to function `neg´!")    
    
    let a_dia = function [x] -> (try
                                  Array.init !n (fun i -> (i>0 && x.(i-1)) || (i< !n-1) && x.(i+1))
                                with Invalid_argument _ -> failwith "Hier!")
                       | _   -> failwith ("ERROR: wrong number of arguments given to function `a-diamond!")

    (*
    let a_box = function        [x]   -> neg [a_dia [neg [x]]]
                              | _     -> failwith ("ERROR: wrong number of arguments given to function `a-box!")
     *)
                                
    let b_dia = function [x] -> Array.init !n (fun i -> x.(0))
                       | _   -> failwith ("ERROR: wrong number of arguments given to function `b-diamond!")
    
    (*
    let b_box = function    [x]   -> neg [b_dia [neg [x]]]
                              | _     -> failwith ("ERROR: wrong number of arguments given to function `b-box!")
     *)
                                       
    let base_funcs = [("p",p);("neg", neg);("disj",disj); ("conj", conj); ("<a>", a_dia); (*("[a]", a_box);*) ("<b>", b_dia) (*; ("[b]", b_box)*)]
  end
  
module PS = MakeHOLattice(PowerSetLattice)
          
let _ =
    let typ0 = grtype in
    let typ1 = FuncType([typ0]) in
    let typ2 = FuncType([typ1]) in
    let a_dia_func = Lamb(["x"], Appl( Base("<a>"), [(Var("x"), typ0)])) in
    let left_conj = Appl(Var("f"), [(Base("p"),typ0)]) in
    let f_composition = Lamb(
                              ["y"], 
                              Appl( 
                                    Var("f"), 
                                    [
                                      ( Appl(
                                          Var("f"), 
                                          [( Var("y"), typ0)]
                                      ),
                                      typ0)
                                    
                                    ]
                                  )
                            ) in
    let right_conj = Appl(Base("<b>"),[(Appl(Var("F"),[(f_composition,typ1)]),typ0)]) in
    let phi = Appl(   Nu("F",typ2,Lamb(["f"], Appl(Base("conj"), [(left_conj,typ0);(right_conj,typ0)]))),    [(a_dia_func,typ1)]) in
    PS.evaluate phi
