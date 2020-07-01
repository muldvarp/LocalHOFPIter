(*** The reachability example ***)

open HOFPIteration

let n = ref 2
    
module RELattice =
  struct
    type t = Top
           | Bot
           | Num of int

    let show = function Top -> "T"
                      | Bot -> "B"
                      | Num(i) -> string_of_int i
                                
    let top = Top
    let bot = Bot

    let first = Bot
    let next = function Top -> None
                      | Bot -> Some(Num(0))
                      | Num(i) -> if i = 3 * !n then Some(Top) else Some(Num(i+1))
                                
    let num i = Num(i)
              
    let height _ = 3
    let size _ = 3 * !n + 3

    let null _ = num(0)
    let a = function [Top]    -> Top
                   | [Num(i)] -> if i=0 then Num(!n-1)
                                 else if i < !n then Num(i-1)
                                 else Bot
                   | [Bot]    -> Bot
                   | _        -> failwith ("ERROR: wrong number of arguments given to function `a´!")
    let b = function [Top]    -> Top
                   | [Num(i)] -> if i=0 then Num(2 * !n - 1)
                                 else if i = !n then Num(0) 
                                 else if i > !n && i < 2 * !n then Num(i-1)
                                 else Bot
                   | [Bot]    -> Bot
                   | _        -> failwith ("ERROR: wrong number of arguments given to function `b´!")
    let c = function [Top]    -> Top
                   | [Num(i)] -> if i=0 then Num(3 * !n)
                                 else if i=2 * !n then Num(0) 
                                 else if i > 2 * !n && i <= 3 * !n then Num(i-1)
                                 else Bot
                   | [Bot]    -> Bot
                   | _        -> failwith ("ERROR: wrong number of arguments given to function `c´!")
    let ite = function [Num(0);_] -> Top
                     | [_;x]      -> x
                     | _        -> failwith ("ERROR: wrong number of arguments given to function `ite´!")

    let base_funcs = [("null",null); ("a",a); ("b",b); ("c",c); ("ite",ite)]           
  end

let _ =
  n := (try
          int_of_string Sys.argv.(1)
        with _ -> 2);
  
module RE = MakeHOLattice(RELattice)

let _ =
  let phi_reach =
    let typ0 = grtype in
    let typ1 = FuncType([typ0]) in
    let null = (Base("null"),typ0) in
    let x = (Var("x"),typ0) in
    let a = (Base("a"),typ1) in
    let a' = fst a in
    let b = (Base("b"),typ1) in
    let b' = fst b in
    let c x = (Appl(Base("c"),[x]),typ0) in
    let f = Var("f") in
    let g = Var("g") in
    let ite (x,y) = Appl(Base("ite"),[x;y]) in
    let aux_var_no = ref 0 in
    let comp f g =
      let aux_var _ =
        let i = !aux_var_no in
        incr aux_var_no;
        "x_" ^ string_of_int i
      in
      let x = aux_var () in
      (Lamb([x], Appl(f,[(Appl(g,[(Var(x),typ0)]),typ0)])),typ1)
    in
    Appl(Mu("F",
            Lamb(["f"; "g"; "x"],
                 ite((Appl(f,[(Appl(Var("g"),[x]), typ0)]), typ0),
                     (Appl(Var("F"),[(comp a' f); (comp b' g); c(x)]), typ0)))),
         [a; b; c(null)])
  in
  RE.evaluate phi_reach

