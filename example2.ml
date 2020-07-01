(*** The reachability example ***)

open HOFPIteration

(*let tokens = ref "bscscbsscsc" *)
let tokens = ref "bsc"
           
module ParsingLattice =
  struct     
    let n _ = String.length !tokens

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
                      | Num(i) -> if i = (n ()) then Some(Top) else Some(Num(i+1))
                                
    let num i = Num(i)
              
    let height _ = 3
    let size _ = (n ()) + 3

    let start _ = num(0)
    let ende _ = num(n ())

    let check_token t = function [Num(i);Num(j)] -> if j=i+1 && !tokens.[i] = t then Top else Bot
                               | _ -> Bot
    let block = check_token 'b'
    let code = check_token 'c'
    let space = check_token 's'
    let epsilon = function [Num(i);Num(j)] -> if j=i then Top else Bot
                         | _ -> Bot
    let concat f g = function (Num(i) as s, Num(j) as e) -> let rec iter h = if h > j then Bot
                                                                             else let h' = Num(h) in
                                                                                  if f s h' = Top && g h' e = Top then Top
                                                                                  else iter (h+1)
                                                            in
                                                            iter i
                            | _ -> Bot

                                                         
    let join = function [Bot;x] -> x
                      | [x;Bot] -> x
                      | _       -> Top

    let disj = function [Top;_] -> Top
                      | [_;Top] -> Top
                      | _ -> Bot
    let conj = function [Top;Top] -> Top
                      | _ -> Bot

    let nxt = function [Num(i)] -> if i < (n ()) then Num(i+1) else Bot
                     | _ -> Bot
                          
    let base_funcs = [("start",start); ("end",ende); ("block",block); ("code",code); ("space",space); ("eps",epsilon);
                      ("disj",disj); ("conj",conj); ("choice",join); ("next",nxt)]           
  end
  
module Parsing = MakeHOLattice(ParsingLattice)

let _ =
  if Array.length Sys.argv > 1 then tokens := Sys.argv.(1);
  print_string ("Parsing " ^ !tokens ^ "\n");
  let phi_parse =
    let i = ref 0 in
    let get_var pre =
      let j = !i in
      incr i;
      pre ^ string_of_int j
    in
    let typ0 = grtype in
    let typ1 = FuncType([typ0;typ0]) in
    let start = (Base("start"),typ0) in
    let ende = (Base("end"),typ0) in
    let code = Base("code") in
    let block = Base("block") in
    let epsilon = Base("epsilon") in
    let space = Base("space") in
    let choice f g =
      let s = get_var "s" in
      let e = get_var "e" in
      Lamb([s;e],Appl(Base("choice"),[(Appl(f,[(Var(s),typ0);(Var(e),typ0)]),typ0); (Appl(g,[(Var(s),typ0);(Var(e),typ0)]),typ0)]))
    in
    let choice3 x y z = choice x (choice y z) in
    let disj x y = Appl(Base("disj"),[(x,typ0);(y,typ0)]) in
    let conj x y = Appl(Base("conj"),[(x,typ0);(y,typ0)]) in
    let concat' =
      let f = get_var "f" in
      let g = get_var "g" in
      let s = get_var "s" in
      let e = get_var "e" in
      let x = get_var "X" in
      let h = get_var "h" in
      Lamb([f;g;s;e], Mu(x, Lamb([h], disj (conj (Appl(Var(f),[(Var(s),typ0);(Var(h),typ0)]))
                                                 (Appl(Var(g),[(Var(h),typ0);(Var(e),typ0)])))
                                           (Appl(Var(x),[(Appl(Base("nxt"),[(Var(h),typ0)]),typ0)])))))
    in
    let concat f g = Appl(concat',[(f,typ1);(g,typ1)]) in 
    let concat3 f g h = concat f (concat g h) in
    
    let nontermS _ =
      let s = get_var "S" in
      Mu(s, choice space (concat space (Var(s))))
    in
    let nontermB = Mu("B", Lamb(["I"], choice3 epsilon
                                               (concat3 (Var("I")) code (Appl(Var("B"),[(Var("I"),typ1)])))
                                               (concat3 (Var("I")) block (Appl(Var("B"),[(concat (nontermS ()) (Var("I")), typ1)])))))
    in
    let nontermP = Mu("P", concat block (Appl(nontermB,[(nontermS (),typ1)]))) in
    Appl(nontermP, [start; ende])
  in
  Parsing.evaluate phi_parse

