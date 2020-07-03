open HOFPIteration

module IntSet = Set.Make  ( struct 
                              type t = int
                              let compare = compare
                            end
                          )

let n = 1

module PowerSetLattice =
  struct

    type t = IntSet.t
    
    let equal = IntSet.equal

    let show set = 
       "{" ^ (String.concat "," (List.map (fun elem -> string_of_int elem) (IntSet.elements set))) ^ "}"
    
    let top =
      let range a b =
        let rec aux acc high low =
          if high >= low then
            aux (high::acc) (high - 1) low
          else acc
        in if a < b then aux [] b a else List.rev (aux [] a b)
      in
        IntSet.of_list (range 0 n)
    
    let bot =
        IntSet.empty
    
    let size _ = int_of_float (2. ** ((float) (n+1)) )
    let height _ = n+2
    
    let p _ = IntSet.add 0 (IntSet.empty) 
    
    let first = IntSet.empty

    let list_of_all_subsets = 
      let rec superset_list = function
      | [] -> [[]]
      | x :: xs -> 
         let ps = superset_list xs in
         ps @ List.map (fun ss -> x :: ss) ps
      in
        List.map (fun subset_list -> IntSet.of_list subset_list) (superset_list (IntSet.elements top))

    let next set =  
      let rec find set lst c = 
        match lst with
          | [] -> failwith ("ERROR: subset not found")
          | hd::tl -> if (IntSet.equal set hd) then c else find set tl (c+1)
      in
      let idx = find set list_of_all_subsets 0 in
      if idx == (size()-1) then
        None
      else
        Some (List.nth list_of_all_subsets (idx+1))
      


    let disj =  function    [x;y] -> IntSet.union x y
                        | _     -> failwith ("ERROR: wrong number of arguments given to function `disj´!")

    let conj =  function    [x;y] -> IntSet.inter x y
                        | _     -> failwith ("ERROR: wrong number of arguments given to function `conj´!")
                        
    let neg =   function    [x] -> IntSet.diff top x
                        | _     -> failwith ("ERROR: wrong number of arguments given to function `neg´!")
    
    
    let a_dia = function    [x]   -> IntSet.fold  (fun elem new_set-> if elem == 0 then 
                                                                            IntSet.add 1 new_set
                                                                          else
                                                                            if elem < n then
                                                                              IntSet.add (elem-1) (IntSet.add (elem+1) new_set)
                                                                            else
                                                                              IntSet.add (elem-1) new_set
                                                      ) x IntSet.empty   
                              | _     -> failwith ("ERROR: wrong number of arguments given to function `a-diamond!")
    
    let a_box = function        [x]   -> neg [a_dia [neg [x]]]
                              | _     -> failwith ("ERROR: wrong number of arguments given to function `a-box!")

    let b_dia = function        [x]   ->  IntSet.fold (fun elem new_set -> 
                                                    if elem == 0 then
                                                      IntSet.add 0 (IntSet.add 1 new_set)
                                                    else
                                                    if elem < n then
                                                      IntSet.add (elem+1) new_set
                                                    else
                                                      new_set
                                                    ) x IntSet.empty
                              | _     -> failwith ("ERROR: wrong number of arguments given to function `b-diamond!")
    

    let b_box = function    [x]   -> neg [b_dia [neg [x]]]
                              | _     -> failwith ("ERROR: wrong number of arguments given to function `b-box!")

    let base_funcs = [("p",p);("neg", neg);("disj",disj); ("conj", conj); ("<a>", a_dia); ("[a]", a_box); ("<b>", b_dia); ("[b]", b_box)]
  end


module PS = MakeHOLattice(PowerSetLattice)

  let _ =
    let typ0 = grtype in
    let typ1 = FuncType([typ0]) in
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
    let phi = Appl(   Nu("F",typ1,Lamb(["f"], Appl(Base("conj"), [(left_conj,typ0);(right_conj,typ0)]))),    [(a_dia_func,typ1)]) in
    PS.evaluate phi
