(*** Auxiliary functions ***)
let rec range i n = if i > n then [] else i::(range (i+1) n)
let rec exp b e = if e=0 then 1 else b * (exp b (e-1))
let rec prefix = function 0 -> fun _ -> []
                        | n -> function []      -> failwith ("ERROR: list not long enough to cut off prefix")
                                      | (x::xs) -> x::(prefix (n-1) xs)
                                                 
(*** Output ***)
let verbosity = 2 (* 0=silent, 
                     1=see info about number and widths of tables in fixpoint iterations, 
                     2=... plus recursion and results, 
                     3=... and arguments and environments, 
                     4=... and function table building in application cases *)
let depth = ref 0
let section_start = ref true
let indent_up _  = incr depth;
                   section_start := true
let indent_down _ = decr depth
let output i s = if i <= verbosity then
                   begin
                     let prefix = String.concat "" (List.map (fun _ -> "| ") (range 1 (!depth - 1))) ^
                                    if !depth > 0 then
                                      "|" ^ if !section_start then "-" else " "
                                    else ""
                     in
                     print_string(prefix ^ s ^ "\n");
                     flush stdout
                   end;
                 section_start := false

(*** Types and terms ***)
type ho_type = FuncType of ho_type list
let grtype = FuncType([])
                      
type term = Var of string
          | Base of string
          | Appl of term * ((term * ho_type) list)
          | Lamb of string list * term
          | Mu of string * ho_type * term
          | Nu of string * ho_type * term

let rec is_subterm t t' = (t=t') || match t' with
                                      Appl(s,ts) -> (is_subterm t s) || (List.fold_left (fun b -> fun (t',_) -> b || is_subterm t t') false ts)
                                    | Lamb(_,t'') -> is_subterm t t''
                                    | Mu(_,_,t'') -> is_subterm t t''
                                    | Nu(_,_,t'') -> is_subterm t t''
                                    | _ -> false


module VarSet = Set.Make(String);;

let rec free_vars = function Var(x) -> VarSet.singleton x
                           | Base(_) -> VarSet.empty
                           | Appl(f,ts) -> let fvs = List.fold_left VarSet.union VarSet.empty (List.map (fun (t,_) -> free_vars t ) ts) in
                                           VarSet.union (free_vars f) fvs
                           | Lamb(xs,t) -> let fvs = free_vars t in
                                           List.fold_left (fun s -> fun x -> VarSet.remove x s) fvs xs
                           | Mu(x,_,t) -> VarSet.remove x (free_vars t)
                           | Nu(x,_,t) -> VarSet.remove x (free_vars t)

let is_strongly_unnested =
  let free_varss ts = List.fold_left VarSet.union VarSet.empty (List.map free_vars ts) in
  let check_free_vars_in_args x ys = 
    let rec check = function Appl(Var(z),ts) -> let ts = List.map fst ts in
                                                if x=z then
                                                  VarSet.subset (free_varss ts) ys
                                                else List.fold_left (fun b -> fun t -> b && check t) true ts
                           | Appl(f,ts) -> let ts = List.map fst ts in
                                           List.fold_left (fun b -> fun t -> b && check t) (check f) ts
                           | Lamb(_,t) -> check t
                           | Mu(z,_,t) -> x=z || x<>z && check t
                           | Nu(z,_,t) -> x=z || x<>z && check t
                           | _ -> true
    in
    check                                                                              
  in
  let rec isunnest = function Appl(f,ts) -> List.fold_left (fun b -> fun t -> b && (isunnest t)) (isunnest f) (List.map fst ts)
                            | Lamb(_,t) -> isunnest t
                            | Mu(x,_,Lamb(ys,t)) -> (check_free_vars_in_args x (VarSet.of_list ys) t) && (isunnest t)
                            | Nu(x,_,Lamb(ys,t)) -> (check_free_vars_in_args x (VarSet.of_list ys) t) && (isunnest t)
                            | Mu(x,_,t) -> (check_free_vars_in_args x VarSet.empty t) && (isunnest t)
                            | Nu(x,_,t) -> (check_free_vars_in_args x VarSet.empty t) && (isunnest t)
                            | _ -> true
  in
  isunnest
  
let show_term =
  let is_atomic = function Var _  -> true
                         | Base _ -> true
                         | _      -> false
  in
  let rec show = function Var(x) -> x
                        | Base(f) -> f
                        | Appl(t,ts) -> let (lpo,rpo) = if is_atomic t then ("","") else ("(",")") in
                                        let (sep,lpa,rpa) = if List.length ts > 1 || (List.length ts = 0) || not(is_atomic(fst (List.hd ts))) then
                                                              ("","(",")")
                                                            else
                                                              (" ","","")
                                        in
                                        lpo ^ show t ^ rpo ^ sep ^ lpa ^ String.concat "," (List.map (fun (t,_) -> show t) ts) ^ rpa
                        | Lamb(xs,t) -> "\\" ^ String.concat "," xs ^ "." ^ show t
                        | Mu(x,_,t) -> "mu " ^ x ^ "." ^ show t
                        | Nu(x,_,t) -> "nu " ^ x ^ "." ^ show t
  in
  show 

  
(*** Signature of a lattice ***)
module type Lattice =
  sig
    type t

    val show: t -> string
    
    val equal : t -> t -> bool

    val top: unit -> t
    val bot: unit -> t
      
    val size: unit -> int
    val height: unit -> int

    val first: unit -> t
    val next: t -> t option

    val base_funcs: (string * (t list -> t)) list
  end

module type HOLattice =
  sig
    type result
    val evaluate: term -> result
  end
  
(*** Building HO lattices including the evaluation of terms over them using function tables ***)
module MakeHOLattice(M: Lattice): HOLattice =
  struct
    type result = M.t
                
    type 'a entry = Any
                  | Key of 'a

    let key x = Key(x)
    let any = Any
            
    type ho_func = Const of M.t
                 | Table of (ho_func list entry * M.t) list

    let const x = Const(x)
    let table t = Table(t)              

    let table_width = function Const _ -> 1
                             | Table(entries) -> List.length (List.filter (function (Key(_),_) -> true | _ -> false)
                                                                entries)
                                               
    let bot = function FuncType [] -> Const(M.bot ())
                     | FuncType ts -> Table([Any,M.bot ()])
    let top = function FuncType [] -> Const(M.top ())
                     | FuncType ts -> Table([Any,M.top ()])

    let rec elements =
      let base_elements = let rec enum elems = function None -> elems
                                                      | Some x -> enum (const(x)::elems) (M.next x)
                          in
                          enum [] (Some(M.first ()))
      in
      function FuncType [] -> base_elements
             | FuncType ts -> let args = arguments ts in
                              let first = List.map (fun a -> (a,M.first ())) args in
                              let next =
                                let rec nxt acc = function []        -> None
                                                         | (a,x)::rs -> match M.next x with
                                                                          None -> nxt ((a,M.first ())::acc) rs
                                                                        | Some y -> Some ((List.rev acc) @ ((a,y)::rs))
                                in
                                nxt []
                              in
                              let rec enum tables = function None -> tables
                                                           | Some t -> enum ((Table(List.map (fun (a,v) -> (Key(a),v)) t))::tables) (next t)
                              in
                              enum [] (Some(first))
    and arguments = function [] -> []
                           | ts -> let elems = List.map elements ts in
                                   let rec combine = function []      -> [[]]
                                                            | es::ess -> let cs = combine ess in
                                                                         List.flatten (List.map (fun c -> (List.map (fun e -> e::c) es)) cs)
                                   in
                                   combine elems

    let show_table =
      let rec show b =
        function Const(c) -> let (lp,rp) = if b then ("[","]") else ("","") in lp ^ M.show c ^ rp
               | Table(entries) -> (if b then
                                     "[" ^ String.concat "|" (List.map (function (Any,v) -> "_:" ^ M.show v
                                                                               | (Key(args),v) -> let (lp,rp) = if List.length args > 1 then ("(",")") else ("","") in
                                                                                                  lp ^ String.concat ","
                                                                                                         (List.map (fun t -> show false t) args) ^ rp ^ ":" ^ M.show v)
                                                                entries)
                                     ^ "]"
                                   else
                                     "[.]")
                                   ^ " of width " ^ string_of_int (List.length entries)
      in
      show true
      
    let rec tables_equal table1 table2 =
      let includes entries table = List.for_all (fun (key,v) -> (match key with
                                                                   Any -> is_default v table  (* das ist eigentlich falsch, denn das wäre bei Superset so! *)
                                                                 | Key(key) -> try
                                                                                 v = table_lookup key table
                                                                               with Not_found -> false))
                                     entries
      in 
      match (table1,table2) with
         (Const(x),Const(y)) ->  M.equal x y
       | (Table(entries1),Table(entries2)) -> (includes entries1 table2) && (includes entries2 table1)
       | _ -> false
    and table_lookup args table =
      let rec find_in = function [] -> raise Not_found
                               | (Any,v)::_ -> v
                               | (Key(args'),v)::ps -> if try
                                                            List.for_all2 (fun t1 -> fun t2 -> tables_equal t1 t2) args args'
                                                          with Invalid_argument(_) -> false
                                                       then v
                                                       else find_in ps 
      in
      match table with
        Table(entries) -> find_in entries
      | Const(c) -> c  
    and is_default v = function
        Table(entries) -> List.exists (fun (k,v') -> k=Any && v=v') entries
      | Const(c) -> v=c
           
    let size =
      let m = M.size () in
      let rec aux_size = function FuncType args -> let argssizes = List.fold_left (fun x y -> x*y) 1 (List.map aux_size args) in
                                                   exp m argssizes
      in
      aux_size

    let height = function FuncType args -> (M.height ()) * (List.fold_left (fun x y -> x*y) 1 (List.map size args))

    let max_table_width = function FuncType args -> List.fold_left (fun b -> fun a -> b * (size a)) 1 args
                                                  
    let evaluate term =
      let env = ref [] in
      let update_env t v = 
        env := (t,v)::(List.filter (fun (t',_) -> not (is_subterm t t')) !env)
      in
      let get_table t = try
                          Some(List.assoc t !env)
                        with Not_found -> None
      in
      let get_var_table x = match get_table (Var(x)) with  
                                  Some(table) -> table
                                | None -> failwith ("ERROR: unbound variable `" ^ x ^ "´!")
      in
      let show_arguments args =
        List.iteri (fun i -> fun t -> output 3 (" #" ^ string_of_int i ^ " = " ^ show_table t)) args;
      in
      let var_table_lookup args x =
        let xt = get_var_table x in
        match xt with
          Table(entries) -> let rec find_in = function [] -> failwith ("ERROR: table for variable `" ^ x ^ "´ has no default value!")
                                                     | (Any,v)::_ -> update_env (Var(x)) (Table((Key(args),v)::entries)); v
                                                     | (Key(args'),v)::ps -> if try
                                                                                 List.for_all2 (fun t1 -> fun t2 -> tables_equal t1 t2) args args'
                                                                               with Invalid_argument(_) -> false
                                                                             then v
                                                                             else begin show_arguments args';show_arguments args; find_in ps end
                            in
                            find_in entries
        | Const(c) -> c  
      in
      let table_map f =
        function Const(c)       -> (Const(c),false)
               | Table(entries) -> let rec tmap c = function []                -> ([],c)
                                                           | (Any,v)::rs       -> let (entries',c') = tmap c rs in
                                                                                  ((Any,v)::entries',c') 
                                                           | (Key(args),v)::rs -> let v' = f args in
                                                                                  let (entries',c') = tmap c rs in
                                                                                  ((Key(args),v')::entries', c' || (v <> v')) 
                                   in
                                   let (entries',c) = tmap false entries in
                                   (Table(entries'), c)
      in

      let base_func_lookup args f =
        let ff = try
                   List.assoc f M.base_funcs
                 with Not_found -> failwith ("ERROR: function `" ^ f ^ "´ is undefined!")
        in
        ff (List.map (function Const(c) -> c
                             | Table(_) -> failwith ("ERROR: expected first-order base function. Use term algebra to build higher-order (base) functions!")) args)
      in

      let make_table f = function FuncType([]) -> Const(f [])
                                | FuncType(argtypes) -> Table(List.map (fun args -> (Key(args), f args)) (arguments argtypes))
      in

      let show_environment _ =
        List.iter (fun (x,t) -> output 3 (" " ^ show_term x ^ " = " ^ show_table t)) !env;
      in

      let merge_iterations =
        function (Table(old_entries),Table(new_entries)) -> let l = (List.length old_entries) - (List.length new_entries) in
                                                            Table((prefix l old_entries)@new_entries)
               | _ -> failwith ("ERROR: cannot merge non-tables in FP iteration!")
      in

      let rec eval term args =
        output 2 ("Starting evaluation of term `" ^ show_term term ^ "´");
        output 2 (let l = List.length args in
                  "on " ^ string_of_int (List.length args) ^ " argument" ^ (if l=1 then "" else "s"));
        show_arguments args;
        output 3 (let l = List.length !env in "w.r.t. " ^ (if l=0 then "the empty " else "") ^ "environment" ^ (if l>0 then ":" else ""));
        show_environment ();
        indent_up ();
        let result = match term with
            Var(x)  -> output 2 "Variable case.";
                       var_table_lookup args x
          | Base(f) -> output 2 "Base function case.";
                       base_func_lookup args f
          | Appl(t,ts) -> output 2 "Application case.";
                          let new_args = List.map (fun (t',tau) -> match get_table t' with
                                                                       Some(table) -> begin
                                                                                        output 4 ("Table for argument `" ^ show_term t' ^ "´ is available.");
                                                                                        table
                                                                                      end
                                                                      | None -> begin
                                                                                  output 4 ("Now making table for argument `" ^ show_term t' ^ "´");
                                                                                  let table = make_table (eval t') tau in
                                                                                  update_env t' table;
                                                                                  table
                                                                                end)
                                           ts
                          in
                          eval t (new_args@args)
          | Lamb(xs,t) -> output 2 "Lambda-abstraction case.";
                          let rec bind ys bs = match (ys,bs) with
                              ([],_) -> bs
                            | (z::zs,[]) -> failwith "ERROR: not enough arguments to bind all lambda variables!"
                            | (z::zs,c::cs) -> update_env (Var(z)) c;
                                               bind zs cs
                          in
                          let rargs = bind xs args in
                          eval t rargs
          | Mu(x,tau,t) -> output 2 "LFP case.";
                           let mt = max_table_width tau in
                           let ht = height tau in
                           let i = ref 1 in
                           update_env (Var(x)) (Table([(Key(args),M.bot ()); (Any,M.bot ())]));
                           while output 1 ("starting LFP iteration #" ^ string_of_int !i ^ " for FP variable `" ^ x ^ "´");
                                 incr i;
                                 output 3 (let l = List.length !env in
                                           "with " ^ (if l=0 then "empty " else "") ^ "environment" ^ (if l>0 then ":" else ""));
                                 show_environment 3;
                                 let xt = get_var_table x in
                                 output 1 ("width of table for FP variable `" ^ x ^ "´ is " ^ string_of_int (table_width xt) ^ " of possible " ^
                                             (if mt > 0 then string_of_int mt else ">" ^ string_of_int max_int));
                                 let (next_table,changed) = table_map (eval t) xt in
                                 let ln = table_width next_table in
                                 let xt = get_var_table x in
                                 let lx = table_width xt in
                                 if (ln <> lx) then
                                   begin
                                     update_env (Var(x)) (merge_iterations (xt,next_table));
                                     true
                                   end
                                 else
                                   begin
                                     update_env (Var(x)) next_table;
                                     changed
                                   end
                           do ()
                           done;
                           output 1 ("finished after " ^ string_of_int (!i-1) ^ " iterations of possible " ^
                                       (if ht > 0 then string_of_int ht else ">" ^ string_of_int max_int));
                           table_lookup args (get_var_table x)
          | Nu(x,tau,t) -> output 2 "GFP case.";
                           let mt = max_table_width tau in
                           let ht = height tau in
                           let i = ref 1 in
                           update_env (Var(x)) (Table([(Key(args),M.top ()); (Any,M.top ())]));
                           while output 1 ("starting GFP iteration #" ^ string_of_int !i ^ " for FP variable `" ^ x ^ "´");
                                 incr i;
                                 output 3 (let l = List.length !env in
                                           "with " ^ (if l=0 then "empty " else "") ^ "environment" ^ (if l>0 then ":" else ""));
                                 show_environment 3;
                                 let xt = get_var_table x in
                                 output 1 ("width of table for FP variable `" ^ x ^ "´ is " ^ string_of_int (table_width xt) ^ " of possible " ^
                                             (if mt > 0 then string_of_int mt else ">" ^ string_of_int max_int));
                                 let (next_table,changed) = table_map (eval t) xt in
                                 let ln = table_width next_table in
                                 let xt = get_var_table x in
                                 let lx = table_width xt in
                                 if (ln <> lx) then
                                   begin
                                     update_env (Var(x)) (merge_iterations (xt,next_table));
                                     true
                                   end
                                 else
                                   begin
                                     update_env (Var(x)) next_table;
                                     changed
                                   end
                           do ()
                           done;
                           output 1 ("finished after " ^ string_of_int (!i-1) ^ " iteration" ^ (if !i=2 then "" else "s") ^ " of possible " ^
                                       (if ht > 0 then string_of_int ht else ">" ^ string_of_int max_int));
                           table_lookup args (get_var_table x)
        in
        indent_down ();
        output 2 ("resulting in value `" ^ M.show result ^ "´.");
        result
      in
      output 1 ("Evaluation initialised for term `" ^ show_term term ^ "´");
(*      let unnested = is_strongly_unnested term in
      output 1 ("Checking whether it is strongly unnested ... " ^ (if unnested then "yes!" else "no.")); *)
      eval term []
end;;
     



