(**1 Implementing the λ-calculus*)

(**1.1 λ-terms*)

type var = string;;
type t =
  | Var of var
  | App of t * t
  | Abs of string * t;;

let rec to_string (term:t) : string = match term with
  | Var s -> s
  | App (t1, t2) -> "(" ^ (to_string t1) ^ " " ^ (to_string t2) ^ ")"
  | Abs (s, t') -> "(λ" ^ s ^  "." ^  (to_string t') ^  ")" ;;

let () =
  print_endline (to_string (Abs ("x", App (Var "y", Var "x"))));
  print_endline (to_string (App (Abs ("x", Var "y"), Var "x")));;


(**1.2 Free variables*)

let rec has_fv (x:var) (term:t) : bool = match term with
  | Var v when v = x -> true
  | App(t1, t2) -> (has_fv x t1) || (has_fv x t2)
  | Abs(s, t') -> (s <> x) && (has_fv x t')
  | _ -> false;;

let () =
  let t = App (Var "x", Abs ("y", App (Var "y", Var "z"))) in
  assert (has_fv "x" t);
  assert (not (has_fv "y" t));
  assert (has_fv "z" t);
  assert (not (has_fv "w" t));;

(**1.3 Fresh variables*)

let n = ref 0;;
let fresh () = let new_var = "x" ^ (string_of_int !n) in n := !n + 1; new_var;;

let test_fresh0 = fresh ();;
let test_fresh1 = fresh ();;

(**1.4 Substitution*)

let rec sub (x:var) (u:t) (t:t) : t = match t with
  | Var v when v = x -> u
  | App (t1, t2) -> App (sub x u t1, sub x u t2)
  | Abs (s, t') when s = x -> let new_s = fresh () in
                              let new_t = sub s (Var new_s) t' in
                              Abs (new_s, new_t)
  | Abs (s, t') when has_fv s u ->  let new_s = fresh () in
                                    let new_t = sub s (Var new_s) t' in
                                    Abs (new_s, sub x u new_t)
  | Abs (s, t') -> Abs (s, sub x u t')
  | _ -> t;;

let () =
  let t = App (Var "x", Abs ("y", Var "x")) in
  let i = Abs ("x", Var "x") in
  let ti = App (Abs ("x", Var "x"), Abs ("y", Abs ("x", Var "x"))) in
  assert (sub "x" i t = ti);
  assert (not (sub "x" (Var "y") (Abs ("y", Var "x")) = Abs("y", Var "y")));;

(**1.5 β-reduction*)

(*the order of reduction is very important to compute factorial for example:
 - App (Abs (s, t), u) -> Some (sub s u t) and not : App (Abs (s, t), u) -> match red u with |Some u' -> Some (App (Abs (s, t), u')) | _ -> Some (sub s u t)
 - App (t1, t2) ->  begin                                      and not :        App (t1, t2) ->  begin
       		let red_t1 = red t1 in								let red_t1 = red t1 in
		        let red_t2 = red t2 in							let red_t2 = red t2 in
		        match (red_t1, red_t2) with							match (red_t1, red_t2) with
		        | (Some (t1'), _) -> Some (App (t1', t2))					| (_, Some (t2')) -> Some (App (t1, t2'))
		        | (_, Some (t2')) -> Some (App (t1, t2'))					| (Some (t1'), _) -> Some (App (t1', t2))
		        | _ -> None									| _ -> None
		     end									     end *)
     
     
let rec red (term:t) : t option = match term with
  | App (Abs (s, t), u) -> Some (sub s u t)
  | Var _ -> None
  | App (t1, t2) ->
     begin
       let red_t1 = red t1 in
       let red_t2 = red t2 in
       match (red_t1, red_t2) with
       | (Some (t1'), _) -> Some (App (t1', t2))
       | (_, Some (t2')) -> Some (App (t1, t2'))
       | _ -> None
     end 
  | Abs (s, t) ->
      begin
       let red_t = red t in
       match red_t with
       | Some (t') -> Some (Abs (s, t'))
       | _ -> None
      end ;;

let rec normalize (term:t) : t = match red term with
  | Some (t) -> normalize t
  | None -> term;;

let reduction (term:t) =
  print_endline (to_string term);
  let steps = ref 0 in
  
  let rec print_red (t:t) = match red t with
    | None -> print_endline ((string_of_int !steps) ^ " reduction steps")
    | Some (new_t) -> print_endline ("-> " ^ (to_string new_t));
                      steps := !steps + 1;
                      print_red new_t
  in

  print_red term;;

let _ =
  let id = Abs ("x", Var "x") in
  let id2 = App (id, id) in
  reduction (App (id2, id2));;
  
(**1.6 Equivalence*)

let eq (t1:t) (t2:t) : bool = (normalize t1) = (normalize t2);;

let () =
  let id = Abs ("x", Var "x") in
  let id2 = App (id, id) in
  assert (eq (App (id2, id2)) id2);;

(**1.7 Optional: proper β-equivalence of λ-terms*)

let rec alpha (t1:t) (t2:t) : bool = match (t1, t2) with
  | (t1, t2) when t1 = t2 -> true
  | (App (t1, t1'), App (t2, t2')) -> (alpha t1 t2) && (alpha t1' t2')
  | (Abs (s1, t1), Abs(s2, t2)) when s1 = s2 -> alpha t1 t2
  | (Abs (s1, t1), Abs(s2, t2)) -> alpha t1 (sub s2 (Var s1) t2)
  | _ -> false;;

let () =
  assert (alpha (Abs ("x", Var "x")) (Abs ("y", Var "y")));
  assert (not (alpha (Abs ("x", Var "x")) (Abs ("x", Var "y"))));;

(*this is not optionnal because the other equivalence does not work for next exercices
"be carefull to use beta and not eq"*)
let beta (t1:t) (t2:t) : bool = alpha (normalize t1) (normalize t2);;

let () =
  let t = App (Abs ("x", Abs ("y", Var "x")), Var "y") in
  print_endline (to_string (normalize t));
  assert (beta t (Abs ("z", Var "y")));;

(**2 Computing in the λ-calculus*)

(**2.1 Identity*)

let id = Abs ("x", Var "x");;

(**2.2 Booleans*)

let btrue = Abs ("x", Abs ("y", Var "x"));;
let bfalse = Abs ("x", Abs ("y", Var "y"));;

(**2.3 Helper functions*)

let rec abss (v_list: var list) (term:t) : t = match v_list with
  | [] -> term
  | v::new_list -> Abs (v, abss new_list term);;

exception Empty_list
let apps (t_list:t list) : t =
  let rec aux  (t_list:t list) (acc:t) : t = match t_list with
    | [] -> acc
    | t::new_list -> aux new_list (App (acc, t))
  in
  match t_list with
  | [] -> raise Empty_list
  | t::new_list -> aux new_list t;;

let () =
  let t = Var "t" in
  let u = Var "u" in
  let v = Var "v" in
  let w = Var "w" in
  assert (apps [t; u; v; w] = App (App (App (t, u), v), w));;

(**2.4 Conditional*)

let bif = abss ["b"; "x"; "y"] (apps [Var "b"; Var "x" ; Var "y"]);;

let () =
  let t = Var "t" in
  let u = Var "u" in
  assert (eq (apps [bif; btrue; t; u]) t);
  assert (eq (apps [bif; bfalse; t; u]) u);;

(**2.5 Natural numbers*)

exception Error_nat
let rec nat (n:int) : t = match n with
  | 0 -> abss ["f"; "x"] (Var "x")
  | n -> match nat (n-1) with
         | Abs ("f", Abs("x", t)) ->  abss ["f"; "x"] (App (Var "f", t))
         | _ -> raise Error_nat;;

let test_0 = nat 0;;
let test_1 = nat 1;;

(**2.6 Successor*)

let succ = abss ["n"; "f"; "x"] (apps [Var "f"; apps [Var "n"; Var "f"; Var "x"]]);;
let () =
  assert (eq (apps [succ; nat 5]) (nat 6));;

(**2.7 Addition*)

let add = abss ["n"; "m"] (apps [Var "m"; succ; Var "n"]);;
let () =
  assert (beta (apps [add; nat 6; nat 5]) (nat 11));;

(**2.8 Multiplication*)

let mul = abss ["n"; "m"; "f"; "x"] (apps [Var "m"; apps [Var "n"; Var "f"]; Var "x"]);;
let () =
  assert (beta (apps [mul; nat 3; nat 4]) (nat 12));;
(*let () = reduction (apps [mul; nat 8; nat 5]);;*)
(* mul n m -> 2*(m+2) *)

(**2.9 Is zero*)

let iszero = abss ["n"; "x"; "y"] (apps [Var "n"; Abs("z", Var "y"); Var "x"]);;
let () =
  assert (beta (apps [iszero; nat 5]) bfalse);
  assert (beta (apps [iszero; nat 0]) btrue);;

(**2.10 Pairs*)

let pair = abss ["x"; "y"; "b"] (apps [bif; Var "b"; Var "x"; Var "y"]);;
let fst = abss ["p"] (apps [Var "p"; btrue]);;
let snd = abss ["p"] (apps [Var "p"; bfalse]);;
let () =
  let t = Var "t" in
  let u = Var "u" in
  assert (beta (apps [fst; apps [pair; t; u]]) t);
  assert (beta (apps [snd; apps [pair; t; u]]) u);;

(**2.11 Predecessor: Fibonacci as a warmup*)

let rec fib_naive (n:int) : int = match n with
  | 0 -> 0
  | 1 -> 1
  | _ -> (fib_naive (n-1)) + (fib_naive (n-2));;
(*exponential complexity*)

let () = assert (fib_naive 10 = 55);;

let rec fib_fun ((fib1, fib2): int*int) : int*int = (fib2, fib1 + fib2);;

let fib (n:int) : int =
  let rec aux (n:int) ((acc1, acc2): int*int) : int = match n with
    | 0 -> acc1
    | _ -> aux (n-1) (fib_fun (acc1, acc2))
  in
  aux n (0, 1);;

let () = assert (fib 10 = 55);;

(**2.12 Predecessor*)

let pred_fun = abss ["p"] (apps [pair; apps [snd; Var "p"]; apps [succ; apps [snd; Var "p"]]]);;
let () =
  assert (beta (apps [pred_fun; apps [pair; nat 1; nat 5]]) (apps [pair; nat 5; nat 6]));;

(*
pred_fun (p,q) = (q, q+1)
pred_fun (pred_fun (p,q)) = (q+1, q+2)
pred_fun applied n times to (p,q) = (q+n-1, q+n)
 *)

let pred = abss ["n"] (apps [fst; apps [Var "n"; pred_fun; apps [pair; nat 0; nat 0]]]);;
let () =
  assert (beta (apps [pred; nat 11]) (nat 10));
  assert (beta (apps [pred; nat 0]) (nat 0));;

(**2.13 Subtraction*)

let substraction = abss ["n"; "m"] (apps [Var "m"; pred; Var "n"]);;
let () =
  assert (beta (apps [substraction; nat 5; nat 3]) (nat 2));;

(**2.14 Warmup on the factorial*)
let fact_fun (f: int -> int) (n:int) : int = match n with
  | 0 -> 1
  | n -> f (n-1) * n;;

let rec fix f n = f (fix f) n;;

let fact (n:int) : int = fix fact_fun n;;

let () =
  assert ((fact 5) == 120) ;;

(**2.15 Fixpoint*)

let fixpoint = abss ["f"] (apps [abss ["x"] (apps [Var "f"; apps [Var "x"; Var "x"]]);
                                 abss ["x"] (apps [Var "f"; apps [Var "x"; Var "x"]])]);;


let fact_aux =  abss ["f"; "n"] (apps [bif;
                                     apps [iszero;
                                           Var "n"];
                                     nat 1;
                                     apps [mul;
                                           Var "n";
                                           apps [Var "f";
                                                 apps [pred;
                                                       Var "n"]]]]);;
                                                       
let factorial = abss ["n"] (apps [fixpoint; fact_aux; Var "n"]);;

let () = assert (beta (App (factorial, nat 5)) (nat 120));;
                                                              
(**3 Optional: De Bruijn indices*)

type dvar = int

type db =
  | DVar of dvar
  | DApp of db * db
  | DAbs of db;;

(**3.1 Conversion*)

(*used to associate abstraction variables with their depth*)
exception Not_found
let rec assoc x l = match l with
  | [] -> raise Not_found
  | (a, b)::_ when a = x -> b
  | _::t -> assoc x t;;

(*I first have not seen that it was only for closed lambda-terms so this is my solution for all terms*)
let db_of_term (term:t) : db =
  let rec increment acc = match acc with
    | [] -> []
    | (x, n)::t -> (x, n+1)::(increment t)
  in
  
  let n_free = ref 0 in (*used to name free variables*)
  
  let rec aux term acc = match term with
    | Var v ->
       begin
         try
           let index = assoc v acc in
           DVar (index)
         with
           Not_found -> let free = !n_free in
                        n_free := !n_free + 1;(*increment each time there is a free variable so there is no interference with other free variables*)
                        DVar (free)
       end
    | App (t1, t2) -> DApp (aux t1 acc, aux t2 acc)
    | Abs (s, t) -> 
       begin
         try
           let unused_test = assoc s acc in (*look if there is another variable named like s, because if there is them assoc will not do its job properly*)
           let new_s = fresh() in
           aux (Abs (new_s, sub s (Var new_s) t)) acc
         with
           Not_found -> n_free := !n_free + 1;(*increment each time there is an abstraction so there is no interference with bounded variables*)
                        DAbs(aux t ((s, 0)::(increment acc)))
       end
  in

  aux term [];;

(*the function for the TD*)
let db_of_term (term:t) : db =
  let rec increment acc = match acc with
    | [] -> []
    | (x, n)::t -> (x, n+1)::(increment t)
  in
  let rec aux term acc = match term with
    | Var v ->
       begin
         let index = assoc v acc in
         DVar (index)
       end
    | App (t1, t2) -> DApp (aux t1 acc, aux t2 acc)
    | Abs (s, t) -> 
       begin
         try
           let unused_test = assoc s acc in (*look if there is another variable named like s, because if there is them assoc will not do its job properly*)
           let new_s = fresh() in
           aux (Abs (new_s, sub s (Var new_s) t)) acc
         with
           Not_found -> DAbs(aux t ((s, 0)::(increment acc)))
       end
  in

  aux term [];;

let () =
    let t = Abs ("x", Abs ("y", App (App (Var "x", Abs ("z", Var "x")), Abs ("x", App (Var "x", Var "y"))))) in
    let t' = DAbs (DAbs (DApp (DApp (DVar 1, DAbs (DVar 2)), DAbs (DApp (DVar 0, DVar 1))))) in
    assert (db_of_term t = t');;

(**3.2 Lifting*)

(*I prefered to use the next function which lift of n all free variables*)
let lift (n:int) (term:db) : db =
  let rec aux (n:int) (term:db) (depth:int) : db = match term with
    |DVar dvar when dvar > depth -> if (dvar < n) then DVar dvar else DVar (dvar + 1)
    |DApp (t1, t2) -> DApp (aux n t1 depth, aux n t2 depth)
    |DAbs (t) -> DAbs (aux n t (depth + 1))
    |_ -> term
  in
  aux n term (-1);;

let n_lift (n:int) (term:db) : db =
  let rec aux (n:int) (term:db) (depth:int) : db = match term with
    |DVar dvar when dvar > depth -> DVar (dvar + n)
    |DApp (t1, t2) -> DApp (aux n t1 depth, aux n t2 depth)
    |DAbs (t) -> DAbs (aux n t (depth + 1))
    |_ -> term
  in
  aux n term (-1);;

let () =
  let t = lift 0 (DAbs (DApp (DVar 0, DVar 1))) in
  let t' = DAbs (DApp (DVar 0, DVar 2)) in
  assert (t = t');;

(**3.3 Unlifting*)

let unlift (n:int) (dvar:dvar) : dvar = if dvar > n then dvar - 1 else dvar;;

let () =
  assert (unlift 5 1 = 1);
  assert (unlift 5 4 = 4);
  assert (unlift 5 6 = 5);
  assert (unlift 5 9 = 8);;

(**3.4 Substitution*)

(*As substitution is only used to do a β-reduction step : (λx.t)u → t[u/x] the name of the variable is not relevant.
It is in the auxiliary function because a same variable can be called by different integer depending on its depth in the term.
But here it is "dangerous" to give access to this in the function dsub, so I hidden it into the auxiliary function.*)
let dsub (u:db) (term:db) : db =
  let rec aux (n:dvar) (u:db) (term:db) : db = match term with
    | DVar x when x = n -> n_lift n u
    | DVar x -> DVar (unlift n x)
    | DAbs t -> DAbs (aux (n + 1) u t)
    | DApp (t1, t2) -> DApp (aux n u t1, aux n u t2)
  in
  aux 0 u term;;

let t = DAbs(DApp(DApp(DVar 1, DAbs(DVar 2)), DAbs(DApp(DVar 0,DVar 1)))) ;;
let u = DAbs(DVar 1);;
let test_dsub = dsub u t;;
(*this correspond to the application of λ.λ.1(λ.2)(λ.01) to λ.1*)

(**3.5 Reduction*)

let rec dred (term:db) : db option = match term with
  | DVar _-> None
  | DApp (DAbs (t), u) -> Some (dsub u t)
  | DApp (t1, t2) ->
     begin
       let red_t1 = dred t1 in
       let red_t2 = dred t2 in
       match (red_t1, red_t2) with
       | (Some (t1'), _) -> Some (DApp (t1', t2))
       | (_, Some (t2')) -> Some (DApp (t1, t2'))
       | _ -> None
     end 
  | DAbs (t) ->
     begin
       let red_t = dred t in
       match red_t with
       | Some (t') -> Some (DAbs (t'))
       | _ -> None
     end;;

let rec dnormalize (term:db) = match dred term with
  | Some (t) -> dnormalize t
  | None -> term;;

let test_dnormalize =
  let t1 = apps [add; nat 6; nat 5] in
  let t2 = nat 11 in
  let u1 = db_of_term(t1) in
  let u2 = db_of_term(t2) in
  let n1 = dnormalize u1 in
  let n2 = dnormalize u2 in
  n1 = n2;;

let test_factorial_db =
  let t = db_of_term (apps [factorial; nat 4]) in
  let u = db_of_term (nat 24) in
  dnormalize t = dnormalize u;;
