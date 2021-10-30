(** 1 Type inference for a simply typed calculus. *)
(** Type variables. *)
type tvar = string;;

(** Term variables. *)
type var = string;;

(** 1.1 Simple types. *)
type ty =
  |TVar of tvar
  |Imp of ty * ty
  |And of ty * ty
  |Or of ty * ty
  |True
  |False
  |Nat
;;

(** 1.2 λ-term. *)
type tm =
  |Var of var
  |Abs of var * ty * tm
  |App of tm * tm
  |Pair of tm * tm
  |Fst of tm
  |Snd of tm
  |Case of tm * var * tm * var * tm
  |Left of tm * ty
  |Right of ty * tm
  |Unit
  |Absurd of tm * ty
  |Z
  |S of tm
  |Rec of tm * tm * tm
;;

(** 1.3 String representation. *)
let rec string_of_ty (ty:ty) : string = match ty with
  |True -> "T"
  |False -> "_"
  |TVar str -> str
  |Imp (tyl, tyr) -> "(" ^ (string_of_ty tyl) ^ " => " ^ (string_of_ty tyr) ^ ")"
  |And (tyl, tyr) -> "(" ^ (string_of_ty tyl) ^ " /\\ " ^ (string_of_ty tyr) ^ ")"
  |Or (tyl, tyr) -> "(" ^ (string_of_ty tyl) ^ " \\/ " ^ (string_of_ty tyr) ^ ")"
  |Nat -> "Nat"
;;

let rec string_of_tm (tm:tm) : string = match tm with
  |Unit -> "()"
  |Var str -> str
  |Pair (tml, tmr) -> "(" ^ (string_of_tm tml) ^ " , " ^ (string_of_tm tmr) ^ ")"
  |Fst tm' -> "fst(" ^ (string_of_tm tm') ^ ")"
  |Snd tm' -> "snd(" ^ (string_of_tm tm') ^ ")"
  |Case(tm', varl, tml, varr, tmr) -> "(case " ^ (string_of_tm tm') ^ " of " ^ varl ^ " -> " ^ (string_of_tm tml) ^ " | " ^ varr ^ " -> " ^ (string_of_tm tmr) ^ ")"
  |Absurd (tm', ty) -> "absurd(" ^ (string_of_tm tm') ^ "," ^ (string_of_ty ty) ^ ")"
  |Left (tm', ty) -> "left(" ^ (string_of_tm tm') ^ "," ^ (string_of_ty ty) ^ ")"
  |Right (ty, tm') -> "right(" ^ (string_of_ty ty) ^ "," ^ (string_of_tm tm') ^ ")"
  |Abs (var, ty, tm') ->
    "(fun (" ^ var ^ " : " ^ (string_of_ty ty) ^ ") -> " ^ (string_of_tm tm') ^ ")"
  |App (tml, tmr) -> "(" ^ (string_of_tm tml) ^ " " ^ (string_of_tm tmr) ^ ")"
  |Z -> "Z"
  |S (tm') -> "S(" ^ (string_of_tm tm') ^ ")"
  |Rec (n, z, s) -> "rec(" ^ (string_of_tm n) ^ " , " ^ (string_of_tm z) ^ " , "  ^ (string_of_tm s) ^ ")";;

(** 1.4 Type inference. *)
type context = (var * ty) list;;

exception Type_error;;

(*used to associate variables with their type*)
exception Not_found
let rec assoc x l = match l with
  |[] -> raise Not_found
  |(a, b)::_ when a = x -> b
  |_::t -> assoc x t;;

let rec infer_type (context:context) (tm:tm) : ty = match tm with
  (* axiom *)
  |Var var -> (try assoc var context with Not_found -> raise Type_error)
  (* ⊤I *)
  |Unit -> True
  (* ⊥E *)
  |Absurd (tm', ty) -> (if (infer_type context tm') = False then ty else raise Type_error)
  (* l+I *)
  |Left (tm', ty) -> Or (infer_type context tm', ty)
  (* r+I *)
  |Right (ty, tm') -> Or (ty, infer_type context tm')
  (* +E *)
  |Case (tm', varl, tml, varr, tmr) -> begin match infer_type context tm' with
                                       |Or (a, b) ->
                                         let tyl = infer_type ((varl,a)::context) tml in
                                         let tyr = infer_type ((varr,b)::context) tmr in
                                         if tyl = tyr then tyl else raise Type_error
                                       |_ -> raise Type_error
                                       end
  (* ×I *)
  |Pair (tml, tmr) -> let tyl = infer_type context tml in
                      let tyr = infer_type context tmr in
                      And (tyl, tyr)
  (* l×E *)
  |Fst tm' -> begin match tm' with
              |Pair (tml, _) -> infer_type context tml
              |Var t -> begin try match assoc t context with
                                  |And (tyl, _) -> tyl
                                  | _ -> raise Type_error
                              with Not_found -> raise Type_error
                        end
              |_ -> raise Type_error
              end
  (* r×E *)
  |Snd tm' -> begin match tm' with
              |Pair (_, tmr) -> infer_type context tmr
              |Var t -> begin try match assoc t context with
                                  |And (_, tyr) -> tyr
                                  | _ -> raise Type_error
                              with Not_found -> raise Type_error
                        end
              |_ -> raise Type_error
              end
  (* →I *)
  |Abs (var, ty, tm') -> Imp (ty, infer_type ((var, ty)::context) tm')
  (* →E *)
  |App (tm1, tm2) -> begin
                     let ty1 = infer_type context tm1 in
                     let ty2 = infer_type context tm2 in
                     match ty1 with
                     |Imp (ty1', ty2') when ty1' = ty2 -> ty2'
                     |_ -> raise Type_error
                     end
  (* zeroI *)
  |Z -> Nat
  (* succI *)
  |S (tm') -> if (infer_type context tm') = Nat then Nat else raise Type_error
  (* recE *)
  |Rec (n, z, s) -> let tyn = infer_type context n in 
                    let tyz = infer_type context z in 
                    let tys = infer_type context s in
                    if (tys = Imp (Nat, Imp (tyz, tyz))) && (tyn = Nat) then tyz else raise Type_error;;

(** 1.5 Type checking. *)
let check_type (context:context) (tm:tm) (ty:ty) : bool =
  try
    ty = infer_type context tm
  with
    Type_error -> false;;

(** 1.6 Type inference and checking together. *)
let rec infer_type' (context:context) (tm:tm) : ty = match tm with
  (* axiom *)
  |Var var -> (try assoc var context with Not_found -> raise Type_error)
  (* ⊤I *)
  |Unit -> True
  (* ⊥E *)
  |Absurd (tm', ty) -> (if  (check_type' context tm' False) then ty else raise Type_error)
  (* l+I *)
  |Left (tm', ty) -> Or (infer_type' context tm', ty)
  (* r+I *)
  |Right (ty, tm') -> Or (ty, infer_type' context tm')
  (* +E *)
  |Case (tm', varl, tml, varr, tmr) -> begin match infer_type' context tm' with
                                       |Or (a, b) ->
                                         let tyl = infer_type' ((varl,a)::context) tml in
                                         if (check_type' ((varr,b)::context) tmr tyl)
                                         then tyl
                                         else raise Type_error
                                       |_ -> raise Type_error
                                       end
  (* ×I *)
  |Pair (tml, tmr) -> let tyl = infer_type' context tml in
                      let tyr = infer_type' context tmr in
                      And (tyl, tyr)
  (* l×E *)
  |Fst tm' -> begin match tm' with
              |Pair (tml, _) -> infer_type' context tml
              |Var t -> begin try match assoc t context with
                                  |And (tyl, _) -> tyl
                                  | _ -> raise Type_error
                              with Not_found -> raise Type_error
                        end
              |_ -> raise Type_error
              end
  (* r×E *)
  |Snd tm' -> begin match tm' with
              |Pair (_, tmr) -> infer_type' context tmr
              |Var t -> begin try match assoc t context with
                                  |And (_, tyr) -> tyr
                                  | _ -> raise Type_error
                              with Not_found -> raise Type_error
                        end
              |_ -> raise Type_error
              end
  (* →I *)
  |Abs (var, ty, tm') -> Imp (ty, infer_type' ((var, ty)::context) tm')
  (* →E *)
  |App (tm1, tm2) -> begin
                     let ty1 = infer_type' context tm1 in
                     match ty1 with
                     |Imp (ty1', ty2') when check_type' context tm2 ty1' -> ty2'
                     |_ -> raise Type_error
                     end
  (* zeroI *)
  |Z -> Nat
  (* succI *)
  |S (tm') -> if (check_type' context tm' Nat) then Nat else raise Type_error
  (* recE *)
  |Rec (n, z, s) -> let tyz = infer_type' context z in 
                    if (check_type' context n Nat) && (check_type' context s (Imp (Nat, Imp (tyz, tyz)))) then tyz else raise Type_error

and check_type' (context:context) (tm:tm) (ty:ty) : bool =
  try
    ty = infer_type' context tm
  with
    Type_error -> false;;

(** 1.12 Parsing strings. *)

let () = Printexc.record_backtrace true
exception Parse_error
let must_kwd (s:Genlex.token Stream.t) (k:string) : unit = match Stream.next s with Genlex.Kwd k' when k' = k -> () | _ -> raise Parse_error;;
let peek_kwd (s:Genlex.token Stream.t) (k:string) : bool = match Stream.peek s with Some (Genlex.Kwd k') when k' = k -> let _ = Stream.next s in true | _ -> false;;
let stream_is_empty (s:'a Stream.t) : bool = try Stream.empty s; true with Stream.Failure -> false;;
let ident (s:Genlex.token Stream.t) : var = match Stream.next s with Genlex.Ident x -> x | _ -> raise Parse_error;;
let lexer = Genlex.make_lexer ["("; ")"; "=>"; "/\\"; "\\/"; "fun"; "->"; ","; ":"; "fst"; "snd"; "T"; "left"; "right"; "not"; "case"; "of"; "|"; "absurd"; "_"; "Nat"];;
let ty_of_tk (s:Genlex.token Stream.t) : ty =
  let rec ty () : ty = arr ()
  and arr () : ty =
    let a = prod () in
    if peek_kwd s "=>" then Imp (a, arr ()) else a
  and prod () : ty =
    let a = sum () in
    if peek_kwd s "/\\" then And (a, prod ()) else a
  and sum () : ty =
    let a = base () in
    if peek_kwd s "\\/" then Or (a, sum ()) else a
  and base () : ty =
    match Stream.next s with
    | Genlex.Ident x -> TVar x
    | Genlex.Kwd "(" ->
       let a = ty () in
       must_kwd s ")";
       a
    | Genlex.Kwd "T" -> True
    | Genlex.Kwd "_" -> False
    | Genlex.Kwd "not" ->
       let a = base () in
       Imp (a, False)
    | Genlex.Kwd "Nat" -> Nat
    | _ -> raise Parse_error
  in
  ty ();;
let tm_of_tk (s:Genlex.token Stream.t) : tm =
  let noapp = List.map (fun k -> Some (Genlex.Kwd k)) [")"; ","; "case"; "fun"; "of"; "->"; "|"] in
  let ty () : ty = ty_of_tk s in
  let rec tm () : tm = app ()
  and app () : tm =
    let t = ref (abs ()) in
    while not (stream_is_empty s) && not (List.mem (Stream.peek s) noapp) do
      t := App (!t, abs ())
    done;
    !t
  and abs () : tm =
    if peek_kwd s "fun" then
      (
        must_kwd s "(";
        let x = ident s in
        must_kwd s ":";
        let a = ty () in
        must_kwd s ")";
        must_kwd s "->";
        let t = tm () in
        Abs (x, a, t)
      )
    else if peek_kwd s "case" then
      (
        let t = tm () in
        must_kwd s "of";
        let x = ident s in
        must_kwd s "->";
        let u = tm () in
        must_kwd s "|";
        let y = ident s in
        must_kwd s "->";
        let v = tm () in
        Case (t, x, u, y, v)
      )
    else
      base ()
  and base () : tm =
    match Stream.next s with
    | Genlex.Ident x -> Var x
    | Genlex.Kwd "(" ->
       if peek_kwd s ")" then
         Unit
       else
         let t = tm () in
         if peek_kwd s "," then
           let u = tm () in
           must_kwd s ")";
           Pair (t, u)
         else
           (
             must_kwd s ")";
             t
           )
    | Genlex.Kwd "fst" ->
       must_kwd s "(";
       let t = tm () in
       must_kwd s ")";
       Fst t
    | Genlex.Kwd "snd" ->
       must_kwd s "(";
       let t = tm () in
       must_kwd s ")";
       Snd t
    | Genlex.Kwd "left" ->
       must_kwd s "(";
       let t = tm () in
       must_kwd s ",";
       let b = ty () in
       must_kwd s ")";
       Left (t, b)
    | Genlex.Kwd "right" ->
       must_kwd s "(";
       let a = ty () in
       must_kwd s ",";
       let t = tm () in
       must_kwd s ")";
       Right (a, t)
    | Genlex.Kwd "absurd" ->
       must_kwd s "(";
       let t = tm () in
       must_kwd s ",";
       let a = ty () in
       must_kwd s ")";
       Absurd (t, a)
    | _ -> raise Parse_error
  in
  tm ();;
let ty_of_string a = ty_of_tk (lexer (Stream.of_string a));;
let tm_of_string t = tm_of_tk (lexer (Stream.of_string t));;

let () =
  let l = [
      "A => B";
      "A /\\ B";
      "T";
      "A \\/ B";
      "_";
      "not A"
    ]
  in
  List.iter (fun s -> Printf.printf "the parsing of %S is %s\n%!" s (string_of_ty (ty_of_string s))) l;;

let () =
  let l = [
      "t u";
      "fun (x : A) -> t";
      "(t , u)";
      "fst(t)";
      "snd(t)";
      "()";
      "case t of x -> u | y -> v";
      "left(t,B)";
      "right(A,t)";
      "absurd(t,A)"
    ]
  in
  List.iter (fun s -> Printf.printf "the parsing of %S is %s\n%!" s (string_of_tm (tm_of_string s))) l;;


(** 2 Interactive prover. *)
(** 2.1 String representation of contexts. *)
let string_of_ctx (context:context) : string =
  let f ((var, ty): var * ty) : string = var ^ " : " ^ (string_of_ty ty) in
  String.concat " , " (List.map f context);;
let test_string_of_ctx = string_of_ctx [("x", Imp(TVar "A", TVar "B")) ; ("y", And(TVar "A", TVar "B")) ; ("Z", TVar "T")];;

(** 2.2 Sequents. *)
type sequent = context * ty;;

let string_of_seq ((context, ty):sequent) : string =
  (string_of_ctx context) ^ " |- " ^ string_of_ty ty;;
let test_string_of_seq = string_of_seq ([("x", Imp(TVar "A", TVar "B")) ; ("y", TVar "A")], TVar "B");;

(** 2.3 An interactive prover. *)
let file = open_out "proof/k.proof";;

let rec prove env a =
  print_endline (string_of_seq (env,a));
  print_string "? "; flush_all ();
  let error e = print_endline e; prove env a in
  let cmd, arg =
    let cmd = input_line stdin in
    output_string file (cmd ^ "\n");
    let n = try String.index cmd ' ' with Not_found -> String.length cmd in
    let c = String.sub cmd 0 n in
    let a = String.sub cmd n (String.length cmd - n) in
    let a = String.trim a in
    c, a
  in
  match cmd with
  | "intro" ->
     (
       match a with
       | Imp (a, b) ->
          if arg = "" then error "Please provide an argument for intro." else
            let x = arg in
            let t = prove ((x,a)::env) b in
            Abs (x, a, t)
       | And (a, b) ->
          if arg = "" then let tl = prove env a in
            		    let tr = prove env b in
            		    Pair (tl, tr)
          else error "No argument expected." 
       | True -> Unit
       | Nat -> 
          if arg = "" then Z
          else let t = tm_of_string arg in
               if infer_type env t <> a then error "Not the right type."
               else S(t)
       | _ ->
          error "Don't know how to introduce this."
     )
  | "fst" ->
     (if arg = "" then error "Please provide an argument for fst." else
        let t = tm_of_string arg in
        match infer_type env t with
        | And(a', _) when a' = a -> Fst(t)
        | _ -> error "Not the right type."
     )
  | "snd" ->
     (if arg = "" then error "Please provide an argument for snd." else
        let t = tm_of_string arg in
        match infer_type env t with
        | And(_, b') when b' = a -> Snd(t)
        | _ -> error "Not the right type."
     )
  | "left" ->
     (if arg = "" then match a with
                       | Or(a', b') -> let tl = prove env a' in Left(tl, b')
                       | _ -> error "Not the right type."
      else error "No argument expected."
     )
  | "right" ->
     (if arg = "" then match a with
                       | Or(a', b') -> let tr = prove env b' in Right (a', tr)
                       | _ -> error "Not the right type."
      else error "No argument expected."
     )
  | "elim" -> 
     (
       if arg = "" then error "Please provide an argument for elim." else
         match  assoc arg env with
         | Imp (a', b') when b' = a-> let u = prove env a' in
                                      App (Var arg, u)
         | Or (a', b') -> let t = prove ((arg, a')::env) a in
                          let u = prove ((arg, b')::env) a in
                          Case(Var arg, arg, t, arg, u)
         | False -> Absurd (Var arg, a)
         | Nat -> let rec remove_from_ctx (context:context) (var:var) : context = match context with
                    | [] -> []
                    | (v, _)::q when v = var -> q
                    | h::q -> h::(remove_from_ctx q var)
                  in (* we need to remove n because it is true for any Nat, so to n *)
                  let z = prove (remove_from_ctx env arg) a in 
                  let s = prove (remove_from_ctx env arg) (Imp (Nat, Imp (a, a))) in
                  Rec(Var arg, z, s)
         | _ -> 
            error "Don't know how to eliminate this."
     )
  | "cut" -> 
     (
       if arg = "" then error "Please provide an argument for cut." else
         let ty = ty_of_string arg in
         let t = prove env (Imp (ty, a)) in
         print_endline (string_of_tm t);
         let lemma = prove env ty in
         print_endline (string_of_tm lemma);
         App(t, lemma)
     )
  | "exact" ->
     let t = tm_of_string arg in
     if infer_type env t <> a then error "Not the right type."
     else t
  | cmd -> error ("Unknown command: " ^ cmd);;
         
(** 2.5 Proofs in files. *)
let () =
  print_endline "Please enter the formula to prove:";
  let a = input_line stdin in
  output_string file (a ^ "\n");
  let a = ty_of_string a in
  print_endline "Let's prove it.";
  let t = prove [] a in
  print_endline "done.";
  print_endline "Proof term is";
  print_endline (string_of_tm t);
  print_string  "Typechecking... "; flush_all ();
  assert (infer_type [] t = a);
  print_endline "ok.";
  print_endline "Please enter the proof name (k.proof):";
  let a = input_line stdin in
  output_string file (a);
  Sys.rename "proof/k.proof" ("proof/" ^ a);;
    
(** 4 Optional: small extensions. *)
(** 4.1 Reduction. *)
let rec has_fv (x:var) (t:tm) : bool = match t with
  | Var v when v = x -> true
  | App (tl, tr) -> (has_fv x tl) || (has_fv x tr)
  | Abs (s, _, t') -> (s <> x) && (has_fv x t')
  | Pair (tl, tr) -> (has_fv x tl) || (has_fv x tr)
  | Fst t' -> has_fv x t'
  | Snd t' -> has_fv x t'
  | Case (t', varl, tl, varr, tr) -> (has_fv x t')||((varl <> x) && (has_fv x tl))||((varr <> x) && (has_fv x tr))
  | Left (t', ty) -> has_fv x t'
  | Right (ty, t') -> has_fv x t'
  | Absurd (t', ty) -> has_fv x t'
  | S t' -> has_fv x t'
  | Rec (t1, t2, t3) -> (has_fv x t1) || (has_fv x t2) || (has_fv x t3)
  | _ -> false;;

let n = ref 0;;
let fresh () = let new_var = "x" ^ (string_of_int !n) in n := !n + 1; new_var;;

let rec sub (x:var) (u:tm) (t:tm) : tm = match t with
  | Var v when v = x -> u
  | App (tl, tr) -> App (sub x u tl, sub x u tr)
  | Abs (s, ty, t') when s = x -> let new_s = fresh () in
                              let new_t = sub s (Var new_s) t' in
                              Abs (new_s, ty, new_t)
  | Abs (s, ty, t') when has_fv s u ->  let new_s = fresh () in
                                    let new_t = sub s (Var new_s) t' in
                                    Abs (new_s, ty, sub x u new_t)
  | Abs (s, ty, t') -> Abs (s, ty, sub x u t')
  | Pair (tl, tr) -> Pair (sub x u tl, sub x u tr)
  | Fst t' -> Fst (sub x u t')
  | Snd t' -> Snd (sub x u t')
  | Case (t', varl, tl, varr, tr) when varl = x -> let new_varl = fresh () in
                                                   let new_tl = sub varl (Var new_varl) tl in
                                                   sub x u (Case (t', new_varl, new_tl, varr, tr))
  | Case (t', varl, tl, varr, tr) when varr = x -> let new_varr = fresh () in
                                                   let new_tr = sub varr (Var new_varr) tr in
                                                   sub x u (Case (t', varl, tl, new_varr, new_tr))
  | Case (t', varl, tl, varr, tr) when has_fv varl u -> let new_varl = fresh () in
                                                        let new_tl = sub varl (Var new_varl) tl in
                                                        sub x u (Case (t', new_varl, sub x u new_tl, varr, tr))
  | Case (t', varl, tl, varr, tr) when has_fv varr u -> let new_varr = fresh () in
                                                        let new_tr = sub varr (Var new_varr) tr in
                                                        sub x u (Case (t', varl, tl, new_varr, sub x u new_tr))
  | Case (t', varl, tl, varr, tr) -> Case (sub x u t', varl, tl, varr, tr)
  | Left (t', ty) -> Left (sub x u t', ty)
  | Right (ty, t') -> Right (ty, sub x u t')
  | Absurd (t', ty) -> Absurd (sub x u t', ty)
  | S t' -> S (sub x u t')
  | Rec (t1, t2, t3) -> Rec (sub x u t1, sub x u t2, sub x u t3)
  | _ -> t;;

let rec red (term:tm) : tm option = match term with
  | App (Abs (s, _, t), u) -> Some (sub s u t)
  | App (tl, tr) ->
     begin
       let red_tl = red tl in
       let red_tr = red tr in
       match (red_tl, red_tr) with
       | (Some (tl'), _) -> Some (App (tl', tr))
       | (_, Some (tr')) -> Some (App (tl, tr'))
       | _ -> None
     end 
  | Abs (s, ty, t) ->
      begin
       let red_t = red t in
       match red_t with
       | Some (t') -> Some (Abs (s, ty, t'))
       | _ -> None
      end
  | Pair (tl, tr) -> 
     begin
       let red_tl = red tl in
       let red_tr = red tr in
       match (red_tl, red_tr) with
       | (Some (tl'), _) -> Some (Pair (tl', tr))
       | (_, Some (tr')) -> Some (Pair (tl, tr'))
       | _ -> None
     end 
  | Fst t ->
     begin
       let red_t = red t in
       match red_t with
       | Some (t') -> Some (Fst t')
       | _ -> None
     end 
  | Snd t ->
     begin
       let red_t = red t in
       match red_t with
       | Some (t') -> Some (Snd t')
       | _ -> None
     end 
  | Case (t, varl, tl, varr, tr) -> 
     begin
       let red_t = red t in
       let red_tl = red tl in
       let red_tr = red tr in
       match (red_t, red_tl, red_tr) with
       | (Some (t'), _, _) -> Some (Case (t', varl, tl, varr, tr))
       | (_, Some (tl'), _) -> Some (Case (t, varl, tl', varr, tr))
       | (_, _, Some (tr')) -> Some (Case (t, varl, tl, varr, tr'))
       | _ -> None
     end 
  | Left (t, ty) ->
     begin
       let red_t = red t in
       match red_t with
       | Some (t') -> Some (Left (t', ty))
       | _ -> None
     end 
  | Right (ty, t)->
     begin
       let red_t = red t in
       match red_t with
       | Some (t') -> Some (Right (ty, t'))
       | _ -> None
     end 
  | Absurd (t, ty) ->
     begin
       let red_t = red t in
       match red_t with
       | Some (t') -> Some (Absurd (t', ty))
       | _ -> None
     end 
  | S t ->
     begin
       let red_t = red t in
       match red_t with
       | Some (t') -> Some (S t')
       | _ -> None
     end 
  | Rec (n, z, s) ->
     begin
       let red_n = red n in
       let red_z = red z in
       let red_s = red s in
       match (n, red_n, red_z, red_s) with
       | (Z, _, _, _) -> Some (z)
       | (S (n'), _, _, _) -> Some (App (App (s, n'), Rec (n', z, s)))
       | (_, Some (Z), _, _) -> Some (z)
       | (_, Some (S (n')), _, _) -> Some (App (App (s, n'), Rec (n', z, s)))
       | (_, Some (n'), _, _) -> Some (Rec (n', z, s))
       | (_, _, Some (z'), _) -> Some (Rec (n, z', s))
       | (_, _, _, Some (s')) -> Some (Rec (n, z, s'))
       | _ -> None
     end 
  | _ -> None

;;

let rec normalize (term:tm) : tm = match red term with
  | Some (t) -> normalize t
  | None -> term;;

let rec eq (t1:tm) (t2:tm) : bool = match (t1, t2) with
  | (t1, t2) when t1 = t2 -> true
  | (App (t1, t1'), App (t2, t2')) -> (eq t1 t2) && (eq t1' t2')
  | (Abs (s1, ty1, t1), Abs(s2, ty2, t2)) when s1 = s2 -> (ty1 = ty2) && (eq t1 t2)
  | (Abs (s1, ty1, t1), Abs(s2, ty2, t2)) -> (ty1 = ty2) && (eq t1 (sub s2 (Var s1) t2))
  | (Pair (t1, t1'), Pair (t2, t2')) -> (eq t1 t2) && (eq t1' t2')
  | (Fst t1, Fst t2) -> (eq t1 t2)
  | (Snd t1, Snd t2) -> (eq t1 t2)
  | (Case (t1, varl1, tl1, varr1, tr1),
     Case (t2, varl2, tl2, varr2, tr2))
       when varl1 <> varl2 ->
     eq (Case (t1, varl1, tl1, varr1, tr1)) (Case (t2, varl1, sub varl2 (Var varl1) tl2, varr2, tr2))
  | (Case (t1, varl1, tl1, varr1, tr1),
     Case (t2, varl2, tl2, varr2, tr2))
       when varr1 <> varr2 ->
     eq (Case (t1, varl1, tl1, varr1, tr1)) (Case (t2, varl2, tl2, varr1, sub varr2 (Var varr1) tr2))
  | (Case (t1, varl1, tl1, varr1, tr1),
     Case (t2, varl2, tl2, varr2, tr2)) -> (eq t1 t2) && (eq tl1 tl2) && (eq tr1 tr2)
  | (Left (t1, ty1), Left (t2, ty2)) -> (ty1 = ty2) && (eq t1 t2)
  | (Right (ty1, t1), Right (ty2, t2)) -> (ty1 = ty2) && (eq t1 t2)
  | (Absurd (t1, ty1), Absurd (t2, ty2)) -> (ty1 = ty2) && (eq t1 t2)
  | (S t1, S t2) -> (eq t1 t2)
  | (Rec (t1, tl1, tr1), Rec (t2, tl2, tr2)) -> (eq t1 t2) && (eq tl1 tl2) && (eq tr1 tr2)
  | _ -> false;;

