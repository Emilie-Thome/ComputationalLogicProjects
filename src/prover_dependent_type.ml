
(** 5 Dependent types. *)
(** 5.1 Expressions. *)
type var = string;;
type expr =
  | Type
  | Var of var
  | App of expr * expr
  | Abs of var * expr * expr
  | Pi of var * expr * expr
  | Nat
  | Z
  | S of expr
  | Ind of expr * expr * expr * expr
  | Eq of expr * expr
  | Refl of expr
  | J of expr * expr * expr * expr * expr;;

(** 5.2 String representation. *)
let rec to_string (expr:expr) : string = match expr with
  | Type -> "Type"
  | Var var -> var
  | App (exprl, exprr) -> "(" ^ (to_string exprl) ^ " " ^ (to_string exprr) ^ ")"
  | Abs (var, exprl, exprr) -> "(fun (" ^ var ^ " : " ^ (to_string exprl) ^ ") -> " ^ (to_string exprr) ^ ")"
  | Pi (var, exprl, exprr) -> "(Pi (" ^ var ^ " , " ^ (to_string exprl) ^ ") -> " ^ (to_string exprr) ^ ")"
  | Nat -> "Nat"
  | Z -> "Z"
  | S n -> "S(" ^ (to_string n) ^ ")"
  | Ind (p, z, s, n) -> "(Ind (" ^ (to_string p) ^ " , " ^ (to_string z) ^ " , " ^ (to_string s) ^ " , " ^ (to_string n) ^ "))"
  | Eq (t, u) -> "(Eq " ^ (to_string t) ^ " " ^ (to_string u) ^ ")"
  | Refl t -> "(Refl " ^ (to_string t) ^ ")"
  | J (p, r, x, y, e) -> "(J " ^ (to_string p) ^ " " ^ (to_string r) ^ " " ^ (to_string x) ^ " " ^ (to_string y) ^ " " ^ (to_string e) ^ ")";;

(** 5.3 Fresh variable names. *)
let n = ref 0;;
let fresh () = let new_var = "x" ^ (string_of_int !n) in n := !n + 1; new_var;;

(** 5.4 Substitution. *)
let rec has_fv (x:var) (t:expr) : bool = match t with
  | Var v when v = x -> true
  | App (tl, tr) -> (has_fv x tl) || (has_fv x tr)
  | Abs (s, a, t') -> (has_fv x a) || ((s <> x) && (has_fv x t'))
  | Pi (s, a, b) -> (has_fv x a) || ((s <> x) && (has_fv x b))
  | S n -> has_fv x n
  | Ind (p, z, s, n) ->  (has_fv x p) || (has_fv x z) || (has_fv x s) || (has_fv x n)
  | Eq (t, v) -> (has_fv x t) || (has_fv x v)
  | Refl t -> (has_fv x t)
  | J (p, r, t, y, e) -> (has_fv x p) || (has_fv x r) || (has_fv x t) || (has_fv x y) || (has_fv x e)
  | _ -> false;;

let rec sub (x:var) (u:expr) (expr:expr) : expr = match expr with
  | Var v when v = x -> u
  | App (tl, tr) -> App (sub x u tl, sub x u tr)
  | Abs (s, a, t') when s = x -> let new_s = fresh () in
                                 let new_t = sub s (Var new_s) t' in
                                 Abs (new_s, sub x u a, new_t)
  | Abs (s, a, t') when has_fv s u ->  let new_s = fresh () in
                                       let new_t = sub s (Var new_s) t' in
                                       Abs (new_s, sub x u a, sub x u new_t)
  | Abs (s, a, t') -> Abs (s, sub x u a, sub x u t')
  | Pi (y, a, b) when y = x -> let new_y = fresh () in
                               let new_b = sub y (Var new_y) b in
                               Pi (new_y, sub x u a, new_b)
  | Pi (y, a, b) when has_fv y u ->  let new_y = fresh () in
                                     let new_b = sub y (Var new_y) b in
                                     Pi (new_y, sub x u a, sub x u new_b)
  | Pi (y, a, b) -> Pi (y, sub x u a, sub x u b)
  | S n -> S (sub x u n)
  | Ind (p, z, s, n) ->  Ind (sub x u p, sub x u z, sub x u s, sub x u n)
  | Eq (t, v) -> Eq (sub x u t, sub x u v)
  | Refl t -> Refl (sub x u t)
  | J (p, r, t, y, e) -> J (sub x u p, sub x u r, sub x u t, sub x u y, sub x u e)
  | _ -> expr;;

(** 5.5 Contexts. *)
type context = (var * (expr * expr option)) list;;

let rec string_of_context (context:context) : string = match context with
  | [] -> ""
  | (var, (expr_ty, None))::q -> (string_of_context q) ^ var ^ " : " ^ (to_string expr_ty) ^ "\n" 
  | (var, (expr_ty, Some expr))::q -> (string_of_context q) ^ var ^ " : " ^ (to_string expr_ty) ^ " = " ^ (to_string expr) ^ "\n";;

(** 5.6 Normalization. *)

(*used to associate variables with their type*)
exception Not_found
let rec assoc x l = match l with
  |[] -> raise Not_found
  |(a, b)::_ when a = x -> b
  |_::t -> assoc x t;;

let rec in_context (x:var) (context:context) : bool = match context with
  | (var, _)::q -> (in_context x q) || (x = var)
  | _ -> false;;

let rec normalize (context:context) (expr:expr) : expr =
   match expr with
  | Var var -> begin try let tuple = assoc var context in
                         match tuple with
                         | (_, Some expr') -> normalize context expr'
                         | _ -> Var var
                     with
                       Not_found -> Var var
               end
  | App (Abs (s, a, t), u)
       when in_context s context -> let new_s = fresh () in
                                    let new_t = sub s (Var new_s) t in
                                    let norm_a = normalize context a in
                                    let norm_u = normalize context u in
                                    normalize ((new_s, (norm_a, Some norm_u))::context) new_t
  | App (Abs (s, a, t), u) ->  let norm_a = normalize context a in
                               let norm_u = normalize context u in
                               normalize ((s, (norm_a, Some norm_u))::context) t
  | App (tl, tr) -> begin let norm_tl = normalize context tl in
                    let norm_tr = normalize context tr in
                    match norm_tl with
                    | Abs(_, _, _) -> normalize context (App (norm_tl, norm_tr))
                    | _ -> App (norm_tl, norm_tr)
                    end
  | Abs (s, a, t)
       when in_context s context -> let new_s = fresh () in
                                    let new_t = sub s (Var new_s) t in
                                    let norm_a = normalize context a in
                                    let norm_t = normalize ((new_s, (norm_a, None))::context) new_t in
                                    Abs (new_s, norm_a, norm_t)
  | Abs (s, a, t) -> let norm_a = normalize context a in
                     let norm_t = normalize ((s, (norm_a, None))::context) t in
                     Abs (s, norm_a, norm_t)
  | Pi (s, a, b)
       when in_context s context -> let new_s = fresh () in
                                    let new_b = sub s (Var new_s) b in
                                    let norm_a = normalize context a in
                                    let norm_b = normalize ((new_s, (norm_a, None))::context) new_b in
                                    Pi (new_s, norm_a, norm_b)
  | Pi (s, a, b) -> let norm_a = normalize context a in
                    let norm_b = normalize ((s, (norm_a, None))::context) b in
                    Pi (s, norm_a, norm_b)
  | S n -> S (normalize context n)
  | Ind (p, z ,s ,n) -> begin let norm_p = normalize context p in
                         let norm_z = normalize context z in
                         let norm_s = normalize context s in
                         let norm_n = normalize context n in
                              match norm_n with
                              | Z -> normalize context z
                              | S n' -> normalize context (App (App (s, n'), Ind (p, z, s, n')))
                              | _ -> Ind (norm_p, norm_z, norm_s, norm_n)
                        end
  | Eq (t, u) -> Eq (normalize context t, normalize context u)
  | Refl t -> Refl (normalize context t)
  | J (p, r, x, y, e) -> let norm_p = normalize context p in
                         let norm_r = normalize context r in
                         let norm_x = normalize context x in
                         let norm_y = normalize context y in
                         let norm_e = normalize context e in
                         if (norm_x = norm_y) && (norm_e = (Refl norm_x))
                         then normalize context (App (norm_r, norm_x))
                         else J (norm_p, norm_r, norm_x, norm_y, norm_e)
  | _ -> expr
       
;;

(** 5.7 α-conversion. *)
let rec alpha (expr1:expr) (expr2:expr) : bool = match (expr1, expr2) with
  | (expr1, expr2) when expr1 = expr2 -> true
  | (App (t1, t1'), App (t2, t2')) -> (alpha t1 t2) && (alpha t1' t2')
  | (Abs (s1, a1, t1), Abs(s2, a2, t2)) when s1 = s2 -> (alpha a1 a2) && (alpha t1 t2)
  | (Abs (s1, a1, t1), Abs(s2, a2, t2)) -> (alpha a1 a2) && (alpha t1 (sub s2 (Var s1) t2))
  | (Pi (s1, a1, b1), Pi (s2, a2, b2)) when s1 = s2 -> (alpha a1 a2) && (alpha b1 b2)
  | (Pi (s1, a1, b1), Pi (s2, a2, b2)) -> (alpha a1 a2) && (alpha b1 (sub s2 (Var s1) b2))
  | (S n1, S n2) -> alpha n1 n2
  | (Ind (p1, z1, s1, n1), Ind (p2, z2, s2, n2)) -> (alpha p1 p2) && (alpha z1 z2) && (alpha s1 s2) && (alpha n1 n2)
  | (Eq (t1, u1), Eq (t2, u2)) -> (alpha t1 t2) && (alpha u1 u2)
  | (Refl t1, Refl t2) -> (alpha t1 t2)
  | (J (p1, r1, x1, y1, e1), J (p2, r2, x2, y2, e2)) -> (alpha p1 p2) && (alpha r1 r2) && (alpha x1 x2) && (alpha y1 y2) && (alpha e1 e2)
  | _ -> false;;

(** 5.8 Conversion. *)
let conv (context:context) (expr1:expr) (expr2:expr) : bool = alpha (normalize context expr1) (normalize context expr2);;

(** 5.9 Type inference. *)
exception Type_error;;
let rec infer (context:context) (expr:expr) : expr = 
  match normalize context expr with
  | Type -> Type
  | Var var -> begin try let tuple = assoc var context in
                         match tuple with
                         | (a, _) -> a
                     with
                       Not_found -> Type (* We don't know if it is a type or a term variable. *)
               end
  | App (t1, t2) -> begin
                      let infer_t1 = infer context t1 in
                      let type2 = infer context t2 in
                      match infer_t1 with
                      | Pi (s, type1, type1') when conv context type1 type2 -> type1'
                      | _ -> (print_endline("here App") ; raise Type_error)
                    end
  | Abs (s, a, t)
       when in_context s context -> let new_s = fresh () in
                                    let new_t = sub s (Var new_s) t in
                                    let infer_new_t = infer ((new_s,(a, None))::context) new_t in
                                    Pi (new_s, a, infer_new_t) 
  | Abs (s, a, t) -> let infer_t = infer ((s,(a, None))::context) t in 
                     Pi (s, a, infer_t)
  | Pi (_, _, _) -> Type
  | Nat -> Type
  | Z -> Nat
  | S n -> if (infer context n) = Nat then Nat else (print_endline("here S") ; raise Type_error)
  | Ind (p, z, s, n) -> let infer_p = infer context p in
                        let infer_z = infer context z in
                        let infer_s = infer context s in
                        let infer_n = infer context n in
                        let n_infer = fresh () in 
                        let m_infer = fresh () in 
                        let b_p = conv context infer_p (Pi (n_infer, Nat, Type)) in
                        let b_z = conv context infer_z (App (p, Z)) in
                        let b_s = conv context infer_s (Pi (n_infer, Nat, Pi (m_infer,
                                                        App (p, Var n_infer),
                                                        App (p, S (Var n_infer)))))
                        in
                        let b_n = conv context infer_n Nat in
                        if b_p && b_z && b_s && b_n
                        then 
                        normalize context (App(p, n))
                        else (print_endline("here Ind") ; raise Type_error)
  | Eq (t, u) -> Type
  | Refl t -> Eq (t, t)
  | J (p, r, x, y, e) -> let infer_p = infer context p in
                         let infer_r = infer context r in
                         let infer_x = infer context x in
                         let infer_y = infer context y in
                         let infer_e = infer context e in
                         let x_infer = fresh () in
                         let y_infer = fresh () in
                         let b_p = conv context infer_p (Pi (x_infer, infer_x, Pi (y_infer, infer_y, Pi ("_", Eq (Var x_infer, Var y_infer), Type)))) in
                         let b_r = conv context infer_r (Pi (x_infer, infer_x, App (App (App (p, Var x_infer), Var x_infer), (Refl (Var x_infer))))) in
                         let b_e = conv context infer_e (Eq (x, y)) in
                         if b_p && b_r && b_e && (conv context infer_x infer_y)
                         then normalize context (App (App (App (p, x), y), e))
                         else (print_endline("here J") ; raise Type_error)
  | _ -> raise Type_error;;

(** 5.10 Type checking. *)
let check (context:context) (term:expr) (ty:expr) = let infer_t = infer context term in
                                                    if not (conv context infer_t ty)
                                                    then raise Type_error
                                                    else ();;

(** 5.11 Interaction loop. *)
(** Parsing of expressions. *)
let () = Printexc.record_backtrace true;;
exception Parse_error;;
let lexer = Genlex.make_lexer ["("; ","; ")"; "->"; "=>"; "fun"; "Pi"; ":"; "Type"; "Nat"; "Z"; "S"; "Ind"; "Eq"; "Refl"; "J"];;
let of_tk s =
  let must_kwd s k = match Stream.next s with Genlex.Kwd k' when k' = k -> () | _ -> raise Parse_error in
  let peek_kwd s k = match Stream.peek s with Some (Genlex.Kwd k') when k' = k -> let _ = Stream.next s in true | _ -> false in
  let stream_is_empty s = try Stream.empty s; true with Stream.Failure -> false in
  let ident s = match Stream.next s with Genlex.Ident x -> x | _ -> raise Parse_error in
  let noapp = List.map (fun k -> Some (Genlex.Kwd k)) [")"; "->"; "=>"; "fun"; "Pi"; ":"; "Type"; "Ind"] in
  let rec e () = abs ()
  and abs () =
    if peek_kwd s "Pi" then
      (
        must_kwd s "(";
        let x = ident s in
        must_kwd s ":";
        let a = e () in
        must_kwd s ")";
        must_kwd s "->";
        let b = e () in
        Pi (x, a, b)
      )
    else if peek_kwd s "fun" then
      (
        must_kwd s "(";
        let x = ident s in
        must_kwd s ":";
        let a = e () in
        must_kwd s ")";
        must_kwd s "->";
        let t = e () in
        Abs (x, a, t)
      )
    else
      ind ()
  and ind () = 
    if peek_kwd s "Ind" then 
       (
        must_kwd s "(";
        let p = base () in
        must_kwd s ",";
        let z = base () in
        must_kwd s ",";
        let ps = base () in
        must_kwd s ",";
        let n = base () in
        must_kwd s ")";
        Ind (p, z, ps, n)    
       )
    else
      j ()
  and j () =
    if peek_kwd s "J" then
       (
        let p = base () in
        let r = base () in
        let x = base () in
        let y = base () in
        let e = base () in
        J (p, r, x, y, e)
       )
    else
      eq ()
  and eq () =
    if peek_kwd s "Eq" then
      (
       let t = base () in
       let u = base () in
       Eq (t, u)
      )
    else
      refl ()
  and refl () =
    if peek_kwd s "Refl" then
      (
       let t = base () in
       Refl t
      )
    else
      app ()
  and app () =
    let t = ref (arr ()) in
    while not (stream_is_empty s) && not (List.mem (Stream.peek s) noapp) do
      t := App (!t, base ())
    done;
    !t
  and arr () =
    let t = base () in
    if peek_kwd s "=>" then
      let u = e () in
      Pi ("_", t, u)
    else
      t
  and base () =
    match Stream.next s with
    | Genlex.Ident x -> Var x
    | Genlex.Kwd "Type" -> Type
    | Genlex.Kwd "Nat" -> Nat
    | Genlex.Kwd "Z" -> Z
    | Genlex.Kwd "S" ->
       let t = base () in
       S t
    | Genlex.Kwd "Ind" ->
       let p = base () in
       let z = base () in
       let ps = base () in
       let n = base () in
       Ind (p, z, ps, n)
    | Genlex.Kwd "Eq" ->
       let t = base () in
       let u = base () in
       Eq (t, u)
    | Genlex.Kwd "Refl" ->
       let t = base () in
       Refl t
    | Genlex.Kwd "J" ->
       let p = base () in
       let r = base () in
       let x = base () in
       let y = base () in
       let e = base () in
       J (p, r, x, y, e)
    | Genlex.Kwd "(" ->
       let t = e () in
       must_kwd s ")";
       t
    | _ -> raise Parse_error
  in
  e ();;
let of_string a = of_tk (lexer (Stream.of_string a));;


let pred = Abs ("n", Nat, Ind (Abs ("z", Nat, Nat), Z, Abs ("x", Nat, Abs ("y", Nat, Var "x")), Var "n"));;

let add = Abs ("n", Nat, Abs ("m", Nat, Ind (Abs ("z", Nat, Nat), Var "m", Abs ("x", Nat, Abs ("y", Nat, S (Var "y"))), Var "n")));;

let seq = 
let p = Abs ("x", Nat, Abs ("y", Nat, Abs ("e", Eq (Var "x", Var "y"), Eq (S (Var "x"), S (Var "y"))))) in
let r = Abs ("x", Nat, Refl (S(Var "x"))) in
let j = J (p, r, Var "x", Var "y", Var "e") in
Abs ("x", Nat, Abs ("y", Nat, Abs ("e", Eq (Var "x", Var "y"), j)));;

let zadd = Abs ("n", Nat, Refl (Var "n"));;

let addz = let p = Abs ("x", Nat, Abs ("y", Nat, Abs ("e", Eq (Var "x", Var "y"), Eq (App (App (add, Var "x"), Z), Var "y")))) in
let s = Abs ("n", Nat, Abs ("e", Eq (App (App (add, Var "n"), Z), Var "n"), App (App (App (seq, (App (App (add, Var "n"), Z))), (Var "n")), (Var "e")))) in
let i = Ind (Abs ("x", Nat, Eq (App (App (add, Var "x"), Z), Var "x")), Refl Z, s, Var "x") in
let r = Abs ("x", Nat, i) in
let j = J (p, r, Var "n", Var "n", Refl (Var "n")) in
Abs ("n", Nat, j);;

let sym = 
let p = Abs ("x", Nat, Abs ("y", Nat, Abs ("e", Eq (Var "x", Var "y"), Eq (Var "y", Var "x")))) in
let r = Abs ("x", Nat, Refl (Var "x")) in
let j = J (p, r, Var "x", Var "y", Var "e") in
Abs ("x", Nat, Abs ("y", Nat, Abs ("e", Eq (Var "x", Var "y"), j)));;

let trans = 
let p = Abs ("x", Nat, Abs ("y", Nat, Abs ("e1", Eq (Var "x", Var "y"), Pi("e2", Eq (Var "y", Var "z"), Eq (Var "x", Var "z"))))) in
let r = Abs ("x", Nat, Abs("e2", Eq (Var "x", Var "z"), Var "e2")) in
let j = J (p, r, Var "x", Var "y", Var "e1") in
Abs ("x", Nat, Abs ("y", Nat, Abs ("z", Nat, Abs ("e1", Eq (Var "x", Var "y"), Abs ("e2", Eq (Var "y", Var "z"), App(j, Var "e2"))))));;

let cong =
let p = Abs ("x", Nat, Abs ("y", Nat, Abs ("e1", Eq (Var "x", Var "y"), Eq (App(Var "f", Var "x"), App(Var "f", Var "y"))))) in
let r = Abs ("x", Nat, Refl(App(Var "f", Var "x"))) in
let j = J (p, r, Var "x", Var "y", Var "e") in
Abs ("x", Nat, Abs ("y", Nat, Abs ("e", Eq (Var "x", Var "y"), Abs("f", Pi("n", Nat, Nat), j))));;


let ass_add = 
let xaplusb_c = App ( App (add, App (App (add, Var "xa"), Var "b")), Var "c") in
let ya_bplusc = App ( App (add, Var "ya"), App (App (add, Var "b"), Var "c")) in
let p = Abs ("xa", Nat, Abs ("ya", Nat, Abs ("e", Eq (Var "xa", Var "ya"), Eq (xaplusb_c, ya_bplusc)))) in
let xplusb_c = App ( App (add, App (App (add, Var "x"), Var "b")), Var "c") in
let x_bplusc = App ( App (add, Var "x"), App (App (add, Var "b"), Var "c")) in
let s = Abs (
  "n",
  Nat, 
  Abs (
    "e1", 
    Eq (
      App ( App (add, App (App (add, Var "n"), Var "b")), Var "c"),
      App ( App (add, Var "n"), App (App (add, Var "b"), Var "c"))),
    App (App (App (seq, App ( App (add, App (App (add, Var "n"), Var "b")), Var "c")), App ( App (add, Var "n"), App (App (add, Var "b"), Var "c"))), (Var "e1")))) in
let i = Ind (
  Abs ("x", Nat, Eq (xplusb_c, x_bplusc)),
  App(
    App(
      App(
        App(
          cong,
          App(App(add, Z), Var "b")),
        Var "b"),
      App(zadd, Var "b")),
    Abs("cong", Nat, App(App(add, Var "cong"), Var "c"))),
  s,
  Var "ya") in
let r = Abs ("ya", Nat, i) in
let j = J (p, r, Var "a", Var "a", Refl (Var "a")) in
Abs ("a", Nat, Abs ("b", Nat, Abs ("c", Nat, j)));;

let com_1 = let p = Abs ("x", Nat, Abs ("y", Nat, Abs ("e", Eq (Var "x", Var "y"), Eq (App (App (add, S(Z)), Var "x"), App (App (add, Var "x"), S(Z)))))) in
let s = Abs ("n", Nat, Abs ("e", Eq (App (App (add, S(Z)), Var "n"), App (App (add, Var "n"), S(Z))), App (App (App (seq, App (App (add, S(Z)), Var "n")), App (App (add, Var "n"), S(Z))), (Var "e")))) in
let i = Ind (
  Abs ("x", Nat, Eq (App (App (add, S(Z)), Var "x"), App (App (add, Var "x"), S(Z)))), 
  Refl (S(Z)), 
  s, 
  Var "x") in
let r = Abs ("x", Nat, i) in
let j = J (p, r, Var "n", Var "n", Refl (Var "n")) in
Abs ("n", Nat, j);;


let com_add =
let p = Abs ("xa", Nat, Abs ("ya", Nat, Abs ("e", Eq (Var "xa", Var "ya"), Eq (App(App(add, Var "xa"), Var "b"), App(App(add, Var "b"), Var "ya"))))) in
let s = Abs (
  "n",
  Nat, 
  Abs (
    "e1", 
    Eq (
      App ( App (add, Var "n"), Var "b"),
      App ( App (add, Var "b"), Var "n")),
    (*trans: 1+a+b=b+(1+a)*)
    App(App(App(App(App(trans, S(App(App(add, Var "n"), Var "b"))), App(App(add, App(App(add, Var "b"), S(Z))), Var "n")), App(App(add, Var "b"), S(Var "n"))),
      (*trans: 1+a+b=b+1+a*)
      App(App(App(App(App(trans, S(App(App(add, Var "n"), Var "b"))), S(App( App(add, Var "b"), Var "n"))), App(App(add, App(App(add, Var "b"), S(Z))), Var "n")),
        (*seq: 1+a+b=1+b+a*)
        App (App (App (seq, App(App(add, Var "n"), Var "b")), App( App(add, Var "b"), Var "n")), (Var "e1")) (*S(a+b) = S(b+a)*)),
      (*cong: 1+b+a=b+1+a*)
      App(
        App(
          App(
            App(
              cong,
              S(Var "b")), (* 1+b *)
            App(App(add, Var "b"), S(Z))), (*b+1*)
          App(com_1, Var "b")),  (* 1+b=b+1 *)
        Abs("n'", Nat, App(App(add, Var "n'"), Var "n"))))), (* Pi (n':Nat) -> n'+n *)
    (*ass_add: b+1+a=b+(1+a)*)
    App(App(App(ass_add, Var "b"), S(Z)), Var "n")))) in
let i = Ind (
  Abs ("x", Nat, Eq (App(App(add, Var "x"), Var "b"), App(App(add, Var "b"), Var "x"))),
  App(App(App(sym, App(App(add, Var "b"), Z)), Var "b"), App(addz, Var "b")),
  s,
  Var "a'") in
let r = Abs ("a'", Nat, i) in
let j = J (p, r, Var "a", Var "a", Refl (Var "a")) in
Abs("a", Nat, Abs("b", Nat, j));;


let mult = Abs ("n", Nat, Abs ("m", Nat, Ind (Abs ("z", Nat, Nat), Z, Abs ("x", Nat, Abs ("y", Nat, App(App(add, Var "m"), Var "y"))), Var "n")));;

let zmult = Abs ("n", Nat, Refl Z);;

let multz = let p = Abs ("x", Nat, Abs ("y", Nat, Abs ("e", Eq (Var "x", Var "y"), Eq (App (App (mult, Var "x"), Z), Z)))) in
let s = Abs ("n", Nat, Abs ("e", Eq (App (App (mult, Var "n"), Z), Z), Var "e")) in
let i = Ind (Abs ("x", Nat, Eq (App (App (mult, Var "x"), Z), Z)), Refl Z, s, Var "x") in
let r = Abs ("x", Nat, i) in
let j = J (p, r, Var "n", Var "n", Refl (Var "n")) in
Abs ("n", Nat, j);;

let dev_add_mult = 
let xaplusbmultc = App(App(mult, App(App(add, Var "xa"), Var "b")), Var "c") in
let yamultcplusbmultc = App(App(add, App(App(mult, Var "ya"), Var "c")), App(App(mult, Var "b"), Var "c")) in
let p = Abs ("xa", Nat, Abs ("ya", Nat, Abs ("e", Eq (Var "xa", Var "ya"), Eq (xaplusbmultc, yamultcplusbmultc)))) in
let s = Abs (
  "n",
  Nat, 
  Abs (
    "e1", 
    Eq (
      App(App(mult, App(App(add, Var "n"), Var "b")), Var "c"),
      App(App(add, App(App(mult, Var "n"), Var "c")), App(App(mult, Var "b"), Var "c"))),
    (*trans: (1+a+b)*c=((1+a)*c+b*c)*)
    App(
      App(
        App(
          App(
            App(
            trans,
            App(App(mult, App(App(add, S(Var "n")), Var "b")), Var "c")),
          App(App(add, Var "c"), App(App(add, App(App(mult, Var "n"), Var "c")), App(App(mult, Var "b"), Var "c")))),
        App(App(add, App(App(mult, S(Var "n")), Var "c")), App(App(mult, Var "b"), Var "c"))),
      (*cong: (1+a+b)*c=c+(a*c+b*c)*)
      App(
        App(
          App(
            App(
              cong,
              App(App(mult, App(App(add, Var "n"), Var "b")), Var "c")),
            App(App(add, App(App(mult, Var "n"), Var "c")), App(App(mult, Var "b"), Var "c"))),
          Var "e1"),
        Abs("cong", Nat, App(App(add, Var "c"), Var "cong")))),
    (*sym ass_add: c+(a*c+b*c)=((1+a)*c+b*c)*)
    App(
      App(
        App(
          sym,
          App(App(add, App(App(add, Var "c"), App(App(mult, Var "n"), Var "c"))), App(App(mult, Var "b"), Var "c"))),
      App(App(add, Var "c"), App(App(add, App(App(mult, Var "n"), Var "c")), App(App(mult, Var "b"), Var "c")))),
    App(App(App(ass_add, Var "c"), App(App(mult, Var "n"), Var "c")), App(App(mult, Var "b"), Var "c")))))) in
let xplusbmultc = App(App(mult, App(App(add, Var "x"), Var "b")), Var "c") in
let xmultcplusbmultc = App(App(add, App(App(mult, Var "x"), Var "c")), App(App(mult, Var "b"), Var "c")) in
let i = Ind (
  Abs ("x", Nat, Eq (xplusbmultc, xmultcplusbmultc)),
  App(
    App(
      App(
        App(
          cong,
          App(App(add, Z), Var "b")),
        Var "b"),
      Refl(Var "b")),
    Abs("cong", Nat, App(App(mult, Var "cong"), Var "c"))),
  s,
  Var "ya") in
let r = Abs ("ya", Nat, i) in
let j = J (p, r, Var "a", Var "a", Refl (Var "a")) in
Abs ("a", Nat, Abs ("b", Nat, Abs ("c", Nat, j)));;


let ass_mult =  
let xamultb_c = App ( App (mult, App (App (mult, Var "xa"), Var "b")), Var "c") in
let ya_bmultc = App ( App (mult, Var "ya"), App (App (mult, Var "b"), Var "c")) in
let p = Abs ("xa", Nat, Abs ("ya", Nat, Abs ("e", Eq (Var "xa", Var "ya"), Eq (xamultb_c, ya_bmultc)))) in
let xmultb_c = App ( App (mult, App (App (mult, Var "x"), Var "b")), Var "c") in
let x_bmultc = App ( App (mult, Var "x"), App (App (mult, Var "b"), Var "c")) in
let s = Abs (
  "n",
  Nat, 
  Abs (
    "e1", 
    Eq (
      App ( App (mult, App (App (mult, Var "n"), Var "b")), Var "c"),
      App ( App (mult, Var "n"), App (App (mult, Var "b"), Var "c"))),
    (*trans: ((1+a)*b)*c=(1+a)*(b*c)*)
    App(
      App(
        App(
          App(
            App(
            trans,
            App ( App (mult, App (App (mult, S(Var "n")), Var "b")), Var "c")),
          App(App(add, App(App(mult, Var "b"), Var "c")), App(App(mult, App(App(mult, Var "n"), Var "b")), Var "c"))),
        App ( App (mult, S(Var "n")), App (App (mult, Var "b"), Var "c"))),
      (*dev_add_mult: ((1+a)*b)*c=b*c+(a*b)*c*)
      App(
        App(
          App(
          dev_add_mult,
          Var "b"),
        App(App(mult, Var "n"),Var "b")),
      Var "c")),
    (*cong: b*c+(a*b)*c=(1+a)*(b*c)*)
    App(
      App(
        App(
          App(
          cong,
          App ( App (mult, App (App (mult, Var "n"), Var "b")), Var "c")),
        App ( App (mult, Var "n"), App (App (mult, Var "b"), Var "c"))),
      Var "e1"),
      Abs("cong", Nat, App(App(add, App(App(mult, Var "b"), Var "c")), Var "cong")))))) in
let i = Ind (
  Abs ("x", Nat, Eq (xmultb_c, x_bmultc)),
  Refl Z,
  s,
  Var "ya") in
let r = Abs ("ya", Nat, i) in
let j = J (p, r, Var "a", Var "a", Refl (Var "a")) in
Abs ("a", Nat, Abs ("b", Nat, Abs ("c", Nat, j)));;





let dev_mult_add = 
let xamultbplusc = App(App(mult, Var "xa"), App(App(add, Var "b"), Var "c")) in
let yamultbplusyamultc = App(App(add, App(App(mult, Var "ya"), Var "b")), App(App(mult, Var "ya"), Var "c")) in
let p = Abs ("xa", Nat, Abs ("ya", Nat, Abs ("e", Eq (Var "xa", Var "ya"), Eq (xamultbplusc, yamultbplusyamultc)))) in
let s = Abs (
  "n",
  Nat, 
  Abs (
    "e1", 
    Eq (
      App(App(mult, Var "n"), App(App(add, Var "b"), Var "c")),
      App(App(add, App(App(mult, Var "n"), Var "b")), App(App(mult, Var "n"), Var "c"))),
    (*trans: (1+a)*(b+c)=(b+a*b)+(c+a*c)*)
    App(
      App(
        App(
          App(
            App(
            trans,
            App(App(add, App(App(add, Var "b"), Var "c")), App(App(mult, Var "n"), App(App(add, Var "b"), Var "c")))),
          App(App(add, App(App(add, App(App(add, Var "b"), App(App(mult, Var "n"), Var "b"))), Var "c")), App(App(mult, Var "n"), Var "c"))),
        App(App(add, App(App(add, Var "b"), App(App(mult, Var "n"), Var "b"))), App(App(add, Var "c"), App(App(mult, Var "n"), Var "c")))),
      (*trans: (1+a)*(b+c)=((b+a*b)+c)+a*c*)
      App(
        App(
          App(
            App(
              App(
              trans,
              App(App(add, App(App(add, Var "b"), Var "c")), App(App(mult, Var "n"), App(App(add, Var "b"), Var "c")))),
            App(App(add, App(App(add, Var "b"), App(App(add, App(App(mult, Var "n"), Var "b")), Var "c"))), App(App(mult, Var "n"), Var "c"))),
          App(App(add, App(App(add, App(App(add, Var "b"), App(App(mult, Var "n"), Var "b"))), Var "c")), App(App(mult, Var "n"), Var "c"))),
        (*trans: (1+a)*(b+c)=(b+(a*b+c))+a*c*)
        App(
          App(
            App(
              App(
                App(
                trans,
                App(App(add, App(App(add, Var "b"), Var "c")), App(App(mult, Var "n"), App(App(add, Var "b"), Var "c")))),
              App(App(add, App(App(add, Var "b"), App(App(add, Var "c"), App(App(mult, Var "n"), Var "b")))), App(App(mult, Var "n"), Var "c"))),
            App(App(add, App(App(add, Var "b"), App(App(add, App(App(mult, Var "n"), Var "b")), Var "c"))), App(App(mult, Var "n"), Var "c"))),
          (*trans: (1+a)*(b+c)=(b+(c+a*b))+a*c*)
          App(
            App(
              App(
                App(
                  App(
                  trans, 
                  App(App(add, App(App(add, Var "b"), Var "c")), App(App(mult, Var "n"), App(App(add, Var "b"), Var "c")))),
                App(App(add, App(App(add, App(App(add, Var "b"), Var "c")), App(App(mult, Var "n"), Var "b"))), App(App(mult, Var "n"), Var "c"))),
              App(App(add, App(App(add, Var "b"), App(App(add, Var "c"), App(App(mult, Var "n"), Var "b")))), App(App(mult, Var "n"), Var "c"))),
            (*trans: (1+a)*(b+c)=((b+c)+a*b)+a*c*)
            App(
              App(
                App(
                  App(
                    App(
                    trans, 
                    App(App(add, App(App(add, Var "b"), Var "c")), App(App(mult, Var "n"), App(App(add, Var "b"), Var "c")))), 
                  App(App(add, App(App(add, Var "b"), Var "c")),App(App(add, App(App(mult, Var "n"), Var "b")), App(App(mult, Var "n"), Var "c")))), 
                App(App(add, App(App(add, App(App(add, Var "b"), Var "c")), App(App(mult, Var "n"), Var "b"))), App(App(mult, Var "n"), Var "c"))),
              (*cong: (1+a)*(b+c)=(b+c)+(a*b+a*c)*)
              App(
                App(
                  App(
                    App(
                    cong,
                    App(App(mult, Var "n"), App(App(add, Var "b"), Var "c"))),
                  App(App(add, App(App(mult, Var "n"), Var "b")), App(App(mult, Var "n"), Var "c"))),
                Var "e1"),
              Abs("cong", Nat, App(App(add, App(App(add, Var "b"), Var "c")), Var "cong")))), 
            (*sym ass_add: (b+c)+(a*b+a*c)=((b+c)+a*b)+a*c*)
            App(
              App(
                App(
                sym, 
                App(App(add, App(App(add, App(App(add, Var "b"), Var "c")), App(App(mult, Var "n"), Var "b"))), App(App(mult, Var "n"), Var "c"))), 
              App(App(add, App(App(add, Var "b"), Var "c")),App(App(add, App(App(mult, Var "n"), Var "b")), App(App(mult, Var "n"), Var "c")))), 
            App(App(App(ass_add, App(App(add, Var "b"), Var "c")), App(App(mult, Var "n"), Var "b")), App(App(mult, Var "n"), Var "c"))))), 
          (*cong ass_add: ((b+c)+a*b)+a*c=(b+(c+a*b))+a*c*)
          App(
            App(
              App(
                App(
                cong, 
                App(App(add, App(App(add, Var "b"), Var "c")), App(App(mult, Var "n"), Var "b"))), 
              App(App(add, Var "b"), App(App(add, Var "c"), App(App(mult, Var "n"), Var "b")))), 
            App(App(App(ass_add, Var "b"), Var "c"), App(App(mult, Var "n"), Var "b"))), 
          Abs("cong", Nat, App(App(add, Var "cong"), App(App(mult, Var "n"), Var "c")))))),
        (*cong com_add: (b+(c+a*b))+a*c=(b+(a*b+c))+a*c*)
        App(
          App(
            App(
              App(
              cong, 
              App(App(add, Var "c"), App(App(mult, Var "n"), Var "b"))), 
            App(App(add, App(App(mult, Var "n"), Var "b")), Var "c")), 
          App(App(com_add, Var "c"), App(App(mult, Var "n"), Var "b"))), 
        Abs("cong", Nat, App(App(add, App(App(add, Var "b"), Var "cong")), App(App(mult, Var "n"), Var "c")))))),
      (*cong sym ass_add: (b+(a*b+c))+a*c=((b+a*b)+c)+a*c*)
      App(
        App(
          App(
            App(
            cong, 
            App(App(add, Var "b"), App(App(add, App(App(mult, Var "n"), Var "b")), Var "c"))), 
          App(App(add, App(App(add, Var "b"), App(App(mult, Var "n"), Var "b"))), Var "c")), 
        App(
          App(
            App(
            sym, 
            App(App(add, App(App(add, Var "b"), App(App(mult, Var "n"), Var "b"))), Var "c")), 
          App(App(add, Var "b"), App(App(add, App(App(mult, Var "n"), Var "b")), Var "c"))), 
        App(App(App(ass_add, Var "b"), App(App(mult, Var "n"), Var "b")), Var "c"))), 
      Abs("cong", Nat, App(App(add, Var "cong"), App(App(mult, Var "n"), Var "c")))))),
    (*ass_add: ((b+a*b)+c)+a*c=(b+a*b)+(c+a*c)*)
    App(App(App(ass_add, App(App(add, Var "b"), App(App(mult, Var "n"), Var "b"))), Var "c"), App(App(mult, Var "n"), Var "c"))))) in
let xmultbplusc = App(App(mult, Var "x"), App(App(add, Var "b"), Var "c")) in
let xmultbplusyamultc = App(App(add, App(App(mult, Var "x"), Var "b")), App(App(mult, Var "x"), Var "c")) in
let i = Ind (
  Abs ("x", Nat, Eq (xmultbplusc, xmultbplusyamultc)),
  Refl Z,
  s,
  Var "ya") in
let r = Abs ("ya", Nat, i) in
let j = J (p, r, Var "a", Var "a", Refl (Var "a")) in
Abs ("a", Nat, Abs ("b", Nat, Abs ("c", Nat, j)));;

let mult_1 = let p = Abs ("x", Nat, Abs ("y", Nat, Abs ("e", Eq (Var "x", Var "y"), Eq (App (App (mult, Var "x"), S(Z)), Var "y")))) in
let s = Abs ("n", Nat, Abs ("e", Eq (App (App (mult, Var "n"), S(Z)), Var "n"), App(App(App(seq, App(App(mult,Var "n"), S(Z))), Var "n"), Var "e"))) in
let i = Ind (Abs ("x", Nat, Eq (App (App (mult, Var "x"), S(Z)), Var "x")), Refl Z, s, Var "x") in
let r = Abs ("x", Nat, i) in
let j = J (p, r, Var "n", Var "n", Refl (Var "n")) in
Abs ("n", Nat, j);;


let com_mult =
let p = Abs ("xa", Nat, Abs ("ya", Nat, Abs ("e", Eq (Var "xa", Var "ya"), Eq (App(App(mult, Var "xa"), Var "b"), App(App(mult, Var "b"), Var "ya"))))) in
let s = Abs (
  "n",
  Nat, 
  Abs (
    "e1", 
    Eq (
      App ( App (mult, Var "n"), Var "b"),
      App ( App (mult, Var "b"), Var "n")),
    (*trans: (1+a)*b=b*(1+a)*)
    App(
      App(
        App(
          App(
            App(
            trans, 
            App(App(mult, S(Var "n")), Var "b")), 
          App(App(add, App(App(mult, Var "b"), S(Z))), App(App(mult, Var "b"), Var "n"))), 
        App(App(mult, Var "b"), S(Var "n"))), 
      (*trans: (1+a)*b=b*1+b*a*)
      App(
        App(
          App(
            App(
              App(
              trans, 
              App(App(mult, S(Var "n")), Var "b")), 
            App(App(add, Var "b"), App(App(mult, Var "b"), Var "n"))), 
          App(App(add, App(App(mult, Var "b"), S(Z))), App(App(mult, Var "b"), Var "n"))), 
        (*cong: (1+a)*b=b+b*a*)
        App(
          App(
            App(
              App(
              cong, 
              App(App(mult, Var "n"), Var "b")),
            App(App(mult, Var "b"), Var "n")), 
          Var "e1"), 
        Abs("cong", Nat, App(App(add, Var "b"), Var "cong")))), 
      (*cong sym: b+b*a=b*1+b*a*)
      App(
        App(
          App(
            App(
            cong, 
            Var "b"),
          App(App(mult, Var "b"), S(Z))), 
        App(App(App(sym, App(App(mult, Var "b"), S(Z))), Var "b"), App(mult_1, Var "b"))), 
      Abs("cong", Nat, App(App(add, Var "cong"), App(App(mult, Var "b"), Var "n")))))),
    (*sym dev_mult_add: b*1+b*a=b*(1+a)*)
    App(
      App(
        App(
        sym, 
        App(App(mult, Var "b"), S(Var "n"))), 
      App(App(add, App(App(mult, Var "b"), S(Z))), App(App(mult, Var "b"), Var "n"))), 
    App(App(App(dev_mult_add, Var "b"), S(Z)), Var "n"))))) in
let i = Ind (
  Abs ("x", Nat, Eq (App(App(mult, Var "x"), Var "b"), App(App(mult, Var "b"), Var "x"))),
  App(App(App(sym, App(App(mult, Var "b"), Z)), Z), App(multz, Var "b")),
  s,
  Var "a'") in
let r = Abs ("a'", Nat, i) in
let j = J (p, r, Var "a", Var "a", Refl (Var "a")) in
Abs("a", Nat, Abs("b", Nat, j));;




let () =
  let env = ref [
    ("com_mult", (infer [] com_mult, Some com_mult)) ; 
    ("mult_1", (infer [] mult_1, Some mult_1)) ; 
    ("dev_mult_add", (infer [] dev_mult_add, Some dev_mult_add)) ; 
    ("multz", (infer [] multz, Some multz)) ; 
    ("zmult", (infer [] zmult, Some zmult)) ; 
    ("ass_mult", (infer [] ass_mult, Some ass_mult)) ; 
    ("dev_add_mult", (infer [] dev_add_mult, Some dev_add_mult)) ; 
    ("mult", (infer [] mult, Some mult)) ; 
    ("com_add", (infer [] com_add, Some com_add)) ; 
    ("com_1", (infer [] com_1, Some com_1)) ; 
    ("ass_add", (infer [] ass_add, Some ass_add)) ; 
    ("Cong", (infer [] cong, Some cong)) ; 
    ("Sym", (infer [] sym, Some sym)) ; 
    ("Trans", (infer [] trans, Some trans)) ; 
    ("addz", (infer [] addz, Some addz)) ; 
    ("zadd", (infer [] zadd, Some zadd)) ; 
    ("pred", (infer [] pred, Some pred)) ; 
    ("Seq", (infer [] seq, Some seq)) ; 
    ("add", (infer [] add, Some add))] in
  let loop = ref true in
  let file = open_out "proof/k.proof" in
  let split c s =
    try
      let n = String.index s c in
      String.trim (String.sub s 0 n), String.trim (String.sub s (n+1) (String.length s - (n+1)))
    with Not_found -> s, ""
  in
  while !loop do
    try
      print_string "? ";
      flush_all ();
      let cmd, arg =
        let cmd = input_line stdin in
        output_string file (cmd^"\n");
        print_endline cmd;
        split ' ' cmd
      in
      match cmd with
      | "assume" ->
         let x, sa = split ':' arg in
         let a = of_string sa in
         check !env a Type;
         env := (x,(a,None)) :: !env;
         print_endline (x^" assumed of type "^to_string a)
      | "define" ->
         let x, st = split '=' arg in
         let t = of_string st in
         let a = infer !env t in
         env := (x,(a,Some t)) :: !env;
         print_endline (x^" defined to "^to_string t^" of type "^to_string a)
      | "context" ->
         print_endline (string_of_context !env)
      | "type" ->
         let t = of_string arg in
         let a = infer !env t in
         print_endline (to_string t^" is of type "^to_string a)
      | "check" ->
         let t, a = split '=' arg in
         let t = of_string t in
         let a = of_string a in
         check !env t a;
         print_endline "Ok."
      | "eval" ->
         let t = of_string arg in
         let _ = infer !env t in
         print_endline (to_string (normalize !env t))
      | "exit" -> loop := false
      | "" | "#" -> ()
      | cmd -> print_endline ("Unknown command: "^cmd)
    with
    | End_of_file -> loop := false
    | Failure err -> print_endline ("Error: "^err^".")
    | e -> print_endline ("Error: "^Printexc.to_string e)
  done;
  print_endline "Please enter the proof name (k.proof):";
  let a = input_line stdin in
  output_string file (a);
  Sys.rename "proof/k.proof" ("proof/" ^ a);;
  print_endline "Bye.";;
 

