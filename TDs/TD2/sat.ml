type var = int;;
type formula =
  |Var of var
  |And of formula * formula
  |Or of formula * formula
  |Not of formula
  |True
  |False;;


(* substitute the variable x by the formula b in the formula a *)
let rec subst x b a = match a with
  |Var y when x = y -> b
  |And(a1, a2) -> And(subst x b a1, subst x b a2)
  |Or(a1, a2) -> Or(subst x b a1, subst x b a2)
  |Not(a1) -> Not(subst x b a1)
  |_ -> a;;

let testsubst = subst 5 (And(Var 1, True)) (Or(False, Var 5));;

(* return a free variable of the form, Not_found is raised otherwise *)
exception Not_found
let rec free_var form = match form with
  |Var x -> x
  |And(form1, form2) ->
    begin
      try
        free_var form1
      with
        Not_found -> free_var form2 
    end
  |Or(form1, form2) ->
    begin     
      try
        free_var form1
      with
        Not_found -> free_var form2
    end
  |Not form1 -> free_var form1
  |_ -> raise Not_found;;

let testfree_var = free_var (Or(False, Var 5));;

(* evaluate a form with no free variable, otherwise it raises Not_closed *)
exception Not_closed
let rec eval form = match form with
  |True -> true
  |False -> false
  |And(form1, form2) ->
    begin
      let eval1 = eval form1 in
      let eval2 = eval form2 in
      eval1 && eval2
    end
  |Or(form1, form2) ->
    begin
      let eval1 = eval form1 in
      let eval2 = eval form2 in
      eval1 || eval2
    end
  |Not(form1) ->
    begin
      let eval1 = eval form1 in
      not eval1
    end
  |_ -> raise Not_closed;;

let testeval = eval (And(Not(Or(False, True)), Or(True, False)));;

(* say if a form is satisfiable but naively *)
let rec sat form =
  try
    let x = free_var form in
    (sat (subst x True form)) || (sat (subst x False form))
  with
    Not_found -> eval form;;

let () =
  let x = Var 0 in
  let x'= Not x in
  let y = Var 1 in
  let y'= Not y in
  let a = And (And(Or (x,y), Or (x',y)), Or (x',y')) in
  let b = And (And(Or (x,y), Or (x',y)), And(Or (x,y'), Or (x',y'))) in
  assert (sat a);
  assert (not (sat b));;

(* say is x is a member of the list lst *)
let rec list_mem x lst = match lst with
  |[] -> false
  |y::_ when y = x -> true
  |_::t -> list_mem x t;;

let () =
  assert (list_mem 2 [1;2;3]);
  assert (not (list_mem 5 [1;2;3]));
  assert (not (list_mem 1 []));;

(* map the list with f *)
let rec list_map f lst = match lst with
  |[] -> []
  |h::t -> (f h)::(list_map f t);;

let () =
  assert (list_map (fun x -> 2*x) [1;2;3] = [2;4;6]);
  assert (list_map (fun _ -> ()) [] = []);;

(* filter the list with f *)
let rec list_filter f lst = match lst with
  |[] -> []
  |h::t when (f h) -> h::(list_filter f t)
  |_::t -> list_filter f t;;

let () =
  let even x = x mod 2 = 0 in
  assert (list_filter even [1;2;3;4;6] = [2;4;6]);;


type literal = bool * var;; (* false means negated *)
type clause = literal list;;
type cnf = clause list;;

(* substitute x by top or bottom (true or false) in the cnf form *)
let subst_cnf (x : var) (b : bool) (form_cnf : cnf) : cnf =
  let filter_not_b_x literal = not ((not b, x) = literal) in (* removing (not b, x) from the clauses  *)
  let filter_b_x clause = not (list_mem (b, x) clause) in (* removing the clauses were (b, x) is  *)
  list_map
    (list_filter filter_not_b_x)
    (list_filter filter_b_x form_cnf);; (* after having removed the clauses were (b, x) is, we can remove (not b, x) from all the remaining clauses *)

let test_subst_cnf = 
  let x = true, 0 in
  let x'= false,0 in
  let y = true, 1 in
  let y'= false,1 in
  let a = [[x;y]; [x';y]; [x';y']] in
  subst_cnf 0 true a;;

(* less naive satisfiability detector *)
let rec dpll (form_cnf : cnf) = match form_cnf with
  |[] -> true
  |[]::_ -> false
  |((_,x)::_)::_ -> (dpll (subst_cnf x true form_cnf)) || (dpll (subst_cnf x false form_cnf));;

let () =
  let x = true, 0 in
  let x'= false,0 in
  let y = true, 1 in
  let y'= false,1 in
  let a = [[x;y]; [x';y]; [x';y']] in
  let b = [[x;y]; [x';y]; [x;y']; [x';y']] in
  assert (dpll a);
  assert (not (dpll b));;

(* find an unitary clause and return the literal, otherwise raise Not_found *)
let rec unit (form_cnf : cnf) = match form_cnf with
  |[] -> raise Not_found
  |[b_x]::_ -> b_x
  |_::t -> unit t;;

let () =
  let x = true, 0 in
  let y = true, 1 in
  let y'= false,1 in
  assert (unit [[x;y]; [x]; [y;y']] = x);;

(* find a pure literal in the form, otherwise raise Not_found *)
let pure (form_cnf : cnf) : literal =
  let rec is_x_pure form b x = match form with
    |[] -> true
    |h_clause::t_cns when not (list_mem (not b,x) h_clause) -> is_x_pure t_cns b x
    |_ -> false
  in
    
  let rec find_pure form acc = match form with (* That acc argument is a list of literal x
                                                      wich are not pure. Only x is entered because
                                                      if (b, x) is not pure then (not b, x) either.*)
    |[] -> raise Not_found
    |[]::t_cns -> find_pure t_cns acc
    |((b,x)::t_clause)::t_cns
         when (not (list_mem x acc)) && (is_x_pure (t_clause::t_cns) b x)  (* To begin with  we assure that
                                                                              the literal x has not been tested *)
     -> (b,x) (* It is the first pure x encounter and it is returned.
                 This assures that the acc list contains every unpure x tested *)
    |((_,x)::t_clause)::t_cns -> find_pure (t_clause::t_cns) (x::acc) (* So if x is unpure then
                                                                         it is added to the accumulator *)
  in
  find_pure form_cnf [];; (* And we find a pure x by initialize the accumulator to the empty list *)

let () =
  let x = true, 0 in
  let y = true, 1 in
  let y'= false,1 in
  assert (pure [[x;y]; [x]; [y;y']] = x);;

let test_pure2 =
  let x = true, 0 in
  let x'= false,0 in
  let y = true, 1 in
  let y'= false,1 in
  let z = false,2 in
  pure [[z;x;y']; [z;y';y];[x';y]] ;;

(* the less naive satisfiability test function *)
exception Error_dpll2 (* not supposed to be raised but if it is then there is a problem *)
let rec dpll2 form_cnf =
  if form_cnf = [] then true
  else
    begin
      if list_mem [] form_cnf then false
      else
        begin
          try
            let (b, x) = unit form_cnf in
            dpll2 (subst_cnf x b form_cnf)
          with
            Not_found -> 
            begin
              try
                let (b, x) = pure form_cnf in
                dpll2 (subst_cnf x b form_cnf)
              with
                Not_found ->
                 begin
                   match form_cnf with
                   |((_,x)::_)::_ -> (dpll2 (subst_cnf x true form_cnf))
                                     || (dpll2 (subst_cnf x false form_cnf))
                   |_ -> raise Error_dpll2
                end
            end
        end
    end
;;   
           
let test_dpll2 =
  let x = true, 0 in
  let x'= false,0 in
  let y = true, 1 in
  let y'= false,1 in
  let a = [[x;y]; [x';y]; [x';y']] in
  let b = [[x;y]; [x';y]; [x;y']; [x';y']] in
  assert (dpll2 a);
  not (dpll2 b);;

(** Parse a CNF file. *)
let parse f : cnf =
  let load_file f =
    let ic = open_in f in
    let n = in_channel_length ic in
    let s = Bytes.create n in
    really_input ic s 0 n;
    close_in ic;
    Bytes.to_string s
  in
  let f = load_file f in
  let f = String.map (function '\t' -> ' ' | c -> c) f in
  let f = String.split_on_char '\n' f in
  let f = List.map (String.split_on_char ' ') f in
  let f = List.filter (function "c"::_ | "p"::_ -> false | _ -> true) f in
  let f = List.flatten f in
  let aux (a,c) = function
    | "" -> (a,c)
    | "0" -> (c::a,[])
    | n ->
       let n = int_of_string n in
       let x = if n < 0 then (false,-n) else (true,n) in
       (a,x::c)
  in
  fst (List.fold_left aux ([],[]) f);;

(* let test_parse = dpll2 (parse "ais12.cnf");;  took me 3 minutes approximately to compute so I put it in comment *)

let test_parse' = dpll2 (parse "aim-50-1_6-no-1.cnf");;

let var i j n : var =
  let i = i mod 9 in
  let j = j mod 9 in
  9*(9*i+j)+n;;

(* sudoku encoder *)
let sudoku matrix : cnf =
  let ans_cnf = ref [] in
  
  (* look at each square to see if the condition on the squares is respected *)
  for i_square = 0 to 2 do (* distinct the 3 squares by their position in the sudoku *)
    for j_square = 0 to 2 do
      for i1 = 3 * i_square to 3 * (i_square + 1) - 1 do
        for j1 = 3 * j_square to 3 * (j_square + 1) - 1 do
          for i2 = 3 * i_square to 3 * (i_square + 1) - 1 do
            for j2 = 3 * j_square to 3 * (j_square + 1) - 1 do
              if (i1 != i2) || (j1 != j2) then
                for n = 0 to 8 do
                  ans_cnf := [(false, var i1 j1 n); (false, var i2 j2 n)]::!ans_cnf
                done
            done
          done
        done
      done
    done
  done;
  
  (* loop on lines to see if the condition on them is respected *)
  for line = 0 to 8 do
    for n = 0 to 8 do
      for j1 = 0 to 7 do
        for j2 = j1 + 1 to 8 do
  (* not(a && b) = not(a) || not(b), so I can write it like that to make it a clause *)
          ans_cnf := [(false, var line j1 n);(false, var line j2 n)]::!ans_cnf 
        done
      done
    done
  done;

  (* loop on columns to see if the condition on them is respected *)
  for column = 0 to 8 do
    for n = 0 to 8 do
      for i1 = 0 to 7 do
        for i2 = i1 + 1 to 8 do
  (* not(a && b) = not(a) || not(b), so I can write it like that to make it a clause *)
          ans_cnf := [(false, var i1 column n);(false, var i2 column n)]::!ans_cnf 
        done
      done
    done
  done;

  (* look if it matches with the sudoku *)
  for i = 0 to 8 do
    for j = 0 to 8 do
      if matrix.(i).(j) < 9 then
        ans_cnf := [(true, var i j (matrix.(i).(j)))]::!ans_cnf
    done
  done;
  
  (* look at all cells to see if each cell has at least one digit *)
  for i = 0 to 8 do
    for j = 0 to 8 do
      let clause = ref [] in
      for n = 0 to 8 do
        clause := (true, var i j n)::!clause
      done;
      ans_cnf := !clause::!ans_cnf
    done
  done;
  
  !ans_cnf;;


let simple_sudoku =
  [|[|9;9;7;9;8;2;4;9;9|];
    [|5;4;9;3;9;1;9;9;9|];
    [|9;1;0;9;7;9;2;9;9|];
    [|2;7;9;9;5;9;1;9;8|];
    [|9;6;9;9;9;9;9;0;9|];
    [|0;9;8;9;3;9;9;6;2|];
    [|9;9;4;9;0;9;6;2;9|];
    [|9;9;9;2;9;8;9;1;5|];
    [|9;9;5;7;1;9;0;9;9|]|];;

let test_sudoku = sudoku simple_sudoku;;
let test_dpll2 = dpll2 test_sudoku;;

let medium_sudoku =
  [|[|9;1;9;7;4;3;9;9;9|];
    [|9;9;9;5;9;9;9;9;7|];
    [|9;0;9;9;9;9;9;9;8|];
    [|1;9;9;9;9;9;9;8;2|];
    [|9;6;4;2;9;7;5;1;9|];
    [|7;8;9;9;9;9;9;9;6|];
    [|3;9;9;9;9;9;9;5;9|];
    [|2;9;9;9;9;1;9;9;9|];
    [|9;9;9;6;5;0;9;3;9|]|]

let test_sudoku' = sudoku medium_sudoku;;
let test_dpll2' = dpll2 test_sudoku';;

let hard_sudoku =
  [|[|9;9;9;9;4;9;8;9;9|];
    [|8;7;9;9;9;9;9;4;9|];
    [|9;3;4;6;9;9;2;9;9|];
    [|9;9;3;1;9;9;7;6;9|];
    [|9;9;9;0;9;3;9;9;9|];
    [|9;6;5;9;9;8;0;9;9|];
    [|9;9;7;9;9;0;5;2;9|];
    [|9;1;9;9;9;9;9;7;0|];
    [|9;9;6;9;2;9;9;9;9|]|]

let test_sudoku'' = sudoku hard_sudoku;;
let test_dpll2'' = dpll2 test_sudoku'';;

(* useful functions on lists *)
let rec fold_left f a b_list = match b_list with
  |[] -> a
  |b::t_b_list -> fold_left f (f a b) t_b_list;;
let rec fold_right f a_list b = match a_list with
  |[] -> b
  |a::t_a_list -> f a (fold_right f t_a_list b);;

(* formula to cnf function *)
let rec cnf (form : formula) : cnf =
  (* handle Or *)
  let or_cnf form_cnf1 form_cnf2 = match (form_cnf1, form_cnf2) with
    |([], _) -> []
    |(_, []) -> [] (* because [] means true and (_ || true) = true *)
    |(form_cnf1, form_cnf2) -> fold_left
                                 (fun form_cnf h_clause -> form_cnf @ list_map
                                                             (fun clause -> clause @ h_clause)
                                                             form_cnf1)
                                 []
                                 form_cnf2
  in
  (* handle Not *)
  let rec not_cnf form_cnf = match form_cnf with
    |[] -> [[]]
    |[[]] -> []
    |form_cnf -> fold_right
                   (fun clause form_cnf' -> fold_left
                                              (fun form_cnf'' (b, x) -> form_cnf'' @  list_map
                                                                          (fun clause' -> (not b, x)::clause')
                                                                          form_cnf')
                                              []
                                              clause)
                   form_cnf
                   [[]]
  in
  
  match form with
  |True -> []
  |False -> [[]]
  |Var x -> [[(true, x)]]
  |And (form1, form2) -> (cnf form1) @ (cnf form2)
  |Or (form1, form2) -> let form1_cnf = cnf form1 in
                        let form2_cnf = cnf form2 in
                        or_cnf form1_cnf form2_cnf
  |Not form -> let form_cnf = cnf form in
               not_cnf form_cnf;;
                       
let test_cnf =
  let x = Var 0 in
  let x'= Not x in
  let y = Var 1 in
  let y'= Not y in
  let b = And (And(Or (x,y), Or (x',y)), Not(And(Or (x,y'), Or (x',y')))) in
  let b_cnf = cnf b in
  dpll2 b_cnf;;        
let test_cnf' =
  let x = Var 0 in
  let x'= Not x in
  let y = Var 1 in
  let y'= Not y in
  let b = Not (And(Or (x,y), Or (x',y))) in
  cnf b;;
