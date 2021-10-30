type prog =
  |Bool of bool
  |Int of int
  |Add of prog * prog
  |Prd of prog * prog (* This is a product operation that I added
                         because I was confused with the products
                         demanded in the question 5 *)
  |Lt of prog * prog
  |If of prog * prog * prog
  |Pair of prog * prog (* The products demanded in the question 5 *)
  |Unit;; (* Added in question 5*)

 (* This function reduce perform a SINGLE STEP reduction,
    first by reducing the left argument of any programme with couples.
    The returned value is an option of prog which permit us to know
    if the program can be reduced or not. *)
let rec reduce prog = match prog with
  |Pair(prog1, prog2) ->
    begin
      let reduc1 = reduce prog1 in
      let reduc2 = reduce prog2 in
      match (reduc1, reduc2) with
      |(Some prog1r, _) -> Some(Pair(prog1r, prog2))
      |(None, Some prog2r) -> Some(Pair(prog1, prog2r))
      |(None, None) -> None
    end
  |Prd(Int n1, Int n2) -> Some(Int (n1 * n2))
  |Prd(prog1, prog2) ->
    begin
      let reduc1 = reduce prog1 in
      let reduc2 = reduce prog2 in
      match (reduc1, reduc2) with
      |(Some prog1r, _) -> Some(Prd(prog1r, prog2))
      |(None, Some prog2r) -> Some(Prd(prog1, prog2r))
      |(None, None) -> None
    end
  |Add(Int n1, Int n2) -> Some(Int (n1 + n2))
  |Add(prog1, prog2) ->
    begin
      let reduc1 = reduce prog1 in
      let reduc2 = reduce prog2 in
      match (reduc1, reduc2) with
      |(Some prog1r, _) -> Some(Add(prog1r, prog2))
      |(None, Some prog2r) -> Some(Add(prog1, prog2r))
      |(None, None) -> None
    end
  |Lt(Int n1, Int n2) when n1 < n2 -> Some(Bool true)
  |Lt(Int n1, Int n2) when n1 >= n2 -> Some(Bool false)
  |Lt(prog1, prog2) ->
    begin
      let reduc1 = reduce prog1 in
      let reduc2 = reduce prog2 in
      match (reduc1, reduc2) with
      |(Some prog1r, Some prog2r) -> Some(Lt(prog1r, prog2r))
      |(Some prog1r, None) -> Some(Lt(prog1r, prog2))
      |(None, Some prog2r) -> Some(Lt(prog1, prog2r))
      |(None, None) -> None
    end
  |If(Bool true, prog1, prog2) -> Some(prog1)
  |If(Bool false, prog1, prog2) -> Some(prog2)
  |If(prog1, prog2, prog3) ->
    begin
      let reduc1 = reduce prog1 in
      match reduc1 with
      |Some prog1r -> Some(If(prog1r, prog2, prog3))
      |None -> None
    end
  |_ -> None;;

(* Test for the reduction *)
let test1 = reduce (Prd( Add(Int 1, Int 2), Add(Int 2, Int 4)));;

(* This function normalize complitely the programme using reduce *)
let rec normalize prog =
  let reduc = reduce prog in
  match reduc with
  |None -> prog
  |Some progr -> normalize progr;;

(* Tests for the normalization *)
let test2 = normalize (Pair(Prd( Add(Int 1, Int 2), Add(Int 2, Int 4)), Unit));;
let test3 = normalize (If(Lt(Add(Int 1, Add(Int 2, Int 3)), Int 4), Bool false, Int 5));;

(* The function preduce reduces a programme with MULTI STEPS in parallele.
   It returns a prog type. *)
let rec preduce prog =  match prog with
  |Pair(prog1, prog2) ->
    begin
      let preduc1 = preduce prog1 in
      let preduc2 = preduce prog2 in
      Pair(preduc1, preduc2)
    end
  |Prd(Int n1, Int n2) -> Int (n1 * n2)
  |Prd(prog1, prog2) ->
    begin
      let preduc1 = preduce prog1 in
      let preduc2 = preduce prog2 in
      Prd(preduc1, preduc2)
    end
  |Add(Int n1, Int n2) -> Int (n1 + n2)
  |Add(prog1, prog2) ->
    begin
      let preduc1 = preduce prog1 in
      let preduc2 = preduce prog2 in
      Add(preduc1, preduc2)
    end
  |Lt(Int n1, Int n2) when n1 < n2 -> Bool true
  |Lt(Int n1, Int n2) when n1 >= n2 -> Bool false
  |Lt(prog1, prog2) ->
    begin
      let preduc1 = preduce prog1 in
      let preduc2 = preduce prog2 in
      Lt(preduc1, preduc2)
    end
  |If(Bool true, prog1, prog2) -> prog1
  |If(Bool false, prog1, prog2) -> prog2
  |If(prog1, prog2, prog3) ->
    begin
      let preduc1 = preduce prog1 in
      let preduc2 = preduce prog2 in
      let preduc3 = preduce prog3 in
      If(preduc1, preduc2, preduc3)
    end
  |_ -> prog;;

(* Tests for the preduce function *)
let test1b = preduce (Unit);;
let test2b = preduce (If(Lt(Prd(Int 1, Add(Int 2, Int 3)), Int 4), Bool false, Add(Int 4, Int 1)));;

(* pnormalize normalizes a programme using preduce *)
let rec pnormalize prog =
  let preduc = preduce prog in
  if prog = preduc then prog else pnormalize preduc;;

(* Test of pnormalize *)
let test3b = pnormalize (Pair(If(Lt(Prd(Int 1, Add(Int 2, Int 3)), Int 4), Bool false, Add(Int 4, Int 1)), Unit));;

(* The type typ is defined here *)
type typ =
  |TBool
  |TInt
  |TPair of typ * typ
  |TUnit;;

(* The function infer return the type of a programme.
   It raises an error if their is no type to describe the type of
   the programme (as for If (Bool true, Int 4, Bool false)) *)
exception Type_error
let rec infer prog =
  match prog with
  |Unit -> TUnit
  |Int n -> TInt
  |Bool b -> TBool
  |Pair(p1, p2) ->
    begin
      let inf1 = infer p1 in
      let inf2 = infer p2 in
      TPair(inf1, inf2)
    end
  |Prd(p1, p2) ->
    begin
      let inf1 = infer p1 in
      let inf2 = infer p2 in
      match (inf1, inf2) with
      |(TInt, TInt) -> TInt
      |_ -> raise Type_error
    end
  |Add(p1, p2) ->
    begin
      let inf1 = infer p1 in
      let inf2 = infer p2 in
      match (inf1, inf2) with
      |(TInt, TInt) -> TInt
      |_ -> raise Type_error
    end
  |Lt(p1, p2) ->
    begin
      let inf1 = infer p1 in
      let inf2 = infer p2 in
      match (inf1, inf2) with
      |(TInt, TInt) -> TBool
      |_ -> raise Type_error
    end
  |If(p, p1, p2) ->
    begin
      let infp = infer p in
      let inf1 = infer p1 in
      let inf2 = infer p2 in
      match (infp, inf1, inf2) with
      |(TBool, TInt, TInt) -> TInt
      |(TBool, TBool, TBool) -> TBool
      |_ -> raise Type_error
    end;;

(* Tests of infer function *)
let test4 = infer (Pair(If(Lt(Prd(Int 1, Add(Int 2, Int 3)), Int 4), Bool false, Int 5), Int 1));;
let test5 = infer (Pair(If(Lt(Prd(Int 1, Add(Int 2, Int 3)), Int 4), Bool false, Bool true), Unit));;

(* The function typable returns if the programme is typable or not *)
let typable prog =
  try
   match infer prog with _ -> true
  with
  |Type_error -> false;;

(* Tests for typable *)
let test6 = typable (Prd(Unit, Bool false));;
let test7 = typable (If(Lt(Add(Int 1, Add(Int 2, Int 3)), Int 4), Bool false, Bool true));;
let test8 = typable (Pair(Unit, Bool false));;

(* Operations added to use pairs.
   It returns respectively the first and the second argument *)
exception Not_a_pair
let first prog = match prog with
  |Pair(prog1, _) -> prog1
  |_ -> raise Not_a_pair;;
let second prog = match prog with
  |Pair(_, prog1) -> prog1
  |_ -> raise Not_a_pair;;

(* Tests for first *)
let test9 = first (Pair(Unit, Bool false));;
let test10 = first(Int 3);;


let rec sublist l1 l2 = match (l1, l2) with
  |([], []) -> true
  | (_, []) -> true
  |(x :: q1, y :: q2) when x = y -> sublist q1 q2
  |(x :: q1, y :: q2) when x != y -> sublist q1 (y :: q2)
  | (_ ,_) -> false;;

let l1 = 1 :: 2 :: 3::4::5::6::[];;
let l2 = 2::4::4::[];;
let testsublist = sublist l1 l2;;

let (un, deux, trois) = ref (1, 2, 3);;
