#use "tag-parser.ml";;

type var = 
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int;;

type expr' =
  | Const' of constant
  | Var' of var
  | Box' of var
  | BoxGet' of var
  | BoxSet' of var * expr'
  | If' of expr' * expr' * expr'
  | Seq' of expr' list
  | Set' of var * expr'
  | Def' of var * expr'
  | Or' of expr' list
  | LambdaSimple' of string list * expr'
  | LambdaOpt' of string list * string * expr'
  | Applic' of expr' * (expr' list)
  | ApplicTP' of expr' * (expr' list);;

let rec expr'_eq e1 e2 =
  match e1, e2 with
  | Const' Void, Const' Void -> true
  | Const'(Sexpr s1), Const'(Sexpr s2) -> sexpr_eq s1 s2
  | Var'(VarFree v1), Var'(VarFree v2) -> String.equal v1 v2
  | Var'(VarParam (v1,mn1)), Var'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
  | Var'(VarBound (v1,mj1,mn1)), Var'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
  | If'(t1, th1, el1), If'(t2, th2, el2) -> (expr'_eq t1 t2) &&
                                            (expr'_eq th1 th2) &&
                                              (expr'_eq el1 el2)
  | (Seq'(l1), Seq'(l2)
  | Or'(l1), Or'(l2)) -> List.for_all2 expr'_eq l1 l2
  | (Set'(var1, val1), Set'(var2, val2)
  | Def'(var1, val1), Def'(var2, val2)) -> (expr'_eq (Var'(var1)) (Var'(var2))) &&
                                             (expr'_eq val1 val2)
  | LambdaSimple'(vars1, body1), LambdaSimple'(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr'_eq body1 body2)
  | LambdaOpt'(vars1, var1, body1), LambdaOpt'(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr'_eq body1 body2)
  | Applic'(e1, args1), Applic'(e2, args2)
  | ApplicTP'(e1, args1), ApplicTP'(e2, args2) ->
	 (expr'_eq e1 e2) &&
	   (List.for_all2 expr'_eq args1 args2)
  | _ -> false;;
	
                       
exception X_syntax_error;;

module type SEMANTICS = sig
  val run_semantics : expr -> expr'
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
end;;

module Semantics : SEMANTICS = struct

(*-------------------------------------------------*)
(*---------------Lexical addressing----------------*)
(*-------------------------------------------------*)

let rec getMinor j ps v = match ps with 
(*int -> 'a list -> 'a -> int*)
  | []-> -1
  | e::s -> if (e=v) then j else (getMinor (j + 1) s v)

and getMajor i ps v = match ps with
  | []-> (-1,-1)
  | e::s -> 
      let j = (getMinor 0 e v) in  
      if (j >= 0) then (i,j) else (getMajor (i + 1) s v)

and var_cases i j v = match i with
  | -1 -> VarFree(v)
  | 0 -> VarParam(v,j)
  | _ -> VarBound(v,(i-1),j)

and lex_Var ps v = 
  let (i,j)= (getMajor 0 ps v) in
  let v = (var_cases i j v) in 
  v

and lex ps e = match e with
  | Const(e)-> Const'(e)
  | Var(e)-> Var'(lex_Var ps e)
  | If(test, dit, dif)-> If'((lex ps test),(lex ps dit),(lex ps dif))
  | Seq(e)-> Seq'(List.map (lex ps) e)
  | Set(Var(v),e)-> Set'((lex_Var ps v),(lex ps e))
  | Def(Var(v),e)-> Def'((lex_Var ps v),(lex ps e))
  | Or(e)-> Or'(List.map (lex ps) e)
  | LambdaSimple(params,e)-> LambdaSimple'(params,(lex (List.append [params] ps) e))
  | LambdaOpt(params,p,e)-> LambdaOpt'(params,p,(lex (List.append [(List.append params [p])] ps) e))
  | Applic(op,e)-> Applic'((lex ps op),(List.map (lex ps) e))
  | _ -> raise X_no_match;;

let annotate_lexical_addresses e = (lex [] e);;
let check1 str = 
  let e = Tag_Parser.tag_parse_expressions(Reader.read_sexprs str) in
  let e1 = (List.map (lex []) e) in
  e1;;

(*-------------------------------------------------*)
(*-------------Annotating tail calls---------------*)
(*-------------------------------------------------*)

let rec find_last es e tp = match e with 
  | [e] -> (List.append es [(annotate tp e)])
  | e::s -> (find_last (List.append es [(annotate false e)]) s tp)
  | _ -> raise X_no_match

and annotate tp e = match e with
  | Const'(e) -> Const'(e)
  | Var'(e) -> Var'(e)
  | If'(test,dit,dif)-> If'(test, (annotate tp dit), (annotate tp dif))
  | Seq'(e)-> Seq'(find_last [] e tp)
  | Set'(v,e)-> Set'(v,(annotate false e))
  | Def'(v,e)-> Def'(v,(annotate false e))
  | Or'(e)-> Or'(find_last [] e tp)
  | LambdaSimple'(p,b)-> LambdaSimple'(p,(annotate true b))
  | LambdaOpt'(p1,p2,b) -> LambdaOpt'(p1,p2,(annotate true b))
  | Applic'(op,es) -> (annotate_applic op es tp)
  | _ -> raise X_no_match

and annotate_applic e es tp = 
  if (tp) 
  then (ApplicTP'((annotate false e), (List.map (annotate false) es)))
  else (Applic'((annotate false e), (List.map (annotate false) es)));;

let annotate_tail_calls e = (annotate false e);;
let check2 str = 
    let e = Tag_Parser.tag_parse_expressions(Reader.read_sexprs str) in
    let e1 = (List.map (lex []) e) in
    let e2 = (List.map (annotate false) e1) in
    (e,e2);;

(*-------------------------------------------------*)
(*--------------Boxing of variables----------------*)
(*-------------------------------------------------*)

let eq n e = if (e = n) then true else false;;

let check_var n x l_path all_path = match x with
  | VarFree(v) -> []
  | VarParam(v,j) -> if (n=v) 
      then [[l_path; all_path]] 
      else [] 
  | VarBound(v,i,j) -> if (n=v) 
      then [[l_path; all_path]] 
      else [];;

let check_ts hd1 hd2 = 
  let t1= (int_of_char (String.get hd1 1)) in 
  let t2 = (int_of_char (String.get hd2 1)) in 
  if (t1 < t2) then false else true;;

(*["L0";"S0"] ["L0";"S1";"LL0S1"]*)
let rec check_if_seq p1 p2 = match p1,p2 with
(*Responde: if it one of the Additional boxing criteria -> false  else ->true*)
  | [],hd::tl -> true 
  | hd1::tl1,hd2::tl2 -> 
      if (hd1 = hd2) then (check_if_seq tl1 tl2)
      else
        let h1 = (String.get hd1 0) in 
        let h2 = (String.get hd2 0) in
        if ((h1 = 'S') && (h2 = 'S'))
          then (check_ts hd1 hd2) 
          else true
  | _ -> raise X_no_match;;

(*[] ["L0S1"] ["L0";"S0"] ["L0";"S1";"LL0S1"]*)
let check_tail rest_l1 rest_l2 all_path1 all_path2 = match rest_l1,rest_l2 with
  | [],[] -> false
  | [],hd::tl -> (check_if_seq all_path1 all_path2)
  | hd::tl,[] -> (check_if_seq all_path2 all_path1)
  | _-> 
    let l1= (List.hd rest_l1) in
    let l2= (List.hd rest_l2) in 
    if (l1=l2) then false else true;;

(* P1 [["0"];["L0";"S0"]]   P2 [["0";"L0S1"];["L0";"S1";"LL0S1"]]*)   
let eq_path p1 p2 =   
  let l_path_1 = (List.hd p1) in (*["0"]*) 
  let l_path_2 = (List.hd p2) in (*["0";"L0S1"]*) 
  let first_l1 = (List.hd l_path_1) in (*"0"*) 
  let first_l2 = (List.hd l_path_2) in (*"0"*) 
  let rest_l1 = (List.tl l_path_1) in (*[]*)
  let rest_l2 = (List.tl l_path_2) in (*["L0S1"]*)
  let all_path1 = (List.hd (List.tl p1)) in (*["L0";"S0"]*)
  let all_path2 = (List.hd (List.tl p2)) in (*["L0";"S1";"LL0S1"]*)
  if (first_l1 = first_l2) 
    then (check_tail rest_l1 rest_l2 all_path1 all_path2)
    else true;;

let rec compare_everything r_list w_list = match r_list with 
  | [] -> false
  | _ -> 
    let res1 = (List.exists (eq_path (List.hd r_list)) w_list) in
    if (res1) 
      then true 
      else (compare_everything (List.tl r_list) w_list);;

let rec check_read n e l_path all_path = match e with  
  | Const'(x) -> []
  | Var'(x) -> (check_var n x l_path all_path)
  | Box'(x) -> []
  | BoxGet'(x) -> []
  | BoxSet'(x, ex) -> (check_read n ex l_path (List.append all_path ["0"]))
  | If'(test, dit, dif) -> (List.append (check_read n test l_path (List.append all_path ["0"])) 
                            (List.append (check_read n dit l_path (List.append all_path ["1"])) 
                              (check_read n dif l_path (List.append all_path ["2"]))))                          
  | Seq'(ex) -> (check_list n ex l_path all_path "S" 0)
  | Set'(v, ex) -> (check_read n ex l_path (List.append all_path ["0"]))
  | Or'(ex) -> (check_list n ex l_path all_path "" 0)
  | LambdaSimple'(params, ex) -> (read_lambda params ex n l_path all_path)
  | LambdaOpt'(params, optional, ex) -> (read_lambda (List.append params [optional]) ex n l_path all_path)
  | Applic'(operator, operands) -> (List.append (check_read n operator l_path (List.append all_path ["0"]))
                                    (check_list n operands l_path all_path "" 1))
  | ApplicTP'(operator, operands) -> (List.append (check_read n operator l_path (List.append all_path ["0"]))
                                      (check_list n operands l_path all_path "" 1))
  | _ -> raise X_no_match

and check_list n e l_path all_path sign index = match e with
  | [] -> []
  | _ -> let l1 = (check_read n (List.hd e) l_path (List.append all_path [sign^(string_of_int index)])) in
          let l2 = (check_list n (List.tl e) l_path all_path sign (index+1)) in
          (List.append l1 l2)

and read_lambda params ex n l_path all_path = 
  if (List.exists (eq n) params) 
    then []
    else 
      let id= (String.concat "" all_path) in 
      (check_read n ex (List.append l_path [id]) (List.append all_path ["L"^id]));;

let rec check_write n e l_path all_path = match e with 
  | Const'(x) -> []
  | Var'(x) -> []
  | Box'(x) -> []
  | BoxGet'(x) -> []
  | BoxSet'(x, ex) -> (check_write n ex l_path (List.append all_path ["0"]))
  | If'(test, dit, dif) -> (List.append (check_write n test l_path (List.append all_path ["0"])) 
                            (List.append (check_write n dit l_path (List.append all_path ["1"])) 
                              (check_write n dif l_path (List.append all_path ["2"]))))                          
  | Seq'(ex) -> (check_list_w n ex l_path all_path "S" 0)
  | Set'(v, ex) -> (List.append (check_var n v l_path all_path)
                    (check_write n ex l_path (List.append all_path ["0"])))
  | Or'(ex) -> (check_list_w n ex l_path all_path "" 0)
  | LambdaSimple'(params, ex) -> (write_lambda params ex n l_path all_path)
  | LambdaOpt'(params, optional, ex) -> (write_lambda (List.append params [optional]) ex n l_path all_path)
  | Applic'(operator, operands) -> (List.append (check_write n operator l_path (List.append all_path ["0"]))
                                    (check_list_w n operands l_path all_path "" 1))
  | ApplicTP'(operator, operands) -> (List.append (check_write n operator l_path (List.append all_path ["0"]))
                                      (check_list_w n operands l_path all_path "" 1))
  | _ -> raise X_no_match

and check_list_w n e l_path all_path sign index = match e with
  | [] -> []
  | _ -> let l1 = (check_write n (List.hd e) l_path (List.append all_path [sign^(string_of_int index)])) in
          let l2 = (check_list_w n (List.tl e) l_path all_path sign (index+1)) in
          (List.append l1 l2)

and write_lambda params ex n l_path all_path = 
  if (List.exists (eq n) params) 
    then []
    else 
      let id= (String.concat "" all_path) in 
      (check_write n ex (List.append l_path [id]) (List.append all_path ["L"^id]));;

let check_box e n l_path all_path = 
  let r_list = (check_read n e l_path all_path) in 
  let w_list = (check_write n e l_path all_path) in 
  if (((List.length r_list) = 0) || ((List.length w_list) = 0))
    then false
    else (compare_everything r_list w_list);;

let pred_var n e = match e with
  | VarFree(v) -> if (n=v) then true else false
  | VarParam(v,j) -> if (n=v) then true else false
  | VarBound(v,i,j) -> if (n=v) then true else false

let get_Box n x = if (pred_var n x) then BoxGet'(x) else Var'(x);; 
let rec make_box n e = match e with
  | Const'(x) -> Const'(x)
  | Var'(x) -> (get_Box n x)  
  | Box'(x) -> Box'(x)
  | BoxGet'(x) -> BoxGet'(x)
  | BoxSet'(x, ex) -> BoxSet'(x, (make_box n ex))
  | If'(test, dit, dif) -> If'((make_box n test), (make_box n dit), (make_box n dif))
  | Seq'(ex) -> Seq'(List.map (make_box n) ex)
  | Set'(v, ex) -> if (pred_var n v) then BoxSet'(v,(make_box n ex)) else Set'(v,(make_box n ex))
  | Def'(v, ex) -> Def'(v, (make_box n ex))
  | Or'(ex) -> Or'(List.map (make_box n) ex)
  | LambdaSimple'(params, ex) -> LambdaSimple'(params, (make_lambda n ex params)) 
  | LambdaOpt'(params, optional, ex) -> LambdaOpt'(params, optional, (make_lambda n ex (List.append params [optional]))) 
  | Applic'(operator, operands) -> Applic'((make_box n operator), (List.map (make_box n) operands))
  | ApplicTP'(operator, operands) -> ApplicTP'((make_box n operator), (List.map (make_box n) operands))

and make_lambda n e params = 
  if (List.exists (eq n) params) 
    then e 
    else (make_box n e);; 

let add_Box n e minor a = 
  (e, (List.append a [Set'(VarParam(n,minor),Box'(VarParam(n,minor)))]));;
  
let check_param e n index a=
  if (check_box e n ["0"] ["L0"])
    then (add_Box n (make_box n e) index a)
    else (e,a);; 

let add_SetBox e a = match e with
  | Seq'(e) -> Seq'((List.append a e))
  | _ -> Seq'((List.append a [e]));;

let rec check_lambda e p_list index add_set = match p_list with 
  | [] -> (check_if_seq_needed e add_set)
  | _ -> 
      let (e1,a1) = (check_param e (List.hd p_list) index add_set) in 
      (check_lambda e1 (List.tl p_list) (index+1) a1) 

and check_if_seq_needed e add_set = match add_set with 
  | [] -> (box_fun e)
  | _ -> let e = (add_SetBox e add_set) in 
    (box_fun e)

and box_fun e = match e with 
  | Const'(x) -> Const'(x)
  | Var'(x) -> Var'(x)  
  | Box'(x) -> Box'(x)
  | BoxGet'(x) -> BoxGet'(x)
  | BoxSet'(x, ex) -> BoxSet'(x, box_fun ex)
  | If'(test, dit, dif) -> If'(box_fun test, box_fun dit, box_fun dif)
  | Seq'(ex) -> Seq'(List.map box_fun ex)
  | Set'(v, ex) -> Set'(v, box_fun ex)
  | Def'(v, ex) -> Def'(v, box_fun ex)
  | Or'(ex) -> Or'(List.map box_fun ex)
  | LambdaSimple'(params, ex) -> LambdaSimple'(params, (check_lambda ex params 0 [])) 
  | LambdaOpt'(params, optional, ex) -> LambdaOpt'(params, optional, (check_lambda ex (List.append params [optional]) 0 [])) 
  | Applic'(operator, operands) -> Applic'(box_fun operator, (List.map box_fun operands))
  | ApplicTP'(operator, operands) -> ApplicTP'(box_fun operator, (List.map box_fun operands))

let box_set e = box_fun e;;

let check3 str =  
  let e = Tag_Parser.tag_parse_expressions(Reader.read_sexprs str) in
  let e1 = (List.map (lex []) e) in
  let e2 = (List.map (annotate false) e1) in
  let e3 = (List.map box_fun e2) in
  (e,e3);;

let run_semantics expr =
  box_set
    (annotate_tail_calls
       (annotate_lexical_addresses expr));;
  
end;;

let check str =
  let e = Reader.read_sexprs str in
  let e1 = Tag_Parser.tag_parse_expressions e in
  let r1= (List.map Semantics.annotate_lexical_addresses e1) in
  let r2 = (List.map Semantics.annotate_tail_calls r1) in 
  let r3 = (List.map Semantics.box_set r2) in 
  (e,e1,r1, r2, r3);;

let check2 e = 
  let r1= (List.map Semantics.annotate_lexical_addresses e) in
  let r2 = (List.map Semantics.annotate_tail_calls r1) in 
  let r3 = (List.map Semantics.box_set r2) in 
  (r1, r2, r3);;