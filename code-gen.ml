#use "semantic-analyser.ml";;

(* This module is here for you convenience only!
   You are not required to use it.
   you are allowed to change it. *)
module type CODE_GEN = sig
  (* This signature assumes the structure of the constants table is
     a list of key-value pairs:
     - The keys are constant values (Sexpr(x) or Void)
     - The values are pairs of:
       * the offset from the base const_table address in bytes; and
       * a string containing the byte representation (or a sequence of nasm macros)
         of the constant value
     For example: [(Sexpr(Nil), (1, "T_NIL"))]
   *)
  val make_consts_tbl : expr' list -> (constant * (int * string)) list

  (* This signature assumes the structure of the fvars table is
     a list of key-value pairs:
     - The keys are the fvar names as strings
     - The values are the offsets from the base fvars_table address in bytes
     For example: [("boolean?", 0)]
   *)  
  val make_fvars_tbl : expr' list -> (string * int) list


  (* If you change the types of the constants and fvars tables, you will have to update
     this signature to match: The first argument is the constants table type, the second 
     argument is the fvars table type, and the third is an expr' that has been annotated 
     by the semantic analyser.
   *)
  val generate : (constant * (int * string)) list -> (string * int) list -> expr' -> string
end;;

module Code_Gen : CODE_GEN = struct
let counter = ref 0;;
let next_val = 
  fun () ->
    counter := (!counter) + 1;
    !counter;;

let string_to_ascii_list str =
  let chars = string_to_list str in
  let ascii = (List.map Char.code chars) in 
  let ascii1= (List.map Pervasives.string_of_int ascii) in
  let ascii2= (String.concat ", " ascii1) in 
  ascii2;;


(*-------------------------------------------------*)
(*-----------------constnts table------------------*)
(*-------------------------------------------------*)

let rec check_const lst ast = match ast with 
    | Const'(x) -> [x]
    | Var'(x) -> []
    | Box'(x) -> []
    | BoxGet'(x) -> [] 
    | BoxSet'(x, ex) -> (check_const lst ex) 
    | If'(test, dit, dif) -> (List.append (check_const lst test) (List.append (check_const lst dit) (check_const lst dif)))
    | Seq'(ex) -> (check_seq_const lst ex)
    | Set'(v, ex) -> (check_const lst ex) 
    | Def'(v, ex) -> (check_const lst ex)
    | Or'(ex) -> (check_seq_const lst ex)
    | LambdaSimple'(params, ex) -> (check_const lst ex)
    | LambdaOpt'(params, optional, ex) -> (check_const lst ex)
    | Applic'(operator, operands) -> (List.append (check_const lst operator) 
                                      (check_seq_const lst operands))
    | ApplicTP'(operator, operands) -> (List.append (check_const lst operator) 
                                        (check_seq_const lst operands))

  and check_seq_const lst e = match e with 
    | [] -> []
    | _ -> let l1 = (check_const lst (List.hd e)) in
            let l2 = (check_seq_const lst (List.tl e)) in
            (List.append l1 l2);;

  let rec remove_duplicates original_lst new_lst = match original_lst with
    | [] -> new_lst
    | _ -> if (List.mem (List.hd original_lst) new_lst)
            then (remove_duplicates (List.tl original_lst) new_lst)
            else (remove_duplicates (List.tl original_lst) (List.append new_lst [(List.hd original_lst)]));;

  let rec search_sub_const original_lst new_lst e = match original_lst with 
    | [] -> (List.append new_lst (check_sub_e e))
    | _ -> (search_sub_const (List.tl original_lst) (List.append new_lst (check_sub_e e)) (List.hd original_lst))

  and check_sub_e e = match e with
    | Void -> [e]
    | Sexpr(Nil) -> [e]
    | Sexpr(Bool(x)) -> [e]
    | Sexpr(Number(x)) -> [e]
    | Sexpr(Char(x)) -> [e]
    | Sexpr(String(x)) -> [e]
    | Sexpr(Symbol(x)) -> [Sexpr(String(x)); e]
    | Sexpr(x) -> (add_sub_e x [e]) 
    
  and add_sub_e e sub_lst= match e with
    | Pair(x, Nil) -> (add_sub_e x (List.append [Sexpr(x)] sub_lst))
    | Pair(x, rest) -> let l1 = (add_sub_e rest [Sexpr(rest)]) in
                        let l2 = (add_sub_e x [Sexpr(x)]) in
                        (List.append l1 (List.append l2 sub_lst))
    | Symbol(x) -> (List.append [Sexpr(String(x))] sub_lst)
    | _ -> sub_lst ;;

  let make_string_to_symbol e_symbol tuple = match tuple with
    | (sexpr, (index , s)) -> "MAKE_LITERAL_SYMBOL(const_tbl+"^(Pervasives.string_of_int index)^")";;

  let check_sexpr e_symbol e = match e with
    | Void -> false
    | Sexpr(Nil) -> false
    | Sexpr(Bool(x)) -> false
    | Sexpr(Number(x)) -> false
    | Sexpr(Symbol(x)) -> false
    | Sexpr(Char(x)) -> false
    | Sexpr(Pair(x,y)) -> false
    | Sexpr(String(x)) -> match e_symbol with
                          | Sexpr(Symbol(x2)) -> if (x=x2) then true else false 
                          | _ -> false ;;

  let check_eq_ss e_symbol tuple = match tuple with
    | (sexpr, (index, s)) -> (check_sexpr e_symbol sexpr) ;;
    
  let rec find_match tuple_list e = match tuple_list with
    | [] -> -1
    | _ -> (check_if_match (List.hd tuple_list) e tuple_list) 
                                    
  and check_if_match tuple e tuple_list = match tuple with
    | (Void, (index, s)) -> (find_match (List.tl tuple_list) e) 
    | (Sexpr(x), (index, s)) -> if (sexpr_eq e x) 
                              then index 
                              else (find_match (List.tl tuple_list) e);;

  let find_car_cdr tuple_list e = match e with 
    | Nil -> ""
    | Bool(x) -> ""
    | Number(x) -> ""
    | Char(x) -> ""
    | String(x) -> ""
    | Symbol(x) -> ""
    | Pair(car, cdr) ->let index1 = (find_match tuple_list car) in
                        let index2 = (find_match tuple_list cdr) in
                        ("MAKE_LITERAL_PAIR(const_tbl+"^(Pervasives.string_of_int index1)^", const_tbl+"^(Pervasives.string_of_int index2)^")");;
  
  let rec list_tuples original_lst tuple_list index = match original_lst with
    | [] -> tuple_list
    | _ -> (make_tuples (List.hd original_lst) (List.tl original_lst) tuple_list index) 
 
  and make_tuples e original_lst tuple_list index = match e with 
    | Void -> (list_tuples original_lst (List.append tuple_list [(e, (index, "db T_VOID"))]) (index+1)) 
    | Sexpr(Nil) -> (list_tuples original_lst (List.append tuple_list [(e, (index, "db T_NIL"))]) (index+1))
    | Sexpr(Bool(false)) -> (list_tuples original_lst (List.append tuple_list [(e, (index, "db T_BOOL, 0"))]) (index+2))
    | Sexpr(Bool(true)) -> (list_tuples original_lst (List.append tuple_list [(e, (index, "db T_BOOL, 1"))]) (index+2))
    | Sexpr(Char(x)) -> let ascii=  (Pervasives.string_of_int (Char.code x)) in
                        (list_tuples original_lst (List.append tuple_list [(e, (index,"MAKE_LITERAL_CHAR ("^ascii^")"))]) (index+2))
    | Sexpr(Number(Float(x))) -> (list_tuples original_lst (List.append tuple_list [(e, (index, "MAKE_LITERAL_FLOAT("^(Pervasives.string_of_float x)^")"))]) (index+9))
    | Sexpr(Number(Fraction(n,d))) -> (list_tuples original_lst (List.append tuple_list [(e, (index, "MAKE_LITERAL_RATIONAL("^(Pervasives.string_of_int n)^","^(Pervasives.string_of_int d)^")"))]) (index+17))
    | Sexpr(String(x)) -> let ascii = (string_to_ascii_list x) in
                        (list_tuples original_lst (List.append tuple_list [(e, (index, "MAKE_LITERAL_STRING "^ascii))]) (index+9+(String.length x)))
    | Sexpr(Symbol(x)) -> (list_tuples original_lst (List.append tuple_list [(e, (index, (find_string_to_symbol tuple_list e)))]) (index+9))
    | Sexpr(x) -> (list_tuples original_lst (List.append tuple_list [(e, (index, (find_car_cdr tuple_list x)))]) (index+17))
    
  and find_string_to_symbol tuple_list e = match tuple_list with
    | [] -> raise X_no_match
    | _ -> let flag = (check_eq_ss e (List.hd tuple_list)) in
            if (flag) 
            then (make_string_to_symbol e (List.hd tuple_list))
            else (find_string_to_symbol (List.tl tuple_list) e) ;;   

  let make_consts_tbl asts = 
    let regulars = [Void; Sexpr(Nil); Sexpr (Bool (false)); Sexpr (Bool (true))] in
    let lst = (List.map (check_const regulars) asts) in
    let lst = (List.concat lst) in
    let lst = (List.append regulars lst) in 
    let lst = (remove_duplicates lst []) in
    let lst = (search_sub_const (List.tl lst) [] (List.hd lst)) in 
    let lst = (remove_duplicates lst []) in
    let lst = (list_tuples lst [] 0) in
    lst;;

(*-------------------------------------------------*)
(*-------------------fvars table-------------------*)
(*-------------------------------------------------*)

  let rec look_for_fvar lst ast = match ast with 
    | Const'(x) -> []
    | Var'(x) -> (check_if_fver x)
    | Box'(x) -> []
    | BoxGet'(x) -> [] 
    | BoxSet'(x, ex) -> (look_for_fvar lst ex) 
    | If'(test, dit, dif) -> (List.append (look_for_fvar lst test) (List.append (look_for_fvar lst dit) (look_for_fvar lst dif)))
    | Seq'(ex) -> (check_seq_fvar lst ex)
    | Set'(v, ex) -> (List.append (check_if_fver v) (look_for_fvar lst ex)) 
    | Def'(v, ex) -> (List.append (check_if_fver v) (look_for_fvar lst ex))
    | Or'(ex) -> (check_seq_fvar lst ex)
    | LambdaSimple'(params, ex) -> (look_for_fvar lst ex)
    | LambdaOpt'(params, optional, ex) -> (look_for_fvar lst ex)
    | Applic'(operator, operands) -> (List.append (look_for_fvar lst operator) 
                                      (check_seq_fvar lst operands))
    | ApplicTP'(operator, operands) -> (List.append (look_for_fvar lst operator) 
                                        (check_seq_fvar lst operands))

  and check_if_fver e = match e with
    | VarFree(x) -> [x]
    | _ -> []

  and check_seq_fvar lst e = match e with 
    | [] -> []
    | _ -> let l1 = (look_for_fvar lst (List.hd e)) in
            let l2 = (check_seq_fvar lst (List.tl e)) in
            (List.append l1 l2);;

  let rec make_tuples_fvar original_lst tuple_list index = match original_lst with 
    | [] -> tuple_list
    | _ -> (make_tuples_fvar (List.tl original_lst) (List.append tuple_list [((List.hd original_lst), (index*8))]) (index+1))

  let make_fvars_tbl asts = 
    let regulars = ["boolean?";"equal?";"flonum?";"string->list";"rational?";"length";"pair?";"number?";"null?";"integer?";
    "char?";"zero?";"string?";">";"procedure?";"-";"symbol?";"not";"string-length";"map-many";"string-ref";"map-one";
    "string-set!";"make-string";"symbol->string";"char->integer";"integer->char";"exact->inexact";
    "eq?";"+";"*";"/";"=";"<";"numerator";"denominator";"gcd";"car"; "cdr";"set-car!";"set-cdr!";"cons";"map";
    "apply";"fold-left";"fold-right";"inside";"cons*";"append";"list";"list?";"make-string"] in
    let lst = (List.map (look_for_fvar regulars) asts) in
    let lst = (List.concat lst) in
    let lst = (List.append regulars lst) in 
    let lst = (remove_duplicates lst []) in
    let lst = (make_tuples_fvar lst [] 0) in
    lst;;
  
(*-------------------------------------------------*)
(*--------------------generate---------------------*)
(*-------------------------------------------------*)

  let rec get_const_add consts_tbl e = match consts_tbl with
    | [] -> -1
    | _ -> (check_add (List.hd consts_tbl) e consts_tbl)
  
  and check_add (expr, (index, s)) e consts_tbl = match e with
    | Void -> if (expr = Void) then index else raise X_no_match
    | Sexpr(x1) -> match expr with 
                  | Void -> (get_const_add (List.tl consts_tbl) e)
                  | Sexpr(x2) -> if (sexpr_eq x1 x2)
                                  then index
                                  else (get_const_add (List.tl consts_tbl) e);;

  let rec get_fvar_add fvars_tbl e = match fvars_tbl with
    | [] -> -1
    | _ -> (check_add2 (List.hd fvars_tbl) e fvars_tbl)
  
  and check_add2 (s, index) e fvars_tbl = if (e = s) then index else (get_fvar_add (List.tl fvars_tbl) e);;
let rec concat_or lst s e_s c = match lst with
    | [] -> (s^"\n"^e_s^"\nLexit"^c^":")
    | _ -> let a = "cmp rax, SOB_FALSE_ADDRESS\njne Lexit"^c in
            (concat_or (List.tl lst) (s^"\n"^e_s^"\n"^a) (List.hd lst) c);;
(*let () = Printf.printf "check L:%s Params:%s\n" c ch in*)            
let lambda_simple d body lambda_opt=  
    let c = (Pervasives.string_of_int (next_val())) in
    let env_0 = "mov rax, qword[rbp + 8 * 3]\ninc rax ;for magic\nmov rcx, rax\nmov rbx, 8 \nimul rbx \nMALLOC rbx, rax \nCOPY_ARGS rcx, rbx" in
    let new_env = env_0^"\nMALLOC rcx, "^(Pervasives.string_of_int ((d+1)*8))^"\nmov [rcx], rbx \nmov rax, qword[rbp + 8 * 2] \nCOPY_ENV "^(Pervasives.string_of_int (d+1))^", rcx, rax" in 
    let create_lcode= "Lcode"^c^":\n"^lambda_opt^"\npush rbp\nmov rbp, rsp\n"^body^"\nmov rsp, rbp\npop rbp\nret\n" in 
    new_env^"\nMAKE_CLOSURE(rax, rcx, Lcode"^c^")\njmp Lcont"^c^"\n"^create_lcode^"\nLcont"^c^":";;

let check_args_applic s_operands len = if (len = 0) 
  then "\npush "^(Pervasives.string_of_int len)^" ;check_args_applic"^s_operands
  else s_operands^"\npush rax\npush "^(Pervasives.string_of_int len);;

let rec lambda_Opt d params body =
  let update_stack = "\nmov rax,"^(Pervasives.string_of_int (List.length params))^" ;the length of the obligatory params\nLAMBDA_OPT rax\n" in
  (lambda_simple d body update_stack )
(*(String.concat ", " params)*)
and check_applic consts fvars d operator operands =  
  let rev_operands = (List.rev operands) in
        if ((List.length rev_operands) = 0) 
        then ([], 0)
        else ((List.map (generate1 consts fvars d) rev_operands), (List.length operands))

and generate1 consts fvars d e = match e with 
    | Const'(x) -> let address = (Pervasives.string_of_int(get_const_add consts x)) in
                  "mov rax, const_tbl + "^address
    | Var'(VarFree(x)) -> let address = (get_fvar_add fvars x) in
                                "mov rax, qword[fvar_tbl +"^(Pervasives.string_of_int address)^"]"
    | Var'(VarBound(x, major, minor)) -> "mov rax, qword[rbp + 8 * 2] \nmov rax, qword[rax + 8 * "^(Pervasives.string_of_int major)^"] \nmov rax, qword[rax + 8 * "^(Pervasives.string_of_int minor)^"]"
    | Var'(VarParam(x, minor)) -> "mov rax, qword [rbp + 8 *(4 + "^(Pervasives.string_of_int minor)^")] ;4"
    | Box'(VarFree(x)) -> "" (*there is no reason to do box here, so we wont get that option*)
    | Box'(VarBound(x, major, minor)) -> "" (*do we need to do box here??*)
    | Box'(VarParam(x, minor)) -> "mov rbx, qword [rbp + 8 *(4 + "^(Pervasives.string_of_int minor)^")];5\nMALLOC rax, 8 \nmov [rax], rbx ;regular box"
    | BoxGet'(x) -> let string_x = (generate1 consts fvars d (Var'(x))) in 
                              string_x^"\nmov rax, qword[rax]"
    | BoxSet'(x, ex) -> let string_ex = (generate1 consts fvars d ex) in
                        let string_x = (generate1 consts fvars d (Var'(x))) in 
                        string_ex^" ;boxset first line\npush rax\n"^string_x^"\npop qword[rax]\nmov rax, SOB_VOID_ADDRESS"
    | If'(test, dit, dif) -> let string_test = (generate1 consts fvars d test) in
                              let string_dit = (generate1 consts fvars d dit) in
                              let string_dif = (generate1 consts fvars d dif) in
                              let c = (Pervasives.string_of_int (next_val())) in 
                              string_test^"\ncmp rax, SOB_FALSE_ADDRESS \nje Lelse"^c^"\n"^string_dit^"\njmp Lexit"^c^" \nLelse"^c^": \n"^string_dif^"\nLexit"^c^":"
    | Seq'(ex) -> let lst = (List.map (generate1 consts fvars d) ex) in 
                  (String.concat "\n" lst)
    | Set'(VarParam(v, minor), ex) -> let string_c = (generate1 consts fvars d ex) in
                                              string_c^" ;set varparam \nmov qword[rbp + 8 * (4 + "^(Pervasives.string_of_int minor)^")],rax ;6\nmov rax, SOB_VOID_ADDRESS"
    | Set'(VarBound(v, major,minor), ex) -> let string_c = (generate1 consts fvars d ex) in
                                                    ""^string_c^" ; set var bound\nmov rbx, qword[rbp + 8 * 2] \nmov rbx, qword[rbx + 8 * "^(Pervasives.string_of_int major)^"] \nmov qword[rbx + 8 * "^(Pervasives.string_of_int minor)^"], rax \nmov rax, SOB_VOID_ADDRESS"
    | Set'(VarFree(v),ex) -> let string_c = (generate1 consts fvars d ex) in
                                      let address = (get_fvar_add fvars v) in
                                      string_c^"\nmov qword[fvar_tbl +"^(Pervasives.string_of_int (address))^"], rax \nmov rax, SOB_VOID_ADDRESS"
    | Def'(VarBound(v, major,minor), ex) -> ""
    | Def'(VarParam(v, minor), ex) -> ""
    | Def'(VarFree(v), ex) -> let string_c = (generate1 consts fvars d ex) in
                              let address = (get_fvar_add fvars v) in
                              string_c^"\nmov qword[fvar_tbl +"^(Pervasives.string_of_int address)^"], rax \nmov rax, SOB_VOID_ADDRESS"
    | Or'(ex) -> let lst = (List.map (generate1 consts fvars d) ex) in 
                 let c= (Pervasives.string_of_int (next_val())) in
                  (concat_or (List.tl lst) "" (List.hd lst) c)
    | LambdaSimple'(params, ex) -> let body = (generate1 consts fvars (d+1) ex) in 
                                    (lambda_simple d body "")
    | LambdaOpt'(params, optional, ex) -> let body = (generate1 consts fvars (d+1) ex) in 
                                          (lambda_Opt d params body)
    | Applic'(operator, operands) ->  let (lst,l) = (check_applic consts fvars d operator operands) in
                                      let s_operands = (String.concat "\npush rax\n" lst) in
                                      let s_op_and_n = (check_args_applic s_operands l) in
                                      let s_operator = (generate1 consts fvars d operator) in 
                                      "push SOB_NIL_ADDRESS ;magic applic"^(Pervasives.string_of_int l)^"\n"^s_op_and_n^"\n"^s_operator^"\nmov rbx, rax\nCLOSURE_ENV rax, rbx \npush rax \nCLOSURE_CODE rax, rbx \ncall rax \nadd rsp, 8 \npop rbx \nadd rbx, 1 ; add 1 for the magic\nshl rbx, 3\nadd rsp, rbx"
    | ApplicTP'(operator, operands) -> let (lst,l) = (check_applic consts fvars d operator operands) in
                                      let s_operands = (String.concat "\npush rax\n" lst) in
                                      let s_op_and_n = (check_args_applic s_operands l) in
                                      let s_operator = (generate1 consts fvars d operator) in 
                                      "push SOB_NIL_ADDRESS ;magic applictp"^(Pervasives.string_of_int l)^"\n"^s_op_and_n^"\n"^s_operator^"\nmov rbx, rax\nCLOSURE_ENV rax, rbx \npush rax \npush qword[rbp+8] \nmov rcx, qword[rbp+8*3] \nUPDATE_FRAME rcx, "^(Pervasives.string_of_int l)^"\nCLOSURE_CODE rax, rbx\njmp rax";;

  let generate consts fvars e = (generate1 consts fvars 0 e);;

end;;
(*
  *)
let check str =
  let p1= (Reader.read_sexprs str) in 
  let p2= (Tag_Parser.tag_parse_expressions p1) in
  let e = List.map Semantics.run_semantics p2 in
  let e2 = (Code_Gen.make_consts_tbl e) in 
  let e3 = (Code_Gen.make_fvars_tbl e) in
  let e4 = (String.concat "\n\n"
              (List.map
                (fun ast -> (Code_Gen.generate e2 e3 ast) ^ "\n\tcall write_sob_if_not_void")
                e)) in
  (p1, p2 , e,e2,e3, e4);;