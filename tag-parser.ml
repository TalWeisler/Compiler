#use "reader.ml";;

type constant =
  | Sexpr of sexpr
  | Void

type expr =
  | Const of constant
  | Var of string
  | If of expr * expr * expr
  | Seq of expr list
  | Set of expr * expr
  | Def of expr * expr
  | Or of expr list
  | LambdaSimple of string list * expr
  | LambdaOpt of string list * string * expr
  | Applic of expr * (expr list);;

let rec expr_eq e1 e2 =
  match e1, e2 with
  | Const Void, Const Void -> true
  | Const(Sexpr s1), Const(Sexpr s2) -> sexpr_eq s1 s2
  | Var(v1), Var(v2) -> String.equal v1 v2
  | If(t1, th1, el1), If(t2, th2, el2) -> (expr_eq t1 t2) &&
                                            (expr_eq th1 th2) &&
                                              (expr_eq el1 el2)
  | (Seq(l1), Seq(l2)
    | Or(l1), Or(l2)) -> List.for_all2 expr_eq l1 l2
  | (Set(var1, val1), Set(var2, val2)
    | Def(var1, val1), Def(var2, val2)) -> (expr_eq var1 var2) &&
                                             (expr_eq val1 val2)
  | LambdaSimple(vars1, body1), LambdaSimple(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr_eq body1 body2)
  | LambdaOpt(vars1, var1, body1), LambdaOpt(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr_eq body1 body2)
  | Applic(e1, args1), Applic(e2, args2) ->
     (expr_eq e1 e2) &&
       (List.for_all2 expr_eq args1 args2)
  | _ -> false;;
	
                       
exception X_syntax_error;;

module type TAG_PARSER = sig
  val tag_parse_expressions : sexpr list -> expr list
end;; (* signature TAG_PARSER *)

module Tag_Parser : TAG_PARSER = struct

(*-----------------------------------------------------------*)
(*-------------------- Help Functions -----------------------*)
(*-----------------------------------------------------------*)

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
    "if"; "lambda"; "let"; "let*"; "letrec"; "or";
    "quasiquote"; "quote"; "set!"; "pset!"; "unquote";
    "unquote-splicing"];;  

let word_list s = (List.exists (fun word-> word=s) reserved_word_list);;

let nt_param_string s = 
  if (word_list s)
  then raise X_syntax_error  
  else s;;

let exists_Nil p = List.exists (fun w-> w=Nil) p;;

let nt_VarSymbol x = 
  if(word_list x)
  then raise X_syntax_error(*X_syntax_error*) 
  else Var(x);;
  
(*-----------------------------------------------------------*)
(*-------------------- Main Functions -----------------------*)
(*-----------------------------------------------------------*)

let rec nt_Constant = function 
  | Bool(x) -> Const(Sexpr(Bool(x)))
  | Char (x) -> Const(Sexpr(Char(x)))
  | Number (x) -> Const(Sexpr(Number(x)))
  | String (x) -> Const(Sexpr(String(x)))
  | Pair(Symbol("quote"),Pair(x,Nil)) -> Const(Sexpr(x))
  | _-> raise X_no_match
  
and nt_Variables = function
  | Symbol(x) -> nt_VarSymbol(x)
  | _-> raise X_no_match 

and nt_Conditionals = function 
  | Pair(Symbol("if"),Pair(test, Pair(dit,Pair(dif,Nil))))->
      If(tag_parse test, tag_parse dit, tag_parse dif)
  | Pair(Symbol("if"),Pair(test, Pair(dit,Nil)))->
      If(tag_parse test, tag_parse dit, Const(Void))
  | _-> raise X_no_match

and nt_Lambdas = function
  | Pair(Symbol("lambda"), Pair(Nil, rest)) -> nt_lambda_exp (Pair(Nil, rest))
  | Pair(Symbol("lambda"),Pair(Pair(Symbol(x),restParams),Pair(body1,restBody)))->
      nt_lambda_exp (Pair(Pair(Symbol(x),restParams),Pair(body1,restBody)))
  | Pair(Symbol("lambda"),Pair(param,body)) -> nt_lambdaVariadic (Pair(param,body))
  | _-> raise X_no_match

and nt_lambdaVariadic e = match e with
  | (Pair(Symbol(x), Pair(b,Nil))) -> LambdaOpt([], x, (tag_parse b))
  | (Pair(Symbol(x), rest)) -> LambdaOpt([], x, Seq(nt_body [] rest))
  | _-> raise X_no_match

and nt_lambda_exp e = match e with
  | Pair(Nil, Pair(x,Nil)) -> LambdaSimple([], (tag_parse x)) (*without parameters and 1 body example: (lambda () a)*)
  | Pair(Nil, rest) -> LambdaSimple([], Seq(nt_body [] rest)) (*without parameters and more than 1 body example: (lambda () a b) *)
  | Pair(x, Pair(y,Nil)) -> nt_ParmsToLambdaOne [] x y (*parameters and 1 body example: (lambda (x) x) or (lambda (x . y) x) *)
  | Pair(x, rest) -> nt_ParmsToLambdaMoreThanOne [] x rest (*parameters and more than 1 body example: (lambda (x) x y) or (lambda (x . y) x y)*)
  | _-> raise X_no_match

and nt_lambda_exp2 e = match e with
  | Pair(Nil, Pair(x,Nil)) -> (tag_parse x) (*without parameters and 1 body example: (lambda () a)*)
  | Pair(Nil, rest) -> Seq(nt_body [] rest) (*without parameters and more than 1 body example: (lambda () a b) *)
  | Pair(x, Pair(y,Nil)) -> nt_ParmsToLambdaOne [] x y (*parameters and 1 body example: (lambda (x) x) or (lambda (x . y) x) *)
  | Pair(x, rest) -> nt_ParmsToLambdaMoreThanOne [] x rest (*parameters and more than 1 body example: (lambda (x) x y) or (lambda (x . y) x y)*)
  | _-> raise X_no_match

and nt_ParmsToLambdaOne l e b = match e with
  | Pair(Symbol(x),Nil) -> LambdaSimple((List.map nt_param_string (List.append l [x])), (tag_parse b))
  | Pair(Symbol(x), Symbol(y)) -> LambdaOpt((List.map nt_param_string (List.append l [x])), y, (tag_parse b))
  | Pair(Symbol(x), rest) -> nt_ParmsToLambdaOne (List.append l [x]) rest b
  | _-> raise X_no_match

and nt_ParmsToLambdaMoreThanOne l e b = match e with
  | Pair(Symbol(x),Nil) -> LambdaSimple((List.map nt_param_string (List.append l [x])), Seq(nt_body [] b))
  | Pair(Symbol(x), Symbol(y)) -> LambdaOpt((List.map nt_param_string (List.append l [x])), y, Seq(nt_body [] b))
  | Pair(Symbol(x), rest) -> (nt_ParmsToLambdaMoreThanOne (List.append l [x]) rest b)
  | _-> raise X_no_match

and nt_body l rest = match rest with
  | Pair(x,Nil) -> (List.map tag_parse (List.append l [x])) (*x can be Pair(Symbol a) example: (lambda (...) (if...)), then x will catch all the if including the pair(Avi)*)
  | Pair(x,rest) -> (nt_body (List.append l [x]) rest)
  | _ -> raise X_no_match

and nt_Disjunction = function
  | Pair(Symbol("or"), Nil) -> Const(Sexpr(Bool(false)))
  | Pair(Symbol("or"), Pair(x,Nil)) -> tag_parse x
  | Pair(Symbol("or"), parms) -> Or((nt_ParamsList [] parms))
  | _-> raise X_no_match

and nt_ParamsList ps p = match p with 
  | Pair(Symbol("quote"), Pair (x, Nil)) -> (List.map tag_parse (List.append ps [p])) 
  | Pair(x,Nil) -> (List.map tag_parse (List.append ps [x]))
  | Pair(Symbol("quote"),Pair(x, rest)) -> (nt_ParamsList (List.append ps [Pair(Symbol("quote"),Pair(x,Nil))]) rest)
  | Pair(x,y) -> (nt_ParamsList (List.append ps [x]) y)
  | x -> [(tag_parse x)] 

and nt_define = function
  | Pair(Symbol("define"), Pair(Pair(Symbol(var),argslist),Pair(expr, Nil))) -> 
    tag_parse (Pair(Symbol"define", Pair(Symbol(var),Pair(Pair(Symbol("lambda"), Pair(argslist, Pair(expr, Nil))),Nil))))
  | Pair(Symbol("define"), Pair(Symbol(name), Pair(expr, Nil)))->
    Def(nt_VarSymbol(name), tag_parse expr)
  | _ -> raise X_no_match

and nt_set = function
  | Pair(Symbol("set!"), Pair(Symbol(name), Pair(expr, Nil))) ->
    Set(nt_VarSymbol(name), tag_parse expr)
  | _ -> raise X_no_match

and nt_moreThanOne_begin l rest = match rest with 
  | Pair(x,Nil) -> (List.map tag_parse (List.append l [x]))
  | Pair(Pair(Symbol("begin"), e),x) -> (nt_moreThanOne_begin l (Pair(e,x))) (*remove the "begin" example: (begin a (begin b c))*)
  | Pair(x,e) -> (nt_moreThanOne_begin (List.append l [x]) e)
  | _ -> raise X_no_match

and nt_seq_begin = function
  | Pair(Symbol("begin"), Nil) -> Const(Void)
  | Pair(Symbol("begin"), Pair(rest, Nil)) -> tag_parse rest  
  | Pair(Symbol("begin"), rest) -> Seq(nt_moreThanOne_begin [] rest)
  | _ -> raise X_no_match

and nt_ParamsOrParse = 
  fun e -> try (nt_ParamsList [] e)
  with X_no_match -> [(tag_parse e)]

and nilOrNot params =match params with
  | Nil -> []
  | _ -> nt_ParamsOrParse params

and nt_Applic = function
  | Pair(app,params)-> Applic(tag_parse app, nilOrNot params) 
  | _ -> raise X_no_match

(*-------------------- Macro Expension -----------------------*)  
 
and expand_quasiquote e = match e with
  | Pair (Symbol "unquote", Pair (x, Nil)) -> tag_parse x
  | Nil -> Const(Sexpr(Nil))
  | Symbol(x) -> tag_parse (Pair(Symbol("quote"),Pair(Symbol(x),Nil)))
  | Pair (Symbol "unquote-splicing", Pair (x, Nil)) -> tag_parse (Pair(Symbol("quote"), Pair(Pair(Symbol("unquote-splicing"), Pair(x,Nil)),Nil)))
  | Pair (Pair (Symbol "unquote-splicing", Pair (a, Nil)), Nil) -> Applic(Var("append"),[tag_parse a; Const(Sexpr(Nil))]) 
  | Pair (Pair (Symbol "unquote-splicing", Pair (a, Nil)),Pair (b, Nil)) -> Applic(Var("append"), [(tag_parse a); (expand_quasiquote (Pair (b, Nil)))])
  | Pair (Pair (Symbol "unquote-splicing", Pair (a, Nil)),Pair (b, rest)) -> Applic(Var("append"), [(tag_parse a); (expand_quasiquote (Pair (b, rest)))])
  | Pair (a, b) -> Applic(Var("cons"), [(expand_quasiquote a); (expand_quasiquote b)])
  | _ -> raise X_no_match

and nt_quasiquoted_sexpr = function 
  | Pair(Symbol("quasiquote"),Pair(e,Nil)) -> expand_quasiquote e
  | _ -> raise X_no_match

and expand_cond = function
  | Pair(Symbol("cond"), ribs) -> tag_parse (cond_ribs ribs)
  | _ -> raise X_no_match

and cond_ribs e = match e with
  | Pair(Pair(expr, Pair(Symbol("=>"), Pair(exprf, Nil))), Nil) -> 
    (Pair(Symbol("let"), 
      Pair(Pair(Pair(Symbol("value"), Pair(expr, Nil)),
        Pair(Pair(Symbol("f"), Pair(Pair(Symbol("lambda"),Pair(Nil,Pair(exprf,Nil))), Nil)), Nil)), 
          Pair(Pair(Symbol("if"), Pair(Symbol("value"), Pair(Pair(Pair(Symbol("f"), Nil), 
            Pair(Symbol("value"),Nil)), Nil))), Nil))))
  | Pair(Pair(expr, Pair(Symbol("=>"), Pair(exprf, Nil))),restCond) -> 
    (Pair(Symbol("let"), 
      Pair(Pair(Pair(Symbol("value"), Pair(expr, Nil)),
        Pair(Pair(Symbol("f"), Pair(Pair(Symbol("lambda"), Pair(Nil, Pair(exprf,Nil))), Nil)), 
          Pair(Pair(Symbol("rest"),Pair(Pair(Symbol("lambda"), Pair(Nil, Pair((cond_ribs restCond), Nil))), Nil)), Nil))), 
            Pair(Pair(Symbol("if"), Pair(Symbol("value"), Pair(Pair(Pair(Symbol("f"), Nil), 
              Pair(Symbol("value"),Nil)), Pair(Pair(Symbol("rest"), Nil),Nil)))), Nil))))
  | Pair(Pair(Symbol("else"), body), rest) -> (Pair(Symbol("begin"), body))
  | Pair(Pair(test, body),Nil) -> Pair(Symbol("if"), Pair(test, Pair(Pair(Symbol("begin"), body), Nil)))
  | Pair(Pair(test, body),rest) -> Pair(Symbol("if"), Pair(test, Pair(Pair(Symbol("begin"), body), Pair((cond_ribs rest), Nil)))) (*CHECK IF IT BECOMES A SEQUENCE*)
  | _ -> raise X_no_match

and let_body b = match b with 
  | Pair(body, Nil) -> tag_parse body
  | Pair(body, rest) -> Seq(nt_body [] b)
  | _ -> raise X_no_match

and nt_Let_params ps vs s b = match s with 
  | Nil -> Applic(nt_lambda_exp(Pair(Nil, b)),[])
  | Pair(Pair(Symbol(p), Pair (v, Nil)),Nil)-> 
      Applic((LambdaSimple((List.map nt_param_string (List.append ps [p])),(let_body b))),
      (List.map tag_parse (List.append vs [v])))
  | Pair(Pair (Symbol(p), Pair (v, Nil)),next)-> 
      (nt_Let_params (List.append ps [p]) (List.append vs [v]) next b)
  | _ -> raise X_no_match

and nt_Let = function 
  | Pair(Symbol("let"),Pair(params,body))-> (nt_Let_params [] [] params body)
  | _ -> raise X_no_match 
  
and nt_Let_star_cases s b = match s with 
  | Nil-> Applic((LambdaSimple([],(let_body b))),[]) 
  | Pair(Pair (Symbol(p), Pair (v, Nil)),Nil)->
    Applic(LambdaSimple([(nt_param_string p)],(let_body b)),[(tag_parse v)])
  | Pair(Pair (Symbol(p), Pair (v, Nil)),x)-> 
    Applic(LambdaSimple([(nt_param_string p)],(nt_Let_star_cases x b)),[(tag_parse v)])
  | _ -> raise X_no_match
 
and nt_Let_star = function 
  | Pair(Symbol("let*"),Pair(params,body))-> (nt_Let_star_cases params body)
  | _ -> raise X_no_match 

and nt_Letrec_check lst_var lst_expr params body = match params with
  | Nil -> tag_parse (Pair(Symbol("let"),Pair(Nil, body)))
  | Pair(Pair(var, expr),Nil) -> 
      let e_whatever = (nt_letrec_param (List.append lst_var [var]) Nil) in 
      let e_set = (nt_letrec_set (List.append lst_var [var]) (List.append lst_expr [expr]) Nil body) in
      (tag_parse (Pair(Symbol("let"), Pair(e_whatever, e_set))))
  | Pair(Pair(var, expr),rest)-> nt_Letrec_check (List.append lst_var [var]) (List.append lst_expr [expr]) rest body
  | _ -> raise X_no_match

and nt_letrec_param lst_var e = match lst_var with
  | [] -> e
  | _ -> match e with
        | Nil -> (nt_letrec_param (List.tl lst_var)
                  (Pair(Pair((List.hd lst_var), Pair(Pair(Symbol("quote"),Pair(Symbol("Wahtever"),Nil)), Nil)),Nil)))
        | _ -> (nt_letrec_param (List.tl lst_var)
        (Pair(Pair((List.hd lst_var), Pair(Pair(Symbol("quote"),Pair(Symbol("Wahtever"),Nil)), Nil)),e)))
        
and nt_letrec_set lst_var lst_expr e body= match lst_var with 
  | [] -> e
  | _ -> match e with
        | Nil -> (nt_letrec_set (List.tl lst_var) (List.tl lst_expr)
                (Pair(Pair(Symbol("set!"), Pair((List.hd lst_var), (List.hd lst_expr))),body)) Nil)
        | _ -> (nt_letrec_set (List.tl lst_var) (List.tl lst_expr)
              (Pair(Pair(Symbol("set!"), Pair((List.hd lst_var), (List.hd lst_expr))), e)) Nil)

and nt_Letrec = function 
  | Pair(Symbol("letrec"),Pair(params,body))-> (nt_Letrec_check [] [] params body)
  | _ -> raise X_no_match 

and nt_and = function
  | Pair(Symbol("and"), Nil) -> tag_parse (Bool(true))
  | Pair(Symbol("and"), Pair(e,Nil)) -> tag_parse e 
  | Pair(Symbol("and"), Pair(e1, Pair(e2, rest))) -> tag_parse (Pair(Symbol("if"), Pair(e1, Pair(Pair(Symbol("and"), Pair(e2, rest)), Pair(Bool (false), Nil)))))
  | _ -> raise X_no_match

and nt_pset = function
  | Pair(Symbol("pset!"),Pair(e1,e2)) -> nt_macroPset (Pair(e1,e2)) Nil Nil
  | _ -> raise X_no_match

and nt_macroPset e ribs body = match e with
  | Pair(Pair(Symbol(var), Pair(expr, Nil)), Nil) -> tag_parse (Pair(Symbol("let"),
    Pair
      (Pair(Pair(Symbol(list_to_string (List.append (string_to_list var) ['|';'|';'1'])), Pair(expr, Nil)),ribs), 
        Pair(Pair(Symbol("set!"), Pair(Symbol(var), 
          Pair(Symbol(list_to_string (List.append (string_to_list var) ['|';'|';'1'])),Nil))),body))))
  | Pair(Pair(Symbol(var), Pair(expr, Nil)), rest) ->
    nt_macroPset rest (Pair(Pair(Symbol(list_to_string (List.append (string_to_list var) ['|';'|';'1'])), Pair(expr, Nil)),ribs)) 
          (Pair(Pair(Symbol("set!"), Pair(Symbol(var), 
            Pair(Symbol(list_to_string (List.append (string_to_list var) ['|';'|';'1'])),Nil))),body))
  | _ -> raise X_no_match

and tag_parse s = disj_list[nt_Constant; nt_Variables; nt_Conditionals; nt_seq_begin; nt_Lambdas; 
                  nt_Disjunction; nt_define; nt_set; nt_pset; nt_and; 
                  nt_Let; nt_Let_star; nt_Letrec; nt_quasiquoted_sexpr; expand_cond; nt_Applic] s;; 
      

                  
let nt_tag s = (List.map tag_parse s);;

let tag_parse_expressions sexpr = nt_tag sexpr;;
 
end;; (* struct Tag_Parser *)
