
#use "pc.ml";;
open PC;;

exception X_not_yet_implemented;;
exception X_this_should_not_happen;;

(*-----------------------------------------------------------*)
(*------------------- Types & Modules -----------------------*)
(*-----------------------------------------------------------*)

type number =
  | Fraction of int * int
  | Float of float;;
  
type sexpr =
  | Bool of bool
  | Nil
  | Number of number
  | Char of char
  | String of string
  | Symbol of string
  | Pair of sexpr * sexpr;;

let rec sexpr_eq s1 s2 =
  match s1, s2 with
  | Bool(b1), Bool(b2) -> b1 = b2
  | Nil, Nil -> true
  | Number(Float f1), Number(Float f2) -> abs_float(f1 -. f2) < 0.001
  | Number(Fraction (n1, d1)), Number(Fraction (n2, d2)) -> n1 = n2 && d1 = d2
  | Char(c1), Char(c2) -> c1 = c2
  | String(s1), String(s2) -> s1 = s2
  | Symbol(s1), Symbol(s2) -> s1 = s2
  | Pair(car1, cdr1), Pair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
  | _ -> false;;
  

module Reader: sig
  val read_sexprs : string -> sexpr list
end
= struct
let normalize_scheme_symbol str =
  let s = string_to_list str in
  if (andmap
	(fun ch -> (ch = (lowercase_ascii ch)))
	s) then str
  else Printf.sprintf "|%s|" str;;


  
(*-----------------------------------------------------------*)
(*-------------------- Help functions -----------------------*)
(*-----------------------------------------------------------*)

let make_paired nt_left nt_right nt =
  let nt= caten nt_left nt in
  let nt= pack nt (function (_,e)->e) in 
  let nt = caten nt nt_right in
  let nt = pack nt (function (e, _)->e) in nt ;;

let nt_whitespaces = star nt_whitespace;; 

let make_spaced nt= 
  make_paired nt_whitespaces nt_whitespaces nt;;

let rec rest s = 
  try let x = nt_end_of_input s in
   x
  with X_no_match -> try let (e,s) = (char '\n') s in
   ([], s)
  with X_no_match ->
  let (e,s) = nt_any s in
    rest s;; 

let nt_LineComment s = 
  let (semicolon,s) = (char ';') s in
  let (com,s) = rest s in
  ([],s) ;;

let nt_Space s=
  let (_,s)= nt_whitespace s in
  ([],s);;

(*-----------------------------------------------------------*)
(*-------------------------- Char ---------------------------*)
(*-----------------------------------------------------------*)

let ntVisibleChar = const (fun ch -> ' ' <= ch && ch <= '~');; 

let ntNamedChars s = 
    let check_nul = pack (word_ci "nul") (fun _-> Char.chr 0) in 
    let check_newLine = pack (word_ci "newline") (fun _-> Char.chr 10) in 
    let check_return = pack (word_ci "return") (fun _-> Char.chr 13) in 
    let check_tab = pack (word_ci "tab") (fun _-> Char.chr 9) in 
    let check_formfeed = pack (word_ci "page") (fun _-> Char.chr 12) in 
    let check_space = pack (word_ci "space") (fun _-> Char.chr 32) in 
    let packed = disj_list [ check_nul ; check_newLine ; check_return ; check_tab ; check_formfeed ; check_space] in
    packed s;; 
  


(*-----------------------------------------------------------*)
(*------------------------ Number ---------------------------*)
(*-----------------------------------------------------------*)

let ntSign s =
  let check_minus = pack (char '-') (fun _-> (-1)) in  
  let check_plus = pack (char '+') (fun _-> (1)) in  
  let other = pack nt_epsilon (fun _-> (1)) in  
  let packed = disj_list [check_minus ; check_plus ; other] in
  packed s ;;

let nt_digit_0_to_9 = const (fun ch -> '0' <= ch && ch <= '9');;
let nt_natural =
  let rec make_nt_natural () = 
    pack (caten nt_digit_0_to_9 (disj (delayed make_nt_natural) nt_epsilon)) (function (a, s) -> a :: s) in
    pack (make_nt_natural()) (fun s -> (List.fold_left(fun a b -> 10 * a + (int_of_char b - 48)) 0 s));;

let nt_mantissa =
  let rec make_nt_mantissa () = 
    pack (caten nt_digit_0_to_9 (disj (delayed make_nt_mantissa) nt_epsilon)) (function (a, s) -> a :: s) in
    pack (make_nt_mantissa())(fun s -> (List.fold_right(fun a b -> ((float_of_int (int_of_char a - 48)) +. b) /. 10.0) s 0.0));;

let nt_E s =
  let (e,s)= (one_of "eE") s in
  let (sign,s) =  ntSign s in
  let (exp,s) = nt_natural s in 
  let packed= (pack nt_epsilon (fun _-> 10.0 ** (float_of_int (sign*exp)))) in
  packed s;;

let nt_MaybeE s= 
  try let (e,s) = nt_E s in
    (e,s)
  with X_no_match ->  (1.0,s);;

let rec gcd a b =
  if b=0 then a else gcd b (a mod b);;  

(*-----------------------------------------------------------*)
(*----------------------- String ----------------------------*)
(*-----------------------------------------------------------*)

let nt_metaChars s = 
  let check_return = pack (word_ci "\\r") (fun _-> (Char.chr 13)) in 
  let check_newline = pack (word_ci "\\n") (fun _-> (Char.chr 10)) in 
  let check_newline2 = pack (word_ci "\n") (fun _-> (Char.chr 10)) in 
  let check_tab = pack (word_ci "\\t") (fun _-> (Char.chr 9)) in 
  let check_page = pack (word_ci "\\f") (fun _-> (Char.chr 12)) in
  let check_backslash = pack (word_ci "\\\\") (fun _-> (Char.chr 92)) in 
  let check_doubleQuote = pack (word_ci "\\\"") (fun _-> (Char.chr 34)) in 
  let packed = disj_list [check_doubleQuote ; check_return ; check_newline ; check_newline2 ; 
    check_tab ; check_page ; check_backslash ] in
  packed s;;

let ntRegularChars = const (fun ch -> ' ' <= ch && ch <= '~' && ch!='\"' && ch!='\\');; 

let nt_charsInString = star(disj nt_metaChars ntRegularChars) ;;
 
(*-----------------------------------------------------------*)
(*----------------------- Symbol ----------------------------*)
(*-----------------------------------------------------------*)
let nt_lowCaseChar = const (fun ch -> 'a' <= ch && ch <= 'z');;

let nt_upperCaseChar = pack (const (fun ch -> 'A' <= ch && ch <= 'Z')) lowercase_ascii;;

let nt_puncruation = one_of "?<>+=_-*^$!:/";;

let nt_dot = char '.';;

let nt_charNoDot = disj_list [nt_lowCaseChar ; nt_upperCaseChar ; nt_puncruation ; nt_digit_0_to_9];;

let nt_symbolChar = disj nt_charNoDot nt_dot;;
  
(*-----------------------------------------------------------*)
(*------------------------- Pair ----------------------------*)
(*-----------------------------------------------------------*)

let tok_lparen s = 
  let lp = char '(' in
  let spaced= caten(caten nt_whitespaces lp) nt_whitespaces in
  pack spaced (fun ((l, p), r) -> p) s;;

let tok_rparen s = 
  let rp = char ')' in
  let spaced= caten(caten nt_whitespaces rp) nt_whitespaces in
  pack spaced (fun ((l, p), r) -> p) s;;

(*-----------------------------------------------------------*)
(*------------------ Quoute-like forms ----------------------*)
(*-----------------------------------------------------------*)

let nt_quoted = char '\'';;

let nt_quasiquoted = char '`';;

let nt_unquoted = char ',';;

let nt_unquotedSpliced = word ",@";;

(*-----------------------------------------------------------*)
(*-------------------- Main-Function ------------------------*)
(*-----------------------------------------------------------*)

(*------------------ Quoute-like forms ----------------------*)
let rec nt_Quouted s = 
  try let (e, s) =  (pack (caten nt_quoted nt_expr) (fun(a,b) -> b)) s in
    Pair(Symbol ("quote"), Pair(e, Nil)),s
  with X_no_match ->
    try let (e, s) = (pack (caten nt_quasiquoted nt_expr) (fun(a,b) -> b)) s in
      Pair(Symbol ("quasiquote"), Pair(e, Nil)),s
  with X_no_match ->
    try let (e, s) = (pack (caten nt_unquoted nt_expr) (fun(a,b) -> b)) s in
      Pair(Symbol ("unquote"), Pair(e, Nil)),s
  with X_no_match ->
    let (e, s) = (pack (caten nt_unquotedSpliced nt_expr) (fun(a,b) -> b)) s in
      Pair(Symbol ("unquote-splicing"), Pair(e, Nil)),s

(*------------------------- Pair ----------------------------*)

and nt_PairBody s = 
  let (car,s) = nt_expr s in
  try let (rp,s) = tok_rparen s in
    Pair(car, Nil),s
  with X_no_match -> 
  try let (dot,s) = (make_spaced nt_dot) s in
    let (cdr, s) = nt_expr s in
    let (rp, s) = tok_rparen s in
    Pair(car, cdr),s
  with X_no_match -> 
    let (cdr,s)= nt_PairBody s in 
    Pair (car,cdr),s

and nt_Pair s = 
  let (lp,s)= tok_lparen s in 
  let x = nt_PairBody s in 
  x
  

(*----------------------- Symbol ----------------------------*)
and ntSymbol s = 
  try let (e, s) = nt_charNoDot s in
    let (es, s) = (star nt_symbolChar) s in
    Symbol (list_to_string (e::es)),s
  with X_no_match -> 
    let (e,s)= nt_symbolChar s in 
    let (es,s) = (plus nt_symbolChar) s in
    Symbol (list_to_string (e::es)),s

(*----------------------- String ----------------------------*)
and ntString s =  
  let (body,s) = (make_paired (char '\"') (char '\"') nt_charsInString) s in
  String(list_to_string body),s

(*------------------------ Number ---------------------------*)
and ntNumber s = 
  try let (sign,s)= ntSign s in
    let (num1, s) = (pack nt_natural (fun n-> sign * n))(s)  in
    try let (f, s) = (const (fun ch -> ch = '.') s) in 
      let (num2,s) = (pack nt_mantissa (fun m -> (float_of_int sign) *. m)) s in
      let (e,s) = (nt_MaybeE s) in
      let (space, s)= disj_list [nt_whitespace ; (pack nt_end_of_input (fun (_) -> ' ')) ; (char ')')] s in
      let num = ((float_of_int num1) +. num2) *. e in  
      Number(Float(num)),(space::s)
    with X_no_match -> 
      try let (e,s) = nt_E s in
      let (space, s)= disj_list [nt_whitespace ; (pack nt_end_of_input (fun (_) -> ' ')) ; (char ')')] s in
      let f = (float_of_int num1) *. e in
      Number(Float(f)),(space::s)
    with X_no_match -> 
      try let (e, s) = (const (fun ch -> ch = '/') s) in 
      let (num2,s) = (nt_natural s) in
      let (space, s)= disj_list [nt_whitespace ; (pack nt_end_of_input (fun (_) -> ' ')) ; (char ')')] s in
      let n = gcd num1 num2 in
      let n_sign = (n * sign) in
      Number(Fraction (num1/n_sign,num2/n_sign)),(space::s)
    with X_no_match -> 
    let (space, s)= disj_list [nt_whitespace ; (pack nt_end_of_input (fun (_) -> ' ')) ; (char ')')] s in
    Number(Fraction (num1,1)),(space::s)
  with X_no_match -> ntSymbol s
  
(*-------------------------- Char ---------------------------*)
and ntChar s =
  let (e,s) = (word "#\\") s in
  let (c,s) = (disj ntNamedChars ntVisibleChar) s in
  Char(c),s 

(*-------------------------- Nil ----------------------------*)
and ntNil s= 
  let (lp,s) = tok_lparen s in
  try let (e,s) = (char ';') s in  
    let (es,s) = rest s in
    let (rp,s) = tok_rparen s in
    Nil,s
  with X_no_match -> 
  try let (e,s)= (word "#;") s in 
    let (_, s) = nt_expr s in
    Nil,s 
  with X_no_match -> let (rp,s) = char ')' s in
    Nil,s

(*------------------------- Bool ----------------------------*)
and ntBool s=
  let head = char '#' in
  let _one = one_of "tTfF" in
  let chain = caten head _one in
  let (e,s) = pack chain (fun (hd, tl) -> match tl with
    | 't' -> true
    | 'T' -> true
    | 'f' -> false
    | 'F' -> false
    | _ -> raise X_no_match) s in
    Bool(e),s

(*----------------------- Comments ----------------------------*)

and nt_SexpComment s = 
  let (_, s) = (word "#;") s in 
  let (_, s) = nt_expr s in
  ([],s) 

and nt_Comments s = 
  let (_,s) = star (disj_list [nt_Space;nt_LineComment;nt_SexpComment]) s in
  ([],s)

and make_spaced2 nt= 
make_paired nt_Comments nt_Comments nt
 
and nt_expr s = disj_list [(make_spaced2 ntBool) ;  (make_spaced2 ntChar) ; (make_spaced2 ntNumber) ; (make_spaced2 ntString) ; 
  (make_spaced2 ntSymbol) ; (make_spaced2 nt_Pair); (make_spaced2 ntNil) ;(make_spaced2 nt_Quouted)] s ;;

let ntSexpr = star nt_expr ;;

let read_sexprs string = 
  let (e,_) = ntSexpr (string_to_list string) in
  e ;;
    
end;; (* struct Reader *)