
(* reader.ml
 * A compiler from Scheme to x86/64
 *
 * Programmer: Mayer Goldberg, 2018
 *)

#use "pc.ml";;

exception X_not_yet_implemented;;
exception X_this_should_not_happen;;
  
type number =
  | Int of int
  | Float of float;;
  
type sexpr =
  | Bool of bool
  | Nil
  | Number of number
  | Char of char
  | String of string
  | Symbol of string
  | Pair of sexpr * sexpr
  | Vector of sexpr list;;

let rec sexpr_eq s1 s2 =
  match s1, s2 with
  | Bool(b1), Bool(b2) -> b1 = b2
  | Nil, Nil -> true
  | Number(Float f1), Number(Float f2) -> abs_float(f1 -. f2) < 0.001
  | Number(Int n1), Number(Int n2) -> n1 = n2
  | Char(c1), Char(c2) -> c1 = c2
  | String(s1), String(s2) -> s1 = s2
  | Symbol(s1), Symbol(s2) -> s1 = s2
  | Pair(car1, cdr1), Pair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
  | Vector(l1), Vector(l2) -> List.for_all2 sexpr_eq l1 l2
  | _ -> false;;
  
  module Reader: sig
    val read_sexpr : string -> sexpr
    val read_sexprs : string -> sexpr list
  end
  = struct
  let normalize_scheme_symbol str =
    let s = string_to_list str in
    if (andmap
      (fun ch -> (ch = (lowercase_ascii ch)))
      s) then str
    else Printf.sprintf "|%s|" str;;
  
(* Delimeters - Start *)

let space = PC.const (fun ch -> ch <= ' ');;

let whitespaces_star = PC.star (space);;

(* Delimeters - End *)

(* Boolean - Start *)

let hashtag = PC.char '#';;

let boolean =
    let booleanOption = PC.disj (PC.char_ci 't') (PC.char_ci 'f') in
    let getBoolean = PC.caten hashtag booleanOption in
    let booleanProtected =
        PC.not_followed_by
            getBoolean
            (PC.const (fun ch -> ch > ' ' && ch != '#' && ch != '(' && ch != ')' && ch != '[' && ch != ']' && ch != ',' && ch != ';'
                        && ch != '\x27' && ch != '\x60' && ch != '\"' && ch != '\n'))
    in
    PC.pack booleanProtected (fun (a, b) -> match (lowercase_ascii b) with
                                            | 't' -> Bool (true)
                                            | 'f' -> Bool (false)
                                            | _ -> raise PC.X_no_match);;

(* Boolean - End *)

(* Char - Start *)

let charPrefix = PC.caten hashtag (PC.char '\\');;

let visibleSimpleChar =
  PC.pack
    (PC.range '!' '~')
    (fun c -> Char (c));;

let namedChar =
  PC.pack
    (PC.disj_list [PC.word_ci "newline"; PC.word_ci "return"; PC.word_ci "tab"; PC.word_ci "page"; PC.word_ci "space" ; PC.word_ci "nul"])
    (fun (nameCharList) -> match (list_to_string nameCharList) with
                            | "newline" -> Char ('\n')
                            | "return" -> Char ('\r')
                            | "tab" -> Char ('\t')
                            | "page" -> Char ('\x0c')
                            | "space" -> Char (' ')
                            | "nul" -> Char ('\x00')
                            | _ -> raise PC.X_no_match);;

let hexDigit = PC.disj (PC.range '0' '9') (PC.range_ci 'a' 'f');;

let hexChar =
  PC.pack
    (PC.caten (PC.char_ci 'x') (PC.plus hexDigit))
    (fun (x, ascii) -> Char (char_of_int (Scanf.sscanf (list_to_string ascii) "%x" (fun x -> x))));;

let charLHS =
    let getChar = PC.caten charPrefix (PC.disj_list [hexChar; namedChar; visibleSimpleChar]) in
    let charProtector =
        PC.not_followed_by
        getChar
        (PC.const (fun ch -> ch > ' ' && ch != '(' && ch != ')' && ch != '[' && ch != ']' && ch != ',' && ch != ';'
                            && ch != '\x27' && ch != '\x60' && ch != '\"' && ch != '\n'))
    in
    PC.pack charProtector (fun ((charPrefixA, charPrefixB), actualChar) -> actualChar);;

(* Char - End *)

(* Number - Start *)

let hexDigit = PC.disj  (PC.range '0' '9') (PC.range_ci 'a' 'f');;

let sign = PC.disj  (PC.char '+') (PC.char '-');;

let digit = PC.range '0' '9';;

let natural = PC.plus digit;;

let unwrapNumber wrappedNumber = match wrappedNumber with
                                    | Number x -> x
                                    | _ -> raise PC.X_no_match;;

let unwrapInt wrappedInteger = match wrappedInteger with
                                    | Int x -> x
                                    | _ -> raise PC.X_no_match;;

let integer =
    let calc x = int_of_string (list_to_string x) in
    PC.pack
        (PC.caten (PC.maybe sign) natural)
        (fun (maybeSign, numberString) -> match maybeSign with
                                            | Some '+' -> Number (Int (calc numberString))
                                            | Some '-' -> Number (Int ((calc numberString) * (-1)))
                                            | None -> Number (Int (calc numberString))
                                            | _ -> raise PC.X_no_match);;

let floatNt =
    PC.pack
        (PC.caten (PC.maybe sign) (PC.caten natural (PC.caten (PC.char '.') natural)))
        (fun (maybeSign, (intList, (point, fracList))) -> match maybeSign with
                                            | Some '+' -> Number (Float (float_of_string ((list_to_string intList) ^ "." ^ (list_to_string fracList))))
                                            | Some '-' -> Number (Float (float_of_string ((list_to_string intList) ^ "." ^ (list_to_string fracList)) *. (-1.0)))
                                            | None -> Number (Float (float_of_string ((list_to_string intList) ^ "." ^ (list_to_string fracList))))
                                            | _ -> raise PC.X_no_match);;

let hexNatural = PC.plus hexDigit;;

let hexPrefix = PC.caten hashtag (PC.char_ci 'x');;

let hexInteger =
    let calc x = (int_of_string (String.concat "" ["0x"; list_to_string x])) in
    PC.pack
        (PC.caten hexPrefix (PC.caten (PC.maybe sign) hexNatural))
        (fun ((hexPrefixA, hexPrefixB), (maybeSign, digitList)) -> match maybeSign with
                                                                    | Some '+' -> Number (Int (calc digitList))
                                                                    | Some '-' -> Number (Int (calc digitList * (-1)))
                                                                    | None -> Number (Int (calc digitList))
                                                                    | _ -> raise PC.X_no_match);;

let hexFloat =
    let calc x y = float_of_string ("0x" ^ (list_to_string x) ^ "." ^ (list_to_string y)) in
    PC.pack
        (PC.caten hexPrefix (PC.caten (PC.maybe sign) (PC.caten hexNatural (PC.caten (PC.char '.') hexNatural))))
        (fun (prefix , (maybeSign, (intHexList, (dot, fracHexList)))) ->
            match maybeSign with
            | Some '+' -> Number (Float (calc intHexList fracHexList))
            | Some '-' -> Number (Float ((calc intHexList fracHexList) *. (-1.0)))
            | None -> Number (Float (calc intHexList fracHexList))
            | _ -> raise PC.X_no_match);;

let scientificNotation =
    PC.pack
        (PC.caten (PC.disj floatNt integer) (PC.caten (PC.char_ci 'e')  integer))
        (fun (builtNumber,(e,exponent)) -> match unwrapNumber builtNumber with
                                            | Int x -> Number (Float (float_of_string ((string_of_int x) ^ "e" ^ (string_of_int (unwrapInt (unwrapNumber exponent))))))
                                            | Float x -> Number (Float (float_of_string ((string_of_float x) ^ "e" ^ (string_of_int (unwrapInt (unwrapNumber exponent)))))))

let numberLHS =
    PC.not_followed_by
    (PC.disj_list [scientificNotation; floatNt; integer; hexFloat; hexInteger])
    (PC.const (fun ch -> ch > ' ' && ch != '(' && ch != ')' && ch != '[' && ch != ']' && ch != ',' && ch != ';'
                            && ch != '\x27' && ch != '\x60' && ch != '\"' && ch != '\n'));;

(* Number - End *)

(* String - Start *)

let stringLiteralChar =
    PC.pack
        (PC.const (fun ch -> ch != '\\' && ch != '\"'))
        (fun (stringLC) -> match (stringLC) with
                            | _ -> String (list_to_string [stringLC]));;

let stringMetaChar =
    PC.pack
        (PC.disj_list [PC.word "\\\""; PC.word "\\\\"; PC.word_ci "\\t"; PC.word_ci "\\f"; PC.word "\\n"; PC.word "\\r"])
        (fun (stringList) -> match (list_to_string stringList) with
                                | "\\\\" -> String ("\\")
                                | "\\\"" -> String ("\"")
                                | "\\t" -> String ("\t")
                                | "\\f" -> String ("\x0c")
                                | "\\n" -> String ("\n")
                                | "\\r" -> String ("\r")
                                | _ -> raise PC.X_no_match);;

let stringHexChar =
    PC.pack
        (PC.caten (PC.word_ci "\\x") (PC.caten (PC.plus hexDigit) (PC.char ';')))
        (fun (backSlashX, (asciiList ,semiColon)) -> String (String.make 1 (char_of_int (int_of_string ("0x" ^ (list_to_string asciiList))))));;

let stringChar = PC.disj_list [stringHexChar; stringMetaChar; stringLiteralChar];;

let stringNt =
    let unwrapString x = match x with
                            | String wrappedString -> wrappedString
                            | _ -> raise PC.X_no_match in
    PC.pack
        (PC.caten (PC.char '\"' ) (PC.caten (PC.star stringChar) (PC.char '\"')))
        (fun (openQuote,(stringList,closeQuote)) -> String(String.concat "" (List.map unwrapString stringList)));;

(* String - End *)

(* Symbol - Start *)

let symbol =
    let punctuation = PC.disj_list [PC.char '!'; PC.char '$'; PC.char '^'; PC.char '*'; PC.char '-'; PC.char '_'; PC.char '='; PC.char '+'; PC.char '<'; PC.char '>'; PC.char '?'; PC.char '/'; PC.char ':'] in
    let symbolChar = PC.disj_list [PC.range '0' '9'; PC.range_ci 'a' 'z'; punctuation] in
    let getSymbol = (PC.plus symbolChar) in
    let symbolProtected =
        PC.not_followed_by
        getSymbol
        (PC.const (fun ch -> ch > ' ' && ch != '#' && ch != '(' && ch != ')' && ch != '[' && ch != ']' && ch != ',' && ch != ';'
                                && ch != '\x27' && ch != '\x60' && ch != '\"' && ch != '\n'))
        in
        PC.pack symbolProtected (fun (symbolList) -> Symbol (list_to_string (List.map lowercase_ascii symbolList)));;

(* Symbol - End *)

(* Sexpr - Start *)

let rec sexprLHS inputString =
    let lineComment =
        PC.pack
            (PC.caten (PC.char ';') (PC.caten (PC.star (PC.const (fun ch -> ch != '\n' && ch != '\x03'))) (PC.disj (PC.char '\n') (PC.char '\x03'))))
            (fun (_) -> Char (' '))
    in
    let sexprComment =
        PC.pack
            (PC.caten (PC.word "#;") (PC.delayed (fun () -> sexprLHS)))
            (fun (_) -> Char (' '))
    in
    let packed =
        PC.pack
        (PC.caten whitespaces_star (PC.caten (PC.star (PC.caten whitespaces_star (PC.disj lineComment sexprComment))) (PC.caten whitespaces_star (PC.caten (PC.disj_list [boolean; charLHS; numberLHS; threeDots; symbol; nil; listOfSexpr; dottedListOfSexpr; vectorOfSexpr; stringNt; quoted; quasiQuoted; unquoted; unquoteAndSpliced]) (PC.caten whitespaces_star (PC.caten (PC.star (PC.disj lineComment sexprComment)) whitespaces_star))))))
            (fun (leftSpaces, (starComment, (midSpaces1 ,(actualSexpr, (midSpaces2, (starLineComment2, rightSpaces)))))) -> actualSexpr)
    in
    packed inputString

(* Sexpr - End *)

(* List - Start *)

and listOfSexpr inputString1 =
    let packed =
        PC.pack
            (PC.disj
                (PC.caten (PC.char '\x28') (PC.caten (PC.star (PC.caten whitespaces_star (PC.delayed (fun () -> sexprLHS)))) (PC.caten whitespaces_star (PC.char '\x29'))))
                (PC.caten (PC.char '\x5b') (PC.caten (PC.star (PC.caten whitespaces_star (PC.delayed (fun () -> sexprLHS)))) (PC.caten whitespaces_star (PC.char '\x5d')))))
            (fun
                (lapren, (sexprList, spacesWithLparen)) ->
                List.fold_right (fun (spaceList, actualSexpr) acc -> Pair (actualSexpr, acc))
                sexprList Nil
            )
    in
    packed inputString1

(* List - End *)

(* DottedList - Start *)

and dottedListOfSexpr inputString2 =
    let packed =
        PC.pack
            (PC.disj
                (PC.caten (PC.char '\x28') (PC.caten (PC.plus (PC.caten whitespaces_star (PC.delayed (fun () -> sexprLHS)))) (PC.caten (PC.caten whitespaces_star (PC.char '.')) (PC.caten (PC.caten whitespaces_star sexprLHS) (PC.caten whitespaces_star (PC.char '\x29'))))))
                (PC.caten (PC.char '\x5b') (PC.caten (PC.plus (PC.caten whitespaces_star (PC.delayed (fun () -> sexprLHS)))) (PC.caten (PC.caten whitespaces_star (PC.char '.')) (PC.caten (PC.caten whitespaces_star sexprLHS) (PC.caten whitespaces_star (PC.char '\x5d')))))))
            (fun
                (lapren, (leftToPoint ,(point,( (additionalElementSpaces ,additionalElement ),rparen )) ) ) ->
                List.fold_right (fun (elementSpaces, actualElement) acc -> Pair (actualElement, acc))
                leftToPoint additionalElement
            )
            in
    packed inputString2

(* DottedList - End *)

(* Vector - Start *)

and vectorOfSexpr inputString3 =
    let packed =
        PC.pack
            (PC.pack
                (PC.caten hashtag (PC.caten (PC.char '\x28') (PC.caten (PC.star (PC.caten whitespaces_star (PC.delayed (fun () -> sexprLHS)))) (PC.caten whitespaces_star (PC.char '\x29')))))
                (fun
                    (hashTag,(lapren, (sexprList, spacesWithLparen))) ->
                    List.fold_right (fun (spaceList, actualSexpr) acc -> actualSexpr :: acc)
                    sexprList []
                ))
            (fun (gottenList) -> Vector (gottenList))
        in
    packed inputString3

(* Vector - End *)

(* Quoted - Start *)

and quoted inputString4 =
    let packed = PC.pack
        (PC.caten (PC.char '\x27') (PC.caten whitespaces_star (PC.delayed (fun () -> sexprLHS))))
        (fun (chupchik, (sapceList, sexpr)) -> Pair (Symbol ("quote"), Pair (sexpr, Nil))) in
    packed inputString4

(* Quoted - End *)

(* QuasiQuoted - Start *)

and quasiQuoted inputString5 =
    let packed = PC.pack
        (PC.caten (PC.char '\x60') (PC.caten whitespaces_star (PC.delayed (fun () -> sexprLHS))))
        (fun (chupchik, (sapceList, sexpr)) -> Pair (Symbol ("quasiquote"), Pair (sexpr, Nil))) in
    packed inputString5

(* QuasiQuoted - End *)

(* Unquoted - Start *)

and unquoted inputString6 =
    let packed = PC.pack
        (PC.caten (PC.char ',') (PC.caten whitespaces_star (PC.delayed (fun () -> sexprLHS))))
        (fun (chupchik, (sapceList, sexpr)) -> Pair (Symbol ("unquote"), Pair (sexpr, Nil))) in
    packed inputString6

(* Unquoted - End *)

(* UnquoteAndSpliced - Start *)

and unquoteAndSpliced inputString7 =
    let packed = PC.pack
        (PC.caten (PC.word ",@") (PC.caten whitespaces_star (PC.delayed (fun () -> sexprLHS))))
        (fun (chupchik, (sapceList, sexpr)) -> Pair (Symbol ("unquote-splicing"), Pair (sexpr, Nil))) in
    packed inputString7

(* UnquoteAndSpliced - End *)

(* Nil - Start *)

and nil inputString8 =
    let packed = PC.pack
        (PC.caten (PC.char '\x28') (PC.caten whitespaces_star (PC.char '\x29')))
        (fun (anything) -> Nil) in
    packed inputString8

(* Nil - End *)

(* threeDots - Start *)

and threeDots inputString10 =
    let anyChar =
        PC.star
            (
                PC.disj
                    (PC.const (fun ch -> ch >= ' ' && ch <= '~' && ch != '.'))
                    (PC.not_followed_by (PC.const (fun ch -> ch = '.')) (PC.const (fun ch -> ch = '.')))
            )
        in
    let packed =
        PC.pack
            (PC.caten anyChar (PC.word "..."))
            (fun (allChars, threeDotsSymbol) ->
                List.fold_left
                    (
                        fun (allChars, acc) loneChar -> match loneChar with
                                                        | '\x28' -> (allChars, '\x29' :: acc)
                                                        | '\x5b' -> (allChars, '\x5d' :: acc)
                                                        | '\x5d' -> (allChars, List.tl acc)
                                                        | '\x29' -> (allChars, List.tl acc)
                                                        | _ -> (allChars, acc)
                    )
                    (allChars, [])
                    allChars
            )
    in
    let ((input, fill), rest) = packed inputString10 in
    sexprLHS (List.append input fill);;

(* threeDots - End *)

(* General Parser - Start *)

let read_sexpr string =
    let (returnValue, rest) = (sexprLHS (string_to_list string)) in
    returnValue;;

let read_sexprs string =
    let (returnValue, rest) = ((PC.star sexprLHS) (string_to_list string)) in
    returnValue;;

(* General Parser - End *)

end;; (* struct Reader *)
