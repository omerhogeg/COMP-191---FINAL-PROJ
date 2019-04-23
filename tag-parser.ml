(* tag-parser.ml
 * A compiler from Scheme to CISC
 *
 * Programmer: Mayer Goldberg, 2018
 *)

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
  val tag_parse_expression : sexpr -> expr
  val tag_parse_expressions : sexpr list -> expr list
end;; (* signature TAG_PARSER *)

module Tag_Parser : TAG_PARSER = struct

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "unquote";
   "unquote-splicing"];;

let rec tag_parse sexpr = match sexpr with
  | Bool (x) -> Const (Sexpr (Bool (x)))
  | Number (x) -> Const (Sexpr (Number (x)))
  | Char (x) -> Const (Sexpr (Char (x)))
  | String (x) -> Const (Sexpr (String (x)))
  | Symbol (x) ->
      if (List.mem x reserved_word_list) then raise X_syntax_error else Var (x)
  | Nil -> Const (Void)
  | Pair (Symbol ("quote"), Pair (x, Nil)) -> Const (Sexpr (x))
  | Pair (Symbol ("if"), Pair (test, Pair (dit, Pair (dif, Nil)))) -> If (tag_parse test, tag_parse dit, tag_parse dif)
  | Pair (Symbol ("if"), Pair (test, Pair (dit, Nil))) -> If (tag_parse test, tag_parse dit, Const (Void))
  | Pair (Symbol ("lambda"), Pair (Symbol varible, sexprs)) -> LambdaOpt ([], varible, sexprsToExprListToSeq sexprs) (* Lambda Type 3 *)
  | Pair (Symbol ("lambda"), Pair (bindings, Nil)) -> raise X_syntax_error
  | Pair (Symbol ("lambda"), Pair (bindings, sexprs)) ->
      (
        try LambdaSimple (lambdaSimpleBindingsToStringList bindings, sexprsToExprListToSeq sexprs) (* Lambda Type 1 *)
        with X_syntax_error -> buildLabmdaOpt (bindings, sexprs) (* Lambda Type 2 *)
      )
  | Pair (Symbol "or", args) -> sexprsToExprListToOr args
  | Pair (Symbol "define", Pair (Symbol (varibleName), Pair (varibleValue, Nil))) -> Def (tag_parse (Symbol (varibleName)), tag_parse (varibleValue)) (* Define - Regular *)
  | Pair (Symbol "define", Pair (Pair (Symbol (varibleName), arguments), sexprs)) -> tag_parse (Pair (Symbol "define", Pair (Symbol (varibleName), Pair (Pair (Symbol "lambda", Pair (arguments, sexprs)), Nil)))) (* MIT-Define *)
  | Pair (Symbol "set!", Pair (Symbol varibleName, Pair (newValue, Nil))) -> Set (tag_parse (Symbol (varibleName)), tag_parse (newValue))
  | Pair (Symbol "begin", Nil) -> Const (Void) (* Begin - Empty *)
  | Pair (Symbol "begin", Pair (singleSexpr, Nil)) -> tag_parse singleSexpr (* Begin - Single Expression *)
  | Pair (Symbol "begin", Pair (firstSexpr, restSexprs)) -> exprListToSeq ((tag_parse firstSexpr) :: (sexprsToExprList restSexprs)) (* Begin - Multiple Expressions *)
  | Pair (Symbol "let", Pair (Nil, sexprs)) -> Applic (LambdaSimple ([], sexprsToExprListToSeq sexprs), []) (* Let - No Bindings *)
  | Pair (Symbol "let", Pair (bindings, sexprs)) -> Applic (LambdaSimple (getVariblesForLet bindings, sexprsToExprListToSeq sexprs), getArgumentsForLet bindings) (* Let - With Bindings *)
  | Pair (Symbol "let*", Pair (Nil, sexprs)) -> tag_parse (Pair (Symbol "let", Pair (Nil, sexprs))) (* Let* - No Bindings *)
  | Pair (Symbol "let*", Pair (Pair (singleBinding, Nil), sexprs)) -> tag_parse (Pair (Symbol "let", Pair (Pair (singleBinding, Nil), sexprs))) (* Let* - Single Binding *)
  | Pair (Symbol "let*", Pair (Pair (firstBinding, restBindings), sexprs)) -> tag_parse (letStarToLet sexpr) (* Let* - Multiple Bindings *)
  | Pair (Symbol "letrec", Pair (bindings, sexprs)) -> Applic (LambdaSimple (getVariblesForLet bindings, getExprsForLetrecToSeq (bindings, sexprs)), createWhateverForLetrec bindings)
  | Pair (Symbol "and", Nil) -> Const (Sexpr (Bool (true))) (* And - Empty *)
  | Pair (Symbol "and", Pair (singleSexpr, Nil)) -> tag_parse singleSexpr (* And - Single Expression *)
  | Pair (Symbol "and", Pair (firstSexpr, restSexprs)) -> andToIf (firstSexpr, restSexprs) (* And - Multiple Expressions *)
  | Pair (Symbol "cond", Nil) -> Const (Void) (* Cond - Empty ??? *)
  | Pair (Symbol "cond", Pair (firstRib, restRibs)) -> condToIf (firstRib,restRibs)
  | Pair (Pair (Symbol "lambda", lambdaSpecifications), arguments) -> Applic (tag_parse (Pair (Symbol "lambda", lambdaSpecifications)), sexprsToExprList arguments)
  | Pair (Symbol "quasiquote", Pair (sexpr, Nil)) -> handleQuasiquote sexpr
  | Pair (procedure, args) -> Applic (tag_parse procedure, sexprsToExprList args)
  | _ -> raise X_syntax_error

and sexprsToExprList sexprs = match sexprs with
  | Pair (sexpr, rest) -> (tag_parse sexpr) :: (sexprsToExprList rest)
  | Nil -> []
  | _ -> raise X_syntax_error

and sexprsToExprListToSeq sexprs = match (sexprsToExprList sexprs) with
  | [] -> Const (Void)
  | [singleElement] -> singleElement
  | _ -> Seq (sexprsToExprList sexprs)

and sexprsToExprListToOr sexprs = match (sexprsToExprList sexprs) with
  | [] -> Const(Sexpr(Bool(false)))
  | [singleElement] -> singleElement
  | _ -> Or (sexprsToExprList sexprs)

and exprListToSeq exprs = match exprs with
  | [] -> Const (Void)
  | [singleElement] -> singleElement
  | _ -> Seq (exprs)

and lambdaSimpleBindingsToStringList bindings = match bindings with
  | Pair (Symbol varible, rest) ->
      if (List.mem varible (lambdaSimpleBindingsToStringList rest)) then raise X_syntax_error else (varible :: (lambdaSimpleBindingsToStringList rest))
  | Nil -> []
  | _ -> raise X_syntax_error

and buildLabmdaOpt (bindings, sexprs) =
  let rec lambdaOptBindingsToStringList bindings = match bindings with
    | Pair (Symbol varible, rest) ->
        if (List.mem varible (lambdaOptBindingsToStringList rest)) then raise X_syntax_error else (varible :: (lambdaOptBindingsToStringList rest))
    | Symbol lastVarible -> [lastVarible]
    | _ -> raise X_syntax_error
  in
  let bindingsToList = lambdaOptBindingsToStringList bindings in
  let (varibles, additionalVarible) = ((List.rev (List.tl (List.rev bindingsToList)), List.hd (List.rev (bindingsToList)))) in
  LambdaOpt (varibles, additionalVarible, sexprsToExprListToSeq sexprs)

and getVariblesForLet bindings = match bindings with
  | Pair (Pair (Symbol (firstVarible), firstVaribleValue), restVaribles) ->
      if (List.mem firstVarible (getVariblesForLet restVaribles)) then raise X_syntax_error else (firstVarible :: (getVariblesForLet restVaribles))
  | Nil -> []
  | _ -> raise X_syntax_error

and getArgumentsForLet bindings = match bindings with
  | Pair (Pair (firstVarible, Pair(actualfirstVaribleValue, endOfPair)), restVaribles) -> (tag_parse actualfirstVaribleValue) :: (getArgumentsForLet restVaribles)
  | Nil -> []
  | _ -> raise X_syntax_error

and letStarToLet sexpr =  match sexpr with
  | Pair (Symbol "let*", Pair (Pair (singleBinding, Nil), sexprs)) -> Pair (Symbol "let", Pair (Pair (singleBinding, Nil), sexprs))
  | Pair (Symbol "let*", Pair (Pair (firstBinding, restBindings), sexprs)) -> Pair (Symbol "let", Pair (Pair (firstBinding, Nil), Pair (letStarToLet (Pair (Symbol "let*", Pair (restBindings, sexprs))), Nil)))
  | _ -> raise X_syntax_error

and getExprsForLetrec (bindings, sexprs) =
  List.fold_right2
    (fun currentVarible currentArgument acc -> Set (tag_parse (Symbol (currentVarible)), currentArgument) :: acc)
    (getVariblesForLet bindings)
    (getArgumentsForLet bindings)
    (sexprsToExprList sexprs)

and getExprsForLetrecToSeq (bindings, sexprs) = match (getExprsForLetrec (bindings, sexprs)) with
  | [] -> Const (Void)
  | [singleElement] -> singleElement
  | _ -> Seq (getExprsForLetrec (bindings, sexprs))

and createWhateverForLetrec bindings =
  List.fold_right
  (fun currentVarible acc -> tag_parse (Pair (Symbol "quote", Pair (Symbol "whatever", Nil))) :: acc)
  (getVariblesForLet bindings)
  []

and andToIf (firstSexpr, restSexprs) =
  If
  (
    tag_parse firstSexpr,
    tag_parse (Pair (Symbol "and", restSexprs)),
    Const (Sexpr (Bool (false)))
  )

and condToIf (firstRib, restRibs) =
  match firstRib with
    | Pair (Symbol "else", sexprs) -> if (restRibs = Nil) then sexprsToExprListToSeq sexprs else raise X_syntax_error
    | Pair (test, Pair (Symbol "=>", Pair (exprf, Nil))) ->
        if (restRibs = Nil)
        then
          tag_parse
            (
              Pair
              (
                Symbol "let",
                Pair
                (
                  Pair
                  (
                    Pair
                    (
                      Symbol "value",
                      Pair (test, Nil)
                    ),
                    Pair
                    (
                      Pair
                      (
                        Symbol "f",
                        Pair
                        (
                          Pair
                          (
                            Symbol "lambda",
                            Pair
                            (
                              Nil,
                              Pair (exprf, Nil)
                            )
                          ),
                          Nil
                        )
                      ),
                      Nil
                    )
                  ),
                  Pair
                  (
                    Pair
                    (Symbol "if",
                      Pair
                      (
                        Symbol "value",
                        Pair
                        (
                          Pair
                          (
                            Pair (Symbol "f", Nil),
                            Pair (Symbol "value", Nil)
                          ),
                          Nil
                        )
                      )
                    ),
                    Nil
                  )
                )
              )
            )
        else
        tag_parse
        (
          Pair
          (
            Symbol "let",
            Pair
            (
              Pair
              (
                Pair
                (
                  Symbol "value",
                  Pair (test, Nil)
                ),
                Pair
                (
                  Pair
                  (
                    Symbol "f",
                    Pair
                    (
                      Pair
                      (
                        Symbol "lambda",
                        Pair
                        (
                          Nil,
                          Pair (exprf, Nil)
                        )
                      ),
                      Nil
                    )
                  ),
                  Pair
                  (
                    Pair
                    (
                      Symbol "rest",
                      Pair
                      (
                        Pair
                        (
                          Symbol "lambda",
                          Pair
                          (
                            Nil,
                            Pair
                            (
                              Pair
                              (
                                Symbol "cond",
                                restRibs
                              ),
                              Nil
                            )
                          )
                        ),
                        Nil
                      )
                    ),
                    Nil
                  )
                )
              ),
              Pair
              (
                Pair
                (
                  Symbol "if",
                  Pair
                  (
                    Symbol "value",
                    Pair
                    (
                      Pair
                      (
                        Pair (Symbol "f", Nil),
                        Pair (Symbol "value", Nil)
                      ),
                      Pair
                      (
                        Pair
                        (
                          Symbol "rest",
                          Nil
                        ),
                        Nil
                      )
                    )
                  )
                ),
                Nil
              )
            )
          )
        )
    | Pair (test, sexprs) -> If (tag_parse test, sexprsToExprListToSeq sexprs, tag_parse (Pair (Symbol "cond", restRibs)))
    | _ -> raise X_syntax_error

and handleQuasiquote sexpr = match sexpr with
  | Pair (Symbol "unquote", Pair (element, Nil)) -> tag_parse element
  | Pair (Symbol "unquote-splicing", Pair (element, Nil)) -> raise X_syntax_error
  | Pair (Pair (Symbol "unquote-splicing", Pair (firstElement, Nil)), restElements) ->
      Applic
        (
          Var ("append"),
          [
            tag_parse firstElement;
            handleQuasiquote restElements
          ]
        )
  | Pair (firstElement, Pair (Symbol "unquote-splicing", Pair (currentElement, Nil))) ->
      Applic
      (
        Var ("cons"),
        [
          handleQuasiquote firstElement;
          tag_parse currentElement
        ]
      )
  | Pair (firstElement, Pair (Pair (Symbol "unquote-splicing", restElements), Nil)) ->
      Applic
        (
          Var ("cons"),
          [
            handleQuasiquote firstElement;
            handleQuasiquote (Pair (Pair (Symbol "unquote-splicing", restElements), Nil))
          ]
        )
  | Vector (listInVector) ->
      Applic
        (
          Var ("vector"),
          List.map (fun currentElement ->  tag_parse (Pair (Symbol "quasiquote", Pair (currentElement, Nil)))) listInVector
        )
  | Pair (firstElement, restElements) ->
      Applic
        (
          Var ("cons"),
          [
            handleQuasiquote firstElement;
            handleQuasiquote restElements
          ]
        )
  | x -> Const (Sexpr (x))

let tag_parse_expression sexpr = tag_parse sexpr;;

let tag_parse_expressions sexpr = List.map tag_parse_expression sexpr;;


end;; (* struct Tag_Parser *)
