(* tag-parser.ml
 * A compiler from Scheme to CISC
 *
 * Programmer: Mayer Goldberg, 2018
 *)

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
  | Set' of expr' * expr'
  | Def' of expr' * expr'
  | Or' of expr' list
  | LambdaSimple' of string list * expr'
  | LambdaOpt' of string list * string * expr'
  | Applic' of expr' * (expr' list)
  | ApplicTP' of expr' * (expr' list);;

let rec expr'_eq e1 e2 = match e1, e2 with
  | Const' Void, Const' Void -> true
  | Const'(Sexpr s1), Const'(Sexpr s2) -> sexpr_eq s1 s2
  | Var'(VarFree v1), Var'(VarFree v2) -> String.equal v1 v2
  | Var'(VarParam (v1,mn1)), Var'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
  | Var'(VarBound (v1,mj1,mn1)), Var'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
  | If'(t1, th1, el1), If'(t2, th2, el2) -> (expr'_eq t1 t2) && (expr'_eq th1 th2) && (expr'_eq el1 el2)
  | (Seq'(l1), Seq'(l2)
  | Or'(l1), Or'(l2)) -> List.for_all2 expr'_eq l1 l2
  | (Set'(var1, val1), Set'(var2, val2)
  | Def'(var1, val1), Def'(var2, val2)) -> (expr'_eq var1 var2) && (expr'_eq val1 val2)
  | LambdaSimple'(vars1, body1), LambdaSimple'(vars2, body2) -> (List.for_all2 String.equal vars1 vars2) && (expr'_eq body1 body2)
  | LambdaOpt'(vars1, var1, body1), LambdaOpt'(vars2, var2, body2) -> (String.equal var1 var2) && (List.for_all2 String.equal vars1 vars2) && (expr'_eq body1 body2)
  | Applic'(e1, args1), Applic'(e2, args2)
  | ApplicTP'(e1, args1), ApplicTP'(e2, args2) -> (expr'_eq e1 e2) && (List.for_all2 expr'_eq args1 args2)
  | Box'(_), Box'(_) -> true
  | BoxGet'(_), BoxGet'(_) -> true
  | BoxSet'(_, v1), BoxSet'(_, v2) -> expr'_eq v1 v2
  | _ -> false;;


exception X_syntax_error;;

let environment = ref [];;

module type SEMANTICS = sig
  val run_semantics : expr -> expr'
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
end;;

module Semantics : SEMANTICS = struct

let searchInEnvironment varibleName =
  let varToReturn = ref [(VarFree (varibleName))] in
  begin
    for i = 0 to (List.length !environment - 1) do
      for j = 0 to (List.length (List.nth !environment i) - 1) do
        if (List.nth (List.nth !environment i) j) = varibleName
          then
            (if i = 0
              then varToReturn := (!varToReturn) @ [VarParam (varibleName, j)]
              else varToReturn := (!varToReturn) @ [VarBound (varibleName, i-1, j)])
      done
    done;
  if List.length (!varToReturn) = 1
    then List.nth (!varToReturn) 0
    else List.nth (!varToReturn) 1
  end;;

let rec annotate_lexical_addresses e = match e with
  | Const (x) -> Const' (x)
  | Var (varibleName) -> Var' (searchInEnvironment varibleName)
  | If (test, dit, dif) -> If' (annotate_lexical_addresses test, annotate_lexical_addresses dit, annotate_lexical_addresses dif)
  | Seq (exprList) -> Seq' (List.map annotate_lexical_addresses exprList)
  | Set (varibleName, newValue) -> Set' (annotate_lexical_addresses varibleName, annotate_lexical_addresses newValue)
  | Def (varibleName, varibleValue) -> Def' (annotate_lexical_addresses varibleName, annotate_lexical_addresses varibleValue)
  | Or (exprList) -> Or' (List.map annotate_lexical_addresses exprList)
  | LambdaSimple (argList, expr) ->
      begin
        environment := argList :: !environment;
        let lambdaSimpleToReturn = LambdaSimple' (argList, annotate_lexical_addresses expr)
        in
          begin
            environment := List.tl !environment;
            lambdaSimpleToReturn
          end
      end
  | LambdaOpt (argList, additionalArg, expr) ->
      begin
        environment := (argList @ [additionalArg]) :: !environment;
        let lambdaOptToReturn = LambdaOpt' (argList, additionalArg, annotate_lexical_addresses expr)
        in
          begin
            environment := List.tl !environment;
            lambdaOptToReturn
          end
      end
  | Applic (procedureName, argList) -> Applic' (annotate_lexical_addresses procedureName, List.map annotate_lexical_addresses argList);;

let rec annotate_tail_calls_helper e flag = match e with
  | If' (test, dit, dif) -> if flag = true
                            then If' (test, annotate_tail_calls_helper dit true, annotate_tail_calls_helper dif true)
                            else If' (test, annotate_tail_calls_helper dit false, annotate_tail_calls_helper dif false)
  | Seq' (exprList) -> if flag = true
                        then Seq' (
                                    List.map
                                    (fun element -> if element = List.hd (List.rev exprList)
                                                    then annotate_tail_calls_helper element true
                                                    else annotate_tail_calls_helper element false)
                                    exprList
                                  )
                        else Seq' (
                                    List.map
                                    (fun element -> if element = List.hd (List.rev exprList)
                                                    then annotate_tail_calls_helper element false
                                                    else annotate_tail_calls_helper element false)
                                    exprList
                                  )
  | Set' (varibleName, newValue) -> Set' (varibleName, annotate_tail_calls_helper newValue false)
  | Def' (varibleName, varibleValue) -> Def' (varibleName, annotate_tail_calls_helper varibleValue false)
  | Or' (exprList) -> if flag = true
                        then Or' (
                                    List.map
                                    (fun element -> if element = List.hd (List.rev exprList)
                                                    then annotate_tail_calls_helper element true
                                                    else annotate_tail_calls_helper element false)
                                    exprList
                                  )
                        else Or' (
                                    List.map
                                    (fun element -> if element = List.hd (List.rev exprList)
                                                    then annotate_tail_calls_helper element false
                                                    else annotate_tail_calls_helper element false)
                                    exprList
                                  )
  | LambdaSimple' (argList, expr) -> LambdaSimple' (argList, annotate_tail_calls_helper expr true)
  | LambdaOpt' (argList, additionalArg, expr) -> LambdaOpt' (argList, additionalArg, annotate_tail_calls_helper expr true)
  | Applic' (procedureName, argList) -> if flag = true
                                          then ApplicTP' (
                                                            annotate_tail_calls procedureName,
                                                            List.map
                                                            (fun arg -> annotate_tail_calls arg)
                                                            argList
                                                          )
                                          else Applic' (
                                                          annotate_tail_calls procedureName,
                                                          List.map
                                                          (fun arg -> annotate_tail_calls arg)
                                                          argList
                                                        )
  | x -> x

and annotate_tail_calls e = annotate_tail_calls_helper e false;;

let rec isThereRead arg expr = match expr with
  | Const' (x) -> []
  | Var' (varibleType) -> (match varibleType with
      | VarFree (varibleName) -> []
      | VarParam (varibleName, minor) -> if varibleName = arg then [Var' (VarFree (arg))] else []
      | VarBound (varibleName, major, minor) -> if varibleName = arg then [Var' (VarFree (arg))] else [])
  | If' (test, dit, dif) -> (isThereRead arg test) @ (isThereRead arg dit) @ (isThereRead arg dif)
  | Seq' (exprList) -> List.fold_left
                        (fun acc element -> acc @ (isThereRead arg element))
                        []
                        exprList
  | Set' (varibleName, newValue) -> isThereRead arg newValue
  | Def' (varibleName, varibleValue) -> isThereRead arg varibleValue
  | Or' (exprList) -> List.fold_left
                        (fun acc element -> acc @ (isThereRead arg element))
                        []
                        exprList
  | LambdaSimple' (argList, innerExpr) -> if List.mem arg argList
                                            then []
                                            else (if (isThereRead arg innerExpr) <> [] then [expr] else [])
  | LambdaOpt' (argList, additionalArg, innerExpr) -> if List.mem arg (argList @ [additionalArg])
                                                        then []
                                                        else (if (isThereRead arg innerExpr) <> [] then [expr] else [])
  | Applic' (procedureName, argList) -> (isThereRead arg procedureName)
                                        @
                                        (List.fold_left
                                          (fun acc element -> acc @ (isThereRead arg element))
                                          []
                                          argList)
  | ApplicTP' (procedureName, argList) -> (isThereRead arg procedureName)
                                          @
                                          (List.fold_left
                                            (fun acc element -> acc @ (isThereRead arg element))
                                            []
                                            argList)
  | x -> [];;

let rec isThereWrite arg expr = match expr with
  | Const' (x) -> []
  | Var' (varibleType) -> []
  | If' (test, dit, dif) -> (isThereWrite arg test) @ (isThereWrite arg dit) @ (isThereWrite arg dif)
  | Seq' (exprList) -> List.fold_left
                        (fun acc element -> acc @ (isThereWrite arg element))
                        []
                        exprList
  | Set' (Var' (varibleType), newValue) -> (match varibleType with
    | VarFree (varibleName) -> isThereWrite arg newValue
    | VarParam (varibleName, minor) -> if varibleName = arg then ([Var' (VarFree (arg))] @ (isThereWrite arg newValue)) else isThereWrite arg newValue
    | VarBound (varibleName, major, minor) -> if varibleName = arg then ([Var' (VarFree (arg))] @ (isThereWrite arg newValue)) else isThereWrite arg newValue)
  | Set' (x, y) -> raise X_syntax_error
  | Def' (varibleName, varibleValue) -> isThereWrite arg varibleValue
  | Or' (exprList) -> List.fold_left
                        (fun acc element -> acc @ (isThereWrite arg element))
                        []
                        exprList
  | LambdaSimple' (argList, innerExpr) -> if List.mem arg argList
                                            then []
                                            else (if (isThereWrite arg innerExpr) <> [] then [expr] else [])
  | LambdaOpt' (argList, additionalArg, innerExpr) -> if List.mem arg argList
                                                        then []
                                                        else (if (isThereWrite arg innerExpr) <> [] then [expr] else [])
  | Applic' (procedureName, argList) -> (isThereWrite arg procedureName)
                                        @
                                        (List.fold_left
                                          (fun acc element -> acc @ (isThereWrite arg element))
                                          []
                                          argList)
  | ApplicTP' (procedureName, argList) -> (isThereWrite arg procedureName)
                                          @
                                          (List.fold_left
                                            (fun acc element -> acc @ (isThereWrite arg element))
                                            []
                                            argList)
  | x -> [];;

let isWrapNeeded arg expr =
  let readList = isThereRead arg expr in
  let readListThreshold = if List.mem (Var' (VarFree (arg))) readList then 0 else 1 in
  let writeList =  isThereWrite arg expr in
  let writeListThreshold = if List.mem (Var' (VarFree (arg))) writeList then 0 else 1 in
  let readListFiltered = List.filter (fun element -> element <> Var' (VarFree (arg))) readList in
  let writeListFiltered = List.filter (fun element -> element <> Var' (VarFree (arg))) writeList in
  let readListFilteredLength = List.length readListFiltered in
  let writeListFilteredLength = List.length writeListFiltered in
  if readListFilteredLength > readListThreshold && writeListFilteredLength >= writeListThreshold
    then true
  else if readListFilteredLength >= readListThreshold && writeListFilteredLength > writeListThreshold
    then true
  else if readListFilteredLength = readListThreshold && writeListFilteredLength = writeListThreshold && readListFiltered <> writeListFiltered
      then true
  else false;;

let rec box_set_wrapper e varibleListToWrap = match e with
  | Const' (x) -> Const' (x)
  | Var' (varibleType) -> (match varibleType with
      | VarFree (varibleName) -> Var' (VarFree (varibleName))
      | VarParam (varibleName, minor) -> if List.mem varibleName varibleListToWrap
                                          then BoxGet' (VarParam (varibleName, minor))
                                          else Var' (VarParam (varibleName, minor))
      | VarBound (varibleName, major, minor) ->  if List.mem varibleName varibleListToWrap
                                                  then BoxGet' (VarBound (varibleName, major, minor))
                                                  else Var' (VarBound (varibleName, major, minor)))
  | If' (test, dit, dif) -> If' (box_set_wrapper test varibleListToWrap, box_set_wrapper dit varibleListToWrap, box_set_wrapper dif varibleListToWrap)
  | Seq' (exprList) -> Seq' (
                              List.map
                                (fun element -> box_set_wrapper element varibleListToWrap)
                                exprList
                            )
  | Set' (Var' (varibleType), newValue) -> (match varibleType with
    | VarFree (varibleName) -> Set' (Var' (varibleType),  box_set_wrapper newValue varibleListToWrap)
    | VarParam (varibleName, minor) -> if List.mem varibleName varibleListToWrap
                                        then BoxSet' (VarParam (varibleName, minor), box_set_wrapper newValue varibleListToWrap)
                                        else Set' (Var' varibleType, box_set_wrapper newValue varibleListToWrap)
    | VarBound (varibleName, major, minor) -> if List.mem varibleName varibleListToWrap
                                                then BoxSet' (VarBound (varibleName, major, minor), box_set_wrapper newValue varibleListToWrap)
                                                else Set' (Var' varibleType, box_set_wrapper newValue varibleListToWrap))
  | Set' (x, y) -> raise X_syntax_error
  | Def' (varibleName, varibleValue) -> Def' (varibleName, box_set_wrapper varibleValue varibleListToWrap)
  | Or' (exprList) -> Or' (
                            List.map
                              (fun element -> box_set_wrapper element varibleListToWrap)
                              exprList
                          )
  | LambdaSimple' (argList, expr) ->
      let serachInList argToFind =
        let indexToReturn = ref (-1) in
        begin
          (for i = 0 to (List.length argList - 1) do (if (List.nth argList i) = argToFind then indexToReturn := i) done);
          !indexToReturn
        end in
      let isWrapNeededArgs = (List.filter (fun element -> isWrapNeeded element expr) argList) in
      let argsToWrap = (List.filter (fun oldArg -> not (List.mem oldArg argList)) varibleListToWrap) @ isWrapNeededArgs in
      let newExpr = box_set_wrapper expr argsToWrap in
      let newBodyPrefix = List.map (fun argToWrap -> (Set' (Var' (VarParam (argToWrap, serachInList argToWrap)), Box' (VarParam (argToWrap, serachInList argToWrap))))) isWrapNeededArgs in
      if List.length newBodyPrefix = 0
          then LambdaSimple' (argList, newExpr)
          else
            (match newExpr with
              | Seq' (exprList) -> LambdaSimple' (argList, Seq' (newBodyPrefix @ [Seq' (exprList)]))
              | x -> LambdaSimple' (argList, Seq' (newBodyPrefix @ [x])))
  | LambdaOpt' (argList, additionalArg, expr) ->
      let argListWithAdditional = argList @ [additionalArg] in
      let serachInList argToFind =
        let indexToReturn = ref (-1) in
        begin
          (for i = 0 to (List.length argListWithAdditional - 1) do (if ((List.nth argListWithAdditional i) = argToFind) then indexToReturn := i) done);
          !indexToReturn
        end in
      let isWrapNeededArgs = (List.filter (fun element -> isWrapNeeded element expr) argListWithAdditional) in
      let argsToWrap = (List.filter (fun oldArg -> not (List.mem oldArg argListWithAdditional)) varibleListToWrap) @ isWrapNeededArgs in
      let newExpr = box_set_wrapper expr argsToWrap in
      let newBodyPrefix = List.map (fun argToWrap -> Set' (Var' (VarParam (argToWrap, serachInList argToWrap)), Box' (VarParam (argToWrap, serachInList argToWrap)))) isWrapNeededArgs in
      if List.length newBodyPrefix = 0
        then LambdaOpt' (argList, additionalArg, newExpr)
        else
          (match newExpr with
            | Seq' (exprList) -> LambdaOpt' (argList, additionalArg, Seq' (newBodyPrefix @ [Seq' (exprList)]))
            | x -> LambdaOpt' (argList, additionalArg, Seq' (newBodyPrefix @ [x])))
  | Applic' (procedureName, argList) -> Applic' (
                                                  box_set_wrapper procedureName varibleListToWrap,
                                                  List.map
                                                    (fun element -> box_set_wrapper element varibleListToWrap)
                                                    argList
                                                )
  | ApplicTP' (procedureName, argList) -> ApplicTP' (
                                                      box_set_wrapper procedureName varibleListToWrap,
                                                      List.map
                                                        (fun element -> box_set_wrapper element varibleListToWrap)
                                                        argList
                                                    )
  | _ -> raise X_syntax_error;;

let box_set e = box_set_wrapper e [];;

let run_semantics expr =
  box_set
    (annotate_tail_calls
       (annotate_lexical_addresses expr));;

end;; (* struct Semantics *)
