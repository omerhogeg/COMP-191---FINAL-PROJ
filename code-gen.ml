#use "semantic-analyser.ml";;

module type CODE_GEN = sig
  val make_consts_tbl : expr' list -> (constant * (int * string)) list
  val make_fvars_tbl : expr' list -> (string * int) list
  val generate : (constant * (int * string)) list -> (string * int) list -> expr' -> int -> string
end;;

module Code_Gen : CODE_GEN = struct

let sexprListForConstTable = ref [Void; Sexpr (Nil); Sexpr (Bool (false)); Sexpr (Bool (true))];;
let sexprListForConstTableIncludingSubs = ref [Void; Sexpr (Nil); Sexpr (Bool (false)); Sexpr (Bool (true))];;
let currentAddress = ref 6;;
let tripleListForConstTable =
  ref [
        (Void, (0, "MAKE_VOID"));
        (Sexpr (Nil), (1, "MAKE_NIL"));
        (Sexpr (Bool (false)), (2, "MAKE_BOOL(0)"));
        (Sexpr (Bool (true)), (4, "MAKE_BOOL(1)"))
  ];;

let varFreeForFVarTable =
  ref [
    "boolean?"; "float?"; "integer?"; "pair?"; "null?"; "char?"; "vector?"; "string?";
    "procedure?"; "symbol?"; "string-length"; "string-ref"; "string-set!"; "make-string";
    "vector-length"; "vector-ref"; "vector-set!"; "make-vector"; "symbol->string";
    "char->integer"; "integer->char"; "eq?"; "+"; "*"; "-"; "/"; "<"; "="; "car";
    "cdr"; "set-car!"; "set-cdr!"; "cons"; "apply"
  ];;
let index = ref 0;;
let varFreeTupleForFVarTable = ref [];;

let counterOfOr = ref (-1);;
let counterOfIf = ref (-1);;
let counterOfLambdaSimple = ref (-1);;
let counterOfLambdaOpt = ref (-2);;
let counterOfApplic = ref (-1);;
let counterOfApplicTP = ref (-2);;

let temp = ref [];;
let tempCharList = ref [];;

let rec scanSexprForConst sexpr = match sexpr with
  | Bool (boolValue) -> sexprListForConstTable := !sexprListForConstTable
  | Nil -> sexprListForConstTable := !sexprListForConstTable
  | _ ->
      begin
        if List.mem (Sexpr (sexpr)) !sexprListForConstTable
          then sexprListForConstTable := !sexprListForConstTable
          else sexprListForConstTable := !sexprListForConstTable @ [Sexpr (sexpr)]
      end;;

let rec scanAstForConst ast = match ast with
  | Const' (constType) ->

      (match constType with
        | Sexpr (sexprType) -> scanSexprForConst sexprType
        | Void -> sexprListForConstTable := !sexprListForConstTable
      )
  | BoxSet' (varArg, exprArg) -> scanAstForConst exprArg
  | If' (test, dit, dif) ->
      begin
        scanAstForConst test;
        scanAstForConst dit;
        scanAstForConst dif
      end
  | Seq' (exprList) -> List.iter (fun element -> scanAstForConst element) exprList
  | Set' (varible, value) -> scanAstForConst value
  | Def' (varible, value) -> scanAstForConst value
  | Or' (exprList) -> List.iter (fun element -> scanAstForConst element) exprList
  | LambdaSimple' (args, body) -> scanAstForConst body
  | LambdaOpt' (args, additionalArg, body) -> scanAstForConst body
  | Applic' (proc, exprList) ->
      begin
        scanAstForConst proc;
        List.iter (fun element -> scanAstForConst element) exprList
      end
  | ApplicTP' (proc, exprList) ->
      begin
        scanAstForConst proc;
        List.iter (fun element -> scanAstForConst element) exprList
      end
  | _ -> sexprListForConstTable := !sexprListForConstTable;;

let rec makeSubConstant constantElement = match constantElement with
  | Sexpr (Symbol (stringValue)) ->
      begin
        sexprListForConstTableIncludingSubs := !sexprListForConstTableIncludingSubs @ [Sexpr (String (stringValue))];
        sexprListForConstTableIncludingSubs := !sexprListForConstTableIncludingSubs @ [constantElement];
      end
  | Sexpr (Pair (firstSexpr, secondSexpr)) -> begin
                                                makeSubConstant (Sexpr (firstSexpr));
                                                makeSubConstant (Sexpr (secondSexpr));
                                                if List.mem constantElement !sexprListForConstTableIncludingSubs
                                                  then sexprListForConstTableIncludingSubs := !sexprListForConstTableIncludingSubs
                                                  else sexprListForConstTableIncludingSubs := !sexprListForConstTableIncludingSubs @ [constantElement];
                                              end
  | Sexpr (Vector (sexprList)) ->
      begin
        List.iter
          (fun element -> makeSubConstant (Sexpr (element)))
          sexprList;
        if List.mem constantElement !sexprListForConstTableIncludingSubs
          then sexprListForConstTableIncludingSubs := !sexprListForConstTableIncludingSubs
          else sexprListForConstTableIncludingSubs := !sexprListForConstTableIncludingSubs @ [constantElement];
      end
  | x ->
      if List.mem x !sexprListForConstTableIncludingSubs
        then sexprListForConstTableIncludingSubs := !sexprListForConstTableIncludingSubs
        else sexprListForConstTableIncludingSubs := !sexprListForConstTableIncludingSubs @ [x];;

let searchAddressForMakeTriple sexprToSearch =
  let getConstant (c, (a, s)) = c in
  let getAddress (c, (a, s)) = a in
  let found = ref [] in
  begin
    for i = 0 to (List.length !tripleListForConstTable - 1) do
      if getConstant (List.nth !tripleListForConstTable i) = sexprToSearch
        then
          found := !found @ [getAddress (List.nth !tripleListForConstTable i)]
    done;
    List.nth !found 0
  end;;

let makeTriple constantElement = match constantElement with
  | Sexpr (Number (numberValue)) ->
      (match numberValue with
        | Int (intValue) ->
            begin
              currentAddress := !currentAddress + 9;
              tripleListForConstTable := !tripleListForConstTable @ [(constantElement, (!currentAddress - 9, "MAKE_LITERAL_INT(" ^ (string_of_int intValue) ^ ")"))]
            end
        | Float (floatValue) ->
            begin
              currentAddress := !currentAddress + 9;
              tripleListForConstTable := !tripleListForConstTable @ [(constantElement, (!currentAddress - 9, "MAKE_LITERAL_FLOAT(" ^ (string_of_float floatValue) ^ ")"))]
            end
      )
  | Sexpr (Char (charValue)) ->
      begin
        currentAddress := !currentAddress + 2;
        (match charValue with
          | '\n' -> tripleListForConstTable := !tripleListForConstTable @ [(constantElement, (!currentAddress - 2, "MAKE_LITERAL_CHAR(CHAR_NEWLINE)"))]
          | '\r' -> tripleListForConstTable := !tripleListForConstTable @ [(constantElement, (!currentAddress - 2, "MAKE_LITERAL_CHAR(CHAR_RETURN)"))]
          | '\t' -> tripleListForConstTable := !tripleListForConstTable @ [(constantElement, (!currentAddress - 2, "MAKE_LITERAL_CHAR(CHAR_TAB)"))]
          | '\x0c' -> tripleListForConstTable := !tripleListForConstTable @ [(constantElement, (!currentAddress - 2, "MAKE_LITERAL_CHAR(CHAR_PAGE)"))]
          | ' ' -> tripleListForConstTable := !tripleListForConstTable @ [(constantElement, (!currentAddress - 2, "MAKE_LITERAL_CHAR(CHAR_SPACE)"))]
          | '\x00' -> tripleListForConstTable := !tripleListForConstTable @ [(constantElement, (!currentAddress - 2, "MAKE_LITERAL_CHAR(CHAR_NUL)"))]
          | '\x27' -> tripleListForConstTable := !tripleListForConstTable @ [(constantElement, (!currentAddress - 2, "MAKE_LITERAL_CHAR(39)"))]
          | _ -> tripleListForConstTable := !tripleListForConstTable @ [(constantElement, (!currentAddress - 2, "MAKE_LITERAL_CHAR('" ^ (String.make 1 charValue) ^ "')"))]
        )
      end
  | Sexpr (String (stringValue)) ->
      (try
          let x = searchAddressForMakeTriple constantElement in
          temp := [(List.hd !temp)] @ [x]
      with _ ->
        begin
          currentAddress := !currentAddress + 9 + (String.length stringValue);
          for i = 0 to (String.length stringValue - 1) do
            let currentChar = String.get stringValue i in
            match currentChar with
              | '\n' -> tempCharList := !tempCharList @ ["CHAR_NEWLINE"]
              | '\r' -> tempCharList := !tempCharList @ ["CHAR_RETURN"]
              | '\t' -> tempCharList := !tempCharList @ ["CHAR_TAB"]
              | '\x0c' -> tempCharList := !tempCharList @ ["CHAR_PAGE"]
              | ' ' -> tempCharList := !tempCharList @ ["CHAR_SPACE"]
              | '\x00' -> tempCharList := !tempCharList @ ["CHAR_NUL"]
              | '\x27' -> tempCharList := !tempCharList @ ["39"]
              | _ ->  tempCharList := !tempCharList @ ["'" ^ (String.make 1 currentChar) ^ "'"]
          done;
          tripleListForConstTable := !tripleListForConstTable
                                      @
                                      [
                                        (
                                          constantElement,
                                          (
                                            !currentAddress - (String.length stringValue) - 9,
                                            "MAKE_LITERAL_STRING_LIKE_VECTOR " ^ (String.concat ", " !tempCharList)
                                          )
                                        )
                                      ];
          tempCharList := []
        end)
  | Sexpr (Symbol (stringValue)) ->
      begin
        currentAddress := !currentAddress + 9;
        tripleListForConstTable :=
          !tripleListForConstTable
          @
          [(constantElement, (!currentAddress - 9, "MAKE_LITERAL_SYMBOL(const_tbl+" ^ string_of_int (searchAddressForMakeTriple (Sexpr(String(stringValue)))) ^ ")"))]
      end
  | Sexpr (Pair (car, cdr)) ->
      begin
        currentAddress := !currentAddress + 17;
        tripleListForConstTable :=
          !tripleListForConstTable
          @
          [(constantElement, (!currentAddress - 17, "MAKE_LITERAL_PAIR(const_tbl+" ^ string_of_int (searchAddressForMakeTriple (Sexpr(car))) ^ ", const_tbl+" ^ string_of_int (searchAddressForMakeTriple (Sexpr(cdr))) ^ ")"))]
      end
  | Sexpr (Vector ([])) ->
      begin
        currentAddress := !currentAddress + 9;
        tripleListForConstTable :=
          !tripleListForConstTable
          @
          [
            (
              constantElement,
              (
                (!currentAddress - 9),
                "MAKE_LITERAL_VECTOR"
              )
            )
          ]
      end
  | Sexpr (Vector (sexpList)) ->
      begin
        currentAddress := !currentAddress + 9 + (List.length sexpList) * 8;
        let vectorElements = String.concat
                              ""
                              (
                                List.map
                                  (fun element -> "const_tbl+" ^ (string_of_int (searchAddressForMakeTriple (Sexpr(element)))) ^ ", ")
                                  sexpList
                              )
        in
        tripleListForConstTable :=
          !tripleListForConstTable
          @
          [
            (
              constantElement,
              (
                (!currentAddress - 9 - (List.length sexpList) * 8),
                "MAKE_LITERAL_VECTOR " ^ (String.sub vectorElements 0 (String.length vectorElements - 2))
              )
            )
          ]
      end
  | _ -> currentAddress := !currentAddress;;

let rec scanAstForVarFree ast = match ast with
  | Var' (varType) ->
      (match varType with
        | VarFree (varFreeName) ->
            if List.mem varFreeName !varFreeForFVarTable
              then varFreeForFVarTable := !varFreeForFVarTable
              else varFreeForFVarTable := !varFreeForFVarTable @ [varFreeName]
        | _ -> varFreeForFVarTable := !varFreeForFVarTable
      )
  | If' (test, dit, dif) ->
      begin
        scanAstForVarFree test;
        scanAstForVarFree dit;
        scanAstForVarFree dif
      end
  | Seq' (exprList) -> List.iter (fun element -> scanAstForVarFree element) exprList
  | Set' (varible, value) ->
      begin
        scanAstForVarFree varible;
        scanAstForVarFree value
      end
  | Def' (varible, value) ->
      begin
        scanAstForVarFree varible;
        scanAstForVarFree value
      end
  | Or' (exprList) -> List.iter (fun element -> scanAstForVarFree element) exprList
  | LambdaSimple' (args, body) -> scanAstForVarFree body
  | LambdaOpt' (args, additionalArg, body) -> scanAstForVarFree body
  | Applic' (proc, exprList) ->
      begin
        scanAstForVarFree proc;
        List.iter (fun element -> scanAstForVarFree element) exprList
      end
  | ApplicTP' (proc, exprList) ->
      begin
        scanAstForVarFree proc;
        List.iter (fun element -> scanAstForVarFree element) exprList
      end
  | _ -> varFreeForFVarTable := !varFreeForFVarTable;;

let makeTuple varElement =
  begin
    varFreeTupleForFVarTable := !varFreeTupleForFVarTable @ [(varElement, !index)];
    index := !index + 1
  end;;

let make_consts_tbl asts =
  begin
    List.iter
      scanAstForConst
      asts;
    List.iter
      makeSubConstant
      !sexprListForConstTable;
    List.iter
      makeTriple
      !sexprListForConstTableIncludingSubs;
    !tripleListForConstTable
  end;;

let make_fvars_tbl asts =
  begin
    List.iter
      scanAstForVarFree
      asts;
    List.iter
      makeTuple
      !varFreeForFVarTable;
    !varFreeTupleForFVarTable
  end;;

  let getAddressOfConst consts constElement =
    let getConstant (c, (a, (s : string))) = c in
    let getAddress (c, (a, (s : string))) = a in
    let found = ref [] in
    begin
      for i = 0 to (List.length consts - 1) do
        if getConstant (List.nth consts i) = constElement
          then
            found := !found @ [getAddress (List.nth consts i)]
      done;
      List.nth !found 0
    end;;

let getIndexOfFVar fvars fvarElement =
  let getFvar (f, i) = f in
  let getIndex (f, i) = i in
  let found = ref [] in
  begin
    for i = 0 to (List.length fvars - 1) do
      if getFvar (List.nth fvars i) = fvarElement
        then
          found := !found @ [getIndex (List.nth fvars i)]
    done;
    List.nth !found 0
  end;;

let rec generate consts fvars e depth = match e with
  | Const' (constType) -> "mov rax, const_tbl+" ^ (string_of_int (getAddressOfConst consts constType)) ^ "\n"
  | Var' (varType) ->
      (match varType with
        | VarFree (varFreeName) -> "mov rax, FVAR(" ^ (string_of_int (getIndexOfFVar fvars varFreeName)) ^ ")" ^ "\n"
        | VarParam (_, minor) ->
            "mov rax, " ^ (string_of_int minor) ^ "\n" ^
            "add rax, 4" ^ "\n" ^
            "mov rbx, 8" ^ "\n" ^
            "mul rbx" ^ "\n" ^
            "mov rax, qword [rbp + rax]" ^ "\n"
        | VarBound (_, major, minor) ->
            "mov rax, qword [rbp + 8 * 2]" ^ "\n" ^
            "mov rax, qword [rax + 8 * " ^ (string_of_int major) ^ "]" ^ "\n" ^
            "mov rax, qword [rax + 8 * " ^ (string_of_int minor) ^ "]" ^ "\n"
      )
  | Box' (insideVar) ->
      (generate consts fvars (Var' (insideVar)) depth) ^
      "MALLOC r15, WORD_SIZE" ^ "\n" ^
      "mov [r15], rax" ^ "\n" ^
      "mov rax, r15" ^ "\n"
  | BoxGet' (insideVar) ->
      (generate consts fvars (Var' (insideVar)) depth) ^
      "mov rax, qword [rax]" ^ "\n"
  | BoxSet' (insideVar, newVal) ->
      (generate consts fvars newVal depth) ^
      "push rax" ^ "\n" ^
      (generate consts fvars (Var' (insideVar)) depth) ^
      "pop qword [rax]" ^ "\n" ^
      "mov rax, SOB_VOID_ADDRESS" ^ "\n"
  | If' (test, dit, dif) ->
      begin
        counterOfIf := !counterOfIf + 1;
        let currentCounter = !counterOfIf in
        (generate consts fvars test depth) ^
        "cmp rax, SOB_FALSE_ADDRESS" ^ "\n" ^
        "je Lelse" ^ (string_of_int currentCounter) ^ "\n" ^
        (generate consts fvars dit depth) ^
        "jmp LexitIf" ^ (string_of_int currentCounter) ^ "\n" ^
        "Lelse" ^ (string_of_int currentCounter) ^ ":" ^ "\n" ^
        (generate consts fvars dif depth) ^
        "LexitIf" ^ (string_of_int currentCounter) ^ ":" ^ "\n"
      end
  | Seq' (exprList) ->
      List.fold_left
        (fun acc element -> acc ^ (generate consts fvars element depth))
        ""
        exprList
  | Set' (Var'(varType), value) ->
      (match varType with
        | VarFree (varFreeName) ->
            (generate consts fvars value depth) ^
            "mov qword FVAR(" ^ (string_of_int (getIndexOfFVar fvars varFreeName)) ^ "), rax" ^ "\n" ^
            "mov rax, SOB_VOID_ADDRESS" ^ "\n"
        | VarParam (_, minor) ->
            (generate consts fvars value depth) ^
            "mov qword [rbp + 8 * (4 + " ^ (string_of_int minor) ^ ")], rax" ^ "\n" ^
            "mov rax, SOB_VOID_ADDRESS" ^ "\n"
        | VarBound (_, major, minor) ->
            (generate consts fvars value depth) ^
            "mov rbx, qword [rbp + 8 * 2]" ^ "\n" ^
            "mov rbx, qword [rbx + 8 * " ^ (string_of_int major) ^ "]" ^ "\n" ^
            "mov qword [rbx + 8 * " ^ (string_of_int minor) ^ "], rax" ^ "\n" ^
            "mov rax, SOB_VOID_ADDRESS" ^ "\n"
      )
  | Set' (x, y) -> " "
  | Def' (Var'(varType), value) ->
      (match varType with
        | VarFree (varFreeName) ->
          (generate consts fvars value depth) ^
          "mov qword FVAR(" ^  (string_of_int (getIndexOfFVar fvars varFreeName)) ^ "), rax" ^ "\n" ^
          "mov rax, SOB_VOID_ADDRESS" ^ "\n"
        | _ -> " "
      )
  | Def' (x, y) -> " "
  | Or' (exprList) ->
      begin
        counterOfOr := !counterOfOr + 1;
        let currentCounter = !counterOfOr in
        (
          List.fold_left
            (fun acc element -> acc ^
                                (generate consts fvars element depth) ^ "\n" ^
                                "cmp rax, SOB_FALSE_ADDRESS" ^ "\n" ^
                                "jne LexitOr" ^ (string_of_int currentCounter) ^ "\n")
            ""
            (List.rev (List.tl (List.rev exprList)))
        )
        ^
        (generate consts fvars (List.hd (List.rev exprList)) depth)^ "\n" ^
        "LexitOr" ^ (string_of_int currentCounter) ^ ":" ^ "\n"
      end
  | LambdaSimple' (args, body) ->
      begin
        counterOfLambdaSimple := (!counterOfLambdaSimple + 2);
        let currentCounter = !counterOfLambdaSimple in
        (if depth = 0
          then
            "MAKE_CLOSURE(rax, SOB_NIL_ADDRESS, Lcode" ^ (string_of_int currentCounter) ^ ")" ^ "\n" ^
            "jmp Lcont" ^ (string_of_int currentCounter) ^ "\n" ^
            "Lcode" ^ (string_of_int currentCounter) ^ ":" ^ "\n" ^
            "push rbp" ^ "\n" ^
            "mov rbp, rsp" ^ "\n" ^
            (generate consts fvars body (depth + 1)) ^
            "leave" ^ "\n" ^
            "ret" ^ "\n" ^
            "Lcont" ^ (string_of_int currentCounter) ^ ":" ^ "\n"
          else
            "mov rcx, qword[rbp + 8 * 2]" ^ "\n" ^ (* rcx = old env *)
            "mov rdx, qword[rbp + 8 * 3]" ^ "\n" ^  (* rdx = number of params *)
            "mov rbx, rbp" ^ "\n" ^
            "add rbx, 32" ^ "\n" ^ (* rbx = address of param0 *)
            (* allocate ExtEnv *)
            "MALLOC r11, 8 * " ^ (string_of_int (depth + 1)) ^ "\n" ^
            "MAKE_CLOSURE(rax, r11, Lcode" ^ (string_of_int currentCounter) ^ ")" ^ "\n" ^
            "xor r12, r12" ^ "\n" ^
            (* copy Env to ExtEnv *)
            ".copyEnv" ^ (string_of_int currentCounter) ^ ":" ^ "\n" ^
            "mov r13, qword [rcx + 8 * r12]" ^ "\n" ^
            "mov qword [r11 + 8 * (r12 + 1)], r13" ^ "\n" ^
            "inc r12" ^ "\n" ^
            "cmp r12, " ^ (string_of_int depth) ^ "\n" ^
            "jne .copyEnv" ^ (string_of_int currentCounter) ^ "\n" ^
            (* check if need to allocate new vector of params *)
            "mov qword[r11], SOB_NIL_ADDRESS" ^ "\n" ^
            "cmp rdx, 0" ^ "\n" ^
            "je .finish" ^ (string_of_int currentCounter) ^ "\n" ^
            (* allocate new vector of params *)
            "inc rdx" ^ "\n" ^
            "shl rdx, 3" ^ "\n" ^
            "MALLOC r8, rdx" ^ "\n" ^
            "shr rdx, 3" ^ "\n" ^
            "dec rdx" ^ "\n" ^
            "mov qword[r11], r8" ^ "\n" ^ (* puts new vector in ExtEnv *)
            "xor r10, r10" ^ "\n" ^
            (* copying params to new vector *)
            ".copyCurrentParam" ^ (string_of_int currentCounter) ^ ":" ^ "\n" ^
            "mov r9, qword [rbx + 8 * r10]" ^ "\n" ^
            "mov qword [r8 + 8 * r10], r9" ^ "\n" ^
            "inc r10" ^ "\n" ^
            "cmp rdx, r10" ^ "\n" ^
            "jne .copyCurrentParam" ^ (string_of_int currentCounter) ^ "\n" ^
            "mov qword [r8 + 8 * rdx], SOB_NIL_ADDRESS" ^ "\n" ^
            (* finish *)
            ".finish" ^ (string_of_int currentCounter) ^ ":" ^ "\n" ^
            "jmp Lcont" ^ (string_of_int currentCounter) ^ "\n" ^
            "Lcode" ^ (string_of_int currentCounter) ^ ":" ^ "\n" ^
            "push rbp" ^ "\n" ^
            "mov rbp, rsp" ^ "\n" ^
            (generate consts fvars body (depth + 1)) ^
            "leave" ^ "\n" ^
            "ret" ^ "\n" ^
            "Lcont" ^ (string_of_int currentCounter) ^ ":" ^ "\n"
        )
      end
  | LambdaOpt' (args, additionalArg, body) ->
      begin
        counterOfLambdaOpt := (!counterOfLambdaOpt + 2);
        let currentCounter = !counterOfLambdaOpt in
        (if depth = 0
          then
            "MAKE_CLOSURE(rax, SOB_NIL_ADDRESS, Lcode" ^ (string_of_int currentCounter) ^ ")" ^ "\n" ^
            "jmp Lcont" ^ (string_of_int currentCounter) ^ "\n" ^
            "Lcode" ^ (string_of_int currentCounter) ^ ":" ^ "\n" ^
            "push rbp" ^ "\n" ^
            "mov rbp, rsp" ^ "\n" ^
            "mov rdx, qword[rbp + 8 * 3]" ^ "\n" ^
            "cmp rdx, " ^ (string_of_int (List.length args)) ^ "\n" ^
            "je finishAdjust" ^ (string_of_int currentCounter) ^ "\n" ^
            "mov rax, SOB_NIL_ADDRESS" ^ "\n" ^
            "mov r14, rdx" ^ "\n" ^
            "sub r14, " ^ (string_of_int (List.length args)) ^ "\n" ^
            "mov r15, r14" ^ "\n" ^
            "add r15, 3" ^ "\n" ^
            "add r15, " ^ (string_of_int (List.length args)) ^ "\n" ^
            "shl r15, 3" ^ "\n" ^
            "add r15, rbp" ^ "\n" ^
            "mov rdi, [r15]" ^ "\n" ^
            ".createPair" ^ (string_of_int currentCounter) ^ ":" ^ "\n" ^
            "push rbx" ^ "\n" ^
            "MAKE_PAIR(rbx, rdi, rax)" ^ "\n" ^
            "mov rax, rbx" ^ "\n" ^
            "pop rbx" ^ "\n" ^
            "sub r15, 8" ^ "\n" ^
            "mov rdi, [r15]" ^ "\n" ^
            "dec r14" ^ "\n" ^
            "cmp r14, 0" ^ "\n" ^
            "jne .createPair" ^ (string_of_int currentCounter) ^ "\n" ^
            "mov r14, 4" ^ "\n" ^
            "add r14, " ^ (string_of_int (List.length args)) ^ "\n" ^
            "shl r14, 3" ^ "\n" ^
            "mov [rbp + r14], rax" ^ "\n" ^
            "finishAdjust" ^ (string_of_int currentCounter) ^ ":" ^ "\n" ^
            (generate consts fvars body (depth + 1)) ^
            "leave" ^ "\n" ^
            "ret" ^ "\n" ^
            "Lcont" ^ (string_of_int currentCounter) ^ ":" ^ "\n"
          else
            "mov rcx, qword[rbp + 8 * 2]" ^ "\n" ^ (* rcx = old env *)
            "mov rdx, qword[rbp + 8 * 3]" ^ "\n" ^  (* rdx = number of params *)
            "mov rbx, rbp" ^ "\n" ^
            "add rbx, 32" ^ "\n" ^ (* rbx = address of param0 *)
            (* allocate ExtEnv *)
            "MALLOC r11, 8 * " ^ (string_of_int (depth + 1)) ^ "\n" ^
            "MAKE_CLOSURE(rax, r11, Lcode" ^ (string_of_int currentCounter) ^ ")" ^ "\n" ^
            "xor r12, r12" ^ "\n" ^
            (* copy Env to ExtEnv *)
            ".copyEnv" ^ (string_of_int currentCounter) ^ ":" ^ "\n" ^
            "mov r13, qword [rcx + 8 * r12]" ^ "\n" ^
            "mov qword [r11 + 8 * (r12 + 1)], r13" ^ "\n" ^
            "inc r12" ^ "\n" ^
            "cmp r12, " ^ (string_of_int depth) ^ "\n" ^
            "jne .copyEnv" ^ (string_of_int currentCounter) ^ "\n" ^
             (* check if need to allocate new vector of params *)
             "mov qword[r11], SOB_NIL_ADDRESS" ^ "\n" ^
             "cmp rdx, 0" ^ "\n" ^
             "je .finish" ^ (string_of_int currentCounter) ^ "\n" ^
            (* allocate new vector of params *)
            "inc rdx" ^ "\n" ^
            "shl rdx, 3" ^ "\n" ^
            "MALLOC r8, rdx" ^ "\n" ^
            "shr rdx, 3" ^ "\n" ^
            "dec rdx" ^ "\n" ^
            "mov qword[r11], r8" ^ "\n" ^ (* puts new vector in ExtEnv *)
            "xor r10, r10" ^ "\n" ^
            (* copying params to new vector *)
            ".copyCurrentParam" ^ (string_of_int currentCounter) ^ ":" ^ "\n" ^
            "mov r9, qword [rbx + 8 * r10]" ^ "\n" ^
            "mov qword [r8 + 8 * r10], r9" ^ "\n" ^
            "inc r10" ^ "\n" ^
            "cmp rdx, r10" ^ "\n" ^
            "jne .copyCurrentParam" ^ (string_of_int currentCounter) ^ "\n" ^
            "mov qword [r8 + 8 * rdx], SOB_NIL_ADDRESS" ^ "\n" ^
            (* finish *)
            ".finish" ^ (string_of_int currentCounter) ^ ":" ^ "\n" ^
            "jmp Lcont" ^ (string_of_int currentCounter) ^ "\n" ^
            "Lcode" ^ (string_of_int currentCounter) ^ ":" ^ "\n" ^
            "push rbp" ^ "\n" ^
            "mov rbp, rsp" ^ "\n" ^
            "mov rdx, qword[rbp + 8 * 3]" ^ "\n" ^
            "cmp rdx, " ^ (string_of_int (List.length args)) ^ "\n" ^
            "je finishAdjust" ^ (string_of_int currentCounter) ^ "\n" ^
            "mov rax, SOB_NIL_ADDRESS" ^ "\n" ^
            "mov r14, rdx" ^ "\n" ^
            "sub r14, " ^ (string_of_int (List.length args)) ^ "\n" ^
            "mov r15, r14" ^ "\n" ^
            "add r15, 3" ^ "\n" ^
            "add r15, " ^ (string_of_int (List.length args)) ^ "\n" ^
            "shl r15, 3" ^ "\n" ^
            "add r15, rbp" ^ "\n" ^
            "mov rdi, [r15]" ^ "\n" ^
            ".createPair" ^ (string_of_int currentCounter) ^ ":" ^ "\n" ^
            "push rbx" ^ "\n" ^
            "MAKE_PAIR(rbx, rdi, rax)" ^ "\n" ^
            "mov rax, rbx" ^ "\n" ^
            "pop rbx" ^ "\n" ^
            "sub r15, 8" ^ "\n" ^
            "mov rdi, [r15]" ^ "\n" ^
            "dec r14" ^ "\n" ^
            "cmp r14, 0" ^ "\n" ^
            "jne .createPair" ^ (string_of_int currentCounter) ^ "\n" ^
            "mov r14, 4" ^ "\n" ^
            "add r14, " ^ (string_of_int (List.length args)) ^ "\n" ^
            "shl r14, 3" ^ "\n" ^
            "mov [rbp + r14], rax" ^ "\n" ^
            "finishAdjust" ^ (string_of_int currentCounter) ^ ":" ^ "\n" ^
            (generate consts fvars body (depth + 1)) ^
            "leave" ^ "\n" ^
            "ret" ^ "\n" ^
            "Lcont" ^ (string_of_int currentCounter) ^ ":" ^ "\n"
        )
      end
  | Applic' (proc, exprList) ->
      begin
        counterOfApplic := !counterOfApplic + 2;
        let currentCounter = !counterOfApplic in
        "push SOB_NIL_ADDRESS" ^ "\n" ^
        List.fold_right
          (fun element acc ->
            acc ^
            (generate consts fvars element depth) ^
            "push rax" ^ "\n"
          )
          exprList
          ""
        ^
        "push " ^ string_of_int (List.length exprList) ^ "\n" ^
        (generate consts fvars proc depth) ^
        "cmp byte [rax], T_CLOSURE" ^ "\n" ^
        "jne LnotClosureOfApplic" ^ (string_of_int currentCounter) ^ "\n" ^
        "CLOSURE_ENV rbx, rax" ^ "\n" ^
        "push rbx" ^ "\n" ^
        "CLOSURE_CODE rbx, rax" ^ "\n" ^
        "call rbx" ^ "\n" ^
        "add rsp, 8" ^ "\n" ^
        "pop rbx" ^ "\n" ^
        "shl rbx, 3" ^ "\n" ^
        "add rsp , rbx" ^ "\n" ^
        "pop rbx" ^ "\n" ^
        "jmp LendApplic" ^ (string_of_int currentCounter) ^ "\n" ^
        "LnotClosureOfApplic" ^ (string_of_int currentCounter) ^ ":" ^ "\n" ^
        "pop rbx" ^ "\n" ^
        "shl rbx, 3" ^ "\n" ^
        "add rsp, rbx" ^ "\n" ^
        "pop rax" ^ "\n" ^
        "mov rax, 60" ^ "\n" ^
        "syscall" ^ "\n" ^
        "LendApplic" ^ (string_of_int currentCounter) ^ ":" ^ "\n"
      end
  | ApplicTP' (proc, exprList) ->
      begin
        counterOfApplicTP := !counterOfApplicTP + 2;
        let currentCounter = !counterOfApplicTP in
        "push SOB_NIL_ADDRESS" ^ "\n" ^
        List.fold_right
          (fun element acc ->
            acc ^
            (generate consts fvars element depth) ^
            "push rax" ^ "\n"
          )
          exprList
          ""
        ^
        "push " ^ string_of_int (List.length exprList) ^ "\n" ^
        (generate consts fvars proc depth) ^
        "cmp byte [rax], T_CLOSURE" ^ "\n" ^
        "jne LnotClosureOfApplic" ^ (string_of_int currentCounter) ^ "\n" ^
        "CLOSURE_ENV rbx, rax" ^ "\n" ^
        "push rbx" ^ "\n" ^
        "CLOSURE_CODE rbx, rax" ^ "\n" ^
        "push qword [rbp + 8 * 1]" ^ "\n" ^
        "push qword[rbp]" ^ "\n" ^
        "SHIFT_FRAME " ^ string_of_int ((List.length exprList) + 5) ^ "\n" ^
        "pop rbp" ^ "\n" ^
        "jmp rbx" ^ "\n" ^
        "LnotClosureOfApplic" ^ (string_of_int currentCounter) ^ ":" ^ "\n" ^
        "pop rbx" ^ "\n" ^
        "shl rbx, 3" ^ "\n" ^
        "add rsp , rbx" ^ "\n" ^
        "pop rax" ^ "\n" ^
        "mov rax, 60" ^ "\n" ^
        "syscall" ^ "\n" ^
        "LendApplic" ^ (string_of_int currentCounter) ^ ":" ^ "\n"
      end;;
end;;

