open List

type ident = string

type ref = int
type value = IntV of int | BoolV of bool | StrV of ident | RefV of ref | ListS of ident list | ListV of value list

type typ = Tint | Tbool | Tstring | Tfloat | Tcomplex | Tdictionary | Tclass of ident
(* Dictionaries https://www.w3schools.com/python/python_dictionaries.asp *)

type exp_res = Val of value option | Exc
type exps_res = LsVal of value list | Exc
(*To handle expceptions in list of expressions*)

type str_val_list = StValLs of (ident * value) list
type obj = Obj of ident * value list | Dict of (ident * value) list

type exp = Int of int | Add of exp * exp | Sub of exp * exp | Mul of exp * exp
         | Div of exp * exp | Bool of bool | And of exp * exp | Or of exp * exp
         | Eq of exp * exp | If of exp * exp * exp | Str of ident | Var of ident
         | GetField of exp * ident
         (*start of Dictionaries methods*)
         | Get of exp * ident

type cmd = Assign of ident * exp | Seq of cmd * cmd | Skip
         | IfC of exp * cmd * cmd | While of exp * cmd | Throw | Try of cmd * cmd
         | New of ident * ident * exp list | SetField of exp * ident * exp
         | Invoke of ident * exp * ident * exp list | Return of exp
         | Instantiate_dict of ident * str_val_list
         | Set of exp * ident * value


type mdecl = MDecl of ident * ident list * cmd

type cdecl = Class of ident * ident * ident list * mdecl list | Dict_decl of ident * str_val_list

type class_table = ident -> cdecl option


type env = ident -> value option
type store = (ref -> obj option) * ref
let empty_state = fun x -> None
let update s x v = fun y -> if y = x then Some v else s y

let empty_store : store = (empty_state, 0)
let store_lookup (s : store) = fst s
let next_ref (s : store) = snd s
let update_store (s : store) (r : ref) (o : obj) : store =
  (update (store_lookup s) r o, next_ref s)

(* field and method lookup *)
let rec fields (ct : class_table) (c : ident) : ident list =
  if c = "Object" then [] else
    match ct c with
    | Some (Class (_, d, lf, _)) -> fields ct d @ lf
    | _ -> []

let rec field_index_aux (l : ident list) (f : ident) (n : int) =
  match l with
  | [] -> None
  | g :: rest ->
     if f = g then Some n else field_index_aux rest f (n - 1)

let field_index ct c f =
  field_index_aux (rev (fields ct c)) f (length (fields ct c) - 1)

let rec methods (ct : class_table) (c : ident) : mdecl list =
  if c = "Object" then [] else
    match ct c with
    | Some (Class (_, d, _, lm)) -> methods ct d @ lm
    | _ -> []

let lookup_method_aux (l : mdecl list) (m : ident) : mdecl option =
  find_opt (fun d -> match d with MDecl (n, _, _) -> n = m) l

let lookup_method ct c m =
  lookup_method_aux (rev (methods ct c)) m

let replace l pos a  = mapi (fun i x -> if i = pos then a else x) l

let rec dictionary_index_aux (l: (ident * value) list) (key:ident) (n:int) =
      match l with
      | [] -> None
      | (k, v):: rest ->
        if k = key then Some v else dictionary_index_aux rest key (n -1)

let dictionary_index (list_val_key: (ident * value) list) (key:ident)=
    dictionary_index_aux list_val_key key (length (list_val_key) - 1)
(*auxiliary function *)
let rec get_keys_from_dict (dic:(ident*value) list) (list_k: ident list) =
    match dic with
    | [] -> list_k
    | (k,v)::rest ->
      get_keys_from_dict rest list_k@[k]

let rec get_values_from_dict (dic:(ident*value) list) (list_v: value list) =
    match dic with
    | [] -> list_v
    | (k,v)::rest ->
      get_values_from_dict rest list_v@[v]

(*Here we define some functions in order to allow operations between int and booleans*)
let to_int (v: value option) : int =
    match v with
        | Some (IntV i) -> i
        | Some (BoolV b) -> if b = true then 1 else 0
        | _ -> 0


let to_bool (v: value option) : bool =
    match v with
        | Some (BoolV b) -> b
        | Some (IntV i) -> if i = 0 then false else true
        | Some (StrV s) -> if s = "" then false else true
        | _ -> false

(*concat a string i times*)
let rec concat_i_times (s: ident) (i: int) : ident  =
    match i with
      | 0 -> ""
      | _ -> s ^ concat_i_times s (i - 1)


(* evaluating expressions (based on big-step rules) *)
let rec eval_exp (ct : class_table) (e : exp) (r : env) (s : store)
: exp_res option =
    match e with
        | Var x -> Some (Val (r x))
        | Int i -> Some (Val (Some(IntV i)))
        | Bool b -> Some (Val (Some(BoolV b)))
        | Str s -> Some (Val (Some(StrV s)))
        | Add (e1, e2) -> (match eval_exp ct e1 r s, eval_exp ct e2 r s with
                          | Some (Val (Some(StrV st))), _ | _, Some (Val (Some(StrV st))) -> Some Exc
                          | Some (Val i1), Some (Val i2) -> Some (Val (Some(IntV (to_int i1 + to_int i2))))
                          | Some Exc, _ | Some _, Some Exc -> Some Exc
                          | _, _ -> None)
        | Sub (e1, e2) -> (match eval_exp ct e1 r s, eval_exp ct e2 r s with
                          | Some (Val (Some(StrV st))), _ | _, Some (Val (Some(StrV st))) -> Some Exc
                          | Some (Val i1), Some (Val i2) -> Some (Val (Some(IntV (to_int i1 - to_int i2))))
                          | Some Exc, _ | Some _, Some Exc -> Some Exc
                          | _, _ -> None)
        | Mul (e1, e2) -> (match eval_exp ct e1 r s, eval_exp ct e2 r s with
                          | Some (Val (Some(StrV st))), Some (Val i) | Some (Val i), Some (Val (Some(StrV st))) -> Some (Val (Some(StrV (concat_i_times st (to_int i)))))
                          | Some (Val i1), Some (Val i2) -> Some (Val (Some(IntV (to_int i1 * to_int i2))))
                          | Some Exc, _ | Some _, Some Exc -> Some Exc
                          | _, _ -> None)
        | Div (e1, e2) -> (match eval_exp ct e1 r s, eval_exp ct e2 r s with
                          | Some (Val (Some(StrV st))), _ | _, Some (Val (Some(StrV st))) -> Some Exc
                          | Some (Val  i1), Some (Val i2) ->
                             if to_int i2 = 0 then Some Exc else Some (Val (Some(IntV (to_int i1 / to_int i2))))
                          | Some Exc, _ | Some _, Some Exc -> Some Exc
                          | _, _ -> None)
        | And (e1, e2) -> (match eval_exp ct e1 r s, eval_exp ct e2 r s with
                          | Some (Val (Some(StrV st))), _ | _, Some (Val (Some(StrV st))) -> Some Exc
                          | Some (Val b1), Some (Val b2) -> if to_bool b1 then Some(Val(b2)) else Some(Val(b1))
                          | Some Exc, _ | Some _, Some Exc -> Some Exc
                          | _, _ -> None)
        | Or (e1, e2) -> (match eval_exp ct e1 r s, eval_exp ct e2 r s with
                          | Some (Val (Some(StrV st))), _ | _, Some (Val (Some(StrV st))) -> Some Exc
                          | Some (Val b1), Some (Val b2) -> if to_bool b1 then Some(Val(b1)) else Some(Val(b2))
                          | Some Exc, _ | Some _, Some Exc -> Some Exc
                          | _, _ -> None)
        | Eq (e1, e2) -> (match eval_exp ct e1 r s, eval_exp ct e2 r s with
                          | Some (Val v1), Some (Val v2) -> Some (Val (Some(BoolV (v1 = v2))))
                          | Some Exc, _ | Some _, Some Exc -> Some Exc
                          | _, _ -> None)
        | If (e, e1, e2) -> (match  eval_exp ct e r s with
                            | Some (Val v1) -> if to_bool v1 then eval_exp ct e1 r s else eval_exp ct e2 r s
                            | Some Exc -> Some Exc
                            | _ -> None)
        | GetField (e, f) ->
           (match eval_exp ct e r s with
            | Some (Val (Some(RefV(p)))) ->
               (match store_lookup s p with
                | Some (Obj (c, lv)) ->
                   (match field_index ct c f with
                    | Some i -> Some (Val (nth_opt lv i))
                    | None -> Some Exc) (*duck typing exception*)
                | _ -> None)
            | _ -> None)

        | Get (e, key) ->
           (match eval_exp ct e r s with
            | Some (Val (Some(RefV(p)))) ->
               (match store_lookup s p with
                | Some (Dict (list_val_key)) ->
                (match dictionary_index list_val_key key with
                  | Some i -> Some (Val (Some(i)))
                  | None -> Some Exc)
                 | _ -> Some Exc)
              | Some Exc -> Some Exc
              | _ -> None)



let rec eval_exps (ct : class_table) (le : exp list) (r : env) (s : store)
        : exps_res option =
  match le with
  | [] -> Some (LsVal [])
  | e :: rest ->
     (match eval_exp ct e r s, eval_exps ct rest r s with
      | Some (Val (Some v)), Some (LsVal lv) -> Some (LsVal(v :: lv))
      | Some Exc, _  | _, Some Exc -> Some Exc
      | _, _ -> None)


(* evaluating commands (based on small-step rules) *)
type stack = (env * ident) list
type config = cmd * stack * env * store

let rec make_env (li : ident list) (lv : value list) : env =
  match li, lv with
  | i :: irest, v :: vrest -> update (make_env irest vrest) i v
  | _, _ -> empty_state


  let rec step_cmd (ct : class_table) (c : cmd) (k : stack) (r : env) (s : store)
          : config option =
    match c with
    | Assign (x, e) ->
       (match eval_exp ct e r s with
        | Some (Val (Some(v))) -> Some (Skip, k, update r x v, s)
        | Some Exc -> Some (Throw, k, r, s)  (* added *)
        | _ -> None)
    | Seq (Skip, c2) -> Some (c2, k, r, s)
    | Seq (Throw, c2) -> Some (Throw, k, r, s)  (* added *)
    | Seq (c1, c2) ->
       (match step_cmd ct c1 k r s with
        | Some (c1', k', r', s') -> Some (Seq (c1', c2), k', r', s')
        | None -> None)
    | Skip -> None
  (*start for the modified part *)
    | IfC(e,c1,c2) ->
      (match eval_exp ct e r s with
        | Some (Val v1) -> if to_bool v1 then Some(c1,k,r,s) else Some(c2,k,r,s)
        | Some Exc -> Some (Throw, k, r, s)  (* added *)
        | _ -> None
        )
    | While (e, c) -> Some (IfC (e, Seq (c, While (e, c)), Skip), k, r, s)
    | Invoke(x,e,m,args) ->
      (match eval_exp ct e r s, eval_exps ct args r s with
        | Some (Val (Some(RefV(p)))), Some (LsVal vals) ->
          (match (store_lookup s) p with
           | Some(Obj(c,lv)) ->
           (match lookup_method ct c m with
             | Some(MDecl(_,params,body))->
             let pref = RefV (p) in
              Some(body,(r,x)::k, update (make_env params vals) "this" pref, s)
              | None -> Some (Throw, k, r, s))  (*duck typing exception*)
           | _ -> None)
        | Some Exc, _ | _, Some Exc-> Some (Throw, k, r, s)
        | _, _ -> None)
  (*Small step for Return invocation*)
    | Return(exp)->
      ( match eval_exp ct exp r s with
        | Some (Val (Some v)) -> (
            match k with
            | (r0,x0)::k0 -> Some(Skip, k0, update r0 x0 v, s)
            | _ -> None
            )
        | Some Exc -> Some (Throw, k, r, s)
        | _ -> None)
  (*End small step for method invocation*)
  (*end for the modified part *)
    | Instantiate_dict (x, dict) ->
        (match dict with
        | StValLs(args) ->
           let p = next_ref s in
           Some (Skip, k, update r x (RefV p),
                 (update (store_lookup s) p (Dict(args)), p + 1)))

    | New (x, c, args) ->
       (match eval_exps ct args r s with
        | Some (LsVal lv) ->
           let p = next_ref s in
           Some (Skip, k, update r x (RefV p),
                 (update (store_lookup s) p (Obj (c, lv)), p + 1))
        | Some Exc -> Some (Throw, k, r, s)
        | None -> None)

    | SetField (e, f, e1) ->
       (match eval_exp ct e r s, eval_exp ct e1 r s with
        | Some (Val (Some(RefV(p)))), Some (Val (Some v)) ->
           (match store_lookup s p with
            | Some (Obj (c, lv)) ->
               (match field_index ct c f with
                | Some i -> Some (Skip, k, r, update_store s p (Obj (c, replace lv i v)))
                | None -> Some (Throw, k, r, s)) (*duck typing exception*)
            | _ -> None)
        | Some Exc, _ | _, Some Exc -> Some (Throw, k, r, s)
        | _, _ -> None)

      (*(e, f, e1)*)
      | Set (e, key, value) ->
         (match eval_exp ct e r s with
          | Some (Val (Some(RefV(p))))  ->
             (match store_lookup s p with
               | Some (Dict (list_val_key)) -> Some (Skip, k, r,update_store s p (Dict(list_val_key@[(key,value)])))
               | None -> Some (Throw, k, r, s)) (*duck typing exception*)
               | _ -> Some (Throw, k, r, s)
          | Some Exc -> Some (Throw, k, r, s)
          | _-> None)

    | Throw -> None (* added *)
    | Try (Skip, c2) -> Some (Skip,  k, r, s)  (* added *)
    | Try (Throw, c2) -> Some (c2,  k, r, s)  (* added *)
    | Try (c1, c2) -> (match step_cmd ct c1 k r s with   (* added *)
                       | Some (c1', k', r', s') -> Some (Try(c1', c2), k', r', s')
                       | None -> None)


let ct1 d = if d = "Shape" then
              Some (Class ("Shape", "Object", [("id")],
                           [MDecl ("area", [],
                                   Return (Int 0))]))
            else if d = "Square" then
              Some (Class ("Square", "Shape", [("side")],
                           [MDecl ("area", [],
                                   Seq (Assign ("x", GetField (Var "this", "side")),
                                        Return (Mul (Var "x", Var "x"))))]))
            (*else if d = "dict_1" then
              Some (Dict_decl("dict_1", Dict([("flavio",IntV(3));("santa",IntV(4))])))*)

            else None

  let rec run_config (ct : class_table) (con : config) : config =
    let (c, k, r, s) = con in
    match step_cmd ct c k r s with
    | Some con' -> run_config ct con'
    | None -> con

  let run_prog (ct : class_table) (c : cmd) =
    run_config ct (c, [], empty_state, empty_store)

  (* test cases *)
  let test0 : cmd =
    Seq (New ("s", "Square", [Int 0; Int 2]),
         (* s = new Square(0, 2); *)
         SetField (Var "s", "side", Add (GetField (Var "s", "side"), Int 1)))
         (* s.side = s.side + 1; *)

(*Set field duck typing exception*)
 let test0_exc0 : cmd =
   Seq (New ("s", "Square", [Int 0; Int 2]),
        (* s = new Square(0, 2); *)
        SetField (Var "s", "front", Add (GetField (Var "s", "side"), Int 1)))
        (* s.side = s.side + 1; *)



(*Get field duck typing exception*)
let test0_exc1 : cmd =
  Seq (New ("s", "Square", [Int 0; Int 2]),
       (* s = new Square(0, 2); *)
       SetField (Var "s", "side", Add (GetField (Var "s", "front"), Int 1)))
       (* s.side = s.side + 1; *)


  let test1 : cmd =
    Seq (Assign ("x", Int 1),
         IfC (Var "x", Assign ("x", Int 2), Assign ("x", Int 3)))

  let test2 : cmd =
    Seq (New ("s", "Shape", [Int 2]),
         (* s = new Shape(2); *)
         Invoke ("x", Var "s", "area", []))
         (* x = s.area(); *)

  let test2_exc : cmd =
   Seq (New ("s", "Shape", [Int 2]),
        (* s = new Shape(2); *)
        Invoke ("x", Var "s", "volume", []))
        (* x = s.area(); *)

  let test_set_dict : cmd = Seq(Instantiate_dict ("s", StValLs [("flavio",IntV(3));("santa",IntV(4))]),Set(Var "s","porco", IntV(3)))

  (*test instantiate dictionary*)
  let test_dict : cmd =
    Instantiate_dict ("s", StValLs [("flavio",IntV(3));("santa",IntV(4))])
         (* s = new Square(0, 2); *)

  let test3 : cmd =
    Seq (New ("s", "Square", [Int 0; Int 2]),
         (* s = new Square(0, 2); *)
    Seq (SetField (Var "s", "side", Add (GetField (Var "s", "side"), Int 1)),
         (* s.side = s.side + 1; *)
         Invoke ("x", Var "s", "area", [])))
         (* x = s.area(); *)

 (*type exceptions*)
  let test_exc0 : exp =
    Add(Str "x", Int 3)

  let test_0 : exp =
    Mul (Str "x", Int (-3))

  let test_1 : exp =
    Div (Str "x", Int 3)
