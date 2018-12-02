open List

type ident = string
type typ = Tint | Tbool | Tstring | Tfloat | Tcomplex | Tdictionary
(* Dictionaries https://www.w3schools.com/python/python_dictionaries.asp *)
type value = IntV of int | BoolV of bool | StrV of ident
type dict = Dict of (ident * value) list

type exp = Int of int | Add of exp * exp | Sub of exp * exp | Mul of exp * exp
         | Div of exp * exp | Bool of bool | And of exp * exp | Or of exp * exp
         | Eq of exp * exp | If of exp * exp * exp | Str of ident
         (*start of Dictionaries methods*)
         | Get of dict * ident

type cmd = Assign of ident * exp | Seq of cmd * cmd | Skip
          | IfC of exp * cmd * cmd | While of exp * cmd | Throw | Try of cmd * cmd
          (* | Throw | Try of cmd * cmd *)

type exp_res = Val of value | Exc

type state = ident -> value option
let empty_state = fun x -> None
let update s x v = fun y -> if y = x then Some v else None

let rec dictionary_index_aux (l: (ident * value) list) (key:ident) (n:int) =
      match l with
      | [] -> None
      | (k, v):: rest ->
        if k = key then Some v else dictionary_index_aux rest key (n -1)

let dictionary_index (list_val_key: (ident * value) list) (key:ident)=
    dictionary_index_aux list_val_key key (length (list_val_key) - 1)

(*Here we define some functions in order to allow operations between int and booleans*)
let to_int (v: value) : int =
    match v with
        | IntV i ->  i
        | BoolV b -> if b = true then 1 else 0


let to_bool (v: value) : bool =
    match v with
        | BoolV b -> b
        | IntV i -> if i = 0 then false else true
        | StrV s -> if s = "" then false else true

let rec concat_i_times (s: ident) (i: int) : ident  =
    match i with
      | 0 -> ""
      | _ -> s ^ concat_i_times s (i - 1)

let rec eval_exp (e : exp) (s : state) : exp_res option =
    match e with
        | Int i -> Some (Val (IntV i))
        | Bool b -> Some (Val (BoolV b))
        | Str s -> Some (Val (StrV s))
        | Add (e1, e2) -> (match eval_exp e1 s, eval_exp e2 s with
                          | Some (Val i1), Some (Val i2) -> Some (Val (IntV (to_int i1 + to_int i2)))
                          | Some (Val (StrV s)), _ | _, Some (Val (StrV s)) -> Some Exc
                          | Some Exc, _ | Some _, Some Exc -> Some Exc
                          | _, _ -> None)

        | Sub (e1, e2) -> (match eval_exp e1 s, eval_exp e2 s with
                          | Some (Val i1), Some (Val i2) -> Some (Val (IntV (to_int i1 - to_int i2)))
                          | Some (Val (StrV s)), _ | _, Some (Val (StrV s)) -> Some Exc
                          | Some Exc, _ | Some _, Some Exc -> Some Exc
                          | _, _ -> None)
        | Mul (e1, e2) -> (match eval_exp e1 s, eval_exp e2 s with
                          | Some (Val i1), Some (Val i2) -> Some (Val (IntV (to_int i1 * to_int i2)))
                          | Some (Val (StrV s)), Some (Val i) | Some (Val i), Some (Val (StrV s)) -> Some (Val (StrV (concat_i_times s (to_int i))))
                          | Some Exc, _ | Some _, Some Exc -> Some Exc
                          | _, _ -> None)
        | Div (e1, e2) -> (match eval_exp e1 s, eval_exp e2 s with
                          | Some (Val  i1), Some (Val i2) ->
                             if to_int i2 = 0 then Some Exc else Some (Val (IntV (to_int i1 / to_int i2)))
                          | Some (Val (StrV s)), _ | _, Some (Val (StrV s)) -> Some Exc
                          | Some Exc, _ | Some _, Some Exc -> Some Exc
                          | _, _ -> None)
        | And (e1, e2) -> (match eval_exp e1 s, eval_exp e2 s with
                          | Some (Val (BoolV b1)), Some (Val (BoolV b2)) -> Some (Val (BoolV (b1 && b2)))
                          | Some (Val b1), Some (Val b2) -> if to_bool b1 then Some(Val(b2)) else Some(Val(b1))
                          | Some (Val (StrV s)), _ | _, Some (Val (StrV s)) -> Some Exc
                          | Some Exc, _ | Some _, Some Exc -> Some Exc
                          | _, _ -> None)
        | Or (e1, e2) -> (match eval_exp e1 s, eval_exp e2 s with
                          | Some (Val (BoolV b1)), Some (Val (BoolV b2)) -> Some (Val (BoolV (b1 || b2)))
                          | Some (Val b1), Some (Val b2) -> if to_bool b1 then Some(Val(b1)) else Some(Val(b2))
                          | Some (Val (StrV s)), _ | _, Some (Val (StrV s)) -> Some Exc
                          | Some Exc, _ | Some _, Some Exc -> Some Exc
                          | _, _ -> None)
        | Eq (e1, e2) -> (match eval_exp e1 s, eval_exp e2 s with
                          | Some (Val v1), Some (Val v2) -> Some (Val (BoolV (v1 = v2)))
                          | Some Exc, _ | Some _, Some Exc -> Some Exc
                          | _, _ -> None)
        | If (e, e1, e2) -> (match eval_exp e s with
                            | Some (Val (BoolV true)) -> eval_exp e1 s
                            | Some (Val (BoolV false)) -> eval_exp e2 s
                            | Some Exc -> Some Exc
                            | _ -> None)

        | Get (dict, key) -> (match dict with
          | Dict(list_val_key) ->
              (match dictionary_index list_val_key key with
                | Some  (IntV i) -> Some (Val (IntV i))
                | Some (BoolV b) -> Some (Val (BoolV b))
                | None -> None)
          | _ -> None)


let rec step_cmd (c : cmd) (s : state) : (cmd * state) option =
    match c with
        | Assign (x, e) -> (match eval_exp e s with
                           | Some (Val v) -> Some (Skip, update s x v)
                           | Some Exc -> Some (Throw, s)  (* added *)
                           | None -> None)
        | Seq (Skip, c2) -> Some (c2, s)
        | Seq (Throw, c2) -> Some (Throw, s)  (* added *)
        | Seq (c1, c2) -> (match step_cmd c1 s with
                          | Some (c1', s') -> Some (Seq (c1', c2), s')
                          | None -> None)
        | Skip -> None
        | Throw -> None (* added *)
        | Try (Skip, c2) -> Some (Skip, s)  (* added *)
        | Try (Throw, c2) -> Some (c2, s)  (* added *)
        | Try (c1, c2) -> (match step_cmd c1 s with   (* added *)
                           | Some (c1', s') -> Some (Try(c1', c2), s')
                           | None -> None)
        | IfC (e, c1, c2) -> (match eval_exp e s with
                             | Some (Val (BoolV true)) -> Some (c1, s)
                             | Some (Val (BoolV false)) -> Some (c2, s)
                             | Some Exc -> Some (Throw, s)  (* added *)
                             | _ -> None)
        | While (e, c) -> Some (IfC (e, Seq (c, While (e, c)), Skip), s)
