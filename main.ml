type ident = string
type typ = Tint | Tbool | Tstring | Tfloat | Tcomplex

type cmd = Assign of ident * exp | Seq of cmd * cmd | Skip
          | IfC of exp * cmd * cmd | While of exp * cmd
          (* | Throw | Try of cmd * cmd *)

type exp = Int of int | Add of exp * exp | Sub of exp * exp | Div of exp * exp
         | Bool of bool | And of exp * exp | Or of exp * exp
         | Eq of exp * exp | If of exp * exp * exp

type value = IntV of int | BoolV of bool

let rec eval_exp (e : exp) (s : state) : exp_res option =
    match e with
        | Int i -> Some (Val (IntV i))
        | Add (e1, e2) -> (match eval_exp e1 s, eval_exp e2 s with
                          | Some (Val (IntV i1)), Some (Val (IntV i2)) -> Some (Val (IntV (i1 + i2)))
                          | Some Exc, _ | Some _, Some Exc -> Some Exc
                          | _, _ -> None)
        | Sub (e1, e2) -> (match eval_exp e1 s, eval_exp e2 s with
                          | Some (Val (IntV i1)), Some (Val (IntV i2)) -> Some (Val (IntV (i1 - i2)))
                          | Some Exc, _ | Some _, Some Exc -> Some Exc
                          | _, _ -> None)
        | Div (e1, e2) -> (match eval_exp e1 s, eval_exp e2 s with
                          | Some (Val (IntV i1)), Some (Val (IntV i2)) ->
                             if i2 = 0 then Some Exc else Some (Val (IntV (i1 / i2)))
                          | Some Exc, _ | Some _, Some Exc -> Some Exc
                          | _, _ -> None)
        | Bool b -> Some (Val (BoolV b))
        | And (e1, e2) -> (match eval_exp e1 s, eval_exp e2 s with
                          | Some (Val (BoolV b1)), Some (Val (BoolV b2)) -> Some (Val (BoolV (b1 && b2)))
                          | Some Exc, _ | Some _, Some Exc -> Some Exc
                          | _, _ -> None)
        | Or (e1, e2) -> (match eval_exp e1 s, eval_exp e2 s with
                          | Some (Val (BoolV b1)), Some (Val (BoolV b2)) -> Some (Val (BoolV (b1 || b2)))
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
