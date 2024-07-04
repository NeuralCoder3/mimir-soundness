type binder =
  | BNamed of string
  | BAnon

(* all number < n *)
type fin = int (* Simplified representation *)

type expr =
  | Star
  | Box
  | Bot
  | Nat
  | Idx
  | LitNat of int
  | LitIdx of int * fin
  | Var of string
  | Pi of binder * expr * expr
  (* x T f U e *)
  | Lam of binder * expr * expr * expr * expr
  | App of expr * expr
  | Sigma of (binder * expr) list
  | Tuple of expr list
  | Array of binder * expr * expr
  | Pack of binder * expr * expr
  | Extract of expr * expr

let rec subst x es e =
  let recurse_under y expr =
    match y with
    | BNamed y_str -> if y_str = x then expr else subst x es expr
    | BAnon -> subst x es expr
  in
  match e with
  | Star | Box | Bot | Nat | Idx | LitNat _ | LitIdx (_,_) -> e
  | Var y -> if y = x then es else e
  | Pi (y, t, u) -> Pi (y, subst x es t, recurse_under y u)
  | Lam (y, t, f, u, e) ->
      Lam (y, subst x es t, recurse_under y f, recurse_under y u, recurse_under y e)
  | App (e1, e2) -> App (subst x es e1, subst x es e2)
  | Tuple expr_list -> Tuple (List.map (subst x es) expr_list)
  | Sigma xs ->
      let rec fold_subst xs =
        match xs with
        | [] -> []
        | (y, t) :: xs' ->
            let rest = if y = BNamed x then xs' else fold_subst xs' in
            (y, subst x es t) :: rest
      in
      Sigma (fold_subst xs)
  | Array (y, en, t) -> Array (y, subst x es en, recurse_under y t)
  | Pack (y, en, e) -> Pack (y, subst x es en, recurse_under y e)
  | Extract (e, ei) -> Extract (subst x es e, subst x es ei)

let subst' mx es =
  match mx with
  | BNamed x -> subst x es
  | BAnon -> fun e -> e


let ebool = App (Idx, LitNat 2)
let etrue = LitIdx (2, 1)

(* ith element is i *)
let rec fin_list n = List.init n (fun i -> i)

let rec replicate n x =
  if n = 0 then [] else x :: replicate (n - 1) x

(* instantiate e via subst with x = LitIdx n 0 ... ListIdx (n-1) *)
let instantiate x n e =
  List.map (fun i -> subst x (LitIdx (n, i)) e) (fin_list n)

let normalize_step e =
  match e with
  (*
     normalize_extract_one
     e#0_1 -> e
  *)
  | Extract (e, LitIdx (1, 0)) -> Some e
  (*
     normalize_tuple_one
      (e) -> e
  *)
  | Tuple [e] -> Some e
  (*
    normalize_sigma_one
    [(_,T)] -> T
    (in paper just [T])
  *)
  | Sigma [(_,t)] -> Some t
  (*
    normalize_tuple_beta
    (e0, ..., en-1)#i_n -> ei
  *)
  | Extract (Tuple xs, LitIdx (n, i)) ->
      (* check superfluous as we assume typed *)
      if List.length xs = n then
        (* has to be true *)
        (match List.nth_opt xs i with
         | Some e -> Some e
         | None -> None)
      else None
  (*
      normalize_pack_beta
      <_:n;e>#ei -> e
  *)
  | Extract (Pack (BAnon, en, e), ei) -> Some e
  (* when all elements are ith extracts of some e => e *)
  (*
    normalize_tuple_eta
    (e#0_n, ..., e#n-1_n) -> e
  *)
  | Tuple (es) 
    when (List.length es > 1 && 
      match List.hd es with
      | Extract (eB,_) -> 
        List.mapi (fun i e -> (e,i)) es
        |> List.for_all (fun (e,i) -> 
          e = Extract (eB, LitIdx (List.length es, i))
        )
      | _ -> false) ->
      (match List.hd es with
      | Extract (eB,_) -> Some eB
      | _ -> None)
  (* when all elements are the same e => Pack *)
  (*
      normalize_pack_tuple
      (e, ..., e) -> <_:n;e>
  *)
  | Tuple (es) when (List.length es > 1 &&
      List.for_all (fun e -> e = List.hd es) es) ->
      Some (Pack (BAnon, LitNat (List.length es), List.hd es))
  (* when all elements are the same e for Sigma with an anon *)
  (*
     normalize_array_sigma
     [(_,T), ..., (_,T)] -> <<_:n;T>>
  *)
  | Sigma xs when (List.length xs > 1 &&
      List.for_all (fun (x,t) -> x = BAnon && t = snd (List.hd xs)) xs) ->
      Some (Array (BAnon, LitNat (List.length xs), snd (List.hd xs)))
  (*
    normalize_beta
    if ef normalizes to etrue
    (λ (x:T) : U @ ef, eb) ea -> eb[ea/x]
  *)
      (* TODO: ef normalizes to etrue not just equal *)
  | App (Lam (x, t, ef, u, eb), ea) when ef = etrue ->
      Some (subst' x ea eb)
  (*
    normalize_tuple_pack
    <x:n;e> -> (e[0_n/x], ..., e[n-1_n/x])
  *)
  | Pack (BNamed x, LitNat n, e) -> Some (Tuple (instantiate x n e))
  (*
    normalize_sigma_array
    <<x:n;T>> -> [(BAnon, T[0_n/x]), ..., (BAnon, T[n-1_n/x])
  *)
  | Array (BNamed x, LitNat n, t) ->
      Some (Sigma (List.map (fun x -> (BAnon, x)) (instantiate x n t)))

  (* TODO: not in paper *)
  (* unnamed pack of length 1 *)
  | Pack (BAnon, LitNat 1, e) -> Some e
  (* unnamed array of length 1 *)
  | Array (BAnon, LitNat 1, t) -> Some t

  | _ -> None


let rec string_of_list s1 s2 sep f xs =
  s1 ^ (String.concat sep (List.map f xs)) ^ s2

(* explicit printer
   e.g. 
   Lam(BNamed "x", Nat, LitNat 0, Idx, Var "x")
*)
let string_of_binder = function
  | BNamed x -> "BNamed \"" ^ x ^ "\""
  | BAnon -> "BAnon"

let rec string_of_expr e =
  match e with
  | Star -> "Star"
  | Box -> "Box"
  | Bot -> "Bot"
  | Nat -> "Nat"
  | Idx -> "Idx"
  | LitNat n -> "LitNat " ^ string_of_int n
  | LitIdx (n, i) -> "LitIdx (" ^ string_of_int n ^ ", " ^ string_of_int i ^ ")"
  | Var x -> "Var \"" ^ x ^ "\""
  | Pi (x, t, u) -> 
      "Pi (" ^ string_of_binder x ^ ", " ^ string_of_expr t ^ ", " ^ string_of_expr u ^ ")"
  | Lam (x, t, f, u, e) ->
      "Lam (" ^ string_of_binder x ^ ", " ^ string_of_expr t ^ ", " ^ string_of_expr f ^ ", " ^ string_of_expr u ^ ", " ^ string_of_expr e ^ ")"
  | App (e1, e2) -> "App (" ^ string_of_expr e1 ^ ", " ^ string_of_expr e2 ^ ")"
  | Sigma xs -> 
      "Sigma [" ^ string_of_list "" "" ", " (fun (x, t) -> "(" ^ string_of_binder x ^ ", " ^ string_of_expr t ^ ")") xs ^ "]"
  | Tuple es -> 
      "Tuple [" ^ string_of_list "" "" ", " string_of_expr es ^ "]"
  | Array (x, en, t) -> 
      "Array (" ^ string_of_binder x ^ ", " ^ string_of_expr en ^ ", " ^ string_of_expr t ^ ")"
  | Pack (x, en, e) -> 
      "Pack (" ^ string_of_binder x ^ ", " ^ string_of_expr en ^ ", " ^ string_of_expr e ^ ")"
  | Extract (e, ei) -> 
      "Extract (" ^ string_of_expr e ^ ", " ^ string_of_expr ei ^ ")"


let pretty_string_of_binder = function
  | BNamed x -> x
  | BAnon -> "_"
let rec pretty_string_of_expr e =
  match e with
  | Star -> "*"
  | Box -> "[]"
  | Bot -> "⊥"
  | Nat -> "ℕ"
  | Idx -> "Idx"
  | App(Idx, LitNat n) -> "Idx "^string_of_int n
  | LitNat n -> string_of_int n
  | LitIdx (n, i) -> string_of_int i ^ "_" ^ string_of_int n
  | Var x -> x
  | Pi (x, t, u) -> 
      let x_str = pretty_string_of_binder x in
      let t_str = pretty_string_of_expr t in
      let u_str = pretty_string_of_expr u in
      "Π "^ x_str ^ ":" ^ t_str ^ ", " ^ u_str
  | Lam (x, t, f, u, e) ->
      let x_str = pretty_string_of_binder x in
      let t_str = pretty_string_of_expr t in
      let f_str = pretty_string_of_expr f in
      let u_str = pretty_string_of_expr u in
      let e_str = pretty_string_of_expr e in
      "λ ("^ x_str ^ ":" ^ t_str ^ ") : (" ^ u_str ^ ") @ " ^ f_str ^ ", " ^ e_str
  | App (e1, e2) ->
      let e1_str = pretty_string_of_expr e1 in
      let e2_str = pretty_string_of_expr e2 in
      let e1_str = "(" ^ e1_str ^ ")" in
      let e2_str = "(" ^ e2_str ^ ")" in
      e1_str ^ " " ^ e2_str
  | Sigma xs ->
      let xs_str = List.map (fun (x, t) -> pretty_string_of_binder x ^ ":" ^ pretty_string_of_expr t) xs in
      "[" ^ String.concat ", " xs_str ^ "]"
  | Tuple es ->
      let es_str = List.map pretty_string_of_expr es in
      "(" ^ String.concat ", " es_str ^ ")"
  | Array (x, en, t) ->
      let x_str = pretty_string_of_binder x in
      let en_str = pretty_string_of_expr en in
      let t_str = pretty_string_of_expr t in
      "<<" ^ x_str ^ ":" ^ en_str ^ ";" ^ t_str ^ ">>"
  | Pack (x, en, e) ->
      let x_str = pretty_string_of_binder x in
      let en_str = pretty_string_of_expr en in
      let e_str = pretty_string_of_expr e in
      "<" ^ x_str ^ ":" ^ en_str ^ ";" ^ e_str ^ ">"
  | Extract (e, ei) ->
      let e_str = pretty_string_of_expr e in
      let ei_str = pretty_string_of_expr ei in
      e_str ^ "#" ^ ei_str
  






(*
   check out eta rule
   (x#0_3, x#1_3, x#2_3) -> x
*)
let example = 
    let e = Var "x" in
    Tuple [Extract (e, LitIdx (3, 0)); Extract (e, LitIdx (3, 1)); Extract (e, LitIdx (3, 2))]

(* let _ = print_endline (string_of_expr example) *)
let _ = print_endline (pretty_string_of_expr example)

let example_norm = 
  match normalize_step example with
  | Some e -> e
  | None -> example

(* let _ = print_endline (string_of_expr example_norm) *)
let _ = print_endline (pretty_string_of_expr example_norm)
let _ = print_endline ""

let efalse = LitIdx (2, 0)
(*
  T = Nat
  efalse = LitIdx (2, 0)
  t = 0
   ((lam (n:nat) : <<n;T>> @ efalse, <_:n;t>) 1) # 0_1
*)
let example2 = 
  let n = BNamed "n" in
  let t = LitNat 42 in
  let _T = Nat in
  (*
   (λ (n:<<_:n;ℕ>>) : (<_:n;0>) @ 0_2, 1) (0_1)  
   is no further normalized but is typed (TODO: check)
  *)
  (*
    (λ (n:ℕ) : (<<_:n;ℕ>>) @ 0_2, <_:n;42>) (1)#0_1
    (λ (n:ℕ) : (<<_:n;ℕ>>) @ 0_2, <_:n;42>) (1)

    (λ (n:ℕ) : (<<_:n;ℕ>>) @ 1_2, <_:n;42>) (1)#0_1
    (λ (n:ℕ) : (<<_:n;ℕ>>) @ 1_2, <_:n;42>) (1)
    <_:1;42>

    (λ (n:ℕ) : (<<_:n;ℕ>>) @ 1_2, <z:n;42>) (1)#0_1
    (λ (n:ℕ) : (<<_:n;ℕ>>) @ 1_2, <z:n;42>) (1)
    <z:1;42>
    (42)
    42
  *)
  Extract(
    App(
      Lam (n, Nat, efalse, Array (BAnon, Var "n", _T), Pack (BAnon, Var "n", t)),
      (* Lam (n, Nat, etrue , Array (BAnon, Var "n", _T), Pack (BAnon, Var "n", t)), *)
      (* Lam (n, Nat, etrue , Array (BAnon, Var "n", _T), Pack (BNamed "z", Var "n", t)), *)
      LitNat 1
    ),
    LitIdx (1, 0)
  )
  (* <_:1;t>#0_1 
    <_:1;0>#0_1
    <_:1;0>   
    no tuple expansion as unnamed
    - unnamed pack extract, or
    - extract 1 extract
    => if first both rules are same "precedence" (neither is more nested)
    if extract removed => leaves normalized term
      that is no further normalized
    TODO: here is a problem
  *)
  (* |> ignore; *)
  (* Extract (Pack (BAnon, LitNat 1, t), LitIdx (1, 0)) *)
  (*
     <_:z;0>#y => 0
  *)
  (* Extract (Pack (BAnon, Var "z", t), Var "y")  *)
  (* <i:1;t>#0_1 *)
  (*
    <i:1;0>#0_1
    <i:1;0>
    (0)
    0   
  *)
  (* Extract (Pack (BNamed "i", LitNat 1, t), LitIdx (1, 0)) *)

let refl_opt_closure f x = 
  match f x with
  | Some x' -> x'
  | None -> x

let norm_or_refl = refl_opt_closure normalize_step

let repeat_until_fixpoint f x =
  let rec loop x =
    let x' = f x in
    if x = x' then x else loop x'
  in
  loop x

let iter_norm_step ?(norm=norm_or_refl) = repeat_until_fixpoint (fun e -> 
    print_endline (pretty_string_of_expr e);
    norm e
  )

let _ = iter_norm_step example2
let _ = print_endline ""


(*
   TODO: full contextual step (left to right)
   full normalize
   typing
*)

(* try left to right if some subexpression can be normalized, if so, stop *)
let rec full_contextual_step e =
  (* TODO: first inner or first outer *)
  match normalize_step e with
  | Some e' -> Some e'
  | None -> 
      match e with
      | Star | Box | Bot | Nat | Idx | LitNat _ | LitIdx (_,_) | Var _ -> None
      | Pi (x, t, u) ->
        (match full_contextual_step t with
        | Some t' -> Some (Pi (x, t', u))
        | None -> 
          (match full_contextual_step u with
          | Some u' -> Some (Pi (x, t, u'))
          | None -> None))
      | Lam (x, t, f, u, e) ->
        (match full_contextual_step t with
        | Some t' -> Some (Lam (x, t', f, u, e))
        | None -> 
          (match full_contextual_step f with
          | Some f' -> Some (Lam (x, t, f', u, e))
          | None -> 
            (match full_contextual_step u with
            | Some u' -> Some (Lam (x, t, f, u', e))
            | None -> 
              (match full_contextual_step e with
              | Some e' -> Some (Lam (x, t, f, u, e'))
              | None -> None))))
      | App (e1, e2) ->
        (match full_contextual_step e1 with
        | Some e1' -> Some (App (e1', e2))
        | None -> 
          (match full_contextual_step e2 with
          | Some e2' -> Some (App (e1, e2'))
          | None -> None))
      | Sigma xs ->
        let rec fold_step xs =
          match xs with
          | [] -> None
          | (x, t) :: xs' ->
            (match full_contextual_step t with
            | Some t' -> Some (((x, t') :: xs'))
            | None -> 
              (match fold_step xs' with
              | Some xs'' -> Some (((x, t) :: xs''))
              | None -> None))
        in
        fold_step xs |> Option.map (fun xs -> Sigma xs)
      | Tuple es ->
        let rec fold_step es =
          match es with
          | [] -> None
          | e :: es' ->
            (match full_contextual_step e with
            | Some e' -> Some ((e' :: es'))
            | None -> 
              (match fold_step es' with
              | Some es'' -> Some ((e :: es''))
              | None -> None))
        in
        fold_step es |> Option.map (fun es -> Tuple es)
      | Array (x, en, t) ->
        (match full_contextual_step en with
        | Some en' -> Some (Array (x, en', t))
        | None -> 
          (match full_contextual_step t with
          | Some t' -> Some (Array (x, en, t'))
          | None -> None))
      | Pack (x, en, e) ->
        (match full_contextual_step en with
        | Some en' -> Some (Pack (x, en', e))
        | None -> 
          (match full_contextual_step e with
          | Some e' -> Some (Pack (x, en, e'))
          | None -> None))
      | Extract (e, ei) ->
        (match full_contextual_step e with
        | Some e' -> Some (Extract (e', ei))
        | None -> 
          (match full_contextual_step ei with
          | Some ei' -> Some (Extract (e, ei'))
          | None -> None)
        )
      
let example3 =
  (* test for deeper norm step *)
    (* (λ (n:ℕ) : (<<_:3;ℕ>>) @ 0_2, (1,1,1)) *)
  (*
    (λ (n:ℕ) : [ℕ,ℕ,ℕ] @ 0_2, (1,1,1))

    full context steps
    λ (n:ℕ) : ([_:ℕ, _:ℕ, _:ℕ]) @ 0_2, (1, 1, 1)
    λ (n:ℕ) : (<<_:3;ℕ>>) @ 0_2, (1, 1, 1)
    λ (n:ℕ) : (<<_:3;ℕ>>) @ 0_2, <_:3;1>
  *)
  Lam (BNamed "n", Nat, efalse, 
    (* Array (BAnon, LitNat 3, Nat), *)
    Sigma [(BAnon, Nat); (BAnon, Nat); (BAnon, Nat)],
  Tuple [LitNat 1; LitNat 1; LitNat 1])


(* let example3_norm = iter_norm_step example3 *)
let refl_full_contextual_step = refl_opt_closure full_contextual_step
let _ = iter_norm_step example3
let _ = print_endline ""
let _ = iter_norm_step ~norm:(refl_full_contextual_step) example3
let _ = print_endline ""

(* 
  normalize all subexpressions that itself
*)
let rec full_normalize_aux e = 
  norm_or_refl (match e with
  | Star | Box | Bot | Nat | Idx | LitNat _ | LitIdx (_,_) | Var _ -> e
  | Pi (x, t, u) -> Pi (x, full_normalize_aux t, full_normalize_aux u)
  | Lam (x, t, f, u, e) -> Lam (x, full_normalize_aux t, full_normalize_aux f, full_normalize_aux u, full_normalize_aux e)
  | App (e1, e2) -> App (full_normalize_aux e1, full_normalize_aux e2)
  | Sigma xs -> Sigma (List.map (fun (x, t) -> (x, full_normalize_aux t)) xs)
  | Tuple es -> Tuple (List.map full_normalize_aux es)  
  | Array (x, en, t) -> Array (x, full_normalize_aux en, full_normalize_aux t)
  | Pack (x, en, e) -> Pack (x, full_normalize_aux en, full_normalize_aux e)
  | Extract (e, ei) -> Extract (full_normalize_aux e, full_normalize_aux ei)
  )

let full_normalize = repeat_until_fixpoint full_normalize_aux

let _ = print_endline (pretty_string_of_expr (full_normalize example3))
let _ = print_endline ""

(*
   TODO: beta
*)
type ('a, 'b) map = ('a * 'b) list

let insert_name x t env = 
  match x with
  | BNamed x -> (x, t) :: env
  | BAnon -> env

let rec kind_dominance xs = 
  match xs with
  | [] -> Some Star
  | Star::xs' -> kind_dominance xs'
  | Box::xs' -> 
    ( match kind_dominance xs' with
      | Some s -> Some Box
      | None -> None
    )
  | _ -> None

let is_sort e = 
  match e with
  | Star | Box -> true
  | _ -> false


let subst'_norm mx es e = subst' mx es e |> full_normalize
(*
e, n, Ts: binder*expr

Tj' = Tj[e#0_n/x0]...[e#(j-1)_n/x_(j-1)] (j < n)
=> [
  T0,
  subst x0 (Extract e (LitIdx n i)) T1,
  ...
*)
let close_subst e n ts = 
  let rec close_subst' i ts = 
    match ts with
    | [] -> []
    | (x,t) :: tr -> 
      t::
      let tr' = close_subst' (i+1) tr in
      List.map (subst'_norm x (Extract(e,LitIdx(n,i)))) tr'
  in
  close_subst' 0 ts

let rec type_of (env: (string, expr) map) (e:expr) : expr option = 
  match e with 
  | Star -> Some Box
  | Bot -> Some Star
  | Nat -> Some Star
  | Idx -> Some (Pi (BAnon, Nat, Star))
  | LitNat n -> Some Nat

  | LitIdx (n, i) -> 
    if i < n then Some (App (Idx, LitNat n)) else None
  | Var x -> 
    (match List.assoc_opt x env with
    | Some _A -> 
        (match type_of env _A with
        | Some _ -> Some _A
        | None -> None)
    | None -> None)
  | Pi (x, t, u) -> 
    (match type_of env t, type_of (insert_name x t env) u with
    | Some sT, Some sU -> 
        (match kind_dominance [sT; sU] with
        | Some s -> Some s
        | None -> None)
    | _ -> None)

  | Lam (x, t, f, u, e) -> 
    let env' = insert_name x t env in
    (match type_of env t, type_of env' f, type_of env' u with
    | Some sT, Some sF, Some sU -> 
        if sF <> ebool then None else
        (* TODO: body assignable to U *)
        if type_of env' e <> Some u then None else
          (* (print_endline (Printf.sprintf "U: %s, E: %s" (pretty_string_of_expr sU) (pretty_string_of_expr (type_of env' e |> Option.get)));
          None) else *)
        Some (Pi (x, t, u))
    | _ -> None)
  | App (e1, e2) -> 
    (* TODO: e2 should be assignable t *)
    (match type_of env e1, type_of env e2 with
    | Some (Pi (x, t, u)), Some t2 -> 
        if t2 = t then Some (subst'_norm x e2 u) else None
    | _ -> None)

  (* this is like Coq (not paper) *)
  | Sigma [] -> Some Star
  | Sigma ((x, t) :: xs) -> 
    (match type_of env t, type_of (insert_name x t env) (Sigma xs) with
    | Some s, Some s' -> 
        (match kind_dominance [s; s'] with
        | Some s'' -> Some s''
        | None -> None)
    | _ -> None)
  | Tuple es -> 
    let ts = List.map (type_of env) es in
    if List.for_all (fun t -> Option.is_some t) ts then
      let ts = List.map (fun t -> Option.get t) ts in
      let ts = List.map (fun t -> (BAnon, t)) ts in
      let ts' = full_normalize (Sigma ts) in
      (* Sigma (List.map (fun t -> match t with Some t -> (BAnon, t) | None -> failwith "impossible") ts) *)
      Some ts'
    else None

  | Array (x, en, t) ->
    (
      match type_of env en, type_of (insert_name x en env) t with
      | Some sEN, Some s -> 
        if sEN <> Nat then None else
        if not (is_sort s) then None else 
        Some s
      | _ -> None
    )
  | Pack (x, en, e) -> 
    (
      match type_of env en, type_of (insert_name x (App(Idx,en)) env) e with
      | Some sEN, Some t -> 
        if sEN <> Nat then None else
          (* TODO: different from coq *)
        let _U = full_normalize (Array (x, en, t)) in
        Some _U
      | _ -> None
    )

  | Extract (e, ei) -> 
    (
      match type_of env e, type_of env ei with
      | Some (Array (x, en, t)), Some (App (Idx, en')) ->
        (* TODO: should size be normalized? *)
        if en <> en' then None else
        Some (subst'_norm x ei t)
      | Some (Sigma ts), Some (App (Idx, LitNat n)) ->
          if List.length ts <> n then None else
          let ts' = close_subst e n ts in
          let t = full_normalize (Tuple ts') in
          (match type_of env t with
          | Some s -> 
              let _U = full_normalize (Extract (t, ei)) in
              Some _U
          | None -> None)
      | _ -> None
    )

  | _ -> None

let string_of_option f = function
  | Some x -> f x
  | None -> "None"

let _ =
  print_endline (pretty_string_of_expr example);
  print_endline (string_of_option pretty_string_of_expr (type_of [("x", Sigma [(BAnon,Nat);(BAnon,Nat);(BAnon,Nat)])] example));
  let example = full_normalize example in
  print_endline (pretty_string_of_expr example);
  print_endline (string_of_option pretty_string_of_expr (type_of [("x", Sigma [(BAnon,Nat);(BAnon,Nat);(BAnon,Nat)])] example));
  print_endline "";

  print_endline (pretty_string_of_expr example2);
  print_endline (string_of_option pretty_string_of_expr (type_of [] example2));
  let example2 = full_normalize example2 in
  print_endline (pretty_string_of_expr example2);
  print_endline (string_of_option pretty_string_of_expr (type_of [] example2));
  print_endline "";

  print_endline (pretty_string_of_expr example3);
  print_endline (string_of_option pretty_string_of_expr (type_of [] example3));
  let example3 = full_normalize example3 in
  print_endline (pretty_string_of_expr example3);
  print_endline (string_of_option pretty_string_of_expr (type_of [] example3));
  print_endline ""


(* let rec expressions cost = 
  let identifiers = ["x"; "y"; "z"] in
  let rec_expr = expressions (cost - 1) in
  if cost <= 0 then [] else
    [Star; Box; Bot; Nat; Idx] @
    (List.init 3 (fun i -> LitNat i)) @
    List.concat (List.init 3 (fun n -> List.init 3 (fun i -> LitIdx (n, i))) ) @
    List.map (fun x -> Var x) identifiers @ *)
    
(*
   random fuzzer for expressions
*)
(* let _ = Random.self_init () *)
let _ = Random.init 42

let fuzz_identifier () = 
  let identifiers = ["x"; "y"; "z"] in
  List.nth identifiers (Random.int (List.length identifiers))

let rec random_expression depth = 
  if depth <= 0 then 
    (* 
      atomic expression: ListNat, LitIdx, Var
    *)
    match Random.int 3 with
    | 0 -> LitNat (Random.int 4)
    | 1 -> let n = 1+Random.int 3 in LitIdx (n, Random.int n)
    | 2 -> Var (fuzz_identifier ())
    | _ -> failwith "impossible"
  else
    (*
       Lam, App, Tuple, Pack, Extract
    *)
    match Random.int 5 with
    (* match 3 with *)
    | 0 -> (* Lam *)
      let x = BNamed (fuzz_identifier ()) in
      let t = random_type (depth - 1) in
      let f = List.nth [etrue; efalse] (Random.int 2) in
      let u = random_type (depth - 1) in
      let e = random_expression (depth - 1) in
      Lam (x, t, f, u, e)
    | 1 -> (* App *)
      let e1 = random_expression (depth - 1) in
      let e2 = random_expression (depth - 1) in
      App (e1, e2)
    | 2 -> (* Tuple *)
      let n = Random.int 4 in
      Tuple (List.init n (fun _ -> random_expression (depth - 1)))
    | 3 -> (* Pack *)
      let x = BNamed (fuzz_identifier ()) in
      (* let en = random_expression (depth - 1) in
      let e = random_expression (depth - 1) in *)
      (* let en = random_expression 0 in
      let e = random_expression 0 in
      Pack (x, en, e) *)
      Pack (x, LitNat (Random.int 4), random_expression (depth - 1))
    | 4 -> (* Extract *)
      let e = random_expression (depth - 1) in
      let ei = random_expression (depth - 1) in
      Extract (e, ei)
    | _ -> failwith "impossible"
and random_type depth =
  if depth <= 0 then 
    match Random.int 4 with
    | 0 -> Star
    | 1 -> Box
    | 2 -> Nat
    | 3 -> App(Idx, LitNat (Random.int 4))
    | 4 -> Var (fuzz_identifier ())
    | _ -> failwith "impossible"
  else
    (*
       Pi, Sigma, Array
    *)
    match Random.int 3 with
    (* match 2 with *)
    | 0 -> (* Pi *)
      let x = BNamed (fuzz_identifier ()) in
      let t = random_type (depth - 1) in
      let u = random_type (depth - 1) in
      Pi (x, t, u)
    | 1 -> (* Sigma *)
      let n = Random.int 4 in
      Sigma (List.init n (fun _ -> (BNamed (fuzz_identifier ()), random_type (depth - 1))))
    | 2 -> (* Array *)
      let x = BNamed (fuzz_identifier ()) in
      (* let en = random_expression (depth - 1) in *)
      let en = LitNat (Random.int 4) in
      let t = random_type (depth - 1) in
      Array (x, en, t)
    | _ -> failwith "impossible"


(*
   generate 1000000 random expressions and filter out those that are typed
*)
let expressions_rand_5 = List.init 1000000 (fun _ -> random_expression 3)
(* let expressions_rand_5 = List.init 1000000 (fun _ -> random_expression 5) *)
(* let expressions_rand_5 = List.init 10000 (fun _ -> random_expression 10) *)
  |> List.sort_uniq compare
  |> List.filter (fun e -> type_of [] e <> None)

(* let _ =
  List.iter (fun e -> print_endline (pretty_string_of_expr e)) expressions_rand_5;
  print_endline "" *)

let errors = 
    expressions_rand_5 
    |> List.filter(fun e ->
      let e' = full_normalize e in
      let _A = Option.get (type_of [] e) in
      let _A' = Option.get (type_of [] e') in
      (* full_normalize (Option.get (type_of [] e)) <> Option.get (type_of [] (full_normalize e)) *)
      (*
        if e:A
        then full_normalize e:full_normalize A

        => find expressions where type_of (normalize e) <> normalize (type_of e)
      *)
      full_normalize _A <> _A'
      

    )

let _ =
  List.iter (fun e -> 
    (* Printf.printf "Expr: %s\nExpr: %s\nType: %s\nNorm: %s\nType: %s\nType: %s\n\n"  *)
    (* Printf.printf "Expr: %s\nExpr: %s\nType: %s\nNorm: %s\nType: %s\n\n" 
      (pretty_string_of_expr e) 
      (string_of_expr e) 
      (string_of_option pretty_string_of_expr (type_of [] e))
      (pretty_string_of_expr (full_normalize e))
      (string_of_option pretty_string_of_expr (type_of [] (full_normalize e))) *)
      (* (string_of_option string_of_expr (type_of [] (full_normalize e))) *)

    let e' = full_normalize e in (* = e_norm *)
    let _A = Option.get (type_of [] e) in
    let _A' = Option.get (type_of [] e') in
    let _A_norm = full_normalize _A in

    Printf.printf "e   : %s\n" (pretty_string_of_expr e);
    Printf.printf "A   : %s\n" (pretty_string_of_expr _A);
    Printf.printf "e'  : %s\n" (pretty_string_of_expr e');
    Printf.printf "A'  : %s\n" (pretty_string_of_expr _A');
    Printf.printf "An  : %s\n" (pretty_string_of_expr _A_norm);
    print_endline ""
  ) errors;
  print_endline ""




(* let rec expressions cost = 
  let identifiers = ["x"; "y"; "z"] in
  if cost <= 0 then [] else
  let rec_expr = expressions (cost - 1) in
  let rec_types = types (cost - 1) in
  (List.init 3 (fun i -> LitNat i)) @
  List.concat (List.init 3 (fun n -> List.init 3 (fun i -> LitIdx (n, i))) ) @
  List.map (fun x -> Var x) identifiers @
  List.concat_map (fun x -> 
    List.concat_map (fun t -> 
      List.concat_map (fun u -> 
        List.concat_map (fun e -> 
          List.map (fun f -> 
            Lam (BNamed x, t, f, u, e)
          ) [etrue; efalse]
        ) rec_expr
      ) rec_types
    ) rec_types
  ) identifiers @
  List.concat_map (fun e1 -> 
    List.map (fun e2 -> 
      App (e1, e2)
    ) rec_expr
  ) rec_expr @
  List.concat (
    List.init 3 (fun n -> 
      List.init n (fun i -> 
        Tuple (List.init n (fun j -> Extract (Var "x", LitIdx (n, j))))
      )
    )
  ) @
  []
    
and types cost =
  let identifiers = ["x"; "y"; "z"] in
  if cost <= 0 then [] else
  let rec_expr = expressions (cost - 1) in
  let rec_types = types (cost - 1) in
  [Star; Box; Bot; Nat; Idx] @
  List.concat_map (fun x -> 
    List.concat_map (fun t -> 
      List.map (fun u -> Pi (BNamed x, t, u)) rec_types
    ) rec_types
  ) identifiers @
  []

let expressions_d1 = expressions 1
let expressions_d2 = expressions 2
(* let expressions_d3 = expressions 3 *)

let expressions_d2 = List.filter (fun e -> type_of [] e <> None) expressions_d2
(* let expressions_d3 = List.filter (fun e -> type_of [] e <> None) expressions_d3 *)

let _ =
  List.iter (fun e -> print_endline (pretty_string_of_expr e)) expressions_d2;
  print_endline "" *)
