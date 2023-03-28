namespace Self.Core

module Sweet =

  open System.Collections.Generic

  type Name = string

  type Term =
    | Var of Name
    | Lam of Name * Term
    | App of Term * Term
    | Pi of Name * Term * Term
    | Self of Name * Term
    | New of Name * Term
    | Use of Term
    | Let of Name * Term * Term * Term
    | Typ

  type Def = { Type : Term; Expr : Term }

  type Defs = Dictionary<Name, Def>

  type Value =
    | VVar of Name
    | VRef of Name
    | VLam of Name * (Value -> Value)
    | VApp of Value * Value
    | VPi of Name * Value * (Value -> Value)
    | VSelf of Name * (Value -> Value)
    | VNew of Name * Value
    | VUse of Value
    | VTyp
  
  type VDef = { Type : Value; Expr : Value }

  type VDefs = Dictionary<Name, VDef>

  type VEnv = (Name * Value) list

  let rec lookup (x : Name) env =
    match env with
    | [] -> ValueNone
    | (x', t) :: _ when x' = x -> ValueSome t
    | _ :: env' -> lookup x env'

  let rec fresh (ns : Name list) (x : Name) =
    if x = "_" then x
    elif List.contains x ns then fresh ns $"{x}'"
    else x
  
  let inline (@@) (t : Value) (u : Value) =
    match t with
    | VLam (_, t) -> t u
    | _ -> VApp (t, u)
  
  let rec eval (defs : Defs) (vdefs : VDefs) (env : VEnv) (trm : Term) : Value =
    let inline go t = eval defs vdefs env t
    let inline gobind x t = fun u -> eval defs vdefs ((x, u) :: env) t
    match trm with
    | Var x ->
      match lookup x env with
      | ValueSome t -> t
      | ValueNone ->
        match vdefs.TryGetValue x with
        | true, t -> t.Expr
        | false, _ ->
          let def = defs[x]
          let vdef = { Type = go def.Type; Expr = go def.Expr }
          vdefs.Add (x, vdef)
          VRef x
    | Lam (x, t) -> VLam (x, gobind x t) 
    | App (t, u) -> (go t) @@ (go u)
    | Pi (x, a, b) -> VPi (x, go a, gobind x b)
    | Self (x, t) -> VSelf (x, gobind x t)
    | New (x, t) -> VNew (x, go t)
    | Use t -> VUse (go t)
    | Let (x, _, t, u) -> eval defs vdefs ((x, go t) :: env) u
    | Typ -> VTyp
  
  let rec quote (vdefs : VDefs) (ns : Name list) (t : Value) : Term =
    match t with
    | VVar x -> Var x
    | VRef x -> quote vdefs ns (vdefs[x].Expr)
    | VLam (x, t) ->
      let x = fresh ns x
      Lam (x, quote vdefs (x :: ns) (t (VVar x)))
    | VApp (t, u) -> App (quote vdefs ns t, quote vdefs ns u)
    | VPi (x, a, b) ->
      let x = fresh ns x
      Pi (x, quote vdefs ns a, quote vdefs ns (b (VVar x)))
    | VSelf (x, t) -> Self (x, quote vdefs ns (t (VVar x)))
    | VNew (x, t) -> New (x, quote vdefs ns t)
    | VUse t -> Use (quote vdefs ns t)
    | VTyp -> Typ
  
  let normalize defs vdefs env trm =
    quote vdefs (List.map (fun (x, _) -> x) env) (eval defs vdefs  env trm)
  
  type Ctx = (Name * Value) list

  let rec check
    (defs : Defs) (vdefs : VDefs) (env : VEnv) (ctx : Ctx) (trm : Term) (typ : Value) : Term =
    match trm with
    | Lam (x, t) ->
      match typ with
      | VPi (_, a, b) ->
        let ctx' = (x, a) :: ctx
        check defs vdefs env ctx' t (b (VVar x)) 
  
  and infer
    (defs : Defs) (vdefs : VDefs) (env : VEnv) (ctx : Ctx) (trm : Term) : Value =
    match trm with
    | Var x ->
      match lookup x ctx with
      | ValueSome tty -> tty
      | ValueNone -> failwith $"can not infer type of {x}"

module Kore =

  type Term =
    | Var of string * int // name * de Bruijn
    | Ref of string // Reference to definition.
    | Lam of string * (Term -> Term)
    | App of Term * Term
    | Fun of string * Term * (Term -> Term)
    | Slf of string * (Term -> Term)
    | New of string * Term
    | Use of Term
    | Ann of bool * Term * Term
    | Typ
  and Binding =
    { Name : string; Type : Term; Erased : bool }
  and Data =
    { Name : string; Parameters : Binding list; Body : Term -> Term }
  
  /// Alpha equality, except references are by reference.
  let rec alphaeq trm trm' =
    match trm, trm' with
    | Var (_, i), Var (_, i') -> i = i'
    | Ref x, Ref x' -> x = x'
    | Lam ( _, b), Lam ( _, b') ->
      let v = Var ("", 0) in alphaeq (b v) (b' v)
    | App (f, a), App (f', a') ->
      (alphaeq f f') && (alphaeq a a')
    | Fun (_, d, c), Fun (_, d', c') ->
      let v = Var ("", 0) in (alphaeq d d') && (alphaeq (c v) (c' v))
    | Slf (_, t), Slf (_, t') ->
      let v = Var ("", 0) in alphaeq (t v) (t' v)
    | Ann (d, u, t), Ann (d', u', t') ->
      (d = d') && (alphaeq u u') && (alphaeq t t')
    | Typ, Typ -> true
    | _ -> false
  
  type Def = { Name : string; Type : Term; Expr : Term }


  type Defs = Map<string, Def>

  let rec reduce defs trm =
    let inline go trm = reduce defs trm
    match trm with
    | Ref x -> go (Map.find x defs).Expr
    | App (f, a) ->
      match go f with
      | Lam (_, b) -> go (b a)
      | f' -> App (f', a)
    | Ann (_, u, _) -> go u
    | _ -> trm
  
  let rec normalize defs trm =
    let inline go trm = normalize defs trm
    match reduce defs trm with
    | Lam (x, b) -> Lam (x, fun x -> go (b x))
    | App (f, a) -> App (go f, go a)
    | Fun (x, d, c) -> Fun (x, go d, fun x -> go (c x))
    | Slf (s, t) -> Slf (s, fun s -> go (t s))
    | Ann (_ , u, _) -> go u
    | trm' -> trm'
  
  type Ctx = list<string * Term>

  let inline depth (ctx : Ctx) = ctx.Length
  
  let rec findType x ctx =
    match ctx with
    | (y, t) :: _ when y = x -> t
    | _ :: ctx' -> findType x ctx'
    | [] -> failwith $"Variable {x} has no type in context."

  exception TypeMismatch of Ctx * Term * Term
  exception NonFunctionLambda of Ctx * Term * Term
  exception NonFunctionType of Ctx * Term * Term
  exception ErasureMismatch of Ctx * Term * Term
  exception NonFunctionApplication of Ctx * Term * Term
  exception NotInferrable of Ctx * Term

  let rec check defs ctx trm typ =
    match trm with
    | Lam (x, b) ->
      let typ' = normalize defs typ
      match typ' with
      | Fun (_, d, c) ->
        check defs ctx d Typ
        let xVar = Ann (true, Var (x, depth ctx), d)
        check defs ((x, d) :: ctx) (b xVar) (c xVar)
      | typ' -> raise <| NonFunctionLambda (ctx, trm, typ')
    | New (s, g) -> 
      let typ' = normalize defs typ
      match typ' with
      | Slf (_, t) ->
        check defs ctx typ' Typ
        let sVar = Ann (true, trm, t trm)
        check defs ctx trm (t sVar)
    | _ ->
      let inferred = infer defs ctx trm
      if not (alphaeq inferred typ) then
        // try to unify!
        raise <| TypeMismatch (ctx, inferred, typ)

  and infer defs ctx trm =
    match trm with
    | Var (x, _) -> findType x ctx
    | Ref x ->
      let def = Map.find x defs
      check defs ctx def.Expr def.Type
      def.Type
    | App (f, a) ->
      let rec unifySelf tt =
        match tt with
        | Fun (_, d, c) ->
          let aVar = Ann (true, a, d)
          check defs ctx a d
          c aVar
        | Slf (_, t) -> unifySelf (t (Ann (true, f, tt)))
        | _ -> raise <| NonFunctionApplication (ctx, f, tt)
      unifySelf (normalize defs (infer defs ctx f))
    | Fun (x, d, c) ->
      let xVar = Ann (true, Var (x, depth ctx), d)
      check defs ctx d Typ
      check defs ((x, d) :: ctx) (c xVar) Typ
      Typ
    | Slf (s, t) ->
      let sVar = Ann (true, Var (s, depth ctx), trm)
      check defs ((s, trm) :: ctx) (t sVar) Typ
      Typ
    | Ann (d, u, t) -> (if not d then check defs ctx u t); t
    | Typ -> Typ
    | _ -> raise <| NotInferrable (ctx, trm)
