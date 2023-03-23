namespace Self.Core

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
