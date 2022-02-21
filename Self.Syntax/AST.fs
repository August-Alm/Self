namespace Self.Syntax

module PTerm =

  open Self.Core.Term

  type PTerm =
    | PVar of string 
    | PLam of bool * string * PTerm
    | PApp of bool * PTerm * PTerm
    | PLet of string * PTerm * PTerm
    | PFix of string * PTerm
    | PAll of bool * string * PTerm * PTerm
    | PSlf of string * string * PTerm * PTerm
    | PAnn of PTerm * PTerm
    | PTyp

  type PDef = {Line : int; Name : string; PType : PTerm; PTerm : PTerm}

  type PDefs = Map<string, PDef>

  let toModule (defs : PDefs) : Module =
    let names = defs |> Seq.map (fun kv -> kv.Key) |> Seq.toArray    
    let varOrRef (env : (string * Term) list) n =
      let inline hasstring n = fun xt -> let x, _ = xt in x = n
      match List.tryFindIndex (hasstring n) env with
      | Some i -> Var (n, i)
      | None ->
        match Array.tryFindIndex (fun n' -> n' = n) names with
        | Some i -> Ref (n, i)
        | None -> failwith $"Unbound variable {n}."
    let rec go env t =
      match t with
      | PVar n ->
        match varOrRef env n with
        | Var (_, i) when i < env.Length -> let _, t = env[i] in t 
        | x -> x
      | PLam (e, x, b) -> Lam (e, x, fun xt -> go ((x, xt) :: env) b)
      | PApp (e, f, a) -> App (e, go env f, go env a)
      | PFix (f, b) -> Fix (f, fun ft -> go ((f, ft) :: env) b)
      | PAll (e, x, d, c) -> All (e, x, go env d, fun xt -> go ((x, xt) :: env) c)
      | PLet (x, e, t) -> go ((x, go env e) :: env) t
      | PSlf (s, x, d, c) ->
        Slf (s, x, go env d, fun st xt -> go ((x, xt) :: (s, st) :: env) c)
      | PAnn (u, t) -> Ann (false, go env u, go env t)
      | PTyp _ -> Typ
    {Defs =
      names |> Array.map (fun n ->
        let def = defs[n]
        {Name = n; Type = go [] def.PType; Term = go [] def.PTerm})}