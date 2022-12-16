namespace Self.Core

module Kore =

  let private hashNeg = hash "^^^"
  let private hashPos = hash "###"
  let private hashRef = hash "Var"
  let private hashLam = hash "Lam"
  let private hashApp = hash "App"
  let private hashLet = hash "Let"
  let private hashAll = hash "All"
  let private hashAnn = hash "Ann"
  let private hashLoc = hash "Loc"
  let private hashTyp = hash "Typ"

  type Hoas =
    | Var of int
    | Ref of string
    | Lam of bool * string * (Hoas -> Hoas)
    | App of bool * Hoas * Hoas
    | Let of bool * string * Hoas * (Hoas -> Hoas)
    | All of bool * string * string * Hoas * (Hoas -> Hoas -> Hoas)
    | Ann of bool * Hoas * Hoas
    | Loc of int * int * Hoas
    | Typ
  
    static member hash dep trm =
      match trm with
      | Var i when i < 0 -> hashNeg + dep + i
      | Var i -> hashPos + i
      | Ref n -> hashRef + hash n
      | Lam (_, _, b) -> hashLam + Hoas.hash (dep + 1) (b (Var -(dep + 1)))
      | App (_, f, a) -> hashApp + Hoas.hash dep f + Hoas.hash dep a
      | Let (_, _, e, b) ->
        hashLet + Hoas.hash dep e + Hoas.hash (dep + 1) (b (Var -(dep + 1)))
      | All (_, _, _, d, c) ->
        hashAll + Hoas.hash dep d + Hoas.hash (dep + 2) (c (Var -(dep + 1)) (Var -(dep + 2)))
      | Ann (_, e, _) -> hashAnn + Hoas.hash dep e
      | Loc (_, _, e) -> hashLoc + Hoas.hash dep e
      | Typ -> hashTyp
    

  type Def = { Term : Hoas; Type : Hoas }

  type Defs = Map<string, Def>

  let rec reduce defs era trm =
    match trm with
    | Var _ -> trm
    | Ref n ->
      match Map.tryFind n defs with
      | Some def ->
        let got = def.Term
        match got with
        | Ref n' when n' = n  -> got
        | Loc _ -> got
        | _ -> reduce defs era got
      | None -> Ref n
    | Lam (e, _, b) ->
      if era && e then
        reduce defs era (b (Lam (false, "", fun x -> x)))
      else trm
    | App (e, f, a) ->
      if era && e then
        reduce defs era f
      else
        match reduce defs era f with
        | Lam (_, _, b) -> reduce defs era (b a)
        | f' -> App (e, f', a)
    | Let (_, _, e, b) -> reduce defs era (b e)
    | All _ -> trm
    | Ann (_, e, _) -> reduce defs era e
    | Loc (_, _, e) -> reduce defs era e 
    | Typ ->  trm

  let rec normalize defs (seen : Set<int>) era trm =
    let red = reduce defs era trm 
    let trmH = Hoas.hash 0 trm
    let redH = Hoas.hash 0 red
    if Set.contains trmH seen || Set.contains redH seen then
      red // MaiaVictor has trm ...?
    else
      let seen = seen |> Set.add trmH |> Set.add redH
      let inline norm t = normalize defs seen era t
      match red with
      | Var _ -> red
      | Ref _ -> red
      | Lam (e, x, b) -> Lam (e, x, fun x -> norm (b x)) 
      | App (e, f, a) -> App (e, norm f, norm a)
      | Let (_, _, e, b) -> norm (b e)
      | All (e, s, x, d, c) -> All (e, s, x, norm d, fun s x -> norm (c s x))
      | Ann (_, e, _) -> norm e
      | Loc (_, _, e) -> norm e
      | Typ -> red
  
  let private hashEq = hash "=="

  let rec equal defs seen dep ta tb =
    let ta1 = reduce defs true ta
    let tb1 = reduce defs true tb
    let taH = Hoas.hash 0 ta1
    let tbH = Hoas.hash 0 tb1
    let eqH = hashEq + taH + tbH
    if (taH = tbH) || (Set.contains eqH seen) then
      true
    else
      let seen = Set.add eqH seen
      match ta1, tb1 with
      | Var _, Var _ -> false