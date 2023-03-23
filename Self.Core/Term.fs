namespace Self.Core


module Term =

  open BytesBuilder
  open System.Collections.Generic

  type Term =
    | Var of string * int // de Bruijn
    | Ref of string * int // definition index
    | Lam of bool * string * (Term -> Term)
    | App of bool * Term * Term
    | Fix of string * (Term -> Term)
    | All of bool * string * Term * (Term -> Term) 
    | Slf of string * (Term -> Term)
    | New of string * Term
    | Use of Term
    | Ann of bool * Term * Term
    | Typ
  
  type Def = {Name : string; Type : Term; Term : Term}
  type Module = {Defs : Def[]}

  let rec serialize dep (bb : BytesBuilder) (t : Term) =
    let inline ser t = serialize dep bb t
    let inline serbind x b = serialize (dep + 1) bb (b (Var (x, -dep - 1)))
    let inline addEras b = if b then bb.Add 1uy else bb.Add 0uy
    match t with
    | Var (_, i) when i >= 0 -> bb.Add 'v'B; bb.Add i
    | Var (_, i) -> bb.Add 'v'B; bb.Add (i + dep)
    | Ref (_, i) -> bb.Add 'r'B; bb.Add  i
    | Lam (e, x, b) -> bb.Add 'l'B; addEras e; serbind x b
    | Fix (f, b) -> bb.Add 'F'B; serbind f b
    | App (e, f, a) -> bb.Add 'a'B; addEras e; ser f; ser a
    | All (e, x, d, c) -> bb.Add 'A'B; addEras e; ser d; serbind x c
    | Slf (s, t) -> bb.Add 'S'B; bb.Add s; serbind s t
    | New (s, t) -> bb.Add 'N'B; bb.Add s; ser t
    | Use t -> bb.Add 'U'B; ser t
    | Ann (_, u, _) -> ser u
    | Typ -> bb.Add 'T'B

  let serializeTerm t =
    use bb = new BytesBuilder 256
    serialize 0 bb t
    bb.GetBytes ()
  
  let private md5 = System.Security.Cryptography.MD5.Create ()

  let hashTerm t = hashBytes md5 (serializeTerm t)

  // Evaluation

  let rec reduce (md : Module) erase trm =
    let inline go trm = reduce md erase trm
    match trm with
    | Ref (_, i) -> go md.Defs[i].Term
    | Lam (e, _, b) when e && erase -> go (b (Lam (false, "", fun x -> x)))
    | Fix (f, b) -> go (b (Fix (f, b)))
    | App (e, f, a) ->
      if e && erase then go f
      else match go f with Lam (_, _, b) -> go (b a) | _ -> trm 
    | Ann (_, u, _) -> go u
    | New (s, t) -> New (s, go t)
    | Use (New (_, t)) -> go t
    | Use t -> Use (go t)
    | _ -> trm
  
  type Seen = HashSet<System.Guid>

  let rec normalize (md : Module) (seen : Seen) erased trm =
    let inline go trm = normalize md seen erased trm
    let trm' = reduce md erased trm
    let hsh = hashTerm trm
    let hsh' = hashTerm trm'
    if (not (seen.Add hsh)) || (not (seen.Add hsh')) then trm'
    else
      match trm' with
      | Lam (e, x, b) -> Lam (e, x, fun x -> go (b x))
      | Fix (f, b) -> go (b (Fix (f, b)))
      | App (e, f, a) -> App (e, go f, go a)
      | All (e, x, d, c) -> All (e, x, go d, fun x -> go (c x))
      | Slf (s, t) -> Slf (s, fun s -> go (t s))
      | New (s, t) -> New (s, go t)
      | Use t -> Use (go t)
      | Ann (_, u, _) -> go u
      | _ -> trm'

  type Eq = HashSet<struct (System.Guid * System.Guid)>
  
  let equal
    (eq : Eq) (bb : BytesBuilder) (md : Module) dep
    (trm1 : Term) (trm2 : Term) =
    let rec go dep trm1 trm2 =
      let t1 = reduce md false trm1
      let t2 = reduce md false trm2
      serialize 0 bb t1
      let ser1 = bb.GetBytes ()
      let h1 = hashBytes md5 ser1
      serialize 0 bb t2
      let ser2 = (bb.GetBytes ()).Slice ser1.Length
      let h2 = hashBytes md5 ser2
      if
        h1 = h2 ||
        not (eq.Add (struct (h1, h2))) ||
        not (eq.Add (struct (h2, h1)))
      then
        bb.Clear (); true
      else
        bb.Clear ()
        let inline bind x b = b (Var (x, dep))
        match t1, t2 with
        | Lam (e, x, b), Lam (e', x', b') ->
          e = e' && go (dep + 1) (bind x b) (bind x' b')
        | App (e, f, a), App (e', f', a') ->
          e = e' && go dep f f' && go dep a a'
        | All (e, x, d, c), All (e', x', d', c') ->
          e = e' && go dep d d' && go (dep + 1) (bind x c) (bind x' c')
        | Slf (s, t), Slf (s', t') ->
          s = s' && go (dep + 1) (bind s t) (bind s' t')
        | Ann (_, u, _), Ann (_, u', _) -> go dep u u'
        | _ -> false
    go dep trm1 trm2
  
  // Type-checking

  type Ctx = (string * Term) list
  let inline depth (ctx : Ctx) = ctx.Length

  exception TypeMismatch of Ctx * Term * Term
  exception NonFunctionLambda of Ctx * Term * Term
  exception ErasureMismatch of Ctx * Term * Term
  exception NonFunctionApplication of Ctx * Term * Term
  exception NotInferrable of Ctx * Term
  
  let rec check eq (bb : BytesBuilder) (md : Module) (ctx : Ctx) trm typ =
    match trm with
    | Lam (e, x, b) ->
     let tty = reduce md false typ
     match tty with
      | All (e', _, d, c) ->
        if e' <> e then
          raise <| ErasureMismatch (ctx, trm, tty)
        else
          let xVar = Ann (true, Var (x, depth ctx), d)
          check eq bb md ((x, d) :: ctx) (b xVar) (c xVar)
      | _ -> raise <| NonFunctionLambda (ctx, trm, tty)
    | New (s, t) ->
      let tty = reduce md false typ
      match tty with
      | Slf (s', a) ->
        if s <> s' then
          failwith $"Self-names {s} and {s'} do not match."
        else
          let sVar = Ann (true, trm, typ)
          check eq bb md ctx t (a sVar)
      | _ -> failwith "New-term of non-self type."
    | Fix (f, b) -> check eq bb md ctx (b (Fix (f, b))) typ
    | _ ->
      let infr = infer eq bb md ctx trm
      if not (equal eq bb md (depth ctx) infr typ) then
        raise <| TypeMismatch (ctx, infr, typ)
  
  and infer eq bb md ctx trm =
    match trm with
    | Var _ -> trm
    | Ref (_, i) -> md.Defs[i].Type
    | App (e, f, a) ->
      match reduce md false (infer eq bb md ctx f) with
      | All (e', _, d, c) as tty ->
        if e' <> e then
          raise <| ErasureMismatch (ctx, trm, tty)
        else
          let nVar = Ann (true, a, d)
          check eq bb md ctx a d
          c nVar
      | tty -> raise <| NonFunctionApplication (ctx, trm, tty)
    | All (_, x, d, c) ->
      let xVar = Ann (true, Var (x, depth ctx), d)
      check eq bb md ctx d Typ
      check eq bb md ((x, xVar) :: ctx) (c xVar) Typ
      Typ
    | Slf (s, t) ->
      let sVar = Ann (true, Var (s, depth ctx), trm)
      check eq bb md ctx (t sVar) Typ
      Typ
    | Use t ->
      match infer eq bb md ctx t with
      | Slf (_, ty) -> ty t
      | _ -> failwith "Use of non-self type."
    | Typ -> Typ
    | Ann (d, u, t) -> (if not d then check eq bb md ctx u t); t
    | _ -> raise <| NotInferrable (ctx, trm)

  // Work in progress.
  let rec erase md trm =
    normalize md (Seen ()) true trm
    (*
    match trm with
    | Lam (true, _, b) -> erase (b (Var ("<erased>", 0)))
    | Lam (e, x, b) -> Lam (e, x, erase << b)
    | App (true, f, _) -> erase f
    | App (_, f, Var ("<erased>", _)) -> erase f
    | App (e, App (true, Var (n, i), _), _) -> Var (n, i) 
    | App (e, f, a) -> App (e, erase f, erase a)
    | All (true, x, Typ, c) -> All (true, x, Typ, erase << c)
    | All (false, _, d, c) -> All (false, "", erase d, erase << c)
    | All (e, x, d, c) -> erase (c (Var ("<erased>", 0)))
    | Slf (s, x, d, c) ->
      All (true, x, Typ, fun y -> erase (c (Var ("<erased>", 0)) (App (true, Var (x, 1), y))))
    | _ -> trm
    *)