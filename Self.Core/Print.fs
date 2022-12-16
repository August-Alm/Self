namespace Self.Core

module Print =

  open Term
  open System.Text

  type R = private { _Num : int }
  module E =
    let num r = r._Num

  let inline append (sb : StringBuilder) (s : string) =
    sb.Append s |> ignore
  
  let rec appendTerm sb (trm : Term) =
    let inline bind x b = b (Var (x, 0))
    let inline bind2 s x c = c (Var (s, 1)) (Var (x, 0))
    match trm with
    | Var (n, _) -> append sb n
    | Ref (n, _) -> append sb n
    | Lam (e, x, b) ->
      append sb "lam "
      append sb <| if e then $"{{x}}. " else $"{x}. "
      appendTerm sb (bind x b)
    | App (e, f, a) ->
      appendTerm sb f
      append sb <| if e then "{" else "("
      appendTerm sb a
      append sb <| if e then "}" else ")"
    | Fix (f, b) ->
      append sb "fix f. "
      appendTerm sb (bind f b)
    | All (e, x, d, c) ->
      if e then
        append sb (sprintf "{%s: " x)
        appendTerm sb d
        append sb "} "
        appendTerm sb (bind x c)
      elif System.String.IsNullOrEmpty x then
        match d with
        | All (false, _, _, _) ->
          append sb "("
          appendTerm sb d
          append sb ")"
          append sb " -> "
          appendTerm sb (bind "" c)
        | _ ->
          appendTerm sb d
          append sb " -> "
          appendTerm sb (bind "" c)
      else
        append sb $"({x}: "
        appendTerm sb d
        append sb ") -> "
        appendTerm sb (bind x c)
    | Slf (s, x, d, c) ->
      append sb $"@{s} "
      append sb (sprintf "{%s: " x)
      appendTerm sb d
      append sb "} "
      appendTerm sb (bind2 s x c)
    | Ann (d, u, t) ->
      if d then
        appendTerm sb u
      else
        append sb "("
        appendTerm sb u
        append sb ": "
        appendTerm sb t
        append sb ")"
    | Typ -> append sb "Typ"
  
  let printTerm trm =
    let sb = StringBuilder 256
    appendTerm sb trm
    sb.ToString () |> printfn "%s"
  
  let printCtx (ctx : Ctx) =
    let sb = StringBuilder 256
    printfn "Context:"
    for n, t in ctx do
      appendTerm sb t
      printfn "%s: %s" n (sb.ToString ())
      sb.Clear () |> ignore
