namespace Self

module Program =

  open Self.Syntax.PTerm
  open Self.Syntax.Frontend
  open Self.Core.BytesBuilder
  open Self.Core.Term
  open Self.Core.Print
  
  [<EntryPoint>]  
  let main argv =
  
    try
      let md = parseFile "test.slf" |> toModule 
      let eq = Eq ()
      use bb = new BytesBuilder 1024
      for def in md.Defs do
        check eq bb md [] def.Term def.Type
      printfn "All terms check!"
    with
    | :? TypeMismatch as e ->
      let ctx, t1, t2 = e.Data0, e.Data1, e.Data2
      printfn "Type mismatch:"; printTerm t1; printTerm t2
      printCtx ctx
    | :? ErasureMismatch as e ->
      let ctx, t1, t2 = e.Data0, e.Data1, e.Data2
      printfn "Erasure mismatch:"; printTerm t1; printTerm t2
      printCtx ctx
  
    0