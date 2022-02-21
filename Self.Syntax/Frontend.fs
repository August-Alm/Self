namespace Self.Syntax

module Frontend =

  open FSharp.Text.Lexing

  let parseFile (path : string) =
    use input = new System.IO.StreamReader(path)
    let lexbuf = LexBuffer<char>.FromTextReader input
    try
      Parser.defs Lexer.tokenize lexbuf
    with
    | _ ->
      let pos = lexbuf.EndPos
      failwith $"Parse error at ({pos.Line + 1}, {pos.Column})."