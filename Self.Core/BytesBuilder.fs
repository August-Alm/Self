namespace Self.Core

module BytesBuilder =

  open Microsoft.FSharp.NativeInterop
  open System.Security.Cryptography
  open System

  type BytesBuilder (cap : int) =
    let ms = new IO.MemoryStream(cap)
    
    interface IDisposable with
      member _.Dispose () = ms.Dispose ()

    member _.Add (bs : Span<byte>) = ms.Write bs
    member _.Add (b : byte) = ms.WriteByte b
    member _.Add (i : int) =
      let mutable i = i
      let s = Span<byte> (NativePtr.toVoidPtr &&i, 4)
      ms.Write s
    
    member _.GetBytes () =
      let buf = ms.GetBuffer ()
      (ReadOnlySpan<byte> buf).Slice (0, int ms.Length)
    
    member _.Clear () =
      let buf = ms.GetBuffer ()
      System.Array.Clear (buf, 0, buf.Length)
      ms.Position <- 0; ms.SetLength 0
    

  let seqeq (s1 : ReadOnlySpan<byte>) (s2 : ReadOnlySpan<byte>) =
    s1.SequenceEqual s2

  let inline stackalloc<'a when 'a: unmanaged> size =
    let p = NativePtr.stackalloc<'a> size |> NativePtr.toVoidPtr
    Span<'a>(p, size)

  let hashBytes (hasher : MD5) (bs : ReadOnlySpan<byte>) : Guid =
    let mutable length = 16
    let target = stackalloc<byte> length
    if hasher.TryComputeHash (bs, target, &length) then
      Guid target
    else failwith "Failed hashing!"