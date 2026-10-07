-- Raw mesh completion scalar slots mirror the C ABI's tagged union.
def lint.fieldAllow1 := "MeshEvent.a,MeshEvent.b"
def lint.fieldAllow2 := "st"

-- Preserve the public completion predicate at its exact owner.
def lint.declarationAllow2 := "StdlibEx.IOUring.Loop.Event.ok"
