-- Traditional Lean notation is local to this theorem-heavy tree. This is a
-- lint-policy patch: layout, casing, and the systems floor continue to inherit.
def lint.symbolPolicy := "traditionalLean"

-- SHA-256 working-variable names are fixed by the algorithm specification.
-- Owner qualification prevents these exceptions from admitting unrelated fields.
def lint.fieldAllow1 := "State.a,State.b,State.c,State.d,State.e,State.f,State.g"
def lint.fieldAllow2 := "st,State.hh"

-- Conventional cryptographic names and the filesystem grade label retain their
-- specification spellings. Owner qualification keeps the patch local.
def lint.declarationAllow1 := "Continuity.Crypto.SHA256.K"
def lint.declarationAllow2 := "Continuity.Crypto.SHA256.ch,Continuity.GradeLabel.Fs"
