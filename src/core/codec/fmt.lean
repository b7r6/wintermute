-- Preserve canonical protocol vocabulary without admitting these leaves on
-- unrelated records.
def lint.fieldAllow2 := "st,nar_info_data.ca,valid_path_info.ca,vsock_header.op"

-- Preserve exact protocol/API vocabulary without exempting unrelated short
-- declarations in the codec tree.
def lint.declarationAllow2 :=
  "Continuity.Codec.Core.ParseResult.ok,Continuity.Codec.Core.u8,Continuity.Codec.Core.Parser.presult.ok,Continuity.Codec.Core.Scanner.LF,Continuity.Codec.Core.Scanner.CR,Continuity.Codec.Wire.Nix.Daemon.mk,Continuity.Codec.Wire.Nix.Daemon.StrictParseResult.ok,Continuity.Codec.Wire.Nix.Nar.nar_parse_result.ok,Continuity.Codec.Wire.Nix.NarInfo.Compression.xz,Continuity.Codec.Wire.Nix.NarInfo.Compression.br,Continuity.Codec.Wire.Nix.NarInfo.nar_info_result.ok,Continuity.Codec.Wire.Protobuf.StrictParseResult.ok,Continuity.Codec.Wire.Zmtp.StrictParseResult.ok"
