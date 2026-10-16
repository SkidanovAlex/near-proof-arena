import NearCompression

-- Evaluated metadata only. The theorem audit remains in Audit.lean.
#eval IO.println ("COVERED\n" ++ String.intercalate "\n" NearCompression.provedHostNames ++ "\nEND")
#eval IO.println ("REAL_GATED\n" ++ String.intercalate "\n" NearSpecV3.Wasm.realOodHosts ++ "\nEND")
#eval IO.println ("CURVES\n" ++ String.intercalate "\n" NearSpecV3.Wasm.curveHosts ++ "\nEND")

#eval IO.println ("REAL_WRAPPERS\n" ++ String.intercalate "\n" NearCompression.realWrapperNames ++ "\nEND")
