import ZkFormal.V2.Export
import NearCompression.PreparedPublicBoundary

def main : IO Unit :=
  IO.println ((NearCompression.preparedBoundaryAir []).exportJson)
