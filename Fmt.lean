module

import all LeanFmt.Cli

public unsafe def main (args : List String) : IO UInt32 :=
  LeanFmt.Internal.Cli.runCli (if args.isEmpty then ["format", "--workers", "2"] else args)
