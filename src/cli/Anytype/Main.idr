||| anytype-check: the kernel's stable process-boundary entry point.
|||
||| Usage:  echo '<term-sexp>' | anytype-check --discipline affine|exact
|||
||| Output (one line) and exit code follow Abi.Types.verdictCode:
|||   ACCEPT <type>      exit 0   (VAccepted)
|||   REJECT <reason>    exit 1   (VRejected)
|||   ILLFORMED <what>   exit 2   (VIllFormed)
||| The Zig side (src/interface/ffi) maps these back to anytype_check's
||| C return value; the codes are proven injective in Abi.Types.
module Anytype.Main

import System
import Abi.Types
import Anytype.Kernel
import Anytype.Sexp

%default total

-- Exit codes are verdictCode values; the literals let ExitFailure's
-- nonzero proof discharge by computation (Abi.Types proves them
-- injective, disciplineRoundTrip ties decode to encode).
exitVerdict : Verdict -> IO ()
exitVerdict VAccepted = exitWith ExitSuccess
exitVerdict VRejected = exitWith (ExitFailure 1)
exitVerdict VIllFormed = exitWith (ExitFailure 2)

run : (pg : String -> Maybe g) -> (GradeAlgebra g) -> (g -> String) ->
      String -> IO ()
run pg alg sg input =
  case parseClosed pg input of
    Nothing => do
      putStrLn "ILLFORMED unreadable or ill-scoped term"
      exitVerdict VIllFormed
    Just t =>
      case checkClosed alg t of
        Right ty => do
          putStrLn ("ACCEPT " ++ showTy sg ty)
          exitVerdict VAccepted
        Left err => do
          putStrLn ("REJECT " ++ show err)
          exitVerdict VRejected

usage : IO ()
usage = do
  putStrLn "ILLFORMED usage: anytype-check --discipline affine|exact"
  exitVerdict VIllFormed

main : IO ()
main = do
  args <- getArgs
  input <- getLine
  case args of
    [_, "--discipline", "affine"] => run affineGrade AffineAlgebra show input
    [_, "--discipline", "exact"]  => run exactGrade ExactAlgebra show input
    _ => usage
