
import Unlambda
import System.Environment

main = do
    prog <- getProgName
    args <- getArgs
    if length args /= 2
        then error $ "Usage: " ++ prog ++ " [infile.u] [outfile.c]"
        else compileFile (args !! 0) (args !! 1)

