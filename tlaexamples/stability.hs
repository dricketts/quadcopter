--module StabilityGraphs where
import System.Random
import Control.Monad
import Graphics.EasyPlot


velocity = -1
epsilon = 0.25

initial = \x -> (-1 *x) + 1

nextF f t = \x -> ((-1) * (f t) * (x - t)) + (f t)

times = iterate (+ epsilon) 0

functions = foldl (\a@(f:fs) t -> nextF f t : a) [initial] times

--randomInterrupts :: [Double]
--randomInterrupts = runState (

graphs :: [Graph2D Double Double]
graphs = map (Function2D [Title "STRING"] [Range 0 20]) $
  take 10 functions

main :: IO ()
main = do
   plot X11 graphs
   return ()
