--module StabilityGraphs where
import System.Random
import Control.Monad
import Graphics.EasyPlot


velocity = -1
epsilon = 0.25

initial = \x -> (-100 *x) + 100

nextF f t = \x -> ((-1) * (f t) * (x - t)) + (f t)

times = iterate (+ epsilon) 0

functions = foldl (\a@(x:xs) t -> nextF x t : a) [initial] times

--randomInterrupts :: [Double]
--randomInterrupts = runState (

graphs :: [Graph2D Double Double]
graphs = map (Function2D [] []) $ take 10 functions

main :: IO ()
main = do
   plot (PNG "plot.png")  graphs
   return ()
