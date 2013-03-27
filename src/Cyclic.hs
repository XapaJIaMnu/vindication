module Cyclic(cyclic) where
import Data.Graph.Inductive

cyclic :: (Eq a, Eq b, DynGraph g) => g a b -> Bool
cyclic x 
  | (isEmpty newgraph) = False --Empty graph => Acyclic
  | equal x newgraph = True --Same graph two consecutive iterations
  | otherwise = cyclic newgraph
  where newgraph = traversenodes (nodes x) x

--Tries to remove a node which has no other nodes going to it from the graph.
--If it fails it just returns the same graph. We will call this function recursively
--Until we either get empty graph or the same graph in two consectutive calls.
--If we get the same graph in two consecutive calls, it means that we have a cycle.
--If we get an empty graph at the end it means it is acyclic.
traversenodes :: Graph gr => [Node] -> gr a b -> gr a b
traversenodes nodes graph
    |nodes == [] = graph
    |(pre graph current_node) == [] = delNode current_node graph
    |otherwise = traversenodes (tail nodes) graph
    where current_node = head nodes