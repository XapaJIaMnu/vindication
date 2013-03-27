%include arg-preamble.fmt

\section{The Language}
\label{sec:language}

%Imports and module name
%These are excluded from the pdf, but included here to provide a 
%fully working .lhs
%if False
\begin{code}
module Carneades where

import Data.Graph.Inductive
import Cyclic
-- import Data.Graph.Analysis
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromJust)
\end{code}
%endif


%Just a placeholder to demonstrate use of lhs2TeX.
%\begin{code}
%fac :: Integer -> Integer
%fac n  | n == 0     = 1
%       | n > 0      = n * fac (n-1)
%       | otherwise  = error "Invalid argument!"
%\end{code}%imports

\subsection{Arguments}
% One of the goals of our implementation is to show how close Haskell
% data types can be to the mathematical constructions used in the
% Carneades argumentation model.

As our ultimate goal is a DSL for argumentation theory, we strive for a
realisation in Haskell that mirrors the mathematical model of Carneades
argumentation framework as closely as possible. Ideally, there would be little
more to a realisation than a transliteration. In Carneades all logical
formulae are atomic propositions in propositional logic; i.e., all
propositions are either positive or negative literals. Taking literals to be
strings suffice in the following, and propositions can then be formed by
pairing a literal with a Boolean to denote whether it is positive or negative:
\begin{code}
type Proposition = (Bool, String) 
\end{code}	
Negation of a proposition is now trivial:
\begin{code}
negation :: Proposition -> Proposition
negation (b, p) = (not b, p) 
\end{code}

An argument is formed from two lists of propositions, its
\emph{premises} and its \emph{exceptions}, and a proposition that denotes the
\emph{conclusion}. An argument is said to be \emph{pro} its conclusion $c$ and
\emph{con} its negation, $\overline{c}$.
\begin{code}
data Argument = Arg [Proposition] [Proposition] Proposition
  deriving (Show, Eq)
\end{code}  

% Arguments are combined in a list of arguments, where the acyclicity of the
% list is determined by checking acyclicity of a corresponding dependency
% graph. Instead we immediately use FGL to define inductive graphs of 
% arguments, where its nodes are proposition paired with the list of its pro
% arguments and edges are unlabelled.
% 
% In Carneades, arguments are combined as an acyclic set, where the acyclicity
% of the set is determined by checking acyclicity of a corresponding dependency
% graph.


A set of arguments thus determines how propositions depend on each other;
i.e., a \emph{dependence graph} is induced. In Carneades, this dependence
graph is required to be acyclic. Using FGL \cite{Erwig2001}, we can take this
quite literally and form an inductively defined graph with propositions
paired with the corresponding pro arguments as nodes, and unlabelled
dependence edges determined by the overall set of arguments:

\begin{code}
type AGraph = Gr (Proposition, [Argument]) ()
\end{code}

\subsection{Evaluation}
In Carneades, arguments are evaluated relative to their assigned proof
standard and a given audience. A proof standard is a function that given a
proposition $p$, aggregates arguments pro and con $p$ and decides whether it
is acceptable or not. An audience is a pair of \emph{assumptions} and a
\emph{weight function} assigning real values to arguments:
%
\begin{code}
type ProofStandard = Proposition -> CAES -> Bool
type Audience = (Assumptions, Weight)
type Assumptions = [Proposition]
type Weight = Argument -> Double
\end{code}


The main structure of the argumentation model is called a Carneades Argument
Evaluation Structure (CAES). It is a triple of an acyclic set of arguments,
an audience, and a function that assigns proof standards to propositions.
Note that propositions thus can be associated with \emph{different} standards.
This is considered a particular strength of the Carneades framework:
\begin{code}
type AssignStandard = Proposition -> ProofStandard
newtype CAES = CAES (AGraph, Audience, AssignStandard)
\end{code}

Evaluation of a proposition $p$ in a CAES $C$ is called \emph{acceptability}
of $p$ in $C$. It is determined by satisfaction of the assigned proof
standard:
%
\begin{code}
acceptable :: Proposition -> CAES -> Bool
acceptable c caes@(CAES (_, (assumptions, _), standard))  
  |  c `elem` assumptions           = True   -- A fix of the original model
  |  negation c `elem` assumptions  = False  -- A fix of the original model
  |  otherwise                      = c `s` caes 
  where s = standard c
\end{code}

For an argument to be considered in the aggregation process of a proof
standard, it needs to be \emph{applicable}. An argument is applicable iff all
its premises are either assumptions or have been deemed acceptable in the
CAES, and none of its exceptions is an assumption or acceptable. Thus:
% 
\begin{code}
applicability :: Argument -> CAES -> Bool
applicability (Arg prem exc _) caes@(CAES (_, (assumptions, _), _)) 
  = and $  zipWith (||)     (inAssumptions prem)  (isAcceptable prem) ++
           zipWith (nor)    (inAssumptions exc)   (isAcceptable exc)
      where   inAssumptions  =   map (`elem` assumptions)
              isAcceptable   =   map (`acceptable` caes)  
              x `nor` y      =   not (x || y)
\end{code}

\subsection{Proof standards}



Carneades predefines five proof standards, originating from the work of
Freeman and Farley \cite{Freeman96,Farley95}: \emph{scintilla of
evidence}, \emph{preponderance of the evidence}, \emph{clear and convincing
evidence}, \emph{beyond reasonable doubt} and finally \emph{dialectical
validity}.

For a proposition $p$ to satisfy the weakest proof standard, scintilla of
evidence, there should be at least one applicable argument pro $p$ in the CAES:
\begin{code}
scintilla :: ProofStandard
scintilla p caes@(CAES (g, _, _))
 = any (`applicability` caes) (getArgs p g)  
\end{code}
Here, |getArgs| is a utility function that returns all arguments pro a given
proposition form an acyclic set of arguments.

Preponderance of the evidence additionally requires that the maximum weight of
the applicable arguments pro $p$ is greater than the maximum weight of the
applicable arguments con $p$. The weight of zero arguments is taken to
be 0:
\begin{code}
maxWeightBy :: Weight -> [Argument] -> Double
maxWeightBy w = foldl max 0.0 . map w 

preponderance :: ProofStandard 
preponderance p caes@(CAES (g, (_, weight), _)) 
 =  maxWeight (applicableArgs proArgs) > maxWeight (applicableArgs conArgs)
    where  proArgs         = getArgs p g
           conArgs         = getArgs (negation p) g
           applicableArgs  = filter (`applicability` caes)
           maxWeight       = maxWeightBy weight
\end{code}

Clear and convincing evidence adds two more constraints: the weight difference
should now be larger than a given constant $\beta$, and there should be
an applicable argument pro $p$ that is stronger than a given constant $\alpha$:
\begin{code}
clear_and_convincing :: ProofStandard 
clear_and_convincing p caes@(CAES (g, (_, weight), _)) 
 =  maxWeightp > alpha &&
    maxWeightp > maxWeight (applicableArgs conArgs) + beta
    where  proArgs         = getArgs p g
           conArgs         = getArgs (negation p) g
           applicableArgs  = filter (`applicability` caes)
           maxWeight       = maxWeightBy weight
           maxWeightp      = maxWeight $ applicableArgs proArgs
\end{code}

Beyond reasonable doubt has one more requirement still: the strongest argument
con $p$ needs to be less than a given constant $\gamma$; i.e., there must
be no reasonable doubt:
\begin{code}
beyond_reasonable_doubt :: ProofStandard 
beyond_reasonable_doubt p caes@(CAES (g, (_, weight), _)) 
 =  maxWeightp > alpha &&
    maxWeightp > maxWeightnegp && 
    maxWeightnegp < gamma                                                 
     where  proArgs         = getArgs p g
            conArgs         = getArgs (negation p) g
            applicableArgs  = filter (`applicability` caes)
            maxWeight       = maxWeightBy weight
            maxWeightp      = maxWeight $ applicableArgs proArgs
            maxWeightnegp   = maxWeight $ applicableArgs conArgs
\end{code}

Finally dialectical validity requires at least one applicable argument pro $p$
and no applicable arguments con $p$:
\begin{code}
dialectical_validity :: ProofStandard 
dialectical_validity p caes   
  = scintilla p caes && 
    not (scintilla (negation p) caes)
\end{code}

%\subsection{Utility functions on graphs}
% Utility functions (not included in paper)
%if False
\begin{code}
contextP :: Proposition -> AGraph -> [Context (Proposition, [Argument]) ()]
contextP p = gsel (\ (_, _, a, _) -> fst a == p) 
     
getArgs :: Proposition -> AGraph -> [Argument]  
getArgs p g 
  =  case contextP p g of
       []                          -> []
       ((_, _, (_, args), _) : _)  -> args
\end{code}
%endif

%if False

% HN 2012-03-26:
% Notes for reference:
% * Split the current definition 1 into two:
%   - Dependence graph
%   - Acyclic set of arguments (defined in terms of dependence graph)
% * It seems to me that the central notion is an acyclic set of arguments.
%   That they are represented as a graph is just an implementation choice.
%   This suggests:
%   - Rename AGraph to something that suggests "Acyclic set of arguments".
%   - Possibly rename this section.

\subsection{Graph construction}
We associate a graph along with a |Map| that stores the node number for every |Proposition| to make construction of the |AGraph| easier.
\begin{code}
type PropNode = LNode (Proposition, [Argument])
type AssociatedGraph = (AGraph, Map Proposition Node)
\end{code}

An argument graph is then constructed as following:
\begin{code}
mkArgGraph :: [Argument] -> AGraph
mkArgGraph = fst . foldr addArgument (empty, Map.empty)
\end{code}

Carneades uses the following definition for acyclicity:
\begin{definition}[Acyclic set of arguments]
\label{def:carneadesacyclic}
A list of arguments is acyclic iff its corresponding dependency graph is acyclic. The corresponding dependency graph has nodes for every literal appearing in the list of arguments. A node $p$ has a directed link to node $q$ whenever $p$ depends on $q$ in the sense that there is an argument pro or con $p$ that has $q$ or $\overline{q}$ in its list of premises or exceptions.
\end{definition}

So when we add an argument |(Arg premises exceptions conclusion)| to our graph, we need to add both the conclusion and its negation to the graph, adding edges for both to all premises and exceptions while adding the argument to the list of arguments for |conclusion| as well. 

\begin{code}
addArgument :: Argument -> AssociatedGraph -> AssociatedGraph
addArgument arg@(Arg prem exc c) gr  = 
  let  deps             =  prem ++ exc
       (gr',  nodeNr)   =  addArgument' arg gr
       (gr'', nodeNr')  =  addNode (negation c) gr'
  in addEdges nodeNr' deps $ addEdges nodeNr deps gr'' 
\end{code}


%Some relatively uninteresting/ugly code to access the Graph.
%%if False
\begin{code}
addToContext :: Argument -> (Context (Proposition, [Argument]) (), AGraph) -> AGraph
addToContext arg ((adjb, n, (p, args), adja), g') = (adjb, n, (p, arg:args), adja) & g'

unsafeMatch :: Graph gr => Node -> gr a b -> (Context a b, gr a b)
unsafeMatch n g = mapFst fromJust $ match n g
\end{code}
%%endif
\todo{naming is not nice}

Add an argument to the graph. If there is no node present yet for the conclusion insert it, in both cases add the argument to the context of the conclusion.
\begin{code}
addArgument' :: Argument -> AssociatedGraph -> (AssociatedGraph, Node)
addArgument' arg@(Arg _ _ c) (g, m) 
 = case Map.lookup c m of 
       Nothing  ->  ((insNode (nodeNr, (c, [arg])) g, 
                       Map.insert c nodeNr m), 
                         nodeNr)
       Just n   ->  ((addToContext arg (unsafeMatch n g), 
                       m), 
                         n) 
  where nodeNr = Map.size m + 1
\end{code}

Add a proposition to the graph.
\begin{code}
addNode :: Proposition -> AssociatedGraph -> (AssociatedGraph, Node)
addNode p gr@(g,m) 
 =  case Map.lookup p m of 
       Nothing -> ((insNode (nodeNr, (p, [])) g, Map.insert p nodeNr m), nodeNr)
       Just n  -> (gr, n)
    where nodeNr = Map.size m + 1
\end{code}

For a specific node, add an edge for every |Proposition| in the list for the given graph.
\begin{code}
addEdges :: Node -> [Proposition] -> AssociatedGraph -> AssociatedGraph
addEdges n ps (g, m) = addEdges' n (map (fromJust . flip Map.lookup m') ps)  (g', m')-- addEdges' c n ps (g', m')
 where  nodeNr    = Map.size m + 1 
        newProps  = filter ( (== Nothing) . flip Map.lookup m) ps  
        g'        = insNodes (propsToNodes newProps nodeNr) g
        m'        = Map.union m . Map.fromList $ zip newProps [nodeNr..]
\end{code}

\todo{naming is not nice}

Generate unlabelled edges from a |Node| to a list of |Node|s and add it to the graph.
\begin{code}
addEdges' :: Node -> [Node] -> AssociatedGraph -> AssociatedGraph
addEdges' c ps (g, m) = (insEdges edges' g, m)
 where  edges' = map (genEdge c) ps
        genEdge k l = (k, l, ())

\end{code}

Some useful functions.
\begin{code}
propsToNodes :: [Proposition] -> Node -> [PropNode]
propsToNodes ps n = zip [n..] (map (\ p -> (p, [])) ps)

checkCycle :: AGraph -> Bool
-- import cyclic from module;  need to fix its definition
checkCycle = not . cyclic

mkProp :: String -> Proposition
mkProp ('-':s)  = mapFst not (mkProp s)
mkProp s        = (True, s)

mkAssumptions :: [String] -> [Proposition]
mkAssumptions = map mkProp

mkArg :: [String] -> [String] -> String -> Argument
mkArg ps es c = Arg (map mkProp ps) (map mkProp es) (mkProp c)
\end{code}

Blaat
%endif




\subsection{Implementing a CAES}

This subsection shows how we, given the formalisation of the notions
of Carneades argumentation framework developed above, quickly and at a
high level of abstraction can implement a Carneades argument
evaluation structure and evaluate it as well. We revisit the arguments
from Section \ref{sec:background} and assume the following:
%
\begin{align*}
\mathit{arguments} &= \{\mathit{arg1}, \mathit{arg2}, \mathit{arg3} \}, \\
\mathit{assumptions} &= \{\mathit{kill}, \mathit{witness}, \mathit{witness2}, \mathit{unreliable2} \},\\
\mathit{standard(intent)} &= \mathit{beyond}\textit{-}\mathit{reasonable}\textit{-}\mathit{doubt}, \\
\mathit{standard(x)} &= \mathit{scintilla},\ \textrm{for any other proposition x}, \\
\alpha &= 0.4,\ \beta = 0.3,\ \gamma = 0.2.
\end{align*}
%
%
%
%
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%Start example code%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
%
%if False
\begin{code}
alpha, beta, gamma :: Double
alpha  =  0.4
beta   =  0.3
gamma  =  0.2
\end{code}
%endif
%%

Arguments and the argument graph are constructed by calling |mkArg| and
|mkArgGraph| respectively:
\begin{code}
arg1, arg2, arg3 :: Argument 
arg1 = mkArg ["kill", "intent"] [] "murder"
arg2 = mkArg ["witness"] ["unreliable"] "intent"
arg3 = mkArg ["witness2"] ["unreliable2"] "-intent"

argGraph :: AGraph
argGraph = mkArgGraph [arg1, arg2, arg3]
\end{code}

The audience is implemented by defining the |weight| function and calling
|mkAssumptions| on the propositions which are to be assumed. The audience is
just a pair of these:
%
\begin{code}
weight :: Weight
weight  arg  |  arg == arg1  = 0.8
weight  arg  |  arg == arg2  = 0.3
weight  arg  |  arg == arg3  = 0.8
weight  _                    = error "no weight assigned"

assumptions :: [Proposition]
assumptions = mkAssumptions ["kill", "witness", "witness2","unreliable2"] 

audience :: Audience
audience = (assumptions, weight) 
\end{code}

Finally, after assigning proof standards in the |standard| function, we form
the CAES from the argument graph, audience and function |standard|:
\begin{code}
standard :: AssignStandard 
standard  (_, "intent")  = beyond_reasonable_doubt
standard  _              = scintilla 

caes :: CAES 
caes = CAES (argGraph, audience, standard)
\end{code}

We can now try out the argumentation structure. As expected, there are no
applicable arguments for $\mathit{-intent}$, since $\mathit{unreliable2}$ is
an exception, but there is an applicable argument for $\mathit{intent}$,
namely $\mathit{arg2}$:
%
\begin{spec}
filter (`applicability` caes) $ getArgs (mkProp "intent") argGraph  == [arg2]
 > True

filter (`applicability` caes) $ getArgs (mkProp "-intent") argGraph
 >  []
\end{spec}

Despite the applicable argument $\mathit{arg2}$ for $\mathit{intent}$,
$\mathit{murder}$ should not be acceptable, because the weight of
$\mathit{arg2} < \alpha$. However, note that we can't reach the opposite
conclusion either:
%
\begin{spec}
acceptable (mkProp "murder") caes
 > False
acceptable (mkProp "-murder") caes
 > False
\end{spec}


%if false
\begin{code}
testAppIntent :: [Argument]
testAppIntent = filter (`applicability` caes) $ getArgs (mkProp "intent") argGraph        

testAppNotIntent :: [Argument]
testAppNotIntent = filter (`applicability` caes) $ getArgs (mkProp "-intent") argGraph        

testAppMurder :: [Argument]
testAppMurder = filter (`applicability` caes) $ getArgs (mkProp "murder") argGraph        

testAppNotMurder :: [Argument]
testAppNotMurder = filter (`applicability` caes) $ getArgs (mkProp "-murder") argGraph        

testMurder  :: Bool
testMurder  = acceptable (mkProp "murder") caes

testNotMurder  :: Bool
testNotMurder  = acceptable (mkProp "-murder") caes
\end{code}
%endif

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%End example code%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%





%\begin{example}
%\label{exmp:carneades}
%Let $\alpha = 0.3$, $\beta = 0.3$ and $\gamma = 0.6$. Consider a CAES $C = \langle arguments, audience, standard \rangle$ and \emph{audience} $=$ $\langle$\emph{assumptions}$,$\emph{weight}$\rangle$ with 
%\begin{align*}
%arguments &= \{a_1, a_2, a_3, a_4 \}, \\
%a_1 &= \langle \{p_1, p_2 \}, \{ e_1 \}, c \rangle,\ a_2 = \langle \{ p_2, p_3 \}, \{ e_2 \}, \neg c \rangle, \\
%a_3 &= \langle \{ p_2 \}, \{ e_3 \}, \neg c \rangle,\ a_4 = \langle \emptyset, \{ e_4 \}, \neg c \rangle,\\
%assumptions &= \{ p_1, p_2, e_4 \},\\
%weight(a_1) &= 0.4;\ weight(a_2) = 0.9;\ weight(a_3) = 0.5;\ weight(a_4) = 0.6,\\
%standard(c) &= preponderance,\ standard(\neg c) = \emph{clear-and-convincing}.
%\end{align*}
%
%
%We can visualise these arguments (arrows denote premises/inferences and open circles denote exceptions):
%% \begin{figure}[H]%
%% \centering
%% \parbox{2in}{
%% \input{Diagrams/asub1.tex}}
%% \qquad
%% \begin{minipage}{2in}%
%% {\input{Diagrams/asub2.tex}}%}
%% \end{minipage}%
%% 
%% \label{fig:carneadesarguments}%
%% \end{figure}
%
%\begin{figure}
%\begin{center}
%\subfigure[Example 1]{
%    % \fbox{
%    \includegraphics[scale=0.8]{Diagrams/asub1.eps}
%    % }
%    \label{fig:ca-ex1}
%}
%\subfigure[Example 2]{
%    % \fbox{
%    \includegraphics[scale=0.8]{Diagrams/asub2.eps}
%    % }
%    \label{fig:ca-ex2}
%}
%\end{center}
%\caption{
%    Carneades Arguments
%    \label{fig:ca}
%}
%\end{figure}
%
%% \begin{figure}[H]
%% \centering
%% \parbox{2in}{\input{Diagrams/asub3.tex} \hfill}%
%% \qquad 
%% \begin{minipage}{1.2in}%
%% {\qquad \quad \input{Diagrams/asub4.tex}}%}
%% \end{minipage}%
%% \caption{Arguments in Carneades}
%% \label{fig:carneadesarguments2}%
%% \end{figure}
%
%\begin{figure}
%\begin{center}
%\subfigure[Example 3]{
%    % \fbox{
%    \includegraphics[scale=0.8]{Diagrams/asub3.eps}
%    % }
%    \label{fig:ca2-ex3}
%}
%\subfigure[Example 4]{
%    % \fbox{
%    \includegraphics[scale=0.8]{Diagrams/asub4.eps}
%    % }
%    \label{fig:ca2-ex4}
%}
%\end{center}
%\caption{
%    Arguments in Carneades
%    \label{fig:ca2}
%}
%\end{figure}
%
%
%Then we have that argument $a_2$ is not applicable because $p_3 \notin assumptions$ and $p_3$ is not acceptable because there is no argument with $p_3$ as conclusion. Argument $a_4$ is not applicable because $e_4 \in assumptions$. Argument $a_1$ and $a_3$ are applicable. 
%
%The conclusion $c$ (of argument $a_1$) is not acceptable because $standard(c) = preponderance$ and $weight(a_1) \not > weight(a_3)$ while $a_3$ is an applicable con argument for $c$. The conclusion $\neg c$ is also not acceptable because $standard(\neg c) =$ \emph{clear-and-convincing} and when considering the argument $a_4$ it holds for the applicable con argument $a_1$ that: $weight(a_3) \not > weight(a_1) + \beta$ (although $weight(a_3) > \alpha$).
%\end{example}
%
%
%
%
%

