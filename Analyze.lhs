%!TEX encoding = UTF-8 Unicode

\documentclass{article}
%include Analyze.fmt

\usepackage{homework,stmaryrd,wasysym,url,upgreek,subfigure}
\usepackage[margin=1cm]{caption}
\usepackage{xytree}
\DeclareMathAlphabet{\mathkw}{OT1}{cmss}{bx}{n}

\begin{document}
\setmainfont{Times New Roman}

\author{Jonathan Sterling}

\title{Phrase Projectivity in Antigone}
\date{April 2013}
\maketitle

\ignore{

> {-# LANGUAGE StandaloneDeriving #-}

> module Analyze where
> import Control.Applicative
> import Control.Arrow((&&&))
> import Data.Foldable
> import Debug.Trace
> import Data.Maybe (isJust, maybeToList)
> import Data.Tree
> import Data.List (genericLength, nub, findIndex, sortBy)
> import Data.Function (on)
> import Prelude hiding (maximum, minimum, foldl, notElem, elem, concat, sum)

}

\section{Dependency Trees and Their Projectivity}

A dependency tree encodes the head-dependent relation for a string of words,
where arcs are drawn from heads to their dependents. We consider a phrase
\emph{projective} when these arcs do not cross each other, and
\emph{discontinuous} to the extent that any of the arcs intersect.
Figure~\ref{fig:dependency-trees} illustrates the various kinds of projectivity
violations that may occur.

\begin{figure}[h!]
\centering
\subfigure[``Full of plentiful supplies'' (Xenophon, \emph{Anabasis} 3.5.1) is fully projective.]{
  \xytext{
    \xybarnode{μεστῇ}\xybarconnect[6]{2}&
    \xybarnode{πολλῶν}&
    \xybarnode{ἀγαθῶν}\xybarconnect[3]{-1}
  }
}
\hspace{6pt}
\subfigure[``Full of many good things'' (Plato, \emph{Laws} 906a) has one
projectivity violation.]{
  \xytext{
    \xybarnode{πολλῶν}&
    \xybarnode{μεστὸν}\xybarconnect[6]{1}&
    \xybarnode{ἀγαθῶν}\xybarconnect[3]{-2}
  }
}
\subfigure[``And he stood over the rooftops, gaped in a circle with murderous
spears around the seven-gated mouth, and left'' (Sophocles, \emph{Antigone}
117--120) has five projectivity violations (note that multiple arcs may
intersect at a point).]{
  \xytext{
    \xybarnode{στὰς}\xybarconnect[6]{2} &
    \xybarnode{δ'} &
    \xybarnode{ὑπὲρ}\xybarconnect[3]{1} &
    \xybarnode{μελάθρων} &
    \xybarnode{φονώσαισιν}\xybarconnect[3]{3} &
    \xybarnode{ἀμφιχανὼν}
      \xybarconnect[6]{1}
      \xybarconnect[6]{2}
      \xybarconnect[6]{4}&
    \xybarnode{κύκλῳ} &
    \xybarnode{λόγχαις} &
    \xybarnode{ἐπτάπυλον} &
    \xybarnode{στόμα}\xybarconnect[3]{-1} &
    \xybarnode{ἔβα}
      \xybarconnect[9]{-10}
      \xybarconnect[9]{-9}
      \xybarconnect[9]{-5}
  }
}

\caption{A dependency path wrapping around itself is a projectivity violation,
as in (b); interlacing adjacent phrases also violate projectivity, as in
(c). Examples (a--b) drawn from Devine~\&~Stephens.}
\label{fig:dependency-trees}
\end{figure}

\noindent
In this paper, we use a concrete metric of projectivity $\omega$, given by the following
ratio:
\[
    \omega = \frac{\text{number of violations}}{\text{number of arcs}}
\]
Section~\ref{sec:algorithm} deals with the development of an algorithm to
compute this quantity for a particular dependency tree.

\section{The Algorithm}
\label{sec:algorithm}

Dependency trees are a recursive data structure
with a head node, which may have any number of arcs drawn to further trees (this
is called a \emph{rose tree}). We represent them as a Haskell data-type as
follows:

< data Tree a = Node a [Tree a]

This can be read as ``For all types |a|, a |Tree| of |a| is constructed from a
label of type |a| and a forest of |Tree|s of |a|,'' where brackets are a notation
for lists.

Given a tree, we can extract its root label by pattern matching on its structure
as follows:

> getLabel :: Tree a -> a
> getLabel (Node l _) = l
> getForest :: Tree a -> [Tree a]
> getForest (Node _ ts) = ts

\subsection{From Edges to Trees}

A sentence from the Perseus treebank is in the form of a list of words that are
indexed their linear position, and cross-referenced by the linear position of
their dominating head. We shall consider each index to be a \emph{vertex}, and
each pair of vertices to be an |Edge|, which we shall write as follows:

> data Edge a = a :-: a deriving Eq

\ignore{

> deriving instance Show a => Show (Edge a)

}
%
An |Edge a| is given by two vertices of type |a|; the |deriving Eq| statement
generates the code that is necessary to determine whether or not two |Edge|s are
equal using the |(==)| operator. In order to perform our analysis, we should wish
to transform the raw list of edges into a tree structure. The basic procedure is
as follows:

First, we try to find the root vertex of the tree. This will be a vertex that is
given as the head of one of the words, but does not itself appear in the
sentence:

> rootVertex :: Eq a => [Edge a] -> Maybe a
> rootVertex es = find (`notElem` deps) heads where
>   heads  = (\(x :-: y) -> x) <$> es
>   deps   = (\(x :-: y) -> y) <$> es

If the data that we are working with are not well-formed, there is a chance that
we will not find a root vertex; that is why the type is given as |Maybe|.

Then, given a root vertex, we look to find all the edges that
it touches, and try to build the subtrees that are connected with those edges.

> onEdge :: Ord a => a -> Edge a -> Bool
> onEdge i (x :-: y) = x == i || y == i
>
> oppositeVertex :: Ord a => a -> Edge a -> a
> oppositeVertex i (x :-: y)
>   | x == i     = y
>   | otherwise  = x

This is done recursively until the list of edges is exhausted and we have a
complete tree structure:

%format buildWithRoot = "\FN{buildWithRoot}"

> treeFromEdges :: Ord a => [Edge a] -> Maybe (Tree a)
> treeFromEdges es = buildWithRoot es <$> rootVertex es where
>   buildWithRoot es root = Node root sortedChildren where
>     roots           = oppositeVertex root <$> filter (onEdge root) es
>     children        = buildWithRoot (filter (not . onEdge root) es) <$> roots
>     sortedChildren  = sortBy (compare `on` getLabel) children


\subsection{Counting Violations: Computing |omega|}
Violations are given as an integer tally:

> type Violations = Integer

The basic procedure for counting projectivity violations is as follows: flatten
down the tree into a list of edges cross-referenced by their vertical position
in the tree; then traverse the list and see how many times these edges intersect
each other.

> type Level = Integer

The vertical position of a node in a tree is represented as its |Level|,
counting backwards from the total depth of the tree. That is, the deepest node
in the tree is at level |0|, and the highest node in the tree is at level |n|,
where |n| is the tree's depth.

< levels :: Tree a -> [[a]]
< levels t = map (map getLabel) $
<             takeWhile (not . null) $
<             iterate (>>= getForest) [t]

> depth :: Tree a -> Integer
> depth = genericLength . levels

We can now annotate each node in a tree with what level it is at:

> annotateLevels :: Tree a -> Tree (Level, a)
> annotateLevels tree = aux (depth tree) tree where
>   aux l (Node x ts) = Node (l, x) (aux (l - 1) <$> ts)

Then, we fold up the tree into a list of edges and levels:

> allEdges :: Ord a => Tree a -> [(Level, Edge a)]
> allEdges tree = aux (annotateLevels tree) where
>   aux (Node (_,x) ts) = ts >>= go where
>     go t@(Node (l, y) _) = (l, edgeWithRange [x,y]) : aux t

> edgeWithRange :: (Foldable phi, Ord a) => phi a -> Edge a
> edgeWithRange xs = minimum xs :-: maximum xs

A handy way to think of edges annotated by levels is as a representation of the
arc itself, where the ends of the edge are the endpoints, and the level is the
height of the arc.

If on end of one arc is between the ends of another, then there is a single
intersection. If one arc is higher than another and the latter is in between the
endpoints of the former, there is no violation; but if they are at the same
level, or if the latter is higher than the former, there is a double
intersection. Otherwise, there is no intersection.

> checkEdges :: Ord a => (Level, Edge a) -> (Level, Edge a) -> Violations
> checkEdges (l, xy@(x :-: y)) (l', uv@(u :-: v))
>   | inRange y uv && inRange u xy             = 1
>   | inRange x uv && inRange v xy             = 1
>   | inRange x uv && inRange y uv && l >= l'  = 2
>   | inRange u xy && inRange v xy && l <= l'  = 2
>   | otherwise                                = 0

We determine whether a vertex is in the bounds of an edge using |inRange|.

> inRange :: Ord a => a -> Edge a -> Bool
> inRange z (x :-: y) = z > minimum [x,y] && z < maximum [x,y]

We can now use what we've built to count the intersections that occur in a
collection of edges. This is done by adding up the result of |checkEdges| of
combination of each edge with the subset of edges which are at or below its
level:

%format rangesBelow = "\FN{rangesBelow}"
%format violationsWith = "\FN{violationsWith}"

> edgeViolations :: Ord a => [(Level, Edge a)] -> Violations
> edgeViolations xs = sum $ violationsWith <$> xs where
>   rangesBelow (l, _)  = filter (\(l', _) -> l' <= l) xs
>   violationsWith x    = sum $ (checkEdges x <$> rangesBelow x)

Finally, |omega| is computed for a tree as follows:

%format edges = "\FN{edges}"
%format totalArcs = "\FN{totalArcs}"
%format violations = "\FN{violations}"

> omega :: (Fractional n, Ord a) => Tree a -> n
> omega tree = violations / totalArcs where
>   edges       = allEdges tree
>   totalArcs   = genericLength edges
>   violations  = fromInteger $ edgeViolations edges

\end{document}


