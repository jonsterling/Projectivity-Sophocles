%!TEX encoding = UTF-8 Unicode

\documentclass{article}
%include Analyze.fmt

\usepackage{homework,stmaryrd,wasysym,url,upgreek,subfigure}
\usepackage[margin=1cm]{caption}
\usepackage{tikz-dependency}
\DeclareMathAlphabet{\mathkw}{OT1}{cmss}{bx}{n}

\begin{document}
\setmainfont{Times New Roman}

\author{Jonathan Sterling}

\title{Phrase Projectivity in Antigone}
\maketitle

\ignore{

> {-# LANGUAGE StandaloneDeriving #-}

> module Analyze where
> import Control.Applicative
> import Control.Arrow((&&&))
> import Data.Foldable
> import Debug.Trace
> import Data.Monoid
> import Data.Maybe (isJust, fromJust)
> import Data.Tree
> import Data.List (genericLength, nub, findIndex)
> import Prelude hiding (maximum, minimum, foldl, notElem, elem)

}

\section{Introduction}
\label{sec:introduction}

\subsection{Dependency Trees and Projectivity}
\label{sec:introduction.dependency}

A dependency tree encodes the head-dependent relation for a string of words,
where arcs are drawn from heads to their dependents. We consider a phrase
\emph{projective} when these arcs do not cross each other, and
\emph{discontinuous} inasmuch as any of the arcs do cross.
Figure~\ref{fig:dependency-trees} illustrates the various kinds of projectivity
violations that may occur.

\begin{figure}[h!]
\centering
\subfigure[``Full of plentiful supplies'' (Xenophon, \emph{Anabasis} 3.5.1).]{
  \begin{dependency}[theme = simple]
      \begin{deptext}[column sep=1em]
          μεστῇ \& πολλῶν \& ἀγαθῶν\\
      \end{deptext}
      \depedge{3}{2}{ADJ}
      \depedge{1}{3}{GEN}
  \end{dependency}
}
\hspace{6pt}
\subfigure[``Full of many good things'' (Plato, \emph{Laws} 906a).]{
  \begin{dependency}[theme = simple]
      \begin{deptext}[column sep=1em]
          πολλῶν \& μεστὸν \& ἀγαθῶν\\
      \end{deptext}
      \depedge[edge start x offset=-6pt, arc angle=20]{3}{1}{ADJ}
      \depedge{2}{3}{GEN}
  \end{dependency}
}
\subfigure[``And he stood over the rooftops, gaped in a circle with murderous
spears around the seven-gated mouth, and left.'' (Sophocles, \emph{Antigone}
117--120).]{
  \begin{dependency}[theme = simple]
      \begin{deptext}[column sep=0.1em]
        στὰς \& δ' \& ὑπὲρ \& μελάθρων \& φονώσαισιν \& ἀμφιχανὼν \& κύκλῳ \&
λόγχαις \& ἑπτάπυλον \& στόμα \& ἔβα \\
      \end{deptext}
      \depedge{3}{4}{OBJ}
      \depedge{1}{3}{ADV}
      \depedge{6}{7}{ADV}
      \depedge{8}{5}{ADJ}
      \depedge{6}{8}{ADV}
      \depedge{10}{9}{ADJ}
      \depedge{6}{10}{OBJ}
      \depedge{11}{6}{ADV}
      \depedge{11}{1}{ADV}
      \depedge{11}{2}{CONJ}
  \end{dependency}
}

\caption{A dependency path wrapping around itself is a projectivity violation,
as in (b); interlacing adjacent phrases also violate projectivity, as in
(c). Examples (a--b) drawn from Devine~\&~Stephens.}
\label{fig:dependency-trees}
\end{figure}


< data Tree a = Node a [Tree a]

> getLabel :: Tree a -> a
> getLabel (Node l _) = l

> type Edge a       = (a,a)
> data Range a      = a :-: a | RangeZero deriving Eq
> data RangeState a = Integer :| Range a

> getRange :: RangeState a -> Range a
> getRange (_ :| r) = r

> getViolations :: RangeState a -> Integer
> getViolations (vs :| _) = vs

\ignore{

> deriving instance Show a => Show (Range a)
> deriving instance Show a => Show (RangeState a)

}

\noindent
A |Monoid| is an algebraic structure which has a zero |mempty| and a binary
operation |mappend|, and which satisfies some laws:

< class Monoid a where
<   mempty :: a
<   mappend :: a -> a -> a
<
<   associativity :: mappend l (mappend c r) == mappend (mappend l c) r
<   leftIdentity  :: mappend l mempty == l
<   rightIdentity :: mappend mempty l == l


> instance Ord a => Monoid (Range a) where
>   mempty = RangeZero
>   mappend (x :-: y) (u :-: v) = rangeFrom [x,y,u,v]
>   mappend RangeZero xy = xy
>   mappend xy RangeZero = xy

> instance (Num a, Ord a) => Monoid (RangeState a) where
>   mempty = 0 :| mempty
>   mappend (i :| xy) (j :| uv) = count :| (mappend xy uv) where
>     count = if rangesIntersect xy uv
>                then i + j + 1
>                else i + j


> rangesIntersect :: Ord a => Range a -> Range a -> Bool
> rangesIntersect (x :-: y) (u :-: v) =
>   not ((x < u && y < u) || (u < v && v < x))
> rangesIntersect _         _         = False


> rangeFrom :: (Foldable phi, Ord a) => phi a -> Range a
> rangeFrom xs = minimum xs :-: maximum xs


> analyzePath :: (Num a, Ord a) => [a] -> RangeState a
> analyzePath path = foldl op mempty (reverse path) where
>   op (c :| r) i = if inRange r i
>                     then (c + 1) :| r
>                     else c :| (extend r i)


> violations :: (Show a, Eq a, Ord a) => Range a -> Range a -> Int
> violations xy@(x :-: y) uv@(u :-: v)
>   | (inRange uv y) && (inRange xy u) = trace "1" $ traceShow (xy,uv) 1
>   | (inRange uv x) && (inRange xy v) = trace "1" $ traceShow (xy,uv) 1
>   | (inRange uv x) && (inRange uv y) = trace "2" $ traceShow (xy,uv) 2
>   | otherwise = 0


> allEdges' :: Ord a => Tree a -> [(Int, Range a)]
> allEdges' tree = allEdges tree tree

> allEdges :: Ord a => Tree a -> Tree a -> [(Int, Range a)]
> allEdges tree (Node i ts) = (\t@(Node j _) -> (fromJust (levelIn' j tree), rangeFrom [i,j]) : (allEdges tree t)) =<< ts

> analyzeEdges :: (Show a, Ord a) => [(Int, Range a)] -> [Int]
> analyzeEdges xs = violationsWith <$> xs where
>   rangesBelow (l, r) = snd <$> (filter (\(l', _) -> l' <= l) xs)
>   violationsWith x = Prelude.sum $ violations (snd x) <$> (rangesBelow x)



> depth :: Tree a -> Int
> depth = length . levels

> levelIn' :: Eq a => a -> Tree a -> Maybe Int
> levelIn' x t = levelIn (length (levels t)) x t

> levelIn :: Eq a => Int -> a -> Tree a -> Maybe Int
> levelIn l x (Node y ts) | x == y = Just l
>                         | otherwise = msum (levelIn (l - 1) x <$> ts)

> analyzeTree :: (Num a, Ord a) => Tree a -> Tree (RangeState a)
> analyzeTree tree =
>   case treeOrPath tree of
>     Left (Node i ts) -> Node (c' :| extend r i) children where
>       children = analyzeTree <$> ts
>       childLabels = getLabel <$> children
>       c :| r   = fold childLabels
>       c' = c + (genericLength (filter (\r' -> inRange r' i) (getRange <$> childLabels)))
>     Right path       -> Node (analyzePath path) []


> treeOrPath :: Tree a -> Either (Tree a) [a]
> treeOrPath (Node i [])  = Right [i]
> treeOrPath (Node i [x]) = (i :) <$> treeOrPath x
> treeOrPath t            = Left t

> extend :: Ord a => Range a -> a -> Range a
> extend (x :-: y) z = rangeFrom [x,y,z]
> extend RangeZero z = z :-: z


> inRange :: Ord a => Range a -> a -> Bool
> inRange (x :-: y) z = z > x && z < y
> inRange RangeZero _ = False


> maximalPoint :: Eq a => [Edge a] -> Maybe a
> maximalPoint es =
>  find (\x -> notElem x (snd <$> es)) (fst <$> es)

\end{document}


