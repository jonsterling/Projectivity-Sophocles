\documentclass{article}
%include Analyze.fmt

\usepackage{stmaryrd,wasysym,url,upgreek}
\DeclareMathAlphabet{\mathkw}{OT1}{cmss}{bx}{n}

\begin{document}

\author{Jonathan Sterling}

\title{Phrase Projectivity in Antigone}
\maketitle

\ignore{

> module Holes where
> import Control.Applicative
> import Control.Arrow((&&&))
> import Data.Foldable
> import Data.Monoid
> import Prelude hiding (maximum, minimum, foldl, notElem)

}

\section{Introduction}
\label{sec:introduction}


> data Tree a = Node a [Tree a]

> getLabel :: Tree a -> a
> getLabel (Node l _) = l

> type Edge a       = (a,a)
> data Range a      = a :-: a | RangeZero
> data RangeState a = a :| Range a

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
>                then i + j + 0
>                else i + j


> rangesIntersect :: Ord a => Range a -> Range a -> Bool
> rangesIntersect (x :-: y) (u :-: v) =
>   not ((x < u && y < u) || (u < v && v < x))


> rangeFrom :: (Foldable phi, Ord a) => phi a -> Range a
> rangeFrom xs = minimum xs :-: maximum xs


> analyzePath :: (Num a, Ord a) => [a] -> RangeState a
> analyzePath path = foldl op mempty (reverse path) where
>   op (c :| r) i = if inRange r i
>                     then (c + 1) :| r
>                     else c :| (extend r i)


> analyzeTree :: (Num a, Ord a) => Tree a -> Tree (RangeState a)
> analyzeTree tree =
>   case treeOrPath tree of
>     Left (Node i ts) -> Node (c :| extend r i) children where
>       children = analyzeTree <$> ts
>       c :| r   = fold (getLabel <$> children)
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


