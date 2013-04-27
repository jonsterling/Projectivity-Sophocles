%&program=xelatex
%&encoding=UTF-8 Unicode

\documentclass{article}

%options ghci -fglasgow-exts
%include Analyze.fmt

\usepackage{setspace,stmaryrd,url,subfigure, amssymb, amsfonts,amsmath,multicol,booktabs}
\usepackage[margin=1cm]{caption}
\usepackage{xytree, listings, cgloss4e, qtree}
\usepackage[toc,page]{appendix}

\usepackage[silent]{fontspec}
\usepackage{xltxtra}
\usepackage{polyglossia}

\newICUfeature{Contextual}{on}{+calt}

\defaultfontfeatures{Mapping=tex-text}
\newcommand{\salt}[1]{{\addfontfeature{Style=Alternate}{#1}}}
\newcommand{\hlig}[1]{{\addfontfeature{Ligatures=Historical}{#1}}}

\newfontfamily\greekfont[Script=Greek, Scale=MatchUppercase, Contextual=on]{Junicode}
\setotherlanguage{greek}
\setmainfont{Adobe Text Pro}

\let\eachwordone=\textgreek

\def\gkbarnode#1{\xybarnode{\textgreek{#1}}}

\definecolor{gray}{rgb}{0.4,0.4,0.4}

\lstset{
  basicstyle=\ttfamily,
  columns=fullflexible,
  showstringspaces=false,
  commentstyle=\color{gray}\upshape
}

\lstdefinelanguage{XML}
{
  morestring=[b]",
  morestring=[s]{>}{<},
  morecomment=[s]{<?}{?>},
  stringstyle=\color{gray},
  identifierstyle=\color{black},
  keywordstyle=\color{black},
  morekeywords={xmlns,version,type}% list your attributes here
}


\begin{document}
\onehalfspacing

\author{Jonathan Sterling}

\title{A Survey of Phrase Projectivity in the \emph{Antigone}}
\date{April 2013}
\maketitle

%if codeOnly || showModuleHeader

> {-# LANGUAGE StandaloneDeriving        #-}
> {-# LANGUAGE DeriveFunctor             #-}
> {-# LANGUAGE NoMonomorphismRestriction #-}

> module Analyze where

> import Control.Applicative
> import Control.Monad ((>=>))
> import Control.Arrow((&&&))
> import Data.Monoid
> import Data.Foldable
> import Debug.Trace
> import Data.Maybe (isJust, maybeToList, catMaybes)
> import Data.Tree
> import Data.List (genericLength, nub, findIndex, sortBy)
> import Data.Function (on)
> import Data.Ratio
> import Text.XML.Light
> import Text.Printf
> import Prelude hiding (maximum, minimum, foldl, notElem, elem, concat, sum)


%endif

\noindent \textbf{THIS IS A DRAFT.} It is currently lacking a bibliography, and
the analysis is a bit just-so, I'm afraid. I also intend to add a section about
how specific choices made about data representation by Perseus annotators can
affect such an analysis as I have given here.

In this paper, I will show how, and to what degree, phrase projectivity
corresponds with register and meter in Sophocles's \emph{Antigone}, by
developing a quantitative metric for projectivity and comparing it across
lyrics, trimeters and anapaests using the data provided by the Perseus Ancient
Greek Dependency Treebank. In the appendices, the formal algorithm for the
computations done herein is developed in the programming language Haskell.

\section{Dependency Trees and Their Projectivity}

A dependency tree encodes the head-dependent relation for a string of words,
where arcs are drawn from heads to their dependents. We consider a phrase
\emph{projective} when these arcs do not cross each other, and
\emph{discontinuous} to the extent that any of the arcs intersect.
Figure~\ref{fig:dependency-trees1} is a minimal pair that demonstrates how
hyperbaton introduces a projectivity violation; in this case, a path of
dependency ``wraps around itself''.

\begin{figure}[h!]
\centering
\subfigure[``Full of plentiful supplies'' (Xenophon, \emph{Anabasis} 3.5.1) is fully projective.]{
  \xytext{
    \gkbarnode{μεστῇ}\xybarconnect[6](U,U){2}&
    \gkbarnode{πολλῶν}&
    \gkbarnode{ἀγα\salt{θ}ῶν}\xybarconnect[3](UL,U){-1}
  }
}
\hspace{6pt}
\subfigure[``Full of many good things'' (Plato, \emph{Laws} 906a) has one
projectivity violation.]{
  \xytext{
    \gkbarnode{πολλῶν}&
    \gkbarnode{μεστὸν}\xybarconnect[6]{1}&
    \gkbarnode{ἀγα\salt{θ}ῶν}\xybarconnect[3](UL,U){-2}
  }
}

\caption{Examples drawn from Devine~\&~Stephens.}
\label{fig:dependency-trees1}
\end{figure}

In addition to the above, adjacent phrases (that is, phrases at the same level
in the tree) may interlace, causing projectivity violations. This is commonly
introduced by Wackernagel's Law, as in Figure~\ref{fig:wackernagel}, where the
placement of \textgreek{μὲν δὴ} interlaces with the \textgreek{τὰ...πόλεος} phrase.

\begin{figure}[h!]
\centering
\xytext{
    \gkbarnode{τὰ}\xybarconnect[6]{3}&
    \gkbarnode{μὲν}\xybarconnect[3](UR,U){1}&
    \gkbarnode{δὴ}&
    \gkbarnode{πόλεος}&
    \gkbarnode{...}&
    \gkbarnode{ὤρ\salt{θ}ησαν}\xybarconnect[9](U,UL){-5}\xybarconnect[9]{-4}
}
\caption{``[The gods] righted the matters of the city...'' (\emph{Antigone}
162--163) has
one projectivity violation, due to the \textgreek{μὲν δὴ} falling in Wackernagel's Position.}
\label{fig:wackernagel}
\end{figure}

We consider a violation to have occured for each and every intersection of lines
on such a drawing; thus, the hyperbaton of one word may introduce multiple
violations. Consider, for instance, Figure~\ref{fig:stas-tree}, in which five
violations are brought about by the displacement of \textgreek{φονώσαισιν}. In
this way, the number of intersections is a good heuristic for judging the
severity of hyperbata.

\begin{figure}[h!]
\centering
\xytext{
  \gkbarnode{στὰς}\xybarconnect[6]{2} &
  \gkbarnode{δ'} &
  \gkbarnode{ὑπὲρ}\xybarconnect[3](UR,U){1} &
  \gkbarnode{μελά\salt{θ}ρων} &
  \gkbarnode{φονώσαισιν} &
  \gkbarnode{ἀμφι}
    \xybarconnect[6](UR,U){3} &
  \gkbarnode{\!\!\!χανὼν}
    \xybarconnect[6](U,U){1}
    \xybarconnect[6](UL,U){4}&
  \gkbarnode{κύκλῳ} &
  \gkbarnode{λόγχαις}\xybarconnect[3](UL,U){-4} &
  \gkbarnode{ἑπτάπυλον} &
  \gkbarnode{στόμα}\xybarconnect[3](UL,U){-1} &
  \gkbarnode{ἔβα}
    \xybarconnect[9](U,UL){-11}
    \xybarconnect[9](U,U){-10}
    \xybarconnect[9](U,U){-6}
}
\caption{``And he stood over the rooftops, gaped in a circle with murderous
spears around the seven-gated mouth, and left'' (\emph{Antigone} 117--120) has
six projectivity violations, five of which are induced by the hyperbaton of
\textgreek{φονώσαισιν}, and one from the usual placement of δ' in Wackernagel's
Position.}
\label{fig:stas-tree}
\end{figure}

\subsection{Counting Violations}

Drawing trees and counting intersections is time-consuming and error-prone,
especially since the number of intersections may vary if one is not consistent
with the relative height of arcs and placement of endpoints. It is clear, then,
that a computer ought to be able to do the job faster and more accurately than a
human, given at least the head-dependent relations for a corpus.

The formal algorithm for counting the number of intersections is given in
Appendix~\ref{sec:counting}, but I shall reproduce an informal and mostly
nontechnical version of it here. First, we index each word in the sentence by
its linear position, and cross-reference it with the linear position of its
head:

\begin{quote}
\gll στὰς δ' ὑπὲρ μελά\salt{θ}ρων φονώσαισιν ἀμφικανὼν κύκλῳ λόγχαις ἑπτάπυλον στόμα
ἔβα\\
      1:11  2:11 3:1 4:3 5:8 6:11 7:6 8:6 9:10 10:6 11:\_\\
\end{quote}

\noindent
Next, arrange the dependencies into a tree as in Figure~\ref{fig:rose-tree}.
Then, counting upwards from the lowest edges (i.e.\ the lines) in the tree up to
the topmost ones, make a list of edges indexed by vertical level as in
Table~\ref{tab:edges}.

\begin{figure}
  \Tree
  [.11
    [.1 [.3 4 ] ]
    2
    [.6
      7
      [.8 5 ]
      [.10 9 ]
    ]
  ]
\caption{The dependency relations arranged in a non-linear tree.}
\label{fig:rose-tree}
\end{figure}

\begin{table}
\centering
  \begin{tabular}{cl}
  \toprule
  \emph{level} & \emph{edges}\\
  \midrule
  1 & |3:-:4, 5:-:8, 9:-:10|\\
  2 & |1:-:3, 6:-:7, 6:-:8, 6:-:10|\\
  3 & |1:-:11, 2:-:11, 6:-:11|
  \\
  \bottomrule
  \end{tabular}
  \caption{Edges of the tree in Figure~\ref{fig:rose-tree} arranged by level.}
  \label{tab:edges}
\end{table}

Then, each edge in our table must be checked for violations against all the
other edges in the table except those which are in a level higher than it. The
level of the edge corresponds with the height at which we drew the arcs; this
condition arises out of the fact that an arc cannot cross an arc that is above
it.

Next, we must figure out all the possible ways for an arc to intersect another
at given levels. These are enumerated in detail in the function |checkEdges| in
Appendix~\ref{sec:counting}, but suffice it to say that they fall into a few
main categories:

\begin{enumerate}
\item Both vertices of the higher edge are within the bounds of the lower edge.
This is a double violation, as both sides of an arc will extrude through
another.
\item One vertex of the higher edge is within the bounds of the lower edge, and
the other vertex is not; this vertex is allowed to be equal to the second vertex
of the lower edge. In either case, this is a single violation, as just one
intersection occurs.
\item The edges are at the same level, and one vertex of the higher edge is
neither within bounds of the other, nor equal to any of the vertices of the
other. This is a single violation.
\end{enumerate}

\noindent
Using this procedure, we shall have found the edge violations which are listed
in Table~\ref{tab:violations}, which are |6| in total.

\begin{table}
\centering
\begin{tabular}{ccc}
\toprule
|2:-:11| & |1:-:3| & 1\\
|6:-:11| & |5:-:8| & 1\\
|6:-:7|  & |5:-:8| & 2\\
|6:-:8|  & |5:-:8| & 1\\
|6:-:10| & |5:-:8|  & 1\\
\midrule
\multicolumn{3}{r}{$\FN{total}$ | = 6|}\\
\bottomrule
\end{tabular}
\caption{Projectivity violations which arise from the edges in
Table~\ref{tab:edges}.}
\label{tab:violations}
\end{table}

\subsection{|omega|: a metric of projectivity}

In order for our view of a text's overall projectivity to not be skewed by its
length, we must have a ratio. For the purposes of this paper, we shall call this
metric |\omega|, as given by the following ratio:
%
\[ \wp = \frac{\text{number of violations}}{\text{number of arcs}} \]
%
Now, this metric applies just as much to a single sentence as it does to a
larger body of text. So, averages of |omega| should not be taken; rather, total
numbers of violations and total numbers of arcs should be accumulated until
|omega| may be computed for the entire body of text being examined.

\section{The Perseus Treebank}
%
The Perseus Ancient Greek Dependency Treebank is a massive trove of annotated
texts that encode all the dependency relations in every sentence. The data is
given in an XML (E\textbf{x}tensible \textbf{M}arkup \textbf{L}anguage) format
resembling the following:

\lstset{
  language=XML,
  escapeinside=**
}

\begin{lstlisting}
    <sentence id="2900759">
      <word id="1" form="*\color{gray}\textrm{\textgreek{\hlig{χρὴ}}}*" lemma="*\color{gray}\textrm{\textgreek{\hlig{χρή}}}*" head="0" />
      <word id="2" form="*\color{gray}\textrm{\textgreek{δὲ}}*" lemma="*\color{gray}\textrm{\textgreek{δέ}}*" head="1" />
      ...
    </sentence>
\end{lstlisting}

\noindent
%
Every sentence is given a unique, sequential identifier; within each sentence,
every word is indexed by its linear position and coreferenced with the linear
position of its dominating head. In the case of the data for the \emph{Antigone},
the maximal head of each sentence has its own head given as \lstinline{0}.
Appendix~\ref{sec:parsing} deals with parsing these XML representations into
dependency trees for which we can compute |omega|.

The Perseus data also includes punctuation in the dependency trees, which we
must of course filter out; a comma, for instance, may induce a technical
hyperbaton, simply by virtue of what the Perseus editors have chosen to mark as
its ``head'', to the extent that it means anything at all for a punctuation mark
to have a head.


\section{Projectivity in the \emph{Antigone}}

To observe the variation of projectivity within a text, then, one may make a
selection of sentences that have something in common, compute their trees and
thence derive a cumulative |omega| for the entire selection. Then that figure
may be compared with that of other selections.

I have chosen to compare projectivity in lyrics, anapaests and trimeters. Lyrics
I have divided into two categories: choral odes and laments, whereas I divide
trimeters into medium-to-long speeches and stichomythia.

To that end, I have selected passages from the \emph{Antigone} and organized
them by type. Table~\ref{tab:lyrics} enumerates the lyric passages of the play,
along with their computed |omega| values, and a cumulative |omega| value for the
entire set. Table~\ref{tab:anapaests} does the same for anapaests. Lastly,
Table~\ref{tab:dialogue} gives selections of dialogue (which is in iambic
trimeters), divided between medium-to-long speeches and stichomythia.

\begin{table}
  \centering
  \subtable[Choral Odes]{\perform{makeTable odes}}
  \vspace{6pt}
  \subtable[Laments]{\perform{makeTable kommoi}}
  \caption{Lyrics}
  \label{tab:lyrics}
\end{table}

\begin{table}
  \centering
  \perform{makeTable anapaests}
  \caption{Anapaests.}
  \label{tab:anapaests}
\end{table}

\begin{table}
  \centering
  \subfigure[Speeches and Dialogue]{\perform{makeTable speeches}}
  \vspace{6pt}
  \subfigure[Stichomythia]{\perform{makeTable stichos}}
  \caption{Dialogue (Trimeters)}
  \label{tab:dialogue}
\end{table}

As can be seen from the data, lyrics have the highest degree of
non-projectivity, followed by speeches, then anapaests, and then stichomythia.
To try and understand why this is the case, it will be useful to discuss Greek
hyperbaton in more general terms.

Whereas in prose, hyperbaton corresponds to \emph{strong focus}, which ``does
not merely fill a gap in the addressee's knowledge but additionally evokes and
excludes alternatives'' (Devine~\&~Stephens 303), hyperbaton in verse only
entails weak focus, which emphasizes but does not exclude (ibid.\ 107).

As a result, hyperbaton in verse may be used to evoke a kind of elevated style
without incidentally entailing more emphasis and other pragmatic effects than
intended. And so it should not be surprising that lyric passages, which reside
in the most poetic and elevated register present in tragic diction, should have
proved in the \emph{Antigone} to have the highest proportion of projectivity
violations.

Within the lyric passages, the laments appear to have consistently higher
|omega| than the choral odes, which may stem from their being much more emotive
and personal in nature. It should be noted that, whilst the individual odes
conform tightly to the cumulative |omega| of their category, there is a fair
degree of variation among the laments. Likewise, the anapaests vary so wildly in
their |omega| that it may be difficult to say very much about them that is
relevant to the questions we are considering.

As for dialog, longer-form speeches are largely conformant in their |omega|,
with stichomythias varying a bit more. Speeches are a somewhat less projective
than the stichomythias, being typically more eloquent and long-winded than their
argumentative, choppy counterparts.

So far, the most surprising thing about the data is the degree to which certain
verse-types vary in |omega| (or, if you like, the degree to which other types
\emph{don't}). The data draw us, then, to the following conclusions:

\begin{enumerate}
\item Non-projectivity varies within a single metrical type (lyrics, iambic trimeters,
anapaests).

\item Certain registers seem to be more conventionalized with respect to |omega|
than others; that is, choral odes and speeches do not vary greatly amongst
themselves, but laments and anapaests do.
\end{enumerate}

\noindent
%
Lyric passages are in general less projective than anything else, but some
laments reach a degree of non-projectivity that exceeds the most elliptical odes
in the \emph{Antigone}. Further, within the trimeters, speeches are less projective
than stichomythias. From these things, then, we can say that that meter itself
would not seem to be a primary factor for predicting incidence and severity of
hyperbaton, but rather a secondary one at best.

That is to say, we know for a fact that passages in lyric meters have greater
|omega| than passages in other meters. Yet, the variation of |omega| within that
very meter indicates that there is some other factor involved, which very likely
has to do with register along two different dimensions, which is to say,
relative ``dignity of style'' and emotive force.

With regard to the very low |omega| found in the stichomythias, I suggest that
it is the necessary shortness of each utterance which is at fault here. That is,
the maximum ``damage'' that a hyperbaton can do is greatly lessened, when the
ultimate depth of the phrase structure is limited by its length (whence, for
instance, it is unlikely for a single hyperbaton to cause more than a few
projectivity violations).

\newpage
\begin{appendices}

The functions used in parsing and computing the data for this paper are
developed here in the programming language Haskell. Haskell is a typed lambda
calculus with inductive data types and type classes; the listings below use
standard Haskell syntax with the exception of some infix operators to improve
readability, and the addition of so-called ``idiom brackets'', which allow a
more syntactically clean presentation of function application within a
context.

\section{Algorithm \& Data Representation}
\label{sec:algorithm}

Dependency trees are a recursive data structure with a head node, which may have
any number of arcs drawn to further trees (this is called a \emph{rose tree}).
We represent them as a Haskell data-type as follows:

< data Tree a = Node a [Tree a]

This can be read as ``For all types |a|, a |Tree| of |a| is constructed from a
\emph{label} of type |a| and a \emph{subforest} of |Tree|s of |a|,'' where brackets are a notation
for lists.

Given a tree, we can extract its root label or its subforest by pattern matching
on its structure as follows:

> getLabel :: Tree a -> a
> getLabel (Node l _) = l
> getForest :: Tree a -> [Tree a]
> getForest (Node _ ts) = ts

\subsection{From Edges to Trees}
\label{sec:edges-to-trees}

We shall consider each word index to be a \emph{vertex}, and each pair of
vertices to be an |Edge|, which we shall write as follows:

> data Edge a = a :-: a deriving Eq

\ignore{

> deriving instance Show a => Show (Edge a)
> deriving instance Show Sentence

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

%format heads = "\FN{heads}"
%format deps = "\FN{deps}"

> rootVertex :: Eq a => [Edge a] -> Maybe a
> rootVertex es = find (`notElem` deps) heads where
>   heads  = liftA (\(x :-: y) -> x) es
>   deps   = liftA (\(x :-: y) -> y) es

If the data that we are working with are not well-formed, there is a chance that
we will not find a root vertex; that is why the type is given as |Maybe|.

Then, given a root vertex, we look to find all the edges that
it touches, and try to build the subtrees that are connected with those edges.

> onEdge :: Eq a => a -> Edge a -> Bool
> onEdge i (x :-: y) = x == i || y == i
>
> oppositeVertex :: Eq a => a -> Edge a -> a
> oppositeVertex i (x :-: y)
>   | x == i     = y
>   | otherwise  = x

This is done recursively until the list of edges is exhausted and we have a
complete tree structure:

%format buildWithRoot = "\FN{buildWithRoot}"
%format sortedChildren = "\FN{sortedChildren}"
%format children = "\FN{children}"
%format roots = "\FN{roots}"
%format localVertices = "\FN{localVertices}"
%format foreignVertices = "\FN{foreignVertices}"

> treeFromEdges :: Ord a => [Edge a] -> Maybe (Tree a)
> treeFromEdges es = liftA (buildWithRoot es) (rootVertex es) where
>   buildWithRoot es root = Node root sortedChildren where
>     roots            = liftA (oppositeVertex root) localVertices
>     children         = liftA (buildWithRoot foreignVertices) roots
>     localVertices    = filter (onEdge root) es
>     foreignVertices  = filter (not . onEdge root) es
>     sortedChildren   = sortBy (compare `on` getLabel) children


\subsection{Counting Violations}
\label{sec:counting}

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
< levels t = fmap (fmap getLabel) $
<             takeWhile (not . null) $
<             iterate (>>= getForest) [t]

> depth :: Tree a -> Integer
> depth = genericLength . levels

We can now annotate each node in a tree with what level it is at:

> annotateLevels :: Tree a -> Tree (Level, a)
> annotateLevels = liftA2 aux depth id where
>   aux l (Node x ts) = Node (l, x) (liftA (aux (l - 1)) ts)

Then, we fold up the tree into a list of edges and levels:

%format go = "\FN{go}"

> allEdges :: Ord a => Tree a -> [(Level, Edge a)]
> allEdges = aux . annotateLevels where
>   aux (Node (_,x) ts) = ts >>= go where
>     go t@(Node (l, y) _) = (l, edgeWithRange [x,y]) : aux t

> edgeWithRange :: Ord a => [a] -> Edge a
> edgeWithRange = liftOp2 (:-:) minimum maximum

A handy way to think of edges annotated by levels is as a representation of the
arc itself, where the vertices of the edge are the endpoints, and the level is the
height of the arc. Now, we can count the violations that occur between two arcs.

> checkEdges :: Ord a => (Level, Edge a) -> (Level, Edge a) -> Integer
> checkEdges (l, xy@(x :-: y)) (l', uv@(u :-: v))
>   | inRange x uv && ((y >= v && l > l') || y > v)  = 1
>   | inRange y uv && ((x <= u && l > l') || u < u)  = 1
>   | inRange u xy && ((v >= y && l < l') || v > y)  = 1
>   | inRange v xy && ((u <= x && l < l') || u < x)  = 1
>   | inRange x uv && inRange y uv && l >= l'        = 2
>   | inRange u xy && inRange v xy && l <= l'        = 2
>   | otherwise                                      = 0

We determine whether a vertex is in the bounds of an edge using |inRange|.

> inRange :: Ord a => a -> Edge a -> Bool
> inRange z (x :-: y)  =   z > minimum   [x,y]
>                      &&  z < maximum   [x,y]

\ignore{

> notInRange x xy = not (inRange x xy)

}
%
We can now use what we've built to count the intersections that occur in a
collection of edges. This is done by adding up the result of |checkEdges| of the
combination of each edge with the subset of edges which are at or below its
level:

%format rangesBelow = "\FN{rangesBelow}"
%format violationsWith = "\FN{violationsWith}"

> edgeViolations :: Ord a => [(Level, Edge a)] -> Integer
> edgeViolations xs = sum (liftA violationsWith xs) where
>   rangesBelow (l, _)  = filter (\(l', _) -> l' <= l) xs
>   violationsWith x    = sum (liftA (checkEdges x) (rangesBelow x))

\subsection{Computing |omega|}
\label{sec:computing-omega}

We introduce a data type |Omega| of integer-to-integer ratios which may be
computed into a rational.

%format edgeCount = "\FN{edgeCount}"
%format violationCount = "\FN{violationCount}"
%format liftRatio f g = "\left\llbracket" ^^ "\dfrac{" f "}{" g "}\right\rrbracket"

> data Omega = Omega { violationCount :: Integer, edgeCount :: Integer }
> computeOmega :: Omega -> Rational
> computeOmega = liftRatio violationCount edgeCount

\ignore{

> liftRatio = liftA2 ratio

}

\noindent
Furthermore, |Omega|s generate a monoid, which is an algebraic structure that
abstracts out the notion of an identity and an associative binary operation that
respects that identity. In this way, we can combine |Omega| values:

> instance Monoid Omega where
>   mempty = Omega 0 0
>   mappend (Omega x y) (Omega u v) = Omega (x + u) (y + v)

Finally, |omega| may be computed for trees.

> omega :: Ord a => Tree a -> Omega
> omega = liftA2 Omega edgeViolations genericLength . allEdges

\section{Working with the Perseus Treebank}
\label{sec:working-with-treebase}

\subsection{Parsing the XML}
\label{sec:parsing}

\noindent
We can express the general shape of a treebank document as follows:

%format sequence = "\FN{sequence}"
%format sentenceFromXML = "\FN{sentenceFromXML}"
%format sentenceId = "\FN{sentenceId}"
%format sentenceEdges = "\FN{sentenceEdges}"
%format edgeFromXML = "\FN{edgeFromXML}"
%format documentFromXML = "\FN{documentFromXML}"
%format treesFromDocument = "\FN{treesFromDocument}"

> type Document = [Sentence]
> data Sentence = Sentence { sentenceId :: Integer, sentenceEdges :: [Edge Integer] }

To construct a |Document| from the contents of an XML file, it suffices to
find all of the sentences.

%format elems = "\FN{elems}"

> documentFromXML :: [Content] -> Document
> documentFromXML xml = catMaybes (liftA sentenceFromXML elems) where
>   elems = onlyElems xml >>= findElements (simpleName "sentence")

|Sentence|s are got by taking the contents of their \lstinline{id} attribute,
and extracting edges from their children.

%format edges = "\FN{edges}"

> sentenceFromXML :: Element -> Maybe Sentence
> sentenceFromXML e = liftA2 Sentence (readAttr "id" e) (pure edges) where
>   edges     = catMaybes (liftA edgeFromXML children)
>   children  = findChildren (simpleName "word") e

An edge is got from an element by taking the contents of its \lstinline{id}
attribute with the contents of its \lstinline{head} attribute. We make sure to
filter out punctuation which would skew our data.

> edgeFromXML :: Element -> Maybe (Edge Integer)
> edgeFromXML e =
>   case findAttr (simpleName "form") e of
>      Just x | x `elem` [".",",",";",":"] -> Nothing
>      otherwise -> liftOp2 (:-:) (readAttr "head" e) (readAttr "id" e)

Thence, turn a sentence into a tree by its edges using the machinery from
Section~\ref{sec:edges-to-trees}.

> treeFromSentence :: Sentence -> Maybe (Tree Integer)
> treeFromSentence (Sentence _ ws) = treeFromEdges ws

By applying |treeFromSentence| to every sentence within a document, we can
generate all the trees in a document.

> treesFromDocument :: Document -> [Tree Integer]
> treesFromDocument ss = catMaybes (liftA treeFromSentence ss)

By combining the above, we also may derive a document structure from a file on
disk.

%format documentFromFile = "\FN{documentFromFile}"

> documentFromFile :: FilePath -> IO Document
> documentFromFile path = liftA (documentFromXML . parseXML) (readFile path)

\subsection{Analysis of Data}
\label{sec:analyzing}

We compute the cumulative |omega| of the trees contained in a document as follows:

> analyzeDocument :: Document -> Omega
> analyzeDocument doc = mconcat (liftA omega (treesFromDocument doc))

We will wish to compare the |omega| for parts of the \emph{Antigone}. A section
is given by a two sentence indices (a beginning and an end):

> data Section = MkRange Integer Integer

Then, the entire document can be cut down into smaller documents by section:

%format restrictDocument = "\FN{restrictDocument}"
%format withinSection = "\FN{withinSection}"

> restrictDocument :: Section -> Document -> Document
> restrictDocument (MkRange start finish) = filter withinSection where
>   withinSection (Sentence i _) = i >= start && i <= finish

\ignore{

> makeTable :: [(Section, Section, String)] -> IO UnquotedString
> makeTable sections = do
>   antigone <- documentFromFile "antigone.xml"
>   let pre = "\\begin{tabular}{clc}\\toprule\\textbf{Lines}&\\textbf{}&|omega|\\\\ \\midrule"
>   let post = "\\bottomrule\\end{tabular}"
>   let omegas = (\(_,r,_) -> analyzeDocument $ restrictDocument r antigone) <$> sections
>   let totalOmega = computeOmega $ mconcat omegas
>   let body = fold $ uncurry makeTableRow <$> zip sections (computeOmega <$> omegas)
>   let avg = "\\midrule\\multicolumn{3}{r}{|cumulative omega| = |" ++ showRational totalOmega ++ "|}\\\\"
>   return . Unquote $ pre ++ body ++ avg ++ post

> showRational x = printf "%.2f" (fromInteger (round $ x * (10^2)) / (10.0**2) :: Float)

> makeTableRow :: (Section, Section, String) -> Rational -> String
> makeTableRow (ls, r, d) om = lines ++ "&" ++ desc ++ "&" ++ omega ++ "\\\\" where
>   desc = "\\emph{" ++ d ++ "}"
>   lines = "|" ++ show ls ++ "|"
>   range = "|" ++ show r ++ "|"
>   omega = "|" ++ showRational om ++ "|"

> deriving instance Show Section
> newtype UnquotedString = Unquote String
> instance Show UnquotedString where
>   show (Unquote str) = str

> odes :: [(Section, Section, String)]
> odes =  [  (MkRange 100 154,    MkRange 2900135 2900144, "First choral ode"),
>            (MkRange 332 375,    MkRange 2900236 2900247, "Second choral ode"),
>            (MkRange 583 625,    MkRange 2900390 2900402, "Third choral ode"),
>            (MkRange 781 800,    MkRange 2900496 2900501, "Fourth choral ode"),
>            (MkRange 944 987,    MkRange 2900554 2900566, "Fifth choral ode"),
>            (MkRange 1116 1152,  MkRange 2900649 2900654, "Sixth choral ode")
>         ]

> kommoi = [
>            (MkRange 806 816,    MkRange 2900503 2900504, "Antigone's Lament"),
>            (MkRange 823 833,    MkRange 2900506 2900507, "Antigone's Lament (cntd.)"),
>            (MkRange 839 882,    MkRange 2900511 2900526, "Antigone's Lament (cntd.)"),
>            (MkRange 1261 1269,  MkRange 2900714 2900716, "Kreon's Lament"),
>            (MkRange 1283 1292,  MkRange 2900725 2900729, "Kreon's Lament (cntd.)"),
>            (MkRange 1306 1311,  MkRange 2900737 2900739, "Kreon's Lament (cntd.)"),
>            (MkRange 1317 1325,  MkRange 2900743 2900745, "Kreon's Lament (cntd.)"),
>            (MkRange 1239 1246,  MkRange 2900756 2900767, "Kreon's Lament (cntd.)")
>          ]


> anapaests :: [(Section, Section, String)]
> anapaests =  [  (MkRange 155 161,    MkRange 2900145 2900145, "Kreon's Entrance"),
>                 (MkRange 376 383,    MkRange 2900248 2900251, "Antigone's Entrance"),-- sung
>                 (MkRange 526 530,    MkRange 2900345 2900346, "Ismene's Entrance"),
>                 (MkRange 626 630,    MkRange 2900403 2900404, "Haimon's Entrance"),
>                 (MkRange 801 805,    MkRange 2900502 2900502, "Antigone's Entrance"),
>                 (MkRange 817 822,    MkRange 2900505 2900505, "Chorus to Antigone"),
>                 (MkRange 834 838,    MkRange 2900508 2900510, "Chorus to Antigone"),
>                 (MkRange 929 943,    MkRange 2900548 2900553, "Chorus, Kreon and Antigone"),
>                 (MkRange 1257 1260,  MkRange 2900713 2900713, "Chorus before Kreon's Kommos"),
>                 (MkRange 1347 1353,  MkRange 2900758 2900760, "Final anapaests of the Chorus")
>              ]

> speeches :: [(Section, Section, String)]
> speeches =  [  (MkRange 162 210,    MkRange 2900146 2900157, "\\emph{Kreon: \\textgreek{ἄνδρες, τὰ μὲν δὴ...}}"),
>                (MkRange 249 277,    MkRange 2900191 2900204, "\\emph{Guard: \\textgreek{οὐκ οἶδ'· ἐκ\\hlig{εῖ} γὰρ οὔτε...}}"),
>                (MkRange 280 314,    MkRange 2900206 2900220, "\\emph{Kreon: \\textgreek{παῦσαι, πρὶν ὀργῆς...}}"),
>                (MkRange 407 440,    MkRange 2900271 2900282, "\\emph{Guard: \\textgreek{τοιοῦτον ἦν τὸ πρᾶγμ'...}}"),
>                (MkRange 450 470,    MkRange 2900291 2900302, "\\emph{Antigone: \\textgreek{οὐ γάρ τί μοι Ζεὺς...}}"),
>                (MkRange 473 495,    MkRange 2900305 2900316, "\\emph{Kreon: \\textgreek{ἀλλ' ἴσ\\salt{θ}ι τοι...}}"),
>                (MkRange 639 680,    MkRange 2900410 2900427, "\\emph{Kreon: \\textgreek{οὕτω γὰρ, ὦ παῖ...}}"),
>                (MkRange 683 723,    MkRange 2900429 2900446, "\\emph{Haimon: \\textgreek{πἀτερ, \\salt{θ}εοὶ φύουσιν...}}"),
>                (MkRange 891 928,    MkRange 2900531 2900547, "\\emph{Antigone: \\textgreek{ὦ τύμβος, ὦ νυμφ\\hlig{εῖ}ον...}}"),
>                (MkRange 998 1032,   MkRange 2900577 2900595, "\\emph{Teiresias: \\textgreek{γνώσῃ, τέχνης σημ\\hlig{εῖ}α...}}"),
>                (MkRange 1033 1047,  MkRange 2900596 2900601, "\\emph{Kreon: \\textgreek{ὦ πρέσβυ, πάντες...}}"),
>                (MkRange 1064 1090,  MkRange 2900621 2900628, "\\emph{Teiresias: \\textgreek{ἀλλ' εὖ γέ τοι...}}"),
>                (MkRange 1155 1172,  MkRange 2900655 2900662, "\\emph{Messenger: \\textgreek{Κάδμου πάροικοι καὶ...}}"),
>                (MkRange 1192 1243,  MkRange 2900681 2900703, "\\emph{Messenger: \\textgreek{ἐγώ, φίλη δέσποινα...}}") ]
>

> stichos :: [(Section, Section, String)]
> stichos =  [  (MkRange 536 576,    MkRange 2900348 2900385, "Ismene, Antigone and Kreon"),
>               (MkRange 728 757,    MkRange 2900450 2900480, "Haimon and Kreon"),
>               (MkRange 991 997,    MkRange 2900569 2900576, "Kreon and Teiresias"),
>               (MkRange 1047 1063,  MkRange 2900602 2900620, "Kreon and Teiresias"),
>               (MkRange 1172 1179,  MkRange 2900663 2900674, "Chorus and Messenger")
>            ]

}


\ignore{

> simpleName :: String -> QName
> simpleName s = QName s Nothing Nothing

> readAttr :: Read a => String -> Element -> Maybe a
> readAttr n = fmap read . findAttr (simpleName n)


< mean :: Fractional n => [n] -> n
< mean =  liftOp2 (/) sum genericLength

< sdev :: Floating n => [n] -> n
< sdev xs = sqrt (divFrac (sum (liftA (\x -> power x 2) (liftA (- (mean xs) +) xs))) (genericLength xs - 1))

> liftOp2 = liftA2
> ratio = (%)
> divFrac = (/)

> power x n = x ^ n

}

\end{appendices}
\end{document}


