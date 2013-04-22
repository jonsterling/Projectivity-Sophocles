%!TEX encoding = UTF-8 Unicode

\documentclass{article}

%options ghci -fglasgow-exts
%include Analyze.fmt

\usepackage{setspace,homework,stmaryrd,wasysym,url,upgreek,subfigure}
\usepackage[margin=1cm]{caption}
\usepackage{xytree, listings}
\usepackage[toc,page]{appendix}

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
\setmainfont{Times New Roman}

\author{Jonathan Sterling}

\title{A Survey of Phrase Projectivity in \emph{Antigone}}
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

\noindent
%
In this paper, I will show how phrase projectivity (which corresponds to lacking
hyperbaton) is linked to register and meter in Sophocles's \emph{Antigone}, by
developing a quantitative metric for projectivity and comparing it across
lyrics, trimeters and anapaests.

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
%
In this paper, we shall use a concrete metric of projectivity, $\omega$, given
by the following ratio:
%
\[ \omega = \frac{\text{number of violations}}{\text{number of arcs}} \]
%
The number of violations is simply the total number of intersections that occur
in a tree. Appendix~\ref{sec:algorithm} deals with the development of a model
and algorithm in the programming language Haskell to compute this quantity for a
particular dependency tree.


\section{The Perseus Treebank}
%
The Perseus Ancient Greek Dependency Treebank is a massive trove of annotated
texts that encode the all dependency relations in every sentence. The data is
given in an XML (E\textbf{x}tensible \textbf{M}arkup \textbf{L}anguage) format
resembling the following:

\lstset{
  language=XML,
  escapeinside=**
}

\begin{lstlisting}
    <sentence id="2900759">
      <word id="1" form="*\color{gray}\textrm{χρὴ}*" lemma="*\color{gray}\textrm{χρή}*" head="0" />
      <word id="2" form="*\color{gray}\textrm{δὲ}*" lemma="*\color{gray}\textrm{δέ}*" head="1" />
      ...
    </sentence>
\end{lstlisting}

\noindent
%
Every sentence is given a unique, sequential identifier; within each sentence,
every word is indexed by its linear position and coreferenced with the linear
position of its dominating head. In the case of the data for \emph{Antigone},
the maximal head of each sentence has its own head given as \lstinline{0}.
Appendix~\ref{sec:parsing} deals with parsing these XML representations into
dependency trees for which we can compute |omega|.


\section{Projectivity in Antigone}

To observe the variation of projectivity within a text, then, one may make a
selection of sentences that have something in common (such as meter), compute
their trees and thence derive |omega|, and then average the results. Then that
quantity may be compared with that of other selections.

To that end, I have selected passages from \emph{Antigone} and organized them by
type. Table~\ref{tab:lyrics} enumerates the lyric passages of the play, along
with their computed mean |omega| values, and a final mean of means with the
standard deviation of the set.  Table~\ref{tab:anapaests} does the same for
anapaests. Lastly, Table~\ref{tab:dialogue} gives the data for dialogue (which
is in iambic trimeters), divided between medium-to-long speeches and
stichomythia.

\begin{table}
  \centering
  \perform{makeTable lyrics}
  \caption{Lyrics, including odes and kommoi.}
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
However, the standard deviation of the |omega| for anapaestic passages is so
high that it may be difficult to say much of interest about them at all in
respect to the questions that we are considering. So, let us put the anapaests
aside for the moment and deal exclusively with lyrics, speeches and
stichomythias.

Whereas in prose, hyperbaton corresponds to \emph{strong
focus}, which ``does not merely fill a gap in the addressee's knowledge but
additionally evokes and excludes alternatives'' (Devine~\&~Stephens 303),
hyperbaton in verse only entails weak focus, which emphasizes but does not
exclude (ibid.\ 107).

As a result, hyperbaton in verse may be used to evoke a kind of
elevated style without incidentally entailing more emphasis and other pragmatic
effects than intended. And so it should not be surprising that lyric passages,
which reside in the most poetic and elevated register present in tragic diction,
should have proved in \emph{Antigone} to have the highest proportion of
projectivity violations.











\newpage
\begin{appendices}
\section{Algorithm \& Data Representation}
\label{sec:algorithm}

Dependency trees are a recursive data structure
with a head node, which may have any number of arcs drawn to further trees (this
is called a \emph{rose tree}). We represent them as a Haskell data-type as
follows:

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
< levels t = fmap (fmap getLabel) $
<             takeWhile (not . null) $
<             iterate (>>= getForest) [t]

> depth :: Tree a -> Integer
> depth = genericLength . levels

We can now annotate each node in a tree with what level it is at:

> annotateLevels :: Tree a -> Tree (Level, a)
> annotateLevels tree = aux (depth tree) tree where
>   aux l (Node x ts) = Node (l, x) (liftA (aux (l - 1)) ts)

Then, we fold up the tree into a list of edges and levels:

%format go = "\FN{go}"

> allEdges :: Ord a => Tree a -> [(Level, Edge a)]
> allEdges tree = aux (annotateLevels tree) where
>   aux (Node (_,x) ts) = ts >>= go where
>     go t@(Node (l, y) _) = (l, edgeWithRange [x,y]) : aux t

> edgeWithRange :: (Ord a) => [a] -> Edge a
> edgeWithRange xs = minimum xs :-: maximum xs

A handy way to think of edges annotated by levels is as a representation of the
arc itself, where the vertices of the edge are the endpoints, and the level is the
height of the arc.

If one end of an arc is between the ends of another, then there is a single
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
> inRange z (x :-: y)  =   z > minimum   [x,y]
>                      &&  z < maximum   [x,y]

We can now use what we've built to count the intersections that occur in a
collection of edges. This is done by adding up the result of |checkEdges| of the
combination of each edge with the subset of edges which are at or below its
level:

%format rangesBelow = "\FN{rangesBelow}"
%format violationsWith = "\FN{violationsWith}"

> edgeViolations :: Ord a => [(Level, Edge a)] -> Violations
> edgeViolations xs = sum (liftA violationsWith xs) where
>   rangesBelow (l, _)  = filter (\(l', _) -> l' <= l) xs
>   violationsWith x    = sum (liftA (checkEdges x) (rangesBelow x))

Finally, |omega| is computed for a tree as follows:

%format edges = "\FN{edges}"
%format totalArcsCount = "\FN{totalArcsCount}"
%format violationsCount = "\FN{violationsCount}"

> omega :: Ord a => Tree a -> Rational
> omega tree = ratio (edgeViolations edges) (genericLength edges) where
>   edges = allEdges tree


\newpage
\section{Parsing the Perseus Treebank}
\label{sec:parsing}

\noindent
We can express the general shape of such a document as follows:

%format sequence = "\FN{sequence}"
%format sentenceFromXML = "\FN{sentenceFromXML}"
%format sentenceId = "\FN{sentenceId}"
%format sentenceEdges = "\FN{sentenceEdges}"
%format edgeFromXML = "\FN{edgeFromXML}"
%format documentFromXML = "\FN{documentFromXML}"
%format treesFromDocument = "\FN{treesFromDocument}"

> type Document = [Sentence]
> data Sentence = Sentence { sentenceId :: Integer, sentenceEdges :: [Edge Integer] } deriving Show

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
attribute with the contents of its \lstinline{head} attribute.

> edgeFromXML :: Element -> Maybe (Edge Integer)
> edgeFromXML e =
>   case findAttr (simpleName "form") e of
>      Just x | elem x [".",",",";",":"] -> Nothing
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

\section{Analysis of Data}

We compute the mean |omega| of the trees contained in a document as follows:

> analyzeDocument :: Document -> Rational
> analyzeDocument doc = mean (liftA omega (treesFromDocument doc))

We will wish to compare the |omega| for parts of \emph{Antigone}. A section is
given by a two sentence indices (a beginning and an end):

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
>   let body = fold $ uncurry makeTableRow <$> zip sections omegas
>   let avg = "\\midrule\\multicolumn{3}{r}{|mean omega| = |" ++ showRational (mean omegas)
>               ++ " |, |sdev| = |" ++ showRational (sdev (fromRational <$> omegas)) ++ "|}\\\\"
>   return . Unquote $ pre ++ body ++ avg ++ post

> showRational x = printf "%.2f" ((fromInteger $ round $ x * (10^2)) / (10.0^^2) :: Float)

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

> lyrics :: [(Section, Section, String)]
> lyrics =  [  (MkRange 100 154,    MkRange 2900135 2900144, "First choral ode"),
>              (MkRange 332 375,    MkRange 2900236 2900247, "Second choral ode"),
>              (MkRange 583 625,    MkRange 2900390 2900402, "Third choral ode"),
>              (MkRange 781 800,    MkRange 2900496 2900501, "Fourth choral ode"),
>              (MkRange 806 816,    MkRange 2900503 2900504, "Antigone's Kommos"),
>              (MkRange 823 833,    MkRange 2900506 2900507, "Antigone's Kommos (cntd.)"),
>              (MkRange 839 882,    MkRange 2900511 2900526, "Antigone's Kommos (cntd.)"),
>              (MkRange 944 987,    MkRange 2900554 2900566, "Fifth choral ode"),
>              (MkRange 1116 1152,  MkRange 2900649 2900654, "Sixth choral ode"),
>              (MkRange 1261 1269,  MkRange 2900714 2900716, "Kreon's Kommos"),
>              (MkRange 1283 1292,  MkRange 2900725 2900729, "Kreon's Kommos (cntd.)"),
>              (MkRange 1306 1311,  MkRange 2900737 2900739, "Kreon's Kommos (cntd.)"),
>              (MkRange 1317 1325,  MkRange 2900743 2900745, "Kreon's Kommos (cntd.)"),
>              (MkRange 1239 1246,  MkRange 2900756 2900767, "Kreon's Kommos (cntd.)")
>           ]


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
> speeches =  [  (MkRange 162 210,    MkRange 2900146 2900157, "\\emph{Kreon:} ἄνδρες, τὰ μὲν δὴ..."),
>                (MkRange 249 277,    MkRange 2900191 2900204, "\\emph{Guard:} οὐκ οἶδ'· ἐκεῖ γὰρ οὔτε..."),
>                (MkRange 280 314,    MkRange 2900206 2900220, "\\emph{Kreon:} παῦσαι, πρὶν ὀργῆς..."),
>                (MkRange 407 440,    MkRange 2900271 2900282, "\\emph{Guard:} τοιοῦτον ἦν τὸ πρᾶγμ'..."),
>                (MkRange 450 470,    MkRange 2900291 2900302, "\\emph{Antigone:} οὐ γάρ τί μοι Ζεὺς..."),
>                (MkRange 473 495,    MkRange 2900305 2900316, "\\emph{Kreon:} ἀλλ' ἴσθι τοι..."),
>                (MkRange 639 680,    MkRange 2900410 2900427, "\\emph{Kreon:} οὕτω γὰρ, ὦ παῖ..."),
>                (MkRange 683 723,    MkRange 2900429 2900446, "\\emph{Haimon:} πἀτερ, θεοὶ φύουσιν..."),
>                (MkRange 891 928,    MkRange 2900531 2900547, "\\emph{Antigone:} ὦ τύμβος, ὦ νυμφεῖον..."),
>                (MkRange 998 1032,   MkRange 2900577 2900595, "\\emph{Teiresias:} γνώσῃ, τέχνης σημεῖα..."),
>                (MkRange 1033 1047,  MkRange 2900596 2900601, "\\emph{Kreon:} ὦ πρέσβυ, πάντες..."),
>                (MkRange 1064 1090,  MkRange 2900621 2900628, "\\emph{Teiresias:} ἀλλ' εὖ γέ τοι..."),
>                (MkRange 1155 1172,  MkRange 2900655 2900662, "\\emph{Messenger:} Κάδμου πάροικοι καὶ..."),
>                (MkRange 1192 1243,  MkRange 2900681 2900703, "\\emph{Messenger:} ἐγώ, φίλη δέσποινα...") ]
>

> stichos :: [(Section, Section, String)]
> stichos =  [  (MkRange 536 576,    MkRange 2900348 2900385, "Ismene, Antigone and Kreon"),
>               (MkRange 728 757,    MkRange 2900450 2900480, "Haimon and Kreon"),
>               (MkRange 991 997,    MkRange 2900569 2900576, "Kreon and Teiresias"),
>               (MkRange 1047 1063,  MkRange 2900602 2900620, "Kreon and Teiresias"),
>               (MkRange 1172 1179,  MkRange 2900663 2900674, "Chorus and Messenger")
>            ]

}


\section*{Auxiliary Functions}

> simpleName :: String -> QName
> simpleName s = QName s Nothing Nothing

> readAttr :: Read a => String -> Element -> Maybe a
> readAttr n = fmap read . findAttr (simpleName n)

> mean :: Fractional n => [n] -> n
> mean =  liftOp2 (/) sum genericLength

> sdev :: Floating n => [n] -> n
> sdev xs = sqrt (divFrac (sum (liftA (\x -> power x 2) (liftA (- (mean xs) +) xs))) (genericLength xs - 1))


\ignore{

> liftOp2 = liftA2
> ratio = (%)
> divFrac = (/)

> power x n = x ^ n

}

\end{appendices}
\end{document}


