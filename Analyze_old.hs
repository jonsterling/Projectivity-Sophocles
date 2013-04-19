{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies      #-}
{-# LANGUAGE TypeOperators     #-}
{-# LANGUAGE UnicodeSyntax     #-}

import           Control.Applicative
import           Control.Arrow       ((&&&))
import           Data.Foldable
import           Data.Function       (on)
import           Data.List           (sortBy)
import           Data.Maybe          (catMaybes)
import           Data.Monoid
import           Data.Tree           (Tree (..), drawTree)
import           Prelude             hiding (foldl, foldl1, maximum, minimum,
                                      notElem, sequence_, sum)
import           System.Environment  (getArgs)

import           Text.XML.Light

type Edge α = (α, α)
data Range α
  = α :-: α
  | Range0
  deriving Show

data RangeState α
  = (:|) { getError :: α, getRange :: Range α }
  deriving Show

analyzeTree :: (Num α, Ord α) => Tree α -> Tree (RangeState α)
analyzeTree tree =
  case treeOrPath tree of
    Left (Node i ts) -> Node (e :| extend cov i) children
      where children = analyzeTree <$> ts
            e :| cov = fold $ rootLabel <$> children
    Right path       -> Node (analyzePath path) []

analyzePath :: (Num α, Ord α) => [α] -> RangeState α
analyzePath path = foldl op mempty (reverse path)
  where op (e :| cov) i | inRange cov i = (e + 1) :| cov
                        | otherwise     = e :| extend cov i


treeOrPath :: Tree α -> Either (Tree α) [α]
treeOrPath (Node i [])  = Right [i]
treeOrPath (Node i [x]) = (i :) <$> treeOrPath x
treeOrPath t            = Left t

inRange :: Ord α => Range α -> α -> Bool
inRange (x :-: y) z = z > x && z < y
inRange Range0 _ = False

rangeFrom :: (Foldable φ, Ord α) => φ α -> Range α
rangeFrom xs = minimum xs :-: maximum xs

rangesIntersect :: Ord α => Range α -> Range α -> Bool
rangesIntersect (x :-: y) (u :-: v) = not $ (x < u && y < u) || (u < x && v < x)
rangesIntersect _         _         = False

extend :: Ord α => Range α -> α -> Range α
extend (x :-: y) z = rangeFrom [x, y, z]
extend Range0 z = z :-: z

instance Ord α => Monoid (Range α) where
  mempty = Range0

  mappend (x :-: y) (u :-: v) = rangeFrom [x,y,u,v]
  mappend Range0 uv = uv
  mappend xy Range0 = xy

instance (Num α, Ord α) => Monoid (RangeState α) where
  mempty = 0 :| mempty

  mappend (i :| xy) (j :| uv) = count :| (xy <> uv)
    where count | rangesIntersect xy uv = i + j + 1
                | otherwise             = i + j


draw' t = putStrLn $ drawTree $ show <$> t

sortWith :: Ord β => (α -> β) -> [α] -> [α]
sortWith f = sortBy (compare `on` f)

maximalPoint :: Eq α => [Edge α] -> Maybe α
maximalPoint es = find (\x -> x `notElem` (snd <$> es)) (fst <$> es)

makeTree :: Ord α => [Edge α] -> Maybe (Tree α)
makeTree es = makeTree' es <$> (maximalPoint es)

makeTree' :: Ord α => [Edge α] -> α -> Tree α
makeTree' edges maxLabel = Node maxLabel (sortWith rootLabel children)
    where children = makeTree' (filter (not . touches maxLabel) edges) <$> roots
          roots = opposite maxLabel <$> filter (touches maxLabel) edges

          touches :: Ord α => α -> Edge α -> Bool
          touches i (x, y) = x == i || y == i

          opposite :: Ord α => α -> Edge α -> α
          opposite i (x,y) | x == i     = y
                           | otherwise = x


(<$$>) :: (Functor φ, Functor γ) => (α -> β) -> φ (γ α) -> φ (γ β)
(<$$>) = fmap . fmap

main :: IO ()
main = do
  files <- getArgs
  forM_ files $ \name -> do
    src <- readFile name
    let contents = parseXML src
        sentences = onlyElems contents >>= findElements (simpleName "sentence")
        words = findChildren (simpleName "word") <$> sentences
        edges = catMaybes <$> (mkPair . (readHead &&& readId)) <$$> words

        trees :: [Tree Integer]
        trees = catMaybes $ makeTree <$> edges

        analyzed :: [Tree (RangeState Integer)]
        analyzed = analyzeTree <$> trees

        result = sum $ getError . rootLabel <$> analyzed

    putStrLn $ name ++ ": " ++ show result


simpleName :: String -> QName
simpleName s = QName s Nothing Nothing

readAttr :: Read a => String -> Element -> Maybe a
readAttr name = (<$>) read . findAttr (simpleName name)

readId, readHead :: Element -> Maybe Integer
readId = readAttr "id"
readHead = readAttr "head"


mkPair :: (Maybe a, Maybe a) -> Maybe (Edge a)
mkPair (Just h, Just i) = Just (h, i)
mkPair _                = Nothing
