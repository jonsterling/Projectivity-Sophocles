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
import Analyze

draw' t = putStrLn $ drawTree $ show <$> t

sortWith :: Ord β => (α -> β) -> [α] -> [α]
sortWith f = sortBy (compare `on` f)

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

analyzeFile :: String -> IO ()
analyzeFile name = do
    src <- readFile name
    let contents = parseXML src
        sentences = onlyElems contents >>= findElements (simpleName "sentence")
        words = findChildren (simpleName "word") <$> sentences
        edges = catMaybes <$> (mkPair . (readHead &&& readId)) <$$> words

        trees :: [Tree Integer]
        trees = catMaybes $ makeTree <$> edges

        analyzed :: [Tree (RangeState Integer)]
        analyzed = analyzeTree <$> trees
    forM_ trees $ \t -> do
      print $ allEdges' t
      print $ sum $ analyzeEdges (allEdges' t)

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

        --result = sum $  <$> analyzed

    forM_ trees draw'
    forM_ analyzed draw'
    --putStrLn $ name ++ ": " ++ show result


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
