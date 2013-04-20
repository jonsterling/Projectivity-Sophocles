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


(<$$>) :: (Functor φ, Functor γ) => (α -> β) -> φ (γ α) -> φ (γ β)
(<$$>) = fmap . fmap

analyzeFile :: String -> IO ()
analyzeFile name = do
    src <- readFile name
    let contents = parseXML src
        sentences = onlyElems contents >>= findElements (simpleName "sentence")
        words = findChildren (simpleName "word") <$> sentences
        edges = catMaybes <$> (mkEdge . (readHead &&& readId)) <$$> words

        trees :: [Tree Integer]
        trees = catMaybes $ treeFromEdges <$> edges

    forM_ trees $ \t -> do
      print $ omega t

main :: IO ()
main = do
  files <- getArgs
  forM_ files $ \name -> do
    src <- readFile name
    let contents = parseXML src
        sentences = onlyElems contents >>= findElements (simpleName "sentence")
        words = findChildren (simpleName "word") <$> sentences
        edges = catMaybes <$> (mkEdge . (readHead &&& readId)) <$$> words

        trees :: [Tree Integer]
        trees = catMaybes $ treeFromEdges <$> edges

        --result = sum $  <$> analyzed

    forM_ trees draw'
    --putStrLn $ name ++ ": " ++ show result


simpleName :: String -> QName
simpleName s = QName s Nothing Nothing

readAttr :: Read a => String -> Element -> Maybe a
readAttr name = (<$>) read . findAttr (simpleName name)

readId, readHead :: Element -> Maybe Integer
readId = readAttr "id"
readHead = readAttr "head"


mkEdge :: (Maybe a, Maybe a) -> Maybe (Edge a)
mkEdge (Just h, Just i) = Just (h :-: i)
mkEdge _                = Nothing

