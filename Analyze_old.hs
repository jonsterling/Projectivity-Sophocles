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

