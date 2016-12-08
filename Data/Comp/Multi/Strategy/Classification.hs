{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

-- | 
-- 
-- This module contains typeclasses and operations allowing dynamic casing on sorts.

module Data.Comp.Multi.Strategy.Classification
  (
    DynCase(..)
  , KDynCase(..)
  , dynProj
  , caseE
  , subterms
  , isSort
  ) where

import Data.Type.Equality ( (:~:)(..), gcastWith )
import Data.Proxy ( Proxy )

import Data.Comp.Multi ( Term, (:+:), E, K, runE, caseH, (:&:), remA, Cxt(..), subs )
import Data.Comp.Multi.HFoldable ( HFoldable )

--------------------------------------------------------------------------------


-- |
-- This operation allows you to rediscover the label giving
-- the sort of a term by inspecting the term. It is mainly used
-- through the 'caseE' and 'dynProj' operators
class DynCase f a where
  -- | Determine whether a node has sort @a@
  dyncase :: f b -> Maybe (b :~: a)

-- | An instance @KDynCase f a@ defines an instance @DynCase (Term f) a@
class KDynCase f a where
  kdyncase :: forall (e :: * -> *) b. DynCase e a => f e b -> Maybe (b :~: a)

instance {-# OVERLAPPABLE #-} KDynCase f a where
  kdyncase = const Nothing

instance {-# OVERLAPPING #-} (KDynCase f l, KDynCase g l) => KDynCase (f :+: g) l where
  kdyncase = caseH kdyncase kdyncase

instance {-# OVERLAPPING #-} (KDynCase f l) => KDynCase (f :&: a) l where
  kdyncase = kdyncase . remA

instance DynCase (K a) b where
  dyncase _ = Nothing

instance (KDynCase f l, DynCase a l) => DynCase (Cxt h f a) l where
  dyncase (Term x) = kdyncase x
  dyncase (Hole x) = dyncase x

--------------------------------------------------------------------------------

dynProj :: forall f l l'. (DynCase f l) => f l' -> Maybe (f l)
dynProj x = case (dyncase x :: Maybe (l' :~: l)) of
              Just p -> Just (gcastWith p x)
              Nothing -> Nothing

-- | Inspect an existentially-quantified sort
caseE :: (DynCase f a) => E f -> Maybe (f a)
caseE = runE dynProj

-- | Gives all subterms of any given sort of a term
subterms :: (DynCase (Term f) l, HFoldable f) => Term f l' -> [Term f l]
subterms x = [ y | Just y <- map caseE $ subs x]

isSort :: forall e l. (DynCase e l) => Proxy l -> forall i. e i -> Bool
isSort _ x = case (dyncase x :: Maybe (_ :~: l)) of
  Just _  -> True
  Nothing -> False