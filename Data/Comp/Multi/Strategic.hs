{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}

module Data.Comp.Multi.Strategic
  (
    -- * Rewrites
    RewriteM
  , Rewrite
  , GRewriteM
  , GRewrite
  , addFail
  , tryR
  , promoteR
  , promoteRF
  , allR
  , (>+>)
  , (+>)
  , anyR
  , oneR
  , alltdR
  , allbuR
  , anytdR
  , anybuR
  , prunetdR
  , onetdR
  , onebuR

    -- * Translations
  , Translate
  , TranslateM
  , GTranslateM
  , promoteTF
  , mtryM
  , onetdT
  , foldtdT
  , crushtdT
  ) where

import Control.Applicative ( Applicative, (<*), liftA )

import Control.Monad ( MonadPlus(..), liftM, liftM2, (>=>) )
import Control.Monad.Identity ( Identity )
import Control.Monad.Trans ( lift )
import Control.Monad.Trans.Maybe ( MaybeT, runMaybeT )
import Control.Monad.State ( StateT, runStateT, get, put )
import Control.Monad.Writer ( WriterT, runWriterT, tell )

import Control.Parallel.Strategies ( rparWith )

import Data.Comp.Multi ( Cxt(..), Term, unTerm )
import Data.Comp.Multi.Generic ( query )
import Data.Comp.Multi.HFoldable ( HFoldable )
import Data.Comp.Multi.HTraversable ( HTraversable(..) )
import Data.Monoid ( Monoid, mappend, mempty, Any(..) )
import Data.Type.Equality ( (:~:)(..), sym )

import Data.Comp.Multi.Strategy.Classification

--------------------------------------------------------------------------------

-- Porting from the old type-equality library to the new base Data.Type.Equality
-- Haven't yet looked into rewriting with gcastWith instead

subst :: (a :~: b) -> f a -> f b
subst Refl x = x

subst2 :: (a :~: b) -> f (g a) -> f (g b)
subst2 Refl x = x

--------------------------------------------------------------------------------

evalPar :: (HTraversable f) => f l -> f l
evalPar = withStrategy (htraverse id)

--------------------------------------------------------------------------------

type RewriteM m f l = f l -> m (f l)
type Rewrite f l = RewriteM Identity f l
type GRewriteM m f = forall l. RewriteM m f l
type GRewrite f = GRewriteM Identity f

--------------------------------------------------------------------------------
-- Rewrites
--------------------------------------------------------------------------------

type AnyR m = WriterT Any m

wrapAnyR :: (MonadPlus m) => RewriteM m f l -> RewriteM (AnyR m) f l
wrapAnyR f t = (lift (f t) <* tell (Any True)) `mplus` return t

unwrapAnyR :: MonadPlus m => RewriteM (AnyR m) f l -> RewriteM m f l
unwrapAnyR f t = do (t', Any b) <- runWriterT (f t)
                    if b then
                      return t'
                     else
                      mzero

--------------------------------------------------------------------------------

type OneR m = StateT Bool m

wrapOneR :: (Applicative m, MonadPlus m) => RewriteM m f l -> RewriteM (OneR m) f l
wrapOneR f t = do b <- get
                  if b then
                    return t
                   else
                    (lift (f t) <* put True) `mplus` return t

unwrapOneR :: MonadPlus m => RewriteM (OneR m) f l -> RewriteM m f l
unwrapOneR f t = do (t', b) <- runStateT (f t) False
                    if b then
                      return t'
                     else
                      mzero

--------------------------------------------------------------------------------

dynamicR :: (DynCase f l, MonadPlus m) => RewriteM m f l -> GRewriteM m f
dynamicR f t = case dyncase t of
                 Just p -> subst2 (sym p) $ f (subst p t)
                 Nothing -> mzero

tryR :: (Monad m) => RewriteM (MaybeT m) f l -> RewriteM m f l
tryR f t = liftM (maybe t id) $ runMaybeT (f t)

promoteR :: (DynCase f l, Monad m) => RewriteM (MaybeT m) f l -> GRewriteM m f
promoteR = tryR . dynamicR

promoteRF :: (DynCase f l, Monad m) => RewriteM (MaybeT m) f l -> GRewriteM (MaybeT m) f
promoteRF = dynamicR

-- | Applies a rewrite to all immediate subterms of the current term
allR :: (Applicative m, HTraversable f) => GRewriteM m (Term f) -> RewriteM m (Term f) l
allR f t = liftA Term $ evalPar $ htraverse f $ unTerm t

-- | Applies two rewrites in suceesion, succeeding if one or both succeed
(>+>) :: (MonadPlus m) => GRewriteM m f -> GRewriteM m f -> GRewriteM m f
f >+> g = unwrapAnyR (wrapAnyR f >=> wrapAnyR g)

-- | Left-biased choice -- (f +> g) runs f, and, if it fails, then runs g
(+>) :: (MonadPlus m) => RewriteM m f l -> RewriteM m f l -> RewriteM m f l
(+>) f g x = f x `mplus` g x

-- | Applies a rewrite to all immediate subterms of the current term, succeeding if any succeed
anyR :: (MonadPlus m, HTraversable f) => GRewriteM m (Term f) -> RewriteM m (Term f) l
anyR f = unwrapAnyR $ allR $ wrapAnyR f -- not point-free because of type inference

-- | Applies a rewrite to the first immediate subterm of the current term where it can succeed
oneR :: (MonadPlus m, HTraversable f) => GRewriteM m (Term f) -> RewriteM m (Term f) l
oneR f = unwrapOneR $ allR $ wrapOneR f -- not point-free because of type inference

-- | Runs a rewrite in a bottom-up traversal
allbuR :: (Applicative m, HTraversable f) => GRewriteM m (Term f) -> GRewriteM m (Term f)
allbuR f = allR (allbuR f) >=> f

-- | Runs a rewrite in a top-down traversal
alltdR :: (Applicative m, HTraversable f) => GRewriteM m (Term f) -> GRewriteM m (Term f)
alltdR f = f >=> allR (alltdR f)

-- | Runs a rewrite in a bottom-up traversal, succeeding if any succeed
anybuR :: (MonadPlus m, HTraversable f) => GRewriteM m (Term f) -> GRewriteM m (Term f)
anybuR f = anyR (anybuR f) >+> f

-- | Runs a rewrite in a top-down traversal, succeeding if any succeed
anytdR :: (MonadPlus m, HTraversable f) => GRewriteM m (Term f) -> GRewriteM m (Term f)
anytdR f = f >+> anyR (anytdR f)

-- | Runs a rewrite in a top-down traversal, succeeding if any succeed, and pruning below successes
prunetdR :: (MonadPlus m, HTraversable f) => GRewriteM m (Term f) -> GRewriteM m (Term f)
prunetdR f = f +> anyR (prunetdR f)

-- | Applies a rewrite to the first node where it can succeed in a bottom-up traversal
onebuR :: (MonadPlus m, HTraversable f) => GRewriteM m (Term f) -> GRewriteM m (Term f)
onebuR f = oneR (onebuR f) +> f

-- | Applies a rewrite to the first node where it can succeed in a top-down traversal
onetdR :: (MonadPlus m, HTraversable f) => GRewriteM m (Term f) -> GRewriteM m (Term f)
onetdR f = f +> oneR (onetdR f)

--------------------------------------------------------------------------------
-- Translations
--------------------------------------------------------------------------------

-- | A single-sorted translation in the Identity monad
type Translate f l t = TranslateM Identity f l t

-- | A monadic translation for a single sort
type TranslateM m f l t = f l -> m t

-- | A monadic translation for all sorts
type GTranslateM m f t = forall l. TranslateM m f l t

-- | Allows a one-sorted translation to be applied to any sort, failing at sorts
--   different form the original
promoteTF :: (DynCase f l, MonadPlus m) => TranslateM m f l t -> GTranslateM m f t
promoteTF f t = case dyncase t of
                  Just p -> f (subst p t)
                  Nothing -> mzero

-- | Lifts a translation into the Maybe monad, allowing it to fail
addFail :: Monad m => TranslateM m f l t -> TranslateM (MaybeT m) f l t
addFail = (lift . )

-- | Runs a failable computation, replacing failure with mempty
mtryM :: (Monad m, Monoid a) => MaybeT m a -> m a
mtryM = liftM (maybe mempty id) . runMaybeT

-- | Runs a translation in a top-down manner, combining its
--   When run using MaybeT, returns its result for the last node where it succeded
onetdT :: (MonadPlus m, HFoldable f) => GTranslateM m (Term f) t -> GTranslateM m (Term f) t
onetdT t = query t mplus

-- | Fold a tree in a top-down manner
foldtdT :: (HFoldable f, Monoid t, Monad m) => GTranslateM m (Term f) t -> GTranslateM m (Term f) t
foldtdT t = query t (liftM2 mappend)

-- | An always successful top-down fold, replacing failures with mempty.
crushtdT :: (HFoldable f, Monoid t, Monad m) => GTranslateM (MaybeT m) (Term f) t -> GTranslateM m (Term f) t
crushtdT f = foldtdT $ mtryM . f