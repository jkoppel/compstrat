{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}


import Control.Monad ( MonadPlus(..) )
import Control.Monad.Identity ( Identity(..) )
import Control.Monad.State ( MonadState )
import Control.Monad.Trans.Maybe ( MaybeT )

import Data.Comp.Multi
import Data.Comp.Multi.Derive
import Data.Comp.Multi.HFoldable
import Data.Comp.Multi.HTraversable
import qualified Data.Comp.Ops as O ( (:&:)(..) )

import Data.Map ( Map )
import qualified Data.Map as Map
import Data.Maybe ( fromJust )

import Data.Comp.Multi.Strategic
import Data.Comp.Multi.Strategy.Classification
import Data.Comp.Multi.Strategy.Derive

import Tarski.Language.Java.Parametric.Full
import Tarski.SCM.Src
import Tarski.Sin.Compdata.Derive ( smartFConstructors )

-- data Label = Label !Int -- other fields omitted
--  deriving ( Eq, Ord, Read, Show )

getName' :: (Ident :<: f, ClassDecl :<: f) => GTranslateM Maybe (Term f) String
getName' (project -> (Just (ClassDecl _ (project -> (Just (Ident s))) _ _ _ _))) = return s
getName' _ = mzero

-- | Gets the name of the main class of a Java term
getName :: JavaTerm CompilationUnitL -> String
getName = fromJust . onetdT (getName' :: GTranslateM Maybe JavaTerm String)

extractLabels' :: (DistAnn f Label f') => Translate (Term f') i (Map Label (Term f' i))
extractLabels' s = return $ Map.singleton (getAnn s) s

-- | Creates a map from all statement labels to the corresponding statements
extractLabels :: (DistAnn f Label f', DynCase (Term f') i, HFoldable f') => Term f' :=> (Map Label (Term f' i))
extractLabels = runIdentity . (crushtdT $ promoteTF $ addFail extractLabels')

-- | Extract the annotation from the top of an annotated term
getAnn :: (DistAnn s p s') => Term s' :=> p
getAnn = annSnd . projectA . unTerm
  where
    annSnd (_ O.:&: x) = x


--------------------------------------------------------------------------------


-- | A sort denoting the top-level sort seen in a source file. To use in a CDT, create a constructor
--   that injects another sort into TopL. E.g.: CompilationUnitIsTop :: f e CompilationUnitL -> e TopL
--data TopL 
--
--data SourceFileL
--data SourceFile e l where
--  SourceFile :: Bool     -- whether the file is changed. 
--             -> FilePath -- File path of the corresponding source file
--             -> e TopL   -- Contents of the source file
--             -> SourceFile e SourceFileL

--derive [makeHFunctor, makeHTraversable, makeHFoldable, makeEqHF, makeShowHF, makeOrdHF, smartFConstructors, makeDynCase]
--       [''SourceFile]

trackingFiles' :: (Monad m, SourceFile :<: f, DistAnn f a f', HFunctor f', HFunctor f, RemA f' f) => GRewriteM m (Term f') -> RewriteM m (Term f') SourceFileL
trackingFiles' f s@(project' -> Just (SourceFile _ x e)) = do e' <- f e
                                                              return $ appCxt $ ann lab (iSourceFile True x (Hole e'))
  where
    lab = getAnn s

trackingFiles' _ _                                        = error "trackingFiles' failed"

-- | Lifts a rewrite to one that marks whether each source file has changed. This allows you to output only the files that changed.
-- 
-- Yes, this is in the /MaybeT (MaybeT m)/ monad
trackingFiles :: (Monad m, HTraversable f', DistAnn f a f', HFunctor f', HFunctor f, RemA f' f, SourceFile :<: f, DynCase (Term f') SourceFileL ) => GRewriteM (MaybeT (MaybeT m)) (Term f') -> GRewriteM (MaybeT m) (Term f')
trackingFiles f = prunetdR $ promoteRF $ tryR (trackingFiles' f)


--------------------------------------------------------------------------------


-- This example requires the actual Java CDT from the comptrans examples or some surrogate


targetLabel :: (MonadPlus m, DistAnn f Label f') => Label -> Rewrite (Term f') i -> RewriteM m (Term f') i
targetLabel l f t@(Term (projectA -> _ O.:&: l'))
                                 | l == l'   = return $ runIdentity (f t)
                                 | otherwise = mzero


type JavaProg = JavaProjLab [SourceFileL]

runJavaRewrite :: (DynCase JavaProjLab i) => RewriteM (MaybeT (MaybeT Identity)) JavaProjLab i -> JavaProg -> JavaProg
runJavaRewrite r = runIdentity . (tryR $ trackingFiles $ onebuR $ promoteRF r)

delete' :: (HTraversable f, DistAnn f Label f', Stmt :<: f, HFunctor f) => Rewrite (Term f') StmtL
delete' _ = return $ ann Nonlabel iEmpty

-- | Replaces the statement with the target label with the empty statement
delete :: (Monad m) => Label -> JavaProg -> m JavaProg
delete l = return . (runJavaRewrite $ targetLabel l delete')

main = return ()