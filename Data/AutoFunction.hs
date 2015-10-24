{-|
Module      : Data.AutoFunction
Description : Functions on open unions.
Copyright   : (c) Alexander Vieth, 2015
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)
-}

{-# LANGUAGE AutoDeriveTypeable #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}

module Data.AutoFunction (

      type (:+:)
    , MonoSumInject
    , monoSumInject

    , MapThroughArrows
    , mapThroughArrows

    , AutoFunction
    , autoFunction

    ) where

import Data.Proxy

-- | A sum, just like Either. It's called MonoSum because its kind is
--   * -> * -> * . Contrast it with, say, a functor sum, whose kind is
--   (* -> *) -> (* -> *) -> * -> * .
data MonoSum a b = MonoSumLeft a | MonoSumRight b

type (:+:) = MonoSum
infixr 6 :+:

-- | MonoSum terms are constructed from individual summands using this typeclass.
class MonoSumInject t sum where
    monoSumInject :: t -> sum

instance {-# OVERLAPS #-} MonoSumInject t t where
    monoSumInject = id

instance {-# OVERLAPS #-} MonoSumInject t rest => MonoSumInject t (s :+: rest) where
    monoSumInject = MonoSumRight . monoSumInject

instance {-# OVERLAPS #-} MonoSumInject t (t :+: rest) where
    monoSumInject = MonoSumLeft

-- Here we show how to consume a MonoSum, akin to applying a total
-- function composed of total functions on each summand.

-- | If we have a MonoSum
--
--   > p_1 :+: ... :+: p_n
--
--   then an
--
--   > FList '[p_1 ... p_n] t
--
--   holds enough information to create a total function
--
--   > (p_1 :+: ... :+: p_n) -> t
--
--   This is described by the class ConsumeMonoSum.
data FList (ps :: [*]) (t :: *) where
    FListZ :: FList '[] t
    FListS :: (p -> t) -> FList ps t -> FList (p ': ps) t

-- | Identifies a singleton type list.
type family IsSingleton (ps :: [*]) :: Bool where
    IsSingleton '[p] = 'True
    IsSingleton (p ': q ': ps) = 'False

-- | This typeclass produces functions from FLists.
class ConsumeMonoSum sum ps t where
    consumeMonoSum :: FList ps t -> sum -> t

instance {-# OVERLAPS #-} ConsumeMonoSum p '[p] t where
    consumeMonoSum l s = case (l, s) of
        (FListS f FListZ, x) -> f x

instance {-# OVERLAPS #-}
    ( ConsumeMonoSum rest ps t
    ) => ConsumeMonoSum (p :+: rest) (p ': ps) t
  where
    consumeMonoSum l s = case (l, s) of
        (FListS f _, MonoSumLeft x) -> f x
        (FListS _ fs, MonoSumRight x) -> consumeMonoSum fs x

-- | @MapThroughArrows f g s u@ states that a function @s -> u@ is enough to
--   produce a @g@ from an @f@. It's very abstract, but its instances are
--   simple: if @s@ is found on the right-hand-side of some arrow in @f@, then
--   we can replace that @s@ with @u@, which determines the type of @g@.
--
--   Check out its use in the @MakeFList@ recursive instance.
class MapThroughArrows (f :: *) (g :: *) (s :: *) (u :: *) where
    mapThroughArrows :: (s -> u) -> f -> g

instance {-# OVERLAPS #-} MapThroughArrows (s -> t) (s -> u) t u where
    mapThroughArrows = fmap

instance {-# OVERLAPS #-}
    ( MapThroughArrows q r t u
    ) => MapThroughArrows (s -> q) (s -> r) t u
  where
    mapThroughArrows f = fmap (mapThroughArrows f)

-- | Produce a function with as many arrows as there are elements of @ps@.
--   A @t@ follows the rightmost arrow, if any.
--
--     @
--       AsFunction [p_1, .., p_n] t =
--              (p_1 -> t)
--           -> (p_2 -> t)
--           -> ..
--           -> (p_n -> t)
--           -> t
--     @
--
type family AsFunction (ps :: [*]) (t :: *) (r :: *) :: * where
    AsFunction '[] t r = r
    AsFunction (p ': ps) t r = (p -> t) -> AsFunction ps t r

-- | Here we describe how to pull an FList out of thin air.
--   It's convenient to put he FList behind some applicative, so we do that.
--
--   > (p_1 -> t) -> .. -> (p_n -> t) -> a (FList [p_1 .. p_n] t)
--
class MakeFList (b :: Bool) (ps :: [*]) (t :: *) (a :: * -> *) where
    makeFList
        :: Proxy b
        -> Proxy ps
        -> Proxy t
        -> Proxy a
        -> AsFunction ps t (a (FList ps t))

instance {-# OVERLAPS #-} Applicative a => MakeFList 'True '[p] t a where
    makeFList _ _ _ _ = \f -> pure (FListS f FListZ)

instance {-# OVERLAPS #-}
    ( MakeFList (IsSingleton ps) ps t a
    , f ~ AsFunction ps t (a (FList ps t))
    , g ~ AsFunction ps t (a (FList (p ': ps) t))
    , MapThroughArrows f g (a (FList ps t)) (a (FList (p ': ps) t))
    , Functor a
    ) => MakeFList 'False (p ': ps) t a
  where
    makeFList _ _ proxyT proxyA = \f ->
        let 
            extendFList :: a (FList ps t) -> a (FList (p ': ps) t)
            extendFList = fmap (FListS f)
            proxyB :: Proxy (IsSingleton ps)
            proxyB = Proxy
            proxyPS :: Proxy ps
            proxyPS = Proxy
        in  mapThroughArrows (extendFList) (makeFList proxyB proxyPS proxyT proxyA)

-- | This class allows us to create the FList function without proxies.
class AutoFList f where
    autoFList :: f

-- | Should be such that
--   > AutoFListParameters (AsFunction ps t r) = ps
type family AutoFListParameters (f :: *) :: [*] where
    AutoFListParameters ((p -> t) -> r) = p ': AutoFListParameters r
    AutoFListParameters r = '[]

type family AutoFListCodomain (f :: *) :: * where
    AutoFListCodomain ((p -> t) -> r) = AutoFListCodomain r
    AutoFListCodomain (a (FList ps t)) = t

type family AutoFListCodomainFunctor (f :: *) :: (* -> *) where
    AutoFListCodomainFunctor ((p -> t) -> r) = AutoFListCodomainFunctor r
    AutoFListCodomainFunctor (a (FList ps t)) = a

instance
    ( MakeFList (IsSingleton (AutoFListParameters f)) (AutoFListParameters f) (AutoFListCodomain f) (AutoFListCodomainFunctor f)
    , f ~ AsFunction
              (AutoFListParameters f)
              (AutoFListCodomain f)
              (AutoFListCodomainFunctor f (FList (AutoFListParameters f) (AutoFListCodomain f)))
    ) => AutoFList f
  where
    autoFList = makeFList proxyB proxyPS proxyT proxyA
      where
        proxyB :: Proxy (IsSingleton (AutoFListParameters f))
        proxyB = Proxy
        proxyPS :: Proxy (AutoFListParameters f)
        proxyPS = Proxy
        proxyT :: Proxy (AutoFListCodomain f)
        proxyT = Proxy
        proxyA :: Proxy (AutoFListCodomainFunctor f)
        proxyA = Proxy

-- | AutoFunction uses AutoFList and ConsumeMonoSum to construct functions on
--   sums which don't feature the FList. Like MakeFList, they feature an
--   applicative.
--
--   > (s_1 -> t) -> ... -> (s_n -> t) -> a (s_1 :+: ... :+: s n) -> a t
--
class AutoFunction f where
    autoFunction :: f

type family AsSum (ps :: [*]) :: * where
    AsSum '[p] = p
    AsSum (p ': ps) = p :+: AsSum ps

type family AsList (sum :: *) :: [*] where
    AsList (p :+: ps) = p ': AsList ps
    AsList p = '[p]

-- | The function type which presumably has an AutoFList instance, which
--   would generate a function type with an AutoFunction instance. It replaces
--   the latter's (a sum -> a t) with the relevant FList representing this
--   function, inside the functor a.
type family GeneratingFunction (f :: *) :: * where
    GeneratingFunction ((s -> t) -> q) = (s -> t) -> GeneratingFunction q
    GeneratingFunction (a sum -> a t) = a (FList (AsList sum) t)

-- | Picks the type to the left of the rightmost arrow, inside the 
--   functor.
type family AutoFunctionSum (f :: *) :: * where
    AutoFunctionSum ((s -> t) -> q) = AutoFunctionSum q
    AutoFunctionSum (a s -> a t) = s

type family AutoFunctionCodomain (f :: *) :: * where
    AutoFunctionCodomain ((s -> t) -> q) = AutoFunctionCodomain q
    AutoFunctionCodomain (s -> a t) = t

type family AutoFunctionCodomainFunctor (f :: *) :: (* -> *) where
    AutoFunctionCodomainFunctor ((s -> t) -> q) = AutoFunctionCodomainFunctor q
    AutoFunctionCodomainFunctor (a s -> a t) = a

type family AutoFunctionParameters (f :: *) :: [*] where
    AutoFunctionParameters ((p -> t) -> r) = p ': AutoFunctionParameters r
    AutoFunctionParameters r = '[]

instance
    ( AutoFList (GeneratingFunction f)
    , MapThroughArrows
          (GeneratingFunction f)
          f
          (a (FList (AutoFunctionParameters f) (AutoFunctionCodomain f)))
          (a (AutoFunctionSum f) -> a (AutoFunctionCodomain f))
    , ConsumeMonoSum (AutoFunctionSum f) (AutoFunctionParameters f) (AutoFunctionCodomain f)
    , a ~ AutoFunctionCodomainFunctor f
    , Applicative a
    ) => AutoFunction f
  where
    autoFunction =
        let g = autoFList :: GeneratingFunction f
            consume = consumeMonoSum :: FList (AutoFunctionParameters f) (AutoFunctionCodomain f) -> (AutoFunctionSum f) -> (AutoFunctionCodomain f)
            mapConsume :: (AutoFunctionCodomainFunctor f) (FList (AutoFunctionParameters f) (AutoFunctionCodomain f))
                       -> (AutoFunctionCodomainFunctor f) (AutoFunctionSum f)
                       -> (AutoFunctionCodomainFunctor f) (AutoFunctionCodomain f)
            mapConsume = whatWeNeed consume
        in  mapThroughArrows mapConsume g
      where
        whatWeNeed :: forall f a b c . Applicative f => (a -> b -> c) -> f a -> f b -> f c
        whatWeNeed f x =
            let step1 = fmap f x :: f (b -> c)
            in  \fb -> step1 <*> fb
