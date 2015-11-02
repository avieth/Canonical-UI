{-|
Module      : UI.Canonical
Description : Description of user interfaces as types.
Copyright   : (c) Alexander Vieth, 2015
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)
-}

{-# LANGUAGE AutoDeriveTypeable #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor #-}

module UI.Canonical (

      N(..)
    , T(..)
    , R
    , Close

    , type (->:)
    , type (-->:)
    , type (--->:)
    , type (---->:)
    , type (:>-)
    , type (:>--)
    , type (:>---)
    , type (:>----)

    , UI
    , makeUI

    , AutoUI
    , autoUI

    , InterpretedUI
    , runInterpretedUI


    , UITransitionFunctionT

    ) where

import GHC.TypeLits
import Control.Monad (join, when)
import Data.Profunctor (dimap)
import Data.Proxy
import Data.Void
import Data.AutoFunction

-- | A node. Second component should be a @T@.
--
--     > N '(node, T '[ '(edge1, ui1), '(edge2, ui2) ])
--
data N (k :: (*, *))

-- | A list of edges. Second component of each should be an @N@, @R@, or @Close@.
data T (k :: [(*, *)])

-- | A hole for recursion. It indicates a loop back to the start of a UI.
data R

-- | Close recursion. It indicates that any @R@s found in @t@ should loop back
--   to @t@.
data Close t 

-- | An @m t@ with a phantom type @q@. That @q@ will be some ui (an @N@)
--   indicates that the @m t@ is an interpreteation of that ui.
data InterpretedUI q m t = InterpretedUI {
      runInterpretedUI :: m t
    }

reinterpretUI :: InterpretedUI q m t -> InterpretedUI r m t
reinterpretUI = InterpretedUI . runInterpretedUI

type family UITransitionSumT (es :: *) :: * where
    UITransitionSumT (T '[]) = Void
    UITransitionSumT (T '[ '(e, q) ]) = e
    UITransitionSumT (T ( '(e, q) ': es )) = e :+: UITransitionSumT (T es)

-- | This gives the function which you'll get from makeUI. It includes all of
--   the dependecies of the UI as functions from the relevant edge summand to
--   its relevant InterpretedUI.
type family UITransitionFunctionT (t :: *) (m :: * -> *) (r :: *) :: * where
    UITransitionFunctionT (N '(node, edges)) m r = UITransitionFunctionT_ (N '(node, edges)) edges m r

type family UITransitionFunctionT_ (t :: *) (t' :: *) (m :: * -> *) (r :: *) :: * where

    UITransitionFunctionT_ (N '(node, edges)) (T '[]) m r =
           (node -> m (UITransitionSumT edges))
        -> (node -> InterpretedUI (N '(node, edges)) m r)

    UITransitionFunctionT_ (N '(node, edges)) (T ( '(e, q) ': rest )) m r =
           (e -> InterpretedUI (UITransitionTypeParameter (N '(node, edges)) q) m r)
        -> UITransitionFunctionT_ (N '(node, edges)) (T rest) m r

-- The family UITransitionFunctionT is injective. Here we give the inverse for t.
-- 
-- I suspect this is wrong in the presence of R. 
--
--    UITransitionFunctionT (N '(node, T '[ '(edge, R) ])) m r =
--           (edge -> InterpretedUI (UITransitionFunctionT (N '(node, T '[ '(edge, R) ]))) m r)
--        -> (node -> m edge)
--        -> (node -> InterpretedUI (N '(node, T '[ '(edge, R) ])) m r)
--
--    UITransitionFunctionTInverseT
--           (edge -> InterpretedUI (UITransitionFunctionT (N '(node, T '[ '(edge, R) ]))) m r)
--        -> (node -> m edge)
--        -> (node -> InterpretedUI (N '(node, T '[ '(edge, R) ])) m r)
--
--      = N '(node, T '[ '(edge, R) ])
--
--
--     UITransitionFunctionT (UITransitionFunctionTInverseT (UITransitionFunctionT t m r))
--   ~ UITransitionFunctionT t m r
--
type family UITransitionFunctionTInverseT (f :: *) :: * where
    UITransitionFunctionTInverseT ((node -> m sum) -> (node -> InterpretedUI (N '(node, edges)) m r)) =
        N '(node, edges)
    UITransitionFunctionTInverseT ((e -> r) -> rest) = UITransitionFunctionTInverseT rest

-- The inverse for m.
type family UITransitionFunctionTInverseM (f :: *) :: * -> * where
    UITransitionFunctionTInverseM ((node -> m sum) -> (node -> InterpretedUI (N '(node, edges)) m r)) = m
    UITransitionFunctionTInverseM ((e -> r) -> rest) = UITransitionFunctionTInverseM rest

-- The inverse for r.
type family UITransitionFunctionTInverseR (f :: *) :: * where
    UITransitionFunctionTInverseR ((node -> m sum) -> (node -> InterpretedUI (N '(node, edges)) m r)) = r
    UITransitionFunctionTInverseR ((e -> r) -> rest) = UITransitionFunctionTInverseR rest

-- | Like UITransitionFunctionT, except that the first parameter of each
--   InterpretedUI type appearing to the right of a function arrow in the
--   function parameters is set to t.
--   There will be an instance
--
--       Reparameterize (UITransitionFunctionMonoT t m r) (UITransitionFunctionT t m r)
--
type family UITransitionFunctionMonoT (t :: *) (m :: * -> *) (r :: *) :: * where
    UITransitionFunctionMonoT (N '(node, edges)) m r = UITransitionFunctionMonoT_ (N '(node, edges)) edges m r

type family UITransitionFunctionMonoT_ (t :: *) (t' :: *) (m :: * -> *) (r :: *) :: * where

    UITransitionFunctionMonoT_ (N '(node, edges)) (T '[]) m r =
           (node -> m (UITransitionSumT edges))
        -> (node -> InterpretedUI (N '(node, edges)) m r)

    UITransitionFunctionMonoT_ (N '(node, edges)) (T ( '(e, q) ': rest )) m r =
           (e -> InterpretedUI (N '(node, edges)) m r)
        -> UITransitionFunctionMonoT_ (N '(node, edges)) (T rest) m r

-- | Like UITransitionFunctionMonoT, except that it uses the Q wrapper on
--   the rightmost part. This is to ensure an AutoFunction instance!
type family UITransitionFunctionMonoQT (t :: *) (m :: * -> *) (r :: *) :: * where
    UITransitionFunctionMonoQT (N '(node, edges)) m r = UITransitionFunctionMonoQT_ (N '(node, edges)) edges m r

type family UITransitionFunctionMonoQT_ (t :: *) (t' :: *) (m :: * -> *) (r :: *) :: * where

    UITransitionFunctionMonoQT_ (N '(node, edges)) (T '[]) m r =
           (Q node m (UITransitionSumT edges))
        -> (Q node m (InterpretedUI (N '(node, edges)) m r))

    UITransitionFunctionMonoQT_ (N '(node, edges)) (T ( '(e, q) ': rest )) m r =
           (e -> InterpretedUI (N '(node, edges)) m r)
        -> UITransitionFunctionMonoQT_ (N '(node, edges)) (T rest) m r

-- | Replace @R@s with the original UI @t@.
--   For other UIs (constructed with @N@) we defer to
--   UITransitionTypeParameterRec which processes each edge. That in turn uses
--   UITransitionTypeParameterGuarded, which replaces @R@s with @Close t@.
--   This is very important. See the note on UITransitionTypeParameterGuarded.
--
--   We also strip off the @Close@ constructor. But is this the right thing
--   to do? TBD
type family UITransitionTypeParameter (t :: *) (q :: *) :: * where
    UITransitionTypeParameter t R = t
    UITransitionTypeParameter t (Close r) = r
    UITransitionTypeParameter t (N '(node, T edges)) = N '(node, T (UITransitionTypeParameterRec t edges))

type family UITransitionTypeParameterRec (t :: *) (es :: [(*, *)]) :: [(*, *)] where
    UITransitionTypeParameterRec t '[] = '[]
    UITransitionTypeParameterRec t ( '(node, e) ': rest ) =
           '(node, UITransitionTypeParameterGuarded t e)
        ': (UITransitionTypeParameterRec t rest)

-- | This is how we achieve recursion: the R type becomes Close over the
--   original t.
--   The Close constructor stops recursion; we do not R-replacement under a
--   Close.
--   Why do we close it??
--   To indicate that the Rs should *not* be expanded again.
--   Imagine we have a very simple UI
--
--   > N '(node1, T '[ '(edge1, R) ])
--
--   Its transition function without closing:
--
--   > :: (edge1 -> InterpretedUI (N '(node1, T '[ '(edge1, R) ] )) m r)
--   > -> (node1 -> m edge1)
--   > -> (node1 -> InterpretedUI (N '(node1, T '[ '(edge1, R) ] )) m r)
--
--   Its transition function with closing:
--
--   > :: (edge1 -> InterpretedUI (Close (N '(node1, T '[ '(edge1, R) ] ))) m r)
--   > -> (node1 -> m edge1)
--   > -> (node1 -> InterpretedUI (N '(node1, T '[ '(edge1, R) ] )) m r)
--
--   What's the difference? Nothing substantial, this is fine.
--   But! Throw one more edge in there:
--
--   > N '(node1, T '[ '(edge1, N '(node2, T '[ '(edge2, R) ])) ])
--
--   Now we'll require
--
--   > :: (edge1 -> InterpretedUI (N '(node2, T '[ '(edge2, N '(node1, T '[ '(edge1, N '(node2, T '[ '(edge2, R) ])) ])) ])) m r)
--   > -> (node1 -> m edge1)
--   > -> (node1 -> InterpretedUI (N '(node1, T '[ '(edge1, N '(node2, T '[ '(edge2, R) ])) ])) m r)
--
--   See the problem? It's there in the type
--   
--   > InterpretedUI (N '(node2, T '[ '(edge2, N '(node1, T '[ '(edge1, N '(node2, T '[ '(edge2, R) ])) ])) ])) m r
--
--   in which the R is hijacked! It now points back to N '(node2...) but
--   this is never what we wanted. We should have closed it:
--
--   > :: (edge1 -> InterpretedUI (N '(node2, T '[ '(edge2, Close (N '(node1, T '[ '(edge1, N '(node2, T '[ '(edge2, R) ])) ]) )) ])) m r)
--   > -> (node1 -> m edge1)
--   > -> (node1 -> InterpretedUI (N '(node1, T '[ '(edge1, N '(node2, T '[ '(edge2, R) ])) ])) m r)
--
--   The R is safely tucked away behind the Close, always pointing back to
--   the intended place.
type family UITransitionTypeParameterGuarded (t :: *) (q :: *) :: * where
    UITransitionTypeParameterGuarded t R = Close t
    -- When we encounter an R we add a Close, but when we enounter a Close
    -- we strip it; we do not want the user to have to create an InterpretedUI
    -- for a Close <something>.
    UITransitionTypeParameterGuarded t (Close (N '(node, T edges))) = (N '(node, T edges))
    UITransitionTypeParameterGuarded t (N '(node, T edges)) = N '(node, T (UITransitionTypeParameterRec t edges))

-- | With this class we can alter the codomain of every function parameter in
--   the UITransitionFunctionT. It's useful because those transitions functions
--   all have disparate target types: the InterpretedUI is tagged with a
--   phantom type indicating the UI from which it comes. This is for added
--   type safety. If you have, for instance, this UI:
--
--     type MyUI = N '( SomeNode, T '[ '(SomeEvent, OtherUI) ] )
--
--   then you cannot run it unless you really do use an OtherUI interpreter
--   for the sole transition, rather than just any old monad of the given
--   type parameter. Since the only way to obtain an InterpretedUI OtherUI m
--   is via makeUI, we know that you really have run that UI!
class Reparameterize f g where
    reparameterize :: f -> g

instance {-# OVERLAPS #-} Reparameterize q q where
    reparameterize = id

instance {-# OVERLAPS #-} Reparameterize (a -> InterpretedUI s m r) (a -> InterpretedUI t m r) where
    reparameterize = fmap reinterpretUI

instance {-# OVERLAPS #-} Reparameterize (a -> InterpretedUI s m r) (a -> InterpretedUI s m r) where
    reparameterize = id

instance {-# OVERLAPS #-}
    ( Reparameterize rest1 rest2
    ) => Reparameterize ((a -> InterpretedUI s m r) -> rest1) ((a -> InterpretedUI t m r) -> rest2)
  where
    reparameterize (f :: (a -> InterpretedUI s m r) -> rest1) = \(g :: a -> InterpretedUI t m r) ->
        let x = fmap reinterpretUI g :: a -> InterpretedUI s m r
            y = f x :: rest1
            z = reparameterize y :: rest2
        in  z

instance {-# OVERLAPS #-} 
    (
    ) => Reparameterize ((a -> InterpretedUI s m r) -> rest1) ((a -> InterpretedUI s m r) -> rest1)
  where
    reparameterize = id

-- Ok, so here we have the UITransitionFunctionT, where each parameter has
-- the special type parameter on the target InterpretedUI. We also have the
-- reinterpreted version of that, where all of the target parameters have been
-- fixed to the common one from the instance head.
-- We can produce the latter from the former. good. But what remains? We need
-- to show GHC how to take that reinterpreted function and use it to obtain
-- an InterpretedUI!
-- No not quite! Remember that UITransitionFunctionT is ultimately what we
-- want! We must be able to compute this from the reinterpreted ones! We
-- ought to be able to come up with a function
--
--     :: (s_1 -> InterpretedUI t m r)
--     -> ...
--     -> (s_n -> InterpretedUI t m r)
--     -> (t -> m (s_1 :+: ... :+: s_n))
--     -> t -> InterpretedUI t m r
--
-- Step 1: be able to generate values of that type from the type alone.
-- Step 2: be able to relax values of that type to ones where the @t@ is free
--   for each of the function parameters.
--
-- Step 2, I believe, is finished via ParameterizedFmap
-- Step 1 will be more difficult, although I believe I have solved this very
--   problem yesterday.
--   Yeah, isnt' step 1 just the auto function!?!?!?!?!
--   It's the same idea, except that the autofunction terminates in
--     sum -> t
--   rather than, as here
--     (t -> m sum) -> t -> InterpretedUI t m r
--   I think autofunction is in need of a generalization.
--   What we have here is merely a functor over the typical result type.
--     (t -> m sum) -> (t -> r)
--   rather than
--     sum -> r
--
--   Currently autofunction can do
--
--     :: (s_1 -> InterpretedUI t m r)
--     -> ...
--     -> (s_n -> InterpretedUI t m r)
--     -> (s_1 :+: ... :+: s_n)
--     -> InterpretedUI t m r
--
--   but suppose we generalized it to work through a functor. Then we could
--   do
--
--     :: (s_1 -> InterpretedUI t m r)
--     -> ...
--     -> (s_n -> InterpretedUI t m r)
--     -> f (s_1 :+: ... :+: s_n)
--     -> f (InterpretedUI t m r)
--
--   But the (t -> m (s_1 :+: ... :+: s_n)) disparity is a problem. Or is it?
--   If we set f q = t -> m q then the output is
--
--       t -> m (InterpretedUI t m r)
--
--   which is easily coerced to t -> InterpretedUI t m r, since
--   InterpretedUI t m ~ m
--
-- Ok, so with AutoFunction generalized, what's the next move?
--
-- Define

newtype Q t m r = Q {
      runQ :: t -> m r
    }

deriving instance Functor m => Functor (Q t m)

instance Applicative m => Applicative (Q t m) where
    pure = Q . pure . pure
    mf <*> mx = Q ((<*>) <$> runQ mf <*> runQ mx)

instance Monad m => Monad (Q t m) where
    return = pure
    mx >>= k = Q $ \t -> do
        x <- runQ mx t
        runQ (k x) t

mergeInterpreted :: Monad m => m (InterpretedUI t m r) -> InterpretedUI t m r
mergeInterpreted = InterpretedUI . join . fmap runInterpretedUI

-- Use autoFunction to get
--
--     :: (s_1 -> InterpretedUI t m r)
--     -> ...
--     -> (s_n -> InterpretedUI t m r)
--     -> Q t m (s_1 :+: ... :+: s_n)
--     -> Q t m (InterpretedUI t m r)
--
-- And define

inQ :: (t -> m s) -> Q t m s
inQ = Q

outQ :: Monad m => Q t m (m s) -> t -> m s
outQ q t = join (runQ q t)

-- To run a  @UI m t@  we must give, for each event @e@, a function
--     e -> InterpretedUI m t
-- as well as an initial  @InterpretedUI m es@  where @es@ is the union of
-- all event types. This must be the only way to recover an @InterpretedUI m t@.
--
-- t is the UI-describing type.
-- m is the monad in which we'll work.
-- r is the return value. A complete UI has r ~ Void, meaning it does not
--   end until the program ends.
class UI (t :: *) (m :: * -> *) (r :: *) where
    makeUI
        :: Proxy t
        -> Proxy m
        -> Proxy r
        -> UITransitionFunctionT t m r

instance {-# OVERLAPS #-}
    ( 
    ) => UI (N '(node, (T '[]))) m Void
  where
    makeUI _ _ _ = \(mk :: node -> m Void) (x :: node) -> InterpretedUI (mk x)

instance {-# OVERLAPS #-}
    ( AutoFunction (UITransitionFunctionMonoQT (N '(node, T edges)) m r)

    , MapThroughArrows (UITransitionFunctionMonoQT (N '(node, T edges)) m r)
                  (UITransitionFunctionMonoT (N '(node, T edges)) m r)
                  ((Q node m (UITransitionSumT (T edges))) -> (Q node m (InterpretedUI (N '(node, T edges)) m r)))
                  ((node -> m (UITransitionSumT (T edges))) -> (node -> InterpretedUI (N '(node, T edges)) m r))

    , Reparameterize (UITransitionFunctionMonoT (N '(node, T edges)) m r)
                     (UITransitionFunctionT (N '(node, T edges)) m r)
    , Monad m
    ) => UI (N '(node, T edges)) m r
  where
    makeUI _ _ _ =
        let
            -- UITransitionFunctionAutoT is designed so that its images have
            -- AutoFunction instances.
            f = autoFunction :: UITransitionFunctionMonoQT (N '(node, T edges)) m r
            -- Before we can reparameterize, we must make the part after the
            -- parameters uniform. That is: erase the Q t m prefix.
            dimapLeft :: (node -> m (UITransitionSumT (T edges))) -> Q node m (UITransitionSumT (T edges))
            dimapLeft = inQ
            dimapRight :: Q node m (InterpretedUI (N '(node, T edges)) m r) -> (node -> InterpretedUI (N '(node, T edges)) m r)
            dimapRight = fmap InterpretedUI . outQ . fmap runInterpretedUI
            g :: ((Q node m (UITransitionSumT (T edges))) -> (Q node m (InterpretedUI (N '(node, T edges)) m r)))
              -> ((node -> m (UITransitionSumT (T edges))) -> (node -> InterpretedUI (N '(node, T edges)) m r))
            g = dimap dimapLeft dimapRight
            -- With g in hand we can recover something which is reparameterizable
            -- to our goal!
            f' = mapThroughArrows g f :: UITransitionFunctionMonoT (N '(node, T edges)) m r
            f'' = reparameterize f' :: UITransitionFunctionT (N '(node, T edges)) m r
        in  f''

{-
 - You should never have to makeUI for a (Close ui)
instance
    ( UI ui m r
    , MapThroughArrows (UITransitionFunctionT ui m r)
                       (UITransitionFunctionT (Close ui) m r)
                       (InterpretedUI ui m r)
                       (InterpretedUI (Close ui) m r)
    ) => UI (Close ui) m r
  where
    makeUI _ proxyM proxyR =
        let ui = makeUI (Proxy :: Proxy ui) proxyM proxyR
            reinterpret :: InterpretedUI ui m r -> InterpretedUI (Close ui) m r
            reinterpret = reinterpretUI
        in  mapThroughArrows reinterpret ui
-}

class AutoUI (f :: *) where
    autoUI :: f

instance
    ( UI (UITransitionFunctionTInverseT f) (UITransitionFunctionTInverseM f) (UITransitionFunctionTInverseR f)
    , f ~ UITransitionFunctionT (UITransitionFunctionTInverseT f) (UITransitionFunctionTInverseM f) (UITransitionFunctionTInverseR f)
    ) => AutoUI f
  where
    autoUI = makeUI proxyT proxyM proxyR
      where
        proxyT :: Proxy (UITransitionFunctionTInverseT f)
        proxyT = Proxy
        proxyM :: Proxy (UITransitionFunctionTInverseM f)
        proxyM = Proxy
        proxyR :: Proxy (UITransitionFunctionTInverseR f)
        proxyR = Proxy

-- | x can be anything, but y should be an N.
type x ->: y = '(x, y)
infixr 3 ->:

type x -->: y = '(x, y)
infixr 5 -->:

type x --->: y = '(x, y)
infixr 7 --->:

type x ---->: y = '(x, y)
infixr 9 ---->:

type family Transition (x :: *) (y :: (*, *)) :: * where
    Transition (N '(node, T edges)) edge = N '(node, T (Snoc edge edges))
    Transition node edge = N '(node, T '[edge])

type family Snoc (t :: k) (ts :: [k]) :: [k] where
    Snoc t '[] = '[t]
    Snoc t (r ': ts) = r ': Snoc t ts

type x :>- y = Transition x y
infixl 2 :>-

type x :>-- y = Transition x y
infixl 4 :>--

type x :>--- y = Transition x y
infixl 6 :>---

type x :>---- y = Transition x y
infixl 8 :>----

-- Want to say that if you have a UX which can produce a d, then you can
-- give a Maybe d and always get a d.
--
-- No... this just seems weird. We want to say that the output UI r has
-- t as an input type. But how can we write that?!?!
type UIMaybe t r = Maybe t :>- t  ->: r
                           :>- () ->: r

runUIMaybe
    :: (t -> InterpretedUX s m r)
    -> 
    -> InterpretedUI (UIMaybe t s) m r
runUIMaybe runS runNothing = autoUI (runS)
                                    (\() -> runNothing)

{-

-- UXTransitionFunctionT expands @R@s by rewriting them as the original UI.
-- What follows is a description of how to contract those @R@s. So if you're
-- given a UITransitionFunctionT, you can run it through
-- UIContractRecursiveParts to pull those expansions back. It's commented out
-- because we don't actually need it (at one point I thought we did).

type family NatHalf (n :: Nat) :: Nat where
    NatHalf 2 = 1
    NatHalf n = 1 + NatHalf (n - 2) 

type family Append (xs :: [k]) (ys :: [k]) :: [k] where
    Append '[] ys = ys
    Append (x ': xs) ys = x ': Append xs ys

type family PrefixLists (p :: k) (xss :: [[k]]) where
    PrefixLists x '[] = '[]
    PrefixLists x (xs ': xss) = (x ': xs) ': (PrefixLists x xss)

type family Tail (xs :: [k]) :: [k] where
    Tail '[] = '[]
    Tail (x ': xs) = xs

type family Tails (xss :: [[k]]) :: [[k]] where
    Tails '[] = '[]
    Tails (xs ': xss) = Tail xs ': Tails xss

-- | Remove all empty lists from a list of lists.
type family RemoveEmptyLists (xs :: [[*]]) :: [[*]] where
    RemoveEmptyLists '[] = '[]
    RemoveEmptyLists ( '[] ': xs ) = RemoveEmptyLists xs
    RemoveEmptyLists ( x ': xs ) = x ': RemoveEmptyLists xs

-- 1. Factor into paths.
-- 2. Trim each path using the counting method.
-- 3. Build from trimmed paths.
--
-- Ok, so what's factoring into paths look like?
-- We recursively factor into paths, and throw the node in front of every one
-- of them. Each path is <node>, <edge>, <node>, <edge>, etc. ending in node.
--
-- | Factor a UI into its paths. The form of each path in the list is
--
--     '[ <node>, <edge>, <node>, etc. ]
--
--   If we line up all the paths in FactorUIIntoPaths ux, we find that the
--   first element of every list is the same as the first element in the other
--   lists.
--   If we pop that element off then we obtain a list where each consequtive
--   group of lists where the first two elements are the same indicates that
--   the path diverges later on.
--
--   The form of FactorUIIntoPaths is
--
--       '[ '[ <node> ] ]
--
--     | '[ '[ R ] ]
--
--     | '[ '[ Close ux ] ]
--
--     | '[ '[ <node>, <edge_1>, etc. ] ]
--        , '[ <node>, <edge_2>, etc. ] ]
--        , ...
--        , '[ <node>, <edge_n>, etc. ]
--        ]
--
--   Where <edge_n> and <edge_m> are not necessarily distinct.
--
--   We can reconstruct a UI from this path representation.
--   
--       '[ '[ <node> ] ] -> N '(node, T '[])
--
--       '[ '[ R ] ] -> R
--
--       '[ '[ Close ux ] ] -> Close ux
--
--   But for the final case it's more involved. We know the first element of
--   every list is the same as all of the other first elements. We pop that
--   off, group the resulting list by the first 2 elements, so that we have
--   something of kind  [(*, [[*]])]. The first component is the edge, the
--   second component is a list of paths suitable for recursion! It is one
--   of those FactorUIIntoPaths forms listed above.
--
--       '[ '[ <node>, <edge_1>, etc. ] ]
--        , '[ <node>, <edge_2>, etc. ] ]
--        , ...
--        , '[ <node>, <edge_n>, etc. ]    -> N '(node, T (RecurseOnEdges))
--
type family FactorUIIntoPaths (ux :: *) :: [[*]] where
    FactorUIIntoPaths (N '(node, T '[])) = '[ '[node] ]
    FactorUIIntoPaths (N '(node, T edges)) =
        PrefixLists node (FactorUIIntoPathsRec edges)
    FactorUIIntoPaths R = '[ '[R] ]
    FactorUIIntoPaths (Close x) = '[ '[Close x] ]

type family FactorUIIntoPathsRec (es :: [(*, *)]) :: [[*]] where
    FactorUIIntoPathsRec '[] = '[]
    FactorUIIntoPathsRec ( '(edge, nextUI) ': edges ) =
        Append
            (PrefixLists edge (FactorUIIntoPaths nextUI))
            (FactorUIIntoPathsRec edges)

type family ContractRecursiveParts (paths :: [[*]]) :: [[*]] where
    ContractRecursiveParts '[] = '[]
    ContractRecursiveParts (path ': paths) =
           ContractRecursivePart path
        ': ContractRecursiveParts paths

type family ContractRecursivePart (path :: [*]) :: [*] where
    ContractRecursivePart (node ': rest) = 
        ContractRecursivePartRec (node ': rest) rest 1

type family ContractRecursivePartRec (original :: [*]) (path :: [*]) (count :: Nat) :: [*] where
    ContractRecursivePartRec (node ': rest) '[] count = node ': rest
    ContractRecursivePartRec (node ': rest) '[Close x] count = node ': rest
    ContractRecursivePartRec (node ': rest) '[R] count = 
        ContractRecursivePartFinal (node ': rest) (node ': rest) '[] (NatHalf count)
    ContractRecursivePartRec (node ': rest) (node ': rest') count =
        ContractRecursivePartRec (node ': rest) rest' (count + 1)
    ContractRecursivePartRec (node ': rest) (node' ': rest') count =
        ContractRecursivePartRec (node ': rest) rest' (count)

type family ContractRecursivePartFinal (original :: [*]) (path :: [*]) (accumulate :: [*]) (count :: Nat) :: [*] where
    ContractRecursivePartFinal (node ': rest) (node ': rest') accumulate 1 = Snoc R accumulate
    ContractRecursivePartFinal (node ': rest) (node ': rest') accumulate count =
        ContractRecursivePartFinal (node ': rest) rest' (Snoc node accumulate) (count - 1)
    ContractRecursivePartFinal (node ': rest) (node' ': rest') accumulate count =
        ContractRecursivePartFinal (node ': rest) rest' (Snoc node' accumulate) count

type family ReconstructUIFromPaths (paths :: [[*]]) :: * where
    ReconstructUIFromPaths '[ '[R] ] = R
    ReconstructUIFromPaths '[ '[Close x] ] = Close x
    ReconstructUIFromPaths '[ '[node] ] = N '(node, T '[])
    ReconstructUIFromPaths paths =
        N '(FirstElement paths, T (ReconstructUIFromPathsRec (GroupByFirstTwoElements (RemoveEmptyLists (Tails paths)))))

type family ReconstructUIFromPathsRec (groupedPaths :: [(*, [[*]])]) :: [(*, *)] where
    ReconstructUIFromPathsRec '[] = '[]
    ReconstructUIFromPathsRec ( '(edge, paths) ': rest ) =
           '(edge, ReconstructUIFromPaths paths)
        ': (ReconstructUIFromPathsRec rest)

-- | Takes the first element of a list of lists, assuming that they all share
--   the same first element!
type family FirstElement (paths :: [[*]]) :: * where
    FirstElement ( (p ': rest) ': rest' ) = p

type family UIContractRecursiveParts (ux :: *) :: * where
    UIContractRecursiveParts ux = ReconstructUIFromPaths (ContractRecursiveParts (FactorUIIntoPaths ux))

type family GroupByFirstTwoElements (paths :: [[*]]) :: [(*, [[*]])] where
    GroupByFirstTwoElements '[] = '[]
    GroupByFirstTwoElements ( (p ': q ': rest) ': rest' ) =
        GroupByFirstTwoElementsParticular p q rest' '[q ': rest]

type family GroupByFirstTwoElementsParticular (p :: *) (q :: *) (paths :: [[*]]) (accumulated :: [[*]]) where
    
    GroupByFirstTwoElementsParticular p q '[] accumulated = '[ '(p, accumulated) ]

    -- Two cases for a match.
    GroupByFirstTwoElementsParticular p q ( '[( p ': q ': rest) ] ) accumulated =
        '[ '(p, Snoc (q ': rest) accumulated) ]

    GroupByFirstTwoElementsParticular p q ( ( p ': q ': rest ) ': rest' ) accumulated =
        GroupByFirstTwoElementsParticular p q rest' (Snoc (q ': rest) accumulated)

    -- Two cases for no match.
    GroupByFirstTwoElementsParticular p q ( '[( r ': s ': rest )] ) accumulated =
           '(p, accumulated)
        ': '[ '(r, '[ s ': rest ]) ]

    GroupByFirstTwoElementsParticular p q ( ( r ': s ': rest ) ': rest' ) accumulated =
           '(p, accumulated)
        ': GroupByFirstTwoElements ( ( r ': s ': rest ) ': rest' )
-}
