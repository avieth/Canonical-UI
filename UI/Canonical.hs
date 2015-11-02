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
{-# LANGUAGE RankNTypes #-}

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

    , runUI
    , ui
    , InterpretedUI
    , runInterpretedUI

    ) where

import GHC.TypeLits
import Control.Monad (join, when)
import Data.Profunctor (dimap)
import Data.Proxy
import Data.Void
import Data.Algebraic.Index
import Data.Algebraic.Sum
import Data.Algebraic.Product

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


-- | An @m t@ with a phantom type @q@. That @q@ will be some ui (an @N@)
--   indicates that the @m t@ is an interpreteation of that ui.
data InterpretedUI q m t = InterpretedUI {
      runInterpretedUI :: m t
    }

reinterpretUI :: InterpretedUI q m t -> InterpretedUI r m t
reinterpretUI = InterpretedUI . runInterpretedUI

-- How it's gonna work?
--   1. You have your UI  N (node, T transtions).
--   2. To interpret it, you must give an arrow
--
--        node -> m (UITransitionSumT (T transitions))
--
--      and a sum of functions: for each event in the transitions, a function
--      from it to its corresponding interpretedUI.
--
--   3. The result?
--
--        node -> InterpretedUX ui t
--
--      To run it, use the node to evaluate the arrow, and when an event
--      comes back, run the appropriate function and reinterpret the output
--      UI.
--
-- So when we take that product of functions, what do we do with it?
-- We need to be able to apply it to the corresponding sum, and we need to
-- be able to reinterpret the outputs to the current UI type.

type family UINode (ui :: *) :: * where
    UINode (N '(node, trans)) = node

type family UITransEdges (ui :: *) :: * where
    UITransEdges (N '(node, trans)) = UITransitionSumT trans

-- | From a transition type (T '[(e, q)]) compute the sum of events which must
--   be handled in order to interpret it.
type family UITransitionSumT (es :: *) :: * where
    UITransitionSumT (T '[]) = Void
    UITransitionSumT (T '[ '(e, q) ]) = e
    UITransitionSumT (T ( '(e, q) ': es )) = e :+: UITransitionSumT (T es)

-- | This family determines the product of functions required to do transitions
--   on a UI. It is responsible for juggling the R and Close types, to ensure
--   that recursion is rolled out only where appropriate.
--
--
type family UITransitionFunctions (ui :: *) (m :: * -> *) (r :: *) where
    UITransitionFunctions (N '(node, T edges)) m r =
        UITransitionFunctionsRec (N '(node, T edges)) (N '(node, T edges)) m r

type family UITransitionFunctionsRec (originalUI :: *) (recurseUI :: *) (m :: * -> *) (r :: *) where
    UITransitionFunctionsRec ui (N '(node, T '[])) m r = Void -> m r
    UITransitionFunctionsRec ui (N '(node, T '[ '(e, q) ])) m r =
            (e -> InterpretedUI (UITransitionTypeParameter ui q) m r)
    UITransitionFunctionsRec ui (N '(node, T ( '(e, q) ': rest ))) m r =
            (e -> InterpretedUI (UITransitionTypeParameter ui q) m r)
        :*: UITransitionFunctionsRec ui (N '(node, T rest)) m r

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



-- | Instances follow the UITransitionFunctions/UITransitionFunctionsRec family.
class UITransition product sum m r where
    uiTransition :: product -> sum -> m r

instance
    (
    ) => UITransition (Void -> m r) Void m r
  where
    uiTransition f = f

instance {-# OVERLAPS #-}
    (
    ) => UITransition (e -> InterpretedUI q m r) e m r
  where
    uiTransition f e = runInterpretedUI (f e)

instance {-# OVERLAPS #-}
    ( UITransition frest erest m r
    ) => UITransition ((e -> InterpretedUI q m r) :*: frest) (e :+: erest) m r
  where
    uiTransition (Product (f, frest)) (Sum esum) = case esum of
        Left e -> runInterpretedUI (f e)
        Right erest -> uiTransition frest erest

runUI
    :: ( Monad m 
       , UITransition (UITransitionFunctions ui m r) (UITransEdges ui) m r
       )
    => Proxy ui
    -> Proxy m
    -> Proxy r
    -> (UITransitionFunctions ui m r)
    -> (UINode ui -> m (UITransEdges ui))
    -> (UINode ui -> InterpretedUI ui m r)
runUI _ _ _ trans wait node = InterpretedUI $ do
    event <- wait node
    uiTransition trans event

ui
    :: ( Monad m 
       , UITransition (UITransitionFunctions ui m r) (UITransEdges ui) m r
       )
    => (UITransitionFunctions ui m r)
    -> (UINode ui -> m (UITransEdges ui))
    -> (UINode ui -> InterpretedUI ui m r)
ui = runUI Proxy Proxy Proxy

type Singleton n = N '(n, T '[])

type Loop ui e = ui :>- e ->: R

-- How about that Maybe UI?
--
--   initial >------ s -----> output
--       v                      ^
--        \                    /
--       Nothing              s
--          \                /
--           \              /
--            +--- input --+
--
-- To run it you must give only
--
--     s -> InterpretedUX output m r
--     () -> input
--     input -> m s
--
-- Something's not right, though. We should be allowed to use any ui for input,
-- just as we can use any ui for output. Well, any ui so long as it outputs
-- an s. But we don't have any indication of that here...
-- And that's really what we want to express, right? If you have a UI which
-- has a dangling s edge, and you have a way to run some UI from an s, then
-- we can optionally run that input UI by taking an s :+: ().
--
-- The canonical example: input is a login UI, but we may want to bypass it
-- in case we already know who the user is.
type UIMaybe s initial input output = initial :>- s  ->: output
                                              :>- () ->: input :>-- s -->: output


type UILogin initial attempt attempting failed succeeded t =
    initial :>- attempt ->: attempting :>-- failed    -->: R
                                       :>-- succeeded -->: t

uiLogin :: Int -> InterpretedUI (UILogin Int (Int, String) () () String (Singleton ())) IO Void
uiLogin = ui (\(i, str) -> ui ((\() -> uiLogin (i + 1))
                              .*. (\str -> ui return (\() -> let q = getLine >>= \str -> putStrLn ("Echo " ++ str) >> q in q) ())
                              )
                              (\() -> if str == "foo" then return (inject two "foo") else return (inject one ()))
                              ()
             )
             (\i -> putStrLn ("Attempt " ++ (show i)) >> getLine >>= \str -> return (i, str))
