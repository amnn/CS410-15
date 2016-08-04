module Ex2 where

----------------------------------------------------------------------------
-- EXERCISE 2 -- STRUCTURE WITH VECTORS
--
-- VALUE:     15%
-- DEADLINE:  5pm, Friday 23 October (week 5)
--
-- DON'T SUBMIT, COMMIT!
--
-- The purpose of this exercise is to introduce you to some useful
-- mathematical structures and build good tools for working with
-- vectors
----------------------------------------------------------------------------

open import CS410-Prelude
open import CS410-Monoid
open import CS410-Nat
open import CS410-Vec hiding (vec; vapp)
open import CS410-Functor

-- HINT: your tasks are heralded with the eminently searchable tag, "???"


----------------------------------------------------------------------------
-- ??? 2.1 replicattion to make a constant vector             (score: ? / 1)
----------------------------------------------------------------------------

vec : forall {n X} -> X -> Vec X n
vec {zero}  x = []
vec {suc n} x = x :: vec {n} x

-- HINT: you may need to override default invisibility

-- SUSPICIOUS: no specification? why not?


----------------------------------------------------------------------------
-- ??? 2.2 vectorised application                             (score: ? / 1)
----------------------------------------------------------------------------

-- implement the operator which takes the same number of functions
-- and arguments and computes the applications in corresponding
-- positions

vapp : forall {n X Y} ->
       Vec (X -> Y) n -> Vec X n -> Vec Y n
vapp  []        []       = []
vapp (f :: fs) (x :: xs) = f x :: vapp fs xs


----------------------------------------------------------------------------
-- ??? 2.3 one-liners                                         (score: ? / 1)
----------------------------------------------------------------------------

-- implement map and zip for vectors using vec and vapp
-- no pattern matching or recursion permitted

vmap : forall {n X Y} -> (X -> Y) -> Vec X n -> Vec Y n
vmap f xs = vapp (vec f) xs

vzip : forall {n X Y} -> Vec X n -> Vec Y n -> Vec (X * Y) n
vzip xs ys = vapp (vmap _,_ xs) ys


----------------------------------------------------------------------------
-- ??? 2.4 unzipping                                          (score: ? / 2)
----------------------------------------------------------------------------

-- implement unzipping as a view, showing that every vector of pairs
-- is given by zipping two vectors

-- you'll need to complete the view type yourself

data Unzippable {X Y n} : Vec (X * Y) n -> Set where
  unzipped : (xs : Vec X n) -> (ys : Vec Y n) -> Unzippable (vzip xs ys)

unzip : forall {X Y n}(xys : Vec (X * Y) n) -> Unzippable xys
unzip  []                                       = unzipped [] []
unzip (x , y :: xys)           with unzip xys
unzip (x , y :: .(vzip xs ys)) | unzipped xs ys = unzipped (x :: xs) (y :: ys)


----------------------------------------------------------------------------
-- ??? 2.5 vectors are applicative                            (score: ? / 2)
----------------------------------------------------------------------------

-- prove the Applicative laws for vectors

VecApp : forall n -> Applicative \X -> Vec X n
VecApp n = record
  { pure         = vec
  ; _<*>_        = vapp
  ; identity     = Identity-Law
  ; composition  = Composition-Law
  ; homomorphism = Homomorphism-Law
  ; interchange  = Interchange-Law
  } where
    Identity-Law :
         forall {n X}
      -> (v : Vec X n)
      -> vapp (vec id) v
      == v

    Identity-Law [] = refl
    Identity-Law (x :: xs)
      rewrite Identity-Law xs
      = refl

    Composition-Law :
         forall {n X Y Z}
      -> (fs : Vec (Y -> Z) n)
      -> (gs : Vec (X -> Y) n)
      -> (xs : Vec  X       n)
      ->  vapp (vapp (vapp (vec \ f g x -> f (g x)) fs) gs) xs
      ==  vapp fs (vapp gs xs)

    Composition-Law [] [] [] = refl
    Composition-Law (f :: fs) (g :: gs) (x :: xs)
      rewrite Composition-Law fs gs xs
      = refl

    Homomorphism-Law :
         forall {n X Y}
      -> (f : X -> Y)
      -> (x : X)
      ->  vec {n} (f x)
      ==  vapp (vec f) (vec x)

    Homomorphism-Law {zero}  f x = refl
    Homomorphism-Law {suc n} f x
      rewrite Homomorphism-Law {n} f x
      = refl

    Interchange-Law :
         forall {n X Y}
      -> (fs : Vec (X -> Y) n)
      -> (x  : X)
      -> vapp fs (vec x)
      == vapp (vec \ f -> f x) fs

    Interchange-Law [] x = refl
    Interchange-Law (f :: fs) x
      rewrite Interchange-Law fs x
      = refl

----------------------------------------------------------------------------
-- ??? 2.6 vectors are traversable                            (score: ? / 1)
----------------------------------------------------------------------------

-- show that vectors are traversable; make sure your traverse function
-- acts on the elements of the input once each, left-to-right

VecTrav : forall n -> Traversable \X -> Vec X n
VecTrav n = record
  { traverse = vtrav {n}
  } where
    vtrav :
         forall {m : Nat}
      -> {F : Set -> Set}
      ->  Applicative F
      -> {A B : Set}
      -> (A -> F B)
      ->  Vec A m
      ->  F (Vec B m)

    vtrav {zero}  apF act xs = Applicative.pure apF []
    vtrav {suc m} apF act (x :: xs) =
      pure _::_ <*> act x <*> vtrav {m} apF act xs
      where
        open Applicative apF


----------------------------------------------------------------------------
-- ??? 2.7 monoids make constant applicatives                 (score: ? / 1)
----------------------------------------------------------------------------

-- Show that every monoid gives rise to a degenerate applicative functor

MonCon : forall {X} -> Monoid X -> Applicative \_ -> X
MonCon {A} M = record
  { pure          = \ _ -> e
  ; _<*>_         = op
  ; identity      = lunit
  ; composition   = Composition-Law
  ; homomorphism  = \ _ _ -> sym (lunit e)
  ; interchange   = Interchange-Law
  } where
    open Monoid M

    Composition-Law :
         (u v w : A)
      -> op (op (op e u) v) w
      == op u (op v w)

    Composition-Law u v w
      rewrite lunit u
            | assoc u v w
      = refl

    Interchange-Law :
         forall {X : Set}
      -> (u : A)
      -> X
      -> op u e
      == op e u

    Interchange-Law u _
      rewrite lunit u
            | runit u
      = refl


----------------------------------------------------------------------------
-- ??? 2.8 vector combine                                     (score: ? / 1)
----------------------------------------------------------------------------

-- Using your answers to 2.6 and 2.7, rather than any new vector recursion,
-- show how to compute the result of combining all the elements of a vector
-- when they belong to some monoid.

vcombine : forall {X} -> Monoid X ->
           forall {n} -> Vec X n -> X
vcombine M = {!!}


----------------------------------------------------------------------------
-- ??? 2.9 scalar product                                     (score: ? / 1)
----------------------------------------------------------------------------

-- Show how to compute the scalar ("dot") product of two vectors of numbers.
-- (Multiply elements in corresponding positions; compute total of products.)
-- HINT: think zippily, then combine

vdot : forall {n} -> Vec Nat n -> Vec Nat n -> Nat
vdot xs ys = {!!}


----------------------------------------------------------------------------
-- MATRICES
----------------------------------------------------------------------------

-- let's say that an h by w matrix is a column h high of rows w wide

Matrix : Set -> Nat * Nat -> Set
Matrix X (h , w) = Vec (Vec X w) h


----------------------------------------------------------------------------
-- ??? 2.11 identity matrix                                   (score: ? / 1)
----------------------------------------------------------------------------

-- show how to construct the identity matrix of a given size, with
-- 1 on the main diagonal and 0 everywhere else, e.g,
-- (1 :: 0 :: 0 :: []) ::
-- (0 :: 1 :: 0 :: []) ::
-- (0 :: 0 :: 1 :: []) ::
-- []

idMat : forall {n} -> Matrix Nat (n , n)
idMat = {!!}

-- HINT: you may need to do recursion on the side, but then you
-- can make good use of vec and vapp


----------------------------------------------------------------------------
-- ??? 2.10 transposition                                     (score: ? / 1)
----------------------------------------------------------------------------

-- show how to transpose matrices
-- HINT: use traverse, and it's a one-liner

transpose : forall {X m n} -> Matrix X (m , n) -> Matrix X (n , m)
transpose = {!!}


----------------------------------------------------------------------------
-- ??? 2.11 multiplication                                    (score: ? / 2)
----------------------------------------------------------------------------

-- implement matrix multiplication
-- HINT: transpose and vdot can be useful

matMult : forall {m n p} ->
          Matrix Nat (m , n) -> Matrix Nat (n , p) -> Matrix Nat (m , p)
matMult xmn xnp = {!!}
