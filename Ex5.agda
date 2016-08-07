------------------------------------------------------------------------------
-- CS410 Exercise 5
--
-- Given the overrunning of exercise 4, I've decided to shift the deadline
-- for exercise 5 back to the end of semester 2, so you can have a wee go
-- in the last week of semester 1, but then focus on your CS408 projects.
--
-- Exercise 6 will follow directly on from this and share the deadline, but
-- it will be issued at Easter.
--
-- I don't know the precise deadline, because I have not yet been told the
-- mark upload deadline for the semester 2 exam board. I will give you as
-- much time as I can. Usually, I can make the deadline after the last
-- exam, but I haven't seen the timetable yet.
--
-- It's a good idea to start well before the exams, get the basics sorted,
-- then come back to it after the exams and apply polish.
------------------------------------------------------------------------------

module Ex5 where

open import CS410-Prelude
open import CS410-Nat
open import CS410-Vec
open import CS410-Indexed
open import CS410-Monoid


------------------------------------------------------------------------------
-- CHARACTERS AND STRINGS  -- moved to CS410-Prelude
------------------------------------------------------------------------------
{-
data List (X : Set) : Set where  -- X scopes over the whole declaration...
  []    : List X                 -- ...so you can use it here...
  _::_  : X -> List X -> List X  -- ...and here.
infixr 3 _::_

{-# BUILTIN BOOL Two #-}
{-# BUILTIN TRUE tt #-}
{-# BUILTIN FALSE ff #-}
{-# BUILTIN LIST List #-}
{-# BUILTIN NIL [] #-}
{-# BUILTIN CONS _::_ #-}
{-# COMPILED_DATA List [] [] (:) #-}

postulate -- this means that we just suppose the following things exist...
  Char : Set
  String : Set
{-# BUILTIN CHAR Char #-}
{-# COMPILED_TYPE Char Char #-}
{-# BUILTIN STRING String #-}
{-# COMPILED_TYPE String String #-}

primitive -- these are baked in; they even work!
  primCharEquality : Char -> Char -> Two
  primStringAppend : String -> String -> String
  primStringToList : String -> List Char
  primStringFromList : List Char -> String
-}


------------------------------------------------------------------------------
-- THE TILING MONAD (from lectures)
------------------------------------------------------------------------------

WH : Set
WH = Nat * Nat

data Tiling (X : WH -> Set)(wh : WH) : Set where
  ! : X wh -> Tiling X wh

  joinH :
       (wl wr : Nat)
    -> (wq    : wl +N wr == fst wh)
    ->  Tiling X (wl , snd wh)
    ->  Tiling X (wr , snd wh)
    ->  Tiling X  wh

  joinV :
       (ht hb : Nat)
    -> (hq    : ht +N hb == snd wh)
    ->  Tiling X (fst wh , ht)
    ->  Tiling X (fst wh , hb)
    ->  Tiling X wh

TilingMonadIx : MonadIx Tiling
TilingMonadIx = record
  { retIx = !
  ; extendIx = help
  } where
  help : {P Q : WH -> Set} -> [ P -:> Tiling Q ] -> [ Tiling P -:> Tiling Q ]
  help f (! p) = f p
  help f (joinH wl wr wq t-l t-r) = joinH wl wr wq (help f t-l) (help f t-r)
  help f (joinV ht hb hq t-t t-b) = joinV ht hb hq (help f t-t) (help f t-b)

-- That's the monad you'll need in this file, so let's open it.

open MonadIx TilingMonadIx
open FunctorIx (monadFunctorIx TilingMonadIx)


------------------------------------------------------------------------------
-- PASTE KITS
------------------------------------------------------------------------------

-- A PasteKit equips rectangular stuff with the means to stick
-- things the same height side-by-side, or things the same width
-- one-on-top-of-the-other

record PasteKit (X : WH -> Set) : Set where
  field
    pasteH :
         {wh : WH}
      -> (wl wr : Nat)
      -> (wq : wl +N wr == fst wh)
      ->  X (wl , snd wh)
      ->  X (wr , snd wh)
      -> X wh

    pasteV :
         {wh : WH}
      -> (ht hb : Nat)
      -> (hq : ht +N hb == snd wh)
      ->  X (fst wh , ht)
      ->  X (fst wh , hb) -> X wh

-- ??? 5.1 (1 mark)
-- Show that if you have a PasteKit for X tiles, you can turn a
-- Tiling X into one big X.

paste : forall {X} -> PasteKit X -> [ Tiling X -:> X ]
paste {X} pk = go where
  open PasteKit pk
  go : [ Tiling X -:> X ]
  go (! x) = x
  go (joinH wl wr wq l r) = pasteH wl wr wq (go l) (go r)
  go (joinV ht hb hq t b) = pasteV ht hb hq (go t) (go b)


------------------------------------------------------------------------------
-- CUT KITS
------------------------------------------------------------------------------

-- A CutKit consists of functions which split a rectangular thing in two,
-- horizontally or vertically.

record CutKit (X : WH -> Set) : Set where
  field
    cutH :
         {wh : WH}
      -> (wl wr : Nat)
      -> (wq : wl +N wr == fst wh)
      ->  X wh
      ->  X (wl , snd wh) *  X (wr , snd wh)

    cutV :
         {wh : WH}
      -> (ht hb : Nat)
      -> (hq : ht +N hb == snd wh)
      -> X wh
      -> X (fst wh , ht) *  X (fst wh , hb)


------------------------------------------------------------------------------
-- MATRICES
------------------------------------------------------------------------------

Matrix : Set -> WH -> Set
Matrix C (w , h) = Vec (Vec C w) h

-- ??? 5.2 (2 marks)
-- Equip matrices with a PasteKit and a CutKit. Try to make good use of
-- the operations developed for vectors.

matrixPaste : {C : Set} -> PasteKit (Matrix C)
matrixPaste {C} = record
  {  pasteH = mPH
  ;  pasteV = mPV
  }  where

  _<*>_ : forall {n X Y} -> Vec (X -> Y) n -> Vec X n -> Vec Y n
  _<*>_ = vapp
  infixl 3 _<*>_

  mPH :
       {wh : WH}
    -> (wl wr : Nat)
    ->  wl +N wr == fst wh
    ->  Matrix C (wl , snd wh)
    ->  Matrix C (wr , snd wh)
    ->  Matrix C wh

  mPH wl wr refl ml mr = vec _+V_ <*> ml <*> mr


  mPV :
       {wh : WH}
    -> (ht hb : Nat)
    ->  ht +N hb == snd wh
    ->  Matrix C (fst wh , ht)
    ->  Matrix C (fst wh , hb)
    ->  Matrix C wh

  mPV ht hb refl mt mb = mt +V mb

matrixCut : {C : Set} -> CutKit (Matrix C)
matrixCut {C} = record
  {  cutH = mCH
  ;  cutV = mCV
  }  where

  open import Ex2 using (vmap)

  mCH :
       {wh : WH}
    -> (wl wr : Nat)
    ->  wl +N wr == fst wh
    ->  Matrix C wh
    ->  Matrix C (wl , snd wh)
     *  Matrix C (wr , snd wh)

  mCH {.(wl +N wr) , h } wl wr refl m =
    let
      split : Vec (Vec C wl * Vec C wr) h
      split = vmap (chopParts wl wr) m
    in
      vmap fst split ,
      vmap snd split

  mCV :
       {wh : WH}
    -> (ht hb : Nat)
    ->  ht +N hb == snd wh
    ->  Matrix C wh
    ->  Matrix C (fst wh , ht)
     *  Matrix C (fst wh , hb)

  mCV ht hb refl m = chopParts ht hb m


---------------------------------------------------------------------------
-- COLOURS
---------------------------------------------------------------------------

-- We're going to be making displays from coloured text.
{- moved to prelude
data Colour : Set where
  black red green yellow blue magenta cyan white : Colour
{-# COMPILED_DATA Colour HaskellSetup.Colour
      HaskellSetup.Black HaskellSetup.Red HaskellSetup.Green
      HaskellSetup.Yellow HaskellSetup.Blue HaskellSetup.Magenta
      HaskellSetup.Cyan HaskellSetup.White #-}
-}
-- Each cell in a display has this information:

record Cell : Set where
  constructor _-_/_
  field
    fgCo  : Colour    -- foreground colour
    char  : Char      -- character to display in cell
    bgCo  : Colour    -- background colour

-- e.g.   white - '*' / black

-- Now,
--      Matrix Cell : WH -> Set
-- is a suitable notion of sized display


---------------------------------------------------------------------------
-- INTERLUDE: TESTING WITH TEXT
---------------------------------------------------------------------------

-- I've written some code which should help you see what you're doing.

-- Turn a list into a vector, either by truncating or padding with
-- a given dummy element.
paddy : {X : Set} -> X -> List X -> {n : Nat} -> Vec X n
paddy _ _         {zero}   = []
paddy x []        {suc n}  = x :: paddy x [] {n}
paddy x (y :: ys) {suc n}  = y :: paddy x ys {n}

-- Turn some colours and a string into a vector of cells
_-_//_ : Colour -> String -> Colour -> {n : Nat} -> Vec Cell n
f - s // b =  vapp  (vapp (vec (_-_/_ f))
                    (paddy ' ' (primStringToList s)))
              (vec b)
infixr 4 _-_//_

-- Build an example matrix
example1 : Matrix Cell (10 , 5)
example1  =   black - "hydrogen"   // white
          ::  black - "helium"     // white
          ::  black - "lithium"    // white
          ::  black - "beryllium"  // white
          ::  black - "boron"      // white
          ::  []

-- Cut it up
example23 : Matrix Cell (5 , 5) * Matrix Cell (5 , 5)
example23 = cutH 5 5 refl example1
  where open CutKit matrixCut

-- Stick the bits back together, vertically
example4 : Matrix Cell (5 , 10)
example4 = pasteV 5 5 refl (fst example23) (snd example23)
  where open PasteKit matrixPaste


---------------------------------------------------------------------------
-- CUTTING UP TILINGS
---------------------------------------------------------------------------

-- Previously...
-- ... we established what it is to be a CutKit, and we built CutKits
-- for some sorts of basic tile. Now we need to build the CutKit for
-- Tilings. Let's think about what that involves for a moment. We're going
-- to need a CutKit for basic tiles to stand a chance. But how do we
-- cut compound tiles?
--
-- Suppose we're writing cutH, and we have some
--   cq : cwl + cwr == w   -- the "cut widths" equation
-- telling us where we want to make the cut in something of width w.
--
--             v
--    +--------:------+
--    |        :      |
--    |        :      |
--    +--cwl---:-cwr--+
--    :        ^      :
--    :.......w.......:
--
-- The tricky part is when the tiling we're cutting here is built with
--   joinH twl twr tq tl tr
-- where
--   tq : twl + twr == w   -- the "tiling widths" equation
--
-- There are three possible situations, all of which you must detect
-- and handle.
--
-- (i) you hit the sweet spot...
--
--             v
--    +--bwl---+-bwr--+
--    |        |      |
--    |        |      |
--    +--cwl---+-cwr--+
--    :        ^      :
--    :.......w.......:
--
--     ...where the box is already divided in the place where the cut
--     has to go. Happy days.
--
-- (ii) you're cutting to the left of the join...
--
--             v
--    +--bwl-----+bwr-+
--    |        : |    |
--    |        : |    |
--    +--cwl---:-cwr--+
--    :        ^      :
--    :.......w.......:
--
--     ...so you'll need to cut the left box in the correct place. You
--     will need some evidence about widths to do that. And then you'll
--     the have three pieces you can see in my diagram, so to complete
--     the cut, you will need to put two of those pieces together, which
--     will take more evidence.
--
-- (iii) you're cutting to the right of the join...
--
--             v
--    +--bwl-+--bwr---+
--    |      | :      |
--    |      | :      |
--    +--cwl---:-cwr--+
--    :        ^      :
--    :.......w.......:
--
--     ...so you'll need to cut the right box in the correct place, and
--     reassemble the bits.
--
-- HINT: The next three tasks go together.

-- ??? 5.3.1 (1 mark)
-- COMPARING THE CUT POSITION

data CutComparable (x x' y y' n : Nat) : Set where
  -- Give three constructors for this type which characterize the three
  -- possibilities described above whenever
  --   x + x' == n   and   y + y' == n
  -- (E.g., take n to be w, x and x' to be cwl and cwr, y and y' to be
  -- twl and twr. But later, you'll need to do use the same tool for
  -- heights.)
  --
  -- You will need to investigate what evidence must be packaged in each
  -- situation. On the one hand, you need to be able to *generate* the
  -- evidence, with cutCompare, below. On the other hand, the evidence
  -- must be *useful* when you come to write tilingCut, further below.
  -- Don't expect to know what to put here from the get-go. Figure it
  -- out by discovering what you *need*.

  -- YOUR CONSTRUCTORS GO HERE
  sweet-spot :
       (cq : x +N x' == n)
    -> (dq : y +N y' == n)
    -> (q  : x == y)
    -> CutComparable x x' y y' n

  cut-near :
       (cq : x +N x' == n)
    -> (dq : y +N y' == n)
    -> (d : Nat)
    -> (q : x +N d == y)
    -> CutComparable x x' y y' n

  cut-far :
       (cq : x +N x' == n)
    -> (dq : y +N y' == n)
    -> (d : Nat)
    -> (q : d +N x' == y')
    -> CutComparable x x' y y' n

-- The following facts may come in handy.

trans :
      forall {l}
  -> {X : Set l}
  -> {a b c : X}
  -> (a == b)
  -> (b == c)
  -> (a == c)
trans refl refl = refl

cong :
      forall {l}
  -> {X : Set l}
  -> (P : X -> Set)
  -> {x y : X}
  -> (x == y)
  ->  P x
  ->  P y
cong _ refl px = px

sucInject : {m n : Nat} -> suc m == suc n -> m == n
sucInject refl = refl

sucRespect : {m n : Nat} -> m == n -> suc m == suc n
sucRespect refl = refl

sucInject* : {m n : Nat} -> (p : Nat) -> p +N m == p +N n -> m == n
sucInject*  zero   q = q
sucInject* (suc p) q = sucInject* p (sucInject q)

comm : (m n : Nat) -> m +N n == n +N m
comm  zero    n      = sym (Monoid.runit +Mon n)
comm (suc m)  zero   = sucRespect (Monoid.runit +Mon m)
comm (suc m) (suc n) = sucRespect (trans p₁ (trans p₂ p₃))
  where
    p₁ : m +N suc n == suc (n +N m)
    p₁ = comm m (suc n)

    p₂ : suc (n +N m) == suc (m +N n)
    p₂ = sucRespect (comm n m)

    p₃ : suc (m +N n) == n +N suc m
    p₃ = sym (comm n (suc m))

-- ??? 5.3.2 (1 mark)
-- Show that whenever you have two ways to express the same n as a sum,
-- you can always deliver the CutComparable evidence.

cutCompare :
     (x x' y y' n : Nat)
  -> x +N x' == n
  -> y +N y' == n
  -> CutComparable x x' y y' n

cutCompare zero x' zero y' n xq yq =
  sweet-spot xq yq refl

cutCompare zero x' (suc y) y' n xq yq =
  cut-near xq yq (suc y) refl

cutCompare (suc x) x' zero y' n xq yq =
  cut-far xq yq (suc x) (trans xq (sym yq))

cutCompare (suc x) x' (suc y) y'  zero   () ()
cutCompare (suc x) x' (suc y) y' (suc n) xq yq
   with cutCompare x x' y y' n (sucInject xq) (sucInject yq)
...| sweet-spot _ _   q = sweet-spot xq yq   (sucRespect q)
...| cut-near   _ _ d q = cut-near   xq yq d (sucRespect q)
...| cut-far    _ _ d q = cut-far    xq yq d  q


-- ??? 5.3.3 (2 marks)
-- A CUTKIT FOR TILINGS

-- Now, show that you can construct a CutKit for Tiling X, given a CutKit
-- for X. There will be key points where you get stuck for want of crucial
-- information. The purpose of CutCompare is to *describe* that
-- information. The purpose of cutCompare is to *compute* that information.
-- Note that cutH and cutV will work out very similarly, just exchanging
-- the roles of width and height.

-- Hint: good solutions are likely to use "with" a lot.

tilingCut : {X : WH -> Set} -> CutKit X -> CutKit (Tiling X)
tilingCut {X} ck = record
  { cutH = cH
  ; cutV = cV
  } where
    open CutKit ck
    cH :
         {wh : WH}
      -> (wl wr : Nat)
      -> (wq : wl +N wr == fst wh)
      ->  Tiling X wh
      ->  Tiling X (wl , snd wh)
      *   Tiling X (wr , snd wh)

    cH {w , h} cwl cwr wq (! x) =
      let
        cx : X (cwl , h) * X (cwr , h)
        cx = cutH cwl cwr wq x
      in
        ! (fst cx) , ! (snd cx)

    cH {w , h} cwl cwr cwq (joinH wl wr dwq l r)
       with cutCompare cwl cwr wl wr w cwq dwq

    ...| sweet-spot cq dq q
       rewrite q
             | sucInject* wl (trans cq (sym dq))
       = l , r

    ...| cut-near cq dq d q =
      let
        cl : Tiling X (cwl , h) * Tiling X (d , h)
        cl = cH cwl d q l

        p₁ : (cwl +N d) +N wr == w
        p₁ = cong (\ ● -> ● +N wr == w) (sym q) dwq

        p₂ : cwl +N (d +N wr) == (cwl +N d) +N wr
        p₂ = Monoid.assoc +Mon cwl d wr

        p₃ : cwl +N (d +N wr) == cwl +N cwr
        p₃ = trans (trans p₂ p₁) (sym cwq)

        qr : d +N wr == cwr
        qr = sucInject* cwl p₃
      in
        fst cl , joinH d wr qr (snd cl) r

    ...| cut-far cq dq d q =
      let
        cr : Tiling X (d , h) * Tiling X (cwr , h)
        cr = cH d cwr q r

        p₁ : wl +N (d +N cwr) == w
        p₁ = cong (\ ● -> wl +N ● == w) (sym q) dwq

        p₂ : (wl +N d) +N cwr == wl +N (d +N cwr)
        p₂ = sym (Monoid.assoc +Mon wl d cwr)

        p₃ : (wl +N d) +N cwr == cwl +N cwr
        p₃ = trans (trans p₂ p₁) (sym cwq)

        ql : wl +N d == cwl
        ql = sucInject* cwr (trans (trans (comm cwr (wl +N d)) p₃)
                                   (comm cwl cwr))
      in
        joinH wl d ql l (fst cr) , snd cr

    cH {w , h} cwl cwr cwq (joinV ht hb hq  t b) =
      let
        ct : Tiling X (cwl , ht) * Tiling X (cwr , ht)
        ct = cH cwl cwr cwq t

        cb : Tiling X (cwl , hb) * Tiling X (cwr , hb)
        cb = cH cwl cwr cwq b
      in
        (joinV ht hb hq (fst ct) (fst cb)) ,
        (joinV ht hb hq (snd ct) (snd cb))


    cV :
         {wh : WH}
      -> (ht hb : Nat)
      -> (hq : ht +N hb == snd wh)
      ->  Tiling X wh
      ->  Tiling X (fst wh , ht)
      *   Tiling X (fst wh , hb)

    cV {w , h} cht chb cq (! x) =
      let
        cx : X (w , cht) * X (w , chb)
        cx = cutV cht chb cq x
      in
        ! (fst cx) , ! (snd cx)

    cV cht chb cq (joinH wl wr wq l r) =
      let
        cl : Tiling X (wl , cht) * Tiling X (wl , chb)
        cl = cV cht chb cq l

        cr : Tiling X (wr , cht) * Tiling X (wr , chb)
        cr = cV cht chb cq r
      in
        (joinH wl wr wq (fst cl) (fst cr)) ,
        (joinH wl wr wq (snd cl) (snd cr))

    cV {w , h} cht chb chq (joinV ht hb dhq t b)
       with cutCompare cht chb ht hb h chq dhq

    ...| sweet-spot cq dq q
       rewrite q
             | sucInject* ht (trans cq (sym dq))
       = t , b

    ...| cut-near cq dq d q =
      let
        ct : Tiling X (w , cht) * Tiling X (w , d)
        ct = cV cht d q t

        p₁ : (cht +N d) +N hb == h
        p₁ = cong (\ ● -> ● +N hb == h) (sym q) dhq

        p₂ : cht +N (d +N hb) == (cht +N d) +N hb
        p₂ = Monoid.assoc +Mon cht d hb

        p₃ : cht +N (d +N hb) == cht +N chb
        p₃ = trans (trans p₂ p₁) (sym chq)

        qb : d +N hb == chb
        qb = sucInject* cht p₃
      in
        fst ct , joinV d hb qb (snd ct) b

    ...| cut-far cq dq d q =
      let
        cb : Tiling X (w , d) * Tiling X (w , chb)
        cb = cV d chb q b

        p₁ : ht +N (d +N chb) == h
        p₁ = cong (\ ● -> ht +N ● == h) (sym q) dhq

        p₂ : (ht +N d) +N chb == ht +N (d +N chb)
        p₂ = sym (Monoid.assoc +Mon ht d chb)

        p₃ : (ht +N d) +N chb == cht +N chb
        p₃ = trans (trans p₂ p₁) (sym chq)

        qt : ht +N d == cht
        qt = sucInject* chb (trans (trans (comm chb (ht +N d)) p₃)
                                   (comm cht chb))
      in
        joinV ht d qt t (fst cb) , snd cb

---------------------------------------------------------------------------
-- SUPERIMPOSITION
---------------------------------------------------------------------------

-- ??? 5.4 (2 marks)
-- Suppose you have a tiling made of X tiles in front of a tiling made of
-- Y tiles.  Suppose you have a CutKit for Y. Suppose you know how to
-- superimpose *one* X tile on a Y tiling to make a Z tiling. You should be
-- able to superimpose X tilings on Y tilings to get a Z tiling: you can but
-- the back Y tiling into pieces which fit with the individual X tiles in
-- front.

super : {X Y Z : WH -> Set} -> CutKit Y ->
       [        X -:> Tiling Y -:> Tiling Z ] ->
       [ Tiling X -:> Tiling Y -:> Tiling Z ]
super {X}{Y}{Z} ck m = go where
  open CutKit (tilingCut ck)
  go : [ Tiling X -:> Tiling Y -:> Tiling Z ]
  go xt yt = {!!}

-- HINT: no new recursive operations are needed in the rest of this file.
-- You've done the hard work. Now get paid.


---------------------------------------------------------------------------
-- HOLES
---------------------------------------------------------------------------

-- ??? 5.5 (2 marks)
-- In order to build up displays in layers, we will need to work with
-- tilings where one sort of primitive tile is, in fact, a hole!

data HoleOr (X : WH -> Set)(wh : WH) : Set where
  hole   : HoleOr X wh           -- a hole you can see through
  block  : X wh -> HoleOr X wh   -- a block of stuff you can't see through


-- Explain how to see through a hole but not through a block

seeThrough : {X : WH -> Set} ->
             [ HoleOr X -:> Tiling (HoleOr X) -:> Tiling (HoleOr X) ]
seeThrough hx thx = {!!}


-- Show that if X has a CutKit, then so has HoleOr X. Cutting up holes is
-- very easy as they don't put up much resistance.

holeCut : {X : WH -> Set} -> CutKit X -> CutKit (HoleOr X)
holeCut ck = record
  { cutH = {!!}
  ; cutV = {!!}
  }
  where open CutKit ck


-- Now, a rectangular layer is a tiling whose pieces are either holes or
-- blocks of coloured text.

Layer : WH -> Set
Layer = Tiling (HoleOr (Matrix Cell))


-- By making careful use of super and seeThrough, show how layers of a given
-- size have monoid structure, where the operation combines "front" and "back"
-- layers by making the back layer visible only through the holes in the front.

layerId : [ Layer ]
layerId = {!!}

layerOp : [ Layer -:> Layer -:> Layer ]
layerOp = super {!!} {!!}

-- I'd ask you to prove that the monoid laws hold (they do), but when I did it,
-- it was too much of a slog for too few ideas.


-- A typical display is made by superimposing a bunch of layers, but you might
-- still leave some holes, so we need to fill in a background. Use the MonadIx
-- structure of tilings to fill in each hole in a Layer with a matrix of black
-- (but who can tell?) spaces on a white background.

background : [ Layer -:> Tiling (Matrix Cell) ]
background = mapIx {!!}


---------------------------------------------------------------------------
-- CHANGES
---------------------------------------------------------------------------

-- Applications change what they display as you use them, of course. Often
-- they change a little at a time, so it's not necessary to repaint the
-- whole thing. Let's build tilings to represent just what changes.

data Change (wh : WH) : Set where
  new : Layer wh -> Change wh
  old : Change wh

-- The idea is that you make a top-level tiling to show which regions have
-- changed, and for the ones with new content, you give the layer which is
-- that content. So a Tiling Change tells you the difference between the
-- old layer and the new layer.

-- ??? 5.6 (1 mark)
-- You should be able to compute the changed layer given the change and the old
-- layer. Hint: This, also, is a job for super.

changed : [ Tiling Change -:> Layer -:> Layer ]
changed = super {!!} {!!}


---------------------------------------------------------------------------
-- UPDATA
---------------------------------------------------------------------------

-- ??? 5.7 (3 marks)
-- A notion related to "Change" is "Updata", but they're subtly different:
--   the actual content in a change is just the new stuff, and we've seen we
--     can grab any old parts from the old layer;
--   the Updata structure stores *all* the content, but each tile is tagged
--     with a bit which tells you if it comes from the change or was there
--     before.

record Updata (wh : WH) : Set where
  constructor _-:_
  field
    updated  : Two                      -- has it changed
    content  : HoleOr (Matrix Cell) wh  -- what is it, anyway?

-- Correspondingly, you should be able to generate a Tiling Updata
-- from a Tiling Change and the old Layer. Work in two stages. First,
-- make a thing that generates a Tiling Updata from a Layer by
-- applying the same tag to all tiles.

tagLayer : Two -> [ Layer -:> Tiling Updata ]
tagLayer u = {!!}

-- Now you should be able to generate a version of "changed" that adds tags.

updata : [ Tiling Change -:> Layer -:> Tiling Updata ]
updata = {!!}

-- Last but not least, develop the monoid operations for Updata. Here's where
-- you sort out the logic for displaying changing layers. Content-wise, it should
-- be a lot like the Layer monoid, in that you can see the back stuff through
-- the holes in the front stuff. But what about the "updated" tags? Is there a
-- difference between an "old" hole in the front and a "new" hole in the front?
-- You will need to build a CutKit in order to use super appropriately.

updataId : [ Tiling Updata ]
updataId = {!!}

updataCut : CutKit Updata
updataCut = {!!}

updataOp : [ Tiling Updata -:> Tiling Updata -:> Tiling Updata ]
updataOp = {!!}


---------------------------------------------------------------------------
-- NEXT TIME...
---------------------------------------------------------------------------

-- We'll develop a notion of "Application" which can each display
-- their Layer, and respond to events by delivering a Tiling
-- Change. We'll develop a notion of "Desktop" which amounts to a
-- front-to-back stack of applications. The Desktop display updates
-- by superimposing the Tiling Updata which comes from the change made
-- by each application in the stack.

-- Once we've got that setup, we can run applications by getting events
-- from the keyboard, generating the Tiling Updata for the whole Desktop,
-- then use cursor movement to skip the unchanged parts and just rewrite
-- the regions which need it. It'll actually go!
