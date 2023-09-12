{- 

      Dependently Typed Programming
      
           Mauro Jaskelioff
 
   Universidad Nacionl de Rosario, Argentina

 Inspired by a course by Thorsten Altenkirch, 
 and a talk by Conor McBride (ICFP 2012).


-}

module Intro3 where


{- Let's learn about Agda. -}

{- Agda has very few reserved characters and a very simple lexer.
 The characters (){} separate things, but everything else must be separated by spaces.
-}

{- Let us define the natural numbers -}
data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

{- C-c C-l executes the type checker. 
 if everything goes well we should see colour
-}
{- Unicode characters
  → = \to

   -}

{- The following pragma allows to write arabic numerals
  instead of suc (suc (.... ))
-}
{-# BUILTIN NATURAL Nat    #-}


_+_ : Nat → Nat → Nat
zero + n = n
suc m + n = suc (m + n)

--{-# BUILTIN NATPLUS _+_ #-}


{- C-c C-c splits in cases -}
{- C-c C-r refines the problem -}
{- We can look for a definition using M-click -}
{- We can evaluate using C-c C-n -}

infixl 6 _+_


{- The underscore _ denote where the arguments should go
 This is a nice notation that easily allows for mixfix operators.
-}
{- Let us see another example -}

data Bool : Set where
        tt : Bool
        ff : Bool

if_then_else_ : {T : Set} -> Bool -> T -> T -> T
if tt then e1 else e2 = e1
if ff then e1 else e2 = e2










{- Let us define lists  -}
{- We declare the precedence and associativity of the operator ∷ -}
infixr 5 _∷_

{- UNICODE \:: = ∷ -}

data List (A : Set) : Set where
      [] : List A
      _∷_ : (x : A) → (xs : List A) → List A


{- Concatenate two lists -}
_++_ : {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷  xs ++ ys

{- C-c SPC checks the type of what I wrote in the shed -}
{- {A : Set} .. is an implicit parameter. It is filled by the compiler. -}
infixr 5 _++_

{- pointwise application -}
appL : {A B : Set} → List (A → B) → List A -> List B
appL [] [] = []
appL (x ∷ fs) [] = []
appL [] (x ∷ xs) = []
appL (f ∷ fs) (x ∷ xs) = f x ∷ appL fs xs

{- We define the Maybe type -}
data Maybe (A : Set) : Set where
     nothing : Maybe A
     just    : A → Maybe A

{- lookup for the nth element of a list. -}
_!!_ : {A : Set} → List A → Nat → Maybe A
[] !! n = nothing
(x ∷ xs) !! zero = just x
(x ∷ xs) !! suc n = xs !! suc n






{- Dynamic checks?
  We better put depedent types to work and use more precise types!
-}
{- We define vectors -}

data Vec (A : Set) : Nat → Set where
    []   : Vec A 0 
    _∷_  : {n : Nat} → (x : A) → (xs : Vec A n) → Vec A (1 + n)


{- Pointwise application for vectors -}
appV : {A B : Set}{n : Nat} → Vec (A → B) n → Vec A n → Vec B n
appV [] [] = []
appV (f ∷ fs) (x ∷ xs) = f x ∷ appV fs xs


{- the Fin n type is the type of naturals up to n-1, i.e. {0,1,...,n-1}  -}
data Fin : Nat -> Set where
  zero : {n : Nat} → Fin (suc n)
  suc : {n : Nat} → Fin n -> Fin (suc n)

{-
Fin 0   -> ∅    (empty set)
Fin 1   { zero }
Fin 2   { zero , suc (zero) }
Fin 3   { zero , suc zero , suc (suc (zero)) }
...
-}

{- lookup in a Vector -}
_!!v_ : {A : Set}{n : Nat} → Vec A n → Fin n → A
(x ∷ vs) !!v zero = x
(x ∷ vs) !!v suc i = vs !!v i

{- We statically ensure that application is well-defined! -}












-------------------------------------------------------------
{- Let's construct a compiler -}

data Expr : Set where
  val   : (v : Nat) ->  Expr
  boo   : (b : Bool) -> Expr
  _+'_  : (e1 e2 : Expr) ->  Expr
  if'_then_else_ : (e1 e2 e3 : Expr) -> Expr
  
data Val : Set where
  VN : Nat -> Val
  VB : Bool -> Val

eval_ : Expr -> Val
eval (val n) = VN n
eval (boo b) =  VB b 
eval (e1 +' e2) with eval e1 | eval e2 
(eval (e1 +' e2)) | VN x | VN x₁ = {!   !}
(eval (e1 +' e2)) | VN x | VB x₁ = {!   !}
(eval (e1 +' e2)) | VB x | VN x₁ = {!   !}
(eval (e1 +' e2)) | VB x | VB x₁ = {!   !}
-- eval (e1 +' e2) | VN y | VN y' = VN (y + y')
-- eval (e1 +' e2) | VN y | VB y' = {!!}
-- eval (e1 +' e2) | VB y | v2 = {!!}
eval (if' e1 then e2 else e3) = {!!}



-- Transitive Reflexive Closure of a Relation
data TRC {I : Set}(R : I -> I -> Set) : I -> I -> Set where
  []   : {i : I} -> TRC R i i
  _∷_ : {i j k : I}(x : R i j) -> (xs : TRC R j k) 
                 -> TRC R i k

_<>_ : forall {I R i j}{k : I} -> TRC R i j -> TRC R j k -> TRC R i k
[]       <> ys  = ys
(x ∷ xs)  <> ys  = x ∷ (xs <> ys)

infixr 5 _<>_ 

{- Language for a simple stack machine -}

data Inst : Nat → Nat → Set where
  PUSH  : ∀{n}(v : Nat) -> Inst n (1 + n)
  ADD   : ∀{n}          -> Inst (2 + n) (1 + n)

{- 
 PUSH pushes a value into the stack
 ADD pops the two values at the top of the stack, adds them, and pushes the result into the stack
-}

compile : ∀{n} → Expr → TRC Inst n (1 + n)  
compile (val v) = PUSH v ∷ []
compile (e1 +' e2) = compile e1 <> compile e2 <> ADD ∷ []
compile (boo b) = {!   !} 
compile (if' x then x₁ else x₂) = {!   !}


{- How to run the machine? -}

run : ∀{i j} → TRC Inst i j -> Vec Nat i -> Vec Nat j
run [] ns = ns
run (PUSH v ∷ is) ns = run is (v ∷ ns)
run (ADD ∷ is) (n ∷ m ∷ ns) = run is ((n + m) ∷ ns)


test : Vec Nat 1
test = run (compile ((val 2) +' (val 3))) [] 

{- C-C C-N evaluates (normalizes) a term -}

















{- https://github.com/mjaskelioff/USP2023 -}