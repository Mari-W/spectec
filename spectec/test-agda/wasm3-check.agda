{-# OPTIONS -WnoUnreachableClauses #-}
{- Preamble -}
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Bool using (Bool; true; false; not; _∧_; _∨_; if_then_else_)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; _>_; _≥_; _^_; _⊔_; _≡ᵇ_; _≤ᵇ_; _<ᵇ_)
open import Agda.Builtin.Nat using (_+_; _*_) renaming (_-_ to _–_)
open import Data.Nat using () renaming (_/_ to _/′_; _%_ to _%′_)
open import Data.String using (String) renaming (_==_ to eqString)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_)
open import Data.Maybe using (Maybe; nothing; just) renaming (map to mapMaybe; zipWith to maybeZipWith)
open import Data.List using (List; []; _∷_; fromMaybe; length; _++_; replicate; take; drop; zip; zipWith; map; upTo)
open import Data.Bool.ListAction using (any)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Relation.Binary.Pointwise using (Pointwise)

{- Type ascription -}
as : (A : Set) → A → A
as A x = x

{- Truth of booleans -}
is-true : Bool → Set
is-true b = b ≡ true

{- Boolean operations -}
_impliesᵇ_ : Bool → Bool → Bool
a impliesᵇ b = not a ∨ b

_=ᵇ_ : Bool → Bool → Bool
true =ᵇ b = b
false =ᵇ b = not b

{- Default values -}
record Inhabited (A : Set) : Set where
  field default-val : A
open Inhabited {{...}}

instance
  Inh-ℕ : Inhabited ℕ
  Inh-ℕ = record { default-val = 0 }

  Inh-Bool : Inhabited Bool
  Inh-Bool = record { default-val = false }

  Inh-⊤ : Inhabited ⊤
  Inh-⊤ = record { default-val = tt }

  Inh-String : Inhabited String
  Inh-String = record { default-val = "" }

  Inh-List : {A : Set} → Inhabited (List A)
  Inh-List = record { default-val = [] }

  Inh-Maybe : {A : Set} → Inhabited (Maybe A)
  Inh-Maybe = record { default-val = nothing }

  Inh-× : {A B : Set} → {{Inhabited A}} → {{Inhabited B}} → Inhabited (A × B)
  Inh-× = record { default-val = (default-val , default-val) }

{- Boolean equality -}
record HasEq (A : Set) : Set where
  field _=?_ : A → A → Bool
open HasEq {{...}}

_≠?_ : {A : Set} → {{HasEq A}} → A → A → Bool
x ≠? y = not (x =? y)

eq-List-fun : {A : Set} → {{HasEq A}} → List A → List A → Bool
eq-List-fun [] [] = true
eq-List-fun (x ∷ xs) (y ∷ ys) = (x =? y) ∧ eq-List-fun xs ys
eq-List-fun _ _ = false

eq-Maybe-fun : {A : Set} → {{HasEq A}} → Maybe A → Maybe A → Bool
eq-Maybe-fun nothing nothing = true
eq-Maybe-fun (just x) (just y) = x =? y
eq-Maybe-fun _ _ = false

instance
  Eq-ℕ : HasEq ℕ
  Eq-ℕ = record { _=?_ = _≡ᵇ_ }

  Eq-Bool : HasEq Bool
  Eq-Bool = record { _=?_ = _=ᵇ_ }

  Eq-String : HasEq String
  Eq-String = record { _=?_ = eqString }

  Eq-List : {A : Set} → {{HasEq A}} → HasEq (List A)
  Eq-List = record { _=?_ = eq-List-fun }

  Eq-Maybe : {A : Set} → {{HasEq A}} → HasEq (Maybe A)
  Eq-Maybe = record { _=?_ = eq-Maybe-fun }

  Eq-× : {A B : Set} → {{HasEq A}} → {{HasEq B}} → HasEq (A × B)
  Eq-× = record { _=?_ = λ where (a , b) (a' , b') → (a =? a') ∧ (b =? b') }

_∈ᵇ_ : {A : Set} → {{HasEq A}} → A → List A → Bool
x ∈ᵇ xs = any (λ y → x =? y) xs

{- Boolean number comparisons -}
_<?_ : ℕ → ℕ → Bool
a <? b = a <ᵇ b

_>?_ : ℕ → ℕ → Bool
a >? b = b <ᵇ a

_≤?_ : ℕ → ℕ → Bool
a ≤? b = a ≤ᵇ b

_≥?_ : ℕ → ℕ → Bool
a ≥? b = b ≤ᵇ a

{- Arithmetic operations (total: division by zero yields zero) -}
_/_ : ℕ → ℕ → ℕ
a / zero = 0
a / suc b = a /′ suc b

_%_ : ℕ → ℕ → ℕ
a % zero = 0
a % suc b = a %′ suc b

{- Numeric type coercions -}
record Coerce (A B : Set) : Set where
  field coerce : A → B
open Coerce {{...}}

instance
  Coerce-ℕ : Coerce ℕ ℕ
  Coerce-ℕ = record { coerce = λ n → n }

  Coerce-Maybe : {A B : Set} → {{Coerce A B}} → Coerce (Maybe A) (Maybe B)
  Coerce-Maybe = record { coerce = mapMaybe coerce }

  Coerce-List : {A B : Set} → {{Coerce A B}} → Coerce (List A) (List B)
  Coerce-List = record { coerce = map coerce }

{- Record composition -}
record HasAppend (A : Set) : Set where
  field append : A → A → A
open HasAppend {{...}}

_⧺_ : {A : Set} → {{HasAppend A}} → A → A → A
_⧺_ = append
infixr 5 _⧺_

maybe-append : {A : Set} → Maybe A → Maybe A → Maybe A
maybe-append (just x) _ = just x
maybe-append nothing y = y

instance
  Append-List : {A : Set} → HasAppend (List A)
  Append-List = record { append = _++_ }

  Append-Maybe : {A : Set} → HasAppend (Maybe A)
  Append-Maybe = record { append = maybe-append }

  Append-ℕ : HasAppend ℕ
  Append-ℕ = record { append = _+_ }

{- List operations -}
slice : {A : Set} → List A → ℕ → ℕ → List A
slice xs i n = take n (drop i xs)

slice-update : {A : Set} → List A → ℕ → ℕ → List A → List A
slice-update xs i n u = take i xs ++ take n u ++ drop (i + n) xs

modify : {A : Set} → List A → ℕ → (A → A) → List A
modify (x ∷ xs) zero    f = f x ∷ xs
modify (x ∷ xs) (suc n) f = x ∷ modify xs n f
modify [] _ _ = []

mkseq : {A : Set} → (ℕ → A) → ℕ → List A
mkseq f n = map f (upTo n)

unsnoc-cons : {A : Set} → A → List A → (List A × A)
unsnoc-cons x [] = ([] , x)
unsnoc-cons x (y ∷ ys) = let (zs , z) = unsnoc-cons y ys in ((x ∷ zs) , z)

zipWith₃ : {A B C D : Set} → (A → B → C → D) → List A → List B → List C → List D
zipWith₃ f (x ∷ xs) (y ∷ ys) (z ∷ zs) = f x y z ∷ zipWith₃ f xs ys zs
zipWith₃ _ _ _ _ = []

maybeZipWith₃ : {A B C D : Set} → (A → B → C → D) → Maybe A → Maybe B → Maybe C → Maybe D
maybeZipWith₃ f (just x) (just y) (just z) = just (f x y z)
maybeZipWith₃ _ _ _ _ = nothing

{- Total lookup and unwrapping (default values off-domain; the generated
   side conditions guarantee on-domain use) -}
_[_]! : {A : Set} → {{Inhabited A}} → (xs : List A) → (i : ℕ) → A
([] [ _ ]!) = default-val
((x ∷ xs) [ zero ]!)  = x
((x ∷ xs) [ suc i ]!) = xs [ i ]!

unwrap! : {A : Set} → {{Inhabited A}} → Maybe A → A
unwrap! (just a) = a
unwrap! nothing = default-val

{- Iterated premises (inductive: length-forcing, with induction principles) -}
Forall : {A : Set} → (A → Set) → List A → Set
Forall = All

Forall₂ : {A B : Set} → (A → B → Set) → List A → List B → Set
Forall₂ = Pointwise

data Forall₃ {A B C : Set} (R : A → B → C → Set) :
             List A → List B → List C → Set where
  []  : Forall₃ R [] [] []
  _∷_ : ∀ {x y z xs ys zs} → R x y z → Forall₃ R xs ys zs →
        Forall₃ R (x ∷ xs) (y ∷ ys) (z ∷ zs)

Foralli : {A : Set} → (ℕ → A → Set) → List A → Set
Foralli f xs = Pointwise f (upTo (length xs)) xs

holds-upto : (ℕ → Set) → ℕ → Set
holds-upto P n = All P (upTo n)

{- Generated Code -}

{- Type Alias Definition at: ../specification/wasm-3.0/0.1-aux.vars.spectec:5.1-5.32 -}
N : Set
N = ℕ

{- Type Alias Definition at: ../specification/wasm-3.0/0.1-aux.vars.spectec:6.1-6.32 -}
M : Set
M = ℕ

{- Type Alias Definition at: ../specification/wasm-3.0/0.1-aux.vars.spectec:7.1-7.32 -}
K : Set
K = ℕ

{- Type Alias Definition at: ../specification/wasm-3.0/0.1-aux.vars.spectec:8.1-8.32 -}
n : Set
n = ℕ

{- Type Alias Definition at: ../specification/wasm-3.0/0.1-aux.vars.spectec:9.1-9.32 -}
m : Set
m = ℕ

{- Auxiliary Definition at: ../specification/wasm-3.0/0.2-aux.num.spectec:5.1-5.25 -}
{-# TERMINATING #-}
min : (nat : ℕ) (nat-0 : ℕ) → ℕ
min i j = (if (i ≤? j) then i else j)

{- Auxiliary Definition at: ../specification/wasm-3.0/0.2-aux.num.spectec:9.1-9.56 -}
{-# TERMINATING #-}
sum : (var-0-lst : (List ℕ)) → ℕ
sum [] = 0
sum (v-n ∷ n'-lst) = (v-n + (sum n'-lst))
sum var-0-lst = default-val

{- Auxiliary Definition at: ../specification/wasm-3.0/0.2-aux.num.spectec:13.1-13.57 -}
{-# TERMINATING #-}
prod : (var-0-lst : (List ℕ)) → ℕ
prod [] = 1
prod (v-n ∷ n'-lst) = (v-n * (prod n'-lst))
prod var-0-lst = default-val

{- Auxiliary Definition at: ../specification/wasm-3.0/0.3-aux.seq.spectec:7.1-7.58 -}
{-# TERMINATING #-}
opt- : (X : Set) (var-0-lst : (List X)) → (Maybe (Maybe X))
opt- X [] = (just nothing)
opt- X (w ∷ []) = (just (just w))
opt- X x1 = nothing

{- Auxiliary Definition at: ../specification/wasm-3.0/0.3-aux.seq.spectec:14.1-14.82 -}
{-# TERMINATING #-}
concat- : (X : Set) (var-0-lst-lst : (List (List X))) → (List X)
concat- X [] = []
concat- X (w-lst ∷ w'-lst-lst) = (w-lst ++ (concat- X w'-lst-lst))
concat- X var-0-lst-lst = []

{- Auxiliary Definition at: ../specification/wasm-3.0/0.3-aux.seq.spectec:18.1-18.89 -}
{-# TERMINATING #-}
concatn- : (X : Set) (var-0-lst-lst : (List (List X))) (nat : ℕ) → (List X)
concatn- X [] v-n = []
concatn- X (w-lst ∷ w'-lst-lst) v-n = (w-lst ++ (concatn- X w'-lst-lst v-n))
concatn- X var-0-lst-lst nat = []

{- Auxiliary Definition at: ../specification/wasm-3.0/0.3-aux.seq.spectec:22.1-22.58 -}
{-# TERMINATING #-}
concatopt- : (X : Set) (var-0-opt-lst : (List (Maybe X))) → (List X)
concatopt- X [] = []
concatopt- X (w-opt ∷ w'-opt-lst) = ((fromMaybe w-opt) ++ (concat- X (map (λ (w'-opt : (Maybe X)) → (fromMaybe w'-opt)) w'-opt-lst)))
concatopt- X var-0-opt-lst = []

{- Axiom Definition at: ../specification/wasm-3.0/0.3-aux.seq.spectec:26.1-26.39 -}
postulate inv-concat- : ∀ (X : Set) (var-0-lst : (List X)) → (List (List X))

{- Axiom Definition at: ../specification/wasm-3.0/0.3-aux.seq.spectec:29.1-29.45 -}
postulate inv-concatn- : ∀ (X : Set) (nat : ℕ) (var-0-lst : (List X)) → (List (List X))

{- Auxiliary Definition at: ../specification/wasm-3.0/0.3-aux.seq.spectec:35.1-35.78 -}
{-# TERMINATING #-}
disjoint- : (X : Set) {{_ : HasEq X}} (var-0-lst : (List X)) → Bool
disjoint- X [] = true
disjoint- X (w ∷ w'-lst) = ((not (w ∈ᵇ w'-lst)) ∧ (disjoint- X w'-lst))
disjoint- X var-0-lst = default-val

{- Auxiliary Definition at: ../specification/wasm-3.0/0.3-aux.seq.spectec:40.1-40.38 -}
{-# TERMINATING #-}
setminus1- : (X : Set) {{_ : HasEq X}} (X-0 : X) (var-0-lst : (List X)) → (List X)
setminus1- X w [] = (w ∷ [])
setminus1- X w (w-1 ∷ w'-lst) = (if (w =? w-1) then [] else (setminus1- X w w'-lst))
setminus1- X X-0 var-0-lst = []

{- Auxiliary Definition at: ../specification/wasm-3.0/0.3-aux.seq.spectec:39.1-39.56 -}
{-# TERMINATING #-}
setminus- : (X : Set) {{_ : HasEq X}} (var-0-lst : (List X)) (var-1-lst : (List X)) → (List X)
setminus- X [] w-lst = []
setminus- X (w-1 ∷ w'-lst) w-lst = ((setminus1- X w-1 w-lst) ++ (setminus- X w'-lst w-lst))
setminus- X var-0-lst var-1-lst = []

{- Auxiliary Definition at: ../specification/wasm-3.0/0.3-aux.seq.spectec:51.1-51.46 -}
{-# TERMINATING #-}
setproduct2- : (X : Set) (X-0 : X) (var-0-lst-lst : (List (List X))) → (List (List X))
setproduct2- X w-1 [] = []
setproduct2- X w-1 (w'-lst ∷ w-lst-lst) = ((((w-1 ∷ []) ++ w'-lst) ∷ []) ++ (setproduct2- X w-1 w-lst-lst))
setproduct2- X X-0 var-0-lst-lst = []

{- Auxiliary Definition at: ../specification/wasm-3.0/0.3-aux.seq.spectec:50.1-50.47 -}
{-# TERMINATING #-}
setproduct1- : (X : Set) (var-0-lst : (List X)) (var-1-lst-lst : (List (List X))) → (List (List X))
setproduct1- X [] w-lst-lst = []
setproduct1- X (w-1 ∷ w'-lst) w-lst-lst = ((setproduct2- X w-1 w-lst-lst) ++ (setproduct1- X w'-lst w-lst-lst))
setproduct1- X var-0-lst var-1-lst-lst = []

{- Auxiliary Definition at: ../specification/wasm-3.0/0.3-aux.seq.spectec:49.1-49.84 -}
{-# TERMINATING #-}
setproduct- : (X : Set) (var-0-lst-lst : (List (List X))) → (List (List X))
setproduct- X [] = ([] ∷ [])
setproduct- X (w-1-lst ∷ w-lst-lst) = (setproduct1- X w-1-lst (setproduct- X w-lst-lst))
setproduct- X var-0-lst-lst = []

{- Axiom Definition at: ../specification/wasm-3.0/1.0-syntax.profiles.spectec:5.1-5.29 -}
postulate ND : Bool

{- Inductive Type Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:7.1-7.37 -}
data bit : Set where
  mk-bit : (i : ℕ) → bit {- 1 premise(s) dropped -}

{- Inductive Type Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:8.1-8.50 -}
data byte : Set where
  mk-byte : (i : ℕ) → byte {- 1 premise(s) dropped -}

instance
  inh-byte : Inhabited byte
  inh-byte = record { default-val = (mk-byte (default-val)) }

{- Auxiliary Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:8.1-8.50 -}
{-# TERMINATING #-}
proj-byte-0 : (x : byte) → (ℕ)
proj-byte-0 (mk-byte v-num-0) = (v-num-0)
proj-byte-0 x = (default-val)

instance
  proj-byte-0-coercion : Coerce byte (ℕ)
  proj-byte-0-coercion = record { coerce = proj-byte-0 }

{- Inductive Type Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:10.1-11.25 -}
data uN-fam0 (v-N : N) : Set where
  mk-uN : (i : ℕ) → uN-fam0 v-N {- 1 premise(s) dropped -}

instance
  inh-uN-fam0 : {v-N : N} → Inhabited (uN-fam0 v-N)
  inh-uN-fam0 {v-N} = record { default-val = (mk-uN (default-val)) }

eq-uN-fam0-fun : {v-N : N} → (uN-fam0 v-N) → (uN-fam0 v-N) → Bool
eq-uN-fam0-fun (mk-uN x0) (mk-uN y0) = (x0 =? y0)
instance
  haseq-uN-fam0 : {v-N : N} → HasEq (uN-fam0 v-N)
  haseq-uN-fam0 = record { _=?_ = eq-uN-fam0-fun }

uN : (v-N : N) → Set
uN v-N = uN-fam0 v-N
uN _ = ⊤

inh-uN-fun : (v-N : N) → Inhabited (uN v-N)
inh-uN-fun v-N = record { default-val = default-val }

{- Auxiliary Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:10.1-11.25 -}
{-# TERMINATING #-}
proj-uN-0 : (v-N : N) (x : (uN-fam0 (v-N))) → (ℕ)
proj-uN-0 v-N (mk-uN v-num-0) = (v-num-0)
proj-uN-0 v-N x = (default-val)

instance
  proj-uN-0-coercion : {v-N : N} → Coerce (uN-fam0 (v-N)) (ℕ)
  proj-uN-0-coercion = record { coerce = proj-uN-0 _ }

{- Inductive Type Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:12.1-13.50 -}
data sN-fam0 (v-N : N) : Set where
  mk-sN : (i : ℕ) → sN-fam0 v-N {- 1 premise(s) dropped -}

sN : (v-N : N) → Set
sN v-N = sN-fam0 v-N
sN _ = ⊤

{- Auxiliary Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:12.1-13.50 -}
{-# TERMINATING #-}
proj-sN-0 : (v-N : N) (x : (sN-fam0 (v-N))) → (ℕ)
proj-sN-0 v-N (mk-sN v-num-0) = (v-num-0)
proj-sN-0 v-N x = (default-val)

instance
  proj-sN-0-coercion : {v-N : N} → Coerce (sN-fam0 (v-N)) (ℕ)
  proj-sN-0-coercion = record { coerce = proj-sN-0 _ }

{- Type Alias Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:14.1-15.8 -}
iN : (v-N : N) → Set
iN v-N = (uN-fam0 (v-N))
iN _ = ⊤

inh-iN-fun : (v-N : N) → Inhabited (iN v-N)
inh-iN-fun v-N = record { default-val = (Inhabited.default-val (inh-uN-fun v-N)) }

{- Type Alias Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:17.1-17.20 -}
u8 : Set
u8 = (uN-fam0 (8))

{- Type Alias Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:18.1-18.21 -}
u16 : Set
u16 = (uN-fam0 (16))

{- Type Alias Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:19.1-19.21 -}
u31 : Set
u31 = (uN-fam0 (31))

{- Type Alias Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:20.1-20.21 -}
u32 : Set
u32 = (uN-fam0 (32))

{- Type Alias Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:21.1-21.21 -}
u64 : Set
u64 = (uN-fam0 (64))

{- Type Alias Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:22.1-22.21 -}
s33 : Set
s33 = (sN-fam0 (33))

{- Type Alias Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:23.1-23.21 -}
i32 : Set
i32 = (uN-fam0 (32))

{- Type Alias Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:24.1-24.21 -}
i64 : Set
i64 = (uN-fam0 (64))

{- Type Alias Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:25.1-25.23 -}
i128 : Set
i128 = (uN-fam0 (128))

{- Auxiliary Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:32.1-32.35 -}
{-# TERMINATING #-}
signif : (v-N : N) → (Maybe ℕ)
signif (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (zero))))))))))))))))))))))))))))))))) = (just 23)
signif (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (zero))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = (just 52)
signif x0 = nothing

{- Auxiliary Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:36.1-36.34 -}
{-# TERMINATING #-}
expon : (v-N : N) → (Maybe ℕ)
expon (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (zero))))))))))))))))))))))))))))))))) = (just 8)
expon (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (zero))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = (just 11)
expon x0 = nothing

{- Auxiliary Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:40.1-40.47 -}
{-# TERMINATING #-}
fun-M : (v-N : N) → ℕ
fun-M v-N = (unwrap! (signif v-N))

{- Auxiliary Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:43.1-43.47 -}
{-# TERMINATING #-}
E : (v-N : N) → ℕ
E v-N = (unwrap! (expon v-N))

{- Type Alias Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:50.1-50.47 -}
exp : Set
exp = ℕ

{- Inductive Type Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:51.1-55.84 -}
data fNmag-fam0 (v-N : N) : Set where
  NORM : (v-m : m) → (v-exp : exp) → fNmag-fam0 v-N {- 1 premise(s) dropped -}
  SUBNORM : (v-m : m) → fNmag-fam0 v-N {- 1 premise(s) dropped -}
  INF : fNmag-fam0 v-N
  NAN : (v-m : m) → fNmag-fam0 v-N {- 1 premise(s) dropped -}

instance
  inh-fNmag-fam0 : {v-N : N} → Inhabited (fNmag-fam0 v-N)
  inh-fNmag-fam0 {v-N} = record { default-val = (NORM (default-val) (default-val)) }

eq-fNmag-fam0-fun : {v-N : N} → (fNmag-fam0 v-N) → (fNmag-fam0 v-N) → Bool
eq-fNmag-fam0-fun (NORM x0 x1) (NORM y0 y1) = (x0 =? y0) ∧ (x1 =? y1)
eq-fNmag-fam0-fun (SUBNORM x0) (SUBNORM y0) = (x0 =? y0)
eq-fNmag-fam0-fun INF INF = true
eq-fNmag-fam0-fun (NAN x0) (NAN y0) = (x0 =? y0)
eq-fNmag-fam0-fun _ _ = false
instance
  haseq-fNmag-fam0 : {v-N : N} → HasEq (fNmag-fam0 v-N)
  haseq-fNmag-fam0 = record { _=?_ = eq-fNmag-fam0-fun }

fNmag : (v-N : N) → Set
fNmag v-N = fNmag-fam0 v-N
fNmag _ = ⊤

inh-fNmag-fun : (v-N : N) → Inhabited (fNmag v-N)
inh-fNmag-fun v-N = record { default-val = default-val }

{- Inductive Type Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:46.1-48.35 -}
data fN-fam0 (v-N : N) : Set where
  POS : (_ : (fNmag-fam0 (v-N))) → fN-fam0 v-N
  NEG : (_ : (fNmag-fam0 (v-N))) → fN-fam0 v-N

instance
  inh-fN-fam0 : {v-N : N} → Inhabited (fN-fam0 v-N)
  inh-fN-fam0 {v-N} = record { default-val = (POS ((Inhabited.default-val (inh-fNmag-fun v-N)))) }

eq-fN-fam0-fun : {v-N : N} → (fN-fam0 v-N) → (fN-fam0 v-N) → Bool
eq-fN-fam0-fun (POS x0) (POS y0) = (x0 =? y0)
eq-fN-fam0-fun (NEG x0) (NEG y0) = (x0 =? y0)
eq-fN-fam0-fun _ _ = false
instance
  haseq-fN-fam0 : {v-N : N} → HasEq (fN-fam0 v-N)
  haseq-fN-fam0 = record { _=?_ = eq-fN-fam0-fun }

fN : (v-N : N) → Set
fN v-N = fN-fam0 v-N
fN _ = ⊤

inh-fN-fun : (v-N : N) → Inhabited (fN v-N)
inh-fN-fun v-N = record { default-val = default-val }

{- Type Alias Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:57.1-57.21 -}
f32 : Set
f32 = (fN-fam0 (32))

{- Type Alias Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:58.1-58.21 -}
f64 : Set
f64 = (fN-fam0 (64))

{- Auxiliary Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:60.1-60.39 -}
{-# TERMINATING #-}
fzero : (v-N : N) → (fN-fam0 (v-N))
fzero v-N = (POS (SUBNORM 0))

{- Auxiliary Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:63.1-63.45 -}
{-# TERMINATING #-}
fnat : (v-N : N) (nat : ℕ) → (fN-fam0 (v-N))
fnat v-N v-n = (POS (NORM v-n (coerce {B = ℕ} 0)))

{- Auxiliary Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:66.1-66.39 -}
{-# TERMINATING #-}
fone : (v-N : N) → (fN-fam0 (v-N))
fone v-N = (POS (NORM 1 (coerce {B = ℕ} 0)))

{- Auxiliary Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:69.1-69.21 -}
{-# TERMINATING #-}
canon- : (v-N : N) → ℕ
canon- v-N = (2 ^ (coerce {B = ℕ} ((coerce {B = ℕ} (unwrap! (signif v-N))) – (coerce {B = ℕ} 1))))

{- Type Alias Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:75.1-76.8 -}
vN : (v-N : N) → Set
vN v-N = (uN-fam0 (v-N))
vN _ = ⊤

inh-vN-fun : (v-N : N) → Inhabited (vN v-N)
inh-vN-fun v-N = record { default-val = (Inhabited.default-val (inh-uN-fun v-N)) }

{- Type Alias Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:78.1-78.23 -}
v128 : Set
v128 = (uN-fam0 (128))

{- Inductive Type Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:84.1-84.49 -}
data list-fam0 (X : Set) : Set where
  mk-list : (X-lst : (List X)) → list-fam0 X {- 1 premise(s) dropped -}

instance
  inh-list-fam0 : {X : Set} → Inhabited (list-fam0 X)
  inh-list-fam0 {X} = record { default-val = (mk-list ([])) }

eq-list-fam0-fun : {X : Set} → {{HasEq X}} → (list-fam0 X) → (list-fam0 X) → Bool
eq-list-fam0-fun (mk-list x0) (mk-list y0) = (x0 =? y0)
instance
  haseq-list-fam0 : {X : Set} → {{HasEq X}} → HasEq (list-fam0 X)
  haseq-list-fam0 = record { _=?_ = eq-list-fam0-fun }

list : (X : Set) → Set
list X = list-fam0 X
list _ = ⊤

inh-list-fun : (X : Set) → Inhabited (list X)
inh-list-fun X = record { default-val = default-val }

{- Auxiliary Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:84.1-84.49 -}
{-# TERMINATING #-}
proj-list-0 : (X : Set) (x : (list-fam0 (X))) → ((List X))
proj-list-0 X (mk-list v-X-list-0) = (v-X-list-0)
proj-list-0 X x = ([])

instance
  proj-list-0-coercion : {X : Set} → Coerce (list-fam0 (X)) ((List X))
  proj-list-0-coercion = record { coerce = proj-list-0 _ }

{- Inductive Type Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:89.1-89.85 -}
data char : Set where
  mk-char : (i : ℕ) → char {- 1 premise(s) dropped -}

instance
  inh-char : Inhabited char
  inh-char = record { default-val = (mk-char (default-val)) }

eq-char-fun : char → char → Bool
eq-char-fun (mk-char x0) (mk-char y0) = (x0 =? y0)
instance
  haseq-char : HasEq char
  haseq-char = record { _=?_ = eq-char-fun }

{- Auxiliary Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:89.1-89.85 -}
{-# TERMINATING #-}
proj-char-0 : (x : char) → (ℕ)
proj-char-0 (mk-char v-num-0) = (v-num-0)
proj-char-0 x = (default-val)

instance
  proj-char-0-coercion : Coerce char (ℕ)
  proj-char-0-coercion = record { coerce = proj-char-0 }

{- Auxiliary Definition at: ../specification/wasm-3.0/5.1-binary.values.spectec:48.1-48.39 -}
postulate cont : ∀ (v-byte : byte) → ℕ

{- Auxiliary Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:91.1-91.25 -}
postulate utf8 : ∀ (var-0-lst : (List char)) → (List byte)

{- Inductive Type Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:93.1-93.70 -}
data name : Set where
  mk-name : (char-lst : (List char)) → name {- 1 premise(s) dropped -}

instance
  inh-name : Inhabited name
  inh-name = record { default-val = (mk-name ([])) }

eq-name-fun : name → name → Bool
eq-name-fun (mk-name x0) (mk-name y0) = (x0 =? y0)
instance
  haseq-name : HasEq name
  haseq-name = record { _=?_ = eq-name-fun }

{- Auxiliary Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:93.1-93.70 -}
{-# TERMINATING #-}
proj-name-0 : (x : name) → ((List char))
proj-name-0 (mk-name v-char-list-0) = (v-char-list-0)
proj-name-0 x = ([])

instance
  proj-name-0-coercion : Coerce name ((List char))
  proj-name-0-coercion = record { coerce = proj-name-0 }

{- Type Alias Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:100.1-100.36 -}
idx : Set
idx = u32

{- Type Alias Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:101.1-101.44 -}
laneidx : Set
laneidx = u8

{- Type Alias Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:103.1-103.45 -}
typeidx : Set
typeidx = idx

{- Type Alias Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:104.1-104.49 -}
funcidx : Set
funcidx = idx

{- Type Alias Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:105.1-105.49 -}
globalidx : Set
globalidx = idx

{- Type Alias Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:106.1-106.47 -}
tableidx : Set
tableidx = idx

{- Type Alias Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:107.1-107.46 -}
memidx : Set
memidx = idx

{- Type Alias Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:108.1-108.43 -}
tagidx : Set
tagidx = idx

{- Type Alias Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:109.1-109.45 -}
elemidx : Set
elemidx = idx

{- Type Alias Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:110.1-110.45 -}
dataidx : Set
dataidx = idx

{- Type Alias Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:111.1-111.47 -}
labelidx : Set
labelidx = idx

{- Type Alias Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:112.1-112.47 -}
localidx : Set
localidx = idx

{- Type Alias Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:113.1-113.47 -}
fieldidx : Set
fieldidx = idx

{- Inductive Type Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:115.1-116.79 -}
data externidx : Set where
  FUNC : (v-funcidx : funcidx) → externidx
  GLOBAL : (v-globalidx : globalidx) → externidx
  TABLE : (v-tableidx : tableidx) → externidx
  MEM : (v-memidx : memidx) → externidx
  TAG : (v-tagidx : tagidx) → externidx

instance
  inh-externidx : Inhabited externidx
  inh-externidx = record { default-val = (FUNC (default-val)) }

{- Auxiliary Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:129.1-129.86 -}
{-# TERMINATING #-}
funcsxx : (var-0-lst : (List externidx)) → (List typeidx)
funcsxx [] = []
funcsxx ((FUNC x) ∷ xx-lst) = ((x ∷ []) ++ (funcsxx xx-lst))
funcsxx (v-externidx ∷ xx-lst) = (funcsxx xx-lst)
funcsxx var-0-lst = []

{- Auxiliary Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:130.1-130.88 -}
{-# TERMINATING #-}
globalsxx : (var-0-lst : (List externidx)) → (List globalidx)
globalsxx [] = []
globalsxx ((GLOBAL x) ∷ xx-lst) = ((x ∷ []) ++ (globalsxx xx-lst))
globalsxx (v-externidx ∷ xx-lst) = (globalsxx xx-lst)
globalsxx var-0-lst = []

{- Auxiliary Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:131.1-131.87 -}
{-# TERMINATING #-}
tablesxx : (var-0-lst : (List externidx)) → (List tableidx)
tablesxx [] = []
tablesxx ((TABLE x) ∷ xx-lst) = ((x ∷ []) ++ (tablesxx xx-lst))
tablesxx (v-externidx ∷ xx-lst) = (tablesxx xx-lst)
tablesxx var-0-lst = []

{- Auxiliary Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:132.1-132.85 -}
{-# TERMINATING #-}
memsxx : (var-0-lst : (List externidx)) → (List memidx)
memsxx [] = []
memsxx ((MEM x) ∷ xx-lst) = ((x ∷ []) ++ (memsxx xx-lst))
memsxx (v-externidx ∷ xx-lst) = (memsxx xx-lst)
memsxx var-0-lst = []

{- Auxiliary Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:133.1-133.85 -}
{-# TERMINATING #-}
tagsxx : (var-0-lst : (List externidx)) → (List tagidx)
tagsxx [] = []
tagsxx ((TAG x) ∷ xx-lst) = ((x ∷ []) ++ (tagsxx xx-lst))
tagsxx (v-externidx ∷ xx-lst) = (tagsxx xx-lst)
tagsxx var-0-lst = []

{- Record Creation Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:158.1-169.4 -}
record free : Set where
  constructor mk-free
  field
    TYPES : (List typeidx)
    FUNCS : (List funcidx)
    GLOBALS : (List globalidx)
    TABLES : (List tableidx)
    MEMS : (List memidx)
    ELEMS : (List elemidx)
    DATAS : (List dataidx)
    LOCALS : (List localidx)
    LABELS : (List labelidx)
    TAGS : (List tagidx)
open free

instance
  append-free : HasAppend (free)
  append-free = record { append = λ arg1 arg2 → record {
    TYPES = TYPES arg1 ⧺ TYPES arg2 ;
    FUNCS = FUNCS arg1 ⧺ FUNCS arg2 ;
    GLOBALS = GLOBALS arg1 ⧺ GLOBALS arg2 ;
    TABLES = TABLES arg1 ⧺ TABLES arg2 ;
    MEMS = MEMS arg1 ⧺ MEMS arg2 ;
    ELEMS = ELEMS arg1 ⧺ ELEMS arg2 ;
    DATAS = DATAS arg1 ⧺ DATAS arg2 ;
    LOCALS = LOCALS arg1 ⧺ LOCALS arg2 ;
    LABELS = LABELS arg1 ⧺ LABELS arg2 ;
    TAGS = TAGS arg1 ⧺ TAGS arg2 } }

instance
  inh-free : Inhabited free
  inh-free = record { default-val = record { TYPES = default-val ; FUNCS = default-val ; GLOBALS = default-val ; TABLES = default-val ; MEMS = default-val ; ELEMS = default-val ; DATAS = default-val ; LOCALS = default-val ; LABELS = default-val ; TAGS = default-val } }

{- Auxiliary Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:172.1-172.28 -}
{-# TERMINATING #-}
free-opt : (var-0-opt : (Maybe free)) → free
free-opt nothing = record { TYPES = [] ; FUNCS = [] ; GLOBALS = [] ; TABLES = [] ; MEMS = [] ; ELEMS = [] ; DATAS = [] ; LOCALS = [] ; LABELS = [] ; TAGS = [] }
free-opt (just v-free) = v-free
free-opt var-0-opt = default-val

{- Auxiliary Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:173.1-173.29 -}
{-# TERMINATING #-}
free-list : (var-0-lst : (List free)) → free
free-list [] = record { TYPES = [] ; FUNCS = [] ; GLOBALS = [] ; TABLES = [] ; MEMS = [] ; ELEMS = [] ; DATAS = [] ; LOCALS = [] ; LABELS = [] ; TAGS = [] }
free-list (v-free ∷ free'-lst) = (v-free ⧺ (free-list free'-lst))
free-list var-0-lst = default-val

{- Auxiliary Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:182.1-182.34 -}
{-# TERMINATING #-}
free-typeidx : (v-typeidx : typeidx) → free
free-typeidx v-typeidx = record { TYPES = (v-typeidx ∷ []) ; FUNCS = [] ; GLOBALS = [] ; TABLES = [] ; MEMS = [] ; ELEMS = [] ; DATAS = [] ; LOCALS = [] ; LABELS = [] ; TAGS = [] }

{- Auxiliary Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:183.1-183.34 -}
{-# TERMINATING #-}
free-funcidx : (v-funcidx : funcidx) → free
free-funcidx v-funcidx = record { TYPES = [] ; FUNCS = (v-funcidx ∷ []) ; GLOBALS = [] ; TABLES = [] ; MEMS = [] ; ELEMS = [] ; DATAS = [] ; LOCALS = [] ; LABELS = [] ; TAGS = [] }

{- Auxiliary Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:184.1-184.38 -}
{-# TERMINATING #-}
free-globalidx : (v-globalidx : globalidx) → free
free-globalidx v-globalidx = record { TYPES = [] ; FUNCS = [] ; GLOBALS = (v-globalidx ∷ []) ; TABLES = [] ; MEMS = [] ; ELEMS = [] ; DATAS = [] ; LOCALS = [] ; LABELS = [] ; TAGS = [] }

{- Auxiliary Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:185.1-185.36 -}
{-# TERMINATING #-}
free-tableidx : (v-tableidx : tableidx) → free
free-tableidx v-tableidx = record { TYPES = [] ; FUNCS = [] ; GLOBALS = [] ; TABLES = (v-tableidx ∷ []) ; MEMS = [] ; ELEMS = [] ; DATAS = [] ; LOCALS = [] ; LABELS = [] ; TAGS = [] }

{- Auxiliary Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:186.1-186.32 -}
{-# TERMINATING #-}
free-memidx : (v-memidx : memidx) → free
free-memidx v-memidx = record { TYPES = [] ; FUNCS = [] ; GLOBALS = [] ; TABLES = [] ; MEMS = (v-memidx ∷ []) ; ELEMS = [] ; DATAS = [] ; LOCALS = [] ; LABELS = [] ; TAGS = [] }

{- Auxiliary Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:187.1-187.34 -}
{-# TERMINATING #-}
free-elemidx : (v-elemidx : elemidx) → free
free-elemidx v-elemidx = record { TYPES = [] ; FUNCS = [] ; GLOBALS = [] ; TABLES = [] ; MEMS = [] ; ELEMS = (v-elemidx ∷ []) ; DATAS = [] ; LOCALS = [] ; LABELS = [] ; TAGS = [] }

{- Auxiliary Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:188.1-188.34 -}
{-# TERMINATING #-}
free-dataidx : (v-dataidx : dataidx) → free
free-dataidx v-dataidx = record { TYPES = [] ; FUNCS = [] ; GLOBALS = [] ; TABLES = [] ; MEMS = [] ; ELEMS = [] ; DATAS = (v-dataidx ∷ []) ; LOCALS = [] ; LABELS = [] ; TAGS = [] }

{- Auxiliary Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:189.1-189.36 -}
{-# TERMINATING #-}
free-localidx : (v-localidx : localidx) → free
free-localidx v-localidx = record { TYPES = [] ; FUNCS = [] ; GLOBALS = [] ; TABLES = [] ; MEMS = [] ; ELEMS = [] ; DATAS = [] ; LOCALS = (v-localidx ∷ []) ; LABELS = [] ; TAGS = [] }

{- Auxiliary Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:190.1-190.36 -}
{-# TERMINATING #-}
free-labelidx : (v-labelidx : labelidx) → free
free-labelidx v-labelidx = record { TYPES = [] ; FUNCS = [] ; GLOBALS = [] ; TABLES = [] ; MEMS = [] ; ELEMS = [] ; DATAS = [] ; LOCALS = [] ; LABELS = (v-labelidx ∷ []) ; TAGS = [] }

{- Auxiliary Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:192.1-192.32 -}
{-# TERMINATING #-}
free-tagidx : (v-tagidx : tagidx) → free
free-tagidx v-tagidx = record { TYPES = [] ; FUNCS = [] ; GLOBALS = [] ; TABLES = [] ; MEMS = [] ; ELEMS = [] ; DATAS = [] ; LOCALS = [] ; LABELS = [] ; TAGS = (v-tagidx ∷ []) }

{- Auxiliary Definition at: ../specification/wasm-3.0/1.1-syntax.values.spectec:191.1-191.38 -}
{-# TERMINATING #-}
free-externidx : (v-externidx : externidx) → free
free-externidx (FUNC v-funcidx) = (free-funcidx v-funcidx)
free-externidx (GLOBAL v-globalidx) = (free-globalidx v-globalidx)
free-externidx (TABLE v-tableidx) = (free-tableidx v-tableidx)
free-externidx (MEM v-memidx) = (free-memidx v-memidx)
free-externidx (TAG v-tagidx) = (free-tagidx v-tagidx)
free-externidx v-externidx = default-val

{- Inductive Type Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:8.1-8.55 -}
data null : Set where
  NULL : null

instance
  inh-null : Inhabited null
  inh-null = record { default-val = NULL }

eq-null-fun : null → null → Bool
eq-null-fun NULL NULL = true
instance
  haseq-null : HasEq null
  haseq-null = record { _=?_ = eq-null-fun }

{- Inductive Type Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:10.1-11.14 -}
data addrtype : Set where
  I32 : addrtype
  I64 : addrtype

instance
  inh-addrtype : Inhabited addrtype
  inh-addrtype = record { default-val = I32 }

eq-addrtype-fun : addrtype → addrtype → Bool
eq-addrtype-fun I32 I32 = true
eq-addrtype-fun I64 I64 = true
eq-addrtype-fun _ _ = false
instance
  haseq-addrtype : HasEq addrtype
  haseq-addrtype = record { _=?_ = eq-addrtype-fun }

{- Inductive Type Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:13.1-14.26 -}
data numtype : Set where
  numtype-I32 : numtype
  numtype-I64 : numtype
  F32 : numtype
  F64 : numtype

instance
  inh-numtype : Inhabited numtype
  inh-numtype = record { default-val = numtype-I32 }

eq-numtype-fun : numtype → numtype → Bool
eq-numtype-fun numtype-I32 numtype-I32 = true
eq-numtype-fun numtype-I64 numtype-I64 = true
eq-numtype-fun F32 F32 = true
eq-numtype-fun F64 F64 = true
eq-numtype-fun _ _ = false
instance
  haseq-numtype : HasEq numtype
  haseq-numtype = record { _=?_ = eq-numtype-fun }

{- Auxiliary Definition at:  -}
{-# TERMINATING #-}
numtype-addrtype : (var-0 : addrtype) → numtype
numtype-addrtype I32 = numtype-I32
numtype-addrtype I64 = numtype-I64
numtype-addrtype var-0 = default-val

{- Inductive Type Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:16.1-17.9 -}
data vectype : Set where
  V128 : vectype

eq-vectype-fun : vectype → vectype → Bool
eq-vectype-fun V128 V128 = true
instance
  haseq-vectype : HasEq vectype
  haseq-vectype = record { _=?_ = eq-vectype-fun }

{- Inductive Type Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:19.1-20.22 -}
data consttype : Set where
  consttype-I32 : consttype
  consttype-I64 : consttype
  consttype-F32 : consttype
  consttype-F64 : consttype
  consttype-V128 : consttype

instance
  inh-consttype : Inhabited consttype
  inh-consttype = record { default-val = consttype-I32 }

{- Auxiliary Definition at:  -}
{-# TERMINATING #-}
consttype-numtype : (var-0 : numtype) → consttype
consttype-numtype numtype-I32 = consttype-I32
consttype-numtype numtype-I64 = consttype-I64
consttype-numtype F32 = consttype-F32
consttype-numtype F64 = consttype-F64
consttype-numtype var-0 = default-val

{- Auxiliary Definition at:  -}
{-# TERMINATING #-}
consttype-vectype : (var-0 : vectype) → consttype
consttype-vectype V128 = consttype-V128
consttype-vectype var-0 = default-val

{- Inductive Type Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:28.1-29.14 -}
data absheaptype : Set where
  ANY : absheaptype
  EQ : absheaptype
  I31 : absheaptype
  STRUCT : absheaptype
  ARRAY : absheaptype
  NONE : absheaptype
  absheaptype-FUNC : absheaptype
  NOFUNC : absheaptype
  EXN : absheaptype
  NOEXN : absheaptype
  EXTERN : absheaptype
  NOEXTERN : absheaptype
  BOT : absheaptype

{- Inductive Type Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:109.1-109.54 -}
data mut : Set where
  MUT : mut

instance
  inh-mut : Inhabited mut
  inh-mut = record { default-val = MUT }

eq-mut-fun : mut → mut → Bool
eq-mut-fun MUT MUT = true
instance
  haseq-mut : HasEq mut
  haseq-mut = record { _=?_ = eq-mut-fun }

{- Inductive Type Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:110.1-110.60 -}
data final : Set where
  FINAL : final

instance
  inh-final : Inhabited final
  inh-final = record { default-val = FINAL }

eq-final-fun : final → final → Bool
eq-final-fun FINAL FINAL = true
instance
  haseq-final : HasEq final
  haseq-final = record { _=?_ = eq-final-fun }

mutual
  {- Inductive Type Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:37.1-38.43 -}
  data typeuse : Set where
    -IDX : (v-typeidx : typeidx) → typeuse
    -DEF : (v-rectype : rectype) → (v-n : n) → typeuse
    REC : (v-n : n) → typeuse
  
  instance
    inh-typeuse : Inhabited typeuse
    inh-typeuse = record { default-val = (-IDX (default-val)) }
  
  eq-typeuse-fun : typeuse → typeuse → Bool
  eq-typeuse-fun (-IDX x0) (-IDX y0) = (x0 =? y0)
  eq-typeuse-fun (-DEF x0 x1) (-DEF y0 y1) = (eq-rectype-fun x0 y0) ∧ (x1 =? y1)
  eq-typeuse-fun (REC x0) (REC y0) = (x0 =? y0)
  eq-typeuse-fun _ _ = false
  instance
    haseq-typeuse : HasEq typeuse
    haseq-typeuse = record { _=?_ = eq-typeuse-fun }

  {- Inductive Type Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:43.1-44.26 -}
  data heaptype : Set where
    heaptype-ANY : heaptype
    heaptype-EQ : heaptype
    heaptype-I31 : heaptype
    heaptype-STRUCT : heaptype
    heaptype-ARRAY : heaptype
    heaptype-NONE : heaptype
    heaptype-FUNC : heaptype
    heaptype-NOFUNC : heaptype
    heaptype-EXN : heaptype
    heaptype-NOEXN : heaptype
    heaptype-EXTERN : heaptype
    heaptype-NOEXTERN : heaptype
    heaptype-BOT : heaptype
    heaptype--IDX : (v-typeidx : typeidx) → heaptype
    heaptype--DEF : (v-rectype : rectype) → (v-n : n) → heaptype
    heaptype-REC : (v-n : n) → heaptype
  
  instance
    inh-heaptype : Inhabited heaptype
    inh-heaptype = record { default-val = heaptype-ANY }
  
  eq-heaptype-fun : heaptype → heaptype → Bool
  eq-heaptype-fun heaptype-ANY heaptype-ANY = true
  eq-heaptype-fun heaptype-EQ heaptype-EQ = true
  eq-heaptype-fun heaptype-I31 heaptype-I31 = true
  eq-heaptype-fun heaptype-STRUCT heaptype-STRUCT = true
  eq-heaptype-fun heaptype-ARRAY heaptype-ARRAY = true
  eq-heaptype-fun heaptype-NONE heaptype-NONE = true
  eq-heaptype-fun heaptype-FUNC heaptype-FUNC = true
  eq-heaptype-fun heaptype-NOFUNC heaptype-NOFUNC = true
  eq-heaptype-fun heaptype-EXN heaptype-EXN = true
  eq-heaptype-fun heaptype-NOEXN heaptype-NOEXN = true
  eq-heaptype-fun heaptype-EXTERN heaptype-EXTERN = true
  eq-heaptype-fun heaptype-NOEXTERN heaptype-NOEXTERN = true
  eq-heaptype-fun heaptype-BOT heaptype-BOT = true
  eq-heaptype-fun (heaptype--IDX x0) (heaptype--IDX y0) = (x0 =? y0)
  eq-heaptype-fun (heaptype--DEF x0 x1) (heaptype--DEF y0 y1) = (eq-rectype-fun x0 y0) ∧ (x1 =? y1)
  eq-heaptype-fun (heaptype-REC x0) (heaptype-REC y0) = (x0 =? y0)
  eq-heaptype-fun _ _ = false
  instance
    haseq-heaptype : HasEq heaptype
    haseq-heaptype = record { _=?_ = eq-heaptype-fun }

  {- Inductive Type Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:51.1-52.14 -}
  data valtype : Set where
    valtype-I32 : valtype
    valtype-I64 : valtype
    valtype-F32 : valtype
    valtype-F64 : valtype
    valtype-V128 : valtype
    REF : (null-opt : (Maybe null)) → (v-heaptype : heaptype) → valtype
    valtype-BOT : valtype
  
  instance
    inh-valtype : Inhabited valtype
    inh-valtype = record { default-val = valtype-I32 }
  
  eq-valtype-fun : valtype → valtype → Bool
  eq-valtype-fun valtype-I32 valtype-I32 = true
  eq-valtype-fun valtype-I64 valtype-I64 = true
  eq-valtype-fun valtype-F32 valtype-F32 = true
  eq-valtype-fun valtype-F64 valtype-F64 = true
  eq-valtype-fun valtype-V128 valtype-V128 = true
  eq-valtype-fun (REF x0 x1) (REF y0 y1) = (x0 =? y0) ∧ (eq-heaptype-fun x1 y1)
  eq-valtype-fun valtype-BOT valtype-BOT = true
  eq-valtype-fun _ _ = false
  instance
    haseq-valtype : HasEq valtype
    haseq-valtype = record { _=?_ = eq-valtype-fun }

  {- Inductive Type Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:92.1-92.66 -}
  data storagetype : Set where
    storagetype-I32 : storagetype
    storagetype-I64 : storagetype
    storagetype-F32 : storagetype
    storagetype-F64 : storagetype
    storagetype-V128 : storagetype
    storagetype-REF : (null-opt : (Maybe null)) → (v-heaptype : heaptype) → storagetype
    storagetype-BOT : storagetype
    I8 : storagetype
    I16 : storagetype
  
  instance
    inh-storagetype : Inhabited storagetype
    inh-storagetype = record { default-val = storagetype-I32 }
  
  eq-storagetype-fun : storagetype → storagetype → Bool
  eq-storagetype-fun storagetype-I32 storagetype-I32 = true
  eq-storagetype-fun storagetype-I64 storagetype-I64 = true
  eq-storagetype-fun storagetype-F32 storagetype-F32 = true
  eq-storagetype-fun storagetype-F64 storagetype-F64 = true
  eq-storagetype-fun storagetype-V128 storagetype-V128 = true
  eq-storagetype-fun (storagetype-REF x0 x1) (storagetype-REF y0 y1) = (x0 =? y0) ∧ (eq-heaptype-fun x1 y1)
  eq-storagetype-fun storagetype-BOT storagetype-BOT = true
  eq-storagetype-fun I8 I8 = true
  eq-storagetype-fun I16 I16 = true
  eq-storagetype-fun _ _ = false
  instance
    haseq-storagetype : HasEq storagetype
    haseq-storagetype = record { _=?_ = eq-storagetype-fun }

  {- Inductive Type Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:112.1-112.61 -}
  data fieldtype : Set where
    mk-fieldtype : (mut-opt : (Maybe mut)) → (v-storagetype : storagetype) → fieldtype
  
  instance
    inh-fieldtype : Inhabited fieldtype
    inh-fieldtype = record { default-val = (mk-fieldtype (nothing) (default-val)) }
  
  eq-fieldtype-fun : fieldtype → fieldtype → Bool
  eq-fieldtype-fun (mk-fieldtype x0 x1) (mk-fieldtype y0 y1) = (x0 =? y0) ∧ (eq-storagetype-fun x1 y1)
  instance
    haseq-fieldtype : HasEq fieldtype
    haseq-fieldtype = record { _=?_ = eq-fieldtype-fun }

  {- Inductive Type Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:114.1-117.34 -}
  data comptype : Set where
    comptype-STRUCT : (_ : (list-fam0 (fieldtype))) → comptype
    comptype-ARRAY : (v-fieldtype : fieldtype) → comptype
    comptype-FUNC : (v-resulttype : (list-fam0 (valtype))) → (v-resulttype : (list-fam0 (valtype))) → comptype
  
  instance
    inh-comptype : Inhabited comptype
    inh-comptype = record { default-val = (comptype-STRUCT ((Inhabited.default-val (inh-list-fun fieldtype)))) }
  
  eq-fieldtype-lst-fun : List fieldtype → List fieldtype → Bool
  eq-fieldtype-lst-fun [] [] = true
  eq-fieldtype-lst-fun (x ∷ xs) (y ∷ ys) = (eq-fieldtype-fun x y) ∧ (eq-fieldtype-lst-fun xs ys)
  eq-fieldtype-lst-fun _ _ = false
  eq--list-fam0--fieldtype---fam-fun : (list-fam0 (fieldtype)) → (list-fam0 (fieldtype)) → Bool
  eq--list-fam0--fieldtype---fam-fun (mk-list x) (mk-list y) = eq-fieldtype-lst-fun x y
  eq-valtype-lst-fun : List valtype → List valtype → Bool
  eq-valtype-lst-fun [] [] = true
  eq-valtype-lst-fun (x ∷ xs) (y ∷ ys) = (eq-valtype-fun x y) ∧ (eq-valtype-lst-fun xs ys)
  eq-valtype-lst-fun _ _ = false
  eq--list-fam0--valtype---fam-fun : (list-fam0 (valtype)) → (list-fam0 (valtype)) → Bool
  eq--list-fam0--valtype---fam-fun (mk-list x) (mk-list y) = eq-valtype-lst-fun x y
  eq-comptype-fun : comptype → comptype → Bool
  eq-comptype-fun (comptype-STRUCT x0) (comptype-STRUCT y0) = (eq--list-fam0--fieldtype---fam-fun x0 y0)
  eq-comptype-fun (comptype-ARRAY x0) (comptype-ARRAY y0) = (eq-fieldtype-fun x0 y0)
  eq-comptype-fun (comptype-FUNC x0 x1) (comptype-FUNC y0 y1) = (eq--list-fam0--valtype---fam-fun x0 y0) ∧ (eq--list-fam0--valtype---fam-fun x1 y1)
  eq-comptype-fun _ _ = false
  instance
    haseq-comptype : HasEq comptype
    haseq-comptype = record { _=?_ = eq-comptype-fun }

  {- Inductive Type Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:119.1-120.33 -}
  data subtype : Set where
    SUB : (final-opt : (Maybe final)) → (typeuse-lst : (List typeuse)) → (v-comptype : comptype) → subtype
  
  instance
    inh-subtype : Inhabited subtype
    inh-subtype = record { default-val = (SUB (nothing) ([]) (default-val)) }
  
  eq-typeuse-lst-fun : List typeuse → List typeuse → Bool
  eq-typeuse-lst-fun [] [] = true
  eq-typeuse-lst-fun (x ∷ xs) (y ∷ ys) = (eq-typeuse-fun x y) ∧ (eq-typeuse-lst-fun xs ys)
  eq-typeuse-lst-fun _ _ = false
  eq-subtype-fun : subtype → subtype → Bool
  eq-subtype-fun (SUB x0 x1 x2) (SUB y0 y1 y2) = (x0 =? y0) ∧ (eq-typeuse-lst-fun x1 y1) ∧ (eq-comptype-fun x2 y2)
  instance
    haseq-subtype : HasEq subtype
    haseq-subtype = record { _=?_ = eq-subtype-fun }

  {- Inductive Type Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:122.1-123.22 -}
  data rectype : Set where
    rectype-REC : (_ : (list-fam0 (subtype))) → rectype
  
  instance
    inh-rectype : Inhabited rectype
    inh-rectype = record { default-val = (rectype-REC ((Inhabited.default-val (inh-list-fun subtype)))) }
  
  eq-subtype-lst-fun : List subtype → List subtype → Bool
  eq-subtype-lst-fun [] [] = true
  eq-subtype-lst-fun (x ∷ xs) (y ∷ ys) = (eq-subtype-fun x y) ∧ (eq-subtype-lst-fun xs ys)
  eq-subtype-lst-fun _ _ = false
  eq--list-fam0--subtype---fam-fun : (list-fam0 (subtype)) → (list-fam0 (subtype)) → Bool
  eq--list-fam0--subtype---fam-fun (mk-list x) (mk-list y) = eq-subtype-lst-fun x y
  eq-rectype-fun : rectype → rectype → Bool
  eq-rectype-fun (rectype-REC x0) (rectype-REC y0) = (eq--list-fam0--subtype---fam-fun x0 y0)
  instance
    haseq-rectype : HasEq rectype
    haseq-rectype = record { _=?_ = eq-rectype-fun }

{- Type Alias Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:102.1-103.16 -}
resulttype : Set
resulttype = (list-fam0 (valtype))

{- Auxiliary Definition at:  -}
{-# TERMINATING #-}
heaptype-absheaptype : (var-0 : absheaptype) → heaptype
heaptype-absheaptype ANY = heaptype-ANY
heaptype-absheaptype EQ = heaptype-EQ
heaptype-absheaptype I31 = heaptype-I31
heaptype-absheaptype STRUCT = heaptype-STRUCT
heaptype-absheaptype ARRAY = heaptype-ARRAY
heaptype-absheaptype NONE = heaptype-NONE
heaptype-absheaptype absheaptype-FUNC = heaptype-FUNC
heaptype-absheaptype NOFUNC = heaptype-NOFUNC
heaptype-absheaptype EXN = heaptype-EXN
heaptype-absheaptype NOEXN = heaptype-NOEXN
heaptype-absheaptype EXTERN = heaptype-EXTERN
heaptype-absheaptype NOEXTERN = heaptype-NOEXTERN
heaptype-absheaptype BOT = heaptype-BOT
heaptype-absheaptype var-0 = default-val

{- Auxiliary Definition at:  -}
{-# TERMINATING #-}
valtype-addrtype : (var-0 : addrtype) → valtype
valtype-addrtype I32 = valtype-I32
valtype-addrtype I64 = valtype-I64
valtype-addrtype var-0 = default-val

{- Auxiliary Definition at:  -}
{-# TERMINATING #-}
storagetype-consttype : (var-0 : consttype) → storagetype
storagetype-consttype consttype-I32 = storagetype-I32
storagetype-consttype consttype-I64 = storagetype-I64
storagetype-consttype consttype-F32 = storagetype-F32
storagetype-consttype consttype-F64 = storagetype-F64
storagetype-consttype consttype-V128 = storagetype-V128
storagetype-consttype var-0 = default-val

{- Auxiliary Definition at:  -}
{-# TERMINATING #-}
valtype-numtype : (var-0 : numtype) → valtype
valtype-numtype numtype-I32 = valtype-I32
valtype-numtype numtype-I64 = valtype-I64
valtype-numtype F32 = valtype-F32
valtype-numtype F64 = valtype-F64
valtype-numtype var-0 = default-val

{- Auxiliary Definition at:  -}
{-# TERMINATING #-}
heaptype-typeuse : (var-0 : typeuse) → heaptype
heaptype-typeuse (-IDX x0) = (heaptype--IDX x0)
heaptype-typeuse (-DEF x0 x1) = (heaptype--DEF x0 x1)
heaptype-typeuse (REC x0) = (heaptype-REC x0)
heaptype-typeuse var-0 = default-val

{- Auxiliary Definition at:  -}
{-# TERMINATING #-}
storagetype-valtype : (var-0 : valtype) → storagetype
storagetype-valtype valtype-I32 = storagetype-I32
storagetype-valtype valtype-I64 = storagetype-I64
storagetype-valtype valtype-F32 = storagetype-F32
storagetype-valtype valtype-F64 = storagetype-F64
storagetype-valtype valtype-V128 = storagetype-V128
storagetype-valtype (REF x0 x1) = (storagetype-REF x0 x1)
storagetype-valtype valtype-BOT = storagetype-BOT
storagetype-valtype var-0 = default-val

{- Auxiliary Definition at:  -}
{-# TERMINATING #-}
valtype-vectype : (var-0 : vectype) → valtype
valtype-vectype V128 = valtype-V128
valtype-vectype var-0 = default-val

{- Inductive Type Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:32.1-33.34 -}
data deftype : Set where
  deftype--DEF : (v-rectype : rectype) → (v-n : n) → deftype

instance
  inh-deftype : Inhabited deftype
  inh-deftype = record { default-val = (deftype--DEF (default-val) (default-val)) }

eq-deftype-fun : deftype → deftype → Bool
eq-deftype-fun (deftype--DEF x0 x1) (deftype--DEF y0 y1) = (x0 =? y0) ∧ (x1 =? y1)
instance
  haseq-deftype : HasEq deftype
  haseq-deftype = record { _=?_ = eq-deftype-fun }

{- Auxiliary Definition at:  -}
{-# TERMINATING #-}
heaptype-deftype : (var-0 : deftype) → heaptype
heaptype-deftype (deftype--DEF x0 x1) = (heaptype--DEF x0 x1)
heaptype-deftype var-0 = default-val

{- Auxiliary Definition at:  -}
{-# TERMINATING #-}
typeuse-deftype : (var-0 : deftype) → typeuse
typeuse-deftype (deftype--DEF x0 x1) = (-DEF x0 x1)
typeuse-deftype var-0 = default-val

{- Inductive Type Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:40.1-41.42 -}
data typevar : Set where
  typevar--IDX : (v-typeidx : typeidx) → typevar
  typevar-REC : (v-n : n) → typevar

instance
  inh-typevar : Inhabited typevar
  inh-typevar = record { default-val = (typevar--IDX (default-val)) }

eq-typevar-fun : typevar → typevar → Bool
eq-typevar-fun (typevar--IDX x0) (typevar--IDX y0) = (x0 =? y0)
eq-typevar-fun (typevar-REC x0) (typevar-REC y0) = (x0 =? y0)
eq-typevar-fun _ _ = false
instance
  haseq-typevar : HasEq typevar
  haseq-typevar = record { _=?_ = eq-typevar-fun }

{- Auxiliary Definition at:  -}
{-# TERMINATING #-}
typeuse-typevar : (var-0 : typevar) → typeuse
typeuse-typevar (typevar--IDX x0) = (-IDX x0)
typeuse-typevar (typevar-REC x0) = (REC x0)
typeuse-typevar var-0 = default-val

{- Inductive Type Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:46.1-47.23 -}
data reftype : Set where
  reftype-REF : (null-opt : (Maybe null)) → (v-heaptype : heaptype) → reftype

instance
  inh-reftype : Inhabited reftype
  inh-reftype = record { default-val = (reftype-REF (nothing) (default-val)) }

eq-reftype-fun : reftype → reftype → Bool
eq-reftype-fun (reftype-REF x0 x1) (reftype-REF y0 y1) = (x0 =? y0) ∧ (x1 =? y1)
instance
  haseq-reftype : HasEq reftype
  haseq-reftype = record { _=?_ = eq-reftype-fun }

{- Auxiliary Definition at:  -}
{-# TERMINATING #-}
storagetype-reftype : (var-0 : reftype) → storagetype
storagetype-reftype (reftype-REF x0 x1) = (storagetype-REF x0 x1)
storagetype-reftype var-0 = default-val

{- Auxiliary Definition at:  -}
{-# TERMINATING #-}
valtype-reftype : (var-0 : reftype) → valtype
valtype-reftype (reftype-REF x0 x1) = (REF x0 x1)
valtype-reftype var-0 = default-val

{- Type Alias Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:55.1-55.55 -}
Inn : Set
Inn = addrtype

{- Inductive Type Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:56.1-56.56 -}
data Fnn : Set where
  Fnn-F32 : Fnn
  Fnn-F64 : Fnn

{- Auxiliary Definition at:  -}
{-# TERMINATING #-}
numtype-Fnn : (var-0 : Fnn) → numtype
numtype-Fnn Fnn-F32 = F32
numtype-Fnn Fnn-F64 = F64
numtype-Fnn var-0 = default-val

{- Type Alias Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:57.1-57.54 -}
Vnn : Set
Vnn = vectype

{- Inductive Type Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:58.1-58.42 -}
data Cnn : Set where
  Cnn-I32 : Cnn
  Cnn-I64 : Cnn
  Cnn-F32 : Cnn
  Cnn-F64 : Cnn
  Cnn-V128 : Cnn

{- Auxiliary Definition at:  -}
{-# TERMINATING #-}
storagetype-Cnn : (var-0 : Cnn) → storagetype
storagetype-Cnn Cnn-I32 = storagetype-I32
storagetype-Cnn Cnn-I64 = storagetype-I64
storagetype-Cnn Cnn-F32 = storagetype-F32
storagetype-Cnn Cnn-F64 = storagetype-F64
storagetype-Cnn Cnn-V128 = storagetype-V128
storagetype-Cnn var-0 = default-val

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:61.1-61.43 -}
ANYREF : reftype
ANYREF = (reftype-REF (just NULL) heaptype-ANY)

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:62.1-62.42 -}
EQREF : reftype
EQREF = (reftype-REF (just NULL) heaptype-EQ)

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:63.1-63.43 -}
I31REF : reftype
I31REF = (reftype-REF (just NULL) heaptype-I31)

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:64.1-64.46 -}
STRUCTREF : reftype
STRUCTREF = (reftype-REF (just NULL) heaptype-STRUCT)

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:65.1-65.45 -}
ARRAYREF : reftype
ARRAYREF = (reftype-REF (just NULL) heaptype-ARRAY)

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:66.1-66.44 -}
FUNCREF : reftype
FUNCREF = (reftype-REF (just NULL) heaptype-FUNC)

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:67.1-67.43 -}
EXNREF : reftype
EXNREF = (reftype-REF (just NULL) heaptype-EXN)

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:68.1-68.46 -}
EXTERNREF : reftype
EXTERNREF = (reftype-REF (just NULL) heaptype-EXTERN)

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:69.1-69.44 -}
NULLREF : reftype
NULLREF = (reftype-REF (just NULL) heaptype-NONE)

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:70.1-70.50 -}
NULLFUNCREF : reftype
NULLFUNCREF = (reftype-REF (just NULL) heaptype-NOFUNC)

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:71.1-71.49 -}
NULLEXNREF : reftype
NULLEXNREF = (reftype-REF (just NULL) heaptype-NOEXN)

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:72.1-72.54 -}
NULLEXTERNREF : reftype
NULLEXTERNREF = (reftype-REF (just NULL) heaptype-NOEXTERN)

{- Inductive Type Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:90.1-90.52 -}
data packtype : Set where
  packtype-I8 : packtype
  packtype-I16 : packtype

{- Auxiliary Definition at:  -}
{-# TERMINATING #-}
storagetype-packtype : (var-0 : packtype) → storagetype
storagetype-packtype packtype-I8 = I8
storagetype-packtype packtype-I16 = I16
storagetype-packtype var-0 = default-val

{- Inductive Type Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:91.1-91.60 -}
data lanetype : Set where
  lanetype-I32 : lanetype
  lanetype-I64 : lanetype
  lanetype-F32 : lanetype
  lanetype-F64 : lanetype
  lanetype-I8 : lanetype
  lanetype-I16 : lanetype

instance
  inh-lanetype : Inhabited lanetype
  inh-lanetype = record { default-val = lanetype-I32 }

eq-lanetype-fun : lanetype → lanetype → Bool
eq-lanetype-fun lanetype-I32 lanetype-I32 = true
eq-lanetype-fun lanetype-I64 lanetype-I64 = true
eq-lanetype-fun lanetype-F32 lanetype-F32 = true
eq-lanetype-fun lanetype-F64 lanetype-F64 = true
eq-lanetype-fun lanetype-I8 lanetype-I8 = true
eq-lanetype-fun lanetype-I16 lanetype-I16 = true
eq-lanetype-fun _ _ = false
instance
  haseq-lanetype : HasEq lanetype
  haseq-lanetype = record { _=?_ = eq-lanetype-fun }

{- Auxiliary Definition at:  -}
{-# TERMINATING #-}
lanetype-Fnn : (var-0 : Fnn) → lanetype
lanetype-Fnn Fnn-F32 = lanetype-F32
lanetype-Fnn Fnn-F64 = lanetype-F64
lanetype-Fnn var-0 = default-val

{- Auxiliary Definition at:  -}
{-# TERMINATING #-}
lanetype-addrtype : (var-0 : addrtype) → lanetype
lanetype-addrtype I32 = lanetype-I32
lanetype-addrtype I64 = lanetype-I64
lanetype-addrtype var-0 = default-val

{- Auxiliary Definition at:  -}
{-# TERMINATING #-}
lanetype-numtype : (var-0 : numtype) → lanetype
lanetype-numtype numtype-I32 = lanetype-I32
lanetype-numtype numtype-I64 = lanetype-I64
lanetype-numtype F32 = lanetype-F32
lanetype-numtype F64 = lanetype-F64
lanetype-numtype var-0 = default-val

{- Auxiliary Definition at:  -}
{-# TERMINATING #-}
lanetype-packtype : (var-0 : packtype) → lanetype
lanetype-packtype packtype-I8 = lanetype-I8
lanetype-packtype packtype-I16 = lanetype-I16
lanetype-packtype var-0 = default-val

{- Type Alias Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:95.1-95.55 -}
Pnn : Set
Pnn = packtype

{- Inductive Type Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:96.1-96.56 -}
data Jnn : Set where
  Jnn-I32 : Jnn
  Jnn-I64 : Jnn
  Jnn-I8 : Jnn
  Jnn-I16 : Jnn

instance
  inh-Jnn : Inhabited Jnn
  inh-Jnn = record { default-val = Jnn-I32 }

{- Auxiliary Definition at:  -}
{-# TERMINATING #-}
lanetype-Jnn : (var-0 : Jnn) → lanetype
lanetype-Jnn Jnn-I32 = lanetype-I32
lanetype-Jnn Jnn-I64 = lanetype-I64
lanetype-Jnn Jnn-I8 = lanetype-I8
lanetype-Jnn Jnn-I16 = lanetype-I16
lanetype-Jnn var-0 = default-val

{- Auxiliary Definition at:  -}
{-# TERMINATING #-}
Jnn-addrtype : (var-0 : addrtype) → Jnn
Jnn-addrtype I32 = Jnn-I32
Jnn-addrtype I64 = Jnn-I64
Jnn-addrtype var-0 = default-val

{- Type Alias Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:97.1-97.55 -}
Lnn : Set
Lnn = lanetype

{- Inductive Type Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:128.1-128.74 -}
data limits : Set where
  mk-limits : (v-u64 : u64) → (u64-opt : (Maybe u64)) → limits

instance
  inh-limits : Inhabited limits
  inh-limits = record { default-val = (mk-limits (default-val) (nothing)) }

eq-limits-fun : limits → limits → Bool
eq-limits-fun (mk-limits x0 x1) (mk-limits y0 y1) = (x0 =? y0) ∧ (x1 =? y1)
instance
  haseq-limits : HasEq limits
  haseq-limits = record { _=?_ = eq-limits-fun }

{- Type Alias Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:130.1-130.47 -}
tagtype : Set
tagtype = typeuse

{- Inductive Type Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:131.1-131.58 -}
data globaltype : Set where
  mk-globaltype : (mut-opt : (Maybe mut)) → (v-valtype : valtype) → globaltype

instance
  inh-globaltype : Inhabited globaltype
  inh-globaltype = record { default-val = (mk-globaltype (nothing) (default-val)) }

eq-globaltype-fun : globaltype → globaltype → Bool
eq-globaltype-fun (mk-globaltype x0 x1) (mk-globaltype y0 y1) = (x0 =? y0) ∧ (x1 =? y1)
instance
  haseq-globaltype : HasEq globaltype
  haseq-globaltype = record { _=?_ = eq-globaltype-fun }

{- Inductive Type Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:132.1-132.63 -}
data memtype : Set where
  PAGE : (v-addrtype : addrtype) → (v-limits : limits) → memtype

instance
  inh-memtype : Inhabited memtype
  inh-memtype = record { default-val = (PAGE (default-val) (default-val)) }

eq-memtype-fun : memtype → memtype → Bool
eq-memtype-fun (PAGE x0 x1) (PAGE y0 y1) = (x0 =? y0) ∧ (x1 =? y1)
instance
  haseq-memtype : HasEq memtype
  haseq-memtype = record { _=?_ = eq-memtype-fun }

{- Inductive Type Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:133.1-133.67 -}
data tabletype : Set where
  mk-tabletype : (v-addrtype : addrtype) → (v-limits : limits) → (v-reftype : reftype) → tabletype

instance
  inh-tabletype : Inhabited tabletype
  inh-tabletype = record { default-val = (mk-tabletype (default-val) (default-val) (default-val)) }

eq-tabletype-fun : tabletype → tabletype → Bool
eq-tabletype-fun (mk-tabletype x0 x1 x2) (mk-tabletype y0 y1 y2) = (x0 =? y0) ∧ (x1 =? y1) ∧ (x2 =? y2)
instance
  haseq-tabletype : HasEq tabletype
  haseq-tabletype = record { _=?_ = eq-tabletype-fun }

{- Inductive Type Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:134.1-134.64 -}
data datatype : Set where
  OK : datatype

instance
  inh-datatype : Inhabited datatype
  inh-datatype = record { default-val = OK }

{- Type Alias Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:135.1-135.52 -}
elemtype : Set
elemtype = reftype

{- Inductive Type Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:137.1-138.83 -}
data externtype : Set where
  externtype-TAG : (v-tagtype : tagtype) → externtype
  externtype-GLOBAL : (v-globaltype : globaltype) → externtype
  externtype-MEM : (v-memtype : memtype) → externtype
  externtype-TABLE : (v-tabletype : tabletype) → externtype
  externtype-FUNC : (v-typeuse : typeuse) → externtype

instance
  inh-externtype : Inhabited externtype
  inh-externtype = record { default-val = (externtype-TAG (default-val)) }

eq-externtype-fun : externtype → externtype → Bool
eq-externtype-fun (externtype-TAG x0) (externtype-TAG y0) = (x0 =? y0)
eq-externtype-fun (externtype-GLOBAL x0) (externtype-GLOBAL y0) = (x0 =? y0)
eq-externtype-fun (externtype-MEM x0) (externtype-MEM y0) = (x0 =? y0)
eq-externtype-fun (externtype-TABLE x0) (externtype-TABLE y0) = (x0 =? y0)
eq-externtype-fun (externtype-FUNC x0) (externtype-FUNC y0) = (x0 =? y0)
eq-externtype-fun _ _ = false
instance
  haseq-externtype : HasEq externtype
  haseq-externtype = record { _=?_ = eq-externtype-fun }

{- Inductive Type Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:140.1-141.47 -}
data moduletype : Set where
  mk-moduletype : (externtype-lst : (List externtype)) → (externtype-lst : (List externtype)) → moduletype

instance
  inh-moduletype : Inhabited moduletype
  inh-moduletype = record { default-val = (mk-moduletype ([]) ([])) }

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:179.1-179.65 -}
{-# TERMINATING #-}
IN : (v-N : N) → (Maybe Inn)
IN (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (zero))))))))))))))))))))))))))))))))) = (just I32)
IN (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (zero))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = (just I64)
IN x0 = nothing

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:183.1-183.65 -}
{-# TERMINATING #-}
FN : (v-N : N) → (Maybe Fnn)
FN (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (zero))))))))))))))))))))))))))))))))) = (just Fnn-F32)
FN (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (zero))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = (just Fnn-F64)
FN x0 = nothing

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:187.1-187.65 -}
{-# TERMINATING #-}
JN : (v-N : N) → (Maybe Jnn)
JN (suc (suc (suc (suc (suc (suc (suc (suc (zero))))))))) = (just Jnn-I8)
JN (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (zero))))))))))))))))) = (just Jnn-I16)
JN (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (zero))))))))))))))))))))))))))))))))) = (just Jnn-I32)
JN (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (zero))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = (just Jnn-I64)
JN x0 = nothing

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:196.1-196.46 -}
{-# TERMINATING #-}
size : (v-numtype : numtype) → ℕ
size numtype-I32 = 32
size numtype-I64 = 64
size F32 = 32
size F64 = 64
size v-numtype = default-val

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:197.1-197.46 -}
{-# TERMINATING #-}
vsize : (v-vectype : vectype) → ℕ
vsize V128 = 128
vsize v-vectype = default-val

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:198.1-198.46 -}
{-# TERMINATING #-}
psize : (v-packtype : packtype) → ℕ
psize packtype-I8 = 8
psize packtype-I16 = 16
psize v-packtype = default-val

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:199.1-199.46 -}
{-# TERMINATING #-}
lsize : (v-lanetype : lanetype) → ℕ
lsize lanetype-I32 = (size numtype-I32)
lsize lanetype-I64 = (size numtype-I64)
lsize lanetype-F32 = (size F32)
lsize lanetype-F64 = (size F64)
lsize lanetype-I8 = (psize packtype-I8)
lsize lanetype-I16 = (psize packtype-I16)
lsize v-lanetype = default-val

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:200.1-200.60 -}
{-# TERMINATING #-}
zsize : (v-storagetype : storagetype) → (Maybe ℕ)
zsize storagetype-I32 = (just (size numtype-I32))
zsize storagetype-I64 = (just (size numtype-I64))
zsize storagetype-F32 = (just (size F32))
zsize storagetype-F64 = (just (size F64))
zsize storagetype-V128 = (just (vsize V128))
zsize I8 = (just (psize packtype-I8))
zsize I16 = (just (psize packtype-I16))
zsize x0 = nothing

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:201.1-201.71 -}
{-# TERMINATING #-}
isize : (v-Inn : Inn) → ℕ
isize v-Inn = (size (numtype-addrtype v-Inn))

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:202.1-202.71 -}
{-# TERMINATING #-}
jsize : (v-Jnn : Jnn) → ℕ
jsize v-Jnn = (lsize (lanetype-Jnn v-Jnn))

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:203.1-203.71 -}
{-# TERMINATING #-}
fsize : (v-Fnn : Fnn) → ℕ
fsize v-Fnn = (size (numtype-Fnn v-Fnn))

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:226.1-226.40 -}
{-# TERMINATING #-}
inv-isize : (nat : ℕ) → (Maybe Inn)
inv-isize (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (zero))))))))))))))))))))))))))))))))) = (just I32)
inv-isize (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (zero))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = (just I64)
inv-isize x0 = nothing

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:227.1-227.40 -}
{-# TERMINATING #-}
inv-jsize : (nat : ℕ) → (Maybe Jnn)
inv-jsize (suc (suc (suc (suc (suc (suc (suc (suc (zero))))))))) = (just Jnn-I8)
inv-jsize (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (zero))))))))))))))))) = (just Jnn-I16)
inv-jsize v-n = (mapMaybe (λ (iter-val-1 : Inn) → (Jnn-addrtype iter-val-1)) (inv-isize v-n))

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:228.1-228.40 -}
{-# TERMINATING #-}
inv-fsize : (nat : ℕ) → (Maybe Fnn)
inv-fsize (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (zero))))))))))))))))))))))))))))))))) = (just Fnn-F32)
inv-fsize (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (zero))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = (just Fnn-F64)
inv-fsize x0 = nothing

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:239.1-239.63 -}
{-# TERMINATING #-}
sizenn : (v-numtype : numtype) → ℕ
sizenn nt = (size nt)

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:240.1-240.63 -}
{-# TERMINATING #-}
sizenn1 : (v-numtype : numtype) → ℕ
sizenn1 nt = (size nt)

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:241.1-241.63 -}
{-# TERMINATING #-}
sizenn2 : (v-numtype : numtype) → ℕ
sizenn2 nt = (size nt)

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:246.1-246.63 -}
{-# TERMINATING #-}
vsizenn : (v-vectype : vectype) → ℕ
vsizenn vt = (vsize vt)

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:249.1-249.63 -}
{-# TERMINATING #-}
psizenn : (v-packtype : packtype) → ℕ
psizenn pt = (psize pt)

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:252.1-252.63 -}
{-# TERMINATING #-}
lsizenn : (v-lanetype : lanetype) → ℕ
lsizenn lt = (lsize lt)

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:253.1-253.63 -}
{-# TERMINATING #-}
lsizenn1 : (v-lanetype : lanetype) → ℕ
lsizenn1 lt = (lsize lt)

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:254.1-254.63 -}
{-# TERMINATING #-}
lsizenn2 : (v-lanetype : lanetype) → ℕ
lsizenn2 lt = (lsize lt)

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:259.1-259.83 -}
{-# TERMINATING #-}
jsizenn : (v-Jnn : Jnn) → ℕ
jsizenn v-Jnn = (lsize (lanetype-Jnn v-Jnn))

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:262.1-262.42 -}
{-# TERMINATING #-}
inv-jsizenn : (nat : ℕ) → (Maybe Jnn)
inv-jsizenn v-n = (inv-jsize v-n)

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:268.1-268.56 -}
{-# TERMINATING #-}
lunpack : (v-lanetype : lanetype) → numtype
lunpack lanetype-I32 = numtype-I32
lunpack lanetype-I64 = numtype-I64
lunpack lanetype-F32 = F32
lunpack lanetype-F64 = F64
lunpack lanetype-I8 = numtype-I32
lunpack lanetype-I16 = numtype-I32
lunpack v-lanetype = default-val

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:272.1-272.35 -}
{-# TERMINATING #-}
unpack : (v-storagetype : storagetype) → valtype
unpack storagetype-BOT = valtype-BOT
unpack (storagetype-REF null-opt v-heaptype) = (REF null-opt v-heaptype)
unpack storagetype-V128 = valtype-V128
unpack storagetype-F64 = valtype-F64
unpack storagetype-F32 = valtype-F32
unpack storagetype-I64 = valtype-I64
unpack storagetype-I32 = valtype-I32
unpack I8 = valtype-I32
unpack I16 = valtype-I32
unpack v-storagetype = default-val

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:276.1-276.73 -}
{-# TERMINATING #-}
nunpack : (v-storagetype : storagetype) → (Maybe numtype)
nunpack storagetype-I32 = (just numtype-I32)
nunpack storagetype-I64 = (just numtype-I64)
nunpack storagetype-F32 = (just F32)
nunpack storagetype-F64 = (just F64)
nunpack I8 = (just numtype-I32)
nunpack I16 = (just numtype-I32)
nunpack x0 = nothing

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:280.1-280.73 -}
{-# TERMINATING #-}
vunpack : (v-storagetype : storagetype) → (Maybe vectype)
vunpack storagetype-V128 = (just V128)
vunpack x0 = nothing

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:283.1-283.74 -}
{-# TERMINATING #-}
cunpack : (v-storagetype : storagetype) → (Maybe consttype)
cunpack storagetype-I32 = (just consttype-I32)
cunpack storagetype-I64 = (just consttype-I64)
cunpack storagetype-F32 = (just consttype-F32)
cunpack storagetype-F64 = (just consttype-F64)
cunpack storagetype-V128 = (just consttype-V128)
cunpack I8 = (just consttype-I32)
cunpack I16 = (just consttype-I32)
cunpack storagetype-I32 = (just (consttype-numtype (lunpack lanetype-I32)))
cunpack storagetype-I64 = (just (consttype-numtype (lunpack lanetype-I64)))
cunpack storagetype-F32 = (just (consttype-numtype (lunpack lanetype-F32)))
cunpack storagetype-F64 = (just (consttype-numtype (lunpack lanetype-F64)))
cunpack I8 = (just (consttype-numtype (lunpack lanetype-I8)))
cunpack I16 = (just (consttype-numtype (lunpack lanetype-I16)))
cunpack x0 = nothing

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:291.1-291.90 -}
{-# TERMINATING #-}
minat : (v-addrtype : addrtype) (addrtype-0 : addrtype) → addrtype
minat at-1 at-2 = (if ((size (numtype-addrtype at-1)) ≤? (size (numtype-addrtype at-2))) then at-1 else at-2)

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:295.1-295.82 -}
{-# TERMINATING #-}
diffrt : (v-reftype : reftype) (reftype-0 : reftype) → reftype
diffrt (reftype-REF null-1-opt ht-1) (reftype-REF (just NULL) ht-2) = (reftype-REF nothing ht-1)
diffrt (reftype-REF null-1-opt ht-1) (reftype-REF nothing ht-2) = (reftype-REF null-1-opt ht-1)
diffrt v-reftype reftype-0 = default-val

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:300.1-300.63 -}
{-# TERMINATING #-}
as-deftype : (v-typeuse : typeuse) → (Maybe deftype)
as-deftype (-DEF v-rectype v-n) = (just (deftype--DEF v-rectype v-n))
as-deftype x0 = nothing

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:308.1-308.87 -}
{-# TERMINATING #-}
tagsxt : (var-0-lst : (List externtype)) → (List tagtype)
tagsxt [] = []
tagsxt ((externtype-TAG jt) ∷ xt-lst) = ((jt ∷ []) ++ (tagsxt xt-lst))
tagsxt (v-externtype ∷ xt-lst) = (tagsxt xt-lst)
tagsxt var-0-lst = []

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:309.1-309.90 -}
{-# TERMINATING #-}
globalsxt : (var-0-lst : (List externtype)) → (List globaltype)
globalsxt [] = []
globalsxt ((externtype-GLOBAL gt) ∷ xt-lst) = ((gt ∷ []) ++ (globalsxt xt-lst))
globalsxt (v-externtype ∷ xt-lst) = (globalsxt xt-lst)
globalsxt var-0-lst = []

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:310.1-310.87 -}
{-# TERMINATING #-}
memsxt : (var-0-lst : (List externtype)) → (List memtype)
memsxt [] = []
memsxt ((externtype-MEM mt) ∷ xt-lst) = ((mt ∷ []) ++ (memsxt xt-lst))
memsxt (v-externtype ∷ xt-lst) = (memsxt xt-lst)
memsxt var-0-lst = []

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:311.1-311.89 -}
{-# TERMINATING #-}
tablesxt : (var-0-lst : (List externtype)) → (List tabletype)
tablesxt [] = []
tablesxt ((externtype-TABLE tt') ∷ xt-lst) = ((tt' ∷ []) ++ (tablesxt xt-lst))
tablesxt (v-externtype ∷ xt-lst) = (tablesxt xt-lst)
tablesxt var-0-lst = []

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:312.1-312.88 -}
{-# TERMINATING #-}
funcsxt : (var-0-lst : (List externtype)) → (List deftype)
funcsxt [] = []
funcsxt ((externtype-FUNC (-DEF v-rectype v-n)) ∷ xt-lst) = ((as (List deftype) ((deftype--DEF v-rectype v-n) ∷ [])) ++ (funcsxt xt-lst))
funcsxt (v-externtype ∷ xt-lst) = (funcsxt xt-lst)
funcsxt var-0-lst = []

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:337.1-337.126 -}
{-# TERMINATING #-}
subst-typevar : (v-typevar : typevar) (var-0-lst : (List typevar)) (var-1-lst : (List typeuse)) → (Maybe typeuse)
subst-typevar tv [] [] = (just (typeuse-typevar tv))
subst-typevar tv (tv-1 ∷ tv'-lst) (tu-1 ∷ tu'-lst) = (mapMaybe (λ (iter-val-2 : typeuse) → (if (tv =? tv-1) then tu-1 else iter-val-2)) (subst-typevar tv tv'-lst tu'-lst))
subst-typevar x0 x1 x2 = nothing

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:401.1-401.87 -}
{-# TERMINATING #-}
minus-recs : (var-0-lst : (List typevar)) (var-1-lst : (List typeuse)) → (Maybe ((List typevar) × (List typeuse)))
minus-recs [] [] = (just ([] , []))
minus-recs ((typevar-REC v-n) ∷ tv-lst) (tu-1 ∷ tu-lst) = (minus-recs tv-lst tu-lst)
minus-recs ((typevar--IDX x) ∷ tv-lst) (tu-1 ∷ tu-lst) = let (tv'-lst , tu'-lst) = (unwrap! (minus-recs tv-lst tu-lst)) in (just (((as (List typevar) ((typevar--IDX x) ∷ [])) ++ tv'-lst) , ((tu-1 ∷ []) ++ tu'-lst)))
minus-recs x0 x1 = nothing

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:347.1-347.112 -}
{-# TERMINATING #-}
subst-packtype : (v-packtype : packtype) (var-0-lst : (List typevar)) (var-1-lst : (List typeuse)) → packtype
subst-packtype pt tv-lst tu-lst = pt

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:341.1-341.112 -}
{-# TERMINATING #-}
subst-numtype : (v-numtype : numtype) (var-0-lst : (List typevar)) (var-1-lst : (List typeuse)) → numtype
subst-numtype nt tv-lst tu-lst = nt

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:342.1-342.112 -}
{-# TERMINATING #-}
subst-vectype : (v-vectype : vectype) (var-0-lst : (List typevar)) (var-1-lst : (List typeuse)) → vectype
subst-vectype vt tv-lst tu-lst = vt

mutual
  {- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:338.1-338.112 -}
  {-# TERMINATING #-}
  subst-typeuse : (v-typeuse : typeuse) (var-0-lst : (List typevar)) (var-1-lst : (List typeuse)) → typeuse
  subst-typeuse (REC v-n) tv-lst tu-lst = (unwrap! (subst-typevar (typevar-REC v-n) tv-lst tu-lst))
  subst-typeuse (-IDX v-typeidx) tv-lst tu-lst = (unwrap! (subst-typevar (typevar--IDX v-typeidx) tv-lst tu-lst))
  subst-typeuse (-DEF v-rectype v-n) tv-lst tu-lst = (typeuse-deftype (subst-deftype (deftype--DEF v-rectype v-n) tv-lst tu-lst))
  subst-typeuse v-typeuse var-0-lst var-1-lst = default-val

  {- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:343.1-343.112 -}
  {-# TERMINATING #-}
  subst-heaptype : (v-heaptype : heaptype) (var-0-lst : (List typevar)) (var-1-lst : (List typeuse)) → heaptype
  subst-heaptype (heaptype-REC v-n) tv-lst tu-lst = (heaptype-typeuse (unwrap! (subst-typevar (typevar-REC v-n) tv-lst tu-lst)))
  subst-heaptype (heaptype--IDX v-typeidx) tv-lst tu-lst = (heaptype-typeuse (unwrap! (subst-typevar (typevar--IDX v-typeidx) tv-lst tu-lst)))
  subst-heaptype (heaptype--DEF v-rectype v-n) tv-lst tu-lst = (heaptype-deftype (subst-deftype (deftype--DEF v-rectype v-n) tv-lst tu-lst))
  subst-heaptype ht tv-lst tu-lst = ht

  {- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:344.1-344.112 -}
  {-# TERMINATING #-}
  subst-reftype : (v-reftype : reftype) (var-0-lst : (List typevar)) (var-1-lst : (List typeuse)) → reftype
  subst-reftype (reftype-REF null-opt ht) tv-lst tu-lst = (reftype-REF null-opt (subst-heaptype ht tv-lst tu-lst))
  subst-reftype v-reftype var-0-lst var-1-lst = default-val

  {- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:345.1-345.112 -}
  {-# TERMINATING #-}
  subst-valtype : (v-valtype : valtype) (var-0-lst : (List typevar)) (var-1-lst : (List typeuse)) → valtype
  subst-valtype valtype-I32 tv-lst tu-lst = (valtype-numtype (subst-numtype numtype-I32 tv-lst tu-lst))
  subst-valtype valtype-I64 tv-lst tu-lst = (valtype-numtype (subst-numtype numtype-I64 tv-lst tu-lst))
  subst-valtype valtype-F32 tv-lst tu-lst = (valtype-numtype (subst-numtype F32 tv-lst tu-lst))
  subst-valtype valtype-F64 tv-lst tu-lst = (valtype-numtype (subst-numtype F64 tv-lst tu-lst))
  subst-valtype valtype-V128 tv-lst tu-lst = (valtype-vectype (subst-vectype V128 tv-lst tu-lst))
  subst-valtype (REF null-opt v-heaptype) tv-lst tu-lst = (valtype-reftype (subst-reftype (reftype-REF null-opt v-heaptype) tv-lst tu-lst))
  subst-valtype valtype-BOT tv-lst tu-lst = valtype-BOT
  subst-valtype v-valtype var-0-lst var-1-lst = default-val

  {- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:348.1-348.112 -}
  {-# TERMINATING #-}
  subst-storagetype : (v-storagetype : storagetype) (var-0-lst : (List typevar)) (var-1-lst : (List typeuse)) → storagetype
  subst-storagetype storagetype-BOT tv-lst tu-lst = (storagetype-valtype (subst-valtype valtype-BOT tv-lst tu-lst))
  subst-storagetype (storagetype-REF null-opt v-heaptype) tv-lst tu-lst = (storagetype-valtype (subst-valtype (REF null-opt v-heaptype) tv-lst tu-lst))
  subst-storagetype storagetype-V128 tv-lst tu-lst = (storagetype-valtype (subst-valtype valtype-V128 tv-lst tu-lst))
  subst-storagetype storagetype-F64 tv-lst tu-lst = (storagetype-valtype (subst-valtype valtype-F64 tv-lst tu-lst))
  subst-storagetype storagetype-F32 tv-lst tu-lst = (storagetype-valtype (subst-valtype valtype-F32 tv-lst tu-lst))
  subst-storagetype storagetype-I64 tv-lst tu-lst = (storagetype-valtype (subst-valtype valtype-I64 tv-lst tu-lst))
  subst-storagetype storagetype-I32 tv-lst tu-lst = (storagetype-valtype (subst-valtype valtype-I32 tv-lst tu-lst))
  subst-storagetype I8 tv-lst tu-lst = (storagetype-packtype (subst-packtype packtype-I8 tv-lst tu-lst))
  subst-storagetype I16 tv-lst tu-lst = (storagetype-packtype (subst-packtype packtype-I16 tv-lst tu-lst))
  subst-storagetype v-storagetype var-0-lst var-1-lst = default-val

  {- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:349.1-349.112 -}
  {-# TERMINATING #-}
  subst-fieldtype : (v-fieldtype : fieldtype) (var-0-lst : (List typevar)) (var-1-lst : (List typeuse)) → fieldtype
  subst-fieldtype (mk-fieldtype mut-opt zt) tv-lst tu-lst = (mk-fieldtype mut-opt (subst-storagetype zt tv-lst tu-lst))
  subst-fieldtype v-fieldtype var-0-lst var-1-lst = default-val

  {- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:351.1-351.112 -}
  {-# TERMINATING #-}
  subst-comptype : (v-comptype : comptype) (var-0-lst : (List typevar)) (var-1-lst : (List typeuse)) → comptype
  subst-comptype (comptype-STRUCT (mk-list ft-lst)) tv-lst tu-lst = (comptype-STRUCT (mk-list (map (λ (ft : fieldtype) → (subst-fieldtype ft tv-lst tu-lst)) ft-lst)))
  subst-comptype (comptype-ARRAY ft) tv-lst tu-lst = (comptype-ARRAY (subst-fieldtype ft tv-lst tu-lst))
  subst-comptype (comptype-FUNC (mk-list t-1-lst) (mk-list t-2-lst)) tv-lst tu-lst = (comptype-FUNC (mk-list (map (λ (t-1 : valtype) → (subst-valtype t-1 tv-lst tu-lst)) t-1-lst)) (mk-list (map (λ (t-2 : valtype) → (subst-valtype t-2 tv-lst tu-lst)) t-2-lst)))
  subst-comptype v-comptype var-0-lst var-1-lst = default-val

  {- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:352.1-352.112 -}
  {-# TERMINATING #-}
  subst-subtype : (v-subtype : subtype) (var-0-lst : (List typevar)) (var-1-lst : (List typeuse)) → subtype
  subst-subtype (SUB final-opt tu'-lst ct) tv-lst tu-lst = (SUB final-opt (map (λ (tu' : typeuse) → (subst-typeuse tu' tv-lst tu-lst)) tu'-lst) (subst-comptype ct tv-lst tu-lst))
  subst-subtype v-subtype var-0-lst var-1-lst = default-val

  {- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:353.1-353.112 -}
  {-# TERMINATING #-}
  subst-rectype : (v-rectype : rectype) (var-0-lst : (List typevar)) (var-1-lst : (List typeuse)) → rectype
  subst-rectype (rectype-REC (mk-list st-lst)) tv-lst tu-lst = let (tv'-lst , tu'-lst) = (unwrap! (minus-recs tv-lst tu-lst)) in (rectype-REC (mk-list (map (λ (st : subtype) → (subst-subtype st tv'-lst tu'-lst)) st-lst)))
  subst-rectype v-rectype var-0-lst var-1-lst = default-val

  {- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:354.1-354.112 -}
  {-# TERMINATING #-}
  subst-deftype : (v-deftype : deftype) (var-0-lst : (List typevar)) (var-1-lst : (List typeuse)) → deftype
  subst-deftype (deftype--DEF qt i) tv-lst tu-lst = (deftype--DEF (subst-rectype qt tv-lst tu-lst) i)
  subst-deftype v-deftype var-0-lst var-1-lst = default-val

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:340.1-340.112 -}
{-# TERMINATING #-}
subst-addrtype : (v-addrtype : addrtype) (var-0-lst : (List typevar)) (var-1-lst : (List typeuse)) → addrtype
subst-addrtype at tv-lst tu-lst = at

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:356.1-356.112 -}
{-# TERMINATING #-}
subst-tagtype : (v-tagtype : tagtype) (var-0-lst : (List typevar)) (var-1-lst : (List typeuse)) → tagtype
subst-tagtype tu' tv-lst tu-lst = (subst-typeuse tu' tv-lst tu-lst)

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:357.1-357.112 -}
{-# TERMINATING #-}
subst-globaltype : (v-globaltype : globaltype) (var-0-lst : (List typevar)) (var-1-lst : (List typeuse)) → globaltype
subst-globaltype (mk-globaltype mut-opt t) tv-lst tu-lst = (mk-globaltype mut-opt (subst-valtype t tv-lst tu-lst))
subst-globaltype v-globaltype var-0-lst var-1-lst = default-val

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:358.1-358.112 -}
{-# TERMINATING #-}
subst-memtype : (v-memtype : memtype) (var-0-lst : (List typevar)) (var-1-lst : (List typeuse)) → memtype
subst-memtype (PAGE at lim) tv-lst tu-lst = (PAGE at lim)
subst-memtype v-memtype var-0-lst var-1-lst = default-val

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:359.1-359.112 -}
{-# TERMINATING #-}
subst-tabletype : (v-tabletype : tabletype) (var-0-lst : (List typevar)) (var-1-lst : (List typeuse)) → tabletype
subst-tabletype (mk-tabletype at lim rt) tv-lst tu-lst = (mk-tabletype at lim (subst-reftype rt tv-lst tu-lst))
subst-tabletype v-tabletype var-0-lst var-1-lst = default-val

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:361.1-361.112 -}
{-# TERMINATING #-}
subst-externtype : (v-externtype : externtype) (var-0-lst : (List typevar)) (var-1-lst : (List typeuse)) → externtype
subst-externtype (externtype-TAG jt) tv-lst tu-lst = (externtype-TAG (subst-tagtype jt tv-lst tu-lst))
subst-externtype (externtype-GLOBAL gt) tv-lst tu-lst = (externtype-GLOBAL (subst-globaltype gt tv-lst tu-lst))
subst-externtype (externtype-TABLE tt') tv-lst tu-lst = (externtype-TABLE (subst-tabletype tt' tv-lst tu-lst))
subst-externtype (externtype-MEM mt) tv-lst tu-lst = (externtype-MEM (subst-memtype mt tv-lst tu-lst))
subst-externtype (externtype-FUNC tu') tv-lst tu-lst = (externtype-FUNC (subst-typeuse tu' tv-lst tu-lst))
subst-externtype v-externtype var-0-lst var-1-lst = default-val

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:362.1-362.112 -}
{-# TERMINATING #-}
subst-moduletype : (v-moduletype : moduletype) (var-0-lst : (List typevar)) (var-1-lst : (List typeuse)) → moduletype
subst-moduletype (mk-moduletype xt-1-lst xt-2-lst) tv-lst tu-lst = (mk-moduletype (map (λ (xt-1 : externtype) → (subst-externtype xt-1 tv-lst tu-lst)) xt-1-lst) (map (λ (xt-2 : externtype) → (subst-externtype xt-2 tv-lst tu-lst)) xt-2-lst))
subst-moduletype v-moduletype var-0-lst var-1-lst = default-val

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:431.1-431.94 -}
{-# TERMINATING #-}
subst-all-valtype : (v-valtype : valtype) (var-0-lst : (List typeuse)) → valtype
subst-all-valtype t tu-lst = let v-n = length (tu-lst) in (subst-valtype t (mkseq (λ i → (typevar--IDX (mk-uN i))) v-n) tu-lst)

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:432.1-432.94 -}
{-# TERMINATING #-}
subst-all-reftype : (v-reftype : reftype) (var-0-lst : (List typeuse)) → reftype
subst-all-reftype rt tu-lst = let v-n = length (tu-lst) in (subst-reftype rt (mkseq (λ i → (typevar--IDX (mk-uN i))) v-n) tu-lst)

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:433.1-433.94 -}
{-# TERMINATING #-}
subst-all-deftype : (v-deftype : deftype) (var-0-lst : (List typeuse)) → deftype
subst-all-deftype dt tu-lst = let v-n = length (tu-lst) in (subst-deftype dt (mkseq (λ i → (typevar--IDX (mk-uN i))) v-n) tu-lst)

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:434.1-434.94 -}
{-# TERMINATING #-}
subst-all-tagtype : (v-tagtype : tagtype) (var-0-lst : (List typeuse)) → tagtype
subst-all-tagtype jt tu-lst = let v-n = length (tu-lst) in (subst-tagtype jt (mkseq (λ i → (typevar--IDX (mk-uN i))) v-n) tu-lst)

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:435.1-435.103 -}
{-# TERMINATING #-}
subst-all-globaltype : (v-globaltype : globaltype) (var-0-lst : (List typeuse)) → globaltype
subst-all-globaltype gt tu-lst = let v-n = length (tu-lst) in (subst-globaltype gt (mkseq (λ i → (typevar--IDX (mk-uN i))) v-n) tu-lst)

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:436.1-436.94 -}
{-# TERMINATING #-}
subst-all-memtype : (v-memtype : memtype) (var-0-lst : (List typeuse)) → memtype
subst-all-memtype mt tu-lst = let v-n = length (tu-lst) in (subst-memtype mt (mkseq (λ i → (typevar--IDX (mk-uN i))) v-n) tu-lst)

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:437.1-437.100 -}
{-# TERMINATING #-}
subst-all-tabletype : (v-tabletype : tabletype) (var-0-lst : (List typeuse)) → tabletype
subst-all-tabletype tt' tu-lst = let v-n = length (tu-lst) in (subst-tabletype tt' (mkseq (λ i → (typevar--IDX (mk-uN i))) v-n) tu-lst)

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:438.1-438.103 -}
{-# TERMINATING #-}
subst-all-externtype : (v-externtype : externtype) (var-0-lst : (List typeuse)) → externtype
subst-all-externtype xt tu-lst = let v-n = length (tu-lst) in (subst-externtype xt (mkseq (λ i → (typevar--IDX (mk-uN i))) v-n) tu-lst)

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:439.1-439.103 -}
{-# TERMINATING #-}
subst-all-moduletype : (v-moduletype : moduletype) (var-0-lst : (List typeuse)) → moduletype
subst-all-moduletype mmt tu-lst = let v-n = length (tu-lst) in (subst-moduletype mmt (mkseq (λ i → (typevar--IDX (mk-uN i))) v-n) tu-lst)

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:451.1-451.97 -}
{-# TERMINATING #-}
subst-all-deftypes : (var-0-lst : (List deftype)) (var-1-lst : (List typeuse)) → (List deftype)
subst-all-deftypes [] tu-lst = []
subst-all-deftypes (dt-1 ∷ dt-lst) tu-lst = (((subst-all-deftype dt-1 tu-lst) ∷ []) ++ (subst-all-deftypes dt-lst tu-lst))
subst-all-deftypes var-0-lst var-1-lst = []

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:458.1-458.88 -}
postulate rollrt : ∀ (v-typeidx : typeidx) (v-rectype : rectype) → rectype

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:459.1-459.90 -}
postulate unrollrt : ∀ (v-rectype : rectype) → rectype

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:460.1-460.90 -}
postulate rolldt : ∀ (v-typeidx : typeidx) (v-rectype : rectype) → (List deftype)

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:461.1-461.90 -}
{-# TERMINATING #-}
unrolldt : (v-deftype : deftype) → subtype
unrolldt (deftype--DEF v-rectype i) = ((as (rectype → subtype) (λ { ((rectype-REC (mk-list subtype-lst))) → (subtype-lst [ i ]!) })) ((unrollrt v-rectype)))
unrolldt v-deftype = default-val

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:474.1-474.36 -}
{-# TERMINATING #-}
free-addrtype : (v-addrtype : addrtype) → free
free-addrtype v-addrtype = record { TYPES = [] ; FUNCS = [] ; GLOBALS = [] ; TABLES = [] ; MEMS = [] ; ELEMS = [] ; DATAS = [] ; LOCALS = [] ; LABELS = [] ; TAGS = [] }

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:475.1-475.34 -}
{-# TERMINATING #-}
free-numtype : (v-numtype : numtype) → free
free-numtype v-numtype = record { TYPES = [] ; FUNCS = [] ; GLOBALS = [] ; TABLES = [] ; MEMS = [] ; ELEMS = [] ; DATAS = [] ; LOCALS = [] ; LABELS = [] ; TAGS = [] }

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:476.1-476.36 -}
{-# TERMINATING #-}
free-packtype : (v-packtype : packtype) → free
free-packtype v-packtype = record { TYPES = [] ; FUNCS = [] ; GLOBALS = [] ; TABLES = [] ; MEMS = [] ; ELEMS = [] ; DATAS = [] ; LOCALS = [] ; LABELS = [] ; TAGS = [] }

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:477.1-477.36 -}
{-# TERMINATING #-}
free-lanetype : (v-lanetype : lanetype) → free
free-lanetype lanetype-I32 = (free-numtype numtype-I32)
free-lanetype lanetype-I64 = (free-numtype numtype-I64)
free-lanetype lanetype-F32 = (free-numtype F32)
free-lanetype lanetype-F64 = (free-numtype F64)
free-lanetype lanetype-I8 = (free-packtype packtype-I8)
free-lanetype lanetype-I16 = (free-packtype packtype-I16)
free-lanetype v-lanetype = default-val

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:478.1-478.34 -}
{-# TERMINATING #-}
free-vectype : (v-vectype : vectype) → free
free-vectype v-vectype = record { TYPES = [] ; FUNCS = [] ; GLOBALS = [] ; TABLES = [] ; MEMS = [] ; ELEMS = [] ; DATAS = [] ; LOCALS = [] ; LABELS = [] ; TAGS = [] }

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:479.1-479.38 -}
{-# TERMINATING #-}
free-consttype : (v-consttype : consttype) → free
free-consttype consttype-I32 = (free-numtype numtype-I32)
free-consttype consttype-I64 = (free-numtype numtype-I64)
free-consttype consttype-F32 = (free-numtype F32)
free-consttype consttype-F64 = (free-numtype F64)
free-consttype consttype-V128 = (free-vectype V128)
free-consttype v-consttype = default-val

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:480.1-480.42 -}
{-# TERMINATING #-}
free-absheaptype : (v-absheaptype : absheaptype) → free
free-absheaptype v-absheaptype = record { TYPES = [] ; FUNCS = [] ; GLOBALS = [] ; TABLES = [] ; MEMS = [] ; ELEMS = [] ; DATAS = [] ; LOCALS = [] ; LABELS = [] ; TAGS = [] }

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:483.1-483.34 -}
{-# TERMINATING #-}
free-typevar : (v-typevar : typevar) → free
free-typevar (typevar--IDX v-typeidx) = (free-typeidx v-typeidx)
free-typevar (typevar-REC v-n) = record { TYPES = [] ; FUNCS = [] ; GLOBALS = [] ; TABLES = [] ; MEMS = [] ; ELEMS = [] ; DATAS = [] ; LOCALS = [] ; LABELS = [] ; TAGS = [] }
free-typevar v-typevar = default-val

mutual
  {- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:481.1-481.36 -}
  {-# TERMINATING #-}
  free-heaptype : (v-heaptype : heaptype) → free
  free-heaptype heaptype-ANY = (free-absheaptype ANY)
  free-heaptype heaptype-EQ = (free-absheaptype EQ)
  free-heaptype heaptype-I31 = (free-absheaptype I31)
  free-heaptype heaptype-STRUCT = (free-absheaptype STRUCT)
  free-heaptype heaptype-ARRAY = (free-absheaptype ARRAY)
  free-heaptype heaptype-NONE = (free-absheaptype NONE)
  free-heaptype heaptype-FUNC = (free-absheaptype absheaptype-FUNC)
  free-heaptype heaptype-NOFUNC = (free-absheaptype NOFUNC)
  free-heaptype heaptype-EXN = (free-absheaptype EXN)
  free-heaptype heaptype-NOEXN = (free-absheaptype NOEXN)
  free-heaptype heaptype-EXTERN = (free-absheaptype EXTERN)
  free-heaptype heaptype-NOEXTERN = (free-absheaptype NOEXTERN)
  free-heaptype heaptype-BOT = (free-absheaptype BOT)
  free-heaptype (heaptype-REC n-0) = (free-typeuse (REC n-0))
  free-heaptype (heaptype--DEF v-rectype v-n) = (free-typeuse (-DEF v-rectype v-n))
  free-heaptype (heaptype--IDX v-typeidx) = (free-typeuse (-IDX v-typeidx))
  free-heaptype v-heaptype = default-val

  {- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:482.1-482.34 -}
  {-# TERMINATING #-}
  free-reftype : (v-reftype : reftype) → free
  free-reftype (reftype-REF null-opt v-heaptype) = (free-heaptype v-heaptype)
  free-reftype v-reftype = default-val

  {- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:484.1-484.34 -}
  {-# TERMINATING #-}
  free-typeuse : (v-typeuse : typeuse) → free
  free-typeuse (REC v-n) = (free-typevar (typevar-REC v-n))
  free-typeuse (-IDX v-typeidx) = (free-typevar (typevar--IDX v-typeidx))
  free-typeuse (-DEF v-rectype v-n) = (free-deftype (deftype--DEF v-rectype v-n))
  free-typeuse v-typeuse = default-val

  {- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:485.1-485.34 -}
  {-# TERMINATING #-}
  free-valtype : (v-valtype : valtype) → free
  free-valtype valtype-I32 = (free-numtype numtype-I32)
  free-valtype valtype-I64 = (free-numtype numtype-I64)
  free-valtype valtype-F32 = (free-numtype F32)
  free-valtype valtype-F64 = (free-numtype F64)
  free-valtype valtype-V128 = (free-vectype V128)
  free-valtype (REF null-opt v-heaptype) = (free-reftype (reftype-REF null-opt v-heaptype))
  free-valtype valtype-BOT = record { TYPES = [] ; FUNCS = [] ; GLOBALS = [] ; TABLES = [] ; MEMS = [] ; ELEMS = [] ; DATAS = [] ; LOCALS = [] ; LABELS = [] ; TAGS = [] }
  free-valtype v-valtype = default-val

  {- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:487.1-487.40 -}
  {-# TERMINATING #-}
  free-resulttype : (v-resulttype : resulttype) → free
  free-resulttype (mk-list valtype-lst) = (free-list (map (λ (v-valtype : valtype) → (free-valtype v-valtype)) valtype-lst))
  free-resulttype v-resulttype = default-val

  {- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:488.1-488.42 -}
  {-# TERMINATING #-}
  free-storagetype : (v-storagetype : storagetype) → free
  free-storagetype storagetype-BOT = (free-valtype valtype-BOT)
  free-storagetype (storagetype-REF null-opt v-heaptype) = (free-valtype (REF null-opt v-heaptype))
  free-storagetype storagetype-V128 = (free-valtype valtype-V128)
  free-storagetype storagetype-F64 = (free-valtype valtype-F64)
  free-storagetype storagetype-F32 = (free-valtype valtype-F32)
  free-storagetype storagetype-I64 = (free-valtype valtype-I64)
  free-storagetype storagetype-I32 = (free-valtype valtype-I32)
  free-storagetype I8 = (free-packtype packtype-I8)
  free-storagetype I16 = (free-packtype packtype-I16)
  free-storagetype v-storagetype = default-val

  {- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:489.1-489.38 -}
  {-# TERMINATING #-}
  free-fieldtype : (v-fieldtype : fieldtype) → free
  free-fieldtype (mk-fieldtype mut-opt v-storagetype) = (free-storagetype v-storagetype)
  free-fieldtype v-fieldtype = default-val

  {- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:490.1-490.36 -}
  {-# TERMINATING #-}
  free-comptype : (v-comptype : comptype) → free
  free-comptype (comptype-STRUCT (mk-list fieldtype-lst)) = (free-list (map (λ (v-fieldtype : fieldtype) → (free-fieldtype v-fieldtype)) fieldtype-lst))
  free-comptype (comptype-ARRAY v-fieldtype) = (free-fieldtype v-fieldtype)
  free-comptype (comptype-FUNC resulttype-1 resulttype-2) = ((free-resulttype resulttype-1) ⧺ (free-resulttype resulttype-2))
  free-comptype v-comptype = default-val

  {- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:491.1-491.34 -}
  {-# TERMINATING #-}
  free-subtype : (v-subtype : subtype) → free
  free-subtype (SUB final-opt typeuse-lst v-comptype) = ((free-list (map (λ (v-typeuse : typeuse) → (free-typeuse v-typeuse)) typeuse-lst)) ⧺ (free-comptype v-comptype))
  free-subtype v-subtype = default-val

  {- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:492.1-492.34 -}
  {-# TERMINATING #-}
  free-rectype : (v-rectype : rectype) → free
  free-rectype (rectype-REC (mk-list subtype-lst)) = (free-list (map (λ (v-subtype : subtype) → (free-subtype v-subtype)) subtype-lst))
  free-rectype v-rectype = default-val

  {- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:520.1-520.34 -}
  {-# TERMINATING #-}
  free-deftype : (v-deftype : deftype) → free
  free-deftype (deftype--DEF v-rectype v-n) = (free-rectype v-rectype)
  free-deftype v-deftype = default-val

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:494.1-494.49 -}
{-# TERMINATING #-}
free-tagtype : (v-tagtype : tagtype) → (Maybe free)
free-tagtype (-DEF v-rectype v-n) = (just (free-deftype (deftype--DEF v-rectype v-n)))
free-tagtype x0 = nothing

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:495.1-495.40 -}
{-# TERMINATING #-}
free-globaltype : (v-globaltype : globaltype) → free
free-globaltype (mk-globaltype mut-opt v-valtype) = (free-valtype v-valtype)
free-globaltype v-globaltype = default-val

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:496.1-496.34 -}
{-# TERMINATING #-}
free-memtype : (v-memtype : memtype) → free
free-memtype (PAGE v-addrtype v-limits) = (free-addrtype v-addrtype)
free-memtype v-memtype = default-val

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:497.1-497.38 -}
{-# TERMINATING #-}
free-tabletype : (v-tabletype : tabletype) → free
free-tabletype (mk-tabletype v-addrtype v-limits v-reftype) = ((free-addrtype v-addrtype) ⧺ (free-reftype v-reftype))
free-tabletype v-tabletype = default-val

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:498.1-498.36 -}
{-# TERMINATING #-}
free-datatype : (v-datatype : datatype) → free
free-datatype OK = record { TYPES = [] ; FUNCS = [] ; GLOBALS = [] ; TABLES = [] ; MEMS = [] ; ELEMS = [] ; DATAS = [] ; LOCALS = [] ; LABELS = [] ; TAGS = [] }
free-datatype v-datatype = default-val

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:499.1-499.36 -}
{-# TERMINATING #-}
free-elemtype : (v-elemtype : elemtype) → free
free-elemtype v-reftype = (free-reftype v-reftype)

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:500.1-500.54 -}
{-# TERMINATING #-}
free-externtype : (v-externtype : externtype) → (Maybe free)
free-externtype (externtype-TAG v-tagtype) = (free-tagtype v-tagtype)
free-externtype (externtype-GLOBAL v-globaltype) = (just (free-globaltype v-globaltype))
free-externtype (externtype-MEM v-memtype) = (just (free-memtype v-memtype))
free-externtype (externtype-TABLE v-tabletype) = (just (free-tabletype v-tabletype))
free-externtype (externtype-FUNC v-typeuse) = (just (free-typeuse v-typeuse))
free-externtype x0 = nothing

{- Auxiliary Definition at: ../specification/wasm-3.0/1.2-syntax.types.spectec:501.1-501.40 -}
{-# TERMINATING #-}
free-moduletype : (v-moduletype : moduletype) → free
free-moduletype (mk-moduletype externtype-1-lst externtype-2-lst) = ((free-list (map (λ (externtype-1 : externtype) → (unwrap! (free-externtype externtype-1))) externtype-1-lst)) ⧺ (free-list (map (λ (externtype-2 : externtype) → (unwrap! (free-externtype externtype-2))) externtype-2-lst)))
free-moduletype v-moduletype = default-val

{- Type Family Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:7.1-7.21 -}
num- : (v-numtype : numtype) → Set
num- numtype-I32 = (uN-fam0 (32))
num- numtype-I64 = (uN-fam0 (64))
num- F32 = (fN-fam0 (32))
num- F64 = (fN-fam0 (64))
num- _ = ⊤

inh-num--fun : (v-numtype : numtype) → Inhabited (num- v-numtype)
inh-num--fun numtype-I32 = record { default-val = (Inhabited.default-val (inh-iN-fun (sizenn (numtype-addrtype I32)))) }
inh-num--fun numtype-I64 = record { default-val = (Inhabited.default-val (inh-iN-fun (sizenn (numtype-addrtype I64)))) }
inh-num--fun F32 = record { default-val = (Inhabited.default-val (inh-fN-fun (sizenn (numtype-Fnn Fnn-F32)))) }
inh-num--fun F64 = record { default-val = (Inhabited.default-val (inh-fN-fun (sizenn (numtype-Fnn Fnn-F64)))) }

{- Type Alias Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:11.1-11.38 -}
pack- : (v-Pnn : Pnn) → Set
pack- v-Pnn = (uN-fam0 ((psize v-Pnn)))
pack- _ = ⊤

inh-pack--fun : (v-Pnn : Pnn) → Inhabited (pack- v-Pnn)
inh-pack--fun v-Pnn = record { default-val = (Inhabited.default-val (inh-iN-fun (psizenn v-Pnn))) }

{- Type Family Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:13.1-13.23 -}
lane- : (v-lanetype : lanetype) → Set
lane- lanetype-I32 = (uN-fam0 (32))
lane- lanetype-I64 = (uN-fam0 (64))
lane- lanetype-F32 = (fN-fam0 (32))
lane- lanetype-F64 = (fN-fam0 (64))
lane- lanetype-I8 = (uN-fam0 (8))
lane- lanetype-I16 = (uN-fam0 (16))
lane- lanetype-I32 = (uN-fam0 (32))
lane- lanetype-I64 = (uN-fam0 (64))
lane- lanetype-I8 = (uN-fam0 (8))
lane- lanetype-I16 = (uN-fam0 (16))
lane- _ = ⊤

inh-lane--fun : (v-lanetype : lanetype) → Inhabited (lane- v-lanetype)
inh-lane--fun lanetype-I32 = record { default-val = (Inhabited.default-val (inh-num--fun numtype-I32)) }
inh-lane--fun lanetype-I64 = record { default-val = (Inhabited.default-val (inh-num--fun numtype-I64)) }
inh-lane--fun lanetype-F32 = record { default-val = (Inhabited.default-val (inh-num--fun F32)) }
inh-lane--fun lanetype-F64 = record { default-val = (Inhabited.default-val (inh-num--fun F64)) }
inh-lane--fun lanetype-I8 = record { default-val = (Inhabited.default-val (inh-pack--fun packtype-I8)) }
inh-lane--fun lanetype-I16 = record { default-val = (Inhabited.default-val (inh-pack--fun packtype-I16)) }
inh-lane--fun lanetype-I32 = record { default-val = (Inhabited.default-val (inh-iN-fun (lsize (lanetype-Jnn Jnn-I32)))) }
inh-lane--fun lanetype-I64 = record { default-val = (Inhabited.default-val (inh-iN-fun (lsize (lanetype-Jnn Jnn-I64)))) }
inh-lane--fun lanetype-I8 = record { default-val = (Inhabited.default-val (inh-iN-fun (lsize (lanetype-Jnn Jnn-I8)))) }
inh-lane--fun lanetype-I16 = record { default-val = (Inhabited.default-val (inh-iN-fun (lsize (lanetype-Jnn Jnn-I16)))) }

{- Type Alias Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:18.1-18.35 -}
vec- : (v-Vnn : Vnn) → Set
vec- v-Vnn = (uN-fam0 ((vsize v-Vnn)))
vec- _ = ⊤

inh-vec--fun : (v-Vnn : Vnn) → Inhabited (vec- v-Vnn)
inh-vec--fun v-Vnn = record { default-val = (Inhabited.default-val (inh-vN-fun (vsize v-Vnn))) }

{- Type Family Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:20.1-20.25 -}
lit- : (v-storagetype : storagetype) → Set
lit- storagetype-I32 = (uN-fam0 (32))
lit- storagetype-I64 = (uN-fam0 (64))
lit- storagetype-F32 = (fN-fam0 (32))
lit- storagetype-F64 = (fN-fam0 (64))
lit- storagetype-V128 = (uN-fam0 (128))
lit- I8 = (uN-fam0 (8))
lit- I16 = (uN-fam0 (16))
lit- _ = ⊤

inh-lit--fun : (v-storagetype : storagetype) → Inhabited (lit- v-storagetype)
inh-lit--fun storagetype-I32 = record { default-val = (Inhabited.default-val (inh-num--fun numtype-I32)) }
inh-lit--fun storagetype-I64 = record { default-val = (Inhabited.default-val (inh-num--fun numtype-I64)) }
inh-lit--fun storagetype-F32 = record { default-val = (Inhabited.default-val (inh-num--fun F32)) }
inh-lit--fun storagetype-F64 = record { default-val = (Inhabited.default-val (inh-num--fun F64)) }
inh-lit--fun storagetype-V128 = record { default-val = (Inhabited.default-val (inh-vec--fun V128)) }
inh-lit--fun I8 = record { default-val = (Inhabited.default-val (inh-pack--fun packtype-I8)) }
inh-lit--fun I16 = record { default-val = (Inhabited.default-val (inh-pack--fun packtype-I16)) }
inh-lit--fun (storagetype-REF _ _) = record { default-val = tt }
inh-lit--fun storagetype-BOT = record { default-val = tt }

{- Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:28.1-28.56 -}
data sz : Set where
  mk-sz : (i : ℕ) → sz {- 1 premise(s) dropped -}

eq-sz-fun : sz → sz → Bool
eq-sz-fun (mk-sz x0) (mk-sz y0) = (x0 =? y0)
instance
  haseq-sz : HasEq sz
  haseq-sz = record { _=?_ = eq-sz-fun }

{- Auxiliary Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:28.1-28.56 -}
{-# TERMINATING #-}
proj-sz-0 : (x : sz) → (ℕ)
proj-sz-0 (mk-sz v-num-0) = (v-num-0)
proj-sz-0 x = (default-val)

instance
  proj-sz-0-coercion : Coerce sz (ℕ)
  proj-sz-0-coercion = record { coerce = proj-sz-0 }

{- Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:29.1-29.42 -}
data sx : Set where
  U : sx
  S : sx

instance
  inh-sx : Inhabited sx
  inh-sx = record { default-val = U }

eq-sx-fun : sx → sx → Bool
eq-sx-fun U U = true
eq-sx-fun S S = true
eq-sx-fun _ _ = false
instance
  haseq-sx : HasEq sx
  haseq-sx = record { _=?_ = eq-sx-fun }

{- Type Family Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:31.1-31.22 -}
data unop--fam0 : Set where
  CLZ : unop--fam0
  CTZ : unop--fam0
  POPCNT : unop--fam0
  EXTEND : (sz-4990 : sz) → unop--fam0 {- 1 premise(s) dropped -}

eq-unop--fam0-fun : unop--fam0 → unop--fam0 → Bool
eq-unop--fam0-fun CLZ CLZ = true
eq-unop--fam0-fun CTZ CTZ = true
eq-unop--fam0-fun POPCNT POPCNT = true
eq-unop--fam0-fun (EXTEND x0) (EXTEND y0) = (x0 =? y0)
eq-unop--fam0-fun _ _ = false
instance
  haseq-unop--fam0 : HasEq unop--fam0
  haseq-unop--fam0 = record { _=?_ = eq-unop--fam0-fun }

data unop--fam1 : Set where
  CLZ : unop--fam1
  CTZ : unop--fam1
  POPCNT : unop--fam1
  EXTEND : (sz-4991 : sz) → unop--fam1 {- 1 premise(s) dropped -}

eq-unop--fam1-fun : unop--fam1 → unop--fam1 → Bool
eq-unop--fam1-fun CLZ CLZ = true
eq-unop--fam1-fun CTZ CTZ = true
eq-unop--fam1-fun POPCNT POPCNT = true
eq-unop--fam1-fun (EXTEND x0) (EXTEND y0) = (x0 =? y0)
eq-unop--fam1-fun _ _ = false
instance
  haseq-unop--fam1 : HasEq unop--fam1
  haseq-unop--fam1 = record { _=?_ = eq-unop--fam1-fun }

data unop--fam2 : Set where
  ABS : unop--fam2
  unop--NEG : unop--fam2
  SQRT : unop--fam2
  CEIL : unop--fam2
  FLOOR : unop--fam2
  TRUNC : unop--fam2
  NEAREST : unop--fam2

eq-unop--fam2-fun : unop--fam2 → unop--fam2 → Bool
eq-unop--fam2-fun ABS ABS = true
eq-unop--fam2-fun unop--NEG unop--NEG = true
eq-unop--fam2-fun SQRT SQRT = true
eq-unop--fam2-fun CEIL CEIL = true
eq-unop--fam2-fun FLOOR FLOOR = true
eq-unop--fam2-fun TRUNC TRUNC = true
eq-unop--fam2-fun NEAREST NEAREST = true
eq-unop--fam2-fun _ _ = false
instance
  haseq-unop--fam2 : HasEq unop--fam2
  haseq-unop--fam2 = record { _=?_ = eq-unop--fam2-fun }

data unop--fam3 : Set where
  ABS : unop--fam3
  unop--NEG : unop--fam3
  SQRT : unop--fam3
  CEIL : unop--fam3
  FLOOR : unop--fam3
  TRUNC : unop--fam3
  NEAREST : unop--fam3

eq-unop--fam3-fun : unop--fam3 → unop--fam3 → Bool
eq-unop--fam3-fun ABS ABS = true
eq-unop--fam3-fun unop--NEG unop--NEG = true
eq-unop--fam3-fun SQRT SQRT = true
eq-unop--fam3-fun CEIL CEIL = true
eq-unop--fam3-fun FLOOR FLOOR = true
eq-unop--fam3-fun TRUNC TRUNC = true
eq-unop--fam3-fun NEAREST NEAREST = true
eq-unop--fam3-fun _ _ = false
instance
  haseq-unop--fam3 : HasEq unop--fam3
  haseq-unop--fam3 = record { _=?_ = eq-unop--fam3-fun }

unop- : (v-numtype : numtype) → Set
unop- numtype-I32 = unop--fam0
unop- numtype-I64 = unop--fam1
unop- F32 = unop--fam2
unop- F64 = unop--fam3
unop- _ = ⊤

{- Type Family Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:35.1-35.23 -}
data binop--fam0 : Set where
  ADD : binop--fam0
  binop--SUB : binop--fam0
  MUL : binop--fam0
  DIV : (sx-51486 : sx) → binop--fam0
  REM : (sx-51487 : sx) → binop--fam0
  AND : binop--fam0
  OR : binop--fam0
  XOR : binop--fam0
  SHL : binop--fam0
  SHR : (sx-51488 : sx) → binop--fam0
  ROTL : binop--fam0
  ROTR : binop--fam0

eq-binop--fam0-fun : binop--fam0 → binop--fam0 → Bool
eq-binop--fam0-fun ADD ADD = true
eq-binop--fam0-fun binop--SUB binop--SUB = true
eq-binop--fam0-fun MUL MUL = true
eq-binop--fam0-fun (DIV x0) (DIV y0) = (x0 =? y0)
eq-binop--fam0-fun (REM x0) (REM y0) = (x0 =? y0)
eq-binop--fam0-fun AND AND = true
eq-binop--fam0-fun OR OR = true
eq-binop--fam0-fun XOR XOR = true
eq-binop--fam0-fun SHL SHL = true
eq-binop--fam0-fun (SHR x0) (SHR y0) = (x0 =? y0)
eq-binop--fam0-fun ROTL ROTL = true
eq-binop--fam0-fun ROTR ROTR = true
eq-binop--fam0-fun _ _ = false
instance
  haseq-binop--fam0 : HasEq binop--fam0
  haseq-binop--fam0 = record { _=?_ = eq-binop--fam0-fun }

data binop--fam1 : Set where
  ADD : binop--fam1
  binop--SUB : binop--fam1
  MUL : binop--fam1
  DIV : (sx-51489 : sx) → binop--fam1
  REM : (sx-51490 : sx) → binop--fam1
  AND : binop--fam1
  OR : binop--fam1
  XOR : binop--fam1
  SHL : binop--fam1
  SHR : (sx-51491 : sx) → binop--fam1
  ROTL : binop--fam1
  ROTR : binop--fam1

eq-binop--fam1-fun : binop--fam1 → binop--fam1 → Bool
eq-binop--fam1-fun ADD ADD = true
eq-binop--fam1-fun binop--SUB binop--SUB = true
eq-binop--fam1-fun MUL MUL = true
eq-binop--fam1-fun (DIV x0) (DIV y0) = (x0 =? y0)
eq-binop--fam1-fun (REM x0) (REM y0) = (x0 =? y0)
eq-binop--fam1-fun AND AND = true
eq-binop--fam1-fun OR OR = true
eq-binop--fam1-fun XOR XOR = true
eq-binop--fam1-fun SHL SHL = true
eq-binop--fam1-fun (SHR x0) (SHR y0) = (x0 =? y0)
eq-binop--fam1-fun ROTL ROTL = true
eq-binop--fam1-fun ROTR ROTR = true
eq-binop--fam1-fun _ _ = false
instance
  haseq-binop--fam1 : HasEq binop--fam1
  haseq-binop--fam1 = record { _=?_ = eq-binop--fam1-fun }

data binop--fam2 : Set where
  ADD : binop--fam2
  binop--SUB : binop--fam2
  MUL : binop--fam2
  DIV : binop--fam2
  MIN : binop--fam2
  MAX : binop--fam2
  COPYSIGN : binop--fam2

eq-binop--fam2-fun : binop--fam2 → binop--fam2 → Bool
eq-binop--fam2-fun ADD ADD = true
eq-binop--fam2-fun binop--SUB binop--SUB = true
eq-binop--fam2-fun MUL MUL = true
eq-binop--fam2-fun DIV DIV = true
eq-binop--fam2-fun MIN MIN = true
eq-binop--fam2-fun MAX MAX = true
eq-binop--fam2-fun COPYSIGN COPYSIGN = true
eq-binop--fam2-fun _ _ = false
instance
  haseq-binop--fam2 : HasEq binop--fam2
  haseq-binop--fam2 = record { _=?_ = eq-binop--fam2-fun }

data binop--fam3 : Set where
  ADD : binop--fam3
  binop--SUB : binop--fam3
  MUL : binop--fam3
  DIV : binop--fam3
  MIN : binop--fam3
  MAX : binop--fam3
  COPYSIGN : binop--fam3

eq-binop--fam3-fun : binop--fam3 → binop--fam3 → Bool
eq-binop--fam3-fun ADD ADD = true
eq-binop--fam3-fun binop--SUB binop--SUB = true
eq-binop--fam3-fun MUL MUL = true
eq-binop--fam3-fun DIV DIV = true
eq-binop--fam3-fun MIN MIN = true
eq-binop--fam3-fun MAX MAX = true
eq-binop--fam3-fun COPYSIGN COPYSIGN = true
eq-binop--fam3-fun _ _ = false
instance
  haseq-binop--fam3 : HasEq binop--fam3
  haseq-binop--fam3 = record { _=?_ = eq-binop--fam3-fun }

binop- : (v-numtype : numtype) → Set
binop- numtype-I32 = binop--fam0
binop- numtype-I64 = binop--fam1
binop- F32 = binop--fam2
binop- F64 = binop--fam3
binop- _ = ⊤

{- Type Family Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:42.1-42.24 -}
data testop--fam0 : Set where
  EQZ : testop--fam0

eq-testop--fam0-fun : testop--fam0 → testop--fam0 → Bool
eq-testop--fam0-fun EQZ EQZ = true
instance
  haseq-testop--fam0 : HasEq testop--fam0
  haseq-testop--fam0 = record { _=?_ = eq-testop--fam0-fun }

data testop--fam1 : Set where
  EQZ : testop--fam1

eq-testop--fam1-fun : testop--fam1 → testop--fam1 → Bool
eq-testop--fam1-fun EQZ EQZ = true
instance
  haseq-testop--fam1 : HasEq testop--fam1
  haseq-testop--fam1 = record { _=?_ = eq-testop--fam1-fun }

testop- : (v-numtype : numtype) → Set
testop- numtype-I32 = testop--fam0
testop- numtype-I64 = testop--fam1
testop- _ = ⊤

{- Type Family Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:46.1-46.23 -}
data relop--fam0 : Set where
  relop--EQ : relop--fam0
  NE : relop--fam0
  LT : (sx-51492 : sx) → relop--fam0
  GT : (sx-51493 : sx) → relop--fam0
  LE : (sx-51494 : sx) → relop--fam0
  GE : (sx-51495 : sx) → relop--fam0

eq-relop--fam0-fun : relop--fam0 → relop--fam0 → Bool
eq-relop--fam0-fun relop--EQ relop--EQ = true
eq-relop--fam0-fun NE NE = true
eq-relop--fam0-fun (LT x0) (LT y0) = (x0 =? y0)
eq-relop--fam0-fun (GT x0) (GT y0) = (x0 =? y0)
eq-relop--fam0-fun (LE x0) (LE y0) = (x0 =? y0)
eq-relop--fam0-fun (GE x0) (GE y0) = (x0 =? y0)
eq-relop--fam0-fun _ _ = false
instance
  haseq-relop--fam0 : HasEq relop--fam0
  haseq-relop--fam0 = record { _=?_ = eq-relop--fam0-fun }

data relop--fam1 : Set where
  relop--EQ : relop--fam1
  NE : relop--fam1
  LT : (sx-51496 : sx) → relop--fam1
  GT : (sx-51497 : sx) → relop--fam1
  LE : (sx-51498 : sx) → relop--fam1
  GE : (sx-51499 : sx) → relop--fam1

eq-relop--fam1-fun : relop--fam1 → relop--fam1 → Bool
eq-relop--fam1-fun relop--EQ relop--EQ = true
eq-relop--fam1-fun NE NE = true
eq-relop--fam1-fun (LT x0) (LT y0) = (x0 =? y0)
eq-relop--fam1-fun (GT x0) (GT y0) = (x0 =? y0)
eq-relop--fam1-fun (LE x0) (LE y0) = (x0 =? y0)
eq-relop--fam1-fun (GE x0) (GE y0) = (x0 =? y0)
eq-relop--fam1-fun _ _ = false
instance
  haseq-relop--fam1 : HasEq relop--fam1
  haseq-relop--fam1 = record { _=?_ = eq-relop--fam1-fun }

data relop--fam2 : Set where
  relop--EQ : relop--fam2
  NE : relop--fam2
  LT : relop--fam2
  GT : relop--fam2
  LE : relop--fam2
  GE : relop--fam2

eq-relop--fam2-fun : relop--fam2 → relop--fam2 → Bool
eq-relop--fam2-fun relop--EQ relop--EQ = true
eq-relop--fam2-fun NE NE = true
eq-relop--fam2-fun LT LT = true
eq-relop--fam2-fun GT GT = true
eq-relop--fam2-fun LE LE = true
eq-relop--fam2-fun GE GE = true
eq-relop--fam2-fun _ _ = false
instance
  haseq-relop--fam2 : HasEq relop--fam2
  haseq-relop--fam2 = record { _=?_ = eq-relop--fam2-fun }

data relop--fam3 : Set where
  relop--EQ : relop--fam3
  NE : relop--fam3
  LT : relop--fam3
  GT : relop--fam3
  LE : relop--fam3
  GE : relop--fam3

eq-relop--fam3-fun : relop--fam3 → relop--fam3 → Bool
eq-relop--fam3-fun relop--EQ relop--EQ = true
eq-relop--fam3-fun NE NE = true
eq-relop--fam3-fun LT LT = true
eq-relop--fam3-fun GT GT = true
eq-relop--fam3-fun LE LE = true
eq-relop--fam3-fun GE GE = true
eq-relop--fam3-fun _ _ = false
instance
  haseq-relop--fam3 : HasEq relop--fam3
  haseq-relop--fam3 = record { _=?_ = eq-relop--fam3-fun }

relop- : (v-numtype : numtype) → Set
relop- numtype-I32 = relop--fam0
relop- numtype-I64 = relop--fam1
relop- F32 = relop--fam2
relop- F64 = relop--fam3
relop- _ = ⊤

{- Type Family Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:55.1-55.37 -}
data cvtop---fam0 : Set where
  cvtop---EXTEND : (sx-51500 : sx) → cvtop---fam0 {- 1 premise(s) dropped -}
  WRAP : cvtop---fam0 {- 1 premise(s) dropped -}

eq-cvtop---fam0-fun : cvtop---fam0 → cvtop---fam0 → Bool
eq-cvtop---fam0-fun (cvtop---EXTEND x0) (cvtop---EXTEND y0) = (x0 =? y0)
eq-cvtop---fam0-fun WRAP WRAP = true
eq-cvtop---fam0-fun _ _ = false
instance
  haseq-cvtop---fam0 : HasEq cvtop---fam0
  haseq-cvtop---fam0 = record { _=?_ = eq-cvtop---fam0-fun }

data cvtop---fam1 : Set where
  cvtop---EXTEND : (sx-51501 : sx) → cvtop---fam1 {- 1 premise(s) dropped -}
  WRAP : cvtop---fam1 {- 1 premise(s) dropped -}

eq-cvtop---fam1-fun : cvtop---fam1 → cvtop---fam1 → Bool
eq-cvtop---fam1-fun (cvtop---EXTEND x0) (cvtop---EXTEND y0) = (x0 =? y0)
eq-cvtop---fam1-fun WRAP WRAP = true
eq-cvtop---fam1-fun _ _ = false
instance
  haseq-cvtop---fam1 : HasEq cvtop---fam1
  haseq-cvtop---fam1 = record { _=?_ = eq-cvtop---fam1-fun }

data cvtop---fam2 : Set where
  cvtop---EXTEND : (sx-51502 : sx) → cvtop---fam2 {- 1 premise(s) dropped -}
  WRAP : cvtop---fam2 {- 1 premise(s) dropped -}

eq-cvtop---fam2-fun : cvtop---fam2 → cvtop---fam2 → Bool
eq-cvtop---fam2-fun (cvtop---EXTEND x0) (cvtop---EXTEND y0) = (x0 =? y0)
eq-cvtop---fam2-fun WRAP WRAP = true
eq-cvtop---fam2-fun _ _ = false
instance
  haseq-cvtop---fam2 : HasEq cvtop---fam2
  haseq-cvtop---fam2 = record { _=?_ = eq-cvtop---fam2-fun }

data cvtop---fam3 : Set where
  cvtop---EXTEND : (sx-51503 : sx) → cvtop---fam3 {- 1 premise(s) dropped -}
  WRAP : cvtop---fam3 {- 1 premise(s) dropped -}

eq-cvtop---fam3-fun : cvtop---fam3 → cvtop---fam3 → Bool
eq-cvtop---fam3-fun (cvtop---EXTEND x0) (cvtop---EXTEND y0) = (x0 =? y0)
eq-cvtop---fam3-fun WRAP WRAP = true
eq-cvtop---fam3-fun _ _ = false
instance
  haseq-cvtop---fam3 : HasEq cvtop---fam3
  haseq-cvtop---fam3 = record { _=?_ = eq-cvtop---fam3-fun }

data cvtop---fam4 : Set where
  CONVERT : (sx-51504 : sx) → cvtop---fam4
  REINTERPRET : cvtop---fam4 {- 1 premise(s) dropped -}

eq-cvtop---fam4-fun : cvtop---fam4 → cvtop---fam4 → Bool
eq-cvtop---fam4-fun (CONVERT x0) (CONVERT y0) = (x0 =? y0)
eq-cvtop---fam4-fun REINTERPRET REINTERPRET = true
eq-cvtop---fam4-fun _ _ = false
instance
  haseq-cvtop---fam4 : HasEq cvtop---fam4
  haseq-cvtop---fam4 = record { _=?_ = eq-cvtop---fam4-fun }

data cvtop---fam5 : Set where
  CONVERT : (sx-51505 : sx) → cvtop---fam5
  REINTERPRET : cvtop---fam5 {- 1 premise(s) dropped -}

eq-cvtop---fam5-fun : cvtop---fam5 → cvtop---fam5 → Bool
eq-cvtop---fam5-fun (CONVERT x0) (CONVERT y0) = (x0 =? y0)
eq-cvtop---fam5-fun REINTERPRET REINTERPRET = true
eq-cvtop---fam5-fun _ _ = false
instance
  haseq-cvtop---fam5 : HasEq cvtop---fam5
  haseq-cvtop---fam5 = record { _=?_ = eq-cvtop---fam5-fun }

data cvtop---fam6 : Set where
  CONVERT : (sx-51506 : sx) → cvtop---fam6
  REINTERPRET : cvtop---fam6 {- 1 premise(s) dropped -}

eq-cvtop---fam6-fun : cvtop---fam6 → cvtop---fam6 → Bool
eq-cvtop---fam6-fun (CONVERT x0) (CONVERT y0) = (x0 =? y0)
eq-cvtop---fam6-fun REINTERPRET REINTERPRET = true
eq-cvtop---fam6-fun _ _ = false
instance
  haseq-cvtop---fam6 : HasEq cvtop---fam6
  haseq-cvtop---fam6 = record { _=?_ = eq-cvtop---fam6-fun }

data cvtop---fam7 : Set where
  CONVERT : (sx-51507 : sx) → cvtop---fam7
  REINTERPRET : cvtop---fam7 {- 1 premise(s) dropped -}

eq-cvtop---fam7-fun : cvtop---fam7 → cvtop---fam7 → Bool
eq-cvtop---fam7-fun (CONVERT x0) (CONVERT y0) = (x0 =? y0)
eq-cvtop---fam7-fun REINTERPRET REINTERPRET = true
eq-cvtop---fam7-fun _ _ = false
instance
  haseq-cvtop---fam7 : HasEq cvtop---fam7
  haseq-cvtop---fam7 = record { _=?_ = eq-cvtop---fam7-fun }

data cvtop---fam8 : Set where
  cvtop---TRUNC : (sx-51508 : sx) → cvtop---fam8
  TRUNC-SAT : (sx-51509 : sx) → cvtop---fam8
  REINTERPRET : cvtop---fam8 {- 1 premise(s) dropped -}

eq-cvtop---fam8-fun : cvtop---fam8 → cvtop---fam8 → Bool
eq-cvtop---fam8-fun (cvtop---TRUNC x0) (cvtop---TRUNC y0) = (x0 =? y0)
eq-cvtop---fam8-fun (TRUNC-SAT x0) (TRUNC-SAT y0) = (x0 =? y0)
eq-cvtop---fam8-fun REINTERPRET REINTERPRET = true
eq-cvtop---fam8-fun _ _ = false
instance
  haseq-cvtop---fam8 : HasEq cvtop---fam8
  haseq-cvtop---fam8 = record { _=?_ = eq-cvtop---fam8-fun }

data cvtop---fam9 : Set where
  cvtop---TRUNC : (sx-51510 : sx) → cvtop---fam9
  TRUNC-SAT : (sx-51511 : sx) → cvtop---fam9
  REINTERPRET : cvtop---fam9 {- 1 premise(s) dropped -}

eq-cvtop---fam9-fun : cvtop---fam9 → cvtop---fam9 → Bool
eq-cvtop---fam9-fun (cvtop---TRUNC x0) (cvtop---TRUNC y0) = (x0 =? y0)
eq-cvtop---fam9-fun (TRUNC-SAT x0) (TRUNC-SAT y0) = (x0 =? y0)
eq-cvtop---fam9-fun REINTERPRET REINTERPRET = true
eq-cvtop---fam9-fun _ _ = false
instance
  haseq-cvtop---fam9 : HasEq cvtop---fam9
  haseq-cvtop---fam9 = record { _=?_ = eq-cvtop---fam9-fun }

data cvtop---fam10 : Set where
  cvtop---TRUNC : (sx-51512 : sx) → cvtop---fam10
  TRUNC-SAT : (sx-51513 : sx) → cvtop---fam10
  REINTERPRET : cvtop---fam10 {- 1 premise(s) dropped -}

eq-cvtop---fam10-fun : cvtop---fam10 → cvtop---fam10 → Bool
eq-cvtop---fam10-fun (cvtop---TRUNC x0) (cvtop---TRUNC y0) = (x0 =? y0)
eq-cvtop---fam10-fun (TRUNC-SAT x0) (TRUNC-SAT y0) = (x0 =? y0)
eq-cvtop---fam10-fun REINTERPRET REINTERPRET = true
eq-cvtop---fam10-fun _ _ = false
instance
  haseq-cvtop---fam10 : HasEq cvtop---fam10
  haseq-cvtop---fam10 = record { _=?_ = eq-cvtop---fam10-fun }

data cvtop---fam11 : Set where
  cvtop---TRUNC : (sx-51514 : sx) → cvtop---fam11
  TRUNC-SAT : (sx-51515 : sx) → cvtop---fam11
  REINTERPRET : cvtop---fam11 {- 1 premise(s) dropped -}

eq-cvtop---fam11-fun : cvtop---fam11 → cvtop---fam11 → Bool
eq-cvtop---fam11-fun (cvtop---TRUNC x0) (cvtop---TRUNC y0) = (x0 =? y0)
eq-cvtop---fam11-fun (TRUNC-SAT x0) (TRUNC-SAT y0) = (x0 =? y0)
eq-cvtop---fam11-fun REINTERPRET REINTERPRET = true
eq-cvtop---fam11-fun _ _ = false
instance
  haseq-cvtop---fam11 : HasEq cvtop---fam11
  haseq-cvtop---fam11 = record { _=?_ = eq-cvtop---fam11-fun }

data cvtop---fam12 : Set where
  PROMOTE : cvtop---fam12 {- 1 premise(s) dropped -}
  DEMOTE : cvtop---fam12 {- 1 premise(s) dropped -}

eq-cvtop---fam12-fun : cvtop---fam12 → cvtop---fam12 → Bool
eq-cvtop---fam12-fun PROMOTE PROMOTE = true
eq-cvtop---fam12-fun DEMOTE DEMOTE = true
eq-cvtop---fam12-fun _ _ = false
instance
  haseq-cvtop---fam12 : HasEq cvtop---fam12
  haseq-cvtop---fam12 = record { _=?_ = eq-cvtop---fam12-fun }

data cvtop---fam13 : Set where
  PROMOTE : cvtop---fam13 {- 1 premise(s) dropped -}
  DEMOTE : cvtop---fam13 {- 1 premise(s) dropped -}

eq-cvtop---fam13-fun : cvtop---fam13 → cvtop---fam13 → Bool
eq-cvtop---fam13-fun PROMOTE PROMOTE = true
eq-cvtop---fam13-fun DEMOTE DEMOTE = true
eq-cvtop---fam13-fun _ _ = false
instance
  haseq-cvtop---fam13 : HasEq cvtop---fam13
  haseq-cvtop---fam13 = record { _=?_ = eq-cvtop---fam13-fun }

data cvtop---fam14 : Set where
  PROMOTE : cvtop---fam14 {- 1 premise(s) dropped -}
  DEMOTE : cvtop---fam14 {- 1 premise(s) dropped -}

eq-cvtop---fam14-fun : cvtop---fam14 → cvtop---fam14 → Bool
eq-cvtop---fam14-fun PROMOTE PROMOTE = true
eq-cvtop---fam14-fun DEMOTE DEMOTE = true
eq-cvtop---fam14-fun _ _ = false
instance
  haseq-cvtop---fam14 : HasEq cvtop---fam14
  haseq-cvtop---fam14 = record { _=?_ = eq-cvtop---fam14-fun }

data cvtop---fam15 : Set where
  PROMOTE : cvtop---fam15 {- 1 premise(s) dropped -}
  DEMOTE : cvtop---fam15 {- 1 premise(s) dropped -}

eq-cvtop---fam15-fun : cvtop---fam15 → cvtop---fam15 → Bool
eq-cvtop---fam15-fun PROMOTE PROMOTE = true
eq-cvtop---fam15-fun DEMOTE DEMOTE = true
eq-cvtop---fam15-fun _ _ = false
instance
  haseq-cvtop---fam15 : HasEq cvtop---fam15
  haseq-cvtop---fam15 = record { _=?_ = eq-cvtop---fam15-fun }

cvtop-- : (numtype-1 : numtype) (numtype-2 : numtype) → Set
cvtop-- numtype-I32 numtype-I32 = cvtop---fam0
cvtop-- numtype-I64 numtype-I32 = cvtop---fam1
cvtop-- numtype-I32 numtype-I64 = cvtop---fam2
cvtop-- numtype-I64 numtype-I64 = cvtop---fam3
cvtop-- numtype-I32 F32 = cvtop---fam4
cvtop-- numtype-I64 F32 = cvtop---fam5
cvtop-- numtype-I32 F64 = cvtop---fam6
cvtop-- numtype-I64 F64 = cvtop---fam7
cvtop-- F32 numtype-I32 = cvtop---fam8
cvtop-- F64 numtype-I32 = cvtop---fam9
cvtop-- F32 numtype-I64 = cvtop---fam10
cvtop-- F64 numtype-I64 = cvtop---fam11
cvtop-- F32 F32 = cvtop---fam12
cvtop-- F64 F32 = cvtop---fam13
cvtop-- F32 F64 = cvtop---fam14
cvtop-- F64 F64 = cvtop---fam15
cvtop-- _ _ = ⊤

{- Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:73.1-73.60 -}
data dim : Set where
  mk-dim : (i : ℕ) → dim {- 1 premise(s) dropped -}

instance
  inh-dim : Inhabited dim
  inh-dim = record { default-val = (mk-dim (default-val)) }

eq-dim-fun : dim → dim → Bool
eq-dim-fun (mk-dim x0) (mk-dim y0) = (x0 =? y0)
instance
  haseq-dim : HasEq dim
  haseq-dim = record { _=?_ = eq-dim-fun }

{- Auxiliary Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:73.1-73.60 -}
{-# TERMINATING #-}
proj-dim-0 : (x : dim) → (ℕ)
proj-dim-0 (mk-dim v-num-0) = (v-num-0)
proj-dim-0 x = (default-val)

instance
  proj-dim-0-coercion : Coerce dim (ℕ)
  proj-dim-0-coercion = record { coerce = proj-dim-0 }

{- Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:74.1-75.40 -}
data shape : Set where
  X : (v-lanetype : lanetype) → (v-dim : dim) → shape {- 1 premise(s) dropped -}

instance
  inh-shape : Inhabited shape
  inh-shape = record { default-val = (X (default-val) (default-val)) }

eq-shape-fun : shape → shape → Bool
eq-shape-fun (X x0 x1) (X y0 y1) = (x0 =? y0) ∧ (x1 =? y1)
instance
  haseq-shape : HasEq shape
  haseq-shape = record { _=?_ = eq-shape-fun }

{- Auxiliary Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:78.1-78.43 -}
{-# TERMINATING #-}
fun-dim : (v-shape : shape) → dim
fun-dim (X v-Lnn (mk-dim v-N)) = (mk-dim v-N)
fun-dim v-shape = default-val

{- Auxiliary Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:81.1-81.58 -}
{-# TERMINATING #-}
fun-lanetype : (v-shape : shape) → lanetype
fun-lanetype (X v-Lnn (mk-dim v-N)) = v-Lnn
fun-lanetype v-shape = default-val

{- Auxiliary Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:84.1-84.57 -}
{-# TERMINATING #-}
unpackshape : (v-shape : shape) → numtype
unpackshape (X v-Lnn (mk-dim v-N)) = (lunpack v-Lnn)
unpackshape v-shape = default-val

{- Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:88.1-88.78 -}
data ishape : Set where
  mk-ishape : (v-shape : shape) → ishape {- 1 premise(s) dropped -}

eq-ishape-fun : ishape → ishape → Bool
eq-ishape-fun (mk-ishape x0) (mk-ishape y0) = (x0 =? y0)
instance
  haseq-ishape : HasEq ishape
  haseq-ishape = record { _=?_ = eq-ishape-fun }

{- Auxiliary Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:88.1-88.78 -}
{-# TERMINATING #-}
proj-ishape-0 : (x : ishape) → (shape)
proj-ishape-0 (mk-ishape v-shape-0) = (v-shape-0)
proj-ishape-0 x = (default-val)

instance
  proj-ishape-0-coercion : Coerce ishape (shape)
  proj-ishape-0-coercion = record { coerce = proj-ishape-0 }

{- Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:89.1-89.77 -}
data bshape : Set where
  mk-bshape : (v-shape : shape) → bshape {- 1 premise(s) dropped -}

eq-bshape-fun : bshape → bshape → Bool
eq-bshape-fun (mk-bshape x0) (mk-bshape y0) = (x0 =? y0)
instance
  haseq-bshape : HasEq bshape
  haseq-bshape = record { _=?_ = eq-bshape-fun }

{- Auxiliary Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:89.1-89.77 -}
{-# TERMINATING #-}
proj-bshape-0 : (x : bshape) → (shape)
proj-bshape-0 (mk-bshape v-shape-0) = (v-shape-0)
proj-bshape-0 x = (default-val)

instance
  proj-bshape-0-coercion : Coerce bshape (shape)
  proj-bshape-0-coercion = record { coerce = proj-bshape-0 }

{- Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:94.1-94.19 -}
data zero' : Set where
  ZERO : zero'

instance
  inh-zero' : Inhabited zero'
  inh-zero' = record { default-val = ZERO }

eq-zero'-fun : zero' → zero' → Bool
eq-zero'-fun ZERO ZERO = true
instance
  haseq-zero' : HasEq zero'
  haseq-zero' = record { _=?_ = eq-zero'-fun }

{- Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:95.1-95.25 -}
data half : Set where
  LOW : half
  HIGH : half

instance
  inh-half : Inhabited half
  inh-half = record { default-val = LOW }

eq-half-fun : half → half → Bool
eq-half-fun LOW LOW = true
eq-half-fun HIGH HIGH = true
eq-half-fun _ _ = false
instance
  haseq-half : HasEq half
  haseq-half = record { _=?_ = eq-half-fun }

{- Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:97.1-97.41 -}
data vvunop : Set where
  NOT : vvunop

eq-vvunop-fun : vvunop → vvunop → Bool
eq-vvunop-fun NOT NOT = true
instance
  haseq-vvunop : HasEq vvunop
  haseq-vvunop = record { _=?_ = eq-vvunop-fun }

{- Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:98.1-98.62 -}
data vvbinop : Set where
  vvbinop-AND : vvbinop
  ANDNOT : vvbinop
  vvbinop-OR : vvbinop
  vvbinop-XOR : vvbinop

eq-vvbinop-fun : vvbinop → vvbinop → Bool
eq-vvbinop-fun vvbinop-AND vvbinop-AND = true
eq-vvbinop-fun ANDNOT ANDNOT = true
eq-vvbinop-fun vvbinop-OR vvbinop-OR = true
eq-vvbinop-fun vvbinop-XOR vvbinop-XOR = true
eq-vvbinop-fun _ _ = false
instance
  haseq-vvbinop : HasEq vvbinop
  haseq-vvbinop = record { _=?_ = eq-vvbinop-fun }

{- Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:99.1-99.49 -}
data vvternop : Set where
  BITSELECT : vvternop

eq-vvternop-fun : vvternop → vvternop → Bool
eq-vvternop-fun BITSELECT BITSELECT = true
instance
  haseq-vvternop : HasEq vvternop
  haseq-vvternop = record { _=?_ = eq-vvternop-fun }

{- Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:100.1-100.48 -}
data vvtestop : Set where
  ANY-TRUE : vvtestop

eq-vvtestop-fun : vvtestop → vvtestop → Bool
eq-vvtestop-fun ANY-TRUE ANY-TRUE = true
instance
  haseq-vvtestop : HasEq vvtestop
  haseq-vvtestop = record { _=?_ = eq-vvtestop-fun }

{- Type Family Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:102.1-102.42 -}
data vunop--fam0 (v-M : M) : Set where
  vunop--ABS : vunop--fam0 v-M
  vunop--NEG : vunop--fam0 v-M
  vunop--POPCNT : vunop--fam0 v-M {- 1 premise(s) dropped -}

eq-vunop--fam0-fun : {v-M : M} → (vunop--fam0 v-M) → (vunop--fam0 v-M) → Bool
eq-vunop--fam0-fun vunop--ABS vunop--ABS = true
eq-vunop--fam0-fun vunop--NEG vunop--NEG = true
eq-vunop--fam0-fun vunop--POPCNT vunop--POPCNT = true
eq-vunop--fam0-fun _ _ = false
instance
  haseq-vunop--fam0 : {v-M : M} → HasEq (vunop--fam0 v-M)
  haseq-vunop--fam0 = record { _=?_ = eq-vunop--fam0-fun }

data vunop--fam1 (v-M : M) : Set where
  vunop--ABS : vunop--fam1 v-M
  vunop--NEG : vunop--fam1 v-M
  vunop--POPCNT : vunop--fam1 v-M {- 1 premise(s) dropped -}

eq-vunop--fam1-fun : {v-M : M} → (vunop--fam1 v-M) → (vunop--fam1 v-M) → Bool
eq-vunop--fam1-fun vunop--ABS vunop--ABS = true
eq-vunop--fam1-fun vunop--NEG vunop--NEG = true
eq-vunop--fam1-fun vunop--POPCNT vunop--POPCNT = true
eq-vunop--fam1-fun _ _ = false
instance
  haseq-vunop--fam1 : {v-M : M} → HasEq (vunop--fam1 v-M)
  haseq-vunop--fam1 = record { _=?_ = eq-vunop--fam1-fun }

data vunop--fam2 (v-M : M) : Set where
  vunop--ABS : vunop--fam2 v-M
  vunop--NEG : vunop--fam2 v-M
  vunop--POPCNT : vunop--fam2 v-M {- 1 premise(s) dropped -}

eq-vunop--fam2-fun : {v-M : M} → (vunop--fam2 v-M) → (vunop--fam2 v-M) → Bool
eq-vunop--fam2-fun vunop--ABS vunop--ABS = true
eq-vunop--fam2-fun vunop--NEG vunop--NEG = true
eq-vunop--fam2-fun vunop--POPCNT vunop--POPCNT = true
eq-vunop--fam2-fun _ _ = false
instance
  haseq-vunop--fam2 : {v-M : M} → HasEq (vunop--fam2 v-M)
  haseq-vunop--fam2 = record { _=?_ = eq-vunop--fam2-fun }

data vunop--fam3 (v-M : M) : Set where
  vunop--ABS : vunop--fam3 v-M
  vunop--NEG : vunop--fam3 v-M
  vunop--POPCNT : vunop--fam3 v-M {- 1 premise(s) dropped -}

eq-vunop--fam3-fun : {v-M : M} → (vunop--fam3 v-M) → (vunop--fam3 v-M) → Bool
eq-vunop--fam3-fun vunop--ABS vunop--ABS = true
eq-vunop--fam3-fun vunop--NEG vunop--NEG = true
eq-vunop--fam3-fun vunop--POPCNT vunop--POPCNT = true
eq-vunop--fam3-fun _ _ = false
instance
  haseq-vunop--fam3 : {v-M : M} → HasEq (vunop--fam3 v-M)
  haseq-vunop--fam3 = record { _=?_ = eq-vunop--fam3-fun }

data vunop--fam4 (v-M : M) : Set where
  vunop--ABS : vunop--fam4 v-M
  vunop--NEG : vunop--fam4 v-M
  vunop--SQRT : vunop--fam4 v-M
  vunop--CEIL : vunop--fam4 v-M
  vunop--FLOOR : vunop--fam4 v-M
  vunop--TRUNC : vunop--fam4 v-M
  vunop--NEAREST : vunop--fam4 v-M

eq-vunop--fam4-fun : {v-M : M} → (vunop--fam4 v-M) → (vunop--fam4 v-M) → Bool
eq-vunop--fam4-fun vunop--ABS vunop--ABS = true
eq-vunop--fam4-fun vunop--NEG vunop--NEG = true
eq-vunop--fam4-fun vunop--SQRT vunop--SQRT = true
eq-vunop--fam4-fun vunop--CEIL vunop--CEIL = true
eq-vunop--fam4-fun vunop--FLOOR vunop--FLOOR = true
eq-vunop--fam4-fun vunop--TRUNC vunop--TRUNC = true
eq-vunop--fam4-fun vunop--NEAREST vunop--NEAREST = true
eq-vunop--fam4-fun _ _ = false
instance
  haseq-vunop--fam4 : {v-M : M} → HasEq (vunop--fam4 v-M)
  haseq-vunop--fam4 = record { _=?_ = eq-vunop--fam4-fun }

data vunop--fam5 (v-M : M) : Set where
  vunop--ABS : vunop--fam5 v-M
  vunop--NEG : vunop--fam5 v-M
  vunop--SQRT : vunop--fam5 v-M
  vunop--CEIL : vunop--fam5 v-M
  vunop--FLOOR : vunop--fam5 v-M
  vunop--TRUNC : vunop--fam5 v-M
  vunop--NEAREST : vunop--fam5 v-M

eq-vunop--fam5-fun : {v-M : M} → (vunop--fam5 v-M) → (vunop--fam5 v-M) → Bool
eq-vunop--fam5-fun vunop--ABS vunop--ABS = true
eq-vunop--fam5-fun vunop--NEG vunop--NEG = true
eq-vunop--fam5-fun vunop--SQRT vunop--SQRT = true
eq-vunop--fam5-fun vunop--CEIL vunop--CEIL = true
eq-vunop--fam5-fun vunop--FLOOR vunop--FLOOR = true
eq-vunop--fam5-fun vunop--TRUNC vunop--TRUNC = true
eq-vunop--fam5-fun vunop--NEAREST vunop--NEAREST = true
eq-vunop--fam5-fun _ _ = false
instance
  haseq-vunop--fam5 : {v-M : M} → HasEq (vunop--fam5 v-M)
  haseq-vunop--fam5 = record { _=?_ = eq-vunop--fam5-fun }

vunop- : (v-shape : shape) → Set
vunop- (X lanetype-I32 (mk-dim v-M)) = vunop--fam0 v-M
vunop- (X lanetype-I64 (mk-dim v-M)) = vunop--fam1 v-M
vunop- (X lanetype-I8 (mk-dim v-M)) = vunop--fam2 v-M
vunop- (X lanetype-I16 (mk-dim v-M)) = vunop--fam3 v-M
vunop- (X lanetype-F32 (mk-dim v-M)) = vunop--fam4 v-M
vunop- (X lanetype-F64 (mk-dim v-M)) = vunop--fam5 v-M
vunop- _ = ⊤

{- Type Family Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:108.1-108.43 -}
data vbinop--fam0 (v-M : M) : Set where
  vbinop--ADD : vbinop--fam0 v-M
  vbinop--SUB : vbinop--fam0 v-M
  ADD-SAT : (sx-51516 : sx) → vbinop--fam0 v-M {- 1 premise(s) dropped -}
  SUB-SAT : (sx-51517 : sx) → vbinop--fam0 v-M {- 1 premise(s) dropped -}
  vbinop--MUL : vbinop--fam0 v-M {- 1 premise(s) dropped -}
  AVGRU : vbinop--fam0 v-M {- 1 premise(s) dropped -}
  Q15MULR-SATS : vbinop--fam0 v-M {- 1 premise(s) dropped -}
  RELAXED-Q15MULRS : vbinop--fam0 v-M {- 1 premise(s) dropped -}
  vbinop--MIN : (sx-51518 : sx) → vbinop--fam0 v-M {- 1 premise(s) dropped -}
  vbinop--MAX : (sx-51519 : sx) → vbinop--fam0 v-M {- 1 premise(s) dropped -}

eq-vbinop--fam0-fun : {v-M : M} → (vbinop--fam0 v-M) → (vbinop--fam0 v-M) → Bool
eq-vbinop--fam0-fun vbinop--ADD vbinop--ADD = true
eq-vbinop--fam0-fun vbinop--SUB vbinop--SUB = true
eq-vbinop--fam0-fun (ADD-SAT x0) (ADD-SAT y0) = (x0 =? y0)
eq-vbinop--fam0-fun (SUB-SAT x0) (SUB-SAT y0) = (x0 =? y0)
eq-vbinop--fam0-fun vbinop--MUL vbinop--MUL = true
eq-vbinop--fam0-fun AVGRU AVGRU = true
eq-vbinop--fam0-fun Q15MULR-SATS Q15MULR-SATS = true
eq-vbinop--fam0-fun RELAXED-Q15MULRS RELAXED-Q15MULRS = true
eq-vbinop--fam0-fun (vbinop--MIN x0) (vbinop--MIN y0) = (x0 =? y0)
eq-vbinop--fam0-fun (vbinop--MAX x0) (vbinop--MAX y0) = (x0 =? y0)
eq-vbinop--fam0-fun _ _ = false
instance
  haseq-vbinop--fam0 : {v-M : M} → HasEq (vbinop--fam0 v-M)
  haseq-vbinop--fam0 = record { _=?_ = eq-vbinop--fam0-fun }

data vbinop--fam1 (v-M : M) : Set where
  vbinop--ADD : vbinop--fam1 v-M
  vbinop--SUB : vbinop--fam1 v-M
  ADD-SAT : (sx-51520 : sx) → vbinop--fam1 v-M {- 1 premise(s) dropped -}
  SUB-SAT : (sx-51521 : sx) → vbinop--fam1 v-M {- 1 premise(s) dropped -}
  vbinop--MUL : vbinop--fam1 v-M {- 1 premise(s) dropped -}
  AVGRU : vbinop--fam1 v-M {- 1 premise(s) dropped -}
  Q15MULR-SATS : vbinop--fam1 v-M {- 1 premise(s) dropped -}
  RELAXED-Q15MULRS : vbinop--fam1 v-M {- 1 premise(s) dropped -}
  vbinop--MIN : (sx-51522 : sx) → vbinop--fam1 v-M {- 1 premise(s) dropped -}
  vbinop--MAX : (sx-51523 : sx) → vbinop--fam1 v-M {- 1 premise(s) dropped -}

eq-vbinop--fam1-fun : {v-M : M} → (vbinop--fam1 v-M) → (vbinop--fam1 v-M) → Bool
eq-vbinop--fam1-fun vbinop--ADD vbinop--ADD = true
eq-vbinop--fam1-fun vbinop--SUB vbinop--SUB = true
eq-vbinop--fam1-fun (ADD-SAT x0) (ADD-SAT y0) = (x0 =? y0)
eq-vbinop--fam1-fun (SUB-SAT x0) (SUB-SAT y0) = (x0 =? y0)
eq-vbinop--fam1-fun vbinop--MUL vbinop--MUL = true
eq-vbinop--fam1-fun AVGRU AVGRU = true
eq-vbinop--fam1-fun Q15MULR-SATS Q15MULR-SATS = true
eq-vbinop--fam1-fun RELAXED-Q15MULRS RELAXED-Q15MULRS = true
eq-vbinop--fam1-fun (vbinop--MIN x0) (vbinop--MIN y0) = (x0 =? y0)
eq-vbinop--fam1-fun (vbinop--MAX x0) (vbinop--MAX y0) = (x0 =? y0)
eq-vbinop--fam1-fun _ _ = false
instance
  haseq-vbinop--fam1 : {v-M : M} → HasEq (vbinop--fam1 v-M)
  haseq-vbinop--fam1 = record { _=?_ = eq-vbinop--fam1-fun }

data vbinop--fam2 (v-M : M) : Set where
  vbinop--ADD : vbinop--fam2 v-M
  vbinop--SUB : vbinop--fam2 v-M
  ADD-SAT : (sx-51524 : sx) → vbinop--fam2 v-M {- 1 premise(s) dropped -}
  SUB-SAT : (sx-51525 : sx) → vbinop--fam2 v-M {- 1 premise(s) dropped -}
  vbinop--MUL : vbinop--fam2 v-M {- 1 premise(s) dropped -}
  AVGRU : vbinop--fam2 v-M {- 1 premise(s) dropped -}
  Q15MULR-SATS : vbinop--fam2 v-M {- 1 premise(s) dropped -}
  RELAXED-Q15MULRS : vbinop--fam2 v-M {- 1 premise(s) dropped -}
  vbinop--MIN : (sx-51526 : sx) → vbinop--fam2 v-M {- 1 premise(s) dropped -}
  vbinop--MAX : (sx-51527 : sx) → vbinop--fam2 v-M {- 1 premise(s) dropped -}

eq-vbinop--fam2-fun : {v-M : M} → (vbinop--fam2 v-M) → (vbinop--fam2 v-M) → Bool
eq-vbinop--fam2-fun vbinop--ADD vbinop--ADD = true
eq-vbinop--fam2-fun vbinop--SUB vbinop--SUB = true
eq-vbinop--fam2-fun (ADD-SAT x0) (ADD-SAT y0) = (x0 =? y0)
eq-vbinop--fam2-fun (SUB-SAT x0) (SUB-SAT y0) = (x0 =? y0)
eq-vbinop--fam2-fun vbinop--MUL vbinop--MUL = true
eq-vbinop--fam2-fun AVGRU AVGRU = true
eq-vbinop--fam2-fun Q15MULR-SATS Q15MULR-SATS = true
eq-vbinop--fam2-fun RELAXED-Q15MULRS RELAXED-Q15MULRS = true
eq-vbinop--fam2-fun (vbinop--MIN x0) (vbinop--MIN y0) = (x0 =? y0)
eq-vbinop--fam2-fun (vbinop--MAX x0) (vbinop--MAX y0) = (x0 =? y0)
eq-vbinop--fam2-fun _ _ = false
instance
  haseq-vbinop--fam2 : {v-M : M} → HasEq (vbinop--fam2 v-M)
  haseq-vbinop--fam2 = record { _=?_ = eq-vbinop--fam2-fun }

data vbinop--fam3 (v-M : M) : Set where
  vbinop--ADD : vbinop--fam3 v-M
  vbinop--SUB : vbinop--fam3 v-M
  ADD-SAT : (sx-51528 : sx) → vbinop--fam3 v-M {- 1 premise(s) dropped -}
  SUB-SAT : (sx-51529 : sx) → vbinop--fam3 v-M {- 1 premise(s) dropped -}
  vbinop--MUL : vbinop--fam3 v-M {- 1 premise(s) dropped -}
  AVGRU : vbinop--fam3 v-M {- 1 premise(s) dropped -}
  Q15MULR-SATS : vbinop--fam3 v-M {- 1 premise(s) dropped -}
  RELAXED-Q15MULRS : vbinop--fam3 v-M {- 1 premise(s) dropped -}
  vbinop--MIN : (sx-51530 : sx) → vbinop--fam3 v-M {- 1 premise(s) dropped -}
  vbinop--MAX : (sx-51531 : sx) → vbinop--fam3 v-M {- 1 premise(s) dropped -}

eq-vbinop--fam3-fun : {v-M : M} → (vbinop--fam3 v-M) → (vbinop--fam3 v-M) → Bool
eq-vbinop--fam3-fun vbinop--ADD vbinop--ADD = true
eq-vbinop--fam3-fun vbinop--SUB vbinop--SUB = true
eq-vbinop--fam3-fun (ADD-SAT x0) (ADD-SAT y0) = (x0 =? y0)
eq-vbinop--fam3-fun (SUB-SAT x0) (SUB-SAT y0) = (x0 =? y0)
eq-vbinop--fam3-fun vbinop--MUL vbinop--MUL = true
eq-vbinop--fam3-fun AVGRU AVGRU = true
eq-vbinop--fam3-fun Q15MULR-SATS Q15MULR-SATS = true
eq-vbinop--fam3-fun RELAXED-Q15MULRS RELAXED-Q15MULRS = true
eq-vbinop--fam3-fun (vbinop--MIN x0) (vbinop--MIN y0) = (x0 =? y0)
eq-vbinop--fam3-fun (vbinop--MAX x0) (vbinop--MAX y0) = (x0 =? y0)
eq-vbinop--fam3-fun _ _ = false
instance
  haseq-vbinop--fam3 : {v-M : M} → HasEq (vbinop--fam3 v-M)
  haseq-vbinop--fam3 = record { _=?_ = eq-vbinop--fam3-fun }

data vbinop--fam4 (v-M : M) : Set where
  vbinop--ADD : vbinop--fam4 v-M
  vbinop--SUB : vbinop--fam4 v-M
  vbinop--MUL : vbinop--fam4 v-M
  vbinop--DIV : vbinop--fam4 v-M
  vbinop--MIN : vbinop--fam4 v-M
  vbinop--MAX : vbinop--fam4 v-M
  PMIN : vbinop--fam4 v-M
  PMAX : vbinop--fam4 v-M
  RELAXED-MIN : vbinop--fam4 v-M
  RELAXED-MAX : vbinop--fam4 v-M

eq-vbinop--fam4-fun : {v-M : M} → (vbinop--fam4 v-M) → (vbinop--fam4 v-M) → Bool
eq-vbinop--fam4-fun vbinop--ADD vbinop--ADD = true
eq-vbinop--fam4-fun vbinop--SUB vbinop--SUB = true
eq-vbinop--fam4-fun vbinop--MUL vbinop--MUL = true
eq-vbinop--fam4-fun vbinop--DIV vbinop--DIV = true
eq-vbinop--fam4-fun vbinop--MIN vbinop--MIN = true
eq-vbinop--fam4-fun vbinop--MAX vbinop--MAX = true
eq-vbinop--fam4-fun PMIN PMIN = true
eq-vbinop--fam4-fun PMAX PMAX = true
eq-vbinop--fam4-fun RELAXED-MIN RELAXED-MIN = true
eq-vbinop--fam4-fun RELAXED-MAX RELAXED-MAX = true
eq-vbinop--fam4-fun _ _ = false
instance
  haseq-vbinop--fam4 : {v-M : M} → HasEq (vbinop--fam4 v-M)
  haseq-vbinop--fam4 = record { _=?_ = eq-vbinop--fam4-fun }

data vbinop--fam5 (v-M : M) : Set where
  vbinop--ADD : vbinop--fam5 v-M
  vbinop--SUB : vbinop--fam5 v-M
  vbinop--MUL : vbinop--fam5 v-M
  vbinop--DIV : vbinop--fam5 v-M
  vbinop--MIN : vbinop--fam5 v-M
  vbinop--MAX : vbinop--fam5 v-M
  PMIN : vbinop--fam5 v-M
  PMAX : vbinop--fam5 v-M
  RELAXED-MIN : vbinop--fam5 v-M
  RELAXED-MAX : vbinop--fam5 v-M

eq-vbinop--fam5-fun : {v-M : M} → (vbinop--fam5 v-M) → (vbinop--fam5 v-M) → Bool
eq-vbinop--fam5-fun vbinop--ADD vbinop--ADD = true
eq-vbinop--fam5-fun vbinop--SUB vbinop--SUB = true
eq-vbinop--fam5-fun vbinop--MUL vbinop--MUL = true
eq-vbinop--fam5-fun vbinop--DIV vbinop--DIV = true
eq-vbinop--fam5-fun vbinop--MIN vbinop--MIN = true
eq-vbinop--fam5-fun vbinop--MAX vbinop--MAX = true
eq-vbinop--fam5-fun PMIN PMIN = true
eq-vbinop--fam5-fun PMAX PMAX = true
eq-vbinop--fam5-fun RELAXED-MIN RELAXED-MIN = true
eq-vbinop--fam5-fun RELAXED-MAX RELAXED-MAX = true
eq-vbinop--fam5-fun _ _ = false
instance
  haseq-vbinop--fam5 : {v-M : M} → HasEq (vbinop--fam5 v-M)
  haseq-vbinop--fam5 = record { _=?_ = eq-vbinop--fam5-fun }

vbinop- : (v-shape : shape) → Set
vbinop- (X lanetype-I32 (mk-dim v-M)) = vbinop--fam0 v-M
vbinop- (X lanetype-I64 (mk-dim v-M)) = vbinop--fam1 v-M
vbinop- (X lanetype-I8 (mk-dim v-M)) = vbinop--fam2 v-M
vbinop- (X lanetype-I16 (mk-dim v-M)) = vbinop--fam3 v-M
vbinop- (X lanetype-F32 (mk-dim v-M)) = vbinop--fam4 v-M
vbinop- (X lanetype-F64 (mk-dim v-M)) = vbinop--fam5 v-M
vbinop- _ = ⊤

{- Type Family Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:124.1-124.44 -}
data vternop--fam0 (v-M : M) : Set where
  RELAXED-LANESELECT : vternop--fam0 v-M

eq-vternop--fam0-fun : {v-M : M} → (vternop--fam0 v-M) → (vternop--fam0 v-M) → Bool
eq-vternop--fam0-fun RELAXED-LANESELECT RELAXED-LANESELECT = true
instance
  haseq-vternop--fam0 : {v-M : M} → HasEq (vternop--fam0 v-M)
  haseq-vternop--fam0 = record { _=?_ = eq-vternop--fam0-fun }

data vternop--fam1 (v-M : M) : Set where
  RELAXED-LANESELECT : vternop--fam1 v-M

eq-vternop--fam1-fun : {v-M : M} → (vternop--fam1 v-M) → (vternop--fam1 v-M) → Bool
eq-vternop--fam1-fun RELAXED-LANESELECT RELAXED-LANESELECT = true
instance
  haseq-vternop--fam1 : {v-M : M} → HasEq (vternop--fam1 v-M)
  haseq-vternop--fam1 = record { _=?_ = eq-vternop--fam1-fun }

data vternop--fam2 (v-M : M) : Set where
  RELAXED-LANESELECT : vternop--fam2 v-M

eq-vternop--fam2-fun : {v-M : M} → (vternop--fam2 v-M) → (vternop--fam2 v-M) → Bool
eq-vternop--fam2-fun RELAXED-LANESELECT RELAXED-LANESELECT = true
instance
  haseq-vternop--fam2 : {v-M : M} → HasEq (vternop--fam2 v-M)
  haseq-vternop--fam2 = record { _=?_ = eq-vternop--fam2-fun }

data vternop--fam3 (v-M : M) : Set where
  RELAXED-LANESELECT : vternop--fam3 v-M

eq-vternop--fam3-fun : {v-M : M} → (vternop--fam3 v-M) → (vternop--fam3 v-M) → Bool
eq-vternop--fam3-fun RELAXED-LANESELECT RELAXED-LANESELECT = true
instance
  haseq-vternop--fam3 : {v-M : M} → HasEq (vternop--fam3 v-M)
  haseq-vternop--fam3 = record { _=?_ = eq-vternop--fam3-fun }

data vternop--fam4 (v-M : M) : Set where
  RELAXED-MADD : vternop--fam4 v-M
  RELAXED-NMADD : vternop--fam4 v-M

eq-vternop--fam4-fun : {v-M : M} → (vternop--fam4 v-M) → (vternop--fam4 v-M) → Bool
eq-vternop--fam4-fun RELAXED-MADD RELAXED-MADD = true
eq-vternop--fam4-fun RELAXED-NMADD RELAXED-NMADD = true
eq-vternop--fam4-fun _ _ = false
instance
  haseq-vternop--fam4 : {v-M : M} → HasEq (vternop--fam4 v-M)
  haseq-vternop--fam4 = record { _=?_ = eq-vternop--fam4-fun }

data vternop--fam5 (v-M : M) : Set where
  RELAXED-MADD : vternop--fam5 v-M
  RELAXED-NMADD : vternop--fam5 v-M

eq-vternop--fam5-fun : {v-M : M} → (vternop--fam5 v-M) → (vternop--fam5 v-M) → Bool
eq-vternop--fam5-fun RELAXED-MADD RELAXED-MADD = true
eq-vternop--fam5-fun RELAXED-NMADD RELAXED-NMADD = true
eq-vternop--fam5-fun _ _ = false
instance
  haseq-vternop--fam5 : {v-M : M} → HasEq (vternop--fam5 v-M)
  haseq-vternop--fam5 = record { _=?_ = eq-vternop--fam5-fun }

vternop- : (v-shape : shape) → Set
vternop- (X lanetype-I32 (mk-dim v-M)) = vternop--fam0 v-M
vternop- (X lanetype-I64 (mk-dim v-M)) = vternop--fam1 v-M
vternop- (X lanetype-I8 (mk-dim v-M)) = vternop--fam2 v-M
vternop- (X lanetype-I16 (mk-dim v-M)) = vternop--fam3 v-M
vternop- (X lanetype-F32 (mk-dim v-M)) = vternop--fam4 v-M
vternop- (X lanetype-F64 (mk-dim v-M)) = vternop--fam5 v-M
vternop- _ = ⊤

{- Type Family Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:128.1-128.44 -}
data vtestop--fam0 (v-M : M) : Set where
  ALL-TRUE : vtestop--fam0 v-M

eq-vtestop--fam0-fun : {v-M : M} → (vtestop--fam0 v-M) → (vtestop--fam0 v-M) → Bool
eq-vtestop--fam0-fun ALL-TRUE ALL-TRUE = true
instance
  haseq-vtestop--fam0 : {v-M : M} → HasEq (vtestop--fam0 v-M)
  haseq-vtestop--fam0 = record { _=?_ = eq-vtestop--fam0-fun }

data vtestop--fam1 (v-M : M) : Set where
  ALL-TRUE : vtestop--fam1 v-M

eq-vtestop--fam1-fun : {v-M : M} → (vtestop--fam1 v-M) → (vtestop--fam1 v-M) → Bool
eq-vtestop--fam1-fun ALL-TRUE ALL-TRUE = true
instance
  haseq-vtestop--fam1 : {v-M : M} → HasEq (vtestop--fam1 v-M)
  haseq-vtestop--fam1 = record { _=?_ = eq-vtestop--fam1-fun }

data vtestop--fam2 (v-M : M) : Set where
  ALL-TRUE : vtestop--fam2 v-M

eq-vtestop--fam2-fun : {v-M : M} → (vtestop--fam2 v-M) → (vtestop--fam2 v-M) → Bool
eq-vtestop--fam2-fun ALL-TRUE ALL-TRUE = true
instance
  haseq-vtestop--fam2 : {v-M : M} → HasEq (vtestop--fam2 v-M)
  haseq-vtestop--fam2 = record { _=?_ = eq-vtestop--fam2-fun }

data vtestop--fam3 (v-M : M) : Set where
  ALL-TRUE : vtestop--fam3 v-M

eq-vtestop--fam3-fun : {v-M : M} → (vtestop--fam3 v-M) → (vtestop--fam3 v-M) → Bool
eq-vtestop--fam3-fun ALL-TRUE ALL-TRUE = true
instance
  haseq-vtestop--fam3 : {v-M : M} → HasEq (vtestop--fam3 v-M)
  haseq-vtestop--fam3 = record { _=?_ = eq-vtestop--fam3-fun }

vtestop- : (v-shape : shape) → Set
vtestop- (X lanetype-I32 (mk-dim v-M)) = vtestop--fam0 v-M
vtestop- (X lanetype-I64 (mk-dim v-M)) = vtestop--fam1 v-M
vtestop- (X lanetype-I8 (mk-dim v-M)) = vtestop--fam2 v-M
vtestop- (X lanetype-I16 (mk-dim v-M)) = vtestop--fam3 v-M
vtestop- _ = ⊤

{- Type Family Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:132.1-132.43 -}
data vrelop--fam0 (v-M : M) : Set where
  vrelop--EQ : vrelop--fam0 v-M
  vrelop--NE : vrelop--fam0 v-M
  vrelop--LT : (sx-51532 : sx) → vrelop--fam0 v-M {- 1 premise(s) dropped -}
  vrelop--GT : (sx-51533 : sx) → vrelop--fam0 v-M {- 1 premise(s) dropped -}
  vrelop--LE : (sx-51534 : sx) → vrelop--fam0 v-M {- 1 premise(s) dropped -}
  vrelop--GE : (sx-51535 : sx) → vrelop--fam0 v-M {- 1 premise(s) dropped -}

eq-vrelop--fam0-fun : {v-M : M} → (vrelop--fam0 v-M) → (vrelop--fam0 v-M) → Bool
eq-vrelop--fam0-fun vrelop--EQ vrelop--EQ = true
eq-vrelop--fam0-fun vrelop--NE vrelop--NE = true
eq-vrelop--fam0-fun (vrelop--LT x0) (vrelop--LT y0) = (x0 =? y0)
eq-vrelop--fam0-fun (vrelop--GT x0) (vrelop--GT y0) = (x0 =? y0)
eq-vrelop--fam0-fun (vrelop--LE x0) (vrelop--LE y0) = (x0 =? y0)
eq-vrelop--fam0-fun (vrelop--GE x0) (vrelop--GE y0) = (x0 =? y0)
eq-vrelop--fam0-fun _ _ = false
instance
  haseq-vrelop--fam0 : {v-M : M} → HasEq (vrelop--fam0 v-M)
  haseq-vrelop--fam0 = record { _=?_ = eq-vrelop--fam0-fun }

data vrelop--fam1 (v-M : M) : Set where
  vrelop--EQ : vrelop--fam1 v-M
  vrelop--NE : vrelop--fam1 v-M
  vrelop--LT : (sx-51536 : sx) → vrelop--fam1 v-M {- 1 premise(s) dropped -}
  vrelop--GT : (sx-51537 : sx) → vrelop--fam1 v-M {- 1 premise(s) dropped -}
  vrelop--LE : (sx-51538 : sx) → vrelop--fam1 v-M {- 1 premise(s) dropped -}
  vrelop--GE : (sx-51539 : sx) → vrelop--fam1 v-M {- 1 premise(s) dropped -}

eq-vrelop--fam1-fun : {v-M : M} → (vrelop--fam1 v-M) → (vrelop--fam1 v-M) → Bool
eq-vrelop--fam1-fun vrelop--EQ vrelop--EQ = true
eq-vrelop--fam1-fun vrelop--NE vrelop--NE = true
eq-vrelop--fam1-fun (vrelop--LT x0) (vrelop--LT y0) = (x0 =? y0)
eq-vrelop--fam1-fun (vrelop--GT x0) (vrelop--GT y0) = (x0 =? y0)
eq-vrelop--fam1-fun (vrelop--LE x0) (vrelop--LE y0) = (x0 =? y0)
eq-vrelop--fam1-fun (vrelop--GE x0) (vrelop--GE y0) = (x0 =? y0)
eq-vrelop--fam1-fun _ _ = false
instance
  haseq-vrelop--fam1 : {v-M : M} → HasEq (vrelop--fam1 v-M)
  haseq-vrelop--fam1 = record { _=?_ = eq-vrelop--fam1-fun }

data vrelop--fam2 (v-M : M) : Set where
  vrelop--EQ : vrelop--fam2 v-M
  vrelop--NE : vrelop--fam2 v-M
  vrelop--LT : (sx-51540 : sx) → vrelop--fam2 v-M {- 1 premise(s) dropped -}
  vrelop--GT : (sx-51541 : sx) → vrelop--fam2 v-M {- 1 premise(s) dropped -}
  vrelop--LE : (sx-51542 : sx) → vrelop--fam2 v-M {- 1 premise(s) dropped -}
  vrelop--GE : (sx-51543 : sx) → vrelop--fam2 v-M {- 1 premise(s) dropped -}

eq-vrelop--fam2-fun : {v-M : M} → (vrelop--fam2 v-M) → (vrelop--fam2 v-M) → Bool
eq-vrelop--fam2-fun vrelop--EQ vrelop--EQ = true
eq-vrelop--fam2-fun vrelop--NE vrelop--NE = true
eq-vrelop--fam2-fun (vrelop--LT x0) (vrelop--LT y0) = (x0 =? y0)
eq-vrelop--fam2-fun (vrelop--GT x0) (vrelop--GT y0) = (x0 =? y0)
eq-vrelop--fam2-fun (vrelop--LE x0) (vrelop--LE y0) = (x0 =? y0)
eq-vrelop--fam2-fun (vrelop--GE x0) (vrelop--GE y0) = (x0 =? y0)
eq-vrelop--fam2-fun _ _ = false
instance
  haseq-vrelop--fam2 : {v-M : M} → HasEq (vrelop--fam2 v-M)
  haseq-vrelop--fam2 = record { _=?_ = eq-vrelop--fam2-fun }

data vrelop--fam3 (v-M : M) : Set where
  vrelop--EQ : vrelop--fam3 v-M
  vrelop--NE : vrelop--fam3 v-M
  vrelop--LT : (sx-51544 : sx) → vrelop--fam3 v-M {- 1 premise(s) dropped -}
  vrelop--GT : (sx-51545 : sx) → vrelop--fam3 v-M {- 1 premise(s) dropped -}
  vrelop--LE : (sx-51546 : sx) → vrelop--fam3 v-M {- 1 premise(s) dropped -}
  vrelop--GE : (sx-51547 : sx) → vrelop--fam3 v-M {- 1 premise(s) dropped -}

eq-vrelop--fam3-fun : {v-M : M} → (vrelop--fam3 v-M) → (vrelop--fam3 v-M) → Bool
eq-vrelop--fam3-fun vrelop--EQ vrelop--EQ = true
eq-vrelop--fam3-fun vrelop--NE vrelop--NE = true
eq-vrelop--fam3-fun (vrelop--LT x0) (vrelop--LT y0) = (x0 =? y0)
eq-vrelop--fam3-fun (vrelop--GT x0) (vrelop--GT y0) = (x0 =? y0)
eq-vrelop--fam3-fun (vrelop--LE x0) (vrelop--LE y0) = (x0 =? y0)
eq-vrelop--fam3-fun (vrelop--GE x0) (vrelop--GE y0) = (x0 =? y0)
eq-vrelop--fam3-fun _ _ = false
instance
  haseq-vrelop--fam3 : {v-M : M} → HasEq (vrelop--fam3 v-M)
  haseq-vrelop--fam3 = record { _=?_ = eq-vrelop--fam3-fun }

data vrelop--fam4 (v-M : M) : Set where
  vrelop--EQ : vrelop--fam4 v-M
  vrelop--NE : vrelop--fam4 v-M
  vrelop--LT : vrelop--fam4 v-M
  vrelop--GT : vrelop--fam4 v-M
  vrelop--LE : vrelop--fam4 v-M
  vrelop--GE : vrelop--fam4 v-M

eq-vrelop--fam4-fun : {v-M : M} → (vrelop--fam4 v-M) → (vrelop--fam4 v-M) → Bool
eq-vrelop--fam4-fun vrelop--EQ vrelop--EQ = true
eq-vrelop--fam4-fun vrelop--NE vrelop--NE = true
eq-vrelop--fam4-fun vrelop--LT vrelop--LT = true
eq-vrelop--fam4-fun vrelop--GT vrelop--GT = true
eq-vrelop--fam4-fun vrelop--LE vrelop--LE = true
eq-vrelop--fam4-fun vrelop--GE vrelop--GE = true
eq-vrelop--fam4-fun _ _ = false
instance
  haseq-vrelop--fam4 : {v-M : M} → HasEq (vrelop--fam4 v-M)
  haseq-vrelop--fam4 = record { _=?_ = eq-vrelop--fam4-fun }

data vrelop--fam5 (v-M : M) : Set where
  vrelop--EQ : vrelop--fam5 v-M
  vrelop--NE : vrelop--fam5 v-M
  vrelop--LT : vrelop--fam5 v-M
  vrelop--GT : vrelop--fam5 v-M
  vrelop--LE : vrelop--fam5 v-M
  vrelop--GE : vrelop--fam5 v-M

eq-vrelop--fam5-fun : {v-M : M} → (vrelop--fam5 v-M) → (vrelop--fam5 v-M) → Bool
eq-vrelop--fam5-fun vrelop--EQ vrelop--EQ = true
eq-vrelop--fam5-fun vrelop--NE vrelop--NE = true
eq-vrelop--fam5-fun vrelop--LT vrelop--LT = true
eq-vrelop--fam5-fun vrelop--GT vrelop--GT = true
eq-vrelop--fam5-fun vrelop--LE vrelop--LE = true
eq-vrelop--fam5-fun vrelop--GE vrelop--GE = true
eq-vrelop--fam5-fun _ _ = false
instance
  haseq-vrelop--fam5 : {v-M : M} → HasEq (vrelop--fam5 v-M)
  haseq-vrelop--fam5 = record { _=?_ = eq-vrelop--fam5-fun }

vrelop- : (v-shape : shape) → Set
vrelop- (X lanetype-I32 (mk-dim v-M)) = vrelop--fam0 v-M
vrelop- (X lanetype-I64 (mk-dim v-M)) = vrelop--fam1 v-M
vrelop- (X lanetype-I8 (mk-dim v-M)) = vrelop--fam2 v-M
vrelop- (X lanetype-I16 (mk-dim v-M)) = vrelop--fam3 v-M
vrelop- (X lanetype-F32 (mk-dim v-M)) = vrelop--fam4 v-M
vrelop- (X lanetype-F64 (mk-dim v-M)) = vrelop--fam5 v-M
vrelop- _ = ⊤

{- Type Family Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:140.1-140.46 -}
data vshiftop--fam0 (v-M : M) : Set where
  vshiftop--SHL : vshiftop--fam0 v-M
  vshiftop--SHR : (sx-51548 : sx) → vshiftop--fam0 v-M

eq-vshiftop--fam0-fun : {v-M : M} → (vshiftop--fam0 v-M) → (vshiftop--fam0 v-M) → Bool
eq-vshiftop--fam0-fun vshiftop--SHL vshiftop--SHL = true
eq-vshiftop--fam0-fun (vshiftop--SHR x0) (vshiftop--SHR y0) = (x0 =? y0)
eq-vshiftop--fam0-fun _ _ = false
instance
  haseq-vshiftop--fam0 : {v-M : M} → HasEq (vshiftop--fam0 v-M)
  haseq-vshiftop--fam0 = record { _=?_ = eq-vshiftop--fam0-fun }

data vshiftop--fam1 (v-M : M) : Set where
  vshiftop--SHL : vshiftop--fam1 v-M
  vshiftop--SHR : (sx-51549 : sx) → vshiftop--fam1 v-M

eq-vshiftop--fam1-fun : {v-M : M} → (vshiftop--fam1 v-M) → (vshiftop--fam1 v-M) → Bool
eq-vshiftop--fam1-fun vshiftop--SHL vshiftop--SHL = true
eq-vshiftop--fam1-fun (vshiftop--SHR x0) (vshiftop--SHR y0) = (x0 =? y0)
eq-vshiftop--fam1-fun _ _ = false
instance
  haseq-vshiftop--fam1 : {v-M : M} → HasEq (vshiftop--fam1 v-M)
  haseq-vshiftop--fam1 = record { _=?_ = eq-vshiftop--fam1-fun }

data vshiftop--fam2 (v-M : M) : Set where
  vshiftop--SHL : vshiftop--fam2 v-M
  vshiftop--SHR : (sx-51550 : sx) → vshiftop--fam2 v-M

eq-vshiftop--fam2-fun : {v-M : M} → (vshiftop--fam2 v-M) → (vshiftop--fam2 v-M) → Bool
eq-vshiftop--fam2-fun vshiftop--SHL vshiftop--SHL = true
eq-vshiftop--fam2-fun (vshiftop--SHR x0) (vshiftop--SHR y0) = (x0 =? y0)
eq-vshiftop--fam2-fun _ _ = false
instance
  haseq-vshiftop--fam2 : {v-M : M} → HasEq (vshiftop--fam2 v-M)
  haseq-vshiftop--fam2 = record { _=?_ = eq-vshiftop--fam2-fun }

data vshiftop--fam3 (v-M : M) : Set where
  vshiftop--SHL : vshiftop--fam3 v-M
  vshiftop--SHR : (sx-51551 : sx) → vshiftop--fam3 v-M

eq-vshiftop--fam3-fun : {v-M : M} → (vshiftop--fam3 v-M) → (vshiftop--fam3 v-M) → Bool
eq-vshiftop--fam3-fun vshiftop--SHL vshiftop--SHL = true
eq-vshiftop--fam3-fun (vshiftop--SHR x0) (vshiftop--SHR y0) = (x0 =? y0)
eq-vshiftop--fam3-fun _ _ = false
instance
  haseq-vshiftop--fam3 : {v-M : M} → HasEq (vshiftop--fam3 v-M)
  haseq-vshiftop--fam3 = record { _=?_ = eq-vshiftop--fam3-fun }

vshiftop- : (v-ishape : ishape) → Set
vshiftop- (mk-ishape (X lanetype-I32 (mk-dim v-M))) = vshiftop--fam0 v-M
vshiftop- (mk-ishape (X lanetype-I64 (mk-dim v-M))) = vshiftop--fam1 v-M
vshiftop- (mk-ishape (X lanetype-I8 (mk-dim v-M))) = vshiftop--fam2 v-M
vshiftop- (mk-ishape (X lanetype-I16 (mk-dim v-M))) = vshiftop--fam3 v-M
vshiftop- _ = ⊤

{- Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:143.1-143.47 -}
data vswizzlop--fam0 (v-M : M) : Set where
  SWIZZLE : vswizzlop--fam0 v-M
  RELAXED-SWIZZLE : vswizzlop--fam0 v-M

eq-vswizzlop--fam0-fun : {v-M : M} → (vswizzlop--fam0 v-M) → (vswizzlop--fam0 v-M) → Bool
eq-vswizzlop--fam0-fun SWIZZLE SWIZZLE = true
eq-vswizzlop--fam0-fun RELAXED-SWIZZLE RELAXED-SWIZZLE = true
eq-vswizzlop--fam0-fun _ _ = false
instance
  haseq-vswizzlop--fam0 : {v-M : M} → HasEq (vswizzlop--fam0 v-M)
  haseq-vswizzlop--fam0 = record { _=?_ = eq-vswizzlop--fam0-fun }

vswizzlop- : (v-bshape : bshape) → Set
vswizzlop- (mk-bshape (X lanetype-I8 (mk-dim v-M))) = vswizzlop--fam0 v-M
vswizzlop- _ = ⊤

{- Type Family Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:146.1-146.59 -}
data vextunop---fam0 (M-1 : M) (M-2 : M) : Set where
  EXTADD-PAIRWISE : (sx-51552 : sx) → vextunop---fam0 M-1 M-2 {- 1 premise(s) dropped -}

eq-vextunop---fam0-fun : {M-1 : M} → {M-2 : M} → (vextunop---fam0 M-1 M-2) → (vextunop---fam0 M-1 M-2) → Bool
eq-vextunop---fam0-fun (EXTADD-PAIRWISE x0) (EXTADD-PAIRWISE y0) = (x0 =? y0)
instance
  haseq-vextunop---fam0 : {M-1 : M} → {M-2 : M} → HasEq (vextunop---fam0 M-1 M-2)
  haseq-vextunop---fam0 = record { _=?_ = eq-vextunop---fam0-fun }

data vextunop---fam1 (M-1 : M) (M-2 : M) : Set where
  EXTADD-PAIRWISE : (sx-51553 : sx) → vextunop---fam1 M-1 M-2 {- 1 premise(s) dropped -}

eq-vextunop---fam1-fun : {M-1 : M} → {M-2 : M} → (vextunop---fam1 M-1 M-2) → (vextunop---fam1 M-1 M-2) → Bool
eq-vextunop---fam1-fun (EXTADD-PAIRWISE x0) (EXTADD-PAIRWISE y0) = (x0 =? y0)
instance
  haseq-vextunop---fam1 : {M-1 : M} → {M-2 : M} → HasEq (vextunop---fam1 M-1 M-2)
  haseq-vextunop---fam1 = record { _=?_ = eq-vextunop---fam1-fun }

data vextunop---fam2 (M-1 : M) (M-2 : M) : Set where
  EXTADD-PAIRWISE : (sx-51554 : sx) → vextunop---fam2 M-1 M-2 {- 1 premise(s) dropped -}

eq-vextunop---fam2-fun : {M-1 : M} → {M-2 : M} → (vextunop---fam2 M-1 M-2) → (vextunop---fam2 M-1 M-2) → Bool
eq-vextunop---fam2-fun (EXTADD-PAIRWISE x0) (EXTADD-PAIRWISE y0) = (x0 =? y0)
instance
  haseq-vextunop---fam2 : {M-1 : M} → {M-2 : M} → HasEq (vextunop---fam2 M-1 M-2)
  haseq-vextunop---fam2 = record { _=?_ = eq-vextunop---fam2-fun }

data vextunop---fam3 (M-1 : M) (M-2 : M) : Set where
  EXTADD-PAIRWISE : (sx-51555 : sx) → vextunop---fam3 M-1 M-2 {- 1 premise(s) dropped -}

eq-vextunop---fam3-fun : {M-1 : M} → {M-2 : M} → (vextunop---fam3 M-1 M-2) → (vextunop---fam3 M-1 M-2) → Bool
eq-vextunop---fam3-fun (EXTADD-PAIRWISE x0) (EXTADD-PAIRWISE y0) = (x0 =? y0)
instance
  haseq-vextunop---fam3 : {M-1 : M} → {M-2 : M} → HasEq (vextunop---fam3 M-1 M-2)
  haseq-vextunop---fam3 = record { _=?_ = eq-vextunop---fam3-fun }

data vextunop---fam4 (M-1 : M) (M-2 : M) : Set where
  EXTADD-PAIRWISE : (sx-51556 : sx) → vextunop---fam4 M-1 M-2 {- 1 premise(s) dropped -}

eq-vextunop---fam4-fun : {M-1 : M} → {M-2 : M} → (vextunop---fam4 M-1 M-2) → (vextunop---fam4 M-1 M-2) → Bool
eq-vextunop---fam4-fun (EXTADD-PAIRWISE x0) (EXTADD-PAIRWISE y0) = (x0 =? y0)
instance
  haseq-vextunop---fam4 : {M-1 : M} → {M-2 : M} → HasEq (vextunop---fam4 M-1 M-2)
  haseq-vextunop---fam4 = record { _=?_ = eq-vextunop---fam4-fun }

data vextunop---fam5 (M-1 : M) (M-2 : M) : Set where
  EXTADD-PAIRWISE : (sx-51557 : sx) → vextunop---fam5 M-1 M-2 {- 1 premise(s) dropped -}

eq-vextunop---fam5-fun : {M-1 : M} → {M-2 : M} → (vextunop---fam5 M-1 M-2) → (vextunop---fam5 M-1 M-2) → Bool
eq-vextunop---fam5-fun (EXTADD-PAIRWISE x0) (EXTADD-PAIRWISE y0) = (x0 =? y0)
instance
  haseq-vextunop---fam5 : {M-1 : M} → {M-2 : M} → HasEq (vextunop---fam5 M-1 M-2)
  haseq-vextunop---fam5 = record { _=?_ = eq-vextunop---fam5-fun }

data vextunop---fam6 (M-1 : M) (M-2 : M) : Set where
  EXTADD-PAIRWISE : (sx-51558 : sx) → vextunop---fam6 M-1 M-2 {- 1 premise(s) dropped -}

eq-vextunop---fam6-fun : {M-1 : M} → {M-2 : M} → (vextunop---fam6 M-1 M-2) → (vextunop---fam6 M-1 M-2) → Bool
eq-vextunop---fam6-fun (EXTADD-PAIRWISE x0) (EXTADD-PAIRWISE y0) = (x0 =? y0)
instance
  haseq-vextunop---fam6 : {M-1 : M} → {M-2 : M} → HasEq (vextunop---fam6 M-1 M-2)
  haseq-vextunop---fam6 = record { _=?_ = eq-vextunop---fam6-fun }

data vextunop---fam7 (M-1 : M) (M-2 : M) : Set where
  EXTADD-PAIRWISE : (sx-51559 : sx) → vextunop---fam7 M-1 M-2 {- 1 premise(s) dropped -}

eq-vextunop---fam7-fun : {M-1 : M} → {M-2 : M} → (vextunop---fam7 M-1 M-2) → (vextunop---fam7 M-1 M-2) → Bool
eq-vextunop---fam7-fun (EXTADD-PAIRWISE x0) (EXTADD-PAIRWISE y0) = (x0 =? y0)
instance
  haseq-vextunop---fam7 : {M-1 : M} → {M-2 : M} → HasEq (vextunop---fam7 M-1 M-2)
  haseq-vextunop---fam7 = record { _=?_ = eq-vextunop---fam7-fun }

data vextunop---fam8 (M-1 : M) (M-2 : M) : Set where
  EXTADD-PAIRWISE : (sx-51560 : sx) → vextunop---fam8 M-1 M-2 {- 1 premise(s) dropped -}

eq-vextunop---fam8-fun : {M-1 : M} → {M-2 : M} → (vextunop---fam8 M-1 M-2) → (vextunop---fam8 M-1 M-2) → Bool
eq-vextunop---fam8-fun (EXTADD-PAIRWISE x0) (EXTADD-PAIRWISE y0) = (x0 =? y0)
instance
  haseq-vextunop---fam8 : {M-1 : M} → {M-2 : M} → HasEq (vextunop---fam8 M-1 M-2)
  haseq-vextunop---fam8 = record { _=?_ = eq-vextunop---fam8-fun }

data vextunop---fam9 (M-1 : M) (M-2 : M) : Set where
  EXTADD-PAIRWISE : (sx-51561 : sx) → vextunop---fam9 M-1 M-2 {- 1 premise(s) dropped -}

eq-vextunop---fam9-fun : {M-1 : M} → {M-2 : M} → (vextunop---fam9 M-1 M-2) → (vextunop---fam9 M-1 M-2) → Bool
eq-vextunop---fam9-fun (EXTADD-PAIRWISE x0) (EXTADD-PAIRWISE y0) = (x0 =? y0)
instance
  haseq-vextunop---fam9 : {M-1 : M} → {M-2 : M} → HasEq (vextunop---fam9 M-1 M-2)
  haseq-vextunop---fam9 = record { _=?_ = eq-vextunop---fam9-fun }

data vextunop---fam10 (M-1 : M) (M-2 : M) : Set where
  EXTADD-PAIRWISE : (sx-51562 : sx) → vextunop---fam10 M-1 M-2 {- 1 premise(s) dropped -}

eq-vextunop---fam10-fun : {M-1 : M} → {M-2 : M} → (vextunop---fam10 M-1 M-2) → (vextunop---fam10 M-1 M-2) → Bool
eq-vextunop---fam10-fun (EXTADD-PAIRWISE x0) (EXTADD-PAIRWISE y0) = (x0 =? y0)
instance
  haseq-vextunop---fam10 : {M-1 : M} → {M-2 : M} → HasEq (vextunop---fam10 M-1 M-2)
  haseq-vextunop---fam10 = record { _=?_ = eq-vextunop---fam10-fun }

data vextunop---fam11 (M-1 : M) (M-2 : M) : Set where
  EXTADD-PAIRWISE : (sx-51563 : sx) → vextunop---fam11 M-1 M-2 {- 1 premise(s) dropped -}

eq-vextunop---fam11-fun : {M-1 : M} → {M-2 : M} → (vextunop---fam11 M-1 M-2) → (vextunop---fam11 M-1 M-2) → Bool
eq-vextunop---fam11-fun (EXTADD-PAIRWISE x0) (EXTADD-PAIRWISE y0) = (x0 =? y0)
instance
  haseq-vextunop---fam11 : {M-1 : M} → {M-2 : M} → HasEq (vextunop---fam11 M-1 M-2)
  haseq-vextunop---fam11 = record { _=?_ = eq-vextunop---fam11-fun }

data vextunop---fam12 (M-1 : M) (M-2 : M) : Set where
  EXTADD-PAIRWISE : (sx-51564 : sx) → vextunop---fam12 M-1 M-2 {- 1 premise(s) dropped -}

eq-vextunop---fam12-fun : {M-1 : M} → {M-2 : M} → (vextunop---fam12 M-1 M-2) → (vextunop---fam12 M-1 M-2) → Bool
eq-vextunop---fam12-fun (EXTADD-PAIRWISE x0) (EXTADD-PAIRWISE y0) = (x0 =? y0)
instance
  haseq-vextunop---fam12 : {M-1 : M} → {M-2 : M} → HasEq (vextunop---fam12 M-1 M-2)
  haseq-vextunop---fam12 = record { _=?_ = eq-vextunop---fam12-fun }

data vextunop---fam13 (M-1 : M) (M-2 : M) : Set where
  EXTADD-PAIRWISE : (sx-51565 : sx) → vextunop---fam13 M-1 M-2 {- 1 premise(s) dropped -}

eq-vextunop---fam13-fun : {M-1 : M} → {M-2 : M} → (vextunop---fam13 M-1 M-2) → (vextunop---fam13 M-1 M-2) → Bool
eq-vextunop---fam13-fun (EXTADD-PAIRWISE x0) (EXTADD-PAIRWISE y0) = (x0 =? y0)
instance
  haseq-vextunop---fam13 : {M-1 : M} → {M-2 : M} → HasEq (vextunop---fam13 M-1 M-2)
  haseq-vextunop---fam13 = record { _=?_ = eq-vextunop---fam13-fun }

data vextunop---fam14 (M-1 : M) (M-2 : M) : Set where
  EXTADD-PAIRWISE : (sx-51566 : sx) → vextunop---fam14 M-1 M-2 {- 1 premise(s) dropped -}

eq-vextunop---fam14-fun : {M-1 : M} → {M-2 : M} → (vextunop---fam14 M-1 M-2) → (vextunop---fam14 M-1 M-2) → Bool
eq-vextunop---fam14-fun (EXTADD-PAIRWISE x0) (EXTADD-PAIRWISE y0) = (x0 =? y0)
instance
  haseq-vextunop---fam14 : {M-1 : M} → {M-2 : M} → HasEq (vextunop---fam14 M-1 M-2)
  haseq-vextunop---fam14 = record { _=?_ = eq-vextunop---fam14-fun }

data vextunop---fam15 (M-1 : M) (M-2 : M) : Set where
  EXTADD-PAIRWISE : (sx-51567 : sx) → vextunop---fam15 M-1 M-2 {- 1 premise(s) dropped -}

eq-vextunop---fam15-fun : {M-1 : M} → {M-2 : M} → (vextunop---fam15 M-1 M-2) → (vextunop---fam15 M-1 M-2) → Bool
eq-vextunop---fam15-fun (EXTADD-PAIRWISE x0) (EXTADD-PAIRWISE y0) = (x0 =? y0)
instance
  haseq-vextunop---fam15 : {M-1 : M} → {M-2 : M} → HasEq (vextunop---fam15 M-1 M-2)
  haseq-vextunop---fam15 = record { _=?_ = eq-vextunop---fam15-fun }

vextunop-- : (ishape-1 : ishape) (ishape-2 : ishape) → Set
vextunop-- (mk-ishape (X lanetype-I32 (mk-dim M-1))) (mk-ishape (X lanetype-I32 (mk-dim M-2))) = vextunop---fam0 M-1 M-2
vextunop-- (mk-ishape (X lanetype-I64 (mk-dim M-1))) (mk-ishape (X lanetype-I32 (mk-dim M-2))) = vextunop---fam1 M-1 M-2
vextunop-- (mk-ishape (X lanetype-I8 (mk-dim M-1))) (mk-ishape (X lanetype-I32 (mk-dim M-2))) = vextunop---fam2 M-1 M-2
vextunop-- (mk-ishape (X lanetype-I16 (mk-dim M-1))) (mk-ishape (X lanetype-I32 (mk-dim M-2))) = vextunop---fam3 M-1 M-2
vextunop-- (mk-ishape (X lanetype-I32 (mk-dim M-1))) (mk-ishape (X lanetype-I64 (mk-dim M-2))) = vextunop---fam4 M-1 M-2
vextunop-- (mk-ishape (X lanetype-I64 (mk-dim M-1))) (mk-ishape (X lanetype-I64 (mk-dim M-2))) = vextunop---fam5 M-1 M-2
vextunop-- (mk-ishape (X lanetype-I8 (mk-dim M-1))) (mk-ishape (X lanetype-I64 (mk-dim M-2))) = vextunop---fam6 M-1 M-2
vextunop-- (mk-ishape (X lanetype-I16 (mk-dim M-1))) (mk-ishape (X lanetype-I64 (mk-dim M-2))) = vextunop---fam7 M-1 M-2
vextunop-- (mk-ishape (X lanetype-I32 (mk-dim M-1))) (mk-ishape (X lanetype-I8 (mk-dim M-2))) = vextunop---fam8 M-1 M-2
vextunop-- (mk-ishape (X lanetype-I64 (mk-dim M-1))) (mk-ishape (X lanetype-I8 (mk-dim M-2))) = vextunop---fam9 M-1 M-2
vextunop-- (mk-ishape (X lanetype-I8 (mk-dim M-1))) (mk-ishape (X lanetype-I8 (mk-dim M-2))) = vextunop---fam10 M-1 M-2
vextunop-- (mk-ishape (X lanetype-I16 (mk-dim M-1))) (mk-ishape (X lanetype-I8 (mk-dim M-2))) = vextunop---fam11 M-1 M-2
vextunop-- (mk-ishape (X lanetype-I32 (mk-dim M-1))) (mk-ishape (X lanetype-I16 (mk-dim M-2))) = vextunop---fam12 M-1 M-2
vextunop-- (mk-ishape (X lanetype-I64 (mk-dim M-1))) (mk-ishape (X lanetype-I16 (mk-dim M-2))) = vextunop---fam13 M-1 M-2
vextunop-- (mk-ishape (X lanetype-I8 (mk-dim M-1))) (mk-ishape (X lanetype-I16 (mk-dim M-2))) = vextunop---fam14 M-1 M-2
vextunop-- (mk-ishape (X lanetype-I16 (mk-dim M-1))) (mk-ishape (X lanetype-I16 (mk-dim M-2))) = vextunop---fam15 M-1 M-2
vextunop-- _ _ = ⊤

{- Type Family Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:151.1-151.60 -}
data vextbinop---fam0 (M-1 : M) (M-2 : M) : Set where
  EXTMUL : (half-3380 : half) → (sx-51568 : sx) → vextbinop---fam0 M-1 M-2 {- 1 premise(s) dropped -}
  DOTS : vextbinop---fam0 M-1 M-2 {- 1 premise(s) dropped -}
  RELAXED-DOTS : vextbinop---fam0 M-1 M-2 {- 1 premise(s) dropped -}

eq-vextbinop---fam0-fun : {M-1 : M} → {M-2 : M} → (vextbinop---fam0 M-1 M-2) → (vextbinop---fam0 M-1 M-2) → Bool
eq-vextbinop---fam0-fun (EXTMUL x0 x1) (EXTMUL y0 y1) = (x0 =? y0) ∧ (x1 =? y1)
eq-vextbinop---fam0-fun DOTS DOTS = true
eq-vextbinop---fam0-fun RELAXED-DOTS RELAXED-DOTS = true
eq-vextbinop---fam0-fun _ _ = false
instance
  haseq-vextbinop---fam0 : {M-1 : M} → {M-2 : M} → HasEq (vextbinop---fam0 M-1 M-2)
  haseq-vextbinop---fam0 = record { _=?_ = eq-vextbinop---fam0-fun }

data vextbinop---fam1 (M-1 : M) (M-2 : M) : Set where
  EXTMUL : (half-3381 : half) → (sx-51569 : sx) → vextbinop---fam1 M-1 M-2 {- 1 premise(s) dropped -}
  DOTS : vextbinop---fam1 M-1 M-2 {- 1 premise(s) dropped -}
  RELAXED-DOTS : vextbinop---fam1 M-1 M-2 {- 1 premise(s) dropped -}

eq-vextbinop---fam1-fun : {M-1 : M} → {M-2 : M} → (vextbinop---fam1 M-1 M-2) → (vextbinop---fam1 M-1 M-2) → Bool
eq-vextbinop---fam1-fun (EXTMUL x0 x1) (EXTMUL y0 y1) = (x0 =? y0) ∧ (x1 =? y1)
eq-vextbinop---fam1-fun DOTS DOTS = true
eq-vextbinop---fam1-fun RELAXED-DOTS RELAXED-DOTS = true
eq-vextbinop---fam1-fun _ _ = false
instance
  haseq-vextbinop---fam1 : {M-1 : M} → {M-2 : M} → HasEq (vextbinop---fam1 M-1 M-2)
  haseq-vextbinop---fam1 = record { _=?_ = eq-vextbinop---fam1-fun }

data vextbinop---fam2 (M-1 : M) (M-2 : M) : Set where
  EXTMUL : (half-3382 : half) → (sx-51570 : sx) → vextbinop---fam2 M-1 M-2 {- 1 premise(s) dropped -}
  DOTS : vextbinop---fam2 M-1 M-2 {- 1 premise(s) dropped -}
  RELAXED-DOTS : vextbinop---fam2 M-1 M-2 {- 1 premise(s) dropped -}

eq-vextbinop---fam2-fun : {M-1 : M} → {M-2 : M} → (vextbinop---fam2 M-1 M-2) → (vextbinop---fam2 M-1 M-2) → Bool
eq-vextbinop---fam2-fun (EXTMUL x0 x1) (EXTMUL y0 y1) = (x0 =? y0) ∧ (x1 =? y1)
eq-vextbinop---fam2-fun DOTS DOTS = true
eq-vextbinop---fam2-fun RELAXED-DOTS RELAXED-DOTS = true
eq-vextbinop---fam2-fun _ _ = false
instance
  haseq-vextbinop---fam2 : {M-1 : M} → {M-2 : M} → HasEq (vextbinop---fam2 M-1 M-2)
  haseq-vextbinop---fam2 = record { _=?_ = eq-vextbinop---fam2-fun }

data vextbinop---fam3 (M-1 : M) (M-2 : M) : Set where
  EXTMUL : (half-3383 : half) → (sx-51571 : sx) → vextbinop---fam3 M-1 M-2 {- 1 premise(s) dropped -}
  DOTS : vextbinop---fam3 M-1 M-2 {- 1 premise(s) dropped -}
  RELAXED-DOTS : vextbinop---fam3 M-1 M-2 {- 1 premise(s) dropped -}

eq-vextbinop---fam3-fun : {M-1 : M} → {M-2 : M} → (vextbinop---fam3 M-1 M-2) → (vextbinop---fam3 M-1 M-2) → Bool
eq-vextbinop---fam3-fun (EXTMUL x0 x1) (EXTMUL y0 y1) = (x0 =? y0) ∧ (x1 =? y1)
eq-vextbinop---fam3-fun DOTS DOTS = true
eq-vextbinop---fam3-fun RELAXED-DOTS RELAXED-DOTS = true
eq-vextbinop---fam3-fun _ _ = false
instance
  haseq-vextbinop---fam3 : {M-1 : M} → {M-2 : M} → HasEq (vextbinop---fam3 M-1 M-2)
  haseq-vextbinop---fam3 = record { _=?_ = eq-vextbinop---fam3-fun }

data vextbinop---fam4 (M-1 : M) (M-2 : M) : Set where
  EXTMUL : (half-3384 : half) → (sx-51572 : sx) → vextbinop---fam4 M-1 M-2 {- 1 premise(s) dropped -}
  DOTS : vextbinop---fam4 M-1 M-2 {- 1 premise(s) dropped -}
  RELAXED-DOTS : vextbinop---fam4 M-1 M-2 {- 1 premise(s) dropped -}

eq-vextbinop---fam4-fun : {M-1 : M} → {M-2 : M} → (vextbinop---fam4 M-1 M-2) → (vextbinop---fam4 M-1 M-2) → Bool
eq-vextbinop---fam4-fun (EXTMUL x0 x1) (EXTMUL y0 y1) = (x0 =? y0) ∧ (x1 =? y1)
eq-vextbinop---fam4-fun DOTS DOTS = true
eq-vextbinop---fam4-fun RELAXED-DOTS RELAXED-DOTS = true
eq-vextbinop---fam4-fun _ _ = false
instance
  haseq-vextbinop---fam4 : {M-1 : M} → {M-2 : M} → HasEq (vextbinop---fam4 M-1 M-2)
  haseq-vextbinop---fam4 = record { _=?_ = eq-vextbinop---fam4-fun }

data vextbinop---fam5 (M-1 : M) (M-2 : M) : Set where
  EXTMUL : (half-3385 : half) → (sx-51573 : sx) → vextbinop---fam5 M-1 M-2 {- 1 premise(s) dropped -}
  DOTS : vextbinop---fam5 M-1 M-2 {- 1 premise(s) dropped -}
  RELAXED-DOTS : vextbinop---fam5 M-1 M-2 {- 1 premise(s) dropped -}

eq-vextbinop---fam5-fun : {M-1 : M} → {M-2 : M} → (vextbinop---fam5 M-1 M-2) → (vextbinop---fam5 M-1 M-2) → Bool
eq-vextbinop---fam5-fun (EXTMUL x0 x1) (EXTMUL y0 y1) = (x0 =? y0) ∧ (x1 =? y1)
eq-vextbinop---fam5-fun DOTS DOTS = true
eq-vextbinop---fam5-fun RELAXED-DOTS RELAXED-DOTS = true
eq-vextbinop---fam5-fun _ _ = false
instance
  haseq-vextbinop---fam5 : {M-1 : M} → {M-2 : M} → HasEq (vextbinop---fam5 M-1 M-2)
  haseq-vextbinop---fam5 = record { _=?_ = eq-vextbinop---fam5-fun }

data vextbinop---fam6 (M-1 : M) (M-2 : M) : Set where
  EXTMUL : (half-3386 : half) → (sx-51574 : sx) → vextbinop---fam6 M-1 M-2 {- 1 premise(s) dropped -}
  DOTS : vextbinop---fam6 M-1 M-2 {- 1 premise(s) dropped -}
  RELAXED-DOTS : vextbinop---fam6 M-1 M-2 {- 1 premise(s) dropped -}

eq-vextbinop---fam6-fun : {M-1 : M} → {M-2 : M} → (vextbinop---fam6 M-1 M-2) → (vextbinop---fam6 M-1 M-2) → Bool
eq-vextbinop---fam6-fun (EXTMUL x0 x1) (EXTMUL y0 y1) = (x0 =? y0) ∧ (x1 =? y1)
eq-vextbinop---fam6-fun DOTS DOTS = true
eq-vextbinop---fam6-fun RELAXED-DOTS RELAXED-DOTS = true
eq-vextbinop---fam6-fun _ _ = false
instance
  haseq-vextbinop---fam6 : {M-1 : M} → {M-2 : M} → HasEq (vextbinop---fam6 M-1 M-2)
  haseq-vextbinop---fam6 = record { _=?_ = eq-vextbinop---fam6-fun }

data vextbinop---fam7 (M-1 : M) (M-2 : M) : Set where
  EXTMUL : (half-3387 : half) → (sx-51575 : sx) → vextbinop---fam7 M-1 M-2 {- 1 premise(s) dropped -}
  DOTS : vextbinop---fam7 M-1 M-2 {- 1 premise(s) dropped -}
  RELAXED-DOTS : vextbinop---fam7 M-1 M-2 {- 1 premise(s) dropped -}

eq-vextbinop---fam7-fun : {M-1 : M} → {M-2 : M} → (vextbinop---fam7 M-1 M-2) → (vextbinop---fam7 M-1 M-2) → Bool
eq-vextbinop---fam7-fun (EXTMUL x0 x1) (EXTMUL y0 y1) = (x0 =? y0) ∧ (x1 =? y1)
eq-vextbinop---fam7-fun DOTS DOTS = true
eq-vextbinop---fam7-fun RELAXED-DOTS RELAXED-DOTS = true
eq-vextbinop---fam7-fun _ _ = false
instance
  haseq-vextbinop---fam7 : {M-1 : M} → {M-2 : M} → HasEq (vextbinop---fam7 M-1 M-2)
  haseq-vextbinop---fam7 = record { _=?_ = eq-vextbinop---fam7-fun }

data vextbinop---fam8 (M-1 : M) (M-2 : M) : Set where
  EXTMUL : (half-3388 : half) → (sx-51576 : sx) → vextbinop---fam8 M-1 M-2 {- 1 premise(s) dropped -}
  DOTS : vextbinop---fam8 M-1 M-2 {- 1 premise(s) dropped -}
  RELAXED-DOTS : vextbinop---fam8 M-1 M-2 {- 1 premise(s) dropped -}

eq-vextbinop---fam8-fun : {M-1 : M} → {M-2 : M} → (vextbinop---fam8 M-1 M-2) → (vextbinop---fam8 M-1 M-2) → Bool
eq-vextbinop---fam8-fun (EXTMUL x0 x1) (EXTMUL y0 y1) = (x0 =? y0) ∧ (x1 =? y1)
eq-vextbinop---fam8-fun DOTS DOTS = true
eq-vextbinop---fam8-fun RELAXED-DOTS RELAXED-DOTS = true
eq-vextbinop---fam8-fun _ _ = false
instance
  haseq-vextbinop---fam8 : {M-1 : M} → {M-2 : M} → HasEq (vextbinop---fam8 M-1 M-2)
  haseq-vextbinop---fam8 = record { _=?_ = eq-vextbinop---fam8-fun }

data vextbinop---fam9 (M-1 : M) (M-2 : M) : Set where
  EXTMUL : (half-3389 : half) → (sx-51577 : sx) → vextbinop---fam9 M-1 M-2 {- 1 premise(s) dropped -}
  DOTS : vextbinop---fam9 M-1 M-2 {- 1 premise(s) dropped -}
  RELAXED-DOTS : vextbinop---fam9 M-1 M-2 {- 1 premise(s) dropped -}

eq-vextbinop---fam9-fun : {M-1 : M} → {M-2 : M} → (vextbinop---fam9 M-1 M-2) → (vextbinop---fam9 M-1 M-2) → Bool
eq-vextbinop---fam9-fun (EXTMUL x0 x1) (EXTMUL y0 y1) = (x0 =? y0) ∧ (x1 =? y1)
eq-vextbinop---fam9-fun DOTS DOTS = true
eq-vextbinop---fam9-fun RELAXED-DOTS RELAXED-DOTS = true
eq-vextbinop---fam9-fun _ _ = false
instance
  haseq-vextbinop---fam9 : {M-1 : M} → {M-2 : M} → HasEq (vextbinop---fam9 M-1 M-2)
  haseq-vextbinop---fam9 = record { _=?_ = eq-vextbinop---fam9-fun }

data vextbinop---fam10 (M-1 : M) (M-2 : M) : Set where
  EXTMUL : (half-3390 : half) → (sx-51578 : sx) → vextbinop---fam10 M-1 M-2 {- 1 premise(s) dropped -}
  DOTS : vextbinop---fam10 M-1 M-2 {- 1 premise(s) dropped -}
  RELAXED-DOTS : vextbinop---fam10 M-1 M-2 {- 1 premise(s) dropped -}

eq-vextbinop---fam10-fun : {M-1 : M} → {M-2 : M} → (vextbinop---fam10 M-1 M-2) → (vextbinop---fam10 M-1 M-2) → Bool
eq-vextbinop---fam10-fun (EXTMUL x0 x1) (EXTMUL y0 y1) = (x0 =? y0) ∧ (x1 =? y1)
eq-vextbinop---fam10-fun DOTS DOTS = true
eq-vextbinop---fam10-fun RELAXED-DOTS RELAXED-DOTS = true
eq-vextbinop---fam10-fun _ _ = false
instance
  haseq-vextbinop---fam10 : {M-1 : M} → {M-2 : M} → HasEq (vextbinop---fam10 M-1 M-2)
  haseq-vextbinop---fam10 = record { _=?_ = eq-vextbinop---fam10-fun }

data vextbinop---fam11 (M-1 : M) (M-2 : M) : Set where
  EXTMUL : (half-3391 : half) → (sx-51579 : sx) → vextbinop---fam11 M-1 M-2 {- 1 premise(s) dropped -}
  DOTS : vextbinop---fam11 M-1 M-2 {- 1 premise(s) dropped -}
  RELAXED-DOTS : vextbinop---fam11 M-1 M-2 {- 1 premise(s) dropped -}

eq-vextbinop---fam11-fun : {M-1 : M} → {M-2 : M} → (vextbinop---fam11 M-1 M-2) → (vextbinop---fam11 M-1 M-2) → Bool
eq-vextbinop---fam11-fun (EXTMUL x0 x1) (EXTMUL y0 y1) = (x0 =? y0) ∧ (x1 =? y1)
eq-vextbinop---fam11-fun DOTS DOTS = true
eq-vextbinop---fam11-fun RELAXED-DOTS RELAXED-DOTS = true
eq-vextbinop---fam11-fun _ _ = false
instance
  haseq-vextbinop---fam11 : {M-1 : M} → {M-2 : M} → HasEq (vextbinop---fam11 M-1 M-2)
  haseq-vextbinop---fam11 = record { _=?_ = eq-vextbinop---fam11-fun }

data vextbinop---fam12 (M-1 : M) (M-2 : M) : Set where
  EXTMUL : (half-3392 : half) → (sx-51580 : sx) → vextbinop---fam12 M-1 M-2 {- 1 premise(s) dropped -}
  DOTS : vextbinop---fam12 M-1 M-2 {- 1 premise(s) dropped -}
  RELAXED-DOTS : vextbinop---fam12 M-1 M-2 {- 1 premise(s) dropped -}

eq-vextbinop---fam12-fun : {M-1 : M} → {M-2 : M} → (vextbinop---fam12 M-1 M-2) → (vextbinop---fam12 M-1 M-2) → Bool
eq-vextbinop---fam12-fun (EXTMUL x0 x1) (EXTMUL y0 y1) = (x0 =? y0) ∧ (x1 =? y1)
eq-vextbinop---fam12-fun DOTS DOTS = true
eq-vextbinop---fam12-fun RELAXED-DOTS RELAXED-DOTS = true
eq-vextbinop---fam12-fun _ _ = false
instance
  haseq-vextbinop---fam12 : {M-1 : M} → {M-2 : M} → HasEq (vextbinop---fam12 M-1 M-2)
  haseq-vextbinop---fam12 = record { _=?_ = eq-vextbinop---fam12-fun }

data vextbinop---fam13 (M-1 : M) (M-2 : M) : Set where
  EXTMUL : (half-3393 : half) → (sx-51581 : sx) → vextbinop---fam13 M-1 M-2 {- 1 premise(s) dropped -}
  DOTS : vextbinop---fam13 M-1 M-2 {- 1 premise(s) dropped -}
  RELAXED-DOTS : vextbinop---fam13 M-1 M-2 {- 1 premise(s) dropped -}

eq-vextbinop---fam13-fun : {M-1 : M} → {M-2 : M} → (vextbinop---fam13 M-1 M-2) → (vextbinop---fam13 M-1 M-2) → Bool
eq-vextbinop---fam13-fun (EXTMUL x0 x1) (EXTMUL y0 y1) = (x0 =? y0) ∧ (x1 =? y1)
eq-vextbinop---fam13-fun DOTS DOTS = true
eq-vextbinop---fam13-fun RELAXED-DOTS RELAXED-DOTS = true
eq-vextbinop---fam13-fun _ _ = false
instance
  haseq-vextbinop---fam13 : {M-1 : M} → {M-2 : M} → HasEq (vextbinop---fam13 M-1 M-2)
  haseq-vextbinop---fam13 = record { _=?_ = eq-vextbinop---fam13-fun }

data vextbinop---fam14 (M-1 : M) (M-2 : M) : Set where
  EXTMUL : (half-3394 : half) → (sx-51582 : sx) → vextbinop---fam14 M-1 M-2 {- 1 premise(s) dropped -}
  DOTS : vextbinop---fam14 M-1 M-2 {- 1 premise(s) dropped -}
  RELAXED-DOTS : vextbinop---fam14 M-1 M-2 {- 1 premise(s) dropped -}

eq-vextbinop---fam14-fun : {M-1 : M} → {M-2 : M} → (vextbinop---fam14 M-1 M-2) → (vextbinop---fam14 M-1 M-2) → Bool
eq-vextbinop---fam14-fun (EXTMUL x0 x1) (EXTMUL y0 y1) = (x0 =? y0) ∧ (x1 =? y1)
eq-vextbinop---fam14-fun DOTS DOTS = true
eq-vextbinop---fam14-fun RELAXED-DOTS RELAXED-DOTS = true
eq-vextbinop---fam14-fun _ _ = false
instance
  haseq-vextbinop---fam14 : {M-1 : M} → {M-2 : M} → HasEq (vextbinop---fam14 M-1 M-2)
  haseq-vextbinop---fam14 = record { _=?_ = eq-vextbinop---fam14-fun }

data vextbinop---fam15 (M-1 : M) (M-2 : M) : Set where
  EXTMUL : (half-3395 : half) → (sx-51583 : sx) → vextbinop---fam15 M-1 M-2 {- 1 premise(s) dropped -}
  DOTS : vextbinop---fam15 M-1 M-2 {- 1 premise(s) dropped -}
  RELAXED-DOTS : vextbinop---fam15 M-1 M-2 {- 1 premise(s) dropped -}

eq-vextbinop---fam15-fun : {M-1 : M} → {M-2 : M} → (vextbinop---fam15 M-1 M-2) → (vextbinop---fam15 M-1 M-2) → Bool
eq-vextbinop---fam15-fun (EXTMUL x0 x1) (EXTMUL y0 y1) = (x0 =? y0) ∧ (x1 =? y1)
eq-vextbinop---fam15-fun DOTS DOTS = true
eq-vextbinop---fam15-fun RELAXED-DOTS RELAXED-DOTS = true
eq-vextbinop---fam15-fun _ _ = false
instance
  haseq-vextbinop---fam15 : {M-1 : M} → {M-2 : M} → HasEq (vextbinop---fam15 M-1 M-2)
  haseq-vextbinop---fam15 = record { _=?_ = eq-vextbinop---fam15-fun }

vextbinop-- : (ishape-1 : ishape) (ishape-2 : ishape) → Set
vextbinop-- (mk-ishape (X lanetype-I32 (mk-dim M-1))) (mk-ishape (X lanetype-I32 (mk-dim M-2))) = vextbinop---fam0 M-1 M-2
vextbinop-- (mk-ishape (X lanetype-I64 (mk-dim M-1))) (mk-ishape (X lanetype-I32 (mk-dim M-2))) = vextbinop---fam1 M-1 M-2
vextbinop-- (mk-ishape (X lanetype-I8 (mk-dim M-1))) (mk-ishape (X lanetype-I32 (mk-dim M-2))) = vextbinop---fam2 M-1 M-2
vextbinop-- (mk-ishape (X lanetype-I16 (mk-dim M-1))) (mk-ishape (X lanetype-I32 (mk-dim M-2))) = vextbinop---fam3 M-1 M-2
vextbinop-- (mk-ishape (X lanetype-I32 (mk-dim M-1))) (mk-ishape (X lanetype-I64 (mk-dim M-2))) = vextbinop---fam4 M-1 M-2
vextbinop-- (mk-ishape (X lanetype-I64 (mk-dim M-1))) (mk-ishape (X lanetype-I64 (mk-dim M-2))) = vextbinop---fam5 M-1 M-2
vextbinop-- (mk-ishape (X lanetype-I8 (mk-dim M-1))) (mk-ishape (X lanetype-I64 (mk-dim M-2))) = vextbinop---fam6 M-1 M-2
vextbinop-- (mk-ishape (X lanetype-I16 (mk-dim M-1))) (mk-ishape (X lanetype-I64 (mk-dim M-2))) = vextbinop---fam7 M-1 M-2
vextbinop-- (mk-ishape (X lanetype-I32 (mk-dim M-1))) (mk-ishape (X lanetype-I8 (mk-dim M-2))) = vextbinop---fam8 M-1 M-2
vextbinop-- (mk-ishape (X lanetype-I64 (mk-dim M-1))) (mk-ishape (X lanetype-I8 (mk-dim M-2))) = vextbinop---fam9 M-1 M-2
vextbinop-- (mk-ishape (X lanetype-I8 (mk-dim M-1))) (mk-ishape (X lanetype-I8 (mk-dim M-2))) = vextbinop---fam10 M-1 M-2
vextbinop-- (mk-ishape (X lanetype-I16 (mk-dim M-1))) (mk-ishape (X lanetype-I8 (mk-dim M-2))) = vextbinop---fam11 M-1 M-2
vextbinop-- (mk-ishape (X lanetype-I32 (mk-dim M-1))) (mk-ishape (X lanetype-I16 (mk-dim M-2))) = vextbinop---fam12 M-1 M-2
vextbinop-- (mk-ishape (X lanetype-I64 (mk-dim M-1))) (mk-ishape (X lanetype-I16 (mk-dim M-2))) = vextbinop---fam13 M-1 M-2
vextbinop-- (mk-ishape (X lanetype-I8 (mk-dim M-1))) (mk-ishape (X lanetype-I16 (mk-dim M-2))) = vextbinop---fam14 M-1 M-2
vextbinop-- (mk-ishape (X lanetype-I16 (mk-dim M-1))) (mk-ishape (X lanetype-I16 (mk-dim M-2))) = vextbinop---fam15 M-1 M-2
vextbinop-- _ _ = ⊤

{- Type Family Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:160.1-160.61 -}
data vextternop---fam0 (M-1 : M) (M-2 : M) : Set where
  RELAXED-DOT-ADDS : vextternop---fam0 M-1 M-2 {- 1 premise(s) dropped -}

eq-vextternop---fam0-fun : {M-1 : M} → {M-2 : M} → (vextternop---fam0 M-1 M-2) → (vextternop---fam0 M-1 M-2) → Bool
eq-vextternop---fam0-fun RELAXED-DOT-ADDS RELAXED-DOT-ADDS = true
instance
  haseq-vextternop---fam0 : {M-1 : M} → {M-2 : M} → HasEq (vextternop---fam0 M-1 M-2)
  haseq-vextternop---fam0 = record { _=?_ = eq-vextternop---fam0-fun }

data vextternop---fam1 (M-1 : M) (M-2 : M) : Set where
  RELAXED-DOT-ADDS : vextternop---fam1 M-1 M-2 {- 1 premise(s) dropped -}

eq-vextternop---fam1-fun : {M-1 : M} → {M-2 : M} → (vextternop---fam1 M-1 M-2) → (vextternop---fam1 M-1 M-2) → Bool
eq-vextternop---fam1-fun RELAXED-DOT-ADDS RELAXED-DOT-ADDS = true
instance
  haseq-vextternop---fam1 : {M-1 : M} → {M-2 : M} → HasEq (vextternop---fam1 M-1 M-2)
  haseq-vextternop---fam1 = record { _=?_ = eq-vextternop---fam1-fun }

data vextternop---fam2 (M-1 : M) (M-2 : M) : Set where
  RELAXED-DOT-ADDS : vextternop---fam2 M-1 M-2 {- 1 premise(s) dropped -}

eq-vextternop---fam2-fun : {M-1 : M} → {M-2 : M} → (vextternop---fam2 M-1 M-2) → (vextternop---fam2 M-1 M-2) → Bool
eq-vextternop---fam2-fun RELAXED-DOT-ADDS RELAXED-DOT-ADDS = true
instance
  haseq-vextternop---fam2 : {M-1 : M} → {M-2 : M} → HasEq (vextternop---fam2 M-1 M-2)
  haseq-vextternop---fam2 = record { _=?_ = eq-vextternop---fam2-fun }

data vextternop---fam3 (M-1 : M) (M-2 : M) : Set where
  RELAXED-DOT-ADDS : vextternop---fam3 M-1 M-2 {- 1 premise(s) dropped -}

eq-vextternop---fam3-fun : {M-1 : M} → {M-2 : M} → (vextternop---fam3 M-1 M-2) → (vextternop---fam3 M-1 M-2) → Bool
eq-vextternop---fam3-fun RELAXED-DOT-ADDS RELAXED-DOT-ADDS = true
instance
  haseq-vextternop---fam3 : {M-1 : M} → {M-2 : M} → HasEq (vextternop---fam3 M-1 M-2)
  haseq-vextternop---fam3 = record { _=?_ = eq-vextternop---fam3-fun }

data vextternop---fam4 (M-1 : M) (M-2 : M) : Set where
  RELAXED-DOT-ADDS : vextternop---fam4 M-1 M-2 {- 1 premise(s) dropped -}

eq-vextternop---fam4-fun : {M-1 : M} → {M-2 : M} → (vextternop---fam4 M-1 M-2) → (vextternop---fam4 M-1 M-2) → Bool
eq-vextternop---fam4-fun RELAXED-DOT-ADDS RELAXED-DOT-ADDS = true
instance
  haseq-vextternop---fam4 : {M-1 : M} → {M-2 : M} → HasEq (vextternop---fam4 M-1 M-2)
  haseq-vextternop---fam4 = record { _=?_ = eq-vextternop---fam4-fun }

data vextternop---fam5 (M-1 : M) (M-2 : M) : Set where
  RELAXED-DOT-ADDS : vextternop---fam5 M-1 M-2 {- 1 premise(s) dropped -}

eq-vextternop---fam5-fun : {M-1 : M} → {M-2 : M} → (vextternop---fam5 M-1 M-2) → (vextternop---fam5 M-1 M-2) → Bool
eq-vextternop---fam5-fun RELAXED-DOT-ADDS RELAXED-DOT-ADDS = true
instance
  haseq-vextternop---fam5 : {M-1 : M} → {M-2 : M} → HasEq (vextternop---fam5 M-1 M-2)
  haseq-vextternop---fam5 = record { _=?_ = eq-vextternop---fam5-fun }

data vextternop---fam6 (M-1 : M) (M-2 : M) : Set where
  RELAXED-DOT-ADDS : vextternop---fam6 M-1 M-2 {- 1 premise(s) dropped -}

eq-vextternop---fam6-fun : {M-1 : M} → {M-2 : M} → (vextternop---fam6 M-1 M-2) → (vextternop---fam6 M-1 M-2) → Bool
eq-vextternop---fam6-fun RELAXED-DOT-ADDS RELAXED-DOT-ADDS = true
instance
  haseq-vextternop---fam6 : {M-1 : M} → {M-2 : M} → HasEq (vextternop---fam6 M-1 M-2)
  haseq-vextternop---fam6 = record { _=?_ = eq-vextternop---fam6-fun }

data vextternop---fam7 (M-1 : M) (M-2 : M) : Set where
  RELAXED-DOT-ADDS : vextternop---fam7 M-1 M-2 {- 1 premise(s) dropped -}

eq-vextternop---fam7-fun : {M-1 : M} → {M-2 : M} → (vextternop---fam7 M-1 M-2) → (vextternop---fam7 M-1 M-2) → Bool
eq-vextternop---fam7-fun RELAXED-DOT-ADDS RELAXED-DOT-ADDS = true
instance
  haseq-vextternop---fam7 : {M-1 : M} → {M-2 : M} → HasEq (vextternop---fam7 M-1 M-2)
  haseq-vextternop---fam7 = record { _=?_ = eq-vextternop---fam7-fun }

data vextternop---fam8 (M-1 : M) (M-2 : M) : Set where
  RELAXED-DOT-ADDS : vextternop---fam8 M-1 M-2 {- 1 premise(s) dropped -}

eq-vextternop---fam8-fun : {M-1 : M} → {M-2 : M} → (vextternop---fam8 M-1 M-2) → (vextternop---fam8 M-1 M-2) → Bool
eq-vextternop---fam8-fun RELAXED-DOT-ADDS RELAXED-DOT-ADDS = true
instance
  haseq-vextternop---fam8 : {M-1 : M} → {M-2 : M} → HasEq (vextternop---fam8 M-1 M-2)
  haseq-vextternop---fam8 = record { _=?_ = eq-vextternop---fam8-fun }

data vextternop---fam9 (M-1 : M) (M-2 : M) : Set where
  RELAXED-DOT-ADDS : vextternop---fam9 M-1 M-2 {- 1 premise(s) dropped -}

eq-vextternop---fam9-fun : {M-1 : M} → {M-2 : M} → (vextternop---fam9 M-1 M-2) → (vextternop---fam9 M-1 M-2) → Bool
eq-vextternop---fam9-fun RELAXED-DOT-ADDS RELAXED-DOT-ADDS = true
instance
  haseq-vextternop---fam9 : {M-1 : M} → {M-2 : M} → HasEq (vextternop---fam9 M-1 M-2)
  haseq-vextternop---fam9 = record { _=?_ = eq-vextternop---fam9-fun }

data vextternop---fam10 (M-1 : M) (M-2 : M) : Set where
  RELAXED-DOT-ADDS : vextternop---fam10 M-1 M-2 {- 1 premise(s) dropped -}

eq-vextternop---fam10-fun : {M-1 : M} → {M-2 : M} → (vextternop---fam10 M-1 M-2) → (vextternop---fam10 M-1 M-2) → Bool
eq-vextternop---fam10-fun RELAXED-DOT-ADDS RELAXED-DOT-ADDS = true
instance
  haseq-vextternop---fam10 : {M-1 : M} → {M-2 : M} → HasEq (vextternop---fam10 M-1 M-2)
  haseq-vextternop---fam10 = record { _=?_ = eq-vextternop---fam10-fun }

data vextternop---fam11 (M-1 : M) (M-2 : M) : Set where
  RELAXED-DOT-ADDS : vextternop---fam11 M-1 M-2 {- 1 premise(s) dropped -}

eq-vextternop---fam11-fun : {M-1 : M} → {M-2 : M} → (vextternop---fam11 M-1 M-2) → (vextternop---fam11 M-1 M-2) → Bool
eq-vextternop---fam11-fun RELAXED-DOT-ADDS RELAXED-DOT-ADDS = true
instance
  haseq-vextternop---fam11 : {M-1 : M} → {M-2 : M} → HasEq (vextternop---fam11 M-1 M-2)
  haseq-vextternop---fam11 = record { _=?_ = eq-vextternop---fam11-fun }

data vextternop---fam12 (M-1 : M) (M-2 : M) : Set where
  RELAXED-DOT-ADDS : vextternop---fam12 M-1 M-2 {- 1 premise(s) dropped -}

eq-vextternop---fam12-fun : {M-1 : M} → {M-2 : M} → (vextternop---fam12 M-1 M-2) → (vextternop---fam12 M-1 M-2) → Bool
eq-vextternop---fam12-fun RELAXED-DOT-ADDS RELAXED-DOT-ADDS = true
instance
  haseq-vextternop---fam12 : {M-1 : M} → {M-2 : M} → HasEq (vextternop---fam12 M-1 M-2)
  haseq-vextternop---fam12 = record { _=?_ = eq-vextternop---fam12-fun }

data vextternop---fam13 (M-1 : M) (M-2 : M) : Set where
  RELAXED-DOT-ADDS : vextternop---fam13 M-1 M-2 {- 1 premise(s) dropped -}

eq-vextternop---fam13-fun : {M-1 : M} → {M-2 : M} → (vextternop---fam13 M-1 M-2) → (vextternop---fam13 M-1 M-2) → Bool
eq-vextternop---fam13-fun RELAXED-DOT-ADDS RELAXED-DOT-ADDS = true
instance
  haseq-vextternop---fam13 : {M-1 : M} → {M-2 : M} → HasEq (vextternop---fam13 M-1 M-2)
  haseq-vextternop---fam13 = record { _=?_ = eq-vextternop---fam13-fun }

data vextternop---fam14 (M-1 : M) (M-2 : M) : Set where
  RELAXED-DOT-ADDS : vextternop---fam14 M-1 M-2 {- 1 premise(s) dropped -}

eq-vextternop---fam14-fun : {M-1 : M} → {M-2 : M} → (vextternop---fam14 M-1 M-2) → (vextternop---fam14 M-1 M-2) → Bool
eq-vextternop---fam14-fun RELAXED-DOT-ADDS RELAXED-DOT-ADDS = true
instance
  haseq-vextternop---fam14 : {M-1 : M} → {M-2 : M} → HasEq (vextternop---fam14 M-1 M-2)
  haseq-vextternop---fam14 = record { _=?_ = eq-vextternop---fam14-fun }

data vextternop---fam15 (M-1 : M) (M-2 : M) : Set where
  RELAXED-DOT-ADDS : vextternop---fam15 M-1 M-2 {- 1 premise(s) dropped -}

eq-vextternop---fam15-fun : {M-1 : M} → {M-2 : M} → (vextternop---fam15 M-1 M-2) → (vextternop---fam15 M-1 M-2) → Bool
eq-vextternop---fam15-fun RELAXED-DOT-ADDS RELAXED-DOT-ADDS = true
instance
  haseq-vextternop---fam15 : {M-1 : M} → {M-2 : M} → HasEq (vextternop---fam15 M-1 M-2)
  haseq-vextternop---fam15 = record { _=?_ = eq-vextternop---fam15-fun }

vextternop-- : (ishape-1 : ishape) (ishape-2 : ishape) → Set
vextternop-- (mk-ishape (X lanetype-I32 (mk-dim M-1))) (mk-ishape (X lanetype-I32 (mk-dim M-2))) = vextternop---fam0 M-1 M-2
vextternop-- (mk-ishape (X lanetype-I64 (mk-dim M-1))) (mk-ishape (X lanetype-I32 (mk-dim M-2))) = vextternop---fam1 M-1 M-2
vextternop-- (mk-ishape (X lanetype-I8 (mk-dim M-1))) (mk-ishape (X lanetype-I32 (mk-dim M-2))) = vextternop---fam2 M-1 M-2
vextternop-- (mk-ishape (X lanetype-I16 (mk-dim M-1))) (mk-ishape (X lanetype-I32 (mk-dim M-2))) = vextternop---fam3 M-1 M-2
vextternop-- (mk-ishape (X lanetype-I32 (mk-dim M-1))) (mk-ishape (X lanetype-I64 (mk-dim M-2))) = vextternop---fam4 M-1 M-2
vextternop-- (mk-ishape (X lanetype-I64 (mk-dim M-1))) (mk-ishape (X lanetype-I64 (mk-dim M-2))) = vextternop---fam5 M-1 M-2
vextternop-- (mk-ishape (X lanetype-I8 (mk-dim M-1))) (mk-ishape (X lanetype-I64 (mk-dim M-2))) = vextternop---fam6 M-1 M-2
vextternop-- (mk-ishape (X lanetype-I16 (mk-dim M-1))) (mk-ishape (X lanetype-I64 (mk-dim M-2))) = vextternop---fam7 M-1 M-2
vextternop-- (mk-ishape (X lanetype-I32 (mk-dim M-1))) (mk-ishape (X lanetype-I8 (mk-dim M-2))) = vextternop---fam8 M-1 M-2
vextternop-- (mk-ishape (X lanetype-I64 (mk-dim M-1))) (mk-ishape (X lanetype-I8 (mk-dim M-2))) = vextternop---fam9 M-1 M-2
vextternop-- (mk-ishape (X lanetype-I8 (mk-dim M-1))) (mk-ishape (X lanetype-I8 (mk-dim M-2))) = vextternop---fam10 M-1 M-2
vextternop-- (mk-ishape (X lanetype-I16 (mk-dim M-1))) (mk-ishape (X lanetype-I8 (mk-dim M-2))) = vextternop---fam11 M-1 M-2
vextternop-- (mk-ishape (X lanetype-I32 (mk-dim M-1))) (mk-ishape (X lanetype-I16 (mk-dim M-2))) = vextternop---fam12 M-1 M-2
vextternop-- (mk-ishape (X lanetype-I64 (mk-dim M-1))) (mk-ishape (X lanetype-I16 (mk-dim M-2))) = vextternop---fam13 M-1 M-2
vextternop-- (mk-ishape (X lanetype-I8 (mk-dim M-1))) (mk-ishape (X lanetype-I16 (mk-dim M-2))) = vextternop---fam14 M-1 M-2
vextternop-- (mk-ishape (X lanetype-I16 (mk-dim M-1))) (mk-ishape (X lanetype-I16 (mk-dim M-2))) = vextternop---fam15 M-1 M-2
vextternop-- _ _ = ⊤

{- Type Family Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:165.1-165.55 -}
data vcvtop---fam0 (M-1 : M) (M-2 : M) : Set where
  vcvtop---EXTEND : (half-3396 : half) → (sx-51584 : sx) → vcvtop---fam0 M-1 M-2 {- 1 premise(s) dropped -}

eq-vcvtop---fam0-fun : {M-1 : M} → {M-2 : M} → (vcvtop---fam0 M-1 M-2) → (vcvtop---fam0 M-1 M-2) → Bool
eq-vcvtop---fam0-fun (vcvtop---EXTEND x0 x1) (vcvtop---EXTEND y0 y1) = (x0 =? y0) ∧ (x1 =? y1)
instance
  haseq-vcvtop---fam0 : {M-1 : M} → {M-2 : M} → HasEq (vcvtop---fam0 M-1 M-2)
  haseq-vcvtop---fam0 = record { _=?_ = eq-vcvtop---fam0-fun }

data vcvtop---fam1 (M-1 : M) (M-2 : M) : Set where
  vcvtop---EXTEND : (half-3397 : half) → (sx-51585 : sx) → vcvtop---fam1 M-1 M-2 {- 1 premise(s) dropped -}

eq-vcvtop---fam1-fun : {M-1 : M} → {M-2 : M} → (vcvtop---fam1 M-1 M-2) → (vcvtop---fam1 M-1 M-2) → Bool
eq-vcvtop---fam1-fun (vcvtop---EXTEND x0 x1) (vcvtop---EXTEND y0 y1) = (x0 =? y0) ∧ (x1 =? y1)
instance
  haseq-vcvtop---fam1 : {M-1 : M} → {M-2 : M} → HasEq (vcvtop---fam1 M-1 M-2)
  haseq-vcvtop---fam1 = record { _=?_ = eq-vcvtop---fam1-fun }

data vcvtop---fam2 (M-1 : M) (M-2 : M) : Set where
  vcvtop---EXTEND : (half-3398 : half) → (sx-51586 : sx) → vcvtop---fam2 M-1 M-2 {- 1 premise(s) dropped -}

eq-vcvtop---fam2-fun : {M-1 : M} → {M-2 : M} → (vcvtop---fam2 M-1 M-2) → (vcvtop---fam2 M-1 M-2) → Bool
eq-vcvtop---fam2-fun (vcvtop---EXTEND x0 x1) (vcvtop---EXTEND y0 y1) = (x0 =? y0) ∧ (x1 =? y1)
instance
  haseq-vcvtop---fam2 : {M-1 : M} → {M-2 : M} → HasEq (vcvtop---fam2 M-1 M-2)
  haseq-vcvtop---fam2 = record { _=?_ = eq-vcvtop---fam2-fun }

data vcvtop---fam3 (M-1 : M) (M-2 : M) : Set where
  vcvtop---EXTEND : (half-3399 : half) → (sx-51587 : sx) → vcvtop---fam3 M-1 M-2 {- 1 premise(s) dropped -}

eq-vcvtop---fam3-fun : {M-1 : M} → {M-2 : M} → (vcvtop---fam3 M-1 M-2) → (vcvtop---fam3 M-1 M-2) → Bool
eq-vcvtop---fam3-fun (vcvtop---EXTEND x0 x1) (vcvtop---EXTEND y0 y1) = (x0 =? y0) ∧ (x1 =? y1)
instance
  haseq-vcvtop---fam3 : {M-1 : M} → {M-2 : M} → HasEq (vcvtop---fam3 M-1 M-2)
  haseq-vcvtop---fam3 = record { _=?_ = eq-vcvtop---fam3-fun }

data vcvtop---fam4 (M-1 : M) (M-2 : M) : Set where
  vcvtop---EXTEND : (half-3400 : half) → (sx-51588 : sx) → vcvtop---fam4 M-1 M-2 {- 1 premise(s) dropped -}

eq-vcvtop---fam4-fun : {M-1 : M} → {M-2 : M} → (vcvtop---fam4 M-1 M-2) → (vcvtop---fam4 M-1 M-2) → Bool
eq-vcvtop---fam4-fun (vcvtop---EXTEND x0 x1) (vcvtop---EXTEND y0 y1) = (x0 =? y0) ∧ (x1 =? y1)
instance
  haseq-vcvtop---fam4 : {M-1 : M} → {M-2 : M} → HasEq (vcvtop---fam4 M-1 M-2)
  haseq-vcvtop---fam4 = record { _=?_ = eq-vcvtop---fam4-fun }

data vcvtop---fam5 (M-1 : M) (M-2 : M) : Set where
  vcvtop---EXTEND : (half-3401 : half) → (sx-51589 : sx) → vcvtop---fam5 M-1 M-2 {- 1 premise(s) dropped -}

eq-vcvtop---fam5-fun : {M-1 : M} → {M-2 : M} → (vcvtop---fam5 M-1 M-2) → (vcvtop---fam5 M-1 M-2) → Bool
eq-vcvtop---fam5-fun (vcvtop---EXTEND x0 x1) (vcvtop---EXTEND y0 y1) = (x0 =? y0) ∧ (x1 =? y1)
instance
  haseq-vcvtop---fam5 : {M-1 : M} → {M-2 : M} → HasEq (vcvtop---fam5 M-1 M-2)
  haseq-vcvtop---fam5 = record { _=?_ = eq-vcvtop---fam5-fun }

data vcvtop---fam6 (M-1 : M) (M-2 : M) : Set where
  vcvtop---EXTEND : (half-3402 : half) → (sx-51590 : sx) → vcvtop---fam6 M-1 M-2 {- 1 premise(s) dropped -}

eq-vcvtop---fam6-fun : {M-1 : M} → {M-2 : M} → (vcvtop---fam6 M-1 M-2) → (vcvtop---fam6 M-1 M-2) → Bool
eq-vcvtop---fam6-fun (vcvtop---EXTEND x0 x1) (vcvtop---EXTEND y0 y1) = (x0 =? y0) ∧ (x1 =? y1)
instance
  haseq-vcvtop---fam6 : {M-1 : M} → {M-2 : M} → HasEq (vcvtop---fam6 M-1 M-2)
  haseq-vcvtop---fam6 = record { _=?_ = eq-vcvtop---fam6-fun }

data vcvtop---fam7 (M-1 : M) (M-2 : M) : Set where
  vcvtop---EXTEND : (half-3403 : half) → (sx-51591 : sx) → vcvtop---fam7 M-1 M-2 {- 1 premise(s) dropped -}

eq-vcvtop---fam7-fun : {M-1 : M} → {M-2 : M} → (vcvtop---fam7 M-1 M-2) → (vcvtop---fam7 M-1 M-2) → Bool
eq-vcvtop---fam7-fun (vcvtop---EXTEND x0 x1) (vcvtop---EXTEND y0 y1) = (x0 =? y0) ∧ (x1 =? y1)
instance
  haseq-vcvtop---fam7 : {M-1 : M} → {M-2 : M} → HasEq (vcvtop---fam7 M-1 M-2)
  haseq-vcvtop---fam7 = record { _=?_ = eq-vcvtop---fam7-fun }

data vcvtop---fam8 (M-1 : M) (M-2 : M) : Set where
  vcvtop---EXTEND : (half-3404 : half) → (sx-51592 : sx) → vcvtop---fam8 M-1 M-2 {- 1 premise(s) dropped -}

eq-vcvtop---fam8-fun : {M-1 : M} → {M-2 : M} → (vcvtop---fam8 M-1 M-2) → (vcvtop---fam8 M-1 M-2) → Bool
eq-vcvtop---fam8-fun (vcvtop---EXTEND x0 x1) (vcvtop---EXTEND y0 y1) = (x0 =? y0) ∧ (x1 =? y1)
instance
  haseq-vcvtop---fam8 : {M-1 : M} → {M-2 : M} → HasEq (vcvtop---fam8 M-1 M-2)
  haseq-vcvtop---fam8 = record { _=?_ = eq-vcvtop---fam8-fun }

data vcvtop---fam9 (M-1 : M) (M-2 : M) : Set where
  vcvtop---EXTEND : (half-3405 : half) → (sx-51593 : sx) → vcvtop---fam9 M-1 M-2 {- 1 premise(s) dropped -}

eq-vcvtop---fam9-fun : {M-1 : M} → {M-2 : M} → (vcvtop---fam9 M-1 M-2) → (vcvtop---fam9 M-1 M-2) → Bool
eq-vcvtop---fam9-fun (vcvtop---EXTEND x0 x1) (vcvtop---EXTEND y0 y1) = (x0 =? y0) ∧ (x1 =? y1)
instance
  haseq-vcvtop---fam9 : {M-1 : M} → {M-2 : M} → HasEq (vcvtop---fam9 M-1 M-2)
  haseq-vcvtop---fam9 = record { _=?_ = eq-vcvtop---fam9-fun }

data vcvtop---fam10 (M-1 : M) (M-2 : M) : Set where
  vcvtop---EXTEND : (half-3406 : half) → (sx-51594 : sx) → vcvtop---fam10 M-1 M-2 {- 1 premise(s) dropped -}

eq-vcvtop---fam10-fun : {M-1 : M} → {M-2 : M} → (vcvtop---fam10 M-1 M-2) → (vcvtop---fam10 M-1 M-2) → Bool
eq-vcvtop---fam10-fun (vcvtop---EXTEND x0 x1) (vcvtop---EXTEND y0 y1) = (x0 =? y0) ∧ (x1 =? y1)
instance
  haseq-vcvtop---fam10 : {M-1 : M} → {M-2 : M} → HasEq (vcvtop---fam10 M-1 M-2)
  haseq-vcvtop---fam10 = record { _=?_ = eq-vcvtop---fam10-fun }

data vcvtop---fam11 (M-1 : M) (M-2 : M) : Set where
  vcvtop---EXTEND : (half-3407 : half) → (sx-51595 : sx) → vcvtop---fam11 M-1 M-2 {- 1 premise(s) dropped -}

eq-vcvtop---fam11-fun : {M-1 : M} → {M-2 : M} → (vcvtop---fam11 M-1 M-2) → (vcvtop---fam11 M-1 M-2) → Bool
eq-vcvtop---fam11-fun (vcvtop---EXTEND x0 x1) (vcvtop---EXTEND y0 y1) = (x0 =? y0) ∧ (x1 =? y1)
instance
  haseq-vcvtop---fam11 : {M-1 : M} → {M-2 : M} → HasEq (vcvtop---fam11 M-1 M-2)
  haseq-vcvtop---fam11 = record { _=?_ = eq-vcvtop---fam11-fun }

data vcvtop---fam12 (M-1 : M) (M-2 : M) : Set where
  vcvtop---EXTEND : (half-3408 : half) → (sx-51596 : sx) → vcvtop---fam12 M-1 M-2 {- 1 premise(s) dropped -}

eq-vcvtop---fam12-fun : {M-1 : M} → {M-2 : M} → (vcvtop---fam12 M-1 M-2) → (vcvtop---fam12 M-1 M-2) → Bool
eq-vcvtop---fam12-fun (vcvtop---EXTEND x0 x1) (vcvtop---EXTEND y0 y1) = (x0 =? y0) ∧ (x1 =? y1)
instance
  haseq-vcvtop---fam12 : {M-1 : M} → {M-2 : M} → HasEq (vcvtop---fam12 M-1 M-2)
  haseq-vcvtop---fam12 = record { _=?_ = eq-vcvtop---fam12-fun }

data vcvtop---fam13 (M-1 : M) (M-2 : M) : Set where
  vcvtop---EXTEND : (half-3409 : half) → (sx-51597 : sx) → vcvtop---fam13 M-1 M-2 {- 1 premise(s) dropped -}

eq-vcvtop---fam13-fun : {M-1 : M} → {M-2 : M} → (vcvtop---fam13 M-1 M-2) → (vcvtop---fam13 M-1 M-2) → Bool
eq-vcvtop---fam13-fun (vcvtop---EXTEND x0 x1) (vcvtop---EXTEND y0 y1) = (x0 =? y0) ∧ (x1 =? y1)
instance
  haseq-vcvtop---fam13 : {M-1 : M} → {M-2 : M} → HasEq (vcvtop---fam13 M-1 M-2)
  haseq-vcvtop---fam13 = record { _=?_ = eq-vcvtop---fam13-fun }

data vcvtop---fam14 (M-1 : M) (M-2 : M) : Set where
  vcvtop---EXTEND : (half-3410 : half) → (sx-51598 : sx) → vcvtop---fam14 M-1 M-2 {- 1 premise(s) dropped -}

eq-vcvtop---fam14-fun : {M-1 : M} → {M-2 : M} → (vcvtop---fam14 M-1 M-2) → (vcvtop---fam14 M-1 M-2) → Bool
eq-vcvtop---fam14-fun (vcvtop---EXTEND x0 x1) (vcvtop---EXTEND y0 y1) = (x0 =? y0) ∧ (x1 =? y1)
instance
  haseq-vcvtop---fam14 : {M-1 : M} → {M-2 : M} → HasEq (vcvtop---fam14 M-1 M-2)
  haseq-vcvtop---fam14 = record { _=?_ = eq-vcvtop---fam14-fun }

data vcvtop---fam15 (M-1 : M) (M-2 : M) : Set where
  vcvtop---EXTEND : (half-3411 : half) → (sx-51599 : sx) → vcvtop---fam15 M-1 M-2 {- 1 premise(s) dropped -}

eq-vcvtop---fam15-fun : {M-1 : M} → {M-2 : M} → (vcvtop---fam15 M-1 M-2) → (vcvtop---fam15 M-1 M-2) → Bool
eq-vcvtop---fam15-fun (vcvtop---EXTEND x0 x1) (vcvtop---EXTEND y0 y1) = (x0 =? y0) ∧ (x1 =? y1)
instance
  haseq-vcvtop---fam15 : {M-1 : M} → {M-2 : M} → HasEq (vcvtop---fam15 M-1 M-2)
  haseq-vcvtop---fam15 = record { _=?_ = eq-vcvtop---fam15-fun }

data vcvtop---fam16 (M-1 : M) (M-2 : M) : Set where
  vcvtop---CONVERT : (half-opt-440 : (Maybe half)) → (sx-51600 : sx) → vcvtop---fam16 M-1 M-2 {- 1 premise(s) dropped -}

eq-vcvtop---fam16-fun : {M-1 : M} → {M-2 : M} → (vcvtop---fam16 M-1 M-2) → (vcvtop---fam16 M-1 M-2) → Bool
eq-vcvtop---fam16-fun (vcvtop---CONVERT x0 x1) (vcvtop---CONVERT y0 y1) = (x0 =? y0) ∧ (x1 =? y1)
instance
  haseq-vcvtop---fam16 : {M-1 : M} → {M-2 : M} → HasEq (vcvtop---fam16 M-1 M-2)
  haseq-vcvtop---fam16 = record { _=?_ = eq-vcvtop---fam16-fun }

data vcvtop---fam17 (M-1 : M) (M-2 : M) : Set where
  vcvtop---CONVERT : (half-opt-441 : (Maybe half)) → (sx-51601 : sx) → vcvtop---fam17 M-1 M-2 {- 1 premise(s) dropped -}

eq-vcvtop---fam17-fun : {M-1 : M} → {M-2 : M} → (vcvtop---fam17 M-1 M-2) → (vcvtop---fam17 M-1 M-2) → Bool
eq-vcvtop---fam17-fun (vcvtop---CONVERT x0 x1) (vcvtop---CONVERT y0 y1) = (x0 =? y0) ∧ (x1 =? y1)
instance
  haseq-vcvtop---fam17 : {M-1 : M} → {M-2 : M} → HasEq (vcvtop---fam17 M-1 M-2)
  haseq-vcvtop---fam17 = record { _=?_ = eq-vcvtop---fam17-fun }

data vcvtop---fam18 (M-1 : M) (M-2 : M) : Set where
  vcvtop---CONVERT : (half-opt-442 : (Maybe half)) → (sx-51602 : sx) → vcvtop---fam18 M-1 M-2 {- 1 premise(s) dropped -}

eq-vcvtop---fam18-fun : {M-1 : M} → {M-2 : M} → (vcvtop---fam18 M-1 M-2) → (vcvtop---fam18 M-1 M-2) → Bool
eq-vcvtop---fam18-fun (vcvtop---CONVERT x0 x1) (vcvtop---CONVERT y0 y1) = (x0 =? y0) ∧ (x1 =? y1)
instance
  haseq-vcvtop---fam18 : {M-1 : M} → {M-2 : M} → HasEq (vcvtop---fam18 M-1 M-2)
  haseq-vcvtop---fam18 = record { _=?_ = eq-vcvtop---fam18-fun }

data vcvtop---fam19 (M-1 : M) (M-2 : M) : Set where
  vcvtop---CONVERT : (half-opt-443 : (Maybe half)) → (sx-51603 : sx) → vcvtop---fam19 M-1 M-2 {- 1 premise(s) dropped -}

eq-vcvtop---fam19-fun : {M-1 : M} → {M-2 : M} → (vcvtop---fam19 M-1 M-2) → (vcvtop---fam19 M-1 M-2) → Bool
eq-vcvtop---fam19-fun (vcvtop---CONVERT x0 x1) (vcvtop---CONVERT y0 y1) = (x0 =? y0) ∧ (x1 =? y1)
instance
  haseq-vcvtop---fam19 : {M-1 : M} → {M-2 : M} → HasEq (vcvtop---fam19 M-1 M-2)
  haseq-vcvtop---fam19 = record { _=?_ = eq-vcvtop---fam19-fun }

data vcvtop---fam20 (M-1 : M) (M-2 : M) : Set where
  vcvtop---CONVERT : (half-opt-444 : (Maybe half)) → (sx-51604 : sx) → vcvtop---fam20 M-1 M-2 {- 1 premise(s) dropped -}

eq-vcvtop---fam20-fun : {M-1 : M} → {M-2 : M} → (vcvtop---fam20 M-1 M-2) → (vcvtop---fam20 M-1 M-2) → Bool
eq-vcvtop---fam20-fun (vcvtop---CONVERT x0 x1) (vcvtop---CONVERT y0 y1) = (x0 =? y0) ∧ (x1 =? y1)
instance
  haseq-vcvtop---fam20 : {M-1 : M} → {M-2 : M} → HasEq (vcvtop---fam20 M-1 M-2)
  haseq-vcvtop---fam20 = record { _=?_ = eq-vcvtop---fam20-fun }

data vcvtop---fam21 (M-1 : M) (M-2 : M) : Set where
  vcvtop---CONVERT : (half-opt-445 : (Maybe half)) → (sx-51605 : sx) → vcvtop---fam21 M-1 M-2 {- 1 premise(s) dropped -}

eq-vcvtop---fam21-fun : {M-1 : M} → {M-2 : M} → (vcvtop---fam21 M-1 M-2) → (vcvtop---fam21 M-1 M-2) → Bool
eq-vcvtop---fam21-fun (vcvtop---CONVERT x0 x1) (vcvtop---CONVERT y0 y1) = (x0 =? y0) ∧ (x1 =? y1)
instance
  haseq-vcvtop---fam21 : {M-1 : M} → {M-2 : M} → HasEq (vcvtop---fam21 M-1 M-2)
  haseq-vcvtop---fam21 = record { _=?_ = eq-vcvtop---fam21-fun }

data vcvtop---fam22 (M-1 : M) (M-2 : M) : Set where
  vcvtop---CONVERT : (half-opt-446 : (Maybe half)) → (sx-51606 : sx) → vcvtop---fam22 M-1 M-2 {- 1 premise(s) dropped -}

eq-vcvtop---fam22-fun : {M-1 : M} → {M-2 : M} → (vcvtop---fam22 M-1 M-2) → (vcvtop---fam22 M-1 M-2) → Bool
eq-vcvtop---fam22-fun (vcvtop---CONVERT x0 x1) (vcvtop---CONVERT y0 y1) = (x0 =? y0) ∧ (x1 =? y1)
instance
  haseq-vcvtop---fam22 : {M-1 : M} → {M-2 : M} → HasEq (vcvtop---fam22 M-1 M-2)
  haseq-vcvtop---fam22 = record { _=?_ = eq-vcvtop---fam22-fun }

data vcvtop---fam23 (M-1 : M) (M-2 : M) : Set where
  vcvtop---CONVERT : (half-opt-447 : (Maybe half)) → (sx-51607 : sx) → vcvtop---fam23 M-1 M-2 {- 1 premise(s) dropped -}

eq-vcvtop---fam23-fun : {M-1 : M} → {M-2 : M} → (vcvtop---fam23 M-1 M-2) → (vcvtop---fam23 M-1 M-2) → Bool
eq-vcvtop---fam23-fun (vcvtop---CONVERT x0 x1) (vcvtop---CONVERT y0 y1) = (x0 =? y0) ∧ (x1 =? y1)
instance
  haseq-vcvtop---fam23 : {M-1 : M} → {M-2 : M} → HasEq (vcvtop---fam23 M-1 M-2)
  haseq-vcvtop---fam23 = record { _=?_ = eq-vcvtop---fam23-fun }

data vcvtop---fam24 (M-1 : M) (M-2 : M) : Set where
  vcvtop---TRUNC-SAT : (sx-51608 : sx) → (zero-opt-1757 : (Maybe zero')) → vcvtop---fam24 M-1 M-2 {- 1 premise(s) dropped -}
  RELAXED-TRUNC : (sx-51609 : sx) → (zero-opt-1758 : (Maybe zero')) → vcvtop---fam24 M-1 M-2 {- 1 premise(s) dropped -}

eq-vcvtop---fam24-fun : {M-1 : M} → {M-2 : M} → (vcvtop---fam24 M-1 M-2) → (vcvtop---fam24 M-1 M-2) → Bool
eq-vcvtop---fam24-fun (vcvtop---TRUNC-SAT x0 x1) (vcvtop---TRUNC-SAT y0 y1) = (x0 =? y0) ∧ (x1 =? y1)
eq-vcvtop---fam24-fun (RELAXED-TRUNC x0 x1) (RELAXED-TRUNC y0 y1) = (x0 =? y0) ∧ (x1 =? y1)
eq-vcvtop---fam24-fun _ _ = false
instance
  haseq-vcvtop---fam24 : {M-1 : M} → {M-2 : M} → HasEq (vcvtop---fam24 M-1 M-2)
  haseq-vcvtop---fam24 = record { _=?_ = eq-vcvtop---fam24-fun }

data vcvtop---fam25 (M-1 : M) (M-2 : M) : Set where
  vcvtop---TRUNC-SAT : (sx-51610 : sx) → (zero-opt-1759 : (Maybe zero')) → vcvtop---fam25 M-1 M-2 {- 1 premise(s) dropped -}
  RELAXED-TRUNC : (sx-51611 : sx) → (zero-opt-1760 : (Maybe zero')) → vcvtop---fam25 M-1 M-2 {- 1 premise(s) dropped -}

eq-vcvtop---fam25-fun : {M-1 : M} → {M-2 : M} → (vcvtop---fam25 M-1 M-2) → (vcvtop---fam25 M-1 M-2) → Bool
eq-vcvtop---fam25-fun (vcvtop---TRUNC-SAT x0 x1) (vcvtop---TRUNC-SAT y0 y1) = (x0 =? y0) ∧ (x1 =? y1)
eq-vcvtop---fam25-fun (RELAXED-TRUNC x0 x1) (RELAXED-TRUNC y0 y1) = (x0 =? y0) ∧ (x1 =? y1)
eq-vcvtop---fam25-fun _ _ = false
instance
  haseq-vcvtop---fam25 : {M-1 : M} → {M-2 : M} → HasEq (vcvtop---fam25 M-1 M-2)
  haseq-vcvtop---fam25 = record { _=?_ = eq-vcvtop---fam25-fun }

data vcvtop---fam26 (M-1 : M) (M-2 : M) : Set where
  vcvtop---TRUNC-SAT : (sx-51612 : sx) → (zero-opt-1761 : (Maybe zero')) → vcvtop---fam26 M-1 M-2 {- 1 premise(s) dropped -}
  RELAXED-TRUNC : (sx-51613 : sx) → (zero-opt-1762 : (Maybe zero')) → vcvtop---fam26 M-1 M-2 {- 1 premise(s) dropped -}

eq-vcvtop---fam26-fun : {M-1 : M} → {M-2 : M} → (vcvtop---fam26 M-1 M-2) → (vcvtop---fam26 M-1 M-2) → Bool
eq-vcvtop---fam26-fun (vcvtop---TRUNC-SAT x0 x1) (vcvtop---TRUNC-SAT y0 y1) = (x0 =? y0) ∧ (x1 =? y1)
eq-vcvtop---fam26-fun (RELAXED-TRUNC x0 x1) (RELAXED-TRUNC y0 y1) = (x0 =? y0) ∧ (x1 =? y1)
eq-vcvtop---fam26-fun _ _ = false
instance
  haseq-vcvtop---fam26 : {M-1 : M} → {M-2 : M} → HasEq (vcvtop---fam26 M-1 M-2)
  haseq-vcvtop---fam26 = record { _=?_ = eq-vcvtop---fam26-fun }

data vcvtop---fam27 (M-1 : M) (M-2 : M) : Set where
  vcvtop---TRUNC-SAT : (sx-51614 : sx) → (zero-opt-1763 : (Maybe zero')) → vcvtop---fam27 M-1 M-2 {- 1 premise(s) dropped -}
  RELAXED-TRUNC : (sx-51615 : sx) → (zero-opt-1764 : (Maybe zero')) → vcvtop---fam27 M-1 M-2 {- 1 premise(s) dropped -}

eq-vcvtop---fam27-fun : {M-1 : M} → {M-2 : M} → (vcvtop---fam27 M-1 M-2) → (vcvtop---fam27 M-1 M-2) → Bool
eq-vcvtop---fam27-fun (vcvtop---TRUNC-SAT x0 x1) (vcvtop---TRUNC-SAT y0 y1) = (x0 =? y0) ∧ (x1 =? y1)
eq-vcvtop---fam27-fun (RELAXED-TRUNC x0 x1) (RELAXED-TRUNC y0 y1) = (x0 =? y0) ∧ (x1 =? y1)
eq-vcvtop---fam27-fun _ _ = false
instance
  haseq-vcvtop---fam27 : {M-1 : M} → {M-2 : M} → HasEq (vcvtop---fam27 M-1 M-2)
  haseq-vcvtop---fam27 = record { _=?_ = eq-vcvtop---fam27-fun }

data vcvtop---fam28 (M-1 : M) (M-2 : M) : Set where
  vcvtop---TRUNC-SAT : (sx-51616 : sx) → (zero-opt-1765 : (Maybe zero')) → vcvtop---fam28 M-1 M-2 {- 1 premise(s) dropped -}
  RELAXED-TRUNC : (sx-51617 : sx) → (zero-opt-1766 : (Maybe zero')) → vcvtop---fam28 M-1 M-2 {- 1 premise(s) dropped -}

eq-vcvtop---fam28-fun : {M-1 : M} → {M-2 : M} → (vcvtop---fam28 M-1 M-2) → (vcvtop---fam28 M-1 M-2) → Bool
eq-vcvtop---fam28-fun (vcvtop---TRUNC-SAT x0 x1) (vcvtop---TRUNC-SAT y0 y1) = (x0 =? y0) ∧ (x1 =? y1)
eq-vcvtop---fam28-fun (RELAXED-TRUNC x0 x1) (RELAXED-TRUNC y0 y1) = (x0 =? y0) ∧ (x1 =? y1)
eq-vcvtop---fam28-fun _ _ = false
instance
  haseq-vcvtop---fam28 : {M-1 : M} → {M-2 : M} → HasEq (vcvtop---fam28 M-1 M-2)
  haseq-vcvtop---fam28 = record { _=?_ = eq-vcvtop---fam28-fun }

data vcvtop---fam29 (M-1 : M) (M-2 : M) : Set where
  vcvtop---TRUNC-SAT : (sx-51618 : sx) → (zero-opt-1767 : (Maybe zero')) → vcvtop---fam29 M-1 M-2 {- 1 premise(s) dropped -}
  RELAXED-TRUNC : (sx-51619 : sx) → (zero-opt-1768 : (Maybe zero')) → vcvtop---fam29 M-1 M-2 {- 1 premise(s) dropped -}

eq-vcvtop---fam29-fun : {M-1 : M} → {M-2 : M} → (vcvtop---fam29 M-1 M-2) → (vcvtop---fam29 M-1 M-2) → Bool
eq-vcvtop---fam29-fun (vcvtop---TRUNC-SAT x0 x1) (vcvtop---TRUNC-SAT y0 y1) = (x0 =? y0) ∧ (x1 =? y1)
eq-vcvtop---fam29-fun (RELAXED-TRUNC x0 x1) (RELAXED-TRUNC y0 y1) = (x0 =? y0) ∧ (x1 =? y1)
eq-vcvtop---fam29-fun _ _ = false
instance
  haseq-vcvtop---fam29 : {M-1 : M} → {M-2 : M} → HasEq (vcvtop---fam29 M-1 M-2)
  haseq-vcvtop---fam29 = record { _=?_ = eq-vcvtop---fam29-fun }

data vcvtop---fam30 (M-1 : M) (M-2 : M) : Set where
  vcvtop---TRUNC-SAT : (sx-51620 : sx) → (zero-opt-1769 : (Maybe zero')) → vcvtop---fam30 M-1 M-2 {- 1 premise(s) dropped -}
  RELAXED-TRUNC : (sx-51621 : sx) → (zero-opt-1770 : (Maybe zero')) → vcvtop---fam30 M-1 M-2 {- 1 premise(s) dropped -}

eq-vcvtop---fam30-fun : {M-1 : M} → {M-2 : M} → (vcvtop---fam30 M-1 M-2) → (vcvtop---fam30 M-1 M-2) → Bool
eq-vcvtop---fam30-fun (vcvtop---TRUNC-SAT x0 x1) (vcvtop---TRUNC-SAT y0 y1) = (x0 =? y0) ∧ (x1 =? y1)
eq-vcvtop---fam30-fun (RELAXED-TRUNC x0 x1) (RELAXED-TRUNC y0 y1) = (x0 =? y0) ∧ (x1 =? y1)
eq-vcvtop---fam30-fun _ _ = false
instance
  haseq-vcvtop---fam30 : {M-1 : M} → {M-2 : M} → HasEq (vcvtop---fam30 M-1 M-2)
  haseq-vcvtop---fam30 = record { _=?_ = eq-vcvtop---fam30-fun }

data vcvtop---fam31 (M-1 : M) (M-2 : M) : Set where
  vcvtop---TRUNC-SAT : (sx-51622 : sx) → (zero-opt-1771 : (Maybe zero')) → vcvtop---fam31 M-1 M-2 {- 1 premise(s) dropped -}
  RELAXED-TRUNC : (sx-51623 : sx) → (zero-opt-1772 : (Maybe zero')) → vcvtop---fam31 M-1 M-2 {- 1 premise(s) dropped -}

eq-vcvtop---fam31-fun : {M-1 : M} → {M-2 : M} → (vcvtop---fam31 M-1 M-2) → (vcvtop---fam31 M-1 M-2) → Bool
eq-vcvtop---fam31-fun (vcvtop---TRUNC-SAT x0 x1) (vcvtop---TRUNC-SAT y0 y1) = (x0 =? y0) ∧ (x1 =? y1)
eq-vcvtop---fam31-fun (RELAXED-TRUNC x0 x1) (RELAXED-TRUNC y0 y1) = (x0 =? y0) ∧ (x1 =? y1)
eq-vcvtop---fam31-fun _ _ = false
instance
  haseq-vcvtop---fam31 : {M-1 : M} → {M-2 : M} → HasEq (vcvtop---fam31 M-1 M-2)
  haseq-vcvtop---fam31 = record { _=?_ = eq-vcvtop---fam31-fun }

data vcvtop---fam32 (M-1 : M) (M-2 : M) : Set where
  vcvtop---DEMOTE : (zero-3895 : zero') → vcvtop---fam32 M-1 M-2 {- 1 premise(s) dropped -}
  PROMOTELOW : vcvtop---fam32 M-1 M-2 {- 1 premise(s) dropped -}

eq-vcvtop---fam32-fun : {M-1 : M} → {M-2 : M} → (vcvtop---fam32 M-1 M-2) → (vcvtop---fam32 M-1 M-2) → Bool
eq-vcvtop---fam32-fun (vcvtop---DEMOTE x0) (vcvtop---DEMOTE y0) = (x0 =? y0)
eq-vcvtop---fam32-fun PROMOTELOW PROMOTELOW = true
eq-vcvtop---fam32-fun _ _ = false
instance
  haseq-vcvtop---fam32 : {M-1 : M} → {M-2 : M} → HasEq (vcvtop---fam32 M-1 M-2)
  haseq-vcvtop---fam32 = record { _=?_ = eq-vcvtop---fam32-fun }

data vcvtop---fam33 (M-1 : M) (M-2 : M) : Set where
  vcvtop---DEMOTE : (zero-3896 : zero') → vcvtop---fam33 M-1 M-2 {- 1 premise(s) dropped -}
  PROMOTELOW : vcvtop---fam33 M-1 M-2 {- 1 premise(s) dropped -}

eq-vcvtop---fam33-fun : {M-1 : M} → {M-2 : M} → (vcvtop---fam33 M-1 M-2) → (vcvtop---fam33 M-1 M-2) → Bool
eq-vcvtop---fam33-fun (vcvtop---DEMOTE x0) (vcvtop---DEMOTE y0) = (x0 =? y0)
eq-vcvtop---fam33-fun PROMOTELOW PROMOTELOW = true
eq-vcvtop---fam33-fun _ _ = false
instance
  haseq-vcvtop---fam33 : {M-1 : M} → {M-2 : M} → HasEq (vcvtop---fam33 M-1 M-2)
  haseq-vcvtop---fam33 = record { _=?_ = eq-vcvtop---fam33-fun }

data vcvtop---fam34 (M-1 : M) (M-2 : M) : Set where
  vcvtop---DEMOTE : (zero-3897 : zero') → vcvtop---fam34 M-1 M-2 {- 1 premise(s) dropped -}
  PROMOTELOW : vcvtop---fam34 M-1 M-2 {- 1 premise(s) dropped -}

eq-vcvtop---fam34-fun : {M-1 : M} → {M-2 : M} → (vcvtop---fam34 M-1 M-2) → (vcvtop---fam34 M-1 M-2) → Bool
eq-vcvtop---fam34-fun (vcvtop---DEMOTE x0) (vcvtop---DEMOTE y0) = (x0 =? y0)
eq-vcvtop---fam34-fun PROMOTELOW PROMOTELOW = true
eq-vcvtop---fam34-fun _ _ = false
instance
  haseq-vcvtop---fam34 : {M-1 : M} → {M-2 : M} → HasEq (vcvtop---fam34 M-1 M-2)
  haseq-vcvtop---fam34 = record { _=?_ = eq-vcvtop---fam34-fun }

data vcvtop---fam35 (M-1 : M) (M-2 : M) : Set where
  vcvtop---DEMOTE : (zero-3898 : zero') → vcvtop---fam35 M-1 M-2 {- 1 premise(s) dropped -}
  PROMOTELOW : vcvtop---fam35 M-1 M-2 {- 1 premise(s) dropped -}

eq-vcvtop---fam35-fun : {M-1 : M} → {M-2 : M} → (vcvtop---fam35 M-1 M-2) → (vcvtop---fam35 M-1 M-2) → Bool
eq-vcvtop---fam35-fun (vcvtop---DEMOTE x0) (vcvtop---DEMOTE y0) = (x0 =? y0)
eq-vcvtop---fam35-fun PROMOTELOW PROMOTELOW = true
eq-vcvtop---fam35-fun _ _ = false
instance
  haseq-vcvtop---fam35 : {M-1 : M} → {M-2 : M} → HasEq (vcvtop---fam35 M-1 M-2)
  haseq-vcvtop---fam35 = record { _=?_ = eq-vcvtop---fam35-fun }

vcvtop-- : (shape-1 : shape) (shape-2 : shape) → Set
vcvtop-- (X lanetype-I32 (mk-dim M-1)) (X lanetype-I32 (mk-dim M-2)) = vcvtop---fam0 M-1 M-2
vcvtop-- (X lanetype-I64 (mk-dim M-1)) (X lanetype-I32 (mk-dim M-2)) = vcvtop---fam1 M-1 M-2
vcvtop-- (X lanetype-I8 (mk-dim M-1)) (X lanetype-I32 (mk-dim M-2)) = vcvtop---fam2 M-1 M-2
vcvtop-- (X lanetype-I16 (mk-dim M-1)) (X lanetype-I32 (mk-dim M-2)) = vcvtop---fam3 M-1 M-2
vcvtop-- (X lanetype-I32 (mk-dim M-1)) (X lanetype-I64 (mk-dim M-2)) = vcvtop---fam4 M-1 M-2
vcvtop-- (X lanetype-I64 (mk-dim M-1)) (X lanetype-I64 (mk-dim M-2)) = vcvtop---fam5 M-1 M-2
vcvtop-- (X lanetype-I8 (mk-dim M-1)) (X lanetype-I64 (mk-dim M-2)) = vcvtop---fam6 M-1 M-2
vcvtop-- (X lanetype-I16 (mk-dim M-1)) (X lanetype-I64 (mk-dim M-2)) = vcvtop---fam7 M-1 M-2
vcvtop-- (X lanetype-I32 (mk-dim M-1)) (X lanetype-I8 (mk-dim M-2)) = vcvtop---fam8 M-1 M-2
vcvtop-- (X lanetype-I64 (mk-dim M-1)) (X lanetype-I8 (mk-dim M-2)) = vcvtop---fam9 M-1 M-2
vcvtop-- (X lanetype-I8 (mk-dim M-1)) (X lanetype-I8 (mk-dim M-2)) = vcvtop---fam10 M-1 M-2
vcvtop-- (X lanetype-I16 (mk-dim M-1)) (X lanetype-I8 (mk-dim M-2)) = vcvtop---fam11 M-1 M-2
vcvtop-- (X lanetype-I32 (mk-dim M-1)) (X lanetype-I16 (mk-dim M-2)) = vcvtop---fam12 M-1 M-2
vcvtop-- (X lanetype-I64 (mk-dim M-1)) (X lanetype-I16 (mk-dim M-2)) = vcvtop---fam13 M-1 M-2
vcvtop-- (X lanetype-I8 (mk-dim M-1)) (X lanetype-I16 (mk-dim M-2)) = vcvtop---fam14 M-1 M-2
vcvtop-- (X lanetype-I16 (mk-dim M-1)) (X lanetype-I16 (mk-dim M-2)) = vcvtop---fam15 M-1 M-2
vcvtop-- (X lanetype-I32 (mk-dim M-1)) (X lanetype-F32 (mk-dim M-2)) = vcvtop---fam16 M-1 M-2
vcvtop-- (X lanetype-I64 (mk-dim M-1)) (X lanetype-F32 (mk-dim M-2)) = vcvtop---fam17 M-1 M-2
vcvtop-- (X lanetype-I8 (mk-dim M-1)) (X lanetype-F32 (mk-dim M-2)) = vcvtop---fam18 M-1 M-2
vcvtop-- (X lanetype-I16 (mk-dim M-1)) (X lanetype-F32 (mk-dim M-2)) = vcvtop---fam19 M-1 M-2
vcvtop-- (X lanetype-I32 (mk-dim M-1)) (X lanetype-F64 (mk-dim M-2)) = vcvtop---fam20 M-1 M-2
vcvtop-- (X lanetype-I64 (mk-dim M-1)) (X lanetype-F64 (mk-dim M-2)) = vcvtop---fam21 M-1 M-2
vcvtop-- (X lanetype-I8 (mk-dim M-1)) (X lanetype-F64 (mk-dim M-2)) = vcvtop---fam22 M-1 M-2
vcvtop-- (X lanetype-I16 (mk-dim M-1)) (X lanetype-F64 (mk-dim M-2)) = vcvtop---fam23 M-1 M-2
vcvtop-- (X lanetype-F32 (mk-dim M-1)) (X lanetype-I32 (mk-dim M-2)) = vcvtop---fam24 M-1 M-2
vcvtop-- (X lanetype-F64 (mk-dim M-1)) (X lanetype-I32 (mk-dim M-2)) = vcvtop---fam25 M-1 M-2
vcvtop-- (X lanetype-F32 (mk-dim M-1)) (X lanetype-I64 (mk-dim M-2)) = vcvtop---fam26 M-1 M-2
vcvtop-- (X lanetype-F64 (mk-dim M-1)) (X lanetype-I64 (mk-dim M-2)) = vcvtop---fam27 M-1 M-2
vcvtop-- (X lanetype-F32 (mk-dim M-1)) (X lanetype-I8 (mk-dim M-2)) = vcvtop---fam28 M-1 M-2
vcvtop-- (X lanetype-F64 (mk-dim M-1)) (X lanetype-I8 (mk-dim M-2)) = vcvtop---fam29 M-1 M-2
vcvtop-- (X lanetype-F32 (mk-dim M-1)) (X lanetype-I16 (mk-dim M-2)) = vcvtop---fam30 M-1 M-2
vcvtop-- (X lanetype-F64 (mk-dim M-1)) (X lanetype-I16 (mk-dim M-2)) = vcvtop---fam31 M-1 M-2
vcvtop-- (X lanetype-F32 (mk-dim M-1)) (X lanetype-F32 (mk-dim M-2)) = vcvtop---fam32 M-1 M-2
vcvtop-- (X lanetype-F64 (mk-dim M-1)) (X lanetype-F32 (mk-dim M-2)) = vcvtop---fam33 M-1 M-2
vcvtop-- (X lanetype-F32 (mk-dim M-1)) (X lanetype-F64 (mk-dim M-2)) = vcvtop---fam34 M-1 M-2
vcvtop-- (X lanetype-F64 (mk-dim M-1)) (X lanetype-F64 (mk-dim M-2)) = vcvtop---fam35 M-1 M-2
vcvtop-- _ _ = ⊤

{- Record Creation Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:189.1-189.69 -}
record memarg : Set where
  constructor mk-memarg
  field
    ALIGN : u32
    OFFSET : u64
open memarg

instance
  append-memarg : HasAppend (memarg)
  append-memarg = record { append = λ arg1 arg2 → record {
    ALIGN = ALIGN arg1 {- FIXME - Non-trivial append -} ;
    OFFSET = OFFSET arg1 {- FIXME - Non-trivial append -} } }

eq-memarg-fun : memarg → memarg → Bool
eq-memarg-fun r1 r2 = ((ALIGN r1) =? (ALIGN r2)) ∧ ((OFFSET r1) =? (OFFSET r2))
instance
  haseq-memarg : HasEq memarg
  haseq-memarg = record { _=?_ = eq-memarg-fun }

{- Type Family Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:193.1-193.24 -}
data loadop--fam0 : Set where
  mk-loadop- : (sz-4992 : sz) → (sx-51624 : sx) → loadop--fam0 {- 1 premise(s) dropped -}

eq-loadop--fam0-fun : loadop--fam0 → loadop--fam0 → Bool
eq-loadop--fam0-fun (mk-loadop- x0 x1) (mk-loadop- y0 y1) = (x0 =? y0) ∧ (x1 =? y1)
instance
  haseq-loadop--fam0 : HasEq loadop--fam0
  haseq-loadop--fam0 = record { _=?_ = eq-loadop--fam0-fun }

data loadop--fam1 : Set where
  mk-loadop- : (sz-4993 : sz) → (sx-51625 : sx) → loadop--fam1 {- 1 premise(s) dropped -}

eq-loadop--fam1-fun : loadop--fam1 → loadop--fam1 → Bool
eq-loadop--fam1-fun (mk-loadop- x0 x1) (mk-loadop- y0 y1) = (x0 =? y0) ∧ (x1 =? y1)
instance
  haseq-loadop--fam1 : HasEq loadop--fam1
  haseq-loadop--fam1 = record { _=?_ = eq-loadop--fam1-fun }

loadop- : (v-numtype : numtype) → Set
loadop- numtype-I32 = loadop--fam0
loadop- numtype-I64 = loadop--fam1
loadop- _ = ⊤

{- Type Family Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:196.1-196.25 -}
data storeop--fam0 : Set where
  mk-storeop- : (sz-4994 : sz) → storeop--fam0 {- 1 premise(s) dropped -}

eq-storeop--fam0-fun : storeop--fam0 → storeop--fam0 → Bool
eq-storeop--fam0-fun (mk-storeop- x0) (mk-storeop- y0) = (x0 =? y0)
instance
  haseq-storeop--fam0 : HasEq storeop--fam0
  haseq-storeop--fam0 = record { _=?_ = eq-storeop--fam0-fun }

data storeop--fam1 : Set where
  mk-storeop- : (sz-4995 : sz) → storeop--fam1 {- 1 premise(s) dropped -}

eq-storeop--fam1-fun : storeop--fam1 → storeop--fam1 → Bool
eq-storeop--fam1-fun (mk-storeop- x0) (mk-storeop- y0) = (x0 =? y0)
instance
  haseq-storeop--fam1 : HasEq storeop--fam1
  haseq-storeop--fam1 = record { _=?_ = eq-storeop--fam1-fun }

storeop- : (v-numtype : numtype) → Set
storeop- numtype-I32 = storeop--fam0
storeop- numtype-I64 = storeop--fam1
storeop- _ = ⊤

{- Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:199.1-202.59 -}
data vloadop--fam0 (v-vectype : vectype) : Set where
  SHAPEX- : (v-sz : sz) → (v-M : M) → (v-sx : sx) → vloadop--fam0 v-vectype {- 1 premise(s) dropped -}
  SPLAT : (v-sz : sz) → vloadop--fam0 v-vectype
  vloadop--ZERO : (v-sz : sz) → vloadop--fam0 v-vectype {- 1 premise(s) dropped -}

eq-vloadop--fam0-fun : {v-vectype : vectype} → (vloadop--fam0 v-vectype) → (vloadop--fam0 v-vectype) → Bool
eq-vloadop--fam0-fun (SHAPEX- x0 x1 x2) (SHAPEX- y0 y1 y2) = (x0 =? y0) ∧ (x1 =? y1) ∧ (x2 =? y2)
eq-vloadop--fam0-fun (SPLAT x0) (SPLAT y0) = (x0 =? y0)
eq-vloadop--fam0-fun (vloadop--ZERO x0) (vloadop--ZERO y0) = (x0 =? y0)
eq-vloadop--fam0-fun _ _ = false
instance
  haseq-vloadop--fam0 : {v-vectype : vectype} → HasEq (vloadop--fam0 v-vectype)
  haseq-vloadop--fam0 = record { _=?_ = eq-vloadop--fam0-fun }

vloadop- : (v-vectype : vectype) → Set
vloadop- v-vectype = vloadop--fam0 v-vectype
vloadop- _ = ⊤

{- Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:207.1-209.17 -}
data blocktype : Set where
  -RESULT : (valtype-opt : (Maybe valtype)) → blocktype
  blocktype--IDX : (v-typeidx : typeidx) → blocktype

eq-blocktype-fun : blocktype → blocktype → Bool
eq-blocktype-fun (-RESULT x0) (-RESULT y0) = (x0 =? y0)
eq-blocktype-fun (blocktype--IDX x0) (blocktype--IDX y0) = (x0 =? y0)
eq-blocktype-fun _ _ = false
instance
  haseq-blocktype : HasEq blocktype
  haseq-blocktype = record { _=?_ = eq-blocktype-fun }

{- Type Alias Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:7.1-7.39 -}
addr : Set
addr = ℕ

{- Type Alias Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:16.1-16.51 -}
arrayaddr : Set
arrayaddr = addr

{- Inductive Type Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:257.1-261.27 -}
data catch : Set where
  CATCH : (v-tagidx : tagidx) → (v-labelidx : labelidx) → catch
  CATCH-REF : (v-tagidx : tagidx) → (v-labelidx : labelidx) → catch
  CATCH-ALL : (v-labelidx : labelidx) → catch
  CATCH-ALL-REF : (v-labelidx : labelidx) → catch

eq-catch-fun : catch → catch → Bool
eq-catch-fun (CATCH x0 x1) (CATCH y0 y1) = (x0 =? y0) ∧ (x1 =? y1)
eq-catch-fun (CATCH-REF x0 x1) (CATCH-REF y0 y1) = (x0 =? y0) ∧ (x1 =? y1)
eq-catch-fun (CATCH-ALL x0) (CATCH-ALL y0) = (x0 =? y0)
eq-catch-fun (CATCH-ALL-REF x0) (CATCH-ALL-REF y0) = (x0 =? y0)
eq-catch-fun _ _ = false
instance
  haseq-catch : HasEq catch
  haseq-catch = record { _=?_ = eq-catch-fun }

{- Type Alias Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:17.1-17.53 -}
exnaddr : Set
exnaddr = addr

{- Type Alias Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:13.1-13.49 -}
dataaddr : Set
dataaddr = addr

{- Type Alias Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:14.1-14.49 -}
elemaddr : Set
elemaddr = addr

{- Type Alias Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:12.1-12.53 -}
funcaddr : Set
funcaddr = addr

{- Type Alias Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:9.1-9.53 -}
globaladdr : Set
globaladdr = addr

{- Type Alias Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:10.1-10.50 -}
memaddr : Set
memaddr = addr

{- Type Alias Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:11.1-11.51 -}
tableaddr : Set
tableaddr = addr

{- Type Alias Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:8.1-8.47 -}
tagaddr : Set
tagaddr = addr

{- Inductive Type Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:20.1-21.84 -}
data externaddr : Set where
  externaddr-TAG : (v-tagaddr : tagaddr) → externaddr
  externaddr-GLOBAL : (v-globaladdr : globaladdr) → externaddr
  externaddr-MEM : (v-memaddr : memaddr) → externaddr
  externaddr-TABLE : (v-tableaddr : tableaddr) → externaddr
  externaddr-FUNC : (v-funcaddr : funcaddr) → externaddr

instance
  inh-externaddr : Inhabited externaddr
  inh-externaddr = record { default-val = (externaddr-TAG (default-val)) }

eq-externaddr-fun : externaddr → externaddr → Bool
eq-externaddr-fun (externaddr-TAG x0) (externaddr-TAG y0) = (x0 =? y0)
eq-externaddr-fun (externaddr-GLOBAL x0) (externaddr-GLOBAL y0) = (x0 =? y0)
eq-externaddr-fun (externaddr-MEM x0) (externaddr-MEM y0) = (x0 =? y0)
eq-externaddr-fun (externaddr-TABLE x0) (externaddr-TABLE y0) = (x0 =? y0)
eq-externaddr-fun (externaddr-FUNC x0) (externaddr-FUNC y0) = (x0 =? y0)
eq-externaddr-fun _ _ = false
instance
  haseq-externaddr : HasEq externaddr
  haseq-externaddr = record { _=?_ = eq-externaddr-fun }

{- Record Creation Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:81.1-82.33 -}
record exportinst : Set where
  constructor mk-exportinst
  field
    NAME : name
    ADDR : externaddr
open exportinst

instance
  append-exportinst : HasAppend (exportinst)
  append-exportinst = record { append = λ arg1 arg2 → record {
    NAME = NAME arg1 {- FIXME - Non-trivial append -} ;
    ADDR = ADDR arg1 {- FIXME - Non-trivial append -} } }

instance
  inh-exportinst : Inhabited exportinst
  inh-exportinst = record { default-val = record { NAME = default-val ; ADDR = default-val } }

eq-exportinst-fun : exportinst → exportinst → Bool
eq-exportinst-fun r1 r2 = ((NAME r1) =? (NAME r2)) ∧ ((ADDR r1) =? (ADDR r2))
instance
  haseq-exportinst : HasEq exportinst
  haseq-exportinst = record { _=?_ = eq-exportinst-fun }

{- Record Creation Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:101.1-110.26 -}
record moduleinst : Set where
  constructor mk-moduleinst
  field
    moduleinst-TYPES : (List deftype)
    moduleinst-TAGS : (List tagaddr)
    moduleinst-GLOBALS : (List globaladdr)
    moduleinst-MEMS : (List memaddr)
    moduleinst-TABLES : (List tableaddr)
    moduleinst-FUNCS : (List funcaddr)
    moduleinst-DATAS : (List dataaddr)
    moduleinst-ELEMS : (List elemaddr)
    EXPORTS : (List exportinst)
open moduleinst

instance
  append-moduleinst : HasAppend (moduleinst)
  append-moduleinst = record { append = λ arg1 arg2 → record {
    moduleinst-TYPES = moduleinst-TYPES arg1 ⧺ moduleinst-TYPES arg2 ;
    moduleinst-TAGS = moduleinst-TAGS arg1 ⧺ moduleinst-TAGS arg2 ;
    moduleinst-GLOBALS = moduleinst-GLOBALS arg1 ⧺ moduleinst-GLOBALS arg2 ;
    moduleinst-MEMS = moduleinst-MEMS arg1 ⧺ moduleinst-MEMS arg2 ;
    moduleinst-TABLES = moduleinst-TABLES arg1 ⧺ moduleinst-TABLES arg2 ;
    moduleinst-FUNCS = moduleinst-FUNCS arg1 ⧺ moduleinst-FUNCS arg2 ;
    moduleinst-DATAS = moduleinst-DATAS arg1 ⧺ moduleinst-DATAS arg2 ;
    moduleinst-ELEMS = moduleinst-ELEMS arg1 ⧺ moduleinst-ELEMS arg2 ;
    EXPORTS = EXPORTS arg1 ⧺ EXPORTS arg2 } }

instance
  inh-moduleinst : Inhabited moduleinst
  inh-moduleinst = record { default-val = record { moduleinst-TYPES = default-val ; moduleinst-TAGS = default-val ; moduleinst-GLOBALS = default-val ; moduleinst-MEMS = default-val ; moduleinst-TABLES = default-val ; moduleinst-FUNCS = default-val ; moduleinst-DATAS = default-val ; moduleinst-ELEMS = default-val ; EXPORTS = default-val } }

eq-moduleinst-fun : moduleinst → moduleinst → Bool
eq-moduleinst-fun r1 r2 = ((moduleinst-TYPES r1) =? (moduleinst-TYPES r2)) ∧ ((moduleinst-TAGS r1) =? (moduleinst-TAGS r2)) ∧ ((moduleinst-GLOBALS r1) =? (moduleinst-GLOBALS r2)) ∧ ((moduleinst-MEMS r1) =? (moduleinst-MEMS r2)) ∧ ((moduleinst-TABLES r1) =? (moduleinst-TABLES r2)) ∧ ((moduleinst-FUNCS r1) =? (moduleinst-FUNCS r2)) ∧ ((moduleinst-DATAS r1) =? (moduleinst-DATAS r2)) ∧ ((moduleinst-ELEMS r1) =? (moduleinst-ELEMS r2)) ∧ ((EXPORTS r1) =? (EXPORTS r2))
instance
  haseq-moduleinst : HasEq moduleinst
  haseq-moduleinst = record { _=?_ = eq-moduleinst-fun }

{- Type Alias Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:18.1-18.49 -}
hostaddr : Set
hostaddr = addr

{- Type Alias Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:15.1-15.56 -}
structaddr : Set
structaddr = addr

{- Inductive Type Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:35.1-43.19 -}
data ref : Set where
  REF-I31-NUM : (v-u31 : u31) → ref
  REF-NULL-ADDR : ref
  REF-STRUCT-ADDR : (v-structaddr : structaddr) → ref
  REF-ARRAY-ADDR : (v-arrayaddr : arrayaddr) → ref
  REF-FUNC-ADDR : (v-funcaddr : funcaddr) → ref
  REF-EXN-ADDR : (v-exnaddr : exnaddr) → ref
  REF-HOST-ADDR : (v-hostaddr : hostaddr) → ref
  REF-EXTERN : (v-ref : ref) → ref

instance
  inh-ref : Inhabited ref
  inh-ref = record { default-val = (REF-I31-NUM (default-val)) }

eq-ref-fun : ref → ref → Bool
eq-ref-fun (REF-I31-NUM x0) (REF-I31-NUM y0) = (x0 =? y0)
eq-ref-fun REF-NULL-ADDR REF-NULL-ADDR = true
eq-ref-fun (REF-STRUCT-ADDR x0) (REF-STRUCT-ADDR y0) = (x0 =? y0)
eq-ref-fun (REF-ARRAY-ADDR x0) (REF-ARRAY-ADDR y0) = (x0 =? y0)
eq-ref-fun (REF-FUNC-ADDR x0) (REF-FUNC-ADDR y0) = (x0 =? y0)
eq-ref-fun (REF-EXN-ADDR x0) (REF-EXN-ADDR y0) = (x0 =? y0)
eq-ref-fun (REF-HOST-ADDR x0) (REF-HOST-ADDR y0) = (x0 =? y0)
eq-ref-fun (REF-EXTERN x0) (REF-EXTERN y0) = (eq-ref-fun x0 y0)
eq-ref-fun _ _ = false
instance
  haseq-ref : HasEq ref
  haseq-ref = record { _=?_ = eq-ref-fun }

{- Inductive Type Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:45.1-46.20 -}
data val : Set where
  CONST : (v-numtype : numtype) → (_ : (num- v-numtype)) → val
  VCONST : (v-vectype : vectype) → (_ : (uN-fam0 ((vsize v-vectype)))) → val
  val-REF-I31-NUM : (v-u31 : u31) → val
  val-REF-NULL-ADDR : val
  val-REF-STRUCT-ADDR : (v-structaddr : structaddr) → val
  val-REF-ARRAY-ADDR : (v-arrayaddr : arrayaddr) → val
  val-REF-FUNC-ADDR : (v-funcaddr : funcaddr) → val
  val-REF-EXN-ADDR : (v-exnaddr : exnaddr) → val
  val-REF-HOST-ADDR : (v-hostaddr : hostaddr) → val
  val-REF-EXTERN : (v-ref : ref) → val

instance
  inh-val : Inhabited val
  inh-val = record { default-val = (let v-numtype = default-val in CONST v-numtype ((Inhabited.default-val (inh-num--fun v-numtype)))) }

{- Auxiliary Definition at:  -}
{-# TERMINATING #-}
val-ref : (var-0 : ref) → val
val-ref (REF-I31-NUM x0) = (val-REF-I31-NUM x0)
val-ref REF-NULL-ADDR = val-REF-NULL-ADDR
val-ref (REF-STRUCT-ADDR x0) = (val-REF-STRUCT-ADDR x0)
val-ref (REF-ARRAY-ADDR x0) = (val-REF-ARRAY-ADDR x0)
val-ref (REF-FUNC-ADDR x0) = (val-REF-FUNC-ADDR x0)
val-ref (REF-EXN-ADDR x0) = (val-REF-EXN-ADDR x0)
val-ref (REF-HOST-ADDR x0) = (val-REF-HOST-ADDR x0)
val-ref (REF-EXTERN x0) = (val-REF-EXTERN x0)
val-ref var-0 = default-val

{- Record Creation Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:127.1-128.40 -}
record frame : Set where
  constructor mk-frame
  field
    frame-LOCALS : (List (Maybe val))
    MODULE : moduleinst
open frame

instance
  append-frame : HasAppend (frame)
  append-frame = record { append = λ arg1 arg2 → record {
    frame-LOCALS = frame-LOCALS arg1 ⧺ frame-LOCALS arg2 ;
    MODULE = MODULE arg1 ⧺ MODULE arg2 } }

instance
  inh-frame : Inhabited frame
  inh-frame = record { default-val = record { frame-LOCALS = default-val ; MODULE = default-val } }

{- Inductive Type Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:133.1-139.9 -}
data instr : Set where
  NOP : instr
  UNREACHABLE : instr
  DROP : instr
  SELECT : (valtype-lst-opt : (Maybe (List valtype))) → instr
  BLOCK : (v-blocktype : blocktype) → (instr-lst : (List instr)) → instr
  LOOP : (v-blocktype : blocktype) → (instr-lst : (List instr)) → instr
  IFELSE : (v-blocktype : blocktype) → (instr-lst : (List instr)) → (instr-lst : (List instr)) → instr
  BR : (v-labelidx : labelidx) → instr
  BR-IF : (v-labelidx : labelidx) → instr
  BR-TABLE : (labelidx-lst : (List labelidx)) → (v-labelidx : labelidx) → instr
  BR-ON-NULL : (v-labelidx : labelidx) → instr
  BR-ON-NON-NULL : (v-labelidx : labelidx) → instr
  BR-ON-CAST : (v-labelidx : labelidx) → (v-reftype : reftype) → (v-reftype : reftype) → instr
  BR-ON-CAST-FAIL : (v-labelidx : labelidx) → (v-reftype : reftype) → (v-reftype : reftype) → instr
  CALL : (v-funcidx : funcidx) → instr
  CALL-REF : (v-typeuse : typeuse) → instr
  CALL-INDIRECT : (v-tableidx : tableidx) → (v-typeuse : typeuse) → instr
  RETURN : instr
  RETURN-CALL : (v-funcidx : funcidx) → instr
  RETURN-CALL-REF : (v-typeuse : typeuse) → instr
  RETURN-CALL-INDIRECT : (v-tableidx : tableidx) → (v-typeuse : typeuse) → instr
  THROW : (v-tagidx : tagidx) → instr
  THROW-REF : instr
  TRY-TABLE : (v-blocktype : blocktype) → (_ : (list-fam0 (catch))) → (instr-lst : (List instr)) → instr
  LOCAL-GET : (v-localidx : localidx) → instr
  LOCAL-SET : (v-localidx : localidx) → instr
  LOCAL-TEE : (v-localidx : localidx) → instr
  GLOBAL-GET : (v-globalidx : globalidx) → instr
  GLOBAL-SET : (v-globalidx : globalidx) → instr
  TABLE-GET : (v-tableidx : tableidx) → instr
  TABLE-SET : (v-tableidx : tableidx) → instr
  TABLE-SIZE : (v-tableidx : tableidx) → instr
  TABLE-GROW : (v-tableidx : tableidx) → instr
  TABLE-FILL : (v-tableidx : tableidx) → instr
  TABLE-COPY : (v-tableidx : tableidx) → (v-tableidx : tableidx) → instr
  TABLE-INIT : (v-tableidx : tableidx) → (v-elemidx : elemidx) → instr
  ELEM-DROP : (v-elemidx : elemidx) → instr
  LOAD : (v-numtype : numtype) → (_ : (Maybe (loadop- v-numtype))) → (v-memidx : memidx) → (v-memarg : memarg) → instr
  STORE : (v-numtype : numtype) → (_ : (Maybe (storeop- v-numtype))) → (v-memidx : memidx) → (v-memarg : memarg) → instr
  VLOAD : (v-vectype : vectype) → (_ : (Maybe (vloadop--fam0 (v-vectype)))) → (v-memidx : memidx) → (v-memarg : memarg) → instr
  VLOAD-LANE : (v-vectype : vectype) → (v-sz : sz) → (v-memidx : memidx) → (v-memarg : memarg) → (v-laneidx : laneidx) → instr
  VSTORE : (v-vectype : vectype) → (v-memidx : memidx) → (v-memarg : memarg) → instr
  VSTORE-LANE : (v-vectype : vectype) → (v-sz : sz) → (v-memidx : memidx) → (v-memarg : memarg) → (v-laneidx : laneidx) → instr
  MEMORY-SIZE : (v-memidx : memidx) → instr
  MEMORY-GROW : (v-memidx : memidx) → instr
  MEMORY-FILL : (v-memidx : memidx) → instr
  MEMORY-COPY : (v-memidx : memidx) → (v-memidx : memidx) → instr
  MEMORY-INIT : (v-memidx : memidx) → (v-dataidx : dataidx) → instr
  DATA-DROP : (v-dataidx : dataidx) → instr
  REF-NULL : (v-heaptype : heaptype) → instr
  REF-IS-NULL : instr
  REF-AS-NON-NULL : instr
  REF-EQ : instr
  REF-TEST : (v-reftype : reftype) → instr
  REF-CAST : (v-reftype : reftype) → instr
  REF-FUNC : (v-funcidx : funcidx) → instr
  REF-I31 : instr
  I31-GET : (v-sx : sx) → instr
  STRUCT-NEW : (v-typeidx : typeidx) → instr
  STRUCT-NEW-DEFAULT : (v-typeidx : typeidx) → instr
  STRUCT-GET : (sx-opt : (Maybe sx)) → (v-typeidx : typeidx) → (v-fieldidx : fieldidx) → instr
  STRUCT-SET : (v-typeidx : typeidx) → (v-fieldidx : fieldidx) → instr
  ARRAY-NEW : (v-typeidx : typeidx) → instr
  ARRAY-NEW-DEFAULT : (v-typeidx : typeidx) → instr
  ARRAY-NEW-FIXED : (v-typeidx : typeidx) → (v-u32 : u32) → instr
  ARRAY-NEW-DATA : (v-typeidx : typeidx) → (v-dataidx : dataidx) → instr
  ARRAY-NEW-ELEM : (v-typeidx : typeidx) → (v-elemidx : elemidx) → instr
  ARRAY-GET : (sx-opt : (Maybe sx)) → (v-typeidx : typeidx) → instr
  ARRAY-SET : (v-typeidx : typeidx) → instr
  ARRAY-LEN : instr
  ARRAY-FILL : (v-typeidx : typeidx) → instr
  ARRAY-COPY : (v-typeidx : typeidx) → (v-typeidx : typeidx) → instr
  ARRAY-INIT-DATA : (v-typeidx : typeidx) → (v-dataidx : dataidx) → instr
  ARRAY-INIT-ELEM : (v-typeidx : typeidx) → (v-elemidx : elemidx) → instr
  EXTERN-CONVERT-ANY : instr
  ANY-CONVERT-EXTERN : instr
  instr-CONST : (v-numtype : numtype) → (_ : (num- v-numtype)) → instr
  UNOP : (v-numtype : numtype) → (_ : (unop- v-numtype)) → instr
  BINOP : (v-numtype : numtype) → (_ : (binop- v-numtype)) → instr
  TESTOP : (v-numtype : numtype) → (_ : (testop- v-numtype)) → instr
  RELOP : (v-numtype : numtype) → (_ : (relop- v-numtype)) → instr
  CVTOP : (numtype-1 : numtype) → (numtype-2 : numtype) → (_ : (cvtop-- numtype-2 numtype-1)) → instr
  instr-VCONST : (v-vectype : vectype) → (_ : (uN-fam0 ((vsize v-vectype)))) → instr
  VVUNOP : (v-vectype : vectype) → (v-vvunop : vvunop) → instr
  VVBINOP : (v-vectype : vectype) → (v-vvbinop : vvbinop) → instr
  VVTERNOP : (v-vectype : vectype) → (v-vvternop : vvternop) → instr
  VVTESTOP : (v-vectype : vectype) → (v-vvtestop : vvtestop) → instr
  VUNOP : (v-shape : shape) → (_ : (vunop- v-shape)) → instr
  VBINOP : (v-shape : shape) → (_ : (vbinop- v-shape)) → instr
  VTERNOP : (v-shape : shape) → (_ : (vternop- v-shape)) → instr
  VTESTOP : (v-shape : shape) → (_ : (vtestop- v-shape)) → instr
  VRELOP : (v-shape : shape) → (_ : (vrelop- v-shape)) → instr
  VSHIFTOP : (v-ishape : ishape) → (_ : (vshiftop- v-ishape)) → instr
  VBITMASK : (v-ishape : ishape) → instr
  VSWIZZLOP : (v-bshape : bshape) → (_ : (vswizzlop- v-bshape)) → instr
  VSHUFFLE : (v-bshape : bshape) → (laneidx-lst : (List laneidx)) → instr {- 1 premise(s) dropped -}
  VEXTUNOP : (ishape-1 : ishape) → (ishape-2 : ishape) → (_ : (vextunop-- ishape-2 ishape-1)) → instr
  VEXTBINOP : (ishape-1 : ishape) → (ishape-2 : ishape) → (_ : (vextbinop-- ishape-2 ishape-1)) → instr
  VEXTTERNOP : (ishape-1 : ishape) → (ishape-2 : ishape) → (_ : (vextternop-- ishape-2 ishape-1)) → instr
  VNARROW : (ishape-1 : ishape) → (ishape-2 : ishape) → (v-sx : sx) → instr {- 1 premise(s) dropped -}
  VCVTOP : (shape-1 : shape) → (shape-2 : shape) → (_ : (vcvtop-- shape-2 shape-1)) → instr
  VSPLAT : (v-shape : shape) → instr
  VEXTRACT-LANE : (v-shape : shape) → (sx-opt : (Maybe sx)) → (v-laneidx : laneidx) → instr {- 1 premise(s) dropped -}
  VREPLACE-LANE : (v-shape : shape) → (v-laneidx : laneidx) → instr
  instr-REF-I31-NUM : (v-u31 : u31) → instr
  instr-REF-NULL-ADDR : instr
  instr-REF-STRUCT-ADDR : (v-structaddr : structaddr) → instr
  instr-REF-ARRAY-ADDR : (v-arrayaddr : arrayaddr) → instr
  instr-REF-FUNC-ADDR : (v-funcaddr : funcaddr) → instr
  instr-REF-EXN-ADDR : (v-exnaddr : exnaddr) → instr
  instr-REF-HOST-ADDR : (v-hostaddr : hostaddr) → instr
  instr-REF-EXTERN : (v-ref : ref) → instr
  LABEL- : (v-n : n) → (instr-lst : (List instr)) → (instr-lst : (List instr)) → instr
  FRAME- : (v-n : n) → (v-frame : frame) → (instr-lst : (List instr)) → instr
  HANDLER- : (v-n : n) → (catch-lst : (List catch)) → (instr-lst : (List instr)) → instr
  TRAP : instr

instance
  inh-instr : Inhabited instr
  inh-instr = record { default-val = NOP }

{- Auxiliary Definition at:  -}
{-# TERMINATING #-}
instr-ref : (var-0 : ref) → instr
instr-ref (REF-I31-NUM x0) = (instr-REF-I31-NUM x0)
instr-ref REF-NULL-ADDR = instr-REF-NULL-ADDR
instr-ref (REF-STRUCT-ADDR x0) = (instr-REF-STRUCT-ADDR x0)
instr-ref (REF-ARRAY-ADDR x0) = (instr-REF-ARRAY-ADDR x0)
instr-ref (REF-FUNC-ADDR x0) = (instr-REF-FUNC-ADDR x0)
instr-ref (REF-EXN-ADDR x0) = (instr-REF-EXN-ADDR x0)
instr-ref (REF-HOST-ADDR x0) = (instr-REF-HOST-ADDR x0)
instr-ref (REF-EXTERN x0) = (instr-REF-EXTERN x0)
instr-ref var-0 = default-val

{- Auxiliary Definition at:  -}
{-# TERMINATING #-}
instr-val : (var-0 : val) → instr
instr-val (CONST x0 x1) = (instr-CONST x0 x1)
instr-val (VCONST x0 x1) = (instr-VCONST x0 x1)
instr-val (val-REF-I31-NUM x0) = (instr-REF-I31-NUM x0)
instr-val val-REF-NULL-ADDR = instr-REF-NULL-ADDR
instr-val (val-REF-STRUCT-ADDR x0) = (instr-REF-STRUCT-ADDR x0)
instr-val (val-REF-ARRAY-ADDR x0) = (instr-REF-ARRAY-ADDR x0)
instr-val (val-REF-FUNC-ADDR x0) = (instr-REF-FUNC-ADDR x0)
instr-val (val-REF-EXN-ADDR x0) = (instr-REF-EXN-ADDR x0)
instr-val (val-REF-HOST-ADDR x0) = (instr-REF-HOST-ADDR x0)
instr-val (val-REF-EXTERN x0) = (instr-REF-EXTERN x0)
instr-val var-0 = default-val

{- Type Alias Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:394.1-395.9 -}
expr : Set
expr = (List instr)

{- Auxiliary Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:406.1-406.35 -}
memarg0 : memarg
memarg0 = record { ALIGN = (mk-uN 0) ; OFFSET = (mk-uN 0) }

{- Auxiliary Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:409.1-409.69 -}
{-# TERMINATING #-}
const : (v-consttype : consttype) (v-lit- : (lit- (storagetype-consttype v-consttype))) → instr
const consttype-I32 c = (instr-CONST numtype-I32 c)
const consttype-I64 c = (instr-CONST numtype-I64 c)
const consttype-F32 c = (instr-CONST F32 c)
const consttype-F64 c = (instr-CONST F64 c)
const consttype-V128 c = (instr-VCONST V128 c)
const v-consttype v-lit- = default-val

{- Auxiliary Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:416.1-416.30 -}
{-# TERMINATING #-}
free-shape : (v-shape : shape) → free
free-shape (X v-lanetype v-dim) = (free-lanetype v-lanetype)
free-shape v-shape = default-val

{- Auxiliary Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:417.1-417.38 -}
{-# TERMINATING #-}
free-blocktype : (v-blocktype : blocktype) → free
free-blocktype (-RESULT valtype-opt) = (free-opt (mapMaybe (λ (v-valtype : valtype) → (free-valtype v-valtype)) valtype-opt))
free-blocktype (blocktype--IDX v-typeidx) = (free-typeidx v-typeidx)
free-blocktype v-blocktype = default-val

{- Auxiliary Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:418.1-418.30 -}
{-# TERMINATING #-}
free-catch : (v-catch : catch) → free
free-catch (CATCH v-tagidx v-labelidx) = ((free-tagidx v-tagidx) ⧺ (free-labelidx v-labelidx))
free-catch (CATCH-REF v-tagidx v-labelidx) = ((free-tagidx v-tagidx) ⧺ (free-labelidx v-labelidx))
free-catch (CATCH-ALL v-labelidx) = (free-labelidx v-labelidx)
free-catch (CATCH-ALL-REF v-labelidx) = (free-labelidx v-labelidx)
free-catch v-catch = default-val

{- Auxiliary Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:584.1-584.44 -}
{-# TERMINATING #-}
shift-labelidxs : (var-0-lst : (List labelidx)) → (List labelidx)
shift-labelidxs [] = []
shift-labelidxs ((mk-uN (zero)) ∷ labelidx'-lst) = (shift-labelidxs labelidx'-lst)
shift-labelidxs (v-labelidx ∷ labelidx'-lst) = ((as (List labelidx) ((mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} (proj-uN-0 32 v-labelidx)) – (coerce {B = ℕ} 1)))) ∷ [])) ++ (shift-labelidxs labelidx'-lst))
shift-labelidxs var-0-lst = []

mutual
  {- Auxiliary Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:420.1-420.30 -}
  {-# TERMINATING #-}
  free-instr : (v-instr : instr) → free
  free-instr NOP = record { TYPES = [] ; FUNCS = [] ; GLOBALS = [] ; TABLES = [] ; MEMS = [] ; ELEMS = [] ; DATAS = [] ; LOCALS = [] ; LABELS = [] ; TAGS = [] }
  free-instr UNREACHABLE = record { TYPES = [] ; FUNCS = [] ; GLOBALS = [] ; TABLES = [] ; MEMS = [] ; ELEMS = [] ; DATAS = [] ; LOCALS = [] ; LABELS = [] ; TAGS = [] }
  free-instr DROP = record { TYPES = [] ; FUNCS = [] ; GLOBALS = [] ; TABLES = [] ; MEMS = [] ; ELEMS = [] ; DATAS = [] ; LOCALS = [] ; LABELS = [] ; TAGS = [] }
  free-instr (SELECT valtype-lst-opt) = (free-opt (mapMaybe (λ (valtype-lst : (List valtype)) → (free-list (map (λ (v-valtype : valtype) → (free-valtype v-valtype)) valtype-lst))) valtype-lst-opt))
  free-instr (BLOCK v-blocktype instr-lst) = ((free-blocktype v-blocktype) ⧺ (free-block instr-lst))
  free-instr (LOOP v-blocktype instr-lst) = ((free-blocktype v-blocktype) ⧺ (free-block instr-lst))
  free-instr (IFELSE v-blocktype instr-1-lst instr-2-lst) = (((free-blocktype v-blocktype) ⧺ (free-block instr-1-lst)) ⧺ (free-block instr-2-lst))
  free-instr (BR v-labelidx) = (free-labelidx v-labelidx)
  free-instr (BR-IF v-labelidx) = (free-labelidx v-labelidx)
  free-instr (BR-TABLE labelidx-lst labelidx') = ((free-list (map (λ (v-labelidx : labelidx) → (free-labelidx v-labelidx)) labelidx-lst)) ⧺ (free-labelidx labelidx'))
  free-instr (BR-ON-NULL v-labelidx) = (free-labelidx v-labelidx)
  free-instr (BR-ON-NON-NULL v-labelidx) = (free-labelidx v-labelidx)
  free-instr (BR-ON-CAST v-labelidx reftype-1 reftype-2) = (((free-labelidx v-labelidx) ⧺ (free-reftype reftype-1)) ⧺ (free-reftype reftype-2))
  free-instr (BR-ON-CAST-FAIL v-labelidx reftype-1 reftype-2) = (((free-labelidx v-labelidx) ⧺ (free-reftype reftype-1)) ⧺ (free-reftype reftype-2))
  free-instr (CALL v-funcidx) = (free-funcidx v-funcidx)
  free-instr (CALL-REF v-typeuse) = (free-typeuse v-typeuse)
  free-instr (CALL-INDIRECT v-tableidx v-typeuse) = ((free-tableidx v-tableidx) ⧺ (free-typeuse v-typeuse))
  free-instr RETURN = record { TYPES = [] ; FUNCS = [] ; GLOBALS = [] ; TABLES = [] ; MEMS = [] ; ELEMS = [] ; DATAS = [] ; LOCALS = [] ; LABELS = [] ; TAGS = [] }
  free-instr (RETURN-CALL v-funcidx) = (free-funcidx v-funcidx)
  free-instr (RETURN-CALL-REF v-typeuse) = (free-typeuse v-typeuse)
  free-instr (RETURN-CALL-INDIRECT v-tableidx v-typeuse) = ((free-tableidx v-tableidx) ⧺ (free-typeuse v-typeuse))
  free-instr (THROW v-tagidx) = (free-tagidx v-tagidx)
  free-instr THROW-REF = record { TYPES = [] ; FUNCS = [] ; GLOBALS = [] ; TABLES = [] ; MEMS = [] ; ELEMS = [] ; DATAS = [] ; LOCALS = [] ; LABELS = [] ; TAGS = [] }
  free-instr (TRY-TABLE v-blocktype (mk-list catch-lst) instr-lst) = (((free-blocktype v-blocktype) ⧺ (free-list (map (λ (v-catch : catch) → (free-catch v-catch)) catch-lst))) ⧺ (free-list (map (λ (v-instr : instr) → (free-instr v-instr)) instr-lst)))
  free-instr (instr-CONST v-numtype numlit) = (free-numtype v-numtype)
  free-instr (UNOP v-numtype unop) = (free-numtype v-numtype)
  free-instr (BINOP v-numtype binop) = (free-numtype v-numtype)
  free-instr (TESTOP v-numtype testop) = (free-numtype v-numtype)
  free-instr (RELOP v-numtype relop) = (free-numtype v-numtype)
  free-instr (CVTOP numtype-1 numtype-2 cvtop) = ((free-numtype numtype-1) ⧺ (free-numtype numtype-2))
  free-instr (instr-VCONST v-vectype veclit) = (free-vectype v-vectype)
  free-instr (VVUNOP v-vectype v-vvunop) = (free-vectype v-vectype)
  free-instr (VVBINOP v-vectype v-vvbinop) = (free-vectype v-vectype)
  free-instr (VVTERNOP v-vectype v-vvternop) = (free-vectype v-vectype)
  free-instr (VVTESTOP v-vectype v-vvtestop) = (free-vectype v-vectype)
  free-instr (VUNOP v-shape vunop) = (free-shape v-shape)
  free-instr (VBINOP v-shape vbinop) = (free-shape v-shape)
  free-instr (VTERNOP v-shape vternop) = (free-shape v-shape)
  free-instr (VTESTOP v-shape vtestop) = (free-shape v-shape)
  free-instr (VRELOP v-shape vrelop) = (free-shape v-shape)
  free-instr (VSHIFTOP v-ishape vshiftop) = (free-shape (coerce {B = shape} (v-ishape)))
  free-instr (VBITMASK v-ishape) = (free-shape (coerce {B = shape} (v-ishape)))
  free-instr (VSWIZZLOP v-bshape vswizzlop) = (free-shape (coerce {B = shape} (v-bshape)))
  free-instr (VSHUFFLE v-bshape laneidx-lst) = (free-shape (coerce {B = shape} (v-bshape)))
  free-instr (VEXTUNOP ishape-1 ishape-2 vextunop) = ((free-shape (coerce {B = shape} (ishape-1))) ⧺ (free-shape (coerce {B = shape} (ishape-2))))
  free-instr (VEXTBINOP ishape-1 ishape-2 vextbinop) = ((free-shape (coerce {B = shape} (ishape-1))) ⧺ (free-shape (coerce {B = shape} (ishape-2))))
  free-instr (VEXTTERNOP ishape-1 ishape-2 vextternop) = ((free-shape (coerce {B = shape} (ishape-1))) ⧺ (free-shape (coerce {B = shape} (ishape-2))))
  free-instr (VNARROW ishape-1 ishape-2 v-sx) = ((free-shape (coerce {B = shape} (ishape-1))) ⧺ (free-shape (coerce {B = shape} (ishape-2))))
  free-instr (VCVTOP shape-1 shape-2 vcvtop) = ((free-shape shape-1) ⧺ (free-shape shape-2))
  free-instr (VSPLAT v-shape) = (free-shape v-shape)
  free-instr (VEXTRACT-LANE v-shape sx-opt v-laneidx) = (free-shape v-shape)
  free-instr (VREPLACE-LANE v-shape v-laneidx) = (free-shape v-shape)
  free-instr (REF-NULL v-heaptype) = (free-heaptype v-heaptype)
  free-instr REF-IS-NULL = record { TYPES = [] ; FUNCS = [] ; GLOBALS = [] ; TABLES = [] ; MEMS = [] ; ELEMS = [] ; DATAS = [] ; LOCALS = [] ; LABELS = [] ; TAGS = [] }
  free-instr REF-AS-NON-NULL = record { TYPES = [] ; FUNCS = [] ; GLOBALS = [] ; TABLES = [] ; MEMS = [] ; ELEMS = [] ; DATAS = [] ; LOCALS = [] ; LABELS = [] ; TAGS = [] }
  free-instr REF-EQ = record { TYPES = [] ; FUNCS = [] ; GLOBALS = [] ; TABLES = [] ; MEMS = [] ; ELEMS = [] ; DATAS = [] ; LOCALS = [] ; LABELS = [] ; TAGS = [] }
  free-instr (REF-TEST v-reftype) = (free-reftype v-reftype)
  free-instr (REF-CAST v-reftype) = (free-reftype v-reftype)
  free-instr (REF-FUNC v-funcidx) = (free-funcidx v-funcidx)
  free-instr REF-I31 = record { TYPES = [] ; FUNCS = [] ; GLOBALS = [] ; TABLES = [] ; MEMS = [] ; ELEMS = [] ; DATAS = [] ; LOCALS = [] ; LABELS = [] ; TAGS = [] }
  free-instr (I31-GET v-sx) = record { TYPES = [] ; FUNCS = [] ; GLOBALS = [] ; TABLES = [] ; MEMS = [] ; ELEMS = [] ; DATAS = [] ; LOCALS = [] ; LABELS = [] ; TAGS = [] }
  free-instr (STRUCT-NEW v-typeidx) = (free-typeidx v-typeidx)
  free-instr (STRUCT-NEW-DEFAULT v-typeidx) = (free-typeidx v-typeidx)
  free-instr (STRUCT-GET sx-opt v-typeidx v-u32) = (free-typeidx v-typeidx)
  free-instr (STRUCT-SET v-typeidx v-u32) = (free-typeidx v-typeidx)
  free-instr (ARRAY-NEW v-typeidx) = (free-typeidx v-typeidx)
  free-instr (ARRAY-NEW-DEFAULT v-typeidx) = (free-typeidx v-typeidx)
  free-instr (ARRAY-NEW-FIXED v-typeidx v-u32) = (free-typeidx v-typeidx)
  free-instr (ARRAY-NEW-DATA v-typeidx v-dataidx) = ((free-typeidx v-typeidx) ⧺ (free-dataidx v-dataidx))
  free-instr (ARRAY-NEW-ELEM v-typeidx v-elemidx) = ((free-typeidx v-typeidx) ⧺ (free-elemidx v-elemidx))
  free-instr (ARRAY-GET sx-opt v-typeidx) = (free-typeidx v-typeidx)
  free-instr (ARRAY-SET v-typeidx) = (free-typeidx v-typeidx)
  free-instr ARRAY-LEN = record { TYPES = [] ; FUNCS = [] ; GLOBALS = [] ; TABLES = [] ; MEMS = [] ; ELEMS = [] ; DATAS = [] ; LOCALS = [] ; LABELS = [] ; TAGS = [] }
  free-instr (ARRAY-FILL v-typeidx) = (free-typeidx v-typeidx)
  free-instr (ARRAY-COPY typeidx-1 typeidx-2) = ((free-typeidx typeidx-1) ⧺ (free-typeidx typeidx-2))
  free-instr (ARRAY-INIT-DATA v-typeidx v-dataidx) = ((free-typeidx v-typeidx) ⧺ (free-dataidx v-dataidx))
  free-instr (ARRAY-INIT-ELEM v-typeidx v-elemidx) = ((free-typeidx v-typeidx) ⧺ (free-elemidx v-elemidx))
  free-instr EXTERN-CONVERT-ANY = record { TYPES = [] ; FUNCS = [] ; GLOBALS = [] ; TABLES = [] ; MEMS = [] ; ELEMS = [] ; DATAS = [] ; LOCALS = [] ; LABELS = [] ; TAGS = [] }
  free-instr ANY-CONVERT-EXTERN = record { TYPES = [] ; FUNCS = [] ; GLOBALS = [] ; TABLES = [] ; MEMS = [] ; ELEMS = [] ; DATAS = [] ; LOCALS = [] ; LABELS = [] ; TAGS = [] }
  free-instr (LOCAL-GET v-localidx) = (free-localidx v-localidx)
  free-instr (LOCAL-SET v-localidx) = (free-localidx v-localidx)
  free-instr (LOCAL-TEE v-localidx) = (free-localidx v-localidx)
  free-instr (GLOBAL-GET v-globalidx) = (free-globalidx v-globalidx)
  free-instr (GLOBAL-SET v-globalidx) = (free-globalidx v-globalidx)
  free-instr (TABLE-GET v-tableidx) = (free-tableidx v-tableidx)
  free-instr (TABLE-SET v-tableidx) = (free-tableidx v-tableidx)
  free-instr (TABLE-SIZE v-tableidx) = (free-tableidx v-tableidx)
  free-instr (TABLE-GROW v-tableidx) = (free-tableidx v-tableidx)
  free-instr (TABLE-FILL v-tableidx) = (free-tableidx v-tableidx)
  free-instr (TABLE-COPY tableidx-1 tableidx-2) = ((free-tableidx tableidx-1) ⧺ (free-tableidx tableidx-2))
  free-instr (TABLE-INIT v-tableidx v-elemidx) = ((free-tableidx v-tableidx) ⧺ (free-elemidx v-elemidx))
  free-instr (ELEM-DROP v-elemidx) = (free-elemidx v-elemidx)
  free-instr (LOAD v-numtype loadop-opt v-memidx v-memarg) = ((free-numtype v-numtype) ⧺ (free-memidx v-memidx))
  free-instr (STORE v-numtype storeop-opt v-memidx v-memarg) = ((free-numtype v-numtype) ⧺ (free-memidx v-memidx))
  free-instr (VLOAD v-vectype vloadop-opt v-memidx v-memarg) = ((free-vectype v-vectype) ⧺ (free-memidx v-memidx))
  free-instr (VLOAD-LANE v-vectype v-sz v-memidx v-memarg v-laneidx) = ((free-vectype v-vectype) ⧺ (free-memidx v-memidx))
  free-instr (VSTORE v-vectype v-memidx v-memarg) = ((free-vectype v-vectype) ⧺ (free-memidx v-memidx))
  free-instr (VSTORE-LANE v-vectype v-sz v-memidx v-memarg v-laneidx) = ((free-vectype v-vectype) ⧺ (free-memidx v-memidx))
  free-instr (MEMORY-SIZE v-memidx) = (free-memidx v-memidx)
  free-instr (MEMORY-GROW v-memidx) = (free-memidx v-memidx)
  free-instr (MEMORY-FILL v-memidx) = (free-memidx v-memidx)
  free-instr (MEMORY-COPY memidx-1 memidx-2) = ((free-memidx memidx-1) ⧺ (free-memidx memidx-2))
  free-instr (MEMORY-INIT v-memidx v-dataidx) = ((free-memidx v-memidx) ⧺ (free-dataidx v-dataidx))
  free-instr (DATA-DROP v-dataidx) = (free-dataidx v-dataidx)
  free-instr v-instr = default-val

  {- Auxiliary Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:421.1-421.31 -}
  {-# TERMINATING #-}
  free-block : (var-0-lst : (List instr)) → free
  free-block instr-lst = let v-free = (free-list (map (λ (v-instr : instr) → (free-instr v-instr)) instr-lst)) in (record v-free { LABELS = (shift-labelidxs (LABELS v-free)) })

{- Auxiliary Definition at: ../specification/wasm-3.0/1.3-syntax.instructions.spectec:422.1-422.28 -}
{-# TERMINATING #-}
free-expr : (v-expr : expr) → free
free-expr instr-lst = (free-list (map (λ (v-instr : instr) → (free-instr v-instr)) instr-lst))

{- Inductive Type Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:5.1-6.43 -}
data elemmode : Set where
  ACTIVE : (v-tableidx : tableidx) → (v-expr : expr) → elemmode
  PASSIVE : elemmode
  DECLARE : elemmode

instance
  inh-elemmode : Inhabited elemmode
  inh-elemmode = record { default-val = (ACTIVE (default-val) (default-val)) }

{- Inductive Type Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:7.1-8.31 -}
data datamode : Set where
  datamode-ACTIVE : (v-memidx : memidx) → (v-expr : expr) → datamode
  datamode-PASSIVE : datamode

instance
  inh-datamode : Inhabited datamode
  inh-datamode = record { default-val = (datamode-ACTIVE (default-val) (default-val)) }

{- Inductive Type Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:10.1-11.15 -}
data type : Set where
  TYPE : (v-rectype : rectype) → type

instance
  inh-type : Inhabited type
  inh-type = record { default-val = (TYPE (default-val)) }

{- Inductive Type Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:13.1-14.14 -}
data tag : Set where
  tag-TAG : (v-tagtype : tagtype) → tag

instance
  inh-tag : Inhabited tag
  inh-tag = record { default-val = (tag-TAG (default-val)) }

eq-tag-fun : tag → tag → Bool
eq-tag-fun (tag-TAG x0) (tag-TAG y0) = (x0 =? y0)
instance
  haseq-tag : HasEq tag
  haseq-tag = record { _=?_ = eq-tag-fun }

{- Inductive Type Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:16.1-17.25 -}
data global : Set where
  global-GLOBAL : (v-globaltype : globaltype) → (v-expr : expr) → global

instance
  inh-global : Inhabited global
  inh-global = record { default-val = (global-GLOBAL (default-val) (default-val)) }

{- Inductive Type Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:19.1-20.17 -}
data mem : Set where
  MEMORY : (v-memtype : memtype) → mem

instance
  inh-mem : Inhabited mem
  inh-mem = record { default-val = (MEMORY (default-val)) }

eq-mem-fun : mem → mem → Bool
eq-mem-fun (MEMORY x0) (MEMORY y0) = (x0 =? y0)
instance
  haseq-mem : HasEq mem
  haseq-mem = record { _=?_ = eq-mem-fun }

{- Inductive Type Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:22.1-23.23 -}
data table : Set where
  table-TABLE : (v-tabletype : tabletype) → (v-expr : expr) → table

instance
  inh-table : Inhabited table
  inh-table = record { default-val = (table-TABLE (default-val) (default-val)) }

{- Inductive Type Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:25.1-26.22 -}
data data' : Set where
  DATA : (byte-lst : (List byte)) → (v-datamode : datamode) → data'

instance
  inh-data' : Inhabited data'
  inh-data' = record { default-val = (DATA ([]) (default-val)) }

{- Inductive Type Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:28.1-29.16 -}
data local : Set where
  LOCAL : (v-valtype : valtype) → local

instance
  inh-local : Inhabited local
  inh-local = record { default-val = (LOCAL (default-val)) }

eq-local-fun : local → local → Bool
eq-local-fun (LOCAL x0) (LOCAL y0) = (x0 =? y0)
instance
  haseq-local : HasEq local
  haseq-local = record { _=?_ = eq-local-fun }

{- Inductive Type Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:31.1-32.27 -}
data func : Set where
  func-FUNC : (v-typeidx : typeidx) → (local-lst : (List local)) → (v-expr : expr) → func

instance
  inh-func : Inhabited func
  inh-func = record { default-val = (func-FUNC (default-val) ([]) (default-val)) }

{- Inductive Type Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:34.1-35.30 -}
data elem : Set where
  ELEM : (v-reftype : reftype) → (expr-lst : (List expr)) → (v-elemmode : elemmode) → elem

instance
  inh-elem : Inhabited elem
  inh-elem = record { default-val = (ELEM (default-val) ([]) (default-val)) }

{- Inductive Type Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:37.1-38.16 -}
data start : Set where
  START : (v-funcidx : funcidx) → start

instance
  inh-start : Inhabited start
  inh-start = record { default-val = (START (default-val)) }

{- Inductive Type Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:40.1-41.30 -}
data import' : Set where
  IMPORT : (v-name : name) → (v-name : name) → (v-externtype : externtype) → import'

instance
  inh-import' : Inhabited import'
  inh-import' = record { default-val = (IMPORT (default-val) (default-val) (default-val)) }

eq-import'-fun : import' → import' → Bool
eq-import'-fun (IMPORT x0 x1 x2) (IMPORT y0 y1 y2) = (x0 =? y0) ∧ (x1 =? y1) ∧ (x2 =? y2)
instance
  haseq-import' : HasEq import'
  haseq-import' = record { _=?_ = eq-import'-fun }

{- Inductive Type Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:43.1-44.24 -}
data export : Set where
  EXPORT : (v-name : name) → (v-externidx : externidx) → export

instance
  inh-export : Inhabited export
  inh-export = record { default-val = (EXPORT (default-val) (default-val)) }

{- Inductive Type Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:46.1-58.17 -}
data module' : Set where
  module-MODULE : (_ : (list-fam0 (type))) → (_ : (list-fam0 (import'))) → (_ : (list-fam0 (tag))) → (_ : (list-fam0 (global))) → (_ : (list-fam0 (mem))) → (_ : (list-fam0 (table))) → (_ : (list-fam0 (func))) → (_ : (list-fam0 (data'))) → (_ : (list-fam0 (elem))) → (start-opt : (Maybe start)) → (_ : (list-fam0 (export))) → module'

{- Auxiliary Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:73.1-73.28 -}
{-# TERMINATING #-}
free-type : (v-type : type) → free
free-type (TYPE v-rectype) = (free-rectype v-rectype)
free-type v-type = default-val

{- Auxiliary Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:74.1-74.26 -}
{-# TERMINATING #-}
free-tag : (v-tag : tag) → free
free-tag (tag-TAG v-tagtype) = (unwrap! (free-tagtype v-tagtype))
free-tag v-tag = default-val

{- Auxiliary Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:75.1-75.32 -}
{-# TERMINATING #-}
free-global : (v-global : global) → free
free-global (global-GLOBAL v-globaltype v-expr) = ((free-globaltype v-globaltype) ⧺ (free-expr v-expr))
free-global v-global = default-val

{- Auxiliary Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:76.1-76.26 -}
{-# TERMINATING #-}
free-mem : (v-mem : mem) → free
free-mem (MEMORY v-memtype) = (free-memtype v-memtype)
free-mem v-mem = default-val

{- Auxiliary Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:77.1-77.30 -}
{-# TERMINATING #-}
free-table : (v-table : table) → free
free-table (table-TABLE v-tabletype v-expr) = ((free-tabletype v-tabletype) ⧺ (free-expr v-expr))
free-table v-table = default-val

{- Auxiliary Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:78.1-78.30 -}
{-# TERMINATING #-}
free-local : (v-local : local) → free
free-local (LOCAL t) = (free-valtype t)
free-local v-local = default-val

{- Auxiliary Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:79.1-79.28 -}
{-# TERMINATING #-}
free-func : (v-func : func) → free
free-func (func-FUNC v-typeidx local-lst v-expr) = (((free-typeidx v-typeidx) ⧺ (free-list (map (λ (v-local : local) → (free-local v-local)) local-lst))) ⧺ (record (free-block v-expr) { LOCALS = [] }))
free-func v-func = default-val

{- Auxiliary Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:82.1-82.36 -}
{-# TERMINATING #-}
free-datamode : (v-datamode : datamode) → free
free-datamode (datamode-ACTIVE v-memidx v-expr) = ((free-memidx v-memidx) ⧺ (free-expr v-expr))
free-datamode datamode-PASSIVE = record { TYPES = [] ; FUNCS = [] ; GLOBALS = [] ; TABLES = [] ; MEMS = [] ; ELEMS = [] ; DATAS = [] ; LOCALS = [] ; LABELS = [] ; TAGS = [] }
free-datamode v-datamode = default-val

{- Auxiliary Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:80.1-80.28 -}
{-# TERMINATING #-}
free-data : (v-data : data') → free
free-data (DATA byte-lst v-datamode) = (free-datamode v-datamode)
free-data v-data = default-val

{- Auxiliary Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:83.1-83.36 -}
{-# TERMINATING #-}
free-elemmode : (v-elemmode : elemmode) → free
free-elemmode (ACTIVE v-tableidx v-expr) = ((free-tableidx v-tableidx) ⧺ (free-expr v-expr))
free-elemmode PASSIVE = record { TYPES = [] ; FUNCS = [] ; GLOBALS = [] ; TABLES = [] ; MEMS = [] ; ELEMS = [] ; DATAS = [] ; LOCALS = [] ; LABELS = [] ; TAGS = [] }
free-elemmode DECLARE = record { TYPES = [] ; FUNCS = [] ; GLOBALS = [] ; TABLES = [] ; MEMS = [] ; ELEMS = [] ; DATAS = [] ; LOCALS = [] ; LABELS = [] ; TAGS = [] }
free-elemmode v-elemmode = default-val

{- Auxiliary Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:81.1-81.28 -}
{-# TERMINATING #-}
free-elem : (v-elem : elem) → free
free-elem (ELEM v-reftype expr-lst v-elemmode) = (((free-reftype v-reftype) ⧺ (free-list (map (λ (v-expr : expr) → (free-expr v-expr)) expr-lst))) ⧺ (free-elemmode v-elemmode))
free-elem v-elem = default-val

{- Auxiliary Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:84.1-84.30 -}
{-# TERMINATING #-}
free-start : (v-start : start) → free
free-start (START v-funcidx) = (free-funcidx v-funcidx)
free-start v-start = default-val

{- Auxiliary Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:85.1-85.32 -}
{-# TERMINATING #-}
free-import : (v-import : import') → free
free-import (IMPORT name-1 name-2 v-externtype) = (unwrap! (free-externtype v-externtype))
free-import v-import = default-val

{- Auxiliary Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:86.1-86.32 -}
{-# TERMINATING #-}
free-export : (v-export : export) → free
free-export (EXPORT v-name v-externidx) = (free-externidx v-externidx)
free-export v-export = default-val

{- Auxiliary Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:87.1-87.32 -}
{-# TERMINATING #-}
free-module : (v-module : module') → free
free-module (module-MODULE (mk-list type-lst) (mk-list import-lst) (mk-list tag-lst) (mk-list global-lst) (mk-list mem-lst) (mk-list table-lst) (mk-list func-lst) (mk-list data-lst) (mk-list elem-lst) start-opt (mk-list export-lst)) = (((((((((((free-list (map (λ (v-type : type) → (free-type v-type)) type-lst)) ⧺ (free-list (map (λ (v-tag : tag) → (free-tag v-tag)) tag-lst))) ⧺ (free-list (map (λ (v-global : global) → (free-global v-global)) global-lst))) ⧺ (free-list (map (λ (v-mem : mem) → (free-mem v-mem)) mem-lst))) ⧺ (free-list (map (λ (v-table : table) → (free-table v-table)) table-lst))) ⧺ (free-list (map (λ (v-func : func) → (free-func v-func)) func-lst))) ⧺ (free-list (map (λ (v-data : data') → (free-data v-data)) data-lst))) ⧺ (free-list (map (λ (v-elem : elem) → (free-elem v-elem)) elem-lst))) ⧺ (free-opt (mapMaybe (λ (v-start : start) → (free-start v-start)) start-opt))) ⧺ (free-list (map (λ (v-import : import') → (free-import v-import)) import-lst))) ⧺ (free-list (map (λ (v-export : export) → (free-export v-export)) export-lst)))
free-module v-module = default-val

{- Auxiliary Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:141.1-141.89 -}
{-# TERMINATING #-}
funcidx-module : (v-module : module') → (List funcidx)
funcidx-module v-module = (FUNCS (free-module v-module))

{- Auxiliary Definition at: ../specification/wasm-3.0/1.4-syntax.modules.spectec:144.1-144.87 -}
{-# TERMINATING #-}
dataidx-funcs : (var-0-lst : (List func)) → (List dataidx)
dataidx-funcs func-lst = (DATAS (free-list (map (λ (v-func : func) → (free-func v-func)) func-lst)))

{- Inductive Type Definition at: ../specification/wasm-3.0/2.0-validation.contexts.spectec:8.1-9.16 -}
data init : Set where
  SET : init
  UNSET : init

instance
  inh-init : Inhabited init
  inh-init = record { default-val = SET }

{- Inductive Type Definition at: ../specification/wasm-3.0/2.0-validation.contexts.spectec:11.1-12.15 -}
data localtype : Set where
  mk-localtype : (v-init : init) → (v-valtype : valtype) → localtype

instance
  inh-localtype : Inhabited localtype
  inh-localtype = record { default-val = (mk-localtype (default-val) (default-val)) }

{- Inductive Type Definition at: ../specification/wasm-3.0/2.0-validation.contexts.spectec:14.1-15.57 -}
data instrtype : Set where
  mk-instrtype : (v-resulttype : resulttype) → (localidx-lst : (List localidx)) → (v-resulttype : resulttype) → instrtype

instance
  inh-instrtype : Inhabited instrtype
  inh-instrtype = record { default-val = (mk-instrtype (default-val) ([]) (default-val)) }

{- Record Creation Definition at: ../specification/wasm-3.0/2.0-validation.contexts.spectec:40.1-41.58 -}
record context : Set where
  constructor mk-context
  field
    context-TYPES : (List deftype)
    context-TAGS : (List tagtype)
    context-GLOBALS : (List globaltype)
    context-MEMS : (List memtype)
    context-TABLES : (List tabletype)
    context-FUNCS : (List deftype)
    context-DATAS : (List datatype)
    context-ELEMS : (List elemtype)
    context-LOCALS : (List localtype)
    context-LABELS : (List resulttype)
    context-RETURN : (Maybe resulttype)
    REFS : (List funcidx)
    RECS : (List subtype)
open context

instance
  append-context : HasAppend (context)
  append-context = record { append = λ arg1 arg2 → record {
    context-TYPES = context-TYPES arg1 ⧺ context-TYPES arg2 ;
    context-TAGS = context-TAGS arg1 ⧺ context-TAGS arg2 ;
    context-GLOBALS = context-GLOBALS arg1 ⧺ context-GLOBALS arg2 ;
    context-MEMS = context-MEMS arg1 ⧺ context-MEMS arg2 ;
    context-TABLES = context-TABLES arg1 ⧺ context-TABLES arg2 ;
    context-FUNCS = context-FUNCS arg1 ⧺ context-FUNCS arg2 ;
    context-DATAS = context-DATAS arg1 ⧺ context-DATAS arg2 ;
    context-ELEMS = context-ELEMS arg1 ⧺ context-ELEMS arg2 ;
    context-LOCALS = context-LOCALS arg1 ⧺ context-LOCALS arg2 ;
    context-LABELS = context-LABELS arg1 ⧺ context-LABELS arg2 ;
    context-RETURN = context-RETURN arg1 ⧺ context-RETURN arg2 ;
    REFS = REFS arg1 ⧺ REFS arg2 ;
    RECS = RECS arg1 ⧺ RECS arg2 } }

instance
  inh-context : Inhabited context
  inh-context = record { default-val = record { context-TYPES = default-val ; context-TAGS = default-val ; context-GLOBALS = default-val ; context-MEMS = default-val ; context-TABLES = default-val ; context-FUNCS = default-val ; context-DATAS = default-val ; context-ELEMS = default-val ; context-LOCALS = default-val ; context-LABELS = default-val ; context-RETURN = default-val ; REFS = default-val ; RECS = default-val } }

{- Auxiliary Definition at: ../specification/wasm-3.0/2.0-validation.contexts.spectec:49.1-49.158 -}
{-# TERMINATING #-}
with-locals : (v-context : context) (var-0-lst : (List localidx)) (var-1-lst : (List localtype)) → (Maybe context)
with-locals C [] [] = (just C)
with-locals C (x-1 ∷ x-lst) (lct-1 ∷ lct-lst) = (with-locals (record C { context-LOCALS = (modify (context-LOCALS C) (proj-uN-0 32 x-1) (λ (_ : localtype) → lct-1)) }) x-lst lct-lst)
with-locals x0 x1 x2 = nothing

{- Auxiliary Definition at: ../specification/wasm-3.0/2.0-validation.contexts.spectec:62.1-62.94 -}
{-# TERMINATING #-}
clos-deftypes : (var-0-lst : (List deftype)) → (List deftype)
clos-deftypes [] = []
clos-deftypes (dt-lst-hd ∷ dt-lst-tl) = let (dt-lst , dt-n) = unsnoc-cons dt-lst-hd dt-lst-tl in let dt'-lst = (clos-deftypes dt-lst) in (dt'-lst ++ ((subst-all-deftype dt-n (map (λ (dt' : deftype) → (typeuse-deftype dt')) dt'-lst)) ∷ []))
clos-deftypes var-0-lst = []

{- Auxiliary Definition at: ../specification/wasm-3.0/2.0-validation.contexts.spectec:57.1-57.93 -}
{-# TERMINATING #-}
clos-valtype : (v-context : context) (v-valtype : valtype) → valtype
clos-valtype C t = let dt-lst = (clos-deftypes (context-TYPES C)) in (subst-all-valtype t (map (λ (dt : deftype) → (typeuse-deftype dt)) dt-lst))

{- Auxiliary Definition at: ../specification/wasm-3.0/2.0-validation.contexts.spectec:58.1-58.93 -}
{-# TERMINATING #-}
clos-deftype : (v-context : context) (v-deftype : deftype) → deftype
clos-deftype C dt = let dt'-lst = (clos-deftypes (context-TYPES C)) in (subst-all-deftype dt (map (λ (dt' : deftype) → (typeuse-deftype dt')) dt'-lst))

{- Auxiliary Definition at: ../specification/wasm-3.0/2.0-validation.contexts.spectec:59.1-59.93 -}
{-# TERMINATING #-}
clos-tagtype : (v-context : context) (v-tagtype : tagtype) → tagtype
clos-tagtype C jt = let dt-lst = (clos-deftypes (context-TYPES C)) in (subst-all-tagtype jt (map (λ (dt : deftype) → (typeuse-deftype dt)) dt-lst))

{- Auxiliary Definition at: ../specification/wasm-3.0/2.0-validation.contexts.spectec:60.1-60.102 -}
{-# TERMINATING #-}
clos-externtype : (v-context : context) (v-externtype : externtype) → externtype
clos-externtype C xt = let dt-lst = (clos-deftypes (context-TYPES C)) in (subst-all-externtype xt (map (λ (dt : deftype) → (typeuse-deftype dt)) dt-lst))

{- Auxiliary Definition at: ../specification/wasm-3.0/2.0-validation.contexts.spectec:61.1-61.102 -}
{-# TERMINATING #-}
clos-moduletype : (v-context : context) (v-moduletype : moduletype) → moduletype
clos-moduletype C mmt = let dt-lst = (clos-deftypes (context-TYPES C)) in (subst-all-moduletype mmt (map (λ (dt : deftype) → (typeuse-deftype dt)) dt-lst))

{- Inductive Relations Definition at: ../specification/wasm-3.0/2.1-validation.types.spectec:7.1-7.91 -}
data Numtype-ok : context → numtype → Set where
  mk-Numtype-ok : ∀ (C : context) (v-numtype : numtype) → Numtype-ok C v-numtype

{- Inductive Relations Definition at: ../specification/wasm-3.0/2.1-validation.types.spectec:8.1-8.91 -}
data Vectype-ok : context → vectype → Set where
  mk-Vectype-ok : ∀ (C : context) (v-vectype : vectype) → Vectype-ok C v-vectype

{- Inductive Type Definition at: ../specification/wasm-3.0/2.1-validation.types.spectec:88.1-89.79 -}
data oktypenat : Set where
  oktypenat-OK : (_ : ℕ) → oktypenat

{- Inductive Relations Definition at: ../specification/wasm-3.0/2.1-validation.types.spectec:91.1-91.103 -}
data Packtype-ok : context → packtype → Set where
  mk-Packtype-ok : ∀ (C : context) (v-packtype : packtype) → Packtype-ok C v-packtype

{- Inductive Relations Definition at: ../specification/wasm-3.0/2.2-validation.subtyping.spectec:149.1-149.116 -}
data Packtype-sub : context → packtype → packtype → Set where
  mk-Packtype-sub : ∀ (C : context) (v-packtype : packtype) → Packtype-sub C v-packtype v-packtype

{- Inductive Relations Definition at: ../specification/wasm-3.0/2.2-validation.subtyping.spectec:7.1-7.103 -}
data Numtype-sub : context → numtype → numtype → Set where
  mk-Numtype-sub : ∀ (C : context) (v-numtype : numtype) → Numtype-sub C v-numtype v-numtype

{- Inductive Relations Definition at: ../specification/wasm-3.0/2.1-validation.types.spectec:73.1-74.70 -}
data Expand : deftype → comptype → Set where
  mk-Expand : ∀ (v-deftype : deftype) (v-comptype : comptype) (final-opt : (Maybe final)) (typeuse-lst : (List typeuse)) → 
    ((unrolldt v-deftype) ≡ (SUB final-opt typeuse-lst v-comptype)) →
    Expand v-deftype v-comptype

{- Inductive Relations Definition at: ../specification/wasm-3.0/2.2-validation.subtyping.spectec:8.1-8.103 -}
data Vectype-sub : context → vectype → vectype → Set where
  mk-Vectype-sub : ∀ (C : context) (v-vectype : vectype) → Vectype-sub C v-vectype v-vectype

{- Auxiliary Definition at: ../specification/wasm-3.0/2.1-validation.types.spectec:158.1-158.70 -}
{-# TERMINATING #-}
before : (v-typeuse : typeuse) (nat : ℕ) → Bool
before (REC j) i = (j <? i)
before v-typeuse i = true

{- Auxiliary Definition at: ../specification/wasm-3.0/2.1-validation.types.spectec:162.1-162.44 -}
{-# TERMINATING #-}
unrollht- : (v-context : context) (v-heaptype : heaptype) → subtype
unrollht- C (heaptype--DEF v-rectype v-n) = (unrolldt (deftype--DEF v-rectype v-n))
unrollht- C (heaptype--IDX v-typeidx) = (unrolldt ((context-TYPES C) [ (proj-uN-0 32 v-typeidx) ]!))
unrollht- C (heaptype-REC i) = ((RECS C) [ i ]!)
unrollht- v-context v-heaptype = default-val

mutual
  {- Inductive Relations Definition at: ../specification/wasm-3.0/2.1-validation.types.spectec:9.1-9.92 -}
  data Heaptype-ok : context → heaptype → Set where
    abs : ∀ (C : context) (v-absheaptype : absheaptype) → Heaptype-ok C (heaptype-absheaptype v-absheaptype)
    Heaptype-ok--typeuse : ∀ (C : context) (v-typeuse : typeuse) → 
      (Typeuse-ok C v-typeuse) →
      Heaptype-ok C (heaptype-typeuse v-typeuse)
    bot : ∀ (C : context) → Heaptype-ok C heaptype-BOT

  {- Inductive Relations Definition at: ../specification/wasm-3.0/2.1-validation.types.spectec:10.1-10.91 -}
  data Reftype-ok : context → reftype → Set where
    mk-Reftype-ok : ∀ (C : context) (v-heaptype : heaptype) → 
      (Heaptype-ok C v-heaptype) →
      Reftype-ok C (reftype-REF (just NULL) v-heaptype)

  {- Inductive Relations Definition at: ../specification/wasm-3.0/2.1-validation.types.spectec:11.1-11.91 -}
  data Valtype-ok : context → valtype → Set where
    Valtype-ok--num : ∀ (C : context) (v-numtype : numtype) → 
      (Numtype-ok C v-numtype) →
      Valtype-ok C (valtype-numtype v-numtype)
    Valtype-ok--vec : ∀ (C : context) (v-vectype : vectype) → 
      (Vectype-ok C v-vectype) →
      Valtype-ok C (valtype-vectype v-vectype)
    Valtype-ok--ref : ∀ (C : context) (v-reftype : reftype) → 
      (Reftype-ok C v-reftype) →
      Valtype-ok C (valtype-reftype v-reftype)
    Valtype-ok--bot : ∀ (C : context) → Valtype-ok C valtype-BOT

  {- Inductive Relations Definition at: ../specification/wasm-3.0/2.1-validation.types.spectec:12.1-12.94 -}
  data Typeuse-ok : context → typeuse → Set where
    Typeuse-ok--typeidx : ∀ (C : context) (v-typeidx : typeidx) (dt : deftype) → 
      ((proj-uN-0 32 v-typeidx) < (length (context-TYPES C))) →
      (((context-TYPES C) [ (proj-uN-0 32 v-typeidx) ]!) ≡ dt) →
      Typeuse-ok C (-IDX v-typeidx)
    rec : ∀ (C : context) (i : n) (st : subtype) → 
      (i < (length (RECS C))) →
      (((RECS C) [ i ]!) ≡ st) →
      Typeuse-ok C (REC i)
    Typeuse-ok--deftype : ∀ (C : context) (v-deftype : deftype) → 
      (Deftype-ok C v-deftype) →
      Typeuse-ok C (typeuse-deftype v-deftype)

  {- Inductive Relations Definition at: ../specification/wasm-3.0/2.1-validation.types.spectec:53.1-53.100 -}
  data Resulttype-ok : context → resulttype → Set where
    mk-Resulttype-ok : ∀ (C : context) (t-lst : (List valtype)) → 
      Forall (λ (t : valtype) → (Valtype-ok C t)) t-lst →
      Resulttype-ok C (mk-list t-lst)

  {- Inductive Relations Definition at: ../specification/wasm-3.0/2.1-validation.types.spectec:92.1-92.104 -}
  data Fieldtype-ok : context → fieldtype → Set where
    mk-Fieldtype-ok : ∀ (C : context) (v-storagetype : storagetype) → 
      (Storagetype-ok C v-storagetype) →
      Fieldtype-ok C (mk-fieldtype (just MUT) v-storagetype)

  {- Inductive Relations Definition at: ../specification/wasm-3.0/2.1-validation.types.spectec:93.1-93.106 -}
  data Storagetype-ok : context → storagetype → Set where
    Storagetype-ok--val : ∀ (C : context) (v-valtype : valtype) → 
      (Valtype-ok C v-valtype) →
      Storagetype-ok C (storagetype-valtype v-valtype)
    pack : ∀ (C : context) (v-packtype : packtype) → 
      (Packtype-ok C v-packtype) →
      Storagetype-ok C (storagetype-packtype v-packtype)

  {- Inductive Relations Definition at: ../specification/wasm-3.0/2.1-validation.types.spectec:94.1-94.103 -}
  data Comptype-ok : context → comptype → Set where
    struct : ∀ (C : context) (fieldtype-lst : (List fieldtype)) → 
      Forall (λ (v-fieldtype : fieldtype) → (Fieldtype-ok C v-fieldtype)) fieldtype-lst →
      Comptype-ok C (comptype-STRUCT (mk-list fieldtype-lst))
    array : ∀ (C : context) (v-fieldtype : fieldtype) → 
      (Fieldtype-ok C v-fieldtype) →
      Comptype-ok C (comptype-ARRAY v-fieldtype)
    Comptype-ok--func : ∀ (C : context) (t-1-lst : (List valtype)) (t-2-lst : (List valtype)) → 
      (Resulttype-ok C (mk-list t-1-lst)) →
      (Resulttype-ok C (mk-list t-2-lst)) →
      Comptype-ok C (comptype-FUNC (mk-list t-1-lst) (mk-list t-2-lst))

  {- Inductive Relations Definition at: ../specification/wasm-3.0/2.1-validation.types.spectec:97.1-97.126 -}
  data Subtype-ok2 : context → subtype → oktypenat → Set where
    mk-Subtype-ok2 : ∀ (C : context) (typeuse-lst : (List typeuse)) (v-comptype : comptype) (i : ℕ) (comptype'-lst : (List comptype)) (typeuse'-lst-lst : (List (List typeuse))) → 
      ((length typeuse-lst) ≤ 1) →
      Forall (λ (v-typeuse : typeuse) → (Typeuse-ok C v-typeuse)) typeuse-lst →
      Forall (λ (v-typeuse : typeuse) → (is-true (before v-typeuse i))) typeuse-lst →
      ((length comptype'-lst) ≡ (length typeuse-lst)) →
      ((length comptype'-lst) ≡ (length typeuse'-lst-lst)) →
      Forall₃ (λ (comptype' : comptype) (v-typeuse : typeuse) (typeuse'-lst : (List typeuse)) → ((unrollht- C (heaptype-typeuse v-typeuse)) ≡ (SUB nothing typeuse'-lst comptype'))) comptype'-lst typeuse-lst typeuse'-lst-lst →
      (Comptype-ok C v-comptype) →
      Forall (λ (comptype' : comptype) → (Comptype-sub C v-comptype comptype')) comptype'-lst →
      Subtype-ok2 C (SUB (just FINAL) typeuse-lst v-comptype) (oktypenat-OK i)

  {- Inductive Relations Definition at: ../specification/wasm-3.0/2.1-validation.types.spectec:98.1-98.126 -}
  data Rectype-ok2 : context → rectype → oktypenat → Set where
    empty : ∀ (C : context) (i : ℕ) → Rectype-ok2 C (rectype-REC (mk-list [])) (oktypenat-OK i)
    cons : ∀ (C : context) (subtype-1 : subtype) (subtype-lst : (List subtype)) (i : ℕ) → 
      (Subtype-ok2 C subtype-1 (oktypenat-OK i)) →
      (Rectype-ok2 C (rectype-REC (mk-list subtype-lst)) (oktypenat-OK (i + 1))) →
      Rectype-ok2 C (rectype-REC (mk-list ((subtype-1 ∷ []) ++ subtype-lst))) (oktypenat-OK i)

  {- Inductive Relations Definition at: ../specification/wasm-3.0/2.1-validation.types.spectec:99.1-99.102 -}
  data Deftype-ok : context → deftype → Set where
    mk-Deftype-ok : ∀ (C : context) (v-rectype : rectype) (i : n) (v-n : n) (subtype-lst : (List subtype)) → 
      ((length (subtype-lst)) ≡ (v-n)) →
      (Rectype-ok2 (record { context-TYPES = [] ; context-TAGS = [] ; context-GLOBALS = [] ; context-MEMS = [] ; context-TABLES = [] ; context-FUNCS = [] ; context-DATAS = [] ; context-ELEMS = [] ; context-LOCALS = [] ; context-LABELS = [] ; context-RETURN = nothing ; REFS = [] ; RECS = subtype-lst } ⧺ C) v-rectype (oktypenat-OK 0)) →
      (v-rectype ≡ (rectype-REC (mk-list subtype-lst))) →
      (i < v-n) →
      Deftype-ok C (deftype--DEF v-rectype i)

  {- Inductive Relations Definition at: ../specification/wasm-3.0/2.1-validation.types.spectec:102.1-102.108 -}
  data Comptype-sub : context → comptype → comptype → Set where
    Comptype-sub--struct : ∀ (C : context) (ft-1-lst : (List fieldtype)) (ft'-1-lst : (List fieldtype)) (ft-2-lst : (List fieldtype)) → 
      ((length ft-1-lst) ≡ (length ft-2-lst)) →
      Forall₂ (λ (ft-1 : fieldtype) (ft-2 : fieldtype) → (Fieldtype-sub C ft-1 ft-2)) ft-1-lst ft-2-lst →
      Comptype-sub C (comptype-STRUCT (mk-list (ft-1-lst ++ ft'-1-lst))) (comptype-STRUCT (mk-list ft-2-lst))
    Comptype-sub--array : ∀ (C : context) (ft-1 : fieldtype) (ft-2 : fieldtype) → 
      (Fieldtype-sub C ft-1 ft-2) →
      Comptype-sub C (comptype-ARRAY ft-1) (comptype-ARRAY ft-2)
    Comptype-sub--func : ∀ (C : context) (t-11-lst : (List valtype)) (t-12-lst : (List valtype)) (t-21-lst : (List valtype)) (t-22-lst : (List valtype)) → 
      (Resulttype-sub C (mk-list t-21-lst) (mk-list t-11-lst)) →
      (Resulttype-sub C (mk-list t-12-lst) (mk-list t-22-lst)) →
      Comptype-sub C (comptype-FUNC (mk-list t-11-lst) (mk-list t-12-lst)) (comptype-FUNC (mk-list t-21-lst) (mk-list t-22-lst))

  {- Inductive Relations Definition at: ../specification/wasm-3.0/2.1-validation.types.spectec:103.1-103.107 -}
  data Deftype-sub : context → deftype → deftype → Set where
    refl' : ∀ (C : context) (deftype-1 : deftype) (deftype-2 : deftype) → 
      ((clos-deftype C deftype-1) ≡ (clos-deftype C deftype-2)) →
      Deftype-sub C deftype-1 deftype-2
    super : ∀ (C : context) (deftype-1 : deftype) (deftype-2 : deftype) (final-opt : (Maybe final)) (typeuse-lst : (List typeuse)) (ct : comptype) (i : ℕ) → 
      ((unrolldt deftype-1) ≡ (SUB final-opt typeuse-lst ct)) →
      (i < (length typeuse-lst)) →
      (Heaptype-sub C (heaptype-typeuse (typeuse-lst [ i ]!)) (heaptype-deftype deftype-2)) →
      Deftype-sub C deftype-1 deftype-2

  {- Inductive Relations Definition at: ../specification/wasm-3.0/2.2-validation.subtyping.spectec:9.1-9.104 -}
  data Heaptype-sub : context → heaptype → heaptype → Set where
    Heaptype-sub--refl : ∀ (C : context) (v-heaptype : heaptype) → Heaptype-sub C v-heaptype v-heaptype
    trans : ∀ (C : context) (heaptype-1 : heaptype) (heaptype-2 : heaptype) (heaptype' : heaptype) → 
      (Heaptype-ok C heaptype') →
      (Heaptype-sub C heaptype-1 heaptype') →
      (Heaptype-sub C heaptype' heaptype-2) →
      Heaptype-sub C heaptype-1 heaptype-2
    eq-any : ∀ (C : context) → Heaptype-sub C heaptype-EQ heaptype-ANY
    i31-eq : ∀ (C : context) → Heaptype-sub C heaptype-I31 heaptype-EQ
    struct-eq : ∀ (C : context) → Heaptype-sub C heaptype-STRUCT heaptype-EQ
    array-eq : ∀ (C : context) → Heaptype-sub C heaptype-ARRAY heaptype-EQ
    Heaptype-sub--struct : ∀ (C : context) (v-deftype : deftype) (fieldtype-lst : (List fieldtype)) → 
      (Expand v-deftype (comptype-STRUCT (mk-list fieldtype-lst))) →
      Heaptype-sub C (heaptype-deftype v-deftype) heaptype-STRUCT
    Heaptype-sub--array : ∀ (C : context) (v-deftype : deftype) (v-fieldtype : fieldtype) → 
      (Expand v-deftype (comptype-ARRAY v-fieldtype)) →
      Heaptype-sub C (heaptype-deftype v-deftype) heaptype-ARRAY
    Heaptype-sub--func : ∀ (C : context) (v-deftype : deftype) (t-1-lst : (List valtype)) (t-2-lst : (List valtype)) → 
      (Expand v-deftype (comptype-FUNC (mk-list t-1-lst) (mk-list t-2-lst))) →
      Heaptype-sub C (heaptype-deftype v-deftype) heaptype-FUNC
    def : ∀ (C : context) (deftype-1 : deftype) (deftype-2 : deftype) → 
      (Deftype-sub C deftype-1 deftype-2) →
      Heaptype-sub C (heaptype-deftype deftype-1) (heaptype-deftype deftype-2)
    typeidx-l : ∀ (C : context) (v-typeidx : typeidx) (v-heaptype : heaptype) → 
      ((proj-uN-0 32 v-typeidx) < (length (context-TYPES C))) →
      (Heaptype-sub C (heaptype-deftype ((context-TYPES C) [ (proj-uN-0 32 v-typeidx) ]!)) v-heaptype) →
      Heaptype-sub C (heaptype--IDX v-typeidx) v-heaptype
    typeidx-r : ∀ (C : context) (v-heaptype : heaptype) (v-typeidx : typeidx) → 
      ((proj-uN-0 32 v-typeidx) < (length (context-TYPES C))) →
      (Heaptype-sub C v-heaptype (heaptype-deftype ((context-TYPES C) [ (proj-uN-0 32 v-typeidx) ]!))) →
      Heaptype-sub C v-heaptype (heaptype--IDX v-typeidx)
    rec-struct : ∀ (C : context) (i : n) (final-opt : (Maybe final)) (fieldtype-lst : (List fieldtype)) → 
      (i < (length (RECS C))) →
      (((RECS C) [ i ]!) ≡ (SUB final-opt [] (comptype-STRUCT (mk-list fieldtype-lst)))) →
      Heaptype-sub C (heaptype-REC i) heaptype-STRUCT
    rec-array : ∀ (C : context) (i : n) (final-opt : (Maybe final)) (v-fieldtype : fieldtype) → 
      (i < (length (RECS C))) →
      (((RECS C) [ i ]!) ≡ (SUB final-opt [] (comptype-ARRAY v-fieldtype))) →
      Heaptype-sub C (heaptype-REC i) heaptype-ARRAY
    rec-func : ∀ (C : context) (i : n) (final-opt : (Maybe final)) (t-1-lst : (List valtype)) (t-2-lst : (List valtype)) → 
      (i < (length (RECS C))) →
      (((RECS C) [ i ]!) ≡ (SUB final-opt [] (comptype-FUNC (mk-list t-1-lst) (mk-list t-2-lst)))) →
      Heaptype-sub C (heaptype-REC i) heaptype-FUNC
    rec-sub : ∀ (C : context) (i : n) (typeuse-lst : (List typeuse)) (j : ℕ) (final-opt : (Maybe final)) (ct : comptype) → 
      (j < (length typeuse-lst)) →
      (i < (length (RECS C))) →
      (((RECS C) [ i ]!) ≡ (SUB final-opt typeuse-lst ct)) →
      Heaptype-sub C (heaptype-REC i) (heaptype-typeuse (typeuse-lst [ j ]!))
    none : ∀ (C : context) (v-heaptype : heaptype) → 
      (Heaptype-sub C v-heaptype heaptype-ANY) →
      (v-heaptype ≢ heaptype-BOT) →
      Heaptype-sub C heaptype-NONE v-heaptype
    nofunc : ∀ (C : context) (v-heaptype : heaptype) → 
      (Heaptype-sub C v-heaptype heaptype-FUNC) →
      (v-heaptype ≢ heaptype-BOT) →
      Heaptype-sub C heaptype-NOFUNC v-heaptype
    noexn : ∀ (C : context) (v-heaptype : heaptype) → 
      (Heaptype-sub C v-heaptype heaptype-EXN) →
      (v-heaptype ≢ heaptype-BOT) →
      Heaptype-sub C heaptype-NOEXN v-heaptype
    noextern : ∀ (C : context) (v-heaptype : heaptype) → 
      (Heaptype-sub C v-heaptype heaptype-EXTERN) →
      (v-heaptype ≢ heaptype-BOT) →
      Heaptype-sub C heaptype-NOEXTERN v-heaptype
    Heaptype-sub--bot : ∀ (C : context) (v-heaptype : heaptype) → Heaptype-sub C heaptype-BOT v-heaptype

  {- Inductive Relations Definition at: ../specification/wasm-3.0/2.2-validation.subtyping.spectec:10.1-10.103 -}
  data Reftype-sub : context → reftype → reftype → Set where
    nonnull : ∀ (C : context) (ht-1 : heaptype) (ht-2 : heaptype) → 
      (Heaptype-sub C ht-1 ht-2) →
      Reftype-sub C (reftype-REF nothing ht-1) (reftype-REF nothing ht-2)
    Reftype-sub--null : ∀ (C : context) (ht-1 : heaptype) (ht-2 : heaptype) → 
      (Heaptype-sub C ht-1 ht-2) →
      Reftype-sub C (reftype-REF (just NULL) ht-1) (reftype-REF (just NULL) ht-2)

  {- Inductive Relations Definition at: ../specification/wasm-3.0/2.2-validation.subtyping.spectec:11.1-11.103 -}
  data Valtype-sub : context → valtype → valtype → Set where
    Valtype-sub--num : ∀ (C : context) (numtype-1 : numtype) (numtype-2 : numtype) → 
      (Numtype-sub C numtype-1 numtype-2) →
      Valtype-sub C (valtype-numtype numtype-1) (valtype-numtype numtype-2)
    Valtype-sub--vec : ∀ (C : context) (vectype-1 : vectype) (vectype-2 : vectype) → 
      (Vectype-sub C vectype-1 vectype-2) →
      Valtype-sub C (valtype-vectype vectype-1) (valtype-vectype vectype-2)
    Valtype-sub--ref : ∀ (C : context) (reftype-1 : reftype) (reftype-2 : reftype) → 
      (Reftype-sub C reftype-1 reftype-2) →
      Valtype-sub C (valtype-reftype reftype-1) (valtype-reftype reftype-2)
    Valtype-sub--bot : ∀ (C : context) (v-valtype : valtype) → Valtype-sub C valtype-BOT v-valtype

  {- Inductive Relations Definition at: ../specification/wasm-3.0/2.2-validation.subtyping.spectec:132.1-132.115 -}
  data Resulttype-sub : context → resulttype → resulttype → Set where
    mk-Resulttype-sub : ∀ (C : context) (t-1-lst : (List valtype)) (t-2-lst : (List valtype)) → 
      ((length t-1-lst) ≡ (length t-2-lst)) →
      Forall₂ (λ (t-1 : valtype) (t-2 : valtype) → (Valtype-sub C t-1 t-2)) t-1-lst t-2-lst →
      Resulttype-sub C (mk-list t-1-lst) (mk-list t-2-lst)

  {- Inductive Relations Definition at: ../specification/wasm-3.0/2.2-validation.subtyping.spectec:150.1-150.119 -}
  data Storagetype-sub : context → storagetype → storagetype → Set where
    Storagetype-sub--val : ∀ (C : context) (valtype-1 : valtype) (valtype-2 : valtype) → 
      (Valtype-sub C valtype-1 valtype-2) →
      Storagetype-sub C (storagetype-valtype valtype-1) (storagetype-valtype valtype-2)
    Storagetype-sub--pack : ∀ (C : context) (packtype-1 : packtype) (packtype-2 : packtype) → 
      (Packtype-sub C packtype-1 packtype-2) →
      Storagetype-sub C (storagetype-packtype packtype-1) (storagetype-packtype packtype-2)

  {- Inductive Relations Definition at: ../specification/wasm-3.0/2.2-validation.subtyping.spectec:151.1-151.117 -}
  data Fieldtype-sub : context → fieldtype → fieldtype → Set where
    Fieldtype-sub--const : ∀ (C : context) (zt-1 : storagetype) (zt-2 : storagetype) → 
      (Storagetype-sub C zt-1 zt-2) →
      Fieldtype-sub C (mk-fieldtype nothing zt-1) (mk-fieldtype nothing zt-2)
    var : ∀ (C : context) (zt-1 : storagetype) (zt-2 : storagetype) → 
      (Storagetype-sub C zt-1 zt-2) →
      (Storagetype-sub C zt-2 zt-1) →
      Fieldtype-sub C (mk-fieldtype (just MUT) zt-1) (mk-fieldtype (just MUT) zt-2)

{- Inductive Relations Definition at: ../specification/wasm-3.0/2.1-validation.types.spectec:52.1-52.96 -}
data Localtype-ok : context → localtype → Set where
  mk-Localtype-ok : ∀ (C : context) (v-init : init) (t : valtype) → 
    (Valtype-ok C t) →
    Localtype-ok C (mk-localtype v-init t)

{- Inductive Relations Definition at: ../specification/wasm-3.0/2.1-validation.types.spectec:54.1-54.99 -}
data Instrtype-ok : context → instrtype → Set where
  mk-Instrtype-ok : ∀ (C : context) (t-1-lst : (List valtype)) (x-lst : (List idx)) (t-2-lst : (List valtype)) (lct-lst : (List localtype)) → 
    (Resulttype-ok C (mk-list t-1-lst)) →
    (Resulttype-ok C (mk-list t-2-lst)) →
    ((length lct-lst) ≡ (length x-lst)) →
    Forall (λ (x : idx) → ((proj-uN-0 32 x) < (length (context-LOCALS C)))) x-lst →
    Forall₂ (λ (lct : localtype) (x : idx) → (((context-LOCALS C) [ (proj-uN-0 32 x) ]!) ≡ lct)) lct-lst x-lst →
    Instrtype-ok C (mk-instrtype (mk-list t-1-lst) x-lst (mk-list t-2-lst))

{- Inductive Relations Definition at: ../specification/wasm-3.0/2.1-validation.types.spectec:75.1-76.70 -}
data Expand-use : typeuse → context → comptype → Set where
  Expand-use--deftype : ∀ (v-deftype : deftype) (C : context) (v-comptype : comptype) → 
    (Expand v-deftype v-comptype) →
    Expand-use (typeuse-deftype v-deftype) C v-comptype
  Expand-use--typeidx : ∀ (v-typeidx : typeidx) (C : context) (v-comptype : comptype) → 
    ((proj-uN-0 32 v-typeidx) < (length (context-TYPES C))) →
    (Expand ((context-TYPES C) [ (proj-uN-0 32 v-typeidx) ]!) v-comptype) →
    Expand-use (-IDX v-typeidx) C v-comptype

{- Inductive Type Definition at: ../specification/wasm-3.0/2.1-validation.types.spectec:86.1-87.76 -}
data oktypeidx : Set where
  oktypeidx-OK : (v-typeidx : typeidx) → oktypeidx

{- Inductive Relations Definition at: ../specification/wasm-3.0/2.1-validation.types.spectec:95.1-95.126 -}
data Subtype-ok : context → subtype → oktypeidx → Set where
  mk-Subtype-ok : ∀ (C : context) (x-lst : (List idx)) (v-comptype : comptype) (x-0 : idx) (comptype'-lst : (List comptype)) (yy-lst-lst : (List (List typeuse))) → 
    ((length x-lst) ≤ 1) →
    Forall (λ (x : idx) → ((proj-uN-0 32 x) < (proj-uN-0 32 x-0))) x-lst →
    ((length comptype'-lst) ≡ (length x-lst)) →
    ((length comptype'-lst) ≡ (length yy-lst-lst)) →
    Forall (λ (x : idx) → ((proj-uN-0 32 x) < (length (context-TYPES C)))) x-lst →
    Forall₃ (λ (comptype' : comptype) (x : idx) (yy-lst : (List typeuse)) → ((unrolldt ((context-TYPES C) [ (proj-uN-0 32 x) ]!)) ≡ (SUB nothing yy-lst comptype'))) comptype'-lst x-lst yy-lst-lst →
    (Comptype-ok C v-comptype) →
    Forall (λ (comptype' : comptype) → (Comptype-sub C v-comptype comptype')) comptype'-lst →
    Subtype-ok C (SUB (just FINAL) (map (λ (x : typeidx) → (-IDX x)) x-lst) v-comptype) (oktypeidx-OK x-0)

{- Inductive Relations Definition at: ../specification/wasm-3.0/2.1-validation.types.spectec:96.1-96.126 -}
data Rectype-ok : context → rectype → oktypeidx → Set where
  Rectype-ok--empty : ∀ (C : context) (x : idx) → Rectype-ok C (rectype-REC (mk-list [])) (oktypeidx-OK x)
  Rectype-ok--cons : ∀ (C : context) (subtype-1 : subtype) (subtype-lst : (List subtype)) (x : idx) → 
    (Subtype-ok C subtype-1 (oktypeidx-OK x)) →
    (Rectype-ok C (rectype-REC (mk-list subtype-lst)) (oktypeidx-OK (mk-uN ((proj-uN-0 32 x) + 1)))) →
    Rectype-ok C (rectype-REC (mk-list ((subtype-1 ∷ []) ++ subtype-lst))) (oktypeidx-OK x)

{- Inductive Relations Definition at: ../specification/wasm-3.0/2.1-validation.types.spectec:206.1-206.120 -}
data Limits-ok : context → limits → ℕ → Set where
  mk-Limits-ok : ∀ (C : context) (v-n : n) (m-opt : (Maybe m)) (k : ℕ) → 
    (v-n ≤ k) →
    Forall (λ (v-m : ℕ) → ((v-n ≤ v-m) × (v-m ≤ k))) (fromMaybe m-opt) →
    Limits-ok C (mk-limits (mk-uN v-n) (mapMaybe (λ (v-m : ℕ) → (mk-uN v-m)) m-opt)) k

{- Inductive Relations Definition at: ../specification/wasm-3.0/2.1-validation.types.spectec:207.1-207.97 -}
data Tagtype-ok : context → tagtype → Set where
  mk-Tagtype-ok : ∀ (C : context) (v-typeuse : typeuse) (t-1-lst : (List valtype)) (t-2-lst : (List valtype)) → 
    (Typeuse-ok C v-typeuse) →
    (Expand-use v-typeuse C (comptype-FUNC (mk-list t-1-lst) (mk-list t-2-lst))) →
    Tagtype-ok C v-typeuse

{- Inductive Relations Definition at: ../specification/wasm-3.0/2.1-validation.types.spectec:208.1-208.100 -}
data Globaltype-ok : context → globaltype → Set where
  mk-Globaltype-ok : ∀ (C : context) (t : valtype) → 
    (Valtype-ok C t) →
    Globaltype-ok C (mk-globaltype (just MUT) t)

{- Inductive Relations Definition at: ../specification/wasm-3.0/2.1-validation.types.spectec:209.1-209.97 -}
data Memtype-ok : context → memtype → Set where
  mk-Memtype-ok : ∀ (C : context) (v-addrtype : addrtype) (v-limits : limits) → 
    (Limits-ok C v-limits (2 ^ (coerce {B = ℕ} ((coerce {B = ℕ} (size (numtype-addrtype v-addrtype))) – (coerce {B = ℕ} 16))))) →
    Memtype-ok C (PAGE v-addrtype v-limits)

{- Inductive Relations Definition at: ../specification/wasm-3.0/2.1-validation.types.spectec:210.1-210.99 -}
data Tabletype-ok : context → tabletype → Set where
  mk-Tabletype-ok : ∀ (C : context) (v-addrtype : addrtype) (v-limits : limits) (v-reftype : reftype) → 
    (Limits-ok C v-limits (coerce {B = ℕ} ((coerce {B = ℕ} (2 ^ (size (numtype-addrtype v-addrtype)))) – (coerce {B = ℕ} 1)))) →
    (Reftype-ok C v-reftype) →
    Tabletype-ok C (mk-tabletype v-addrtype v-limits v-reftype)

{- Inductive Relations Definition at: ../specification/wasm-3.0/2.1-validation.types.spectec:211.1-211.100 -}
data Externtype-ok : context → externtype → Set where
  Externtype-ok--tag : ∀ (C : context) (v-tagtype : tagtype) → 
    (Tagtype-ok C v-tagtype) →
    Externtype-ok C (externtype-TAG v-tagtype)
  Externtype-ok--global : ∀ (C : context) (v-globaltype : globaltype) → 
    (Globaltype-ok C v-globaltype) →
    Externtype-ok C (externtype-GLOBAL v-globaltype)
  Externtype-ok--mem : ∀ (C : context) (v-memtype : memtype) → 
    (Memtype-ok C v-memtype) →
    Externtype-ok C (externtype-MEM v-memtype)
  Externtype-ok--table : ∀ (C : context) (v-tabletype : tabletype) → 
    (Tabletype-ok C v-tabletype) →
    Externtype-ok C (externtype-TABLE v-tabletype)
  Externtype-ok--func : ∀ (C : context) (v-typeuse : typeuse) (t-1-lst : (List valtype)) (t-2-lst : (List valtype)) → 
    (Typeuse-ok C v-typeuse) →
    (Expand-use v-typeuse C (comptype-FUNC (mk-list t-1-lst) (mk-list t-2-lst))) →
    Externtype-ok C (externtype-FUNC v-typeuse)

{- Inductive Relations Definition at: ../specification/wasm-3.0/2.2-validation.subtyping.spectec:133.1-133.114 -}
data Instrtype-sub : context → instrtype → instrtype → Set where
  mk-Instrtype-sub : ∀ (C : context) (t-11-lst : (List valtype)) (x-1-lst : (List idx)) (t-12-lst : (List valtype)) (t-21-lst : (List valtype)) (x-2-lst : (List idx)) (t-22-lst : (List valtype)) (x-lst : (List idx)) (t-lst : (List valtype)) → 
    (Resulttype-sub C (mk-list t-21-lst) (mk-list t-11-lst)) →
    (Resulttype-sub C (mk-list t-12-lst) (mk-list t-22-lst)) →
    (x-lst ≡ (setminus- localidx x-2-lst x-1-lst)) →
    ((length t-lst) ≡ (length x-lst)) →
    Forall (λ (x : idx) → ((proj-uN-0 32 x) < (length (context-LOCALS C)))) x-lst →
    Forall₂ (λ (t : valtype) (x : idx) → (((context-LOCALS C) [ (proj-uN-0 32 x) ]!) ≡ (mk-localtype SET t))) t-lst x-lst →
    Instrtype-sub C (mk-instrtype (mk-list t-11-lst) x-1-lst (mk-list t-12-lst)) (mk-instrtype (mk-list t-21-lst) x-2-lst (mk-list t-22-lst))

{- Inductive Relations Definition at: ../specification/wasm-3.0/2.2-validation.subtyping.spectec:207.1-207.110 -}
data Limits-sub : context → limits → limits → Set where
  max : ∀ (C : context) (n-1 : n) (m-1 : m) (n-2 : n) (m-2-opt : (Maybe m)) → 
    (n-1 ≥ n-2) →
    Forall (λ (m-2 : ℕ) → (m-1 ≤ m-2)) (fromMaybe m-2-opt) →
    Limits-sub C (mk-limits (mk-uN n-1) (just (mk-uN m-1))) (mk-limits (mk-uN n-2) (mapMaybe (λ (m-2 : ℕ) → (mk-uN m-2)) m-2-opt))
  eps : ∀ (C : context) (n-1 : n) (n-2 : n) → 
    (n-1 ≥ n-2) →
    Limits-sub C (mk-limits (mk-uN n-1) nothing) (mk-limits (mk-uN n-2) nothing)

{- Inductive Relations Definition at: ../specification/wasm-3.0/2.2-validation.subtyping.spectec:208.1-208.111 -}
data Tagtype-sub : context → tagtype → tagtype → Set where
  mk-Tagtype-sub : ∀ (C : context) (deftype-1 : deftype) (deftype-2 : deftype) → 
    (Deftype-sub C deftype-1 deftype-2) →
    (Deftype-sub C deftype-2 deftype-1) →
    Tagtype-sub C (typeuse-deftype deftype-1) (typeuse-deftype deftype-2)

{- Inductive Relations Definition at: ../specification/wasm-3.0/2.2-validation.subtyping.spectec:209.1-209.114 -}
data Globaltype-sub : context → globaltype → globaltype → Set where
  Globaltype-sub--const : ∀ (C : context) (valtype-1 : valtype) (valtype-2 : valtype) → 
    (Valtype-sub C valtype-1 valtype-2) →
    Globaltype-sub C (mk-globaltype nothing valtype-1) (mk-globaltype nothing valtype-2)
  Globaltype-sub--var : ∀ (C : context) (valtype-1 : valtype) (valtype-2 : valtype) → 
    (Valtype-sub C valtype-1 valtype-2) →
    (Valtype-sub C valtype-2 valtype-1) →
    Globaltype-sub C (mk-globaltype (just MUT) valtype-1) (mk-globaltype (just MUT) valtype-2)

{- Inductive Relations Definition at: ../specification/wasm-3.0/2.2-validation.subtyping.spectec:210.1-210.111 -}
data Memtype-sub : context → memtype → memtype → Set where
  mk-Memtype-sub : ∀ (C : context) (v-addrtype : addrtype) (limits-1 : limits) (limits-2 : limits) → 
    (Limits-sub C limits-1 limits-2) →
    Memtype-sub C (PAGE v-addrtype limits-1) (PAGE v-addrtype limits-2)

{- Inductive Relations Definition at: ../specification/wasm-3.0/2.2-validation.subtyping.spectec:211.1-211.113 -}
data Tabletype-sub : context → tabletype → tabletype → Set where
  mk-Tabletype-sub : ∀ (C : context) (v-addrtype : addrtype) (limits-1 : limits) (reftype-1 : reftype) (limits-2 : limits) (reftype-2 : reftype) → 
    (Limits-sub C limits-1 limits-2) →
    (Reftype-sub C reftype-1 reftype-2) →
    (Reftype-sub C reftype-2 reftype-1) →
    Tabletype-sub C (mk-tabletype v-addrtype limits-1 reftype-1) (mk-tabletype v-addrtype limits-2 reftype-2)

{- Inductive Relations Definition at: ../specification/wasm-3.0/2.2-validation.subtyping.spectec:212.1-212.114 -}
data Externtype-sub : context → externtype → externtype → Set where
  Externtype-sub--tag : ∀ (C : context) (tagtype-1 : tagtype) (tagtype-2 : tagtype) → 
    (Tagtype-sub C tagtype-1 tagtype-2) →
    Externtype-sub C (externtype-TAG tagtype-1) (externtype-TAG tagtype-2)
  Externtype-sub--global : ∀ (C : context) (globaltype-1 : globaltype) (globaltype-2 : globaltype) → 
    (Globaltype-sub C globaltype-1 globaltype-2) →
    Externtype-sub C (externtype-GLOBAL globaltype-1) (externtype-GLOBAL globaltype-2)
  Externtype-sub--mem : ∀ (C : context) (memtype-1 : memtype) (memtype-2 : memtype) → 
    (Memtype-sub C memtype-1 memtype-2) →
    Externtype-sub C (externtype-MEM memtype-1) (externtype-MEM memtype-2)
  Externtype-sub--table : ∀ (C : context) (tabletype-1 : tabletype) (tabletype-2 : tabletype) → 
    (Tabletype-sub C tabletype-1 tabletype-2) →
    Externtype-sub C (externtype-TABLE tabletype-1) (externtype-TABLE tabletype-2)
  Externtype-sub--func : ∀ (C : context) (deftype-1 : deftype) (deftype-2 : deftype) → 
    (Deftype-sub C deftype-1 deftype-2) →
    Externtype-sub C (externtype-FUNC (typeuse-deftype deftype-1)) (externtype-FUNC (typeuse-deftype deftype-2))

{- Inductive Relations Definition at: ../specification/wasm-3.0/2.3-validation.instructions.spectec:42.1-42.121 -}
data Blocktype-ok : context → blocktype → instrtype → Set where
  Blocktype-ok--valtype : ∀ (C : context) (valtype-opt : (Maybe valtype)) → 
    Forall (λ (v-valtype : valtype) → (Valtype-ok C v-valtype)) (fromMaybe valtype-opt) →
    Blocktype-ok C (-RESULT valtype-opt) (mk-instrtype (mk-list []) [] (mk-list (fromMaybe valtype-opt)))
  Blocktype-ok--typeidx : ∀ (C : context) (v-typeidx : typeidx) (t-1-lst : (List valtype)) (t-2-lst : (List valtype)) → 
    ((proj-uN-0 32 v-typeidx) < (length (context-TYPES C))) →
    (Expand ((context-TYPES C) [ (proj-uN-0 32 v-typeidx) ]!) (comptype-FUNC (mk-list t-1-lst) (mk-list t-2-lst))) →
    Blocktype-ok C (blocktype--IDX v-typeidx) (mk-instrtype (mk-list t-1-lst) [] (mk-list t-2-lst))

{- Inductive Relations Definition at: ../specification/wasm-3.0/2.3-validation.instructions.spectec:164.1-164.77 -}
data Catch-ok : context → catch → Set where
  Catch-ok--catch : ∀ (C : context) (x : idx) (l : labelidx) (t-lst : (List valtype)) → 
    ((as-deftype ((context-TAGS C) [ (proj-uN-0 32 x) ]!)) ≢ nothing) →
    ((proj-uN-0 32 x) < (length (context-TAGS C))) →
    (Expand (unwrap! (as-deftype ((context-TAGS C) [ (proj-uN-0 32 x) ]!))) (comptype-FUNC (mk-list t-lst) (mk-list []))) →
    ((proj-uN-0 32 l) < (length (context-LABELS C))) →
    (Resulttype-sub C (mk-list t-lst) ((context-LABELS C) [ (proj-uN-0 32 l) ]!)) →
    Catch-ok C (CATCH x l)
  catch-ref : ∀ (C : context) (x : idx) (l : labelidx) (t-lst : (List valtype)) → 
    ((as-deftype ((context-TAGS C) [ (proj-uN-0 32 x) ]!)) ≢ nothing) →
    ((proj-uN-0 32 x) < (length (context-TAGS C))) →
    (Expand (unwrap! (as-deftype ((context-TAGS C) [ (proj-uN-0 32 x) ]!))) (comptype-FUNC (mk-list t-lst) (mk-list []))) →
    ((proj-uN-0 32 l) < (length (context-LABELS C))) →
    (Resulttype-sub C (mk-list (t-lst ++ (as (List valtype) ((REF nothing heaptype-EXN) ∷ [])))) ((context-LABELS C) [ (proj-uN-0 32 l) ]!)) →
    Catch-ok C (CATCH-REF x l)
  catch-all : ∀ (C : context) (l : labelidx) → 
    ((proj-uN-0 32 l) < (length (context-LABELS C))) →
    (Resulttype-sub C (mk-list []) ((context-LABELS C) [ (proj-uN-0 32 l) ]!)) →
    Catch-ok C (CATCH-ALL l)
  catch-all-ref : ∀ (C : context) (l : labelidx) → 
    ((proj-uN-0 32 l) < (length (context-LABELS C))) →
    (Resulttype-sub C (mk-list (as (List valtype) ((REF nothing heaptype-EXN) ∷ []))) ((context-LABELS C) [ (proj-uN-0 32 l) ]!)) →
    Catch-ok C (CATCH-ALL-REF l)

{- Auxiliary Definition at: ../specification/wasm-3.0/4.1-execution.values.spectec:7.1-7.44 -}
{-# TERMINATING #-}
default- : (v-valtype : valtype) → (Maybe (Maybe val))
default- valtype-I32 = (just (just (CONST (numtype-addrtype I32) (mk-uN 0))))
default- valtype-I64 = (just (just (CONST (numtype-addrtype I64) (mk-uN 0))))
default- valtype-F32 = (just (just (CONST (numtype-Fnn Fnn-F32) (fzero (size (numtype-Fnn Fnn-F32))))))
default- valtype-F64 = (just (just (CONST (numtype-Fnn Fnn-F64) (fzero (size (numtype-Fnn Fnn-F64))))))
default- valtype-V128 = (just (just (VCONST V128 (mk-uN 0))))
default- (REF (just NULL) ht) = (just (just val-REF-NULL-ADDR))
default- (REF nothing ht) = (just nothing)
default- x0 = nothing

{- Inductive Relations Definition at: ../specification/wasm-3.0/2.3-validation.instructions.spectec:9.1-10.71 -}
data Defaultable : valtype → Set where
  mk-Defaultable : ∀ (t : valtype) (o0 : (Maybe val)) → 
    ((default- t) ≡ (just o0)) →
    (o0 ≢ nothing) →
    Defaultable t

{- Inductive Relations Definition at: ../specification/wasm-3.0/2.3-validation.instructions.spectec:408.1-408.131 -}
data Memarg-ok : memarg → addrtype → N → Set where
  mk-Memarg-ok : ∀ (v-n : n) (v-m : m) (at : addrtype) (v-N : N) → 
    ((coerce {B = ℕ} (2 ^ v-n)) ≤ ((coerce {B = ℕ} v-N) / (coerce {B = ℕ} 8))) →
    (v-m < (2 ^ (size (numtype-addrtype at)))) →
    Memarg-ok record { ALIGN = (mk-uN v-n) ; OFFSET = (mk-uN v-m) } at v-N

{- Auxiliary Definition at: ../specification/wasm-3.0/2.3-validation.instructions.spectec:255.1-255.111 -}
{-# TERMINATING #-}
is-packtype : (v-storagetype : storagetype) → Bool
is-packtype zt = (zt ≠? (storagetype-valtype (unpack zt)))

mutual
  {- Inductive Relations Definition at: ../specification/wasm-3.0/2.3-validation.instructions.spectec:5.1-5.95 -}
  data Instr-ok : context → instr → instrtype → Set where
    nop : ∀ (C : context) → Instr-ok C NOP (mk-instrtype (mk-list []) [] (mk-list []))
    unreachable : ∀ (C : context) (t-1-lst : (List valtype)) (t-2-lst : (List valtype)) → 
      (Instrtype-ok C (mk-instrtype (mk-list t-1-lst) [] (mk-list t-2-lst))) →
      Instr-ok C UNREACHABLE (mk-instrtype (mk-list t-1-lst) [] (mk-list t-2-lst))
    drop' : ∀ (C : context) (t : valtype) → 
      (Valtype-ok C t) →
      Instr-ok C DROP (mk-instrtype (mk-list (t ∷ [])) [] (mk-list []))
    select-expl : ∀ (C : context) (t : valtype) → 
      (Valtype-ok C t) →
      Instr-ok C (SELECT (just (t ∷ []))) (mk-instrtype (mk-list (as (List valtype) (t ∷ t ∷ valtype-I32 ∷ []))) [] (mk-list (t ∷ [])))
    select-impl : ∀ (C : context) (t : valtype) (t' : valtype) (v-numtype : numtype) (v-vectype : vectype) → 
      (Valtype-ok C t) →
      (Valtype-sub C t t') →
      ((t' ≡ (valtype-numtype v-numtype)) ⊎ (t' ≡ (valtype-vectype v-vectype))) →
      Instr-ok C (SELECT nothing) (mk-instrtype (mk-list (as (List valtype) (t ∷ t ∷ valtype-I32 ∷ []))) [] (mk-list (t ∷ [])))
    block : ∀ (C : context) (bt : blocktype) (instr-lst : (List instr)) (t-1-lst : (List valtype)) (t-2-lst : (List valtype)) (x-lst : (List idx)) → 
      (Blocktype-ok C bt (mk-instrtype (mk-list t-1-lst) [] (mk-list t-2-lst))) →
      (Instrs-ok (record { context-TYPES = [] ; context-TAGS = [] ; context-GLOBALS = [] ; context-MEMS = [] ; context-TABLES = [] ; context-FUNCS = [] ; context-DATAS = [] ; context-ELEMS = [] ; context-LOCALS = [] ; context-LABELS = (as (List resulttype) ((mk-list t-2-lst) ∷ [])) ; context-RETURN = nothing ; REFS = [] ; RECS = [] } ⧺ C) instr-lst (mk-instrtype (mk-list t-1-lst) x-lst (mk-list t-2-lst))) →
      Instr-ok C (BLOCK bt instr-lst) (mk-instrtype (mk-list t-1-lst) [] (mk-list t-2-lst))
    loop : ∀ (C : context) (bt : blocktype) (instr-lst : (List instr)) (t-1-lst : (List valtype)) (t-2-lst : (List valtype)) (x-lst : (List idx)) → 
      (Blocktype-ok C bt (mk-instrtype (mk-list t-1-lst) [] (mk-list t-2-lst))) →
      (Instrs-ok (record { context-TYPES = [] ; context-TAGS = [] ; context-GLOBALS = [] ; context-MEMS = [] ; context-TABLES = [] ; context-FUNCS = [] ; context-DATAS = [] ; context-ELEMS = [] ; context-LOCALS = [] ; context-LABELS = (as (List resulttype) ((mk-list t-1-lst) ∷ [])) ; context-RETURN = nothing ; REFS = [] ; RECS = [] } ⧺ C) instr-lst (mk-instrtype (mk-list t-1-lst) x-lst (mk-list t-2-lst))) →
      Instr-ok C (LOOP bt instr-lst) (mk-instrtype (mk-list t-1-lst) [] (mk-list t-2-lst))
    if' : ∀ (C : context) (bt : blocktype) (instr-1-lst : (List instr)) (instr-2-lst : (List instr)) (t-1-lst : (List valtype)) (t-2-lst : (List valtype)) (x-1-lst : (List idx)) (x-2-lst : (List idx)) → 
      (Blocktype-ok C bt (mk-instrtype (mk-list t-1-lst) [] (mk-list t-2-lst))) →
      (Instrs-ok (record { context-TYPES = [] ; context-TAGS = [] ; context-GLOBALS = [] ; context-MEMS = [] ; context-TABLES = [] ; context-FUNCS = [] ; context-DATAS = [] ; context-ELEMS = [] ; context-LOCALS = [] ; context-LABELS = (as (List resulttype) ((mk-list t-2-lst) ∷ [])) ; context-RETURN = nothing ; REFS = [] ; RECS = [] } ⧺ C) instr-1-lst (mk-instrtype (mk-list t-1-lst) x-1-lst (mk-list t-2-lst))) →
      (Instrs-ok (record { context-TYPES = [] ; context-TAGS = [] ; context-GLOBALS = [] ; context-MEMS = [] ; context-TABLES = [] ; context-FUNCS = [] ; context-DATAS = [] ; context-ELEMS = [] ; context-LOCALS = [] ; context-LABELS = (as (List resulttype) ((mk-list t-2-lst) ∷ [])) ; context-RETURN = nothing ; REFS = [] ; RECS = [] } ⧺ C) instr-2-lst (mk-instrtype (mk-list t-1-lst) x-2-lst (mk-list t-2-lst))) →
      Instr-ok C (IFELSE bt instr-1-lst instr-2-lst) (mk-instrtype (mk-list (t-1-lst ++ (as (List valtype) (valtype-I32 ∷ [])))) [] (mk-list t-2-lst))
    br : ∀ (C : context) (l : labelidx) (t-1-lst : (List valtype)) (t-lst : (List valtype)) (t-2-lst : (List valtype)) → 
      ((proj-uN-0 32 l) < (length (context-LABELS C))) →
      ((proj-list-0 valtype ((context-LABELS C) [ (proj-uN-0 32 l) ]!)) ≡ t-lst) →
      (Instrtype-ok C (mk-instrtype (mk-list t-1-lst) [] (mk-list t-2-lst))) →
      Instr-ok C (BR l) (mk-instrtype (mk-list (t-1-lst ++ t-lst)) [] (mk-list t-2-lst))
    br-if : ∀ (C : context) (l : labelidx) (t-lst : (List valtype)) → 
      ((proj-uN-0 32 l) < (length (context-LABELS C))) →
      ((proj-list-0 valtype ((context-LABELS C) [ (proj-uN-0 32 l) ]!)) ≡ t-lst) →
      Instr-ok C (BR-IF l) (mk-instrtype (mk-list (t-lst ++ (as (List valtype) (valtype-I32 ∷ [])))) [] (mk-list t-lst))
    br-table : ∀ (C : context) (l-lst : (List labelidx)) (l' : labelidx) (t-1-lst : (List valtype)) (t-lst : (List valtype)) (t-2-lst : (List valtype)) → 
      Forall (λ (l : labelidx) → ((proj-uN-0 32 l) < (length (context-LABELS C)))) l-lst →
      Forall (λ (l : labelidx) → (Resulttype-sub C (mk-list t-lst) ((context-LABELS C) [ (proj-uN-0 32 l) ]!))) l-lst →
      ((proj-uN-0 32 l') < (length (context-LABELS C))) →
      (Resulttype-sub C (mk-list t-lst) ((context-LABELS C) [ (proj-uN-0 32 l') ]!)) →
      (Instrtype-ok C (mk-instrtype (mk-list (t-1-lst ++ (t-lst ++ (as (List valtype) (valtype-I32 ∷ []))))) [] (mk-list t-2-lst))) →
      Instr-ok C (BR-TABLE l-lst l') (mk-instrtype (mk-list (t-1-lst ++ (t-lst ++ (as (List valtype) (valtype-I32 ∷ []))))) [] (mk-list t-2-lst))
    br-on-null : ∀ (C : context) (l : labelidx) (t-lst : (List valtype)) (ht : heaptype) → 
      ((proj-uN-0 32 l) < (length (context-LABELS C))) →
      ((proj-list-0 valtype ((context-LABELS C) [ (proj-uN-0 32 l) ]!)) ≡ t-lst) →
      (Heaptype-ok C ht) →
      Instr-ok C (BR-ON-NULL l) (mk-instrtype (mk-list (t-lst ++ (as (List valtype) ((REF (just NULL) ht) ∷ [])))) [] (mk-list (t-lst ++ (as (List valtype) ((REF nothing ht) ∷ [])))))
    br-on-non-null : ∀ (C : context) (l : labelidx) (t-lst : (List valtype)) (ht : heaptype) → 
      ((proj-uN-0 32 l) < (length (context-LABELS C))) →
      (((context-LABELS C) [ (proj-uN-0 32 l) ]!) ≡ (mk-list (t-lst ++ (as (List valtype) ((REF (just NULL) ht) ∷ []))))) →
      Instr-ok C (BR-ON-NON-NULL l) (mk-instrtype (mk-list (t-lst ++ (as (List valtype) ((REF (just NULL) ht) ∷ [])))) [] (mk-list t-lst))
    br-on-cast : ∀ (C : context) (l : labelidx) (rt-1 : reftype) (rt-2 : reftype) (t-lst : (List valtype)) (rt : reftype) → 
      ((proj-uN-0 32 l) < (length (context-LABELS C))) →
      (((context-LABELS C) [ (proj-uN-0 32 l) ]!) ≡ (mk-list (t-lst ++ ((valtype-reftype rt) ∷ [])))) →
      (Reftype-ok C rt-1) →
      (Reftype-ok C rt-2) →
      (Reftype-sub C rt-2 rt-1) →
      (Reftype-sub C rt-2 rt) →
      Instr-ok C (BR-ON-CAST l rt-1 rt-2) (mk-instrtype (mk-list (t-lst ++ ((valtype-reftype rt-1) ∷ []))) [] (mk-list (t-lst ++ ((valtype-reftype (diffrt rt-1 rt-2)) ∷ []))))
    br-on-cast-fail : ∀ (C : context) (l : labelidx) (rt-1 : reftype) (rt-2 : reftype) (t-lst : (List valtype)) (rt : reftype) → 
      ((proj-uN-0 32 l) < (length (context-LABELS C))) →
      (((context-LABELS C) [ (proj-uN-0 32 l) ]!) ≡ (mk-list (t-lst ++ ((valtype-reftype rt) ∷ [])))) →
      (Reftype-ok C rt-1) →
      (Reftype-ok C rt-2) →
      (Reftype-sub C rt-2 rt-1) →
      (Reftype-sub C (diffrt rt-1 rt-2) rt) →
      Instr-ok C (BR-ON-CAST-FAIL l rt-1 rt-2) (mk-instrtype (mk-list (t-lst ++ ((valtype-reftype rt-1) ∷ []))) [] (mk-list (t-lst ++ ((valtype-reftype rt-2) ∷ []))))
    call : ∀ (C : context) (x : idx) (t-1-lst : (List valtype)) (t-2-lst : (List valtype)) → 
      ((proj-uN-0 32 x) < (length (context-FUNCS C))) →
      (Expand ((context-FUNCS C) [ (proj-uN-0 32 x) ]!) (comptype-FUNC (mk-list t-1-lst) (mk-list t-2-lst))) →
      Instr-ok C (CALL x) (mk-instrtype (mk-list t-1-lst) [] (mk-list t-2-lst))
    call-ref : ∀ (C : context) (x : idx) (t-1-lst : (List valtype)) (t-2-lst : (List valtype)) → 
      ((proj-uN-0 32 x) < (length (context-TYPES C))) →
      (Expand ((context-TYPES C) [ (proj-uN-0 32 x) ]!) (comptype-FUNC (mk-list t-1-lst) (mk-list t-2-lst))) →
      Instr-ok C (CALL-REF (-IDX x)) (mk-instrtype (mk-list (t-1-lst ++ (as (List valtype) ((REF (just NULL) (heaptype--IDX x)) ∷ [])))) [] (mk-list t-2-lst))
    call-indirect : ∀ (C : context) (x : idx) (y : idx) (t-1-lst : (List valtype)) (at : addrtype) (t-2-lst : (List valtype)) (lim : limits) (rt : reftype) → 
      ((proj-uN-0 32 x) < (length (context-TABLES C))) →
      (((context-TABLES C) [ (proj-uN-0 32 x) ]!) ≡ (mk-tabletype at lim rt)) →
      (Reftype-sub C rt (reftype-REF (just NULL) heaptype-FUNC)) →
      ((proj-uN-0 32 y) < (length (context-TYPES C))) →
      (Expand ((context-TYPES C) [ (proj-uN-0 32 y) ]!) (comptype-FUNC (mk-list t-1-lst) (mk-list t-2-lst))) →
      Instr-ok C (CALL-INDIRECT x (-IDX y)) (mk-instrtype (mk-list (t-1-lst ++ ((valtype-addrtype at) ∷ []))) [] (mk-list t-2-lst))
    return : ∀ (C : context) (t-1-lst : (List valtype)) (t-lst : (List valtype)) (t-2-lst : (List valtype)) → 
      ((context-RETURN C) ≡ (just (mk-list t-lst))) →
      (Instrtype-ok C (mk-instrtype (mk-list t-1-lst) [] (mk-list t-2-lst))) →
      Instr-ok C RETURN (mk-instrtype (mk-list (t-1-lst ++ t-lst)) [] (mk-list t-2-lst))
    return-call : ∀ (C : context) (x : idx) (t-3-lst : (List valtype)) (t-1-lst : (List valtype)) (t-4-lst : (List valtype)) (t-2-lst : (List valtype)) (t'-2-lst : (List valtype)) → 
      ((proj-uN-0 32 x) < (length (context-FUNCS C))) →
      (Expand ((context-FUNCS C) [ (proj-uN-0 32 x) ]!) (comptype-FUNC (mk-list t-1-lst) (mk-list t-2-lst))) →
      ((context-RETURN C) ≡ (just (mk-list t'-2-lst))) →
      (Resulttype-sub C (mk-list t-2-lst) (mk-list t'-2-lst)) →
      (Instrtype-ok C (mk-instrtype (mk-list t-3-lst) [] (mk-list t-4-lst))) →
      Instr-ok C (RETURN-CALL x) (mk-instrtype (mk-list (t-3-lst ++ t-1-lst)) [] (mk-list t-4-lst))
    return-call-ref : ∀ (C : context) (x : idx) (t-3-lst : (List valtype)) (t-1-lst : (List valtype)) (t-4-lst : (List valtype)) (t-2-lst : (List valtype)) (t'-2-lst : (List valtype)) → 
      ((proj-uN-0 32 x) < (length (context-TYPES C))) →
      (Expand ((context-TYPES C) [ (proj-uN-0 32 x) ]!) (comptype-FUNC (mk-list t-1-lst) (mk-list t-2-lst))) →
      ((context-RETURN C) ≡ (just (mk-list t'-2-lst))) →
      (Resulttype-sub C (mk-list t-2-lst) (mk-list t'-2-lst)) →
      (Instrtype-ok C (mk-instrtype (mk-list t-3-lst) [] (mk-list t-4-lst))) →
      Instr-ok C (RETURN-CALL-REF (-IDX x)) (mk-instrtype (mk-list (t-3-lst ++ (t-1-lst ++ (as (List valtype) ((REF (just NULL) (heaptype--IDX x)) ∷ []))))) [] (mk-list t-4-lst))
    return-call-indirect : ∀ (C : context) (x : idx) (y : idx) (t-3-lst : (List valtype)) (t-1-lst : (List valtype)) (at : addrtype) (t-4-lst : (List valtype)) (lim : limits) (rt : reftype) (t-2-lst : (List valtype)) (t'-2-lst : (List valtype)) → 
      ((proj-uN-0 32 x) < (length (context-TABLES C))) →
      (((context-TABLES C) [ (proj-uN-0 32 x) ]!) ≡ (mk-tabletype at lim rt)) →
      (Reftype-sub C rt (reftype-REF (just NULL) heaptype-FUNC)) →
      ((proj-uN-0 32 y) < (length (context-TYPES C))) →
      (Expand ((context-TYPES C) [ (proj-uN-0 32 y) ]!) (comptype-FUNC (mk-list t-1-lst) (mk-list t-2-lst))) →
      ((context-RETURN C) ≡ (just (mk-list t'-2-lst))) →
      (Resulttype-sub C (mk-list t-2-lst) (mk-list t'-2-lst)) →
      (Instrtype-ok C (mk-instrtype (mk-list t-3-lst) [] (mk-list t-4-lst))) →
      Instr-ok C (RETURN-CALL-INDIRECT x (-IDX y)) (mk-instrtype (mk-list (t-3-lst ++ (t-1-lst ++ ((valtype-addrtype at) ∷ [])))) [] (mk-list t-4-lst))
    throw : ∀ (C : context) (x : idx) (t-1-lst : (List valtype)) (t-lst : (List valtype)) (t-2-lst : (List valtype)) → 
      ((as-deftype ((context-TAGS C) [ (proj-uN-0 32 x) ]!)) ≢ nothing) →
      ((proj-uN-0 32 x) < (length (context-TAGS C))) →
      (Expand (unwrap! (as-deftype ((context-TAGS C) [ (proj-uN-0 32 x) ]!))) (comptype-FUNC (mk-list t-lst) (mk-list []))) →
      (Instrtype-ok C (mk-instrtype (mk-list t-1-lst) [] (mk-list t-2-lst))) →
      Instr-ok C (THROW x) (mk-instrtype (mk-list (t-1-lst ++ t-lst)) [] (mk-list t-2-lst))
    throw-ref : ∀ (C : context) (t-1-lst : (List valtype)) (t-2-lst : (List valtype)) → 
      (Instrtype-ok C (mk-instrtype (mk-list t-1-lst) [] (mk-list t-2-lst))) →
      Instr-ok C THROW-REF (mk-instrtype (mk-list (t-1-lst ++ (as (List valtype) ((REF (just NULL) heaptype-EXN) ∷ [])))) [] (mk-list t-2-lst))
    try-table : ∀ (C : context) (bt : blocktype) (catch-lst : (List catch)) (instr-lst : (List instr)) (t-1-lst : (List valtype)) (t-2-lst : (List valtype)) (x-lst : (List idx)) → 
      (Blocktype-ok C bt (mk-instrtype (mk-list t-1-lst) [] (mk-list t-2-lst))) →
      (Instrs-ok (record { context-TYPES = [] ; context-TAGS = [] ; context-GLOBALS = [] ; context-MEMS = [] ; context-TABLES = [] ; context-FUNCS = [] ; context-DATAS = [] ; context-ELEMS = [] ; context-LOCALS = [] ; context-LABELS = (as (List resulttype) ((mk-list t-2-lst) ∷ [])) ; context-RETURN = nothing ; REFS = [] ; RECS = [] } ⧺ C) instr-lst (mk-instrtype (mk-list t-1-lst) x-lst (mk-list t-2-lst))) →
      Forall (λ (v-catch : catch) → (Catch-ok C v-catch)) catch-lst →
      Instr-ok C (TRY-TABLE bt (mk-list catch-lst) instr-lst) (mk-instrtype (mk-list t-1-lst) [] (mk-list t-2-lst))
    ref-null : ∀ (C : context) (ht : heaptype) → 
      (Heaptype-ok C ht) →
      Instr-ok C (REF-NULL ht) (mk-instrtype (mk-list []) [] (mk-list (as (List valtype) ((REF (just NULL) ht) ∷ []))))
    ref-func : ∀ (C : context) (x : idx) (dt : deftype) → 
      ((proj-uN-0 32 x) < (length (context-FUNCS C))) →
      (((context-FUNCS C) [ (proj-uN-0 32 x) ]!) ≡ dt) →
      ((length (REFS C)) > 0) →
      (x ∈ (REFS C)) →
      Instr-ok C (REF-FUNC x) (mk-instrtype (mk-list []) [] (mk-list (as (List valtype) ((REF nothing (heaptype-deftype dt)) ∷ []))))
    ref-i31 : ∀ (C : context) → Instr-ok C REF-I31 (mk-instrtype (mk-list (as (List valtype) (valtype-I32 ∷ []))) [] (mk-list (as (List valtype) ((REF nothing heaptype-I31) ∷ []))))
    ref-is-null : ∀ (C : context) (ht : heaptype) → 
      (Heaptype-ok C ht) →
      Instr-ok C REF-IS-NULL (mk-instrtype (mk-list (as (List valtype) ((REF (just NULL) ht) ∷ []))) [] (mk-list (as (List valtype) (valtype-I32 ∷ []))))
    ref-as-non-null : ∀ (C : context) (ht : heaptype) → 
      (Heaptype-ok C ht) →
      Instr-ok C REF-AS-NON-NULL (mk-instrtype (mk-list (as (List valtype) ((REF (just NULL) ht) ∷ []))) [] (mk-list (as (List valtype) ((REF nothing ht) ∷ []))))
    ref-eq : ∀ (C : context) → Instr-ok C REF-EQ (mk-instrtype (mk-list (as (List valtype) ((REF (just NULL) heaptype-EQ) ∷ (REF (just NULL) heaptype-EQ) ∷ []))) [] (mk-list (as (List valtype) (valtype-I32 ∷ []))))
    ref-test : ∀ (C : context) (rt : reftype) (rt' : reftype) → 
      (Reftype-ok C rt) →
      (Reftype-ok C rt') →
      (Reftype-sub C rt rt') →
      Instr-ok C (REF-TEST rt) (mk-instrtype (mk-list ((valtype-reftype rt') ∷ [])) [] (mk-list (as (List valtype) (valtype-I32 ∷ []))))
    ref-cast : ∀ (C : context) (rt : reftype) (rt' : reftype) → 
      (Reftype-ok C rt) →
      (Reftype-ok C rt') →
      (Reftype-sub C rt rt') →
      Instr-ok C (REF-CAST rt) (mk-instrtype (mk-list ((valtype-reftype rt') ∷ [])) [] (mk-list ((valtype-reftype rt) ∷ [])))
    i31-get : ∀ (C : context) (v-sx : sx) → Instr-ok C (I31-GET v-sx) (mk-instrtype (mk-list (as (List valtype) ((REF (just NULL) heaptype-I31) ∷ []))) [] (mk-list (as (List valtype) (valtype-I32 ∷ []))))
    struct-new : ∀ (C : context) (x : idx) (zt-lst : (List storagetype)) (mut-opt-lst : (List (Maybe mut))) → 
      ((proj-uN-0 32 x) < (length (context-TYPES C))) →
      (Expand ((context-TYPES C) [ (proj-uN-0 32 x) ]!) (comptype-STRUCT (mk-list (zipWith (λ (mut-opt : (Maybe mut)) (zt : storagetype) → (mk-fieldtype mut-opt zt)) mut-opt-lst zt-lst)))) →
      Instr-ok C (STRUCT-NEW x) (mk-instrtype (mk-list (map (λ (zt : storagetype) → (unpack zt)) zt-lst)) [] (mk-list (as (List valtype) ((REF nothing (heaptype--IDX x)) ∷ []))))
    struct-new-default : ∀ (C : context) (x : idx) (mut-opt-lst : (List (Maybe mut))) (zt-lst : (List storagetype)) → 
      ((proj-uN-0 32 x) < (length (context-TYPES C))) →
      (Expand ((context-TYPES C) [ (proj-uN-0 32 x) ]!) (comptype-STRUCT (mk-list (zipWith (λ (mut-opt : (Maybe mut)) (zt : storagetype) → (mk-fieldtype mut-opt zt)) mut-opt-lst zt-lst)))) →
      Forall (λ (zt : storagetype) → (Defaultable (unpack zt))) zt-lst →
      Instr-ok C (STRUCT-NEW-DEFAULT x) (mk-instrtype (mk-list []) [] (mk-list (as (List valtype) ((REF nothing (heaptype--IDX x)) ∷ []))))
    struct-get : ∀ (C : context) (sx-opt : (Maybe sx)) (x : idx) (i : fieldidx) (zt : storagetype) (ft-lst : (List fieldtype)) (mut-opt : (Maybe mut)) → 
      ((proj-uN-0 32 x) < (length (context-TYPES C))) →
      (Expand ((context-TYPES C) [ (proj-uN-0 32 x) ]!) (comptype-STRUCT (mk-list ft-lst))) →
      ((proj-uN-0 32 i) < (length ft-lst)) →
      ((ft-lst [ (proj-uN-0 32 i) ]!) ≡ (mk-fieldtype mut-opt zt)) →
      (((sx-opt ≢ nothing) → (is-true (is-packtype zt))) × ((is-true (is-packtype zt)) → (sx-opt ≢ nothing))) →
      Instr-ok C (STRUCT-GET sx-opt x i) (mk-instrtype (mk-list (as (List valtype) ((REF (just NULL) (heaptype--IDX x)) ∷ []))) [] (mk-list ((unpack zt) ∷ [])))
    struct-set : ∀ (C : context) (x : idx) (i : fieldidx) (zt : storagetype) (ft-lst : (List fieldtype)) → 
      ((proj-uN-0 32 x) < (length (context-TYPES C))) →
      (Expand ((context-TYPES C) [ (proj-uN-0 32 x) ]!) (comptype-STRUCT (mk-list ft-lst))) →
      ((proj-uN-0 32 i) < (length ft-lst)) →
      ((ft-lst [ (proj-uN-0 32 i) ]!) ≡ (mk-fieldtype (just MUT) zt)) →
      Instr-ok C (STRUCT-SET x i) (mk-instrtype (mk-list (as (List valtype) ((REF (just NULL) (heaptype--IDX x)) ∷ (unpack zt) ∷ []))) [] (mk-list []))
    array-new : ∀ (C : context) (x : idx) (zt : storagetype) (mut-opt : (Maybe mut)) → 
      ((proj-uN-0 32 x) < (length (context-TYPES C))) →
      (Expand ((context-TYPES C) [ (proj-uN-0 32 x) ]!) (comptype-ARRAY (mk-fieldtype mut-opt zt))) →
      Instr-ok C (ARRAY-NEW x) (mk-instrtype (mk-list (as (List valtype) ((unpack zt) ∷ valtype-I32 ∷ []))) [] (mk-list (as (List valtype) ((REF nothing (heaptype--IDX x)) ∷ []))))
    array-new-default : ∀ (C : context) (x : idx) (mut-opt : (Maybe mut)) (zt : storagetype) → 
      ((proj-uN-0 32 x) < (length (context-TYPES C))) →
      (Expand ((context-TYPES C) [ (proj-uN-0 32 x) ]!) (comptype-ARRAY (mk-fieldtype mut-opt zt))) →
      (Defaultable (unpack zt)) →
      Instr-ok C (ARRAY-NEW-DEFAULT x) (mk-instrtype (mk-list (as (List valtype) (valtype-I32 ∷ []))) [] (mk-list (as (List valtype) ((REF nothing (heaptype--IDX x)) ∷ []))))
    array-new-fixed : ∀ (C : context) (x : idx) (v-n : n) (zt : storagetype) (mut-opt : (Maybe mut)) → 
      ((proj-uN-0 32 x) < (length (context-TYPES C))) →
      (Expand ((context-TYPES C) [ (proj-uN-0 32 x) ]!) (comptype-ARRAY (mk-fieldtype mut-opt zt))) →
      Instr-ok C (ARRAY-NEW-FIXED x (mk-uN v-n)) (mk-instrtype (mk-list (replicate v-n (unpack zt))) [] (mk-list (as (List valtype) ((REF nothing (heaptype--IDX x)) ∷ []))))
    array-new-elem : ∀ (C : context) (x : idx) (y : idx) (mut-opt : (Maybe mut)) (rt : reftype) → 
      ((proj-uN-0 32 x) < (length (context-TYPES C))) →
      (Expand ((context-TYPES C) [ (proj-uN-0 32 x) ]!) (comptype-ARRAY (mk-fieldtype mut-opt (storagetype-reftype rt)))) →
      ((proj-uN-0 32 y) < (length (context-ELEMS C))) →
      (Reftype-sub C ((context-ELEMS C) [ (proj-uN-0 32 y) ]!) rt) →
      Instr-ok C (ARRAY-NEW-ELEM x y) (mk-instrtype (mk-list (as (List valtype) (valtype-I32 ∷ valtype-I32 ∷ []))) [] (mk-list (as (List valtype) ((REF nothing (heaptype--IDX x)) ∷ []))))
    array-new-data : ∀ (C : context) (x : idx) (y : idx) (mut-opt : (Maybe mut)) (zt : storagetype) (v-numtype : numtype) (v-vectype : vectype) → 
      ((proj-uN-0 32 x) < (length (context-TYPES C))) →
      (Expand ((context-TYPES C) [ (proj-uN-0 32 x) ]!) (comptype-ARRAY (mk-fieldtype mut-opt zt))) →
      (((unpack zt) ≡ (valtype-numtype v-numtype)) ⊎ ((unpack zt) ≡ (valtype-vectype v-vectype))) →
      ((proj-uN-0 32 y) < (length (context-DATAS C))) →
      (((context-DATAS C) [ (proj-uN-0 32 y) ]!) ≡ OK) →
      Instr-ok C (ARRAY-NEW-DATA x y) (mk-instrtype (mk-list (as (List valtype) (valtype-I32 ∷ valtype-I32 ∷ []))) [] (mk-list (as (List valtype) ((REF nothing (heaptype--IDX x)) ∷ []))))
    array-get : ∀ (C : context) (sx-opt : (Maybe sx)) (x : idx) (zt : storagetype) (mut-opt : (Maybe mut)) → 
      ((proj-uN-0 32 x) < (length (context-TYPES C))) →
      (Expand ((context-TYPES C) [ (proj-uN-0 32 x) ]!) (comptype-ARRAY (mk-fieldtype mut-opt zt))) →
      (((sx-opt ≢ nothing) → (is-true (is-packtype zt))) × ((is-true (is-packtype zt)) → (sx-opt ≢ nothing))) →
      Instr-ok C (ARRAY-GET sx-opt x) (mk-instrtype (mk-list (as (List valtype) ((REF (just NULL) (heaptype--IDX x)) ∷ valtype-I32 ∷ []))) [] (mk-list ((unpack zt) ∷ [])))
    array-set : ∀ (C : context) (x : idx) (zt : storagetype) → 
      ((proj-uN-0 32 x) < (length (context-TYPES C))) →
      (Expand ((context-TYPES C) [ (proj-uN-0 32 x) ]!) (comptype-ARRAY (mk-fieldtype (just MUT) zt))) →
      Instr-ok C (ARRAY-SET x) (mk-instrtype (mk-list (as (List valtype) ((REF (just NULL) (heaptype--IDX x)) ∷ valtype-I32 ∷ (unpack zt) ∷ []))) [] (mk-list []))
    array-len : ∀ (C : context) → Instr-ok C ARRAY-LEN (mk-instrtype (mk-list (as (List valtype) ((REF (just NULL) heaptype-ARRAY) ∷ []))) [] (mk-list (as (List valtype) (valtype-I32 ∷ []))))
    array-fill : ∀ (C : context) (x : idx) (zt : storagetype) → 
      ((proj-uN-0 32 x) < (length (context-TYPES C))) →
      (Expand ((context-TYPES C) [ (proj-uN-0 32 x) ]!) (comptype-ARRAY (mk-fieldtype (just MUT) zt))) →
      Instr-ok C (ARRAY-FILL x) (mk-instrtype (mk-list (as (List valtype) ((REF (just NULL) (heaptype--IDX x)) ∷ valtype-I32 ∷ (unpack zt) ∷ valtype-I32 ∷ []))) [] (mk-list []))
    array-copy : ∀ (C : context) (x-1 : idx) (x-2 : idx) (zt-1 : storagetype) (mut-opt : (Maybe mut)) (zt-2 : storagetype) → 
      ((proj-uN-0 32 x-1) < (length (context-TYPES C))) →
      (Expand ((context-TYPES C) [ (proj-uN-0 32 x-1) ]!) (comptype-ARRAY (mk-fieldtype (just MUT) zt-1))) →
      ((proj-uN-0 32 x-2) < (length (context-TYPES C))) →
      (Expand ((context-TYPES C) [ (proj-uN-0 32 x-2) ]!) (comptype-ARRAY (mk-fieldtype mut-opt zt-2))) →
      (Storagetype-sub C zt-2 zt-1) →
      Instr-ok C (ARRAY-COPY x-1 x-2) (mk-instrtype (mk-list (as (List valtype) ((REF (just NULL) (heaptype--IDX x-1)) ∷ valtype-I32 ∷ (REF (just NULL) (heaptype--IDX x-2)) ∷ valtype-I32 ∷ valtype-I32 ∷ []))) [] (mk-list []))
    array-init-elem : ∀ (C : context) (x : idx) (y : idx) (zt : storagetype) → 
      ((proj-uN-0 32 x) < (length (context-TYPES C))) →
      (Expand ((context-TYPES C) [ (proj-uN-0 32 x) ]!) (comptype-ARRAY (mk-fieldtype (just MUT) zt))) →
      ((proj-uN-0 32 y) < (length (context-ELEMS C))) →
      (Storagetype-sub C (storagetype-reftype ((context-ELEMS C) [ (proj-uN-0 32 y) ]!)) zt) →
      Instr-ok C (ARRAY-INIT-ELEM x y) (mk-instrtype (mk-list (as (List valtype) ((REF (just NULL) (heaptype--IDX x)) ∷ valtype-I32 ∷ valtype-I32 ∷ valtype-I32 ∷ []))) [] (mk-list []))
    array-init-data : ∀ (C : context) (x : idx) (y : idx) (zt : storagetype) (v-numtype : numtype) (v-vectype : vectype) → 
      ((proj-uN-0 32 x) < (length (context-TYPES C))) →
      (Expand ((context-TYPES C) [ (proj-uN-0 32 x) ]!) (comptype-ARRAY (mk-fieldtype (just MUT) zt))) →
      (((unpack zt) ≡ (valtype-numtype v-numtype)) ⊎ ((unpack zt) ≡ (valtype-vectype v-vectype))) →
      ((proj-uN-0 32 y) < (length (context-DATAS C))) →
      (((context-DATAS C) [ (proj-uN-0 32 y) ]!) ≡ OK) →
      Instr-ok C (ARRAY-INIT-DATA x y) (mk-instrtype (mk-list (as (List valtype) ((REF (just NULL) (heaptype--IDX x)) ∷ valtype-I32 ∷ valtype-I32 ∷ valtype-I32 ∷ []))) [] (mk-list []))
    extern-convert-any : ∀ (C : context) (null-1-opt : (Maybe null)) (null-2-opt : (Maybe null)) → 
      (null-1-opt ≡ null-2-opt) →
      Instr-ok C EXTERN-CONVERT-ANY (mk-instrtype (mk-list (as (List valtype) ((REF null-1-opt heaptype-ANY) ∷ []))) [] (mk-list (as (List valtype) ((REF null-2-opt heaptype-EXTERN) ∷ []))))
    any-convert-extern : ∀ (C : context) (null-1-opt : (Maybe null)) (null-2-opt : (Maybe null)) → 
      (null-1-opt ≡ null-2-opt) →
      Instr-ok C ANY-CONVERT-EXTERN (mk-instrtype (mk-list (as (List valtype) ((REF null-1-opt heaptype-EXTERN) ∷ []))) [] (mk-list (as (List valtype) ((REF null-2-opt heaptype-ANY) ∷ []))))
    local-get : ∀ (C : context) (x : idx) (t : valtype) → 
      ((proj-uN-0 32 x) < (length (context-LOCALS C))) →
      (((context-LOCALS C) [ (proj-uN-0 32 x) ]!) ≡ (mk-localtype SET t)) →
      Instr-ok C (LOCAL-GET x) (mk-instrtype (mk-list []) [] (mk-list (t ∷ [])))
    local-set : ∀ (C : context) (x : idx) (t : valtype) (v-init : init) → 
      ((proj-uN-0 32 x) < (length (context-LOCALS C))) →
      (((context-LOCALS C) [ (proj-uN-0 32 x) ]!) ≡ (mk-localtype v-init t)) →
      Instr-ok C (LOCAL-SET x) (mk-instrtype (mk-list (t ∷ [])) (x ∷ []) (mk-list []))
    local-tee : ∀ (C : context) (x : idx) (t : valtype) (v-init : init) → 
      ((proj-uN-0 32 x) < (length (context-LOCALS C))) →
      (((context-LOCALS C) [ (proj-uN-0 32 x) ]!) ≡ (mk-localtype v-init t)) →
      Instr-ok C (LOCAL-TEE x) (mk-instrtype (mk-list (t ∷ [])) (x ∷ []) (mk-list (t ∷ [])))
    global-get : ∀ (C : context) (x : idx) (t : valtype) (mut-opt : (Maybe mut)) → 
      ((proj-uN-0 32 x) < (length (context-GLOBALS C))) →
      (((context-GLOBALS C) [ (proj-uN-0 32 x) ]!) ≡ (mk-globaltype mut-opt t)) →
      Instr-ok C (GLOBAL-GET x) (mk-instrtype (mk-list []) [] (mk-list (t ∷ [])))
    global-set : ∀ (C : context) (x : idx) (t : valtype) → 
      ((proj-uN-0 32 x) < (length (context-GLOBALS C))) →
      (((context-GLOBALS C) [ (proj-uN-0 32 x) ]!) ≡ (mk-globaltype (just MUT) t)) →
      Instr-ok C (GLOBAL-SET x) (mk-instrtype (mk-list (t ∷ [])) [] (mk-list []))
    table-get : ∀ (C : context) (x : idx) (at : addrtype) (rt : reftype) (lim : limits) → 
      ((proj-uN-0 32 x) < (length (context-TABLES C))) →
      (((context-TABLES C) [ (proj-uN-0 32 x) ]!) ≡ (mk-tabletype at lim rt)) →
      Instr-ok C (TABLE-GET x) (mk-instrtype (mk-list ((valtype-addrtype at) ∷ [])) [] (mk-list ((valtype-reftype rt) ∷ [])))
    table-set : ∀ (C : context) (x : idx) (at : addrtype) (rt : reftype) (lim : limits) → 
      ((proj-uN-0 32 x) < (length (context-TABLES C))) →
      (((context-TABLES C) [ (proj-uN-0 32 x) ]!) ≡ (mk-tabletype at lim rt)) →
      Instr-ok C (TABLE-SET x) (mk-instrtype (mk-list ((valtype-addrtype at) ∷ (valtype-reftype rt) ∷ [])) [] (mk-list []))
    table-size : ∀ (C : context) (x : idx) (at : addrtype) (lim : limits) (rt : reftype) → 
      ((proj-uN-0 32 x) < (length (context-TABLES C))) →
      (((context-TABLES C) [ (proj-uN-0 32 x) ]!) ≡ (mk-tabletype at lim rt)) →
      Instr-ok C (TABLE-SIZE x) (mk-instrtype (mk-list []) [] (mk-list ((valtype-addrtype at) ∷ [])))
    table-grow : ∀ (C : context) (x : idx) (rt : reftype) (at : addrtype) (lim : limits) → 
      ((proj-uN-0 32 x) < (length (context-TABLES C))) →
      (((context-TABLES C) [ (proj-uN-0 32 x) ]!) ≡ (mk-tabletype at lim rt)) →
      Instr-ok C (TABLE-GROW x) (mk-instrtype (mk-list ((valtype-reftype rt) ∷ (valtype-addrtype at) ∷ [])) [] (mk-list ((valtype-addrtype at) ∷ [])))
    table-fill : ∀ (C : context) (x : idx) (at : addrtype) (rt : reftype) (lim : limits) → 
      ((proj-uN-0 32 x) < (length (context-TABLES C))) →
      (((context-TABLES C) [ (proj-uN-0 32 x) ]!) ≡ (mk-tabletype at lim rt)) →
      Instr-ok C (TABLE-FILL x) (mk-instrtype (mk-list ((valtype-addrtype at) ∷ (valtype-reftype rt) ∷ (valtype-addrtype at) ∷ [])) [] (mk-list []))
    table-copy : ∀ (C : context) (x-1 : idx) (x-2 : idx) (at-1 : addrtype) (at-2 : addrtype) (lim-1 : limits) (rt-1 : reftype) (lim-2 : limits) (rt-2 : reftype) → 
      ((proj-uN-0 32 x-1) < (length (context-TABLES C))) →
      (((context-TABLES C) [ (proj-uN-0 32 x-1) ]!) ≡ (mk-tabletype at-1 lim-1 rt-1)) →
      ((proj-uN-0 32 x-2) < (length (context-TABLES C))) →
      (((context-TABLES C) [ (proj-uN-0 32 x-2) ]!) ≡ (mk-tabletype at-2 lim-2 rt-2)) →
      (Reftype-sub C rt-2 rt-1) →
      Instr-ok C (TABLE-COPY x-1 x-2) (mk-instrtype (mk-list ((valtype-addrtype at-1) ∷ (valtype-addrtype at-2) ∷ (valtype-addrtype (minat at-1 at-2)) ∷ [])) [] (mk-list []))
    table-init : ∀ (C : context) (x : idx) (y : idx) (at : addrtype) (lim : limits) (rt-1 : reftype) (rt-2 : reftype) → 
      ((proj-uN-0 32 x) < (length (context-TABLES C))) →
      (((context-TABLES C) [ (proj-uN-0 32 x) ]!) ≡ (mk-tabletype at lim rt-1)) →
      ((proj-uN-0 32 y) < (length (context-ELEMS C))) →
      (((context-ELEMS C) [ (proj-uN-0 32 y) ]!) ≡ rt-2) →
      (Reftype-sub C rt-2 rt-1) →
      Instr-ok C (TABLE-INIT x y) (mk-instrtype (mk-list (as (List valtype) ((valtype-addrtype at) ∷ valtype-I32 ∷ valtype-I32 ∷ []))) [] (mk-list []))
    elem-drop : ∀ (C : context) (x : idx) (rt : reftype) → 
      ((proj-uN-0 32 x) < (length (context-ELEMS C))) →
      (((context-ELEMS C) [ (proj-uN-0 32 x) ]!) ≡ rt) →
      Instr-ok C (ELEM-DROP x) (mk-instrtype (mk-list []) [] (mk-list []))
    memory-size : ∀ (C : context) (x : idx) (at : addrtype) (lim : limits) → 
      ((proj-uN-0 32 x) < (length (context-MEMS C))) →
      (((context-MEMS C) [ (proj-uN-0 32 x) ]!) ≡ (PAGE at lim)) →
      Instr-ok C (MEMORY-SIZE x) (mk-instrtype (mk-list []) [] (mk-list ((valtype-addrtype at) ∷ [])))
    memory-grow : ∀ (C : context) (x : idx) (at : addrtype) (lim : limits) → 
      ((proj-uN-0 32 x) < (length (context-MEMS C))) →
      (((context-MEMS C) [ (proj-uN-0 32 x) ]!) ≡ (PAGE at lim)) →
      Instr-ok C (MEMORY-GROW x) (mk-instrtype (mk-list ((valtype-addrtype at) ∷ [])) [] (mk-list ((valtype-addrtype at) ∷ [])))
    memory-fill : ∀ (C : context) (x : idx) (at : addrtype) (lim : limits) → 
      ((proj-uN-0 32 x) < (length (context-MEMS C))) →
      (((context-MEMS C) [ (proj-uN-0 32 x) ]!) ≡ (PAGE at lim)) →
      Instr-ok C (MEMORY-FILL x) (mk-instrtype (mk-list (as (List valtype) ((valtype-addrtype at) ∷ valtype-I32 ∷ (valtype-addrtype at) ∷ []))) [] (mk-list []))
    memory-copy : ∀ (C : context) (x-1 : idx) (x-2 : idx) (at-1 : addrtype) (at-2 : addrtype) (lim-1 : limits) (lim-2 : limits) → 
      ((proj-uN-0 32 x-1) < (length (context-MEMS C))) →
      (((context-MEMS C) [ (proj-uN-0 32 x-1) ]!) ≡ (PAGE at-1 lim-1)) →
      ((proj-uN-0 32 x-2) < (length (context-MEMS C))) →
      (((context-MEMS C) [ (proj-uN-0 32 x-2) ]!) ≡ (PAGE at-2 lim-2)) →
      Instr-ok C (MEMORY-COPY x-1 x-2) (mk-instrtype (mk-list ((valtype-addrtype at-1) ∷ (valtype-addrtype at-2) ∷ (valtype-addrtype (minat at-1 at-2)) ∷ [])) [] (mk-list []))
    memory-init : ∀ (C : context) (x : idx) (y : idx) (at : addrtype) (lim : limits) → 
      ((proj-uN-0 32 x) < (length (context-MEMS C))) →
      (((context-MEMS C) [ (proj-uN-0 32 x) ]!) ≡ (PAGE at lim)) →
      ((proj-uN-0 32 y) < (length (context-DATAS C))) →
      (((context-DATAS C) [ (proj-uN-0 32 y) ]!) ≡ OK) →
      Instr-ok C (MEMORY-INIT x y) (mk-instrtype (mk-list (as (List valtype) ((valtype-addrtype at) ∷ valtype-I32 ∷ valtype-I32 ∷ []))) [] (mk-list []))
    data-drop : ∀ (C : context) (x : idx) → 
      ((proj-uN-0 32 x) < (length (context-DATAS C))) →
      (((context-DATAS C) [ (proj-uN-0 32 x) ]!) ≡ OK) →
      Instr-ok C (DATA-DROP x) (mk-instrtype (mk-list []) [] (mk-list []))
    load-val : ∀ (C : context) (nt : numtype) (x : idx) (v-memarg : memarg) (at : addrtype) (lim : limits) → 
      ((proj-uN-0 32 x) < (length (context-MEMS C))) →
      (((context-MEMS C) [ (proj-uN-0 32 x) ]!) ≡ (PAGE at lim)) →
      (Memarg-ok v-memarg at (size nt)) →
      Instr-ok C (LOAD nt nothing x v-memarg) (mk-instrtype (mk-list ((valtype-addrtype at) ∷ [])) [] (mk-list ((valtype-numtype nt) ∷ [])))
    load-pack-0 : ∀ (C : context) (v-M : M) (v-sx : sx) (x : idx) (v-memarg : memarg) (at : addrtype) (lim : limits) → 
      ((proj-uN-0 32 x) < (length (context-MEMS C))) →
      (((context-MEMS C) [ (proj-uN-0 32 x) ]!) ≡ (PAGE at lim)) →
      (Memarg-ok v-memarg at v-M) →
      Instr-ok C (LOAD (numtype-addrtype I32) (just (mk-loadop- (mk-sz v-M) v-sx)) x v-memarg) (mk-instrtype (mk-list ((valtype-addrtype at) ∷ [])) [] (mk-list ((valtype-addrtype I32) ∷ [])))
    load-pack-1 : ∀ (C : context) (v-M : M) (v-sx : sx) (x : idx) (v-memarg : memarg) (at : addrtype) (lim : limits) → 
      ((proj-uN-0 32 x) < (length (context-MEMS C))) →
      (((context-MEMS C) [ (proj-uN-0 32 x) ]!) ≡ (PAGE at lim)) →
      (Memarg-ok v-memarg at v-M) →
      Instr-ok C (LOAD (numtype-addrtype I64) (just (mk-loadop- (mk-sz v-M) v-sx)) x v-memarg) (mk-instrtype (mk-list ((valtype-addrtype at) ∷ [])) [] (mk-list ((valtype-addrtype I64) ∷ [])))
    store-val : ∀ (C : context) (nt : numtype) (x : idx) (v-memarg : memarg) (at : addrtype) (lim : limits) → 
      ((proj-uN-0 32 x) < (length (context-MEMS C))) →
      (((context-MEMS C) [ (proj-uN-0 32 x) ]!) ≡ (PAGE at lim)) →
      (Memarg-ok v-memarg at (size nt)) →
      Instr-ok C (STORE nt nothing x v-memarg) (mk-instrtype (mk-list ((valtype-addrtype at) ∷ (valtype-numtype nt) ∷ [])) [] (mk-list []))
    store-pack-0 : ∀ (C : context) (v-M : M) (x : idx) (v-memarg : memarg) (at : addrtype) (lim : limits) → 
      ((proj-uN-0 32 x) < (length (context-MEMS C))) →
      (((context-MEMS C) [ (proj-uN-0 32 x) ]!) ≡ (PAGE at lim)) →
      (Memarg-ok v-memarg at v-M) →
      Instr-ok C (STORE (numtype-addrtype I32) (just (mk-storeop- (mk-sz v-M))) x v-memarg) (mk-instrtype (mk-list ((valtype-addrtype at) ∷ (valtype-addrtype I32) ∷ [])) [] (mk-list []))
    store-pack-1 : ∀ (C : context) (v-M : M) (x : idx) (v-memarg : memarg) (at : addrtype) (lim : limits) → 
      ((proj-uN-0 32 x) < (length (context-MEMS C))) →
      (((context-MEMS C) [ (proj-uN-0 32 x) ]!) ≡ (PAGE at lim)) →
      (Memarg-ok v-memarg at v-M) →
      Instr-ok C (STORE (numtype-addrtype I64) (just (mk-storeop- (mk-sz v-M))) x v-memarg) (mk-instrtype (mk-list ((valtype-addrtype at) ∷ (valtype-addrtype I64) ∷ [])) [] (mk-list []))
    vload-val : ∀ (C : context) (x : idx) (v-memarg : memarg) (at : addrtype) (lim : limits) → 
      ((proj-uN-0 32 x) < (length (context-MEMS C))) →
      (((context-MEMS C) [ (proj-uN-0 32 x) ]!) ≡ (PAGE at lim)) →
      (Memarg-ok v-memarg at (vsize V128)) →
      Instr-ok C (VLOAD V128 nothing x v-memarg) (mk-instrtype (mk-list ((valtype-addrtype at) ∷ [])) [] (mk-list (as (List valtype) (valtype-V128 ∷ []))))
    vload-pack : ∀ (C : context) (v-M : M) (v-N : N) (v-sx : sx) (x : idx) (v-memarg : memarg) (at : addrtype) (lim : limits) → 
      ((proj-uN-0 32 x) < (length (context-MEMS C))) →
      (((context-MEMS C) [ (proj-uN-0 32 x) ]!) ≡ (PAGE at lim)) →
      (Memarg-ok v-memarg at (v-M * v-N)) →
      Instr-ok C (VLOAD V128 (just (SHAPEX- (mk-sz v-M) v-N v-sx)) x v-memarg) (mk-instrtype (mk-list ((valtype-addrtype at) ∷ [])) [] (mk-list (as (List valtype) (valtype-V128 ∷ []))))
    vload-splat : ∀ (C : context) (v-N : N) (x : idx) (v-memarg : memarg) (at : addrtype) (lim : limits) → 
      ((proj-uN-0 32 x) < (length (context-MEMS C))) →
      (((context-MEMS C) [ (proj-uN-0 32 x) ]!) ≡ (PAGE at lim)) →
      (Memarg-ok v-memarg at v-N) →
      Instr-ok C (VLOAD V128 (just (SPLAT (mk-sz v-N))) x v-memarg) (mk-instrtype (mk-list ((valtype-addrtype at) ∷ [])) [] (mk-list (as (List valtype) (valtype-V128 ∷ []))))
    vload-zero : ∀ (C : context) (v-N : N) (x : idx) (v-memarg : memarg) (at : addrtype) (lim : limits) → 
      ((proj-uN-0 32 x) < (length (context-MEMS C))) →
      (((context-MEMS C) [ (proj-uN-0 32 x) ]!) ≡ (PAGE at lim)) →
      (Memarg-ok v-memarg at v-N) →
      Instr-ok C (VLOAD V128 (just (vloadop--ZERO (mk-sz v-N))) x v-memarg) (mk-instrtype (mk-list ((valtype-addrtype at) ∷ [])) [] (mk-list (as (List valtype) (valtype-V128 ∷ []))))
    vload-lane : ∀ (C : context) (v-N : N) (x : idx) (v-memarg : memarg) (i : laneidx) (at : addrtype) (lim : limits) → 
      ((proj-uN-0 32 x) < (length (context-MEMS C))) →
      (((context-MEMS C) [ (proj-uN-0 32 x) ]!) ≡ (PAGE at lim)) →
      (Memarg-ok v-memarg at v-N) →
      ((coerce {B = ℕ} (proj-uN-0 8 i)) < ((coerce {B = ℕ} 128) / (coerce {B = ℕ} v-N))) →
      Instr-ok C (VLOAD-LANE V128 (mk-sz v-N) x v-memarg i) (mk-instrtype (mk-list (as (List valtype) ((valtype-addrtype at) ∷ valtype-V128 ∷ []))) [] (mk-list (as (List valtype) (valtype-V128 ∷ []))))
    vstore : ∀ (C : context) (x : idx) (v-memarg : memarg) (at : addrtype) (lim : limits) → 
      ((proj-uN-0 32 x) < (length (context-MEMS C))) →
      (((context-MEMS C) [ (proj-uN-0 32 x) ]!) ≡ (PAGE at lim)) →
      (Memarg-ok v-memarg at (vsize V128)) →
      Instr-ok C (VSTORE V128 x v-memarg) (mk-instrtype (mk-list (as (List valtype) ((valtype-addrtype at) ∷ valtype-V128 ∷ []))) [] (mk-list []))
    vstore-lane : ∀ (C : context) (v-N : N) (x : idx) (v-memarg : memarg) (i : laneidx) (at : addrtype) (lim : limits) → 
      ((proj-uN-0 32 x) < (length (context-MEMS C))) →
      (((context-MEMS C) [ (proj-uN-0 32 x) ]!) ≡ (PAGE at lim)) →
      (Memarg-ok v-memarg at v-N) →
      ((coerce {B = ℕ} (proj-uN-0 8 i)) < ((coerce {B = ℕ} 128) / (coerce {B = ℕ} v-N))) →
      Instr-ok C (VSTORE-LANE V128 (mk-sz v-N) x v-memarg i) (mk-instrtype (mk-list (as (List valtype) ((valtype-addrtype at) ∷ valtype-V128 ∷ []))) [] (mk-list []))
    Instr-ok--const : ∀ (C : context) (nt : numtype) (c-nt : (num- nt)) → Instr-ok C (instr-CONST nt c-nt) (mk-instrtype (mk-list []) [] (mk-list ((valtype-numtype nt) ∷ [])))
    unop : ∀ (C : context) (nt : numtype) (unop-nt : (unop- nt)) → Instr-ok C (UNOP nt unop-nt) (mk-instrtype (mk-list ((valtype-numtype nt) ∷ [])) [] (mk-list ((valtype-numtype nt) ∷ [])))
    binop : ∀ (C : context) (nt : numtype) (binop-nt : (binop- nt)) → Instr-ok C (BINOP nt binop-nt) (mk-instrtype (mk-list ((valtype-numtype nt) ∷ (valtype-numtype nt) ∷ [])) [] (mk-list ((valtype-numtype nt) ∷ [])))
    testop : ∀ (C : context) (nt : numtype) (testop-nt : (testop- nt)) → Instr-ok C (TESTOP nt testop-nt) (mk-instrtype (mk-list ((valtype-numtype nt) ∷ [])) [] (mk-list (as (List valtype) (valtype-I32 ∷ []))))
    relop : ∀ (C : context) (nt : numtype) (relop-nt : (relop- nt)) → Instr-ok C (RELOP nt relop-nt) (mk-instrtype (mk-list ((valtype-numtype nt) ∷ (valtype-numtype nt) ∷ [])) [] (mk-list (as (List valtype) (valtype-I32 ∷ []))))
    cvtop : ∀ (C : context) (nt-1 : numtype) (nt-2 : numtype) (cvtop : (cvtop-- nt-2 nt-1)) → Instr-ok C (CVTOP nt-1 nt-2 cvtop) (mk-instrtype (mk-list ((valtype-numtype nt-2) ∷ [])) [] (mk-list ((valtype-numtype nt-1) ∷ [])))
    vconst : ∀ (C : context) (c : (uN-fam0 (128))) → Instr-ok C (instr-VCONST V128 c) (mk-instrtype (mk-list []) [] (mk-list (as (List valtype) (valtype-V128 ∷ []))))
    Instr-ok--vvunop : ∀ (C : context) (v-vvunop : vvunop) → Instr-ok C (VVUNOP V128 v-vvunop) (mk-instrtype (mk-list (as (List valtype) (valtype-V128 ∷ []))) [] (mk-list (as (List valtype) (valtype-V128 ∷ []))))
    Instr-ok--vvbinop : ∀ (C : context) (v-vvbinop : vvbinop) → Instr-ok C (VVBINOP V128 v-vvbinop) (mk-instrtype (mk-list (as (List valtype) (valtype-V128 ∷ valtype-V128 ∷ []))) [] (mk-list (as (List valtype) (valtype-V128 ∷ []))))
    Instr-ok--vvternop : ∀ (C : context) (v-vvternop : vvternop) → Instr-ok C (VVTERNOP V128 v-vvternop) (mk-instrtype (mk-list (as (List valtype) (valtype-V128 ∷ valtype-V128 ∷ valtype-V128 ∷ []))) [] (mk-list (as (List valtype) (valtype-V128 ∷ []))))
    Instr-ok--vvtestop : ∀ (C : context) (v-vvtestop : vvtestop) → Instr-ok C (VVTESTOP V128 v-vvtestop) (mk-instrtype (mk-list (as (List valtype) (valtype-V128 ∷ []))) [] (mk-list (as (List valtype) (valtype-I32 ∷ []))))
    vunop : ∀ (C : context) (sh : shape) (vunop : (vunop- sh)) → Instr-ok C (VUNOP sh vunop) (mk-instrtype (mk-list (as (List valtype) (valtype-V128 ∷ []))) [] (mk-list (as (List valtype) (valtype-V128 ∷ []))))
    vbinop : ∀ (C : context) (sh : shape) (vbinop : (vbinop- sh)) → Instr-ok C (VBINOP sh vbinop) (mk-instrtype (mk-list (as (List valtype) (valtype-V128 ∷ valtype-V128 ∷ []))) [] (mk-list (as (List valtype) (valtype-V128 ∷ []))))
    vternop : ∀ (C : context) (sh : shape) (vternop : (vternop- sh)) → Instr-ok C (VTERNOP sh vternop) (mk-instrtype (mk-list (as (List valtype) (valtype-V128 ∷ valtype-V128 ∷ valtype-V128 ∷ []))) [] (mk-list (as (List valtype) (valtype-V128 ∷ []))))
    vtestop : ∀ (C : context) (sh : shape) (vtestop : (vtestop- sh)) → Instr-ok C (VTESTOP sh vtestop) (mk-instrtype (mk-list (as (List valtype) (valtype-V128 ∷ []))) [] (mk-list (as (List valtype) (valtype-I32 ∷ []))))
    vrelop : ∀ (C : context) (sh : shape) (vrelop : (vrelop- sh)) → Instr-ok C (VRELOP sh vrelop) (mk-instrtype (mk-list (as (List valtype) (valtype-V128 ∷ valtype-V128 ∷ []))) [] (mk-list (as (List valtype) (valtype-V128 ∷ []))))
    vshiftop : ∀ (C : context) (sh : ishape) (vshiftop : (vshiftop- sh)) → Instr-ok C (VSHIFTOP sh vshiftop) (mk-instrtype (mk-list (as (List valtype) (valtype-V128 ∷ valtype-I32 ∷ []))) [] (mk-list (as (List valtype) (valtype-V128 ∷ []))))
    vbitmask : ∀ (C : context) (sh : ishape) → Instr-ok C (VBITMASK sh) (mk-instrtype (mk-list (as (List valtype) (valtype-V128 ∷ []))) [] (mk-list (as (List valtype) (valtype-I32 ∷ []))))
    vswizzlop : ∀ (C : context) (sh : bshape) (vswizzlop : (vswizzlop- sh)) → Instr-ok C (VSWIZZLOP sh vswizzlop) (mk-instrtype (mk-list (as (List valtype) (valtype-V128 ∷ valtype-V128 ∷ []))) [] (mk-list (as (List valtype) (valtype-V128 ∷ []))))
    vshuffle : ∀ (C : context) (sh : bshape) (i-lst : (List laneidx)) → 
      Forall (λ (i : laneidx) → ((proj-uN-0 8 i) < (2 * (coerce {B = ℕ} ((fun-dim (coerce {B = shape} (sh)))))))) i-lst →
      Instr-ok C (VSHUFFLE sh i-lst) (mk-instrtype (mk-list (as (List valtype) (valtype-V128 ∷ valtype-V128 ∷ []))) [] (mk-list (as (List valtype) (valtype-V128 ∷ []))))
    vsplat : ∀ (C : context) (sh : shape) → Instr-ok C (VSPLAT sh) (mk-instrtype (mk-list ((valtype-numtype (unpackshape sh)) ∷ [])) [] (mk-list (as (List valtype) (valtype-V128 ∷ []))))
    vextract-lane : ∀ (C : context) (sh : shape) (sx-opt : (Maybe sx)) (i : laneidx) → 
      ((proj-uN-0 8 i) < (coerce {B = ℕ} ((fun-dim sh)))) →
      Instr-ok C (VEXTRACT-LANE sh sx-opt i) (mk-instrtype (mk-list (as (List valtype) (valtype-V128 ∷ []))) [] (mk-list ((valtype-numtype (unpackshape sh)) ∷ [])))
    vreplace-lane : ∀ (C : context) (sh : shape) (i : laneidx) → 
      ((proj-uN-0 8 i) < (coerce {B = ℕ} ((fun-dim sh)))) →
      Instr-ok C (VREPLACE-LANE sh i) (mk-instrtype (mk-list (as (List valtype) (valtype-V128 ∷ (valtype-numtype (unpackshape sh)) ∷ []))) [] (mk-list (as (List valtype) (valtype-V128 ∷ []))))
    vextunop : ∀ (C : context) (sh-1 : ishape) (sh-2 : ishape) (vextunop : (vextunop-- sh-2 sh-1)) → Instr-ok C (VEXTUNOP sh-1 sh-2 vextunop) (mk-instrtype (mk-list (as (List valtype) (valtype-V128 ∷ []))) [] (mk-list (as (List valtype) (valtype-V128 ∷ []))))
    vextbinop : ∀ (C : context) (sh-1 : ishape) (sh-2 : ishape) (vextbinop : (vextbinop-- sh-2 sh-1)) → Instr-ok C (VEXTBINOP sh-1 sh-2 vextbinop) (mk-instrtype (mk-list (as (List valtype) (valtype-V128 ∷ valtype-V128 ∷ []))) [] (mk-list (as (List valtype) (valtype-V128 ∷ []))))
    vextternop : ∀ (C : context) (sh-1 : ishape) (sh-2 : ishape) (vextternop : (vextternop-- sh-2 sh-1)) → Instr-ok C (VEXTTERNOP sh-1 sh-2 vextternop) (mk-instrtype (mk-list (as (List valtype) (valtype-V128 ∷ valtype-V128 ∷ valtype-V128 ∷ []))) [] (mk-list (as (List valtype) (valtype-V128 ∷ []))))
    vnarrow : ∀ (C : context) (sh-1 : ishape) (sh-2 : ishape) (v-sx : sx) → Instr-ok C (VNARROW sh-1 sh-2 v-sx) (mk-instrtype (mk-list (as (List valtype) (valtype-V128 ∷ valtype-V128 ∷ []))) [] (mk-list (as (List valtype) (valtype-V128 ∷ []))))
    vcvtop : ∀ (C : context) (sh-1 : shape) (sh-2 : shape) (vcvtop : (vcvtop-- sh-2 sh-1)) → Instr-ok C (VCVTOP sh-1 sh-2 vcvtop) (mk-instrtype (mk-list (as (List valtype) (valtype-V128 ∷ []))) [] (mk-list (as (List valtype) (valtype-V128 ∷ []))))

  {- Inductive Relations Definition at: ../specification/wasm-3.0/2.3-validation.instructions.spectec:6.1-6.96 -}
  data Instrs-ok : context → (List instr) → instrtype → Set where
    Instrs-ok--empty : ∀ (C : context) → Instrs-ok C [] (mk-instrtype (mk-list []) [] (mk-list []))
    Instrs-ok--instr : ∀ (C : context) (v-instr : instr) (t-1-lst : (List valtype)) (x-lst : (List idx)) (t-2-lst : (List valtype)) → 
      (Instr-ok C v-instr (mk-instrtype (mk-list t-1-lst) x-lst (mk-list t-2-lst))) →
      Instrs-ok C (v-instr ∷ []) (mk-instrtype (mk-list t-1-lst) x-lst (mk-list t-2-lst))
    seq : ∀ (C : context) (instr-1-lst : (List instr)) (instr-2-lst : (List instr)) (t-1-lst : (List valtype)) (x-1-lst : (List idx)) (x-2-lst : (List idx)) (t-3-lst : (List valtype)) (t-2-lst : (List valtype)) (init-lst : (List init)) (t-lst : (List valtype)) → 
      (Instrs-ok C instr-1-lst (mk-instrtype (mk-list t-1-lst) x-1-lst (mk-list t-2-lst))) →
      ((length init-lst) ≡ (length t-lst)) →
      ((length init-lst) ≡ (length x-1-lst)) →
      Forall (λ (x-1 : idx) → ((proj-uN-0 32 x-1) < (length (context-LOCALS C)))) x-1-lst →
      Forall₃ (λ (v-init : init) (t : valtype) (x-1 : idx) → (((context-LOCALS C) [ (proj-uN-0 32 x-1) ]!) ≡ (mk-localtype v-init t))) init-lst t-lst x-1-lst →
      ((with-locals C x-1-lst (map (λ (t : valtype) → (mk-localtype SET t)) t-lst)) ≢ nothing) →
      (Instrs-ok (unwrap! (with-locals C x-1-lst (map (λ (t : valtype) → (mk-localtype SET t)) t-lst))) instr-2-lst (mk-instrtype (mk-list t-2-lst) x-2-lst (mk-list t-3-lst))) →
      Instrs-ok C (instr-1-lst ++ instr-2-lst) (mk-instrtype (mk-list t-1-lst) (x-1-lst ++ x-2-lst) (mk-list t-3-lst))
    sub : ∀ (C : context) (instr-lst : (List instr)) (it' : instrtype) (it : instrtype) → 
      (Instrs-ok C instr-lst it) →
      (Instrtype-sub C it it') →
      (Instrtype-ok C it') →
      Instrs-ok C instr-lst it'
    Instrs-ok--frame : ∀ (C : context) (instr-lst : (List instr)) (t-lst : (List valtype)) (t-1-lst : (List valtype)) (x-lst : (List idx)) (t-2-lst : (List valtype)) → 
      (Instrs-ok C instr-lst (mk-instrtype (mk-list t-1-lst) x-lst (mk-list t-2-lst))) →
      (Resulttype-ok C (mk-list t-lst)) →
      Instrs-ok C instr-lst (mk-instrtype (mk-list (t-lst ++ t-1-lst)) x-lst (mk-list (t-lst ++ t-2-lst)))

{- Inductive Relations Definition at: ../specification/wasm-3.0/2.3-validation.instructions.spectec:7.1-7.94 -}
data Expr-ok : context → expr → resulttype → Set where
  mk-Expr-ok : ∀ (C : context) (instr-lst : (List instr)) (t-lst : (List valtype)) → 
    (Instrs-ok C instr-lst (mk-instrtype (mk-list []) [] (mk-list t-lst))) →
    Expr-ok C instr-lst (mk-list t-lst)

{- Inductive Relations Definition at: ../specification/wasm-3.0/2.3-validation.instructions.spectec:12.1-13.75 -}
data Nondefaultable : valtype → Set where
  mk-Nondefaultable : ∀ (t : valtype) (o0 : (Maybe val)) → 
    ((default- t) ≡ (just o0)) →
    (o0 ≡ nothing) →
    Nondefaultable t

{- Inductive Relations Definition at: ../specification/wasm-3.0/2.3-validation.instructions.spectec:649.1-649.104 -}
data Instr-const : context → instr → Set where
  Instr-const--const : ∀ (C : context) (nt : numtype) (c-nt : (num- nt)) → Instr-const C (instr-CONST nt c-nt)
  Instr-const--vconst : ∀ (C : context) (vt : vectype) (c-vt : (uN-fam0 ((vsize vt)))) → Instr-const C (instr-VCONST vt c-vt)
  Instr-const--ref-null : ∀ (C : context) (ht : heaptype) → Instr-const C (REF-NULL ht)
  Instr-const--ref-i31 : ∀ (C : context) → Instr-const C REF-I31
  Instr-const--ref-func : ∀ (C : context) (x : idx) → Instr-const C (REF-FUNC x)
  Instr-const--struct-new : ∀ (C : context) (x : idx) → Instr-const C (STRUCT-NEW x)
  Instr-const--struct-new-default : ∀ (C : context) (x : idx) → Instr-const C (STRUCT-NEW-DEFAULT x)
  Instr-const--array-new : ∀ (C : context) (x : idx) → Instr-const C (ARRAY-NEW x)
  Instr-const--array-new-default : ∀ (C : context) (x : idx) → Instr-const C (ARRAY-NEW-DEFAULT x)
  Instr-const--array-new-fixed : ∀ (C : context) (x : idx) (v-n : n) → Instr-const C (ARRAY-NEW-FIXED x (mk-uN v-n))
  Instr-const--any-convert-extern : ∀ (C : context) → Instr-const C ANY-CONVERT-EXTERN
  Instr-const--extern-convert-any : ∀ (C : context) → Instr-const C EXTERN-CONVERT-ANY
  Instr-const--global-get : ∀ (C : context) (x : idx) (t : valtype) → 
    ((proj-uN-0 32 x) < (length (context-GLOBALS C))) →
    (((context-GLOBALS C) [ (proj-uN-0 32 x) ]!) ≡ (mk-globaltype nothing t)) →
    Instr-const C (GLOBAL-GET x)
  binop-0 : ∀ (C : context) (binop : binop--fam0) → 
    ((length (as (List Inn) (I32 ∷ I64 ∷ []))) > 0) →
    (I32 ∈ (as (List Inn) (I32 ∷ I64 ∷ []))) →
    ((length (as (List binop--fam0) (ADD ∷ binop--SUB ∷ MUL ∷ []))) > 0) →
    (binop ∈ (as (List binop--fam0) (ADD ∷ binop--SUB ∷ MUL ∷ []))) →
    Instr-const C (BINOP (numtype-addrtype I32) binop)
  binop-1 : ∀ (C : context) (binop : binop--fam1) → 
    ((length (as (List Inn) (I32 ∷ I64 ∷ []))) > 0) →
    (I64 ∈ (as (List Inn) (I32 ∷ I64 ∷ []))) →
    ((length (as (List binop--fam1) (ADD ∷ binop--SUB ∷ MUL ∷ []))) > 0) →
    (binop ∈ (as (List binop--fam1) (ADD ∷ binop--SUB ∷ MUL ∷ []))) →
    Instr-const C (BINOP (numtype-addrtype I64) binop)

{- Inductive Relations Definition at: ../specification/wasm-3.0/2.3-validation.instructions.spectec:650.1-650.103 -}
data Expr-const : context → expr → Set where
  mk-Expr-const : ∀ (C : context) (instr-lst : (List instr)) → 
    Forall (λ (v-instr : instr) → (Instr-const C v-instr)) instr-lst →
    Expr-const C instr-lst

{- Inductive Relations Definition at: ../specification/wasm-3.0/2.3-validation.instructions.spectec:651.1-651.105 -}
data Expr-ok-const : context → expr → valtype → Set where
  mk-Expr-ok-const : ∀ (C : context) (v-expr : expr) (t : valtype) → 
    (Expr-ok C v-expr (mk-list (t ∷ []))) →
    (Expr-const C v-expr) →
    Expr-ok-const C v-expr t

{- Inductive Relations Definition at: ../specification/wasm-3.0/2.4-validation.modules.spectec:7.1-7.97 -}
data Type-ok : context → type → (List deftype) → Set where
  mk-Type-ok : ∀ (C : context) (v-rectype : rectype) (dt-lst : (List deftype)) (x : idx) → 
    ((proj-uN-0 32 x) ≡ (length (context-TYPES C))) →
    (dt-lst ≡ (rolldt x v-rectype)) →
    (Rectype-ok (C ⧺ record { context-TYPES = dt-lst ; context-TAGS = [] ; context-GLOBALS = [] ; context-MEMS = [] ; context-TABLES = [] ; context-FUNCS = [] ; context-DATAS = [] ; context-ELEMS = [] ; context-LOCALS = [] ; context-LABELS = [] ; context-RETURN = nothing ; REFS = [] ; RECS = [] }) v-rectype (oktypeidx-OK x)) →
    Type-ok C (TYPE v-rectype) dt-lst

{- Inductive Relations Definition at: ../specification/wasm-3.0/2.4-validation.modules.spectec:8.1-8.96 -}
data Tag-ok : context → tag → tagtype → Set where
  mk-Tag-ok : ∀ (C : context) (v-tagtype : tagtype) → 
    (Tagtype-ok C v-tagtype) →
    Tag-ok C (tag-TAG v-tagtype) (clos-tagtype C v-tagtype)

{- Inductive Relations Definition at: ../specification/wasm-3.0/2.4-validation.modules.spectec:9.1-9.99 -}
data Global-ok : context → global → globaltype → Set where
  mk-Global-ok : ∀ (C : context) (v-globaltype : globaltype) (v-expr : expr) (t : valtype) → 
    (Globaltype-ok C v-globaltype) →
    (v-globaltype ≡ (mk-globaltype (just MUT) t)) →
    (Expr-ok-const C v-expr t) →
    Global-ok C (global-GLOBAL v-globaltype v-expr) v-globaltype

{- Inductive Relations Definition at: ../specification/wasm-3.0/2.4-validation.modules.spectec:10.1-10.96 -}
data Mem-ok : context → mem → memtype → Set where
  mk-Mem-ok : ∀ (C : context) (v-memtype : memtype) → 
    (Memtype-ok C v-memtype) →
    Mem-ok C (MEMORY v-memtype) v-memtype

{- Inductive Relations Definition at: ../specification/wasm-3.0/2.4-validation.modules.spectec:11.1-11.98 -}
data Table-ok : context → table → tabletype → Set where
  mk-Table-ok : ∀ (C : context) (v-tabletype : tabletype) (v-expr : expr) (at : addrtype) (lim : limits) (rt : reftype) → 
    (Tabletype-ok C v-tabletype) →
    (v-tabletype ≡ (mk-tabletype at lim rt)) →
    (Expr-ok-const C v-expr (valtype-reftype rt)) →
    Table-ok C (table-TABLE v-tabletype v-expr) v-tabletype

{- Inductive Relations Definition at: ../specification/wasm-3.0/2.4-validation.modules.spectec:18.1-18.98 -}
data Local-ok : context → local → localtype → Set where
  set : ∀ (C : context) (t : valtype) → 
    (Defaultable t) →
    Local-ok C (LOCAL t) (mk-localtype SET t)
  unset : ∀ (C : context) (t : valtype) → 
    (Nondefaultable t) →
    Local-ok C (LOCAL t) (mk-localtype UNSET t)

{- Inductive Relations Definition at: ../specification/wasm-3.0/2.4-validation.modules.spectec:12.1-12.97 -}
data Func-ok : context → func → deftype → Set where
  mk-Func-ok : ∀ (C : context) (x : idx) (local-lst : (List local)) (v-expr : expr) (t-1-lst : (List valtype)) (t-2-lst : (List valtype)) (lct-lst : (List localtype)) → 
    ((proj-uN-0 32 x) < (length (context-TYPES C))) →
    (Expand ((context-TYPES C) [ (proj-uN-0 32 x) ]!) (comptype-FUNC (mk-list t-1-lst) (mk-list t-2-lst))) →
    ((length lct-lst) ≡ (length local-lst)) →
    Forall₂ (λ (lct : localtype) (v-local : local) → (Local-ok C v-local lct)) lct-lst local-lst →
    (Expr-ok (C ⧺ record { context-TYPES = [] ; context-TAGS = [] ; context-GLOBALS = [] ; context-MEMS = [] ; context-TABLES = [] ; context-FUNCS = [] ; context-DATAS = [] ; context-ELEMS = [] ; context-LOCALS = ((map (λ (t-1 : valtype) → (mk-localtype SET t-1)) t-1-lst) ++ lct-lst) ; context-LABELS = (as (List resulttype) ((mk-list t-2-lst) ∷ [])) ; context-RETURN = (just (mk-list t-2-lst)) ; REFS = [] ; RECS = [] }) v-expr (mk-list t-2-lst)) →
    Func-ok C (func-FUNC x local-lst v-expr) ((context-TYPES C) [ (proj-uN-0 32 x) ]!)

{- Inductive Relations Definition at: ../specification/wasm-3.0/2.4-validation.modules.spectec:15.1-15.118 -}
data Datamode-ok : context → datamode → datatype → Set where
  passive : ∀ (C : context) → Datamode-ok C datamode-PASSIVE OK
  active : ∀ (C : context) (x : idx) (v-expr : expr) (at : addrtype) (lim : limits) → 
    ((proj-uN-0 32 x) < (length (context-MEMS C))) →
    (((context-MEMS C) [ (proj-uN-0 32 x) ]!) ≡ (PAGE at lim)) →
    (Expr-ok-const C v-expr (valtype-addrtype at)) →
    Datamode-ok C (datamode-ACTIVE x v-expr) OK

{- Inductive Relations Definition at: ../specification/wasm-3.0/2.4-validation.modules.spectec:13.1-13.115 -}
data Data-ok : context → data' → datatype → Set where
  mk-Data-ok : ∀ (C : context) (b-lst : (List byte)) (v-datamode : datamode) → 
    (Datamode-ok C v-datamode OK) →
    Data-ok C (DATA b-lst v-datamode) OK

{- Inductive Relations Definition at: ../specification/wasm-3.0/2.4-validation.modules.spectec:16.1-16.101 -}
data Elemmode-ok : context → elemmode → elemtype → Set where
  Elemmode-ok--passive : ∀ (C : context) (rt : reftype) → Elemmode-ok C PASSIVE rt
  declare : ∀ (C : context) (rt : reftype) → Elemmode-ok C DECLARE rt
  Elemmode-ok--active : ∀ (C : context) (x : idx) (v-expr : expr) (rt : reftype) (at : addrtype) (lim : limits) (rt' : reftype) → 
    ((proj-uN-0 32 x) < (length (context-TABLES C))) →
    (((context-TABLES C) [ (proj-uN-0 32 x) ]!) ≡ (mk-tabletype at lim rt')) →
    (Reftype-sub C rt rt') →
    (Expr-ok-const C v-expr (valtype-addrtype at)) →
    Elemmode-ok C (ACTIVE x v-expr) rt

{- Inductive Relations Definition at: ../specification/wasm-3.0/2.4-validation.modules.spectec:14.1-14.97 -}
data Elem-ok : context → elem → elemtype → Set where
  mk-Elem-ok : ∀ (C : context) (v-elemtype : elemtype) (expr-lst : (List expr)) (v-elemmode : elemmode) → 
    (Reftype-ok C v-elemtype) →
    Forall (λ (v-expr : expr) → (Expr-ok-const C v-expr (valtype-reftype v-elemtype))) expr-lst →
    (Elemmode-ok C v-elemmode v-elemtype) →
    Elem-ok C (ELEM v-elemtype expr-lst v-elemmode) v-elemtype

{- Inductive Relations Definition at: ../specification/wasm-3.0/2.4-validation.modules.spectec:17.1-17.98 -}
data Start-ok : context → start → Set where
  mk-Start-ok : ∀ (C : context) (x : idx) → 
    ((proj-uN-0 32 x) < (length (context-FUNCS C))) →
    (Expand ((context-FUNCS C) [ (proj-uN-0 32 x) ]!) (comptype-FUNC (mk-list []) (mk-list []))) →
    Start-ok C (START x)

{- Inductive Relations Definition at: ../specification/wasm-3.0/2.4-validation.modules.spectec:98.1-98.105 -}
data Import-ok : context → import' → externtype → Set where
  mk-Import-ok : ∀ (C : context) (name-1 : name) (name-2 : name) (xt : externtype) → 
    (Externtype-ok C xt) →
    Import-ok C (IMPORT name-1 name-2 xt) (clos-externtype C xt)

{- Inductive Relations Definition at: ../specification/wasm-3.0/2.4-validation.modules.spectec:100.1-100.108 -}
data Externidx-ok : context → externidx → externtype → Set where
  Externidx-ok--tag : ∀ (C : context) (x : idx) (jt : tagtype) → 
    ((proj-uN-0 32 x) < (length (context-TAGS C))) →
    (((context-TAGS C) [ (proj-uN-0 32 x) ]!) ≡ jt) →
    Externidx-ok C (TAG x) (externtype-TAG jt)
  Externidx-ok--global : ∀ (C : context) (x : idx) (gt : globaltype) → 
    ((proj-uN-0 32 x) < (length (context-GLOBALS C))) →
    (((context-GLOBALS C) [ (proj-uN-0 32 x) ]!) ≡ gt) →
    Externidx-ok C (GLOBAL x) (externtype-GLOBAL gt)
  Externidx-ok--mem : ∀ (C : context) (x : idx) (mt : memtype) → 
    ((proj-uN-0 32 x) < (length (context-MEMS C))) →
    (((context-MEMS C) [ (proj-uN-0 32 x) ]!) ≡ mt) →
    Externidx-ok C (MEM x) (externtype-MEM mt)
  Externidx-ok--table : ∀ (C : context) (x : idx) (tt' : tabletype) → 
    ((proj-uN-0 32 x) < (length (context-TABLES C))) →
    (((context-TABLES C) [ (proj-uN-0 32 x) ]!) ≡ tt') →
    Externidx-ok C (TABLE x) (externtype-TABLE tt')
  Externidx-ok--func : ∀ (C : context) (x : idx) (dt : deftype) → 
    ((proj-uN-0 32 x) < (length (context-FUNCS C))) →
    (((context-FUNCS C) [ (proj-uN-0 32 x) ]!) ≡ dt) →
    Externidx-ok C (FUNC x) (externtype-FUNC (typeuse-deftype dt))

{- Inductive Relations Definition at: ../specification/wasm-3.0/2.4-validation.modules.spectec:99.1-99.105 -}
data Export-ok : context → export → name → externtype → Set where
  mk-Export-ok : ∀ (C : context) (v-name : name) (v-externidx : externidx) (xt : externtype) → 
    (Externidx-ok C v-externidx xt) →
    Export-ok C (EXPORT v-name v-externidx) v-name xt

{- Inductive Relations Definition at: ../specification/wasm-3.0/2.4-validation.modules.spectec:136.1-136.100 -}
data Globals-ok : context → (List global) → (List globaltype) → Set where
  Globals-ok--empty : ∀ (C : context) → Globals-ok C [] []
  Globals-ok--cons : ∀ (C : context) (global-1 : global) (global-lst : (List global)) (gt-1 : globaltype) (gt-lst : (List globaltype)) → 
    (Global-ok C global-1 gt-1) →
    (Globals-ok (C ⧺ record { context-TYPES = [] ; context-TAGS = [] ; context-GLOBALS = (gt-1 ∷ []) ; context-MEMS = [] ; context-TABLES = [] ; context-FUNCS = [] ; context-DATAS = [] ; context-ELEMS = [] ; context-LOCALS = [] ; context-LABELS = [] ; context-RETURN = nothing ; REFS = [] ; RECS = [] }) global-lst gt-lst) →
    Globals-ok C ((global-1 ∷ []) ++ global-lst) ((gt-1 ∷ []) ++ gt-lst)

{- Inductive Relations Definition at: ../specification/wasm-3.0/2.4-validation.modules.spectec:135.1-135.98 -}
data Types-ok : context → (List type) → (List deftype) → Set where
  Types-ok--empty : ∀ (C : context) → Types-ok C [] []
  Types-ok--cons : ∀ (C : context) (type-1 : type) (type-lst : (List type)) (dt-1-lst : (List deftype)) (dt-lst : (List deftype)) → 
    (Type-ok C type-1 dt-1-lst) →
    (Types-ok (C ⧺ record { context-TYPES = dt-1-lst ; context-TAGS = [] ; context-GLOBALS = [] ; context-MEMS = [] ; context-TABLES = [] ; context-FUNCS = [] ; context-DATAS = [] ; context-ELEMS = [] ; context-LOCALS = [] ; context-LABELS = [] ; context-RETURN = nothing ; REFS = [] ; RECS = [] }) type-lst dt-lst) →
    Types-ok C ((type-1 ∷ []) ++ type-lst) (dt-1-lst ++ dt-lst)

{- Inductive Type Definition at: ../specification/wasm-3.0/2.4-validation.modules.spectec:139.1-139.59 -}
data nonfuncs : Set where
  mk-nonfuncs : (global-lst : (List global)) → (mem-lst : (List mem)) → (table-lst : (List table)) → (elem-lst : (List elem)) → (start-opt : (Maybe start)) → (export-lst : (List export)) → nonfuncs

{- Auxiliary Definition at: ../specification/wasm-3.0/2.4-validation.modules.spectec:140.1-140.93 -}
{-# TERMINATING #-}
funcidx-nonfuncs : (v-nonfuncs : nonfuncs) → (List funcidx)
funcidx-nonfuncs (mk-nonfuncs global-lst mem-lst table-lst elem-lst start-opt export-lst) = (funcidx-module (module-MODULE (mk-list []) (mk-list []) (mk-list []) (mk-list global-lst) (mk-list mem-lst) (mk-list table-lst) (mk-list []) (mk-list []) (mk-list elem-lst) start-opt (mk-list export-lst)))
funcidx-nonfuncs v-nonfuncs = []

{- Inductive Relations Definition at: ../specification/wasm-3.0/2.4-validation.modules.spectec:134.1-134.99 -}
data Module-ok : module' → moduletype → Set where
  mk-Module-ok : ∀ (type-lst : (List type)) (import-lst : (List import')) (tag-lst : (List tag)) (global-lst : (List global)) (mem-lst : (List mem)) (table-lst : (List table)) (func-lst : (List func)) (data-lst : (List data')) (elem-lst : (List elem)) (start-opt : (Maybe start)) (export-lst : (List export)) (C : context) (xt-I-lst : (List externtype)) (xt-E-lst : (List externtype)) (dt'-lst : (List deftype)) (C' : context) (jt-lst : (List tagtype)) (gt-lst : (List globaltype)) (mt-lst : (List memtype)) (tt-lst : (List tabletype)) (dt-lst : (List deftype)) (ok-lst : (List datatype)) (rt-lst : (List reftype)) (nm-lst : (List name)) (jt-I-lst : (List tagtype)) (mt-I-lst : (List memtype)) (tt-I-lst : (List tabletype)) (gt-I-lst : (List globaltype)) (dt-I-lst : (List deftype)) (x-lst : (List idx)) → 
    (Types-ok record { context-TYPES = [] ; context-TAGS = [] ; context-GLOBALS = [] ; context-MEMS = [] ; context-TABLES = [] ; context-FUNCS = [] ; context-DATAS = [] ; context-ELEMS = [] ; context-LOCALS = [] ; context-LABELS = [] ; context-RETURN = nothing ; REFS = [] ; RECS = [] } type-lst dt'-lst) →
    ((length import-lst) ≡ (length xt-I-lst)) →
    Forall₂ (λ (v-import : import') (xt-I : externtype) → (Import-ok record { context-TYPES = dt'-lst ; context-TAGS = [] ; context-GLOBALS = [] ; context-MEMS = [] ; context-TABLES = [] ; context-FUNCS = [] ; context-DATAS = [] ; context-ELEMS = [] ; context-LOCALS = [] ; context-LABELS = [] ; context-RETURN = nothing ; REFS = [] ; RECS = [] } v-import xt-I)) import-lst xt-I-lst →
    ((length jt-lst) ≡ (length tag-lst)) →
    Forall₂ (λ (jt : tagtype) (v-tag : tag) → (Tag-ok C' v-tag jt)) jt-lst tag-lst →
    (Globals-ok C' global-lst gt-lst) →
    ((length mem-lst) ≡ (length mt-lst)) →
    Forall₂ (λ (v-mem : mem) (mt : memtype) → (Mem-ok C' v-mem mt)) mem-lst mt-lst →
    ((length table-lst) ≡ (length tt-lst)) →
    Forall₂ (λ (v-table : table) (tt' : tabletype) → (Table-ok C' v-table tt')) table-lst tt-lst →
    ((length dt-lst) ≡ (length func-lst)) →
    Forall₂ (λ (dt : deftype) (v-func : func) → (Func-ok C v-func dt)) dt-lst func-lst →
    ((length data-lst) ≡ (length ok-lst)) →
    Forall₂ (λ (v-data : data') (ok : datatype) → (Data-ok C v-data ok)) data-lst ok-lst →
    ((length elem-lst) ≡ (length rt-lst)) →
    Forall₂ (λ (v-elem : elem) (rt : elemtype) → (Elem-ok C v-elem rt)) elem-lst rt-lst →
    Forall (λ (v-start : start) → (Start-ok C v-start)) (fromMaybe start-opt) →
    ((length export-lst) ≡ (length nm-lst)) →
    ((length export-lst) ≡ (length xt-E-lst)) →
    Forall₃ (λ (v-export : export) (nm : name) (xt-E : externtype) → (Export-ok C v-export nm xt-E)) export-lst nm-lst xt-E-lst →
    (is-true (disjoint- name nm-lst)) →
    (C ≡ (C' ⧺ record { context-TYPES = [] ; context-TAGS = (jt-I-lst ++ jt-lst) ; context-GLOBALS = gt-lst ; context-MEMS = (mt-I-lst ++ mt-lst) ; context-TABLES = (tt-I-lst ++ tt-lst) ; context-FUNCS = [] ; context-DATAS = ok-lst ; context-ELEMS = rt-lst ; context-LOCALS = [] ; context-LABELS = [] ; context-RETURN = nothing ; REFS = [] ; RECS = [] })) →
    (C' ≡ record { context-TYPES = dt'-lst ; context-TAGS = [] ; context-GLOBALS = gt-I-lst ; context-MEMS = [] ; context-TABLES = [] ; context-FUNCS = (dt-I-lst ++ dt-lst) ; context-DATAS = [] ; context-ELEMS = [] ; context-LOCALS = [] ; context-LABELS = [] ; context-RETURN = nothing ; REFS = x-lst ; RECS = [] }) →
    (x-lst ≡ (funcidx-nonfuncs (mk-nonfuncs global-lst mem-lst table-lst elem-lst start-opt export-lst))) →
    (jt-I-lst ≡ (tagsxt xt-I-lst)) →
    (gt-I-lst ≡ (globalsxt xt-I-lst)) →
    (mt-I-lst ≡ (memsxt xt-I-lst)) →
    (tt-I-lst ≡ (tablesxt xt-I-lst)) →
    (dt-I-lst ≡ (funcsxt xt-I-lst)) →
    Module-ok (module-MODULE (mk-list type-lst) (mk-list import-lst) (mk-list tag-lst) (mk-list global-lst) (mk-list mem-lst) (mk-list table-lst) (mk-list func-lst) (mk-list data-lst) (mk-list elem-lst) start-opt (mk-list export-lst)) (clos-moduletype C (mk-moduletype xt-I-lst xt-E-lst))

{- Inductive Type Definition at: ../specification/wasm-3.0/3.0-numerics.relaxed.spectec:5.1-5.24 -}
data relaxed2 : Set where
  mk-relaxed2 : (i : ℕ) → relaxed2 {- 1 premise(s) dropped -}

{- Auxiliary Definition at: ../specification/wasm-3.0/3.0-numerics.relaxed.spectec:5.1-5.24 -}
{-# TERMINATING #-}
proj-relaxed2-0 : (x : relaxed2) → (ℕ)
proj-relaxed2-0 (mk-relaxed2 v-num-0) = (v-num-0)
proj-relaxed2-0 x = (default-val)

instance
  proj-relaxed2-0-coercion : Coerce relaxed2 (ℕ)
  proj-relaxed2-0-coercion = record { coerce = proj-relaxed2-0 }

{- Inductive Type Definition at: ../specification/wasm-3.0/3.0-numerics.relaxed.spectec:6.1-6.32 -}
data relaxed4 : Set where
  mk-relaxed4 : (i : ℕ) → relaxed4 {- 1 premise(s) dropped -}

{- Auxiliary Definition at: ../specification/wasm-3.0/3.0-numerics.relaxed.spectec:6.1-6.32 -}
{-# TERMINATING #-}
proj-relaxed4-0 : (x : relaxed4) → (ℕ)
proj-relaxed4-0 (mk-relaxed4 v-num-0) = (v-num-0)
proj-relaxed4-0 x = (default-val)

instance
  proj-relaxed4-0-coercion : Coerce relaxed4 (ℕ)
  proj-relaxed4-0-coercion = record { coerce = proj-relaxed4-0 }

{- Auxiliary Definition at: ../specification/wasm-3.0/3.0-numerics.relaxed.spectec:8.1-8.83 -}
{-# TERMINATING #-}
fun-relaxed2 : (v-relaxed2 : relaxed2) (r-X : Set) {{_ : Inhabited r-X}} (X-0 : r-X) (X-1 : r-X) → r-X
fun-relaxed2 i r-X X-1 X-2 = (if (ND ) then ((X-1 ∷ X-2 ∷ []) [ (coerce {B = ℕ} (i)) ]!) else ((X-1 ∷ X-2 ∷ []) [ 0 ]!))

{- Auxiliary Definition at: ../specification/wasm-3.0/3.0-numerics.relaxed.spectec:9.1-9.89 -}
{-# TERMINATING #-}
fun-relaxed4 : (v-relaxed4 : relaxed4) (r-X : Set) {{_ : Inhabited r-X}} (X-0 : r-X) (X-1 : r-X) (X-2 : r-X) (X-3 : r-X) → r-X
fun-relaxed4 i r-X X-1 X-2 X-3 X-4 = (if (ND ) then ((X-1 ∷ X-2 ∷ X-3 ∷ X-4 ∷ []) [ (coerce {B = ℕ} (i)) ]!) else ((X-1 ∷ X-2 ∷ X-3 ∷ X-4 ∷ []) [ 0 ]!))

{- Axiom Definition at: ../specification/wasm-3.0/3.0-numerics.relaxed.spectec:18.1-18.43 -}
postulate R-fmadd : relaxed2

{- Axiom Definition at: ../specification/wasm-3.0/3.0-numerics.relaxed.spectec:19.1-19.43 -}
postulate R-fmin : relaxed4

{- Axiom Definition at: ../specification/wasm-3.0/3.0-numerics.relaxed.spectec:20.1-20.43 -}
postulate R-fmax : relaxed4

{- Axiom Definition at: ../specification/wasm-3.0/3.0-numerics.relaxed.spectec:21.1-21.43 -}
postulate R-idot : relaxed2

{- Axiom Definition at: ../specification/wasm-3.0/3.0-numerics.relaxed.spectec:22.1-22.43 -}
postulate R-iq15mulr : relaxed2

{- Axiom Definition at: ../specification/wasm-3.0/3.0-numerics.relaxed.spectec:23.1-23.43 -}
postulate R-trunc-u : relaxed4

{- Axiom Definition at: ../specification/wasm-3.0/3.0-numerics.relaxed.spectec:24.1-24.43 -}
postulate R-trunc-s : relaxed2

{- Axiom Definition at: ../specification/wasm-3.0/3.0-numerics.relaxed.spectec:25.1-25.43 -}
postulate R-swizzle : relaxed2

{- Axiom Definition at: ../specification/wasm-3.0/3.0-numerics.relaxed.spectec:26.1-26.43 -}
postulate R-laneselect : relaxed2

{- Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:7.1-7.41 -}
postulate s33-to-u32 : ∀ (v-s33 : s33) → u32

{- Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:12.1-12.107 -}
postulate ibits- : ∀ (v-N : N) (v-iN : (uN-fam0 (v-N))) → (List bit)

{- Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:13.1-13.107 -}
postulate fbits- : ∀ (v-N : N) (v-fN : (fN-fam0 (v-N))) → (List bit)

{- Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:14.1-14.109 -}
postulate ibytes- : ∀ (v-N : N) (v-iN : (uN-fam0 (v-N))) → (List byte)

{- Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:15.1-15.109 -}
postulate fbytes- : ∀ (v-N : N) (v-fN : (fN-fam0 (v-N))) → (List byte)

{- Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:16.1-16.104 -}
postulate nbytes- : ∀ (v-numtype : numtype) (v-num- : (num- v-numtype)) → (List byte)

{- Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:17.1-17.104 -}
postulate vbytes- : ∀ (v-vectype : vectype) (v-vec- : (uN-fam0 ((vsize v-vectype)))) → (List byte)

{- Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:18.1-18.104 -}
postulate zbytes- : ∀ (v-storagetype : storagetype) (v-lit- : (lit- v-storagetype)) → (List byte)

{- Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:19.1-19.104 -}
postulate cbytes- : ∀ (v-Cnn : Cnn) (v-lit- : (lit- (storagetype-Cnn v-Cnn))) → (List byte)

{- Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:21.1-21.91 -}
postulate inv-ibits- : ∀ (v-N : N) (var-0-lst : (List bit)) → (uN-fam0 (v-N))

{- Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:22.1-22.91 -}
postulate inv-fbits- : ∀ (v-N : N) (var-0-lst : (List bit)) → (fN-fam0 (v-N))

{- Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:23.1-23.92 -}
postulate inv-ibytes- : ∀ (v-N : N) (var-0-lst : (List byte)) → (uN-fam0 (v-N))

{- Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:24.1-24.92 -}
postulate inv-fbytes- : ∀ (v-N : N) (var-0-lst : (List byte)) → (fN-fam0 (v-N))

{- Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:25.1-25.87 -}
postulate inv-nbytes- : ∀ (v-numtype : numtype) (var-0-lst : (List byte)) → (num- v-numtype)

{- Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:26.1-26.87 -}
postulate inv-vbytes- : ∀ (v-vectype : vectype) (var-0-lst : (List byte)) → (uN-fam0 ((vsize v-vectype)))

{- Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:27.1-27.92 -}
postulate inv-zbytes- : ∀ (v-storagetype : storagetype) (var-0-lst : (List byte)) → (lit- v-storagetype)

{- Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:28.1-28.87 -}
postulate inv-cbytes- : ∀ (v-Cnn : Cnn) (var-0-lst : (List byte)) → (lit- (storagetype-Cnn v-Cnn))

{- Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:52.1-52.54 -}
postulate signed- : ∀ (v-N : N) (nat : ℕ) → ℕ

{- Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:56.1-56.68 -}
postulate inv-signed- : ∀ (v-N : N) (int : ℕ) → ℕ

{- Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:61.1-61.60 -}
{-# TERMINATING #-}
fun-sx : (v-storagetype : storagetype) → (Maybe (Maybe sx))
fun-sx storagetype-I32 = (just nothing)
fun-sx storagetype-I64 = (just nothing)
fun-sx storagetype-F32 = (just nothing)
fun-sx storagetype-F64 = (just nothing)
fun-sx storagetype-V128 = (just nothing)
fun-sx I8 = (just (just S))
fun-sx I16 = (just (just S))
fun-sx x0 = nothing

{- Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:68.1-68.51 -}
{-# TERMINATING #-}
fun-zero : (v-lanetype : lanetype) → (lane- v-lanetype)
fun-zero lanetype-I32 = (mk-uN 0)
fun-zero lanetype-I64 = (mk-uN 0)
fun-zero lanetype-I8 = (mk-uN 0)
fun-zero lanetype-I16 = (mk-uN 0)
fun-zero lanetype-F32 = (fzero (size (numtype-Fnn Fnn-F32)))
fun-zero lanetype-F64 = (fzero (size (numtype-Fnn Fnn-F64)))
fun-zero v-lanetype = (Inhabited.default-val (inh-lane--fun v-lanetype))

{- Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:72.1-72.22 -}
{-# TERMINATING #-}
bool : (v-bool : Bool) → ℕ
bool false = 0
bool true = 1
bool v-bool = default-val

{- Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:76.1-76.23 -}
postulate truncz : ∀ (rat : ℕ) → ℕ

{- Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:80.1-80.59 -}
postulate ceilz : ∀ (rat : ℕ) → ℕ

{- Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:87.1-87.61 -}
{-# TERMINATING #-}
sat-u- : (v-N : N) (int : ℕ) → ℕ
sat-u- v-N i = (if (i <? (coerce {B = ℕ} 0)) then 0 else (if (i >? ((coerce {B = ℕ} (2 ^ v-N)) – (coerce {B = ℕ} 1))) then (coerce {B = ℕ} ((coerce {B = ℕ} (2 ^ v-N)) – (coerce {B = ℕ} 1))) else (coerce {B = ℕ} i)))

{- Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:92.1-92.61 -}
{-# TERMINATING #-}
sat-s- : (v-N : N) (int : ℕ) → ℕ
sat-s- v-N i = (if (i <? (0 – (coerce {B = ℕ} (2 ^ (coerce {B = ℕ} ((coerce {B = ℕ} v-N) – (coerce {B = ℕ} 1))))))) then (0 – (coerce {B = ℕ} (2 ^ (coerce {B = ℕ} ((coerce {B = ℕ} v-N) – (coerce {B = ℕ} 1)))))) else (if (i >? ((coerce {B = ℕ} (2 ^ (coerce {B = ℕ} ((coerce {B = ℕ} v-N) – (coerce {B = ℕ} 1))))) – (coerce {B = ℕ} 1))) then ((coerce {B = ℕ} (2 ^ (coerce {B = ℕ} ((coerce {B = ℕ} v-N) – (coerce {B = ℕ} 1))))) – (coerce {B = ℕ} 1)) else i))

{- Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:100.1-100.29 -}
{-# TERMINATING #-}
ineg- : (v-N : N) (v-iN : (uN-fam0 (v-N))) → (uN-fam0 (v-N))
ineg- v-N i-1 = (mk-uN (coerce {B = ℕ} (((coerce {B = ℕ} (2 ^ v-N)) – (coerce {B = ℕ} (proj-uN-0 v-N i-1))) % (coerce {B = ℕ} (2 ^ v-N)))))

{- Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:101.1-101.29 -}
{-# TERMINATING #-}
iabs- : (v-N : N) (v-iN : (uN-fam0 (v-N))) → (uN-fam0 (v-N))
iabs- v-N i-1 = (if ((signed- v-N (proj-uN-0 v-N i-1)) ≥? (coerce {B = ℕ} 0)) then i-1 else (ineg- v-N i-1))

{- Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:102.1-102.29 -}
postulate iclz- : ∀ (v-N : N) (v-iN : (uN-fam0 (v-N))) → (uN-fam0 (v-N))

{- Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:103.1-103.29 -}
postulate ictz- : ∀ (v-N : N) (v-iN : (uN-fam0 (v-N))) → (uN-fam0 (v-N))

{- Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:104.1-104.32 -}
postulate ipopcnt- : ∀ (v-N : N) (v-iN : (uN-fam0 (v-N))) → (uN-fam0 (v-N))

{- Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:105.1-105.86 -}
{-# TERMINATING #-}
iextend- : (v-N : N) (v-M : M) (v-sx : sx) (v-iN : (uN-fam0 (v-N))) → (uN-fam0 (v-N))
iextend- v-N v-M U i = (mk-uN ((proj-uN-0 v-N i) % (2 ^ v-M)))
iextend- v-N v-M S i = (mk-uN (inv-signed- v-N (signed- v-M ((proj-uN-0 v-N i) % (2 ^ v-M)))))
iextend- v-N v-M v-sx v-iN = (Inhabited.default-val (inh-iN-fun v-N))

{- Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:107.1-107.36 -}
{-# TERMINATING #-}
iadd- : (v-N : N) (v-iN : (uN-fam0 (v-N))) (iN-0 : (uN-fam0 (v-N))) → (uN-fam0 (v-N))
iadd- v-N i-1 i-2 = (mk-uN (((proj-uN-0 v-N i-1) + (proj-uN-0 v-N i-2)) % (2 ^ v-N)))

{- Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:108.1-108.36 -}
{-# TERMINATING #-}
isub- : (v-N : N) (v-iN : (uN-fam0 (v-N))) (iN-0 : (uN-fam0 (v-N))) → (uN-fam0 (v-N))
isub- v-N i-1 i-2 = (mk-uN (coerce {B = ℕ} (((coerce {B = ℕ} ((2 ^ v-N) + (proj-uN-0 v-N i-1))) – (coerce {B = ℕ} (proj-uN-0 v-N i-2))) % (coerce {B = ℕ} (2 ^ v-N)))))

{- Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:109.1-109.36 -}
{-# TERMINATING #-}
imul- : (v-N : N) (v-iN : (uN-fam0 (v-N))) (iN-0 : (uN-fam0 (v-N))) → (uN-fam0 (v-N))
imul- v-N i-1 i-2 = (mk-uN (((proj-uN-0 v-N i-1) * (proj-uN-0 v-N i-2)) % (2 ^ v-N)))

{- Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:110.1-110.83 -}
postulate idiv- : ∀ (v-N : N) (v-sx : sx) (v-iN : (uN-fam0 (v-N))) (iN-0 : (uN-fam0 (v-N))) → (Maybe (uN-fam0 (v-N)))

{- Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:111.1-111.83 -}
postulate irem- : ∀ (v-N : N) (v-sx : sx) (v-iN : (uN-fam0 (v-N))) (iN-0 : (uN-fam0 (v-N))) → (Maybe (uN-fam0 (v-N)))

{- Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:112.1-112.83 -}
postulate imin- : ∀ (v-N : N) (v-sx : sx) (v-iN : (uN-fam0 (v-N))) (iN-0 : (uN-fam0 (v-N))) → (uN-fam0 (v-N))

{- Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:113.1-113.83 -}
postulate imax- : ∀ (v-N : N) (v-sx : sx) (v-iN : (uN-fam0 (v-N))) (iN-0 : (uN-fam0 (v-N))) → (uN-fam0 (v-N))

{- Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:114.1-114.88 -}
{-# TERMINATING #-}
iadd-sat- : (v-N : N) (v-sx : sx) (v-iN : (uN-fam0 (v-N))) (iN-0 : (uN-fam0 (v-N))) → (uN-fam0 (v-N))
iadd-sat- v-N U i-1 i-2 = (mk-uN (sat-u- v-N (coerce {B = ℕ} ((proj-uN-0 v-N i-1) + (proj-uN-0 v-N i-2)))))
iadd-sat- v-N S i-1 i-2 = (mk-uN (inv-signed- v-N (sat-s- v-N ((signed- v-N (proj-uN-0 v-N i-1)) + (signed- v-N (proj-uN-0 v-N i-2))))))
iadd-sat- v-N v-sx v-iN iN-0 = (Inhabited.default-val (inh-iN-fun v-N))

{- Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:115.1-115.88 -}
{-# TERMINATING #-}
isub-sat- : (v-N : N) (v-sx : sx) (v-iN : (uN-fam0 (v-N))) (iN-0 : (uN-fam0 (v-N))) → (uN-fam0 (v-N))
isub-sat- v-N U i-1 i-2 = (mk-uN (sat-u- v-N ((coerce {B = ℕ} (proj-uN-0 v-N i-1)) – (coerce {B = ℕ} (proj-uN-0 v-N i-2)))))
isub-sat- v-N S i-1 i-2 = (mk-uN (inv-signed- v-N (sat-s- v-N ((signed- v-N (proj-uN-0 v-N i-1)) – (signed- v-N (proj-uN-0 v-N i-2))))))
isub-sat- v-N v-sx v-iN iN-0 = (Inhabited.default-val (inh-iN-fun v-N))

{- Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:116.1-116.92 -}
postulate iq15mulr-sat- : ∀ (v-N : N) (v-sx : sx) (v-iN : (uN-fam0 (v-N))) (iN-0 : (uN-fam0 (v-N))) → (uN-fam0 (v-N))

{- Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:117.1-117.101 -}
postulate irelaxed-q15mulr- : ∀ (v-N : N) (v-sx : sx) (v-iN : (uN-fam0 (v-N))) (iN-0 : (uN-fam0 (v-N))) → (List (uN-fam0 (v-N)))

{- Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:118.1-118.84 -}
postulate iavgr- : ∀ (v-N : N) (v-sx : sx) (v-iN : (uN-fam0 (v-N))) (iN-0 : (uN-fam0 (v-N))) → (uN-fam0 (v-N))

{- Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:120.1-120.29 -}
postulate inot- : ∀ (v-N : N) (v-iN : (uN-fam0 (v-N))) → (uN-fam0 (v-N))

{- Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:121.1-121.29 -}
postulate irev- : ∀ (v-N : N) (v-iN : (uN-fam0 (v-N))) → (uN-fam0 (v-N))

{- Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:122.1-122.36 -}
postulate iand- : ∀ (v-N : N) (v-iN : (uN-fam0 (v-N))) (iN-0 : (uN-fam0 (v-N))) → (uN-fam0 (v-N))

{- Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:123.1-123.39 -}
postulate iandnot- : ∀ (v-N : N) (v-iN : (uN-fam0 (v-N))) (iN-0 : (uN-fam0 (v-N))) → (uN-fam0 (v-N))

{- Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:124.1-124.35 -}
postulate ior- : ∀ (v-N : N) (v-iN : (uN-fam0 (v-N))) (iN-0 : (uN-fam0 (v-N))) → (uN-fam0 (v-N))

{- Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:125.1-125.36 -}
postulate ixor- : ∀ (v-N : N) (v-iN : (uN-fam0 (v-N))) (iN-0 : (uN-fam0 (v-N))) → (uN-fam0 (v-N))

{- Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:126.1-126.34 -}
postulate ishl- : ∀ (v-N : N) (v-iN : (uN-fam0 (v-N))) (v-u32 : u32) → (uN-fam0 (v-N))

{- Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:127.1-127.76 -}
postulate ishr- : ∀ (v-N : N) (v-sx : sx) (v-iN : (uN-fam0 (v-N))) (v-u32 : u32) → (uN-fam0 (v-N))

{- Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:128.1-128.37 -}
postulate irotl- : ∀ (v-N : N) (v-iN : (uN-fam0 (v-N))) (iN-0 : (uN-fam0 (v-N))) → (uN-fam0 (v-N))

{- Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:129.1-129.37 -}
postulate irotr- : ∀ (v-N : N) (v-iN : (uN-fam0 (v-N))) (iN-0 : (uN-fam0 (v-N))) → (uN-fam0 (v-N))

{- Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:131.1-131.49 -}
postulate ibitselect- : ∀ (v-N : N) (v-iN : (uN-fam0 (v-N))) (iN-0 : (uN-fam0 (v-N))) (iN-1 : (uN-fam0 (v-N))) → (uN-fam0 (v-N))

{- Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:132.1-132.59 -}
postulate irelaxed-laneselect- : ∀ (v-N : N) (v-iN : (uN-fam0 (v-N))) (iN-0 : (uN-fam0 (v-N))) (iN-1 : (uN-fam0 (v-N))) → (List (uN-fam0 (v-N)))

{- Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:134.1-134.27 -}
{-# TERMINATING #-}
ieqz- : (v-N : N) (v-iN : (uN-fam0 (v-N))) → u32
ieqz- v-N i-1 = (mk-uN (bool ((proj-uN-0 v-N i-1) =? 0)))

{- Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:135.1-135.27 -}
{-# TERMINATING #-}
inez- : (v-N : N) (v-iN : (uN-fam0 (v-N))) → u32
inez- v-N i-1 = (mk-uN (bool ((proj-uN-0 v-N i-1) ≠? 0)))

{- Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:137.1-137.33 -}
{-# TERMINATING #-}
ieq- : (v-N : N) (v-iN : (uN-fam0 (v-N))) (iN-0 : (uN-fam0 (v-N))) → u32
ieq- v-N i-1 i-2 = (mk-uN (bool (i-1 =? i-2)))

{- Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:138.1-138.33 -}
{-# TERMINATING #-}
ine- : (v-N : N) (v-iN : (uN-fam0 (v-N))) (iN-0 : (uN-fam0 (v-N))) → u32
ine- v-N i-1 i-2 = (mk-uN (bool (i-1 ≠? i-2)))

{- Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:139.1-139.75 -}
{-# TERMINATING #-}
ilt- : (v-N : N) (v-sx : sx) (v-iN : (uN-fam0 (v-N))) (iN-0 : (uN-fam0 (v-N))) → u32
ilt- v-N U i-1 i-2 = (mk-uN (bool ((proj-uN-0 v-N i-1) <? (proj-uN-0 v-N i-2))))
ilt- v-N S i-1 i-2 = (mk-uN (bool ((signed- v-N (proj-uN-0 v-N i-1)) <? (signed- v-N (proj-uN-0 v-N i-2)))))
ilt- v-N v-sx v-iN iN-0 = default-val

{- Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:140.1-140.75 -}
{-# TERMINATING #-}
igt- : (v-N : N) (v-sx : sx) (v-iN : (uN-fam0 (v-N))) (iN-0 : (uN-fam0 (v-N))) → u32
igt- v-N U i-1 i-2 = (mk-uN (bool ((proj-uN-0 v-N i-1) >? (proj-uN-0 v-N i-2))))
igt- v-N S i-1 i-2 = (mk-uN (bool ((signed- v-N (proj-uN-0 v-N i-1)) >? (signed- v-N (proj-uN-0 v-N i-2)))))
igt- v-N v-sx v-iN iN-0 = default-val

{- Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:141.1-141.75 -}
{-# TERMINATING #-}
ile- : (v-N : N) (v-sx : sx) (v-iN : (uN-fam0 (v-N))) (iN-0 : (uN-fam0 (v-N))) → u32
ile- v-N U i-1 i-2 = (mk-uN (bool ((proj-uN-0 v-N i-1) ≤? (proj-uN-0 v-N i-2))))
ile- v-N S i-1 i-2 = (mk-uN (bool ((signed- v-N (proj-uN-0 v-N i-1)) ≤? (signed- v-N (proj-uN-0 v-N i-2)))))
ile- v-N v-sx v-iN iN-0 = default-val

{- Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:142.1-142.75 -}
{-# TERMINATING #-}
ige- : (v-N : N) (v-sx : sx) (v-iN : (uN-fam0 (v-N))) (iN-0 : (uN-fam0 (v-N))) → u32
ige- v-N U i-1 i-2 = (mk-uN (bool ((proj-uN-0 v-N i-1) ≥? (proj-uN-0 v-N i-2))))
ige- v-N S i-1 i-2 = (mk-uN (bool ((signed- v-N (proj-uN-0 v-N i-1)) ≥? (signed- v-N (proj-uN-0 v-N i-2)))))
ige- v-N v-sx v-iN iN-0 = default-val

{- Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:242.1-242.30 -}
postulate fabs- : ∀ (v-N : N) (v-fN : (fN-fam0 (v-N))) → (List (fN-fam0 (v-N)))

{- Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:243.1-243.30 -}
postulate fneg- : ∀ (v-N : N) (v-fN : (fN-fam0 (v-N))) → (List (fN-fam0 (v-N)))

{- Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:244.1-244.31 -}
postulate fsqrt- : ∀ (v-N : N) (v-fN : (fN-fam0 (v-N))) → (List (fN-fam0 (v-N)))

{- Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:245.1-245.31 -}
postulate fceil- : ∀ (v-N : N) (v-fN : (fN-fam0 (v-N))) → (List (fN-fam0 (v-N)))

{- Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:246.1-246.32 -}
postulate ffloor- : ∀ (v-N : N) (v-fN : (fN-fam0 (v-N))) → (List (fN-fam0 (v-N)))

{- Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:247.1-247.32 -}
postulate ftrunc- : ∀ (v-N : N) (v-fN : (fN-fam0 (v-N))) → (List (fN-fam0 (v-N)))

{- Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:248.1-248.34 -}
postulate fnearest- : ∀ (v-N : N) (v-fN : (fN-fam0 (v-N))) → (List (fN-fam0 (v-N)))

{- Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:250.1-250.37 -}
postulate fadd- : ∀ (v-N : N) (v-fN : (fN-fam0 (v-N))) (fN-0 : (fN-fam0 (v-N))) → (List (fN-fam0 (v-N)))

{- Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:251.1-251.37 -}
postulate fsub- : ∀ (v-N : N) (v-fN : (fN-fam0 (v-N))) (fN-0 : (fN-fam0 (v-N))) → (List (fN-fam0 (v-N)))

{- Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:252.1-252.37 -}
postulate fmul- : ∀ (v-N : N) (v-fN : (fN-fam0 (v-N))) (fN-0 : (fN-fam0 (v-N))) → (List (fN-fam0 (v-N)))

{- Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:253.1-253.37 -}
postulate fdiv- : ∀ (v-N : N) (v-fN : (fN-fam0 (v-N))) (fN-0 : (fN-fam0 (v-N))) → (List (fN-fam0 (v-N)))

{- Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:254.1-254.37 -}
postulate fmin- : ∀ (v-N : N) (v-fN : (fN-fam0 (v-N))) (fN-0 : (fN-fam0 (v-N))) → (List (fN-fam0 (v-N)))

{- Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:255.1-255.37 -}
postulate fmax- : ∀ (v-N : N) (v-fN : (fN-fam0 (v-N))) (fN-0 : (fN-fam0 (v-N))) → (List (fN-fam0 (v-N)))

{- Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:256.1-256.38 -}
postulate fpmin- : ∀ (v-N : N) (v-fN : (fN-fam0 (v-N))) (fN-0 : (fN-fam0 (v-N))) → (List (fN-fam0 (v-N)))

{- Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:257.1-257.38 -}
postulate fpmax- : ∀ (v-N : N) (v-fN : (fN-fam0 (v-N))) (fN-0 : (fN-fam0 (v-N))) → (List (fN-fam0 (v-N)))

{- Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:258.1-258.82 -}
postulate frelaxed-min- : ∀ (v-N : N) (v-fN : (fN-fam0 (v-N))) (fN-0 : (fN-fam0 (v-N))) → (List (fN-fam0 (v-N)))

{- Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:259.1-259.82 -}
postulate frelaxed-max- : ∀ (v-N : N) (v-fN : (fN-fam0 (v-N))) (fN-0 : (fN-fam0 (v-N))) → (List (fN-fam0 (v-N)))

{- Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:260.1-260.42 -}
postulate fcopysign- : ∀ (v-N : N) (v-fN : (fN-fam0 (v-N))) (fN-0 : (fN-fam0 (v-N))) → (List (fN-fam0 (v-N)))

{- Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:262.1-262.33 -}
postulate feq- : ∀ (v-N : N) (v-fN : (fN-fam0 (v-N))) (fN-0 : (fN-fam0 (v-N))) → u32

{- Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:263.1-263.33 -}
postulate fne- : ∀ (v-N : N) (v-fN : (fN-fam0 (v-N))) (fN-0 : (fN-fam0 (v-N))) → u32

{- Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:264.1-264.33 -}
postulate flt- : ∀ (v-N : N) (v-fN : (fN-fam0 (v-N))) (fN-0 : (fN-fam0 (v-N))) → u32

{- Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:265.1-265.33 -}
postulate fgt- : ∀ (v-N : N) (v-fN : (fN-fam0 (v-N))) (fN-0 : (fN-fam0 (v-N))) → u32

{- Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:266.1-266.33 -}
postulate fle- : ∀ (v-N : N) (v-fN : (fN-fam0 (v-N))) (fN-0 : (fN-fam0 (v-N))) → u32

{- Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:267.1-267.33 -}
postulate fge- : ∀ (v-N : N) (v-fN : (fN-fam0 (v-N))) (fN-0 : (fN-fam0 (v-N))) → u32

{- Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:269.1-269.91 -}
postulate frelaxed-madd- : ∀ (v-N : N) (v-fN : (fN-fam0 (v-N))) (fN-0 : (fN-fam0 (v-N))) (fN-1 : (fN-fam0 (v-N))) → (List (fN-fam0 (v-N)))

{- Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:270.1-270.92 -}
postulate frelaxed-nmadd- : ∀ (v-N : N) (v-fN : (fN-fam0 (v-N))) (fN-0 : (fN-fam0 (v-N))) (fN-1 : (fN-fam0 (v-N))) → (List (fN-fam0 (v-N)))

{- Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:308.1-308.33 -}
postulate wrap-- : ∀ (v-M : M) (v-N : N) (v-iN : (uN-fam0 (v-M))) → (uN-fam0 (v-N))

{- Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:309.1-309.90 -}
postulate extend-- : ∀ (v-M : M) (v-N : N) (v-sx : sx) (v-iN : (uN-fam0 (v-M))) → (uN-fam0 (v-N))

{- Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:310.1-310.89 -}
postulate trunc-- : ∀ (v-M : M) (v-N : N) (v-sx : sx) (v-fN : (fN-fam0 (v-M))) → (Maybe (uN-fam0 (v-N)))

{- Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:311.1-311.94 -}
postulate trunc-sat-- : ∀ (v-M : M) (v-N : N) (v-sx : sx) (v-fN : (fN-fam0 (v-M))) → (Maybe (uN-fam0 (v-N)))

{- Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:312.1-312.98 -}
postulate relaxed-trunc-- : ∀ (v-M : M) (v-N : N) (v-sx : sx) (v-fN : (fN-fam0 (v-M))) → (Maybe (uN-fam0 (v-N)))

{- Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:313.1-313.36 -}
postulate demote-- : ∀ (v-M : M) (v-N : N) (v-fN : (fN-fam0 (v-M))) → (List (fN-fam0 (v-N)))

{- Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:314.1-314.37 -}
postulate promote-- : ∀ (v-M : M) (v-N : N) (v-fN : (fN-fam0 (v-M))) → (List (fN-fam0 (v-N)))

{- Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:315.1-315.91 -}
postulate convert-- : ∀ (v-M : M) (v-N : N) (v-sx : sx) (v-iN : (uN-fam0 (v-M))) → (fN-fam0 (v-N))

{- Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:316.1-316.88 -}
postulate narrow-- : ∀ (v-M : M) (v-N : N) (v-sx : sx) (v-iN : (uN-fam0 (v-M))) → (uN-fam0 (v-N))

{- Axiom Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:318.1-318.76 -}
postulate reinterpret-- : ∀ (numtype-1 : numtype) (numtype-2 : numtype) (v-num- : (num- numtype-1)) → (num- numtype-2)

{- Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:338.1-339.49 -}
{-# TERMINATING #-}
lpacknum- : (v-lanetype : lanetype) (v-num- : (num- (lunpack v-lanetype))) → (lane- v-lanetype)
lpacknum- lanetype-I32 c = c
lpacknum- lanetype-I64 c = c
lpacknum- lanetype-F32 c = c
lpacknum- lanetype-F64 c = c
lpacknum- lanetype-I8 c = (wrap-- (size (lunpack (lanetype-packtype packtype-I8))) (psize packtype-I8) c)
lpacknum- lanetype-I16 c = (wrap-- (size (lunpack (lanetype-packtype packtype-I16))) (psize packtype-I16) c)
lpacknum- v-lanetype v-num- = (Inhabited.default-val (inh-lane--fun v-lanetype))

{- Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:340.1-341.49 -}
{-# TERMINATING #-}
cpacknum- : (v-storagetype : storagetype) (v-lit- : (lit- (storagetype-consttype (unwrap! (cunpack v-storagetype))))) → (lit- v-storagetype)
cpacknum- storagetype-I32 c = c
cpacknum- storagetype-I64 c = c
cpacknum- storagetype-F32 c = c
cpacknum- storagetype-F64 c = c
cpacknum- storagetype-V128 c = c
cpacknum- I8 c = (wrap-- (size (lunpack (lanetype-packtype packtype-I8))) (psize packtype-I8) c)
cpacknum- I16 c = (wrap-- (size (lunpack (lanetype-packtype packtype-I16))) (psize packtype-I16) c)
cpacknum- v-storagetype v-lit- = (Inhabited.default-val (inh-lit--fun v-storagetype))

{- Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:350.1-351.53 -}
{-# TERMINATING #-}
lunpacknum- : (v-lanetype : lanetype) (v-lane- : (lane- v-lanetype)) → (num- (lunpack v-lanetype))
lunpacknum- lanetype-I32 c = c
lunpacknum- lanetype-I64 c = c
lunpacknum- lanetype-F32 c = c
lunpacknum- lanetype-F64 c = c
lunpacknum- lanetype-I8 c = (extend-- (psize packtype-I8) (size (lunpack (lanetype-packtype packtype-I8))) U c)
lunpacknum- lanetype-I16 c = (extend-- (psize packtype-I16) (size (lunpack (lanetype-packtype packtype-I16))) U c)
lunpacknum- v-lanetype v-lane- = (Inhabited.default-val (inh-num--fun (lunpack v-lanetype)))

{- Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:352.1-353.53 -}
{-# TERMINATING #-}
cunpacknum- : (v-storagetype : storagetype) (v-lit- : (lit- v-storagetype)) → (lit- (storagetype-consttype (unwrap! (cunpack v-storagetype))))
cunpacknum- storagetype-I32 c = c
cunpacknum- storagetype-I64 c = c
cunpacknum- storagetype-F32 c = c
cunpacknum- storagetype-F64 c = c
cunpacknum- storagetype-V128 c = c
cunpacknum- I8 c = (extend-- (psize packtype-I8) (size (lunpack (lanetype-packtype packtype-I8))) U c)
cunpacknum- I16 c = (extend-- (psize packtype-I16) (size (lunpack (lanetype-packtype packtype-I16))) U c)
cunpacknum- v-storagetype v-lit- = (Inhabited.default-val (inh-lit--fun (storagetype-consttype (unwrap! (cunpack v-storagetype)))))

{- Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:364.1-365.28 -}
{-# TERMINATING #-}
fun-unop- : (v-numtype : numtype) (v-unop- : (unop- v-numtype)) (v-num- : (num- v-numtype)) → (List (num- v-numtype))
fun-unop- numtype-I32 CLZ i = ((iclz- (sizenn (numtype-addrtype I32)) i) ∷ [])
fun-unop- numtype-I64 CLZ i = ((iclz- (sizenn (numtype-addrtype I64)) i) ∷ [])
fun-unop- numtype-I32 CTZ i = ((ictz- (sizenn (numtype-addrtype I32)) i) ∷ [])
fun-unop- numtype-I64 CTZ i = ((ictz- (sizenn (numtype-addrtype I64)) i) ∷ [])
fun-unop- numtype-I32 POPCNT i = ((ipopcnt- (sizenn (numtype-addrtype I32)) i) ∷ [])
fun-unop- numtype-I64 POPCNT i = ((ipopcnt- (sizenn (numtype-addrtype I64)) i) ∷ [])
fun-unop- numtype-I32 (EXTEND (mk-sz v-M)) i = ((iextend- (sizenn (numtype-addrtype I32)) v-M S i) ∷ [])
fun-unop- numtype-I64 (EXTEND (mk-sz v-M)) i = ((iextend- (sizenn (numtype-addrtype I64)) v-M S i) ∷ [])
fun-unop- F32 ABS f = (fabs- (sizenn (numtype-Fnn Fnn-F32)) f)
fun-unop- F64 ABS f = (fabs- (sizenn (numtype-Fnn Fnn-F64)) f)
fun-unop- F32 unop--NEG f = (fneg- (sizenn (numtype-Fnn Fnn-F32)) f)
fun-unop- F64 unop--NEG f = (fneg- (sizenn (numtype-Fnn Fnn-F64)) f)
fun-unop- F32 SQRT f = (fsqrt- (sizenn (numtype-Fnn Fnn-F32)) f)
fun-unop- F64 SQRT f = (fsqrt- (sizenn (numtype-Fnn Fnn-F64)) f)
fun-unop- F32 CEIL f = (fceil- (sizenn (numtype-Fnn Fnn-F32)) f)
fun-unop- F64 CEIL f = (fceil- (sizenn (numtype-Fnn Fnn-F64)) f)
fun-unop- F32 FLOOR f = (ffloor- (sizenn (numtype-Fnn Fnn-F32)) f)
fun-unop- F64 FLOOR f = (ffloor- (sizenn (numtype-Fnn Fnn-F64)) f)
fun-unop- F32 TRUNC f = (ftrunc- (sizenn (numtype-Fnn Fnn-F32)) f)
fun-unop- F64 TRUNC f = (ftrunc- (sizenn (numtype-Fnn Fnn-F64)) f)
fun-unop- F32 NEAREST f = (fnearest- (sizenn (numtype-Fnn Fnn-F32)) f)
fun-unop- F64 NEAREST f = (fnearest- (sizenn (numtype-Fnn Fnn-F64)) f)
fun-unop- v-numtype v-unop- v-num- = []

{- Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:366.1-367.32 -}
{-# TERMINATING #-}
fun-binop- : (v-numtype : numtype) (v-binop- : (binop- v-numtype)) (v-num- : (num- v-numtype)) (num--0 : (num- v-numtype)) → (List (num- v-numtype))
fun-binop- numtype-I32 ADD i-1 i-2 = ((iadd- (sizenn (numtype-addrtype I32)) i-1 i-2) ∷ [])
fun-binop- numtype-I64 ADD i-1 i-2 = ((iadd- (sizenn (numtype-addrtype I64)) i-1 i-2) ∷ [])
fun-binop- numtype-I32 binop--SUB i-1 i-2 = ((isub- (sizenn (numtype-addrtype I32)) i-1 i-2) ∷ [])
fun-binop- numtype-I64 binop--SUB i-1 i-2 = ((isub- (sizenn (numtype-addrtype I64)) i-1 i-2) ∷ [])
fun-binop- numtype-I32 MUL i-1 i-2 = ((imul- (sizenn (numtype-addrtype I32)) i-1 i-2) ∷ [])
fun-binop- numtype-I64 MUL i-1 i-2 = ((imul- (sizenn (numtype-addrtype I64)) i-1 i-2) ∷ [])
fun-binop- numtype-I32 (DIV v-sx) i-1 i-2 = (fromMaybe (idiv- (sizenn (numtype-addrtype I32)) v-sx i-1 i-2))
fun-binop- numtype-I64 (DIV v-sx) i-1 i-2 = (fromMaybe (idiv- (sizenn (numtype-addrtype I64)) v-sx i-1 i-2))
fun-binop- numtype-I32 (REM v-sx) i-1 i-2 = (fromMaybe (irem- (sizenn (numtype-addrtype I32)) v-sx i-1 i-2))
fun-binop- numtype-I64 (REM v-sx) i-1 i-2 = (fromMaybe (irem- (sizenn (numtype-addrtype I64)) v-sx i-1 i-2))
fun-binop- numtype-I32 AND i-1 i-2 = ((iand- (sizenn (numtype-addrtype I32)) i-1 i-2) ∷ [])
fun-binop- numtype-I64 AND i-1 i-2 = ((iand- (sizenn (numtype-addrtype I64)) i-1 i-2) ∷ [])
fun-binop- numtype-I32 OR i-1 i-2 = ((ior- (sizenn (numtype-addrtype I32)) i-1 i-2) ∷ [])
fun-binop- numtype-I64 OR i-1 i-2 = ((ior- (sizenn (numtype-addrtype I64)) i-1 i-2) ∷ [])
fun-binop- numtype-I32 XOR i-1 i-2 = ((ixor- (sizenn (numtype-addrtype I32)) i-1 i-2) ∷ [])
fun-binop- numtype-I64 XOR i-1 i-2 = ((ixor- (sizenn (numtype-addrtype I64)) i-1 i-2) ∷ [])
fun-binop- numtype-I32 SHL i-1 i-2 = ((ishl- (sizenn (numtype-addrtype I32)) i-1 (mk-uN (proj-uN-0 (size (numtype-addrtype I32)) i-2))) ∷ [])
fun-binop- numtype-I64 SHL i-1 i-2 = ((ishl- (sizenn (numtype-addrtype I64)) i-1 (mk-uN (proj-uN-0 (size (numtype-addrtype I64)) i-2))) ∷ [])
fun-binop- numtype-I32 (SHR v-sx) i-1 i-2 = ((ishr- (sizenn (numtype-addrtype I32)) v-sx i-1 (mk-uN (proj-uN-0 (size (numtype-addrtype I32)) i-2))) ∷ [])
fun-binop- numtype-I64 (SHR v-sx) i-1 i-2 = ((ishr- (sizenn (numtype-addrtype I64)) v-sx i-1 (mk-uN (proj-uN-0 (size (numtype-addrtype I64)) i-2))) ∷ [])
fun-binop- numtype-I32 ROTL i-1 i-2 = ((irotl- (sizenn (numtype-addrtype I32)) i-1 i-2) ∷ [])
fun-binop- numtype-I64 ROTL i-1 i-2 = ((irotl- (sizenn (numtype-addrtype I64)) i-1 i-2) ∷ [])
fun-binop- numtype-I32 ROTR i-1 i-2 = ((irotr- (sizenn (numtype-addrtype I32)) i-1 i-2) ∷ [])
fun-binop- numtype-I64 ROTR i-1 i-2 = ((irotr- (sizenn (numtype-addrtype I64)) i-1 i-2) ∷ [])
fun-binop- F32 ADD f-1 f-2 = (fadd- (sizenn (numtype-Fnn Fnn-F32)) f-1 f-2)
fun-binop- F64 ADD f-1 f-2 = (fadd- (sizenn (numtype-Fnn Fnn-F64)) f-1 f-2)
fun-binop- F32 binop--SUB f-1 f-2 = (fsub- (sizenn (numtype-Fnn Fnn-F32)) f-1 f-2)
fun-binop- F64 binop--SUB f-1 f-2 = (fsub- (sizenn (numtype-Fnn Fnn-F64)) f-1 f-2)
fun-binop- F32 MUL f-1 f-2 = (fmul- (sizenn (numtype-Fnn Fnn-F32)) f-1 f-2)
fun-binop- F64 MUL f-1 f-2 = (fmul- (sizenn (numtype-Fnn Fnn-F64)) f-1 f-2)
fun-binop- F32 DIV f-1 f-2 = (fdiv- (sizenn (numtype-Fnn Fnn-F32)) f-1 f-2)
fun-binop- F64 DIV f-1 f-2 = (fdiv- (sizenn (numtype-Fnn Fnn-F64)) f-1 f-2)
fun-binop- F32 MIN f-1 f-2 = (fmin- (sizenn (numtype-Fnn Fnn-F32)) f-1 f-2)
fun-binop- F64 MIN f-1 f-2 = (fmin- (sizenn (numtype-Fnn Fnn-F64)) f-1 f-2)
fun-binop- F32 MAX f-1 f-2 = (fmax- (sizenn (numtype-Fnn Fnn-F32)) f-1 f-2)
fun-binop- F64 MAX f-1 f-2 = (fmax- (sizenn (numtype-Fnn Fnn-F64)) f-1 f-2)
fun-binop- F32 COPYSIGN f-1 f-2 = (fcopysign- (sizenn (numtype-Fnn Fnn-F32)) f-1 f-2)
fun-binop- F64 COPYSIGN f-1 f-2 = (fcopysign- (sizenn (numtype-Fnn Fnn-F64)) f-1 f-2)
fun-binop- v-numtype v-binop- v-num- num--0 = []

{- Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:368.1-369.28 -}
{-# TERMINATING #-}
fun-testop- : (v-numtype : numtype) (v-testop- : (testop- v-numtype)) (v-num- : (num- v-numtype)) → u32
fun-testop- numtype-I32 EQZ i = (ieqz- (sizenn (numtype-addrtype I32)) i)
fun-testop- numtype-I64 EQZ i = (ieqz- (sizenn (numtype-addrtype I64)) i)
fun-testop- v-numtype v-testop- v-num- = default-val

{- Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:370.1-371.32 -}
{-# TERMINATING #-}
fun-relop- : (v-numtype : numtype) (v-relop- : (relop- v-numtype)) (v-num- : (num- v-numtype)) (num--0 : (num- v-numtype)) → u32
fun-relop- numtype-I32 relop--EQ i-1 i-2 = (ieq- (sizenn (numtype-addrtype I32)) i-1 i-2)
fun-relop- numtype-I64 relop--EQ i-1 i-2 = (ieq- (sizenn (numtype-addrtype I64)) i-1 i-2)
fun-relop- numtype-I32 NE i-1 i-2 = (ine- (sizenn (numtype-addrtype I32)) i-1 i-2)
fun-relop- numtype-I64 NE i-1 i-2 = (ine- (sizenn (numtype-addrtype I64)) i-1 i-2)
fun-relop- numtype-I32 (LT v-sx) i-1 i-2 = (ilt- (sizenn (numtype-addrtype I32)) v-sx i-1 i-2)
fun-relop- numtype-I64 (LT v-sx) i-1 i-2 = (ilt- (sizenn (numtype-addrtype I64)) v-sx i-1 i-2)
fun-relop- numtype-I32 (GT v-sx) i-1 i-2 = (igt- (sizenn (numtype-addrtype I32)) v-sx i-1 i-2)
fun-relop- numtype-I64 (GT v-sx) i-1 i-2 = (igt- (sizenn (numtype-addrtype I64)) v-sx i-1 i-2)
fun-relop- numtype-I32 (LE v-sx) i-1 i-2 = (ile- (sizenn (numtype-addrtype I32)) v-sx i-1 i-2)
fun-relop- numtype-I64 (LE v-sx) i-1 i-2 = (ile- (sizenn (numtype-addrtype I64)) v-sx i-1 i-2)
fun-relop- numtype-I32 (GE v-sx) i-1 i-2 = (ige- (sizenn (numtype-addrtype I32)) v-sx i-1 i-2)
fun-relop- numtype-I64 (GE v-sx) i-1 i-2 = (ige- (sizenn (numtype-addrtype I64)) v-sx i-1 i-2)
fun-relop- F32 relop--EQ f-1 f-2 = (feq- (sizenn (numtype-Fnn Fnn-F32)) f-1 f-2)
fun-relop- F64 relop--EQ f-1 f-2 = (feq- (sizenn (numtype-Fnn Fnn-F64)) f-1 f-2)
fun-relop- F32 NE f-1 f-2 = (fne- (sizenn (numtype-Fnn Fnn-F32)) f-1 f-2)
fun-relop- F64 NE f-1 f-2 = (fne- (sizenn (numtype-Fnn Fnn-F64)) f-1 f-2)
fun-relop- F32 LT f-1 f-2 = (flt- (sizenn (numtype-Fnn Fnn-F32)) f-1 f-2)
fun-relop- F64 LT f-1 f-2 = (flt- (sizenn (numtype-Fnn Fnn-F64)) f-1 f-2)
fun-relop- F32 GT f-1 f-2 = (fgt- (sizenn (numtype-Fnn Fnn-F32)) f-1 f-2)
fun-relop- F64 GT f-1 f-2 = (fgt- (sizenn (numtype-Fnn Fnn-F64)) f-1 f-2)
fun-relop- F32 LE f-1 f-2 = (fle- (sizenn (numtype-Fnn Fnn-F32)) f-1 f-2)
fun-relop- F64 LE f-1 f-2 = (fle- (sizenn (numtype-Fnn Fnn-F64)) f-1 f-2)
fun-relop- F32 GE f-1 f-2 = (fge- (sizenn (numtype-Fnn Fnn-F32)) f-1 f-2)
fun-relop- F64 GE f-1 f-2 = (fge- (sizenn (numtype-Fnn Fnn-F64)) f-1 f-2)
fun-relop- v-numtype v-relop- v-num- num--0 = default-val

{- Auxiliary Definition at: ../specification/wasm-3.0/3.1-numerics.scalar.spectec:372.1-373.32 -}
postulate fun-cvtop-- : ∀ (numtype-1 : numtype) (numtype-2 : numtype) (v-cvtop-- : (cvtop-- numtype-1 numtype-2)) (v-num- : (num- numtype-1)) → (List (num- numtype-2))

{- Axiom Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:10.1-10.84 -}
postulate lanes- : ∀ (v-shape : shape) (v-vec- : (uN-fam0 (128))) → (List (lane- (fun-lanetype v-shape)))

{- Axiom Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:12.1-13.37 -}
postulate inv-lanes- : ∀ (v-shape : shape) (var-0-lst : (List (lane- (fun-lanetype v-shape)))) → (uN-fam0 (128))

{- Auxiliary Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:19.1-19.66 -}
{-# TERMINATING #-}
zeroop : (shape-1 : shape) (shape-2 : shape) (v-vcvtop-- : (vcvtop-- shape-1 shape-2)) → (Maybe zero')
zeroop (X lanetype-I32 (mk-dim M-1)) (X lanetype-I32 (mk-dim M-2)) (vcvtop---EXTEND v-half v-sx) = nothing
zeroop (X lanetype-I64 (mk-dim M-1)) (X lanetype-I32 (mk-dim M-2)) (vcvtop---EXTEND v-half v-sx) = nothing
zeroop (X lanetype-I8 (mk-dim M-1)) (X lanetype-I32 (mk-dim M-2)) (vcvtop---EXTEND v-half v-sx) = nothing
zeroop (X lanetype-I16 (mk-dim M-1)) (X lanetype-I32 (mk-dim M-2)) (vcvtop---EXTEND v-half v-sx) = nothing
zeroop (X lanetype-I32 (mk-dim M-1)) (X lanetype-I64 (mk-dim M-2)) (vcvtop---EXTEND v-half v-sx) = nothing
zeroop (X lanetype-I64 (mk-dim M-1)) (X lanetype-I64 (mk-dim M-2)) (vcvtop---EXTEND v-half v-sx) = nothing
zeroop (X lanetype-I8 (mk-dim M-1)) (X lanetype-I64 (mk-dim M-2)) (vcvtop---EXTEND v-half v-sx) = nothing
zeroop (X lanetype-I16 (mk-dim M-1)) (X lanetype-I64 (mk-dim M-2)) (vcvtop---EXTEND v-half v-sx) = nothing
zeroop (X lanetype-I32 (mk-dim M-1)) (X lanetype-I8 (mk-dim M-2)) (vcvtop---EXTEND v-half v-sx) = nothing
zeroop (X lanetype-I64 (mk-dim M-1)) (X lanetype-I8 (mk-dim M-2)) (vcvtop---EXTEND v-half v-sx) = nothing
zeroop (X lanetype-I8 (mk-dim M-1)) (X lanetype-I8 (mk-dim M-2)) (vcvtop---EXTEND v-half v-sx) = nothing
zeroop (X lanetype-I16 (mk-dim M-1)) (X lanetype-I8 (mk-dim M-2)) (vcvtop---EXTEND v-half v-sx) = nothing
zeroop (X lanetype-I32 (mk-dim M-1)) (X lanetype-I16 (mk-dim M-2)) (vcvtop---EXTEND v-half v-sx) = nothing
zeroop (X lanetype-I64 (mk-dim M-1)) (X lanetype-I16 (mk-dim M-2)) (vcvtop---EXTEND v-half v-sx) = nothing
zeroop (X lanetype-I8 (mk-dim M-1)) (X lanetype-I16 (mk-dim M-2)) (vcvtop---EXTEND v-half v-sx) = nothing
zeroop (X lanetype-I16 (mk-dim M-1)) (X lanetype-I16 (mk-dim M-2)) (vcvtop---EXTEND v-half v-sx) = nothing
zeroop (X lanetype-I32 (mk-dim M-1)) (X lanetype-F32 (mk-dim M-2)) (vcvtop---CONVERT half-opt v-sx) = nothing
zeroop (X lanetype-I64 (mk-dim M-1)) (X lanetype-F32 (mk-dim M-2)) (vcvtop---CONVERT half-opt v-sx) = nothing
zeroop (X lanetype-I8 (mk-dim M-1)) (X lanetype-F32 (mk-dim M-2)) (vcvtop---CONVERT half-opt v-sx) = nothing
zeroop (X lanetype-I16 (mk-dim M-1)) (X lanetype-F32 (mk-dim M-2)) (vcvtop---CONVERT half-opt v-sx) = nothing
zeroop (X lanetype-I32 (mk-dim M-1)) (X lanetype-F64 (mk-dim M-2)) (vcvtop---CONVERT half-opt v-sx) = nothing
zeroop (X lanetype-I64 (mk-dim M-1)) (X lanetype-F64 (mk-dim M-2)) (vcvtop---CONVERT half-opt v-sx) = nothing
zeroop (X lanetype-I8 (mk-dim M-1)) (X lanetype-F64 (mk-dim M-2)) (vcvtop---CONVERT half-opt v-sx) = nothing
zeroop (X lanetype-I16 (mk-dim M-1)) (X lanetype-F64 (mk-dim M-2)) (vcvtop---CONVERT half-opt v-sx) = nothing
zeroop (X lanetype-F32 (mk-dim M-1)) (X lanetype-I32 (mk-dim M-2)) (vcvtop---TRUNC-SAT v-sx zero-opt) = zero-opt
zeroop (X lanetype-F64 (mk-dim M-1)) (X lanetype-I32 (mk-dim M-2)) (vcvtop---TRUNC-SAT v-sx zero-opt) = zero-opt
zeroop (X lanetype-F32 (mk-dim M-1)) (X lanetype-I64 (mk-dim M-2)) (vcvtop---TRUNC-SAT v-sx zero-opt) = zero-opt
zeroop (X lanetype-F64 (mk-dim M-1)) (X lanetype-I64 (mk-dim M-2)) (vcvtop---TRUNC-SAT v-sx zero-opt) = zero-opt
zeroop (X lanetype-F32 (mk-dim M-1)) (X lanetype-I8 (mk-dim M-2)) (vcvtop---TRUNC-SAT v-sx zero-opt) = zero-opt
zeroop (X lanetype-F64 (mk-dim M-1)) (X lanetype-I8 (mk-dim M-2)) (vcvtop---TRUNC-SAT v-sx zero-opt) = zero-opt
zeroop (X lanetype-F32 (mk-dim M-1)) (X lanetype-I16 (mk-dim M-2)) (vcvtop---TRUNC-SAT v-sx zero-opt) = zero-opt
zeroop (X lanetype-F64 (mk-dim M-1)) (X lanetype-I16 (mk-dim M-2)) (vcvtop---TRUNC-SAT v-sx zero-opt) = zero-opt
zeroop (X lanetype-F32 (mk-dim M-1)) (X lanetype-I32 (mk-dim M-2)) (RELAXED-TRUNC v-sx zero-opt) = zero-opt
zeroop (X lanetype-F64 (mk-dim M-1)) (X lanetype-I32 (mk-dim M-2)) (RELAXED-TRUNC v-sx zero-opt) = zero-opt
zeroop (X lanetype-F32 (mk-dim M-1)) (X lanetype-I64 (mk-dim M-2)) (RELAXED-TRUNC v-sx zero-opt) = zero-opt
zeroop (X lanetype-F64 (mk-dim M-1)) (X lanetype-I64 (mk-dim M-2)) (RELAXED-TRUNC v-sx zero-opt) = zero-opt
zeroop (X lanetype-F32 (mk-dim M-1)) (X lanetype-I8 (mk-dim M-2)) (RELAXED-TRUNC v-sx zero-opt) = zero-opt
zeroop (X lanetype-F64 (mk-dim M-1)) (X lanetype-I8 (mk-dim M-2)) (RELAXED-TRUNC v-sx zero-opt) = zero-opt
zeroop (X lanetype-F32 (mk-dim M-1)) (X lanetype-I16 (mk-dim M-2)) (RELAXED-TRUNC v-sx zero-opt) = zero-opt
zeroop (X lanetype-F64 (mk-dim M-1)) (X lanetype-I16 (mk-dim M-2)) (RELAXED-TRUNC v-sx zero-opt) = zero-opt
zeroop (X lanetype-F32 (mk-dim M-1)) (X lanetype-F32 (mk-dim M-2)) (vcvtop---DEMOTE v-zero) = (just v-zero)
zeroop (X lanetype-F64 (mk-dim M-1)) (X lanetype-F32 (mk-dim M-2)) (vcvtop---DEMOTE v-zero) = (just v-zero)
zeroop (X lanetype-F32 (mk-dim M-1)) (X lanetype-F64 (mk-dim M-2)) (vcvtop---DEMOTE v-zero) = (just v-zero)
zeroop (X lanetype-F64 (mk-dim M-1)) (X lanetype-F64 (mk-dim M-2)) (vcvtop---DEMOTE v-zero) = (just v-zero)
zeroop (X lanetype-F32 (mk-dim M-1)) (X lanetype-F32 (mk-dim M-2)) PROMOTELOW = nothing
zeroop (X lanetype-F64 (mk-dim M-1)) (X lanetype-F32 (mk-dim M-2)) PROMOTELOW = nothing
zeroop (X lanetype-F32 (mk-dim M-1)) (X lanetype-F64 (mk-dim M-2)) PROMOTELOW = nothing
zeroop (X lanetype-F64 (mk-dim M-1)) (X lanetype-F64 (mk-dim M-2)) PROMOTELOW = nothing
zeroop shape-1 shape-2 v-vcvtop-- = nothing

{- Auxiliary Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:27.1-27.66 -}
{-# TERMINATING #-}
halfop : (shape-1 : shape) (shape-2 : shape) (v-vcvtop-- : (vcvtop-- shape-1 shape-2)) → (Maybe half)
halfop (X lanetype-I32 (mk-dim M-1)) (X lanetype-I32 (mk-dim M-2)) (vcvtop---EXTEND v-half v-sx) = (just v-half)
halfop (X lanetype-I64 (mk-dim M-1)) (X lanetype-I32 (mk-dim M-2)) (vcvtop---EXTEND v-half v-sx) = (just v-half)
halfop (X lanetype-I8 (mk-dim M-1)) (X lanetype-I32 (mk-dim M-2)) (vcvtop---EXTEND v-half v-sx) = (just v-half)
halfop (X lanetype-I16 (mk-dim M-1)) (X lanetype-I32 (mk-dim M-2)) (vcvtop---EXTEND v-half v-sx) = (just v-half)
halfop (X lanetype-I32 (mk-dim M-1)) (X lanetype-I64 (mk-dim M-2)) (vcvtop---EXTEND v-half v-sx) = (just v-half)
halfop (X lanetype-I64 (mk-dim M-1)) (X lanetype-I64 (mk-dim M-2)) (vcvtop---EXTEND v-half v-sx) = (just v-half)
halfop (X lanetype-I8 (mk-dim M-1)) (X lanetype-I64 (mk-dim M-2)) (vcvtop---EXTEND v-half v-sx) = (just v-half)
halfop (X lanetype-I16 (mk-dim M-1)) (X lanetype-I64 (mk-dim M-2)) (vcvtop---EXTEND v-half v-sx) = (just v-half)
halfop (X lanetype-I32 (mk-dim M-1)) (X lanetype-I8 (mk-dim M-2)) (vcvtop---EXTEND v-half v-sx) = (just v-half)
halfop (X lanetype-I64 (mk-dim M-1)) (X lanetype-I8 (mk-dim M-2)) (vcvtop---EXTEND v-half v-sx) = (just v-half)
halfop (X lanetype-I8 (mk-dim M-1)) (X lanetype-I8 (mk-dim M-2)) (vcvtop---EXTEND v-half v-sx) = (just v-half)
halfop (X lanetype-I16 (mk-dim M-1)) (X lanetype-I8 (mk-dim M-2)) (vcvtop---EXTEND v-half v-sx) = (just v-half)
halfop (X lanetype-I32 (mk-dim M-1)) (X lanetype-I16 (mk-dim M-2)) (vcvtop---EXTEND v-half v-sx) = (just v-half)
halfop (X lanetype-I64 (mk-dim M-1)) (X lanetype-I16 (mk-dim M-2)) (vcvtop---EXTEND v-half v-sx) = (just v-half)
halfop (X lanetype-I8 (mk-dim M-1)) (X lanetype-I16 (mk-dim M-2)) (vcvtop---EXTEND v-half v-sx) = (just v-half)
halfop (X lanetype-I16 (mk-dim M-1)) (X lanetype-I16 (mk-dim M-2)) (vcvtop---EXTEND v-half v-sx) = (just v-half)
halfop (X lanetype-I32 (mk-dim M-1)) (X lanetype-F32 (mk-dim M-2)) (vcvtop---CONVERT half-opt v-sx) = half-opt
halfop (X lanetype-I64 (mk-dim M-1)) (X lanetype-F32 (mk-dim M-2)) (vcvtop---CONVERT half-opt v-sx) = half-opt
halfop (X lanetype-I8 (mk-dim M-1)) (X lanetype-F32 (mk-dim M-2)) (vcvtop---CONVERT half-opt v-sx) = half-opt
halfop (X lanetype-I16 (mk-dim M-1)) (X lanetype-F32 (mk-dim M-2)) (vcvtop---CONVERT half-opt v-sx) = half-opt
halfop (X lanetype-I32 (mk-dim M-1)) (X lanetype-F64 (mk-dim M-2)) (vcvtop---CONVERT half-opt v-sx) = half-opt
halfop (X lanetype-I64 (mk-dim M-1)) (X lanetype-F64 (mk-dim M-2)) (vcvtop---CONVERT half-opt v-sx) = half-opt
halfop (X lanetype-I8 (mk-dim M-1)) (X lanetype-F64 (mk-dim M-2)) (vcvtop---CONVERT half-opt v-sx) = half-opt
halfop (X lanetype-I16 (mk-dim M-1)) (X lanetype-F64 (mk-dim M-2)) (vcvtop---CONVERT half-opt v-sx) = half-opt
halfop (X lanetype-F32 (mk-dim M-1)) (X lanetype-I32 (mk-dim M-2)) (vcvtop---TRUNC-SAT v-sx zero-opt) = nothing
halfop (X lanetype-F64 (mk-dim M-1)) (X lanetype-I32 (mk-dim M-2)) (vcvtop---TRUNC-SAT v-sx zero-opt) = nothing
halfop (X lanetype-F32 (mk-dim M-1)) (X lanetype-I64 (mk-dim M-2)) (vcvtop---TRUNC-SAT v-sx zero-opt) = nothing
halfop (X lanetype-F64 (mk-dim M-1)) (X lanetype-I64 (mk-dim M-2)) (vcvtop---TRUNC-SAT v-sx zero-opt) = nothing
halfop (X lanetype-F32 (mk-dim M-1)) (X lanetype-I8 (mk-dim M-2)) (vcvtop---TRUNC-SAT v-sx zero-opt) = nothing
halfop (X lanetype-F64 (mk-dim M-1)) (X lanetype-I8 (mk-dim M-2)) (vcvtop---TRUNC-SAT v-sx zero-opt) = nothing
halfop (X lanetype-F32 (mk-dim M-1)) (X lanetype-I16 (mk-dim M-2)) (vcvtop---TRUNC-SAT v-sx zero-opt) = nothing
halfop (X lanetype-F64 (mk-dim M-1)) (X lanetype-I16 (mk-dim M-2)) (vcvtop---TRUNC-SAT v-sx zero-opt) = nothing
halfop (X lanetype-F32 (mk-dim M-1)) (X lanetype-I32 (mk-dim M-2)) (RELAXED-TRUNC v-sx zero-opt) = nothing
halfop (X lanetype-F64 (mk-dim M-1)) (X lanetype-I32 (mk-dim M-2)) (RELAXED-TRUNC v-sx zero-opt) = nothing
halfop (X lanetype-F32 (mk-dim M-1)) (X lanetype-I64 (mk-dim M-2)) (RELAXED-TRUNC v-sx zero-opt) = nothing
halfop (X lanetype-F64 (mk-dim M-1)) (X lanetype-I64 (mk-dim M-2)) (RELAXED-TRUNC v-sx zero-opt) = nothing
halfop (X lanetype-F32 (mk-dim M-1)) (X lanetype-I8 (mk-dim M-2)) (RELAXED-TRUNC v-sx zero-opt) = nothing
halfop (X lanetype-F64 (mk-dim M-1)) (X lanetype-I8 (mk-dim M-2)) (RELAXED-TRUNC v-sx zero-opt) = nothing
halfop (X lanetype-F32 (mk-dim M-1)) (X lanetype-I16 (mk-dim M-2)) (RELAXED-TRUNC v-sx zero-opt) = nothing
halfop (X lanetype-F64 (mk-dim M-1)) (X lanetype-I16 (mk-dim M-2)) (RELAXED-TRUNC v-sx zero-opt) = nothing
halfop (X lanetype-F32 (mk-dim M-1)) (X lanetype-F32 (mk-dim M-2)) (vcvtop---DEMOTE v-zero) = nothing
halfop (X lanetype-F64 (mk-dim M-1)) (X lanetype-F32 (mk-dim M-2)) (vcvtop---DEMOTE v-zero) = nothing
halfop (X lanetype-F32 (mk-dim M-1)) (X lanetype-F64 (mk-dim M-2)) (vcvtop---DEMOTE v-zero) = nothing
halfop (X lanetype-F64 (mk-dim M-1)) (X lanetype-F64 (mk-dim M-2)) (vcvtop---DEMOTE v-zero) = nothing
halfop (X lanetype-F32 (mk-dim M-1)) (X lanetype-F32 (mk-dim M-2)) PROMOTELOW = (just LOW)
halfop (X lanetype-F64 (mk-dim M-1)) (X lanetype-F32 (mk-dim M-2)) PROMOTELOW = (just LOW)
halfop (X lanetype-F32 (mk-dim M-1)) (X lanetype-F64 (mk-dim M-2)) PROMOTELOW = (just LOW)
halfop (X lanetype-F64 (mk-dim M-1)) (X lanetype-F64 (mk-dim M-2)) PROMOTELOW = (just LOW)
halfop shape-1 shape-2 v-vcvtop-- = nothing

{- Auxiliary Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:35.1-35.32 -}
{-# TERMINATING #-}
fun-half : (v-half : half) (nat : ℕ) (nat-0 : ℕ) → ℕ
fun-half LOW i j = i
fun-half HIGH i j = j
fun-half v-half nat nat-0 = default-val

{- Auxiliary Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:40.1-40.46 -}
{-# TERMINATING #-}
iswizzle-lane- : (v-N : N) (var-0-lst : (List (uN-fam0 (v-N)))) (v-iN : (uN-fam0 (v-N))) → (uN-fam0 (v-N))
iswizzle-lane- v-N c-lst i = (if ((proj-uN-0 v-N i) <? (length c-lst)) then (c-lst [ (proj-uN-0 v-N i) ]!) else (mk-uN 0))

{- Auxiliary Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:41.1-41.54 -}
{-# TERMINATING #-}
irelaxed-swizzle-lane- : (v-N : N) (var-0-lst : (List (uN-fam0 (v-N)))) (v-iN : (uN-fam0 (v-N))) → (uN-fam0 (v-N))
irelaxed-swizzle-lane- v-N c-lst i = (if ((proj-uN-0 v-N i) <? (length c-lst)) then (c-lst [ (proj-uN-0 v-N i) ]!) else (if ((signed- v-N (proj-uN-0 v-N i)) <? (coerce {B = ℕ} 0)) then (mk-uN 0) else (fun-relaxed2 (R-swizzle ) (uN-fam0 (v-N)) (mk-uN 0) (c-lst [ ((proj-uN-0 v-N i) % (length c-lst)) ]!))))

{- Auxiliary Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:54.1-54.87 -}
{-# TERMINATING #-}
ivunop- : (v-shape : shape) (f- : (v-N : N) → (v-iN : (uN-fam0 (v-N))) → (uN-fam0 (v-N))) (v-vec- : (uN-fam0 (128))) → (Maybe (List (uN-fam0 (128))))
ivunop- (X lanetype-I32 (mk-dim v-M)) f- v-1 = let c-1-lst = (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) v-1) in let c-lst = (map (λ (c-1-2 : (uN-fam0 (32))) → (f- (lsizenn (lanetype-Jnn Jnn-I32)) c-1-2)) c-1-lst) in (just ((inv-lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) c-lst) ∷ []))
ivunop- (X lanetype-I64 (mk-dim v-M)) f- v-1 = let c-1-lst = (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) v-1) in let c-lst = (map (λ (c-1-4 : (uN-fam0 (64))) → (f- (lsizenn (lanetype-Jnn Jnn-I64)) c-1-4)) c-1-lst) in (just ((inv-lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) c-lst) ∷ []))
ivunop- (X lanetype-I8 (mk-dim v-M)) f- v-1 = let c-1-lst = (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) v-1) in let c-lst = (map (λ (c-1-6 : (uN-fam0 (8))) → (f- (lsizenn (lanetype-Jnn Jnn-I8)) c-1-6)) c-1-lst) in (just ((inv-lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) c-lst) ∷ []))
ivunop- (X lanetype-I16 (mk-dim v-M)) f- v-1 = let c-1-lst = (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) v-1) in let c-lst = (map (λ (c-1-8 : (uN-fam0 (16))) → (f- (lsizenn (lanetype-Jnn Jnn-I16)) c-1-8)) c-1-lst) in (just ((inv-lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) c-lst) ∷ []))
ivunop- x0 f- x2 = nothing

{- Auxiliary Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:55.1-55.74 -}
{-# TERMINATING #-}
fvunop- : (v-shape : shape) (f- : (v-N : N) → (v-fN : (fN-fam0 (v-N))) → (List (fN-fam0 (v-N)))) (v-vec- : (uN-fam0 (128))) → (List (uN-fam0 (128)))
fvunop- (X lanetype-F32 (mk-dim v-M)) f- v-1 = let c-1-lst = (lanes- (X (lanetype-Fnn Fnn-F32) (mk-dim v-M)) v-1) in let c-lst-lst = (setproduct- (fN-fam0 (32)) (map (λ (c-1-10 : (fN-fam0 (32))) → (f- (sizenn (numtype-Fnn Fnn-F32)) c-1-10)) c-1-lst)) in (map (λ (c-lst-2 : (List (fN-fam0 (32)))) → (inv-lanes- (X (lanetype-Fnn Fnn-F32) (mk-dim v-M)) c-lst-2)) c-lst-lst)
fvunop- (X lanetype-F64 (mk-dim v-M)) f- v-1 = let c-1-lst = (lanes- (X (lanetype-Fnn Fnn-F64) (mk-dim v-M)) v-1) in let c-lst-lst = (setproduct- (fN-fam0 (64)) (map (λ (c-1-12 : (fN-fam0 (64))) → (f- (sizenn (numtype-Fnn Fnn-F64)) c-1-12)) c-1-lst)) in (map (λ (c-lst-4 : (List (fN-fam0 (64)))) → (inv-lanes- (X (lanetype-Fnn Fnn-F64) (mk-dim v-M)) c-lst-4)) c-lst-lst)
fvunop- v-shape f- v-vec- = []

{- Auxiliary Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:57.1-57.107 -}
{-# TERMINATING #-}
ivbinop- : (v-shape : shape) (f- : (v-N : N) → (v-iN : (uN-fam0 (v-N))) → (v-iN : (uN-fam0 (v-N))) → (uN-fam0 (v-N))) (v-vec- : (uN-fam0 (128))) (vec--0 : (uN-fam0 (128))) → (Maybe (List (uN-fam0 (128))))
ivbinop- (X lanetype-I32 (mk-dim v-M)) f- v-1 v-2 = let c-1-lst = (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) v-1) in let c-2-lst = (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) v-2) in let c-lst = (zipWith (λ (c-1-14 : (uN-fam0 (32))) (c-2-2 : (uN-fam0 (32))) → (f- (lsizenn (lanetype-Jnn Jnn-I32)) c-1-14 c-2-2)) c-1-lst c-2-lst) in (just ((inv-lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) c-lst) ∷ []))
ivbinop- (X lanetype-I64 (mk-dim v-M)) f- v-1 v-2 = let c-1-lst = (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) v-1) in let c-2-lst = (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) v-2) in let c-lst = (zipWith (λ (c-1-16 : (uN-fam0 (64))) (c-2-4 : (uN-fam0 (64))) → (f- (lsizenn (lanetype-Jnn Jnn-I64)) c-1-16 c-2-4)) c-1-lst c-2-lst) in (just ((inv-lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) c-lst) ∷ []))
ivbinop- (X lanetype-I8 (mk-dim v-M)) f- v-1 v-2 = let c-1-lst = (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) v-1) in let c-2-lst = (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) v-2) in let c-lst = (zipWith (λ (c-1-18 : (uN-fam0 (8))) (c-2-6 : (uN-fam0 (8))) → (f- (lsizenn (lanetype-Jnn Jnn-I8)) c-1-18 c-2-6)) c-1-lst c-2-lst) in (just ((inv-lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) c-lst) ∷ []))
ivbinop- (X lanetype-I16 (mk-dim v-M)) f- v-1 v-2 = let c-1-lst = (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) v-1) in let c-2-lst = (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) v-2) in let c-lst = (zipWith (λ (c-1-20 : (uN-fam0 (16))) (c-2-8 : (uN-fam0 (16))) → (f- (lsizenn (lanetype-Jnn Jnn-I16)) c-1-20 c-2-8)) c-1-lst c-2-lst) in (just ((inv-lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) c-lst) ∷ []))
ivbinop- x0 f- x2 x3 = nothing

{- Auxiliary Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:58.1-58.117 -}
{-# TERMINATING #-}
ivbinopsx- : (v-shape : shape) (f- : (v-N : N) → (v-sx : sx) → (v-iN : (uN-fam0 (v-N))) → (v-iN : (uN-fam0 (v-N))) → (uN-fam0 (v-N))) (v-sx : sx) (v-vec- : (uN-fam0 (128))) (vec--0 : (uN-fam0 (128))) → (Maybe (List (uN-fam0 (128))))
ivbinopsx- (X lanetype-I32 (mk-dim v-M)) f- v-sx v-1 v-2 = let c-1-lst = (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) v-1) in let c-2-lst = (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) v-2) in let c-lst = (zipWith (λ (c-1-22 : (uN-fam0 (32))) (c-2-10 : (uN-fam0 (32))) → (f- (lsizenn (lanetype-Jnn Jnn-I32)) v-sx c-1-22 c-2-10)) c-1-lst c-2-lst) in (just ((inv-lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) c-lst) ∷ []))
ivbinopsx- (X lanetype-I64 (mk-dim v-M)) f- v-sx v-1 v-2 = let c-1-lst = (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) v-1) in let c-2-lst = (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) v-2) in let c-lst = (zipWith (λ (c-1-24 : (uN-fam0 (64))) (c-2-12 : (uN-fam0 (64))) → (f- (lsizenn (lanetype-Jnn Jnn-I64)) v-sx c-1-24 c-2-12)) c-1-lst c-2-lst) in (just ((inv-lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) c-lst) ∷ []))
ivbinopsx- (X lanetype-I8 (mk-dim v-M)) f- v-sx v-1 v-2 = let c-1-lst = (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) v-1) in let c-2-lst = (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) v-2) in let c-lst = (zipWith (λ (c-1-26 : (uN-fam0 (8))) (c-2-14 : (uN-fam0 (8))) → (f- (lsizenn (lanetype-Jnn Jnn-I8)) v-sx c-1-26 c-2-14)) c-1-lst c-2-lst) in (just ((inv-lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) c-lst) ∷ []))
ivbinopsx- (X lanetype-I16 (mk-dim v-M)) f- v-sx v-1 v-2 = let c-1-lst = (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) v-1) in let c-2-lst = (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) v-2) in let c-lst = (zipWith (λ (c-1-28 : (uN-fam0 (16))) (c-2-16 : (uN-fam0 (16))) → (f- (lsizenn (lanetype-Jnn Jnn-I16)) v-sx c-1-28 c-2-16)) c-1-lst c-2-lst) in (just ((inv-lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) c-lst) ∷ []))
ivbinopsx- x0 f- x2 x3 x4 = nothing

{- Auxiliary Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:59.1-59.106 -}
{-# TERMINATING #-}
ivbinopsxnd- : (v-shape : shape) (f- : (v-N : N) → (v-sx : sx) → (v-iN : (uN-fam0 (v-N))) → (v-iN : (uN-fam0 (v-N))) → (List (uN-fam0 (v-N)))) (v-sx : sx) (v-vec- : (uN-fam0 (128))) (vec--0 : (uN-fam0 (128))) → (List (uN-fam0 (128)))
ivbinopsxnd- (X lanetype-I32 (mk-dim v-M)) f- v-sx v-1 v-2 = let c-1-lst = (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) v-1) in let c-2-lst = (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) v-2) in let c-lst-lst = (setproduct- (uN-fam0 (32)) (zipWith (λ (c-1-30 : (uN-fam0 (32))) (c-2-18 : (uN-fam0 (32))) → (f- (lsizenn (lanetype-Jnn Jnn-I32)) v-sx c-1-30 c-2-18)) c-1-lst c-2-lst)) in (map (λ (c-lst-6 : (List (uN-fam0 (32)))) → (inv-lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) c-lst-6)) c-lst-lst)
ivbinopsxnd- (X lanetype-I64 (mk-dim v-M)) f- v-sx v-1 v-2 = let c-1-lst = (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) v-1) in let c-2-lst = (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) v-2) in let c-lst-lst = (setproduct- (uN-fam0 (64)) (zipWith (λ (c-1-32 : (uN-fam0 (64))) (c-2-20 : (uN-fam0 (64))) → (f- (lsizenn (lanetype-Jnn Jnn-I64)) v-sx c-1-32 c-2-20)) c-1-lst c-2-lst)) in (map (λ (c-lst-8 : (List (uN-fam0 (64)))) → (inv-lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) c-lst-8)) c-lst-lst)
ivbinopsxnd- (X lanetype-I8 (mk-dim v-M)) f- v-sx v-1 v-2 = let c-1-lst = (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) v-1) in let c-2-lst = (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) v-2) in let c-lst-lst = (setproduct- (uN-fam0 (8)) (zipWith (λ (c-1-34 : (uN-fam0 (8))) (c-2-22 : (uN-fam0 (8))) → (f- (lsizenn (lanetype-Jnn Jnn-I8)) v-sx c-1-34 c-2-22)) c-1-lst c-2-lst)) in (map (λ (c-lst-10 : (List (uN-fam0 (8)))) → (inv-lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) c-lst-10)) c-lst-lst)
ivbinopsxnd- (X lanetype-I16 (mk-dim v-M)) f- v-sx v-1 v-2 = let c-1-lst = (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) v-1) in let c-2-lst = (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) v-2) in let c-lst-lst = (setproduct- (uN-fam0 (16)) (zipWith (λ (c-1-36 : (uN-fam0 (16))) (c-2-24 : (uN-fam0 (16))) → (f- (lsizenn (lanetype-Jnn Jnn-I16)) v-sx c-1-36 c-2-24)) c-1-lst c-2-lst)) in (map (λ (c-lst-12 : (List (uN-fam0 (16)))) → (inv-lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) c-lst-12)) c-lst-lst)
ivbinopsxnd- v-shape f- v-sx v-vec- vec--0 = []

{- Auxiliary Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:60.1-60.94 -}
{-# TERMINATING #-}
fvbinop- : (v-shape : shape) (f- : (v-N : N) → (v-fN : (fN-fam0 (v-N))) → (v-fN : (fN-fam0 (v-N))) → (List (fN-fam0 (v-N)))) (v-vec- : (uN-fam0 (128))) (vec--0 : (uN-fam0 (128))) → (List (uN-fam0 (128)))
fvbinop- (X lanetype-F32 (mk-dim v-M)) f- v-1 v-2 = let c-1-lst = (lanes- (X (lanetype-Fnn Fnn-F32) (mk-dim v-M)) v-1) in let c-2-lst = (lanes- (X (lanetype-Fnn Fnn-F32) (mk-dim v-M)) v-2) in let c-lst-lst = (setproduct- (fN-fam0 (32)) (zipWith (λ (c-1-38 : (fN-fam0 (32))) (c-2-26 : (fN-fam0 (32))) → (f- (sizenn (numtype-Fnn Fnn-F32)) c-1-38 c-2-26)) c-1-lst c-2-lst)) in (map (λ (c-lst-14 : (List (fN-fam0 (32)))) → (inv-lanes- (X (lanetype-Fnn Fnn-F32) (mk-dim v-M)) c-lst-14)) c-lst-lst)
fvbinop- (X lanetype-F64 (mk-dim v-M)) f- v-1 v-2 = let c-1-lst = (lanes- (X (lanetype-Fnn Fnn-F64) (mk-dim v-M)) v-1) in let c-2-lst = (lanes- (X (lanetype-Fnn Fnn-F64) (mk-dim v-M)) v-2) in let c-lst-lst = (setproduct- (fN-fam0 (64)) (zipWith (λ (c-1-40 : (fN-fam0 (64))) (c-2-28 : (fN-fam0 (64))) → (f- (sizenn (numtype-Fnn Fnn-F64)) c-1-40 c-2-28)) c-1-lst c-2-lst)) in (map (λ (c-lst-16 : (List (fN-fam0 (64)))) → (inv-lanes- (X (lanetype-Fnn Fnn-F64) (mk-dim v-M)) c-lst-16)) c-lst-lst)
fvbinop- v-shape f- v-vec- vec--0 = []

{- Auxiliary Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:62.1-62.116 -}
{-# TERMINATING #-}
ivternopnd- : (v-shape : shape) (f- : (v-N : N) → (v-iN : (uN-fam0 (v-N))) → (v-iN : (uN-fam0 (v-N))) → (v-iN : (uN-fam0 (v-N))) → (List (uN-fam0 (v-N)))) (v-vec- : (uN-fam0 (128))) (vec--0 : (uN-fam0 (128))) (vec--1 : (uN-fam0 (128))) → (List (uN-fam0 (128)))
ivternopnd- (X lanetype-I32 (mk-dim v-M)) f- v-1 v-2 v-3 = let c-1-lst = (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) v-1) in let c-2-lst = (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) v-2) in let c-3-lst = (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) v-3) in let c-lst-lst = (setproduct- (uN-fam0 (32)) (zipWith₃ (λ (c-1-42 : (uN-fam0 (32))) (c-2-30 : (uN-fam0 (32))) (c-3-2 : (uN-fam0 (32))) → (f- (lsizenn (lanetype-Jnn Jnn-I32)) c-1-42 c-2-30 c-3-2)) c-1-lst c-2-lst c-3-lst)) in (map (λ (c-lst-18 : (List (uN-fam0 (32)))) → (inv-lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) c-lst-18)) c-lst-lst)
ivternopnd- (X lanetype-I64 (mk-dim v-M)) f- v-1 v-2 v-3 = let c-1-lst = (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) v-1) in let c-2-lst = (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) v-2) in let c-3-lst = (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) v-3) in let c-lst-lst = (setproduct- (uN-fam0 (64)) (zipWith₃ (λ (c-1-44 : (uN-fam0 (64))) (c-2-32 : (uN-fam0 (64))) (c-3-4 : (uN-fam0 (64))) → (f- (lsizenn (lanetype-Jnn Jnn-I64)) c-1-44 c-2-32 c-3-4)) c-1-lst c-2-lst c-3-lst)) in (map (λ (c-lst-20 : (List (uN-fam0 (64)))) → (inv-lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) c-lst-20)) c-lst-lst)
ivternopnd- (X lanetype-I8 (mk-dim v-M)) f- v-1 v-2 v-3 = let c-1-lst = (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) v-1) in let c-2-lst = (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) v-2) in let c-3-lst = (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) v-3) in let c-lst-lst = (setproduct- (uN-fam0 (8)) (zipWith₃ (λ (c-1-46 : (uN-fam0 (8))) (c-2-34 : (uN-fam0 (8))) (c-3-6 : (uN-fam0 (8))) → (f- (lsizenn (lanetype-Jnn Jnn-I8)) c-1-46 c-2-34 c-3-6)) c-1-lst c-2-lst c-3-lst)) in (map (λ (c-lst-22 : (List (uN-fam0 (8)))) → (inv-lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) c-lst-22)) c-lst-lst)
ivternopnd- (X lanetype-I16 (mk-dim v-M)) f- v-1 v-2 v-3 = let c-1-lst = (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) v-1) in let c-2-lst = (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) v-2) in let c-3-lst = (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) v-3) in let c-lst-lst = (setproduct- (uN-fam0 (16)) (zipWith₃ (λ (c-1-48 : (uN-fam0 (16))) (c-2-36 : (uN-fam0 (16))) (c-3-8 : (uN-fam0 (16))) → (f- (lsizenn (lanetype-Jnn Jnn-I16)) c-1-48 c-2-36 c-3-8)) c-1-lst c-2-lst c-3-lst)) in (map (λ (c-lst-24 : (List (uN-fam0 (16)))) → (inv-lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) c-lst-24)) c-lst-lst)
ivternopnd- v-shape f- v-vec- vec--0 vec--1 = []

{- Auxiliary Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:63.1-63.114 -}
{-# TERMINATING #-}
fvternop- : (v-shape : shape) (f- : (v-N : N) → (v-fN : (fN-fam0 (v-N))) → (v-fN : (fN-fam0 (v-N))) → (v-fN : (fN-fam0 (v-N))) → (List (fN-fam0 (v-N)))) (v-vec- : (uN-fam0 (128))) (vec--0 : (uN-fam0 (128))) (vec--1 : (uN-fam0 (128))) → (List (uN-fam0 (128)))
fvternop- (X lanetype-F32 (mk-dim v-M)) f- v-1 v-2 v-3 = let c-1-lst = (lanes- (X (lanetype-Fnn Fnn-F32) (mk-dim v-M)) v-1) in let c-2-lst = (lanes- (X (lanetype-Fnn Fnn-F32) (mk-dim v-M)) v-2) in let c-3-lst = (lanes- (X (lanetype-Fnn Fnn-F32) (mk-dim v-M)) v-3) in let c-lst-lst = (setproduct- (fN-fam0 (32)) (zipWith₃ (λ (c-1-50 : (fN-fam0 (32))) (c-2-38 : (fN-fam0 (32))) (c-3-10 : (fN-fam0 (32))) → (f- (sizenn (numtype-Fnn Fnn-F32)) c-1-50 c-2-38 c-3-10)) c-1-lst c-2-lst c-3-lst)) in (map (λ (c-lst-26 : (List (fN-fam0 (32)))) → (inv-lanes- (X (lanetype-Fnn Fnn-F32) (mk-dim v-M)) c-lst-26)) c-lst-lst)
fvternop- (X lanetype-F64 (mk-dim v-M)) f- v-1 v-2 v-3 = let c-1-lst = (lanes- (X (lanetype-Fnn Fnn-F64) (mk-dim v-M)) v-1) in let c-2-lst = (lanes- (X (lanetype-Fnn Fnn-F64) (mk-dim v-M)) v-2) in let c-3-lst = (lanes- (X (lanetype-Fnn Fnn-F64) (mk-dim v-M)) v-3) in let c-lst-lst = (setproduct- (fN-fam0 (64)) (zipWith₃ (λ (c-1-52 : (fN-fam0 (64))) (c-2-40 : (fN-fam0 (64))) (c-3-12 : (fN-fam0 (64))) → (f- (sizenn (numtype-Fnn Fnn-F64)) c-1-52 c-2-40 c-3-12)) c-1-lst c-2-lst c-3-lst)) in (map (λ (c-lst-28 : (List (fN-fam0 (64)))) → (inv-lanes- (X (lanetype-Fnn Fnn-F64) (mk-dim v-M)) c-lst-28)) c-lst-lst)
fvternop- v-shape f- v-vec- vec--0 vec--1 = []

{- Auxiliary Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:65.1-65.90 -}
{-# TERMINATING #-}
ivrelop- : (v-shape : shape) (f- : (v-N : N) → (v-iN : (uN-fam0 (v-N))) → (v-iN : (uN-fam0 (v-N))) → u32) (v-vec- : (uN-fam0 (128))) (vec--0 : (uN-fam0 (128))) → (uN-fam0 (128))
ivrelop- (X lanetype-I32 (mk-dim v-M)) f- v-1 v-2 = let c-1-lst = (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) v-1) in let c-2-lst = (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) v-2) in let c-lst = (zipWith (λ (c-1-54 : (uN-fam0 (32))) (c-2-42 : (uN-fam0 (32))) → (extend-- 1 (lsizenn (lanetype-Jnn Jnn-I32)) S (mk-uN (proj-uN-0 32 (f- (lsizenn (lanetype-Jnn Jnn-I32)) c-1-54 c-2-42))))) c-1-lst c-2-lst) in (inv-lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) c-lst)
ivrelop- (X lanetype-I64 (mk-dim v-M)) f- v-1 v-2 = let c-1-lst = (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) v-1) in let c-2-lst = (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) v-2) in let c-lst = (zipWith (λ (c-1-56 : (uN-fam0 (64))) (c-2-44 : (uN-fam0 (64))) → (extend-- 1 (lsizenn (lanetype-Jnn Jnn-I64)) S (mk-uN (proj-uN-0 32 (f- (lsizenn (lanetype-Jnn Jnn-I64)) c-1-56 c-2-44))))) c-1-lst c-2-lst) in (inv-lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) c-lst)
ivrelop- (X lanetype-I8 (mk-dim v-M)) f- v-1 v-2 = let c-1-lst = (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) v-1) in let c-2-lst = (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) v-2) in let c-lst = (zipWith (λ (c-1-58 : (uN-fam0 (8))) (c-2-46 : (uN-fam0 (8))) → (extend-- 1 (lsizenn (lanetype-Jnn Jnn-I8)) S (mk-uN (proj-uN-0 32 (f- (lsizenn (lanetype-Jnn Jnn-I8)) c-1-58 c-2-46))))) c-1-lst c-2-lst) in (inv-lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) c-lst)
ivrelop- (X lanetype-I16 (mk-dim v-M)) f- v-1 v-2 = let c-1-lst = (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) v-1) in let c-2-lst = (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) v-2) in let c-lst = (zipWith (λ (c-1-60 : (uN-fam0 (16))) (c-2-48 : (uN-fam0 (16))) → (extend-- 1 (lsizenn (lanetype-Jnn Jnn-I16)) S (mk-uN (proj-uN-0 32 (f- (lsizenn (lanetype-Jnn Jnn-I16)) c-1-60 c-2-48))))) c-1-lst c-2-lst) in (inv-lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) c-lst)
ivrelop- v-shape f- v-vec- vec--0 = (Inhabited.default-val (inh-vec--fun V128))

{- Auxiliary Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:66.1-66.100 -}
{-# TERMINATING #-}
ivrelopsx- : (v-shape : shape) (f- : (v-N : N) → (v-sx : sx) → (v-iN : (uN-fam0 (v-N))) → (v-iN : (uN-fam0 (v-N))) → u32) (v-sx : sx) (v-vec- : (uN-fam0 (128))) (vec--0 : (uN-fam0 (128))) → (uN-fam0 (128))
ivrelopsx- (X lanetype-I32 (mk-dim v-M)) f- v-sx v-1 v-2 = let c-1-lst = (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) v-1) in let c-2-lst = (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) v-2) in let c-lst = (zipWith (λ (c-1-62 : (uN-fam0 (32))) (c-2-50 : (uN-fam0 (32))) → (extend-- 1 (lsizenn (lanetype-Jnn Jnn-I32)) S (mk-uN (proj-uN-0 32 (f- (lsizenn (lanetype-Jnn Jnn-I32)) v-sx c-1-62 c-2-50))))) c-1-lst c-2-lst) in (inv-lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) c-lst)
ivrelopsx- (X lanetype-I64 (mk-dim v-M)) f- v-sx v-1 v-2 = let c-1-lst = (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) v-1) in let c-2-lst = (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) v-2) in let c-lst = (zipWith (λ (c-1-64 : (uN-fam0 (64))) (c-2-52 : (uN-fam0 (64))) → (extend-- 1 (lsizenn (lanetype-Jnn Jnn-I64)) S (mk-uN (proj-uN-0 32 (f- (lsizenn (lanetype-Jnn Jnn-I64)) v-sx c-1-64 c-2-52))))) c-1-lst c-2-lst) in (inv-lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) c-lst)
ivrelopsx- (X lanetype-I8 (mk-dim v-M)) f- v-sx v-1 v-2 = let c-1-lst = (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) v-1) in let c-2-lst = (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) v-2) in let c-lst = (zipWith (λ (c-1-66 : (uN-fam0 (8))) (c-2-54 : (uN-fam0 (8))) → (extend-- 1 (lsizenn (lanetype-Jnn Jnn-I8)) S (mk-uN (proj-uN-0 32 (f- (lsizenn (lanetype-Jnn Jnn-I8)) v-sx c-1-66 c-2-54))))) c-1-lst c-2-lst) in (inv-lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) c-lst)
ivrelopsx- (X lanetype-I16 (mk-dim v-M)) f- v-sx v-1 v-2 = let c-1-lst = (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) v-1) in let c-2-lst = (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) v-2) in let c-lst = (zipWith (λ (c-1-68 : (uN-fam0 (16))) (c-2-56 : (uN-fam0 (16))) → (extend-- 1 (lsizenn (lanetype-Jnn Jnn-I16)) S (mk-uN (proj-uN-0 32 (f- (lsizenn (lanetype-Jnn Jnn-I16)) v-sx c-1-68 c-2-56))))) c-1-lst c-2-lst) in (inv-lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) c-lst)
ivrelopsx- v-shape f- v-sx v-vec- vec--0 = (Inhabited.default-val (inh-vec--fun V128))

{- Auxiliary Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:67.1-67.90 -}
postulate fvrelop- : ∀ (v-shape : shape) (f- : (v-N : N) → (v-fN : (fN-fam0 (v-N))) → (v-fN : (fN-fam0 (v-N))) → u32) (v-vec- : (uN-fam0 (128))) (vec--0 : (uN-fam0 (128))) → (uN-fam0 (128))

{- Auxiliary Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:69.1-69.99 -}
{-# TERMINATING #-}
ivshiftop- : (v-shape : shape) (f- : (v-N : N) → (v-iN : (uN-fam0 (v-N))) → (v-u32 : u32) → (uN-fam0 (v-N))) (v-vec- : (uN-fam0 (128))) (v-u32 : u32) → (Maybe (uN-fam0 (128)))
ivshiftop- (X lanetype-I32 (mk-dim v-M)) f- v-1 i = let c-1-lst = (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) v-1) in let c-lst = (map (λ (c-1-78 : (uN-fam0 (32))) → (f- (lsizenn (lanetype-Jnn Jnn-I32)) c-1-78 i)) c-1-lst) in (just (inv-lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) c-lst))
ivshiftop- (X lanetype-I64 (mk-dim v-M)) f- v-1 i = let c-1-lst = (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) v-1) in let c-lst = (map (λ (c-1-80 : (uN-fam0 (64))) → (f- (lsizenn (lanetype-Jnn Jnn-I64)) c-1-80 i)) c-1-lst) in (just (inv-lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) c-lst))
ivshiftop- (X lanetype-I8 (mk-dim v-M)) f- v-1 i = let c-1-lst = (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) v-1) in let c-lst = (map (λ (c-1-82 : (uN-fam0 (8))) → (f- (lsizenn (lanetype-Jnn Jnn-I8)) c-1-82 i)) c-1-lst) in (just (inv-lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) c-lst))
ivshiftop- (X lanetype-I16 (mk-dim v-M)) f- v-1 i = let c-1-lst = (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) v-1) in let c-lst = (map (λ (c-1-84 : (uN-fam0 (16))) → (f- (lsizenn (lanetype-Jnn Jnn-I16)) c-1-84 i)) c-1-lst) in (just (inv-lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) c-lst))
ivshiftop- x0 f- x2 x3 = nothing

{- Auxiliary Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:70.1-70.109 -}
{-# TERMINATING #-}
ivshiftopsx- : (v-shape : shape) (f- : (v-N : N) → (v-sx : sx) → (v-iN : (uN-fam0 (v-N))) → (v-u32 : u32) → (uN-fam0 (v-N))) (v-sx : sx) (v-vec- : (uN-fam0 (128))) (v-u32 : u32) → (Maybe (uN-fam0 (128)))
ivshiftopsx- (X lanetype-I32 (mk-dim v-M)) f- v-sx v-1 i = let c-1-lst = (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) v-1) in let c-lst = (map (λ (c-1-86 : (uN-fam0 (32))) → (f- (lsizenn (lanetype-Jnn Jnn-I32)) v-sx c-1-86 i)) c-1-lst) in (just (inv-lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) c-lst))
ivshiftopsx- (X lanetype-I64 (mk-dim v-M)) f- v-sx v-1 i = let c-1-lst = (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) v-1) in let c-lst = (map (λ (c-1-88 : (uN-fam0 (64))) → (f- (lsizenn (lanetype-Jnn Jnn-I64)) v-sx c-1-88 i)) c-1-lst) in (just (inv-lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) c-lst))
ivshiftopsx- (X lanetype-I8 (mk-dim v-M)) f- v-sx v-1 i = let c-1-lst = (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) v-1) in let c-lst = (map (λ (c-1-90 : (uN-fam0 (8))) → (f- (lsizenn (lanetype-Jnn Jnn-I8)) v-sx c-1-90 i)) c-1-lst) in (just (inv-lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) c-lst))
ivshiftopsx- (X lanetype-I16 (mk-dim v-M)) f- v-sx v-1 i = let c-1-lst = (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) v-1) in let c-lst = (map (λ (c-1-92 : (uN-fam0 (16))) → (f- (lsizenn (lanetype-Jnn Jnn-I16)) v-sx c-1-92 i)) c-1-lst) in (just (inv-lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) c-lst))
ivshiftopsx- x0 f- x2 x3 x4 = nothing

{- Auxiliary Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:72.1-72.43 -}
postulate ivbitmaskop- : ∀ (v-shape : shape) (v-vec- : (uN-fam0 (128))) → u32

{- Auxiliary Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:73.1-73.110 -}
{-# TERMINATING #-}
ivswizzlop- : (v-shape : shape) (f- : (v-N : N) → (_ : (List (uN-fam0 (v-N)))) → (v-iN : (uN-fam0 (v-N))) → (uN-fam0 (v-N))) (v-vec- : (uN-fam0 (128))) (vec--0 : (uN-fam0 (128))) → (Maybe (uN-fam0 (128)))
ivswizzlop- (X lanetype-I32 (mk-dim v-M)) f- v-1 v-2 = let c-1-lst = (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) v-1) in let c-2-lst = (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) v-2) in let c-lst = (map (λ (c-2-66 : (uN-fam0 (32))) → (f- (lsizenn (lanetype-Jnn Jnn-I32)) c-1-lst c-2-66)) c-2-lst) in (just (inv-lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) c-lst))
ivswizzlop- (X lanetype-I64 (mk-dim v-M)) f- v-1 v-2 = let c-1-lst = (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) v-1) in let c-2-lst = (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) v-2) in let c-lst = (map (λ (c-2-68 : (uN-fam0 (64))) → (f- (lsizenn (lanetype-Jnn Jnn-I64)) c-1-lst c-2-68)) c-2-lst) in (just (inv-lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) c-lst))
ivswizzlop- (X lanetype-I8 (mk-dim v-M)) f- v-1 v-2 = let c-1-lst = (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) v-1) in let c-2-lst = (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) v-2) in let c-lst = (map (λ (c-2-70 : (uN-fam0 (8))) → (f- (lsizenn (lanetype-Jnn Jnn-I8)) c-1-lst c-2-70)) c-2-lst) in (just (inv-lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) c-lst))
ivswizzlop- (X lanetype-I16 (mk-dim v-M)) f- v-1 v-2 = let c-1-lst = (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) v-1) in let c-2-lst = (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) v-2) in let c-lst = (map (λ (c-2-72 : (uN-fam0 (16))) → (f- (lsizenn (lanetype-Jnn Jnn-I16)) c-1-lst c-2-72)) c-2-lst) in (just (inv-lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) c-lst))
ivswizzlop- x0 f- x2 x3 = nothing

{- Auxiliary Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:74.1-74.85 -}
{-# TERMINATING #-}
ivshufflop- : (v-shape : shape) (var-0-lst : (List laneidx)) (v-vec- : (uN-fam0 (128))) (vec--0 : (uN-fam0 (128))) → (Maybe (uN-fam0 (128)))
ivshufflop- (X lanetype-I32 (mk-dim v-M)) i-lst v-1 v-2 = let c-1-lst = (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) v-1) in let c-2-lst = (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) v-2) in let c-lst = (map (λ (i-166274 : laneidx) → ((c-1-lst ++ c-2-lst) [ (proj-uN-0 8 i-166274) ]!)) i-lst) in (just (inv-lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) c-lst))
ivshufflop- (X lanetype-I64 (mk-dim v-M)) i-lst v-1 v-2 = let c-1-lst = (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) v-1) in let c-2-lst = (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) v-2) in let c-lst = (map (λ (i-166306 : laneidx) → ((c-1-lst ++ c-2-lst) [ (proj-uN-0 8 i-166306) ]!)) i-lst) in (just (inv-lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) c-lst))
ivshufflop- (X lanetype-I8 (mk-dim v-M)) i-lst v-1 v-2 = let c-1-lst = (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) v-1) in let c-2-lst = (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) v-2) in let c-lst = (map (λ (i-166338 : laneidx) → ((c-1-lst ++ c-2-lst) [ (proj-uN-0 8 i-166338) ]!)) i-lst) in (just (inv-lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) c-lst))
ivshufflop- (X lanetype-I16 (mk-dim v-M)) i-lst v-1 v-2 = let c-1-lst = (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) v-1) in let c-2-lst = (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) v-2) in let c-lst = (map (λ (i-166370 : laneidx) → ((c-1-lst ++ c-2-lst) [ (proj-uN-0 8 i-166370) ]!)) i-lst) in (just (inv-lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) c-lst))
ivshufflop- x0 x1 x2 x3 = nothing

{- Auxiliary Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:165.1-166.28 -}
{-# TERMINATING #-}
vvunop- : (v-vectype : vectype) (v-vvunop : vvunop) (v-vec- : (uN-fam0 ((vsize v-vectype)))) → (List (uN-fam0 ((vsize v-vectype))))
vvunop- v-Vnn NOT v = ((inot- (vsizenn v-Vnn) v) ∷ [])
vvunop- v-vectype v-vvunop v-vec- = []

{- Auxiliary Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:167.1-168.31 -}
{-# TERMINATING #-}
vvbinop- : (v-vectype : vectype) (v-vvbinop : vvbinop) (v-vec- : (uN-fam0 ((vsize v-vectype)))) (vec--0 : (uN-fam0 ((vsize v-vectype)))) → (List (uN-fam0 ((vsize v-vectype))))
vvbinop- v-Vnn vvbinop-AND v-1 v-2 = ((iand- (vsizenn v-Vnn) v-1 v-2) ∷ [])
vvbinop- v-Vnn ANDNOT v-1 v-2 = ((iandnot- (vsizenn v-Vnn) v-1 v-2) ∷ [])
vvbinop- v-Vnn vvbinop-OR v-1 v-2 = ((ior- (vsizenn v-Vnn) v-1 v-2) ∷ [])
vvbinop- v-Vnn vvbinop-XOR v-1 v-2 = ((ixor- (vsizenn v-Vnn) v-1 v-2) ∷ [])
vvbinop- v-vectype v-vvbinop v-vec- vec--0 = []

{- Auxiliary Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:169.1-170.34 -}
{-# TERMINATING #-}
vvternop- : (v-vectype : vectype) (v-vvternop : vvternop) (v-vec- : (uN-fam0 ((vsize v-vectype)))) (vec--0 : (uN-fam0 ((vsize v-vectype)))) (vec--1 : (uN-fam0 ((vsize v-vectype)))) → (List (uN-fam0 ((vsize v-vectype))))
vvternop- v-Vnn BITSELECT v-1 v-2 v-3 = ((ibitselect- (vsizenn v-Vnn) v-1 v-2 v-3) ∷ [])
vvternop- v-vectype v-vvternop v-vec- vec--0 vec--1 = []

{- Auxiliary Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:172.1-173.28 -}
{-# TERMINATING #-}
fun-vunop- : (v-shape : shape) (v-vunop- : (vunop- v-shape)) (v-vec- : (uN-fam0 (128))) → (List (uN-fam0 (128)))
fun-vunop- (X lanetype-F32 (mk-dim v-M)) vunop--ABS v = (fvunop- (X (lanetype-Fnn Fnn-F32) (mk-dim v-M)) fabs- v)
fun-vunop- (X lanetype-F64 (mk-dim v-M)) vunop--ABS v = (fvunop- (X (lanetype-Fnn Fnn-F64) (mk-dim v-M)) fabs- v)
fun-vunop- (X lanetype-F32 (mk-dim v-M)) vunop--NEG v = (fvunop- (X (lanetype-Fnn Fnn-F32) (mk-dim v-M)) fneg- v)
fun-vunop- (X lanetype-F64 (mk-dim v-M)) vunop--NEG v = (fvunop- (X (lanetype-Fnn Fnn-F64) (mk-dim v-M)) fneg- v)
fun-vunop- (X lanetype-F32 (mk-dim v-M)) vunop--SQRT v = (fvunop- (X (lanetype-Fnn Fnn-F32) (mk-dim v-M)) fsqrt- v)
fun-vunop- (X lanetype-F64 (mk-dim v-M)) vunop--SQRT v = (fvunop- (X (lanetype-Fnn Fnn-F64) (mk-dim v-M)) fsqrt- v)
fun-vunop- (X lanetype-F32 (mk-dim v-M)) vunop--CEIL v = (fvunop- (X (lanetype-Fnn Fnn-F32) (mk-dim v-M)) fceil- v)
fun-vunop- (X lanetype-F64 (mk-dim v-M)) vunop--CEIL v = (fvunop- (X (lanetype-Fnn Fnn-F64) (mk-dim v-M)) fceil- v)
fun-vunop- (X lanetype-F32 (mk-dim v-M)) vunop--FLOOR v = (fvunop- (X (lanetype-Fnn Fnn-F32) (mk-dim v-M)) ffloor- v)
fun-vunop- (X lanetype-F64 (mk-dim v-M)) vunop--FLOOR v = (fvunop- (X (lanetype-Fnn Fnn-F64) (mk-dim v-M)) ffloor- v)
fun-vunop- (X lanetype-F32 (mk-dim v-M)) vunop--TRUNC v = (fvunop- (X (lanetype-Fnn Fnn-F32) (mk-dim v-M)) ftrunc- v)
fun-vunop- (X lanetype-F64 (mk-dim v-M)) vunop--TRUNC v = (fvunop- (X (lanetype-Fnn Fnn-F64) (mk-dim v-M)) ftrunc- v)
fun-vunop- (X lanetype-F32 (mk-dim v-M)) vunop--NEAREST v = (fvunop- (X (lanetype-Fnn Fnn-F32) (mk-dim v-M)) fnearest- v)
fun-vunop- (X lanetype-F64 (mk-dim v-M)) vunop--NEAREST v = (fvunop- (X (lanetype-Fnn Fnn-F64) (mk-dim v-M)) fnearest- v)
fun-vunop- (X lanetype-I32 (mk-dim v-M)) vunop--ABS v = (unwrap! (ivunop- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) iabs- v))
fun-vunop- (X lanetype-I64 (mk-dim v-M)) vunop--ABS v = (unwrap! (ivunop- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) iabs- v))
fun-vunop- (X lanetype-I8 (mk-dim v-M)) vunop--ABS v = (unwrap! (ivunop- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) iabs- v))
fun-vunop- (X lanetype-I16 (mk-dim v-M)) vunop--ABS v = (unwrap! (ivunop- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) iabs- v))
fun-vunop- (X lanetype-I32 (mk-dim v-M)) vunop--NEG v = (unwrap! (ivunop- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) ineg- v))
fun-vunop- (X lanetype-I64 (mk-dim v-M)) vunop--NEG v = (unwrap! (ivunop- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) ineg- v))
fun-vunop- (X lanetype-I8 (mk-dim v-M)) vunop--NEG v = (unwrap! (ivunop- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) ineg- v))
fun-vunop- (X lanetype-I16 (mk-dim v-M)) vunop--NEG v = (unwrap! (ivunop- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) ineg- v))
fun-vunop- (X lanetype-I32 (mk-dim v-M)) vunop--POPCNT v = (unwrap! (ivunop- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) ipopcnt- v))
fun-vunop- (X lanetype-I64 (mk-dim v-M)) vunop--POPCNT v = (unwrap! (ivunop- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) ipopcnt- v))
fun-vunop- (X lanetype-I8 (mk-dim v-M)) vunop--POPCNT v = (unwrap! (ivunop- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) ipopcnt- v))
fun-vunop- (X lanetype-I16 (mk-dim v-M)) vunop--POPCNT v = (unwrap! (ivunop- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) ipopcnt- v))
fun-vunop- v-shape v-vunop- v-vec- = []

{- Auxiliary Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:174.1-175.31 -}
{-# TERMINATING #-}
fun-vbinop- : (v-shape : shape) (v-vbinop- : (vbinop- v-shape)) (v-vec- : (uN-fam0 (128))) (vec--0 : (uN-fam0 (128))) → (List (uN-fam0 (128)))
fun-vbinop- (X lanetype-I32 (mk-dim v-M)) vbinop--ADD v-1 v-2 = (unwrap! (ivbinop- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) iadd- v-1 v-2))
fun-vbinop- (X lanetype-I64 (mk-dim v-M)) vbinop--ADD v-1 v-2 = (unwrap! (ivbinop- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) iadd- v-1 v-2))
fun-vbinop- (X lanetype-I8 (mk-dim v-M)) vbinop--ADD v-1 v-2 = (unwrap! (ivbinop- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) iadd- v-1 v-2))
fun-vbinop- (X lanetype-I16 (mk-dim v-M)) vbinop--ADD v-1 v-2 = (unwrap! (ivbinop- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) iadd- v-1 v-2))
fun-vbinop- (X lanetype-I32 (mk-dim v-M)) vbinop--SUB v-1 v-2 = (unwrap! (ivbinop- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) isub- v-1 v-2))
fun-vbinop- (X lanetype-I64 (mk-dim v-M)) vbinop--SUB v-1 v-2 = (unwrap! (ivbinop- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) isub- v-1 v-2))
fun-vbinop- (X lanetype-I8 (mk-dim v-M)) vbinop--SUB v-1 v-2 = (unwrap! (ivbinop- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) isub- v-1 v-2))
fun-vbinop- (X lanetype-I16 (mk-dim v-M)) vbinop--SUB v-1 v-2 = (unwrap! (ivbinop- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) isub- v-1 v-2))
fun-vbinop- (X lanetype-I32 (mk-dim v-M)) vbinop--MUL v-1 v-2 = (unwrap! (ivbinop- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) imul- v-1 v-2))
fun-vbinop- (X lanetype-I64 (mk-dim v-M)) vbinop--MUL v-1 v-2 = (unwrap! (ivbinop- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) imul- v-1 v-2))
fun-vbinop- (X lanetype-I8 (mk-dim v-M)) vbinop--MUL v-1 v-2 = (unwrap! (ivbinop- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) imul- v-1 v-2))
fun-vbinop- (X lanetype-I16 (mk-dim v-M)) vbinop--MUL v-1 v-2 = (unwrap! (ivbinop- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) imul- v-1 v-2))
fun-vbinop- (X lanetype-I32 (mk-dim v-M)) (ADD-SAT v-sx) v-1 v-2 = (unwrap! (ivbinopsx- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) iadd-sat- v-sx v-1 v-2))
fun-vbinop- (X lanetype-I64 (mk-dim v-M)) (ADD-SAT v-sx) v-1 v-2 = (unwrap! (ivbinopsx- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) iadd-sat- v-sx v-1 v-2))
fun-vbinop- (X lanetype-I8 (mk-dim v-M)) (ADD-SAT v-sx) v-1 v-2 = (unwrap! (ivbinopsx- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) iadd-sat- v-sx v-1 v-2))
fun-vbinop- (X lanetype-I16 (mk-dim v-M)) (ADD-SAT v-sx) v-1 v-2 = (unwrap! (ivbinopsx- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) iadd-sat- v-sx v-1 v-2))
fun-vbinop- (X lanetype-I32 (mk-dim v-M)) (SUB-SAT v-sx) v-1 v-2 = (unwrap! (ivbinopsx- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) isub-sat- v-sx v-1 v-2))
fun-vbinop- (X lanetype-I64 (mk-dim v-M)) (SUB-SAT v-sx) v-1 v-2 = (unwrap! (ivbinopsx- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) isub-sat- v-sx v-1 v-2))
fun-vbinop- (X lanetype-I8 (mk-dim v-M)) (SUB-SAT v-sx) v-1 v-2 = (unwrap! (ivbinopsx- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) isub-sat- v-sx v-1 v-2))
fun-vbinop- (X lanetype-I16 (mk-dim v-M)) (SUB-SAT v-sx) v-1 v-2 = (unwrap! (ivbinopsx- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) isub-sat- v-sx v-1 v-2))
fun-vbinop- (X lanetype-I32 (mk-dim v-M)) (vbinop--MIN v-sx) v-1 v-2 = (unwrap! (ivbinopsx- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) imin- v-sx v-1 v-2))
fun-vbinop- (X lanetype-I64 (mk-dim v-M)) (vbinop--MIN v-sx) v-1 v-2 = (unwrap! (ivbinopsx- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) imin- v-sx v-1 v-2))
fun-vbinop- (X lanetype-I8 (mk-dim v-M)) (vbinop--MIN v-sx) v-1 v-2 = (unwrap! (ivbinopsx- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) imin- v-sx v-1 v-2))
fun-vbinop- (X lanetype-I16 (mk-dim v-M)) (vbinop--MIN v-sx) v-1 v-2 = (unwrap! (ivbinopsx- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) imin- v-sx v-1 v-2))
fun-vbinop- (X lanetype-I32 (mk-dim v-M)) (vbinop--MAX v-sx) v-1 v-2 = (unwrap! (ivbinopsx- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) imax- v-sx v-1 v-2))
fun-vbinop- (X lanetype-I64 (mk-dim v-M)) (vbinop--MAX v-sx) v-1 v-2 = (unwrap! (ivbinopsx- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) imax- v-sx v-1 v-2))
fun-vbinop- (X lanetype-I8 (mk-dim v-M)) (vbinop--MAX v-sx) v-1 v-2 = (unwrap! (ivbinopsx- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) imax- v-sx v-1 v-2))
fun-vbinop- (X lanetype-I16 (mk-dim v-M)) (vbinop--MAX v-sx) v-1 v-2 = (unwrap! (ivbinopsx- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) imax- v-sx v-1 v-2))
fun-vbinop- (X lanetype-I32 (mk-dim v-M)) AVGRU v-1 v-2 = (unwrap! (ivbinopsx- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) iavgr- U v-1 v-2))
fun-vbinop- (X lanetype-I64 (mk-dim v-M)) AVGRU v-1 v-2 = (unwrap! (ivbinopsx- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) iavgr- U v-1 v-2))
fun-vbinop- (X lanetype-I8 (mk-dim v-M)) AVGRU v-1 v-2 = (unwrap! (ivbinopsx- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) iavgr- U v-1 v-2))
fun-vbinop- (X lanetype-I16 (mk-dim v-M)) AVGRU v-1 v-2 = (unwrap! (ivbinopsx- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) iavgr- U v-1 v-2))
fun-vbinop- (X lanetype-I32 (mk-dim v-M)) Q15MULR-SATS v-1 v-2 = (unwrap! (ivbinopsx- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) iq15mulr-sat- S v-1 v-2))
fun-vbinop- (X lanetype-I64 (mk-dim v-M)) Q15MULR-SATS v-1 v-2 = (unwrap! (ivbinopsx- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) iq15mulr-sat- S v-1 v-2))
fun-vbinop- (X lanetype-I8 (mk-dim v-M)) Q15MULR-SATS v-1 v-2 = (unwrap! (ivbinopsx- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) iq15mulr-sat- S v-1 v-2))
fun-vbinop- (X lanetype-I16 (mk-dim v-M)) Q15MULR-SATS v-1 v-2 = (unwrap! (ivbinopsx- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) iq15mulr-sat- S v-1 v-2))
fun-vbinop- (X lanetype-I32 (mk-dim v-M)) RELAXED-Q15MULRS v-1 v-2 = (ivbinopsxnd- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) irelaxed-q15mulr- S v-1 v-2)
fun-vbinop- (X lanetype-I64 (mk-dim v-M)) RELAXED-Q15MULRS v-1 v-2 = (ivbinopsxnd- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) irelaxed-q15mulr- S v-1 v-2)
fun-vbinop- (X lanetype-I8 (mk-dim v-M)) RELAXED-Q15MULRS v-1 v-2 = (ivbinopsxnd- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) irelaxed-q15mulr- S v-1 v-2)
fun-vbinop- (X lanetype-I16 (mk-dim v-M)) RELAXED-Q15MULRS v-1 v-2 = (ivbinopsxnd- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) irelaxed-q15mulr- S v-1 v-2)
fun-vbinop- (X lanetype-F32 (mk-dim v-M)) vbinop--ADD v-1 v-2 = (fvbinop- (X (lanetype-Fnn Fnn-F32) (mk-dim v-M)) fadd- v-1 v-2)
fun-vbinop- (X lanetype-F64 (mk-dim v-M)) vbinop--ADD v-1 v-2 = (fvbinop- (X (lanetype-Fnn Fnn-F64) (mk-dim v-M)) fadd- v-1 v-2)
fun-vbinop- (X lanetype-F32 (mk-dim v-M)) vbinop--SUB v-1 v-2 = (fvbinop- (X (lanetype-Fnn Fnn-F32) (mk-dim v-M)) fsub- v-1 v-2)
fun-vbinop- (X lanetype-F64 (mk-dim v-M)) vbinop--SUB v-1 v-2 = (fvbinop- (X (lanetype-Fnn Fnn-F64) (mk-dim v-M)) fsub- v-1 v-2)
fun-vbinop- (X lanetype-F32 (mk-dim v-M)) vbinop--MUL v-1 v-2 = (fvbinop- (X (lanetype-Fnn Fnn-F32) (mk-dim v-M)) fmul- v-1 v-2)
fun-vbinop- (X lanetype-F64 (mk-dim v-M)) vbinop--MUL v-1 v-2 = (fvbinop- (X (lanetype-Fnn Fnn-F64) (mk-dim v-M)) fmul- v-1 v-2)
fun-vbinop- (X lanetype-F32 (mk-dim v-M)) vbinop--DIV v-1 v-2 = (fvbinop- (X (lanetype-Fnn Fnn-F32) (mk-dim v-M)) fdiv- v-1 v-2)
fun-vbinop- (X lanetype-F64 (mk-dim v-M)) vbinop--DIV v-1 v-2 = (fvbinop- (X (lanetype-Fnn Fnn-F64) (mk-dim v-M)) fdiv- v-1 v-2)
fun-vbinop- (X lanetype-F32 (mk-dim v-M)) vbinop--MIN v-1 v-2 = (fvbinop- (X (lanetype-Fnn Fnn-F32) (mk-dim v-M)) fmin- v-1 v-2)
fun-vbinop- (X lanetype-F64 (mk-dim v-M)) vbinop--MIN v-1 v-2 = (fvbinop- (X (lanetype-Fnn Fnn-F64) (mk-dim v-M)) fmin- v-1 v-2)
fun-vbinop- (X lanetype-F32 (mk-dim v-M)) vbinop--MAX v-1 v-2 = (fvbinop- (X (lanetype-Fnn Fnn-F32) (mk-dim v-M)) fmax- v-1 v-2)
fun-vbinop- (X lanetype-F64 (mk-dim v-M)) vbinop--MAX v-1 v-2 = (fvbinop- (X (lanetype-Fnn Fnn-F64) (mk-dim v-M)) fmax- v-1 v-2)
fun-vbinop- (X lanetype-F32 (mk-dim v-M)) PMIN v-1 v-2 = (fvbinop- (X (lanetype-Fnn Fnn-F32) (mk-dim v-M)) fpmin- v-1 v-2)
fun-vbinop- (X lanetype-F64 (mk-dim v-M)) PMIN v-1 v-2 = (fvbinop- (X (lanetype-Fnn Fnn-F64) (mk-dim v-M)) fpmin- v-1 v-2)
fun-vbinop- (X lanetype-F32 (mk-dim v-M)) PMAX v-1 v-2 = (fvbinop- (X (lanetype-Fnn Fnn-F32) (mk-dim v-M)) fpmax- v-1 v-2)
fun-vbinop- (X lanetype-F64 (mk-dim v-M)) PMAX v-1 v-2 = (fvbinop- (X (lanetype-Fnn Fnn-F64) (mk-dim v-M)) fpmax- v-1 v-2)
fun-vbinop- (X lanetype-F32 (mk-dim v-M)) RELAXED-MIN v-1 v-2 = (fvbinop- (X (lanetype-Fnn Fnn-F32) (mk-dim v-M)) frelaxed-min- v-1 v-2)
fun-vbinop- (X lanetype-F64 (mk-dim v-M)) RELAXED-MIN v-1 v-2 = (fvbinop- (X (lanetype-Fnn Fnn-F64) (mk-dim v-M)) frelaxed-min- v-1 v-2)
fun-vbinop- (X lanetype-F32 (mk-dim v-M)) RELAXED-MAX v-1 v-2 = (fvbinop- (X (lanetype-Fnn Fnn-F32) (mk-dim v-M)) frelaxed-max- v-1 v-2)
fun-vbinop- (X lanetype-F64 (mk-dim v-M)) RELAXED-MAX v-1 v-2 = (fvbinop- (X (lanetype-Fnn Fnn-F64) (mk-dim v-M)) frelaxed-max- v-1 v-2)
fun-vbinop- v-shape v-vbinop- v-vec- vec--0 = []

{- Auxiliary Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:176.1-177.34 -}
{-# TERMINATING #-}
fun-vternop- : (v-shape : shape) (v-vternop- : (vternop- v-shape)) (v-vec- : (uN-fam0 (128))) (vec--0 : (uN-fam0 (128))) (vec--1 : (uN-fam0 (128))) → (List (uN-fam0 (128)))
fun-vternop- (X lanetype-I32 (mk-dim v-M)) RELAXED-LANESELECT v-1 v-2 v-3 = (ivternopnd- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) irelaxed-laneselect- v-1 v-2 v-3)
fun-vternop- (X lanetype-I64 (mk-dim v-M)) RELAXED-LANESELECT v-1 v-2 v-3 = (ivternopnd- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) irelaxed-laneselect- v-1 v-2 v-3)
fun-vternop- (X lanetype-I8 (mk-dim v-M)) RELAXED-LANESELECT v-1 v-2 v-3 = (ivternopnd- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) irelaxed-laneselect- v-1 v-2 v-3)
fun-vternop- (X lanetype-I16 (mk-dim v-M)) RELAXED-LANESELECT v-1 v-2 v-3 = (ivternopnd- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) irelaxed-laneselect- v-1 v-2 v-3)
fun-vternop- (X lanetype-F32 (mk-dim v-M)) RELAXED-MADD v-1 v-2 v-3 = (fvternop- (X (lanetype-Fnn Fnn-F32) (mk-dim v-M)) frelaxed-madd- v-1 v-2 v-3)
fun-vternop- (X lanetype-F64 (mk-dim v-M)) RELAXED-MADD v-1 v-2 v-3 = (fvternop- (X (lanetype-Fnn Fnn-F64) (mk-dim v-M)) frelaxed-madd- v-1 v-2 v-3)
fun-vternop- (X lanetype-F32 (mk-dim v-M)) RELAXED-NMADD v-1 v-2 v-3 = (fvternop- (X (lanetype-Fnn Fnn-F32) (mk-dim v-M)) frelaxed-nmadd- v-1 v-2 v-3)
fun-vternop- (X lanetype-F64 (mk-dim v-M)) RELAXED-NMADD v-1 v-2 v-3 = (fvternop- (X (lanetype-Fnn Fnn-F64) (mk-dim v-M)) frelaxed-nmadd- v-1 v-2 v-3)
fun-vternop- v-shape v-vternop- v-vec- vec--0 vec--1 = []

{- Auxiliary Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:178.1-179.31 -}
{-# TERMINATING #-}
fun-vrelop- : (v-shape : shape) (v-vrelop- : (vrelop- v-shape)) (v-vec- : (uN-fam0 (128))) (vec--0 : (uN-fam0 (128))) → (uN-fam0 (128))
fun-vrelop- (X lanetype-I32 (mk-dim v-M)) vrelop--EQ v-1 v-2 = (ivrelop- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) ieq- v-1 v-2)
fun-vrelop- (X lanetype-I64 (mk-dim v-M)) vrelop--EQ v-1 v-2 = (ivrelop- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) ieq- v-1 v-2)
fun-vrelop- (X lanetype-I8 (mk-dim v-M)) vrelop--EQ v-1 v-2 = (ivrelop- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) ieq- v-1 v-2)
fun-vrelop- (X lanetype-I16 (mk-dim v-M)) vrelop--EQ v-1 v-2 = (ivrelop- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) ieq- v-1 v-2)
fun-vrelop- (X lanetype-I32 (mk-dim v-M)) vrelop--NE v-1 v-2 = (ivrelop- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) ine- v-1 v-2)
fun-vrelop- (X lanetype-I64 (mk-dim v-M)) vrelop--NE v-1 v-2 = (ivrelop- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) ine- v-1 v-2)
fun-vrelop- (X lanetype-I8 (mk-dim v-M)) vrelop--NE v-1 v-2 = (ivrelop- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) ine- v-1 v-2)
fun-vrelop- (X lanetype-I16 (mk-dim v-M)) vrelop--NE v-1 v-2 = (ivrelop- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) ine- v-1 v-2)
fun-vrelop- (X lanetype-I32 (mk-dim v-M)) (vrelop--LT v-sx) v-1 v-2 = (ivrelopsx- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) ilt- v-sx v-1 v-2)
fun-vrelop- (X lanetype-I64 (mk-dim v-M)) (vrelop--LT v-sx) v-1 v-2 = (ivrelopsx- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) ilt- v-sx v-1 v-2)
fun-vrelop- (X lanetype-I8 (mk-dim v-M)) (vrelop--LT v-sx) v-1 v-2 = (ivrelopsx- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) ilt- v-sx v-1 v-2)
fun-vrelop- (X lanetype-I16 (mk-dim v-M)) (vrelop--LT v-sx) v-1 v-2 = (ivrelopsx- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) ilt- v-sx v-1 v-2)
fun-vrelop- (X lanetype-I32 (mk-dim v-M)) (vrelop--GT v-sx) v-1 v-2 = (ivrelopsx- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) igt- v-sx v-1 v-2)
fun-vrelop- (X lanetype-I64 (mk-dim v-M)) (vrelop--GT v-sx) v-1 v-2 = (ivrelopsx- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) igt- v-sx v-1 v-2)
fun-vrelop- (X lanetype-I8 (mk-dim v-M)) (vrelop--GT v-sx) v-1 v-2 = (ivrelopsx- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) igt- v-sx v-1 v-2)
fun-vrelop- (X lanetype-I16 (mk-dim v-M)) (vrelop--GT v-sx) v-1 v-2 = (ivrelopsx- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) igt- v-sx v-1 v-2)
fun-vrelop- (X lanetype-I32 (mk-dim v-M)) (vrelop--LE v-sx) v-1 v-2 = (ivrelopsx- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) ile- v-sx v-1 v-2)
fun-vrelop- (X lanetype-I64 (mk-dim v-M)) (vrelop--LE v-sx) v-1 v-2 = (ivrelopsx- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) ile- v-sx v-1 v-2)
fun-vrelop- (X lanetype-I8 (mk-dim v-M)) (vrelop--LE v-sx) v-1 v-2 = (ivrelopsx- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) ile- v-sx v-1 v-2)
fun-vrelop- (X lanetype-I16 (mk-dim v-M)) (vrelop--LE v-sx) v-1 v-2 = (ivrelopsx- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) ile- v-sx v-1 v-2)
fun-vrelop- (X lanetype-I32 (mk-dim v-M)) (vrelop--GE v-sx) v-1 v-2 = (ivrelopsx- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) ige- v-sx v-1 v-2)
fun-vrelop- (X lanetype-I64 (mk-dim v-M)) (vrelop--GE v-sx) v-1 v-2 = (ivrelopsx- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) ige- v-sx v-1 v-2)
fun-vrelop- (X lanetype-I8 (mk-dim v-M)) (vrelop--GE v-sx) v-1 v-2 = (ivrelopsx- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) ige- v-sx v-1 v-2)
fun-vrelop- (X lanetype-I16 (mk-dim v-M)) (vrelop--GE v-sx) v-1 v-2 = (ivrelopsx- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) ige- v-sx v-1 v-2)
fun-vrelop- (X lanetype-F32 (mk-dim v-M)) vrelop--EQ v-1 v-2 = (fvrelop- (X (lanetype-Fnn Fnn-F32) (mk-dim v-M)) feq- v-1 v-2)
fun-vrelop- (X lanetype-F64 (mk-dim v-M)) vrelop--EQ v-1 v-2 = (fvrelop- (X (lanetype-Fnn Fnn-F64) (mk-dim v-M)) feq- v-1 v-2)
fun-vrelop- (X lanetype-F32 (mk-dim v-M)) vrelop--NE v-1 v-2 = (fvrelop- (X (lanetype-Fnn Fnn-F32) (mk-dim v-M)) fne- v-1 v-2)
fun-vrelop- (X lanetype-F64 (mk-dim v-M)) vrelop--NE v-1 v-2 = (fvrelop- (X (lanetype-Fnn Fnn-F64) (mk-dim v-M)) fne- v-1 v-2)
fun-vrelop- (X lanetype-F32 (mk-dim v-M)) vrelop--LT v-1 v-2 = (fvrelop- (X (lanetype-Fnn Fnn-F32) (mk-dim v-M)) flt- v-1 v-2)
fun-vrelop- (X lanetype-F64 (mk-dim v-M)) vrelop--LT v-1 v-2 = (fvrelop- (X (lanetype-Fnn Fnn-F64) (mk-dim v-M)) flt- v-1 v-2)
fun-vrelop- (X lanetype-F32 (mk-dim v-M)) vrelop--GT v-1 v-2 = (fvrelop- (X (lanetype-Fnn Fnn-F32) (mk-dim v-M)) fgt- v-1 v-2)
fun-vrelop- (X lanetype-F64 (mk-dim v-M)) vrelop--GT v-1 v-2 = (fvrelop- (X (lanetype-Fnn Fnn-F64) (mk-dim v-M)) fgt- v-1 v-2)
fun-vrelop- (X lanetype-F32 (mk-dim v-M)) vrelop--LE v-1 v-2 = (fvrelop- (X (lanetype-Fnn Fnn-F32) (mk-dim v-M)) fle- v-1 v-2)
fun-vrelop- (X lanetype-F64 (mk-dim v-M)) vrelop--LE v-1 v-2 = (fvrelop- (X (lanetype-Fnn Fnn-F64) (mk-dim v-M)) fle- v-1 v-2)
fun-vrelop- (X lanetype-F32 (mk-dim v-M)) vrelop--GE v-1 v-2 = (fvrelop- (X (lanetype-Fnn Fnn-F32) (mk-dim v-M)) fge- v-1 v-2)
fun-vrelop- (X lanetype-F64 (mk-dim v-M)) vrelop--GE v-1 v-2 = (fvrelop- (X (lanetype-Fnn Fnn-F64) (mk-dim v-M)) fge- v-1 v-2)
fun-vrelop- v-shape v-vrelop- v-vec- vec--0 = (Inhabited.default-val (inh-vec--fun V128))

{- Auxiliary Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:181.1-182.41 -}
{-# TERMINATING #-}
lcvtop-- : (shape-1 : shape) (shape-2 : shape) (v-vcvtop-- : (vcvtop-- shape-1 shape-2)) (v-lane- : (lane- (fun-lanetype shape-1))) → (List (lane- (fun-lanetype shape-2)))
lcvtop-- (X lanetype-I32 (mk-dim M-1)) (X lanetype-I32 (mk-dim M-2)) (vcvtop---EXTEND v-half v-sx) c-1 = let c = (extend-- (lsizenn1 (lanetype-Jnn Jnn-I32)) (lsizenn2 (lanetype-Jnn Jnn-I32)) v-sx c-1) in (c ∷ [])
lcvtop-- (X lanetype-I64 (mk-dim M-1)) (X lanetype-I32 (mk-dim M-2)) (vcvtop---EXTEND v-half v-sx) c-1 = let c = (extend-- (lsizenn1 (lanetype-Jnn Jnn-I64)) (lsizenn2 (lanetype-Jnn Jnn-I32)) v-sx c-1) in (c ∷ [])
lcvtop-- (X lanetype-I8 (mk-dim M-1)) (X lanetype-I32 (mk-dim M-2)) (vcvtop---EXTEND v-half v-sx) c-1 = let c = (extend-- (lsizenn1 (lanetype-Jnn Jnn-I8)) (lsizenn2 (lanetype-Jnn Jnn-I32)) v-sx c-1) in (c ∷ [])
lcvtop-- (X lanetype-I16 (mk-dim M-1)) (X lanetype-I32 (mk-dim M-2)) (vcvtop---EXTEND v-half v-sx) c-1 = let c = (extend-- (lsizenn1 (lanetype-Jnn Jnn-I16)) (lsizenn2 (lanetype-Jnn Jnn-I32)) v-sx c-1) in (c ∷ [])
lcvtop-- (X lanetype-I32 (mk-dim M-1)) (X lanetype-I64 (mk-dim M-2)) (vcvtop---EXTEND v-half v-sx) c-1 = let c = (extend-- (lsizenn1 (lanetype-Jnn Jnn-I32)) (lsizenn2 (lanetype-Jnn Jnn-I64)) v-sx c-1) in (c ∷ [])
lcvtop-- (X lanetype-I64 (mk-dim M-1)) (X lanetype-I64 (mk-dim M-2)) (vcvtop---EXTEND v-half v-sx) c-1 = let c = (extend-- (lsizenn1 (lanetype-Jnn Jnn-I64)) (lsizenn2 (lanetype-Jnn Jnn-I64)) v-sx c-1) in (c ∷ [])
lcvtop-- (X lanetype-I8 (mk-dim M-1)) (X lanetype-I64 (mk-dim M-2)) (vcvtop---EXTEND v-half v-sx) c-1 = let c = (extend-- (lsizenn1 (lanetype-Jnn Jnn-I8)) (lsizenn2 (lanetype-Jnn Jnn-I64)) v-sx c-1) in (c ∷ [])
lcvtop-- (X lanetype-I16 (mk-dim M-1)) (X lanetype-I64 (mk-dim M-2)) (vcvtop---EXTEND v-half v-sx) c-1 = let c = (extend-- (lsizenn1 (lanetype-Jnn Jnn-I16)) (lsizenn2 (lanetype-Jnn Jnn-I64)) v-sx c-1) in (c ∷ [])
lcvtop-- (X lanetype-I32 (mk-dim M-1)) (X lanetype-I8 (mk-dim M-2)) (vcvtop---EXTEND v-half v-sx) c-1 = let c = (extend-- (lsizenn1 (lanetype-Jnn Jnn-I32)) (lsizenn2 (lanetype-Jnn Jnn-I8)) v-sx c-1) in (c ∷ [])
lcvtop-- (X lanetype-I64 (mk-dim M-1)) (X lanetype-I8 (mk-dim M-2)) (vcvtop---EXTEND v-half v-sx) c-1 = let c = (extend-- (lsizenn1 (lanetype-Jnn Jnn-I64)) (lsizenn2 (lanetype-Jnn Jnn-I8)) v-sx c-1) in (c ∷ [])
lcvtop-- (X lanetype-I8 (mk-dim M-1)) (X lanetype-I8 (mk-dim M-2)) (vcvtop---EXTEND v-half v-sx) c-1 = let c = (extend-- (lsizenn1 (lanetype-Jnn Jnn-I8)) (lsizenn2 (lanetype-Jnn Jnn-I8)) v-sx c-1) in (c ∷ [])
lcvtop-- (X lanetype-I16 (mk-dim M-1)) (X lanetype-I8 (mk-dim M-2)) (vcvtop---EXTEND v-half v-sx) c-1 = let c = (extend-- (lsizenn1 (lanetype-Jnn Jnn-I16)) (lsizenn2 (lanetype-Jnn Jnn-I8)) v-sx c-1) in (c ∷ [])
lcvtop-- (X lanetype-I32 (mk-dim M-1)) (X lanetype-I16 (mk-dim M-2)) (vcvtop---EXTEND v-half v-sx) c-1 = let c = (extend-- (lsizenn1 (lanetype-Jnn Jnn-I32)) (lsizenn2 (lanetype-Jnn Jnn-I16)) v-sx c-1) in (c ∷ [])
lcvtop-- (X lanetype-I64 (mk-dim M-1)) (X lanetype-I16 (mk-dim M-2)) (vcvtop---EXTEND v-half v-sx) c-1 = let c = (extend-- (lsizenn1 (lanetype-Jnn Jnn-I64)) (lsizenn2 (lanetype-Jnn Jnn-I16)) v-sx c-1) in (c ∷ [])
lcvtop-- (X lanetype-I8 (mk-dim M-1)) (X lanetype-I16 (mk-dim M-2)) (vcvtop---EXTEND v-half v-sx) c-1 = let c = (extend-- (lsizenn1 (lanetype-Jnn Jnn-I8)) (lsizenn2 (lanetype-Jnn Jnn-I16)) v-sx c-1) in (c ∷ [])
lcvtop-- (X lanetype-I16 (mk-dim M-1)) (X lanetype-I16 (mk-dim M-2)) (vcvtop---EXTEND v-half v-sx) c-1 = let c = (extend-- (lsizenn1 (lanetype-Jnn Jnn-I16)) (lsizenn2 (lanetype-Jnn Jnn-I16)) v-sx c-1) in (c ∷ [])
lcvtop-- (X lanetype-I32 (mk-dim M-1)) (X lanetype-F32 (mk-dim M-2)) (vcvtop---CONVERT half-opt v-sx) c-1 = let c = (convert-- (lsizenn1 (lanetype-Jnn Jnn-I32)) (lsizenn2 (lanetype-Fnn Fnn-F32)) v-sx c-1) in (c ∷ [])
lcvtop-- (X lanetype-I64 (mk-dim M-1)) (X lanetype-F32 (mk-dim M-2)) (vcvtop---CONVERT half-opt v-sx) c-1 = let c = (convert-- (lsizenn1 (lanetype-Jnn Jnn-I64)) (lsizenn2 (lanetype-Fnn Fnn-F32)) v-sx c-1) in (c ∷ [])
lcvtop-- (X lanetype-I8 (mk-dim M-1)) (X lanetype-F32 (mk-dim M-2)) (vcvtop---CONVERT half-opt v-sx) c-1 = let c = (convert-- (lsizenn1 (lanetype-Jnn Jnn-I8)) (lsizenn2 (lanetype-Fnn Fnn-F32)) v-sx c-1) in (c ∷ [])
lcvtop-- (X lanetype-I16 (mk-dim M-1)) (X lanetype-F32 (mk-dim M-2)) (vcvtop---CONVERT half-opt v-sx) c-1 = let c = (convert-- (lsizenn1 (lanetype-Jnn Jnn-I16)) (lsizenn2 (lanetype-Fnn Fnn-F32)) v-sx c-1) in (c ∷ [])
lcvtop-- (X lanetype-I32 (mk-dim M-1)) (X lanetype-F64 (mk-dim M-2)) (vcvtop---CONVERT half-opt v-sx) c-1 = let c = (convert-- (lsizenn1 (lanetype-Jnn Jnn-I32)) (lsizenn2 (lanetype-Fnn Fnn-F64)) v-sx c-1) in (c ∷ [])
lcvtop-- (X lanetype-I64 (mk-dim M-1)) (X lanetype-F64 (mk-dim M-2)) (vcvtop---CONVERT half-opt v-sx) c-1 = let c = (convert-- (lsizenn1 (lanetype-Jnn Jnn-I64)) (lsizenn2 (lanetype-Fnn Fnn-F64)) v-sx c-1) in (c ∷ [])
lcvtop-- (X lanetype-I8 (mk-dim M-1)) (X lanetype-F64 (mk-dim M-2)) (vcvtop---CONVERT half-opt v-sx) c-1 = let c = (convert-- (lsizenn1 (lanetype-Jnn Jnn-I8)) (lsizenn2 (lanetype-Fnn Fnn-F64)) v-sx c-1) in (c ∷ [])
lcvtop-- (X lanetype-I16 (mk-dim M-1)) (X lanetype-F64 (mk-dim M-2)) (vcvtop---CONVERT half-opt v-sx) c-1 = let c = (convert-- (lsizenn1 (lanetype-Jnn Jnn-I16)) (lsizenn2 (lanetype-Fnn Fnn-F64)) v-sx c-1) in (c ∷ [])
lcvtop-- (X lanetype-F32 (mk-dim M-1)) (X lanetype-I32 (mk-dim M-2)) (vcvtop---TRUNC-SAT v-sx zero-opt) c-1 = let c-opt = (trunc-sat-- (lsizenn1 (lanetype-Fnn Fnn-F32)) (lsizenn2 (lanetype-addrtype I32)) v-sx c-1) in (fromMaybe c-opt)
lcvtop-- (X lanetype-F64 (mk-dim M-1)) (X lanetype-I32 (mk-dim M-2)) (vcvtop---TRUNC-SAT v-sx zero-opt) c-1 = let c-opt = (trunc-sat-- (lsizenn1 (lanetype-Fnn Fnn-F64)) (lsizenn2 (lanetype-addrtype I32)) v-sx c-1) in (fromMaybe c-opt)
lcvtop-- (X lanetype-F32 (mk-dim M-1)) (X lanetype-I64 (mk-dim M-2)) (vcvtop---TRUNC-SAT v-sx zero-opt) c-1 = let c-opt = (trunc-sat-- (lsizenn1 (lanetype-Fnn Fnn-F32)) (lsizenn2 (lanetype-addrtype I64)) v-sx c-1) in (fromMaybe c-opt)
lcvtop-- (X lanetype-F64 (mk-dim M-1)) (X lanetype-I64 (mk-dim M-2)) (vcvtop---TRUNC-SAT v-sx zero-opt) c-1 = let c-opt = (trunc-sat-- (lsizenn1 (lanetype-Fnn Fnn-F64)) (lsizenn2 (lanetype-addrtype I64)) v-sx c-1) in (fromMaybe c-opt)
lcvtop-- (X lanetype-F32 (mk-dim M-1)) (X lanetype-I32 (mk-dim M-2)) (RELAXED-TRUNC v-sx zero-opt) c-1 = let c-opt = (relaxed-trunc-- (lsizenn1 (lanetype-Fnn Fnn-F32)) (lsizenn2 (lanetype-addrtype I32)) v-sx c-1) in (fromMaybe c-opt)
lcvtop-- (X lanetype-F64 (mk-dim M-1)) (X lanetype-I32 (mk-dim M-2)) (RELAXED-TRUNC v-sx zero-opt) c-1 = let c-opt = (relaxed-trunc-- (lsizenn1 (lanetype-Fnn Fnn-F64)) (lsizenn2 (lanetype-addrtype I32)) v-sx c-1) in (fromMaybe c-opt)
lcvtop-- (X lanetype-F32 (mk-dim M-1)) (X lanetype-I64 (mk-dim M-2)) (RELAXED-TRUNC v-sx zero-opt) c-1 = let c-opt = (relaxed-trunc-- (lsizenn1 (lanetype-Fnn Fnn-F32)) (lsizenn2 (lanetype-addrtype I64)) v-sx c-1) in (fromMaybe c-opt)
lcvtop-- (X lanetype-F64 (mk-dim M-1)) (X lanetype-I64 (mk-dim M-2)) (RELAXED-TRUNC v-sx zero-opt) c-1 = let c-opt = (relaxed-trunc-- (lsizenn1 (lanetype-Fnn Fnn-F64)) (lsizenn2 (lanetype-addrtype I64)) v-sx c-1) in (fromMaybe c-opt)
lcvtop-- (X lanetype-F32 (mk-dim M-1)) (X lanetype-F32 (mk-dim M-2)) (vcvtop---DEMOTE ZERO) c-1 = let c-lst = (demote-- (lsizenn1 (lanetype-Fnn Fnn-F32)) (lsizenn2 (lanetype-Fnn Fnn-F32)) c-1) in c-lst
lcvtop-- (X lanetype-F64 (mk-dim M-1)) (X lanetype-F32 (mk-dim M-2)) (vcvtop---DEMOTE ZERO) c-1 = let c-lst = (demote-- (lsizenn1 (lanetype-Fnn Fnn-F64)) (lsizenn2 (lanetype-Fnn Fnn-F32)) c-1) in c-lst
lcvtop-- (X lanetype-F32 (mk-dim M-1)) (X lanetype-F64 (mk-dim M-2)) (vcvtop---DEMOTE ZERO) c-1 = let c-lst = (demote-- (lsizenn1 (lanetype-Fnn Fnn-F32)) (lsizenn2 (lanetype-Fnn Fnn-F64)) c-1) in c-lst
lcvtop-- (X lanetype-F64 (mk-dim M-1)) (X lanetype-F64 (mk-dim M-2)) (vcvtop---DEMOTE ZERO) c-1 = let c-lst = (demote-- (lsizenn1 (lanetype-Fnn Fnn-F64)) (lsizenn2 (lanetype-Fnn Fnn-F64)) c-1) in c-lst
lcvtop-- (X lanetype-F32 (mk-dim M-1)) (X lanetype-F32 (mk-dim M-2)) PROMOTELOW c-1 = let c-lst = (promote-- (lsizenn1 (lanetype-Fnn Fnn-F32)) (lsizenn2 (lanetype-Fnn Fnn-F32)) c-1) in c-lst
lcvtop-- (X lanetype-F64 (mk-dim M-1)) (X lanetype-F32 (mk-dim M-2)) PROMOTELOW c-1 = let c-lst = (promote-- (lsizenn1 (lanetype-Fnn Fnn-F64)) (lsizenn2 (lanetype-Fnn Fnn-F32)) c-1) in c-lst
lcvtop-- (X lanetype-F32 (mk-dim M-1)) (X lanetype-F64 (mk-dim M-2)) PROMOTELOW c-1 = let c-lst = (promote-- (lsizenn1 (lanetype-Fnn Fnn-F32)) (lsizenn2 (lanetype-Fnn Fnn-F64)) c-1) in c-lst
lcvtop-- (X lanetype-F64 (mk-dim M-1)) (X lanetype-F64 (mk-dim M-2)) PROMOTELOW c-1 = let c-lst = (promote-- (lsizenn1 (lanetype-Fnn Fnn-F64)) (lsizenn2 (lanetype-Fnn Fnn-F64)) c-1) in c-lst
lcvtop-- shape-1 shape-2 v-vcvtop-- v-lane- = []

{- Auxiliary Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:183.1-184.41 -}
postulate fun-vcvtop-- : ∀ (shape-1 : shape) (shape-2 : shape) (v-vcvtop-- : (vcvtop-- shape-1 shape-2)) (v-vec- : (uN-fam0 (128))) → (uN-fam0 (128))

{- Auxiliary Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:186.1-187.34 -}
{-# TERMINATING #-}
fun-vshiftop- : (v-ishape : ishape) (v-vshiftop- : (vshiftop- v-ishape)) (v-vec- : (uN-fam0 (128))) (v-u32 : u32) → (uN-fam0 (128))
fun-vshiftop- (mk-ishape (X lanetype-I32 (mk-dim v-M))) vshiftop--SHL v i = (unwrap! (ivshiftop- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) ishl- v i))
fun-vshiftop- (mk-ishape (X lanetype-I64 (mk-dim v-M))) vshiftop--SHL v i = (unwrap! (ivshiftop- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) ishl- v i))
fun-vshiftop- (mk-ishape (X lanetype-I8 (mk-dim v-M))) vshiftop--SHL v i = (unwrap! (ivshiftop- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) ishl- v i))
fun-vshiftop- (mk-ishape (X lanetype-I16 (mk-dim v-M))) vshiftop--SHL v i = (unwrap! (ivshiftop- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) ishl- v i))
fun-vshiftop- (mk-ishape (X lanetype-I32 (mk-dim v-M))) (vshiftop--SHR v-sx) v i = (unwrap! (ivshiftopsx- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) ishr- v-sx v i))
fun-vshiftop- (mk-ishape (X lanetype-I64 (mk-dim v-M))) (vshiftop--SHR v-sx) v i = (unwrap! (ivshiftopsx- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) ishr- v-sx v i))
fun-vshiftop- (mk-ishape (X lanetype-I8 (mk-dim v-M))) (vshiftop--SHR v-sx) v i = (unwrap! (ivshiftopsx- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) ishr- v-sx v i))
fun-vshiftop- (mk-ishape (X lanetype-I16 (mk-dim v-M))) (vshiftop--SHR v-sx) v i = (unwrap! (ivshiftopsx- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) ishr- v-sx v i))
fun-vshiftop- v-ishape v-vshiftop- v-vec- v-u32 = (Inhabited.default-val (inh-vec--fun V128))

{- Auxiliary Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:188.1-189.34 -}
{-# TERMINATING #-}
vbitmaskop- : (v-ishape : ishape) (v-vec- : (uN-fam0 (128))) → u32
vbitmaskop- (mk-ishape (X lanetype-I32 (mk-dim v-M))) v = (ivbitmaskop- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) v)
vbitmaskop- (mk-ishape (X lanetype-I64 (mk-dim v-M))) v = (ivbitmaskop- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) v)
vbitmaskop- (mk-ishape (X lanetype-I8 (mk-dim v-M))) v = (ivbitmaskop- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) v)
vbitmaskop- (mk-ishape (X lanetype-I16 (mk-dim v-M))) v = (ivbitmaskop- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) v)
vbitmaskop- v-ishape v-vec- = default-val

{- Auxiliary Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:190.1-191.31 -}
{-# TERMINATING #-}
fun-vswizzlop- : (v-bshape : bshape) (v-vswizzlop- : (vswizzlop- v-bshape)) (v-vec- : (uN-fam0 (128))) (vec--0 : (uN-fam0 (128))) → (uN-fam0 (128))
fun-vswizzlop- (mk-bshape (X lanetype-I8 (mk-dim v-M))) SWIZZLE v-1 v-2 = (unwrap! (ivswizzlop- (X lanetype-I8 (mk-dim v-M)) iswizzle-lane- v-1 v-2))
fun-vswizzlop- (mk-bshape (X lanetype-I8 (mk-dim v-M))) RELAXED-SWIZZLE v-1 v-2 = (unwrap! (ivswizzlop- (X lanetype-I8 (mk-dim v-M)) irelaxed-swizzle-lane- v-1 v-2))
fun-vswizzlop- v-bshape v-vswizzlop- v-vec- vec--0 = (Inhabited.default-val (inh-vec--fun V128))

{- Auxiliary Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:192.1-193.40 -}
{-# TERMINATING #-}
vshufflop- : (v-bshape : bshape) (var-0-lst : (List laneidx)) (v-vec- : (uN-fam0 (128))) (vec--0 : (uN-fam0 (128))) → (Maybe (uN-fam0 (128)))
vshufflop- (mk-bshape (X lanetype-I8 (mk-dim v-M))) i-lst v-1 v-2 = (ivshufflop- (X lanetype-I8 (mk-dim v-M)) i-lst v-1 v-2)
vshufflop- x0 x1 x2 x3 = nothing

{- Auxiliary Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:195.1-196.49 -}
{-# TERMINATING #-}
vnarrowop-- : (shape-1 : shape) (shape-2 : shape) (v-sx : sx) (v-vec- : (uN-fam0 (128))) (vec--0 : (uN-fam0 (128))) → (uN-fam0 (128))
vnarrowop-- (X lanetype-I32 (mk-dim M-1)) (X lanetype-I32 (mk-dim M-2)) v-sx v-1 v-2 = let c-1-lst = (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim M-1)) v-1) in let c-2-lst = (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim M-1)) v-2) in let c'-1-lst = (map (λ (c-1-118 : (uN-fam0 (32))) → (narrow-- (lsize (lanetype-Jnn Jnn-I32)) (lsize (lanetype-Jnn Jnn-I32)) v-sx c-1-118)) c-1-lst) in let c'-2-lst = (map (λ (c-2-82 : (uN-fam0 (32))) → (narrow-- (lsize (lanetype-Jnn Jnn-I32)) (lsize (lanetype-Jnn Jnn-I32)) v-sx c-2-82)) c-2-lst) in let v = (inv-lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim M-2)) (c'-1-lst ++ c'-2-lst)) in v
vnarrowop-- (X lanetype-I64 (mk-dim M-1)) (X lanetype-I32 (mk-dim M-2)) v-sx v-1 v-2 = let c-1-lst = (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim M-1)) v-1) in let c-2-lst = (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim M-1)) v-2) in let c'-1-lst = (map (λ (c-1-120 : (uN-fam0 (64))) → (narrow-- (lsize (lanetype-Jnn Jnn-I64)) (lsize (lanetype-Jnn Jnn-I32)) v-sx c-1-120)) c-1-lst) in let c'-2-lst = (map (λ (c-2-84 : (uN-fam0 (64))) → (narrow-- (lsize (lanetype-Jnn Jnn-I64)) (lsize (lanetype-Jnn Jnn-I32)) v-sx c-2-84)) c-2-lst) in let v = (inv-lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim M-2)) (c'-1-lst ++ c'-2-lst)) in v
vnarrowop-- (X lanetype-I8 (mk-dim M-1)) (X lanetype-I32 (mk-dim M-2)) v-sx v-1 v-2 = let c-1-lst = (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim M-1)) v-1) in let c-2-lst = (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim M-1)) v-2) in let c'-1-lst = (map (λ (c-1-122 : (uN-fam0 (8))) → (narrow-- (lsize (lanetype-Jnn Jnn-I8)) (lsize (lanetype-Jnn Jnn-I32)) v-sx c-1-122)) c-1-lst) in let c'-2-lst = (map (λ (c-2-86 : (uN-fam0 (8))) → (narrow-- (lsize (lanetype-Jnn Jnn-I8)) (lsize (lanetype-Jnn Jnn-I32)) v-sx c-2-86)) c-2-lst) in let v = (inv-lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim M-2)) (c'-1-lst ++ c'-2-lst)) in v
vnarrowop-- (X lanetype-I16 (mk-dim M-1)) (X lanetype-I32 (mk-dim M-2)) v-sx v-1 v-2 = let c-1-lst = (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim M-1)) v-1) in let c-2-lst = (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim M-1)) v-2) in let c'-1-lst = (map (λ (c-1-124 : (uN-fam0 (16))) → (narrow-- (lsize (lanetype-Jnn Jnn-I16)) (lsize (lanetype-Jnn Jnn-I32)) v-sx c-1-124)) c-1-lst) in let c'-2-lst = (map (λ (c-2-88 : (uN-fam0 (16))) → (narrow-- (lsize (lanetype-Jnn Jnn-I16)) (lsize (lanetype-Jnn Jnn-I32)) v-sx c-2-88)) c-2-lst) in let v = (inv-lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim M-2)) (c'-1-lst ++ c'-2-lst)) in v
vnarrowop-- (X lanetype-I32 (mk-dim M-1)) (X lanetype-I64 (mk-dim M-2)) v-sx v-1 v-2 = let c-1-lst = (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim M-1)) v-1) in let c-2-lst = (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim M-1)) v-2) in let c'-1-lst = (map (λ (c-1-126 : (uN-fam0 (32))) → (narrow-- (lsize (lanetype-Jnn Jnn-I32)) (lsize (lanetype-Jnn Jnn-I64)) v-sx c-1-126)) c-1-lst) in let c'-2-lst = (map (λ (c-2-90 : (uN-fam0 (32))) → (narrow-- (lsize (lanetype-Jnn Jnn-I32)) (lsize (lanetype-Jnn Jnn-I64)) v-sx c-2-90)) c-2-lst) in let v = (inv-lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim M-2)) (c'-1-lst ++ c'-2-lst)) in v
vnarrowop-- (X lanetype-I64 (mk-dim M-1)) (X lanetype-I64 (mk-dim M-2)) v-sx v-1 v-2 = let c-1-lst = (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim M-1)) v-1) in let c-2-lst = (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim M-1)) v-2) in let c'-1-lst = (map (λ (c-1-128 : (uN-fam0 (64))) → (narrow-- (lsize (lanetype-Jnn Jnn-I64)) (lsize (lanetype-Jnn Jnn-I64)) v-sx c-1-128)) c-1-lst) in let c'-2-lst = (map (λ (c-2-92 : (uN-fam0 (64))) → (narrow-- (lsize (lanetype-Jnn Jnn-I64)) (lsize (lanetype-Jnn Jnn-I64)) v-sx c-2-92)) c-2-lst) in let v = (inv-lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim M-2)) (c'-1-lst ++ c'-2-lst)) in v
vnarrowop-- (X lanetype-I8 (mk-dim M-1)) (X lanetype-I64 (mk-dim M-2)) v-sx v-1 v-2 = let c-1-lst = (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim M-1)) v-1) in let c-2-lst = (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim M-1)) v-2) in let c'-1-lst = (map (λ (c-1-130 : (uN-fam0 (8))) → (narrow-- (lsize (lanetype-Jnn Jnn-I8)) (lsize (lanetype-Jnn Jnn-I64)) v-sx c-1-130)) c-1-lst) in let c'-2-lst = (map (λ (c-2-94 : (uN-fam0 (8))) → (narrow-- (lsize (lanetype-Jnn Jnn-I8)) (lsize (lanetype-Jnn Jnn-I64)) v-sx c-2-94)) c-2-lst) in let v = (inv-lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim M-2)) (c'-1-lst ++ c'-2-lst)) in v
vnarrowop-- (X lanetype-I16 (mk-dim M-1)) (X lanetype-I64 (mk-dim M-2)) v-sx v-1 v-2 = let c-1-lst = (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim M-1)) v-1) in let c-2-lst = (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim M-1)) v-2) in let c'-1-lst = (map (λ (c-1-132 : (uN-fam0 (16))) → (narrow-- (lsize (lanetype-Jnn Jnn-I16)) (lsize (lanetype-Jnn Jnn-I64)) v-sx c-1-132)) c-1-lst) in let c'-2-lst = (map (λ (c-2-96 : (uN-fam0 (16))) → (narrow-- (lsize (lanetype-Jnn Jnn-I16)) (lsize (lanetype-Jnn Jnn-I64)) v-sx c-2-96)) c-2-lst) in let v = (inv-lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim M-2)) (c'-1-lst ++ c'-2-lst)) in v
vnarrowop-- (X lanetype-I32 (mk-dim M-1)) (X lanetype-I8 (mk-dim M-2)) v-sx v-1 v-2 = let c-1-lst = (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim M-1)) v-1) in let c-2-lst = (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim M-1)) v-2) in let c'-1-lst = (map (λ (c-1-134 : (uN-fam0 (32))) → (narrow-- (lsize (lanetype-Jnn Jnn-I32)) (lsize (lanetype-Jnn Jnn-I8)) v-sx c-1-134)) c-1-lst) in let c'-2-lst = (map (λ (c-2-98 : (uN-fam0 (32))) → (narrow-- (lsize (lanetype-Jnn Jnn-I32)) (lsize (lanetype-Jnn Jnn-I8)) v-sx c-2-98)) c-2-lst) in let v = (inv-lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim M-2)) (c'-1-lst ++ c'-2-lst)) in v
vnarrowop-- (X lanetype-I64 (mk-dim M-1)) (X lanetype-I8 (mk-dim M-2)) v-sx v-1 v-2 = let c-1-lst = (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim M-1)) v-1) in let c-2-lst = (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim M-1)) v-2) in let c'-1-lst = (map (λ (c-1-136 : (uN-fam0 (64))) → (narrow-- (lsize (lanetype-Jnn Jnn-I64)) (lsize (lanetype-Jnn Jnn-I8)) v-sx c-1-136)) c-1-lst) in let c'-2-lst = (map (λ (c-2-100 : (uN-fam0 (64))) → (narrow-- (lsize (lanetype-Jnn Jnn-I64)) (lsize (lanetype-Jnn Jnn-I8)) v-sx c-2-100)) c-2-lst) in let v = (inv-lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim M-2)) (c'-1-lst ++ c'-2-lst)) in v
vnarrowop-- (X lanetype-I8 (mk-dim M-1)) (X lanetype-I8 (mk-dim M-2)) v-sx v-1 v-2 = let c-1-lst = (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim M-1)) v-1) in let c-2-lst = (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim M-1)) v-2) in let c'-1-lst = (map (λ (c-1-138 : (uN-fam0 (8))) → (narrow-- (lsize (lanetype-Jnn Jnn-I8)) (lsize (lanetype-Jnn Jnn-I8)) v-sx c-1-138)) c-1-lst) in let c'-2-lst = (map (λ (c-2-102 : (uN-fam0 (8))) → (narrow-- (lsize (lanetype-Jnn Jnn-I8)) (lsize (lanetype-Jnn Jnn-I8)) v-sx c-2-102)) c-2-lst) in let v = (inv-lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim M-2)) (c'-1-lst ++ c'-2-lst)) in v
vnarrowop-- (X lanetype-I16 (mk-dim M-1)) (X lanetype-I8 (mk-dim M-2)) v-sx v-1 v-2 = let c-1-lst = (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim M-1)) v-1) in let c-2-lst = (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim M-1)) v-2) in let c'-1-lst = (map (λ (c-1-140 : (uN-fam0 (16))) → (narrow-- (lsize (lanetype-Jnn Jnn-I16)) (lsize (lanetype-Jnn Jnn-I8)) v-sx c-1-140)) c-1-lst) in let c'-2-lst = (map (λ (c-2-104 : (uN-fam0 (16))) → (narrow-- (lsize (lanetype-Jnn Jnn-I16)) (lsize (lanetype-Jnn Jnn-I8)) v-sx c-2-104)) c-2-lst) in let v = (inv-lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim M-2)) (c'-1-lst ++ c'-2-lst)) in v
vnarrowop-- (X lanetype-I32 (mk-dim M-1)) (X lanetype-I16 (mk-dim M-2)) v-sx v-1 v-2 = let c-1-lst = (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim M-1)) v-1) in let c-2-lst = (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim M-1)) v-2) in let c'-1-lst = (map (λ (c-1-142 : (uN-fam0 (32))) → (narrow-- (lsize (lanetype-Jnn Jnn-I32)) (lsize (lanetype-Jnn Jnn-I16)) v-sx c-1-142)) c-1-lst) in let c'-2-lst = (map (λ (c-2-106 : (uN-fam0 (32))) → (narrow-- (lsize (lanetype-Jnn Jnn-I32)) (lsize (lanetype-Jnn Jnn-I16)) v-sx c-2-106)) c-2-lst) in let v = (inv-lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim M-2)) (c'-1-lst ++ c'-2-lst)) in v
vnarrowop-- (X lanetype-I64 (mk-dim M-1)) (X lanetype-I16 (mk-dim M-2)) v-sx v-1 v-2 = let c-1-lst = (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim M-1)) v-1) in let c-2-lst = (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim M-1)) v-2) in let c'-1-lst = (map (λ (c-1-144 : (uN-fam0 (64))) → (narrow-- (lsize (lanetype-Jnn Jnn-I64)) (lsize (lanetype-Jnn Jnn-I16)) v-sx c-1-144)) c-1-lst) in let c'-2-lst = (map (λ (c-2-108 : (uN-fam0 (64))) → (narrow-- (lsize (lanetype-Jnn Jnn-I64)) (lsize (lanetype-Jnn Jnn-I16)) v-sx c-2-108)) c-2-lst) in let v = (inv-lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim M-2)) (c'-1-lst ++ c'-2-lst)) in v
vnarrowop-- (X lanetype-I8 (mk-dim M-1)) (X lanetype-I16 (mk-dim M-2)) v-sx v-1 v-2 = let c-1-lst = (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim M-1)) v-1) in let c-2-lst = (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim M-1)) v-2) in let c'-1-lst = (map (λ (c-1-146 : (uN-fam0 (8))) → (narrow-- (lsize (lanetype-Jnn Jnn-I8)) (lsize (lanetype-Jnn Jnn-I16)) v-sx c-1-146)) c-1-lst) in let c'-2-lst = (map (λ (c-2-110 : (uN-fam0 (8))) → (narrow-- (lsize (lanetype-Jnn Jnn-I8)) (lsize (lanetype-Jnn Jnn-I16)) v-sx c-2-110)) c-2-lst) in let v = (inv-lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim M-2)) (c'-1-lst ++ c'-2-lst)) in v
vnarrowop-- (X lanetype-I16 (mk-dim M-1)) (X lanetype-I16 (mk-dim M-2)) v-sx v-1 v-2 = let c-1-lst = (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim M-1)) v-1) in let c-2-lst = (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim M-1)) v-2) in let c'-1-lst = (map (λ (c-1-148 : (uN-fam0 (16))) → (narrow-- (lsize (lanetype-Jnn Jnn-I16)) (lsize (lanetype-Jnn Jnn-I16)) v-sx c-1-148)) c-1-lst) in let c'-2-lst = (map (λ (c-2-112 : (uN-fam0 (16))) → (narrow-- (lsize (lanetype-Jnn Jnn-I16)) (lsize (lanetype-Jnn Jnn-I16)) v-sx c-2-112)) c-2-lst) in let v = (inv-lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim M-2)) (c'-1-lst ++ c'-2-lst)) in v
vnarrowop-- shape-1 shape-2 v-sx v-vec- vec--0 = (Inhabited.default-val (inh-vec--fun V128))

{- Auxiliary Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:356.1-356.76 -}
postulate ivadd-pairwise- : ∀ (v-N : N) (var-0-lst : (List (uN-fam0 (v-N)))) → (List (uN-fam0 (v-N)))

{- Auxiliary Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:342.1-342.93 -}
{-# TERMINATING #-}
ivextunop-- : (shape-1 : shape) (shape-2 : shape) (f- : (v-N : N) → (_ : (List (uN-fam0 (v-N)))) → (List (uN-fam0 (v-N)))) (v-sx : sx) (v-vec- : (uN-fam0 (128))) → (uN-fam0 (128))
ivextunop-- (X lanetype-I32 (mk-dim M-1)) (X lanetype-I32 (mk-dim M-2)) f- v-sx v-1 = let c-1-lst = (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim M-1)) v-1) in let c'-1-lst = (map (λ (c-1-150 : (uN-fam0 (32))) → (extend-- (lsizenn1 (lanetype-Jnn Jnn-I32)) (lsizenn2 (lanetype-Jnn Jnn-I32)) v-sx c-1-150)) c-1-lst) in let c-lst = (f- (lsizenn2 (lanetype-Jnn Jnn-I32)) c'-1-lst) in (inv-lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim M-2)) c-lst)
ivextunop-- (X lanetype-I64 (mk-dim M-1)) (X lanetype-I32 (mk-dim M-2)) f- v-sx v-1 = let c-1-lst = (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim M-1)) v-1) in let c'-1-lst = (map (λ (c-1-152 : (uN-fam0 (64))) → (extend-- (lsizenn1 (lanetype-Jnn Jnn-I64)) (lsizenn2 (lanetype-Jnn Jnn-I32)) v-sx c-1-152)) c-1-lst) in let c-lst = (f- (lsizenn2 (lanetype-Jnn Jnn-I32)) c'-1-lst) in (inv-lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim M-2)) c-lst)
ivextunop-- (X lanetype-I8 (mk-dim M-1)) (X lanetype-I32 (mk-dim M-2)) f- v-sx v-1 = let c-1-lst = (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim M-1)) v-1) in let c'-1-lst = (map (λ (c-1-154 : (uN-fam0 (8))) → (extend-- (lsizenn1 (lanetype-Jnn Jnn-I8)) (lsizenn2 (lanetype-Jnn Jnn-I32)) v-sx c-1-154)) c-1-lst) in let c-lst = (f- (lsizenn2 (lanetype-Jnn Jnn-I32)) c'-1-lst) in (inv-lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim M-2)) c-lst)
ivextunop-- (X lanetype-I16 (mk-dim M-1)) (X lanetype-I32 (mk-dim M-2)) f- v-sx v-1 = let c-1-lst = (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim M-1)) v-1) in let c'-1-lst = (map (λ (c-1-156 : (uN-fam0 (16))) → (extend-- (lsizenn1 (lanetype-Jnn Jnn-I16)) (lsizenn2 (lanetype-Jnn Jnn-I32)) v-sx c-1-156)) c-1-lst) in let c-lst = (f- (lsizenn2 (lanetype-Jnn Jnn-I32)) c'-1-lst) in (inv-lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim M-2)) c-lst)
ivextunop-- (X lanetype-I32 (mk-dim M-1)) (X lanetype-I64 (mk-dim M-2)) f- v-sx v-1 = let c-1-lst = (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim M-1)) v-1) in let c'-1-lst = (map (λ (c-1-158 : (uN-fam0 (32))) → (extend-- (lsizenn1 (lanetype-Jnn Jnn-I32)) (lsizenn2 (lanetype-Jnn Jnn-I64)) v-sx c-1-158)) c-1-lst) in let c-lst = (f- (lsizenn2 (lanetype-Jnn Jnn-I64)) c'-1-lst) in (inv-lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim M-2)) c-lst)
ivextunop-- (X lanetype-I64 (mk-dim M-1)) (X lanetype-I64 (mk-dim M-2)) f- v-sx v-1 = let c-1-lst = (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim M-1)) v-1) in let c'-1-lst = (map (λ (c-1-160 : (uN-fam0 (64))) → (extend-- (lsizenn1 (lanetype-Jnn Jnn-I64)) (lsizenn2 (lanetype-Jnn Jnn-I64)) v-sx c-1-160)) c-1-lst) in let c-lst = (f- (lsizenn2 (lanetype-Jnn Jnn-I64)) c'-1-lst) in (inv-lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim M-2)) c-lst)
ivextunop-- (X lanetype-I8 (mk-dim M-1)) (X lanetype-I64 (mk-dim M-2)) f- v-sx v-1 = let c-1-lst = (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim M-1)) v-1) in let c'-1-lst = (map (λ (c-1-162 : (uN-fam0 (8))) → (extend-- (lsizenn1 (lanetype-Jnn Jnn-I8)) (lsizenn2 (lanetype-Jnn Jnn-I64)) v-sx c-1-162)) c-1-lst) in let c-lst = (f- (lsizenn2 (lanetype-Jnn Jnn-I64)) c'-1-lst) in (inv-lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim M-2)) c-lst)
ivextunop-- (X lanetype-I16 (mk-dim M-1)) (X lanetype-I64 (mk-dim M-2)) f- v-sx v-1 = let c-1-lst = (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim M-1)) v-1) in let c'-1-lst = (map (λ (c-1-164 : (uN-fam0 (16))) → (extend-- (lsizenn1 (lanetype-Jnn Jnn-I16)) (lsizenn2 (lanetype-Jnn Jnn-I64)) v-sx c-1-164)) c-1-lst) in let c-lst = (f- (lsizenn2 (lanetype-Jnn Jnn-I64)) c'-1-lst) in (inv-lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim M-2)) c-lst)
ivextunop-- (X lanetype-I32 (mk-dim M-1)) (X lanetype-I8 (mk-dim M-2)) f- v-sx v-1 = let c-1-lst = (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim M-1)) v-1) in let c'-1-lst = (map (λ (c-1-166 : (uN-fam0 (32))) → (extend-- (lsizenn1 (lanetype-Jnn Jnn-I32)) (lsizenn2 (lanetype-Jnn Jnn-I8)) v-sx c-1-166)) c-1-lst) in let c-lst = (f- (lsizenn2 (lanetype-Jnn Jnn-I8)) c'-1-lst) in (inv-lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim M-2)) c-lst)
ivextunop-- (X lanetype-I64 (mk-dim M-1)) (X lanetype-I8 (mk-dim M-2)) f- v-sx v-1 = let c-1-lst = (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim M-1)) v-1) in let c'-1-lst = (map (λ (c-1-168 : (uN-fam0 (64))) → (extend-- (lsizenn1 (lanetype-Jnn Jnn-I64)) (lsizenn2 (lanetype-Jnn Jnn-I8)) v-sx c-1-168)) c-1-lst) in let c-lst = (f- (lsizenn2 (lanetype-Jnn Jnn-I8)) c'-1-lst) in (inv-lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim M-2)) c-lst)
ivextunop-- (X lanetype-I8 (mk-dim M-1)) (X lanetype-I8 (mk-dim M-2)) f- v-sx v-1 = let c-1-lst = (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim M-1)) v-1) in let c'-1-lst = (map (λ (c-1-170 : (uN-fam0 (8))) → (extend-- (lsizenn1 (lanetype-Jnn Jnn-I8)) (lsizenn2 (lanetype-Jnn Jnn-I8)) v-sx c-1-170)) c-1-lst) in let c-lst = (f- (lsizenn2 (lanetype-Jnn Jnn-I8)) c'-1-lst) in (inv-lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim M-2)) c-lst)
ivextunop-- (X lanetype-I16 (mk-dim M-1)) (X lanetype-I8 (mk-dim M-2)) f- v-sx v-1 = let c-1-lst = (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim M-1)) v-1) in let c'-1-lst = (map (λ (c-1-172 : (uN-fam0 (16))) → (extend-- (lsizenn1 (lanetype-Jnn Jnn-I16)) (lsizenn2 (lanetype-Jnn Jnn-I8)) v-sx c-1-172)) c-1-lst) in let c-lst = (f- (lsizenn2 (lanetype-Jnn Jnn-I8)) c'-1-lst) in (inv-lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim M-2)) c-lst)
ivextunop-- (X lanetype-I32 (mk-dim M-1)) (X lanetype-I16 (mk-dim M-2)) f- v-sx v-1 = let c-1-lst = (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim M-1)) v-1) in let c'-1-lst = (map (λ (c-1-174 : (uN-fam0 (32))) → (extend-- (lsizenn1 (lanetype-Jnn Jnn-I32)) (lsizenn2 (lanetype-Jnn Jnn-I16)) v-sx c-1-174)) c-1-lst) in let c-lst = (f- (lsizenn2 (lanetype-Jnn Jnn-I16)) c'-1-lst) in (inv-lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim M-2)) c-lst)
ivextunop-- (X lanetype-I64 (mk-dim M-1)) (X lanetype-I16 (mk-dim M-2)) f- v-sx v-1 = let c-1-lst = (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim M-1)) v-1) in let c'-1-lst = (map (λ (c-1-176 : (uN-fam0 (64))) → (extend-- (lsizenn1 (lanetype-Jnn Jnn-I64)) (lsizenn2 (lanetype-Jnn Jnn-I16)) v-sx c-1-176)) c-1-lst) in let c-lst = (f- (lsizenn2 (lanetype-Jnn Jnn-I16)) c'-1-lst) in (inv-lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim M-2)) c-lst)
ivextunop-- (X lanetype-I8 (mk-dim M-1)) (X lanetype-I16 (mk-dim M-2)) f- v-sx v-1 = let c-1-lst = (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim M-1)) v-1) in let c'-1-lst = (map (λ (c-1-178 : (uN-fam0 (8))) → (extend-- (lsizenn1 (lanetype-Jnn Jnn-I8)) (lsizenn2 (lanetype-Jnn Jnn-I16)) v-sx c-1-178)) c-1-lst) in let c-lst = (f- (lsizenn2 (lanetype-Jnn Jnn-I16)) c'-1-lst) in (inv-lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim M-2)) c-lst)
ivextunop-- (X lanetype-I16 (mk-dim M-1)) (X lanetype-I16 (mk-dim M-2)) f- v-sx v-1 = let c-1-lst = (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim M-1)) v-1) in let c'-1-lst = (map (λ (c-1-180 : (uN-fam0 (16))) → (extend-- (lsizenn1 (lanetype-Jnn Jnn-I16)) (lsizenn2 (lanetype-Jnn Jnn-I16)) v-sx c-1-180)) c-1-lst) in let c-lst = (f- (lsizenn2 (lanetype-Jnn Jnn-I16)) c'-1-lst) in (inv-lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim M-2)) c-lst)
ivextunop-- shape-1 shape-2 f- v-sx v-vec- = (Inhabited.default-val (inh-vec--fun V128))

{- Auxiliary Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:198.1-199.32 -}
{-# TERMINATING #-}
fun-vextunop-- : (ishape-1 : ishape) (ishape-2 : ishape) (v-vextunop-- : (vextunop-- ishape-1 ishape-2)) (v-vec- : (uN-fam0 (128))) → (uN-fam0 (128))
fun-vextunop-- (mk-ishape (X lanetype-I32 (mk-dim M-1))) (mk-ishape (X lanetype-I32 (mk-dim M-2))) (EXTADD-PAIRWISE v-sx) v-1 = (ivextunop-- (X (lanetype-Jnn Jnn-I32) (mk-dim M-1)) (X (lanetype-Jnn Jnn-I32) (mk-dim M-2)) ivadd-pairwise- v-sx v-1)
fun-vextunop-- (mk-ishape (X lanetype-I64 (mk-dim M-1))) (mk-ishape (X lanetype-I32 (mk-dim M-2))) (EXTADD-PAIRWISE v-sx) v-1 = (ivextunop-- (X (lanetype-Jnn Jnn-I64) (mk-dim M-1)) (X (lanetype-Jnn Jnn-I32) (mk-dim M-2)) ivadd-pairwise- v-sx v-1)
fun-vextunop-- (mk-ishape (X lanetype-I8 (mk-dim M-1))) (mk-ishape (X lanetype-I32 (mk-dim M-2))) (EXTADD-PAIRWISE v-sx) v-1 = (ivextunop-- (X (lanetype-Jnn Jnn-I8) (mk-dim M-1)) (X (lanetype-Jnn Jnn-I32) (mk-dim M-2)) ivadd-pairwise- v-sx v-1)
fun-vextunop-- (mk-ishape (X lanetype-I16 (mk-dim M-1))) (mk-ishape (X lanetype-I32 (mk-dim M-2))) (EXTADD-PAIRWISE v-sx) v-1 = (ivextunop-- (X (lanetype-Jnn Jnn-I16) (mk-dim M-1)) (X (lanetype-Jnn Jnn-I32) (mk-dim M-2)) ivadd-pairwise- v-sx v-1)
fun-vextunop-- (mk-ishape (X lanetype-I32 (mk-dim M-1))) (mk-ishape (X lanetype-I64 (mk-dim M-2))) (EXTADD-PAIRWISE v-sx) v-1 = (ivextunop-- (X (lanetype-Jnn Jnn-I32) (mk-dim M-1)) (X (lanetype-Jnn Jnn-I64) (mk-dim M-2)) ivadd-pairwise- v-sx v-1)
fun-vextunop-- (mk-ishape (X lanetype-I64 (mk-dim M-1))) (mk-ishape (X lanetype-I64 (mk-dim M-2))) (EXTADD-PAIRWISE v-sx) v-1 = (ivextunop-- (X (lanetype-Jnn Jnn-I64) (mk-dim M-1)) (X (lanetype-Jnn Jnn-I64) (mk-dim M-2)) ivadd-pairwise- v-sx v-1)
fun-vextunop-- (mk-ishape (X lanetype-I8 (mk-dim M-1))) (mk-ishape (X lanetype-I64 (mk-dim M-2))) (EXTADD-PAIRWISE v-sx) v-1 = (ivextunop-- (X (lanetype-Jnn Jnn-I8) (mk-dim M-1)) (X (lanetype-Jnn Jnn-I64) (mk-dim M-2)) ivadd-pairwise- v-sx v-1)
fun-vextunop-- (mk-ishape (X lanetype-I16 (mk-dim M-1))) (mk-ishape (X lanetype-I64 (mk-dim M-2))) (EXTADD-PAIRWISE v-sx) v-1 = (ivextunop-- (X (lanetype-Jnn Jnn-I16) (mk-dim M-1)) (X (lanetype-Jnn Jnn-I64) (mk-dim M-2)) ivadd-pairwise- v-sx v-1)
fun-vextunop-- (mk-ishape (X lanetype-I32 (mk-dim M-1))) (mk-ishape (X lanetype-I8 (mk-dim M-2))) (EXTADD-PAIRWISE v-sx) v-1 = (ivextunop-- (X (lanetype-Jnn Jnn-I32) (mk-dim M-1)) (X (lanetype-Jnn Jnn-I8) (mk-dim M-2)) ivadd-pairwise- v-sx v-1)
fun-vextunop-- (mk-ishape (X lanetype-I64 (mk-dim M-1))) (mk-ishape (X lanetype-I8 (mk-dim M-2))) (EXTADD-PAIRWISE v-sx) v-1 = (ivextunop-- (X (lanetype-Jnn Jnn-I64) (mk-dim M-1)) (X (lanetype-Jnn Jnn-I8) (mk-dim M-2)) ivadd-pairwise- v-sx v-1)
fun-vextunop-- (mk-ishape (X lanetype-I8 (mk-dim M-1))) (mk-ishape (X lanetype-I8 (mk-dim M-2))) (EXTADD-PAIRWISE v-sx) v-1 = (ivextunop-- (X (lanetype-Jnn Jnn-I8) (mk-dim M-1)) (X (lanetype-Jnn Jnn-I8) (mk-dim M-2)) ivadd-pairwise- v-sx v-1)
fun-vextunop-- (mk-ishape (X lanetype-I16 (mk-dim M-1))) (mk-ishape (X lanetype-I8 (mk-dim M-2))) (EXTADD-PAIRWISE v-sx) v-1 = (ivextunop-- (X (lanetype-Jnn Jnn-I16) (mk-dim M-1)) (X (lanetype-Jnn Jnn-I8) (mk-dim M-2)) ivadd-pairwise- v-sx v-1)
fun-vextunop-- (mk-ishape (X lanetype-I32 (mk-dim M-1))) (mk-ishape (X lanetype-I16 (mk-dim M-2))) (EXTADD-PAIRWISE v-sx) v-1 = (ivextunop-- (X (lanetype-Jnn Jnn-I32) (mk-dim M-1)) (X (lanetype-Jnn Jnn-I16) (mk-dim M-2)) ivadd-pairwise- v-sx v-1)
fun-vextunop-- (mk-ishape (X lanetype-I64 (mk-dim M-1))) (mk-ishape (X lanetype-I16 (mk-dim M-2))) (EXTADD-PAIRWISE v-sx) v-1 = (ivextunop-- (X (lanetype-Jnn Jnn-I64) (mk-dim M-1)) (X (lanetype-Jnn Jnn-I16) (mk-dim M-2)) ivadd-pairwise- v-sx v-1)
fun-vextunop-- (mk-ishape (X lanetype-I8 (mk-dim M-1))) (mk-ishape (X lanetype-I16 (mk-dim M-2))) (EXTADD-PAIRWISE v-sx) v-1 = (ivextunop-- (X (lanetype-Jnn Jnn-I8) (mk-dim M-1)) (X (lanetype-Jnn Jnn-I16) (mk-dim M-2)) ivadd-pairwise- v-sx v-1)
fun-vextunop-- (mk-ishape (X lanetype-I16 (mk-dim M-1))) (mk-ishape (X lanetype-I16 (mk-dim M-2))) (EXTADD-PAIRWISE v-sx) v-1 = (ivextunop-- (X (lanetype-Jnn Jnn-I16) (mk-dim M-1)) (X (lanetype-Jnn Jnn-I16) (mk-dim M-2)) ivadd-pairwise- v-sx v-1)
fun-vextunop-- ishape-1 ishape-2 v-vextunop-- v-vec- = (Inhabited.default-val (inh-vec--fun V128))

{- Auxiliary Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:363.1-363.40 -}
postulate ivdot- : ∀ (v-N : N) (var-0-lst : (List (uN-fam0 (v-N)))) (var-1-lst : (List (uN-fam0 (v-N)))) → (List (uN-fam0 (v-N)))

{- Auxiliary Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:367.1-367.76 -}
postulate ivdot-sat- : ∀ (v-N : N) (var-0-lst : (List (uN-fam0 (v-N)))) (var-1-lst : (List (uN-fam0 (v-N)))) → (List (uN-fam0 (v-N)))

{- Auxiliary Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:348.1-348.136 -}
{-# TERMINATING #-}
ivextbinop-- : (shape-1 : shape) (shape-2 : shape) (f- : (v-N : N) → (_ : (List (uN-fam0 (v-N)))) → (_ : (List (uN-fam0 (v-N)))) → (List (uN-fam0 (v-N)))) (v-sx : sx) (sx-0 : sx) (v-laneidx : laneidx) (laneidx-0 : laneidx) (v-vec- : (uN-fam0 (128))) (vec--0 : (uN-fam0 (128))) → (uN-fam0 (128))
ivextbinop-- (X lanetype-I32 (mk-dim M-1)) (X lanetype-I32 (mk-dim M-2)) f- sx-1 sx-2 i k v-1 v-2 = let c-1-lst = (slice (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim M-1)) v-1) (proj-uN-0 8 i) (proj-uN-0 8 k)) in let c-2-lst = (slice (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim M-1)) v-2) (proj-uN-0 8 i) (proj-uN-0 8 k)) in let c'-1-lst = (map (λ (c-1-182 : (uN-fam0 (32))) → (extend-- (lsizenn1 (lanetype-Jnn Jnn-I32)) (lsizenn2 (lanetype-Jnn Jnn-I32)) sx-1 c-1-182)) c-1-lst) in let c'-2-lst = (map (λ (c-2-114 : (uN-fam0 (32))) → (extend-- (lsizenn1 (lanetype-Jnn Jnn-I32)) (lsizenn2 (lanetype-Jnn Jnn-I32)) sx-2 c-2-114)) c-2-lst) in let c-lst = (f- (lsizenn2 (lanetype-Jnn Jnn-I32)) c'-1-lst c'-2-lst) in (inv-lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim M-2)) c-lst)
ivextbinop-- (X lanetype-I64 (mk-dim M-1)) (X lanetype-I32 (mk-dim M-2)) f- sx-1 sx-2 i k v-1 v-2 = let c-1-lst = (slice (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim M-1)) v-1) (proj-uN-0 8 i) (proj-uN-0 8 k)) in let c-2-lst = (slice (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim M-1)) v-2) (proj-uN-0 8 i) (proj-uN-0 8 k)) in let c'-1-lst = (map (λ (c-1-184 : (uN-fam0 (64))) → (extend-- (lsizenn1 (lanetype-Jnn Jnn-I64)) (lsizenn2 (lanetype-Jnn Jnn-I32)) sx-1 c-1-184)) c-1-lst) in let c'-2-lst = (map (λ (c-2-116 : (uN-fam0 (64))) → (extend-- (lsizenn1 (lanetype-Jnn Jnn-I64)) (lsizenn2 (lanetype-Jnn Jnn-I32)) sx-2 c-2-116)) c-2-lst) in let c-lst = (f- (lsizenn2 (lanetype-Jnn Jnn-I32)) c'-1-lst c'-2-lst) in (inv-lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim M-2)) c-lst)
ivextbinop-- (X lanetype-I8 (mk-dim M-1)) (X lanetype-I32 (mk-dim M-2)) f- sx-1 sx-2 i k v-1 v-2 = let c-1-lst = (slice (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim M-1)) v-1) (proj-uN-0 8 i) (proj-uN-0 8 k)) in let c-2-lst = (slice (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim M-1)) v-2) (proj-uN-0 8 i) (proj-uN-0 8 k)) in let c'-1-lst = (map (λ (c-1-186 : (uN-fam0 (8))) → (extend-- (lsizenn1 (lanetype-Jnn Jnn-I8)) (lsizenn2 (lanetype-Jnn Jnn-I32)) sx-1 c-1-186)) c-1-lst) in let c'-2-lst = (map (λ (c-2-118 : (uN-fam0 (8))) → (extend-- (lsizenn1 (lanetype-Jnn Jnn-I8)) (lsizenn2 (lanetype-Jnn Jnn-I32)) sx-2 c-2-118)) c-2-lst) in let c-lst = (f- (lsizenn2 (lanetype-Jnn Jnn-I32)) c'-1-lst c'-2-lst) in (inv-lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim M-2)) c-lst)
ivextbinop-- (X lanetype-I16 (mk-dim M-1)) (X lanetype-I32 (mk-dim M-2)) f- sx-1 sx-2 i k v-1 v-2 = let c-1-lst = (slice (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim M-1)) v-1) (proj-uN-0 8 i) (proj-uN-0 8 k)) in let c-2-lst = (slice (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim M-1)) v-2) (proj-uN-0 8 i) (proj-uN-0 8 k)) in let c'-1-lst = (map (λ (c-1-188 : (uN-fam0 (16))) → (extend-- (lsizenn1 (lanetype-Jnn Jnn-I16)) (lsizenn2 (lanetype-Jnn Jnn-I32)) sx-1 c-1-188)) c-1-lst) in let c'-2-lst = (map (λ (c-2-120 : (uN-fam0 (16))) → (extend-- (lsizenn1 (lanetype-Jnn Jnn-I16)) (lsizenn2 (lanetype-Jnn Jnn-I32)) sx-2 c-2-120)) c-2-lst) in let c-lst = (f- (lsizenn2 (lanetype-Jnn Jnn-I32)) c'-1-lst c'-2-lst) in (inv-lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim M-2)) c-lst)
ivextbinop-- (X lanetype-I32 (mk-dim M-1)) (X lanetype-I64 (mk-dim M-2)) f- sx-1 sx-2 i k v-1 v-2 = let c-1-lst = (slice (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim M-1)) v-1) (proj-uN-0 8 i) (proj-uN-0 8 k)) in let c-2-lst = (slice (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim M-1)) v-2) (proj-uN-0 8 i) (proj-uN-0 8 k)) in let c'-1-lst = (map (λ (c-1-190 : (uN-fam0 (32))) → (extend-- (lsizenn1 (lanetype-Jnn Jnn-I32)) (lsizenn2 (lanetype-Jnn Jnn-I64)) sx-1 c-1-190)) c-1-lst) in let c'-2-lst = (map (λ (c-2-122 : (uN-fam0 (32))) → (extend-- (lsizenn1 (lanetype-Jnn Jnn-I32)) (lsizenn2 (lanetype-Jnn Jnn-I64)) sx-2 c-2-122)) c-2-lst) in let c-lst = (f- (lsizenn2 (lanetype-Jnn Jnn-I64)) c'-1-lst c'-2-lst) in (inv-lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim M-2)) c-lst)
ivextbinop-- (X lanetype-I64 (mk-dim M-1)) (X lanetype-I64 (mk-dim M-2)) f- sx-1 sx-2 i k v-1 v-2 = let c-1-lst = (slice (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim M-1)) v-1) (proj-uN-0 8 i) (proj-uN-0 8 k)) in let c-2-lst = (slice (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim M-1)) v-2) (proj-uN-0 8 i) (proj-uN-0 8 k)) in let c'-1-lst = (map (λ (c-1-192 : (uN-fam0 (64))) → (extend-- (lsizenn1 (lanetype-Jnn Jnn-I64)) (lsizenn2 (lanetype-Jnn Jnn-I64)) sx-1 c-1-192)) c-1-lst) in let c'-2-lst = (map (λ (c-2-124 : (uN-fam0 (64))) → (extend-- (lsizenn1 (lanetype-Jnn Jnn-I64)) (lsizenn2 (lanetype-Jnn Jnn-I64)) sx-2 c-2-124)) c-2-lst) in let c-lst = (f- (lsizenn2 (lanetype-Jnn Jnn-I64)) c'-1-lst c'-2-lst) in (inv-lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim M-2)) c-lst)
ivextbinop-- (X lanetype-I8 (mk-dim M-1)) (X lanetype-I64 (mk-dim M-2)) f- sx-1 sx-2 i k v-1 v-2 = let c-1-lst = (slice (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim M-1)) v-1) (proj-uN-0 8 i) (proj-uN-0 8 k)) in let c-2-lst = (slice (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim M-1)) v-2) (proj-uN-0 8 i) (proj-uN-0 8 k)) in let c'-1-lst = (map (λ (c-1-194 : (uN-fam0 (8))) → (extend-- (lsizenn1 (lanetype-Jnn Jnn-I8)) (lsizenn2 (lanetype-Jnn Jnn-I64)) sx-1 c-1-194)) c-1-lst) in let c'-2-lst = (map (λ (c-2-126 : (uN-fam0 (8))) → (extend-- (lsizenn1 (lanetype-Jnn Jnn-I8)) (lsizenn2 (lanetype-Jnn Jnn-I64)) sx-2 c-2-126)) c-2-lst) in let c-lst = (f- (lsizenn2 (lanetype-Jnn Jnn-I64)) c'-1-lst c'-2-lst) in (inv-lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim M-2)) c-lst)
ivextbinop-- (X lanetype-I16 (mk-dim M-1)) (X lanetype-I64 (mk-dim M-2)) f- sx-1 sx-2 i k v-1 v-2 = let c-1-lst = (slice (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim M-1)) v-1) (proj-uN-0 8 i) (proj-uN-0 8 k)) in let c-2-lst = (slice (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim M-1)) v-2) (proj-uN-0 8 i) (proj-uN-0 8 k)) in let c'-1-lst = (map (λ (c-1-196 : (uN-fam0 (16))) → (extend-- (lsizenn1 (lanetype-Jnn Jnn-I16)) (lsizenn2 (lanetype-Jnn Jnn-I64)) sx-1 c-1-196)) c-1-lst) in let c'-2-lst = (map (λ (c-2-128 : (uN-fam0 (16))) → (extend-- (lsizenn1 (lanetype-Jnn Jnn-I16)) (lsizenn2 (lanetype-Jnn Jnn-I64)) sx-2 c-2-128)) c-2-lst) in let c-lst = (f- (lsizenn2 (lanetype-Jnn Jnn-I64)) c'-1-lst c'-2-lst) in (inv-lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim M-2)) c-lst)
ivextbinop-- (X lanetype-I32 (mk-dim M-1)) (X lanetype-I8 (mk-dim M-2)) f- sx-1 sx-2 i k v-1 v-2 = let c-1-lst = (slice (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim M-1)) v-1) (proj-uN-0 8 i) (proj-uN-0 8 k)) in let c-2-lst = (slice (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim M-1)) v-2) (proj-uN-0 8 i) (proj-uN-0 8 k)) in let c'-1-lst = (map (λ (c-1-198 : (uN-fam0 (32))) → (extend-- (lsizenn1 (lanetype-Jnn Jnn-I32)) (lsizenn2 (lanetype-Jnn Jnn-I8)) sx-1 c-1-198)) c-1-lst) in let c'-2-lst = (map (λ (c-2-130 : (uN-fam0 (32))) → (extend-- (lsizenn1 (lanetype-Jnn Jnn-I32)) (lsizenn2 (lanetype-Jnn Jnn-I8)) sx-2 c-2-130)) c-2-lst) in let c-lst = (f- (lsizenn2 (lanetype-Jnn Jnn-I8)) c'-1-lst c'-2-lst) in (inv-lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim M-2)) c-lst)
ivextbinop-- (X lanetype-I64 (mk-dim M-1)) (X lanetype-I8 (mk-dim M-2)) f- sx-1 sx-2 i k v-1 v-2 = let c-1-lst = (slice (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim M-1)) v-1) (proj-uN-0 8 i) (proj-uN-0 8 k)) in let c-2-lst = (slice (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim M-1)) v-2) (proj-uN-0 8 i) (proj-uN-0 8 k)) in let c'-1-lst = (map (λ (c-1-200 : (uN-fam0 (64))) → (extend-- (lsizenn1 (lanetype-Jnn Jnn-I64)) (lsizenn2 (lanetype-Jnn Jnn-I8)) sx-1 c-1-200)) c-1-lst) in let c'-2-lst = (map (λ (c-2-132 : (uN-fam0 (64))) → (extend-- (lsizenn1 (lanetype-Jnn Jnn-I64)) (lsizenn2 (lanetype-Jnn Jnn-I8)) sx-2 c-2-132)) c-2-lst) in let c-lst = (f- (lsizenn2 (lanetype-Jnn Jnn-I8)) c'-1-lst c'-2-lst) in (inv-lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim M-2)) c-lst)
ivextbinop-- (X lanetype-I8 (mk-dim M-1)) (X lanetype-I8 (mk-dim M-2)) f- sx-1 sx-2 i k v-1 v-2 = let c-1-lst = (slice (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim M-1)) v-1) (proj-uN-0 8 i) (proj-uN-0 8 k)) in let c-2-lst = (slice (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim M-1)) v-2) (proj-uN-0 8 i) (proj-uN-0 8 k)) in let c'-1-lst = (map (λ (c-1-202 : (uN-fam0 (8))) → (extend-- (lsizenn1 (lanetype-Jnn Jnn-I8)) (lsizenn2 (lanetype-Jnn Jnn-I8)) sx-1 c-1-202)) c-1-lst) in let c'-2-lst = (map (λ (c-2-134 : (uN-fam0 (8))) → (extend-- (lsizenn1 (lanetype-Jnn Jnn-I8)) (lsizenn2 (lanetype-Jnn Jnn-I8)) sx-2 c-2-134)) c-2-lst) in let c-lst = (f- (lsizenn2 (lanetype-Jnn Jnn-I8)) c'-1-lst c'-2-lst) in (inv-lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim M-2)) c-lst)
ivextbinop-- (X lanetype-I16 (mk-dim M-1)) (X lanetype-I8 (mk-dim M-2)) f- sx-1 sx-2 i k v-1 v-2 = let c-1-lst = (slice (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim M-1)) v-1) (proj-uN-0 8 i) (proj-uN-0 8 k)) in let c-2-lst = (slice (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim M-1)) v-2) (proj-uN-0 8 i) (proj-uN-0 8 k)) in let c'-1-lst = (map (λ (c-1-204 : (uN-fam0 (16))) → (extend-- (lsizenn1 (lanetype-Jnn Jnn-I16)) (lsizenn2 (lanetype-Jnn Jnn-I8)) sx-1 c-1-204)) c-1-lst) in let c'-2-lst = (map (λ (c-2-136 : (uN-fam0 (16))) → (extend-- (lsizenn1 (lanetype-Jnn Jnn-I16)) (lsizenn2 (lanetype-Jnn Jnn-I8)) sx-2 c-2-136)) c-2-lst) in let c-lst = (f- (lsizenn2 (lanetype-Jnn Jnn-I8)) c'-1-lst c'-2-lst) in (inv-lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim M-2)) c-lst)
ivextbinop-- (X lanetype-I32 (mk-dim M-1)) (X lanetype-I16 (mk-dim M-2)) f- sx-1 sx-2 i k v-1 v-2 = let c-1-lst = (slice (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim M-1)) v-1) (proj-uN-0 8 i) (proj-uN-0 8 k)) in let c-2-lst = (slice (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim M-1)) v-2) (proj-uN-0 8 i) (proj-uN-0 8 k)) in let c'-1-lst = (map (λ (c-1-206 : (uN-fam0 (32))) → (extend-- (lsizenn1 (lanetype-Jnn Jnn-I32)) (lsizenn2 (lanetype-Jnn Jnn-I16)) sx-1 c-1-206)) c-1-lst) in let c'-2-lst = (map (λ (c-2-138 : (uN-fam0 (32))) → (extend-- (lsizenn1 (lanetype-Jnn Jnn-I32)) (lsizenn2 (lanetype-Jnn Jnn-I16)) sx-2 c-2-138)) c-2-lst) in let c-lst = (f- (lsizenn2 (lanetype-Jnn Jnn-I16)) c'-1-lst c'-2-lst) in (inv-lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim M-2)) c-lst)
ivextbinop-- (X lanetype-I64 (mk-dim M-1)) (X lanetype-I16 (mk-dim M-2)) f- sx-1 sx-2 i k v-1 v-2 = let c-1-lst = (slice (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim M-1)) v-1) (proj-uN-0 8 i) (proj-uN-0 8 k)) in let c-2-lst = (slice (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim M-1)) v-2) (proj-uN-0 8 i) (proj-uN-0 8 k)) in let c'-1-lst = (map (λ (c-1-208 : (uN-fam0 (64))) → (extend-- (lsizenn1 (lanetype-Jnn Jnn-I64)) (lsizenn2 (lanetype-Jnn Jnn-I16)) sx-1 c-1-208)) c-1-lst) in let c'-2-lst = (map (λ (c-2-140 : (uN-fam0 (64))) → (extend-- (lsizenn1 (lanetype-Jnn Jnn-I64)) (lsizenn2 (lanetype-Jnn Jnn-I16)) sx-2 c-2-140)) c-2-lst) in let c-lst = (f- (lsizenn2 (lanetype-Jnn Jnn-I16)) c'-1-lst c'-2-lst) in (inv-lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim M-2)) c-lst)
ivextbinop-- (X lanetype-I8 (mk-dim M-1)) (X lanetype-I16 (mk-dim M-2)) f- sx-1 sx-2 i k v-1 v-2 = let c-1-lst = (slice (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim M-1)) v-1) (proj-uN-0 8 i) (proj-uN-0 8 k)) in let c-2-lst = (slice (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim M-1)) v-2) (proj-uN-0 8 i) (proj-uN-0 8 k)) in let c'-1-lst = (map (λ (c-1-210 : (uN-fam0 (8))) → (extend-- (lsizenn1 (lanetype-Jnn Jnn-I8)) (lsizenn2 (lanetype-Jnn Jnn-I16)) sx-1 c-1-210)) c-1-lst) in let c'-2-lst = (map (λ (c-2-142 : (uN-fam0 (8))) → (extend-- (lsizenn1 (lanetype-Jnn Jnn-I8)) (lsizenn2 (lanetype-Jnn Jnn-I16)) sx-2 c-2-142)) c-2-lst) in let c-lst = (f- (lsizenn2 (lanetype-Jnn Jnn-I16)) c'-1-lst c'-2-lst) in (inv-lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim M-2)) c-lst)
ivextbinop-- (X lanetype-I16 (mk-dim M-1)) (X lanetype-I16 (mk-dim M-2)) f- sx-1 sx-2 i k v-1 v-2 = let c-1-lst = (slice (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim M-1)) v-1) (proj-uN-0 8 i) (proj-uN-0 8 k)) in let c-2-lst = (slice (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim M-1)) v-2) (proj-uN-0 8 i) (proj-uN-0 8 k)) in let c'-1-lst = (map (λ (c-1-212 : (uN-fam0 (16))) → (extend-- (lsizenn1 (lanetype-Jnn Jnn-I16)) (lsizenn2 (lanetype-Jnn Jnn-I16)) sx-1 c-1-212)) c-1-lst) in let c'-2-lst = (map (λ (c-2-144 : (uN-fam0 (16))) → (extend-- (lsizenn1 (lanetype-Jnn Jnn-I16)) (lsizenn2 (lanetype-Jnn Jnn-I16)) sx-2 c-2-144)) c-2-lst) in let c-lst = (f- (lsizenn2 (lanetype-Jnn Jnn-I16)) c'-1-lst c'-2-lst) in (inv-lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim M-2)) c-lst)
ivextbinop-- shape-1 shape-2 f- v-sx sx-0 v-laneidx laneidx-0 v-vec- vec--0 = (Inhabited.default-val (inh-vec--fun V128))

{- Auxiliary Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:360.1-360.40 -}
{-# TERMINATING #-}
ivmul- : (v-N : N) (var-0-lst : (List (uN-fam0 (v-N)))) (var-1-lst : (List (uN-fam0 (v-N)))) → (List (uN-fam0 (v-N)))
ivmul- v-N i-1-lst i-2-lst = (zipWith (λ (i-1 : (uN-fam0 (v-N))) (i-2 : (uN-fam0 (v-N))) → (imul- v-N i-1 i-2)) i-1-lst i-2-lst)

{- Auxiliary Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:200.1-201.35 -}
{-# TERMINATING #-}
fun-vextbinop-- : (ishape-1 : ishape) (ishape-2 : ishape) (v-vextbinop-- : (vextbinop-- ishape-1 ishape-2)) (v-vec- : (uN-fam0 (128))) (vec--0 : (uN-fam0 (128))) → (uN-fam0 (128))
fun-vextbinop-- (mk-ishape (X lanetype-I32 (mk-dim M-1))) (mk-ishape (X lanetype-I32 (mk-dim M-2))) (EXTMUL v-half v-sx) v-1 v-2 = (ivextbinop-- (X (lanetype-Jnn Jnn-I32) (mk-dim M-1)) (X (lanetype-Jnn Jnn-I32) (mk-dim M-2)) ivmul- v-sx v-sx (mk-uN (fun-half v-half 0 M-2)) (mk-uN M-2) v-1 v-2)
fun-vextbinop-- (mk-ishape (X lanetype-I64 (mk-dim M-1))) (mk-ishape (X lanetype-I32 (mk-dim M-2))) (EXTMUL v-half v-sx) v-1 v-2 = (ivextbinop-- (X (lanetype-Jnn Jnn-I64) (mk-dim M-1)) (X (lanetype-Jnn Jnn-I32) (mk-dim M-2)) ivmul- v-sx v-sx (mk-uN (fun-half v-half 0 M-2)) (mk-uN M-2) v-1 v-2)
fun-vextbinop-- (mk-ishape (X lanetype-I8 (mk-dim M-1))) (mk-ishape (X lanetype-I32 (mk-dim M-2))) (EXTMUL v-half v-sx) v-1 v-2 = (ivextbinop-- (X (lanetype-Jnn Jnn-I8) (mk-dim M-1)) (X (lanetype-Jnn Jnn-I32) (mk-dim M-2)) ivmul- v-sx v-sx (mk-uN (fun-half v-half 0 M-2)) (mk-uN M-2) v-1 v-2)
fun-vextbinop-- (mk-ishape (X lanetype-I16 (mk-dim M-1))) (mk-ishape (X lanetype-I32 (mk-dim M-2))) (EXTMUL v-half v-sx) v-1 v-2 = (ivextbinop-- (X (lanetype-Jnn Jnn-I16) (mk-dim M-1)) (X (lanetype-Jnn Jnn-I32) (mk-dim M-2)) ivmul- v-sx v-sx (mk-uN (fun-half v-half 0 M-2)) (mk-uN M-2) v-1 v-2)
fun-vextbinop-- (mk-ishape (X lanetype-I32 (mk-dim M-1))) (mk-ishape (X lanetype-I64 (mk-dim M-2))) (EXTMUL v-half v-sx) v-1 v-2 = (ivextbinop-- (X (lanetype-Jnn Jnn-I32) (mk-dim M-1)) (X (lanetype-Jnn Jnn-I64) (mk-dim M-2)) ivmul- v-sx v-sx (mk-uN (fun-half v-half 0 M-2)) (mk-uN M-2) v-1 v-2)
fun-vextbinop-- (mk-ishape (X lanetype-I64 (mk-dim M-1))) (mk-ishape (X lanetype-I64 (mk-dim M-2))) (EXTMUL v-half v-sx) v-1 v-2 = (ivextbinop-- (X (lanetype-Jnn Jnn-I64) (mk-dim M-1)) (X (lanetype-Jnn Jnn-I64) (mk-dim M-2)) ivmul- v-sx v-sx (mk-uN (fun-half v-half 0 M-2)) (mk-uN M-2) v-1 v-2)
fun-vextbinop-- (mk-ishape (X lanetype-I8 (mk-dim M-1))) (mk-ishape (X lanetype-I64 (mk-dim M-2))) (EXTMUL v-half v-sx) v-1 v-2 = (ivextbinop-- (X (lanetype-Jnn Jnn-I8) (mk-dim M-1)) (X (lanetype-Jnn Jnn-I64) (mk-dim M-2)) ivmul- v-sx v-sx (mk-uN (fun-half v-half 0 M-2)) (mk-uN M-2) v-1 v-2)
fun-vextbinop-- (mk-ishape (X lanetype-I16 (mk-dim M-1))) (mk-ishape (X lanetype-I64 (mk-dim M-2))) (EXTMUL v-half v-sx) v-1 v-2 = (ivextbinop-- (X (lanetype-Jnn Jnn-I16) (mk-dim M-1)) (X (lanetype-Jnn Jnn-I64) (mk-dim M-2)) ivmul- v-sx v-sx (mk-uN (fun-half v-half 0 M-2)) (mk-uN M-2) v-1 v-2)
fun-vextbinop-- (mk-ishape (X lanetype-I32 (mk-dim M-1))) (mk-ishape (X lanetype-I8 (mk-dim M-2))) (EXTMUL v-half v-sx) v-1 v-2 = (ivextbinop-- (X (lanetype-Jnn Jnn-I32) (mk-dim M-1)) (X (lanetype-Jnn Jnn-I8) (mk-dim M-2)) ivmul- v-sx v-sx (mk-uN (fun-half v-half 0 M-2)) (mk-uN M-2) v-1 v-2)
fun-vextbinop-- (mk-ishape (X lanetype-I64 (mk-dim M-1))) (mk-ishape (X lanetype-I8 (mk-dim M-2))) (EXTMUL v-half v-sx) v-1 v-2 = (ivextbinop-- (X (lanetype-Jnn Jnn-I64) (mk-dim M-1)) (X (lanetype-Jnn Jnn-I8) (mk-dim M-2)) ivmul- v-sx v-sx (mk-uN (fun-half v-half 0 M-2)) (mk-uN M-2) v-1 v-2)
fun-vextbinop-- (mk-ishape (X lanetype-I8 (mk-dim M-1))) (mk-ishape (X lanetype-I8 (mk-dim M-2))) (EXTMUL v-half v-sx) v-1 v-2 = (ivextbinop-- (X (lanetype-Jnn Jnn-I8) (mk-dim M-1)) (X (lanetype-Jnn Jnn-I8) (mk-dim M-2)) ivmul- v-sx v-sx (mk-uN (fun-half v-half 0 M-2)) (mk-uN M-2) v-1 v-2)
fun-vextbinop-- (mk-ishape (X lanetype-I16 (mk-dim M-1))) (mk-ishape (X lanetype-I8 (mk-dim M-2))) (EXTMUL v-half v-sx) v-1 v-2 = (ivextbinop-- (X (lanetype-Jnn Jnn-I16) (mk-dim M-1)) (X (lanetype-Jnn Jnn-I8) (mk-dim M-2)) ivmul- v-sx v-sx (mk-uN (fun-half v-half 0 M-2)) (mk-uN M-2) v-1 v-2)
fun-vextbinop-- (mk-ishape (X lanetype-I32 (mk-dim M-1))) (mk-ishape (X lanetype-I16 (mk-dim M-2))) (EXTMUL v-half v-sx) v-1 v-2 = (ivextbinop-- (X (lanetype-Jnn Jnn-I32) (mk-dim M-1)) (X (lanetype-Jnn Jnn-I16) (mk-dim M-2)) ivmul- v-sx v-sx (mk-uN (fun-half v-half 0 M-2)) (mk-uN M-2) v-1 v-2)
fun-vextbinop-- (mk-ishape (X lanetype-I64 (mk-dim M-1))) (mk-ishape (X lanetype-I16 (mk-dim M-2))) (EXTMUL v-half v-sx) v-1 v-2 = (ivextbinop-- (X (lanetype-Jnn Jnn-I64) (mk-dim M-1)) (X (lanetype-Jnn Jnn-I16) (mk-dim M-2)) ivmul- v-sx v-sx (mk-uN (fun-half v-half 0 M-2)) (mk-uN M-2) v-1 v-2)
fun-vextbinop-- (mk-ishape (X lanetype-I8 (mk-dim M-1))) (mk-ishape (X lanetype-I16 (mk-dim M-2))) (EXTMUL v-half v-sx) v-1 v-2 = (ivextbinop-- (X (lanetype-Jnn Jnn-I8) (mk-dim M-1)) (X (lanetype-Jnn Jnn-I16) (mk-dim M-2)) ivmul- v-sx v-sx (mk-uN (fun-half v-half 0 M-2)) (mk-uN M-2) v-1 v-2)
fun-vextbinop-- (mk-ishape (X lanetype-I16 (mk-dim M-1))) (mk-ishape (X lanetype-I16 (mk-dim M-2))) (EXTMUL v-half v-sx) v-1 v-2 = (ivextbinop-- (X (lanetype-Jnn Jnn-I16) (mk-dim M-1)) (X (lanetype-Jnn Jnn-I16) (mk-dim M-2)) ivmul- v-sx v-sx (mk-uN (fun-half v-half 0 M-2)) (mk-uN M-2) v-1 v-2)
fun-vextbinop-- (mk-ishape (X lanetype-I32 (mk-dim M-1))) (mk-ishape (X lanetype-I32 (mk-dim M-2))) DOTS v-1 v-2 = (ivextbinop-- (X (lanetype-Jnn Jnn-I32) (mk-dim M-1)) (X (lanetype-Jnn Jnn-I32) (mk-dim M-2)) ivdot- S S (mk-uN 0) (mk-uN M-1) v-1 v-2)
fun-vextbinop-- (mk-ishape (X lanetype-I64 (mk-dim M-1))) (mk-ishape (X lanetype-I32 (mk-dim M-2))) DOTS v-1 v-2 = (ivextbinop-- (X (lanetype-Jnn Jnn-I64) (mk-dim M-1)) (X (lanetype-Jnn Jnn-I32) (mk-dim M-2)) ivdot- S S (mk-uN 0) (mk-uN M-1) v-1 v-2)
fun-vextbinop-- (mk-ishape (X lanetype-I8 (mk-dim M-1))) (mk-ishape (X lanetype-I32 (mk-dim M-2))) DOTS v-1 v-2 = (ivextbinop-- (X (lanetype-Jnn Jnn-I8) (mk-dim M-1)) (X (lanetype-Jnn Jnn-I32) (mk-dim M-2)) ivdot- S S (mk-uN 0) (mk-uN M-1) v-1 v-2)
fun-vextbinop-- (mk-ishape (X lanetype-I16 (mk-dim M-1))) (mk-ishape (X lanetype-I32 (mk-dim M-2))) DOTS v-1 v-2 = (ivextbinop-- (X (lanetype-Jnn Jnn-I16) (mk-dim M-1)) (X (lanetype-Jnn Jnn-I32) (mk-dim M-2)) ivdot- S S (mk-uN 0) (mk-uN M-1) v-1 v-2)
fun-vextbinop-- (mk-ishape (X lanetype-I32 (mk-dim M-1))) (mk-ishape (X lanetype-I64 (mk-dim M-2))) DOTS v-1 v-2 = (ivextbinop-- (X (lanetype-Jnn Jnn-I32) (mk-dim M-1)) (X (lanetype-Jnn Jnn-I64) (mk-dim M-2)) ivdot- S S (mk-uN 0) (mk-uN M-1) v-1 v-2)
fun-vextbinop-- (mk-ishape (X lanetype-I64 (mk-dim M-1))) (mk-ishape (X lanetype-I64 (mk-dim M-2))) DOTS v-1 v-2 = (ivextbinop-- (X (lanetype-Jnn Jnn-I64) (mk-dim M-1)) (X (lanetype-Jnn Jnn-I64) (mk-dim M-2)) ivdot- S S (mk-uN 0) (mk-uN M-1) v-1 v-2)
fun-vextbinop-- (mk-ishape (X lanetype-I8 (mk-dim M-1))) (mk-ishape (X lanetype-I64 (mk-dim M-2))) DOTS v-1 v-2 = (ivextbinop-- (X (lanetype-Jnn Jnn-I8) (mk-dim M-1)) (X (lanetype-Jnn Jnn-I64) (mk-dim M-2)) ivdot- S S (mk-uN 0) (mk-uN M-1) v-1 v-2)
fun-vextbinop-- (mk-ishape (X lanetype-I16 (mk-dim M-1))) (mk-ishape (X lanetype-I64 (mk-dim M-2))) DOTS v-1 v-2 = (ivextbinop-- (X (lanetype-Jnn Jnn-I16) (mk-dim M-1)) (X (lanetype-Jnn Jnn-I64) (mk-dim M-2)) ivdot- S S (mk-uN 0) (mk-uN M-1) v-1 v-2)
fun-vextbinop-- (mk-ishape (X lanetype-I32 (mk-dim M-1))) (mk-ishape (X lanetype-I8 (mk-dim M-2))) DOTS v-1 v-2 = (ivextbinop-- (X (lanetype-Jnn Jnn-I32) (mk-dim M-1)) (X (lanetype-Jnn Jnn-I8) (mk-dim M-2)) ivdot- S S (mk-uN 0) (mk-uN M-1) v-1 v-2)
fun-vextbinop-- (mk-ishape (X lanetype-I64 (mk-dim M-1))) (mk-ishape (X lanetype-I8 (mk-dim M-2))) DOTS v-1 v-2 = (ivextbinop-- (X (lanetype-Jnn Jnn-I64) (mk-dim M-1)) (X (lanetype-Jnn Jnn-I8) (mk-dim M-2)) ivdot- S S (mk-uN 0) (mk-uN M-1) v-1 v-2)
fun-vextbinop-- (mk-ishape (X lanetype-I8 (mk-dim M-1))) (mk-ishape (X lanetype-I8 (mk-dim M-2))) DOTS v-1 v-2 = (ivextbinop-- (X (lanetype-Jnn Jnn-I8) (mk-dim M-1)) (X (lanetype-Jnn Jnn-I8) (mk-dim M-2)) ivdot- S S (mk-uN 0) (mk-uN M-1) v-1 v-2)
fun-vextbinop-- (mk-ishape (X lanetype-I16 (mk-dim M-1))) (mk-ishape (X lanetype-I8 (mk-dim M-2))) DOTS v-1 v-2 = (ivextbinop-- (X (lanetype-Jnn Jnn-I16) (mk-dim M-1)) (X (lanetype-Jnn Jnn-I8) (mk-dim M-2)) ivdot- S S (mk-uN 0) (mk-uN M-1) v-1 v-2)
fun-vextbinop-- (mk-ishape (X lanetype-I32 (mk-dim M-1))) (mk-ishape (X lanetype-I16 (mk-dim M-2))) DOTS v-1 v-2 = (ivextbinop-- (X (lanetype-Jnn Jnn-I32) (mk-dim M-1)) (X (lanetype-Jnn Jnn-I16) (mk-dim M-2)) ivdot- S S (mk-uN 0) (mk-uN M-1) v-1 v-2)
fun-vextbinop-- (mk-ishape (X lanetype-I64 (mk-dim M-1))) (mk-ishape (X lanetype-I16 (mk-dim M-2))) DOTS v-1 v-2 = (ivextbinop-- (X (lanetype-Jnn Jnn-I64) (mk-dim M-1)) (X (lanetype-Jnn Jnn-I16) (mk-dim M-2)) ivdot- S S (mk-uN 0) (mk-uN M-1) v-1 v-2)
fun-vextbinop-- (mk-ishape (X lanetype-I8 (mk-dim M-1))) (mk-ishape (X lanetype-I16 (mk-dim M-2))) DOTS v-1 v-2 = (ivextbinop-- (X (lanetype-Jnn Jnn-I8) (mk-dim M-1)) (X (lanetype-Jnn Jnn-I16) (mk-dim M-2)) ivdot- S S (mk-uN 0) (mk-uN M-1) v-1 v-2)
fun-vextbinop-- (mk-ishape (X lanetype-I16 (mk-dim M-1))) (mk-ishape (X lanetype-I16 (mk-dim M-2))) DOTS v-1 v-2 = (ivextbinop-- (X (lanetype-Jnn Jnn-I16) (mk-dim M-1)) (X (lanetype-Jnn Jnn-I16) (mk-dim M-2)) ivdot- S S (mk-uN 0) (mk-uN M-1) v-1 v-2)
fun-vextbinop-- (mk-ishape (X lanetype-I32 (mk-dim M-1))) (mk-ishape (X lanetype-I32 (mk-dim M-2))) RELAXED-DOTS v-1 v-2 = (ivextbinop-- (X (lanetype-Jnn Jnn-I32) (mk-dim M-1)) (X (lanetype-Jnn Jnn-I32) (mk-dim M-2)) ivdot-sat- S (fun-relaxed2 (R-idot ) sx S U) (mk-uN 0) (mk-uN M-1) v-1 v-2)
fun-vextbinop-- (mk-ishape (X lanetype-I64 (mk-dim M-1))) (mk-ishape (X lanetype-I32 (mk-dim M-2))) RELAXED-DOTS v-1 v-2 = (ivextbinop-- (X (lanetype-Jnn Jnn-I64) (mk-dim M-1)) (X (lanetype-Jnn Jnn-I32) (mk-dim M-2)) ivdot-sat- S (fun-relaxed2 (R-idot ) sx S U) (mk-uN 0) (mk-uN M-1) v-1 v-2)
fun-vextbinop-- (mk-ishape (X lanetype-I8 (mk-dim M-1))) (mk-ishape (X lanetype-I32 (mk-dim M-2))) RELAXED-DOTS v-1 v-2 = (ivextbinop-- (X (lanetype-Jnn Jnn-I8) (mk-dim M-1)) (X (lanetype-Jnn Jnn-I32) (mk-dim M-2)) ivdot-sat- S (fun-relaxed2 (R-idot ) sx S U) (mk-uN 0) (mk-uN M-1) v-1 v-2)
fun-vextbinop-- (mk-ishape (X lanetype-I16 (mk-dim M-1))) (mk-ishape (X lanetype-I32 (mk-dim M-2))) RELAXED-DOTS v-1 v-2 = (ivextbinop-- (X (lanetype-Jnn Jnn-I16) (mk-dim M-1)) (X (lanetype-Jnn Jnn-I32) (mk-dim M-2)) ivdot-sat- S (fun-relaxed2 (R-idot ) sx S U) (mk-uN 0) (mk-uN M-1) v-1 v-2)
fun-vextbinop-- (mk-ishape (X lanetype-I32 (mk-dim M-1))) (mk-ishape (X lanetype-I64 (mk-dim M-2))) RELAXED-DOTS v-1 v-2 = (ivextbinop-- (X (lanetype-Jnn Jnn-I32) (mk-dim M-1)) (X (lanetype-Jnn Jnn-I64) (mk-dim M-2)) ivdot-sat- S (fun-relaxed2 (R-idot ) sx S U) (mk-uN 0) (mk-uN M-1) v-1 v-2)
fun-vextbinop-- (mk-ishape (X lanetype-I64 (mk-dim M-1))) (mk-ishape (X lanetype-I64 (mk-dim M-2))) RELAXED-DOTS v-1 v-2 = (ivextbinop-- (X (lanetype-Jnn Jnn-I64) (mk-dim M-1)) (X (lanetype-Jnn Jnn-I64) (mk-dim M-2)) ivdot-sat- S (fun-relaxed2 (R-idot ) sx S U) (mk-uN 0) (mk-uN M-1) v-1 v-2)
fun-vextbinop-- (mk-ishape (X lanetype-I8 (mk-dim M-1))) (mk-ishape (X lanetype-I64 (mk-dim M-2))) RELAXED-DOTS v-1 v-2 = (ivextbinop-- (X (lanetype-Jnn Jnn-I8) (mk-dim M-1)) (X (lanetype-Jnn Jnn-I64) (mk-dim M-2)) ivdot-sat- S (fun-relaxed2 (R-idot ) sx S U) (mk-uN 0) (mk-uN M-1) v-1 v-2)
fun-vextbinop-- (mk-ishape (X lanetype-I16 (mk-dim M-1))) (mk-ishape (X lanetype-I64 (mk-dim M-2))) RELAXED-DOTS v-1 v-2 = (ivextbinop-- (X (lanetype-Jnn Jnn-I16) (mk-dim M-1)) (X (lanetype-Jnn Jnn-I64) (mk-dim M-2)) ivdot-sat- S (fun-relaxed2 (R-idot ) sx S U) (mk-uN 0) (mk-uN M-1) v-1 v-2)
fun-vextbinop-- (mk-ishape (X lanetype-I32 (mk-dim M-1))) (mk-ishape (X lanetype-I8 (mk-dim M-2))) RELAXED-DOTS v-1 v-2 = (ivextbinop-- (X (lanetype-Jnn Jnn-I32) (mk-dim M-1)) (X (lanetype-Jnn Jnn-I8) (mk-dim M-2)) ivdot-sat- S (fun-relaxed2 (R-idot ) sx S U) (mk-uN 0) (mk-uN M-1) v-1 v-2)
fun-vextbinop-- (mk-ishape (X lanetype-I64 (mk-dim M-1))) (mk-ishape (X lanetype-I8 (mk-dim M-2))) RELAXED-DOTS v-1 v-2 = (ivextbinop-- (X (lanetype-Jnn Jnn-I64) (mk-dim M-1)) (X (lanetype-Jnn Jnn-I8) (mk-dim M-2)) ivdot-sat- S (fun-relaxed2 (R-idot ) sx S U) (mk-uN 0) (mk-uN M-1) v-1 v-2)
fun-vextbinop-- (mk-ishape (X lanetype-I8 (mk-dim M-1))) (mk-ishape (X lanetype-I8 (mk-dim M-2))) RELAXED-DOTS v-1 v-2 = (ivextbinop-- (X (lanetype-Jnn Jnn-I8) (mk-dim M-1)) (X (lanetype-Jnn Jnn-I8) (mk-dim M-2)) ivdot-sat- S (fun-relaxed2 (R-idot ) sx S U) (mk-uN 0) (mk-uN M-1) v-1 v-2)
fun-vextbinop-- (mk-ishape (X lanetype-I16 (mk-dim M-1))) (mk-ishape (X lanetype-I8 (mk-dim M-2))) RELAXED-DOTS v-1 v-2 = (ivextbinop-- (X (lanetype-Jnn Jnn-I16) (mk-dim M-1)) (X (lanetype-Jnn Jnn-I8) (mk-dim M-2)) ivdot-sat- S (fun-relaxed2 (R-idot ) sx S U) (mk-uN 0) (mk-uN M-1) v-1 v-2)
fun-vextbinop-- (mk-ishape (X lanetype-I32 (mk-dim M-1))) (mk-ishape (X lanetype-I16 (mk-dim M-2))) RELAXED-DOTS v-1 v-2 = (ivextbinop-- (X (lanetype-Jnn Jnn-I32) (mk-dim M-1)) (X (lanetype-Jnn Jnn-I16) (mk-dim M-2)) ivdot-sat- S (fun-relaxed2 (R-idot ) sx S U) (mk-uN 0) (mk-uN M-1) v-1 v-2)
fun-vextbinop-- (mk-ishape (X lanetype-I64 (mk-dim M-1))) (mk-ishape (X lanetype-I16 (mk-dim M-2))) RELAXED-DOTS v-1 v-2 = (ivextbinop-- (X (lanetype-Jnn Jnn-I64) (mk-dim M-1)) (X (lanetype-Jnn Jnn-I16) (mk-dim M-2)) ivdot-sat- S (fun-relaxed2 (R-idot ) sx S U) (mk-uN 0) (mk-uN M-1) v-1 v-2)
fun-vextbinop-- (mk-ishape (X lanetype-I8 (mk-dim M-1))) (mk-ishape (X lanetype-I16 (mk-dim M-2))) RELAXED-DOTS v-1 v-2 = (ivextbinop-- (X (lanetype-Jnn Jnn-I8) (mk-dim M-1)) (X (lanetype-Jnn Jnn-I16) (mk-dim M-2)) ivdot-sat- S (fun-relaxed2 (R-idot ) sx S U) (mk-uN 0) (mk-uN M-1) v-1 v-2)
fun-vextbinop-- (mk-ishape (X lanetype-I16 (mk-dim M-1))) (mk-ishape (X lanetype-I16 (mk-dim M-2))) RELAXED-DOTS v-1 v-2 = (ivextbinop-- (X (lanetype-Jnn Jnn-I16) (mk-dim M-1)) (X (lanetype-Jnn Jnn-I16) (mk-dim M-2)) ivdot-sat- S (fun-relaxed2 (R-idot ) sx S U) (mk-uN 0) (mk-uN M-1) v-1 v-2)
fun-vextbinop-- ishape-1 ishape-2 v-vextbinop-- v-vec- vec--0 = (Inhabited.default-val (inh-vec--fun V128))

{- Auxiliary Definition at: ../specification/wasm-3.0/3.2-numerics.vector.spectec:202.1-203.38 -}
postulate fun-vextternop-- : ∀ (ishape-1 : ishape) (ishape-2 : ishape) (v-vextternop-- : (vextternop-- ishape-1 ishape-2)) (v-vec- : (uN-fam0 (128))) (vec--0 : (uN-fam0 (128))) (vec--1 : (uN-fam0 (128))) → (uN-fam0 (128))

{- Inductive Type Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:29.1-30.63 -}
data num : Set where
  num-CONST : (v-numtype : numtype) → (_ : (num- v-numtype)) → num

{- Auxiliary Definition at:  -}
{-# TERMINATING #-}
val-num : (var-0 : num) → val
val-num (num-CONST x0 x1) = (CONST x0 x1)
val-num var-0 = default-val

{- Inductive Type Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:32.1-33.87 -}
data vec : Set where
  vec-VCONST : (v-vectype : vectype) → (_ : (uN-fam0 ((vsize v-vectype)))) → vec

{- Auxiliary Definition at:  -}
{-# TERMINATING #-}
val-vec : (var-0 : vec) → val
val-vec (vec-VCONST x0 x1) = (VCONST x0 x1)
val-vec var-0 = default-val

{- Inductive Type Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:48.1-49.58 -}
data result : Set where
  -VALS : (val-lst : (List val)) → result
  REF-EXN-ADDRTHROW-REF : (v-exnaddr : exnaddr) → result
  result-TRAP : result

{- Inductive Type Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:57.1-57.72 -}
data hostfunc : Set where
  mk-hostfunc : hostfunc

{- Inductive Type Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:58.1-58.73 -}
data funccode : Set where
  funccode-FUNC : (v-typeidx : typeidx) → (local-lst : (List local)) → (v-expr : expr) → funccode
  mk-funccode : funccode

instance
  inh-funccode : Inhabited funccode
  inh-funccode = record { default-val = (funccode-FUNC (default-val) ([]) (default-val)) }

{- Auxiliary Definition at:  -}
{-# TERMINATING #-}
funccode-func : (var-0 : func) → funccode
funccode-func (func-FUNC x0 x1 x2) = (funccode-FUNC x0 x1 x2)
funccode-func var-0 = default-val

{- Record Creation Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:60.1-61.19 -}
record taginst : Set where
  constructor mk-taginst
  field
    taginst-TYPE : tagtype
open taginst

instance
  append-taginst : HasAppend (taginst)
  append-taginst = record { append = λ arg1 arg2 → record {
    taginst-TYPE = taginst-TYPE arg1 {- FIXME - Non-trivial append -} } }

instance
  inh-taginst : Inhabited taginst
  inh-taginst = record { default-val = record { taginst-TYPE = default-val } }

{- Record Creation Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:63.1-64.33 -}
record globalinst : Set where
  constructor mk-globalinst
  field
    globalinst-TYPE : globaltype
    VALUE : val
open globalinst

instance
  append-globalinst : HasAppend (globalinst)
  append-globalinst = record { append = λ arg1 arg2 → record {
    globalinst-TYPE = globalinst-TYPE arg1 {- FIXME - Non-trivial append -} ;
    VALUE = VALUE arg1 {- FIXME - Non-trivial append -} } }

instance
  inh-globalinst : Inhabited globalinst
  inh-globalinst = record { default-val = record { globalinst-TYPE = default-val ; VALUE = default-val } }

{- Record Creation Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:66.1-67.32 -}
record meminst : Set where
  constructor mk-meminst
  field
    meminst-TYPE : memtype
    BYTES : (List byte)
open meminst

instance
  append-meminst : HasAppend (meminst)
  append-meminst = record { append = λ arg1 arg2 → record {
    meminst-TYPE = meminst-TYPE arg1 {- FIXME - Non-trivial append -} ;
    BYTES = BYTES arg1 ⧺ BYTES arg2 } }

instance
  inh-meminst : Inhabited meminst
  inh-meminst = record { default-val = record { meminst-TYPE = default-val ; BYTES = default-val } }

{- Record Creation Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:69.1-70.32 -}
record tableinst : Set where
  constructor mk-tableinst
  field
    tableinst-TYPE : tabletype
    tableinst-REFS : (List ref)
open tableinst

instance
  append-tableinst : HasAppend (tableinst)
  append-tableinst = record { append = λ arg1 arg2 → record {
    tableinst-TYPE = tableinst-TYPE arg1 {- FIXME - Non-trivial append -} ;
    tableinst-REFS = tableinst-REFS arg1 ⧺ tableinst-REFS arg2 } }

instance
  inh-tableinst : Inhabited tableinst
  inh-tableinst = record { default-val = record { tableinst-TYPE = default-val ; tableinst-REFS = default-val } }

{- Record Creation Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:72.1-73.53 -}
record funcinst : Set where
  constructor mk-funcinst
  field
    funcinst-TYPE : deftype
    funcinst-MODULE : moduleinst
    CODE : funccode
open funcinst

instance
  append-funcinst : HasAppend (funcinst)
  append-funcinst = record { append = λ arg1 arg2 → record {
    funcinst-TYPE = funcinst-TYPE arg1 {- FIXME - Non-trivial append -} ;
    funcinst-MODULE = funcinst-MODULE arg1 ⧺ funcinst-MODULE arg2 ;
    CODE = CODE arg1 {- FIXME - Non-trivial append -} } }

instance
  inh-funcinst : Inhabited funcinst
  inh-funcinst = record { default-val = record { funcinst-TYPE = default-val ; funcinst-MODULE = default-val ; CODE = default-val } }

{- Record Creation Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:75.1-76.18 -}
record datainst : Set where
  constructor mk-datainst
  field
    datainst-BYTES : (List byte)
open datainst

instance
  append-datainst : HasAppend (datainst)
  append-datainst = record { append = λ arg1 arg2 → record {
    datainst-BYTES = datainst-BYTES arg1 ⧺ datainst-BYTES arg2 } }

instance
  inh-datainst : Inhabited datainst
  inh-datainst = record { default-val = record { datainst-BYTES = default-val } }

{- Record Creation Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:78.1-79.31 -}
record eleminst : Set where
  constructor mk-eleminst
  field
    eleminst-TYPE : elemtype
    eleminst-REFS : (List ref)
open eleminst

instance
  append-eleminst : HasAppend (eleminst)
  append-eleminst = record { append = λ arg1 arg2 → record {
    eleminst-TYPE = eleminst-TYPE arg1 {- FIXME - Non-trivial append -} ;
    eleminst-REFS = eleminst-REFS arg1 ⧺ eleminst-REFS arg2 } }

instance
  inh-eleminst : Inhabited eleminst
  inh-eleminst = record { default-val = record { eleminst-TYPE = default-val ; eleminst-REFS = default-val } }

{- Inductive Type Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:85.1-86.64 -}
data packval : Set where
  PACK : (v-packtype : packtype) → (_ : (uN-fam0 ((psize v-packtype)))) → packval

{- Inductive Type Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:88.1-89.18 -}
data fieldval : Set where
  fieldval-CONST : (v-numtype : numtype) → (_ : (num- v-numtype)) → fieldval
  fieldval-VCONST : (v-vectype : vectype) → (_ : (uN-fam0 ((vsize v-vectype)))) → fieldval
  fieldval-REF-I31-NUM : (v-u31 : u31) → fieldval
  fieldval-REF-NULL-ADDR : fieldval
  fieldval-REF-STRUCT-ADDR : (v-structaddr : structaddr) → fieldval
  fieldval-REF-ARRAY-ADDR : (v-arrayaddr : arrayaddr) → fieldval
  fieldval-REF-FUNC-ADDR : (v-funcaddr : funcaddr) → fieldval
  fieldval-REF-EXN-ADDR : (v-exnaddr : exnaddr) → fieldval
  fieldval-REF-HOST-ADDR : (v-hostaddr : hostaddr) → fieldval
  fieldval-REF-EXTERN : (v-ref : ref) → fieldval
  fieldval-PACK : (v-packtype : packtype) → (_ : (uN-fam0 ((psize v-packtype)))) → fieldval

instance
  inh-fieldval : Inhabited fieldval
  inh-fieldval = record { default-val = (let v-numtype = default-val in fieldval-CONST v-numtype ((Inhabited.default-val (inh-num--fun v-numtype)))) }

{- Auxiliary Definition at:  -}
{-# TERMINATING #-}
fieldval-packval : (var-0 : packval) → fieldval
fieldval-packval (PACK x0 x1) = (fieldval-PACK x0 x1)
fieldval-packval var-0 = default-val

{- Auxiliary Definition at:  -}
{-# TERMINATING #-}
fieldval-ref : (var-0 : ref) → fieldval
fieldval-ref (REF-I31-NUM x0) = (fieldval-REF-I31-NUM x0)
fieldval-ref REF-NULL-ADDR = fieldval-REF-NULL-ADDR
fieldval-ref (REF-STRUCT-ADDR x0) = (fieldval-REF-STRUCT-ADDR x0)
fieldval-ref (REF-ARRAY-ADDR x0) = (fieldval-REF-ARRAY-ADDR x0)
fieldval-ref (REF-FUNC-ADDR x0) = (fieldval-REF-FUNC-ADDR x0)
fieldval-ref (REF-EXN-ADDR x0) = (fieldval-REF-EXN-ADDR x0)
fieldval-ref (REF-HOST-ADDR x0) = (fieldval-REF-HOST-ADDR x0)
fieldval-ref (REF-EXTERN x0) = (fieldval-REF-EXTERN x0)
fieldval-ref var-0 = default-val

{- Auxiliary Definition at:  -}
{-# TERMINATING #-}
fieldval-val : (var-0 : val) → fieldval
fieldval-val (CONST x0 x1) = (fieldval-CONST x0 x1)
fieldval-val (VCONST x0 x1) = (fieldval-VCONST x0 x1)
fieldval-val (val-REF-I31-NUM x0) = (fieldval-REF-I31-NUM x0)
fieldval-val val-REF-NULL-ADDR = fieldval-REF-NULL-ADDR
fieldval-val (val-REF-STRUCT-ADDR x0) = (fieldval-REF-STRUCT-ADDR x0)
fieldval-val (val-REF-ARRAY-ADDR x0) = (fieldval-REF-ARRAY-ADDR x0)
fieldval-val (val-REF-FUNC-ADDR x0) = (fieldval-REF-FUNC-ADDR x0)
fieldval-val (val-REF-EXN-ADDR x0) = (fieldval-REF-EXN-ADDR x0)
fieldval-val (val-REF-HOST-ADDR x0) = (fieldval-REF-HOST-ADDR x0)
fieldval-val (val-REF-EXTERN x0) = (fieldval-REF-EXTERN x0)
fieldval-val var-0 = default-val

{- Record Creation Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:91.1-92.37 -}
record structinst : Set where
  constructor mk-structinst
  field
    structinst-TYPE : deftype
    FIELDS : (List fieldval)
open structinst

instance
  append-structinst : HasAppend (structinst)
  append-structinst = record { append = λ arg1 arg2 → record {
    structinst-TYPE = structinst-TYPE arg1 {- FIXME - Non-trivial append -} ;
    FIELDS = FIELDS arg1 ⧺ FIELDS arg2 } }

instance
  inh-structinst : Inhabited structinst
  inh-structinst = record { default-val = record { structinst-TYPE = default-val ; FIELDS = default-val } }

{- Record Creation Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:94.1-95.37 -}
record arrayinst : Set where
  constructor mk-arrayinst
  field
    arrayinst-TYPE : deftype
    arrayinst-FIELDS : (List fieldval)
open arrayinst

instance
  append-arrayinst : HasAppend (arrayinst)
  append-arrayinst = record { append = λ arg1 arg2 → record {
    arrayinst-TYPE = arrayinst-TYPE arg1 {- FIXME - Non-trivial append -} ;
    arrayinst-FIELDS = arrayinst-FIELDS arg1 ⧺ arrayinst-FIELDS arg2 } }

instance
  inh-arrayinst : Inhabited arrayinst
  inh-arrayinst = record { default-val = record { arrayinst-TYPE = default-val ; arrayinst-FIELDS = default-val } }

{- Record Creation Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:97.1-98.31 -}
record exninst : Set where
  constructor mk-exninst
  field
    exninst-TAG : tagaddr
    exninst-FIELDS : (List val)
open exninst

instance
  append-exninst : HasAppend (exninst)
  append-exninst = record { append = λ arg1 arg2 → record {
    exninst-TAG = exninst-TAG arg1 {- FIXME - Non-trivial append -} ;
    exninst-FIELDS = exninst-FIELDS arg1 ⧺ exninst-FIELDS arg2 } }

instance
  inh-exninst : Inhabited exninst
  inh-exninst = record { default-val = record { exninst-TAG = default-val ; exninst-FIELDS = default-val } }

{- Record Creation Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:115.1-125.20 -}
record store : Set where
  constructor mk-store
  field
    store-TAGS : (List taginst)
    store-GLOBALS : (List globalinst)
    store-MEMS : (List meminst)
    store-TABLES : (List tableinst)
    store-FUNCS : (List funcinst)
    store-DATAS : (List datainst)
    store-ELEMS : (List eleminst)
    STRUCTS : (List structinst)
    ARRAYS : (List arrayinst)
    EXNS : (List exninst)
open store

instance
  append-store : HasAppend (store)
  append-store = record { append = λ arg1 arg2 → record {
    store-TAGS = store-TAGS arg1 ⧺ store-TAGS arg2 ;
    store-GLOBALS = store-GLOBALS arg1 ⧺ store-GLOBALS arg2 ;
    store-MEMS = store-MEMS arg1 ⧺ store-MEMS arg2 ;
    store-TABLES = store-TABLES arg1 ⧺ store-TABLES arg2 ;
    store-FUNCS = store-FUNCS arg1 ⧺ store-FUNCS arg2 ;
    store-DATAS = store-DATAS arg1 ⧺ store-DATAS arg2 ;
    store-ELEMS = store-ELEMS arg1 ⧺ store-ELEMS arg2 ;
    STRUCTS = STRUCTS arg1 ⧺ STRUCTS arg2 ;
    ARRAYS = ARRAYS arg1 ⧺ ARRAYS arg2 ;
    EXNS = EXNS arg1 ⧺ EXNS arg2 } }

instance
  inh-store : Inhabited store
  inh-store = record { default-val = record { store-TAGS = default-val ; store-GLOBALS = default-val ; store-MEMS = default-val ; store-TABLES = default-val ; store-FUNCS = default-val ; store-DATAS = default-val ; store-ELEMS = default-val ; STRUCTS = default-val ; ARRAYS = default-val ; EXNS = default-val } }

{- Inductive Type Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:144.1-144.47 -}
data state : Set where
  mk-state : (v-store : store) → (v-frame : frame) → state

instance
  inh-state : Inhabited state
  inh-state = record { default-val = (mk-state (default-val) (default-val)) }

{- Inductive Type Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:145.1-145.57 -}
data config : Set where
  mk-config : (v-state : state) → (instr-lst : (List instr)) → config

{- Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:172.1-172.31 -}
Ki : ℕ
Ki = 1024

{- Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:178.1-178.114 -}
{-# TERMINATING #-}
packfield- : (v-storagetype : storagetype) (v-val : val) → (Maybe fieldval)
packfield- storagetype-BOT v-val = (just (fieldval-val v-val))
packfield- (storagetype-REF null-opt v-heaptype) v-val = (just (fieldval-val v-val))
packfield- storagetype-V128 v-val = (just (fieldval-val v-val))
packfield- storagetype-F64 v-val = (just (fieldval-val v-val))
packfield- storagetype-F32 v-val = (just (fieldval-val v-val))
packfield- storagetype-I64 v-val = (just (fieldval-val v-val))
packfield- storagetype-I32 v-val = (just (fieldval-val v-val))
packfield- I8 (CONST numtype-I32 i) = (just (fieldval-PACK packtype-I8 (wrap-- 32 (psize packtype-I8) i)))
packfield- I16 (CONST numtype-I32 i) = (just (fieldval-PACK packtype-I16 (wrap-- 32 (psize packtype-I16) i)))
packfield- x0 x1 = nothing

{- Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:179.1-179.126 -}
{-# TERMINATING #-}
unpackfield- : (v-storagetype : storagetype) (var-0-opt : (Maybe sx)) (v-fieldval : fieldval) → (Maybe val)
unpackfield- storagetype-BOT nothing (fieldval-REF-EXTERN v-ref) = (just (val-REF-EXTERN v-ref))
unpackfield- (storagetype-REF null-opt v-heaptype) nothing (fieldval-REF-EXTERN v-ref) = (just (val-REF-EXTERN v-ref))
unpackfield- storagetype-V128 nothing (fieldval-REF-EXTERN v-ref) = (just (val-REF-EXTERN v-ref))
unpackfield- storagetype-F64 nothing (fieldval-REF-EXTERN v-ref) = (just (val-REF-EXTERN v-ref))
unpackfield- storagetype-F32 nothing (fieldval-REF-EXTERN v-ref) = (just (val-REF-EXTERN v-ref))
unpackfield- storagetype-I64 nothing (fieldval-REF-EXTERN v-ref) = (just (val-REF-EXTERN v-ref))
unpackfield- storagetype-I32 nothing (fieldval-REF-EXTERN v-ref) = (just (val-REF-EXTERN v-ref))
unpackfield- storagetype-BOT nothing (fieldval-REF-HOST-ADDR v-hostaddr) = (just (val-REF-HOST-ADDR v-hostaddr))
unpackfield- (storagetype-REF null-opt v-heaptype) nothing (fieldval-REF-HOST-ADDR v-hostaddr) = (just (val-REF-HOST-ADDR v-hostaddr))
unpackfield- storagetype-V128 nothing (fieldval-REF-HOST-ADDR v-hostaddr) = (just (val-REF-HOST-ADDR v-hostaddr))
unpackfield- storagetype-F64 nothing (fieldval-REF-HOST-ADDR v-hostaddr) = (just (val-REF-HOST-ADDR v-hostaddr))
unpackfield- storagetype-F32 nothing (fieldval-REF-HOST-ADDR v-hostaddr) = (just (val-REF-HOST-ADDR v-hostaddr))
unpackfield- storagetype-I64 nothing (fieldval-REF-HOST-ADDR v-hostaddr) = (just (val-REF-HOST-ADDR v-hostaddr))
unpackfield- storagetype-I32 nothing (fieldval-REF-HOST-ADDR v-hostaddr) = (just (val-REF-HOST-ADDR v-hostaddr))
unpackfield- storagetype-BOT nothing (fieldval-REF-EXN-ADDR v-exnaddr) = (just (val-REF-EXN-ADDR v-exnaddr))
unpackfield- (storagetype-REF null-opt v-heaptype) nothing (fieldval-REF-EXN-ADDR v-exnaddr) = (just (val-REF-EXN-ADDR v-exnaddr))
unpackfield- storagetype-V128 nothing (fieldval-REF-EXN-ADDR v-exnaddr) = (just (val-REF-EXN-ADDR v-exnaddr))
unpackfield- storagetype-F64 nothing (fieldval-REF-EXN-ADDR v-exnaddr) = (just (val-REF-EXN-ADDR v-exnaddr))
unpackfield- storagetype-F32 nothing (fieldval-REF-EXN-ADDR v-exnaddr) = (just (val-REF-EXN-ADDR v-exnaddr))
unpackfield- storagetype-I64 nothing (fieldval-REF-EXN-ADDR v-exnaddr) = (just (val-REF-EXN-ADDR v-exnaddr))
unpackfield- storagetype-I32 nothing (fieldval-REF-EXN-ADDR v-exnaddr) = (just (val-REF-EXN-ADDR v-exnaddr))
unpackfield- storagetype-BOT nothing (fieldval-REF-FUNC-ADDR v-funcaddr) = (just (val-REF-FUNC-ADDR v-funcaddr))
unpackfield- (storagetype-REF null-opt v-heaptype) nothing (fieldval-REF-FUNC-ADDR v-funcaddr) = (just (val-REF-FUNC-ADDR v-funcaddr))
unpackfield- storagetype-V128 nothing (fieldval-REF-FUNC-ADDR v-funcaddr) = (just (val-REF-FUNC-ADDR v-funcaddr))
unpackfield- storagetype-F64 nothing (fieldval-REF-FUNC-ADDR v-funcaddr) = (just (val-REF-FUNC-ADDR v-funcaddr))
unpackfield- storagetype-F32 nothing (fieldval-REF-FUNC-ADDR v-funcaddr) = (just (val-REF-FUNC-ADDR v-funcaddr))
unpackfield- storagetype-I64 nothing (fieldval-REF-FUNC-ADDR v-funcaddr) = (just (val-REF-FUNC-ADDR v-funcaddr))
unpackfield- storagetype-I32 nothing (fieldval-REF-FUNC-ADDR v-funcaddr) = (just (val-REF-FUNC-ADDR v-funcaddr))
unpackfield- storagetype-BOT nothing (fieldval-REF-ARRAY-ADDR v-arrayaddr) = (just (val-REF-ARRAY-ADDR v-arrayaddr))
unpackfield- (storagetype-REF null-opt v-heaptype) nothing (fieldval-REF-ARRAY-ADDR v-arrayaddr) = (just (val-REF-ARRAY-ADDR v-arrayaddr))
unpackfield- storagetype-V128 nothing (fieldval-REF-ARRAY-ADDR v-arrayaddr) = (just (val-REF-ARRAY-ADDR v-arrayaddr))
unpackfield- storagetype-F64 nothing (fieldval-REF-ARRAY-ADDR v-arrayaddr) = (just (val-REF-ARRAY-ADDR v-arrayaddr))
unpackfield- storagetype-F32 nothing (fieldval-REF-ARRAY-ADDR v-arrayaddr) = (just (val-REF-ARRAY-ADDR v-arrayaddr))
unpackfield- storagetype-I64 nothing (fieldval-REF-ARRAY-ADDR v-arrayaddr) = (just (val-REF-ARRAY-ADDR v-arrayaddr))
unpackfield- storagetype-I32 nothing (fieldval-REF-ARRAY-ADDR v-arrayaddr) = (just (val-REF-ARRAY-ADDR v-arrayaddr))
unpackfield- storagetype-BOT nothing (fieldval-REF-STRUCT-ADDR v-structaddr) = (just (val-REF-STRUCT-ADDR v-structaddr))
unpackfield- (storagetype-REF null-opt v-heaptype) nothing (fieldval-REF-STRUCT-ADDR v-structaddr) = (just (val-REF-STRUCT-ADDR v-structaddr))
unpackfield- storagetype-V128 nothing (fieldval-REF-STRUCT-ADDR v-structaddr) = (just (val-REF-STRUCT-ADDR v-structaddr))
unpackfield- storagetype-F64 nothing (fieldval-REF-STRUCT-ADDR v-structaddr) = (just (val-REF-STRUCT-ADDR v-structaddr))
unpackfield- storagetype-F32 nothing (fieldval-REF-STRUCT-ADDR v-structaddr) = (just (val-REF-STRUCT-ADDR v-structaddr))
unpackfield- storagetype-I64 nothing (fieldval-REF-STRUCT-ADDR v-structaddr) = (just (val-REF-STRUCT-ADDR v-structaddr))
unpackfield- storagetype-I32 nothing (fieldval-REF-STRUCT-ADDR v-structaddr) = (just (val-REF-STRUCT-ADDR v-structaddr))
unpackfield- storagetype-BOT nothing fieldval-REF-NULL-ADDR = (just val-REF-NULL-ADDR)
unpackfield- (storagetype-REF null-opt v-heaptype) nothing fieldval-REF-NULL-ADDR = (just val-REF-NULL-ADDR)
unpackfield- storagetype-V128 nothing fieldval-REF-NULL-ADDR = (just val-REF-NULL-ADDR)
unpackfield- storagetype-F64 nothing fieldval-REF-NULL-ADDR = (just val-REF-NULL-ADDR)
unpackfield- storagetype-F32 nothing fieldval-REF-NULL-ADDR = (just val-REF-NULL-ADDR)
unpackfield- storagetype-I64 nothing fieldval-REF-NULL-ADDR = (just val-REF-NULL-ADDR)
unpackfield- storagetype-I32 nothing fieldval-REF-NULL-ADDR = (just val-REF-NULL-ADDR)
unpackfield- storagetype-BOT nothing (fieldval-REF-I31-NUM v-u31) = (just (val-REF-I31-NUM v-u31))
unpackfield- (storagetype-REF null-opt v-heaptype) nothing (fieldval-REF-I31-NUM v-u31) = (just (val-REF-I31-NUM v-u31))
unpackfield- storagetype-V128 nothing (fieldval-REF-I31-NUM v-u31) = (just (val-REF-I31-NUM v-u31))
unpackfield- storagetype-F64 nothing (fieldval-REF-I31-NUM v-u31) = (just (val-REF-I31-NUM v-u31))
unpackfield- storagetype-F32 nothing (fieldval-REF-I31-NUM v-u31) = (just (val-REF-I31-NUM v-u31))
unpackfield- storagetype-I64 nothing (fieldval-REF-I31-NUM v-u31) = (just (val-REF-I31-NUM v-u31))
unpackfield- storagetype-I32 nothing (fieldval-REF-I31-NUM v-u31) = (just (val-REF-I31-NUM v-u31))
unpackfield- storagetype-BOT nothing (fieldval-VCONST v-vectype var-1) = (just (VCONST v-vectype var-1))
unpackfield- (storagetype-REF null-opt v-heaptype) nothing (fieldval-VCONST v-vectype var-1) = (just (VCONST v-vectype var-1))
unpackfield- storagetype-V128 nothing (fieldval-VCONST v-vectype var-1) = (just (VCONST v-vectype var-1))
unpackfield- storagetype-F64 nothing (fieldval-VCONST v-vectype var-1) = (just (VCONST v-vectype var-1))
unpackfield- storagetype-F32 nothing (fieldval-VCONST v-vectype var-1) = (just (VCONST v-vectype var-1))
unpackfield- storagetype-I64 nothing (fieldval-VCONST v-vectype var-1) = (just (VCONST v-vectype var-1))
unpackfield- storagetype-I32 nothing (fieldval-VCONST v-vectype var-1) = (just (VCONST v-vectype var-1))
unpackfield- storagetype-BOT nothing (fieldval-CONST v-numtype var-0) = (just (CONST v-numtype var-0))
unpackfield- (storagetype-REF null-opt v-heaptype) nothing (fieldval-CONST v-numtype var-0) = (just (CONST v-numtype var-0))
unpackfield- storagetype-V128 nothing (fieldval-CONST v-numtype var-0) = (just (CONST v-numtype var-0))
unpackfield- storagetype-F64 nothing (fieldval-CONST v-numtype var-0) = (just (CONST v-numtype var-0))
unpackfield- storagetype-F32 nothing (fieldval-CONST v-numtype var-0) = (just (CONST v-numtype var-0))
unpackfield- storagetype-I64 nothing (fieldval-CONST v-numtype var-0) = (just (CONST v-numtype var-0))
unpackfield- storagetype-I32 nothing (fieldval-CONST v-numtype var-0) = (just (CONST v-numtype var-0))
unpackfield- I8 (just v-sx) (fieldval-PACK packtype-I8 i) = (just (CONST numtype-I32 (extend-- (psize packtype-I8) 32 v-sx i)))
unpackfield- I16 (just v-sx) (fieldval-PACK packtype-I16 i) = (just (CONST numtype-I32 (extend-- (psize packtype-I16) 32 v-sx i)))
unpackfield- x0 x1 x2 = nothing

{- Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:190.1-190.86 -}
{-# TERMINATING #-}
tagsxa : (var-0-lst : (List externaddr)) → (List tagaddr)
tagsxa [] = []
tagsxa ((externaddr-TAG a) ∷ xa-lst) = ((a ∷ []) ++ (tagsxa xa-lst))
tagsxa (v-externaddr ∷ xa-lst) = (tagsxa xa-lst)
tagsxa var-0-lst = []

{- Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:191.1-191.89 -}
{-# TERMINATING #-}
globalsxa : (var-0-lst : (List externaddr)) → (List globaladdr)
globalsxa [] = []
globalsxa ((externaddr-GLOBAL a) ∷ xa-lst) = ((a ∷ []) ++ (globalsxa xa-lst))
globalsxa (v-externaddr ∷ xa-lst) = (globalsxa xa-lst)
globalsxa var-0-lst = []

{- Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:192.1-192.86 -}
{-# TERMINATING #-}
memsxa : (var-0-lst : (List externaddr)) → (List memaddr)
memsxa [] = []
memsxa ((externaddr-MEM a) ∷ xa-lst) = ((a ∷ []) ++ (memsxa xa-lst))
memsxa (v-externaddr ∷ xa-lst) = (memsxa xa-lst)
memsxa var-0-lst = []

{- Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:193.1-193.88 -}
{-# TERMINATING #-}
tablesxa : (var-0-lst : (List externaddr)) → (List tableaddr)
tablesxa [] = []
tablesxa ((externaddr-TABLE a) ∷ xa-lst) = ((a ∷ []) ++ (tablesxa xa-lst))
tablesxa (v-externaddr ∷ xa-lst) = (tablesxa xa-lst)
tablesxa var-0-lst = []

{- Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:194.1-194.87 -}
{-# TERMINATING #-}
funcsxa : (var-0-lst : (List externaddr)) → (List funcaddr)
funcsxa [] = []
funcsxa ((externaddr-FUNC a) ∷ xa-lst) = ((a ∷ []) ++ (funcsxa xa-lst))
funcsxa (v-externaddr ∷ xa-lst) = (funcsxa xa-lst)
funcsxa var-0-lst = []

{- Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:219.1-219.74 -}
{-# TERMINATING #-}
fun-store : (v-state : state) → store
fun-store (mk-state s f) = s
fun-store v-state = default-val

{- Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:220.1-220.74 -}
{-# TERMINATING #-}
fun-frame : (v-state : state) → frame
fun-frame (mk-state s f) = f
fun-frame v-state = default-val

{- Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:225.1-225.80 -}
{-# TERMINATING #-}
fun-tagaddr : (v-state : state) → (List tagaddr)
fun-tagaddr (mk-state s f) = (moduleinst-TAGS (MODULE f))
fun-tagaddr v-state = []

{- Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:228.1-228.76 -}
{-# TERMINATING #-}
fun-moduleinst : (v-state : state) → moduleinst
fun-moduleinst (mk-state s f) = (MODULE f)
fun-moduleinst v-state = default-val

{- Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:229.1-229.76 -}
{-# TERMINATING #-}
fun-taginst : (v-state : state) → (List taginst)
fun-taginst (mk-state s f) = (store-TAGS s)
fun-taginst v-state = []

{- Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:230.1-230.76 -}
{-# TERMINATING #-}
fun-globalinst : (v-state : state) → (List globalinst)
fun-globalinst (mk-state s f) = (store-GLOBALS s)
fun-globalinst v-state = []

{- Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:231.1-231.76 -}
{-# TERMINATING #-}
fun-meminst : (v-state : state) → (List meminst)
fun-meminst (mk-state s f) = (store-MEMS s)
fun-meminst v-state = []

{- Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:232.1-232.76 -}
{-# TERMINATING #-}
fun-tableinst : (v-state : state) → (List tableinst)
fun-tableinst (mk-state s f) = (store-TABLES s)
fun-tableinst v-state = []

{- Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:233.1-233.76 -}
{-# TERMINATING #-}
fun-funcinst : (v-state : state) → (List funcinst)
fun-funcinst (mk-state s f) = (store-FUNCS s)
fun-funcinst v-state = []

{- Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:234.1-234.76 -}
{-# TERMINATING #-}
fun-datainst : (v-state : state) → (List datainst)
fun-datainst (mk-state s f) = (store-DATAS s)
fun-datainst v-state = []

{- Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:235.1-235.76 -}
{-# TERMINATING #-}
fun-eleminst : (v-state : state) → (List eleminst)
fun-eleminst (mk-state s f) = (store-ELEMS s)
fun-eleminst v-state = []

{- Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:236.1-236.76 -}
{-# TERMINATING #-}
fun-structinst : (v-state : state) → (List structinst)
fun-structinst (mk-state s f) = (STRUCTS s)
fun-structinst v-state = []

{- Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:237.1-237.76 -}
{-# TERMINATING #-}
fun-arrayinst : (v-state : state) → (List arrayinst)
fun-arrayinst (mk-state s f) = (ARRAYS s)
fun-arrayinst v-state = []

{- Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:238.1-238.76 -}
{-# TERMINATING #-}
fun-exninst : (v-state : state) → (List exninst)
fun-exninst (mk-state s f) = (EXNS s)
fun-exninst v-state = []

{- Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:264.1-264.38 -}
{-# TERMINATING #-}
fof : (v-state : state) → frame
fof z = (fun-frame z)

{- Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:253.1-253.85 -}
{-# TERMINATING #-}
fun-type : (v-state : state) (v-typeidx : typeidx) → deftype
fun-type z x = ((moduleinst-TYPES (MODULE (fof z))) [ (proj-uN-0 32 x) ]!)

{- Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:263.1-263.38 -}
{-# TERMINATING #-}
sof : (v-state : state) → store
sof z = (fun-store z)

{- Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:254.1-254.85 -}
{-# TERMINATING #-}
fun-tag : (v-state : state) (v-tagidx : tagidx) → taginst
fun-tag z x = ((store-TAGS (sof z)) [ ((moduleinst-TAGS (MODULE (fof z))) [ (proj-uN-0 32 x) ]!) ]!)

{- Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:255.1-255.85 -}
{-# TERMINATING #-}
fun-global : (v-state : state) (v-globalidx : globalidx) → globalinst
fun-global z x = ((store-GLOBALS (sof z)) [ ((moduleinst-GLOBALS (MODULE (fof z))) [ (proj-uN-0 32 x) ]!) ]!)

{- Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:256.1-256.85 -}
{-# TERMINATING #-}
fun-mem : (v-state : state) (v-memidx : memidx) → meminst
fun-mem z x = ((store-MEMS (sof z)) [ ((moduleinst-MEMS (MODULE (fof z))) [ (proj-uN-0 32 x) ]!) ]!)

{- Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:257.1-257.85 -}
{-# TERMINATING #-}
fun-table : (v-state : state) (v-tableidx : tableidx) → tableinst
fun-table z x = ((store-TABLES (sof z)) [ ((moduleinst-TABLES (MODULE (fof z))) [ (proj-uN-0 32 x) ]!) ]!)

{- Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:258.1-258.85 -}
{-# TERMINATING #-}
fun-func : (v-state : state) (v-funcidx : funcidx) → funcinst
fun-func z x = ((store-FUNCS (sof z)) [ ((moduleinst-FUNCS (MODULE (fof z))) [ (proj-uN-0 32 x) ]!) ]!)

{- Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:259.1-259.85 -}
{-# TERMINATING #-}
fun-data : (v-state : state) (v-dataidx : dataidx) → datainst
fun-data z x = ((store-DATAS (sof z)) [ ((moduleinst-DATAS (MODULE (fof z))) [ (proj-uN-0 32 x) ]!) ]!)

{- Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:260.1-260.85 -}
{-# TERMINATING #-}
fun-elem : (v-state : state) (v-tableidx : tableidx) → eleminst
fun-elem z x = ((store-ELEMS (sof z)) [ ((moduleinst-ELEMS (MODULE (fof z))) [ (proj-uN-0 32 x) ]!) ]!)

{- Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:261.1-261.85 -}
{-# TERMINATING #-}
fun-local : (v-state : state) (v-localidx : localidx) → (Maybe val)
fun-local z x = ((frame-LOCALS (fof z)) [ (proj-uN-0 32 x) ]!)

{- Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:282.1-282.165 -}
{-# TERMINATING #-}
with-local : (v-state : state) (v-localidx : localidx) (v-val : val) → state
with-local z x v = (mk-state (sof z) (record (fof z) { frame-LOCALS = (modify (frame-LOCALS (fof z)) (proj-uN-0 32 x) (λ (_ : (Maybe val)) → (just v))) }))

{- Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:283.1-283.172 -}
{-# TERMINATING #-}
with-global : (v-state : state) (v-globalidx : globalidx) (v-val : val) → state
with-global z x v = (mk-state (record (sof z) { store-GLOBALS = (modify (store-GLOBALS (sof z)) ((moduleinst-GLOBALS (MODULE (fof z))) [ (proj-uN-0 32 x) ]!) (λ (var-1 : globalinst) → (record var-1 { VALUE = v }))) }) (fof z))

{- Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:284.1-284.174 -}
{-# TERMINATING #-}
with-table : (v-state : state) (v-tableidx : tableidx) (nat : ℕ) (v-ref : ref) → state
with-table z x i r = (mk-state (record (sof z) { store-TABLES = (modify (store-TABLES (sof z)) ((moduleinst-TABLES (MODULE (fof z))) [ (proj-uN-0 32 x) ]!) (λ (var-1 : tableinst) → (record var-1 { tableinst-REFS = (modify (tableinst-REFS var-1) i (λ (_ : ref) → r)) }))) }) (fof z))

{- Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:285.1-285.165 -}
{-# TERMINATING #-}
with-tableinst : (v-state : state) (v-tableidx : tableidx) (v-tableinst : tableinst) → state
with-tableinst z x ti = (mk-state (record (sof z) { store-TABLES = (modify (store-TABLES (sof z)) ((moduleinst-TABLES (MODULE (fof z))) [ (proj-uN-0 32 x) ]!) (λ (_ : tableinst) → ti)) }) (fof z))

{- Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:286.1-286.176 -}
{-# TERMINATING #-}
with-mem : (v-state : state) (v-memidx : memidx) (nat : ℕ) (nat-0 : ℕ) (var-0-lst : (List byte)) → state
with-mem z x i j b-lst = (mk-state (record (sof z) { store-MEMS = (modify (store-MEMS (sof z)) ((moduleinst-MEMS (MODULE (fof z))) [ (proj-uN-0 32 x) ]!) (λ (var-1 : meminst) → (record var-1 { BYTES = (slice-update (BYTES var-1) i j b-lst) }))) }) (fof z))

{- Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:287.1-287.167 -}
{-# TERMINATING #-}
with-meminst : (v-state : state) (v-memidx : memidx) (v-meminst : meminst) → state
with-meminst z x mi = (mk-state (record (sof z) { store-MEMS = (modify (store-MEMS (sof z)) ((moduleinst-MEMS (MODULE (fof z))) [ (proj-uN-0 32 x) ]!) (λ (_ : meminst) → mi)) }) (fof z))

{- Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:288.1-288.169 -}
{-# TERMINATING #-}
with-elem : (v-state : state) (v-elemidx : elemidx) (var-0-lst : (List ref)) → state
with-elem z x r-lst = (mk-state (record (sof z) { store-ELEMS = (modify (store-ELEMS (sof z)) ((moduleinst-ELEMS (MODULE (fof z))) [ (proj-uN-0 32 x) ]!) (λ (var-1 : eleminst) → (record var-1 { eleminst-REFS = r-lst }))) }) (fof z))

{- Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:289.1-289.170 -}
{-# TERMINATING #-}
with-data : (v-state : state) (v-dataidx : dataidx) (var-0-lst : (List byte)) → state
with-data z x b-lst = (mk-state (record (sof z) { store-DATAS = (modify (store-DATAS (sof z)) ((moduleinst-DATAS (MODULE (fof z))) [ (proj-uN-0 32 x) ]!) (λ (var-1 : datainst) → (record var-1 { datainst-BYTES = b-lst }))) }) (fof z))

{- Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:290.1-290.181 -}
{-# TERMINATING #-}
with-struct : (v-state : state) (v-structaddr : structaddr) (nat : ℕ) (v-fieldval : fieldval) → state
with-struct z a i fv = (mk-state (record (sof z) { STRUCTS = (modify (STRUCTS (sof z)) a (λ (var-1 : structinst) → (record var-1 { FIELDS = (modify (FIELDS var-1) i (λ (_ : fieldval) → fv)) }))) }) (fof z))

{- Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:291.1-291.180 -}
{-# TERMINATING #-}
with-array : (v-state : state) (v-arrayaddr : arrayaddr) (nat : ℕ) (v-fieldval : fieldval) → state
with-array z a i fv = (mk-state (record (sof z) { ARRAYS = (modify (ARRAYS (sof z)) a (λ (var-1 : arrayinst) → (record var-1 { arrayinst-FIELDS = (modify (arrayinst-FIELDS var-1) i (λ (_ : fieldval) → fv)) }))) }) (fof z))

{- Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:305.1-305.140 -}
{-# TERMINATING #-}
add-structinst : (v-state : state) (var-0-lst : (List structinst)) → state
add-structinst z si-lst = (mk-state (record (sof z) { STRUCTS = ((STRUCTS (sof z)) ⧺ si-lst) }) (fof z))

{- Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:306.1-306.139 -}
{-# TERMINATING #-}
add-arrayinst : (v-state : state) (var-0-lst : (List arrayinst)) → state
add-arrayinst z ai-lst = (mk-state (record (sof z) { ARRAYS = ((ARRAYS (sof z)) ⧺ ai-lst) }) (fof z))

{- Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:307.1-307.137 -}
{-# TERMINATING #-}
add-exninst : (v-state : state) (var-0-lst : (List exninst)) → state
add-exninst z exn-lst = (mk-state (record (sof z) { EXNS = ((EXNS (sof z)) ⧺ exn-lst) }) (fof z))

{- Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:316.1-316.62 -}
postulate growtable : ∀ (v-tableinst : tableinst) (nat : ℕ) (v-ref : ref) → (Maybe tableinst)

{- Auxiliary Definition at: ../specification/wasm-3.0/4.0-execution.configurations.spectec:317.1-317.62 -}
postulate growmem : ∀ (v-meminst : meminst) (nat : ℕ) → (Maybe meminst)

{- Inductive Relations Definition at: ../specification/wasm-3.0/4.1-execution.values.spectec:23.1-23.60 -}
data Num-ok : store → num → numtype → Set where
  mk-Num-ok : ∀ (s : store) (nt : numtype) (c : (num- nt)) → Num-ok s (num-CONST nt c) nt

{- Inductive Relations Definition at: ../specification/wasm-3.0/4.1-execution.values.spectec:24.1-24.60 -}
data Vec-ok : store → vec → vectype → Set where
  mk-Vec-ok : ∀ (s : store) (vt : vectype) (c : (uN-fam0 ((vsize vt)))) → Vec-ok s (vec-VCONST vt c) vt

{- Inductive Relations Definition at: ../specification/wasm-3.0/4.1-execution.values.spectec:25.1-25.60 -}
data Ref-ok : store → ref → reftype → Set where
  Ref-ok--null : ∀ (s : store) → Ref-ok s REF-NULL-ADDR (reftype-REF (just NULL) heaptype-BOT)
  i31 : ∀ (s : store) (i : u31) → Ref-ok s (REF-I31-NUM i) (reftype-REF nothing heaptype-I31)
  Ref-ok--struct : ∀ (s : store) (a : addr) (dt : deftype) → 
    (a < (length (STRUCTS s))) →
    ((structinst-TYPE ((STRUCTS s) [ a ]!)) ≡ dt) →
    Ref-ok s (REF-STRUCT-ADDR a) (reftype-REF nothing (heaptype-deftype dt))
  Ref-ok--array : ∀ (s : store) (a : addr) (dt : deftype) → 
    (a < (length (ARRAYS s))) →
    ((arrayinst-TYPE ((ARRAYS s) [ a ]!)) ≡ dt) →
    Ref-ok s (REF-ARRAY-ADDR a) (reftype-REF nothing (heaptype-deftype dt))
  Ref-ok--func : ∀ (s : store) (a : addr) (dt : deftype) → 
    (a < (length (store-FUNCS s))) →
    ((funcinst-TYPE ((store-FUNCS s) [ a ]!)) ≡ dt) →
    Ref-ok s (REF-FUNC-ADDR a) (reftype-REF nothing (heaptype-deftype dt))
  exn : ∀ (s : store) (a : addr) (exn : exninst) → 
    (a < (length (EXNS s))) →
    (((EXNS s) [ a ]!) ≡ exn) →
    Ref-ok s (REF-EXN-ADDR a) (reftype-REF nothing heaptype-EXN)
  host : ∀ (s : store) (a : addr) → Ref-ok s (REF-HOST-ADDR a) (reftype-REF nothing heaptype-ANY)
  extern : ∀ (s : store) (v-ref : ref) → 
    (Ref-ok s v-ref (reftype-REF nothing heaptype-ANY)) →
    (v-ref ≢ REF-NULL-ADDR) →
    Ref-ok s (REF-EXTERN v-ref) (reftype-REF nothing heaptype-EXTERN)
  Ref-ok--sub : ∀ (s : store) (v-ref : ref) (rt : reftype) (rt' : reftype) → 
    (Ref-ok s v-ref rt') →
    (Reftype-ok record { context-TYPES = [] ; context-TAGS = [] ; context-GLOBALS = [] ; context-MEMS = [] ; context-TABLES = [] ; context-FUNCS = [] ; context-DATAS = [] ; context-ELEMS = [] ; context-LOCALS = [] ; context-LABELS = [] ; context-RETURN = nothing ; REFS = [] ; RECS = [] } rt) →
    (Reftype-sub record { context-TYPES = [] ; context-TAGS = [] ; context-GLOBALS = [] ; context-MEMS = [] ; context-TABLES = [] ; context-FUNCS = [] ; context-DATAS = [] ; context-ELEMS = [] ; context-LOCALS = [] ; context-LABELS = [] ; context-RETURN = nothing ; REFS = [] ; RECS = [] } rt' rt) →
    Ref-ok s v-ref rt

{- Inductive Relations Definition at: ../specification/wasm-3.0/4.1-execution.values.spectec:26.1-26.60 -}
data Val-ok : store → val → valtype → Set where
  Val-ok--num : ∀ (s : store) (v-num : num) (nt : numtype) → 
    (Num-ok s v-num nt) →
    Val-ok s (val-num v-num) (valtype-numtype nt)
  Val-ok--vec : ∀ (s : store) (v-vec : vec) (vt : vectype) → 
    (Vec-ok s v-vec vt) →
    Val-ok s (val-vec v-vec) (valtype-vectype vt)
  Val-ok--ref : ∀ (s : store) (v-ref : ref) (rt : reftype) → 
    (Ref-ok s v-ref rt) →
    Val-ok s (val-ref v-ref) (valtype-reftype rt)

{- Inductive Relations Definition at: ../specification/wasm-3.0/4.1-execution.values.spectec:87.1-87.49 -}
data Packval-ok : store → packval → packtype → Set where
  mk-Packval-ok : ∀ (s : store) (pt : packtype) (c : (uN-fam0 ((psize pt)))) → Packval-ok s (PACK pt c) pt

{- Inductive Relations Definition at: ../specification/wasm-3.0/4.1-execution.values.spectec:88.1-88.54 -}
data Fieldval-ok : store → fieldval → storagetype → Set where
  Fieldval-ok--val : ∀ (s : store) (v-val : val) (t : valtype) → 
    (Val-ok s v-val t) →
    Fieldval-ok s (fieldval-val v-val) (storagetype-valtype t)
  Fieldval-ok--packval : ∀ (s : store) (v-packval : packval) (pt : packtype) → 
    (Packval-ok s v-packval pt) →
    Fieldval-ok s (fieldval-packval v-packval) (storagetype-packtype pt)

{- Inductive Relations Definition at: ../specification/wasm-3.0/4.1-execution.values.spectec:104.1-104.84 -}
data Externaddr-ok : store → externaddr → externtype → Set where
  Externaddr-ok--tag : ∀ (s : store) (a : addr) (v-taginst : taginst) → 
    (a < (length (store-TAGS s))) →
    (((store-TAGS s) [ a ]!) ≡ v-taginst) →
    Externaddr-ok s (externaddr-TAG a) (externtype-TAG (taginst-TYPE v-taginst))
  Externaddr-ok--global : ∀ (s : store) (a : addr) (v-globalinst : globalinst) → 
    (a < (length (store-GLOBALS s))) →
    (((store-GLOBALS s) [ a ]!) ≡ v-globalinst) →
    Externaddr-ok s (externaddr-GLOBAL a) (externtype-GLOBAL (globalinst-TYPE v-globalinst))
  Externaddr-ok--mem : ∀ (s : store) (a : addr) (v-meminst : meminst) → 
    (a < (length (store-MEMS s))) →
    (((store-MEMS s) [ a ]!) ≡ v-meminst) →
    Externaddr-ok s (externaddr-MEM a) (externtype-MEM (meminst-TYPE v-meminst))
  Externaddr-ok--table : ∀ (s : store) (a : addr) (v-tableinst : tableinst) → 
    (a < (length (store-TABLES s))) →
    (((store-TABLES s) [ a ]!) ≡ v-tableinst) →
    Externaddr-ok s (externaddr-TABLE a) (externtype-TABLE (tableinst-TYPE v-tableinst))
  Externaddr-ok--func : ∀ (s : store) (a : addr) (v-funcinst : funcinst) → 
    (a < (length (store-FUNCS s))) →
    (((store-FUNCS s) [ a ]!) ≡ v-funcinst) →
    Externaddr-ok s (externaddr-FUNC a) (externtype-FUNC (typeuse-deftype (funcinst-TYPE v-funcinst)))
  Externaddr-ok--sub : ∀ (s : store) (v-externaddr : externaddr) (xt : externtype) (xt' : externtype) → 
    (Externaddr-ok s v-externaddr xt') →
    (Externtype-ok record { context-TYPES = [] ; context-TAGS = [] ; context-GLOBALS = [] ; context-MEMS = [] ; context-TABLES = [] ; context-FUNCS = [] ; context-DATAS = [] ; context-ELEMS = [] ; context-LOCALS = [] ; context-LABELS = [] ; context-RETURN = nothing ; REFS = [] ; RECS = [] } xt) →
    (Externtype-sub record { context-TYPES = [] ; context-TAGS = [] ; context-GLOBALS = [] ; context-MEMS = [] ; context-TABLES = [] ; context-FUNCS = [] ; context-DATAS = [] ; context-ELEMS = [] ; context-LOCALS = [] ; context-LABELS = [] ; context-RETURN = nothing ; REFS = [] ; RECS = [] } xt' xt) →
    Externaddr-ok s v-externaddr xt

{- Auxiliary Definition at: ../specification/wasm-3.0/4.2-execution.types.spectec:5.1-5.96 -}
{-# TERMINATING #-}
inst-valtype : (v-moduleinst : moduleinst) (v-valtype : valtype) → valtype
inst-valtype v-moduleinst t = (subst-all-valtype t (map (λ (iter-val-3 : deftype) → (typeuse-deftype iter-val-3)) (moduleinst-TYPES v-moduleinst)))

{- Auxiliary Definition at: ../specification/wasm-3.0/4.2-execution.types.spectec:6.1-6.96 -}
{-# TERMINATING #-}
inst-reftype : (v-moduleinst : moduleinst) (v-reftype : reftype) → reftype
inst-reftype v-moduleinst rt = (subst-all-reftype rt (map (λ (iter-val-4 : deftype) → (typeuse-deftype iter-val-4)) (moduleinst-TYPES v-moduleinst)))

{- Auxiliary Definition at: ../specification/wasm-3.0/4.2-execution.types.spectec:7.1-7.105 -}
{-# TERMINATING #-}
inst-globaltype : (v-moduleinst : moduleinst) (v-globaltype : globaltype) → globaltype
inst-globaltype v-moduleinst gt = (subst-all-globaltype gt (map (λ (iter-val-5 : deftype) → (typeuse-deftype iter-val-5)) (moduleinst-TYPES v-moduleinst)))

{- Auxiliary Definition at: ../specification/wasm-3.0/4.2-execution.types.spectec:8.1-8.96 -}
{-# TERMINATING #-}
inst-memtype : (v-moduleinst : moduleinst) (v-memtype : memtype) → memtype
inst-memtype v-moduleinst mt = (subst-all-memtype mt (map (λ (iter-val-6 : deftype) → (typeuse-deftype iter-val-6)) (moduleinst-TYPES v-moduleinst)))

{- Auxiliary Definition at: ../specification/wasm-3.0/4.2-execution.types.spectec:9.1-9.102 -}
{-# TERMINATING #-}
inst-tabletype : (v-moduleinst : moduleinst) (v-tabletype : tabletype) → tabletype
inst-tabletype v-moduleinst tt' = (subst-all-tabletype tt' (map (λ (iter-val-7 : deftype) → (typeuse-deftype iter-val-7)) (moduleinst-TYPES v-moduleinst)))

{- Inductive Relations Definition at: ../specification/wasm-3.0/4.3-execution.instructions.spectec:653.1-656.22 -}
data Step-pure-before-ref-eq-true : (List instr) → Set where
  ref-eq-null-0 : ∀ (ref-1 : ref) (ref-2 : ref) → 
    ((ref-1 ≡ REF-NULL-ADDR) × (ref-2 ≡ REF-NULL-ADDR)) →
    Step-pure-before-ref-eq-true (as (List instr) ((instr-ref ref-1) ∷ (instr-ref ref-2) ∷ REF-EQ ∷ []))

{- Inductive Relations Definition at: ../specification/wasm-3.0/4.3-execution.instructions.spectec:6.1-6.88 -}
data Step-pure : (List instr) → (List instr) → Set where
  Step-pure--unreachable : Step-pure (as (List instr) (UNREACHABLE ∷ [])) (as (List instr) (TRAP ∷ []))
  Step-pure--nop : Step-pure (as (List instr) (NOP ∷ [])) []
  Step-pure--drop : ∀ (v-val : val) → Step-pure (as (List instr) ((instr-val v-val) ∷ DROP ∷ [])) []
  select-true : ∀ (val-1 : val) (val-2 : val) (c : (uN-fam0 (32))) (t-lst-opt : (Maybe (List valtype))) → 
    ((proj-uN-0 32 c) ≢ 0) →
    Step-pure (as (List instr) ((instr-val val-1) ∷ (instr-val val-2) ∷ (instr-CONST numtype-I32 c) ∷ (SELECT t-lst-opt) ∷ [])) ((instr-val val-1) ∷ [])
  select-false : ∀ (val-1 : val) (val-2 : val) (c : (uN-fam0 (32))) (t-lst-opt : (Maybe (List valtype))) → 
    ((proj-uN-0 32 c) ≡ 0) →
    Step-pure (as (List instr) ((instr-val val-1) ∷ (instr-val val-2) ∷ (instr-CONST numtype-I32 c) ∷ (SELECT t-lst-opt) ∷ [])) ((instr-val val-2) ∷ [])
  if-true : ∀ (c : (uN-fam0 (32))) (bt : blocktype) (instr-1-lst : (List instr)) (instr-2-lst : (List instr)) → 
    ((proj-uN-0 32 c) ≢ 0) →
    Step-pure (as (List instr) ((instr-CONST numtype-I32 c) ∷ (IFELSE bt instr-1-lst instr-2-lst) ∷ [])) (as (List instr) ((BLOCK bt instr-1-lst) ∷ []))
  if-false : ∀ (c : (uN-fam0 (32))) (bt : blocktype) (instr-1-lst : (List instr)) (instr-2-lst : (List instr)) → 
    ((proj-uN-0 32 c) ≡ 0) →
    Step-pure (as (List instr) ((instr-CONST numtype-I32 c) ∷ (IFELSE bt instr-1-lst instr-2-lst) ∷ [])) (as (List instr) ((BLOCK bt instr-2-lst) ∷ []))
  label-vals : ∀ (v-n : n) (instr-lst : (List instr)) (val-lst : (List val)) → Step-pure (as (List instr) ((LABEL- v-n instr-lst (map (λ (v-val : val) → (instr-val v-val)) val-lst)) ∷ [])) (map (λ (v-val : val) → (instr-val v-val)) val-lst)
  br-label-zero : ∀ (v-n : n) (instr'-lst : (List instr)) (val'-lst : (List val)) (val-lst : (List val)) (l : labelidx) (instr-lst : (List instr)) → 
    ((length (val-lst)) ≡ (v-n)) →
    ((proj-uN-0 32 l) ≡ 0) →
    Step-pure (as (List instr) ((LABEL- v-n instr'-lst ((((map (λ (val' : val) → (instr-val val')) val'-lst) ++ (map (λ (v-val : val) → (instr-val v-val)) val-lst)) ++ (as (List instr) ((BR l) ∷ []))) ++ instr-lst)) ∷ [])) ((map (λ (v-val : val) → (instr-val v-val)) val-lst) ++ instr'-lst)
  br-label-succ : ∀ (v-n : n) (instr'-lst : (List instr)) (val-lst : (List val)) (l : labelidx) (instr-lst : (List instr)) → 
    ((proj-uN-0 32 l) > 0) →
    Step-pure (as (List instr) ((LABEL- v-n instr'-lst (((map (λ (v-val : val) → (instr-val v-val)) val-lst) ++ (as (List instr) ((BR l) ∷ []))) ++ instr-lst)) ∷ [])) ((map (λ (v-val : val) → (instr-val v-val)) val-lst) ++ (as (List instr) ((BR (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} (proj-uN-0 32 l)) – (coerce {B = ℕ} 1))))) ∷ [])))
  br-handler : ∀ (v-n : n) (catch-lst : (List catch)) (val-lst : (List val)) (l : labelidx) (instr-lst : (List instr)) → Step-pure (as (List instr) ((HANDLER- v-n catch-lst (((map (λ (v-val : val) → (instr-val v-val)) val-lst) ++ (as (List instr) ((BR l) ∷ []))) ++ instr-lst)) ∷ [])) ((map (λ (v-val : val) → (instr-val v-val)) val-lst) ++ (as (List instr) ((BR l) ∷ [])))
  br-if-true : ∀ (c : (uN-fam0 (32))) (l : labelidx) → 
    ((proj-uN-0 32 c) ≢ 0) →
    Step-pure (as (List instr) ((instr-CONST numtype-I32 c) ∷ (BR-IF l) ∷ [])) (as (List instr) ((BR l) ∷ []))
  br-if-false : ∀ (c : (uN-fam0 (32))) (l : labelidx) → 
    ((proj-uN-0 32 c) ≡ 0) →
    Step-pure (as (List instr) ((instr-CONST numtype-I32 c) ∷ (BR-IF l) ∷ [])) []
  br-table-lt : ∀ (i : (uN-fam0 (32))) (l-lst : (List labelidx)) (l' : labelidx) → 
    ((proj-uN-0 32 i) < (length l-lst)) →
    Step-pure (as (List instr) ((instr-CONST numtype-I32 i) ∷ (BR-TABLE l-lst l') ∷ [])) (as (List instr) ((BR (l-lst [ (proj-uN-0 32 i) ]!)) ∷ []))
  br-table-ge : ∀ (i : (uN-fam0 (32))) (l-lst : (List labelidx)) (l' : labelidx) → 
    ((proj-uN-0 32 i) ≥ (length l-lst)) →
    Step-pure (as (List instr) ((instr-CONST numtype-I32 i) ∷ (BR-TABLE l-lst l') ∷ [])) (as (List instr) ((BR l') ∷ []))
  br-on-null-null : ∀ (v-val : val) (l : labelidx) → 
    (v-val ≡ val-REF-NULL-ADDR) →
    Step-pure (as (List instr) ((instr-val v-val) ∷ (BR-ON-NULL l) ∷ [])) (as (List instr) ((BR l) ∷ []))
  br-on-null-addr : ∀ (v-val : val) (l : labelidx) → 
    (v-val ≢ val-REF-NULL-ADDR) →
    Step-pure (as (List instr) ((instr-val v-val) ∷ (BR-ON-NULL l) ∷ [])) ((instr-val v-val) ∷ [])
  br-on-non-null-null : ∀ (v-val : val) (l : labelidx) → 
    (v-val ≡ val-REF-NULL-ADDR) →
    Step-pure (as (List instr) ((instr-val v-val) ∷ (BR-ON-NON-NULL l) ∷ [])) []
  br-on-non-null-addr : ∀ (v-val : val) (l : labelidx) → 
    (v-val ≢ val-REF-NULL-ADDR) →
    Step-pure (as (List instr) ((instr-val v-val) ∷ (BR-ON-NON-NULL l) ∷ [])) (as (List instr) ((instr-val v-val) ∷ (BR l) ∷ []))
  Step-pure--call-indirect : ∀ (x : idx) (yy : typeuse) → Step-pure (as (List instr) ((CALL-INDIRECT x yy) ∷ [])) (as (List instr) ((TABLE-GET x) ∷ (REF-CAST (reftype-REF (just NULL) (heaptype-typeuse yy))) ∷ (CALL-REF yy) ∷ []))
  Step-pure--return-call-indirect : ∀ (x : idx) (yy : typeuse) → Step-pure (as (List instr) ((RETURN-CALL-INDIRECT x yy) ∷ [])) (as (List instr) ((TABLE-GET x) ∷ (REF-CAST (reftype-REF (just NULL) (heaptype-typeuse yy))) ∷ (RETURN-CALL-REF yy) ∷ []))
  frame-vals : ∀ (v-n : n) (f : frame) (val-lst : (List val)) → 
    ((length (val-lst)) ≡ (v-n)) →
    Step-pure (as (List instr) ((FRAME- v-n f (map (λ (v-val : val) → (instr-val v-val)) val-lst)) ∷ [])) (map (λ (v-val : val) → (instr-val v-val)) val-lst)
  return-frame : ∀ (v-n : n) (f : frame) (val'-lst : (List val)) (val-lst : (List val)) (instr-lst : (List instr)) → 
    ((length (val-lst)) ≡ (v-n)) →
    Step-pure (as (List instr) ((FRAME- v-n f ((((map (λ (val' : val) → (instr-val val')) val'-lst) ++ (map (λ (v-val : val) → (instr-val v-val)) val-lst)) ++ (as (List instr) (RETURN ∷ []))) ++ instr-lst)) ∷ [])) (map (λ (v-val : val) → (instr-val v-val)) val-lst)
  return-label : ∀ (v-n : n) (instr'-lst : (List instr)) (val-lst : (List val)) (instr-lst : (List instr)) → Step-pure (as (List instr) ((LABEL- v-n instr'-lst (((map (λ (v-val : val) → (instr-val v-val)) val-lst) ++ (as (List instr) (RETURN ∷ []))) ++ instr-lst)) ∷ [])) ((map (λ (v-val : val) → (instr-val v-val)) val-lst) ++ (as (List instr) (RETURN ∷ [])))
  return-handler : ∀ (v-n : n) (catch-lst : (List catch)) (val-lst : (List val)) (instr-lst : (List instr)) → Step-pure (as (List instr) ((HANDLER- v-n catch-lst (((map (λ (v-val : val) → (instr-val v-val)) val-lst) ++ (as (List instr) (RETURN ∷ []))) ++ instr-lst)) ∷ [])) ((map (λ (v-val : val) → (instr-val v-val)) val-lst) ++ (as (List instr) (RETURN ∷ [])))
  handler-vals : ∀ (v-n : n) (catch-lst : (List catch)) (val-lst : (List val)) → Step-pure (as (List instr) ((HANDLER- v-n catch-lst (map (λ (v-val : val) → (instr-val v-val)) val-lst)) ∷ [])) (map (λ (v-val : val) → (instr-val v-val)) val-lst)
  trap-instrs : ∀ (val-lst : (List val)) (instr-lst : (List instr)) → 
    ((val-lst ≢ []) ⊎ (instr-lst ≢ [])) →
    Step-pure ((map (λ (v-val : val) → (instr-val v-val)) val-lst) ++ ((as (List instr) (TRAP ∷ [])) ++ instr-lst)) (as (List instr) (TRAP ∷ []))
  trap-label : ∀ (v-n : n) (instr'-lst : (List instr)) → Step-pure (as (List instr) ((LABEL- v-n instr'-lst (as (List instr) (TRAP ∷ []))) ∷ [])) (as (List instr) (TRAP ∷ []))
  trap-handler : ∀ (v-n : n) (catch-lst : (List catch)) → Step-pure (as (List instr) ((HANDLER- v-n catch-lst (as (List instr) (TRAP ∷ []))) ∷ [])) (as (List instr) (TRAP ∷ []))
  trap-frame : ∀ (v-n : n) (f : frame) → Step-pure (as (List instr) ((FRAME- v-n f (as (List instr) (TRAP ∷ []))) ∷ [])) (as (List instr) (TRAP ∷ []))
  Step-pure--local-tee : ∀ (v-val : val) (x : idx) → Step-pure (as (List instr) ((instr-val v-val) ∷ (LOCAL-TEE x) ∷ [])) (as (List instr) ((instr-val v-val) ∷ (instr-val v-val) ∷ (LOCAL-SET x) ∷ []))
  Step-pure--ref-i31 : ∀ (i : (uN-fam0 (32))) → Step-pure (as (List instr) ((instr-CONST numtype-I32 i) ∷ REF-I31 ∷ [])) (as (List instr) ((instr-REF-I31-NUM (wrap-- 32 31 i)) ∷ []))
  ref-is-null-true : ∀ (v-ref : ref) → 
    (v-ref ≡ REF-NULL-ADDR) →
    Step-pure (as (List instr) ((instr-ref v-ref) ∷ REF-IS-NULL ∷ [])) (as (List instr) ((instr-CONST numtype-I32 (mk-uN 1)) ∷ []))
  ref-is-null-false : ∀ (v-ref : ref) → 
    (v-ref ≢ REF-NULL-ADDR) →
    Step-pure (as (List instr) ((instr-ref v-ref) ∷ REF-IS-NULL ∷ [])) (as (List instr) ((instr-CONST numtype-I32 (mk-uN 0)) ∷ []))
  ref-as-non-null-null : ∀ (v-ref : ref) → 
    (v-ref ≡ REF-NULL-ADDR) →
    Step-pure (as (List instr) ((instr-ref v-ref) ∷ REF-AS-NON-NULL ∷ [])) (as (List instr) (TRAP ∷ []))
  ref-as-non-null-addr : ∀ (v-ref : ref) → 
    (v-ref ≢ REF-NULL-ADDR) →
    Step-pure (as (List instr) ((instr-ref v-ref) ∷ REF-AS-NON-NULL ∷ [])) ((instr-ref v-ref) ∷ [])
  ref-eq-null : ∀ (ref-1 : ref) (ref-2 : ref) → 
    ((ref-1 ≡ REF-NULL-ADDR) × (ref-2 ≡ REF-NULL-ADDR)) →
    Step-pure (as (List instr) ((instr-ref ref-1) ∷ (instr-ref ref-2) ∷ REF-EQ ∷ [])) (as (List instr) ((instr-CONST numtype-I32 (mk-uN 1)) ∷ []))
  ref-eq-true : ∀ (ref-1 : ref) (ref-2 : ref) → 
    ((ref-1 ≢ REF-NULL-ADDR) ⊎ (ref-2 ≢ REF-NULL-ADDR)) →
    (ref-1 ≡ ref-2) →
    Step-pure (as (List instr) ((instr-ref ref-1) ∷ (instr-ref ref-2) ∷ REF-EQ ∷ [])) (as (List instr) ((instr-CONST numtype-I32 (mk-uN 1)) ∷ []))
  ref-eq-false : ∀ (ref-1 : ref) (ref-2 : ref) → 
    (ref-1 ≢ ref-2) →
    ((ref-1 ≢ REF-NULL-ADDR) ⊎ (ref-2 ≢ REF-NULL-ADDR)) →
    Step-pure (as (List instr) ((instr-ref ref-1) ∷ (instr-ref ref-2) ∷ REF-EQ ∷ [])) (as (List instr) ((instr-CONST numtype-I32 (mk-uN 0)) ∷ []))
  i31-get-null : ∀ (v-sx : sx) → Step-pure (as (List instr) (instr-REF-NULL-ADDR ∷ (I31-GET v-sx) ∷ [])) (as (List instr) (TRAP ∷ []))
  i31-get-num : ∀ (i : u31) (v-sx : sx) → Step-pure (as (List instr) ((instr-REF-I31-NUM i) ∷ (I31-GET v-sx) ∷ [])) (as (List instr) ((instr-CONST numtype-I32 (extend-- 31 32 v-sx i)) ∷ []))
  Step-pure--array-new : ∀ (v-val : val) (v-n : n) (x : idx) → Step-pure (as (List instr) ((instr-val v-val) ∷ (instr-CONST numtype-I32 (mk-uN v-n)) ∷ (ARRAY-NEW x) ∷ [])) ((replicate v-n (instr-val v-val)) ++ (as (List instr) ((ARRAY-NEW-FIXED x (mk-uN v-n)) ∷ [])))
  extern-convert-any-null : ∀ (v-ref : ref) → 
    (v-ref ≡ REF-NULL-ADDR) →
    Step-pure (as (List instr) ((instr-ref v-ref) ∷ EXTERN-CONVERT-ANY ∷ [])) (as (List instr) (instr-REF-NULL-ADDR ∷ []))
  extern-convert-any-addr : ∀ (v-ref : ref) → 
    (v-ref ≢ REF-NULL-ADDR) →
    Step-pure (as (List instr) ((instr-ref v-ref) ∷ EXTERN-CONVERT-ANY ∷ [])) (as (List instr) ((instr-REF-EXTERN v-ref) ∷ []))
  any-convert-extern-null : Step-pure (as (List instr) (instr-REF-NULL-ADDR ∷ ANY-CONVERT-EXTERN ∷ [])) (as (List instr) (instr-REF-NULL-ADDR ∷ []))
  any-convert-extern-addr : ∀ (v-ref : ref) → Step-pure (as (List instr) ((instr-REF-EXTERN v-ref) ∷ ANY-CONVERT-EXTERN ∷ [])) ((instr-ref v-ref) ∷ [])
  unop-val : ∀ (nt : numtype) (c-1 : (num- nt)) (unop : (unop- nt)) (c : (num- nt)) → 
    ((length (fun-unop- nt unop c-1)) > 0) →
    (c ∈ (fun-unop- nt unop c-1)) →
    Step-pure (as (List instr) ((instr-CONST nt c-1) ∷ (UNOP nt unop) ∷ [])) (as (List instr) ((instr-CONST nt c) ∷ []))
  unop-trap : ∀ (nt : numtype) (c-1 : (num- nt)) (unop : (unop- nt)) → 
    ((fun-unop- nt unop c-1) ≡ []) →
    Step-pure (as (List instr) ((instr-CONST nt c-1) ∷ (UNOP nt unop) ∷ [])) (as (List instr) (TRAP ∷ []))
  binop-val : ∀ (nt : numtype) (c-1 : (num- nt)) (c-2 : (num- nt)) (binop : (binop- nt)) (c : (num- nt)) → 
    ((length (fun-binop- nt binop c-1 c-2)) > 0) →
    (c ∈ (fun-binop- nt binop c-1 c-2)) →
    Step-pure (as (List instr) ((instr-CONST nt c-1) ∷ (instr-CONST nt c-2) ∷ (BINOP nt binop) ∷ [])) (as (List instr) ((instr-CONST nt c) ∷ []))
  binop-trap : ∀ (nt : numtype) (c-1 : (num- nt)) (c-2 : (num- nt)) (binop : (binop- nt)) → 
    ((fun-binop- nt binop c-1 c-2) ≡ []) →
    Step-pure (as (List instr) ((instr-CONST nt c-1) ∷ (instr-CONST nt c-2) ∷ (BINOP nt binop) ∷ [])) (as (List instr) (TRAP ∷ []))
  Step-pure--testop : ∀ (nt : numtype) (c-1 : (num- nt)) (testop : (testop- nt)) (c : (uN-fam0 (32))) → 
    (c ≡ (fun-testop- nt testop c-1)) →
    Step-pure (as (List instr) ((instr-CONST nt c-1) ∷ (TESTOP nt testop) ∷ [])) (as (List instr) ((instr-CONST numtype-I32 c) ∷ []))
  Step-pure--relop : ∀ (nt : numtype) (c-1 : (num- nt)) (c-2 : (num- nt)) (relop : (relop- nt)) (c : (uN-fam0 (32))) → 
    (c ≡ (fun-relop- nt relop c-1 c-2)) →
    Step-pure (as (List instr) ((instr-CONST nt c-1) ∷ (instr-CONST nt c-2) ∷ (RELOP nt relop) ∷ [])) (as (List instr) ((instr-CONST numtype-I32 c) ∷ []))
  cvtop-val : ∀ (nt-1 : numtype) (c-1 : (num- nt-1)) (nt-2 : numtype) (cvtop : (cvtop-- nt-1 nt-2)) (c : (num- nt-2)) → 
    ((length (fun-cvtop-- nt-1 nt-2 cvtop c-1)) > 0) →
    (c ∈ (fun-cvtop-- nt-1 nt-2 cvtop c-1)) →
    Step-pure (as (List instr) ((instr-CONST nt-1 c-1) ∷ (CVTOP nt-2 nt-1 cvtop) ∷ [])) (as (List instr) ((instr-CONST nt-2 c) ∷ []))
  cvtop-trap : ∀ (nt-1 : numtype) (c-1 : (num- nt-1)) (nt-2 : numtype) (cvtop : (cvtop-- nt-1 nt-2)) → 
    ((fun-cvtop-- nt-1 nt-2 cvtop c-1) ≡ []) →
    Step-pure (as (List instr) ((instr-CONST nt-1 c-1) ∷ (CVTOP nt-2 nt-1 cvtop) ∷ [])) (as (List instr) (TRAP ∷ []))
  Step-pure--vvunop : ∀ (c-1 : (uN-fam0 (128))) (v-vvunop : vvunop) (c : (uN-fam0 (128))) → 
    ((length (vvunop- V128 v-vvunop c-1)) > 0) →
    (c ∈ (vvunop- V128 v-vvunop c-1)) →
    Step-pure (as (List instr) ((instr-VCONST V128 c-1) ∷ (VVUNOP V128 v-vvunop) ∷ [])) (as (List instr) ((instr-VCONST V128 c) ∷ []))
  Step-pure--vvbinop : ∀ (c-1 : (uN-fam0 (128))) (c-2 : (uN-fam0 (128))) (v-vvbinop : vvbinop) (c : (uN-fam0 (128))) → 
    ((length (vvbinop- V128 v-vvbinop c-1 c-2)) > 0) →
    (c ∈ (vvbinop- V128 v-vvbinop c-1 c-2)) →
    Step-pure (as (List instr) ((instr-VCONST V128 c-1) ∷ (instr-VCONST V128 c-2) ∷ (VVBINOP V128 v-vvbinop) ∷ [])) (as (List instr) ((instr-VCONST V128 c) ∷ []))
  Step-pure--vvternop : ∀ (c-1 : (uN-fam0 (128))) (c-2 : (uN-fam0 (128))) (c-3 : (uN-fam0 (128))) (v-vvternop : vvternop) (c : (uN-fam0 (128))) → 
    ((length (vvternop- V128 v-vvternop c-1 c-2 c-3)) > 0) →
    (c ∈ (vvternop- V128 v-vvternop c-1 c-2 c-3)) →
    Step-pure (as (List instr) ((instr-VCONST V128 c-1) ∷ (instr-VCONST V128 c-2) ∷ (instr-VCONST V128 c-3) ∷ (VVTERNOP V128 v-vvternop) ∷ [])) (as (List instr) ((instr-VCONST V128 c) ∷ []))
  Step-pure--vvtestop : ∀ (c-1 : (uN-fam0 (128))) (c : (uN-fam0 (32))) → 
    (c ≡ (inez- (vsize V128) c-1)) →
    Step-pure (as (List instr) ((instr-VCONST V128 c-1) ∷ (VVTESTOP V128 ANY-TRUE) ∷ [])) (as (List instr) ((instr-CONST numtype-I32 c) ∷ []))
  vunop-val : ∀ (c-1 : (uN-fam0 (128))) (sh : shape) (vunop : (vunop- sh)) (c : (uN-fam0 (128))) → 
    ((length (fun-vunop- sh vunop c-1)) > 0) →
    (c ∈ (fun-vunop- sh vunop c-1)) →
    Step-pure (as (List instr) ((instr-VCONST V128 c-1) ∷ (VUNOP sh vunop) ∷ [])) (as (List instr) ((instr-VCONST V128 c) ∷ []))
  vunop-trap : ∀ (c-1 : (uN-fam0 (128))) (sh : shape) (vunop : (vunop- sh)) → 
    ((fun-vunop- sh vunop c-1) ≡ []) →
    Step-pure (as (List instr) ((instr-VCONST V128 c-1) ∷ (VUNOP sh vunop) ∷ [])) (as (List instr) (TRAP ∷ []))
  vbinop-val : ∀ (c-1 : (uN-fam0 (128))) (c-2 : (uN-fam0 (128))) (sh : shape) (vbinop : (vbinop- sh)) (c : (uN-fam0 (128))) → 
    ((length (fun-vbinop- sh vbinop c-1 c-2)) > 0) →
    (c ∈ (fun-vbinop- sh vbinop c-1 c-2)) →
    Step-pure (as (List instr) ((instr-VCONST V128 c-1) ∷ (instr-VCONST V128 c-2) ∷ (VBINOP sh vbinop) ∷ [])) (as (List instr) ((instr-VCONST V128 c) ∷ []))
  vbinop-trap : ∀ (c-1 : (uN-fam0 (128))) (c-2 : (uN-fam0 (128))) (sh : shape) (vbinop : (vbinop- sh)) → 
    ((fun-vbinop- sh vbinop c-1 c-2) ≡ []) →
    Step-pure (as (List instr) ((instr-VCONST V128 c-1) ∷ (instr-VCONST V128 c-2) ∷ (VBINOP sh vbinop) ∷ [])) (as (List instr) (TRAP ∷ []))
  vternop-val : ∀ (c-1 : (uN-fam0 (128))) (c-2 : (uN-fam0 (128))) (c-3 : (uN-fam0 (128))) (sh : shape) (vternop : (vternop- sh)) (c : (uN-fam0 (128))) → 
    ((length (fun-vternop- sh vternop c-1 c-2 c-3)) > 0) →
    (c ∈ (fun-vternop- sh vternop c-1 c-2 c-3)) →
    Step-pure (as (List instr) ((instr-VCONST V128 c-1) ∷ (instr-VCONST V128 c-2) ∷ (instr-VCONST V128 c-3) ∷ (VTERNOP sh vternop) ∷ [])) (as (List instr) ((instr-VCONST V128 c) ∷ []))
  vternop-trap : ∀ (c-1 : (uN-fam0 (128))) (c-2 : (uN-fam0 (128))) (c-3 : (uN-fam0 (128))) (sh : shape) (vternop : (vternop- sh)) → 
    ((fun-vternop- sh vternop c-1 c-2 c-3) ≡ []) →
    Step-pure (as (List instr) ((instr-VCONST V128 c-1) ∷ (instr-VCONST V128 c-2) ∷ (instr-VCONST V128 c-3) ∷ (VTERNOP sh vternop) ∷ [])) (as (List instr) (TRAP ∷ []))
  vtestop-0 : ∀ (c-1 : (uN-fam0 (128))) (v-M : M) (c : (uN-fam0 (32))) (i-lst : (List (uN-fam0 (32)))) → 
    (i-lst ≡ (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) c-1)) →
    ((proj-uN-0 32 c) ≡ (prod (map (λ (i-172609 : (uN-fam0 (32))) → (proj-uN-0 32 (inez- (jsizenn Jnn-I32) i-172609))) i-lst))) →
    Step-pure (as (List instr) ((instr-VCONST V128 c-1) ∷ (VTESTOP (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) ALL-TRUE) ∷ [])) (as (List instr) ((instr-CONST numtype-I32 c) ∷ []))
  vtestop-1 : ∀ (c-1 : (uN-fam0 (128))) (v-M : M) (c : (uN-fam0 (32))) (i-lst : (List (uN-fam0 (64)))) → 
    (i-lst ≡ (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) c-1)) →
    ((proj-uN-0 32 c) ≡ (prod (map (λ (i-172620 : (uN-fam0 (64))) → (proj-uN-0 32 (inez- (jsizenn Jnn-I64) i-172620))) i-lst))) →
    Step-pure (as (List instr) ((instr-VCONST V128 c-1) ∷ (VTESTOP (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) ALL-TRUE) ∷ [])) (as (List instr) ((instr-CONST numtype-I32 c) ∷ []))
  vtestop-2 : ∀ (c-1 : (uN-fam0 (128))) (v-M : M) (c : (uN-fam0 (32))) (i-lst : (List (uN-fam0 (8)))) → 
    (i-lst ≡ (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) c-1)) →
    ((proj-uN-0 32 c) ≡ (prod (map (λ (i-172631 : (uN-fam0 (8))) → (proj-uN-0 32 (inez- (jsizenn Jnn-I8) i-172631))) i-lst))) →
    Step-pure (as (List instr) ((instr-VCONST V128 c-1) ∷ (VTESTOP (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) ALL-TRUE) ∷ [])) (as (List instr) ((instr-CONST numtype-I32 c) ∷ []))
  vtestop-3 : ∀ (c-1 : (uN-fam0 (128))) (v-M : M) (c : (uN-fam0 (32))) (i-lst : (List (uN-fam0 (16)))) → 
    (i-lst ≡ (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) c-1)) →
    ((proj-uN-0 32 c) ≡ (prod (map (λ (i-172642 : (uN-fam0 (16))) → (proj-uN-0 32 (inez- (jsizenn Jnn-I16) i-172642))) i-lst))) →
    Step-pure (as (List instr) ((instr-VCONST V128 c-1) ∷ (VTESTOP (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) ALL-TRUE) ∷ [])) (as (List instr) ((instr-CONST numtype-I32 c) ∷ []))
  Step-pure--vrelop : ∀ (c-1 : (uN-fam0 (128))) (c-2 : (uN-fam0 (128))) (sh : shape) (vrelop : (vrelop- sh)) (c : (uN-fam0 (128))) → 
    (c ≡ (fun-vrelop- sh vrelop c-1 c-2)) →
    Step-pure (as (List instr) ((instr-VCONST V128 c-1) ∷ (instr-VCONST V128 c-2) ∷ (VRELOP sh vrelop) ∷ [])) (as (List instr) ((instr-VCONST V128 c) ∷ []))
  Step-pure--vshiftop : ∀ (c-1 : (uN-fam0 (128))) (i : (uN-fam0 (32))) (sh : ishape) (vshiftop : (vshiftop- sh)) (c : (uN-fam0 (128))) → 
    (c ≡ (fun-vshiftop- sh vshiftop c-1 i)) →
    Step-pure (as (List instr) ((instr-VCONST V128 c-1) ∷ (instr-CONST numtype-I32 i) ∷ (VSHIFTOP sh vshiftop) ∷ [])) (as (List instr) ((instr-VCONST V128 c) ∷ []))
  Step-pure--vbitmask : ∀ (c-1 : (uN-fam0 (128))) (sh : ishape) (c : (uN-fam0 (32))) → 
    (c ≡ (vbitmaskop- sh c-1)) →
    Step-pure (as (List instr) ((instr-VCONST V128 c-1) ∷ (VBITMASK sh) ∷ [])) (as (List instr) ((instr-CONST numtype-I32 c) ∷ []))
  Step-pure--vswizzlop : ∀ (c-1 : (uN-fam0 (128))) (c-2 : (uN-fam0 (128))) (sh : bshape) (swizzlop : (vswizzlop- sh)) (c : (uN-fam0 (128))) → 
    (c ≡ (fun-vswizzlop- sh swizzlop c-1 c-2)) →
    Step-pure (as (List instr) ((instr-VCONST V128 c-1) ∷ (instr-VCONST V128 c-2) ∷ (VSWIZZLOP sh swizzlop) ∷ [])) (as (List instr) ((instr-VCONST V128 c) ∷ []))
  Step-pure--vshuffle : ∀ (c-1 : (uN-fam0 (128))) (c-2 : (uN-fam0 (128))) (sh : bshape) (i-lst : (List laneidx)) (c : (uN-fam0 (128))) (o0 : (uN-fam0 (128))) → 
    ((vshufflop- sh i-lst c-1 c-2) ≡ (just o0)) →
    (c ≡ o0) →
    Step-pure (as (List instr) ((instr-VCONST V128 c-1) ∷ (instr-VCONST V128 c-2) ∷ (VSHUFFLE sh i-lst) ∷ [])) (as (List instr) ((instr-VCONST V128 c) ∷ []))
  Step-pure--vsplat : ∀ (v-Lnn : Lnn) (c-1 : (num- (lunpack v-Lnn))) (v-M : M) (c : (uN-fam0 (128))) → 
    (c ≡ (inv-lanes- (X v-Lnn (mk-dim v-M)) (replicate v-M (lpacknum- v-Lnn c-1)))) →
    Step-pure (as (List instr) ((instr-CONST (lunpack v-Lnn) c-1) ∷ (VSPLAT (X v-Lnn (mk-dim v-M))) ∷ [])) (as (List instr) ((instr-VCONST V128 c) ∷ []))
  vextract-lane-num-0 : ∀ (c-1 : (uN-fam0 (128))) (v-M : M) (i : laneidx) (c-2 : (uN-fam0 (32))) → 
    ((proj-uN-0 8 i) < (length (lanes- (X (lanetype-numtype numtype-I32) (mk-dim v-M)) c-1))) →
    (c-2 ≡ ((lanes- (X (lanetype-numtype numtype-I32) (mk-dim v-M)) c-1) [ (proj-uN-0 8 i) ]!)) →
    Step-pure (as (List instr) ((instr-VCONST V128 c-1) ∷ (VEXTRACT-LANE (X (lanetype-numtype numtype-I32) (mk-dim v-M)) nothing i) ∷ [])) (as (List instr) ((instr-CONST numtype-I32 c-2) ∷ []))
  vextract-lane-num-1 : ∀ (c-1 : (uN-fam0 (128))) (v-M : M) (i : laneidx) (c-2 : (uN-fam0 (64))) → 
    ((proj-uN-0 8 i) < (length (lanes- (X (lanetype-numtype numtype-I64) (mk-dim v-M)) c-1))) →
    (c-2 ≡ ((lanes- (X (lanetype-numtype numtype-I64) (mk-dim v-M)) c-1) [ (proj-uN-0 8 i) ]!)) →
    Step-pure (as (List instr) ((instr-VCONST V128 c-1) ∷ (VEXTRACT-LANE (X (lanetype-numtype numtype-I64) (mk-dim v-M)) nothing i) ∷ [])) (as (List instr) ((instr-CONST numtype-I64 c-2) ∷ []))
  vextract-lane-num-2 : ∀ (c-1 : (uN-fam0 (128))) (v-M : M) (i : laneidx) (c-2 : (fN-fam0 (32))) → 
    ((proj-uN-0 8 i) < (length (lanes- (X (lanetype-numtype F32) (mk-dim v-M)) c-1))) →
    (c-2 ≡ ((lanes- (X (lanetype-numtype F32) (mk-dim v-M)) c-1) [ (proj-uN-0 8 i) ]!)) →
    Step-pure (as (List instr) ((instr-VCONST V128 c-1) ∷ (VEXTRACT-LANE (X (lanetype-numtype F32) (mk-dim v-M)) nothing i) ∷ [])) (as (List instr) ((instr-CONST F32 c-2) ∷ []))
  vextract-lane-num-3 : ∀ (c-1 : (uN-fam0 (128))) (v-M : M) (i : laneidx) (c-2 : (fN-fam0 (64))) → 
    ((proj-uN-0 8 i) < (length (lanes- (X (lanetype-numtype F64) (mk-dim v-M)) c-1))) →
    (c-2 ≡ ((lanes- (X (lanetype-numtype F64) (mk-dim v-M)) c-1) [ (proj-uN-0 8 i) ]!)) →
    Step-pure (as (List instr) ((instr-VCONST V128 c-1) ∷ (VEXTRACT-LANE (X (lanetype-numtype F64) (mk-dim v-M)) nothing i) ∷ [])) (as (List instr) ((instr-CONST F64 c-2) ∷ []))
  vextract-lane-pack-0 : ∀ (c-1 : (uN-fam0 (128))) (v-M : M) (v-sx : sx) (i : laneidx) (c-2 : (uN-fam0 (32))) → 
    ((proj-uN-0 8 i) < (length (lanes- (X (lanetype-packtype packtype-I8) (mk-dim v-M)) c-1))) →
    (c-2 ≡ (extend-- (psize packtype-I8) 32 v-sx ((lanes- (X (lanetype-packtype packtype-I8) (mk-dim v-M)) c-1) [ (proj-uN-0 8 i) ]!))) →
    Step-pure (as (List instr) ((instr-VCONST V128 c-1) ∷ (VEXTRACT-LANE (X (lanetype-packtype packtype-I8) (mk-dim v-M)) (just v-sx) i) ∷ [])) (as (List instr) ((instr-CONST numtype-I32 c-2) ∷ []))
  vextract-lane-pack-1 : ∀ (c-1 : (uN-fam0 (128))) (v-M : M) (v-sx : sx) (i : laneidx) (c-2 : (uN-fam0 (32))) → 
    ((proj-uN-0 8 i) < (length (lanes- (X (lanetype-packtype packtype-I16) (mk-dim v-M)) c-1))) →
    (c-2 ≡ (extend-- (psize packtype-I16) 32 v-sx ((lanes- (X (lanetype-packtype packtype-I16) (mk-dim v-M)) c-1) [ (proj-uN-0 8 i) ]!))) →
    Step-pure (as (List instr) ((instr-VCONST V128 c-1) ∷ (VEXTRACT-LANE (X (lanetype-packtype packtype-I16) (mk-dim v-M)) (just v-sx) i) ∷ [])) (as (List instr) ((instr-CONST numtype-I32 c-2) ∷ []))
  Step-pure--vreplace-lane : ∀ (c-1 : (uN-fam0 (128))) (v-Lnn : Lnn) (c-2 : (num- (lunpack v-Lnn))) (v-M : M) (i : laneidx) (c : (uN-fam0 (128))) → 
    (c ≡ (inv-lanes- (X v-Lnn (mk-dim v-M)) (modify (lanes- (X v-Lnn (mk-dim v-M)) c-1) (proj-uN-0 8 i) (λ (_ : (lane- (fun-lanetype (X v-Lnn (mk-dim v-M))))) → (lpacknum- v-Lnn c-2))))) →
    Step-pure (as (List instr) ((instr-VCONST V128 c-1) ∷ (instr-CONST (lunpack v-Lnn) c-2) ∷ (VREPLACE-LANE (X v-Lnn (mk-dim v-M)) i) ∷ [])) (as (List instr) ((instr-VCONST V128 c) ∷ []))
  Step-pure--vextunop : ∀ (c-1 : (uN-fam0 (128))) (sh-2 : ishape) (sh-1 : ishape) (vextunop : (vextunop-- sh-1 sh-2)) (c : (uN-fam0 (128))) → 
    ((fun-vextunop-- sh-1 sh-2 vextunop c-1) ≡ c) →
    Step-pure (as (List instr) ((instr-VCONST V128 c-1) ∷ (VEXTUNOP sh-2 sh-1 vextunop) ∷ [])) (as (List instr) ((instr-VCONST V128 c) ∷ []))
  Step-pure--vextbinop : ∀ (c-1 : (uN-fam0 (128))) (c-2 : (uN-fam0 (128))) (sh-2 : ishape) (sh-1 : ishape) (vextbinop : (vextbinop-- sh-1 sh-2)) (c : (uN-fam0 (128))) → 
    ((fun-vextbinop-- sh-1 sh-2 vextbinop c-1 c-2) ≡ c) →
    Step-pure (as (List instr) ((instr-VCONST V128 c-1) ∷ (instr-VCONST V128 c-2) ∷ (VEXTBINOP sh-2 sh-1 vextbinop) ∷ [])) (as (List instr) ((instr-VCONST V128 c) ∷ []))
  Step-pure--vextternop : ∀ (c-1 : (uN-fam0 (128))) (c-2 : (uN-fam0 (128))) (c-3 : (uN-fam0 (128))) (sh-2 : ishape) (sh-1 : ishape) (vextternop : (vextternop-- sh-1 sh-2)) (c : (uN-fam0 (128))) → 
    ((fun-vextternop-- sh-1 sh-2 vextternop c-1 c-2 c-3) ≡ c) →
    Step-pure (as (List instr) ((instr-VCONST V128 c-1) ∷ (instr-VCONST V128 c-2) ∷ (instr-VCONST V128 c-3) ∷ (VEXTTERNOP sh-2 sh-1 vextternop) ∷ [])) (as (List instr) ((instr-VCONST V128 c) ∷ []))
  Step-pure--vnarrow : ∀ (c-1 : (uN-fam0 (128))) (c-2 : (uN-fam0 (128))) (sh-2 : ishape) (sh-1 : ishape) (v-sx : sx) (c : (uN-fam0 (128))) → 
    (c ≡ (vnarrowop-- (coerce {B = shape} (sh-1)) (coerce {B = shape} (sh-2)) v-sx c-1 c-2)) →
    Step-pure (as (List instr) ((instr-VCONST V128 c-1) ∷ (instr-VCONST V128 c-2) ∷ (VNARROW sh-2 sh-1 v-sx) ∷ [])) (as (List instr) ((instr-VCONST V128 c) ∷ []))
  Step-pure--vcvtop : ∀ (c-1 : (uN-fam0 (128))) (sh-2 : shape) (sh-1 : shape) (vcvtop : (vcvtop-- sh-1 sh-2)) (c : (uN-fam0 (128))) → 
    (c ≡ (fun-vcvtop-- sh-1 sh-2 vcvtop c-1)) →
    Step-pure (as (List instr) ((instr-VCONST V128 c-1) ∷ (VCVTOP sh-2 sh-1 vcvtop) ∷ [])) (as (List instr) ((instr-VCONST V128 c) ∷ []))

{- Auxiliary Definition at: ../specification/wasm-3.0/4.3-execution.instructions.spectec:73.1-73.71 -}
postulate blocktype- : ∀ (v-state : state) (v-blocktype : blocktype) → instrtype

{- Inductive Relations Definition at: ../specification/wasm-3.0/4.3-execution.instructions.spectec:153.1-155.15 -}
data Step-read-before-br-on-cast-fail : config → Set where
  br-on-cast-succeed-0 : ∀ (s : store) (f : frame) (v-ref : ref) (l : labelidx) (rt-1 : reftype) (rt-2 : reftype) → 
    (Ref-ok s v-ref (inst-reftype (MODULE f) rt-2)) →
    Step-read-before-br-on-cast-fail (mk-config (mk-state s f) (as (List instr) ((instr-ref v-ref) ∷ (BR-ON-CAST l rt-1 rt-2) ∷ [])))

{- Inductive Relations Definition at: ../specification/wasm-3.0/4.3-execution.instructions.spectec:162.1-164.15 -}
data Step-read-before-br-on-cast-fail-fail : config → Set where
  br-on-cast-fail-succeed-0 : ∀ (s : store) (f : frame) (v-ref : ref) (l : labelidx) (rt-1 : reftype) (rt-2 : reftype) → 
    (Ref-ok s v-ref (inst-reftype (MODULE f) rt-2)) →
    Step-read-before-br-on-cast-fail-fail (mk-config (mk-state s f) (as (List instr) ((instr-ref v-ref) ∷ (BR-ON-CAST-FAIL l rt-1 rt-2) ∷ [])))

{- Inductive Relations Definition at: ../specification/wasm-3.0/4.3-execution.instructions.spectec:268.1-271.15 -}
data Step-read-before-throw-ref-handler-next : config → Set where
  throw-ref-handler-catch-all-ref-0 : ∀ (z : state) (v-n : n) (l : labelidx) (catch'-lst : (List catch)) (a : addr) → Step-read-before-throw-ref-handler-next (mk-config z (as (List instr) ((HANDLER- v-n ((as (List catch) ((CATCH-ALL-REF l) ∷ [])) ++ catch'-lst) (as (List instr) ((instr-REF-EXN-ADDR a) ∷ THROW-REF ∷ []))) ∷ [])))
  throw-ref-handler-catch-all-0 : ∀ (z : state) (v-n : n) (l : labelidx) (catch'-lst : (List catch)) (a : addr) → Step-read-before-throw-ref-handler-next (mk-config z (as (List instr) ((HANDLER- v-n ((as (List catch) ((CATCH-ALL l) ∷ [])) ++ catch'-lst) (as (List instr) ((instr-REF-EXN-ADDR a) ∷ THROW-REF ∷ []))) ∷ [])))
  throw-ref-handler-catch-ref-0 : ∀ (z : state) (v-n : n) (x : idx) (l : labelidx) (catch'-lst : (List catch)) (a : addr) (val-lst : (List val)) → 
    (a < (length (fun-exninst z))) →
    ((proj-uN-0 32 x) < (length (fun-tagaddr z))) →
    ((exninst-TAG ((fun-exninst z) [ a ]!)) ≡ ((fun-tagaddr z) [ (proj-uN-0 32 x) ]!)) →
    (val-lst ≡ (exninst-FIELDS ((fun-exninst z) [ a ]!))) →
    Step-read-before-throw-ref-handler-next (mk-config z (as (List instr) ((HANDLER- v-n ((as (List catch) ((CATCH-REF x l) ∷ [])) ++ catch'-lst) (as (List instr) ((instr-REF-EXN-ADDR a) ∷ THROW-REF ∷ []))) ∷ [])))
  throw-ref-handler-catch-0 : ∀ (z : state) (v-n : n) (x : idx) (l : labelidx) (catch'-lst : (List catch)) (a : addr) (val-lst : (List val)) → 
    (a < (length (fun-exninst z))) →
    ((proj-uN-0 32 x) < (length (fun-tagaddr z))) →
    ((exninst-TAG ((fun-exninst z) [ a ]!)) ≡ ((fun-tagaddr z) [ (proj-uN-0 32 x) ]!)) →
    (val-lst ≡ (exninst-FIELDS ((fun-exninst z) [ a ]!))) →
    Step-read-before-throw-ref-handler-next (mk-config z (as (List instr) ((HANDLER- v-n ((as (List catch) ((CATCH x l) ∷ [])) ++ catch'-lst) (as (List instr) ((instr-REF-EXN-ADDR a) ∷ THROW-REF ∷ []))) ∷ [])))

{- Inductive Relations Definition at: ../specification/wasm-3.0/4.3-execution.instructions.spectec:360.1-363.14 -}
data Step-read-before-table-fill-zero : config → Set where
  table-fill-oob-0-0 : ∀ (z : state) (i : (uN-fam0 (32))) (v-val : val) (v-n : n) (x : idx) → 
    (((proj-uN-0 (size (numtype-addrtype I32)) i) + v-n) > (length (tableinst-REFS (fun-table z x)))) →
    Step-read-before-table-fill-zero (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i) ∷ (instr-val v-val) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (TABLE-FILL x) ∷ [])))
  table-fill-oob-0-1 : ∀ (z : state) (i : (uN-fam0 (64))) (v-val : val) (v-n : n) (x : idx) → 
    (((proj-uN-0 (size (numtype-addrtype I64)) i) + v-n) > (length (tableinst-REFS (fun-table z x)))) →
    Step-read-before-table-fill-zero (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i) ∷ (instr-val v-val) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (TABLE-FILL x) ∷ [])))

{- Inductive Relations Definition at: ../specification/wasm-3.0/4.3-execution.instructions.spectec:377.1-380.14 -}
data Step-read-before-table-copy-zero : config → Set where
  table-copy-oob-0-0 : ∀ (z : state) (i-1 : (uN-fam0 (32))) (i-2 : (uN-fam0 (32))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    ((((proj-uN-0 (size (numtype-addrtype I32)) i-1) + v-n) > (length (tableinst-REFS (fun-table z x-1)))) ⊎ (((proj-uN-0 (size (numtype-addrtype I32)) i-2) + v-n) > (length (tableinst-REFS (fun-table z x-2))))) →
    Step-read-before-table-copy-zero (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (TABLE-COPY x-1 x-2) ∷ [])))
  table-copy-oob-0-1 : ∀ (z : state) (i-1 : (uN-fam0 (64))) (i-2 : (uN-fam0 (32))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    ((((proj-uN-0 (size (numtype-addrtype I64)) i-1) + v-n) > (length (tableinst-REFS (fun-table z x-1)))) ⊎ (((proj-uN-0 (size (numtype-addrtype I32)) i-2) + v-n) > (length (tableinst-REFS (fun-table z x-2))))) →
    Step-read-before-table-copy-zero (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (TABLE-COPY x-1 x-2) ∷ [])))
  table-copy-oob-0-2 : ∀ (z : state) (i-1 : (uN-fam0 (32))) (i-2 : (uN-fam0 (64))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    ((((proj-uN-0 (size (numtype-addrtype I32)) i-1) + v-n) > (length (tableinst-REFS (fun-table z x-1)))) ⊎ (((proj-uN-0 (size (numtype-addrtype I64)) i-2) + v-n) > (length (tableinst-REFS (fun-table z x-2))))) →
    Step-read-before-table-copy-zero (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (TABLE-COPY x-1 x-2) ∷ [])))
  table-copy-oob-0-3 : ∀ (z : state) (i-1 : (uN-fam0 (64))) (i-2 : (uN-fam0 (64))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    ((((proj-uN-0 (size (numtype-addrtype I64)) i-1) + v-n) > (length (tableinst-REFS (fun-table z x-1)))) ⊎ (((proj-uN-0 (size (numtype-addrtype I64)) i-2) + v-n) > (length (tableinst-REFS (fun-table z x-2))))) →
    Step-read-before-table-copy-zero (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (TABLE-COPY x-1 x-2) ∷ [])))
  table-copy-oob-0-4 : ∀ (z : state) (i-1 : (uN-fam0 (32))) (i-2 : (uN-fam0 (32))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    ((((proj-uN-0 (size (numtype-addrtype I32)) i-1) + v-n) > (length (tableinst-REFS (fun-table z x-1)))) ⊎ (((proj-uN-0 (size (numtype-addrtype I32)) i-2) + v-n) > (length (tableinst-REFS (fun-table z x-2))))) →
    Step-read-before-table-copy-zero (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (TABLE-COPY x-1 x-2) ∷ [])))
  table-copy-oob-0-5 : ∀ (z : state) (i-1 : (uN-fam0 (64))) (i-2 : (uN-fam0 (32))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    ((((proj-uN-0 (size (numtype-addrtype I64)) i-1) + v-n) > (length (tableinst-REFS (fun-table z x-1)))) ⊎ (((proj-uN-0 (size (numtype-addrtype I32)) i-2) + v-n) > (length (tableinst-REFS (fun-table z x-2))))) →
    Step-read-before-table-copy-zero (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (TABLE-COPY x-1 x-2) ∷ [])))
  table-copy-oob-0-6 : ∀ (z : state) (i-1 : (uN-fam0 (32))) (i-2 : (uN-fam0 (64))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    ((((proj-uN-0 (size (numtype-addrtype I32)) i-1) + v-n) > (length (tableinst-REFS (fun-table z x-1)))) ⊎ (((proj-uN-0 (size (numtype-addrtype I64)) i-2) + v-n) > (length (tableinst-REFS (fun-table z x-2))))) →
    Step-read-before-table-copy-zero (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (TABLE-COPY x-1 x-2) ∷ [])))
  table-copy-oob-0-7 : ∀ (z : state) (i-1 : (uN-fam0 (64))) (i-2 : (uN-fam0 (64))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    ((((proj-uN-0 (size (numtype-addrtype I64)) i-1) + v-n) > (length (tableinst-REFS (fun-table z x-1)))) ⊎ (((proj-uN-0 (size (numtype-addrtype I64)) i-2) + v-n) > (length (tableinst-REFS (fun-table z x-2))))) →
    Step-read-before-table-copy-zero (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (TABLE-COPY x-1 x-2) ∷ [])))

{- Inductive Relations Definition at: ../specification/wasm-3.0/4.3-execution.instructions.spectec:382.1-387.19 -}
data Step-read-before-table-copy-le : config → Set where
  table-copy-zero-0-0 : ∀ (z : state) (i-1 : (uN-fam0 (32))) (i-2 : (uN-fam0 (32))) (v-n : n) (x : idx) (y : idx) → 
    (¬ (Step-read-before-table-copy-zero (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ []))))) →
    (v-n ≡ 0) →
    Step-read-before-table-copy-le (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ [])))
  table-copy-zero-0-1 : ∀ (z : state) (i-1 : (uN-fam0 (64))) (i-2 : (uN-fam0 (32))) (v-n : n) (x : idx) (y : idx) → 
    (¬ (Step-read-before-table-copy-zero (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ []))))) →
    (v-n ≡ 0) →
    Step-read-before-table-copy-le (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ [])))
  table-copy-zero-0-2 : ∀ (z : state) (i-1 : (uN-fam0 (32))) (i-2 : (uN-fam0 (64))) (v-n : n) (x : idx) (y : idx) → 
    (¬ (Step-read-before-table-copy-zero (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ []))))) →
    (v-n ≡ 0) →
    Step-read-before-table-copy-le (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ [])))
  table-copy-zero-0-3 : ∀ (z : state) (i-1 : (uN-fam0 (64))) (i-2 : (uN-fam0 (64))) (v-n : n) (x : idx) (y : idx) → 
    (¬ (Step-read-before-table-copy-zero (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ []))))) →
    (v-n ≡ 0) →
    Step-read-before-table-copy-le (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ [])))
  table-copy-zero-0-4 : ∀ (z : state) (i-1 : (uN-fam0 (32))) (i-2 : (uN-fam0 (32))) (v-n : n) (x : idx) (y : idx) → 
    (¬ (Step-read-before-table-copy-zero (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ []))))) →
    (v-n ≡ 0) →
    Step-read-before-table-copy-le (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ [])))
  table-copy-zero-0-5 : ∀ (z : state) (i-1 : (uN-fam0 (64))) (i-2 : (uN-fam0 (32))) (v-n : n) (x : idx) (y : idx) → 
    (¬ (Step-read-before-table-copy-zero (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ []))))) →
    (v-n ≡ 0) →
    Step-read-before-table-copy-le (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ [])))
  table-copy-zero-0-6 : ∀ (z : state) (i-1 : (uN-fam0 (32))) (i-2 : (uN-fam0 (64))) (v-n : n) (x : idx) (y : idx) → 
    (¬ (Step-read-before-table-copy-zero (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ []))))) →
    (v-n ≡ 0) →
    Step-read-before-table-copy-le (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ [])))
  table-copy-zero-0-7 : ∀ (z : state) (i-1 : (uN-fam0 (64))) (i-2 : (uN-fam0 (64))) (v-n : n) (x : idx) (y : idx) → 
    (¬ (Step-read-before-table-copy-zero (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ []))))) →
    (v-n ≡ 0) →
    Step-read-before-table-copy-le (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ [])))
  table-copy-oob-1-0 : ∀ (z : state) (i-1 : (uN-fam0 (32))) (i-2 : (uN-fam0 (32))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    ((((proj-uN-0 (size (numtype-addrtype I32)) i-1) + v-n) > (length (tableinst-REFS (fun-table z x-1)))) ⊎ (((proj-uN-0 (size (numtype-addrtype I32)) i-2) + v-n) > (length (tableinst-REFS (fun-table z x-2))))) →
    Step-read-before-table-copy-le (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (TABLE-COPY x-1 x-2) ∷ [])))
  table-copy-oob-1-1 : ∀ (z : state) (i-1 : (uN-fam0 (64))) (i-2 : (uN-fam0 (32))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    ((((proj-uN-0 (size (numtype-addrtype I64)) i-1) + v-n) > (length (tableinst-REFS (fun-table z x-1)))) ⊎ (((proj-uN-0 (size (numtype-addrtype I32)) i-2) + v-n) > (length (tableinst-REFS (fun-table z x-2))))) →
    Step-read-before-table-copy-le (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (TABLE-COPY x-1 x-2) ∷ [])))
  table-copy-oob-1-2 : ∀ (z : state) (i-1 : (uN-fam0 (32))) (i-2 : (uN-fam0 (64))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    ((((proj-uN-0 (size (numtype-addrtype I32)) i-1) + v-n) > (length (tableinst-REFS (fun-table z x-1)))) ⊎ (((proj-uN-0 (size (numtype-addrtype I64)) i-2) + v-n) > (length (tableinst-REFS (fun-table z x-2))))) →
    Step-read-before-table-copy-le (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (TABLE-COPY x-1 x-2) ∷ [])))
  table-copy-oob-1-3 : ∀ (z : state) (i-1 : (uN-fam0 (64))) (i-2 : (uN-fam0 (64))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    ((((proj-uN-0 (size (numtype-addrtype I64)) i-1) + v-n) > (length (tableinst-REFS (fun-table z x-1)))) ⊎ (((proj-uN-0 (size (numtype-addrtype I64)) i-2) + v-n) > (length (tableinst-REFS (fun-table z x-2))))) →
    Step-read-before-table-copy-le (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (TABLE-COPY x-1 x-2) ∷ [])))
  table-copy-oob-1-4 : ∀ (z : state) (i-1 : (uN-fam0 (32))) (i-2 : (uN-fam0 (32))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    ((((proj-uN-0 (size (numtype-addrtype I32)) i-1) + v-n) > (length (tableinst-REFS (fun-table z x-1)))) ⊎ (((proj-uN-0 (size (numtype-addrtype I32)) i-2) + v-n) > (length (tableinst-REFS (fun-table z x-2))))) →
    Step-read-before-table-copy-le (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (TABLE-COPY x-1 x-2) ∷ [])))
  table-copy-oob-1-5 : ∀ (z : state) (i-1 : (uN-fam0 (64))) (i-2 : (uN-fam0 (32))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    ((((proj-uN-0 (size (numtype-addrtype I64)) i-1) + v-n) > (length (tableinst-REFS (fun-table z x-1)))) ⊎ (((proj-uN-0 (size (numtype-addrtype I32)) i-2) + v-n) > (length (tableinst-REFS (fun-table z x-2))))) →
    Step-read-before-table-copy-le (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (TABLE-COPY x-1 x-2) ∷ [])))
  table-copy-oob-1-6 : ∀ (z : state) (i-1 : (uN-fam0 (32))) (i-2 : (uN-fam0 (64))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    ((((proj-uN-0 (size (numtype-addrtype I32)) i-1) + v-n) > (length (tableinst-REFS (fun-table z x-1)))) ⊎ (((proj-uN-0 (size (numtype-addrtype I64)) i-2) + v-n) > (length (tableinst-REFS (fun-table z x-2))))) →
    Step-read-before-table-copy-le (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (TABLE-COPY x-1 x-2) ∷ [])))
  table-copy-oob-1-7 : ∀ (z : state) (i-1 : (uN-fam0 (64))) (i-2 : (uN-fam0 (64))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    ((((proj-uN-0 (size (numtype-addrtype I64)) i-1) + v-n) > (length (tableinst-REFS (fun-table z x-1)))) ⊎ (((proj-uN-0 (size (numtype-addrtype I64)) i-2) + v-n) > (length (tableinst-REFS (fun-table z x-2))))) →
    Step-read-before-table-copy-le (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (TABLE-COPY x-1 x-2) ∷ [])))

{- Inductive Relations Definition at: ../specification/wasm-3.0/4.3-execution.instructions.spectec:389.1-393.15 -}
data Step-read-before-table-copy-gt : config → Set where
  table-copy-le-0-0 : ∀ (z : state) (i-1 : (uN-fam0 (32))) (i-2 : (uN-fam0 (32))) (v-n : n) (x : idx) (y : idx) → 
    (¬ (Step-read-before-table-copy-le (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ []))))) →
    ((proj-uN-0 (size (numtype-addrtype I32)) i-1) ≤ (proj-uN-0 (size (numtype-addrtype I32)) i-2)) →
    Step-read-before-table-copy-gt (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ [])))
  table-copy-le-0-1 : ∀ (z : state) (i-1 : (uN-fam0 (64))) (i-2 : (uN-fam0 (32))) (v-n : n) (x : idx) (y : idx) → 
    (¬ (Step-read-before-table-copy-le (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ []))))) →
    ((proj-uN-0 (size (numtype-addrtype I64)) i-1) ≤ (proj-uN-0 (size (numtype-addrtype I32)) i-2)) →
    Step-read-before-table-copy-gt (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ [])))
  table-copy-le-0-2 : ∀ (z : state) (i-1 : (uN-fam0 (32))) (i-2 : (uN-fam0 (64))) (v-n : n) (x : idx) (y : idx) → 
    (¬ (Step-read-before-table-copy-le (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ []))))) →
    ((proj-uN-0 (size (numtype-addrtype I32)) i-1) ≤ (proj-uN-0 (size (numtype-addrtype I64)) i-2)) →
    Step-read-before-table-copy-gt (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ [])))
  table-copy-le-0-3 : ∀ (z : state) (i-1 : (uN-fam0 (64))) (i-2 : (uN-fam0 (64))) (v-n : n) (x : idx) (y : idx) → 
    (¬ (Step-read-before-table-copy-le (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ []))))) →
    ((proj-uN-0 (size (numtype-addrtype I64)) i-1) ≤ (proj-uN-0 (size (numtype-addrtype I64)) i-2)) →
    Step-read-before-table-copy-gt (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ [])))
  table-copy-le-0-4 : ∀ (z : state) (i-1 : (uN-fam0 (32))) (i-2 : (uN-fam0 (32))) (v-n : n) (x : idx) (y : idx) → 
    (¬ (Step-read-before-table-copy-le (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ []))))) →
    ((proj-uN-0 (size (numtype-addrtype I32)) i-1) ≤ (proj-uN-0 (size (numtype-addrtype I32)) i-2)) →
    Step-read-before-table-copy-gt (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ [])))
  table-copy-le-0-5 : ∀ (z : state) (i-1 : (uN-fam0 (64))) (i-2 : (uN-fam0 (32))) (v-n : n) (x : idx) (y : idx) → 
    (¬ (Step-read-before-table-copy-le (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ []))))) →
    ((proj-uN-0 (size (numtype-addrtype I64)) i-1) ≤ (proj-uN-0 (size (numtype-addrtype I32)) i-2)) →
    Step-read-before-table-copy-gt (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ [])))
  table-copy-le-0-6 : ∀ (z : state) (i-1 : (uN-fam0 (32))) (i-2 : (uN-fam0 (64))) (v-n : n) (x : idx) (y : idx) → 
    (¬ (Step-read-before-table-copy-le (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ []))))) →
    ((proj-uN-0 (size (numtype-addrtype I32)) i-1) ≤ (proj-uN-0 (size (numtype-addrtype I64)) i-2)) →
    Step-read-before-table-copy-gt (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ [])))
  table-copy-le-0-7 : ∀ (z : state) (i-1 : (uN-fam0 (64))) (i-2 : (uN-fam0 (64))) (v-n : n) (x : idx) (y : idx) → 
    (¬ (Step-read-before-table-copy-le (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ []))))) →
    ((proj-uN-0 (size (numtype-addrtype I64)) i-1) ≤ (proj-uN-0 (size (numtype-addrtype I64)) i-2)) →
    Step-read-before-table-copy-gt (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ [])))
  table-copy-zero-1-0 : ∀ (z : state) (i-1 : (uN-fam0 (32))) (i-2 : (uN-fam0 (32))) (v-n : n) (x : idx) (y : idx) → 
    (¬ (Step-read-before-table-copy-zero (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ []))))) →
    (v-n ≡ 0) →
    Step-read-before-table-copy-gt (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ [])))
  table-copy-zero-1-1 : ∀ (z : state) (i-1 : (uN-fam0 (64))) (i-2 : (uN-fam0 (32))) (v-n : n) (x : idx) (y : idx) → 
    (¬ (Step-read-before-table-copy-zero (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ []))))) →
    (v-n ≡ 0) →
    Step-read-before-table-copy-gt (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ [])))
  table-copy-zero-1-2 : ∀ (z : state) (i-1 : (uN-fam0 (32))) (i-2 : (uN-fam0 (64))) (v-n : n) (x : idx) (y : idx) → 
    (¬ (Step-read-before-table-copy-zero (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ []))))) →
    (v-n ≡ 0) →
    Step-read-before-table-copy-gt (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ [])))
  table-copy-zero-1-3 : ∀ (z : state) (i-1 : (uN-fam0 (64))) (i-2 : (uN-fam0 (64))) (v-n : n) (x : idx) (y : idx) → 
    (¬ (Step-read-before-table-copy-zero (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ []))))) →
    (v-n ≡ 0) →
    Step-read-before-table-copy-gt (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ [])))
  table-copy-zero-1-4 : ∀ (z : state) (i-1 : (uN-fam0 (32))) (i-2 : (uN-fam0 (32))) (v-n : n) (x : idx) (y : idx) → 
    (¬ (Step-read-before-table-copy-zero (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ []))))) →
    (v-n ≡ 0) →
    Step-read-before-table-copy-gt (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ [])))
  table-copy-zero-1-5 : ∀ (z : state) (i-1 : (uN-fam0 (64))) (i-2 : (uN-fam0 (32))) (v-n : n) (x : idx) (y : idx) → 
    (¬ (Step-read-before-table-copy-zero (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ []))))) →
    (v-n ≡ 0) →
    Step-read-before-table-copy-gt (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ [])))
  table-copy-zero-1-6 : ∀ (z : state) (i-1 : (uN-fam0 (32))) (i-2 : (uN-fam0 (64))) (v-n : n) (x : idx) (y : idx) → 
    (¬ (Step-read-before-table-copy-zero (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ []))))) →
    (v-n ≡ 0) →
    Step-read-before-table-copy-gt (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ [])))
  table-copy-zero-1-7 : ∀ (z : state) (i-1 : (uN-fam0 (64))) (i-2 : (uN-fam0 (64))) (v-n : n) (x : idx) (y : idx) → 
    (¬ (Step-read-before-table-copy-zero (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ []))))) →
    (v-n ≡ 0) →
    Step-read-before-table-copy-gt (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ [])))
  table-copy-oob-2-0 : ∀ (z : state) (i-1 : (uN-fam0 (32))) (i-2 : (uN-fam0 (32))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    ((((proj-uN-0 (size (numtype-addrtype I32)) i-1) + v-n) > (length (tableinst-REFS (fun-table z x-1)))) ⊎ (((proj-uN-0 (size (numtype-addrtype I32)) i-2) + v-n) > (length (tableinst-REFS (fun-table z x-2))))) →
    Step-read-before-table-copy-gt (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (TABLE-COPY x-1 x-2) ∷ [])))
  table-copy-oob-2-1 : ∀ (z : state) (i-1 : (uN-fam0 (64))) (i-2 : (uN-fam0 (32))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    ((((proj-uN-0 (size (numtype-addrtype I64)) i-1) + v-n) > (length (tableinst-REFS (fun-table z x-1)))) ⊎ (((proj-uN-0 (size (numtype-addrtype I32)) i-2) + v-n) > (length (tableinst-REFS (fun-table z x-2))))) →
    Step-read-before-table-copy-gt (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (TABLE-COPY x-1 x-2) ∷ [])))
  table-copy-oob-2-2 : ∀ (z : state) (i-1 : (uN-fam0 (32))) (i-2 : (uN-fam0 (64))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    ((((proj-uN-0 (size (numtype-addrtype I32)) i-1) + v-n) > (length (tableinst-REFS (fun-table z x-1)))) ⊎ (((proj-uN-0 (size (numtype-addrtype I64)) i-2) + v-n) > (length (tableinst-REFS (fun-table z x-2))))) →
    Step-read-before-table-copy-gt (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (TABLE-COPY x-1 x-2) ∷ [])))
  table-copy-oob-2-3 : ∀ (z : state) (i-1 : (uN-fam0 (64))) (i-2 : (uN-fam0 (64))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    ((((proj-uN-0 (size (numtype-addrtype I64)) i-1) + v-n) > (length (tableinst-REFS (fun-table z x-1)))) ⊎ (((proj-uN-0 (size (numtype-addrtype I64)) i-2) + v-n) > (length (tableinst-REFS (fun-table z x-2))))) →
    Step-read-before-table-copy-gt (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (TABLE-COPY x-1 x-2) ∷ [])))
  table-copy-oob-2-4 : ∀ (z : state) (i-1 : (uN-fam0 (32))) (i-2 : (uN-fam0 (32))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    ((((proj-uN-0 (size (numtype-addrtype I32)) i-1) + v-n) > (length (tableinst-REFS (fun-table z x-1)))) ⊎ (((proj-uN-0 (size (numtype-addrtype I32)) i-2) + v-n) > (length (tableinst-REFS (fun-table z x-2))))) →
    Step-read-before-table-copy-gt (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (TABLE-COPY x-1 x-2) ∷ [])))
  table-copy-oob-2-5 : ∀ (z : state) (i-1 : (uN-fam0 (64))) (i-2 : (uN-fam0 (32))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    ((((proj-uN-0 (size (numtype-addrtype I64)) i-1) + v-n) > (length (tableinst-REFS (fun-table z x-1)))) ⊎ (((proj-uN-0 (size (numtype-addrtype I32)) i-2) + v-n) > (length (tableinst-REFS (fun-table z x-2))))) →
    Step-read-before-table-copy-gt (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (TABLE-COPY x-1 x-2) ∷ [])))
  table-copy-oob-2-6 : ∀ (z : state) (i-1 : (uN-fam0 (32))) (i-2 : (uN-fam0 (64))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    ((((proj-uN-0 (size (numtype-addrtype I32)) i-1) + v-n) > (length (tableinst-REFS (fun-table z x-1)))) ⊎ (((proj-uN-0 (size (numtype-addrtype I64)) i-2) + v-n) > (length (tableinst-REFS (fun-table z x-2))))) →
    Step-read-before-table-copy-gt (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (TABLE-COPY x-1 x-2) ∷ [])))
  table-copy-oob-2-7 : ∀ (z : state) (i-1 : (uN-fam0 (64))) (i-2 : (uN-fam0 (64))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    ((((proj-uN-0 (size (numtype-addrtype I64)) i-1) + v-n) > (length (tableinst-REFS (fun-table z x-1)))) ⊎ (((proj-uN-0 (size (numtype-addrtype I64)) i-2) + v-n) > (length (tableinst-REFS (fun-table z x-2))))) →
    Step-read-before-table-copy-gt (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (TABLE-COPY x-1 x-2) ∷ [])))

{- Inductive Relations Definition at: ../specification/wasm-3.0/4.3-execution.instructions.spectec:401.1-404.14 -}
data Step-read-before-table-init-zero : config → Set where
  table-init-oob-0-0 : ∀ (z : state) (i : (uN-fam0 (32))) (j : (uN-fam0 (32))) (v-n : n) (x : idx) (y : idx) → 
    ((((proj-uN-0 (size (numtype-addrtype I32)) i) + v-n) > (length (tableinst-REFS (fun-table z x)))) ⊎ (((proj-uN-0 32 j) + v-n) > (length (eleminst-REFS (fun-elem z y))))) →
    Step-read-before-table-init-zero (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i) ∷ (instr-CONST numtype-I32 j) ∷ (instr-CONST numtype-I32 (mk-uN v-n)) ∷ (TABLE-INIT x y) ∷ [])))
  table-init-oob-0-1 : ∀ (z : state) (i : (uN-fam0 (64))) (j : (uN-fam0 (32))) (v-n : n) (x : idx) (y : idx) → 
    ((((proj-uN-0 (size (numtype-addrtype I64)) i) + v-n) > (length (tableinst-REFS (fun-table z x)))) ⊎ (((proj-uN-0 32 j) + v-n) > (length (eleminst-REFS (fun-elem z y))))) →
    Step-read-before-table-init-zero (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i) ∷ (instr-CONST numtype-I32 j) ∷ (instr-CONST numtype-I32 (mk-uN v-n)) ∷ (TABLE-INIT x y) ∷ [])))

{- Inductive Relations Definition at: ../specification/wasm-3.0/4.3-execution.instructions.spectec:562.1-565.14 -}
data Step-read-before-memory-fill-zero : config → Set where
  memory-fill-oob-0-0 : ∀ (z : state) (i : (uN-fam0 (32))) (v-val : val) (v-n : n) (x : idx) → 
    (((proj-uN-0 (size (numtype-addrtype I32)) i) + v-n) > (length (BYTES (fun-mem z x)))) →
    Step-read-before-memory-fill-zero (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i) ∷ (instr-val v-val) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (MEMORY-FILL x) ∷ [])))
  memory-fill-oob-0-1 : ∀ (z : state) (i : (uN-fam0 (64))) (v-val : val) (v-n : n) (x : idx) → 
    (((proj-uN-0 (size (numtype-addrtype I64)) i) + v-n) > (length (BYTES (fun-mem z x)))) →
    Step-read-before-memory-fill-zero (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i) ∷ (instr-val v-val) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (MEMORY-FILL x) ∷ [])))

{- Inductive Relations Definition at: ../specification/wasm-3.0/4.3-execution.instructions.spectec:579.1-582.14 -}
data Step-read-before-memory-copy-zero : config → Set where
  memory-copy-oob-0-0 : ∀ (z : state) (i-1 : (uN-fam0 (32))) (i-2 : (uN-fam0 (32))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    ((((proj-uN-0 (size (numtype-addrtype I32)) i-1) + v-n) > (length (BYTES (fun-mem z x-1)))) ⊎ (((proj-uN-0 (size (numtype-addrtype I32)) i-2) + v-n) > (length (BYTES (fun-mem z x-2))))) →
    Step-read-before-memory-copy-zero (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (MEMORY-COPY x-1 x-2) ∷ [])))
  memory-copy-oob-0-1 : ∀ (z : state) (i-1 : (uN-fam0 (64))) (i-2 : (uN-fam0 (32))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    ((((proj-uN-0 (size (numtype-addrtype I64)) i-1) + v-n) > (length (BYTES (fun-mem z x-1)))) ⊎ (((proj-uN-0 (size (numtype-addrtype I32)) i-2) + v-n) > (length (BYTES (fun-mem z x-2))))) →
    Step-read-before-memory-copy-zero (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (MEMORY-COPY x-1 x-2) ∷ [])))
  memory-copy-oob-0-2 : ∀ (z : state) (i-1 : (uN-fam0 (32))) (i-2 : (uN-fam0 (64))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    ((((proj-uN-0 (size (numtype-addrtype I32)) i-1) + v-n) > (length (BYTES (fun-mem z x-1)))) ⊎ (((proj-uN-0 (size (numtype-addrtype I64)) i-2) + v-n) > (length (BYTES (fun-mem z x-2))))) →
    Step-read-before-memory-copy-zero (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (MEMORY-COPY x-1 x-2) ∷ [])))
  memory-copy-oob-0-3 : ∀ (z : state) (i-1 : (uN-fam0 (64))) (i-2 : (uN-fam0 (64))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    ((((proj-uN-0 (size (numtype-addrtype I64)) i-1) + v-n) > (length (BYTES (fun-mem z x-1)))) ⊎ (((proj-uN-0 (size (numtype-addrtype I64)) i-2) + v-n) > (length (BYTES (fun-mem z x-2))))) →
    Step-read-before-memory-copy-zero (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (MEMORY-COPY x-1 x-2) ∷ [])))
  memory-copy-oob-0-4 : ∀ (z : state) (i-1 : (uN-fam0 (32))) (i-2 : (uN-fam0 (32))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    ((((proj-uN-0 (size (numtype-addrtype I32)) i-1) + v-n) > (length (BYTES (fun-mem z x-1)))) ⊎ (((proj-uN-0 (size (numtype-addrtype I32)) i-2) + v-n) > (length (BYTES (fun-mem z x-2))))) →
    Step-read-before-memory-copy-zero (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (MEMORY-COPY x-1 x-2) ∷ [])))
  memory-copy-oob-0-5 : ∀ (z : state) (i-1 : (uN-fam0 (64))) (i-2 : (uN-fam0 (32))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    ((((proj-uN-0 (size (numtype-addrtype I64)) i-1) + v-n) > (length (BYTES (fun-mem z x-1)))) ⊎ (((proj-uN-0 (size (numtype-addrtype I32)) i-2) + v-n) > (length (BYTES (fun-mem z x-2))))) →
    Step-read-before-memory-copy-zero (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (MEMORY-COPY x-1 x-2) ∷ [])))
  memory-copy-oob-0-6 : ∀ (z : state) (i-1 : (uN-fam0 (32))) (i-2 : (uN-fam0 (64))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    ((((proj-uN-0 (size (numtype-addrtype I32)) i-1) + v-n) > (length (BYTES (fun-mem z x-1)))) ⊎ (((proj-uN-0 (size (numtype-addrtype I64)) i-2) + v-n) > (length (BYTES (fun-mem z x-2))))) →
    Step-read-before-memory-copy-zero (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (MEMORY-COPY x-1 x-2) ∷ [])))
  memory-copy-oob-0-7 : ∀ (z : state) (i-1 : (uN-fam0 (64))) (i-2 : (uN-fam0 (64))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    ((((proj-uN-0 (size (numtype-addrtype I64)) i-1) + v-n) > (length (BYTES (fun-mem z x-1)))) ⊎ (((proj-uN-0 (size (numtype-addrtype I64)) i-2) + v-n) > (length (BYTES (fun-mem z x-2))))) →
    Step-read-before-memory-copy-zero (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (MEMORY-COPY x-1 x-2) ∷ [])))

{- Inductive Relations Definition at: ../specification/wasm-3.0/4.3-execution.instructions.spectec:584.1-589.19 -}
data Step-read-before-memory-copy-le : config → Set where
  memory-copy-zero-0-0 : ∀ (z : state) (i-1 : (uN-fam0 (32))) (i-2 : (uN-fam0 (32))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    (¬ (Step-read-before-memory-copy-zero (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (MEMORY-COPY x-1 x-2) ∷ []))))) →
    (v-n ≡ 0) →
    Step-read-before-memory-copy-le (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (MEMORY-COPY x-1 x-2) ∷ [])))
  memory-copy-zero-0-1 : ∀ (z : state) (i-1 : (uN-fam0 (64))) (i-2 : (uN-fam0 (32))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    (¬ (Step-read-before-memory-copy-zero (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (MEMORY-COPY x-1 x-2) ∷ []))))) →
    (v-n ≡ 0) →
    Step-read-before-memory-copy-le (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (MEMORY-COPY x-1 x-2) ∷ [])))
  memory-copy-zero-0-2 : ∀ (z : state) (i-1 : (uN-fam0 (32))) (i-2 : (uN-fam0 (64))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    (¬ (Step-read-before-memory-copy-zero (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (MEMORY-COPY x-1 x-2) ∷ []))))) →
    (v-n ≡ 0) →
    Step-read-before-memory-copy-le (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (MEMORY-COPY x-1 x-2) ∷ [])))
  memory-copy-zero-0-3 : ∀ (z : state) (i-1 : (uN-fam0 (64))) (i-2 : (uN-fam0 (64))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    (¬ (Step-read-before-memory-copy-zero (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (MEMORY-COPY x-1 x-2) ∷ []))))) →
    (v-n ≡ 0) →
    Step-read-before-memory-copy-le (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (MEMORY-COPY x-1 x-2) ∷ [])))
  memory-copy-zero-0-4 : ∀ (z : state) (i-1 : (uN-fam0 (32))) (i-2 : (uN-fam0 (32))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    (¬ (Step-read-before-memory-copy-zero (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (MEMORY-COPY x-1 x-2) ∷ []))))) →
    (v-n ≡ 0) →
    Step-read-before-memory-copy-le (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (MEMORY-COPY x-1 x-2) ∷ [])))
  memory-copy-zero-0-5 : ∀ (z : state) (i-1 : (uN-fam0 (64))) (i-2 : (uN-fam0 (32))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    (¬ (Step-read-before-memory-copy-zero (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (MEMORY-COPY x-1 x-2) ∷ []))))) →
    (v-n ≡ 0) →
    Step-read-before-memory-copy-le (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (MEMORY-COPY x-1 x-2) ∷ [])))
  memory-copy-zero-0-6 : ∀ (z : state) (i-1 : (uN-fam0 (32))) (i-2 : (uN-fam0 (64))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    (¬ (Step-read-before-memory-copy-zero (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (MEMORY-COPY x-1 x-2) ∷ []))))) →
    (v-n ≡ 0) →
    Step-read-before-memory-copy-le (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (MEMORY-COPY x-1 x-2) ∷ [])))
  memory-copy-zero-0-7 : ∀ (z : state) (i-1 : (uN-fam0 (64))) (i-2 : (uN-fam0 (64))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    (¬ (Step-read-before-memory-copy-zero (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (MEMORY-COPY x-1 x-2) ∷ []))))) →
    (v-n ≡ 0) →
    Step-read-before-memory-copy-le (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (MEMORY-COPY x-1 x-2) ∷ [])))
  memory-copy-oob-1-0 : ∀ (z : state) (i-1 : (uN-fam0 (32))) (i-2 : (uN-fam0 (32))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    ((((proj-uN-0 (size (numtype-addrtype I32)) i-1) + v-n) > (length (BYTES (fun-mem z x-1)))) ⊎ (((proj-uN-0 (size (numtype-addrtype I32)) i-2) + v-n) > (length (BYTES (fun-mem z x-2))))) →
    Step-read-before-memory-copy-le (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (MEMORY-COPY x-1 x-2) ∷ [])))
  memory-copy-oob-1-1 : ∀ (z : state) (i-1 : (uN-fam0 (64))) (i-2 : (uN-fam0 (32))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    ((((proj-uN-0 (size (numtype-addrtype I64)) i-1) + v-n) > (length (BYTES (fun-mem z x-1)))) ⊎ (((proj-uN-0 (size (numtype-addrtype I32)) i-2) + v-n) > (length (BYTES (fun-mem z x-2))))) →
    Step-read-before-memory-copy-le (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (MEMORY-COPY x-1 x-2) ∷ [])))
  memory-copy-oob-1-2 : ∀ (z : state) (i-1 : (uN-fam0 (32))) (i-2 : (uN-fam0 (64))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    ((((proj-uN-0 (size (numtype-addrtype I32)) i-1) + v-n) > (length (BYTES (fun-mem z x-1)))) ⊎ (((proj-uN-0 (size (numtype-addrtype I64)) i-2) + v-n) > (length (BYTES (fun-mem z x-2))))) →
    Step-read-before-memory-copy-le (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (MEMORY-COPY x-1 x-2) ∷ [])))
  memory-copy-oob-1-3 : ∀ (z : state) (i-1 : (uN-fam0 (64))) (i-2 : (uN-fam0 (64))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    ((((proj-uN-0 (size (numtype-addrtype I64)) i-1) + v-n) > (length (BYTES (fun-mem z x-1)))) ⊎ (((proj-uN-0 (size (numtype-addrtype I64)) i-2) + v-n) > (length (BYTES (fun-mem z x-2))))) →
    Step-read-before-memory-copy-le (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (MEMORY-COPY x-1 x-2) ∷ [])))
  memory-copy-oob-1-4 : ∀ (z : state) (i-1 : (uN-fam0 (32))) (i-2 : (uN-fam0 (32))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    ((((proj-uN-0 (size (numtype-addrtype I32)) i-1) + v-n) > (length (BYTES (fun-mem z x-1)))) ⊎ (((proj-uN-0 (size (numtype-addrtype I32)) i-2) + v-n) > (length (BYTES (fun-mem z x-2))))) →
    Step-read-before-memory-copy-le (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (MEMORY-COPY x-1 x-2) ∷ [])))
  memory-copy-oob-1-5 : ∀ (z : state) (i-1 : (uN-fam0 (64))) (i-2 : (uN-fam0 (32))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    ((((proj-uN-0 (size (numtype-addrtype I64)) i-1) + v-n) > (length (BYTES (fun-mem z x-1)))) ⊎ (((proj-uN-0 (size (numtype-addrtype I32)) i-2) + v-n) > (length (BYTES (fun-mem z x-2))))) →
    Step-read-before-memory-copy-le (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (MEMORY-COPY x-1 x-2) ∷ [])))
  memory-copy-oob-1-6 : ∀ (z : state) (i-1 : (uN-fam0 (32))) (i-2 : (uN-fam0 (64))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    ((((proj-uN-0 (size (numtype-addrtype I32)) i-1) + v-n) > (length (BYTES (fun-mem z x-1)))) ⊎ (((proj-uN-0 (size (numtype-addrtype I64)) i-2) + v-n) > (length (BYTES (fun-mem z x-2))))) →
    Step-read-before-memory-copy-le (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (MEMORY-COPY x-1 x-2) ∷ [])))
  memory-copy-oob-1-7 : ∀ (z : state) (i-1 : (uN-fam0 (64))) (i-2 : (uN-fam0 (64))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    ((((proj-uN-0 (size (numtype-addrtype I64)) i-1) + v-n) > (length (BYTES (fun-mem z x-1)))) ⊎ (((proj-uN-0 (size (numtype-addrtype I64)) i-2) + v-n) > (length (BYTES (fun-mem z x-2))))) →
    Step-read-before-memory-copy-le (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (MEMORY-COPY x-1 x-2) ∷ [])))

{- Inductive Relations Definition at: ../specification/wasm-3.0/4.3-execution.instructions.spectec:603.1-606.14 -}
data Step-read-before-memory-init-zero : config → Set where
  memory-init-oob-0-0 : ∀ (z : state) (i : (uN-fam0 (32))) (j : (uN-fam0 (32))) (v-n : n) (x : idx) (y : idx) → 
    ((((proj-uN-0 (size (numtype-addrtype I32)) i) + v-n) > (length (BYTES (fun-mem z x)))) ⊎ (((proj-uN-0 32 j) + v-n) > (length (datainst-BYTES (fun-data z y))))) →
    Step-read-before-memory-init-zero (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i) ∷ (instr-CONST numtype-I32 j) ∷ (instr-CONST numtype-I32 (mk-uN v-n)) ∷ (MEMORY-INIT x y) ∷ [])))
  memory-init-oob-0-1 : ∀ (z : state) (i : (uN-fam0 (64))) (j : (uN-fam0 (32))) (v-n : n) (x : idx) (y : idx) → 
    ((((proj-uN-0 (size (numtype-addrtype I64)) i) + v-n) > (length (BYTES (fun-mem z x)))) ⊎ (((proj-uN-0 32 j) + v-n) > (length (datainst-BYTES (fun-data z y))))) →
    Step-read-before-memory-init-zero (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i) ∷ (instr-CONST numtype-I32 j) ∷ (instr-CONST numtype-I32 (mk-uN v-n)) ∷ (MEMORY-INIT x y) ∷ [])))

{- Inductive Relations Definition at: ../specification/wasm-3.0/4.3-execution.instructions.spectec:667.1-669.15 -}
data Step-read-before-ref-test-false : config → Set where
  ref-test-true-0 : ∀ (s : store) (f : frame) (v-ref : ref) (rt : reftype) → 
    (Ref-ok s v-ref (inst-reftype (MODULE f) rt)) →
    Step-read-before-ref-test-false (mk-config (mk-state s f) (as (List instr) ((instr-ref v-ref) ∷ (REF-TEST rt) ∷ [])))

{- Inductive Relations Definition at: ../specification/wasm-3.0/4.3-execution.instructions.spectec:676.1-678.15 -}
data Step-read-before-ref-cast-fail : config → Set where
  ref-cast-succeed-0 : ∀ (s : store) (f : frame) (v-ref : ref) (rt : reftype) → 
    (Ref-ok s v-ref (inst-reftype (MODULE f) rt)) →
    Step-read-before-ref-cast-fail (mk-config (mk-state s f) (as (List instr) ((instr-ref v-ref) ∷ (REF-CAST rt) ∷ [])))

{- Inductive Relations Definition at: ../specification/wasm-3.0/4.3-execution.instructions.spectec:804.1-807.14 -}
data Step-read-before-array-fill-zero : config → Set where
  array-fill-oob-0 : ∀ (z : state) (a : addr) (i : (uN-fam0 (32))) (v-val : val) (v-n : n) (x : idx) → 
    (a < (length (fun-arrayinst z))) →
    (((proj-uN-0 32 i) + v-n) > (length (arrayinst-FIELDS ((fun-arrayinst z) [ a ]!)))) →
    Step-read-before-array-fill-zero (mk-config z (as (List instr) ((instr-REF-ARRAY-ADDR a) ∷ (instr-CONST numtype-I32 i) ∷ (instr-val v-val) ∷ (instr-CONST numtype-I32 (mk-uN v-n)) ∷ (ARRAY-FILL x) ∷ [])))

{- Inductive Relations Definition at: ../specification/wasm-3.0/4.3-execution.instructions.spectec:831.1-835.14 -}
data Step-read-before-array-copy-zero : config → Set where
  array-copy-oob2-0 : ∀ (z : state) (a-1 : addr) (i-1 : (uN-fam0 (32))) (a-2 : addr) (i-2 : (uN-fam0 (32))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    (a-2 < (length (fun-arrayinst z))) →
    (((proj-uN-0 32 i-2) + v-n) > (length (arrayinst-FIELDS ((fun-arrayinst z) [ a-2 ]!)))) →
    Step-read-before-array-copy-zero (mk-config z (as (List instr) ((instr-REF-ARRAY-ADDR a-1) ∷ (instr-CONST numtype-I32 i-1) ∷ (instr-REF-ARRAY-ADDR a-2) ∷ (instr-CONST numtype-I32 i-2) ∷ (instr-CONST numtype-I32 (mk-uN v-n)) ∷ (ARRAY-COPY x-1 x-2) ∷ [])))
  array-copy-oob1-0 : ∀ (z : state) (a-1 : addr) (i-1 : (uN-fam0 (32))) (a-2 : addr) (i-2 : (uN-fam0 (32))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    (a-1 < (length (fun-arrayinst z))) →
    (((proj-uN-0 32 i-1) + v-n) > (length (arrayinst-FIELDS ((fun-arrayinst z) [ a-1 ]!)))) →
    Step-read-before-array-copy-zero (mk-config z (as (List instr) ((instr-REF-ARRAY-ADDR a-1) ∷ (instr-CONST numtype-I32 i-1) ∷ (instr-REF-ARRAY-ADDR a-2) ∷ (instr-CONST numtype-I32 i-2) ∷ (instr-CONST numtype-I32 (mk-uN v-n)) ∷ (ARRAY-COPY x-1 x-2) ∷ [])))

{- Inductive Relations Definition at: ../specification/wasm-3.0/4.3-execution.instructions.spectec:837.1-847.24 -}
data Step-read-before-array-copy-le : config → Set where
  array-copy-zero-0 : ∀ (z : state) (a-1 : addr) (i-1 : (uN-fam0 (32))) (a-2 : addr) (i-2 : (uN-fam0 (32))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    (¬ (Step-read-before-array-copy-zero (mk-config z (as (List instr) ((instr-REF-ARRAY-ADDR a-1) ∷ (instr-CONST numtype-I32 i-1) ∷ (instr-REF-ARRAY-ADDR a-2) ∷ (instr-CONST numtype-I32 i-2) ∷ (instr-CONST numtype-I32 (mk-uN v-n)) ∷ (ARRAY-COPY x-1 x-2) ∷ []))))) →
    (v-n ≡ 0) →
    Step-read-before-array-copy-le (mk-config z (as (List instr) ((instr-REF-ARRAY-ADDR a-1) ∷ (instr-CONST numtype-I32 i-1) ∷ (instr-REF-ARRAY-ADDR a-2) ∷ (instr-CONST numtype-I32 i-2) ∷ (instr-CONST numtype-I32 (mk-uN v-n)) ∷ (ARRAY-COPY x-1 x-2) ∷ [])))
  array-copy-oob2-1 : ∀ (z : state) (a-1 : addr) (i-1 : (uN-fam0 (32))) (a-2 : addr) (i-2 : (uN-fam0 (32))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    (a-2 < (length (fun-arrayinst z))) →
    (((proj-uN-0 32 i-2) + v-n) > (length (arrayinst-FIELDS ((fun-arrayinst z) [ a-2 ]!)))) →
    Step-read-before-array-copy-le (mk-config z (as (List instr) ((instr-REF-ARRAY-ADDR a-1) ∷ (instr-CONST numtype-I32 i-1) ∷ (instr-REF-ARRAY-ADDR a-2) ∷ (instr-CONST numtype-I32 i-2) ∷ (instr-CONST numtype-I32 (mk-uN v-n)) ∷ (ARRAY-COPY x-1 x-2) ∷ [])))
  array-copy-oob1-1 : ∀ (z : state) (a-1 : addr) (i-1 : (uN-fam0 (32))) (a-2 : addr) (i-2 : (uN-fam0 (32))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    (a-1 < (length (fun-arrayinst z))) →
    (((proj-uN-0 32 i-1) + v-n) > (length (arrayinst-FIELDS ((fun-arrayinst z) [ a-1 ]!)))) →
    Step-read-before-array-copy-le (mk-config z (as (List instr) ((instr-REF-ARRAY-ADDR a-1) ∷ (instr-CONST numtype-I32 i-1) ∷ (instr-REF-ARRAY-ADDR a-2) ∷ (instr-CONST numtype-I32 i-2) ∷ (instr-CONST numtype-I32 (mk-uN v-n)) ∷ (ARRAY-COPY x-1 x-2) ∷ [])))

{- Inductive Relations Definition at: ../specification/wasm-3.0/4.3-execution.instructions.spectec:849.1-858.24 -}
data Step-read-before-array-copy-gt : config → Set where
  array-copy-le-0 : ∀ (z : state) (a-1 : addr) (i-1 : (uN-fam0 (32))) (a-2 : addr) (i-2 : (uN-fam0 (32))) (v-n : n) (x-1 : idx) (x-2 : idx) (sx-opt : (Maybe sx)) (mut-opt : (Maybe mut)) (zt-2 : storagetype) (o0 : (Maybe sx)) → 
    ((fun-sx zt-2) ≡ (just o0)) →
    (¬ (Step-read-before-array-copy-le (mk-config z (as (List instr) ((instr-REF-ARRAY-ADDR a-1) ∷ (instr-CONST numtype-I32 i-1) ∷ (instr-REF-ARRAY-ADDR a-2) ∷ (instr-CONST numtype-I32 i-2) ∷ (instr-CONST numtype-I32 (mk-uN v-n)) ∷ (ARRAY-COPY x-1 x-2) ∷ []))))) →
    (Expand (fun-type z x-2) (comptype-ARRAY (mk-fieldtype mut-opt zt-2))) →
    (((proj-uN-0 32 i-1) ≤ (proj-uN-0 32 i-2)) × (sx-opt ≡ o0)) →
    Step-read-before-array-copy-gt (mk-config z (as (List instr) ((instr-REF-ARRAY-ADDR a-1) ∷ (instr-CONST numtype-I32 i-1) ∷ (instr-REF-ARRAY-ADDR a-2) ∷ (instr-CONST numtype-I32 i-2) ∷ (instr-CONST numtype-I32 (mk-uN v-n)) ∷ (ARRAY-COPY x-1 x-2) ∷ [])))
  array-copy-zero-1 : ∀ (z : state) (a-1 : addr) (i-1 : (uN-fam0 (32))) (a-2 : addr) (i-2 : (uN-fam0 (32))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    (¬ (Step-read-before-array-copy-zero (mk-config z (as (List instr) ((instr-REF-ARRAY-ADDR a-1) ∷ (instr-CONST numtype-I32 i-1) ∷ (instr-REF-ARRAY-ADDR a-2) ∷ (instr-CONST numtype-I32 i-2) ∷ (instr-CONST numtype-I32 (mk-uN v-n)) ∷ (ARRAY-COPY x-1 x-2) ∷ []))))) →
    (v-n ≡ 0) →
    Step-read-before-array-copy-gt (mk-config z (as (List instr) ((instr-REF-ARRAY-ADDR a-1) ∷ (instr-CONST numtype-I32 i-1) ∷ (instr-REF-ARRAY-ADDR a-2) ∷ (instr-CONST numtype-I32 i-2) ∷ (instr-CONST numtype-I32 (mk-uN v-n)) ∷ (ARRAY-COPY x-1 x-2) ∷ [])))
  array-copy-oob2-2 : ∀ (z : state) (a-1 : addr) (i-1 : (uN-fam0 (32))) (a-2 : addr) (i-2 : (uN-fam0 (32))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    (a-2 < (length (fun-arrayinst z))) →
    (((proj-uN-0 32 i-2) + v-n) > (length (arrayinst-FIELDS ((fun-arrayinst z) [ a-2 ]!)))) →
    Step-read-before-array-copy-gt (mk-config z (as (List instr) ((instr-REF-ARRAY-ADDR a-1) ∷ (instr-CONST numtype-I32 i-1) ∷ (instr-REF-ARRAY-ADDR a-2) ∷ (instr-CONST numtype-I32 i-2) ∷ (instr-CONST numtype-I32 (mk-uN v-n)) ∷ (ARRAY-COPY x-1 x-2) ∷ [])))
  array-copy-oob1-2 : ∀ (z : state) (a-1 : addr) (i-1 : (uN-fam0 (32))) (a-2 : addr) (i-2 : (uN-fam0 (32))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    (a-1 < (length (fun-arrayinst z))) →
    (((proj-uN-0 32 i-1) + v-n) > (length (arrayinst-FIELDS ((fun-arrayinst z) [ a-1 ]!)))) →
    Step-read-before-array-copy-gt (mk-config z (as (List instr) ((instr-REF-ARRAY-ADDR a-1) ∷ (instr-CONST numtype-I32 i-1) ∷ (instr-REF-ARRAY-ADDR a-2) ∷ (instr-CONST numtype-I32 i-2) ∷ (instr-CONST numtype-I32 (mk-uN v-n)) ∷ (ARRAY-COPY x-1 x-2) ∷ [])))

{- Inductive Relations Definition at: ../specification/wasm-3.0/4.3-execution.instructions.spectec:874.1-878.14 -}
data Step-read-before-array-init-elem-zero : config → Set where
  array-init-elem-oob2-0 : ∀ (z : state) (a : addr) (i : (uN-fam0 (32))) (j : (uN-fam0 (32))) (v-n : n) (x : idx) (y : idx) → 
    (((proj-uN-0 32 j) + v-n) > (length (eleminst-REFS (fun-elem z y)))) →
    Step-read-before-array-init-elem-zero (mk-config z (as (List instr) ((instr-REF-ARRAY-ADDR a) ∷ (instr-CONST numtype-I32 i) ∷ (instr-CONST numtype-I32 j) ∷ (instr-CONST numtype-I32 (mk-uN v-n)) ∷ (ARRAY-INIT-ELEM x y) ∷ [])))
  array-init-elem-oob1-0 : ∀ (z : state) (a : addr) (i : (uN-fam0 (32))) (j : (uN-fam0 (32))) (v-n : n) (x : idx) (y : idx) → 
    (a < (length (fun-arrayinst z))) →
    (((proj-uN-0 32 i) + v-n) > (length (arrayinst-FIELDS ((fun-arrayinst z) [ a ]!)))) →
    Step-read-before-array-init-elem-zero (mk-config z (as (List instr) ((instr-REF-ARRAY-ADDR a) ∷ (instr-CONST numtype-I32 i) ∷ (instr-CONST numtype-I32 j) ∷ (instr-CONST numtype-I32 (mk-uN v-n)) ∷ (ARRAY-INIT-ELEM x y) ∷ [])))

{- Inductive Relations Definition at: ../specification/wasm-3.0/4.3-execution.instructions.spectec:903.1-907.14 -}
data Step-read-before-array-init-data-zero : config → Set where
  array-init-data-oob2-0 : ∀ (z : state) (a : addr) (i : (uN-fam0 (32))) (j : (uN-fam0 (32))) (v-n : n) (x : idx) (y : idx) (mut-opt : (Maybe mut)) (zt : storagetype) → 
    (Expand (fun-type z x) (comptype-ARRAY (mk-fieldtype mut-opt zt))) →
    ((zsize zt) ≢ nothing) →
    (((proj-uN-0 32 j) + (coerce {B = ℕ} ((coerce {B = ℕ} (v-n * (unwrap! (zsize zt)))) / (coerce {B = ℕ} 8)))) > (length (datainst-BYTES (fun-data z y)))) →
    Step-read-before-array-init-data-zero (mk-config z (as (List instr) ((instr-REF-ARRAY-ADDR a) ∷ (instr-CONST numtype-I32 i) ∷ (instr-CONST numtype-I32 j) ∷ (instr-CONST numtype-I32 (mk-uN v-n)) ∷ (ARRAY-INIT-DATA x y) ∷ [])))
  array-init-data-oob1-0 : ∀ (z : state) (a : addr) (i : (uN-fam0 (32))) (j : (uN-fam0 (32))) (v-n : n) (x : idx) (y : idx) → 
    (a < (length (fun-arrayinst z))) →
    (((proj-uN-0 32 i) + v-n) > (length (arrayinst-FIELDS ((fun-arrayinst z) [ a ]!)))) →
    Step-read-before-array-init-data-zero (mk-config z (as (List instr) ((instr-REF-ARRAY-ADDR a) ∷ (instr-CONST numtype-I32 i) ∷ (instr-CONST numtype-I32 j) ∷ (instr-CONST numtype-I32 (mk-uN v-n)) ∷ (ARRAY-INIT-DATA x y) ∷ [])))

{- Inductive Relations Definition at: ../specification/wasm-3.0/4.3-execution.instructions.spectec:910.1-917.62 -}
data Step-read-before-array-init-data-num : config → Set where
  array-init-data-zero-0 : ∀ (z : state) (a : addr) (i : (uN-fam0 (32))) (j : (uN-fam0 (32))) (v-n : n) (x : idx) (y : idx) → 
    (¬ (Step-read-before-array-init-data-zero (mk-config z (as (List instr) ((instr-REF-ARRAY-ADDR a) ∷ (instr-CONST numtype-I32 i) ∷ (instr-CONST numtype-I32 j) ∷ (instr-CONST numtype-I32 (mk-uN v-n)) ∷ (ARRAY-INIT-DATA x y) ∷ []))))) →
    (v-n ≡ 0) →
    Step-read-before-array-init-data-num (mk-config z (as (List instr) ((instr-REF-ARRAY-ADDR a) ∷ (instr-CONST numtype-I32 i) ∷ (instr-CONST numtype-I32 j) ∷ (instr-CONST numtype-I32 (mk-uN v-n)) ∷ (ARRAY-INIT-DATA x y) ∷ [])))
  array-init-data-oob2-1 : ∀ (z : state) (a : addr) (i : (uN-fam0 (32))) (j : (uN-fam0 (32))) (v-n : n) (x : idx) (y : idx) (mut-opt : (Maybe mut)) (zt : storagetype) → 
    (Expand (fun-type z x) (comptype-ARRAY (mk-fieldtype mut-opt zt))) →
    ((zsize zt) ≢ nothing) →
    (((proj-uN-0 32 j) + (coerce {B = ℕ} ((coerce {B = ℕ} (v-n * (unwrap! (zsize zt)))) / (coerce {B = ℕ} 8)))) > (length (datainst-BYTES (fun-data z y)))) →
    Step-read-before-array-init-data-num (mk-config z (as (List instr) ((instr-REF-ARRAY-ADDR a) ∷ (instr-CONST numtype-I32 i) ∷ (instr-CONST numtype-I32 j) ∷ (instr-CONST numtype-I32 (mk-uN v-n)) ∷ (ARRAY-INIT-DATA x y) ∷ [])))
  array-init-data-oob1-1 : ∀ (z : state) (a : addr) (i : (uN-fam0 (32))) (j : (uN-fam0 (32))) (v-n : n) (x : idx) (y : idx) → 
    (a < (length (fun-arrayinst z))) →
    (((proj-uN-0 32 i) + v-n) > (length (arrayinst-FIELDS ((fun-arrayinst z) [ a ]!)))) →
    Step-read-before-array-init-data-num (mk-config z (as (List instr) ((instr-REF-ARRAY-ADDR a) ∷ (instr-CONST numtype-I32 i) ∷ (instr-CONST numtype-I32 j) ∷ (instr-CONST numtype-I32 (mk-uN v-n)) ∷ (ARRAY-INIT-DATA x y) ∷ [])))

{- Inductive Relations Definition at: ../specification/wasm-3.0/4.3-execution.instructions.spectec:7.1-7.88 -}
data Step-read : config → (List instr) → Set where
  Step-read--block : ∀ (z : state) (v-m : m) (val-lst : (List val)) (bt : blocktype) (instr-lst : (List instr)) (v-n : n) (t-1-lst : (List valtype)) (t-2-lst : (List valtype)) → 
    ((length (val-lst)) ≡ (v-m)) →
    ((length (t-2-lst)) ≡ (v-n)) →
    ((length (t-1-lst)) ≡ (v-m)) →
    ((blocktype- z bt) ≡ (mk-instrtype (mk-list t-1-lst) [] (mk-list t-2-lst))) →
    Step-read (mk-config z ((map (λ (v-val : val) → (instr-val v-val)) val-lst) ++ (as (List instr) ((BLOCK bt instr-lst) ∷ [])))) (as (List instr) ((LABEL- v-n [] ((map (λ (v-val : val) → (instr-val v-val)) val-lst) ++ instr-lst)) ∷ []))
  Step-read--loop : ∀ (z : state) (v-m : m) (val-lst : (List val)) (bt : blocktype) (instr-lst : (List instr)) (t-1-lst : (List valtype)) (v-n : n) (t-2-lst : (List valtype)) → 
    ((length (val-lst)) ≡ (v-m)) →
    ((length (t-2-lst)) ≡ (v-n)) →
    ((length (t-1-lst)) ≡ (v-m)) →
    ((blocktype- z bt) ≡ (mk-instrtype (mk-list t-1-lst) [] (mk-list t-2-lst))) →
    Step-read (mk-config z ((map (λ (v-val : val) → (instr-val v-val)) val-lst) ++ (as (List instr) ((LOOP bt instr-lst) ∷ [])))) (as (List instr) ((LABEL- v-m (as (List instr) ((LOOP bt instr-lst) ∷ [])) ((map (λ (v-val : val) → (instr-val v-val)) val-lst) ++ instr-lst)) ∷ []))
  br-on-cast-succeed : ∀ (s : store) (f : frame) (v-ref : ref) (l : labelidx) (rt-1 : reftype) (rt-2 : reftype) → 
    (Ref-ok s v-ref (inst-reftype (MODULE f) rt-2)) →
    Step-read (mk-config (mk-state s f) (as (List instr) ((instr-ref v-ref) ∷ (BR-ON-CAST l rt-1 rt-2) ∷ []))) (as (List instr) ((instr-ref v-ref) ∷ (BR l) ∷ []))
  Step-read--br-on-cast-fail : ∀ (s : store) (f : frame) (v-ref : ref) (l : labelidx) (rt-1 : reftype) (rt-2 : reftype) → 
    (¬ (Step-read-before-br-on-cast-fail (mk-config (mk-state s f) (as (List instr) ((instr-ref v-ref) ∷ (BR-ON-CAST l rt-1 rt-2) ∷ []))))) →
    Step-read (mk-config (mk-state s f) (as (List instr) ((instr-ref v-ref) ∷ (BR-ON-CAST l rt-1 rt-2) ∷ []))) ((instr-ref v-ref) ∷ [])
  br-on-cast-fail-succeed : ∀ (s : store) (f : frame) (v-ref : ref) (l : labelidx) (rt-1 : reftype) (rt-2 : reftype) → 
    (Ref-ok s v-ref (inst-reftype (MODULE f) rt-2)) →
    Step-read (mk-config (mk-state s f) (as (List instr) ((instr-ref v-ref) ∷ (BR-ON-CAST-FAIL l rt-1 rt-2) ∷ []))) ((instr-ref v-ref) ∷ [])
  br-on-cast-fail-fail : ∀ (s : store) (f : frame) (v-ref : ref) (l : labelidx) (rt-1 : reftype) (rt-2 : reftype) → 
    (¬ (Step-read-before-br-on-cast-fail-fail (mk-config (mk-state s f) (as (List instr) ((instr-ref v-ref) ∷ (BR-ON-CAST-FAIL l rt-1 rt-2) ∷ []))))) →
    Step-read (mk-config (mk-state s f) (as (List instr) ((instr-ref v-ref) ∷ (BR-ON-CAST-FAIL l rt-1 rt-2) ∷ []))) (as (List instr) ((instr-ref v-ref) ∷ (BR l) ∷ []))
  Step-read--call : ∀ (z : state) (x : idx) (a : addr) → 
    (a < (length (fun-funcinst z))) →
    ((proj-uN-0 32 x) < (length (moduleinst-FUNCS (fun-moduleinst z)))) →
    (((moduleinst-FUNCS (fun-moduleinst z)) [ (proj-uN-0 32 x) ]!) ≡ a) →
    Step-read (mk-config z (as (List instr) ((CALL x) ∷ []))) (as (List instr) ((instr-REF-FUNC-ADDR a) ∷ (CALL-REF (typeuse-deftype (funcinst-TYPE ((fun-funcinst z) [ a ]!)))) ∷ []))
  call-ref-null : ∀ (z : state) (yy : typeuse) → Step-read (mk-config z (as (List instr) (instr-REF-NULL-ADDR ∷ (CALL-REF yy) ∷ []))) (as (List instr) (TRAP ∷ []))
  call-ref-func : ∀ (z : state) (v-n : n) (val-lst : (List val)) (a : addr) (yy : typeuse) (v-m : m) (f : frame) (instr-lst : (List instr)) (fi : funcinst) (t-1-lst : (List valtype)) (t-2-lst : (List valtype)) (x : idx) (t-lst : (List valtype)) (o0 : (List (Maybe val))) → 
    ((length (val-lst)) ≡ (v-n)) →
    ((length (t-2-lst)) ≡ (v-m)) →
    ((length (t-1-lst)) ≡ (v-n)) →
    ((length t-lst) ≡ (length o0)) →
    Forall₂ (λ (t : valtype) (o0 : (Maybe val)) → ((default- t) ≡ (just o0))) t-lst o0 →
    (a < (length (fun-funcinst z))) →
    (((fun-funcinst z) [ a ]!) ≡ fi) →
    (Expand (funcinst-TYPE fi) (comptype-FUNC (mk-list t-1-lst) (mk-list t-2-lst))) →
    ((CODE fi) ≡ (funccode-FUNC x (map (λ (t : valtype) → (LOCAL t)) t-lst) instr-lst)) →
    (f ≡ record { frame-LOCALS = ((map (λ (v-val : val) → (just v-val)) val-lst) ++ o0) ; MODULE = (funcinst-MODULE fi) }) →
    Step-read (mk-config z ((map (λ (v-val : val) → (instr-val v-val)) val-lst) ++ (as (List instr) ((instr-REF-FUNC-ADDR a) ∷ (CALL-REF yy) ∷ [])))) (as (List instr) ((FRAME- v-m f (as (List instr) ((LABEL- v-m [] instr-lst) ∷ []))) ∷ []))
  Step-read--return-call : ∀ (z : state) (x : idx) (a : addr) → 
    (a < (length (fun-funcinst z))) →
    ((proj-uN-0 32 x) < (length (moduleinst-FUNCS (fun-moduleinst z)))) →
    (((moduleinst-FUNCS (fun-moduleinst z)) [ (proj-uN-0 32 x) ]!) ≡ a) →
    Step-read (mk-config z (as (List instr) ((RETURN-CALL x) ∷ []))) (as (List instr) ((instr-REF-FUNC-ADDR a) ∷ (RETURN-CALL-REF (typeuse-deftype (funcinst-TYPE ((fun-funcinst z) [ a ]!)))) ∷ []))
  return-call-ref-label : ∀ (z : state) (k : n) (instr'-lst : (List instr)) (val-lst : (List val)) (yy : typeuse) (instr-lst : (List instr)) → Step-read (mk-config z (as (List instr) ((LABEL- k instr'-lst (((map (λ (v-val : val) → (instr-val v-val)) val-lst) ++ (as (List instr) ((RETURN-CALL-REF yy) ∷ []))) ++ instr-lst)) ∷ []))) ((map (λ (v-val : val) → (instr-val v-val)) val-lst) ++ (as (List instr) ((RETURN-CALL-REF yy) ∷ [])))
  return-call-ref-handler : ∀ (z : state) (k : n) (catch-lst : (List catch)) (val-lst : (List val)) (yy : typeuse) (instr-lst : (List instr)) → Step-read (mk-config z (as (List instr) ((HANDLER- k catch-lst (((map (λ (v-val : val) → (instr-val v-val)) val-lst) ++ (as (List instr) ((RETURN-CALL-REF yy) ∷ []))) ++ instr-lst)) ∷ []))) ((map (λ (v-val : val) → (instr-val v-val)) val-lst) ++ (as (List instr) ((RETURN-CALL-REF yy) ∷ [])))
  return-call-ref-frame-null : ∀ (z : state) (k : n) (f : frame) (val-lst : (List val)) (yy : typeuse) (instr-lst : (List instr)) → Step-read (mk-config z (as (List instr) ((FRAME- k f ((((map (λ (v-val : val) → (instr-val v-val)) val-lst) ++ (as (List instr) (instr-REF-NULL-ADDR ∷ []))) ++ (as (List instr) ((RETURN-CALL-REF yy) ∷ []))) ++ instr-lst)) ∷ []))) (as (List instr) (TRAP ∷ []))
  return-call-ref-frame-addr : ∀ (z : state) (k : n) (f : frame) (val'-lst : (List val)) (v-n : n) (val-lst : (List val)) (a : addr) (yy : typeuse) (instr-lst : (List instr)) (t-1-lst : (List valtype)) (v-m : m) (t-2-lst : (List valtype)) → 
    ((length (val-lst)) ≡ (v-n)) →
    ((length (t-2-lst)) ≡ (v-m)) →
    ((length (t-1-lst)) ≡ (v-n)) →
    (a < (length (fun-funcinst z))) →
    (Expand (funcinst-TYPE ((fun-funcinst z) [ a ]!)) (comptype-FUNC (mk-list t-1-lst) (mk-list t-2-lst))) →
    Step-read (mk-config z (as (List instr) ((FRAME- k f (((((map (λ (val' : val) → (instr-val val')) val'-lst) ++ (map (λ (v-val : val) → (instr-val v-val)) val-lst)) ++ (as (List instr) ((instr-REF-FUNC-ADDR a) ∷ []))) ++ (as (List instr) ((RETURN-CALL-REF yy) ∷ []))) ++ instr-lst)) ∷ []))) ((map (λ (v-val : val) → (instr-val v-val)) val-lst) ++ (as (List instr) ((instr-REF-FUNC-ADDR a) ∷ (CALL-REF yy) ∷ [])))
  throw-ref-null : ∀ (z : state) → Step-read (mk-config z (as (List instr) (instr-REF-NULL-ADDR ∷ THROW-REF ∷ []))) (as (List instr) (TRAP ∷ []))
  throw-ref-instrs : ∀ (z : state) (val-lst : (List val)) (a : addr) (instr-lst : (List instr)) → 
    ((val-lst ≢ []) ⊎ (instr-lst ≢ [])) →
    Step-read (mk-config z ((map (λ (v-val : val) → (instr-val v-val)) val-lst) ++ ((as (List instr) ((instr-REF-EXN-ADDR a) ∷ [])) ++ ((as (List instr) (THROW-REF ∷ [])) ++ instr-lst)))) (as (List instr) ((instr-REF-EXN-ADDR a) ∷ THROW-REF ∷ []))
  throw-ref-label : ∀ (z : state) (v-n : n) (instr'-lst : (List instr)) (a : addr) → Step-read (mk-config z (as (List instr) ((LABEL- v-n instr'-lst (as (List instr) ((instr-REF-EXN-ADDR a) ∷ THROW-REF ∷ []))) ∷ []))) (as (List instr) ((instr-REF-EXN-ADDR a) ∷ THROW-REF ∷ []))
  throw-ref-frame : ∀ (z : state) (v-n : n) (f : frame) (a : addr) → Step-read (mk-config z (as (List instr) ((FRAME- v-n f (as (List instr) ((instr-REF-EXN-ADDR a) ∷ THROW-REF ∷ []))) ∷ []))) (as (List instr) ((instr-REF-EXN-ADDR a) ∷ THROW-REF ∷ []))
  throw-ref-handler-empty : ∀ (z : state) (v-n : n) (a : addr) → Step-read (mk-config z (as (List instr) ((HANDLER- v-n [] (as (List instr) ((instr-REF-EXN-ADDR a) ∷ THROW-REF ∷ []))) ∷ []))) (as (List instr) ((instr-REF-EXN-ADDR a) ∷ THROW-REF ∷ []))
  throw-ref-handler-catch : ∀ (z : state) (v-n : n) (x : idx) (l : labelidx) (catch'-lst : (List catch)) (a : addr) (val-lst : (List val)) → 
    (a < (length (fun-exninst z))) →
    ((proj-uN-0 32 x) < (length (fun-tagaddr z))) →
    ((exninst-TAG ((fun-exninst z) [ a ]!)) ≡ ((fun-tagaddr z) [ (proj-uN-0 32 x) ]!)) →
    (val-lst ≡ (exninst-FIELDS ((fun-exninst z) [ a ]!))) →
    Step-read (mk-config z (as (List instr) ((HANDLER- v-n ((as (List catch) ((CATCH x l) ∷ [])) ++ catch'-lst) (as (List instr) ((instr-REF-EXN-ADDR a) ∷ THROW-REF ∷ []))) ∷ []))) ((map (λ (v-val : val) → (instr-val v-val)) val-lst) ++ (as (List instr) ((BR l) ∷ [])))
  throw-ref-handler-catch-ref : ∀ (z : state) (v-n : n) (x : idx) (l : labelidx) (catch'-lst : (List catch)) (a : addr) (val-lst : (List val)) → 
    (a < (length (fun-exninst z))) →
    ((proj-uN-0 32 x) < (length (fun-tagaddr z))) →
    ((exninst-TAG ((fun-exninst z) [ a ]!)) ≡ ((fun-tagaddr z) [ (proj-uN-0 32 x) ]!)) →
    (val-lst ≡ (exninst-FIELDS ((fun-exninst z) [ a ]!))) →
    Step-read (mk-config z (as (List instr) ((HANDLER- v-n ((as (List catch) ((CATCH-REF x l) ∷ [])) ++ catch'-lst) (as (List instr) ((instr-REF-EXN-ADDR a) ∷ THROW-REF ∷ []))) ∷ []))) ((map (λ (v-val : val) → (instr-val v-val)) val-lst) ++ (as (List instr) ((instr-REF-EXN-ADDR a) ∷ (BR l) ∷ [])))
  throw-ref-handler-catch-all : ∀ (z : state) (v-n : n) (l : labelidx) (catch'-lst : (List catch)) (a : addr) → Step-read (mk-config z (as (List instr) ((HANDLER- v-n ((as (List catch) ((CATCH-ALL l) ∷ [])) ++ catch'-lst) (as (List instr) ((instr-REF-EXN-ADDR a) ∷ THROW-REF ∷ []))) ∷ []))) (as (List instr) ((BR l) ∷ []))
  throw-ref-handler-catch-all-ref : ∀ (z : state) (v-n : n) (l : labelidx) (catch'-lst : (List catch)) (a : addr) → Step-read (mk-config z (as (List instr) ((HANDLER- v-n ((as (List catch) ((CATCH-ALL-REF l) ∷ [])) ++ catch'-lst) (as (List instr) ((instr-REF-EXN-ADDR a) ∷ THROW-REF ∷ []))) ∷ []))) (as (List instr) ((instr-REF-EXN-ADDR a) ∷ (BR l) ∷ []))
  throw-ref-handler-next : ∀ (z : state) (v-n : n) (v-catch : catch) (catch'-lst : (List catch)) (a : addr) → 
    (¬ (Step-read-before-throw-ref-handler-next (mk-config z (as (List instr) ((HANDLER- v-n ((v-catch ∷ []) ++ catch'-lst) (as (List instr) ((instr-REF-EXN-ADDR a) ∷ THROW-REF ∷ []))) ∷ []))))) →
    Step-read (mk-config z (as (List instr) ((HANDLER- v-n ((v-catch ∷ []) ++ catch'-lst) (as (List instr) ((instr-REF-EXN-ADDR a) ∷ THROW-REF ∷ []))) ∷ []))) (as (List instr) ((HANDLER- v-n catch'-lst (as (List instr) ((instr-REF-EXN-ADDR a) ∷ THROW-REF ∷ []))) ∷ []))
  Step-read--try-table : ∀ (z : state) (v-m : m) (val-lst : (List val)) (bt : blocktype) (catch-lst : (List catch)) (instr-lst : (List instr)) (v-n : n) (t-1-lst : (List valtype)) (t-2-lst : (List valtype)) → 
    ((length (val-lst)) ≡ (v-m)) →
    ((length (t-2-lst)) ≡ (v-n)) →
    ((length (t-1-lst)) ≡ (v-m)) →
    ((blocktype- z bt) ≡ (mk-instrtype (mk-list t-1-lst) [] (mk-list t-2-lst))) →
    Step-read (mk-config z ((map (λ (v-val : val) → (instr-val v-val)) val-lst) ++ (as (List instr) ((TRY-TABLE bt (mk-list catch-lst) instr-lst) ∷ [])))) (as (List instr) ((HANDLER- v-n catch-lst (as (List instr) ((LABEL- v-n [] ((map (λ (v-val : val) → (instr-val v-val)) val-lst) ++ instr-lst)) ∷ []))) ∷ []))
  Step-read--local-get : ∀ (z : state) (x : idx) (v-val : val) → 
    ((fun-local z x) ≡ (just v-val)) →
    Step-read (mk-config z (as (List instr) ((LOCAL-GET x) ∷ []))) ((instr-val v-val) ∷ [])
  Step-read--global-get : ∀ (z : state) (x : idx) (v-val : val) → 
    ((VALUE (fun-global z x)) ≡ v-val) →
    Step-read (mk-config z (as (List instr) ((GLOBAL-GET x) ∷ []))) ((instr-val v-val) ∷ [])
  table-get-oob-0 : ∀ (z : state) (i : (uN-fam0 (32))) (x : idx) → 
    ((proj-uN-0 (size (numtype-addrtype I32)) i) ≥ (length (tableinst-REFS (fun-table z x)))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i) ∷ (TABLE-GET x) ∷ []))) (as (List instr) (TRAP ∷ []))
  table-get-oob-1 : ∀ (z : state) (i : (uN-fam0 (64))) (x : idx) → 
    ((proj-uN-0 (size (numtype-addrtype I64)) i) ≥ (length (tableinst-REFS (fun-table z x)))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i) ∷ (TABLE-GET x) ∷ []))) (as (List instr) (TRAP ∷ []))
  table-get-val-0 : ∀ (z : state) (i : (uN-fam0 (32))) (x : idx) → 
    ((proj-uN-0 (size (numtype-addrtype I32)) i) < (length (tableinst-REFS (fun-table z x)))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i) ∷ (TABLE-GET x) ∷ []))) ((instr-ref ((tableinst-REFS (fun-table z x)) [ (proj-uN-0 (size (numtype-addrtype I32)) i) ]!)) ∷ [])
  table-get-val-1 : ∀ (z : state) (i : (uN-fam0 (64))) (x : idx) → 
    ((proj-uN-0 (size (numtype-addrtype I64)) i) < (length (tableinst-REFS (fun-table z x)))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i) ∷ (TABLE-GET x) ∷ []))) ((instr-ref ((tableinst-REFS (fun-table z x)) [ (proj-uN-0 (size (numtype-addrtype I64)) i) ]!)) ∷ [])
  table-size-0 : ∀ (z : state) (x : idx) (v-n : n) (lim : limits) (rt : reftype) → 
    ((length (tableinst-REFS (fun-table z x))) ≡ v-n) →
    ((tableinst-TYPE (fun-table z x)) ≡ (mk-tabletype I32 lim rt)) →
    Step-read (mk-config z (as (List instr) ((TABLE-SIZE x) ∷ []))) (as (List instr) ((instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ []))
  table-size-1 : ∀ (z : state) (x : idx) (v-n : n) (lim : limits) (rt : reftype) → 
    ((length (tableinst-REFS (fun-table z x))) ≡ v-n) →
    ((tableinst-TYPE (fun-table z x)) ≡ (mk-tabletype I64 lim rt)) →
    Step-read (mk-config z (as (List instr) ((TABLE-SIZE x) ∷ []))) (as (List instr) ((instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ []))
  table-fill-oob-0 : ∀ (z : state) (i : (uN-fam0 (32))) (v-val : val) (v-n : n) (x : idx) → 
    (((proj-uN-0 (size (numtype-addrtype I32)) i) + v-n) > (length (tableinst-REFS (fun-table z x)))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i) ∷ (instr-val v-val) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (TABLE-FILL x) ∷ []))) (as (List instr) (TRAP ∷ []))
  table-fill-oob-1 : ∀ (z : state) (i : (uN-fam0 (64))) (v-val : val) (v-n : n) (x : idx) → 
    (((proj-uN-0 (size (numtype-addrtype I64)) i) + v-n) > (length (tableinst-REFS (fun-table z x)))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i) ∷ (instr-val v-val) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (TABLE-FILL x) ∷ []))) (as (List instr) (TRAP ∷ []))
  table-fill-zero-0 : ∀ (z : state) (i : (uN-fam0 (32))) (v-val : val) (v-n : n) (x : idx) → 
    (((proj-uN-0 (size (numtype-addrtype I32)) i) + v-n) ≤ (length (tableinst-REFS (fun-table z x)))) →
    (v-n ≡ 0) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i) ∷ (instr-val v-val) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (TABLE-FILL x) ∷ []))) []
  table-fill-zero-1 : ∀ (z : state) (i : (uN-fam0 (64))) (v-val : val) (v-n : n) (x : idx) → 
    (((proj-uN-0 (size (numtype-addrtype I64)) i) + v-n) ≤ (length (tableinst-REFS (fun-table z x)))) →
    (v-n ≡ 0) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i) ∷ (instr-val v-val) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (TABLE-FILL x) ∷ []))) []
  table-fill-succ-0 : ∀ (z : state) (i : (uN-fam0 (32))) (v-val : val) (v-n : n) (x : idx) → 
    (v-n ≢ 0) →
    (((proj-uN-0 (size (numtype-addrtype I32)) i) + v-n) ≤ (length (tableinst-REFS (fun-table z x)))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i) ∷ (instr-val v-val) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (TABLE-FILL x) ∷ []))) (as (List instr) ((instr-CONST (numtype-addrtype I32) i) ∷ (instr-val v-val) ∷ (TABLE-SET x) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN ((proj-uN-0 (size (numtype-addrtype I32)) i) + 1))) ∷ (instr-val v-val) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} v-n) – (coerce {B = ℕ} 1))))) ∷ (TABLE-FILL x) ∷ []))
  table-fill-succ-1 : ∀ (z : state) (i : (uN-fam0 (64))) (v-val : val) (v-n : n) (x : idx) → 
    (v-n ≢ 0) →
    (((proj-uN-0 (size (numtype-addrtype I64)) i) + v-n) ≤ (length (tableinst-REFS (fun-table z x)))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i) ∷ (instr-val v-val) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (TABLE-FILL x) ∷ []))) (as (List instr) ((instr-CONST (numtype-addrtype I64) i) ∷ (instr-val v-val) ∷ (TABLE-SET x) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN ((proj-uN-0 (size (numtype-addrtype I64)) i) + 1))) ∷ (instr-val v-val) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} v-n) – (coerce {B = ℕ} 1))))) ∷ (TABLE-FILL x) ∷ []))
  table-copy-oob-0 : ∀ (z : state) (i-1 : (uN-fam0 (32))) (i-2 : (uN-fam0 (32))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    ((((proj-uN-0 (size (numtype-addrtype I32)) i-1) + v-n) > (length (tableinst-REFS (fun-table z x-1)))) ⊎ (((proj-uN-0 (size (numtype-addrtype I32)) i-2) + v-n) > (length (tableinst-REFS (fun-table z x-2))))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (TABLE-COPY x-1 x-2) ∷ []))) (as (List instr) (TRAP ∷ []))
  table-copy-oob-1 : ∀ (z : state) (i-1 : (uN-fam0 (64))) (i-2 : (uN-fam0 (32))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    ((((proj-uN-0 (size (numtype-addrtype I64)) i-1) + v-n) > (length (tableinst-REFS (fun-table z x-1)))) ⊎ (((proj-uN-0 (size (numtype-addrtype I32)) i-2) + v-n) > (length (tableinst-REFS (fun-table z x-2))))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (TABLE-COPY x-1 x-2) ∷ []))) (as (List instr) (TRAP ∷ []))
  table-copy-oob-2 : ∀ (z : state) (i-1 : (uN-fam0 (32))) (i-2 : (uN-fam0 (64))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    ((((proj-uN-0 (size (numtype-addrtype I32)) i-1) + v-n) > (length (tableinst-REFS (fun-table z x-1)))) ⊎ (((proj-uN-0 (size (numtype-addrtype I64)) i-2) + v-n) > (length (tableinst-REFS (fun-table z x-2))))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (TABLE-COPY x-1 x-2) ∷ []))) (as (List instr) (TRAP ∷ []))
  table-copy-oob-3 : ∀ (z : state) (i-1 : (uN-fam0 (64))) (i-2 : (uN-fam0 (64))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    ((((proj-uN-0 (size (numtype-addrtype I64)) i-1) + v-n) > (length (tableinst-REFS (fun-table z x-1)))) ⊎ (((proj-uN-0 (size (numtype-addrtype I64)) i-2) + v-n) > (length (tableinst-REFS (fun-table z x-2))))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (TABLE-COPY x-1 x-2) ∷ []))) (as (List instr) (TRAP ∷ []))
  table-copy-oob-4 : ∀ (z : state) (i-1 : (uN-fam0 (32))) (i-2 : (uN-fam0 (32))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    ((((proj-uN-0 (size (numtype-addrtype I32)) i-1) + v-n) > (length (tableinst-REFS (fun-table z x-1)))) ⊎ (((proj-uN-0 (size (numtype-addrtype I32)) i-2) + v-n) > (length (tableinst-REFS (fun-table z x-2))))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (TABLE-COPY x-1 x-2) ∷ []))) (as (List instr) (TRAP ∷ []))
  table-copy-oob-5 : ∀ (z : state) (i-1 : (uN-fam0 (64))) (i-2 : (uN-fam0 (32))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    ((((proj-uN-0 (size (numtype-addrtype I64)) i-1) + v-n) > (length (tableinst-REFS (fun-table z x-1)))) ⊎ (((proj-uN-0 (size (numtype-addrtype I32)) i-2) + v-n) > (length (tableinst-REFS (fun-table z x-2))))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (TABLE-COPY x-1 x-2) ∷ []))) (as (List instr) (TRAP ∷ []))
  table-copy-oob-6 : ∀ (z : state) (i-1 : (uN-fam0 (32))) (i-2 : (uN-fam0 (64))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    ((((proj-uN-0 (size (numtype-addrtype I32)) i-1) + v-n) > (length (tableinst-REFS (fun-table z x-1)))) ⊎ (((proj-uN-0 (size (numtype-addrtype I64)) i-2) + v-n) > (length (tableinst-REFS (fun-table z x-2))))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (TABLE-COPY x-1 x-2) ∷ []))) (as (List instr) (TRAP ∷ []))
  table-copy-oob-7 : ∀ (z : state) (i-1 : (uN-fam0 (64))) (i-2 : (uN-fam0 (64))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    ((((proj-uN-0 (size (numtype-addrtype I64)) i-1) + v-n) > (length (tableinst-REFS (fun-table z x-1)))) ⊎ (((proj-uN-0 (size (numtype-addrtype I64)) i-2) + v-n) > (length (tableinst-REFS (fun-table z x-2))))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (TABLE-COPY x-1 x-2) ∷ []))) (as (List instr) (TRAP ∷ []))
  table-copy-zero-0 : ∀ (z : state) (i-1 : (uN-fam0 (32))) (i-2 : (uN-fam0 (32))) (v-n : n) (x : idx) (y : idx) → 
    (¬ (Step-read-before-table-copy-zero (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ []))))) →
    (v-n ≡ 0) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ []))) []
  table-copy-zero-1 : ∀ (z : state) (i-1 : (uN-fam0 (64))) (i-2 : (uN-fam0 (32))) (v-n : n) (x : idx) (y : idx) → 
    (¬ (Step-read-before-table-copy-zero (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ []))))) →
    (v-n ≡ 0) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ []))) []
  table-copy-zero-2 : ∀ (z : state) (i-1 : (uN-fam0 (32))) (i-2 : (uN-fam0 (64))) (v-n : n) (x : idx) (y : idx) → 
    (¬ (Step-read-before-table-copy-zero (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ []))))) →
    (v-n ≡ 0) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ []))) []
  table-copy-zero-3 : ∀ (z : state) (i-1 : (uN-fam0 (64))) (i-2 : (uN-fam0 (64))) (v-n : n) (x : idx) (y : idx) → 
    (¬ (Step-read-before-table-copy-zero (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ []))))) →
    (v-n ≡ 0) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ []))) []
  table-copy-zero-4 : ∀ (z : state) (i-1 : (uN-fam0 (32))) (i-2 : (uN-fam0 (32))) (v-n : n) (x : idx) (y : idx) → 
    (¬ (Step-read-before-table-copy-zero (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ []))))) →
    (v-n ≡ 0) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ []))) []
  table-copy-zero-5 : ∀ (z : state) (i-1 : (uN-fam0 (64))) (i-2 : (uN-fam0 (32))) (v-n : n) (x : idx) (y : idx) → 
    (¬ (Step-read-before-table-copy-zero (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ []))))) →
    (v-n ≡ 0) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ []))) []
  table-copy-zero-6 : ∀ (z : state) (i-1 : (uN-fam0 (32))) (i-2 : (uN-fam0 (64))) (v-n : n) (x : idx) (y : idx) → 
    (¬ (Step-read-before-table-copy-zero (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ []))))) →
    (v-n ≡ 0) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ []))) []
  table-copy-zero-7 : ∀ (z : state) (i-1 : (uN-fam0 (64))) (i-2 : (uN-fam0 (64))) (v-n : n) (x : idx) (y : idx) → 
    (¬ (Step-read-before-table-copy-zero (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ []))))) →
    (v-n ≡ 0) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ []))) []
  table-copy-le-0 : ∀ (z : state) (i-1 : (uN-fam0 (32))) (i-2 : (uN-fam0 (32))) (v-n : n) (x : idx) (y : idx) → 
    (¬ (Step-read-before-table-copy-le (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ []))))) →
    ((proj-uN-0 (size (numtype-addrtype I32)) i-1) ≤ (proj-uN-0 (size (numtype-addrtype I32)) i-2)) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ []))) (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (TABLE-GET y) ∷ (TABLE-SET x) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN ((proj-uN-0 (size (numtype-addrtype I32)) i-1) + 1))) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN ((proj-uN-0 (size (numtype-addrtype I32)) i-2) + 1))) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} v-n) – (coerce {B = ℕ} 1))))) ∷ (TABLE-COPY x y) ∷ []))
  table-copy-le-1 : ∀ (z : state) (i-1 : (uN-fam0 (64))) (i-2 : (uN-fam0 (32))) (v-n : n) (x : idx) (y : idx) → 
    (¬ (Step-read-before-table-copy-le (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ []))))) →
    ((proj-uN-0 (size (numtype-addrtype I64)) i-1) ≤ (proj-uN-0 (size (numtype-addrtype I32)) i-2)) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ []))) (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (TABLE-GET y) ∷ (TABLE-SET x) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN ((proj-uN-0 (size (numtype-addrtype I64)) i-1) + 1))) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN ((proj-uN-0 (size (numtype-addrtype I32)) i-2) + 1))) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} v-n) – (coerce {B = ℕ} 1))))) ∷ (TABLE-COPY x y) ∷ []))
  table-copy-le-2 : ∀ (z : state) (i-1 : (uN-fam0 (32))) (i-2 : (uN-fam0 (64))) (v-n : n) (x : idx) (y : idx) → 
    (¬ (Step-read-before-table-copy-le (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ []))))) →
    ((proj-uN-0 (size (numtype-addrtype I32)) i-1) ≤ (proj-uN-0 (size (numtype-addrtype I64)) i-2)) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ []))) (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (TABLE-GET y) ∷ (TABLE-SET x) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN ((proj-uN-0 (size (numtype-addrtype I32)) i-1) + 1))) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN ((proj-uN-0 (size (numtype-addrtype I64)) i-2) + 1))) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} v-n) – (coerce {B = ℕ} 1))))) ∷ (TABLE-COPY x y) ∷ []))
  table-copy-le-3 : ∀ (z : state) (i-1 : (uN-fam0 (64))) (i-2 : (uN-fam0 (64))) (v-n : n) (x : idx) (y : idx) → 
    (¬ (Step-read-before-table-copy-le (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ []))))) →
    ((proj-uN-0 (size (numtype-addrtype I64)) i-1) ≤ (proj-uN-0 (size (numtype-addrtype I64)) i-2)) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ []))) (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (TABLE-GET y) ∷ (TABLE-SET x) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN ((proj-uN-0 (size (numtype-addrtype I64)) i-1) + 1))) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN ((proj-uN-0 (size (numtype-addrtype I64)) i-2) + 1))) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} v-n) – (coerce {B = ℕ} 1))))) ∷ (TABLE-COPY x y) ∷ []))
  table-copy-le-4 : ∀ (z : state) (i-1 : (uN-fam0 (32))) (i-2 : (uN-fam0 (32))) (v-n : n) (x : idx) (y : idx) → 
    (¬ (Step-read-before-table-copy-le (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ []))))) →
    ((proj-uN-0 (size (numtype-addrtype I32)) i-1) ≤ (proj-uN-0 (size (numtype-addrtype I32)) i-2)) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ []))) (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (TABLE-GET y) ∷ (TABLE-SET x) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN ((proj-uN-0 (size (numtype-addrtype I32)) i-1) + 1))) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN ((proj-uN-0 (size (numtype-addrtype I32)) i-2) + 1))) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} v-n) – (coerce {B = ℕ} 1))))) ∷ (TABLE-COPY x y) ∷ []))
  table-copy-le-5 : ∀ (z : state) (i-1 : (uN-fam0 (64))) (i-2 : (uN-fam0 (32))) (v-n : n) (x : idx) (y : idx) → 
    (¬ (Step-read-before-table-copy-le (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ []))))) →
    ((proj-uN-0 (size (numtype-addrtype I64)) i-1) ≤ (proj-uN-0 (size (numtype-addrtype I32)) i-2)) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ []))) (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (TABLE-GET y) ∷ (TABLE-SET x) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN ((proj-uN-0 (size (numtype-addrtype I64)) i-1) + 1))) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN ((proj-uN-0 (size (numtype-addrtype I32)) i-2) + 1))) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} v-n) – (coerce {B = ℕ} 1))))) ∷ (TABLE-COPY x y) ∷ []))
  table-copy-le-6 : ∀ (z : state) (i-1 : (uN-fam0 (32))) (i-2 : (uN-fam0 (64))) (v-n : n) (x : idx) (y : idx) → 
    (¬ (Step-read-before-table-copy-le (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ []))))) →
    ((proj-uN-0 (size (numtype-addrtype I32)) i-1) ≤ (proj-uN-0 (size (numtype-addrtype I64)) i-2)) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ []))) (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (TABLE-GET y) ∷ (TABLE-SET x) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN ((proj-uN-0 (size (numtype-addrtype I32)) i-1) + 1))) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN ((proj-uN-0 (size (numtype-addrtype I64)) i-2) + 1))) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} v-n) – (coerce {B = ℕ} 1))))) ∷ (TABLE-COPY x y) ∷ []))
  table-copy-le-7 : ∀ (z : state) (i-1 : (uN-fam0 (64))) (i-2 : (uN-fam0 (64))) (v-n : n) (x : idx) (y : idx) → 
    (¬ (Step-read-before-table-copy-le (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ []))))) →
    ((proj-uN-0 (size (numtype-addrtype I64)) i-1) ≤ (proj-uN-0 (size (numtype-addrtype I64)) i-2)) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ []))) (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (TABLE-GET y) ∷ (TABLE-SET x) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN ((proj-uN-0 (size (numtype-addrtype I64)) i-1) + 1))) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN ((proj-uN-0 (size (numtype-addrtype I64)) i-2) + 1))) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} v-n) – (coerce {B = ℕ} 1))))) ∷ (TABLE-COPY x y) ∷ []))
  table-copy-gt-0 : ∀ (z : state) (i-1 : (uN-fam0 (32))) (i-2 : (uN-fam0 (32))) (v-n : n) (x : idx) (y : idx) → 
    (¬ (Step-read-before-table-copy-gt (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ []))))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ []))) (as (List instr) ((instr-CONST (numtype-addrtype I32) (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} ((proj-uN-0 (size (numtype-addrtype I32)) i-1) + v-n)) – (coerce {B = ℕ} 1))))) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} ((proj-uN-0 (size (numtype-addrtype I32)) i-2) + v-n)) – (coerce {B = ℕ} 1))))) ∷ (TABLE-GET y) ∷ (TABLE-SET x) ∷ (instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} v-n) – (coerce {B = ℕ} 1))))) ∷ (TABLE-COPY x y) ∷ []))
  table-copy-gt-1 : ∀ (z : state) (i-1 : (uN-fam0 (64))) (i-2 : (uN-fam0 (32))) (v-n : n) (x : idx) (y : idx) → 
    (¬ (Step-read-before-table-copy-gt (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ []))))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ []))) (as (List instr) ((instr-CONST (numtype-addrtype I64) (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} ((proj-uN-0 (size (numtype-addrtype I64)) i-1) + v-n)) – (coerce {B = ℕ} 1))))) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} ((proj-uN-0 (size (numtype-addrtype I32)) i-2) + v-n)) – (coerce {B = ℕ} 1))))) ∷ (TABLE-GET y) ∷ (TABLE-SET x) ∷ (instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} v-n) – (coerce {B = ℕ} 1))))) ∷ (TABLE-COPY x y) ∷ []))
  table-copy-gt-2 : ∀ (z : state) (i-1 : (uN-fam0 (32))) (i-2 : (uN-fam0 (64))) (v-n : n) (x : idx) (y : idx) → 
    (¬ (Step-read-before-table-copy-gt (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ []))))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ []))) (as (List instr) ((instr-CONST (numtype-addrtype I32) (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} ((proj-uN-0 (size (numtype-addrtype I32)) i-1) + v-n)) – (coerce {B = ℕ} 1))))) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} ((proj-uN-0 (size (numtype-addrtype I64)) i-2) + v-n)) – (coerce {B = ℕ} 1))))) ∷ (TABLE-GET y) ∷ (TABLE-SET x) ∷ (instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} v-n) – (coerce {B = ℕ} 1))))) ∷ (TABLE-COPY x y) ∷ []))
  table-copy-gt-3 : ∀ (z : state) (i-1 : (uN-fam0 (64))) (i-2 : (uN-fam0 (64))) (v-n : n) (x : idx) (y : idx) → 
    (¬ (Step-read-before-table-copy-gt (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ []))))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ []))) (as (List instr) ((instr-CONST (numtype-addrtype I64) (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} ((proj-uN-0 (size (numtype-addrtype I64)) i-1) + v-n)) – (coerce {B = ℕ} 1))))) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} ((proj-uN-0 (size (numtype-addrtype I64)) i-2) + v-n)) – (coerce {B = ℕ} 1))))) ∷ (TABLE-GET y) ∷ (TABLE-SET x) ∷ (instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} v-n) – (coerce {B = ℕ} 1))))) ∷ (TABLE-COPY x y) ∷ []))
  table-copy-gt-4 : ∀ (z : state) (i-1 : (uN-fam0 (32))) (i-2 : (uN-fam0 (32))) (v-n : n) (x : idx) (y : idx) → 
    (¬ (Step-read-before-table-copy-gt (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ []))))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ []))) (as (List instr) ((instr-CONST (numtype-addrtype I32) (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} ((proj-uN-0 (size (numtype-addrtype I32)) i-1) + v-n)) – (coerce {B = ℕ} 1))))) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} ((proj-uN-0 (size (numtype-addrtype I32)) i-2) + v-n)) – (coerce {B = ℕ} 1))))) ∷ (TABLE-GET y) ∷ (TABLE-SET x) ∷ (instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} v-n) – (coerce {B = ℕ} 1))))) ∷ (TABLE-COPY x y) ∷ []))
  table-copy-gt-5 : ∀ (z : state) (i-1 : (uN-fam0 (64))) (i-2 : (uN-fam0 (32))) (v-n : n) (x : idx) (y : idx) → 
    (¬ (Step-read-before-table-copy-gt (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ []))))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ []))) (as (List instr) ((instr-CONST (numtype-addrtype I64) (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} ((proj-uN-0 (size (numtype-addrtype I64)) i-1) + v-n)) – (coerce {B = ℕ} 1))))) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} ((proj-uN-0 (size (numtype-addrtype I32)) i-2) + v-n)) – (coerce {B = ℕ} 1))))) ∷ (TABLE-GET y) ∷ (TABLE-SET x) ∷ (instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} v-n) – (coerce {B = ℕ} 1))))) ∷ (TABLE-COPY x y) ∷ []))
  table-copy-gt-6 : ∀ (z : state) (i-1 : (uN-fam0 (32))) (i-2 : (uN-fam0 (64))) (v-n : n) (x : idx) (y : idx) → 
    (¬ (Step-read-before-table-copy-gt (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ []))))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ []))) (as (List instr) ((instr-CONST (numtype-addrtype I32) (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} ((proj-uN-0 (size (numtype-addrtype I32)) i-1) + v-n)) – (coerce {B = ℕ} 1))))) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} ((proj-uN-0 (size (numtype-addrtype I64)) i-2) + v-n)) – (coerce {B = ℕ} 1))))) ∷ (TABLE-GET y) ∷ (TABLE-SET x) ∷ (instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} v-n) – (coerce {B = ℕ} 1))))) ∷ (TABLE-COPY x y) ∷ []))
  table-copy-gt-7 : ∀ (z : state) (i-1 : (uN-fam0 (64))) (i-2 : (uN-fam0 (64))) (v-n : n) (x : idx) (y : idx) → 
    (¬ (Step-read-before-table-copy-gt (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ []))))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (TABLE-COPY x y) ∷ []))) (as (List instr) ((instr-CONST (numtype-addrtype I64) (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} ((proj-uN-0 (size (numtype-addrtype I64)) i-1) + v-n)) – (coerce {B = ℕ} 1))))) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} ((proj-uN-0 (size (numtype-addrtype I64)) i-2) + v-n)) – (coerce {B = ℕ} 1))))) ∷ (TABLE-GET y) ∷ (TABLE-SET x) ∷ (instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} v-n) – (coerce {B = ℕ} 1))))) ∷ (TABLE-COPY x y) ∷ []))
  table-init-oob-0 : ∀ (z : state) (i : (uN-fam0 (32))) (j : (uN-fam0 (32))) (v-n : n) (x : idx) (y : idx) → 
    ((((proj-uN-0 (size (numtype-addrtype I32)) i) + v-n) > (length (tableinst-REFS (fun-table z x)))) ⊎ (((proj-uN-0 32 j) + v-n) > (length (eleminst-REFS (fun-elem z y))))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i) ∷ (instr-CONST numtype-I32 j) ∷ (instr-CONST numtype-I32 (mk-uN v-n)) ∷ (TABLE-INIT x y) ∷ []))) (as (List instr) (TRAP ∷ []))
  table-init-oob-1 : ∀ (z : state) (i : (uN-fam0 (64))) (j : (uN-fam0 (32))) (v-n : n) (x : idx) (y : idx) → 
    ((((proj-uN-0 (size (numtype-addrtype I64)) i) + v-n) > (length (tableinst-REFS (fun-table z x)))) ⊎ (((proj-uN-0 32 j) + v-n) > (length (eleminst-REFS (fun-elem z y))))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i) ∷ (instr-CONST numtype-I32 j) ∷ (instr-CONST numtype-I32 (mk-uN v-n)) ∷ (TABLE-INIT x y) ∷ []))) (as (List instr) (TRAP ∷ []))
  table-init-zero-0 : ∀ (z : state) (i : (uN-fam0 (32))) (j : (uN-fam0 (32))) (v-n : n) (x : idx) (y : idx) → 
    ((((proj-uN-0 (size (numtype-addrtype I32)) i) + v-n) ≤ (length (tableinst-REFS (fun-table z x)))) × (((proj-uN-0 32 j) + v-n) ≤ (length (eleminst-REFS (fun-elem z y))))) →
    (v-n ≡ 0) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i) ∷ (instr-CONST numtype-I32 j) ∷ (instr-CONST numtype-I32 (mk-uN v-n)) ∷ (TABLE-INIT x y) ∷ []))) []
  table-init-zero-1 : ∀ (z : state) (i : (uN-fam0 (64))) (j : (uN-fam0 (32))) (v-n : n) (x : idx) (y : idx) → 
    ((((proj-uN-0 (size (numtype-addrtype I64)) i) + v-n) ≤ (length (tableinst-REFS (fun-table z x)))) × (((proj-uN-0 32 j) + v-n) ≤ (length (eleminst-REFS (fun-elem z y))))) →
    (v-n ≡ 0) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i) ∷ (instr-CONST numtype-I32 j) ∷ (instr-CONST numtype-I32 (mk-uN v-n)) ∷ (TABLE-INIT x y) ∷ []))) []
  table-init-succ-0 : ∀ (z : state) (i : (uN-fam0 (32))) (j : (uN-fam0 (32))) (v-n : n) (x : idx) (y : idx) → 
    ((proj-uN-0 32 j) < (length (eleminst-REFS (fun-elem z y)))) →
    (v-n ≢ 0) →
    ((((proj-uN-0 (size (numtype-addrtype I32)) i) + v-n) ≤ (length (tableinst-REFS (fun-table z x)))) × (((proj-uN-0 32 j) + v-n) ≤ (length (eleminst-REFS (fun-elem z y))))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i) ∷ (instr-CONST numtype-I32 j) ∷ (instr-CONST numtype-I32 (mk-uN v-n)) ∷ (TABLE-INIT x y) ∷ []))) (as (List instr) ((instr-CONST (numtype-addrtype I32) i) ∷ (instr-ref ((eleminst-REFS (fun-elem z y)) [ (proj-uN-0 32 j) ]!)) ∷ (TABLE-SET x) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN ((proj-uN-0 (size (numtype-addrtype I32)) i) + 1))) ∷ (instr-CONST numtype-I32 (mk-uN ((proj-uN-0 32 j) + 1))) ∷ (instr-CONST numtype-I32 (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} v-n) – (coerce {B = ℕ} 1))))) ∷ (TABLE-INIT x y) ∷ []))
  table-init-succ-1 : ∀ (z : state) (i : (uN-fam0 (64))) (j : (uN-fam0 (32))) (v-n : n) (x : idx) (y : idx) → 
    ((proj-uN-0 32 j) < (length (eleminst-REFS (fun-elem z y)))) →
    (v-n ≢ 0) →
    ((((proj-uN-0 (size (numtype-addrtype I64)) i) + v-n) ≤ (length (tableinst-REFS (fun-table z x)))) × (((proj-uN-0 32 j) + v-n) ≤ (length (eleminst-REFS (fun-elem z y))))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i) ∷ (instr-CONST numtype-I32 j) ∷ (instr-CONST numtype-I32 (mk-uN v-n)) ∷ (TABLE-INIT x y) ∷ []))) (as (List instr) ((instr-CONST (numtype-addrtype I64) i) ∷ (instr-ref ((eleminst-REFS (fun-elem z y)) [ (proj-uN-0 32 j) ]!)) ∷ (TABLE-SET x) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN ((proj-uN-0 (size (numtype-addrtype I64)) i) + 1))) ∷ (instr-CONST numtype-I32 (mk-uN ((proj-uN-0 32 j) + 1))) ∷ (instr-CONST numtype-I32 (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} v-n) – (coerce {B = ℕ} 1))))) ∷ (TABLE-INIT x y) ∷ []))
  load-num-oob-0 : ∀ (z : state) (i : (uN-fam0 (32))) (nt : numtype) (x : idx) (ao : memarg) → 
    ((((proj-uN-0 (size (numtype-addrtype I32)) i) + (proj-uN-0 64 (OFFSET ao))) + (coerce {B = ℕ} ((coerce {B = ℕ} (size nt)) / (coerce {B = ℕ} 8)))) > (length (BYTES (fun-mem z x)))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i) ∷ (LOAD nt nothing x ao) ∷ []))) (as (List instr) (TRAP ∷ []))
  load-num-oob-1 : ∀ (z : state) (i : (uN-fam0 (64))) (nt : numtype) (x : idx) (ao : memarg) → 
    ((((proj-uN-0 (size (numtype-addrtype I64)) i) + (proj-uN-0 64 (OFFSET ao))) + (coerce {B = ℕ} ((coerce {B = ℕ} (size nt)) / (coerce {B = ℕ} 8)))) > (length (BYTES (fun-mem z x)))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i) ∷ (LOAD nt nothing x ao) ∷ []))) (as (List instr) (TRAP ∷ []))
  load-num-val-0 : ∀ (z : state) (i : (uN-fam0 (32))) (nt : numtype) (x : idx) (ao : memarg) (c : (num- nt)) → 
    ((nbytes- nt c) ≡ (slice (BYTES (fun-mem z x)) ((proj-uN-0 (size (numtype-addrtype I32)) i) + (proj-uN-0 64 (OFFSET ao))) (coerce {B = ℕ} ((coerce {B = ℕ} (size nt)) / (coerce {B = ℕ} 8))))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i) ∷ (LOAD nt nothing x ao) ∷ []))) (as (List instr) ((instr-CONST nt c) ∷ []))
  load-num-val-1 : ∀ (z : state) (i : (uN-fam0 (64))) (nt : numtype) (x : idx) (ao : memarg) (c : (num- nt)) → 
    ((nbytes- nt c) ≡ (slice (BYTES (fun-mem z x)) ((proj-uN-0 (size (numtype-addrtype I64)) i) + (proj-uN-0 64 (OFFSET ao))) (coerce {B = ℕ} ((coerce {B = ℕ} (size nt)) / (coerce {B = ℕ} 8))))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i) ∷ (LOAD nt nothing x ao) ∷ []))) (as (List instr) ((instr-CONST nt c) ∷ []))
  load-pack-oob-0 : ∀ (z : state) (i : (uN-fam0 (32))) (v-n : n) (v-sx : sx) (x : idx) (ao : memarg) → 
    ((((proj-uN-0 (size (numtype-addrtype I32)) i) + (proj-uN-0 64 (OFFSET ao))) + (coerce {B = ℕ} ((coerce {B = ℕ} v-n) / (coerce {B = ℕ} 8)))) > (length (BYTES (fun-mem z x)))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i) ∷ (LOAD (numtype-addrtype I32) (just (mk-loadop- (mk-sz v-n) v-sx)) x ao) ∷ []))) (as (List instr) (TRAP ∷ []))
  load-pack-oob-1 : ∀ (z : state) (i : (uN-fam0 (64))) (v-n : n) (v-sx : sx) (x : idx) (ao : memarg) → 
    ((((proj-uN-0 (size (numtype-addrtype I64)) i) + (proj-uN-0 64 (OFFSET ao))) + (coerce {B = ℕ} ((coerce {B = ℕ} v-n) / (coerce {B = ℕ} 8)))) > (length (BYTES (fun-mem z x)))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i) ∷ (LOAD (numtype-addrtype I32) (just (mk-loadop- (mk-sz v-n) v-sx)) x ao) ∷ []))) (as (List instr) (TRAP ∷ []))
  load-pack-oob-2 : ∀ (z : state) (i : (uN-fam0 (32))) (v-n : n) (v-sx : sx) (x : idx) (ao : memarg) → 
    ((((proj-uN-0 (size (numtype-addrtype I32)) i) + (proj-uN-0 64 (OFFSET ao))) + (coerce {B = ℕ} ((coerce {B = ℕ} v-n) / (coerce {B = ℕ} 8)))) > (length (BYTES (fun-mem z x)))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i) ∷ (LOAD (numtype-addrtype I64) (just (mk-loadop- (mk-sz v-n) v-sx)) x ao) ∷ []))) (as (List instr) (TRAP ∷ []))
  load-pack-oob-3 : ∀ (z : state) (i : (uN-fam0 (64))) (v-n : n) (v-sx : sx) (x : idx) (ao : memarg) → 
    ((((proj-uN-0 (size (numtype-addrtype I64)) i) + (proj-uN-0 64 (OFFSET ao))) + (coerce {B = ℕ} ((coerce {B = ℕ} v-n) / (coerce {B = ℕ} 8)))) > (length (BYTES (fun-mem z x)))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i) ∷ (LOAD (numtype-addrtype I64) (just (mk-loadop- (mk-sz v-n) v-sx)) x ao) ∷ []))) (as (List instr) (TRAP ∷ []))
  load-pack-val-0 : ∀ (z : state) (i : (uN-fam0 (32))) (v-n : n) (v-sx : sx) (x : idx) (ao : memarg) (c : (uN-fam0 (v-n))) → 
    ((ibytes- v-n c) ≡ (slice (BYTES (fun-mem z x)) ((proj-uN-0 (size (numtype-addrtype I32)) i) + (proj-uN-0 64 (OFFSET ao))) (coerce {B = ℕ} ((coerce {B = ℕ} v-n) / (coerce {B = ℕ} 8))))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i) ∷ (LOAD (numtype-addrtype I32) (just (mk-loadop- (mk-sz v-n) v-sx)) x ao) ∷ []))) (as (List instr) ((instr-CONST (numtype-addrtype I32) (extend-- v-n (size (numtype-addrtype I32)) v-sx c)) ∷ []))
  load-pack-val-1 : ∀ (z : state) (i : (uN-fam0 (64))) (v-n : n) (v-sx : sx) (x : idx) (ao : memarg) (c : (uN-fam0 (v-n))) → 
    ((ibytes- v-n c) ≡ (slice (BYTES (fun-mem z x)) ((proj-uN-0 (size (numtype-addrtype I64)) i) + (proj-uN-0 64 (OFFSET ao))) (coerce {B = ℕ} ((coerce {B = ℕ} v-n) / (coerce {B = ℕ} 8))))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i) ∷ (LOAD (numtype-addrtype I32) (just (mk-loadop- (mk-sz v-n) v-sx)) x ao) ∷ []))) (as (List instr) ((instr-CONST (numtype-addrtype I32) (extend-- v-n (size (numtype-addrtype I32)) v-sx c)) ∷ []))
  load-pack-val-2 : ∀ (z : state) (i : (uN-fam0 (32))) (v-n : n) (v-sx : sx) (x : idx) (ao : memarg) (c : (uN-fam0 (v-n))) → 
    ((ibytes- v-n c) ≡ (slice (BYTES (fun-mem z x)) ((proj-uN-0 (size (numtype-addrtype I32)) i) + (proj-uN-0 64 (OFFSET ao))) (coerce {B = ℕ} ((coerce {B = ℕ} v-n) / (coerce {B = ℕ} 8))))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i) ∷ (LOAD (numtype-addrtype I64) (just (mk-loadop- (mk-sz v-n) v-sx)) x ao) ∷ []))) (as (List instr) ((instr-CONST (numtype-addrtype I64) (extend-- v-n (size (numtype-addrtype I64)) v-sx c)) ∷ []))
  load-pack-val-3 : ∀ (z : state) (i : (uN-fam0 (64))) (v-n : n) (v-sx : sx) (x : idx) (ao : memarg) (c : (uN-fam0 (v-n))) → 
    ((ibytes- v-n c) ≡ (slice (BYTES (fun-mem z x)) ((proj-uN-0 (size (numtype-addrtype I64)) i) + (proj-uN-0 64 (OFFSET ao))) (coerce {B = ℕ} ((coerce {B = ℕ} v-n) / (coerce {B = ℕ} 8))))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i) ∷ (LOAD (numtype-addrtype I64) (just (mk-loadop- (mk-sz v-n) v-sx)) x ao) ∷ []))) (as (List instr) ((instr-CONST (numtype-addrtype I64) (extend-- v-n (size (numtype-addrtype I64)) v-sx c)) ∷ []))
  vload-oob-0 : ∀ (z : state) (i : (uN-fam0 (32))) (x : idx) (ao : memarg) → 
    ((((proj-uN-0 (size (numtype-addrtype I32)) i) + (proj-uN-0 64 (OFFSET ao))) + (coerce {B = ℕ} ((coerce {B = ℕ} (vsize V128)) / (coerce {B = ℕ} 8)))) > (length (BYTES (fun-mem z x)))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i) ∷ (VLOAD V128 nothing x ao) ∷ []))) (as (List instr) (TRAP ∷ []))
  vload-oob-1 : ∀ (z : state) (i : (uN-fam0 (64))) (x : idx) (ao : memarg) → 
    ((((proj-uN-0 (size (numtype-addrtype I64)) i) + (proj-uN-0 64 (OFFSET ao))) + (coerce {B = ℕ} ((coerce {B = ℕ} (vsize V128)) / (coerce {B = ℕ} 8)))) > (length (BYTES (fun-mem z x)))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i) ∷ (VLOAD V128 nothing x ao) ∷ []))) (as (List instr) (TRAP ∷ []))
  vload-val-0 : ∀ (z : state) (i : (uN-fam0 (32))) (x : idx) (ao : memarg) (c : (uN-fam0 (128))) → 
    ((vbytes- V128 c) ≡ (slice (BYTES (fun-mem z x)) ((proj-uN-0 (size (numtype-addrtype I32)) i) + (proj-uN-0 64 (OFFSET ao))) (coerce {B = ℕ} ((coerce {B = ℕ} (vsize V128)) / (coerce {B = ℕ} 8))))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i) ∷ (VLOAD V128 nothing x ao) ∷ []))) (as (List instr) ((instr-VCONST V128 c) ∷ []))
  vload-val-1 : ∀ (z : state) (i : (uN-fam0 (64))) (x : idx) (ao : memarg) (c : (uN-fam0 (128))) → 
    ((vbytes- V128 c) ≡ (slice (BYTES (fun-mem z x)) ((proj-uN-0 (size (numtype-addrtype I64)) i) + (proj-uN-0 64 (OFFSET ao))) (coerce {B = ℕ} ((coerce {B = ℕ} (vsize V128)) / (coerce {B = ℕ} 8))))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i) ∷ (VLOAD V128 nothing x ao) ∷ []))) (as (List instr) ((instr-VCONST V128 c) ∷ []))
  vload-pack-oob-0 : ∀ (z : state) (i : (uN-fam0 (32))) (v-M : M) (v-K : K) (v-sx : sx) (x : idx) (ao : memarg) → 
    ((((proj-uN-0 (size (numtype-addrtype I32)) i) + (proj-uN-0 64 (OFFSET ao))) + (coerce {B = ℕ} ((coerce {B = ℕ} (v-M * v-K)) / (coerce {B = ℕ} 8)))) > (length (BYTES (fun-mem z x)))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i) ∷ (VLOAD V128 (just (SHAPEX- (mk-sz v-M) v-K v-sx)) x ao) ∷ []))) (as (List instr) (TRAP ∷ []))
  vload-pack-oob-1 : ∀ (z : state) (i : (uN-fam0 (64))) (v-M : M) (v-K : K) (v-sx : sx) (x : idx) (ao : memarg) → 
    ((((proj-uN-0 (size (numtype-addrtype I64)) i) + (proj-uN-0 64 (OFFSET ao))) + (coerce {B = ℕ} ((coerce {B = ℕ} (v-M * v-K)) / (coerce {B = ℕ} 8)))) > (length (BYTES (fun-mem z x)))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i) ∷ (VLOAD V128 (just (SHAPEX- (mk-sz v-M) v-K v-sx)) x ao) ∷ []))) (as (List instr) (TRAP ∷ []))
  vload-pack-val-0 : ∀ (z : state) (i : (uN-fam0 (32))) (v-M : M) (v-K : K) (v-sx : sx) (x : idx) (ao : memarg) (c : (uN-fam0 (128))) (j-lst : (List (uN-fam0 (v-M)))) → 
    ((length (j-lst)) ≡ (v-K)) →
    Foralli (λ k-1 (j-1 : (uN-fam0 (v-M))) → ((ibytes- v-M j-1) ≡ (slice (BYTES (fun-mem z x)) (((proj-uN-0 (size (numtype-addrtype I32)) i) + (proj-uN-0 64 (OFFSET ao))) + (coerce {B = ℕ} ((coerce {B = ℕ} (k-1 * v-M)) / (coerce {B = ℕ} 8)))) (coerce {B = ℕ} ((coerce {B = ℕ} v-M) / (coerce {B = ℕ} 8)))))) j-lst →
    ((c ≡ (inv-lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-K)) (map (λ (j-2 : (uN-fam0 (v-M))) → (extend-- v-M (jsizenn Jnn-I32) v-sx j-2)) j-lst))) × ((jsizenn Jnn-I32) ≡ (v-M * 2))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i) ∷ (VLOAD V128 (just (SHAPEX- (mk-sz v-M) v-K v-sx)) x ao) ∷ []))) (as (List instr) ((instr-VCONST V128 c) ∷ []))
  vload-pack-val-1 : ∀ (z : state) (i : (uN-fam0 (64))) (v-M : M) (v-K : K) (v-sx : sx) (x : idx) (ao : memarg) (c : (uN-fam0 (128))) (j-lst : (List (uN-fam0 (v-M)))) → 
    ((length (j-lst)) ≡ (v-K)) →
    Foralli (λ k-2 (j-3 : (uN-fam0 (v-M))) → ((ibytes- v-M j-3) ≡ (slice (BYTES (fun-mem z x)) (((proj-uN-0 (size (numtype-addrtype I64)) i) + (proj-uN-0 64 (OFFSET ao))) + (coerce {B = ℕ} ((coerce {B = ℕ} (k-2 * v-M)) / (coerce {B = ℕ} 8)))) (coerce {B = ℕ} ((coerce {B = ℕ} v-M) / (coerce {B = ℕ} 8)))))) j-lst →
    ((c ≡ (inv-lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-K)) (map (λ (j-4 : (uN-fam0 (v-M))) → (extend-- v-M (jsizenn Jnn-I32) v-sx j-4)) j-lst))) × ((jsizenn Jnn-I32) ≡ (v-M * 2))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i) ∷ (VLOAD V128 (just (SHAPEX- (mk-sz v-M) v-K v-sx)) x ao) ∷ []))) (as (List instr) ((instr-VCONST V128 c) ∷ []))
  vload-pack-val-2 : ∀ (z : state) (i : (uN-fam0 (32))) (v-M : M) (v-K : K) (v-sx : sx) (x : idx) (ao : memarg) (c : (uN-fam0 (128))) (j-lst : (List (uN-fam0 (v-M)))) → 
    ((length (j-lst)) ≡ (v-K)) →
    Foralli (λ k-3 (j-5 : (uN-fam0 (v-M))) → ((ibytes- v-M j-5) ≡ (slice (BYTES (fun-mem z x)) (((proj-uN-0 (size (numtype-addrtype I32)) i) + (proj-uN-0 64 (OFFSET ao))) + (coerce {B = ℕ} ((coerce {B = ℕ} (k-3 * v-M)) / (coerce {B = ℕ} 8)))) (coerce {B = ℕ} ((coerce {B = ℕ} v-M) / (coerce {B = ℕ} 8)))))) j-lst →
    ((c ≡ (inv-lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-K)) (map (λ (j-6 : (uN-fam0 (v-M))) → (extend-- v-M (jsizenn Jnn-I64) v-sx j-6)) j-lst))) × ((jsizenn Jnn-I64) ≡ (v-M * 2))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i) ∷ (VLOAD V128 (just (SHAPEX- (mk-sz v-M) v-K v-sx)) x ao) ∷ []))) (as (List instr) ((instr-VCONST V128 c) ∷ []))
  vload-pack-val-3 : ∀ (z : state) (i : (uN-fam0 (64))) (v-M : M) (v-K : K) (v-sx : sx) (x : idx) (ao : memarg) (c : (uN-fam0 (128))) (j-lst : (List (uN-fam0 (v-M)))) → 
    ((length (j-lst)) ≡ (v-K)) →
    Foralli (λ k-4 (j-7 : (uN-fam0 (v-M))) → ((ibytes- v-M j-7) ≡ (slice (BYTES (fun-mem z x)) (((proj-uN-0 (size (numtype-addrtype I64)) i) + (proj-uN-0 64 (OFFSET ao))) + (coerce {B = ℕ} ((coerce {B = ℕ} (k-4 * v-M)) / (coerce {B = ℕ} 8)))) (coerce {B = ℕ} ((coerce {B = ℕ} v-M) / (coerce {B = ℕ} 8)))))) j-lst →
    ((c ≡ (inv-lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-K)) (map (λ (j-8 : (uN-fam0 (v-M))) → (extend-- v-M (jsizenn Jnn-I64) v-sx j-8)) j-lst))) × ((jsizenn Jnn-I64) ≡ (v-M * 2))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i) ∷ (VLOAD V128 (just (SHAPEX- (mk-sz v-M) v-K v-sx)) x ao) ∷ []))) (as (List instr) ((instr-VCONST V128 c) ∷ []))
  vload-pack-val-4 : ∀ (z : state) (i : (uN-fam0 (32))) (v-M : M) (v-K : K) (v-sx : sx) (x : idx) (ao : memarg) (c : (uN-fam0 (128))) (j-lst : (List (uN-fam0 (v-M)))) → 
    ((length (j-lst)) ≡ (v-K)) →
    Foralli (λ k-5 (j-9 : (uN-fam0 (v-M))) → ((ibytes- v-M j-9) ≡ (slice (BYTES (fun-mem z x)) (((proj-uN-0 (size (numtype-addrtype I32)) i) + (proj-uN-0 64 (OFFSET ao))) + (coerce {B = ℕ} ((coerce {B = ℕ} (k-5 * v-M)) / (coerce {B = ℕ} 8)))) (coerce {B = ℕ} ((coerce {B = ℕ} v-M) / (coerce {B = ℕ} 8)))))) j-lst →
    ((c ≡ (inv-lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-K)) (map (λ (j-10 : (uN-fam0 (v-M))) → (extend-- v-M (jsizenn Jnn-I8) v-sx j-10)) j-lst))) × ((jsizenn Jnn-I8) ≡ (v-M * 2))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i) ∷ (VLOAD V128 (just (SHAPEX- (mk-sz v-M) v-K v-sx)) x ao) ∷ []))) (as (List instr) ((instr-VCONST V128 c) ∷ []))
  vload-pack-val-5 : ∀ (z : state) (i : (uN-fam0 (64))) (v-M : M) (v-K : K) (v-sx : sx) (x : idx) (ao : memarg) (c : (uN-fam0 (128))) (j-lst : (List (uN-fam0 (v-M)))) → 
    ((length (j-lst)) ≡ (v-K)) →
    Foralli (λ k-6 (j-11 : (uN-fam0 (v-M))) → ((ibytes- v-M j-11) ≡ (slice (BYTES (fun-mem z x)) (((proj-uN-0 (size (numtype-addrtype I64)) i) + (proj-uN-0 64 (OFFSET ao))) + (coerce {B = ℕ} ((coerce {B = ℕ} (k-6 * v-M)) / (coerce {B = ℕ} 8)))) (coerce {B = ℕ} ((coerce {B = ℕ} v-M) / (coerce {B = ℕ} 8)))))) j-lst →
    ((c ≡ (inv-lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-K)) (map (λ (j-12 : (uN-fam0 (v-M))) → (extend-- v-M (jsizenn Jnn-I8) v-sx j-12)) j-lst))) × ((jsizenn Jnn-I8) ≡ (v-M * 2))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i) ∷ (VLOAD V128 (just (SHAPEX- (mk-sz v-M) v-K v-sx)) x ao) ∷ []))) (as (List instr) ((instr-VCONST V128 c) ∷ []))
  vload-pack-val-6 : ∀ (z : state) (i : (uN-fam0 (32))) (v-M : M) (v-K : K) (v-sx : sx) (x : idx) (ao : memarg) (c : (uN-fam0 (128))) (j-lst : (List (uN-fam0 (v-M)))) → 
    ((length (j-lst)) ≡ (v-K)) →
    Foralli (λ k-7 (j-13 : (uN-fam0 (v-M))) → ((ibytes- v-M j-13) ≡ (slice (BYTES (fun-mem z x)) (((proj-uN-0 (size (numtype-addrtype I32)) i) + (proj-uN-0 64 (OFFSET ao))) + (coerce {B = ℕ} ((coerce {B = ℕ} (k-7 * v-M)) / (coerce {B = ℕ} 8)))) (coerce {B = ℕ} ((coerce {B = ℕ} v-M) / (coerce {B = ℕ} 8)))))) j-lst →
    ((c ≡ (inv-lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-K)) (map (λ (j-14 : (uN-fam0 (v-M))) → (extend-- v-M (jsizenn Jnn-I16) v-sx j-14)) j-lst))) × ((jsizenn Jnn-I16) ≡ (v-M * 2))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i) ∷ (VLOAD V128 (just (SHAPEX- (mk-sz v-M) v-K v-sx)) x ao) ∷ []))) (as (List instr) ((instr-VCONST V128 c) ∷ []))
  vload-pack-val-7 : ∀ (z : state) (i : (uN-fam0 (64))) (v-M : M) (v-K : K) (v-sx : sx) (x : idx) (ao : memarg) (c : (uN-fam0 (128))) (j-lst : (List (uN-fam0 (v-M)))) → 
    ((length (j-lst)) ≡ (v-K)) →
    Foralli (λ k-8 (j-15 : (uN-fam0 (v-M))) → ((ibytes- v-M j-15) ≡ (slice (BYTES (fun-mem z x)) (((proj-uN-0 (size (numtype-addrtype I64)) i) + (proj-uN-0 64 (OFFSET ao))) + (coerce {B = ℕ} ((coerce {B = ℕ} (k-8 * v-M)) / (coerce {B = ℕ} 8)))) (coerce {B = ℕ} ((coerce {B = ℕ} v-M) / (coerce {B = ℕ} 8)))))) j-lst →
    ((c ≡ (inv-lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-K)) (map (λ (j-16 : (uN-fam0 (v-M))) → (extend-- v-M (jsizenn Jnn-I16) v-sx j-16)) j-lst))) × ((jsizenn Jnn-I16) ≡ (v-M * 2))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i) ∷ (VLOAD V128 (just (SHAPEX- (mk-sz v-M) v-K v-sx)) x ao) ∷ []))) (as (List instr) ((instr-VCONST V128 c) ∷ []))
  vload-splat-oob-0 : ∀ (z : state) (i : (uN-fam0 (32))) (v-N : N) (x : idx) (ao : memarg) → 
    ((((proj-uN-0 (size (numtype-addrtype I32)) i) + (proj-uN-0 64 (OFFSET ao))) + (coerce {B = ℕ} ((coerce {B = ℕ} v-N) / (coerce {B = ℕ} 8)))) > (length (BYTES (fun-mem z x)))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i) ∷ (VLOAD V128 (just (SPLAT (mk-sz v-N))) x ao) ∷ []))) (as (List instr) (TRAP ∷ []))
  vload-splat-oob-1 : ∀ (z : state) (i : (uN-fam0 (64))) (v-N : N) (x : idx) (ao : memarg) → 
    ((((proj-uN-0 (size (numtype-addrtype I64)) i) + (proj-uN-0 64 (OFFSET ao))) + (coerce {B = ℕ} ((coerce {B = ℕ} v-N) / (coerce {B = ℕ} 8)))) > (length (BYTES (fun-mem z x)))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i) ∷ (VLOAD V128 (just (SPLAT (mk-sz v-N))) x ao) ∷ []))) (as (List instr) (TRAP ∷ []))
  vload-splat-val-0 : ∀ (z : state) (i : (uN-fam0 (32))) (v-N : N) (x : idx) (ao : memarg) (c : (uN-fam0 (128))) (j : (uN-fam0 (v-N))) (v-M : M) → 
    ((ibytes- v-N j) ≡ (slice (BYTES (fun-mem z x)) ((proj-uN-0 (size (numtype-addrtype I32)) i) + (proj-uN-0 64 (OFFSET ao))) (coerce {B = ℕ} ((coerce {B = ℕ} v-N) / (coerce {B = ℕ} 8))))) →
    (v-N ≡ (jsize Jnn-I32)) →
    ((coerce {B = ℕ} v-M) ≡ ((coerce {B = ℕ} 128) / (coerce {B = ℕ} v-N))) →
    (c ≡ (inv-lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) (replicate v-M (mk-uN (proj-uN-0 v-N j))))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i) ∷ (VLOAD V128 (just (SPLAT (mk-sz v-N))) x ao) ∷ []))) (as (List instr) ((instr-VCONST V128 c) ∷ []))
  vload-splat-val-1 : ∀ (z : state) (i : (uN-fam0 (64))) (v-N : N) (x : idx) (ao : memarg) (c : (uN-fam0 (128))) (j : (uN-fam0 (v-N))) (v-M : M) → 
    ((ibytes- v-N j) ≡ (slice (BYTES (fun-mem z x)) ((proj-uN-0 (size (numtype-addrtype I64)) i) + (proj-uN-0 64 (OFFSET ao))) (coerce {B = ℕ} ((coerce {B = ℕ} v-N) / (coerce {B = ℕ} 8))))) →
    (v-N ≡ (jsize Jnn-I32)) →
    ((coerce {B = ℕ} v-M) ≡ ((coerce {B = ℕ} 128) / (coerce {B = ℕ} v-N))) →
    (c ≡ (inv-lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) (replicate v-M (mk-uN (proj-uN-0 v-N j))))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i) ∷ (VLOAD V128 (just (SPLAT (mk-sz v-N))) x ao) ∷ []))) (as (List instr) ((instr-VCONST V128 c) ∷ []))
  vload-splat-val-2 : ∀ (z : state) (i : (uN-fam0 (32))) (v-N : N) (x : idx) (ao : memarg) (c : (uN-fam0 (128))) (j : (uN-fam0 (v-N))) (v-M : M) → 
    ((ibytes- v-N j) ≡ (slice (BYTES (fun-mem z x)) ((proj-uN-0 (size (numtype-addrtype I32)) i) + (proj-uN-0 64 (OFFSET ao))) (coerce {B = ℕ} ((coerce {B = ℕ} v-N) / (coerce {B = ℕ} 8))))) →
    (v-N ≡ (jsize Jnn-I64)) →
    ((coerce {B = ℕ} v-M) ≡ ((coerce {B = ℕ} 128) / (coerce {B = ℕ} v-N))) →
    (c ≡ (inv-lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) (replicate v-M (mk-uN (proj-uN-0 v-N j))))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i) ∷ (VLOAD V128 (just (SPLAT (mk-sz v-N))) x ao) ∷ []))) (as (List instr) ((instr-VCONST V128 c) ∷ []))
  vload-splat-val-3 : ∀ (z : state) (i : (uN-fam0 (64))) (v-N : N) (x : idx) (ao : memarg) (c : (uN-fam0 (128))) (j : (uN-fam0 (v-N))) (v-M : M) → 
    ((ibytes- v-N j) ≡ (slice (BYTES (fun-mem z x)) ((proj-uN-0 (size (numtype-addrtype I64)) i) + (proj-uN-0 64 (OFFSET ao))) (coerce {B = ℕ} ((coerce {B = ℕ} v-N) / (coerce {B = ℕ} 8))))) →
    (v-N ≡ (jsize Jnn-I64)) →
    ((coerce {B = ℕ} v-M) ≡ ((coerce {B = ℕ} 128) / (coerce {B = ℕ} v-N))) →
    (c ≡ (inv-lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) (replicate v-M (mk-uN (proj-uN-0 v-N j))))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i) ∷ (VLOAD V128 (just (SPLAT (mk-sz v-N))) x ao) ∷ []))) (as (List instr) ((instr-VCONST V128 c) ∷ []))
  vload-splat-val-4 : ∀ (z : state) (i : (uN-fam0 (32))) (v-N : N) (x : idx) (ao : memarg) (c : (uN-fam0 (128))) (j : (uN-fam0 (v-N))) (v-M : M) → 
    ((ibytes- v-N j) ≡ (slice (BYTES (fun-mem z x)) ((proj-uN-0 (size (numtype-addrtype I32)) i) + (proj-uN-0 64 (OFFSET ao))) (coerce {B = ℕ} ((coerce {B = ℕ} v-N) / (coerce {B = ℕ} 8))))) →
    (v-N ≡ (jsize Jnn-I8)) →
    ((coerce {B = ℕ} v-M) ≡ ((coerce {B = ℕ} 128) / (coerce {B = ℕ} v-N))) →
    (c ≡ (inv-lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) (replicate v-M (mk-uN (proj-uN-0 v-N j))))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i) ∷ (VLOAD V128 (just (SPLAT (mk-sz v-N))) x ao) ∷ []))) (as (List instr) ((instr-VCONST V128 c) ∷ []))
  vload-splat-val-5 : ∀ (z : state) (i : (uN-fam0 (64))) (v-N : N) (x : idx) (ao : memarg) (c : (uN-fam0 (128))) (j : (uN-fam0 (v-N))) (v-M : M) → 
    ((ibytes- v-N j) ≡ (slice (BYTES (fun-mem z x)) ((proj-uN-0 (size (numtype-addrtype I64)) i) + (proj-uN-0 64 (OFFSET ao))) (coerce {B = ℕ} ((coerce {B = ℕ} v-N) / (coerce {B = ℕ} 8))))) →
    (v-N ≡ (jsize Jnn-I8)) →
    ((coerce {B = ℕ} v-M) ≡ ((coerce {B = ℕ} 128) / (coerce {B = ℕ} v-N))) →
    (c ≡ (inv-lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) (replicate v-M (mk-uN (proj-uN-0 v-N j))))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i) ∷ (VLOAD V128 (just (SPLAT (mk-sz v-N))) x ao) ∷ []))) (as (List instr) ((instr-VCONST V128 c) ∷ []))
  vload-splat-val-6 : ∀ (z : state) (i : (uN-fam0 (32))) (v-N : N) (x : idx) (ao : memarg) (c : (uN-fam0 (128))) (j : (uN-fam0 (v-N))) (v-M : M) → 
    ((ibytes- v-N j) ≡ (slice (BYTES (fun-mem z x)) ((proj-uN-0 (size (numtype-addrtype I32)) i) + (proj-uN-0 64 (OFFSET ao))) (coerce {B = ℕ} ((coerce {B = ℕ} v-N) / (coerce {B = ℕ} 8))))) →
    (v-N ≡ (jsize Jnn-I16)) →
    ((coerce {B = ℕ} v-M) ≡ ((coerce {B = ℕ} 128) / (coerce {B = ℕ} v-N))) →
    (c ≡ (inv-lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) (replicate v-M (mk-uN (proj-uN-0 v-N j))))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i) ∷ (VLOAD V128 (just (SPLAT (mk-sz v-N))) x ao) ∷ []))) (as (List instr) ((instr-VCONST V128 c) ∷ []))
  vload-splat-val-7 : ∀ (z : state) (i : (uN-fam0 (64))) (v-N : N) (x : idx) (ao : memarg) (c : (uN-fam0 (128))) (j : (uN-fam0 (v-N))) (v-M : M) → 
    ((ibytes- v-N j) ≡ (slice (BYTES (fun-mem z x)) ((proj-uN-0 (size (numtype-addrtype I64)) i) + (proj-uN-0 64 (OFFSET ao))) (coerce {B = ℕ} ((coerce {B = ℕ} v-N) / (coerce {B = ℕ} 8))))) →
    (v-N ≡ (jsize Jnn-I16)) →
    ((coerce {B = ℕ} v-M) ≡ ((coerce {B = ℕ} 128) / (coerce {B = ℕ} v-N))) →
    (c ≡ (inv-lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) (replicate v-M (mk-uN (proj-uN-0 v-N j))))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i) ∷ (VLOAD V128 (just (SPLAT (mk-sz v-N))) x ao) ∷ []))) (as (List instr) ((instr-VCONST V128 c) ∷ []))
  vload-zero-oob-0 : ∀ (z : state) (i : (uN-fam0 (32))) (v-N : N) (x : idx) (ao : memarg) → 
    ((((proj-uN-0 (size (numtype-addrtype I32)) i) + (proj-uN-0 64 (OFFSET ao))) + (coerce {B = ℕ} ((coerce {B = ℕ} v-N) / (coerce {B = ℕ} 8)))) > (length (BYTES (fun-mem z x)))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i) ∷ (VLOAD V128 (just (vloadop--ZERO (mk-sz v-N))) x ao) ∷ []))) (as (List instr) (TRAP ∷ []))
  vload-zero-oob-1 : ∀ (z : state) (i : (uN-fam0 (64))) (v-N : N) (x : idx) (ao : memarg) → 
    ((((proj-uN-0 (size (numtype-addrtype I64)) i) + (proj-uN-0 64 (OFFSET ao))) + (coerce {B = ℕ} ((coerce {B = ℕ} v-N) / (coerce {B = ℕ} 8)))) > (length (BYTES (fun-mem z x)))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i) ∷ (VLOAD V128 (just (vloadop--ZERO (mk-sz v-N))) x ao) ∷ []))) (as (List instr) (TRAP ∷ []))
  vload-zero-val-0 : ∀ (z : state) (i : (uN-fam0 (32))) (v-N : N) (x : idx) (ao : memarg) (c : (uN-fam0 (128))) (j : (uN-fam0 (v-N))) → 
    ((ibytes- v-N j) ≡ (slice (BYTES (fun-mem z x)) ((proj-uN-0 (size (numtype-addrtype I32)) i) + (proj-uN-0 64 (OFFSET ao))) (coerce {B = ℕ} ((coerce {B = ℕ} v-N) / (coerce {B = ℕ} 8))))) →
    (c ≡ (extend-- v-N 128 U j)) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i) ∷ (VLOAD V128 (just (vloadop--ZERO (mk-sz v-N))) x ao) ∷ []))) (as (List instr) ((instr-VCONST V128 c) ∷ []))
  vload-zero-val-1 : ∀ (z : state) (i : (uN-fam0 (64))) (v-N : N) (x : idx) (ao : memarg) (c : (uN-fam0 (128))) (j : (uN-fam0 (v-N))) → 
    ((ibytes- v-N j) ≡ (slice (BYTES (fun-mem z x)) ((proj-uN-0 (size (numtype-addrtype I64)) i) + (proj-uN-0 64 (OFFSET ao))) (coerce {B = ℕ} ((coerce {B = ℕ} v-N) / (coerce {B = ℕ} 8))))) →
    (c ≡ (extend-- v-N 128 U j)) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i) ∷ (VLOAD V128 (just (vloadop--ZERO (mk-sz v-N))) x ao) ∷ []))) (as (List instr) ((instr-VCONST V128 c) ∷ []))
  vload-lane-oob-0 : ∀ (z : state) (i : (uN-fam0 (32))) (c-1 : (uN-fam0 (128))) (v-N : N) (x : idx) (ao : memarg) (j : laneidx) → 
    ((((proj-uN-0 (size (numtype-addrtype I32)) i) + (proj-uN-0 64 (OFFSET ao))) + (coerce {B = ℕ} ((coerce {B = ℕ} v-N) / (coerce {B = ℕ} 8)))) > (length (BYTES (fun-mem z x)))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i) ∷ (instr-VCONST V128 c-1) ∷ (VLOAD-LANE V128 (mk-sz v-N) x ao j) ∷ []))) (as (List instr) (TRAP ∷ []))
  vload-lane-oob-1 : ∀ (z : state) (i : (uN-fam0 (64))) (c-1 : (uN-fam0 (128))) (v-N : N) (x : idx) (ao : memarg) (j : laneidx) → 
    ((((proj-uN-0 (size (numtype-addrtype I64)) i) + (proj-uN-0 64 (OFFSET ao))) + (coerce {B = ℕ} ((coerce {B = ℕ} v-N) / (coerce {B = ℕ} 8)))) > (length (BYTES (fun-mem z x)))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i) ∷ (instr-VCONST V128 c-1) ∷ (VLOAD-LANE V128 (mk-sz v-N) x ao j) ∷ []))) (as (List instr) (TRAP ∷ []))
  vload-lane-val-0 : ∀ (z : state) (i : (uN-fam0 (32))) (c-1 : (uN-fam0 (128))) (v-N : N) (x : idx) (ao : memarg) (j : laneidx) (c : (uN-fam0 (128))) (k : (uN-fam0 (v-N))) (v-M : M) → 
    ((ibytes- v-N k) ≡ (slice (BYTES (fun-mem z x)) ((proj-uN-0 (size (numtype-addrtype I32)) i) + (proj-uN-0 64 (OFFSET ao))) (coerce {B = ℕ} ((coerce {B = ℕ} v-N) / (coerce {B = ℕ} 8))))) →
    (v-N ≡ (jsize Jnn-I32)) →
    ((coerce {B = ℕ} v-M) ≡ ((coerce {B = ℕ} (vsize V128)) / (coerce {B = ℕ} v-N))) →
    (c ≡ (inv-lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) (modify (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) c-1) (proj-uN-0 8 j) (λ (_ : (uN-fam0 (32))) → (mk-uN (proj-uN-0 v-N k)))))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i) ∷ (instr-VCONST V128 c-1) ∷ (VLOAD-LANE V128 (mk-sz v-N) x ao j) ∷ []))) (as (List instr) ((instr-VCONST V128 c) ∷ []))
  vload-lane-val-1 : ∀ (z : state) (i : (uN-fam0 (64))) (c-1 : (uN-fam0 (128))) (v-N : N) (x : idx) (ao : memarg) (j : laneidx) (c : (uN-fam0 (128))) (k : (uN-fam0 (v-N))) (v-M : M) → 
    ((ibytes- v-N k) ≡ (slice (BYTES (fun-mem z x)) ((proj-uN-0 (size (numtype-addrtype I64)) i) + (proj-uN-0 64 (OFFSET ao))) (coerce {B = ℕ} ((coerce {B = ℕ} v-N) / (coerce {B = ℕ} 8))))) →
    (v-N ≡ (jsize Jnn-I32)) →
    ((coerce {B = ℕ} v-M) ≡ ((coerce {B = ℕ} (vsize V128)) / (coerce {B = ℕ} v-N))) →
    (c ≡ (inv-lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) (modify (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) c-1) (proj-uN-0 8 j) (λ (_ : (uN-fam0 (32))) → (mk-uN (proj-uN-0 v-N k)))))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i) ∷ (instr-VCONST V128 c-1) ∷ (VLOAD-LANE V128 (mk-sz v-N) x ao j) ∷ []))) (as (List instr) ((instr-VCONST V128 c) ∷ []))
  vload-lane-val-2 : ∀ (z : state) (i : (uN-fam0 (32))) (c-1 : (uN-fam0 (128))) (v-N : N) (x : idx) (ao : memarg) (j : laneidx) (c : (uN-fam0 (128))) (k : (uN-fam0 (v-N))) (v-M : M) → 
    ((ibytes- v-N k) ≡ (slice (BYTES (fun-mem z x)) ((proj-uN-0 (size (numtype-addrtype I32)) i) + (proj-uN-0 64 (OFFSET ao))) (coerce {B = ℕ} ((coerce {B = ℕ} v-N) / (coerce {B = ℕ} 8))))) →
    (v-N ≡ (jsize Jnn-I64)) →
    ((coerce {B = ℕ} v-M) ≡ ((coerce {B = ℕ} (vsize V128)) / (coerce {B = ℕ} v-N))) →
    (c ≡ (inv-lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) (modify (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) c-1) (proj-uN-0 8 j) (λ (_ : (uN-fam0 (64))) → (mk-uN (proj-uN-0 v-N k)))))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i) ∷ (instr-VCONST V128 c-1) ∷ (VLOAD-LANE V128 (mk-sz v-N) x ao j) ∷ []))) (as (List instr) ((instr-VCONST V128 c) ∷ []))
  vload-lane-val-3 : ∀ (z : state) (i : (uN-fam0 (64))) (c-1 : (uN-fam0 (128))) (v-N : N) (x : idx) (ao : memarg) (j : laneidx) (c : (uN-fam0 (128))) (k : (uN-fam0 (v-N))) (v-M : M) → 
    ((ibytes- v-N k) ≡ (slice (BYTES (fun-mem z x)) ((proj-uN-0 (size (numtype-addrtype I64)) i) + (proj-uN-0 64 (OFFSET ao))) (coerce {B = ℕ} ((coerce {B = ℕ} v-N) / (coerce {B = ℕ} 8))))) →
    (v-N ≡ (jsize Jnn-I64)) →
    ((coerce {B = ℕ} v-M) ≡ ((coerce {B = ℕ} (vsize V128)) / (coerce {B = ℕ} v-N))) →
    (c ≡ (inv-lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) (modify (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) c-1) (proj-uN-0 8 j) (λ (_ : (uN-fam0 (64))) → (mk-uN (proj-uN-0 v-N k)))))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i) ∷ (instr-VCONST V128 c-1) ∷ (VLOAD-LANE V128 (mk-sz v-N) x ao j) ∷ []))) (as (List instr) ((instr-VCONST V128 c) ∷ []))
  vload-lane-val-4 : ∀ (z : state) (i : (uN-fam0 (32))) (c-1 : (uN-fam0 (128))) (v-N : N) (x : idx) (ao : memarg) (j : laneidx) (c : (uN-fam0 (128))) (k : (uN-fam0 (v-N))) (v-M : M) → 
    ((ibytes- v-N k) ≡ (slice (BYTES (fun-mem z x)) ((proj-uN-0 (size (numtype-addrtype I32)) i) + (proj-uN-0 64 (OFFSET ao))) (coerce {B = ℕ} ((coerce {B = ℕ} v-N) / (coerce {B = ℕ} 8))))) →
    (v-N ≡ (jsize Jnn-I8)) →
    ((coerce {B = ℕ} v-M) ≡ ((coerce {B = ℕ} (vsize V128)) / (coerce {B = ℕ} v-N))) →
    (c ≡ (inv-lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) (modify (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) c-1) (proj-uN-0 8 j) (λ (_ : (uN-fam0 (8))) → (mk-uN (proj-uN-0 v-N k)))))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i) ∷ (instr-VCONST V128 c-1) ∷ (VLOAD-LANE V128 (mk-sz v-N) x ao j) ∷ []))) (as (List instr) ((instr-VCONST V128 c) ∷ []))
  vload-lane-val-5 : ∀ (z : state) (i : (uN-fam0 (64))) (c-1 : (uN-fam0 (128))) (v-N : N) (x : idx) (ao : memarg) (j : laneidx) (c : (uN-fam0 (128))) (k : (uN-fam0 (v-N))) (v-M : M) → 
    ((ibytes- v-N k) ≡ (slice (BYTES (fun-mem z x)) ((proj-uN-0 (size (numtype-addrtype I64)) i) + (proj-uN-0 64 (OFFSET ao))) (coerce {B = ℕ} ((coerce {B = ℕ} v-N) / (coerce {B = ℕ} 8))))) →
    (v-N ≡ (jsize Jnn-I8)) →
    ((coerce {B = ℕ} v-M) ≡ ((coerce {B = ℕ} (vsize V128)) / (coerce {B = ℕ} v-N))) →
    (c ≡ (inv-lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) (modify (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) c-1) (proj-uN-0 8 j) (λ (_ : (uN-fam0 (8))) → (mk-uN (proj-uN-0 v-N k)))))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i) ∷ (instr-VCONST V128 c-1) ∷ (VLOAD-LANE V128 (mk-sz v-N) x ao j) ∷ []))) (as (List instr) ((instr-VCONST V128 c) ∷ []))
  vload-lane-val-6 : ∀ (z : state) (i : (uN-fam0 (32))) (c-1 : (uN-fam0 (128))) (v-N : N) (x : idx) (ao : memarg) (j : laneidx) (c : (uN-fam0 (128))) (k : (uN-fam0 (v-N))) (v-M : M) → 
    ((ibytes- v-N k) ≡ (slice (BYTES (fun-mem z x)) ((proj-uN-0 (size (numtype-addrtype I32)) i) + (proj-uN-0 64 (OFFSET ao))) (coerce {B = ℕ} ((coerce {B = ℕ} v-N) / (coerce {B = ℕ} 8))))) →
    (v-N ≡ (jsize Jnn-I16)) →
    ((coerce {B = ℕ} v-M) ≡ ((coerce {B = ℕ} (vsize V128)) / (coerce {B = ℕ} v-N))) →
    (c ≡ (inv-lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) (modify (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) c-1) (proj-uN-0 8 j) (λ (_ : (uN-fam0 (16))) → (mk-uN (proj-uN-0 v-N k)))))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i) ∷ (instr-VCONST V128 c-1) ∷ (VLOAD-LANE V128 (mk-sz v-N) x ao j) ∷ []))) (as (List instr) ((instr-VCONST V128 c) ∷ []))
  vload-lane-val-7 : ∀ (z : state) (i : (uN-fam0 (64))) (c-1 : (uN-fam0 (128))) (v-N : N) (x : idx) (ao : memarg) (j : laneidx) (c : (uN-fam0 (128))) (k : (uN-fam0 (v-N))) (v-M : M) → 
    ((ibytes- v-N k) ≡ (slice (BYTES (fun-mem z x)) ((proj-uN-0 (size (numtype-addrtype I64)) i) + (proj-uN-0 64 (OFFSET ao))) (coerce {B = ℕ} ((coerce {B = ℕ} v-N) / (coerce {B = ℕ} 8))))) →
    (v-N ≡ (jsize Jnn-I16)) →
    ((coerce {B = ℕ} v-M) ≡ ((coerce {B = ℕ} (vsize V128)) / (coerce {B = ℕ} v-N))) →
    (c ≡ (inv-lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) (modify (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) c-1) (proj-uN-0 8 j) (λ (_ : (uN-fam0 (16))) → (mk-uN (proj-uN-0 v-N k)))))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i) ∷ (instr-VCONST V128 c-1) ∷ (VLOAD-LANE V128 (mk-sz v-N) x ao j) ∷ []))) (as (List instr) ((instr-VCONST V128 c) ∷ []))
  memory-size-0 : ∀ (z : state) (x : idx) (v-n : n) (lim : limits) → 
    ((v-n * (64 * (Ki ))) ≡ (length (BYTES (fun-mem z x)))) →
    ((meminst-TYPE (fun-mem z x)) ≡ (PAGE I32 lim)) →
    Step-read (mk-config z (as (List instr) ((MEMORY-SIZE x) ∷ []))) (as (List instr) ((instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ []))
  memory-size-1 : ∀ (z : state) (x : idx) (v-n : n) (lim : limits) → 
    ((v-n * (64 * (Ki ))) ≡ (length (BYTES (fun-mem z x)))) →
    ((meminst-TYPE (fun-mem z x)) ≡ (PAGE I64 lim)) →
    Step-read (mk-config z (as (List instr) ((MEMORY-SIZE x) ∷ []))) (as (List instr) ((instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ []))
  memory-fill-oob-0 : ∀ (z : state) (i : (uN-fam0 (32))) (v-val : val) (v-n : n) (x : idx) → 
    (((proj-uN-0 (size (numtype-addrtype I32)) i) + v-n) > (length (BYTES (fun-mem z x)))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i) ∷ (instr-val v-val) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (MEMORY-FILL x) ∷ []))) (as (List instr) (TRAP ∷ []))
  memory-fill-oob-1 : ∀ (z : state) (i : (uN-fam0 (64))) (v-val : val) (v-n : n) (x : idx) → 
    (((proj-uN-0 (size (numtype-addrtype I64)) i) + v-n) > (length (BYTES (fun-mem z x)))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i) ∷ (instr-val v-val) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (MEMORY-FILL x) ∷ []))) (as (List instr) (TRAP ∷ []))
  memory-fill-zero-0 : ∀ (z : state) (i : (uN-fam0 (32))) (v-val : val) (v-n : n) (x : idx) → 
    (((proj-uN-0 (size (numtype-addrtype I32)) i) + v-n) ≤ (length (BYTES (fun-mem z x)))) →
    (v-n ≡ 0) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i) ∷ (instr-val v-val) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (MEMORY-FILL x) ∷ []))) []
  memory-fill-zero-1 : ∀ (z : state) (i : (uN-fam0 (64))) (v-val : val) (v-n : n) (x : idx) → 
    (((proj-uN-0 (size (numtype-addrtype I64)) i) + v-n) ≤ (length (BYTES (fun-mem z x)))) →
    (v-n ≡ 0) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i) ∷ (instr-val v-val) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (MEMORY-FILL x) ∷ []))) []
  memory-fill-succ-0 : ∀ (z : state) (i : (uN-fam0 (32))) (v-val : val) (v-n : n) (x : idx) → 
    (v-n ≢ 0) →
    (((proj-uN-0 (size (numtype-addrtype I32)) i) + v-n) ≤ (length (BYTES (fun-mem z x)))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i) ∷ (instr-val v-val) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (MEMORY-FILL x) ∷ []))) (as (List instr) ((instr-CONST (numtype-addrtype I32) i) ∷ (instr-val v-val) ∷ (STORE numtype-I32 (just (mk-storeop- (mk-sz 8))) x (memarg0 )) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN ((proj-uN-0 (size (numtype-addrtype I32)) i) + 1))) ∷ (instr-val v-val) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} v-n) – (coerce {B = ℕ} 1))))) ∷ (MEMORY-FILL x) ∷ []))
  memory-fill-succ-1 : ∀ (z : state) (i : (uN-fam0 (64))) (v-val : val) (v-n : n) (x : idx) → 
    (v-n ≢ 0) →
    (((proj-uN-0 (size (numtype-addrtype I64)) i) + v-n) ≤ (length (BYTES (fun-mem z x)))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i) ∷ (instr-val v-val) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (MEMORY-FILL x) ∷ []))) (as (List instr) ((instr-CONST (numtype-addrtype I64) i) ∷ (instr-val v-val) ∷ (STORE numtype-I32 (just (mk-storeop- (mk-sz 8))) x (memarg0 )) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN ((proj-uN-0 (size (numtype-addrtype I64)) i) + 1))) ∷ (instr-val v-val) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} v-n) – (coerce {B = ℕ} 1))))) ∷ (MEMORY-FILL x) ∷ []))
  memory-copy-oob-0 : ∀ (z : state) (i-1 : (uN-fam0 (32))) (i-2 : (uN-fam0 (32))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    ((((proj-uN-0 (size (numtype-addrtype I32)) i-1) + v-n) > (length (BYTES (fun-mem z x-1)))) ⊎ (((proj-uN-0 (size (numtype-addrtype I32)) i-2) + v-n) > (length (BYTES (fun-mem z x-2))))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (MEMORY-COPY x-1 x-2) ∷ []))) (as (List instr) (TRAP ∷ []))
  memory-copy-oob-1 : ∀ (z : state) (i-1 : (uN-fam0 (64))) (i-2 : (uN-fam0 (32))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    ((((proj-uN-0 (size (numtype-addrtype I64)) i-1) + v-n) > (length (BYTES (fun-mem z x-1)))) ⊎ (((proj-uN-0 (size (numtype-addrtype I32)) i-2) + v-n) > (length (BYTES (fun-mem z x-2))))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (MEMORY-COPY x-1 x-2) ∷ []))) (as (List instr) (TRAP ∷ []))
  memory-copy-oob-2 : ∀ (z : state) (i-1 : (uN-fam0 (32))) (i-2 : (uN-fam0 (64))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    ((((proj-uN-0 (size (numtype-addrtype I32)) i-1) + v-n) > (length (BYTES (fun-mem z x-1)))) ⊎ (((proj-uN-0 (size (numtype-addrtype I64)) i-2) + v-n) > (length (BYTES (fun-mem z x-2))))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (MEMORY-COPY x-1 x-2) ∷ []))) (as (List instr) (TRAP ∷ []))
  memory-copy-oob-3 : ∀ (z : state) (i-1 : (uN-fam0 (64))) (i-2 : (uN-fam0 (64))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    ((((proj-uN-0 (size (numtype-addrtype I64)) i-1) + v-n) > (length (BYTES (fun-mem z x-1)))) ⊎ (((proj-uN-0 (size (numtype-addrtype I64)) i-2) + v-n) > (length (BYTES (fun-mem z x-2))))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (MEMORY-COPY x-1 x-2) ∷ []))) (as (List instr) (TRAP ∷ []))
  memory-copy-oob-4 : ∀ (z : state) (i-1 : (uN-fam0 (32))) (i-2 : (uN-fam0 (32))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    ((((proj-uN-0 (size (numtype-addrtype I32)) i-1) + v-n) > (length (BYTES (fun-mem z x-1)))) ⊎ (((proj-uN-0 (size (numtype-addrtype I32)) i-2) + v-n) > (length (BYTES (fun-mem z x-2))))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (MEMORY-COPY x-1 x-2) ∷ []))) (as (List instr) (TRAP ∷ []))
  memory-copy-oob-5 : ∀ (z : state) (i-1 : (uN-fam0 (64))) (i-2 : (uN-fam0 (32))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    ((((proj-uN-0 (size (numtype-addrtype I64)) i-1) + v-n) > (length (BYTES (fun-mem z x-1)))) ⊎ (((proj-uN-0 (size (numtype-addrtype I32)) i-2) + v-n) > (length (BYTES (fun-mem z x-2))))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (MEMORY-COPY x-1 x-2) ∷ []))) (as (List instr) (TRAP ∷ []))
  memory-copy-oob-6 : ∀ (z : state) (i-1 : (uN-fam0 (32))) (i-2 : (uN-fam0 (64))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    ((((proj-uN-0 (size (numtype-addrtype I32)) i-1) + v-n) > (length (BYTES (fun-mem z x-1)))) ⊎ (((proj-uN-0 (size (numtype-addrtype I64)) i-2) + v-n) > (length (BYTES (fun-mem z x-2))))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (MEMORY-COPY x-1 x-2) ∷ []))) (as (List instr) (TRAP ∷ []))
  memory-copy-oob-7 : ∀ (z : state) (i-1 : (uN-fam0 (64))) (i-2 : (uN-fam0 (64))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    ((((proj-uN-0 (size (numtype-addrtype I64)) i-1) + v-n) > (length (BYTES (fun-mem z x-1)))) ⊎ (((proj-uN-0 (size (numtype-addrtype I64)) i-2) + v-n) > (length (BYTES (fun-mem z x-2))))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (MEMORY-COPY x-1 x-2) ∷ []))) (as (List instr) (TRAP ∷ []))
  memory-copy-zero-0 : ∀ (z : state) (i-1 : (uN-fam0 (32))) (i-2 : (uN-fam0 (32))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    ((((proj-uN-0 (size (numtype-addrtype I32)) i-1) + v-n) ≤ (length (BYTES (fun-mem z x-1)))) × (((proj-uN-0 (size (numtype-addrtype I32)) i-2) + v-n) ≤ (length (BYTES (fun-mem z x-2))))) →
    (v-n ≡ 0) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (MEMORY-COPY x-1 x-2) ∷ []))) []
  memory-copy-zero-1 : ∀ (z : state) (i-1 : (uN-fam0 (64))) (i-2 : (uN-fam0 (32))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    ((((proj-uN-0 (size (numtype-addrtype I64)) i-1) + v-n) ≤ (length (BYTES (fun-mem z x-1)))) × (((proj-uN-0 (size (numtype-addrtype I32)) i-2) + v-n) ≤ (length (BYTES (fun-mem z x-2))))) →
    (v-n ≡ 0) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (MEMORY-COPY x-1 x-2) ∷ []))) []
  memory-copy-zero-2 : ∀ (z : state) (i-1 : (uN-fam0 (32))) (i-2 : (uN-fam0 (64))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    ((((proj-uN-0 (size (numtype-addrtype I32)) i-1) + v-n) ≤ (length (BYTES (fun-mem z x-1)))) × (((proj-uN-0 (size (numtype-addrtype I64)) i-2) + v-n) ≤ (length (BYTES (fun-mem z x-2))))) →
    (v-n ≡ 0) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (MEMORY-COPY x-1 x-2) ∷ []))) []
  memory-copy-zero-3 : ∀ (z : state) (i-1 : (uN-fam0 (64))) (i-2 : (uN-fam0 (64))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    ((((proj-uN-0 (size (numtype-addrtype I64)) i-1) + v-n) ≤ (length (BYTES (fun-mem z x-1)))) × (((proj-uN-0 (size (numtype-addrtype I64)) i-2) + v-n) ≤ (length (BYTES (fun-mem z x-2))))) →
    (v-n ≡ 0) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (MEMORY-COPY x-1 x-2) ∷ []))) []
  memory-copy-zero-4 : ∀ (z : state) (i-1 : (uN-fam0 (32))) (i-2 : (uN-fam0 (32))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    ((((proj-uN-0 (size (numtype-addrtype I32)) i-1) + v-n) ≤ (length (BYTES (fun-mem z x-1)))) × (((proj-uN-0 (size (numtype-addrtype I32)) i-2) + v-n) ≤ (length (BYTES (fun-mem z x-2))))) →
    (v-n ≡ 0) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (MEMORY-COPY x-1 x-2) ∷ []))) []
  memory-copy-zero-5 : ∀ (z : state) (i-1 : (uN-fam0 (64))) (i-2 : (uN-fam0 (32))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    ((((proj-uN-0 (size (numtype-addrtype I64)) i-1) + v-n) ≤ (length (BYTES (fun-mem z x-1)))) × (((proj-uN-0 (size (numtype-addrtype I32)) i-2) + v-n) ≤ (length (BYTES (fun-mem z x-2))))) →
    (v-n ≡ 0) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (MEMORY-COPY x-1 x-2) ∷ []))) []
  memory-copy-zero-6 : ∀ (z : state) (i-1 : (uN-fam0 (32))) (i-2 : (uN-fam0 (64))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    ((((proj-uN-0 (size (numtype-addrtype I32)) i-1) + v-n) ≤ (length (BYTES (fun-mem z x-1)))) × (((proj-uN-0 (size (numtype-addrtype I64)) i-2) + v-n) ≤ (length (BYTES (fun-mem z x-2))))) →
    (v-n ≡ 0) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (MEMORY-COPY x-1 x-2) ∷ []))) []
  memory-copy-zero-7 : ∀ (z : state) (i-1 : (uN-fam0 (64))) (i-2 : (uN-fam0 (64))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    ((((proj-uN-0 (size (numtype-addrtype I64)) i-1) + v-n) ≤ (length (BYTES (fun-mem z x-1)))) × (((proj-uN-0 (size (numtype-addrtype I64)) i-2) + v-n) ≤ (length (BYTES (fun-mem z x-2))))) →
    (v-n ≡ 0) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (MEMORY-COPY x-1 x-2) ∷ []))) []
  memory-copy-le-0 : ∀ (z : state) (i-1 : (uN-fam0 (32))) (i-2 : (uN-fam0 (32))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    (v-n ≢ 0) →
    ((((proj-uN-0 (size (numtype-addrtype I32)) i-1) + v-n) ≤ (length (BYTES (fun-mem z x-1)))) × (((proj-uN-0 (size (numtype-addrtype I32)) i-2) + v-n) ≤ (length (BYTES (fun-mem z x-2))))) →
    ((proj-uN-0 (size (numtype-addrtype I32)) i-1) ≤ (proj-uN-0 (size (numtype-addrtype I32)) i-2)) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (MEMORY-COPY x-1 x-2) ∷ []))) (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (LOAD numtype-I32 (just (mk-loadop- (mk-sz 8) U)) x-2 (memarg0 )) ∷ (STORE numtype-I32 (just (mk-storeop- (mk-sz 8))) x-1 (memarg0 )) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN ((proj-uN-0 (size (numtype-addrtype I32)) i-1) + 1))) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN ((proj-uN-0 (size (numtype-addrtype I32)) i-2) + 1))) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} v-n) – (coerce {B = ℕ} 1))))) ∷ (MEMORY-COPY x-1 x-2) ∷ []))
  memory-copy-le-1 : ∀ (z : state) (i-1 : (uN-fam0 (64))) (i-2 : (uN-fam0 (32))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    (v-n ≢ 0) →
    ((((proj-uN-0 (size (numtype-addrtype I64)) i-1) + v-n) ≤ (length (BYTES (fun-mem z x-1)))) × (((proj-uN-0 (size (numtype-addrtype I32)) i-2) + v-n) ≤ (length (BYTES (fun-mem z x-2))))) →
    ((proj-uN-0 (size (numtype-addrtype I64)) i-1) ≤ (proj-uN-0 (size (numtype-addrtype I32)) i-2)) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (MEMORY-COPY x-1 x-2) ∷ []))) (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (LOAD numtype-I32 (just (mk-loadop- (mk-sz 8) U)) x-2 (memarg0 )) ∷ (STORE numtype-I32 (just (mk-storeop- (mk-sz 8))) x-1 (memarg0 )) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN ((proj-uN-0 (size (numtype-addrtype I64)) i-1) + 1))) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN ((proj-uN-0 (size (numtype-addrtype I32)) i-2) + 1))) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} v-n) – (coerce {B = ℕ} 1))))) ∷ (MEMORY-COPY x-1 x-2) ∷ []))
  memory-copy-le-2 : ∀ (z : state) (i-1 : (uN-fam0 (32))) (i-2 : (uN-fam0 (64))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    (v-n ≢ 0) →
    ((((proj-uN-0 (size (numtype-addrtype I32)) i-1) + v-n) ≤ (length (BYTES (fun-mem z x-1)))) × (((proj-uN-0 (size (numtype-addrtype I64)) i-2) + v-n) ≤ (length (BYTES (fun-mem z x-2))))) →
    ((proj-uN-0 (size (numtype-addrtype I32)) i-1) ≤ (proj-uN-0 (size (numtype-addrtype I64)) i-2)) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (MEMORY-COPY x-1 x-2) ∷ []))) (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (LOAD numtype-I32 (just (mk-loadop- (mk-sz 8) U)) x-2 (memarg0 )) ∷ (STORE numtype-I32 (just (mk-storeop- (mk-sz 8))) x-1 (memarg0 )) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN ((proj-uN-0 (size (numtype-addrtype I32)) i-1) + 1))) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN ((proj-uN-0 (size (numtype-addrtype I64)) i-2) + 1))) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} v-n) – (coerce {B = ℕ} 1))))) ∷ (MEMORY-COPY x-1 x-2) ∷ []))
  memory-copy-le-3 : ∀ (z : state) (i-1 : (uN-fam0 (64))) (i-2 : (uN-fam0 (64))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    (v-n ≢ 0) →
    ((((proj-uN-0 (size (numtype-addrtype I64)) i-1) + v-n) ≤ (length (BYTES (fun-mem z x-1)))) × (((proj-uN-0 (size (numtype-addrtype I64)) i-2) + v-n) ≤ (length (BYTES (fun-mem z x-2))))) →
    ((proj-uN-0 (size (numtype-addrtype I64)) i-1) ≤ (proj-uN-0 (size (numtype-addrtype I64)) i-2)) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (MEMORY-COPY x-1 x-2) ∷ []))) (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (LOAD numtype-I32 (just (mk-loadop- (mk-sz 8) U)) x-2 (memarg0 )) ∷ (STORE numtype-I32 (just (mk-storeop- (mk-sz 8))) x-1 (memarg0 )) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN ((proj-uN-0 (size (numtype-addrtype I64)) i-1) + 1))) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN ((proj-uN-0 (size (numtype-addrtype I64)) i-2) + 1))) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} v-n) – (coerce {B = ℕ} 1))))) ∷ (MEMORY-COPY x-1 x-2) ∷ []))
  memory-copy-le-4 : ∀ (z : state) (i-1 : (uN-fam0 (32))) (i-2 : (uN-fam0 (32))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    (v-n ≢ 0) →
    ((((proj-uN-0 (size (numtype-addrtype I32)) i-1) + v-n) ≤ (length (BYTES (fun-mem z x-1)))) × (((proj-uN-0 (size (numtype-addrtype I32)) i-2) + v-n) ≤ (length (BYTES (fun-mem z x-2))))) →
    ((proj-uN-0 (size (numtype-addrtype I32)) i-1) ≤ (proj-uN-0 (size (numtype-addrtype I32)) i-2)) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (MEMORY-COPY x-1 x-2) ∷ []))) (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (LOAD numtype-I32 (just (mk-loadop- (mk-sz 8) U)) x-2 (memarg0 )) ∷ (STORE numtype-I32 (just (mk-storeop- (mk-sz 8))) x-1 (memarg0 )) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN ((proj-uN-0 (size (numtype-addrtype I32)) i-1) + 1))) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN ((proj-uN-0 (size (numtype-addrtype I32)) i-2) + 1))) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} v-n) – (coerce {B = ℕ} 1))))) ∷ (MEMORY-COPY x-1 x-2) ∷ []))
  memory-copy-le-5 : ∀ (z : state) (i-1 : (uN-fam0 (64))) (i-2 : (uN-fam0 (32))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    (v-n ≢ 0) →
    ((((proj-uN-0 (size (numtype-addrtype I64)) i-1) + v-n) ≤ (length (BYTES (fun-mem z x-1)))) × (((proj-uN-0 (size (numtype-addrtype I32)) i-2) + v-n) ≤ (length (BYTES (fun-mem z x-2))))) →
    ((proj-uN-0 (size (numtype-addrtype I64)) i-1) ≤ (proj-uN-0 (size (numtype-addrtype I32)) i-2)) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (MEMORY-COPY x-1 x-2) ∷ []))) (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (LOAD numtype-I32 (just (mk-loadop- (mk-sz 8) U)) x-2 (memarg0 )) ∷ (STORE numtype-I32 (just (mk-storeop- (mk-sz 8))) x-1 (memarg0 )) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN ((proj-uN-0 (size (numtype-addrtype I64)) i-1) + 1))) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN ((proj-uN-0 (size (numtype-addrtype I32)) i-2) + 1))) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} v-n) – (coerce {B = ℕ} 1))))) ∷ (MEMORY-COPY x-1 x-2) ∷ []))
  memory-copy-le-6 : ∀ (z : state) (i-1 : (uN-fam0 (32))) (i-2 : (uN-fam0 (64))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    (v-n ≢ 0) →
    ((((proj-uN-0 (size (numtype-addrtype I32)) i-1) + v-n) ≤ (length (BYTES (fun-mem z x-1)))) × (((proj-uN-0 (size (numtype-addrtype I64)) i-2) + v-n) ≤ (length (BYTES (fun-mem z x-2))))) →
    ((proj-uN-0 (size (numtype-addrtype I32)) i-1) ≤ (proj-uN-0 (size (numtype-addrtype I64)) i-2)) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (MEMORY-COPY x-1 x-2) ∷ []))) (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (LOAD numtype-I32 (just (mk-loadop- (mk-sz 8) U)) x-2 (memarg0 )) ∷ (STORE numtype-I32 (just (mk-storeop- (mk-sz 8))) x-1 (memarg0 )) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN ((proj-uN-0 (size (numtype-addrtype I32)) i-1) + 1))) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN ((proj-uN-0 (size (numtype-addrtype I64)) i-2) + 1))) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} v-n) – (coerce {B = ℕ} 1))))) ∷ (MEMORY-COPY x-1 x-2) ∷ []))
  memory-copy-le-7 : ∀ (z : state) (i-1 : (uN-fam0 (64))) (i-2 : (uN-fam0 (64))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    (v-n ≢ 0) →
    ((((proj-uN-0 (size (numtype-addrtype I64)) i-1) + v-n) ≤ (length (BYTES (fun-mem z x-1)))) × (((proj-uN-0 (size (numtype-addrtype I64)) i-2) + v-n) ≤ (length (BYTES (fun-mem z x-2))))) →
    ((proj-uN-0 (size (numtype-addrtype I64)) i-1) ≤ (proj-uN-0 (size (numtype-addrtype I64)) i-2)) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (MEMORY-COPY x-1 x-2) ∷ []))) (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (LOAD numtype-I32 (just (mk-loadop- (mk-sz 8) U)) x-2 (memarg0 )) ∷ (STORE numtype-I32 (just (mk-storeop- (mk-sz 8))) x-1 (memarg0 )) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN ((proj-uN-0 (size (numtype-addrtype I64)) i-1) + 1))) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN ((proj-uN-0 (size (numtype-addrtype I64)) i-2) + 1))) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} v-n) – (coerce {B = ℕ} 1))))) ∷ (MEMORY-COPY x-1 x-2) ∷ []))
  memory-copy-gt-0 : ∀ (z : state) (i-1 : (uN-fam0 (32))) (i-2 : (uN-fam0 (32))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    ((proj-uN-0 (size (numtype-addrtype I32)) i-1) > (proj-uN-0 (size (numtype-addrtype I32)) i-2)) →
    (v-n ≢ 0) →
    ((((proj-uN-0 (size (numtype-addrtype I32)) i-1) + v-n) ≤ (length (BYTES (fun-mem z x-1)))) × (((proj-uN-0 (size (numtype-addrtype I32)) i-2) + v-n) ≤ (length (BYTES (fun-mem z x-2))))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (MEMORY-COPY x-1 x-2) ∷ []))) (as (List instr) ((instr-CONST (numtype-addrtype I32) (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} ((proj-uN-0 (size (numtype-addrtype I32)) i-1) + v-n)) – (coerce {B = ℕ} 1))))) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} ((proj-uN-0 (size (numtype-addrtype I32)) i-2) + v-n)) – (coerce {B = ℕ} 1))))) ∷ (LOAD numtype-I32 (just (mk-loadop- (mk-sz 8) U)) x-2 (memarg0 )) ∷ (STORE numtype-I32 (just (mk-storeop- (mk-sz 8))) x-1 (memarg0 )) ∷ (instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} v-n) – (coerce {B = ℕ} 1))))) ∷ (MEMORY-COPY x-1 x-2) ∷ []))
  memory-copy-gt-1 : ∀ (z : state) (i-1 : (uN-fam0 (64))) (i-2 : (uN-fam0 (32))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    ((proj-uN-0 (size (numtype-addrtype I64)) i-1) > (proj-uN-0 (size (numtype-addrtype I32)) i-2)) →
    (v-n ≢ 0) →
    ((((proj-uN-0 (size (numtype-addrtype I64)) i-1) + v-n) ≤ (length (BYTES (fun-mem z x-1)))) × (((proj-uN-0 (size (numtype-addrtype I32)) i-2) + v-n) ≤ (length (BYTES (fun-mem z x-2))))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (MEMORY-COPY x-1 x-2) ∷ []))) (as (List instr) ((instr-CONST (numtype-addrtype I64) (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} ((proj-uN-0 (size (numtype-addrtype I64)) i-1) + v-n)) – (coerce {B = ℕ} 1))))) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} ((proj-uN-0 (size (numtype-addrtype I32)) i-2) + v-n)) – (coerce {B = ℕ} 1))))) ∷ (LOAD numtype-I32 (just (mk-loadop- (mk-sz 8) U)) x-2 (memarg0 )) ∷ (STORE numtype-I32 (just (mk-storeop- (mk-sz 8))) x-1 (memarg0 )) ∷ (instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} v-n) – (coerce {B = ℕ} 1))))) ∷ (MEMORY-COPY x-1 x-2) ∷ []))
  memory-copy-gt-2 : ∀ (z : state) (i-1 : (uN-fam0 (32))) (i-2 : (uN-fam0 (64))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    ((proj-uN-0 (size (numtype-addrtype I32)) i-1) > (proj-uN-0 (size (numtype-addrtype I64)) i-2)) →
    (v-n ≢ 0) →
    ((((proj-uN-0 (size (numtype-addrtype I32)) i-1) + v-n) ≤ (length (BYTES (fun-mem z x-1)))) × (((proj-uN-0 (size (numtype-addrtype I64)) i-2) + v-n) ≤ (length (BYTES (fun-mem z x-2))))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (MEMORY-COPY x-1 x-2) ∷ []))) (as (List instr) ((instr-CONST (numtype-addrtype I32) (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} ((proj-uN-0 (size (numtype-addrtype I32)) i-1) + v-n)) – (coerce {B = ℕ} 1))))) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} ((proj-uN-0 (size (numtype-addrtype I64)) i-2) + v-n)) – (coerce {B = ℕ} 1))))) ∷ (LOAD numtype-I32 (just (mk-loadop- (mk-sz 8) U)) x-2 (memarg0 )) ∷ (STORE numtype-I32 (just (mk-storeop- (mk-sz 8))) x-1 (memarg0 )) ∷ (instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} v-n) – (coerce {B = ℕ} 1))))) ∷ (MEMORY-COPY x-1 x-2) ∷ []))
  memory-copy-gt-3 : ∀ (z : state) (i-1 : (uN-fam0 (64))) (i-2 : (uN-fam0 (64))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    ((proj-uN-0 (size (numtype-addrtype I64)) i-1) > (proj-uN-0 (size (numtype-addrtype I64)) i-2)) →
    (v-n ≢ 0) →
    ((((proj-uN-0 (size (numtype-addrtype I64)) i-1) + v-n) ≤ (length (BYTES (fun-mem z x-1)))) × (((proj-uN-0 (size (numtype-addrtype I64)) i-2) + v-n) ≤ (length (BYTES (fun-mem z x-2))))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (MEMORY-COPY x-1 x-2) ∷ []))) (as (List instr) ((instr-CONST (numtype-addrtype I64) (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} ((proj-uN-0 (size (numtype-addrtype I64)) i-1) + v-n)) – (coerce {B = ℕ} 1))))) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} ((proj-uN-0 (size (numtype-addrtype I64)) i-2) + v-n)) – (coerce {B = ℕ} 1))))) ∷ (LOAD numtype-I32 (just (mk-loadop- (mk-sz 8) U)) x-2 (memarg0 )) ∷ (STORE numtype-I32 (just (mk-storeop- (mk-sz 8))) x-1 (memarg0 )) ∷ (instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} v-n) – (coerce {B = ℕ} 1))))) ∷ (MEMORY-COPY x-1 x-2) ∷ []))
  memory-copy-gt-4 : ∀ (z : state) (i-1 : (uN-fam0 (32))) (i-2 : (uN-fam0 (32))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    ((proj-uN-0 (size (numtype-addrtype I32)) i-1) > (proj-uN-0 (size (numtype-addrtype I32)) i-2)) →
    (v-n ≢ 0) →
    ((((proj-uN-0 (size (numtype-addrtype I32)) i-1) + v-n) ≤ (length (BYTES (fun-mem z x-1)))) × (((proj-uN-0 (size (numtype-addrtype I32)) i-2) + v-n) ≤ (length (BYTES (fun-mem z x-2))))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (MEMORY-COPY x-1 x-2) ∷ []))) (as (List instr) ((instr-CONST (numtype-addrtype I32) (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} ((proj-uN-0 (size (numtype-addrtype I32)) i-1) + v-n)) – (coerce {B = ℕ} 1))))) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} ((proj-uN-0 (size (numtype-addrtype I32)) i-2) + v-n)) – (coerce {B = ℕ} 1))))) ∷ (LOAD numtype-I32 (just (mk-loadop- (mk-sz 8) U)) x-2 (memarg0 )) ∷ (STORE numtype-I32 (just (mk-storeop- (mk-sz 8))) x-1 (memarg0 )) ∷ (instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} v-n) – (coerce {B = ℕ} 1))))) ∷ (MEMORY-COPY x-1 x-2) ∷ []))
  memory-copy-gt-5 : ∀ (z : state) (i-1 : (uN-fam0 (64))) (i-2 : (uN-fam0 (32))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    ((proj-uN-0 (size (numtype-addrtype I64)) i-1) > (proj-uN-0 (size (numtype-addrtype I32)) i-2)) →
    (v-n ≢ 0) →
    ((((proj-uN-0 (size (numtype-addrtype I64)) i-1) + v-n) ≤ (length (BYTES (fun-mem z x-1)))) × (((proj-uN-0 (size (numtype-addrtype I32)) i-2) + v-n) ≤ (length (BYTES (fun-mem z x-2))))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (MEMORY-COPY x-1 x-2) ∷ []))) (as (List instr) ((instr-CONST (numtype-addrtype I64) (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} ((proj-uN-0 (size (numtype-addrtype I64)) i-1) + v-n)) – (coerce {B = ℕ} 1))))) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} ((proj-uN-0 (size (numtype-addrtype I32)) i-2) + v-n)) – (coerce {B = ℕ} 1))))) ∷ (LOAD numtype-I32 (just (mk-loadop- (mk-sz 8) U)) x-2 (memarg0 )) ∷ (STORE numtype-I32 (just (mk-storeop- (mk-sz 8))) x-1 (memarg0 )) ∷ (instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I32) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} v-n) – (coerce {B = ℕ} 1))))) ∷ (MEMORY-COPY x-1 x-2) ∷ []))
  memory-copy-gt-6 : ∀ (z : state) (i-1 : (uN-fam0 (32))) (i-2 : (uN-fam0 (64))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    ((proj-uN-0 (size (numtype-addrtype I32)) i-1) > (proj-uN-0 (size (numtype-addrtype I64)) i-2)) →
    (v-n ≢ 0) →
    ((((proj-uN-0 (size (numtype-addrtype I32)) i-1) + v-n) ≤ (length (BYTES (fun-mem z x-1)))) × (((proj-uN-0 (size (numtype-addrtype I64)) i-2) + v-n) ≤ (length (BYTES (fun-mem z x-2))))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (MEMORY-COPY x-1 x-2) ∷ []))) (as (List instr) ((instr-CONST (numtype-addrtype I32) (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} ((proj-uN-0 (size (numtype-addrtype I32)) i-1) + v-n)) – (coerce {B = ℕ} 1))))) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} ((proj-uN-0 (size (numtype-addrtype I64)) i-2) + v-n)) – (coerce {B = ℕ} 1))))) ∷ (LOAD numtype-I32 (just (mk-loadop- (mk-sz 8) U)) x-2 (memarg0 )) ∷ (STORE numtype-I32 (just (mk-storeop- (mk-sz 8))) x-1 (memarg0 )) ∷ (instr-CONST (numtype-addrtype I32) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} v-n) – (coerce {B = ℕ} 1))))) ∷ (MEMORY-COPY x-1 x-2) ∷ []))
  memory-copy-gt-7 : ∀ (z : state) (i-1 : (uN-fam0 (64))) (i-2 : (uN-fam0 (64))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    ((proj-uN-0 (size (numtype-addrtype I64)) i-1) > (proj-uN-0 (size (numtype-addrtype I64)) i-2)) →
    (v-n ≢ 0) →
    ((((proj-uN-0 (size (numtype-addrtype I64)) i-1) + v-n) ≤ (length (BYTES (fun-mem z x-1)))) × (((proj-uN-0 (size (numtype-addrtype I64)) i-2) + v-n) ≤ (length (BYTES (fun-mem z x-2))))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (MEMORY-COPY x-1 x-2) ∷ []))) (as (List instr) ((instr-CONST (numtype-addrtype I64) (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} ((proj-uN-0 (size (numtype-addrtype I64)) i-1) + v-n)) – (coerce {B = ℕ} 1))))) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} ((proj-uN-0 (size (numtype-addrtype I64)) i-2) + v-n)) – (coerce {B = ℕ} 1))))) ∷ (LOAD numtype-I32 (just (mk-loadop- (mk-sz 8) U)) x-2 (memarg0 )) ∷ (STORE numtype-I32 (just (mk-storeop- (mk-sz 8))) x-1 (memarg0 )) ∷ (instr-CONST (numtype-addrtype I64) i-1) ∷ (instr-CONST (numtype-addrtype I64) i-2) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} v-n) – (coerce {B = ℕ} 1))))) ∷ (MEMORY-COPY x-1 x-2) ∷ []))
  memory-init-oob-0 : ∀ (z : state) (i : (uN-fam0 (32))) (j : (uN-fam0 (32))) (v-n : n) (x : idx) (y : idx) → 
    ((((proj-uN-0 (size (numtype-addrtype I32)) i) + v-n) > (length (BYTES (fun-mem z x)))) ⊎ (((proj-uN-0 32 j) + v-n) > (length (datainst-BYTES (fun-data z y))))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i) ∷ (instr-CONST numtype-I32 j) ∷ (instr-CONST numtype-I32 (mk-uN v-n)) ∷ (MEMORY-INIT x y) ∷ []))) (as (List instr) (TRAP ∷ []))
  memory-init-oob-1 : ∀ (z : state) (i : (uN-fam0 (64))) (j : (uN-fam0 (32))) (v-n : n) (x : idx) (y : idx) → 
    ((((proj-uN-0 (size (numtype-addrtype I64)) i) + v-n) > (length (BYTES (fun-mem z x)))) ⊎ (((proj-uN-0 32 j) + v-n) > (length (datainst-BYTES (fun-data z y))))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i) ∷ (instr-CONST numtype-I32 j) ∷ (instr-CONST numtype-I32 (mk-uN v-n)) ∷ (MEMORY-INIT x y) ∷ []))) (as (List instr) (TRAP ∷ []))
  memory-init-zero-0 : ∀ (z : state) (i : (uN-fam0 (32))) (j : (uN-fam0 (32))) (v-n : n) (x : idx) (y : idx) → 
    ((((proj-uN-0 (size (numtype-addrtype I32)) i) + v-n) ≤ (length (BYTES (fun-mem z x)))) × (((proj-uN-0 32 j) + v-n) ≤ (length (datainst-BYTES (fun-data z y))))) →
    (v-n ≡ 0) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i) ∷ (instr-CONST numtype-I32 j) ∷ (instr-CONST numtype-I32 (mk-uN v-n)) ∷ (MEMORY-INIT x y) ∷ []))) []
  memory-init-zero-1 : ∀ (z : state) (i : (uN-fam0 (64))) (j : (uN-fam0 (32))) (v-n : n) (x : idx) (y : idx) → 
    ((((proj-uN-0 (size (numtype-addrtype I64)) i) + v-n) ≤ (length (BYTES (fun-mem z x)))) × (((proj-uN-0 32 j) + v-n) ≤ (length (datainst-BYTES (fun-data z y))))) →
    (v-n ≡ 0) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i) ∷ (instr-CONST numtype-I32 j) ∷ (instr-CONST numtype-I32 (mk-uN v-n)) ∷ (MEMORY-INIT x y) ∷ []))) []
  memory-init-succ-0 : ∀ (z : state) (i : (uN-fam0 (32))) (j : (uN-fam0 (32))) (v-n : n) (x : idx) (y : idx) → 
    ((proj-uN-0 32 j) < (length (datainst-BYTES (fun-data z y)))) →
    (v-n ≢ 0) →
    ((((proj-uN-0 (size (numtype-addrtype I32)) i) + v-n) ≤ (length (BYTES (fun-mem z x)))) × (((proj-uN-0 32 j) + v-n) ≤ (length (datainst-BYTES (fun-data z y))))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i) ∷ (instr-CONST numtype-I32 j) ∷ (instr-CONST numtype-I32 (mk-uN v-n)) ∷ (MEMORY-INIT x y) ∷ []))) (as (List instr) ((instr-CONST (numtype-addrtype I32) i) ∷ (instr-CONST numtype-I32 (mk-uN (coerce {B = (ℕ)} (((datainst-BYTES (fun-data z y)) [ (proj-uN-0 32 j) ]!))))) ∷ (STORE numtype-I32 (just (mk-storeop- (mk-sz 8))) x (memarg0 )) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN ((proj-uN-0 (size (numtype-addrtype I32)) i) + 1))) ∷ (instr-CONST numtype-I32 (mk-uN ((proj-uN-0 32 j) + 1))) ∷ (instr-CONST numtype-I32 (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} v-n) – (coerce {B = ℕ} 1))))) ∷ (MEMORY-INIT x y) ∷ []))
  memory-init-succ-1 : ∀ (z : state) (i : (uN-fam0 (64))) (j : (uN-fam0 (32))) (v-n : n) (x : idx) (y : idx) → 
    ((proj-uN-0 32 j) < (length (datainst-BYTES (fun-data z y)))) →
    (v-n ≢ 0) →
    ((((proj-uN-0 (size (numtype-addrtype I64)) i) + v-n) ≤ (length (BYTES (fun-mem z x)))) × (((proj-uN-0 32 j) + v-n) ≤ (length (datainst-BYTES (fun-data z y))))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i) ∷ (instr-CONST numtype-I32 j) ∷ (instr-CONST numtype-I32 (mk-uN v-n)) ∷ (MEMORY-INIT x y) ∷ []))) (as (List instr) ((instr-CONST (numtype-addrtype I64) i) ∷ (instr-CONST numtype-I32 (mk-uN (coerce {B = (ℕ)} (((datainst-BYTES (fun-data z y)) [ (proj-uN-0 32 j) ]!))))) ∷ (STORE numtype-I32 (just (mk-storeop- (mk-sz 8))) x (memarg0 )) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN ((proj-uN-0 (size (numtype-addrtype I64)) i) + 1))) ∷ (instr-CONST numtype-I32 (mk-uN ((proj-uN-0 32 j) + 1))) ∷ (instr-CONST numtype-I32 (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} v-n) – (coerce {B = ℕ} 1))))) ∷ (MEMORY-INIT x y) ∷ []))
  Step-read--ref-null : ∀ (z : state) (ht : heaptype) → Step-read (mk-config z (as (List instr) ((REF-NULL ht) ∷ []))) (as (List instr) (instr-REF-NULL-ADDR ∷ []))
  Step-read--ref-func : ∀ (z : state) (x : idx) → 
    ((proj-uN-0 32 x) < (length (moduleinst-FUNCS (fun-moduleinst z)))) →
    Step-read (mk-config z (as (List instr) ((REF-FUNC x) ∷ []))) (as (List instr) ((instr-REF-FUNC-ADDR ((moduleinst-FUNCS (fun-moduleinst z)) [ (proj-uN-0 32 x) ]!)) ∷ []))
  ref-test-true : ∀ (s : store) (f : frame) (v-ref : ref) (rt : reftype) → 
    (Ref-ok s v-ref (inst-reftype (MODULE f) rt)) →
    Step-read (mk-config (mk-state s f) (as (List instr) ((instr-ref v-ref) ∷ (REF-TEST rt) ∷ []))) (as (List instr) ((instr-CONST numtype-I32 (mk-uN 1)) ∷ []))
  ref-test-false : ∀ (s : store) (f : frame) (v-ref : ref) (rt : reftype) → 
    (¬ (Step-read-before-ref-test-false (mk-config (mk-state s f) (as (List instr) ((instr-ref v-ref) ∷ (REF-TEST rt) ∷ []))))) →
    Step-read (mk-config (mk-state s f) (as (List instr) ((instr-ref v-ref) ∷ (REF-TEST rt) ∷ []))) (as (List instr) ((instr-CONST numtype-I32 (mk-uN 0)) ∷ []))
  ref-cast-succeed : ∀ (s : store) (f : frame) (v-ref : ref) (rt : reftype) → 
    (Ref-ok s v-ref (inst-reftype (MODULE f) rt)) →
    Step-read (mk-config (mk-state s f) (as (List instr) ((instr-ref v-ref) ∷ (REF-CAST rt) ∷ []))) ((instr-ref v-ref) ∷ [])
  ref-cast-fail : ∀ (s : store) (f : frame) (v-ref : ref) (rt : reftype) → 
    (¬ (Step-read-before-ref-cast-fail (mk-config (mk-state s f) (as (List instr) ((instr-ref v-ref) ∷ (REF-CAST rt) ∷ []))))) →
    Step-read (mk-config (mk-state s f) (as (List instr) ((instr-ref v-ref) ∷ (REF-CAST rt) ∷ []))) (as (List instr) (TRAP ∷ []))
  Step-read--struct-new-default : ∀ (z : state) (x : idx) (val-lst : (List val)) (mut-opt-lst : (List (Maybe mut))) (zt-lst : (List storagetype)) (o0 : (List (Maybe val))) → 
    ((length zt-lst) ≡ (length o0)) →
    Forall₂ (λ (zt : storagetype) (o0 : (Maybe val)) → ((default- (unpack zt)) ≡ (just o0))) zt-lst o0 →
    (Expand (fun-type z x) (comptype-STRUCT (mk-list (zipWith (λ (mut-opt : (Maybe mut)) (zt : storagetype) → (mk-fieldtype mut-opt zt)) mut-opt-lst zt-lst)))) →
    ((length val-lst) ≡ (length o0)) →
    Forall₂ (λ (v-val : val) (o0 : (Maybe val)) → (o0 ≡ (just v-val))) val-lst o0 →
    Step-read (mk-config z (as (List instr) ((STRUCT-NEW-DEFAULT x) ∷ []))) ((map (λ (v-val : val) → (instr-val v-val)) val-lst) ++ (as (List instr) ((STRUCT-NEW x) ∷ [])))
  struct-get-null : ∀ (z : state) (sx-opt : (Maybe sx)) (x : idx) (i : fieldidx) → Step-read (mk-config z (as (List instr) (instr-REF-NULL-ADDR ∷ (STRUCT-GET sx-opt x i) ∷ []))) (as (List instr) (TRAP ∷ []))
  struct-get-struct : ∀ (z : state) (a : addr) (sx-opt : (Maybe sx)) (x : idx) (i : fieldidx) (zt-lst : (List storagetype)) (mut-opt-lst : (List (Maybe mut))) → 
    ((unpackfield- (zt-lst [ (proj-uN-0 32 i) ]!) sx-opt ((FIELDS ((fun-structinst z) [ a ]!)) [ (proj-uN-0 32 i) ]!)) ≢ nothing) →
    ((proj-uN-0 32 i) < (length zt-lst)) →
    ((proj-uN-0 32 i) < (length (FIELDS ((fun-structinst z) [ a ]!)))) →
    (a < (length (fun-structinst z))) →
    (Expand (fun-type z x) (comptype-STRUCT (mk-list (zipWith (λ (mut-opt : (Maybe mut)) (zt : storagetype) → (mk-fieldtype mut-opt zt)) mut-opt-lst zt-lst)))) →
    Step-read (mk-config z (as (List instr) ((instr-REF-STRUCT-ADDR a) ∷ (STRUCT-GET sx-opt x i) ∷ []))) ((instr-val (unwrap! (unpackfield- (zt-lst [ (proj-uN-0 32 i) ]!) sx-opt ((FIELDS ((fun-structinst z) [ a ]!)) [ (proj-uN-0 32 i) ]!)))) ∷ [])
  Step-read--array-new-default : ∀ (z : state) (v-n : n) (x : idx) (v-val : val) (mut-opt : (Maybe mut)) (zt : storagetype) (o0 : (Maybe val)) → 
    ((default- (unpack zt)) ≡ (just o0)) →
    (Expand (fun-type z x) (comptype-ARRAY (mk-fieldtype mut-opt zt))) →
    (o0 ≡ (just v-val)) →
    Step-read (mk-config z (as (List instr) ((instr-CONST numtype-I32 (mk-uN v-n)) ∷ (ARRAY-NEW-DEFAULT x) ∷ []))) ((replicate v-n (instr-val v-val)) ++ (as (List instr) ((ARRAY-NEW-FIXED x (mk-uN v-n)) ∷ [])))
  array-new-elem-oob : ∀ (z : state) (i : (uN-fam0 (32))) (v-n : n) (x : idx) (y : idx) → 
    (((proj-uN-0 32 i) + v-n) > (length (eleminst-REFS (fun-elem z y)))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST numtype-I32 i) ∷ (instr-CONST numtype-I32 (mk-uN v-n)) ∷ (ARRAY-NEW-ELEM x y) ∷ []))) (as (List instr) (TRAP ∷ []))
  array-new-elem-alloc : ∀ (z : state) (i : (uN-fam0 (32))) (v-n : n) (x : idx) (y : idx) (ref-lst : (List ref)) → 
    ((length (ref-lst)) ≡ (v-n)) →
    (ref-lst ≡ (slice (eleminst-REFS (fun-elem z y)) (proj-uN-0 32 i) v-n)) →
    Step-read (mk-config z (as (List instr) ((instr-CONST numtype-I32 i) ∷ (instr-CONST numtype-I32 (mk-uN v-n)) ∷ (ARRAY-NEW-ELEM x y) ∷ []))) ((map (λ (v-ref : ref) → (instr-ref v-ref)) ref-lst) ++ (as (List instr) ((ARRAY-NEW-FIXED x (mk-uN v-n)) ∷ [])))
  array-new-data-oob : ∀ (z : state) (i : (uN-fam0 (32))) (v-n : n) (x : idx) (y : idx) (mut-opt : (Maybe mut)) (zt : storagetype) → 
    (Expand (fun-type z x) (comptype-ARRAY (mk-fieldtype mut-opt zt))) →
    ((zsize zt) ≢ nothing) →
    (((proj-uN-0 32 i) + (coerce {B = ℕ} ((coerce {B = ℕ} (v-n * (unwrap! (zsize zt)))) / (coerce {B = ℕ} 8)))) > (length (datainst-BYTES (fun-data z y)))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST numtype-I32 i) ∷ (instr-CONST numtype-I32 (mk-uN v-n)) ∷ (ARRAY-NEW-DATA x y) ∷ []))) (as (List instr) (TRAP ∷ []))
  array-new-data-num : ∀ (z : state) (i : (uN-fam0 (32))) (v-n : n) (x : idx) (y : idx) (zt : storagetype) (c-lst : (List (lit- zt))) (mut-opt : (Maybe mut)) → 
    ((length (c-lst)) ≡ (v-n)) →
    ((cunpack zt) ≢ nothing) →
    (Expand (fun-type z x) (comptype-ARRAY (mk-fieldtype mut-opt zt))) →
    ((zsize zt) ≢ nothing) →
    ((concatn- byte (map (λ (c : (lit- zt)) → (zbytes- zt c)) c-lst) (coerce {B = ℕ} ((coerce {B = ℕ} (unwrap! (zsize zt))) / (coerce {B = ℕ} 8)))) ≡ (slice (datainst-BYTES (fun-data z y)) (proj-uN-0 32 i) (coerce {B = ℕ} ((coerce {B = ℕ} (v-n * (unwrap! (zsize zt)))) / (coerce {B = ℕ} 8))))) →
    Step-read (mk-config z (as (List instr) ((instr-CONST numtype-I32 i) ∷ (instr-CONST numtype-I32 (mk-uN v-n)) ∷ (ARRAY-NEW-DATA x y) ∷ []))) ((map (λ (c : (lit- zt)) → (const (unwrap! (cunpack zt)) (cunpacknum- zt c))) c-lst) ++ (as (List instr) ((ARRAY-NEW-FIXED x (mk-uN v-n)) ∷ [])))
  array-get-null : ∀ (z : state) (i : (uN-fam0 (32))) (sx-opt : (Maybe sx)) (x : idx) → Step-read (mk-config z (as (List instr) (instr-REF-NULL-ADDR ∷ (instr-CONST numtype-I32 i) ∷ (ARRAY-GET sx-opt x) ∷ []))) (as (List instr) (TRAP ∷ []))
  array-get-oob : ∀ (z : state) (a : addr) (i : (uN-fam0 (32))) (sx-opt : (Maybe sx)) (x : idx) → 
    (a < (length (fun-arrayinst z))) →
    ((proj-uN-0 32 i) ≥ (length (arrayinst-FIELDS ((fun-arrayinst z) [ a ]!)))) →
    Step-read (mk-config z (as (List instr) ((instr-REF-ARRAY-ADDR a) ∷ (instr-CONST numtype-I32 i) ∷ (ARRAY-GET sx-opt x) ∷ []))) (as (List instr) (TRAP ∷ []))
  array-get-array : ∀ (z : state) (a : addr) (i : (uN-fam0 (32))) (sx-opt : (Maybe sx)) (x : idx) (zt : storagetype) (mut-opt : (Maybe mut)) → 
    ((unpackfield- zt sx-opt ((arrayinst-FIELDS ((fun-arrayinst z) [ a ]!)) [ (proj-uN-0 32 i) ]!)) ≢ nothing) →
    ((proj-uN-0 32 i) < (length (arrayinst-FIELDS ((fun-arrayinst z) [ a ]!)))) →
    (a < (length (fun-arrayinst z))) →
    (Expand (fun-type z x) (comptype-ARRAY (mk-fieldtype mut-opt zt))) →
    Step-read (mk-config z (as (List instr) ((instr-REF-ARRAY-ADDR a) ∷ (instr-CONST numtype-I32 i) ∷ (ARRAY-GET sx-opt x) ∷ []))) ((instr-val (unwrap! (unpackfield- zt sx-opt ((arrayinst-FIELDS ((fun-arrayinst z) [ a ]!)) [ (proj-uN-0 32 i) ]!)))) ∷ [])
  array-len-null : ∀ (z : state) → Step-read (mk-config z (as (List instr) (instr-REF-NULL-ADDR ∷ ARRAY-LEN ∷ []))) (as (List instr) (TRAP ∷ []))
  array-len-array : ∀ (z : state) (a : addr) → 
    (a < (length (fun-arrayinst z))) →
    Step-read (mk-config z (as (List instr) ((instr-REF-ARRAY-ADDR a) ∷ ARRAY-LEN ∷ []))) (as (List instr) ((instr-CONST numtype-I32 (mk-uN (length (arrayinst-FIELDS ((fun-arrayinst z) [ a ]!))))) ∷ []))
  array-fill-null : ∀ (z : state) (i : (uN-fam0 (32))) (v-val : val) (v-n : n) (x : idx) → Step-read (mk-config z (as (List instr) (instr-REF-NULL-ADDR ∷ (instr-CONST numtype-I32 i) ∷ (instr-val v-val) ∷ (instr-CONST numtype-I32 (mk-uN v-n)) ∷ (ARRAY-FILL x) ∷ []))) (as (List instr) (TRAP ∷ []))
  array-fill-oob : ∀ (z : state) (a : addr) (i : (uN-fam0 (32))) (v-val : val) (v-n : n) (x : idx) → 
    (a < (length (fun-arrayinst z))) →
    (((proj-uN-0 32 i) + v-n) > (length (arrayinst-FIELDS ((fun-arrayinst z) [ a ]!)))) →
    Step-read (mk-config z (as (List instr) ((instr-REF-ARRAY-ADDR a) ∷ (instr-CONST numtype-I32 i) ∷ (instr-val v-val) ∷ (instr-CONST numtype-I32 (mk-uN v-n)) ∷ (ARRAY-FILL x) ∷ []))) (as (List instr) (TRAP ∷ []))
  array-fill-zero : ∀ (z : state) (a : addr) (i : (uN-fam0 (32))) (v-val : val) (v-n : n) (x : idx) → 
    (a < (length (fun-arrayinst z))) →
    (((proj-uN-0 32 i) + v-n) ≤ (length (arrayinst-FIELDS ((fun-arrayinst z) [ a ]!)))) →
    (v-n ≡ 0) →
    Step-read (mk-config z (as (List instr) ((instr-REF-ARRAY-ADDR a) ∷ (instr-CONST numtype-I32 i) ∷ (instr-val v-val) ∷ (instr-CONST numtype-I32 (mk-uN v-n)) ∷ (ARRAY-FILL x) ∷ []))) []
  array-fill-succ : ∀ (z : state) (a : addr) (i : (uN-fam0 (32))) (v-val : val) (v-n : n) (x : idx) → 
    (v-n ≢ 0) →
    (a < (length (fun-arrayinst z))) →
    (((proj-uN-0 32 i) + v-n) ≤ (length (arrayinst-FIELDS ((fun-arrayinst z) [ a ]!)))) →
    Step-read (mk-config z (as (List instr) ((instr-REF-ARRAY-ADDR a) ∷ (instr-CONST numtype-I32 i) ∷ (instr-val v-val) ∷ (instr-CONST numtype-I32 (mk-uN v-n)) ∷ (ARRAY-FILL x) ∷ []))) (as (List instr) ((instr-REF-ARRAY-ADDR a) ∷ (instr-CONST numtype-I32 i) ∷ (instr-val v-val) ∷ (ARRAY-SET x) ∷ (instr-REF-ARRAY-ADDR a) ∷ (instr-CONST numtype-I32 (mk-uN ((proj-uN-0 32 i) + 1))) ∷ (instr-val v-val) ∷ (instr-CONST numtype-I32 (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} v-n) – (coerce {B = ℕ} 1))))) ∷ (ARRAY-FILL x) ∷ []))
  array-copy-null1 : ∀ (z : state) (i-1 : (uN-fam0 (32))) (v-ref : ref) (i-2 : (uN-fam0 (32))) (v-n : n) (x-1 : idx) (x-2 : idx) → Step-read (mk-config z (as (List instr) (instr-REF-NULL-ADDR ∷ (instr-CONST numtype-I32 i-1) ∷ (instr-ref v-ref) ∷ (instr-CONST numtype-I32 i-2) ∷ (instr-CONST numtype-I32 (mk-uN v-n)) ∷ (ARRAY-COPY x-1 x-2) ∷ []))) (as (List instr) (TRAP ∷ []))
  array-copy-null2 : ∀ (z : state) (v-ref : ref) (i-1 : (uN-fam0 (32))) (i-2 : (uN-fam0 (32))) (v-n : n) (x-1 : idx) (x-2 : idx) → Step-read (mk-config z (as (List instr) ((instr-ref v-ref) ∷ (instr-CONST numtype-I32 i-1) ∷ instr-REF-NULL-ADDR ∷ (instr-CONST numtype-I32 i-2) ∷ (instr-CONST numtype-I32 (mk-uN v-n)) ∷ (ARRAY-COPY x-1 x-2) ∷ []))) (as (List instr) (TRAP ∷ []))
  array-copy-oob1 : ∀ (z : state) (a-1 : addr) (i-1 : (uN-fam0 (32))) (a-2 : addr) (i-2 : (uN-fam0 (32))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    (a-1 < (length (fun-arrayinst z))) →
    (((proj-uN-0 32 i-1) + v-n) > (length (arrayinst-FIELDS ((fun-arrayinst z) [ a-1 ]!)))) →
    Step-read (mk-config z (as (List instr) ((instr-REF-ARRAY-ADDR a-1) ∷ (instr-CONST numtype-I32 i-1) ∷ (instr-REF-ARRAY-ADDR a-2) ∷ (instr-CONST numtype-I32 i-2) ∷ (instr-CONST numtype-I32 (mk-uN v-n)) ∷ (ARRAY-COPY x-1 x-2) ∷ []))) (as (List instr) (TRAP ∷ []))
  array-copy-oob2 : ∀ (z : state) (a-1 : addr) (i-1 : (uN-fam0 (32))) (a-2 : addr) (i-2 : (uN-fam0 (32))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    (a-2 < (length (fun-arrayinst z))) →
    (((proj-uN-0 32 i-2) + v-n) > (length (arrayinst-FIELDS ((fun-arrayinst z) [ a-2 ]!)))) →
    Step-read (mk-config z (as (List instr) ((instr-REF-ARRAY-ADDR a-1) ∷ (instr-CONST numtype-I32 i-1) ∷ (instr-REF-ARRAY-ADDR a-2) ∷ (instr-CONST numtype-I32 i-2) ∷ (instr-CONST numtype-I32 (mk-uN v-n)) ∷ (ARRAY-COPY x-1 x-2) ∷ []))) (as (List instr) (TRAP ∷ []))
  array-copy-zero : ∀ (z : state) (a-1 : addr) (i-1 : (uN-fam0 (32))) (a-2 : addr) (i-2 : (uN-fam0 (32))) (v-n : n) (x-1 : idx) (x-2 : idx) → 
    (a-2 < (length (fun-arrayinst z))) →
    (((proj-uN-0 32 i-2) + v-n) ≤ (length (arrayinst-FIELDS ((fun-arrayinst z) [ a-2 ]!)))) →
    (a-1 < (length (fun-arrayinst z))) →
    (((proj-uN-0 32 i-1) + v-n) ≤ (length (arrayinst-FIELDS ((fun-arrayinst z) [ a-1 ]!)))) →
    (v-n ≡ 0) →
    Step-read (mk-config z (as (List instr) ((instr-REF-ARRAY-ADDR a-1) ∷ (instr-CONST numtype-I32 i-1) ∷ (instr-REF-ARRAY-ADDR a-2) ∷ (instr-CONST numtype-I32 i-2) ∷ (instr-CONST numtype-I32 (mk-uN v-n)) ∷ (ARRAY-COPY x-1 x-2) ∷ []))) []
  array-copy-le : ∀ (z : state) (a-1 : addr) (i-1 : (uN-fam0 (32))) (a-2 : addr) (i-2 : (uN-fam0 (32))) (v-n : n) (x-1 : idx) (x-2 : idx) (sx-opt : (Maybe sx)) (mut-opt : (Maybe mut)) (zt-2 : storagetype) (o0 : (Maybe sx)) → 
    ((fun-sx zt-2) ≡ (just o0)) →
    (v-n ≢ 0) →
    (a-2 < (length (fun-arrayinst z))) →
    (((proj-uN-0 32 i-2) + v-n) ≤ (length (arrayinst-FIELDS ((fun-arrayinst z) [ a-2 ]!)))) →
    (a-1 < (length (fun-arrayinst z))) →
    (((proj-uN-0 32 i-1) + v-n) ≤ (length (arrayinst-FIELDS ((fun-arrayinst z) [ a-1 ]!)))) →
    (Expand (fun-type z x-2) (comptype-ARRAY (mk-fieldtype mut-opt zt-2))) →
    (((proj-uN-0 32 i-1) ≤ (proj-uN-0 32 i-2)) × (sx-opt ≡ o0)) →
    Step-read (mk-config z (as (List instr) ((instr-REF-ARRAY-ADDR a-1) ∷ (instr-CONST numtype-I32 i-1) ∷ (instr-REF-ARRAY-ADDR a-2) ∷ (instr-CONST numtype-I32 i-2) ∷ (instr-CONST numtype-I32 (mk-uN v-n)) ∷ (ARRAY-COPY x-1 x-2) ∷ []))) (as (List instr) ((instr-REF-ARRAY-ADDR a-1) ∷ (instr-CONST numtype-I32 i-1) ∷ (instr-REF-ARRAY-ADDR a-2) ∷ (instr-CONST numtype-I32 i-2) ∷ (ARRAY-GET sx-opt x-2) ∷ (ARRAY-SET x-1) ∷ (instr-REF-ARRAY-ADDR a-1) ∷ (instr-CONST numtype-I32 (mk-uN ((proj-uN-0 32 i-1) + 1))) ∷ (instr-REF-ARRAY-ADDR a-2) ∷ (instr-CONST numtype-I32 (mk-uN ((proj-uN-0 32 i-2) + 1))) ∷ (instr-CONST numtype-I32 (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} v-n) – (coerce {B = ℕ} 1))))) ∷ (ARRAY-COPY x-1 x-2) ∷ []))
  array-copy-gt : ∀ (z : state) (a-1 : addr) (i-1 : (uN-fam0 (32))) (a-2 : addr) (i-2 : (uN-fam0 (32))) (v-n : n) (x-1 : idx) (x-2 : idx) (sx-opt : (Maybe sx)) (mut-opt : (Maybe mut)) (zt-2 : storagetype) (o0 : (Maybe sx)) → 
    ((fun-sx zt-2) ≡ (just o0)) →
    (¬ (Step-read-before-array-copy-gt (mk-config z (as (List instr) ((instr-REF-ARRAY-ADDR a-1) ∷ (instr-CONST numtype-I32 i-1) ∷ (instr-REF-ARRAY-ADDR a-2) ∷ (instr-CONST numtype-I32 i-2) ∷ (instr-CONST numtype-I32 (mk-uN v-n)) ∷ (ARRAY-COPY x-1 x-2) ∷ []))))) →
    (Expand (fun-type z x-2) (comptype-ARRAY (mk-fieldtype mut-opt zt-2))) →
    (sx-opt ≡ o0) →
    Step-read (mk-config z (as (List instr) ((instr-REF-ARRAY-ADDR a-1) ∷ (instr-CONST numtype-I32 i-1) ∷ (instr-REF-ARRAY-ADDR a-2) ∷ (instr-CONST numtype-I32 i-2) ∷ (instr-CONST numtype-I32 (mk-uN v-n)) ∷ (ARRAY-COPY x-1 x-2) ∷ []))) (as (List instr) ((instr-REF-ARRAY-ADDR a-1) ∷ (instr-CONST numtype-I32 (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} ((proj-uN-0 32 i-1) + v-n)) – (coerce {B = ℕ} 1))))) ∷ (instr-REF-ARRAY-ADDR a-2) ∷ (instr-CONST numtype-I32 (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} ((proj-uN-0 32 i-2) + v-n)) – (coerce {B = ℕ} 1))))) ∷ (ARRAY-GET sx-opt x-2) ∷ (ARRAY-SET x-1) ∷ (instr-REF-ARRAY-ADDR a-1) ∷ (instr-CONST numtype-I32 i-1) ∷ (instr-REF-ARRAY-ADDR a-2) ∷ (instr-CONST numtype-I32 i-2) ∷ (instr-CONST numtype-I32 (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} v-n) – (coerce {B = ℕ} 1))))) ∷ (ARRAY-COPY x-1 x-2) ∷ []))
  array-init-elem-null : ∀ (z : state) (i : (uN-fam0 (32))) (j : (uN-fam0 (32))) (v-n : n) (x : idx) (y : idx) → Step-read (mk-config z (as (List instr) (instr-REF-NULL-ADDR ∷ (instr-CONST numtype-I32 i) ∷ (instr-CONST numtype-I32 j) ∷ (instr-CONST numtype-I32 (mk-uN v-n)) ∷ (ARRAY-INIT-ELEM x y) ∷ []))) (as (List instr) (TRAP ∷ []))
  array-init-elem-oob1 : ∀ (z : state) (a : addr) (i : (uN-fam0 (32))) (j : (uN-fam0 (32))) (v-n : n) (x : idx) (y : idx) → 
    (a < (length (fun-arrayinst z))) →
    (((proj-uN-0 32 i) + v-n) > (length (arrayinst-FIELDS ((fun-arrayinst z) [ a ]!)))) →
    Step-read (mk-config z (as (List instr) ((instr-REF-ARRAY-ADDR a) ∷ (instr-CONST numtype-I32 i) ∷ (instr-CONST numtype-I32 j) ∷ (instr-CONST numtype-I32 (mk-uN v-n)) ∷ (ARRAY-INIT-ELEM x y) ∷ []))) (as (List instr) (TRAP ∷ []))
  array-init-elem-oob2 : ∀ (z : state) (a : addr) (i : (uN-fam0 (32))) (j : (uN-fam0 (32))) (v-n : n) (x : idx) (y : idx) → 
    (((proj-uN-0 32 j) + v-n) > (length (eleminst-REFS (fun-elem z y)))) →
    Step-read (mk-config z (as (List instr) ((instr-REF-ARRAY-ADDR a) ∷ (instr-CONST numtype-I32 i) ∷ (instr-CONST numtype-I32 j) ∷ (instr-CONST numtype-I32 (mk-uN v-n)) ∷ (ARRAY-INIT-ELEM x y) ∷ []))) (as (List instr) (TRAP ∷ []))
  array-init-elem-zero : ∀ (z : state) (a : addr) (i : (uN-fam0 (32))) (j : (uN-fam0 (32))) (v-n : n) (x : idx) (y : idx) → 
    (((proj-uN-0 32 j) + v-n) ≤ (length (eleminst-REFS (fun-elem z y)))) →
    (a < (length (fun-arrayinst z))) →
    (((proj-uN-0 32 i) + v-n) ≤ (length (arrayinst-FIELDS ((fun-arrayinst z) [ a ]!)))) →
    (v-n ≡ 0) →
    Step-read (mk-config z (as (List instr) ((instr-REF-ARRAY-ADDR a) ∷ (instr-CONST numtype-I32 i) ∷ (instr-CONST numtype-I32 j) ∷ (instr-CONST numtype-I32 (mk-uN v-n)) ∷ (ARRAY-INIT-ELEM x y) ∷ []))) []
  array-init-elem-succ : ∀ (z : state) (a : addr) (i : (uN-fam0 (32))) (j : (uN-fam0 (32))) (v-n : n) (x : idx) (y : idx) (v-ref : ref) → 
    (v-n ≢ 0) →
    (((proj-uN-0 32 j) + v-n) ≤ (length (eleminst-REFS (fun-elem z y)))) →
    (a < (length (fun-arrayinst z))) →
    (((proj-uN-0 32 i) + v-n) ≤ (length (arrayinst-FIELDS ((fun-arrayinst z) [ a ]!)))) →
    ((proj-uN-0 32 j) < (length (eleminst-REFS (fun-elem z y)))) →
    (v-ref ≡ ((eleminst-REFS (fun-elem z y)) [ (proj-uN-0 32 j) ]!)) →
    Step-read (mk-config z (as (List instr) ((instr-REF-ARRAY-ADDR a) ∷ (instr-CONST numtype-I32 i) ∷ (instr-CONST numtype-I32 j) ∷ (instr-CONST numtype-I32 (mk-uN v-n)) ∷ (ARRAY-INIT-ELEM x y) ∷ []))) (as (List instr) ((instr-REF-ARRAY-ADDR a) ∷ (instr-CONST numtype-I32 i) ∷ (instr-ref v-ref) ∷ (ARRAY-SET x) ∷ (instr-REF-ARRAY-ADDR a) ∷ (instr-CONST numtype-I32 (mk-uN ((proj-uN-0 32 i) + 1))) ∷ (instr-CONST numtype-I32 (mk-uN ((proj-uN-0 32 j) + 1))) ∷ (instr-CONST numtype-I32 (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} v-n) – (coerce {B = ℕ} 1))))) ∷ (ARRAY-INIT-ELEM x y) ∷ []))
  array-init-data-null : ∀ (z : state) (i : (uN-fam0 (32))) (j : (uN-fam0 (32))) (v-n : n) (x : idx) (y : idx) → Step-read (mk-config z (as (List instr) (instr-REF-NULL-ADDR ∷ (instr-CONST numtype-I32 i) ∷ (instr-CONST numtype-I32 j) ∷ (instr-CONST numtype-I32 (mk-uN v-n)) ∷ (ARRAY-INIT-DATA x y) ∷ []))) (as (List instr) (TRAP ∷ []))
  array-init-data-oob1 : ∀ (z : state) (a : addr) (i : (uN-fam0 (32))) (j : (uN-fam0 (32))) (v-n : n) (x : idx) (y : idx) → 
    (a < (length (fun-arrayinst z))) →
    (((proj-uN-0 32 i) + v-n) > (length (arrayinst-FIELDS ((fun-arrayinst z) [ a ]!)))) →
    Step-read (mk-config z (as (List instr) ((instr-REF-ARRAY-ADDR a) ∷ (instr-CONST numtype-I32 i) ∷ (instr-CONST numtype-I32 j) ∷ (instr-CONST numtype-I32 (mk-uN v-n)) ∷ (ARRAY-INIT-DATA x y) ∷ []))) (as (List instr) (TRAP ∷ []))
  array-init-data-oob2 : ∀ (z : state) (a : addr) (i : (uN-fam0 (32))) (j : (uN-fam0 (32))) (v-n : n) (x : idx) (y : idx) (mut-opt : (Maybe mut)) (zt : storagetype) → 
    (Expand (fun-type z x) (comptype-ARRAY (mk-fieldtype mut-opt zt))) →
    ((zsize zt) ≢ nothing) →
    (((proj-uN-0 32 j) + (coerce {B = ℕ} ((coerce {B = ℕ} (v-n * (unwrap! (zsize zt)))) / (coerce {B = ℕ} 8)))) > (length (datainst-BYTES (fun-data z y)))) →
    Step-read (mk-config z (as (List instr) ((instr-REF-ARRAY-ADDR a) ∷ (instr-CONST numtype-I32 i) ∷ (instr-CONST numtype-I32 j) ∷ (instr-CONST numtype-I32 (mk-uN v-n)) ∷ (ARRAY-INIT-DATA x y) ∷ []))) (as (List instr) (TRAP ∷ []))
  array-init-data-zero : ∀ (z : state) (a : addr) (i : (uN-fam0 (32))) (j : (uN-fam0 (32))) (v-n : n) (x : idx) (y : idx) → 
    (¬ (Step-read-before-array-init-data-zero (mk-config z (as (List instr) ((instr-REF-ARRAY-ADDR a) ∷ (instr-CONST numtype-I32 i) ∷ (instr-CONST numtype-I32 j) ∷ (instr-CONST numtype-I32 (mk-uN v-n)) ∷ (ARRAY-INIT-DATA x y) ∷ []))))) →
    (v-n ≡ 0) →
    Step-read (mk-config z (as (List instr) ((instr-REF-ARRAY-ADDR a) ∷ (instr-CONST numtype-I32 i) ∷ (instr-CONST numtype-I32 j) ∷ (instr-CONST numtype-I32 (mk-uN v-n)) ∷ (ARRAY-INIT-DATA x y) ∷ []))) []
  array-init-data-num : ∀ (z : state) (a : addr) (i : (uN-fam0 (32))) (j : (uN-fam0 (32))) (v-n : n) (x : idx) (y : idx) (zt : storagetype) (c : (lit- zt)) (mut-opt : (Maybe mut)) → 
    ((cunpack zt) ≢ nothing) →
    ((zsize zt) ≢ nothing) →
    (¬ (Step-read-before-array-init-data-num (mk-config z (as (List instr) ((instr-REF-ARRAY-ADDR a) ∷ (instr-CONST numtype-I32 i) ∷ (instr-CONST numtype-I32 j) ∷ (instr-CONST numtype-I32 (mk-uN v-n)) ∷ (ARRAY-INIT-DATA x y) ∷ []))))) →
    (Expand (fun-type z x) (comptype-ARRAY (mk-fieldtype mut-opt zt))) →
    ((zbytes- zt c) ≡ (slice (datainst-BYTES (fun-data z y)) (proj-uN-0 32 j) (coerce {B = ℕ} ((coerce {B = ℕ} (unwrap! (zsize zt))) / (coerce {B = ℕ} 8))))) →
    Step-read (mk-config z (as (List instr) ((instr-REF-ARRAY-ADDR a) ∷ (instr-CONST numtype-I32 i) ∷ (instr-CONST numtype-I32 j) ∷ (instr-CONST numtype-I32 (mk-uN v-n)) ∷ (ARRAY-INIT-DATA x y) ∷ []))) (as (List instr) ((instr-REF-ARRAY-ADDR a) ∷ (instr-CONST numtype-I32 i) ∷ (const (unwrap! (cunpack zt)) (cunpacknum- zt c)) ∷ (ARRAY-SET x) ∷ (instr-REF-ARRAY-ADDR a) ∷ (instr-CONST numtype-I32 (mk-uN ((proj-uN-0 32 i) + 1))) ∷ (instr-CONST numtype-I32 (mk-uN ((proj-uN-0 32 j) + (coerce {B = ℕ} ((coerce {B = ℕ} (unwrap! (zsize zt))) / (coerce {B = ℕ} 8)))))) ∷ (instr-CONST numtype-I32 (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} v-n) – (coerce {B = ℕ} 1))))) ∷ (ARRAY-INIT-DATA x y) ∷ []))

{- Inductive Relations Definition at: ../specification/wasm-3.0/4.3-execution.instructions.spectec:5.1-5.88 -}
data Step : config → config → Set where
  pure : ∀ (z : state) (instr-lst : (List instr)) (instr'-lst : (List instr)) → 
    (Step-pure instr-lst instr'-lst) →
    Step (mk-config z instr-lst) (mk-config z instr'-lst)
  read : ∀ (z : state) (instr-lst : (List instr)) (instr'-lst : (List instr)) → 
    (Step-read (mk-config z instr-lst) instr'-lst) →
    Step (mk-config z instr-lst) (mk-config z instr'-lst)
  ctxt-instrs : ∀ (z : state) (val-lst : (List val)) (instr-lst : (List instr)) (instr-1-lst : (List instr)) (z' : state) (instr'-lst : (List instr)) → 
    (Step (mk-config z instr-lst) (mk-config z' instr'-lst)) →
    ((val-lst ≢ []) ⊎ (instr-1-lst ≢ [])) →
    Step (mk-config z ((map (λ (v-val : val) → (instr-val v-val)) val-lst) ++ (instr-lst ++ instr-1-lst))) (mk-config z' ((map (λ (v-val : val) → (instr-val v-val)) val-lst) ++ (instr'-lst ++ instr-1-lst)))
  ctxt-label : ∀ (z : state) (v-n : n) (instr-0-lst : (List instr)) (instr-lst : (List instr)) (z' : state) (instr'-lst : (List instr)) → 
    (Step (mk-config z instr-lst) (mk-config z' instr'-lst)) →
    Step (mk-config z (as (List instr) ((LABEL- v-n instr-0-lst instr-lst) ∷ []))) (mk-config z' (as (List instr) ((LABEL- v-n instr-0-lst instr'-lst) ∷ [])))
  ctxt-handler : ∀ (z : state) (v-n : n) (catch-lst : (List catch)) (instr-lst : (List instr)) (z' : state) (instr'-lst : (List instr)) → 
    (Step (mk-config z instr-lst) (mk-config z' instr'-lst)) →
    Step (mk-config z (as (List instr) ((HANDLER- v-n catch-lst instr-lst) ∷ []))) (mk-config z' (as (List instr) ((HANDLER- v-n catch-lst instr'-lst) ∷ [])))
  ctxt-frame : ∀ (s : store) (f : frame) (v-n : n) (f' : frame) (instr-lst : (List instr)) (s' : store) (f'' : frame) (instr'-lst : (List instr)) → 
    (Step (mk-config (mk-state s f') instr-lst) (mk-config (mk-state s' f'') instr'-lst)) →
    Step (mk-config (mk-state s f) (as (List instr) ((FRAME- v-n f' instr-lst) ∷ []))) (mk-config (mk-state s' f) (as (List instr) ((FRAME- v-n f'' instr'-lst) ∷ [])))
  Step--throw : ∀ (z : state) (v-n : n) (val-lst : (List val)) (x : idx) (exn : exninst) (a : addr) (t-lst : (List valtype)) → 
    ((length (val-lst)) ≡ (v-n)) →
    ((length (t-lst)) ≡ (v-n)) →
    ((as-deftype (taginst-TYPE (fun-tag z x))) ≢ nothing) →
    (Expand (unwrap! (as-deftype (taginst-TYPE (fun-tag z x)))) (comptype-FUNC (mk-list t-lst) (mk-list []))) →
    (a ≡ (length (fun-exninst z))) →
    ((proj-uN-0 32 x) < (length (fun-tagaddr z))) →
    (exn ≡ record { exninst-TAG = ((fun-tagaddr z) [ (proj-uN-0 32 x) ]!) ; exninst-FIELDS = val-lst }) →
    Step (mk-config z ((map (λ (v-val : val) → (instr-val v-val)) val-lst) ++ (as (List instr) ((THROW x) ∷ [])))) (mk-config (add-exninst z (exn ∷ [])) (as (List instr) ((instr-REF-EXN-ADDR a) ∷ THROW-REF ∷ [])))
  Step--local-set : ∀ (z : state) (v-val : val) (x : idx) → Step (mk-config z (as (List instr) ((instr-val v-val) ∷ (LOCAL-SET x) ∷ []))) (mk-config (with-local z x v-val) [])
  Step--global-set : ∀ (z : state) (v-val : val) (x : idx) → Step (mk-config z (as (List instr) ((instr-val v-val) ∷ (GLOBAL-SET x) ∷ []))) (mk-config (with-global z x v-val) [])
  table-set-oob-0 : ∀ (z : state) (i : (uN-fam0 (32))) (v-ref : ref) (x : idx) → 
    ((proj-uN-0 (size (numtype-addrtype I32)) i) ≥ (length (tableinst-REFS (fun-table z x)))) →
    Step (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i) ∷ (instr-ref v-ref) ∷ (TABLE-SET x) ∷ []))) (mk-config z (as (List instr) (TRAP ∷ [])))
  table-set-oob-1 : ∀ (z : state) (i : (uN-fam0 (64))) (v-ref : ref) (x : idx) → 
    ((proj-uN-0 (size (numtype-addrtype I64)) i) ≥ (length (tableinst-REFS (fun-table z x)))) →
    Step (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i) ∷ (instr-ref v-ref) ∷ (TABLE-SET x) ∷ []))) (mk-config z (as (List instr) (TRAP ∷ [])))
  table-set-val-0 : ∀ (z : state) (i : (uN-fam0 (32))) (v-ref : ref) (x : idx) → 
    ((proj-uN-0 (size (numtype-addrtype I32)) i) < (length (tableinst-REFS (fun-table z x)))) →
    Step (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i) ∷ (instr-ref v-ref) ∷ (TABLE-SET x) ∷ []))) (mk-config (with-table z x (proj-uN-0 (size (numtype-addrtype I32)) i) v-ref) [])
  table-set-val-1 : ∀ (z : state) (i : (uN-fam0 (64))) (v-ref : ref) (x : idx) → 
    ((proj-uN-0 (size (numtype-addrtype I64)) i) < (length (tableinst-REFS (fun-table z x)))) →
    Step (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i) ∷ (instr-ref v-ref) ∷ (TABLE-SET x) ∷ []))) (mk-config (with-table z x (proj-uN-0 (size (numtype-addrtype I64)) i) v-ref) [])
  table-grow-succeed-0 : ∀ (z : state) (v-ref : ref) (v-n : n) (x : idx) (ti : tableinst) → 
    ((growtable (fun-table z x) v-n v-ref) ≢ nothing) →
    (ti ≡ (unwrap! (growtable (fun-table z x) v-n v-ref))) →
    Step (mk-config z (as (List instr) ((instr-ref v-ref) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (TABLE-GROW x) ∷ []))) (mk-config (with-tableinst z x ti) (as (List instr) ((instr-CONST (numtype-addrtype I32) (mk-uN (length (tableinst-REFS (fun-table z x))))) ∷ [])))
  table-grow-succeed-1 : ∀ (z : state) (v-ref : ref) (v-n : n) (x : idx) (ti : tableinst) → 
    ((growtable (fun-table z x) v-n v-ref) ≢ nothing) →
    (ti ≡ (unwrap! (growtable (fun-table z x) v-n v-ref))) →
    Step (mk-config z (as (List instr) ((instr-ref v-ref) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (TABLE-GROW x) ∷ []))) (mk-config (with-tableinst z x ti) (as (List instr) ((instr-CONST (numtype-addrtype I64) (mk-uN (length (tableinst-REFS (fun-table z x))))) ∷ [])))
  table-grow-fail-0 : ∀ (z : state) (v-ref : ref) (v-n : n) (x : idx) → Step (mk-config z (as (List instr) ((instr-ref v-ref) ∷ (instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (TABLE-GROW x) ∷ []))) (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) (mk-uN (inv-signed- (size (numtype-addrtype I32)) (0 – (coerce {B = ℕ} 1))))) ∷ [])))
  table-grow-fail-1 : ∀ (z : state) (v-ref : ref) (v-n : n) (x : idx) → Step (mk-config z (as (List instr) ((instr-ref v-ref) ∷ (instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (TABLE-GROW x) ∷ []))) (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) (mk-uN (inv-signed- (size (numtype-addrtype I64)) (0 – (coerce {B = ℕ} 1))))) ∷ [])))
  Step--elem-drop : ∀ (z : state) (x : idx) → Step (mk-config z (as (List instr) ((ELEM-DROP x) ∷ []))) (mk-config (with-elem z x []) [])
  store-num-oob-0 : ∀ (z : state) (i : (uN-fam0 (32))) (nt : numtype) (c : (num- nt)) (x : idx) (ao : memarg) → 
    ((((proj-uN-0 (size (numtype-addrtype I32)) i) + (proj-uN-0 64 (OFFSET ao))) + (coerce {B = ℕ} ((coerce {B = ℕ} (size nt)) / (coerce {B = ℕ} 8)))) > (length (BYTES (fun-mem z x)))) →
    Step (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i) ∷ (instr-CONST nt c) ∷ (STORE nt nothing x ao) ∷ []))) (mk-config z (as (List instr) (TRAP ∷ [])))
  store-num-oob-1 : ∀ (z : state) (i : (uN-fam0 (64))) (nt : numtype) (c : (num- nt)) (x : idx) (ao : memarg) → 
    ((((proj-uN-0 (size (numtype-addrtype I64)) i) + (proj-uN-0 64 (OFFSET ao))) + (coerce {B = ℕ} ((coerce {B = ℕ} (size nt)) / (coerce {B = ℕ} 8)))) > (length (BYTES (fun-mem z x)))) →
    Step (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i) ∷ (instr-CONST nt c) ∷ (STORE nt nothing x ao) ∷ []))) (mk-config z (as (List instr) (TRAP ∷ [])))
  store-num-val-0 : ∀ (z : state) (i : (uN-fam0 (32))) (nt : numtype) (c : (num- nt)) (x : idx) (ao : memarg) (b-lst : (List byte)) → 
    (b-lst ≡ (nbytes- nt c)) →
    Step (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i) ∷ (instr-CONST nt c) ∷ (STORE nt nothing x ao) ∷ []))) (mk-config (with-mem z x ((proj-uN-0 (size (numtype-addrtype I32)) i) + (proj-uN-0 64 (OFFSET ao))) (coerce {B = ℕ} ((coerce {B = ℕ} (size nt)) / (coerce {B = ℕ} 8))) b-lst) [])
  store-num-val-1 : ∀ (z : state) (i : (uN-fam0 (64))) (nt : numtype) (c : (num- nt)) (x : idx) (ao : memarg) (b-lst : (List byte)) → 
    (b-lst ≡ (nbytes- nt c)) →
    Step (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i) ∷ (instr-CONST nt c) ∷ (STORE nt nothing x ao) ∷ []))) (mk-config (with-mem z x ((proj-uN-0 (size (numtype-addrtype I64)) i) + (proj-uN-0 64 (OFFSET ao))) (coerce {B = ℕ} ((coerce {B = ℕ} (size nt)) / (coerce {B = ℕ} 8))) b-lst) [])
  store-pack-oob-0 : ∀ (z : state) (i : (uN-fam0 (32))) (c : (uN-fam0 (32))) (v-n : n) (x : idx) (ao : memarg) → 
    ((((proj-uN-0 (size (numtype-addrtype I32)) i) + (proj-uN-0 64 (OFFSET ao))) + (coerce {B = ℕ} ((coerce {B = ℕ} v-n) / (coerce {B = ℕ} 8)))) > (length (BYTES (fun-mem z x)))) →
    Step (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i) ∷ (instr-CONST (numtype-addrtype I32) c) ∷ (STORE (numtype-addrtype I32) (just (mk-storeop- (mk-sz v-n))) x ao) ∷ []))) (mk-config z (as (List instr) (TRAP ∷ [])))
  store-pack-oob-1 : ∀ (z : state) (i : (uN-fam0 (64))) (c : (uN-fam0 (32))) (v-n : n) (x : idx) (ao : memarg) → 
    ((((proj-uN-0 (size (numtype-addrtype I64)) i) + (proj-uN-0 64 (OFFSET ao))) + (coerce {B = ℕ} ((coerce {B = ℕ} v-n) / (coerce {B = ℕ} 8)))) > (length (BYTES (fun-mem z x)))) →
    Step (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i) ∷ (instr-CONST (numtype-addrtype I32) c) ∷ (STORE (numtype-addrtype I32) (just (mk-storeop- (mk-sz v-n))) x ao) ∷ []))) (mk-config z (as (List instr) (TRAP ∷ [])))
  store-pack-oob-2 : ∀ (z : state) (i : (uN-fam0 (32))) (c : (uN-fam0 (64))) (v-n : n) (x : idx) (ao : memarg) → 
    ((((proj-uN-0 (size (numtype-addrtype I32)) i) + (proj-uN-0 64 (OFFSET ao))) + (coerce {B = ℕ} ((coerce {B = ℕ} v-n) / (coerce {B = ℕ} 8)))) > (length (BYTES (fun-mem z x)))) →
    Step (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i) ∷ (instr-CONST (numtype-addrtype I64) c) ∷ (STORE (numtype-addrtype I64) (just (mk-storeop- (mk-sz v-n))) x ao) ∷ []))) (mk-config z (as (List instr) (TRAP ∷ [])))
  store-pack-oob-3 : ∀ (z : state) (i : (uN-fam0 (64))) (c : (uN-fam0 (64))) (v-n : n) (x : idx) (ao : memarg) → 
    ((((proj-uN-0 (size (numtype-addrtype I64)) i) + (proj-uN-0 64 (OFFSET ao))) + (coerce {B = ℕ} ((coerce {B = ℕ} v-n) / (coerce {B = ℕ} 8)))) > (length (BYTES (fun-mem z x)))) →
    Step (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i) ∷ (instr-CONST (numtype-addrtype I64) c) ∷ (STORE (numtype-addrtype I64) (just (mk-storeop- (mk-sz v-n))) x ao) ∷ []))) (mk-config z (as (List instr) (TRAP ∷ [])))
  store-pack-val-0 : ∀ (z : state) (i : (uN-fam0 (32))) (c : (uN-fam0 (32))) (v-n : n) (x : idx) (ao : memarg) (b-lst : (List byte)) → 
    (b-lst ≡ (ibytes- v-n (wrap-- (size (numtype-addrtype I32)) v-n c))) →
    Step (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i) ∷ (instr-CONST (numtype-addrtype I32) c) ∷ (STORE (numtype-addrtype I32) (just (mk-storeop- (mk-sz v-n))) x ao) ∷ []))) (mk-config (with-mem z x ((proj-uN-0 (size (numtype-addrtype I32)) i) + (proj-uN-0 64 (OFFSET ao))) (coerce {B = ℕ} ((coerce {B = ℕ} v-n) / (coerce {B = ℕ} 8))) b-lst) [])
  store-pack-val-1 : ∀ (z : state) (i : (uN-fam0 (64))) (c : (uN-fam0 (32))) (v-n : n) (x : idx) (ao : memarg) (b-lst : (List byte)) → 
    (b-lst ≡ (ibytes- v-n (wrap-- (size (numtype-addrtype I32)) v-n c))) →
    Step (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i) ∷ (instr-CONST (numtype-addrtype I32) c) ∷ (STORE (numtype-addrtype I32) (just (mk-storeop- (mk-sz v-n))) x ao) ∷ []))) (mk-config (with-mem z x ((proj-uN-0 (size (numtype-addrtype I64)) i) + (proj-uN-0 64 (OFFSET ao))) (coerce {B = ℕ} ((coerce {B = ℕ} v-n) / (coerce {B = ℕ} 8))) b-lst) [])
  store-pack-val-2 : ∀ (z : state) (i : (uN-fam0 (32))) (c : (uN-fam0 (64))) (v-n : n) (x : idx) (ao : memarg) (b-lst : (List byte)) → 
    (b-lst ≡ (ibytes- v-n (wrap-- (size (numtype-addrtype I64)) v-n c))) →
    Step (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i) ∷ (instr-CONST (numtype-addrtype I64) c) ∷ (STORE (numtype-addrtype I64) (just (mk-storeop- (mk-sz v-n))) x ao) ∷ []))) (mk-config (with-mem z x ((proj-uN-0 (size (numtype-addrtype I32)) i) + (proj-uN-0 64 (OFFSET ao))) (coerce {B = ℕ} ((coerce {B = ℕ} v-n) / (coerce {B = ℕ} 8))) b-lst) [])
  store-pack-val-3 : ∀ (z : state) (i : (uN-fam0 (64))) (c : (uN-fam0 (64))) (v-n : n) (x : idx) (ao : memarg) (b-lst : (List byte)) → 
    (b-lst ≡ (ibytes- v-n (wrap-- (size (numtype-addrtype I64)) v-n c))) →
    Step (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i) ∷ (instr-CONST (numtype-addrtype I64) c) ∷ (STORE (numtype-addrtype I64) (just (mk-storeop- (mk-sz v-n))) x ao) ∷ []))) (mk-config (with-mem z x ((proj-uN-0 (size (numtype-addrtype I64)) i) + (proj-uN-0 64 (OFFSET ao))) (coerce {B = ℕ} ((coerce {B = ℕ} v-n) / (coerce {B = ℕ} 8))) b-lst) [])
  vstore-oob-0 : ∀ (z : state) (i : (uN-fam0 (32))) (c : (uN-fam0 (128))) (x : idx) (ao : memarg) → 
    ((((proj-uN-0 (size (numtype-addrtype I32)) i) + (proj-uN-0 64 (OFFSET ao))) + (coerce {B = ℕ} ((coerce {B = ℕ} (vsize V128)) / (coerce {B = ℕ} 8)))) > (length (BYTES (fun-mem z x)))) →
    Step (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i) ∷ (instr-VCONST V128 c) ∷ (VSTORE V128 x ao) ∷ []))) (mk-config z (as (List instr) (TRAP ∷ [])))
  vstore-oob-1 : ∀ (z : state) (i : (uN-fam0 (64))) (c : (uN-fam0 (128))) (x : idx) (ao : memarg) → 
    ((((proj-uN-0 (size (numtype-addrtype I64)) i) + (proj-uN-0 64 (OFFSET ao))) + (coerce {B = ℕ} ((coerce {B = ℕ} (vsize V128)) / (coerce {B = ℕ} 8)))) > (length (BYTES (fun-mem z x)))) →
    Step (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i) ∷ (instr-VCONST V128 c) ∷ (VSTORE V128 x ao) ∷ []))) (mk-config z (as (List instr) (TRAP ∷ [])))
  vstore-val-0 : ∀ (z : state) (i : (uN-fam0 (32))) (c : (uN-fam0 (128))) (x : idx) (ao : memarg) (b-lst : (List byte)) → 
    (b-lst ≡ (vbytes- V128 c)) →
    Step (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i) ∷ (instr-VCONST V128 c) ∷ (VSTORE V128 x ao) ∷ []))) (mk-config (with-mem z x ((proj-uN-0 (size (numtype-addrtype I32)) i) + (proj-uN-0 64 (OFFSET ao))) (coerce {B = ℕ} ((coerce {B = ℕ} (vsize V128)) / (coerce {B = ℕ} 8))) b-lst) [])
  vstore-val-1 : ∀ (z : state) (i : (uN-fam0 (64))) (c : (uN-fam0 (128))) (x : idx) (ao : memarg) (b-lst : (List byte)) → 
    (b-lst ≡ (vbytes- V128 c)) →
    Step (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i) ∷ (instr-VCONST V128 c) ∷ (VSTORE V128 x ao) ∷ []))) (mk-config (with-mem z x ((proj-uN-0 (size (numtype-addrtype I64)) i) + (proj-uN-0 64 (OFFSET ao))) (coerce {B = ℕ} ((coerce {B = ℕ} (vsize V128)) / (coerce {B = ℕ} 8))) b-lst) [])
  vstore-lane-oob-0 : ∀ (z : state) (i : (uN-fam0 (32))) (c : (uN-fam0 (128))) (v-N : N) (x : idx) (ao : memarg) (j : laneidx) → 
    ((((proj-uN-0 (size (numtype-addrtype I32)) i) + (proj-uN-0 64 (OFFSET ao))) + v-N) > (length (BYTES (fun-mem z x)))) →
    Step (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i) ∷ (instr-VCONST V128 c) ∷ (VSTORE-LANE V128 (mk-sz v-N) x ao j) ∷ []))) (mk-config z (as (List instr) (TRAP ∷ [])))
  vstore-lane-oob-1 : ∀ (z : state) (i : (uN-fam0 (64))) (c : (uN-fam0 (128))) (v-N : N) (x : idx) (ao : memarg) (j : laneidx) → 
    ((((proj-uN-0 (size (numtype-addrtype I64)) i) + (proj-uN-0 64 (OFFSET ao))) + v-N) > (length (BYTES (fun-mem z x)))) →
    Step (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i) ∷ (instr-VCONST V128 c) ∷ (VSTORE-LANE V128 (mk-sz v-N) x ao j) ∷ []))) (mk-config z (as (List instr) (TRAP ∷ [])))
  vstore-lane-val-0 : ∀ (z : state) (i : (uN-fam0 (32))) (c : (uN-fam0 (128))) (v-N : N) (x : idx) (ao : memarg) (j : laneidx) (b-lst : (List byte)) (v-M : M) → 
    (v-N ≡ (jsize Jnn-I32)) →
    ((coerce {B = ℕ} v-M) ≡ ((coerce {B = ℕ} 128) / (coerce {B = ℕ} v-N))) →
    ((proj-uN-0 8 j) < (length (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) c))) →
    (b-lst ≡ (ibytes- v-N (mk-uN (proj-uN-0 (lsize (lanetype-Jnn Jnn-I32)) ((lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) c) [ (proj-uN-0 8 j) ]!))))) →
    Step (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i) ∷ (instr-VCONST V128 c) ∷ (VSTORE-LANE V128 (mk-sz v-N) x ao j) ∷ []))) (mk-config (with-mem z x ((proj-uN-0 (size (numtype-addrtype I32)) i) + (proj-uN-0 64 (OFFSET ao))) (coerce {B = ℕ} ((coerce {B = ℕ} v-N) / (coerce {B = ℕ} 8))) b-lst) [])
  vstore-lane-val-1 : ∀ (z : state) (i : (uN-fam0 (64))) (c : (uN-fam0 (128))) (v-N : N) (x : idx) (ao : memarg) (j : laneidx) (b-lst : (List byte)) (v-M : M) → 
    (v-N ≡ (jsize Jnn-I32)) →
    ((coerce {B = ℕ} v-M) ≡ ((coerce {B = ℕ} 128) / (coerce {B = ℕ} v-N))) →
    ((proj-uN-0 8 j) < (length (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) c))) →
    (b-lst ≡ (ibytes- v-N (mk-uN (proj-uN-0 (lsize (lanetype-Jnn Jnn-I32)) ((lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) c) [ (proj-uN-0 8 j) ]!))))) →
    Step (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i) ∷ (instr-VCONST V128 c) ∷ (VSTORE-LANE V128 (mk-sz v-N) x ao j) ∷ []))) (mk-config (with-mem z x ((proj-uN-0 (size (numtype-addrtype I64)) i) + (proj-uN-0 64 (OFFSET ao))) (coerce {B = ℕ} ((coerce {B = ℕ} v-N) / (coerce {B = ℕ} 8))) b-lst) [])
  vstore-lane-val-2 : ∀ (z : state) (i : (uN-fam0 (32))) (c : (uN-fam0 (128))) (v-N : N) (x : idx) (ao : memarg) (j : laneidx) (b-lst : (List byte)) (v-M : M) → 
    (v-N ≡ (jsize Jnn-I64)) →
    ((coerce {B = ℕ} v-M) ≡ ((coerce {B = ℕ} 128) / (coerce {B = ℕ} v-N))) →
    ((proj-uN-0 8 j) < (length (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) c))) →
    (b-lst ≡ (ibytes- v-N (mk-uN (proj-uN-0 (lsize (lanetype-Jnn Jnn-I64)) ((lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) c) [ (proj-uN-0 8 j) ]!))))) →
    Step (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i) ∷ (instr-VCONST V128 c) ∷ (VSTORE-LANE V128 (mk-sz v-N) x ao j) ∷ []))) (mk-config (with-mem z x ((proj-uN-0 (size (numtype-addrtype I32)) i) + (proj-uN-0 64 (OFFSET ao))) (coerce {B = ℕ} ((coerce {B = ℕ} v-N) / (coerce {B = ℕ} 8))) b-lst) [])
  vstore-lane-val-3 : ∀ (z : state) (i : (uN-fam0 (64))) (c : (uN-fam0 (128))) (v-N : N) (x : idx) (ao : memarg) (j : laneidx) (b-lst : (List byte)) (v-M : M) → 
    (v-N ≡ (jsize Jnn-I64)) →
    ((coerce {B = ℕ} v-M) ≡ ((coerce {B = ℕ} 128) / (coerce {B = ℕ} v-N))) →
    ((proj-uN-0 8 j) < (length (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) c))) →
    (b-lst ≡ (ibytes- v-N (mk-uN (proj-uN-0 (lsize (lanetype-Jnn Jnn-I64)) ((lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) c) [ (proj-uN-0 8 j) ]!))))) →
    Step (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i) ∷ (instr-VCONST V128 c) ∷ (VSTORE-LANE V128 (mk-sz v-N) x ao j) ∷ []))) (mk-config (with-mem z x ((proj-uN-0 (size (numtype-addrtype I64)) i) + (proj-uN-0 64 (OFFSET ao))) (coerce {B = ℕ} ((coerce {B = ℕ} v-N) / (coerce {B = ℕ} 8))) b-lst) [])
  vstore-lane-val-4 : ∀ (z : state) (i : (uN-fam0 (32))) (c : (uN-fam0 (128))) (v-N : N) (x : idx) (ao : memarg) (j : laneidx) (b-lst : (List byte)) (v-M : M) → 
    (v-N ≡ (jsize Jnn-I8)) →
    ((coerce {B = ℕ} v-M) ≡ ((coerce {B = ℕ} 128) / (coerce {B = ℕ} v-N))) →
    ((proj-uN-0 8 j) < (length (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) c))) →
    (b-lst ≡ (ibytes- v-N (mk-uN (proj-uN-0 (lsize (lanetype-Jnn Jnn-I8)) ((lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) c) [ (proj-uN-0 8 j) ]!))))) →
    Step (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i) ∷ (instr-VCONST V128 c) ∷ (VSTORE-LANE V128 (mk-sz v-N) x ao j) ∷ []))) (mk-config (with-mem z x ((proj-uN-0 (size (numtype-addrtype I32)) i) + (proj-uN-0 64 (OFFSET ao))) (coerce {B = ℕ} ((coerce {B = ℕ} v-N) / (coerce {B = ℕ} 8))) b-lst) [])
  vstore-lane-val-5 : ∀ (z : state) (i : (uN-fam0 (64))) (c : (uN-fam0 (128))) (v-N : N) (x : idx) (ao : memarg) (j : laneidx) (b-lst : (List byte)) (v-M : M) → 
    (v-N ≡ (jsize Jnn-I8)) →
    ((coerce {B = ℕ} v-M) ≡ ((coerce {B = ℕ} 128) / (coerce {B = ℕ} v-N))) →
    ((proj-uN-0 8 j) < (length (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) c))) →
    (b-lst ≡ (ibytes- v-N (mk-uN (proj-uN-0 (lsize (lanetype-Jnn Jnn-I8)) ((lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) c) [ (proj-uN-0 8 j) ]!))))) →
    Step (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i) ∷ (instr-VCONST V128 c) ∷ (VSTORE-LANE V128 (mk-sz v-N) x ao j) ∷ []))) (mk-config (with-mem z x ((proj-uN-0 (size (numtype-addrtype I64)) i) + (proj-uN-0 64 (OFFSET ao))) (coerce {B = ℕ} ((coerce {B = ℕ} v-N) / (coerce {B = ℕ} 8))) b-lst) [])
  vstore-lane-val-6 : ∀ (z : state) (i : (uN-fam0 (32))) (c : (uN-fam0 (128))) (v-N : N) (x : idx) (ao : memarg) (j : laneidx) (b-lst : (List byte)) (v-M : M) → 
    (v-N ≡ (jsize Jnn-I16)) →
    ((coerce {B = ℕ} v-M) ≡ ((coerce {B = ℕ} 128) / (coerce {B = ℕ} v-N))) →
    ((proj-uN-0 8 j) < (length (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) c))) →
    (b-lst ≡ (ibytes- v-N (mk-uN (proj-uN-0 (lsize (lanetype-Jnn Jnn-I16)) ((lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) c) [ (proj-uN-0 8 j) ]!))))) →
    Step (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) i) ∷ (instr-VCONST V128 c) ∷ (VSTORE-LANE V128 (mk-sz v-N) x ao j) ∷ []))) (mk-config (with-mem z x ((proj-uN-0 (size (numtype-addrtype I32)) i) + (proj-uN-0 64 (OFFSET ao))) (coerce {B = ℕ} ((coerce {B = ℕ} v-N) / (coerce {B = ℕ} 8))) b-lst) [])
  vstore-lane-val-7 : ∀ (z : state) (i : (uN-fam0 (64))) (c : (uN-fam0 (128))) (v-N : N) (x : idx) (ao : memarg) (j : laneidx) (b-lst : (List byte)) (v-M : M) → 
    (v-N ≡ (jsize Jnn-I16)) →
    ((coerce {B = ℕ} v-M) ≡ ((coerce {B = ℕ} 128) / (coerce {B = ℕ} v-N))) →
    ((proj-uN-0 8 j) < (length (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) c))) →
    (b-lst ≡ (ibytes- v-N (mk-uN (proj-uN-0 (lsize (lanetype-Jnn Jnn-I16)) ((lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) c) [ (proj-uN-0 8 j) ]!))))) →
    Step (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) i) ∷ (instr-VCONST V128 c) ∷ (VSTORE-LANE V128 (mk-sz v-N) x ao j) ∷ []))) (mk-config (with-mem z x ((proj-uN-0 (size (numtype-addrtype I64)) i) + (proj-uN-0 64 (OFFSET ao))) (coerce {B = ℕ} ((coerce {B = ℕ} v-N) / (coerce {B = ℕ} 8))) b-lst) [])
  memory-grow-succeed-0 : ∀ (z : state) (v-n : n) (x : idx) (mi : meminst) → 
    ((growmem (fun-mem z x) v-n) ≢ nothing) →
    (mi ≡ (unwrap! (growmem (fun-mem z x) v-n))) →
    Step (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (MEMORY-GROW x) ∷ []))) (mk-config (with-meminst z x mi) (as (List instr) ((instr-CONST (numtype-addrtype I32) (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} (length (BYTES (fun-mem z x)))) / (coerce {B = ℕ} (64 * (Ki ))))))) ∷ [])))
  memory-grow-succeed-1 : ∀ (z : state) (v-n : n) (x : idx) (mi : meminst) → 
    ((growmem (fun-mem z x) v-n) ≢ nothing) →
    (mi ≡ (unwrap! (growmem (fun-mem z x) v-n))) →
    Step (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (MEMORY-GROW x) ∷ []))) (mk-config (with-meminst z x mi) (as (List instr) ((instr-CONST (numtype-addrtype I64) (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} (length (BYTES (fun-mem z x)))) / (coerce {B = ℕ} (64 * (Ki ))))))) ∷ [])))
  memory-grow-fail-0 : ∀ (z : state) (v-n : n) (x : idx) → Step (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) (mk-uN v-n)) ∷ (MEMORY-GROW x) ∷ []))) (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I32) (mk-uN (inv-signed- (size (numtype-addrtype I32)) (0 – (coerce {B = ℕ} 1))))) ∷ [])))
  memory-grow-fail-1 : ∀ (z : state) (v-n : n) (x : idx) → Step (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) (mk-uN v-n)) ∷ (MEMORY-GROW x) ∷ []))) (mk-config z (as (List instr) ((instr-CONST (numtype-addrtype I64) (mk-uN (inv-signed- (size (numtype-addrtype I64)) (0 – (coerce {B = ℕ} 1))))) ∷ [])))
  Step--data-drop : ∀ (z : state) (x : idx) → Step (mk-config z (as (List instr) ((DATA-DROP x) ∷ []))) (mk-config (with-data z x []) [])
  Step--struct-new : ∀ (z : state) (v-n : n) (val-lst : (List val)) (x : idx) (si : structinst) (a : addr) (mut-opt-lst : (List (Maybe mut))) (zt-lst : (List storagetype)) → 
    ((length (val-lst)) ≡ (v-n)) →
    ((length (mut-opt-lst)) ≡ (v-n)) →
    ((length (zt-lst)) ≡ (v-n)) →
    (Expand (fun-type z x) (comptype-STRUCT (mk-list (zipWith (λ (mut-opt : (Maybe mut)) (zt : storagetype) → (mk-fieldtype mut-opt zt)) mut-opt-lst zt-lst)))) →
    (a ≡ (length (fun-structinst z))) →
    Forall₂ (λ (v-val : val) (zt : storagetype) → ((packfield- zt v-val) ≢ nothing)) val-lst zt-lst →
    (si ≡ record { structinst-TYPE = (fun-type z x) ; FIELDS = (zipWith (λ (v-val : val) (zt : storagetype) → (unwrap! (packfield- zt v-val))) val-lst zt-lst) }) →
    Step (mk-config z ((map (λ (v-val : val) → (instr-val v-val)) val-lst) ++ (as (List instr) ((STRUCT-NEW x) ∷ [])))) (mk-config (add-structinst z (si ∷ [])) (as (List instr) ((instr-REF-STRUCT-ADDR a) ∷ [])))
  struct-set-null : ∀ (z : state) (v-val : val) (x : idx) (i : fieldidx) → Step (mk-config z (as (List instr) (instr-REF-NULL-ADDR ∷ (instr-val v-val) ∷ (STRUCT-SET x i) ∷ []))) (mk-config z (as (List instr) (TRAP ∷ [])))
  struct-set-struct : ∀ (z : state) (a : addr) (v-val : val) (x : idx) (i : fieldidx) (zt-lst : (List storagetype)) (mut-opt-lst : (List (Maybe mut))) → 
    ((packfield- (zt-lst [ (proj-uN-0 32 i) ]!) v-val) ≢ nothing) →
    ((proj-uN-0 32 i) < (length zt-lst)) →
    (Expand (fun-type z x) (comptype-STRUCT (mk-list (zipWith (λ (mut-opt : (Maybe mut)) (zt : storagetype) → (mk-fieldtype mut-opt zt)) mut-opt-lst zt-lst)))) →
    Step (mk-config z (as (List instr) ((instr-REF-STRUCT-ADDR a) ∷ (instr-val v-val) ∷ (STRUCT-SET x i) ∷ []))) (mk-config (with-struct z a (proj-uN-0 32 i) (unwrap! (packfield- (zt-lst [ (proj-uN-0 32 i) ]!) v-val))) [])
  Step--array-new-fixed : ∀ (z : state) (v-n : n) (val-lst : (List val)) (x : idx) (ai : arrayinst) (a : addr) (mut-opt : (Maybe mut)) (zt : storagetype) → 
    ((length (val-lst)) ≡ (v-n)) →
    (Expand (fun-type z x) (comptype-ARRAY (mk-fieldtype mut-opt zt))) →
    Forall (λ (v-val : val) → ((packfield- zt v-val) ≢ nothing)) val-lst →
    ((a ≡ (length (fun-arrayinst z))) × (ai ≡ record { arrayinst-TYPE = (fun-type z x) ; arrayinst-FIELDS = (map (λ (v-val : val) → (unwrap! (packfield- zt v-val))) val-lst) })) →
    Step (mk-config z ((map (λ (v-val : val) → (instr-val v-val)) val-lst) ++ (as (List instr) ((ARRAY-NEW-FIXED x (mk-uN v-n)) ∷ [])))) (mk-config (add-arrayinst z (ai ∷ [])) (as (List instr) ((instr-REF-ARRAY-ADDR a) ∷ [])))
  array-set-null : ∀ (z : state) (i : (uN-fam0 (32))) (v-val : val) (x : idx) → Step (mk-config z (as (List instr) (instr-REF-NULL-ADDR ∷ (instr-CONST numtype-I32 i) ∷ (instr-val v-val) ∷ (ARRAY-SET x) ∷ []))) (mk-config z (as (List instr) (TRAP ∷ [])))
  array-set-oob : ∀ (z : state) (a : addr) (i : (uN-fam0 (32))) (v-val : val) (x : idx) → 
    (a < (length (fun-arrayinst z))) →
    ((proj-uN-0 32 i) ≥ (length (arrayinst-FIELDS ((fun-arrayinst z) [ a ]!)))) →
    Step (mk-config z (as (List instr) ((instr-REF-ARRAY-ADDR a) ∷ (instr-CONST numtype-I32 i) ∷ (instr-val v-val) ∷ (ARRAY-SET x) ∷ []))) (mk-config z (as (List instr) (TRAP ∷ [])))
  array-set-array : ∀ (z : state) (a : addr) (i : (uN-fam0 (32))) (v-val : val) (x : idx) (zt : storagetype) (mut-opt : (Maybe mut)) → 
    ((packfield- zt v-val) ≢ nothing) →
    (Expand (fun-type z x) (comptype-ARRAY (mk-fieldtype mut-opt zt))) →
    Step (mk-config z (as (List instr) ((instr-REF-ARRAY-ADDR a) ∷ (instr-CONST numtype-I32 i) ∷ (instr-val v-val) ∷ (ARRAY-SET x) ∷ []))) (mk-config (with-array z a (proj-uN-0 32 i) (unwrap! (packfield- zt v-val))) [])

{- Inductive Relations Definition at: ../specification/wasm-3.0/4.3-execution.instructions.spectec:8.1-8.92 -}
data Steps : config → config → Set where
  Steps--refl : ∀ (z : state) (instr-lst : (List instr)) → Steps (mk-config z instr-lst) (mk-config z instr-lst)
  Steps--trans : ∀ (z : state) (instr-lst : (List instr)) (z'' : state) (instr''-lst : (List instr)) (z' : state) (instr'-lst : (List instr)) → 
    (Step (mk-config z instr-lst) (mk-config z' instr'-lst)) →
    (Steps (mk-config z' instr'-lst) (mk-config z'' instr''-lst)) →
    Steps (mk-config z instr-lst) (mk-config z'' instr''-lst)

{- Inductive Relations Definition at: ../specification/wasm-3.0/4.3-execution.instructions.spectec:1105.1-1105.108 -}
data Eval-expr : state → expr → state → (List val) → Set where
  mk-Eval-expr : ∀ (z : state) (instr-lst : (List instr)) (z' : state) (val-lst : (List val)) → 
    (Steps (mk-config z instr-lst) (mk-config z' (map (λ (v-val : val) → (instr-val v-val)) val-lst))) →
    Eval-expr z instr-lst z' val-lst

{- Auxiliary Definition at: ../specification/wasm-3.0/4.4-execution.modules.spectec:7.1-7.63 -}
postulate alloctypes : ∀ (var-0-lst : (List type)) → (List deftype)

{- Auxiliary Definition at: ../specification/wasm-3.0/4.4-execution.modules.spectec:15.1-15.49 -}
postulate alloctag : ∀ (v-store : store) (v-tagtype : tagtype) → (store × tagaddr)

{- Auxiliary Definition at: ../specification/wasm-3.0/4.4-execution.modules.spectec:20.1-20.102 -}
{-# TERMINATING #-}
alloctags : (v-store : store) (var-0-lst : (List tagtype)) → (store × (List tagaddr))
alloctags s [] = (s , [])
alloctags s (v-tagtype ∷ tagtype'-lst) = let (s-1 , ja) = (alloctag s v-tagtype) in let (s-2 , ja'-lst) = (alloctags s-1 tagtype'-lst) in (s-2 , ((ja ∷ []) ++ ja'-lst))
alloctags v-store var-0-lst = (default-val , [])

{- Auxiliary Definition at: ../specification/wasm-3.0/4.4-execution.modules.spectec:26.1-26.63 -}
postulate allocglobal : ∀ (v-store : store) (v-globaltype : globaltype) (v-val : val) → (store × globaladdr)

{- Auxiliary Definition at: ../specification/wasm-3.0/4.4-execution.modules.spectec:31.1-31.122 -}
{-# TERMINATING #-}
allocglobals : (v-store : store) (var-0-lst : (List globaltype)) (var-1-lst : (List val)) → (store × (List globaladdr))
allocglobals s [] [] = (s , [])
allocglobals s (v-globaltype ∷ globaltype'-lst) (v-val ∷ val'-lst) = let (s-1 , ga) = (allocglobal s v-globaltype v-val) in let (s-2 , ga'-lst) = (allocglobals s-1 globaltype'-lst val'-lst) in (s-2 , ((ga ∷ []) ++ ga'-lst))
allocglobals v-store var-0-lst var-1-lst = (default-val , [])

{- Auxiliary Definition at: ../specification/wasm-3.0/4.4-execution.modules.spectec:37.1-37.49 -}
postulate allocmem : ∀ (v-store : store) (v-memtype : memtype) → (store × memaddr)

{- Auxiliary Definition at: ../specification/wasm-3.0/4.4-execution.modules.spectec:42.1-42.102 -}
{-# TERMINATING #-}
allocmems : (v-store : store) (var-0-lst : (List memtype)) → (store × (List memaddr))
allocmems s [] = (s , [])
allocmems s (v-memtype ∷ memtype'-lst) = let (s-1 , ma) = (allocmem s v-memtype) in let (s-2 , ma'-lst) = (allocmems s-1 memtype'-lst) in (s-2 , ((ma ∷ []) ++ ma'-lst))
allocmems v-store var-0-lst = (default-val , [])

{- Auxiliary Definition at: ../specification/wasm-3.0/4.4-execution.modules.spectec:48.1-48.60 -}
postulate alloctable : ∀ (v-store : store) (v-tabletype : tabletype) (v-ref : ref) → (store × tableaddr)

{- Auxiliary Definition at: ../specification/wasm-3.0/4.4-execution.modules.spectec:53.1-53.118 -}
{-# TERMINATING #-}
alloctables : (v-store : store) (var-0-lst : (List tabletype)) (var-1-lst : (List ref)) → (store × (List tableaddr))
alloctables s [] [] = (s , [])
alloctables s (v-tabletype ∷ tabletype'-lst) (v-ref ∷ ref'-lst) = let (s-1 , ta) = (alloctable s v-tabletype v-ref) in let (s-2 , ta'-lst) = (alloctables s-1 tabletype'-lst ref'-lst) in (s-2 , ((ta ∷ []) ++ ta'-lst))
alloctables v-store var-0-lst var-1-lst = (default-val , [])

{- Auxiliary Definition at: ../specification/wasm-3.0/4.4-execution.modules.spectec:59.1-59.73 -}
postulate allocfunc : ∀ (v-store : store) (v-deftype : deftype) (v-funccode : funccode) (v-moduleinst : moduleinst) → (store × funcaddr)

{- Auxiliary Definition at: ../specification/wasm-3.0/4.4-execution.modules.spectec:64.1-64.133 -}
{-# TERMINATING #-}
allocfuncs : (v-store : store) (var-0-lst : (List deftype)) (var-1-lst : (List funccode)) (var-2-lst : (List moduleinst)) → (store × (List funcaddr))
allocfuncs s [] [] [] = (s , [])
allocfuncs s (dt ∷ dt'-lst) (v-funccode ∷ funccode'-lst) (v-moduleinst ∷ moduleinst'-lst) = let (s-1 , fa) = (allocfunc s dt v-funccode v-moduleinst) in let (s-2 , fa'-lst) = (allocfuncs s-1 dt'-lst funccode'-lst moduleinst'-lst) in (s-2 , ((fa ∷ []) ++ fa'-lst))
allocfuncs v-store var-0-lst var-1-lst var-2-lst = (default-val , [])

{- Auxiliary Definition at: ../specification/wasm-3.0/4.4-execution.modules.spectec:70.1-70.59 -}
postulate allocdata : ∀ (v-store : store) (v-datatype : datatype) (var-0-lst : (List byte)) → (store × dataaddr)

{- Auxiliary Definition at: ../specification/wasm-3.0/4.4-execution.modules.spectec:75.1-75.118 -}
{-# TERMINATING #-}
allocdatas : (v-store : store) (var-0-lst : (List datatype)) (var-1-lst-lst : (List (List byte))) → (store × (List dataaddr))
allocdatas s [] [] = (s , [])
allocdatas s (ok ∷ ok'-lst) (b-lst ∷ b'-lst-lst) = let (s-1 , da) = (allocdata s ok b-lst) in let (s-2 , da'-lst) = (allocdatas s-1 ok'-lst b'-lst-lst) in (s-2 , ((da ∷ []) ++ da'-lst))
allocdatas v-store var-0-lst var-1-lst-lst = (default-val , [])

{- Auxiliary Definition at: ../specification/wasm-3.0/4.4-execution.modules.spectec:81.1-81.58 -}
postulate allocelem : ∀ (v-store : store) (v-elemtype : elemtype) (var-0-lst : (List ref)) → (store × elemaddr)

{- Auxiliary Definition at: ../specification/wasm-3.0/4.4-execution.modules.spectec:86.1-86.117 -}
{-# TERMINATING #-}
allocelems : (v-store : store) (var-0-lst : (List elemtype)) (var-1-lst-lst : (List (List ref))) → (store × (List elemaddr))
allocelems s [] [] = (s , [])
allocelems s (rt ∷ rt'-lst) (ref-lst ∷ ref'-lst-lst) = let (s-1 , ea) = (allocelem s rt ref-lst) in let (s-2 , ea'-lst) = (allocelems s-1 rt'-lst ref'-lst-lst) in (s-2 , ((ea ∷ []) ++ ea'-lst))
allocelems v-store var-0-lst var-1-lst-lst = (default-val , [])

{- Auxiliary Definition at: ../specification/wasm-3.0/4.4-execution.modules.spectec:92.1-92.90 -}
{-# TERMINATING #-}
allocexport : (v-moduleinst : moduleinst) (v-export : export) → exportinst
allocexport v-moduleinst (EXPORT v-name (TAG x)) = record { NAME = v-name ; ADDR = (externaddr-TAG ((moduleinst-TAGS v-moduleinst) [ (proj-uN-0 32 x) ]!)) }
allocexport v-moduleinst (EXPORT v-name (GLOBAL x)) = record { NAME = v-name ; ADDR = (externaddr-GLOBAL ((moduleinst-GLOBALS v-moduleinst) [ (proj-uN-0 32 x) ]!)) }
allocexport v-moduleinst (EXPORT v-name (MEM x)) = record { NAME = v-name ; ADDR = (externaddr-MEM ((moduleinst-MEMS v-moduleinst) [ (proj-uN-0 32 x) ]!)) }
allocexport v-moduleinst (EXPORT v-name (TABLE x)) = record { NAME = v-name ; ADDR = (externaddr-TABLE ((moduleinst-TABLES v-moduleinst) [ (proj-uN-0 32 x) ]!)) }
allocexport v-moduleinst (EXPORT v-name (FUNC x)) = record { NAME = v-name ; ADDR = (externaddr-FUNC ((moduleinst-FUNCS v-moduleinst) [ (proj-uN-0 32 x) ]!)) }
allocexport v-moduleinst v-export = default-val

{- Auxiliary Definition at: ../specification/wasm-3.0/4.4-execution.modules.spectec:99.1-99.104 -}
{-# TERMINATING #-}
allocexports : (v-moduleinst : moduleinst) (var-0-lst : (List export)) → (List exportinst)
allocexports v-moduleinst export-lst = (map (λ (v-export : export) → (allocexport v-moduleinst v-export)) export-lst)

{- Auxiliary Definition at: ../specification/wasm-3.0/4.4-execution.modules.spectec:103.1-103.88 -}
postulate allocmodule : ∀ (v-store : store) (v-module : module') (var-0-lst : (List externaddr)) (var-1-lst : (List val)) (var-2-lst : (List ref)) (var-3-lst-lst : (List (List ref))) → (store × moduleinst)

{- Auxiliary Definition at: ../specification/wasm-3.0/4.4-execution.modules.spectec:148.1-148.38 -}
{-# TERMINATING #-}
rundata- : (v-dataidx : dataidx) (v-data : data') → (List instr)
rundata- x (DATA b-lst datamode-PASSIVE) = let v-n = length (b-lst) in []
rundata- x (DATA b-lst (datamode-ACTIVE y instr-lst)) = let v-n = length (b-lst) in (instr-lst ++ (as (List instr) ((instr-CONST numtype-I32 (mk-uN 0)) ∷ (instr-CONST numtype-I32 (mk-uN v-n)) ∷ (MEMORY-INIT y x) ∷ (DATA-DROP x) ∷ [])))
rundata- v-dataidx v-data = []

{- Auxiliary Definition at: ../specification/wasm-3.0/4.4-execution.modules.spectec:153.1-153.38 -}
{-# TERMINATING #-}
runelem- : (v-elemidx : elemidx) (v-elem : elem) → (List instr)
runelem- x (ELEM rt e-lst PASSIVE) = let v-n = length (e-lst) in []
runelem- x (ELEM rt e-lst DECLARE) = let v-n = length (e-lst) in (as (List instr) ((ELEM-DROP x) ∷ []))
runelem- x (ELEM rt e-lst (ACTIVE y instr-lst)) = let v-n = length (e-lst) in (instr-lst ++ (as (List instr) ((instr-CONST numtype-I32 (mk-uN 0)) ∷ (instr-CONST numtype-I32 (mk-uN v-n)) ∷ (TABLE-INIT y x) ∷ (ELEM-DROP x) ∷ [])))
runelem- v-elemidx v-elem = []

{- Auxiliary Definition at: ../specification/wasm-3.0/4.4-execution.modules.spectec:160.1-160.92 -}
postulate evalexprs : ∀ (v-state : state) (var-0-lst : (List expr)) → (state × (List ref))

{- Auxiliary Definition at: ../specification/wasm-3.0/4.4-execution.modules.spectec:167.1-167.96 -}
{-# TERMINATING #-}
evalexprss : (v-state : state) (var-0-lst-lst : (List (List expr))) → (state × (List (List ref)))
evalexprss z [] = (z , [])
evalexprss z (expr-lst ∷ expr'-lst-lst) = let (z' , ref-lst) = (evalexprs z expr-lst) in let (z'' , ref'-lst-lst) = (evalexprss z' expr'-lst-lst) in (z'' , ((ref-lst ∷ []) ++ ref'-lst-lst))
evalexprss v-state var-0-lst-lst = (default-val , [])

{- Auxiliary Definition at: ../specification/wasm-3.0/4.4-execution.modules.spectec:174.1-174.111 -}
postulate evalglobals : ∀ (v-state : state) (var-0-lst : (List globaltype)) (var-1-lst : (List expr)) → (state × (List val))

{- Auxiliary Definition at: ../specification/wasm-3.0/4.4-execution.modules.spectec:183.1-183.54 -}
postulate instantiate : ∀ (v-store : store) (v-module : module') (var-0-lst : (List externaddr)) → config

{- Auxiliary Definition at: ../specification/wasm-3.0/4.4-execution.modules.spectec:214.1-214.44 -}
postulate invoke : ∀ (v-store : store) (v-funcaddr : funcaddr) (var-0-lst : (List val)) → config

{- Type Alias Definition at: ../specification/wasm-3.0/5.3-binary.instructions.spectec:18.1-18.31 -}
castop : Set
castop = ((Maybe null) × (Maybe null))

{- Type Alias Definition at: ../specification/wasm-3.0/5.3-binary.instructions.spectec:98.1-98.35 -}
memidxop : Set
memidxop = (memidx × memarg)

{- Type Alias Definition at: ../specification/wasm-3.0/5.4-binary.modules.spectec:89.1-89.43 -}
startopt : Set
startopt = (List start)

{- Type Alias Definition at: ../specification/wasm-3.0/5.4-binary.modules.spectec:124.1-124.46 -}
code : Set
code = ((List local) × expr)

{- Type Alias Definition at: ../specification/wasm-3.0/5.4-binary.modules.spectec:156.1-156.33 -}
nopt : Set
nopt = (List u32)

{- Axiom Definition at: ../specification/wasm-3.0/6.1-text.values.spectec:55.1-55.30 -}
postulate ieee- : ∀ (v-N : N) (rat : ℕ) → (fNmag-fam0 (v-N))

{- Record Creation Definition at: ../specification/wasm-3.0/6.1-text.values.spectec:137.1-150.4 -}
record idctxt : Set where
  constructor mk-idctxt
  field
    idctxt-TYPES : (List (Maybe name))
    idctxt-TAGS : (List (Maybe name))
    idctxt-GLOBALS : (List (Maybe name))
    idctxt-MEMS : (List (Maybe name))
    idctxt-TABLES : (List (Maybe name))
    idctxt-FUNCS : (List (Maybe name))
    idctxt-DATAS : (List (Maybe name))
    idctxt-ELEMS : (List (Maybe name))
    idctxt-LOCALS : (List (Maybe name))
    idctxt-LABELS : (List (Maybe name))
    idctxt-FIELDS : (List (List (Maybe name)))
    TYPEDEFS : (List (Maybe deftype))
open idctxt

instance
  append-idctxt : HasAppend (idctxt)
  append-idctxt = record { append = λ arg1 arg2 → record {
    idctxt-TYPES = idctxt-TYPES arg1 ⧺ idctxt-TYPES arg2 ;
    idctxt-TAGS = idctxt-TAGS arg1 ⧺ idctxt-TAGS arg2 ;
    idctxt-GLOBALS = idctxt-GLOBALS arg1 ⧺ idctxt-GLOBALS arg2 ;
    idctxt-MEMS = idctxt-MEMS arg1 ⧺ idctxt-MEMS arg2 ;
    idctxt-TABLES = idctxt-TABLES arg1 ⧺ idctxt-TABLES arg2 ;
    idctxt-FUNCS = idctxt-FUNCS arg1 ⧺ idctxt-FUNCS arg2 ;
    idctxt-DATAS = idctxt-DATAS arg1 ⧺ idctxt-DATAS arg2 ;
    idctxt-ELEMS = idctxt-ELEMS arg1 ⧺ idctxt-ELEMS arg2 ;
    idctxt-LOCALS = idctxt-LOCALS arg1 ⧺ idctxt-LOCALS arg2 ;
    idctxt-LABELS = idctxt-LABELS arg1 ⧺ idctxt-LABELS arg2 ;
    idctxt-FIELDS = idctxt-FIELDS arg1 ⧺ idctxt-FIELDS arg2 ;
    TYPEDEFS = TYPEDEFS arg1 ⧺ TYPEDEFS arg2 } }

instance
  inh-idctxt : Inhabited idctxt
  inh-idctxt = record { default-val = record { idctxt-TYPES = default-val ; idctxt-TAGS = default-val ; idctxt-GLOBALS = default-val ; idctxt-MEMS = default-val ; idctxt-TABLES = default-val ; idctxt-FUNCS = default-val ; idctxt-DATAS = default-val ; idctxt-ELEMS = default-val ; idctxt-LOCALS = default-val ; idctxt-LABELS = default-val ; idctxt-FIELDS = default-val ; TYPEDEFS = default-val } }

{- Type Alias Definition at: ../specification/wasm-3.0/6.1-text.values.spectec:152.1-152.18 -}
I : Set
I = idctxt

{- Auxiliary Definition at: ../specification/wasm-3.0/6.1-text.values.spectec:154.1-154.56 -}
{-# TERMINATING #-}
concat-idctxt : (var-0-lst : (List idctxt)) → idctxt
concat-idctxt [] = record { idctxt-TYPES = [] ; idctxt-TAGS = [] ; idctxt-GLOBALS = [] ; idctxt-MEMS = [] ; idctxt-TABLES = [] ; idctxt-FUNCS = [] ; idctxt-DATAS = [] ; idctxt-ELEMS = [] ; idctxt-LOCALS = [] ; idctxt-LABELS = [] ; idctxt-FIELDS = [] ; TYPEDEFS = [] }
concat-idctxt (v-I ∷ I'-lst) = (v-I ⧺ (concat-idctxt I'-lst))
concat-idctxt var-0-lst = default-val

{- Inductive Relations Definition at: ../specification/wasm-3.0/6.1-text.values.spectec:159.1-159.35 -}
data Idctxt-ok : idctxt → Set where
  mk-Idctxt-ok : ∀ (v-I : I) (field-lst-lst : (List (List char))) → 
    (is-true (disjoint- name (concatopt- name (idctxt-TYPES v-I)))) →
    (is-true (disjoint- name (concatopt- name (idctxt-TAGS v-I)))) →
    (is-true (disjoint- name (concatopt- name (idctxt-GLOBALS v-I)))) →
    (is-true (disjoint- name (concatopt- name (idctxt-MEMS v-I)))) →
    (is-true (disjoint- name (concatopt- name (idctxt-TABLES v-I)))) →
    (is-true (disjoint- name (concatopt- name (idctxt-FUNCS v-I)))) →
    (is-true (disjoint- name (concatopt- name (idctxt-DATAS v-I)))) →
    (is-true (disjoint- name (concatopt- name (idctxt-ELEMS v-I)))) →
    (is-true (disjoint- name (concatopt- name (idctxt-LOCALS v-I)))) →
    (is-true (disjoint- name (concatopt- name (idctxt-LABELS v-I)))) →
    Forall (λ (field-lst : (List char)) → (is-true (disjoint- name (concatopt- name ((just (mk-name field-lst)) ∷ []))))) field-lst-lst →
    (((map (λ (field-lst : (List char)) → (just (mk-name field-lst))) field-lst-lst) ∷ []) ≡ (idctxt-FIELDS v-I)) →
    Idctxt-ok v-I

{- Axiom Definition at: ../specification/wasm-3.0/6.4-text.modules.spectec:170.1-170.31 -}
postulate dots : ⊤

{- Inductive Type Definition at: ../specification/wasm-3.0/6.4-text.modules.spectec:255.1-256.83 -}
data decl : Set where
  decl-TYPE : (v-rectype : rectype) → decl
  decl-IMPORT : (v-name : name) → (v-name : name) → (v-externtype : externtype) → decl
  decl-TAG : (v-tagtype : tagtype) → decl
  decl-GLOBAL : (v-globaltype : globaltype) → (v-expr : expr) → decl
  decl-MEMORY : (v-memtype : memtype) → decl
  decl-TABLE : (v-tabletype : tabletype) → (v-expr : expr) → decl
  decl-FUNC : (v-typeidx : typeidx) → (local-lst : (List local)) → (v-expr : expr) → decl
  decl-DATA : (byte-lst : (List byte)) → (v-datamode : datamode) → decl
  decl-ELEM : (v-reftype : reftype) → (expr-lst : (List expr)) → (v-elemmode : elemmode) → decl
  decl-START : (v-funcidx : funcidx) → decl
  decl-EXPORT : (v-name : name) → (v-externidx : externidx) → decl

instance
  inh-decl : Inhabited decl
  inh-decl = record { default-val = (decl-TYPE (default-val)) }

{- Auxiliary Definition at:  -}
{-# TERMINATING #-}
decl-data : (var-0 : data') → decl
decl-data (DATA x0 x1) = (decl-DATA x0 x1)
decl-data var-0 = default-val

{- Auxiliary Definition at:  -}
{-# TERMINATING #-}
decl-elem : (var-0 : elem) → decl
decl-elem (ELEM x0 x1 x2) = (decl-ELEM x0 x1 x2)
decl-elem var-0 = default-val

{- Auxiliary Definition at:  -}
{-# TERMINATING #-}
decl-export : (var-0 : export) → decl
decl-export (EXPORT x0 x1) = (decl-EXPORT x0 x1)
decl-export var-0 = default-val

{- Auxiliary Definition at:  -}
{-# TERMINATING #-}
decl-func : (var-0 : func) → decl
decl-func (func-FUNC x0 x1 x2) = (decl-FUNC x0 x1 x2)
decl-func var-0 = default-val

{- Auxiliary Definition at:  -}
{-# TERMINATING #-}
decl-global : (var-0 : global) → decl
decl-global (global-GLOBAL x0 x1) = (decl-GLOBAL x0 x1)
decl-global var-0 = default-val

{- Auxiliary Definition at:  -}
{-# TERMINATING #-}
decl-import : (var-0 : import') → decl
decl-import (IMPORT x0 x1 x2) = (decl-IMPORT x0 x1 x2)
decl-import var-0 = default-val

{- Auxiliary Definition at:  -}
{-# TERMINATING #-}
decl-mem : (var-0 : mem) → decl
decl-mem (MEMORY x0) = (decl-MEMORY x0)
decl-mem var-0 = default-val

{- Auxiliary Definition at:  -}
{-# TERMINATING #-}
decl-start : (var-0 : start) → decl
decl-start (START x0) = (decl-START x0)
decl-start var-0 = default-val

{- Auxiliary Definition at:  -}
{-# TERMINATING #-}
decl-table : (var-0 : table) → decl
decl-table (table-TABLE x0 x1) = (decl-TABLE x0 x1)
decl-table var-0 = default-val

{- Auxiliary Definition at:  -}
{-# TERMINATING #-}
decl-tag : (var-0 : tag) → decl
decl-tag (tag-TAG x0) = (decl-TAG x0)
decl-tag var-0 = default-val

{- Auxiliary Definition at:  -}
{-# TERMINATING #-}
decl-type : (var-0 : type) → decl
decl-type (TYPE x0) = (decl-TYPE x0)
decl-type var-0 = default-val

{- Auxiliary Definition at: ../specification/wasm-3.0/6.4-text.modules.spectec:258.1-258.76 -}
{-# TERMINATING #-}
typesd : (var-0-lst : (List decl)) → (List type)
typesd [] = []
typesd ((decl-TYPE v-rectype) ∷ decl'-lst) = ((as (List type) ((TYPE v-rectype) ∷ [])) ++ (typesd decl'-lst))
typesd (v-decl ∷ decl'-lst) = (typesd decl'-lst)
typesd var-0-lst = []

{- Auxiliary Definition at: ../specification/wasm-3.0/6.4-text.modules.spectec:259.1-259.78 -}
{-# TERMINATING #-}
importsd : (var-0-lst : (List decl)) → (List import')
importsd [] = []
importsd ((decl-IMPORT v-name name-0 v-externtype) ∷ decl'-lst) = ((as (List import') ((IMPORT v-name name-0 v-externtype) ∷ [])) ++ (importsd decl'-lst))
importsd (v-decl ∷ decl'-lst) = (importsd decl'-lst)
importsd var-0-lst = []

{- Auxiliary Definition at: ../specification/wasm-3.0/6.4-text.modules.spectec:260.1-260.75 -}
{-# TERMINATING #-}
tagsd : (var-0-lst : (List decl)) → (List tag)
tagsd [] = []
tagsd ((decl-TAG v-tagtype) ∷ decl'-lst) = ((as (List tag) ((tag-TAG v-tagtype) ∷ [])) ++ (tagsd decl'-lst))
tagsd (v-decl ∷ decl'-lst) = (tagsd decl'-lst)
tagsd var-0-lst = []

{- Auxiliary Definition at: ../specification/wasm-3.0/6.4-text.modules.spectec:261.1-261.78 -}
{-# TERMINATING #-}
globalsd : (var-0-lst : (List decl)) → (List global)
globalsd [] = []
globalsd ((decl-GLOBAL v-globaltype v-expr) ∷ decl'-lst) = ((as (List global) ((global-GLOBAL v-globaltype v-expr) ∷ [])) ++ (globalsd decl'-lst))
globalsd (v-decl ∷ decl'-lst) = (globalsd decl'-lst)
globalsd var-0-lst = []

{- Auxiliary Definition at: ../specification/wasm-3.0/6.4-text.modules.spectec:262.1-262.75 -}
{-# TERMINATING #-}
memsd : (var-0-lst : (List decl)) → (List mem)
memsd [] = []
memsd ((decl-MEMORY v-memtype) ∷ decl'-lst) = ((as (List mem) ((MEMORY v-memtype) ∷ [])) ++ (memsd decl'-lst))
memsd (v-decl ∷ decl'-lst) = (memsd decl'-lst)
memsd var-0-lst = []

{- Auxiliary Definition at: ../specification/wasm-3.0/6.4-text.modules.spectec:263.1-263.77 -}
{-# TERMINATING #-}
tablesd : (var-0-lst : (List decl)) → (List table)
tablesd [] = []
tablesd ((decl-TABLE v-tabletype v-expr) ∷ decl'-lst) = ((as (List table) ((table-TABLE v-tabletype v-expr) ∷ [])) ++ (tablesd decl'-lst))
tablesd (v-decl ∷ decl'-lst) = (tablesd decl'-lst)
tablesd var-0-lst = []

{- Auxiliary Definition at: ../specification/wasm-3.0/6.4-text.modules.spectec:264.1-264.76 -}
{-# TERMINATING #-}
funcsd : (var-0-lst : (List decl)) → (List func)
funcsd [] = []
funcsd ((decl-FUNC v-typeidx local-lst v-expr) ∷ decl'-lst) = ((as (List func) ((func-FUNC v-typeidx local-lst v-expr) ∷ [])) ++ (funcsd decl'-lst))
funcsd (v-decl ∷ decl'-lst) = (funcsd decl'-lst)
funcsd var-0-lst = []

{- Auxiliary Definition at: ../specification/wasm-3.0/6.4-text.modules.spectec:265.1-265.76 -}
{-# TERMINATING #-}
datasd : (var-0-lst : (List decl)) → (List data')
datasd [] = []
datasd ((decl-DATA byte-lst v-datamode) ∷ decl'-lst) = ((as (List data') ((DATA byte-lst v-datamode) ∷ [])) ++ (datasd decl'-lst))
datasd (v-decl ∷ decl'-lst) = (datasd decl'-lst)
datasd var-0-lst = []

{- Auxiliary Definition at: ../specification/wasm-3.0/6.4-text.modules.spectec:266.1-266.76 -}
{-# TERMINATING #-}
elemsd : (var-0-lst : (List decl)) → (List elem)
elemsd [] = []
elemsd ((decl-ELEM v-reftype expr-lst v-elemmode) ∷ decl'-lst) = ((as (List elem) ((ELEM v-reftype expr-lst v-elemmode) ∷ [])) ++ (elemsd decl'-lst))
elemsd (v-decl ∷ decl'-lst) = (elemsd decl'-lst)
elemsd var-0-lst = []

{- Auxiliary Definition at: ../specification/wasm-3.0/6.4-text.modules.spectec:267.1-267.77 -}
{-# TERMINATING #-}
startsd : (var-0-lst : (List decl)) → (List start)
startsd [] = []
startsd ((decl-START v-funcidx) ∷ decl'-lst) = ((as (List start) ((START v-funcidx) ∷ [])) ++ (startsd decl'-lst))
startsd (v-decl ∷ decl'-lst) = (startsd decl'-lst)
startsd var-0-lst = []

{- Auxiliary Definition at: ../specification/wasm-3.0/6.4-text.modules.spectec:268.1-268.78 -}
{-# TERMINATING #-}
exportsd : (var-0-lst : (List decl)) → (List export)
exportsd [] = []
exportsd ((decl-EXPORT v-name v-externidx) ∷ decl'-lst) = ((as (List export) ((EXPORT v-name v-externidx) ∷ [])) ++ (exportsd decl'-lst))
exportsd (v-decl ∷ decl'-lst) = (exportsd decl'-lst)
exportsd var-0-lst = []

{- Auxiliary Definition at: ../specification/wasm-3.0/6.4-text.modules.spectec:314.1-314.27 -}
postulate ordered : ∀ (var-0-lst : (List decl)) → Bool

{- Inductive Relations Definition at: ../specification/wasm-3.0/7.0-soundness.contexts.spectec:3.1-3.61 -}
data Context-ok : context → Set where
  mk-Context-ok : ∀ (C : context) (v-n : n) (dt-lst : (List deftype)) (jt-lst : (List tagtype)) (gt-lst : (List globaltype)) (mt-lst : (List memtype)) (tt-lst : (List tabletype)) (dt-F-lst : (List deftype)) (ok-lst : (List datatype)) (et-lst : (List elemtype)) (lct-lst : (List localtype)) (rt-lst : (List reftype)) (rt'-opt : (Maybe reftype)) (x-lst : (List idx)) (v-m : m) (st-lst : (List subtype)) (C-0 : context) (t-1-lst : (List valtype)) (t-2-lst : (List valtype)) → 
    ((length (st-lst)) ≡ (v-m)) →
    ((length (dt-lst)) ≡ (v-n)) →
    (C ≡ record { context-TYPES = dt-lst ; context-TAGS = jt-lst ; context-GLOBALS = gt-lst ; context-MEMS = mt-lst ; context-TABLES = tt-lst ; context-FUNCS = dt-F-lst ; context-DATAS = ok-lst ; context-ELEMS = et-lst ; context-LOCALS = lct-lst ; context-LABELS = (as (List resulttype) ((mk-list (map (λ (rt : reftype) → (valtype-reftype rt)) rt-lst)) ∷ [])) ; context-RETURN = (just (mk-list (fromMaybe (mapMaybe (λ (rt' : reftype) → (valtype-reftype rt')) rt'-opt)))) ; REFS = x-lst ; RECS = st-lst }) →
    (C-0 ≡ record { context-TYPES = dt-lst ; context-TAGS = [] ; context-GLOBALS = [] ; context-MEMS = [] ; context-TABLES = [] ; context-FUNCS = [] ; context-DATAS = [] ; context-ELEMS = [] ; context-LOCALS = [] ; context-LABELS = [] ; context-RETURN = nothing ; REFS = [] ; RECS = [] }) →
    Foralli (λ i (dt : deftype) → (Deftype-ok record { context-TYPES = (slice dt-lst 0 i) ; context-TAGS = [] ; context-GLOBALS = [] ; context-MEMS = [] ; context-TABLES = [] ; context-FUNCS = [] ; context-DATAS = [] ; context-ELEMS = [] ; context-LOCALS = [] ; context-LABELS = [] ; context-RETURN = nothing ; REFS = [] ; RECS = [] } dt)) dt-lst →
    Foralli (λ i (st : subtype) → (Subtype-ok2 record { context-TYPES = dt-lst ; context-TAGS = [] ; context-GLOBALS = [] ; context-MEMS = [] ; context-TABLES = [] ; context-FUNCS = [] ; context-DATAS = [] ; context-ELEMS = [] ; context-LOCALS = [] ; context-LABELS = [] ; context-RETURN = nothing ; REFS = [] ; RECS = st-lst } st (oktypenat-OK i))) st-lst →
    Forall (λ (jt : tagtype) → (Tagtype-ok C-0 jt)) jt-lst →
    Forall (λ (gt : globaltype) → (Globaltype-ok C-0 gt)) gt-lst →
    Forall (λ (mt : memtype) → (Memtype-ok C-0 mt)) mt-lst →
    Forall (λ (tt' : tabletype) → (Tabletype-ok C-0 tt')) tt-lst →
    Forall (λ (dt-F : deftype) → (Deftype-ok C-0 dt-F)) dt-F-lst →
    ((length dt-F-lst) ≡ (length t-1-lst)) →
    ((length dt-F-lst) ≡ (length t-2-lst)) →
    Forall₃ (λ (dt-F : deftype) (t-1 : valtype) (t-2 : valtype) → (Expand dt-F (comptype-FUNC (mk-list (t-1 ∷ [])) (mk-list (t-2 ∷ []))))) dt-F-lst t-1-lst t-2-lst →
    Forall (λ (et : reftype) → (Reftype-ok C-0 et)) et-lst →
    Forall (λ (lct : localtype) → (Localtype-ok C-0 lct)) lct-lst →
    Forall (λ (rt : reftype) → (Resulttype-ok C-0 (mk-list ((valtype-reftype rt) ∷ [])))) rt-lst →
    Forall (λ (rt' : reftype) → (Resulttype-ok C-0 (mk-list ((valtype-reftype rt') ∷ [])))) (fromMaybe rt'-opt) →
    Forall (λ (x : idx) → ((proj-uN-0 32 x) < (length dt-F-lst))) x-lst →
    Context-ok C

{- Inductive Relations Definition at: ../specification/wasm-3.0/7.1-soundness.configurations.spectec:323.1-323.48 -}
data Localval-ok : store → (Maybe val) → localtype → Set where
  Localval-ok--set : ∀ (s : store) (v-val : val) (t : valtype) → 
    (Val-ok s v-val t) →
    Localval-ok s (just v-val) (mk-localtype SET t)
  Localval-ok--unset : ∀ (s : store) → Localval-ok s nothing (mk-localtype UNSET valtype-BOT)

{- Inductive Relations Definition at: ../specification/wasm-3.0/7.1-soundness.configurations.spectec:76.1-76.51 -}
data Datainst-ok : store → datainst → datatype → Set where
  mk-Datainst-ok : ∀ (s : store) (b-lst : (List byte)) → Datainst-ok s record { datainst-BYTES = b-lst } OK

{- Inductive Relations Definition at: ../specification/wasm-3.0/7.1-soundness.configurations.spectec:77.1-77.51 -}
data Eleminst-ok : store → eleminst → elemtype → Set where
  mk-Eleminst-ok : ∀ (s : store) (rt : reftype) (ref-lst : (List ref)) → 
    (Reftype-ok record { context-TYPES = [] ; context-TAGS = [] ; context-GLOBALS = [] ; context-MEMS = [] ; context-TABLES = [] ; context-FUNCS = [] ; context-DATAS = [] ; context-ELEMS = [] ; context-LOCALS = [] ; context-LABELS = [] ; context-RETURN = nothing ; REFS = [] ; RECS = [] } rt) →
    Forall (λ (v-ref : ref) → (Ref-ok s v-ref rt)) ref-lst →
    Eleminst-ok s record { eleminst-TYPE = rt ; eleminst-REFS = ref-lst } rt

{- Inductive Relations Definition at: ../specification/wasm-3.0/7.1-soundness.configurations.spectec:78.1-78.49 -}
data Exportinst-ok : store → exportinst → Set where
  mk-Exportinst-ok : ∀ (s : store) (nm : name) (xa : externaddr) (xt : externtype) → 
    (Externaddr-ok s xa xt) →
    Exportinst-ok s record { NAME = nm ; ADDR = xa }

{- Inductive Relations Definition at: ../specification/wasm-3.0/7.1-soundness.configurations.spectec:143.1-143.54 -}
data Moduleinst-ok : store → moduleinst → context → Set where
  mk-Moduleinst-ok : ∀ (s : store) (deftype-lst : (List deftype)) (tagaddr-lst : (List tagaddr)) (globaladdr-lst : (List globaladdr)) (memaddr-lst : (List memaddr)) (tableaddr-lst : (List tableaddr)) (funcaddr-lst : (List funcaddr)) (dataaddr-lst : (List dataaddr)) (elemaddr-lst : (List elemaddr)) (exportinst-lst : (List exportinst)) (tagtype-lst : (List tagtype)) (globaltype-lst : (List globaltype)) (memtype-lst : (List memtype)) (tabletype-lst : (List tabletype)) (deftype-F-lst : (List deftype)) (datatype-lst : (List datatype)) (elemtype-lst : (List elemtype)) (subtype-lst : (List subtype)) → 
    Forall (λ (v-deftype : deftype) → (Deftype-ok record { context-TYPES = [] ; context-TAGS = [] ; context-GLOBALS = [] ; context-MEMS = [] ; context-TABLES = [] ; context-FUNCS = [] ; context-DATAS = [] ; context-ELEMS = [] ; context-LOCALS = [] ; context-LABELS = [] ; context-RETURN = nothing ; REFS = [] ; RECS = [] } v-deftype)) deftype-lst →
    ((length tagaddr-lst) ≡ (length tagtype-lst)) →
    Forall₂ (λ (v-tagaddr : tagaddr) (v-tagtype : tagtype) → (Externaddr-ok s (externaddr-TAG v-tagaddr) (externtype-TAG v-tagtype))) tagaddr-lst tagtype-lst →
    ((length globaladdr-lst) ≡ (length globaltype-lst)) →
    Forall₂ (λ (v-globaladdr : globaladdr) (v-globaltype : globaltype) → (Externaddr-ok s (externaddr-GLOBAL v-globaladdr) (externtype-GLOBAL v-globaltype))) globaladdr-lst globaltype-lst →
    ((length deftype-F-lst) ≡ (length funcaddr-lst)) →
    Forall₂ (λ (deftype-F : deftype) (v-funcaddr : funcaddr) → (Externaddr-ok s (externaddr-FUNC v-funcaddr) (externtype-FUNC (typeuse-deftype deftype-F)))) deftype-F-lst funcaddr-lst →
    ((length memaddr-lst) ≡ (length memtype-lst)) →
    Forall₂ (λ (v-memaddr : memaddr) (v-memtype : memtype) → (Externaddr-ok s (externaddr-MEM v-memaddr) (externtype-MEM v-memtype))) memaddr-lst memtype-lst →
    ((length tableaddr-lst) ≡ (length tabletype-lst)) →
    Forall₂ (λ (v-tableaddr : tableaddr) (v-tabletype : tabletype) → (Externaddr-ok s (externaddr-TABLE v-tableaddr) (externtype-TABLE v-tabletype))) tableaddr-lst tabletype-lst →
    ((length dataaddr-lst) ≡ (length datatype-lst)) →
    Forall (λ (v-dataaddr : ℕ) → (v-dataaddr < (length (store-DATAS s)))) dataaddr-lst →
    Forall₂ (λ (v-dataaddr : ℕ) (v-datatype : datatype) → (Datainst-ok s ((store-DATAS s) [ v-dataaddr ]!) v-datatype)) dataaddr-lst datatype-lst →
    ((length elemaddr-lst) ≡ (length elemtype-lst)) →
    Forall (λ (v-elemaddr : ℕ) → (v-elemaddr < (length (store-ELEMS s)))) elemaddr-lst →
    Forall₂ (λ (v-elemaddr : ℕ) (v-elemtype : elemtype) → (Eleminst-ok s ((store-ELEMS s) [ v-elemaddr ]!) v-elemtype)) elemaddr-lst elemtype-lst →
    Forall (λ (v-exportinst : exportinst) → (Exportinst-ok s v-exportinst)) exportinst-lst →
    (is-true (disjoint- name (map (λ (v-exportinst : exportinst) → (NAME v-exportinst)) exportinst-lst))) →
    ((length ((map (λ (v-tagaddr : tagaddr) → (externaddr-TAG v-tagaddr)) tagaddr-lst) ++ ((map (λ (v-globaladdr : globaladdr) → (externaddr-GLOBAL v-globaladdr)) globaladdr-lst) ++ ((map (λ (v-memaddr : memaddr) → (externaddr-MEM v-memaddr)) memaddr-lst) ++ ((map (λ (v-tableaddr : tableaddr) → (externaddr-TABLE v-tableaddr)) tableaddr-lst) ++ (map (λ (v-funcaddr : funcaddr) → (externaddr-FUNC v-funcaddr)) funcaddr-lst)))))) > 0) →
    Forall (λ (v-exportinst : exportinst) → ((ADDR v-exportinst) ∈ ((map (λ (v-tagaddr : tagaddr) → (externaddr-TAG v-tagaddr)) tagaddr-lst) ++ ((map (λ (v-globaladdr : globaladdr) → (externaddr-GLOBAL v-globaladdr)) globaladdr-lst) ++ ((map (λ (v-memaddr : memaddr) → (externaddr-MEM v-memaddr)) memaddr-lst) ++ ((map (λ (v-tableaddr : tableaddr) → (externaddr-TABLE v-tableaddr)) tableaddr-lst) ++ (map (λ (v-funcaddr : funcaddr) → (externaddr-FUNC v-funcaddr)) funcaddr-lst))))))) exportinst-lst →
    Moduleinst-ok s record { moduleinst-TYPES = deftype-lst ; moduleinst-TAGS = tagaddr-lst ; moduleinst-GLOBALS = globaladdr-lst ; moduleinst-MEMS = memaddr-lst ; moduleinst-TABLES = tableaddr-lst ; moduleinst-FUNCS = funcaddr-lst ; moduleinst-DATAS = dataaddr-lst ; moduleinst-ELEMS = elemaddr-lst ; EXPORTS = exportinst-lst } record { context-TYPES = deftype-lst ; context-TAGS = tagtype-lst ; context-GLOBALS = globaltype-lst ; context-MEMS = memtype-lst ; context-TABLES = tabletype-lst ; context-FUNCS = deftype-F-lst ; context-DATAS = datatype-lst ; context-ELEMS = elemtype-lst ; context-LOCALS = [] ; context-LABELS = [] ; context-RETURN = nothing ; REFS = (mkseq (λ i → (mk-uN i)) (length funcaddr-lst)) ; RECS = subtype-lst }

{- Inductive Relations Definition at: ../specification/wasm-3.0/7.1-soundness.configurations.spectec:324.1-324.44 -}
data Frame-ok : store → frame → context → Set where
  mk-Frame-ok : ∀ (s : store) (val-opt-lst : (List (Maybe val))) (v-moduleinst : moduleinst) (C : context) (lct-lst : (List localtype)) → 
    (Moduleinst-ok s v-moduleinst C) →
    ((length lct-lst) ≡ (length val-opt-lst)) →
    Forall₂ (λ (lct : localtype) (val-opt : (Maybe val)) → (Localval-ok s val-opt lct)) lct-lst val-opt-lst →
    Frame-ok s record { frame-LOCALS = val-opt-lst ; MODULE = v-moduleinst } (C ⧺ record { context-TYPES = [] ; context-TAGS = [] ; context-GLOBALS = [] ; context-MEMS = [] ; context-TABLES = [] ; context-FUNCS = [] ; context-DATAS = [] ; context-ELEMS = [] ; context-LOCALS = lct-lst ; context-LABELS = [] ; context-RETURN = nothing ; REFS = [] ; RECS = [] })

mutual
  {- Inductive Relations Definition at: ../specification/wasm-3.0/7.1-soundness.configurations.spectec:3.1-4.36 -}
  data Instr-ok2 : store → context → instr → instrtype → Set where
    plain : ∀ (s : store) (C : context) (v-instr : instr) (t-1-lst : (List valtype)) (x-lst : (List idx)) (t-2-lst : (List valtype)) → 
      (Instr-ok C v-instr (mk-instrtype (mk-list t-1-lst) x-lst (mk-list t-2-lst))) →
      Instr-ok2 s C v-instr (mk-instrtype (mk-list t-1-lst) x-lst (mk-list t-2-lst))
    Instr-ok2--ref : ∀ (s : store) (C : context) (v-ref : ref) (rt : reftype) → 
      (Ref-ok s v-ref rt) →
      Instr-ok2 s C (instr-ref v-ref) (mk-instrtype (mk-list []) [] (mk-list ((valtype-reftype rt) ∷ [])))
    label : ∀ (s : store) (C : context) (v-n : n) (instr'-lst : (List instr)) (instr-lst : (List instr)) (t-lst : (List valtype)) (t'-lst : (List valtype)) (x'-lst : (List idx)) (x-lst : (List idx)) → 
      ((length (t'-lst)) ≡ (v-n)) →
      (Instrs-ok2 s C instr'-lst (mk-instrtype (mk-list t'-lst) x'-lst (mk-list t-lst))) →
      (Instrs-ok2 s (record { context-TYPES = [] ; context-TAGS = [] ; context-GLOBALS = [] ; context-MEMS = [] ; context-TABLES = [] ; context-FUNCS = [] ; context-DATAS = [] ; context-ELEMS = [] ; context-LOCALS = [] ; context-LABELS = (as (List resulttype) ((mk-list t'-lst) ∷ [])) ; context-RETURN = nothing ; REFS = [] ; RECS = [] } ⧺ C) instr-lst (mk-instrtype (mk-list []) x-lst (mk-list t-lst))) →
      Instr-ok2 s C (LABEL- v-n instr'-lst instr-lst) (mk-instrtype (mk-list []) [] (mk-list t-lst))
    Instr-ok2--frame : ∀ (s : store) (C : context) (v-n : n) (f : frame) (instr-lst : (List instr)) (t-lst : (List valtype)) (C' : context) → 
      ((length (t-lst)) ≡ (v-n)) →
      (Frame-ok s f C') →
      (Expr-ok2 s C' instr-lst (mk-list t-lst)) →
      Instr-ok2 s C (FRAME- v-n f instr-lst) (mk-instrtype (mk-list []) [] (mk-list t-lst))
    handler : ∀ (s : store) (C : context) (v-n : n) (catch-lst : (List catch)) (instr-lst : (List instr)) (t-1-lst : (List valtype)) (t-2-lst : (List valtype)) (x-lst : (List idx)) → 
      Forall (λ (v-catch : catch) → (Catch-ok C v-catch)) catch-lst →
      (Instrs-ok2 s C instr-lst (mk-instrtype (mk-list t-1-lst) x-lst (mk-list t-2-lst))) →
      Instr-ok2 s C (HANDLER- v-n catch-lst instr-lst) (mk-instrtype (mk-list t-1-lst) [] (mk-list t-2-lst))
    trap : ∀ (s : store) (C : context) (t-1-lst : (List valtype)) (t-2-lst : (List valtype)) → 
      (Instrtype-ok C (mk-instrtype (mk-list t-1-lst) [] (mk-list t-2-lst))) →
      Instr-ok2 s C TRAP (mk-instrtype (mk-list t-1-lst) [] (mk-list t-2-lst))

  {- Inductive Relations Definition at: ../specification/wasm-3.0/7.1-soundness.configurations.spectec:5.1-6.36 -}
  data Instrs-ok2 : store → context → (List instr) → instrtype → Set where
    Instrs-ok2--empty : ∀ (s : store) (C : context) → Instrs-ok2 s C [] (mk-instrtype (mk-list []) [] (mk-list []))
    Instrs-ok2--instr : ∀ (s : store) (C : context) (v-instr : instr) (t-1-lst : (List valtype)) (t-2-lst : (List valtype)) → 
      (Instr-ok2 s C v-instr (mk-instrtype (mk-list t-1-lst) [] (mk-list t-2-lst))) →
      Instrs-ok2 s C (v-instr ∷ []) (mk-instrtype (mk-list t-1-lst) [] (mk-list t-2-lst))
    Instrs-ok2--seq : ∀ (s : store) (C : context) (instr-1-lst : (List instr)) (instr-2-lst : (List instr)) (t-1-lst : (List valtype)) (x-1-lst : (List idx)) (x-2-lst : (List idx)) (t-3-lst : (List valtype)) (t-2-lst : (List valtype)) (init-lst : (List init)) (t-lst : (List valtype)) → 
      (Instrs-ok2 s C instr-1-lst (mk-instrtype (mk-list t-1-lst) x-1-lst (mk-list t-2-lst))) →
      ((length init-lst) ≡ (length t-lst)) →
      ((length init-lst) ≡ (length x-1-lst)) →
      Forall (λ (x-1 : idx) → ((proj-uN-0 32 x-1) < (length (context-LOCALS C)))) x-1-lst →
      Forall₃ (λ (v-init : init) (t : valtype) (x-1 : idx) → (((context-LOCALS C) [ (proj-uN-0 32 x-1) ]!) ≡ (mk-localtype v-init t))) init-lst t-lst x-1-lst →
      ((with-locals C x-1-lst (map (λ (t : valtype) → (mk-localtype SET t)) t-lst)) ≢ nothing) →
      (Instrs-ok2 s (unwrap! (with-locals C x-1-lst (map (λ (t : valtype) → (mk-localtype SET t)) t-lst))) instr-2-lst (mk-instrtype (mk-list t-2-lst) x-2-lst (mk-list t-3-lst))) →
      Instrs-ok2 s C (instr-1-lst ++ instr-2-lst) (mk-instrtype (mk-list t-1-lst) (x-1-lst ++ x-2-lst) (mk-list t-3-lst))
    Instrs-ok2--sub : ∀ (s : store) (C : context) (instr-lst : (List instr)) (it' : instrtype) (it : instrtype) → 
      (Instrs-ok2 s C instr-lst it) →
      (Instrtype-sub C it it') →
      (Instrtype-ok C it') →
      Instrs-ok2 s C instr-lst it'
    Instrs-ok2--frame : ∀ (s : store) (C : context) (instr-lst : (List instr)) (t-lst : (List valtype)) (t-1-lst : (List valtype)) (x-lst : (List idx)) (t-2-lst : (List valtype)) → 
      (Instrs-ok2 s C instr-lst (mk-instrtype (mk-list t-1-lst) x-lst (mk-list t-2-lst))) →
      (Resulttype-ok C (mk-list t-lst)) →
      Instrs-ok2 s C instr-lst (mk-instrtype (mk-list (t-lst ++ t-1-lst)) x-lst (mk-list (t-lst ++ t-2-lst)))

  {- Inductive Relations Definition at: ../specification/wasm-3.0/7.1-soundness.configurations.spectec:7.1-8.36 -}
  data Expr-ok2 : store → context → expr → resulttype → Set where
    mk-Expr-ok2 : ∀ (s : store) (C : context) (instr-lst : (List instr)) (t-lst : (List valtype)) → 
      (Instrs-ok2 s C instr-lst (mk-instrtype (mk-list []) [] (mk-list t-lst))) →
      Expr-ok2 s C instr-lst (mk-list t-lst)

{- Inductive Relations Definition at: ../specification/wasm-3.0/7.1-soundness.configurations.spectec:71.1-71.48 -}
data Taginst-ok : store → taginst → tagtype → Set where
  mk-Taginst-ok : ∀ (s : store) (jt : tagtype) → 
    (Tagtype-ok record { context-TYPES = [] ; context-TAGS = [] ; context-GLOBALS = [] ; context-MEMS = [] ; context-TABLES = [] ; context-FUNCS = [] ; context-DATAS = [] ; context-ELEMS = [] ; context-LOCALS = [] ; context-LABELS = [] ; context-RETURN = nothing ; REFS = [] ; RECS = [] } jt) →
    Taginst-ok s record { taginst-TYPE = jt } jt

{- Inductive Relations Definition at: ../specification/wasm-3.0/7.1-soundness.configurations.spectec:72.1-72.57 -}
data Globalinst-ok : store → globalinst → globaltype → Set where
  mk-Globalinst-ok : ∀ (s : store) (mut-opt : (Maybe mut)) (t : valtype) (v-val : val) → 
    (Globaltype-ok record { context-TYPES = [] ; context-TAGS = [] ; context-GLOBALS = [] ; context-MEMS = [] ; context-TABLES = [] ; context-FUNCS = [] ; context-DATAS = [] ; context-ELEMS = [] ; context-LOCALS = [] ; context-LABELS = [] ; context-RETURN = nothing ; REFS = [] ; RECS = [] } (mk-globaltype mut-opt t)) →
    (Val-ok s v-val t) →
    Globalinst-ok s record { globalinst-TYPE = (mk-globaltype mut-opt t) ; VALUE = v-val } (mk-globaltype mut-opt t)

{- Inductive Relations Definition at: ../specification/wasm-3.0/7.1-soundness.configurations.spectec:73.1-73.48 -}
data Meminst-ok : store → meminst → memtype → Set where
  mk-Meminst-ok : ∀ (s : store) (at : addrtype) (v-n : n) (m-opt : (Maybe m)) (b-lst : (List byte)) → 
    (Memtype-ok record { context-TYPES = [] ; context-TAGS = [] ; context-GLOBALS = [] ; context-MEMS = [] ; context-TABLES = [] ; context-FUNCS = [] ; context-DATAS = [] ; context-ELEMS = [] ; context-LOCALS = [] ; context-LABELS = [] ; context-RETURN = nothing ; REFS = [] ; RECS = [] } (PAGE at (mk-limits (mk-uN v-n) (mapMaybe (λ (v-m : ℕ) → (mk-uN v-m)) m-opt)))) →
    ((length b-lst) ≡ (v-n * (64 * (Ki )))) →
    Meminst-ok s record { meminst-TYPE = (PAGE at (mk-limits (mk-uN v-n) (mapMaybe (λ (v-m : ℕ) → (mk-uN v-m)) m-opt))) ; BYTES = b-lst } (PAGE at (mk-limits (mk-uN v-n) (mapMaybe (λ (v-m : ℕ) → (mk-uN v-m)) m-opt)))

{- Inductive Relations Definition at: ../specification/wasm-3.0/7.1-soundness.configurations.spectec:74.1-74.54 -}
data Tableinst-ok : store → tableinst → tabletype → Set where
  mk-Tableinst-ok : ∀ (s : store) (at : addrtype) (v-n : n) (m-opt : (Maybe m)) (rt : reftype) (ref-lst : (List ref)) → 
    (Tabletype-ok record { context-TYPES = [] ; context-TAGS = [] ; context-GLOBALS = [] ; context-MEMS = [] ; context-TABLES = [] ; context-FUNCS = [] ; context-DATAS = [] ; context-ELEMS = [] ; context-LOCALS = [] ; context-LABELS = [] ; context-RETURN = nothing ; REFS = [] ; RECS = [] } (mk-tabletype at (mk-limits (mk-uN v-n) (mapMaybe (λ (v-m : ℕ) → (mk-uN v-m)) m-opt)) rt)) →
    ((length ref-lst) ≡ v-n) →
    Forall (λ (v-ref : ref) → (Ref-ok s v-ref rt)) ref-lst →
    Tableinst-ok s record { tableinst-TYPE = (mk-tabletype at (mk-limits (mk-uN v-n) (mapMaybe (λ (v-m : ℕ) → (mk-uN v-m)) m-opt)) rt) ; tableinst-REFS = ref-lst } (mk-tabletype at (mk-limits (mk-uN v-n) (mapMaybe (λ (v-m : ℕ) → (mk-uN v-m)) m-opt)) rt)

{- Inductive Relations Definition at: ../specification/wasm-3.0/7.1-soundness.configurations.spectec:75.1-75.50 -}
data Funcinst-ok : store → funcinst → deftype → Set where
  mk-Funcinst-ok : ∀ (s : store) (dt : deftype) (v-moduleinst : moduleinst) (v-func : func) (C : context) (dt' : deftype) → 
    (Deftype-ok record { context-TYPES = [] ; context-TAGS = [] ; context-GLOBALS = [] ; context-MEMS = [] ; context-TABLES = [] ; context-FUNCS = [] ; context-DATAS = [] ; context-ELEMS = [] ; context-LOCALS = [] ; context-LABELS = [] ; context-RETURN = nothing ; REFS = [] ; RECS = [] } dt) →
    (Moduleinst-ok s v-moduleinst C) →
    (Func-ok C v-func dt') →
    (Deftype-sub C dt' dt) →
    Funcinst-ok s record { funcinst-TYPE = dt ; funcinst-MODULE = v-moduleinst ; CODE = (funccode-func v-func) } dt

{- Inductive Relations Definition at: ../specification/wasm-3.0/7.1-soundness.configurations.spectec:79.1-79.49 -}
data Structinst-ok : store → structinst → Set where
  mk-Structinst-ok : ∀ (s : store) (dt : deftype) (fv-lst : (List fieldval)) (mut-opt-lst : (List (Maybe mut))) (zt-lst : (List storagetype)) → 
    (Expand dt (comptype-STRUCT (mk-list (zipWith (λ (mut-opt : (Maybe mut)) (zt : storagetype) → (mk-fieldtype mut-opt zt)) mut-opt-lst zt-lst)))) →
    ((length fv-lst) ≡ (length zt-lst)) →
    Forall₂ (λ (fv : fieldval) (zt : storagetype) → (Fieldval-ok s fv zt)) fv-lst zt-lst →
    Structinst-ok s record { structinst-TYPE = dt ; FIELDS = fv-lst }

{- Inductive Relations Definition at: ../specification/wasm-3.0/7.1-soundness.configurations.spectec:80.1-80.47 -}
data Arrayinst-ok : store → arrayinst → Set where
  mk-Arrayinst-ok : ∀ (s : store) (dt : deftype) (fv-lst : (List fieldval)) (mut-opt : (Maybe mut)) (zt : storagetype) → 
    (Expand dt (comptype-ARRAY (mk-fieldtype mut-opt zt))) →
    Forall (λ (fv : fieldval) → (Fieldval-ok s fv zt)) fv-lst →
    Arrayinst-ok s record { arrayinst-TYPE = dt ; arrayinst-FIELDS = fv-lst }

{- Inductive Relations Definition at: ../specification/wasm-3.0/7.1-soundness.configurations.spectec:81.1-81.43 -}
data Exninst-ok : store → exninst → Set where
  mk-Exninst-ok : ∀ (s : store) (ta : tagaddr) (val-lst : (List val)) (dt : deftype) (t-lst : (List valtype)) → 
    (ta < (length (store-TAGS s))) →
    ((typeuse-deftype dt) ≡ (taginst-TYPE ((store-TAGS s) [ ta ]!))) →
    (Expand dt (comptype-FUNC (mk-list t-lst) (mk-list []))) →
    ((length t-lst) ≡ (length val-lst)) →
    Forall₂ (λ (t : valtype) (v-val : val) → (Val-ok s v-val t)) t-lst val-lst →
    Exninst-ok s record { exninst-TAG = ta ; exninst-FIELDS = val-lst }

{- Inductive Relations Definition at: ../specification/wasm-3.0/7.1-soundness.configurations.spectec:212.1-213.50 -}
data ImmutReachable : fieldval → store → fieldval → Set where
  ImmutReachable--trans : ∀ (fv-1 : fieldval) (s : store) (fv-2 : fieldval) (fv' : fieldval) → 
    (ImmutReachable fv-1 s fv') →
    (ImmutReachable fv' s fv-2) →
    ImmutReachable fv-1 s fv-2
  ref-struct : ∀ (a : addr) (s : store) (i : ℕ) (ft-lst : (List fieldtype)) (zt : storagetype) → 
    (i < (length (FIELDS ((STRUCTS s) [ a ]!)))) →
    (a < (length (STRUCTS s))) →
    (Expand (structinst-TYPE ((STRUCTS s) [ a ]!)) (comptype-STRUCT (mk-list ft-lst))) →
    (i < (length ft-lst)) →
    ((ft-lst [ i ]!) ≡ (mk-fieldtype nothing zt)) →
    ImmutReachable (fieldval-REF-STRUCT-ADDR a) s ((FIELDS ((STRUCTS s) [ a ]!)) [ i ]!)
  ref-array : ∀ (a : addr) (s : store) (i : ℕ) (zt : storagetype) → 
    (i < (length (arrayinst-FIELDS ((ARRAYS s) [ a ]!)))) →
    (a < (length (ARRAYS s))) →
    (Expand (arrayinst-TYPE ((ARRAYS s) [ a ]!)) (comptype-ARRAY (mk-fieldtype nothing zt))) →
    ImmutReachable (fieldval-REF-ARRAY-ADDR a) s ((arrayinst-FIELDS ((ARRAYS s) [ a ]!)) [ i ]!)
  ref-exn : ∀ (a : addr) (s : store) (i : ℕ) → 
    (i < (length (exninst-FIELDS ((EXNS s) [ a ]!)))) →
    (a < (length (EXNS s))) →
    ImmutReachable (fieldval-REF-EXN-ADDR a) s (fieldval-val ((exninst-FIELDS ((EXNS s) [ a ]!)) [ i ]!))
  ref-extern : ∀ (v-ref : ref) (s : store) → ImmutReachable (fieldval-REF-EXTERN v-ref) s (fieldval-ref v-ref)

{- Auxiliary Definition at: ../specification/wasm-3.0/7.1-soundness.configurations.spectec:219.1-219.57 -}
postulate fun-NotImmutReachable : ∀ (v-fieldval : fieldval) (v-store : store) (fieldval-0 : fieldval) → Bool

{- Inductive Relations Definition at: ../specification/wasm-3.0/7.1-soundness.configurations.spectec:214.1-215.54 -}
data NotImmutReachable : fieldval → store → fieldval → Set where
  mk-NotImmutReachable : ∀ (fv-1 : fieldval) (s : store) (fv-2 : fieldval) → 
    (is-true (fun-NotImmutReachable fv-1 s fv-2)) →
    NotImmutReachable fv-1 s fv-2

{- Inductive Relations Definition at: ../specification/wasm-3.0/7.1-soundness.configurations.spectec:186.1-186.33 -}
data Store-ok : store → Set where
  mk-Store-ok : ∀ (s : store) (taginst-lst : (List taginst)) (tagtype-lst : (List tagtype)) (globalinst-lst : (List globalinst)) (globaltype-lst : (List globaltype)) (meminst-lst : (List meminst)) (memtype-lst : (List memtype)) (tableinst-lst : (List tableinst)) (tabletype-lst : (List tabletype)) (deftype-lst : (List deftype)) (funcinst-lst : (List funcinst)) (datainst-lst : (List datainst)) (datatype-lst : (List datatype)) (eleminst-lst : (List eleminst)) (elemtype-lst : (List elemtype)) (structinst-lst : (List structinst)) (arrayinst-lst : (List arrayinst)) (exninst-lst : (List exninst)) → 
    ((length taginst-lst) ≡ (length tagtype-lst)) →
    Forall₂ (λ (v-taginst : taginst) (v-tagtype : tagtype) → (Taginst-ok s v-taginst v-tagtype)) taginst-lst tagtype-lst →
    ((length globalinst-lst) ≡ (length globaltype-lst)) →
    Forall₂ (λ (v-globalinst : globalinst) (v-globaltype : globaltype) → (Globalinst-ok s v-globalinst v-globaltype)) globalinst-lst globaltype-lst →
    ((length meminst-lst) ≡ (length memtype-lst)) →
    Forall₂ (λ (v-meminst : meminst) (v-memtype : memtype) → (Meminst-ok s v-meminst v-memtype)) meminst-lst memtype-lst →
    ((length tableinst-lst) ≡ (length tabletype-lst)) →
    Forall₂ (λ (v-tableinst : tableinst) (v-tabletype : tabletype) → (Tableinst-ok s v-tableinst v-tabletype)) tableinst-lst tabletype-lst →
    ((length deftype-lst) ≡ (length funcinst-lst)) →
    Forall₂ (λ (v-deftype : deftype) (v-funcinst : funcinst) → (Funcinst-ok s v-funcinst v-deftype)) deftype-lst funcinst-lst →
    ((length datainst-lst) ≡ (length datatype-lst)) →
    Forall₂ (λ (v-datainst : datainst) (v-datatype : datatype) → (Datainst-ok s v-datainst v-datatype)) datainst-lst datatype-lst →
    ((length eleminst-lst) ≡ (length elemtype-lst)) →
    Forall₂ (λ (v-eleminst : eleminst) (v-elemtype : elemtype) → (Eleminst-ok s v-eleminst v-elemtype)) eleminst-lst elemtype-lst →
    Forall (λ (v-structinst : structinst) → (Structinst-ok s v-structinst)) structinst-lst →
    Forall (λ (v-arrayinst : arrayinst) → (Arrayinst-ok s v-arrayinst)) arrayinst-lst →
    Forall (λ (v-exninst : exninst) → (Exninst-ok s v-exninst)) exninst-lst →
    holds-upto (λ a → (NotImmutReachable (fieldval-REF-STRUCT-ADDR a) s (fieldval-REF-STRUCT-ADDR a))) (length structinst-lst) →
    holds-upto (λ a → (NotImmutReachable (fieldval-REF-ARRAY-ADDR a) s (fieldval-REF-ARRAY-ADDR a))) (length arrayinst-lst) →
    holds-upto (λ a → (NotImmutReachable (fieldval-REF-EXN-ADDR a) s (fieldval-REF-EXN-ADDR a))) (length exninst-lst) →
    (s ≡ record { store-TAGS = taginst-lst ; store-GLOBALS = globalinst-lst ; store-MEMS = meminst-lst ; store-TABLES = tableinst-lst ; store-FUNCS = funcinst-lst ; store-DATAS = datainst-lst ; store-ELEMS = eleminst-lst ; STRUCTS = structinst-lst ; ARRAYS = arrayinst-lst ; EXNS = exninst-lst }) →
    Store-ok s

{- Inductive Relations Definition at: ../specification/wasm-3.0/7.1-soundness.configurations.spectec:249.1-249.45 -}
data Extend-taginst : taginst → taginst → Set where
  mk-Extend-taginst : ∀ (jt : tagtype) → Extend-taginst record { taginst-TYPE = jt } record { taginst-TYPE = jt }

{- Inductive Relations Definition at: ../specification/wasm-3.0/7.1-soundness.configurations.spectec:250.1-250.54 -}
data Extend-globalinst : globalinst → globalinst → Set where
  mk-Extend-globalinst : ∀ (mut-opt : (Maybe mut)) (t : valtype) (v-val : val) (val' : val) → 
    ((mut-opt ≡ (just MUT)) ⊎ (v-val ≡ val')) →
    Extend-globalinst record { globalinst-TYPE = (mk-globaltype mut-opt t) ; VALUE = v-val } record { globalinst-TYPE = (mk-globaltype mut-opt t) ; VALUE = val' }

{- Inductive Relations Definition at: ../specification/wasm-3.0/7.1-soundness.configurations.spectec:251.1-251.45 -}
data Extend-meminst : meminst → meminst → Set where
  mk-Extend-meminst : ∀ (at : addrtype) (v-n : n) (m-opt : (Maybe m)) (b-lst : (List byte)) (n' : n) (b'-lst : (List byte)) → 
    (v-n ≤ n') →
    ((length b-lst) ≤ (length b'-lst)) →
    Extend-meminst record { meminst-TYPE = (PAGE at (mk-limits (mk-uN v-n) (mapMaybe (λ (v-m : ℕ) → (mk-uN v-m)) m-opt))) ; BYTES = b-lst } record { meminst-TYPE = (PAGE at (mk-limits (mk-uN n') (mapMaybe (λ (v-m : ℕ) → (mk-uN v-m)) m-opt))) ; BYTES = b'-lst }

{- Inductive Relations Definition at: ../specification/wasm-3.0/7.1-soundness.configurations.spectec:252.1-252.51 -}
data Extend-tableinst : tableinst → tableinst → Set where
  mk-Extend-tableinst : ∀ (at : addrtype) (v-n : n) (m-opt : (Maybe m)) (rt : reftype) (ref-lst : (List ref)) (n' : n) (ref'-lst : (List ref)) → 
    (v-n ≤ n') →
    ((length ref-lst) ≤ (length ref'-lst)) →
    Extend-tableinst record { tableinst-TYPE = (mk-tabletype at (mk-limits (mk-uN v-n) (mapMaybe (λ (v-m : ℕ) → (mk-uN v-m)) m-opt)) rt) ; tableinst-REFS = ref-lst } record { tableinst-TYPE = (mk-tabletype at (mk-limits (mk-uN n') (mapMaybe (λ (v-m : ℕ) → (mk-uN v-m)) m-opt)) rt) ; tableinst-REFS = ref'-lst }

{- Inductive Relations Definition at: ../specification/wasm-3.0/7.1-soundness.configurations.spectec:253.1-253.48 -}
data Extend-funcinst : funcinst → funcinst → Set where
  mk-Extend-funcinst : ∀ (dt : deftype) (mm : moduleinst) (fc : funccode) → Extend-funcinst record { funcinst-TYPE = dt ; funcinst-MODULE = mm ; CODE = fc } record { funcinst-TYPE = dt ; funcinst-MODULE = mm ; CODE = fc }

{- Inductive Relations Definition at: ../specification/wasm-3.0/7.1-soundness.configurations.spectec:254.1-254.48 -}
data Extend-datainst : datainst → datainst → Set where
  mk-Extend-datainst : ∀ (b-lst : (List byte)) (b'-lst : (List byte)) → 
    ((b-lst ≡ b'-lst) ⊎ (b'-lst ≡ [])) →
    Extend-datainst record { datainst-BYTES = b-lst } record { datainst-BYTES = b'-lst }

{- Inductive Relations Definition at: ../specification/wasm-3.0/7.1-soundness.configurations.spectec:255.1-255.48 -}
data Extend-eleminst : eleminst → eleminst → Set where
  mk-Extend-eleminst : ∀ (rt : reftype) (ref-lst : (List ref)) (ref'-lst : (List ref)) → 
    ((ref-lst ≡ ref'-lst) ⊎ (ref'-lst ≡ [])) →
    Extend-eleminst record { eleminst-TYPE = rt ; eleminst-REFS = ref-lst } record { eleminst-TYPE = rt ; eleminst-REFS = ref'-lst }

{- Inductive Relations Definition at: ../specification/wasm-3.0/7.1-soundness.configurations.spectec:256.1-256.54 -}
data Extend-structinst : structinst → structinst → Set where
  mk-Extend-structinst : ∀ (dt : deftype) (fv-lst : (List fieldval)) (fv'-lst : (List fieldval)) (mut-opt-lst : (List (Maybe mut))) (zt-lst : (List storagetype)) → 
    (Expand dt (comptype-STRUCT (mk-list (zipWith (λ (mut-opt : (Maybe mut)) (zt : storagetype) → (mk-fieldtype mut-opt zt)) mut-opt-lst zt-lst)))) →
    ((length fv-lst) ≡ (length fv'-lst)) →
    ((length fv-lst) ≡ (length mut-opt-lst)) →
    Forall₃ (λ (fv : fieldval) (fv' : fieldval) (mut-opt : (Maybe mut)) → ((mut-opt ≡ (just MUT)) ⊎ (fv ≡ fv'))) fv-lst fv'-lst mut-opt-lst →
    Extend-structinst record { structinst-TYPE = dt ; FIELDS = fv-lst } record { structinst-TYPE = dt ; FIELDS = fv'-lst }

{- Inductive Relations Definition at: ../specification/wasm-3.0/7.1-soundness.configurations.spectec:257.1-257.51 -}
data Extend-arrayinst : arrayinst → arrayinst → Set where
  mk-Extend-arrayinst : ∀ (dt : deftype) (fv-lst : (List fieldval)) (fv'-lst : (List fieldval)) (mut-opt : (Maybe mut)) (zt : storagetype) → 
    (Expand dt (comptype-ARRAY (mk-fieldtype mut-opt zt))) →
    ((length fv-lst) ≡ (length fv'-lst)) →
    Forall₂ (λ (fv : fieldval) (fv' : fieldval) → ((mut-opt ≡ (just MUT)) ⊎ (fv ≡ fv'))) fv-lst fv'-lst →
    Extend-arrayinst record { arrayinst-TYPE = dt ; arrayinst-FIELDS = fv-lst } record { arrayinst-TYPE = dt ; arrayinst-FIELDS = fv'-lst }

{- Inductive Relations Definition at: ../specification/wasm-3.0/7.1-soundness.configurations.spectec:258.1-258.45 -}
data Extend-exninst : exninst → exninst → Set where
  mk-Extend-exninst : ∀ (ta : tagaddr) (val-lst : (List val)) → Extend-exninst record { exninst-TAG = ta ; exninst-FIELDS = val-lst } record { exninst-TAG = ta ; exninst-FIELDS = val-lst }

{- Inductive Relations Definition at: ../specification/wasm-3.0/7.1-soundness.configurations.spectec:259.1-259.39 -}
data Extend-store : store → store → Set where
  mk-Extend-store : ∀ (s : store) (s' : store) → 
    holds-upto (λ a → (a < (length (store-TAGS s)))) (length (store-TAGS s)) →
    holds-upto (λ a → (a < (length (store-TAGS s')))) (length (store-TAGS s)) →
    holds-upto (λ a → (Extend-taginst ((store-TAGS s) [ a ]!) ((store-TAGS s') [ a ]!))) (length (store-TAGS s)) →
    holds-upto (λ a → (a < (length (store-GLOBALS s)))) (length (store-GLOBALS s)) →
    holds-upto (λ a → (a < (length (store-GLOBALS s')))) (length (store-GLOBALS s)) →
    holds-upto (λ a → (Extend-globalinst ((store-GLOBALS s) [ a ]!) ((store-GLOBALS s') [ a ]!))) (length (store-GLOBALS s)) →
    holds-upto (λ a → (a < (length (store-MEMS s)))) (length (store-MEMS s)) →
    holds-upto (λ a → (a < (length (store-MEMS s')))) (length (store-MEMS s)) →
    holds-upto (λ a → (Extend-meminst ((store-MEMS s) [ a ]!) ((store-MEMS s') [ a ]!))) (length (store-MEMS s)) →
    holds-upto (λ a → (a < (length (store-TABLES s)))) (length (store-TABLES s)) →
    holds-upto (λ a → (a < (length (store-TABLES s')))) (length (store-TABLES s)) →
    holds-upto (λ a → (Extend-tableinst ((store-TABLES s) [ a ]!) ((store-TABLES s') [ a ]!))) (length (store-TABLES s)) →
    holds-upto (λ a → (a < (length (store-FUNCS s)))) (length (store-FUNCS s)) →
    holds-upto (λ a → (a < (length (store-FUNCS s')))) (length (store-FUNCS s)) →
    holds-upto (λ a → (Extend-funcinst ((store-FUNCS s) [ a ]!) ((store-FUNCS s') [ a ]!))) (length (store-FUNCS s)) →
    holds-upto (λ a → (a < (length (store-DATAS s)))) (length (store-DATAS s)) →
    holds-upto (λ a → (a < (length (store-DATAS s')))) (length (store-DATAS s)) →
    holds-upto (λ a → (Extend-datainst ((store-DATAS s) [ a ]!) ((store-DATAS s') [ a ]!))) (length (store-DATAS s)) →
    holds-upto (λ a → (a < (length (store-ELEMS s)))) (length (store-ELEMS s)) →
    holds-upto (λ a → (a < (length (store-ELEMS s')))) (length (store-ELEMS s)) →
    holds-upto (λ a → (Extend-eleminst ((store-ELEMS s) [ a ]!) ((store-ELEMS s') [ a ]!))) (length (store-ELEMS s)) →
    holds-upto (λ a → (a < (length (STRUCTS s)))) (length (STRUCTS s)) →
    holds-upto (λ a → (a < (length (STRUCTS s')))) (length (STRUCTS s)) →
    holds-upto (λ a → (Extend-structinst ((STRUCTS s) [ a ]!) ((STRUCTS s') [ a ]!))) (length (STRUCTS s)) →
    holds-upto (λ a → (a < (length (ARRAYS s)))) (length (ARRAYS s)) →
    holds-upto (λ a → (a < (length (ARRAYS s')))) (length (ARRAYS s)) →
    holds-upto (λ a → (Extend-arrayinst ((ARRAYS s) [ a ]!) ((ARRAYS s') [ a ]!))) (length (ARRAYS s)) →
    holds-upto (λ a → (a < (length (EXNS s)))) (length (EXNS s)) →
    holds-upto (λ a → (a < (length (EXNS s')))) (length (EXNS s)) →
    holds-upto (λ a → (Extend-exninst ((EXNS s) [ a ]!) ((EXNS s') [ a ]!))) (length (EXNS s)) →
    Extend-store s s'

{- Inductive Relations Definition at: ../specification/wasm-3.0/7.1-soundness.configurations.spectec:325.1-325.38 -}
data State-ok : state → context → Set where
  mk-State-ok : ∀ (s : store) (f : frame) (C : context) → 
    (Store-ok s) →
    (Frame-ok s f C) →
    State-ok (mk-state s f) C

{- Inductive Relations Definition at: ../specification/wasm-3.0/7.1-soundness.configurations.spectec:326.1-326.43 -}
data Config-ok : config → resulttype → Set where
  mk-Config-ok : ∀ (s : store) (f : frame) (instr-lst : (List instr)) (t-lst : (List valtype)) (C : context) → 
    (State-ok (mk-state s f) C) →
    (Expr-ok2 s C instr-lst (mk-list t-lst)) →
    Config-ok (mk-config (mk-state s f) instr-lst) (mk-list t-lst)




















