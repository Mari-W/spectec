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

{- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:162.14-162.17 -}
data r-MUT : Set where
  MUT : r-MUT

instance
  inh-r-MUT : Inhabited r-MUT
  inh-r-MUT = record { default-val = MUT }

{- Type Alias Definition at: ../specification/wasm-2.0/0-aux.spectec:7.1-7.15 -}
N : Set
N = ℕ

{- Type Alias Definition at: ../specification/wasm-2.0/0-aux.spectec:8.1-8.15 -}
M : Set
M = ℕ

{- Type Alias Definition at: ../specification/wasm-2.0/0-aux.spectec:9.1-9.15 -}
n : Set
n = ℕ

{- Type Alias Definition at: ../specification/wasm-2.0/0-aux.spectec:10.1-10.15 -}
m : Set
m = ℕ

{- Auxiliary Definition at: ../specification/wasm-2.0/0-aux.spectec:15.1-15.14 -}
Ki : ℕ
Ki = 1024

{- Auxiliary Definition at: ../specification/wasm-2.0/0-aux.spectec:21.1-21.25 -}
{-# TERMINATING #-}
min : (nat : ℕ) (nat-0 : ℕ) → ℕ
min i j = (if (i ≤? j) then i else j)

{- Auxiliary Definition at: ../specification/wasm-2.0/0-aux.spectec:25.1-25.21 -}
{-# TERMINATING #-}
sum : (var-0-lst : (List ℕ)) → ℕ
sum [] = 0
sum (v-n ∷ n'-lst) = (v-n + (sum n'-lst))
sum var-0-lst = default-val

{- Auxiliary Definition at: ../specification/wasm-2.0/0-aux.spectec:32.1-32.58 -}
{-# TERMINATING #-}
opt- : (X : Set) (var-0-lst : (List X)) → (Maybe (Maybe X))
opt- X [] = (just nothing)
opt- X (w ∷ []) = (just (just w))
opt- X x1 = nothing

{- Auxiliary Definition at: ../specification/wasm-2.0/0-aux.spectec:36.1-36.45 -}
{-# TERMINATING #-}
list- : (X : Set) (var-0-opt : (Maybe X)) → (List X)
list- X nothing = []
list- X (just w) = (w ∷ [])
list- X var-0-opt = []

{- Auxiliary Definition at: ../specification/wasm-2.0/0-aux.spectec:40.1-40.86 -}
{-# TERMINATING #-}
concat- : (X : Set) (var-0-lst-lst : (List (List X))) → (List X)
concat- X [] = []
concat- X (w-lst ∷ w'-lst-lst) = (w-lst ++ (concat- X w'-lst-lst))
concat- X var-0-lst-lst = []

{- Axiom Definition at: ../specification/wasm-2.0/0-aux.spectec:44.1-44.39 -}
postulate inv-concat- : ∀ (X : Set) (var-0-lst : (List X)) → (List (List X))

{- Auxiliary Definition at: ../specification/wasm-2.0/0-aux.spectec:51.1-51.46 -}
{-# TERMINATING #-}
setproduct2- : (X : Set) (X-0 : X) (var-0-lst-lst : (List (List X))) → (List (List X))
setproduct2- X w-1 [] = []
setproduct2- X w-1 (w'-lst ∷ w-lst-lst) = ((((w-1 ∷ []) ++ w'-lst) ∷ []) ++ (setproduct2- X w-1 w-lst-lst))
setproduct2- X X-0 var-0-lst-lst = []

{- Auxiliary Definition at: ../specification/wasm-2.0/0-aux.spectec:50.1-50.47 -}
{-# TERMINATING #-}
setproduct1- : (X : Set) (var-0-lst : (List X)) (var-1-lst-lst : (List (List X))) → (List (List X))
setproduct1- X [] w-lst-lst = []
setproduct1- X (w-1 ∷ w'-lst) w-lst-lst = ((setproduct2- X w-1 w-lst-lst) ++ (setproduct1- X w'-lst w-lst-lst))
setproduct1- X var-0-lst var-1-lst-lst = []

{- Auxiliary Definition at: ../specification/wasm-2.0/0-aux.spectec:49.1-49.84 -}
{-# TERMINATING #-}
setproduct- : (X : Set) (var-0-lst-lst : (List (List X))) → (List (List X))
setproduct- X [] = ([] ∷ [])
setproduct- X (w-1-lst ∷ w-lst-lst) = (setproduct1- X w-1-lst (setproduct- X w-lst-lst))
setproduct- X var-0-lst-lst = []

{- Auxiliary Definition at: ../specification/wasm-2.0/0-aux.spectec:60.1-60.78 -}
{-# TERMINATING #-}
disjoint- : (X : Set) {{_ : HasEq X}} (var-0-lst : (List X)) → Bool
disjoint- X [] = true
disjoint- X (w ∷ w'-lst) = ((not (w ∈ᵇ w'-lst)) ∧ (disjoint- X w'-lst))
disjoint- X var-0-lst = default-val

{- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:6.1-6.49 -}
data list-fam0 (X : Set) : Set where
  mk-list : (X-lst : (List X)) → list-fam0 X {- 1 premise(s) dropped -}

instance
  inh-list-fam0 : {X : Set} → Inhabited (list-fam0 X)
  inh-list-fam0 {X} = record { default-val = (mk-list ([])) }

list : (X : Set) → Set
list X = list-fam0 X
list _ = ⊤

inh-list-fun : (X : Set) → Inhabited (list X)
inh-list-fun X = record { default-val = default-val }

{- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:6.1-6.49 -}
{-# TERMINATING #-}
proj-list-0 : (X : Set) (x : (list-fam0 (X))) → ((List X))
proj-list-0 X (mk-list v-X-list-0) = (v-X-list-0)
proj-list-0 X x = ([])

instance
  proj-list-0-coercion : {X : Set} → Coerce (list-fam0 (X)) ((List X))
  proj-list-0-coercion = record { coerce = proj-list-0 _ }

{- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:15.1-15.36 -}
data bit : Set where
  mk-bit : (i : ℕ) → bit {- 1 premise(s) dropped -}

{- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:16.1-16.50 -}
data byte : Set where
  mk-byte : (i : ℕ) → byte {- 1 premise(s) dropped -}

instance
  inh-byte : Inhabited byte
  inh-byte = record { default-val = (mk-byte (default-val)) }

{- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:16.1-16.50 -}
{-# TERMINATING #-}
proj-byte-0 : (x : byte) → (ℕ)
proj-byte-0 (mk-byte v-num-0) = (v-num-0)
proj-byte-0 x = (default-val)

instance
  proj-byte-0-coercion : Coerce byte (ℕ)
  proj-byte-0-coercion = record { coerce = proj-byte-0 }

{- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:18.1-19.25 -}
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

{- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:18.1-19.25 -}
{-# TERMINATING #-}
proj-uN-0 : (v-N : N) (x : (uN-fam0 (v-N))) → (ℕ)
proj-uN-0 v-N (mk-uN v-num-0) = (v-num-0)
proj-uN-0 v-N x = (default-val)

instance
  proj-uN-0-coercion : {v-N : N} → Coerce (uN-fam0 (v-N)) (ℕ)
  proj-uN-0-coercion = record { coerce = proj-uN-0 _ }

{- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:20.1-21.49 -}
data sN-fam0 (v-N : N) : Set where
  mk-sN : (i : ℕ) → sN-fam0 v-N {- 1 premise(s) dropped -}

sN : (v-N : N) → Set
sN v-N = sN-fam0 v-N
sN _ = ⊤

{- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:22.1-23.8 -}
iN : (v-N : N) → Set
iN v-N = (uN-fam0 (v-N))
iN _ = ⊤

inh-iN-fun : (v-N : N) → Inhabited (iN v-N)
inh-iN-fun v-N = record { default-val = (Inhabited.default-val (inh-uN-fun v-N)) }

{- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:25.1-25.18 -}
u8 : Set
u8 = (uN-fam0 (8))

{- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:26.1-26.20 -}
u16 : Set
u16 = (uN-fam0 (16))

{- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:27.1-27.20 -}
u31 : Set
u31 = (uN-fam0 (31))

{- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:28.1-28.20 -}
u32 : Set
u32 = (uN-fam0 (32))

{- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:29.1-29.20 -}
u64 : Set
u64 = (uN-fam0 (64))

{- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:30.1-30.20 -}
s33 : Set
s33 = (sN-fam0 (33))

{- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:31.1-31.20 -}
i32 : Set
i32 = (uN-fam0 (32))

{- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:32.1-32.20 -}
i64 : Set
i64 = (uN-fam0 (64))

{- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:33.1-33.22 -}
i128 : Set
i128 = (uN-fam0 (128))

{- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:40.1-40.35 -}
{-# TERMINATING #-}
signif : (v-N : N) → (Maybe ℕ)
signif (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (zero))))))))))))))))))))))))))))))))) = (just 23)
signif (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (zero))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = (just 52)
signif x0 = nothing

{- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:44.1-44.34 -}
{-# TERMINATING #-}
expon : (v-N : N) → (Maybe ℕ)
expon (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (zero))))))))))))))))))))))))))))))))) = (just 8)
expon (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (zero))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = (just 11)
expon x0 = nothing

{- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:48.1-48.30 -}
{-# TERMINATING #-}
fun-M : (v-N : N) → ℕ
fun-M v-N = (unwrap! (signif v-N))

{- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:51.1-51.30 -}
{-# TERMINATING #-}
E : (v-N : N) → ℕ
E v-N = (unwrap! (expon v-N))

{- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:58.1-58.30 -}
exp : Set
exp = ℕ

{- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:59.1-63.84 -}
data fNmag-fam0 (v-N : N) : Set where
  NORM : (v-m : m) → (v-exp : exp) → fNmag-fam0 v-N {- 1 premise(s) dropped -}
  SUBNORM : (v-m : m) → fNmag-fam0 v-N {- 1 premise(s) dropped -}
  INF : fNmag-fam0 v-N
  NAN : (v-m : m) → fNmag-fam0 v-N {- 1 premise(s) dropped -}

instance
  inh-fNmag-fam0 : {v-N : N} → Inhabited (fNmag-fam0 v-N)
  inh-fNmag-fam0 {v-N} = record { default-val = (NORM (default-val) (default-val)) }

fNmag : (v-N : N) → Set
fNmag v-N = fNmag-fam0 v-N
fNmag _ = ⊤

inh-fNmag-fun : (v-N : N) → Inhabited (fNmag v-N)
inh-fNmag-fun v-N = record { default-val = default-val }

{- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:54.1-56.35 -}
data fN-fam0 (v-N : N) : Set where
  POS : (_ : (fNmag-fam0 (v-N))) → fN-fam0 v-N
  NEG : (_ : (fNmag-fam0 (v-N))) → fN-fam0 v-N

instance
  inh-fN-fam0 : {v-N : N} → Inhabited (fN-fam0 v-N)
  inh-fN-fam0 {v-N} = record { default-val = (POS ((Inhabited.default-val (inh-fNmag-fun v-N)))) }

fN : (v-N : N) → Set
fN v-N = fN-fam0 v-N
fN _ = ⊤

inh-fN-fun : (v-N : N) → Inhabited (fN v-N)
inh-fN-fun v-N = record { default-val = default-val }

{- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:65.1-65.20 -}
f32 : Set
f32 = (fN-fam0 (32))

{- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:66.1-66.20 -}
f64 : Set
f64 = (fN-fam0 (64))

{- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:68.1-68.39 -}
{-# TERMINATING #-}
fzero : (v-N : N) → (fN-fam0 (v-N))
fzero v-N = (POS (SUBNORM 0))

{- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:71.1-71.39 -}
{-# TERMINATING #-}
fone : (v-N : N) → (fN-fam0 (v-N))
fone v-N = (POS (NORM 1 (coerce {B = ℕ} 0)))

{- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:74.1-74.21 -}
{-# TERMINATING #-}
canon- : (v-N : N) → ℕ
canon- v-N = (2 ^ (coerce {B = ℕ} ((coerce {B = ℕ} (unwrap! (signif v-N))) – (coerce {B = ℕ} 1))))

{- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:80.1-81.8 -}
vN : (v-N : N) → Set
vN v-N = (uN-fam0 (v-N))
vN _ = ⊤

inh-vN-fun : (v-N : N) → Inhabited (vN v-N)
inh-vN-fun v-N = record { default-val = (Inhabited.default-val (inh-iN-fun v-N)) }

{- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:88.1-88.85 -}
data char : Set where
  mk-char : (i : ℕ) → char {- 1 premise(s) dropped -}

instance
  inh-char : Inhabited char
  inh-char = record { default-val = (mk-char (default-val)) }

{- Axiom Definition at: ../specification/wasm-2.0/1-syntax.spectec:90.1-90.25 -}
postulate utf8 : ∀ (var-0-lst : (List char)) → (List byte)

{- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:92.1-92.70 -}
data name : Set where
  mk-name : (char-lst : (List char)) → name {- 1 premise(s) dropped -}

instance
  inh-name : Inhabited name
  inh-name = record { default-val = (mk-name ([])) }

{- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:101.1-101.36 -}
idx : Set
idx = u32

{- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:102.1-102.44 -}
laneidx : Set
laneidx = u8

{- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:104.1-104.45 -}
typeidx : Set
typeidx = idx

{- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:105.1-105.49 -}
funcidx : Set
funcidx = idx

{- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:106.1-106.49 -}
globalidx : Set
globalidx = idx

{- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:107.1-107.47 -}
tableidx : Set
tableidx = idx

{- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:108.1-108.46 -}
memidx : Set
memidx = idx

{- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:109.1-109.45 -}
elemidx : Set
elemidx = idx

{- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:110.1-110.45 -}
dataidx : Set
dataidx = idx

{- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:111.1-111.47 -}
labelidx : Set
labelidx = idx

{- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:112.1-112.47 -}
localidx : Set
localidx = idx

{- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:126.1-127.26 -}
data numtype : Set where
  I32 : numtype
  I64 : numtype
  F32 : numtype
  F64 : numtype

instance
  inh-numtype : Inhabited numtype
  inh-numtype = record { default-val = I32 }

{- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:129.1-130.9 -}
data vectype : Set where
  V128 : vectype

{- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:132.1-133.22 -}
data consttype : Set where
  consttype-I32 : consttype
  consttype-I64 : consttype
  consttype-F32 : consttype
  consttype-F64 : consttype
  consttype-V128 : consttype

{- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:135.1-136.24 -}
data reftype : Set where
  FUNCREF : reftype
  EXTERNREF : reftype

instance
  inh-reftype : Inhabited reftype
  inh-reftype = record { default-val = FUNCREF }

{- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:138.1-139.38 -}
data valtype : Set where
  valtype-I32 : valtype
  valtype-I64 : valtype
  valtype-F32 : valtype
  valtype-F64 : valtype
  valtype-V128 : valtype
  valtype-FUNCREF : valtype
  valtype-EXTERNREF : valtype
  BOT : valtype

instance
  inh-valtype : Inhabited valtype
  inh-valtype = record { default-val = valtype-I32 }

{- Auxiliary Definition at:  -}
{-# TERMINATING #-}
valtype-numtype : (var-0 : numtype) → valtype
valtype-numtype I32 = valtype-I32
valtype-numtype I64 = valtype-I64
valtype-numtype F32 = valtype-F32
valtype-numtype F64 = valtype-F64
valtype-numtype var-0 = default-val

{- Auxiliary Definition at:  -}
{-# TERMINATING #-}
valtype-reftype : (var-0 : reftype) → valtype
valtype-reftype FUNCREF = valtype-FUNCREF
valtype-reftype EXTERNREF = valtype-EXTERNREF
valtype-reftype var-0 = default-val

{- Auxiliary Definition at:  -}
{-# TERMINATING #-}
valtype-vectype : (var-0 : vectype) → valtype
valtype-vectype V128 = valtype-V128
valtype-vectype var-0 = default-val

{- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:141.1-141.38 -}
data Inn : Set where
  Inn-I32 : Inn
  Inn-I64 : Inn

{- Auxiliary Definition at:  -}
{-# TERMINATING #-}
numtype-Inn : (var-0 : Inn) → numtype
numtype-Inn Inn-I32 = I32
numtype-Inn Inn-I64 = I64
numtype-Inn var-0 = default-val

{- Auxiliary Definition at:  -}
{-# TERMINATING #-}
valtype-Inn : (var-0 : Inn) → valtype
valtype-Inn Inn-I32 = valtype-I32
valtype-Inn Inn-I64 = valtype-I64
valtype-Inn var-0 = default-val

{- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:142.1-142.38 -}
data Fnn : Set where
  Fnn-F32 : Fnn
  Fnn-F64 : Fnn

{- Auxiliary Definition at:  -}
{-# TERMINATING #-}
numtype-Fnn : (var-0 : Fnn) → numtype
numtype-Fnn Fnn-F32 = F32
numtype-Fnn Fnn-F64 = F64
numtype-Fnn var-0 = default-val

{- Auxiliary Definition at:  -}
{-# TERMINATING #-}
valtype-Fnn : (var-0 : Fnn) → valtype
valtype-Fnn Fnn-F32 = valtype-F32
valtype-Fnn Fnn-F64 = valtype-F64
valtype-Fnn var-0 = default-val

{- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:143.1-143.36 -}
Vnn : Set
Vnn = vectype

{- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:146.1-147.16 -}
resulttype : Set
resulttype = (list-fam0 (valtype))

{- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:152.1-152.52 -}
data packtype : Set where
  I8 : packtype
  I16 : packtype

{- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:153.1-153.60 -}
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

{- Auxiliary Definition at:  -}
{-# TERMINATING #-}
lanetype-Fnn : (var-0 : Fnn) → lanetype
lanetype-Fnn Fnn-F32 = lanetype-F32
lanetype-Fnn Fnn-F64 = lanetype-F64
lanetype-Fnn var-0 = default-val

{- Auxiliary Definition at:  -}
{-# TERMINATING #-}
lanetype-Inn : (var-0 : Inn) → lanetype
lanetype-Inn Inn-I32 = lanetype-I32
lanetype-Inn Inn-I64 = lanetype-I64
lanetype-Inn var-0 = default-val

{- Auxiliary Definition at:  -}
{-# TERMINATING #-}
lanetype-numtype : (var-0 : numtype) → lanetype
lanetype-numtype I32 = lanetype-I32
lanetype-numtype I64 = lanetype-I64
lanetype-numtype F32 = lanetype-F32
lanetype-numtype F64 = lanetype-F64
lanetype-numtype var-0 = default-val

{- Auxiliary Definition at:  -}
{-# TERMINATING #-}
lanetype-packtype : (var-0 : packtype) → lanetype
lanetype-packtype I8 = lanetype-I8
lanetype-packtype I16 = lanetype-I16
lanetype-packtype var-0 = default-val

{- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:155.1-155.37 -}
Pnn : Set
Pnn = packtype

{- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:156.1-156.38 -}
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
Jnn-Inn : (var-0 : Inn) → Jnn
Jnn-Inn Inn-I32 = Jnn-I32
Jnn-Inn Inn-I64 = Jnn-I64
Jnn-Inn var-0 = default-val

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
Jnn-packtype : (var-0 : packtype) → Jnn
Jnn-packtype I8 = Jnn-I8
Jnn-packtype I16 = Jnn-I16
Jnn-packtype var-0 = default-val

{- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:157.1-157.37 -}
Lnn : Set
Lnn = lanetype

{- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:162.1-162.18 -}
mut : Set
mut = (Maybe r-MUT)

{- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:164.1-165.17 -}
data limits : Set where
  mk-limits : (v-u32 : u32) → (u32-opt : (Maybe u32)) → limits

instance
  inh-limits : Inhabited limits
  inh-limits = record { default-val = (mk-limits (default-val) (nothing)) }

{- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:167.1-168.14 -}
data globaltype : Set where
  mk-globaltype : (v-mut : mut) → (v-valtype : valtype) → globaltype

instance
  inh-globaltype : Inhabited globaltype
  inh-globaltype = record { default-val = (mk-globaltype (default-val) (default-val)) }

{- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:169.1-170.27 -}
data functype : Set where
  mk-functype : (v-resulttype : resulttype) → (v-resulttype : resulttype) → functype

instance
  inh-functype : Inhabited functype
  inh-functype = record { default-val = (mk-functype (default-val) (default-val)) }

{- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:171.1-172.17 -}
data tabletype : Set where
  mk-tabletype : (v-limits : limits) → (v-reftype : reftype) → tabletype

instance
  inh-tabletype : Inhabited tabletype
  inh-tabletype = record { default-val = (mk-tabletype (default-val) (default-val)) }

{- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:173.1-174.14 -}
data memtype : Set where
  PAGE : (v-limits : limits) → memtype

instance
  inh-memtype : Inhabited memtype
  inh-memtype = record { default-val = (PAGE (default-val)) }

{- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:175.1-176.10 -}
elemtype : Set
elemtype = reftype

{- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:177.1-178.5 -}
data datatype : Set where
  OK : datatype

instance
  inh-datatype : Inhabited datatype
  inh-datatype = record { default-val = OK }

{- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:179.1-180.70 -}
data externtype : Set where
  FUNC : (v-functype : functype) → externtype
  GLOBAL : (v-globaltype : globaltype) → externtype
  TABLE : (v-tabletype : tabletype) → externtype
  MEM : (v-memtype : memtype) → externtype

{- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:318.1-318.60 -}
data dim : Set where
  mk-dim : (i : ℕ) → dim {- 1 premise(s) dropped -}

instance
  inh-dim : Inhabited dim
  inh-dim = record { default-val = (mk-dim (default-val)) }

{- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:318.1-318.60 -}
{-# TERMINATING #-}
proj-dim-0 : (x : dim) → (ℕ)
proj-dim-0 (mk-dim v-num-0) = (v-num-0)
proj-dim-0 x = (default-val)

instance
  proj-dim-0-coercion : Coerce dim (ℕ)
  proj-dim-0-coercion = record { coerce = proj-dim-0 }

{- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:319.1-319.69 -}
data shape : Set where
  X : (v-lanetype : lanetype) → (v-dim : dim) → shape

instance
  inh-shape : Inhabited shape
  inh-shape = record { default-val = (X (default-val) (default-val)) }

{- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:206.1-206.32 -}
{-# TERMINATING #-}
fun-lanetype : (v-shape : shape) → lanetype
fun-lanetype (X v-Lnn (mk-dim v-N)) = v-Lnn
fun-lanetype v-shape = default-val

{- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:208.1-208.59 -}
{-# TERMINATING #-}
size : (v-valtype : valtype) → (Maybe ℕ)
size valtype-I32 = (just 32)
size valtype-I64 = (just 64)
size valtype-F32 = (just 32)
size valtype-F64 = (just 64)
size valtype-V128 = (just 128)
size x0 = nothing

{- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:209.1-209.45 -}
{-# TERMINATING #-}
psize : (v-packtype : packtype) → ℕ
psize I8 = 8
psize I16 = 16
psize v-packtype = default-val

{- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:210.1-210.45 -}
{-# TERMINATING #-}
lsize : (v-lanetype : lanetype) → ℕ
lsize lanetype-I32 = (unwrap! (size (valtype-numtype I32)))
lsize lanetype-I64 = (unwrap! (size (valtype-numtype I64)))
lsize lanetype-F32 = (unwrap! (size (valtype-numtype F32)))
lsize lanetype-F64 = (unwrap! (size (valtype-numtype F64)))
lsize lanetype-I8 = (psize I8)
lsize lanetype-I16 = (psize I16)
lsize v-lanetype = default-val

{- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:211.1-211.70 -}
{-# TERMINATING #-}
isize : (v-Inn : Inn) → ℕ
isize v-Inn = (unwrap! (size (valtype-Inn v-Inn)))

{- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:212.1-212.70 -}
{-# TERMINATING #-}
jsize : (v-Jnn : Jnn) → ℕ
jsize v-Jnn = (lsize (lanetype-Jnn v-Jnn))

{- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:213.1-213.70 -}
{-# TERMINATING #-}
fsize : (v-Fnn : Fnn) → ℕ
fsize v-Fnn = (unwrap! (size (valtype-Fnn v-Fnn)))

{- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:231.1-231.63 -}
{-# TERMINATING #-}
sizenn : (v-numtype : numtype) → ℕ
sizenn nt = (unwrap! (size (valtype-numtype nt)))

{- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:232.1-232.63 -}
{-# TERMINATING #-}
sizenn1 : (v-numtype : numtype) → ℕ
sizenn1 nt = (unwrap! (size (valtype-numtype nt)))

{- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:233.1-233.63 -}
{-# TERMINATING #-}
sizenn2 : (v-numtype : numtype) → ℕ
sizenn2 nt = (unwrap! (size (valtype-numtype nt)))

{- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:238.1-238.63 -}
{-# TERMINATING #-}
lsizenn : (v-lanetype : lanetype) → ℕ
lsizenn lt = (lsize lt)

{- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:239.1-239.63 -}
{-# TERMINATING #-}
lsizenn1 : (v-lanetype : lanetype) → ℕ
lsizenn1 lt = (lsize lt)

{- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:240.1-240.63 -}
{-# TERMINATING #-}
lsizenn2 : (v-lanetype : lanetype) → ℕ
lsizenn2 lt = (lsize lt)

{- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:245.1-245.40 -}
{-# TERMINATING #-}
inv-isize : (nat : ℕ) → (Maybe Inn)
inv-isize (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (zero))))))))))))))))))))))))))))))))) = (just Inn-I32)
inv-isize (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (zero))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = (just Inn-I64)
inv-isize x0 = nothing

{- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:246.1-246.40 -}
{-# TERMINATING #-}
inv-jsize : (nat : ℕ) → (Maybe Jnn)
inv-jsize (suc (suc (suc (suc (suc (suc (suc (suc (zero))))))))) = (just Jnn-I8)
inv-jsize (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (zero))))))))))))))))) = (just Jnn-I16)
inv-jsize (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (zero))))))))))))))))))))))))))))))))) = (just Jnn-I32)
inv-jsize (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (zero))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = (just Jnn-I64)
inv-jsize x0 = nothing

{- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:247.1-247.40 -}
{-# TERMINATING #-}
inv-fsize : (nat : ℕ) → (Maybe Fnn)
inv-fsize (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (zero))))))))))))))))))))))))))))))))) = (just Fnn-F32)
inv-fsize (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (zero))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = (just Fnn-F64)
inv-fsize x0 = nothing

{- Type Family Definition at: ../specification/wasm-2.0/1-syntax.spectec:259.1-259.21 -}
num- : (v-numtype : numtype) → Set
num- I32 = (uN-fam0 (32))
num- I64 = (uN-fam0 (64))
num- F32 = (fN-fam0 (32))
num- F64 = (fN-fam0 (64))
num- _ = ⊤

inh-num--fun : (v-numtype : numtype) → Inhabited (num- v-numtype)
inh-num--fun I32 = record { default-val = (Inhabited.default-val (inh-iN-fun (sizenn (numtype-Inn Inn-I32)))) }
inh-num--fun I64 = record { default-val = (Inhabited.default-val (inh-iN-fun (sizenn (numtype-Inn Inn-I64)))) }
inh-num--fun F32 = record { default-val = (Inhabited.default-val (inh-fN-fun (sizenn (numtype-Fnn Fnn-F32)))) }
inh-num--fun F64 = record { default-val = (Inhabited.default-val (inh-fN-fun (sizenn (numtype-Fnn Fnn-F64)))) }

{- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:263.1-263.36 -}
pack- : (v-Pnn : Pnn) → Set
pack- v-Pnn = (uN-fam0 ((psize v-Pnn)))
pack- _ = ⊤

inh-pack--fun : (v-Pnn : Pnn) → Inhabited (pack- v-Pnn)
inh-pack--fun v-Pnn = record { default-val = (Inhabited.default-val (inh-iN-fun (psize v-Pnn))) }

{- Type Family Definition at: ../specification/wasm-2.0/1-syntax.spectec:265.1-265.23 -}
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
inh-lane--fun lanetype-I32 = record { default-val = (Inhabited.default-val (inh-num--fun I32)) }
inh-lane--fun lanetype-I64 = record { default-val = (Inhabited.default-val (inh-num--fun I64)) }
inh-lane--fun lanetype-F32 = record { default-val = (Inhabited.default-val (inh-num--fun F32)) }
inh-lane--fun lanetype-F64 = record { default-val = (Inhabited.default-val (inh-num--fun F64)) }
inh-lane--fun lanetype-I8 = record { default-val = (Inhabited.default-val (inh-pack--fun I8)) }
inh-lane--fun lanetype-I16 = record { default-val = (Inhabited.default-val (inh-pack--fun I16)) }
inh-lane--fun lanetype-I32 = record { default-val = (Inhabited.default-val (inh-iN-fun (lsize (lanetype-Jnn Jnn-I32)))) }
inh-lane--fun lanetype-I64 = record { default-val = (Inhabited.default-val (inh-iN-fun (lsize (lanetype-Jnn Jnn-I64)))) }
inh-lane--fun lanetype-I8 = record { default-val = (Inhabited.default-val (inh-iN-fun (lsize (lanetype-Jnn Jnn-I8)))) }
inh-lane--fun lanetype-I16 = record { default-val = (Inhabited.default-val (inh-iN-fun (lsize (lanetype-Jnn Jnn-I16)))) }

{- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:270.1-270.34 -}
vec- : (v-Vnn : Vnn) → Set
vec- v-Vnn = (uN-fam0 ((unwrap! (size (valtype-vectype v-Vnn)))))
vec- _ = ⊤

inh-vec--fun : (v-Vnn : Vnn) → Inhabited (vec- v-Vnn)
inh-vec--fun v-Vnn = record { default-val = (Inhabited.default-val (inh-vN-fun (unwrap! (size (valtype-vectype v-Vnn))))) }

{- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:272.1-272.35 -}
{-# TERMINATING #-}
fun-zero : (v-numtype : numtype) → (num- v-numtype)
fun-zero I32 = (mk-uN 0)
fun-zero I64 = (mk-uN 0)
fun-zero F32 = (fzero (unwrap! (size (valtype-Fnn Fnn-F32))))
fun-zero F64 = (fzero (unwrap! (size (valtype-Fnn Fnn-F64))))
fun-zero v-numtype = (Inhabited.default-val (inh-num--fun v-numtype))

{- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:279.1-279.42 -}
data sx : Set where
  U : sx
  S : sx

{- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:280.1-280.56 -}
data sz : Set where
  mk-sz : (i : ℕ) → sz {- 1 premise(s) dropped -}

{- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:280.1-280.56 -}
{-# TERMINATING #-}
proj-sz-0 : (x : sz) → (ℕ)
proj-sz-0 (mk-sz v-num-0) = (v-num-0)
proj-sz-0 x = (default-val)

instance
  proj-sz-0-coercion : Coerce sz (ℕ)
  proj-sz-0-coercion = record { coerce = proj-sz-0 }

{- Type Family Definition at: ../specification/wasm-2.0/1-syntax.spectec:282.1-282.22 -}
data unop--fam0 : Set where
  CLZ : unop--fam0
  CTZ : unop--fam0
  POPCNT : unop--fam0
  EXTEND : (n-111 : n) → unop--fam0

data unop--fam1 : Set where
  CLZ : unop--fam1
  CTZ : unop--fam1
  POPCNT : unop--fam1
  EXTEND : (n-112 : n) → unop--fam1

data unop--fam2 : Set where
  ABS : unop--fam2
  unop--NEG : unop--fam2
  SQRT : unop--fam2
  CEIL : unop--fam2
  FLOOR : unop--fam2
  TRUNC : unop--fam2
  NEAREST : unop--fam2

data unop--fam3 : Set where
  ABS : unop--fam3
  unop--NEG : unop--fam3
  SQRT : unop--fam3
  CEIL : unop--fam3
  FLOOR : unop--fam3
  TRUNC : unop--fam3
  NEAREST : unop--fam3

unop- : (v-numtype : numtype) → Set
unop- I32 = unop--fam0
unop- I64 = unop--fam1
unop- F32 = unop--fam2
unop- F64 = unop--fam3
unop- _ = ⊤

{- Type Family Definition at: ../specification/wasm-2.0/1-syntax.spectec:286.1-286.23 -}
data binop--fam0 : Set where
  ADD : binop--fam0
  SUB : binop--fam0
  MUL : binop--fam0
  DIV : (sx-3676 : sx) → binop--fam0
  REM : (sx-3677 : sx) → binop--fam0
  AND : binop--fam0
  OR : binop--fam0
  XOR : binop--fam0
  SHL : binop--fam0
  SHR : (sx-3678 : sx) → binop--fam0
  ROTL : binop--fam0
  ROTR : binop--fam0

data binop--fam1 : Set where
  ADD : binop--fam1
  SUB : binop--fam1
  MUL : binop--fam1
  DIV : (sx-3679 : sx) → binop--fam1
  REM : (sx-3680 : sx) → binop--fam1
  AND : binop--fam1
  OR : binop--fam1
  XOR : binop--fam1
  SHL : binop--fam1
  SHR : (sx-3681 : sx) → binop--fam1
  ROTL : binop--fam1
  ROTR : binop--fam1

data binop--fam2 : Set where
  ADD : binop--fam2
  SUB : binop--fam2
  MUL : binop--fam2
  DIV : binop--fam2
  MIN : binop--fam2
  MAX : binop--fam2
  COPYSIGN : binop--fam2

data binop--fam3 : Set where
  ADD : binop--fam3
  SUB : binop--fam3
  MUL : binop--fam3
  DIV : binop--fam3
  MIN : binop--fam3
  MAX : binop--fam3
  COPYSIGN : binop--fam3

binop- : (v-numtype : numtype) → Set
binop- I32 = binop--fam0
binop- I64 = binop--fam1
binop- F32 = binop--fam2
binop- F64 = binop--fam3
binop- _ = ⊤

{- Type Family Definition at: ../specification/wasm-2.0/1-syntax.spectec:293.1-293.24 -}
data testop--fam0 : Set where
  EQZ : testop--fam0

data testop--fam1 : Set where
  EQZ : testop--fam1

testop- : (v-numtype : numtype) → Set
testop- I32 = testop--fam0
testop- I64 = testop--fam1
testop- _ = ⊤

{- Type Family Definition at: ../specification/wasm-2.0/1-syntax.spectec:297.1-297.23 -}
data relop--fam0 : Set where
  EQ : relop--fam0
  NE : relop--fam0
  LT : (sx-3682 : sx) → relop--fam0
  GT : (sx-3683 : sx) → relop--fam0
  LE : (sx-3684 : sx) → relop--fam0
  GE : (sx-3685 : sx) → relop--fam0

data relop--fam1 : Set where
  EQ : relop--fam1
  NE : relop--fam1
  LT : (sx-3686 : sx) → relop--fam1
  GT : (sx-3687 : sx) → relop--fam1
  LE : (sx-3688 : sx) → relop--fam1
  GE : (sx-3689 : sx) → relop--fam1

data relop--fam2 : Set where
  EQ : relop--fam2
  NE : relop--fam2
  LT : relop--fam2
  GT : relop--fam2
  LE : relop--fam2
  GE : relop--fam2

data relop--fam3 : Set where
  EQ : relop--fam3
  NE : relop--fam3
  LT : relop--fam3
  GT : relop--fam3
  LE : relop--fam3
  GE : relop--fam3

relop- : (v-numtype : numtype) → Set
relop- I32 = relop--fam0
relop- I64 = relop--fam1
relop- F32 = relop--fam2
relop- F64 = relop--fam3
relop- _ = ⊤

{- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:305.1-313.16 -}
data cvtop : Set where
  cvtop-EXTEND : (v-sx : sx) → cvtop
  WRAP : cvtop
  CONVERT : (v-sx : sx) → cvtop
  cvtop-TRUNC : (v-sx : sx) → cvtop
  TRUNC-SAT : (v-sx : sx) → cvtop
  PROMOTE : cvtop
  DEMOTE : cvtop
  REINTERPRET : cvtop

{- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:320.1-320.69 -}
data ishape : Set where
  ishape-X : (v-Jnn : Jnn) → (v-dim : dim) → ishape

{- Auxiliary Definition at:  -}
{-# TERMINATING #-}
shape-ishape : (var-0 : ishape) → shape
shape-ishape (ishape-X x0 x1) = (X (lanetype-Jnn x0) x1)
shape-ishape var-0 = default-val

{- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:321.1-321.69 -}
data fshape : Set where
  fshape-X : (v-Fnn : Fnn) → (v-dim : dim) → fshape

{- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:322.1-322.69 -}
data pshape : Set where
  pshape-X : (v-Pnn : Pnn) → (v-dim : dim) → pshape

{- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:324.1-324.22 -}
{-# TERMINATING #-}
fun-dim : (v-shape : shape) → dim
fun-dim (X v-Lnn (mk-dim v-N)) = (mk-dim v-N)
fun-dim v-shape = default-val

{- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:325.1-325.41 -}
{-# TERMINATING #-}
shsize : (v-shape : shape) → ℕ
shsize (X v-Lnn (mk-dim v-N)) = ((lsize v-Lnn) * v-N)
shsize v-shape = default-val

{- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:327.1-327.20 -}
data vvunop : Set where
  NOT : vvunop

{- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:328.1-328.41 -}
data vvbinop : Set where
  vvbinop-AND : vvbinop
  ANDNOT : vvbinop
  vvbinop-OR : vvbinop
  vvbinop-XOR : vvbinop

{- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:329.1-329.28 -}
data vvternop : Set where
  BITSELECT : vvternop

{- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:330.1-330.27 -}
data vvtestop : Set where
  ANY-TRUE : vvtestop

{- Type Family Definition at: ../specification/wasm-2.0/1-syntax.spectec:332.1-332.21 -}
data vunop--fam0 (v-N : N) : Set where
  vunop--ABS : vunop--fam0 v-N
  vunop--NEG : vunop--fam0 v-N
  vunop--POPCNT : vunop--fam0 v-N {- 1 premise(s) dropped -}

data vunop--fam1 (v-N : N) : Set where
  vunop--ABS : vunop--fam1 v-N
  vunop--NEG : vunop--fam1 v-N
  vunop--POPCNT : vunop--fam1 v-N {- 1 premise(s) dropped -}

data vunop--fam2 (v-N : N) : Set where
  vunop--ABS : vunop--fam2 v-N
  vunop--NEG : vunop--fam2 v-N
  vunop--POPCNT : vunop--fam2 v-N {- 1 premise(s) dropped -}

data vunop--fam3 (v-N : N) : Set where
  vunop--ABS : vunop--fam3 v-N
  vunop--NEG : vunop--fam3 v-N
  vunop--POPCNT : vunop--fam3 v-N {- 1 premise(s) dropped -}

data vunop--fam4 (v-N : N) : Set where
  vunop--ABS : vunop--fam4 v-N
  vunop--NEG : vunop--fam4 v-N
  vunop--SQRT : vunop--fam4 v-N
  vunop--CEIL : vunop--fam4 v-N
  vunop--FLOOR : vunop--fam4 v-N
  vunop--TRUNC : vunop--fam4 v-N
  vunop--NEAREST : vunop--fam4 v-N

data vunop--fam5 (v-N : N) : Set where
  vunop--ABS : vunop--fam5 v-N
  vunop--NEG : vunop--fam5 v-N
  vunop--SQRT : vunop--fam5 v-N
  vunop--CEIL : vunop--fam5 v-N
  vunop--FLOOR : vunop--fam5 v-N
  vunop--TRUNC : vunop--fam5 v-N
  vunop--NEAREST : vunop--fam5 v-N

vunop- : (v-shape : shape) → Set
vunop- (X lanetype-I32 (mk-dim v-N)) = vunop--fam0 v-N
vunop- (X lanetype-I64 (mk-dim v-N)) = vunop--fam1 v-N
vunop- (X lanetype-I8 (mk-dim v-N)) = vunop--fam2 v-N
vunop- (X lanetype-I16 (mk-dim v-N)) = vunop--fam3 v-N
vunop- (X lanetype-F32 (mk-dim v-N)) = vunop--fam4 v-N
vunop- (X lanetype-F64 (mk-dim v-N)) = vunop--fam5 v-N
vunop- _ = ⊤

{- Type Family Definition at: ../specification/wasm-2.0/1-syntax.spectec:337.1-337.22 -}
data vbinop--fam0 (v-N : N) : Set where
  vbinop--ADD : vbinop--fam0 v-N
  vbinop--SUB : vbinop--fam0 v-N
  ADD-SAT : (sx-3690 : sx) → vbinop--fam0 v-N {- 1 premise(s) dropped -}
  SUB-SAT : (sx-3691 : sx) → vbinop--fam0 v-N {- 1 premise(s) dropped -}
  vbinop--MUL : vbinop--fam0 v-N {- 1 premise(s) dropped -}
  AVGRU : vbinop--fam0 v-N {- 1 premise(s) dropped -}
  Q15MULR-SATS : vbinop--fam0 v-N {- 1 premise(s) dropped -}
  vbinop--MIN : (sx-3692 : sx) → vbinop--fam0 v-N {- 1 premise(s) dropped -}
  vbinop--MAX : (sx-3693 : sx) → vbinop--fam0 v-N {- 1 premise(s) dropped -}

data vbinop--fam1 (v-N : N) : Set where
  vbinop--ADD : vbinop--fam1 v-N
  vbinop--SUB : vbinop--fam1 v-N
  ADD-SAT : (sx-3694 : sx) → vbinop--fam1 v-N {- 1 premise(s) dropped -}
  SUB-SAT : (sx-3695 : sx) → vbinop--fam1 v-N {- 1 premise(s) dropped -}
  vbinop--MUL : vbinop--fam1 v-N {- 1 premise(s) dropped -}
  AVGRU : vbinop--fam1 v-N {- 1 premise(s) dropped -}
  Q15MULR-SATS : vbinop--fam1 v-N {- 1 premise(s) dropped -}
  vbinop--MIN : (sx-3696 : sx) → vbinop--fam1 v-N {- 1 premise(s) dropped -}
  vbinop--MAX : (sx-3697 : sx) → vbinop--fam1 v-N {- 1 premise(s) dropped -}

data vbinop--fam2 (v-N : N) : Set where
  vbinop--ADD : vbinop--fam2 v-N
  vbinop--SUB : vbinop--fam2 v-N
  ADD-SAT : (sx-3698 : sx) → vbinop--fam2 v-N {- 1 premise(s) dropped -}
  SUB-SAT : (sx-3699 : sx) → vbinop--fam2 v-N {- 1 premise(s) dropped -}
  vbinop--MUL : vbinop--fam2 v-N {- 1 premise(s) dropped -}
  AVGRU : vbinop--fam2 v-N {- 1 premise(s) dropped -}
  Q15MULR-SATS : vbinop--fam2 v-N {- 1 premise(s) dropped -}
  vbinop--MIN : (sx-3700 : sx) → vbinop--fam2 v-N {- 1 premise(s) dropped -}
  vbinop--MAX : (sx-3701 : sx) → vbinop--fam2 v-N {- 1 premise(s) dropped -}

data vbinop--fam3 (v-N : N) : Set where
  vbinop--ADD : vbinop--fam3 v-N
  vbinop--SUB : vbinop--fam3 v-N
  ADD-SAT : (sx-3702 : sx) → vbinop--fam3 v-N {- 1 premise(s) dropped -}
  SUB-SAT : (sx-3703 : sx) → vbinop--fam3 v-N {- 1 premise(s) dropped -}
  vbinop--MUL : vbinop--fam3 v-N {- 1 premise(s) dropped -}
  AVGRU : vbinop--fam3 v-N {- 1 premise(s) dropped -}
  Q15MULR-SATS : vbinop--fam3 v-N {- 1 premise(s) dropped -}
  vbinop--MIN : (sx-3704 : sx) → vbinop--fam3 v-N {- 1 premise(s) dropped -}
  vbinop--MAX : (sx-3705 : sx) → vbinop--fam3 v-N {- 1 premise(s) dropped -}

data vbinop--fam4 (v-N : N) : Set where
  vbinop--ADD : vbinop--fam4 v-N
  vbinop--SUB : vbinop--fam4 v-N
  vbinop--MUL : vbinop--fam4 v-N
  vbinop--DIV : vbinop--fam4 v-N
  vbinop--MIN : vbinop--fam4 v-N
  vbinop--MAX : vbinop--fam4 v-N
  PMIN : vbinop--fam4 v-N
  PMAX : vbinop--fam4 v-N

data vbinop--fam5 (v-N : N) : Set where
  vbinop--ADD : vbinop--fam5 v-N
  vbinop--SUB : vbinop--fam5 v-N
  vbinop--MUL : vbinop--fam5 v-N
  vbinop--DIV : vbinop--fam5 v-N
  vbinop--MIN : vbinop--fam5 v-N
  vbinop--MAX : vbinop--fam5 v-N
  PMIN : vbinop--fam5 v-N
  PMAX : vbinop--fam5 v-N

vbinop- : (v-shape : shape) → Set
vbinop- (X lanetype-I32 (mk-dim v-N)) = vbinop--fam0 v-N
vbinop- (X lanetype-I64 (mk-dim v-N)) = vbinop--fam1 v-N
vbinop- (X lanetype-I8 (mk-dim v-N)) = vbinop--fam2 v-N
vbinop- (X lanetype-I16 (mk-dim v-N)) = vbinop--fam3 v-N
vbinop- (X lanetype-F32 (mk-dim v-N)) = vbinop--fam4 v-N
vbinop- (X lanetype-F64 (mk-dim v-N)) = vbinop--fam5 v-N
vbinop- _ = ⊤

{- Type Family Definition at: ../specification/wasm-2.0/1-syntax.spectec:350.1-350.23 -}
data vtestop--fam0 (v-N : N) : Set where
  ALL-TRUE : vtestop--fam0 v-N

data vtestop--fam1 (v-N : N) : Set where
  ALL-TRUE : vtestop--fam1 v-N

data vtestop--fam2 (v-N : N) : Set where
  ALL-TRUE : vtestop--fam2 v-N

data vtestop--fam3 (v-N : N) : Set where
  ALL-TRUE : vtestop--fam3 v-N

vtestop- : (v-shape : shape) → Set
vtestop- (X lanetype-I32 (mk-dim v-N)) = vtestop--fam0 v-N
vtestop- (X lanetype-I64 (mk-dim v-N)) = vtestop--fam1 v-N
vtestop- (X lanetype-I8 (mk-dim v-N)) = vtestop--fam2 v-N
vtestop- (X lanetype-I16 (mk-dim v-N)) = vtestop--fam3 v-N
vtestop- _ = ⊤

{- Type Family Definition at: ../specification/wasm-2.0/1-syntax.spectec:354.1-354.22 -}
data vrelop--fam0 (v-N : N) : Set where
  vrelop--EQ : vrelop--fam0 v-N
  vrelop--NE : vrelop--fam0 v-N
  vrelop--LT : (sx-3706 : sx) → vrelop--fam0 v-N {- 1 premise(s) dropped -}
  vrelop--GT : (sx-3707 : sx) → vrelop--fam0 v-N {- 1 premise(s) dropped -}
  vrelop--LE : (sx-3708 : sx) → vrelop--fam0 v-N {- 1 premise(s) dropped -}
  vrelop--GE : (sx-3709 : sx) → vrelop--fam0 v-N {- 1 premise(s) dropped -}

data vrelop--fam1 (v-N : N) : Set where
  vrelop--EQ : vrelop--fam1 v-N
  vrelop--NE : vrelop--fam1 v-N
  vrelop--LT : (sx-3710 : sx) → vrelop--fam1 v-N {- 1 premise(s) dropped -}
  vrelop--GT : (sx-3711 : sx) → vrelop--fam1 v-N {- 1 premise(s) dropped -}
  vrelop--LE : (sx-3712 : sx) → vrelop--fam1 v-N {- 1 premise(s) dropped -}
  vrelop--GE : (sx-3713 : sx) → vrelop--fam1 v-N {- 1 premise(s) dropped -}

data vrelop--fam2 (v-N : N) : Set where
  vrelop--EQ : vrelop--fam2 v-N
  vrelop--NE : vrelop--fam2 v-N
  vrelop--LT : (sx-3714 : sx) → vrelop--fam2 v-N {- 1 premise(s) dropped -}
  vrelop--GT : (sx-3715 : sx) → vrelop--fam2 v-N {- 1 premise(s) dropped -}
  vrelop--LE : (sx-3716 : sx) → vrelop--fam2 v-N {- 1 premise(s) dropped -}
  vrelop--GE : (sx-3717 : sx) → vrelop--fam2 v-N {- 1 premise(s) dropped -}

data vrelop--fam3 (v-N : N) : Set where
  vrelop--EQ : vrelop--fam3 v-N
  vrelop--NE : vrelop--fam3 v-N
  vrelop--LT : (sx-3718 : sx) → vrelop--fam3 v-N {- 1 premise(s) dropped -}
  vrelop--GT : (sx-3719 : sx) → vrelop--fam3 v-N {- 1 premise(s) dropped -}
  vrelop--LE : (sx-3720 : sx) → vrelop--fam3 v-N {- 1 premise(s) dropped -}
  vrelop--GE : (sx-3721 : sx) → vrelop--fam3 v-N {- 1 premise(s) dropped -}

data vrelop--fam4 (v-N : N) : Set where
  vrelop--EQ : vrelop--fam4 v-N
  vrelop--NE : vrelop--fam4 v-N
  vrelop--LT : vrelop--fam4 v-N
  vrelop--GT : vrelop--fam4 v-N
  vrelop--LE : vrelop--fam4 v-N
  vrelop--GE : vrelop--fam4 v-N

data vrelop--fam5 (v-N : N) : Set where
  vrelop--EQ : vrelop--fam5 v-N
  vrelop--NE : vrelop--fam5 v-N
  vrelop--LT : vrelop--fam5 v-N
  vrelop--GT : vrelop--fam5 v-N
  vrelop--LE : vrelop--fam5 v-N
  vrelop--GE : vrelop--fam5 v-N

vrelop- : (v-shape : shape) → Set
vrelop- (X lanetype-I32 (mk-dim v-N)) = vrelop--fam0 v-N
vrelop- (X lanetype-I64 (mk-dim v-N)) = vrelop--fam1 v-N
vrelop- (X lanetype-I8 (mk-dim v-N)) = vrelop--fam2 v-N
vrelop- (X lanetype-I16 (mk-dim v-N)) = vrelop--fam3 v-N
vrelop- (X lanetype-F32 (mk-dim v-N)) = vrelop--fam4 v-N
vrelop- (X lanetype-F64 (mk-dim v-N)) = vrelop--fam5 v-N
vrelop- _ = ⊤

{- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:362.1-362.48 -}
data half : Set where
  LOW : half
  HIGH : half

instance
  inh-half : Inhabited half
  inh-half = record { default-val = LOW }

{- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:363.1-363.19 -}
data zero' : Set where
  ZERO : zero'

instance
  inh-zero' : Inhabited zero'
  inh-zero' = record { default-val = ZERO }

{- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:365.1-365.99 -}
data vcvtop : Set where
  vcvtop-EXTEND : (v-half : half) → (v-sx : sx) → vcvtop
  vcvtop-TRUNC-SAT : (v-sx : sx) → (zero-opt : (Maybe zero')) → vcvtop
  vcvtop-CONVERT : (half-opt : (Maybe half)) → (v-sx : sx) → vcvtop
  vcvtop-DEMOTE : (v-zero : zero') → vcvtop
  PROMOTELOW : vcvtop

{- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:367.1-367.25 -}
data vshiftop--fam0 (v-Jnn : Jnn) (v-N : N) : Set where
  vshiftop--SHL : vshiftop--fam0 v-Jnn v-N
  vshiftop--SHR : (v-sx : sx) → vshiftop--fam0 v-Jnn v-N

vshiftop- : (v-ishape : ishape) → Set
vshiftop- (ishape-X v-Jnn (mk-dim v-N)) = vshiftop--fam0 v-Jnn v-N
vshiftop- _ = ⊤

{- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:370.1-370.25 -}
data vextunop--fam0 (v-Jnn : Jnn) (v-N : N) : Set where
  EXTADD-PAIRWISE : (v-sx : sx) → vextunop--fam0 v-Jnn v-N {- 1 premise(s) dropped -}

vextunop- : (v-ishape : ishape) → Set
vextunop- (ishape-X v-Jnn (mk-dim v-N)) = vextunop--fam0 v-Jnn v-N
vextunop- _ = ⊤

{- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:373.1-373.26 -}
data vextbinop--fam0 (v-Jnn : Jnn) (v-N : N) : Set where
  EXTMUL : (v-half : half) → (v-sx : sx) → vextbinop--fam0 v-Jnn v-N
  DOTS : vextbinop--fam0 v-Jnn v-N {- 1 premise(s) dropped -}

vextbinop- : (v-ishape : ishape) → Set
vextbinop- (ishape-X v-Jnn (mk-dim v-N)) = vextbinop--fam0 v-Jnn v-N
vextbinop- _ = ⊤

{- Record Creation Definition at: ../specification/wasm-2.0/1-syntax.spectec:381.1-381.69 -}
record memarg : Set where
  constructor mk-memarg
  field
    ALIGN : u32
    OFFSET : u32
open memarg

instance
  append-memarg : HasAppend (memarg)
  append-memarg = record { append = λ arg1 arg2 → record {
    ALIGN = ALIGN arg1 {- FIXME - Non-trivial append -} ;
    OFFSET = OFFSET arg1 {- FIXME - Non-trivial append -} } }

{- Type Family Definition at: ../specification/wasm-2.0/1-syntax.spectec:385.1-385.24 -}
data loadop--fam0 : Set where
  mk-loadop- : (sz-151 : sz) → (sx-3722 : sx) → loadop--fam0 {- 1 premise(s) dropped -}

data loadop--fam1 : Set where
  mk-loadop- : (sz-152 : sz) → (sx-3723 : sx) → loadop--fam1 {- 1 premise(s) dropped -}

loadop- : (v-numtype : numtype) → Set
loadop- I32 = loadop--fam0
loadop- I64 = loadop--fam1
loadop- _ = ⊤

{- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:388.1-391.46 -}
data vloadop : Set where
  SHAPEX- : (_ : ℕ) → (_ : ℕ) → (v-sx : sx) → vloadop
  SPLAT : (_ : ℕ) → vloadop
  vloadop-ZERO : (_ : ℕ) → vloadop

{- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:398.1-400.17 -}
data blocktype : Set where
  -RESULT : (valtype-opt : (Maybe valtype)) → blocktype
  -IDX : (v-typeidx : typeidx) → blocktype

{- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:519.1-520.22 -}
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
  CALL : (v-funcidx : funcidx) → instr
  CALL-INDIRECT : (v-tableidx : tableidx) → (v-typeidx : typeidx) → instr
  RETURN : instr
  CONST : (v-numtype : numtype) → (_ : (num- v-numtype)) → instr
  UNOP : (v-numtype : numtype) → (_ : (unop- v-numtype)) → instr
  BINOP : (v-numtype : numtype) → (_ : (binop- v-numtype)) → instr
  TESTOP : (v-numtype : numtype) → (_ : (testop- v-numtype)) → instr
  RELOP : (v-numtype : numtype) → (_ : (relop- v-numtype)) → instr
  CVTOP : (numtype-1 : numtype) → (numtype-2 : numtype) → (v-cvtop : cvtop) → instr {- 1 premise(s) dropped -}
  instr-EXTEND : (v-numtype : numtype) → (v-n : n) → instr
  VCONST : (v-vectype : vectype) → (_ : (uN-fam0 ((unwrap! (size (valtype-vectype v-vectype)))))) → instr
  VVUNOP : (v-vectype : vectype) → (v-vvunop : vvunop) → instr
  VVBINOP : (v-vectype : vectype) → (v-vvbinop : vvbinop) → instr
  VVTERNOP : (v-vectype : vectype) → (v-vvternop : vvternop) → instr
  VVTESTOP : (v-vectype : vectype) → (v-vvtestop : vvtestop) → instr
  VUNOP : (v-shape : shape) → (_ : (vunop- v-shape)) → instr
  VBINOP : (v-shape : shape) → (_ : (vbinop- v-shape)) → instr
  VTESTOP : (v-shape : shape) → (_ : (vtestop- v-shape)) → instr
  VRELOP : (v-shape : shape) → (_ : (vrelop- v-shape)) → instr
  VSHIFTOP : (v-ishape : ishape) → (_ : (vshiftop- v-ishape)) → instr
  VBITMASK : (v-ishape : ishape) → instr
  VSWIZZLE : (v-ishape : ishape) → instr {- 1 premise(s) dropped -}
  VSHUFFLE : (v-ishape : ishape) → (laneidx-lst : (List laneidx)) → instr {- 1 premise(s) dropped -}
  VSPLAT : (v-shape : shape) → instr
  VEXTRACT-LANE : (v-shape : shape) → (sx-opt : (Maybe sx)) → (v-laneidx : laneidx) → instr {- 1 premise(s) dropped -}
  VREPLACE-LANE : (v-shape : shape) → (v-laneidx : laneidx) → instr
  VEXTUNOP : (ishape-1 : ishape) → (ishape-2 : ishape) → (_ : (vextunop- ishape-1)) → instr {- 1 premise(s) dropped -}
  VEXTBINOP : (ishape-1 : ishape) → (ishape-2 : ishape) → (_ : (vextbinop- ishape-1)) → instr {- 1 premise(s) dropped -}
  VNARROW : (ishape-1 : ishape) → (ishape-2 : ishape) → (v-sx : sx) → instr {- 1 premise(s) dropped -}
  VCVTOP : (v-shape : shape) → (v-shape : shape) → (v-vcvtop : vcvtop) → instr
  REF-NULL : (v-reftype : reftype) → instr
  REF-FUNC : (v-funcidx : funcidx) → instr
  REF-IS-NULL : instr
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
  LOAD : (v-numtype : numtype) → (_ : (Maybe (loadop- v-numtype))) → (v-memarg : memarg) → instr
  STORE : (v-numtype : numtype) → (sz-opt : (Maybe sz)) → (v-memarg : memarg) → instr {- 1 premise(s) dropped -}
  VLOAD : (v-vectype : vectype) → (vloadop-opt : (Maybe vloadop)) → (v-memarg : memarg) → instr
  VLOAD-LANE : (v-vectype : vectype) → (v-sz : sz) → (v-memarg : memarg) → (v-laneidx : laneidx) → instr
  VSTORE : (v-vectype : vectype) → (v-memarg : memarg) → instr
  VSTORE-LANE : (v-vectype : vectype) → (v-sz : sz) → (v-memarg : memarg) → (v-laneidx : laneidx) → instr
  MEMORY-SIZE : instr
  MEMORY-GROW : instr
  MEMORY-FILL : instr
  MEMORY-COPY : instr
  MEMORY-INIT : (v-dataidx : dataidx) → instr
  DATA-DROP : (v-dataidx : dataidx) → instr

instance
  inh-instr : Inhabited instr
  inh-instr = record { default-val = NOP }

{- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:523.1-524.9 -}
expr : Set
expr = (List instr)

{- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:536.1-536.59 -}
data elemmode : Set where
  ACTIVE : (v-tableidx : tableidx) → (v-expr : expr) → elemmode
  PASSIVE : elemmode
  DECLARE : elemmode

instance
  inh-elemmode : Inhabited elemmode
  inh-elemmode = record { default-val = (ACTIVE (default-val) (default-val)) }

{- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:537.1-537.47 -}
data datamode : Set where
  datamode-ACTIVE : (v-memidx : memidx) → (v-expr : expr) → datamode
  datamode-PASSIVE : datamode

instance
  inh-datamode : Inhabited datamode
  inh-datamode = record { default-val = (datamode-ACTIVE (default-val) (default-val)) }

{- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:539.1-540.16 -}
data type : Set where
  TYPE : (v-functype : functype) → type

{- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:541.1-542.16 -}
data local : Set where
  LOCAL : (v-valtype : valtype) → local

instance
  inh-local : Inhabited local
  inh-local = record { default-val = (LOCAL (default-val)) }

{- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:543.1-544.27 -}
data func : Set where
  func-FUNC : (v-typeidx : typeidx) → (local-lst : (List local)) → (v-expr : expr) → func

instance
  inh-func : Inhabited func
  inh-func = record { default-val = (func-FUNC (default-val) ([]) (default-val)) }

{- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:545.1-546.25 -}
data global : Set where
  global-GLOBAL : (v-globaltype : globaltype) → (v-expr : expr) → global

{- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:547.1-548.18 -}
data table : Set where
  table-TABLE : (v-tabletype : tabletype) → table

{- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:549.1-550.17 -}
data mem : Set where
  MEMORY : (v-memtype : memtype) → mem

{- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:551.1-552.30 -}
data elem : Set where
  ELEM : (v-reftype : reftype) → (expr-lst : (List expr)) → (v-elemmode : elemmode) → elem

instance
  inh-elem : Inhabited elem
  inh-elem = record { default-val = (ELEM (default-val) ([]) (default-val)) }

{- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:553.1-554.22 -}
data data' : Set where
  DATA : (byte-lst : (List byte)) → (v-datamode : datamode) → data'

instance
  inh-data' : Inhabited data'
  inh-data' = record { default-val = (DATA ([]) (default-val)) }

{- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:555.1-556.16 -}
data start : Set where
  START : (v-funcidx : funcidx) → start

{- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:558.1-559.66 -}
data externidx : Set where
  externidx-FUNC : (v-funcidx : funcidx) → externidx
  externidx-GLOBAL : (v-globalidx : globalidx) → externidx
  externidx-TABLE : (v-tableidx : tableidx) → externidx
  externidx-MEM : (v-memidx : memidx) → externidx

{- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:560.1-561.24 -}
data export : Set where
  EXPORT : (v-name : name) → (v-externidx : externidx) → export

{- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:562.1-563.30 -}
data import' : Set where
  IMPORT : (v-name : name) → (v-name : name) → (v-externtype : externtype) → import'

{- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:565.1-566.76 -}
data module' : Set where
  MODULE : (type-lst : (List type)) → (import-lst : (List import')) → (func-lst : (List func)) → (global-lst : (List global)) → (table-lst : (List table)) → (mem-lst : (List mem)) → (elem-lst : (List elem)) → (data-lst : (List data')) → (start-opt : (Maybe start)) → (export-lst : (List export)) → module'

{- Auxiliary Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:7.1-7.59 -}
{-# TERMINATING #-}
concat-bytes : (var-0-lst-lst : (List (List byte))) → (List byte)
concat-bytes [] = []
concat-bytes (b-lst ∷ b'-lst-lst) = (b-lst ++ (concat-bytes b'-lst-lst))
concat-bytes var-0-lst-lst = []

{- Auxiliary Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:28.1-28.32 -}
{-# TERMINATING #-}
unpack : (v-lanetype : lanetype) → numtype
unpack lanetype-I32 = I32
unpack lanetype-I64 = I64
unpack lanetype-F32 = F32
unpack lanetype-F64 = F64
unpack lanetype-I8 = I32
unpack lanetype-I16 = I32
unpack v-lanetype = default-val

{- Auxiliary Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:44.1-44.54 -}
{-# TERMINATING #-}
shunpack : (v-shape : shape) → numtype
shunpack (X v-Lnn (mk-dim v-N)) = (unpack v-Lnn)
shunpack v-shape = default-val

{- Auxiliary Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:51.1-51.64 -}
{-# TERMINATING #-}
funcsxt : (var-0-lst : (List externtype)) → (List functype)
funcsxt [] = []
funcsxt ((FUNC ft) ∷ xt-lst) = ((ft ∷ []) ++ (funcsxt xt-lst))
funcsxt (v-externtype ∷ xt-lst) = (funcsxt xt-lst)
funcsxt var-0-lst = []

{- Auxiliary Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:52.1-52.66 -}
{-# TERMINATING #-}
globalsxt : (var-0-lst : (List externtype)) → (List globaltype)
globalsxt [] = []
globalsxt ((GLOBAL gt) ∷ xt-lst) = ((gt ∷ []) ++ (globalsxt xt-lst))
globalsxt (v-externtype ∷ xt-lst) = (globalsxt xt-lst)
globalsxt var-0-lst = []

{- Auxiliary Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:53.1-53.65 -}
{-# TERMINATING #-}
tablesxt : (var-0-lst : (List externtype)) → (List tabletype)
tablesxt [] = []
tablesxt ((TABLE tt') ∷ xt-lst) = ((tt' ∷ []) ++ (tablesxt xt-lst))
tablesxt (v-externtype ∷ xt-lst) = (tablesxt xt-lst)
tablesxt var-0-lst = []

{- Auxiliary Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:54.1-54.63 -}
{-# TERMINATING #-}
memsxt : (var-0-lst : (List externtype)) → (List memtype)
memsxt [] = []
memsxt ((MEM mt) ∷ xt-lst) = ((mt ∷ []) ++ (memsxt xt-lst))
memsxt (v-externtype ∷ xt-lst) = (memsxt xt-lst)
memsxt var-0-lst = []

{- Auxiliary Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:80.1-80.61 -}
{-# TERMINATING #-}
dataidx-instr : (v-instr : instr) → (List dataidx)
dataidx-instr (MEMORY-INIT x) = (x ∷ [])
dataidx-instr (DATA-DROP x) = (x ∷ [])
dataidx-instr in' = []

{- Auxiliary Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:85.1-85.63 -}
{-# TERMINATING #-}
dataidx-instrs : (var-0-lst : (List instr)) → (List dataidx)
dataidx-instrs [] = []
dataidx-instrs (v-instr ∷ instr'-lst) = ((dataidx-instr v-instr) ++ (dataidx-instrs instr'-lst))
dataidx-instrs var-0-lst = []

{- Auxiliary Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:89.1-89.59 -}
{-# TERMINATING #-}
dataidx-expr : (v-expr : expr) → (List dataidx)
dataidx-expr in-lst = (dataidx-instrs in-lst)

{- Auxiliary Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:92.1-92.59 -}
{-# TERMINATING #-}
dataidx-func : (v-func : func) → (List dataidx)
dataidx-func (func-FUNC x loc-lst e) = (dataidx-expr e)
dataidx-func v-func = []

{- Auxiliary Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:95.1-95.61 -}
{-# TERMINATING #-}
dataidx-funcs : (var-0-lst : (List func)) → (List dataidx)
dataidx-funcs [] = []
dataidx-funcs (v-func ∷ func'-lst) = ((dataidx-func v-func) ++ (dataidx-funcs func'-lst))
dataidx-funcs var-0-lst = []

{- Auxiliary Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:106.1-106.35 -}
memarg0 : memarg
memarg0 = record { ALIGN = (mk-uN 0) ; OFFSET = (mk-uN 0) }

{- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:7.1-7.41 -}
postulate s33-to-u32 : ∀ (v-s33 : s33) → u32

{- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:9.1-9.22 -}
{-# TERMINATING #-}
bool : (v-bool : Bool) → ℕ
bool false = 0
bool true = 1
bool v-bool = default-val

{- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:13.1-13.23 -}
postulate truncz : ∀ (rat : ℕ) → ℕ

{- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:20.1-20.54 -}
postulate signed- : ∀ (v-N : N) (nat : ℕ) → ℕ

{- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:24.1-24.70 -}
postulate inv-signed- : ∀ (v-N : N) (int : ℕ) → ℕ

{- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:31.1-31.61 -}
{-# TERMINATING #-}
sat-u- : (v-N : N) (int : ℕ) → ℕ
sat-u- v-N i = (if (i <? (coerce {B = ℕ} 0)) then 0 else (if (i >? ((coerce {B = ℕ} (2 ^ v-N)) – (coerce {B = ℕ} 1))) then (coerce {B = ℕ} ((coerce {B = ℕ} (2 ^ v-N)) – (coerce {B = ℕ} 1))) else (coerce {B = ℕ} i)))

{- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:36.1-36.61 -}
{-# TERMINATING #-}
sat-s- : (v-N : N) (int : ℕ) → ℕ
sat-s- v-N i = (if (i <? (0 – (coerce {B = ℕ} (2 ^ (coerce {B = ℕ} ((coerce {B = ℕ} v-N) – (coerce {B = ℕ} 1))))))) then (0 – (coerce {B = ℕ} (2 ^ (coerce {B = ℕ} ((coerce {B = ℕ} v-N) – (coerce {B = ℕ} 1)))))) else (if (i >? ((coerce {B = ℕ} (2 ^ (coerce {B = ℕ} ((coerce {B = ℕ} v-N) – (coerce {B = ℕ} 1))))) – (coerce {B = ℕ} 1))) then ((coerce {B = ℕ} (2 ^ (coerce {B = ℕ} ((coerce {B = ℕ} v-N) – (coerce {B = ℕ} 1))))) – (coerce {B = ℕ} 1)) else i))

{- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:56.1-56.89 -}
postulate extend-- : ∀ (v-M : M) (v-N : N) (v-sx : sx) (v-iN : (uN-fam0 (v-M))) → (uN-fam0 (v-N))

{- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:224.1-224.30 -}
postulate fabs- : ∀ (v-N : N) (v-fN : (fN-fam0 (v-N))) → (List (fN-fam0 (v-N)))

{- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:227.1-227.31 -}
postulate fceil- : ∀ (v-N : N) (v-fN : (fN-fam0 (v-N))) → (List (fN-fam0 (v-N)))

{- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:228.1-228.32 -}
postulate ffloor- : ∀ (v-N : N) (v-fN : (fN-fam0 (v-N))) → (List (fN-fam0 (v-N)))

{- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:230.1-230.34 -}
postulate fnearest- : ∀ (v-N : N) (v-fN : (fN-fam0 (v-N))) → (List (fN-fam0 (v-N)))

{- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:225.1-225.30 -}
postulate fneg- : ∀ (v-N : N) (v-fN : (fN-fam0 (v-N))) → (List (fN-fam0 (v-N)))

{- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:226.1-226.31 -}
postulate fsqrt- : ∀ (v-N : N) (v-fN : (fN-fam0 (v-N))) → (List (fN-fam0 (v-N)))

{- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:229.1-229.32 -}
postulate ftrunc- : ∀ (v-N : N) (v-fN : (fN-fam0 (v-N))) → (List (fN-fam0 (v-N)))

{- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:120.1-120.29 -}
postulate iclz- : ∀ (v-N : N) (v-iN : (uN-fam0 (v-N))) → (uN-fam0 (v-N))

{- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:121.1-121.29 -}
postulate ictz- : ∀ (v-N : N) (v-iN : (uN-fam0 (v-N))) → (uN-fam0 (v-N))

{- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:122.1-122.32 -}
postulate ipopcnt- : ∀ (v-N : N) (v-iN : (uN-fam0 (v-N))) → (uN-fam0 (v-N))

{- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:55.1-55.33 -}
postulate wrap-- : ∀ (v-M : M) (v-N : N) (v-iN : (uN-fam0 (v-M))) → (uN-fam0 (v-N))

{- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:44.1-45.32 -}
{-# TERMINATING #-}
fun-unop- : (v-numtype : numtype) (v-unop- : (unop- v-numtype)) (v-num- : (num- v-numtype)) → (List (num- v-numtype))
fun-unop- I32 CLZ v-iN = ((iclz- (sizenn (numtype-Inn Inn-I32)) v-iN) ∷ [])
fun-unop- I64 CLZ v-iN = ((iclz- (sizenn (numtype-Inn Inn-I64)) v-iN) ∷ [])
fun-unop- I32 CTZ v-iN = ((ictz- (sizenn (numtype-Inn Inn-I32)) v-iN) ∷ [])
fun-unop- I64 CTZ v-iN = ((ictz- (sizenn (numtype-Inn Inn-I64)) v-iN) ∷ [])
fun-unop- I32 POPCNT v-iN = ((ipopcnt- (sizenn (numtype-Inn Inn-I32)) v-iN) ∷ [])
fun-unop- I64 POPCNT v-iN = ((ipopcnt- (sizenn (numtype-Inn Inn-I64)) v-iN) ∷ [])
fun-unop- I32 (EXTEND v-M) v-iN = ((extend-- v-M (sizenn (numtype-Inn Inn-I32)) S (wrap-- (sizenn (numtype-Inn Inn-I32)) v-M v-iN)) ∷ [])
fun-unop- I64 (EXTEND v-M) v-iN = ((extend-- v-M (sizenn (numtype-Inn Inn-I64)) S (wrap-- (sizenn (numtype-Inn Inn-I64)) v-M v-iN)) ∷ [])
fun-unop- F32 ABS v-fN = (fabs- (sizenn (numtype-Fnn Fnn-F32)) v-fN)
fun-unop- F64 ABS v-fN = (fabs- (sizenn (numtype-Fnn Fnn-F64)) v-fN)
fun-unop- F32 unop--NEG v-fN = (fneg- (sizenn (numtype-Fnn Fnn-F32)) v-fN)
fun-unop- F64 unop--NEG v-fN = (fneg- (sizenn (numtype-Fnn Fnn-F64)) v-fN)
fun-unop- F32 SQRT v-fN = (fsqrt- (sizenn (numtype-Fnn Fnn-F32)) v-fN)
fun-unop- F64 SQRT v-fN = (fsqrt- (sizenn (numtype-Fnn Fnn-F64)) v-fN)
fun-unop- F32 CEIL v-fN = (fceil- (sizenn (numtype-Fnn Fnn-F32)) v-fN)
fun-unop- F64 CEIL v-fN = (fceil- (sizenn (numtype-Fnn Fnn-F64)) v-fN)
fun-unop- F32 FLOOR v-fN = (ffloor- (sizenn (numtype-Fnn Fnn-F32)) v-fN)
fun-unop- F64 FLOOR v-fN = (ffloor- (sizenn (numtype-Fnn Fnn-F64)) v-fN)
fun-unop- F32 TRUNC v-fN = (ftrunc- (sizenn (numtype-Fnn Fnn-F32)) v-fN)
fun-unop- F64 TRUNC v-fN = (ftrunc- (sizenn (numtype-Fnn Fnn-F64)) v-fN)
fun-unop- F32 NEAREST v-fN = (fnearest- (sizenn (numtype-Fnn Fnn-F32)) v-fN)
fun-unop- F64 NEAREST v-fN = (fnearest- (sizenn (numtype-Fnn Fnn-F64)) v-fN)
fun-unop- v-numtype v-unop- v-num- = []

{- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:215.1-215.37 -}
postulate fadd- : ∀ (v-N : N) (v-fN : (fN-fam0 (v-N))) (fN-0 : (fN-fam0 (v-N))) → (List (fN-fam0 (v-N)))

{- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:223.1-223.42 -}
postulate fcopysign- : ∀ (v-N : N) (v-fN : (fN-fam0 (v-N))) (fN-0 : (fN-fam0 (v-N))) → (List (fN-fam0 (v-N)))

{- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:218.1-218.37 -}
postulate fdiv- : ∀ (v-N : N) (v-fN : (fN-fam0 (v-N))) (fN-0 : (fN-fam0 (v-N))) → (List (fN-fam0 (v-N)))

{- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:220.1-220.37 -}
postulate fmax- : ∀ (v-N : N) (v-fN : (fN-fam0 (v-N))) (fN-0 : (fN-fam0 (v-N))) → (List (fN-fam0 (v-N)))

{- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:219.1-219.37 -}
postulate fmin- : ∀ (v-N : N) (v-fN : (fN-fam0 (v-N))) (fN-0 : (fN-fam0 (v-N))) → (List (fN-fam0 (v-N)))

{- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:217.1-217.37 -}
postulate fmul- : ∀ (v-N : N) (v-fN : (fN-fam0 (v-N))) (fN-0 : (fN-fam0 (v-N))) → (List (fN-fam0 (v-N)))

{- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:216.1-216.37 -}
postulate fsub- : ∀ (v-N : N) (v-fN : (fN-fam0 (v-N))) (fN-0 : (fN-fam0 (v-N))) → (List (fN-fam0 (v-N)))

{- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:105.1-105.36 -}
{-# TERMINATING #-}
iadd- : (v-N : N) (v-iN : (uN-fam0 (v-N))) (iN-0 : (uN-fam0 (v-N))) → (uN-fam0 (v-N))
iadd- v-N i-1 i-2 = (mk-uN (((proj-uN-0 v-N i-1) + (proj-uN-0 v-N i-2)) % (2 ^ v-N)))

{- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:112.1-112.36 -}
postulate iand- : ∀ (v-N : N) (v-iN : (uN-fam0 (v-N))) (iN-0 : (uN-fam0 (v-N))) → (uN-fam0 (v-N))

{- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:108.1-108.74 -}
postulate idiv- : ∀ (v-N : N) (v-sx : sx) (v-iN : (uN-fam0 (v-N))) (iN-0 : (uN-fam0 (v-N))) → (Maybe (uN-fam0 (v-N)))

{- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:107.1-107.36 -}
{-# TERMINATING #-}
imul- : (v-N : N) (v-iN : (uN-fam0 (v-N))) (iN-0 : (uN-fam0 (v-N))) → (uN-fam0 (v-N))
imul- v-N i-1 i-2 = (mk-uN (((proj-uN-0 v-N i-1) * (proj-uN-0 v-N i-2)) % (2 ^ v-N)))

{- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:114.1-114.35 -}
postulate ior- : ∀ (v-N : N) (v-iN : (uN-fam0 (v-N))) (iN-0 : (uN-fam0 (v-N))) → (uN-fam0 (v-N))

{- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:109.1-109.74 -}
postulate irem- : ∀ (v-N : N) (v-sx : sx) (v-iN : (uN-fam0 (v-N))) (iN-0 : (uN-fam0 (v-N))) → (Maybe (uN-fam0 (v-N)))

{- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:118.1-118.37 -}
postulate irotl- : ∀ (v-N : N) (v-iN : (uN-fam0 (v-N))) (iN-0 : (uN-fam0 (v-N))) → (uN-fam0 (v-N))

{- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:119.1-119.37 -}
postulate irotr- : ∀ (v-N : N) (v-iN : (uN-fam0 (v-N))) (iN-0 : (uN-fam0 (v-N))) → (uN-fam0 (v-N))

{- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:116.1-116.34 -}
postulate ishl- : ∀ (v-N : N) (v-iN : (uN-fam0 (v-N))) (v-u32 : u32) → (uN-fam0 (v-N))

{- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:117.1-117.74 -}
postulate ishr- : ∀ (v-N : N) (v-sx : sx) (v-iN : (uN-fam0 (v-N))) (v-u32 : u32) → (uN-fam0 (v-N))

{- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:106.1-106.36 -}
{-# TERMINATING #-}
isub- : (v-N : N) (v-iN : (uN-fam0 (v-N))) (iN-0 : (uN-fam0 (v-N))) → (uN-fam0 (v-N))
isub- v-N i-1 i-2 = (mk-uN (coerce {B = ℕ} (((coerce {B = ℕ} ((2 ^ v-N) + (proj-uN-0 v-N i-1))) – (coerce {B = ℕ} (proj-uN-0 v-N i-2))) % (coerce {B = ℕ} (2 ^ v-N)))))

{- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:115.1-115.36 -}
postulate ixor- : ∀ (v-N : N) (v-iN : (uN-fam0 (v-N))) (iN-0 : (uN-fam0 (v-N))) → (uN-fam0 (v-N))

{- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:46.1-47.34 -}
{-# TERMINATING #-}
fun-binop- : (v-numtype : numtype) (v-binop- : (binop- v-numtype)) (v-num- : (num- v-numtype)) (num--0 : (num- v-numtype)) → (List (num- v-numtype))
fun-binop- I32 ADD iN-1 iN-2 = ((iadd- (sizenn (numtype-Inn Inn-I32)) iN-1 iN-2) ∷ [])
fun-binop- I64 ADD iN-1 iN-2 = ((iadd- (sizenn (numtype-Inn Inn-I64)) iN-1 iN-2) ∷ [])
fun-binop- I32 SUB iN-1 iN-2 = ((isub- (sizenn (numtype-Inn Inn-I32)) iN-1 iN-2) ∷ [])
fun-binop- I64 SUB iN-1 iN-2 = ((isub- (sizenn (numtype-Inn Inn-I64)) iN-1 iN-2) ∷ [])
fun-binop- I32 MUL iN-1 iN-2 = ((imul- (sizenn (numtype-Inn Inn-I32)) iN-1 iN-2) ∷ [])
fun-binop- I64 MUL iN-1 iN-2 = ((imul- (sizenn (numtype-Inn Inn-I64)) iN-1 iN-2) ∷ [])
fun-binop- I32 (DIV v-sx) iN-1 iN-2 = (list- (uN-fam0 (32)) (idiv- (sizenn (numtype-Inn Inn-I32)) v-sx iN-1 iN-2))
fun-binop- I64 (DIV v-sx) iN-1 iN-2 = (list- (uN-fam0 (64)) (idiv- (sizenn (numtype-Inn Inn-I64)) v-sx iN-1 iN-2))
fun-binop- I32 (REM v-sx) iN-1 iN-2 = (list- (uN-fam0 (32)) (irem- (sizenn (numtype-Inn Inn-I32)) v-sx iN-1 iN-2))
fun-binop- I64 (REM v-sx) iN-1 iN-2 = (list- (uN-fam0 (64)) (irem- (sizenn (numtype-Inn Inn-I64)) v-sx iN-1 iN-2))
fun-binop- I32 AND iN-1 iN-2 = ((iand- (sizenn (numtype-Inn Inn-I32)) iN-1 iN-2) ∷ [])
fun-binop- I64 AND iN-1 iN-2 = ((iand- (sizenn (numtype-Inn Inn-I64)) iN-1 iN-2) ∷ [])
fun-binop- I32 OR iN-1 iN-2 = ((ior- (sizenn (numtype-Inn Inn-I32)) iN-1 iN-2) ∷ [])
fun-binop- I64 OR iN-1 iN-2 = ((ior- (sizenn (numtype-Inn Inn-I64)) iN-1 iN-2) ∷ [])
fun-binop- I32 XOR iN-1 iN-2 = ((ixor- (sizenn (numtype-Inn Inn-I32)) iN-1 iN-2) ∷ [])
fun-binop- I64 XOR iN-1 iN-2 = ((ixor- (sizenn (numtype-Inn Inn-I64)) iN-1 iN-2) ∷ [])
fun-binop- I32 SHL iN-1 iN-2 = ((ishl- (sizenn (numtype-Inn Inn-I32)) iN-1 (mk-uN (proj-uN-0 (unwrap! (size (valtype-Inn Inn-I32))) iN-2))) ∷ [])
fun-binop- I64 SHL iN-1 iN-2 = ((ishl- (sizenn (numtype-Inn Inn-I64)) iN-1 (mk-uN (proj-uN-0 (unwrap! (size (valtype-Inn Inn-I64))) iN-2))) ∷ [])
fun-binop- I32 (SHR v-sx) iN-1 iN-2 = ((ishr- (sizenn (numtype-Inn Inn-I32)) v-sx iN-1 (mk-uN (proj-uN-0 (unwrap! (size (valtype-Inn Inn-I32))) iN-2))) ∷ [])
fun-binop- I64 (SHR v-sx) iN-1 iN-2 = ((ishr- (sizenn (numtype-Inn Inn-I64)) v-sx iN-1 (mk-uN (proj-uN-0 (unwrap! (size (valtype-Inn Inn-I64))) iN-2))) ∷ [])
fun-binop- I32 ROTL iN-1 iN-2 = ((irotl- (sizenn (numtype-Inn Inn-I32)) iN-1 iN-2) ∷ [])
fun-binop- I64 ROTL iN-1 iN-2 = ((irotl- (sizenn (numtype-Inn Inn-I64)) iN-1 iN-2) ∷ [])
fun-binop- I32 ROTR iN-1 iN-2 = ((irotr- (sizenn (numtype-Inn Inn-I32)) iN-1 iN-2) ∷ [])
fun-binop- I64 ROTR iN-1 iN-2 = ((irotr- (sizenn (numtype-Inn Inn-I64)) iN-1 iN-2) ∷ [])
fun-binop- F32 ADD fN-1 fN-2 = (fadd- (sizenn (numtype-Fnn Fnn-F32)) fN-1 fN-2)
fun-binop- F64 ADD fN-1 fN-2 = (fadd- (sizenn (numtype-Fnn Fnn-F64)) fN-1 fN-2)
fun-binop- F32 SUB fN-1 fN-2 = (fsub- (sizenn (numtype-Fnn Fnn-F32)) fN-1 fN-2)
fun-binop- F64 SUB fN-1 fN-2 = (fsub- (sizenn (numtype-Fnn Fnn-F64)) fN-1 fN-2)
fun-binop- F32 MUL fN-1 fN-2 = (fmul- (sizenn (numtype-Fnn Fnn-F32)) fN-1 fN-2)
fun-binop- F64 MUL fN-1 fN-2 = (fmul- (sizenn (numtype-Fnn Fnn-F64)) fN-1 fN-2)
fun-binop- F32 DIV fN-1 fN-2 = (fdiv- (sizenn (numtype-Fnn Fnn-F32)) fN-1 fN-2)
fun-binop- F64 DIV fN-1 fN-2 = (fdiv- (sizenn (numtype-Fnn Fnn-F64)) fN-1 fN-2)
fun-binop- F32 MIN fN-1 fN-2 = (fmin- (sizenn (numtype-Fnn Fnn-F32)) fN-1 fN-2)
fun-binop- F64 MIN fN-1 fN-2 = (fmin- (sizenn (numtype-Fnn Fnn-F64)) fN-1 fN-2)
fun-binop- F32 MAX fN-1 fN-2 = (fmax- (sizenn (numtype-Fnn Fnn-F32)) fN-1 fN-2)
fun-binop- F64 MAX fN-1 fN-2 = (fmax- (sizenn (numtype-Fnn Fnn-F64)) fN-1 fN-2)
fun-binop- F32 COPYSIGN fN-1 fN-2 = (fcopysign- (sizenn (numtype-Fnn Fnn-F32)) fN-1 fN-2)
fun-binop- F64 COPYSIGN fN-1 fN-2 = (fcopysign- (sizenn (numtype-Fnn Fnn-F64)) fN-1 fN-2)
fun-binop- v-numtype v-binop- v-num- num--0 = []

{- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:123.1-123.27 -}
{-# TERMINATING #-}
ieqz- : (v-N : N) (v-iN : (uN-fam0 (v-N))) → u32
ieqz- v-N i-1 = (mk-uN (bool ((proj-uN-0 v-N i-1) =? 0)))

{- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:48.1-49.32 -}
{-# TERMINATING #-}
fun-testop- : (v-numtype : numtype) (v-testop- : (testop- v-numtype)) (v-num- : (num- v-numtype)) → (uN-fam0 (32))
fun-testop- I32 EQZ v-iN = (ieqz- (sizenn (numtype-Inn Inn-I32)) v-iN)
fun-testop- I64 EQZ v-iN = (ieqz- (sizenn (numtype-Inn Inn-I64)) v-iN)
fun-testop- v-numtype v-testop- v-num- = (Inhabited.default-val (inh-num--fun I32))

{- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:231.1-231.33 -}
postulate feq- : ∀ (v-N : N) (v-fN : (fN-fam0 (v-N))) (fN-0 : (fN-fam0 (v-N))) → u32

{- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:236.1-236.33 -}
postulate fge- : ∀ (v-N : N) (v-fN : (fN-fam0 (v-N))) (fN-0 : (fN-fam0 (v-N))) → u32

{- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:234.1-234.33 -}
postulate fgt- : ∀ (v-N : N) (v-fN : (fN-fam0 (v-N))) (fN-0 : (fN-fam0 (v-N))) → u32

{- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:235.1-235.33 -}
postulate fle- : ∀ (v-N : N) (v-fN : (fN-fam0 (v-N))) (fN-0 : (fN-fam0 (v-N))) → u32

{- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:233.1-233.33 -}
postulate flt- : ∀ (v-N : N) (v-fN : (fN-fam0 (v-N))) (fN-0 : (fN-fam0 (v-N))) → u32

{- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:232.1-232.33 -}
postulate fne- : ∀ (v-N : N) (v-fN : (fN-fam0 (v-N))) (fN-0 : (fN-fam0 (v-N))) → u32

{- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:125.1-125.33 -}
{-# TERMINATING #-}
ieq- : (v-N : N) (v-iN : (uN-fam0 (v-N))) (iN-0 : (uN-fam0 (v-N))) → u32
ieq- v-N i-1 i-2 = (mk-uN (bool (i-1 =? i-2)))

{- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:130.1-130.73 -}
{-# TERMINATING #-}
ige- : (v-N : N) (v-sx : sx) (v-iN : (uN-fam0 (v-N))) (iN-0 : (uN-fam0 (v-N))) → u32
ige- v-N U i-1 i-2 = (mk-uN (bool ((proj-uN-0 v-N i-1) ≥? (proj-uN-0 v-N i-2))))
ige- v-N S i-1 i-2 = (mk-uN (bool ((signed- v-N (proj-uN-0 v-N i-1)) ≥? (signed- v-N (proj-uN-0 v-N i-2)))))
ige- v-N v-sx v-iN iN-0 = default-val

{- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:128.1-128.73 -}
{-# TERMINATING #-}
igt- : (v-N : N) (v-sx : sx) (v-iN : (uN-fam0 (v-N))) (iN-0 : (uN-fam0 (v-N))) → u32
igt- v-N U i-1 i-2 = (mk-uN (bool ((proj-uN-0 v-N i-1) >? (proj-uN-0 v-N i-2))))
igt- v-N S i-1 i-2 = (mk-uN (bool ((signed- v-N (proj-uN-0 v-N i-1)) >? (signed- v-N (proj-uN-0 v-N i-2)))))
igt- v-N v-sx v-iN iN-0 = default-val

{- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:129.1-129.73 -}
{-# TERMINATING #-}
ile- : (v-N : N) (v-sx : sx) (v-iN : (uN-fam0 (v-N))) (iN-0 : (uN-fam0 (v-N))) → u32
ile- v-N U i-1 i-2 = (mk-uN (bool ((proj-uN-0 v-N i-1) ≤? (proj-uN-0 v-N i-2))))
ile- v-N S i-1 i-2 = (mk-uN (bool ((signed- v-N (proj-uN-0 v-N i-1)) ≤? (signed- v-N (proj-uN-0 v-N i-2)))))
ile- v-N v-sx v-iN iN-0 = default-val

{- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:127.1-127.73 -}
{-# TERMINATING #-}
ilt- : (v-N : N) (v-sx : sx) (v-iN : (uN-fam0 (v-N))) (iN-0 : (uN-fam0 (v-N))) → u32
ilt- v-N U i-1 i-2 = (mk-uN (bool ((proj-uN-0 v-N i-1) <? (proj-uN-0 v-N i-2))))
ilt- v-N S i-1 i-2 = (mk-uN (bool ((signed- v-N (proj-uN-0 v-N i-1)) <? (signed- v-N (proj-uN-0 v-N i-2)))))
ilt- v-N v-sx v-iN iN-0 = default-val

{- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:126.1-126.33 -}
{-# TERMINATING #-}
ine- : (v-N : N) (v-iN : (uN-fam0 (v-N))) (iN-0 : (uN-fam0 (v-N))) → u32
ine- v-N i-1 i-2 = (mk-uN (bool (i-1 ≠? i-2)))

{- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:50.1-51.34 -}
{-# TERMINATING #-}
fun-relop- : (v-numtype : numtype) (v-relop- : (relop- v-numtype)) (v-num- : (num- v-numtype)) (num--0 : (num- v-numtype)) → (uN-fam0 (32))
fun-relop- I32 EQ iN-1 iN-2 = (ieq- (sizenn (numtype-Inn Inn-I32)) iN-1 iN-2)
fun-relop- I64 EQ iN-1 iN-2 = (ieq- (sizenn (numtype-Inn Inn-I64)) iN-1 iN-2)
fun-relop- I32 NE iN-1 iN-2 = (ine- (sizenn (numtype-Inn Inn-I32)) iN-1 iN-2)
fun-relop- I64 NE iN-1 iN-2 = (ine- (sizenn (numtype-Inn Inn-I64)) iN-1 iN-2)
fun-relop- I32 (LT v-sx) iN-1 iN-2 = (ilt- (sizenn (numtype-Inn Inn-I32)) v-sx iN-1 iN-2)
fun-relop- I64 (LT v-sx) iN-1 iN-2 = (ilt- (sizenn (numtype-Inn Inn-I64)) v-sx iN-1 iN-2)
fun-relop- I32 (GT v-sx) iN-1 iN-2 = (igt- (sizenn (numtype-Inn Inn-I32)) v-sx iN-1 iN-2)
fun-relop- I64 (GT v-sx) iN-1 iN-2 = (igt- (sizenn (numtype-Inn Inn-I64)) v-sx iN-1 iN-2)
fun-relop- I32 (LE v-sx) iN-1 iN-2 = (ile- (sizenn (numtype-Inn Inn-I32)) v-sx iN-1 iN-2)
fun-relop- I64 (LE v-sx) iN-1 iN-2 = (ile- (sizenn (numtype-Inn Inn-I64)) v-sx iN-1 iN-2)
fun-relop- I32 (GE v-sx) iN-1 iN-2 = (ige- (sizenn (numtype-Inn Inn-I32)) v-sx iN-1 iN-2)
fun-relop- I64 (GE v-sx) iN-1 iN-2 = (ige- (sizenn (numtype-Inn Inn-I64)) v-sx iN-1 iN-2)
fun-relop- F32 EQ fN-1 fN-2 = (feq- (sizenn (numtype-Fnn Fnn-F32)) fN-1 fN-2)
fun-relop- F64 EQ fN-1 fN-2 = (feq- (sizenn (numtype-Fnn Fnn-F64)) fN-1 fN-2)
fun-relop- F32 NE fN-1 fN-2 = (fne- (sizenn (numtype-Fnn Fnn-F32)) fN-1 fN-2)
fun-relop- F64 NE fN-1 fN-2 = (fne- (sizenn (numtype-Fnn Fnn-F64)) fN-1 fN-2)
fun-relop- F32 LT fN-1 fN-2 = (flt- (sizenn (numtype-Fnn Fnn-F32)) fN-1 fN-2)
fun-relop- F64 LT fN-1 fN-2 = (flt- (sizenn (numtype-Fnn Fnn-F64)) fN-1 fN-2)
fun-relop- F32 GT fN-1 fN-2 = (fgt- (sizenn (numtype-Fnn Fnn-F32)) fN-1 fN-2)
fun-relop- F64 GT fN-1 fN-2 = (fgt- (sizenn (numtype-Fnn Fnn-F64)) fN-1 fN-2)
fun-relop- F32 LE fN-1 fN-2 = (fle- (sizenn (numtype-Fnn Fnn-F32)) fN-1 fN-2)
fun-relop- F64 LE fN-1 fN-2 = (fle- (sizenn (numtype-Fnn Fnn-F64)) fN-1 fN-2)
fun-relop- F32 GE fN-1 fN-2 = (fge- (sizenn (numtype-Fnn Fnn-F32)) fN-1 fN-2)
fun-relop- F64 GE fN-1 fN-2 = (fge- (sizenn (numtype-Fnn Fnn-F64)) fN-1 fN-2)
fun-relop- v-numtype v-relop- v-num- num--0 = (Inhabited.default-val (inh-num--fun I32))

{- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:61.1-61.90 -}
postulate convert-- : ∀ (v-M : M) (v-N : N) (v-sx : sx) (v-iN : (uN-fam0 (v-M))) → (fN-fam0 (v-N))

{- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:59.1-59.36 -}
postulate demote-- : ∀ (v-M : M) (v-N : N) (v-fN : (fN-fam0 (v-M))) → (List (fN-fam0 (v-N)))

{- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:60.1-60.37 -}
postulate promote-- : ∀ (v-M : M) (v-N : N) (v-fN : (fN-fam0 (v-M))) → (List (fN-fam0 (v-N)))

{- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:63.1-63.76 -}
postulate reinterpret-- : ∀ (numtype-1 : numtype) (numtype-2 : numtype) (v-num- : (num- numtype-1)) → (num- numtype-2)

{- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:57.1-57.88 -}
postulate trunc-- : ∀ (v-M : M) (v-N : N) (v-sx : sx) (v-fN : (fN-fam0 (v-M))) → (Maybe (uN-fam0 (v-N)))

{- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:58.1-58.93 -}
postulate trunc-sat-- : ∀ (v-M : M) (v-N : N) (v-sx : sx) (v-fN : (fN-fam0 (v-M))) → (Maybe (uN-fam0 (v-N)))

{- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:52.1-53.36 -}
postulate cvtop-- : ∀ (numtype-1 : numtype) (numtype-2 : numtype) (v-cvtop : cvtop) (v-num- : (num- numtype-1)) → (List (num- numtype-2))

{- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:62.1-62.87 -}
postulate narrow-- : ∀ (v-M : M) (v-N : N) (v-sx : sx) (v-iN : (uN-fam0 (v-M))) → (uN-fam0 (v-N))

{- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:76.1-76.102 -}
postulate ibits- : ∀ (v-N : N) (v-iN : (uN-fam0 (v-N))) → (List bit)

{- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:77.1-77.102 -}
postulate fbits- : ∀ (v-N : N) (v-fN : (fN-fam0 (v-N))) → (List bit)

{- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:78.1-78.103 -}
postulate ibytes- : ∀ (v-N : N) (v-iN : (uN-fam0 (v-N))) → (List byte)

{- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:79.1-79.103 -}
postulate fbytes- : ∀ (v-N : N) (v-fN : (fN-fam0 (v-N))) → (List byte)

{- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:80.1-80.103 -}
postulate nbytes- : ∀ (v-numtype : numtype) (v-num- : (num- v-numtype)) → (List byte)

{- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:81.1-81.103 -}
postulate vbytes- : ∀ (v-vectype : vectype) (v-vec- : (uN-fam0 ((unwrap! (size (valtype-vectype v-vectype)))))) → (List byte)

{- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:83.1-83.85 -}
postulate inv-ibits- : ∀ (v-N : N) (var-0-lst : (List bit)) → (uN-fam0 (v-N))

{- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:84.1-84.85 -}
postulate inv-fbits- : ∀ (v-N : N) (var-0-lst : (List bit)) → (fN-fam0 (v-N))

{- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:85.1-85.86 -}
postulate inv-ibytes- : ∀ (v-N : N) (var-0-lst : (List byte)) → (uN-fam0 (v-N))

{- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:86.1-86.86 -}
postulate inv-fbytes- : ∀ (v-N : N) (var-0-lst : (List byte)) → (fN-fam0 (v-N))

{- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:87.1-87.84 -}
postulate inv-nbytes- : ∀ (v-numtype : numtype) (var-0-lst : (List byte)) → (num- v-numtype)

{- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:88.1-88.84 -}
postulate inv-vbytes- : ∀ (v-vectype : vectype) (var-0-lst : (List byte)) → (uN-fam0 ((unwrap! (size (valtype-vectype v-vectype)))))

{- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:110.1-110.29 -}
postulate inot- : ∀ (v-N : N) (v-iN : (uN-fam0 (v-N))) → (uN-fam0 (v-N))

{- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:111.1-111.29 -}
postulate irev- : ∀ (v-N : N) (v-iN : (uN-fam0 (v-N))) → (uN-fam0 (v-N))

{- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:113.1-113.39 -}
postulate iandnot- : ∀ (v-N : N) (v-iN : (uN-fam0 (v-N))) (iN-0 : (uN-fam0 (v-N))) → (uN-fam0 (v-N))

{- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:124.1-124.27 -}
{-# TERMINATING #-}
inez- : (v-N : N) (v-iN : (uN-fam0 (v-N))) → u32
inez- v-N i-1 = (mk-uN (bool ((proj-uN-0 v-N i-1) ≠? 0)))

{- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:131.1-131.49 -}
postulate ibitselect- : ∀ (v-N : N) (v-iN : (uN-fam0 (v-N))) (iN-0 : (uN-fam0 (v-N))) (iN-1 : (uN-fam0 (v-N))) → (uN-fam0 (v-N))

{- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:133.1-133.29 -}
{-# TERMINATING #-}
ineg- : (v-N : N) (v-iN : (uN-fam0 (v-N))) → (uN-fam0 (v-N))
ineg- v-N i-1 = (mk-uN (coerce {B = ℕ} (((coerce {B = ℕ} (2 ^ v-N)) – (coerce {B = ℕ} (proj-uN-0 v-N i-1))) % (coerce {B = ℕ} (2 ^ v-N)))))

{- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:132.1-132.29 -}
{-# TERMINATING #-}
iabs- : (v-N : N) (v-iN : (uN-fam0 (v-N))) → (uN-fam0 (v-N))
iabs- v-N i-1 = (if ((signed- v-N (proj-uN-0 v-N i-1)) ≥? (coerce {B = ℕ} 0)) then i-1 else (ineg- v-N i-1))

{- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:134.1-134.81 -}
postulate imin- : ∀ (v-N : N) (v-sx : sx) (v-iN : (uN-fam0 (v-N))) (iN-0 : (uN-fam0 (v-N))) → (uN-fam0 (v-N))

{- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:135.1-135.81 -}
postulate imax- : ∀ (v-N : N) (v-sx : sx) (v-iN : (uN-fam0 (v-N))) (iN-0 : (uN-fam0 (v-N))) → (uN-fam0 (v-N))

{- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:136.1-136.86 -}
{-# TERMINATING #-}
iadd-sat- : (v-N : N) (v-sx : sx) (v-iN : (uN-fam0 (v-N))) (iN-0 : (uN-fam0 (v-N))) → (uN-fam0 (v-N))
iadd-sat- v-N U i-1 i-2 = (mk-uN (sat-u- v-N (coerce {B = ℕ} ((proj-uN-0 v-N i-1) + (proj-uN-0 v-N i-2)))))
iadd-sat- v-N S i-1 i-2 = (mk-uN (inv-signed- v-N (sat-s- v-N ((signed- v-N (proj-uN-0 v-N i-1)) + (signed- v-N (proj-uN-0 v-N i-2))))))
iadd-sat- v-N v-sx v-iN iN-0 = (Inhabited.default-val (inh-iN-fun v-N))

{- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:137.1-137.86 -}
{-# TERMINATING #-}
isub-sat- : (v-N : N) (v-sx : sx) (v-iN : (uN-fam0 (v-N))) (iN-0 : (uN-fam0 (v-N))) → (uN-fam0 (v-N))
isub-sat- v-N U i-1 i-2 = (mk-uN (sat-u- v-N ((coerce {B = ℕ} (proj-uN-0 v-N i-1)) – (coerce {B = ℕ} (proj-uN-0 v-N i-2)))))
isub-sat- v-N S i-1 i-2 = (mk-uN (inv-signed- v-N (sat-s- v-N ((signed- v-N (proj-uN-0 v-N i-1)) – (signed- v-N (proj-uN-0 v-N i-2))))))
isub-sat- v-N v-sx v-iN iN-0 = (Inhabited.default-val (inh-iN-fun v-N))

{- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:138.1-138.82 -}
postulate iavgr- : ∀ (v-N : N) (v-sx : sx) (v-iN : (uN-fam0 (v-N))) (iN-0 : (uN-fam0 (v-N))) → (uN-fam0 (v-N))

{- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:139.1-139.90 -}
postulate iq15mulr-sat- : ∀ (v-N : N) (v-sx : sx) (v-iN : (uN-fam0 (v-N))) (iN-0 : (uN-fam0 (v-N))) → (uN-fam0 (v-N))

{- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:221.1-221.38 -}
postulate fpmin- : ∀ (v-N : N) (v-fN : (fN-fam0 (v-N))) (fN-0 : (fN-fam0 (v-N))) → (List (fN-fam0 (v-N)))

{- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:222.1-222.38 -}
postulate fpmax- : ∀ (v-N : N) (v-fN : (fN-fam0 (v-N))) (fN-0 : (fN-fam0 (v-N))) → (List (fN-fam0 (v-N)))

{- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:323.1-324.27 -}
{-# TERMINATING #-}
packnum- : (v-lanetype : lanetype) (v-num- : (num- (unpack v-lanetype))) → (lane- v-lanetype)
packnum- lanetype-I32 c = c
packnum- lanetype-I64 c = c
packnum- lanetype-F32 c = c
packnum- lanetype-F64 c = c
packnum- lanetype-I8 c = (wrap-- (unwrap! (size (valtype-numtype (unpack (lanetype-packtype I8))))) (psize I8) c)
packnum- lanetype-I16 c = (wrap-- (unwrap! (size (valtype-numtype (unpack (lanetype-packtype I16))))) (psize I16) c)
packnum- v-lanetype v-num- = (Inhabited.default-val (inh-lane--fun v-lanetype))

{- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:328.1-329.29 -}
{-# TERMINATING #-}
unpacknum- : (v-lanetype : lanetype) (v-lane- : (lane- v-lanetype)) → (num- (unpack v-lanetype))
unpacknum- lanetype-I32 c = c
unpacknum- lanetype-I64 c = c
unpacknum- lanetype-F32 c = c
unpacknum- lanetype-F64 c = c
unpacknum- lanetype-I8 c = (extend-- (psize I8) (unwrap! (size (valtype-numtype (unpack (lanetype-packtype I8))))) U c)
unpacknum- lanetype-I16 c = (extend-- (psize I16) (unwrap! (size (valtype-numtype (unpack (lanetype-packtype I16))))) U c)
unpacknum- v-lanetype v-lane- = (Inhabited.default-val (inh-num--fun (unpack v-lanetype)))

{- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:336.1-336.84 -}
postulate lanes- : ∀ (v-shape : shape) (v-vec- : (uN-fam0 (128))) → (List (lane- (fun-lanetype v-shape)))

{- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:339.1-340.36 -}
postulate inv-lanes- : ∀ (v-shape : shape) (var-0-lst : (List (lane- (fun-lanetype v-shape)))) → (uN-fam0 (128))

{- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:343.1-343.28 -}
{-# TERMINATING #-}
zeroop : (v-vcvtop : vcvtop) → (Maybe zero')
zeroop (vcvtop-EXTEND v-half v-sx) = nothing
zeroop (vcvtop-CONVERT half-opt v-sx) = nothing
zeroop (vcvtop-TRUNC-SAT v-sx zero-opt) = zero-opt
zeroop (vcvtop-DEMOTE v-zero) = (just v-zero)
zeroop PROMOTELOW = nothing
zeroop v-vcvtop = nothing

{- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:350.1-350.28 -}
{-# TERMINATING #-}
halfop : (v-vcvtop : vcvtop) → (Maybe half)
halfop (vcvtop-EXTEND v-half v-sx) = (just v-half)
halfop (vcvtop-CONVERT half-opt v-sx) = half-opt
halfop (vcvtop-TRUNC-SAT v-sx zero-opt) = nothing
halfop (vcvtop-DEMOTE v-zero) = nothing
halfop PROMOTELOW = (just LOW)
halfop v-vcvtop = nothing

{- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:357.1-357.32 -}
{-# TERMINATING #-}
fun-half : (v-half : half) (nat : ℕ) (nat-0 : ℕ) → ℕ
fun-half LOW i j = i
fun-half HIGH i j = j
fun-half v-half nat nat-0 = default-val

{- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:362.1-363.28 -}
{-# TERMINATING #-}
vvunop- : (v-vectype : vectype) (v-vvunop : vvunop) (v-vec- : (uN-fam0 ((unwrap! (size (valtype-vectype v-vectype)))))) → (uN-fam0 ((unwrap! (size (valtype-vectype v-vectype)))))
vvunop- V128 NOT v128 = (inot- (unwrap! (size valtype-V128)) v128)
vvunop- v-vectype v-vvunop v-vec- = (Inhabited.default-val (inh-vec--fun v-vectype))

{- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:364.1-365.31 -}
{-# TERMINATING #-}
vvbinop- : (v-vectype : vectype) (v-vvbinop : vvbinop) (v-vec- : (uN-fam0 ((unwrap! (size (valtype-vectype v-vectype)))))) (vec--0 : (uN-fam0 ((unwrap! (size (valtype-vectype v-vectype)))))) → (uN-fam0 ((unwrap! (size (valtype-vectype v-vectype)))))
vvbinop- V128 vvbinop-AND v128-1 v128-2 = (iand- (unwrap! (size valtype-V128)) v128-1 v128-2)
vvbinop- V128 ANDNOT v128-1 v128-2 = (iandnot- (unwrap! (size valtype-V128)) v128-1 v128-2)
vvbinop- V128 vvbinop-OR v128-1 v128-2 = (ior- (unwrap! (size valtype-V128)) v128-1 v128-2)
vvbinop- V128 vvbinop-XOR v128-1 v128-2 = (ixor- (unwrap! (size valtype-V128)) v128-1 v128-2)
vvbinop- v-vectype v-vvbinop v-vec- vec--0 = (Inhabited.default-val (inh-vec--fun v-vectype))

{- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:366.1-367.34 -}
{-# TERMINATING #-}
vvternop- : (v-vectype : vectype) (v-vvternop : vvternop) (v-vec- : (uN-fam0 ((unwrap! (size (valtype-vectype v-vectype)))))) (vec--0 : (uN-fam0 ((unwrap! (size (valtype-vectype v-vectype)))))) (vec--1 : (uN-fam0 ((unwrap! (size (valtype-vectype v-vectype)))))) → (uN-fam0 ((unwrap! (size (valtype-vectype v-vectype)))))
vvternop- V128 BITSELECT v128-1 v128-2 v128-3 = (ibitselect- (unwrap! (size valtype-V128)) v128-1 v128-2 v128-3)
vvternop- v-vectype v-vvternop v-vec- vec--0 vec--1 = (Inhabited.default-val (inh-vec--fun v-vectype))

{- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:377.1-378.32 -}
{-# TERMINATING #-}
fun-vunop- : (v-shape : shape) (v-vunop- : (vunop- v-shape)) (v-vec- : (uN-fam0 (128))) → (List (uN-fam0 (128)))
fun-vunop- (X lanetype-I32 (mk-dim v-M)) vunop--ABS v128-1 = let lane-1-lst = (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) v128-1) in let v128 = (inv-lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) (map (λ (lane-1-2 : (uN-fam0 (32))) → (iabs- (lsizenn (lanetype-Jnn Jnn-I32)) lane-1-2)) lane-1-lst)) in (v128 ∷ [])
fun-vunop- (X lanetype-I64 (mk-dim v-M)) vunop--ABS v128-1 = let lane-1-lst = (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) v128-1) in let v128 = (inv-lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) (map (λ (lane-1-4 : (uN-fam0 (64))) → (iabs- (lsizenn (lanetype-Jnn Jnn-I64)) lane-1-4)) lane-1-lst)) in (v128 ∷ [])
fun-vunop- (X lanetype-I8 (mk-dim v-M)) vunop--ABS v128-1 = let lane-1-lst = (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) v128-1) in let v128 = (inv-lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) (map (λ (lane-1-6 : (uN-fam0 (8))) → (iabs- (lsizenn (lanetype-Jnn Jnn-I8)) lane-1-6)) lane-1-lst)) in (v128 ∷ [])
fun-vunop- (X lanetype-I16 (mk-dim v-M)) vunop--ABS v128-1 = let lane-1-lst = (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) v128-1) in let v128 = (inv-lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) (map (λ (lane-1-8 : (uN-fam0 (16))) → (iabs- (lsizenn (lanetype-Jnn Jnn-I16)) lane-1-8)) lane-1-lst)) in (v128 ∷ [])
fun-vunop- (X lanetype-I32 (mk-dim v-M)) vunop--NEG v128-1 = let lane-1-lst = (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) v128-1) in let v128 = (inv-lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) (map (λ (lane-1-10 : (uN-fam0 (32))) → (ineg- (lsizenn (lanetype-Jnn Jnn-I32)) lane-1-10)) lane-1-lst)) in (v128 ∷ [])
fun-vunop- (X lanetype-I64 (mk-dim v-M)) vunop--NEG v128-1 = let lane-1-lst = (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) v128-1) in let v128 = (inv-lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) (map (λ (lane-1-12 : (uN-fam0 (64))) → (ineg- (lsizenn (lanetype-Jnn Jnn-I64)) lane-1-12)) lane-1-lst)) in (v128 ∷ [])
fun-vunop- (X lanetype-I8 (mk-dim v-M)) vunop--NEG v128-1 = let lane-1-lst = (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) v128-1) in let v128 = (inv-lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) (map (λ (lane-1-14 : (uN-fam0 (8))) → (ineg- (lsizenn (lanetype-Jnn Jnn-I8)) lane-1-14)) lane-1-lst)) in (v128 ∷ [])
fun-vunop- (X lanetype-I16 (mk-dim v-M)) vunop--NEG v128-1 = let lane-1-lst = (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) v128-1) in let v128 = (inv-lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) (map (λ (lane-1-16 : (uN-fam0 (16))) → (ineg- (lsizenn (lanetype-Jnn Jnn-I16)) lane-1-16)) lane-1-lst)) in (v128 ∷ [])
fun-vunop- (X lanetype-I32 (mk-dim v-M)) vunop--POPCNT v128-1 = let lane-1-lst = (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) v128-1) in let v128 = (inv-lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) (map (λ (lane-1-18 : (uN-fam0 (32))) → (ipopcnt- (lsizenn (lanetype-Jnn Jnn-I32)) lane-1-18)) lane-1-lst)) in (v128 ∷ [])
fun-vunop- (X lanetype-I64 (mk-dim v-M)) vunop--POPCNT v128-1 = let lane-1-lst = (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) v128-1) in let v128 = (inv-lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) (map (λ (lane-1-20 : (uN-fam0 (64))) → (ipopcnt- (lsizenn (lanetype-Jnn Jnn-I64)) lane-1-20)) lane-1-lst)) in (v128 ∷ [])
fun-vunop- (X lanetype-I8 (mk-dim v-M)) vunop--POPCNT v128-1 = let lane-1-lst = (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) v128-1) in let v128 = (inv-lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) (map (λ (lane-1-22 : (uN-fam0 (8))) → (ipopcnt- (lsizenn (lanetype-Jnn Jnn-I8)) lane-1-22)) lane-1-lst)) in (v128 ∷ [])
fun-vunop- (X lanetype-I16 (mk-dim v-M)) vunop--POPCNT v128-1 = let lane-1-lst = (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) v128-1) in let v128 = (inv-lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) (map (λ (lane-1-24 : (uN-fam0 (16))) → (ipopcnt- (lsizenn (lanetype-Jnn Jnn-I16)) lane-1-24)) lane-1-lst)) in (v128 ∷ [])
fun-vunop- (X lanetype-F32 (mk-dim v-M)) vunop--ABS v128-1 = let lane-1-lst = (lanes- (X (lanetype-Fnn Fnn-F32) (mk-dim v-M)) v128-1) in let lane-lst-lst = (setproduct- (fN-fam0 (32)) (map (λ (lane-1-26 : (fN-fam0 (32))) → (fabs- (sizenn (numtype-Fnn Fnn-F32)) lane-1-26)) lane-1-lst)) in let v128-lst = (map (λ (lane-lst-2 : (List (fN-fam0 (32)))) → (inv-lanes- (X (lanetype-Fnn Fnn-F32) (mk-dim v-M)) lane-lst-2)) lane-lst-lst) in v128-lst
fun-vunop- (X lanetype-F64 (mk-dim v-M)) vunop--ABS v128-1 = let lane-1-lst = (lanes- (X (lanetype-Fnn Fnn-F64) (mk-dim v-M)) v128-1) in let lane-lst-lst = (setproduct- (fN-fam0 (64)) (map (λ (lane-1-28 : (fN-fam0 (64))) → (fabs- (sizenn (numtype-Fnn Fnn-F64)) lane-1-28)) lane-1-lst)) in let v128-lst = (map (λ (lane-lst-4 : (List (fN-fam0 (64)))) → (inv-lanes- (X (lanetype-Fnn Fnn-F64) (mk-dim v-M)) lane-lst-4)) lane-lst-lst) in v128-lst
fun-vunop- (X lanetype-F32 (mk-dim v-M)) vunop--NEG v128-1 = let lane-1-lst = (lanes- (X (lanetype-Fnn Fnn-F32) (mk-dim v-M)) v128-1) in let lane-lst-lst = (setproduct- (fN-fam0 (32)) (map (λ (lane-1-30 : (fN-fam0 (32))) → (fneg- (sizenn (numtype-Fnn Fnn-F32)) lane-1-30)) lane-1-lst)) in let v128-lst = (map (λ (lane-lst-6 : (List (fN-fam0 (32)))) → (inv-lanes- (X (lanetype-Fnn Fnn-F32) (mk-dim v-M)) lane-lst-6)) lane-lst-lst) in v128-lst
fun-vunop- (X lanetype-F64 (mk-dim v-M)) vunop--NEG v128-1 = let lane-1-lst = (lanes- (X (lanetype-Fnn Fnn-F64) (mk-dim v-M)) v128-1) in let lane-lst-lst = (setproduct- (fN-fam0 (64)) (map (λ (lane-1-32 : (fN-fam0 (64))) → (fneg- (sizenn (numtype-Fnn Fnn-F64)) lane-1-32)) lane-1-lst)) in let v128-lst = (map (λ (lane-lst-8 : (List (fN-fam0 (64)))) → (inv-lanes- (X (lanetype-Fnn Fnn-F64) (mk-dim v-M)) lane-lst-8)) lane-lst-lst) in v128-lst
fun-vunop- (X lanetype-F32 (mk-dim v-M)) vunop--SQRT v128-1 = let lane-1-lst = (lanes- (X (lanetype-Fnn Fnn-F32) (mk-dim v-M)) v128-1) in let lane-lst-lst = (setproduct- (fN-fam0 (32)) (map (λ (lane-1-34 : (fN-fam0 (32))) → (fsqrt- (sizenn (numtype-Fnn Fnn-F32)) lane-1-34)) lane-1-lst)) in let v128-lst = (map (λ (lane-lst-10 : (List (fN-fam0 (32)))) → (inv-lanes- (X (lanetype-Fnn Fnn-F32) (mk-dim v-M)) lane-lst-10)) lane-lst-lst) in v128-lst
fun-vunop- (X lanetype-F64 (mk-dim v-M)) vunop--SQRT v128-1 = let lane-1-lst = (lanes- (X (lanetype-Fnn Fnn-F64) (mk-dim v-M)) v128-1) in let lane-lst-lst = (setproduct- (fN-fam0 (64)) (map (λ (lane-1-36 : (fN-fam0 (64))) → (fsqrt- (sizenn (numtype-Fnn Fnn-F64)) lane-1-36)) lane-1-lst)) in let v128-lst = (map (λ (lane-lst-12 : (List (fN-fam0 (64)))) → (inv-lanes- (X (lanetype-Fnn Fnn-F64) (mk-dim v-M)) lane-lst-12)) lane-lst-lst) in v128-lst
fun-vunop- (X lanetype-F32 (mk-dim v-M)) vunop--CEIL v128-1 = let lane-1-lst = (lanes- (X (lanetype-Fnn Fnn-F32) (mk-dim v-M)) v128-1) in let lane-lst-lst = (setproduct- (fN-fam0 (32)) (map (λ (lane-1-38 : (fN-fam0 (32))) → (fceil- (sizenn (numtype-Fnn Fnn-F32)) lane-1-38)) lane-1-lst)) in let v128-lst = (map (λ (lane-lst-14 : (List (fN-fam0 (32)))) → (inv-lanes- (X (lanetype-Fnn Fnn-F32) (mk-dim v-M)) lane-lst-14)) lane-lst-lst) in v128-lst
fun-vunop- (X lanetype-F64 (mk-dim v-M)) vunop--CEIL v128-1 = let lane-1-lst = (lanes- (X (lanetype-Fnn Fnn-F64) (mk-dim v-M)) v128-1) in let lane-lst-lst = (setproduct- (fN-fam0 (64)) (map (λ (lane-1-40 : (fN-fam0 (64))) → (fceil- (sizenn (numtype-Fnn Fnn-F64)) lane-1-40)) lane-1-lst)) in let v128-lst = (map (λ (lane-lst-16 : (List (fN-fam0 (64)))) → (inv-lanes- (X (lanetype-Fnn Fnn-F64) (mk-dim v-M)) lane-lst-16)) lane-lst-lst) in v128-lst
fun-vunop- (X lanetype-F32 (mk-dim v-M)) vunop--FLOOR v128-1 = let lane-1-lst = (lanes- (X (lanetype-Fnn Fnn-F32) (mk-dim v-M)) v128-1) in let lane-lst-lst = (setproduct- (fN-fam0 (32)) (map (λ (lane-1-42 : (fN-fam0 (32))) → (ffloor- (sizenn (numtype-Fnn Fnn-F32)) lane-1-42)) lane-1-lst)) in let v128-lst = (map (λ (lane-lst-18 : (List (fN-fam0 (32)))) → (inv-lanes- (X (lanetype-Fnn Fnn-F32) (mk-dim v-M)) lane-lst-18)) lane-lst-lst) in v128-lst
fun-vunop- (X lanetype-F64 (mk-dim v-M)) vunop--FLOOR v128-1 = let lane-1-lst = (lanes- (X (lanetype-Fnn Fnn-F64) (mk-dim v-M)) v128-1) in let lane-lst-lst = (setproduct- (fN-fam0 (64)) (map (λ (lane-1-44 : (fN-fam0 (64))) → (ffloor- (sizenn (numtype-Fnn Fnn-F64)) lane-1-44)) lane-1-lst)) in let v128-lst = (map (λ (lane-lst-20 : (List (fN-fam0 (64)))) → (inv-lanes- (X (lanetype-Fnn Fnn-F64) (mk-dim v-M)) lane-lst-20)) lane-lst-lst) in v128-lst
fun-vunop- (X lanetype-F32 (mk-dim v-M)) vunop--TRUNC v128-1 = let lane-1-lst = (lanes- (X (lanetype-Fnn Fnn-F32) (mk-dim v-M)) v128-1) in let lane-lst-lst = (setproduct- (fN-fam0 (32)) (map (λ (lane-1-46 : (fN-fam0 (32))) → (ftrunc- (sizenn (numtype-Fnn Fnn-F32)) lane-1-46)) lane-1-lst)) in let v128-lst = (map (λ (lane-lst-22 : (List (fN-fam0 (32)))) → (inv-lanes- (X (lanetype-Fnn Fnn-F32) (mk-dim v-M)) lane-lst-22)) lane-lst-lst) in v128-lst
fun-vunop- (X lanetype-F64 (mk-dim v-M)) vunop--TRUNC v128-1 = let lane-1-lst = (lanes- (X (lanetype-Fnn Fnn-F64) (mk-dim v-M)) v128-1) in let lane-lst-lst = (setproduct- (fN-fam0 (64)) (map (λ (lane-1-48 : (fN-fam0 (64))) → (ftrunc- (sizenn (numtype-Fnn Fnn-F64)) lane-1-48)) lane-1-lst)) in let v128-lst = (map (λ (lane-lst-24 : (List (fN-fam0 (64)))) → (inv-lanes- (X (lanetype-Fnn Fnn-F64) (mk-dim v-M)) lane-lst-24)) lane-lst-lst) in v128-lst
fun-vunop- (X lanetype-F32 (mk-dim v-M)) vunop--NEAREST v128-1 = let lane-1-lst = (lanes- (X (lanetype-Fnn Fnn-F32) (mk-dim v-M)) v128-1) in let lane-lst-lst = (setproduct- (fN-fam0 (32)) (map (λ (lane-1-50 : (fN-fam0 (32))) → (fnearest- (sizenn (numtype-Fnn Fnn-F32)) lane-1-50)) lane-1-lst)) in let v128-lst = (map (λ (lane-lst-26 : (List (fN-fam0 (32)))) → (inv-lanes- (X (lanetype-Fnn Fnn-F32) (mk-dim v-M)) lane-lst-26)) lane-lst-lst) in v128-lst
fun-vunop- (X lanetype-F64 (mk-dim v-M)) vunop--NEAREST v128-1 = let lane-1-lst = (lanes- (X (lanetype-Fnn Fnn-F64) (mk-dim v-M)) v128-1) in let lane-lst-lst = (setproduct- (fN-fam0 (64)) (map (λ (lane-1-52 : (fN-fam0 (64))) → (fnearest- (sizenn (numtype-Fnn Fnn-F64)) lane-1-52)) lane-1-lst)) in let v128-lst = (map (λ (lane-lst-28 : (List (fN-fam0 (64)))) → (inv-lanes- (X (lanetype-Fnn Fnn-F64) (mk-dim v-M)) lane-lst-28)) lane-lst-lst) in v128-lst
fun-vunop- v-shape v-vunop- v-vec- = []

{- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:379.1-380.34 -}
{-# TERMINATING #-}
fun-vbinop- : (v-shape : shape) (v-vbinop- : (vbinop- v-shape)) (v-vec- : (uN-fam0 (128))) (vec--0 : (uN-fam0 (128))) → (List (uN-fam0 (128)))
fun-vbinop- (X lanetype-I32 (mk-dim v-M)) vbinop--ADD v128-1 v128-2 = let lane-1-lst = (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) v128-1) in let lane-2-lst = (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) v128-2) in let v128 = (inv-lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) (zipWith (λ (lane-1-54 : (uN-fam0 (32))) (lane-2-2 : (uN-fam0 (32))) → (iadd- (lsizenn (lanetype-Jnn Jnn-I32)) lane-1-54 lane-2-2)) lane-1-lst lane-2-lst)) in (v128 ∷ [])
fun-vbinop- (X lanetype-I64 (mk-dim v-M)) vbinop--ADD v128-1 v128-2 = let lane-1-lst = (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) v128-1) in let lane-2-lst = (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) v128-2) in let v128 = (inv-lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) (zipWith (λ (lane-1-56 : (uN-fam0 (64))) (lane-2-4 : (uN-fam0 (64))) → (iadd- (lsizenn (lanetype-Jnn Jnn-I64)) lane-1-56 lane-2-4)) lane-1-lst lane-2-lst)) in (v128 ∷ [])
fun-vbinop- (X lanetype-I8 (mk-dim v-M)) vbinop--ADD v128-1 v128-2 = let lane-1-lst = (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) v128-1) in let lane-2-lst = (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) v128-2) in let v128 = (inv-lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) (zipWith (λ (lane-1-58 : (uN-fam0 (8))) (lane-2-6 : (uN-fam0 (8))) → (iadd- (lsizenn (lanetype-Jnn Jnn-I8)) lane-1-58 lane-2-6)) lane-1-lst lane-2-lst)) in (v128 ∷ [])
fun-vbinop- (X lanetype-I16 (mk-dim v-M)) vbinop--ADD v128-1 v128-2 = let lane-1-lst = (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) v128-1) in let lane-2-lst = (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) v128-2) in let v128 = (inv-lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) (zipWith (λ (lane-1-60 : (uN-fam0 (16))) (lane-2-8 : (uN-fam0 (16))) → (iadd- (lsizenn (lanetype-Jnn Jnn-I16)) lane-1-60 lane-2-8)) lane-1-lst lane-2-lst)) in (v128 ∷ [])
fun-vbinop- (X lanetype-I32 (mk-dim v-M)) vbinop--SUB v128-1 v128-2 = let lane-1-lst = (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) v128-1) in let lane-2-lst = (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) v128-2) in let v128 = (inv-lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) (zipWith (λ (lane-1-62 : (uN-fam0 (32))) (lane-2-10 : (uN-fam0 (32))) → (isub- (lsizenn (lanetype-Jnn Jnn-I32)) lane-1-62 lane-2-10)) lane-1-lst lane-2-lst)) in (v128 ∷ [])
fun-vbinop- (X lanetype-I64 (mk-dim v-M)) vbinop--SUB v128-1 v128-2 = let lane-1-lst = (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) v128-1) in let lane-2-lst = (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) v128-2) in let v128 = (inv-lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) (zipWith (λ (lane-1-64 : (uN-fam0 (64))) (lane-2-12 : (uN-fam0 (64))) → (isub- (lsizenn (lanetype-Jnn Jnn-I64)) lane-1-64 lane-2-12)) lane-1-lst lane-2-lst)) in (v128 ∷ [])
fun-vbinop- (X lanetype-I8 (mk-dim v-M)) vbinop--SUB v128-1 v128-2 = let lane-1-lst = (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) v128-1) in let lane-2-lst = (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) v128-2) in let v128 = (inv-lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) (zipWith (λ (lane-1-66 : (uN-fam0 (8))) (lane-2-14 : (uN-fam0 (8))) → (isub- (lsizenn (lanetype-Jnn Jnn-I8)) lane-1-66 lane-2-14)) lane-1-lst lane-2-lst)) in (v128 ∷ [])
fun-vbinop- (X lanetype-I16 (mk-dim v-M)) vbinop--SUB v128-1 v128-2 = let lane-1-lst = (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) v128-1) in let lane-2-lst = (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) v128-2) in let v128 = (inv-lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) (zipWith (λ (lane-1-68 : (uN-fam0 (16))) (lane-2-16 : (uN-fam0 (16))) → (isub- (lsizenn (lanetype-Jnn Jnn-I16)) lane-1-68 lane-2-16)) lane-1-lst lane-2-lst)) in (v128 ∷ [])
fun-vbinop- (X lanetype-I32 (mk-dim v-M)) (vbinop--MIN v-sx) v128-1 v128-2 = let lane-1-lst = (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) v128-1) in let lane-2-lst = (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) v128-2) in let v128 = (inv-lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) (zipWith (λ (lane-1-70 : (uN-fam0 (32))) (lane-2-18 : (uN-fam0 (32))) → (imin- (lsizenn (lanetype-Jnn Jnn-I32)) v-sx lane-1-70 lane-2-18)) lane-1-lst lane-2-lst)) in (v128 ∷ [])
fun-vbinop- (X lanetype-I64 (mk-dim v-M)) (vbinop--MIN v-sx) v128-1 v128-2 = let lane-1-lst = (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) v128-1) in let lane-2-lst = (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) v128-2) in let v128 = (inv-lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) (zipWith (λ (lane-1-72 : (uN-fam0 (64))) (lane-2-20 : (uN-fam0 (64))) → (imin- (lsizenn (lanetype-Jnn Jnn-I64)) v-sx lane-1-72 lane-2-20)) lane-1-lst lane-2-lst)) in (v128 ∷ [])
fun-vbinop- (X lanetype-I8 (mk-dim v-M)) (vbinop--MIN v-sx) v128-1 v128-2 = let lane-1-lst = (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) v128-1) in let lane-2-lst = (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) v128-2) in let v128 = (inv-lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) (zipWith (λ (lane-1-74 : (uN-fam0 (8))) (lane-2-22 : (uN-fam0 (8))) → (imin- (lsizenn (lanetype-Jnn Jnn-I8)) v-sx lane-1-74 lane-2-22)) lane-1-lst lane-2-lst)) in (v128 ∷ [])
fun-vbinop- (X lanetype-I16 (mk-dim v-M)) (vbinop--MIN v-sx) v128-1 v128-2 = let lane-1-lst = (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) v128-1) in let lane-2-lst = (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) v128-2) in let v128 = (inv-lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) (zipWith (λ (lane-1-76 : (uN-fam0 (16))) (lane-2-24 : (uN-fam0 (16))) → (imin- (lsizenn (lanetype-Jnn Jnn-I16)) v-sx lane-1-76 lane-2-24)) lane-1-lst lane-2-lst)) in (v128 ∷ [])
fun-vbinop- (X lanetype-I32 (mk-dim v-M)) (vbinop--MAX v-sx) v128-1 v128-2 = let lane-1-lst = (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) v128-1) in let lane-2-lst = (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) v128-2) in let v128 = (inv-lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) (zipWith (λ (lane-1-78 : (uN-fam0 (32))) (lane-2-26 : (uN-fam0 (32))) → (imax- (lsizenn (lanetype-Jnn Jnn-I32)) v-sx lane-1-78 lane-2-26)) lane-1-lst lane-2-lst)) in (v128 ∷ [])
fun-vbinop- (X lanetype-I64 (mk-dim v-M)) (vbinop--MAX v-sx) v128-1 v128-2 = let lane-1-lst = (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) v128-1) in let lane-2-lst = (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) v128-2) in let v128 = (inv-lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) (zipWith (λ (lane-1-80 : (uN-fam0 (64))) (lane-2-28 : (uN-fam0 (64))) → (imax- (lsizenn (lanetype-Jnn Jnn-I64)) v-sx lane-1-80 lane-2-28)) lane-1-lst lane-2-lst)) in (v128 ∷ [])
fun-vbinop- (X lanetype-I8 (mk-dim v-M)) (vbinop--MAX v-sx) v128-1 v128-2 = let lane-1-lst = (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) v128-1) in let lane-2-lst = (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) v128-2) in let v128 = (inv-lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) (zipWith (λ (lane-1-82 : (uN-fam0 (8))) (lane-2-30 : (uN-fam0 (8))) → (imax- (lsizenn (lanetype-Jnn Jnn-I8)) v-sx lane-1-82 lane-2-30)) lane-1-lst lane-2-lst)) in (v128 ∷ [])
fun-vbinop- (X lanetype-I16 (mk-dim v-M)) (vbinop--MAX v-sx) v128-1 v128-2 = let lane-1-lst = (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) v128-1) in let lane-2-lst = (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) v128-2) in let v128 = (inv-lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) (zipWith (λ (lane-1-84 : (uN-fam0 (16))) (lane-2-32 : (uN-fam0 (16))) → (imax- (lsizenn (lanetype-Jnn Jnn-I16)) v-sx lane-1-84 lane-2-32)) lane-1-lst lane-2-lst)) in (v128 ∷ [])
fun-vbinop- (X lanetype-I32 (mk-dim v-M)) (ADD-SAT v-sx) v128-1 v128-2 = let lane-1-lst = (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) v128-1) in let lane-2-lst = (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) v128-2) in let v128 = (inv-lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) (zipWith (λ (lane-1-86 : (uN-fam0 (32))) (lane-2-34 : (uN-fam0 (32))) → (iadd-sat- (lsizenn (lanetype-Jnn Jnn-I32)) v-sx lane-1-86 lane-2-34)) lane-1-lst lane-2-lst)) in (v128 ∷ [])
fun-vbinop- (X lanetype-I64 (mk-dim v-M)) (ADD-SAT v-sx) v128-1 v128-2 = let lane-1-lst = (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) v128-1) in let lane-2-lst = (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) v128-2) in let v128 = (inv-lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) (zipWith (λ (lane-1-88 : (uN-fam0 (64))) (lane-2-36 : (uN-fam0 (64))) → (iadd-sat- (lsizenn (lanetype-Jnn Jnn-I64)) v-sx lane-1-88 lane-2-36)) lane-1-lst lane-2-lst)) in (v128 ∷ [])
fun-vbinop- (X lanetype-I8 (mk-dim v-M)) (ADD-SAT v-sx) v128-1 v128-2 = let lane-1-lst = (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) v128-1) in let lane-2-lst = (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) v128-2) in let v128 = (inv-lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) (zipWith (λ (lane-1-90 : (uN-fam0 (8))) (lane-2-38 : (uN-fam0 (8))) → (iadd-sat- (lsizenn (lanetype-Jnn Jnn-I8)) v-sx lane-1-90 lane-2-38)) lane-1-lst lane-2-lst)) in (v128 ∷ [])
fun-vbinop- (X lanetype-I16 (mk-dim v-M)) (ADD-SAT v-sx) v128-1 v128-2 = let lane-1-lst = (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) v128-1) in let lane-2-lst = (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) v128-2) in let v128 = (inv-lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) (zipWith (λ (lane-1-92 : (uN-fam0 (16))) (lane-2-40 : (uN-fam0 (16))) → (iadd-sat- (lsizenn (lanetype-Jnn Jnn-I16)) v-sx lane-1-92 lane-2-40)) lane-1-lst lane-2-lst)) in (v128 ∷ [])
fun-vbinop- (X lanetype-I32 (mk-dim v-M)) (SUB-SAT v-sx) v128-1 v128-2 = let lane-1-lst = (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) v128-1) in let lane-2-lst = (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) v128-2) in let v128 = (inv-lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) (zipWith (λ (lane-1-94 : (uN-fam0 (32))) (lane-2-42 : (uN-fam0 (32))) → (isub-sat- (lsizenn (lanetype-Jnn Jnn-I32)) v-sx lane-1-94 lane-2-42)) lane-1-lst lane-2-lst)) in (v128 ∷ [])
fun-vbinop- (X lanetype-I64 (mk-dim v-M)) (SUB-SAT v-sx) v128-1 v128-2 = let lane-1-lst = (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) v128-1) in let lane-2-lst = (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) v128-2) in let v128 = (inv-lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) (zipWith (λ (lane-1-96 : (uN-fam0 (64))) (lane-2-44 : (uN-fam0 (64))) → (isub-sat- (lsizenn (lanetype-Jnn Jnn-I64)) v-sx lane-1-96 lane-2-44)) lane-1-lst lane-2-lst)) in (v128 ∷ [])
fun-vbinop- (X lanetype-I8 (mk-dim v-M)) (SUB-SAT v-sx) v128-1 v128-2 = let lane-1-lst = (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) v128-1) in let lane-2-lst = (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) v128-2) in let v128 = (inv-lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) (zipWith (λ (lane-1-98 : (uN-fam0 (8))) (lane-2-46 : (uN-fam0 (8))) → (isub-sat- (lsizenn (lanetype-Jnn Jnn-I8)) v-sx lane-1-98 lane-2-46)) lane-1-lst lane-2-lst)) in (v128 ∷ [])
fun-vbinop- (X lanetype-I16 (mk-dim v-M)) (SUB-SAT v-sx) v128-1 v128-2 = let lane-1-lst = (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) v128-1) in let lane-2-lst = (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) v128-2) in let v128 = (inv-lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) (zipWith (λ (lane-1-100 : (uN-fam0 (16))) (lane-2-48 : (uN-fam0 (16))) → (isub-sat- (lsizenn (lanetype-Jnn Jnn-I16)) v-sx lane-1-100 lane-2-48)) lane-1-lst lane-2-lst)) in (v128 ∷ [])
fun-vbinop- (X lanetype-I32 (mk-dim v-M)) vbinop--MUL v128-1 v128-2 = let lane-1-lst = (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) v128-1) in let lane-2-lst = (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) v128-2) in let v128 = (inv-lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) (zipWith (λ (lane-1-102 : (uN-fam0 (32))) (lane-2-50 : (uN-fam0 (32))) → (imul- (lsizenn (lanetype-Jnn Jnn-I32)) lane-1-102 lane-2-50)) lane-1-lst lane-2-lst)) in (v128 ∷ [])
fun-vbinop- (X lanetype-I64 (mk-dim v-M)) vbinop--MUL v128-1 v128-2 = let lane-1-lst = (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) v128-1) in let lane-2-lst = (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) v128-2) in let v128 = (inv-lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) (zipWith (λ (lane-1-104 : (uN-fam0 (64))) (lane-2-52 : (uN-fam0 (64))) → (imul- (lsizenn (lanetype-Jnn Jnn-I64)) lane-1-104 lane-2-52)) lane-1-lst lane-2-lst)) in (v128 ∷ [])
fun-vbinop- (X lanetype-I8 (mk-dim v-M)) vbinop--MUL v128-1 v128-2 = let lane-1-lst = (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) v128-1) in let lane-2-lst = (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) v128-2) in let v128 = (inv-lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) (zipWith (λ (lane-1-106 : (uN-fam0 (8))) (lane-2-54 : (uN-fam0 (8))) → (imul- (lsizenn (lanetype-Jnn Jnn-I8)) lane-1-106 lane-2-54)) lane-1-lst lane-2-lst)) in (v128 ∷ [])
fun-vbinop- (X lanetype-I16 (mk-dim v-M)) vbinop--MUL v128-1 v128-2 = let lane-1-lst = (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) v128-1) in let lane-2-lst = (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) v128-2) in let v128 = (inv-lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) (zipWith (λ (lane-1-108 : (uN-fam0 (16))) (lane-2-56 : (uN-fam0 (16))) → (imul- (lsizenn (lanetype-Jnn Jnn-I16)) lane-1-108 lane-2-56)) lane-1-lst lane-2-lst)) in (v128 ∷ [])
fun-vbinop- (X lanetype-I32 (mk-dim v-M)) AVGRU v128-1 v128-2 = let lane-1-lst = (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) v128-1) in let lane-2-lst = (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) v128-2) in let v128 = (inv-lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) (zipWith (λ (lane-1-110 : (uN-fam0 (32))) (lane-2-58 : (uN-fam0 (32))) → (iavgr- (lsizenn (lanetype-Jnn Jnn-I32)) U lane-1-110 lane-2-58)) lane-1-lst lane-2-lst)) in (v128 ∷ [])
fun-vbinop- (X lanetype-I64 (mk-dim v-M)) AVGRU v128-1 v128-2 = let lane-1-lst = (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) v128-1) in let lane-2-lst = (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) v128-2) in let v128 = (inv-lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) (zipWith (λ (lane-1-112 : (uN-fam0 (64))) (lane-2-60 : (uN-fam0 (64))) → (iavgr- (lsizenn (lanetype-Jnn Jnn-I64)) U lane-1-112 lane-2-60)) lane-1-lst lane-2-lst)) in (v128 ∷ [])
fun-vbinop- (X lanetype-I8 (mk-dim v-M)) AVGRU v128-1 v128-2 = let lane-1-lst = (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) v128-1) in let lane-2-lst = (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) v128-2) in let v128 = (inv-lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) (zipWith (λ (lane-1-114 : (uN-fam0 (8))) (lane-2-62 : (uN-fam0 (8))) → (iavgr- (lsizenn (lanetype-Jnn Jnn-I8)) U lane-1-114 lane-2-62)) lane-1-lst lane-2-lst)) in (v128 ∷ [])
fun-vbinop- (X lanetype-I16 (mk-dim v-M)) AVGRU v128-1 v128-2 = let lane-1-lst = (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) v128-1) in let lane-2-lst = (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) v128-2) in let v128 = (inv-lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) (zipWith (λ (lane-1-116 : (uN-fam0 (16))) (lane-2-64 : (uN-fam0 (16))) → (iavgr- (lsizenn (lanetype-Jnn Jnn-I16)) U lane-1-116 lane-2-64)) lane-1-lst lane-2-lst)) in (v128 ∷ [])
fun-vbinop- (X lanetype-I32 (mk-dim v-M)) Q15MULR-SATS v128-1 v128-2 = let lane-1-lst = (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) v128-1) in let lane-2-lst = (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) v128-2) in let v128 = (inv-lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) (zipWith (λ (lane-1-118 : (uN-fam0 (32))) (lane-2-66 : (uN-fam0 (32))) → (iq15mulr-sat- (lsizenn (lanetype-Jnn Jnn-I32)) S lane-1-118 lane-2-66)) lane-1-lst lane-2-lst)) in (v128 ∷ [])
fun-vbinop- (X lanetype-I64 (mk-dim v-M)) Q15MULR-SATS v128-1 v128-2 = let lane-1-lst = (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) v128-1) in let lane-2-lst = (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) v128-2) in let v128 = (inv-lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) (zipWith (λ (lane-1-120 : (uN-fam0 (64))) (lane-2-68 : (uN-fam0 (64))) → (iq15mulr-sat- (lsizenn (lanetype-Jnn Jnn-I64)) S lane-1-120 lane-2-68)) lane-1-lst lane-2-lst)) in (v128 ∷ [])
fun-vbinop- (X lanetype-I8 (mk-dim v-M)) Q15MULR-SATS v128-1 v128-2 = let lane-1-lst = (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) v128-1) in let lane-2-lst = (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) v128-2) in let v128 = (inv-lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) (zipWith (λ (lane-1-122 : (uN-fam0 (8))) (lane-2-70 : (uN-fam0 (8))) → (iq15mulr-sat- (lsizenn (lanetype-Jnn Jnn-I8)) S lane-1-122 lane-2-70)) lane-1-lst lane-2-lst)) in (v128 ∷ [])
fun-vbinop- (X lanetype-I16 (mk-dim v-M)) Q15MULR-SATS v128-1 v128-2 = let lane-1-lst = (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) v128-1) in let lane-2-lst = (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) v128-2) in let v128 = (inv-lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) (zipWith (λ (lane-1-124 : (uN-fam0 (16))) (lane-2-72 : (uN-fam0 (16))) → (iq15mulr-sat- (lsizenn (lanetype-Jnn Jnn-I16)) S lane-1-124 lane-2-72)) lane-1-lst lane-2-lst)) in (v128 ∷ [])
fun-vbinop- (X lanetype-F32 (mk-dim v-M)) vbinop--ADD v128-1 v128-2 = let lane-1-lst = (lanes- (X (lanetype-Fnn Fnn-F32) (mk-dim v-M)) v128-1) in let lane-2-lst = (lanes- (X (lanetype-Fnn Fnn-F32) (mk-dim v-M)) v128-2) in let lane-lst-lst = (setproduct- (fN-fam0 (32)) (zipWith (λ (lane-1-126 : (fN-fam0 (32))) (lane-2-74 : (fN-fam0 (32))) → (fadd- (sizenn (numtype-Fnn Fnn-F32)) lane-1-126 lane-2-74)) lane-1-lst lane-2-lst)) in let v128-lst = (map (λ (lane-lst-30 : (List (fN-fam0 (32)))) → (inv-lanes- (X (lanetype-Fnn Fnn-F32) (mk-dim v-M)) lane-lst-30)) lane-lst-lst) in v128-lst
fun-vbinop- (X lanetype-F64 (mk-dim v-M)) vbinop--ADD v128-1 v128-2 = let lane-1-lst = (lanes- (X (lanetype-Fnn Fnn-F64) (mk-dim v-M)) v128-1) in let lane-2-lst = (lanes- (X (lanetype-Fnn Fnn-F64) (mk-dim v-M)) v128-2) in let lane-lst-lst = (setproduct- (fN-fam0 (64)) (zipWith (λ (lane-1-128 : (fN-fam0 (64))) (lane-2-76 : (fN-fam0 (64))) → (fadd- (sizenn (numtype-Fnn Fnn-F64)) lane-1-128 lane-2-76)) lane-1-lst lane-2-lst)) in let v128-lst = (map (λ (lane-lst-32 : (List (fN-fam0 (64)))) → (inv-lanes- (X (lanetype-Fnn Fnn-F64) (mk-dim v-M)) lane-lst-32)) lane-lst-lst) in v128-lst
fun-vbinop- (X lanetype-F32 (mk-dim v-M)) vbinop--SUB v128-1 v128-2 = let lane-1-lst = (lanes- (X (lanetype-Fnn Fnn-F32) (mk-dim v-M)) v128-1) in let lane-2-lst = (lanes- (X (lanetype-Fnn Fnn-F32) (mk-dim v-M)) v128-2) in let lane-lst-lst = (setproduct- (fN-fam0 (32)) (zipWith (λ (lane-1-130 : (fN-fam0 (32))) (lane-2-78 : (fN-fam0 (32))) → (fsub- (sizenn (numtype-Fnn Fnn-F32)) lane-1-130 lane-2-78)) lane-1-lst lane-2-lst)) in let v128-lst = (map (λ (lane-lst-34 : (List (fN-fam0 (32)))) → (inv-lanes- (X (lanetype-Fnn Fnn-F32) (mk-dim v-M)) lane-lst-34)) lane-lst-lst) in v128-lst
fun-vbinop- (X lanetype-F64 (mk-dim v-M)) vbinop--SUB v128-1 v128-2 = let lane-1-lst = (lanes- (X (lanetype-Fnn Fnn-F64) (mk-dim v-M)) v128-1) in let lane-2-lst = (lanes- (X (lanetype-Fnn Fnn-F64) (mk-dim v-M)) v128-2) in let lane-lst-lst = (setproduct- (fN-fam0 (64)) (zipWith (λ (lane-1-132 : (fN-fam0 (64))) (lane-2-80 : (fN-fam0 (64))) → (fsub- (sizenn (numtype-Fnn Fnn-F64)) lane-1-132 lane-2-80)) lane-1-lst lane-2-lst)) in let v128-lst = (map (λ (lane-lst-36 : (List (fN-fam0 (64)))) → (inv-lanes- (X (lanetype-Fnn Fnn-F64) (mk-dim v-M)) lane-lst-36)) lane-lst-lst) in v128-lst
fun-vbinop- (X lanetype-F32 (mk-dim v-M)) vbinop--MUL v128-1 v128-2 = let lane-1-lst = (lanes- (X (lanetype-Fnn Fnn-F32) (mk-dim v-M)) v128-1) in let lane-2-lst = (lanes- (X (lanetype-Fnn Fnn-F32) (mk-dim v-M)) v128-2) in let lane-lst-lst = (setproduct- (fN-fam0 (32)) (zipWith (λ (lane-1-134 : (fN-fam0 (32))) (lane-2-82 : (fN-fam0 (32))) → (fmul- (sizenn (numtype-Fnn Fnn-F32)) lane-1-134 lane-2-82)) lane-1-lst lane-2-lst)) in let v128-lst = (map (λ (lane-lst-38 : (List (fN-fam0 (32)))) → (inv-lanes- (X (lanetype-Fnn Fnn-F32) (mk-dim v-M)) lane-lst-38)) lane-lst-lst) in v128-lst
fun-vbinop- (X lanetype-F64 (mk-dim v-M)) vbinop--MUL v128-1 v128-2 = let lane-1-lst = (lanes- (X (lanetype-Fnn Fnn-F64) (mk-dim v-M)) v128-1) in let lane-2-lst = (lanes- (X (lanetype-Fnn Fnn-F64) (mk-dim v-M)) v128-2) in let lane-lst-lst = (setproduct- (fN-fam0 (64)) (zipWith (λ (lane-1-136 : (fN-fam0 (64))) (lane-2-84 : (fN-fam0 (64))) → (fmul- (sizenn (numtype-Fnn Fnn-F64)) lane-1-136 lane-2-84)) lane-1-lst lane-2-lst)) in let v128-lst = (map (λ (lane-lst-40 : (List (fN-fam0 (64)))) → (inv-lanes- (X (lanetype-Fnn Fnn-F64) (mk-dim v-M)) lane-lst-40)) lane-lst-lst) in v128-lst
fun-vbinop- (X lanetype-F32 (mk-dim v-M)) vbinop--DIV v128-1 v128-2 = let lane-1-lst = (lanes- (X (lanetype-Fnn Fnn-F32) (mk-dim v-M)) v128-1) in let lane-2-lst = (lanes- (X (lanetype-Fnn Fnn-F32) (mk-dim v-M)) v128-2) in let lane-lst-lst = (setproduct- (fN-fam0 (32)) (zipWith (λ (lane-1-138 : (fN-fam0 (32))) (lane-2-86 : (fN-fam0 (32))) → (fdiv- (sizenn (numtype-Fnn Fnn-F32)) lane-1-138 lane-2-86)) lane-1-lst lane-2-lst)) in let v128-lst = (map (λ (lane-lst-42 : (List (fN-fam0 (32)))) → (inv-lanes- (X (lanetype-Fnn Fnn-F32) (mk-dim v-M)) lane-lst-42)) lane-lst-lst) in v128-lst
fun-vbinop- (X lanetype-F64 (mk-dim v-M)) vbinop--DIV v128-1 v128-2 = let lane-1-lst = (lanes- (X (lanetype-Fnn Fnn-F64) (mk-dim v-M)) v128-1) in let lane-2-lst = (lanes- (X (lanetype-Fnn Fnn-F64) (mk-dim v-M)) v128-2) in let lane-lst-lst = (setproduct- (fN-fam0 (64)) (zipWith (λ (lane-1-140 : (fN-fam0 (64))) (lane-2-88 : (fN-fam0 (64))) → (fdiv- (sizenn (numtype-Fnn Fnn-F64)) lane-1-140 lane-2-88)) lane-1-lst lane-2-lst)) in let v128-lst = (map (λ (lane-lst-44 : (List (fN-fam0 (64)))) → (inv-lanes- (X (lanetype-Fnn Fnn-F64) (mk-dim v-M)) lane-lst-44)) lane-lst-lst) in v128-lst
fun-vbinop- (X lanetype-F32 (mk-dim v-M)) vbinop--MIN v128-1 v128-2 = let lane-1-lst = (lanes- (X (lanetype-Fnn Fnn-F32) (mk-dim v-M)) v128-1) in let lane-2-lst = (lanes- (X (lanetype-Fnn Fnn-F32) (mk-dim v-M)) v128-2) in let lane-lst-lst = (setproduct- (fN-fam0 (32)) (zipWith (λ (lane-1-142 : (fN-fam0 (32))) (lane-2-90 : (fN-fam0 (32))) → (fmin- (sizenn (numtype-Fnn Fnn-F32)) lane-1-142 lane-2-90)) lane-1-lst lane-2-lst)) in let v128-lst = (map (λ (lane-lst-46 : (List (fN-fam0 (32)))) → (inv-lanes- (X (lanetype-Fnn Fnn-F32) (mk-dim v-M)) lane-lst-46)) lane-lst-lst) in v128-lst
fun-vbinop- (X lanetype-F64 (mk-dim v-M)) vbinop--MIN v128-1 v128-2 = let lane-1-lst = (lanes- (X (lanetype-Fnn Fnn-F64) (mk-dim v-M)) v128-1) in let lane-2-lst = (lanes- (X (lanetype-Fnn Fnn-F64) (mk-dim v-M)) v128-2) in let lane-lst-lst = (setproduct- (fN-fam0 (64)) (zipWith (λ (lane-1-144 : (fN-fam0 (64))) (lane-2-92 : (fN-fam0 (64))) → (fmin- (sizenn (numtype-Fnn Fnn-F64)) lane-1-144 lane-2-92)) lane-1-lst lane-2-lst)) in let v128-lst = (map (λ (lane-lst-48 : (List (fN-fam0 (64)))) → (inv-lanes- (X (lanetype-Fnn Fnn-F64) (mk-dim v-M)) lane-lst-48)) lane-lst-lst) in v128-lst
fun-vbinop- (X lanetype-F32 (mk-dim v-M)) vbinop--MAX v128-1 v128-2 = let lane-1-lst = (lanes- (X (lanetype-Fnn Fnn-F32) (mk-dim v-M)) v128-1) in let lane-2-lst = (lanes- (X (lanetype-Fnn Fnn-F32) (mk-dim v-M)) v128-2) in let lane-lst-lst = (setproduct- (fN-fam0 (32)) (zipWith (λ (lane-1-146 : (fN-fam0 (32))) (lane-2-94 : (fN-fam0 (32))) → (fmax- (sizenn (numtype-Fnn Fnn-F32)) lane-1-146 lane-2-94)) lane-1-lst lane-2-lst)) in let v128-lst = (map (λ (lane-lst-50 : (List (fN-fam0 (32)))) → (inv-lanes- (X (lanetype-Fnn Fnn-F32) (mk-dim v-M)) lane-lst-50)) lane-lst-lst) in v128-lst
fun-vbinop- (X lanetype-F64 (mk-dim v-M)) vbinop--MAX v128-1 v128-2 = let lane-1-lst = (lanes- (X (lanetype-Fnn Fnn-F64) (mk-dim v-M)) v128-1) in let lane-2-lst = (lanes- (X (lanetype-Fnn Fnn-F64) (mk-dim v-M)) v128-2) in let lane-lst-lst = (setproduct- (fN-fam0 (64)) (zipWith (λ (lane-1-148 : (fN-fam0 (64))) (lane-2-96 : (fN-fam0 (64))) → (fmax- (sizenn (numtype-Fnn Fnn-F64)) lane-1-148 lane-2-96)) lane-1-lst lane-2-lst)) in let v128-lst = (map (λ (lane-lst-52 : (List (fN-fam0 (64)))) → (inv-lanes- (X (lanetype-Fnn Fnn-F64) (mk-dim v-M)) lane-lst-52)) lane-lst-lst) in v128-lst
fun-vbinop- (X lanetype-F32 (mk-dim v-M)) PMIN v128-1 v128-2 = let lane-1-lst = (lanes- (X (lanetype-Fnn Fnn-F32) (mk-dim v-M)) v128-1) in let lane-2-lst = (lanes- (X (lanetype-Fnn Fnn-F32) (mk-dim v-M)) v128-2) in let lane-lst-lst = (setproduct- (fN-fam0 (32)) (zipWith (λ (lane-1-150 : (fN-fam0 (32))) (lane-2-98 : (fN-fam0 (32))) → (fpmin- (sizenn (numtype-Fnn Fnn-F32)) lane-1-150 lane-2-98)) lane-1-lst lane-2-lst)) in let v128-lst = (map (λ (lane-lst-54 : (List (fN-fam0 (32)))) → (inv-lanes- (X (lanetype-Fnn Fnn-F32) (mk-dim v-M)) lane-lst-54)) lane-lst-lst) in v128-lst
fun-vbinop- (X lanetype-F64 (mk-dim v-M)) PMIN v128-1 v128-2 = let lane-1-lst = (lanes- (X (lanetype-Fnn Fnn-F64) (mk-dim v-M)) v128-1) in let lane-2-lst = (lanes- (X (lanetype-Fnn Fnn-F64) (mk-dim v-M)) v128-2) in let lane-lst-lst = (setproduct- (fN-fam0 (64)) (zipWith (λ (lane-1-152 : (fN-fam0 (64))) (lane-2-100 : (fN-fam0 (64))) → (fpmin- (sizenn (numtype-Fnn Fnn-F64)) lane-1-152 lane-2-100)) lane-1-lst lane-2-lst)) in let v128-lst = (map (λ (lane-lst-56 : (List (fN-fam0 (64)))) → (inv-lanes- (X (lanetype-Fnn Fnn-F64) (mk-dim v-M)) lane-lst-56)) lane-lst-lst) in v128-lst
fun-vbinop- (X lanetype-F32 (mk-dim v-M)) PMAX v128-1 v128-2 = let lane-1-lst = (lanes- (X (lanetype-Fnn Fnn-F32) (mk-dim v-M)) v128-1) in let lane-2-lst = (lanes- (X (lanetype-Fnn Fnn-F32) (mk-dim v-M)) v128-2) in let lane-lst-lst = (setproduct- (fN-fam0 (32)) (zipWith (λ (lane-1-154 : (fN-fam0 (32))) (lane-2-102 : (fN-fam0 (32))) → (fpmax- (sizenn (numtype-Fnn Fnn-F32)) lane-1-154 lane-2-102)) lane-1-lst lane-2-lst)) in let v128-lst = (map (λ (lane-lst-58 : (List (fN-fam0 (32)))) → (inv-lanes- (X (lanetype-Fnn Fnn-F32) (mk-dim v-M)) lane-lst-58)) lane-lst-lst) in v128-lst
fun-vbinop- (X lanetype-F64 (mk-dim v-M)) PMAX v128-1 v128-2 = let lane-1-lst = (lanes- (X (lanetype-Fnn Fnn-F64) (mk-dim v-M)) v128-1) in let lane-2-lst = (lanes- (X (lanetype-Fnn Fnn-F64) (mk-dim v-M)) v128-2) in let lane-lst-lst = (setproduct- (fN-fam0 (64)) (zipWith (λ (lane-1-156 : (fN-fam0 (64))) (lane-2-104 : (fN-fam0 (64))) → (fpmax- (sizenn (numtype-Fnn Fnn-F64)) lane-1-156 lane-2-104)) lane-1-lst lane-2-lst)) in let v128-lst = (map (λ (lane-lst-60 : (List (fN-fam0 (64)))) → (inv-lanes- (X (lanetype-Fnn Fnn-F64) (mk-dim v-M)) lane-lst-60)) lane-lst-lst) in v128-lst
fun-vbinop- v-shape v-vbinop- v-vec- vec--0 = []

{- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:381.1-382.34 -}
postulate fun-vrelop- : ∀ (v-shape : shape) (v-vrelop- : (vrelop- v-shape)) (v-vec- : (uN-fam0 (128))) (vec--0 : (uN-fam0 (128))) → (uN-fam0 (128))

{- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.1-384.41 -}
{-# TERMINATING #-}
vcvtop-- : (shape-1 : shape) (shape-2 : shape) (v-vcvtop : vcvtop) (v-lane- : (lane- (fun-lanetype shape-1))) → (List (lane- (fun-lanetype shape-2)))
vcvtop-- (X lanetype-I32 (mk-dim M-1)) (X lanetype-I32 (mk-dim M-2)) (vcvtop-EXTEND v-half v-sx) iN-1 = let iN-2 = (extend-- (lsizenn1 (lanetype-Jnn Jnn-I32)) (lsizenn2 (lanetype-Jnn Jnn-I32)) v-sx iN-1) in (iN-2 ∷ [])
vcvtop-- (X lanetype-I64 (mk-dim M-1)) (X lanetype-I32 (mk-dim M-2)) (vcvtop-EXTEND v-half v-sx) iN-1 = let iN-2 = (extend-- (lsizenn1 (lanetype-Jnn Jnn-I64)) (lsizenn2 (lanetype-Jnn Jnn-I32)) v-sx iN-1) in (iN-2 ∷ [])
vcvtop-- (X lanetype-I8 (mk-dim M-1)) (X lanetype-I32 (mk-dim M-2)) (vcvtop-EXTEND v-half v-sx) iN-1 = let iN-2 = (extend-- (lsizenn1 (lanetype-Jnn Jnn-I8)) (lsizenn2 (lanetype-Jnn Jnn-I32)) v-sx iN-1) in (iN-2 ∷ [])
vcvtop-- (X lanetype-I16 (mk-dim M-1)) (X lanetype-I32 (mk-dim M-2)) (vcvtop-EXTEND v-half v-sx) iN-1 = let iN-2 = (extend-- (lsizenn1 (lanetype-Jnn Jnn-I16)) (lsizenn2 (lanetype-Jnn Jnn-I32)) v-sx iN-1) in (iN-2 ∷ [])
vcvtop-- (X lanetype-I32 (mk-dim M-1)) (X lanetype-I64 (mk-dim M-2)) (vcvtop-EXTEND v-half v-sx) iN-1 = let iN-2 = (extend-- (lsizenn1 (lanetype-Jnn Jnn-I32)) (lsizenn2 (lanetype-Jnn Jnn-I64)) v-sx iN-1) in (iN-2 ∷ [])
vcvtop-- (X lanetype-I64 (mk-dim M-1)) (X lanetype-I64 (mk-dim M-2)) (vcvtop-EXTEND v-half v-sx) iN-1 = let iN-2 = (extend-- (lsizenn1 (lanetype-Jnn Jnn-I64)) (lsizenn2 (lanetype-Jnn Jnn-I64)) v-sx iN-1) in (iN-2 ∷ [])
vcvtop-- (X lanetype-I8 (mk-dim M-1)) (X lanetype-I64 (mk-dim M-2)) (vcvtop-EXTEND v-half v-sx) iN-1 = let iN-2 = (extend-- (lsizenn1 (lanetype-Jnn Jnn-I8)) (lsizenn2 (lanetype-Jnn Jnn-I64)) v-sx iN-1) in (iN-2 ∷ [])
vcvtop-- (X lanetype-I16 (mk-dim M-1)) (X lanetype-I64 (mk-dim M-2)) (vcvtop-EXTEND v-half v-sx) iN-1 = let iN-2 = (extend-- (lsizenn1 (lanetype-Jnn Jnn-I16)) (lsizenn2 (lanetype-Jnn Jnn-I64)) v-sx iN-1) in (iN-2 ∷ [])
vcvtop-- (X lanetype-I32 (mk-dim M-1)) (X lanetype-I8 (mk-dim M-2)) (vcvtop-EXTEND v-half v-sx) iN-1 = let iN-2 = (extend-- (lsizenn1 (lanetype-Jnn Jnn-I32)) (lsizenn2 (lanetype-Jnn Jnn-I8)) v-sx iN-1) in (iN-2 ∷ [])
vcvtop-- (X lanetype-I64 (mk-dim M-1)) (X lanetype-I8 (mk-dim M-2)) (vcvtop-EXTEND v-half v-sx) iN-1 = let iN-2 = (extend-- (lsizenn1 (lanetype-Jnn Jnn-I64)) (lsizenn2 (lanetype-Jnn Jnn-I8)) v-sx iN-1) in (iN-2 ∷ [])
vcvtop-- (X lanetype-I8 (mk-dim M-1)) (X lanetype-I8 (mk-dim M-2)) (vcvtop-EXTEND v-half v-sx) iN-1 = let iN-2 = (extend-- (lsizenn1 (lanetype-Jnn Jnn-I8)) (lsizenn2 (lanetype-Jnn Jnn-I8)) v-sx iN-1) in (iN-2 ∷ [])
vcvtop-- (X lanetype-I16 (mk-dim M-1)) (X lanetype-I8 (mk-dim M-2)) (vcvtop-EXTEND v-half v-sx) iN-1 = let iN-2 = (extend-- (lsizenn1 (lanetype-Jnn Jnn-I16)) (lsizenn2 (lanetype-Jnn Jnn-I8)) v-sx iN-1) in (iN-2 ∷ [])
vcvtop-- (X lanetype-I32 (mk-dim M-1)) (X lanetype-I16 (mk-dim M-2)) (vcvtop-EXTEND v-half v-sx) iN-1 = let iN-2 = (extend-- (lsizenn1 (lanetype-Jnn Jnn-I32)) (lsizenn2 (lanetype-Jnn Jnn-I16)) v-sx iN-1) in (iN-2 ∷ [])
vcvtop-- (X lanetype-I64 (mk-dim M-1)) (X lanetype-I16 (mk-dim M-2)) (vcvtop-EXTEND v-half v-sx) iN-1 = let iN-2 = (extend-- (lsizenn1 (lanetype-Jnn Jnn-I64)) (lsizenn2 (lanetype-Jnn Jnn-I16)) v-sx iN-1) in (iN-2 ∷ [])
vcvtop-- (X lanetype-I8 (mk-dim M-1)) (X lanetype-I16 (mk-dim M-2)) (vcvtop-EXTEND v-half v-sx) iN-1 = let iN-2 = (extend-- (lsizenn1 (lanetype-Jnn Jnn-I8)) (lsizenn2 (lanetype-Jnn Jnn-I16)) v-sx iN-1) in (iN-2 ∷ [])
vcvtop-- (X lanetype-I16 (mk-dim M-1)) (X lanetype-I16 (mk-dim M-2)) (vcvtop-EXTEND v-half v-sx) iN-1 = let iN-2 = (extend-- (lsizenn1 (lanetype-Jnn Jnn-I16)) (lsizenn2 (lanetype-Jnn Jnn-I16)) v-sx iN-1) in (iN-2 ∷ [])
vcvtop-- (X lanetype-I32 (mk-dim M-1)) (X lanetype-F32 (mk-dim M-2)) (vcvtop-CONVERT half-opt v-sx) iN-1 = let fN-2 = (convert-- (lsizenn1 (lanetype-Jnn Jnn-I32)) (lsizenn2 (lanetype-Fnn Fnn-F32)) v-sx iN-1) in (fN-2 ∷ [])
vcvtop-- (X lanetype-I64 (mk-dim M-1)) (X lanetype-F32 (mk-dim M-2)) (vcvtop-CONVERT half-opt v-sx) iN-1 = let fN-2 = (convert-- (lsizenn1 (lanetype-Jnn Jnn-I64)) (lsizenn2 (lanetype-Fnn Fnn-F32)) v-sx iN-1) in (fN-2 ∷ [])
vcvtop-- (X lanetype-I8 (mk-dim M-1)) (X lanetype-F32 (mk-dim M-2)) (vcvtop-CONVERT half-opt v-sx) iN-1 = let fN-2 = (convert-- (lsizenn1 (lanetype-Jnn Jnn-I8)) (lsizenn2 (lanetype-Fnn Fnn-F32)) v-sx iN-1) in (fN-2 ∷ [])
vcvtop-- (X lanetype-I16 (mk-dim M-1)) (X lanetype-F32 (mk-dim M-2)) (vcvtop-CONVERT half-opt v-sx) iN-1 = let fN-2 = (convert-- (lsizenn1 (lanetype-Jnn Jnn-I16)) (lsizenn2 (lanetype-Fnn Fnn-F32)) v-sx iN-1) in (fN-2 ∷ [])
vcvtop-- (X lanetype-I32 (mk-dim M-1)) (X lanetype-F64 (mk-dim M-2)) (vcvtop-CONVERT half-opt v-sx) iN-1 = let fN-2 = (convert-- (lsizenn1 (lanetype-Jnn Jnn-I32)) (lsizenn2 (lanetype-Fnn Fnn-F64)) v-sx iN-1) in (fN-2 ∷ [])
vcvtop-- (X lanetype-I64 (mk-dim M-1)) (X lanetype-F64 (mk-dim M-2)) (vcvtop-CONVERT half-opt v-sx) iN-1 = let fN-2 = (convert-- (lsizenn1 (lanetype-Jnn Jnn-I64)) (lsizenn2 (lanetype-Fnn Fnn-F64)) v-sx iN-1) in (fN-2 ∷ [])
vcvtop-- (X lanetype-I8 (mk-dim M-1)) (X lanetype-F64 (mk-dim M-2)) (vcvtop-CONVERT half-opt v-sx) iN-1 = let fN-2 = (convert-- (lsizenn1 (lanetype-Jnn Jnn-I8)) (lsizenn2 (lanetype-Fnn Fnn-F64)) v-sx iN-1) in (fN-2 ∷ [])
vcvtop-- (X lanetype-I16 (mk-dim M-1)) (X lanetype-F64 (mk-dim M-2)) (vcvtop-CONVERT half-opt v-sx) iN-1 = let fN-2 = (convert-- (lsizenn1 (lanetype-Jnn Jnn-I16)) (lsizenn2 (lanetype-Fnn Fnn-F64)) v-sx iN-1) in (fN-2 ∷ [])
vcvtop-- (X lanetype-F32 (mk-dim M-1)) (X lanetype-I32 (mk-dim M-2)) (vcvtop-TRUNC-SAT v-sx zero-opt) fN-1 = let iN-2-opt = (trunc-sat-- (lsizenn1 (lanetype-Fnn Fnn-F32)) (lsizenn2 (lanetype-Inn Inn-I32)) v-sx fN-1) in (list- (uN-fam0 (32)) iN-2-opt)
vcvtop-- (X lanetype-F64 (mk-dim M-1)) (X lanetype-I32 (mk-dim M-2)) (vcvtop-TRUNC-SAT v-sx zero-opt) fN-1 = let iN-2-opt = (trunc-sat-- (lsizenn1 (lanetype-Fnn Fnn-F64)) (lsizenn2 (lanetype-Inn Inn-I32)) v-sx fN-1) in (list- (uN-fam0 (32)) iN-2-opt)
vcvtop-- (X lanetype-F32 (mk-dim M-1)) (X lanetype-I64 (mk-dim M-2)) (vcvtop-TRUNC-SAT v-sx zero-opt) fN-1 = let iN-2-opt = (trunc-sat-- (lsizenn1 (lanetype-Fnn Fnn-F32)) (lsizenn2 (lanetype-Inn Inn-I64)) v-sx fN-1) in (list- (uN-fam0 (64)) iN-2-opt)
vcvtop-- (X lanetype-F64 (mk-dim M-1)) (X lanetype-I64 (mk-dim M-2)) (vcvtop-TRUNC-SAT v-sx zero-opt) fN-1 = let iN-2-opt = (trunc-sat-- (lsizenn1 (lanetype-Fnn Fnn-F64)) (lsizenn2 (lanetype-Inn Inn-I64)) v-sx fN-1) in (list- (uN-fam0 (64)) iN-2-opt)
vcvtop-- (X lanetype-F32 (mk-dim M-1)) (X lanetype-F32 (mk-dim M-2)) (vcvtop-DEMOTE ZERO) fN-1 = let fN-2-lst = (demote-- (lsizenn1 (lanetype-Fnn Fnn-F32)) (lsizenn2 (lanetype-Fnn Fnn-F32)) fN-1) in fN-2-lst
vcvtop-- (X lanetype-F64 (mk-dim M-1)) (X lanetype-F32 (mk-dim M-2)) (vcvtop-DEMOTE ZERO) fN-1 = let fN-2-lst = (demote-- (lsizenn1 (lanetype-Fnn Fnn-F64)) (lsizenn2 (lanetype-Fnn Fnn-F32)) fN-1) in fN-2-lst
vcvtop-- (X lanetype-F32 (mk-dim M-1)) (X lanetype-F64 (mk-dim M-2)) (vcvtop-DEMOTE ZERO) fN-1 = let fN-2-lst = (demote-- (lsizenn1 (lanetype-Fnn Fnn-F32)) (lsizenn2 (lanetype-Fnn Fnn-F64)) fN-1) in fN-2-lst
vcvtop-- (X lanetype-F64 (mk-dim M-1)) (X lanetype-F64 (mk-dim M-2)) (vcvtop-DEMOTE ZERO) fN-1 = let fN-2-lst = (demote-- (lsizenn1 (lanetype-Fnn Fnn-F64)) (lsizenn2 (lanetype-Fnn Fnn-F64)) fN-1) in fN-2-lst
vcvtop-- (X lanetype-F32 (mk-dim M-1)) (X lanetype-F32 (mk-dim M-2)) PROMOTELOW fN-1 = let fN-2-lst = (promote-- (lsizenn1 (lanetype-Fnn Fnn-F32)) (lsizenn2 (lanetype-Fnn Fnn-F32)) fN-1) in fN-2-lst
vcvtop-- (X lanetype-F64 (mk-dim M-1)) (X lanetype-F32 (mk-dim M-2)) PROMOTELOW fN-1 = let fN-2-lst = (promote-- (lsizenn1 (lanetype-Fnn Fnn-F64)) (lsizenn2 (lanetype-Fnn Fnn-F32)) fN-1) in fN-2-lst
vcvtop-- (X lanetype-F32 (mk-dim M-1)) (X lanetype-F64 (mk-dim M-2)) PROMOTELOW fN-1 = let fN-2-lst = (promote-- (lsizenn1 (lanetype-Fnn Fnn-F32)) (lsizenn2 (lanetype-Fnn Fnn-F64)) fN-1) in fN-2-lst
vcvtop-- (X lanetype-F64 (mk-dim M-1)) (X lanetype-F64 (mk-dim M-2)) PROMOTELOW fN-1 = let fN-2-lst = (promote-- (lsizenn1 (lanetype-Fnn Fnn-F64)) (lsizenn2 (lanetype-Fnn Fnn-F64)) fN-1) in fN-2-lst
vcvtop-- shape-1 shape-2 v-vcvtop v-lane- = []

{- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:583.1-584.42 -}
postulate vextunop-- : ∀ (ishape-1 : ishape) (ishape-2 : ishape) (v-vextunop- : (vextunop- ishape-1)) (v-vec- : (uN-fam0 (128))) → (uN-fam0 (128))

{- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:585.1-586.45 -}
postulate vextbinop-- : ∀ (ishape-1 : ishape) (ishape-2 : ishape) (v-vextbinop- : (vextbinop- ishape-1)) (v-vec- : (uN-fam0 (128))) (vec--0 : (uN-fam0 (128))) → (uN-fam0 (128))

{- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:608.1-609.31 -}
{-# TERMINATING #-}
fun-vshiftop- : (v-ishape : ishape) (v-vshiftop- : (vshiftop- v-ishape)) (v-lane- : (lane- (fun-lanetype (shape-ishape v-ishape)))) (v-u32 : u32) → (lane- (fun-lanetype (shape-ishape v-ishape)))
fun-vshiftop- (ishape-X Jnn-I32 (mk-dim v-M)) vshiftop--SHL lane (mk-uN v-n) = (ishl- (lsizenn (lanetype-Jnn Jnn-I32)) lane (mk-uN v-n))
fun-vshiftop- (ishape-X Jnn-I64 (mk-dim v-M)) vshiftop--SHL lane (mk-uN v-n) = (ishl- (lsizenn (lanetype-Jnn Jnn-I64)) lane (mk-uN v-n))
fun-vshiftop- (ishape-X Jnn-I8 (mk-dim v-M)) vshiftop--SHL lane (mk-uN v-n) = (ishl- (lsizenn (lanetype-Jnn Jnn-I8)) lane (mk-uN v-n))
fun-vshiftop- (ishape-X Jnn-I16 (mk-dim v-M)) vshiftop--SHL lane (mk-uN v-n) = (ishl- (lsizenn (lanetype-Jnn Jnn-I16)) lane (mk-uN v-n))
fun-vshiftop- (ishape-X Jnn-I32 (mk-dim v-M)) (vshiftop--SHR v-sx) lane (mk-uN v-n) = (ishr- (lsizenn (lanetype-Jnn Jnn-I32)) v-sx lane (mk-uN v-n))
fun-vshiftop- (ishape-X Jnn-I64 (mk-dim v-M)) (vshiftop--SHR v-sx) lane (mk-uN v-n) = (ishr- (lsizenn (lanetype-Jnn Jnn-I64)) v-sx lane (mk-uN v-n))
fun-vshiftop- (ishape-X Jnn-I8 (mk-dim v-M)) (vshiftop--SHR v-sx) lane (mk-uN v-n) = (ishr- (lsizenn (lanetype-Jnn Jnn-I8)) v-sx lane (mk-uN v-n))
fun-vshiftop- (ishape-X Jnn-I16 (mk-dim v-M)) (vshiftop--SHR v-sx) lane (mk-uN v-n) = (ishr- (lsizenn (lanetype-Jnn Jnn-I16)) v-sx lane (mk-uN v-n))
fun-vshiftop- v-ishape v-vshiftop- v-lane- v-u32 = (Inhabited.default-val (inh-lane--fun (fun-lanetype (shape-ishape v-ishape))))

{- Type Alias Definition at: ../specification/wasm-2.0/4-runtime.spectec:5.1-5.39 -}
addr : Set
addr = ℕ

{- Type Alias Definition at: ../specification/wasm-2.0/4-runtime.spectec:6.1-6.53 -}
funcaddr : Set
funcaddr = addr

{- Type Alias Definition at: ../specification/wasm-2.0/4-runtime.spectec:7.1-7.53 -}
globaladdr : Set
globaladdr = addr

{- Type Alias Definition at: ../specification/wasm-2.0/4-runtime.spectec:8.1-8.51 -}
tableaddr : Set
tableaddr = addr

{- Type Alias Definition at: ../specification/wasm-2.0/4-runtime.spectec:9.1-9.50 -}
memaddr : Set
memaddr = addr

{- Type Alias Definition at: ../specification/wasm-2.0/4-runtime.spectec:10.1-10.49 -}
elemaddr : Set
elemaddr = addr

{- Type Alias Definition at: ../specification/wasm-2.0/4-runtime.spectec:11.1-11.49 -}
dataaddr : Set
dataaddr = addr

{- Type Alias Definition at: ../specification/wasm-2.0/4-runtime.spectec:12.1-12.49 -}
hostaddr : Set
hostaddr = addr

{- Inductive Type Definition at: ../specification/wasm-2.0/4-runtime.spectec:25.1-26.70 -}
data externaddr : Set where
  externaddr-FUNC : (v-funcaddr : funcaddr) → externaddr
  externaddr-GLOBAL : (v-globaladdr : globaladdr) → externaddr
  externaddr-TABLE : (v-tableaddr : tableaddr) → externaddr
  externaddr-MEM : (v-memaddr : memaddr) → externaddr

instance
  inh-externaddr : Inhabited externaddr
  inh-externaddr = record { default-val = (externaddr-FUNC (default-val)) }

{- Inductive Type Definition at: ../specification/wasm-2.0/4-runtime.spectec:37.1-38.62 -}
data num : Set where
  num-CONST : (v-numtype : numtype) → (_ : (num- v-numtype)) → num

{- Inductive Type Definition at: ../specification/wasm-2.0/4-runtime.spectec:39.1-40.62 -}
data vec : Set where
  vec-VCONST : (v-vectype : vectype) → (_ : (uN-fam0 ((unwrap! (size (valtype-vectype v-vectype)))))) → vec

{- Inductive Type Definition at: ../specification/wasm-2.0/4-runtime.spectec:41.1-42.71 -}
data ref : Set where
  ref-REF-NULL : (v-reftype : reftype) → ref
  REF-FUNC-ADDR : (v-funcaddr : funcaddr) → ref
  REF-HOST-ADDR : (v-hostaddr : hostaddr) → ref

instance
  inh-ref : Inhabited ref
  inh-ref = record { default-val = (ref-REF-NULL (default-val)) }

{- Inductive Type Definition at: ../specification/wasm-2.0/4-runtime.spectec:43.1-44.20 -}
data val : Set where
  val-CONST : (v-numtype : numtype) → (_ : (num- v-numtype)) → val
  val-VCONST : (v-vectype : vectype) → (_ : (uN-fam0 ((unwrap! (size (valtype-vectype v-vectype)))))) → val
  val-REF-NULL : (v-reftype : reftype) → val
  val-REF-FUNC-ADDR : (v-funcaddr : funcaddr) → val
  val-REF-HOST-ADDR : (v-hostaddr : hostaddr) → val

instance
  inh-val : Inhabited val
  inh-val = record { default-val = (let v-numtype = default-val in val-CONST v-numtype ((Inhabited.default-val (inh-num--fun v-numtype)))) }

{- Auxiliary Definition at:  -}
{-# TERMINATING #-}
val-ref : (var-0 : ref) → val
val-ref (ref-REF-NULL x0) = (val-REF-NULL x0)
val-ref (REF-FUNC-ADDR x0) = (val-REF-FUNC-ADDR x0)
val-ref (REF-HOST-ADDR x0) = (val-REF-HOST-ADDR x0)
val-ref var-0 = default-val

{- Inductive Type Definition at: ../specification/wasm-2.0/4-runtime.spectec:46.1-47.22 -}
data result : Set where
  -VALS : (val-lst : (List val)) → result
  TRAP : result

{- Record Creation Definition at: ../specification/wasm-2.0/4-runtime.spectec:78.1-80.22 -}
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

{- Record Creation Definition at: ../specification/wasm-2.0/4-runtime.spectec:82.1-90.26 -}
record moduleinst : Set where
  constructor mk-moduleinst
  field
    TYPES : (List functype)
    FUNCS : (List funcaddr)
    GLOBALS : (List globaladdr)
    TABLES : (List tableaddr)
    MEMS : (List memaddr)
    ELEMS : (List elemaddr)
    DATAS : (List dataaddr)
    EXPORTS : (List exportinst)
open moduleinst

instance
  append-moduleinst : HasAppend (moduleinst)
  append-moduleinst = record { append = λ arg1 arg2 → record {
    TYPES = TYPES arg1 ⧺ TYPES arg2 ;
    FUNCS = FUNCS arg1 ⧺ FUNCS arg2 ;
    GLOBALS = GLOBALS arg1 ⧺ GLOBALS arg2 ;
    TABLES = TABLES arg1 ⧺ TABLES arg2 ;
    MEMS = MEMS arg1 ⧺ MEMS arg2 ;
    ELEMS = ELEMS arg1 ⧺ ELEMS arg2 ;
    DATAS = DATAS arg1 ⧺ DATAS arg2 ;
    EXPORTS = EXPORTS arg1 ⧺ EXPORTS arg2 } }

instance
  inh-moduleinst : Inhabited moduleinst
  inh-moduleinst = record { default-val = record { TYPES = default-val ; FUNCS = default-val ; GLOBALS = default-val ; TABLES = default-val ; MEMS = default-val ; ELEMS = default-val ; DATAS = default-val ; EXPORTS = default-val } }

{- Record Creation Definition at: ../specification/wasm-2.0/4-runtime.spectec:60.1-63.16 -}
record funcinst : Set where
  constructor mk-funcinst
  field
    funcinst-TYPE : functype
    funcinst-MODULE : moduleinst
    CODE : func
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

{- Record Creation Definition at: ../specification/wasm-2.0/4-runtime.spectec:64.1-66.16 -}
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

{- Record Creation Definition at: ../specification/wasm-2.0/4-runtime.spectec:67.1-69.16 -}
record tableinst : Set where
  constructor mk-tableinst
  field
    tableinst-TYPE : tabletype
    REFS : (List ref)
open tableinst

instance
  append-tableinst : HasAppend (tableinst)
  append-tableinst = record { append = λ arg1 arg2 → record {
    tableinst-TYPE = tableinst-TYPE arg1 {- FIXME - Non-trivial append -} ;
    REFS = REFS arg1 ⧺ REFS arg2 } }

instance
  inh-tableinst : Inhabited tableinst
  inh-tableinst = record { default-val = record { tableinst-TYPE = default-val ; REFS = default-val } }

{- Record Creation Definition at: ../specification/wasm-2.0/4-runtime.spectec:70.1-72.18 -}
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

{- Record Creation Definition at: ../specification/wasm-2.0/4-runtime.spectec:73.1-75.16 -}
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

{- Record Creation Definition at: ../specification/wasm-2.0/4-runtime.spectec:76.1-77.18 -}
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

{- Record Creation Definition at: ../specification/wasm-2.0/4-runtime.spectec:104.1-110.22 -}
record store : Set where
  constructor mk-store
  field
    store-FUNCS : (List funcinst)
    store-GLOBALS : (List globalinst)
    store-TABLES : (List tableinst)
    store-MEMS : (List meminst)
    store-ELEMS : (List eleminst)
    store-DATAS : (List datainst)
open store

instance
  append-store : HasAppend (store)
  append-store = record { append = λ arg1 arg2 → record {
    store-FUNCS = store-FUNCS arg1 ⧺ store-FUNCS arg2 ;
    store-GLOBALS = store-GLOBALS arg1 ⧺ store-GLOBALS arg2 ;
    store-TABLES = store-TABLES arg1 ⧺ store-TABLES arg2 ;
    store-MEMS = store-MEMS arg1 ⧺ store-MEMS arg2 ;
    store-ELEMS = store-ELEMS arg1 ⧺ store-ELEMS arg2 ;
    store-DATAS = store-DATAS arg1 ⧺ store-DATAS arg2 } }

instance
  inh-store : Inhabited store
  inh-store = record { default-val = record { store-FUNCS = default-val ; store-GLOBALS = default-val ; store-TABLES = default-val ; store-MEMS = default-val ; store-ELEMS = default-val ; store-DATAS = default-val } }

{- Record Creation Definition at: ../specification/wasm-2.0/4-runtime.spectec:112.1-114.24 -}
record frame : Set where
  constructor mk-frame
  field
    LOCALS : (List val)
    frame-MODULE : moduleinst
open frame

instance
  append-frame : HasAppend (frame)
  append-frame = record { append = λ arg1 arg2 → record {
    LOCALS = LOCALS arg1 ⧺ LOCALS arg2 ;
    frame-MODULE = frame-MODULE arg1 ⧺ frame-MODULE arg2 } }

instance
  inh-frame : Inhabited frame
  inh-frame = record { default-val = record { LOCALS = default-val ; frame-MODULE = default-val } }

{- Inductive Type Definition at: ../specification/wasm-2.0/4-runtime.spectec:116.1-116.47 -}
data state : Set where
  mk-state : (v-store : store) → (v-frame : frame) → state

instance
  inh-state : Inhabited state
  inh-state = record { default-val = (mk-state (default-val) (default-val)) }

{- Inductive Type Definition at: ../specification/wasm-2.0/4-runtime.spectec:128.1-135.9 -}
data admininstr : Set where
  admininstr-NOP : admininstr
  admininstr-UNREACHABLE : admininstr
  admininstr-DROP : admininstr
  admininstr-SELECT : (valtype-lst-opt : (Maybe (List valtype))) → admininstr
  admininstr-BLOCK : (v-blocktype : blocktype) → (instr-lst : (List instr)) → admininstr
  admininstr-LOOP : (v-blocktype : blocktype) → (instr-lst : (List instr)) → admininstr
  admininstr-IFELSE : (v-blocktype : blocktype) → (instr-lst : (List instr)) → (instr-lst : (List instr)) → admininstr
  admininstr-BR : (v-labelidx : labelidx) → admininstr
  admininstr-BR-IF : (v-labelidx : labelidx) → admininstr
  admininstr-BR-TABLE : (labelidx-lst : (List labelidx)) → (v-labelidx : labelidx) → admininstr
  admininstr-CALL : (v-funcidx : funcidx) → admininstr
  admininstr-CALL-INDIRECT : (v-tableidx : tableidx) → (v-typeidx : typeidx) → admininstr
  admininstr-RETURN : admininstr
  admininstr-CONST : (v-numtype : numtype) → (_ : (num- v-numtype)) → admininstr
  admininstr-UNOP : (v-numtype : numtype) → (_ : (unop- v-numtype)) → admininstr
  admininstr-BINOP : (v-numtype : numtype) → (_ : (binop- v-numtype)) → admininstr
  admininstr-TESTOP : (v-numtype : numtype) → (_ : (testop- v-numtype)) → admininstr
  admininstr-RELOP : (v-numtype : numtype) → (_ : (relop- v-numtype)) → admininstr
  admininstr-CVTOP : (numtype-1 : numtype) → (numtype-2 : numtype) → (v-cvtop : cvtop) → admininstr {- 1 premise(s) dropped -}
  admininstr-EXTEND : (v-numtype : numtype) → (v-n : n) → admininstr
  admininstr-VCONST : (v-vectype : vectype) → (_ : (uN-fam0 ((unwrap! (size (valtype-vectype v-vectype)))))) → admininstr
  admininstr-VVUNOP : (v-vectype : vectype) → (v-vvunop : vvunop) → admininstr
  admininstr-VVBINOP : (v-vectype : vectype) → (v-vvbinop : vvbinop) → admininstr
  admininstr-VVTERNOP : (v-vectype : vectype) → (v-vvternop : vvternop) → admininstr
  admininstr-VVTESTOP : (v-vectype : vectype) → (v-vvtestop : vvtestop) → admininstr
  admininstr-VUNOP : (v-shape : shape) → (_ : (vunop- v-shape)) → admininstr
  admininstr-VBINOP : (v-shape : shape) → (_ : (vbinop- v-shape)) → admininstr
  admininstr-VTESTOP : (v-shape : shape) → (_ : (vtestop- v-shape)) → admininstr
  admininstr-VRELOP : (v-shape : shape) → (_ : (vrelop- v-shape)) → admininstr
  admininstr-VSHIFTOP : (v-ishape : ishape) → (_ : (vshiftop- v-ishape)) → admininstr
  admininstr-VBITMASK : (v-ishape : ishape) → admininstr
  admininstr-VSWIZZLE : (v-ishape : ishape) → admininstr {- 1 premise(s) dropped -}
  admininstr-VSHUFFLE : (v-ishape : ishape) → (laneidx-lst : (List laneidx)) → admininstr {- 1 premise(s) dropped -}
  admininstr-VSPLAT : (v-shape : shape) → admininstr
  admininstr-VEXTRACT-LANE : (v-shape : shape) → (sx-opt : (Maybe sx)) → (v-laneidx : laneidx) → admininstr {- 1 premise(s) dropped -}
  admininstr-VREPLACE-LANE : (v-shape : shape) → (v-laneidx : laneidx) → admininstr
  admininstr-VEXTUNOP : (ishape-1 : ishape) → (ishape-2 : ishape) → (_ : (vextunop- ishape-1)) → admininstr {- 1 premise(s) dropped -}
  admininstr-VEXTBINOP : (ishape-1 : ishape) → (ishape-2 : ishape) → (_ : (vextbinop- ishape-1)) → admininstr {- 1 premise(s) dropped -}
  admininstr-VNARROW : (ishape-1 : ishape) → (ishape-2 : ishape) → (v-sx : sx) → admininstr {- 1 premise(s) dropped -}
  admininstr-VCVTOP : (v-shape : shape) → (v-shape : shape) → (v-vcvtop : vcvtop) → admininstr
  admininstr-REF-NULL : (v-reftype : reftype) → admininstr
  admininstr-REF-FUNC : (v-funcidx : funcidx) → admininstr
  admininstr-REF-IS-NULL : admininstr
  admininstr-LOCAL-GET : (v-localidx : localidx) → admininstr
  admininstr-LOCAL-SET : (v-localidx : localidx) → admininstr
  admininstr-LOCAL-TEE : (v-localidx : localidx) → admininstr
  admininstr-GLOBAL-GET : (v-globalidx : globalidx) → admininstr
  admininstr-GLOBAL-SET : (v-globalidx : globalidx) → admininstr
  admininstr-TABLE-GET : (v-tableidx : tableidx) → admininstr
  admininstr-TABLE-SET : (v-tableidx : tableidx) → admininstr
  admininstr-TABLE-SIZE : (v-tableidx : tableidx) → admininstr
  admininstr-TABLE-GROW : (v-tableidx : tableidx) → admininstr
  admininstr-TABLE-FILL : (v-tableidx : tableidx) → admininstr
  admininstr-TABLE-COPY : (v-tableidx : tableidx) → (v-tableidx : tableidx) → admininstr
  admininstr-TABLE-INIT : (v-tableidx : tableidx) → (v-elemidx : elemidx) → admininstr
  admininstr-ELEM-DROP : (v-elemidx : elemidx) → admininstr
  admininstr-LOAD : (v-numtype : numtype) → (_ : (Maybe (loadop- v-numtype))) → (v-memarg : memarg) → admininstr
  admininstr-STORE : (v-numtype : numtype) → (sz-opt : (Maybe sz)) → (v-memarg : memarg) → admininstr {- 1 premise(s) dropped -}
  admininstr-VLOAD : (v-vectype : vectype) → (vloadop-opt : (Maybe vloadop)) → (v-memarg : memarg) → admininstr
  admininstr-VLOAD-LANE : (v-vectype : vectype) → (v-sz : sz) → (v-memarg : memarg) → (v-laneidx : laneidx) → admininstr
  admininstr-VSTORE : (v-vectype : vectype) → (v-memarg : memarg) → admininstr
  admininstr-VSTORE-LANE : (v-vectype : vectype) → (v-sz : sz) → (v-memarg : memarg) → (v-laneidx : laneidx) → admininstr
  admininstr-MEMORY-SIZE : admininstr
  admininstr-MEMORY-GROW : admininstr
  admininstr-MEMORY-FILL : admininstr
  admininstr-MEMORY-COPY : admininstr
  admininstr-MEMORY-INIT : (v-dataidx : dataidx) → admininstr
  admininstr-DATA-DROP : (v-dataidx : dataidx) → admininstr
  admininstr-REF-FUNC-ADDR : (v-funcaddr : funcaddr) → admininstr
  admininstr-REF-HOST-ADDR : (v-hostaddr : hostaddr) → admininstr
  CALL-ADDR : (v-funcaddr : funcaddr) → admininstr
  LABEL- : (v-n : n) → (instr-lst : (List instr)) → (admininstr-lst : (List admininstr)) → admininstr
  FRAME- : (v-n : n) → (v-frame : frame) → (admininstr-lst : (List admininstr)) → admininstr
  admininstr-TRAP : admininstr

instance
  inh-admininstr : Inhabited admininstr
  inh-admininstr = record { default-val = admininstr-NOP }

{- Auxiliary Definition at:  -}
{-# TERMINATING #-}
admininstr-instr : (var-0 : instr) → admininstr
admininstr-instr NOP = admininstr-NOP
admininstr-instr UNREACHABLE = admininstr-UNREACHABLE
admininstr-instr DROP = admininstr-DROP
admininstr-instr (SELECT x0) = (admininstr-SELECT x0)
admininstr-instr (BLOCK x0 x1) = (admininstr-BLOCK x0 x1)
admininstr-instr (LOOP x0 x1) = (admininstr-LOOP x0 x1)
admininstr-instr (IFELSE x0 x1 x2) = (admininstr-IFELSE x0 x1 x2)
admininstr-instr (BR x0) = (admininstr-BR x0)
admininstr-instr (BR-IF x0) = (admininstr-BR-IF x0)
admininstr-instr (BR-TABLE x0 x1) = (admininstr-BR-TABLE x0 x1)
admininstr-instr (CALL x0) = (admininstr-CALL x0)
admininstr-instr (CALL-INDIRECT x0 x1) = (admininstr-CALL-INDIRECT x0 x1)
admininstr-instr RETURN = admininstr-RETURN
admininstr-instr (CONST x0 x1) = (admininstr-CONST x0 x1)
admininstr-instr (UNOP x0 x1) = (admininstr-UNOP x0 x1)
admininstr-instr (BINOP x0 x1) = (admininstr-BINOP x0 x1)
admininstr-instr (TESTOP x0 x1) = (admininstr-TESTOP x0 x1)
admininstr-instr (RELOP x0 x1) = (admininstr-RELOP x0 x1)
admininstr-instr (CVTOP x0 x1 x2) = (admininstr-CVTOP x0 x1 x2)
admininstr-instr (instr-EXTEND x0 x1) = (admininstr-EXTEND x0 x1)
admininstr-instr (VCONST x0 x1) = (admininstr-VCONST x0 x1)
admininstr-instr (VVUNOP x0 x1) = (admininstr-VVUNOP x0 x1)
admininstr-instr (VVBINOP x0 x1) = (admininstr-VVBINOP x0 x1)
admininstr-instr (VVTERNOP x0 x1) = (admininstr-VVTERNOP x0 x1)
admininstr-instr (VVTESTOP x0 x1) = (admininstr-VVTESTOP x0 x1)
admininstr-instr (VUNOP x0 x1) = (admininstr-VUNOP x0 x1)
admininstr-instr (VBINOP x0 x1) = (admininstr-VBINOP x0 x1)
admininstr-instr (VTESTOP x0 x1) = (admininstr-VTESTOP x0 x1)
admininstr-instr (VRELOP x0 x1) = (admininstr-VRELOP x0 x1)
admininstr-instr (VSHIFTOP x0 x1) = (admininstr-VSHIFTOP x0 x1)
admininstr-instr (VBITMASK x0) = (admininstr-VBITMASK x0)
admininstr-instr (VSWIZZLE x0) = (admininstr-VSWIZZLE x0)
admininstr-instr (VSHUFFLE x0 x1) = (admininstr-VSHUFFLE x0 x1)
admininstr-instr (VSPLAT x0) = (admininstr-VSPLAT x0)
admininstr-instr (VEXTRACT-LANE x0 x1 x2) = (admininstr-VEXTRACT-LANE x0 x1 x2)
admininstr-instr (VREPLACE-LANE x0 x1) = (admininstr-VREPLACE-LANE x0 x1)
admininstr-instr (VEXTUNOP x0 x1 x2) = (admininstr-VEXTUNOP x0 x1 x2)
admininstr-instr (VEXTBINOP x0 x1 x2) = (admininstr-VEXTBINOP x0 x1 x2)
admininstr-instr (VNARROW x0 x1 x2) = (admininstr-VNARROW x0 x1 x2)
admininstr-instr (VCVTOP x0 x1 x2) = (admininstr-VCVTOP x0 x1 x2)
admininstr-instr (REF-NULL x0) = (admininstr-REF-NULL x0)
admininstr-instr (REF-FUNC x0) = (admininstr-REF-FUNC x0)
admininstr-instr REF-IS-NULL = admininstr-REF-IS-NULL
admininstr-instr (LOCAL-GET x0) = (admininstr-LOCAL-GET x0)
admininstr-instr (LOCAL-SET x0) = (admininstr-LOCAL-SET x0)
admininstr-instr (LOCAL-TEE x0) = (admininstr-LOCAL-TEE x0)
admininstr-instr (GLOBAL-GET x0) = (admininstr-GLOBAL-GET x0)
admininstr-instr (GLOBAL-SET x0) = (admininstr-GLOBAL-SET x0)
admininstr-instr (TABLE-GET x0) = (admininstr-TABLE-GET x0)
admininstr-instr (TABLE-SET x0) = (admininstr-TABLE-SET x0)
admininstr-instr (TABLE-SIZE x0) = (admininstr-TABLE-SIZE x0)
admininstr-instr (TABLE-GROW x0) = (admininstr-TABLE-GROW x0)
admininstr-instr (TABLE-FILL x0) = (admininstr-TABLE-FILL x0)
admininstr-instr (TABLE-COPY x0 x1) = (admininstr-TABLE-COPY x0 x1)
admininstr-instr (TABLE-INIT x0 x1) = (admininstr-TABLE-INIT x0 x1)
admininstr-instr (ELEM-DROP x0) = (admininstr-ELEM-DROP x0)
admininstr-instr (LOAD x0 x1 x2) = (admininstr-LOAD x0 x1 x2)
admininstr-instr (STORE x0 x1 x2) = (admininstr-STORE x0 x1 x2)
admininstr-instr (VLOAD x0 x1 x2) = (admininstr-VLOAD x0 x1 x2)
admininstr-instr (VLOAD-LANE x0 x1 x2 x3) = (admininstr-VLOAD-LANE x0 x1 x2 x3)
admininstr-instr (VSTORE x0 x1) = (admininstr-VSTORE x0 x1)
admininstr-instr (VSTORE-LANE x0 x1 x2 x3) = (admininstr-VSTORE-LANE x0 x1 x2 x3)
admininstr-instr MEMORY-SIZE = admininstr-MEMORY-SIZE
admininstr-instr MEMORY-GROW = admininstr-MEMORY-GROW
admininstr-instr MEMORY-FILL = admininstr-MEMORY-FILL
admininstr-instr MEMORY-COPY = admininstr-MEMORY-COPY
admininstr-instr (MEMORY-INIT x0) = (admininstr-MEMORY-INIT x0)
admininstr-instr (DATA-DROP x0) = (admininstr-DATA-DROP x0)
admininstr-instr var-0 = default-val

{- Auxiliary Definition at:  -}
{-# TERMINATING #-}
admininstr-ref : (var-0 : ref) → admininstr
admininstr-ref (ref-REF-NULL x0) = (admininstr-REF-NULL x0)
admininstr-ref (REF-FUNC-ADDR x0) = (admininstr-REF-FUNC-ADDR x0)
admininstr-ref (REF-HOST-ADDR x0) = (admininstr-REF-HOST-ADDR x0)
admininstr-ref var-0 = default-val

{- Auxiliary Definition at:  -}
{-# TERMINATING #-}
admininstr-val : (var-0 : val) → admininstr
admininstr-val (val-CONST x0 x1) = (admininstr-CONST x0 x1)
admininstr-val (val-VCONST x0 x1) = (admininstr-VCONST x0 x1)
admininstr-val (val-REF-NULL x0) = (admininstr-REF-NULL x0)
admininstr-val (val-REF-FUNC-ADDR x0) = (admininstr-REF-FUNC-ADDR x0)
admininstr-val (val-REF-HOST-ADDR x0) = (admininstr-REF-HOST-ADDR x0)
admininstr-val var-0 = default-val

{- Inductive Type Definition at: ../specification/wasm-2.0/4-runtime.spectec:117.1-117.62 -}
data config : Set where
  mk-config : (v-state : state) → (admininstr-lst : (List admininstr)) → config

{- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:7.1-7.43 -}
{-# TERMINATING #-}
default- : (v-valtype : valtype) → (Maybe val)
default- valtype-I32 = (just (val-CONST I32 (mk-uN 0)))
default- valtype-I64 = (just (val-CONST I64 (mk-uN 0)))
default- valtype-F32 = (just (val-CONST F32 (fzero 32)))
default- valtype-F64 = (just (val-CONST F64 (fzero 64)))
default- valtype-V128 = (just (val-VCONST V128 (mk-uN 0)))
default- valtype-FUNCREF = (just (val-REF-NULL FUNCREF))
default- valtype-EXTERNREF = (just (val-REF-NULL EXTERNREF))
default- x0 = nothing

{- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:20.1-20.63 -}
{-# TERMINATING #-}
funcsxa : (var-0-lst : (List externaddr)) → (List funcaddr)
funcsxa [] = []
funcsxa ((externaddr-FUNC fa) ∷ xv-lst) = ((fa ∷ []) ++ (funcsxa xv-lst))
funcsxa (v-externaddr ∷ xv-lst) = (funcsxa xv-lst)
funcsxa var-0-lst = []

{- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:21.1-21.65 -}
{-# TERMINATING #-}
globalsxa : (var-0-lst : (List externaddr)) → (List globaladdr)
globalsxa [] = []
globalsxa ((externaddr-GLOBAL ga) ∷ xv-lst) = ((ga ∷ []) ++ (globalsxa xv-lst))
globalsxa (v-externaddr ∷ xv-lst) = (globalsxa xv-lst)
globalsxa var-0-lst = []

{- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:22.1-22.64 -}
{-# TERMINATING #-}
tablesxa : (var-0-lst : (List externaddr)) → (List tableaddr)
tablesxa [] = []
tablesxa ((externaddr-TABLE ta) ∷ xv-lst) = ((ta ∷ []) ++ (tablesxa xv-lst))
tablesxa (v-externaddr ∷ xv-lst) = (tablesxa xv-lst)
tablesxa var-0-lst = []

{- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:23.1-23.62 -}
{-# TERMINATING #-}
memsxa : (var-0-lst : (List externaddr)) → (List memaddr)
memsxa [] = []
memsxa ((externaddr-MEM ma) ∷ xv-lst) = ((ma ∷ []) ++ (memsxa xv-lst))
memsxa (v-externaddr ∷ xv-lst) = (memsxa xv-lst)
memsxa var-0-lst = []

{- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:48.1-48.57 -}
{-# TERMINATING #-}
fun-store : (v-state : state) → store
fun-store (mk-state s f) = s
fun-store v-state = default-val

{- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:49.1-49.57 -}
{-# TERMINATING #-}
fun-frame : (v-state : state) → frame
fun-frame (mk-state s f) = f
fun-frame v-state = default-val

{- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:55.1-55.64 -}
{-# TERMINATING #-}
fun-funcaddr : (v-state : state) → (List funcaddr)
fun-funcaddr (mk-state s f) = (FUNCS (frame-MODULE f))
fun-funcaddr v-state = []

{- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:58.1-58.57 -}
{-# TERMINATING #-}
fun-funcinst : (v-state : state) → (List funcinst)
fun-funcinst (mk-state s f) = (store-FUNCS s)
fun-funcinst v-state = []

{- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:59.1-59.59 -}
{-# TERMINATING #-}
fun-globalinst : (v-state : state) → (List globalinst)
fun-globalinst (mk-state s f) = (store-GLOBALS s)
fun-globalinst v-state = []

{- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:60.1-60.58 -}
{-# TERMINATING #-}
fun-tableinst : (v-state : state) → (List tableinst)
fun-tableinst (mk-state s f) = (store-TABLES s)
fun-tableinst v-state = []

{- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:61.1-61.56 -}
{-# TERMINATING #-}
fun-meminst : (v-state : state) → (List meminst)
fun-meminst (mk-state s f) = (store-MEMS s)
fun-meminst v-state = []

{- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:62.1-62.57 -}
{-# TERMINATING #-}
fun-eleminst : (v-state : state) → (List eleminst)
fun-eleminst (mk-state s f) = (store-ELEMS s)
fun-eleminst v-state = []

{- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:63.1-63.57 -}
{-# TERMINATING #-}
fun-datainst : (v-state : state) → (List datainst)
fun-datainst (mk-state s f) = (store-DATAS s)
fun-datainst v-state = []

{- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:64.1-64.58 -}
{-# TERMINATING #-}
fun-moduleinst : (v-state : state) → moduleinst
fun-moduleinst (mk-state s f) = (frame-MODULE f)
fun-moduleinst v-state = default-val

{- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:74.1-74.66 -}
{-# TERMINATING #-}
fun-type : (v-state : state) (v-typeidx : typeidx) → functype
fun-type (mk-state s f) x = ((TYPES (frame-MODULE f)) [ (proj-uN-0 32 x) ]!)
fun-type v-state v-typeidx = default-val

{- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:75.1-75.66 -}
{-# TERMINATING #-}
fun-func : (v-state : state) (v-funcidx : funcidx) → funcinst
fun-func (mk-state s f) x = ((store-FUNCS s) [ ((FUNCS (frame-MODULE f)) [ (proj-uN-0 32 x) ]!) ]!)
fun-func v-state v-funcidx = default-val

{- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:76.1-76.68 -}
{-# TERMINATING #-}
fun-global : (v-state : state) (v-globalidx : globalidx) → globalinst
fun-global (mk-state s f) x = ((store-GLOBALS s) [ ((GLOBALS (frame-MODULE f)) [ (proj-uN-0 32 x) ]!) ]!)
fun-global v-state v-globalidx = default-val

{- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:77.1-77.67 -}
{-# TERMINATING #-}
fun-table : (v-state : state) (v-tableidx : tableidx) → tableinst
fun-table (mk-state s f) x = ((store-TABLES s) [ ((TABLES (frame-MODULE f)) [ (proj-uN-0 32 x) ]!) ]!)
fun-table v-state v-tableidx = default-val

{- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:78.1-78.65 -}
{-# TERMINATING #-}
fun-mem : (v-state : state) (v-memidx : memidx) → meminst
fun-mem (mk-state s f) x = ((store-MEMS s) [ ((MEMS (frame-MODULE f)) [ (proj-uN-0 32 x) ]!) ]!)
fun-mem v-state v-memidx = default-val

{- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:79.1-79.66 -}
{-# TERMINATING #-}
fun-elem : (v-state : state) (v-tableidx : tableidx) → eleminst
fun-elem (mk-state s f) x = ((store-ELEMS s) [ ((ELEMS (frame-MODULE f)) [ (proj-uN-0 32 x) ]!) ]!)
fun-elem v-state v-tableidx = default-val

{- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:80.1-80.66 -}
{-# TERMINATING #-}
fun-data : (v-state : state) (v-dataidx : dataidx) → datainst
fun-data (mk-state s f) x = ((store-DATAS s) [ ((DATAS (frame-MODULE f)) [ (proj-uN-0 32 x) ]!) ]!)
fun-data v-state v-dataidx = default-val

{- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:81.1-81.67 -}
{-# TERMINATING #-}
fun-local : (v-state : state) (v-localidx : localidx) → val
fun-local (mk-state s f) x = ((LOCALS f) [ (proj-uN-0 32 x) ]!)
fun-local v-state v-localidx = default-val

{- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:95.1-95.89 -}
{-# TERMINATING #-}
with-local : (v-state : state) (v-localidx : localidx) (v-val : val) → state
with-local (mk-state s f) x v = (mk-state s (record f { LOCALS = (modify (LOCALS f) (proj-uN-0 32 x) (λ (_ : val) → v)) }))
with-local v-state v-localidx v-val = default-val

{- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:96.1-96.96 -}
{-# TERMINATING #-}
with-global : (v-state : state) (v-globalidx : globalidx) (v-val : val) → state
with-global (mk-state s f) x v = (mk-state (record s { store-GLOBALS = (modify (store-GLOBALS s) ((GLOBALS (frame-MODULE f)) [ (proj-uN-0 32 x) ]!) (λ (var-1 : globalinst) → (record var-1 { VALUE = v }))) }) f)
with-global v-state v-globalidx v-val = default-val

{- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:97.1-97.97 -}
{-# TERMINATING #-}
with-table : (v-state : state) (v-tableidx : tableidx) (nat : ℕ) (v-ref : ref) → state
with-table (mk-state s f) x i r = (mk-state (record s { store-TABLES = (modify (store-TABLES s) ((TABLES (frame-MODULE f)) [ (proj-uN-0 32 x) ]!) (λ (var-1 : tableinst) → (record var-1 { REFS = (modify (REFS var-1) i (λ (_ : ref) → r)) }))) }) f)
with-table v-state v-tableidx nat v-ref = default-val

{- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:98.1-98.89 -}
{-# TERMINATING #-}
with-tableinst : (v-state : state) (v-tableidx : tableidx) (v-tableinst : tableinst) → state
with-tableinst (mk-state s f) x ti = (mk-state (record s { store-TABLES = (modify (store-TABLES s) ((TABLES (frame-MODULE f)) [ (proj-uN-0 32 x) ]!) (λ (_ : tableinst) → ti)) }) f)
with-tableinst v-state v-tableidx v-tableinst = default-val

{- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:99.1-99.100 -}
{-# TERMINATING #-}
with-mem : (v-state : state) (v-memidx : memidx) (nat : ℕ) (nat-0 : ℕ) (var-0-lst : (List byte)) → state
with-mem (mk-state s f) x i j b-lst = (mk-state (record s { store-MEMS = (modify (store-MEMS s) ((MEMS (frame-MODULE f)) [ (proj-uN-0 32 x) ]!) (λ (var-1 : meminst) → (record var-1 { BYTES = (slice-update (BYTES var-1) i j b-lst) }))) }) f)
with-mem v-state v-memidx nat nat-0 var-0-lst = default-val

{- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:100.1-100.87 -}
{-# TERMINATING #-}
with-meminst : (v-state : state) (v-memidx : memidx) (v-meminst : meminst) → state
with-meminst (mk-state s f) x mi = (mk-state (record s { store-MEMS = (modify (store-MEMS s) ((MEMS (frame-MODULE f)) [ (proj-uN-0 32 x) ]!) (λ (_ : meminst) → mi)) }) f)
with-meminst v-state v-memidx v-meminst = default-val

{- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:101.1-101.93 -}
{-# TERMINATING #-}
with-elem : (v-state : state) (v-elemidx : elemidx) (var-0-lst : (List ref)) → state
with-elem (mk-state s f) x r-lst = (mk-state (record s { store-ELEMS = (modify (store-ELEMS s) ((ELEMS (frame-MODULE f)) [ (proj-uN-0 32 x) ]!) (λ (var-1 : eleminst) → (record var-1 { eleminst-REFS = r-lst }))) }) f)
with-elem v-state v-elemidx var-0-lst = default-val

{- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:102.1-102.94 -}
{-# TERMINATING #-}
with-data : (v-state : state) (v-dataidx : dataidx) (var-0-lst : (List byte)) → state
with-data (mk-state s f) x b-lst = (mk-state (record s { store-DATAS = (modify (store-DATAS s) ((DATAS (frame-MODULE f)) [ (proj-uN-0 32 x) ]!) (λ (var-1 : datainst) → (record var-1 { datainst-BYTES = b-lst }))) }) f)
with-data v-state v-dataidx var-0-lst = default-val

{- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:116.1-116.62 -}
postulate growtable : ∀ (v-tableinst : tableinst) (nat : ℕ) (v-ref : ref) → (Maybe tableinst)

{- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:117.1-117.62 -}
postulate growmemory : ∀ (v-meminst : meminst) (nat : ℕ) → (Maybe meminst)

{- Record Creation Definition at: ../specification/wasm-2.0/6-typing.spectec:5.1-9.62 -}
record context : Set where
  constructor mk-context
  field
    context-TYPES : (List functype)
    context-FUNCS : (List functype)
    context-GLOBALS : (List globaltype)
    context-TABLES : (List tabletype)
    context-MEMS : (List memtype)
    context-ELEMS : (List elemtype)
    context-DATAS : (List datatype)
    context-LOCALS : (List valtype)
    LABELS : (List resulttype)
    context-RETURN : (Maybe resulttype)
open context

instance
  append-context : HasAppend (context)
  append-context = record { append = λ arg1 arg2 → record {
    context-TYPES = context-TYPES arg1 ⧺ context-TYPES arg2 ;
    context-FUNCS = context-FUNCS arg1 ⧺ context-FUNCS arg2 ;
    context-GLOBALS = context-GLOBALS arg1 ⧺ context-GLOBALS arg2 ;
    context-TABLES = context-TABLES arg1 ⧺ context-TABLES arg2 ;
    context-MEMS = context-MEMS arg1 ⧺ context-MEMS arg2 ;
    context-ELEMS = context-ELEMS arg1 ⧺ context-ELEMS arg2 ;
    context-DATAS = context-DATAS arg1 ⧺ context-DATAS arg2 ;
    context-LOCALS = context-LOCALS arg1 ⧺ context-LOCALS arg2 ;
    LABELS = LABELS arg1 ⧺ LABELS arg2 ;
    context-RETURN = context-RETURN arg1 ⧺ context-RETURN arg2 } }

{- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:19.1-19.66 -}
data Limits-ok : limits → ℕ → Set where
  mk-Limits-ok : ∀ (v-n : n) (m-opt : (Maybe m)) (k : ℕ) → 
    (v-n ≤ k) →
    Forall (λ (v-m : ℕ) → ((v-n ≤ v-m) × (v-m ≤ k))) (fromMaybe m-opt) →
    Limits-ok (mk-limits (mk-uN v-n) (mapMaybe (λ (v-m : ℕ) → (mk-uN v-m)) m-opt)) k

{- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:20.1-20.64 -}
data Functype-ok : functype → Set where
  mk-Functype-ok : ∀ (t-1-lst : (List valtype)) (t-2-lst : (List valtype)) → Functype-ok (mk-functype (mk-list t-1-lst) (mk-list t-2-lst))

{- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:21.1-21.66 -}
data Globaltype-ok : globaltype → Set where
  mk-Globaltype-ok : ∀ (t : valtype) → Globaltype-ok (mk-globaltype (just MUT) t)

{- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:22.1-22.65 -}
data Tabletype-ok : tabletype → Set where
  mk-Tabletype-ok : ∀ (v-limits : limits) (v-reftype : reftype) → 
    (Limits-ok v-limits (coerce {B = ℕ} ((coerce {B = ℕ} (2 ^ 32)) – (coerce {B = ℕ} 1)))) →
    Tabletype-ok (mk-tabletype v-limits v-reftype)

{- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:23.1-23.63 -}
data Memtype-ok : memtype → Set where
  mk-Memtype-ok : ∀ (v-limits : limits) → 
    (Limits-ok v-limits (2 ^ 16)) →
    Memtype-ok (PAGE v-limits)

{- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:24.1-24.66 -}
data Externtype-ok : externtype → Set where
  Externtype-ok--func : ∀ (v-functype : functype) → 
    (Functype-ok v-functype) →
    Externtype-ok (FUNC v-functype)
  Externtype-ok--global : ∀ (v-globaltype : globaltype) → 
    (Globaltype-ok v-globaltype) →
    Externtype-ok (GLOBAL v-globaltype)
  Externtype-ok--table : ∀ (v-tabletype : tabletype) → 
    (Tabletype-ok v-tabletype) →
    Externtype-ok (TABLE v-tabletype)
  Externtype-ok--mem : ∀ (v-memtype : memtype) → 
    (Memtype-ok v-memtype) →
    Externtype-ok (MEM v-memtype)

{- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:71.1-71.69 -}
data Valtype-sub : valtype → valtype → Set where
  refl' : ∀ (t : valtype) → Valtype-sub t t
  bot : ∀ (t : valtype) → Valtype-sub BOT t

{- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:72.1-72.76 -}
data Resulttype-sub : resulttype → resulttype → Set where
  mk-Resulttype-sub : ∀ (t-1-lst : (List valtype)) (t-2-lst : (List valtype)) → 
    ((length t-1-lst) ≡ (length t-2-lst)) →
    Forall₂ (λ (t-1 : valtype) (t-2 : valtype) → (Valtype-sub t-1 t-2)) t-1-lst t-2-lst →
    Resulttype-sub (mk-list t-1-lst) (mk-list t-2-lst)

{- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:87.1-87.75 -}
data Limits-sub : limits → limits → Set where
  mk-Limits-sub : ∀ (n-11 : n) (n-12 : n) (n-21 : n) (n-22 : n) → 
    (n-11 ≥ n-21) →
    (n-12 ≤ n-22) →
    Limits-sub (mk-limits (mk-uN n-11) (just (mk-uN n-12))) (mk-limits (mk-uN n-21) (just (mk-uN n-22)))

{- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:88.1-88.73 -}
data Functype-sub : functype → functype → Set where
  mk-Functype-sub : ∀ (ft : functype) → Functype-sub ft ft

{- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:89.1-89.75 -}
data Globaltype-sub : globaltype → globaltype → Set where
  mk-Globaltype-sub : ∀ (gt : globaltype) → Globaltype-sub gt gt

{- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:90.1-90.74 -}
data Tabletype-sub : tabletype → tabletype → Set where
  mk-Tabletype-sub : ∀ (lim-1 : limits) (rt : reftype) (lim-2 : limits) → 
    (Limits-sub lim-1 lim-2) →
    Tabletype-sub (mk-tabletype lim-1 rt) (mk-tabletype lim-2 rt)

{- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:91.1-91.72 -}
data Memtype-sub : memtype → memtype → Set where
  mk-Memtype-sub : ∀ (lim-1 : limits) (lim-2 : limits) → 
    (Limits-sub lim-1 lim-2) →
    Memtype-sub (PAGE lim-1) (PAGE lim-2)

{- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:92.1-92.75 -}
data Externtype-sub : externtype → externtype → Set where
  Externtype-sub--func : ∀ (ft-1 : functype) (ft-2 : functype) → 
    (Functype-sub ft-1 ft-2) →
    Externtype-sub (FUNC ft-1) (FUNC ft-2)
  Externtype-sub--global : ∀ (gt-1 : globaltype) (gt-2 : globaltype) → 
    (Globaltype-sub gt-1 gt-2) →
    Externtype-sub (GLOBAL gt-1) (GLOBAL gt-2)
  Externtype-sub--table : ∀ (tt-1 : tabletype) (tt-2 : tabletype) → 
    (Tabletype-sub tt-1 tt-2) →
    Externtype-sub (TABLE tt-1) (TABLE tt-2)
  Externtype-sub--mem : ∀ (mt-1 : memtype) (mt-2 : memtype) → 
    (Memtype-sub mt-1 mt-2) →
    Externtype-sub (MEM mt-1) (MEM mt-2)

{- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:198.1-198.76 -}
data Blocktype-ok : context → blocktype → functype → Set where
  Blocktype-ok--valtype : ∀ (C : context) (valtype-opt : (Maybe valtype)) → Blocktype-ok C (-RESULT valtype-opt) (mk-functype (mk-list []) (mk-list (fromMaybe valtype-opt)))
  Blocktype-ok--typeidx : ∀ (C : context) (v-typeidx : typeidx) (t-1-lst : (List valtype)) (t-2-lst : (List valtype)) → 
    ((proj-uN-0 32 v-typeidx) < (length (context-TYPES C))) →
    (((context-TYPES C) [ (proj-uN-0 32 v-typeidx) ]!) ≡ (mk-functype (mk-list t-1-lst) (mk-list t-2-lst))) →
    Blocktype-ok C (-IDX v-typeidx) (mk-functype (mk-list t-1-lst) (mk-list t-2-lst))

mutual
  {- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:137.1-137.64 -}
  data Instr-ok : context → instr → functype → Set where
    nop : ∀ (C : context) → Instr-ok C NOP (mk-functype (mk-list []) (mk-list []))
    unreachable : ∀ (C : context) (t-1-lst : (List valtype)) (t-2-lst : (List valtype)) → Instr-ok C UNREACHABLE (mk-functype (mk-list t-1-lst) (mk-list t-2-lst))
    drop' : ∀ (C : context) (t : valtype) → Instr-ok C DROP (mk-functype (mk-list (t ∷ [])) (mk-list []))
    select-expl : ∀ (C : context) (t : valtype) → Instr-ok C (SELECT (just (t ∷ []))) (mk-functype (mk-list (as (List valtype) (t ∷ t ∷ valtype-I32 ∷ []))) (mk-list (t ∷ [])))
    select-impl : ∀ (C : context) (t : valtype) (t' : valtype) (v-numtype : numtype) (v-vectype : vectype) → 
      (Valtype-sub t t') →
      ((t' ≡ (valtype-numtype v-numtype)) ⊎ (t' ≡ (valtype-vectype v-vectype))) →
      Instr-ok C (SELECT nothing) (mk-functype (mk-list (as (List valtype) (t ∷ t ∷ valtype-I32 ∷ []))) (mk-list (t ∷ [])))
    block : ∀ (C : context) (bt : blocktype) (instr-lst : (List instr)) (t-1-lst : (List valtype)) (t-2-lst : (List valtype)) → 
      (Blocktype-ok C bt (mk-functype (mk-list t-1-lst) (mk-list t-2-lst))) →
      (Instrs-ok (record { context-TYPES = [] ; context-FUNCS = [] ; context-GLOBALS = [] ; context-TABLES = [] ; context-MEMS = [] ; context-ELEMS = [] ; context-DATAS = [] ; context-LOCALS = [] ; LABELS = (as (List resulttype) ((mk-list t-2-lst) ∷ [])) ; context-RETURN = nothing } ⧺ C) instr-lst (mk-functype (mk-list t-1-lst) (mk-list t-2-lst))) →
      Instr-ok C (BLOCK bt instr-lst) (mk-functype (mk-list t-1-lst) (mk-list t-2-lst))
    loop : ∀ (C : context) (bt : blocktype) (instr-lst : (List instr)) (t-1-lst : (List valtype)) (t-2-lst : (List valtype)) → 
      (Blocktype-ok C bt (mk-functype (mk-list t-1-lst) (mk-list t-2-lst))) →
      (Instrs-ok (record { context-TYPES = [] ; context-FUNCS = [] ; context-GLOBALS = [] ; context-TABLES = [] ; context-MEMS = [] ; context-ELEMS = [] ; context-DATAS = [] ; context-LOCALS = [] ; LABELS = (as (List resulttype) ((mk-list t-1-lst) ∷ [])) ; context-RETURN = nothing } ⧺ C) instr-lst (mk-functype (mk-list t-1-lst) (mk-list t-2-lst))) →
      Instr-ok C (LOOP bt instr-lst) (mk-functype (mk-list t-1-lst) (mk-list t-2-lst))
    if' : ∀ (C : context) (bt : blocktype) (instr-1-lst : (List instr)) (instr-2-lst : (List instr)) (t-1-lst : (List valtype)) (t-2-lst : (List valtype)) → 
      (Blocktype-ok C bt (mk-functype (mk-list t-1-lst) (mk-list t-2-lst))) →
      (Instrs-ok (record { context-TYPES = [] ; context-FUNCS = [] ; context-GLOBALS = [] ; context-TABLES = [] ; context-MEMS = [] ; context-ELEMS = [] ; context-DATAS = [] ; context-LOCALS = [] ; LABELS = (as (List resulttype) ((mk-list t-2-lst) ∷ [])) ; context-RETURN = nothing } ⧺ C) instr-1-lst (mk-functype (mk-list t-1-lst) (mk-list t-2-lst))) →
      (Instrs-ok (record { context-TYPES = [] ; context-FUNCS = [] ; context-GLOBALS = [] ; context-TABLES = [] ; context-MEMS = [] ; context-ELEMS = [] ; context-DATAS = [] ; context-LOCALS = [] ; LABELS = (as (List resulttype) ((mk-list t-2-lst) ∷ [])) ; context-RETURN = nothing } ⧺ C) instr-2-lst (mk-functype (mk-list t-1-lst) (mk-list t-2-lst))) →
      Instr-ok C (IFELSE bt instr-1-lst instr-2-lst) (mk-functype (mk-list (t-1-lst ++ (as (List valtype) (valtype-I32 ∷ [])))) (mk-list t-2-lst))
    br : ∀ (C : context) (l : labelidx) (t-1-lst : (List valtype)) (t-lst : (List valtype)) (t-2-lst : (List valtype)) → 
      ((proj-uN-0 32 l) < (length (LABELS C))) →
      ((proj-list-0 valtype ((LABELS C) [ (proj-uN-0 32 l) ]!)) ≡ t-lst) →
      Instr-ok C (BR l) (mk-functype (mk-list (t-1-lst ++ t-lst)) (mk-list t-2-lst))
    br-if : ∀ (C : context) (l : labelidx) (t-lst : (List valtype)) → 
      ((proj-uN-0 32 l) < (length (LABELS C))) →
      ((proj-list-0 valtype ((LABELS C) [ (proj-uN-0 32 l) ]!)) ≡ t-lst) →
      Instr-ok C (BR-IF l) (mk-functype (mk-list (t-lst ++ (as (List valtype) (valtype-I32 ∷ [])))) (mk-list t-lst))
    br-table : ∀ (C : context) (l-lst : (List labelidx)) (l' : labelidx) (t-1-lst : (List valtype)) (t-lst : (List valtype)) (t-2-lst : (List valtype)) → 
      Forall (λ (l : labelidx) → ((proj-uN-0 32 l) < (length (LABELS C)))) l-lst →
      Forall (λ (l : labelidx) → (Resulttype-sub (mk-list t-lst) ((LABELS C) [ (proj-uN-0 32 l) ]!))) l-lst →
      ((proj-uN-0 32 l') < (length (LABELS C))) →
      (Resulttype-sub (mk-list t-lst) ((LABELS C) [ (proj-uN-0 32 l') ]!)) →
      Instr-ok C (BR-TABLE l-lst l') (mk-functype (mk-list (t-1-lst ++ (t-lst ++ (as (List valtype) (valtype-I32 ∷ []))))) (mk-list t-2-lst))
    call : ∀ (C : context) (x : idx) (t-1-lst : (List valtype)) (t-2-lst : (List valtype)) → 
      ((proj-uN-0 32 x) < (length (context-FUNCS C))) →
      (((context-FUNCS C) [ (proj-uN-0 32 x) ]!) ≡ (mk-functype (mk-list t-1-lst) (mk-list t-2-lst))) →
      Instr-ok C (CALL x) (mk-functype (mk-list t-1-lst) (mk-list t-2-lst))
    call-indirect : ∀ (C : context) (x : idx) (y : idx) (t-1-lst : (List valtype)) (t-2-lst : (List valtype)) (lim : limits) → 
      ((proj-uN-0 32 x) < (length (context-TABLES C))) →
      (((context-TABLES C) [ (proj-uN-0 32 x) ]!) ≡ (mk-tabletype lim FUNCREF)) →
      ((proj-uN-0 32 y) < (length (context-TYPES C))) →
      (((context-TYPES C) [ (proj-uN-0 32 y) ]!) ≡ (mk-functype (mk-list t-1-lst) (mk-list t-2-lst))) →
      Instr-ok C (CALL-INDIRECT x y) (mk-functype (mk-list (t-1-lst ++ (as (List valtype) (valtype-I32 ∷ [])))) (mk-list t-2-lst))
    return : ∀ (C : context) (t-1-lst : (List valtype)) (t-lst : (List valtype)) (t-2-lst : (List valtype)) → 
      ((context-RETURN C) ≡ (just (mk-list t-lst))) →
      Instr-ok C RETURN (mk-functype (mk-list (t-1-lst ++ t-lst)) (mk-list t-2-lst))
    const : ∀ (C : context) (nt : numtype) (c-nt : (num- nt)) → Instr-ok C (CONST nt c-nt) (mk-functype (mk-list []) (mk-list ((valtype-numtype nt) ∷ [])))
    unop : ∀ (C : context) (nt : numtype) (unop-nt : (unop- nt)) → Instr-ok C (UNOP nt unop-nt) (mk-functype (mk-list ((valtype-numtype nt) ∷ [])) (mk-list ((valtype-numtype nt) ∷ [])))
    binop : ∀ (C : context) (nt : numtype) (binop-nt : (binop- nt)) → Instr-ok C (BINOP nt binop-nt) (mk-functype (mk-list ((valtype-numtype nt) ∷ (valtype-numtype nt) ∷ [])) (mk-list ((valtype-numtype nt) ∷ [])))
    testop : ∀ (C : context) (nt : numtype) (testop-nt : (testop- nt)) → Instr-ok C (TESTOP nt testop-nt) (mk-functype (mk-list ((valtype-numtype nt) ∷ [])) (mk-list (as (List valtype) (valtype-I32 ∷ []))))
    relop : ∀ (C : context) (nt : numtype) (relop-nt : (relop- nt)) → Instr-ok C (RELOP nt relop-nt) (mk-functype (mk-list ((valtype-numtype nt) ∷ (valtype-numtype nt) ∷ [])) (mk-list (as (List valtype) (valtype-I32 ∷ []))))
    cvtop-reinterpret : ∀ (C : context) (nt-1 : numtype) (nt-2 : numtype) → 
      ((size (valtype-numtype nt-1)) ≢ nothing) →
      ((size (valtype-numtype nt-2)) ≢ nothing) →
      ((unwrap! (size (valtype-numtype nt-1))) ≡ (unwrap! (size (valtype-numtype nt-2)))) →
      Instr-ok C (CVTOP nt-1 nt-2 REINTERPRET) (mk-functype (mk-list ((valtype-numtype nt-2) ∷ [])) (mk-list ((valtype-numtype nt-1) ∷ [])))
    cvtop-convert : ∀ (C : context) (nt-1 : numtype) (nt-2 : numtype) (v-cvtop : cvtop) → Instr-ok C (CVTOP nt-1 nt-2 v-cvtop) (mk-functype (mk-list ((valtype-numtype nt-2) ∷ [])) (mk-list ((valtype-numtype nt-1) ∷ [])))
    ref-null : ∀ (C : context) (rt : reftype) → Instr-ok C (REF-NULL rt) (mk-functype (mk-list []) (mk-list ((valtype-reftype rt) ∷ [])))
    ref-func : ∀ (C : context) (x : idx) (ft : functype) → 
      ((proj-uN-0 32 x) < (length (context-FUNCS C))) →
      (((context-FUNCS C) [ (proj-uN-0 32 x) ]!) ≡ ft) →
      Instr-ok C (REF-FUNC x) (mk-functype (mk-list []) (mk-list (as (List valtype) (valtype-FUNCREF ∷ []))))
    ref-is-null : ∀ (C : context) (rt : reftype) → Instr-ok C REF-IS-NULL (mk-functype (mk-list ((valtype-reftype rt) ∷ [])) (mk-list (as (List valtype) (valtype-I32 ∷ []))))
    vconst : ∀ (C : context) (c : (uN-fam0 (128))) → Instr-ok C (VCONST V128 c) (mk-functype (mk-list []) (mk-list (as (List valtype) (valtype-V128 ∷ []))))
    Instr-ok--vvunop : ∀ (C : context) (v-vvunop : vvunop) → Instr-ok C (VVUNOP V128 v-vvunop) (mk-functype (mk-list (as (List valtype) (valtype-V128 ∷ []))) (mk-list (as (List valtype) (valtype-V128 ∷ []))))
    Instr-ok--vvbinop : ∀ (C : context) (v-vvbinop : vvbinop) → Instr-ok C (VVBINOP V128 v-vvbinop) (mk-functype (mk-list (as (List valtype) (valtype-V128 ∷ valtype-V128 ∷ []))) (mk-list (as (List valtype) (valtype-V128 ∷ []))))
    Instr-ok--vvternop : ∀ (C : context) (v-vvternop : vvternop) → Instr-ok C (VVTERNOP V128 v-vvternop) (mk-functype (mk-list (as (List valtype) (valtype-V128 ∷ valtype-V128 ∷ valtype-V128 ∷ []))) (mk-list (as (List valtype) (valtype-V128 ∷ []))))
    Instr-ok--vvtestop : ∀ (C : context) (v-vvtestop : vvtestop) → Instr-ok C (VVTESTOP V128 v-vvtestop) (mk-functype (mk-list (as (List valtype) (valtype-V128 ∷ []))) (mk-list (as (List valtype) (valtype-I32 ∷ []))))
    vunop : ∀ (C : context) (sh : shape) (vunop-sh : (vunop- sh)) → Instr-ok C (VUNOP sh vunop-sh) (mk-functype (mk-list (as (List valtype) (valtype-V128 ∷ []))) (mk-list (as (List valtype) (valtype-V128 ∷ []))))
    vbinop : ∀ (C : context) (sh : shape) (vbinop-sh : (vbinop- sh)) → Instr-ok C (VBINOP sh vbinop-sh) (mk-functype (mk-list (as (List valtype) (valtype-V128 ∷ valtype-V128 ∷ []))) (mk-list (as (List valtype) (valtype-V128 ∷ []))))
    vtestop : ∀ (C : context) (sh : shape) (vtestop-sh : (vtestop- sh)) → Instr-ok C (VTESTOP sh vtestop-sh) (mk-functype (mk-list (as (List valtype) (valtype-V128 ∷ []))) (mk-list (as (List valtype) (valtype-I32 ∷ []))))
    vrelop : ∀ (C : context) (sh : shape) (vrelop-sh : (vrelop- sh)) → Instr-ok C (VRELOP sh vrelop-sh) (mk-functype (mk-list (as (List valtype) (valtype-V128 ∷ valtype-V128 ∷ []))) (mk-list (as (List valtype) (valtype-V128 ∷ []))))
    vshiftop : ∀ (C : context) (sh : ishape) (vshiftop-sh : (vshiftop- sh)) → Instr-ok C (VSHIFTOP sh vshiftop-sh) (mk-functype (mk-list (as (List valtype) (valtype-V128 ∷ valtype-I32 ∷ []))) (mk-list (as (List valtype) (valtype-V128 ∷ []))))
    vbitmask : ∀ (C : context) (sh : ishape) → Instr-ok C (VBITMASK sh) (mk-functype (mk-list (as (List valtype) (valtype-V128 ∷ []))) (mk-list (as (List valtype) (valtype-I32 ∷ []))))
    vswizzle : ∀ (C : context) (sh : ishape) → Instr-ok C (VSWIZZLE sh) (mk-functype (mk-list (as (List valtype) (valtype-V128 ∷ valtype-V128 ∷ []))) (mk-list (as (List valtype) (valtype-V128 ∷ []))))
    vshuffle : ∀ (C : context) (sh : ishape) (i-lst : (List laneidx)) → 
      Forall (λ (i : laneidx) → ((proj-uN-0 8 i) < (2 * (coerce {B = ℕ} ((fun-dim (shape-ishape sh))))))) i-lst →
      Instr-ok C (VSHUFFLE sh i-lst) (mk-functype (mk-list (as (List valtype) (valtype-V128 ∷ valtype-V128 ∷ []))) (mk-list (as (List valtype) (valtype-V128 ∷ []))))
    vsplat : ∀ (C : context) (sh : shape) → Instr-ok C (VSPLAT sh) (mk-functype (mk-list ((valtype-numtype (shunpack sh)) ∷ [])) (mk-list (as (List valtype) (valtype-V128 ∷ []))))
    vextract-lane : ∀ (C : context) (sh : shape) (sx-opt : (Maybe sx)) (i : laneidx) → 
      ((proj-uN-0 8 i) < (coerce {B = ℕ} ((fun-dim sh)))) →
      Instr-ok C (VEXTRACT-LANE sh sx-opt i) (mk-functype (mk-list (as (List valtype) (valtype-V128 ∷ []))) (mk-list ((valtype-numtype (shunpack sh)) ∷ [])))
    vreplace-lane : ∀ (C : context) (sh : shape) (i : laneidx) → 
      ((proj-uN-0 8 i) < (coerce {B = ℕ} ((fun-dim sh)))) →
      Instr-ok C (VREPLACE-LANE sh i) (mk-functype (mk-list (as (List valtype) (valtype-V128 ∷ (valtype-numtype (shunpack sh)) ∷ []))) (mk-list (as (List valtype) (valtype-V128 ∷ []))))
    vextunop : ∀ (C : context) (sh-1 : ishape) (sh-2 : ishape) (vextunop : (vextunop- sh-1)) → Instr-ok C (VEXTUNOP sh-1 sh-2 vextunop) (mk-functype (mk-list (as (List valtype) (valtype-V128 ∷ []))) (mk-list (as (List valtype) (valtype-V128 ∷ []))))
    vextbinop : ∀ (C : context) (sh-1 : ishape) (sh-2 : ishape) (vextbinop : (vextbinop- sh-1)) → Instr-ok C (VEXTBINOP sh-1 sh-2 vextbinop) (mk-functype (mk-list (as (List valtype) (valtype-V128 ∷ valtype-V128 ∷ []))) (mk-list (as (List valtype) (valtype-V128 ∷ []))))
    vnarrow : ∀ (C : context) (sh-1 : ishape) (sh-2 : ishape) (v-sx : sx) → Instr-ok C (VNARROW sh-1 sh-2 v-sx) (mk-functype (mk-list (as (List valtype) (valtype-V128 ∷ valtype-V128 ∷ []))) (mk-list (as (List valtype) (valtype-V128 ∷ []))))
    Instr-ok--vcvtop : ∀ (C : context) (sh-1 : shape) (sh-2 : shape) (v-vcvtop : vcvtop) → Instr-ok C (VCVTOP sh-1 sh-2 v-vcvtop) (mk-functype (mk-list (as (List valtype) (valtype-V128 ∷ []))) (mk-list (as (List valtype) (valtype-V128 ∷ []))))
    local-get : ∀ (C : context) (x : idx) (t : valtype) → 
      ((proj-uN-0 32 x) < (length (context-LOCALS C))) →
      (((context-LOCALS C) [ (proj-uN-0 32 x) ]!) ≡ t) →
      Instr-ok C (LOCAL-GET x) (mk-functype (mk-list []) (mk-list (t ∷ [])))
    local-set : ∀ (C : context) (x : idx) (t : valtype) → 
      ((proj-uN-0 32 x) < (length (context-LOCALS C))) →
      (((context-LOCALS C) [ (proj-uN-0 32 x) ]!) ≡ t) →
      Instr-ok C (LOCAL-SET x) (mk-functype (mk-list (t ∷ [])) (mk-list []))
    local-tee : ∀ (C : context) (x : idx) (t : valtype) → 
      ((proj-uN-0 32 x) < (length (context-LOCALS C))) →
      (((context-LOCALS C) [ (proj-uN-0 32 x) ]!) ≡ t) →
      Instr-ok C (LOCAL-TEE x) (mk-functype (mk-list (t ∷ [])) (mk-list (t ∷ [])))
    global-get : ∀ (C : context) (x : idx) (t : valtype) (v-mut : mut) → 
      ((proj-uN-0 32 x) < (length (context-GLOBALS C))) →
      (((context-GLOBALS C) [ (proj-uN-0 32 x) ]!) ≡ (mk-globaltype v-mut t)) →
      Instr-ok C (GLOBAL-GET x) (mk-functype (mk-list []) (mk-list (t ∷ [])))
    global-set : ∀ (C : context) (x : idx) (t : valtype) → 
      ((proj-uN-0 32 x) < (length (context-GLOBALS C))) →
      (((context-GLOBALS C) [ (proj-uN-0 32 x) ]!) ≡ (mk-globaltype (just MUT) t)) →
      Instr-ok C (GLOBAL-SET x) (mk-functype (mk-list (t ∷ [])) (mk-list []))
    table-get : ∀ (C : context) (x : idx) (rt : reftype) (lim : limits) → 
      ((proj-uN-0 32 x) < (length (context-TABLES C))) →
      (((context-TABLES C) [ (proj-uN-0 32 x) ]!) ≡ (mk-tabletype lim rt)) →
      Instr-ok C (TABLE-GET x) (mk-functype (mk-list (as (List valtype) (valtype-I32 ∷ []))) (mk-list ((valtype-reftype rt) ∷ [])))
    table-set : ∀ (C : context) (x : idx) (rt : reftype) (lim : limits) → 
      ((proj-uN-0 32 x) < (length (context-TABLES C))) →
      (((context-TABLES C) [ (proj-uN-0 32 x) ]!) ≡ (mk-tabletype lim rt)) →
      Instr-ok C (TABLE-SET x) (mk-functype (mk-list (as (List valtype) (valtype-I32 ∷ (valtype-reftype rt) ∷ []))) (mk-list []))
    table-size : ∀ (C : context) (x : idx) (lim : limits) (rt : reftype) → 
      ((proj-uN-0 32 x) < (length (context-TABLES C))) →
      (((context-TABLES C) [ (proj-uN-0 32 x) ]!) ≡ (mk-tabletype lim rt)) →
      Instr-ok C (TABLE-SIZE x) (mk-functype (mk-list []) (mk-list (as (List valtype) (valtype-I32 ∷ []))))
    table-grow : ∀ (C : context) (x : idx) (rt : reftype) (lim : limits) → 
      ((proj-uN-0 32 x) < (length (context-TABLES C))) →
      (((context-TABLES C) [ (proj-uN-0 32 x) ]!) ≡ (mk-tabletype lim rt)) →
      Instr-ok C (TABLE-GROW x) (mk-functype (mk-list (as (List valtype) ((valtype-reftype rt) ∷ valtype-I32 ∷ []))) (mk-list (as (List valtype) (valtype-I32 ∷ []))))
    table-fill : ∀ (C : context) (x : idx) (rt : reftype) (lim : limits) → 
      ((proj-uN-0 32 x) < (length (context-TABLES C))) →
      (((context-TABLES C) [ (proj-uN-0 32 x) ]!) ≡ (mk-tabletype lim rt)) →
      Instr-ok C (TABLE-FILL x) (mk-functype (mk-list (as (List valtype) (valtype-I32 ∷ (valtype-reftype rt) ∷ valtype-I32 ∷ []))) (mk-list []))
    table-copy : ∀ (C : context) (x-1 : idx) (x-2 : idx) (lim-1 : limits) (rt : reftype) (lim-2 : limits) → 
      ((proj-uN-0 32 x-1) < (length (context-TABLES C))) →
      (((context-TABLES C) [ (proj-uN-0 32 x-1) ]!) ≡ (mk-tabletype lim-1 rt)) →
      ((proj-uN-0 32 x-2) < (length (context-TABLES C))) →
      (((context-TABLES C) [ (proj-uN-0 32 x-2) ]!) ≡ (mk-tabletype lim-2 rt)) →
      Instr-ok C (TABLE-COPY x-1 x-2) (mk-functype (mk-list (as (List valtype) (valtype-I32 ∷ valtype-I32 ∷ valtype-I32 ∷ []))) (mk-list []))
    table-init : ∀ (C : context) (x-1 : idx) (x-2 : idx) (lim : limits) (rt : reftype) → 
      ((proj-uN-0 32 x-1) < (length (context-TABLES C))) →
      (((context-TABLES C) [ (proj-uN-0 32 x-1) ]!) ≡ (mk-tabletype lim rt)) →
      ((proj-uN-0 32 x-2) < (length (context-ELEMS C))) →
      (((context-ELEMS C) [ (proj-uN-0 32 x-2) ]!) ≡ rt) →
      Instr-ok C (TABLE-INIT x-1 x-2) (mk-functype (mk-list (as (List valtype) (valtype-I32 ∷ valtype-I32 ∷ valtype-I32 ∷ []))) (mk-list []))
    elem-drop : ∀ (C : context) (x : idx) (rt : reftype) → 
      ((proj-uN-0 32 x) < (length (context-ELEMS C))) →
      (((context-ELEMS C) [ (proj-uN-0 32 x) ]!) ≡ rt) →
      Instr-ok C (ELEM-DROP x) (mk-functype (mk-list []) (mk-list []))
    memory-size : ∀ (C : context) (mt : memtype) → 
      (0 < (length (context-MEMS C))) →
      (((context-MEMS C) [ 0 ]!) ≡ mt) →
      Instr-ok C MEMORY-SIZE (mk-functype (mk-list []) (mk-list (as (List valtype) (valtype-I32 ∷ []))))
    memory-grow : ∀ (C : context) (mt : memtype) → 
      (0 < (length (context-MEMS C))) →
      (((context-MEMS C) [ 0 ]!) ≡ mt) →
      Instr-ok C MEMORY-GROW (mk-functype (mk-list (as (List valtype) (valtype-I32 ∷ []))) (mk-list (as (List valtype) (valtype-I32 ∷ []))))
    memory-fill : ∀ (C : context) (mt : memtype) → 
      (0 < (length (context-MEMS C))) →
      (((context-MEMS C) [ 0 ]!) ≡ mt) →
      Instr-ok C MEMORY-FILL (mk-functype (mk-list (as (List valtype) (valtype-I32 ∷ valtype-I32 ∷ valtype-I32 ∷ []))) (mk-list []))
    memory-copy : ∀ (C : context) (mt : memtype) → 
      (0 < (length (context-MEMS C))) →
      (((context-MEMS C) [ 0 ]!) ≡ mt) →
      Instr-ok C MEMORY-COPY (mk-functype (mk-list (as (List valtype) (valtype-I32 ∷ valtype-I32 ∷ valtype-I32 ∷ []))) (mk-list []))
    memory-init : ∀ (C : context) (x : idx) (mt : memtype) → 
      (0 < (length (context-MEMS C))) →
      (((context-MEMS C) [ 0 ]!) ≡ mt) →
      ((proj-uN-0 32 x) < (length (context-DATAS C))) →
      (((context-DATAS C) [ (proj-uN-0 32 x) ]!) ≡ OK) →
      Instr-ok C (MEMORY-INIT x) (mk-functype (mk-list (as (List valtype) (valtype-I32 ∷ valtype-I32 ∷ valtype-I32 ∷ []))) (mk-list []))
    data-drop : ∀ (C : context) (x : idx) → 
      ((proj-uN-0 32 x) < (length (context-DATAS C))) →
      (((context-DATAS C) [ (proj-uN-0 32 x) ]!) ≡ OK) →
      Instr-ok C (DATA-DROP x) (mk-functype (mk-list []) (mk-list []))
    load-val : ∀ (C : context) (nt : numtype) (v-memarg : memarg) (mt : memtype) → 
      (0 < (length (context-MEMS C))) →
      (((context-MEMS C) [ 0 ]!) ≡ mt) →
      ((size (valtype-numtype nt)) ≢ nothing) →
      ((coerce {B = ℕ} (2 ^ (proj-uN-0 32 (ALIGN v-memarg)))) ≤ ((coerce {B = ℕ} (unwrap! (size (valtype-numtype nt)))) / (coerce {B = ℕ} 8))) →
      Instr-ok C (LOAD nt nothing v-memarg) (mk-functype (mk-list (as (List valtype) (valtype-I32 ∷ []))) (mk-list ((valtype-numtype nt) ∷ [])))
    load-pack-0 : ∀ (C : context) (v-M : M) (v-sx : sx) (v-memarg : memarg) (mt : memtype) → 
      (0 < (length (context-MEMS C))) →
      (((context-MEMS C) [ 0 ]!) ≡ mt) →
      ((coerce {B = ℕ} (2 ^ (proj-uN-0 32 (ALIGN v-memarg)))) ≤ ((coerce {B = ℕ} v-M) / (coerce {B = ℕ} 8))) →
      Instr-ok C (LOAD (numtype-Inn Inn-I32) (just (mk-loadop- (mk-sz v-M) v-sx)) v-memarg) (mk-functype (mk-list (as (List valtype) (valtype-I32 ∷ []))) (mk-list ((valtype-Inn Inn-I32) ∷ [])))
    load-pack-1 : ∀ (C : context) (v-M : M) (v-sx : sx) (v-memarg : memarg) (mt : memtype) → 
      (0 < (length (context-MEMS C))) →
      (((context-MEMS C) [ 0 ]!) ≡ mt) →
      ((coerce {B = ℕ} (2 ^ (proj-uN-0 32 (ALIGN v-memarg)))) ≤ ((coerce {B = ℕ} v-M) / (coerce {B = ℕ} 8))) →
      Instr-ok C (LOAD (numtype-Inn Inn-I64) (just (mk-loadop- (mk-sz v-M) v-sx)) v-memarg) (mk-functype (mk-list (as (List valtype) (valtype-I32 ∷ []))) (mk-list ((valtype-Inn Inn-I64) ∷ [])))
    store-val : ∀ (C : context) (nt : numtype) (v-memarg : memarg) (mt : memtype) → 
      (0 < (length (context-MEMS C))) →
      (((context-MEMS C) [ 0 ]!) ≡ mt) →
      ((size (valtype-numtype nt)) ≢ nothing) →
      ((coerce {B = ℕ} (2 ^ (proj-uN-0 32 (ALIGN v-memarg)))) ≤ ((coerce {B = ℕ} (unwrap! (size (valtype-numtype nt)))) / (coerce {B = ℕ} 8))) →
      Instr-ok C (STORE nt nothing v-memarg) (mk-functype (mk-list (as (List valtype) (valtype-I32 ∷ (valtype-numtype nt) ∷ []))) (mk-list []))
    store-pack : ∀ (C : context) (v-Inn : Inn) (v-M : M) (v-memarg : memarg) (mt : memtype) → 
      (0 < (length (context-MEMS C))) →
      (((context-MEMS C) [ 0 ]!) ≡ mt) →
      ((coerce {B = ℕ} (2 ^ (proj-uN-0 32 (ALIGN v-memarg)))) ≤ ((coerce {B = ℕ} v-M) / (coerce {B = ℕ} 8))) →
      Instr-ok C (STORE (numtype-Inn v-Inn) (just (mk-sz v-M)) v-memarg) (mk-functype (mk-list (as (List valtype) (valtype-I32 ∷ (valtype-Inn v-Inn) ∷ []))) (mk-list []))
    vload : ∀ (C : context) (v-M : M) (v-N : N) (v-sx : sx) (v-memarg : memarg) (mt : memtype) → 
      (0 < (length (context-MEMS C))) →
      (((context-MEMS C) [ 0 ]!) ≡ mt) →
      ((coerce {B = ℕ} (2 ^ (proj-uN-0 32 (ALIGN v-memarg)))) ≤ (((coerce {B = ℕ} v-M) / (coerce {B = ℕ} 8)) * (coerce {B = ℕ} v-N))) →
      Instr-ok C (VLOAD V128 (just (SHAPEX- v-M v-N v-sx)) v-memarg) (mk-functype (mk-list (as (List valtype) (valtype-I32 ∷ []))) (mk-list (as (List valtype) (valtype-V128 ∷ []))))
    vload-splat : ∀ (C : context) (v-n : n) (v-memarg : memarg) (mt : memtype) → 
      (0 < (length (context-MEMS C))) →
      (((context-MEMS C) [ 0 ]!) ≡ mt) →
      ((coerce {B = ℕ} (2 ^ (proj-uN-0 32 (ALIGN v-memarg)))) ≤ ((coerce {B = ℕ} v-n) / (coerce {B = ℕ} 8))) →
      Instr-ok C (VLOAD V128 (just (SPLAT v-n)) v-memarg) (mk-functype (mk-list (as (List valtype) (valtype-I32 ∷ []))) (mk-list (as (List valtype) (valtype-V128 ∷ []))))
    vload-zero : ∀ (C : context) (v-n : n) (v-memarg : memarg) (mt : memtype) → 
      (0 < (length (context-MEMS C))) →
      (((context-MEMS C) [ 0 ]!) ≡ mt) →
      ((coerce {B = ℕ} (2 ^ (proj-uN-0 32 (ALIGN v-memarg)))) ≤ ((coerce {B = ℕ} v-n) / (coerce {B = ℕ} 8))) →
      Instr-ok C (VLOAD V128 (just (vloadop-ZERO v-n)) v-memarg) (mk-functype (mk-list (as (List valtype) (valtype-I32 ∷ []))) (mk-list (as (List valtype) (valtype-V128 ∷ []))))
    vload-lane : ∀ (C : context) (v-n : n) (v-memarg : memarg) (v-laneidx : laneidx) (mt : memtype) → 
      (0 < (length (context-MEMS C))) →
      (((context-MEMS C) [ 0 ]!) ≡ mt) →
      ((coerce {B = ℕ} (2 ^ (proj-uN-0 32 (ALIGN v-memarg)))) ≤ ((coerce {B = ℕ} v-n) / (coerce {B = ℕ} 8))) →
      ((coerce {B = ℕ} (proj-uN-0 8 v-laneidx)) < ((coerce {B = ℕ} 128) / (coerce {B = ℕ} v-n))) →
      Instr-ok C (VLOAD-LANE V128 (mk-sz v-n) v-memarg v-laneidx) (mk-functype (mk-list (as (List valtype) (valtype-I32 ∷ valtype-V128 ∷ []))) (mk-list (as (List valtype) (valtype-V128 ∷ []))))
    vstore : ∀ (C : context) (v-memarg : memarg) (mt : memtype) → 
      (0 < (length (context-MEMS C))) →
      (((context-MEMS C) [ 0 ]!) ≡ mt) →
      ((size valtype-V128) ≢ nothing) →
      ((coerce {B = ℕ} (2 ^ (proj-uN-0 32 (ALIGN v-memarg)))) ≤ ((coerce {B = ℕ} (unwrap! (size valtype-V128))) / (coerce {B = ℕ} 8))) →
      Instr-ok C (VSTORE V128 v-memarg) (mk-functype (mk-list (as (List valtype) (valtype-I32 ∷ valtype-V128 ∷ []))) (mk-list []))
    vstore-lane : ∀ (C : context) (v-n : n) (v-memarg : memarg) (v-laneidx : laneidx) (mt : memtype) → 
      (0 < (length (context-MEMS C))) →
      (((context-MEMS C) [ 0 ]!) ≡ mt) →
      ((coerce {B = ℕ} (2 ^ (proj-uN-0 32 (ALIGN v-memarg)))) ≤ ((coerce {B = ℕ} v-n) / (coerce {B = ℕ} 8))) →
      ((coerce {B = ℕ} (proj-uN-0 8 v-laneidx)) < ((coerce {B = ℕ} 128) / (coerce {B = ℕ} v-n))) →
      Instr-ok C (VSTORE-LANE V128 (mk-sz v-n) v-memarg v-laneidx) (mk-functype (mk-list (as (List valtype) (valtype-I32 ∷ valtype-V128 ∷ []))) (mk-list []))

  {- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:138.1-138.65 -}
  data Instrs-ok : context → (List instr) → functype → Set where
    empty : ∀ (C : context) → Instrs-ok C [] (mk-functype (mk-list []) (mk-list []))
    Instrs-ok--instr : ∀ (C : context) (v-instr : instr) (t-1-lst : (List valtype)) (t-2-lst : (List valtype)) → 
      (Instr-ok C v-instr (mk-functype (mk-list t-1-lst) (mk-list t-2-lst))) →
      Instrs-ok C (v-instr ∷ []) (mk-functype (mk-list t-1-lst) (mk-list t-2-lst))
    seq : ∀ (C : context) (instr-1-lst : (List instr)) (instr-2-lst : (List instr)) (t-1-lst : (List valtype)) (t-3-lst : (List valtype)) (t-2-lst : (List valtype)) → 
      (Instrs-ok C instr-1-lst (mk-functype (mk-list t-1-lst) (mk-list t-2-lst))) →
      (Instrs-ok C instr-2-lst (mk-functype (mk-list t-2-lst) (mk-list t-3-lst))) →
      Instrs-ok C (instr-1-lst ++ instr-2-lst) (mk-functype (mk-list t-1-lst) (mk-list t-3-lst))
    sub : ∀ (C : context) (instr-lst : (List instr)) (t'-1-lst : (List valtype)) (t'-2-lst : (List valtype)) (t-1-lst : (List valtype)) (t-2-lst : (List valtype)) → 
      (Instrs-ok C instr-lst (mk-functype (mk-list t-1-lst) (mk-list t-2-lst))) →
      (Resulttype-sub (mk-list t'-1-lst) (mk-list t-1-lst)) →
      (Resulttype-sub (mk-list t-2-lst) (mk-list t'-2-lst)) →
      Instrs-ok C instr-lst (mk-functype (mk-list t'-1-lst) (mk-list t'-2-lst))
    Instrs-ok--frame : ∀ (C : context) (instr-lst : (List instr)) (t-lst : (List valtype)) (t-1-lst : (List valtype)) (t-2-lst : (List valtype)) → 
      (Instrs-ok C instr-lst (mk-functype (mk-list t-1-lst) (mk-list t-2-lst))) →
      Instrs-ok C instr-lst (mk-functype (mk-list (t-lst ++ t-1-lst)) (mk-list (t-lst ++ t-2-lst)))

{- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:139.1-139.69 -}
data Expr-ok : context → expr → resulttype → Set where
  mk-Expr-ok : ∀ (C : context) (instr-lst : (List instr)) (t-lst : (List valtype)) → 
    (Instrs-ok C instr-lst (mk-functype (mk-list []) (mk-list t-lst))) →
    Expr-ok C instr-lst (mk-list t-lst)

{- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:529.1-529.78 -}
data Instr-const : context → instr → Set where
  Instr-const--const : ∀ (C : context) (nt : numtype) (c : (num- nt)) → Instr-const C (CONST nt c)
  Instr-const--vconst : ∀ (C : context) (vt : vectype) (vc : (uN-fam0 ((unwrap! (size (valtype-vectype vt)))))) → Instr-const C (VCONST vt vc)
  Instr-const--ref-null : ∀ (C : context) (rt : reftype) → Instr-const C (REF-NULL rt)
  Instr-const--ref-func : ∀ (C : context) (x : idx) → Instr-const C (REF-FUNC x)
  Instr-const--global-get : ∀ (C : context) (x : idx) (t : valtype) → 
    ((proj-uN-0 32 x) < (length (context-GLOBALS C))) →
    (((context-GLOBALS C) [ (proj-uN-0 32 x) ]!) ≡ (mk-globaltype nothing t)) →
    Instr-const C (GLOBAL-GET x)

{- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:530.1-530.77 -}
data Expr-const : context → expr → Set where
  mk-Expr-const : ∀ (C : context) (instr-lst : (List instr)) → 
    Forall (λ (v-instr : instr) → (Instr-const C v-instr)) instr-lst →
    Expr-const C instr-lst

{- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:531.1-531.78 -}
data Expr-ok-const : context → expr → valtype → Set where
  mk-Expr-ok-const : ∀ (C : context) (v-expr : expr) (t : valtype) → 
    (Expr-ok C v-expr (mk-list (t ∷ []))) →
    (Expr-const C v-expr) →
    Expr-ok-const C v-expr t

{- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:564.1-564.73 -}
data Type-ok : type → functype → Set where
  mk-Type-ok : ∀ (ft : functype) → 
    (Functype-ok ft) →
    Type-ok (TYPE ft) ft

{- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:565.1-565.73 -}
data Func-ok : context → func → functype → Set where
  mk-Func-ok : ∀ (C : context) (x : idx) (t-lst : (List valtype)) (v-expr : expr) (t-1-lst : (List valtype)) (t-2-lst : (List valtype)) → 
    ((proj-uN-0 32 x) < (length (context-TYPES C))) →
    (((context-TYPES C) [ (proj-uN-0 32 x) ]!) ≡ (mk-functype (mk-list t-1-lst) (mk-list t-2-lst))) →
    Forall (λ (t : valtype) → (t ≢ BOT)) t-lst →
    (Expr-ok (C ⧺ record { context-TYPES = [] ; context-FUNCS = [] ; context-GLOBALS = [] ; context-TABLES = [] ; context-MEMS = [] ; context-ELEMS = [] ; context-DATAS = [] ; context-LOCALS = (t-1-lst ++ t-lst) ; LABELS = (as (List resulttype) ((mk-list t-2-lst) ∷ [])) ; context-RETURN = (just (mk-list t-2-lst)) }) v-expr (mk-list t-2-lst)) →
    Func-ok C (func-FUNC x (map (λ (t : valtype) → (LOCAL t)) t-lst) v-expr) (mk-functype (mk-list t-1-lst) (mk-list t-2-lst))

{- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:566.1-566.75 -}
data Global-ok : context → global → globaltype → Set where
  mk-Global-ok : ∀ (C : context) (gt : globaltype) (v-expr : expr) (v-mut : mut) (t : valtype) → 
    (Globaltype-ok gt) →
    (gt ≡ (mk-globaltype v-mut t)) →
    (Expr-ok-const C v-expr t) →
    Global-ok C (global-GLOBAL gt v-expr) gt

{- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:567.1-567.74 -}
data Table-ok : context → table → tabletype → Set where
  mk-Table-ok : ∀ (C : context) (tt' : tabletype) → 
    (Tabletype-ok tt') →
    Table-ok C (table-TABLE tt') tt'

{- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:568.1-568.72 -}
data Mem-ok : context → mem → memtype → Set where
  mk-Mem-ok : ∀ (C : context) (mt : memtype) → 
    (Memtype-ok mt) →
    Mem-ok C (MEMORY mt) mt

{- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:571.1-571.77 -}
data Elemmode-ok : context → elemmode → reftype → Set where
  active : ∀ (C : context) (x : idx) (v-expr : expr) (rt : reftype) (lim : limits) → 
    ((proj-uN-0 32 x) < (length (context-TABLES C))) →
    (((context-TABLES C) [ (proj-uN-0 32 x) ]!) ≡ (mk-tabletype lim rt)) →
    (Expr-ok-const C v-expr valtype-I32) →
    Elemmode-ok C (ACTIVE x v-expr) rt
  passive : ∀ (C : context) (rt : reftype) → Elemmode-ok C PASSIVE rt
  declare : ∀ (C : context) (rt : reftype) → Elemmode-ok C DECLARE rt

{- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:569.1-569.73 -}
data Elem-ok : context → elem → reftype → Set where
  mk-Elem-ok : ∀ (C : context) (rt : reftype) (expr-lst : (List expr)) (v-elemmode : elemmode) → 
    Forall (λ (v-expr : expr) → (Expr-ok-const C v-expr (valtype-reftype rt))) expr-lst →
    (Elemmode-ok C v-elemmode rt) →
    Elem-ok C (ELEM rt expr-lst v-elemmode) rt

{- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:572.1-572.77 -}
data Datamode-ok : context → datamode → Set where
  Datamode-ok--active : ∀ (C : context) (v-expr : expr) (mt : memtype) → 
    (0 < (length (context-MEMS C))) →
    (((context-MEMS C) [ 0 ]!) ≡ mt) →
    (Expr-ok-const C v-expr valtype-I32) →
    Datamode-ok C (datamode-ACTIVE (mk-uN 0) v-expr)
  Datamode-ok--passive : ∀ (C : context) → Datamode-ok C datamode-PASSIVE

{- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:570.1-570.73 -}
data Data-ok : context → data' → Set where
  mk-Data-ok : ∀ (C : context) (b-lst : (List byte)) (v-datamode : datamode) → 
    (Datamode-ok C v-datamode) →
    Data-ok C (DATA b-lst v-datamode)

{- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:573.1-573.74 -}
data Start-ok : context → start → Set where
  mk-Start-ok : ∀ (C : context) (x : idx) → 
    ((proj-uN-0 32 x) < (length (context-FUNCS C))) →
    (((context-FUNCS C) [ (proj-uN-0 32 x) ]!) ≡ (mk-functype (mk-list []) (mk-list []))) →
    Start-ok C (START x)

{- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:637.1-637.80 -}
data Import-ok : context → import' → externtype → Set where
  mk-Import-ok : ∀ (C : context) (name-1 : name) (name-2 : name) (xt : externtype) → 
    (Externtype-ok xt) →
    Import-ok C (IMPORT name-1 name-2 xt) xt

{- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:639.1-639.83 -}
data Externidx-ok : context → externidx → externtype → Set where
  Externidx-ok--func : ∀ (C : context) (x : idx) (ft : functype) → 
    ((proj-uN-0 32 x) < (length (context-FUNCS C))) →
    (((context-FUNCS C) [ (proj-uN-0 32 x) ]!) ≡ ft) →
    Externidx-ok C (externidx-FUNC x) (FUNC ft)
  Externidx-ok--global : ∀ (C : context) (x : idx) (gt : globaltype) → 
    ((proj-uN-0 32 x) < (length (context-GLOBALS C))) →
    (((context-GLOBALS C) [ (proj-uN-0 32 x) ]!) ≡ gt) →
    Externidx-ok C (externidx-GLOBAL x) (GLOBAL gt)
  Externidx-ok--table : ∀ (C : context) (x : idx) (tt' : tabletype) → 
    ((proj-uN-0 32 x) < (length (context-TABLES C))) →
    (((context-TABLES C) [ (proj-uN-0 32 x) ]!) ≡ tt') →
    Externidx-ok C (externidx-TABLE x) (TABLE tt')
  Externidx-ok--mem : ∀ (C : context) (x : idx) (mt : memtype) → 
    ((proj-uN-0 32 x) < (length (context-MEMS C))) →
    (((context-MEMS C) [ (proj-uN-0 32 x) ]!) ≡ mt) →
    Externidx-ok C (externidx-MEM x) (MEM mt)

{- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:638.1-638.80 -}
data Export-ok : context → export → externtype → Set where
  mk-Export-ok : ∀ (C : context) (v-name : name) (v-externidx : externidx) (xt : externtype) → 
    (Externidx-ok C v-externidx xt) →
    Export-ok C (EXPORT v-name v-externidx) xt

{- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:669.1-669.62 -}
data Module-ok : module' → Set where
  mk-Module-ok : ∀ (type-lst : (List type)) (import-lst : (List import')) (func-lst : (List func)) (global-lst : (List global)) (table-lst : (List table)) (mem-lst : (List mem)) (elem-lst : (List elem)) (v-n : n) (data-lst : (List data')) (start-opt : (Maybe start)) (export-lst : (List export)) (ft'-lst : (List functype)) (ixt-lst : (List externtype)) (C' : context) (gt-lst : (List globaltype)) (tt-lst : (List tabletype)) (mt-lst : (List memtype)) (rt-lst : (List reftype)) (C : context) (ft-lst : (List functype)) (xt-lst : (List externtype)) (ift-lst : (List functype)) (igt-lst : (List globaltype)) (itt-lst : (List tabletype)) (imt-lst : (List memtype)) → 
    ((length (data-lst)) ≡ (v-n)) →
    ((length ft'-lst) ≡ (length type-lst)) →
    Forall₂ (λ (ft' : functype) (v-type : type) → (Type-ok v-type ft')) ft'-lst type-lst →
    ((length import-lst) ≡ (length ixt-lst)) →
    Forall₂ (λ (v-import : import') (ixt : externtype) → (Import-ok record { context-TYPES = ft'-lst ; context-FUNCS = [] ; context-GLOBALS = [] ; context-TABLES = [] ; context-MEMS = [] ; context-ELEMS = [] ; context-DATAS = [] ; context-LOCALS = [] ; LABELS = [] ; context-RETURN = nothing } v-import ixt)) import-lst ixt-lst →
    ((length global-lst) ≡ (length gt-lst)) →
    Forall₂ (λ (v-global : global) (gt : globaltype) → (Global-ok C' v-global gt)) global-lst gt-lst →
    ((length table-lst) ≡ (length tt-lst)) →
    Forall₂ (λ (v-table : table) (tt' : tabletype) → (Table-ok C' v-table tt')) table-lst tt-lst →
    ((length mem-lst) ≡ (length mt-lst)) →
    Forall₂ (λ (v-mem : mem) (mt : memtype) → (Mem-ok C' v-mem mt)) mem-lst mt-lst →
    ((length elem-lst) ≡ (length rt-lst)) →
    Forall₂ (λ (v-elem : elem) (rt : reftype) → (Elem-ok C' v-elem rt)) elem-lst rt-lst →
    Forall (λ (v-data : data') → (Data-ok C' v-data)) data-lst →
    ((length ft-lst) ≡ (length func-lst)) →
    Forall₂ (λ (ft : functype) (v-func : func) → (Func-ok C v-func ft)) ft-lst func-lst →
    Forall (λ (v-start : start) → (Start-ok C v-start)) (fromMaybe start-opt) →
    ((length export-lst) ≡ (length xt-lst)) →
    Forall₂ (λ (v-export : export) (xt : externtype) → (Export-ok C v-export xt)) export-lst xt-lst →
    ((length mt-lst) ≤ 1) →
    (C ≡ record { context-TYPES = ft'-lst ; context-FUNCS = (ift-lst ++ ft-lst) ; context-GLOBALS = (igt-lst ++ gt-lst) ; context-TABLES = (itt-lst ++ tt-lst) ; context-MEMS = (imt-lst ++ mt-lst) ; context-ELEMS = rt-lst ; context-DATAS = (replicate v-n OK) ; context-LOCALS = [] ; LABELS = [] ; context-RETURN = nothing }) →
    (C' ≡ record { context-TYPES = ft'-lst ; context-FUNCS = (ift-lst ++ ft-lst) ; context-GLOBALS = igt-lst ; context-TABLES = (itt-lst ++ tt-lst) ; context-MEMS = (imt-lst ++ mt-lst) ; context-ELEMS = [] ; context-DATAS = [] ; context-LOCALS = [] ; LABELS = [] ; context-RETURN = nothing }) →
    (ift-lst ≡ (funcsxt ixt-lst)) →
    (igt-lst ≡ (globalsxt ixt-lst)) →
    (itt-lst ≡ (tablesxt ixt-lst)) →
    (imt-lst ≡ (memsxt ixt-lst)) →
    Module-ok (MODULE type-lst import-lst func-lst global-lst table-lst mem-lst elem-lst data-lst start-opt export-lst)

{- Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:224.1-226.15 -}
data Step-pure-before-ref-is-null-false : (List admininstr) → Set where
  ref-is-null-true-0 : ∀ (v-ref : ref) (rt : reftype) → 
    (v-ref ≡ (ref-REF-NULL rt)) →
    Step-pure-before-ref-is-null-false (as (List admininstr) ((admininstr-ref v-ref) ∷ admininstr-REF-IS-NULL ∷ []))

{- Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:276.1-278.15 -}
data Step-pure-before-vtestop-false : (List admininstr) → Set where
  vtestop-true-0-0 : ∀ (c : (uN-fam0 (128))) (v-N : N) (ci-1-lst : (List (uN-fam0 (32)))) → 
    (ci-1-lst ≡ (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-N)) c)) →
    Forall (λ (ci-1-18 : (uN-fam0 (32))) → ((proj-uN-0 (lsize (lanetype-Jnn Jnn-I32)) ci-1-18) ≢ 0)) ci-1-lst →
    Step-pure-before-vtestop-false (as (List admininstr) ((admininstr-VCONST V128 c) ∷ (admininstr-VTESTOP (X (lanetype-Jnn Jnn-I32) (mk-dim v-N)) ALL-TRUE) ∷ []))
  vtestop-true-0-1 : ∀ (c : (uN-fam0 (128))) (v-N : N) (ci-1-lst : (List (uN-fam0 (64)))) → 
    (ci-1-lst ≡ (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-N)) c)) →
    Forall (λ (ci-1-20 : (uN-fam0 (64))) → ((proj-uN-0 (lsize (lanetype-Jnn Jnn-I64)) ci-1-20) ≢ 0)) ci-1-lst →
    Step-pure-before-vtestop-false (as (List admininstr) ((admininstr-VCONST V128 c) ∷ (admininstr-VTESTOP (X (lanetype-Jnn Jnn-I64) (mk-dim v-N)) ALL-TRUE) ∷ []))
  vtestop-true-0-2 : ∀ (c : (uN-fam0 (128))) (v-N : N) (ci-1-lst : (List (uN-fam0 (8)))) → 
    (ci-1-lst ≡ (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-N)) c)) →
    Forall (λ (ci-1-22 : (uN-fam0 (8))) → ((proj-uN-0 (lsize (lanetype-Jnn Jnn-I8)) ci-1-22) ≢ 0)) ci-1-lst →
    Step-pure-before-vtestop-false (as (List admininstr) ((admininstr-VCONST V128 c) ∷ (admininstr-VTESTOP (X (lanetype-Jnn Jnn-I8) (mk-dim v-N)) ALL-TRUE) ∷ []))
  vtestop-true-0-3 : ∀ (c : (uN-fam0 (128))) (v-N : N) (ci-1-lst : (List (uN-fam0 (16)))) → 
    (ci-1-lst ≡ (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-N)) c)) →
    Forall (λ (ci-1-24 : (uN-fam0 (16))) → ((proj-uN-0 (lsize (lanetype-Jnn Jnn-I16)) ci-1-24) ≢ 0)) ci-1-lst →
    Step-pure-before-vtestop-false (as (List admininstr) ((admininstr-VCONST V128 c) ∷ (admininstr-VTESTOP (X (lanetype-Jnn Jnn-I16) (mk-dim v-N)) ALL-TRUE) ∷ []))

{- Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:6.1-6.109 -}
data Step-pure : (List admininstr) → (List admininstr) → Set where
  Step-pure--unreachable : Step-pure (as (List admininstr) (admininstr-UNREACHABLE ∷ [])) (as (List admininstr) (admininstr-TRAP ∷ []))
  Step-pure--nop : Step-pure (as (List admininstr) (admininstr-NOP ∷ [])) []
  Step-pure--drop : ∀ (v-val : val) → Step-pure (as (List admininstr) ((admininstr-val v-val) ∷ admininstr-DROP ∷ [])) []
  select-true : ∀ (val-1 : val) (val-2 : val) (c : (uN-fam0 (32))) (t-lst-opt : (Maybe (List valtype))) → 
    ((proj-uN-0 32 c) ≢ 0) →
    Step-pure (as (List admininstr) ((admininstr-val val-1) ∷ (admininstr-val val-2) ∷ (admininstr-CONST I32 c) ∷ (admininstr-SELECT t-lst-opt) ∷ [])) ((admininstr-val val-1) ∷ [])
  select-false : ∀ (val-1 : val) (val-2 : val) (c : (uN-fam0 (32))) (t-lst-opt : (Maybe (List valtype))) → 
    ((proj-uN-0 32 c) ≡ 0) →
    Step-pure (as (List admininstr) ((admininstr-val val-1) ∷ (admininstr-val val-2) ∷ (admininstr-CONST I32 c) ∷ (admininstr-SELECT t-lst-opt) ∷ [])) ((admininstr-val val-2) ∷ [])
  if-true : ∀ (c : (uN-fam0 (32))) (bt : blocktype) (instr-1-lst : (List instr)) (instr-2-lst : (List instr)) → 
    ((proj-uN-0 32 c) ≢ 0) →
    Step-pure (as (List admininstr) ((admininstr-CONST I32 c) ∷ (admininstr-IFELSE bt instr-1-lst instr-2-lst) ∷ [])) (as (List admininstr) ((admininstr-BLOCK bt instr-1-lst) ∷ []))
  if-false : ∀ (c : (uN-fam0 (32))) (bt : blocktype) (instr-1-lst : (List instr)) (instr-2-lst : (List instr)) → 
    ((proj-uN-0 32 c) ≡ 0) →
    Step-pure (as (List admininstr) ((admininstr-CONST I32 c) ∷ (admininstr-IFELSE bt instr-1-lst instr-2-lst) ∷ [])) (as (List admininstr) ((admininstr-BLOCK bt instr-2-lst) ∷ []))
  label-vals : ∀ (v-n : n) (instr-lst : (List instr)) (val-lst : (List val)) → Step-pure (as (List admininstr) ((LABEL- v-n instr-lst (map (λ (v-val : val) → (admininstr-val v-val)) val-lst)) ∷ [])) (map (λ (v-val : val) → (admininstr-val v-val)) val-lst)
  br-zero : ∀ (v-n : n) (instr'-lst : (List instr)) (val'-lst : (List val)) (val-lst : (List val)) (instr-lst : (List instr)) → 
    ((length (val-lst)) ≡ (v-n)) →
    Step-pure (as (List admininstr) ((LABEL- v-n instr'-lst ((((map (λ (val' : val) → (admininstr-val val')) val'-lst) ++ (map (λ (v-val : val) → (admininstr-val v-val)) val-lst)) ++ (as (List admininstr) ((admininstr-BR (mk-uN 0)) ∷ []))) ++ (map (λ (v-instr : instr) → (admininstr-instr v-instr)) instr-lst))) ∷ [])) ((map (λ (v-val : val) → (admininstr-val v-val)) val-lst) ++ (map (λ (instr' : instr) → (admininstr-instr instr')) instr'-lst))
  br-succ : ∀ (v-n : n) (instr'-lst : (List instr)) (val-lst : (List val)) (l : labelidx) (instr-lst : (List instr)) → Step-pure (as (List admininstr) ((LABEL- v-n instr'-lst (((map (λ (v-val : val) → (admininstr-val v-val)) val-lst) ++ (as (List admininstr) ((admininstr-BR (mk-uN ((proj-uN-0 32 l) + 1))) ∷ []))) ++ (map (λ (v-instr : instr) → (admininstr-instr v-instr)) instr-lst))) ∷ [])) ((map (λ (v-val : val) → (admininstr-val v-val)) val-lst) ++ (as (List admininstr) ((admininstr-BR l) ∷ [])))
  br-if-true : ∀ (c : (uN-fam0 (32))) (l : labelidx) → 
    ((proj-uN-0 32 c) ≢ 0) →
    Step-pure (as (List admininstr) ((admininstr-CONST I32 c) ∷ (admininstr-BR-IF l) ∷ [])) (as (List admininstr) ((admininstr-BR l) ∷ []))
  br-if-false : ∀ (c : (uN-fam0 (32))) (l : labelidx) → 
    ((proj-uN-0 32 c) ≡ 0) →
    Step-pure (as (List admininstr) ((admininstr-CONST I32 c) ∷ (admininstr-BR-IF l) ∷ [])) []
  br-table-lt : ∀ (i : (uN-fam0 (32))) (l-lst : (List labelidx)) (l' : labelidx) → 
    ((proj-uN-0 32 i) < (length l-lst)) →
    Step-pure (as (List admininstr) ((admininstr-CONST I32 i) ∷ (admininstr-BR-TABLE l-lst l') ∷ [])) (as (List admininstr) ((admininstr-BR (l-lst [ (proj-uN-0 32 i) ]!)) ∷ []))
  br-table-ge : ∀ (i : (uN-fam0 (32))) (l-lst : (List labelidx)) (l' : labelidx) → 
    ((proj-uN-0 32 i) ≥ (length l-lst)) →
    Step-pure (as (List admininstr) ((admininstr-CONST I32 i) ∷ (admininstr-BR-TABLE l-lst l') ∷ [])) (as (List admininstr) ((admininstr-BR l') ∷ []))
  frame-vals : ∀ (v-n : n) (f : frame) (val-lst : (List val)) → 
    ((length (val-lst)) ≡ (v-n)) →
    Step-pure (as (List admininstr) ((FRAME- v-n f (map (λ (v-val : val) → (admininstr-val v-val)) val-lst)) ∷ [])) (map (λ (v-val : val) → (admininstr-val v-val)) val-lst)
  return-frame : ∀ (v-n : n) (f : frame) (val'-lst : (List val)) (val-lst : (List val)) (instr-lst : (List instr)) → 
    ((length (val-lst)) ≡ (v-n)) →
    Step-pure (as (List admininstr) ((FRAME- v-n f ((((map (λ (val' : val) → (admininstr-val val')) val'-lst) ++ (map (λ (v-val : val) → (admininstr-val v-val)) val-lst)) ++ (as (List admininstr) (admininstr-RETURN ∷ []))) ++ (map (λ (v-instr : instr) → (admininstr-instr v-instr)) instr-lst))) ∷ [])) (map (λ (v-val : val) → (admininstr-val v-val)) val-lst)
  return-label : ∀ (v-n : n) (instr'-lst : (List instr)) (val-lst : (List val)) (instr-lst : (List instr)) → Step-pure (as (List admininstr) ((LABEL- v-n instr'-lst (((map (λ (v-val : val) → (admininstr-val v-val)) val-lst) ++ (as (List admininstr) (admininstr-RETURN ∷ []))) ++ (map (λ (v-instr : instr) → (admininstr-instr v-instr)) instr-lst))) ∷ [])) ((map (λ (v-val : val) → (admininstr-val v-val)) val-lst) ++ (as (List admininstr) (admininstr-RETURN ∷ [])))
  trap-vals : ∀ (val-lst : (List val)) (instr-lst : (List instr)) → 
    ((val-lst ≢ []) ⊎ (instr-lst ≢ [])) →
    Step-pure ((map (λ (v-val : val) → (admininstr-val v-val)) val-lst) ++ ((as (List admininstr) (admininstr-TRAP ∷ [])) ++ (map (λ (v-instr : instr) → (admininstr-instr v-instr)) instr-lst))) (as (List admininstr) (admininstr-TRAP ∷ []))
  trap-label : ∀ (v-n : n) (instr'-lst : (List instr)) → Step-pure (as (List admininstr) ((LABEL- v-n instr'-lst (as (List admininstr) (admininstr-TRAP ∷ []))) ∷ [])) (as (List admininstr) (admininstr-TRAP ∷ []))
  trap-frame : ∀ (v-n : n) (f : frame) → Step-pure (as (List admininstr) ((FRAME- v-n f (as (List admininstr) (admininstr-TRAP ∷ []))) ∷ [])) (as (List admininstr) (admininstr-TRAP ∷ []))
  unop-val : ∀ (nt : numtype) (c-1 : (num- nt)) (unop : (unop- nt)) (c : (num- nt)) → 
    ((length (fun-unop- nt unop c-1)) > 0) →
    (c ∈ (fun-unop- nt unop c-1)) →
    Step-pure (as (List admininstr) ((admininstr-CONST nt c-1) ∷ (admininstr-UNOP nt unop) ∷ [])) (as (List admininstr) ((admininstr-CONST nt c) ∷ []))
  unop-trap : ∀ (nt : numtype) (c-1 : (num- nt)) (unop : (unop- nt)) → 
    ((fun-unop- nt unop c-1) ≡ []) →
    Step-pure (as (List admininstr) ((admininstr-CONST nt c-1) ∷ (admininstr-UNOP nt unop) ∷ [])) (as (List admininstr) (admininstr-TRAP ∷ []))
  binop-val : ∀ (nt : numtype) (c-1 : (num- nt)) (c-2 : (num- nt)) (binop : (binop- nt)) (c : (num- nt)) → 
    ((length (fun-binop- nt binop c-1 c-2)) > 0) →
    (c ∈ (fun-binop- nt binop c-1 c-2)) →
    Step-pure (as (List admininstr) ((admininstr-CONST nt c-1) ∷ (admininstr-CONST nt c-2) ∷ (admininstr-BINOP nt binop) ∷ [])) (as (List admininstr) ((admininstr-CONST nt c) ∷ []))
  binop-trap : ∀ (nt : numtype) (c-1 : (num- nt)) (c-2 : (num- nt)) (binop : (binop- nt)) → 
    ((fun-binop- nt binop c-1 c-2) ≡ []) →
    Step-pure (as (List admininstr) ((admininstr-CONST nt c-1) ∷ (admininstr-CONST nt c-2) ∷ (admininstr-BINOP nt binop) ∷ [])) (as (List admininstr) (admininstr-TRAP ∷ []))
  Step-pure--testop : ∀ (nt : numtype) (c-1 : (num- nt)) (testop : (testop- nt)) (c : (uN-fam0 (32))) → 
    (c ≡ (fun-testop- nt testop c-1)) →
    Step-pure (as (List admininstr) ((admininstr-CONST nt c-1) ∷ (admininstr-TESTOP nt testop) ∷ [])) (as (List admininstr) ((admininstr-CONST I32 c) ∷ []))
  Step-pure--relop : ∀ (nt : numtype) (c-1 : (num- nt)) (c-2 : (num- nt)) (relop : (relop- nt)) (c : (uN-fam0 (32))) → 
    (c ≡ (fun-relop- nt relop c-1 c-2)) →
    Step-pure (as (List admininstr) ((admininstr-CONST nt c-1) ∷ (admininstr-CONST nt c-2) ∷ (admininstr-RELOP nt relop) ∷ [])) (as (List admininstr) ((admininstr-CONST I32 c) ∷ []))
  cvtop-val : ∀ (nt-1 : numtype) (c-1 : (num- nt-1)) (nt-2 : numtype) (v-cvtop : cvtop) (c : (num- nt-2)) → 
    ((length (cvtop-- nt-1 nt-2 v-cvtop c-1)) > 0) →
    (c ∈ (cvtop-- nt-1 nt-2 v-cvtop c-1)) →
    Step-pure (as (List admininstr) ((admininstr-CONST nt-1 c-1) ∷ (admininstr-CVTOP nt-2 nt-1 v-cvtop) ∷ [])) (as (List admininstr) ((admininstr-CONST nt-2 c) ∷ []))
  cvtop-trap : ∀ (nt-1 : numtype) (c-1 : (num- nt-1)) (nt-2 : numtype) (v-cvtop : cvtop) → 
    ((cvtop-- nt-1 nt-2 v-cvtop c-1) ≡ []) →
    Step-pure (as (List admininstr) ((admininstr-CONST nt-1 c-1) ∷ (admininstr-CVTOP nt-2 nt-1 v-cvtop) ∷ [])) (as (List admininstr) (admininstr-TRAP ∷ []))
  ref-is-null-true : ∀ (v-ref : ref) (rt : reftype) → 
    (v-ref ≡ (ref-REF-NULL rt)) →
    Step-pure (as (List admininstr) ((admininstr-ref v-ref) ∷ admininstr-REF-IS-NULL ∷ [])) (as (List admininstr) ((admininstr-CONST I32 (mk-uN 1)) ∷ []))
  ref-is-null-false : ∀ (v-ref : ref) → 
    (¬ (Step-pure-before-ref-is-null-false (as (List admininstr) ((admininstr-ref v-ref) ∷ admininstr-REF-IS-NULL ∷ [])))) →
    Step-pure (as (List admininstr) ((admininstr-ref v-ref) ∷ admininstr-REF-IS-NULL ∷ [])) (as (List admininstr) ((admininstr-CONST I32 (mk-uN 0)) ∷ []))
  Step-pure--vvunop : ∀ (c-1 : (uN-fam0 (128))) (v-vvunop : vvunop) (c : (uN-fam0 (128))) → 
    (c ≡ (vvunop- V128 v-vvunop c-1)) →
    Step-pure (as (List admininstr) ((admininstr-VCONST V128 c-1) ∷ (admininstr-VVUNOP V128 v-vvunop) ∷ [])) (as (List admininstr) ((admininstr-VCONST V128 c) ∷ []))
  Step-pure--vvbinop : ∀ (c-1 : (uN-fam0 (128))) (c-2 : (uN-fam0 (128))) (v-vvbinop : vvbinop) (c : (uN-fam0 (128))) → 
    (c ≡ (vvbinop- V128 v-vvbinop c-1 c-2)) →
    Step-pure (as (List admininstr) ((admininstr-VCONST V128 c-1) ∷ (admininstr-VCONST V128 c-2) ∷ (admininstr-VVBINOP V128 v-vvbinop) ∷ [])) (as (List admininstr) ((admininstr-VCONST V128 c) ∷ []))
  Step-pure--vvternop : ∀ (c-1 : (uN-fam0 (128))) (c-2 : (uN-fam0 (128))) (c-3 : (uN-fam0 (128))) (v-vvternop : vvternop) (c : (uN-fam0 (128))) → 
    (c ≡ (vvternop- V128 v-vvternop c-1 c-2 c-3)) →
    Step-pure (as (List admininstr) ((admininstr-VCONST V128 c-1) ∷ (admininstr-VCONST V128 c-2) ∷ (admininstr-VCONST V128 c-3) ∷ (admininstr-VVTERNOP V128 v-vvternop) ∷ [])) (as (List admininstr) ((admininstr-VCONST V128 c) ∷ []))
  Step-pure--vvtestop : ∀ (c-1 : (uN-fam0 (128))) (c : (uN-fam0 (32))) → 
    ((size valtype-V128) ≢ nothing) →
    (c ≡ (ine- (unwrap! (size valtype-V128)) c-1 (mk-uN 0))) →
    Step-pure (as (List admininstr) ((admininstr-VCONST V128 c-1) ∷ (admininstr-VVTESTOP V128 ANY-TRUE) ∷ [])) (as (List admininstr) ((admininstr-CONST I32 c) ∷ []))
  Step-pure--vunop : ∀ (c-1 : (uN-fam0 (128))) (sh : shape) (vunop : (vunop- sh)) (c : (uN-fam0 (128))) → 
    ((length (fun-vunop- sh vunop c-1)) > 0) →
    (c ∈ (fun-vunop- sh vunop c-1)) →
    Step-pure (as (List admininstr) ((admininstr-VCONST V128 c-1) ∷ (admininstr-VUNOP sh vunop) ∷ [])) (as (List admininstr) ((admininstr-VCONST V128 c) ∷ []))
  vunop-trap : ∀ (c-1 : (uN-fam0 (128))) (sh : shape) (vunop : (vunop- sh)) → 
    ((fun-vunop- sh vunop c-1) ≡ []) →
    Step-pure (as (List admininstr) ((admininstr-VCONST V128 c-1) ∷ (admininstr-VUNOP sh vunop) ∷ [])) (as (List admininstr) (admininstr-TRAP ∷ []))
  vbinop-val : ∀ (c-1 : (uN-fam0 (128))) (c-2 : (uN-fam0 (128))) (sh : shape) (vbinop : (vbinop- sh)) (c : (uN-fam0 (128))) → 
    ((length (fun-vbinop- sh vbinop c-1 c-2)) > 0) →
    (c ∈ (fun-vbinop- sh vbinop c-1 c-2)) →
    Step-pure (as (List admininstr) ((admininstr-VCONST V128 c-1) ∷ (admininstr-VCONST V128 c-2) ∷ (admininstr-VBINOP sh vbinop) ∷ [])) (as (List admininstr) ((admininstr-VCONST V128 c) ∷ []))
  vbinop-trap : ∀ (c-1 : (uN-fam0 (128))) (c-2 : (uN-fam0 (128))) (sh : shape) (vbinop : (vbinop- sh)) → 
    ((fun-vbinop- sh vbinop c-1 c-2) ≡ []) →
    Step-pure (as (List admininstr) ((admininstr-VCONST V128 c-1) ∷ (admininstr-VCONST V128 c-2) ∷ (admininstr-VBINOP sh vbinop) ∷ [])) (as (List admininstr) (admininstr-TRAP ∷ []))
  vtestop-true-0 : ∀ (c : (uN-fam0 (128))) (v-N : N) (ci-1-lst : (List (uN-fam0 (32)))) → 
    (ci-1-lst ≡ (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-N)) c)) →
    Forall (λ (ci-1-26 : (uN-fam0 (32))) → ((proj-uN-0 (lsize (lanetype-Jnn Jnn-I32)) ci-1-26) ≢ 0)) ci-1-lst →
    Step-pure (as (List admininstr) ((admininstr-VCONST V128 c) ∷ (admininstr-VTESTOP (X (lanetype-Jnn Jnn-I32) (mk-dim v-N)) ALL-TRUE) ∷ [])) (as (List admininstr) ((admininstr-CONST I32 (mk-uN 1)) ∷ []))
  vtestop-true-1 : ∀ (c : (uN-fam0 (128))) (v-N : N) (ci-1-lst : (List (uN-fam0 (64)))) → 
    (ci-1-lst ≡ (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-N)) c)) →
    Forall (λ (ci-1-28 : (uN-fam0 (64))) → ((proj-uN-0 (lsize (lanetype-Jnn Jnn-I64)) ci-1-28) ≢ 0)) ci-1-lst →
    Step-pure (as (List admininstr) ((admininstr-VCONST V128 c) ∷ (admininstr-VTESTOP (X (lanetype-Jnn Jnn-I64) (mk-dim v-N)) ALL-TRUE) ∷ [])) (as (List admininstr) ((admininstr-CONST I32 (mk-uN 1)) ∷ []))
  vtestop-true-2 : ∀ (c : (uN-fam0 (128))) (v-N : N) (ci-1-lst : (List (uN-fam0 (8)))) → 
    (ci-1-lst ≡ (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-N)) c)) →
    Forall (λ (ci-1-30 : (uN-fam0 (8))) → ((proj-uN-0 (lsize (lanetype-Jnn Jnn-I8)) ci-1-30) ≢ 0)) ci-1-lst →
    Step-pure (as (List admininstr) ((admininstr-VCONST V128 c) ∷ (admininstr-VTESTOP (X (lanetype-Jnn Jnn-I8) (mk-dim v-N)) ALL-TRUE) ∷ [])) (as (List admininstr) ((admininstr-CONST I32 (mk-uN 1)) ∷ []))
  vtestop-true-3 : ∀ (c : (uN-fam0 (128))) (v-N : N) (ci-1-lst : (List (uN-fam0 (16)))) → 
    (ci-1-lst ≡ (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-N)) c)) →
    Forall (λ (ci-1-32 : (uN-fam0 (16))) → ((proj-uN-0 (lsize (lanetype-Jnn Jnn-I16)) ci-1-32) ≢ 0)) ci-1-lst →
    Step-pure (as (List admininstr) ((admininstr-VCONST V128 c) ∷ (admininstr-VTESTOP (X (lanetype-Jnn Jnn-I16) (mk-dim v-N)) ALL-TRUE) ∷ [])) (as (List admininstr) ((admininstr-CONST I32 (mk-uN 1)) ∷ []))
  vtestop-false-0 : ∀ (c : (uN-fam0 (128))) (v-N : N) → 
    (¬ (Step-pure-before-vtestop-false (as (List admininstr) ((admininstr-VCONST V128 c) ∷ (admininstr-VTESTOP (X (lanetype-Jnn Jnn-I32) (mk-dim v-N)) ALL-TRUE) ∷ [])))) →
    Step-pure (as (List admininstr) ((admininstr-VCONST V128 c) ∷ (admininstr-VTESTOP (X (lanetype-Jnn Jnn-I32) (mk-dim v-N)) ALL-TRUE) ∷ [])) (as (List admininstr) ((admininstr-CONST I32 (mk-uN 0)) ∷ []))
  vtestop-false-1 : ∀ (c : (uN-fam0 (128))) (v-N : N) → 
    (¬ (Step-pure-before-vtestop-false (as (List admininstr) ((admininstr-VCONST V128 c) ∷ (admininstr-VTESTOP (X (lanetype-Jnn Jnn-I64) (mk-dim v-N)) ALL-TRUE) ∷ [])))) →
    Step-pure (as (List admininstr) ((admininstr-VCONST V128 c) ∷ (admininstr-VTESTOP (X (lanetype-Jnn Jnn-I64) (mk-dim v-N)) ALL-TRUE) ∷ [])) (as (List admininstr) ((admininstr-CONST I32 (mk-uN 0)) ∷ []))
  vtestop-false-2 : ∀ (c : (uN-fam0 (128))) (v-N : N) → 
    (¬ (Step-pure-before-vtestop-false (as (List admininstr) ((admininstr-VCONST V128 c) ∷ (admininstr-VTESTOP (X (lanetype-Jnn Jnn-I8) (mk-dim v-N)) ALL-TRUE) ∷ [])))) →
    Step-pure (as (List admininstr) ((admininstr-VCONST V128 c) ∷ (admininstr-VTESTOP (X (lanetype-Jnn Jnn-I8) (mk-dim v-N)) ALL-TRUE) ∷ [])) (as (List admininstr) ((admininstr-CONST I32 (mk-uN 0)) ∷ []))
  vtestop-false-3 : ∀ (c : (uN-fam0 (128))) (v-N : N) → 
    (¬ (Step-pure-before-vtestop-false (as (List admininstr) ((admininstr-VCONST V128 c) ∷ (admininstr-VTESTOP (X (lanetype-Jnn Jnn-I16) (mk-dim v-N)) ALL-TRUE) ∷ [])))) →
    Step-pure (as (List admininstr) ((admininstr-VCONST V128 c) ∷ (admininstr-VTESTOP (X (lanetype-Jnn Jnn-I16) (mk-dim v-N)) ALL-TRUE) ∷ [])) (as (List admininstr) ((admininstr-CONST I32 (mk-uN 0)) ∷ []))
  Step-pure--vrelop : ∀ (c-1 : (uN-fam0 (128))) (c-2 : (uN-fam0 (128))) (sh : shape) (vrelop : (vrelop- sh)) (c : (uN-fam0 (128))) → 
    ((fun-vrelop- sh vrelop c-1 c-2) ≡ c) →
    Step-pure (as (List admininstr) ((admininstr-VCONST V128 c-1) ∷ (admininstr-VCONST V128 c-2) ∷ (admininstr-VRELOP sh vrelop) ∷ [])) (as (List admininstr) ((admininstr-VCONST V128 c) ∷ []))
  vshiftop-0 : ∀ (c-1 : (uN-fam0 (128))) (v-n : n) (v-N : N) (vshiftop : (vshiftop--fam0 (Jnn-I32) (v-N))) (c : (uN-fam0 (128))) (c'-lst : (List (uN-fam0 (32)))) → 
    (c'-lst ≡ (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-N)) c-1)) →
    (c ≡ (inv-lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-N)) (map (λ (c'-2 : (uN-fam0 (32))) → (fun-vshiftop- (ishape-X Jnn-I32 (mk-dim v-N)) vshiftop c'-2 (mk-uN v-n))) c'-lst))) →
    Step-pure (as (List admininstr) ((admininstr-VCONST V128 c-1) ∷ (admininstr-CONST I32 (mk-uN v-n)) ∷ (admininstr-VSHIFTOP (ishape-X Jnn-I32 (mk-dim v-N)) vshiftop) ∷ [])) (as (List admininstr) ((admininstr-VCONST V128 c) ∷ []))
  vshiftop-1 : ∀ (c-1 : (uN-fam0 (128))) (v-n : n) (v-N : N) (vshiftop : (vshiftop--fam0 (Jnn-I64) (v-N))) (c : (uN-fam0 (128))) (c'-lst : (List (uN-fam0 (64)))) → 
    (c'-lst ≡ (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-N)) c-1)) →
    (c ≡ (inv-lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-N)) (map (λ (c'-4 : (uN-fam0 (64))) → (fun-vshiftop- (ishape-X Jnn-I64 (mk-dim v-N)) vshiftop c'-4 (mk-uN v-n))) c'-lst))) →
    Step-pure (as (List admininstr) ((admininstr-VCONST V128 c-1) ∷ (admininstr-CONST I32 (mk-uN v-n)) ∷ (admininstr-VSHIFTOP (ishape-X Jnn-I64 (mk-dim v-N)) vshiftop) ∷ [])) (as (List admininstr) ((admininstr-VCONST V128 c) ∷ []))
  vshiftop-2 : ∀ (c-1 : (uN-fam0 (128))) (v-n : n) (v-N : N) (vshiftop : (vshiftop--fam0 (Jnn-I8) (v-N))) (c : (uN-fam0 (128))) (c'-lst : (List (uN-fam0 (8)))) → 
    (c'-lst ≡ (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-N)) c-1)) →
    (c ≡ (inv-lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-N)) (map (λ (c'-6 : (uN-fam0 (8))) → (fun-vshiftop- (ishape-X Jnn-I8 (mk-dim v-N)) vshiftop c'-6 (mk-uN v-n))) c'-lst))) →
    Step-pure (as (List admininstr) ((admininstr-VCONST V128 c-1) ∷ (admininstr-CONST I32 (mk-uN v-n)) ∷ (admininstr-VSHIFTOP (ishape-X Jnn-I8 (mk-dim v-N)) vshiftop) ∷ [])) (as (List admininstr) ((admininstr-VCONST V128 c) ∷ []))
  vshiftop-3 : ∀ (c-1 : (uN-fam0 (128))) (v-n : n) (v-N : N) (vshiftop : (vshiftop--fam0 (Jnn-I16) (v-N))) (c : (uN-fam0 (128))) (c'-lst : (List (uN-fam0 (16)))) → 
    (c'-lst ≡ (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-N)) c-1)) →
    (c ≡ (inv-lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-N)) (map (λ (c'-8 : (uN-fam0 (16))) → (fun-vshiftop- (ishape-X Jnn-I16 (mk-dim v-N)) vshiftop c'-8 (mk-uN v-n))) c'-lst))) →
    Step-pure (as (List admininstr) ((admininstr-VCONST V128 c-1) ∷ (admininstr-CONST I32 (mk-uN v-n)) ∷ (admininstr-VSHIFTOP (ishape-X Jnn-I16 (mk-dim v-N)) vshiftop) ∷ [])) (as (List admininstr) ((admininstr-VCONST V128 c) ∷ []))
  vbitmask-0 : ∀ (c : (uN-fam0 (128))) (v-N : N) (ci : (uN-fam0 (32))) (ci-1-lst : (List (uN-fam0 (32)))) → 
    (ci-1-lst ≡ (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-N)) c)) →
    ((ibits- 32 ci) ≡ ((map (λ (ci-1-34 : (uN-fam0 (32))) → (mk-bit (proj-uN-0 32 (ilt- (lsize (lanetype-Jnn Jnn-I32)) S ci-1-34 (mk-uN 0))))) ci-1-lst) ++ (replicate (coerce {B = ℕ} ((coerce {B = ℕ} 32) – (coerce {B = ℕ} v-N))) (mk-bit 0)))) →
    Step-pure (as (List admininstr) ((admininstr-VCONST V128 c) ∷ (admininstr-VBITMASK (ishape-X Jnn-I32 (mk-dim v-N))) ∷ [])) (as (List admininstr) ((admininstr-CONST I32 (irev- 32 ci)) ∷ []))
  vbitmask-1 : ∀ (c : (uN-fam0 (128))) (v-N : N) (ci : (uN-fam0 (32))) (ci-1-lst : (List (uN-fam0 (64)))) → 
    (ci-1-lst ≡ (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-N)) c)) →
    ((ibits- 32 ci) ≡ ((map (λ (ci-1-36 : (uN-fam0 (64))) → (mk-bit (proj-uN-0 32 (ilt- (lsize (lanetype-Jnn Jnn-I64)) S ci-1-36 (mk-uN 0))))) ci-1-lst) ++ (replicate (coerce {B = ℕ} ((coerce {B = ℕ} 32) – (coerce {B = ℕ} v-N))) (mk-bit 0)))) →
    Step-pure (as (List admininstr) ((admininstr-VCONST V128 c) ∷ (admininstr-VBITMASK (ishape-X Jnn-I64 (mk-dim v-N))) ∷ [])) (as (List admininstr) ((admininstr-CONST I32 (irev- 32 ci)) ∷ []))
  vbitmask-2 : ∀ (c : (uN-fam0 (128))) (v-N : N) (ci : (uN-fam0 (32))) (ci-1-lst : (List (uN-fam0 (8)))) → 
    (ci-1-lst ≡ (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-N)) c)) →
    ((ibits- 32 ci) ≡ ((map (λ (ci-1-38 : (uN-fam0 (8))) → (mk-bit (proj-uN-0 32 (ilt- (lsize (lanetype-Jnn Jnn-I8)) S ci-1-38 (mk-uN 0))))) ci-1-lst) ++ (replicate (coerce {B = ℕ} ((coerce {B = ℕ} 32) – (coerce {B = ℕ} v-N))) (mk-bit 0)))) →
    Step-pure (as (List admininstr) ((admininstr-VCONST V128 c) ∷ (admininstr-VBITMASK (ishape-X Jnn-I8 (mk-dim v-N))) ∷ [])) (as (List admininstr) ((admininstr-CONST I32 (irev- 32 ci)) ∷ []))
  vbitmask-3 : ∀ (c : (uN-fam0 (128))) (v-N : N) (ci : (uN-fam0 (32))) (ci-1-lst : (List (uN-fam0 (16)))) → 
    (ci-1-lst ≡ (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-N)) c)) →
    ((ibits- 32 ci) ≡ ((map (λ (ci-1-40 : (uN-fam0 (16))) → (mk-bit (proj-uN-0 32 (ilt- (lsize (lanetype-Jnn Jnn-I16)) S ci-1-40 (mk-uN 0))))) ci-1-lst) ++ (replicate (coerce {B = ℕ} ((coerce {B = ℕ} 32) – (coerce {B = ℕ} v-N))) (mk-bit 0)))) →
    Step-pure (as (List admininstr) ((admininstr-VCONST V128 c) ∷ (admininstr-VBITMASK (ishape-X Jnn-I16 (mk-dim v-N))) ∷ [])) (as (List admininstr) ((admininstr-CONST I32 (irev- 32 ci)) ∷ []))
  vswizzle-0 : ∀ (c-1 : (uN-fam0 (128))) (c-2 : (uN-fam0 (128))) (v-M : M) (c : (uN-fam0 (128))) (ci-lst : (List (uN-fam0 (8)))) (c'-lst : (List (uN-fam0 (8)))) (k : ℕ) → 
    (ci-lst ≡ (lanes- (X (lanetype-packtype I8) (mk-dim v-M)) c-2)) →
    (c'-lst ≡ ((lanes- (X (lanetype-packtype I8) (mk-dim v-M)) c-1) ++ (replicate (coerce {B = ℕ} ((coerce {B = ℕ} 256) – (coerce {B = ℕ} v-M))) (mk-uN 0)))) →
    holds-upto (λ k-1 → ((proj-uN-0 (psize I8) (ci-lst [ k-1 ]!)) < (length c'-lst))) v-M →
    holds-upto (λ k-1 → (k-1 < (length ci-lst))) v-M →
    (c ≡ (inv-lanes- (X (lanetype-packtype I8) (mk-dim v-M)) (mkseq (λ k-1 → (c'-lst [ (proj-uN-0 (psize I8) (ci-lst [ k-1 ]!)) ]!)) v-M))) →
    Step-pure (as (List admininstr) ((admininstr-VCONST V128 c-1) ∷ (admininstr-VCONST V128 c-2) ∷ (admininstr-VSWIZZLE (ishape-X (Jnn-packtype I8) (mk-dim v-M))) ∷ [])) (as (List admininstr) ((admininstr-VCONST V128 c) ∷ []))
  vswizzle-1 : ∀ (c-1 : (uN-fam0 (128))) (c-2 : (uN-fam0 (128))) (v-M : M) (c : (uN-fam0 (128))) (ci-lst : (List (uN-fam0 (16)))) (c'-lst : (List (uN-fam0 (16)))) (k : ℕ) → 
    (ci-lst ≡ (lanes- (X (lanetype-packtype I16) (mk-dim v-M)) c-2)) →
    (c'-lst ≡ ((lanes- (X (lanetype-packtype I16) (mk-dim v-M)) c-1) ++ (replicate (coerce {B = ℕ} ((coerce {B = ℕ} 256) – (coerce {B = ℕ} v-M))) (mk-uN 0)))) →
    holds-upto (λ k-2 → ((proj-uN-0 (psize I16) (ci-lst [ k-2 ]!)) < (length c'-lst))) v-M →
    holds-upto (λ k-2 → (k-2 < (length ci-lst))) v-M →
    (c ≡ (inv-lanes- (X (lanetype-packtype I16) (mk-dim v-M)) (mkseq (λ k-2 → (c'-lst [ (proj-uN-0 (psize I16) (ci-lst [ k-2 ]!)) ]!)) v-M))) →
    Step-pure (as (List admininstr) ((admininstr-VCONST V128 c-1) ∷ (admininstr-VCONST V128 c-2) ∷ (admininstr-VSWIZZLE (ishape-X (Jnn-packtype I16) (mk-dim v-M))) ∷ [])) (as (List admininstr) ((admininstr-VCONST V128 c) ∷ []))
  vshuffle-0 : ∀ (c-1 : (uN-fam0 (128))) (c-2 : (uN-fam0 (128))) (v-N : N) (i-lst : (List laneidx)) (c : (uN-fam0 (128))) (c'-lst : (List (uN-fam0 (8)))) (k : ℕ) → 
    (c'-lst ≡ ((lanes- (X (lanetype-packtype I8) (mk-dim v-N)) c-1) ++ (lanes- (X (lanetype-packtype I8) (mk-dim v-N)) c-2))) →
    holds-upto (λ k-3 → ((proj-uN-0 8 (i-lst [ k-3 ]!)) < (length c'-lst))) v-N →
    holds-upto (λ k-3 → (k-3 < (length i-lst))) v-N →
    (c ≡ (inv-lanes- (X (lanetype-packtype I8) (mk-dim v-N)) (mkseq (λ k-3 → (c'-lst [ (proj-uN-0 8 (i-lst [ k-3 ]!)) ]!)) v-N))) →
    Step-pure (as (List admininstr) ((admininstr-VCONST V128 c-1) ∷ (admininstr-VCONST V128 c-2) ∷ (admininstr-VSHUFFLE (ishape-X (Jnn-packtype I8) (mk-dim v-N)) i-lst) ∷ [])) (as (List admininstr) ((admininstr-VCONST V128 c) ∷ []))
  vshuffle-1 : ∀ (c-1 : (uN-fam0 (128))) (c-2 : (uN-fam0 (128))) (v-N : N) (i-lst : (List laneidx)) (c : (uN-fam0 (128))) (c'-lst : (List (uN-fam0 (16)))) (k : ℕ) → 
    (c'-lst ≡ ((lanes- (X (lanetype-packtype I16) (mk-dim v-N)) c-1) ++ (lanes- (X (lanetype-packtype I16) (mk-dim v-N)) c-2))) →
    holds-upto (λ k-4 → ((proj-uN-0 8 (i-lst [ k-4 ]!)) < (length c'-lst))) v-N →
    holds-upto (λ k-4 → (k-4 < (length i-lst))) v-N →
    (c ≡ (inv-lanes- (X (lanetype-packtype I16) (mk-dim v-N)) (mkseq (λ k-4 → (c'-lst [ (proj-uN-0 8 (i-lst [ k-4 ]!)) ]!)) v-N))) →
    Step-pure (as (List admininstr) ((admininstr-VCONST V128 c-1) ∷ (admininstr-VCONST V128 c-2) ∷ (admininstr-VSHUFFLE (ishape-X (Jnn-packtype I16) (mk-dim v-N)) i-lst) ∷ [])) (as (List admininstr) ((admininstr-VCONST V128 c) ∷ []))
  Step-pure--vsplat : ∀ (v-Lnn : Lnn) (c-1 : (num- (unpack v-Lnn))) (v-N : N) (c : (uN-fam0 (128))) → 
    (c ≡ (inv-lanes- (X v-Lnn (mk-dim v-N)) (replicate v-N (packnum- v-Lnn c-1)))) →
    Step-pure (as (List admininstr) ((admininstr-CONST (unpack v-Lnn) c-1) ∷ (admininstr-VSPLAT (X v-Lnn (mk-dim v-N))) ∷ [])) (as (List admininstr) ((admininstr-VCONST V128 c) ∷ []))
  vextract-lane-num-0 : ∀ (c-1 : (uN-fam0 (128))) (v-N : N) (i : laneidx) (c-2 : (uN-fam0 (32))) → 
    ((proj-uN-0 8 i) < (length (lanes- (X (lanetype-numtype I32) (mk-dim v-N)) c-1))) →
    (c-2 ≡ ((lanes- (X (lanetype-numtype I32) (mk-dim v-N)) c-1) [ (proj-uN-0 8 i) ]!)) →
    Step-pure (as (List admininstr) ((admininstr-VCONST V128 c-1) ∷ (admininstr-VEXTRACT-LANE (X (lanetype-numtype I32) (mk-dim v-N)) nothing i) ∷ [])) (as (List admininstr) ((admininstr-CONST I32 c-2) ∷ []))
  vextract-lane-num-1 : ∀ (c-1 : (uN-fam0 (128))) (v-N : N) (i : laneidx) (c-2 : (uN-fam0 (64))) → 
    ((proj-uN-0 8 i) < (length (lanes- (X (lanetype-numtype I64) (mk-dim v-N)) c-1))) →
    (c-2 ≡ ((lanes- (X (lanetype-numtype I64) (mk-dim v-N)) c-1) [ (proj-uN-0 8 i) ]!)) →
    Step-pure (as (List admininstr) ((admininstr-VCONST V128 c-1) ∷ (admininstr-VEXTRACT-LANE (X (lanetype-numtype I64) (mk-dim v-N)) nothing i) ∷ [])) (as (List admininstr) ((admininstr-CONST I64 c-2) ∷ []))
  vextract-lane-num-2 : ∀ (c-1 : (uN-fam0 (128))) (v-N : N) (i : laneidx) (c-2 : (fN-fam0 (32))) → 
    ((proj-uN-0 8 i) < (length (lanes- (X (lanetype-numtype F32) (mk-dim v-N)) c-1))) →
    (c-2 ≡ ((lanes- (X (lanetype-numtype F32) (mk-dim v-N)) c-1) [ (proj-uN-0 8 i) ]!)) →
    Step-pure (as (List admininstr) ((admininstr-VCONST V128 c-1) ∷ (admininstr-VEXTRACT-LANE (X (lanetype-numtype F32) (mk-dim v-N)) nothing i) ∷ [])) (as (List admininstr) ((admininstr-CONST F32 c-2) ∷ []))
  vextract-lane-num-3 : ∀ (c-1 : (uN-fam0 (128))) (v-N : N) (i : laneidx) (c-2 : (fN-fam0 (64))) → 
    ((proj-uN-0 8 i) < (length (lanes- (X (lanetype-numtype F64) (mk-dim v-N)) c-1))) →
    (c-2 ≡ ((lanes- (X (lanetype-numtype F64) (mk-dim v-N)) c-1) [ (proj-uN-0 8 i) ]!)) →
    Step-pure (as (List admininstr) ((admininstr-VCONST V128 c-1) ∷ (admininstr-VEXTRACT-LANE (X (lanetype-numtype F64) (mk-dim v-N)) nothing i) ∷ [])) (as (List admininstr) ((admininstr-CONST F64 c-2) ∷ []))
  vextract-lane-pack-0 : ∀ (c-1 : (uN-fam0 (128))) (v-N : N) (v-sx : sx) (i : laneidx) (c-2 : (uN-fam0 (32))) → 
    ((proj-uN-0 8 i) < (length (lanes- (X (lanetype-packtype I8) (mk-dim v-N)) c-1))) →
    (c-2 ≡ (extend-- (psize I8) 32 v-sx ((lanes- (X (lanetype-packtype I8) (mk-dim v-N)) c-1) [ (proj-uN-0 8 i) ]!))) →
    Step-pure (as (List admininstr) ((admininstr-VCONST V128 c-1) ∷ (admininstr-VEXTRACT-LANE (X (lanetype-packtype I8) (mk-dim v-N)) (just v-sx) i) ∷ [])) (as (List admininstr) ((admininstr-CONST I32 c-2) ∷ []))
  vextract-lane-pack-1 : ∀ (c-1 : (uN-fam0 (128))) (v-N : N) (v-sx : sx) (i : laneidx) (c-2 : (uN-fam0 (32))) → 
    ((proj-uN-0 8 i) < (length (lanes- (X (lanetype-packtype I16) (mk-dim v-N)) c-1))) →
    (c-2 ≡ (extend-- (psize I16) 32 v-sx ((lanes- (X (lanetype-packtype I16) (mk-dim v-N)) c-1) [ (proj-uN-0 8 i) ]!))) →
    Step-pure (as (List admininstr) ((admininstr-VCONST V128 c-1) ∷ (admininstr-VEXTRACT-LANE (X (lanetype-packtype I16) (mk-dim v-N)) (just v-sx) i) ∷ [])) (as (List admininstr) ((admininstr-CONST I32 c-2) ∷ []))
  Step-pure--vreplace-lane : ∀ (c-1 : (uN-fam0 (128))) (v-Lnn : Lnn) (c-2 : (num- (unpack v-Lnn))) (v-N : N) (i : laneidx) (c : (uN-fam0 (128))) → 
    (c ≡ (inv-lanes- (X v-Lnn (mk-dim v-N)) (modify (lanes- (X v-Lnn (mk-dim v-N)) c-1) (proj-uN-0 8 i) (λ (_ : (lane- (fun-lanetype (X v-Lnn (mk-dim v-N))))) → (packnum- v-Lnn c-2))))) →
    Step-pure (as (List admininstr) ((admininstr-VCONST V128 c-1) ∷ (admininstr-CONST (unpack v-Lnn) c-2) ∷ (admininstr-VREPLACE-LANE (X v-Lnn (mk-dim v-N)) i) ∷ [])) (as (List admininstr) ((admininstr-VCONST V128 c) ∷ []))
  Step-pure--vextunop : ∀ (c-1 : (uN-fam0 (128))) (sh-1 : ishape) (sh-2 : ishape) (vextunop : (vextunop- sh-1)) (c : (uN-fam0 (128))) → 
    ((vextunop-- sh-1 sh-2 vextunop c-1) ≡ c) →
    Step-pure (as (List admininstr) ((admininstr-VCONST V128 c-1) ∷ (admininstr-VEXTUNOP sh-1 sh-2 vextunop) ∷ [])) (as (List admininstr) ((admininstr-VCONST V128 c) ∷ []))
  Step-pure--vextbinop : ∀ (c-1 : (uN-fam0 (128))) (c-2 : (uN-fam0 (128))) (sh-1 : ishape) (sh-2 : ishape) (vextbinop : (vextbinop- sh-1)) (c : (uN-fam0 (128))) → 
    ((vextbinop-- sh-1 sh-2 vextbinop c-1 c-2) ≡ c) →
    Step-pure (as (List admininstr) ((admininstr-VCONST V128 c-1) ∷ (admininstr-VCONST V128 c-2) ∷ (admininstr-VEXTBINOP sh-1 sh-2 vextbinop) ∷ [])) (as (List admininstr) ((admininstr-VCONST V128 c) ∷ []))
  vnarrow-0 : ∀ (c-1 : (uN-fam0 (128))) (c-2 : (uN-fam0 (128))) (N-2 : N) (N-1 : N) (v-sx : sx) (c : (uN-fam0 (128))) (ci-1-lst : (List (uN-fam0 (32)))) (ci-2-lst : (List (uN-fam0 (32)))) (cj-1-lst : (List (uN-fam0 (32)))) (cj-2-lst : (List (uN-fam0 (32)))) → 
    (ci-1-lst ≡ (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim N-1)) c-1)) →
    (ci-2-lst ≡ (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim N-1)) c-2)) →
    (cj-1-lst ≡ (map (λ (ci-1-42 : (uN-fam0 (32))) → (narrow-- (lsize (lanetype-Jnn Jnn-I32)) (lsize (lanetype-Jnn Jnn-I32)) v-sx ci-1-42)) ci-1-lst)) →
    (cj-2-lst ≡ (map (λ (ci-2-18 : (uN-fam0 (32))) → (narrow-- (lsize (lanetype-Jnn Jnn-I32)) (lsize (lanetype-Jnn Jnn-I32)) v-sx ci-2-18)) ci-2-lst)) →
    (c ≡ (inv-lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim N-2)) (cj-1-lst ++ cj-2-lst))) →
    Step-pure (as (List admininstr) ((admininstr-VCONST V128 c-1) ∷ (admininstr-VCONST V128 c-2) ∷ (admininstr-VNARROW (ishape-X Jnn-I32 (mk-dim N-2)) (ishape-X Jnn-I32 (mk-dim N-1)) v-sx) ∷ [])) (as (List admininstr) ((admininstr-VCONST V128 c) ∷ []))
  vnarrow-1 : ∀ (c-1 : (uN-fam0 (128))) (c-2 : (uN-fam0 (128))) (N-2 : N) (N-1 : N) (v-sx : sx) (c : (uN-fam0 (128))) (ci-1-lst : (List (uN-fam0 (64)))) (ci-2-lst : (List (uN-fam0 (64)))) (cj-1-lst : (List (uN-fam0 (32)))) (cj-2-lst : (List (uN-fam0 (32)))) → 
    (ci-1-lst ≡ (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim N-1)) c-1)) →
    (ci-2-lst ≡ (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim N-1)) c-2)) →
    (cj-1-lst ≡ (map (λ (ci-1-44 : (uN-fam0 (64))) → (narrow-- (lsize (lanetype-Jnn Jnn-I64)) (lsize (lanetype-Jnn Jnn-I32)) v-sx ci-1-44)) ci-1-lst)) →
    (cj-2-lst ≡ (map (λ (ci-2-20 : (uN-fam0 (64))) → (narrow-- (lsize (lanetype-Jnn Jnn-I64)) (lsize (lanetype-Jnn Jnn-I32)) v-sx ci-2-20)) ci-2-lst)) →
    (c ≡ (inv-lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim N-2)) (cj-1-lst ++ cj-2-lst))) →
    Step-pure (as (List admininstr) ((admininstr-VCONST V128 c-1) ∷ (admininstr-VCONST V128 c-2) ∷ (admininstr-VNARROW (ishape-X Jnn-I32 (mk-dim N-2)) (ishape-X Jnn-I64 (mk-dim N-1)) v-sx) ∷ [])) (as (List admininstr) ((admininstr-VCONST V128 c) ∷ []))
  vnarrow-2 : ∀ (c-1 : (uN-fam0 (128))) (c-2 : (uN-fam0 (128))) (N-2 : N) (N-1 : N) (v-sx : sx) (c : (uN-fam0 (128))) (ci-1-lst : (List (uN-fam0 (8)))) (ci-2-lst : (List (uN-fam0 (8)))) (cj-1-lst : (List (uN-fam0 (32)))) (cj-2-lst : (List (uN-fam0 (32)))) → 
    (ci-1-lst ≡ (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim N-1)) c-1)) →
    (ci-2-lst ≡ (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim N-1)) c-2)) →
    (cj-1-lst ≡ (map (λ (ci-1-46 : (uN-fam0 (8))) → (narrow-- (lsize (lanetype-Jnn Jnn-I8)) (lsize (lanetype-Jnn Jnn-I32)) v-sx ci-1-46)) ci-1-lst)) →
    (cj-2-lst ≡ (map (λ (ci-2-22 : (uN-fam0 (8))) → (narrow-- (lsize (lanetype-Jnn Jnn-I8)) (lsize (lanetype-Jnn Jnn-I32)) v-sx ci-2-22)) ci-2-lst)) →
    (c ≡ (inv-lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim N-2)) (cj-1-lst ++ cj-2-lst))) →
    Step-pure (as (List admininstr) ((admininstr-VCONST V128 c-1) ∷ (admininstr-VCONST V128 c-2) ∷ (admininstr-VNARROW (ishape-X Jnn-I32 (mk-dim N-2)) (ishape-X Jnn-I8 (mk-dim N-1)) v-sx) ∷ [])) (as (List admininstr) ((admininstr-VCONST V128 c) ∷ []))
  vnarrow-3 : ∀ (c-1 : (uN-fam0 (128))) (c-2 : (uN-fam0 (128))) (N-2 : N) (N-1 : N) (v-sx : sx) (c : (uN-fam0 (128))) (ci-1-lst : (List (uN-fam0 (16)))) (ci-2-lst : (List (uN-fam0 (16)))) (cj-1-lst : (List (uN-fam0 (32)))) (cj-2-lst : (List (uN-fam0 (32)))) → 
    (ci-1-lst ≡ (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim N-1)) c-1)) →
    (ci-2-lst ≡ (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim N-1)) c-2)) →
    (cj-1-lst ≡ (map (λ (ci-1-48 : (uN-fam0 (16))) → (narrow-- (lsize (lanetype-Jnn Jnn-I16)) (lsize (lanetype-Jnn Jnn-I32)) v-sx ci-1-48)) ci-1-lst)) →
    (cj-2-lst ≡ (map (λ (ci-2-24 : (uN-fam0 (16))) → (narrow-- (lsize (lanetype-Jnn Jnn-I16)) (lsize (lanetype-Jnn Jnn-I32)) v-sx ci-2-24)) ci-2-lst)) →
    (c ≡ (inv-lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim N-2)) (cj-1-lst ++ cj-2-lst))) →
    Step-pure (as (List admininstr) ((admininstr-VCONST V128 c-1) ∷ (admininstr-VCONST V128 c-2) ∷ (admininstr-VNARROW (ishape-X Jnn-I32 (mk-dim N-2)) (ishape-X Jnn-I16 (mk-dim N-1)) v-sx) ∷ [])) (as (List admininstr) ((admininstr-VCONST V128 c) ∷ []))
  vnarrow-4 : ∀ (c-1 : (uN-fam0 (128))) (c-2 : (uN-fam0 (128))) (N-2 : N) (N-1 : N) (v-sx : sx) (c : (uN-fam0 (128))) (ci-1-lst : (List (uN-fam0 (32)))) (ci-2-lst : (List (uN-fam0 (32)))) (cj-1-lst : (List (uN-fam0 (64)))) (cj-2-lst : (List (uN-fam0 (64)))) → 
    (ci-1-lst ≡ (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim N-1)) c-1)) →
    (ci-2-lst ≡ (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim N-1)) c-2)) →
    (cj-1-lst ≡ (map (λ (ci-1-50 : (uN-fam0 (32))) → (narrow-- (lsize (lanetype-Jnn Jnn-I32)) (lsize (lanetype-Jnn Jnn-I64)) v-sx ci-1-50)) ci-1-lst)) →
    (cj-2-lst ≡ (map (λ (ci-2-26 : (uN-fam0 (32))) → (narrow-- (lsize (lanetype-Jnn Jnn-I32)) (lsize (lanetype-Jnn Jnn-I64)) v-sx ci-2-26)) ci-2-lst)) →
    (c ≡ (inv-lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim N-2)) (cj-1-lst ++ cj-2-lst))) →
    Step-pure (as (List admininstr) ((admininstr-VCONST V128 c-1) ∷ (admininstr-VCONST V128 c-2) ∷ (admininstr-VNARROW (ishape-X Jnn-I64 (mk-dim N-2)) (ishape-X Jnn-I32 (mk-dim N-1)) v-sx) ∷ [])) (as (List admininstr) ((admininstr-VCONST V128 c) ∷ []))
  vnarrow-5 : ∀ (c-1 : (uN-fam0 (128))) (c-2 : (uN-fam0 (128))) (N-2 : N) (N-1 : N) (v-sx : sx) (c : (uN-fam0 (128))) (ci-1-lst : (List (uN-fam0 (64)))) (ci-2-lst : (List (uN-fam0 (64)))) (cj-1-lst : (List (uN-fam0 (64)))) (cj-2-lst : (List (uN-fam0 (64)))) → 
    (ci-1-lst ≡ (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim N-1)) c-1)) →
    (ci-2-lst ≡ (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim N-1)) c-2)) →
    (cj-1-lst ≡ (map (λ (ci-1-52 : (uN-fam0 (64))) → (narrow-- (lsize (lanetype-Jnn Jnn-I64)) (lsize (lanetype-Jnn Jnn-I64)) v-sx ci-1-52)) ci-1-lst)) →
    (cj-2-lst ≡ (map (λ (ci-2-28 : (uN-fam0 (64))) → (narrow-- (lsize (lanetype-Jnn Jnn-I64)) (lsize (lanetype-Jnn Jnn-I64)) v-sx ci-2-28)) ci-2-lst)) →
    (c ≡ (inv-lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim N-2)) (cj-1-lst ++ cj-2-lst))) →
    Step-pure (as (List admininstr) ((admininstr-VCONST V128 c-1) ∷ (admininstr-VCONST V128 c-2) ∷ (admininstr-VNARROW (ishape-X Jnn-I64 (mk-dim N-2)) (ishape-X Jnn-I64 (mk-dim N-1)) v-sx) ∷ [])) (as (List admininstr) ((admininstr-VCONST V128 c) ∷ []))
  vnarrow-6 : ∀ (c-1 : (uN-fam0 (128))) (c-2 : (uN-fam0 (128))) (N-2 : N) (N-1 : N) (v-sx : sx) (c : (uN-fam0 (128))) (ci-1-lst : (List (uN-fam0 (8)))) (ci-2-lst : (List (uN-fam0 (8)))) (cj-1-lst : (List (uN-fam0 (64)))) (cj-2-lst : (List (uN-fam0 (64)))) → 
    (ci-1-lst ≡ (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim N-1)) c-1)) →
    (ci-2-lst ≡ (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim N-1)) c-2)) →
    (cj-1-lst ≡ (map (λ (ci-1-54 : (uN-fam0 (8))) → (narrow-- (lsize (lanetype-Jnn Jnn-I8)) (lsize (lanetype-Jnn Jnn-I64)) v-sx ci-1-54)) ci-1-lst)) →
    (cj-2-lst ≡ (map (λ (ci-2-30 : (uN-fam0 (8))) → (narrow-- (lsize (lanetype-Jnn Jnn-I8)) (lsize (lanetype-Jnn Jnn-I64)) v-sx ci-2-30)) ci-2-lst)) →
    (c ≡ (inv-lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim N-2)) (cj-1-lst ++ cj-2-lst))) →
    Step-pure (as (List admininstr) ((admininstr-VCONST V128 c-1) ∷ (admininstr-VCONST V128 c-2) ∷ (admininstr-VNARROW (ishape-X Jnn-I64 (mk-dim N-2)) (ishape-X Jnn-I8 (mk-dim N-1)) v-sx) ∷ [])) (as (List admininstr) ((admininstr-VCONST V128 c) ∷ []))
  vnarrow-7 : ∀ (c-1 : (uN-fam0 (128))) (c-2 : (uN-fam0 (128))) (N-2 : N) (N-1 : N) (v-sx : sx) (c : (uN-fam0 (128))) (ci-1-lst : (List (uN-fam0 (16)))) (ci-2-lst : (List (uN-fam0 (16)))) (cj-1-lst : (List (uN-fam0 (64)))) (cj-2-lst : (List (uN-fam0 (64)))) → 
    (ci-1-lst ≡ (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim N-1)) c-1)) →
    (ci-2-lst ≡ (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim N-1)) c-2)) →
    (cj-1-lst ≡ (map (λ (ci-1-56 : (uN-fam0 (16))) → (narrow-- (lsize (lanetype-Jnn Jnn-I16)) (lsize (lanetype-Jnn Jnn-I64)) v-sx ci-1-56)) ci-1-lst)) →
    (cj-2-lst ≡ (map (λ (ci-2-32 : (uN-fam0 (16))) → (narrow-- (lsize (lanetype-Jnn Jnn-I16)) (lsize (lanetype-Jnn Jnn-I64)) v-sx ci-2-32)) ci-2-lst)) →
    (c ≡ (inv-lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim N-2)) (cj-1-lst ++ cj-2-lst))) →
    Step-pure (as (List admininstr) ((admininstr-VCONST V128 c-1) ∷ (admininstr-VCONST V128 c-2) ∷ (admininstr-VNARROW (ishape-X Jnn-I64 (mk-dim N-2)) (ishape-X Jnn-I16 (mk-dim N-1)) v-sx) ∷ [])) (as (List admininstr) ((admininstr-VCONST V128 c) ∷ []))
  vnarrow-8 : ∀ (c-1 : (uN-fam0 (128))) (c-2 : (uN-fam0 (128))) (N-2 : N) (N-1 : N) (v-sx : sx) (c : (uN-fam0 (128))) (ci-1-lst : (List (uN-fam0 (32)))) (ci-2-lst : (List (uN-fam0 (32)))) (cj-1-lst : (List (uN-fam0 (8)))) (cj-2-lst : (List (uN-fam0 (8)))) → 
    (ci-1-lst ≡ (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim N-1)) c-1)) →
    (ci-2-lst ≡ (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim N-1)) c-2)) →
    (cj-1-lst ≡ (map (λ (ci-1-58 : (uN-fam0 (32))) → (narrow-- (lsize (lanetype-Jnn Jnn-I32)) (lsize (lanetype-Jnn Jnn-I8)) v-sx ci-1-58)) ci-1-lst)) →
    (cj-2-lst ≡ (map (λ (ci-2-34 : (uN-fam0 (32))) → (narrow-- (lsize (lanetype-Jnn Jnn-I32)) (lsize (lanetype-Jnn Jnn-I8)) v-sx ci-2-34)) ci-2-lst)) →
    (c ≡ (inv-lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim N-2)) (cj-1-lst ++ cj-2-lst))) →
    Step-pure (as (List admininstr) ((admininstr-VCONST V128 c-1) ∷ (admininstr-VCONST V128 c-2) ∷ (admininstr-VNARROW (ishape-X Jnn-I8 (mk-dim N-2)) (ishape-X Jnn-I32 (mk-dim N-1)) v-sx) ∷ [])) (as (List admininstr) ((admininstr-VCONST V128 c) ∷ []))
  vnarrow-9 : ∀ (c-1 : (uN-fam0 (128))) (c-2 : (uN-fam0 (128))) (N-2 : N) (N-1 : N) (v-sx : sx) (c : (uN-fam0 (128))) (ci-1-lst : (List (uN-fam0 (64)))) (ci-2-lst : (List (uN-fam0 (64)))) (cj-1-lst : (List (uN-fam0 (8)))) (cj-2-lst : (List (uN-fam0 (8)))) → 
    (ci-1-lst ≡ (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim N-1)) c-1)) →
    (ci-2-lst ≡ (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim N-1)) c-2)) →
    (cj-1-lst ≡ (map (λ (ci-1-60 : (uN-fam0 (64))) → (narrow-- (lsize (lanetype-Jnn Jnn-I64)) (lsize (lanetype-Jnn Jnn-I8)) v-sx ci-1-60)) ci-1-lst)) →
    (cj-2-lst ≡ (map (λ (ci-2-36 : (uN-fam0 (64))) → (narrow-- (lsize (lanetype-Jnn Jnn-I64)) (lsize (lanetype-Jnn Jnn-I8)) v-sx ci-2-36)) ci-2-lst)) →
    (c ≡ (inv-lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim N-2)) (cj-1-lst ++ cj-2-lst))) →
    Step-pure (as (List admininstr) ((admininstr-VCONST V128 c-1) ∷ (admininstr-VCONST V128 c-2) ∷ (admininstr-VNARROW (ishape-X Jnn-I8 (mk-dim N-2)) (ishape-X Jnn-I64 (mk-dim N-1)) v-sx) ∷ [])) (as (List admininstr) ((admininstr-VCONST V128 c) ∷ []))
  vnarrow-10 : ∀ (c-1 : (uN-fam0 (128))) (c-2 : (uN-fam0 (128))) (N-2 : N) (N-1 : N) (v-sx : sx) (c : (uN-fam0 (128))) (ci-1-lst : (List (uN-fam0 (8)))) (ci-2-lst : (List (uN-fam0 (8)))) (cj-1-lst : (List (uN-fam0 (8)))) (cj-2-lst : (List (uN-fam0 (8)))) → 
    (ci-1-lst ≡ (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim N-1)) c-1)) →
    (ci-2-lst ≡ (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim N-1)) c-2)) →
    (cj-1-lst ≡ (map (λ (ci-1-62 : (uN-fam0 (8))) → (narrow-- (lsize (lanetype-Jnn Jnn-I8)) (lsize (lanetype-Jnn Jnn-I8)) v-sx ci-1-62)) ci-1-lst)) →
    (cj-2-lst ≡ (map (λ (ci-2-38 : (uN-fam0 (8))) → (narrow-- (lsize (lanetype-Jnn Jnn-I8)) (lsize (lanetype-Jnn Jnn-I8)) v-sx ci-2-38)) ci-2-lst)) →
    (c ≡ (inv-lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim N-2)) (cj-1-lst ++ cj-2-lst))) →
    Step-pure (as (List admininstr) ((admininstr-VCONST V128 c-1) ∷ (admininstr-VCONST V128 c-2) ∷ (admininstr-VNARROW (ishape-X Jnn-I8 (mk-dim N-2)) (ishape-X Jnn-I8 (mk-dim N-1)) v-sx) ∷ [])) (as (List admininstr) ((admininstr-VCONST V128 c) ∷ []))
  vnarrow-11 : ∀ (c-1 : (uN-fam0 (128))) (c-2 : (uN-fam0 (128))) (N-2 : N) (N-1 : N) (v-sx : sx) (c : (uN-fam0 (128))) (ci-1-lst : (List (uN-fam0 (16)))) (ci-2-lst : (List (uN-fam0 (16)))) (cj-1-lst : (List (uN-fam0 (8)))) (cj-2-lst : (List (uN-fam0 (8)))) → 
    (ci-1-lst ≡ (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim N-1)) c-1)) →
    (ci-2-lst ≡ (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim N-1)) c-2)) →
    (cj-1-lst ≡ (map (λ (ci-1-64 : (uN-fam0 (16))) → (narrow-- (lsize (lanetype-Jnn Jnn-I16)) (lsize (lanetype-Jnn Jnn-I8)) v-sx ci-1-64)) ci-1-lst)) →
    (cj-2-lst ≡ (map (λ (ci-2-40 : (uN-fam0 (16))) → (narrow-- (lsize (lanetype-Jnn Jnn-I16)) (lsize (lanetype-Jnn Jnn-I8)) v-sx ci-2-40)) ci-2-lst)) →
    (c ≡ (inv-lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim N-2)) (cj-1-lst ++ cj-2-lst))) →
    Step-pure (as (List admininstr) ((admininstr-VCONST V128 c-1) ∷ (admininstr-VCONST V128 c-2) ∷ (admininstr-VNARROW (ishape-X Jnn-I8 (mk-dim N-2)) (ishape-X Jnn-I16 (mk-dim N-1)) v-sx) ∷ [])) (as (List admininstr) ((admininstr-VCONST V128 c) ∷ []))
  vnarrow-12 : ∀ (c-1 : (uN-fam0 (128))) (c-2 : (uN-fam0 (128))) (N-2 : N) (N-1 : N) (v-sx : sx) (c : (uN-fam0 (128))) (ci-1-lst : (List (uN-fam0 (32)))) (ci-2-lst : (List (uN-fam0 (32)))) (cj-1-lst : (List (uN-fam0 (16)))) (cj-2-lst : (List (uN-fam0 (16)))) → 
    (ci-1-lst ≡ (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim N-1)) c-1)) →
    (ci-2-lst ≡ (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim N-1)) c-2)) →
    (cj-1-lst ≡ (map (λ (ci-1-66 : (uN-fam0 (32))) → (narrow-- (lsize (lanetype-Jnn Jnn-I32)) (lsize (lanetype-Jnn Jnn-I16)) v-sx ci-1-66)) ci-1-lst)) →
    (cj-2-lst ≡ (map (λ (ci-2-42 : (uN-fam0 (32))) → (narrow-- (lsize (lanetype-Jnn Jnn-I32)) (lsize (lanetype-Jnn Jnn-I16)) v-sx ci-2-42)) ci-2-lst)) →
    (c ≡ (inv-lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim N-2)) (cj-1-lst ++ cj-2-lst))) →
    Step-pure (as (List admininstr) ((admininstr-VCONST V128 c-1) ∷ (admininstr-VCONST V128 c-2) ∷ (admininstr-VNARROW (ishape-X Jnn-I16 (mk-dim N-2)) (ishape-X Jnn-I32 (mk-dim N-1)) v-sx) ∷ [])) (as (List admininstr) ((admininstr-VCONST V128 c) ∷ []))
  vnarrow-13 : ∀ (c-1 : (uN-fam0 (128))) (c-2 : (uN-fam0 (128))) (N-2 : N) (N-1 : N) (v-sx : sx) (c : (uN-fam0 (128))) (ci-1-lst : (List (uN-fam0 (64)))) (ci-2-lst : (List (uN-fam0 (64)))) (cj-1-lst : (List (uN-fam0 (16)))) (cj-2-lst : (List (uN-fam0 (16)))) → 
    (ci-1-lst ≡ (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim N-1)) c-1)) →
    (ci-2-lst ≡ (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim N-1)) c-2)) →
    (cj-1-lst ≡ (map (λ (ci-1-68 : (uN-fam0 (64))) → (narrow-- (lsize (lanetype-Jnn Jnn-I64)) (lsize (lanetype-Jnn Jnn-I16)) v-sx ci-1-68)) ci-1-lst)) →
    (cj-2-lst ≡ (map (λ (ci-2-44 : (uN-fam0 (64))) → (narrow-- (lsize (lanetype-Jnn Jnn-I64)) (lsize (lanetype-Jnn Jnn-I16)) v-sx ci-2-44)) ci-2-lst)) →
    (c ≡ (inv-lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim N-2)) (cj-1-lst ++ cj-2-lst))) →
    Step-pure (as (List admininstr) ((admininstr-VCONST V128 c-1) ∷ (admininstr-VCONST V128 c-2) ∷ (admininstr-VNARROW (ishape-X Jnn-I16 (mk-dim N-2)) (ishape-X Jnn-I64 (mk-dim N-1)) v-sx) ∷ [])) (as (List admininstr) ((admininstr-VCONST V128 c) ∷ []))
  vnarrow-14 : ∀ (c-1 : (uN-fam0 (128))) (c-2 : (uN-fam0 (128))) (N-2 : N) (N-1 : N) (v-sx : sx) (c : (uN-fam0 (128))) (ci-1-lst : (List (uN-fam0 (8)))) (ci-2-lst : (List (uN-fam0 (8)))) (cj-1-lst : (List (uN-fam0 (16)))) (cj-2-lst : (List (uN-fam0 (16)))) → 
    (ci-1-lst ≡ (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim N-1)) c-1)) →
    (ci-2-lst ≡ (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim N-1)) c-2)) →
    (cj-1-lst ≡ (map (λ (ci-1-70 : (uN-fam0 (8))) → (narrow-- (lsize (lanetype-Jnn Jnn-I8)) (lsize (lanetype-Jnn Jnn-I16)) v-sx ci-1-70)) ci-1-lst)) →
    (cj-2-lst ≡ (map (λ (ci-2-46 : (uN-fam0 (8))) → (narrow-- (lsize (lanetype-Jnn Jnn-I8)) (lsize (lanetype-Jnn Jnn-I16)) v-sx ci-2-46)) ci-2-lst)) →
    (c ≡ (inv-lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim N-2)) (cj-1-lst ++ cj-2-lst))) →
    Step-pure (as (List admininstr) ((admininstr-VCONST V128 c-1) ∷ (admininstr-VCONST V128 c-2) ∷ (admininstr-VNARROW (ishape-X Jnn-I16 (mk-dim N-2)) (ishape-X Jnn-I8 (mk-dim N-1)) v-sx) ∷ [])) (as (List admininstr) ((admininstr-VCONST V128 c) ∷ []))
  vnarrow-15 : ∀ (c-1 : (uN-fam0 (128))) (c-2 : (uN-fam0 (128))) (N-2 : N) (N-1 : N) (v-sx : sx) (c : (uN-fam0 (128))) (ci-1-lst : (List (uN-fam0 (16)))) (ci-2-lst : (List (uN-fam0 (16)))) (cj-1-lst : (List (uN-fam0 (16)))) (cj-2-lst : (List (uN-fam0 (16)))) → 
    (ci-1-lst ≡ (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim N-1)) c-1)) →
    (ci-2-lst ≡ (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim N-1)) c-2)) →
    (cj-1-lst ≡ (map (λ (ci-1-72 : (uN-fam0 (16))) → (narrow-- (lsize (lanetype-Jnn Jnn-I16)) (lsize (lanetype-Jnn Jnn-I16)) v-sx ci-1-72)) ci-1-lst)) →
    (cj-2-lst ≡ (map (λ (ci-2-48 : (uN-fam0 (16))) → (narrow-- (lsize (lanetype-Jnn Jnn-I16)) (lsize (lanetype-Jnn Jnn-I16)) v-sx ci-2-48)) ci-2-lst)) →
    (c ≡ (inv-lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim N-2)) (cj-1-lst ++ cj-2-lst))) →
    Step-pure (as (List admininstr) ((admininstr-VCONST V128 c-1) ∷ (admininstr-VCONST V128 c-2) ∷ (admininstr-VNARROW (ishape-X Jnn-I16 (mk-dim N-2)) (ishape-X Jnn-I16 (mk-dim N-1)) v-sx) ∷ [])) (as (List admininstr) ((admininstr-VCONST V128 c) ∷ []))
  vcvtop-full : ∀ (c-1 : (uN-fam0 (128))) (Lnn-2 : Lnn) (v-M : M) (Lnn-1 : Lnn) (v-vcvtop : vcvtop) (c : (uN-fam0 (128))) (ci-lst : (List (lane- (fun-lanetype (X Lnn-1 (mk-dim v-M)))))) (cj-lst-lst : (List (List (lane- Lnn-2)))) → 
    (((halfop v-vcvtop) ≡ nothing) × ((zeroop v-vcvtop) ≡ nothing)) →
    (ci-lst ≡ (lanes- (X Lnn-1 (mk-dim v-M)) c-1)) →
    (cj-lst-lst ≡ (setproduct- (lane- Lnn-2) (map (λ (ci : (lane- (fun-lanetype (X Lnn-1 (mk-dim v-M))))) → (vcvtop-- (X Lnn-1 (mk-dim v-M)) (X Lnn-2 (mk-dim v-M)) v-vcvtop ci)) ci-lst))) →
    ((length (map (λ (cj-lst : (List (lane- (fun-lanetype (X Lnn-2 (mk-dim v-M)))))) → (inv-lanes- (X Lnn-2 (mk-dim v-M)) cj-lst)) cj-lst-lst)) > 0) →
    (c ∈ (map (λ (cj-lst : (List (lane- (fun-lanetype (X Lnn-2 (mk-dim v-M)))))) → (inv-lanes- (X Lnn-2 (mk-dim v-M)) cj-lst)) cj-lst-lst)) →
    Step-pure (as (List admininstr) ((admininstr-VCONST V128 c-1) ∷ (admininstr-VCVTOP (X Lnn-2 (mk-dim v-M)) (X Lnn-1 (mk-dim v-M)) v-vcvtop) ∷ [])) (as (List admininstr) ((admininstr-VCONST V128 c) ∷ []))
  vcvtop-half : ∀ (c-1 : (uN-fam0 (128))) (Lnn-2 : Lnn) (M-2 : M) (Lnn-1 : Lnn) (M-1 : M) (v-vcvtop : vcvtop) (c : (uN-fam0 (128))) (v-half : half) (ci-lst : (List (lane- (fun-lanetype (X Lnn-1 (mk-dim M-1)))))) (cj-lst-lst : (List (List (lane- Lnn-2)))) → 
    ((halfop v-vcvtop) ≡ (just v-half)) →
    (ci-lst ≡ (slice (lanes- (X Lnn-1 (mk-dim M-1)) c-1) (fun-half v-half 0 M-2) M-2)) →
    (cj-lst-lst ≡ (setproduct- (lane- Lnn-2) (map (λ (ci : (lane- (fun-lanetype (X Lnn-1 (mk-dim M-1))))) → (vcvtop-- (X Lnn-1 (mk-dim M-1)) (X Lnn-2 (mk-dim M-2)) v-vcvtop ci)) ci-lst))) →
    ((length (map (λ (cj-lst : (List (lane- (fun-lanetype (X Lnn-2 (mk-dim M-2)))))) → (inv-lanes- (X Lnn-2 (mk-dim M-2)) cj-lst)) cj-lst-lst)) > 0) →
    (c ∈ (map (λ (cj-lst : (List (lane- (fun-lanetype (X Lnn-2 (mk-dim M-2)))))) → (inv-lanes- (X Lnn-2 (mk-dim M-2)) cj-lst)) cj-lst-lst)) →
    Step-pure (as (List admininstr) ((admininstr-VCONST V128 c-1) ∷ (admininstr-VCVTOP (X Lnn-2 (mk-dim M-2)) (X Lnn-1 (mk-dim M-1)) v-vcvtop) ∷ [])) (as (List admininstr) ((admininstr-VCONST V128 c) ∷ []))
  vcvtop-zero-0 : ∀ (c-1 : (uN-fam0 (128))) (M-2 : M) (M-1 : M) (v-vcvtop : vcvtop) (c : (uN-fam0 (128))) (ci-lst : (List (uN-fam0 (32)))) (cj-lst-lst : (List (List (uN-fam0 (32))))) → 
    ((zeroop v-vcvtop) ≡ (just ZERO)) →
    (ci-lst ≡ (lanes- (X (lanetype-numtype I32) (mk-dim M-1)) c-1)) →
    (cj-lst-lst ≡ (setproduct- (uN-fam0 (32)) ((map (λ (ci-14 : (uN-fam0 (32))) → (vcvtop-- (X (lanetype-numtype I32) (mk-dim M-1)) (X (lanetype-numtype I32) (mk-dim M-2)) v-vcvtop ci-14)) ci-lst) ++ (replicate M-1 ((fun-zero I32) ∷ []))))) →
    ((length (map (λ (cj-lst-2 : (List (uN-fam0 (32)))) → (inv-lanes- (X (lanetype-numtype I32) (mk-dim M-2)) cj-lst-2)) cj-lst-lst)) > 0) →
    (c ∈ (map (λ (cj-lst-2 : (List (uN-fam0 (32)))) → (inv-lanes- (X (lanetype-numtype I32) (mk-dim M-2)) cj-lst-2)) cj-lst-lst)) →
    Step-pure (as (List admininstr) ((admininstr-VCONST V128 c-1) ∷ (admininstr-VCVTOP (X (lanetype-numtype I32) (mk-dim M-2)) (X (lanetype-numtype I32) (mk-dim M-1)) v-vcvtop) ∷ [])) (as (List admininstr) ((admininstr-VCONST V128 c) ∷ []))
  vcvtop-zero-1 : ∀ (c-1 : (uN-fam0 (128))) (M-2 : M) (M-1 : M) (v-vcvtop : vcvtop) (c : (uN-fam0 (128))) (ci-lst : (List (uN-fam0 (64)))) (cj-lst-lst : (List (List (uN-fam0 (32))))) → 
    ((zeroop v-vcvtop) ≡ (just ZERO)) →
    (ci-lst ≡ (lanes- (X (lanetype-numtype I64) (mk-dim M-1)) c-1)) →
    (cj-lst-lst ≡ (setproduct- (uN-fam0 (32)) ((map (λ (ci-16 : (uN-fam0 (64))) → (vcvtop-- (X (lanetype-numtype I64) (mk-dim M-1)) (X (lanetype-numtype I32) (mk-dim M-2)) v-vcvtop ci-16)) ci-lst) ++ (replicate M-1 ((fun-zero I32) ∷ []))))) →
    ((length (map (λ (cj-lst-4 : (List (uN-fam0 (32)))) → (inv-lanes- (X (lanetype-numtype I32) (mk-dim M-2)) cj-lst-4)) cj-lst-lst)) > 0) →
    (c ∈ (map (λ (cj-lst-4 : (List (uN-fam0 (32)))) → (inv-lanes- (X (lanetype-numtype I32) (mk-dim M-2)) cj-lst-4)) cj-lst-lst)) →
    Step-pure (as (List admininstr) ((admininstr-VCONST V128 c-1) ∷ (admininstr-VCVTOP (X (lanetype-numtype I32) (mk-dim M-2)) (X (lanetype-numtype I64) (mk-dim M-1)) v-vcvtop) ∷ [])) (as (List admininstr) ((admininstr-VCONST V128 c) ∷ []))
  vcvtop-zero-2 : ∀ (c-1 : (uN-fam0 (128))) (M-2 : M) (M-1 : M) (v-vcvtop : vcvtop) (c : (uN-fam0 (128))) (ci-lst : (List (fN-fam0 (32)))) (cj-lst-lst : (List (List (uN-fam0 (32))))) → 
    ((zeroop v-vcvtop) ≡ (just ZERO)) →
    (ci-lst ≡ (lanes- (X (lanetype-numtype F32) (mk-dim M-1)) c-1)) →
    (cj-lst-lst ≡ (setproduct- (uN-fam0 (32)) ((map (λ (ci-18 : (fN-fam0 (32))) → (vcvtop-- (X (lanetype-numtype F32) (mk-dim M-1)) (X (lanetype-numtype I32) (mk-dim M-2)) v-vcvtop ci-18)) ci-lst) ++ (replicate M-1 ((fun-zero I32) ∷ []))))) →
    ((length (map (λ (cj-lst-6 : (List (uN-fam0 (32)))) → (inv-lanes- (X (lanetype-numtype I32) (mk-dim M-2)) cj-lst-6)) cj-lst-lst)) > 0) →
    (c ∈ (map (λ (cj-lst-6 : (List (uN-fam0 (32)))) → (inv-lanes- (X (lanetype-numtype I32) (mk-dim M-2)) cj-lst-6)) cj-lst-lst)) →
    Step-pure (as (List admininstr) ((admininstr-VCONST V128 c-1) ∷ (admininstr-VCVTOP (X (lanetype-numtype I32) (mk-dim M-2)) (X (lanetype-numtype F32) (mk-dim M-1)) v-vcvtop) ∷ [])) (as (List admininstr) ((admininstr-VCONST V128 c) ∷ []))
  vcvtop-zero-3 : ∀ (c-1 : (uN-fam0 (128))) (M-2 : M) (M-1 : M) (v-vcvtop : vcvtop) (c : (uN-fam0 (128))) (ci-lst : (List (fN-fam0 (64)))) (cj-lst-lst : (List (List (uN-fam0 (32))))) → 
    ((zeroop v-vcvtop) ≡ (just ZERO)) →
    (ci-lst ≡ (lanes- (X (lanetype-numtype F64) (mk-dim M-1)) c-1)) →
    (cj-lst-lst ≡ (setproduct- (uN-fam0 (32)) ((map (λ (ci-20 : (fN-fam0 (64))) → (vcvtop-- (X (lanetype-numtype F64) (mk-dim M-1)) (X (lanetype-numtype I32) (mk-dim M-2)) v-vcvtop ci-20)) ci-lst) ++ (replicate M-1 ((fun-zero I32) ∷ []))))) →
    ((length (map (λ (cj-lst-8 : (List (uN-fam0 (32)))) → (inv-lanes- (X (lanetype-numtype I32) (mk-dim M-2)) cj-lst-8)) cj-lst-lst)) > 0) →
    (c ∈ (map (λ (cj-lst-8 : (List (uN-fam0 (32)))) → (inv-lanes- (X (lanetype-numtype I32) (mk-dim M-2)) cj-lst-8)) cj-lst-lst)) →
    Step-pure (as (List admininstr) ((admininstr-VCONST V128 c-1) ∷ (admininstr-VCVTOP (X (lanetype-numtype I32) (mk-dim M-2)) (X (lanetype-numtype F64) (mk-dim M-1)) v-vcvtop) ∷ [])) (as (List admininstr) ((admininstr-VCONST V128 c) ∷ []))
  vcvtop-zero-4 : ∀ (c-1 : (uN-fam0 (128))) (M-2 : M) (M-1 : M) (v-vcvtop : vcvtop) (c : (uN-fam0 (128))) (ci-lst : (List (uN-fam0 (32)))) (cj-lst-lst : (List (List (uN-fam0 (64))))) → 
    ((zeroop v-vcvtop) ≡ (just ZERO)) →
    (ci-lst ≡ (lanes- (X (lanetype-numtype I32) (mk-dim M-1)) c-1)) →
    (cj-lst-lst ≡ (setproduct- (uN-fam0 (64)) ((map (λ (ci-22 : (uN-fam0 (32))) → (vcvtop-- (X (lanetype-numtype I32) (mk-dim M-1)) (X (lanetype-numtype I64) (mk-dim M-2)) v-vcvtop ci-22)) ci-lst) ++ (replicate M-1 ((fun-zero I64) ∷ []))))) →
    ((length (map (λ (cj-lst-10 : (List (uN-fam0 (64)))) → (inv-lanes- (X (lanetype-numtype I64) (mk-dim M-2)) cj-lst-10)) cj-lst-lst)) > 0) →
    (c ∈ (map (λ (cj-lst-10 : (List (uN-fam0 (64)))) → (inv-lanes- (X (lanetype-numtype I64) (mk-dim M-2)) cj-lst-10)) cj-lst-lst)) →
    Step-pure (as (List admininstr) ((admininstr-VCONST V128 c-1) ∷ (admininstr-VCVTOP (X (lanetype-numtype I64) (mk-dim M-2)) (X (lanetype-numtype I32) (mk-dim M-1)) v-vcvtop) ∷ [])) (as (List admininstr) ((admininstr-VCONST V128 c) ∷ []))
  vcvtop-zero-5 : ∀ (c-1 : (uN-fam0 (128))) (M-2 : M) (M-1 : M) (v-vcvtop : vcvtop) (c : (uN-fam0 (128))) (ci-lst : (List (uN-fam0 (64)))) (cj-lst-lst : (List (List (uN-fam0 (64))))) → 
    ((zeroop v-vcvtop) ≡ (just ZERO)) →
    (ci-lst ≡ (lanes- (X (lanetype-numtype I64) (mk-dim M-1)) c-1)) →
    (cj-lst-lst ≡ (setproduct- (uN-fam0 (64)) ((map (λ (ci-24 : (uN-fam0 (64))) → (vcvtop-- (X (lanetype-numtype I64) (mk-dim M-1)) (X (lanetype-numtype I64) (mk-dim M-2)) v-vcvtop ci-24)) ci-lst) ++ (replicate M-1 ((fun-zero I64) ∷ []))))) →
    ((length (map (λ (cj-lst-12 : (List (uN-fam0 (64)))) → (inv-lanes- (X (lanetype-numtype I64) (mk-dim M-2)) cj-lst-12)) cj-lst-lst)) > 0) →
    (c ∈ (map (λ (cj-lst-12 : (List (uN-fam0 (64)))) → (inv-lanes- (X (lanetype-numtype I64) (mk-dim M-2)) cj-lst-12)) cj-lst-lst)) →
    Step-pure (as (List admininstr) ((admininstr-VCONST V128 c-1) ∷ (admininstr-VCVTOP (X (lanetype-numtype I64) (mk-dim M-2)) (X (lanetype-numtype I64) (mk-dim M-1)) v-vcvtop) ∷ [])) (as (List admininstr) ((admininstr-VCONST V128 c) ∷ []))
  vcvtop-zero-6 : ∀ (c-1 : (uN-fam0 (128))) (M-2 : M) (M-1 : M) (v-vcvtop : vcvtop) (c : (uN-fam0 (128))) (ci-lst : (List (fN-fam0 (32)))) (cj-lst-lst : (List (List (uN-fam0 (64))))) → 
    ((zeroop v-vcvtop) ≡ (just ZERO)) →
    (ci-lst ≡ (lanes- (X (lanetype-numtype F32) (mk-dim M-1)) c-1)) →
    (cj-lst-lst ≡ (setproduct- (uN-fam0 (64)) ((map (λ (ci-26 : (fN-fam0 (32))) → (vcvtop-- (X (lanetype-numtype F32) (mk-dim M-1)) (X (lanetype-numtype I64) (mk-dim M-2)) v-vcvtop ci-26)) ci-lst) ++ (replicate M-1 ((fun-zero I64) ∷ []))))) →
    ((length (map (λ (cj-lst-14 : (List (uN-fam0 (64)))) → (inv-lanes- (X (lanetype-numtype I64) (mk-dim M-2)) cj-lst-14)) cj-lst-lst)) > 0) →
    (c ∈ (map (λ (cj-lst-14 : (List (uN-fam0 (64)))) → (inv-lanes- (X (lanetype-numtype I64) (mk-dim M-2)) cj-lst-14)) cj-lst-lst)) →
    Step-pure (as (List admininstr) ((admininstr-VCONST V128 c-1) ∷ (admininstr-VCVTOP (X (lanetype-numtype I64) (mk-dim M-2)) (X (lanetype-numtype F32) (mk-dim M-1)) v-vcvtop) ∷ [])) (as (List admininstr) ((admininstr-VCONST V128 c) ∷ []))
  vcvtop-zero-7 : ∀ (c-1 : (uN-fam0 (128))) (M-2 : M) (M-1 : M) (v-vcvtop : vcvtop) (c : (uN-fam0 (128))) (ci-lst : (List (fN-fam0 (64)))) (cj-lst-lst : (List (List (uN-fam0 (64))))) → 
    ((zeroop v-vcvtop) ≡ (just ZERO)) →
    (ci-lst ≡ (lanes- (X (lanetype-numtype F64) (mk-dim M-1)) c-1)) →
    (cj-lst-lst ≡ (setproduct- (uN-fam0 (64)) ((map (λ (ci-28 : (fN-fam0 (64))) → (vcvtop-- (X (lanetype-numtype F64) (mk-dim M-1)) (X (lanetype-numtype I64) (mk-dim M-2)) v-vcvtop ci-28)) ci-lst) ++ (replicate M-1 ((fun-zero I64) ∷ []))))) →
    ((length (map (λ (cj-lst-16 : (List (uN-fam0 (64)))) → (inv-lanes- (X (lanetype-numtype I64) (mk-dim M-2)) cj-lst-16)) cj-lst-lst)) > 0) →
    (c ∈ (map (λ (cj-lst-16 : (List (uN-fam0 (64)))) → (inv-lanes- (X (lanetype-numtype I64) (mk-dim M-2)) cj-lst-16)) cj-lst-lst)) →
    Step-pure (as (List admininstr) ((admininstr-VCONST V128 c-1) ∷ (admininstr-VCVTOP (X (lanetype-numtype I64) (mk-dim M-2)) (X (lanetype-numtype F64) (mk-dim M-1)) v-vcvtop) ∷ [])) (as (List admininstr) ((admininstr-VCONST V128 c) ∷ []))
  vcvtop-zero-8 : ∀ (c-1 : (uN-fam0 (128))) (M-2 : M) (M-1 : M) (v-vcvtop : vcvtop) (c : (uN-fam0 (128))) (ci-lst : (List (uN-fam0 (32)))) (cj-lst-lst : (List (List (fN-fam0 (32))))) → 
    ((zeroop v-vcvtop) ≡ (just ZERO)) →
    (ci-lst ≡ (lanes- (X (lanetype-numtype I32) (mk-dim M-1)) c-1)) →
    (cj-lst-lst ≡ (setproduct- (fN-fam0 (32)) ((map (λ (ci-30 : (uN-fam0 (32))) → (vcvtop-- (X (lanetype-numtype I32) (mk-dim M-1)) (X (lanetype-numtype F32) (mk-dim M-2)) v-vcvtop ci-30)) ci-lst) ++ (replicate M-1 ((fun-zero F32) ∷ []))))) →
    ((length (map (λ (cj-lst-18 : (List (fN-fam0 (32)))) → (inv-lanes- (X (lanetype-numtype F32) (mk-dim M-2)) cj-lst-18)) cj-lst-lst)) > 0) →
    (c ∈ (map (λ (cj-lst-18 : (List (fN-fam0 (32)))) → (inv-lanes- (X (lanetype-numtype F32) (mk-dim M-2)) cj-lst-18)) cj-lst-lst)) →
    Step-pure (as (List admininstr) ((admininstr-VCONST V128 c-1) ∷ (admininstr-VCVTOP (X (lanetype-numtype F32) (mk-dim M-2)) (X (lanetype-numtype I32) (mk-dim M-1)) v-vcvtop) ∷ [])) (as (List admininstr) ((admininstr-VCONST V128 c) ∷ []))
  vcvtop-zero-9 : ∀ (c-1 : (uN-fam0 (128))) (M-2 : M) (M-1 : M) (v-vcvtop : vcvtop) (c : (uN-fam0 (128))) (ci-lst : (List (uN-fam0 (64)))) (cj-lst-lst : (List (List (fN-fam0 (32))))) → 
    ((zeroop v-vcvtop) ≡ (just ZERO)) →
    (ci-lst ≡ (lanes- (X (lanetype-numtype I64) (mk-dim M-1)) c-1)) →
    (cj-lst-lst ≡ (setproduct- (fN-fam0 (32)) ((map (λ (ci-32 : (uN-fam0 (64))) → (vcvtop-- (X (lanetype-numtype I64) (mk-dim M-1)) (X (lanetype-numtype F32) (mk-dim M-2)) v-vcvtop ci-32)) ci-lst) ++ (replicate M-1 ((fun-zero F32) ∷ []))))) →
    ((length (map (λ (cj-lst-20 : (List (fN-fam0 (32)))) → (inv-lanes- (X (lanetype-numtype F32) (mk-dim M-2)) cj-lst-20)) cj-lst-lst)) > 0) →
    (c ∈ (map (λ (cj-lst-20 : (List (fN-fam0 (32)))) → (inv-lanes- (X (lanetype-numtype F32) (mk-dim M-2)) cj-lst-20)) cj-lst-lst)) →
    Step-pure (as (List admininstr) ((admininstr-VCONST V128 c-1) ∷ (admininstr-VCVTOP (X (lanetype-numtype F32) (mk-dim M-2)) (X (lanetype-numtype I64) (mk-dim M-1)) v-vcvtop) ∷ [])) (as (List admininstr) ((admininstr-VCONST V128 c) ∷ []))
  vcvtop-zero-10 : ∀ (c-1 : (uN-fam0 (128))) (M-2 : M) (M-1 : M) (v-vcvtop : vcvtop) (c : (uN-fam0 (128))) (ci-lst : (List (fN-fam0 (32)))) (cj-lst-lst : (List (List (fN-fam0 (32))))) → 
    ((zeroop v-vcvtop) ≡ (just ZERO)) →
    (ci-lst ≡ (lanes- (X (lanetype-numtype F32) (mk-dim M-1)) c-1)) →
    (cj-lst-lst ≡ (setproduct- (fN-fam0 (32)) ((map (λ (ci-34 : (fN-fam0 (32))) → (vcvtop-- (X (lanetype-numtype F32) (mk-dim M-1)) (X (lanetype-numtype F32) (mk-dim M-2)) v-vcvtop ci-34)) ci-lst) ++ (replicate M-1 ((fun-zero F32) ∷ []))))) →
    ((length (map (λ (cj-lst-22 : (List (fN-fam0 (32)))) → (inv-lanes- (X (lanetype-numtype F32) (mk-dim M-2)) cj-lst-22)) cj-lst-lst)) > 0) →
    (c ∈ (map (λ (cj-lst-22 : (List (fN-fam0 (32)))) → (inv-lanes- (X (lanetype-numtype F32) (mk-dim M-2)) cj-lst-22)) cj-lst-lst)) →
    Step-pure (as (List admininstr) ((admininstr-VCONST V128 c-1) ∷ (admininstr-VCVTOP (X (lanetype-numtype F32) (mk-dim M-2)) (X (lanetype-numtype F32) (mk-dim M-1)) v-vcvtop) ∷ [])) (as (List admininstr) ((admininstr-VCONST V128 c) ∷ []))
  vcvtop-zero-11 : ∀ (c-1 : (uN-fam0 (128))) (M-2 : M) (M-1 : M) (v-vcvtop : vcvtop) (c : (uN-fam0 (128))) (ci-lst : (List (fN-fam0 (64)))) (cj-lst-lst : (List (List (fN-fam0 (32))))) → 
    ((zeroop v-vcvtop) ≡ (just ZERO)) →
    (ci-lst ≡ (lanes- (X (lanetype-numtype F64) (mk-dim M-1)) c-1)) →
    (cj-lst-lst ≡ (setproduct- (fN-fam0 (32)) ((map (λ (ci-36 : (fN-fam0 (64))) → (vcvtop-- (X (lanetype-numtype F64) (mk-dim M-1)) (X (lanetype-numtype F32) (mk-dim M-2)) v-vcvtop ci-36)) ci-lst) ++ (replicate M-1 ((fun-zero F32) ∷ []))))) →
    ((length (map (λ (cj-lst-24 : (List (fN-fam0 (32)))) → (inv-lanes- (X (lanetype-numtype F32) (mk-dim M-2)) cj-lst-24)) cj-lst-lst)) > 0) →
    (c ∈ (map (λ (cj-lst-24 : (List (fN-fam0 (32)))) → (inv-lanes- (X (lanetype-numtype F32) (mk-dim M-2)) cj-lst-24)) cj-lst-lst)) →
    Step-pure (as (List admininstr) ((admininstr-VCONST V128 c-1) ∷ (admininstr-VCVTOP (X (lanetype-numtype F32) (mk-dim M-2)) (X (lanetype-numtype F64) (mk-dim M-1)) v-vcvtop) ∷ [])) (as (List admininstr) ((admininstr-VCONST V128 c) ∷ []))
  vcvtop-zero-12 : ∀ (c-1 : (uN-fam0 (128))) (M-2 : M) (M-1 : M) (v-vcvtop : vcvtop) (c : (uN-fam0 (128))) (ci-lst : (List (uN-fam0 (32)))) (cj-lst-lst : (List (List (fN-fam0 (64))))) → 
    ((zeroop v-vcvtop) ≡ (just ZERO)) →
    (ci-lst ≡ (lanes- (X (lanetype-numtype I32) (mk-dim M-1)) c-1)) →
    (cj-lst-lst ≡ (setproduct- (fN-fam0 (64)) ((map (λ (ci-38 : (uN-fam0 (32))) → (vcvtop-- (X (lanetype-numtype I32) (mk-dim M-1)) (X (lanetype-numtype F64) (mk-dim M-2)) v-vcvtop ci-38)) ci-lst) ++ (replicate M-1 ((fun-zero F64) ∷ []))))) →
    ((length (map (λ (cj-lst-26 : (List (fN-fam0 (64)))) → (inv-lanes- (X (lanetype-numtype F64) (mk-dim M-2)) cj-lst-26)) cj-lst-lst)) > 0) →
    (c ∈ (map (λ (cj-lst-26 : (List (fN-fam0 (64)))) → (inv-lanes- (X (lanetype-numtype F64) (mk-dim M-2)) cj-lst-26)) cj-lst-lst)) →
    Step-pure (as (List admininstr) ((admininstr-VCONST V128 c-1) ∷ (admininstr-VCVTOP (X (lanetype-numtype F64) (mk-dim M-2)) (X (lanetype-numtype I32) (mk-dim M-1)) v-vcvtop) ∷ [])) (as (List admininstr) ((admininstr-VCONST V128 c) ∷ []))
  vcvtop-zero-13 : ∀ (c-1 : (uN-fam0 (128))) (M-2 : M) (M-1 : M) (v-vcvtop : vcvtop) (c : (uN-fam0 (128))) (ci-lst : (List (uN-fam0 (64)))) (cj-lst-lst : (List (List (fN-fam0 (64))))) → 
    ((zeroop v-vcvtop) ≡ (just ZERO)) →
    (ci-lst ≡ (lanes- (X (lanetype-numtype I64) (mk-dim M-1)) c-1)) →
    (cj-lst-lst ≡ (setproduct- (fN-fam0 (64)) ((map (λ (ci-40 : (uN-fam0 (64))) → (vcvtop-- (X (lanetype-numtype I64) (mk-dim M-1)) (X (lanetype-numtype F64) (mk-dim M-2)) v-vcvtop ci-40)) ci-lst) ++ (replicate M-1 ((fun-zero F64) ∷ []))))) →
    ((length (map (λ (cj-lst-28 : (List (fN-fam0 (64)))) → (inv-lanes- (X (lanetype-numtype F64) (mk-dim M-2)) cj-lst-28)) cj-lst-lst)) > 0) →
    (c ∈ (map (λ (cj-lst-28 : (List (fN-fam0 (64)))) → (inv-lanes- (X (lanetype-numtype F64) (mk-dim M-2)) cj-lst-28)) cj-lst-lst)) →
    Step-pure (as (List admininstr) ((admininstr-VCONST V128 c-1) ∷ (admininstr-VCVTOP (X (lanetype-numtype F64) (mk-dim M-2)) (X (lanetype-numtype I64) (mk-dim M-1)) v-vcvtop) ∷ [])) (as (List admininstr) ((admininstr-VCONST V128 c) ∷ []))
  vcvtop-zero-14 : ∀ (c-1 : (uN-fam0 (128))) (M-2 : M) (M-1 : M) (v-vcvtop : vcvtop) (c : (uN-fam0 (128))) (ci-lst : (List (fN-fam0 (32)))) (cj-lst-lst : (List (List (fN-fam0 (64))))) → 
    ((zeroop v-vcvtop) ≡ (just ZERO)) →
    (ci-lst ≡ (lanes- (X (lanetype-numtype F32) (mk-dim M-1)) c-1)) →
    (cj-lst-lst ≡ (setproduct- (fN-fam0 (64)) ((map (λ (ci-42 : (fN-fam0 (32))) → (vcvtop-- (X (lanetype-numtype F32) (mk-dim M-1)) (X (lanetype-numtype F64) (mk-dim M-2)) v-vcvtop ci-42)) ci-lst) ++ (replicate M-1 ((fun-zero F64) ∷ []))))) →
    ((length (map (λ (cj-lst-30 : (List (fN-fam0 (64)))) → (inv-lanes- (X (lanetype-numtype F64) (mk-dim M-2)) cj-lst-30)) cj-lst-lst)) > 0) →
    (c ∈ (map (λ (cj-lst-30 : (List (fN-fam0 (64)))) → (inv-lanes- (X (lanetype-numtype F64) (mk-dim M-2)) cj-lst-30)) cj-lst-lst)) →
    Step-pure (as (List admininstr) ((admininstr-VCONST V128 c-1) ∷ (admininstr-VCVTOP (X (lanetype-numtype F64) (mk-dim M-2)) (X (lanetype-numtype F32) (mk-dim M-1)) v-vcvtop) ∷ [])) (as (List admininstr) ((admininstr-VCONST V128 c) ∷ []))
  vcvtop-zero-15 : ∀ (c-1 : (uN-fam0 (128))) (M-2 : M) (M-1 : M) (v-vcvtop : vcvtop) (c : (uN-fam0 (128))) (ci-lst : (List (fN-fam0 (64)))) (cj-lst-lst : (List (List (fN-fam0 (64))))) → 
    ((zeroop v-vcvtop) ≡ (just ZERO)) →
    (ci-lst ≡ (lanes- (X (lanetype-numtype F64) (mk-dim M-1)) c-1)) →
    (cj-lst-lst ≡ (setproduct- (fN-fam0 (64)) ((map (λ (ci-44 : (fN-fam0 (64))) → (vcvtop-- (X (lanetype-numtype F64) (mk-dim M-1)) (X (lanetype-numtype F64) (mk-dim M-2)) v-vcvtop ci-44)) ci-lst) ++ (replicate M-1 ((fun-zero F64) ∷ []))))) →
    ((length (map (λ (cj-lst-32 : (List (fN-fam0 (64)))) → (inv-lanes- (X (lanetype-numtype F64) (mk-dim M-2)) cj-lst-32)) cj-lst-lst)) > 0) →
    (c ∈ (map (λ (cj-lst-32 : (List (fN-fam0 (64)))) → (inv-lanes- (X (lanetype-numtype F64) (mk-dim M-2)) cj-lst-32)) cj-lst-lst)) →
    Step-pure (as (List admininstr) ((admininstr-VCONST V128 c-1) ∷ (admininstr-VCVTOP (X (lanetype-numtype F64) (mk-dim M-2)) (X (lanetype-numtype F64) (mk-dim M-1)) v-vcvtop) ∷ [])) (as (List admininstr) ((admininstr-VCONST V128 c) ∷ []))
  Step-pure--local-tee : ∀ (v-val : val) (x : idx) → Step-pure (as (List admininstr) ((admininstr-val v-val) ∷ (admininstr-LOCAL-TEE x) ∷ [])) (as (List admininstr) ((admininstr-val v-val) ∷ (admininstr-val v-val) ∷ (admininstr-LOCAL-SET x) ∷ []))

{- Auxiliary Definition at: ../specification/wasm-2.0/8-reduction.spectec:63.1-63.73 -}
{-# TERMINATING #-}
fun-blocktype : (v-state : state) (v-blocktype : blocktype) → functype
fun-blocktype z (-RESULT nothing) = (mk-functype (mk-list []) (mk-list []))
fun-blocktype z (-RESULT (just t)) = (mk-functype (mk-list []) (mk-list (t ∷ [])))
fun-blocktype z (-IDX x) = (fun-type z x)
fun-blocktype v-state v-blocktype = default-val

{- Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:127.1-129.15 -}
data Step-read-before-call-indirect-trap : config → Set where
  call-indirect-call-0 : ∀ (z : state) (i : (uN-fam0 (32))) (x : idx) (y : idx) (a : addr) → 
    ((proj-uN-0 32 i) < (length (REFS (fun-table z x)))) →
    (((REFS (fun-table z x)) [ (proj-uN-0 32 i) ]!) ≡ (REF-FUNC-ADDR a)) →
    (a < (length (fun-funcinst z))) →
    ((fun-type z y) ≡ (funcinst-TYPE ((fun-funcinst z) [ a ]!))) →
    Step-read-before-call-indirect-trap (mk-config z (as (List admininstr) ((admininstr-CONST I32 i) ∷ (admininstr-CALL-INDIRECT x y) ∷ [])))

{- Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:436.1-439.14 -}
data Step-read-before-table-fill-zero : config → Set where
  table-fill-trap-0 : ∀ (z : state) (i : (uN-fam0 (32))) (v-val : val) (v-n : n) (x : idx) → 
    (((proj-uN-0 32 i) + v-n) > (length (REFS (fun-table z x)))) →
    Step-read-before-table-fill-zero (mk-config z (as (List admininstr) ((admininstr-CONST I32 i) ∷ (admininstr-val v-val) ∷ (admininstr-CONST I32 (mk-uN v-n)) ∷ (admininstr-TABLE-FILL x) ∷ [])))

{- Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:452.1-455.14 -}
data Step-read-before-table-copy-zero : config → Set where
  table-copy-trap-0 : ∀ (z : state) (j : (uN-fam0 (32))) (i : (uN-fam0 (32))) (v-n : n) (x : idx) (y : idx) → 
    ((((proj-uN-0 32 i) + v-n) > (length (REFS (fun-table z y)))) ⊎ (((proj-uN-0 32 j) + v-n) > (length (REFS (fun-table z x))))) →
    Step-read-before-table-copy-zero (mk-config z (as (List admininstr) ((admininstr-CONST I32 j) ∷ (admininstr-CONST I32 i) ∷ (admininstr-CONST I32 (mk-uN v-n)) ∷ (admininstr-TABLE-COPY x y) ∷ [])))

{- Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:457.1-462.15 -}
data Step-read-before-table-copy-le : config → Set where
  table-copy-zero-0 : ∀ (z : state) (j : (uN-fam0 (32))) (i : (uN-fam0 (32))) (v-n : n) (x : idx) (y : idx) → 
    (¬ (Step-read-before-table-copy-zero (mk-config z (as (List admininstr) ((admininstr-CONST I32 j) ∷ (admininstr-CONST I32 i) ∷ (admininstr-CONST I32 (mk-uN v-n)) ∷ (admininstr-TABLE-COPY x y) ∷ []))))) →
    (v-n ≡ 0) →
    Step-read-before-table-copy-le (mk-config z (as (List admininstr) ((admininstr-CONST I32 j) ∷ (admininstr-CONST I32 i) ∷ (admininstr-CONST I32 (mk-uN v-n)) ∷ (admininstr-TABLE-COPY x y) ∷ [])))
  table-copy-trap-1 : ∀ (z : state) (j : (uN-fam0 (32))) (i : (uN-fam0 (32))) (v-n : n) (x : idx) (y : idx) → 
    ((((proj-uN-0 32 i) + v-n) > (length (REFS (fun-table z y)))) ⊎ (((proj-uN-0 32 j) + v-n) > (length (REFS (fun-table z x))))) →
    Step-read-before-table-copy-le (mk-config z (as (List admininstr) ((admininstr-CONST I32 j) ∷ (admininstr-CONST I32 i) ∷ (admininstr-CONST I32 (mk-uN v-n)) ∷ (admininstr-TABLE-COPY x y) ∷ [])))

{- Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:475.1-478.14 -}
data Step-read-before-table-init-zero : config → Set where
  table-init-trap-0 : ∀ (z : state) (j : (uN-fam0 (32))) (i : (uN-fam0 (32))) (v-n : n) (x : idx) (y : idx) → 
    ((((proj-uN-0 32 i) + v-n) > (length (eleminst-REFS (fun-elem z y)))) ⊎ (((proj-uN-0 32 j) + v-n) > (length (REFS (fun-table z x))))) →
    Step-read-before-table-init-zero (mk-config z (as (List admininstr) ((admininstr-CONST I32 j) ∷ (admininstr-CONST I32 i) ∷ (admininstr-CONST I32 (mk-uN v-n)) ∷ (admininstr-TABLE-INIT x y) ∷ [])))

{- Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:616.1-619.14 -}
data Step-read-before-memory-fill-zero : config → Set where
  memory-fill-trap-0 : ∀ (z : state) (i : (uN-fam0 (32))) (v-val : val) (v-n : n) → 
    (((proj-uN-0 32 i) + v-n) > (length (BYTES (fun-mem z (mk-uN 0))))) →
    Step-read-before-memory-fill-zero (mk-config z (as (List admininstr) ((admininstr-CONST I32 i) ∷ (admininstr-val v-val) ∷ (admininstr-CONST I32 (mk-uN v-n)) ∷ admininstr-MEMORY-FILL ∷ [])))

{- Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:632.1-635.14 -}
data Step-read-before-memory-copy-zero : config → Set where
  memory-copy-trap-0 : ∀ (z : state) (j : (uN-fam0 (32))) (i : (uN-fam0 (32))) (v-n : n) → 
    ((((proj-uN-0 32 i) + v-n) > (length (BYTES (fun-mem z (mk-uN 0))))) ⊎ (((proj-uN-0 32 j) + v-n) > (length (BYTES (fun-mem z (mk-uN 0)))))) →
    Step-read-before-memory-copy-zero (mk-config z (as (List admininstr) ((admininstr-CONST I32 j) ∷ (admininstr-CONST I32 i) ∷ (admininstr-CONST I32 (mk-uN v-n)) ∷ admininstr-MEMORY-COPY ∷ [])))

{- Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:637.1-642.15 -}
data Step-read-before-memory-copy-le : config → Set where
  memory-copy-zero-0 : ∀ (z : state) (j : (uN-fam0 (32))) (i : (uN-fam0 (32))) (v-n : n) → 
    (¬ (Step-read-before-memory-copy-zero (mk-config z (as (List admininstr) ((admininstr-CONST I32 j) ∷ (admininstr-CONST I32 i) ∷ (admininstr-CONST I32 (mk-uN v-n)) ∷ admininstr-MEMORY-COPY ∷ []))))) →
    (v-n ≡ 0) →
    Step-read-before-memory-copy-le (mk-config z (as (List admininstr) ((admininstr-CONST I32 j) ∷ (admininstr-CONST I32 i) ∷ (admininstr-CONST I32 (mk-uN v-n)) ∷ admininstr-MEMORY-COPY ∷ [])))
  memory-copy-trap-1 : ∀ (z : state) (j : (uN-fam0 (32))) (i : (uN-fam0 (32))) (v-n : n) → 
    ((((proj-uN-0 32 i) + v-n) > (length (BYTES (fun-mem z (mk-uN 0))))) ⊎ (((proj-uN-0 32 j) + v-n) > (length (BYTES (fun-mem z (mk-uN 0)))))) →
    Step-read-before-memory-copy-le (mk-config z (as (List admininstr) ((admininstr-CONST I32 j) ∷ (admininstr-CONST I32 i) ∷ (admininstr-CONST I32 (mk-uN v-n)) ∷ admininstr-MEMORY-COPY ∷ [])))

{- Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:655.1-658.14 -}
data Step-read-before-memory-init-zero : config → Set where
  memory-init-trap-0 : ∀ (z : state) (j : (uN-fam0 (32))) (i : (uN-fam0 (32))) (v-n : n) (x : idx) → 
    ((((proj-uN-0 32 i) + v-n) > (length (datainst-BYTES (fun-data z x)))) ⊎ (((proj-uN-0 32 j) + v-n) > (length (BYTES (fun-mem z (mk-uN 0)))))) →
    Step-read-before-memory-init-zero (mk-config z (as (List admininstr) ((admininstr-CONST I32 j) ∷ (admininstr-CONST I32 i) ∷ (admininstr-CONST I32 (mk-uN v-n)) ∷ (admininstr-MEMORY-INIT x) ∷ [])))

{- Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:7.1-7.109 -}
data Step-read : config → (List admininstr) → Set where
  Step-read--block : ∀ (z : state) (k : ℕ) (val-lst : (List val)) (bt : blocktype) (instr-lst : (List instr)) (v-n : n) (t-1-lst : (List valtype)) (t-2-lst : (List valtype)) → 
    ((length (val-lst)) ≡ (k)) →
    ((length (t-2-lst)) ≡ (v-n)) →
    ((length (t-1-lst)) ≡ (k)) →
    ((fun-blocktype z bt) ≡ (mk-functype (mk-list t-1-lst) (mk-list t-2-lst))) →
    Step-read (mk-config z ((map (λ (v-val : val) → (admininstr-val v-val)) val-lst) ++ (as (List admininstr) ((admininstr-BLOCK bt instr-lst) ∷ [])))) (as (List admininstr) ((LABEL- v-n [] ((map (λ (v-val : val) → (admininstr-val v-val)) val-lst) ++ (map (λ (v-instr : instr) → (admininstr-instr v-instr)) instr-lst))) ∷ []))
  Step-read--loop : ∀ (z : state) (k : ℕ) (val-lst : (List val)) (bt : blocktype) (instr-lst : (List instr)) (t-1-lst : (List valtype)) (v-n : n) (t-2-lst : (List valtype)) → 
    ((length (val-lst)) ≡ (k)) →
    ((length (t-2-lst)) ≡ (v-n)) →
    ((length (t-1-lst)) ≡ (k)) →
    ((fun-blocktype z bt) ≡ (mk-functype (mk-list t-1-lst) (mk-list t-2-lst))) →
    Step-read (mk-config z ((map (λ (v-val : val) → (admininstr-val v-val)) val-lst) ++ (as (List admininstr) ((admininstr-LOOP bt instr-lst) ∷ [])))) (as (List admininstr) ((LABEL- k (as (List instr) ((LOOP bt instr-lst) ∷ [])) ((map (λ (v-val : val) → (admininstr-val v-val)) val-lst) ++ (map (λ (v-instr : instr) → (admininstr-instr v-instr)) instr-lst))) ∷ []))
  Step-read--call : ∀ (z : state) (x : idx) → 
    ((proj-uN-0 32 x) < (length (fun-funcaddr z))) →
    Step-read (mk-config z (as (List admininstr) ((admininstr-CALL x) ∷ []))) (as (List admininstr) ((CALL-ADDR ((fun-funcaddr z) [ (proj-uN-0 32 x) ]!)) ∷ []))
  call-indirect-call : ∀ (z : state) (i : (uN-fam0 (32))) (x : idx) (y : idx) (a : addr) → 
    ((proj-uN-0 32 i) < (length (REFS (fun-table z x)))) →
    (((REFS (fun-table z x)) [ (proj-uN-0 32 i) ]!) ≡ (REF-FUNC-ADDR a)) →
    (a < (length (fun-funcinst z))) →
    ((fun-type z y) ≡ (funcinst-TYPE ((fun-funcinst z) [ a ]!))) →
    Step-read (mk-config z (as (List admininstr) ((admininstr-CONST I32 i) ∷ (admininstr-CALL-INDIRECT x y) ∷ []))) (as (List admininstr) ((CALL-ADDR a) ∷ []))
  call-indirect-trap : ∀ (z : state) (i : (uN-fam0 (32))) (x : idx) (y : idx) → 
    (¬ (Step-read-before-call-indirect-trap (mk-config z (as (List admininstr) ((admininstr-CONST I32 i) ∷ (admininstr-CALL-INDIRECT x y) ∷ []))))) →
    Step-read (mk-config z (as (List admininstr) ((admininstr-CONST I32 i) ∷ (admininstr-CALL-INDIRECT x y) ∷ []))) (as (List admininstr) (admininstr-TRAP ∷ []))
  call-addr : ∀ (z : state) (k : ℕ) (val-lst : (List val)) (a : addr) (v-n : n) (f : frame) (instr-lst : (List instr)) (t-1-lst : (List valtype)) (t-2-lst : (List valtype)) (mm : moduleinst) (v-func : func) (x : idx) (t-lst : (List valtype)) → 
    ((length (val-lst)) ≡ (k)) →
    ((length (t-2-lst)) ≡ (v-n)) →
    ((length (t-1-lst)) ≡ (k)) →
    (a < (length (fun-funcinst z))) →
    (((fun-funcinst z) [ a ]!) ≡ record { funcinst-TYPE = (mk-functype (mk-list t-1-lst) (mk-list t-2-lst)) ; funcinst-MODULE = mm ; CODE = v-func }) →
    (v-func ≡ (func-FUNC x (map (λ (t : valtype) → (LOCAL t)) t-lst) instr-lst)) →
    Forall (λ (t : valtype) → ((default- t) ≢ nothing)) t-lst →
    (f ≡ record { LOCALS = (val-lst ++ (map (λ (t : valtype) → (unwrap! (default- t))) t-lst)) ; frame-MODULE = mm }) →
    Step-read (mk-config z ((map (λ (v-val : val) → (admininstr-val v-val)) val-lst) ++ (as (List admininstr) ((CALL-ADDR a) ∷ [])))) (as (List admininstr) ((FRAME- v-n f (as (List admininstr) ((LABEL- v-n [] (map (λ (v-instr : instr) → (admininstr-instr v-instr)) instr-lst)) ∷ []))) ∷ []))
  Step-read--ref-func : ∀ (z : state) (x : idx) → 
    ((proj-uN-0 32 x) < (length (fun-funcaddr z))) →
    Step-read (mk-config z (as (List admininstr) ((admininstr-REF-FUNC x) ∷ []))) (as (List admininstr) ((admininstr-REF-FUNC-ADDR ((fun-funcaddr z) [ (proj-uN-0 32 x) ]!)) ∷ []))
  Step-read--local-get : ∀ (z : state) (x : idx) → Step-read (mk-config z (as (List admininstr) ((admininstr-LOCAL-GET x) ∷ []))) ((admininstr-val (fun-local z x)) ∷ [])
  Step-read--global-get : ∀ (z : state) (x : idx) → Step-read (mk-config z (as (List admininstr) ((admininstr-GLOBAL-GET x) ∷ []))) ((admininstr-val (VALUE (fun-global z x))) ∷ [])
  table-get-trap : ∀ (z : state) (i : (uN-fam0 (32))) (x : idx) → 
    ((proj-uN-0 32 i) ≥ (length (REFS (fun-table z x)))) →
    Step-read (mk-config z (as (List admininstr) ((admininstr-CONST I32 i) ∷ (admininstr-TABLE-GET x) ∷ []))) (as (List admininstr) (admininstr-TRAP ∷ []))
  table-get-val : ∀ (z : state) (i : (uN-fam0 (32))) (x : idx) → 
    ((proj-uN-0 32 i) < (length (REFS (fun-table z x)))) →
    Step-read (mk-config z (as (List admininstr) ((admininstr-CONST I32 i) ∷ (admininstr-TABLE-GET x) ∷ []))) ((admininstr-ref ((REFS (fun-table z x)) [ (proj-uN-0 32 i) ]!)) ∷ [])
  Step-read--table-size : ∀ (z : state) (x : idx) (v-n : n) → 
    ((length (REFS (fun-table z x))) ≡ v-n) →
    Step-read (mk-config z (as (List admininstr) ((admininstr-TABLE-SIZE x) ∷ []))) (as (List admininstr) ((admininstr-CONST I32 (mk-uN v-n)) ∷ []))
  table-fill-trap : ∀ (z : state) (i : (uN-fam0 (32))) (v-val : val) (v-n : n) (x : idx) → 
    (((proj-uN-0 32 i) + v-n) > (length (REFS (fun-table z x)))) →
    Step-read (mk-config z (as (List admininstr) ((admininstr-CONST I32 i) ∷ (admininstr-val v-val) ∷ (admininstr-CONST I32 (mk-uN v-n)) ∷ (admininstr-TABLE-FILL x) ∷ []))) (as (List admininstr) (admininstr-TRAP ∷ []))
  table-fill-zero : ∀ (z : state) (i : (uN-fam0 (32))) (v-val : val) (v-n : n) (x : idx) → 
    (((proj-uN-0 32 i) + v-n) ≤ (length (REFS (fun-table z x)))) →
    (v-n ≡ 0) →
    Step-read (mk-config z (as (List admininstr) ((admininstr-CONST I32 i) ∷ (admininstr-val v-val) ∷ (admininstr-CONST I32 (mk-uN v-n)) ∷ (admininstr-TABLE-FILL x) ∷ []))) []
  table-fill-succ : ∀ (z : state) (i : (uN-fam0 (32))) (v-val : val) (v-n : n) (x : idx) → 
    (v-n ≢ 0) →
    (((proj-uN-0 32 i) + v-n) ≤ (length (REFS (fun-table z x)))) →
    Step-read (mk-config z (as (List admininstr) ((admininstr-CONST I32 i) ∷ (admininstr-val v-val) ∷ (admininstr-CONST I32 (mk-uN v-n)) ∷ (admininstr-TABLE-FILL x) ∷ []))) (as (List admininstr) ((admininstr-CONST I32 i) ∷ (admininstr-val v-val) ∷ (admininstr-TABLE-SET x) ∷ (admininstr-CONST I32 (mk-uN ((proj-uN-0 32 i) + 1))) ∷ (admininstr-val v-val) ∷ (admininstr-CONST I32 (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} v-n) – (coerce {B = ℕ} 1))))) ∷ (admininstr-TABLE-FILL x) ∷ []))
  table-copy-trap : ∀ (z : state) (j : (uN-fam0 (32))) (i : (uN-fam0 (32))) (v-n : n) (x : idx) (y : idx) → 
    ((((proj-uN-0 32 i) + v-n) > (length (REFS (fun-table z y)))) ⊎ (((proj-uN-0 32 j) + v-n) > (length (REFS (fun-table z x))))) →
    Step-read (mk-config z (as (List admininstr) ((admininstr-CONST I32 j) ∷ (admininstr-CONST I32 i) ∷ (admininstr-CONST I32 (mk-uN v-n)) ∷ (admininstr-TABLE-COPY x y) ∷ []))) (as (List admininstr) (admininstr-TRAP ∷ []))
  table-copy-zero : ∀ (z : state) (j : (uN-fam0 (32))) (i : (uN-fam0 (32))) (v-n : n) (x : idx) (y : idx) → 
    ((((proj-uN-0 32 i) + v-n) ≤ (length (REFS (fun-table z y)))) × (((proj-uN-0 32 j) + v-n) ≤ (length (REFS (fun-table z x))))) →
    (v-n ≡ 0) →
    Step-read (mk-config z (as (List admininstr) ((admininstr-CONST I32 j) ∷ (admininstr-CONST I32 i) ∷ (admininstr-CONST I32 (mk-uN v-n)) ∷ (admininstr-TABLE-COPY x y) ∷ []))) []
  table-copy-le : ∀ (z : state) (j : (uN-fam0 (32))) (i : (uN-fam0 (32))) (v-n : n) (x : idx) (y : idx) → 
    (v-n ≢ 0) →
    ((((proj-uN-0 32 i) + v-n) ≤ (length (REFS (fun-table z y)))) × (((proj-uN-0 32 j) + v-n) ≤ (length (REFS (fun-table z x))))) →
    ((proj-uN-0 32 j) ≤ (proj-uN-0 32 i)) →
    Step-read (mk-config z (as (List admininstr) ((admininstr-CONST I32 j) ∷ (admininstr-CONST I32 i) ∷ (admininstr-CONST I32 (mk-uN v-n)) ∷ (admininstr-TABLE-COPY x y) ∷ []))) (as (List admininstr) ((admininstr-CONST I32 j) ∷ (admininstr-CONST I32 i) ∷ (admininstr-TABLE-GET y) ∷ (admininstr-TABLE-SET x) ∷ (admininstr-CONST I32 (mk-uN ((proj-uN-0 32 j) + 1))) ∷ (admininstr-CONST I32 (mk-uN ((proj-uN-0 32 i) + 1))) ∷ (admininstr-CONST I32 (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} v-n) – (coerce {B = ℕ} 1))))) ∷ (admininstr-TABLE-COPY x y) ∷ []))
  table-copy-gt : ∀ (z : state) (j : (uN-fam0 (32))) (i : (uN-fam0 (32))) (v-n : n) (x : idx) (y : idx) → 
    ((proj-uN-0 32 j) > (proj-uN-0 32 i)) →
    (v-n ≢ 0) →
    ((((proj-uN-0 32 i) + v-n) ≤ (length (REFS (fun-table z y)))) × (((proj-uN-0 32 j) + v-n) ≤ (length (REFS (fun-table z x))))) →
    Step-read (mk-config z (as (List admininstr) ((admininstr-CONST I32 j) ∷ (admininstr-CONST I32 i) ∷ (admininstr-CONST I32 (mk-uN v-n)) ∷ (admininstr-TABLE-COPY x y) ∷ []))) (as (List admininstr) ((admininstr-CONST I32 (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} ((proj-uN-0 32 j) + v-n)) – (coerce {B = ℕ} 1))))) ∷ (admininstr-CONST I32 (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} ((proj-uN-0 32 i) + v-n)) – (coerce {B = ℕ} 1))))) ∷ (admininstr-TABLE-GET y) ∷ (admininstr-TABLE-SET x) ∷ (admininstr-CONST I32 j) ∷ (admininstr-CONST I32 i) ∷ (admininstr-CONST I32 (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} v-n) – (coerce {B = ℕ} 1))))) ∷ (admininstr-TABLE-COPY x y) ∷ []))
  table-init-trap : ∀ (z : state) (j : (uN-fam0 (32))) (i : (uN-fam0 (32))) (v-n : n) (x : idx) (y : idx) → 
    ((((proj-uN-0 32 i) + v-n) > (length (eleminst-REFS (fun-elem z y)))) ⊎ (((proj-uN-0 32 j) + v-n) > (length (REFS (fun-table z x))))) →
    Step-read (mk-config z (as (List admininstr) ((admininstr-CONST I32 j) ∷ (admininstr-CONST I32 i) ∷ (admininstr-CONST I32 (mk-uN v-n)) ∷ (admininstr-TABLE-INIT x y) ∷ []))) (as (List admininstr) (admininstr-TRAP ∷ []))
  table-init-zero : ∀ (z : state) (j : (uN-fam0 (32))) (i : (uN-fam0 (32))) (v-n : n) (x : idx) (y : idx) → 
    ((((proj-uN-0 32 i) + v-n) ≤ (length (eleminst-REFS (fun-elem z y)))) × (((proj-uN-0 32 j) + v-n) ≤ (length (REFS (fun-table z x))))) →
    (v-n ≡ 0) →
    Step-read (mk-config z (as (List admininstr) ((admininstr-CONST I32 j) ∷ (admininstr-CONST I32 i) ∷ (admininstr-CONST I32 (mk-uN v-n)) ∷ (admininstr-TABLE-INIT x y) ∷ []))) []
  table-init-succ : ∀ (z : state) (j : (uN-fam0 (32))) (i : (uN-fam0 (32))) (v-n : n) (x : idx) (y : idx) → 
    ((proj-uN-0 32 i) < (length (eleminst-REFS (fun-elem z y)))) →
    (v-n ≢ 0) →
    ((((proj-uN-0 32 i) + v-n) ≤ (length (eleminst-REFS (fun-elem z y)))) × (((proj-uN-0 32 j) + v-n) ≤ (length (REFS (fun-table z x))))) →
    Step-read (mk-config z (as (List admininstr) ((admininstr-CONST I32 j) ∷ (admininstr-CONST I32 i) ∷ (admininstr-CONST I32 (mk-uN v-n)) ∷ (admininstr-TABLE-INIT x y) ∷ []))) (as (List admininstr) ((admininstr-CONST I32 j) ∷ (admininstr-ref ((eleminst-REFS (fun-elem z y)) [ (proj-uN-0 32 i) ]!)) ∷ (admininstr-TABLE-SET x) ∷ (admininstr-CONST I32 (mk-uN ((proj-uN-0 32 j) + 1))) ∷ (admininstr-CONST I32 (mk-uN ((proj-uN-0 32 i) + 1))) ∷ (admininstr-CONST I32 (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} v-n) – (coerce {B = ℕ} 1))))) ∷ (admininstr-TABLE-INIT x y) ∷ []))
  load-num-trap : ∀ (z : state) (i : (uN-fam0 (32))) (nt : numtype) (ao : memarg) → 
    ((size (valtype-numtype nt)) ≢ nothing) →
    ((((proj-uN-0 32 i) + (proj-uN-0 32 (OFFSET ao))) + (coerce {B = ℕ} ((coerce {B = ℕ} (unwrap! (size (valtype-numtype nt)))) / (coerce {B = ℕ} 8)))) > (length (BYTES (fun-mem z (mk-uN 0))))) →
    Step-read (mk-config z (as (List admininstr) ((admininstr-CONST I32 i) ∷ (admininstr-LOAD nt nothing ao) ∷ []))) (as (List admininstr) (admininstr-TRAP ∷ []))
  load-num-val : ∀ (z : state) (i : (uN-fam0 (32))) (nt : numtype) (ao : memarg) (c : (num- nt)) → 
    ((size (valtype-numtype nt)) ≢ nothing) →
    ((nbytes- nt c) ≡ (slice (BYTES (fun-mem z (mk-uN 0))) ((proj-uN-0 32 i) + (proj-uN-0 32 (OFFSET ao))) (coerce {B = ℕ} ((coerce {B = ℕ} (unwrap! (size (valtype-numtype nt)))) / (coerce {B = ℕ} 8))))) →
    Step-read (mk-config z (as (List admininstr) ((admininstr-CONST I32 i) ∷ (admininstr-LOAD nt nothing ao) ∷ []))) (as (List admininstr) ((admininstr-CONST nt c) ∷ []))
  load-pack-trap-0 : ∀ (z : state) (i : (uN-fam0 (32))) (v-n : n) (v-sx : sx) (ao : memarg) → 
    ((((proj-uN-0 32 i) + (proj-uN-0 32 (OFFSET ao))) + (coerce {B = ℕ} ((coerce {B = ℕ} v-n) / (coerce {B = ℕ} 8)))) > (length (BYTES (fun-mem z (mk-uN 0))))) →
    Step-read (mk-config z (as (List admininstr) ((admininstr-CONST I32 i) ∷ (admininstr-LOAD (numtype-Inn Inn-I32) (just (mk-loadop- (mk-sz v-n) v-sx)) ao) ∷ []))) (as (List admininstr) (admininstr-TRAP ∷ []))
  load-pack-trap-1 : ∀ (z : state) (i : (uN-fam0 (32))) (v-n : n) (v-sx : sx) (ao : memarg) → 
    ((((proj-uN-0 32 i) + (proj-uN-0 32 (OFFSET ao))) + (coerce {B = ℕ} ((coerce {B = ℕ} v-n) / (coerce {B = ℕ} 8)))) > (length (BYTES (fun-mem z (mk-uN 0))))) →
    Step-read (mk-config z (as (List admininstr) ((admininstr-CONST I32 i) ∷ (admininstr-LOAD (numtype-Inn Inn-I64) (just (mk-loadop- (mk-sz v-n) v-sx)) ao) ∷ []))) (as (List admininstr) (admininstr-TRAP ∷ []))
  load-pack-val-0 : ∀ (z : state) (i : (uN-fam0 (32))) (v-n : n) (v-sx : sx) (ao : memarg) (c : (uN-fam0 (v-n))) → 
    ((size (valtype-Inn Inn-I32)) ≢ nothing) →
    ((ibytes- v-n c) ≡ (slice (BYTES (fun-mem z (mk-uN 0))) ((proj-uN-0 32 i) + (proj-uN-0 32 (OFFSET ao))) (coerce {B = ℕ} ((coerce {B = ℕ} v-n) / (coerce {B = ℕ} 8))))) →
    Step-read (mk-config z (as (List admininstr) ((admininstr-CONST I32 i) ∷ (admininstr-LOAD (numtype-Inn Inn-I32) (just (mk-loadop- (mk-sz v-n) v-sx)) ao) ∷ []))) (as (List admininstr) ((admininstr-CONST (numtype-Inn Inn-I32) (extend-- v-n (unwrap! (size (valtype-Inn Inn-I32))) v-sx c)) ∷ []))
  load-pack-val-1 : ∀ (z : state) (i : (uN-fam0 (32))) (v-n : n) (v-sx : sx) (ao : memarg) (c : (uN-fam0 (v-n))) → 
    ((size (valtype-Inn Inn-I64)) ≢ nothing) →
    ((ibytes- v-n c) ≡ (slice (BYTES (fun-mem z (mk-uN 0))) ((proj-uN-0 32 i) + (proj-uN-0 32 (OFFSET ao))) (coerce {B = ℕ} ((coerce {B = ℕ} v-n) / (coerce {B = ℕ} 8))))) →
    Step-read (mk-config z (as (List admininstr) ((admininstr-CONST I32 i) ∷ (admininstr-LOAD (numtype-Inn Inn-I64) (just (mk-loadop- (mk-sz v-n) v-sx)) ao) ∷ []))) (as (List admininstr) ((admininstr-CONST (numtype-Inn Inn-I64) (extend-- v-n (unwrap! (size (valtype-Inn Inn-I64))) v-sx c)) ∷ []))
  vload-oob : ∀ (z : state) (i : (uN-fam0 (32))) (ao : memarg) → 
    ((size valtype-V128) ≢ nothing) →
    ((((proj-uN-0 32 i) + (proj-uN-0 32 (OFFSET ao))) + (coerce {B = ℕ} ((coerce {B = ℕ} (unwrap! (size valtype-V128))) / (coerce {B = ℕ} 8)))) > (length (BYTES (fun-mem z (mk-uN 0))))) →
    Step-read (mk-config z (as (List admininstr) ((admininstr-CONST I32 i) ∷ (admininstr-VLOAD V128 nothing ao) ∷ []))) (as (List admininstr) (admininstr-TRAP ∷ []))
  vload-val : ∀ (z : state) (i : (uN-fam0 (32))) (ao : memarg) (c : (uN-fam0 (128))) → 
    ((size valtype-V128) ≢ nothing) →
    ((vbytes- V128 c) ≡ (slice (BYTES (fun-mem z (mk-uN 0))) ((proj-uN-0 32 i) + (proj-uN-0 32 (OFFSET ao))) (coerce {B = ℕ} ((coerce {B = ℕ} (unwrap! (size valtype-V128))) / (coerce {B = ℕ} 8))))) →
    Step-read (mk-config z (as (List admininstr) ((admininstr-CONST I32 i) ∷ (admininstr-VLOAD V128 nothing ao) ∷ []))) (as (List admininstr) ((admininstr-VCONST V128 c) ∷ []))
  vload-shape-oob : ∀ (z : state) (i : (uN-fam0 (32))) (v-M : M) (v-N : N) (v-sx : sx) (ao : memarg) → 
    ((((proj-uN-0 32 i) + (proj-uN-0 32 (OFFSET ao))) + (coerce {B = ℕ} ((coerce {B = ℕ} (v-M * v-N)) / (coerce {B = ℕ} 8)))) > (length (BYTES (fun-mem z (mk-uN 0))))) →
    Step-read (mk-config z (as (List admininstr) ((admininstr-CONST I32 i) ∷ (admininstr-VLOAD V128 (just (SHAPEX- v-M v-N v-sx)) ao) ∷ []))) (as (List admininstr) (admininstr-TRAP ∷ []))
  vload-shape-val-0 : ∀ (z : state) (i : (uN-fam0 (32))) (v-M : M) (v-N : N) (v-sx : sx) (ao : memarg) (c : (uN-fam0 (128))) (j-lst : (List (uN-fam0 (v-M)))) → 
    ((length (j-lst)) ≡ (v-N)) →
    Foralli (λ k-5 (j-1 : (uN-fam0 (v-M))) → ((ibytes- v-M j-1) ≡ (slice (BYTES (fun-mem z (mk-uN 0))) (((proj-uN-0 32 i) + (proj-uN-0 32 (OFFSET ao))) + (coerce {B = ℕ} ((coerce {B = ℕ} (k-5 * v-M)) / (coerce {B = ℕ} 8)))) (coerce {B = ℕ} ((coerce {B = ℕ} v-M) / (coerce {B = ℕ} 8)))))) j-lst →
    ((jsize Jnn-I32) ≡ (v-M * 2)) →
    (c ≡ (inv-lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-N)) (map (λ (j-2 : (uN-fam0 (v-M))) → (extend-- v-M (jsize Jnn-I32) v-sx j-2)) j-lst))) →
    Step-read (mk-config z (as (List admininstr) ((admininstr-CONST I32 i) ∷ (admininstr-VLOAD V128 (just (SHAPEX- v-M v-N v-sx)) ao) ∷ []))) (as (List admininstr) ((admininstr-VCONST V128 c) ∷ []))
  vload-shape-val-1 : ∀ (z : state) (i : (uN-fam0 (32))) (v-M : M) (v-N : N) (v-sx : sx) (ao : memarg) (c : (uN-fam0 (128))) (j-lst : (List (uN-fam0 (v-M)))) → 
    ((length (j-lst)) ≡ (v-N)) →
    Foralli (λ k-6 (j-3 : (uN-fam0 (v-M))) → ((ibytes- v-M j-3) ≡ (slice (BYTES (fun-mem z (mk-uN 0))) (((proj-uN-0 32 i) + (proj-uN-0 32 (OFFSET ao))) + (coerce {B = ℕ} ((coerce {B = ℕ} (k-6 * v-M)) / (coerce {B = ℕ} 8)))) (coerce {B = ℕ} ((coerce {B = ℕ} v-M) / (coerce {B = ℕ} 8)))))) j-lst →
    ((jsize Jnn-I64) ≡ (v-M * 2)) →
    (c ≡ (inv-lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-N)) (map (λ (j-4 : (uN-fam0 (v-M))) → (extend-- v-M (jsize Jnn-I64) v-sx j-4)) j-lst))) →
    Step-read (mk-config z (as (List admininstr) ((admininstr-CONST I32 i) ∷ (admininstr-VLOAD V128 (just (SHAPEX- v-M v-N v-sx)) ao) ∷ []))) (as (List admininstr) ((admininstr-VCONST V128 c) ∷ []))
  vload-shape-val-2 : ∀ (z : state) (i : (uN-fam0 (32))) (v-M : M) (v-N : N) (v-sx : sx) (ao : memarg) (c : (uN-fam0 (128))) (j-lst : (List (uN-fam0 (v-M)))) → 
    ((length (j-lst)) ≡ (v-N)) →
    Foralli (λ k-7 (j-5 : (uN-fam0 (v-M))) → ((ibytes- v-M j-5) ≡ (slice (BYTES (fun-mem z (mk-uN 0))) (((proj-uN-0 32 i) + (proj-uN-0 32 (OFFSET ao))) + (coerce {B = ℕ} ((coerce {B = ℕ} (k-7 * v-M)) / (coerce {B = ℕ} 8)))) (coerce {B = ℕ} ((coerce {B = ℕ} v-M) / (coerce {B = ℕ} 8)))))) j-lst →
    ((jsize Jnn-I8) ≡ (v-M * 2)) →
    (c ≡ (inv-lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-N)) (map (λ (j-6 : (uN-fam0 (v-M))) → (extend-- v-M (jsize Jnn-I8) v-sx j-6)) j-lst))) →
    Step-read (mk-config z (as (List admininstr) ((admininstr-CONST I32 i) ∷ (admininstr-VLOAD V128 (just (SHAPEX- v-M v-N v-sx)) ao) ∷ []))) (as (List admininstr) ((admininstr-VCONST V128 c) ∷ []))
  vload-shape-val-3 : ∀ (z : state) (i : (uN-fam0 (32))) (v-M : M) (v-N : N) (v-sx : sx) (ao : memarg) (c : (uN-fam0 (128))) (j-lst : (List (uN-fam0 (v-M)))) → 
    ((length (j-lst)) ≡ (v-N)) →
    Foralli (λ k-8 (j-7 : (uN-fam0 (v-M))) → ((ibytes- v-M j-7) ≡ (slice (BYTES (fun-mem z (mk-uN 0))) (((proj-uN-0 32 i) + (proj-uN-0 32 (OFFSET ao))) + (coerce {B = ℕ} ((coerce {B = ℕ} (k-8 * v-M)) / (coerce {B = ℕ} 8)))) (coerce {B = ℕ} ((coerce {B = ℕ} v-M) / (coerce {B = ℕ} 8)))))) j-lst →
    ((jsize Jnn-I16) ≡ (v-M * 2)) →
    (c ≡ (inv-lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-N)) (map (λ (j-8 : (uN-fam0 (v-M))) → (extend-- v-M (jsize Jnn-I16) v-sx j-8)) j-lst))) →
    Step-read (mk-config z (as (List admininstr) ((admininstr-CONST I32 i) ∷ (admininstr-VLOAD V128 (just (SHAPEX- v-M v-N v-sx)) ao) ∷ []))) (as (List admininstr) ((admininstr-VCONST V128 c) ∷ []))
  vload-splat-oob : ∀ (z : state) (i : (uN-fam0 (32))) (v-N : N) (ao : memarg) → 
    ((((proj-uN-0 32 i) + (proj-uN-0 32 (OFFSET ao))) + (coerce {B = ℕ} ((coerce {B = ℕ} v-N) / (coerce {B = ℕ} 8)))) > (length (BYTES (fun-mem z (mk-uN 0))))) →
    Step-read (mk-config z (as (List admininstr) ((admininstr-CONST I32 i) ∷ (admininstr-VLOAD V128 (just (SPLAT v-N)) ao) ∷ []))) (as (List admininstr) (admininstr-TRAP ∷ []))
  vload-splat-val-0 : ∀ (z : state) (i : (uN-fam0 (32))) (v-N : N) (ao : memarg) (c : (uN-fam0 (128))) (j : (uN-fam0 (v-N))) (v-M : M) → 
    ((ibytes- v-N j) ≡ (slice (BYTES (fun-mem z (mk-uN 0))) ((proj-uN-0 32 i) + (proj-uN-0 32 (OFFSET ao))) (coerce {B = ℕ} ((coerce {B = ℕ} v-N) / (coerce {B = ℕ} 8))))) →
    (v-N ≡ (jsize Jnn-I32)) →
    ((coerce {B = ℕ} v-M) ≡ ((coerce {B = ℕ} 128) / (coerce {B = ℕ} v-N))) →
    (c ≡ (inv-lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) (replicate v-M (mk-uN (proj-uN-0 v-N j))))) →
    Step-read (mk-config z (as (List admininstr) ((admininstr-CONST I32 i) ∷ (admininstr-VLOAD V128 (just (SPLAT v-N)) ao) ∷ []))) (as (List admininstr) ((admininstr-VCONST V128 c) ∷ []))
  vload-splat-val-1 : ∀ (z : state) (i : (uN-fam0 (32))) (v-N : N) (ao : memarg) (c : (uN-fam0 (128))) (j : (uN-fam0 (v-N))) (v-M : M) → 
    ((ibytes- v-N j) ≡ (slice (BYTES (fun-mem z (mk-uN 0))) ((proj-uN-0 32 i) + (proj-uN-0 32 (OFFSET ao))) (coerce {B = ℕ} ((coerce {B = ℕ} v-N) / (coerce {B = ℕ} 8))))) →
    (v-N ≡ (jsize Jnn-I64)) →
    ((coerce {B = ℕ} v-M) ≡ ((coerce {B = ℕ} 128) / (coerce {B = ℕ} v-N))) →
    (c ≡ (inv-lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) (replicate v-M (mk-uN (proj-uN-0 v-N j))))) →
    Step-read (mk-config z (as (List admininstr) ((admininstr-CONST I32 i) ∷ (admininstr-VLOAD V128 (just (SPLAT v-N)) ao) ∷ []))) (as (List admininstr) ((admininstr-VCONST V128 c) ∷ []))
  vload-splat-val-2 : ∀ (z : state) (i : (uN-fam0 (32))) (v-N : N) (ao : memarg) (c : (uN-fam0 (128))) (j : (uN-fam0 (v-N))) (v-M : M) → 
    ((ibytes- v-N j) ≡ (slice (BYTES (fun-mem z (mk-uN 0))) ((proj-uN-0 32 i) + (proj-uN-0 32 (OFFSET ao))) (coerce {B = ℕ} ((coerce {B = ℕ} v-N) / (coerce {B = ℕ} 8))))) →
    (v-N ≡ (jsize Jnn-I8)) →
    ((coerce {B = ℕ} v-M) ≡ ((coerce {B = ℕ} 128) / (coerce {B = ℕ} v-N))) →
    (c ≡ (inv-lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) (replicate v-M (mk-uN (proj-uN-0 v-N j))))) →
    Step-read (mk-config z (as (List admininstr) ((admininstr-CONST I32 i) ∷ (admininstr-VLOAD V128 (just (SPLAT v-N)) ao) ∷ []))) (as (List admininstr) ((admininstr-VCONST V128 c) ∷ []))
  vload-splat-val-3 : ∀ (z : state) (i : (uN-fam0 (32))) (v-N : N) (ao : memarg) (c : (uN-fam0 (128))) (j : (uN-fam0 (v-N))) (v-M : M) → 
    ((ibytes- v-N j) ≡ (slice (BYTES (fun-mem z (mk-uN 0))) ((proj-uN-0 32 i) + (proj-uN-0 32 (OFFSET ao))) (coerce {B = ℕ} ((coerce {B = ℕ} v-N) / (coerce {B = ℕ} 8))))) →
    (v-N ≡ (jsize Jnn-I16)) →
    ((coerce {B = ℕ} v-M) ≡ ((coerce {B = ℕ} 128) / (coerce {B = ℕ} v-N))) →
    (c ≡ (inv-lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) (replicate v-M (mk-uN (proj-uN-0 v-N j))))) →
    Step-read (mk-config z (as (List admininstr) ((admininstr-CONST I32 i) ∷ (admininstr-VLOAD V128 (just (SPLAT v-N)) ao) ∷ []))) (as (List admininstr) ((admininstr-VCONST V128 c) ∷ []))
  vload-zero-oob : ∀ (z : state) (i : (uN-fam0 (32))) (v-N : N) (ao : memarg) → 
    ((((proj-uN-0 32 i) + (proj-uN-0 32 (OFFSET ao))) + (coerce {B = ℕ} ((coerce {B = ℕ} v-N) / (coerce {B = ℕ} 8)))) > (length (BYTES (fun-mem z (mk-uN 0))))) →
    Step-read (mk-config z (as (List admininstr) ((admininstr-CONST I32 i) ∷ (admininstr-VLOAD V128 (just (vloadop-ZERO v-N)) ao) ∷ []))) (as (List admininstr) (admininstr-TRAP ∷ []))
  vload-zero-val : ∀ (z : state) (i : (uN-fam0 (32))) (v-N : N) (ao : memarg) (c : (uN-fam0 (128))) (j : (uN-fam0 (v-N))) → 
    ((ibytes- v-N j) ≡ (slice (BYTES (fun-mem z (mk-uN 0))) ((proj-uN-0 32 i) + (proj-uN-0 32 (OFFSET ao))) (coerce {B = ℕ} ((coerce {B = ℕ} v-N) / (coerce {B = ℕ} 8))))) →
    (c ≡ (extend-- v-N 128 U j)) →
    Step-read (mk-config z (as (List admininstr) ((admininstr-CONST I32 i) ∷ (admininstr-VLOAD V128 (just (vloadop-ZERO v-N)) ao) ∷ []))) (as (List admininstr) ((admininstr-VCONST V128 c) ∷ []))
  vload-lane-oob : ∀ (z : state) (i : (uN-fam0 (32))) (c-1 : (uN-fam0 (128))) (v-N : N) (ao : memarg) (j : laneidx) → 
    ((((proj-uN-0 32 i) + (proj-uN-0 32 (OFFSET ao))) + (coerce {B = ℕ} ((coerce {B = ℕ} v-N) / (coerce {B = ℕ} 8)))) > (length (BYTES (fun-mem z (mk-uN 0))))) →
    Step-read (mk-config z (as (List admininstr) ((admininstr-CONST I32 i) ∷ (admininstr-VCONST V128 c-1) ∷ (admininstr-VLOAD-LANE V128 (mk-sz v-N) ao j) ∷ []))) (as (List admininstr) (admininstr-TRAP ∷ []))
  vload-lane-val-0 : ∀ (z : state) (i : (uN-fam0 (32))) (c-1 : (uN-fam0 (128))) (v-N : N) (ao : memarg) (j : laneidx) (c : (uN-fam0 (128))) (k : (uN-fam0 (v-N))) (v-M : M) → 
    ((ibytes- v-N k) ≡ (slice (BYTES (fun-mem z (mk-uN 0))) ((proj-uN-0 32 i) + (proj-uN-0 32 (OFFSET ao))) (coerce {B = ℕ} ((coerce {B = ℕ} v-N) / (coerce {B = ℕ} 8))))) →
    (v-N ≡ (jsize Jnn-I32)) →
    ((coerce {B = ℕ} v-M) ≡ ((coerce {B = ℕ} 128) / (coerce {B = ℕ} v-N))) →
    (c ≡ (inv-lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) (modify (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) c-1) (proj-uN-0 8 j) (λ (_ : (uN-fam0 (32))) → (mk-uN (proj-uN-0 v-N k)))))) →
    Step-read (mk-config z (as (List admininstr) ((admininstr-CONST I32 i) ∷ (admininstr-VCONST V128 c-1) ∷ (admininstr-VLOAD-LANE V128 (mk-sz v-N) ao j) ∷ []))) (as (List admininstr) ((admininstr-VCONST V128 c) ∷ []))
  vload-lane-val-1 : ∀ (z : state) (i : (uN-fam0 (32))) (c-1 : (uN-fam0 (128))) (v-N : N) (ao : memarg) (j : laneidx) (c : (uN-fam0 (128))) (k : (uN-fam0 (v-N))) (v-M : M) → 
    ((ibytes- v-N k) ≡ (slice (BYTES (fun-mem z (mk-uN 0))) ((proj-uN-0 32 i) + (proj-uN-0 32 (OFFSET ao))) (coerce {B = ℕ} ((coerce {B = ℕ} v-N) / (coerce {B = ℕ} 8))))) →
    (v-N ≡ (jsize Jnn-I64)) →
    ((coerce {B = ℕ} v-M) ≡ ((coerce {B = ℕ} 128) / (coerce {B = ℕ} v-N))) →
    (c ≡ (inv-lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) (modify (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) c-1) (proj-uN-0 8 j) (λ (_ : (uN-fam0 (64))) → (mk-uN (proj-uN-0 v-N k)))))) →
    Step-read (mk-config z (as (List admininstr) ((admininstr-CONST I32 i) ∷ (admininstr-VCONST V128 c-1) ∷ (admininstr-VLOAD-LANE V128 (mk-sz v-N) ao j) ∷ []))) (as (List admininstr) ((admininstr-VCONST V128 c) ∷ []))
  vload-lane-val-2 : ∀ (z : state) (i : (uN-fam0 (32))) (c-1 : (uN-fam0 (128))) (v-N : N) (ao : memarg) (j : laneidx) (c : (uN-fam0 (128))) (k : (uN-fam0 (v-N))) (v-M : M) → 
    ((ibytes- v-N k) ≡ (slice (BYTES (fun-mem z (mk-uN 0))) ((proj-uN-0 32 i) + (proj-uN-0 32 (OFFSET ao))) (coerce {B = ℕ} ((coerce {B = ℕ} v-N) / (coerce {B = ℕ} 8))))) →
    (v-N ≡ (jsize Jnn-I8)) →
    ((coerce {B = ℕ} v-M) ≡ ((coerce {B = ℕ} 128) / (coerce {B = ℕ} v-N))) →
    (c ≡ (inv-lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) (modify (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) c-1) (proj-uN-0 8 j) (λ (_ : (uN-fam0 (8))) → (mk-uN (proj-uN-0 v-N k)))))) →
    Step-read (mk-config z (as (List admininstr) ((admininstr-CONST I32 i) ∷ (admininstr-VCONST V128 c-1) ∷ (admininstr-VLOAD-LANE V128 (mk-sz v-N) ao j) ∷ []))) (as (List admininstr) ((admininstr-VCONST V128 c) ∷ []))
  vload-lane-val-3 : ∀ (z : state) (i : (uN-fam0 (32))) (c-1 : (uN-fam0 (128))) (v-N : N) (ao : memarg) (j : laneidx) (c : (uN-fam0 (128))) (k : (uN-fam0 (v-N))) (v-M : M) → 
    ((ibytes- v-N k) ≡ (slice (BYTES (fun-mem z (mk-uN 0))) ((proj-uN-0 32 i) + (proj-uN-0 32 (OFFSET ao))) (coerce {B = ℕ} ((coerce {B = ℕ} v-N) / (coerce {B = ℕ} 8))))) →
    (v-N ≡ (jsize Jnn-I16)) →
    ((coerce {B = ℕ} v-M) ≡ ((coerce {B = ℕ} 128) / (coerce {B = ℕ} v-N))) →
    (c ≡ (inv-lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) (modify (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) c-1) (proj-uN-0 8 j) (λ (_ : (uN-fam0 (16))) → (mk-uN (proj-uN-0 v-N k)))))) →
    Step-read (mk-config z (as (List admininstr) ((admininstr-CONST I32 i) ∷ (admininstr-VCONST V128 c-1) ∷ (admininstr-VLOAD-LANE V128 (mk-sz v-N) ao j) ∷ []))) (as (List admininstr) ((admininstr-VCONST V128 c) ∷ []))
  Step-read--memory-size : ∀ (z : state) (v-n : n) → 
    (((v-n * 64) * (Ki )) ≡ (length (BYTES (fun-mem z (mk-uN 0))))) →
    Step-read (mk-config z (as (List admininstr) (admininstr-MEMORY-SIZE ∷ []))) (as (List admininstr) ((admininstr-CONST I32 (mk-uN v-n)) ∷ []))
  memory-fill-trap : ∀ (z : state) (i : (uN-fam0 (32))) (v-val : val) (v-n : n) → 
    (((proj-uN-0 32 i) + v-n) > (length (BYTES (fun-mem z (mk-uN 0))))) →
    Step-read (mk-config z (as (List admininstr) ((admininstr-CONST I32 i) ∷ (admininstr-val v-val) ∷ (admininstr-CONST I32 (mk-uN v-n)) ∷ admininstr-MEMORY-FILL ∷ []))) (as (List admininstr) (admininstr-TRAP ∷ []))
  memory-fill-zero : ∀ (z : state) (i : (uN-fam0 (32))) (v-val : val) (v-n : n) → 
    (((proj-uN-0 32 i) + v-n) ≤ (length (BYTES (fun-mem z (mk-uN 0))))) →
    (v-n ≡ 0) →
    Step-read (mk-config z (as (List admininstr) ((admininstr-CONST I32 i) ∷ (admininstr-val v-val) ∷ (admininstr-CONST I32 (mk-uN v-n)) ∷ admininstr-MEMORY-FILL ∷ []))) []
  memory-fill-succ : ∀ (z : state) (i : (uN-fam0 (32))) (v-val : val) (v-n : n) → 
    (v-n ≢ 0) →
    (((proj-uN-0 32 i) + v-n) ≤ (length (BYTES (fun-mem z (mk-uN 0))))) →
    Step-read (mk-config z (as (List admininstr) ((admininstr-CONST I32 i) ∷ (admininstr-val v-val) ∷ (admininstr-CONST I32 (mk-uN v-n)) ∷ admininstr-MEMORY-FILL ∷ []))) (as (List admininstr) ((admininstr-CONST I32 i) ∷ (admininstr-val v-val) ∷ (admininstr-STORE I32 (just (mk-sz 8)) (memarg0 )) ∷ (admininstr-CONST I32 (mk-uN ((proj-uN-0 32 i) + 1))) ∷ (admininstr-val v-val) ∷ (admininstr-CONST I32 (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} v-n) – (coerce {B = ℕ} 1))))) ∷ admininstr-MEMORY-FILL ∷ []))
  memory-copy-trap : ∀ (z : state) (j : (uN-fam0 (32))) (i : (uN-fam0 (32))) (v-n : n) → 
    ((((proj-uN-0 32 i) + v-n) > (length (BYTES (fun-mem z (mk-uN 0))))) ⊎ (((proj-uN-0 32 j) + v-n) > (length (BYTES (fun-mem z (mk-uN 0)))))) →
    Step-read (mk-config z (as (List admininstr) ((admininstr-CONST I32 j) ∷ (admininstr-CONST I32 i) ∷ (admininstr-CONST I32 (mk-uN v-n)) ∷ admininstr-MEMORY-COPY ∷ []))) (as (List admininstr) (admininstr-TRAP ∷ []))
  memory-copy-zero : ∀ (z : state) (j : (uN-fam0 (32))) (i : (uN-fam0 (32))) (v-n : n) → 
    ((((proj-uN-0 32 i) + v-n) ≤ (length (BYTES (fun-mem z (mk-uN 0))))) × (((proj-uN-0 32 j) + v-n) ≤ (length (BYTES (fun-mem z (mk-uN 0)))))) →
    (v-n ≡ 0) →
    Step-read (mk-config z (as (List admininstr) ((admininstr-CONST I32 j) ∷ (admininstr-CONST I32 i) ∷ (admininstr-CONST I32 (mk-uN v-n)) ∷ admininstr-MEMORY-COPY ∷ []))) []
  memory-copy-le : ∀ (z : state) (j : (uN-fam0 (32))) (i : (uN-fam0 (32))) (v-n : n) → 
    (v-n ≢ 0) →
    ((((proj-uN-0 32 i) + v-n) ≤ (length (BYTES (fun-mem z (mk-uN 0))))) × (((proj-uN-0 32 j) + v-n) ≤ (length (BYTES (fun-mem z (mk-uN 0)))))) →
    ((proj-uN-0 32 j) ≤ (proj-uN-0 32 i)) →
    Step-read (mk-config z (as (List admininstr) ((admininstr-CONST I32 j) ∷ (admininstr-CONST I32 i) ∷ (admininstr-CONST I32 (mk-uN v-n)) ∷ admininstr-MEMORY-COPY ∷ []))) (as (List admininstr) ((admininstr-CONST I32 j) ∷ (admininstr-CONST I32 i) ∷ (admininstr-LOAD I32 (just (mk-loadop- (mk-sz 8) U)) (memarg0 )) ∷ (admininstr-STORE I32 (just (mk-sz 8)) (memarg0 )) ∷ (admininstr-CONST I32 (mk-uN ((proj-uN-0 32 j) + 1))) ∷ (admininstr-CONST I32 (mk-uN ((proj-uN-0 32 i) + 1))) ∷ (admininstr-CONST I32 (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} v-n) – (coerce {B = ℕ} 1))))) ∷ admininstr-MEMORY-COPY ∷ []))
  memory-copy-gt : ∀ (z : state) (j : (uN-fam0 (32))) (i : (uN-fam0 (32))) (v-n : n) → 
    ((proj-uN-0 32 j) > (proj-uN-0 32 i)) →
    (v-n ≢ 0) →
    ((((proj-uN-0 32 i) + v-n) ≤ (length (BYTES (fun-mem z (mk-uN 0))))) × (((proj-uN-0 32 j) + v-n) ≤ (length (BYTES (fun-mem z (mk-uN 0)))))) →
    Step-read (mk-config z (as (List admininstr) ((admininstr-CONST I32 j) ∷ (admininstr-CONST I32 i) ∷ (admininstr-CONST I32 (mk-uN v-n)) ∷ admininstr-MEMORY-COPY ∷ []))) (as (List admininstr) ((admininstr-CONST I32 (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} ((proj-uN-0 32 j) + v-n)) – (coerce {B = ℕ} 1))))) ∷ (admininstr-CONST I32 (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} ((proj-uN-0 32 i) + v-n)) – (coerce {B = ℕ} 1))))) ∷ (admininstr-LOAD I32 (just (mk-loadop- (mk-sz 8) U)) (memarg0 )) ∷ (admininstr-STORE I32 (just (mk-sz 8)) (memarg0 )) ∷ (admininstr-CONST I32 j) ∷ (admininstr-CONST I32 i) ∷ (admininstr-CONST I32 (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} v-n) – (coerce {B = ℕ} 1))))) ∷ admininstr-MEMORY-COPY ∷ []))
  memory-init-trap : ∀ (z : state) (j : (uN-fam0 (32))) (i : (uN-fam0 (32))) (v-n : n) (x : idx) → 
    ((((proj-uN-0 32 i) + v-n) > (length (datainst-BYTES (fun-data z x)))) ⊎ (((proj-uN-0 32 j) + v-n) > (length (BYTES (fun-mem z (mk-uN 0)))))) →
    Step-read (mk-config z (as (List admininstr) ((admininstr-CONST I32 j) ∷ (admininstr-CONST I32 i) ∷ (admininstr-CONST I32 (mk-uN v-n)) ∷ (admininstr-MEMORY-INIT x) ∷ []))) (as (List admininstr) (admininstr-TRAP ∷ []))
  memory-init-zero : ∀ (z : state) (j : (uN-fam0 (32))) (i : (uN-fam0 (32))) (v-n : n) (x : idx) → 
    ((((proj-uN-0 32 i) + v-n) ≤ (length (datainst-BYTES (fun-data z x)))) × (((proj-uN-0 32 j) + v-n) ≤ (length (BYTES (fun-mem z (mk-uN 0)))))) →
    (v-n ≡ 0) →
    Step-read (mk-config z (as (List admininstr) ((admininstr-CONST I32 j) ∷ (admininstr-CONST I32 i) ∷ (admininstr-CONST I32 (mk-uN v-n)) ∷ (admininstr-MEMORY-INIT x) ∷ []))) []
  memory-init-succ : ∀ (z : state) (j : (uN-fam0 (32))) (i : (uN-fam0 (32))) (v-n : n) (x : idx) → 
    ((proj-uN-0 32 i) < (length (datainst-BYTES (fun-data z x)))) →
    (v-n ≢ 0) →
    ((((proj-uN-0 32 i) + v-n) ≤ (length (datainst-BYTES (fun-data z x)))) × (((proj-uN-0 32 j) + v-n) ≤ (length (BYTES (fun-mem z (mk-uN 0)))))) →
    Step-read (mk-config z (as (List admininstr) ((admininstr-CONST I32 j) ∷ (admininstr-CONST I32 i) ∷ (admininstr-CONST I32 (mk-uN v-n)) ∷ (admininstr-MEMORY-INIT x) ∷ []))) (as (List admininstr) ((admininstr-CONST I32 j) ∷ (admininstr-CONST I32 (mk-uN (coerce {B = (ℕ)} (((datainst-BYTES (fun-data z x)) [ (proj-uN-0 32 i) ]!))))) ∷ (admininstr-STORE I32 (just (mk-sz 8)) (memarg0 )) ∷ (admininstr-CONST I32 (mk-uN ((proj-uN-0 32 j) + 1))) ∷ (admininstr-CONST I32 (mk-uN ((proj-uN-0 32 i) + 1))) ∷ (admininstr-CONST I32 (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} v-n) – (coerce {B = ℕ} 1))))) ∷ (admininstr-MEMORY-INIT x) ∷ []))

{- Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:5.1-5.109 -}
data Step : config → config → Set where
  pure : ∀ (z : state) (admininstr-lst : (List admininstr)) (admininstr'-lst : (List admininstr)) → 
    (Step-pure admininstr-lst admininstr'-lst) →
    Step (mk-config z admininstr-lst) (mk-config z admininstr'-lst)
  read : ∀ (z : state) (admininstr-lst : (List admininstr)) (admininstr'-lst : (List admininstr)) → 
    (Step-read (mk-config z admininstr-lst) admininstr'-lst) →
    Step (mk-config z admininstr-lst) (mk-config z admininstr'-lst)
  ctxt-label : ∀ (z : state) (v-n : n) (instr-0-lst : (List instr)) (admininstr-lst : (List admininstr)) (z' : state) (admininstr'-lst : (List admininstr)) → 
    (Step (mk-config z admininstr-lst) (mk-config z' admininstr'-lst)) →
    Step (mk-config z (as (List admininstr) ((LABEL- v-n instr-0-lst admininstr-lst) ∷ []))) (mk-config z' (as (List admininstr) ((LABEL- v-n instr-0-lst admininstr'-lst) ∷ [])))
  ctxt-frame : ∀ (s : store) (f : frame) (v-n : n) (f' : frame) (admininstr-lst : (List admininstr)) (s' : store) (f'' : frame) (admininstr'-lst : (List admininstr)) → 
    (Step (mk-config (mk-state s f') admininstr-lst) (mk-config (mk-state s' f'') admininstr'-lst)) →
    Step (mk-config (mk-state s f) (as (List admininstr) ((FRAME- v-n f' admininstr-lst) ∷ []))) (mk-config (mk-state s' f) (as (List admininstr) ((FRAME- v-n f'' admininstr'-lst) ∷ [])))
  ctxt-instrs : ∀ (z : state) (val-lst : (List val)) (admininstr-lst : (List admininstr)) (admininstr-1-lst : (List admininstr)) (z' : state) (admininstr'-lst : (List admininstr)) → 
    (Step (mk-config z admininstr-lst) (mk-config z' admininstr'-lst)) →
    ((val-lst ≢ []) ⊎ (admininstr-1-lst ≢ [])) →
    Step (mk-config z ((map (λ (v-val : val) → (admininstr-val v-val)) val-lst) ++ (admininstr-lst ++ admininstr-1-lst))) (mk-config z' ((map (λ (v-val : val) → (admininstr-val v-val)) val-lst) ++ (admininstr'-lst ++ admininstr-1-lst)))
  Step--local-set : ∀ (z : state) (v-val : val) (x : idx) → Step (mk-config z (as (List admininstr) ((admininstr-val v-val) ∷ (admininstr-LOCAL-SET x) ∷ []))) (mk-config (with-local z x v-val) [])
  Step--global-set : ∀ (z : state) (v-val : val) (x : idx) → Step (mk-config z (as (List admininstr) ((admininstr-val v-val) ∷ (admininstr-GLOBAL-SET x) ∷ []))) (mk-config (with-global z x v-val) [])
  table-set-trap : ∀ (z : state) (i : (uN-fam0 (32))) (v-ref : ref) (x : idx) → 
    ((proj-uN-0 32 i) ≥ (length (REFS (fun-table z x)))) →
    Step (mk-config z (as (List admininstr) ((admininstr-CONST I32 i) ∷ (admininstr-ref v-ref) ∷ (admininstr-TABLE-SET x) ∷ []))) (mk-config z (as (List admininstr) (admininstr-TRAP ∷ [])))
  table-set-val : ∀ (z : state) (i : (uN-fam0 (32))) (v-ref : ref) (x : idx) → 
    ((proj-uN-0 32 i) < (length (REFS (fun-table z x)))) →
    Step (mk-config z (as (List admininstr) ((admininstr-CONST I32 i) ∷ (admininstr-ref v-ref) ∷ (admininstr-TABLE-SET x) ∷ []))) (mk-config (with-table z x (proj-uN-0 32 i) v-ref) [])
  table-grow-succeed : ∀ (z : state) (v-ref : ref) (v-n : n) (x : idx) (ti : tableinst) → 
    ((growtable (fun-table z x) v-n v-ref) ≢ nothing) →
    ((unwrap! (growtable (fun-table z x) v-n v-ref)) ≡ ti) →
    Step (mk-config z (as (List admininstr) ((admininstr-ref v-ref) ∷ (admininstr-CONST I32 (mk-uN v-n)) ∷ (admininstr-TABLE-GROW x) ∷ []))) (mk-config (with-tableinst z x ti) (as (List admininstr) ((admininstr-CONST I32 (mk-uN (length (REFS (fun-table z x))))) ∷ [])))
  table-grow-fail : ∀ (z : state) (v-ref : ref) (v-n : n) (x : idx) → Step (mk-config z (as (List admininstr) ((admininstr-ref v-ref) ∷ (admininstr-CONST I32 (mk-uN v-n)) ∷ (admininstr-TABLE-GROW x) ∷ []))) (mk-config z (as (List admininstr) ((admininstr-CONST I32 (mk-uN (inv-signed- 32 (0 – (coerce {B = ℕ} 1))))) ∷ [])))
  Step--elem-drop : ∀ (z : state) (x : idx) → Step (mk-config z (as (List admininstr) ((admininstr-ELEM-DROP x) ∷ []))) (mk-config (with-elem z x []) [])
  store-num-trap : ∀ (z : state) (i : (uN-fam0 (32))) (nt : numtype) (c : (num- nt)) (ao : memarg) → 
    ((size (valtype-numtype nt)) ≢ nothing) →
    ((((proj-uN-0 32 i) + (proj-uN-0 32 (OFFSET ao))) + (coerce {B = ℕ} ((coerce {B = ℕ} (unwrap! (size (valtype-numtype nt)))) / (coerce {B = ℕ} 8)))) > (length (BYTES (fun-mem z (mk-uN 0))))) →
    Step (mk-config z (as (List admininstr) ((admininstr-CONST I32 i) ∷ (admininstr-CONST nt c) ∷ (admininstr-STORE nt nothing ao) ∷ []))) (mk-config z (as (List admininstr) (admininstr-TRAP ∷ [])))
  store-num-val : ∀ (z : state) (i : (uN-fam0 (32))) (nt : numtype) (c : (num- nt)) (ao : memarg) (b-lst : (List byte)) → 
    ((size (valtype-numtype nt)) ≢ nothing) →
    (b-lst ≡ (nbytes- nt c)) →
    Step (mk-config z (as (List admininstr) ((admininstr-CONST I32 i) ∷ (admininstr-CONST nt c) ∷ (admininstr-STORE nt nothing ao) ∷ []))) (mk-config (with-mem z (mk-uN 0) ((proj-uN-0 32 i) + (proj-uN-0 32 (OFFSET ao))) (coerce {B = ℕ} ((coerce {B = ℕ} (unwrap! (size (valtype-numtype nt)))) / (coerce {B = ℕ} 8))) b-lst) [])
  store-pack-trap-0 : ∀ (z : state) (i : (uN-fam0 (32))) (c : (uN-fam0 (32))) (v-n : n) (ao : memarg) → 
    ((((proj-uN-0 32 i) + (proj-uN-0 32 (OFFSET ao))) + (coerce {B = ℕ} ((coerce {B = ℕ} v-n) / (coerce {B = ℕ} 8)))) > (length (BYTES (fun-mem z (mk-uN 0))))) →
    Step (mk-config z (as (List admininstr) ((admininstr-CONST I32 i) ∷ (admininstr-CONST (numtype-Inn Inn-I32) c) ∷ (admininstr-STORE (numtype-Inn Inn-I32) (just (mk-sz v-n)) ao) ∷ []))) (mk-config z (as (List admininstr) (admininstr-TRAP ∷ [])))
  store-pack-trap-1 : ∀ (z : state) (i : (uN-fam0 (32))) (c : (uN-fam0 (64))) (v-n : n) (ao : memarg) → 
    ((((proj-uN-0 32 i) + (proj-uN-0 32 (OFFSET ao))) + (coerce {B = ℕ} ((coerce {B = ℕ} v-n) / (coerce {B = ℕ} 8)))) > (length (BYTES (fun-mem z (mk-uN 0))))) →
    Step (mk-config z (as (List admininstr) ((admininstr-CONST I32 i) ∷ (admininstr-CONST (numtype-Inn Inn-I64) c) ∷ (admininstr-STORE (numtype-Inn Inn-I64) (just (mk-sz v-n)) ao) ∷ []))) (mk-config z (as (List admininstr) (admininstr-TRAP ∷ [])))
  store-pack-val-0 : ∀ (z : state) (i : (uN-fam0 (32))) (c : (uN-fam0 (32))) (v-n : n) (ao : memarg) (b-lst : (List byte)) → 
    ((size (valtype-Inn Inn-I32)) ≢ nothing) →
    (b-lst ≡ (ibytes- v-n (wrap-- (unwrap! (size (valtype-Inn Inn-I32))) v-n c))) →
    Step (mk-config z (as (List admininstr) ((admininstr-CONST I32 i) ∷ (admininstr-CONST (numtype-Inn Inn-I32) c) ∷ (admininstr-STORE (numtype-Inn Inn-I32) (just (mk-sz v-n)) ao) ∷ []))) (mk-config (with-mem z (mk-uN 0) ((proj-uN-0 32 i) + (proj-uN-0 32 (OFFSET ao))) (coerce {B = ℕ} ((coerce {B = ℕ} v-n) / (coerce {B = ℕ} 8))) b-lst) [])
  store-pack-val-1 : ∀ (z : state) (i : (uN-fam0 (32))) (c : (uN-fam0 (64))) (v-n : n) (ao : memarg) (b-lst : (List byte)) → 
    ((size (valtype-Inn Inn-I64)) ≢ nothing) →
    (b-lst ≡ (ibytes- v-n (wrap-- (unwrap! (size (valtype-Inn Inn-I64))) v-n c))) →
    Step (mk-config z (as (List admininstr) ((admininstr-CONST I32 i) ∷ (admininstr-CONST (numtype-Inn Inn-I64) c) ∷ (admininstr-STORE (numtype-Inn Inn-I64) (just (mk-sz v-n)) ao) ∷ []))) (mk-config (with-mem z (mk-uN 0) ((proj-uN-0 32 i) + (proj-uN-0 32 (OFFSET ao))) (coerce {B = ℕ} ((coerce {B = ℕ} v-n) / (coerce {B = ℕ} 8))) b-lst) [])
  vstore-oob : ∀ (z : state) (i : (uN-fam0 (32))) (c : (uN-fam0 (128))) (ao : memarg) → 
    ((size valtype-V128) ≢ nothing) →
    ((((proj-uN-0 32 i) + (proj-uN-0 32 (OFFSET ao))) + (coerce {B = ℕ} ((coerce {B = ℕ} (unwrap! (size valtype-V128))) / (coerce {B = ℕ} 8)))) > (length (BYTES (fun-mem z (mk-uN 0))))) →
    Step (mk-config z (as (List admininstr) ((admininstr-CONST I32 i) ∷ (admininstr-VCONST V128 c) ∷ (admininstr-VSTORE V128 ao) ∷ []))) (mk-config z (as (List admininstr) (admininstr-TRAP ∷ [])))
  vstore-val : ∀ (z : state) (i : (uN-fam0 (32))) (c : (uN-fam0 (128))) (ao : memarg) (b-lst : (List byte)) → 
    ((size valtype-V128) ≢ nothing) →
    (b-lst ≡ (vbytes- V128 c)) →
    Step (mk-config z (as (List admininstr) ((admininstr-CONST I32 i) ∷ (admininstr-VCONST V128 c) ∷ (admininstr-VSTORE V128 ao) ∷ []))) (mk-config (with-mem z (mk-uN 0) ((proj-uN-0 32 i) + (proj-uN-0 32 (OFFSET ao))) (coerce {B = ℕ} ((coerce {B = ℕ} (unwrap! (size valtype-V128))) / (coerce {B = ℕ} 8))) b-lst) [])
  vstore-lane-oob : ∀ (z : state) (i : (uN-fam0 (32))) (c : (uN-fam0 (128))) (v-N : N) (ao : memarg) (j : laneidx) → 
    ((((proj-uN-0 32 i) + (proj-uN-0 32 (OFFSET ao))) + v-N) > (length (BYTES (fun-mem z (mk-uN 0))))) →
    Step (mk-config z (as (List admininstr) ((admininstr-CONST I32 i) ∷ (admininstr-VCONST V128 c) ∷ (admininstr-VSTORE-LANE V128 (mk-sz v-N) ao j) ∷ []))) (mk-config z (as (List admininstr) (admininstr-TRAP ∷ [])))
  vstore-lane-val-0 : ∀ (z : state) (i : (uN-fam0 (32))) (c : (uN-fam0 (128))) (v-N : N) (ao : memarg) (j : laneidx) (b-lst : (List byte)) (v-M : M) → 
    (v-N ≡ (jsize Jnn-I32)) →
    ((coerce {B = ℕ} v-M) ≡ ((coerce {B = ℕ} 128) / (coerce {B = ℕ} v-N))) →
    ((proj-uN-0 8 j) < (length (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) c))) →
    (b-lst ≡ (ibytes- v-N (mk-uN (proj-uN-0 (lsize (lanetype-Jnn Jnn-I32)) ((lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim v-M)) c) [ (proj-uN-0 8 j) ]!))))) →
    Step (mk-config z (as (List admininstr) ((admininstr-CONST I32 i) ∷ (admininstr-VCONST V128 c) ∷ (admininstr-VSTORE-LANE V128 (mk-sz v-N) ao j) ∷ []))) (mk-config (with-mem z (mk-uN 0) ((proj-uN-0 32 i) + (proj-uN-0 32 (OFFSET ao))) (coerce {B = ℕ} ((coerce {B = ℕ} v-N) / (coerce {B = ℕ} 8))) b-lst) [])
  vstore-lane-val-1 : ∀ (z : state) (i : (uN-fam0 (32))) (c : (uN-fam0 (128))) (v-N : N) (ao : memarg) (j : laneidx) (b-lst : (List byte)) (v-M : M) → 
    (v-N ≡ (jsize Jnn-I64)) →
    ((coerce {B = ℕ} v-M) ≡ ((coerce {B = ℕ} 128) / (coerce {B = ℕ} v-N))) →
    ((proj-uN-0 8 j) < (length (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) c))) →
    (b-lst ≡ (ibytes- v-N (mk-uN (proj-uN-0 (lsize (lanetype-Jnn Jnn-I64)) ((lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim v-M)) c) [ (proj-uN-0 8 j) ]!))))) →
    Step (mk-config z (as (List admininstr) ((admininstr-CONST I32 i) ∷ (admininstr-VCONST V128 c) ∷ (admininstr-VSTORE-LANE V128 (mk-sz v-N) ao j) ∷ []))) (mk-config (with-mem z (mk-uN 0) ((proj-uN-0 32 i) + (proj-uN-0 32 (OFFSET ao))) (coerce {B = ℕ} ((coerce {B = ℕ} v-N) / (coerce {B = ℕ} 8))) b-lst) [])
  vstore-lane-val-2 : ∀ (z : state) (i : (uN-fam0 (32))) (c : (uN-fam0 (128))) (v-N : N) (ao : memarg) (j : laneidx) (b-lst : (List byte)) (v-M : M) → 
    (v-N ≡ (jsize Jnn-I8)) →
    ((coerce {B = ℕ} v-M) ≡ ((coerce {B = ℕ} 128) / (coerce {B = ℕ} v-N))) →
    ((proj-uN-0 8 j) < (length (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) c))) →
    (b-lst ≡ (ibytes- v-N (mk-uN (proj-uN-0 (lsize (lanetype-Jnn Jnn-I8)) ((lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim v-M)) c) [ (proj-uN-0 8 j) ]!))))) →
    Step (mk-config z (as (List admininstr) ((admininstr-CONST I32 i) ∷ (admininstr-VCONST V128 c) ∷ (admininstr-VSTORE-LANE V128 (mk-sz v-N) ao j) ∷ []))) (mk-config (with-mem z (mk-uN 0) ((proj-uN-0 32 i) + (proj-uN-0 32 (OFFSET ao))) (coerce {B = ℕ} ((coerce {B = ℕ} v-N) / (coerce {B = ℕ} 8))) b-lst) [])
  vstore-lane-val-3 : ∀ (z : state) (i : (uN-fam0 (32))) (c : (uN-fam0 (128))) (v-N : N) (ao : memarg) (j : laneidx) (b-lst : (List byte)) (v-M : M) → 
    (v-N ≡ (jsize Jnn-I16)) →
    ((coerce {B = ℕ} v-M) ≡ ((coerce {B = ℕ} 128) / (coerce {B = ℕ} v-N))) →
    ((proj-uN-0 8 j) < (length (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) c))) →
    (b-lst ≡ (ibytes- v-N (mk-uN (proj-uN-0 (lsize (lanetype-Jnn Jnn-I16)) ((lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim v-M)) c) [ (proj-uN-0 8 j) ]!))))) →
    Step (mk-config z (as (List admininstr) ((admininstr-CONST I32 i) ∷ (admininstr-VCONST V128 c) ∷ (admininstr-VSTORE-LANE V128 (mk-sz v-N) ao j) ∷ []))) (mk-config (with-mem z (mk-uN 0) ((proj-uN-0 32 i) + (proj-uN-0 32 (OFFSET ao))) (coerce {B = ℕ} ((coerce {B = ℕ} v-N) / (coerce {B = ℕ} 8))) b-lst) [])
  memory-grow-succeed : ∀ (z : state) (v-n : n) (mi : meminst) → 
    ((growmemory (fun-mem z (mk-uN 0)) v-n) ≢ nothing) →
    ((unwrap! (growmemory (fun-mem z (mk-uN 0)) v-n)) ≡ mi) →
    Step (mk-config z (as (List admininstr) ((admininstr-CONST I32 (mk-uN v-n)) ∷ admininstr-MEMORY-GROW ∷ []))) (mk-config (with-meminst z (mk-uN 0) mi) (as (List admininstr) ((admininstr-CONST I32 (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} (length (BYTES (fun-mem z (mk-uN 0))))) / (coerce {B = ℕ} (64 * (Ki ))))))) ∷ [])))
  memory-grow-fail : ∀ (z : state) (v-n : n) → Step (mk-config z (as (List admininstr) ((admininstr-CONST I32 (mk-uN v-n)) ∷ admininstr-MEMORY-GROW ∷ []))) (mk-config z (as (List admininstr) ((admininstr-CONST I32 (mk-uN (inv-signed- 32 (0 – (coerce {B = ℕ} 1))))) ∷ [])))
  Step--data-drop : ∀ (z : state) (x : idx) → Step (mk-config z (as (List admininstr) ((admininstr-DATA-DROP x) ∷ []))) (mk-config (with-data z x []) [])

{- Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:8.1-8.77 -}
data Steps : config → config → Set where
  Steps--refl : ∀ (z : state) (admininstr-lst : (List admininstr)) → Steps (mk-config z admininstr-lst) (mk-config z admininstr-lst)
  trans : ∀ (z : state) (admininstr-lst : (List admininstr)) (z'' : state) (admininstr''-lst : (List admininstr)) (z' : state) (admininstr'-lst : (List admininstr)) → 
    (Step (mk-config z admininstr-lst) (mk-config z' admininstr'-lst)) →
    (Steps (mk-config z' admininstr'-lst) (mk-config z'' admininstr''-lst)) →
    Steps (mk-config z admininstr-lst) (mk-config z'' admininstr''-lst)

{- Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:29.1-29.83 -}
data Eval-expr : state → expr → state → (List val) → Set where
  mk-Eval-expr : ∀ (z : state) (instr-lst : (List instr)) (z' : state) (val-lst : (List val)) → 
    (Steps (mk-config z (map (λ (v-instr : instr) → (admininstr-instr v-instr)) instr-lst)) (mk-config z' (map (λ (v-val : val) → (admininstr-val v-val)) val-lst))) →
    Eval-expr z instr-lst z' val-lst

{- Auxiliary Definition at: ../specification/wasm-2.0/9-module.spectec:5.1-5.36 -}
{-# TERMINATING #-}
funcs : (var-0-lst : (List externaddr)) → (List funcaddr)
funcs [] = []
funcs ((externaddr-FUNC fa) ∷ externaddr'-lst) = ((fa ∷ []) ++ (funcs externaddr'-lst))
funcs (v-externaddr ∷ externaddr'-lst) = (funcs externaddr'-lst)
funcs var-0-lst = []

{- Auxiliary Definition at: ../specification/wasm-2.0/9-module.spectec:11.1-11.40 -}
{-# TERMINATING #-}
globals : (var-0-lst : (List externaddr)) → (List globaladdr)
globals [] = []
globals ((externaddr-GLOBAL ga) ∷ externaddr'-lst) = ((ga ∷ []) ++ (globals externaddr'-lst))
globals (v-externaddr ∷ externaddr'-lst) = (globals externaddr'-lst)
globals var-0-lst = []

{- Auxiliary Definition at: ../specification/wasm-2.0/9-module.spectec:17.1-17.38 -}
{-# TERMINATING #-}
tables : (var-0-lst : (List externaddr)) → (List tableaddr)
tables [] = []
tables ((externaddr-TABLE ta) ∷ externaddr'-lst) = ((ta ∷ []) ++ (tables externaddr'-lst))
tables (v-externaddr ∷ externaddr'-lst) = (tables externaddr'-lst)
tables var-0-lst = []

{- Auxiliary Definition at: ../specification/wasm-2.0/9-module.spectec:23.1-23.34 -}
{-# TERMINATING #-}
mems : (var-0-lst : (List externaddr)) → (List memaddr)
mems [] = []
mems ((externaddr-MEM ma) ∷ externaddr'-lst) = ((ma ∷ []) ++ (mems externaddr'-lst))
mems (v-externaddr ∷ externaddr'-lst) = (mems externaddr'-lst)
mems var-0-lst = []

{- Auxiliary Definition at: ../specification/wasm-2.0/9-module.spectec:36.1-36.60 -}
postulate allocfunc : ∀ (v-store : store) (v-moduleinst : moduleinst) (v-func : func) → (store × funcaddr)

{- Auxiliary Definition at: ../specification/wasm-2.0/9-module.spectec:41.1-41.63 -}
{-# TERMINATING #-}
allocfuncs : (v-store : store) (v-moduleinst : moduleinst) (var-0-lst : (List func)) → (store × (List funcaddr))
allocfuncs s v-moduleinst [] = (s , [])
allocfuncs s v-moduleinst (v-func ∷ func'-lst) = let (s-1 , fa) = (allocfunc s v-moduleinst v-func) in let (s-2 , fa'-lst) = (allocfuncs s-1 v-moduleinst func'-lst) in (s-2 , ((fa ∷ []) ++ fa'-lst))
allocfuncs v-store v-moduleinst var-0-lst = (default-val , [])

{- Auxiliary Definition at: ../specification/wasm-2.0/9-module.spectec:47.1-47.63 -}
postulate allocglobal : ∀ (v-store : store) (v-globaltype : globaltype) (v-val : val) → (store × globaladdr)

{- Auxiliary Definition at: ../specification/wasm-2.0/9-module.spectec:51.1-51.67 -}
{-# TERMINATING #-}
allocglobals : (v-store : store) (var-0-lst : (List globaltype)) (var-1-lst : (List val)) → (store × (List globaladdr))
allocglobals s [] [] = (s , [])
allocglobals s (v-globaltype ∷ globaltype'-lst) (v-val ∷ val'-lst) = let (s-1 , ga) = (allocglobal s v-globaltype v-val) in let (s-2 , ga'-lst) = (allocglobals s-1 globaltype'-lst val'-lst) in (s-2 , ((ga ∷ []) ++ ga'-lst))
allocglobals v-store var-0-lst var-1-lst = (default-val , [])

{- Auxiliary Definition at: ../specification/wasm-2.0/9-module.spectec:57.1-57.55 -}
postulate alloctable : ∀ (v-store : store) (v-tabletype : tabletype) → (store × tableaddr)

{- Auxiliary Definition at: ../specification/wasm-2.0/9-module.spectec:61.1-61.58 -}
{-# TERMINATING #-}
alloctables : (v-store : store) (var-0-lst : (List tabletype)) → (store × (List tableaddr))
alloctables s [] = (s , [])
alloctables s (v-tabletype ∷ tabletype'-lst) = let (s-1 , ta) = (alloctable s v-tabletype) in let (s-2 , ta'-lst) = (alloctables s-1 tabletype'-lst) in (s-2 , ((ta ∷ []) ++ ta'-lst))
alloctables v-store var-0-lst = (default-val , [])

{- Auxiliary Definition at: ../specification/wasm-2.0/9-module.spectec:67.1-67.49 -}
postulate allocmem : ∀ (v-store : store) (v-memtype : memtype) → (store × memaddr)

{- Auxiliary Definition at: ../specification/wasm-2.0/9-module.spectec:71.1-71.52 -}
{-# TERMINATING #-}
allocmems : (v-store : store) (var-0-lst : (List memtype)) → (store × (List memaddr))
allocmems s [] = (s , [])
allocmems s (v-memtype ∷ memtype'-lst) = let (s-1 , ma) = (allocmem s v-memtype) in let (s-2 , ma'-lst) = (allocmems s-1 memtype'-lst) in (s-2 , ((ma ∷ []) ++ ma'-lst))
allocmems v-store var-0-lst = (default-val , [])

{- Auxiliary Definition at: ../specification/wasm-2.0/9-module.spectec:77.1-77.57 -}
postulate allocelem : ∀ (v-store : store) (v-reftype : reftype) (var-0-lst : (List ref)) → (store × elemaddr)

{- Auxiliary Definition at: ../specification/wasm-2.0/9-module.spectec:81.1-81.63 -}
{-# TERMINATING #-}
allocelems : (v-store : store) (var-0-lst : (List reftype)) (var-1-lst-lst : (List (List ref))) → (store × (List elemaddr))
allocelems s [] [] = (s , [])
allocelems s (rt ∷ rt'-lst) (ref-lst ∷ ref'-lst-lst) = let (s-1 , ea) = (allocelem s rt ref-lst) in let (s-2 , ea'-lst) = (allocelems s-1 rt'-lst ref'-lst-lst) in (s-2 , ((ea ∷ []) ++ ea'-lst))
allocelems v-store var-0-lst var-1-lst-lst = (default-val , [])

{- Auxiliary Definition at: ../specification/wasm-2.0/9-module.spectec:87.1-87.49 -}
postulate allocdata : ∀ (v-store : store) (var-0-lst : (List byte)) → (store × dataaddr)

{- Auxiliary Definition at: ../specification/wasm-2.0/9-module.spectec:91.1-91.54 -}
{-# TERMINATING #-}
allocdatas : (v-store : store) (var-0-lst-lst : (List (List byte))) → (store × (List dataaddr))
allocdatas s [] = (s , [])
allocdatas s (byte-lst ∷ byte'-lst-lst) = let (s-1 , da) = (allocdata s byte-lst) in let (s-2 , da'-lst) = (allocdatas s-1 byte'-lst-lst) in (s-2 , ((da ∷ []) ++ da'-lst))
allocdatas v-store var-0-lst-lst = (default-val , [])

{- Auxiliary Definition at: ../specification/wasm-2.0/9-module.spectec:100.1-100.83 -}
{-# TERMINATING #-}
instexport : (var-0-lst : (List funcaddr)) (var-1-lst : (List globaladdr)) (var-2-lst : (List tableaddr)) (var-3-lst : (List memaddr)) (v-export : export) → exportinst
instexport fa-lst ga-lst ta-lst ma-lst (EXPORT v-name (externidx-FUNC x)) = record { NAME = v-name ; ADDR = (externaddr-FUNC (fa-lst [ (proj-uN-0 32 x) ]!)) }
instexport fa-lst ga-lst ta-lst ma-lst (EXPORT v-name (externidx-GLOBAL x)) = record { NAME = v-name ; ADDR = (externaddr-GLOBAL (ga-lst [ (proj-uN-0 32 x) ]!)) }
instexport fa-lst ga-lst ta-lst ma-lst (EXPORT v-name (externidx-TABLE x)) = record { NAME = v-name ; ADDR = (externaddr-TABLE (ta-lst [ (proj-uN-0 32 x) ]!)) }
instexport fa-lst ga-lst ta-lst ma-lst (EXPORT v-name (externidx-MEM x)) = record { NAME = v-name ; ADDR = (externaddr-MEM (ma-lst [ (proj-uN-0 32 x) ]!)) }
instexport var-0-lst var-1-lst var-2-lst var-3-lst v-export = default-val

{- Auxiliary Definition at: ../specification/wasm-2.0/9-module.spectec:107.1-107.82 -}
postulate allocmodule : ∀ (v-store : store) (v-module : module') (var-0-lst : (List externaddr)) (var-1-lst : (List val)) (var-2-lst-lst : (List (List ref))) → (store × moduleinst)

{- Auxiliary Definition at: ../specification/wasm-2.0/9-module.spectec:154.1-154.33 -}
{-# TERMINATING #-}
runelem : (v-elem : elem) (v-idx : idx) → (List instr)
runelem (ELEM v-reftype expr-lst PASSIVE) i = []
runelem (ELEM v-reftype expr-lst DECLARE) i = (as (List instr) ((ELEM-DROP i) ∷ []))
runelem (ELEM v-reftype expr-lst (ACTIVE x instr-lst)) i = let v-n = (length expr-lst) in (instr-lst ++ (as (List instr) ((CONST I32 (mk-uN 0)) ∷ (CONST I32 (mk-uN v-n)) ∷ (TABLE-INIT x i) ∷ (ELEM-DROP i) ∷ [])))
runelem v-elem v-idx = []

{- Auxiliary Definition at: ../specification/wasm-2.0/9-module.spectec:161.1-161.47 -}
{-# TERMINATING #-}
rundata : (v-data : data') (v-idx : idx) → (Maybe (List instr))
rundata (DATA byte-lst datamode-PASSIVE) i = (just [])
rundata (DATA byte-lst (datamode-ACTIVE (mk-uN (zero)) instr-lst)) i = let v-n = (length byte-lst) in (just (instr-lst ++ (as (List instr) ((CONST I32 (mk-uN 0)) ∷ (CONST I32 (mk-uN v-n)) ∷ (MEMORY-INIT i) ∷ (DATA-DROP i) ∷ []))))
rundata x0 x1 = nothing

{- Auxiliary Definition at: ../specification/wasm-2.0/9-module.spectec:167.1-167.54 -}
postulate instantiate : ∀ (v-store : store) (v-module : module') (var-0-lst : (List externaddr)) → config

{- Auxiliary Definition at: ../specification/wasm-2.0/9-module.spectec:196.1-196.44 -}
postulate invoke : ∀ (v-store : store) (v-funcaddr : funcaddr) (var-0-lst : (List val)) → config
