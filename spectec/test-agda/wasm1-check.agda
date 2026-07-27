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

{- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:119.14-119.17 -}
data r-MUT : Set where
  MUT : r-MUT

instance
  inh-r-MUT : Inhabited r-MUT
  inh-r-MUT = record { default-val = MUT }

{- Type Alias Definition at: ../specification/wasm-1.0/0-aux.spectec:7.1-7.27 -}
N : Set
N = ℕ

{- Type Alias Definition at: ../specification/wasm-1.0/0-aux.spectec:8.1-8.27 -}
M : Set
M = ℕ

{- Type Alias Definition at: ../specification/wasm-1.0/0-aux.spectec:9.1-9.27 -}
n : Set
n = ℕ

{- Type Alias Definition at: ../specification/wasm-1.0/0-aux.spectec:10.1-10.27 -}
m : Set
m = ℕ

{- Auxiliary Definition at: ../specification/wasm-1.0/0-aux.spectec:15.1-15.14 -}
Ki : ℕ
Ki = 1024

{- Auxiliary Definition at: ../specification/wasm-1.0/0-aux.spectec:21.1-21.25 -}
{-# TERMINATING #-}
min : (nat : ℕ) (nat-0 : ℕ) → ℕ
min i j = (if (i ≤? j) then i else j)

{- Auxiliary Definition at: ../specification/wasm-1.0/0-aux.spectec:25.1-25.21 -}
{-# TERMINATING #-}
sum : (var-0-lst : (List ℕ)) → ℕ
sum [] = 0
sum (v-n ∷ n'-lst) = (v-n + (sum n'-lst))
sum var-0-lst = default-val

{- Auxiliary Definition at: ../specification/wasm-1.0/0-aux.spectec:32.1-32.58 -}
{-# TERMINATING #-}
opt- : (X : Set) (var-0-lst : (List X)) → (Maybe (Maybe X))
opt- X [] = (just nothing)
opt- X (w ∷ []) = (just (just w))
opt- X x1 = nothing

{- Auxiliary Definition at: ../specification/wasm-1.0/0-aux.spectec:36.1-36.45 -}
{-# TERMINATING #-}
list- : (X : Set) (var-0-opt : (Maybe X)) → (List X)
list- X nothing = []
list- X (just w) = (w ∷ [])
list- X var-0-opt = []

{- Auxiliary Definition at: ../specification/wasm-1.0/0-aux.spectec:40.1-40.59 -}
{-# TERMINATING #-}
concat- : (X : Set) (var-0-lst-lst : (List (List X))) → (List X)
concat- X [] = []
concat- X (w-lst ∷ w'-lst-lst) = (w-lst ++ (concat- X w'-lst-lst))
concat- X var-0-lst-lst = []

{- Auxiliary Definition at: ../specification/wasm-1.0/0-aux.spectec:44.1-44.78 -}
{-# TERMINATING #-}
disjoint- : (X : Set) {{_ : HasEq X}} (var-0-lst : (List X)) → Bool
disjoint- X [] = true
disjoint- X (w ∷ w'-lst) = ((not (w ∈ᵇ w'-lst)) ∧ (disjoint- X w'-lst))
disjoint- X var-0-lst = default-val

{- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:6.1-6.49 -}
data list-fam0 (X : Set) : Set where
  mk-list : (X-lst : (List X)) → list-fam0 X {- 1 premise(s) dropped -}

list : (X : Set) → Set
list X = list-fam0 X
list _ = ⊤

{- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:15.1-15.50 -}
data byte : Set where
  mk-byte : (i : ℕ) → byte {- 1 premise(s) dropped -}

instance
  inh-byte : Inhabited byte
  inh-byte = record { default-val = (mk-byte (default-val)) }

{- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:17.1-18.25 -}
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

{- Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:17.1-18.25 -}
{-# TERMINATING #-}
proj-uN-0 : (v-N : N) (x : (uN-fam0 (v-N))) → (ℕ)
proj-uN-0 v-N (mk-uN v-num-0) = (v-num-0)
proj-uN-0 v-N x = (default-val)

instance
  proj-uN-0-coercion : {v-N : N} → Coerce (uN-fam0 (v-N)) (ℕ)
  proj-uN-0-coercion = record { coerce = proj-uN-0 _ }

{- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:19.1-20.49 -}
data sN-fam0 (v-N : N) : Set where
  mk-sN : (i : ℕ) → sN-fam0 v-N {- 1 premise(s) dropped -}

sN : (v-N : N) → Set
sN v-N = sN-fam0 v-N
sN _ = ⊤

{- Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:21.1-22.8 -}
iN : (v-N : N) → Set
iN v-N = (uN-fam0 (v-N))
iN _ = ⊤

inh-iN-fun : (v-N : N) → Inhabited (iN v-N)
inh-iN-fun v-N = record { default-val = (Inhabited.default-val (inh-uN-fun v-N)) }

{- Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:24.1-24.20 -}
u31 : Set
u31 = (uN-fam0 (31))

{- Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:25.1-25.20 -}
u32 : Set
u32 = (uN-fam0 (32))

{- Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:26.1-26.20 -}
u64 : Set
u64 = (uN-fam0 (64))

{- Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:28.1-28.20 -}
i32 : Set
i32 = (uN-fam0 (32))

{- Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:29.1-29.20 -}
i64 : Set
i64 = (uN-fam0 (64))

{- Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:36.1-36.35 -}
{-# TERMINATING #-}
signif : (v-N : N) → (Maybe ℕ)
signif (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (zero))))))))))))))))))))))))))))))))) = (just 23)
signif (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (zero))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = (just 52)
signif x0 = nothing

{- Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:40.1-40.34 -}
{-# TERMINATING #-}
expon : (v-N : N) → (Maybe ℕ)
expon (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (zero))))))))))))))))))))))))))))))))) = (just 8)
expon (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (zero))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = (just 11)
expon x0 = nothing

{- Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:44.1-44.30 -}
{-# TERMINATING #-}
fun-M : (v-N : N) → ℕ
fun-M v-N = (unwrap! (signif v-N))

{- Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:47.1-47.30 -}
{-# TERMINATING #-}
E : (v-N : N) → ℕ
E v-N = (unwrap! (expon v-N))

{- Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:54.1-54.30 -}
exp : Set
exp = ℕ

{- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:55.1-59.84 -}
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

{- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:50.1-52.35 -}
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

{- Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:61.1-61.20 -}
f32 : Set
f32 = (fN-fam0 (32))

{- Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:62.1-62.20 -}
f64 : Set
f64 = (fN-fam0 (64))

{- Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:64.1-64.39 -}
{-# TERMINATING #-}
fzero : (v-N : N) → (fN-fam0 (v-N))
fzero v-N = (POS (SUBNORM 0))

{- Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:67.1-67.39 -}
{-# TERMINATING #-}
fone : (v-N : N) → (fN-fam0 (v-N))
fone v-N = (POS (NORM 1 (coerce {B = ℕ} 0)))

{- Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:70.1-70.21 -}
{-# TERMINATING #-}
canon- : (v-N : N) → ℕ
canon- v-N = (2 ^ (coerce {B = ℕ} ((coerce {B = ℕ} (unwrap! (signif v-N))) – (coerce {B = ℕ} 1))))

{- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:78.1-78.85 -}
data char : Set where
  mk-char : (i : ℕ) → char {- 1 premise(s) dropped -}

instance
  inh-char : Inhabited char
  inh-char = record { default-val = (mk-char (default-val)) }

{- Axiom Definition at: ../specification/wasm-1.0/1-syntax.spectec:80.1-80.25 -}
postulate utf8 : ∀ (var-0-lst : (List char)) → (List byte)

{- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:82.1-82.70 -}
data name : Set where
  mk-name : (char-lst : (List char)) → name {- 1 premise(s) dropped -}

instance
  inh-name : Inhabited name
  inh-name = record { default-val = (mk-name ([])) }

{- Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:91.1-91.36 -}
idx : Set
idx = u32

{- Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:93.1-93.45 -}
typeidx : Set
typeidx = idx

{- Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:94.1-94.49 -}
funcidx : Set
funcidx = idx

{- Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:95.1-95.49 -}
globalidx : Set
globalidx = idx

{- Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:96.1-96.47 -}
tableidx : Set
tableidx = idx

{- Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:97.1-97.46 -}
memidx : Set
memidx = idx

{- Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:98.1-98.47 -}
labelidx : Set
labelidx = idx

{- Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:99.1-99.47 -}
localidx : Set
localidx = idx

{- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:108.1-109.26 -}
data valtype : Set where
  I32 : valtype
  I64 : valtype
  F32 : valtype
  F64 : valtype

instance
  inh-valtype : Inhabited valtype
  inh-valtype = record { default-val = I32 }

{- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:111.1-111.38 -}
data Inn : Set where
  Inn-I32 : Inn
  Inn-I64 : Inn

{- Auxiliary Definition at:  -}
{-# TERMINATING #-}
valtype-Inn : (var-0 : Inn) → valtype
valtype-Inn Inn-I32 = I32
valtype-Inn Inn-I64 = I64
valtype-Inn var-0 = default-val

{- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:112.1-112.38 -}
data Fnn : Set where
  Fnn-F32 : Fnn
  Fnn-F64 : Fnn

{- Auxiliary Definition at:  -}
{-# TERMINATING #-}
valtype-Fnn : (var-0 : Fnn) → valtype
valtype-Fnn Fnn-F32 = F32
valtype-Fnn Fnn-F64 = F64
valtype-Fnn var-0 = default-val

{- Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:116.1-117.11 -}
resulttype : Set
resulttype = (Maybe valtype)

{- Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:119.1-119.18 -}
mut : Set
mut = (Maybe r-MUT)

{- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:121.1-122.17 -}
data limits : Set where
  mk-limits : (v-u32 : u32) → (u32-opt : (Maybe u32)) → limits

instance
  inh-limits : Inhabited limits
  inh-limits = record { default-val = (mk-limits (default-val) (nothing)) }

{- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:123.1-124.14 -}
data globaltype : Set where
  mk-globaltype : (v-mut : mut) → (v-valtype : valtype) → globaltype

instance
  inh-globaltype : Inhabited globaltype
  inh-globaltype = record { default-val = (mk-globaltype (default-val) (default-val)) }

{- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:125.1-126.23 -}
data functype : Set where
  mk-functype : (valtype-lst : (List valtype)) → (valtype-lst : (List valtype)) → functype

instance
  inh-functype : Inhabited functype
  inh-functype = record { default-val = (mk-functype ([]) ([])) }

{- Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:127.1-128.9 -}
tabletype : Set
tabletype = limits

{- Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:129.1-130.9 -}
memtype : Set
memtype = limits

{- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:131.1-132.70 -}
data externtype : Set where
  FUNC : (v-functype : functype) → externtype
  GLOBAL : (v-globaltype : globaltype) → externtype
  TABLE : (v-tabletype : tabletype) → externtype
  MEM : (v-memtype : memtype) → externtype

{- Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:144.1-144.41 -}
{-# TERMINATING #-}
size : (v-valtype : valtype) → ℕ
size I32 = 32
size I64 = 64
size F32 = 32
size F64 = 64
size v-valtype = default-val

{- Type Family Definition at: ../specification/wasm-1.0/1-syntax.spectec:146.1-146.21 -}
val- : (v-valtype : valtype) → Set
val- I32 = (uN-fam0 (32))
val- I64 = (uN-fam0 (64))
val- F32 = (fN-fam0 (32))
val- F64 = (fN-fam0 (64))
val- _ = ⊤

inh-val--fun : (v-valtype : valtype) → Inhabited (val- v-valtype)
inh-val--fun I32 = record { default-val = (Inhabited.default-val (inh-iN-fun (size (valtype-Inn Inn-I32)))) }
inh-val--fun I64 = record { default-val = (Inhabited.default-val (inh-iN-fun (size (valtype-Inn Inn-I64)))) }
inh-val--fun F32 = record { default-val = (Inhabited.default-val (inh-fN-fun (size (valtype-Fnn Fnn-F32)))) }
inh-val--fun F64 = record { default-val = (Inhabited.default-val (inh-fN-fun (size (valtype-Fnn Fnn-F64)))) }

{- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:153.1-153.42 -}
data sx : Set where
  U : sx
  S : sx

{- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:154.1-154.56 -}
data sz : Set where
  mk-sz : (i : ℕ) → sz {- 1 premise(s) dropped -}

{- Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:154.1-154.56 -}
{-# TERMINATING #-}
proj-sz-0 : (x : sz) → (ℕ)
proj-sz-0 (mk-sz v-num-0) = (v-num-0)
proj-sz-0 x = (default-val)

instance
  proj-sz-0-coercion : Coerce sz (ℕ)
  proj-sz-0-coercion = record { coerce = proj-sz-0 }

{- Type Family Definition at: ../specification/wasm-1.0/1-syntax.spectec:156.1-156.22 -}
data unop--fam0 : Set where
  CLZ : unop--fam0
  CTZ : unop--fam0
  POPCNT : unop--fam0

data unop--fam1 : Set where
  CLZ : unop--fam1
  CTZ : unop--fam1
  POPCNT : unop--fam1

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

unop- : (v-valtype : valtype) → Set
unop- I32 = unop--fam0
unop- I64 = unop--fam1
unop- F32 = unop--fam2
unop- F64 = unop--fam3
unop- _ = ⊤

{- Type Family Definition at: ../specification/wasm-1.0/1-syntax.spectec:160.1-160.23 -}
data binop--fam0 : Set where
  ADD : binop--fam0
  SUB : binop--fam0
  MUL : binop--fam0
  DIV : (sx-1761 : sx) → binop--fam0
  REM : (sx-1762 : sx) → binop--fam0
  AND : binop--fam0
  OR : binop--fam0
  XOR : binop--fam0
  SHL : binop--fam0
  SHR : (sx-1763 : sx) → binop--fam0
  ROTL : binop--fam0
  ROTR : binop--fam0

data binop--fam1 : Set where
  ADD : binop--fam1
  SUB : binop--fam1
  MUL : binop--fam1
  DIV : (sx-1764 : sx) → binop--fam1
  REM : (sx-1765 : sx) → binop--fam1
  AND : binop--fam1
  OR : binop--fam1
  XOR : binop--fam1
  SHL : binop--fam1
  SHR : (sx-1766 : sx) → binop--fam1
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

binop- : (v-valtype : valtype) → Set
binop- I32 = binop--fam0
binop- I64 = binop--fam1
binop- F32 = binop--fam2
binop- F64 = binop--fam3
binop- _ = ⊤

{- Type Family Definition at: ../specification/wasm-1.0/1-syntax.spectec:167.1-167.24 -}
data testop--fam0 : Set where
  EQZ : testop--fam0

data testop--fam1 : Set where
  EQZ : testop--fam1

testop- : (v-valtype : valtype) → Set
testop- I32 = testop--fam0
testop- I64 = testop--fam1
testop- _ = ⊤

{- Type Family Definition at: ../specification/wasm-1.0/1-syntax.spectec:171.1-171.23 -}
data relop--fam0 : Set where
  EQ : relop--fam0
  NE : relop--fam0
  LT : (sx-1767 : sx) → relop--fam0
  GT : (sx-1768 : sx) → relop--fam0
  LE : (sx-1769 : sx) → relop--fam0
  GE : (sx-1770 : sx) → relop--fam0

data relop--fam1 : Set where
  EQ : relop--fam1
  NE : relop--fam1
  LT : (sx-1771 : sx) → relop--fam1
  GT : (sx-1772 : sx) → relop--fam1
  LE : (sx-1773 : sx) → relop--fam1
  GE : (sx-1774 : sx) → relop--fam1

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

relop- : (v-valtype : valtype) → Set
relop- I32 = relop--fam0
relop- I64 = relop--fam1
relop- F32 = relop--fam2
relop- F64 = relop--fam3
relop- _ = ⊤

{- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:179.1-180.78 -}
data cvtop : Set where
  EXTEND : (v-sx : sx) → cvtop
  WRAP : cvtop
  CONVERT : (v-sx : sx) → cvtop
  cvtop-TRUNC : (v-sx : sx) → cvtop
  PROMOTE : cvtop
  DEMOTE : cvtop
  REINTERPRET : cvtop

{- Record Creation Definition at: ../specification/wasm-1.0/1-syntax.spectec:185.1-185.69 -}
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

{- Type Family Definition at: ../specification/wasm-1.0/1-syntax.spectec:189.1-189.24 -}
data loadop--fam0 : Set where
  mk-loadop- : (sz-91 : sz) → (sx-1775 : sx) → loadop--fam0 {- 1 premise(s) dropped -}

data loadop--fam1 : Set where
  mk-loadop- : (sz-92 : sz) → (sx-1776 : sx) → loadop--fam1 {- 1 premise(s) dropped -}

loadop- : (v-valtype : valtype) → Set
loadop- I32 = loadop--fam0
loadop- I64 = loadop--fam1
loadop- _ = ⊤

{- Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:195.1-195.52 -}
blocktype : Set
blocktype = (Maybe valtype)

{- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:245.1-250.16 -}
data instr : Set where
  NOP : instr
  UNREACHABLE : instr
  DROP : instr
  SELECT : instr
  BLOCK : (v-blocktype : blocktype) → (instr-lst : (List instr)) → instr
  LOOP : (v-blocktype : blocktype) → (instr-lst : (List instr)) → instr
  IFELSE : (v-blocktype : blocktype) → (instr-lst : (List instr)) → (instr-lst : (List instr)) → instr
  BR : (v-labelidx : labelidx) → instr
  BR-IF : (v-labelidx : labelidx) → instr
  BR-TABLE : (labelidx-lst : (List labelidx)) → (v-labelidx : labelidx) → instr
  CALL : (v-funcidx : funcidx) → instr
  CALL-INDIRECT : (v-typeidx : typeidx) → instr
  RETURN : instr
  CONST : (v-valtype : valtype) → (_ : (val- v-valtype)) → instr
  UNOP : (v-valtype : valtype) → (_ : (unop- v-valtype)) → instr
  BINOP : (v-valtype : valtype) → (_ : (binop- v-valtype)) → instr
  TESTOP : (v-valtype : valtype) → (_ : (testop- v-valtype)) → instr
  RELOP : (v-valtype : valtype) → (_ : (relop- v-valtype)) → instr
  CVTOP : (valtype-1 : valtype) → (valtype-2 : valtype) → (v-cvtop : cvtop) → instr {- 1 premise(s) dropped -}
  LOCAL-GET : (v-localidx : localidx) → instr
  LOCAL-SET : (v-localidx : localidx) → instr
  LOCAL-TEE : (v-localidx : localidx) → instr
  GLOBAL-GET : (v-globalidx : globalidx) → instr
  GLOBAL-SET : (v-globalidx : globalidx) → instr
  LOAD : (v-valtype : valtype) → (_ : (Maybe (loadop- v-valtype))) → (v-memarg : memarg) → instr
  STORE : (v-valtype : valtype) → (sz-opt : (Maybe sz)) → (v-memarg : memarg) → instr {- 1 premise(s) dropped -}
  MEMORY-SIZE : instr
  MEMORY-GROW : instr

instance
  inh-instr : Inhabited instr
  inh-instr = record { default-val = NOP }

{- Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:252.1-253.9 -}
expr : Set
expr = (List instr)

{- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:263.1-264.16 -}
data type : Set where
  TYPE : (v-functype : functype) → type

{- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:265.1-266.16 -}
data local : Set where
  LOCAL : (v-valtype : valtype) → local

instance
  inh-local : Inhabited local
  inh-local = record { default-val = (LOCAL (default-val)) }

{- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:267.1-268.27 -}
data func : Set where
  func-FUNC : (v-typeidx : typeidx) → (local-lst : (List local)) → (v-expr : expr) → func

instance
  inh-func : Inhabited func
  inh-func = record { default-val = (func-FUNC (default-val) ([]) (default-val)) }

{- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:269.1-270.25 -}
data global : Set where
  global-GLOBAL : (v-globaltype : globaltype) → (v-expr : expr) → global

{- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:271.1-272.18 -}
data table : Set where
  table-TABLE : (v-tabletype : tabletype) → table

{- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:273.1-274.17 -}
data mem : Set where
  MEMORY : (v-memtype : memtype) → mem

{- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:275.1-276.21 -}
data elem : Set where
  ELEM : (v-expr : expr) → (funcidx-lst : (List funcidx)) → elem

{- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:277.1-278.18 -}
data data' : Set where
  DATA : (v-expr : expr) → (byte-lst : (List byte)) → data'

{- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:279.1-280.16 -}
data start : Set where
  START : (v-funcidx : funcidx) → start

{- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:282.1-283.66 -}
data externidx : Set where
  externidx-FUNC : (v-funcidx : funcidx) → externidx
  externidx-GLOBAL : (v-globalidx : globalidx) → externidx
  externidx-TABLE : (v-tableidx : tableidx) → externidx
  externidx-MEM : (v-memidx : memidx) → externidx

{- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:284.1-285.24 -}
data export : Set where
  EXPORT : (v-name : name) → (v-externidx : externidx) → export

{- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:286.1-287.30 -}
data import' : Set where
  IMPORT : (v-name : name) → (v-name : name) → (v-externtype : externtype) → import'

{- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:289.1-290.76 -}
data module' : Set where
  MODULE : (type-lst : (List type)) → (import-lst : (List import')) → (func-lst : (List func)) → (global-lst : (List global)) → (table-lst : (List table)) → (mem-lst : (List mem)) → (elem-lst : (List elem)) → (data-lst : (List data')) → (start-opt : (Maybe start)) → (export-lst : (List export)) → module'

{- Auxiliary Definition at: ../specification/wasm-1.0/2-syntax-aux.spectec:20.1-20.64 -}
{-# TERMINATING #-}
funcsxt : (var-0-lst : (List externtype)) → (List functype)
funcsxt [] = []
funcsxt ((FUNC ft) ∷ xt-lst) = ((ft ∷ []) ++ (funcsxt xt-lst))
funcsxt (v-externtype ∷ xt-lst) = (funcsxt xt-lst)
funcsxt var-0-lst = []

{- Auxiliary Definition at: ../specification/wasm-1.0/2-syntax-aux.spectec:21.1-21.66 -}
{-# TERMINATING #-}
globalsxt : (var-0-lst : (List externtype)) → (List globaltype)
globalsxt [] = []
globalsxt ((GLOBAL gt) ∷ xt-lst) = ((gt ∷ []) ++ (globalsxt xt-lst))
globalsxt (v-externtype ∷ xt-lst) = (globalsxt xt-lst)
globalsxt var-0-lst = []

{- Auxiliary Definition at: ../specification/wasm-1.0/2-syntax-aux.spectec:22.1-22.65 -}
{-# TERMINATING #-}
tablesxt : (var-0-lst : (List externtype)) → (List tabletype)
tablesxt [] = []
tablesxt ((TABLE tt') ∷ xt-lst) = ((tt' ∷ []) ++ (tablesxt xt-lst))
tablesxt (v-externtype ∷ xt-lst) = (tablesxt xt-lst)
tablesxt var-0-lst = []

{- Auxiliary Definition at: ../specification/wasm-1.0/2-syntax-aux.spectec:23.1-23.63 -}
{-# TERMINATING #-}
memsxt : (var-0-lst : (List externtype)) → (List memtype)
memsxt [] = []
memsxt ((MEM mt) ∷ xt-lst) = ((mt ∷ []) ++ (memsxt xt-lst))
memsxt (v-externtype ∷ xt-lst) = (memsxt xt-lst)
memsxt var-0-lst = []

{- Auxiliary Definition at: ../specification/wasm-1.0/2-syntax-aux.spectec:49.1-49.35 -}
memarg0 : memarg
memarg0 = record { ALIGN = (mk-uN 0) ; OFFSET = (mk-uN 0) }

{- Auxiliary Definition at: ../specification/wasm-1.0/3-numerics.spectec:7.1-7.22 -}
{-# TERMINATING #-}
bool : (v-bool : Bool) → ℕ
bool false = 0
bool true = 1
bool v-bool = default-val

{- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:11.1-11.23 -}
postulate truncz : ∀ (rat : ℕ) → ℕ

{- Auxiliary Definition at: ../specification/wasm-1.0/3-numerics.spectec:18.1-18.54 -}
postulate signed- : ∀ (v-N : N) (nat : ℕ) → ℕ

{- Auxiliary Definition at: ../specification/wasm-1.0/3-numerics.spectec:22.1-22.68 -}
postulate inv-signed- : ∀ (v-N : N) (int : ℕ) → ℕ

{- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:152.1-152.30 -}
postulate fabs- : ∀ (v-N : N) (v-fN : (fN-fam0 (v-N))) → (List (fN-fam0 (v-N)))

{- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:155.1-155.31 -}
postulate fceil- : ∀ (v-N : N) (v-fN : (fN-fam0 (v-N))) → (List (fN-fam0 (v-N)))

{- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:156.1-156.32 -}
postulate ffloor- : ∀ (v-N : N) (v-fN : (fN-fam0 (v-N))) → (List (fN-fam0 (v-N)))

{- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:158.1-158.34 -}
postulate fnearest- : ∀ (v-N : N) (v-fN : (fN-fam0 (v-N))) → (List (fN-fam0 (v-N)))

{- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:153.1-153.30 -}
postulate fneg- : ∀ (v-N : N) (v-fN : (fN-fam0 (v-N))) → (List (fN-fam0 (v-N)))

{- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:154.1-154.31 -}
postulate fsqrt- : ∀ (v-N : N) (v-fN : (fN-fam0 (v-N))) → (List (fN-fam0 (v-N)))

{- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:157.1-157.32 -}
postulate ftrunc- : ∀ (v-N : N) (v-fN : (fN-fam0 (v-N))) → (List (fN-fam0 (v-N)))

{- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:86.1-86.29 -}
postulate iclz- : ∀ (v-N : N) (v-iN : (uN-fam0 (v-N))) → (uN-fam0 (v-N))

{- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:87.1-87.29 -}
postulate ictz- : ∀ (v-N : N) (v-iN : (uN-fam0 (v-N))) → (uN-fam0 (v-N))

{- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:88.1-88.32 -}
postulate ipopcnt- : ∀ (v-N : N) (v-iN : (uN-fam0 (v-N))) → (uN-fam0 (v-N))

{- Auxiliary Definition at: ../specification/wasm-1.0/3-numerics.spectec:28.1-29.32 -}
{-# TERMINATING #-}
fun-unop- : (v-valtype : valtype) (v-unop- : (unop- v-valtype)) (v-val- : (val- v-valtype)) → (List (val- v-valtype))
fun-unop- I32 CLZ v-iN = ((iclz- (size (valtype-Inn Inn-I32)) v-iN) ∷ [])
fun-unop- I64 CLZ v-iN = ((iclz- (size (valtype-Inn Inn-I64)) v-iN) ∷ [])
fun-unop- I32 CTZ v-iN = ((ictz- (size (valtype-Inn Inn-I32)) v-iN) ∷ [])
fun-unop- I64 CTZ v-iN = ((ictz- (size (valtype-Inn Inn-I64)) v-iN) ∷ [])
fun-unop- I32 POPCNT v-iN = ((ipopcnt- (size (valtype-Inn Inn-I32)) v-iN) ∷ [])
fun-unop- I64 POPCNT v-iN = ((ipopcnt- (size (valtype-Inn Inn-I64)) v-iN) ∷ [])
fun-unop- F32 ABS v-fN = (fabs- (size (valtype-Fnn Fnn-F32)) v-fN)
fun-unop- F64 ABS v-fN = (fabs- (size (valtype-Fnn Fnn-F64)) v-fN)
fun-unop- F32 unop--NEG v-fN = (fneg- (size (valtype-Fnn Fnn-F32)) v-fN)
fun-unop- F64 unop--NEG v-fN = (fneg- (size (valtype-Fnn Fnn-F64)) v-fN)
fun-unop- F32 SQRT v-fN = (fsqrt- (size (valtype-Fnn Fnn-F32)) v-fN)
fun-unop- F64 SQRT v-fN = (fsqrt- (size (valtype-Fnn Fnn-F64)) v-fN)
fun-unop- F32 CEIL v-fN = (fceil- (size (valtype-Fnn Fnn-F32)) v-fN)
fun-unop- F64 CEIL v-fN = (fceil- (size (valtype-Fnn Fnn-F64)) v-fN)
fun-unop- F32 FLOOR v-fN = (ffloor- (size (valtype-Fnn Fnn-F32)) v-fN)
fun-unop- F64 FLOOR v-fN = (ffloor- (size (valtype-Fnn Fnn-F64)) v-fN)
fun-unop- F32 TRUNC v-fN = (ftrunc- (size (valtype-Fnn Fnn-F32)) v-fN)
fun-unop- F64 TRUNC v-fN = (ftrunc- (size (valtype-Fnn Fnn-F64)) v-fN)
fun-unop- F32 NEAREST v-fN = (fnearest- (size (valtype-Fnn Fnn-F32)) v-fN)
fun-unop- F64 NEAREST v-fN = (fnearest- (size (valtype-Fnn Fnn-F64)) v-fN)
fun-unop- v-valtype v-unop- v-val- = []

{- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:145.1-145.37 -}
postulate fadd- : ∀ (v-N : N) (v-fN : (fN-fam0 (v-N))) (fN-0 : (fN-fam0 (v-N))) → (List (fN-fam0 (v-N)))

{- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:151.1-151.42 -}
postulate fcopysign- : ∀ (v-N : N) (v-fN : (fN-fam0 (v-N))) (fN-0 : (fN-fam0 (v-N))) → (List (fN-fam0 (v-N)))

{- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:148.1-148.37 -}
postulate fdiv- : ∀ (v-N : N) (v-fN : (fN-fam0 (v-N))) (fN-0 : (fN-fam0 (v-N))) → (List (fN-fam0 (v-N)))

{- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:150.1-150.37 -}
postulate fmax- : ∀ (v-N : N) (v-fN : (fN-fam0 (v-N))) (fN-0 : (fN-fam0 (v-N))) → (List (fN-fam0 (v-N)))

{- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:149.1-149.37 -}
postulate fmin- : ∀ (v-N : N) (v-fN : (fN-fam0 (v-N))) (fN-0 : (fN-fam0 (v-N))) → (List (fN-fam0 (v-N)))

{- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:147.1-147.37 -}
postulate fmul- : ∀ (v-N : N) (v-fN : (fN-fam0 (v-N))) (fN-0 : (fN-fam0 (v-N))) → (List (fN-fam0 (v-N)))

{- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:146.1-146.37 -}
postulate fsub- : ∀ (v-N : N) (v-fN : (fN-fam0 (v-N))) (fN-0 : (fN-fam0 (v-N))) → (List (fN-fam0 (v-N)))

{- Auxiliary Definition at: ../specification/wasm-1.0/3-numerics.spectec:73.1-73.36 -}
{-# TERMINATING #-}
iadd- : (v-N : N) (v-iN : (uN-fam0 (v-N))) (iN-0 : (uN-fam0 (v-N))) → (uN-fam0 (v-N))
iadd- v-N i-1 i-2 = (mk-uN (((proj-uN-0 v-N i-1) + (proj-uN-0 v-N i-2)) % (2 ^ v-N)))

{- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:79.1-79.36 -}
postulate iand- : ∀ (v-N : N) (v-iN : (uN-fam0 (v-N))) (iN-0 : (uN-fam0 (v-N))) → (uN-fam0 (v-N))

{- Auxiliary Definition at: ../specification/wasm-1.0/3-numerics.spectec:76.1-76.74 -}
postulate idiv- : ∀ (v-N : N) (v-sx : sx) (v-iN : (uN-fam0 (v-N))) (iN-0 : (uN-fam0 (v-N))) → (Maybe (uN-fam0 (v-N)))

{- Auxiliary Definition at: ../specification/wasm-1.0/3-numerics.spectec:75.1-75.36 -}
{-# TERMINATING #-}
imul- : (v-N : N) (v-iN : (uN-fam0 (v-N))) (iN-0 : (uN-fam0 (v-N))) → (uN-fam0 (v-N))
imul- v-N i-1 i-2 = (mk-uN (((proj-uN-0 v-N i-1) * (proj-uN-0 v-N i-2)) % (2 ^ v-N)))

{- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:80.1-80.35 -}
postulate ior- : ∀ (v-N : N) (v-iN : (uN-fam0 (v-N))) (iN-0 : (uN-fam0 (v-N))) → (uN-fam0 (v-N))

{- Auxiliary Definition at: ../specification/wasm-1.0/3-numerics.spectec:77.1-77.74 -}
postulate irem- : ∀ (v-N : N) (v-sx : sx) (v-iN : (uN-fam0 (v-N))) (iN-0 : (uN-fam0 (v-N))) → (Maybe (uN-fam0 (v-N)))

{- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:84.1-84.37 -}
postulate irotl- : ∀ (v-N : N) (v-iN : (uN-fam0 (v-N))) (iN-0 : (uN-fam0 (v-N))) → (uN-fam0 (v-N))

{- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:85.1-85.37 -}
postulate irotr- : ∀ (v-N : N) (v-iN : (uN-fam0 (v-N))) (iN-0 : (uN-fam0 (v-N))) → (uN-fam0 (v-N))

{- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:82.1-82.34 -}
postulate ishl- : ∀ (v-N : N) (v-iN : (uN-fam0 (v-N))) (v-u32 : u32) → (uN-fam0 (v-N))

{- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:83.1-83.74 -}
postulate ishr- : ∀ (v-N : N) (v-sx : sx) (v-iN : (uN-fam0 (v-N))) (v-u32 : u32) → (uN-fam0 (v-N))

{- Auxiliary Definition at: ../specification/wasm-1.0/3-numerics.spectec:74.1-74.36 -}
{-# TERMINATING #-}
isub- : (v-N : N) (v-iN : (uN-fam0 (v-N))) (iN-0 : (uN-fam0 (v-N))) → (uN-fam0 (v-N))
isub- v-N i-1 i-2 = (mk-uN (coerce {B = ℕ} (((coerce {B = ℕ} ((2 ^ v-N) + (proj-uN-0 v-N i-1))) – (coerce {B = ℕ} (proj-uN-0 v-N i-2))) % (coerce {B = ℕ} (2 ^ v-N)))))

{- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:81.1-81.36 -}
postulate ixor- : ∀ (v-N : N) (v-iN : (uN-fam0 (v-N))) (iN-0 : (uN-fam0 (v-N))) → (uN-fam0 (v-N))

{- Auxiliary Definition at: ../specification/wasm-1.0/3-numerics.spectec:30.1-31.34 -}
{-# TERMINATING #-}
fun-binop- : (v-valtype : valtype) (v-binop- : (binop- v-valtype)) (v-val- : (val- v-valtype)) (val--0 : (val- v-valtype)) → (List (val- v-valtype))
fun-binop- I32 ADD iN-1 iN-2 = ((iadd- (size (valtype-Inn Inn-I32)) iN-1 iN-2) ∷ [])
fun-binop- I64 ADD iN-1 iN-2 = ((iadd- (size (valtype-Inn Inn-I64)) iN-1 iN-2) ∷ [])
fun-binop- I32 SUB iN-1 iN-2 = ((isub- (size (valtype-Inn Inn-I32)) iN-1 iN-2) ∷ [])
fun-binop- I64 SUB iN-1 iN-2 = ((isub- (size (valtype-Inn Inn-I64)) iN-1 iN-2) ∷ [])
fun-binop- I32 MUL iN-1 iN-2 = ((imul- (size (valtype-Inn Inn-I32)) iN-1 iN-2) ∷ [])
fun-binop- I64 MUL iN-1 iN-2 = ((imul- (size (valtype-Inn Inn-I64)) iN-1 iN-2) ∷ [])
fun-binop- I32 (DIV v-sx) iN-1 iN-2 = (list- (uN-fam0 (32)) (idiv- (size (valtype-Inn Inn-I32)) v-sx iN-1 iN-2))
fun-binop- I64 (DIV v-sx) iN-1 iN-2 = (list- (uN-fam0 (64)) (idiv- (size (valtype-Inn Inn-I64)) v-sx iN-1 iN-2))
fun-binop- I32 (REM v-sx) iN-1 iN-2 = (list- (uN-fam0 (32)) (irem- (size (valtype-Inn Inn-I32)) v-sx iN-1 iN-2))
fun-binop- I64 (REM v-sx) iN-1 iN-2 = (list- (uN-fam0 (64)) (irem- (size (valtype-Inn Inn-I64)) v-sx iN-1 iN-2))
fun-binop- I32 AND iN-1 iN-2 = ((iand- (size (valtype-Inn Inn-I32)) iN-1 iN-2) ∷ [])
fun-binop- I64 AND iN-1 iN-2 = ((iand- (size (valtype-Inn Inn-I64)) iN-1 iN-2) ∷ [])
fun-binop- I32 OR iN-1 iN-2 = ((ior- (size (valtype-Inn Inn-I32)) iN-1 iN-2) ∷ [])
fun-binop- I64 OR iN-1 iN-2 = ((ior- (size (valtype-Inn Inn-I64)) iN-1 iN-2) ∷ [])
fun-binop- I32 XOR iN-1 iN-2 = ((ixor- (size (valtype-Inn Inn-I32)) iN-1 iN-2) ∷ [])
fun-binop- I64 XOR iN-1 iN-2 = ((ixor- (size (valtype-Inn Inn-I64)) iN-1 iN-2) ∷ [])
fun-binop- I32 SHL iN-1 iN-2 = ((ishl- (size (valtype-Inn Inn-I32)) iN-1 (mk-uN (proj-uN-0 (size (valtype-Inn Inn-I32)) iN-2))) ∷ [])
fun-binop- I64 SHL iN-1 iN-2 = ((ishl- (size (valtype-Inn Inn-I64)) iN-1 (mk-uN (proj-uN-0 (size (valtype-Inn Inn-I64)) iN-2))) ∷ [])
fun-binop- I32 (SHR v-sx) iN-1 iN-2 = ((ishr- (size (valtype-Inn Inn-I32)) v-sx iN-1 (mk-uN (proj-uN-0 (size (valtype-Inn Inn-I32)) iN-2))) ∷ [])
fun-binop- I64 (SHR v-sx) iN-1 iN-2 = ((ishr- (size (valtype-Inn Inn-I64)) v-sx iN-1 (mk-uN (proj-uN-0 (size (valtype-Inn Inn-I64)) iN-2))) ∷ [])
fun-binop- I32 ROTL iN-1 iN-2 = ((irotl- (size (valtype-Inn Inn-I32)) iN-1 iN-2) ∷ [])
fun-binop- I64 ROTL iN-1 iN-2 = ((irotl- (size (valtype-Inn Inn-I64)) iN-1 iN-2) ∷ [])
fun-binop- I32 ROTR iN-1 iN-2 = ((irotr- (size (valtype-Inn Inn-I32)) iN-1 iN-2) ∷ [])
fun-binop- I64 ROTR iN-1 iN-2 = ((irotr- (size (valtype-Inn Inn-I64)) iN-1 iN-2) ∷ [])
fun-binop- F32 ADD fN-1 fN-2 = (fadd- (size (valtype-Fnn Fnn-F32)) fN-1 fN-2)
fun-binop- F64 ADD fN-1 fN-2 = (fadd- (size (valtype-Fnn Fnn-F64)) fN-1 fN-2)
fun-binop- F32 SUB fN-1 fN-2 = (fsub- (size (valtype-Fnn Fnn-F32)) fN-1 fN-2)
fun-binop- F64 SUB fN-1 fN-2 = (fsub- (size (valtype-Fnn Fnn-F64)) fN-1 fN-2)
fun-binop- F32 MUL fN-1 fN-2 = (fmul- (size (valtype-Fnn Fnn-F32)) fN-1 fN-2)
fun-binop- F64 MUL fN-1 fN-2 = (fmul- (size (valtype-Fnn Fnn-F64)) fN-1 fN-2)
fun-binop- F32 DIV fN-1 fN-2 = (fdiv- (size (valtype-Fnn Fnn-F32)) fN-1 fN-2)
fun-binop- F64 DIV fN-1 fN-2 = (fdiv- (size (valtype-Fnn Fnn-F64)) fN-1 fN-2)
fun-binop- F32 MIN fN-1 fN-2 = (fmin- (size (valtype-Fnn Fnn-F32)) fN-1 fN-2)
fun-binop- F64 MIN fN-1 fN-2 = (fmin- (size (valtype-Fnn Fnn-F64)) fN-1 fN-2)
fun-binop- F32 MAX fN-1 fN-2 = (fmax- (size (valtype-Fnn Fnn-F32)) fN-1 fN-2)
fun-binop- F64 MAX fN-1 fN-2 = (fmax- (size (valtype-Fnn Fnn-F64)) fN-1 fN-2)
fun-binop- F32 COPYSIGN fN-1 fN-2 = (fcopysign- (size (valtype-Fnn Fnn-F32)) fN-1 fN-2)
fun-binop- F64 COPYSIGN fN-1 fN-2 = (fcopysign- (size (valtype-Fnn Fnn-F64)) fN-1 fN-2)
fun-binop- v-valtype v-binop- v-val- val--0 = []

{- Auxiliary Definition at: ../specification/wasm-1.0/3-numerics.spectec:89.1-89.27 -}
{-# TERMINATING #-}
ieqz- : (v-N : N) (v-iN : (uN-fam0 (v-N))) → u32
ieqz- v-N i-1 = (mk-uN (bool ((proj-uN-0 v-N i-1) =? 0)))

{- Auxiliary Definition at: ../specification/wasm-1.0/3-numerics.spectec:32.1-33.32 -}
{-# TERMINATING #-}
fun-testop- : (v-valtype : valtype) (v-testop- : (testop- v-valtype)) (v-val- : (val- v-valtype)) → (uN-fam0 (32))
fun-testop- I32 EQZ v-iN = (ieqz- (size (valtype-Inn Inn-I32)) v-iN)
fun-testop- I64 EQZ v-iN = (ieqz- (size (valtype-Inn Inn-I64)) v-iN)
fun-testop- v-valtype v-testop- v-val- = (Inhabited.default-val (inh-val--fun I32))

{- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:159.1-159.33 -}
postulate feq- : ∀ (v-N : N) (v-fN : (fN-fam0 (v-N))) (fN-0 : (fN-fam0 (v-N))) → u32

{- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:164.1-164.33 -}
postulate fge- : ∀ (v-N : N) (v-fN : (fN-fam0 (v-N))) (fN-0 : (fN-fam0 (v-N))) → u32

{- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:162.1-162.33 -}
postulate fgt- : ∀ (v-N : N) (v-fN : (fN-fam0 (v-N))) (fN-0 : (fN-fam0 (v-N))) → u32

{- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:163.1-163.33 -}
postulate fle- : ∀ (v-N : N) (v-fN : (fN-fam0 (v-N))) (fN-0 : (fN-fam0 (v-N))) → u32

{- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:161.1-161.33 -}
postulate flt- : ∀ (v-N : N) (v-fN : (fN-fam0 (v-N))) (fN-0 : (fN-fam0 (v-N))) → u32

{- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:160.1-160.33 -}
postulate fne- : ∀ (v-N : N) (v-fN : (fN-fam0 (v-N))) (fN-0 : (fN-fam0 (v-N))) → u32

{- Auxiliary Definition at: ../specification/wasm-1.0/3-numerics.spectec:91.1-91.33 -}
{-# TERMINATING #-}
ieq- : (v-N : N) (v-iN : (uN-fam0 (v-N))) (iN-0 : (uN-fam0 (v-N))) → u32
ieq- v-N i-1 i-2 = (mk-uN (bool (i-1 =? i-2)))

{- Auxiliary Definition at: ../specification/wasm-1.0/3-numerics.spectec:96.1-96.73 -}
{-# TERMINATING #-}
ige- : (v-N : N) (v-sx : sx) (v-iN : (uN-fam0 (v-N))) (iN-0 : (uN-fam0 (v-N))) → u32
ige- v-N U i-1 i-2 = (mk-uN (bool ((proj-uN-0 v-N i-1) ≥? (proj-uN-0 v-N i-2))))
ige- v-N S i-1 i-2 = (mk-uN (bool ((signed- v-N (proj-uN-0 v-N i-1)) ≥? (signed- v-N (proj-uN-0 v-N i-2)))))
ige- v-N v-sx v-iN iN-0 = default-val

{- Auxiliary Definition at: ../specification/wasm-1.0/3-numerics.spectec:94.1-94.73 -}
{-# TERMINATING #-}
igt- : (v-N : N) (v-sx : sx) (v-iN : (uN-fam0 (v-N))) (iN-0 : (uN-fam0 (v-N))) → u32
igt- v-N U i-1 i-2 = (mk-uN (bool ((proj-uN-0 v-N i-1) >? (proj-uN-0 v-N i-2))))
igt- v-N S i-1 i-2 = (mk-uN (bool ((signed- v-N (proj-uN-0 v-N i-1)) >? (signed- v-N (proj-uN-0 v-N i-2)))))
igt- v-N v-sx v-iN iN-0 = default-val

{- Auxiliary Definition at: ../specification/wasm-1.0/3-numerics.spectec:95.1-95.73 -}
{-# TERMINATING #-}
ile- : (v-N : N) (v-sx : sx) (v-iN : (uN-fam0 (v-N))) (iN-0 : (uN-fam0 (v-N))) → u32
ile- v-N U i-1 i-2 = (mk-uN (bool ((proj-uN-0 v-N i-1) ≤? (proj-uN-0 v-N i-2))))
ile- v-N S i-1 i-2 = (mk-uN (bool ((signed- v-N (proj-uN-0 v-N i-1)) ≤? (signed- v-N (proj-uN-0 v-N i-2)))))
ile- v-N v-sx v-iN iN-0 = default-val

{- Auxiliary Definition at: ../specification/wasm-1.0/3-numerics.spectec:93.1-93.73 -}
{-# TERMINATING #-}
ilt- : (v-N : N) (v-sx : sx) (v-iN : (uN-fam0 (v-N))) (iN-0 : (uN-fam0 (v-N))) → u32
ilt- v-N U i-1 i-2 = (mk-uN (bool ((proj-uN-0 v-N i-1) <? (proj-uN-0 v-N i-2))))
ilt- v-N S i-1 i-2 = (mk-uN (bool ((signed- v-N (proj-uN-0 v-N i-1)) <? (signed- v-N (proj-uN-0 v-N i-2)))))
ilt- v-N v-sx v-iN iN-0 = default-val

{- Auxiliary Definition at: ../specification/wasm-1.0/3-numerics.spectec:92.1-92.33 -}
{-# TERMINATING #-}
ine- : (v-N : N) (v-iN : (uN-fam0 (v-N))) (iN-0 : (uN-fam0 (v-N))) → u32
ine- v-N i-1 i-2 = (mk-uN (bool (i-1 ≠? i-2)))

{- Auxiliary Definition at: ../specification/wasm-1.0/3-numerics.spectec:34.1-35.34 -}
{-# TERMINATING #-}
fun-relop- : (v-valtype : valtype) (v-relop- : (relop- v-valtype)) (v-val- : (val- v-valtype)) (val--0 : (val- v-valtype)) → (uN-fam0 (32))
fun-relop- I32 EQ iN-1 iN-2 = (ieq- (size (valtype-Inn Inn-I32)) iN-1 iN-2)
fun-relop- I64 EQ iN-1 iN-2 = (ieq- (size (valtype-Inn Inn-I64)) iN-1 iN-2)
fun-relop- I32 NE iN-1 iN-2 = (ine- (size (valtype-Inn Inn-I32)) iN-1 iN-2)
fun-relop- I64 NE iN-1 iN-2 = (ine- (size (valtype-Inn Inn-I64)) iN-1 iN-2)
fun-relop- I32 (LT v-sx) iN-1 iN-2 = (ilt- (size (valtype-Inn Inn-I32)) v-sx iN-1 iN-2)
fun-relop- I64 (LT v-sx) iN-1 iN-2 = (ilt- (size (valtype-Inn Inn-I64)) v-sx iN-1 iN-2)
fun-relop- I32 (GT v-sx) iN-1 iN-2 = (igt- (size (valtype-Inn Inn-I32)) v-sx iN-1 iN-2)
fun-relop- I64 (GT v-sx) iN-1 iN-2 = (igt- (size (valtype-Inn Inn-I64)) v-sx iN-1 iN-2)
fun-relop- I32 (LE v-sx) iN-1 iN-2 = (ile- (size (valtype-Inn Inn-I32)) v-sx iN-1 iN-2)
fun-relop- I64 (LE v-sx) iN-1 iN-2 = (ile- (size (valtype-Inn Inn-I64)) v-sx iN-1 iN-2)
fun-relop- I32 (GE v-sx) iN-1 iN-2 = (ige- (size (valtype-Inn Inn-I32)) v-sx iN-1 iN-2)
fun-relop- I64 (GE v-sx) iN-1 iN-2 = (ige- (size (valtype-Inn Inn-I64)) v-sx iN-1 iN-2)
fun-relop- F32 EQ fN-1 fN-2 = (feq- (size (valtype-Fnn Fnn-F32)) fN-1 fN-2)
fun-relop- F64 EQ fN-1 fN-2 = (feq- (size (valtype-Fnn Fnn-F64)) fN-1 fN-2)
fun-relop- F32 NE fN-1 fN-2 = (fne- (size (valtype-Fnn Fnn-F32)) fN-1 fN-2)
fun-relop- F64 NE fN-1 fN-2 = (fne- (size (valtype-Fnn Fnn-F64)) fN-1 fN-2)
fun-relop- F32 LT fN-1 fN-2 = (flt- (size (valtype-Fnn Fnn-F32)) fN-1 fN-2)
fun-relop- F64 LT fN-1 fN-2 = (flt- (size (valtype-Fnn Fnn-F64)) fN-1 fN-2)
fun-relop- F32 GT fN-1 fN-2 = (fgt- (size (valtype-Fnn Fnn-F32)) fN-1 fN-2)
fun-relop- F64 GT fN-1 fN-2 = (fgt- (size (valtype-Fnn Fnn-F64)) fN-1 fN-2)
fun-relop- F32 LE fN-1 fN-2 = (fle- (size (valtype-Fnn Fnn-F32)) fN-1 fN-2)
fun-relop- F64 LE fN-1 fN-2 = (fle- (size (valtype-Fnn Fnn-F64)) fN-1 fN-2)
fun-relop- F32 GE fN-1 fN-2 = (fge- (size (valtype-Fnn Fnn-F32)) fN-1 fN-2)
fun-relop- F64 GE fN-1 fN-2 = (fge- (size (valtype-Fnn Fnn-F64)) fN-1 fN-2)
fun-relop- v-valtype v-relop- v-val- val--0 = (Inhabited.default-val (inh-val--fun I32))

{- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:44.1-44.90 -}
postulate convert-- : ∀ (v-M : M) (v-N : N) (v-sx : sx) (v-iN : (uN-fam0 (v-M))) → (fN-fam0 (v-N))

{- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:42.1-42.36 -}
postulate demote-- : ∀ (v-M : M) (v-N : N) (v-fN : (fN-fam0 (v-M))) → (List (fN-fam0 (v-N)))

{- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:40.1-40.89 -}
postulate extend-- : ∀ (v-M : M) (v-N : N) (v-sx : sx) (v-iN : (uN-fam0 (v-M))) → (uN-fam0 (v-N))

{- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:43.1-43.37 -}
postulate promote-- : ∀ (v-M : M) (v-N : N) (v-fN : (fN-fam0 (v-M))) → (List (fN-fam0 (v-N)))

{- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:45.1-45.76 -}
postulate reinterpret-- : ∀ (valtype-1 : valtype) (valtype-2 : valtype) (v-val- : (val- valtype-1)) → (val- valtype-2)

{- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:41.1-41.88 -}
postulate trunc-- : ∀ (v-M : M) (v-N : N) (v-sx : sx) (v-fN : (fN-fam0 (v-M))) → (Maybe (uN-fam0 (v-N)))

{- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:39.1-39.33 -}
postulate wrap-- : ∀ (v-M : M) (v-N : N) (v-iN : (uN-fam0 (v-M))) → (uN-fam0 (v-N))

{- Auxiliary Definition at: ../specification/wasm-1.0/3-numerics.spectec:36.1-37.36 -}
postulate cvtop-- : ∀ (valtype-1 : valtype) (valtype-2 : valtype) (v-cvtop : cvtop) (v-val- : (val- valtype-1)) → (List (val- valtype-2))

{- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:56.1-56.102 -}
postulate ibytes- : ∀ (v-N : N) (v-iN : (uN-fam0 (v-N))) → (List byte)

{- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:57.1-57.102 -}
postulate fbytes- : ∀ (v-N : N) (v-fN : (fN-fam0 (v-N))) → (List byte)

{- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:58.1-58.75 -}
postulate bytes- : ∀ (v-valtype : valtype) (v-val- : (val- v-valtype)) → (List byte)

{- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:60.1-60.75 -}
postulate inv-ibytes- : ∀ (v-N : N) (var-0-lst : (List byte)) → (uN-fam0 (v-N))

{- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:61.1-61.75 -}
postulate inv-fbytes- : ∀ (v-N : N) (var-0-lst : (List byte)) → (fN-fam0 (v-N))

{- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:62.1-62.73 -}
postulate inv-bytes- : ∀ (v-valtype : valtype) (var-0-lst : (List byte)) → (val- v-valtype)

{- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:78.1-78.29 -}
postulate inot- : ∀ (v-N : N) (v-iN : (uN-fam0 (v-N))) → (uN-fam0 (v-N))

{- Auxiliary Definition at: ../specification/wasm-1.0/3-numerics.spectec:90.1-90.27 -}
{-# TERMINATING #-}
inez- : (v-N : N) (v-iN : (uN-fam0 (v-N))) → u32
inez- v-N i-1 = (mk-uN (bool ((proj-uN-0 v-N i-1) ≠? 0)))

{- Type Alias Definition at: ../specification/wasm-1.0/4-runtime.spectec:5.1-5.39 -}
addr : Set
addr = ℕ

{- Type Alias Definition at: ../specification/wasm-1.0/4-runtime.spectec:6.1-6.53 -}
funcaddr : Set
funcaddr = addr

{- Type Alias Definition at: ../specification/wasm-1.0/4-runtime.spectec:7.1-7.53 -}
globaladdr : Set
globaladdr = addr

{- Type Alias Definition at: ../specification/wasm-1.0/4-runtime.spectec:8.1-8.51 -}
tableaddr : Set
tableaddr = addr

{- Type Alias Definition at: ../specification/wasm-1.0/4-runtime.spectec:9.1-9.50 -}
memaddr : Set
memaddr = addr

{- Inductive Type Definition at: ../specification/wasm-1.0/4-runtime.spectec:20.1-21.70 -}
data externaddr : Set where
  externaddr-FUNC : (v-funcaddr : funcaddr) → externaddr
  externaddr-GLOBAL : (v-globaladdr : globaladdr) → externaddr
  externaddr-TABLE : (v-tableaddr : tableaddr) → externaddr
  externaddr-MEM : (v-memaddr : memaddr) → externaddr

instance
  inh-externaddr : Inhabited externaddr
  inh-externaddr = record { default-val = (externaddr-FUNC (default-val)) }

{- Inductive Type Definition at: ../specification/wasm-1.0/4-runtime.spectec:32.1-33.55 -}
data val : Set where
  val-CONST : (v-valtype : valtype) → (_ : (val- v-valtype)) → val

instance
  inh-val : Inhabited val
  inh-val = record { default-val = (let v-valtype = default-val in val-CONST v-valtype ((Inhabited.default-val (inh-val--fun v-valtype)))) }

{- Inductive Type Definition at: ../specification/wasm-1.0/4-runtime.spectec:35.1-36.22 -}
data result : Set where
  -VALS : (val-lst : (List val)) → result
  TRAP : result

{- Record Creation Definition at: ../specification/wasm-1.0/4-runtime.spectec:61.1-63.22 -}
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

{- Record Creation Definition at: ../specification/wasm-1.0/4-runtime.spectec:65.1-71.26 -}
record moduleinst : Set where
  constructor mk-moduleinst
  field
    TYPES : (List functype)
    FUNCS : (List funcaddr)
    GLOBALS : (List globaladdr)
    TABLES : (List tableaddr)
    MEMS : (List memaddr)
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
    EXPORTS = EXPORTS arg1 ⧺ EXPORTS arg2 } }

instance
  inh-moduleinst : Inhabited moduleinst
  inh-moduleinst = record { default-val = record { TYPES = default-val ; FUNCS = default-val ; GLOBALS = default-val ; TABLES = default-val ; MEMS = default-val ; EXPORTS = default-val } }

{- Record Creation Definition at: ../specification/wasm-1.0/4-runtime.spectec:48.1-51.16 -}
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

{- Record Creation Definition at: ../specification/wasm-1.0/4-runtime.spectec:52.1-54.16 -}
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

{- Record Creation Definition at: ../specification/wasm-1.0/4-runtime.spectec:55.1-57.24 -}
record tableinst : Set where
  constructor mk-tableinst
  field
    tableinst-TYPE : tabletype
    REFS : (List (Maybe funcaddr))
open tableinst

instance
  append-tableinst : HasAppend (tableinst)
  append-tableinst = record { append = λ arg1 arg2 → record {
    tableinst-TYPE = tableinst-TYPE arg1 {- FIXME - Non-trivial append -} ;
    REFS = REFS arg1 ⧺ REFS arg2 } }

instance
  inh-tableinst : Inhabited tableinst
  inh-tableinst = record { default-val = record { tableinst-TYPE = default-val ; REFS = default-val } }

{- Record Creation Definition at: ../specification/wasm-1.0/4-runtime.spectec:58.1-60.18 -}
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

{- Record Creation Definition at: ../specification/wasm-1.0/4-runtime.spectec:83.1-87.20 -}
record store : Set where
  constructor mk-store
  field
    store-FUNCS : (List funcinst)
    store-GLOBALS : (List globalinst)
    store-TABLES : (List tableinst)
    store-MEMS : (List meminst)
open store

instance
  append-store : HasAppend (store)
  append-store = record { append = λ arg1 arg2 → record {
    store-FUNCS = store-FUNCS arg1 ⧺ store-FUNCS arg2 ;
    store-GLOBALS = store-GLOBALS arg1 ⧺ store-GLOBALS arg2 ;
    store-TABLES = store-TABLES arg1 ⧺ store-TABLES arg2 ;
    store-MEMS = store-MEMS arg1 ⧺ store-MEMS arg2 } }

instance
  inh-store : Inhabited store
  inh-store = record { default-val = record { store-FUNCS = default-val ; store-GLOBALS = default-val ; store-TABLES = default-val ; store-MEMS = default-val } }

{- Record Creation Definition at: ../specification/wasm-1.0/4-runtime.spectec:89.1-91.24 -}
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

{- Inductive Type Definition at: ../specification/wasm-1.0/4-runtime.spectec:93.1-93.47 -}
data state : Set where
  mk-state : (v-store : store) → (v-frame : frame) → state

instance
  inh-state : Inhabited state
  inh-state = record { default-val = (mk-state (default-val) (default-val)) }

{- Inductive Type Definition at: ../specification/wasm-1.0/4-runtime.spectec:105.1-110.9 -}
data admininstr : Set where
  admininstr-NOP : admininstr
  admininstr-UNREACHABLE : admininstr
  admininstr-DROP : admininstr
  admininstr-SELECT : admininstr
  admininstr-BLOCK : (v-blocktype : blocktype) → (instr-lst : (List instr)) → admininstr
  admininstr-LOOP : (v-blocktype : blocktype) → (instr-lst : (List instr)) → admininstr
  admininstr-IFELSE : (v-blocktype : blocktype) → (instr-lst : (List instr)) → (instr-lst : (List instr)) → admininstr
  admininstr-BR : (v-labelidx : labelidx) → admininstr
  admininstr-BR-IF : (v-labelidx : labelidx) → admininstr
  admininstr-BR-TABLE : (labelidx-lst : (List labelidx)) → (v-labelidx : labelidx) → admininstr
  admininstr-CALL : (v-funcidx : funcidx) → admininstr
  admininstr-CALL-INDIRECT : (v-typeidx : typeidx) → admininstr
  admininstr-RETURN : admininstr
  admininstr-CONST : (v-valtype : valtype) → (_ : (val- v-valtype)) → admininstr
  admininstr-UNOP : (v-valtype : valtype) → (_ : (unop- v-valtype)) → admininstr
  admininstr-BINOP : (v-valtype : valtype) → (_ : (binop- v-valtype)) → admininstr
  admininstr-TESTOP : (v-valtype : valtype) → (_ : (testop- v-valtype)) → admininstr
  admininstr-RELOP : (v-valtype : valtype) → (_ : (relop- v-valtype)) → admininstr
  admininstr-CVTOP : (valtype-1 : valtype) → (valtype-2 : valtype) → (v-cvtop : cvtop) → admininstr {- 1 premise(s) dropped -}
  admininstr-LOCAL-GET : (v-localidx : localidx) → admininstr
  admininstr-LOCAL-SET : (v-localidx : localidx) → admininstr
  admininstr-LOCAL-TEE : (v-localidx : localidx) → admininstr
  admininstr-GLOBAL-GET : (v-globalidx : globalidx) → admininstr
  admininstr-GLOBAL-SET : (v-globalidx : globalidx) → admininstr
  admininstr-LOAD : (v-valtype : valtype) → (_ : (Maybe (loadop- v-valtype))) → (v-memarg : memarg) → admininstr
  admininstr-STORE : (v-valtype : valtype) → (sz-opt : (Maybe sz)) → (v-memarg : memarg) → admininstr {- 1 premise(s) dropped -}
  admininstr-MEMORY-SIZE : admininstr
  admininstr-MEMORY-GROW : admininstr
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
admininstr-instr SELECT = admininstr-SELECT
admininstr-instr (BLOCK x0 x1) = (admininstr-BLOCK x0 x1)
admininstr-instr (LOOP x0 x1) = (admininstr-LOOP x0 x1)
admininstr-instr (IFELSE x0 x1 x2) = (admininstr-IFELSE x0 x1 x2)
admininstr-instr (BR x0) = (admininstr-BR x0)
admininstr-instr (BR-IF x0) = (admininstr-BR-IF x0)
admininstr-instr (BR-TABLE x0 x1) = (admininstr-BR-TABLE x0 x1)
admininstr-instr (CALL x0) = (admininstr-CALL x0)
admininstr-instr (CALL-INDIRECT x0) = (admininstr-CALL-INDIRECT x0)
admininstr-instr RETURN = admininstr-RETURN
admininstr-instr (CONST x0 x1) = (admininstr-CONST x0 x1)
admininstr-instr (UNOP x0 x1) = (admininstr-UNOP x0 x1)
admininstr-instr (BINOP x0 x1) = (admininstr-BINOP x0 x1)
admininstr-instr (TESTOP x0 x1) = (admininstr-TESTOP x0 x1)
admininstr-instr (RELOP x0 x1) = (admininstr-RELOP x0 x1)
admininstr-instr (CVTOP x0 x1 x2) = (admininstr-CVTOP x0 x1 x2)
admininstr-instr (LOCAL-GET x0) = (admininstr-LOCAL-GET x0)
admininstr-instr (LOCAL-SET x0) = (admininstr-LOCAL-SET x0)
admininstr-instr (LOCAL-TEE x0) = (admininstr-LOCAL-TEE x0)
admininstr-instr (GLOBAL-GET x0) = (admininstr-GLOBAL-GET x0)
admininstr-instr (GLOBAL-SET x0) = (admininstr-GLOBAL-SET x0)
admininstr-instr (LOAD x0 x1 x2) = (admininstr-LOAD x0 x1 x2)
admininstr-instr (STORE x0 x1 x2) = (admininstr-STORE x0 x1 x2)
admininstr-instr MEMORY-SIZE = admininstr-MEMORY-SIZE
admininstr-instr MEMORY-GROW = admininstr-MEMORY-GROW
admininstr-instr var-0 = default-val

{- Auxiliary Definition at:  -}
{-# TERMINATING #-}
admininstr-val : (var-0 : val) → admininstr
admininstr-val (val-CONST x0 x1) = (admininstr-CONST x0 x1)
admininstr-val var-0 = default-val

{- Inductive Type Definition at: ../specification/wasm-1.0/4-runtime.spectec:94.1-94.62 -}
data config : Set where
  mk-config : (v-state : state) → (admininstr-lst : (List admininstr)) → config

{- Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:7.1-7.29 -}
{-# TERMINATING #-}
default- : (v-valtype : valtype) → val
default- I32 = (val-CONST I32 (mk-uN 0))
default- I64 = (val-CONST I64 (mk-uN 0))
default- F32 = (val-CONST F32 (fzero 32))
default- F64 = (val-CONST F64 (fzero 64))
default- v-valtype = default-val

{- Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:17.1-17.63 -}
{-# TERMINATING #-}
funcsxa : (var-0-lst : (List externaddr)) → (List funcaddr)
funcsxa [] = []
funcsxa ((externaddr-FUNC fa) ∷ xv-lst) = ((fa ∷ []) ++ (funcsxa xv-lst))
funcsxa (v-externaddr ∷ xv-lst) = (funcsxa xv-lst)
funcsxa var-0-lst = []

{- Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:18.1-18.65 -}
{-# TERMINATING #-}
globalsxa : (var-0-lst : (List externaddr)) → (List globaladdr)
globalsxa [] = []
globalsxa ((externaddr-GLOBAL ga) ∷ xv-lst) = ((ga ∷ []) ++ (globalsxa xv-lst))
globalsxa (v-externaddr ∷ xv-lst) = (globalsxa xv-lst)
globalsxa var-0-lst = []

{- Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:19.1-19.64 -}
{-# TERMINATING #-}
tablesxa : (var-0-lst : (List externaddr)) → (List tableaddr)
tablesxa [] = []
tablesxa ((externaddr-TABLE ta) ∷ xv-lst) = ((ta ∷ []) ++ (tablesxa xv-lst))
tablesxa (v-externaddr ∷ xv-lst) = (tablesxa xv-lst)
tablesxa var-0-lst = []

{- Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:20.1-20.62 -}
{-# TERMINATING #-}
memsxa : (var-0-lst : (List externaddr)) → (List memaddr)
memsxa [] = []
memsxa ((externaddr-MEM ma) ∷ xv-lst) = ((ma ∷ []) ++ (memsxa xv-lst))
memsxa (v-externaddr ∷ xv-lst) = (memsxa xv-lst)
memsxa var-0-lst = []

{- Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:46.1-46.57 -}
{-# TERMINATING #-}
fun-store : (v-state : state) → store
fun-store (mk-state s f) = s
fun-store v-state = default-val

{- Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:47.1-47.57 -}
{-# TERMINATING #-}
fun-frame : (v-state : state) → frame
fun-frame (mk-state s f) = f
fun-frame v-state = default-val

{- Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:53.1-53.64 -}
{-# TERMINATING #-}
fun-funcaddr : (v-state : state) → (List funcaddr)
fun-funcaddr (mk-state s f) = (FUNCS (frame-MODULE f))
fun-funcaddr v-state = []

{- Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:56.1-56.57 -}
{-# TERMINATING #-}
fun-funcinst : (v-state : state) → (List funcinst)
fun-funcinst (mk-state s f) = (store-FUNCS s)
fun-funcinst v-state = []

{- Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:57.1-57.59 -}
{-# TERMINATING #-}
fun-globalinst : (v-state : state) → (List globalinst)
fun-globalinst (mk-state s f) = (store-GLOBALS s)
fun-globalinst v-state = []

{- Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:58.1-58.58 -}
{-# TERMINATING #-}
fun-tableinst : (v-state : state) → (List tableinst)
fun-tableinst (mk-state s f) = (store-TABLES s)
fun-tableinst v-state = []

{- Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:59.1-59.56 -}
{-# TERMINATING #-}
fun-meminst : (v-state : state) → (List meminst)
fun-meminst (mk-state s f) = (store-MEMS s)
fun-meminst v-state = []

{- Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:60.1-60.58 -}
{-# TERMINATING #-}
fun-moduleinst : (v-state : state) → moduleinst
fun-moduleinst (mk-state s f) = (frame-MODULE f)
fun-moduleinst v-state = default-val

{- Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:68.1-68.66 -}
{-# TERMINATING #-}
fun-type : (v-state : state) (v-typeidx : typeidx) → functype
fun-type (mk-state s f) x = ((TYPES (frame-MODULE f)) [ (proj-uN-0 32 x) ]!)
fun-type v-state v-typeidx = default-val

{- Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:69.1-69.66 -}
{-# TERMINATING #-}
fun-func : (v-state : state) (v-funcidx : funcidx) → funcinst
fun-func (mk-state s f) x = ((store-FUNCS s) [ ((FUNCS (frame-MODULE f)) [ (proj-uN-0 32 x) ]!) ]!)
fun-func v-state v-funcidx = default-val

{- Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:70.1-70.68 -}
{-# TERMINATING #-}
fun-global : (v-state : state) (v-globalidx : globalidx) → globalinst
fun-global (mk-state s f) x = ((store-GLOBALS s) [ ((GLOBALS (frame-MODULE f)) [ (proj-uN-0 32 x) ]!) ]!)
fun-global v-state v-globalidx = default-val

{- Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:71.1-71.67 -}
{-# TERMINATING #-}
fun-table : (v-state : state) (v-tableidx : tableidx) → tableinst
fun-table (mk-state s f) x = ((store-TABLES s) [ ((TABLES (frame-MODULE f)) [ (proj-uN-0 32 x) ]!) ]!)
fun-table v-state v-tableidx = default-val

{- Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:72.1-72.65 -}
{-# TERMINATING #-}
fun-mem : (v-state : state) (v-memidx : memidx) → meminst
fun-mem (mk-state s f) x = ((store-MEMS s) [ ((MEMS (frame-MODULE f)) [ (proj-uN-0 32 x) ]!) ]!)
fun-mem v-state v-memidx = default-val

{- Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:73.1-73.67 -}
{-# TERMINATING #-}
fun-local : (v-state : state) (v-localidx : localidx) → val
fun-local (mk-state s f) x = ((LOCALS f) [ (proj-uN-0 32 x) ]!)
fun-local v-state v-localidx = default-val

{- Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:85.1-85.89 -}
{-# TERMINATING #-}
with-local : (v-state : state) (v-localidx : localidx) (v-val : val) → state
with-local (mk-state s f) x v = (mk-state s (record f { LOCALS = (modify (LOCALS f) (proj-uN-0 32 x) (λ (_ : val) → v)) }))
with-local v-state v-localidx v-val = default-val

{- Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:86.1-86.96 -}
{-# TERMINATING #-}
with-global : (v-state : state) (v-globalidx : globalidx) (v-val : val) → state
with-global (mk-state s f) x v = (mk-state (record s { store-GLOBALS = (modify (store-GLOBALS s) ((GLOBALS (frame-MODULE f)) [ (proj-uN-0 32 x) ]!) (λ (var-1 : globalinst) → (record var-1 { VALUE = v }))) }) f)
with-global v-state v-globalidx v-val = default-val

{- Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:87.1-87.97 -}
{-# TERMINATING #-}
with-table : (v-state : state) (v-tableidx : tableidx) (nat : ℕ) (v-funcaddr : funcaddr) → state
with-table (mk-state s f) x i a = (mk-state (record s { store-TABLES = (modify (store-TABLES s) ((TABLES (frame-MODULE f)) [ (proj-uN-0 32 x) ]!) (λ (var-1 : tableinst) → (record var-1 { REFS = (modify (REFS var-1) i (λ (_ : (Maybe funcaddr)) → (just a))) }))) }) f)
with-table v-state v-tableidx nat v-funcaddr = default-val

{- Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:88.1-88.89 -}
{-# TERMINATING #-}
with-tableinst : (v-state : state) (v-tableidx : tableidx) (v-tableinst : tableinst) → state
with-tableinst (mk-state s f) x ti = (mk-state (record s { store-TABLES = (modify (store-TABLES s) ((TABLES (frame-MODULE f)) [ (proj-uN-0 32 x) ]!) (λ (_ : tableinst) → ti)) }) f)
with-tableinst v-state v-tableidx v-tableinst = default-val

{- Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:89.1-89.100 -}
{-# TERMINATING #-}
with-mem : (v-state : state) (v-memidx : memidx) (nat : ℕ) (nat-0 : ℕ) (var-0-lst : (List byte)) → state
with-mem (mk-state s f) x i j b-lst = (mk-state (record s { store-MEMS = (modify (store-MEMS s) ((MEMS (frame-MODULE f)) [ (proj-uN-0 32 x) ]!) (λ (var-1 : meminst) → (record var-1 { BYTES = (slice-update (BYTES var-1) i j b-lst) }))) }) f)
with-mem v-state v-memidx nat nat-0 var-0-lst = default-val

{- Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:90.1-90.87 -}
{-# TERMINATING #-}
with-meminst : (v-state : state) (v-memidx : memidx) (v-meminst : meminst) → state
with-meminst (mk-state s f) x mi = (mk-state (record s { store-MEMS = (modify (store-MEMS s) ((MEMS (frame-MODULE f)) [ (proj-uN-0 32 x) ]!) (λ (_ : meminst) → mi)) }) f)
with-meminst v-state v-memidx v-meminst = default-val

{- Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:102.1-102.58 -}
postulate growtable : ∀ (v-tableinst : tableinst) (nat : ℕ) → (Maybe tableinst)

{- Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:103.1-103.58 -}
postulate growmemory : ∀ (v-meminst : meminst) (nat : ℕ) → (Maybe meminst)

{- Record Creation Definition at: ../specification/wasm-1.0/6-typing.spectec:5.1-8.62 -}
record context : Set where
  constructor mk-context
  field
    context-TYPES : (List functype)
    context-FUNCS : (List functype)
    context-GLOBALS : (List globaltype)
    context-TABLES : (List tabletype)
    context-MEMS : (List memtype)
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
    context-LOCALS = context-LOCALS arg1 ⧺ context-LOCALS arg2 ;
    LABELS = LABELS arg1 ⧺ LABELS arg2 ;
    context-RETURN = context-RETURN arg1 ⧺ context-RETURN arg2 } }

{- Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:18.1-18.66 -}
data Limits-ok : limits → ℕ → Set where
  mk-Limits-ok : ∀ (v-n : n) (m-opt : (Maybe m)) (k : ℕ) → 
    (v-n ≤ k) →
    Forall (λ (v-m : ℕ) → ((v-n ≤ v-m) × (v-m ≤ k))) (fromMaybe m-opt) →
    Limits-ok (mk-limits (mk-uN v-n) (mapMaybe (λ (v-m : ℕ) → (mk-uN v-m)) m-opt)) k

{- Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:19.1-19.64 -}
data Functype-ok : functype → Set where
  mk-Functype-ok : ∀ (t-1-lst : (List valtype)) (t-2-opt : (Maybe valtype)) → Functype-ok (mk-functype t-1-lst (fromMaybe t-2-opt))

{- Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:20.1-20.66 -}
data Globaltype-ok : globaltype → Set where
  mk-Globaltype-ok : ∀ (t : valtype) → Globaltype-ok (mk-globaltype (just MUT) t)

{- Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:21.1-21.65 -}
data Tabletype-ok : tabletype → Set where
  mk-Tabletype-ok : ∀ (v-limits : limits) → 
    (Limits-ok v-limits (coerce {B = ℕ} ((coerce {B = ℕ} (2 ^ 32)) – (coerce {B = ℕ} 1)))) →
    Tabletype-ok v-limits

{- Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:22.1-22.63 -}
data Memtype-ok : memtype → Set where
  mk-Memtype-ok : ∀ (v-limits : limits) → 
    (Limits-ok v-limits (2 ^ 16)) →
    Memtype-ok v-limits

{- Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:23.1-23.66 -}
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

{- Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:70.1-70.75 -}
data Limits-sub : limits → limits → Set where
  mk-Limits-sub : ∀ (n-11 : n) (n-12 : n) (n-21 : n) (n-22 : n) → 
    (n-11 ≥ n-21) →
    (n-12 ≤ n-22) →
    Limits-sub (mk-limits (mk-uN n-11) (just (mk-uN n-12))) (mk-limits (mk-uN n-21) (just (mk-uN n-22)))

{- Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:71.1-71.73 -}
data Functype-sub : functype → functype → Set where
  mk-Functype-sub : ∀ (ft : functype) → Functype-sub ft ft

{- Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:72.1-72.75 -}
data Globaltype-sub : globaltype → globaltype → Set where
  mk-Globaltype-sub : ∀ (gt : globaltype) → Globaltype-sub gt gt

{- Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:73.1-73.74 -}
data Tabletype-sub : tabletype → tabletype → Set where
  mk-Tabletype-sub : ∀ (lim-1 : limits) (lim-2 : limits) → 
    (Limits-sub lim-1 lim-2) →
    Tabletype-sub lim-1 lim-2

{- Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:74.1-74.72 -}
data Memtype-sub : memtype → memtype → Set where
  mk-Memtype-sub : ∀ (lim-1 : limits) (lim-2 : limits) → 
    (Limits-sub lim-1 lim-2) →
    Memtype-sub lim-1 lim-2

{- Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:75.1-75.75 -}
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

mutual
  {- Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:120.1-120.64 -}
  data Instr-ok : context → instr → functype → Set where
    nop : ∀ (C : context) → Instr-ok C NOP (mk-functype [] [])
    unreachable : ∀ (C : context) (t-1-lst : (List valtype)) (t-2-lst : (List valtype)) → Instr-ok C UNREACHABLE (mk-functype t-1-lst t-2-lst)
    drop' : ∀ (C : context) (t : valtype) → Instr-ok C DROP (mk-functype (t ∷ []) [])
    select : ∀ (C : context) (t : valtype) → Instr-ok C SELECT (mk-functype (as (List valtype) (t ∷ t ∷ I32 ∷ [])) (t ∷ []))
    block : ∀ (C : context) (t-opt : (Maybe valtype)) (instr-lst : (List instr)) → 
      (Instrs-ok (record { context-TYPES = [] ; context-FUNCS = [] ; context-GLOBALS = [] ; context-TABLES = [] ; context-MEMS = [] ; context-LOCALS = [] ; LABELS = (t-opt ∷ []) ; context-RETURN = nothing } ⧺ C) instr-lst (mk-functype [] (fromMaybe t-opt))) →
      Instr-ok C (BLOCK t-opt instr-lst) (mk-functype [] (fromMaybe t-opt))
    loop : ∀ (C : context) (t-opt : (Maybe valtype)) (instr-lst : (List instr)) → 
      (Instrs-ok (record { context-TYPES = [] ; context-FUNCS = [] ; context-GLOBALS = [] ; context-TABLES = [] ; context-MEMS = [] ; context-LOCALS = [] ; LABELS = (nothing ∷ []) ; context-RETURN = nothing } ⧺ C) instr-lst (mk-functype [] [])) →
      Instr-ok C (LOOP t-opt instr-lst) (mk-functype [] (fromMaybe t-opt))
    if' : ∀ (C : context) (t-opt : (Maybe valtype)) (instr-1-lst : (List instr)) (instr-2-lst : (List instr)) → 
      (Instrs-ok (record { context-TYPES = [] ; context-FUNCS = [] ; context-GLOBALS = [] ; context-TABLES = [] ; context-MEMS = [] ; context-LOCALS = [] ; LABELS = (t-opt ∷ []) ; context-RETURN = nothing } ⧺ C) instr-1-lst (mk-functype [] (fromMaybe t-opt))) →
      (Instrs-ok (record { context-TYPES = [] ; context-FUNCS = [] ; context-GLOBALS = [] ; context-TABLES = [] ; context-MEMS = [] ; context-LOCALS = [] ; LABELS = (t-opt ∷ []) ; context-RETURN = nothing } ⧺ C) instr-2-lst (mk-functype [] (fromMaybe t-opt))) →
      Instr-ok C (IFELSE t-opt instr-1-lst instr-2-lst) (mk-functype (as (List valtype) (I32 ∷ [])) (fromMaybe t-opt))
    br : ∀ (C : context) (l : labelidx) (t-1-lst : (List valtype)) (t-opt : (Maybe valtype)) (t-2-lst : (List valtype)) → 
      ((proj-uN-0 32 l) < (length (LABELS C))) →
      (((LABELS C) [ (proj-uN-0 32 l) ]!) ≡ t-opt) →
      Instr-ok C (BR l) (mk-functype (t-1-lst ++ (fromMaybe t-opt)) t-2-lst)
    br-if : ∀ (C : context) (l : labelidx) (t-opt : (Maybe valtype)) → 
      ((proj-uN-0 32 l) < (length (LABELS C))) →
      (((LABELS C) [ (proj-uN-0 32 l) ]!) ≡ t-opt) →
      Instr-ok C (BR-IF l) (mk-functype ((fromMaybe t-opt) ++ (as (List valtype) (I32 ∷ []))) (fromMaybe t-opt))
    br-table : ∀ (C : context) (l-lst : (List labelidx)) (l' : labelidx) (t-1-lst : (List valtype)) (t-opt : (Maybe valtype)) (t-2-lst : (List valtype)) → 
      ((proj-uN-0 32 l') < (length (LABELS C))) →
      (t-opt ≡ ((LABELS C) [ (proj-uN-0 32 l') ]!)) →
      Forall (λ (l : labelidx) → ((proj-uN-0 32 l) < (length (LABELS C)))) l-lst →
      Forall (λ (l : labelidx) → (t-opt ≡ ((LABELS C) [ (proj-uN-0 32 l) ]!))) l-lst →
      Instr-ok C (BR-TABLE l-lst l') (mk-functype (t-1-lst ++ ((fromMaybe t-opt) ++ (as (List valtype) (I32 ∷ [])))) t-2-lst)
    call : ∀ (C : context) (x : idx) (t-1-lst : (List valtype)) (t-2-opt : (Maybe valtype)) → 
      ((proj-uN-0 32 x) < (length (context-FUNCS C))) →
      (((context-FUNCS C) [ (proj-uN-0 32 x) ]!) ≡ (mk-functype t-1-lst (fromMaybe t-2-opt))) →
      Instr-ok C (CALL x) (mk-functype t-1-lst (fromMaybe t-2-opt))
    call-indirect : ∀ (C : context) (x : idx) (t-1-lst : (List valtype)) (t-2-opt : (Maybe valtype)) → 
      ((proj-uN-0 32 x) < (length (context-TYPES C))) →
      (((context-TYPES C) [ (proj-uN-0 32 x) ]!) ≡ (mk-functype t-1-lst (fromMaybe t-2-opt))) →
      Instr-ok C (CALL-INDIRECT x) (mk-functype (t-1-lst ++ (as (List valtype) (I32 ∷ []))) (fromMaybe t-2-opt))
    return : ∀ (C : context) (t-1-lst : (List valtype)) (t-opt : (Maybe valtype)) (t-2-lst : (List valtype)) → 
      ((context-RETURN C) ≡ (just t-opt)) →
      Instr-ok C RETURN (mk-functype (t-1-lst ++ (fromMaybe t-opt)) t-2-lst)
    const : ∀ (C : context) (t : valtype) (c-t : (val- t)) → Instr-ok C (CONST t c-t) (mk-functype [] (t ∷ []))
    unop : ∀ (C : context) (t : valtype) (unop-t : (unop- t)) → Instr-ok C (UNOP t unop-t) (mk-functype (t ∷ []) (t ∷ []))
    binop : ∀ (C : context) (t : valtype) (binop-t : (binop- t)) → Instr-ok C (BINOP t binop-t) (mk-functype (t ∷ t ∷ []) (t ∷ []))
    testop : ∀ (C : context) (t : valtype) (testop-t : (testop- t)) → Instr-ok C (TESTOP t testop-t) (mk-functype (t ∷ []) (as (List valtype) (I32 ∷ [])))
    relop : ∀ (C : context) (t : valtype) (relop-t : (relop- t)) → Instr-ok C (RELOP t relop-t) (mk-functype (t ∷ t ∷ []) (as (List valtype) (I32 ∷ [])))
    cvtop-reinterpret : ∀ (C : context) (nt-1 : valtype) (nt-2 : valtype) → 
      ((size nt-1) ≡ (size nt-2)) →
      Instr-ok C (CVTOP nt-1 nt-2 REINTERPRET) (mk-functype (nt-2 ∷ []) (nt-1 ∷ []))
    cvtop-convert : ∀ (C : context) (nt-1 : valtype) (nt-2 : valtype) (v-cvtop : cvtop) → Instr-ok C (CVTOP nt-1 nt-2 v-cvtop) (mk-functype (nt-2 ∷ []) (nt-1 ∷ []))
    local-get : ∀ (C : context) (x : idx) (t : valtype) → 
      ((proj-uN-0 32 x) < (length (context-LOCALS C))) →
      (((context-LOCALS C) [ (proj-uN-0 32 x) ]!) ≡ t) →
      Instr-ok C (LOCAL-GET x) (mk-functype [] (t ∷ []))
    local-set : ∀ (C : context) (x : idx) (t : valtype) → 
      ((proj-uN-0 32 x) < (length (context-LOCALS C))) →
      (((context-LOCALS C) [ (proj-uN-0 32 x) ]!) ≡ t) →
      Instr-ok C (LOCAL-SET x) (mk-functype (t ∷ []) [])
    local-tee : ∀ (C : context) (x : idx) (t : valtype) → 
      ((proj-uN-0 32 x) < (length (context-LOCALS C))) →
      (((context-LOCALS C) [ (proj-uN-0 32 x) ]!) ≡ t) →
      Instr-ok C (LOCAL-TEE x) (mk-functype (t ∷ []) (t ∷ []))
    global-get : ∀ (C : context) (x : idx) (t : valtype) (v-mut : mut) → 
      ((proj-uN-0 32 x) < (length (context-GLOBALS C))) →
      (((context-GLOBALS C) [ (proj-uN-0 32 x) ]!) ≡ (mk-globaltype v-mut t)) →
      Instr-ok C (GLOBAL-GET x) (mk-functype [] (t ∷ []))
    global-set : ∀ (C : context) (x : idx) (t : valtype) → 
      ((proj-uN-0 32 x) < (length (context-GLOBALS C))) →
      (((context-GLOBALS C) [ (proj-uN-0 32 x) ]!) ≡ (mk-globaltype (just MUT) t)) →
      Instr-ok C (GLOBAL-SET x) (mk-functype (t ∷ []) [])
    memory-size : ∀ (C : context) (mt : memtype) → 
      (0 < (length (context-MEMS C))) →
      (((context-MEMS C) [ 0 ]!) ≡ mt) →
      Instr-ok C MEMORY-SIZE (mk-functype [] (as (List valtype) (I32 ∷ [])))
    memory-grow : ∀ (C : context) (mt : memtype) → 
      (0 < (length (context-MEMS C))) →
      (((context-MEMS C) [ 0 ]!) ≡ mt) →
      Instr-ok C MEMORY-GROW (mk-functype (as (List valtype) (I32 ∷ [])) (as (List valtype) (I32 ∷ [])))
    load-val : ∀ (C : context) (t : valtype) (v-memarg : memarg) (mt : memtype) → 
      (0 < (length (context-MEMS C))) →
      (((context-MEMS C) [ 0 ]!) ≡ mt) →
      ((coerce {B = ℕ} (2 ^ (proj-uN-0 32 (ALIGN v-memarg)))) ≤ ((coerce {B = ℕ} (size t)) / (coerce {B = ℕ} 8))) →
      Instr-ok C (LOAD t nothing v-memarg) (mk-functype (as (List valtype) (I32 ∷ [])) (t ∷ []))
    load-pack-0 : ∀ (C : context) (v-M : M) (v-sx : sx) (v-memarg : memarg) (mt : memtype) → 
      (0 < (length (context-MEMS C))) →
      (((context-MEMS C) [ 0 ]!) ≡ mt) →
      ((coerce {B = ℕ} (2 ^ (proj-uN-0 32 (ALIGN v-memarg)))) ≤ ((coerce {B = ℕ} v-M) / (coerce {B = ℕ} 8))) →
      Instr-ok C (LOAD (valtype-Inn Inn-I32) (just (mk-loadop- (mk-sz v-M) v-sx)) v-memarg) (mk-functype (as (List valtype) (I32 ∷ [])) ((valtype-Inn Inn-I32) ∷ []))
    load-pack-1 : ∀ (C : context) (v-M : M) (v-sx : sx) (v-memarg : memarg) (mt : memtype) → 
      (0 < (length (context-MEMS C))) →
      (((context-MEMS C) [ 0 ]!) ≡ mt) →
      ((coerce {B = ℕ} (2 ^ (proj-uN-0 32 (ALIGN v-memarg)))) ≤ ((coerce {B = ℕ} v-M) / (coerce {B = ℕ} 8))) →
      Instr-ok C (LOAD (valtype-Inn Inn-I64) (just (mk-loadop- (mk-sz v-M) v-sx)) v-memarg) (mk-functype (as (List valtype) (I32 ∷ [])) ((valtype-Inn Inn-I64) ∷ []))
    store-val : ∀ (C : context) (t : valtype) (v-memarg : memarg) (mt : memtype) → 
      (0 < (length (context-MEMS C))) →
      (((context-MEMS C) [ 0 ]!) ≡ mt) →
      ((coerce {B = ℕ} (2 ^ (proj-uN-0 32 (ALIGN v-memarg)))) ≤ ((coerce {B = ℕ} (size t)) / (coerce {B = ℕ} 8))) →
      Instr-ok C (STORE t nothing v-memarg) (mk-functype (as (List valtype) (I32 ∷ t ∷ [])) [])
    store-pack : ∀ (C : context) (v-Inn : Inn) (v-M : M) (v-memarg : memarg) (mt : memtype) → 
      (0 < (length (context-MEMS C))) →
      (((context-MEMS C) [ 0 ]!) ≡ mt) →
      ((coerce {B = ℕ} (2 ^ (proj-uN-0 32 (ALIGN v-memarg)))) ≤ ((coerce {B = ℕ} v-M) / (coerce {B = ℕ} 8))) →
      Instr-ok C (STORE (valtype-Inn v-Inn) (just (mk-sz v-M)) v-memarg) (mk-functype (as (List valtype) (I32 ∷ (valtype-Inn v-Inn) ∷ [])) [])

  {- Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:121.1-121.65 -}
  data Instrs-ok : context → (List instr) → functype → Set where
    empty : ∀ (C : context) → Instrs-ok C [] (mk-functype [] [])
    Instrs-ok--instr : ∀ (C : context) (v-instr : instr) (t-1-lst : (List valtype)) (t-2-lst : (List valtype)) → 
      (Instr-ok C v-instr (mk-functype t-1-lst t-2-lst)) →
      Instrs-ok C (v-instr ∷ []) (mk-functype t-1-lst t-2-lst)
    seq : ∀ (C : context) (instr-1-lst : (List instr)) (instr-2-lst : (List instr)) (t-1-lst : (List valtype)) (t-3-lst : (List valtype)) (t-2-lst : (List valtype)) → 
      (Instrs-ok C instr-1-lst (mk-functype t-1-lst t-2-lst)) →
      (Instrs-ok C instr-2-lst (mk-functype t-2-lst t-3-lst)) →
      Instrs-ok C (instr-1-lst ++ instr-2-lst) (mk-functype t-1-lst t-3-lst)
    Instrs-ok--frame : ∀ (C : context) (instr-lst : (List instr)) (t-lst : (List valtype)) (t-1-lst : (List valtype)) (t-2-lst : (List valtype)) → 
      (Instrs-ok C instr-lst (mk-functype t-1-lst t-2-lst)) →
      Instrs-ok C instr-lst (mk-functype (t-lst ++ t-1-lst) (t-lst ++ t-2-lst))

{- Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:122.1-122.69 -}
data Expr-ok : context → expr → resulttype → Set where
  mk-Expr-ok : ∀ (C : context) (instr-lst : (List instr)) (t-opt : (Maybe valtype)) → 
    (Instrs-ok C instr-lst (mk-functype [] (fromMaybe t-opt))) →
    Expr-ok C instr-lst t-opt

{- Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:319.1-319.79 -}
data Instr-const : context → instr → Set where
  Instr-const--const : ∀ (C : context) (t : valtype) (c : (val- t)) → Instr-const C (CONST t c)
  Instr-const--global-get : ∀ (C : context) (x : idx) (t : valtype) → 
    ((proj-uN-0 32 x) < (length (context-GLOBALS C))) →
    (((context-GLOBALS C) [ (proj-uN-0 32 x) ]!) ≡ (mk-globaltype nothing t)) →
    Instr-const C (GLOBAL-GET x)

{- Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:320.1-320.78 -}
data Expr-const : context → expr → Set where
  mk-Expr-const : ∀ (C : context) (instr-lst : (List instr)) → 
    Forall (λ (v-instr : instr) → (Instr-const C v-instr)) instr-lst →
    Expr-const C instr-lst

{- Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:321.1-321.79 -}
data Expr-ok-const : context → expr → (Maybe valtype) → Set where
  mk-Expr-ok-const : ∀ (C : context) (v-expr : expr) (t-opt : (Maybe valtype)) → 
    (Expr-ok C v-expr t-opt) →
    (Expr-const C v-expr) →
    Expr-ok-const C v-expr t-opt

{- Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:345.1-345.73 -}
data Type-ok : type → functype → Set where
  mk-Type-ok : ∀ (ft : functype) → 
    (Functype-ok ft) →
    Type-ok (TYPE ft) ft

{- Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:346.1-346.73 -}
data Func-ok : context → func → functype → Set where
  mk-Func-ok : ∀ (C : context) (x : idx) (t-lst : (List valtype)) (v-expr : expr) (t-1-lst : (List valtype)) (t-2-opt : (Maybe valtype)) → 
    ((proj-uN-0 32 x) < (length (context-TYPES C))) →
    (((context-TYPES C) [ (proj-uN-0 32 x) ]!) ≡ (mk-functype t-1-lst (fromMaybe t-2-opt))) →
    (Expr-ok (C ⧺ record { context-TYPES = [] ; context-FUNCS = [] ; context-GLOBALS = [] ; context-TABLES = [] ; context-MEMS = [] ; context-LOCALS = (t-1-lst ++ t-lst) ; LABELS = (t-2-opt ∷ []) ; context-RETURN = (just t-2-opt) }) v-expr t-2-opt) →
    Func-ok C (func-FUNC x (map (λ (t : valtype) → (LOCAL t)) t-lst) v-expr) (mk-functype t-1-lst (fromMaybe t-2-opt))

{- Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:347.1-347.75 -}
data Global-ok : context → global → globaltype → Set where
  mk-Global-ok : ∀ (C : context) (gt : globaltype) (v-expr : expr) (v-mut : mut) (t : valtype) → 
    (Globaltype-ok gt) →
    (gt ≡ (mk-globaltype v-mut t)) →
    (Expr-ok-const C v-expr (just t)) →
    Global-ok C (global-GLOBAL gt v-expr) gt

{- Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:348.1-348.74 -}
data Table-ok : context → table → tabletype → Set where
  mk-Table-ok : ∀ (C : context) (tt' : tabletype) → 
    (Tabletype-ok tt') →
    Table-ok C (table-TABLE tt') tt'

{- Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:349.1-349.72 -}
data Mem-ok : context → mem → memtype → Set where
  mk-Mem-ok : ∀ (C : context) (mt : memtype) → 
    (Memtype-ok mt) →
    Mem-ok C (MEMORY mt) mt

{- Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:350.1-350.73 -}
data Elem-ok : context → elem → Set where
  mk-Elem-ok : ∀ (C : context) (v-expr : expr) (x-lst : (List idx)) (lim : limits) (ft-lst : (List functype)) → 
    (0 < (length (context-TABLES C))) →
    (((context-TABLES C) [ 0 ]!) ≡ lim) →
    (Expr-ok-const C v-expr (just I32)) →
    ((length ft-lst) ≡ (length x-lst)) →
    Forall (λ (x : idx) → ((proj-uN-0 32 x) < (length (context-FUNCS C)))) x-lst →
    Forall₂ (λ (ft : functype) (x : idx) → (((context-FUNCS C) [ (proj-uN-0 32 x) ]!) ≡ ft)) ft-lst x-lst →
    Elem-ok C (ELEM v-expr x-lst)

{- Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:351.1-351.73 -}
data Data-ok : context → data' → Set where
  mk-Data-ok : ∀ (C : context) (v-expr : expr) (b-lst : (List byte)) (lim : limits) → 
    (0 < (length (context-MEMS C))) →
    (((context-MEMS C) [ 0 ]!) ≡ lim) →
    (Expr-ok-const C v-expr (just I32)) →
    Data-ok C (DATA v-expr b-lst)

{- Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:352.1-352.74 -}
data Start-ok : context → start → Set where
  mk-Start-ok : ∀ (C : context) (x : idx) → 
    ((proj-uN-0 32 x) < (length (context-FUNCS C))) →
    (((context-FUNCS C) [ (proj-uN-0 32 x) ]!) ≡ (mk-functype [] [])) →
    Start-ok C (START x)

{- Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:400.1-400.80 -}
data Import-ok : context → import' → externtype → Set where
  mk-Import-ok : ∀ (C : context) (name-1 : name) (name-2 : name) (xt : externtype) → 
    (Externtype-ok xt) →
    Import-ok C (IMPORT name-1 name-2 xt) xt

{- Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:402.1-402.83 -}
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

{- Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:401.1-401.80 -}
data Export-ok : context → export → externtype → Set where
  mk-Export-ok : ∀ (C : context) (v-name : name) (v-externidx : externidx) (xt : externtype) → 
    (Externidx-ok C v-externidx xt) →
    Export-ok C (EXPORT v-name v-externidx) xt

{- Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:432.1-432.62 -}
data Module-ok : module' → Set where
  mk-Module-ok : ∀ (type-lst : (List type)) (import-lst : (List import')) (func-lst : (List func)) (global-lst : (List global)) (table-lst : (List table)) (mem-lst : (List mem)) (elem-lst : (List elem)) (data-lst : (List data')) (start-opt : (Maybe start)) (export-lst : (List export)) (ft'-lst : (List functype)) (ixt-lst : (List externtype)) (C' : context) (gt-lst : (List globaltype)) (C : context) (ft-lst : (List functype)) (tt-lst : (List tabletype)) (mt-lst : (List memtype)) (xt-lst : (List externtype)) (ift-lst : (List functype)) (igt-lst : (List globaltype)) (itt-lst : (List tabletype)) (imt-lst : (List memtype)) → 
    ((length ft'-lst) ≡ (length type-lst)) →
    Forall₂ (λ (ft' : functype) (v-type : type) → (Type-ok v-type ft')) ft'-lst type-lst →
    ((length import-lst) ≡ (length ixt-lst)) →
    Forall₂ (λ (v-import : import') (ixt : externtype) → (Import-ok record { context-TYPES = ft'-lst ; context-FUNCS = [] ; context-GLOBALS = [] ; context-TABLES = [] ; context-MEMS = [] ; context-LOCALS = [] ; LABELS = [] ; context-RETURN = nothing } v-import ixt)) import-lst ixt-lst →
    ((length global-lst) ≡ (length gt-lst)) →
    Forall₂ (λ (v-global : global) (gt : globaltype) → (Global-ok C' v-global gt)) global-lst gt-lst →
    ((length ft-lst) ≡ (length func-lst)) →
    Forall₂ (λ (ft : functype) (v-func : func) → (Func-ok C v-func ft)) ft-lst func-lst →
    ((length table-lst) ≡ (length tt-lst)) →
    Forall₂ (λ (v-table : table) (tt' : tabletype) → (Table-ok C v-table tt')) table-lst tt-lst →
    ((length mem-lst) ≡ (length mt-lst)) →
    Forall₂ (λ (v-mem : mem) (mt : memtype) → (Mem-ok C v-mem mt)) mem-lst mt-lst →
    Forall (λ (v-elem : elem) → (Elem-ok C v-elem)) elem-lst →
    Forall (λ (v-data : data') → (Data-ok C v-data)) data-lst →
    Forall (λ (v-start : start) → (Start-ok C v-start)) (fromMaybe start-opt) →
    ((length export-lst) ≡ (length xt-lst)) →
    Forall₂ (λ (v-export : export) (xt : externtype) → (Export-ok C v-export xt)) export-lst xt-lst →
    ((length tt-lst) ≤ 1) →
    ((length mt-lst) ≤ 1) →
    (C ≡ record { context-TYPES = ft'-lst ; context-FUNCS = (ift-lst ++ ft-lst) ; context-GLOBALS = (igt-lst ++ gt-lst) ; context-TABLES = (itt-lst ++ tt-lst) ; context-MEMS = (imt-lst ++ mt-lst) ; context-LOCALS = [] ; LABELS = [] ; context-RETURN = nothing }) →
    (C' ≡ record { context-TYPES = ft'-lst ; context-FUNCS = (ift-lst ++ ft-lst) ; context-GLOBALS = igt-lst ; context-TABLES = [] ; context-MEMS = [] ; context-LOCALS = [] ; LABELS = [] ; context-RETURN = nothing }) →
    (ift-lst ≡ (funcsxt ixt-lst)) →
    (igt-lst ≡ (globalsxt ixt-lst)) →
    (itt-lst ≡ (tablesxt ixt-lst)) →
    (imt-lst ≡ (memsxt ixt-lst)) →
    Module-ok (MODULE type-lst import-lst func-lst global-lst table-lst mem-lst elem-lst data-lst start-opt export-lst)

{- Inductive Relations Definition at: ../specification/wasm-1.0/8-reduction.spectec:6.1-6.77 -}
data Step-pure : (List admininstr) → (List admininstr) → Set where
  Step-pure--unreachable : Step-pure (as (List admininstr) (admininstr-UNREACHABLE ∷ [])) (as (List admininstr) (admininstr-TRAP ∷ []))
  Step-pure--nop : Step-pure (as (List admininstr) (admininstr-NOP ∷ [])) []
  Step-pure--drop : ∀ (v-val : val) → Step-pure (as (List admininstr) ((admininstr-val v-val) ∷ admininstr-DROP ∷ [])) []
  select-true : ∀ (val-1 : val) (val-2 : val) (c : (uN-fam0 (32))) → 
    ((proj-uN-0 32 c) ≢ 0) →
    Step-pure (as (List admininstr) ((admininstr-val val-1) ∷ (admininstr-val val-2) ∷ (admininstr-CONST I32 c) ∷ admininstr-SELECT ∷ [])) ((admininstr-val val-1) ∷ [])
  select-false : ∀ (val-1 : val) (val-2 : val) (c : (uN-fam0 (32))) → 
    ((proj-uN-0 32 c) ≡ 0) →
    Step-pure (as (List admininstr) ((admininstr-val val-1) ∷ (admininstr-val val-2) ∷ (admininstr-CONST I32 c) ∷ admininstr-SELECT ∷ [])) ((admininstr-val val-2) ∷ [])
  if-true : ∀ (c : (uN-fam0 (32))) (t-opt : (Maybe valtype)) (instr-1-lst : (List instr)) (instr-2-lst : (List instr)) → 
    ((proj-uN-0 32 c) ≢ 0) →
    Step-pure (as (List admininstr) ((admininstr-CONST I32 c) ∷ (admininstr-IFELSE t-opt instr-1-lst instr-2-lst) ∷ [])) (as (List admininstr) ((admininstr-BLOCK t-opt instr-1-lst) ∷ []))
  if-false : ∀ (c : (uN-fam0 (32))) (t-opt : (Maybe valtype)) (instr-1-lst : (List instr)) (instr-2-lst : (List instr)) → 
    ((proj-uN-0 32 c) ≡ 0) →
    Step-pure (as (List admininstr) ((admininstr-CONST I32 c) ∷ (admininstr-IFELSE t-opt instr-1-lst instr-2-lst) ∷ [])) (as (List admininstr) ((admininstr-BLOCK t-opt instr-2-lst) ∷ []))
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
  unop-val : ∀ (t : valtype) (c-1 : (val- t)) (unop : (unop- t)) (c : (val- t)) → 
    ((length (fun-unop- t unop c-1)) > 0) →
    (c ∈ (fun-unop- t unop c-1)) →
    Step-pure (as (List admininstr) ((admininstr-CONST t c-1) ∷ (admininstr-UNOP t unop) ∷ [])) (as (List admininstr) ((admininstr-CONST t c) ∷ []))
  unop-trap : ∀ (t : valtype) (c-1 : (val- t)) (unop : (unop- t)) → 
    ((fun-unop- t unop c-1) ≡ []) →
    Step-pure (as (List admininstr) ((admininstr-CONST t c-1) ∷ (admininstr-UNOP t unop) ∷ [])) (as (List admininstr) (admininstr-TRAP ∷ []))
  binop-val : ∀ (t : valtype) (c-1 : (val- t)) (c-2 : (val- t)) (binop : (binop- t)) (c : (val- t)) → 
    ((length (fun-binop- t binop c-1 c-2)) > 0) →
    (c ∈ (fun-binop- t binop c-1 c-2)) →
    Step-pure (as (List admininstr) ((admininstr-CONST t c-1) ∷ (admininstr-CONST t c-2) ∷ (admininstr-BINOP t binop) ∷ [])) (as (List admininstr) ((admininstr-CONST t c) ∷ []))
  binop-trap : ∀ (t : valtype) (c-1 : (val- t)) (c-2 : (val- t)) (binop : (binop- t)) → 
    ((fun-binop- t binop c-1 c-2) ≡ []) →
    Step-pure (as (List admininstr) ((admininstr-CONST t c-1) ∷ (admininstr-CONST t c-2) ∷ (admininstr-BINOP t binop) ∷ [])) (as (List admininstr) (admininstr-TRAP ∷ []))
  Step-pure--testop : ∀ (t : valtype) (c-1 : (val- t)) (testop : (testop- t)) (c : (uN-fam0 (32))) → 
    (c ≡ (fun-testop- t testop c-1)) →
    Step-pure (as (List admininstr) ((admininstr-CONST t c-1) ∷ (admininstr-TESTOP t testop) ∷ [])) (as (List admininstr) ((admininstr-CONST I32 c) ∷ []))
  Step-pure--relop : ∀ (t : valtype) (c-1 : (val- t)) (c-2 : (val- t)) (relop : (relop- t)) (c : (uN-fam0 (32))) → 
    (c ≡ (fun-relop- t relop c-1 c-2)) →
    Step-pure (as (List admininstr) ((admininstr-CONST t c-1) ∷ (admininstr-CONST t c-2) ∷ (admininstr-RELOP t relop) ∷ [])) (as (List admininstr) ((admininstr-CONST I32 c) ∷ []))
  cvtop-val : ∀ (t-1 : valtype) (c-1 : (val- t-1)) (t-2 : valtype) (v-cvtop : cvtop) (c : (val- t-2)) → 
    ((length (cvtop-- t-1 t-2 v-cvtop c-1)) > 0) →
    (c ∈ (cvtop-- t-1 t-2 v-cvtop c-1)) →
    Step-pure (as (List admininstr) ((admininstr-CONST t-1 c-1) ∷ (admininstr-CVTOP t-2 t-1 v-cvtop) ∷ [])) (as (List admininstr) ((admininstr-CONST t-2 c) ∷ []))
  cvtop-trap : ∀ (t-1 : valtype) (c-1 : (val- t-1)) (t-2 : valtype) (v-cvtop : cvtop) → 
    ((cvtop-- t-1 t-2 v-cvtop c-1) ≡ []) →
    Step-pure (as (List admininstr) ((admininstr-CONST t-1 c-1) ∷ (admininstr-CVTOP t-2 t-1 v-cvtop) ∷ [])) (as (List admininstr) (admininstr-TRAP ∷ []))
  Step-pure--local-tee : ∀ (v-val : val) (x : idx) → Step-pure (as (List admininstr) ((admininstr-val v-val) ∷ (admininstr-LOCAL-TEE x) ∷ [])) (as (List admininstr) ((admininstr-val v-val) ∷ (admininstr-val v-val) ∷ (admininstr-LOCAL-SET x) ∷ []))

{- Inductive Relations Definition at: ../specification/wasm-1.0/8-reduction.spectec:121.1-123.15 -}
data Step-read-before-call-indirect-trap : config → Set where
  call-indirect-call-0 : ∀ (z : state) (i : (uN-fam0 (32))) (x : idx) (a : addr) → 
    ((proj-uN-0 32 i) < (length (REFS (fun-table z (mk-uN 0))))) →
    (((REFS (fun-table z (mk-uN 0))) [ (proj-uN-0 32 i) ]!) ≡ (just a)) →
    (a < (length (fun-funcinst z))) →
    ((fun-type z x) ≡ (funcinst-TYPE ((fun-funcinst z) [ a ]!))) →
    Step-read-before-call-indirect-trap (mk-config z (as (List admininstr) ((admininstr-CONST I32 i) ∷ (admininstr-CALL-INDIRECT x) ∷ [])))

{- Inductive Relations Definition at: ../specification/wasm-1.0/8-reduction.spectec:7.1-7.77 -}
data Step-read : config → (List admininstr) → Set where
  Step-read--block : ∀ (z : state) (t-opt : (Maybe valtype)) (instr-lst : (List instr)) (v-n : n) → 
    (((t-opt ≡ nothing) × (v-n ≡ 0)) ⊎ ((t-opt ≢ nothing) × (v-n ≡ 1))) →
    Step-read (mk-config z (as (List admininstr) ((admininstr-BLOCK t-opt instr-lst) ∷ []))) (as (List admininstr) ((LABEL- v-n [] (map (λ (v-instr : instr) → (admininstr-instr v-instr)) instr-lst)) ∷ []))
  Step-read--loop : ∀ (z : state) (t-opt : (Maybe valtype)) (instr-lst : (List instr)) → Step-read (mk-config z (as (List admininstr) ((admininstr-LOOP t-opt instr-lst) ∷ []))) (as (List admininstr) ((LABEL- 0 (as (List instr) ((LOOP t-opt instr-lst) ∷ [])) (map (λ (v-instr : instr) → (admininstr-instr v-instr)) instr-lst)) ∷ []))
  Step-read--call : ∀ (z : state) (x : idx) → 
    ((proj-uN-0 32 x) < (length (fun-funcaddr z))) →
    Step-read (mk-config z (as (List admininstr) ((admininstr-CALL x) ∷ []))) (as (List admininstr) ((CALL-ADDR ((fun-funcaddr z) [ (proj-uN-0 32 x) ]!)) ∷ []))
  call-indirect-call : ∀ (z : state) (i : (uN-fam0 (32))) (x : idx) (a : addr) → 
    ((proj-uN-0 32 i) < (length (REFS (fun-table z (mk-uN 0))))) →
    (((REFS (fun-table z (mk-uN 0))) [ (proj-uN-0 32 i) ]!) ≡ (just a)) →
    (a < (length (fun-funcinst z))) →
    ((fun-type z x) ≡ (funcinst-TYPE ((fun-funcinst z) [ a ]!))) →
    Step-read (mk-config z (as (List admininstr) ((admininstr-CONST I32 i) ∷ (admininstr-CALL-INDIRECT x) ∷ []))) (as (List admininstr) ((CALL-ADDR a) ∷ []))
  call-indirect-trap : ∀ (z : state) (i : (uN-fam0 (32))) (x : idx) → 
    (¬ (Step-read-before-call-indirect-trap (mk-config z (as (List admininstr) ((admininstr-CONST I32 i) ∷ (admininstr-CALL-INDIRECT x) ∷ []))))) →
    Step-read (mk-config z (as (List admininstr) ((admininstr-CONST I32 i) ∷ (admininstr-CALL-INDIRECT x) ∷ []))) (as (List admininstr) (admininstr-TRAP ∷ []))
  call-addr : ∀ (z : state) (k : ℕ) (val-lst : (List val)) (a : addr) (v-n : n) (f : frame) (instr-lst : (List instr)) (t-1-lst : (List valtype)) (t-2-lst : (List valtype)) (mm : moduleinst) (v-func : func) (x : idx) (t-lst : (List valtype)) → 
    ((length (val-lst)) ≡ (k)) →
    ((length (t-2-lst)) ≡ (v-n)) →
    ((length (t-1-lst)) ≡ (k)) →
    (a < (length (fun-funcinst z))) →
    (((fun-funcinst z) [ a ]!) ≡ record { funcinst-TYPE = (mk-functype t-1-lst t-2-lst) ; funcinst-MODULE = mm ; CODE = v-func }) →
    (v-func ≡ (func-FUNC x (map (λ (t : valtype) → (LOCAL t)) t-lst) instr-lst)) →
    (f ≡ record { LOCALS = (val-lst ++ (map (λ (t : valtype) → (default- t)) t-lst)) ; frame-MODULE = mm }) →
    Step-read (mk-config z ((map (λ (v-val : val) → (admininstr-val v-val)) val-lst) ++ (as (List admininstr) ((CALL-ADDR a) ∷ [])))) (as (List admininstr) ((FRAME- v-n f (as (List admininstr) ((LABEL- v-n [] (map (λ (v-instr : instr) → (admininstr-instr v-instr)) instr-lst)) ∷ []))) ∷ []))
  Step-read--local-get : ∀ (z : state) (x : idx) → Step-read (mk-config z (as (List admininstr) ((admininstr-LOCAL-GET x) ∷ []))) ((admininstr-val (fun-local z x)) ∷ [])
  Step-read--global-get : ∀ (z : state) (x : idx) → Step-read (mk-config z (as (List admininstr) ((admininstr-GLOBAL-GET x) ∷ []))) ((admininstr-val (VALUE (fun-global z x))) ∷ [])
  load-num-trap : ∀ (z : state) (i : (uN-fam0 (32))) (t : valtype) (ao : memarg) → 
    ((((proj-uN-0 32 i) + (proj-uN-0 32 (OFFSET ao))) + (coerce {B = ℕ} ((coerce {B = ℕ} (size t)) / (coerce {B = ℕ} 8)))) > (length (BYTES (fun-mem z (mk-uN 0))))) →
    Step-read (mk-config z (as (List admininstr) ((admininstr-CONST I32 i) ∷ (admininstr-LOAD t nothing ao) ∷ []))) (as (List admininstr) (admininstr-TRAP ∷ []))
  load-num-val : ∀ (z : state) (i : (uN-fam0 (32))) (t : valtype) (ao : memarg) (c : (val- t)) → 
    ((bytes- t c) ≡ (slice (BYTES (fun-mem z (mk-uN 0))) ((proj-uN-0 32 i) + (proj-uN-0 32 (OFFSET ao))) (coerce {B = ℕ} ((coerce {B = ℕ} (size t)) / (coerce {B = ℕ} 8))))) →
    Step-read (mk-config z (as (List admininstr) ((admininstr-CONST I32 i) ∷ (admininstr-LOAD t nothing ao) ∷ []))) (as (List admininstr) ((admininstr-CONST t c) ∷ []))
  load-pack-trap-0 : ∀ (z : state) (i : (uN-fam0 (32))) (v-n : n) (v-sx : sx) (ao : memarg) → 
    ((((proj-uN-0 32 i) + (proj-uN-0 32 (OFFSET ao))) + (coerce {B = ℕ} ((coerce {B = ℕ} v-n) / (coerce {B = ℕ} 8)))) > (length (BYTES (fun-mem z (mk-uN 0))))) →
    Step-read (mk-config z (as (List admininstr) ((admininstr-CONST I32 i) ∷ (admininstr-LOAD (valtype-Inn Inn-I32) (just (mk-loadop- (mk-sz v-n) v-sx)) ao) ∷ []))) (as (List admininstr) (admininstr-TRAP ∷ []))
  load-pack-trap-1 : ∀ (z : state) (i : (uN-fam0 (32))) (v-n : n) (v-sx : sx) (ao : memarg) → 
    ((((proj-uN-0 32 i) + (proj-uN-0 32 (OFFSET ao))) + (coerce {B = ℕ} ((coerce {B = ℕ} v-n) / (coerce {B = ℕ} 8)))) > (length (BYTES (fun-mem z (mk-uN 0))))) →
    Step-read (mk-config z (as (List admininstr) ((admininstr-CONST I32 i) ∷ (admininstr-LOAD (valtype-Inn Inn-I64) (just (mk-loadop- (mk-sz v-n) v-sx)) ao) ∷ []))) (as (List admininstr) (admininstr-TRAP ∷ []))
  load-pack-val-0 : ∀ (z : state) (i : (uN-fam0 (32))) (v-n : n) (v-sx : sx) (ao : memarg) (c : (uN-fam0 (v-n))) → 
    ((ibytes- v-n c) ≡ (slice (BYTES (fun-mem z (mk-uN 0))) ((proj-uN-0 32 i) + (proj-uN-0 32 (OFFSET ao))) (coerce {B = ℕ} ((coerce {B = ℕ} v-n) / (coerce {B = ℕ} 8))))) →
    Step-read (mk-config z (as (List admininstr) ((admininstr-CONST I32 i) ∷ (admininstr-LOAD (valtype-Inn Inn-I32) (just (mk-loadop- (mk-sz v-n) v-sx)) ao) ∷ []))) (as (List admininstr) ((admininstr-CONST (valtype-Inn Inn-I32) (extend-- v-n (size (valtype-Inn Inn-I32)) v-sx c)) ∷ []))
  load-pack-val-1 : ∀ (z : state) (i : (uN-fam0 (32))) (v-n : n) (v-sx : sx) (ao : memarg) (c : (uN-fam0 (v-n))) → 
    ((ibytes- v-n c) ≡ (slice (BYTES (fun-mem z (mk-uN 0))) ((proj-uN-0 32 i) + (proj-uN-0 32 (OFFSET ao))) (coerce {B = ℕ} ((coerce {B = ℕ} v-n) / (coerce {B = ℕ} 8))))) →
    Step-read (mk-config z (as (List admininstr) ((admininstr-CONST I32 i) ∷ (admininstr-LOAD (valtype-Inn Inn-I64) (just (mk-loadop- (mk-sz v-n) v-sx)) ao) ∷ []))) (as (List admininstr) ((admininstr-CONST (valtype-Inn Inn-I64) (extend-- v-n (size (valtype-Inn Inn-I64)) v-sx c)) ∷ []))
  Step-read--memory-size : ∀ (z : state) (v-n : n) → 
    (((v-n * 64) * (Ki )) ≡ (length (BYTES (fun-mem z (mk-uN 0))))) →
    Step-read (mk-config z (as (List admininstr) (admininstr-MEMORY-SIZE ∷ []))) (as (List admininstr) ((admininstr-CONST I32 (mk-uN v-n)) ∷ []))

{- Inductive Relations Definition at: ../specification/wasm-1.0/8-reduction.spectec:5.1-5.77 -}
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
  store-num-trap : ∀ (z : state) (i : (uN-fam0 (32))) (t : valtype) (c : (val- t)) (ao : memarg) → 
    ((((proj-uN-0 32 i) + (proj-uN-0 32 (OFFSET ao))) + (coerce {B = ℕ} ((coerce {B = ℕ} (size t)) / (coerce {B = ℕ} 8)))) > (length (BYTES (fun-mem z (mk-uN 0))))) →
    Step (mk-config z (as (List admininstr) ((admininstr-CONST I32 i) ∷ (admininstr-CONST t c) ∷ (admininstr-STORE t nothing ao) ∷ []))) (mk-config z (as (List admininstr) (admininstr-TRAP ∷ [])))
  store-num-val : ∀ (z : state) (i : (uN-fam0 (32))) (t : valtype) (c : (val- t)) (ao : memarg) (b-lst : (List byte)) → 
    (b-lst ≡ (bytes- t c)) →
    Step (mk-config z (as (List admininstr) ((admininstr-CONST I32 i) ∷ (admininstr-CONST t c) ∷ (admininstr-STORE t nothing ao) ∷ []))) (mk-config (with-mem z (mk-uN 0) ((proj-uN-0 32 i) + (proj-uN-0 32 (OFFSET ao))) (coerce {B = ℕ} ((coerce {B = ℕ} (size t)) / (coerce {B = ℕ} 8))) b-lst) [])
  store-pack-trap-0 : ∀ (z : state) (i : (uN-fam0 (32))) (c : (uN-fam0 (32))) (v-n : n) (ao : memarg) → 
    ((((proj-uN-0 32 i) + (proj-uN-0 32 (OFFSET ao))) + (coerce {B = ℕ} ((coerce {B = ℕ} v-n) / (coerce {B = ℕ} 8)))) > (length (BYTES (fun-mem z (mk-uN 0))))) →
    Step (mk-config z (as (List admininstr) ((admininstr-CONST I32 i) ∷ (admininstr-CONST (valtype-Inn Inn-I32) c) ∷ (admininstr-STORE (valtype-Inn Inn-I32) (just (mk-sz v-n)) ao) ∷ []))) (mk-config z (as (List admininstr) (admininstr-TRAP ∷ [])))
  store-pack-trap-1 : ∀ (z : state) (i : (uN-fam0 (32))) (c : (uN-fam0 (64))) (v-n : n) (ao : memarg) → 
    ((((proj-uN-0 32 i) + (proj-uN-0 32 (OFFSET ao))) + (coerce {B = ℕ} ((coerce {B = ℕ} v-n) / (coerce {B = ℕ} 8)))) > (length (BYTES (fun-mem z (mk-uN 0))))) →
    Step (mk-config z (as (List admininstr) ((admininstr-CONST I32 i) ∷ (admininstr-CONST (valtype-Inn Inn-I64) c) ∷ (admininstr-STORE (valtype-Inn Inn-I64) (just (mk-sz v-n)) ao) ∷ []))) (mk-config z (as (List admininstr) (admininstr-TRAP ∷ [])))
  store-pack-val-0 : ∀ (z : state) (i : (uN-fam0 (32))) (c : (uN-fam0 (32))) (v-n : n) (ao : memarg) (b-lst : (List byte)) → 
    (b-lst ≡ (ibytes- v-n (wrap-- (size (valtype-Inn Inn-I32)) v-n c))) →
    Step (mk-config z (as (List admininstr) ((admininstr-CONST I32 i) ∷ (admininstr-CONST (valtype-Inn Inn-I32) c) ∷ (admininstr-STORE (valtype-Inn Inn-I32) (just (mk-sz v-n)) ao) ∷ []))) (mk-config (with-mem z (mk-uN 0) ((proj-uN-0 32 i) + (proj-uN-0 32 (OFFSET ao))) (coerce {B = ℕ} ((coerce {B = ℕ} v-n) / (coerce {B = ℕ} 8))) b-lst) [])
  store-pack-val-1 : ∀ (z : state) (i : (uN-fam0 (32))) (c : (uN-fam0 (64))) (v-n : n) (ao : memarg) (b-lst : (List byte)) → 
    (b-lst ≡ (ibytes- v-n (wrap-- (size (valtype-Inn Inn-I64)) v-n c))) →
    Step (mk-config z (as (List admininstr) ((admininstr-CONST I32 i) ∷ (admininstr-CONST (valtype-Inn Inn-I64) c) ∷ (admininstr-STORE (valtype-Inn Inn-I64) (just (mk-sz v-n)) ao) ∷ []))) (mk-config (with-mem z (mk-uN 0) ((proj-uN-0 32 i) + (proj-uN-0 32 (OFFSET ao))) (coerce {B = ℕ} ((coerce {B = ℕ} v-n) / (coerce {B = ℕ} 8))) b-lst) [])
  memory-grow-succeed : ∀ (z : state) (v-n : n) (mi : meminst) → 
    ((growmemory (fun-mem z (mk-uN 0)) v-n) ≢ nothing) →
    ((unwrap! (growmemory (fun-mem z (mk-uN 0)) v-n)) ≡ mi) →
    Step (mk-config z (as (List admininstr) ((admininstr-CONST I32 (mk-uN v-n)) ∷ admininstr-MEMORY-GROW ∷ []))) (mk-config (with-meminst z (mk-uN 0) mi) (as (List admininstr) ((admininstr-CONST I32 (mk-uN (coerce {B = ℕ} ((coerce {B = ℕ} (length (BYTES (fun-mem z (mk-uN 0))))) / (coerce {B = ℕ} (64 * (Ki ))))))) ∷ [])))
  memory-grow-fail : ∀ (z : state) (v-n : n) → Step (mk-config z (as (List admininstr) ((admininstr-CONST I32 (mk-uN v-n)) ∷ admininstr-MEMORY-GROW ∷ []))) (mk-config z (as (List admininstr) ((admininstr-CONST I32 (mk-uN (inv-signed- 32 (0 – (coerce {B = ℕ} 1))))) ∷ [])))

{- Inductive Relations Definition at: ../specification/wasm-1.0/8-reduction.spectec:8.1-8.77 -}
data Steps : config → config → Set where
  refl' : ∀ (z : state) (admininstr-lst : (List admininstr)) → Steps (mk-config z admininstr-lst) (mk-config z admininstr-lst)
  trans : ∀ (z : state) (admininstr-lst : (List admininstr)) (z'' : state) (admininstr''-lst : (List admininstr)) (z' : state) (admininstr'-lst : (List admininstr)) → 
    (Step (mk-config z admininstr-lst) (mk-config z' admininstr'-lst)) →
    (Steps (mk-config z' admininstr'-lst) (mk-config z'' admininstr''-lst)) →
    Steps (mk-config z admininstr-lst) (mk-config z'' admininstr''-lst)

{- Inductive Relations Definition at: ../specification/wasm-1.0/8-reduction.spectec:29.1-29.83 -}
data Eval-expr : state → expr → state → (List val) → Set where
  mk-Eval-expr : ∀ (z : state) (instr-lst : (List instr)) (z' : state) (val-lst : (List val)) → 
    (Steps (mk-config z (map (λ (v-instr : instr) → (admininstr-instr v-instr)) instr-lst)) (mk-config z' (map (λ (v-val : val) → (admininstr-val v-val)) val-lst))) →
    Eval-expr z instr-lst z' val-lst

{- Auxiliary Definition at: ../specification/wasm-1.0/9-module.spectec:5.1-5.36 -}
{-# TERMINATING #-}
funcs : (var-0-lst : (List externaddr)) → (List funcaddr)
funcs [] = []
funcs ((externaddr-FUNC fa) ∷ externaddr'-lst) = ((fa ∷ []) ++ (funcs externaddr'-lst))
funcs (v-externaddr ∷ externaddr'-lst) = (funcs externaddr'-lst)
funcs var-0-lst = []

{- Auxiliary Definition at: ../specification/wasm-1.0/9-module.spectec:11.1-11.40 -}
{-# TERMINATING #-}
globals : (var-0-lst : (List externaddr)) → (List globaladdr)
globals [] = []
globals ((externaddr-GLOBAL ga) ∷ externaddr'-lst) = ((ga ∷ []) ++ (globals externaddr'-lst))
globals (v-externaddr ∷ externaddr'-lst) = (globals externaddr'-lst)
globals var-0-lst = []

{- Auxiliary Definition at: ../specification/wasm-1.0/9-module.spectec:17.1-17.38 -}
{-# TERMINATING #-}
tables : (var-0-lst : (List externaddr)) → (List tableaddr)
tables [] = []
tables ((externaddr-TABLE ta) ∷ externaddr'-lst) = ((ta ∷ []) ++ (tables externaddr'-lst))
tables (v-externaddr ∷ externaddr'-lst) = (tables externaddr'-lst)
tables var-0-lst = []

{- Auxiliary Definition at: ../specification/wasm-1.0/9-module.spectec:23.1-23.34 -}
{-# TERMINATING #-}
mems : (var-0-lst : (List externaddr)) → (List memaddr)
mems [] = []
mems ((externaddr-MEM ma) ∷ externaddr'-lst) = ((ma ∷ []) ++ (mems externaddr'-lst))
mems (v-externaddr ∷ externaddr'-lst) = (mems externaddr'-lst)
mems var-0-lst = []

{- Auxiliary Definition at: ../specification/wasm-1.0/9-module.spectec:36.1-36.60 -}
postulate allocfunc : ∀ (v-store : store) (v-moduleinst : moduleinst) (v-func : func) → (store × funcaddr)

{- Auxiliary Definition at: ../specification/wasm-1.0/9-module.spectec:41.1-41.63 -}
{-# TERMINATING #-}
allocfuncs : (v-store : store) (v-moduleinst : moduleinst) (var-0-lst : (List func)) → (store × (List funcaddr))
allocfuncs s v-moduleinst [] = (s , [])
allocfuncs s v-moduleinst (v-func ∷ func'-lst) = let (s-1 , fa) = (allocfunc s v-moduleinst v-func) in let (s-2 , fa'-lst) = (allocfuncs s-1 v-moduleinst func'-lst) in (s-2 , ((fa ∷ []) ++ fa'-lst))
allocfuncs v-store v-moduleinst var-0-lst = (default-val , [])

{- Auxiliary Definition at: ../specification/wasm-1.0/9-module.spectec:47.1-47.63 -}
postulate allocglobal : ∀ (v-store : store) (v-globaltype : globaltype) (v-val : val) → (store × globaladdr)

{- Auxiliary Definition at: ../specification/wasm-1.0/9-module.spectec:51.1-51.67 -}
{-# TERMINATING #-}
allocglobals : (v-store : store) (var-0-lst : (List globaltype)) (var-1-lst : (List val)) → (store × (List globaladdr))
allocglobals s [] [] = (s , [])
allocglobals s (v-globaltype ∷ globaltype'-lst) (v-val ∷ val'-lst) = let (s-1 , ga) = (allocglobal s v-globaltype v-val) in let (s-2 , ga'-lst) = (allocglobals s-1 globaltype'-lst val'-lst) in (s-2 , ((ga ∷ []) ++ ga'-lst))
allocglobals v-store var-0-lst var-1-lst = (default-val , [])

{- Auxiliary Definition at: ../specification/wasm-1.0/9-module.spectec:57.1-57.55 -}
postulate alloctable : ∀ (v-store : store) (v-tabletype : tabletype) → (store × tableaddr)

{- Auxiliary Definition at: ../specification/wasm-1.0/9-module.spectec:61.1-61.58 -}
{-# TERMINATING #-}
alloctables : (v-store : store) (var-0-lst : (List tabletype)) → (store × (List tableaddr))
alloctables s [] = (s , [])
alloctables s (v-tabletype ∷ tabletype'-lst) = let (s-1 , ta) = (alloctable s v-tabletype) in let (s-2 , ta'-lst) = (alloctables s-1 tabletype'-lst) in (s-2 , ((ta ∷ []) ++ ta'-lst))
alloctables v-store var-0-lst = (default-val , [])

{- Auxiliary Definition at: ../specification/wasm-1.0/9-module.spectec:67.1-67.49 -}
postulate allocmem : ∀ (v-store : store) (v-memtype : memtype) → (store × memaddr)

{- Auxiliary Definition at: ../specification/wasm-1.0/9-module.spectec:71.1-71.52 -}
{-# TERMINATING #-}
allocmems : (v-store : store) (var-0-lst : (List memtype)) → (store × (List memaddr))
allocmems s [] = (s , [])
allocmems s (v-memtype ∷ memtype'-lst) = let (s-1 , ma) = (allocmem s v-memtype) in let (s-2 , ma'-lst) = (allocmems s-1 memtype'-lst) in (s-2 , ((ma ∷ []) ++ ma'-lst))
allocmems v-store var-0-lst = (default-val , [])

{- Auxiliary Definition at: ../specification/wasm-1.0/9-module.spectec:80.1-80.83 -}
{-# TERMINATING #-}
instexport : (var-0-lst : (List funcaddr)) (var-1-lst : (List globaladdr)) (var-2-lst : (List tableaddr)) (var-3-lst : (List memaddr)) (v-export : export) → exportinst
instexport fa-lst ga-lst ta-lst ma-lst (EXPORT v-name (externidx-FUNC x)) = record { NAME = v-name ; ADDR = (externaddr-FUNC (fa-lst [ (proj-uN-0 32 x) ]!)) }
instexport fa-lst ga-lst ta-lst ma-lst (EXPORT v-name (externidx-GLOBAL x)) = record { NAME = v-name ; ADDR = (externaddr-GLOBAL (ga-lst [ (proj-uN-0 32 x) ]!)) }
instexport fa-lst ga-lst ta-lst ma-lst (EXPORT v-name (externidx-TABLE x)) = record { NAME = v-name ; ADDR = (externaddr-TABLE (ta-lst [ (proj-uN-0 32 x) ]!)) }
instexport fa-lst ga-lst ta-lst ma-lst (EXPORT v-name (externidx-MEM x)) = record { NAME = v-name ; ADDR = (externaddr-MEM (ma-lst [ (proj-uN-0 32 x) ]!)) }
instexport var-0-lst var-1-lst var-2-lst var-3-lst v-export = default-val

{- Auxiliary Definition at: ../specification/wasm-1.0/9-module.spectec:87.1-87.73 -}
postulate allocmodule : ∀ (v-store : store) (v-module : module') (var-0-lst : (List externaddr)) (var-1-lst : (List val)) → (store × moduleinst)

{- Auxiliary Definition at: ../specification/wasm-1.0/9-module.spectec:128.1-128.61 -}
postulate initelem : ∀ (v-store : store) (v-moduleinst : moduleinst) (var-0-lst : (List u32)) (var-1-lst-lst : (List (List funcaddr))) → store

{- Auxiliary Definition at: ../specification/wasm-1.0/9-module.spectec:134.1-134.57 -}
{-# TERMINATING #-}
initdata : (v-store : store) (v-moduleinst : moduleinst) (var-0-lst : (List u32)) (var-1-lst-lst : (List (List byte))) → store
initdata s v-moduleinst [] [] = s
initdata s v-moduleinst (i ∷ i'-lst) (b-lst ∷ b'-lst-lst) = let s-1 = (record s { store-MEMS = (modify (store-MEMS s) ((MEMS v-moduleinst) [ 0 ]!) (λ (var-1 : meminst) → (record var-1 { BYTES = (slice-update (BYTES var-1) (proj-uN-0 32 i) (length b-lst) b-lst) }))) }) in let s-2 = (initdata s-1 v-moduleinst i'-lst b'-lst-lst) in s-2
initdata v-store v-moduleinst var-0-lst var-1-lst-lst = default-val

{- Auxiliary Definition at: ../specification/wasm-1.0/9-module.spectec:140.1-140.54 -}
postulate instantiate : ∀ (v-store : store) (v-module : module') (var-0-lst : (List externaddr)) → config

{- Auxiliary Definition at: ../specification/wasm-1.0/9-module.spectec:169.1-169.44 -}
postulate invoke : ∀ (v-store : store) (v-funcaddr : funcaddr) (var-0-lst : (List val)) → config
