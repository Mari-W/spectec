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

{- Type Alias Definition at: doc/example/NanoWasm.spectec:7.1-7.22 -}
localidx : Set
localidx = ℕ

{- Type Alias Definition at: doc/example/NanoWasm.spectec:8.1-8.23 -}
globalidx : Set
globalidx = ℕ

{- Inductive Type Definition at: doc/example/NanoWasm.spectec:10.1-10.17 -}
data mut : Set where
  MUT : mut

instance
  inh-mut : Inhabited mut
  inh-mut = record { default-val = MUT }

{- Inductive Type Definition at: doc/example/NanoWasm.spectec:11.1-11.39 -}
data valtype : Set where
  I32 : valtype
  I64 : valtype
  F32 : valtype
  F64 : valtype

instance
  inh-valtype : Inhabited valtype
  inh-valtype = record { default-val = I32 }

{- Inductive Type Definition at: doc/example/NanoWasm.spectec:12.1-12.39 -}
data functype : Set where
  mk-functype : (valtype-lst : (List valtype)) → (valtype-lst : (List valtype)) → functype

{- Inductive Type Definition at: doc/example/NanoWasm.spectec:13.1-13.33 -}
data globaltype : Set where
  mk-globaltype : (mut-opt : (Maybe mut)) → (v-valtype : valtype) → globaltype

instance
  inh-globaltype : Inhabited globaltype
  inh-globaltype = record { default-val = (mk-globaltype (nothing) (default-val)) }

{- Type Alias Definition at: doc/example/NanoWasm.spectec:15.1-15.19 -}
const : Set
const = ℕ

{- Inductive Type Definition at: doc/example/NanoWasm.spectec:17.1-25.27 -}
data instr : Set where
  NOP : instr
  DROP : instr
  SELECT : instr
  CONST : (v-valtype : valtype) → (v-const : const) → instr
  LOCAL-GET : (v-localidx : localidx) → instr
  LOCAL-SET : (v-localidx : localidx) → instr
  GLOBAL-GET : (v-globalidx : globalidx) → instr
  GLOBAL-SET : (v-globalidx : globalidx) → instr

instance
  inh-instr : Inhabited instr
  inh-instr = record { default-val = NOP }

{- Record Creation Definition at: doc/example/NanoWasm.spectec:30.1-30.58 -}
record context : Set where
  constructor mk-context
  field
    GLOBALS : (List globaltype)
    LOCALS : (List valtype)
open context

instance
  append-context : HasAppend (context)
  append-context = record { append = λ arg1 arg2 → record {
    GLOBALS = GLOBALS arg1 ⧺ GLOBALS arg2 ;
    LOCALS = LOCALS arg1 ⧺ LOCALS arg2 } }

{- Inductive Relations Definition at: doc/example/NanoWasm.spectec:35.1-35.47 -}
data Instr-ok : context → instr → functype → Set where
  nop : ∀ (C : context) → Instr-ok C NOP (mk-functype [] [])
  drop' : ∀ (C : context) (t : valtype) → Instr-ok C DROP (mk-functype (t ∷ []) [])
  select : ∀ (C : context) (t : valtype) → Instr-ok C SELECT (mk-functype (as (List valtype) (t ∷ t ∷ I32 ∷ [])) (t ∷ []))
  Instr-ok--const : ∀ (C : context) (t : valtype) (c : const) → Instr-ok C (CONST t c) (mk-functype [] (t ∷ []))
  local-get : ∀ (C : context) (x : localidx) (t : valtype) → 
    (x < (length (LOCALS C))) →
    (((LOCALS C) [ x ]!) ≡ t) →
    Instr-ok C (LOCAL-GET x) (mk-functype [] (t ∷ []))
  local-set : ∀ (C : context) (x : localidx) (t : valtype) → 
    (x < (length (LOCALS C))) →
    (((LOCALS C) [ x ]!) ≡ t) →
    Instr-ok C (LOCAL-SET x) (mk-functype (t ∷ []) [])
  global-get : ∀ (C : context) (x : globalidx) (t : valtype) → 
    (x < (length (GLOBALS C))) →
    (((GLOBALS C) [ x ]!) ≡ (mk-globaltype (just MUT) t)) →
    Instr-ok C (GLOBAL-GET x) (mk-functype [] (t ∷ []))
  global-set : ∀ (C : context) (x : globalidx) (t : valtype) → 
    (x < (length (GLOBALS C))) →
    (((GLOBALS C) [ x ]!) ≡ (mk-globaltype (just MUT) t)) →
    Instr-ok C (GLOBAL-SET x) (mk-functype (t ∷ []) [])

{- Type Alias Definition at: doc/example/NanoWasm.spectec:68.1-68.18 -}
addr : Set
addr = ℕ

{- Record Creation Definition at: doc/example/NanoWasm.spectec:69.1-69.38 -}
record moduleinst : Set where
  constructor mk-moduleinst
  field
    moduleinst-GLOBALS : (List addr)
open moduleinst

instance
  append-moduleinst : HasAppend (moduleinst)
  append-moduleinst = record { append = λ arg1 arg2 → record {
    moduleinst-GLOBALS = moduleinst-GLOBALS arg1 ⧺ moduleinst-GLOBALS arg2 } }

instance
  inh-moduleinst : Inhabited moduleinst
  inh-moduleinst = record { default-val = record { moduleinst-GLOBALS = default-val } }

{- Inductive Type Definition at: doc/example/NanoWasm.spectec:71.1-71.33 -}
data val : Set where
  val-CONST : (v-valtype : valtype) → (v-const : const) → val

instance
  inh-val : Inhabited val
  inh-val = record { default-val = (val-CONST (default-val) (default-val)) }

{- Auxiliary Definition at:  -}
{-# TERMINATING #-}
instr-val : (var-0 : val) → instr
instr-val (val-CONST x0 x1) = (CONST x0 x1)
instr-val var-0 = default-val

{- Record Creation Definition at: doc/example/NanoWasm.spectec:73.1-73.32 -}
record store : Set where
  constructor mk-store
  field
    store-GLOBALS : (List val)
open store

instance
  append-store : HasAppend (store)
  append-store = record { append = λ arg1 arg2 → record {
    store-GLOBALS = store-GLOBALS arg1 ⧺ store-GLOBALS arg2 } }

instance
  inh-store : Inhabited store
  inh-store = record { default-val = record { store-GLOBALS = default-val } }

{- Record Creation Definition at: doc/example/NanoWasm.spectec:74.1-74.50 -}
record frame : Set where
  constructor mk-frame
  field
    frame-LOCALS : (List val)
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

{- Inductive Type Definition at: doc/example/NanoWasm.spectec:75.1-75.28 -}
data state : Set where
  mk-state : (v-store : store) → (v-frame : frame) → state

instance
  inh-state : Inhabited state
  inh-state = record { default-val = (mk-state (default-val) (default-val)) }

{- Inductive Type Definition at: doc/example/NanoWasm.spectec:76.1-76.30 -}
data config : Set where
  mk-config : (v-state : state) → (instr-lst : (List instr)) → config

{- Auxiliary Definition at: doc/example/NanoWasm.spectec:82.1-82.34 -}
{-# TERMINATING #-}
local : (v-state : state) (v-localidx : localidx) → val
local (mk-state s f) x = ((frame-LOCALS f) [ x ]!)
local v-state v-localidx = default-val

{- Auxiliary Definition at: doc/example/NanoWasm.spectec:85.1-85.36 -}
{-# TERMINATING #-}
global : (v-state : state) (v-globalidx : globalidx) → val
global (mk-state s f) x = ((store-GLOBALS s) [ ((moduleinst-GLOBALS (MODULE f)) [ x ]!) ]!)
global v-state v-globalidx = default-val

{- Auxiliary Definition at: doc/example/NanoWasm.spectec:88.1-88.48 -}
{-# TERMINATING #-}
update-local : (v-state : state) (v-localidx : localidx) (v-val : val) → state
update-local (mk-state s f) x v = (mk-state s (record f { frame-LOCALS = (modify (frame-LOCALS f) x (λ (_ : val) → v)) }))
update-local v-state v-localidx v-val = default-val

{- Auxiliary Definition at: doc/example/NanoWasm.spectec:91.1-91.50 -}
{-# TERMINATING #-}
update-global : (v-state : state) (v-globalidx : globalidx) (v-val : val) → state
update-global (mk-state s f) x v = (mk-state (record s { store-GLOBALS = (modify (store-GLOBALS s) ((moduleinst-GLOBALS (MODULE f)) [ x ]!) (λ (_ : val) → v)) }) f)
update-global v-state v-globalidx v-val = default-val

{- Inductive Relations Definition at: doc/example/NanoWasm.spectec:96.1-96.37 -}
data Step-pure : (List instr) → (List instr) → Set where
  Step-pure--nop : Step-pure (as (List instr) (NOP ∷ [])) []
  Step-pure--drop : ∀ (v-val : val) → Step-pure (as (List instr) ((instr-val v-val) ∷ DROP ∷ [])) []
  select-true : ∀ (val-1 : val) (val-2 : val) (c : const) → 
    (c ≢ 0) →
    Step-pure (as (List instr) ((instr-val val-1) ∷ (instr-val val-2) ∷ (CONST I32 c) ∷ SELECT ∷ [])) ((instr-val val-1) ∷ [])
  select-false : ∀ (val-1 : val) (val-2 : val) (c : const) → 
    (c ≡ 0) →
    Step-pure (as (List instr) ((instr-val val-1) ∷ (instr-val val-2) ∷ (CONST I32 c) ∷ SELECT ∷ [])) ((instr-val val-2) ∷ [])

{- Inductive Relations Definition at: doc/example/NanoWasm.spectec:95.1-95.32 -}
data Step : config → config → Set where
  pure : ∀ (z : state) (instr-lst : (List instr)) (instr'-lst : (List instr)) → 
    (Step-pure instr-lst instr'-lst) →
    Step (mk-config z instr-lst) (mk-config z instr'-lst)
  Step--local-get : ∀ (z : state) (x : localidx) (v-val : val) → 
    (v-val ≡ (local z x)) →
    Step (mk-config z (as (List instr) ((LOCAL-GET x) ∷ []))) (mk-config z ((instr-val v-val) ∷ []))
  Step--local-set : ∀ (z : state) (v-val : val) (x : localidx) (z' : state) → 
    (z' ≡ (update-local z x v-val)) →
    Step (mk-config z (as (List instr) ((instr-val v-val) ∷ (LOCAL-SET x) ∷ []))) (mk-config z' [])
  Step--global-get : ∀ (z : state) (x : globalidx) (v-val : val) → 
    (v-val ≡ (global z x)) →
    Step (mk-config z (as (List instr) ((GLOBAL-GET x) ∷ []))) (mk-config z ((instr-val v-val) ∷ []))
  Step--global-set : ∀ (z : state) (v-val : val) (x : globalidx) (z' : state) → 
    (z' ≡ (update-global z x v-val)) →
    Step (mk-config z (as (List instr) ((instr-val v-val) ∷ (GLOBAL-SET x) ∷ []))) (mk-config z' [])

{- Axiom Definition at: doc/example/NanoWasm.spectec:136.1-136.30 -}
postulate float : ∀ (nat : ℕ) (var-0-lst : (List ℕ)) → const


