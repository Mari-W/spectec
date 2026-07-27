------------------------------------------------------------------------
-- nanowasm-safety.agda
--
-- Type safety (progress + preservation) for NanoWasm, proved against
-- the machine-generated spec in nanowasm-check.agda (SpecTec Agda
-- backend output; generated file is NOT modified).
--
-- Judgement shapes follow Haas et al., PLDI 2017, scaled down:
--   value typing        (definitional: typeof)
--   sequence typing     Instrs-ok C es stk ts   (stack types, bottom
--                       of stack at the HEAD of the list, top at the
--                       END, matching the generated Instr-ok functypes)
--   state typing        State-ok C s f
--   config typing       Config-ok (s; f; es) ts
--
-- MAIN RESULTS (see section headers below):
--   preservation       : w.r.t. the generated flat Step — FULLY PROVED
--   progress-ctxt      : w.r.t. Step-ctxt (the standard evaluation-
--                        context closure, which the NanoWasm source
--                        spec omits)                    — FULLY PROVED
--   preservation-ctxt  : FULLY PROVED.  (An earlier version of the
--                        source spec had a typo in Instr_ok/global.set
--                        — its conclusion mentioned GLOBAL.GET — which
--                        made this theorem provably false and forced a
--                        postulate.  The spec was fixed and the
--                        postulate is gone; see the historical note in
--                        section 9.)
--   flat-progress-false: progress w.r.t. the generated flat Step is
--                        provably false ([NOP, NOP] is stuck).
------------------------------------------------------------------------

module nanowasm-safety where

open import nanowasm-check
open context
open moduleinst
open store
open frame

open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (_≟_)
open import Data.List using (List; []; _∷_; _++_; length; map)
open import Data.List.Properties
  using (++-assoc; ++-identityʳ; ++-conicalˡ; ++-conicalʳ;
         ∷ʳ-injective; map-++; ∷-injectiveˡ; ∷-injectiveʳ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; _≢_)

------------------------------------------------------------------------
-- 1. Runtime typing (hand-written; absent from the generated spec)
------------------------------------------------------------------------

-- Value typing is definitional in NanoWasm.
typeof : val → valtype
typeof (val-CONST t _) = t

-- Sequence typing, syntax-directed (cons-based, no _++_ in the
-- instruction index).  Stack types: bottom at head, top at end,
-- matching the generated functypes (SELECT : t t I32 -> t has I32,
-- the top operand, at the END of the input list).
data Instrs-ok (C : context) : List instr → List valtype → List valtype → Set where
  done : ∀ {ts} → Instrs-ok C [] ts ts
  seq  : ∀ {i is ts₀ ts₁ ts₂ ts₃} →
         Instr-ok C i (mk-functype ts₁ ts₂) →
         Instrs-ok C is (ts₀ ++ ts₂) ts₃ →
         Instrs-ok C (i ∷ is) (ts₀ ++ ts₁) ts₃

-- State typing.  NB: the generated global.get/global.set premises
-- both demand globaltype (just MUT) t (the source `MUT? t` option
-- collapses to `just MUT` in translation), so all globals are
-- invariantly MUT here.  The invariant is per context-index but,
-- because it goes through the address indirection, aliased indices
-- are automatically forced to agree on their type.
record State-ok (C : context) (s : store) (f : frame) : Set where
  field
    locals-length  : length (frame-LOCALS f) ≡ length (LOCALS C)
    locals-typing  : ∀ x → x < length (LOCALS C) →
                     typeof ((frame-LOCALS f) [ x ]!) ≡ (LOCALS C) [ x ]!
    globals-addr   : ∀ x → x < length (GLOBALS C) →
                     ((moduleinst-GLOBALS (MODULE f)) [ x ]!) < length (store-GLOBALS s)
    globals-typing : ∀ x → x < length (GLOBALS C) →
                     (GLOBALS C) [ x ]! ≡
                     mk-globaltype (just MUT)
                       (typeof ((store-GLOBALS s) [ (moduleinst-GLOBALS (MODULE f)) [ x ]! ]!))
open State-ok

-- Configuration typing (result type ts; expression typed from the
-- empty stack, as in |- S;T : [t*]).
data Config-ok : config → List valtype → Set where
  config-ok : ∀ {C s f is ts} →
    State-ok C s f →
    Instrs-ok C is [] ts →
    Config-ok (mk-config (mk-state s f) is) ts

-- Terminal configurations: a row of values.
Values : List instr → Set
Values es = Σ (List val) λ vs → es ≡ map instr-val vs

-- The evaluation-context closure of Step.  The NanoWasm source spec
-- (unlike the full Wasm SpecTec spec, which has Step/ctxt) has NO
-- congruence rule, so the generated Step only rewrites entire
-- instruction sequences; this is the standard v* E instr* closure.
data Step-ctxt : config → config → Set where
  ctxt : ∀ {z z′ is₀ is₁} (vs : List val) (rest : List instr) →
    Step (mk-config z is₀) (mk-config z′ is₁) →
    Step-ctxt (mk-config z  (map instr-val vs ++ is₀ ++ rest))
              (mk-config z′ (map instr-val vs ++ is₁ ++ rest))

------------------------------------------------------------------------
-- 2. Generic list / lookup / modify lemmas
------------------------------------------------------------------------

coerce-instrs : ∀ {C is stk stk′ ts ts′} →
  stk ≡ stk′ → ts ≡ ts′ → Instrs-ok C is stk ts → Instrs-ok C is stk′ ts′
coerce-instrs refl refl d = d

length-modify : ∀ {A : Set} (xs : List A) (n : ℕ) (g : A → A) →
  length (modify xs n g) ≡ length xs
length-modify []       n       g = refl
length-modify (x ∷ xs) zero    g = refl
length-modify (x ∷ xs) (suc n) g = cong suc (length-modify xs n g)

lookup-modify-≡ : ∀ {A : Set} {{_ : Inhabited A}} (xs : List A) (n : ℕ) (g : A → A) →
  n < length xs → (modify xs n g) [ n ]! ≡ g (xs [ n ]!)
lookup-modify-≡ (x ∷ xs) zero    g p       = refl
lookup-modify-≡ (x ∷ xs) (suc n) g (s≤s p) = lookup-modify-≡ xs n g p

lookup-modify-≢ : ∀ {A : Set} {{_ : Inhabited A}} (xs : List A) (m n : ℕ) (g : A → A) →
  m ≢ n → (modify xs m g) [ n ]! ≡ xs [ n ]!
lookup-modify-≢ []       m       n       g ne = refl
lookup-modify-≢ (x ∷ xs) zero    zero    g ne = ⊥-elim (ne refl)
lookup-modify-≢ (x ∷ xs) zero    (suc n) g ne = refl
lookup-modify-≢ (x ∷ xs) (suc m) zero    g ne = refl
lookup-modify-≢ (x ∷ xs) (suc m) (suc n) g ne =
  lookup-modify-≢ xs m n g (λ e → ne (cong suc e))

globaltype-inj : ∀ {m m′ t t′} →
  mk-globaltype m t ≡ mk-globaltype m′ t′ → t ≡ t′
globaltype-inj refl = refl

-- map instr-val distributes over a snoc, re-associated to expose the
-- injected value at the head of the tail.
snoc-eq : ∀ (vs₀ : List val) (v : val) (tl : List instr) →
  map instr-val (vs₀ ++ (v ∷ [])) ++ tl ≡ map instr-val vs₀ ++ (instr-val v ∷ tl)
snoc-eq vs₀ v tl =
  trans (cong (_++ tl) (map-++ instr-val vs₀ (v ∷ [])))
        (++-assoc (map instr-val vs₀) (instr-val v ∷ []) tl)

------------------------------------------------------------------------
-- 3. Inversion lemmas
------------------------------------------------------------------------

-- Sequence inversion.  Instrs-ok indices contain ts₀ ++ ts₁ ("green
-- slime"), so inversion must return the equation explicitly instead
-- of letting unification try to solve it.
inv-done : ∀ {C stk ts} → Instrs-ok C [] stk ts → stk ≡ ts
inv-done done = refl

inv-seq : ∀ {C i is stk ts} → Instrs-ok C (i ∷ is) stk ts →
  Σ (List valtype) λ ts₀ → Σ (List valtype) λ ts₁ → Σ (List valtype) λ ts₂ →
    (stk ≡ ts₀ ++ ts₁) ×
    Instr-ok C i (mk-functype ts₁ ts₂) ×
    Instrs-ok C is (ts₀ ++ ts₂) ts
inv-seq (seq {ts₀ = ts₀} {ts₁} {ts₂} iok rest) = ts₀ , ts₁ , ts₂ , refl , iok , rest

-- Per-instruction inversion (all fine for direct matching: the instr
-- index is always a constructor form).
inv-NOP : ∀ {C ts₁ ts₂} → Instr-ok C NOP (mk-functype ts₁ ts₂) →
  (ts₁ ≡ []) × (ts₂ ≡ [])
inv-NOP (nop _) = refl , refl

inv-DROP : ∀ {C ts₁ ts₂} → Instr-ok C DROP (mk-functype ts₁ ts₂) →
  Σ valtype λ t → (ts₁ ≡ t ∷ []) × (ts₂ ≡ [])
inv-DROP (drop' _ t) = t , refl , refl

inv-SELECT : ∀ {C ts₁ ts₂} → Instr-ok C SELECT (mk-functype ts₁ ts₂) →
  Σ valtype λ t → (ts₁ ≡ t ∷ t ∷ I32 ∷ []) × (ts₂ ≡ t ∷ [])
inv-SELECT (select _ t) = t , refl , refl

inv-CONST : ∀ {C t c ts₁ ts₂} → Instr-ok C (CONST t c) (mk-functype ts₁ ts₂) →
  (ts₁ ≡ []) × (ts₂ ≡ t ∷ [])
inv-CONST (Instr-ok--const _ _ _) = refl , refl

inv-LOCAL-GET : ∀ {C x ts₁ ts₂} → Instr-ok C (LOCAL-GET x) (mk-functype ts₁ ts₂) →
  Σ valtype λ t →
    (x < length (LOCALS C)) × ((LOCALS C) [ x ]! ≡ t) ×
    (ts₁ ≡ []) × (ts₂ ≡ t ∷ [])
inv-LOCAL-GET (local-get _ _ t p e) = t , p , e , refl , refl

inv-LOCAL-SET : ∀ {C x ts₁ ts₂} → Instr-ok C (LOCAL-SET x) (mk-functype ts₁ ts₂) →
  Σ valtype λ t →
    (x < length (LOCALS C)) × ((LOCALS C) [ x ]! ≡ t) ×
    (ts₁ ≡ t ∷ []) × (ts₂ ≡ [])
inv-LOCAL-SET (local-set _ _ t p e) = t , p , e , refl , refl

inv-GLOBAL-GET : ∀ {C x ts₁ ts₂} → Instr-ok C (GLOBAL-GET x) (mk-functype ts₁ ts₂) →
  Σ valtype λ t →
    (x < length (GLOBALS C)) ×
    ((GLOBALS C) [ x ]! ≡ mk-globaltype (just MUT) t) ×
    (ts₁ ≡ []) × (ts₂ ≡ t ∷ [])
inv-GLOBAL-GET (global-get _ _ t p e) = t , p , e , refl , refl

inv-GLOBAL-SET : ∀ {C x ts₁ ts₂} → Instr-ok C (GLOBAL-SET x) (mk-functype ts₁ ts₂) →
  Σ valtype λ t →
    (x < length (GLOBALS C)) ×
    ((GLOBALS C) [ x ]! ≡ mk-globaltype (just MUT) t) ×
    (ts₁ ≡ t ∷ []) × (ts₂ ≡ [])
inv-GLOBAL-SET (global-set _ _ t p e) = t , p , e , refl , refl

------------------------------------------------------------------------
-- 4. Value typing and small typing combinators
------------------------------------------------------------------------

-- A single injected value types as a push of its typeof.
value-typing : ∀ {C} (v : val) (ts₀ : List valtype) →
  Instrs-ok C (instr-val v ∷ []) ts₀ (ts₀ ++ (typeof v ∷ []))
value-typing {C} (val-CONST t c) ts₀ =
  coerce-instrs (++-identityʳ ts₀) refl
    (seq {ts₀ = ts₀} (Instr-ok--const C t c) done)

instrs-ok-++ : ∀ {C es₁ es₂ stk ts′ ts} →
  Instrs-ok C es₁ stk ts′ → Instrs-ok C es₂ ts′ ts → Instrs-ok C (es₁ ++ es₂) stk ts
instrs-ok-++ done          d₂ = d₂
instrs-ok-++ (seq iok d₁) d₂ = seq iok (instrs-ok-++ d₁ d₂)

instrs-ok-split : ∀ {C} (es₁ : List instr) {es₂ stk ts} →
  Instrs-ok C (es₁ ++ es₂) stk ts →
  Σ (List valtype) λ ts′ → Instrs-ok C es₁ stk ts′ × Instrs-ok C es₂ ts′ ts
instrs-ok-split []        d           = _ , done , d
instrs-ok-split (i ∷ es₁) (seq iok d) with instrs-ok-split es₁ d
... | ts′ , d₁ , d₂ = ts′ , seq iok d₁ , d₂

------------------------------------------------------------------------
-- 5. Preservation, per redex (generalised over the base stack stk,
--    so the same lemmas serve both the flat and the ctxt-closed
--    theorems)
------------------------------------------------------------------------

nop-pres : ∀ {C stk ts} →
  Instrs-ok C (NOP ∷ []) stk ts → Instrs-ok C [] stk ts
nop-pres d with inv-seq d
... | ts₀ , ts₁ , ts₂ , eq₁ , iok , rest with inv-NOP iok
... | refl , refl =
  coerce-instrs (sym (trans eq₁ (inv-done rest))) refl done

drop-pres : ∀ {C t c stk ts} →
  Instrs-ok C (CONST t c ∷ DROP ∷ []) stk ts → Instrs-ok C [] stk ts
drop-pres d with inv-seq d
... | tsA , ts₁ , ts₂ , eqA , iokC , rest₁ with inv-CONST iokC
... | refl , refl with inv-seq rest₁
... | tsB , ts₁′ , ts₂′ , eqB , iokD , rest₂ with inv-DROP iokD
... | t′ , refl , refl with ∷ʳ-injective tsA tsB eqB
... | tsA≡tsB , _ =
  -- stk ≡ tsA ++ [] ≡ tsB ++ [] ≡ ts
  coerce-instrs
    (sym (trans eqA (trans (cong (_++ []) tsA≡tsB) (inv-done rest₂))))
    refl done

select-pres : ∀ {C t₁ c₁ t₂ c₂ c stk ts} →
  Instrs-ok C (CONST t₁ c₁ ∷ CONST t₂ c₂ ∷ CONST I32 c ∷ SELECT ∷ []) stk ts →
  (Instrs-ok C (CONST t₁ c₁ ∷ []) stk ts) × (Instrs-ok C (CONST t₂ c₂ ∷ []) stk ts)
select-pres {C} {t₁} {c₁} {t₂} {c₂} {c} {stk} {ts} d with inv-seq d
... | tsA , _ , _ , eqA , iok₁ , rest₁ with inv-CONST iok₁
... | refl , refl with inv-seq rest₁
... | tsB , _ , _ , eqB , iok₂ , rest₂ with inv-CONST iok₂
... | refl , refl with inv-seq rest₂
... | tsD , _ , _ , eqD , iok₃ , rest₃ with inv-CONST iok₃
... | refl , refl with inv-seq rest₃
... | tsE , _ , _ , eqE , iokS , rest₄ with inv-SELECT iokS
... | t , refl , refl = result
  where
  -- eqB : tsA ++ (t₁ ∷ []) ≡ tsB ++ []      so tsB ≡ tsA ∷ʳ t₁
  tsB≡ : tsB ≡ tsA ++ (t₁ ∷ [])
  tsB≡ = trans (sym (++-identityʳ tsB)) (sym eqB)
  -- eqD : tsB ++ (t₂ ∷ []) ≡ tsD ++ []      so tsD ≡ tsB ∷ʳ t₂
  tsD≡ : tsD ≡ tsB ++ (t₂ ∷ [])
  tsD≡ = trans (sym (++-identityʳ tsD)) (sym eqD)
  -- eqE : tsD ++ (I32 ∷ []) ≡ tsE ++ (t ∷ t ∷ I32 ∷ [])
  eqE′ : tsD ++ (I32 ∷ []) ≡ (tsE ++ (t ∷ t ∷ [])) ++ (I32 ∷ [])
  eqE′ = trans eqE (sym (++-assoc tsE (t ∷ t ∷ []) (I32 ∷ [])))
  tsD≡′ : tsD ≡ tsE ++ (t ∷ t ∷ [])
  tsD≡′ = proj₁ (∷ʳ-injective tsD (tsE ++ (t ∷ t ∷ [])) eqE′)
  -- peel t₂:  tsB ∷ʳ t₂ ≡ (tsE ∷ʳ t) ∷ʳ t
  eqB′ : tsB ++ (t₂ ∷ []) ≡ (tsE ++ (t ∷ [])) ++ (t ∷ [])
  eqB′ = trans (trans (sym tsD≡) tsD≡′) (sym (++-assoc tsE (t ∷ []) (t ∷ [])))
  tsB≡′ : tsB ≡ tsE ++ (t ∷ [])
  tsB≡′ = proj₁ (∷ʳ-injective tsB (tsE ++ (t ∷ [])) eqB′)
  t₂≡t : t₂ ≡ t
  t₂≡t = proj₂ (∷ʳ-injective tsB (tsE ++ (t ∷ [])) eqB′)
  -- peel t₁:  tsA ∷ʳ t₁ ≡ tsE ∷ʳ t
  eqA′ : tsA ++ (t₁ ∷ []) ≡ tsE ++ (t ∷ [])
  eqA′ = trans (sym tsB≡) tsB≡′
  tsA≡tsE : tsA ≡ tsE
  tsA≡tsE = proj₁ (∷ʳ-injective tsA tsE eqA′)
  t₁≡t : t₁ ≡ t
  t₁≡t = proj₂ (∷ʳ-injective tsA tsE eqA′)
  -- stk ≡ tsA ++ [] ≡ tsA ≡ tsE ;  ts ≡ tsE ++ (t ∷ [])
  stk≡tsE : tsA ++ [] ≡ tsE
  stk≡tsE = trans (++-identityʳ tsA) tsA≡tsE
  ts≡ : tsE ++ (t ∷ []) ≡ ts
  ts≡ = inv-done rest₄
  mk : ∀ t′ c′ → t′ ≡ t → Instrs-ok C (CONST t′ c′ ∷ []) stk ts
  mk t′ c′ e =
    coerce-instrs (trans (sym stk≡tsE) (sym eqA))
      (trans (cong (λ u → tsE ++ (u ∷ [])) e) ts≡)
      (value-typing (val-CONST t′ c′) tsE)
  result = mk t₁ c₁ t₁≡t , mk t₂ c₂ t₂≡t

local-get-pres : ∀ {C s f x stk ts} →
  State-ok C s f →
  Instrs-ok C (LOCAL-GET x ∷ []) stk ts →
  Instrs-ok C (instr-val (local (mk-state s f) x) ∷ []) stk ts
local-get-pres {C} {s} {f} {x} Sok d with inv-seq d
... | tsA , _ , _ , eqA , iok , rest with inv-LOCAL-GET iok
... | t , x< , lk , refl , refl =
  coerce-instrs (trans (sym (++-identityʳ tsA)) (sym eqA))
    (trans (cong (λ u → tsA ++ (u ∷ [])) tv≡t) (inv-done rest))
    (value-typing ((frame-LOCALS f) [ x ]!) tsA)
  where
  tv≡t : typeof ((frame-LOCALS f) [ x ]!) ≡ t
  tv≡t = trans (locals-typing Sok x x<) lk

local-set-pres : ∀ {C s f x t c stk ts} →
  State-ok C s f →
  Instrs-ok C (CONST t c ∷ LOCAL-SET x ∷ []) stk ts →
  State-ok C s (record f { frame-LOCALS = modify (frame-LOCALS f) x (λ _ → val-CONST t c) })
    × Instrs-ok C [] stk ts
local-set-pres {C} {s} {f} {x} {t} {c} Sok d with inv-seq d
... | tsA , _ , _ , eqA , iokC , rest₁ with inv-CONST iokC
... | refl , refl with inv-seq rest₁
... | tsB , _ , _ , eqB , iokS , rest₂ with inv-LOCAL-SET iokS
... | t′ , x< , lk , refl , refl = Sok′ , instrs′
  where
  tsA≡tsB : tsA ≡ tsB
  tsA≡tsB = proj₁ (∷ʳ-injective tsA tsB eqB)
  t≡t′ : t ≡ t′
  t≡t′ = proj₂ (∷ʳ-injective tsA tsB eqB)
  instrs′ : Instrs-ok C [] _ _
  instrs′ =
    coerce-instrs
      (sym (trans eqA (trans (cong (_++ []) tsA≡tsB) (inv-done rest₂))))
      refl done
  f′-locals : List val
  f′-locals = modify (frame-LOCALS f) x (λ _ → val-CONST t c)
  x<f : x < length (frame-LOCALS f)
  x<f = subst (λ n → x < n) (sym (locals-length Sok)) x<
  Sok′ : State-ok C s _
  Sok′ = record
    { locals-length  = trans (length-modify (frame-LOCALS f) x _) (locals-length Sok)
    ; locals-typing  = ltyp
    ; globals-addr   = globals-addr Sok
    ; globals-typing = globals-typing Sok
    }
    where
    ltyp : ∀ y → y < length (LOCALS C) → typeof (f′-locals [ y ]!) ≡ (LOCALS C) [ y ]!
    ltyp y y< with x ≟ y
    ... | yes refl =
      trans (cong typeof (lookup-modify-≡ (frame-LOCALS f) x _ x<f))
            (trans t≡t′ (sym lk))
    ... | no ne =
      trans (cong typeof (lookup-modify-≢ (frame-LOCALS f) x y _ ne))
            (locals-typing Sok y y<)

-- The (intended) GLOBAL-GET result value has the type the context says.
global-get-typeof : ∀ {C s f x t} →
  State-ok C s f →
  x < length (GLOBALS C) →
  (GLOBALS C) [ x ]! ≡ mk-globaltype (just MUT) t →
  typeof (global (mk-state s f) x) ≡ t
global-get-typeof Sok x< lk =
  sym (globaltype-inj (trans (sym lk) (globals-typing Sok _ x<)))

-- GLOBAL-GET preservation (arbitrary base stack).
global-get-pres : ∀ {C s f x stk ts} →
  State-ok C s f →
  Instrs-ok C (GLOBAL-GET x ∷ []) stk ts →
  Instrs-ok C (instr-val (global (mk-state s f) x) ∷ []) stk ts
global-get-pres {C} {s} {f} {x} {stk} {ts} Sok d with inv-seq d
... | tsA , _ , _ , eqA , iok , rest with inv-GLOBAL-GET iok
... | t , x< , lk , refl , refl =
  coerce-instrs (trans (sym (++-identityʳ tsA)) (sym eqA))
    (trans (cong (λ u → tsA ++ (u ∷ [])) (global-get-typeof {C} {s} {f} Sok x< lk))
           (inv-done rest))
    (value-typing (global (mk-state s f) x) tsA)

-- GLOBAL-SET preservation: mirrors LOCAL-SET, but the write goes
-- through the moduleinst address indirection into the store.  The
-- State-ok globals invariant survives the write even for ALIASED
-- context indices (two indices mapping to the same store address),
-- because the invariant already forces aliased indices to agree on
-- their type.
global-set-pres : ∀ {C s f x t c stk ts} →
  State-ok C s f →
  Instrs-ok C (CONST t c ∷ GLOBAL-SET x ∷ []) stk ts →
  State-ok C
    (record s { store-GLOBALS =
       modify (store-GLOBALS s) ((moduleinst-GLOBALS (MODULE f)) [ x ]!) (λ _ → val-CONST t c) })
    f
    × Instrs-ok C [] stk ts
global-set-pres {C} {s} {f} {x} {t} {c} Sok d with inv-seq d
... | tsA , _ , _ , eqA , iokC , rest₁ with inv-CONST iokC
... | refl , refl with inv-seq rest₁
... | tsB , _ , _ , eqB , iokS , rest₂ with inv-GLOBAL-SET iokS
... | t′ , x< , lk , refl , refl = Sok′ , instrs′
  where
  tsA≡tsB : tsA ≡ tsB
  tsA≡tsB = proj₁ (∷ʳ-injective tsA tsB eqB)
  t≡t′ : t ≡ t′
  t≡t′ = proj₂ (∷ʳ-injective tsA tsB eqB)
  instrs′ : Instrs-ok C [] _ _
  instrs′ =
    coerce-instrs
      (sym (trans eqA (trans (cong (_++ []) tsA≡tsB) (inv-done rest₂))))
      refl done
  a : addr
  a = (moduleinst-GLOBALS (MODULE f)) [ x ]!
  sG sG′ : List val
  sG  = store-GLOBALS s
  sG′ = modify sG a (λ _ → val-CONST t c)
  a<s : a < length sG
  a<s = globals-addr Sok x x<
  -- the written cell's old type is t′ (= t, the type of the new value)
  old-typeof : typeof (sG [ a ]!) ≡ t′
  old-typeof = globaltype-inj (trans (sym (globals-typing Sok x x<)) lk)
  new-cell : sG′ [ a ]! ≡ val-CONST t c
  new-cell = lookup-modify-≡ sG a (λ _ → val-CONST t c) a<s
  Sok′ : State-ok C _ f
  Sok′ = record
    { locals-length  = locals-length Sok
    ; locals-typing  = locals-typing Sok
    ; globals-addr   = λ y y< →
        subst (λ n → ((moduleinst-GLOBALS (MODULE f)) [ y ]!) < n)
              (sym (length-modify sG a (λ _ → val-CONST t c)))
              (globals-addr Sok y y<)
    ; globals-typing = gtyp
    }
    where
    gtyp : ∀ y → y < length (GLOBALS C) →
           (GLOBALS C) [ y ]! ≡
           mk-globaltype (just MUT)
             (typeof (sG′ [ (moduleinst-GLOBALS (MODULE f)) [ y ]! ]!))
    gtyp y y< with a ≟ ((moduleinst-GLOBALS (MODULE f)) [ y ]!)
    ... | yes e =
      trans (globals-typing Sok y y<)
        (cong (mk-globaltype (just MUT))
          (trans (subst (λ i → typeof (sG [ i ]!) ≡ t′) e old-typeof)
            (trans (sym t≡t′)
              (sym (cong typeof (subst (λ i → sG′ [ i ]! ≡ val-CONST t c) e new-cell))))))
    ... | no ne =
      trans (globals-typing Sok y y<)
        (cong (mk-globaltype (just MUT))
          (sym (cong typeof
            (lookup-modify-≢ sG a ((moduleinst-GLOBALS (MODULE f)) [ y ]!)
              (λ _ → val-CONST t c) ne))))

------------------------------------------------------------------------
-- 6. PRESERVATION w.r.t. the generated flat Step  (FULLY PROVED,
--    no postulate in the dependency cone)
------------------------------------------------------------------------

preservation : ∀ {c c′ ts} → Config-ok c ts → Step c c′ → Config-ok c′ ts
preservation (config-ok Sok D) (pure z _ _ Step-pure--nop) =
  config-ok Sok (nop-pres D)
preservation (config-ok Sok D) (pure z _ _ (Step-pure--drop (val-CONST t c))) =
  config-ok Sok (drop-pres D)
preservation (config-ok Sok D) (pure z _ _ (select-true (val-CONST t₁ c₁) (val-CONST t₂ c₂) c ne)) =
  config-ok Sok (proj₁ (select-pres D))
preservation (config-ok Sok D) (pure z _ _ (select-false (val-CONST t₁ c₁) (val-CONST t₂ c₂) c e)) =
  config-ok Sok (proj₂ (select-pres D))
preservation (config-ok Sok D) (Step--local-get z x v refl) =
  config-ok Sok (local-get-pres Sok D)
preservation (config-ok Sok D) (Step--local-set z (val-CONST t c) x z′ refl) =
  config-ok (proj₁ (local-set-pres Sok D)) (proj₂ (local-set-pres Sok D))
preservation (config-ok Sok D) (Step--global-get z x v refl) =
  config-ok Sok (global-get-pres Sok D)
preservation (config-ok Sok D) (Step--global-set z (val-CONST t c) x z′ refl) =
  config-ok (proj₁ (global-set-pres Sok D)) (proj₂ (global-set-pres Sok D))

------------------------------------------------------------------------
-- 7. PROGRESS w.r.t. the context closure Step-ctxt  (FULLY PROVED)
--
-- NB: progress w.r.t. the generated flat Step is FALSE (see
-- flat-progress-false below), because the NanoWasm source spec omits
-- the Step/ctxt congruence rule that full Wasm has.  Step-ctxt is
-- exactly that missing rule, written by hand above.
------------------------------------------------------------------------

-- Peel the topmost value off a value row whose stack type ends in t.
split-last : ∀ (vs : List val) (ts₀ : List valtype) (t : valtype) →
  ts₀ ++ (t ∷ []) ≡ map typeof vs →
  Σ (List val) λ vs₀ → Σ val λ v →
    (vs ≡ vs₀ ++ (v ∷ [])) × (map typeof vs₀ ≡ ts₀) × (typeof v ≡ t)
split-last [] [] t ()
split-last [] (_ ∷ _) t ()
split-last (v ∷ []) [] t eq = [] , v , refl , refl , sym (∷-injectiveˡ eq)
split-last (v ∷ w ∷ ws) [] t eq with ∷-injectiveʳ eq
... | ()
split-last (v ∷ vs) (t₀ ∷ ts₀) t eq with split-last vs ts₀ t (∷-injectiveʳ eq)
... | vs₀ , w , e₁ , e₂ , e₃ =
  (v ∷ vs₀) , w , cong (v ∷_) e₁ , cong₂ _∷_ (sym (∷-injectiveˡ eq)) e₂ , e₃

-- Wrap a flat Step into a Step-ctxt at a given decomposition.
step-here : ∀ {z z′ is₁} (vs : List val) (is₀ rest : List instr) {es : List instr} →
  es ≡ map instr-val vs ++ is₀ ++ rest →
  Step (mk-config z is₀) (mk-config z′ is₁) →
  ∃ λ c′ → Step-ctxt (mk-config z es) c′
step-here {z} {z′} {is₁} vs is₀ rest eq st =
  mk-config z′ (map instr-val vs ++ is₁ ++ rest) ,
  subst (λ l → Step-ctxt (mk-config z l) (mk-config z′ (map instr-val vs ++ is₁ ++ rest)))
        (sym eq) (ctxt vs rest st)

-- Main induction: the instruction list splits as an already-consumed
-- value prefix vs (typing the current stack) and a residue is.
progress-seq : ∀ {C s f} (vs : List val) (is : List instr) {stk ts} →
  State-ok C s f →
  Instrs-ok C is stk ts →
  stk ≡ map typeof vs →
  Values (map instr-val vs ++ is)
  ⊎ (∃ λ c′ → Step-ctxt (mk-config (mk-state s f) (map instr-val vs ++ is)) c′)
progress-seq vs _ Sok done eq =
  inj₁ (vs , ++-identityʳ (map instr-val vs))
progress-seq vs _ Sok (seq {is = is′} (nop C) rest) eq =
  inj₂ (step-here vs (NOP ∷ []) is′ refl (pure _ _ _ Step-pure--nop))
progress-seq vs _ Sok (seq {is = is′} {ts₀ = ts₀} (drop' C t) rest) eq
  with split-last vs ts₀ t eq
... | vs₀ , v , refl , _ , _ =
  inj₂ (step-here vs₀ (instr-val v ∷ DROP ∷ []) is′
          (snoc-eq vs₀ v (DROP ∷ is′))
          (pure _ _ _ (Step-pure--drop v)))
progress-seq vs _ Sok (seq {is = is′} {ts₀ = ts₀} (select C t) rest) eq
  with split-last vs (ts₀ ++ (t ∷ t ∷ [])) I32
         (trans (++-assoc ts₀ (t ∷ t ∷ []) (I32 ∷ [])) eq)
... | vs₁ , val-CONST tv c , refl , e₂ , tv≡I32
  with split-last vs₁ (ts₀ ++ (t ∷ [])) t
         (trans (++-assoc ts₀ (t ∷ []) (t ∷ [])) (sym e₂))
... | vs₂ , v₂ , refl , e₂′ , _
  with split-last vs₂ ts₀ t (sym e₂′)
... | vs₃ , v₁ , refl , _ , _ with tv≡I32
... | refl with c ≟ 0
... | yes c≡0 =
  inj₂ (step-here vs₃ (instr-val v₁ ∷ instr-val v₂ ∷ CONST I32 c ∷ SELECT ∷ []) is′
          eqES (pure _ _ _ (select-false v₁ v₂ c c≡0)))
  where
  eqES = trans (snoc-eq ((vs₃ ++ (v₁ ∷ [])) ++ (v₂ ∷ [])) (val-CONST I32 c) (SELECT ∷ is′))
         (trans (snoc-eq (vs₃ ++ (v₁ ∷ [])) v₂ (CONST I32 c ∷ SELECT ∷ is′))
                (snoc-eq vs₃ v₁ (instr-val v₂ ∷ CONST I32 c ∷ SELECT ∷ is′)))
... | no c≢0 =
  inj₂ (step-here vs₃ (instr-val v₁ ∷ instr-val v₂ ∷ CONST I32 c ∷ SELECT ∷ []) is′
          eqES (pure _ _ _ (select-true v₁ v₂ c c≢0)))
  where
  eqES = trans (snoc-eq ((vs₃ ++ (v₁ ∷ [])) ++ (v₂ ∷ [])) (val-CONST I32 c) (SELECT ∷ is′))
         (trans (snoc-eq (vs₃ ++ (v₁ ∷ [])) v₂ (CONST I32 c ∷ SELECT ∷ is′))
                (snoc-eq vs₃ v₁ (instr-val v₂ ∷ CONST I32 c ∷ SELECT ∷ is′)))
progress-seq vs _ Sok (seq {is = is′} {ts₀ = ts₀} (Instr-ok--const C t c) rest) eq
  with progress-seq (vs ++ (val-CONST t c ∷ [])) is′ Sok rest
         (trans (cong (_++ (t ∷ [])) (trans (sym (++-identityʳ ts₀)) eq))
                (sym (map-++ typeof vs (val-CONST t c ∷ []))))
... | inj₁ (ws , p) =
  inj₁ (ws , trans (sym (snoc-eq vs (val-CONST t c) is′)) p)
... | inj₂ (c′ , st) =
  inj₂ (c′ , subst (λ l → Step-ctxt (mk-config _ l) c′)
               (snoc-eq vs (val-CONST t c) is′) st)
progress-seq vs _ Sok (seq {is = is′} (local-get C x t x< lk) rest) eq =
  inj₂ (step-here vs (LOCAL-GET x ∷ []) is′ refl (Step--local-get _ x _ refl))
progress-seq vs _ Sok (seq {is = is′} {ts₀ = ts₀} (local-set C x t x< lk) rest) eq
  with split-last vs ts₀ t eq
... | vs₀ , v , refl , _ , _ =
  inj₂ (step-here vs₀ (instr-val v ∷ LOCAL-SET x ∷ []) is′
          (snoc-eq vs₀ v (LOCAL-SET x ∷ is′))
          (Step--local-set _ v x _ refl))
progress-seq vs _ Sok (seq {is = is′} (global-get C x t x< lk) rest) eq =
  inj₂ (step-here vs (GLOBAL-GET x ∷ []) is′ refl (Step--global-get _ x _ refl))
progress-seq vs _ Sok (seq {is = is′} {ts₀ = ts₀} (global-set C x t x< lk) rest) eq
  with split-last vs ts₀ t eq
... | vs₀ , v , refl , _ , _ =
  inj₂ (step-here vs₀ (instr-val v ∷ GLOBAL-SET x ∷ []) is′
          (snoc-eq vs₀ v (GLOBAL-SET x ∷ is′))
          (Step--global-set _ v x _ refl))

-- THEOREM (progress).  A well-typed configuration is a value row or
-- takes a context step.
progress-ctxt : ∀ {s f is ts} →
  Config-ok (mk-config (mk-state s f) is) ts →
  Values is ⊎ (∃ λ c′ → Step-ctxt (mk-config (mk-state s f) is) c′)
progress-ctxt (config-ok Sok D) = progress-seq [] _ Sok D refl

------------------------------------------------------------------------
-- 8. PRESERVATION w.r.t. Step-ctxt  (FULLY PROVED)
------------------------------------------------------------------------

preserve-redex : ∀ {C s f is₀ z′ is₁ stk ts} →
  State-ok C s f →
  Instrs-ok C is₀ stk ts →
  Step (mk-config (mk-state s f) is₀) (mk-config z′ is₁) →
  Σ store λ s′ → Σ frame λ f′ →
    (z′ ≡ mk-state s′ f′) × State-ok C s′ f′ × Instrs-ok C is₁ stk ts
preserve-redex Sok D (pure _ _ _ Step-pure--nop) =
  _ , _ , refl , Sok , nop-pres D
preserve-redex Sok D (pure _ _ _ (Step-pure--drop (val-CONST t c))) =
  _ , _ , refl , Sok , drop-pres D
preserve-redex Sok D (pure _ _ _ (select-true (val-CONST t₁ c₁) (val-CONST t₂ c₂) c ne)) =
  _ , _ , refl , Sok , proj₁ (select-pres D)
preserve-redex Sok D (pure _ _ _ (select-false (val-CONST t₁ c₁) (val-CONST t₂ c₂) c e)) =
  _ , _ , refl , Sok , proj₂ (select-pres D)
preserve-redex Sok D (Step--local-get _ x v refl) =
  _ , _ , refl , Sok , local-get-pres Sok D
preserve-redex Sok D (Step--local-set _ (val-CONST t c) x z′ refl) =
  _ , _ , refl , proj₁ (local-set-pres Sok D) , proj₂ (local-set-pres Sok D)
preserve-redex Sok D (Step--global-get _ x v refl) =
  _ , _ , refl , Sok , global-get-pres Sok D
preserve-redex Sok D (Step--global-set _ (val-CONST t c) x z′ refl) =
  _ , _ , refl , proj₁ (global-set-pres Sok D) , proj₂ (global-set-pres Sok D)

preservation-ctxt : ∀ {c c′ ts} → Config-ok c ts → Step-ctxt c c′ → Config-ok c′ ts
preservation-ctxt (config-ok Sok D) (ctxt {is₀ = is₀} vs rest st)
  with instrs-ok-split (map instr-val vs) D
... | tsv , Dvals , Drest₁ with instrs-ok-split is₀ Drest₁
... | tsm , Dredex , Drest with preserve-redex Sok Dredex st
... | s′ , f′ , refl , Sok′ , Dredex′ =
  config-ok Sok′ (instrs-ok-++ Dvals (instrs-ok-++ Dredex′ Drest))

------------------------------------------------------------------------
-- 9. Machine-checked demonstration that the remaining gap is a SPEC
--    omission, not a proof gap
------------------------------------------------------------------------

-- A concrete well-typed setup: one MUT I32 global at address 0
-- holding (CONST I32 7); no locals.
C₀ : context
C₀ = mk-context (mk-globaltype (just MUT) I32 ∷ []) []

s₀ : store
s₀ = mk-store (val-CONST I32 7 ∷ [])

f₀ : frame
f₀ = mk-frame [] (mk-moduleinst (0 ∷ []))

z₀ : state
z₀ = mk-state s₀ f₀

state-ok₀ : State-ok C₀ s₀ f₀
state-ok₀ = record
  { locals-length  = refl
  ; locals-typing  = λ x ()
  ; globals-addr   = λ { zero _ → s≤s z≤n ; (suc x) (s≤s ()) }
  ; globals-typing = λ { zero _ → refl ; (suc x) (s≤s ()) }
  }

-- (a) The generated flat Step has NO congruence rule (the source spec
--     omits Step/ctxt), so flat progress is FALSE: [NOP, NOP] is
--     well-typed yet stuck.
nop-nop-ok : Config-ok (mk-config z₀ (NOP ∷ NOP ∷ [])) []
nop-nop-ok = config-ok state-ok₀
  (seq {ts₀ = []} (nop C₀) (seq {ts₀ = []} (nop C₀) done))

nop-nop-stuck : ∀ {c′} → ¬ Step (mk-config z₀ (NOP ∷ NOP ∷ [])) c′
nop-nop-stuck (pure _ _ _ ())

flat-progress-false :
  ¬ (∀ {z is ts} → Config-ok (mk-config z is) ts →
       Values is ⊎ (∃ λ c′ → Step (mk-config z is) c′))
flat-progress-false hyp with hyp nop-nop-ok
... | inj₁ ([] , ())
... | inj₁ (val-CONST _ _ ∷ _ , ())
... | inj₂ (c′ , st) = nop-nop-stuck st

-- (b) HISTORICAL NOTE.  An earlier version of the source spec had a
--     typo in rule Instr_ok/global.set: its conclusion read
--
--         C |- GLOBAL.GET x : t -> eps
--
--     (GLOBAL.GET instead of GLOBAL.SET).  Against that spec, this
--     file additionally proved:
--       * GLOBAL.SET was typed by NO rule at all;
--       * GLOBAL.GET received a second, CONSUMING type t -> eps, which
--         made preservation w.r.t. Step-ctxt PROVABLY FALSE
--         (witness: z₀ ; (CONST I32 0)(GLOBAL.GET 0) : eps -> eps
--         context-stepped to z₀ ; (CONST I32 0)(CONST I32 7), which
--         cannot type at eps -> eps), so that case was isolated in a
--         postulate.
--     The spec has since been fixed and nanowasm-check.agda
--     regenerated; the postulate and the counterexample are gone, and
--     preservation-ctxt above is proved outright.
