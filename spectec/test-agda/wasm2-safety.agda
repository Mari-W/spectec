------------------------------------------------------------------------
-- wasm2-safety.agda
--
-- ATTEMPT #2: type safety (preservation + progress) for the
-- machine-generated WebAssembly 2.0 spec, THIS TIME against the
-- GENERATED runtime typing of wasm2-sound-check.agda (soundness
-- appendix translated: Config-ok / State-ok / Frame-ok / Store-ok /
-- Instr-ok2 / Instrs-ok2 / Expr-ok2 / Ref-ok / Val-ok / Extend-store).
--
-- Headline statements (generated relations only):
--   preservation : Config-ok c rt -> Step c c' -> Config-ok c' rt
--                  (plus Extend-store s s')
--   ProgressStmt : Config-ok c rt -> Terminal c or exists c'. Step c c'
--
-- DELTA vs attempt #1 (SafetyExperiment.agda):
--   B1 GONE: no hand-rolled runtime typing; everything below uses the
--     generated relations.
--   B5 GONE: Forall/Forall2 are All/Pointwise; the subtyping lemmas
--     that were POSTULATED in attempt #1 (Resulttype-sub-trans,
--     Resulttype-sub-++) are PROVED here, as are the sequence-typing
--     decomposition and singleton-inversion lemmas that were the
--     declared blockers of attempt #1 (Section 3.3 / Section 5 there).
--   B2 GONE (after regeneration): dimension premises now cover
--     iterations inside equation premises too; Step-read--block/loop/
--     call-addr tie |val*| = k = |t_1*| and |t_2*| = n, and LABEL-/
--     FRAME- typing rules tie their arity to the label/result type.
--     The under-capture counterexample is dead (section 11) and
--     preservation for block/loop is PROVED here.
--   LIMITS-SUB GONE (after regeneration): `Limits-sub` gained `.max`
--     (bounded) and `.eps` (unbounded) rules, so store-extension
--     weakening `instrs-weaken` is now PROVED end-to-end (mem/table
--     externaddr monotonicity was the last blocker).  pres-pure is
--     TOTAL (all 104 Step-pure rules).  pres-read is TOTAL (all 50
--     Step-read rules, incl. the load/fill/copy/init decompositions).
--     PRESERVATION IS COMPLETE.
--   PROGRESS: progress-decompose is now PROVED (no longer a postulate)
--     from `value-split` (value-row decomposition) + `wrap-step`
--     (the ctxt-instrs sequence congruence) + `progress-nonval`.  The
--     theorem is stated for closed configs (input resulttype []), which
--     is how `progress` uses it (an expr is [] -> t).  progress-nonval
--     is proved for the no-operand heads (nop, unreachable, bare trap);
--     the remaining per-instruction reduction-firing (operand-consuming
--     heads) is scaffolded by the single postulate `progress-rest` and
--     is the last open obligation.  NO generated-relation gap left.
--   B3/B4 still present, worked around: _++_-indexed sequence typing is
--     handled by proved decomposition lemmas; the TERMINATING syntax
--     injections (admininstr-instr, admininstr-val, admininstr-ref) are
--     inverted via a once-and-for-all partial inverse (instr-of) and
--     its roundtrip lemma.
------------------------------------------------------------------------

{-# OPTIONS -WnoUnreachableClauses #-}
module wasm2-safety where

-- needs local unpushed fixes to the wasm 2.0 spec, see spec-local-fixes.patch
--   6-typing, Limits_sub allows an unbounded max
--   8-reduction, store-val rules require the access in-bounds
--   B-soundness, frame typing carries RETURN [t*]

open import Data.Nat using (ℕ; zero; suc; _+_; _<_; _>_; _≤_; z≤n; s≤s; _≟_; _^_; _*_)
open import Data.Nat using (_∸_; _⊓_) renaming (_<?_ to _<?ⁿ_; _≤?_ to _≤?ⁿ_)
open import Data.Nat.Properties using (≤-refl; ≤-reflexive; ≤-trans; suc-injective; +-cancelʳ-≡; +-comm; +-assoc; m≤m+n; m≤n⇒m⊓n≡m; m+[n∸m]≡n; +-monoʳ-≤; ≮⇒≥; ≰⇒>; m+n∸m≡n; ∸-monoˡ-≤; +-suc; +-identityʳ; *-assoc; *-mono-≤; *-comm; *-distribʳ-+; +-mono-≤; n≮0; m≤n+m; m∸[m∸n]≡n)
open import Data.Nat.DivMod using (m/n≤m; m/n*n≤m; m*n/n≡m; /-monoˡ-≤)
open import Relation.Nullary using (yes; no; Dec)
open import Data.List using (List; []; _∷_; _++_; map; length; applyUpTo; upTo; take; drop; replicate)
open import Data.List.Properties using (++-assoc; ++-identityʳ; ++-conicalˡ; ++-conicalʳ; ∷-injective; map-++; length-++; length-map; length-take; length-drop; length-replicate; take++drop≡id)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂; subst; subst₂; _≢_)
  renaming (trans to tr≡)
open import Induction.WellFounded using (Acc) renaming (acc to acc-wf)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.List.Relation.Unary.All using (All; []; _∷_; universal; tabulate) renaming (all? to all-dec?)
open import Data.List.Membership.Propositional.Properties using (∈-upTo⁻)
open import Data.List.Relation.Unary.All.Properties using (map⁺; ++⁺; replicate⁺)
open import Data.List.Properties using (≡-dec)
open import Relation.Nullary.Decidable using () renaming (¬? to ¬-dec?)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_)
open import Function using (case_of_)

open import wasm2-sound-check

open context
open store
open frame
open moduleinst
open globalinst
open funcinst
open meminst
open tableinst
open datainst
open eleminst
open memarg
open Coerce {{...}}

------------------------------------------------------------------------
-- 0. Small general-purpose lemmas
------------------------------------------------------------------------

just-inj : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
just-inj refl = refl

maybe-just : ∀ {A : Set} {{_ : Inhabited A}} {v : A} (m : Maybe A) →
  m ≢ nothing → unwrap! m ≡ v → m ≡ just v
maybe-just (just x) ne eq = cong just eq
maybe-just nothing ne eq = ⊥-elim (ne refl)

singleton-++ : ∀ {A : Set} (xs ys : List A) {e : A} →
  xs ++ ys ≡ e ∷ [] →
  (xs ≡ [] × ys ≡ e ∷ []) ⊎ (xs ≡ e ∷ [] × ys ≡ [])
singleton-++ [] ys eq = inj₁ (refl , eq)
singleton-++ (x ∷ xs) ys eq with ∷-injective eq
... | eqh , eqt =
  inj₂ ( cong₂ _∷_ eqh (++-conicalˡ xs ys eqt)
       , ++-conicalʳ xs ys eqt )

-- Where does a split point of xs ++ ys fall relative to l1 ++ l2?
data SplitCase {A : Set} (l1 l2 xs ys : List A) : Set where
  on-right : ∀ zs → xs ≡ l1 ++ zs → l2 ≡ zs ++ ys → SplitCase l1 l2 xs ys
  on-left  : ∀ zs → l1 ≡ xs ++ zs → ys ≡ zs ++ l2 → SplitCase l1 l2 xs ys

append-cases : ∀ {A : Set} (l1 l2 xs ys : List A) →
  l1 ++ l2 ≡ xs ++ ys → SplitCase l1 l2 xs ys
append-cases [] l2 xs ys eq = on-right xs refl eq
append-cases (a ∷ l1) l2 [] ys eq = on-left (a ∷ l1) refl (sym eq)
append-cases (a ∷ l1) l2 (b ∷ xs) ys eq with ∷-injective eq
... | eqh , eqt with append-cases l1 l2 xs ys eqt
... | on-right zs p q = on-right zs (cong₂ _∷_ (sym eqh) p) q
... | on-left  zs p q = on-left  zs (cong₂ _∷_ eqh p) q

modify-length : ∀ {A : Set} (xs : List A) (i : ℕ) (f : A → A) →
  length (modify xs i f) ≡ length xs
modify-length [] i f = refl
modify-length (x ∷ xs) zero f = refl
modify-length (x ∷ xs) (suc i) f = cong suc (modify-length xs i f)

all-applyUpTo : ∀ {A : Set} {P : A → Set} (f : ℕ → A) (m : ℕ) →
  (∀ i → i < m → P (f i)) → All P (applyUpTo f m)
all-applyUpTo f zero h = []
all-applyUpTo f (suc m) h =
  h 0 (s≤s z≤n) ∷ all-applyUpTo (λ i → f (suc i)) m (λ i i< → h (suc i) (s≤s i<))

all-upto : ∀ {P : ℕ → Set} (m : ℕ) → (∀ i → i < m → P i) → holds-upto P m
all-upto m h = all-applyUpTo (λ i → i) m h

------------------------------------------------------------------------
-- 1. Pointwise (Forall₂) toolkit -- B5 payoff: all of this is provable
--    now that Forall₂ is the inductive Pointwise.
------------------------------------------------------------------------

pw-length : ∀ {A B : Set} {R : A → B → Set} {xs ys} →
  Pointwise R xs ys → length xs ≡ length ys
pw-length [] = refl
pw-length (r ∷ p) = cong suc (pw-length p)

pw-refl : ∀ {A : Set} {R : A → A → Set} → (∀ x → R x x) →
  ∀ xs → Pointwise R xs xs
pw-refl h [] = []
pw-refl h (x ∷ xs) = h x ∷ pw-refl h xs

pw-trans : ∀ {A : Set} {R : A → A → Set} →
  (∀ {x y z} → R x y → R y z → R x z) →
  ∀ {xs ys zs} → Pointwise R xs ys → Pointwise R ys zs → Pointwise R xs zs
pw-trans tr [] [] = []
pw-trans tr (r ∷ p) (r' ∷ p') = tr r r' ∷ pw-trans tr p p'

pw-app : ∀ {A B : Set} {R : A → B → Set} {xs ys as bs} →
  Pointwise R xs ys → Pointwise R as bs → Pointwise R (xs ++ as) (ys ++ bs)
pw-app [] q = q
pw-app (r ∷ p) q = r ∷ pw-app p q

pw-nilˡ : ∀ {A B : Set} {R : A → B → Set} {ys} → Pointwise R [] ys → ys ≡ []
pw-nilˡ [] = refl

pw-nilʳ : ∀ {A B : Set} {R : A → B → Set} {xs} → Pointwise R xs [] → xs ≡ []
pw-nilʳ [] = refl

pw-unsnoc : ∀ {A B : Set} {R : A → B → Set} (xs : List A) (ys : List B) {x y} →
  Pointwise R (xs ++ x ∷ []) (ys ++ y ∷ []) → Pointwise R xs ys × R x y
pw-unsnoc [] [] (r ∷ []) = [] , r
pw-unsnoc [] (y' ∷ ys) (r ∷ p) =
  case ++-conicalʳ ys _ (pw-nilˡ p) of λ ()
pw-unsnoc (x' ∷ xs) [] (r ∷ p) =
  case ++-conicalʳ xs _ (pw-nilʳ p) of λ ()
pw-unsnoc (x' ∷ xs) (y' ∷ ys) (r ∷ p) with pw-unsnoc xs ys p
... | q , ry = (r ∷ q) , ry

pw-lookup : ∀ {A B : Set} {{_ : Inhabited A}} {{_ : Inhabited B}}
  {R : A → B → Set} {xs ys} →
  Pointwise R xs ys → ∀ {i} → i < length xs → R (xs [ i ]!) (ys [ i ]!)
pw-lookup (r ∷ p) {zero} _ = r
pw-lookup (r ∷ p) {suc i} (s≤s i<) = pw-lookup p i<

pw-update : ∀ {A B : Set} {{_ : Inhabited A}} {R : A → B → Set} {ts vs} →
  Pointwise R ts vs → ∀ i (v : B) → R (ts [ i ]!) v →
  Pointwise R ts (modify vs i (λ _ → v))
pw-update [] i v r = []
pw-update (r0 ∷ p) zero v r = r ∷ p
pw-update (r0 ∷ p) (suc i) v r = r0 ∷ pw-update p i v r

all-lookup : ∀ {A : Set} {{_ : Inhabited A}} {P : A → Set} {xs} →
  All P xs → ∀ {i} → i < length xs → P (xs [ i ]!)
all-lookup (px ∷ p) {zero} _ = px
all-lookup (px ∷ p) {suc i} (s≤s i<) = all-lookup p i<

-- Split the left list of a pointwise relation along a split of the right.
pw-take-drop : ∀ {A B : Set} {R : A → B → Set} (c : List B) {d} {xs : List A} →
  Pointwise R xs (c ++ d) →
  Σ (List A × List A) λ (x1 , x2) →
    (xs ≡ x1 ++ x2) × Pointwise R x1 c × Pointwise R x2 d
pw-take-drop [] pw = ([] , _) , refl , [] , pw
pw-take-drop (y ∷ c) (r ∷ pw) with pw-take-drop c pw
... | (x1 , x2) , refl , p1 , p2 = ((_ ∷ x1) , x2) , refl , (r ∷ p1) , p2

rt-eta : ∀ (r : resulttype) → mk-list (proj-list-0 valtype r) ≡ r
rt-eta (mk-list v) = refl

------------------------------------------------------------------------
-- 2. Subtyping toolkit.  In attempt #1, rt-sub-trans and rt-sub-app
--    had to be POSTULATED; both are now proved.
------------------------------------------------------------------------

vt-sub-trans : ∀ {a b c} → Valtype-sub a b → Valtype-sub b c → Valtype-sub a c
vt-sub-trans (refl' _) s = s
vt-sub-trans (bot _) s = bot _

rt-sub-refl : ∀ ts → Resulttype-sub (mk-list ts) (mk-list ts)
rt-sub-refl ts = mk-Resulttype-sub ts ts refl (pw-refl refl' ts)

rt-sub-trans : ∀ {a b c} →
  Resulttype-sub (mk-list a) (mk-list b) →
  Resulttype-sub (mk-list b) (mk-list c) →
  Resulttype-sub (mk-list a) (mk-list c)
rt-sub-trans (mk-Resulttype-sub _ _ l1 p1) (mk-Resulttype-sub _ _ l2 p2) =
  mk-Resulttype-sub _ _ (tr≡ l1 l2) (pw-trans vt-sub-trans p1 p2)

rt-sub-app : ∀ {a b c d} →
  Resulttype-sub (mk-list a) (mk-list b) →
  Resulttype-sub (mk-list c) (mk-list d) →
  Resulttype-sub (mk-list (a ++ c)) (mk-list (b ++ d))
rt-sub-app (mk-Resulttype-sub a b l1 p1) (mk-Resulttype-sub c d l2 p2) =
  mk-Resulttype-sub _ _ (pw-length (pw-app p1 p2)) (pw-app p1 p2)

rt-sub-unsnoc : ∀ {xs ys x y} →
  Resulttype-sub (mk-list (xs ++ x ∷ [])) (mk-list (ys ++ y ∷ [])) →
  Resulttype-sub (mk-list xs) (mk-list ys) × Valtype-sub x y
rt-sub-unsnoc {xs} {ys} (mk-Resulttype-sub _ _ _ pw) with pw-unsnoc xs ys pw
... | q , r = mk-Resulttype-sub _ _ (pw-length q) q , r

rt-sub-pw : ∀ {a b} → Resulttype-sub (mk-list a) (mk-list b) →
  Pointwise Valtype-sub a b
rt-sub-pw (mk-Resulttype-sub _ _ _ pw) = pw

pw-split : ∀ {A B : Set} {R : A → B → Set} (a : List A) (c : List B) {b d} →
  Pointwise R (a ++ b) (c ++ d) → length a ≡ length c →
  Pointwise R a c × Pointwise R b d
pw-split [] [] pw _ = [] , pw
pw-split [] (y ∷ c) pw ()
pw-split (x ∷ a) [] pw ()
pw-split (x ∷ a) (y ∷ c) (r ∷ pw) leq with pw-split a c pw (suc-injective leq)
... | p1 , p2 = (r ∷ p1) , p2

-- split a subtyping over ++, given equal SUFFIX lengths
rt-sub-split : ∀ {a c b d : List valtype} →
  Resulttype-sub (mk-list (a ++ b)) (mk-list (c ++ d)) →
  length b ≡ length d →
  Resulttype-sub (mk-list a) (mk-list c) × Resulttype-sub (mk-list b) (mk-list d)
rt-sub-split {a} {c} {b} {d} (mk-Resulttype-sub _ _ leq pw) sufeq =
  let toteq2 = subst (λ x → length a + length b ≡ length c + x) (sym sufeq)
                 (tr≡ (sym (length-++ a)) (tr≡ leq (length-++ c)))
      ps = pw-split a c pw (+-cancelʳ-≡ (length b) (length a) (length c) toteq2)
  in mk-Resulttype-sub _ _ (pw-length (proj₁ ps)) (proj₁ ps) ,
     mk-Resulttype-sub _ _ (pw-length (proj₂ ps)) (proj₂ ps)

-- normalize p ++ [] on either side
rt-norm : ∀ {a} p → Resulttype-sub (mk-list a) (mk-list (p ++ [])) →
  Resulttype-sub (mk-list a) (mk-list p)
rt-norm {a} p x =
  subst (λ l → Resulttype-sub (mk-list a) (mk-list l)) (++-identityʳ p) x

rt-norml : ∀ p {b} → Resulttype-sub (mk-list (p ++ [])) (mk-list b) →
  Resulttype-sub (mk-list p) (mk-list b)
rt-norml p {b} x =
  subst (λ l → Resulttype-sub (mk-list l) (mk-list b)) (++-identityʳ p) x

unnorm : ∀ {a} p → Resulttype-sub (mk-list a) (mk-list p) →
  Resulttype-sub (mk-list a) (mk-list (p ++ []))
unnorm {a} p x =
  subst (λ l → Resulttype-sub (mk-list a) (mk-list l)) (sym (++-identityʳ p)) x

snoc2 : ∀ {A : Set} (p : List A) (a b : A) →
  (p ++ a ∷ []) ++ b ∷ [] ≡ p ++ a ∷ b ∷ []
snoc2 p a b = ++-assoc p (a ∷ []) (b ∷ [])

snoc3 : ∀ {A : Set} (p : List A) (a b c : A) →
  ((p ++ a ∷ []) ++ b ∷ []) ++ c ∷ [] ≡ p ++ a ∷ b ∷ c ∷ []
snoc3 p a b c =
  tr≡ (cong (_++ c ∷ []) (snoc2 p a b)) (++-assoc p (a ∷ b ∷ []) (c ∷ []))

------------------------------------------------------------------------
-- 3. Sequence-typing toolkit for the generated Instrs-ok2.
--    These are exactly the lemmas attempt #1 declared unprovable-there
--    ("composition typing", Watt CPP'18 Lemma 1): decomposition of a
--    typed sequence at any split point, inversion of the empty
--    sequence, and inversion of singletons down to Instr-ok2 modulo a
--    single frame + a single subsumption.
------------------------------------------------------------------------

empty-ty : ∀ {s C} (t : List valtype) →
  Instrs-ok2 s C [] (mk-functype (mk-list t) (mk-list t))
empty-ty {s} {C} t =
  subst (λ l → Instrs-ok2 s C [] (mk-functype (mk-list l) (mk-list l)))
        (++-identityʳ t)
        (Instrs-ok2--frame _ _ [] t [] [] (Instrs-ok2--empty _ _))

empty-inv : ∀ {s C es u1 u2} →
  Instrs-ok2 s C es (mk-functype (mk-list u1) (mk-list u2)) →
  es ≡ [] → Resulttype-sub (mk-list u1) (mk-list u2)
empty-inv (Instrs-ok2--empty _ _) _ = rt-sub-refl []
empty-inv (Instrs-ok2--instr _ _ _ _ _ _) ()
empty-inv (Instrs-ok2--seq _ _ l1 l2 _ _ _ d1 d2) eq
  with ++-conicalˡ l1 l2 eq | ++-conicalʳ l1 l2 eq
... | refl | refl = rt-sub-trans (empty-inv d1 refl) (empty-inv d2 refl)
empty-inv (Instrs-ok2--sub _ _ _ _ _ _ _ d r1 r2) eq =
  rt-sub-trans r1 (rt-sub-trans (empty-inv d eq) r2)
empty-inv (Instrs-ok2--frame _ _ _ ts _ _ d) eq =
  rt-sub-app (rt-sub-refl ts) (empty-inv d eq)

sub-empty : ∀ {s C u1 u2} →
  Resulttype-sub (mk-list u1) (mk-list u2) →
  Instrs-ok2 s C [] (mk-functype (mk-list u1) (mk-list u2))
sub-empty {u2 = u2} r =
  Instrs-ok2--sub _ _ _ _ _ _ _ (empty-ty u2) r (rt-sub-refl u2)

record Split (s : store) (C : context) (xs ys : List admininstr)
             (u1 u3 : List valtype) : Set where
  constructor mk-split
  field
    mid : List valtype
    okL : Instrs-ok2 s C xs (mk-functype (mk-list u1) (mk-list mid))
    okR : Instrs-ok2 s C ys (mk-functype (mk-list mid) (mk-list u3))

decomp : ∀ {s C es u1 u3} →
  Instrs-ok2 s C es (mk-functype (mk-list u1) (mk-list u3)) →
  (xs ys : List admininstr) → es ≡ xs ++ ys → Split s C xs ys u1 u3
decomp (Instrs-ok2--empty _ _) xs ys eq
  with ++-conicalˡ xs ys (sym eq) | ++-conicalʳ xs ys (sym eq)
... | refl | refl =
  mk-split [] (Instrs-ok2--empty _ _) (Instrs-ok2--empty _ _)
decomp (Instrs-ok2--instr _ _ e t1 t2 d) xs ys eq
  with singleton-++ xs ys (sym eq)
... | inj₁ (refl , refl) =
  mk-split t1 (empty-ty t1) (Instrs-ok2--instr _ _ e t1 t2 d)
... | inj₂ (refl , refl) =
  mk-split t2 (Instrs-ok2--instr _ _ e t1 t2 d) (empty-ty t2)
decomp {s} {C} (Instrs-ok2--seq _ _ l1 l2 tA tC tB d1 d2) xs ys eq
  with append-cases l1 l2 xs ys eq
... | on-right zs xseq l2eq with decomp d2 zs ys l2eq
...   | mk-split w okZ okY =
        mk-split w
          (subst (λ l → Instrs-ok2 s C l (mk-functype (mk-list tA) (mk-list w)))
                 (sym xseq)
                 (Instrs-ok2--seq _ _ l1 zs _ _ _ d1 okZ))
          okY
decomp {s} {C} (Instrs-ok2--seq _ _ l1 l2 tA tC tB d1 d2) xs ys eq
    | on-left zs l1eq yseq with decomp d1 xs zs l1eq
...   | mk-split w okX okZ =
        mk-split w okX
          (subst (λ l → Instrs-ok2 s C l (mk-functype (mk-list w) (mk-list tC)))
                 (sym yseq)
                 (Instrs-ok2--seq _ _ zs l2 _ _ _ okZ d2))
decomp (Instrs-ok2--sub _ _ _ _ _ _ _ d r1 r2) xs ys eq
  with decomp d xs ys eq
... | mk-split w okX okY =
  mk-split w
    (Instrs-ok2--sub _ _ _ _ _ _ _ okX r1 (rt-sub-refl w))
    (Instrs-ok2--sub _ _ _ _ _ _ _ okY (rt-sub-refl w) r2)
decomp (Instrs-ok2--frame _ _ _ ts t1 t2 d) xs ys eq
  with decomp d xs ys eq
... | mk-split w okX okY =
  mk-split (ts ++ w)
    (Instrs-ok2--frame _ _ _ ts _ _ okX)
    (Instrs-ok2--frame _ _ _ ts _ _ okY)

-- Singleton inversion: any typed singleton is one Instr-ok2 under one
-- stack frame and one subsumption.
record SingleTy (s : store) (C : context) (e : admininstr)
                (u1 u2 : List valtype) : Set where
  constructor mk-single
  field
    pre  : List valtype
    dom  : List valtype
    cod  : List valtype
    e-ok : Instr-ok2 s C e (mk-functype (mk-list dom) (mk-list cod))
    sub1 : Resulttype-sub (mk-list u1) (mk-list (pre ++ dom))
    sub2 : Resulttype-sub (mk-list (pre ++ cod)) (mk-list u2)

singleton-inv' : ∀ {s C es u1 u2 e} →
  Instrs-ok2 s C es (mk-functype (mk-list u1) (mk-list u2)) →
  es ≡ e ∷ [] → SingleTy s C e u1 u2
singleton-inv' (Instrs-ok2--empty _ _) ()
singleton-inv' (Instrs-ok2--instr _ _ e' t1 t2 d) refl =
  mk-single [] t1 t2 d (rt-sub-refl t1) (rt-sub-refl t2)
singleton-inv' (Instrs-ok2--seq _ _ l1 l2 tA tC tB d1 d2) eq
  with singleton-++ l1 l2 eq
... | inj₁ (refl , refl) with singleton-inv' d2 refl
...   | mk-single p dm c eok s1 s2 =
        mk-single p dm c eok (rt-sub-trans (empty-inv d1 refl) s1) s2
singleton-inv' (Instrs-ok2--seq _ _ l1 l2 tA tC tB d1 d2) eq
    | inj₂ (refl , refl) with singleton-inv' d1 refl
...   | mk-single p dm c eok s1 s2 =
        mk-single p dm c eok s1 (rt-sub-trans s2 (empty-inv d2 refl))
singleton-inv' (Instrs-ok2--sub _ _ _ _ _ _ _ d r1 r2) eq
  with singleton-inv' d eq
... | mk-single p dm c eok s1 s2 =
  mk-single p dm c eok (rt-sub-trans r1 s1) (rt-sub-trans s2 r2)
singleton-inv' {u1 = u1} {u2 = u2} (Instrs-ok2--frame _ _ _ ts t1 t2 d) eq
  with singleton-inv' d eq
... | mk-single p dm c eok s1 s2 =
  mk-single (ts ++ p) dm c eok
    (subst (λ l → Resulttype-sub (mk-list (ts ++ t1)) (mk-list l))
           (sym (++-assoc ts p dm)) (rt-sub-app (rt-sub-refl ts) s1))
    (subst (λ l → Resulttype-sub (mk-list l) (mk-list (ts ++ t2)))
           (sym (++-assoc ts p c)) (rt-sub-app (rt-sub-refl ts) s2))

singleton-inv : ∀ {s C e u1 u2} →
  Instrs-ok2 s C (e ∷ []) (mk-functype (mk-list u1) (mk-list u2)) →
  SingleTy s C e u1 u2
singleton-inv ok = singleton-inv' ok refl

single-intro : ∀ {s C e u1 u2} → SingleTy s C e u1 u2 →
  Instrs-ok2 s C (e ∷ []) (mk-functype (mk-list u1) (mk-list u2))
single-intro (mk-single p dm c eok s1 s2) =
  Instrs-ok2--sub _ _ _ _ _ _ _
    (Instrs-ok2--frame _ _ _ p _ _ (Instrs-ok2--instr _ _ _ _ _ eok))
    s1 s2

-- Re-embed an instruction of type [] -> [t] at any ambient type.
push1 : ∀ {s C e t u1 u2} (p : List valtype) →
  Instr-ok2 s C e (mk-functype (mk-list []) (mk-list (t ∷ []))) →
  Resulttype-sub (mk-list u1) (mk-list p) →
  Resulttype-sub (mk-list (p ++ t ∷ [])) (mk-list u2) →
  Instrs-ok2 s C (e ∷ []) (mk-functype (mk-list u1) (mk-list u2))
push1 {t = t} {u1 = u1} {u2 = u2} p eok s1 s2 =
  single-intro (mk-single p [] (t ∷ []) eok
    (subst (λ l → Resulttype-sub (mk-list u1) (mk-list l))
           (sym (++-identityʳ p)) s1)
    s2)

trap-ty : ∀ {s C u1 u2} →
  Instrs-ok2 s C (admininstr-TRAP ∷ []) (mk-functype (mk-list u1) (mk-list u2))
trap-ty {u1 = u1} {u2 = u2} =
  Instrs-ok2--instr _ _ _ _ _ (Instr-ok2--trap _ _ u1 u2)

-- Re-embed a whole sequence of type [] -> c at any ambient type.
push* : ∀ {s C es c u1 u2} (p : List valtype) →
  Instrs-ok2 s C es (mk-functype (mk-list []) (mk-list c)) →
  Resulttype-sub (mk-list u1) (mk-list p) →
  Resulttype-sub (mk-list (p ++ c)) (mk-list u2) →
  Instrs-ok2 s C es (mk-functype (mk-list u1) (mk-list u2))
push* {s} {C} {es} {c} p d s1 s2 =
  Instrs-ok2--sub _ _ _ _ _ _ _
    (subst (λ l → Instrs-ok2 s C es (mk-functype (mk-list l) (mk-list (p ++ c))))
           (++-identityʳ p)
           (Instrs-ok2--frame _ _ _ p _ _ d))
    s1 s2

------------------------------------------------------------------------
-- 4. Inverting the TERMINATING syntax injection admininstr-instr (B4
--    workaround).  One partial inverse + one roundtrip lemma serve all
--    instruction classes: from  admininstr-instr i == <admin ctor args>
--    we recover i (or refute) by congruence with instr-of.
------------------------------------------------------------------------

instr-of : admininstr → Maybe instr
instr-of admininstr-NOP = just NOP
instr-of admininstr-UNREACHABLE = just UNREACHABLE
instr-of admininstr-DROP = just DROP
instr-of (admininstr-SELECT x0) = just (SELECT x0)
instr-of (admininstr-BLOCK x0 x1) = just (BLOCK x0 x1)
instr-of (admininstr-LOOP x0 x1) = just (LOOP x0 x1)
instr-of (admininstr-IFELSE x0 x1 x2) = just (IFELSE x0 x1 x2)
instr-of (admininstr-BR x0) = just (BR x0)
instr-of (admininstr-BR-IF x0) = just (BR-IF x0)
instr-of (admininstr-BR-TABLE x0 x1) = just (BR-TABLE x0 x1)
instr-of (admininstr-CALL x0) = just (CALL x0)
instr-of (admininstr-CALL-INDIRECT x0 x1) = just (CALL-INDIRECT x0 x1)
instr-of admininstr-RETURN = just RETURN
instr-of (admininstr-CONST x0 x1) = just (CONST x0 x1)
instr-of (admininstr-UNOP x0 x1) = just (UNOP x0 x1)
instr-of (admininstr-BINOP x0 x1) = just (BINOP x0 x1)
instr-of (admininstr-TESTOP x0 x1) = just (TESTOP x0 x1)
instr-of (admininstr-RELOP x0 x1) = just (RELOP x0 x1)
instr-of (admininstr-CVTOP x0 x1 x2) = just (CVTOP x0 x1 x2)
instr-of (admininstr-EXTEND x0 x1) = just (instr-EXTEND x0 x1)
instr-of (admininstr-VCONST x0 x1) = just (VCONST x0 x1)
instr-of (admininstr-VVUNOP x0 x1) = just (VVUNOP x0 x1)
instr-of (admininstr-VVBINOP x0 x1) = just (VVBINOP x0 x1)
instr-of (admininstr-VVTERNOP x0 x1) = just (VVTERNOP x0 x1)
instr-of (admininstr-VVTESTOP x0 x1) = just (VVTESTOP x0 x1)
instr-of (admininstr-VUNOP x0 x1) = just (VUNOP x0 x1)
instr-of (admininstr-VBINOP x0 x1) = just (VBINOP x0 x1)
instr-of (admininstr-VTESTOP x0 x1) = just (VTESTOP x0 x1)
instr-of (admininstr-VRELOP x0 x1) = just (VRELOP x0 x1)
instr-of (admininstr-VSHIFTOP x0 x1) = just (VSHIFTOP x0 x1)
instr-of (admininstr-VBITMASK x0) = just (VBITMASK x0)
instr-of (admininstr-VSWIZZLE x0) = just (VSWIZZLE x0)
instr-of (admininstr-VSHUFFLE x0 x1) = just (VSHUFFLE x0 x1)
instr-of (admininstr-VSPLAT x0) = just (VSPLAT x0)
instr-of (admininstr-VEXTRACT-LANE x0 x1 x2) = just (VEXTRACT-LANE x0 x1 x2)
instr-of (admininstr-VREPLACE-LANE x0 x1) = just (VREPLACE-LANE x0 x1)
instr-of (admininstr-VEXTUNOP x0 x1 x2) = just (VEXTUNOP x0 x1 x2)
instr-of (admininstr-VEXTBINOP x0 x1 x2) = just (VEXTBINOP x0 x1 x2)
instr-of (admininstr-VNARROW x0 x1 x2) = just (VNARROW x0 x1 x2)
instr-of (admininstr-VCVTOP x0 x1 x2) = just (VCVTOP x0 x1 x2)
instr-of (admininstr-REF-NULL x0) = just (REF-NULL x0)
instr-of (admininstr-REF-FUNC x0) = just (REF-FUNC x0)
instr-of admininstr-REF-IS-NULL = just REF-IS-NULL
instr-of (admininstr-LOCAL-GET x0) = just (LOCAL-GET x0)
instr-of (admininstr-LOCAL-SET x0) = just (LOCAL-SET x0)
instr-of (admininstr-LOCAL-TEE x0) = just (LOCAL-TEE x0)
instr-of (admininstr-GLOBAL-GET x0) = just (GLOBAL-GET x0)
instr-of (admininstr-GLOBAL-SET x0) = just (GLOBAL-SET x0)
instr-of (admininstr-TABLE-GET x0) = just (TABLE-GET x0)
instr-of (admininstr-TABLE-SET x0) = just (TABLE-SET x0)
instr-of (admininstr-TABLE-SIZE x0) = just (TABLE-SIZE x0)
instr-of (admininstr-TABLE-GROW x0) = just (TABLE-GROW x0)
instr-of (admininstr-TABLE-FILL x0) = just (TABLE-FILL x0)
instr-of (admininstr-TABLE-COPY x0 x1) = just (TABLE-COPY x0 x1)
instr-of (admininstr-TABLE-INIT x0 x1) = just (TABLE-INIT x0 x1)
instr-of (admininstr-ELEM-DROP x0) = just (ELEM-DROP x0)
instr-of (admininstr-LOAD x0 x1 x2) = just (LOAD x0 x1 x2)
instr-of (admininstr-STORE x0 x1 x2) = just (STORE x0 x1 x2)
instr-of (admininstr-VLOAD x0 x1 x2) = just (VLOAD x0 x1 x2)
instr-of (admininstr-VLOAD-LANE x0 x1 x2 x3) = just (VLOAD-LANE x0 x1 x2 x3)
instr-of (admininstr-VSTORE x0 x1) = just (VSTORE x0 x1)
instr-of (admininstr-VSTORE-LANE x0 x1 x2 x3) = just (VSTORE-LANE x0 x1 x2 x3)
instr-of admininstr-MEMORY-SIZE = just MEMORY-SIZE
instr-of admininstr-MEMORY-GROW = just MEMORY-GROW
instr-of admininstr-MEMORY-FILL = just MEMORY-FILL
instr-of admininstr-MEMORY-COPY = just MEMORY-COPY
instr-of (admininstr-MEMORY-INIT x0) = just (MEMORY-INIT x0)
instr-of (admininstr-DATA-DROP x0) = just (DATA-DROP x0)
instr-of _ = nothing   -- REF-FUNC-ADDR, REF-HOST-ADDR, CALL-ADDR, LABEL-, FRAME-, TRAP

instr-of-instr : ∀ i → instr-of (admininstr-instr i) ≡ just i
instr-of-instr NOP = refl
instr-of-instr UNREACHABLE = refl
instr-of-instr DROP = refl
instr-of-instr (SELECT x0) = refl
instr-of-instr (BLOCK x0 x1) = refl
instr-of-instr (LOOP x0 x1) = refl
instr-of-instr (IFELSE x0 x1 x2) = refl
instr-of-instr (BR x0) = refl
instr-of-instr (BR-IF x0) = refl
instr-of-instr (BR-TABLE x0 x1) = refl
instr-of-instr (CALL x0) = refl
instr-of-instr (CALL-INDIRECT x0 x1) = refl
instr-of-instr RETURN = refl
instr-of-instr (CONST x0 x1) = refl
instr-of-instr (UNOP x0 x1) = refl
instr-of-instr (BINOP x0 x1) = refl
instr-of-instr (TESTOP x0 x1) = refl
instr-of-instr (RELOP x0 x1) = refl
instr-of-instr (CVTOP x0 x1 x2) = refl
instr-of-instr (instr-EXTEND x0 x1) = refl
instr-of-instr (VCONST x0 x1) = refl
instr-of-instr (VVUNOP x0 x1) = refl
instr-of-instr (VVBINOP x0 x1) = refl
instr-of-instr (VVTERNOP x0 x1) = refl
instr-of-instr (VVTESTOP x0 x1) = refl
instr-of-instr (VUNOP x0 x1) = refl
instr-of-instr (VBINOP x0 x1) = refl
instr-of-instr (VTESTOP x0 x1) = refl
instr-of-instr (VRELOP x0 x1) = refl
instr-of-instr (VSHIFTOP x0 x1) = refl
instr-of-instr (VBITMASK x0) = refl
instr-of-instr (VSWIZZLE x0) = refl
instr-of-instr (VSHUFFLE x0 x1) = refl
instr-of-instr (VSPLAT x0) = refl
instr-of-instr (VEXTRACT-LANE x0 x1 x2) = refl
instr-of-instr (VREPLACE-LANE x0 x1) = refl
instr-of-instr (VEXTUNOP x0 x1 x2) = refl
instr-of-instr (VEXTBINOP x0 x1 x2) = refl
instr-of-instr (VNARROW x0 x1 x2) = refl
instr-of-instr (VCVTOP x0 x1 x2) = refl
instr-of-instr (REF-NULL x0) = refl
instr-of-instr (REF-FUNC x0) = refl
instr-of-instr REF-IS-NULL = refl
instr-of-instr (LOCAL-GET x0) = refl
instr-of-instr (LOCAL-SET x0) = refl
instr-of-instr (LOCAL-TEE x0) = refl
instr-of-instr (GLOBAL-GET x0) = refl
instr-of-instr (GLOBAL-SET x0) = refl
instr-of-instr (TABLE-GET x0) = refl
instr-of-instr (TABLE-SET x0) = refl
instr-of-instr (TABLE-SIZE x0) = refl
instr-of-instr (TABLE-GROW x0) = refl
instr-of-instr (TABLE-FILL x0) = refl
instr-of-instr (TABLE-COPY x0 x1) = refl
instr-of-instr (TABLE-INIT x0 x1) = refl
instr-of-instr (ELEM-DROP x0) = refl
instr-of-instr (LOAD x0 x1 x2) = refl
instr-of-instr (STORE x0 x1 x2) = refl
instr-of-instr (VLOAD x0 x1 x2) = refl
instr-of-instr (VLOAD-LANE x0 x1 x2 x3) = refl
instr-of-instr (VSTORE x0 x1) = refl
instr-of-instr (VSTORE-LANE x0 x1 x2 x3) = refl
instr-of-instr MEMORY-SIZE = refl
instr-of-instr MEMORY-GROW = refl
instr-of-instr MEMORY-FILL = refl
instr-of-instr MEMORY-COPY = refl
instr-of-instr (MEMORY-INIT x0) = refl
instr-of-instr (DATA-DROP x0) = refl

-- recover the source instruction from a stuck injection equation
recover : ∀ {i e j} → admininstr-instr i ≡ e → instr-of e ≡ just j → i ≡ j
recover {i} eq eq2 =
  just-inj (tr≡ (sym (instr-of-instr i)) (tr≡ (cong instr-of eq) eq2))

refute-plain : ∀ {i e} {A : Set} → admininstr-instr i ≡ e → instr-of e ≡ nothing → A
refute-plain {i} eq eq2 =
  case tr≡ (sym (instr-of-instr i)) (tr≡ (cong instr-of eq) eq2) of λ ()

------------------------------------------------------------------------
-- 5. Shape inversion for Instr-ok (constructor-indexed: direct match
--    works) and for Instr-ok2 (function-indexed: equation-generalized).
------------------------------------------------------------------------

iok-nop : ∀ {C d c} → Instr-ok C NOP (mk-functype (mk-list d) (mk-list c)) →
  (d ≡ []) × (c ≡ [])
iok-nop (nop _) = refl , refl

iok-drop : ∀ {C d c} → Instr-ok C DROP (mk-functype (mk-list d) (mk-list c)) →
  Σ valtype λ t → (d ≡ t ∷ []) × (c ≡ [])
iok-drop (drop' _ t) = t , refl , refl

iok-const : ∀ {C nt cn d c} →
  Instr-ok C (CONST nt cn) (mk-functype (mk-list d) (mk-list c)) →
  (d ≡ []) × (c ≡ valtype-numtype nt ∷ [])
iok-const (const _ _ _) = refl , refl

iok-vconst : ∀ {C vt cn d c} →
  Instr-ok C (VCONST vt cn) (mk-functype (mk-list d) (mk-list c)) →
  (d ≡ []) × (c ≡ valtype-V128 ∷ [])
iok-vconst (vconst _ _) = refl , refl

iok-refnull : ∀ {C rt d c} →
  Instr-ok C (REF-NULL rt) (mk-functype (mk-list d) (mk-list c)) →
  (d ≡ []) × (c ≡ valtype-reftype rt ∷ [])
iok-refnull (ref-null _ _) = refl , refl

iok-unop : ∀ {C nt op d c} →
  Instr-ok C (UNOP nt op) (mk-functype (mk-list d) (mk-list c)) →
  (d ≡ valtype-numtype nt ∷ []) × (c ≡ valtype-numtype nt ∷ [])
iok-unop (unop _ _ _) = refl , refl

iok-binop : ∀ {C nt op d c} →
  Instr-ok C (BINOP nt op) (mk-functype (mk-list d) (mk-list c)) →
  (d ≡ valtype-numtype nt ∷ valtype-numtype nt ∷ []) × (c ≡ valtype-numtype nt ∷ [])
iok-binop (binop _ _ _) = refl , refl

iok-testop : ∀ {C nt op d c} →
  Instr-ok C (TESTOP nt op) (mk-functype (mk-list d) (mk-list c)) →
  (d ≡ valtype-numtype nt ∷ []) × (c ≡ valtype-I32 ∷ [])
iok-testop (testop _ _ _) = refl , refl

iok-relop : ∀ {C nt op d c} →
  Instr-ok C (RELOP nt op) (mk-functype (mk-list d) (mk-list c)) →
  (d ≡ valtype-numtype nt ∷ valtype-numtype nt ∷ []) × (c ≡ valtype-I32 ∷ [])
iok-relop (relop _ _ _) = refl , refl

iok-select : ∀ {C opt d c} →
  Instr-ok C (SELECT opt) (mk-functype (mk-list d) (mk-list c)) →
  Σ valtype λ t → (d ≡ t ∷ t ∷ valtype-I32 ∷ []) × (c ≡ t ∷ [])
iok-select (select-expl _ t) = t , refl , refl
iok-select (select-impl _ t _ _ _ _ _) = t , refl , refl

iok-lget : ∀ {C x d c} →
  Instr-ok C (LOCAL-GET x) (mk-functype (mk-list d) (mk-list c)) →
  Σ valtype λ t → (d ≡ []) × (c ≡ t ∷ []) ×
  (proj-uN-0 32 x < length (context-LOCALS C)) ×
  ((context-LOCALS C [ proj-uN-0 32 x ]!) ≡ t)
iok-lget (local-get _ _ t p q) = t , refl , refl , p , q

iok-lset : ∀ {C x d c} →
  Instr-ok C (LOCAL-SET x) (mk-functype (mk-list d) (mk-list c)) →
  Σ valtype λ t → (d ≡ t ∷ []) × (c ≡ []) ×
  (proj-uN-0 32 x < length (context-LOCALS C)) ×
  ((context-LOCALS C [ proj-uN-0 32 x ]!) ≡ t)
iok-lset (local-set _ _ t p q) = t , refl , refl , p , q

iok-gget : ∀ {C x d c} →
  Instr-ok C (GLOBAL-GET x) (mk-functype (mk-list d) (mk-list c)) →
  Σ (mut × valtype) λ (mu , t) → (d ≡ []) × (c ≡ t ∷ []) ×
  (proj-uN-0 32 x < length (context-GLOBALS C)) ×
  ((context-GLOBALS C [ proj-uN-0 32 x ]!) ≡ mk-globaltype mu t)
iok-gget (global-get _ _ t mu p q) = (mu , t) , refl , refl , p , q

-- Instr-ok2 inversion at specific admininstr shapes.  For each shape:
-- `plain` is decided via `recover`/`refute-plain`, admin-only
-- constructors clash syntactically, and Instr-ok2--ref is decided by
-- destructing the ref (its injection then reduces).

nop-inv : ∀ {s C e d c} →
  Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) →
  e ≡ admininstr-NOP → (d ≡ []) × (c ≡ [])
nop-inv (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-nop iok
nop-inv (label _ _ _ _ _ _ _ _ _ _) ()
nop-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
nop-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
nop-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
nop-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
nop-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
nop-inv (Instr-ok2--trap _ _ _ _) ()

drop-inv : ∀ {s C e d c} →
  Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) →
  e ≡ admininstr-DROP → Σ valtype λ t → (d ≡ t ∷ []) × (c ≡ [])
drop-inv (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-drop iok
drop-inv (label _ _ _ _ _ _ _ _ _ _) ()
drop-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
drop-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
drop-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
drop-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
drop-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
drop-inv (Instr-ok2--trap _ _ _ _) ()

sel-inv : ∀ {s C e d c opt} →
  Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) →
  e ≡ admininstr-SELECT opt →
  Σ valtype λ t → (d ≡ t ∷ t ∷ valtype-I32 ∷ []) × (c ≡ t ∷ [])
sel-inv (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-select iok
sel-inv (label _ _ _ _ _ _ _ _ _ _) ()
sel-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
sel-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
sel-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
sel-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
sel-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
sel-inv (Instr-ok2--trap _ _ _ _) ()

unop-inv : ∀ {s C e d c nt op} →
  Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) →
  e ≡ admininstr-UNOP nt op →
  (d ≡ valtype-numtype nt ∷ []) × (c ≡ valtype-numtype nt ∷ [])
unop-inv (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-unop iok
unop-inv (label _ _ _ _ _ _ _ _ _ _) ()
unop-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
unop-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
unop-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
unop-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
unop-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
unop-inv (Instr-ok2--trap _ _ _ _) ()

binop-inv : ∀ {s C e d c nt op} →
  Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) →
  e ≡ admininstr-BINOP nt op →
  (d ≡ valtype-numtype nt ∷ valtype-numtype nt ∷ []) × (c ≡ valtype-numtype nt ∷ [])
binop-inv (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-binop iok
binop-inv (label _ _ _ _ _ _ _ _ _ _) ()
binop-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
binop-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
binop-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
binop-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
binop-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
binop-inv (Instr-ok2--trap _ _ _ _) ()

testop-inv : ∀ {s C e d c nt op} →
  Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) →
  e ≡ admininstr-TESTOP nt op →
  (d ≡ valtype-numtype nt ∷ []) × (c ≡ valtype-I32 ∷ [])
testop-inv (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-testop iok
testop-inv (label _ _ _ _ _ _ _ _ _ _) ()
testop-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
testop-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
testop-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
testop-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
testop-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
testop-inv (Instr-ok2--trap _ _ _ _) ()

relop-inv : ∀ {s C e d c nt op} →
  Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) →
  e ≡ admininstr-RELOP nt op →
  (d ≡ valtype-numtype nt ∷ valtype-numtype nt ∷ []) × (c ≡ valtype-I32 ∷ [])
relop-inv (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-relop iok
relop-inv (label _ _ _ _ _ _ _ _ _ _) ()
relop-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
relop-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
relop-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
relop-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
relop-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
relop-inv (Instr-ok2--trap _ _ _ _) ()

lget-inv : ∀ {s C e d c x} →
  Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) →
  e ≡ admininstr-LOCAL-GET x →
  Σ valtype λ t → (d ≡ []) × (c ≡ t ∷ []) ×
  (proj-uN-0 32 x < length (context-LOCALS C)) ×
  ((context-LOCALS C [ proj-uN-0 32 x ]!) ≡ t)
lget-inv (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-lget iok
lget-inv (label _ _ _ _ _ _ _ _ _ _) ()
lget-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
lget-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
lget-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
lget-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
lget-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
lget-inv (Instr-ok2--trap _ _ _ _) ()

lset-inv : ∀ {s C e d c x} →
  Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) →
  e ≡ admininstr-LOCAL-SET x →
  Σ valtype λ t → (d ≡ t ∷ []) × (c ≡ []) ×
  (proj-uN-0 32 x < length (context-LOCALS C)) ×
  ((context-LOCALS C [ proj-uN-0 32 x ]!) ≡ t)
lset-inv (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-lset iok
lset-inv (label _ _ _ _ _ _ _ _ _ _) ()
lset-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
lset-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
lset-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
lset-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
lset-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
lset-inv (Instr-ok2--trap _ _ _ _) ()

gget-inv : ∀ {s C e d c x} →
  Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) →
  e ≡ admininstr-GLOBAL-GET x →
  Σ (mut × valtype) λ (mu , t) → (d ≡ []) × (c ≡ t ∷ []) ×
  (proj-uN-0 32 x < length (context-GLOBALS C)) ×
  ((context-GLOBALS C [ proj-uN-0 32 x ]!) ≡ mk-globaltype mu t)
gget-inv (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-gget iok
gget-inv (label _ _ _ _ _ _ _ _ _ _) ()
gget-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
gget-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
gget-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
gget-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
gget-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
gget-inv (Instr-ok2--trap _ _ _ _) ()

iok-gset : ∀ {C x d c} →
  Instr-ok C (GLOBAL-SET x) (mk-functype (mk-list d) (mk-list c)) →
  Σ valtype λ t → (d ≡ t ∷ []) × (c ≡ []) ×
  (proj-uN-0 32 x < length (context-GLOBALS C)) ×
  ((context-GLOBALS C [ proj-uN-0 32 x ]!) ≡ mk-globaltype (just MUT) t)
iok-gset (global-set _ _ t p q) = t , refl , refl , p , q

gset-inv : ∀ {s C e d c x} →
  Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) →
  e ≡ admininstr-GLOBAL-SET x →
  Σ valtype λ t → (d ≡ t ∷ []) × (c ≡ []) ×
  (proj-uN-0 32 x < length (context-GLOBALS C)) ×
  ((context-GLOBALS C [ proj-uN-0 32 x ]!) ≡ mk-globaltype (just MUT) t)
gset-inv (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-gset iok
gset-inv (label _ _ _ _ _ _ _ _ _ _) ()
gset-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
gset-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
gset-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
gset-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
gset-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
gset-inv (Instr-ok2--trap _ _ _ _) ()

iok-ddrop : ∀ {C x d c} →
  Instr-ok C (DATA-DROP x) (mk-functype (mk-list d) (mk-list c)) → (d ≡ []) × (c ≡ [])
iok-ddrop (data-drop _ _ _ _) = refl , refl

ddrop-inv : ∀ {s C e d c x} →
  Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) → e ≡ admininstr-DATA-DROP x →
  (d ≡ []) × (c ≡ [])
ddrop-inv (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-ddrop iok
ddrop-inv (label _ _ _ _ _ _ _ _ _ _) ()
ddrop-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
ddrop-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
ddrop-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
ddrop-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
ddrop-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
ddrop-inv (Instr-ok2--trap _ _ _ _) ()

iok-edrop : ∀ {C x d c} →
  Instr-ok C (ELEM-DROP x) (mk-functype (mk-list d) (mk-list c)) → (d ≡ []) × (c ≡ [])
iok-edrop (elem-drop _ _ _ _ _) = refl , refl

edrop-inv : ∀ {s C e d c x} →
  Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) → e ≡ admininstr-ELEM-DROP x →
  (d ≡ []) × (c ≡ [])
edrop-inv (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-edrop iok
edrop-inv (label _ _ _ _ _ _ _ _ _ _) ()
edrop-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
edrop-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
edrop-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
edrop-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
edrop-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
edrop-inv (Instr-ok2--trap _ _ _ _) ()

iok-mgrow : ∀ {C d c} →
  Instr-ok C MEMORY-GROW (mk-functype (mk-list d) (mk-list c)) →
  (d ≡ valtype-I32 ∷ []) × (c ≡ valtype-I32 ∷ [])
iok-mgrow (memory-grow _ _ _ _) = refl , refl

mgrow-inv : ∀ {s C e d c} →
  Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) → e ≡ admininstr-MEMORY-GROW →
  (d ≡ valtype-I32 ∷ []) × (c ≡ valtype-I32 ∷ [])
mgrow-inv (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-mgrow iok
mgrow-inv (label _ _ _ _ _ _ _ _ _ _) ()
mgrow-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
mgrow-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
mgrow-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
mgrow-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
mgrow-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
mgrow-inv (Instr-ok2--trap _ _ _ _) ()

iok-tgrow : ∀ {C x d c} →
  Instr-ok C (TABLE-GROW x) (mk-functype (mk-list d) (mk-list c)) →
  Σ reftype λ rt → (d ≡ valtype-reftype rt ∷ valtype-I32 ∷ []) × (c ≡ valtype-I32 ∷ [])
iok-tgrow (table-grow _ _ rt _ _ _) = rt , refl , refl

tgrow-inv : ∀ {s C e d c x} →
  Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) → e ≡ admininstr-TABLE-GROW x →
  Σ reftype λ rt → (d ≡ valtype-reftype rt ∷ valtype-I32 ∷ []) × (c ≡ valtype-I32 ∷ [])
tgrow-inv (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-tgrow iok
tgrow-inv (label _ _ _ _ _ _ _ _ _ _) ()
tgrow-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
tgrow-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
tgrow-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
tgrow-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
tgrow-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
tgrow-inv (Instr-ok2--trap _ _ _ _) ()

iok-storenum : ∀ {C nt ao d c} →
  Instr-ok C (STORE nt nothing ao) (mk-functype (mk-list d) (mk-list c)) →
  (d ≡ valtype-I32 ∷ valtype-numtype nt ∷ []) × (c ≡ [])
iok-storenum (store-val _ _ _ _ _ _ _ _) = refl , refl

storenum-inv : ∀ {s C e d c nt ao} →
  Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) → e ≡ admininstr-STORE nt nothing ao →
  (d ≡ valtype-I32 ∷ valtype-numtype nt ∷ []) × (c ≡ [])
storenum-inv (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-storenum iok
storenum-inv (label _ _ _ _ _ _ _ _ _ _) ()
storenum-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
storenum-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
storenum-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
storenum-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
storenum-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
storenum-inv (Instr-ok2--trap _ _ _ _) ()

-- store-pack: index by a VARIABLE numtype nt (so store-pack's
-- `numtype-Inn Inn` index unifies nt := numtype-Inn Inn); the concrete
-- value type is returned existentially and discarded by the caller.
iok-storepack : ∀ {C nt sz ao d c} →
  Instr-ok C (STORE nt (just sz) ao) (mk-functype (mk-list d) (mk-list c)) →
  Σ valtype λ t → (d ≡ valtype-I32 ∷ t ∷ []) × (c ≡ [])
iok-storepack (store-pack _ Inn _ _ _ _ _ _) = valtype-Inn Inn , refl , refl

storepack-inv : ∀ {s C e d c nt sz ao} →
  Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) →
  e ≡ admininstr-STORE nt (just sz) ao →
  Σ valtype λ t → (d ≡ valtype-I32 ∷ t ∷ []) × (c ≡ [])
storepack-inv (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-storepack iok
storepack-inv (label _ _ _ _ _ _ _ _ _ _) ()
storepack-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
storepack-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
storepack-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
storepack-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
storepack-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
storepack-inv (Instr-ok2--trap _ _ _ _) ()

iok-storepack-full : ∀ {C nt sz ao d c} → Instr-ok C (STORE nt (just sz) ao) (mk-functype (mk-list d) (mk-list c)) →
  Σ Inn λ In → Σ M λ Mm → (nt ≡ numtype-Inn In) × (sz ≡ mk-sz Mm) × (d ≡ valtype-I32 ∷ valtype-Inn In ∷ [])
iok-storepack-full (store-pack _ In Mm _ _ _ _ _) = In , Mm , refl , refl , refl
storepack-full : ∀ {s C e nt sz ao d c} → Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) → e ≡ admininstr-STORE nt (just sz) ao →
  Σ Inn λ In → Σ M λ Mm → (nt ≡ numtype-Inn In) × (sz ≡ mk-sz Mm) × (d ≡ valtype-I32 ∷ valtype-Inn In ∷ [])
storepack-full (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-storepack-full iok
storepack-full (label _ _ _ _ _ _ _ _ _ _) ()
storepack-full (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
storepack-full (Instr-ok2--call-addr _ _ _ _ _ _) ()
storepack-full (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
storepack-full (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
storepack-full (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
storepack-full (Instr-ok2--trap _ _ _ _) ()

iok-vstore : ∀ {C ao d c} →
  Instr-ok C (VSTORE V128 ao) (mk-functype (mk-list d) (mk-list c)) →
  (d ≡ valtype-I32 ∷ valtype-V128 ∷ []) × (c ≡ [])
iok-vstore (vstore _ _ _ _ _ _ _) = refl , refl

vstore-inv : ∀ {s C e d c ao} →
  Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) → e ≡ admininstr-VSTORE V128 ao →
  (d ≡ valtype-I32 ∷ valtype-V128 ∷ []) × (c ≡ [])
vstore-inv (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-vstore iok
vstore-inv (label _ _ _ _ _ _ _ _ _ _) ()
vstore-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
vstore-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
vstore-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
vstore-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
vstore-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
vstore-inv (Instr-ok2--trap _ _ _ _) ()

iok-vstorelane : ∀ {C n ao j d c} →
  Instr-ok C (VSTORE-LANE V128 (mk-sz n) ao j) (mk-functype (mk-list d) (mk-list c)) →
  (d ≡ valtype-I32 ∷ valtype-V128 ∷ []) × (c ≡ [])
iok-vstorelane (vstore-lane _ _ _ _ _ _ _ _ _) = refl , refl

vstorelane-inv : ∀ {s C e d c n ao j} →
  Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) →
  e ≡ admininstr-VSTORE-LANE V128 (mk-sz n) ao j →
  (d ≡ valtype-I32 ∷ valtype-V128 ∷ []) × (c ≡ [])
vstorelane-inv (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-vstorelane iok
vstorelane-inv (label _ _ _ _ _ _ _ _ _ _) ()
vstorelane-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
vstorelane-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
vstorelane-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
vstorelane-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
vstorelane-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
vstorelane-inv (Instr-ok2--trap _ _ _ _) ()

-- The label-context extension used by block/loop/if and by LABEL-.
labC : List valtype → context
labC ts = record
  { context-TYPES = [] ; context-FUNCS = [] ; context-GLOBALS = []
  ; context-TABLES = [] ; context-MEMS = [] ; context-ELEMS = []
  ; context-DATAS = [] ; context-LOCALS = []
  ; LABELS = mk-list ts ∷ [] ; context-RETURN = nothing }

ft-inj : ∀ {a b c d} →
  mk-functype (mk-list a) (mk-list b) ≡ mk-functype (mk-list c) (mk-list d) →
  (a ≡ c) × (b ≡ d)
ft-inj refl = refl , refl

tabletype-rt-inj : ∀ {l1 r1 l2 r2} → mk-tabletype l1 r1 ≡ mk-tabletype l2 r2 → r1 ≡ r2
tabletype-rt-inj refl = refl

-- Source-level sequence typing embeds into admin-level typing.
instrs-ok→2 : ∀ {C is ft} (s : store) → Instrs-ok C is ft →
  Instrs-ok2 s C (map (λ i → admininstr-instr i) is) ft
instrs-ok→2 s (empty _) = Instrs-ok2--empty _ _
instrs-ok→2 s (Instrs-ok--instr _ i _ _ iok) =
  Instrs-ok2--instr _ _ _ _ _ (plain _ _ _ _ _ iok)
instrs-ok→2 {C} s (seq _ l1 l2 t1 t3 t2 d1 d2) =
  subst (λ l → Instrs-ok2 s C l (mk-functype (mk-list t1) (mk-list t3)))
        (sym (map-++ (λ i → admininstr-instr i) l1 l2))
        (Instrs-ok2--seq _ _ _ _ _ _ _ (instrs-ok→2 s d1) (instrs-ok→2 s d2))
instrs-ok→2 s (sub _ _ _ _ _ _ d r1 r2) =
  Instrs-ok2--sub _ _ _ _ _ _ _ (instrs-ok→2 s d) r1 r2
instrs-ok→2 s (Instrs-ok--frame _ _ ts _ _ d) =
  Instrs-ok2--frame _ _ _ ts _ _ (instrs-ok→2 s d)

iok-block : ∀ {C bt is d c} →
  Instr-ok C (BLOCK bt is) (mk-functype (mk-list d) (mk-list c)) →
  Blocktype-ok C bt (mk-functype (mk-list d) (mk-list c)) ×
  Instrs-ok (labC c ⧺ C) is (mk-functype (mk-list d) (mk-list c))
iok-block (block _ _ _ _ _ bok body) = bok , body

iok-loop : ∀ {C bt is d c} →
  Instr-ok C (LOOP bt is) (mk-functype (mk-list d) (mk-list c)) →
  Blocktype-ok C bt (mk-functype (mk-list d) (mk-list c)) ×
  Instrs-ok (labC d ⧺ C) is (mk-functype (mk-list d) (mk-list c))
iok-loop (loop _ _ _ _ _ bok body) = bok , body

iok-if : ∀ {C bt i1 i2 d c} →
  Instr-ok C (IFELSE bt i1 i2) (mk-functype (mk-list d) (mk-list c)) →
  Σ (List valtype) λ t1 → (d ≡ t1 ++ valtype-I32 ∷ []) ×
  Blocktype-ok C bt (mk-functype (mk-list t1) (mk-list c)) ×
  Instrs-ok (labC c ⧺ C) i1 (mk-functype (mk-list t1) (mk-list c)) ×
  Instrs-ok (labC c ⧺ C) i2 (mk-functype (mk-list t1) (mk-list c))
iok-if (if' _ _ _ _ t1 _ bok b1 b2) = t1 , refl , bok , b1 , b2

iok-br : ∀ {C l d c} →
  Instr-ok C (BR l) (mk-functype (mk-list d) (mk-list c)) →
  Σ (List valtype × List valtype) λ (t1 , tl) → (d ≡ t1 ++ tl) ×
  (proj-uN-0 32 l < length (LABELS C)) ×
  ((proj-list-0 valtype ((LABELS C) [ proj-uN-0 32 l ]!)) ≡ tl)
iok-br (br _ _ t1 tl _ p q) = (t1 , tl) , refl , p , q

iok-brif : ∀ {C l d c} →
  Instr-ok C (BR-IF l) (mk-functype (mk-list d) (mk-list c)) →
  Σ (List valtype) λ tl → (d ≡ tl ++ valtype-I32 ∷ []) × (c ≡ tl) ×
  (proj-uN-0 32 l < length (LABELS C)) ×
  ((proj-list-0 valtype ((LABELS C) [ proj-uN-0 32 l ]!)) ≡ tl)
iok-brif (br-if _ _ tl p q) = tl , refl , refl , p , q

block-inv : ∀ {s C e d c bt is} →
  Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) →
  e ≡ admininstr-BLOCK bt is →
  Blocktype-ok C bt (mk-functype (mk-list d) (mk-list c)) ×
  Instrs-ok (labC c ⧺ C) is (mk-functype (mk-list d) (mk-list c))
block-inv (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-block iok
block-inv (label _ _ _ _ _ _ _ _ _ _) ()
block-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
block-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
block-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
block-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
block-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
block-inv (Instr-ok2--trap _ _ _ _) ()

loop-inv : ∀ {s C e d c bt is} →
  Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) →
  e ≡ admininstr-LOOP bt is →
  Instr-ok C (LOOP bt is) (mk-functype (mk-list d) (mk-list c)) ×
  Blocktype-ok C bt (mk-functype (mk-list d) (mk-list c)) ×
  Instrs-ok (labC d ⧺ C) is (mk-functype (mk-list d) (mk-list c))
loop-inv (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok , iok-loop iok
loop-inv (label _ _ _ _ _ _ _ _ _ _) ()
loop-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
loop-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
loop-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
loop-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
loop-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
loop-inv (Instr-ok2--trap _ _ _ _) ()

if-inv : ∀ {s C e d c bt i1 i2} →
  Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) →
  e ≡ admininstr-IFELSE bt i1 i2 →
  Σ (List valtype) λ t1 → (d ≡ t1 ++ valtype-I32 ∷ []) ×
  Blocktype-ok C bt (mk-functype (mk-list t1) (mk-list c)) ×
  Instrs-ok (labC c ⧺ C) i1 (mk-functype (mk-list t1) (mk-list c)) ×
  Instrs-ok (labC c ⧺ C) i2 (mk-functype (mk-list t1) (mk-list c))
if-inv (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-if iok
if-inv (label _ _ _ _ _ _ _ _ _ _) ()
if-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
if-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
if-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
if-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
if-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
if-inv (Instr-ok2--trap _ _ _ _) ()

br-inv : ∀ {s C e d c l} →
  Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) →
  e ≡ admininstr-BR l →
  Σ (List valtype × List valtype) λ (t1 , tl) → (d ≡ t1 ++ tl) ×
  (proj-uN-0 32 l < length (LABELS C)) ×
  ((proj-list-0 valtype ((LABELS C) [ proj-uN-0 32 l ]!)) ≡ tl)
br-inv (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-br iok
br-inv (label _ _ _ _ _ _ _ _ _ _) ()
br-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
br-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
br-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
br-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
br-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
br-inv (Instr-ok2--trap _ _ _ _) ()

brif-inv : ∀ {s C e d c l} →
  Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) →
  e ≡ admininstr-BR-IF l →
  Σ (List valtype) λ tl → (d ≡ tl ++ valtype-I32 ∷ []) × (c ≡ tl) ×
  (proj-uN-0 32 l < length (LABELS C)) ×
  ((proj-list-0 valtype ((LABELS C) [ proj-uN-0 32 l ]!)) ≡ tl)
brif-inv (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-brif iok
brif-inv (label _ _ _ _ _ _ _ _ _ _) ()
brif-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
brif-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
brif-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
brif-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
brif-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
brif-inv (Instr-ok2--trap _ _ _ _) ()

iok-cvtop : ∀ {C a b op d c} →
  Instr-ok C (CVTOP a b op) (mk-functype (mk-list d) (mk-list c)) →
  (d ≡ valtype-numtype b ∷ []) × (c ≡ valtype-numtype a ∷ [])
iok-cvtop (cvtop-reinterpret _ _ _ _ _ _) = refl , refl
iok-cvtop (cvtop-convert _ _ _ _) = refl , refl

cvtop-inv : ∀ {s C e d c a b op} →
  Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) →
  e ≡ admininstr-CVTOP a b op →
  (d ≡ valtype-numtype b ∷ []) × (c ≡ valtype-numtype a ∷ [])
cvtop-inv (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-cvtop iok
cvtop-inv (label _ _ _ _ _ _ _ _ _ _) ()
cvtop-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
cvtop-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
cvtop-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
cvtop-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
cvtop-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
cvtop-inv (Instr-ok2--trap _ _ _ _) ()

iok-risnull : ∀ {C d c} →
  Instr-ok C REF-IS-NULL (mk-functype (mk-list d) (mk-list c)) →
  Σ reftype λ rt → (d ≡ valtype-reftype rt ∷ []) × (c ≡ valtype-I32 ∷ [])
iok-risnull (ref-is-null _ rt) = rt , refl , refl

risnull-inv : ∀ {s C e d c} →
  Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) →
  e ≡ admininstr-REF-IS-NULL →
  Σ reftype λ rt → (d ≡ valtype-reftype rt ∷ []) × (c ≡ valtype-I32 ∷ [])
risnull-inv (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-risnull iok
risnull-inv (label _ _ _ _ _ _ _ _ _ _) ()
risnull-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
risnull-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
risnull-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
risnull-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
risnull-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
risnull-inv (Instr-ok2--trap _ _ _ _) ()

iok-tee : ∀ {C x d c} →
  Instr-ok C (LOCAL-TEE x) (mk-functype (mk-list d) (mk-list c)) →
  Σ valtype λ t → (d ≡ t ∷ []) × (c ≡ t ∷ []) ×
  (proj-uN-0 32 x < length (context-LOCALS C)) ×
  ((context-LOCALS C [ proj-uN-0 32 x ]!) ≡ t)
iok-tee (local-tee _ _ t p q) = t , refl , refl , p , q

tee-inv : ∀ {s C e d c x} →
  Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) →
  e ≡ admininstr-LOCAL-TEE x →
  Σ valtype λ t → (d ≡ t ∷ []) × (c ≡ t ∷ []) ×
  (proj-uN-0 32 x < length (context-LOCALS C)) ×
  ((context-LOCALS C [ proj-uN-0 32 x ]!) ≡ t)
tee-inv (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-tee iok
tee-inv (label _ _ _ _ _ _ _ _ _ _) ()
tee-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
tee-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
tee-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
tee-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
tee-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
tee-inv (Instr-ok2--trap _ _ _ _) ()

iok-brtable : ∀ {C ls l' d c} →
  Instr-ok C (BR-TABLE ls l') (mk-functype (mk-list d) (mk-list c)) →
  Σ (List valtype × List valtype) λ (t1 , tl) →
    (d ≡ t1 ++ (tl ++ valtype-I32 ∷ [])) ×
    Forall (λ l → (proj-uN-0 32 l < length (LABELS C))) ls ×
    Forall (λ l → Resulttype-sub (mk-list tl) ((LABELS C) [ proj-uN-0 32 l ]!)) ls ×
    (proj-uN-0 32 l' < length (LABELS C)) ×
    Resulttype-sub (mk-list tl) ((LABELS C) [ proj-uN-0 32 l' ]!)
iok-brtable (br-table _ _ _ t1 tl _ ab asb l< ls') =
  (t1 , tl) , refl , ab , asb , l< , ls'

brtable-inv : ∀ {s C e d c ls l'} →
  Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) →
  e ≡ admininstr-BR-TABLE ls l' →
  Σ (List valtype × List valtype) λ (t1 , tl) →
    (d ≡ t1 ++ (tl ++ valtype-I32 ∷ [])) ×
    Forall (λ l → (proj-uN-0 32 l < length (LABELS C))) ls ×
    Forall (λ l → Resulttype-sub (mk-list tl) ((LABELS C) [ proj-uN-0 32 l ]!)) ls ×
    (proj-uN-0 32 l' < length (LABELS C)) ×
    Resulttype-sub (mk-list tl) ((LABELS C) [ proj-uN-0 32 l' ]!)
brtable-inv (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-brtable iok
brtable-inv (label _ _ _ _ _ _ _ _ _ _) ()
brtable-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
brtable-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
brtable-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
brtable-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
brtable-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
brtable-inv (Instr-ok2--trap _ _ _ _) ()

-- Vector (SIMD) op shapes.
iok-vvunop : ∀ {C vt op d c} →
  Instr-ok C (VVUNOP vt op) (mk-functype (mk-list d) (mk-list c)) →
  (d ≡ valtype-V128 ∷ []) × (c ≡ valtype-V128 ∷ [])
iok-vvunop (Instr-ok--vvunop _ _) = refl , refl

iok-vvbinop : ∀ {C vt op d c} →
  Instr-ok C (VVBINOP vt op) (mk-functype (mk-list d) (mk-list c)) →
  (d ≡ valtype-V128 ∷ valtype-V128 ∷ []) × (c ≡ valtype-V128 ∷ [])
iok-vvbinop (Instr-ok--vvbinop _ _) = refl , refl

iok-vvternop : ∀ {C vt op d c} →
  Instr-ok C (VVTERNOP vt op) (mk-functype (mk-list d) (mk-list c)) →
  (d ≡ valtype-V128 ∷ valtype-V128 ∷ valtype-V128 ∷ []) × (c ≡ valtype-V128 ∷ [])
iok-vvternop (Instr-ok--vvternop _ _) = refl , refl

iok-vvtestop : ∀ {C vt op d c} →
  Instr-ok C (VVTESTOP vt op) (mk-functype (mk-list d) (mk-list c)) →
  (d ≡ valtype-V128 ∷ []) × (c ≡ valtype-I32 ∷ [])
iok-vvtestop (Instr-ok--vvtestop _ _) = refl , refl

iok-vunop : ∀ {C sh op d c} →
  Instr-ok C (VUNOP sh op) (mk-functype (mk-list d) (mk-list c)) →
  (d ≡ valtype-V128 ∷ []) × (c ≡ valtype-V128 ∷ [])
iok-vunop (vunop _ _ _) = refl , refl

iok-vbinop : ∀ {C sh op d c} →
  Instr-ok C (VBINOP sh op) (mk-functype (mk-list d) (mk-list c)) →
  (d ≡ valtype-V128 ∷ valtype-V128 ∷ []) × (c ≡ valtype-V128 ∷ [])
iok-vbinop (vbinop _ _ _) = refl , refl

iok-vtestop : ∀ {C sh op d c} →
  Instr-ok C (VTESTOP sh op) (mk-functype (mk-list d) (mk-list c)) →
  (d ≡ valtype-V128 ∷ []) × (c ≡ valtype-I32 ∷ [])
iok-vtestop (vtestop _ _ _) = refl , refl

vvunop-inv : ∀ {s C e d c vt op} →
  Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) →
  e ≡ admininstr-VVUNOP vt op →
  (d ≡ valtype-V128 ∷ []) × (c ≡ valtype-V128 ∷ [])
vvunop-inv (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-vvunop iok
vvunop-inv (label _ _ _ _ _ _ _ _ _ _) ()
vvunop-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
vvunop-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
vvunop-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
vvunop-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
vvunop-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
vvunop-inv (Instr-ok2--trap _ _ _ _) ()

vvbinop-inv : ∀ {s C e d c vt op} →
  Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) →
  e ≡ admininstr-VVBINOP vt op →
  (d ≡ valtype-V128 ∷ valtype-V128 ∷ []) × (c ≡ valtype-V128 ∷ [])
vvbinop-inv (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-vvbinop iok
vvbinop-inv (label _ _ _ _ _ _ _ _ _ _) ()
vvbinop-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
vvbinop-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
vvbinop-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
vvbinop-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
vvbinop-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
vvbinop-inv (Instr-ok2--trap _ _ _ _) ()

vvternop-inv : ∀ {s C e d c vt op} →
  Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) →
  e ≡ admininstr-VVTERNOP vt op →
  (d ≡ valtype-V128 ∷ valtype-V128 ∷ valtype-V128 ∷ []) × (c ≡ valtype-V128 ∷ [])
vvternop-inv (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-vvternop iok
vvternop-inv (label _ _ _ _ _ _ _ _ _ _) ()
vvternop-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
vvternop-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
vvternop-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
vvternop-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
vvternop-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
vvternop-inv (Instr-ok2--trap _ _ _ _) ()

vvtestop-inv : ∀ {s C e d c vt op} →
  Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) →
  e ≡ admininstr-VVTESTOP vt op →
  (d ≡ valtype-V128 ∷ []) × (c ≡ valtype-I32 ∷ [])
vvtestop-inv (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-vvtestop iok
vvtestop-inv (label _ _ _ _ _ _ _ _ _ _) ()
vvtestop-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
vvtestop-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
vvtestop-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
vvtestop-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
vvtestop-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
vvtestop-inv (Instr-ok2--trap _ _ _ _) ()

vunop-inv : ∀ {s C e d c sh op} →
  Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) →
  e ≡ admininstr-VUNOP sh op →
  (d ≡ valtype-V128 ∷ []) × (c ≡ valtype-V128 ∷ [])
vunop-inv (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-vunop iok
vunop-inv (label _ _ _ _ _ _ _ _ _ _) ()
vunop-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
vunop-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
vunop-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
vunop-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
vunop-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
vunop-inv (Instr-ok2--trap _ _ _ _) ()

vbinop-inv : ∀ {s C e d c sh op} →
  Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) →
  e ≡ admininstr-VBINOP sh op →
  (d ≡ valtype-V128 ∷ valtype-V128 ∷ []) × (c ≡ valtype-V128 ∷ [])
vbinop-inv (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-vbinop iok
vbinop-inv (label _ _ _ _ _ _ _ _ _ _) ()
vbinop-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
vbinop-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
vbinop-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
vbinop-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
vbinop-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
vbinop-inv (Instr-ok2--trap _ _ _ _) ()

vtestop-inv : ∀ {s C e d c sh op} →
  Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) →
  e ≡ admininstr-VTESTOP sh op →
  (d ≡ valtype-V128 ∷ []) × (c ≡ valtype-I32 ∷ [])
vtestop-inv (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-vtestop iok
vtestop-inv (label _ _ _ _ _ _ _ _ _ _) ()
vtestop-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
vtestop-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
vtestop-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
vtestop-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
vtestop-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
vtestop-inv (Instr-ok2--trap _ _ _ _) ()

-- More V128-shaped ops (relop / ext-unop / ext-binop / swizzle / shuffle).
iok-vrelop : ∀ {C sh op d c} →
  Instr-ok C (VRELOP sh op) (mk-functype (mk-list d) (mk-list c)) →
  (d ≡ valtype-V128 ∷ valtype-V128 ∷ []) × (c ≡ valtype-V128 ∷ [])
iok-vrelop (vrelop _ _ _) = refl , refl

iok-vextunop : ∀ {C s1 s2 op d c} →
  Instr-ok C (VEXTUNOP s1 s2 op) (mk-functype (mk-list d) (mk-list c)) →
  (d ≡ valtype-V128 ∷ []) × (c ≡ valtype-V128 ∷ [])
iok-vextunop (vextunop _ _ _ _) = refl , refl

iok-vextbinop : ∀ {C s1 s2 op d c} →
  Instr-ok C (VEXTBINOP s1 s2 op) (mk-functype (mk-list d) (mk-list c)) →
  (d ≡ valtype-V128 ∷ valtype-V128 ∷ []) × (c ≡ valtype-V128 ∷ [])
iok-vextbinop (vextbinop _ _ _ _) = refl , refl

iok-vswizzle : ∀ {C sh d c} →
  Instr-ok C (VSWIZZLE sh) (mk-functype (mk-list d) (mk-list c)) →
  (d ≡ valtype-V128 ∷ valtype-V128 ∷ []) × (c ≡ valtype-V128 ∷ [])
iok-vswizzle (vswizzle _ _) = refl , refl

iok-vshuffle : ∀ {C sh ls d c} →
  Instr-ok C (VSHUFFLE sh ls) (mk-functype (mk-list d) (mk-list c)) →
  (d ≡ valtype-V128 ∷ valtype-V128 ∷ []) × (c ≡ valtype-V128 ∷ [])
iok-vshuffle (vshuffle _ _ _ _) = refl , refl

vrelop-inv : ∀ {s C e d c sh op} →
  Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) →
  e ≡ admininstr-VRELOP sh op →
  (d ≡ valtype-V128 ∷ valtype-V128 ∷ []) × (c ≡ valtype-V128 ∷ [])
vrelop-inv (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-vrelop iok
vrelop-inv (label _ _ _ _ _ _ _ _ _ _) ()
vrelop-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
vrelop-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
vrelop-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
vrelop-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
vrelop-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
vrelop-inv (Instr-ok2--trap _ _ _ _) ()

vextunop-inv : ∀ {s C e d c s1 s2 op} →
  Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) →
  e ≡ admininstr-VEXTUNOP s1 s2 op →
  (d ≡ valtype-V128 ∷ []) × (c ≡ valtype-V128 ∷ [])
vextunop-inv (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-vextunop iok
vextunop-inv (label _ _ _ _ _ _ _ _ _ _) ()
vextunop-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
vextunop-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
vextunop-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
vextunop-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
vextunop-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
vextunop-inv (Instr-ok2--trap _ _ _ _) ()

vextbinop-inv : ∀ {s C e d c s1 s2 op} →
  Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) →
  e ≡ admininstr-VEXTBINOP s1 s2 op →
  (d ≡ valtype-V128 ∷ valtype-V128 ∷ []) × (c ≡ valtype-V128 ∷ [])
vextbinop-inv (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-vextbinop iok
vextbinop-inv (label _ _ _ _ _ _ _ _ _ _) ()
vextbinop-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
vextbinop-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
vextbinop-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
vextbinop-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
vextbinop-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
vextbinop-inv (Instr-ok2--trap _ _ _ _) ()

vswizzle-inv : ∀ {s C e d c sh} →
  Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) →
  e ≡ admininstr-VSWIZZLE sh →
  (d ≡ valtype-V128 ∷ valtype-V128 ∷ []) × (c ≡ valtype-V128 ∷ [])
vswizzle-inv (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-vswizzle iok
vswizzle-inv (label _ _ _ _ _ _ _ _ _ _) ()
vswizzle-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
vswizzle-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
vswizzle-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
vswizzle-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
vswizzle-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
vswizzle-inv (Instr-ok2--trap _ _ _ _) ()

vshuffle-inv : ∀ {s C e d c sh ls} →
  Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) →
  e ≡ admininstr-VSHUFFLE sh ls →
  (d ≡ valtype-V128 ∷ valtype-V128 ∷ []) × (c ≡ valtype-V128 ∷ [])
vshuffle-inv (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-vshuffle iok
vshuffle-inv (label _ _ _ _ _ _ _ _ _ _) ()
vshuffle-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
vshuffle-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
vshuffle-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
vshuffle-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
vshuffle-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
vshuffle-inv (Instr-ok2--trap _ _ _ _) ()

-- progress-specific: extract the typing's laneidx bound Forall.
iok-vshuffle-p : ∀ {C sh ls d c} →
  Instr-ok C (VSHUFFLE sh ls) (mk-functype (mk-list d) (mk-list c)) →
  Forall (λ i → proj-uN-0 8 i < 2 * coerce {B = ℕ} (fun-dim (shape-ishape sh))) ls
iok-vshuffle-p (vshuffle _ _ _ fa) = fa

vshuffle-inv-p : ∀ {s C e d c sh ls} →
  Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) → e ≡ admininstr-VSHUFFLE sh ls →
  Forall (λ i → proj-uN-0 8 i < 2 * coerce {B = ℕ} (fun-dim (shape-ishape sh))) ls
vshuffle-inv-p (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-vshuffle-p iok
vshuffle-inv-p (label _ _ _ _ _ _ _ _ _ _) ()
vshuffle-inv-p (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
vshuffle-inv-p (Instr-ok2--call-addr _ _ _ _ _ _) ()
vshuffle-inv-p (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
vshuffle-inv-p (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
vshuffle-inv-p (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
vshuffle-inv-p (Instr-ok2--trap _ _ _ _) ()

-- Remaining shaped-SIMD inversions (shift / bitmask / narrow / cvtop /
-- splat / replace-lane).  All have V128/I32-fixed typing shapes.
iok-vshiftop : ∀ {C sh op d c} →
  Instr-ok C (VSHIFTOP sh op) (mk-functype (mk-list d) (mk-list c)) →
  (d ≡ valtype-V128 ∷ valtype-I32 ∷ []) × (c ≡ valtype-V128 ∷ [])
iok-vshiftop (vshiftop _ _ _) = refl , refl

iok-vbitmask : ∀ {C sh d c} →
  Instr-ok C (VBITMASK sh) (mk-functype (mk-list d) (mk-list c)) →
  (d ≡ valtype-V128 ∷ []) × (c ≡ valtype-I32 ∷ [])
iok-vbitmask (vbitmask _ _) = refl , refl

iok-vnarrow : ∀ {C s1 s2 sx d c} →
  Instr-ok C (VNARROW s1 s2 sx) (mk-functype (mk-list d) (mk-list c)) →
  (d ≡ valtype-V128 ∷ valtype-V128 ∷ []) × (c ≡ valtype-V128 ∷ [])
iok-vnarrow (vnarrow _ _ _ _) = refl , refl

iok-vcvtop : ∀ {C s1 s2 op d c} →
  Instr-ok C (VCVTOP s1 s2 op) (mk-functype (mk-list d) (mk-list c)) →
  (d ≡ valtype-V128 ∷ []) × (c ≡ valtype-V128 ∷ [])
iok-vcvtop (Instr-ok--vcvtop _ _ _ _) = refl , refl

iok-vsplat : ∀ {C sh d c} →
  Instr-ok C (VSPLAT sh) (mk-functype (mk-list d) (mk-list c)) →
  Σ valtype λ a → (d ≡ a ∷ []) × (c ≡ valtype-V128 ∷ [])
iok-vsplat (vsplat _ sh) = valtype-numtype (shunpack sh) , refl , refl

iok-vreplace : ∀ {C sh i d c} →
  Instr-ok C (VREPLACE-LANE sh i) (mk-functype (mk-list d) (mk-list c)) →
  Σ valtype λ a → (d ≡ valtype-V128 ∷ a ∷ []) × (c ≡ valtype-V128 ∷ [])
iok-vreplace (vreplace-lane _ sh i _) = valtype-numtype (shunpack sh) , refl , refl

vshiftop-inv : ∀ {s C e d c sh op} →
  Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) → e ≡ admininstr-VSHIFTOP sh op →
  (d ≡ valtype-V128 ∷ valtype-I32 ∷ []) × (c ≡ valtype-V128 ∷ [])
vshiftop-inv (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-vshiftop iok
vshiftop-inv (label _ _ _ _ _ _ _ _ _ _) ()
vshiftop-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
vshiftop-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
vshiftop-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
vshiftop-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
vshiftop-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
vshiftop-inv (Instr-ok2--trap _ _ _ _) ()

vbitmask-inv : ∀ {s C e d c sh} →
  Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) → e ≡ admininstr-VBITMASK sh →
  (d ≡ valtype-V128 ∷ []) × (c ≡ valtype-I32 ∷ [])
vbitmask-inv (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-vbitmask iok
vbitmask-inv (label _ _ _ _ _ _ _ _ _ _) ()
vbitmask-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
vbitmask-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
vbitmask-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
vbitmask-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
vbitmask-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
vbitmask-inv (Instr-ok2--trap _ _ _ _) ()

vnarrow-inv : ∀ {s C e d c s1 s2 sx} →
  Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) → e ≡ admininstr-VNARROW s1 s2 sx →
  (d ≡ valtype-V128 ∷ valtype-V128 ∷ []) × (c ≡ valtype-V128 ∷ [])
vnarrow-inv (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-vnarrow iok
vnarrow-inv (label _ _ _ _ _ _ _ _ _ _) ()
vnarrow-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
vnarrow-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
vnarrow-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
vnarrow-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
vnarrow-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
vnarrow-inv (Instr-ok2--trap _ _ _ _) ()

vcvtop-inv : ∀ {s C e d c s1 s2 op} →
  Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) → e ≡ admininstr-VCVTOP s1 s2 op →
  (d ≡ valtype-V128 ∷ []) × (c ≡ valtype-V128 ∷ [])
vcvtop-inv (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-vcvtop iok
vcvtop-inv (label _ _ _ _ _ _ _ _ _ _) ()
vcvtop-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
vcvtop-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
vcvtop-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
vcvtop-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
vcvtop-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
vcvtop-inv (Instr-ok2--trap _ _ _ _) ()

vsplat-inv : ∀ {s C e d c sh} →
  Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) → e ≡ admininstr-VSPLAT sh →
  Σ valtype λ a → (d ≡ a ∷ []) × (c ≡ valtype-V128 ∷ [])
vsplat-inv (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-vsplat iok
vsplat-inv (label _ _ _ _ _ _ _ _ _ _) ()
vsplat-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
vsplat-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
vsplat-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
vsplat-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
vsplat-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
vsplat-inv (Instr-ok2--trap _ _ _ _) ()

vreplace-inv : ∀ {s C e d c sh i} →
  Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) → e ≡ admininstr-VREPLACE-LANE sh i →
  Σ valtype λ a → (d ≡ valtype-V128 ∷ a ∷ []) × (c ≡ valtype-V128 ∷ [])
vreplace-inv (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-vreplace iok
vreplace-inv (label _ _ _ _ _ _ _ _ _ _) ()
vreplace-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
vreplace-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
vreplace-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
vreplace-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
vreplace-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
vreplace-inv (Instr-ok2--trap _ _ _ _) ()

iok-vextract : ∀ {C sh sxo i d c} →
  Instr-ok C (VEXTRACT-LANE sh sxo i) (mk-functype (mk-list d) (mk-list c)) →
  (d ≡ valtype-V128 ∷ []) × (c ≡ valtype-numtype (shunpack sh) ∷ [])
iok-vextract (vextract-lane _ _ _ _ _) = refl , refl

vextract-inv : ∀ {s C e d c sh sxo i} →
  Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) → e ≡ admininstr-VEXTRACT-LANE sh sxo i →
  (d ≡ valtype-V128 ∷ []) × (c ≡ valtype-numtype (shunpack sh) ∷ [])
vextract-inv (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-vextract iok
vextract-inv (label _ _ _ _ _ _ _ _ _ _) ()
vextract-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
vextract-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
vextract-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
vextract-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
vextract-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
vextract-inv (Instr-ok2--trap _ _ _ _) ()

-- progress-specific inversions: expose the concrete lane numtype and the fun-dim bound
iok-vsplat-p : ∀ {C sh d c} →
  Instr-ok C (VSPLAT sh) (mk-functype (mk-list d) (mk-list c)) →
  (d ≡ valtype-numtype (shunpack sh) ∷ []) × (c ≡ valtype-V128 ∷ [])
iok-vsplat-p (vsplat _ sh) = refl , refl

vsplat-inv-p : ∀ {s C e d c sh} →
  Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) → e ≡ admininstr-VSPLAT sh →
  (d ≡ valtype-numtype (shunpack sh) ∷ []) × (c ≡ valtype-V128 ∷ [])
vsplat-inv-p (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-vsplat-p iok
vsplat-inv-p (label _ _ _ _ _ _ _ _ _ _) ()
vsplat-inv-p (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
vsplat-inv-p (Instr-ok2--call-addr _ _ _ _ _ _) ()
vsplat-inv-p (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
vsplat-inv-p (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
vsplat-inv-p (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
vsplat-inv-p (Instr-ok2--trap _ _ _ _) ()

iok-vreplace-p : ∀ {C sh i d c} →
  Instr-ok C (VREPLACE-LANE sh i) (mk-functype (mk-list d) (mk-list c)) →
  (d ≡ valtype-V128 ∷ valtype-numtype (shunpack sh) ∷ []) × (c ≡ valtype-V128 ∷ [])
iok-vreplace-p (vreplace-lane _ _ _ _) = refl , refl

vreplace-inv-p : ∀ {s C e d c sh i} →
  Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) → e ≡ admininstr-VREPLACE-LANE sh i →
  (d ≡ valtype-V128 ∷ valtype-numtype (shunpack sh) ∷ []) × (c ≡ valtype-V128 ∷ [])
vreplace-inv-p (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-vreplace-p iok
vreplace-inv-p (label _ _ _ _ _ _ _ _ _ _) ()
vreplace-inv-p (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
vreplace-inv-p (Instr-ok2--call-addr _ _ _ _ _ _) ()
vreplace-inv-p (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
vreplace-inv-p (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
vreplace-inv-p (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
vreplace-inv-p (Instr-ok2--trap _ _ _ _) ()

iok-vextract-p : ∀ {C sh sxo i d c} →
  Instr-ok C (VEXTRACT-LANE sh sxo i) (mk-functype (mk-list d) (mk-list c)) →
  (d ≡ valtype-V128 ∷ []) × (proj-uN-0 8 i < coerce {B = ℕ} (fun-dim sh))
iok-vextract-p (vextract-lane _ _ _ _ bnd) = refl , bnd

vextract-inv-p : ∀ {s C e d c sh sxo i} →
  Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) → e ≡ admininstr-VEXTRACT-LANE sh sxo i →
  (d ≡ valtype-V128 ∷ []) × (proj-uN-0 8 i < coerce {B = ℕ} (fun-dim sh))
vextract-inv-p (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-vextract-p iok
vextract-inv-p (label _ _ _ _ _ _ _ _ _ _) ()
vextract-inv-p (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
vextract-inv-p (Instr-ok2--call-addr _ _ _ _ _ _) ()
vextract-inv-p (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
vextract-inv-p (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
vextract-inv-p (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
vextract-inv-p (Instr-ok2--trap _ _ _ _) ()

iok-return : ∀ {C d c} →
  Instr-ok C RETURN (mk-functype (mk-list d) (mk-list c)) →
  Σ (List valtype × List valtype) λ (t1 , tr) → (d ≡ t1 ++ tr) ×
  (context-RETURN C ≡ just (mk-list tr))
iok-return (return _ t1 tr _ req) = (t1 , tr) , refl , req

return-inv : ∀ {s C e d c} →
  Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) →
  e ≡ admininstr-RETURN →
  Σ (List valtype × List valtype) λ (t1 , tr) → (d ≡ t1 ++ tr) ×
  (context-RETURN C ≡ just (mk-list tr))
return-inv (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-return iok
return-inv (label _ _ _ _ _ _ _ _ _ _) ()
return-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
return-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
return-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
return-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
return-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
return-inv (Instr-ok2--trap _ _ _ _) ()

-- CALL-ADDR / funcinst machinery (for call-addr preservation).
calladdr-inv : ∀ {s C e d c a} →
  Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) →
  e ≡ CALL-ADDR a →
  Externaddr-ok s (externaddr-FUNC a) (FUNC (mk-functype (mk-list d) (mk-list c)))
calladdr-inv (plain _ _ i _ _ iok) eq = refute-plain eq refl
calladdr-inv (label _ _ _ _ _ _ _ _ _ _) ()
calladdr-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
calladdr-inv (Instr-ok2--call-addr _ _ _ _ _ xa) refl = xa
calladdr-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
calladdr-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
calladdr-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
calladdr-inv (Instr-ok2--trap _ _ _ _) ()

xa-func-inv : ∀ {s a ft} →
  Externaddr-ok s (externaddr-FUNC a) (FUNC ft) →
  (a < length (store-FUNCS s)) × (funcinst-TYPE ((store-FUNCS s) [ a ]!) ≡ ft)
xa-func-inv (Externaddr-ok--func _ a fi a< lk) = a< , cong funcinst-TYPE lk
xa-func-inv (Externaddr-ok--sub _ _ _ _ ok'
  (Externtype-sub--func _ _ (mk-Functype-sub _))) = xa-func-inv ok'

finst-type-eq : ∀ {s fi ftv} → Funcinst-ok s fi ftv → funcinst-TYPE fi ≡ ftv
finst-type-eq (mk-Funcinst-ok _ ft mm fc Cf ftok mok fk) = refl

-- Lookup a well-typed funcinst out of Store-ok.
sfok : ∀ {s} → Store-ok s → ∀ {a} → a < length (store-FUNCS s) →
  Funcinst-ok s ((store-FUNCS s) [ a ]!) (funcinst-TYPE ((store-FUNCS s) [ a ]!))
sfok {s} (mk-Store-ok _ gil gtl mil mtl til ttl fil ftl dil dtl eil etl
           glen gok mlen mok tlen tok flen fok dlen dok elen eok seqEq) {a} a< =
  let funcs-eq = cong store-FUNCS seqEq
      a<fil = subst (a <_) (cong length funcs-eq) a<
      flook = pw-lookup fok a<fil
      flook' = subst (λ fi → Funcinst-ok s fi (ftl [ a ]!))
                     (sym (cong (_[ a ]!) funcs-eq)) flook
  in subst (Funcinst-ok s ((store-FUNCS s) [ a ]!))
           (sym (finst-type-eq flook')) flook'

tinst-type-eq : ∀ {s ti tt} → Tableinst-ok s ti tt → tableinst-TYPE ti ≡ tt
tinst-type-eq (mk-Tableinst-ok _ n mo rt refs ttok fr leneq) = refl

-- Lookup a well-typed tableinst out of Store-ok.
stok : ∀ {s} → Store-ok s → ∀ {a} → a < length (store-TABLES s) →
  Tableinst-ok s ((store-TABLES s) [ a ]!) (tableinst-TYPE ((store-TABLES s) [ a ]!))
stok {s} (mk-Store-ok _ gil gtl mil mtl til ttl fil ftl dil dtl eil etl
           glen gok mlen mok tlen tok flen fok dlen dok elen eok seqEq) {a} a< =
  let tables-eq = cong store-TABLES seqEq
      a<til = subst (a <_) (cong length tables-eq) a<
      tlook = pw-lookup tok a<til
      tlook' = subst (λ ti → Tableinst-ok s ti (ttl [ a ]!))
                     (sym (cong (_[ a ]!) tables-eq)) tlook
  in subst (Tableinst-ok s ((store-TABLES s) [ a ]!))
           (sym (tinst-type-eq tlook')) tlook'

minst-type-eq : ∀ {s mi mt} → Meminst-ok s mi mt → meminst-TYPE mi ≡ mt
minst-type-eq (mk-Meminst-ok _ n mo b mtok leneq) = refl

-- Extract the page-count invariant (mi a variable here ⇒ the constructor split succeeds, unlike at
-- an abstract store lookup).
meminst-pages : ∀ {s mi mt} → Meminst-ok s mi mt → Σ ℕ λ v-n → length (BYTES mi) ≡ v-n * (64 * Ki)
meminst-pages (mk-Meminst-ok _ v-n mo b mtok leneq) = v-n , leneq

-- Lookup a well-typed meminst out of Store-ok (mirrors stok).
smok : ∀ {s} → Store-ok s → ∀ {a} → a < length (store-MEMS s) →
  Meminst-ok s ((store-MEMS s) [ a ]!) (meminst-TYPE ((store-MEMS s) [ a ]!))
smok {s} (mk-Store-ok _ gil gtl mil mtl til ttl fil ftl dil dtl eil etl
           glen gok mlen mok tlen tok flen fok dlen dok elen eok seqEq) {a} a< =
  let mems-eq = cong store-MEMS seqEq
      a<mil = subst (a <_) (cong length mems-eq) a<
      mlook = pw-lookup mok a<mil
      mlook' = subst (λ mi → Meminst-ok s mi (mtl [ a ]!))
                     (sym (cong (_[ a ]!) mems-eq)) mlook
  in subst (Meminst-ok s ((store-MEMS s) [ a ]!))
           (sym (minst-type-eq mlook')) mlook'

table-ref-at : ∀ {s ti lim rt i} → Tableinst-ok s ti (mk-tabletype lim rt) →
  i < length (REFS ti) → Ref-ok s (REFS ti [ i ]!) rt
table-ref-at (mk-Tableinst-ok _ n mo rt refs ttok fr leneq) i< = all-lookup fr i<

elem-ref-at : ∀ {s ei rt i} → Eleminst-ok s ei rt →
  i < length (eleminst-REFS ei) → Ref-ok s (eleminst-REFS ei [ i ]!) rt
elem-ref-at (mk-Eleminst-ok _ rt refs fr) i< = all-lookup fr i<

local-inj : ∀ {a b} → LOCAL a ≡ LOCAL b → a ≡ b
local-inj refl = refl

map-LOCAL-inj : ∀ (a b : List valtype) →
  map (λ t → LOCAL t) a ≡ map (λ t → LOCAL t) b → a ≡ b
map-LOCAL-inj [] [] _ = refl
map-LOCAL-inj [] (_ ∷ _) ()
map-LOCAL-inj (_ ∷ _) [] ()
map-LOCAL-inj (x ∷ a) (y ∷ b) eq with ∷-injective eq
... | eqh , eqt = cong₂ _∷_ (local-inj eqh) (map-LOCAL-inj a b eqt)

mk-list-inj : ∀ {A : Set} {a b : List A} →
  mk-list a ≡ mk-list b → a ≡ b
mk-list-inj refl = refl

func-FUNC-inj : ∀ {a b c a' b' c'} → func-FUNC a b c ≡ func-FUNC a' b' c' →
  (a ≡ a') × (b ≡ b') × (c ≡ c')
func-FUNC-inj refl = refl , refl , refl

func-ok-inv : ∀ {Cf fn t1 t2} →
  Func-ok Cf fn (mk-functype (mk-list t1) (mk-list t2)) →
  ∀ {x tloc body} → fn ≡ func-FUNC x (map (λ t → LOCAL t) tloc) body →
  Forall (λ t → t ≢ BOT) tloc ×
  Expr-ok (Cf ⧺ record
    { context-TYPES = [] ; context-FUNCS = [] ; context-GLOBALS = []
    ; context-TABLES = [] ; context-MEMS = [] ; context-ELEMS = []
    ; context-DATAS = [] ; context-LOCALS = (t1 ++ tloc)
    ; LABELS = (mk-list t2 ∷ []) ; context-RETURN = (just (mk-list t2)) })
    body (mk-list t2)
func-ok-inv (mk-Func-ok _ x' tloc' vexpr _ _ x< tlkp nb exok) eq
  with func-FUNC-inj eq
... | xeq , beq , ceq with map-LOCAL-inj tloc' _ beq | ceq
... | refl | refl = nb , exok

expr-ok-instrs : ∀ {C es ts} → Expr-ok C es (mk-list ts) →
  Instrs-ok C es (mk-functype (mk-list []) (mk-list ts))
expr-ok-instrs (mk-Expr-ok _ _ _ d) = d

default-ok : ∀ {s} (t : valtype) → default- t ≢ nothing →
  Val-ok s (unwrap! (default- t)) t
default-ok valtype-I32 _ = Val-ok--numtype _ I32 (mk-uN 0)
default-ok valtype-I64 _ = Val-ok--numtype _ I64 (mk-uN 0)
default-ok valtype-F32 _ = Val-ok--numtype _ F32 (fzero 32)
default-ok valtype-F64 _ = Val-ok--numtype _ F64 (fzero 64)
default-ok valtype-V128 _ = Val-ok--vectype _ V128 (mk-uN 0)
default-ok valtype-FUNCREF _ =
  Val-ok--reftype _ (ref-REF-NULL FUNCREF) FUNCREF (null _ FUNCREF)
default-ok valtype-EXTERNREF _ =
  Val-ok--reftype _ (ref-REF-NULL EXTERNREF) EXTERNREF (null _ EXTERNREF)
default-ok BOT h = ⊥-elim (h refl)

defaults-ok : ∀ {s} (tloc : List valtype) →
  Forall (λ t → default- t ≢ nothing) tloc →
  Forall₂ (λ t v → Val-ok s v t) tloc (map (λ t → unwrap! (default- t)) tloc)
defaults-ok [] [] = []
defaults-ok (t ∷ ts) (h ∷ hs) = default-ok t h ∷ defaults-ok ts hs

label-inv : ∀ {s C e d c vn cont body} →
  Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) →
  e ≡ LABEL- vn cont body →
  (d ≡ []) × (Σ (List valtype) λ t' →
    (length t' ≡ vn) ×
    Instrs-ok2 s C (map (λ i → admininstr-instr i) cont)
      (mk-functype (mk-list t') (mk-list c)) ×
    Instrs-ok2 s (labC t' ⧺ C) body (mk-functype (mk-list []) (mk-list c)))
label-inv (plain _ _ i _ _ iok) eq = refute-plain eq refl
label-inv (label _ _ _ _ _ _ t' lenq contTy bodyTy) refl =
  refl , t' , lenq , contTy , bodyTy
label-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
label-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
label-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
label-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
label-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
label-inv (Instr-ok2--trap _ _ _ _) ()

-- Return-context extension used by the (now W3C-faithful) frame rule.
retC : List valtype → context
retC ts = record
  { context-TYPES = [] ; context-FUNCS = [] ; context-GLOBALS = []
  ; context-TABLES = [] ; context-MEMS = [] ; context-ELEMS = []
  ; context-DATAS = [] ; context-LOCALS = []
  ; LABELS = [] ; context-RETURN = just (mk-list ts) }

frame-inv : ∀ {s C e d c vn fr body} →
  Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) →
  e ≡ FRAME- vn fr body →
  (d ≡ []) × (length c ≡ vn) ×
  (Σ context λ C' → Frame-ok s fr C' × Expr-ok2 s (retC c ⧺ C') body (mk-list c))
frame-inv (plain _ _ i _ _ iok) eq = refute-plain eq refl
frame-inv (label _ _ _ _ _ _ _ _ _ _) ()
frame-inv (Instr-ok2--frame _ _ _ _ _ _ C' lenq frok exok) refl =
  refl , lenq , C' , frok , exok
frame-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
frame-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
frame-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
frame-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
frame-inv (Instr-ok2--trap _ _ _ _) ()

------------------------------------------------------------------------
-- 6. Value typing: introduction and inversion.
------------------------------------------------------------------------

ref-null-rt : ∀ {s rt rt'} → Ref-ok s (ref-REF-NULL rt) rt' → rt' ≡ rt
ref-null-rt (null _ _) = refl

ref-func-rt : ∀ {s a rt'} → Ref-ok s (REF-FUNC-ADDR a) rt' → rt' ≡ FUNCREF
ref-func-rt (Ref-ok--func _ _ _ _) = refl

ref-host-rt : ∀ {s a rt'} → Ref-ok s (REF-HOST-ADDR a) rt' → rt' ≡ EXTERNREF
ref-host-rt (extern _ _) = refl

val-ok-ty : ∀ {s C v t} → Val-ok s v t →
  Instr-ok2 s C (admininstr-val v) (mk-functype (mk-list []) (mk-list (t ∷ [])))
val-ok-ty (Val-ok--numtype _ nt cn) = plain _ _ _ _ _ (const _ nt cn)
val-ok-ty (Val-ok--vectype _ V128 cn) = plain _ _ _ _ _ (vconst _ cn)
val-ok-ty (Val-ok--reftype _ (ref-REF-NULL rt') rt rok) = Instr-ok2--ref _ _ _ _ rok
val-ok-ty (Val-ok--reftype _ (REF-FUNC-ADDR a) rt rok) = Instr-ok2--ref _ _ _ _ rok
val-ok-ty (Val-ok--reftype _ (REF-HOST-ADDR a) rt rok) = Instr-ok2--ref _ _ _ _ rok

-- inversion helpers for the five value shapes
vinv-const : ∀ {s C e d c nt cn} →
  Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) →
  e ≡ admininstr-CONST nt cn → (d ≡ []) × (c ≡ valtype-numtype nt ∷ [])
vinv-const (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-const iok
vinv-const (label _ _ _ _ _ _ _ _ _ _) ()
vinv-const (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
vinv-const (Instr-ok2--call-addr _ _ _ _ _ _) ()
vinv-const (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
vinv-const (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
vinv-const (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
vinv-const (Instr-ok2--trap _ _ _ _) ()

vinv-vconst : ∀ {s C e d c vt cn} →
  Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) →
  e ≡ admininstr-VCONST vt cn → (d ≡ []) × (c ≡ valtype-V128 ∷ [])
vinv-vconst (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-vconst iok
vinv-vconst (label _ _ _ _ _ _ _ _ _ _) ()
vinv-vconst (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
vinv-vconst (Instr-ok2--call-addr _ _ _ _ _ _) ()
vinv-vconst (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
vinv-vconst (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
vinv-vconst (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
vinv-vconst (Instr-ok2--trap _ _ _ _) ()

vinv-refnull : ∀ {s C e d c rt} →
  Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) →
  e ≡ admininstr-REF-NULL rt → (d ≡ []) × (c ≡ valtype-reftype rt ∷ [])
vinv-refnull (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-refnull iok
vinv-refnull (label _ _ _ _ _ _ _ _ _ _) ()
vinv-refnull (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
vinv-refnull (Instr-ok2--call-addr _ _ _ _ _ _) ()
vinv-refnull {rt = rt} (Instr-ok2--ref _ _ (ref-REF-NULL rt') rt2 rok) refl =
  refl , cong (λ r → valtype-reftype r ∷ []) (ref-null-rt rok)
vinv-refnull (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
vinv-refnull (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
vinv-refnull (Instr-ok2--trap _ _ _ _) ()

vinv-reffunc : ∀ {s C e d c fa} →
  Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) →
  e ≡ admininstr-REF-FUNC-ADDR fa →
  (d ≡ []) × (c ≡ valtype-FUNCREF ∷ []) × Ref-ok s (REF-FUNC-ADDR fa) FUNCREF
vinv-reffunc (plain _ _ i _ _ iok) eq = refute-plain eq refl
vinv-reffunc (label _ _ _ _ _ _ _ _ _ _) ()
vinv-reffunc (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
vinv-reffunc (Instr-ok2--call-addr _ _ _ _ _ _) ()
vinv-reffunc (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
vinv-reffunc (Instr-ok2--ref _ _ (REF-FUNC-ADDR a) rt2 rok) refl
  with ref-func-rt rok
... | refl = refl , refl , rok
vinv-reffunc (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
vinv-reffunc (Instr-ok2--trap _ _ _ _) ()

vinv-refhost : ∀ {s C e d c ha} →
  Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) →
  e ≡ admininstr-REF-HOST-ADDR ha →
  (d ≡ []) × (c ≡ valtype-EXTERNREF ∷ []) × Ref-ok s (REF-HOST-ADDR ha) EXTERNREF
vinv-refhost (plain _ _ i _ _ iok) eq = refute-plain eq refl
vinv-refhost (label _ _ _ _ _ _ _ _ _ _) ()
vinv-refhost (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
vinv-refhost (Instr-ok2--call-addr _ _ _ _ _ _) ()
vinv-refhost (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
vinv-refhost (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
vinv-refhost (Instr-ok2--ref _ _ (REF-HOST-ADDR a) rt2 rok) refl
  with ref-host-rt rok
... | refl = refl , refl , rok
vinv-refhost (Instr-ok2--trap _ _ _ _) ()

val-inv : ∀ (v : val) {s C d c} →
  Instr-ok2 s C (admininstr-val v) (mk-functype (mk-list d) (mk-list c)) →
  Σ valtype λ t → (d ≡ []) × (c ≡ t ∷ []) × Val-ok s v t
val-inv (val-CONST nt cn) ok with vinv-const ok refl
... | deq , ceq = valtype-numtype nt , deq , ceq , Val-ok--numtype _ nt cn
val-inv (val-VCONST V128 cn) ok with vinv-vconst ok refl
... | deq , ceq = valtype-vectype V128 , deq , ceq , Val-ok--vectype _ V128 cn
val-inv (val-REF-NULL rt) ok with vinv-refnull ok refl
... | deq , ceq =
  valtype-reftype rt , deq , ceq , Val-ok--reftype _ (ref-REF-NULL rt) rt (null _ rt)
val-inv (val-REF-FUNC-ADDR fa) ok with vinv-reffunc ok refl
... | deq , ceq , rok =
  valtype-FUNCREF , deq , ceq , Val-ok--reftype _ (REF-FUNC-ADDR fa) FUNCREF rok
val-inv (val-REF-HOST-ADDR ha) ok with vinv-refhost ok refl
... | deq , ceq , rok =
  valtype-EXTERNREF , deq , ceq , Val-ok--reftype _ (REF-HOST-ADDR ha) EXTERNREF rok

-- Typed value singleton, in normal form.
record ValTy (s : store) (C : context) (v : val) (u1 u2 : List valtype) : Set where
  constructor mk-valty
  field
    p    : List valtype
    t    : valtype
    vok  : Val-ok s v t
    s1   : Resulttype-sub (mk-list u1) (mk-list p)
    s2   : Resulttype-sub (mk-list (p ++ t ∷ [])) (mk-list u2)

val-ty : ∀ (v : val) {s C u1 u2} →
  Instrs-ok2 s C (admininstr-val v ∷ []) (mk-functype (mk-list u1) (mk-list u2)) →
  ValTy s C v u1 u2
val-ty v ok with singleton-inv ok
... | mk-single p dm c eok s1 s2 with val-inv v eok
... | t , refl , refl , vok = mk-valty p t vok (rt-norm p s1) s2

-- Typed const singleton, keeping the numtype transparent.
const-ty : ∀ {s C nt cn u1 u2} →
  Instrs-ok2 s C (admininstr-CONST nt cn ∷ []) (mk-functype (mk-list u1) (mk-list u2)) →
  Σ (List valtype) λ p →
    Resulttype-sub (mk-list u1) (mk-list p) ×
    Resulttype-sub (mk-list (p ++ valtype-numtype nt ∷ [])) (mk-list u2)
const-ty ok with singleton-inv ok
... | mk-single p dm c eok s1 s2 with vinv-const eok refl
... | refl , refl = p , rt-norm p s1 , s2

vconst-ty : ∀ {s C cn u1 u2} →
  Instrs-ok2 s C (admininstr-VCONST V128 cn ∷ []) (mk-functype (mk-list u1) (mk-list u2)) →
  Σ (List valtype) λ p →
    Resulttype-sub (mk-list u1) (mk-list p) ×
    Resulttype-sub (mk-list (p ++ valtype-V128 ∷ [])) (mk-list u2)
vconst-ty ok with singleton-inv ok
... | mk-single p dm c eok s1 s2 with vinv-vconst eok refl
... | refl , refl = p , rt-norm p s1 , s2

-- Typed reference-value singleton (admininstr-ref is stuck on a ref
-- variable; we case-split the ref to make the injection reduce).
ref-single-ok : ∀ (r : ref) {s C u1 u2} →
  Instrs-ok2 s C (admininstr-ref r ∷ []) (mk-functype (mk-list u1) (mk-list u2)) →
  Σ reftype λ rt → Σ (List valtype) λ p → Ref-ok s r rt ×
    Resulttype-sub (mk-list u1) (mk-list p) ×
    Resulttype-sub (mk-list (p ++ valtype-reftype rt ∷ [])) (mk-list u2)
ref-single-ok (ref-REF-NULL rt0) ok with singleton-inv ok
... | mk-single p dm c eok s1 s2 with vinv-refnull eok refl
... | refl , refl = rt0 , p , null _ rt0 , rt-norm p s1 , s2
ref-single-ok (REF-FUNC-ADDR a) ok with singleton-inv ok
... | mk-single p dm c eok s1 s2 with vinv-reffunc eok refl
... | refl , refl , rok = FUNCREF , p , rok , rt-norm p s1 , s2
ref-single-ok (REF-HOST-ADDR ha) ok with singleton-inv ok
... | mk-single p dm c eok s1 s2 with vinv-refhost eok refl
... | refl , refl , rok = EXTERNREF , p , rok , rt-norm p s1 , s2

-- Values are never typed at BOT, so subtyping degenerates to equality.
val-not-bot : ∀ {s v t} → Val-ok s v t → t ≡ BOT → ⊥
val-not-bot (Val-ok--numtype _ I32 _) ()
val-not-bot (Val-ok--numtype _ I64 _) ()
val-not-bot (Val-ok--numtype _ F32 _) ()
val-not-bot (Val-ok--numtype _ F64 _) ()
val-not-bot (Val-ok--vectype _ V128 _) ()
val-not-bot (Val-ok--reftype _ _ FUNCREF _) ()
val-not-bot (Val-ok--reftype _ _ EXTERNREF _) ()

vt-sub-val : ∀ {s v t t'} → Val-ok s v t → Valtype-sub t t' → t' ≡ t
vt-sub-val vok (refl' _) = refl
vt-sub-val vok (bot _) = ⊥-elim (val-not-bot vok refl)

pw-val-sub : ∀ {s ts t1 vs} →
  Forall₂ (λ t v → Val-ok s v t) ts vs →
  Pointwise Valtype-sub ts t1 →
  Forall₂ (λ t v → Val-ok s v t) t1 vs
pw-val-sub [] [] = []
pw-val-sub (vok ∷ pw) (sb ∷ sbs) =
  subst (Val-ok _ _) (sym (vt-sub-val vok sb)) vok ∷ pw-val-sub pw sbs

-- Value rows: intro and inversion (needed by every LABEL-/FRAME-/block
-- rule).  This is the "value-row lemma" attempt #1 could not state.
row-intro : ∀ {s C ts vs} → Forall₂ (λ t v → Val-ok s v t) ts vs →
  Instrs-ok2 s C (map (λ w → admininstr-val w) vs)
    (mk-functype (mk-list []) (mk-list ts))
row-intro [] = Instrs-ok2--empty _ _
row-intro {ts = t ∷ ts'} {vs = v ∷ vs'} (vok ∷ pw) =
  Instrs-ok2--seq _ _ (admininstr-val v ∷ []) (map (λ w → admininstr-val w) vs') _ _ _
    (Instrs-ok2--instr _ _ _ _ _ (val-ok-ty vok))
    (Instrs-ok2--frame _ _ _ (t ∷ []) _ _ (row-intro pw))

row-inv : ∀ (vs : List val) {s C u1 u2} →
  Instrs-ok2 s C (map (λ w → admininstr-val w) vs)
    (mk-functype (mk-list u1) (mk-list u2)) →
  Σ (List valtype) λ ts →
    Forall₂ (λ t v → Val-ok s v t) ts vs ×
    Resulttype-sub (mk-list (u1 ++ ts)) (mk-list u2)
row-inv [] {u1 = u1} ok =
  [] , [] ,
  subst (λ l → Resulttype-sub (mk-list l) _) (sym (++-identityʳ u1))
        (empty-inv ok refl)
row-inv (v ∷ vs) {u1 = u1} ok
  with decomp ok (admininstr-val v ∷ []) (map (λ w → admininstr-val w) vs) refl
... | mk-split m okV okR with val-ty v okV | row-inv vs okR
... | mk-valty p t vok s1 s2 | (ts' , pw , sub') =
  (t ∷ ts') , (vok ∷ pw) ,
  subst (λ l → Resulttype-sub (mk-list l) _) (++-assoc u1 (t ∷ []) ts')
    (rt-sub-trans (rt-sub-app (rt-sub-app s1 (rt-sub-refl (t ∷ []))) (rt-sub-refl ts'))
      (rt-sub-trans (rt-sub-app s2 (rt-sub-refl ts')) sub'))

------------------------------------------------------------------------
-- 7. Store-extension reflexivity (needed to state preservation-with-
--    extension for the store-preserving steps).  Fully proved.
------------------------------------------------------------------------

ext-g-refl : ∀ (gi : globalinst) → Extend-globalinst gi gi
ext-g-refl (mk-globalinst (mk-globaltype mu t) v) =
  mk-Extend-globalinst mu t v v (inj₂ refl)

ext-m-refl : ∀ (mi : meminst) → Extend-meminst mi mi
ext-m-refl (mk-meminst (PAGE (mk-limits (mk-uN k) nothing)) bs) =
  mk-Extend-meminst k nothing bs k bs ≤-refl ≤-refl
ext-m-refl (mk-meminst (PAGE (mk-limits (mk-uN k) (just (mk-uN j)))) bs) =
  mk-Extend-meminst k (just j) bs k bs ≤-refl ≤-refl

ext-t-refl : ∀ (ti : tableinst) → Extend-tableinst ti ti
ext-t-refl (mk-tableinst (mk-tabletype (mk-limits (mk-uN k) nothing) rt) refs) =
  mk-Extend-tableinst k nothing rt refs k refs ≤-refl ≤-refl
ext-t-refl (mk-tableinst (mk-tabletype (mk-limits (mk-uN k) (just (mk-uN j))) rt) refs) =
  mk-Extend-tableinst k (just j) rt refs k refs ≤-refl ≤-refl

ext-f-refl : ∀ (fi : funcinst) → Extend-funcinst fi fi
ext-f-refl (mk-funcinst ft mm code) = mk-Extend-funcinst ft mm code

ext-d-refl : ∀ (di : datainst) → Extend-datainst di di
ext-d-refl (mk-datainst bs) = mk-Extend-datainst bs bs (inj₁ refl)

ext-e-refl : ∀ (ei : eleminst) → Extend-eleminst ei ei
ext-e-refl (mk-eleminst rt refs) = mk-Extend-eleminst rt refs refs (inj₁ refl)

extend-store-refl : ∀ s → Extend-store s s
extend-store-refl s = mk-Extend-store s s
  (all-upto _ (λ a a< → a<)) (all-upto _ (λ a a< → a<))
  (all-upto _ (λ a a< → ext-g-refl _))
  (all-upto _ (λ a a< → a<)) (all-upto _ (λ a a< → a<))
  (all-upto _ (λ a a< → ext-m-refl _))
  (all-upto _ (λ a a< → a<)) (all-upto _ (λ a a< → a<))
  (all-upto _ (λ a a< → ext-t-refl _))
  (all-upto _ (λ a a< → a<)) (all-upto _ (λ a a< → a<))
  (all-upto _ (λ a a< → ext-f-refl _))
  (all-upto _ (λ a a< → a<)) (all-upto _ (λ a a< → a<))
  (all-upto _ (λ a a< → ext-d-refl _))
  (all-upto _ (λ a a< → a<)) (all-upto _ (λ a a< → a<))
  (all-upto _ (λ a a< → ext-e-refl _))

------------------------------------------------------------------------
-- 8. Frame / store lookup facts.
------------------------------------------------------------------------

record FrameFacts (s : store) (f : frame) (C : context) : Set where
  constructor mk-ff
  field
    lts        : List valtype
    locals-eq  : context-LOCALS C ≡ lts
    locals-len : length lts ≡ length (LOCALS f)
    locals-ok  : Forall₂ (λ t v → Val-ok s v t) lts (LOCALS f)
    gts        : List globaltype
    globals-eq : context-GLOBALS C ≡ gts
    gaddrs-len : length (GLOBALS (frame-MODULE f)) ≡ length gts
    globals-ok : Forall₂ (λ ga gt → Externaddr-ok s (externaddr-GLOBAL ga) (GLOBAL gt))
                   (GLOBALS (frame-MODULE f)) gts
    fts        : List functype
    funcs-eq   : context-FUNCS C ≡ fts
    faddrs-len : length (FUNCS (frame-MODULE f)) ≡ length fts
    funcs-ok   : Forall₂ (λ fa ft → Externaddr-ok s (externaddr-FUNC fa) (FUNC ft))
                   (FUNCS (frame-MODULE f)) fts
    tts        : List tabletype
    tables-eq  : context-TABLES C ≡ tts
    taddrs-len : length (TABLES (frame-MODULE f)) ≡ length tts
    tables-ok  : Forall₂ (λ ta tt → Externaddr-ok s (externaddr-TABLE ta) (TABLE tt))
                   (TABLES (frame-MODULE f)) tts
    ets        : List elemtype
    elems-eq   : context-ELEMS C ≡ ets
    eaddrs-len : length (ELEMS (frame-MODULE f)) ≡ length ets
    elems-ok   : Forall₂ (λ ea et → Eleminst-ok s ((store-ELEMS s) [ ea ]!) et)
                   (ELEMS (frame-MODULE f)) ets
    mts        : List memtype
    mems-eq    : context-MEMS C ≡ mts
    maddrs-len : length (MEMS (frame-MODULE f)) ≡ length mts
    mems-ok    : Forall₂ (λ ma mt → Externaddr-ok s (externaddr-MEM ma) (MEM mt))
                   (MEMS (frame-MODULE f)) mts
    types-eq   : context-TYPES C ≡ TYPES (frame-MODULE f)
    ret-nothing : context-RETURN C ≡ nothing
    locals-rebuild : ∀ vals' → length lts ≡ length vals' →
      Forall₂ (λ t v → Val-ok s v t) lts vals' →
      Frame-ok s (record f { LOCALS = vals' }) C

frame-facts : ∀ {s f C} → Frame-ok s f C → FrameFacts s f C
frame-facts (mk-Frame-ok _ val-lst _ _ t-lst
  mok@(mk-Moduleinst-ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
       _ glen gok flen2 fok5 mlen3 mok3 tlen4 tok9 _ _ _ _ elen _ eok _ _ _)
  len-eq vals-ok) =
  mk-ff t-lst refl len-eq vals-ok _ (++-identityʳ _) glen gok
    _ (++-identityʳ _) flen2 fok5
    _ (++-identityʳ _) tlen4 tok9
    _ (++-identityʳ _) elen eok
    _ (++-identityʳ _) mlen3 mok3
    (++-identityʳ _) refl
    (λ vals' len' pw → mk-Frame-ok _ vals' _ _ _ mok len' pw)

-- The frame context has no labels (module context LABELS = [] and the frame
-- extension adds none) and no return type — used to refute a BR/RETURN that
-- reaches the closed top-level (no enclosing LABEL-/FRAME-).
frame-labels-empty : ∀ {s f C} → Frame-ok s f C → LABELS C ≡ []
frame-labels-empty (mk-Frame-ok _ _ _ _ _
  (mk-Moduleinst-ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
   _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _) = refl

-- The declarative Blocktype-ok agrees with the algorithmic
-- fun-blocktype used by the reduction rules, given that the frame's
-- module types coincide with the context types (from Moduleinst-ok).
blocktype-agree : ∀ {s f C bt ft} → Blocktype-ok C bt ft →
  context-TYPES C ≡ TYPES (frame-MODULE f) →
  fun-blocktype (mk-state s f) bt ≡ ft
blocktype-agree (Blocktype-ok--valtype _ nothing) _ = refl
blocktype-agree (Blocktype-ok--valtype _ (just t)) _ = refl
blocktype-agree (Blocktype-ok--typeidx _ x t1 t2 x< lkp) tyeq =
  tr≡ (cong (λ l → l [ proj-uN-0 32 x ]!) (sym tyeq)) lkp

xa-global-inv : ∀ {s a gt} →
  Externaddr-ok s (externaddr-GLOBAL a) (GLOBAL gt) →
  (a < length (store-GLOBALS s)) ×
  (globalinst-TYPE ((store-GLOBALS s) [ a ]!) ≡ gt)
xa-global-inv (Externaddr-ok--global _ a gi a< lk) = a< , cong globalinst-TYPE lk
xa-global-inv (Externaddr-ok--sub _ _ _ _ ok'
  (Externtype-sub--global _ _ (mk-Globaltype-sub _))) = xa-global-inv ok'

ginst-val : ∀ {s gi gt} → Globalinst-ok s gi gt → ∀ {mu t} →
  globalinst-TYPE gi ≡ mk-globaltype mu t → Val-ok s (VALUE gi) t
ginst-val (mk-Globalinst-ok _ mu' t' v gok vok) refl = vok

xa-table-inv : ∀ {s a lim rt} →
  Externaddr-ok s (externaddr-TABLE a) (TABLE (mk-tabletype lim rt)) →
  (a < length (store-TABLES s)) ×
  (Σ limits λ lim' → tableinst-TYPE ((store-TABLES s) [ a ]!) ≡ mk-tabletype lim' rt)
xa-table-inv (Externaddr-ok--table _ a ti a< lk) = a< , _ , cong tableinst-TYPE lk
xa-table-inv (Externaddr-ok--sub _ _ _ _ ok'
  (Externtype-sub--table _ _ (mk-Tabletype-sub _ _ _ _))) = xa-table-inv ok'

xa-mem-inv : ∀ {s a mt} → Externaddr-ok s (externaddr-MEM a) (MEM mt) → a < length (store-MEMS s)
xa-mem-inv (Externaddr-ok--mem _ a mi a< lk) = a<
xa-mem-inv (Externaddr-ok--sub _ _ _ _ ok' (Externtype-sub--mem _ _ _)) = xa-mem-inv ok'

reftype-sub-eq : ∀ {a b} → Valtype-sub (valtype-reftype a) (valtype-reftype b) → a ≡ b
reftype-sub-eq {FUNCREF} {FUNCREF} _ = refl
reftype-sub-eq {FUNCREF} {EXTERNREF} ()
reftype-sub-eq {EXTERNREF} {FUNCREF} ()
reftype-sub-eq {EXTERNREF} {EXTERNREF} _ = refl

iok-tset : ∀ {C x d c} →
  Instr-ok C (TABLE-SET x) (mk-functype (mk-list d) (mk-list c)) →
  Σ (reftype × limits) λ (rt , lim) →
    (d ≡ valtype-I32 ∷ valtype-reftype rt ∷ []) × (c ≡ []) ×
    (proj-uN-0 32 x < length (context-TABLES C)) ×
    ((context-TABLES C [ proj-uN-0 32 x ]!) ≡ mk-tabletype lim rt)
iok-tset (table-set _ _ rt lim p q) = (rt , lim) , refl , refl , p , q

tset-inv : ∀ {s C e d c x} →
  Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) → e ≡ admininstr-TABLE-SET x →
  Σ (reftype × limits) λ (rt , lim) →
    (d ≡ valtype-I32 ∷ valtype-reftype rt ∷ []) × (c ≡ []) ×
    (proj-uN-0 32 x < length (context-TABLES C)) ×
    ((context-TABLES C [ proj-uN-0 32 x ]!) ≡ mk-tabletype lim rt)
tset-inv (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-tset iok
tset-inv (label _ _ _ _ _ _ _ _ _ _) ()
tset-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
tset-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
tset-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
tset-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
tset-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
tset-inv (Instr-ok2--trap _ _ _ _) ()

------------------------------------------------------------------------
-- 9. PRESERVATION.
--
-- Redex-level preservation over Step-pure, at ARBITRARY types
-- u1 -> u2 (not just canonical ones as in attempt #1).  ALL 104 of the
-- 104 Step-pure rules are proved: control flow (block/loop/call-addr
-- via Step-read, if, br, br_if, br_table, br-succ, label/frame exits,
-- return-label, return-frame, traps), numerics, references, parametric,
-- and the COMPLETE shaped-SIMD tail (vv/vunop/vbinop/vtestop, vrelop,
-- vshiftop, vbitmask, vnarrow, vcvtop, vswizzle, vshuffle, vsplat,
-- vextract-lane, vreplace-lane, vext-un/binop).  pres-pure is TOTAL.
------------------------------------------------------------------------

-- pres-pure is now TOTAL: all 104 Step-pure rules are proved (control
-- flow, numerics, references, parametrics, and the full shaped-SIMD
-- tail).  No postulate remains for the pure-reduction fragment.

pres-pure : ∀ {s C es es' u1 u2} →
  Instrs-ok2 s C es (mk-functype (mk-list u1) (mk-list u2)) →
  Step-pure es es' →
  Instrs-ok2 s C es' (mk-functype (mk-list u1) (mk-list u2))

-- unreachable ~> trap
pres-pure ok Step-pure--unreachable = trap-ty

-- nop ~> eps
pres-pure ok Step-pure--nop with singleton-inv ok
... | mk-single p dm c eok s1 s2 with nop-inv eok refl
... | refl , refl = sub-empty (rt-sub-trans (rt-norm p s1) (rt-norml p s2))

-- v drop ~> eps
pres-pure ok (Step-pure--drop v)
  with decomp ok (admininstr-val v ∷ []) (admininstr-DROP ∷ []) refl
... | mk-split m okV okD with val-ty v okV | singleton-inv okD
... | mk-valty p1 a vok s11 s12 | mk-single p2 dm c dok s21 s22
  with drop-inv dok refl
... | t' , refl , refl =
  sub-empty (rt-sub-trans s11
    (rt-sub-trans (proj₁ (rt-sub-unsnoc (rt-sub-trans s12 s21)))
      (rt-norml p2 s22)))

-- v1 v2 (i32.const c) select ~> v1   (c /= 0)
pres-pure ok (select-true v1 v2 cc opt ne)
  with decomp ok (admininstr-val v1 ∷ [])
        (admininstr-val v2 ∷ admininstr-CONST I32 cc ∷ admininstr-SELECT opt ∷ []) refl
... | mk-split m1 okV1 okR1
  with decomp okR1 (admininstr-val v2 ∷ [])
        (admininstr-CONST I32 cc ∷ admininstr-SELECT opt ∷ []) refl
... | mk-split m2 okV2 okR2
  with decomp okR2 (admininstr-CONST I32 cc ∷ []) (admininstr-SELECT opt ∷ []) refl
... | mk-split m3 okC okS
  with val-ty v1 okV1 | val-ty v2 okV2 | const-ty okC | singleton-inv okS
... | mk-valty p1 a1 vok1 s11 s12 | mk-valty p2 a2 vok2 s21 s22
    | (p3 , s31 , s32) | mk-single p4 d4 c4 selok s41 s42
  with sel-inv selok refl
... | t , refl , refl
  with rt-sub-unsnoc
        (subst (λ l → Resulttype-sub (mk-list (p3 ++ valtype-numtype I32 ∷ [])) (mk-list l))
               (sym (snoc3 p4 t t valtype-I32))
               (rt-sub-trans s32 s41))
... | p3sub , _
  with rt-sub-unsnoc (rt-sub-trans s22 (rt-sub-trans s31 p3sub))
... | p2sub , a2sub
  with rt-sub-unsnoc (rt-sub-trans s12 (rt-sub-trans s21 p2sub))
... | p1sub , a1sub =
  push1 p4 (val-ok-ty vok1) (rt-sub-trans s11 p1sub)
    (subst (λ w → Resulttype-sub (mk-list (p4 ++ w ∷ [])) (mk-list _))
           (vt-sub-val vok1 a1sub) s42)

-- v1 v2 (i32.const 0) select ~> v2
pres-pure ok (select-false v1 v2 cc opt ze)
  with decomp ok (admininstr-val v1 ∷ [])
        (admininstr-val v2 ∷ admininstr-CONST I32 cc ∷ admininstr-SELECT opt ∷ []) refl
... | mk-split m1 okV1 okR1
  with decomp okR1 (admininstr-val v2 ∷ [])
        (admininstr-CONST I32 cc ∷ admininstr-SELECT opt ∷ []) refl
... | mk-split m2 okV2 okR2
  with decomp okR2 (admininstr-CONST I32 cc ∷ []) (admininstr-SELECT opt ∷ []) refl
... | mk-split m3 okC okS
  with val-ty v1 okV1 | val-ty v2 okV2 | const-ty okC | singleton-inv okS
... | mk-valty p1 a1 vok1 s11 s12 | mk-valty p2 a2 vok2 s21 s22
    | (p3 , s31 , s32) | mk-single p4 d4 c4 selok s41 s42
  with sel-inv selok refl
... | t , refl , refl
  with rt-sub-unsnoc
        (subst (λ l → Resulttype-sub (mk-list (p3 ++ valtype-numtype I32 ∷ [])) (mk-list l))
               (sym (snoc3 p4 t t valtype-I32))
               (rt-sub-trans s32 s41))
... | p3sub , _
  with rt-sub-unsnoc (rt-sub-trans s22 (rt-sub-trans s31 p3sub))
... | p2sub , a2sub
  with rt-sub-unsnoc (rt-sub-trans s12 (rt-sub-trans s21 p2sub))
... | p1sub , a1sub =
  push1 p4 (val-ok-ty vok2) (rt-sub-trans s11 p1sub)
    (subst (λ w → Resulttype-sub (mk-list (p4 ++ w ∷ [])) (mk-list _))
           (vt-sub-val vok2 a2sub) s42)

-- (t.const c1) (t.unop) ~> (t.const c)  |  trap
pres-pure ok (unop-val nt c1 op c pr mem)
  with decomp ok (admininstr-CONST nt c1 ∷ []) (admininstr-UNOP nt op ∷ []) refl
... | mk-split m okC okU with const-ty okC | singleton-inv okU
... | (p1 , s11 , s12) | mk-single p2 d2 c2 uok s21 s22
  with unop-inv uok refl
... | refl , refl =
  push1 p1 (plain _ _ _ _ _ (const _ nt c)) s11
    (rt-sub-trans (rt-sub-trans s12 s21) s22)
pres-pure ok (unop-trap nt c1 op emp) = trap-ty

-- (t.const c1) (t.const c2) (t.binop) ~> (t.const c)  |  trap
pres-pure ok (binop-val nt c1 c2 op c pr mem)
  with decomp ok (admininstr-CONST nt c1 ∷ [])
        (admininstr-CONST nt c2 ∷ admininstr-BINOP nt op ∷ []) refl
... | mk-split m1 okC1 okR
  with decomp okR (admininstr-CONST nt c2 ∷ []) (admininstr-BINOP nt op ∷ []) refl
... | mk-split m2 okC2 okB
  with const-ty okC1 | const-ty okC2 | singleton-inv okB
... | (p1 , s11 , s12) | (p2 , s21 , s22) | mk-single p3 d3 c3 bok s31 s32
  with binop-inv bok refl
... | refl , refl
  with rt-sub-unsnoc
        (subst (λ l → Resulttype-sub (mk-list (p2 ++ valtype-numtype nt ∷ [])) (mk-list l))
               (sym (snoc2 p3 (valtype-numtype nt) (valtype-numtype nt)))
               (rt-sub-trans s22 s31))
... | p2sub , _ =
  push1 p1 (plain _ _ _ _ _ (const _ nt c)) s11
    (rt-sub-trans (rt-sub-trans s12 (rt-sub-trans s21 p2sub)) s32)
pres-pure ok (binop-trap nt c1 c2 op emp) = trap-ty

-- (t.const c1) (t.testop) ~> (i32.const c)
pres-pure ok (Step-pure--testop nt c1 op c ceq)
  with decomp ok (admininstr-CONST nt c1 ∷ []) (admininstr-TESTOP nt op ∷ []) refl
... | mk-split m okC okT with const-ty okC | singleton-inv okT
... | (p1 , s11 , s12) | mk-single p2 d2 c2 tok s21 s22
  with testop-inv tok refl
... | refl , refl
  with rt-sub-unsnoc (rt-sub-trans s12 s21)
... | p1sub , _ =
  push1 p2 (plain _ _ _ _ _ (const _ I32 c)) (rt-sub-trans s11 p1sub) s22

-- (t.const c1) (t.const c2) (t.relop) ~> (i32.const c)
pres-pure ok (Step-pure--relop nt c1 c2 op c ceq)
  with decomp ok (admininstr-CONST nt c1 ∷ [])
        (admininstr-CONST nt c2 ∷ admininstr-RELOP nt op ∷ []) refl
... | mk-split m1 okC1 okR
  with decomp okR (admininstr-CONST nt c2 ∷ []) (admininstr-RELOP nt op ∷ []) refl
... | mk-split m2 okC2 okB
  with const-ty okC1 | const-ty okC2 | singleton-inv okB
... | (p1 , s11 , s12) | (p2 , s21 , s22) | mk-single p3 d3 c3 rok s31 s32
  with relop-inv rok refl
... | refl , refl
  with rt-sub-unsnoc
        (subst (λ l → Resulttype-sub (mk-list (p2 ++ valtype-numtype nt ∷ [])) (mk-list l))
               (sym (snoc2 p3 (valtype-numtype nt) (valtype-numtype nt)))
               (rt-sub-trans s22 s31))
... | p2sub , _
  with rt-sub-unsnoc (rt-sub-trans s12 (rt-sub-trans s21 p2sub))
... | p1sub , _ =
  push1 p3 (plain _ _ _ _ _ (const _ I32 c)) (rt-sub-trans s11 p1sub) s32

-- label_n{instr*} v* ~> v*
pres-pure ok (label-vals vn cont vals)
  with singleton-inv ok
... | mk-single p d c lok s1 s2
  with label-inv lok refl
... | refl , t' , lenq , contTy , bodyTy
  with row-inv vals bodyTy
... | ts , pwv , rsub =
  push* p (row-intro (pw-val-sub pwv (rt-sub-pw rsub))) (rt-norm p s1) s2

-- frame_n{F} v* ~> v*
pres-pure ok (frame-vals vn fr vals leneq)
  with singleton-inv ok
... | mk-single p d c fok2 s1 s2
  with frame-inv fok2 refl
... | refl , lenc , C' , frok , mk-Expr-ok2 _ _ _ _ bodyTy
  with row-inv vals bodyTy
... | ts , pwv , rsub =
  push* p (row-intro (pw-val-sub pwv (rt-sub-pw rsub))) (rt-norm p s1) s2

-- label_n{instr*} v'* v^n (br 0) instr'* ~> v^n instr*
pres-pure ok (br-zero vn cont vals' vals instrs leneq)
  with singleton-inv ok
... | mk-single p d c lok s1 s2
  with label-inv lok refl
... | refl , t' , lenq , contTy , bodyTy
  with decomp bodyTy
        ((map (λ w → admininstr-val w) vals' ++ map (λ w → admininstr-val w) vals)
          ++ (admininstr-BR (mk-uN 0) ∷ []))
        (map (λ i → admininstr-instr i) instrs) refl
... | mk-split m3 okA okD
  with decomp okA
        (map (λ w → admininstr-val w) vals' ++ map (λ w → admininstr-val w) vals)
        (admininstr-BR (mk-uN 0) ∷ []) refl
... | mk-split m2 okB okBr
  with decomp okB (map (λ w → admininstr-val w) vals')
        (map (λ w → admininstr-val w) vals) refl
... | mk-split m1 okRow' okRow
  with row-inv vals okRow | singleton-inv okBr
... | (ts , pwv , rsub) | mk-single q dbr cbr brok sb1 sb2
  with br-inv brok refl
... | (t1' , tl) , refl , l< , lkp
  with lkp
... | refl
  with rt-sub-split
        (subst (λ l → Resulttype-sub (mk-list (m1 ++ ts)) (mk-list l))
               (sym (++-assoc q t1' t'))
               (rt-sub-trans rsub sb1))
        (tr≡ (tr≡ (pw-length pwv) leneq) (sym lenq))
... | m1sub , tsub =
  push* p
    (Instrs-ok2--seq _ _ (map (λ w → admininstr-val w) vals)
      (map (λ i → admininstr-instr i) cont) _ _ _
      (row-intro (pw-val-sub pwv (rt-sub-pw tsub))) contTy)
    (rt-norm p s1) s2

-- v* trap instr* ~> trap ; label/frame around trap ~> trap
pres-pure ok (trap-vals vals instrs ne) = trap-ty
pres-pure ok (trap-label vn cont) = trap-ty
pres-pure ok (trap-frame vn fr) = trap-ty

-- (i32.const c) (if bt i1 i2) ~> (block bt i1)  |  (block bt i2)
pres-pure ok (if-true cc bt i1 i2 ne)
  with decomp ok (admininstr-CONST I32 cc ∷ []) (admininstr-IFELSE bt i1 i2 ∷ []) refl
... | mk-split m okC okIf
  with const-ty okC | singleton-inv okIf
... | (p1 , s11 , s12) | mk-single p2 d2 c2 ifok s21 s22
  with if-inv ifok refl
... | t1 , refl , bkok , b1 , b2
  with rt-sub-unsnoc
        (subst (λ l → Resulttype-sub (mk-list (p1 ++ valtype-numtype I32 ∷ [])) (mk-list l))
               (sym (++-assoc p2 t1 (valtype-I32 ∷ [])))
               (rt-sub-trans s12 s21))
... | psub , _ =
  single-intro (mk-single p2 t1 c2 (plain _ _ _ _ _ (block _ bt i1 t1 c2 bkok b1))
    (rt-sub-trans s11 psub) s22)
pres-pure ok (if-false cc bt i1 i2 ze)
  with decomp ok (admininstr-CONST I32 cc ∷ []) (admininstr-IFELSE bt i1 i2 ∷ []) refl
... | mk-split m okC okIf
  with const-ty okC | singleton-inv okIf
... | (p1 , s11 , s12) | mk-single p2 d2 c2 ifok s21 s22
  with if-inv ifok refl
... | t1 , refl , bkok , b1 , b2
  with rt-sub-unsnoc
        (subst (λ l → Resulttype-sub (mk-list (p1 ++ valtype-numtype I32 ∷ [])) (mk-list l))
               (sym (++-assoc p2 t1 (valtype-I32 ∷ [])))
               (rt-sub-trans s12 s21))
... | psub , _ =
  single-intro (mk-single p2 t1 c2 (plain _ _ _ _ _ (block _ bt i2 t1 c2 bkok b2))
    (rt-sub-trans s11 psub) s22)

-- (i32.const c) (br_if l) ~> (br l)  |  eps
pres-pure {u2 = u2} ok (br-if-true cc l ne)
  with decomp ok (admininstr-CONST I32 cc ∷ []) (admininstr-BR-IF l ∷ []) refl
... | mk-split m okC okBi
  with const-ty okC | singleton-inv okBi
... | (p1 , s11 , s12) | mk-single p2 d2 c2 biok s21 s22
  with brif-inv biok refl
... | tl , refl , refl , l< , lkp
  with rt-sub-unsnoc
        (subst (λ l2 → Resulttype-sub (mk-list (p1 ++ valtype-numtype I32 ∷ [])) (mk-list l2))
               (sym (++-assoc p2 tl (valtype-I32 ∷ [])))
               (rt-sub-trans s12 s21))
... | psub , _ =
  single-intro (mk-single [] (p2 ++ tl) u2
    (plain _ _ _ _ _ (br _ l p2 tl u2 l< lkp))
    (rt-sub-trans s11 psub) (rt-sub-refl u2))
pres-pure ok (br-if-false cc l ze)
  with decomp ok (admininstr-CONST I32 cc ∷ []) (admininstr-BR-IF l ∷ []) refl
... | mk-split m okC okBi
  with const-ty okC | singleton-inv okBi
... | (p1 , s11 , s12) | mk-single p2 d2 c2 biok s21 s22
  with brif-inv biok refl
... | tl , refl , refl , l< , lkp
  with rt-sub-unsnoc
        (subst (λ l2 → Resulttype-sub (mk-list (p1 ++ valtype-numtype I32 ∷ [])) (mk-list l2))
               (sym (++-assoc p2 tl (valtype-I32 ∷ [])))
               (rt-sub-trans s12 s21))
... | psub , _ = sub-empty (rt-sub-trans s11 (rt-sub-trans psub s22))

-- (t1.const c1) (t2.cvtop t1) ~> (t2.const c)  |  trap
pres-pure ok (cvtop-val nt1 c1 nt2 op c pr mem)
  with decomp ok (admininstr-CONST nt1 c1 ∷ []) (admininstr-CVTOP nt2 nt1 op ∷ []) refl
... | mk-split m okC okV with const-ty okC | singleton-inv okV
... | (p1 , s11 , s12) | mk-single p2 d2 c2 vok s21 s22
  with cvtop-inv vok refl
... | refl , refl
  with rt-sub-unsnoc (rt-sub-trans s12 s21)
... | psub , _ =
  push1 p2 (plain _ _ _ _ _ (const _ nt2 c)) (rt-sub-trans s11 psub) s22
pres-pure ok (cvtop-trap nt1 c1 nt2 op emp) = trap-ty

-- ref (ref.is_null) ~> (i32.const 1|0)
pres-pure ok (ref-is-null-true r rt req)
  with req
... | refl
  with decomp ok (admininstr-REF-NULL rt ∷ []) (admininstr-REF-IS-NULL ∷ []) refl
... | mk-split m okR okN with singleton-inv okR | singleton-inv okN
... | mk-single p1 d1 c1 rok s11 s12 | mk-single p2 d2 c2 nok s21 s22
  with vinv-refnull rok refl | risnull-inv nok refl
... | refl , refl | (rt2 , refl , refl)
  with rt-sub-unsnoc (rt-sub-trans s12 s21)
... | psub , _ =
  push1 p2 (plain _ _ _ _ _ (const _ I32 (mk-uN 1)))
    (rt-sub-trans (rt-norm p1 s11) psub) s22
pres-pure ok (ref-is-null-false (ref-REF-NULL rt) nb)
  with decomp ok (admininstr-REF-NULL rt ∷ []) (admininstr-REF-IS-NULL ∷ []) refl
... | mk-split m okR okN with singleton-inv okR | singleton-inv okN
... | mk-single p1 d1 c1 rok s11 s12 | mk-single p2 d2 c2 nok s21 s22
  with vinv-refnull rok refl | risnull-inv nok refl
... | refl , refl | (rt2 , refl , refl)
  with rt-sub-unsnoc (rt-sub-trans s12 s21)
... | psub , _ =
  push1 p2 (plain _ _ _ _ _ (const _ I32 (mk-uN 0)))
    (rt-sub-trans (rt-norm p1 s11) psub) s22
pres-pure ok (ref-is-null-false (REF-FUNC-ADDR fa) nb)
  with decomp ok (admininstr-REF-FUNC-ADDR fa ∷ []) (admininstr-REF-IS-NULL ∷ []) refl
... | mk-split m okR okN with singleton-inv okR | singleton-inv okN
... | mk-single p1 d1 c1 rok s11 s12 | mk-single p2 d2 c2 nok s21 s22
  with vinv-reffunc rok refl | risnull-inv nok refl
... | refl , refl , _ | (rt2 , refl , refl)
  with rt-sub-unsnoc (rt-sub-trans s12 s21)
... | psub , _ =
  push1 p2 (plain _ _ _ _ _ (const _ I32 (mk-uN 0)))
    (rt-sub-trans (rt-norm p1 s11) psub) s22
pres-pure ok (ref-is-null-false (REF-HOST-ADDR ha) nb)
  with decomp ok (admininstr-REF-HOST-ADDR ha ∷ []) (admininstr-REF-IS-NULL ∷ []) refl
... | mk-split m okR okN with singleton-inv okR | singleton-inv okN
... | mk-single p1 d1 c1 rok s11 s12 | mk-single p2 d2 c2 nok s21 s22
  with vinv-refhost rok refl | risnull-inv nok refl
... | refl , refl , _ | (rt2 , refl , refl)
  with rt-sub-unsnoc (rt-sub-trans s12 s21)
... | psub , _ =
  push1 p2 (plain _ _ _ _ _ (const _ I32 (mk-uN 0)))
    (rt-sub-trans (rt-norm p1 s11) psub) s22

-- v (local.tee x) ~> v v (local.set x)
pres-pure {u2 = u2} ok (Step-pure--local-tee v x)
  with decomp ok (admininstr-val v ∷ []) (admininstr-LOCAL-TEE x ∷ []) refl
... | mk-split m okV okT with val-ty v okV | singleton-inv okT
... | mk-valty p1 a vok s11 s12 | mk-single p2 d2 c2 teok s21 s22
  with tee-inv teok refl
... | t' , refl , refl , x< , lkp
  with rt-sub-unsnoc (rt-sub-trans s12 s21)
... | psub , asub
  with vt-sub-val vok asub
... | refl =
  Instrs-ok2--sub _ _ _ _ _ _ _
    (Instrs-ok2--seq _ _ (admininstr-val v ∷ [])
        (admininstr-val v ∷ admininstr-LOCAL-SET x ∷ []) _ _ _
      (push1 p2 (val-ok-ty vok) (rt-sub-trans s11 psub)
        (rt-sub-refl (p2 ++ a ∷ [])))
      (Instrs-ok2--seq _ _ (admininstr-val v ∷ [])
          (admininstr-LOCAL-SET x ∷ []) _ _ _
        (push1 (p2 ++ a ∷ []) (val-ok-ty vok)
          (rt-sub-refl (p2 ++ a ∷ []))
          (rt-sub-refl ((p2 ++ a ∷ []) ++ a ∷ [])))
        (single-intro (mk-single (p2 ++ a ∷ []) (a ∷ []) []
          (plain _ _ _ _ _ (local-set _ x a x< lkp))
          (rt-sub-refl ((p2 ++ a ∷ []) ++ a ∷ []))
          (subst (λ l → Resulttype-sub (mk-list l) (mk-list (p2 ++ a ∷ [])))
                 (sym (++-identityʳ (p2 ++ a ∷ [])))
                 (rt-sub-refl (p2 ++ a ∷ [])))))))
    (rt-sub-refl _) s22

-- (i32.const i) (br_table l* l') ~> (br l*[i])  |  (br l')
pres-pure {C = C} {u2 = u2} ok (br-table-lt i ls l' i<)
  with decomp ok (admininstr-CONST I32 i ∷ []) (admininstr-BR-TABLE ls l' ∷ []) refl
... | mk-split m okC okBt
  with const-ty okC | singleton-inv okBt
... | (p1 , s11 , s12) | mk-single p2 d2 c2 btok s21 s22
  with brtable-inv btok refl
... | (t1 , tl) , refl , allb , allsub , l'< , l'sub
  with rt-sub-unsnoc
        (subst (λ l → Resulttype-sub (mk-list (p1 ++ valtype-numtype I32 ∷ [])) (mk-list l))
               (sym (tr≡ (++-assoc (p2 ++ t1) tl (valtype-I32 ∷ []))
                         (++-assoc p2 t1 (tl ++ valtype-I32 ∷ []))))
               (rt-sub-trans s12 s21))
... | psub , _ =
  single-intro (mk-single []
    ((p2 ++ t1) ++ proj-list-0 valtype ((LABELS C) [ proj-uN-0 32 (ls [ proj-uN-0 32 i ]!) ]!))
    u2
    (plain _ _ _ _ _ (br _ (ls [ proj-uN-0 32 i ]!) (p2 ++ t1) _ u2
      (all-lookup allb i<) refl))
    (rt-sub-trans s11 (rt-sub-trans psub
      (rt-sub-app (rt-sub-refl (p2 ++ t1))
        (subst (Resulttype-sub (mk-list tl)) (sym (rt-eta _))
               (all-lookup allsub i<)))))
    (rt-sub-refl u2))
pres-pure {C = C} {u2 = u2} ok (br-table-ge i ls l' i≥)
  with decomp ok (admininstr-CONST I32 i ∷ []) (admininstr-BR-TABLE ls l' ∷ []) refl
... | mk-split m okC okBt
  with const-ty okC | singleton-inv okBt
... | (p1 , s11 , s12) | mk-single p2 d2 c2 btok s21 s22
  with brtable-inv btok refl
... | (t1 , tl) , refl , allb , allsub , l'< , l'sub
  with rt-sub-unsnoc
        (subst (λ l → Resulttype-sub (mk-list (p1 ++ valtype-numtype I32 ∷ [])) (mk-list l))
               (sym (tr≡ (++-assoc (p2 ++ t1) tl (valtype-I32 ∷ []))
                         (++-assoc p2 t1 (tl ++ valtype-I32 ∷ []))))
               (rt-sub-trans s12 s21))
... | psub , _ =
  single-intro (mk-single []
    ((p2 ++ t1) ++ proj-list-0 valtype ((LABELS C) [ proj-uN-0 32 l' ]!))
    u2
    (plain _ _ _ _ _ (br _ l' (p2 ++ t1) _ u2 l'< refl))
    (rt-sub-trans s11 (rt-sub-trans psub
      (rt-sub-app (rt-sub-refl (p2 ++ t1))
        (subst (Resulttype-sub (mk-list tl)) (sym (rt-eta _)) l'sub))))
    (rt-sub-refl u2))

-- label_n{instr*} v* (br l+1) instr'* ~> v* (br l)
pres-pure {C = C} ok (br-succ vn cont vals l instrs)
  with singleton-inv ok
... | mk-single p d c lok s1 s2
  with label-inv lok refl
... | refl , t' , lenq , contTy , bodyTy
  with decomp bodyTy
        (map (λ w → admininstr-val w) vals
          ++ (admininstr-BR (mk-uN (proj-uN-0 32 l + 1)) ∷ []))
        (map (λ i → admininstr-instr i) instrs) refl
... | mk-split m3 okA okD
  with decomp okA (map (λ w → admininstr-val w) vals)
        (admininstr-BR (mk-uN (proj-uN-0 32 l + 1)) ∷ []) refl
... | mk-split m2 okRow okBr
  with row-inv vals okRow | singleton-inv okBr
... | (ts , pwv , rsub) | mk-single q dbr cbr brok sb1 sb2
  with br-inv brok refl
... | (t1' , tl) , refl , bnd , lkp
  with subst (λ n' → proj-list-0 valtype ((mk-list t' ∷ LABELS C) [ n' ]!) ≡ tl)
             (+-comm (proj-uN-0 32 l) 1) lkp
     | subst (λ n' → n' < length (mk-list t' ∷ LABELS C))
             (+-comm (proj-uN-0 32 l) 1) bnd
... | lkp' | s≤s bnd'
  with pw-take-drop (q ++ t1')
        (rt-sub-pw (subst (λ ll → Resulttype-sub (mk-list ts) (mk-list ll))
                          (sym (++-assoc q t1' tl))
                          (rt-sub-trans rsub sb1)))
... | (ts1 , ts2) , tseq , pw1 , pw2 =
  let tlC = proj-list-0 valtype ((LABELS C) [ proj-uN-0 32 l ]!)
      ts2sub = subst (λ w → Resulttype-sub (mk-list ts2) (mk-list w)) (sym lkp')
                 (mk-Resulttype-sub _ _ (pw-length pw2) pw2)
  in push* p
    (Instrs-ok2--seq _ _ (map (λ w → admininstr-val w) vals)
        (admininstr-BR l ∷ []) _ _ _
      (row-intro pwv)
      (single-intro (mk-single [] (ts1 ++ tlC) c
        (plain _ _ _ _ _ (br _ l ts1 tlC c bnd' refl))
        (subst (λ ll → Resulttype-sub (mk-list ll) (mk-list (ts1 ++ tlC)))
               (sym tseq)
               (rt-sub-app (rt-sub-refl ts1) ts2sub))
        (rt-sub-refl c))))
    (rt-norm p s1) s2

-- label_n{instr*} v* return instr'* ~> v* return
pres-pure ok (return-label vn cont vals instrs)
  with singleton-inv ok
... | mk-single p d c lok s1 s2
  with label-inv lok refl
... | refl , t' , lenq , contTy , bodyTy
  with decomp bodyTy
        (map (λ w → admininstr-val w) vals ++ (admininstr-RETURN ∷ []))
        (map (λ i → admininstr-instr i) instrs) refl
... | mk-split m3 okA okD
  with decomp okA (map (λ w → admininstr-val w) vals) (admininstr-RETURN ∷ []) refl
... | mk-split m2 okRow okRet
  with row-inv vals okRow | singleton-inv okRet
... | (ts , pwv , rsub) | mk-single q dret cret retok sb1 sb2
  with return-inv retok refl
... | (t1' , tr) , refl , req
  with pw-take-drop (q ++ t1')
        (rt-sub-pw (subst (λ ll → Resulttype-sub (mk-list ts) (mk-list ll))
                          (sym (++-assoc q t1' tr))
                          (rt-sub-trans rsub sb1)))
... | (ts1 , ts2) , tseq , pw1 , pw2 =
  push* p
    (Instrs-ok2--seq _ _ (map (λ w → admininstr-val w) vals)
        (admininstr-RETURN ∷ []) _ _ _
      (row-intro pwv)
      (single-intro (mk-single [] (ts1 ++ tr) c
        (plain _ _ _ _ _ (return _ ts1 tr c req))
        (subst (λ ll → Resulttype-sub (mk-list ll) (mk-list (ts1 ++ tr)))
               (sym tseq)
               (rt-sub-app (rt-sub-refl ts1)
                 (mk-Resulttype-sub _ _ (pw-length pw2) pw2)))
        (rt-sub-refl c))))
    (rt-norm p s1) s2

-- frame_n{F} v'* v^n return instr* ~> v^n   (now a REAL proof: the
-- regenerated frame rule types the body with RETURN = [t^n], so the
-- return's declared result equals the frame's result type c, and the
-- v^n row -- of length n = |c| -- carries exactly c).
pres-pure ok (return-frame vn fr vals' vals instrs leneq)
  with singleton-inv ok
... | mk-single p d c fok2 s1 s2
  with frame-inv fok2 refl
... | refl , lenc , C' , frok , mk-Expr-ok2 _ _ _ _ bodyTy
  with decomp bodyTy
        ((map (λ w → admininstr-val w) vals' ++ map (λ w → admininstr-val w) vals)
          ++ (admininstr-RETURN ∷ []))
        (map (λ i → admininstr-instr i) instrs) refl
... | mk-split m3 okA okD
  with decomp okA
        (map (λ w → admininstr-val w) vals' ++ map (λ w → admininstr-val w) vals)
        (admininstr-RETURN ∷ []) refl
... | mk-split m2 okB okRet
  with decomp okB (map (λ w → admininstr-val w) vals')
        (map (λ w → admininstr-val w) vals) refl
... | mk-split m1 okRow' okRow
  with row-inv vals okRow | singleton-inv okRet
... | (ts , pwv , rsub) | mk-single q dret cret retok sb1 sb2
  with return-inv retok refl
... | (t1' , tr) , refl , req
  -- context-RETURN (retC c ⧺ C') = just (mk-list c); return says = just (mk-list tr)
  with mk-list-inj (just-inj req)
... | refl
  with rt-sub-split
        (subst (λ l → Resulttype-sub (mk-list (m1 ++ ts)) (mk-list l))
               (sym (++-assoc q t1' tr))
               (rt-sub-trans rsub sb1))
        (tr≡ (tr≡ (pw-length pwv) leneq) (sym lenc))
... | _ , tsub =
  push* p (row-intro (pw-val-sub pwv (rt-sub-pw tsub))) (rt-norm p s1) s2

-- v128 vv-ops: unop / binop / ternop / testop
pres-pure ok (Step-pure--vvunop c1 op c ceq)
  with decomp ok (admininstr-VCONST V128 c1 ∷ []) (admininstr-VVUNOP V128 op ∷ []) refl
... | mk-split m okC okO with vconst-ty okC | singleton-inv okO
... | (p1 , s11 , s12) | mk-single p2 d2 c2 oik s21 s22
  with vvunop-inv oik refl
... | refl , refl =
  push1 p1 (plain _ _ _ _ _ (vconst _ c)) s11
    (rt-sub-trans (rt-sub-trans s12 s21) s22)
pres-pure ok (Step-pure--vvbinop c1 c2 op c ceq)
  with decomp ok (admininstr-VCONST V128 c1 ∷ [])
        (admininstr-VCONST V128 c2 ∷ admininstr-VVBINOP V128 op ∷ []) refl
... | mk-split m1 okC1 okR
  with decomp okR (admininstr-VCONST V128 c2 ∷ []) (admininstr-VVBINOP V128 op ∷ []) refl
... | mk-split m2 okC2 okO
  with vconst-ty okC1 | vconst-ty okC2 | singleton-inv okO
... | (p1 , s11 , s12) | (p2 , s21 , s22) | mk-single p3 d3 c3 oik s31 s32
  with vvbinop-inv oik refl
... | refl , refl
  with rt-sub-unsnoc
        (subst (λ l → Resulttype-sub (mk-list (p2 ++ valtype-V128 ∷ [])) (mk-list l))
               (sym (snoc2 p3 valtype-V128 valtype-V128))
               (rt-sub-trans s22 s31))
... | p2sub , _ =
  push1 p1 (plain _ _ _ _ _ (vconst _ c)) s11
    (rt-sub-trans (rt-sub-trans s12 (rt-sub-trans s21 p2sub)) s32)
pres-pure ok (Step-pure--vvternop c1 c2 c3 op c ceq)
  with decomp ok (admininstr-VCONST V128 c1 ∷ [])
        (admininstr-VCONST V128 c2 ∷ admininstr-VCONST V128 c3 ∷
         admininstr-VVTERNOP V128 op ∷ []) refl
... | mk-split m1 okC1 okR1
  with decomp okR1 (admininstr-VCONST V128 c2 ∷ [])
        (admininstr-VCONST V128 c3 ∷ admininstr-VVTERNOP V128 op ∷ []) refl
... | mk-split m2 okC2 okR2
  with decomp okR2 (admininstr-VCONST V128 c3 ∷ []) (admininstr-VVTERNOP V128 op ∷ []) refl
... | mk-split m3 okC3 okO
  with vconst-ty okC1 | vconst-ty okC2 | vconst-ty okC3 | singleton-inv okO
... | (p1 , s11 , s12) | (p2 , s21 , s22) | (p3 , s31 , s32)
    | mk-single p4 d4 c4 oik s41 s42
  with vvternop-inv oik refl
... | refl , refl
  with rt-sub-unsnoc
        (subst (λ l → Resulttype-sub (mk-list (p3 ++ valtype-V128 ∷ [])) (mk-list l))
               (sym (snoc3 p4 valtype-V128 valtype-V128 valtype-V128))
               (rt-sub-trans s32 s41))
... | p3sub , _
  with rt-sub-unsnoc (rt-sub-trans s22 (rt-sub-trans s31 p3sub))
... | p2sub , _
  with rt-sub-unsnoc (rt-sub-trans s12 (rt-sub-trans s21 p2sub))
... | p1sub , _ =
  push1 p4 (plain _ _ _ _ _ (vconst _ c)) (rt-sub-trans s11 p1sub) s42
pres-pure ok (Step-pure--vvtestop c1 c szp ceq)
  with decomp ok (admininstr-VCONST V128 c1 ∷ [])
        (admininstr-VVTESTOP V128 ANY-TRUE ∷ []) refl
... | mk-split m okC okO with vconst-ty okC | singleton-inv okO
... | (p1 , s11 , s12) | mk-single p2 d2 c2 oik s21 s22
  with vvtestop-inv oik refl
... | refl , refl
  with rt-sub-unsnoc (rt-sub-trans s12 s21)
... | psub , _ =
  push1 p2 (plain _ _ _ _ _ (const _ I32 c)) (rt-sub-trans s11 psub) s22

-- v128 shaped ops: vunop / vbinop / vtestop
pres-pure ok (Step-pure--vunop c1 sh op c pr mem)
  with decomp ok (admininstr-VCONST V128 c1 ∷ []) (admininstr-VUNOP sh op ∷ []) refl
... | mk-split m okC okO with vconst-ty okC | singleton-inv okO
... | (p1 , s11 , s12) | mk-single p2 d2 c2 oik s21 s22
  with vunop-inv oik refl
... | refl , refl =
  push1 p1 (plain _ _ _ _ _ (vconst _ c)) s11
    (rt-sub-trans (rt-sub-trans s12 s21) s22)
pres-pure ok (vunop-trap c1 sh op emp) = trap-ty
pres-pure ok (vbinop-val c1 c2 sh op c pr mem)
  with decomp ok (admininstr-VCONST V128 c1 ∷ [])
        (admininstr-VCONST V128 c2 ∷ admininstr-VBINOP sh op ∷ []) refl
... | mk-split m1 okC1 okR
  with decomp okR (admininstr-VCONST V128 c2 ∷ []) (admininstr-VBINOP sh op ∷ []) refl
... | mk-split m2 okC2 okO
  with vconst-ty okC1 | vconst-ty okC2 | singleton-inv okO
... | (p1 , s11 , s12) | (p2 , s21 , s22) | mk-single p3 d3 c3 oik s31 s32
  with vbinop-inv oik refl
... | refl , refl
  with rt-sub-unsnoc
        (subst (λ l → Resulttype-sub (mk-list (p2 ++ valtype-V128 ∷ [])) (mk-list l))
               (sym (snoc2 p3 valtype-V128 valtype-V128))
               (rt-sub-trans s22 s31))
... | p2sub , _ =
  push1 p1 (plain _ _ _ _ _ (vconst _ c)) s11
    (rt-sub-trans (rt-sub-trans s12 (rt-sub-trans s21 p2sub)) s32)
pres-pure ok (vbinop-trap c1 c2 sh op emp) = trap-ty
pres-pure ok (vtestop-true-0 c vN lanes laneq alltrue)
  with decomp ok (admininstr-VCONST V128 c ∷ [])
        (admininstr-VTESTOP (X (lanetype-Jnn Jnn-I32) (mk-dim vN)) ALL-TRUE ∷ []) refl
... | mk-split m okC okO with vconst-ty okC | singleton-inv okO
... | (p1 , s11 , s12) | mk-single p2 d2 c2 oik s21 s22
  with vtestop-inv oik refl
... | refl , refl
  with rt-sub-unsnoc (rt-sub-trans s12 s21)
... | psub , _ =
  push1 p2 (plain _ _ _ _ _ (const _ I32 (mk-uN 1))) (rt-sub-trans s11 psub) s22
pres-pure ok (vtestop-true-1 c vN lanes laneq alltrue)
  with decomp ok (admininstr-VCONST V128 c ∷ [])
        (admininstr-VTESTOP (X (lanetype-Jnn Jnn-I64) (mk-dim vN)) ALL-TRUE ∷ []) refl
... | mk-split m okC okO with vconst-ty okC | singleton-inv okO
... | (p1 , s11 , s12) | mk-single p2 d2 c2 oik s21 s22
  with vtestop-inv oik refl
... | refl , refl
  with rt-sub-unsnoc (rt-sub-trans s12 s21)
... | psub , _ =
  push1 p2 (plain _ _ _ _ _ (const _ I32 (mk-uN 1))) (rt-sub-trans s11 psub) s22
pres-pure ok (vtestop-true-2 c vN lanes laneq alltrue)
  with decomp ok (admininstr-VCONST V128 c ∷ [])
        (admininstr-VTESTOP (X (lanetype-Jnn Jnn-I8) (mk-dim vN)) ALL-TRUE ∷ []) refl
... | mk-split m okC okO with vconst-ty okC | singleton-inv okO
... | (p1 , s11 , s12) | mk-single p2 d2 c2 oik s21 s22
  with vtestop-inv oik refl
... | refl , refl
  with rt-sub-unsnoc (rt-sub-trans s12 s21)
... | psub , _ =
  push1 p2 (plain _ _ _ _ _ (const _ I32 (mk-uN 1))) (rt-sub-trans s11 psub) s22
pres-pure ok (vtestop-true-3 c vN lanes laneq alltrue)
  with decomp ok (admininstr-VCONST V128 c ∷ [])
        (admininstr-VTESTOP (X (lanetype-Jnn Jnn-I16) (mk-dim vN)) ALL-TRUE ∷ []) refl
... | mk-split m okC okO with vconst-ty okC | singleton-inv okO
... | (p1 , s11 , s12) | mk-single p2 d2 c2 oik s21 s22
  with vtestop-inv oik refl
... | refl , refl
  with rt-sub-unsnoc (rt-sub-trans s12 s21)
... | psub , _ =
  push1 p2 (plain _ _ _ _ _ (const _ I32 (mk-uN 1))) (rt-sub-trans s11 psub) s22
pres-pure ok (vtestop-false-0 c vN nb)
  with decomp ok (admininstr-VCONST V128 c ∷ [])
        (admininstr-VTESTOP (X (lanetype-Jnn Jnn-I32) (mk-dim vN)) ALL-TRUE ∷ []) refl
... | mk-split m okC okO with vconst-ty okC | singleton-inv okO
... | (p1 , s11 , s12) | mk-single p2 d2 c2 oik s21 s22
  with vtestop-inv oik refl
... | refl , refl
  with rt-sub-unsnoc (rt-sub-trans s12 s21)
... | psub , _ =
  push1 p2 (plain _ _ _ _ _ (const _ I32 (mk-uN 0))) (rt-sub-trans s11 psub) s22
pres-pure ok (vtestop-false-1 c vN nb)
  with decomp ok (admininstr-VCONST V128 c ∷ [])
        (admininstr-VTESTOP (X (lanetype-Jnn Jnn-I64) (mk-dim vN)) ALL-TRUE ∷ []) refl
... | mk-split m okC okO with vconst-ty okC | singleton-inv okO
... | (p1 , s11 , s12) | mk-single p2 d2 c2 oik s21 s22
  with vtestop-inv oik refl
... | refl , refl
  with rt-sub-unsnoc (rt-sub-trans s12 s21)
... | psub , _ =
  push1 p2 (plain _ _ _ _ _ (const _ I32 (mk-uN 0))) (rt-sub-trans s11 psub) s22
pres-pure ok (vtestop-false-2 c vN nb)
  with decomp ok (admininstr-VCONST V128 c ∷ [])
        (admininstr-VTESTOP (X (lanetype-Jnn Jnn-I8) (mk-dim vN)) ALL-TRUE ∷ []) refl
... | mk-split m okC okO with vconst-ty okC | singleton-inv okO
... | (p1 , s11 , s12) | mk-single p2 d2 c2 oik s21 s22
  with vtestop-inv oik refl
... | refl , refl
  with rt-sub-unsnoc (rt-sub-trans s12 s21)
... | psub , _ =
  push1 p2 (plain _ _ _ _ _ (const _ I32 (mk-uN 0))) (rt-sub-trans s11 psub) s22
pres-pure ok (vtestop-false-3 c vN nb)
  with decomp ok (admininstr-VCONST V128 c ∷ [])
        (admininstr-VTESTOP (X (lanetype-Jnn Jnn-I16) (mk-dim vN)) ALL-TRUE ∷ []) refl
... | mk-split m okC okO with vconst-ty okC | singleton-inv okO
... | (p1 , s11 , s12) | mk-single p2 d2 c2 oik s21 s22
  with vtestop-inv oik refl
... | refl , refl
  with rt-sub-unsnoc (rt-sub-trans s12 s21)
... | psub , _ =
  push1 p2 (plain _ _ _ _ _ (const _ I32 (mk-uN 0))) (rt-sub-trans s11 psub) s22

-- v128 relop / ext-binop (binop-shaped) ; ext-unop (unop-shaped).
pres-pure ok (Step-pure--vrelop c1 c2 sh op c ceq)
  with decomp ok (admininstr-VCONST V128 c1 ∷ [])
        (admininstr-VCONST V128 c2 ∷ admininstr-VRELOP sh op ∷ []) refl
... | mk-split m1 okC1 okR
  with decomp okR (admininstr-VCONST V128 c2 ∷ []) (admininstr-VRELOP sh op ∷ []) refl
... | mk-split m2 okC2 okO
  with vconst-ty okC1 | vconst-ty okC2 | singleton-inv okO
... | (p1 , s11 , s12) | (p2 , s21 , s22) | mk-single p3 d3 c3 oik s31 s32
  with vrelop-inv oik refl
... | refl , refl
  with rt-sub-unsnoc
        (subst (λ l → Resulttype-sub (mk-list (p2 ++ valtype-V128 ∷ [])) (mk-list l))
               (sym (snoc2 p3 valtype-V128 valtype-V128)) (rt-sub-trans s22 s31))
... | p2sub , _ =
  push1 p1 (plain _ _ _ _ _ (vconst _ c)) s11
    (rt-sub-trans (rt-sub-trans s12 (rt-sub-trans s21 p2sub)) s32)
pres-pure ok (Step-pure--vextbinop c1 c2 s1 s2 op c ceq)
  with decomp ok (admininstr-VCONST V128 c1 ∷ [])
        (admininstr-VCONST V128 c2 ∷ admininstr-VEXTBINOP s1 s2 op ∷ []) refl
... | mk-split m1 okC1 okR
  with decomp okR (admininstr-VCONST V128 c2 ∷ []) (admininstr-VEXTBINOP s1 s2 op ∷ []) refl
... | mk-split m2 okC2 okO
  with vconst-ty okC1 | vconst-ty okC2 | singleton-inv okO
... | (p1 , s11 , s12) | (p2 , s21 , s22) | mk-single p3 d3 c3 oik s31 s32
  with vextbinop-inv oik refl
... | refl , refl
  with rt-sub-unsnoc
        (subst (λ l → Resulttype-sub (mk-list (p2 ++ valtype-V128 ∷ [])) (mk-list l))
               (sym (snoc2 p3 valtype-V128 valtype-V128)) (rt-sub-trans s22 s31))
... | p2sub , _ =
  push1 p1 (plain _ _ _ _ _ (vconst _ c)) s11
    (rt-sub-trans (rt-sub-trans s12 (rt-sub-trans s21 p2sub)) s32)
pres-pure ok (Step-pure--vextunop c1 s1 s2 op c ceq)
  with decomp ok (admininstr-VCONST V128 c1 ∷ []) (admininstr-VEXTUNOP s1 s2 op ∷ []) refl
... | mk-split m okC okO with vconst-ty okC | singleton-inv okO
... | (p1 , s11 , s12) | mk-single p2 d2 c2 oik s21 s22
  with vextunop-inv oik refl
... | refl , refl =
  push1 p1 (plain _ _ _ _ _ (vconst _ c)) s11
    (rt-sub-trans (rt-sub-trans s12 s21) s22)

-- swizzle / shuffle (binop-shaped, distinct helper: vswizzle/vshuffle inv)
pres-pure ok (vswizzle-0 c1 c2 vM c cil cl k _ _ _ _ _)
  with decomp ok (admininstr-VCONST V128 c1 ∷ [])
        (admininstr-VCONST V128 c2 ∷
         admininstr-VSWIZZLE (ishape-X (Jnn-packtype I8) (mk-dim vM)) ∷ []) refl
... | mk-split m1 okC1 okR
  with decomp okR (admininstr-VCONST V128 c2 ∷ [])
        (admininstr-VSWIZZLE (ishape-X (Jnn-packtype I8) (mk-dim vM)) ∷ []) refl
... | mk-split m2 okC2 okO
  with vconst-ty okC1 | vconst-ty okC2 | singleton-inv okO
... | (p1 , s11 , s12) | (p2 , s21 , s22) | mk-single p3 d3 c3 oik s31 s32
  with vswizzle-inv oik refl
... | refl , refl
  with rt-sub-unsnoc
        (subst (λ l → Resulttype-sub (mk-list (p2 ++ valtype-V128 ∷ [])) (mk-list l))
               (sym (snoc2 p3 valtype-V128 valtype-V128)) (rt-sub-trans s22 s31))
... | p2sub , _ =
  push1 p1 (plain _ _ _ _ _ (vconst _ c)) s11
    (rt-sub-trans (rt-sub-trans s12 (rt-sub-trans s21 p2sub)) s32)
pres-pure ok (vswizzle-1 c1 c2 vM c cil cl k _ _ _ _ _)
  with decomp ok (admininstr-VCONST V128 c1 ∷ [])
        (admininstr-VCONST V128 c2 ∷
         admininstr-VSWIZZLE (ishape-X (Jnn-packtype I16) (mk-dim vM)) ∷ []) refl
... | mk-split m1 okC1 okR
  with decomp okR (admininstr-VCONST V128 c2 ∷ [])
        (admininstr-VSWIZZLE (ishape-X (Jnn-packtype I16) (mk-dim vM)) ∷ []) refl
... | mk-split m2 okC2 okO
  with vconst-ty okC1 | vconst-ty okC2 | singleton-inv okO
... | (p1 , s11 , s12) | (p2 , s21 , s22) | mk-single p3 d3 c3 oik s31 s32
  with vswizzle-inv oik refl
... | refl , refl
  with rt-sub-unsnoc
        (subst (λ l → Resulttype-sub (mk-list (p2 ++ valtype-V128 ∷ [])) (mk-list l))
               (sym (snoc2 p3 valtype-V128 valtype-V128)) (rt-sub-trans s22 s31))
... | p2sub , _ =
  push1 p1 (plain _ _ _ _ _ (vconst _ c)) s11
    (rt-sub-trans (rt-sub-trans s12 (rt-sub-trans s21 p2sub)) s32)
pres-pure ok (vshuffle-0 c1 c2 vN il c cl k _ _ _ _)
  with decomp ok (admininstr-VCONST V128 c1 ∷ [])
        (admininstr-VCONST V128 c2 ∷
         admininstr-VSHUFFLE (ishape-X (Jnn-packtype I8) (mk-dim vN)) il ∷ []) refl
... | mk-split m1 okC1 okR
  with decomp okR (admininstr-VCONST V128 c2 ∷ [])
        (admininstr-VSHUFFLE (ishape-X (Jnn-packtype I8) (mk-dim vN)) il ∷ []) refl
... | mk-split m2 okC2 okO
  with vconst-ty okC1 | vconst-ty okC2 | singleton-inv okO
... | (p1 , s11 , s12) | (p2 , s21 , s22) | mk-single p3 d3 c3 oik s31 s32
  with vshuffle-inv oik refl
... | refl , refl
  with rt-sub-unsnoc
        (subst (λ l → Resulttype-sub (mk-list (p2 ++ valtype-V128 ∷ [])) (mk-list l))
               (sym (snoc2 p3 valtype-V128 valtype-V128)) (rt-sub-trans s22 s31))
... | p2sub , _ =
  push1 p1 (plain _ _ _ _ _ (vconst _ c)) s11
    (rt-sub-trans (rt-sub-trans s12 (rt-sub-trans s21 p2sub)) s32)
pres-pure ok (vshuffle-1 c1 c2 vN il c cl k _ _ _ _)
  with decomp ok (admininstr-VCONST V128 c1 ∷ [])
        (admininstr-VCONST V128 c2 ∷
         admininstr-VSHUFFLE (ishape-X (Jnn-packtype I16) (mk-dim vN)) il ∷ []) refl
... | mk-split m1 okC1 okR
  with decomp okR (admininstr-VCONST V128 c2 ∷ [])
        (admininstr-VSHUFFLE (ishape-X (Jnn-packtype I16) (mk-dim vN)) il ∷ []) refl
... | mk-split m2 okC2 okO
  with vconst-ty okC1 | vconst-ty okC2 | singleton-inv okO
... | (p1 , s11 , s12) | (p2 , s21 , s22) | mk-single p3 d3 c3 oik s31 s32
  with vshuffle-inv oik refl
... | refl , refl
  with rt-sub-unsnoc
        (subst (λ l → Resulttype-sub (mk-list (p2 ++ valtype-V128 ∷ [])) (mk-list l))
               (sym (snoc2 p3 valtype-V128 valtype-V128)) (rt-sub-trans s22 s31))
... | p2sub , _ =
  push1 p1 (plain _ _ _ _ _ (vconst _ c)) s11
    (rt-sub-trans (rt-sub-trans s12 (rt-sub-trans s21 p2sub)) s32)

pres-pure ok (vshiftop-0 c1 _ _ _ c _ _ _)
  with decomp ok (admininstr-VCONST V128 c1 ∷ []) (admininstr-CONST I32 _ ∷ admininstr-VSHIFTOP _ _ ∷ []) refl
... | mk-split m1 okC1 okR
  with decomp okR (admininstr-CONST I32 _ ∷ []) (admininstr-VSHIFTOP _ _ ∷ []) refl
... | mk-split m2 okC2 okO
  with vconst-ty okC1 | const-ty okC2 | singleton-inv okO
... | (p1 , s11 , s12) | (p2 , s21 , s22) | mk-single p3 d3 c3 oik s31 s32
  with vshiftop-inv oik refl
... | refl , refl
  with rt-sub-unsnoc
        (subst (λ l → Resulttype-sub (mk-list (p2 ++ valtype-numtype I32 ∷ [])) (mk-list l))
               (sym (snoc2 p3 valtype-V128 (valtype-numtype I32))) (rt-sub-trans s22 s31))
... | p2sub , _
  with rt-sub-unsnoc (rt-sub-trans s12 (rt-sub-trans s21 p2sub))
... | p1sub , _ =
  push1 p3 (plain _ _ _ _ _ (vconst _ c)) (rt-sub-trans s11 p1sub) s32
pres-pure ok (vshiftop-1 c1 _ _ _ c _ _ _)
  with decomp ok (admininstr-VCONST V128 c1 ∷ []) (admininstr-CONST I32 _ ∷ admininstr-VSHIFTOP _ _ ∷ []) refl
... | mk-split m1 okC1 okR
  with decomp okR (admininstr-CONST I32 _ ∷ []) (admininstr-VSHIFTOP _ _ ∷ []) refl
... | mk-split m2 okC2 okO
  with vconst-ty okC1 | const-ty okC2 | singleton-inv okO
... | (p1 , s11 , s12) | (p2 , s21 , s22) | mk-single p3 d3 c3 oik s31 s32
  with vshiftop-inv oik refl
... | refl , refl
  with rt-sub-unsnoc
        (subst (λ l → Resulttype-sub (mk-list (p2 ++ valtype-numtype I32 ∷ [])) (mk-list l))
               (sym (snoc2 p3 valtype-V128 (valtype-numtype I32))) (rt-sub-trans s22 s31))
... | p2sub , _
  with rt-sub-unsnoc (rt-sub-trans s12 (rt-sub-trans s21 p2sub))
... | p1sub , _ =
  push1 p3 (plain _ _ _ _ _ (vconst _ c)) (rt-sub-trans s11 p1sub) s32
pres-pure ok (vshiftop-2 c1 _ _ _ c _ _ _)
  with decomp ok (admininstr-VCONST V128 c1 ∷ []) (admininstr-CONST I32 _ ∷ admininstr-VSHIFTOP _ _ ∷ []) refl
... | mk-split m1 okC1 okR
  with decomp okR (admininstr-CONST I32 _ ∷ []) (admininstr-VSHIFTOP _ _ ∷ []) refl
... | mk-split m2 okC2 okO
  with vconst-ty okC1 | const-ty okC2 | singleton-inv okO
... | (p1 , s11 , s12) | (p2 , s21 , s22) | mk-single p3 d3 c3 oik s31 s32
  with vshiftop-inv oik refl
... | refl , refl
  with rt-sub-unsnoc
        (subst (λ l → Resulttype-sub (mk-list (p2 ++ valtype-numtype I32 ∷ [])) (mk-list l))
               (sym (snoc2 p3 valtype-V128 (valtype-numtype I32))) (rt-sub-trans s22 s31))
... | p2sub , _
  with rt-sub-unsnoc (rt-sub-trans s12 (rt-sub-trans s21 p2sub))
... | p1sub , _ =
  push1 p3 (plain _ _ _ _ _ (vconst _ c)) (rt-sub-trans s11 p1sub) s32
pres-pure ok (vshiftop-3 c1 _ _ _ c _ _ _)
  with decomp ok (admininstr-VCONST V128 c1 ∷ []) (admininstr-CONST I32 _ ∷ admininstr-VSHIFTOP _ _ ∷ []) refl
... | mk-split m1 okC1 okR
  with decomp okR (admininstr-CONST I32 _ ∷ []) (admininstr-VSHIFTOP _ _ ∷ []) refl
... | mk-split m2 okC2 okO
  with vconst-ty okC1 | const-ty okC2 | singleton-inv okO
... | (p1 , s11 , s12) | (p2 , s21 , s22) | mk-single p3 d3 c3 oik s31 s32
  with vshiftop-inv oik refl
... | refl , refl
  with rt-sub-unsnoc
        (subst (λ l → Resulttype-sub (mk-list (p2 ++ valtype-numtype I32 ∷ [])) (mk-list l))
               (sym (snoc2 p3 valtype-V128 (valtype-numtype I32))) (rt-sub-trans s22 s31))
... | p2sub , _
  with rt-sub-unsnoc (rt-sub-trans s12 (rt-sub-trans s21 p2sub))
... | p1sub , _ =
  push1 p3 (plain _ _ _ _ _ (vconst _ c)) (rt-sub-trans s11 p1sub) s32
pres-pure ok (vbitmask-0 c1 _ ci _ _ _)
  with decomp ok (admininstr-VCONST V128 c1 ∷ []) (admininstr-VBITMASK _ ∷ []) refl
... | mk-split m okC okO with vconst-ty okC | singleton-inv okO
... | (p1 , s11 , s12) | mk-single p2 d2 c2 oik s21 s22
  with vbitmask-inv oik refl
... | refl , refl
  with rt-sub-unsnoc (rt-sub-trans s12 s21)
... | p1sub , _ =
  push1 p2 (plain _ _ _ _ _ (const _ I32 (irev- 32 ci))) (rt-sub-trans s11 p1sub) s22
pres-pure ok (vbitmask-1 c1 _ ci _ _ _)
  with decomp ok (admininstr-VCONST V128 c1 ∷ []) (admininstr-VBITMASK _ ∷ []) refl
... | mk-split m okC okO with vconst-ty okC | singleton-inv okO
... | (p1 , s11 , s12) | mk-single p2 d2 c2 oik s21 s22
  with vbitmask-inv oik refl
... | refl , refl
  with rt-sub-unsnoc (rt-sub-trans s12 s21)
... | p1sub , _ =
  push1 p2 (plain _ _ _ _ _ (const _ I32 (irev- 32 ci))) (rt-sub-trans s11 p1sub) s22
pres-pure ok (vbitmask-2 c1 _ ci _ _ _)
  with decomp ok (admininstr-VCONST V128 c1 ∷ []) (admininstr-VBITMASK _ ∷ []) refl
... | mk-split m okC okO with vconst-ty okC | singleton-inv okO
... | (p1 , s11 , s12) | mk-single p2 d2 c2 oik s21 s22
  with vbitmask-inv oik refl
... | refl , refl
  with rt-sub-unsnoc (rt-sub-trans s12 s21)
... | p1sub , _ =
  push1 p2 (plain _ _ _ _ _ (const _ I32 (irev- 32 ci))) (rt-sub-trans s11 p1sub) s22
pres-pure ok (vbitmask-3 c1 _ ci _ _ _)
  with decomp ok (admininstr-VCONST V128 c1 ∷ []) (admininstr-VBITMASK _ ∷ []) refl
... | mk-split m okC okO with vconst-ty okC | singleton-inv okO
... | (p1 , s11 , s12) | mk-single p2 d2 c2 oik s21 s22
  with vbitmask-inv oik refl
... | refl , refl
  with rt-sub-unsnoc (rt-sub-trans s12 s21)
... | p1sub , _ =
  push1 p2 (plain _ _ _ _ _ (const _ I32 (irev- 32 ci))) (rt-sub-trans s11 p1sub) s22
pres-pure ok (vnarrow-0 c1 c2 _ _ _ c _ _ _ _ _ _ _ _ _)
  with decomp ok (admininstr-VCONST V128 c1 ∷ []) (admininstr-VCONST V128 c2 ∷ admininstr-VNARROW _ _ _ ∷ []) refl
... | mk-split m1 okC1 okR
  with decomp okR (admininstr-VCONST V128 c2 ∷ []) (admininstr-VNARROW _ _ _ ∷ []) refl
... | mk-split m2 okC2 okO
  with vconst-ty okC1 | vconst-ty okC2 | singleton-inv okO
... | (p1 , s11 , s12) | (p2 , s21 , s22) | mk-single p3 d3 c3 oik s31 s32
  with vnarrow-inv oik refl
... | refl , refl
  with rt-sub-unsnoc
        (subst (λ l → Resulttype-sub (mk-list (p2 ++ valtype-V128 ∷ [])) (mk-list l))
               (sym (snoc2 p3 valtype-V128 valtype-V128)) (rt-sub-trans s22 s31))
... | p2sub , _
  with rt-sub-unsnoc (rt-sub-trans s12 (rt-sub-trans s21 p2sub))
... | p1sub , _ =
  push1 p3 (plain _ _ _ _ _ (vconst _ c)) (rt-sub-trans s11 p1sub) s32
pres-pure ok (vnarrow-1 c1 c2 _ _ _ c _ _ _ _ _ _ _ _ _)
  with decomp ok (admininstr-VCONST V128 c1 ∷ []) (admininstr-VCONST V128 c2 ∷ admininstr-VNARROW _ _ _ ∷ []) refl
... | mk-split m1 okC1 okR
  with decomp okR (admininstr-VCONST V128 c2 ∷ []) (admininstr-VNARROW _ _ _ ∷ []) refl
... | mk-split m2 okC2 okO
  with vconst-ty okC1 | vconst-ty okC2 | singleton-inv okO
... | (p1 , s11 , s12) | (p2 , s21 , s22) | mk-single p3 d3 c3 oik s31 s32
  with vnarrow-inv oik refl
... | refl , refl
  with rt-sub-unsnoc
        (subst (λ l → Resulttype-sub (mk-list (p2 ++ valtype-V128 ∷ [])) (mk-list l))
               (sym (snoc2 p3 valtype-V128 valtype-V128)) (rt-sub-trans s22 s31))
... | p2sub , _
  with rt-sub-unsnoc (rt-sub-trans s12 (rt-sub-trans s21 p2sub))
... | p1sub , _ =
  push1 p3 (plain _ _ _ _ _ (vconst _ c)) (rt-sub-trans s11 p1sub) s32
pres-pure ok (vnarrow-2 c1 c2 _ _ _ c _ _ _ _ _ _ _ _ _)
  with decomp ok (admininstr-VCONST V128 c1 ∷ []) (admininstr-VCONST V128 c2 ∷ admininstr-VNARROW _ _ _ ∷ []) refl
... | mk-split m1 okC1 okR
  with decomp okR (admininstr-VCONST V128 c2 ∷ []) (admininstr-VNARROW _ _ _ ∷ []) refl
... | mk-split m2 okC2 okO
  with vconst-ty okC1 | vconst-ty okC2 | singleton-inv okO
... | (p1 , s11 , s12) | (p2 , s21 , s22) | mk-single p3 d3 c3 oik s31 s32
  with vnarrow-inv oik refl
... | refl , refl
  with rt-sub-unsnoc
        (subst (λ l → Resulttype-sub (mk-list (p2 ++ valtype-V128 ∷ [])) (mk-list l))
               (sym (snoc2 p3 valtype-V128 valtype-V128)) (rt-sub-trans s22 s31))
... | p2sub , _
  with rt-sub-unsnoc (rt-sub-trans s12 (rt-sub-trans s21 p2sub))
... | p1sub , _ =
  push1 p3 (plain _ _ _ _ _ (vconst _ c)) (rt-sub-trans s11 p1sub) s32
pres-pure ok (vnarrow-3 c1 c2 _ _ _ c _ _ _ _ _ _ _ _ _)
  with decomp ok (admininstr-VCONST V128 c1 ∷ []) (admininstr-VCONST V128 c2 ∷ admininstr-VNARROW _ _ _ ∷ []) refl
... | mk-split m1 okC1 okR
  with decomp okR (admininstr-VCONST V128 c2 ∷ []) (admininstr-VNARROW _ _ _ ∷ []) refl
... | mk-split m2 okC2 okO
  with vconst-ty okC1 | vconst-ty okC2 | singleton-inv okO
... | (p1 , s11 , s12) | (p2 , s21 , s22) | mk-single p3 d3 c3 oik s31 s32
  with vnarrow-inv oik refl
... | refl , refl
  with rt-sub-unsnoc
        (subst (λ l → Resulttype-sub (mk-list (p2 ++ valtype-V128 ∷ [])) (mk-list l))
               (sym (snoc2 p3 valtype-V128 valtype-V128)) (rt-sub-trans s22 s31))
... | p2sub , _
  with rt-sub-unsnoc (rt-sub-trans s12 (rt-sub-trans s21 p2sub))
... | p1sub , _ =
  push1 p3 (plain _ _ _ _ _ (vconst _ c)) (rt-sub-trans s11 p1sub) s32
pres-pure ok (vnarrow-4 c1 c2 _ _ _ c _ _ _ _ _ _ _ _ _)
  with decomp ok (admininstr-VCONST V128 c1 ∷ []) (admininstr-VCONST V128 c2 ∷ admininstr-VNARROW _ _ _ ∷ []) refl
... | mk-split m1 okC1 okR
  with decomp okR (admininstr-VCONST V128 c2 ∷ []) (admininstr-VNARROW _ _ _ ∷ []) refl
... | mk-split m2 okC2 okO
  with vconst-ty okC1 | vconst-ty okC2 | singleton-inv okO
... | (p1 , s11 , s12) | (p2 , s21 , s22) | mk-single p3 d3 c3 oik s31 s32
  with vnarrow-inv oik refl
... | refl , refl
  with rt-sub-unsnoc
        (subst (λ l → Resulttype-sub (mk-list (p2 ++ valtype-V128 ∷ [])) (mk-list l))
               (sym (snoc2 p3 valtype-V128 valtype-V128)) (rt-sub-trans s22 s31))
... | p2sub , _
  with rt-sub-unsnoc (rt-sub-trans s12 (rt-sub-trans s21 p2sub))
... | p1sub , _ =
  push1 p3 (plain _ _ _ _ _ (vconst _ c)) (rt-sub-trans s11 p1sub) s32
pres-pure ok (vnarrow-5 c1 c2 _ _ _ c _ _ _ _ _ _ _ _ _)
  with decomp ok (admininstr-VCONST V128 c1 ∷ []) (admininstr-VCONST V128 c2 ∷ admininstr-VNARROW _ _ _ ∷ []) refl
... | mk-split m1 okC1 okR
  with decomp okR (admininstr-VCONST V128 c2 ∷ []) (admininstr-VNARROW _ _ _ ∷ []) refl
... | mk-split m2 okC2 okO
  with vconst-ty okC1 | vconst-ty okC2 | singleton-inv okO
... | (p1 , s11 , s12) | (p2 , s21 , s22) | mk-single p3 d3 c3 oik s31 s32
  with vnarrow-inv oik refl
... | refl , refl
  with rt-sub-unsnoc
        (subst (λ l → Resulttype-sub (mk-list (p2 ++ valtype-V128 ∷ [])) (mk-list l))
               (sym (snoc2 p3 valtype-V128 valtype-V128)) (rt-sub-trans s22 s31))
... | p2sub , _
  with rt-sub-unsnoc (rt-sub-trans s12 (rt-sub-trans s21 p2sub))
... | p1sub , _ =
  push1 p3 (plain _ _ _ _ _ (vconst _ c)) (rt-sub-trans s11 p1sub) s32
pres-pure ok (vnarrow-6 c1 c2 _ _ _ c _ _ _ _ _ _ _ _ _)
  with decomp ok (admininstr-VCONST V128 c1 ∷ []) (admininstr-VCONST V128 c2 ∷ admininstr-VNARROW _ _ _ ∷ []) refl
... | mk-split m1 okC1 okR
  with decomp okR (admininstr-VCONST V128 c2 ∷ []) (admininstr-VNARROW _ _ _ ∷ []) refl
... | mk-split m2 okC2 okO
  with vconst-ty okC1 | vconst-ty okC2 | singleton-inv okO
... | (p1 , s11 , s12) | (p2 , s21 , s22) | mk-single p3 d3 c3 oik s31 s32
  with vnarrow-inv oik refl
... | refl , refl
  with rt-sub-unsnoc
        (subst (λ l → Resulttype-sub (mk-list (p2 ++ valtype-V128 ∷ [])) (mk-list l))
               (sym (snoc2 p3 valtype-V128 valtype-V128)) (rt-sub-trans s22 s31))
... | p2sub , _
  with rt-sub-unsnoc (rt-sub-trans s12 (rt-sub-trans s21 p2sub))
... | p1sub , _ =
  push1 p3 (plain _ _ _ _ _ (vconst _ c)) (rt-sub-trans s11 p1sub) s32
pres-pure ok (vnarrow-7 c1 c2 _ _ _ c _ _ _ _ _ _ _ _ _)
  with decomp ok (admininstr-VCONST V128 c1 ∷ []) (admininstr-VCONST V128 c2 ∷ admininstr-VNARROW _ _ _ ∷ []) refl
... | mk-split m1 okC1 okR
  with decomp okR (admininstr-VCONST V128 c2 ∷ []) (admininstr-VNARROW _ _ _ ∷ []) refl
... | mk-split m2 okC2 okO
  with vconst-ty okC1 | vconst-ty okC2 | singleton-inv okO
... | (p1 , s11 , s12) | (p2 , s21 , s22) | mk-single p3 d3 c3 oik s31 s32
  with vnarrow-inv oik refl
... | refl , refl
  with rt-sub-unsnoc
        (subst (λ l → Resulttype-sub (mk-list (p2 ++ valtype-V128 ∷ [])) (mk-list l))
               (sym (snoc2 p3 valtype-V128 valtype-V128)) (rt-sub-trans s22 s31))
... | p2sub , _
  with rt-sub-unsnoc (rt-sub-trans s12 (rt-sub-trans s21 p2sub))
... | p1sub , _ =
  push1 p3 (plain _ _ _ _ _ (vconst _ c)) (rt-sub-trans s11 p1sub) s32
pres-pure ok (vnarrow-8 c1 c2 _ _ _ c _ _ _ _ _ _ _ _ _)
  with decomp ok (admininstr-VCONST V128 c1 ∷ []) (admininstr-VCONST V128 c2 ∷ admininstr-VNARROW _ _ _ ∷ []) refl
... | mk-split m1 okC1 okR
  with decomp okR (admininstr-VCONST V128 c2 ∷ []) (admininstr-VNARROW _ _ _ ∷ []) refl
... | mk-split m2 okC2 okO
  with vconst-ty okC1 | vconst-ty okC2 | singleton-inv okO
... | (p1 , s11 , s12) | (p2 , s21 , s22) | mk-single p3 d3 c3 oik s31 s32
  with vnarrow-inv oik refl
... | refl , refl
  with rt-sub-unsnoc
        (subst (λ l → Resulttype-sub (mk-list (p2 ++ valtype-V128 ∷ [])) (mk-list l))
               (sym (snoc2 p3 valtype-V128 valtype-V128)) (rt-sub-trans s22 s31))
... | p2sub , _
  with rt-sub-unsnoc (rt-sub-trans s12 (rt-sub-trans s21 p2sub))
... | p1sub , _ =
  push1 p3 (plain _ _ _ _ _ (vconst _ c)) (rt-sub-trans s11 p1sub) s32
pres-pure ok (vnarrow-9 c1 c2 _ _ _ c _ _ _ _ _ _ _ _ _)
  with decomp ok (admininstr-VCONST V128 c1 ∷ []) (admininstr-VCONST V128 c2 ∷ admininstr-VNARROW _ _ _ ∷ []) refl
... | mk-split m1 okC1 okR
  with decomp okR (admininstr-VCONST V128 c2 ∷ []) (admininstr-VNARROW _ _ _ ∷ []) refl
... | mk-split m2 okC2 okO
  with vconst-ty okC1 | vconst-ty okC2 | singleton-inv okO
... | (p1 , s11 , s12) | (p2 , s21 , s22) | mk-single p3 d3 c3 oik s31 s32
  with vnarrow-inv oik refl
... | refl , refl
  with rt-sub-unsnoc
        (subst (λ l → Resulttype-sub (mk-list (p2 ++ valtype-V128 ∷ [])) (mk-list l))
               (sym (snoc2 p3 valtype-V128 valtype-V128)) (rt-sub-trans s22 s31))
... | p2sub , _
  with rt-sub-unsnoc (rt-sub-trans s12 (rt-sub-trans s21 p2sub))
... | p1sub , _ =
  push1 p3 (plain _ _ _ _ _ (vconst _ c)) (rt-sub-trans s11 p1sub) s32
pres-pure ok (vnarrow-10 c1 c2 _ _ _ c _ _ _ _ _ _ _ _ _)
  with decomp ok (admininstr-VCONST V128 c1 ∷ []) (admininstr-VCONST V128 c2 ∷ admininstr-VNARROW _ _ _ ∷ []) refl
... | mk-split m1 okC1 okR
  with decomp okR (admininstr-VCONST V128 c2 ∷ []) (admininstr-VNARROW _ _ _ ∷ []) refl
... | mk-split m2 okC2 okO
  with vconst-ty okC1 | vconst-ty okC2 | singleton-inv okO
... | (p1 , s11 , s12) | (p2 , s21 , s22) | mk-single p3 d3 c3 oik s31 s32
  with vnarrow-inv oik refl
... | refl , refl
  with rt-sub-unsnoc
        (subst (λ l → Resulttype-sub (mk-list (p2 ++ valtype-V128 ∷ [])) (mk-list l))
               (sym (snoc2 p3 valtype-V128 valtype-V128)) (rt-sub-trans s22 s31))
... | p2sub , _
  with rt-sub-unsnoc (rt-sub-trans s12 (rt-sub-trans s21 p2sub))
... | p1sub , _ =
  push1 p3 (plain _ _ _ _ _ (vconst _ c)) (rt-sub-trans s11 p1sub) s32
pres-pure ok (vnarrow-11 c1 c2 _ _ _ c _ _ _ _ _ _ _ _ _)
  with decomp ok (admininstr-VCONST V128 c1 ∷ []) (admininstr-VCONST V128 c2 ∷ admininstr-VNARROW _ _ _ ∷ []) refl
... | mk-split m1 okC1 okR
  with decomp okR (admininstr-VCONST V128 c2 ∷ []) (admininstr-VNARROW _ _ _ ∷ []) refl
... | mk-split m2 okC2 okO
  with vconst-ty okC1 | vconst-ty okC2 | singleton-inv okO
... | (p1 , s11 , s12) | (p2 , s21 , s22) | mk-single p3 d3 c3 oik s31 s32
  with vnarrow-inv oik refl
... | refl , refl
  with rt-sub-unsnoc
        (subst (λ l → Resulttype-sub (mk-list (p2 ++ valtype-V128 ∷ [])) (mk-list l))
               (sym (snoc2 p3 valtype-V128 valtype-V128)) (rt-sub-trans s22 s31))
... | p2sub , _
  with rt-sub-unsnoc (rt-sub-trans s12 (rt-sub-trans s21 p2sub))
... | p1sub , _ =
  push1 p3 (plain _ _ _ _ _ (vconst _ c)) (rt-sub-trans s11 p1sub) s32
pres-pure ok (vnarrow-12 c1 c2 _ _ _ c _ _ _ _ _ _ _ _ _)
  with decomp ok (admininstr-VCONST V128 c1 ∷ []) (admininstr-VCONST V128 c2 ∷ admininstr-VNARROW _ _ _ ∷ []) refl
... | mk-split m1 okC1 okR
  with decomp okR (admininstr-VCONST V128 c2 ∷ []) (admininstr-VNARROW _ _ _ ∷ []) refl
... | mk-split m2 okC2 okO
  with vconst-ty okC1 | vconst-ty okC2 | singleton-inv okO
... | (p1 , s11 , s12) | (p2 , s21 , s22) | mk-single p3 d3 c3 oik s31 s32
  with vnarrow-inv oik refl
... | refl , refl
  with rt-sub-unsnoc
        (subst (λ l → Resulttype-sub (mk-list (p2 ++ valtype-V128 ∷ [])) (mk-list l))
               (sym (snoc2 p3 valtype-V128 valtype-V128)) (rt-sub-trans s22 s31))
... | p2sub , _
  with rt-sub-unsnoc (rt-sub-trans s12 (rt-sub-trans s21 p2sub))
... | p1sub , _ =
  push1 p3 (plain _ _ _ _ _ (vconst _ c)) (rt-sub-trans s11 p1sub) s32
pres-pure ok (vnarrow-13 c1 c2 _ _ _ c _ _ _ _ _ _ _ _ _)
  with decomp ok (admininstr-VCONST V128 c1 ∷ []) (admininstr-VCONST V128 c2 ∷ admininstr-VNARROW _ _ _ ∷ []) refl
... | mk-split m1 okC1 okR
  with decomp okR (admininstr-VCONST V128 c2 ∷ []) (admininstr-VNARROW _ _ _ ∷ []) refl
... | mk-split m2 okC2 okO
  with vconst-ty okC1 | vconst-ty okC2 | singleton-inv okO
... | (p1 , s11 , s12) | (p2 , s21 , s22) | mk-single p3 d3 c3 oik s31 s32
  with vnarrow-inv oik refl
... | refl , refl
  with rt-sub-unsnoc
        (subst (λ l → Resulttype-sub (mk-list (p2 ++ valtype-V128 ∷ [])) (mk-list l))
               (sym (snoc2 p3 valtype-V128 valtype-V128)) (rt-sub-trans s22 s31))
... | p2sub , _
  with rt-sub-unsnoc (rt-sub-trans s12 (rt-sub-trans s21 p2sub))
... | p1sub , _ =
  push1 p3 (plain _ _ _ _ _ (vconst _ c)) (rt-sub-trans s11 p1sub) s32
pres-pure ok (vnarrow-14 c1 c2 _ _ _ c _ _ _ _ _ _ _ _ _)
  with decomp ok (admininstr-VCONST V128 c1 ∷ []) (admininstr-VCONST V128 c2 ∷ admininstr-VNARROW _ _ _ ∷ []) refl
... | mk-split m1 okC1 okR
  with decomp okR (admininstr-VCONST V128 c2 ∷ []) (admininstr-VNARROW _ _ _ ∷ []) refl
... | mk-split m2 okC2 okO
  with vconst-ty okC1 | vconst-ty okC2 | singleton-inv okO
... | (p1 , s11 , s12) | (p2 , s21 , s22) | mk-single p3 d3 c3 oik s31 s32
  with vnarrow-inv oik refl
... | refl , refl
  with rt-sub-unsnoc
        (subst (λ l → Resulttype-sub (mk-list (p2 ++ valtype-V128 ∷ [])) (mk-list l))
               (sym (snoc2 p3 valtype-V128 valtype-V128)) (rt-sub-trans s22 s31))
... | p2sub , _
  with rt-sub-unsnoc (rt-sub-trans s12 (rt-sub-trans s21 p2sub))
... | p1sub , _ =
  push1 p3 (plain _ _ _ _ _ (vconst _ c)) (rt-sub-trans s11 p1sub) s32
pres-pure ok (vnarrow-15 c1 c2 _ _ _ c _ _ _ _ _ _ _ _ _)
  with decomp ok (admininstr-VCONST V128 c1 ∷ []) (admininstr-VCONST V128 c2 ∷ admininstr-VNARROW _ _ _ ∷ []) refl
... | mk-split m1 okC1 okR
  with decomp okR (admininstr-VCONST V128 c2 ∷ []) (admininstr-VNARROW _ _ _ ∷ []) refl
... | mk-split m2 okC2 okO
  with vconst-ty okC1 | vconst-ty okC2 | singleton-inv okO
... | (p1 , s11 , s12) | (p2 , s21 , s22) | mk-single p3 d3 c3 oik s31 s32
  with vnarrow-inv oik refl
... | refl , refl
  with rt-sub-unsnoc
        (subst (λ l → Resulttype-sub (mk-list (p2 ++ valtype-V128 ∷ [])) (mk-list l))
               (sym (snoc2 p3 valtype-V128 valtype-V128)) (rt-sub-trans s22 s31))
... | p2sub , _
  with rt-sub-unsnoc (rt-sub-trans s12 (rt-sub-trans s21 p2sub))
... | p1sub , _ =
  push1 p3 (plain _ _ _ _ _ (vconst _ c)) (rt-sub-trans s11 p1sub) s32
pres-pure ok (vcvtop-full c1 _ _ _ _ c _ _ _ _ _ _ _)
  with decomp ok (admininstr-VCONST V128 c1 ∷ []) (admininstr-VCVTOP _ _ _ ∷ []) refl
... | mk-split m okC okO with vconst-ty okC | singleton-inv okO
... | (p1 , s11 , s12) | mk-single p2 d2 c2 oik s21 s22
  with vcvtop-inv oik refl
... | refl , refl =
  push1 p1 (plain _ _ _ _ _ (vconst _ c)) s11
    (rt-sub-trans (rt-sub-trans s12 s21) s22)
pres-pure ok (vcvtop-half c1 _ _ _ _ _ c _ _ _ _ _ _ _ _)
  with decomp ok (admininstr-VCONST V128 c1 ∷ []) (admininstr-VCVTOP _ _ _ ∷ []) refl
... | mk-split m okC okO with vconst-ty okC | singleton-inv okO
... | (p1 , s11 , s12) | mk-single p2 d2 c2 oik s21 s22
  with vcvtop-inv oik refl
... | refl , refl =
  push1 p1 (plain _ _ _ _ _ (vconst _ c)) s11
    (rt-sub-trans (rt-sub-trans s12 s21) s22)
pres-pure ok (vcvtop-zero-0 c1 _ _ _ c _ _ _ _ _ _ _)
  with decomp ok (admininstr-VCONST V128 c1 ∷ []) (admininstr-VCVTOP _ _ _ ∷ []) refl
... | mk-split m okC okO with vconst-ty okC | singleton-inv okO
... | (p1 , s11 , s12) | mk-single p2 d2 c2 oik s21 s22
  with vcvtop-inv oik refl
... | refl , refl =
  push1 p1 (plain _ _ _ _ _ (vconst _ c)) s11
    (rt-sub-trans (rt-sub-trans s12 s21) s22)
pres-pure ok (vcvtop-zero-1 c1 _ _ _ c _ _ _ _ _ _ _)
  with decomp ok (admininstr-VCONST V128 c1 ∷ []) (admininstr-VCVTOP _ _ _ ∷ []) refl
... | mk-split m okC okO with vconst-ty okC | singleton-inv okO
... | (p1 , s11 , s12) | mk-single p2 d2 c2 oik s21 s22
  with vcvtop-inv oik refl
... | refl , refl =
  push1 p1 (plain _ _ _ _ _ (vconst _ c)) s11
    (rt-sub-trans (rt-sub-trans s12 s21) s22)
pres-pure ok (vcvtop-zero-2 c1 _ _ _ c _ _ _ _ _ _ _)
  with decomp ok (admininstr-VCONST V128 c1 ∷ []) (admininstr-VCVTOP _ _ _ ∷ []) refl
... | mk-split m okC okO with vconst-ty okC | singleton-inv okO
... | (p1 , s11 , s12) | mk-single p2 d2 c2 oik s21 s22
  with vcvtop-inv oik refl
... | refl , refl =
  push1 p1 (plain _ _ _ _ _ (vconst _ c)) s11
    (rt-sub-trans (rt-sub-trans s12 s21) s22)
pres-pure ok (vcvtop-zero-3 c1 _ _ _ c _ _ _ _ _ _ _)
  with decomp ok (admininstr-VCONST V128 c1 ∷ []) (admininstr-VCVTOP _ _ _ ∷ []) refl
... | mk-split m okC okO with vconst-ty okC | singleton-inv okO
... | (p1 , s11 , s12) | mk-single p2 d2 c2 oik s21 s22
  with vcvtop-inv oik refl
... | refl , refl =
  push1 p1 (plain _ _ _ _ _ (vconst _ c)) s11
    (rt-sub-trans (rt-sub-trans s12 s21) s22)
pres-pure ok (vcvtop-zero-4 c1 _ _ _ c _ _ _ _ _ _ _)
  with decomp ok (admininstr-VCONST V128 c1 ∷ []) (admininstr-VCVTOP _ _ _ ∷ []) refl
... | mk-split m okC okO with vconst-ty okC | singleton-inv okO
... | (p1 , s11 , s12) | mk-single p2 d2 c2 oik s21 s22
  with vcvtop-inv oik refl
... | refl , refl =
  push1 p1 (plain _ _ _ _ _ (vconst _ c)) s11
    (rt-sub-trans (rt-sub-trans s12 s21) s22)
pres-pure ok (vcvtop-zero-5 c1 _ _ _ c _ _ _ _ _ _ _)
  with decomp ok (admininstr-VCONST V128 c1 ∷ []) (admininstr-VCVTOP _ _ _ ∷ []) refl
... | mk-split m okC okO with vconst-ty okC | singleton-inv okO
... | (p1 , s11 , s12) | mk-single p2 d2 c2 oik s21 s22
  with vcvtop-inv oik refl
... | refl , refl =
  push1 p1 (plain _ _ _ _ _ (vconst _ c)) s11
    (rt-sub-trans (rt-sub-trans s12 s21) s22)
pres-pure ok (vcvtop-zero-6 c1 _ _ _ c _ _ _ _ _ _ _)
  with decomp ok (admininstr-VCONST V128 c1 ∷ []) (admininstr-VCVTOP _ _ _ ∷ []) refl
... | mk-split m okC okO with vconst-ty okC | singleton-inv okO
... | (p1 , s11 , s12) | mk-single p2 d2 c2 oik s21 s22
  with vcvtop-inv oik refl
... | refl , refl =
  push1 p1 (plain _ _ _ _ _ (vconst _ c)) s11
    (rt-sub-trans (rt-sub-trans s12 s21) s22)
pres-pure ok (vcvtop-zero-7 c1 _ _ _ c _ _ _ _ _ _ _)
  with decomp ok (admininstr-VCONST V128 c1 ∷ []) (admininstr-VCVTOP _ _ _ ∷ []) refl
... | mk-split m okC okO with vconst-ty okC | singleton-inv okO
... | (p1 , s11 , s12) | mk-single p2 d2 c2 oik s21 s22
  with vcvtop-inv oik refl
... | refl , refl =
  push1 p1 (plain _ _ _ _ _ (vconst _ c)) s11
    (rt-sub-trans (rt-sub-trans s12 s21) s22)
pres-pure ok (vcvtop-zero-8 c1 _ _ _ c _ _ _ _ _ _ _)
  with decomp ok (admininstr-VCONST V128 c1 ∷ []) (admininstr-VCVTOP _ _ _ ∷ []) refl
... | mk-split m okC okO with vconst-ty okC | singleton-inv okO
... | (p1 , s11 , s12) | mk-single p2 d2 c2 oik s21 s22
  with vcvtop-inv oik refl
... | refl , refl =
  push1 p1 (plain _ _ _ _ _ (vconst _ c)) s11
    (rt-sub-trans (rt-sub-trans s12 s21) s22)
pres-pure ok (vcvtop-zero-9 c1 _ _ _ c _ _ _ _ _ _ _)
  with decomp ok (admininstr-VCONST V128 c1 ∷ []) (admininstr-VCVTOP _ _ _ ∷ []) refl
... | mk-split m okC okO with vconst-ty okC | singleton-inv okO
... | (p1 , s11 , s12) | mk-single p2 d2 c2 oik s21 s22
  with vcvtop-inv oik refl
... | refl , refl =
  push1 p1 (plain _ _ _ _ _ (vconst _ c)) s11
    (rt-sub-trans (rt-sub-trans s12 s21) s22)
pres-pure ok (vcvtop-zero-10 c1 _ _ _ c _ _ _ _ _ _ _)
  with decomp ok (admininstr-VCONST V128 c1 ∷ []) (admininstr-VCVTOP _ _ _ ∷ []) refl
... | mk-split m okC okO with vconst-ty okC | singleton-inv okO
... | (p1 , s11 , s12) | mk-single p2 d2 c2 oik s21 s22
  with vcvtop-inv oik refl
... | refl , refl =
  push1 p1 (plain _ _ _ _ _ (vconst _ c)) s11
    (rt-sub-trans (rt-sub-trans s12 s21) s22)
pres-pure ok (vcvtop-zero-11 c1 _ _ _ c _ _ _ _ _ _ _)
  with decomp ok (admininstr-VCONST V128 c1 ∷ []) (admininstr-VCVTOP _ _ _ ∷ []) refl
... | mk-split m okC okO with vconst-ty okC | singleton-inv okO
... | (p1 , s11 , s12) | mk-single p2 d2 c2 oik s21 s22
  with vcvtop-inv oik refl
... | refl , refl =
  push1 p1 (plain _ _ _ _ _ (vconst _ c)) s11
    (rt-sub-trans (rt-sub-trans s12 s21) s22)
pres-pure ok (vcvtop-zero-12 c1 _ _ _ c _ _ _ _ _ _ _)
  with decomp ok (admininstr-VCONST V128 c1 ∷ []) (admininstr-VCVTOP _ _ _ ∷ []) refl
... | mk-split m okC okO with vconst-ty okC | singleton-inv okO
... | (p1 , s11 , s12) | mk-single p2 d2 c2 oik s21 s22
  with vcvtop-inv oik refl
... | refl , refl =
  push1 p1 (plain _ _ _ _ _ (vconst _ c)) s11
    (rt-sub-trans (rt-sub-trans s12 s21) s22)
pres-pure ok (vcvtop-zero-13 c1 _ _ _ c _ _ _ _ _ _ _)
  with decomp ok (admininstr-VCONST V128 c1 ∷ []) (admininstr-VCVTOP _ _ _ ∷ []) refl
... | mk-split m okC okO with vconst-ty okC | singleton-inv okO
... | (p1 , s11 , s12) | mk-single p2 d2 c2 oik s21 s22
  with vcvtop-inv oik refl
... | refl , refl =
  push1 p1 (plain _ _ _ _ _ (vconst _ c)) s11
    (rt-sub-trans (rt-sub-trans s12 s21) s22)
pres-pure ok (vcvtop-zero-14 c1 _ _ _ c _ _ _ _ _ _ _)
  with decomp ok (admininstr-VCONST V128 c1 ∷ []) (admininstr-VCVTOP _ _ _ ∷ []) refl
... | mk-split m okC okO with vconst-ty okC | singleton-inv okO
... | (p1 , s11 , s12) | mk-single p2 d2 c2 oik s21 s22
  with vcvtop-inv oik refl
... | refl , refl =
  push1 p1 (plain _ _ _ _ _ (vconst _ c)) s11
    (rt-sub-trans (rt-sub-trans s12 s21) s22)
pres-pure ok (vcvtop-zero-15 c1 _ _ _ c _ _ _ _ _ _ _)
  with decomp ok (admininstr-VCONST V128 c1 ∷ []) (admininstr-VCVTOP _ _ _ ∷ []) refl
... | mk-split m okC okO with vconst-ty okC | singleton-inv okO
... | (p1 , s11 , s12) | mk-single p2 d2 c2 oik s21 s22
  with vcvtop-inv oik refl
... | refl , refl =
  push1 p1 (plain _ _ _ _ _ (vconst _ c)) s11
    (rt-sub-trans (rt-sub-trans s12 s21) s22)

-- splat (numtype -> V128) and replace-lane (V128 numtype -> V128):
-- shape-typed inputs, discarded via unsnoc; output is fixed V128.
pres-pure ok (Step-pure--vsplat _ c1 _ c _)
  with decomp ok (admininstr-CONST _ c1 ∷ []) (admininstr-VSPLAT _ ∷ []) refl
... | mk-split m okC okO with const-ty okC | singleton-inv okO
... | (p1 , s11 , s12) | mk-single p2 d2 c2 oik s21 s22
  with vsplat-inv oik refl
... | (a , refl , refl)
  with rt-sub-unsnoc (rt-sub-trans s12 s21)
... | p1sub , _ =
  push1 p2 (plain _ _ _ _ _ (vconst _ c)) (rt-sub-trans s11 p1sub) s22
pres-pure ok (Step-pure--vreplace-lane c1 _ c2 _ _ c _)
  with decomp ok (admininstr-VCONST V128 c1 ∷ [])
        (admininstr-CONST _ c2 ∷ admininstr-VREPLACE-LANE _ _ ∷ []) refl
... | mk-split m1 okC1 okR
  with decomp okR (admininstr-CONST _ c2 ∷ []) (admininstr-VREPLACE-LANE _ _ ∷ []) refl
... | mk-split m2 okC2 okO
  with vconst-ty okC1 | const-ty okC2 | singleton-inv okO
... | (p1 , s11 , s12) | (p2 , s21 , s22) | mk-single p3 d3 c3 oik s31 s32
  with vreplace-inv oik refl
... | (a , refl , refl)
  with rt-sub-unsnoc
        (subst (λ l → Resulttype-sub _ (mk-list l))
               (sym (snoc2 p3 valtype-V128 a)) (rt-sub-trans s22 s31))
... | p2sub , _
  with rt-sub-unsnoc (rt-sub-trans s12 (rt-sub-trans s21 p2sub))
... | p1sub , _ =
  push1 p3 (plain _ _ _ _ _ (vconst _ c)) (rt-sub-trans s11 p1sub) s32

-- extract-lane (V128 -> numtype(shunpack sh)): concrete shape makes
-- shunpack reduce, so the emitted CONST's numtype matches the cod.
pres-pure ok (vextract-lane-num-0 c1 _ _ c2 _ _)
  with decomp ok (admininstr-VCONST V128 c1 ∷ []) (admininstr-VEXTRACT-LANE _ _ _ ∷ []) refl
... | mk-split m okC okO with vconst-ty okC | singleton-inv okO
... | (p1 , s11 , s12) | mk-single p2 d2 c2' oik s21 s22
  with vextract-inv oik refl
... | refl , refl
  with rt-sub-unsnoc (rt-sub-trans s12 s21)
... | p1sub , _ =
  push1 p2 (plain _ _ _ _ _ (const _ _ c2)) (rt-sub-trans s11 p1sub) s22
pres-pure ok (vextract-lane-num-1 c1 _ _ c2 _ _)
  with decomp ok (admininstr-VCONST V128 c1 ∷ []) (admininstr-VEXTRACT-LANE _ _ _ ∷ []) refl
... | mk-split m okC okO with vconst-ty okC | singleton-inv okO
... | (p1 , s11 , s12) | mk-single p2 d2 c2' oik s21 s22
  with vextract-inv oik refl
... | refl , refl
  with rt-sub-unsnoc (rt-sub-trans s12 s21)
... | p1sub , _ =
  push1 p2 (plain _ _ _ _ _ (const _ _ c2)) (rt-sub-trans s11 p1sub) s22
pres-pure ok (vextract-lane-num-2 c1 _ _ c2 _ _)
  with decomp ok (admininstr-VCONST V128 c1 ∷ []) (admininstr-VEXTRACT-LANE _ _ _ ∷ []) refl
... | mk-split m okC okO with vconst-ty okC | singleton-inv okO
... | (p1 , s11 , s12) | mk-single p2 d2 c2' oik s21 s22
  with vextract-inv oik refl
... | refl , refl
  with rt-sub-unsnoc (rt-sub-trans s12 s21)
... | p1sub , _ =
  push1 p2 (plain _ _ _ _ _ (const _ _ c2)) (rt-sub-trans s11 p1sub) s22
pres-pure ok (vextract-lane-num-3 c1 _ _ c2 _ _)
  with decomp ok (admininstr-VCONST V128 c1 ∷ []) (admininstr-VEXTRACT-LANE _ _ _ ∷ []) refl
... | mk-split m okC okO with vconst-ty okC | singleton-inv okO
... | (p1 , s11 , s12) | mk-single p2 d2 c2' oik s21 s22
  with vextract-inv oik refl
... | refl , refl
  with rt-sub-unsnoc (rt-sub-trans s12 s21)
... | p1sub , _ =
  push1 p2 (plain _ _ _ _ _ (const _ _ c2)) (rt-sub-trans s11 p1sub) s22
pres-pure ok (vextract-lane-pack-0 c1 _ _ _ c2 _ _)
  with decomp ok (admininstr-VCONST V128 c1 ∷ []) (admininstr-VEXTRACT-LANE _ _ _ ∷ []) refl
... | mk-split m okC okO with vconst-ty okC | singleton-inv okO
... | (p1 , s11 , s12) | mk-single p2 d2 c2' oik s21 s22
  with vextract-inv oik refl
... | refl , refl
  with rt-sub-unsnoc (rt-sub-trans s12 s21)
... | p1sub , _ =
  push1 p2 (plain _ _ _ _ _ (const _ _ c2)) (rt-sub-trans s11 p1sub) s22
pres-pure ok (vextract-lane-pack-1 c1 _ _ _ c2 _ _)
  with decomp ok (admininstr-VCONST V128 c1 ∷ []) (admininstr-VEXTRACT-LANE _ _ _ ∷ []) refl
... | mk-split m okC okO with vconst-ty okC | singleton-inv okO
... | (p1 , s11 , s12) | mk-single p2 d2 c2' oik s21 s22
  with vextract-inv oik refl
... | refl , refl
  with rt-sub-unsnoc (rt-sub-trans s12 s21)
... | p1sub , _ =
  push1 p2 (plain _ _ _ _ _ (const _ _ c2)) (rt-sub-trans s11 p1sub) s22


------------------------------------------------------------------------
-- 9b. Preservation over Step-read for local.get / global.get -- the
--     latter exercises the full store-typing chain
--     Frame-ok -> Moduleinst-ok -> Externaddr-ok -> Store-ok ->
--     Globalinst-ok -> Val-ok.
------------------------------------------------------------------------

-- Remaining Step-read rules: table/memory reads, call, call-indirect,
-- ref-func.  Block, loop, AND call-addr are PROVED below.  call-addr's
-- RETURN gap is closed: the regenerated frame rule types the body under
-- {RETURN [t_2*]} ++ C', matching Func-ok, so the callee body re-types
-- verbatim inside the frame (the two contexts are now definitionally
-- equal once the module-instance context is exposed).
-- ===== inversions for the bulk-op reads =====
iok-msize : ∀ {C d c} → Instr-ok C MEMORY-SIZE (mk-functype (mk-list d) (mk-list c)) →
  (d ≡ []) × (c ≡ valtype-I32 ∷ [])
iok-msize (memory-size _ _ _ _) = refl , refl
msize-inv : ∀ {s C e d c} → Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) →
  e ≡ admininstr-MEMORY-SIZE → (d ≡ []) × (c ≡ valtype-I32 ∷ [])
msize-inv (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-msize iok
msize-inv (label _ _ _ _ _ _ _ _ _ _) ()
msize-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
msize-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
msize-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
msize-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
msize-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
msize-inv (Instr-ok2--trap _ _ _ _) ()

iok-tsize : ∀ {C x d c} → Instr-ok C (TABLE-SIZE x) (mk-functype (mk-list d) (mk-list c)) →
  (d ≡ []) × (c ≡ valtype-I32 ∷ [])
iok-tsize (table-size _ _ _ _ _ _) = refl , refl
tsize-inv : ∀ {s C e d c x} → Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) →
  e ≡ admininstr-TABLE-SIZE x → (d ≡ []) × (c ≡ valtype-I32 ∷ [])
tsize-inv (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-tsize iok
tsize-inv (label _ _ _ _ _ _ _ _ _ _) ()
tsize-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
tsize-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
tsize-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
tsize-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
tsize-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
tsize-inv (Instr-ok2--trap _ _ _ _) ()

iok-loadnum : ∀ {C nt ao d c} → Instr-ok C (LOAD nt nothing ao) (mk-functype (mk-list d) (mk-list c)) →
  (d ≡ valtype-I32 ∷ []) × (c ≡ valtype-numtype nt ∷ [])
iok-loadnum (load-val _ _ _ _ _ _ _ _) = refl , refl
loadnum-inv : ∀ {s C e d c nt ao} → Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) →
  e ≡ admininstr-LOAD nt nothing ao → (d ≡ valtype-I32 ∷ []) × (c ≡ valtype-numtype nt ∷ [])
loadnum-inv (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-loadnum iok
loadnum-inv (label _ _ _ _ _ _ _ _ _ _) ()
loadnum-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
loadnum-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
loadnum-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
loadnum-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
loadnum-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
loadnum-inv (Instr-ok2--trap _ _ _ _) ()

iok-loadpack : ∀ {C nt lo ao d c} → Instr-ok C (LOAD nt (just lo) ao) (mk-functype (mk-list d) (mk-list c)) →
  (d ≡ valtype-I32 ∷ []) × (c ≡ valtype-numtype nt ∷ [])
iok-loadpack (load-pack-0 _ _ _ _ _ _ _ _) = refl , refl
iok-loadpack (load-pack-1 _ _ _ _ _ _ _ _) = refl , refl
loadpack-inv : ∀ {s C e d c nt lo ao} → Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) →
  e ≡ admininstr-LOAD nt (just lo) ao → (d ≡ valtype-I32 ∷ []) × (c ≡ valtype-numtype nt ∷ [])
loadpack-inv (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-loadpack iok
loadpack-inv (label _ _ _ _ _ _ _ _ _ _) ()
loadpack-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
loadpack-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
loadpack-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
loadpack-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
loadpack-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
loadpack-inv (Instr-ok2--trap _ _ _ _) ()

iok-loadpack-full : ∀ {C nt lo ao d c} → Instr-ok C (LOAD nt (just lo) ao) (mk-functype (mk-list d) (mk-list c)) →
  Σ Inn λ In → (nt ≡ numtype-Inn In) × (d ≡ valtype-I32 ∷ [])
iok-loadpack-full (load-pack-0 _ _ _ _ _ _ _ _) = Inn-I32 , refl , refl
iok-loadpack-full (load-pack-1 _ _ _ _ _ _ _ _) = Inn-I64 , refl , refl
loadpack-full : ∀ {s C e nt lo ao d c} → Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) → e ≡ admininstr-LOAD nt (just lo) ao →
  Σ Inn λ In → (nt ≡ numtype-Inn In) × (d ≡ valtype-I32 ∷ [])
loadpack-full (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-loadpack-full iok
loadpack-full (label _ _ _ _ _ _ _ _ _ _) ()
loadpack-full (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
loadpack-full (Instr-ok2--call-addr _ _ _ _ _ _) ()
loadpack-full (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
loadpack-full (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
loadpack-full (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
loadpack-full (Instr-ok2--trap _ _ _ _) ()

-- Vector loads.  NOTE: `VLOAD V128 nothing` (plain v128.load) has NO
-- Instr-ok rule in the generated typing (only just-SHAPEX/SPLAT/ZERO),
-- so it is UNTYPEABLE and its reduction case is vacuously preserved
-- (refuted via vloadN-absurd).  [Flagged: a plausibly-missing typing
-- rule in the spec, but sound to refute for preservation.]
vloadN-absurd : ∀ {C ft ao} → Instr-ok C (VLOAD V128 nothing ao) ft → ⊥
vloadN-absurd ()
vloadN-inv : ∀ {s C e ft ao} → Instr-ok2 s C e ft → e ≡ admininstr-VLOAD V128 nothing ao → ⊥
vloadN-inv (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = vloadN-absurd iok
vloadN-inv (label _ _ _ _ _ _ _ _ _ _) ()
vloadN-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
vloadN-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
vloadN-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
vloadN-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
vloadN-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
vloadN-inv (Instr-ok2--trap _ _ _ _) ()

iok-vloadS : ∀ {C M N sx ao d c} →
  Instr-ok C (VLOAD V128 (just (SHAPEX- M N sx)) ao) (mk-functype (mk-list d) (mk-list c)) →
  (d ≡ valtype-I32 ∷ []) × (c ≡ valtype-V128 ∷ [])
iok-vloadS (vload _ _ _ _ _ _ _ _ _) = refl , refl
vloadS-inv : ∀ {s C e d c M N sx ao} → Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) →
  e ≡ admininstr-VLOAD V128 (just (SHAPEX- M N sx)) ao → (d ≡ valtype-I32 ∷ []) × (c ≡ valtype-V128 ∷ [])
vloadS-inv (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-vloadS iok
vloadS-inv (label _ _ _ _ _ _ _ _ _ _) ()
vloadS-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
vloadS-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
vloadS-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
vloadS-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
vloadS-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
vloadS-inv (Instr-ok2--trap _ _ _ _) ()

iok-vloadSP : ∀ {C n ao d c} →
  Instr-ok C (VLOAD V128 (just (SPLAT n)) ao) (mk-functype (mk-list d) (mk-list c)) →
  (d ≡ valtype-I32 ∷ []) × (c ≡ valtype-V128 ∷ [])
iok-vloadSP (vload-splat _ _ _ _ _ _ _) = refl , refl
vloadSP-inv : ∀ {s C e d c n ao} → Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) →
  e ≡ admininstr-VLOAD V128 (just (SPLAT n)) ao → (d ≡ valtype-I32 ∷ []) × (c ≡ valtype-V128 ∷ [])
vloadSP-inv (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-vloadSP iok
vloadSP-inv (label _ _ _ _ _ _ _ _ _ _) ()
vloadSP-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
vloadSP-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
vloadSP-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
vloadSP-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
vloadSP-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
vloadSP-inv (Instr-ok2--trap _ _ _ _) ()

iok-vloadZ : ∀ {C n ao d c} →
  Instr-ok C (VLOAD V128 (just (vloadop-ZERO n)) ao) (mk-functype (mk-list d) (mk-list c)) →
  (d ≡ valtype-I32 ∷ []) × (c ≡ valtype-V128 ∷ [])
iok-vloadZ (vload-zero _ _ _ _ _ _ _) = refl , refl
vloadZ-inv : ∀ {s C e d c n ao} → Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) →
  e ≡ admininstr-VLOAD V128 (just (vloadop-ZERO n)) ao → (d ≡ valtype-I32 ∷ []) × (c ≡ valtype-V128 ∷ [])
vloadZ-inv (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-vloadZ iok
vloadZ-inv (label _ _ _ _ _ _ _ _ _ _) ()
vloadZ-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
vloadZ-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
vloadZ-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
vloadZ-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
vloadZ-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
vloadZ-inv (Instr-ok2--trap _ _ _ _) ()

iok-vloadL : ∀ {C n ao j d c} →
  Instr-ok C (VLOAD-LANE V128 (mk-sz n) ao j) (mk-functype (mk-list d) (mk-list c)) →
  (d ≡ valtype-I32 ∷ valtype-V128 ∷ []) × (c ≡ valtype-V128 ∷ [])
iok-vloadL (vload-lane _ _ _ _ _ _ _ _ _) = refl , refl
vloadL-inv : ∀ {s C e d c n ao j} → Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) →
  e ≡ admininstr-VLOAD-LANE V128 (mk-sz n) ao j →
  (d ≡ valtype-I32 ∷ valtype-V128 ∷ []) × (c ≡ valtype-V128 ∷ [])
vloadL-inv (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-vloadL iok
vloadL-inv (label _ _ _ _ _ _ _ _ _ _) ()
vloadL-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
vloadL-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
vloadL-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
vloadL-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
vloadL-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
vloadL-inv (Instr-ok2--trap _ _ _ _) ()

-- Extract the memory context facts (0<|MEMS|, MEMS[0]=mt) from a typed MEMORY-FILL.
mfill-facts-iok : ∀ {C d c} → Instr-ok C MEMORY-FILL (mk-functype (mk-list d) (mk-list c)) →
  Σ memtype λ mt → (0 < length (context-MEMS C)) × ((context-MEMS C [ 0 ]!) ≡ mt)
mfill-facts-iok (memory-fill _ mt m< mlk) = mt , m< , mlk
mfill-facts : ∀ {s C e d c} → Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) → e ≡ admininstr-MEMORY-FILL →
  Σ memtype λ mt → (0 < length (context-MEMS C)) × ((context-MEMS C [ 0 ]!) ≡ mt)
mfill-facts (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = mfill-facts-iok iok
mfill-facts (label _ _ _ _ _ _ _ _ _ _) ()
mfill-facts (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
mfill-facts (Instr-ok2--call-addr _ _ _ _ _ _) ()
mfill-facts (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
mfill-facts (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
mfill-facts (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
mfill-facts (Instr-ok2--trap _ _ _ _) ()
msize-facts-iok : ∀ {C d c} → Instr-ok C MEMORY-SIZE (mk-functype (mk-list d) (mk-list c)) →
  Σ memtype λ mt → (0 < length (context-MEMS C)) × ((context-MEMS C [ 0 ]!) ≡ mt)
msize-facts-iok (memory-size _ mt m< mlk) = mt , m< , mlk
msize-facts : ∀ {s C e d c} → Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) → e ≡ admininstr-MEMORY-SIZE →
  Σ memtype λ mt → (0 < length (context-MEMS C)) × ((context-MEMS C [ 0 ]!) ≡ mt)
msize-facts (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = msize-facts-iok iok
msize-facts (label _ _ _ _ _ _ _ _ _ _) ()
msize-facts (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
msize-facts (Instr-ok2--call-addr _ _ _ _ _ _) ()
msize-facts (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
msize-facts (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
msize-facts (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
msize-facts (Instr-ok2--trap _ _ _ _) ()

-- The frame's 0th memory address is in-store-bounds (mem-link: FrameFacts.mems-ok + typing 0<|MEMS C|).
msize-bound : ∀ {s f C} (ff : FrameFacts s f C) → 0 < length (context-MEMS C) →
  (MEMS (frame-MODULE f) [ 0 ]!) < length (store-MEMS s)
msize-bound ff m< = xa-mem-inv (pw-lookup (FrameFacts.mems-ok ff) {i = 0}
  (subst (0 <_) (sym (FrameFacts.maddrs-len ff)) (subst (0 <_) (cong length (FrameFacts.mems-eq ff)) m<)))

_≟vt_ : (a b : valtype) → Dec (a ≡ b)
valtype-I32 ≟vt valtype-I32 = yes refl
valtype-I32 ≟vt valtype-I64 = no (λ ())
valtype-I32 ≟vt valtype-F32 = no (λ ())
valtype-I32 ≟vt valtype-F64 = no (λ ())
valtype-I32 ≟vt valtype-V128 = no (λ ())
valtype-I32 ≟vt valtype-FUNCREF = no (λ ())
valtype-I32 ≟vt valtype-EXTERNREF = no (λ ())
valtype-I32 ≟vt BOT = no (λ ())
valtype-I64 ≟vt valtype-I32 = no (λ ())
valtype-I64 ≟vt valtype-I64 = yes refl
valtype-I64 ≟vt valtype-F32 = no (λ ())
valtype-I64 ≟vt valtype-F64 = no (λ ())
valtype-I64 ≟vt valtype-V128 = no (λ ())
valtype-I64 ≟vt valtype-FUNCREF = no (λ ())
valtype-I64 ≟vt valtype-EXTERNREF = no (λ ())
valtype-I64 ≟vt BOT = no (λ ())
valtype-F32 ≟vt valtype-I32 = no (λ ())
valtype-F32 ≟vt valtype-I64 = no (λ ())
valtype-F32 ≟vt valtype-F32 = yes refl
valtype-F32 ≟vt valtype-F64 = no (λ ())
valtype-F32 ≟vt valtype-V128 = no (λ ())
valtype-F32 ≟vt valtype-FUNCREF = no (λ ())
valtype-F32 ≟vt valtype-EXTERNREF = no (λ ())
valtype-F32 ≟vt BOT = no (λ ())
valtype-F64 ≟vt valtype-I32 = no (λ ())
valtype-F64 ≟vt valtype-I64 = no (λ ())
valtype-F64 ≟vt valtype-F32 = no (λ ())
valtype-F64 ≟vt valtype-F64 = yes refl
valtype-F64 ≟vt valtype-V128 = no (λ ())
valtype-F64 ≟vt valtype-FUNCREF = no (λ ())
valtype-F64 ≟vt valtype-EXTERNREF = no (λ ())
valtype-F64 ≟vt BOT = no (λ ())
valtype-V128 ≟vt valtype-I32 = no (λ ())
valtype-V128 ≟vt valtype-I64 = no (λ ())
valtype-V128 ≟vt valtype-F32 = no (λ ())
valtype-V128 ≟vt valtype-F64 = no (λ ())
valtype-V128 ≟vt valtype-V128 = yes refl
valtype-V128 ≟vt valtype-FUNCREF = no (λ ())
valtype-V128 ≟vt valtype-EXTERNREF = no (λ ())
valtype-V128 ≟vt BOT = no (λ ())
valtype-FUNCREF ≟vt valtype-I32 = no (λ ())
valtype-FUNCREF ≟vt valtype-I64 = no (λ ())
valtype-FUNCREF ≟vt valtype-F32 = no (λ ())
valtype-FUNCREF ≟vt valtype-F64 = no (λ ())
valtype-FUNCREF ≟vt valtype-V128 = no (λ ())
valtype-FUNCREF ≟vt valtype-FUNCREF = yes refl
valtype-FUNCREF ≟vt valtype-EXTERNREF = no (λ ())
valtype-FUNCREF ≟vt BOT = no (λ ())
valtype-EXTERNREF ≟vt valtype-I32 = no (λ ())
valtype-EXTERNREF ≟vt valtype-I64 = no (λ ())
valtype-EXTERNREF ≟vt valtype-F32 = no (λ ())
valtype-EXTERNREF ≟vt valtype-F64 = no (λ ())
valtype-EXTERNREF ≟vt valtype-V128 = no (λ ())
valtype-EXTERNREF ≟vt valtype-FUNCREF = no (λ ())
valtype-EXTERNREF ≟vt valtype-EXTERNREF = yes refl
valtype-EXTERNREF ≟vt BOT = no (λ ())
BOT ≟vt valtype-I32 = no (λ ())
BOT ≟vt valtype-I64 = no (λ ())
BOT ≟vt valtype-F32 = no (λ ())
BOT ≟vt valtype-F64 = no (λ ())
BOT ≟vt valtype-V128 = no (λ ())
BOT ≟vt valtype-FUNCREF = no (λ ())
BOT ≟vt valtype-EXTERNREF = no (λ ())
BOT ≟vt BOT = yes refl


_≟ft_ : (a b : functype) → Dec (a ≡ b)
mk-functype (mk-list d1) (mk-list c1) ≟ft mk-functype (mk-list d2) (mk-list c2)
  with ≡-dec _≟vt_ d1 d2 | ≡-dec _≟vt_ c1 c2
... | yes refl | yes refl = yes refl
... | no ¬d | _ = no λ { refl → ¬d refl }
... | _ | no ¬c = no λ { refl → ¬c refl }

-- ===== call_indirect helpers =====
iok-cind : ∀ {C x y d c} → Instr-ok C (CALL-INDIRECT x y) (mk-functype (mk-list d) (mk-list c)) →
  Σ (List valtype) λ t1 → d ≡ t1 ++ valtype-I32 ∷ []
iok-cind (call-indirect _ _ _ t1 _ _ _ _ _ _) = t1 , refl
cind-inv : ∀ {s C e d c x y} → Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) → e ≡ admininstr-CALL-INDIRECT x y →
  Σ (List valtype) λ t1 → d ≡ t1 ++ valtype-I32 ∷ []
cind-inv (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-cind iok
cind-inv (label _ _ _ _ _ _ _ _ _ _) ()
cind-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
cind-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
cind-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
cind-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
cind-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
cind-inv (Instr-ok2--trap _ _ _ _) ()

funcaddr-inj : ∀ {a b} → REF-FUNC-ADDR a ≡ REF-FUNC-ADDR b → a ≡ b
funcaddr-inj refl = refl
nullref≢funcaddr : ∀ {rt a} → ref-REF-NULL rt ≡ REF-FUNC-ADDR a → ⊥
nullref≢funcaddr ()
hostref≢funcaddr : ∀ {h a} → REF-HOST-ADDR h ≡ REF-FUNC-ADDR a → ⊥
hostref≢funcaddr ()

cfg-st : config → state
cfg-st (mk-config z _) = z
cfg-adm0 : config → admininstr
cfg-adm0 (mk-config _ es) = es [ 0 ]!
cfg-adm1 : config → admininstr
cfg-adm1 (mk-config _ es) = es [ 1 ]!
adm-i32 : admininstr → uN-fam0 32
adm-i32 (admininstr-CONST I32 v) = v
adm-i32 _ = mk-uN 0
adm-cix : admininstr → idx
adm-cix (admininstr-CALL-INDIRECT x y) = x
adm-cix _ = mk-uN 0
adm-ciy : admininstr → idx
adm-ciy (admininstr-CALL-INDIRECT x y) = y
adm-ciy _ = mk-uN 0

before-cit : ∀ {cfg} → Step-read-before-call-indirect-trap cfg →
  Σ (uN-fam0 32) λ i → Σ idx λ x → Σ idx λ y → Σ addr λ a →
    (cfg ≡ mk-config (cfg-st cfg) (as (List admininstr) (admininstr-CONST I32 i ∷ admininstr-CALL-INDIRECT x y ∷ []))) ×
    (proj-uN-0 32 i < length (REFS (fun-table (cfg-st cfg) x))) ×
    ((REFS (fun-table (cfg-st cfg) x)) [ proj-uN-0 32 i ]! ≡ REF-FUNC-ADDR a) ×
    (a < length (fun-funcinst (cfg-st cfg))) ×
    (fun-type (cfg-st cfg) y ≡ funcinst-TYPE ((fun-funcinst (cfg-st cfg)) [ a ]!))
before-cit (call-indirect-call-0 z i x y a c1 c2 c3 c4) = i , x , y , a , refl , c1 , c2 , c3 , c4

-- align a before-derivation to a concrete (s,f,c,x,y) config, yielding the 4 conditions with the head's i/x/y.
cit-align : ∀ {s f c x y}
  (b : Step-read-before-call-indirect-trap
         (mk-config (mk-state s f) (as (List admininstr) (admininstr-CONST I32 c ∷ admininstr-CALL-INDIRECT x y ∷ [])))) →
  Σ addr λ a →
    (proj-uN-0 32 c < length (REFS (fun-table (mk-state s f) x))) ×
    ((REFS (fun-table (mk-state s f) x)) [ proj-uN-0 32 c ]! ≡ REF-FUNC-ADDR a) ×
    (a < length (fun-funcinst (mk-state s f))) ×
    (fun-type (mk-state s f) y ≡ funcinst-TYPE ((fun-funcinst (mk-state s f)) [ a ]!))
cit-align {s} {f} {c} {x} {y} b with before-cit b
... | i' , x' , y' , a , cfgeq , c1 , c2 , c3 , c4 =
  let iaeq = cong adm-i32 (cong cfg-adm0 cfgeq)
      xeq  = cong adm-cix (cong cfg-adm1 cfgeq)
      yeq  = cong adm-ciy (cong cfg-adm1 cfgeq)
      c1a  = subst (λ xx → proj-uN-0 32 c < length (REFS (fun-table (mk-state s f) xx))) (sym xeq)
               (subst (λ ii → proj-uN-0 32 ii < length (REFS (fun-table (mk-state s f) x'))) (sym iaeq) c1)
      c2a  = subst (λ xx → (REFS (fun-table (mk-state s f) xx)) [ proj-uN-0 32 c ]! ≡ REF-FUNC-ADDR a) (sym xeq)
               (subst (λ ii → (REFS (fun-table (mk-state s f) x')) [ proj-uN-0 32 ii ]! ≡ REF-FUNC-ADDR a) (sym iaeq) c2)
      c4a  = subst (λ yy → fun-type (mk-state s f) yy ≡ funcinst-TYPE ((fun-funcinst (mk-state s f)) [ a ]!)) (sym yeq) c4
  in a , c1a , c2a , c3 , c4a

-- BACKEND-LIMITATION (dropped width-refinement) axiom, G4 class.
-- `sz = mk-sz ℕ {- 1 premise(s) dropped -}` (wasm2-sound-check.agda:1082): the lane-store/-load width
-- refinement (n ∈ {8,16,32,64} = jsize of a Jnn) was dropped, so the generic sz is typeable-but-stuck
-- for the width-specific reduction rules.  TRUE of the real language; deletable once sz is a width enum.
data VStoreLaneW : ℕ → Set where
  vslw-i32 : VStoreLaneW (jsize Jnn-I32)
  vslw-i64 : VStoreLaneW (jsize Jnn-I64)
  vslw-i8  : VStoreLaneW (jsize Jnn-I8)
  vslw-i16 : VStoreLaneW (jsize Jnn-I16)

postulate
  vstore-lane-width : ∀ {s C e v-n ao j d cc} →
    Instr-ok2 s C e (mk-functype (mk-list d) (mk-list cc)) → e ≡ admininstr-VSTORE-LANE V128 (mk-sz v-n) ao j →
    VStoreLaneW v-n

iok-vstlane : ∀ {C v-n ao j d cc} → Instr-ok C (VSTORE-LANE V128 (mk-sz v-n) ao j) (mk-functype (mk-list d) (mk-list cc)) →
  (d ≡ valtype-I32 ∷ valtype-V128 ∷ []) × (cc ≡ [])
iok-vstlane (vstore-lane _ _ _ _ _ _ _ _ jb) = refl , refl
vstlane-inv : ∀ {s C e v-n ao j d cc} → Instr-ok2 s C e (mk-functype (mk-list d) (mk-list cc)) → e ≡ admininstr-VSTORE-LANE V128 (mk-sz v-n) ao j →
  (d ≡ valtype-I32 ∷ valtype-V128 ∷ []) × (cc ≡ [])
vstlane-inv (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-vstlane iok
vstlane-inv (label _ _ _ _ _ _ _ _ _ _) ()
vstlane-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
vstlane-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
vstlane-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
vstlane-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
vstlane-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
vstlane-inv (Instr-ok2--trap _ _ _ _) ()

-- lane bound extracted separately, called AFTER the width is concrete (avoids width-metavar corruption).
iok-vstlane-jb : ∀ {C v-n ao j d cc} → Instr-ok C (VSTORE-LANE V128 (mk-sz v-n) ao j) (mk-functype (mk-list d) (mk-list cc)) →
  proj-uN-0 8 j < (128 / v-n)
iok-vstlane-jb (vstore-lane _ _ _ _ _ _ _ _ jb) = jb
vstlane-jb : ∀ {s C e v-n ao j d cc} → Instr-ok2 s C e (mk-functype (mk-list d) (mk-list cc)) → e ≡ admininstr-VSTORE-LANE V128 (mk-sz v-n) ao j →
  proj-uN-0 8 j < (128 / v-n)
vstlane-jb (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-vstlane-jb iok
vstlane-jb (label _ _ _ _ _ _ _ _ _ _) ()
vstlane-jb (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
vstlane-jb (Instr-ok2--call-addr _ _ _ _ _ _) ()
vstlane-jb (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
vstlane-jb (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
vstlane-jb (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
vstlane-jb (Instr-ok2--trap _ _ _ _) ()

postulate
  vload-lane-width : ∀ {s C e v-n ao j d cc} →
    Instr-ok2 s C e (mk-functype (mk-list d) (mk-list cc)) → e ≡ admininstr-VLOAD-LANE V128 (mk-sz v-n) ao j →
    VStoreLaneW v-n

iok-vloadlane : ∀ {C v-n ao j d cc} → Instr-ok C (VLOAD-LANE V128 (mk-sz v-n) ao j) (mk-functype (mk-list d) (mk-list cc)) →
  (d ≡ valtype-I32 ∷ valtype-V128 ∷ []) × (cc ≡ valtype-V128 ∷ [])
iok-vloadlane (vload-lane _ _ _ _ _ _ _ _ _) = refl , refl
vloadlane-inv : ∀ {s C e v-n ao j d cc} → Instr-ok2 s C e (mk-functype (mk-list d) (mk-list cc)) → e ≡ admininstr-VLOAD-LANE V128 (mk-sz v-n) ao j →
  (d ≡ valtype-I32 ∷ valtype-V128 ∷ []) × (cc ≡ valtype-V128 ∷ [])
vloadlane-inv (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-vloadlane iok
vloadlane-inv (label _ _ _ _ _ _ _ _ _ _) ()
vloadlane-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
vloadlane-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
vloadlane-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
vloadlane-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
vloadlane-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
vloadlane-inv (Instr-ok2--trap _ _ _ _) ()



postulate
  vload-splat-width : ∀ {s C e v-n ao d cc} →
    Instr-ok2 s C e (mk-functype (mk-list d) (mk-list cc)) → e ≡ admininstr-VLOAD V128 (just (SPLAT v-n)) ao →
    VStoreLaneW v-n

iok-vload-splat : ∀ {C v-n ao d cc} → Instr-ok C (VLOAD V128 (just (SPLAT v-n)) ao) (mk-functype (mk-list d) (mk-list cc)) →
  (d ≡ valtype-I32 ∷ []) × (cc ≡ valtype-V128 ∷ [])
iok-vload-splat (vload-splat _ _ _ _ _ _ _) = refl , refl
vsplat-inv2 : ∀ {s C e v-n ao d cc} → Instr-ok2 s C e (mk-functype (mk-list d) (mk-list cc)) → e ≡ admininstr-VLOAD V128 (just (SPLAT v-n)) ao →
  (d ≡ valtype-I32 ∷ []) × (cc ≡ valtype-V128 ∷ [])
vsplat-inv2 (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-vload-splat iok
vsplat-inv2 (label _ _ _ _ _ _ _ _ _ _) ()
vsplat-inv2 (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
vsplat-inv2 (Instr-ok2--call-addr _ _ _ _ _ _) ()
vsplat-inv2 (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
vsplat-inv2 (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
vsplat-inv2 (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
vsplat-inv2 (Instr-ok2--trap _ _ _ _) ()

iok-vload-zero : ∀ {C v-n ao d cc} → Instr-ok C (VLOAD V128 (just (vloadop-ZERO v-n)) ao) (mk-functype (mk-list d) (mk-list cc)) →
  (d ≡ valtype-I32 ∷ []) × (cc ≡ valtype-V128 ∷ [])
iok-vload-zero (vload-zero _ _ _ _ _ _ _) = refl , refl
vzero-inv : ∀ {s C e v-n ao d cc} → Instr-ok2 s C e (mk-functype (mk-list d) (mk-list cc)) → e ≡ admininstr-VLOAD V128 (just (vloadop-ZERO v-n)) ao →
  (d ≡ valtype-I32 ∷ []) × (cc ≡ valtype-V128 ∷ [])
vzero-inv (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-vload-zero iok
vzero-inv (label _ _ _ _ _ _ _ _ _ _) ()
vzero-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
vzero-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
vzero-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
vzero-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
vzero-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
vzero-inv (Instr-ok2--trap _ _ _ _) ()

-- General Foralli constructor: build a length-N list whose k-th element satisfies P k, from a
-- per-index Σ-producer.  Foralli P xs = Pointwise P (upTo (length xs)) xs.
map-applyUpTo : ∀ {A B : Set} (g : ℕ → A) (h : A → B) (n : ℕ) → map h (applyUpTo g n) ≡ applyUpTo (λ k → h (g k)) n
map-applyUpTo g h zero = refl
map-applyUpTo g h (suc n) = cong (h (g 0) ∷_) (map-applyUpTo (λ k → g (suc k)) h n)

pw-shift : ∀ {A : Set} {P : ℕ → A → Set} {ks : List ℕ} {xs : List A} →
  Pointwise (λ k x → P (suc k) x) ks xs → Pointwise P (map suc ks) xs
pw-shift [] = []
pw-shift (p ∷ ps) = p ∷ pw-shift ps

foralli-build : ∀ {A : Set} {P : ℕ → A → Set} (N : ℕ) → (∀ k → k < N → Σ A λ a → P k a) →
  Σ (List A) λ xs → (length xs ≡ N) × Pointwise P (upTo N) xs
-- floor superadditivity a/8 + b/8 ≤ (a+b)/8, and the per-chunk memory bound for vload-shape.
/-superadd : ∀ (a b : ℕ) → (a / 8) + (b / 8) ≤ (a + b) / 8
/-superadd a b =
  subst (_≤ (a + b) / 8) (m*n/n≡m ((a / 8) + (b / 8)) 8)
    (/-monoˡ-≤ 8 (subst (_≤ a + b) (sym (*-distribʳ-+ 8 (a / 8) (b / 8)))
      (+-mono-≤ (m/n*n≤m a 8) (m/n*n≤m b 8))))

chunk-bound : ∀ (M N k : ℕ) → k < N → (k * M) / 8 + M / 8 ≤ (M * N) / 8
chunk-bound M N k k<N =
  ≤-trans (/-superadd (k * M) M)
    (/-monoˡ-≤ 8 (≤-trans (≤-reflexive (+-comm (k * M) M))
      (≤-trans (*-mono-≤ k<N (≤-refl {x = M})) (≤-reflexive (*-comm N M)))))

foralli-build zero fn = [] , refl , []
foralli-build {P = P} (suc n) fn with fn 0 (s≤s z≤n)
... | a0 , p0 with foralli-build n (λ k k<n → fn (suc k) (s≤s k<n))
...   | rest , lenr , pwr =
        a0 ∷ rest , cong suc lenr ,
        (p0 ∷ subst (λ l → Pointwise P l rest) (map-applyUpTo (λ k → k) suc n) (pw-shift pwr))





-- Concrete dom for MEMORY-FILL (needed to pin the fill value to i32).
iok-mfill-dom : ∀ {C d c} → Instr-ok C MEMORY-FILL (mk-functype (mk-list d) (mk-list c)) →
  (d ≡ valtype-I32 ∷ valtype-I32 ∷ valtype-I32 ∷ []) × (c ≡ [])
iok-mfill-dom (memory-fill _ _ _ _) = refl , refl
mfill-dom : ∀ {s C e d c} → Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) → e ≡ admininstr-MEMORY-FILL →
  (d ≡ valtype-I32 ∷ valtype-I32 ∷ valtype-I32 ∷ []) × (c ≡ [])
mfill-dom (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-mfill-dom iok
mfill-dom (label _ _ _ _ _ _ _ _ _ _) ()
mfill-dom (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
mfill-dom (Instr-ok2--call-addr _ _ _ _ _ _) ()
mfill-dom (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
mfill-dom (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
mfill-dom (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
mfill-dom (Instr-ok2--trap _ _ _ _) ()

iok-mcopy-dom : ∀ {C d c} → Instr-ok C MEMORY-COPY (mk-functype (mk-list d) (mk-list c)) →
  (d ≡ valtype-I32 ∷ valtype-I32 ∷ valtype-I32 ∷ []) × (c ≡ [])
iok-mcopy-dom (memory-copy _ _ _ _) = refl , refl
mcopy-dom : ∀ {s C e d c} → Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) → e ≡ admininstr-MEMORY-COPY →
  (d ≡ valtype-I32 ∷ valtype-I32 ∷ valtype-I32 ∷ []) × (c ≡ [])
mcopy-dom (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-mcopy-dom iok
mcopy-dom (label _ _ _ _ _ _ _ _ _ _) ()
mcopy-dom (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
mcopy-dom (Instr-ok2--call-addr _ _ _ _ _ _) ()
mcopy-dom (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
mcopy-dom (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
mcopy-dom (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
mcopy-dom (Instr-ok2--trap _ _ _ _) ()

iok-minit-dom : ∀ {C x d c} → Instr-ok C (MEMORY-INIT x) (mk-functype (mk-list d) (mk-list c)) →
  (d ≡ valtype-I32 ∷ valtype-I32 ∷ valtype-I32 ∷ []) × (c ≡ [])
iok-minit-dom (memory-init _ _ _ _ _ _ _) = refl , refl
minit-dom : ∀ {s C e x d c} → Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) → e ≡ admininstr-MEMORY-INIT x →
  (d ≡ valtype-I32 ∷ valtype-I32 ∷ valtype-I32 ∷ []) × (c ≡ [])
minit-dom (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-minit-dom iok
minit-dom (label _ _ _ _ _ _ _ _ _ _) ()
minit-dom (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
minit-dom (Instr-ok2--call-addr _ _ _ _ _ _) ()
minit-dom (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
minit-dom (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
minit-dom (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
minit-dom (Instr-ok2--trap _ _ _ _) ()

iok-tcopy-dom : ∀ {C x y d c} → Instr-ok C (TABLE-COPY x y) (mk-functype (mk-list d) (mk-list c)) →
  (d ≡ valtype-I32 ∷ valtype-I32 ∷ valtype-I32 ∷ []) × (c ≡ [])
iok-tcopy-dom (table-copy _ _ _ _ _ _ _ _ _ _) = refl , refl
tcopy-dom : ∀ {s C e x y d c} → Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) → e ≡ admininstr-TABLE-COPY x y →
  (d ≡ valtype-I32 ∷ valtype-I32 ∷ valtype-I32 ∷ []) × (c ≡ [])
tcopy-dom (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-tcopy-dom iok
tcopy-dom (label _ _ _ _ _ _ _ _ _ _) ()
tcopy-dom (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
tcopy-dom (Instr-ok2--call-addr _ _ _ _ _ _) ()
tcopy-dom (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
tcopy-dom (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
tcopy-dom (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
tcopy-dom (Instr-ok2--trap _ _ _ _) ()

iok-tfill-dom : ∀ {C x d c} → Instr-ok C (TABLE-FILL x) (mk-functype (mk-list d) (mk-list c)) →
  Σ reftype λ rt → (d ≡ valtype-I32 ∷ valtype-reftype rt ∷ valtype-I32 ∷ []) × (c ≡ [])
iok-tfill-dom (table-fill _ _ rt _ _ _) = rt , refl , refl
tfill-dom : ∀ {s C e x d c} → Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) → e ≡ admininstr-TABLE-FILL x →
  Σ reftype λ rt → (d ≡ valtype-I32 ∷ valtype-reftype rt ∷ valtype-I32 ∷ []) × (c ≡ [])
tfill-dom (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-tfill-dom iok
tfill-dom (label _ _ _ _ _ _ _ _ _ _) ()
tfill-dom (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
tfill-dom (Instr-ok2--call-addr _ _ _ _ _ _) ()
tfill-dom (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
tfill-dom (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
tfill-dom (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
tfill-dom (Instr-ok2--trap _ _ _ _) ()

iok-tinit-dom : ∀ {C x y d c} → Instr-ok C (TABLE-INIT x y) (mk-functype (mk-list d) (mk-list c)) →
  (d ≡ valtype-I32 ∷ valtype-I32 ∷ valtype-I32 ∷ []) × (c ≡ [])
iok-tinit-dom (table-init _ _ _ _ _ _ _ _ _) = refl , refl
tinit-dom : ∀ {s C e x y d c} → Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) → e ≡ admininstr-TABLE-INIT x y →
  (d ≡ valtype-I32 ∷ valtype-I32 ∷ valtype-I32 ∷ []) × (c ≡ [])
tinit-dom (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-tinit-dom iok
tinit-dom (label _ _ _ _ _ _ _ _ _ _) ()
tinit-dom (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
tinit-dom (Instr-ok2--call-addr _ _ _ _ _ _) ()
tinit-dom (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
tinit-dom (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
tinit-dom (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
tinit-dom (Instr-ok2--trap _ _ _ _) ()

-- Memory context facts for MEMORY-COPY and MEMORY-INIT.
mcopy-facts-iok : ∀ {C d c} → Instr-ok C MEMORY-COPY (mk-functype (mk-list d) (mk-list c)) →
  Σ memtype λ mt → (0 < length (context-MEMS C)) × ((context-MEMS C [ 0 ]!) ≡ mt)
mcopy-facts-iok (memory-copy _ mt m< mlk) = mt , m< , mlk
mcopy-facts : ∀ {s C e d c} → Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) → e ≡ admininstr-MEMORY-COPY →
  Σ memtype λ mt → (0 < length (context-MEMS C)) × ((context-MEMS C [ 0 ]!) ≡ mt)
mcopy-facts (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = mcopy-facts-iok iok
mcopy-facts (label _ _ _ _ _ _ _ _ _ _) ()
mcopy-facts (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
mcopy-facts (Instr-ok2--call-addr _ _ _ _ _ _) ()
mcopy-facts (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
mcopy-facts (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
mcopy-facts (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
mcopy-facts (Instr-ok2--trap _ _ _ _) ()

minit-facts-iok : ∀ {C x d c} → Instr-ok C (MEMORY-INIT x) (mk-functype (mk-list d) (mk-list c)) →
  Σ memtype λ mt →
    (0 < length (context-MEMS C)) × ((context-MEMS C [ 0 ]!) ≡ mt) ×
    (proj-uN-0 32 x < length (context-DATAS C)) × ((context-DATAS C [ proj-uN-0 32 x ]!) ≡ OK)
minit-facts-iok (memory-init _ _ mt m< mlk d< dlk) = mt , m< , mlk , d< , dlk
minit-facts : ∀ {s C e x d c} → Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) → e ≡ admininstr-MEMORY-INIT x →
  Σ memtype λ mt →
    (0 < length (context-MEMS C)) × ((context-MEMS C [ 0 ]!) ≡ mt) ×
    (proj-uN-0 32 x < length (context-DATAS C)) × ((context-DATAS C [ proj-uN-0 32 x ]!) ≡ OK)
minit-facts (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = minit-facts-iok iok
minit-facts (label _ _ _ _ _ _ _ _ _ _) ()
minit-facts (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
minit-facts (Instr-ok2--call-addr _ _ _ _ _ _) ()
minit-facts (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
minit-facts (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
minit-facts (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
minit-facts (Instr-ok2--trap _ _ _ _) ()

-- Table facts + concrete dom for TABLE-FILL / TABLE-COPY.
iok-tfill-all : ∀ {C x d c} → Instr-ok C (TABLE-FILL x) (mk-functype (mk-list d) (mk-list c)) →
  Σ reftype λ rt → Σ limits λ lim →
    (proj-uN-0 32 x < length (context-TABLES C)) × ((context-TABLES C [ proj-uN-0 32 x ]!) ≡ mk-tabletype lim rt) ×
    (d ≡ valtype-I32 ∷ valtype-reftype rt ∷ valtype-I32 ∷ []) × (c ≡ [])
iok-tfill-all (table-fill _ _ rt lim x< lk) = rt , lim , x< , lk , refl , refl
tfill-all : ∀ {s C e x d c} → Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) → e ≡ admininstr-TABLE-FILL x →
  Σ reftype λ rt → Σ limits λ lim →
    (proj-uN-0 32 x < length (context-TABLES C)) × ((context-TABLES C [ proj-uN-0 32 x ]!) ≡ mk-tabletype lim rt) ×
    (d ≡ valtype-I32 ∷ valtype-reftype rt ∷ valtype-I32 ∷ []) × (c ≡ [])
tfill-all (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-tfill-all iok
tfill-all (label _ _ _ _ _ _ _ _ _ _) ()
tfill-all (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
tfill-all (Instr-ok2--call-addr _ _ _ _ _ _) ()
tfill-all (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
tfill-all (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
tfill-all (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
tfill-all (Instr-ok2--trap _ _ _ _) ()

iok-tcopy-all : ∀ {C x y d c} → Instr-ok C (TABLE-COPY x y) (mk-functype (mk-list d) (mk-list c)) →
  Σ reftype λ rt → Σ limits λ limx → Σ limits λ limy →
    (proj-uN-0 32 x < length (context-TABLES C)) × ((context-TABLES C [ proj-uN-0 32 x ]!) ≡ mk-tabletype limx rt) ×
    (proj-uN-0 32 y < length (context-TABLES C)) × ((context-TABLES C [ proj-uN-0 32 y ]!) ≡ mk-tabletype limy rt) ×
    (d ≡ valtype-I32 ∷ valtype-I32 ∷ valtype-I32 ∷ []) × (c ≡ [])
iok-tcopy-all (table-copy _ _ _ limx rt limy x< lkx y< lky) = rt , limx , limy , x< , lkx , y< , lky , refl , refl
tcopy-all : ∀ {s C e x y d c} → Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) → e ≡ admininstr-TABLE-COPY x y →
  Σ reftype λ rt → Σ limits λ limx → Σ limits λ limy →
    (proj-uN-0 32 x < length (context-TABLES C)) × ((context-TABLES C [ proj-uN-0 32 x ]!) ≡ mk-tabletype limx rt) ×
    (proj-uN-0 32 y < length (context-TABLES C)) × ((context-TABLES C [ proj-uN-0 32 y ]!) ≡ mk-tabletype limy rt) ×
    (d ≡ valtype-I32 ∷ valtype-I32 ∷ valtype-I32 ∷ []) × (c ≡ [])
tcopy-all (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-tcopy-all iok
tcopy-all (label _ _ _ _ _ _ _ _ _ _) ()
tcopy-all (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
tcopy-all (Instr-ok2--call-addr _ _ _ _ _ _) ()
tcopy-all (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
tcopy-all (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
tcopy-all (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
tcopy-all (Instr-ok2--trap _ _ _ _) ()

iok-tinit-all : ∀ {C x y d c} → Instr-ok C (TABLE-INIT x y) (mk-functype (mk-list d) (mk-list c)) →
  Σ reftype λ rt → Σ limits λ lim →
    (proj-uN-0 32 x < length (context-TABLES C)) × ((context-TABLES C [ proj-uN-0 32 x ]!) ≡ mk-tabletype lim rt) ×
    (proj-uN-0 32 y < length (context-ELEMS C)) × ((context-ELEMS C [ proj-uN-0 32 y ]!) ≡ rt) ×
    (d ≡ valtype-I32 ∷ valtype-I32 ∷ valtype-I32 ∷ []) × (c ≡ [])
iok-tinit-all (table-init _ _ _ lim rt x< lkx y< lky) = rt , lim , x< , lkx , y< , lky , refl , refl
tinit-all : ∀ {s C e x y d c} → Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) → e ≡ admininstr-TABLE-INIT x y →
  Σ reftype λ rt → Σ limits λ lim →
    (proj-uN-0 32 x < length (context-TABLES C)) × ((context-TABLES C [ proj-uN-0 32 x ]!) ≡ mk-tabletype lim rt) ×
    (proj-uN-0 32 y < length (context-ELEMS C)) × ((context-ELEMS C [ proj-uN-0 32 y ]!) ≡ rt) ×
    (d ≡ valtype-I32 ∷ valtype-I32 ∷ valtype-I32 ∷ []) × (c ≡ [])
tinit-all (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-tinit-all iok
tinit-all (label _ _ _ _ _ _ _ _ _ _) ()
tinit-all (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
tinit-all (Instr-ok2--call-addr _ _ _ _ _ _) ()
tinit-all (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
tinit-all (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
tinit-all (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
tinit-all (Instr-ok2--trap _ _ _ _) ()

iok-ci : ∀ {C x y d c} → Instr-ok C (CALL-INDIRECT x y) (mk-functype (mk-list d) (mk-list c)) →
  Σ (List valtype) λ t1 → Σ (List valtype) λ t2 →
    (d ≡ t1 ++ valtype-I32 ∷ []) × (c ≡ t2) ×
    ((context-TYPES C [ proj-uN-0 32 y ]!) ≡ mk-functype (mk-list t1) (mk-list t2))
iok-ci (call-indirect _ _ _ t1 t2 _ _ _ _ lky) = t1 , t2 , refl , refl , lky
ci-inv : ∀ {s C e d c x y} → Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) →
  e ≡ admininstr-CALL-INDIRECT x y →
  Σ (List valtype) λ t1 → Σ (List valtype) λ t2 →
    (d ≡ t1 ++ valtype-I32 ∷ []) × (c ≡ t2) ×
    ((context-TYPES C [ proj-uN-0 32 y ]!) ≡ mk-functype (mk-list t1) (mk-list t2))
ci-inv (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-ci iok
ci-inv (label _ _ _ _ _ _ _ _ _ _) ()
ci-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
ci-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
ci-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
ci-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
ci-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
ci-inv (Instr-ok2--trap _ _ _ _) ()

mfill-iok : ∀ {C d c} → Instr-ok C MEMORY-FILL (mk-functype (mk-list d) (mk-list c)) → (length d ≡ 3) × (c ≡ [])
mfill-iok (memory-fill _ _ _ _) = refl , refl
mfill-inv : ∀ {s C e d c} → Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) → e ≡ admininstr-MEMORY-FILL → (length d ≡ 3) × (c ≡ [])
mfill-inv (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = mfill-iok iok
mfill-inv (label _ _ _ _ _ _ _ _ _ _) ()
mfill-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
mfill-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
mfill-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
mfill-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
mfill-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
mfill-inv (Instr-ok2--trap _ _ _ _) ()
mcopy-iok : ∀ {C d c} → Instr-ok C MEMORY-COPY (mk-functype (mk-list d) (mk-list c)) → (length d ≡ 3) × (c ≡ [])
mcopy-iok (memory-copy _ _ _ _) = refl , refl
mcopy-inv : ∀ {s C e d c} → Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) → e ≡ admininstr-MEMORY-COPY → (length d ≡ 3) × (c ≡ [])
mcopy-inv (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = mcopy-iok iok
mcopy-inv (label _ _ _ _ _ _ _ _ _ _) ()
mcopy-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
mcopy-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
mcopy-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
mcopy-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
mcopy-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
mcopy-inv (Instr-ok2--trap _ _ _ _) ()
minit-iok : ∀ {C x d c} → Instr-ok C (MEMORY-INIT x) (mk-functype (mk-list d) (mk-list c)) → (length d ≡ 3) × (c ≡ [])
minit-iok (memory-init _ _ _ _ _ _ _) = refl , refl
minit-inv : ∀ {s C e x d c} → Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) → e ≡ (admininstr-MEMORY-INIT x) → (length d ≡ 3) × (c ≡ [])
minit-inv (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = minit-iok iok
minit-inv (label _ _ _ _ _ _ _ _ _ _) ()
minit-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
minit-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
minit-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
minit-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
minit-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
minit-inv (Instr-ok2--trap _ _ _ _) ()
tfill-iok : ∀ {C x d c} → Instr-ok C (TABLE-FILL x) (mk-functype (mk-list d) (mk-list c)) → (length d ≡ 3) × (c ≡ [])
tfill-iok (table-fill _ _ _ _ _ _) = refl , refl
tfill-inv : ∀ {s C e x d c} → Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) → e ≡ (admininstr-TABLE-FILL x) → (length d ≡ 3) × (c ≡ [])
tfill-inv (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = tfill-iok iok
tfill-inv (label _ _ _ _ _ _ _ _ _ _) ()
tfill-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
tfill-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
tfill-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
tfill-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
tfill-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
tfill-inv (Instr-ok2--trap _ _ _ _) ()
tcopy-iok : ∀ {C x y d c} → Instr-ok C (TABLE-COPY x y) (mk-functype (mk-list d) (mk-list c)) → (length d ≡ 3) × (c ≡ [])
tcopy-iok (table-copy _ _ _ _ _ _ _ _ _ _) = refl , refl
tcopy-inv : ∀ {s C e x y d c} → Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) → e ≡ (admininstr-TABLE-COPY x y) → (length d ≡ 3) × (c ≡ [])
tcopy-inv (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = tcopy-iok iok
tcopy-inv (label _ _ _ _ _ _ _ _ _ _) ()
tcopy-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
tcopy-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
tcopy-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
tcopy-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
tcopy-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
tcopy-inv (Instr-ok2--trap _ _ _ _) ()
tinit-iok : ∀ {C x y d c} → Instr-ok C (TABLE-INIT x y) (mk-functype (mk-list d) (mk-list c)) → (length d ≡ 3) × (c ≡ [])
tinit-iok (table-init _ _ _ _ _ _ _ _ _) = refl , refl
tinit-inv : ∀ {s C e x y d c} → Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) → e ≡ (admininstr-TABLE-INIT x y) → (length d ≡ 3) × (c ≡ [])
tinit-inv (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = tinit-iok iok
tinit-inv (label _ _ _ _ _ _ _ _ _ _) ()
tinit-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
tinit-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
tinit-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
tinit-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
tinit-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
tinit-inv (Instr-ok2--trap _ _ _ _) ()
three-sub : ∀ {s Ci vs u1 u2 m p d} →
  Instrs-ok2 s Ci (map (λ w → admininstr-val w) vs) (mk-functype (mk-list u1) (mk-list m)) →
  Resulttype-sub (mk-list m) (mk-list (p ++ d)) →
  length d ≡ length vs →
  Resulttype-sub (mk-list (p ++ [])) (mk-list u2) →
  Resulttype-sub (mk-list u1) (mk-list u2)
three-sub {vs = vs} {p = p} okRow os1 leq os2 with row-inv vs okRow
... | ts , pwv , rsub =
  rt-sub-trans (proj₁ (rt-sub-split (rt-sub-trans rsub os1) (tr≡ (pw-length pwv) (sym leq)))) (rt-norml p os2)

three-empty : ∀ {s Ci vs u1 u2 m p d} →
  Instrs-ok2 s Ci (map (λ w → admininstr-val w) vs) (mk-functype (mk-list u1) (mk-list m)) →
  Resulttype-sub (mk-list m) (mk-list (p ++ d)) →
  length d ≡ length vs →
  Resulttype-sub (mk-list (p ++ [])) (mk-list u2) →
  Instrs-ok2 s Ci [] (mk-functype (mk-list u1) (mk-list u2))
three-empty okRow os1 leq os2 = sub-empty (three-sub okRow os1 leq os2)

-- Sequencing combinators for building reduct typings of decomposition rules.
_>>>_ : ∀ {s C es1 es2 a b c} →
  Instrs-ok2 s C es1 (mk-functype (mk-list a) (mk-list b)) →
  Instrs-ok2 s C es2 (mk-functype (mk-list b) (mk-list c)) →
  Instrs-ok2 s C (es1 ++ es2) (mk-functype (mk-list a) (mk-list c))
p >>> q = Instrs-ok2--seq _ _ _ _ _ _ _ p q
infixl 5 _>>>_

lift1 : ∀ {s C e d c} → Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) →
  Instrs-ok2 s C (e ∷ []) (mk-functype (mk-list d) (mk-list c))
lift1 iok = single-intro (mk-single [] _ _ iok (rt-sub-refl _) (rt-sub-refl _))

fr : ∀ {s C es d c} acc → Instrs-ok2 s C es (mk-functype (mk-list d) (mk-list c)) →
  Instrs-ok2 s C es (mk-functype (mk-list (acc ++ d)) (mk-list (acc ++ c)))
fr acc p = Instrs-ok2--frame _ _ _ acc _ _ p

-- Lift a balanced ([] → []) reduct typing to any ambient u1 → u2 (given u1 <: u2).
run-empty : ∀ {s Ci es u1 u2} →
  Instrs-ok2 s Ci es (mk-functype (mk-list []) (mk-list [])) →
  Resulttype-sub (mk-list u1) (mk-list u2) →
  Instrs-ok2 s Ci es (mk-functype (mk-list u1) (mk-list u2))
run-empty {u1 = u1} p su =
  Instrs-ok2--sub _ _ _ _ _ u1 u1
    (subst (λ l → Instrs-ok2 _ _ _ (mk-functype (mk-list l) (mk-list l))) (++-identityʳ u1) (fr u1 p))
    (rt-sub-refl u1) su

-- i32.const singleton at [] → [i32], value irrelevant.
c32 : ∀ {s C cn} → Instrs-ok2 s C (admininstr-CONST I32 cn ∷ []) (mk-functype (mk-list []) (mk-list (valtype-I32 ∷ [])))
c32 = lift1 (plain _ _ _ _ _ (const _ I32 _))

-- Memory sub-op builders from context memory facts (0<|MEMS|, MEMS[0]=mt).
store8-ok : ∀ {s C mt} → (0 < length (context-MEMS C)) → ((context-MEMS C [ 0 ]!) ≡ mt) →
  Instr-ok2 s C (admininstr-STORE I32 (just (mk-sz 8)) memarg0)
    (mk-functype (mk-list (valtype-I32 ∷ valtype-I32 ∷ [])) (mk-list []))
store8-ok {mt = mt} m< mlk = plain _ _ _ _ _ (store-pack _ Inn-I32 8 memarg0 mt m< mlk (s≤s z≤n))

load8-ok : ∀ {s C mt} → (0 < length (context-MEMS C)) → ((context-MEMS C [ 0 ]!) ≡ mt) →
  Instr-ok2 s C (admininstr-LOAD I32 (just (mk-loadop- (mk-sz 8) U)) memarg0)
    (mk-functype (mk-list (valtype-I32 ∷ [])) (mk-list (valtype-I32 ∷ [])))
load8-ok {mt = mt} m< mlk = plain _ _ _ _ _ (load-pack-0 _ 8 U memarg0 mt m< mlk (s≤s z≤n))

mfill-ok : ∀ {s C mt} → (0 < length (context-MEMS C)) → ((context-MEMS C [ 0 ]!) ≡ mt) →
  Instr-ok2 s C admininstr-MEMORY-FILL
    (mk-functype (mk-list (valtype-I32 ∷ valtype-I32 ∷ valtype-I32 ∷ [])) (mk-list []))
mfill-ok {mt = mt} m< mlk = plain _ _ _ _ _ (memory-fill _ mt m< mlk)

mcopy-ok : ∀ {s C mt} → (0 < length (context-MEMS C)) → ((context-MEMS C [ 0 ]!) ≡ mt) →
  Instr-ok2 s C admininstr-MEMORY-COPY
    (mk-functype (mk-list (valtype-I32 ∷ valtype-I32 ∷ valtype-I32 ∷ [])) (mk-list []))
mcopy-ok {mt = mt} m< mlk = plain _ _ _ _ _ (memory-copy _ mt m< mlk)

minit-ok : ∀ {s C x mt} → (0 < length (context-MEMS C)) → ((context-MEMS C [ 0 ]!) ≡ mt) →
  (proj-uN-0 32 x < length (context-DATAS C)) → ((context-DATAS C [ proj-uN-0 32 x ]!) ≡ OK) →
  Instr-ok2 s C (admininstr-MEMORY-INIT x)
    (mk-functype (mk-list (valtype-I32 ∷ valtype-I32 ∷ valtype-I32 ∷ [])) (mk-list []))
minit-ok {x = x} {mt = mt} m< mlk d< dlk = plain _ _ _ _ _ (memory-init _ x mt m< mlk d< dlk)

-- Table sub-op builders from context table facts (x<|TABLES|, TABLES[x]=mk-tabletype lim rt).
tget-ok : ∀ {s C x rt lim} → (proj-uN-0 32 x < length (context-TABLES C)) →
  ((context-TABLES C [ proj-uN-0 32 x ]!) ≡ mk-tabletype lim rt) →
  Instr-ok2 s C (admininstr-TABLE-GET x)
    (mk-functype (mk-list (valtype-I32 ∷ [])) (mk-list (valtype-reftype rt ∷ [])))
tget-ok {x = x} {rt = rt} {lim = lim} x< lk = plain _ _ _ _ _ (table-get _ x rt lim x< lk)

tset-ok : ∀ {s C x rt lim} → (proj-uN-0 32 x < length (context-TABLES C)) →
  ((context-TABLES C [ proj-uN-0 32 x ]!) ≡ mk-tabletype lim rt) →
  Instr-ok2 s C (admininstr-TABLE-SET x)
    (mk-functype (mk-list (valtype-I32 ∷ valtype-reftype rt ∷ [])) (mk-list []))
tset-ok {x = x} {rt = rt} {lim = lim} x< lk = plain _ _ _ _ _ (table-set _ x rt lim x< lk)

tfill-ok : ∀ {s C x rt lim} → (proj-uN-0 32 x < length (context-TABLES C)) →
  ((context-TABLES C [ proj-uN-0 32 x ]!) ≡ mk-tabletype lim rt) →
  Instr-ok2 s C (admininstr-TABLE-FILL x)
    (mk-functype (mk-list (valtype-I32 ∷ valtype-reftype rt ∷ valtype-I32 ∷ [])) (mk-list []))
tfill-ok {x = x} {rt = rt} {lim = lim} x< lk = plain _ _ _ _ _ (table-fill _ x rt lim x< lk)

tcopy-ok : ∀ {s C x y rt limx limy} →
  (proj-uN-0 32 x < length (context-TABLES C)) → ((context-TABLES C [ proj-uN-0 32 x ]!) ≡ mk-tabletype limx rt) →
  (proj-uN-0 32 y < length (context-TABLES C)) → ((context-TABLES C [ proj-uN-0 32 y ]!) ≡ mk-tabletype limy rt) →
  Instr-ok2 s C (admininstr-TABLE-COPY x y)
    (mk-functype (mk-list (valtype-I32 ∷ valtype-I32 ∷ valtype-I32 ∷ [])) (mk-list []))
tcopy-ok {x = x} {y = y} {rt = rt} {limx = limx} {limy = limy} x< lkx y< lky =
  plain _ _ _ _ _ (table-copy _ x y limx rt limy x< lkx y< lky)

tinit-ok : ∀ {s C x y rt lim} →
  (proj-uN-0 32 x < length (context-TABLES C)) → ((context-TABLES C [ proj-uN-0 32 x ]!) ≡ mk-tabletype lim rt) →
  (proj-uN-0 32 y < length (context-ELEMS C)) → ((context-ELEMS C [ proj-uN-0 32 y ]!) ≡ rt) →
  Instr-ok2 s C (admininstr-TABLE-INIT x y)
    (mk-functype (mk-list (valtype-I32 ∷ valtype-I32 ∷ valtype-I32 ∷ [])) (mk-list []))
tinit-ok {x = x} {y = y} {rt = rt} {lim = lim} x< lkx y< lky =
  plain _ _ _ _ _ (table-init _ x y lim rt x< lkx y< lky)

iok-tget : ∀ {C x d c} → Instr-ok C (TABLE-GET x) (mk-functype (mk-list d) (mk-list c)) →
  Σ (reftype × limits) λ (rt , lim) → (d ≡ valtype-I32 ∷ []) × (c ≡ valtype-reftype rt ∷ []) ×
    (proj-uN-0 32 x < length (context-TABLES C)) ×
    ((context-TABLES C [ proj-uN-0 32 x ]!) ≡ mk-tabletype lim rt)
iok-tget (table-get _ _ rt lim p q) = (rt , lim) , refl , refl , p , q
tget-inv : ∀ {s C e d c x} → Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) →
  e ≡ admininstr-TABLE-GET x →
  Σ (reftype × limits) λ (rt , lim) → (d ≡ valtype-I32 ∷ []) × (c ≡ valtype-reftype rt ∷ []) ×
    (proj-uN-0 32 x < length (context-TABLES C)) ×
    ((context-TABLES C [ proj-uN-0 32 x ]!) ≡ mk-tabletype lim rt)
tget-inv (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-tget iok
tget-inv (label _ _ _ _ _ _ _ _ _ _) ()
tget-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
tget-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
tget-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
tget-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
tget-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
tget-inv (Instr-ok2--trap _ _ _ _) ()

iok-rfunc : ∀ {C x d c} → Instr-ok C (REF-FUNC x) (mk-functype (mk-list d) (mk-list c)) →
  (d ≡ []) × (c ≡ valtype-FUNCREF ∷ []) × (proj-uN-0 32 x < length (context-FUNCS C))
iok-rfunc (ref-func _ _ ft p q) = refl , refl , p
rfunc-inv : ∀ {s C e d c x} → Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) →
  e ≡ admininstr-REF-FUNC x →
  (d ≡ []) × (c ≡ valtype-FUNCREF ∷ []) × (proj-uN-0 32 x < length (context-FUNCS C))
rfunc-inv (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-rfunc iok
rfunc-inv (label _ _ _ _ _ _ _ _ _ _) ()
rfunc-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
rfunc-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
rfunc-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
rfunc-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
rfunc-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
rfunc-inv (Instr-ok2--trap _ _ _ _) ()

iok-call : ∀ {C x d c} → Instr-ok C (CALL x) (mk-functype (mk-list d) (mk-list c)) →
  Σ (List valtype × List valtype) λ (t1 , t2) → (d ≡ t1) × (c ≡ t2) ×
    (proj-uN-0 32 x < length (context-FUNCS C)) ×
    ((context-FUNCS C [ proj-uN-0 32 x ]!) ≡ mk-functype (mk-list t1) (mk-list t2))
iok-call (call _ _ t1 t2 p q) = (t1 , t2) , refl , refl , p , q
call-inv : ∀ {s C e d c x} → Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) →
  e ≡ admininstr-CALL x →
  Σ (List valtype × List valtype) λ (t1 , t2) → (d ≡ t1) × (c ≡ t2) ×
    (proj-uN-0 32 x < length (context-FUNCS C)) ×
    ((context-FUNCS C [ proj-uN-0 32 x ]!) ≡ mk-functype (mk-list t1) (mk-list t2))
call-inv (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-call iok
call-inv (label _ _ _ _ _ _ _ _ _ _) ()
call-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
call-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
call-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
call-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
call-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
call-inv (Instr-ok2--trap _ _ _ _) ()

-- ===== context-stack agreement for the ctxt-* congruence refactor =====
-- pres-step/pres-read carry the instruction-context Ci separately from
-- the frame-context Cf; Agree records that they coincide on the four
-- frame-relevant fields (LOCALS/GLOBALS/TABLES/TYPES).  For the concrete
-- recursion contexts labC t' ⧺ Ci / retC t' ⧺ Ci this is definitional
-- (labC/retC touch only LABELS/RETURN), so agree-labC/agree-retC just
-- transport the same proofs.
record Agree (Ci Cf : context) : Set where
  constructor mk-agree
  field
    loc≡  : context-LOCALS Ci ≡ context-LOCALS Cf
    glob≡ : context-GLOBALS Ci ≡ context-GLOBALS Cf
    tab≡  : context-TABLES Ci ≡ context-TABLES Cf
    typ≡  : context-TYPES Ci ≡ context-TYPES Cf
    func≡ : context-FUNCS Ci ≡ context-FUNCS Cf
    elem≡ : context-ELEMS Ci ≡ context-ELEMS Cf
    mem≡  : context-MEMS Ci ≡ context-MEMS Cf

agree-refl : ∀ {C} → Agree C C
agree-refl = mk-agree refl refl refl refl refl refl refl

agree-labC : ∀ {Ci Cf} t' → Agree Ci Cf → Agree (labC t' ⧺ Ci) Cf
agree-labC t' (mk-agree l g t y fn e m) = mk-agree l g t y fn e m

agree-retC : ∀ {Ci Cf} t' → Agree Ci Cf → Agree (retC t' ⧺ Ci) Cf
agree-retC t' (mk-agree l g t y fn e m) = mk-agree l g t y fn e m

-- Pin a value's type to the reftype demanded by a bulk table op's middle slot.
pin-ref : ∀ {s v rt t0 t1 t2 a b} → Val-ok s v t1 →
  Resulttype-sub (mk-list (t0 ∷ t1 ∷ t2 ∷ [])) (mk-list (a ∷ valtype-reftype rt ∷ b ∷ [])) →
  Val-ok s v (valtype-reftype rt)
pin-ref vok (mk-Resulttype-sub _ _ _ (_ ∷ vs1 ∷ _ ∷ [])) =
  subst (Val-ok _ _) (sym (vt-sub-val vok vs1)) vok

pres-read : ∀ {s f Cf Ci es es' u1 u2} →
  Store-ok s → Frame-ok s f Cf → Agree Ci Cf →
  Instrs-ok2 s Ci es (mk-functype (mk-list u1) (mk-list u2)) →
  Step-read (mk-config (mk-state s f) es) es' →
  Instrs-ok2 s Ci es' (mk-functype (mk-list u1) (mk-list u2))

pres-read sok fok ag ok (Step-read--local-get _ x)
  with singleton-inv ok
... | mk-single p dm c gok s1 s2 with lget-inv gok refl
... | t , refl , refl , x< , lkp with frame-facts fok
... | ff =
  let open FrameFacts ff
      lkp0 = subst (λ l → (l [ proj-uN-0 32 x ]!) ≡ t) (Agree.loc≡ ag) lkp
      x<0  = subst (λ l → proj-uN-0 32 x < length l) (Agree.loc≡ ag) x<
      lkp' = subst (λ l → (l [ proj-uN-0 32 x ]!) ≡ t) locals-eq lkp0
      x<'  = subst (λ l → proj-uN-0 32 x < length l) locals-eq x<0
      vok  = pw-lookup locals-ok x<'
  in push1 p (val-ok-ty (subst (Val-ok _ _) lkp' vok)) (rt-norm p s1) s2

pres-read (mk-Store-ok _ gil gtl _ _ _ _ _ _ _ _ _ _
            glen gok _ _ _ _ _ _ _ _ _ _ refl)
          fok ag ok (Step-read--global-get _ x)
  with singleton-inv ok
... | mk-single p dm c ggok s1 s2 with gget-inv ggok refl
... | (mu , t) , refl , refl , x< , lkp with frame-facts fok
... | ff =
  let open FrameFacts ff
      lkp0  = subst (λ l → (l [ proj-uN-0 32 x ]!) ≡ mk-globaltype mu t) (Agree.glob≡ ag) lkp
      x<0   = subst (λ l → proj-uN-0 32 x < length l) (Agree.glob≡ ag) x<
      lkp'  = subst (λ l → (l [ proj-uN-0 32 x ]!) ≡ mk-globaltype mu t) globals-eq lkp0
      x<gts = subst (λ l → proj-uN-0 32 x < length l) globals-eq x<0
      x<ga  = subst (proj-uN-0 32 x <_) (sym gaddrs-len) x<gts
      xaok  = pw-lookup globals-ok x<ga
      xaok' = subst (λ g → Externaddr-ok _ _ (GLOBAL g)) lkp' xaok
      inv   = xa-global-inv xaok'
      giok  = pw-lookup gok (proj₁ inv)
      vok   = ginst-val giok (proj₂ inv)
  in push1 p (val-ok-ty vok) (rt-norm p s1) s2

-- v* (block bt instr*) ~> label_n{eps} v* instr*
pres-read {s = s} {f = f} sok fok ag ok
  (Step-read--block _ k vals bt instrs vn t1s t2s lenv lent2 lent1 bteq)
  with decomp ok (map (λ w → admininstr-val w) vals)
        (admininstr-BLOCK bt instrs ∷ []) refl
... | mk-split m okRow okB
  with row-inv vals okRow | singleton-inv okB
... | (ts , pwv , rsub) | mk-single p d c bok sb1 sb2
  with block-inv bok refl
... | bkok , body
  with ft-inj (tr≡ (sym (blocktype-agree {s = s} {f = f} bkok
                     (tr≡ (Agree.typ≡ ag) (FrameFacts.types-eq (frame-facts fok))))) bteq)
... | refl , refl
  with rt-sub-split (rt-sub-trans rsub sb1)
        (tr≡ (tr≡ (pw-length pwv) lenv) (sym lent1))
... | usubp , tsub =
  single-intro (mk-single p [] t2s
    (label _ _ vn [] _ t2s t2s lent2 (empty-ty t2s)
      (Instrs-ok2--seq _ _ (map (λ w → admininstr-val w) vals)
        (map (λ i → admininstr-instr i) instrs) _ _ _
        (row-intro (pw-val-sub pwv (rt-sub-pw tsub)))
        (instrs-ok→2 s body)))
    (unnorm p usubp)
    sb2)

-- v* (loop bt instr*) ~> label_k{loop bt instr*} v* instr*
pres-read {s = s} {f = f} sok fok ag ok
  (Step-read--loop _ k vals bt instrs t1s vn t2s lenv lent2 lent1 bteq)
  with decomp ok (map (λ w → admininstr-val w) vals)
        (admininstr-LOOP bt instrs ∷ []) refl
... | mk-split m okRow okL
  with row-inv vals okRow | singleton-inv okL
... | (ts , pwv , rsub) | mk-single p d c lok sb1 sb2
  with loop-inv lok refl
... | liok , bkok , body
  with ft-inj (tr≡ (sym (blocktype-agree {s = s} {f = f} bkok
                     (tr≡ (Agree.typ≡ ag) (FrameFacts.types-eq (frame-facts fok))))) bteq)
... | refl , refl
  with rt-sub-split (rt-sub-trans rsub sb1)
        (tr≡ (tr≡ (pw-length pwv) lenv) (sym lent1))
... | usubp , tsub =
  single-intro (mk-single p [] t2s
    (label _ _ k (LOOP bt instrs ∷ []) _ t2s t1s lent1
      (Instrs-ok2--instr _ _ _ _ _ (plain _ _ _ _ _ liok))
      (Instrs-ok2--seq _ _ (map (λ w → admininstr-val w) vals)
        (map (λ i → admininstr-instr i) instrs) _ _ _
        (row-intro (pw-val-sub pwv (rt-sub-pw tsub)))
        (instrs-ok→2 s body)))
    (unnorm p usubp)
    sb2)

-- v* (CALL-ADDR a) ~> FRAME_n{f} (LABEL_n{} instr*)
pres-read {s = s} {Ci = C} sok fok ag ok
  (call-addr _ k vals a vn f instrs t1s t2s mm vfunc x tloc
    lenv lent2 lent1 a<fi fieq refl ndef refl)
  with decomp ok (map (λ w → admininstr-val w) vals) (CALL-ADDR a ∷ []) refl
... | mk-split m okRow okCA
  with row-inv vals okRow | singleton-inv okCA
... | (rowts , pwv , rsub) | mk-single p d c caok sCA1 sCA2
  with calladdr-inv caok refl
... | xaok with xa-func-inv xaok
... | a<s , ftyeq
  with ft-inj (tr≡ (sym (cong funcinst-TYPE fieq)) ftyeq)
... | refl , refl
  with subst (λ fi → Funcinst-ok s fi (funcinst-TYPE fi)) fieq (sfok sok a<s)
... | mk-Funcinst-ok _ _ _ _ Cf ftok
        (mk-Moduleinst-ok _ ftl fal gal tal mal eal dal exl fFl gtl ttl mtl etl dtl
          fok1 gl gk2 fl fk2 ml mk2 tl tk2 exk dl dl2 dk2 el el2 ek2 disj sz mem)
        fk
  with func-ok-inv fk refl
... | ndef' , bodyExpr
  with rt-sub-split (rt-sub-trans rsub sCA1)
        (tr≡ (tr≡ (pw-length pwv) lenv) (sym lent1))
... | u1subp , rtsub =
  let Cf' = Cf ⧺ record
        { context-TYPES = [] ; context-FUNCS = [] ; context-GLOBALS = []
        ; context-TABLES = [] ; context-MEMS = [] ; context-ELEMS = []
        ; context-DATAS = [] ; context-LOCALS = (t1s ++ tloc)
        ; LABELS = [] ; context-RETURN = nothing }
      valsT1 = pw-val-sub pwv (rt-sub-pw rtsub)
      framePw = pw-app valsT1 (defaults-ok tloc ndef)
      frameOK = mk-Frame-ok s (vals ++ map (λ t → unwrap! (default- t)) tloc)
        mm Cf (t1s ++ tloc)
        (mk-Moduleinst-ok _ ftl fal gal tal mal eal dal exl fFl gtl ttl mtl etl dtl
          fok1 gl gk2 fl fk2 ml mk2 tl tk2 exk dl dl2 dk2 el el2 ek2 disj sz mem)
        (pw-length framePw) framePw
      bodyTy2 = instrs-ok→2 s (expr-ok-instrs bodyExpr)
      labelInstr = label s (retC t2s ⧺ Cf') vn [] (map (λ i → admininstr-instr i) instrs)
        t2s t2s lent2 (empty-ty t2s) bodyTy2
      frameInstr = Instr-ok2--frame s C vn f
        (LABEL- vn [] (map (λ i → admininstr-instr i) instrs) ∷ []) t2s Cf'
        lent2 frameOK
        (mk-Expr-ok2 s (retC t2s ⧺ Cf') _ t2s
          (Instrs-ok2--instr _ _ _ _ _ labelInstr))
  in single-intro (mk-single p [] t2s frameInstr (unnorm p u1subp) sCA2)

-- memory.size / table.size ~> i32.const (current size).
pres-read sok fok ag ok (Step-read--memory-size _ v-n _)
  with singleton-inv ok
... | mk-single p d c mok s1 s2 with msize-inv mok refl
... | refl , refl =
  push1 p (plain _ _ _ _ _ (const _ I32 (mk-uN v-n))) (rt-norm p s1) s2
pres-read sok fok ag ok (Step-read--table-size _ x v-n _)
  with singleton-inv ok
... | mk-single p d c tok s1 s2 with tsize-inv tok refl
... | refl , refl =
  push1 p (plain _ _ _ _ _ (const _ I32 (mk-uN v-n))) (rt-norm p s1) s2

-- table.get x ~> ref  (push the stored ref, well-typed at the elemtype).
pres-read {s = s} {f = f} sok fok ag ok (table-get-val _ i x irefok)
  with decomp ok (admininstr-CONST I32 i ∷ []) (admininstr-TABLE-GET x ∷ []) refl
... | mk-split m okC okT with const-ty okC | singleton-inv okT
... | (p1 , s11 , s12) | mk-single p2 d2 c2 tgok s21 s22
  with tget-inv tgok refl
... | (rt , lim) , refl , refl , x<C , tlkC
  with rt-sub-unsnoc (rt-sub-trans s12 s21)
... | p1sub , _
  with frame-facts fok
... | ff
  with pw-lookup (FrameFacts.tables-ok ff)
         (subst (proj-uN-0 32 x <_) (sym (FrameFacts.taddrs-len ff))
           (subst (λ l → proj-uN-0 32 x < length l) (FrameFacts.tables-eq ff)
             (subst (λ l → proj-uN-0 32 x < length l) (Agree.tab≡ ag) x<C)))
... | xaok0 =
  let xaok = subst (λ tt → Externaddr-ok s
               (externaddr-TABLE ((TABLES (frame-MODULE f)) [ proj-uN-0 32 x ]!)) (TABLE tt))
               (subst (λ l → (l [ proj-uN-0 32 x ]!) ≡ mk-tabletype lim rt)
                      (FrameFacts.tables-eq ff)
                      (subst (λ l → (l [ proj-uN-0 32 x ]!) ≡ mk-tabletype lim rt)
                             (Agree.tab≡ ag) tlkC))
               xaok0
      a< = proj₁ (xa-table-inv xaok)
      tteq = proj₂ (proj₂ (xa-table-inv xaok))
      rok = table-ref-at
              (subst (Tableinst-ok s ((store-TABLES s) [ (TABLES (frame-MODULE f)) [ proj-uN-0 32 x ]! ]!))
                     tteq (stok sok a<))
              irefok
  in push1 p2 (Instr-ok2--ref _ _ _ rt rok) (rt-sub-trans s11 p1sub) s22

-- ref.func x ~> ref.func_addr a  (a from the module's func addresses).
pres-read {s = s} {f = f} sok fok ag ok (Step-read--ref-func _ x _)
  with singleton-inv ok
... | mk-single p d c rfok s1 s2 with rfunc-inv rfok refl
... | refl , refl , x<C
  with frame-facts fok
... | ff =
  push1 p (Instr-ok2--ref _ _
            (REF-FUNC-ADDR ((FUNCS (frame-MODULE f)) [ proj-uN-0 32 x ]!)) FUNCREF
            (Ref-ok--func _ _ _
              (pw-lookup (FrameFacts.funcs-ok ff)
                (subst (proj-uN-0 32 x <_) (sym (FrameFacts.faddrs-len ff))
                  (subst (λ l → proj-uN-0 32 x < length l) (FrameFacts.funcs-eq ff)
                    (subst (λ l → proj-uN-0 32 x < length l) (Agree.func≡ ag) x<C))))))
    (rt-norm p s1) s2

-- call x ~> call_addr a.
pres-read {s = s} {f = f} sok fok ag ok (Step-read--call _ x _)
  with singleton-inv ok
... | mk-single p d c cok s1 s2 with call-inv cok refl
... | (t1 , t2) , refl , refl , x<C , flkC
  with frame-facts fok
... | ff
  with pw-lookup (FrameFacts.funcs-ok ff)
         (subst (proj-uN-0 32 x <_) (sym (FrameFacts.faddrs-len ff))
           (subst (λ l → proj-uN-0 32 x < length l) (FrameFacts.funcs-eq ff)
             (subst (λ l → proj-uN-0 32 x < length l) (Agree.func≡ ag) x<C)))
... | xaok0 =
  single-intro (mk-single p t1 t2
    (Instr-ok2--call-addr _ _ ((FUNCS (frame-MODULE f)) [ proj-uN-0 32 x ]!) t1 t2
      (subst (λ ft → Externaddr-ok s
               (externaddr-FUNC ((FUNCS (frame-MODULE f)) [ proj-uN-0 32 x ]!)) (FUNC ft))
             (subst (λ l → (l [ proj-uN-0 32 x ]!) ≡ mk-functype (mk-list t1) (mk-list t2))
                    (FrameFacts.funcs-eq ff)
                    (subst (λ l → (l [ proj-uN-0 32 x ]!) ≡ mk-functype (mk-list t1) (mk-list t2))
                           (Agree.func≡ ag) flkC))
             xaok0))
    s1 s2)

-- nt.load ao ~> nt.const c  (loaded value is already typed at nt).
pres-read sok fok ag ok (load-num-val _ i nt ao c _ _)
  with decomp ok (admininstr-CONST I32 i ∷ []) (admininstr-LOAD nt nothing ao ∷ []) refl
... | mk-split m okC okL with const-ty okC | singleton-inv okL
... | (p1 , s11 , s12) | mk-single p2 d2 c2 lok s21 s22
  with loadnum-inv lok refl
... | refl , refl
  with rt-sub-unsnoc (rt-sub-trans s12 s21)
... | p1sub , _ =
  push1 p2 (plain _ _ _ _ _ (const _ nt c)) (rt-sub-trans s11 p1sub) s22
pres-read sok fok ag ok (load-pack-val-0 _ i v-n v-sx ao c _ _)
  with decomp ok (admininstr-CONST I32 i ∷ [])
        (admininstr-LOAD (numtype-Inn Inn-I32) (just (mk-loadop- (mk-sz v-n) v-sx)) ao ∷ []) refl
... | mk-split m okC okL with const-ty okC | singleton-inv okL
... | (p1 , s11 , s12) | mk-single p2 d2 c2 lok s21 s22
  with loadpack-inv lok refl
... | refl , refl
  with rt-sub-unsnoc (rt-sub-trans s12 s21)
... | p1sub , _ =
  push1 p2 (plain _ _ _ _ _ (const _ I32 _)) (rt-sub-trans s11 p1sub) s22
pres-read sok fok ag ok (load-pack-val-1 _ i v-n v-sx ao c _ _)
  with decomp ok (admininstr-CONST I32 i ∷ [])
        (admininstr-LOAD (numtype-Inn Inn-I64) (just (mk-loadop- (mk-sz v-n) v-sx)) ao ∷ []) refl
... | mk-split m okC okL with const-ty okC | singleton-inv okL
... | (p1 , s11 , s12) | mk-single p2 d2 c2 lok s21 s22
  with loadpack-inv lok refl
... | refl , refl
  with rt-sub-unsnoc (rt-sub-trans s12 s21)
... | p1sub , _ =
  push1 p2 (plain _ _ _ _ _ (const _ I64 _)) (rt-sub-trans s11 p1sub) s22

-- call_indirect x y ~> call_addr a  (table[i] = a, a's funcinst type = C.TYPES[y]).
pres-read {s = s} {f = f} sok fok ag ok (call-indirect-call _ i x y a _ _ a< tyeq)
  with decomp ok (admininstr-CONST I32 i ∷ []) (admininstr-CALL-INDIRECT x y ∷ []) refl
... | mk-split m okC okCI with const-ty okC | singleton-inv okCI
... | (p1 , s11 , s12) | mk-single p2 d2 c2 ciok s21 s22
  with ci-inv ciok refl
... | t1 , t2 , refl , refl , lky
  with rt-sub-unsnoc
        (subst (λ l → Resulttype-sub (mk-list (p1 ++ valtype-I32 ∷ [])) (mk-list l))
               (sym (++-assoc p2 t1 (valtype-I32 ∷ [])))
               (rt-sub-trans s12 s21))
... | p1sub , _ =
  single-intro (mk-single p2 t1 t2
    (Instr-ok2--call-addr s _ a t1 t2
      (subst (λ ft → Externaddr-ok s (externaddr-FUNC a) (FUNC ft))
        (tr≡ (sym tyeq)
          (subst (λ l → (l [ proj-uN-0 32 y ]!) ≡ mk-functype (mk-list t1) (mk-list t2))
            (tr≡ (Agree.typ≡ ag) (FrameFacts.types-eq (frame-facts fok))) lky))
        (Externaddr-ok--func s a (store-FUNCS s [ a ]!) a< refl)))
    (rt-sub-trans s11 p1sub) s22)

-- ===== Step-read: bulk-op decompositions (reduct = balanced sequence) =====
-- memory.fill (n≠0) ~> [i, v, store8; i+1, v, n-1, memory.fill]
pres-read {s = s} sok fok ag ok (memory-fill-succ _ i v-val v-n _ _)
  with decomp ok (map (λ w → admininstr-val w) (val-CONST I32 i ∷ v-val ∷ val-CONST I32 (mk-uN v-n) ∷ [])) (admininstr-MEMORY-FILL ∷ []) refl
... | mk-split m okRow okOp with singleton-inv okOp
... | mk-single p d c opok os1 os2
  with mfill-facts opok refl | mfill-dom opok refl
... | mt , mem< , memlk | refl , refl
  with row-inv (val-CONST I32 i ∷ v-val ∷ val-CONST I32 (mk-uN v-n) ∷ []) okRow
... | (t0 ∷ t1 ∷ t2 ∷ []) , (vok0 ∷ vok1 ∷ vok2 ∷ []) , rsub
  with rt-sub-split {b = t0 ∷ t1 ∷ t2 ∷ []} {d = valtype-I32 ∷ valtype-I32 ∷ valtype-I32 ∷ []}
        (rt-sub-trans rsub os1) refl
... | u1p , mk-Resulttype-sub _ _ _ (vs0 ∷ vs1 ∷ vs2 ∷ []) =
  let vok1' : Val-ok s v-val valtype-I32
      vok1' = subst (Val-ok s v-val) (sym (vt-sub-val vok1 vs1)) vok1
      u1u2 = rt-sub-trans u1p (rt-norml p os2)
  in run-empty
       (c32
        >>> fr (valtype-I32 ∷ []) (lift1 (val-ok-ty vok1'))
        >>> lift1 (store8-ok mem< memlk)
        >>> c32
        >>> fr (valtype-I32 ∷ []) (lift1 (val-ok-ty vok1'))
        >>> fr (valtype-I32 ∷ valtype-I32 ∷ []) c32
        >>> lift1 (mfill-ok mem< memlk))
       u1u2

-- memory.init (n≠0) ~> [j, byte, store8; j+1, i+1, n-1, memory.init x]
pres-read sok fok ag ok (memory-init-succ _ j i v-n x _ _ _)
  with decomp ok (map (λ w → admininstr-val w)
        (val-CONST I32 j ∷ val-CONST I32 i ∷ val-CONST I32 (mk-uN v-n) ∷ [])) (admininstr-MEMORY-INIT x ∷ []) refl
... | mk-split m okRow okOp with singleton-inv okOp
... | mk-single p d c opok os1 os2 with minit-facts opok refl | minit-inv opok refl
... | (mt , mem< , memlk , data< , datalk) | dl , refl =
  run-empty
    (c32
     >>> fr (valtype-I32 ∷ []) c32
     >>> lift1 (store8-ok mem< memlk)
     >>> c32
     >>> fr (valtype-I32 ∷ []) c32
     >>> fr (valtype-I32 ∷ valtype-I32 ∷ []) c32
     >>> lift1 (minit-ok mem< memlk data< datalk))
    (three-sub okRow os1 dl os2)

-- memory.copy (j≤i) ~> [j, i, load8, store8; j+1, i+1, n-1, memory.copy]
pres-read sok fok ag ok (memory-copy-le _ j i v-n _ _ _)
  with decomp ok (map (λ w → admininstr-val w)
        (val-CONST I32 j ∷ val-CONST I32 i ∷ val-CONST I32 (mk-uN v-n) ∷ [])) (admininstr-MEMORY-COPY ∷ []) refl
... | mk-split m okRow okOp with singleton-inv okOp
... | mk-single p d c opok os1 os2 with mcopy-facts opok refl | mcopy-inv opok refl
... | (mt , mem< , memlk) | dl , refl =
  run-empty
    (c32
     >>> fr (valtype-I32 ∷ []) c32
     >>> fr (valtype-I32 ∷ []) (lift1 (load8-ok mem< memlk))
     >>> lift1 (store8-ok mem< memlk)
     >>> c32
     >>> fr (valtype-I32 ∷ []) c32
     >>> fr (valtype-I32 ∷ valtype-I32 ∷ []) c32
     >>> lift1 (mcopy-ok mem< memlk))
    (three-sub okRow os1 dl os2)

-- memory.copy (j>i) ~> [j+n-1, i+n-1, load8, store8; j, i, n-1, memory.copy]
pres-read sok fok ag ok (memory-copy-gt _ j i v-n _ _ _)
  with decomp ok (map (λ w → admininstr-val w)
        (val-CONST I32 j ∷ val-CONST I32 i ∷ val-CONST I32 (mk-uN v-n) ∷ [])) (admininstr-MEMORY-COPY ∷ []) refl
... | mk-split m okRow okOp with singleton-inv okOp
... | mk-single p d c opok os1 os2 with mcopy-facts opok refl | mcopy-inv opok refl
... | (mt , mem< , memlk) | dl , refl =
  run-empty
    (c32
     >>> fr (valtype-I32 ∷ []) c32
     >>> fr (valtype-I32 ∷ []) (lift1 (load8-ok mem< memlk))
     >>> lift1 (store8-ok mem< memlk)
     >>> c32
     >>> fr (valtype-I32 ∷ []) c32
     >>> fr (valtype-I32 ∷ valtype-I32 ∷ []) c32
     >>> lift1 (mcopy-ok mem< memlk))
    (three-sub okRow os1 dl os2)

-- table.fill (n≠0) ~> [i, v, table.set x; i+1, v, n-1, table.fill x]
pres-read {s = s} {Ci = Ci} {u1 = u1} {u2 = u2} sok fok ag ok (table-fill-succ _ i v-val v-n x _ _)
  with decomp ok (map (λ w → admininstr-val w)
        (val-CONST I32 i ∷ v-val ∷ val-CONST I32 (mk-uN v-n) ∷ [])) (admininstr-TABLE-FILL x ∷ []) refl
... | mk-split m okRow okOp
  with singleton-inv okOp | row-inv (val-CONST I32 i ∷ v-val ∷ val-CONST I32 (mk-uN v-n) ∷ []) okRow
... | mk-single p d c opok os1 os2 | (t0 ∷ t1 ∷ t2 ∷ []) , (vok0 ∷ vok1 ∷ vok2 ∷ []) , rsub
  with tfill-all opok refl
... | rt , lim , x< , lk , deq , ceq =
  let split = rt-sub-split {b = t0 ∷ t1 ∷ t2 ∷ []} {d = valtype-I32 ∷ valtype-reftype rt ∷ valtype-I32 ∷ []}
                (subst (λ dd → Resulttype-sub (mk-list (u1 ++ t0 ∷ t1 ∷ t2 ∷ [])) (mk-list (p ++ dd)))
                       deq (rt-sub-trans rsub os1)) refl
      vok1' = pin-ref vok1 (proj₂ split)
      u1u2 = rt-sub-trans (proj₁ split)
               (rt-norml p (subst (λ cc → Resulttype-sub (mk-list (p ++ cc)) (mk-list u2)) ceq os2))
      setok : Instr-ok2 s Ci (admininstr-TABLE-SET x)
                (mk-functype (mk-list (valtype-I32 ∷ valtype-reftype rt ∷ [])) (mk-list []))
      setok = tset-ok {x = x} {rt = rt} {lim = lim} x< lk
      fillok : Instr-ok2 s Ci (admininstr-TABLE-FILL x)
                 (mk-functype (mk-list (valtype-I32 ∷ valtype-reftype rt ∷ valtype-I32 ∷ [])) (mk-list []))
      fillok = tfill-ok {x = x} {rt = rt} {lim = lim} x< lk
  in run-empty
       (c32
        >>> fr (valtype-I32 ∷ []) (lift1 (val-ok-ty vok1'))
        >>> lift1 setok
        >>> c32
        >>> fr (valtype-I32 ∷ []) (lift1 (val-ok-ty vok1'))
        >>> fr (valtype-I32 ∷ valtype-reftype rt ∷ []) c32
        >>> lift1 fillok)
       u1u2

-- table.copy (j≤i) ~> [j, i, table.get y, table.set x; j+1, i+1, n-1, table.copy x y]
pres-read sok fok ag ok (table-copy-le _ j i v-n x y _ _ _)
  with decomp ok (map (λ w → admininstr-val w)
        (val-CONST I32 j ∷ val-CONST I32 i ∷ val-CONST I32 (mk-uN v-n) ∷ [])) (admininstr-TABLE-COPY x y ∷ []) refl
... | mk-split m okRow okOp with singleton-inv okOp
... | mk-single p d c opok os1 os2 with tcopy-all opok refl
... | rt , limx , limy , x< , lkx , y< , lky , refl , refl =
  run-empty
    (c32
     >>> fr (valtype-I32 ∷ []) c32
     >>> fr (valtype-I32 ∷ []) (lift1 (tget-ok y< lky))
     >>> lift1 (tset-ok x< lkx)
     >>> c32
     >>> fr (valtype-I32 ∷ []) c32
     >>> fr (valtype-I32 ∷ valtype-I32 ∷ []) c32
     >>> lift1 (tcopy-ok x< lkx y< lky))
    (three-sub okRow os1 refl os2)

-- table.copy (j>i) ~> [j+n-1, i+n-1, table.get y, table.set x; j, i, n-1, table.copy x y]
pres-read sok fok ag ok (table-copy-gt _ j i v-n x y _ _ _)
  with decomp ok (map (λ w → admininstr-val w)
        (val-CONST I32 j ∷ val-CONST I32 i ∷ val-CONST I32 (mk-uN v-n) ∷ [])) (admininstr-TABLE-COPY x y ∷ []) refl
... | mk-split m okRow okOp with singleton-inv okOp
... | mk-single p d c opok os1 os2 with tcopy-all opok refl
... | rt , limx , limy , x< , lkx , y< , lky , refl , refl =
  run-empty
    (c32
     >>> fr (valtype-I32 ∷ []) c32
     >>> fr (valtype-I32 ∷ []) (lift1 (tget-ok y< lky))
     >>> lift1 (tset-ok x< lkx)
     >>> c32
     >>> fr (valtype-I32 ∷ []) c32
     >>> fr (valtype-I32 ∷ valtype-I32 ∷ []) c32
     >>> lift1 (tcopy-ok x< lkx y< lky))
    (three-sub okRow os1 refl os2)

-- table.init (n≠0) ~> [j, elem[i], table.set x; j+1, i+1, n-1, table.init x y]
pres-read {s = s} {f = f} sok fok ag ok (table-init-succ _ j i v-n x y i< _ _)
  with decomp ok (map (λ w → admininstr-val w)
        (val-CONST I32 j ∷ val-CONST I32 i ∷ val-CONST I32 (mk-uN v-n) ∷ [])) (admininstr-TABLE-INIT x y ∷ []) refl
... | mk-split m okRow okOp
  with singleton-inv okOp | frame-facts fok
... | mk-single p d c opok os1 os2 | ff
  with tinit-all opok refl
... | rt , lim , x< , lkx , y< , lky , refl , refl =
  let elk = pw-lookup (FrameFacts.elems-ok ff)
              (subst (proj-uN-0 32 y <_) (sym (FrameFacts.eaddrs-len ff))
                (subst (λ l → proj-uN-0 32 y < length l) (FrameFacts.elems-eq ff)
                  (subst (λ l → proj-uN-0 32 y < length l) (Agree.elem≡ ag) y<)))
      etseq = tr≡ (cong (λ l → l [ proj-uN-0 32 y ]!) (sym (FrameFacts.elems-eq ff)))
                (tr≡ (cong (λ l → l [ proj-uN-0 32 y ]!) (sym (Agree.elem≡ ag))) lky)
      rok = elem-ref-at (subst (Eleminst-ok s (fun-elem (mk-state s f) y)) etseq elk) i<
  in run-empty
       (c32
        >>> fr (valtype-I32 ∷ []) (lift1 (Instr-ok2--ref _ _ _ _ rok))
        >>> lift1 (tset-ok x< lkx)
        >>> c32
        >>> fr (valtype-I32 ∷ []) c32
        >>> fr (valtype-I32 ∷ valtype-I32 ∷ []) c32
        >>> lift1 (tinit-ok x< lkx y< lky))
       (three-sub okRow os1 refl os2)

-- ===== Step-read: bulk-op zero cases (reduct []) =====
pres-read sok fok ag ok (memory-fill-zero _ i v-val v-n _ _)
  with decomp ok (map (λ w → admininstr-val w) (val-CONST I32 i ∷ v-val ∷ val-CONST I32 (mk-uN v-n) ∷ [])) (admininstr-MEMORY-FILL ∷ []) refl
... | mk-split m okRow okOp with singleton-inv okOp
... | mk-single p d c opok os1 os2 with mfill-inv opok refl
... | dl , refl = three-empty okRow os1 dl os2
pres-read sok fok ag ok (memory-copy-zero _ j i v-n _ _)
  with decomp ok (map (λ w → admininstr-val w) (val-CONST I32 j ∷ val-CONST I32 i ∷ val-CONST I32 (mk-uN v-n) ∷ [])) (admininstr-MEMORY-COPY ∷ []) refl
... | mk-split m okRow okOp with singleton-inv okOp
... | mk-single p d c opok os1 os2 with mcopy-inv opok refl
... | dl , refl = three-empty okRow os1 dl os2
pres-read sok fok ag ok (memory-init-zero _ j i v-n x _ _)
  with decomp ok (map (λ w → admininstr-val w) (val-CONST I32 j ∷ val-CONST I32 i ∷ val-CONST I32 (mk-uN v-n) ∷ [])) (admininstr-MEMORY-INIT x ∷ []) refl
... | mk-split m okRow okOp with singleton-inv okOp
... | mk-single p d c opok os1 os2 with minit-inv opok refl
... | dl , refl = three-empty okRow os1 dl os2
pres-read sok fok ag ok (table-fill-zero _ i v-val v-n x _ _)
  with decomp ok (map (λ w → admininstr-val w) (val-CONST I32 i ∷ v-val ∷ val-CONST I32 (mk-uN v-n) ∷ [])) (admininstr-TABLE-FILL x ∷ []) refl
... | mk-split m okRow okOp with singleton-inv okOp
... | mk-single p d c opok os1 os2 with tfill-inv opok refl
... | dl , refl = three-empty okRow os1 dl os2
pres-read sok fok ag ok (table-copy-zero _ j i v-n x y _ _)
  with decomp ok (map (λ w → admininstr-val w) (val-CONST I32 j ∷ val-CONST I32 i ∷ val-CONST I32 (mk-uN v-n) ∷ [])) (admininstr-TABLE-COPY x y ∷ []) refl
... | mk-split m okRow okOp with singleton-inv okOp
... | mk-single p d c opok os1 os2 with tcopy-inv opok refl
... | dl , refl = three-empty okRow os1 dl os2
pres-read sok fok ag ok (table-init-zero _ j i v-n x y _ _)
  with decomp ok (map (λ w → admininstr-val w) (val-CONST I32 j ∷ val-CONST I32 i ∷ val-CONST I32 (mk-uN v-n) ∷ [])) (admininstr-TABLE-INIT x y ∷ []) refl
... | mk-split m okRow okOp with singleton-inv okOp
... | mk-single p d c opok os1 os2 with tinit-inv opok refl
... | dl , refl = three-empty okRow os1 dl os2

-- ===== Step-read: vector loads (push VCONST; plain v128.load vacuous) =====
pres-read sok fok ag ok (vload-val _ i ao c _ _)
  with decomp ok (admininstr-CONST I32 i ∷ []) (admininstr-VLOAD V128 nothing ao ∷ []) refl
... | mk-split m okC okL with singleton-inv okL
... | mk-single p d cc lok s21 s22 = ⊥-elim (vloadN-inv lok refl)
pres-read sok fok ag ok (vload-shape-val-0 _ i v-M v-N v-sx ao c _ _ _ _ _)
  with decomp ok (admininstr-CONST I32 i ∷ []) (admininstr-VLOAD V128 (just (SHAPEX- v-M v-N v-sx)) ao ∷ []) refl
... | mk-split m okC okL with const-ty okC | singleton-inv okL
... | (p1 , s11 , s12) | mk-single p2 d2 c2 lok s21 s22
  with vloadS-inv lok refl
... | refl , refl
  with rt-sub-unsnoc (rt-sub-trans s12 s21)
... | p1sub , _ =
  push1 p2 (plain _ _ _ _ _ (vconst _ c)) (rt-sub-trans s11 p1sub) s22
pres-read sok fok ag ok (vload-shape-val-1 _ i v-M v-N v-sx ao c _ _ _ _ _)
  with decomp ok (admininstr-CONST I32 i ∷ []) (admininstr-VLOAD V128 (just (SHAPEX- v-M v-N v-sx)) ao ∷ []) refl
... | mk-split m okC okL with const-ty okC | singleton-inv okL
... | (p1 , s11 , s12) | mk-single p2 d2 c2 lok s21 s22
  with vloadS-inv lok refl
... | refl , refl
  with rt-sub-unsnoc (rt-sub-trans s12 s21)
... | p1sub , _ =
  push1 p2 (plain _ _ _ _ _ (vconst _ c)) (rt-sub-trans s11 p1sub) s22
pres-read sok fok ag ok (vload-shape-val-2 _ i v-M v-N v-sx ao c _ _ _ _ _)
  with decomp ok (admininstr-CONST I32 i ∷ []) (admininstr-VLOAD V128 (just (SHAPEX- v-M v-N v-sx)) ao ∷ []) refl
... | mk-split m okC okL with const-ty okC | singleton-inv okL
... | (p1 , s11 , s12) | mk-single p2 d2 c2 lok s21 s22
  with vloadS-inv lok refl
... | refl , refl
  with rt-sub-unsnoc (rt-sub-trans s12 s21)
... | p1sub , _ =
  push1 p2 (plain _ _ _ _ _ (vconst _ c)) (rt-sub-trans s11 p1sub) s22
pres-read sok fok ag ok (vload-shape-val-3 _ i v-M v-N v-sx ao c _ _ _ _ _)
  with decomp ok (admininstr-CONST I32 i ∷ []) (admininstr-VLOAD V128 (just (SHAPEX- v-M v-N v-sx)) ao ∷ []) refl
... | mk-split m okC okL with const-ty okC | singleton-inv okL
... | (p1 , s11 , s12) | mk-single p2 d2 c2 lok s21 s22
  with vloadS-inv lok refl
... | refl , refl
  with rt-sub-unsnoc (rt-sub-trans s12 s21)
... | p1sub , _ =
  push1 p2 (plain _ _ _ _ _ (vconst _ c)) (rt-sub-trans s11 p1sub) s22
pres-read sok fok ag ok (vload-splat-val-0 _ i v-N ao c _ _ _ _ _ _)
  with decomp ok (admininstr-CONST I32 i ∷ []) (admininstr-VLOAD V128 (just (SPLAT v-N)) ao ∷ []) refl
... | mk-split m okC okL with const-ty okC | singleton-inv okL
... | (p1 , s11 , s12) | mk-single p2 d2 c2 lok s21 s22
  with vloadSP-inv lok refl
... | refl , refl
  with rt-sub-unsnoc (rt-sub-trans s12 s21)
... | p1sub , _ =
  push1 p2 (plain _ _ _ _ _ (vconst _ c)) (rt-sub-trans s11 p1sub) s22
pres-read sok fok ag ok (vload-splat-val-1 _ i v-N ao c _ _ _ _ _ _)
  with decomp ok (admininstr-CONST I32 i ∷ []) (admininstr-VLOAD V128 (just (SPLAT v-N)) ao ∷ []) refl
... | mk-split m okC okL with const-ty okC | singleton-inv okL
... | (p1 , s11 , s12) | mk-single p2 d2 c2 lok s21 s22
  with vloadSP-inv lok refl
... | refl , refl
  with rt-sub-unsnoc (rt-sub-trans s12 s21)
... | p1sub , _ =
  push1 p2 (plain _ _ _ _ _ (vconst _ c)) (rt-sub-trans s11 p1sub) s22
pres-read sok fok ag ok (vload-splat-val-2 _ i v-N ao c _ _ _ _ _ _)
  with decomp ok (admininstr-CONST I32 i ∷ []) (admininstr-VLOAD V128 (just (SPLAT v-N)) ao ∷ []) refl
... | mk-split m okC okL with const-ty okC | singleton-inv okL
... | (p1 , s11 , s12) | mk-single p2 d2 c2 lok s21 s22
  with vloadSP-inv lok refl
... | refl , refl
  with rt-sub-unsnoc (rt-sub-trans s12 s21)
... | p1sub , _ =
  push1 p2 (plain _ _ _ _ _ (vconst _ c)) (rt-sub-trans s11 p1sub) s22
pres-read sok fok ag ok (vload-splat-val-3 _ i v-N ao c _ _ _ _ _ _)
  with decomp ok (admininstr-CONST I32 i ∷ []) (admininstr-VLOAD V128 (just (SPLAT v-N)) ao ∷ []) refl
... | mk-split m okC okL with const-ty okC | singleton-inv okL
... | (p1 , s11 , s12) | mk-single p2 d2 c2 lok s21 s22
  with vloadSP-inv lok refl
... | refl , refl
  with rt-sub-unsnoc (rt-sub-trans s12 s21)
... | p1sub , _ =
  push1 p2 (plain _ _ _ _ _ (vconst _ c)) (rt-sub-trans s11 p1sub) s22
pres-read sok fok ag ok (vload-zero-val _ i v-N ao c _ _ _)
  with decomp ok (admininstr-CONST I32 i ∷ []) (admininstr-VLOAD V128 (just (vloadop-ZERO v-N)) ao ∷ []) refl
... | mk-split m okC okL with const-ty okC | singleton-inv okL
... | (p1 , s11 , s12) | mk-single p2 d2 c2 lok s21 s22
  with vloadZ-inv lok refl
... | refl , refl
  with rt-sub-unsnoc (rt-sub-trans s12 s21)
... | p1sub , _ =
  push1 p2 (plain _ _ _ _ _ (vconst _ c)) (rt-sub-trans s11 p1sub) s22
pres-read sok fok ag ok (vload-lane-val-0 _ i c-1 v-N ao j c _ _ _ _ _ _)
  with decomp ok (admininstr-CONST I32 i ∷ [])
        (admininstr-VCONST V128 c-1 ∷ admininstr-VLOAD-LANE V128 (mk-sz v-N) ao j ∷ []) refl
... | mk-split m1 okC1 okR
  with decomp okR (admininstr-VCONST V128 c-1 ∷ []) (admininstr-VLOAD-LANE V128 (mk-sz v-N) ao j ∷ []) refl
... | mk-split m2 okC2 okL
  with const-ty okC1 | vconst-ty okC2 | singleton-inv okL
... | (p1 , s11 , s12) | (p2 , s21 , s22) | mk-single p3 d3 c3 lok ls1 ls2
  with vloadL-inv lok refl
... | refl , refl
  with rt-sub-unsnoc
        (subst (λ l → Resulttype-sub (mk-list (p2 ++ valtype-V128 ∷ [])) (mk-list l))
               (sym (snoc2 p3 valtype-I32 valtype-V128)) (rt-sub-trans s22 ls1))
... | p2sub , _
  with rt-sub-unsnoc (rt-sub-trans s12 (rt-sub-trans s21 p2sub))
... | p1sub , _ =
  push1 p3 (plain _ _ _ _ _ (vconst _ c)) (rt-sub-trans s11 p1sub) ls2
pres-read sok fok ag ok (vload-lane-val-1 _ i c-1 v-N ao j c _ _ _ _ _ _)
  with decomp ok (admininstr-CONST I32 i ∷ [])
        (admininstr-VCONST V128 c-1 ∷ admininstr-VLOAD-LANE V128 (mk-sz v-N) ao j ∷ []) refl
... | mk-split m1 okC1 okR
  with decomp okR (admininstr-VCONST V128 c-1 ∷ []) (admininstr-VLOAD-LANE V128 (mk-sz v-N) ao j ∷ []) refl
... | mk-split m2 okC2 okL
  with const-ty okC1 | vconst-ty okC2 | singleton-inv okL
... | (p1 , s11 , s12) | (p2 , s21 , s22) | mk-single p3 d3 c3 lok ls1 ls2
  with vloadL-inv lok refl
... | refl , refl
  with rt-sub-unsnoc
        (subst (λ l → Resulttype-sub (mk-list (p2 ++ valtype-V128 ∷ [])) (mk-list l))
               (sym (snoc2 p3 valtype-I32 valtype-V128)) (rt-sub-trans s22 ls1))
... | p2sub , _
  with rt-sub-unsnoc (rt-sub-trans s12 (rt-sub-trans s21 p2sub))
... | p1sub , _ =
  push1 p3 (plain _ _ _ _ _ (vconst _ c)) (rt-sub-trans s11 p1sub) ls2
pres-read sok fok ag ok (vload-lane-val-2 _ i c-1 v-N ao j c _ _ _ _ _ _)
  with decomp ok (admininstr-CONST I32 i ∷ [])
        (admininstr-VCONST V128 c-1 ∷ admininstr-VLOAD-LANE V128 (mk-sz v-N) ao j ∷ []) refl
... | mk-split m1 okC1 okR
  with decomp okR (admininstr-VCONST V128 c-1 ∷ []) (admininstr-VLOAD-LANE V128 (mk-sz v-N) ao j ∷ []) refl
... | mk-split m2 okC2 okL
  with const-ty okC1 | vconst-ty okC2 | singleton-inv okL
... | (p1 , s11 , s12) | (p2 , s21 , s22) | mk-single p3 d3 c3 lok ls1 ls2
  with vloadL-inv lok refl
... | refl , refl
  with rt-sub-unsnoc
        (subst (λ l → Resulttype-sub (mk-list (p2 ++ valtype-V128 ∷ [])) (mk-list l))
               (sym (snoc2 p3 valtype-I32 valtype-V128)) (rt-sub-trans s22 ls1))
... | p2sub , _
  with rt-sub-unsnoc (rt-sub-trans s12 (rt-sub-trans s21 p2sub))
... | p1sub , _ =
  push1 p3 (plain _ _ _ _ _ (vconst _ c)) (rt-sub-trans s11 p1sub) ls2
pres-read sok fok ag ok (vload-lane-val-3 _ i c-1 v-N ao j c _ _ _ _ _ _)
  with decomp ok (admininstr-CONST I32 i ∷ [])
        (admininstr-VCONST V128 c-1 ∷ admininstr-VLOAD-LANE V128 (mk-sz v-N) ao j ∷ []) refl
... | mk-split m1 okC1 okR
  with decomp okR (admininstr-VCONST V128 c-1 ∷ []) (admininstr-VLOAD-LANE V128 (mk-sz v-N) ao j ∷ []) refl
... | mk-split m2 okC2 okL
  with const-ty okC1 | vconst-ty okC2 | singleton-inv okL
... | (p1 , s11 , s12) | (p2 , s21 , s22) | mk-single p3 d3 c3 lok ls1 ls2
  with vloadL-inv lok refl
... | refl , refl
  with rt-sub-unsnoc
        (subst (λ l → Resulttype-sub (mk-list (p2 ++ valtype-V128 ∷ [])) (mk-list l))
               (sym (snoc2 p3 valtype-I32 valtype-V128)) (rt-sub-trans s22 ls1))
... | p2sub , _
  with rt-sub-unsnoc (rt-sub-trans s12 (rt-sub-trans s21 p2sub))
... | p1sub , _ =
  push1 p3 (plain _ _ _ _ _ (vconst _ c)) (rt-sub-trans s11 p1sub) ls2

-- ===== Step-read: trapping reads (store unchanged, reduct [TRAP]) =====
pres-read sok fok ag ok (call-indirect-trap _ _ _ _ _) = trap-ty
pres-read sok fok ag ok (table-get-trap _ _ _ _) = trap-ty
pres-read sok fok ag ok (table-fill-trap _ _ _ _ _ _) = trap-ty
pres-read sok fok ag ok (table-copy-trap _ _ _ _ _ _ _) = trap-ty
pres-read sok fok ag ok (table-init-trap _ _ _ _ _ _ _) = trap-ty
pres-read sok fok ag ok (load-num-trap _ _ _ _ _ _) = trap-ty
pres-read sok fok ag ok (load-pack-trap-0 _ _ _ _ _ _) = trap-ty
pres-read sok fok ag ok (load-pack-trap-1 _ _ _ _ _ _) = trap-ty
pres-read sok fok ag ok (vload-oob _ _ _ _ _) = trap-ty
pres-read sok fok ag ok (vload-shape-oob _ _ _ _ _ _ _) = trap-ty
pres-read sok fok ag ok (vload-splat-oob _ _ _ _ _) = trap-ty
pres-read sok fok ag ok (vload-zero-oob _ _ _ _ _) = trap-ty
pres-read sok fok ag ok (vload-lane-oob _ _ _ _ _ _ _) = trap-ty
pres-read sok fok ag ok (memory-fill-trap _ _ _ _ _) = trap-ty
pres-read sok fok ag ok (memory-copy-trap _ _ _ _ _) = trap-ty
pres-read sok fok ag ok (memory-init-trap _ _ _ _ _ _) = trap-ty

------------------------------------------------------------------------
-- 9c. Preservation over full Step (congruence + state-changing rules).
------------------------------------------------------------------------

-- Store-extension weakening: every store-indexed judgment is monotone
-- under Extend-store.  Most of the mutual induction is routine
-- (global/func externaddrs preserve their type under Extend-globalinst/
-- Extend-funcinst; Ref/Val/Datainst/Eleminst/Frame follow).  It reduces
-- to ONE IRREDUCIBLE CORE that the GENERATED relations cannot express:
--   Externaddr-ok s (MEM a) (MEM mt)  -->  Externaddr-ok s' (MEM a) (MEM mt)
--   (and likewise TABLE) when memory/table has GROWN.  The grown meminst
--   has type PAGE(n',max) with n' >= n, so one needs
--   Memtype-sub (PAGE(n',max)) (PAGE(n,max)), i.e.
--   Limits-sub (mk-limits n' max) (mk-limits n max).  But the generated
--   `Limits-sub` has a SINGLE constructor, defined ONLY for `just`-max
--   limits (mk-limits (mk-uN _)(just (mk-uN _))); for `nothing` max
--   (unbounded memories, which are valid) there is NO constructor, so
--   the subtyping is UNDERIVABLE.  This is a translation deficiency:
--   the SpecTec `Limits_sub` rule set is incomplete for the nothing
--   case.  Until fixed, mem/table externaddr weakening is the minimal
--   irreducible postulate; everything else in weakening is provable
--   from it.  (Kept as the single `instrs-weaken` postulate here rather
--   than expanding the ~300-line derivation around the same core.)
--
-- ** NOW DISCHARGED **: the regenerated `Limits-sub` has `.max`
-- (bounded) and `.eps` (unbounded refl/monotone) constructors, so
-- mem/table externaddr monotonicity is derivable and instrs-weaken is
-- proved end-to-end below.

-- Extend-store index extraction.
applyUpTo-at : ∀ {A : Set} {P : A → Set} (f : ℕ → A) n {a} →
  a < n → All P (applyUpTo f n) → P (f a)
applyUpTo-at f (suc n) {zero}  _        (px ∷ _)   = px
applyUpTo-at f (suc n) {suc a} (s≤s a<) (_  ∷ rest) =
  applyUpTo-at (λ x → f (suc x)) n a< rest

holds-upto-at : ∀ {P : ℕ → Set} n {a} → a < n → holds-upto P n → P a
holds-upto-at n a< h = applyUpTo-at (λ x → x) n a< h

all-map : ∀ {A : Set} {P Q : A → Set} {xs} →
  (∀ {x} → P x → Q x) → All P xs → All Q xs
all-map f [] = []
all-map f (px ∷ p) = f px ∷ all-map f p

pw-mapR : ∀ {A B : Set} {R R' : A → B → Set} {xs ys} →
  (∀ {x y} → R x y → R' x y) → Pointwise R xs ys → Pointwise R' xs ys
pw-mapR f [] = []
pw-mapR f (r ∷ p) = f r ∷ pw-mapR f p

-- Per-instance type/preservation facts.
ext-globalinst-type : ∀ {g g'} → Extend-globalinst g g' →
  globalinst-TYPE g' ≡ globalinst-TYPE g
ext-globalinst-type (mk-Extend-globalinst mu t v v' _) = refl

ext-funcinst-eq : ∀ {g g'} → Extend-funcinst g g' → g' ≡ g
ext-funcinst-eq (mk-Extend-funcinst ft mm fc) = refl

ext-meminst-memtype-sub : ∀ {mi mi'} → Extend-meminst mi mi' →
  Memtype-sub (meminst-TYPE mi') (meminst-TYPE mi)
ext-meminst-memtype-sub (mk-Extend-meminst n (just m) b n' b' n≤n' _) =
  mk-Memtype-sub _ _ (max n' m n (just m) n≤n' (≤-refl ∷ []))
ext-meminst-memtype-sub (mk-Extend-meminst n nothing b n' b' n≤n' _) =
  mk-Memtype-sub _ _ (eps n' n n≤n')

ext-tableinst-tabletype-sub : ∀ {ti ti'} → Extend-tableinst ti ti' →
  Tabletype-sub (tableinst-TYPE ti') (tableinst-TYPE ti)
ext-tableinst-tabletype-sub (mk-Extend-tableinst n (just m) rt refs n' refs' n≤n' _) =
  mk-Tabletype-sub _ _ _ (max n' m n (just m) n≤n' (≤-refl ∷ []))
ext-tableinst-tabletype-sub (mk-Extend-tableinst n nothing rt refs n' refs' n≤n' _) =
  mk-Tabletype-sub _ _ _ (eps n' n n≤n')

-- Extend-store projections at a valid index.
module _ {s s' : store} where
  ext-global : Extend-store s s' → ∀ {a} → a < length (store-GLOBALS s) →
    (a < length (store-GLOBALS s')) ×
    Extend-globalinst ((store-GLOBALS s) [ a ]!) ((store-GLOBALS s') [ a ]!)
  ext-global (mk-Extend-store _ _ g1 g2 g3 m1 m2 m3 t1 t2 t3 f1 f2 f3 d1 d2 d3 e1 e2 e3) h =
    holds-upto-at _ h g2 , holds-upto-at _ h g3

  ext-mem : Extend-store s s' → ∀ {a} → a < length (store-MEMS s) →
    (a < length (store-MEMS s')) ×
    Extend-meminst ((store-MEMS s) [ a ]!) ((store-MEMS s') [ a ]!)
  ext-mem (mk-Extend-store _ _ g1 g2 g3 m1 m2 m3 t1 t2 t3 f1 f2 f3 d1 d2 d3 e1 e2 e3) h =
    holds-upto-at _ h m2 , holds-upto-at _ h m3

  ext-table : Extend-store s s' → ∀ {a} → a < length (store-TABLES s) →
    (a < length (store-TABLES s')) ×
    Extend-tableinst ((store-TABLES s) [ a ]!) ((store-TABLES s') [ a ]!)
  ext-table (mk-Extend-store _ _ g1 g2 g3 m1 m2 m3 t1 t2 t3 f1 f2 f3 d1 d2 d3 e1 e2 e3) h =
    holds-upto-at _ h t2 , holds-upto-at _ h t3

  ext-func : Extend-store s s' → ∀ {a} → a < length (store-FUNCS s) →
    (a < length (store-FUNCS s')) ×
    Extend-funcinst ((store-FUNCS s) [ a ]!) ((store-FUNCS s') [ a ]!)
  ext-func (mk-Extend-store _ _ g1 g2 g3 m1 m2 m3 t1 t2 t3 f1 f2 f3 d1 d2 d3 e1 e2 e3) h =
    holds-upto-at _ h f2 , holds-upto-at _ h f3

  ext-data-lt : Extend-store s s' → ∀ {a} → a < length (store-DATAS s) →
    a < length (store-DATAS s')
  ext-data-lt (mk-Extend-store _ _ g1 g2 g3 m1 m2 m3 t1 t2 t3 f1 f2 f3 d1 d2 d3 e1 e2 e3) h =
    holds-upto-at _ h d2

  ext-elem-lt : Extend-store s s' → ∀ {a} → a < length (store-ELEMS s) →
    a < length (store-ELEMS s')
  ext-elem-lt (mk-Extend-store _ _ g1 g2 g3 m1 m2 m3 t1 t2 t3 f1 f2 f3 d1 d2 d3 e1 e2 e3) h =
    holds-upto-at _ h e2

  ext-elem-ext : Extend-store s s' → ∀ {a} → a < length (store-ELEMS s) →
    Extend-eleminst ((store-ELEMS s) [ a ]!) ((store-ELEMS s') [ a ]!)
  ext-elem-ext (mk-Extend-store _ _ g1 g2 g3 m1 m2 m3 t1 t2 t3 f1 f2 f3 d1 d2 d3 e1 e2 e3) h =
    holds-upto-at _ h e3

-- Externaddr / Ref / Val weakening.
ext-addr-weaken : ∀ {s s' xa xt} → Extend-store s s' →
  Externaddr-ok s xa xt → Externaddr-ok s' xa xt
ext-addr-weaken {s} {s'} ext (Externaddr-ok--global _ a gi a< lk)
  with ext-global ext a<
... | a<' , eg =
  subst (λ gt → Externaddr-ok s' (externaddr-GLOBAL a) (GLOBAL gt))
    (tr≡ (ext-globalinst-type eg) (cong globalinst-TYPE lk))
    (Externaddr-ok--global s' a ((store-GLOBALS s') [ a ]!) a<' refl)
ext-addr-weaken {s} {s'} ext (Externaddr-ok--mem _ a mi a< lk)
  with ext-mem ext a<
... | a<' , em =
  Externaddr-ok--sub s' (externaddr-MEM a) (MEM (meminst-TYPE mi))
    (MEM (meminst-TYPE ((store-MEMS s') [ a ]!)))
    (Externaddr-ok--mem s' a ((store-MEMS s') [ a ]!) a<' refl)
    (Externtype-sub--mem _ _
      (subst (λ mt → Memtype-sub (meminst-TYPE ((store-MEMS s') [ a ]!)) mt)
             (cong meminst-TYPE lk) (ext-meminst-memtype-sub em)))
ext-addr-weaken {s} {s'} ext (Externaddr-ok--table _ a ti a< lk)
  with ext-table ext a<
... | a<' , et =
  Externaddr-ok--sub s' (externaddr-TABLE a) (TABLE (tableinst-TYPE ti))
    (TABLE (tableinst-TYPE ((store-TABLES s') [ a ]!)))
    (Externaddr-ok--table s' a ((store-TABLES s') [ a ]!) a<' refl)
    (Externtype-sub--table _ _
      (subst (λ tt → Tabletype-sub (tableinst-TYPE ((store-TABLES s') [ a ]!)) tt)
             (cong tableinst-TYPE lk) (ext-tableinst-tabletype-sub et)))
ext-addr-weaken {s} {s'} ext (Externaddr-ok--func _ a fi a< lk)
  with ext-func ext a<
... | a<' , ef =
  Externaddr-ok--func s' a fi a<' (tr≡ (ext-funcinst-eq ef) lk)
ext-addr-weaken ext (Externaddr-ok--sub _ xa xt xt' inner subd) =
  Externaddr-ok--sub _ xa xt xt' (ext-addr-weaken ext inner) subd

ext-ref-weaken : ∀ {s s' r rt} → Extend-store s s' → Ref-ok s r rt → Ref-ok s' r rt
ext-ref-weaken ext (null _ rt) = null _ rt
ext-ref-weaken ext (Ref-ok--func _ a extt xa) =
  Ref-ok--func _ a extt (ext-addr-weaken ext xa)
ext-ref-weaken ext (extern _ a) = extern _ a

ext-val-weaken : ∀ {s s' v t} → Extend-store s s' → Val-ok s v t → Val-ok s' v t
ext-val-weaken ext (Val-ok--numtype _ nt c) = Val-ok--numtype _ nt c
ext-val-weaken ext (Val-ok--vectype _ vt c) = Val-ok--vectype _ vt c
ext-val-weaken ext (Val-ok--reftype _ r rt rok) =
  Val-ok--reftype _ r rt (ext-ref-weaken ext rok)

ext-exportinst-weaken : ∀ {s s' xi} → Extend-store s s' →
  Exportinst-ok s xi → Exportinst-ok s' xi
ext-exportinst-weaken ext (mk-Exportinst-ok _ nm xa xt xaok) =
  mk-Exportinst-ok _ nm xa xt (ext-addr-weaken ext xaok)

ext-eleminst-weaken : ∀ {s s' ei ei' et} → Extend-store s s' →
  Extend-eleminst ei ei' → Eleminst-ok s ei et → Eleminst-ok s' ei' et
ext-eleminst-weaken ext (mk-Extend-eleminst rt refs refs' (inj₁ refl)) (mk-Eleminst-ok _ _ _ fr) =
  mk-Eleminst-ok _ rt refs' (all-map (ext-ref-weaken ext) fr)
ext-eleminst-weaken ext (mk-Extend-eleminst rt refs refs' (inj₂ refl)) (mk-Eleminst-ok _ _ _ fr) =
  mk-Eleminst-ok _ rt [] []

weaken-datas : ∀ {s s' das dts} → Extend-store s s' →
  Forall₂ (λ da dt → Datainst-ok s ((store-DATAS s) [ da ]!) dt) das dts →
  Forall₂ (λ da dt → Datainst-ok s' ((store-DATAS s') [ da ]!) dt) das dts
weaken-datas ext [] = []
weaken-datas {s' = s'} {das = da ∷ _} ext (mk-Datainst-ok _ _ ∷ oks) =
  mk-Datainst-ok s' (datainst-BYTES ((store-DATAS s') [ da ]!)) ∷ weaken-datas ext oks

weaken-elems : ∀ {s s' eas ets} → Extend-store s s' →
  Forall (λ ea → ea < length (store-ELEMS s)) eas →
  Forall₂ (λ ea et → Eleminst-ok s ((store-ELEMS s) [ ea ]!) et) eas ets →
  Forall₂ (λ ea et → Eleminst-ok s' ((store-ELEMS s') [ ea ]!) et) eas ets
weaken-elems ext [] [] = []
weaken-elems ext (b ∷ bs) (ok ∷ oks) =
  ext-eleminst-weaken ext (ext-elem-ext ext b) ok ∷ weaken-elems ext bs oks

-- Moduleinst / Frame weakening.
wk-moduleinst : ∀ {s s' mm C} → Extend-store s s' →
  Moduleinst-ok s mm C → Moduleinst-ok s' mm C
wk-moduleinst {s' = s'} ext
  (mk-Moduleinst-ok _ fnl fal gal tal mal eal dal xil fFl gtl ttl mtl etl dtl
    p1 l1 a1 l2 a2 l3 a3 l4 a4 x1 l5 b1 di l6 b2 ei d1 g1 x2) =
  mk-Moduleinst-ok s' fnl fal gal tal mal eal dal xil fFl gtl ttl mtl etl dtl
    p1 l1 (pw-mapR (ext-addr-weaken ext) a1)
    l2 (pw-mapR (ext-addr-weaken ext) a2)
    l3 (pw-mapR (ext-addr-weaken ext) a3)
    l4 (pw-mapR (ext-addr-weaken ext) a4)
    (all-map (ext-exportinst-weaken ext) x1)
    l5 (all-map (ext-data-lt ext) b1) (weaken-datas ext di)
    l6 (all-map (ext-elem-lt ext) b2) (weaken-elems ext b2 ei)
    d1 g1 x2

wk-frame : ∀ {s s' f C} → Extend-store s s' → Frame-ok s f C → Frame-ok s' f C
wk-frame ext (mk-Frame-ok _ vals mm C ts mok len vok) =
  mk-Frame-ok _ vals mm C ts (wk-moduleinst ext mok) len (pw-mapR (ext-val-weaken ext) vok)

-- Admin-instruction typing weakening (mutual).
mutual
  wk-instr2 : ∀ {s s' C e ft} → Extend-store s s' → Instr-ok2 s C e ft → Instr-ok2 s' C e ft
  wk-instr2 ext (plain _ C i t1 t2 iok) = plain _ C i t1 t2 iok
  wk-instr2 ext (label _ C vn cont body t t' len ct bt) =
    label _ C vn cont body t t' len (wk-instrs2 ext ct) (wk-instrs2 ext bt)
  wk-instr2 ext (Instr-ok2--frame _ C vn f body t C' len frok exok) =
    Instr-ok2--frame _ C vn f body t C' len (wk-frame ext frok) (wk-expr2 ext exok)
  wk-instr2 ext (Instr-ok2--call-addr _ C fa t1 t2 xa) =
    Instr-ok2--call-addr _ C fa t1 t2 (ext-addr-weaken ext xa)
  wk-instr2 ext (Instr-ok2--ref _ C r rt rok) =
    Instr-ok2--ref _ C r rt (ext-ref-weaken ext rok)
  wk-instr2 ext (Instr-ok2--trap _ C t1 t2) = Instr-ok2--trap _ C t1 t2

  wk-instrs2 : ∀ {s s' C es ft} → Extend-store s s' → Instrs-ok2 s C es ft → Instrs-ok2 s' C es ft
  wk-instrs2 ext (Instrs-ok2--empty _ C) = Instrs-ok2--empty _ C
  wk-instrs2 ext (Instrs-ok2--instr _ C e t1 t2 iok) =
    Instrs-ok2--instr _ C e t1 t2 (wk-instr2 ext iok)
  wk-instrs2 ext (Instrs-ok2--seq _ C l1 l2 t1 t3 t2 d1 d2) =
    Instrs-ok2--seq _ C l1 l2 t1 t3 t2 (wk-instrs2 ext d1) (wk-instrs2 ext d2)
  wk-instrs2 ext (Instrs-ok2--sub _ C es t1' t2' t1 t2 d r1 r2) =
    Instrs-ok2--sub _ C es t1' t2' t1 t2 (wk-instrs2 ext d) r1 r2
  wk-instrs2 ext (Instrs-ok2--frame _ C es ts t1 t2 d) =
    Instrs-ok2--frame _ C es ts t1 t2 (wk-instrs2 ext d)

  wk-expr2 : ∀ {s s' C es rt} → Extend-store s s' → Expr-ok2 s C es rt → Expr-ok2 s' C es rt
  wk-expr2 ext (mk-Expr-ok2 _ C es ts d) = mk-Expr-ok2 _ C es ts (wk-instrs2 ext d)

instrs-weaken : ∀ {s s' C es ft} → Extend-store s s' → Store-ok s' →
  Instrs-ok2 s C es ft → Instrs-ok2 s' C es ft
instrs-weaken ext _ = wk-instrs2 ext

------------------------------------------------------------------------
-- 9c-pre. Store-update machinery: Store-ok is preserved by a single-slot
--   store write (with-global / with-table / with-mem / with-elem /
--   with-data / grow).  Built on instrs-weaken's component weakenings.
------------------------------------------------------------------------

-- Component inst-ok weakening under Extend-store.
wk-globalinst : ∀ {s s' gi gt} → Extend-store s s' → Globalinst-ok s gi gt → Globalinst-ok s' gi gt
wk-globalinst ext (mk-Globalinst-ok _ mu t v gtok vok) =
  mk-Globalinst-ok _ mu t v gtok (ext-val-weaken ext vok)

wk-meminst : ∀ {s s' mi mt} → Extend-store s s' → Meminst-ok s mi mt → Meminst-ok s' mi mt
wk-meminst ext (mk-Meminst-ok _ n mo b mtok leneq) = mk-Meminst-ok _ n mo b mtok leneq

wk-tableinst : ∀ {s s' ti tt} → Extend-store s s' → Tableinst-ok s ti tt → Tableinst-ok s' ti tt
wk-tableinst ext (mk-Tableinst-ok _ n mo rt refs ttok fr leneq) =
  mk-Tableinst-ok _ n mo rt refs ttok (all-map (ext-ref-weaken ext) fr) leneq

wk-funcinst : ∀ {s s' fi ft} → Extend-store s s' → Funcinst-ok s fi ft → Funcinst-ok s' fi ft
wk-funcinst ext (mk-Funcinst-ok _ ft mm fc C ftok mok fk) =
  mk-Funcinst-ok _ ft mm fc C ftok (wk-moduleinst ext mok) fk

wk-datainst : ∀ {s s' di dt} → Extend-store s s' → Datainst-ok s di dt → Datainst-ok s' di dt
wk-datainst ext (mk-Datainst-ok _ b) = mk-Datainst-ok _ b

wk-eleminst : ∀ {s s' ei et} → Extend-store s s' → Eleminst-ok s ei et → Eleminst-ok s' ei et
wk-eleminst ext (mk-Eleminst-ok _ rt refs fr) =
  mk-Eleminst-ok _ rt refs (all-map (ext-ref-weaken ext) fr)

-- modify lookup.
modify-neq : ∀ {A : Set} {{_ : Inhabited A}} (xs : List A) a f {i} →
  i < length xs → i ≢ a → (modify xs a f [ i ]!) ≡ (xs [ i ]!)
modify-neq (x ∷ xs) zero    f {zero}  _        i≢a = ⊥-elim (i≢a refl)
modify-neq (x ∷ xs) zero    f {suc i} _        _   = refl
modify-neq (x ∷ xs) (suc a) f {zero}  _        _   = refl
modify-neq (x ∷ xs) (suc a) f {suc i} (s≤s i<) i≢a =
  modify-neq xs a f i< (λ e → i≢a (cong suc e))

modify-eq : ∀ {A : Set} {{_ : Inhabited A}} (xs : List A) a f →
  a < length xs → (modify xs a f [ a ]!) ≡ f (xs [ a ]!)
modify-eq (x ∷ xs) zero    f _        = refl
modify-eq (x ∷ xs) (suc a) f (s≤s a<) = modify-eq xs a f a<

-- Pointwise update: rebuild a Pointwise after modifying the left list at
-- one index (others weakened, the touched slot re-established).
pw-modify : ∀ {A B : Set} {{_ : Inhabited A}} {{_ : Inhabited B}} {P P' : A → B → Set} {xs ys}
  (a : ℕ) (f : A → A) → (∀ {x y} → P x y → P' x y) → Pointwise P xs ys →
  (a < length xs → P' (f (xs [ a ]!)) (ys [ a ]!)) →
  Pointwise P' (modify xs a f) ys
pw-modify a f wk [] upd = []
pw-modify zero f wk (r ∷ p) upd = upd (s≤s z≤n) ∷ pw-mapR wk p
pw-modify (suc a) f wk (r ∷ p) upd = wk r ∷ pw-modify a f wk p (λ a< → upd (s≤s a<))

pw-modify-both : ∀ {A B : Set} {{_ : Inhabited A}} {{_ : Inhabited B}}
  {P P' : A → B → Set} {xs ys} (a : ℕ) (fa : A → A) (fb : B → B) →
  (∀ {x y} → P x y → P' x y) → Pointwise P xs ys →
  (a < length xs → P' (fa (xs [ a ]!)) (fb (ys [ a ]!))) →
  Pointwise P' (modify xs a fa) (modify ys a fb)
pw-modify-both a fa fb wk [] upd = []
pw-modify-both zero fa fb wk (r ∷ p) upd = upd (s≤s z≤n) ∷ pw-mapR wk p
pw-modify-both (suc a) fa fb wk (r ∷ p) upd = wk r ∷ pw-modify-both a fa fb wk p (λ a< → upd (s≤s a<))

all-modify : ∀ {A : Set} {{_ : Inhabited A}} {P P' : A → Set} {xs}
  (a : ℕ) (f : A → A) → (∀ {x} → P x → P' x) → All P xs →
  (a < length xs → P' (f (xs [ a ]!))) → All P' (modify xs a f)
all-modify a f wk [] upd = []
all-modify zero f wk (px ∷ p) upd = upd (s≤s z≤n) ∷ all-map wk p
all-modify (suc a) f wk (px ∷ p) upd = wk px ∷ all-modify a f wk p (λ a< → upd (s≤s a<))

-- Extend-store witness for a mutable-global VALUE update.
extend-set-global : ∀ (s : store) (a : ℕ) (t : valtype) (v : val) →
  (a< : a < length (store-GLOBALS s)) →
  globalinst-TYPE ((store-GLOBALS s) [ a ]!) ≡ mk-globaltype (just MUT) t →
  Extend-store s
    (record s { store-GLOBALS =
      modify (store-GLOBALS s) a (λ gi → record gi { VALUE = v }) })
extend-set-global s a t v a< tyeq =
  mk-Extend-store s _
    (all-upto _ (λ i i< → i<))
    (all-upto _ (λ i i< → subst (i <_)
       (sym (modify-length (store-GLOBALS s) a _)) i<))
    (all-upto _ gext)
    (all-upto _ (λ i i< → i<)) (all-upto _ (λ i i< → i<))
    (all-upto _ (λ i i< → ext-m-refl _))
    (all-upto _ (λ i i< → i<)) (all-upto _ (λ i i< → i<))
    (all-upto _ (λ i i< → ext-t-refl _))
    (all-upto _ (λ i i< → i<)) (all-upto _ (λ i i< → i<))
    (all-upto _ (λ i i< → ext-f-refl _))
    (all-upto _ (λ i i< → i<)) (all-upto _ (λ i i< → i<))
    (all-upto _ (λ i i< → ext-d-refl _))
    (all-upto _ (λ i i< → i<)) (all-upto _ (λ i i< → i<))
    (all-upto _ (λ i i< → ext-e-refl _))
  where
  G = store-GLOBALS s
  upd = λ (gi : globalinst) → record gi { VALUE = v }
  gext : ∀ i → i < length G → Extend-globalinst (G [ i ]!) (modify G a upd [ i ]!)
  gext i i< with i ≟ a
  ... | yes refl =
    let g = G [ a ]!
        geq : g ≡ record { globalinst-TYPE = mk-globaltype (just MUT) t ; VALUE = VALUE g }
        geq = cong (λ ty → record { globalinst-TYPE = ty ; VALUE = VALUE g }) tyeq
        base : Extend-globalinst g (record g { VALUE = v })
        base = subst (λ gg → Extend-globalinst gg (record gg { VALUE = v })) (sym geq)
                 (mk-Extend-globalinst (just MUT) t (VALUE g) v (inj₁ refl))
    in subst (λ z → Extend-globalinst g z) (sym (modify-eq G a upd a<)) base
  ... | no i≢a =
    subst (λ z → Extend-globalinst (G [ i ]!) z)
      (sym (modify-neq G a upd i< i≢a)) (ext-g-refl (G [ i ]!))

-- The touched global slot is re-typeable at its (unchanged) type with
-- the new value.
glob-slot-ok : ∀ {s gg gt t} → Globalinst-ok s gg gt →
  globalinst-TYPE gg ≡ mk-globaltype (just MUT) t →
  ∀ {s'} (v : val) → Val-ok s' v t →
  Globalinst-ok s' (record gg { VALUE = v }) gt
glob-slot-ok (mk-Globalinst-ok _ mu t' ov gtok ovok) refl v vok' =
  mk-Globalinst-ok _ (just MUT) t' v gtok vok'

-- Store-ok preserved by a mutable-global VALUE update.
store-ok-set-global : ∀ (s : store) (a : ℕ) (t : valtype) (v : val) →
  (a< : a < length (store-GLOBALS s)) →
  globalinst-TYPE ((store-GLOBALS s) [ a ]!) ≡ mk-globaltype (just MUT) t →
  Store-ok s →
  Val-ok (record s { store-GLOBALS =
            modify (store-GLOBALS s) a (λ gi → record gi { VALUE = v }) }) v t →
  Store-ok
    (record s { store-GLOBALS =
      modify (store-GLOBALS s) a (λ gi → record gi { VALUE = v }) })
store-ok-set-global s a t v a< tyeq
  (mk-Store-ok _ gil gtl mil mtl til ttl fil ftl dil dtl eil etl
     glen gok mlen mok tlen tok flen fok dlen dok elen eok seqEq) vok'
  with extend-set-global s a t v a< tyeq
... | ext =
  mk-Store-ok _
    (modify (store-GLOBALS s) a upd) gtl mil mtl til ttl fil ftl dil dtl eil etl
    (tr≡ (modify-length (store-GLOBALS s) a upd)
         (subst (λ l → length l ≡ length gtl) (sym gil≡) glen))
    (pw-modify a upd (wk-globalinst ext) gok'
      (λ a<' → glob-slot-ok (pw-lookup gok' a<') tyeq v vok'))
    mlen (pw-mapR (wk-meminst ext) mok)
    tlen (pw-mapR (wk-tableinst ext) tok)
    flen (pw-mapR (wk-funcinst ext) fok)
    dlen (pw-mapR (wk-datainst ext) dok)
    elen (pw-mapR (wk-eleminst ext) eok)
    (cong (λ ss → record ss { store-GLOBALS = modify (store-GLOBALS s) a upd }) seqEq)
  where
  upd = λ (gi : globalinst) → record gi { VALUE = v }
  gil≡ : store-GLOBALS s ≡ gil
  gil≡ = cong store-GLOBALS seqEq
  gok' : Pointwise (λ gi gt → Globalinst-ok s gi gt) (store-GLOBALS s) gtl
  gok' = subst (λ l → Pointwise (λ gi gt → Globalinst-ok s gi gt) l gtl) (sym gil≡) gok

------------------------------------------------------------------------
-- Axioms about builtin byte serialization.
-- ibytes-/nbytes-/vbytes- are `hint(builtin)` in the spec: abstract
-- serialization primitives.  Their byte-length is an INHERENT AXIOM
-- about an unspecified primitive (no mechanization can derive it).
------------------------------------------------------------------------
postulate
  -- |serialization of an N-bit int| = N/8 bytes.
  ibytes-length : ∀ (N : ℕ) (c : uN-fam0 N) → length (ibytes- N c) ≡ N / 8
  -- |serialization of a numeric value of type nt| = size(nt)/8 bytes.
  nbytes-length : ∀ (nt : numtype) (c : num- nt) →
    length (nbytes- nt c) ≡ (unwrap! (size (valtype-numtype nt))) / 8
  -- |serialization of a v128| = size(v128)/8 bytes.
  vbytes-length : ∀ (vt : vectype) (c : uN-fam0 (unwrap! (size (valtype-vectype vt)))) →
    length (vbytes- vt c) ≡ (unwrap! (size (valtype-vectype vt))) / 8
  -- DEserialization: the byte-serializers are surjective onto byte strings of the
  -- serialization length (host-abstract inverse of the *-length axioms above; used
  -- by loads to exhibit the loaded value from the in-bounds memory slice).
  nbytes-surj : ∀ (nt : numtype) (bs : List byte) →
    length bs ≡ (unwrap! (size (valtype-numtype nt))) / 8 →
    Σ (num- nt) λ c → nbytes- nt c ≡ bs
  ibytes-surj : ∀ (N : ℕ) (bs : List byte) →
    length bs ≡ N / 8 → Σ (uN-fam0 N) λ c → ibytes- N c ≡ bs
  vbytes-surj : ∀ (vt : vectype) (bs : List byte) →
    length bs ≡ (unwrap! (size (valtype-vectype vt))) / 8 →
    Σ (uN-fam0 (unwrap! (size (valtype-vectype vt)))) λ c → vbytes- vt c ≡ bs
  -- Bit-serialization round-trip (host-abstract, hint(builtin); the spec postulates
  -- both ibits- and its declared inverse inv-ibits- but not the inversion law).
  -- Used by v128.bitmask to exhibit the mask integer from its bit string.
  ibits-inv : ∀ (N : ℕ) (bits : List bit) → length bits ≡ N → ibits- N (inv-ibits- N bits) ≡ bits
  -- Host-abstract SIMD lane split (hint(builtin), inverse inv-lanes- also builtin);
  -- the N-lane-shape ⇒ N-lanes length law is not derivable.  Shared across lane SIMD ops.
  lanes-length : ∀ (lt : lanetype) (N : ℕ) (c : uN-fam0 128) →
    length (lanes- (X lt (mk-dim N)) c) ≡ N

------------------------------------------------------------------------
-- Axioms: grow* postconditions.
-- growtable/growmemory are DEFINED in the spec but the backend currently
-- postulates the definitions (recorded backend limitation); these are
-- their postconditions: a successful grow yields a well-typed instance
-- whose type is a supertype (more pages/slots) of the old one.
------------------------------------------------------------------------
postulate
  growmemory-ok : ∀ (s : store) (mi mi' : meminst) (n : ℕ) →
    growmemory mi n ≡ just mi' →
    Extend-meminst mi mi' × Meminst-ok s mi' (meminst-TYPE mi')
  growtable-ok : ∀ (s : store) (ti ti' : tableinst) (n : ℕ) (r : ref) →
    growtable ti n r ≡ just ti' →
    Extend-tableinst ti ti' × Tableinst-ok s ti' (tableinst-TYPE ti')

-- BACKEND-LIMITATION axiom (deletable, NOT host-abstract).  The source has
--   syntax dim = `1 | `2 | `4 | `8 | `16   (a bounded enumeration, max 16),
-- but the backend flattens it to `mk-dim : (i : ℕ) → dim {- 1 premise(s) dropped -}`,
-- i.e. unconstrained ℕ, dropping the membership premise.  This axiom recovers
-- the intrinsic bound (needed by v128.bitmask, whose 32-bit mask requires the
-- lane count ≤ 32).  DELETABLE once `dim` is rendered as a bounded enumeration.
postulate
  dim-bound : ∀ (d : dim) → proj-dim-0 d ≤ 16

-- BACKEND-LIMITATION (flattening) axiom, same class as dim-bound.
-- Source syntax has two DISTINCT instructions: `nt.extract_lane` (numeric shape, no sx)
-- and `pt.extract_lane_sx` (packed shape, with sx).  The Agda backend flattens both into
-- one head `VEXTRACT-LANE shape (Maybe sx) laneidx`, and the generated typing rule
-- (Instr_ok/vextract_lane) is GENERIC in `sx?` — it no longer records that sx? is present
-- iff the shape is packed.  The reduction, however, keeps the split (num rule requires
-- sx? = nothing, pack rule requires sx? = just), so ill-formed-but-typeable terms like
-- `VEXTRACT_LANE (I32 X 4) sx l` have no step.  This axiom recovers the lost syntactic
-- invariant; it is TRUE of the real language and deletable once the backend emits the
-- shape/sx? correlation into the typing rule.
data VExtractWF : shape → Maybe sx → Set where
  vewf-i32 : ∀ {N} → VExtractWF (X lanetype-I32 (mk-dim N)) nothing
  vewf-i64 : ∀ {N} → VExtractWF (X lanetype-I64 (mk-dim N)) nothing
  vewf-f32 : ∀ {N} → VExtractWF (X lanetype-F32 (mk-dim N)) nothing
  vewf-f64 : ∀ {N} → VExtractWF (X lanetype-F64 (mk-dim N)) nothing
  vewf-i8  : ∀ {N s} → VExtractWF (X lanetype-I8 (mk-dim N)) (just s)
  vewf-i16 : ∀ {N s} → VExtractWF (X lanetype-I16 (mk-dim N)) (just s)

postulate
  vextract-lane-wf : ∀ {s C e sh sxo i d c} →
    Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) → e ≡ admininstr-VEXTRACT-LANE sh sxo i →
    VExtractWF sh sxo

-- BACKEND-LIMITATION (⊤-completed partial family) axiom, same class as dim-bound.
-- `VTESTOP` takes a general `shape`, and the op-family `vtestop- sh` is ⊤-completed to `⊤`
-- for float shapes (only the four integer Jnn shapes have a real op).  So `VTESTOP (F32 X 4) tt`
-- is vacuously typeable (op = tt : ⊤) but the reduction only fires for integer shapes — it is
-- typeable-but-stuck junk.  This axiom recovers the invariant that a well-typed VTESTOP has an
-- integer shape; it is TRUE of the real language and deletable once the backend ⊤-completes
-- invalid slots to ⊥ instead.
data VTestopWF : shape → Set where
  vtwf-i32 : ∀ {N} → VTestopWF (X lanetype-I32 (mk-dim N))
  vtwf-i64 : ∀ {N} → VTestopWF (X lanetype-I64 (mk-dim N))
  vtwf-i8  : ∀ {N} → VTestopWF (X lanetype-I8 (mk-dim N))
  vtwf-i16 : ∀ {N} → VTestopWF (X lanetype-I16 (mk-dim N))

postulate
  vtestop-int-shape : ∀ {s C e sh op d c} →
    Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) → e ≡ admininstr-VTESTOP sh op →
    VTestopWF sh

-- BACKEND-LIMITATION (dropped constructor premise) axiom, dim-bound class.
-- `uN-fam0 N = mk-uN (i : ℕ) {- 1 premise(s) dropped -}` (wasm2-sound-check.agda:365):
-- the source refinement `i < 2^N` on the numeral was dropped, so `proj-uN-0 N` is unbounded.
-- Needed wherever a runtime numeral must be shown in range (e.g. vswizzle's byte lane indices,
-- which are the 2nd operand's lanes, not typing-bounded).  TRUE of the real language;
-- deletable once uN is emitted as a bounded (Fin-like) type.
postulate
  uN-bound : ∀ (N : ℕ) (x : uN-fam0 N) → proj-uN-0 N x < 2 ^ N

-- BACKEND-LIMITATION (typing generic over a type whose reduction is narrower / merged variant),
-- vtestop-int-shape class.  Source typing `Instr_ok/vswizzle`, `Instr_ok/vshuffle`
-- (6-typing.spectec:336-341) are generic in `sh : ishape`, but the ONLY constructible swizzle/shuffle
-- in the binary format is the I8 shape (A-binary.spectec:510 `VSWIZZLE (I8 X 16)`, :489
-- `VSHUFFLE (I8 X 16) l^16`).  The reduction is written generic in `Pnn` (8-reduction.spectec:304,312)
-- with a hardcoded 256 = 2^8 index table, so the I16 instance is unsound (16-bit indices overflow the
-- table) and every non-I8 shape is typeable-but-stuck.  This axiom recovers the real syntactic
-- restriction (swizzle/shuffle are i8x16-only); deletable once the backend records it in the typing.
data VPackedShapeWF : ishape → Set where
  vpsh-i8  : ∀ {N} → VPackedShapeWF (ishape-X Jnn-I8 (mk-dim N))

postulate
  vswizzle-packed : ∀ {s C e sh d c} →
    Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) → e ≡ admininstr-VSWIZZLE sh → VPackedShapeWF sh
  vshuffle-packed : ∀ {s C e sh ls d c} →
    Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) → e ≡ admininstr-VSHUFFLE sh ls → VPackedShapeWF sh

-- BACKEND-LIMITATION (dropped constructor premise) axiom, dim-bound class.
-- Binary format `VSHUFFLE (I8 X 16) l^16` (A-binary.spectec:489) fixes the shuffle immediate to
-- EXACTLY dim(sh) lane indices, but the abstract syntax `VSHUFFLE ishape laneidx*`
-- (1-syntax.spectec:454, marked `{- 1 premise(s) dropped -}`) drops the length constraint.
-- TRUE of the real language; deletable once the backend emits `|i*| = dim`.
postulate
  vshuffle-lanecount : ∀ {s C e sh ls d c} →
    Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) → e ≡ admininstr-VSHUFFLE sh ls →
    length ls ≡ coerce {B = ℕ} (fun-dim (shape-ishape sh))

-- BACKEND-LIMITATION (typing premise-free over an op/shape space whose reduction is partial), G3.
-- Source typing `Instr_ok/vcvtop` (6-typing.spectec:364) is generic: `C |- VCVTOP sh1 sh2 op : V128->V128`
-- with NO validity premise.  But `vcvtop--` (3-numerics) has a catch-all `= []` (line 2467), so invalid
-- (shape,op) conversion combos are typeable-but-stuck (the rules have no trap alternative, they require
-- `length > 0`).  This root axiom recovers the real invariant: a well-typed conversion's per-lane map is
-- DEFINED (non-empty).  From it, result-set non-emptiness is DERIVED (not axiomatized) via sp-cons.
-- TRUE of the real language (binary emits only valid vcvtop opcodes); deletable once the typing carries
-- the op/shape validity premise.  vcvtop-- arg order is (source, target) = (sh2, sh1) of the instruction.
postulate
  vcvtop-lane-def : ∀ {s C e sh1 sh2 op d cc} →
    Instr-ok2 s C e (mk-functype (mk-list d) (mk-list cc)) → e ≡ admininstr-VCVTOP sh1 sh2 op →
    ∀ (ci : lane- (fun-lanetype sh2)) → vcvtop-- sh2 sh1 op ci ≢ []

-- BACKEND-LIMITATION (same class, facet 2: full-conversion lane-count preservation).
-- `vcvtop-full` (8-reduction, generated 4091) fixes BOTH shapes to the same `mk-dim v-M`, but the generic
-- typing (6-typing.spectec:364) allows independent dims, so a full-type op (halfop=zeroop=nothing) on
-- mismatched dims is typeable-but-stuck.  TRUE of the real language (lane-preserving conversions keep the
-- lane count); deletable once the typing records dim(sh1)=dim(sh2) for full conversions.
postulate
  vcvtop-full-dim : ∀ {s C e Lnn2 Lnn1 M2 M1 op d cc} →
    Instr-ok2 s C e (mk-functype (mk-list d) (mk-list cc)) →
    e ≡ admininstr-VCVTOP (X Lnn2 (mk-dim M2)) (X Lnn1 (mk-dim M1)) op →
    halfop op ≡ nothing → zeroop op ≡ nothing → M1 ≡ M2

-- BACKEND-LIMITATION (same class, facet 3: zero-conversion numeric-shape restriction), G3.
-- `vcvtop-zero-0..15` (generated 4105-4210) cover only numtype² lanetypes (I32/I64/F32/F64), but the
-- generic typing (6-typing.spectec:364) allows packtype (I8/I16) shapes, which are then typeable-but-stuck
-- for a zeroop conversion.  TRUE of the real language (zero conversions are numeric); deletable once the
-- typing records the numeric-shape restriction for zeroop conversions.
data NumLnn : Lnn → Set where
  nl-i32 : NumLnn lanetype-I32
  nl-i64 : NumLnn lanetype-I64
  nl-f32 : NumLnn lanetype-F32
  nl-f64 : NumLnn lanetype-F64

postulate
  vcvtop-zero-num : ∀ {s C e Lnn2 Lnn1 M2 M1 op d cc} →
    Instr-ok2 s C e (mk-functype (mk-list d) (mk-list cc)) →
    e ≡ admininstr-VCVTOP (X Lnn2 (mk-dim M2)) (X Lnn1 (mk-dim M1)) op →
    zeroop op ≡ just ZERO → NumLnn Lnn1 × NumLnn Lnn2

cprime-len : ∀ {A : Set} (xs : List A) (z : A) (M : ℕ) →
  length xs ≡ M → M ≤ 256 → length (xs ++ replicate (256 ∸ M) z) ≡ 256
cprime-len xs z M lenxs M≤ =
  tr≡ (length-++ xs)
    (tr≡ (cong₂ _+_ lenxs (length-replicate (256 ∸ M))) (m+[n∸m]≡n M≤))

-- Total indexing respects a pointwise property, given the index is in range.
all-index! : ∀ {A : Set} {{_ : Inhabited A}} {P : A → Set} (xs : List A) (k : ℕ) →
  k < length xs → All P xs → P (xs [ k ]!)
all-index! [] k () _
all-index! (x ∷ xs) zero    _        (px ∷ _)   = px
all-index! (x ∷ xs) (suc k) (s≤s k<) (_  ∷ pxs) = all-index! xs k k< pxs

-- v128.shuffle helper: the concatenated table lanes-c1 ++ lanes-c2 has length 2*N.
cshuf-len : ∀ (c1 c2 : uN-fam0 128) (lt : lanetype) (N : ℕ) →
  length (lanes- (X lt (mk-dim N)) c1 ++ lanes- (X lt (mk-dim N)) c2) ≡ 2 * N
cshuf-len c1 c2 lt N =
  tr≡ (length-++ (lanes- (X lt (mk-dim N)) c1))
    (tr≡ (cong₂ _+_ (lanes-length lt N c1) (lanes-length lt N c2))
         (cong (N +_) (sym (+-identityʳ N))))

-- vcvtop non-emptiness (DERIVED, not axiomatized): setproduct- of non-empty lists is a cons.
sp-cons : ∀ {X : Set} (yss : List (List X)) → All (λ ys → ys ≢ []) yss →
  Σ (List X) λ h → Σ (List (List X)) λ t → setproduct- X yss ≡ h ∷ t
sp-cons [] _ = [] , [] , refl
sp-cons (y ∷ ys) (y≢[] ∷ allys) with sp-cons ys allys | y
... | h' , t' , eq | []       = ⊥-elim (y≢[] refl)
... | h' , t' , eq | (w ∷ ws) rewrite eq = _ , _ , refl

-- Given every per-lane result is non-empty, the mapped setproduct result is non-empty:
-- extract the witness value, the length>0, and its membership (what the vcvtop rules require).
vcvtop-fire : ∀ {X B : Set} (g : List X → B) (yss : List (List X)) →
  All (λ ys → ys ≢ []) yss →
  Σ B λ c → (length (map g (setproduct- X yss)) > 0) × (c ∈ map g (setproduct- X yss))
vcvtop-fire g yss allne with sp-cons yss allne
... | h , t , eq rewrite eq = g h , s≤s z≤n , here refl

-- vcvtop full/zero extracted so vcvtop-step's cases are all leaves (no with-returns).
vcvtop-full-step : ∀ {s C Lnn2 Lnn1 M2 M1 op d cc} (c-1 : uN-fam0 128) →
  Instr-ok2 s C (admininstr-VCVTOP (X Lnn2 (mk-dim M2)) (X Lnn1 (mk-dim M1)) op) (mk-functype (mk-list d) (mk-list cc)) → halfop op ≡ nothing → zeroop op ≡ nothing →
  Σ (List admininstr) λ res →
    Step-pure (admininstr-VCONST V128 c-1 ∷ admininstr-VCVTOP (X Lnn2 (mk-dim M2)) (X Lnn1 (mk-dim M1)) op ∷ []) res
vcvtop-full-step {Lnn2 = Lnn2} {Lnn1 = Lnn1} {M2 = M2} {M1 = M1} {op = op} c-1 e-iok heq zeq with vcvtop-full-dim e-iok refl heq zeq
... | refl =
      let r = vcvtop-fire (λ cj → inv-lanes- (X Lnn2 (mk-dim M2)) cj)
                (map (λ x → vcvtop-- (X Lnn1 (mk-dim M2)) (X Lnn2 (mk-dim M2)) op x) (lanes- (X Lnn1 (mk-dim M2)) c-1))
                (map⁺ (universal (λ x → vcvtop-lane-def e-iok refl x) (lanes- (X Lnn1 (mk-dim M2)) c-1)))
      in _ , vcvtop-full c-1 Lnn2 M2 Lnn1 op (proj₁ r) _ _ (heq , zeq) refl refl (proj₁ (proj₂ r)) (proj₂ (proj₂ r))

vcvtop-zero-step : ∀ {s C Lnn2 Lnn1 M2 M1 op d cc} (c-1 : uN-fam0 128) →
  Instr-ok2 s C (admininstr-VCVTOP (X Lnn2 (mk-dim M2)) (X Lnn1 (mk-dim M1)) op) (mk-functype (mk-list d) (mk-list cc)) → zeroop op ≡ just ZERO →
  Σ (List admininstr) λ res →
    Step-pure (admininstr-VCONST V128 c-1 ∷ admininstr-VCVTOP (X Lnn2 (mk-dim M2)) (X Lnn1 (mk-dim M1)) op ∷ []) res
vcvtop-zero-step {Lnn2 = Lnn2} {Lnn1 = Lnn1} {M2 = M2} {M1 = M1} {op = op} c-1 e-iok zeq with vcvtop-zero-num e-iok refl zeq
... | nl1 , nl2 with nl1 | nl2
...   | nl-i32 | nl-i32 =
        let r = vcvtop-fire (λ cj → inv-lanes- (X lanetype-I32 (mk-dim M2)) cj) (map (λ x → vcvtop-- (X lanetype-I32 (mk-dim M1)) (X lanetype-I32 (mk-dim M2)) op x) (lanes- (X lanetype-I32 (mk-dim M1)) c-1) ++ replicate M1 ((fun-zero I32) ∷ [])) (++⁺ (map⁺ (universal (λ x → vcvtop-lane-def e-iok refl x) (lanes- (X lanetype-I32 (mk-dim M1)) c-1))) (replicate⁺ M1 (λ ())))
        in _ , vcvtop-zero-0 c-1 M2 M1 op (proj₁ r) _ _ zeq refl refl (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
...   | nl-i32 | nl-i64 =
        let r = vcvtop-fire (λ cj → inv-lanes- (X lanetype-I64 (mk-dim M2)) cj) (map (λ x → vcvtop-- (X lanetype-I32 (mk-dim M1)) (X lanetype-I64 (mk-dim M2)) op x) (lanes- (X lanetype-I32 (mk-dim M1)) c-1) ++ replicate M1 ((fun-zero I64) ∷ [])) (++⁺ (map⁺ (universal (λ x → vcvtop-lane-def e-iok refl x) (lanes- (X lanetype-I32 (mk-dim M1)) c-1))) (replicate⁺ M1 (λ ())))
        in _ , vcvtop-zero-4 c-1 M2 M1 op (proj₁ r) _ _ zeq refl refl (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
...   | nl-i32 | nl-f32 =
        let r = vcvtop-fire (λ cj → inv-lanes- (X lanetype-F32 (mk-dim M2)) cj) (map (λ x → vcvtop-- (X lanetype-I32 (mk-dim M1)) (X lanetype-F32 (mk-dim M2)) op x) (lanes- (X lanetype-I32 (mk-dim M1)) c-1) ++ replicate M1 ((fun-zero F32) ∷ [])) (++⁺ (map⁺ (universal (λ x → vcvtop-lane-def e-iok refl x) (lanes- (X lanetype-I32 (mk-dim M1)) c-1))) (replicate⁺ M1 (λ ())))
        in _ , vcvtop-zero-8 c-1 M2 M1 op (proj₁ r) _ _ zeq refl refl (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
...   | nl-i32 | nl-f64 =
        let r = vcvtop-fire (λ cj → inv-lanes- (X lanetype-F64 (mk-dim M2)) cj) (map (λ x → vcvtop-- (X lanetype-I32 (mk-dim M1)) (X lanetype-F64 (mk-dim M2)) op x) (lanes- (X lanetype-I32 (mk-dim M1)) c-1) ++ replicate M1 ((fun-zero F64) ∷ [])) (++⁺ (map⁺ (universal (λ x → vcvtop-lane-def e-iok refl x) (lanes- (X lanetype-I32 (mk-dim M1)) c-1))) (replicate⁺ M1 (λ ())))
        in _ , vcvtop-zero-12 c-1 M2 M1 op (proj₁ r) _ _ zeq refl refl (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
...   | nl-i64 | nl-i32 =
        let r = vcvtop-fire (λ cj → inv-lanes- (X lanetype-I32 (mk-dim M2)) cj) (map (λ x → vcvtop-- (X lanetype-I64 (mk-dim M1)) (X lanetype-I32 (mk-dim M2)) op x) (lanes- (X lanetype-I64 (mk-dim M1)) c-1) ++ replicate M1 ((fun-zero I32) ∷ [])) (++⁺ (map⁺ (universal (λ x → vcvtop-lane-def e-iok refl x) (lanes- (X lanetype-I64 (mk-dim M1)) c-1))) (replicate⁺ M1 (λ ())))
        in _ , vcvtop-zero-1 c-1 M2 M1 op (proj₁ r) _ _ zeq refl refl (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
...   | nl-i64 | nl-i64 =
        let r = vcvtop-fire (λ cj → inv-lanes- (X lanetype-I64 (mk-dim M2)) cj) (map (λ x → vcvtop-- (X lanetype-I64 (mk-dim M1)) (X lanetype-I64 (mk-dim M2)) op x) (lanes- (X lanetype-I64 (mk-dim M1)) c-1) ++ replicate M1 ((fun-zero I64) ∷ [])) (++⁺ (map⁺ (universal (λ x → vcvtop-lane-def e-iok refl x) (lanes- (X lanetype-I64 (mk-dim M1)) c-1))) (replicate⁺ M1 (λ ())))
        in _ , vcvtop-zero-5 c-1 M2 M1 op (proj₁ r) _ _ zeq refl refl (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
...   | nl-i64 | nl-f32 =
        let r = vcvtop-fire (λ cj → inv-lanes- (X lanetype-F32 (mk-dim M2)) cj) (map (λ x → vcvtop-- (X lanetype-I64 (mk-dim M1)) (X lanetype-F32 (mk-dim M2)) op x) (lanes- (X lanetype-I64 (mk-dim M1)) c-1) ++ replicate M1 ((fun-zero F32) ∷ [])) (++⁺ (map⁺ (universal (λ x → vcvtop-lane-def e-iok refl x) (lanes- (X lanetype-I64 (mk-dim M1)) c-1))) (replicate⁺ M1 (λ ())))
        in _ , vcvtop-zero-9 c-1 M2 M1 op (proj₁ r) _ _ zeq refl refl (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
...   | nl-i64 | nl-f64 =
        let r = vcvtop-fire (λ cj → inv-lanes- (X lanetype-F64 (mk-dim M2)) cj) (map (λ x → vcvtop-- (X lanetype-I64 (mk-dim M1)) (X lanetype-F64 (mk-dim M2)) op x) (lanes- (X lanetype-I64 (mk-dim M1)) c-1) ++ replicate M1 ((fun-zero F64) ∷ [])) (++⁺ (map⁺ (universal (λ x → vcvtop-lane-def e-iok refl x) (lanes- (X lanetype-I64 (mk-dim M1)) c-1))) (replicate⁺ M1 (λ ())))
        in _ , vcvtop-zero-13 c-1 M2 M1 op (proj₁ r) _ _ zeq refl refl (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
...   | nl-f32 | nl-i32 =
        let r = vcvtop-fire (λ cj → inv-lanes- (X lanetype-I32 (mk-dim M2)) cj) (map (λ x → vcvtop-- (X lanetype-F32 (mk-dim M1)) (X lanetype-I32 (mk-dim M2)) op x) (lanes- (X lanetype-F32 (mk-dim M1)) c-1) ++ replicate M1 ((fun-zero I32) ∷ [])) (++⁺ (map⁺ (universal (λ x → vcvtop-lane-def e-iok refl x) (lanes- (X lanetype-F32 (mk-dim M1)) c-1))) (replicate⁺ M1 (λ ())))
        in _ , vcvtop-zero-2 c-1 M2 M1 op (proj₁ r) _ _ zeq refl refl (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
...   | nl-f32 | nl-i64 =
        let r = vcvtop-fire (λ cj → inv-lanes- (X lanetype-I64 (mk-dim M2)) cj) (map (λ x → vcvtop-- (X lanetype-F32 (mk-dim M1)) (X lanetype-I64 (mk-dim M2)) op x) (lanes- (X lanetype-F32 (mk-dim M1)) c-1) ++ replicate M1 ((fun-zero I64) ∷ [])) (++⁺ (map⁺ (universal (λ x → vcvtop-lane-def e-iok refl x) (lanes- (X lanetype-F32 (mk-dim M1)) c-1))) (replicate⁺ M1 (λ ())))
        in _ , vcvtop-zero-6 c-1 M2 M1 op (proj₁ r) _ _ zeq refl refl (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
...   | nl-f32 | nl-f32 =
        let r = vcvtop-fire (λ cj → inv-lanes- (X lanetype-F32 (mk-dim M2)) cj) (map (λ x → vcvtop-- (X lanetype-F32 (mk-dim M1)) (X lanetype-F32 (mk-dim M2)) op x) (lanes- (X lanetype-F32 (mk-dim M1)) c-1) ++ replicate M1 ((fun-zero F32) ∷ [])) (++⁺ (map⁺ (universal (λ x → vcvtop-lane-def e-iok refl x) (lanes- (X lanetype-F32 (mk-dim M1)) c-1))) (replicate⁺ M1 (λ ())))
        in _ , vcvtop-zero-10 c-1 M2 M1 op (proj₁ r) _ _ zeq refl refl (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
...   | nl-f32 | nl-f64 =
        let r = vcvtop-fire (λ cj → inv-lanes- (X lanetype-F64 (mk-dim M2)) cj) (map (λ x → vcvtop-- (X lanetype-F32 (mk-dim M1)) (X lanetype-F64 (mk-dim M2)) op x) (lanes- (X lanetype-F32 (mk-dim M1)) c-1) ++ replicate M1 ((fun-zero F64) ∷ [])) (++⁺ (map⁺ (universal (λ x → vcvtop-lane-def e-iok refl x) (lanes- (X lanetype-F32 (mk-dim M1)) c-1))) (replicate⁺ M1 (λ ())))
        in _ , vcvtop-zero-14 c-1 M2 M1 op (proj₁ r) _ _ zeq refl refl (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
...   | nl-f64 | nl-i32 =
        let r = vcvtop-fire (λ cj → inv-lanes- (X lanetype-I32 (mk-dim M2)) cj) (map (λ x → vcvtop-- (X lanetype-F64 (mk-dim M1)) (X lanetype-I32 (mk-dim M2)) op x) (lanes- (X lanetype-F64 (mk-dim M1)) c-1) ++ replicate M1 ((fun-zero I32) ∷ [])) (++⁺ (map⁺ (universal (λ x → vcvtop-lane-def e-iok refl x) (lanes- (X lanetype-F64 (mk-dim M1)) c-1))) (replicate⁺ M1 (λ ())))
        in _ , vcvtop-zero-3 c-1 M2 M1 op (proj₁ r) _ _ zeq refl refl (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
...   | nl-f64 | nl-i64 =
        let r = vcvtop-fire (λ cj → inv-lanes- (X lanetype-I64 (mk-dim M2)) cj) (map (λ x → vcvtop-- (X lanetype-F64 (mk-dim M1)) (X lanetype-I64 (mk-dim M2)) op x) (lanes- (X lanetype-F64 (mk-dim M1)) c-1) ++ replicate M1 ((fun-zero I64) ∷ [])) (++⁺ (map⁺ (universal (λ x → vcvtop-lane-def e-iok refl x) (lanes- (X lanetype-F64 (mk-dim M1)) c-1))) (replicate⁺ M1 (λ ())))
        in _ , vcvtop-zero-7 c-1 M2 M1 op (proj₁ r) _ _ zeq refl refl (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
...   | nl-f64 | nl-f32 =
        let r = vcvtop-fire (λ cj → inv-lanes- (X lanetype-F32 (mk-dim M2)) cj) (map (λ x → vcvtop-- (X lanetype-F64 (mk-dim M1)) (X lanetype-F32 (mk-dim M2)) op x) (lanes- (X lanetype-F64 (mk-dim M1)) c-1) ++ replicate M1 ((fun-zero F32) ∷ [])) (++⁺ (map⁺ (universal (λ x → vcvtop-lane-def e-iok refl x) (lanes- (X lanetype-F64 (mk-dim M1)) c-1))) (replicate⁺ M1 (λ ())))
        in _ , vcvtop-zero-11 c-1 M2 M1 op (proj₁ r) _ _ zeq refl refl (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
...   | nl-f64 | nl-f64 =
        let r = vcvtop-fire (λ cj → inv-lanes- (X lanetype-F64 (mk-dim M2)) cj) (map (λ x → vcvtop-- (X lanetype-F64 (mk-dim M1)) (X lanetype-F64 (mk-dim M2)) op x) (lanes- (X lanetype-F64 (mk-dim M1)) c-1) ++ replicate M1 ((fun-zero F64) ∷ [])) (++⁺ (map⁺ (universal (λ x → vcvtop-lane-def e-iok refl x) (lanes- (X lanetype-F64 (mk-dim M1)) c-1))) (replicate⁺ M1 (λ ())))
        in _ , vcvtop-zero-15 c-1 M2 M1 op (proj₁ r) _ _ zeq refl refl (proj₁ (proj₂ r)) (proj₂ (proj₂ r))

vcvtop-step : ∀ {s C Lnn2 Lnn1 M2 M1 op d cc} (c-1 : uN-fam0 128) →
  Instr-ok2 s C (admininstr-VCVTOP (X Lnn2 (mk-dim M2)) (X Lnn1 (mk-dim M1)) op) (mk-functype (mk-list d) (mk-list cc)) →
  Σ (List admininstr) λ res →
    Step-pure (admininstr-VCONST V128 c-1 ∷ admininstr-VCVTOP (X Lnn2 (mk-dim M2)) (X Lnn1 (mk-dim M1)) op ∷ []) res
vcvtop-step {Lnn2 = Lnn2} {Lnn1 = Lnn1} {M2 = M2} {M1 = M1} {op = op} c-1 e-iok with halfop op in heq
... | just h =
      let r = vcvtop-fire (λ cj → inv-lanes- (X Lnn2 (mk-dim M2)) cj)
                (map (λ x → vcvtop-- (X Lnn1 (mk-dim M1)) (X Lnn2 (mk-dim M2)) op x) (slice (lanes- (X Lnn1 (mk-dim M1)) c-1) (fun-half h 0 M2) M2))
                (map⁺ (universal (λ x → vcvtop-lane-def e-iok refl x) (slice (lanes- (X Lnn1 (mk-dim M1)) c-1) (fun-half h 0 M2) M2)))
      in _ , vcvtop-half c-1 Lnn2 M2 Lnn1 M1 op (proj₁ r) h _ _ heq refl refl (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
... | nothing with zeroop op in zeq
...   | nothing   = vcvtop-full-step c-1 e-iok heq zeq
...   | just ZERO = vcvtop-zero-step c-1 e-iok zeq




-- v128.bitmask helper: the mask (one bit per lane, zero-padded to 32) has length 32,
-- given the lane count N ≤ 32.  Generic over the lane type A and per-lane map g.
mask-len32 : ∀ {A : Set} (bs : List A) (g : A → bit) (N : ℕ) →
  length bs ≡ N → N ≤ 32 →
  length (map g bs ++ replicate (32 ∸ N) (mk-bit 0)) ≡ 32
mask-len32 bs g N lenbs N≤ =
  tr≡ (length-++ (map g bs))
    (tr≡ (cong₂ _+_ (tr≡ (length-map g bs) lenbs) (length-replicate (32 ∸ N)))
         (m+[n∸m]≡n N≤))

-- v128.swizzle helper: the index table padded to 256 has length 256 (lane count M ≤ 256).

-- ===== data.drop / elem.drop: set the slot's payload to empty. =====
extend-set-data : ∀ (s : store) (a : ℕ) →
  Extend-store s
    (record s { store-DATAS =
      modify (store-DATAS s) a (λ di → record di { datainst-BYTES = [] }) })
extend-set-data s a =
  mk-Extend-store s _
    (all-upto _ (λ i i< → i<)) (all-upto _ (λ i i< → i<))
    (all-upto _ (λ i i< → ext-g-refl _))
    (all-upto _ (λ i i< → i<)) (all-upto _ (λ i i< → i<))
    (all-upto _ (λ i i< → ext-m-refl _))
    (all-upto _ (λ i i< → i<)) (all-upto _ (λ i i< → i<))
    (all-upto _ (λ i i< → ext-t-refl _))
    (all-upto _ (λ i i< → i<)) (all-upto _ (λ i i< → i<))
    (all-upto _ (λ i i< → ext-f-refl _))
    (all-upto _ (λ i i< → i<))
    (all-upto _ (λ i i< → subst (i <_) (sym (modify-length (store-DATAS s) a _)) i<))
    (all-upto _ dext)
    (all-upto _ (λ i i< → i<)) (all-upto _ (λ i i< → i<))
    (all-upto _ (λ i i< → ext-e-refl _))
  where
  DL = store-DATAS s
  upd = λ (di : datainst) → record di { datainst-BYTES = [] }
  dext : ∀ i → i < length DL → Extend-datainst (DL [ i ]!) (modify DL a upd [ i ]!)
  dext i i< with i ≟ a
  ... | yes refl =
    subst (λ z → Extend-datainst (DL [ a ]!) z) (sym (modify-eq DL a upd i<))
      (mk-Extend-datainst (datainst-BYTES (DL [ a ]!)) [] (inj₂ refl))
  ... | no i≢a =
    subst (λ z → Extend-datainst (DL [ i ]!) z) (sym (modify-neq DL a upd i< i≢a))
      (ext-d-refl (DL [ i ]!))

dat-slot : ∀ {s s' gg dt} → Datainst-ok s gg dt →
  Datainst-ok s' (record gg { datainst-BYTES = [] }) dt
dat-slot (mk-Datainst-ok _ _) = mk-Datainst-ok _ []

store-ok-set-data : ∀ (s : store) (a : ℕ) → Store-ok s →
  Store-ok (record s { store-DATAS =
    modify (store-DATAS s) a (λ di → record di { datainst-BYTES = [] }) })
store-ok-set-data s a
  (mk-Store-ok _ gil gtl mil mtl til ttl fil ftl dil dtl eil etl
     glen gok mlen mok tlen tok flen fok dlen dok elen eok seqEq)
  with extend-set-data s a
... | ext =
  mk-Store-ok _ gil gtl mil mtl til ttl fil ftl
    (modify (store-DATAS s) a upd) dtl eil etl
    glen (pw-mapR (wk-globalinst ext) gok)
    mlen (pw-mapR (wk-meminst ext) mok)
    tlen (pw-mapR (wk-tableinst ext) tok)
    flen (pw-mapR (wk-funcinst ext) fok)
    (tr≡ (modify-length (store-DATAS s) a upd)
         (subst (λ l → length l ≡ length dtl) (sym dil≡) dlen))
    (pw-modify a upd (wk-datainst ext) dok' (λ a<' → dat-slot (pw-lookup dok' a<')))
    elen (pw-mapR (wk-eleminst ext) eok)
    (cong (λ ss → record ss { store-DATAS = modify (store-DATAS s) a upd }) seqEq)
  where
  upd = λ (di : datainst) → record di { datainst-BYTES = [] }
  dil≡ : store-DATAS s ≡ dil
  dil≡ = cong store-DATAS seqEq
  dok' : Pointwise (λ di dt → Datainst-ok s di dt) (store-DATAS s) dtl
  dok' = subst (λ l → Pointwise (λ di dt → Datainst-ok s di dt) l dtl) (sym dil≡) dok

extend-set-elem : ∀ (s : store) (a : ℕ) →
  Extend-store s
    (record s { store-ELEMS =
      modify (store-ELEMS s) a (λ ei → record ei { eleminst-REFS = [] }) })
extend-set-elem s a =
  mk-Extend-store s _
    (all-upto _ (λ i i< → i<)) (all-upto _ (λ i i< → i<))
    (all-upto _ (λ i i< → ext-g-refl _))
    (all-upto _ (λ i i< → i<)) (all-upto _ (λ i i< → i<))
    (all-upto _ (λ i i< → ext-m-refl _))
    (all-upto _ (λ i i< → i<)) (all-upto _ (λ i i< → i<))
    (all-upto _ (λ i i< → ext-t-refl _))
    (all-upto _ (λ i i< → i<)) (all-upto _ (λ i i< → i<))
    (all-upto _ (λ i i< → ext-f-refl _))
    (all-upto _ (λ i i< → i<)) (all-upto _ (λ i i< → i<))
    (all-upto _ (λ i i< → ext-d-refl _))
    (all-upto _ (λ i i< → i<))
    (all-upto _ (λ i i< → subst (i <_) (sym (modify-length (store-ELEMS s) a _)) i<))
    (all-upto _ eext)
  where
  EL = store-ELEMS s
  upd = λ (ei : eleminst) → record ei { eleminst-REFS = [] }
  eext : ∀ i → i < length EL → Extend-eleminst (EL [ i ]!) (modify EL a upd [ i ]!)
  eext i i< with i ≟ a
  ... | yes refl =
    subst (λ z → Extend-eleminst (EL [ a ]!) z) (sym (modify-eq EL a upd i<))
      (mk-Extend-eleminst (eleminst-TYPE (EL [ a ]!)) (eleminst-REFS (EL [ a ]!)) []
        (inj₂ refl))
  ... | no i≢a =
    subst (λ z → Extend-eleminst (EL [ i ]!) z) (sym (modify-neq EL a upd i< i≢a))
      (ext-e-refl (EL [ i ]!))

elem-slot : ∀ {s s' gg et} → Eleminst-ok s gg et →
  Eleminst-ok s' (record gg { eleminst-REFS = [] }) et
elem-slot (mk-Eleminst-ok _ rt refs fr) = mk-Eleminst-ok _ rt [] []

store-ok-set-elem : ∀ (s : store) (a : ℕ) → Store-ok s →
  Store-ok (record s { store-ELEMS =
    modify (store-ELEMS s) a (λ ei → record ei { eleminst-REFS = [] }) })
store-ok-set-elem s a
  (mk-Store-ok _ gil gtl mil mtl til ttl fil ftl dil dtl eil etl
     glen gok mlen mok tlen tok flen fok dlen dok elen eok seqEq)
  with extend-set-elem s a
... | ext =
  mk-Store-ok _ gil gtl mil mtl til ttl fil ftl dil dtl
    (modify (store-ELEMS s) a upd) etl
    glen (pw-mapR (wk-globalinst ext) gok)
    mlen (pw-mapR (wk-meminst ext) mok)
    tlen (pw-mapR (wk-tableinst ext) tok)
    flen (pw-mapR (wk-funcinst ext) fok)
    dlen (pw-mapR (wk-datainst ext) dok)
    (tr≡ (modify-length (store-ELEMS s) a upd)
         (subst (λ l → length l ≡ length etl) (sym eil≡) elen))
    (pw-modify a upd (wk-eleminst ext) eok' (λ a<' → elem-slot (pw-lookup eok' a<')))
    (cong (λ ss → record ss { store-ELEMS = modify (store-ELEMS s) a upd }) seqEq)
  where
  upd = λ (ei : eleminst) → record ei { eleminst-REFS = [] }
  eil≡ : store-ELEMS s ≡ eil
  eil≡ = cong store-ELEMS seqEq
  eok' : Pointwise (λ ei et → Eleminst-ok s ei et) (store-ELEMS s) etl
  eok' = subst (λ l → Pointwise (λ ei et → Eleminst-ok s ei et) l etl) (sym eil≡) eok

-- ===== memory store: in-bounds byte write preserves |BYTES|. =====
slice-update-length : ∀ {A : Set} (xs : List A) (off sz : ℕ) (u : List A) →
  off + sz ≤ length xs → sz ≤ length u →
  length (slice-update xs off sz u) ≡ length xs
slice-update-length xs off sz u ib su =
  tr≡ (length-++ (take off xs))
  (tr≡ (cong (length (take off xs) +_) (length-++ (take sz u)))
  (tr≡ (cong (_+ (length (take sz u) + length (drop (off + sz) xs))) len-off)
  (tr≡ (cong (λ z → off + z) (cong (_+ length (drop (off + sz) xs)) len-sz))
  (tr≡ (cong (λ z → off + (sz + z)) (length-drop (off + sz) xs))
       (tr≡ (sym (+-assoc off sz (length xs ∸ (off + sz)))) (m+[n∸m]≡n ib))))))
  where
  len-off : length (take off xs) ≡ off
  len-off = tr≡ (length-take off xs) (m≤n⇒m⊓n≡m (≤-trans (m≤m+n off sz) ib))
  len-sz : length (take sz u) ≡ sz
  len-sz = tr≡ (length-take sz u) (m≤n⇒m⊓n≡m su)

-- Update the BYTES of a well-typed meminst, preserving length ⇒ Meminst-ok.
mem-update-ok : ∀ {s s' mi mt} → Meminst-ok s mi mt → (nb : List byte) →
  length nb ≡ length (BYTES mi) → Meminst-ok s' (record mi { BYTES = nb }) mt
mem-update-ok (mk-Meminst-ok _ n mo b mtok leneq) nb lenq =
  mk-Meminst-ok _ n mo nb mtok (tr≡ lenq leneq)

mem-extend-slot : ∀ {s mi mt} → Meminst-ok s mi mt → (nb : List byte) →
  length (BYTES mi) ≤ length nb → Extend-meminst mi (record mi { BYTES = nb })
mem-extend-slot (mk-Meminst-ok _ n mo b mtok leneq) nb le =
  mk-Extend-meminst n mo b n nb ≤-refl le

-- Combined: an in-bounds byte write yields (Extend-store , Store-ok).
store-write-mem : ∀ (s : store) (a off sz : ℕ) (b : List byte) →
  off + sz ≤ length (BYTES ((store-MEMS s) [ a ]!)) → sz ≤ length b →
  Store-ok s →
  Extend-store s (record s { store-MEMS =
     modify (store-MEMS s) a (λ mi → record mi { BYTES = slice-update (BYTES mi) off sz b }) })
   × Store-ok (record s { store-MEMS =
     modify (store-MEMS s) a (λ mi → record mi { BYTES = slice-update (BYTES mi) off sz b }) })
store-write-mem s a off sz b ib su
  (mk-Store-ok _ gil gtl mil mtl til ttl fil ftl dil dtl eil etl
     glen gok mlen mok tlen tok flen fok dlen dok elen eok seqEq) = ext , sok'
  where
  upd = λ (mi : meminst) → record mi { BYTES = slice-update (BYTES mi) off sz b }
  mil≡ : store-MEMS s ≡ mil
  mil≡ = cong store-MEMS seqEq
  mok' : Pointwise (λ mi mt → Meminst-ok s mi mt) (store-MEMS s) mtl
  mok' = subst (λ l → Pointwise (λ mi mt → Meminst-ok s mi mt) l mtl) (sym mil≡) mok
  slen : length (slice-update (BYTES ((store-MEMS s) [ a ]!)) off sz b)
         ≡ length (BYTES ((store-MEMS s) [ a ]!))
  slen = slice-update-length (BYTES ((store-MEMS s) [ a ]!)) off sz b ib su
  mext : ∀ i → i < length (store-MEMS s) →
    Extend-meminst ((store-MEMS s) [ i ]!) (modify (store-MEMS s) a upd [ i ]!)
  mext i i< with i ≟ a
  ... | yes refl =
    subst (λ z → Extend-meminst ((store-MEMS s) [ a ]!) z)
      (sym (modify-eq (store-MEMS s) a upd i<))
      (mem-extend-slot (pw-lookup mok' i<) (slice-update (BYTES ((store-MEMS s) [ a ]!)) off sz b)
        (≤-reflexive (sym slen)))
  ... | no i≢a =
    subst (λ z → Extend-meminst ((store-MEMS s) [ i ]!) z)
      (sym (modify-neq (store-MEMS s) a upd i< i≢a)) (ext-m-refl _)
  ext : Extend-store s _
  ext = mk-Extend-store s _
    (all-upto _ (λ i i< → i<)) (all-upto _ (λ i i< → i<))
    (all-upto _ (λ i i< → ext-g-refl _))
    (all-upto _ (λ i i< → i<))
    (all-upto _ (λ i i< → subst (i <_) (sym (modify-length (store-MEMS s) a upd)) i<))
    (all-upto _ mext)
    (all-upto _ (λ i i< → i<)) (all-upto _ (λ i i< → i<))
    (all-upto _ (λ i i< → ext-t-refl _))
    (all-upto _ (λ i i< → i<)) (all-upto _ (λ i i< → i<))
    (all-upto _ (λ i i< → ext-f-refl _))
    (all-upto _ (λ i i< → i<)) (all-upto _ (λ i i< → i<))
    (all-upto _ (λ i i< → ext-d-refl _))
    (all-upto _ (λ i i< → i<)) (all-upto _ (λ i i< → i<))
    (all-upto _ (λ i i< → ext-e-refl _))
  mem-slot : ∀ (i< : a < length (store-MEMS s)) →
    Meminst-ok _ (upd ((store-MEMS s) [ a ]!)) (mtl [ a ]!)
  mem-slot i< =
    mem-update-ok (pw-lookup mok' i<)
      (slice-update (BYTES ((store-MEMS s) [ a ]!)) off sz b) slen
  sok' : Store-ok _
  sok' = mk-Store-ok _ gil gtl (modify (store-MEMS s) a upd) mtl til ttl fil ftl dil dtl eil etl
    glen (pw-mapR (wk-globalinst ext) gok)
    (tr≡ (modify-length (store-MEMS s) a upd)
         (subst (λ l → length l ≡ length mtl) (sym mil≡) mlen))
    (pw-modify a upd (wk-meminst ext) mok' mem-slot)
    tlen (pw-mapR (wk-tableinst ext) tok)
    flen (pw-mapR (wk-funcinst ext) fok)
    dlen (pw-mapR (wk-datainst ext) dok)
    elen (pw-mapR (wk-eleminst ext) eok)
    (cong (λ ss → record ss { store-MEMS = modify (store-MEMS s) a upd }) seqEq)

-- ===== grow: replace a whole meminst/tableinst (type grows). =====
store-write-meminst : ∀ (s : store) (a : ℕ) (mi' : meminst) →
  Extend-meminst ((store-MEMS s) [ a ]!) mi' → Meminst-ok s mi' (meminst-TYPE mi') →
  Store-ok s →
  Extend-store s (record s { store-MEMS = modify (store-MEMS s) a (λ _ → mi') })
   × Store-ok (record s { store-MEMS = modify (store-MEMS s) a (λ _ → mi') })
store-write-meminst s a mi' emi miok
  (mk-Store-ok _ gil gtl mil mtl til ttl fil ftl dil dtl eil etl
     glen gok mlen mok tlen tok flen fok dlen dok elen eok seqEq) = ext , sok'
  where
  upd : meminst → meminst
  upd = λ _ → mi'
  updT : memtype → memtype
  updT = λ _ → meminst-TYPE mi'
  mil≡ : store-MEMS s ≡ mil
  mil≡ = cong store-MEMS seqEq
  mok' : Pointwise (λ mi mt → Meminst-ok s mi mt) (store-MEMS s) mtl
  mok' = subst (λ l → Pointwise (λ mi mt → Meminst-ok s mi mt) l mtl) (sym mil≡) mok
  mext : ∀ i → i < length (store-MEMS s) →
    Extend-meminst ((store-MEMS s) [ i ]!) (modify (store-MEMS s) a upd [ i ]!)
  mext i i< with i ≟ a
  ... | yes refl = subst (λ z → Extend-meminst ((store-MEMS s) [ a ]!) z)
                     (sym (modify-eq (store-MEMS s) a upd i<)) emi
  ... | no i≢a = subst (λ z → Extend-meminst ((store-MEMS s) [ i ]!) z)
                   (sym (modify-neq (store-MEMS s) a upd i< i≢a)) (ext-m-refl _)
  ext : Extend-store s _
  ext = mk-Extend-store s _
    (all-upto _ (λ i i< → i<)) (all-upto _ (λ i i< → i<))
    (all-upto _ (λ i i< → ext-g-refl _))
    (all-upto _ (λ i i< → i<))
    (all-upto _ (λ i i< → subst (i <_) (sym (modify-length (store-MEMS s) a upd)) i<))
    (all-upto _ mext)
    (all-upto _ (λ i i< → i<)) (all-upto _ (λ i i< → i<))
    (all-upto _ (λ i i< → ext-t-refl _))
    (all-upto _ (λ i i< → i<)) (all-upto _ (λ i i< → i<))
    (all-upto _ (λ i i< → ext-f-refl _))
    (all-upto _ (λ i i< → i<)) (all-upto _ (λ i i< → i<))
    (all-upto _ (λ i i< → ext-d-refl _))
    (all-upto _ (λ i i< → i<)) (all-upto _ (λ i i< → i<))
    (all-upto _ (λ i i< → ext-e-refl _))
  sok' : Store-ok _
  sok' = mk-Store-ok _ gil gtl (modify (store-MEMS s) a upd) (modify mtl a updT)
    til ttl fil ftl dil dtl eil etl
    glen (pw-mapR (wk-globalinst ext) gok)
    (tr≡ (modify-length (store-MEMS s) a upd)
      (tr≡ (subst (λ l → length l ≡ length mtl) (sym mil≡) mlen)
           (sym (modify-length mtl a updT))))
    (pw-modify-both a upd updT (wk-meminst ext) mok' (λ _ → wk-meminst ext miok))
    tlen (pw-mapR (wk-tableinst ext) tok)
    flen (pw-mapR (wk-funcinst ext) fok)
    dlen (pw-mapR (wk-datainst ext) dok)
    elen (pw-mapR (wk-eleminst ext) eok)
    (cong (λ ss → record ss { store-MEMS = modify (store-MEMS s) a upd }) seqEq)

store-write-tableinst : ∀ (s : store) (a : ℕ) (ti' : tableinst) →
  Extend-tableinst ((store-TABLES s) [ a ]!) ti' → Tableinst-ok s ti' (tableinst-TYPE ti') →
  Store-ok s →
  Extend-store s (record s { store-TABLES = modify (store-TABLES s) a (λ _ → ti') })
   × Store-ok (record s { store-TABLES = modify (store-TABLES s) a (λ _ → ti') })
store-write-tableinst s a ti' eti tiok
  (mk-Store-ok _ gil gtl mil mtl til ttl fil ftl dil dtl eil etl
     glen gok mlen mok tlen tok flen fok dlen dok elen eok seqEq) = ext , sok'
  where
  upd : tableinst → tableinst
  upd = λ _ → ti'
  updT : tabletype → tabletype
  updT = λ _ → tableinst-TYPE ti'
  til≡ : store-TABLES s ≡ til
  til≡ = cong store-TABLES seqEq
  tok' : Pointwise (λ ti tt → Tableinst-ok s ti tt) (store-TABLES s) ttl
  tok' = subst (λ l → Pointwise (λ ti tt → Tableinst-ok s ti tt) l ttl) (sym til≡) tok
  text : ∀ i → i < length (store-TABLES s) →
    Extend-tableinst ((store-TABLES s) [ i ]!) (modify (store-TABLES s) a upd [ i ]!)
  text i i< with i ≟ a
  ... | yes refl = subst (λ z → Extend-tableinst ((store-TABLES s) [ a ]!) z)
                     (sym (modify-eq (store-TABLES s) a upd i<)) eti
  ... | no i≢a = subst (λ z → Extend-tableinst ((store-TABLES s) [ i ]!) z)
                   (sym (modify-neq (store-TABLES s) a upd i< i≢a)) (ext-t-refl _)
  ext : Extend-store s _
  ext = mk-Extend-store s _
    (all-upto _ (λ i i< → i<)) (all-upto _ (λ i i< → i<))
    (all-upto _ (λ i i< → ext-g-refl _))
    (all-upto _ (λ i i< → i<)) (all-upto _ (λ i i< → i<))
    (all-upto _ (λ i i< → ext-m-refl _))
    (all-upto _ (λ i i< → i<))
    (all-upto _ (λ i i< → subst (i <_) (sym (modify-length (store-TABLES s) a upd)) i<))
    (all-upto _ text)
    (all-upto _ (λ i i< → i<)) (all-upto _ (λ i i< → i<))
    (all-upto _ (λ i i< → ext-f-refl _))
    (all-upto _ (λ i i< → i<)) (all-upto _ (λ i i< → i<))
    (all-upto _ (λ i i< → ext-d-refl _))
    (all-upto _ (λ i i< → i<)) (all-upto _ (λ i i< → i<))
    (all-upto _ (λ i i< → ext-e-refl _))
  sok' : Store-ok _
  sok' = mk-Store-ok _ gil gtl mil mtl (modify (store-TABLES s) a upd) (modify ttl a updT)
    fil ftl dil dtl eil etl
    glen (pw-mapR (wk-globalinst ext) gok)
    mlen (pw-mapR (wk-meminst ext) mok)
    (tr≡ (modify-length (store-TABLES s) a upd)
      (tr≡ (subst (λ l → length l ≡ length ttl) (sym til≡) tlen)
           (sym (modify-length ttl a updT))))
    (pw-modify-both a upd updT (wk-tableinst ext) tok' (λ _ → wk-tableinst ext tiok))
    flen (pw-mapR (wk-funcinst ext) fok)
    dlen (pw-mapR (wk-datainst ext) dok)
    elen (pw-mapR (wk-eleminst ext) eok)
    (cong (λ ss → record ss { store-TABLES = modify (store-TABLES s) a upd }) seqEq)

-- table.set: update one ref in a tableinst (length + type preserved).
table-ref-extend : ∀ {s ti tt} → Tableinst-ok s ti tt → (r : ref) (i : ℕ) →
  Extend-tableinst ti (record ti { REFS = modify (REFS ti) i (λ _ → r) })
table-ref-extend (mk-Tableinst-ok _ n mo rt refs ttok fr leneq) r i =
  mk-Extend-tableinst n mo rt refs n (modify refs i (λ _ → r)) ≤-refl
    (≤-reflexive (sym (modify-length refs i _)))

table-ref-update-ok : ∀ {s ti tt} (r : ref) (i : ℕ) → Tableinst-ok s ti tt →
  (∀ {lim rt} → tt ≡ mk-tabletype lim rt → Ref-ok s r rt) →
  Tableinst-ok s (record ti { REFS = modify (REFS ti) i (λ _ → r) }) tt
table-ref-update-ok r i (mk-Tableinst-ok _ n mo rt refs ttok fr leneq) refokf =
  mk-Tableinst-ok _ n mo rt (modify refs i (λ _ → r)) ttok
    (all-modify i (λ _ → r) (λ x → x) fr (λ _ → refokf refl))
    (tr≡ (modify-length refs i _) leneq)

store-write-table-ref : ∀ (s : store) (a i : ℕ) (r : ref) →
  (∀ {lim rt} → tableinst-TYPE ((store-TABLES s) [ a ]!) ≡ mk-tabletype lim rt → Ref-ok s r rt) →
  Store-ok s →
  Extend-store s (record s { store-TABLES =
     modify (store-TABLES s) a (λ ti → record ti { REFS = modify (REFS ti) i (λ _ → r) }) })
   × Store-ok (record s { store-TABLES =
     modify (store-TABLES s) a (λ ti → record ti { REFS = modify (REFS ti) i (λ _ → r) }) })
store-write-table-ref s a i r refokf
  (mk-Store-ok _ gil gtl mil mtl til ttl fil ftl dil dtl eil etl
     glen gok mlen mok tlen tok flen fok dlen dok elen eok seqEq) = ext , sok'
  where
  upd = λ (ti : tableinst) → record ti { REFS = modify (REFS ti) i (λ _ → r) }
  til≡ : store-TABLES s ≡ til
  til≡ = cong store-TABLES seqEq
  tok' : Pointwise (λ ti tt → Tableinst-ok s ti tt) (store-TABLES s) ttl
  tok' = subst (λ l → Pointwise (λ ti tt → Tableinst-ok s ti tt) l ttl) (sym til≡) tok
  text : ∀ i' → i' < length (store-TABLES s) →
    Extend-tableinst ((store-TABLES s) [ i' ]!) (modify (store-TABLES s) a upd [ i' ]!)
  text i' i'< with i' ≟ a
  ... | yes refl = subst (λ z → Extend-tableinst ((store-TABLES s) [ a ]!) z)
                     (sym (modify-eq (store-TABLES s) a upd i'<))
                     (table-ref-extend (pw-lookup tok' i'<) r i)
  ... | no i≢a = subst (λ z → Extend-tableinst ((store-TABLES s) [ i' ]!) z)
                   (sym (modify-neq (store-TABLES s) a upd i'< i≢a)) (ext-t-refl _)
  ext : Extend-store s _
  ext = mk-Extend-store s _
    (all-upto _ (λ i' i'< → i'<)) (all-upto _ (λ i' i'< → i'<))
    (all-upto _ (λ i' i'< → ext-g-refl _))
    (all-upto _ (λ i' i'< → i'<)) (all-upto _ (λ i' i'< → i'<))
    (all-upto _ (λ i' i'< → ext-m-refl _))
    (all-upto _ (λ i' i'< → i'<))
    (all-upto _ (λ i' i'< → subst (i' <_) (sym (modify-length (store-TABLES s) a upd)) i'<))
    (all-upto _ text)
    (all-upto _ (λ i' i'< → i'<)) (all-upto _ (λ i' i'< → i'<))
    (all-upto _ (λ i' i'< → ext-f-refl _))
    (all-upto _ (λ i' i'< → i'<)) (all-upto _ (λ i' i'< → i'<))
    (all-upto _ (λ i' i'< → ext-d-refl _))
    (all-upto _ (λ i' i'< → i'<)) (all-upto _ (λ i' i'< → i'<))
    (all-upto _ (λ i' i'< → ext-e-refl _))
  tab-slot : ∀ (i'< : a < length (store-TABLES s)) →
    Tableinst-ok _ (upd ((store-TABLES s) [ a ]!)) (ttl [ a ]!)
  tab-slot i'< = wk-tableinst ext
    (table-ref-update-ok r i (pw-lookup tok' i'<)
      (λ eq → refokf (tr≡ (tinst-type-eq (pw-lookup tok' i'<)) eq)))
  sok' : Store-ok _
  sok' = mk-Store-ok _ gil gtl mil mtl (modify (store-TABLES s) a upd) ttl fil ftl dil dtl eil etl
    glen (pw-mapR (wk-globalinst ext) gok)
    mlen (pw-mapR (wk-meminst ext) mok)
    (tr≡ (modify-length (store-TABLES s) a upd)
         (subst (λ l → length l ≡ length ttl) (sym til≡) tlen))
    (pw-modify a upd (wk-tableinst ext) tok' tab-slot)
    flen (pw-mapR (wk-funcinst ext) fok)
    dlen (pw-mapR (wk-datainst ext) dok)
    elen (pw-mapR (wk-eleminst ext) eok)
    (cong (λ ss → record ss { store-TABLES = modify (store-TABLES s) a upd }) seqEq)

record CoreRes (Cf Ci : context) (u1 u2 : List valtype)
               (s s' : store) (f' : frame) (es' : List admininstr) : Set where
  constructor mk-core
  field
    ext  : Extend-store s s'
    sok' : Store-ok s'
    fok' : Frame-ok s' f' Cf
    ok'  : Instrs-ok2 s' Ci es' (mk-functype (mk-list u1) (mk-list u2))

-- ** pres-step is TOTAL ** -- defined on EVERY Step rule, with no
-- postulate.  Covered: pure (all 104 Step-pure via pres-pure), read
-- (block/loop/call-addr/local-get/global-get + the bulk-op reads via
-- pres-read), local.set, global.set, data/elem.drop, the 6 trapping
-- store-writes, the 8 memory value-writes, memory.grow (fail+succeed),
-- table.set-val, table.grow (fail+succeed), ctxt-instrs, and -- via the
-- context-stack generalization (Agree Ci Cf, agree-labC/agree-retC) --
-- the two congruence rules ctxt-label / ctxt-frame.  pres-step-rest is
-- DELETED.  pres-read is likewise TOTAL: the bulk-op reads (load /
-- fill / copy / init, incl. the recursive decompositions) are all
-- proved, so pres-read-rest is DELETED too.
pres-step : ∀ {s f Cf Ci es u1 u2 s' f' es'} →
  Store-ok s → Frame-ok s f Cf → Agree Ci Cf →
  Instrs-ok2 s Ci es (mk-functype (mk-list u1) (mk-list u2)) →
  Step (mk-config (mk-state s f) es) (mk-config (mk-state s' f') es') →
  CoreRes Cf Ci u1 u2 s s' f' es'

pres-step sok fok ag ok (pure _ _ _ sp) =
  mk-core (extend-store-refl _) sok fok (pres-pure ok sp)

pres-step sok fok ag ok (read _ _ _ sr) =
  mk-core (extend-store-refl _) sok fok (pres-read sok fok ag ok sr)

-- v (local.set x) ~> eps  with  F.LOCALS[x] := v   (frame update)
pres-step {s = s} {f = f} sok fok ag ok (Step--local-set _ v x)
  with decomp ok (admininstr-val v ∷ []) (admininstr-LOCAL-SET x ∷ []) refl
... | mk-split m okV okL with val-ty v okV | singleton-inv okL
... | mk-valty p1 a vok s11 s12 | mk-single p2 d2 c2 lok s21 s22
  with lset-inv lok refl
... | t' , refl , refl , x< , lkp
  with rt-sub-unsnoc (rt-sub-trans s12 s21)
... | psub , asub
  with frame-facts fok
... | ff =
  let open FrameFacts ff
      lkp'  = subst (λ l → (l [ proj-uN-0 32 x ]!) ≡ t') locals-eq
                (subst (λ l → (l [ proj-uN-0 32 x ]!) ≡ t') (Agree.loc≡ ag) lkp)
      t'≡a  = vt-sub-val vok asub
      vok'  = subst (Val-ok s v) (sym (tr≡ lkp' t'≡a)) vok
  in mk-core (extend-store-refl _) sok
       (locals-rebuild _
         (tr≡ locals-len (sym (modify-length (LOCALS f) (proj-uN-0 32 x) (λ _ → v))))
         (pw-update locals-ok (proj-uN-0 32 x) v vok'))
       (sub-empty (rt-sub-trans s11 (rt-sub-trans psub (rt-norml p2 s22))))

-- congruence: v* [inner] rest  ~>  v* [inner'] rest
pres-step {Ci = Ci} sok fok ag ok (ctxt-instrs _ vals inner rest _ inner' istp disj)
  with decomp ok (map (λ v → admininstr-val v) vals) (inner ++ rest) refl
... | mk-split m1 okV okIR with decomp okIR inner rest refl
... | mk-split m2 okI okR with pres-step sok fok ag okI istp
... | mk-core ext sok' fok' okI' =
  mk-core ext sok' fok'
    (Instrs-ok2--seq _ _ _ _ _ _ _ (instrs-weaken ext sok' okV)
      (Instrs-ok2--seq _ _ _ _ _ _ _ okI' (instrs-weaken ext sok' okR)))

-- v (global.set x) ~> eps, with the store's global x updated to v.
pres-step {s = s} {f = f} {Ci = Ci} sok fok ag ok (Step--global-set _ v x)
  with decomp ok (admininstr-val v ∷ []) (admininstr-GLOBAL-SET x ∷ []) refl
... | mk-split m okV okG
  with val-ty v okV | singleton-inv okG
... | mk-valty p1 tv vok s11 s12 | mk-single p2 d2 c2 gok2 s21 s22
  with gset-inv gok2 refl
... | t , refl , refl , x<C , glkC
  with rt-sub-unsnoc (rt-sub-trans s12 s21)
... | p1sub , tvsub
  with vt-sub-val vok tvsub
... | refl
  with frame-facts fok
... | ff =
  let gaddr<mod = subst (proj-uN-0 32 x <_) (sym (FrameFacts.gaddrs-len ff))
                    (subst (λ l → proj-uN-0 32 x < length l) (FrameFacts.globals-eq ff)
                      (subst (λ l → proj-uN-0 32 x < length l) (Agree.glob≡ ag) x<C))
      xaok = subst (λ g → Externaddr-ok s
                (externaddr-GLOBAL ((GLOBALS (frame-MODULE f)) [ proj-uN-0 32 x ]!)) (GLOBAL g))
               (subst (λ l → (l [ proj-uN-0 32 x ]!) ≡ mk-globaltype (just MUT) t)
                      (FrameFacts.globals-eq ff)
                      (subst (λ l → (l [ proj-uN-0 32 x ]!) ≡ mk-globaltype (just MUT) t)
                             (Agree.glob≡ ag) glkC))
               (pw-lookup (FrameFacts.globals-ok ff) gaddr<mod)
      inv = xa-global-inv xaok
      ext = extend-set-global s _ t v (proj₁ inv) (proj₂ inv)
  in mk-core ext
       (store-ok-set-global s _ t v (proj₁ inv) (proj₂ inv) sok (ext-val-weaken ext vok))
       (wk-frame ext fok)
       (sub-empty (rt-sub-trans (rt-sub-trans s11 p1sub) (rt-norml p2 s22)))

-- data.drop x ~> eps, store's data x emptied.  Reduct [] : u1<:u2.
pres-step {s = s} {f = f} {Ci = Ci} sok fok ag ok (Step--data-drop _ x)
  with singleton-inv ok
... | mk-single p d2 c2 ddok s21 s22
  with ddrop-inv ddok refl
... | refl , refl =
  let ext = extend-set-data s ((DATAS (frame-MODULE f)) [ proj-uN-0 32 x ]!)
  in mk-core ext
       (store-ok-set-data s _ sok) (wk-frame ext fok)
       (sub-empty (rt-sub-trans (rt-norm p s21) (rt-norml p s22)))

-- elem.drop x ~> eps, store's elem x emptied.
pres-step {s = s} {f = f} {Ci = Ci} sok fok ag ok (Step--elem-drop _ x)
  with singleton-inv ok
... | mk-single p d2 c2 edok s21 s22
  with edrop-inv edok refl
... | refl , refl =
  let ext = extend-set-elem s ((ELEMS (frame-MODULE f)) [ proj-uN-0 32 x ]!)
  in mk-core ext
       (store-ok-set-elem s _ sok) (wk-frame ext fok)
       (sub-empty (rt-sub-trans (rt-norm p s21) (rt-norml p s22)))

-- memory.grow SUCCESS: install the grown meminst; reduct is old size.
pres-step {s = s} {f = f} {Ci = Ci} sok fok ag ok (memory-grow-succeed _ v-n mi grow≢ unwrap≡)
  with decomp ok (admininstr-CONST I32 (mk-uN v-n) ∷ []) (admininstr-MEMORY-GROW ∷ []) refl
... | mk-split m okC okG with const-ty okC | singleton-inv okG
... | (p1 , s11 , s12) | mk-single p2 d2 c2 gok2 s21 s22
  with mgrow-inv gok2 refl
... | refl , refl
  with rt-sub-unsnoc (rt-sub-trans s12 s21)
... | p1sub , _
  with growmemory-ok s (fun-mem (mk-state s f) (mk-uN 0)) mi v-n
         (maybe-just (growmemory (fun-mem (mk-state s f) (mk-uN 0)) v-n) grow≢ unwrap≡)
... | emi , miok
  with store-write-meminst s ((MEMS (frame-MODULE f)) [ proj-uN-0 32 (mk-uN 0) ]!) mi emi miok sok
... | ext , sok' =
  mk-core ext sok' (wk-frame ext fok)
    (push1 p2 (plain _ _ _ _ _ (const _ I32 _)) (rt-sub-trans s11 p1sub) s22)

-- Grow FAILURE: store unchanged, reduct is a single i32.const (-1).
pres-step sok fok ag ok (memory-grow-fail _ n)
  with decomp ok (admininstr-CONST I32 (mk-uN n) ∷ []) (admininstr-MEMORY-GROW ∷ []) refl
... | mk-split m okC okG with const-ty okC | singleton-inv okG
... | (p1 , s11 , s12) | mk-single p2 d2 c2 gok2 s21 s22
  with mgrow-inv gok2 refl
... | refl , refl
  with rt-sub-unsnoc (rt-sub-trans s12 s21)
... | p1sub , _ =
  mk-core (extend-store-refl _) sok fok
    (push1 p2 (plain _ _ _ _ _ (const _ I32 _)) (rt-sub-trans s11 p1sub) s22)
-- (i32.const i) (nt.const c) (nt.store ao) ~> eps, in-bounds byte write.
pres-step {s = s} {f = f} {Ci = Ci} sok fok ag ok (store-num-val _ i nt c ao b-lst _ inb beq)
  with decomp ok (admininstr-CONST I32 i ∷ [])
        (admininstr-CONST nt c ∷ admininstr-STORE nt nothing ao ∷ []) refl
... | mk-split m1 okC1 okR
  with decomp okR (admininstr-CONST nt c ∷ []) (admininstr-STORE nt nothing ao ∷ []) refl
... | mk-split m2 okC2 okS
  with const-ty okC1 | const-ty okC2 | singleton-inv okS
... | (p1 , s11 , s12) | (p2 , s21 , s22) | mk-single p3 d3 c3 sok2 ss1 ss2
  with storenum-inv sok2 refl
... | refl , refl
  with rt-sub-unsnoc
        (subst (λ l → Resulttype-sub (mk-list (p2 ++ valtype-numtype nt ∷ [])) (mk-list l))
               (sym (snoc2 p3 valtype-I32 (valtype-numtype nt))) (rt-sub-trans s22 ss1))
... | p2sub , _
  with rt-sub-unsnoc (rt-sub-trans s12 (rt-sub-trans s21 p2sub))
... | p1sub , _
  with store-write-mem s ((MEMS (frame-MODULE f)) [ proj-uN-0 32 (mk-uN 0) ]!)
         ((proj-uN-0 32 i) + (proj-uN-0 32 (OFFSET ao)))
         (coerce {B = ℕ} ((coerce {B = ℕ} (unwrap! (size (valtype-numtype nt)))) / (coerce {B = ℕ} 8)))
         b-lst inb (≤-reflexive (sym (tr≡ (cong length beq) (nbytes-length nt c)))) sok
... | ext , sok' =
  mk-core ext sok' (wk-frame ext fok)
    (sub-empty (rt-sub-trans (rt-sub-trans s11 p1sub) (rt-norml p3 ss2)))

-- (i32.const i) (v128.const c) (v128.store ao) ~> eps.
pres-step {s = s} {f = f} {Ci = Ci} sok fok ag ok (vstore-val _ i c ao b-lst _ inb beq)
  with decomp ok (admininstr-CONST I32 i ∷ [])
        (admininstr-VCONST V128 c ∷ admininstr-VSTORE V128 ao ∷ []) refl
... | mk-split m1 okC1 okR
  with decomp okR (admininstr-VCONST V128 c ∷ []) (admininstr-VSTORE V128 ao ∷ []) refl
... | mk-split m2 okC2 okS
  with const-ty okC1 | vconst-ty okC2 | singleton-inv okS
... | (p1 , s11 , s12) | (p2 , s21 , s22) | mk-single p3 d3 c3 sok2 ss1 ss2
  with vstore-inv sok2 refl
... | refl , refl
  with rt-sub-unsnoc
        (subst (λ l → Resulttype-sub (mk-list (p2 ++ valtype-V128 ∷ [])) (mk-list l))
               (sym (snoc2 p3 valtype-I32 valtype-V128)) (rt-sub-trans s22 ss1))
... | p2sub , _
  with rt-sub-unsnoc (rt-sub-trans s12 (rt-sub-trans s21 p2sub))
... | p1sub , _
  with store-write-mem s ((MEMS (frame-MODULE f)) [ proj-uN-0 32 (mk-uN 0) ]!)
         ((proj-uN-0 32 i) + (proj-uN-0 32 (OFFSET ao)))
         (coerce {B = ℕ} ((coerce {B = ℕ} (unwrap! (size valtype-V128))) / (coerce {B = ℕ} 8)))
         b-lst inb (≤-reflexive (sym (tr≡ (cong length beq) (vbytes-length V128 c)))) sok
... | ext , sok' =
  mk-core ext sok' (wk-frame ext fok)
    (sub-empty (rt-sub-trans (rt-sub-trans s11 p1sub) (rt-norml p3 ss2)))

-- (i32.const i) (v128.const c) (v128.store_lane ao j) ~> eps.  The
-- in-bounds guard bounds v-N while the write is v-N/8 bytes (v-N/8≤v-N).
pres-step {s = s} {f = f} {Ci = Ci} sok fok ag ok (vstore-lane-val-0 _ i c v-N ao j b-lst _ inb _ _ _ beq)
  with decomp ok (admininstr-CONST I32 i ∷ [])
        (admininstr-VCONST V128 c ∷ admininstr-VSTORE-LANE V128 (mk-sz v-N) ao j ∷ []) refl
... | mk-split m1 okC1 okR
  with decomp okR (admininstr-VCONST V128 c ∷ []) (admininstr-VSTORE-LANE V128 (mk-sz v-N) ao j ∷ []) refl
... | mk-split m2 okC2 okS
  with const-ty okC1 | vconst-ty okC2 | singleton-inv okS
... | (p1 , s11 , s12) | (p2 , s21 , s22) | mk-single p3 d3 c3 sok2 ss1 ss2
  with vstorelane-inv sok2 refl
... | refl , refl
  with rt-sub-unsnoc
        (subst (λ l → Resulttype-sub (mk-list (p2 ++ valtype-V128 ∷ [])) (mk-list l))
               (sym (snoc2 p3 valtype-I32 valtype-V128)) (rt-sub-trans s22 ss1))
... | p2sub , _
  with rt-sub-unsnoc (rt-sub-trans s12 (rt-sub-trans s21 p2sub))
... | p1sub , _
  with store-write-mem s ((MEMS (frame-MODULE f)) [ proj-uN-0 32 (mk-uN 0) ]!)
         ((proj-uN-0 32 i) + (proj-uN-0 32 (OFFSET ao)))
         (coerce {B = ℕ} ((coerce {B = ℕ} v-N) / (coerce {B = ℕ} 8)))
         b-lst (≤-trans (+-monoʳ-≤ ((proj-uN-0 32 i) + (proj-uN-0 32 (OFFSET ao))) (m/n≤m v-N 8)) inb)
         (≤-reflexive (sym (tr≡ (cong length beq) (ibytes-length v-N _)))) sok
... | ext , sok' =
  mk-core ext sok' (wk-frame ext fok)
    (sub-empty (rt-sub-trans (rt-sub-trans s11 p1sub) (rt-norml p3 ss2)))

pres-step {s = s} {f = f} {Ci = Ci} sok fok ag ok (vstore-lane-val-1 _ i c v-N ao j b-lst _ inb _ _ _ beq)
  with decomp ok (admininstr-CONST I32 i ∷ [])
        (admininstr-VCONST V128 c ∷ admininstr-VSTORE-LANE V128 (mk-sz v-N) ao j ∷ []) refl
... | mk-split m1 okC1 okR
  with decomp okR (admininstr-VCONST V128 c ∷ []) (admininstr-VSTORE-LANE V128 (mk-sz v-N) ao j ∷ []) refl
... | mk-split m2 okC2 okS
  with const-ty okC1 | vconst-ty okC2 | singleton-inv okS
... | (p1 , s11 , s12) | (p2 , s21 , s22) | mk-single p3 d3 c3 sok2 ss1 ss2
  with vstorelane-inv sok2 refl
... | refl , refl
  with rt-sub-unsnoc
        (subst (λ l → Resulttype-sub (mk-list (p2 ++ valtype-V128 ∷ [])) (mk-list l))
               (sym (snoc2 p3 valtype-I32 valtype-V128)) (rt-sub-trans s22 ss1))
... | p2sub , _
  with rt-sub-unsnoc (rt-sub-trans s12 (rt-sub-trans s21 p2sub))
... | p1sub , _
  with store-write-mem s ((MEMS (frame-MODULE f)) [ proj-uN-0 32 (mk-uN 0) ]!)
         ((proj-uN-0 32 i) + (proj-uN-0 32 (OFFSET ao)))
         (coerce {B = ℕ} ((coerce {B = ℕ} v-N) / (coerce {B = ℕ} 8)))
         b-lst (≤-trans (+-monoʳ-≤ ((proj-uN-0 32 i) + (proj-uN-0 32 (OFFSET ao))) (m/n≤m v-N 8)) inb)
         (≤-reflexive (sym (tr≡ (cong length beq) (ibytes-length v-N _)))) sok
... | ext , sok' =
  mk-core ext sok' (wk-frame ext fok)
    (sub-empty (rt-sub-trans (rt-sub-trans s11 p1sub) (rt-norml p3 ss2)))

pres-step {s = s} {f = f} {Ci = Ci} sok fok ag ok (vstore-lane-val-2 _ i c v-N ao j b-lst _ inb _ _ _ beq)
  with decomp ok (admininstr-CONST I32 i ∷ [])
        (admininstr-VCONST V128 c ∷ admininstr-VSTORE-LANE V128 (mk-sz v-N) ao j ∷ []) refl
... | mk-split m1 okC1 okR
  with decomp okR (admininstr-VCONST V128 c ∷ []) (admininstr-VSTORE-LANE V128 (mk-sz v-N) ao j ∷ []) refl
... | mk-split m2 okC2 okS
  with const-ty okC1 | vconst-ty okC2 | singleton-inv okS
... | (p1 , s11 , s12) | (p2 , s21 , s22) | mk-single p3 d3 c3 sok2 ss1 ss2
  with vstorelane-inv sok2 refl
... | refl , refl
  with rt-sub-unsnoc
        (subst (λ l → Resulttype-sub (mk-list (p2 ++ valtype-V128 ∷ [])) (mk-list l))
               (sym (snoc2 p3 valtype-I32 valtype-V128)) (rt-sub-trans s22 ss1))
... | p2sub , _
  with rt-sub-unsnoc (rt-sub-trans s12 (rt-sub-trans s21 p2sub))
... | p1sub , _
  with store-write-mem s ((MEMS (frame-MODULE f)) [ proj-uN-0 32 (mk-uN 0) ]!)
         ((proj-uN-0 32 i) + (proj-uN-0 32 (OFFSET ao)))
         (coerce {B = ℕ} ((coerce {B = ℕ} v-N) / (coerce {B = ℕ} 8)))
         b-lst (≤-trans (+-monoʳ-≤ ((proj-uN-0 32 i) + (proj-uN-0 32 (OFFSET ao))) (m/n≤m v-N 8)) inb)
         (≤-reflexive (sym (tr≡ (cong length beq) (ibytes-length v-N _)))) sok
... | ext , sok' =
  mk-core ext sok' (wk-frame ext fok)
    (sub-empty (rt-sub-trans (rt-sub-trans s11 p1sub) (rt-norml p3 ss2)))

pres-step {s = s} {f = f} {Ci = Ci} sok fok ag ok (vstore-lane-val-3 _ i c v-N ao j b-lst _ inb _ _ _ beq)
  with decomp ok (admininstr-CONST I32 i ∷ [])
        (admininstr-VCONST V128 c ∷ admininstr-VSTORE-LANE V128 (mk-sz v-N) ao j ∷ []) refl
... | mk-split m1 okC1 okR
  with decomp okR (admininstr-VCONST V128 c ∷ []) (admininstr-VSTORE-LANE V128 (mk-sz v-N) ao j ∷ []) refl
... | mk-split m2 okC2 okS
  with const-ty okC1 | vconst-ty okC2 | singleton-inv okS
... | (p1 , s11 , s12) | (p2 , s21 , s22) | mk-single p3 d3 c3 sok2 ss1 ss2
  with vstorelane-inv sok2 refl
... | refl , refl
  with rt-sub-unsnoc
        (subst (λ l → Resulttype-sub (mk-list (p2 ++ valtype-V128 ∷ [])) (mk-list l))
               (sym (snoc2 p3 valtype-I32 valtype-V128)) (rt-sub-trans s22 ss1))
... | p2sub , _
  with rt-sub-unsnoc (rt-sub-trans s12 (rt-sub-trans s21 p2sub))
... | p1sub , _
  with store-write-mem s ((MEMS (frame-MODULE f)) [ proj-uN-0 32 (mk-uN 0) ]!)
         ((proj-uN-0 32 i) + (proj-uN-0 32 (OFFSET ao)))
         (coerce {B = ℕ} ((coerce {B = ℕ} v-N) / (coerce {B = ℕ} 8)))
         b-lst (≤-trans (+-monoʳ-≤ ((proj-uN-0 32 i) + (proj-uN-0 32 (OFFSET ao))) (m/n≤m v-N 8)) inb)
         (≤-reflexive (sym (tr≡ (cong length beq) (ibytes-length v-N _)))) sok
... | ext , sok' =
  mk-core ext sok' (wk-frame ext fok)
    (sub-empty (rt-sub-trans (rt-sub-trans s11 p1sub) (rt-norml p3 ss2)))

-- (i32.const i) (iNN.const c) (iNN.storeM ao) ~> eps  (packed store).
pres-step {s = s} {f = f} {Ci = Ci} sok fok ag ok (store-pack-val-0 _ i c v-n ao b-lst inb _ beq)
  with decomp ok (admininstr-CONST I32 i ∷ [])
        (admininstr-CONST I32 c ∷ admininstr-STORE I32 (just (mk-sz v-n)) ao ∷ []) refl
... | mk-split m1 okC1 okR
  with decomp okR (admininstr-CONST I32 c ∷ []) (admininstr-STORE I32 (just (mk-sz v-n)) ao ∷ []) refl
... | mk-split m2 okC2 okS
  with const-ty okC1 | const-ty okC2 | singleton-inv okS
... | (p1 , s11 , s12) | (p2 , s21 , s22) | mk-single p3 d3 c3 sok2 ss1 ss2
  with storepack-inv sok2 refl
... | t , refl , refl
  with rt-sub-unsnoc
        (subst (λ l → Resulttype-sub (mk-list (p2 ++ valtype-numtype I32 ∷ [])) (mk-list l))
               (sym (snoc2 p3 valtype-I32 t)) (rt-sub-trans s22 ss1))
... | p2sub , _
  with rt-sub-unsnoc (rt-sub-trans s12 (rt-sub-trans s21 p2sub))
... | p1sub , _
  with store-write-mem s ((MEMS (frame-MODULE f)) [ proj-uN-0 32 (mk-uN 0) ]!)
         ((proj-uN-0 32 i) + (proj-uN-0 32 (OFFSET ao)))
         (coerce {B = ℕ} ((coerce {B = ℕ} v-n) / (coerce {B = ℕ} 8)))
         b-lst inb (≤-reflexive (sym (tr≡ (cong length beq) (ibytes-length v-n _)))) sok
... | ext , sok' =
  mk-core ext sok' (wk-frame ext fok)
    (sub-empty (rt-sub-trans (rt-sub-trans s11 p1sub) (rt-norml p3 ss2)))
pres-step {s = s} {f = f} {Ci = Ci} sok fok ag ok (store-pack-val-1 _ i c v-n ao b-lst inb _ beq)
  with decomp ok (admininstr-CONST I32 i ∷ [])
        (admininstr-CONST I64 c ∷ admininstr-STORE I64 (just (mk-sz v-n)) ao ∷ []) refl
... | mk-split m1 okC1 okR
  with decomp okR (admininstr-CONST I64 c ∷ []) (admininstr-STORE I64 (just (mk-sz v-n)) ao ∷ []) refl
... | mk-split m2 okC2 okS
  with const-ty okC1 | const-ty okC2 | singleton-inv okS
... | (p1 , s11 , s12) | (p2 , s21 , s22) | mk-single p3 d3 c3 sok2 ss1 ss2
  with storepack-inv sok2 refl
... | t , refl , refl
  with rt-sub-unsnoc
        (subst (λ l → Resulttype-sub (mk-list (p2 ++ valtype-numtype I64 ∷ [])) (mk-list l))
               (sym (snoc2 p3 valtype-I32 t)) (rt-sub-trans s22 ss1))
... | p2sub , _
  with rt-sub-unsnoc (rt-sub-trans s12 (rt-sub-trans s21 p2sub))
... | p1sub , _
  with store-write-mem s ((MEMS (frame-MODULE f)) [ proj-uN-0 32 (mk-uN 0) ]!)
         ((proj-uN-0 32 i) + (proj-uN-0 32 (OFFSET ao)))
         (coerce {B = ℕ} ((coerce {B = ℕ} v-n) / (coerce {B = ℕ} 8)))
         b-lst inb (≤-reflexive (sym (tr≡ (cong length beq) (ibytes-length v-n _)))) sok
... | ext , sok' =
  mk-core ext sok' (wk-frame ext fok)
    (sub-empty (rt-sub-trans (rt-sub-trans s11 p1sub) (rt-norml p3 ss2)))

-- table.grow SUCCESS: install grown tableinst; reduct old size.
pres-step {s = s} {f = f} {Ci = Ci} sok fok ag ok (table-grow-succeed _ v-ref v-n x ti grow≢ unwrap≡)
  with decomp ok (admininstr-ref v-ref ∷ [])
        (admininstr-CONST I32 (mk-uN v-n) ∷ admininstr-TABLE-GROW x ∷ []) refl
... | mk-split m1 okR okT
  with decomp okT (admininstr-CONST I32 (mk-uN v-n) ∷ []) (admininstr-TABLE-GROW x ∷ []) refl
... | mk-split m2 okC okG
  with ref-single-ok v-ref okR | const-ty okC | singleton-inv okG
... | (rt , pR , rok , sR1 , sR2) | (p2 , s21 , s22) | mk-single p3 d3 c3 gok2 gs1 gs2
  with tgrow-inv gok2 refl
... | rt' , refl , refl
  with rt-sub-unsnoc
        (subst (λ l → Resulttype-sub (mk-list (p2 ++ valtype-numtype I32 ∷ [])) (mk-list l))
               (sym (snoc2 p3 (valtype-reftype rt') valtype-I32)) (rt-sub-trans s22 gs1))
... | p2sub , _
  with rt-sub-unsnoc (rt-sub-trans sR2 (rt-sub-trans s21 p2sub))
... | pRsub , _
  with growtable-ok s (fun-table (mk-state s f) x) ti v-n v-ref
         (maybe-just (growtable (fun-table (mk-state s f) x) v-n v-ref) grow≢ unwrap≡)
... | eti , tiok
  with store-write-tableinst s ((TABLES (frame-MODULE f)) [ proj-uN-0 32 x ]!) ti eti tiok sok
... | ext , sok' =
  mk-core ext sok' (wk-frame ext fok)
    (push1 p3 (plain _ _ _ _ _ (const _ I32 _)) (rt-sub-trans sR1 pRsub) gs2)

-- table.grow FAILURE: store unchanged, reduct i32.const (-1).
pres-step sok fok ag ok (table-grow-fail _ v-ref n x)
  with decomp ok (admininstr-ref v-ref ∷ [])
        (admininstr-CONST I32 (mk-uN n) ∷ admininstr-TABLE-GROW x ∷ []) refl
... | mk-split m1 okR okT
  with decomp okT (admininstr-CONST I32 (mk-uN n) ∷ []) (admininstr-TABLE-GROW x ∷ []) refl
... | mk-split m2 okC okG
  with ref-single-ok v-ref okR | const-ty okC | singleton-inv okG
... | (rt , pR , rok , sR1 , sR2) | (p2 , s21 , s22) | mk-single p3 d3 c3 gok2 gs1 gs2
  with tgrow-inv gok2 refl
... | rt' , refl , refl
  with rt-sub-unsnoc
        (subst (λ l → Resulttype-sub (mk-list (p2 ++ valtype-numtype I32 ∷ [])) (mk-list l))
               (sym (snoc2 p3 (valtype-reftype rt') valtype-I32)) (rt-sub-trans s22 gs1))
... | p2sub , _
  with rt-sub-unsnoc (rt-sub-trans sR2 (rt-sub-trans s21 p2sub))
... | pRsub , _ =
  mk-core (extend-store-refl _) sok fok
    (push1 p3 (plain _ _ _ _ _ (const _ I32 _)) (rt-sub-trans sR1 pRsub) gs2)

-- (i32.const i) (ref r) (table.set x) ~> eps, table x's ref[i] := r.
pres-step {s = s} {f = f} {Ci = Ci} sok fok ag ok (table-set-val _ i v-ref x _)
  with decomp ok (admininstr-CONST I32 i ∷ [])
        (admininstr-ref v-ref ∷ admininstr-TABLE-SET x ∷ []) refl
... | mk-split m1 okC okR
  with decomp okR (admininstr-ref v-ref ∷ []) (admininstr-TABLE-SET x ∷ []) refl
... | mk-split m2 okRef okT
  with const-ty okC | ref-single-ok v-ref okRef | singleton-inv okT
... | (p1 , s11 , s12) | (rt-ref , pR , rok , sR1 , sR2) | mk-single p3 d3 c3 tsok ts1 ts2
  with tset-inv tsok refl
... | (rt-ctx , lim) , refl , refl , x<C , tlkC
  with rt-sub-unsnoc
        (subst (λ l → Resulttype-sub (mk-list (pR ++ valtype-reftype rt-ref ∷ [])) (mk-list l))
               (sym (snoc2 p3 valtype-I32 (valtype-reftype rt-ctx))) (rt-sub-trans sR2 ts1))
... | pRsub , refsub
  with reftype-sub-eq refsub
... | refl
  with rt-sub-unsnoc (rt-sub-trans s12 (rt-sub-trans sR1 pRsub))
... | p1sub , _
  with frame-facts fok
... | ff
  with pw-lookup (FrameFacts.tables-ok ff)
         (subst (proj-uN-0 32 x <_) (sym (FrameFacts.taddrs-len ff))
           (subst (λ l → proj-uN-0 32 x < length l) (FrameFacts.tables-eq ff)
             (subst (λ l → proj-uN-0 32 x < length l) (Agree.tab≡ ag) x<C)))
... | xaok0 =
  let xaok = subst (λ tt → Externaddr-ok s
               (externaddr-TABLE ((TABLES (frame-MODULE f)) [ proj-uN-0 32 x ]!)) (TABLE tt))
               (subst (λ l → (l [ proj-uN-0 32 x ]!) ≡ mk-tabletype lim rt-ctx)
                      (FrameFacts.tables-eq ff)
                      (subst (λ l → (l [ proj-uN-0 32 x ]!) ≡ mk-tabletype lim rt-ctx)
                             (Agree.tab≡ ag) tlkC))
               xaok0
      a< = proj₁ (xa-table-inv xaok)
      tteq = proj₂ (proj₂ (xa-table-inv xaok))
      refokf : ∀ {lim0 rt0} →
        tableinst-TYPE ((store-TABLES s) [ (TABLES (frame-MODULE f)) [ proj-uN-0 32 x ]! ]!)
          ≡ mk-tabletype lim0 rt0 → Ref-ok s v-ref rt0
      refokf eq = subst (Ref-ok s v-ref) (tabletype-rt-inj (tr≡ (sym tteq) eq)) rok
      res = store-write-table-ref s ((TABLES (frame-MODULE f)) [ proj-uN-0 32 x ]!)
              (proj-uN-0 32 i) v-ref refokf sok
  in mk-core (proj₁ res) (proj₂ res) (wk-frame (proj₁ res) fok)
       (sub-empty (rt-sub-trans (rt-sub-trans s11 p1sub) (rt-norml p3 ts2)))

-- Trapping store-writes: the store is UNCHANGED (same z), the reduct is
-- [TRAP].  Extend-store is reflexive and TRAP types at any function type.
pres-step sok fok ag ok (table-set-trap _ _ _ _ _) =
  mk-core (extend-store-refl _) sok fok trap-ty
pres-step sok fok ag ok (store-num-trap _ _ _ _ _ _ _) =
  mk-core (extend-store-refl _) sok fok trap-ty
pres-step sok fok ag ok (store-pack-trap-0 _ _ _ _ _ _) =
  mk-core (extend-store-refl _) sok fok trap-ty
pres-step sok fok ag ok (store-pack-trap-1 _ _ _ _ _ _) =
  mk-core (extend-store-refl _) sok fok trap-ty
pres-step sok fok ag ok (vstore-oob _ _ _ _ _ _) =
  mk-core (extend-store-refl _) sok fok trap-ty
pres-step sok fok ag ok (vstore-lane-oob _ _ _ _ _ _ _) =
  mk-core (extend-store-refl _) sok fok trap-ty

-- congruence: label_n{cont} body ~> label_n{cont} body'  (body steps).
-- Recurse at the extended instruction-context labC t' ⧺ Ci; the frame
-- context Cf is unchanged, agreement transported by agree-labC.
pres-step {Ci = Ci} sok fok ag ok (ctxt-label _ vn cont body _ body' inner)
  with singleton-inv ok
... | mk-single p d c lok su1 su2
  with label-inv lok refl
... | refl , t' , lenq , contTy , bodyTy
  with pres-step sok fok (agree-labC t' ag) bodyTy inner
... | mk-core ext sok' fok' bodyTy' =
  mk-core ext sok' fok'
    (single-intro (mk-single p [] c
      (label _ Ci vn cont body' c t' lenq (instrs-weaken ext sok' contTy) bodyTy')
      su1 su2))

-- congruence: frame_n{f'} body ~> frame_n{f''} body'  (inner frame steps).
-- Recurse on the INNER frame f' at its own context C', instruction-
-- context retC c ⧺ C'; the OUTER frame f is unchanged.
pres-step {Ci = Ci} sok fok ag ok (ctxt-frame _ _ vn f' body _ f'' body' inner)
  with singleton-inv ok
... | mk-single p d c fiok su1 su2
  with frame-inv fiok refl
... | refl , lenc , C' , frok , mk-Expr-ok2 _ _ _ _ bodyTy
  with pres-step sok frok (agree-retC c agree-refl) bodyTy inner
... | mk-core ext sok' fok'' bodyTy' =
  mk-core ext sok' (wk-frame ext fok)
    (single-intro (mk-single p [] c
      (Instr-ok2--frame _ Ci vn f'' body' c C' lenc fok''
        (mk-Expr-ok2 _ _ _ c bodyTy'))
      su1 su2))

------------------------------------------------------------------------
-- 9d. THE HEADLINE THEOREM, stated purely with generated relations
--     (Config-ok, Step, Extend-store).  Complete modulo the three
--     postulates above.
------------------------------------------------------------------------

preservation : ∀ {s f es s' f' es' rt} →
  Config-ok (mk-config (mk-state s f) es) rt →
  Step (mk-config (mk-state s f) es) (mk-config (mk-state s' f') es') →
  Config-ok (mk-config (mk-state s' f') es') rt × Extend-store s s'
preservation (mk-Config-ok _ _ _ tl C (mk-State-ok _ _ _ sok fok)
               (mk-Expr-ok2 _ _ _ _ ok)) stp
  with pres-step sok fok agree-refl ok stp
... | mk-core ext sok' fok' ok' =
  mk-Config-ok _ _ _ tl C (mk-State-ok _ _ _ sok' fok')
    (mk-Expr-ok2 _ _ _ tl ok') , ext

------------------------------------------------------------------------
-- 10. PROGRESS.
------------------------------------------------------------------------

Terminal : config → Set
Terminal (mk-config z es) =
  (Σ (List val) λ vs → es ≡ map (λ v → admininstr-val v) vs) ⊎
  (es ≡ admininstr-TRAP ∷ [])

ProgressStmt : Set
ProgressStmt = ∀ c rt → Config-ok c rt →
  Terminal c ⊎ (Σ config λ c' → Step c c')

-- 10a. Redex-level progress for the scope classes (no typing needed:
-- B6 junk-totalization makes every lookup/eval total, so reads always
-- step).  Ported from attempt #1, incl. with-abstraction over the
-- totalized partial numerics.

nop-prog : Σ (List admininstr) λ es' → Step-pure (admininstr-NOP ∷ []) es'
nop-prog = [] , Step-pure--nop

unreachable-prog :
  Σ (List admininstr) λ es' → Step-pure (admininstr-UNREACHABLE ∷ []) es'
unreachable-prog = admininstr-TRAP ∷ [] , Step-pure--unreachable

drop-prog : ∀ v →
  Σ (List admininstr) λ es' → Step-pure (admininstr-val v ∷ admininstr-DROP ∷ []) es'
drop-prog v = [] , Step-pure--drop v

select-prog : ∀ v1 v2 c opt → Σ (List admininstr) λ es' →
  Step-pure (admininstr-val v1 ∷ admininstr-val v2 ∷
             admininstr-CONST I32 c ∷ admininstr-SELECT opt ∷ []) es'
select-prog v1 v2 c opt with proj-uN-0 32 c in eq
... | zero = admininstr-val v2 ∷ [] , select-false v1 v2 c opt eq
... | suc k = admininstr-val v1 ∷ [] ,
  select-true v1 v2 c opt (λ p → case tr≡ (sym p) eq of λ ())

unop-prog : ∀ nt (op : unop- nt) c1 → Σ (List admininstr) λ es' →
  Step-pure (admininstr-CONST nt c1 ∷ admininstr-UNOP nt op ∷ []) es'
unop-prog nt op c1 with fun-unop- nt op c1 in eq
... | [] = admininstr-TRAP ∷ [] , unop-trap nt c1 op eq
... | r ∷ rs = admininstr-CONST nt r ∷ [] ,
  unop-val nt c1 op r
    (subst (λ l → length l > 0) (sym eq) (s≤s z≤n))
    (subst (r ∈_) (sym eq) (here refl))

binop-prog : ∀ nt (op : binop- nt) c1 c2 → Σ (List admininstr) λ es' →
  Step-pure (admininstr-CONST nt c1 ∷ admininstr-CONST nt c2 ∷
             admininstr-BINOP nt op ∷ []) es'
binop-prog nt op c1 c2 with fun-binop- nt op c1 c2 in eq
... | [] = admininstr-TRAP ∷ [] , binop-trap nt c1 c2 op eq
... | r ∷ rs = admininstr-CONST nt r ∷ [] ,
  binop-val nt c1 c2 op r
    (subst (λ l → length l > 0) (sym eq) (s≤s z≤n))
    (subst (r ∈_) (sym eq) (here refl))

testop-prog : ∀ nt (op : testop- nt) c1 → Σ (List admininstr) λ es' →
  Step-pure (admininstr-CONST nt c1 ∷ admininstr-TESTOP nt op ∷ []) es'
testop-prog nt op c1 =
  admininstr-CONST I32 (fun-testop- nt op c1) ∷ [] ,
  Step-pure--testop nt c1 op _ refl

relop-prog : ∀ nt (op : relop- nt) c1 c2 → Σ (List admininstr) λ es' →
  Step-pure (admininstr-CONST nt c1 ∷ admininstr-CONST nt c2 ∷
             admininstr-RELOP nt op ∷ []) es'
relop-prog nt op c1 c2 =
  admininstr-CONST I32 (fun-relop- nt op c1 c2) ∷ [] ,
  Step-pure--relop nt c1 c2 op _ refl

local-get-prog : ∀ z x → Σ (List admininstr) λ es' →
  Step-read (mk-config z (admininstr-LOCAL-GET x ∷ [])) es'
local-get-prog z x = _ , Step-read--local-get z x

global-get-prog : ∀ z x → Σ (List admininstr) λ es' →
  Step-read (mk-config z (admininstr-GLOBAL-GET x ∷ [])) es'
global-get-prog z x = _ , Step-read--global-get z x

local-set-prog : ∀ z v x → Σ config λ c' →
  Step (mk-config z (admininstr-val v ∷ admininstr-LOCAL-SET x ∷ [])) c'
local-set-prog z v x = _ , Step--local-set z v x

global-set-prog : ∀ z v x → Σ config λ c' →
  Step (mk-config z (admininstr-val v ∷ admininstr-GLOBAL-SET x ∷ [])) c'
global-set-prog z v x = _ , Step--global-set z v x

-- IsVal: the five value admininstr forms.
data IsVal : admininstr → Set where
  isv-const : ∀ nt c → IsVal (admininstr-CONST nt c)
  isv-vconst : ∀ sh c → IsVal (admininstr-VCONST sh c)
  isv-null : ∀ rt → IsVal (admininstr-REF-NULL rt)
  isv-func : ∀ a → IsVal (admininstr-REF-FUNC-ADDR a)
  isv-host : ∀ a → IsVal (admininstr-REF-HOST-ADDR a)

isVal→val : ∀ {e} → IsVal e → Σ val λ v → e ≡ admininstr-val v
isVal→val (isv-const nt c) = val-CONST nt c , refl
isVal→val (isv-vconst sh c) = val-VCONST sh c , refl
isVal→val (isv-null rt) = val-REF-NULL rt , refl
isVal→val (isv-func a) = val-REF-FUNC-ADDR a , refl
isVal→val (isv-host a) = val-REF-HOST-ADDR a , refl

-- value-split: a maximal value prefix, then either nothing or a non-value head.
value-split : ∀ es →
  (Σ (List val) λ vs → es ≡ map (λ v → admininstr-val v) vs) ⊎
  (Σ (List val) λ vs → Σ admininstr λ e → Σ (List admininstr) λ rest →
     (es ≡ map (λ v → admininstr-val v) vs ++ (e ∷ rest)) × (¬ IsVal e))
value-split [] = inj₁ ([] , refl)
value-split (admininstr-NOP ∷ es) = inj₂ ([] , admininstr-NOP , es , refl , λ ())
value-split (admininstr-UNREACHABLE ∷ es) = inj₂ ([] , admininstr-UNREACHABLE , es , refl , λ ())
value-split (admininstr-DROP ∷ es) = inj₂ ([] , admininstr-DROP , es , refl , λ ())
value-split ((admininstr-SELECT a0) ∷ es) = inj₂ ([] , (admininstr-SELECT a0) , es , refl , λ ())
value-split ((admininstr-BLOCK a0 a1) ∷ es) = inj₂ ([] , (admininstr-BLOCK a0 a1) , es , refl , λ ())
value-split ((admininstr-LOOP a0 a1) ∷ es) = inj₂ ([] , (admininstr-LOOP a0 a1) , es , refl , λ ())
value-split ((admininstr-IFELSE a0 a1 a2) ∷ es) = inj₂ ([] , (admininstr-IFELSE a0 a1 a2) , es , refl , λ ())
value-split ((admininstr-BR a0) ∷ es) = inj₂ ([] , (admininstr-BR a0) , es , refl , λ ())
value-split ((admininstr-BR-IF a0) ∷ es) = inj₂ ([] , (admininstr-BR-IF a0) , es , refl , λ ())
value-split ((admininstr-BR-TABLE a0 a1) ∷ es) = inj₂ ([] , (admininstr-BR-TABLE a0 a1) , es , refl , λ ())
value-split ((admininstr-CALL a0) ∷ es) = inj₂ ([] , (admininstr-CALL a0) , es , refl , λ ())
value-split ((admininstr-CALL-INDIRECT a0 a1) ∷ es) = inj₂ ([] , (admininstr-CALL-INDIRECT a0 a1) , es , refl , λ ())
value-split (admininstr-RETURN ∷ es) = inj₂ ([] , admininstr-RETURN , es , refl , λ ())
value-split ((admininstr-CONST a0 a1) ∷ es) with value-split es
... | inj₁ (vs , eq) = inj₁ (val-CONST a0 a1 ∷ vs , cong ((admininstr-CONST a0 a1) ∷_) eq)
... | inj₂ (vs , e , rest , eq , nv) = inj₂ (val-CONST a0 a1 ∷ vs , e , rest , cong ((admininstr-CONST a0 a1) ∷_) eq , nv)
value-split ((admininstr-UNOP a0 a1) ∷ es) = inj₂ ([] , (admininstr-UNOP a0 a1) , es , refl , λ ())
value-split ((admininstr-BINOP a0 a1) ∷ es) = inj₂ ([] , (admininstr-BINOP a0 a1) , es , refl , λ ())
value-split ((admininstr-TESTOP a0 a1) ∷ es) = inj₂ ([] , (admininstr-TESTOP a0 a1) , es , refl , λ ())
value-split ((admininstr-RELOP a0 a1) ∷ es) = inj₂ ([] , (admininstr-RELOP a0 a1) , es , refl , λ ())
value-split ((admininstr-CVTOP a0 a1 a2) ∷ es) = inj₂ ([] , (admininstr-CVTOP a0 a1 a2) , es , refl , λ ())
value-split ((admininstr-EXTEND a0 a1) ∷ es) = inj₂ ([] , (admininstr-EXTEND a0 a1) , es , refl , λ ())
value-split ((admininstr-VCONST a0 a1) ∷ es) with value-split es
... | inj₁ (vs , eq) = inj₁ (val-VCONST a0 a1 ∷ vs , cong ((admininstr-VCONST a0 a1) ∷_) eq)
... | inj₂ (vs , e , rest , eq , nv) = inj₂ (val-VCONST a0 a1 ∷ vs , e , rest , cong ((admininstr-VCONST a0 a1) ∷_) eq , nv)
value-split ((admininstr-VVUNOP a0 a1) ∷ es) = inj₂ ([] , (admininstr-VVUNOP a0 a1) , es , refl , λ ())
value-split ((admininstr-VVBINOP a0 a1) ∷ es) = inj₂ ([] , (admininstr-VVBINOP a0 a1) , es , refl , λ ())
value-split ((admininstr-VVTERNOP a0 a1) ∷ es) = inj₂ ([] , (admininstr-VVTERNOP a0 a1) , es , refl , λ ())
value-split ((admininstr-VVTESTOP a0 a1) ∷ es) = inj₂ ([] , (admininstr-VVTESTOP a0 a1) , es , refl , λ ())
value-split ((admininstr-VUNOP a0 a1) ∷ es) = inj₂ ([] , (admininstr-VUNOP a0 a1) , es , refl , λ ())
value-split ((admininstr-VBINOP a0 a1) ∷ es) = inj₂ ([] , (admininstr-VBINOP a0 a1) , es , refl , λ ())
value-split ((admininstr-VTESTOP a0 a1) ∷ es) = inj₂ ([] , (admininstr-VTESTOP a0 a1) , es , refl , λ ())
value-split ((admininstr-VRELOP a0 a1) ∷ es) = inj₂ ([] , (admininstr-VRELOP a0 a1) , es , refl , λ ())
value-split ((admininstr-VSHIFTOP a0 a1) ∷ es) = inj₂ ([] , (admininstr-VSHIFTOP a0 a1) , es , refl , λ ())
value-split ((admininstr-VBITMASK a0) ∷ es) = inj₂ ([] , (admininstr-VBITMASK a0) , es , refl , λ ())
value-split ((admininstr-VSWIZZLE a0) ∷ es) = inj₂ ([] , (admininstr-VSWIZZLE a0) , es , refl , λ ())
value-split ((admininstr-VSHUFFLE a0 a1) ∷ es) = inj₂ ([] , (admininstr-VSHUFFLE a0 a1) , es , refl , λ ())
value-split ((admininstr-VSPLAT a0) ∷ es) = inj₂ ([] , (admininstr-VSPLAT a0) , es , refl , λ ())
value-split ((admininstr-VEXTRACT-LANE a0 a1 a2) ∷ es) = inj₂ ([] , (admininstr-VEXTRACT-LANE a0 a1 a2) , es , refl , λ ())
value-split ((admininstr-VREPLACE-LANE a0 a1) ∷ es) = inj₂ ([] , (admininstr-VREPLACE-LANE a0 a1) , es , refl , λ ())
value-split ((admininstr-VEXTUNOP a0 a1 a2) ∷ es) = inj₂ ([] , (admininstr-VEXTUNOP a0 a1 a2) , es , refl , λ ())
value-split ((admininstr-VEXTBINOP a0 a1 a2) ∷ es) = inj₂ ([] , (admininstr-VEXTBINOP a0 a1 a2) , es , refl , λ ())
value-split ((admininstr-VNARROW a0 a1 a2) ∷ es) = inj₂ ([] , (admininstr-VNARROW a0 a1 a2) , es , refl , λ ())
value-split ((admininstr-VCVTOP a0 a1 a2) ∷ es) = inj₂ ([] , (admininstr-VCVTOP a0 a1 a2) , es , refl , λ ())
value-split ((admininstr-REF-NULL a0) ∷ es) with value-split es
... | inj₁ (vs , eq) = inj₁ (val-REF-NULL a0 ∷ vs , cong ((admininstr-REF-NULL a0) ∷_) eq)
... | inj₂ (vs , e , rest , eq , nv) = inj₂ (val-REF-NULL a0 ∷ vs , e , rest , cong ((admininstr-REF-NULL a0) ∷_) eq , nv)
value-split ((admininstr-REF-FUNC a0) ∷ es) = inj₂ ([] , (admininstr-REF-FUNC a0) , es , refl , λ ())
value-split (admininstr-REF-IS-NULL ∷ es) = inj₂ ([] , admininstr-REF-IS-NULL , es , refl , λ ())
value-split ((admininstr-LOCAL-GET a0) ∷ es) = inj₂ ([] , (admininstr-LOCAL-GET a0) , es , refl , λ ())
value-split ((admininstr-LOCAL-SET a0) ∷ es) = inj₂ ([] , (admininstr-LOCAL-SET a0) , es , refl , λ ())
value-split ((admininstr-LOCAL-TEE a0) ∷ es) = inj₂ ([] , (admininstr-LOCAL-TEE a0) , es , refl , λ ())
value-split ((admininstr-GLOBAL-GET a0) ∷ es) = inj₂ ([] , (admininstr-GLOBAL-GET a0) , es , refl , λ ())
value-split ((admininstr-GLOBAL-SET a0) ∷ es) = inj₂ ([] , (admininstr-GLOBAL-SET a0) , es , refl , λ ())
value-split ((admininstr-TABLE-GET a0) ∷ es) = inj₂ ([] , (admininstr-TABLE-GET a0) , es , refl , λ ())
value-split ((admininstr-TABLE-SET a0) ∷ es) = inj₂ ([] , (admininstr-TABLE-SET a0) , es , refl , λ ())
value-split ((admininstr-TABLE-SIZE a0) ∷ es) = inj₂ ([] , (admininstr-TABLE-SIZE a0) , es , refl , λ ())
value-split ((admininstr-TABLE-GROW a0) ∷ es) = inj₂ ([] , (admininstr-TABLE-GROW a0) , es , refl , λ ())
value-split ((admininstr-TABLE-FILL a0) ∷ es) = inj₂ ([] , (admininstr-TABLE-FILL a0) , es , refl , λ ())
value-split ((admininstr-TABLE-COPY a0 a1) ∷ es) = inj₂ ([] , (admininstr-TABLE-COPY a0 a1) , es , refl , λ ())
value-split ((admininstr-TABLE-INIT a0 a1) ∷ es) = inj₂ ([] , (admininstr-TABLE-INIT a0 a1) , es , refl , λ ())
value-split ((admininstr-ELEM-DROP a0) ∷ es) = inj₂ ([] , (admininstr-ELEM-DROP a0) , es , refl , λ ())
value-split ((admininstr-LOAD a0 a1 a2) ∷ es) = inj₂ ([] , (admininstr-LOAD a0 a1 a2) , es , refl , λ ())
value-split ((admininstr-STORE a0 a1 a2) ∷ es) = inj₂ ([] , (admininstr-STORE a0 a1 a2) , es , refl , λ ())
value-split ((admininstr-VLOAD a0 a1 a2) ∷ es) = inj₂ ([] , (admininstr-VLOAD a0 a1 a2) , es , refl , λ ())
value-split ((admininstr-VLOAD-LANE a0 a1 a2 a3) ∷ es) = inj₂ ([] , (admininstr-VLOAD-LANE a0 a1 a2 a3) , es , refl , λ ())
value-split ((admininstr-VSTORE a0 a1) ∷ es) = inj₂ ([] , (admininstr-VSTORE a0 a1) , es , refl , λ ())
value-split ((admininstr-VSTORE-LANE a0 a1 a2 a3) ∷ es) = inj₂ ([] , (admininstr-VSTORE-LANE a0 a1 a2 a3) , es , refl , λ ())
value-split (admininstr-MEMORY-SIZE ∷ es) = inj₂ ([] , admininstr-MEMORY-SIZE , es , refl , λ ())
value-split (admininstr-MEMORY-GROW ∷ es) = inj₂ ([] , admininstr-MEMORY-GROW , es , refl , λ ())
value-split (admininstr-MEMORY-FILL ∷ es) = inj₂ ([] , admininstr-MEMORY-FILL , es , refl , λ ())
value-split (admininstr-MEMORY-COPY ∷ es) = inj₂ ([] , admininstr-MEMORY-COPY , es , refl , λ ())
value-split ((admininstr-MEMORY-INIT a0) ∷ es) = inj₂ ([] , (admininstr-MEMORY-INIT a0) , es , refl , λ ())
value-split ((admininstr-DATA-DROP a0) ∷ es) = inj₂ ([] , (admininstr-DATA-DROP a0) , es , refl , λ ())
value-split ((admininstr-REF-FUNC-ADDR a0) ∷ es) with value-split es
... | inj₁ (vs , eq) = inj₁ (val-REF-FUNC-ADDR a0 ∷ vs , cong ((admininstr-REF-FUNC-ADDR a0) ∷_) eq)
... | inj₂ (vs , e , rest , eq , nv) = inj₂ (val-REF-FUNC-ADDR a0 ∷ vs , e , rest , cong ((admininstr-REF-FUNC-ADDR a0) ∷_) eq , nv)
value-split ((admininstr-REF-HOST-ADDR a0) ∷ es) with value-split es
... | inj₁ (vs , eq) = inj₁ (val-REF-HOST-ADDR a0 ∷ vs , cong ((admininstr-REF-HOST-ADDR a0) ∷_) eq)
... | inj₂ (vs , e , rest , eq , nv) = inj₂ (val-REF-HOST-ADDR a0 ∷ vs , e , rest , cong ((admininstr-REF-HOST-ADDR a0) ∷_) eq , nv)
value-split ((CALL-ADDR a0) ∷ es) = inj₂ ([] , (CALL-ADDR a0) , es , refl , λ ())
value-split ((LABEL- a0 a1 a2) ∷ es) = inj₂ ([] , (LABEL- a0 a1 a2) , es , refl , λ ())
value-split ((FRAME- a0 a1 a2) ∷ es) = inj₂ ([] , (FRAME- a0 a1 a2) , es , refl , λ ())
value-split (admininstr-TRAP ∷ es) = inj₂ ([] , admininstr-TRAP , es , refl , λ ())

-- 10b. The progress spine.  With `value-split` above, progress-decompose
-- is now the standard Wright/Felleisen argument: a well-typed sequence is
-- either an all-value row, or has a first non-value head e (with a value
-- prefix vs providing its operands).  The general SpecTec evaluation
-- context E[_] is available as the `ctxt-instrs` congruence, so a focused
-- step of the redex around e lifts to the whole sequence (`wrap-step`).
-- The remaining work is purely per-instruction: for each non-value head e,
-- exhibit a firing reduction from its typing (progress-nonval).  That
-- per-instruction case analysis (74 admininstr forms) is scaffolded by
-- `progress-rest` and filled incrementally below.

snoc-view : ∀ {A : Set} (xs : List A) →
  (xs ≡ []) ⊎ (Σ (List A) λ ys → Σ A λ y → xs ≡ ys ++ (y ∷ []))
snoc-view [] = inj₁ refl
snoc-view (x ∷ xs) with snoc-view xs
... | inj₁ refl = inj₂ ([] , x , refl)
... | inj₂ (ys , y , refl) = inj₂ (x ∷ ys , y , refl)

-- Congruence: a focused step of [e] (possibly changing the state) lifts to
-- the full sequence `map val vs ++ e ∷ rest` via ctxt-instrs.
wrap-step : ∀ {s f s'' f'' e mid'} (vs : List val) (rest : List admininstr) →
  Step (mk-config (mk-state s f) (e ∷ [])) (mk-config (mk-state s'' f'') mid') →
  Σ config λ c' → Step (mk-config (mk-state s f) (map (λ v → admininstr-val v) vs ++ (e ∷ rest))) c'
wrap-step [] [] st = _ , st
wrap-step {e = e} [] (r ∷ rest) st =
  _ , ctxt-instrs _ [] (e ∷ []) (r ∷ rest) _ _ st (inj₂ (λ ()))
wrap-step {e = e} (v ∷ vs) rest st =
  _ , ctxt-instrs _ (v ∷ vs) (e ∷ []) rest _ _ st (inj₁ (λ ()))

-- Same congruence for a multi-instruction focused redex `mid`.
wrap-any : ∀ {s f s'' f'' mid mid'} (vs' : List val) (rest : List admininstr) →
  Step (mk-config (mk-state s f) mid) (mk-config (mk-state s'' f'') mid') →
  Σ config λ c' → Step (mk-config (mk-state s f) (map (λ v → admininstr-val v) vs' ++ (mid ++ rest))) c'
wrap-any [] [] st = _ , subst (λ z → Step (mk-config _ z) _) (sym (++-identityʳ _)) st
wrap-any {mid = mid} [] (r ∷ rest) st = _ , ctxt-instrs _ [] mid (r ∷ rest) _ _ st (inj₂ (λ ()))
wrap-any {mid = mid} (v ∷ vs') rest st = _ , ctxt-instrs _ (v ∷ vs') mid rest _ _ st (inj₁ (λ ()))

-- A closed (input []) sequence whose head is DROP is untypable: DROP needs
-- one operand but the value prefix is empty.
drop-nil-⊥ : ∀ {s C rest u2} →
  Instrs-ok2 s C (admininstr-DROP ∷ rest) (mk-functype (mk-list []) (mk-list u2)) → ⊥
drop-nil-⊥ ok with decomp ok (admininstr-DROP ∷ []) _ refl
... | mk-split m okD okRest with singleton-inv okD
... | mk-single p d c dok s1 s2 with drop-inv dok refl
... | t , refl , refl with s1
... | mk-Resulttype-sub _ _ leq _
  with tr≡ leq (tr≡ (length-++ p {t ∷ []}) (+-comm (length p) 1))
... | ()

-- ===== Progress: operand extraction + firing machinery =====
list-view : ∀ {A : Set} (xs : List A) → (xs ≡ []) ⊎ (Σ A λ x → (x ∈ xs) × (0 < length xs))
list-view [] = inj₁ refl
list-view (x ∷ xs) = inj₂ (x , here refl , s≤s z≤n)

nothing≢just : ∀ {A : Set} {a : A} → (nothing ≡ just a) → ⊥
nothing≢just ()

i+n≤⇒i< : ∀ {i m n} → i + n ≤ m → n ≢ 0 → i < m
i+n≤⇒i< {n = 0} le n≠ = ⊥-elim (n≠ refl)
i+n≤⇒i< {i} {m} {n = suc n'} le _ = ≤-trans (s≤s (m≤m+n i n')) (subst (λ z → z ≤ m) (+-suc i n') le)

nt-size≢nothing : ∀ (nt : numtype) → size (valtype-numtype nt) ≢ nothing
nt-size≢nothing I32 ()
nt-size≢nothing I64 ()
nt-size≢nothing F32 ()
nt-size≢nothing F64 ()

-- An in-bounds slice has exactly the requested length.
slice-len : ∀ {A : Set} (xs : List A) (start len : ℕ) →
  start + len ≤ length xs → length (slice xs start len) ≡ len
slice-len xs start len le =
  tr≡ (length-take len (drop start xs))
    (tr≡ (cong (len ⊓_) (length-drop start xs))
      (m≤n⇒m⊓n≡m (subst (_≤ length xs ∸ start) (m+n∸m≡n start len) (∸-monoˡ-≤ start le))))

-- BACKEND-LIMITATION (dropped shape-width refinement) axiom, G4 class.
-- `SHAPEX- v-M v-N sx` (vloadop, from sz-like ℕ params, line 1577) — the typing `vload`
-- (6-typing.spectec:496) has no `jsize Jnn = v-M·2` constraint, so a generic v-M is typeable-but-stuck.
-- TRUE of the real language; deletable once the half-lane width is a bounded enum.
data VShapeW : ℕ → Set where
  vshw-i32 : VShapeW 16
  vshw-i64 : VShapeW 32
  vshw-i8  : VShapeW 4
  vshw-i16 : VShapeW 8

postulate
  vload-shape-width : ∀ {s C e v-M v-N v-sx ao d cc} →
    Instr-ok2 s C e (mk-functype (mk-list d) (mk-list cc)) → e ≡ admininstr-VLOAD V128 (just (SHAPEX- v-M v-N v-sx)) ao →
    VShapeW v-M

iok-vshape : ∀ {C v-M v-N v-sx ao d cc} → Instr-ok C (VLOAD V128 (just (SHAPEX- v-M v-N v-sx)) ao) (mk-functype (mk-list d) (mk-list cc)) →
  (d ≡ valtype-I32 ∷ []) × (cc ≡ valtype-V128 ∷ [])
iok-vshape (vload _ _ _ _ _ _ _ _ _) = refl , refl
vshape-inv : ∀ {s C e v-M v-N v-sx ao d cc} → Instr-ok2 s C e (mk-functype (mk-list d) (mk-list cc)) → e ≡ admininstr-VLOAD V128 (just (SHAPEX- v-M v-N v-sx)) ao →
  (d ≡ valtype-I32 ∷ []) × (cc ≡ valtype-V128 ∷ [])
vshape-inv (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-vshape iok
vshape-inv (label _ _ _ _ _ _ _ _ _ _) ()
vshape-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
vshape-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
vshape-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
vshape-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
vshape-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
vshape-inv (Instr-ok2--trap _ _ _ _) ()

-- Deserialize N consecutive M-bit lanes (derived from ibytes-surj via foralli-build; per-chunk bound via chunk-bound).
list-surj : ∀ (M : ℕ) (bs : List byte) (base N : ℕ) → (base + ((M * N) / 8)) ≤ length bs →
  Σ (List (uN-fam0 M)) λ jl → (length jl ≡ N) × Foralli (λ k j → ibytes- M j ≡ slice bs (base + ((k * M) / 8)) (M / 8)) jl
list-surj M bs base N le with foralli-build N (λ k k<N → ibytes-surj M (slice bs (base + ((k * M) / 8)) (M / 8))
       (slice-len bs (base + ((k * M) / 8)) (M / 8)
         (≤-trans (≤-reflexive (+-assoc base ((k * M) / 8) (M / 8)))
           (≤-trans (+-monoʳ-≤ base (chunk-bound M N k k<N)) le))))
... | jl , lenq , pw = jl , lenq , subst (λ n → Pointwise (λ k j → ibytes- M j ≡ slice bs (base + ((k * M) / 8)) (M / 8)) (upTo n) jl) (sym lenq) pw

-- valtype-numtype is a coercion function; make its injectivity/discrimination explicit.
vnt-inj : ∀ {nt nt'} → valtype-numtype nt ≡ valtype-numtype nt' → nt ≡ nt'
vnt-inj {I32} {I32} _ = refl
vnt-inj {I32} {I64} ()
vnt-inj {I32} {F32} ()
vnt-inj {I32} {F64} ()
vnt-inj {I64} {I32} ()
vnt-inj {I64} {I64} _ = refl
vnt-inj {I64} {F32} ()
vnt-inj {I64} {F64} ()
vnt-inj {F32} {I32} ()
vnt-inj {F32} {I64} ()
vnt-inj {F32} {F32} _ = refl
vnt-inj {F32} {F64} ()
vnt-inj {F64} {I32} ()
vnt-inj {F64} {I64} ()
vnt-inj {F64} {F32} ()
vnt-inj {F64} {F64} _ = refl
vnt≢vec : ∀ {nt vt} → valtype-numtype nt ≡ valtype-vectype vt → ⊥
vnt≢vec {I32} {V128} ()
vnt≢vec {I64} {V128} ()
vnt≢vec {F32} {V128} ()
vnt≢vec {F64} {V128} ()
vnt≢ref : ∀ {nt rt} → valtype-numtype nt ≡ valtype-reftype rt → ⊥
vnt≢ref {I32} {FUNCREF} ()
vnt≢ref {I32} {EXTERNREF} ()
vnt≢ref {I64} {FUNCREF} ()
vnt≢ref {I64} {EXTERNREF} ()
vnt≢ref {F32} {FUNCREF} ()
vnt≢ref {F32} {EXTERNREF} ()
vnt≢ref {F64} {FUNCREF} ()
vnt≢ref {F64} {EXTERNREF} ()

vV128≢num : ∀ {nt} → valtype-V128 ≡ valtype-numtype nt → ⊥
vV128≢num {I32} ()
vV128≢num {I64} ()
vV128≢num {F32} ()
vV128≢num {F64} ()
vV128≢ref : ∀ {rt} → valtype-V128 ≡ valtype-reftype rt → ⊥
vV128≢ref {FUNCREF} ()
vV128≢ref {EXTERNREF} ()

-- Value typing inversion (returns type equations, dodging the coercion-index match).
val-ok-inv : ∀ {s v t} → Val-ok s v t →
  (Σ numtype λ nt → Σ (num- nt) λ c → (v ≡ val-CONST nt c) × (t ≡ valtype-numtype nt)) ⊎
  (Σ vectype λ vt → Σ (uN-fam0 (unwrap! (size (valtype-vectype vt)))) λ c → (v ≡ val-VCONST vt c) × (t ≡ valtype-vectype vt)) ⊎
  (Σ ref λ r → Σ reftype λ rt → (v ≡ val-ref r) × (t ≡ valtype-reftype rt) × Ref-ok s r rt)
val-ok-inv (Val-ok--numtype _ nt c) = inj₁ (nt , c , refl , refl)
val-ok-inv (Val-ok--vectype _ vt c) = inj₂ (inj₁ (vt , c , refl , refl))
val-ok-inv (Val-ok--reftype _ r rt rok) = inj₂ (inj₂ (r , rt , refl , refl , rok))

canonical-num : ∀ {s v nt} → Val-ok s v (valtype-numtype nt) → Σ (num- nt) λ c → v ≡ val-CONST nt c
canonical-num vok with val-ok-inv vok
... | inj₁ (nt' , c , veq , teq) with vnt-inj teq
...   | refl = c , veq
canonical-num vok | inj₂ (inj₁ (vt , c , veq , teq)) = ⊥-elim (vnt≢vec teq)
canonical-num vok | inj₂ (inj₂ (r , rt , veq , teq , rok)) = ⊥-elim (vnt≢ref teq)

canonical-vec : ∀ {s v} → Val-ok s v valtype-V128 → Σ (uN-fam0 128) λ c → v ≡ val-VCONST V128 c
canonical-vec vok with val-ok-inv vok
... | inj₁ (nt , c , veq , teq) = ⊥-elim (vV128≢num teq)
... | inj₂ (inj₁ (V128 , c , veq , teq)) = c , veq
canonical-vec vok | inj₂ (inj₂ (r , rt , veq , teq , rok)) = ⊥-elim (vV128≢ref teq)

canonical-ref : ∀ {s v rt} → Val-ok s v (valtype-reftype rt) → Σ ref λ r → v ≡ val-ref r
canonical-ref vok with val-ok-inv vok
... | inj₁ (nt , c , veq , teq) = ⊥-elim (vnt≢ref (sym teq))
... | inj₂ (inj₁ (V128 , c , veq , teq)) = ⊥-elim (vV128≢ref (sym teq))
... | inj₂ (inj₂ (r , rt , veq , teq , rok)) = r , veq

-- A reftype value re-expressed as an admin ref (the two admininstr injections agree).
val-ref-admin : ∀ (r : ref) → admininstr-val (val-ref r) ≡ admininstr-ref r
val-ref-admin (ref-REF-NULL x) = refl
val-ref-admin (REF-FUNC-ADDR x) = refl
val-ref-admin (REF-HOST-ADDR x) = refl

funcaddr≢refnull : ∀ {a rt} → REF-FUNC-ADDR a ≡ ref-REF-NULL rt → ⊥
funcaddr≢refnull ()
hostaddr≢refnull : ∀ {a rt} → REF-HOST-ADDR a ≡ ref-REF-NULL rt → ⊥
hostaddr≢refnull ()

-- Keep the derivation's index a plain variable `es` (so the split is trivial, dodging the `as`
-- constructor-index unification), returning the shape equation; then combine via head-injectivity.
before-ref-null : ∀ {es} → Step-pure-before-ref-is-null-false es →
  Σ ref λ r → Σ reftype λ rt → (es ≡ admininstr-ref r ∷ admininstr-REF-IS-NULL ∷ []) × (r ≡ ref-REF-NULL rt)
before-ref-null (ref-is-null-true-0 v-ref rt eq) = v-ref , rt , refl , eq

adm-ref-of : admininstr → ref
adm-ref-of (admininstr-REF-NULL rt) = ref-REF-NULL rt
adm-ref-of (admininstr-REF-FUNC-ADDR a) = REF-FUNC-ADDR a
adm-ref-of (admininstr-REF-HOST-ADDR a) = REF-HOST-ADDR a
adm-ref-of _ = ref-REF-NULL FUNCREF

adm-ref-of∘ref : ∀ (r : ref) → adm-ref-of (admininstr-ref r) ≡ r
adm-ref-of∘ref (ref-REF-NULL rt) = refl
adm-ref-of∘ref (REF-FUNC-ADDR a) = refl
adm-ref-of∘ref (REF-HOST-ADDR a) = refl

list-head-ref : List admininstr → ref
list-head-ref xs = adm-ref-of (xs [ 0 ]!)

iok-refisnull : ∀ {C d c} → Instr-ok C REF-IS-NULL (mk-functype (mk-list d) (mk-list c)) →
  Σ reftype λ rt → (d ≡ valtype-reftype rt ∷ []) × (c ≡ valtype-I32 ∷ [])
iok-refisnull (ref-is-null _ rt) = rt , refl , refl

refisnull-inv : ∀ {s C e d c} → Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) → e ≡ admininstr-REF-IS-NULL →
  Σ reftype λ rt → (d ≡ valtype-reftype rt ∷ []) × (c ≡ valtype-I32 ∷ [])
refisnull-inv (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-refisnull iok
refisnull-inv (label _ _ _ _ _ _ _ _ _ _) ()
refisnull-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
refisnull-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
refisnull-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
refisnull-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
refisnull-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
refisnull-inv (Instr-ok2--trap _ _ _ _) ()

-- instr-EXTEND has no Instr-ok rule in the source (the real iN.extendM_s is the `unop` EXTEND,
-- handled by UNOP); the standalone EXTEND instruction (1-syntax.spectec:437) is a dead artifact,
-- so admininstr-EXTEND is never well-typed.
iok-extend-imposs : ∀ {C nt n ft} → Instr-ok C (instr-EXTEND nt n) ft → ⊥
iok-extend-imposs ()

extend-imposs : ∀ {s C e nt n d c} →
  Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) → e ≡ admininstr-EXTEND nt n → ⊥
extend-imposs (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-extend-imposs iok
extend-imposs (label _ _ _ _ _ _ _ _ _ _) ()
extend-imposs (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
extend-imposs (Instr-ok2--call-addr _ _ _ _ _ _) ()
extend-imposs (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
extend-imposs (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
extend-imposs (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
extend-imposs (Instr-ok2--trap _ _ _ _) ()

nil-cons-⊥ : ∀ {p} {t : valtype} → Resulttype-sub (mk-list []) (mk-list (p ++ (t ∷ []))) → ⊥
nil-cons-⊥ {p} (mk-Resulttype-sub _ _ leq _)
  with tr≡ leq (tr≡ (length-++ p {_ ∷ []}) (+-comm (length p) 1))
... | ()

len-cons-nil-⊥ : ∀ {A B : Set} {R : A → B → Set} {ts0 : List A} {tl} →
  Forall₂ R (ts0 ++ (tl ∷ [])) [] → ⊥
len-cons-nil-⊥ {ts0 = ts0} pwv
  with tr≡ (sym (tr≡ (length-++ ts0 {_ ∷ []}) (+-comm (length ts0) 1))) (pw-length pwv)
... | ()

-- Extract e's typing (from the sequence) plus the value-row typing and its
-- subtyping into e's domain.
focus : ∀ {s C vs e rest u2} →
  Instrs-ok2 s C (map (λ w → admininstr-val w) vs ++ (e ∷ rest)) (mk-functype (mk-list []) (mk-list u2)) →
  Σ (List valtype) λ d → Σ (List valtype) λ c → Σ (List valtype) λ p → Σ (List valtype) λ ts →
    Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) ×
    Forall₂ (λ t v → Val-ok s v t) ts vs ×
    Resulttype-sub (mk-list ts) (mk-list (p ++ d))
focus {vs = vs} {e = e} {rest = rest} ok
  with decomp ok (map (λ w → admininstr-val w) vs) (e ∷ rest) refl
... | mk-split m row erest with row-inv vs row
... | ts , pwv , rsub with decomp erest (e ∷ []) rest refl
... | mk-split m' eok restok with singleton-inv eok
... | mk-single p d c e-iok s1 s2 = d , c , p , ts , e-iok , pwv , rt-sub-trans rsub s1

-- Peel the top operand of a value row whose types subtype p ++ [t].
last-val : ∀ {s vs ts p} {t : valtype} →
  Forall₂ (λ t' v → Val-ok s v t') ts vs →
  Resulttype-sub (mk-list ts) (mk-list (p ++ (t ∷ []))) →
  Σ (List val) λ vs0 → Σ val λ v → Σ (List valtype) λ ts0 →
    (vs ≡ vs0 ++ (v ∷ [])) × Val-ok s v t ×
    Forall₂ (λ t' w → Val-ok s w t') ts0 vs0 × Resulttype-sub (mk-list ts0) (mk-list p)
last-val {vs = vs} {ts = ts} pwv rt with snoc-view ts
... | inj₁ refl = ⊥-elim (nil-cons-⊥ rt)
... | inj₂ (ts0 , tl , refl) with snoc-view vs
...   | inj₁ refl = ⊥-elim (len-cons-nil-⊥ pwv)
...   | inj₂ (vs0 , v , refl) with pw-unsnoc ts0 vs0 pwv | rt-sub-unsnoc rt
...     | (pwv0 , vlok) | (rt0 , tlsub) =
          vs0 , v , ts0 , refl , subst (Val-ok _ v) (sym (vt-sub-val vlok tlsub)) vlok , pwv0 , rt0

-- Peel the top two operands.
last-2 : ∀ {s vs ts p} {t1 t2 : valtype} →
  Forall₂ (λ t' v → Val-ok s v t') ts vs →
  Resulttype-sub (mk-list ts) (mk-list (p ++ (t1 ∷ t2 ∷ []))) →
  Σ (List val) λ vs0 → Σ val λ v1 → Σ val λ v2 →
    (vs ≡ vs0 ++ (v1 ∷ v2 ∷ [])) × Val-ok s v1 t1 × Val-ok s v2 t2
last-2 {p = p} {t1 = t1} {t2 = t2} pwv rt
  with last-val pwv (subst (λ l → Resulttype-sub (mk-list _) (mk-list l)) (sym (++-assoc p (t1 ∷ []) (t2 ∷ []))) rt)
... | vs0' , v2 , ts0' , eq2 , v2ok , pwv' , rt' with last-val pwv' rt'
...   | vs0 , v1 , ts0 , eq1 , v1ok , pwv0 , rt0 =
        vs0 , v1 , v2 ,
        tr≡ eq2 (tr≡ (cong (_++ (v2 ∷ [])) eq1) (++-assoc vs0 (v1 ∷ []) (v2 ∷ []))) , v1ok , v2ok

last-3 : ∀ {s vs ts p} {t1 t2 t3 : valtype} →
  Forall₂ (λ t' v → Val-ok s v t') ts vs →
  Resulttype-sub (mk-list ts) (mk-list (p ++ (t1 ∷ t2 ∷ t3 ∷ []))) →
  Σ (List val) λ vs0 → Σ val λ v1 → Σ val λ v2 → Σ val λ v3 →
    (vs ≡ vs0 ++ (v1 ∷ v2 ∷ v3 ∷ [])) × Val-ok s v1 t1 × Val-ok s v2 t2 × Val-ok s v3 t3
last-3 {p = p} {t1 = t1} {t2 = t2} {t3 = t3} pwv rt
  with last-val pwv (subst (λ l → Resulttype-sub (mk-list _) (mk-list l)) (sym (++-assoc p (t1 ∷ t2 ∷ []) (t3 ∷ []))) rt)
... | vs0' , v3 , ts0' , eq3 , v3ok , pwv' , rt' with last-2 pwv' rt'
...   | vs0 , v1 , v2 , eq12 , v1ok , v2ok =
        vs0 , v1 , v2 , v3 ,
        tr≡ eq3 (tr≡ (cong (_++ (v3 ∷ [])) eq12) (++-assoc vs0 (v1 ∷ v2 ∷ []) (v3 ∷ []))) , v1ok , v2ok , v3ok

-- Peel just the top i32 operand of an op whose domain ends in valtype-I32.
peel-top-i32 : ∀ {s vs ts p d q} →
  Forall₂ (λ t v → Val-ok s v t) ts vs →
  Resulttype-sub (mk-list ts) (mk-list (p ++ d)) →
  d ≡ q ++ (valtype-I32 ∷ []) →
  Σ (List val) λ vs0 → Σ (uN-fam0 32) λ c → vs ≡ vs0 ++ (val-CONST I32 c ∷ [])
peel-top-i32 {p = p} {q = q} pwv rt deq
  with last-val pwv (subst (λ l → Resulttype-sub (mk-list _) (mk-list l))
        (tr≡ (cong (p ++_) deq) (sym (++-assoc p q (valtype-I32 ∷ [])))) rt)
... | vs0 , v , _ , refl , vok , _ , _ with canonical-num {nt = I32} vok
... | c , refl = vs0 , c , refl

iok-ltee : ∀ {C x d c} → Instr-ok C (LOCAL-TEE x) (mk-functype (mk-list d) (mk-list c)) → Σ valtype λ t → d ≡ t ∷ []
iok-ltee (local-tee _ _ t _ _) = t , refl
ltee-inv : ∀ {s C e d c x} → Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) → e ≡ admininstr-LOCAL-TEE x →
  Σ valtype λ t → d ≡ t ∷ []
ltee-inv (plain _ _ i _ _ iok) eq with recover eq refl
... | refl = iok-ltee iok
ltee-inv (label _ _ _ _ _ _ _ _ _ _) ()
ltee-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
ltee-inv (Instr-ok2--call-addr _ _ _ _ _ _) ()
ltee-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
ltee-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
ltee-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
ltee-inv (Instr-ok2--trap _ _ _ _) ()


-- Lift a one/two-operand focused redex to the whole sequence.
fire1 : ∀ {s f s'' f'' e mid' vs0 v rest} →
  Step (mk-config (mk-state s f) (admininstr-val v ∷ e ∷ [])) (mk-config (mk-state s'' f'') mid') →
  Σ config λ c' → Step (mk-config (mk-state s f)
    (map (λ w → admininstr-val w) (vs0 ++ (v ∷ [])) ++ (e ∷ rest))) c'
fire1 {e = e} {vs0 = vs0} {v = v} {rest = rest} st =
  subst (λ z → Σ config λ c' → Step (mk-config (mk-state _ _) z) c')
    (sym (tr≡ (cong (_++ (e ∷ rest)) (map-++ (λ w → admininstr-val w) vs0 (v ∷ [])))
             (++-assoc (map (λ w → admininstr-val w) vs0) (admininstr-val v ∷ []) (e ∷ rest))))
    (wrap-any vs0 rest st)

fire2 : ∀ {s f s'' f'' e mid' vs0 v1 v2 rest} →
  Step (mk-config (mk-state s f) (admininstr-val v1 ∷ admininstr-val v2 ∷ e ∷ [])) (mk-config (mk-state s'' f'') mid') →
  Σ config λ c' → Step (mk-config (mk-state s f)
    (map (λ w → admininstr-val w) (vs0 ++ (v1 ∷ v2 ∷ [])) ++ (e ∷ rest))) c'
fire2 {e = e} {vs0 = vs0} {v1 = v1} {v2 = v2} {rest = rest} st =
  subst (λ z → Σ config λ c' → Step (mk-config (mk-state _ _) z) c')
    (sym (tr≡ (cong (_++ (e ∷ rest)) (map-++ (λ w → admininstr-val w) vs0 (v1 ∷ v2 ∷ [])))
             (++-assoc (map (λ w → admininstr-val w) vs0) (admininstr-val v1 ∷ admininstr-val v2 ∷ []) (e ∷ rest))))
    (wrap-any vs0 rest st)

fire3 : ∀ {s f s'' f'' e mid' vs0 v1 v2 v3 rest} →
  Step (mk-config (mk-state s f) (admininstr-val v1 ∷ admininstr-val v2 ∷ admininstr-val v3 ∷ e ∷ [])) (mk-config (mk-state s'' f'') mid') →
  Σ config λ c' → Step (mk-config (mk-state s f)
    (map (λ w → admininstr-val w) (vs0 ++ (v1 ∷ v2 ∷ v3 ∷ [])) ++ (e ∷ rest))) c'
fire3 {e = e} {vs0 = vs0} {v1 = v1} {v2 = v2} {v3 = v3} {rest = rest} st =
  subst (λ z → Σ config λ c' → Step (mk-config (mk-state _ _) z) c')
    (sym (tr≡ (cong (_++ (e ∷ rest)) (map-++ (λ w → admininstr-val w) vs0 (v1 ∷ v2 ∷ v3 ∷ [])))
             (++-assoc (map (λ w → admininstr-val w) vs0) (admininstr-val v1 ∷ admininstr-val v2 ∷ admininstr-val v3 ∷ []) (e ∷ rest))))
    (wrap-any vs0 rest st)

-- Re-type a value row at supertypes (values are never BOT).
row-retype : ∀ {s ts d vs} → Forall₂ (λ t v → Val-ok s v t) ts vs →
  Pointwise Valtype-sub ts d → Forall₂ (λ t v → Val-ok s v t) d vs
row-retype [] [] = []
row-retype (vok ∷ pwv) (vsub ∷ psub) = subst (Val-ok _ _) (sym (vt-sub-val vok vsub)) vok ∷ row-retype pwv psub

-- Peel exactly the domain d (a whole value row) off the value prefix.
peel-row : ∀ {s} (p : List valtype) {ts vs d} →
  Forall₂ (λ t v → Val-ok s v t) ts vs →
  Resulttype-sub (mk-list ts) (mk-list (p ++ d)) →
  Σ (List val) λ vs0 → Σ (List val) λ vs1 →
    (vs ≡ vs0 ++ vs1) × Forall₂ (λ t v → Val-ok s v t) d vs1
peel-row [] pwv (mk-Resulttype-sub _ _ _ psub) = [] , _ , refl , row-retype pwv psub
peel-row (x ∷ p) (vok ∷ pwv') (mk-Resulttype-sub _ _ _ (vsub ∷ psub'))
  with peel-row p pwv' (mk-Resulttype-sub _ _ (pw-length psub') psub')
... | vs0 , vs1 , eq , fd = _ ∷ vs0 , vs1 , cong (_ ∷_) eq , fd

-- Lift a redex `map val vs1 ++ [e]` (variable value row) to the whole sequence.
fire-row : ∀ {s f s'' f'' e mid' vs0 vs1 rest} →
  Step (mk-config (mk-state s f) (map (λ w → admininstr-val w) vs1 ++ (e ∷ []))) (mk-config (mk-state s'' f'') mid') →
  Σ config λ c' → Step (mk-config (mk-state s f)
    (map (λ w → admininstr-val w) (vs0 ++ vs1) ++ (e ∷ rest))) c'
fire-row {e = e} {vs0 = vs0} {vs1 = vs1} {rest = rest} st =
  subst (λ z → Σ config λ c' → Step (mk-config (mk-state _ _) z) c')
    (sym (tr≡ (cong (_++ (e ∷ rest)) (map-++ (λ w → admininstr-val w) vs0 vs1))
             (tr≡ (++-assoc (map (λ w → admininstr-val w) vs0) (map (λ w → admininstr-val w) vs1) (e ∷ rest))
                  (cong (map (λ w → admininstr-val w) vs0 ++_)
                        (sym (++-assoc (map (λ w → admininstr-val w) vs1) (e ∷ []) rest))))))
    (wrap-any vs0 rest st)

-- (The former `progress-rest` / `TEMP-batch-e` scaffold postulates are GONE:
-- every admininstr head is now discharged by the explicit Batch E dispatch below.)

-- Structural size of an admininstr sequence, counting nested LABEL-/FRAME-
-- bodies.  Used as the well-founded measure for the body-progress recursion
-- (value-split defeats syntactic subterm ordering, so we recurse on adm-size).
mutual
  adm-size1 : admininstr → ℕ
  adm-size1 (LABEL- _ _ body) = suc (adm-size body)
  adm-size1 (FRAME- _ _ body) = suc (adm-size body)
  adm-size1 _ = 1
  adm-size : List admininstr → ℕ
  adm-size [] = 0
  adm-size (e ∷ es) = adm-size1 e + adm-size es

adm-size-++ : ∀ xs ys → adm-size (xs ++ ys) ≡ adm-size xs + adm-size ys
adm-size-++ [] ys = refl
adm-size-++ (x ∷ xs) ys rewrite adm-size-++ xs ys =
  sym (+-assoc (adm-size1 x) (adm-size xs) (adm-size ys))

private
  lt-mid : ∀ a m b → m < a + (suc m + b)
  lt-mid a m b = subst (m <_) (sym (+-suc a (m + b)))
    (s≤s (≤-trans (m≤m+n m b) (m≤n+m (m + b) a)))

-- adm-size of a LABEL-/FRAME- body is strictly below the size of the whole
-- value-prefixed sequence it sits in.
size-label : ∀ (vs : List val) n instrs body rest →
  adm-size body < adm-size (map (λ v → admininstr-val v) vs ++ ((LABEL- n instrs body) ∷ rest))
size-label vs n instrs body rest
  rewrite adm-size-++ (map (λ v → admininstr-val v) vs) ((LABEL- n instrs body) ∷ rest) =
  lt-mid (adm-size (map (λ v → admininstr-val v) vs)) (adm-size body) (adm-size rest)

size-frame : ∀ (vs : List val) n fr body rest →
  adm-size body < adm-size (map (λ v → admininstr-val v) vs ++ ((FRAME- n fr body) ∷ rest))
size-frame vs n fr body rest
  rewrite adm-size-++ (map (λ v → admininstr-val v) vs) ((FRAME- n fr body) ∷ rest) =
  lt-mid (adm-size (map (λ v → admininstr-val v) vs)) (adm-size body) (adm-size rest)

-- ===== REDUCTION-GENERALIZATION (construction) axioms — distinct, weaker subclass =====
-- These are the five discarding propagation rules generalised from a source
-- `instr*` tail to an `admininstr*` tail.
--
--   Root cause.  A LABEL_ body is `admininstr*` [4-runtime.spectec:133], and
--   Instrs_ok2 types it as such, so a config like
--       LABEL n {} (val^n (BR 0) TRAP)
--   is well-typed.  But the propagation rules
--       br-zero [8-reduction.spectec:141], br-succ [:144], return-label [:150],
--       return-frame [:95], trap-vals [:92]  (rendered as wasm2-sound-check.agda
--       br-zero 3766 / br-succ 3769 / return-label 3788 / return-frame 3785 /
--       trap-vals 3789)
--   match/discard the code after the control head as source `instr*`
--   (`map admininstr-instr instr-lst`).  Such admin-tailed configs are therefore
--   UNREACHABLE yet Instrs_ok2-well-typed and stuck; these axioms supply the
--   intended step.
--
--   Weaker than the refutation backend-limitation axioms: those only carve types
--   down, whereas these ASSERT a reduction step the generated+source relation
--   lacks — the proof's weakest link.
--
--   TRUE of real Wasm: its jump/trap semantics discard ANY administrative tail of
--   the block, not only source instructions.
--
--   Deletion conditions — (spec) regenerate the five rules with `admininstr*`
--   tails; (proof) strengthen the config invariant to exclude admininstr tails
--   after BR / RETURN / TRAP, making the admin-tailed configs unreachable-by-typing.
postulate
  return-label-adm : ∀ n instrs (vs' : List val) (rest' : List admininstr) →
    Step-pure ((LABEL- n instrs (map (λ v → admininstr-val v) vs' ++ (admininstr-RETURN ∷ rest'))) ∷ [])
              (map (λ v → admininstr-val v) vs' ++ (admininstr-RETURN ∷ []))
  trap-vals-adm : ∀ (vs : List val) (rest : List admininstr) → (vs ≢ [] ⊎ rest ≢ []) →
    Step-pure (map (λ v → admininstr-val v) vs ++ (admininstr-TRAP ∷ rest)) (admininstr-TRAP ∷ [])
  br-zero-adm : ∀ n instrs' (vs0 vs1 : List val) (rest' : List admininstr) → length vs1 ≡ n →
    Step-pure ((LABEL- n instrs' (map (λ v → admininstr-val v) (vs0 ++ vs1)
                 ++ (admininstr-BR (mk-uN 0) ∷ rest'))) ∷ [])
              (map (λ v → admininstr-val v) vs1 ++ map (λ i → admininstr-instr i) instrs')
  br-succ-adm : ∀ n instrs' (vs' : List val) (k' : ℕ) (rest' : List admininstr) →
    Step-pure ((LABEL- n instrs' (map (λ v → admininstr-val v) vs'
                 ++ (admininstr-BR (mk-uN (suc k')) ∷ rest'))) ∷ [])
              (map (λ v → admininstr-val v) vs' ++ (admininstr-BR (mk-uN k') ∷ []))
  return-frame-adm : ∀ n fr (vs0 vs1 : List val) (rest' : List admininstr) → length vs1 ≡ n →
    Step-pure ((FRAME- n fr (map (λ v → admininstr-val v) (vs0 ++ vs1)
                 ++ (admininstr-RETURN ∷ rest'))) ∷ [])
              (map (λ v → admininstr-val v) vs1)

-- Split a list, isolating the last `n` elements (needs n ≤ length).
split-last : ∀ {A : Set} (xs : List A) (n : ℕ) → n ≤ length xs →
  Σ (List A) λ ys → Σ (List A) λ zs → (xs ≡ ys ++ zs) × (length zs ≡ n)
split-last xs n n≤ =
  take (length xs ∸ n) xs , drop (length xs ∸ n) xs ,
  sym (take++drop≡id (length xs ∸ n) xs) ,
  tr≡ (length-drop (length xs ∸ n) xs) (m∸[m∸n]≡n n≤)

rtlen : ∀ {a b} → Resulttype-sub (mk-list a) (mk-list b) → length a ≡ length b
rtlen (mk-Resulttype-sub _ _ e _) = e

-- A value row preceding `BR 0` under a label context supplies at least the
-- label-0 arity many operands (so br-zero's last-n split is well-defined).
label0-bound : ∀ {s Ci c} (t' : List valtype) (vs' : List val) {rest'} →
  Instrs-ok2 s (labC t' ⧺ Ci) (map (λ v → admininstr-val v) vs' ++ (admininstr-BR (mk-uN 0) ∷ rest'))
    (mk-functype (mk-list []) (mk-list c)) →
  length t' ≤ length vs'
label0-bound t' vs' ok with focus ok
... | d , c' , p , ts , e-iok , pwv , rtsub with br-inv e-iok refl
... | (t1 , tl) , deq , _ , lookeq =
  let lvs : length vs' ≡ length (p ++ d)
      lvs = tr≡ (sym (pw-length pwv)) (rtlen rtsub)
      ltl : length tl ≤ length d
      ltl = subst (length tl ≤_) (sym (tr≡ (cong length deq) (length-++ t1)))
              (m≤n+m (length tl) (length t1))
      lt'd : length t' ≤ length d
      lt'd = subst (_≤ length d) (sym (cong length lookeq)) ltl
  in subst (length t' ≤_) (sym lvs)
       (≤-trans lt'd (subst (length d ≤_) (sym (length-++ p)) (m≤n+m (length d) (length p))))

-- A value row preceding `RETURN` under a frame's return context supplies at
-- least the return arity many operands (so return-frame's last-n split works).
return-bound : ∀ {s Ci c} (vs' : List val) {rest'} → context-RETURN Ci ≡ just (mk-list c) →
  Instrs-ok2 s Ci (map (λ v → admininstr-val v) vs' ++ (admininstr-RETURN ∷ rest'))
    (mk-functype (mk-list []) (mk-list c)) →
  length c ≤ length vs'
return-bound {c = c} vs' reteq ok with focus ok
... | d , c' , p , ts , e-iok , pwv , rtsub with return-inv e-iok refl
... | (t1 , tr) , deq , reteq2 =
  let ctr : length c ≡ length tr
      ctr = cong maybe-rt-len (tr≡ (sym reteq) reteq2)
      lvs : length vs' ≡ length (p ++ d)
      lvs = tr≡ (sym (pw-length pwv)) (rtlen rtsub)
      ltr : length tr ≤ length d
      ltr = subst (length tr ≤_) (sym (tr≡ (cong length deq) (length-++ t1)))
              (m≤n+m (length tr) (length t1))
  in subst (length c ≤_) (sym lvs)
       (subst (_≤ length (p ++ d)) (sym ctr)
         (≤-trans ltr (subst (length d ≤_) (sym (length-++ p)) (m≤n+m (length d) (length p)))))
  where
    maybe-rt-len : Maybe resulttype → ℕ
    maybe-rt-len (just (mk-list xs)) = length xs
    maybe-rt-len nothing = 0

-- Batch E: 5-way outcome for administrative-instruction progress.

-- A BR reaching a context whose LABELS are empty is ill-typed (used to refute an
-- obranch that escapes a FRAME- activation body: its context retC c ⧺ C' has no
-- labels since C' is a frame context).
no-branch-ctx : ∀ {s Ci u2 l} (vs : List val) {rest} → LABELS Ci ≡ [] →
  Instrs-ok2 s Ci (map (λ v → admininstr-val v) vs ++ (admininstr-BR l ∷ rest))
    (mk-functype (mk-list []) (mk-list u2)) → ⊥
no-branch-ctx vs labeq ok with focus ok
... | _ , _ , _ , _ , e-iok , _ , _ with br-inv e-iok refl
... | _ , _ , l< , _ = n≮0 (subst (λ z → _ < length z) labeq l<)

-- CALL-ADDR (invoke) support: every non-⊥ valtype is defaultable, so a
-- function's declared locals can be zero-initialised.
default-exists : ∀ t → t ≢ BOT → default- t ≢ nothing
default-exists valtype-I32 _ = λ ()
default-exists valtype-I64 _ = λ ()
default-exists valtype-F32 _ = λ ()
default-exists valtype-F64 _ = λ ()
default-exists valtype-V128 _ = λ ()
default-exists valtype-FUNCREF _ = λ ()
default-exists valtype-EXTERNREF _ = λ ()
default-exists BOT ne = ⊥-elim (ne refl)

defaults-forall : ∀ {ts} → Forall (λ t → t ≢ BOT) ts → Forall (λ t → default- t ≢ nothing) ts
defaults-forall [] = []
defaults-forall (ne ∷ fs) = default-exists _ ne ∷ defaults-forall fs

caddr-inv : ∀ {s C e d c a} → Instr-ok2 s C e (mk-functype (mk-list d) (mk-list c)) →
  e ≡ CALL-ADDR a →
  Externaddr-ok s (externaddr-FUNC a) (FUNC (mk-functype (mk-list d) (mk-list c)))
caddr-inv (plain _ _ i _ _ iok) eq = refute-plain eq refl
caddr-inv (label _ _ _ _ _ _ _ _ _ _) ()
caddr-inv (Instr-ok2--frame _ _ _ _ _ _ _ _ _ _) ()
caddr-inv (Instr-ok2--call-addr _ _ _ _ _ extok) refl = extok
caddr-inv (Instr-ok2--ref _ _ (ref-REF-NULL _) _ _) ()
caddr-inv (Instr-ok2--ref _ _ (REF-FUNC-ADDR _) _ _) ()
caddr-inv (Instr-ok2--ref _ _ (REF-HOST-ADDR _) _ _) ()
caddr-inv (Instr-ok2--trap _ _ _ _) ()

-- Destructure a Funcinst-ok with the funcinst as a variable (so it works on the
-- abstract store lookup), exposing the module, code, declared type, and locals.
funcinst-parts : ∀ {s fi ft} → Funcinst-ok s fi ft →
  Σ moduleinst λ mm → Σ idx λ x → Σ (List valtype) λ t-lst → Σ expr λ body →
  Σ (List valtype) λ t1 → Σ (List valtype) λ t2 →
    (fi ≡ record { funcinst-TYPE = mk-functype (mk-list t1) (mk-list t2)
                 ; funcinst-MODULE = mm
                 ; CODE = func-FUNC x (map (λ t → LOCAL t) t-lst) body }) ×
    (ft ≡ mk-functype (mk-list t1) (mk-list t2)) ×
    Forall (λ t → t ≢ BOT) t-lst
funcinst-parts (mk-Funcinst-ok _ _ mm _ C0 ftok mok
                 (mk-Func-ok _ x t-lst body t1 t2 x< tylk forbot exok)) =
  mm , x , t-lst , body , t1 , t2 , refl , refl , forbot

-- Batch E: 5-way outcome for administrative-instruction progress.
-- A well-typed admininstr sequence is either all values (ovals), a bare trap
-- (otrap), can take a step (osteps), or is stuck on a control head (BR/RETURN)
-- that only an *enclosing* LABEL-/FRAME- can consume (obranch/oreturn).
data Outcome (s : store) (f : frame) : List admininstr → Set where
  ovals   : (vs : List val) {es : List admininstr} →
            es ≡ map (λ v → admininstr-val v) vs → Outcome s f es
  otrap   : {es : List admininstr} → es ≡ admininstr-TRAP ∷ [] → Outcome s f es
  osteps  : {es : List admininstr} →
            (Σ config λ c' → Step (mk-config (mk-state s f) es) c') → Outcome s f es
  obranch : (l : labelidx) (vs : List val) (rest : List admininstr) {es : List admininstr} →
            es ≡ map (λ v → admininstr-val v) vs ++ (admininstr-BR l ∷ rest) → Outcome s f es
  oreturn : (vs : List val) (rest : List admininstr) {es : List admininstr} →
            es ≡ map (λ v → admininstr-val v) vs ++ (admininstr-RETURN ∷ rest) → Outcome s f es

-- body-progress / progress-nonval carry the frame context Cf (for frame-facts)
-- separately from the instruction context Ci (which may be extended by an
-- enclosing LABEL-/FRAME-), linked by Agree Ci Cf.  agree-labC / agree-retC
-- transport Agree across the recursion into a LABEL-/FRAME- body.
body-progress : ∀ {s f Cf Ci es u2} →
  Store-ok s → Frame-ok s f Cf → Agree Ci Cf →
  Instrs-ok2 s Ci es (mk-functype (mk-list []) (mk-list u2)) →
  Acc _<_ (adm-size es) →
  Outcome s f es

progress-nonval : ∀ {s f Cf Ci u2} (vs : List val) (e : admininstr) (rest : List admininstr) →
  Store-ok s → Frame-ok s f Cf → Agree Ci Cf → ¬ IsVal e →
  Instrs-ok2 s Ci (map (λ v → admininstr-val v) vs ++ (e ∷ rest)) (mk-functype (mk-list []) (mk-list u2)) →
  Acc _<_ (adm-size (map (λ v → admininstr-val v) vs ++ (e ∷ rest))) →
  Outcome s f (map (λ v → admininstr-val v) vs ++ (e ∷ rest))

body-progress {es = es} sok fok ag ok ac with value-split es
... | inj₁ (vs , eq) = ovals vs eq
... | inj₂ (vs , e , rest , eq , nv) rewrite eq =
      progress-nonval vs e rest sok fok ag nv ok ac
-- nop: [NOP] ~> []
progress-nonval {s = s} {f = f} vs admininstr-NOP rest sok fok ag nv ok ac =
  osteps (wrap-step vs rest (pure (mk-state s f) (admininstr-NOP ∷ []) [] Step-pure--nop))
-- unreachable: [UNREACHABLE] ~> [TRAP]
progress-nonval {s = s} {f = f} vs admininstr-UNREACHABLE rest sok fok ag nv ok ac =
  osteps (wrap-step vs rest
    (pure (mk-state s f) (admininstr-UNREACHABLE ∷ []) (admininstr-TRAP ∷ []) Step-pure--unreachable))
-- bare trap
progress-nonval [] admininstr-TRAP [] sok fok ag nv ok ac = otrap refl
-- drop: [v, DROP] ~> []  (the operand is the top value; empty prefix is untypable)
progress-nonval {s = s} {f = f} vs admininstr-DROP rest sok fok ag nv ok ac with snoc-view vs
... | inj₁ refl = ⊥-elim (drop-nil-⊥ ok)
... | inj₂ (vs' , v , refl) =
      osteps (fire1 (pure (mk-state s f) (admininstr-val v ∷ admininstr-DROP ∷ []) [] (Step-pure--drop v)))
-- unop: [c, UNOP] ~> [c'] or [TRAP]
progress-nonval {s = s} {f = f} vs (admininstr-UNOP nt op) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with unop-inv e-iok refl
... | refl , refl with last-val pwv tspd
... | vs0 , v , _ , refl , vok , _ , _ with canonical-num vok
... | c-1 , refl with list-view (fun-unop- nt op c-1)
...   | inj₁ eq = osteps (fire1 (pure (mk-state s f) _ _ (unop-trap nt c-1 op eq)))
...   | inj₂ (cr , mem , len) = osteps (fire1 (pure (mk-state s f) _ _ (unop-val nt c-1 op cr len mem)))
-- testop: [c, TESTOP] ~> [i32.const _]  (total)
progress-nonval {s = s} {f = f} vs (admininstr-TESTOP nt op) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with testop-inv e-iok refl
... | refl , refl with last-val pwv tspd
... | vs0 , v , _ , refl , vok , _ , _ with canonical-num vok
... | c-1 , refl =
      osteps (fire1 (pure (mk-state s f) _ _ (Step-pure--testop nt c-1 op (fun-testop- nt op c-1) refl)))
-- binop: [c1, c2, BINOP] ~> [c'] or [TRAP]
progress-nonval {s = s} {f = f} vs (admininstr-BINOP nt op) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with binop-inv e-iok refl
... | refl , refl with last-2 pwv tspd
... | vs0 , v1 , v2 , refl , v1ok , v2ok with canonical-num v1ok | canonical-num v2ok
... | c-1 , refl | c-2 , refl with list-view (fun-binop- nt op c-1 c-2)
...   | inj₁ eq = osteps (fire2 (pure (mk-state s f) _ _ (binop-trap nt c-1 c-2 op eq)))
...   | inj₂ (cr , mem , len) = osteps (fire2 (pure (mk-state s f) _ _ (binop-val nt c-1 c-2 op cr len mem)))
-- relop: [c1, c2, RELOP] ~> [i32.const _]  (total)
progress-nonval {s = s} {f = f} vs (admininstr-RELOP nt op) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with relop-inv e-iok refl
... | refl , refl with last-2 pwv tspd
... | vs0 , v1 , v2 , refl , v1ok , v2ok with canonical-num v1ok | canonical-num v2ok
... | c-1 , refl | c-2 , refl =
      osteps (fire2 (pure (mk-state s f) _ _ (Step-pure--relop nt c-1 c-2 op (fun-relop- nt op c-1 c-2) refl)))
-- cvtop: [c, CVTOP nt2 nt1] ~> [c'] or [TRAP]
progress-nonval {s = s} {f = f} vs (admininstr-CVTOP nt2 nt1 op) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with cvtop-inv e-iok refl
... | refl , refl with last-val pwv tspd
... | vs0 , v , _ , refl , vok , _ , _ with canonical-num vok
... | c-1 , refl with list-view (cvtop-- nt1 nt2 op c-1)
...   | inj₁ eq = osteps (fire1 (pure (mk-state s f) _ _ (cvtop-trap nt1 c-1 nt2 op eq)))
...   | inj₂ (cr , mem , len) = osteps (fire1 (pure (mk-state s f) _ _ (cvtop-val nt1 c-1 nt2 op cr len mem)))
-- v128.vvunop: [v] ~> [v']  (total)
progress-nonval {s = s} {f = f} vs (admininstr-VVUNOP V128 op) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with vvunop-inv e-iok refl
... | refl , refl with last-val pwv tspd
... | vs0 , v , _ , refl , vok , _ , _ with canonical-vec vok
... | c-1 , refl =
      osteps (fire1 (pure (mk-state s f) _ _ (Step-pure--vvunop c-1 op (vvunop- V128 op c-1) refl)))
-- v128.vvbinop: [v1, v2] ~> [v']  (total)
progress-nonval {s = s} {f = f} vs (admininstr-VVBINOP V128 op) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with vvbinop-inv e-iok refl
... | refl , refl with last-2 pwv tspd
... | vs0 , v1 , v2 , refl , v1ok , v2ok with canonical-vec v1ok | canonical-vec v2ok
... | c-1 , refl | c-2 , refl =
      osteps (fire2 (pure (mk-state s f) _ _ (Step-pure--vvbinop c-1 c-2 op (vvbinop- V128 op c-1 c-2) refl)))
-- v128.vvternop: [v1, v2, v3] ~> [v']  (total)
progress-nonval {s = s} {f = f} vs (admininstr-VVTERNOP V128 op) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with vvternop-inv e-iok refl
... | refl , refl with last-3 pwv tspd
... | vs0 , v1 , v2 , v3 , refl , v1ok , v2ok , v3ok with canonical-vec v1ok | canonical-vec v2ok | canonical-vec v3ok
... | c-1 , refl | c-2 , refl | c-3 , refl =
      osteps (fire3 (pure (mk-state s f) _ _ (Step-pure--vvternop c-1 c-2 c-3 op (vvternop- V128 op c-1 c-2 c-3) refl)))
-- v128.vvtestop (any_true): [v] ~> [i32.const _]
progress-nonval {s = s} {f = f} vs (admininstr-VVTESTOP V128 ANY-TRUE) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with vvtestop-inv e-iok refl
... | refl , refl with last-val pwv tspd
... | vs0 , v , _ , refl , vok , _ , _ with canonical-vec vok
... | c-1 , refl =
      osteps (fire1 (pure (mk-state s f) _ _
        (Step-pure--vvtestop c-1 (ine- (unwrap! (size valtype-V128)) c-1 (mk-uN 0)) (λ ()) refl)))
-- v128.vunop: [v] ~> [v'] or [TRAP]
progress-nonval {s = s} {f = f} vs (admininstr-VUNOP sh op) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with vunop-inv e-iok refl
... | refl , refl with last-val pwv tspd
... | vs0 , v , _ , refl , vok , _ , _ with canonical-vec vok
... | c-1 , refl with list-view (fun-vunop- sh op c-1)
...   | inj₁ eq = osteps (fire1 (pure (mk-state s f) _ _ (vunop-trap c-1 sh op eq)))
...   | inj₂ (cr , mem , len) = osteps (fire1 (pure (mk-state s f) _ _ (Step-pure--vunop c-1 sh op cr len mem)))
-- v128.vbinop: [v1, v2] ~> [v'] or [TRAP]
progress-nonval {s = s} {f = f} vs (admininstr-VBINOP sh op) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with vbinop-inv e-iok refl
... | refl , refl with last-2 pwv tspd
... | vs0 , v1 , v2 , refl , v1ok , v2ok with canonical-vec v1ok | canonical-vec v2ok
... | c-1 , refl | c-2 , refl with list-view (fun-vbinop- sh op c-1 c-2)
...   | inj₁ eq = osteps (fire2 (pure (mk-state s f) _ _ (vbinop-trap c-1 c-2 sh op eq)))
...   | inj₂ (cr , mem , len) = osteps (fire2 (pure (mk-state s f) _ _ (vbinop-val c-1 c-2 sh op cr len mem)))
-- v128.vrelop: [v1, v2] ~> [v']  (total)
progress-nonval {s = s} {f = f} vs (admininstr-VRELOP sh op) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with vrelop-inv e-iok refl
... | refl , refl with last-2 pwv tspd
... | vs0 , v1 , v2 , refl , v1ok , v2ok with canonical-vec v1ok | canonical-vec v2ok
... | c-1 , refl | c-2 , refl =
      osteps (fire2 (pure (mk-state s f) _ _ (Step-pure--vrelop c-1 c-2 sh op (fun-vrelop- sh op c-1 c-2) refl)))
-- v128.vshiftop: [v, i32] ~> [v']  (per integer shape; inv-lanes- is a function)
progress-nonval {s = s} {f = f} vs (admininstr-VSHIFTOP (ishape-X Jnn-I32 (mk-dim N)) op) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with vshiftop-inv e-iok refl
... | refl , refl with last-2 pwv tspd
... | vs0 , v1 , v2 , refl , v1ok , v2ok with canonical-vec v1ok | canonical-num {nt = I32} v2ok
... | c-1 , refl | mk-uN vn , refl =
      osteps (fire2 (pure (mk-state s f) _ _ (vshiftop-0 c-1 vn N op _ _ refl refl)))
progress-nonval {s = s} {f = f} vs (admininstr-VSHIFTOP (ishape-X Jnn-I64 (mk-dim N)) op) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with vshiftop-inv e-iok refl
... | refl , refl with last-2 pwv tspd
... | vs0 , v1 , v2 , refl , v1ok , v2ok with canonical-vec v1ok | canonical-num {nt = I32} v2ok
... | c-1 , refl | mk-uN vn , refl =
      osteps (fire2 (pure (mk-state s f) _ _ (vshiftop-1 c-1 vn N op _ _ refl refl)))
progress-nonval {s = s} {f = f} vs (admininstr-VSHIFTOP (ishape-X Jnn-I8 (mk-dim N)) op) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with vshiftop-inv e-iok refl
... | refl , refl with last-2 pwv tspd
... | vs0 , v1 , v2 , refl , v1ok , v2ok with canonical-vec v1ok | canonical-num {nt = I32} v2ok
... | c-1 , refl | mk-uN vn , refl =
      osteps (fire2 (pure (mk-state s f) _ _ (vshiftop-2 c-1 vn N op _ _ refl refl)))
progress-nonval {s = s} {f = f} vs (admininstr-VSHIFTOP (ishape-X Jnn-I16 (mk-dim N)) op) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with vshiftop-inv e-iok refl
... | refl , refl with last-2 pwv tspd
... | vs0 , v1 , v2 , refl , v1ok , v2ok with canonical-vec v1ok | canonical-num {nt = I32} v2ok
... | c-1 , refl | mk-uN vn , refl =
      osteps (fire2 (pure (mk-state s f) _ _ (vshiftop-3 c-1 vn N op _ _ refl refl)))
-- v128.bitmask: [v] ~> [i32]  (per integer shape; mask length 32 via dim-bound + lanes-length)
progress-nonval {s = s} {f = f} vs (admininstr-VBITMASK (ishape-X Jnn-I32 (mk-dim N))) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with vbitmask-inv e-iok refl
... | refl , refl with last-val pwv tspd
... | vs0 , v , _ , refl , vok , _ , _ with canonical-vec vok
... | c-1 , refl =
      osteps (fire1 (pure (mk-state s f) _ _
        (vbitmask-0 c-1 N (inv-ibits- 32 _) (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim N)) c-1) refl
          (ibits-inv 32 _ (mask-len32 (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim N)) c-1) _ N
            (lanes-length (lanetype-Jnn Jnn-I32) N c-1) (≤-trans (dim-bound (mk-dim N)) (m≤m+n 16 16)))))))
progress-nonval {s = s} {f = f} vs (admininstr-VBITMASK (ishape-X Jnn-I64 (mk-dim N))) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with vbitmask-inv e-iok refl
... | refl , refl with last-val pwv tspd
... | vs0 , v , _ , refl , vok , _ , _ with canonical-vec vok
... | c-1 , refl =
      osteps (fire1 (pure (mk-state s f) _ _
        (vbitmask-1 c-1 N (inv-ibits- 32 _) (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim N)) c-1) refl
          (ibits-inv 32 _ (mask-len32 (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim N)) c-1) _ N
            (lanes-length (lanetype-Jnn Jnn-I64) N c-1) (≤-trans (dim-bound (mk-dim N)) (m≤m+n 16 16)))))))
progress-nonval {s = s} {f = f} vs (admininstr-VBITMASK (ishape-X Jnn-I8 (mk-dim N))) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with vbitmask-inv e-iok refl
... | refl , refl with last-val pwv tspd
... | vs0 , v , _ , refl , vok , _ , _ with canonical-vec vok
... | c-1 , refl =
      osteps (fire1 (pure (mk-state s f) _ _
        (vbitmask-2 c-1 N (inv-ibits- 32 _) (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim N)) c-1) refl
          (ibits-inv 32 _ (mask-len32 (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim N)) c-1) _ N
            (lanes-length (lanetype-Jnn Jnn-I8) N c-1) (≤-trans (dim-bound (mk-dim N)) (m≤m+n 16 16)))))))
progress-nonval {s = s} {f = f} vs (admininstr-VBITMASK (ishape-X Jnn-I16 (mk-dim N))) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with vbitmask-inv e-iok refl
... | refl , refl with last-val pwv tspd
... | vs0 , v , _ , refl , vok , _ , _ with canonical-vec vok
... | c-1 , refl =
      osteps (fire1 (pure (mk-state s f) _ _
        (vbitmask-3 c-1 N (inv-ibits- 32 _) (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim N)) c-1) refl
          (ibits-inv 32 _ (mask-len32 (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim N)) c-1) _ N
            (lanes-length (lanetype-Jnn Jnn-I16) N c-1) (≤-trans (dim-bound (mk-dim N)) (m≤m+n 16 16)))))))
-- v128.vextunop: [v] ~> [v']  (total, generic ishape)
progress-nonval {s = s} {f = f} vs (admininstr-VEXTUNOP s1 s2 op) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with vextunop-inv e-iok refl
... | refl , refl with last-val pwv tspd
... | vs0 , v , _ , refl , vok , _ , _ with canonical-vec vok
... | c-1 , refl =
      osteps (fire1 (pure (mk-state s f) _ _ (Step-pure--vextunop c-1 s1 s2 op (vextunop-- s1 s2 op c-1) refl)))
-- v128.vextbinop: [v1, v2] ~> [v']  (total, generic ishape)
progress-nonval {s = s} {f = f} vs (admininstr-VEXTBINOP s1 s2 op) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with vextbinop-inv e-iok refl
... | refl , refl with last-2 pwv tspd
... | vs0 , v1 , v2 , refl , v1ok , v2ok with canonical-vec v1ok | canonical-vec v2ok
... | c-1 , refl | c-2 , refl =
      osteps (fire2 (pure (mk-state s f) _ _ (Step-pure--vextbinop c-1 c-2 s1 s2 op (vextbinop-- s1 s2 op c-1 c-2) refl)))
-- select: [v1, v2, i32.const c, SELECT] ~> [v1] (c≠0) or [v2] (c=0)
progress-nonval {s = s} {f = f} vs (admininstr-SELECT opt) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with sel-inv e-iok refl
... | t , refl , refl with last-3 pwv tspd
... | vs0 , v1 , v2 , v3 , refl , v1ok , v2ok , v3ok with canonical-num {nt = I32} v3ok
... | c , refl with proj-uN-0 32 c ≟ 0
...   | yes eq0 = osteps (fire3 (pure (mk-state s f) _ _ (select-false v1 v2 c opt eq0)))
...   | no  ne0 = osteps (fire3 (pure (mk-state s f) _ _ (select-true v1 v2 c opt ne0)))
-- if: [i32.const c, IF bt i1 i2] ~> [BLOCK bt i1] (c≠0) or [BLOCK bt i2] (c=0)
progress-nonval {s = s} {f = f} vs (admininstr-IFELSE bt i1 i2) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with if-inv e-iok refl
... | t1 , deq , _ with peel-top-i32 pwv tspd deq
... | vs0 , c , refl with proj-uN-0 32 c ≟ 0
...   | yes eq0 = osteps (fire1 (pure (mk-state s f) _ _ (if-false c bt i1 i2 eq0)))
...   | no  ne0 = osteps (fire1 (pure (mk-state s f) _ _ (if-true c bt i1 i2 ne0)))
-- br_if: [i32.const c, BR-IF l] ~> [BR l] (c≠0) or [] (c=0)
progress-nonval {s = s} {f = f} vs (admininstr-BR-IF l) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with brif-inv e-iok refl
... | t , deq , _ with peel-top-i32 pwv tspd deq
... | vs0 , c , refl with proj-uN-0 32 c ≟ 0
...   | yes eq0 = osteps (fire1 (pure (mk-state s f) _ _ (br-if-false c l eq0)))
...   | no  ne0 = osteps (fire1 (pure (mk-state s f) _ _ (br-if-true c l ne0)))
-- br_table: [i32.const i, BR-TABLE ls l'] ~> [BR ls[i]] (i<|ls|) or [BR l'] (i≥|ls|)
progress-nonval {s = s} {f = f} vs (admininstr-BR-TABLE ls l') rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with brtable-inv e-iok refl
... | (t1 , tl) , deq , _ with peel-top-i32 pwv tspd (tr≡ deq (sym (++-assoc t1 tl (valtype-I32 ∷ []))))
... | vs0 , i , refl with proj-uN-0 32 i <?ⁿ length ls
...   | yes lt = osteps (fire1 (pure (mk-state s f) _ _ (br-table-lt i ls l' lt)))
...   | no  ge = osteps (fire1 (pure (mk-state s f) _ _ (br-table-ge i ls l' (≮⇒≥ ge))))
-- block: [v*, BLOCK bt is] ~> [LABEL ...]  (consumes the block's input-arity values)
progress-nonval {s = s} {f = f} vs (admininstr-BLOCK bt is) rest sok fok ag nv ok ac with focus ok
... | d , c , p , _ , e-iok , pwv , tspd with block-inv e-iok refl
... | btok , _ with peel-row p pwv tspd
... | vs0 , vs1 , refl , fd =
      osteps (fire-row (read (mk-state s f) _ _
        (Step-read--block (mk-state s f) (length vs1) vs1 bt is (length c) d c
          refl refl (pw-length fd) (blocktype-agree btok (subst (λ z → _ ≡ z) (FrameFacts.types-eq (frame-facts fok)) (Agree.typ≡ ag))))))
-- loop: [v*, LOOP bt is] ~> [LABEL ...]
progress-nonval {s = s} {f = f} vs (admininstr-LOOP bt is) rest sok fok ag nv ok ac with focus ok
... | d , c , p , _ , e-iok , pwv , tspd with loop-inv e-iok refl
... | _ , btok , _ with peel-row p pwv tspd
... | vs0 , vs1 , refl , fd =
      osteps (fire-row (read (mk-state s f) _ _
        (Step-read--loop (mk-state s f) (length vs1) vs1 bt is d (length c) c
          refl refl (pw-length fd) (blocktype-agree btok (subst (λ z → _ ≡ z) (FrameFacts.types-eq (frame-facts fok)) (Agree.typ≡ ag))))))
-- call: [CALL x] ~> [CALL-ADDR a]  (the read rule doesn't consume args; frame supplies the addr)
progress-nonval {s = s} {f = f} vs (admininstr-CALL x) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with call-inv e-iok refl
... | (t1 , t2) , refl , refl , x<C , lk with frame-facts fok
... | ff =
      osteps (wrap-step vs rest
        (read (mk-state s f) _ _
          (Step-read--call (mk-state s f) x
            (subst (proj-uN-0 32 x <_) (sym (FrameFacts.faddrs-len ff))
              (subst (λ l → proj-uN-0 32 x < length l) (FrameFacts.funcs-eq ff) (subst (λ l → proj-uN-0 32 x < length l) (Agree.func≡ ag) x<C))))))
-- local.get / global.get: always step (read rule has no premise)
progress-nonval {s = s} {f = f} vs (admininstr-LOCAL-GET x) rest sok fok ag nv ok ac =
  osteps (wrap-step vs rest (read (mk-state s f) _ _ (Step-read--local-get (mk-state s f) x)))
progress-nonval {s = s} {f = f} vs (admininstr-GLOBAL-GET x) rest sok fok ag nv ok ac =
  osteps (wrap-step vs rest (read (mk-state s f) _ _ (Step-read--global-get (mk-state s f) x)))
-- ref.func: [REF-FUNC x] ~> [REF-FUNC-ADDR a]  (frame supplies the addr)
progress-nonval {s = s} {f = f} vs (admininstr-REF-FUNC x) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with rfunc-inv e-iok refl
... | refl , refl , x<C with frame-facts fok
... | ff =
      osteps (wrap-step vs rest
        (read (mk-state s f) _ _
          (Step-read--ref-func (mk-state s f) x
            (subst (proj-uN-0 32 x <_) (sym (FrameFacts.faddrs-len ff))
              (subst (λ l → proj-uN-0 32 x < length l) (FrameFacts.funcs-eq ff) (subst (λ l → proj-uN-0 32 x < length l) (Agree.func≡ ag) x<C))))))
-- table.set: [i32.const i, ref r, TABLE-SET x] ~> (write) or [TRAP]
-- (r is cased so admininstr-val (val-ref r) ≡ admininstr-ref r holds definitionally)
progress-nonval {s = s} {f = f} vs (admininstr-TABLE-SET x) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with tset-inv e-iok refl
... | (rt , lim) , refl , _ with last-2 pwv tspd
... | vs0 , v1 , v2 , refl , v1ok , v2ok with canonical-num {nt = I32} v1ok | canonical-ref v2ok
... | i , refl | ref-REF-NULL x0 , refl with proj-uN-0 32 i <?ⁿ length (REFS (fun-table (mk-state s f) x))
...   | yes lt = osteps (fire2 (table-set-val (mk-state s f) i (ref-REF-NULL x0) x lt))
...   | no  ge = osteps (fire2 (table-set-trap (mk-state s f) i (ref-REF-NULL x0) x (≮⇒≥ ge)))
progress-nonval {s = s} {f = f} vs (admininstr-TABLE-SET x) rest sok fok ag nv ok ac | _ , _ , _ , _ , e-iok , pwv , tspd | (rt , lim) , refl , _ | vs0 , v1 , v2 , refl , v1ok , v2ok | i , refl | REF-FUNC-ADDR x0 , refl with proj-uN-0 32 i <?ⁿ length (REFS (fun-table (mk-state s f) x))
...   | yes lt = osteps (fire2 (table-set-val (mk-state s f) i (REF-FUNC-ADDR x0) x lt))
...   | no  ge = osteps (fire2 (table-set-trap (mk-state s f) i (REF-FUNC-ADDR x0) x (≮⇒≥ ge)))
progress-nonval {s = s} {f = f} vs (admininstr-TABLE-SET x) rest sok fok ag nv ok ac | _ , _ , _ , _ , e-iok , pwv , tspd | (rt , lim) , refl , _ | vs0 , v1 , v2 , refl , v1ok , v2ok | i , refl | REF-HOST-ADDR x0 , refl with proj-uN-0 32 i <?ⁿ length (REFS (fun-table (mk-state s f) x))
...   | yes lt = osteps (fire2 (table-set-val (mk-state s f) i (REF-HOST-ADDR x0) x lt))
...   | no  ge = osteps (fire2 (table-set-trap (mk-state s f) i (REF-HOST-ADDR x0) x (≮⇒≥ ge)))
-- table.grow: [ref r, i32.const n, TABLE-GROW x] ~> succeed/fail (growtable decision; r cased)
progress-nonval {s = s} {f = f} vs (admininstr-TABLE-GROW x) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with tgrow-inv e-iok refl
... | rt , refl , _ with last-2 pwv tspd
... | vs0 , v1 , v2 , refl , v1ok , v2ok with canonical-ref v1ok | canonical-num {nt = I32} v2ok
... | ref-REF-NULL x0 , refl | mk-uN n , refl with growtable (fun-table (mk-state s f) x) n (ref-REF-NULL x0) in eq
...   | just ti = osteps (fire2 (table-grow-succeed (mk-state s f) (ref-REF-NULL x0) n x ti (λ h → nothing≢just (tr≡ (sym h) eq)) (cong unwrap! eq)))
...   | nothing = osteps (fire2 (table-grow-fail (mk-state s f) (ref-REF-NULL x0) n x))
progress-nonval {s = s} {f = f} vs (admininstr-TABLE-GROW x) rest sok fok ag nv ok ac | _ , _ , _ , _ , e-iok , pwv , tspd | rt , refl , _ | vs0 , v1 , v2 , refl , v1ok , v2ok | REF-FUNC-ADDR x0 , refl | mk-uN n , refl with growtable (fun-table (mk-state s f) x) n (REF-FUNC-ADDR x0) in eq
...   | just ti = osteps (fire2 (table-grow-succeed (mk-state s f) (REF-FUNC-ADDR x0) n x ti (λ h → nothing≢just (tr≡ (sym h) eq)) (cong unwrap! eq)))
...   | nothing = osteps (fire2 (table-grow-fail (mk-state s f) (REF-FUNC-ADDR x0) n x))
progress-nonval {s = s} {f = f} vs (admininstr-TABLE-GROW x) rest sok fok ag nv ok ac | _ , _ , _ , _ , e-iok , pwv , tspd | rt , refl , _ | vs0 , v1 , v2 , refl , v1ok , v2ok | REF-HOST-ADDR x0 , refl | mk-uN n , refl with growtable (fun-table (mk-state s f) x) n (REF-HOST-ADDR x0) in eq
...   | just ti = osteps (fire2 (table-grow-succeed (mk-state s f) (REF-HOST-ADDR x0) n x ti (λ h → nothing≢just (tr≡ (sym h) eq)) (cong unwrap! eq)))
...   | nothing = osteps (fire2 (table-grow-fail (mk-state s f) (REF-HOST-ADDR x0) n x))
-- table.get: [i32.const i, TABLE-GET x] ~> [ref] (i<|refs|) or [TRAP]
progress-nonval {s = s} {f = f} vs (admininstr-TABLE-GET x) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with tget-inv e-iok refl
... | (rt , lim) , refl , _ with last-val pwv tspd
... | vs0 , v , _ , refl , vok , _ , _ with canonical-num {nt = I32} vok
... | i , refl with proj-uN-0 32 i <?ⁿ length (REFS (fun-table (mk-state s f) x))
...   | yes lt = osteps (fire1 (read (mk-state s f) _ _ (table-get-val (mk-state s f) i x lt)))
...   | no  ge = osteps (fire1 (read (mk-state s f) _ _ (table-get-trap (mk-state s f) i x (≮⇒≥ ge))))
-- elem.drop / data.drop: always step (no premise)
progress-nonval {s = s} {f = f} vs (admininstr-ELEM-DROP x) rest sok fok ag nv ok ac =
  osteps (wrap-step vs rest (Step--elem-drop (mk-state s f) x))
progress-nonval {s = s} {f = f} vs (admininstr-DATA-DROP x) rest sok fok ag nv ok ac =
  osteps (wrap-step vs rest (Step--data-drop (mk-state s f) x))
-- local.set: [v, LOCAL-SET x] ~> []  (any value operand)
progress-nonval {s = s} {f = f} vs (admininstr-LOCAL-SET x) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with lset-inv e-iok refl
... | t , refl , _ with last-val pwv tspd
... | vs0 , v , _ , refl , _ , _ , _ = osteps (fire1 (Step--local-set (mk-state s f) v x))
-- global.set: [v, GLOBAL-SET x] ~> []
progress-nonval {s = s} {f = f} vs (admininstr-GLOBAL-SET x) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with gset-inv e-iok refl
... | t , refl , _ with last-val pwv tspd
... | vs0 , v , _ , refl , _ , _ , _ = osteps (fire1 (Step--global-set (mk-state s f) v x))
-- local.tee: [v, LOCAL-TEE x] ~> [v, v, LOCAL-SET x]
progress-nonval {s = s} {f = f} vs (admininstr-LOCAL-TEE x) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with ltee-inv e-iok refl
... | t , refl with last-val pwv tspd
... | vs0 , v , _ , refl , _ , _ , _ = osteps (fire1 (pure (mk-state s f) _ _ (Step-pure--local-tee v x)))
-- load (numeric): [i32.const i, LOAD nt] ~> [nt.const c] (in-bounds) or [TRAP]
progress-nonval {s = s} {f = f} vs (admininstr-LOAD nt nothing ao) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with loadnum-inv e-iok refl
... | refl , refl with last-val pwv tspd
... | vs0 , v , _ , refl , vok , _ , _ with canonical-num {nt = I32} vok
... | i , refl
  with (proj-uN-0 32 i + proj-uN-0 32 (OFFSET ao)) + (unwrap! (size (valtype-numtype nt)) / 8)
         ≤?ⁿ length (BYTES (fun-mem (mk-state s f) (mk-uN 0)))
...   | no gt = osteps (fire1 (read (mk-state s f) _ _
                  (load-num-trap (mk-state s f) i nt ao (nt-size≢nothing nt) (≰⇒> gt))))
...   | yes le
  with nbytes-surj nt
         (slice (BYTES (fun-mem (mk-state s f) (mk-uN 0)))
           (proj-uN-0 32 i + proj-uN-0 32 (OFFSET ao)) (unwrap! (size (valtype-numtype nt)) / 8))
         (slice-len _ _ _ le)
...     | c , ceq = osteps (fire1 (read (mk-state s f) _ _
                      (load-num-val (mk-state s f) i nt ao c (nt-size≢nothing nt) ceq)))
-- store (packed): [i32.const i, Inn.const c, STORE Inn (just sz)] ~> (write) or [TRAP]
progress-nonval {s = s} {f = f} vs (admininstr-STORE nt (just sz) ao) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with storepack-full e-iok refl
... | Inn-I32 , M , refl , refl , refl with last-2 pwv tspd
... | vs0 , v1 , v2 , refl , v1ok , v2ok with canonical-num {nt = I32} v1ok | canonical-num {nt = I32} v2ok
... | i , refl | c , refl
  with (proj-uN-0 32 i + proj-uN-0 32 (OFFSET ao)) + (M / 8)
         ≤?ⁿ length (BYTES (fun-mem (mk-state s f) (mk-uN 0)))
...   | yes le = osteps (fire2 (store-pack-val-0 (mk-state s f) i c M ao _ le (λ ()) refl))
...   | no  gt = osteps (fire2 (store-pack-trap-0 (mk-state s f) i c M ao (≰⇒> gt)))
progress-nonval {s = s} {f = f} vs (admininstr-STORE nt (just sz) ao) rest sok fok ag nv ok ac | _ , _ , _ , _ , e-iok , pwv , tspd | Inn-I64 , M , refl , refl , refl with last-2 pwv tspd
... | vs0 , v1 , v2 , refl , v1ok , v2ok with canonical-num {nt = I32} v1ok | canonical-num {nt = I64} v2ok
... | i , refl | c , refl
  with (proj-uN-0 32 i + proj-uN-0 32 (OFFSET ao)) + (M / 8)
         ≤?ⁿ length (BYTES (fun-mem (mk-state s f) (mk-uN 0)))
...   | yes le = osteps (fire2 (store-pack-val-1 (mk-state s f) i c M ao _ le (λ ()) refl))
...   | no  gt = osteps (fire2 (store-pack-trap-1 (mk-state s f) i c M ao (≰⇒> gt)))
-- v128.store: [i32.const i, v128.const c, VSTORE] ~> (write) or [TRAP]
progress-nonval {s = s} {f = f} vs (admininstr-VSTORE V128 ao) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with vstore-inv e-iok refl
... | refl , refl with last-2 pwv tspd
... | vs0 , v1 , v2 , refl , v1ok , v2ok with canonical-num {nt = I32} v1ok | canonical-vec v2ok
... | i , refl | c , refl
  with (proj-uN-0 32 i + proj-uN-0 32 (OFFSET ao)) + (unwrap! (size valtype-V128) / 8)
         ≤?ⁿ length (BYTES (fun-mem (mk-state s f) (mk-uN 0)))
...   | yes le = osteps (fire2 (vstore-val (mk-state s f) i c ao _ (λ ()) le refl))
...   | no  gt = osteps (fire2 (vstore-oob (mk-state s f) i c ao (λ ()) (≰⇒> gt)))
-- store (numeric): [i32.const i, nt.const c, STORE nt] ~> (write) or [TRAP]
progress-nonval {s = s} {f = f} vs (admininstr-STORE nt nothing ao) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with storenum-inv e-iok refl
... | refl , refl with last-2 pwv tspd
... | vs0 , v1 , v2 , refl , v1ok , v2ok with canonical-num {nt = I32} v1ok | canonical-num {nt = nt} v2ok
... | i , refl | c , refl
  with (proj-uN-0 32 i + proj-uN-0 32 (OFFSET ao)) + (unwrap! (size (valtype-numtype nt)) / 8)
         ≤?ⁿ length (BYTES (fun-mem (mk-state s f) (mk-uN 0)))
...   | yes le = osteps (fire2 (store-num-val (mk-state s f) i nt c ao (nbytes- nt c) (nt-size≢nothing nt) le refl))
...   | no  gt = osteps (fire2 (store-num-trap (mk-state s f) i nt c ao (nt-size≢nothing nt) (≰⇒> gt)))
-- memory.fill: [i, v, n, MEMORY-FILL] ~> decompose (n=0 / n≠0 in-bounds) or [TRAP] (oob)
progress-nonval {s = s} {f = f} vs admininstr-MEMORY-FILL rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with mfill-dom e-iok refl
... | refl , refl with last-3 pwv tspd
... | vs0 , v1 , v2 , v3 , refl , v1ok , v2ok , v3ok with canonical-num {nt = I32} v1ok | canonical-num {nt = I32} v3ok
... | i , refl | mk-uN n , refl
  with (proj-uN-0 32 i + n) ≤?ⁿ length (BYTES (fun-mem (mk-state s f) (mk-uN 0)))
...   | no  gt = osteps (fire3 (read (mk-state s f) _ _ (memory-fill-trap (mk-state s f) i v2 n (≰⇒> gt))))
...   | yes le with n ≟ 0
...     | yes n0 = osteps (fire3 (read (mk-state s f) _ _ (memory-fill-zero (mk-state s f) i v2 n le n0)))
...     | no  n≠ = osteps (fire3 (read (mk-state s f) _ _ (memory-fill-succ (mk-state s f) i v2 n n≠ le)))
-- memory.copy: [j, i, n, MEMORY-COPY] ~> decompose (le/gt) / [] (n=0) / [TRAP] (oob)
progress-nonval {s = s} {f = f} vs admininstr-MEMORY-COPY rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with mcopy-dom e-iok refl
... | refl , refl with last-3 pwv tspd
... | vs0 , v1 , v2 , v3 , refl , v1ok , v2ok , v3ok
  with canonical-num {nt = I32} v1ok | canonical-num {nt = I32} v2ok | canonical-num {nt = I32} v3ok
... | j , refl | i , refl | mk-uN n , refl
  with (proj-uN-0 32 i + n) ≤?ⁿ length (BYTES (fun-mem (mk-state s f) (mk-uN 0)))
     | (proj-uN-0 32 j + n) ≤?ⁿ length (BYTES (fun-mem (mk-state s f) (mk-uN 0)))
...   | no  gi | _ = osteps (fire3 (read (mk-state s f) _ _ (memory-copy-trap (mk-state s f) j i n (inj₁ (≰⇒> gi)))))
...   | yes _  | no gj = osteps (fire3 (read (mk-state s f) _ _ (memory-copy-trap (mk-state s f) j i n (inj₂ (≰⇒> gj)))))
...   | yes lei | yes lej with n ≟ 0
...     | yes n0 = osteps (fire3 (read (mk-state s f) _ _ (memory-copy-zero (mk-state s f) j i n (lei , lej) n0)))
...     | no  n≠ with proj-uN-0 32 j ≤?ⁿ proj-uN-0 32 i
...       | yes jle = osteps (fire3 (read (mk-state s f) _ _ (memory-copy-le (mk-state s f) j i n n≠ (lei , lej) jle)))
...       | no  jgt = osteps (fire3 (read (mk-state s f) _ _ (memory-copy-gt (mk-state s f) j i n (≰⇒> jgt) n≠ (lei , lej))))
-- memory.init: [j, i, n, MEMORY-INIT x] ~> decompose / [] / [TRAP]
progress-nonval {s = s} {f = f} vs (admininstr-MEMORY-INIT x) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with minit-dom e-iok refl
... | refl , refl with last-3 pwv tspd
... | vs0 , v1 , v2 , v3 , refl , v1ok , v2ok , v3ok
  with canonical-num {nt = I32} v1ok | canonical-num {nt = I32} v2ok | canonical-num {nt = I32} v3ok
... | j , refl | i , refl | mk-uN n , refl
  with (proj-uN-0 32 i + n) ≤?ⁿ length (datainst-BYTES (fun-data (mk-state s f) x))
     | (proj-uN-0 32 j + n) ≤?ⁿ length (BYTES (fun-mem (mk-state s f) (mk-uN 0)))
...   | no  gi | _ = osteps (fire3 (read (mk-state s f) _ _ (memory-init-trap (mk-state s f) j i n x (inj₁ (≰⇒> gi)))))
...   | yes _  | no gj = osteps (fire3 (read (mk-state s f) _ _ (memory-init-trap (mk-state s f) j i n x (inj₂ (≰⇒> gj)))))
...   | yes lei | yes lej with n ≟ 0
...     | yes n0 = osteps (fire3 (read (mk-state s f) _ _ (memory-init-zero (mk-state s f) j i n x (lei , lej) n0)))
...     | no  n≠ = osteps (fire3 (read (mk-state s f) _ _ (memory-init-succ (mk-state s f) j i n x (i+n≤⇒i< lei n≠) n≠ (lei , lej))))
-- table.fill: [i, v, n, TABLE-FILL x] ~> decompose / [] / [TRAP]  (v is any ref value)
progress-nonval {s = s} {f = f} vs (admininstr-TABLE-FILL x) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with tfill-dom e-iok refl
... | rt , refl , refl with last-3 pwv tspd
... | vs0 , v1 , v2 , v3 , refl , v1ok , v2ok , v3ok with canonical-num {nt = I32} v1ok | canonical-num {nt = I32} v3ok
... | i , refl | mk-uN n , refl
  with (proj-uN-0 32 i + n) ≤?ⁿ length (REFS (fun-table (mk-state s f) x))
...   | no  gt = osteps (fire3 (read (mk-state s f) _ _ (table-fill-trap (mk-state s f) i v2 n x (≰⇒> gt))))
...   | yes le with n ≟ 0
...     | yes n0 = osteps (fire3 (read (mk-state s f) _ _ (table-fill-zero (mk-state s f) i v2 n x le n0)))
...     | no  n≠ = osteps (fire3 (read (mk-state s f) _ _ (table-fill-succ (mk-state s f) i v2 n x n≠ le)))
-- table.copy: [j, i, n, TABLE-COPY x y] ~> decompose / [] / [TRAP]
progress-nonval {s = s} {f = f} vs (admininstr-TABLE-COPY x y) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with tcopy-dom e-iok refl
... | refl , refl with last-3 pwv tspd
... | vs0 , v1 , v2 , v3 , refl , v1ok , v2ok , v3ok
  with canonical-num {nt = I32} v1ok | canonical-num {nt = I32} v2ok | canonical-num {nt = I32} v3ok
... | j , refl | i , refl | mk-uN n , refl
  with (proj-uN-0 32 i + n) ≤?ⁿ length (REFS (fun-table (mk-state s f) y))
     | (proj-uN-0 32 j + n) ≤?ⁿ length (REFS (fun-table (mk-state s f) x))
...   | no  gi | _ = osteps (fire3 (read (mk-state s f) _ _ (table-copy-trap (mk-state s f) j i n x y (inj₁ (≰⇒> gi)))))
...   | yes _  | no gj = osteps (fire3 (read (mk-state s f) _ _ (table-copy-trap (mk-state s f) j i n x y (inj₂ (≰⇒> gj)))))
...   | yes lei | yes lej with n ≟ 0
...     | yes n0 = osteps (fire3 (read (mk-state s f) _ _ (table-copy-zero (mk-state s f) j i n x y (lei , lej) n0)))
...     | no  n≠ with proj-uN-0 32 j ≤?ⁿ proj-uN-0 32 i
...       | yes jle = osteps (fire3 (read (mk-state s f) _ _ (table-copy-le (mk-state s f) j i n x y n≠ (lei , lej) jle)))
...       | no  jgt = osteps (fire3 (read (mk-state s f) _ _ (table-copy-gt (mk-state s f) j i n x y (≰⇒> jgt) n≠ (lei , lej))))
-- table.init: [j, i, n, TABLE-INIT x y] ~> decompose / [] / [TRAP]
progress-nonval {s = s} {f = f} vs (admininstr-TABLE-INIT x y) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with tinit-dom e-iok refl
... | refl , refl with last-3 pwv tspd
... | vs0 , v1 , v2 , v3 , refl , v1ok , v2ok , v3ok
  with canonical-num {nt = I32} v1ok | canonical-num {nt = I32} v2ok | canonical-num {nt = I32} v3ok
... | j , refl | i , refl | mk-uN n , refl
  with (proj-uN-0 32 i + n) ≤?ⁿ length (eleminst-REFS (fun-elem (mk-state s f) y))
     | (proj-uN-0 32 j + n) ≤?ⁿ length (REFS (fun-table (mk-state s f) x))
...   | no  gi | _ = osteps (fire3 (read (mk-state s f) _ _ (table-init-trap (mk-state s f) j i n x y (inj₁ (≰⇒> gi)))))
...   | yes _  | no gj = osteps (fire3 (read (mk-state s f) _ _ (table-init-trap (mk-state s f) j i n x y (inj₂ (≰⇒> gj)))))
...   | yes lei | yes lej with n ≟ 0
...     | yes n0 = osteps (fire3 (read (mk-state s f) _ _ (table-init-zero (mk-state s f) j i n x y (lei , lej) n0)))
...     | no  n≠ = osteps (fire3 (read (mk-state s f) _ _ (table-init-succ (mk-state s f) j i n x y (i+n≤⇒i< lei n≠) n≠ (lei , lej))))
-- load (packed): [i32.const i, LOAD Inn (just (sz,sx))] ~> [Inn.const (extend c)] or [TRAP]
progress-nonval {s = s} {f = f} vs (admininstr-LOAD nt (just lo) ao) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with loadpack-full e-iok refl
... | Inn-I32 , refl , refl with lo
... | mk-loadop- (mk-sz M) sx with last-val pwv tspd
... | vs0 , v , _ , refl , vok , _ , _ with canonical-num {nt = I32} vok
... | i , refl
  with (proj-uN-0 32 i + proj-uN-0 32 (OFFSET ao)) + (M / 8)
         ≤?ⁿ length (BYTES (fun-mem (mk-state s f) (mk-uN 0)))
...   | no  gt = osteps (fire1 (read (mk-state s f) _ _ (load-pack-trap-0 (mk-state s f) i M sx ao (≰⇒> gt))))
...   | yes le
  with ibytes-surj M
         (slice (BYTES (fun-mem (mk-state s f) (mk-uN 0)))
           (proj-uN-0 32 i + proj-uN-0 32 (OFFSET ao)) (M / 8)) (slice-len _ _ _ le)
...     | c , ceq = osteps (fire1 (read (mk-state s f) _ _ (load-pack-val-0 (mk-state s f) i M sx ao c (λ ()) ceq)))
progress-nonval {s = s} {f = f} vs (admininstr-LOAD nt (just lo) ao) rest sok fok ag nv ok ac | _ , _ , _ , _ , e-iok , pwv , tspd | Inn-I64 , refl , refl with lo
... | mk-loadop- (mk-sz M) sx with last-val pwv tspd
... | vs0 , v , _ , refl , vok , _ , _ with canonical-num {nt = I32} vok
... | i , refl
  with (proj-uN-0 32 i + proj-uN-0 32 (OFFSET ao)) + (M / 8)
         ≤?ⁿ length (BYTES (fun-mem (mk-state s f) (mk-uN 0)))
...   | no  gt = osteps (fire1 (read (mk-state s f) _ _ (load-pack-trap-1 (mk-state s f) i M sx ao (≰⇒> gt))))
...   | yes le
  with ibytes-surj M
         (slice (BYTES (fun-mem (mk-state s f) (mk-uN 0)))
           (proj-uN-0 32 i + proj-uN-0 32 (OFFSET ao)) (M / 8)) (slice-len _ _ _ le)
...     | c , ceq = osteps (fire1 (read (mk-state s f) _ _ (load-pack-val-1 (mk-state s f) i M sx ao c (λ ()) ceq)))
-- table.size: [TABLE-SIZE x] ~> [i32.const |refs|]  (always steps)
progress-nonval {s = s} {f = f} vs (admininstr-TABLE-SIZE x) rest sok fok ag nv ok ac =
  osteps (wrap-step vs rest (read (mk-state s f) _ _
    (Step-read--table-size (mk-state s f) x (length (REFS (fun-table (mk-state s f) x))) refl)))
-- memory.grow: [i32.const n, MEMORY-GROW] ~> [i32.const size] (succeed) or [i32.const -1] (fail)
progress-nonval {s = s} {f = f} vs admininstr-MEMORY-GROW rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with mgrow-inv e-iok refl
... | refl , refl with last-val pwv tspd
... | vs0 , v , _ , refl , vok , _ , _ with canonical-num {nt = I32} vok
... | mk-uN n , refl with growmemory (fun-mem (mk-state s f) (mk-uN 0)) n in eq
...   | just mi = osteps (fire1 (memory-grow-succeed (mk-state s f) n mi
                    (λ h → nothing≢just (tr≡ (sym h) eq)) (cong unwrap! eq)))
...   | nothing = osteps (fire1 (memory-grow-fail (mk-state s f) n))
-- v128.narrow: [v1,v2] ~> [v']  (16 source×target shape combos; all premises are ≡, refl)
progress-nonval {s = s} {f = f} vs (admininstr-VNARROW (ishape-X Jnn-I32 (mk-dim N2)) (ishape-X Jnn-I32 (mk-dim N1)) sx) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with vnarrow-inv e-iok refl
... | refl , refl with last-2 pwv tspd
... | vs0 , v1 , v2 , refl , v1ok , v2ok with canonical-vec v1ok | canonical-vec v2ok
... | c-1 , refl | c-2 , refl =
      osteps (fire2 (pure (mk-state s f) _ _ (vnarrow-0 c-1 c-2 N2 N1 sx _ _ _ _ _ refl refl refl refl refl)))
progress-nonval {s = s} {f = f} vs (admininstr-VNARROW (ishape-X Jnn-I32 (mk-dim N2)) (ishape-X Jnn-I64 (mk-dim N1)) sx) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with vnarrow-inv e-iok refl
... | refl , refl with last-2 pwv tspd
... | vs0 , v1 , v2 , refl , v1ok , v2ok with canonical-vec v1ok | canonical-vec v2ok
... | c-1 , refl | c-2 , refl =
      osteps (fire2 (pure (mk-state s f) _ _ (vnarrow-1 c-1 c-2 N2 N1 sx _ _ _ _ _ refl refl refl refl refl)))
progress-nonval {s = s} {f = f} vs (admininstr-VNARROW (ishape-X Jnn-I32 (mk-dim N2)) (ishape-X Jnn-I8 (mk-dim N1)) sx) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with vnarrow-inv e-iok refl
... | refl , refl with last-2 pwv tspd
... | vs0 , v1 , v2 , refl , v1ok , v2ok with canonical-vec v1ok | canonical-vec v2ok
... | c-1 , refl | c-2 , refl =
      osteps (fire2 (pure (mk-state s f) _ _ (vnarrow-2 c-1 c-2 N2 N1 sx _ _ _ _ _ refl refl refl refl refl)))
progress-nonval {s = s} {f = f} vs (admininstr-VNARROW (ishape-X Jnn-I32 (mk-dim N2)) (ishape-X Jnn-I16 (mk-dim N1)) sx) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with vnarrow-inv e-iok refl
... | refl , refl with last-2 pwv tspd
... | vs0 , v1 , v2 , refl , v1ok , v2ok with canonical-vec v1ok | canonical-vec v2ok
... | c-1 , refl | c-2 , refl =
      osteps (fire2 (pure (mk-state s f) _ _ (vnarrow-3 c-1 c-2 N2 N1 sx _ _ _ _ _ refl refl refl refl refl)))
progress-nonval {s = s} {f = f} vs (admininstr-VNARROW (ishape-X Jnn-I64 (mk-dim N2)) (ishape-X Jnn-I32 (mk-dim N1)) sx) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with vnarrow-inv e-iok refl
... | refl , refl with last-2 pwv tspd
... | vs0 , v1 , v2 , refl , v1ok , v2ok with canonical-vec v1ok | canonical-vec v2ok
... | c-1 , refl | c-2 , refl =
      osteps (fire2 (pure (mk-state s f) _ _ (vnarrow-4 c-1 c-2 N2 N1 sx _ _ _ _ _ refl refl refl refl refl)))
progress-nonval {s = s} {f = f} vs (admininstr-VNARROW (ishape-X Jnn-I64 (mk-dim N2)) (ishape-X Jnn-I64 (mk-dim N1)) sx) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with vnarrow-inv e-iok refl
... | refl , refl with last-2 pwv tspd
... | vs0 , v1 , v2 , refl , v1ok , v2ok with canonical-vec v1ok | canonical-vec v2ok
... | c-1 , refl | c-2 , refl =
      osteps (fire2 (pure (mk-state s f) _ _ (vnarrow-5 c-1 c-2 N2 N1 sx _ _ _ _ _ refl refl refl refl refl)))
progress-nonval {s = s} {f = f} vs (admininstr-VNARROW (ishape-X Jnn-I64 (mk-dim N2)) (ishape-X Jnn-I8 (mk-dim N1)) sx) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with vnarrow-inv e-iok refl
... | refl , refl with last-2 pwv tspd
... | vs0 , v1 , v2 , refl , v1ok , v2ok with canonical-vec v1ok | canonical-vec v2ok
... | c-1 , refl | c-2 , refl =
      osteps (fire2 (pure (mk-state s f) _ _ (vnarrow-6 c-1 c-2 N2 N1 sx _ _ _ _ _ refl refl refl refl refl)))
progress-nonval {s = s} {f = f} vs (admininstr-VNARROW (ishape-X Jnn-I64 (mk-dim N2)) (ishape-X Jnn-I16 (mk-dim N1)) sx) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with vnarrow-inv e-iok refl
... | refl , refl with last-2 pwv tspd
... | vs0 , v1 , v2 , refl , v1ok , v2ok with canonical-vec v1ok | canonical-vec v2ok
... | c-1 , refl | c-2 , refl =
      osteps (fire2 (pure (mk-state s f) _ _ (vnarrow-7 c-1 c-2 N2 N1 sx _ _ _ _ _ refl refl refl refl refl)))
progress-nonval {s = s} {f = f} vs (admininstr-VNARROW (ishape-X Jnn-I8 (mk-dim N2)) (ishape-X Jnn-I32 (mk-dim N1)) sx) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with vnarrow-inv e-iok refl
... | refl , refl with last-2 pwv tspd
... | vs0 , v1 , v2 , refl , v1ok , v2ok with canonical-vec v1ok | canonical-vec v2ok
... | c-1 , refl | c-2 , refl =
      osteps (fire2 (pure (mk-state s f) _ _ (vnarrow-8 c-1 c-2 N2 N1 sx _ _ _ _ _ refl refl refl refl refl)))
progress-nonval {s = s} {f = f} vs (admininstr-VNARROW (ishape-X Jnn-I8 (mk-dim N2)) (ishape-X Jnn-I64 (mk-dim N1)) sx) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with vnarrow-inv e-iok refl
... | refl , refl with last-2 pwv tspd
... | vs0 , v1 , v2 , refl , v1ok , v2ok with canonical-vec v1ok | canonical-vec v2ok
... | c-1 , refl | c-2 , refl =
      osteps (fire2 (pure (mk-state s f) _ _ (vnarrow-9 c-1 c-2 N2 N1 sx _ _ _ _ _ refl refl refl refl refl)))
progress-nonval {s = s} {f = f} vs (admininstr-VNARROW (ishape-X Jnn-I8 (mk-dim N2)) (ishape-X Jnn-I8 (mk-dim N1)) sx) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with vnarrow-inv e-iok refl
... | refl , refl with last-2 pwv tspd
... | vs0 , v1 , v2 , refl , v1ok , v2ok with canonical-vec v1ok | canonical-vec v2ok
... | c-1 , refl | c-2 , refl =
      osteps (fire2 (pure (mk-state s f) _ _ (vnarrow-10 c-1 c-2 N2 N1 sx _ _ _ _ _ refl refl refl refl refl)))
progress-nonval {s = s} {f = f} vs (admininstr-VNARROW (ishape-X Jnn-I8 (mk-dim N2)) (ishape-X Jnn-I16 (mk-dim N1)) sx) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with vnarrow-inv e-iok refl
... | refl , refl with last-2 pwv tspd
... | vs0 , v1 , v2 , refl , v1ok , v2ok with canonical-vec v1ok | canonical-vec v2ok
... | c-1 , refl | c-2 , refl =
      osteps (fire2 (pure (mk-state s f) _ _ (vnarrow-11 c-1 c-2 N2 N1 sx _ _ _ _ _ refl refl refl refl refl)))
progress-nonval {s = s} {f = f} vs (admininstr-VNARROW (ishape-X Jnn-I16 (mk-dim N2)) (ishape-X Jnn-I32 (mk-dim N1)) sx) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with vnarrow-inv e-iok refl
... | refl , refl with last-2 pwv tspd
... | vs0 , v1 , v2 , refl , v1ok , v2ok with canonical-vec v1ok | canonical-vec v2ok
... | c-1 , refl | c-2 , refl =
      osteps (fire2 (pure (mk-state s f) _ _ (vnarrow-12 c-1 c-2 N2 N1 sx _ _ _ _ _ refl refl refl refl refl)))
progress-nonval {s = s} {f = f} vs (admininstr-VNARROW (ishape-X Jnn-I16 (mk-dim N2)) (ishape-X Jnn-I64 (mk-dim N1)) sx) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with vnarrow-inv e-iok refl
... | refl , refl with last-2 pwv tspd
... | vs0 , v1 , v2 , refl , v1ok , v2ok with canonical-vec v1ok | canonical-vec v2ok
... | c-1 , refl | c-2 , refl =
      osteps (fire2 (pure (mk-state s f) _ _ (vnarrow-13 c-1 c-2 N2 N1 sx _ _ _ _ _ refl refl refl refl refl)))
progress-nonval {s = s} {f = f} vs (admininstr-VNARROW (ishape-X Jnn-I16 (mk-dim N2)) (ishape-X Jnn-I8 (mk-dim N1)) sx) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with vnarrow-inv e-iok refl
... | refl , refl with last-2 pwv tspd
... | vs0 , v1 , v2 , refl , v1ok , v2ok with canonical-vec v1ok | canonical-vec v2ok
... | c-1 , refl | c-2 , refl =
      osteps (fire2 (pure (mk-state s f) _ _ (vnarrow-14 c-1 c-2 N2 N1 sx _ _ _ _ _ refl refl refl refl refl)))
progress-nonval {s = s} {f = f} vs (admininstr-VNARROW (ishape-X Jnn-I16 (mk-dim N2)) (ishape-X Jnn-I16 (mk-dim N1)) sx) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with vnarrow-inv e-iok refl
... | refl , refl with last-2 pwv tspd
... | vs0 , v1 , v2 , refl , v1ok , v2ok with canonical-vec v1ok | canonical-vec v2ok
... | c-1 , refl | c-2 , refl =
      osteps (fire2 (pure (mk-state s f) _ _ (vnarrow-15 c-1 c-2 N2 N1 sx _ _ _ _ _ refl refl refl refl refl)))

-- v128.splat: [c] ~> [v]  (single rule, generic lanetype via inv-lanes-)
progress-nonval {s = s} {f = f} vs (admininstr-VSPLAT (X lt (mk-dim N))) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with vsplat-inv-p e-iok refl
... | refl , refl with last-val pwv tspd
... | vs0 , v , _ , refl , vok , _ , _ with canonical-num {nt = unpack lt} vok
... | c-1 , refl =
      osteps (fire1 (pure (mk-state s f) _ _ (Step-pure--vsplat lt c-1 N _ refl)))
-- v128.replace_lane: [v, c] ~> [v']  (single rule, generic lanetype; modify handles the index)
progress-nonval {s = s} {f = f} vs (admininstr-VREPLACE-LANE (X lt (mk-dim N)) i) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with vreplace-inv-p e-iok refl
... | refl , refl with last-2 pwv tspd
... | vs0 , v1 , v2 , refl , v1ok , v2ok with canonical-vec v1ok | canonical-num {nt = unpack lt} v2ok
... | c-1 , refl | c-2 , refl =
      osteps (fire2 (pure (mk-state s f) _ _ (Step-pure--vreplace-lane c-1 lt c-2 N i _ refl)))
-- v128.extract_lane: [v] ~> [c]  (6 well-formed shape/sx? combos fire; 6 ill-formed combos refuted via VExtractWF backend-limitation axiom)
progress-nonval {s = s} {f = f} vs (admininstr-VEXTRACT-LANE (X lanetype-I32 (mk-dim N)) nothing i) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with vextract-inv-p e-iok refl
... | refl , bnd with last-val pwv tspd
... | vs0 , v , _ , refl , vok , _ , _ with canonical-vec vok
... | c-1 , refl =
      osteps (fire1 (pure (mk-state s f) _ _ (vextract-lane-num-0 c-1 N i _ (subst (λ z → proj-uN-0 8 i < z) (sym (lanes-length lanetype-I32 N c-1)) bnd) refl)))
progress-nonval {s = s} {f = f} vs (admininstr-VEXTRACT-LANE (X lanetype-I32 (mk-dim N)) (just sx) i) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with vextract-lane-wf e-iok refl
... | ()
progress-nonval {s = s} {f = f} vs (admininstr-VEXTRACT-LANE (X lanetype-I64 (mk-dim N)) nothing i) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with vextract-inv-p e-iok refl
... | refl , bnd with last-val pwv tspd
... | vs0 , v , _ , refl , vok , _ , _ with canonical-vec vok
... | c-1 , refl =
      osteps (fire1 (pure (mk-state s f) _ _ (vextract-lane-num-1 c-1 N i _ (subst (λ z → proj-uN-0 8 i < z) (sym (lanes-length lanetype-I64 N c-1)) bnd) refl)))
progress-nonval {s = s} {f = f} vs (admininstr-VEXTRACT-LANE (X lanetype-I64 (mk-dim N)) (just sx) i) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with vextract-lane-wf e-iok refl
... | ()
progress-nonval {s = s} {f = f} vs (admininstr-VEXTRACT-LANE (X lanetype-F32 (mk-dim N)) nothing i) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with vextract-inv-p e-iok refl
... | refl , bnd with last-val pwv tspd
... | vs0 , v , _ , refl , vok , _ , _ with canonical-vec vok
... | c-1 , refl =
      osteps (fire1 (pure (mk-state s f) _ _ (vextract-lane-num-2 c-1 N i _ (subst (λ z → proj-uN-0 8 i < z) (sym (lanes-length lanetype-F32 N c-1)) bnd) refl)))
progress-nonval {s = s} {f = f} vs (admininstr-VEXTRACT-LANE (X lanetype-F32 (mk-dim N)) (just sx) i) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with vextract-lane-wf e-iok refl
... | ()
progress-nonval {s = s} {f = f} vs (admininstr-VEXTRACT-LANE (X lanetype-F64 (mk-dim N)) nothing i) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with vextract-inv-p e-iok refl
... | refl , bnd with last-val pwv tspd
... | vs0 , v , _ , refl , vok , _ , _ with canonical-vec vok
... | c-1 , refl =
      osteps (fire1 (pure (mk-state s f) _ _ (vextract-lane-num-3 c-1 N i _ (subst (λ z → proj-uN-0 8 i < z) (sym (lanes-length lanetype-F64 N c-1)) bnd) refl)))
progress-nonval {s = s} {f = f} vs (admininstr-VEXTRACT-LANE (X lanetype-F64 (mk-dim N)) (just sx) i) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with vextract-lane-wf e-iok refl
... | ()
progress-nonval {s = s} {f = f} vs (admininstr-VEXTRACT-LANE (X lanetype-I8 (mk-dim N)) (just sx) i) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with vextract-inv-p e-iok refl
... | refl , bnd with last-val pwv tspd
... | vs0 , v , _ , refl , vok , _ , _ with canonical-vec vok
... | c-1 , refl =
      osteps (fire1 (pure (mk-state s f) _ _ (vextract-lane-pack-0 c-1 N sx i _ (subst (λ z → proj-uN-0 8 i < z) (sym (lanes-length lanetype-I8 N c-1)) bnd) refl)))
progress-nonval {s = s} {f = f} vs (admininstr-VEXTRACT-LANE (X lanetype-I8 (mk-dim N)) nothing i) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with vextract-lane-wf e-iok refl
... | ()
progress-nonval {s = s} {f = f} vs (admininstr-VEXTRACT-LANE (X lanetype-I16 (mk-dim N)) (just sx) i) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with vextract-inv-p e-iok refl
... | refl , bnd with last-val pwv tspd
... | vs0 , v , _ , refl , vok , _ , _ with canonical-vec vok
... | c-1 , refl =
      osteps (fire1 (pure (mk-state s f) _ _ (vextract-lane-pack-1 c-1 N sx i _ (subst (λ z → proj-uN-0 8 i < z) (sym (lanes-length lanetype-I16 N c-1)) bnd) refl)))
progress-nonval {s = s} {f = f} vs (admininstr-VEXTRACT-LANE (X lanetype-I16 (mk-dim N)) nothing i) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with vextract-lane-wf e-iok refl
... | ()

-- v128.all_true: [v] ~> [i32]  (4 integer shapes: decide All(lane≠0) → true/false rule; 2 float shapes refuted via vtestop-int-shape)
progress-nonval {s = s} {f = f} vs (admininstr-VTESTOP (X lanetype-I32 (mk-dim N)) ALL-TRUE) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with vtestop-inv e-iok refl
... | refl , refl with last-val pwv tspd
... | vs0 , v , _ , refl , vok , _ , _ with canonical-vec vok
... | c-1 , refl with all-dec? (λ ci → ¬-dec? (proj-uN-0 (lsize (lanetype-Jnn Jnn-I32)) ci ≟ 0)) (lanes- (X (lanetype-Jnn Jnn-I32) (mk-dim N)) c-1)
...   | yes allp = osteps (fire1 (pure (mk-state s f) _ _ (vtestop-true-0 c-1 N _ refl allp)))
...   | no ¬allp = osteps (fire1 (pure (mk-state s f) _ _ (vtestop-false-0 c-1 N
        (λ { (vtestop-true-0-0 _ _ _ eq' all') → ¬allp (subst (All (λ ci → proj-uN-0 (lsize (lanetype-Jnn Jnn-I32)) ci ≢ 0)) eq' all') }))))
progress-nonval {s = s} {f = f} vs (admininstr-VTESTOP (X lanetype-I64 (mk-dim N)) ALL-TRUE) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with vtestop-inv e-iok refl
... | refl , refl with last-val pwv tspd
... | vs0 , v , _ , refl , vok , _ , _ with canonical-vec vok
... | c-1 , refl with all-dec? (λ ci → ¬-dec? (proj-uN-0 (lsize (lanetype-Jnn Jnn-I64)) ci ≟ 0)) (lanes- (X (lanetype-Jnn Jnn-I64) (mk-dim N)) c-1)
...   | yes allp = osteps (fire1 (pure (mk-state s f) _ _ (vtestop-true-1 c-1 N _ refl allp)))
...   | no ¬allp = osteps (fire1 (pure (mk-state s f) _ _ (vtestop-false-1 c-1 N
        (λ { (vtestop-true-0-1 _ _ _ eq' all') → ¬allp (subst (All (λ ci → proj-uN-0 (lsize (lanetype-Jnn Jnn-I64)) ci ≢ 0)) eq' all') }))))
progress-nonval {s = s} {f = f} vs (admininstr-VTESTOP (X lanetype-I8 (mk-dim N)) ALL-TRUE) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with vtestop-inv e-iok refl
... | refl , refl with last-val pwv tspd
... | vs0 , v , _ , refl , vok , _ , _ with canonical-vec vok
... | c-1 , refl with all-dec? (λ ci → ¬-dec? (proj-uN-0 (lsize (lanetype-Jnn Jnn-I8)) ci ≟ 0)) (lanes- (X (lanetype-Jnn Jnn-I8) (mk-dim N)) c-1)
...   | yes allp = osteps (fire1 (pure (mk-state s f) _ _ (vtestop-true-2 c-1 N _ refl allp)))
...   | no ¬allp = osteps (fire1 (pure (mk-state s f) _ _ (vtestop-false-2 c-1 N
        (λ { (vtestop-true-0-2 _ _ _ eq' all') → ¬allp (subst (All (λ ci → proj-uN-0 (lsize (lanetype-Jnn Jnn-I8)) ci ≢ 0)) eq' all') }))))
progress-nonval {s = s} {f = f} vs (admininstr-VTESTOP (X lanetype-I16 (mk-dim N)) ALL-TRUE) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with vtestop-inv e-iok refl
... | refl , refl with last-val pwv tspd
... | vs0 , v , _ , refl , vok , _ , _ with canonical-vec vok
... | c-1 , refl with all-dec? (λ ci → ¬-dec? (proj-uN-0 (lsize (lanetype-Jnn Jnn-I16)) ci ≟ 0)) (lanes- (X (lanetype-Jnn Jnn-I16) (mk-dim N)) c-1)
...   | yes allp = osteps (fire1 (pure (mk-state s f) _ _ (vtestop-true-3 c-1 N _ refl allp)))
...   | no ¬allp = osteps (fire1 (pure (mk-state s f) _ _ (vtestop-false-3 c-1 N
        (λ { (vtestop-true-0-3 _ _ _ eq' all') → ¬allp (subst (All (λ ci → proj-uN-0 (lsize (lanetype-Jnn Jnn-I16)) ci ≢ 0)) eq' all') }))))
progress-nonval {s = s} {f = f} vs (admininstr-VTESTOP (X lanetype-F32 (mk-dim N)) op) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with vtestop-int-shape e-iok refl
... | ()
progress-nonval {s = s} {f = f} vs (admininstr-VTESTOP (X lanetype-F64 (mk-dim N)) op) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with vtestop-int-shape e-iok refl
... | ()

-- v128.cvtop: delegate to vcvtop-step (operand via canonical-vec; the step is fully determined there).
progress-nonval {s = s} {f = f} vs (admininstr-VCVTOP (X Lnn2 (mk-dim M2)) (X Lnn1 (mk-dim M1)) op) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with vcvtop-inv e-iok refl
... | refl , refl with last-val pwv tspd
... | vs0 , v , _ , refl , vok , _ , _ with canonical-vec vok
... | c-1 , refl = osteps (fire1 (pure (mk-state s f) _ _ (proj₂ (vcvtop-step c-1 e-iok))))
-- v128.swizzle (packed I8/I16): both holds-upto premises discharged — the byte index bound via
-- uN-bound (2^8=256=length of the padded table), and k < length ci-lst via lanes-length.
progress-nonval {s = s} {f = f} vs (admininstr-VSWIZZLE (ishape-X Jnn-I8 (mk-dim M))) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with vswizzle-inv e-iok refl
... | refl , refl with last-2 pwv tspd
... | vs0 , v1 , v2 , refl , v1ok , v2ok with canonical-vec v1ok | canonical-vec v2ok
... | c-1 , refl | c-2 , refl =
      osteps (fire2 (pure (mk-state s f) _ _
        (vswizzle-0 c-1 c-2 M _
          (lanes- (X (lanetype-packtype I8) (mk-dim M)) c-2)
          (lanes- (X (lanetype-packtype I8) (mk-dim M)) c-1 ++ replicate (256 ∸ M) (mk-uN 0)) 0
          refl refl
          (universal (λ k → subst (λ z → proj-uN-0 (psize I8) (lanes- (X (lanetype-packtype I8) (mk-dim M)) c-2 [ k ]!) < z)
                        (sym (cprime-len (lanes- (X (lanetype-packtype I8) (mk-dim M)) c-1) (mk-uN 0) M
                              (lanes-length (lanetype-packtype I8) M c-1) (≤-trans (dim-bound (mk-dim M)) (m≤m+n 16 240))))
                        (uN-bound (psize I8) (lanes- (X (lanetype-packtype I8) (mk-dim M)) c-2 [ k ]!))) (upTo M))
          (tabulate (λ {k} k∈ → subst (λ z → k < z) (sym (lanes-length (lanetype-packtype I8) M c-2)) (∈-upTo⁻ k∈)))
          refl)))
-- v128.swizzle / v128.shuffle non-I8 shapes (Jnn-I16/I32/I64): typeable-but-stuck junk (i16 swizzle
-- is unsound; nothing else is constructible), refuted via vswizzle-packed / vshuffle-packed.
-- (v128.shuffle I8 val case is pending: it needs the dropped |i*|=dim lane-count invariant.)
progress-nonval {s = s} {f = f} vs (admininstr-VSWIZZLE (ishape-X Jnn-I16 (mk-dim N))) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with vswizzle-packed e-iok refl
... | ()
progress-nonval {s = s} {f = f} vs (admininstr-VSWIZZLE (ishape-X Jnn-I32 (mk-dim N))) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with vswizzle-packed e-iok refl
... | ()
progress-nonval {s = s} {f = f} vs (admininstr-VSWIZZLE (ishape-X Jnn-I64 (mk-dim N))) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with vswizzle-packed e-iok refl
... | ()
progress-nonval {s = s} {f = f} vs (admininstr-VSHUFFLE (ishape-X Jnn-I8 (mk-dim N)) ls) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with vshuffle-inv e-iok refl
... | refl , refl with last-2 pwv tspd
... | vs0 , v1 , v2 , refl , v1ok , v2ok with canonical-vec v1ok | canonical-vec v2ok
... | c-1 , refl | c-2 , refl =
      osteps (fire2 (pure (mk-state s f) _ _
        (vshuffle-0 c-1 c-2 N ls _
          (lanes- (X (lanetype-packtype I8) (mk-dim N)) c-1 ++ lanes- (X (lanetype-packtype I8) (mk-dim N)) c-2) 0
          refl
          (tabulate (λ {k} k∈ → subst (λ z → proj-uN-0 8 (ls [ k ]!) < z)
                       (sym (cshuf-len c-1 c-2 (lanetype-packtype I8) N))
                       (all-index! ls k (subst (λ z → k < z) (sym lc) (∈-upTo⁻ k∈)) fa)))
          (tabulate (λ {k} k∈ → subst (λ z → k < z) (sym lc) (∈-upTo⁻ k∈)))
          refl)))
   where
     fa = vshuffle-inv-p e-iok refl
     lc = vshuffle-lanecount e-iok refl
progress-nonval {s = s} {f = f} vs (admininstr-VSHUFFLE (ishape-X Jnn-I16 (mk-dim N)) ls) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with vshuffle-packed e-iok refl
... | ()
progress-nonval {s = s} {f = f} vs (admininstr-VSHUFFLE (ishape-X Jnn-I32 (mk-dim N)) ls) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with vshuffle-packed e-iok refl
... | ()
progress-nonval {s = s} {f = f} vs (admininstr-VSHUFFLE (ishape-X Jnn-I64 (mk-dim N)) ls) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with vshuffle-packed e-iok refl
... | ()
-- ref.is_null: [ref] ~> [i32]  (decide whether the ref is null)
progress-nonval {s = s} {f = f} vs admininstr-REF-IS-NULL rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with refisnull-inv e-iok refl
... | rt , refl , refl with last-val pwv tspd
... | vs0 , v , _ , refl , vok , _ , _ with canonical-ref vok
... | ref-REF-NULL rt' , refl =
      osteps (fire1 (pure (mk-state s f) _ _ (ref-is-null-true (ref-REF-NULL rt') rt' refl)))
... | REF-FUNC-ADDR a , refl =
      osteps (fire1 (pure (mk-state s f) _ _ (ref-is-null-false (REF-FUNC-ADDR a)
        (λ b → let (r , rt , eseq , nulleq) = before-ref-null b in funcaddr≢refnull (tr≡ (tr≡ (cong list-head-ref eseq) (adm-ref-of∘ref r)) nulleq)))))
... | REF-HOST-ADDR a , refl =
      osteps (fire1 (pure (mk-state s f) _ _ (ref-is-null-false (REF-HOST-ADDR a)
        (λ b → let (r , rt , eseq , nulleq) = before-ref-null b in hostaddr≢refnull (tr≡ (tr≡ (cong list-head-ref eseq) (adm-ref-of∘ref r)) nulleq)))))
-- call_indirect: decide index-in-bounds, table entry is a func addr, addr-in-bounds, type match;
-- fire call-indirect-call → CALL-ADDR on success, else call-indirect-trap (refuting the before-pred).
progress-nonval {s = s} {f = f} vs (admininstr-CALL-INDIRECT x y) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with cind-inv e-iok refl
... | t1 , deq with peel-top-i32 pwv tspd deq
... | vs0 , c , refl with proj-uN-0 32 c <?ⁿ length (REFS (fun-table (mk-state s f) x))
...   | no oob = osteps (fire1 (read (mk-state s f) _ _
        (call-indirect-trap (mk-state s f) c x y (λ b → oob (proj₁ (proj₂ (cit-align b)))))))
...   | yes i< with (REFS (fun-table (mk-state s f) x)) [ proj-uN-0 32 c ]! in refeq
...     | ref-REF-NULL rt = osteps (fire1 (read (mk-state s f) _ _
          (call-indirect-trap (mk-state s f) c x y
            (λ b → nullref≢funcaddr (tr≡ (sym refeq) (proj₁ (proj₂ (proj₂ (cit-align b)))))))))
...     | REF-HOST-ADDR h = osteps (fire1 (read (mk-state s f) _ _
          (call-indirect-trap (mk-state s f) c x y
            (λ b → hostref≢funcaddr (tr≡ (sym refeq) (proj₁ (proj₂ (proj₂ (cit-align b)))))))))
...     | REF-FUNC-ADDR a with a <?ⁿ length (fun-funcinst (mk-state s f))
...       | no aoob = osteps (fire1 (read (mk-state s f) _ _
            (call-indirect-trap (mk-state s f) c x y
              (λ b → aoob (subst (_< length (fun-funcinst (mk-state s f)))
                            (sym (funcaddr-inj (tr≡ (sym refeq) (proj₁ (proj₂ (proj₂ (cit-align b)))))))
                            (proj₁ (proj₂ (proj₂ (proj₂ (cit-align b))))))))))
...       | yes a< with (fun-type (mk-state s f) y) ≟ft (funcinst-TYPE ((fun-funcinst (mk-state s f)) [ a ]!))
...         | yes teq = osteps (fire1 (read (mk-state s f) _ _
              (call-indirect-call (mk-state s f) c x y a i< refeq a< teq)))
...         | no tne = osteps (fire1 (read (mk-state s f) _ _
              (call-indirect-trap (mk-state s f) c x y
                (λ b → tne (subst (λ aa → fun-type (mk-state s f) y ≡ funcinst-TYPE ((fun-funcinst (mk-state s f)) [ aa ]!))
                             (sym (funcaddr-inj (tr≡ (sym refeq) (proj₁ (proj₂ (proj₂ (cit-align b)))))))
                             (proj₂ (proj₂ (proj₂ (proj₂ (cit-align b))))))))))
-- memory.size: [MEMORY-SIZE] ~> [i32.const |mem|/pagesize]  (derive the page-count equation from
-- Meminst-ok via the frame mem-link → Store-ok → smok).
progress-nonval {s = s} {f = f} vs admininstr-MEMORY-SIZE rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with msize-facts e-iok refl
... | mt , m< , mlk with meminst-pages (smok sok (msize-bound (frame-facts fok) (subst (λ z → 0 < length z) (Agree.mem≡ ag) m<)))
...   | v-n , leneq =
        osteps (wrap-step vs rest (read (mk-state s f) _ _
          (Step-read--memory-size (mk-state s f) v-n (tr≡ (*-assoc v-n 64 Ki) (sym leneq)))))
-- extend: the standalone instr-EXTEND is never well-typed (dead artifact) — refute the typing.
progress-nonval vs (admininstr-EXTEND nt n) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , _ , _ = ⊥-elim (extend-imposs e-iok refl)
-- value heads: excluded by nv (¬ IsVal e); needed once progress-rest is deleted
progress-nonval vs (admininstr-CONST nt c) rest sok fok ag nv ok ac = ⊥-elim (nv (isv-const nt c))
progress-nonval vs (admininstr-VCONST sh c) rest sok fok ag nv ok ac = ⊥-elim (nv (isv-vconst sh c))
progress-nonval vs (admininstr-REF-NULL rt) rest sok fok ag nv ok ac = ⊥-elim (nv (isv-null rt))
progress-nonval vs (admininstr-REF-FUNC-ADDR a) rest sok fok ag nv ok ac = ⊥-elim (nv (isv-func a))
progress-nonval vs (admininstr-REF-HOST-ADDR a) rest sok fok ag nv ok ac = ⊥-elim (nv (isv-host a))
-- v128.store_lane: OOB decision; trap branch is a leaf (oob rule generic in width); in-bounds
-- branch nests the width-case last (each width a leaf) — no with-returns.
progress-nonval {s = s} {f = f} vs (admininstr-VSTORE-LANE V128 (mk-sz v-n) ao j) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with vstlane-inv e-iok refl
... | refl , refl with last-2 pwv tspd
... | vs0 , v1 , v2 , refl , v1ok , v2ok with canonical-num {nt = I32} v1ok | canonical-vec v2ok
... | i , refl | c , refl with (proj-uN-0 32 i + proj-uN-0 32 (OFFSET ao)) + v-n ≤?ⁿ length (BYTES (fun-mem (mk-state s f) (mk-uN 0)))
...   | no  gt = osteps (fire2 (vstore-lane-oob (mk-state s f) i c v-n ao j (≰⇒> gt)))
...   | yes le with vstore-lane-width e-iok refl
...     | vslw-i32 = osteps (fire2 (vstore-lane-val-0 (mk-state s f) i c (jsize Jnn-I32) ao j _ (128 / jsize Jnn-I32) le refl refl (subst (λ z → proj-uN-0 8 j < z) (sym (lanes-length (lanetype-Jnn Jnn-I32) (128 / jsize Jnn-I32) c)) (vstlane-jb e-iok refl)) refl))
...     | vslw-i64 = osteps (fire2 (vstore-lane-val-1 (mk-state s f) i c (jsize Jnn-I64) ao j _ (128 / jsize Jnn-I64) le refl refl (subst (λ z → proj-uN-0 8 j < z) (sym (lanes-length (lanetype-Jnn Jnn-I64) (128 / jsize Jnn-I64) c)) (vstlane-jb e-iok refl)) refl))
...     | vslw-i8 = osteps (fire2 (vstore-lane-val-2 (mk-state s f) i c (jsize Jnn-I8) ao j _ (128 / jsize Jnn-I8) le refl refl (subst (λ z → proj-uN-0 8 j < z) (sym (lanes-length (lanetype-Jnn Jnn-I8) (128 / jsize Jnn-I8) c)) (vstlane-jb e-iok refl)) refl))
...     | vslw-i16 = osteps (fire2 (vstore-lane-val-3 (mk-state s f) i c (jsize Jnn-I16) ao j _ (128 / jsize Jnn-I16) le refl refl (subst (λ z → proj-uN-0 8 j < z) (sym (lanes-length (lanetype-Jnn Jnn-I16) (128 / jsize Jnn-I16) c)) (vstlane-jb e-iok refl)) refl))


-- v128.load_lane: OOB decision (trap leaf, oob generic in width); in-bounds nests width (leaves)
-- using let (k,keq)=ibytes-surj to avoid an inner with; modify handles the lane index.
progress-nonval {s = s} {f = f} vs (admininstr-VLOAD-LANE V128 (mk-sz v-n) ao j) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with vloadlane-inv e-iok refl
... | refl , refl with last-2 pwv tspd
... | vs0 , v1 , v2 , refl , v1ok , v2ok with canonical-num {nt = I32} v1ok | canonical-vec v2ok
... | i , refl | c-1 , refl with (proj-uN-0 32 i + proj-uN-0 32 (OFFSET ao)) + (v-n / 8) ≤?ⁿ length (BYTES (fun-mem (mk-state s f) (mk-uN 0)))
...   | no  gt = osteps (fire2 (read (mk-state s f) _ _ (vload-lane-oob (mk-state s f) i c-1 v-n ao j (≰⇒> gt))))
...   | yes le with vload-lane-width e-iok refl
...     | vslw-i32 = let (k , keq) = ibytes-surj (jsize Jnn-I32) (slice (BYTES (fun-mem (mk-state s f) (mk-uN 0))) (proj-uN-0 32 i + proj-uN-0 32 (OFFSET ao)) (jsize Jnn-I32 / 8)) (slice-len _ _ _ le)
                 in osteps (fire2 (read (mk-state s f) _ _ (vload-lane-val-0 (mk-state s f) i c-1 (jsize Jnn-I32) ao j _ k (128 / jsize Jnn-I32) keq refl refl refl)))
...     | vslw-i64 = let (k , keq) = ibytes-surj (jsize Jnn-I64) (slice (BYTES (fun-mem (mk-state s f) (mk-uN 0))) (proj-uN-0 32 i + proj-uN-0 32 (OFFSET ao)) (jsize Jnn-I64 / 8)) (slice-len _ _ _ le)
                 in osteps (fire2 (read (mk-state s f) _ _ (vload-lane-val-1 (mk-state s f) i c-1 (jsize Jnn-I64) ao j _ k (128 / jsize Jnn-I64) keq refl refl refl)))
...     | vslw-i8 = let (k , keq) = ibytes-surj (jsize Jnn-I8) (slice (BYTES (fun-mem (mk-state s f) (mk-uN 0))) (proj-uN-0 32 i + proj-uN-0 32 (OFFSET ao)) (jsize Jnn-I8 / 8)) (slice-len _ _ _ le)
                 in osteps (fire2 (read (mk-state s f) _ _ (vload-lane-val-2 (mk-state s f) i c-1 (jsize Jnn-I8) ao j _ k (128 / jsize Jnn-I8) keq refl refl refl)))
...     | vslw-i16 = let (k , keq) = ibytes-surj (jsize Jnn-I16) (slice (BYTES (fun-mem (mk-state s f) (mk-uN 0))) (proj-uN-0 32 i + proj-uN-0 32 (OFFSET ao)) (jsize Jnn-I16 / 8)) (slice-len _ _ _ le)
                 in osteps (fire2 (read (mk-state s f) _ _ (vload-lane-val-3 (mk-state s f) i c-1 (jsize Jnn-I16) ao j _ k (128 / jsize Jnn-I16) keq refl refl refl)))

-- v128.load (plain, vloadop = nothing): untypeable (vloadN-inv) — vacuous.
progress-nonval {s = s} {f = f} vs (admininstr-VLOAD V128 nothing ao) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , _ , _ = ⊥-elim (vloadN-inv e-iok refl)
-- v128.load (ZERO): generic width; OOB (trap leaf) else ibytes-surj + extend--.
progress-nonval {s = s} {f = f} vs (admininstr-VLOAD V128 (just (vloadop-ZERO v-n)) ao) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with vzero-inv e-iok refl
... | refl , refl with last-val pwv tspd
... | vs0 , v , _ , refl , vok , _ , _ with canonical-num {nt = I32} vok
... | i , refl with (proj-uN-0 32 i + proj-uN-0 32 (OFFSET ao)) + (v-n / 8) ≤?ⁿ length (BYTES (fun-mem (mk-state s f) (mk-uN 0)))
...   | no  gt = osteps (fire1 (read (mk-state s f) _ _ (vload-zero-oob (mk-state s f) i v-n ao (≰⇒> gt))))
...   | yes le = let (j , jeq) = ibytes-surj v-n (slice (BYTES (fun-mem (mk-state s f) (mk-uN 0))) (proj-uN-0 32 i + proj-uN-0 32 (OFFSET ao)) (v-n / 8)) (slice-len _ _ _ le)
               in osteps (fire1 (read (mk-state s f) _ _ (vload-zero-val (mk-state s f) i v-n ao _ j jeq refl)))
-- v128.load (SPLAT): width via vload-splat-width; OOB (trap leaf) else ibytes-surj + inv-lanes-.
progress-nonval {s = s} {f = f} vs (admininstr-VLOAD V128 (just (SPLAT v-n)) ao) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with vsplat-inv2 e-iok refl
... | refl , refl with last-val pwv tspd
... | vs0 , v , _ , refl , vok , _ , _ with canonical-num {nt = I32} vok
... | i , refl with (proj-uN-0 32 i + proj-uN-0 32 (OFFSET ao)) + (v-n / 8) ≤?ⁿ length (BYTES (fun-mem (mk-state s f) (mk-uN 0)))
...   | no  gt = osteps (fire1 (read (mk-state s f) _ _ (vload-splat-oob (mk-state s f) i v-n ao (≰⇒> gt))))
...   | yes le with vload-splat-width e-iok refl
...     | vslw-i32 = let (j , jeq) = ibytes-surj (jsize Jnn-I32) (slice (BYTES (fun-mem (mk-state s f) (mk-uN 0))) (proj-uN-0 32 i + proj-uN-0 32 (OFFSET ao)) (jsize Jnn-I32 / 8)) (slice-len _ _ _ le)
                 in osteps (fire1 (read (mk-state s f) _ _ (vload-splat-val-0 (mk-state s f) i (jsize Jnn-I32) ao _ j (128 / jsize Jnn-I32) jeq refl refl refl)))
...     | vslw-i64 = let (j , jeq) = ibytes-surj (jsize Jnn-I64) (slice (BYTES (fun-mem (mk-state s f) (mk-uN 0))) (proj-uN-0 32 i + proj-uN-0 32 (OFFSET ao)) (jsize Jnn-I64 / 8)) (slice-len _ _ _ le)
                 in osteps (fire1 (read (mk-state s f) _ _ (vload-splat-val-1 (mk-state s f) i (jsize Jnn-I64) ao _ j (128 / jsize Jnn-I64) jeq refl refl refl)))
...     | vslw-i8 = let (j , jeq) = ibytes-surj (jsize Jnn-I8) (slice (BYTES (fun-mem (mk-state s f) (mk-uN 0))) (proj-uN-0 32 i + proj-uN-0 32 (OFFSET ao)) (jsize Jnn-I8 / 8)) (slice-len _ _ _ le)
                 in osteps (fire1 (read (mk-state s f) _ _ (vload-splat-val-2 (mk-state s f) i (jsize Jnn-I8) ao _ j (128 / jsize Jnn-I8) jeq refl refl refl)))
...     | vslw-i16 = let (j , jeq) = ibytes-surj (jsize Jnn-I16) (slice (BYTES (fun-mem (mk-state s f) (mk-uN 0))) (proj-uN-0 32 i + proj-uN-0 32 (OFFSET ao)) (jsize Jnn-I16 / 8)) (slice-len _ _ _ le)
                 in osteps (fire1 (read (mk-state s f) _ _ (vload-splat-val-3 (mk-state s f) i (jsize Jnn-I16) ao _ j (128 / jsize Jnn-I16) jeq refl refl refl)))

-- v128.load (SHAPEX-): OOB (trap leaf, generic width) else width-case; list-surj deserializes N lanes.
progress-nonval {s = s} {f = f} vs (admininstr-VLOAD V128 (just (SHAPEX- v-M v-N v-sx)) ao) rest sok fok ag nv ok ac with focus ok
... | _ , _ , _ , _ , e-iok , pwv , tspd with vshape-inv e-iok refl
... | refl , refl with last-val pwv tspd
... | vs0 , v , _ , refl , vok , _ , _ with canonical-num {nt = I32} vok
... | i , refl with (proj-uN-0 32 i + proj-uN-0 32 (OFFSET ao)) + ((v-M * v-N) / 8) ≤?ⁿ length (BYTES (fun-mem (mk-state s f) (mk-uN 0)))
...   | no  gt = osteps (fire1 (read (mk-state s f) _ _ (vload-shape-oob (mk-state s f) i v-M v-N v-sx ao (≰⇒> gt))))
...   | yes le with vload-shape-width e-iok refl
...     | vshw-i32 = let (jl , lenq , fa) = list-surj 16 (BYTES (fun-mem (mk-state s f) (mk-uN 0))) (proj-uN-0 32 i + proj-uN-0 32 (OFFSET ao)) v-N le
                 in osteps (fire1 (read (mk-state s f) _ _ (vload-shape-val-0 (mk-state s f) i 16 v-N v-sx ao _ jl lenq fa refl refl)))
...     | vshw-i64 = let (jl , lenq , fa) = list-surj 32 (BYTES (fun-mem (mk-state s f) (mk-uN 0))) (proj-uN-0 32 i + proj-uN-0 32 (OFFSET ao)) v-N le
                 in osteps (fire1 (read (mk-state s f) _ _ (vload-shape-val-1 (mk-state s f) i 32 v-N v-sx ao _ jl lenq fa refl refl)))
...     | vshw-i8 = let (jl , lenq , fa) = list-surj 4 (BYTES (fun-mem (mk-state s f) (mk-uN 0))) (proj-uN-0 32 i + proj-uN-0 32 (OFFSET ao)) v-N le
                 in osteps (fire1 (read (mk-state s f) _ _ (vload-shape-val-2 (mk-state s f) i 4 v-N v-sx ao _ jl lenq fa refl refl)))
...     | vshw-i16 = let (jl , lenq , fa) = list-surj 8 (BYTES (fun-mem (mk-state s f) (mk-uN 0))) (proj-uN-0 32 i + proj-uN-0 32 (OFFSET ao)) v-N le
                 in osteps (fire1 (read (mk-state s f) _ _ (vload-shape-val-3 (mk-state s f) i 8 v-N v-sx ao _ jl lenq fa refl refl)))

-- remaining heads: scaffolded
-- ===== Batch E: control / administrative heads =====
-- BR: stuck on a branch — propagate up to the enclosing LABEL-.
progress-nonval vs (admininstr-BR l) rest sok fok ag nv ok ac = obranch l vs rest refl
-- RETURN: propagate up to the enclosing FRAME-.
progress-nonval vs admininstr-RETURN rest sok fok ag nv ok ac = oreturn vs rest refl
-- TRAP in a non-empty context: trap-vals collapse (bare TRAP handled above).
progress-nonval {s = s} {f = f} (v ∷ vs) admininstr-TRAP rest sok fok ag nv ok ac =
  osteps (_ , pure (mk-state s f) _ _ (trap-vals-adm (v ∷ vs) rest (inj₁ (λ ()))))
progress-nonval {s = s} {f = f} [] admininstr-TRAP (r ∷ rest) sok fok ag nv ok ac =
  osteps (_ , pure (mk-state s f) _ _ (trap-vals-adm [] (r ∷ rest) (inj₂ (λ ()))))
-- CALL-ADDR: invoke the function (build the activation frame).
-- CALL-ADDR: invoke — peel the k=|t1| arguments, build the activation frame
-- (locals = args ++ zero-initialised declared locals) and fire call-addr.
progress-nonval {s = s} {f = f} vs (CALL-ADDR a) rest sok fok ag nv ok ac with focus ok
... | d , c , p , _ , e-iok , pwv , tspd with caddr-inv e-iok refl
... | extok with xa-func-inv extok
... | a< , ftlk with sfok sok a< | peel-row p pwv tspd
... | fiok | vs0 , vs1 , refl , fd with funcinst-parts fiok
... | mm , x , t-lst , body , t1 , t2 , recordeq , fteq , forbot =
      let fteq' : mk-functype (mk-list t1) (mk-list t2) ≡ mk-functype (mk-list d) (mk-list c)
          fteq' = tr≡ (sym (cong funcinst-TYPE recordeq)) ftlk
          klen : length t1 ≡ length vs1
          klen = tr≡ (cong length (proj₁ (ft-inj fteq'))) (pw-length fd)
      in osteps (fire-row (read (mk-state s f) _ _
           (call-addr (mk-state s f) (length vs1) vs1 a (length t2)
             (record { LOCALS = vs1 ++ map (λ t → unwrap! (default- t)) t-lst
                     ; frame-MODULE = mm })
             body t1 t2 mm (func-FUNC x (map (λ t → LOCAL t) t-lst) body) x t-lst
             refl refl klen a< recordeq refl (defaults-forall forbot) refl)))
-- LABEL-: recurse into the label body and dispatch on its outcome.
progress-nonval {s = s} {f = f} vs (LABEL- n instrs body) rest sok fok ag nv ok (acc-wf rs) with focus ok
... | d , c , p , ts , e-iok , pwv , tspd with label-inv e-iok refl
... | refl , t' , lenq , contTy , bodyTy
        with body-progress sok fok (agree-labC t' ag) bodyTy (rs (size-label vs n instrs body rest))
...   | ovals vs' eq =
        osteps (wrap-step vs rest
          (pure (mk-state s f) _ _
            (subst (λ z → Step-pure ((LABEL- n instrs z) ∷ []) (map (λ v → admininstr-val v) vs'))
              (sym eq) (label-vals n instrs vs'))))
...   | otrap eq =
        osteps (wrap-step vs rest
          (pure (mk-state s f) _ _
            (subst (λ z → Step-pure ((LABEL- n instrs z) ∷ []) (admininstr-TRAP ∷ []))
              (sym eq) (trap-label n instrs))))
...   | osteps (mk-config (mk-state s' f') body' , st) =
        osteps (wrap-step vs rest (ctxt-label (mk-state s f) n instrs body (mk-state s' f') body' st))
...   | obranch (mk-uN 0) vs' rest' eq =
        let n≤ = subst (_≤ length vs') lenq
                   (label0-bound t' vs' (subst (λ z → Instrs-ok2 _ _ z _) eq bodyTy))
            (vs0 , vs1 , spliteq , len1) = split-last vs' n n≤
            eq' = tr≡ eq (cong (λ w → map (λ v → admininstr-val v) w
                                       ++ (admininstr-BR (mk-uN 0) ∷ rest')) spliteq)
        in osteps (wrap-step vs rest
             (pure (mk-state s f) _ _
               (subst (λ z → Step-pure ((LABEL- n instrs z) ∷ [])
                        (map (λ v → admininstr-val v) vs1 ++ map (λ i → admininstr-instr i) instrs))
                 (sym eq') (br-zero-adm n instrs vs0 vs1 rest' len1))))
...   | obranch (mk-uN (suc k')) vs' rest' eq =
        osteps (wrap-step vs rest
          (pure (mk-state s f) _ _
            (subst (λ z → Step-pure ((LABEL- n instrs z) ∷ [])
                     (map (λ v → admininstr-val v) vs' ++ (admininstr-BR (mk-uN k') ∷ [])))
              (sym eq) (br-succ-adm n instrs vs' k' rest'))))
...   | oreturn vs' rest' eq =
        osteps (wrap-step vs rest
          (pure (mk-state s f) _ _
            (subst (λ z → Step-pure ((LABEL- n instrs z) ∷ [])
                     (map (λ v → admininstr-val v) vs' ++ (admininstr-RETURN ∷ [])))
              (sym eq) (return-label-adm n instrs vs' rest'))))
-- FRAME-: recurse into the activation body (inner frame) and dispatch.
progress-nonval {s = s} {f = f} vs (FRAME- n fr body) rest sok fok ag nv ok (acc-wf rs) with focus ok
... | d , c , p , ts , e-iok , pwv , tspd with frame-inv e-iok refl
... | refl , lenc , C' , frok , mk-Expr-ok2 _ _ _ _ bodyTy
        with body-progress sok frok (agree-retC c agree-refl) bodyTy (rs (size-frame vs n fr body rest))
...   | otrap eq =
        osteps (wrap-step vs rest
          (pure (mk-state s f) _ _
            (subst (λ z → Step-pure ((FRAME- n fr z) ∷ []) (admininstr-TRAP ∷ []))
              (sym eq) (trap-frame n fr))))
...   | osteps (mk-config (mk-state s' fr'') body' , st) =
        osteps (wrap-step vs rest (ctxt-frame s f n fr body s' fr'' body' st))
...   | ovals vs' eq =
        osteps (wrap-step vs rest
          (pure (mk-state s f) _ _
            (subst (λ z → Step-pure ((FRAME- n fr z) ∷ []) (map (λ v → admininstr-val v) vs'))
              (sym eq)
              (frame-vals n fr vs'
                (let (ts , pwv , rtsub) = row-inv vs' (subst (λ z → Instrs-ok2 _ _ z _) eq bodyTy)
                 in tr≡ (tr≡ (sym (pw-length pwv)) (rtlen rtsub)) lenc)))))
...   | oreturn vs' rest' eq =
        let n≤ = subst (_≤ length vs') lenc
                   (return-bound vs' refl (subst (λ z → Instrs-ok2 _ _ z _) eq bodyTy))
            (vs0 , vs1 , spliteq , len1) = split-last vs' n n≤
            eq' = tr≡ eq (cong (λ w → map (λ v → admininstr-val v) w
                                       ++ (admininstr-RETURN ∷ rest')) spliteq)
        in osteps (wrap-step vs rest
             (pure (mk-state s f) _ _
               (subst (λ z → Step-pure ((FRAME- n fr z) ∷ []) (map (λ v → admininstr-val v) vs1))
                 (sym eq') (return-frame-adm n fr vs0 vs1 rest' len1))))
...   | obranch l' vs' rest' eq =
        ⊥-elim (no-branch-ctx vs' (frame-labels-empty frok)
          (subst (λ z → Instrs-ok2 _ _ z _) eq bodyTy))

-- At the closed top-level context, a BR (resp. RETURN) reaching the head is
-- ill-typed: the frame context has empty LABELS (resp. RETURN = nothing).
no-branch : ∀ {s f C u2 l vs rest} → Frame-ok s f C →
  Instrs-ok2 s C (map (λ v → admininstr-val v) vs ++ (admininstr-BR l ∷ rest))
    (mk-functype (mk-list []) (mk-list u2)) → ⊥
no-branch fok ok with focus ok
... | _ , _ , _ , _ , e-iok , _ , _ with br-inv e-iok refl
... | _ , _ , l< , _ = n≮0 (subst (λ z → _ < length z) (frame-labels-empty fok) l<)

no-return : ∀ {s f C u2 vs rest} → Frame-ok s f C →
  Instrs-ok2 s C (map (λ v → admininstr-val v) vs ++ (admininstr-RETURN ∷ rest))
    (mk-functype (mk-list []) (mk-list u2)) → ⊥
no-return fok ok with focus ok
... | _ , _ , _ , _ , e-iok , _ , _ with return-inv e-iok refl
... | _ , _ , reteq
      with subst (λ z → z ≡ just _) (FrameFacts.ret-nothing (frame-facts fok)) reteq
...      | ()

progress-decompose : ∀ {s f C es u2} →
  Store-ok s → Frame-ok s f C →
  Instrs-ok2 s C es (mk-functype (mk-list []) (mk-list u2)) →
  (Σ (List val) λ vs → es ≡ map (λ v → admininstr-val v) vs) ⊎
  (es ≡ admininstr-TRAP ∷ []) ⊎
  (Σ config λ c' → Step (mk-config (mk-state s f) es) c')
progress-decompose {es = es} sok fok ok with body-progress sok fok agree-refl ok (<-wellFounded (adm-size es))
... | ovals vs eq          = inj₁ (vs , eq)
... | otrap eq             = inj₂ (inj₁ eq)
... | osteps stp           = inj₂ (inj₂ stp)
... | obranch l vs rest eq = ⊥-elim (no-branch fok (subst (λ z → Instrs-ok2 _ _ z _) eq ok))
... | oreturn vs rest eq   = ⊥-elim (no-return fok (subst (λ z → Instrs-ok2 _ _ z _) eq ok))

progress : ProgressStmt
progress (mk-config (mk-state s f) es) rt
  (mk-Config-ok _ _ _ tl C (mk-State-ok _ _ _ sok fok) (mk-Expr-ok2 _ _ _ _ ok))
  with progress-decompose sok fok ok
... | inj₁ vs = inj₁ (inj₁ vs)
... | inj₂ (inj₁ tr) = inj₁ (inj₂ tr)
... | inj₂ (inj₂ stp) = inj₂ stp

------------------------------------------------------------------------
-- 11. B2 STATUS: COUNTEREXAMPLE DEAD.
--
-- After the regeneration (dimension premises for iterations occurring
-- inside equation premises), Step-read--block carries
--     length val* = k ,  length t_2* = n ,  length t_1* = k
-- alongside  blocktype(z,bt) = t_1* -> t_2*.  The under-capture
-- derivation from attempt #1 / round 1 of this file
-- (val* = [], blocktype = [i32] -> [], k = 0) is now UNDERIVABLE: its
-- Step-read--block application would need the premise
--     length (valtype-I32 ∷ []) ≡ 0
-- which is 1 ≡ 0 -- Agda rejects the old derivation with exactly that
-- unsolved constraint.  Accordingly, preservation for block and loop
-- is now PROVED above (pres-read), using the new premises to link the
-- value row's inferred types to the blocktype's t_1^k.
------------------------------------------------------------------------
