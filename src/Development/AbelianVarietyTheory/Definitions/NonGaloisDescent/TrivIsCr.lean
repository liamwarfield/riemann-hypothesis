module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
public import Formalism.SharpRestriction.LevelLetterCocycles.FourthHypothesisOfLifting

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l}

structure WSeed (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) where

  N : ℕ

  c₁ : ℕ

  c₂ : ℕ

  c₃ : ℕ

  F : Matrix (Fin d) (Fin d) (Wq l bk.a)

  F' : Matrix (Fin d) (Fin d) (Wq l bk.a)
  F_mul : F * F' = (l : Wq l bk.a) ^ c₃ • (1 : Matrix (Fin d) (Fin d) (Wq l bk.a))

  X : Matrix (Fin d) (Fin d) bk.S

  X' : Matrix (Fin d) (Fin d) bk.S
  X_mul : X * X' = ((l : bk.S) ^ c₂ * bk.E ^ (2 * N)) • (1 : Matrix (Fin d) (Fin d) bk.S)

  W : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)

  W' : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)
  W_mul : W * W' = bk.iA τ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀))
  φ : ∀ Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) WittVector.frobenius Φ →
    ((l : bk.DA bk.ρ₀) ^ c₁) • (W * X'.map bk.iS).map Φ =
      bk.iS (frobS l bk.a bk.E) ^ N • (W * X'.map bk.iS * F.map (bk.iS.comp C))

  κ : ↥(GK K) → Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)
  gal : ∀ (g : ↥(GK K)) (G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA (g : GQ l)) G →
    bk.iA (bk.ev bk.E * τ) ^ N • ((ρ g).map (bk.iA.comp (algebraMap ℤ_[l] (Ainf l))) * (W * X'.map bk.iS).map G) =
      bk.iA (Per.σA (g : GQ l) (bk.ev bk.E * τ)) ^ N • (W * X'.map bk.iS * κ g)
  fix : ∀ g : ↥(GK K), bk.FixFlat g → κ g = 1
  nopole : ∀ (g : ↥(GK K)) (G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA (g : GQ l)) G → ∀ i j,
    bk.iS bk.E ^ (2 * N) ∣ (X'.map bk.iS * κ g * (X.map bk.iS).map G) i j
  log : ∀ m : ℕ, ∃ (k : ℕ) (Λ : Matrix (Fin d) (Fin d) bk.S), (∀ i j, bk.E ∣ (Λ - (l : bk.S) ^ k • (1 : Matrix (Fin d) (Fin d) bk.S)) i j) ∧
    ∀ (g : ↥(GK K)) (G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA (g : GQ l)) G → ∀ i j,
      bk.iS bk.E ^ m ∣ (κ g * (Λ.map bk.iS).map G - Λ.map bk.iS) i j

structure Pre (bk : BK K) (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) where

  T : Matrix (Fin d) (Fin d) (WCb l)
  unit : IsUnit T

  A : Matrix (Fin d) (Fin d) bk.S

  A' : Matrix (Fin d) (Fin d) bk.S
  A_mul : A * A' = bk.E ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) bk.S)
  φ : bk.evW bk.E ^ N • T.map (frobW l) = T * A.map bk.evW
  fix : ∀ g : ↥(GK K), bk.FixFlat g → zW (ρ g) * T.map (galW l (g : GQ l)) = T

structure Frame (bk : BK K) (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) extends Pre bk N d ρ where

  ε : ↥(GK K) → Matrix (Fin d) (Fin d) (Ainf l)
  gal : ∀ g : ↥(GK K), zW (ρ g) * T.map (galW l (g : GQ l)) = T * (ε g).map (inclW l)

variable {bk : BK K} {N d : ℕ} {ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]}

def Frame.IsBeta (F : Frame bk N d ρ) (m k : ℕ) (β : Matrix (Fin d) (Fin d) bk.S) : Prop :=
  (∀ i j, bk.E ∣ (β - (l : bk.S) ^ k • (1 : Matrix (Fin d) (Fin d) bk.S)) i j) ∧ ∀ (g : ↥(GK K)) i j,
    bk.ev bk.E ^ m ∣ ((F.ε g).map WittVector.frobenius * (β.map bk.ev).map (Per.σA (g : GQ l)) - β.map bk.ev) i j

def Frame.IsDR (F : Frame bk N d ρ) : Prop := ∀ m : ℕ, ∃ k β, F.IsBeta m k β

def Frame.IsCr (F : Frame bk N d ρ) : Prop :=
  ∀ (g : ↥(GK K)) i j, bk.ev X ∣ (F.ε g - (1 : Matrix (Fin d) (Fin d) (Ainf l))) i j

def Link (bk : BK K) {d' : ℕ} (T : Matrix (Fin d) (Fin d) (WCb l)) (T' : Matrix (Fin d') (Fin d') (WCb l))
    (Pi : Matrix (Fin d) (Fin d') ℤ_[l]) (n r : ℕ) : Prop :=
  ∃ (R : Matrix (Fin d) (Fin d') bk.S) (G : Matrix (Fin d') (Fin d) bk.S),
    (∀ i j, (l : WCb l) ^ n ∣ (zW Pi * T' - T * R.map bk.evW) i j) ∧
    ∀ i j, (l : bk.S) ^ n ∣ (R * G - (l : bk.S) ^ r • (1 : Matrix (Fin d) (Fin d) bk.S)) i j

structure Onto {Γ : Type} {d d' : ℕ} (ρ : Γ → Matrix (Fin d) (Fin d) ℤ_[l]) (ρ' : Γ → Matrix (Fin d') (Fin d') ℤ_[l])
    (Pi : Matrix (Fin d) (Fin d') ℤ_[l]) (n : ℕ) : Prop where
  equi : ∀ g i j, (l : ℤ_[l]) ^ n ∣ (Pi * ρ' g - ρ g * Pi) i j
  surj : ∃ S : Matrix (Fin d') (Fin d) ℤ_[l], ∀ i j, (l : ℤ_[l]) ^ n ∣ (Pi * S - (1 : Matrix (Fin d) (Fin d) ℤ_[l])) i j

structure Tower {Γ : Type} [Group Γ] {d : ℕ} (ρ : Γ →* GL (Fin d) ℤ_[l]) where

  d' : ℕ → ℕ

  ρ' : ∀ n, Γ →* GL (Fin (d' n)) ℤ_[l]

  Pi : ∀ n, Matrix (Fin d) (Fin (d' n)) ℤ_[l]
  onto : ∀ n, Onto (fun g => (ρ g).val) (fun g => (ρ' n g).val) (Pi n) n

  f : ∀ n, Matrix (Fin (d' n)) (Fin (d' (n + 1))) ℤ_[l]
  f_equi : ∀ n g, f n * (ρ' (n + 1) g).val = (ρ' n g).val * f n
  f_Pi : ∀ n i j, (l : ℤ_[l]) ^ n ∣ (Pi n * f n - Pi (n + 1)) i j

def zOm (l : ℕ) [Fact l.Prime] : ℤ_[l] →+* Om l := (algebraMap ℚ_[l] (Om l)).comp (algebraMap ℤ_[l] ℚ_[l])

def qRep {Γ : Type} [Group Γ] {d : ℕ} (ρ : Γ →* GL (Fin d) ℤ_[l]) : Representation ℚ_[l] Γ (Fin d → ℚ_[l]) :=
  ((Matrix.toLinAlgEquiv' : Matrix (Fin d) (Fin d) ℚ_[l] ≃ₐ[ℚ_[l]] _) : _ →* _).comp
    (((algebraMap ℤ_[l] ℚ_[l]).mapMatrix : Matrix (Fin d) (Fin d) ℤ_[l] →+* _).toMonoidHom.comp ((Units.coeHom _).comp ρ))

structure Reads {Γ : Type} [Group Γ] {a d : ℕ} (ρ : Γ →* GL (Fin d) ℤ_[l]) (r : Γ →* GL (Fin a) (Om l))
    (b : Fin d → Matrix (Fin a) (Fin a) (Om l)) (e : Fin d → ℤ_[l]) : Prop where
  equi : ∀ g j, (r g).val * b j = ∑ i, zOm l ((ρ g).val i j) • b i
  one : ∑ i, zOm l (e i) • b i = 1

structure Layer {Γ : Type} [Group Γ] {a d' : ℕ} (L₀ : FinExt l) (Cl : Set (Γ →* GL (Fin a) (Om l))) (ρ' : Γ →* GL (Fin d') ℤ_[l]) where

  m : ℕ

  rep : Fin m → (Γ →* GL (Fin a) (Om l))
  mem : ∀ k, rep k ∈ Cl

  L : Fin m → FinExt l
  le : ∀ k, L₀.1 ≤ (L k).1
  rep_mem : ∀ k g i j, (rep k g).val i j ∈ (L k).1

  b : Fin d' → Fin m → Matrix (Fin a) (Fin a) (Om l)
  b_mem : ∀ s k i j, b s k i j ∈ (L k).1
  indep : LinearIndependent ℚ_[l] b
  span : ∀ x : Fin m → Matrix (Fin a) (Fin a) (Om l), (∀ k i j, x k i j ∈ (L k).1) → x ∈ Submodule.span ℚ_[l] (Set.range b)

  e : Fin d' → ℤ_[l]
  reads : ∀ k, Reads ρ' (rep k) (fun s => b s k) e

  c : Fin m → Om l

structure Cover {Γ : Type} [Group Γ] [TopologicalSpace Γ] {a : ℕ} (L₀ : FinExt l) (r : Γ →* GL (Fin a) (Om l))
    (Cl : Set (Γ →* GL (Fin a) (Om l))) where

  d : ℕ

  ρ : Γ →* GL (Fin d) ℤ_[l]
  cont : Continuous ρ

  b : Fin d → Matrix (Fin a) (Fin a) (Om l)

  e : Fin d → ℤ_[l]
  reads : Reads ρ r b e

  tw : Tower ρ
  cont' : ∀ n, Continuous (tw.ρ' n)

  lay : ∀ n, Layer L₀ Cl (tw.ρ' n)
  unit : ∀ n i, (l : ℤ_[l]) ^ n ∣ (tw.Pi n *ᵥ (lay n).e - e) i
  trace : ∀ n s, ‖(∑ i, zOm l (tw.Pi n i s) • b i).trace - ∑ k, (lay n).c k * ((lay n).b s k).trace‖ ≤ ((l : ℝ) ^ n)⁻¹

def IsHT (C : Core l) (ξ : Ainf l) {a : ℕ} (ρ : ↥(GK K) → Matrix (Fin a) (Fin a) (Om l)) (z : ℂ_[l])
    (u : Matrix (Fin a) (Fin a) ℂ_[l]) : Prop :=
  ∀ (K' : FinExt l) (p q : ℕ) (x : Fin a → Per.BdR l) (y : Fin a → Per.BdRp l),
    (∀ g : ↥(GK K), (g : GQ l) ∈ GK K' →
      (ρ g).map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp C.o) *ᵥ (fun i => Per.σD (g : GQ l) (x i)) = x) →
    (∀ i, algebraMap (Per.BdRp l) (Per.BdR l) (aDp l ξ) ^ q * x i = algebraMap (Per.BdRp l) (Per.BdR l) (aDp l ξ ^ p * y i)) →
    u *ᵥ (fun i => Per.θD l (y i)) = z ^ ((p : ℤ) - q) • fun i => Per.θD l (y i)

structure Hodge (C : Core l) (ξ : Ainf l) {a : ℕ} (ρ : ↥(GK K) → Matrix (Fin a) (Fin a) (Om l)) (K' : FinExt l) where

  V : Matrix (Fin a) (Fin a) (Per.BdRp l)
  unit : IsUnit V

  p : Fin a → ℕ

  q : ℕ

  Q : Matrix (Fin a) (Fin a) (Per.BdR l)
  Q_eq : ∀ i j, algebraMap (Per.BdRp l) (Per.BdR l) (aDp l ξ) ^ q * Q i j =
    algebraMap (Per.BdRp l) (Per.BdR l) (aDp l ξ ^ p j * V i j)
  inv : ∀ g : ↥(GK K), (g : GQ l) ∈ GK K' →
    (ρ g).map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp C.o) * Q.map (Per.σD (g : GQ l)) = Q

def IsZ (bk : BK K) (g : ↥(GK K)) (z : ℂ_[l]) : Prop :=
  ∃ w : Ainf l, Per.σA (g : GQ l) (bk.ev bk.E) = bk.ev bk.E * w ∧ z * Per.θD l (aDp l w) = 1

end GlobalTheory.BKLim

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal

namespace GlobalTheory.BSP

section Cover

variable {l : ℕ} {R : Type} [CommRing R]

abbrev adI (B : Obj l R) : Ideal B.A := Ideal.span {(l : B.A)} ⊔ B.I

theorem adI_pow_le {B B' : Obj l R} (f : Hom B B') (m : ℕ) : adI B ^ m ≤ (adI B' ^ m).comap f.f := by
  refine le_trans (Ideal.pow_right_mono ?_ m) (Ideal.le_comap_pow f.f m)
  refine sup_le ?_ fun a ha => Ideal.mem_sup_right (f.f_I a ha)
  rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]
  exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)

def qmap {B B' : Obj l R} (f : Hom B B') (m : ℕ) : (B.A ⧸ adI B ^ m) →+* (B'.A ⧸ adI B' ^ m) :=
  Ideal.quotientMap _ f.f (adI_pow_le f m)

theorem qmap_mk {B B' : Obj l R} (f : Hom B B') (m : ℕ) (a : B.A) :
    qmap f m (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (f.f a) := rfl

structure IsPO {B C B' C' : Obj l R} (h : Hom B C) (k : Hom B B') (k' : Hom C C') (h' : Hom B' C') : Prop where
  comm : k'.comp h = h'.comp k
  po : ∀ m : ℕ, CategoryTheory.IsPushout (CommRingCat.ofHom (qmap h m)) (CommRingCat.ofHom (qmap k m))
    (CommRingCat.ofHom (qmap k' m)) (CommRingCat.ofHom (qmap h' m))

structure Stable {B C : Obj l R} (h : Hom B C) : Prop where
  flat : ∀ m : ℕ, (qmap h m).Flat
  po : ∀ (B' : Obj l R) (k : Hom B B'), ∃ (C' : Obj l R) (k' : Hom C C') (h' : Hom B' C'), IsPO h k k' h'

structure Cover {B C : Obj l R} (h : Hom B C) : Prop where
  stable : Stable h
  ff : ∀ m : ℕ, (qmap h m).FaithfullyFlat

structure IsLoc {B C : Obj l R} (s : B.A) (h : Hom B C) : Prop where
  away : ∀ m : ℕ, letI := (qmap h m).toAlgebra
    IsLocalization.Away (Ideal.Quotient.mk (adI B ^ m) s) (C.A ⧸ adI C ^ m)
  univ : ∀ (Q : Obj l R) (a : Hom B Q), IsUnit (a.f s) → ∃ c : Hom C Q, c.comp h = a

end Cover

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} {bk : BK K} {d : ℕ}

structure Eval (S : Strat bk d) (B : Obj l ↥(OL K)) (N : Type) [AddCommGroup N] [Module B.A N] where
  fin : Module.Finite B.A N
  proj : Module.Projective B.A N

  v : ∀ {Q : Obj l ↥(OL K)} (a : Hom B Q), Hom bk.prism Q → N →ₛₗ[a.f] (Fin d → Q.A)
  bc : ∀ {Q} (a : Hom B Q) (g : Hom bk.prism Q), SemiBC (v a g)
  v_ε : ∀ {Q} (a : Hom B Q) (g g' : Hom bk.prism Q) (x : N), v a g x = (S.ε g g').mulVec (v a g' x)
  v_nat : ∀ {Q Q'} (c : Hom Q Q') (a : Hom B Q) (g : Hom bk.prism Q) (x : N) (i : Fin d),
    v (c.comp a) (c.comp g) x i = c.f (v a g x i)

def IsPsi {S : Strat bk d} {B : Obj l ↥(OL K)} {N : Type} [AddCommGroup N] [Module B.A N] (V : Eval S B N)
    (t : B.A) (Ψ : N →ₛₗ[B.D.φ] N) : Prop :=
  ∀ {Q : Obj l ↥(OL K)} (a : Hom B Q) (g : Hom bk.prism Q) (x : N),
    BK.hf g bk.E ^ S.a • V.v a g (Ψ x) =
      a.f t ^ S.a • (S.A.map (BK.hf g)).mulVec fun i => Q.D.φ (V.v a g x i)

def IsCoord {S : Strat bk d} {M : FCrys l ↥(OL K)} (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism))
    {B : Obj l ↥(OL K)} (V : Eval S B (M.M B)) : Prop :=
  ∀ {Q : Obj l ↥(OL K)} (a : Hom B Q) (g : Hom bk.prism Q) (x : M.M B),
    M.tr a x = ∑ i, V.v a g x i • M.tr g (e i)

end GlobalTheory.BSP
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Prism

namespace GlobalTheory.BSP

section W2

variable (l : ℕ) {A B : Type} [CommRing A] [CommRing B]

def cc (a b : A) : A := ∑ k ∈ Finset.Ioo 0 l, ((l.choose k / l : ℕ) : A) * a ^ k * b ^ (l - k)

theorem map_cc (f : A →+* B) (a b : A) : f (cc l a b) = cc l (f a) (f b) := by simp [cc]

theorem l_mul_cc [hl : Fact l.Prime] (a b : A) : (l : A) * cc l a b = (a + b) ^ l - a ^ l - b ^ l := by
  rw [add_pow_prime_eq hl.out, cc, Finset.mul_sum]
  have : ∀ k ∈ Finset.Ioo 0 l, (l : A) * (((l.choose k / l : ℕ) : A) * a ^ k * b ^ (l - k)) =
      (l : A) * a * b * (a ^ (k - 1) * b ^ (l - k - 1) * ((l.choose k / l : ℕ) : A)) := fun k hk => by
    obtain ⟨h1, h2⟩ := Finset.mem_Ioo.1 hk
    obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
    obtain ⟨j, hj⟩ : ∃ j, l - (i + 1) = j + 1 := ⟨l - (i + 1) - 1, by omega⟩
    rw [hj, Nat.add_sub_cancel, Nat.add_sub_cancel]; ring
  rw [Finset.sum_congr rfl this, ← Finset.mul_sum]; ring

@[ext] structure W2 (l : ℕ) (A : Type) where

  fst : A

  snd : A

namespace W2

variable {l}

instance : Zero (W2 l A) := ⟨⟨0, 0⟩⟩
instance : One (W2 l A) := ⟨⟨1, 0⟩⟩
instance : Add (W2 l A) := ⟨fun x y => ⟨x.fst + y.fst, x.snd + y.snd - cc l x.fst y.fst⟩⟩
instance : Neg (W2 l A) := ⟨fun x => ⟨-x.fst, -x.snd + cc l (-x.fst) x.fst⟩⟩
instance : Mul (W2 l A) :=
  ⟨fun x y => ⟨x.fst * y.fst, x.fst ^ l * y.snd + y.fst ^ l * x.snd + (l : A) * x.snd * y.snd⟩⟩

def mapF (f : A →+* B) (x : W2 l A) : W2 l B := ⟨f x.fst, f x.snd⟩

theorem mapF_add (f : A →+* B) (x y : W2 l A) : mapF f (x + y) = mapF f x + mapF f y :=
  W2.ext (map_add f _ _) (by
    change f (x.snd + y.snd - cc l x.fst y.fst) = f x.snd + f y.snd - cc l (f x.fst) (f y.fst)
    rw [map_sub, map_add (f := _), map_cc])

theorem mapF_mul (f : A →+* B) (x y : W2 l A) : mapF f (x * y) = mapF f x * mapF f y :=
  W2.ext (map_mul f _ _) (by
    change f (x.fst ^ l * y.snd + y.fst ^ l * x.snd + (l : A) * x.snd * y.snd) =
      f x.fst ^ l * f y.snd + f y.fst ^ l * f x.snd + (l : B) * f x.snd * f y.snd
    simp)

def gh (x : W2 l A) : A := x.fst ^ l + (l : A) * x.snd

variable [hl : Fact l.Prime]

theorem gh_add (x y : W2 l A) : gh (x + y) = gh x + gh y := by
  change (x.fst + y.fst) ^ l + (l : A) * (x.snd + y.snd - cc l x.fst y.fst) = _
  simp only [gh]; linear_combination -l_mul_cc l x.fst y.fst


omit hl in
theorem gh_mul (x y : W2 l A) : gh (x * y) = gh x * gh y := by
  change (x.fst * y.fst) ^ l + (l : A) * (x.fst ^ l * y.snd + y.fst ^ l * x.snd + (l : A) * x.snd * y.snd) = _
  simp only [gh]; ring

theorem ext_gh {σ : Type} {x y : W2 l (MvPolynomial σ ℤ)} (h0 : x.fst = y.fst) (h1 : gh x = gh y) : x = y := by
  refine W2.ext h0 (mul_left_cancel₀ (Nat.cast_ne_zero.2 hl.out.ne_zero : (l : MvPolynomial σ ℤ) ≠ 0) ?_)
  simp only [gh, h0] at h1
  exact add_left_cancel h1


omit hl in
theorem exists_lift (x : W2 l A) :
    ∃ y : W2 l (MvPolynomial A ℤ), mapF (MvPolynomial.eval₂Hom (Int.castRingHom A) id) y = x :=
  ⟨⟨MvPolynomial.X x.fst, MvPolynomial.X x.snd⟩, W2.ext (by simp [mapF]) (by simp [mapF])⟩

instance : CommRing (W2 l A) := CommRing.ofMinimalAxioms
  (fun x y z => by
    obtain ⟨x, rfl⟩ := exists_lift x; obtain ⟨y, rfl⟩ := exists_lift y; obtain ⟨z, rfl⟩ := exists_lift z
    simp only [← mapF_add]
    exact congrArg _ (ext_gh (add_assoc _ _ _) (by simp only [gh_add, add_assoc])))
  (fun x => W2.ext (zero_add _) (by
    change 0 + x.snd - cc l 0 x.fst = x.snd
    have : cc l 0 x.fst = 0 := Finset.sum_eq_zero fun k hk => by
      rw [zero_pow (Finset.mem_Ioo.1 hk).1.ne']; simp
    rw [this]; simp))
  (fun x => W2.ext (neg_add_cancel _) (by
    change -x.snd + cc l (-x.fst) x.fst + x.snd - cc l (-x.fst) x.fst = 0
    ring))
  (fun x y z => by
    obtain ⟨x, rfl⟩ := exists_lift x; obtain ⟨y, rfl⟩ := exists_lift y; obtain ⟨z, rfl⟩ := exists_lift z
    simp only [← mapF_mul]
    exact congrArg _ (ext_gh (mul_assoc _ _ _) (by simp only [gh_mul, mul_assoc])))
  (fun x y => W2.ext (mul_comm _ _) (by
    change x.fst ^ l * y.snd + y.fst ^ l * x.snd + (l : A) * x.snd * y.snd =
      y.fst ^ l * x.snd + x.fst ^ l * y.snd + (l : A) * y.snd * x.snd
    ring))
  (fun x => W2.ext (one_mul _) (by
    change (1 : A) ^ l * x.snd + x.fst ^ l * 0 + (l : A) * 0 * x.snd = x.snd
    ring))
  (fun x y z => by
    obtain ⟨x, rfl⟩ := exists_lift x; obtain ⟨y, rfl⟩ := exists_lift y; obtain ⟨z, rfl⟩ := exists_lift z
    simp only [← mapF_mul, ← mapF_add]
    exact congrArg _ (ext_gh (mul_add _ _ _) (by simp only [gh_mul, gh_add, mul_add])))

def map (f : A →+* B) : W2 l A →+* W2 l B where
  toFun := mapF f
  map_one' := W2.ext (map_one f) (map_zero f)
  map_zero' := W2.ext (map_zero f) (map_zero f)
  map_add' := mapF_add f
  map_mul' := mapF_mul f

def fstHom : W2 l A →+* A where
  toFun := fst
  map_one' := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

def ghHom : W2 l A →+* A where
  toFun := gh
  map_one' := by change (1 : A) ^ l + (l : A) * 0 = 1; simp
  map_zero' := by change (0 : A) ^ l + (l : A) * 0 = 0; simp [hl.out.ne_zero]
  map_add' := gh_add
  map_mul' := gh_mul

end W2

variable {l} [hl : Fact l.Prime]

def deltaSectionToWittLengthTwo (D : Delta l A) : A →+* W2 l A where
  toFun a := ⟨a, D.δ a⟩
  map_one' := W2.ext rfl D.δ_one
  map_zero' := W2.ext rfl D.δ_zero
  map_add' a b := W2.ext rfl (D.δ_add a b)
  map_mul' a b := W2.ext rfl (D.δ_mul a b)

def deltaStructureOfWittLengthTwoSection (s : A →+* W2 l A) (h : ∀ a, (s a).fst = a) : Delta l A where
  δ a := (s a).snd
  δ_one := by rw [map_one]; rfl
  δ_mul a b := by rw [map_mul]; exact (congrArg₂ (fun x y => x ^ l * (s b).snd + y ^ l * (s a).snd +
    (l : A) * (s a).snd * (s b).snd) (h a) (h b))
  δ_add a b := by rw [map_add (f := _)]; exact (congrArg₂ (fun x y => (s a).snd + (s b).snd - cc l x y) (h a) (h b))
  φ := W2.ghHom.comp s
  φ_eq a := congrArg (fun x => x ^ l + (l : A) * (s a).snd) (h a)

def IsδMap (D : Delta l A) (D' : Delta l B) (f : A →+* B) : Prop := ∀ a, f (D.δ a) = D'.δ (f a)

def δLocus (D : Delta l A) (D' : Delta l B) (f : A →+* B) : Subring A :=
  RingHom.eqLocus ((W2.map f).comp (deltaSectionToWittLengthTwo D)) ((deltaSectionToWittLengthTwo D').comp f)

theorem mem_δLocus {D : Delta l A} {D' : Delta l B} {f : A →+* B} {a : A} :
    a ∈ δLocus D D' f ↔ f (D.δ a) = D'.δ (f a) :=
  ⟨fun h => congrArg W2.snd h, fun h => W2.ext rfl h⟩

def polyDelta (D : Delta l A) : Delta l (MvPolynomial ℕ A) :=
  deltaStructureOfWittLengthTwoSection (MvPolynomial.eval₂Hom ((W2.map MvPolynomial.C).comp (deltaSectionToWittLengthTwo D))
                                      fun i => ⟨MvPolynomial.X i, MvPolynomial.X (i + 1)⟩)
    (RingHom.congr_fun (f := W2.fstHom.comp _) (g := RingHom.id _) (MvPolynomial.ringHom_ext
      (fun a => by rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_C]; rfl)
      (fun i => by rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_X']; rfl)))

theorem polyDelta_C (D : Delta l A) (a : A) :
    (polyDelta D).δ (MvPolynomial.C a) = MvPolynomial.C (D.δ a) :=
  congrArg W2.snd (MvPolynomial.eval₂Hom_C _ _ a)

theorem polyDelta_X (D : Delta l A) (i : ℕ) :
    (polyDelta D).δ (MvPolynomial.X i) = MvPolynomial.X (i + 1) :=
  congrArg W2.snd (MvPolynomial.eval₂Hom_X' _ _ i)

def envRel (D : Delta l A) (d p : A) (i : ℕ) : MvPolynomial ℕ A :=
  (polyDelta D).δ^[i + 1] (MvPolynomial.C p + MvPolynomial.C d * MvPolynomial.X 0)

end W2

structure IsCompl {L Q : Type} [CommRing L] [CommRing Q] (i : L →+* Q) (J : Ideal L) : Prop where
  complete : IsAdicComplete (J.map i) Q
  surj : ∀ (x : Q) (n : ℕ), ∃ a, x - i a ∈ (J ^ n).map i
  ker : ∀ (a : L) (n : ℕ), i a ∈ (J ^ n).map i → a ∈ J ^ n

variable {l : ℕ}

abbrev JJ {R : Type} [CommRing R] (B : Obj l R) : Ideal B.A := Ideal.span {(l : B.A)} ⊔ B.I

structure LocP {R : Type} [CommRing R] (B : Obj l R) (f d : B.A) where

  Q : Obj l R

  inl : Hom B Q
  unit : IsUnit (inl.f f)
  I_eq : Q.I = Ideal.span {inl.f d}
  univ : ∀ (C : Obj l R) (g : Hom B C), IsUnit (g.f f) → ∃! h : Hom Q C, h.comp inl = g
  surj : ∀ (x : Q.A) (n : ℕ), ∃ (k : ℕ) (b : B.A), inl.f f ^ k * x - inl.f b ∈ (JJ B ^ n).map inl.f
  ker : ∀ (b : B.A) (n : ℕ), inl.f b ∈ (JJ B ^ n).map inl.f → ∃ k : ℕ, f ^ k * b ∈ JJ B ^ n

def GenAway {R : Type} [CommRing R] (B : Obj l R) (f d : B.A) : Prop :=
  d ∈ B.I ∧ ∀ x ∈ B.I, ∃ k : ℕ, f ^ k * x ∈ Ideal.span {d}

structure EnvRing [Fact l.Prime] {A : Type} [CommRing A] (D : Delta l A) (J : Ideal A) (d p : A) where

  Q : Type
  [ring : CommRing Q]

  DQ : Delta l Q

  i : A →+* Q
  i_δ : IsδMap D DQ i

  w : Q
  rel : DQ.δ (i p + i d * w) = 0

  tb : TopBasis i J (Digits l)
  tb_b : ∀ α, tb.b α = α.1.prod fun k n => (DQ.δ^[k] w) ^ n
  lift : ∀ (C : Type) [CommRing C] (DC : Delta l C) (JC : Ideal C), IsAdicComplete JC C → ∀ f : A →+* C,
    IsδMap D DC f → J.map f ≤ JC → ∀ v : C, DC.δ (f p + f d * v) = 0 →
    ∃ h : Q →+* C, IsδMap DQ DC h ∧ h.comp i = f ∧ h w = v

attribute [instance] EnvRing.ring

end GlobalTheory.BSP
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoeffRingsHaveRootsOfUnity
noncomputable section

namespace GlobalTheory.PendOf

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open Polynomial Module TensorProduct Formalism.MainNotions.PairedCharacterCondition

structure TameOm (D : D7) where
  om : ∀ k : Fin 2, PlE D.host → Fb (D.host.g k) (D.host.g_prime k) → GE D.nd → ℂ
  om_one : ∀ k w x, x ≠ 0 → om k w x 1 = 1
  om_mul : ∀ k w x, x ≠ 0 → ∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w),
    ∀ σ' ∈ Ine (F := D.host.E) (D.nd.plOm.1 w), om k w x (σ * σ') = om k w x σ * om k w x σ'
  tameInertiaChar_mul_root : ∀ k w x y, x ≠ 0 → y ≠ 0 → ∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w),
    om k w (x * y) σ = om k w x σ * om k w y σ
  om_wild : ∀ k, ∀ w ∈ placesOver D.host.E (D.host.g k), ∀ x, x ≠ 0 →
    ∀ σ ∈ wildSet D.nd (D.nd.plOm.1 w), om k w x σ = 1
  om_open : ∀ k w x, x ≠ 0 → ∃ U : Subgroup (GE D.nd), IsOpen (U : Set (GE D.nd)) ∧
    ∀ σ ∈ U, σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w) → om k w x σ = 1
  om_inj : ∀ k, ∀ w ∈ placesOver D.host.E (D.host.g k), ∀ x y, x ≠ 0 → y ≠ 0 → x ≠ y →
    ∃ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w), om k w x σ ≠ om k w y σ
  om_tg : ∀ k (v : D.nd.PlG k) x, x ≠ 0 →
    om k (D.naut.plGw k v) x (D.ntypes.tg k v) = D.ntypes.teichC k x

def LabIne {D : D7} (Ω : TameOm D) : Prop :=
  ∀ k, ∀ w ∈ placesOver D.host.E (D.host.g k), ∀ L : D.naut.LP w,
    (D.naut.items₂ k w L).natDegree = D.naut.lpDim L →
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    ∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w), D.naut.inePol L σ =
      ((Formalism.CyclotomicNorms.rootsBar (D.naut.items₂ k w L)).map fun x => X - C (Ω.om k w x σ)).prod

def LabChar (D : D7) : Prop :=
  ∀ k, ∀ w ∈ placesOver D.host.E (D.host.g k), ∀ (L χ : D.naut.LP w)
    (u : (ZMod (D.host.g k))ˣ), (D.naut.items₂ k w L).natDegree = D.naut.lpDim L →
    D.naut.lpDim χ = 1 → D.naut.items₂ k w χ = X - C (u : ZMod (D.host.g k)) →
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    (D.naut.items₂ k w (D.naut.lpChar L χ)).natDegree = D.naut.lpDim L ∧
    Formalism.CyclotomicNorms.rootsBar (D.naut.items₂ k w (D.naut.lpChar L χ)) =
      (Formalism.CyclotomicNorms.rootsBar (D.naut.items₂ k w L)).map
        (· * algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) (u : ZMod (D.host.g k)))

def IneRep (D : D7) : Prop :=
  ∀ k : Fin 2, ∀ w ∈ placesOver D.host.E (D.host.g k), ∀ L : D.naut.LP w,
    ∃ ρ : ↥(Ine (F := D.host.E) (D.nd.plOm.1 w)) →* GL (Fin (D.naut.lpDim L)) ℂ,
      (∃ U : Subgroup (GE D.nd), IsOpen (U : Set (GE D.nd)) ∧
        ∀ σ : ↥(Ine (F := D.host.E) (D.nd.plOm.1 w)), (σ : GE D.nd) ∈ U → ρ σ = 1) ∧
      ∀ σ : ↥(Ine (F := D.host.E) (D.nd.plOm.1 w)), D.naut.inePol L (σ : GE D.nd) =
        ((ρ σ : GL (Fin (D.naut.lpDim L)) ℂ) : Matrix (Fin (D.naut.lpDim L)) (Fin (D.naut.lpDim L)) ℂ).charpoly

def TameLP (D : D7) {w : PlE D.host} (L : D.naut.LP w) : Prop :=
  ∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w), σ ∈ wildSet D.nd (D.nd.plOm.1 w) →
    D.naut.inePol L σ = (X - 1) ^ D.naut.lpDim L

def LabDepth (D : D7) : Prop :=
  ∀ k : Fin 2, ∀ w ∈ placesOver D.host.E (D.host.g k), ∀ L : D.naut.LP w,
    (D.naut.items₂ k w L).Monic ∧ ((D.naut.items₂ k w L).natDegree = D.naut.lpDim L ↔ TameLP D L)

def GenFam (D : D7) (γ : Fin 2 → PlE D.host → GE D.nd) : Prop :=
  (∀ k v, γ k (D.naut.plGw k v) = D.ntypes.tg k v) ∧
    ∀ k : Fin 2, ∀ w ∈ placesOver D.host.E (D.host.g k), TameGenAt (D.nd.plOm.1 w) (γ k w)

def LabGen (D : D7) : Prop :=
  ∃ γ : Fin 2 → PlE D.host → GE D.nd, GenFam D γ ∧
    ∀ k : Fin 2, ∀ w ∈ placesOver D.host.E (D.host.g k), ∀ L : D.naut.LP w,
      (D.naut.items₂ k w L).natDegree = D.naut.lpDim L →
      haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      D.naut.inePol L (γ k w) =
        ((Formalism.CyclotomicNorms.rootsBar (D.naut.items₂ k w L)).map fun x => X - C (D.ntypes.teichC k x)).prod

def DepthZ (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (PI : D.naut.AV i) (k : Fin 2), ∀ w ∈ placesOver D.host.E (D.host.g k),
    TameLP D (D.naut.locV i PI w)

structure CenO (D : D7) where
  zO : ∀ i : D.nd.Loc,
    ↥(Subalgebra.center (D.nd.O i) (MonoidAlgebra (D.nd.O i) (G0g D.nd))) →ₐ[D.nd.O i]
      Module.End (D.nd.O i) (D.nd.Mt i)
  zO_comm : ∀ i z (f : D.nd.T i), zO i z * D.nd.act i f = D.nd.act i f * zO i z
  zO_act : ∀ i (z : ↥(Subalgebra.center (D.nd.O i) (MonoidAlgebra (D.nd.O i) (G0g D.nd))))
    (x y : D.what₂.MtL (D.nd.mu i) (D.nd.j i)),
    D.what₂.jMt _ _ y = D.ntypes.onMt (D.nd.mu i) (D.nd.j i)
      (mapCoef (iotaO D.nd D.naut i) (z : MonoidAlgebra (D.nd.O i) (G0g D.nd))) (D.what₂.jMt _ _ x) →
    D.nd.prMt i y = (zO i z).baseChange (KK D.nd i) (D.nd.prMt i x)

def ZLStable (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (z : MonoidAlgebra D.what₂.LL (G0g D.nd)), (∀ a, z * a = a * z) →
    ∀ x : D.what₂.MtL (D.nd.mu i) (D.nd.j i), ∃ y : D.what₂.MtL (D.nd.mu i) (D.nd.j i),
      D.what₂.jMt _ _ y =
        D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (mapCoef D.what₂.embLL z) (D.what₂.jMt _ _ x)

def CenInt (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (z : MonoidAlgebra ℤ (G0g D.nd)), (∀ a, z * a = a * z) →
    ∀ x ∈ GlobalTheory.EtaJoin.genSet D (D.nd.mu i) (D.nd.j i), ∃ y ∈ GlobalTheory.EtaJoin.lat D (D.nd.mu i) (D.nd.j i),
      D.what₂.jMt _ _ y =
        D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (mapCoef (Int.castRingHom ℂ) z) (D.what₂.jMt _ _ x)

def OnMtPreservesTypeV (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (PI : D.naut.AV i) (z : MonoidAlgebra ℂ (G0g D.nd)), ∀ F ∈ D.naut.typeV i PI,
    D.ntypes.onMt (D.nd.mu i) (D.nd.j i) z F ∈ D.naut.typeV i PI

def typeSum (D : D7) (i : D.nd.Loc) (o : Option (D.nd.X i)) : Submodule ℂ (D.what₂.Mt (D.nd.mu i) (D.nd.j i)) :=
  ⨆ P ∈ {P | D.naut.ptV i P = o}, D.naut.typeV i P

structure Sec (D : D7) (i : D.nd.Loc) where

  Φ : TensorProduct (D.nd.O i) (KK D.nd i) (D.nd.Mt i) →+ D.what₂.Mt (D.nd.mu i) (D.nd.j i)
  inj : Function.Injective Φ
  semi : ∀ (k : KK D.nd i) v, Φ (k • v) = (D.naut.iotaQC i (D.naut.iotaQ i k)) • Φ v
  eig : ∀ x, ∀ u ∈ heckeEig (D.nd.T i) (D.nd.act i) x, Φ u ∈ typeSum D i (some x)
  split : ∀ y : D.what₂.MtL (D.nd.mu i) (D.nd.j i), D.what₂.jMt _ _ y - Φ (D.nd.prMt i y) ∈ typeSum D i none

def PrType (D : D7) : Prop :=
  ∀ i (PI : D.naut.AV i) (x : D.what₂.MtL (D.nd.mu i) (D.nd.j i)),
    D.what₂.jMt _ _ x ∈ D.naut.typeV i PI →
    (∀ p, D.naut.ptV i PI = some p → D.nd.prMt i x ∈ heckeEig (D.nd.T i) (D.nd.act i) p) ∧
    (D.naut.ptV i PI = none → D.nd.prMt i x = 0)

def ParSurj (D : D7) : Prop :=
  ∀ i x Sig, HasParamX D.nd D.naut i x Sig →
    ∃ σ' : D.ntypes.Par, ∀ w, D.ntypes.locPar σ' w = isoLoc D.nd D.naut Sig w

def SerLL (D : D7) : Prop :=
  ∀ (k : Fin 2) (f : (ZMod (D.host.g k))[X]) (h : GL (Fin D.R.r) (ZMod (D.host.g k))),
    ∃ y : D.what₂.LL, D.what₂.embLL y = (D.ntypes.eSer k f).coeff h

def CoeffRingsHaveRootsOfUnity (D : D7) : Prop := ∀ i : D.nd.Loc, ∃ ζ : D.nd.O i, IsPrimitiveRoot ζ D.what₂.restRowsFiniteGroupCard


open Classical in
def SerEq (D : D7) (lz : ∀ k : Fin 2, LzData (D.host.g k)) : Prop :=
  ∀ (k : Fin 2) (f : (ZMod (D.host.g k))[X]),
    D.ntypes.eSer k f = ∑ τ : (lz k).Irr D.R.r, if (lz k).lab τ = f then (lz k).idem τ else 0

def mk {D : D7} (lz : ∀ k : Fin 2, LzData (D.host.g k)) (h1 : SerEq D lz) (h2 : SerLL D) (h3 : CoeffRingsHaveRootsOfUnity D)
    (Ω : TameOm D) (h4 : LabIne Ω) (h5 : LabChar D) (Z : CenO D) (h6 : ZLStable D) (h7 : PrType D)
    (h8 : ParSurj D) : Pend D where
  lz := lz
  eSer_eq := h1
  eSer_LL := h2
  zetaPrimitiveRoot := h3
  om := Ω.om
  om_one := Ω.om_one
  om_mul := Ω.om_mul
  tameInertiaChar_mul_root := Ω.tameInertiaChar_mul_root
  om_wild := Ω.om_wild
  om_open := Ω.om_open
  om_inj := Ω.om_inj
  om_tg := Ω.om_tg
  inertiaCharpoly_eigenvalues := h4
  inertiaCharpoly_character := h5
  zO := Z.zO
  zO_comm := Z.zO_comm
  zL_stable := h6
  zO_act := Z.zO_act
  prMt_type := h7
  Par_surj := h8
  kty i PI k v := {τ | ∃ F ∈ D.naut.typeV i PI, D.ntypes.onMt (D.nd.mu i) (D.nd.j i)
      (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v ((lz k).idem τ)) F ≠ 0}
  kty_spec _ _ _ _ _ := Iff.rfl

end GlobalTheory.PendOf

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Small2
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.ResSel

namespace GlobalTheory.StepTwo

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (bkP : BKPh X)
  (i : X.Tw) (s : X.Sig i)

def idl : Ideal (X.O0 i) := Ideal.span {(X.l i : X.O0 i) ^ nu X i} * IsLocalRing.maximalIdeal (X.O0 i)

def Small2 (M : ℕ) (L : Subgroup (GE N)) (z : GE N) : Prop :=
  Small i s L z ∧ (∀ g ∈ L, ∀ ζ : N.Om, ζ ^ (2 * X.l i ^ M) = 1 → g ζ = ζ) ∧ ∀ g ∈ L, ∀ a b, (Tmat i s g - 1) a b ∈ idl i

variable (M : ℕ) {R n : ℕ} (d : PlE D.host → (GE N →* Multiplicative (ZMod (X.l i ^ M))))

def PiLocalization₂ (A : Finset (PlE D.host)) (L : Subgroup (GE N)) (z : GE N) (P : Fin R ⊕ Fin n → PlE D.host) : Prop :=
  SlopeTestRemainingChoices X i M A P (fun q => d (P q)) ∧
    (∀ a, (∀ v, Over (P (.inl a)) v → ∀ B : ValuationSubring N.Om, IsPlaceOver B v → Ine (F := D.host.E) B ≤ L) ∧
      ∀ σ : GE N, IsFrob (N.plOm.1 (P (.inl a))) (normV (P (.inl a))) σ → ∃ g : GE N, g * σ * g⁻¹ * z⁻¹ ∈ L) ∧
    ∀ a, DecV N (P (.inr a)) ≤ L ∧ ∀ (b : Fin R) (σ : GE N), IsFrob (N.plOm.1 (P (.inr a))) (normV (P (.inr a))) σ →
      d (P (.inl b)) σ = Multiplicative.ofAdd (if a.val = b.val then 1 else 0)

def NF (P : Fin R ⊕ Fin n → PlE D.host) (c : ℕ) : Prop :=
  ∀ Q, IsQ P Q → ∀ (a : ℕ) (Φ : Matrix (Fin a) (Fin a) (abelian₂ X i M (Fin R ⊕ Fin n))),
    Computes bkP i s M (fun q => d (P q)) Q Φ → ∀ F, toLam X i M (Fin R ⊕ Fin n) F = Φ.det →
      ∃ m : Fin R ⊕ Fin n →₀ ℕ, m.degree < c ∧ F.coeff m ∉ idl i

def NFit (P : Fin R ⊕ Fin n → PlE D.host) (c : ℕ) : Prop :=
  ∀ Q, IsQ P Q → ∀ (a : ℕ) (Φ : Matrix (Fin a) (Fin a) (abelian₂ X i M (Fin R ⊕ Fin n))),
    Computes bkP i s M (fun q => d (P q)) Q Φ → a = 0 ∨ ∃ b b', ∀ F, toLam X i M (Fin R ⊕ Fin n) F = Φ.adjugate b b' →
      ∃ m : Fin R ⊕ Fin n →₀ ℕ, m.degree < c ∧ (∀ j : Fin R, n ≤ j.val → m (.inl j) = 0) ∧ IsUnit (F.coeff m)

def Ext (P : Fin R ⊕ Fin n → PlE D.host) (P' : Fin R ⊕ Fin (n + 1) → PlE D.host) : Prop :=
  ∀ q, P' (Sum.map id Fin.castSucc q) = P q

def Start : Prop :=
  ∀ (M R n : ℕ) d A L z (P : Fin R ⊕ Fin n → PlE D.host) (φ φ' : Fin n → GE N), n ≤ R → 4 * D.R.r * n + 2 < X.l i ^ M →
    IsTameInertiaElementAtTwistPrime X i z → Small i s L z → PiLocalization₂ i M d A L z P →
    (∀ a, IsFrob (N.plOm.1 (P (.inr a))) (normV (P (.inr a))) (φ a) ∧ IsCj X (φ a) (φ' a)) → Corank bkP i s φ φ' 1 →
    NFit bkP i s M d P (4 * D.R.r * n + 1)

def Grow : Prop :=
  0 < nu X i → ∀ (M R n : ℕ) d A L z (P : Fin R ⊕ Fin n → PlE D.host) (P' : Fin R ⊕ Fin (n + 1) → PlE D.host) (c : ℕ), n < R →
    c + 2 * D.R.r ≤ X.l i ^ (M - nu X i - 1) → nu X i + 2 ≤ M → IsTameInertiaElementAtTwistPrime X i z → Small2 i s M L z → PiLocalization₂ i M d A L z P' → Ext P P' →
    (NF bkP i s M d P c → NF bkP i s M d P' (c + 2 * D.R.r)) ∧ (NFit bkP i s M d P c → NFit bkP i s M d P' (c + 2 * D.R.r))

def Step : Prop :=
  0 < nu X i → ∀ (M R n : ℕ) H S d A L z (P : Fin R ⊕ Fin n → PlE D.host) (w e : ℕ), n < R →
    IsDiscreteValuationRing.addVal (X.O0 i) ((X.l i : X.O0 i) ^ nu X i) = e →
    2 * (e + 1) * w + 2 + 2 * D.R.r ≤ X.l i ^ (M - nu X i - 1) → nu X i + 2 ≤ M →
    AdmFam X i M H S d → L ≤ H → IsTameInertiaElementAtTwistPrime X i z → Small2 i s M L z → PiLocalization₂ i M d A L z P → NFit bkP i s M d P (w + 1) →
    ∃ P' : Fin R ⊕ Fin (n + 1) → PlE D.host, Ext P P' ∧ PiLocalization₂ i M d A L z P' ∧
      NF bkP i s M d P' (2 * (e + 1) * w + 2 + 2 * D.R.r)

end GlobalTheory.StepTwo
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Imports
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc PowerSeries GlobalTheory.Prism GlobalTheory.BKReal
open scoped NNReal

namespace GlobalTheory.BSP.Height

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} {bk : BK K} {d : ℕ}
  {ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]} {τ : Ainf l} {s : Seed bk d ρ τ} (ht : Height s)

def bas : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀) := s.X.map (toDisc l (X : bk.S) bk.ρ₀) * ht.Z

def Rel {B : Obj l ↥(OL K)} (u : B.A) (f g : Hom bk.prism B)
    (ε : Matrix (Fin d) (Fin d) (Disc l u bk.ρ₀)) : Prop :=
  ∀ Ff Fg : bk.DS bk.ρ₀ →+* Disc l u bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) (BK.hf f) Ff → IsDiscMap (l := _) (u := _) (ρ := _) (BK.hf g) Fg →
    toDisc l u bk.ρ₀ (BK.hf g bk.E) ^ s.N • (ht.bas.map Ff * ε) =
      toDisc l u bk.ρ₀ (BK.hf f bk.E) ^ s.N • ht.bas.map Fg

theorem rel_one {B : Obj l ↥(OL K)} (u : B.A) (f : Hom bk.prism B) : ht.Rel u f f 1 := fun Ff Fg hf hg => by
  rw [hf.unique hg, mul_one]

end GlobalTheory.BSP.Height
end
end
