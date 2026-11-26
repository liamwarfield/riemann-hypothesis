module

public import Formalism.LocalToGlobal.HermitianForms.PsiZeroNontrivialCharacter
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentHeisenbergDecomposition

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SelfDualAt
noncomputable section

open Formalism.BasicNotions Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

namespace GlobalTheory.St.G

abbrev Ad (F : Type) [Field F] [NumberField F] : Type := FiniteAdeleRing (𝓞 F) F

abbrev OAd (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] : Subring (E ⊗[F] Ad F) :=
  tensInt (F := F) (Ad F) (intOE E) (intAd F)

def SplitsIn (E : Type) [Field E] [NumberField E] (p : ℕ) : Prop :=
  (placesOver E p).ncard = Module.finrank ℚ E

section Lat

variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

abbrev hat (L : Submodule (𝓞 E) (Fin n → E)) : Submodule (OAd F E) (Fin n → E ⊗[F] Ad F) :=
  latS (F := F) (Ad F) (OAd F E) L

variable {F}

abbrev loc (v : HeightOneSpectrum (𝓞 F)) (L : Submodule (𝓞 E) (Fin n → E)) :
    Submodule (intV E v) (Fin n → E ⊗[F] v.adicCompletion F) :=
  latS (F := F) (v.adicCompletion F) (intV E v) L

def IsLat (L : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  Module.Finite (𝓞 E) L ∧ Submodule.span E (L : Set (Fin n → E)) = ⊤

def prVec (v : HeightOneSpectrum (𝓞 F)) (x : Fin n → E ⊗[F] Ad F) : Fin n → E ⊗[F] v.adicCompletion F :=
  fun i => prV (E := E) v (x i)

variable (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E)

abbrev dualL (L : Submodule (𝓞 E) (Fin n → E)) : Submodule (𝓞 E) (Fin n → E) :=
  Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J L)

def hR (R : Type) [CommRing R] [Algebra F R] (x y : Fin n → E ⊗[F] R) : E ⊗[F] R :=
  hform (sigR σ R) (J.map (inclE (F := F) R)) x y

def TLat (T f : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  IsLat L ∧ (∀ x ∈ L, x ∈ dualSet (σ : E →+* E) J L) ∧ (∀ y ∈ dualSet (σ : E →+* E) J L, (T : E) • y ∈ L) ∧
  L.toAddSubgroup.relIndex (dualL σ J L).toAddSubgroup = T ^ (2 * f) ∧
  ∀ v : HeightOneSpectrum (𝓞 F), (T : 𝓞 F) ∈ v.asIdeal → ∃ x ∈ loc v (dualL σ J L), x ∉ loc v L

def SelfDualAt (v : HeightOneSpectrum (𝓞 F)) (L : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  ∀ y, y ∈ loc v L ↔ ∀ z ∈ loc v L, hR σ J (v.adicCompletion F) z y ∈ intV E v

end Lat

def InModL {A : Type} [CommRing A] {O : Subring A} {n : ℕ} (Λ : Submodule O (Fin n → A)) (m : ℕ)
    (S : Set (Fin n → A)) (x : Fin n → A) : Prop :=
  ∃ s ∈ Submodule.span O S, ∃ z ∈ Λ, x = s + (m : A) • z

def supSum {A : Type} [CommRing A] {n k : ℕ} (h : (Fin n → A) → (Fin n → A) → A) (b bd : Fin k → Fin n → A)
    (y : Matrix (Fin n) (Fin n) A) : A :=
  ∑ i : Fin k, if hi : i.1 + 1 < k then h (bd i) (y *ᵥ b ⟨i.1 + 1, hi⟩) else 0

section Frame

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
  (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E)

structure AdFrame (Λ : Submodule (OAd F E) (Fin n → E ⊗[F] Ad F)) (g k : ℕ) where
  eps : E ⊗[F] Ad F
  eps_idem : eps * eps = eps
  eps_orth : eps * sigR σ (Ad F) eps = 0
  eps_int : eps ∈ OAd F E
  eps_full : ∀ y ∈ Λ, ∃ z ∈ Λ, (1 - eps - sigR σ (Ad F) eps) • y = (g : E ⊗[F] Ad F) • z
  b : Fin k → Fin n → E ⊗[F] Ad F
  bd : Fin k → Fin n → E ⊗[F] Ad F
  b_mem : ∀ i, b i ∈ Λ
  bd_mem : ∀ i, bd i ∈ Λ
  b_eps : ∀ i, b i = eps • b i
  bd_eps : ∀ i, bd i = sigR σ (Ad F) eps • bd i
  dual : ∀ i j, ∃ t ∈ OAd F E, hR σ J (Ad F) (bd i) (b j) - (if i = j then eps else 0) = (g : E ⊗[F] Ad F) * t
  span : ∀ y ∈ Λ, InModL Λ g (Set.range b ∪ Set.range bd) y
  psi : E ⊗[F] Ad F → ℂ
  psi_add : ∀ x y, psi (x + y) = psi x * psi y
  psi_int : ∀ x ∈ OAd F E, psi x = 1
  psi_rat : ∀ x : E, psi (inclE (F := F) (Ad F) x) *
    Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ E x : ℚ) : ℂ)) = 1

variable {σ J} {Λ : Submodule (OAd F E) (Fin n → E ⊗[F] Ad F)} {g k : ℕ}

def AdFrame.InK (Fr : AdFrame σ J Λ g k) (y : GL (Fin n) (E ⊗[F] Ad F)) : Prop :=
  y ∈ stabGL Λ ∧
  (∀ x, (∀ z ∈ Λ, hR σ J (Ad F) z x ∈ OAd F E) → (y.1 - 1) *ᵥ x ∈ Λ) ∧
  ∀ i : Fin k, InModL Λ g (Fr.b '' {j | j.1 < i.1}) ((y.1 - 1) *ᵥ Fr.b i)

def AdFrame.chi (Fr : AdFrame σ J Λ g k) (y : GL (Fin n) (E ⊗[F] Ad F)) : ℂ :=
  Fr.psi (algebraMap F (E ⊗[F] Ad F) ((g : F)⁻¹) * supSum (hR σ J (Ad F)) Fr.b Fr.bd y.1)

def AdFrame.LocK (Fr : AdFrame σ J Λ g k) (L : Submodule (𝓞 E) (Fin n → E)) (v : HeightOneSpectrum (𝓞 F))
    (y : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Prop :=
  ∀ i : Fin k, InModL (loc v L) g ((fun j => prVec v (Fr.b j)) '' {j | j.1 < i.1}) ((y.1 - 1) *ᵥ prVec v (Fr.b i))

def AdFrame.locChi (Fr : AdFrame σ J Λ g k) (v : HeightOneSpectrum (𝓞 F))
    (y : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : ℂ :=
  Fr.psi (Formalism.UG.P.afsplitIE v (algebraMap F (E ⊗[F] v.adicCompletion F) ((g : F)⁻¹) *
    supSum (hR σ J (v.adicCompletion F)) (fun j => prVec v (Fr.b j)) (fun j => prVec v (Fr.bd j)) y.1))

end Frame

end GlobalTheory.St.G

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMirClass
noncomputable section

namespace GlobalTheory.GLm

open Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq
open scoped Classical

variable {g : ℕ} [Fact g.Prime]

def InMir {n : ℕ} (M : Mt g n) : Prop := ∀ i j : Fin n, (i : ℕ) + 1 = n → M i j = (1 : Mt g n) i j

def IsMirClass {n : ℕ} (F : Gn g n → ℂ) : Prop :=
  ∀ p x : Gn g n, InMir (p : Mt g n) → InMir (x : Mt g n) → F (p * x * p⁻¹) = F x

def InR (i : ℕ) {n : ℕ} (M : Mt g n) : Prop := InPar i M ∧ IsUniUp (br i (n - i) M)

def supFrom (i : ℕ) {n : ℕ} (M : Mt g n) : ZMod g := ∑ j ∈ Finset.Ico i (n - 1), entN M j (j + 1)

def diag1 {k : ℕ} (h : Gn g k) (n : ℕ) : Gn g n :=
  toG fun i j : Fin n => if (i : ℕ) < k ∧ (j : ℕ) < k then entN (h : Mt g k) i j else (1 : Mt g n) i j

def tail (ψ₀ : AddChar (ZMod g) ℂ) (m : ℕ) {n : ℕ} (F : Gn g n → ℂ) : Gn g m → ℂ := fun p =>
  ((g : ℂ) ^ (m * (n - m) + (n - m) * (n - m - 1) / 2))⁻¹ * ∑ x : Gn g n,
    if InR m (x : Mt g n) ∧ tl m (x : Mt g n) = (p : Mt g m) then
      F x * (ψ₀ (supFrom (m - 1) (x : Mt g n)))⁻¹ else 0

def indR (ψ₀ : AddChar (ZMod g) ℂ) (i n : ℕ) (ρ : Gn g i → ℂ) : Gn g n → ℂ := fun x =>
  ((Finset.univ.filter fun p : Gn g n => InR i (p : Mt g n)).card : ℂ)⁻¹ *
    ∑ y : Gn g n, if InMir (y : Mt g n) ∧ InR i ((y⁻¹ * x * y : Gn g n) : Mt g n) then
      ρ (toG (tl i ((y⁻¹ * x * y : Gn g n) : Mt g n))) * ψ₀ (supFrom i ((y⁻¹ * x * y : Gn g n) : Mt g n)) else 0

def indV (ψ₀ : AddChar (ZMod g) ℂ) (m : ℕ) (f : Gn g m → ℂ) : Gn g (m + 1) → ℂ := fun x =>
  ((Finset.univ.filter fun p : Gn g (m + 1) =>
      InMir (p : Mt g (m + 1)) ∧ InMir (tl m (p : Mt g (m + 1)))).card : ℂ)⁻¹ *
    ∑ y : Gn g (m + 1), if InMir (y : Mt g (m + 1)) ∧ InMir ((y⁻¹ * x * y : Gn g (m + 1)) : Mt g (m + 1)) ∧
        InMir (tl m ((y⁻¹ * x * y : Gn g (m + 1)) : Mt g (m + 1))) then
      f (toG (tl m ((y⁻¹ * x * y : Gn g (m + 1)) : Mt g (m + 1)))) *
        ψ₀ (entN ((y⁻¹ * x * y : Gn g (m + 1)) : Mt g (m + 1)) (m - 1) m) else 0

def InPat {N : ℕ} (Φ : Fin N → Fin N → Prop) (M : Mt g N) : Prop := ∀ a b, ¬ Φ a b → M a b = (1 : Mt g N) a b

def sumAt {N : ℕ} (E : Fin N → Fin N → Prop) (M : Mt g N) : ZMod g := ∑ a, ∑ b, if E a b then M a b else 0

def ePat (g N : ℕ) [Fact g.Prime] (Φ E : Fin N → Fin N → Prop) (ψ₀ : AddChar (ZMod g) ℂ) :
    MonoidAlgebra ℂ (Gn g N) :=
  eDat g N (InPat Φ) (sumAt E) ψ₀

def IsW (k s a : ℕ) : Prop := s ≤ a ∧ a < s + k

def phI (k s i : ℕ) {N : ℕ} (a b : Fin N) : Prop :=
  (IsW k s a ∧ IsW k s b ∧ a < b) ∨ (¬ IsW k s a ∧ ¬ IsW k s b ∧ a < b) ∨ ((a : ℕ) < i ∧ IsW k s b) ∨
    (IsW k s a ∧ ((i < (b : ℕ) ∧ (b : ℕ) < s) ∨ ((b : ℕ) = s + k ∧ i < s) ∨ s + k < (b : ℕ)))

def eeI (k s : ℕ) {N : ℕ} (a b : Fin N) : Prop :=
  ((b : ℕ) = a + 1 ∧ (b : ℕ) < s) ∨ ((a : ℕ) + 1 = s ∧ (b : ℕ) = s + k) ∨ ((b : ℕ) = a + 1 ∧ s + k ≤ (a : ℕ)) ∨
    ((b : ℕ) = a + 1 ∧ IsW k s a ∧ IsW k s b)

def pm (g : ℕ) [Fact g.Prime] {n : ℕ} (σ : Equiv.Perm (Fin n)) : Gn g n :=
  toG fun r j : Fin n => if r = σ j then 1 else 0

def sigI (a c i j : ℕ) : ℕ := if j < i then j else if j < a then c + (j - i) else if j < a + (c - i) then i + (j - a) else j

def wI (g : ℕ) [Fact g.Prime] (a c i n : ℕ) : Gn g n :=
  toG fun r j : Fin n => if (r : ℕ) = sigI a c i j then 1 else 0

def mean {G : Type} [Fintype G] (f : G → ℂ) : ℂ := (Fintype.card G : ℂ)⁻¹ * ∑ x, f x

theorem inMir_one (n : ℕ) : InMir (1 : Mt g n) := fun _ _ _ => rfl

end GlobalTheory.GLm
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsFolnerUWset
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

variable {k r : ℕ}

theorem isUnit_det_Hpk : IsUnit (Hpk k r).det :=
  Matrix.isUnit_det_of_right_inverse (hpkFacts k r).2.1

theorem isUnit_det_of_mem_GG {g : Mat k r} (hg : g ∈ GG k r) : IsUnit g.det :=
  ((uHGroup _ _ isUnit_det_Hpk).2.2 g hg).1

theorem norm_det_of_mem_GG {g : Mat k r} (hg : g ∈ GG k r) : ‖g.det‖ = 1 := by
  have h1 : gᴴ * Hpk k r * g = Hpk k r := hg
  have h2 := congrArg Matrix.det h1
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose] at h2
  have h3 : star g.det * g.det = 1 := by
    have h4 : (star g.det * g.det) * (Hpk k r).det = 1 * (Hpk k r).det := by
      rw [one_mul]; linear_combination h2
    exact (isUnit_det_Hpk (k := k) (r := r)).mul_right_cancel h4
  have h5 : Complex.normSq g.det = 1 := by
    have h6 := Complex.normSq_eq_conj_mul_self (z := g.det)
    rw [starRingEnd_apply, h3] at h6
    exact_mod_cast h6
  have h7 : ‖g.det‖ ^ 2 = 1 := by rw [Complex.sq_norm, h5]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h7

theorem IsClosedSub.isClosedSubgroup {S : Set (Mat k r)} (hS : IsClosedSub k r S) :
    Formalism.FourierDecayAlt.B2.IsClosedSubgroup S := by
  obtain ⟨hG, hc, h1, hm, hi⟩ := hS
  exact ⟨h1, hm, hi, fun a ha => isUnit_det_of_mem_GG (hG ha), hc⟩

theorem isClosedSub_of {S : Set (Mat k r)} (hS : Formalism.FourierDecayAlt.B2.IsClosedSubgroup S) (h : S ⊆ GG k r) :
    IsClosedSub k r S := by
  unfold IsClosedSub
  exact ⟨h, hS.closed, hS.one_mem, hS.mul_mem, hS.inv_mem⟩

theorem isClosedSub_GG : IsClosedSub k r (GG k r) :=
  isClosedSub_of (Formalism.FourierDecayAlt.P.unitary_group_closed k r) subset_rfl

theorem isClosedSub_Nset : IsClosedSub k r (Nset k r) :=
  isClosedSub_of (Formalism.FourierDecayAlt.P.unipotent_radical_closed k r) fun _ hg => hg.1

theorem isClosedSub_UWset (z : Fin (2 * r + k + 1) → ℂ) : IsClosedSub k r (UWset k r z) :=
  isClosedSub_of (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z) fun _ hg => hg.1

private theorem inv_eq_Hpk_conjTranspose_of_mem_GG {g : Mat k r} (hg : g ∈ GG k r) : g⁻¹ = Hpk k r * gᴴ * Hpk k r := by
  apply Matrix.inv_eq_left_inv
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg', (hpkFacts k r).2.1]

theorem isClosedSub_Sset {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z) :
    IsClosedSub k r (Sset k r z) := by
  obtain ⟨h1, hmul, hinv⟩ := sGroup k r z hz
  have hN := Formalism.FourierDecayAlt.P.unipotent_radical_closed k r
  have hK : IsCompact (UWset k r z) := Formalism.FourierDecayAlt.P.B2x3.compactW k r z hz hT
  have hsub : Sset k r z ⊆ GG k r := by
    rintro s ⟨h, hh, m, hm, rfl⟩
    exact (uHGroup _ _ isUnit_det_Hpk).2.1 h hh.1 m hm.1
  have hclosed : IsClosed (Sset k r z) := by
    have : CompactSpace (UWset k r z) := isCompact_iff_compactSpace.mp hK
    have hC : IsClosed {p : UWset k r z × Mat k r | Hpk k r * (p.1 : Mat k r)ᴴ * Hpk k r * p.2 ∈ Nset k r} :=
      IsClosed.preimage (f := fun p : UWset k r z × Mat k r => Hpk k r * (p.1 : Mat k r)ᴴ * Hpk k r * p.2)
        (((continuous_const.mul (continuous_subtype_val.comp continuous_fst).matrix_conjTranspose).mul
          continuous_const).mul continuous_snd) hN.closed
    have himg : Sset k r z =
        Prod.snd '' {p : UWset k r z × Mat k r | Hpk k r * (p.1 : Mat k r)ᴴ * Hpk k r * p.2 ∈ Nset k r} := by
      ext s
      constructor
      · rintro ⟨h, hh, m, hm, rfl⟩
        refine ⟨(⟨h, hh⟩, h * m), ?_, rfl⟩
        show Hpk k r * hᴴ * Hpk k r * (h * m) ∈ Nset k r
        rw [← inv_eq_Hpk_conjTranspose_of_mem_GG hh.1, ← Matrix.mul_assoc,
          Matrix.nonsing_inv_mul _ (isUnit_det_of_mem_GG hh.1), Matrix.one_mul]
        exact hm
      · rintro ⟨⟨⟨h, hh⟩, s'⟩, hp, rfl⟩
        refine ⟨h, hh, Hpk k r * hᴴ * Hpk k r * s', hp, ?_⟩
        show s' = h * (Hpk k r * hᴴ * Hpk k r * s')
        rw [← inv_eq_Hpk_conjTranspose_of_mem_GG hh.1, ← Matrix.mul_assoc,
          Matrix.mul_nonsing_inv _ (isUnit_det_of_mem_GG hh.1), Matrix.one_mul]
    rw [himg]
    exact isClosedMap_snd_of_compactSpace _ hC
  unfold IsClosedSub
  exact ⟨hsub, hclosed, h1, hmul, hinv⟩

theorem haar_unimod_of_biinv {S : Set (Mat k r)} (hS : IsClosedSub k r S) {μ : Measure (Mt k r)}
    (h : Formalism.FourierDecayAlt.B.IsHaarOn S μ) : IsHaarOn S μ ∧ IsUnimod S μ := by
  have : IsFiniteMeasureOnCompacts μ := ⟨h.finite_compact⟩
  have hsf : SigmaFinite μ := inferInstance
  constructor
  · unfold Formalism.MainNotions.S.IsHaarOn
    exact ⟨hsf, h.ne_zero, h.conc, h.left⟩
  · unfold IsUnimod
    exact ⟨h.right, Formalism.FourierDecayAlt.P.haar_measure_inversion k r S μ hS.isClosedSubgroup h⟩

theorem exists_unimod_GG : ∃ μ : Measure (Mt k r), IsHaarOn (GG k r) μ ∧ IsUnimod (GG k r) μ := by
  obtain ⟨μ, hμ⟩ := Formalism.FourierDecayAlt.P.unitary_group_haar_exists k r
  exact ⟨μ, haar_unimod_of_biinv isClosedSub_GG hμ⟩

def zStd (k r : ℕ) : Fin (2 * r + k + 1) → ℂ := bvec (wI k r (Fin.last k))

theorem Tz_zStd : Tz k r (zStd k r) = 1 := by
  have hH : herm (Hpk k r) (zStd k r) (zStd k r) =
      Hpk k r (wI k r (Fin.last k)) (wI k r (Fin.last k)) := by
    simp [herm, zStd, bvec, Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [Tz, hH]
  simp [Hpk, wI]

def detRep (k r m : ℕ) (h : Mat k r) : ℂ →L[ℂ] ℂ := h.det ^ m • ContinuousLinearMap.id ℂ ℂ

end GlobalTheory.SgInf
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
open MeasureTheory Matrix Finset Formalism.MainNotions.S
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GlobalTheory.Dec

variable {n : ℕ}

def muInt (lam : Fin n → ℝ) (a : Fin n) : ℤ := ⌊lam a + Formalism.QuantumDeterminants.rhoStd n a⌋

def sInt (lam : Fin n → ℝ) (i : Fin n) : ℤ :=
  muInt lam i - (if h : i.val + 1 < n then muInt lam ⟨i.val + 1, h⟩ else 0)

def Omega (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {z | ∀ i : Fin n, leadMinor z (i.val + 1) i.isLt ≠ 0}

def Phi (lam : Fin n → ℝ) (z : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  ∏ i : Fin n, leadMinor z (i.val + 1) i.isLt ^ (-(sInt lam i))

def IsLo (b : Matrix (Fin n) (Fin n) ℂ) : Prop := ∀ i j, i < j → b i j = 0

def IsUp (b : Matrix (Fin n) (Fin n) ℂ) : Prop := ∀ i j, j < i → b i j = 0

def KC (ε : Fin n → Bool) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {y | IsUnit y ∧ y * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * y}

def IsTau (ε : Fin n → Bool) (abelian₂ : Fin n → ℝ) {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (w : W) : Prop :=
  FiniteDimensional ℂ W ∧ Formalism.QuantumDeterminants.IsCRepOn (KC ε) τ ∧
    (∀ u v : W, DifferentiableOn ℂ (fun y : Fin n → Fin n → ℂ => ⟪u, τ (Matrix.of y) v⟫_ℂ)
      {y | Matrix.of y ∈ KC ε}) ∧
    (∀ y ∈ KC ε, ∀ u v : W, ⟪τ y u, v⟫_ℂ = ⟪u, τ yᴴ v⟫_ℂ) ∧
    (∀ S : Submodule ℂ W, IsKStableOn ε τ S → S = ⊥ ∨ S = ⊤) ∧
    ‖w‖ = 1 ∧ IsWtOn (Formalism.REAL.Kset ε) τ (-abelian₂) w ∧
    ∀ y ∈ KC ε, IsLoUni y → τ y w = w

def ps (ε : Fin n → Bool) (lam : Fin n → ℝ) {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (w : W) (z : Matrix (Fin n) (Fin n) ℂ) : W →L[ℂ] W :=
  (Module.finrank ℂ W : ℂ) • ∫ k : Formalism.REAL.KG ε,
    Phi lam ((Formalism.REAL.toMK k)⁻¹ * z * Formalism.REAL.toMK k) •
      (innerSL ℂ (τ (Formalism.REAL.toMK k) w)).smulRight (τ (Formalism.REAL.toMK k) w) ∂(Formalism.REAL.muK ε)

def U1 (ε : Fin n → Bool) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {z | ∀ k ∈ Formalism.REAL.Kset ε, k⁻¹ * z * k ∈ Omega n}

def posPart (g : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Classical.epsilon fun p : Matrix (Fin n) (Fin n) ℂ => p.PosDef ∧ p * p = gᴴ * g

def Psi (ε : Fin n → Bool) (lam : Fin n → ℝ) {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (w : W) (g : Matrix (Fin n) (Fin n) ℂ) : W →L[ℂ] W :=
  (τ (g * (posPart g)⁻¹)).comp (ps ε lam τ w (posPart g))

def cycWord {m : ℕ} (a : Fin (m + 1) → Fin n) : List (Fin n × Fin n) :=
  List.ofFn fun i => (a i, a (finRotate (m + 1) i))

def gelf (ε : Fin n → Bool) (m : ℕ) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) : Matrix (Fin n) (Fin n) ℂ → ℂ :=
  fun g => ∑ a : Fin (m + 1) → Fin n, Formalism.REAL.Eword ε (cycWord a) f g

def Rhol (a b : Fin n) (F : Matrix (Fin n) (Fin n) ℂ → ℂ) : Matrix (Fin n) (Fin n) ℂ → ℂ :=
  fun z => deriv (fun t : ℂ => F (z * NormedSpace.exp (t • Matrix.single a b (1 : ℂ)))) 0

def RholW (w : List (Fin n × Fin n)) (F : Matrix (Fin n) (Fin n) ℂ → ℂ) : Matrix (Fin n) (Fin n) ℂ → ℂ :=
  w.foldr (fun p G => Rhol p.1 p.2 G) F

def gelfH (m : ℕ) (F : Matrix (Fin n) (Fin n) ℂ → ℂ) : Matrix (Fin n) (Fin n) ℂ → ℂ :=
  fun z => ∑ a : Fin (m + 1) → Fin n, RholW (cycWord a) F z

def gelfVal (χ : Fin n → ℂ) (k : ℕ) : ℂ :=
  ∑ a, ∑ b, (Formalism.REAL.Amat (fun c => χ c + ((n : ℂ) - 1) / 2) ^ k) a b

def IsZEigen (ε : Fin n → Bool) (χ : Fin n → ℂ) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) : Prop :=
  Formalism.REAL.SmoothOnG ε f ∧ ∀ m : ℕ, ∀ g ∈ UJset ε, gelf ε m f g = gelfVal χ (m + 1) * f g

def IsZFinite (ε : Fin n → Bool) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) : Prop :=
  Formalism.REAL.SmoothOnG ε f ∧ ∀ m : ℕ, ∃ (N : ℕ) (c : Fin N → ℂ), ∀ g ∈ UJset ε,
    (gelf ε m)^[N] f g = ∑ i, c i * (gelf ε m)^[i.val] f g

def IsBiKFin (ε : Fin n → Bool) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) : Prop :=
  FiniteDimensional ℂ (Submodule.span ℂ {F : Formalism.REAL.UJ ε → ℂ |
    ∃ k₁ ∈ Formalism.REAL.Kset ε, ∃ k₂ ∈ Formalism.REAL.Kset ε, F = fun g => f (k₁ * umat g * k₂)})

def HasInfChar (ε : Fin n → Bool) (χ : Fin n → ℂ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  ∀ v w : H, IsKFin ε σ v → IsKFin ε σ w →
    IsZEigen ε χ (fun g => ⟪w, σ g v⟫_ℂ)

def IsSqIntIrr (ε : Fin n → Bool) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  CompleteSpace H ∧ Nontrivial H ∧ IsURepOn (UJset ε) σ ∧ IsIrredOn (UJset ε) σ ∧ IsSqIntOn ε σ

def UEquiv (ε : Fin n → Bool) {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')) : Prop :=
  ∃ T : H ≃ₗᵢ[ℂ] H', ∀ g ∈ UJset ε, ∀ v, T (σ g v) = σ' g (T v)

def decHS (h : ℝ) (q : ℕ) (t : ℝ) : ℝ := Real.exp (-(h / 8) * min (t ^ 2) (t / Real.sqrt (2 * q)))

def stdRep (y : Matrix (Fin n) (Fin n) ℂ) : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
  Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) y

theorem stdRep_apply (y : Matrix (Fin n) (Fin n) ℂ) (v : EuclideanSpace ℂ (Fin n)) (i : Fin n) :
    stdRep y v i = ∑ j, y i j * v j := rfl

theorem gelfVal_succ (χ : Fin n → ℂ) (k : ℕ) :
    gelfVal χ (k + 1) = ∑ a, ((Formalism.REAL.Amat (fun c => χ c + ((n : ℂ) - 1) / 2) ^ k) *ᵥ
      (fun c => χ c - (Formalism.QuantumDeterminants.rhoStd n c : ℂ))) a := by
  have h : Formalism.REAL.Amat (fun c => χ c + ((n : ℂ) - 1) / 2) *ᵥ (fun _ => (1 : ℂ)) =
      fun c => χ c - (Formalism.QuantumDeterminants.rhoStd n c : ℂ) := by
    funext a
    have e : ∀ b : Fin n, (if a = b then χ a + ((n : ℂ) - 1) / 2 else if a < b then -1 else 0) =
        (if a = b then χ a + ((n : ℂ) - 1) / 2 else 0) - (if b ∈ Finset.Ioi a then 1 else 0) := by
      intro b
      by_cases h1 : a = b
      · subst h1; simp
      · by_cases h2 : a < b <;> simp [h1, h2]
    have hc : (((Finset.Ioi a).card : ℕ) : ℂ) = (n : ℂ) - 1 - (a : ℕ) := by
      have := a.isLt
      rw [Fin.card_Ioi, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
    simp only [Matrix.mulVec, dotProduct, Formalism.REAL.Amat, Matrix.of_apply, mul_one, e,
      Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_ite_mem,
      Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, hc, Formalism.QuantumDeterminants.rhoStd]
    push_cast
    ring
  rw [← h, Matrix.mulVec_mulVec, ← pow_succ]
  simp [gelfVal, Matrix.mulVec, dotProduct]

theorem Eword_const (ε : Fin n → Bool) (c : ℂ) (p : Fin n × Fin n) (w : List (Fin n × Fin n)) :
    Formalism.REAL.Eword ε (p :: w) (fun _ => c) = fun _ => 0 := by
  induction w generalizing p with
  | nil => funext g; simp [Formalism.REAL.Eword, Formalism.REAL.Eab, Formalism.REAL.Ec, Formalism.REAL.Rd]
  | cons q w ih =>
    funext g
    rw [Formalism.REAL.Eword]
    simp only [ih q]
    simp [Formalism.REAL.Eab, Formalism.REAL.Ec, Formalism.REAL.Rd]

section Smooth

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end Smooth


open scoped MatrixOrder in
theorem posPart_posDef_sq {g : Matrix (Fin n) (Fin n) ℂ} (hg : IsUnit g) :
    (posPart g).PosDef ∧ posPart g * posPart g = gᴴ * g := by
  apply Classical.epsilon_spec (p := fun p : Matrix (Fin n) (Fin n) ℂ => p.PosDef ∧ p * p = gᴴ * g)
  have h0 : (0 : Matrix (Fin n) (Fin n) ℂ) ≤ gᴴ * g := (Matrix.posSemidef_conjTranspose_mul_self g).nonneg
  have hs : CFC.sqrt (gᴴ * g) * CFC.sqrt (gᴴ * g) = gᴴ * g := CFC.sqrt_mul_sqrt_self _ h0
  refine ⟨CFC.sqrt (gᴴ * g), ?_, hs⟩
  rw [(Matrix.nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg (gᴴ * g))).posDef_iff_isUnit]
  have hu : IsUnit (gᴴ * g) := (by simpa [Matrix.star_eq_conjTranspose] using hg.star : IsUnit gᴴ).mul hg
  rw [← hs] at hu
  exact isUnit_of_mul_isUnit_left hu


open scoped MatrixOrder in
theorem posPart_eq_of_sq {g p : Matrix (Fin n) (Fin n) ℂ} (hp : p.PosDef) (h : p * p = gᴴ * g) :
    posPart g = p := by
  obtain ⟨h1, h2⟩ : (posPart g).PosDef ∧ posPart g * posPart g = gᴴ * g :=
    Classical.epsilon_spec (p := fun p : Matrix (Fin n) (Fin n) ℂ => p.PosDef ∧ p * p = gᴴ * g) ⟨p, hp, h⟩
  rw [← CFC.sqrt_unique h2 h1.posSemidef.nonneg, ← CFC.sqrt_unique h hp.posSemidef.nonneg]

theorem posPart_unitary_mul {k p : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (hp : p.PosDef) : posPart (k * p) = p := by
  apply posPart_eq_of_sq hp
  have h : kᴴ * k = 1 := Unitary.star_mul_self_of_mem hk
  rw [Matrix.conjTranspose_mul, hp.1.eq, Matrix.mul_assoc, ← Matrix.mul_assoc kᴴ, h, Matrix.one_mul]

theorem Psi_unitary_mul (ε : Fin n → Bool) (lam : Fin n → ℝ) {W : Type} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] (τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (w : W)
    {k p : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) (hp : p.PosDef) :
    Psi ε lam τ w (k * p) = (τ k).comp (ps ε lam τ w p) := by
  unfold Psi
  rw [posPart_unitary_mul hk hp,
    Matrix.mul_nonsing_inv_cancel_right _ _ ((Matrix.isUnit_iff_isUnit_det p).1 hp.isUnit)]

theorem Phi_at_one (lam : Fin n → ℝ) : Phi lam 1 = 1 := by
  unfold Phi leadMinor
  refine Finset.prod_eq_one fun i _ => ?_
  rw [Matrix.submatrix_one _ (Fin.castLE_injective _)]
  simp

end GlobalTheory.Dec
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
open MeasureTheory NumberField Matrix Finset

noncomputable section

namespace GlobalTheory.FlagMeas

open Formalism.MainNotions.S GlobalTheory.Count

def sphV (i : ℕ) : ℝ := ∏ l ∈ Finset.Icc 1 i, 2 * Real.pi ^ l / ((l - 1).factorial : ℝ)

def volU (i : ℕ) : ℝ := sphV i * 2 ^ (i * (i - 1) / 2)

def dimN (n : ℕ) {a : ℕ} (j : Fin a → ℕ) : ℕ :=
  4 * (∑ i, ∑ k ∈ univ.filter (fun k => i < k), j i * j k) + 2 * (∑ i, j i) * (n - 2 * ∑ i, j i) + ∑ i, j i ^ 2

def zetaE (E : Type) [Field E] [NumberField E] (l : ℕ) : ℝ := (dedekindZeta E (l : ℂ)).re

def kapBd (E : Type) [Field E] [NumberField E] [StarRing E] (p q : ℕ) {a : ℕ} (j : Fin a → ℕ) : ℝ :=
  Formalism.HermitianLatticesTheory.vInv E ^ (-((Formalism.HermitianLatticesTheory.fDeg E : ℝ) * dimN (p + q) j / 2)) *
    (2 : ℝ) ^ (-((Formalism.HermitianLatticesTheory.fDeg E : ℝ) *
      (((p + q : ℕ) : ℝ) * (∑ i, j i : ℕ) - ((∑ i, j i : ℕ) : ℝ) ^ 2 + ((∑ i, j i : ℕ) : ℝ) / 2))) *
    (sphV p * sphV q / (sphV (p - ∑ i, j i) * sphV (q - ∑ i, j i) * ∏ i, sphV (j i))) ^ Formalism.HermitianLatticesTheory.fDeg E *
    dedekindZeta_residue E ^ a * (∏ i, ∏ l ∈ Finset.Icc 2 (j i), zetaE E l) /
    ∏ M ∈ Finset.Ioc (p + q - 2 * ∑ i, j i) (p + q), Formalism.HermitianLatticesTheory.lValEta E M

def simplexH (a : ℕ) : Set (Fin a → ℝ) := {τ | StrictMono τ ∧ ∀ i, 0 < τ i ∧ τ i < 1 / 2}

def dens (n f : ℕ) {a : ℕ} (j : Fin a → ℕ) (τ : Fin a → ℝ) : ℝ :=
  layerProd n f j τ id * ∏ i, 2 * (f : ℝ) * j i / τ i

def typeSet (I : AutInst) {a : ℕ} (j : Fin a → ℕ) (B : Set (Fin a → ℝ)) : Set I.GA :=
  {x | ∃ τ ∈ B, HasType I x j τ}

def covol {G : Type} [Mul G] [MeasurableSpace G] (Γ : Set G) (μ : Measure G) (A : Set G) : ENNReal :=
  ⨅ (D : Set G) (_ : MeasurableSet D) (_ : ∀ x ∈ A, ∃ γ ∈ Γ, γ * x ∈ D), μ D

def gaugeVol (I : AutInst) (c : InfinitePlace I.F → ℝ) (μf : Measure I.Gf) [SigmaFinite μf] : ENNReal :=
  ENNReal.ofReal (∏ v, c v) * covol I.GFset (I.muA μf) Set.univ / μf I.Kset

def SameField (I I' : AutInst) : Prop := ∃ e : I'.E ≃+* I.E, ∀ x, e (star x) = star (e x)

def HasSig (I : AutInst) (p q : ℕ) : Prop := ∀ v, I.pAt v = p ∧ I.qAt v = q

section Real

variable {n : ℕ} {ε : Fin n → Bool}

def IsGaugeSub (S : Set (Formalism.REAL.UJ ε)) (d : ℕ) (μ : Measure (Formalism.REAL.UJ ε)) : Prop :=
  μ Sᶜ = 0 ∧ (∀ s ∈ S, μ.map (fun g => s * g) = μ) ∧
    Filter.Tendsto
      (fun r : ℝ => μ {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r} / ENNReal.ofReal (r ^ d))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)))

def IsIsoFlag (ε : Fin n → Bool) {a : ℕ} (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) : Prop :=
  W 0 = ⊥ ∧ Monotone W ∧
    (∀ i : Fin a, Module.finrank ℂ (W i.succ) = Module.finrank ℂ (W i.castSucc) + j i) ∧
    ∀ x ∈ W (Fin.last a), ∀ y ∈ W (Fin.last a), star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) = 0

def flagN (ε : Fin n → Bool) {a : ℕ} (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) : Set (Formalism.REAL.UJ ε) :=
  {g | (∀ i : Fin a, ∀ y ∈ W i.succ, uMat g *ᵥ y - y ∈ W i.castSucc) ∧
    ∀ y : Fin n → ℂ, (∀ x ∈ W (Fin.last a), star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) = 0) →
      uMat g *ᵥ y - y ∈ W (Fin.last a)}

def flagM (ε : Fin n → Bool) {a : ℕ} (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) : Set (Formalism.REAL.UJ ε) :=
  {g | ∀ i, ∀ y ∈ W i, uMat g *ᵥ y ∈ W i ∧ (uMat g)ᴴ *ᵥ y ∈ W i}

def maxK (ε : Fin n → Bool) : Set (Formalism.REAL.UJ ε) := {g | (uMat g)ᴴ * uMat g = 1}


open Classical in
def detOn (g : Matrix (Fin n) (Fin n) ℂ) (W : Submodule ℂ (Fin n → ℂ)) : ℝ :=
  if h : ∀ y ∈ W, Matrix.toLin' g y ∈ W then ‖LinearMap.det ((Matrix.toLin' g).restrict h)‖ else 0

def locSize {a : ℕ} (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ))
    (g : Matrix (Fin n) (Fin n) ℂ) (i : Fin a) : ℝ :=
  (detOn g (W i.succ) / detOn g (W i.castSucc)) ^ (-(1 : ℝ) / j i)

end Real

section GenLin

variable (E : Type) [Field E] [NumberField E] (j : ℕ)

def MatInf : Type := InfinitePlace E → Fin j → Fin j → ℂ

instance : MeasurableSpace (MatInf E j) := inferInstanceAs (MeasurableSpace (InfinitePlace E → Fin j → Fin j → ℂ))

instance : Mul (MatInf E j) := ⟨fun x y w a b => (Matrix.of (x w) * Matrix.of (y w)) a b⟩

def detNorm (x : MatInf E j) : ℝ := ∏ w, ‖(Matrix.of (x w)).det‖ ^ 2

def haarGL : Measure (MatInf E j) :=
  Measure.withDensity (volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ))
    fun x => ENNReal.ofReal ((detNorm E j x)⁻¹ ^ j)

def autGL (Λ : Submodule (𝓞 E) (Fin j → E)) : Set (MatInf E j) :=
  {x | ∃ γ : GL (Fin j) E, (∀ y, (γ : Matrix (Fin j) (Fin j) E) *ᵥ y ∈ Λ ↔ y ∈ Λ) ∧
    ∀ w a b, x w a b = w.embedding ((γ : Matrix (Fin j) (Fin j) E) a b)}

def glVol : ENNReal :=
  ∑' c : Quot (fun Λ Λ' : {Λ : Submodule (𝓞 E) (Fin j → E) // Submodule.IsFullLattice E Λ} =>
      ∃ γ : GL (Fin j) E, ∀ y, (γ : Matrix (Fin j) (Fin j) E) *ᵥ y ∈ Λ'.1 ↔ y ∈ Λ.1),
    covol (autGL E j (Quot.out c).1) (haarGL E j) {x | 1 ≤ detNorm E j x ∧ detNorm E j x < Real.exp 1}

end GenLin

def defClassNum (E : Type) [Field E] [NumberField E] [StarRing E] (r : ℕ) : ENat :=
  ENat.card (Quot (fun X Y : {X : Matrix (Fin r) (Fin r) E × Submodule (𝓞 E) (Fin r → E) //
      X.1ᴴ = X.1 ∧ (∀ (φ : E →+* ℂ) (y : Fin r → E), y ≠ 0 → 0 < (φ (star y ⬝ᵥ (X.1 *ᵥ y))).re) ∧
      Submodule.IsLattice E X.2 ∧
      ∀ x, x ∈ X.2 ↔ ∀ y ∈ X.2, star y ⬝ᵥ (X.1 *ᵥ x) ∈ (algebraMap (𝓞 E) E).range} =>
    ∃ γ : GL (Fin r) E, (γ : Matrix (Fin r) (Fin r) E)ᴴ * Y.1.1 * (γ : Matrix (Fin r) (Fin r) E) = X.1.1 ∧
      ∀ y, (γ : Matrix (Fin r) (Fin r) E) *ᵥ y ∈ Y.1.2 ↔ y ∈ X.1.2))

end GlobalTheory.FlagMeas
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LamXEquivariant
open MeasureTheory NumberField Matrix Finset
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.Count.Test

open Formalism.MainNotions.S GlobalTheory.Count

variable (I : AutInst)

theorem mem_lamX (x : I.GA) (y : Fin I.n → I.E) : y ∈ lamX I x ↔
    I.fmat x.2⁻¹ *ᵥ (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (y i)) ∈ I.Lf := by
  constructor
  · intro hy
    unfold lamX at hy
    induction hy using Submodule.span_induction with
    | mem z hz => exact hz
    | zero =>
      have e0 : (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) ((0 : Fin I.n → I.E) i)) = 0 := by
        ext i; simp
      rw [e0, Matrix.mulVec_zero]
      exact zero_mem _
    | add z₁ z₂ _ _ h₁ h₂ =>
      have e2 : (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) ((z₁ + z₂) i)) =
          (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (z₁ i)) +
            (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (z₂ i)) := by
        ext i; simp
      rw [e2, Matrix.mulVec_add]
      exact add_mem h₁ h₂
    | smul a z _ hz =>
      have hc : Formalism.UG.inclE (F := I.F) (Af I.F) (algebraMap (𝓞 I.E) I.E a) ∈ IntAf I.F I.E :=
        Subring.subset_closure (Or.inl ⟨⟨_, a, rfl⟩, rfl⟩)
      have e1 : (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) ((a • z) i)) =
          Formalism.UG.inclE (F := I.F) (Af I.F) (algebraMap (𝓞 I.E) I.E a) •
            (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (z i)) := by
        ext i; simp [Algebra.smul_def]
      rw [e1, Matrix.mulVec_smul]
      exact I.Lf.smul_mem ⟨_, hc⟩ hz
  · intro hy
    exact Submodule.subset_span hy

theorem le_lamX_one : I.L ≤ lamX I 1 := by
  intro y hy
  rw [mem_lamX]
  have h1 : I.fmat (1 : I.GA).2⁻¹ = 1 := by simp [AutInst.fmat]
  rw [h1, Matrix.one_mulVec]
  exact Submodule.subset_span ⟨⟨y, hy⟩, rfl⟩

theorem one_mem_GF : (1 : I.GA) ∈ I.GFset := by
  simp only [AutInst.GFset, Set.mem_ofPred_eq]
  refine ⟨1, one_mem _, fun v => ?_, ?_⟩
  · have hdet : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v)
    simp [uMat, Matrix.nonsing_inv_mul _ hdet]
  · simp [AutInst.fmat]

theorem lamX_equivariant (g x : I.GA) (γ : GL (Fin I.n) I.E)
    (h : I.fmat g.2 = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)))
    (y : Fin I.n → I.E) :
    (γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ y ∈ lamX I (g * x) ↔ y ∈ lamX I x := by
  have hm : ∀ a b : I.Gf, I.fmat (a * b) = I.fmat a * I.fmat b := fun a b => by
    simp [AutInst.fmat]
  have h1 : I.fmat 1 = 1 := by simp [AutInst.fmat]
  have hinc : (fun i => Formalism.UG.inclE (F := I.F) (Af I.F)
      (((γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ y) i)) =
      I.fmat g.2 *ᵥ (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (y i)) := by
    ext i
    rw [h, RingHom.map_mulVec]
    rfl
  rw [mem_lamX, mem_lamX, hinc, Prod.snd_mul, _root_.mul_inv_rev, hm, Matrix.mulVec_mulVec, mul_assoc,
    ← hm g.2⁻¹ g.2, inv_mul_cancel, h1, mul_one]

theorem embedding_cases (w : InfinitePlace I.E) :
    w.embedding = I.φ (w.comap (algebraMap I.F I.E)) ∨
      w.embedding = ComplexEmbedding.conjugate (I.φ (w.comap (algebraMap I.F I.E))) := by
  have hcm := I.cm.cmUnram.2.1
  have hF : ∀ a : I.F, w.embedding (algebraMap I.F I.E a) =
      I.φ (w.comap (algebraMap I.F I.E)) (algebraMap I.F I.E a) := by
    have := I.cm.totReal
    have hv : w.comap (algebraMap I.F I.E) =
        InfinitePlace.mk (w.embedding.comp (algebraMap I.F I.E)) := by
      rw [← InfinitePlace.comap_mk, InfinitePlace.mk_embedding]
    have hψ : (I.φ (w.comap (algebraMap I.F I.E))).comp (algebraMap I.F I.E) =
        (w.comap (algebraMap I.F I.E)).embedding := RingHom.ext (I.φ_over _)
    have hreal : ComplexEmbedding.conjugate (w.embedding.comp (algebraMap I.F I.E)) =
        w.embedding.comp (algebraMap I.F I.E) :=
      ComplexEmbedding.isReal_iff.mp (InfinitePlace.isReal_mk_iff.mp (IsTotallyReal.isReal _))
    have hmk : InfinitePlace.mk (w.embedding.comp (algebraMap I.F I.E)) =
        InfinitePlace.mk ((I.φ (w.comap (algebraMap I.F I.E))).comp (algebraMap I.F I.E)) := by
      rw [hψ, InfinitePlace.mk_embedding, hv]
    have key : w.embedding.comp (algebraMap I.F I.E) =
        (I.φ (w.comap (algebraMap I.F I.E))).comp (algebraMap I.F I.E) := by
      rcases InfinitePlace.mk_eq_iff.mp hmk with h | h
      · exact h
      · rwa [hreal] at h
    intro a
    exact RingHom.congr_fun key a
  set ψ := I.φ (w.comap (algebraMap I.F I.E)) with hψdef
  have hpt : ∀ e : I.E, w.embedding e = ψ e ∨ w.embedding e = starRingEnd ℂ (ψ e) := by
    intro e
    obtain ⟨s, hs⟩ := (I.cm.fixed (e + star e)).1 (by rw [star_add, star_star, add_comm])
    obtain ⟨t, ht⟩ := (I.cm.fixed (e * star e)).1 (by rw [star_mul, star_star])
    have h1 : w.embedding e + starRingEnd ℂ (w.embedding e) = ψ e + starRingEnd ℂ (ψ e) := by
      rw [← hcm w.embedding, ← hcm ψ, ← map_add (f := _), ← map_add (f := _), ← hs, hF]
    have h2 : w.embedding e * starRingEnd ℂ (w.embedding e) = ψ e * starRingEnd ℂ (ψ e) := by
      rw [← hcm w.embedding, ← hcm ψ, ← map_mul, ← map_mul, ← ht, hF]
    have h3 : (w.embedding e - ψ e) * (w.embedding e - starRingEnd ℂ (ψ e)) = 0 := by
      linear_combination (w.embedding e) * h1 - h2
    rcases mul_eq_zero.mp h3 with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (sub_eq_zero.mp h)
  by_contra hne
  push Not at hne
  obtain ⟨hne1, hne2⟩ := hne
  obtain ⟨a, ha⟩ : ∃ a, w.embedding a ≠ ψ a := by
    by_contra hc
    push Not at hc
    exact hne1 (RingHom.ext hc)
  obtain ⟨b, hb⟩ : ∃ b, w.embedding b ≠ starRingEnd ℂ (ψ b) := by
    by_contra hc
    push Not at hc
    exact hne2 (RingHom.ext fun x => (hc x).trans (ComplexEmbedding.conjugate_coe_eq ψ x).symm)
  have ha' := (hpt a).resolve_left ha
  have hb' := (hpt b).resolve_right hb
  rcases hpt (a + b) with h | h
  · apply ha
    rw [map_add (f := _), map_add (f := _)] at h
    linear_combination h - hb'
  · apply hb
    rw [map_add (f := _), map_add (f := _), map_add (f := _)] at h
    linear_combination h - ha'

theorem frm_frame (x : I.GA) (w : InfinitePlace I.E) :
    (frm I x w)ᴴ * I.J.map w.embedding * frm I x w = Formalism.REAL.Jm (I.ε (w.comap (algebraMap I.F I.E))) := by
  have hU : (uMat (x.1 (w.comap (algebraMap I.F I.E))))ᴴ * Formalism.REAL.Jm (I.ε (w.comap (algebraMap I.F I.E))) *
      uMat (x.1 (w.comap (algebraMap I.F I.E))) = Formalism.REAL.Jm (I.ε (w.comap (algebraMap I.F I.E))) :=
    (x.1 (w.comap (algebraMap I.F I.E))).2
  have key : (I.P (w.comap (algebraMap I.F I.E)) * uMat (x.1 (w.comap (algebraMap I.F I.E))))ᴴ *
      I.J.map (I.φ (w.comap (algebraMap I.F I.E))) *
      (I.P (w.comap (algebraMap I.F I.E)) * uMat (x.1 (w.comap (algebraMap I.F I.E)))) =
      Formalism.REAL.Jm (I.ε (w.comap (algebraMap I.F I.E))) := by
    rw [Matrix.conjTranspose_mul]
    calc _ = (uMat (x.1 (w.comap (algebraMap I.F I.E))))ᴴ *
          ((I.P (w.comap (algebraMap I.F I.E)))ᴴ * I.J.map (I.φ (w.comap (algebraMap I.F I.E))) *
            I.P (w.comap (algebraMap I.F I.E))) * uMat (x.1 (w.comap (algebraMap I.F I.E))) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [I.P_spec]; exact hU
  have hc : ∀ A : Matrix (Fin I.n) (Fin I.n) ℂ,
      (A.map (starRingEnd ℂ))ᴴ = Aᴴ.map (starRingEnd ℂ) := by
    intro A; ext i j; simp [Matrix.conjTranspose_apply]
  simp only [frm]
  split_ifs with h
  · rw [h]; exact key
  · rw [(embedding_cases I w).resolve_left h]
    have hJ : I.J.map (ComplexEmbedding.conjugate (I.φ (w.comap (algebraMap I.F I.E)))) =
        (I.J.map (I.φ (w.comap (algebraMap I.F I.E)))).map (starRingEnd ℂ) := by
      ext i j; simp [ComplexEmbedding.conjugate_coe_eq]
    rw [hJ, hc, ← Matrix.map_mul, ← Matrix.map_mul, key]
    ext i j
    simp [Formalism.REAL.Jm, Matrix.diagonal_apply, apply_ite (starRingEnd ℂ)]

theorem one_mem_nearSet (x : I.GA) {δ : ℝ} (hδ : 0 ≤ δ) : (1 : I.GA) ∈ nearSet I x δ := by
  simp only [nearSet, Set.mem_ofPred_eq]
  refine ⟨one_mem_GF I, ?_, fun v => ?_⟩
  · rw [mul_one, inv_mul_cancel]
    exact one_mem (Formalism.UG.stabGL I.Lf)
  · simp [uMat, Formalism.REAL.hs, hδ]

end GlobalTheory.Count.Test
end
end
