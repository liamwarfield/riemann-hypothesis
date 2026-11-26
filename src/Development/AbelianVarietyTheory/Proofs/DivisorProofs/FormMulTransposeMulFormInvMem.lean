module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOfLocallyFiniteFreeLocalizations
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalRingEtaleOverIndEtaleDirectedUnionStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HasQExpansionModularForm
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsNormSubEqOne
public import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIdealInClassOfNormLeSqrtDiscr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzContinuousAtOfPointwiseOfBounded

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormMulTransposeMulFormInvMem
noncomputable section

open Matrix

namespace GlobalTheory.ZarhinFam

def quat (d : ℕ) : Matrix (Fin 4) (Fin 4) ℤ :=
  Classical.choose (GlobalTheory.exists_int_matrix_transpose_mul_eq_smul_one (d - 1))

theorem quat_transpose_mul (d : ℕ) :
    (quat d)ᵀ * quat d = ((d - 1 : ℕ) : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) :=
  (Classical.choose_spec (GlobalTheory.exists_int_matrix_transpose_mul_eq_smul_one (d - 1))).1

theorem quat_mul_transpose (d : ℕ) :
    quat d * (quat d)ᵀ = ((d - 1 : ℕ) : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) :=
  (Classical.choose_spec (GlobalTheory.exists_int_matrix_transpose_mul_eq_smul_one (d - 1))).2

def form (d : ℕ) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ :=
  fromBlocks 1 (quat d)ᵀ (quat d) ((d : ℤ) • 1)

def formInv (d : ℕ) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ :=
  fromBlocks ((d : ℤ) • 1) (-(quat d)ᵀ) (-(quat d)) 1

theorem form_transpose (d : ℕ) : (form d)ᵀ = form d := by
  simp [form, fromBlocks_transpose]

theorem form_mul_formInv {d : ℕ} (hd : 0 < d) : form d * formInv d = 1 := by
  have h1 : ((d - 1 : ℕ) : ℤ) = (d : ℤ) - 1 := by omega
  rw [form, formInv, fromBlocks_multiply, ← fromBlocks_one]
  congr 1
  · rw [Matrix.mul_neg, quat_transpose_mul, h1]; simp [sub_smul]
  · simp
  · simp only [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_neg, smul_neg, add_neg_cancel]
  · rw [Matrix.mul_neg, quat_mul_transpose, h1]; simp [sub_smul]

theorem formInv_mul_form {d : ℕ} (hd : 0 < d) : formInv d * form d = 1 :=
  mul_eq_one_comm.mp (form_mul_formInv hd)

def ord (d : ℕ) : Subring (Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) where
  carrier := {N | ∀ i j, (d : ℤ) ∣ N (Sum.inr i) (Sum.inl j)}
  mul_mem' {N N'} hN hN' i j := by
    simp only [Set.mem_setOf_eq] at hN hN'
    rw [Matrix.mul_apply, Fintype.sum_sum_type]
    exact dvd_add (Finset.dvd_sum fun k _ => (hN i k).mul_right _)
      (Finset.dvd_sum fun k _ => (hN' k j).mul_left _)
  one_mem' i j := by simp
  add_mem' {N N'} hN hN' i j := by
    simp only [Set.mem_setOf_eq] at hN hN'
    exact dvd_add (hN i j) (hN' i j)
  zero_mem' i j := by simp
  neg_mem' {N} hN i j := by
    simp only [Set.mem_setOf_eq] at hN
    simpa using hN i j

theorem form_mul_transpose_mul_formInv_mem {d : ℕ} {N : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ}
    (hN : N ∈ ord d) : form d * Nᵀ * formInv d ∈ ord d := by
  intro i j
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have key : ∀ i j, ((N (Sum.inr i) (Sum.inl j) : ℤ) : ZMod d) = 0 := fun i j =>
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (hN i j)
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, form, formInv, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
    fromBlocks_apply₂₁, fromBlocks_apply₂₂, transpose_apply, Int.cast_add, Int.cast_sum, Int.cast_mul,
    Matrix.smul_apply, Matrix.neg_apply, Int.cast_neg, smul_eq_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul,
    mul_zero, key, Finset.sum_const_zero, add_zero, zero_add, mul_neg, neg_mul]
  simp

def barM (d : ℕ) (N : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ :=
  form d * Nᵀ * formInv d

def bar (d : ℕ) (N : ord d) : ord d := ⟨barM d N, form_mul_transpose_mul_formInv_mem N.2⟩

@[simp] theorem bar_coe (d : ℕ) (N : ord d) :
    ((bar d N : ord d) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) =
      form d * (N : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ)ᵀ * formInv d :=
  rfl

theorem bar_add (d : ℕ) (a b : ord d) : bar d (a + b) = bar d a + bar d b := by
  ext1
  simp [Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul]

theorem formInv_transpose (d : ℕ) : (formInv d)ᵀ = formInv d := by
  simp [formInv, fromBlocks_transpose]

theorem bar_bar {d : ℕ} (hd : 0 < d) (a : ord d) : bar d (bar d a) = a := by
  ext1
  simp only [bar_coe, Matrix.transpose_mul, Matrix.transpose_transpose, form_transpose, formInv_transpose]
  calc form d * (formInv d * ((a : Matrix _ _ ℤ) * form d)) * formInv d
      = (form d * formInv d) * (a : Matrix _ _ ℤ) * (form d * formInv d) := by simp only [Matrix.mul_assoc]
    _ = (a : Matrix _ _ ℤ) := by rw [form_mul_formInv hd, Matrix.one_mul, Matrix.mul_one]

def idem (d : ℕ) : ord d :=
  ⟨single (Sum.inl 0) (Sum.inl 0) 1, fun i j => by simp [single]⟩

theorem idem_mul_self (d : ℕ) : idem d * idem d = idem d := by
  ext1
  simp [idem]

end GlobalTheory.ZarhinFam
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndEtaleLocalizedPiecesTrans
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EssEtaleLocalLeOfDirected
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EssEtaleLocalLeOfDirected
open IsLocalRing

namespace GlobalTheory

theorem essEtaleLocal_le_of_directed :
  ∀ (R T : Type) [CommRing R] [CommRing T] [Algebra R T] (U : Subalgebra R T) (μ : Type) [Preorder μ] [IsDirected μ (· ≤ ·)] [Nonempty μ] (V : μ → Subalgebra R T), Monotone V → (∀ x ∈ U, ∃ m, x ∈ V m) → (∀ m, ∀ x ∈ V m, ∀ y ∈ U, x * y = 1 → ∃ z ∈ V m, x * z = 1) → ∀ (W : Subalgebra R T), W ≤ U → (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] W)) → ∃ m, W ≤ V m := by
  classical
  intro R T _ _ _ U μ _ _ _ V hmono hcov hloc W hWU hW
  obtain ⟨A, _, _, _, q, _, ⟨e⟩⟩ := hW
  let L := Localization.AtPrime q
  let φ : A →ₐ[R] T := W.val.comp (e.toAlgHom.comp (IsScalarTower.toAlgHom R A L))
  have hφW : ∀ a, φ a ∈ W := fun a => (e (algebraMap A L a)).2
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra R A).FG)
  choose f hf using fun a : A => hcov (φ a) (hWU (hφW a))
  obtain ⟨M, hM⟩ := (s.image f).exists_le
  have hrange : ∀ a, φ a ∈ V M := by
    have hle : (⊤ : Subalgebra R A) ≤ (V M).comap φ := by
      rw [← hs]
      refine Algebra.adjoin_le ?_
      intro a ha
      exact hmono (hM _ (Finset.mem_image_of_mem f ha)) (hf a)
    intro a
    exact hle Algebra.mem_top
  refine ⟨M, fun w hw => ?_⟩
  obtain ⟨⟨a, t⟩, hat⟩ := IsLocalization.mk'_surjective q.primeCompl (e.symm ⟨w, hw⟩)
  set y : T := ((e (IsLocalization.mk' L (1 : A) t) : W) : T) with hy
  have hyU : y ∈ U := hWU (e _).2
  have hxy : φ t * y = 1 := by
    have h1 : algebraMap A L t * IsLocalization.mk' L (1:A) t = 1 := by
      rw [IsLocalization.mul_mk'_eq_mk'_of_mul, mul_one, IsLocalization.mk'_self']
    have h2 : ((e (algebraMap A L t * IsLocalization.mk' L (1:A) t) : W) : T) = 1 := by
      rw [h1, map_one]; rfl
    rw [map_mul, Subalgebra.coe_mul] at h2
    exact h2
  obtain ⟨z, hzV, hz⟩ := hloc M (φ t) (hrange t) y hyU hxy
  have hzy : z = y := by
    calc z = (y * φ t) * z := by rw [mul_comm y, hxy, one_mul]
      _ = y * (φ t * z) := by ring
      _ = y := by rw [hz, mul_one]
  have hw' : w = φ a * y := by
    have h1 : (⟨w, hw⟩ : W) = e (IsLocalization.mk' L a t) := by
      change IsLocalization.mk' L a t = _ at hat
      rw [hat, AlgEquiv.apply_symm_apply]
    have h2 : IsLocalization.mk' L a t = algebraMap A L a * IsLocalization.mk' L (1:A) t := by
      rw [IsLocalization.mul_mk'_eq_mk'_of_mul, mul_one]
    have h3 : w = ((e (IsLocalization.mk' L a t) : W) : T) := congrArg Subtype.val h1
    rw [h3, h2, map_mul, Subalgebra.coe_mul]
    rfl
  rw [hw', ← hzy]
  exact (V M).mul_mem (hrange a) hzV

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EssEtaleLocalLeOfDirectedStatement
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_le_of_essEtaleLocal_directed : ∀ (R T : Type) [CommRing R] [CommRing T] [Algebra R T] (U : Subalgebra R T) (μ : Type) [Preorder μ] [IsDirected μ (· ≤ ·)] [Nonempty μ] (V : μ → Subalgebra R T), Monotone V → (∀ x ∈ U, ∃ m, x ∈ V m) → (∀ m, ∀ x ∈ V m, ∀ y ∈ U, x * y = 1 → ∃ z ∈ V m, x * z = 1) → ∀ (W : Subalgebra R T), W ≤ U → (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] W)) → ∃ m, W ≤ V m := by
  first | exact @GlobalTheory.essEtaleLocal_le_of_directed | exact GlobalTheory.essEtaleLocal_le_of_directed | (intros; apply GlobalTheory.essEtaleLocal_le_of_directed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndEtaleLocalizedPiecesTrans
open IsLocalRing

namespace GlobalTheory

theorem indEtale_localPieces_trans : ∀ (R S T : Type) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T], (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra R S), Monotone Si ∧ (∀ s : S, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Si i)) → (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra S T), Monotone Si ∧ (∀ s : T, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra S A) (_ : Algebra.Etale S A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[S] Si i)) → (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra R T), Monotone Si ∧ (∀ s : T, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Si i)) := by
  intro R S T _ _ _ _ _ _ _ hS hT
  obtain ⟨κ, _, _, _, Tj, hmono, hcov, hpc⟩ := hT
  have hK : ∀ j, ∃ (μ : Type) (_ : Preorder μ) (_ : IsDirected μ (· ≤ ·)) (_ : Nonempty μ)
      (V : μ → Subalgebra R T), Monotone V ∧ (∀ m, V m ≤ (Tj j).restrictScalars R) ∧
      (∀ x ∈ Tj j, ∃ m, x ∈ V m) ∧
      (∀ m, ∀ x ∈ V m, ∀ y ∈ Tj j, x * y = 1 → ∃ z ∈ V m, x * z = 1) ∧ ∀ m, (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] V m)) := by
    intro j
    obtain ⟨B, _, _, _, Q, _, ⟨e⟩⟩ := hpc j
    exact GlobalTheory.T.localRing_etale_over_indEtale_directedUnion R S T hS (Tj j) B Q ⟨e⟩
  choose μ pre dir ne V hVmono hVle hVcov hVloc hVee using hK
  let P : Subalgebra R T → Prop := fun W => ∃ (j : κ) (m : μ j), V j m = W
  have key : ∀ (j₁ : κ) (m₁ : μ j₁) (j : κ), j₁ ≤ j → ∃ m : μ j, V j₁ m₁ ≤ V j m := by
    intro j₁ m₁ j hj
    letI := pre j; haveI := dir j; haveI := ne j
    refine GlobalTheory.T.exists_le_of_essEtaleLocal_directed R T ((Tj j).restrictScalars R) (μ j) (V j) (hVmono j) ?_ ?_ (V j₁ m₁) ?_
      (hVee j₁ m₁)
    · intro x hx; exact hVcov j x hx
    · intro m x hx y hy hxy; exact hVloc j m x hx y hy hxy
    · intro x hx
      have := hVle j₁ m₁ hx
      exact hmono hj this
  refine ⟨{W : Subalgebra R T // P W}, inferInstance, ⟨?_⟩, ?_, Subtype.val, fun a b h => h, ?_, ?_⟩
  · rintro ⟨W₁, j₁, m₁, rfl⟩ ⟨W₂, j₂, m₂, rfl⟩
    obtain ⟨j, h₁, h₂⟩ := directed_of (· ≤ ·) j₁ j₂
    obtain ⟨a, ha⟩ := key j₁ m₁ j h₁
    obtain ⟨b, hb⟩ := key j₂ m₂ j h₂
    letI := pre j; haveI := dir j
    obtain ⟨c, hac, hbc⟩ := directed_of (· ≤ ·) a b
    exact ⟨⟨V j c, j, c, rfl⟩, ha.trans (hVmono j hac), hb.trans (hVmono j hbc)⟩
  · obtain ⟨j⟩ := (inferInstance : Nonempty κ)
    obtain ⟨m⟩ := ne j
    exact ⟨⟨V j m, j, m, rfl⟩⟩
  · intro t
    obtain ⟨j, hj⟩ := hcov t
    obtain ⟨m, hm⟩ := hVcov j t hj
    exact ⟨⟨V j m, j, m, rfl⟩, hm⟩
  · rintro ⟨W, j, m, rfl⟩
    exact hVee j m

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndEtaleLocalizedPiecesTransStatement
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.indEtale_localizedPieces_trans : ∀ (R S T : Type) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T], (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra R S), Monotone Si ∧ (∀ s : S, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Si i)) → (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra S T), Monotone Si ∧ (∀ s : T, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra S A) (_ : Algebra.Etale S A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[S] Si i)) → (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra R T), Monotone Si ∧ (∀ s : T, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Si i)) := by
  first | exact @GlobalTheory.indEtale_localPieces_trans | exact GlobalTheory.indEtale_localPieces_trans | (intros; apply GlobalTheory.indEtale_localPieces_trans <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetEqOneUnitaryPrincipalCongruenceLevelThree
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetEqOneUnitaryPrincipalCongruenceLevelThree
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD Polynomial

namespace GlobalTheory.UnitaryCongruenceDet

noncomputable section

def ccHom (E : Type) [Field E] [NumberField E] [IsCMField E] : E →+* E :=
  (IsCMField.complexConj E : E →+* E)

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem cc_eq (x : E) : cc x = ccHom E x := rfl

theorem transpose_mul_mul_map {r : ℕ} (G γ : Matrix (Fin r) (Fin r) E)
    (h : ∀ x y, herm G (γ *ᵥ x) (γ *ᵥ y) = herm G x y) :
    γᵀ * G * γ.map (ccHom E) = G := by
  ext i j
  have hs : ∀ k, γ *ᵥ Pi.single k 1 = fun a => γ a k := by
    intro k; funext a; simp [mulVec, dotProduct, Pi.single_apply]
  have hij := h (Pi.single i 1) (Pi.single j 1)
  simp only [herm, cc_eq, hs] at hij
  simp only [Matrix.mul_apply, transpose_apply, map_apply, Finset.sum_mul]
  rw [Finset.sum_comm, hij]
  simp [Pi.single_apply]

theorem det_mul_cc_det {r : ℕ} (G γ : Matrix (Fin r) (Fin r) E) (hG : G.det ≠ 0)
    (h : ∀ x y, herm G (γ *ᵥ x) (γ *ᵥ y) = herm G x y) :
    γ.det * cc γ.det = 1 := by
  have e := congrArg Matrix.det (transpose_mul_mul_map G γ h)
  have hd : (γ.map (ccHom E)).det = ccHom E γ.det := by rw [RingHom.map_det]; rfl
  rw [det_mul, det_mul, det_transpose, hd] at e
  rw [cc_eq]
  apply mul_right_cancel₀ hG
  linear_combination e

theorem isIntegral_of_left_eigen {r : ℕ} {Ω : Type} [Field Ω] [Algebra E Ω]
    (C : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (hfg : Λ.FG)
    (hspan : Submodule.span E (Λ : Set (Fin r → E)) = ⊤) (hC : ∀ x ∈ Λ, C *ᵥ x ∈ Λ)
    (μ : Ω) (u : Fin r → Ω) (hu : u ≠ 0) (hμ : u ᵥ* C.map (algebraMap E Ω) = μ • u) :
    IsIntegral ℤ μ := by
  classical
  let φ := algebraMap E Ω
  let g : (Fin r → E) →ₗ[E] Ω :=
    { toFun := fun x => u ⬝ᵥ (fun a => φ (x a))
      map_add' := by
        intro x y
        simp only [Pi.add_apply, map_add (f := _)]
        rw [← dotProduct_add]; rfl
      map_smul' := by
        intro c x
        simp only [Pi.smul_apply, smul_eq_mul, map_mul, RingHom.id_apply, dotProduct,
          Algebra.smul_def]
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => by ring }
  let N : Submodule ℤ Ω := (Λ.restrictScalars ℤ).map (g.restrictScalars ℤ)
  have hNfg : N.FG := (Submodule.FG.restrictScalars (R := ℤ) hfg).map _
  have hN : N ≠ ⊥ := by
    intro hN
    apply hu
    have hker : Submodule.span E (Λ : Set (Fin r → E)) ≤ LinearMap.ker g := by
      rw [Submodule.span_le]
      intro x hx
      have : g x ∈ N := Submodule.mem_map.2 ⟨x, hx, rfl⟩
      rw [hN, Submodule.mem_bot] at this
      exact this
    rw [hspan] at hker
    funext j
    have := hker (Submodule.mem_top (x := Pi.single j 1))
    rw [LinearMap.mem_ker] at this
    simpa [g, φ, dotProduct, Pi.single_apply, apply_ite] using this
  refine isIntegral_of_smul_mem_submodule N hN hNfg μ ?_
  rintro n hn
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hn
  refine Submodule.mem_map.2 ⟨C *ᵥ x, hC x hx, ?_⟩
  change u ⬝ᵥ (fun a => φ ((C *ᵥ x) a)) = μ • (u ⬝ᵥ fun a => φ (x a))
  have h1 : (fun a => φ ((C *ᵥ x) a)) = C.map φ *ᵥ (fun a => φ (x a)) := by
    funext a; exact RingHom.map_mulVec φ C x a
  rw [h1, dotProduct_mulVec, hμ, smul_dotProduct, smul_eq_mul]

theorem prod_eq_one_add {Ω : Type} [Field Ω] (M : ℕ) (hM : (M : Ω) ≠ 0) (s : Multiset Ω)
    (hs : ∀ l ∈ s, IsIntegral ℤ ((l - 1) / (M : Ω))) :
    ∃ z : Ω, IsIntegral ℤ z ∧ s.prod = 1 + M * z := by
  have hMint : IsIntegral ℤ (M : Ω) := by
    simpa using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ Ω (M : ℤ)))
  induction s using Multiset.induction_on with
  | empty => exact ⟨0, isIntegral_zero, by simp⟩
  | cons a s ih =>
    obtain ⟨z, hz, hprod⟩ := ih (fun l hl => hs l (Multiset.mem_cons_of_mem hl))
    have ha := hs a (Multiset.mem_cons_self a s)
    set w := (a - 1) / (M : Ω) with hw
    have ha' : a = 1 + M * w := by rw [hw]; field_simp; ring
    refine ⟨w + z + M * w * z, (ha.add hz).add ((hMint.mul ha).mul hz), ?_⟩
    rw [Multiset.prod_cons, hprod, ha']
    ring

theorem det_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r M : ℕ) (X : Data E r),
    3 ≤ M →
    (∀ γ, γ ∈ X.Γ ↔ IsUStab X.Gm X.Λ γ ∧ ∀ x ∈ X.Λ, ∃ y ∈ X.Λ,
      (γ : Matrix (Fin r) (Fin r) E) *ᵥ x - x = M • y) →
    ∀ γ ∈ X.Γ, (γ : Matrix (Fin r) (Fin r) E).det = 1 := by
  intro E _ _ _ r M X hM hΓ γ hγ
  classical
  obtain ⟨⟨hherm, -⟩, hcong⟩ := (hΓ γ).1 hγ
  set g : Matrix (Fin r) (Fin r) E := (γ : Matrix (Fin r) (Fin r) E) with hg
  let φ : E →+* AlgebraicClosure E := algebraMap E (AlgebraicClosure E)
  have hM0 : (M : AlgebraicClosure E) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  have hME : (M : E) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  set A : Matrix (Fin r) (Fin r) E := (M : E)⁻¹ • (g - 1) with hA
  have hAΛ : ∀ x ∈ X.Λ, A *ᵥ x ∈ X.Λ := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hcong x hx
    have : A *ᵥ x = y := by
      rw [hA, smul_mulVec, sub_mulVec, one_mulVec, hxy, ← Nat.cast_smul_eq_nsmul E,
        smul_smul, inv_mul_cancel₀ hME, one_smul]
    rw [this]; exact hy
  have hAmap : A.map φ = (M : AlgebraicClosure E)⁻¹ • (g.map φ - 1) := by
    ext i j
    by_cases hij : i = j <;> simp [hA, Matrix.one_apply, hij]
  have hroot : ∀ l ∈ (g.map φ).charpoly.roots, IsIntegral ℤ ((l - 1) / (M : AlgebraicClosure E)) := by
    intro l hl
    have hdet : (scalar (Fin r) l - g.map φ).det = 0 := by
      rw [← Matrix.eval_charpoly]; exact (mem_roots'.1 hl).2
    obtain ⟨u, hu, hu0⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hdet
    apply isIntegral_of_left_eigen A X.Λ X.Λ_fg X.Λ_span hAΛ _ u hu
    have hgu : u ᵥ* g.map φ = l • u := by
      rw [vecMul_sub, sub_eq_zero] at hu0
      rw [← hu0]
      funext j
      simp [scalar_apply, vecMul_diagonal, mul_comm]
    rw [hAmap, vecMul_smul, vecMul_sub, vecMul_one, hgu]
    funext j
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    field_simp
  obtain ⟨z, hz, hprod⟩ := prod_eq_one_add M hM0 _ hroot
  have hφdet : φ g.det = 1 + M * z := by
    rw [RingHom.map_det, ← hprod]
    exact Matrix.det_eq_prod_roots_charpoly _
  have hint : IsIntegral ℤ ((g.det - 1) / (M : E)) := by
    have h1 : φ ((g.det - 1) / (M : E)) = z := by
      rw [map_div₀, map_sub, map_one, map_natCast, hφdet]; field_simp; ring
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ E (AlgebraicClosure E))
      (algebraMap E (AlgebraicClosure E)).injective).1 (by change IsIntegral ℤ (φ _); rw [h1]; exact hz)
  have hc := det_mul_cc_det X.Gm g X.Gm_det hherm
  by_contra hne
  have hx : (⟨(g.det - 1) / M, hint⟩ : 𝓞 E) ≠ 0 := by
    intro h
    have : (g.det - 1) / (M : E) = 0 := congrArg Subtype.val h
    rcases div_eq_zero_iff.1 this with h | h
    · exact hne (sub_eq_zero.mp h)
    · exact hME h
  obtain ⟨σ, hσ⟩ := NumberField.exists_conjugate_one_le_norm hx
  have hσ' : 1 ≤ ‖σ ((g.det - 1) / M)‖ := hσ
  have h1 : ‖σ g.det‖ = 1 := by
    have := congrArg (fun z => ‖σ z‖) hc
    simp only [cc, map_mul, IsCMField.complexEmbedding_complexConj, norm_mul, map_one, norm_one,
      Complex.norm_conj] at this
    nlinarith [norm_nonneg (σ g.det)]
  rw [map_div₀, map_sub, map_one, map_natCast, norm_div, Complex.norm_natCast] at hσ'
  have hM3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have h2 : ‖σ g.det - 1‖ ≤ 2 := by
    have := norm_sub_le (σ g.det) 1
    rw [h1, norm_one] at this
    linarith
  rw [le_div_iff₀ (by linarith)] at hσ'
  linarith

end

end GlobalTheory.UnitaryCongruenceDet
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetEqOneUnitaryPrincipalCongruenceLevelThreeStatement
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_eq_one_unitary_principal_congruence_level_three : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r M : ℕ) (X : Data E r), 3 ≤ M → (∀ γ, γ ∈ X.Γ ↔ IsUStab X.Gm X.Λ γ ∧ ∀ x ∈ X.Λ, ∃ y ∈ X.Λ, (γ : Matrix (Fin r) (Fin r) E) *ᵥ x - x = M • y) → ∀ γ ∈ X.Γ, (γ : Matrix (Fin r) (Fin r) E).det = 1 := by
  first | exact @GlobalTheory.UnitaryCongruenceDet.det_eq_one | exact GlobalTheory.UnitaryCongruenceDet.det_eq_one | (intros; apply GlobalTheory.UnitaryCongruenceDet.det_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TC
noncomputable section

open GlobalTheory.LKTrip
open scoped TensorProduct

namespace GlobalTheory.TorCls

def TC (D : Type) [Ring D] [Algebra ℚ D] (σ : D →+* Dᵐᵒᵖ) (β y : D) (R : Type) [CommRing R] [Algebra ℚ R]
    (z : (R ⊗[ℚ] D)ˣ × Rˣ) : Prop :=
  (z.1 : R ⊗[ℚ] D) * ((1 : R) ⊗ₜ β) * (starT σ R (z.1 : R ⊗[ℚ] D)).unop =
      algebraMap R (R ⊗[ℚ] D) (z.2 : R) * ((1 : R) ⊗ₜ β) ∧
    Commute (z.1 : R ⊗[ℚ] D) ((1 : R) ⊗ₜ y)

end GlobalTheory.TorCls
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQCoeffIffHasQExpansion
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators

namespace GlobalTheory.QFam


open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
theorem _root_.GlobalTheory.QFam.hasQ_coeff_iff_hasQExpansion (N : ℕ) (f : ℍ → ℂ) (φ : PowerSeries ℂ) :
    _root_.GlobalTheory.QFam.HasQ N f (fun n => PowerSeries.coeff n φ) ↔
      _root_.GlobalTheory.HasQExpansion (N : ℝ) f φ := by
  rw [_root_.GlobalTheory.QFam.hasQ_iff]
  unfold _root_.GlobalTheory.HasQExpansion
  simp only [Function.Periodic.qParam, Complex.ofReal_natCast]

end GlobalTheory.QFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineSpaceSmoothNormal
open CategoryTheory AlgebraicGeometry

namespace GlobalTheory

theorem isIntegrallyClosed_stalk_spec_field (K : Type) [Field K] (x : Spec (.of K)) :
    IsIntegrallyClosed ((Spec (.of K)).presheaf.stalk x) := by
  have hU := isAffineOpen_top (Spec (.of K))
  letI := (Spec (.of K)).presheaf.algebra_section_stalk (⟨x, trivial⟩ : (⊤ : (Spec (.of K)).Opens))
  have h1 := hU.isLocalization_stalk ⟨x, trivial⟩
  have : IsIntegrallyClosed Γ(Spec (.of K), ⊤) :=
    IsIntegrallyClosed.of_equiv (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv
  exact (isDomain_and_isIntegrallyClosed_atPrime_of_isDomain (hU.primeIdealOf ⟨x, trivial⟩).asIdeal
    ((Spec (.of K)).presheaf.stalk x)).2

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumLogDivPredLeReal
open scoped BigOperators Matrix
open Polynomial

namespace GlobalTheory.PrimeLogSum


open scoped BigOperators Matrix in
open Polynomial in
theorem _root_.GlobalTheory.PrimeLogSum.sum_log_div_pred_le_real : ∀ (B : ℝ), 1 ≤ B →
    ∑ p ∈ (Finset.range (⌊B⌋₊ + 1)).filter Nat.Prime, Real.log p / ((p : ℝ) - 1)
      ≤ Real.log B + 3 := by
  intro B hB
  have h := _root_.GlobalTheory.PrimeLogSum.sum_log_div_pred_le ⌊B⌋₊
  have hN : (1 : ℝ) ≤ (⌊B⌋₊ : ℝ) := by
    have : 1 ≤ ⌊B⌋₊ := Nat.le_floor (by exact_mod_cast hB)
    exact_mod_cast this
  have hle : ((⌊B⌋₊ : ℕ) : ℝ) ≤ B := Nat.floor_le (by linarith)
  have hlog : Real.log (⌊B⌋₊ : ℝ) ≤ Real.log B :=
    Real.log_le_log (by linarith) hle
  linarith

end GlobalTheory.PrimeLogSum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedProjectorIdempotentOfGroupAlgebraIdem
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedProjectorIdempotentOfGroupAlgebraIdem
open NumberField

namespace GlobalTheory

theorem eOp_comp_self_of_conv_idem {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks]
    [Algebra Ks LL]
    {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
    [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL] [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL]
    {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
    {G0 : Type} [Group G0] [Fintype G0] (A : Formalism.IndefR.Arith.FormsL LL Ks WL W G0) (eC : G0 → LL)
    (he : ∀ k, ∑ g, eC g * eC (g⁻¹ * k) = eC k) : A.eOp eC ∘ₗ A.eOp eC = A.eOp eC := by
  set c : G0 → LL := fun g => eC g * ((A.chi g)⁻¹ : LLˣ) with hc
  have hchi : ∀ g k : G0, (((A.chi g)⁻¹ : LLˣ) : LL) * (((A.chi (g⁻¹ * k))⁻¹ : LLˣ) : LL)
      = (((A.chi k)⁻¹ : LLˣ) : LL) := by
    intro g k
    rw [← Units.val_mul, ← mul_inv, ← map_mul, mul_inv_cancel_left]
  have hcc : ∀ k, ∑ g, c g * c (g⁻¹ * k) = c k := by
    intro k
    calc ∑ g, c g * c (g⁻¹ * k)
        = ∑ g, (eC g * eC (g⁻¹ * k)) * (((A.chi k)⁻¹ : LLˣ) : LL) := by
          refine Finset.sum_congr rfl fun g _ => ?_
          rw [hc, ← hchi g k]; ring
      _ = c k := by rw [← Finset.sum_mul, he k]
  have hE : A.eOp eC = ∑ g, c g • A.ρ g := rfl
  rw [← Module.End.mul_eq_comp, hE, Finset.sum_mul_sum]
  calc ∑ g, ∑ h, (c g • A.ρ g) * (c h • A.ρ h)
      = ∑ g, ∑ k, (c g * c (g⁻¹ * k)) • A.ρ k := by
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [← Equiv.sum_comp (Equiv.mulLeft g) (fun k => (c g * c (g⁻¹ * k)) • A.ρ k)]
        refine Finset.sum_congr rfl fun h _ => ?_
        simp only [Equiv.coe_mulLeft, inv_mul_cancel_left, map_mul, smul_mul_smul_comm]
    _ = ∑ k, (∑ g, c g * c (g⁻¹ * k)) • A.ρ k := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_smul]
    _ = ∑ k, c k • A.ρ k := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hcc k]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedProjectorIdempotentOfGroupAlgebraIdemStatement
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedProjector_idempotent_of_groupAlgebra_idem : ∀ {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
    {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
    [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL] [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL]
    {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
    {G0 : Type} [Group G0] [Fintype G0] (A : Formalism.IndefR.Arith.FormsL LL Ks WL W G0) (eC : G0 → LL),
    (∀ k, ∑ g, eC g * eC (g⁻¹ * k) = eC k) → A.eOp eC ∘ₗ A.eOp eC = A.eOp eC := by
  first | exact @GlobalTheory.eOp_comp_self_of_conv_idem | exact GlobalTheory.eOp_comp_self_of_conv_idem | (intros; apply GlobalTheory.eOp_comp_self_of_conv_idem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableAbsNormInvSq
open MeasureTheory IsDedekindDomain NumberField

namespace GlobalTheory.PrimeSquareSum

theorem sum_inv_sq_le_one (t : Finset ℕ) (ht : ∀ n ∈ t, 2 ≤ n) :
    ∑ n ∈ t, ((n : ℝ) ^ 2)⁻¹ ≤ 1 := by
  have hs := hasSum_zeta_two
  have h1 : (1 : ℕ) ∉ t := fun h => by
    have := ht 1 h
    omega
  have hsum : ∑ n ∈ insert 1 t, ((n : ℝ) ^ 2)⁻¹ ≤ Real.pi ^ 2 / 6 := by
    rw [← hs.tsum_eq]
    have e : (fun n : ℕ => 1 / (n : ℝ) ^ 2) = fun n : ℕ => ((n : ℝ) ^ 2)⁻¹ := by
      funext n
      rw [one_div]
    rw [e]
    exact Summable.sum_le_tsum _ (fun _ _ => by positivity) (e ▸ hs.summable)
  rw [Finset.sum_insert h1] at hsum
  norm_num at hsum
  have hpi : Real.pi ^ 2 / 6 ≤ 2 := by
    have := Real.pi_lt_d2
    nlinarith [Real.pi_pos]
  linarith

theorem sum_absNorm_inv_sq_le (K : Type) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) :
    ∑ w ∈ s, (((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ 2)⁻¹ ≤ (Module.finrank ℚ K : ℝ) := by
  classical
  obtain ⟨c, hc⟩ := GlobalTheory.exists_colouring_maximal_ideals K
  have hp : ∀ w : HeightOneSpectrum (𝓞 K), ∃ p : ℕ, p.Prime ∧ (p : 𝓞 K) ∈ w.asIdeal ∧
      p ≤ Ideal.absNorm w.asIdeal := by
    intro w
    haveI := w.isMaximal
    obtain ⟨q, n, hn, hqP, hq, H⟩ := Ideal.exists_prime_and_absNorm_eq_pow w.asIdeal
    exact ⟨q, hq, hqP, H ▸ Nat.le_self_pow hn.ne' q⟩
  choose p hp hpm hple using hp
  rw [← Finset.sum_fiberwise s (fun w => c w.asIdeal)]
  calc _ ≤ ∑ _i : Fin (Module.finrank ℚ K), (1 : ℝ) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have hinj : Set.InjOn p (s.filter fun w => c w.asIdeal = i) := by
          intro v hv w hw h
          simp only [Finset.coe_filter, Set.mem_setOf_eq] at hv hw
          exact HeightOneSpectrum.ext (hc (p v) (hp v) _ _ v.isMaximal w.isMaximal (hpm v)
            (h ▸ hpm w) (hv.2.trans hw.2.symm))
        calc _ ≤ ∑ w ∈ s.filter (fun w => c w.asIdeal = i), ((p w : ℝ) ^ 2)⁻¹ := by
              refine Finset.sum_le_sum fun w _ => ?_
              have h0 : (0 : ℝ) < p w := by exact_mod_cast (hp w).pos
              have h1 : (p w : ℝ) ≤ (Ideal.absNorm w.asIdeal : ℕ) := by exact_mod_cast hple w
              gcongr
          _ = ∑ n ∈ (s.filter (fun w => c w.asIdeal = i)).image p, ((n : ℝ) ^ 2)⁻¹ :=
              (Finset.sum_image (f := fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) hinj).symm
          _ ≤ 1 := by
              refine sum_inv_sq_le_one _ fun n hn => ?_
              obtain ⟨w, -, rfl⟩ := Finset.mem_image.1 hn
              exact (hp w).two_le
    _ = _ := by simp

theorem summable_absNorm_inv_sq : ∀ (K : Type) [Field K] [NumberField K], Summable (fun w : HeightOneSpectrum (𝓞 K) => (((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ 2)⁻¹) ∧ ∑' w : HeightOneSpectrum (𝓞 K), (((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ 2)⁻¹ ≤ (Module.finrank ℚ K : ℝ) := by
  intro K _ _
  have hnn : 0 ≤ fun w : HeightOneSpectrum (𝓞 K) => (((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ 2)⁻¹ :=
    fun w => by positivity
  exact ⟨summable_of_sum_le hnn (sum_absNorm_inv_sq_le K),
    tsum_le_of_sum_le' (by positivity) (sum_absNorm_inv_sq_le K)⟩

end GlobalTheory.PrimeSquareSum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedProjectorOrthogonalOfUnitaryAction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedProjectorOrthogonalOfUnitaryAction
open NumberField

open scoped ComplexConjugate InnerProductSpace

namespace GlobalTheory

theorem twistedProjector_orthogonal_of_unitary : ∀ {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
    {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
    [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL] [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL]
    {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
    {G0 : Type} [Group G0] [Fintype G0] (A : Formalism.IndefR.Arith.FormsL LL Ks WL W G0) (eC : G0 → LL), ∀ σ : LL →+* ℂ, A.eOp eC ∘ₗ A.eOp eC = A.eOp eC →
    (∀ g x y, inner ℂ (A.j σ (A.ρ g x)) (A.j σ (A.ρ g y)) = inner ℂ (A.j σ x) (A.j σ y)) →
    (∀ g, σ (eC g⁻¹) = starRingEnd ℂ (σ (eC g))) →
    ∀ x y, ‖A.j σ (A.eOp eC x + (y - A.eOp eC y))‖ ^ 2 = ‖A.j σ (A.eOp eC x)‖ ^ 2 + ‖A.j σ (y - A.eOp eC y)‖ ^ 2 := by
  intro LL Ks _ _ _ _ _ WL _ _ _ _ _ _ _ _ W _ _ G0 _ _ A eC σ hid hu hc x y
  have hunit : ∀ g : G0, starRingEnd ℂ (σ ((A.chi g : LLˣ) : LL)) = (σ ((A.chi g : LLˣ) : LL))⁻¹ := by
    intro g
    set z := σ ((A.chi g : LLˣ) : LL)
    have hpow : z ^ orderOf g = 1 := by
      have h1 : A.chi g ^ orderOf g = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
      have h2 : ((A.chi g : LLˣ) : LL) ^ orderOf g = 1 := by
        rw [← Units.val_pow_eq_pow_val, h1, Units.val_one]
      simp only [z]; rw [← map_pow, h2, map_one]
    have hn : ‖z‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hpow (orderOf_pos g).ne'
    have hz : z ≠ 0 := by intro h; rw [h, norm_zero] at hn; exact zero_ne_one hn
    have hm : z * starRingEnd ℂ z = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]; simp
    exact eq_inv_of_mul_eq_one_right hm
  have key : ∀ g u v, ⟪A.j σ (A.ρ g u), A.j σ v⟫_ℂ = ⟪A.j σ u, A.j σ (A.ρ g⁻¹ v)⟫_ℂ := by
    intro g u v
    have h1 : A.ρ g (A.ρ g⁻¹ v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [← hu g u (A.ρ g⁻¹ v), h1]
  have sa : ∀ u v, ⟪A.j σ (A.eOp eC u), A.j σ v⟫_ℂ = ⟪A.j σ u, A.j σ (A.eOp eC v)⟫_ℂ := by
    intro u v
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Formalism.IndefR.Arith.FormsL.eOp_apply, map_sum, map_smulₛₗ, sum_inner, inner_sum,
      inner_smul_left, inner_smul_right]
    conv_rhs => rw [← Equiv.sum_comp (Equiv.inv G0)]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [key g, Equiv.inv_apply]
    congr 1
    rw [map_mul, map_mul, map_mul, hc, map_inv, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val,
      map_inv₀, map_inv₀, map_inv₀, hunit]
    simp only [Units.val_inv_eq_inv_val, map_inv₀, inv_inv]
  have horth : ⟪A.j σ (A.eOp eC x), A.j σ (y - A.eOp eC y)⟫_ℂ = 0 := by
    have hy : A.eOp eC (A.eOp eC y) = A.eOp eC y := LinearMap.congr_fun hid y
    rw [sa, map_sub, hy, sub_self, map_zero, inner_zero_right]
  rw [map_add (f := _)]
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
  simpa only [sq] using h

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedProjectorOrthogonalOfUnitaryActionStatement
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedProjector_orthogonal_of_unitary_action : ∀ {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
    {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
    [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL] [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL]
    {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
    {G0 : Type} [Group G0] [Fintype G0] (A : Formalism.IndefR.Arith.FormsL LL Ks WL W G0) (eC : G0 → LL), ∀ σ : LL →+* ℂ, A.eOp eC ∘ₗ A.eOp eC = A.eOp eC →
    (∀ g x y, inner ℂ (A.j σ (A.ρ g x)) (A.j σ (A.ρ g y)) = inner ℂ (A.j σ x) (A.j σ y)) →
    (∀ g, σ (eC g⁻¹) = starRingEnd ℂ (σ (eC g))) →
    ∀ x y, ‖A.j σ (A.eOp eC x + (y - A.eOp eC y))‖ ^ 2 = ‖A.j σ (A.eOp eC x)‖ ^ 2 + ‖A.j σ (y - A.eOp eC y)‖ ^ 2 := by
  first | exact @GlobalTheory.twistedProjector_orthogonal_of_unitary | exact GlobalTheory.twistedProjector_orthogonal_of_unitary | (intros; apply GlobalTheory.twistedProjector_orthogonal_of_unitary <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzDenseHasCompactSupport
open Filter Topology
open scoped ContDiff

namespace GlobalTheory

theorem schwartz_dense_hasCompactSupport :
    ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V],
    Dense {f : SchwartzMap V ℂ | HasCompactSupport (f : V → ℂ)} := by
  intro V _ _ _
  obtain ⟨χ, -, hχc, hχs, -, hχ0⟩ := exists_contDiff_tsupport_subset (n := ⊤) (Filter.univ_mem (f := 𝓝 (0 : V)))
  set L : ℝ → V →L[ℝ] V := fun r => r • ContinuousLinearMap.id ℝ V with hL
  have hLx : ∀ r x, L r x = r • x := fun r x => by simp [hL]
  have hLn : ∀ r, ‖L r‖ ≤ |r| := fun r => by
    refine (norm_smul_le _ _).trans ?_
    rw [Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg r) ContinuousLinearMap.norm_id_le
  set g : ℝ → V → ℂ := fun r => Complex.ofRealLI ∘ (χ ∘ L r) with hg
  have hgx : ∀ r x, g r x = ((χ (r • x) : ℝ) : ℂ) := fun r x => by simp [hg, hLx]
  have hχL : ∀ r, ContDiff ℝ ∞ (χ ∘ L r) := fun r => hχs.comp (L r).contDiff
  have hgs : ∀ r, ContDiff ℝ ∞ (g r) := fun r => Complex.ofRealLI.contDiff.comp (hχL r)
  have hM : ∀ i : ℕ, ∃ M, ∀ y, ‖iteratedFDeriv ℝ i χ y‖ ≤ M := fun i =>
    (hχs.continuous_iteratedFDeriv (mod_cast le_top)).bounded_above_of_compact_support
      (hχc.iteratedFDeriv i)
  choose M hM using hM
  have hgb : ∀ i : ℕ, ∀ r x, ‖iteratedFDeriv ℝ i (g r) x‖ ≤ M i * ‖L r‖ ^ i := by
    intro i r x
    rw [hg, Complex.ofRealLI.norm_iteratedFDeriv_comp_left (hχL r).contDiffAt (mod_cast le_top),
      ContinuousLinearMap.iteratedFDeriv_comp_right (L r) hχs x (mod_cast le_top)]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact mul_le_mul_of_nonneg_right (hM i _) (by positivity)
  have htg : ∀ r, (g r).HasTemperateGrowth := fun r =>
    ⟨hgs r, fun n => ⟨0, M n * ‖L r‖ ^ n, fun x => by simpa using hgb n r x⟩⟩
  intro f
  set F : ℝ → SchwartzMap V ℂ := fun r => SchwartzMap.smulLeftCLM ℂ (g r) f with hF
  have hFx : ∀ r, (F r : V → ℂ) = fun y => g r y * f y := fun r => by
    ext y; simp [hF, SchwartzMap.smulLeftCLM_apply_apply (htg r)]
  have hF0 : F 0 = f := by
    ext y; rw [hFx]; simp [hgx, hχ0]
  have hcont : ContinuousAt F 0 := by
    refine schwartz_continuousAt_of_pointwise_of_bounded F 0 (fun v => ?_) (fun k n => ?_)
    · simp only [hFx, hgx]
      exact ((Complex.continuous_ofReal.comp (hχs.continuous.comp
        (continuous_id.smul continuous_const))).mul continuous_const).continuousAt
    · refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * |M i| * SchwartzMap.seminorm ℂ k (n - i) f, ?_⟩
      filter_upwards [Metric.closedBall_mem_nhds (0 : ℝ) one_pos] with r hr v
      have hr1 : |r| ≤ 1 := by simpa [Real.dist_0_eq_abs] using hr
      rw [hFx]
      refine (mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_mul_le (N := ∞) (hgs r) (f.smooth ⊤) v
        (mod_cast le_top)) (by positivity)).trans ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      have h1 : ‖iteratedFDeriv ℝ i (g r) v‖ ≤ |M i| := by
        refine (hgb i r v).trans ?_
        refine (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)).trans ?_
        exact mul_le_of_le_one_right (abs_nonneg _)
          (pow_le_one₀ (norm_nonneg _) ((hLn r).trans hr1))
      have h2 := SchwartzMap.le_seminorm ℂ k (n - i) f v
      calc ‖v‖ ^ k * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (g r) v‖ * ‖iteratedFDeriv ℝ (n - i) (⇑f) v‖)
          = (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (g r) v‖ * (‖v‖ ^ k * ‖iteratedFDeriv ℝ (n - i) (⇑f) v‖) := by ring
        _ ≤ (n.choose i : ℝ) * |M i| * SchwartzMap.seminorm ℂ k (n - i) f :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1 (by positivity)) h2 (by positivity) (by positivity)
  have ht : Tendsto F (𝓝[≠] 0) (𝓝 f) := by
    rw [← hF0]; exact hcont.tendsto.mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto ht (eventually_nhdsWithin_of_forall fun r hr => ?_)
  have hr0 : r ≠ 0 := hr
  show HasCompactSupport (F r : V → ℂ)
  rw [hFx]
  have hgc : HasCompactSupport (g r) := by
    have : g r = fun x => ((χ (r • x) : ℝ) : ℂ) := funext (hgx r)
    rw [this]
    exact (hχc.comp_smul hr0).comp_left Complex.ofReal_zero
  exact hgc.mul_right

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardSmulTwistedProjectorMemIntegralForms
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardSmulTwistedProjectorMemIntegralForms
open NumberField

namespace GlobalTheory

open Formalism.IndefR.Arith

theorem card_smul_eOp_mem_Mall : ∀ {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
    {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
    [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL] [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL]
    {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
    {G0 : Type} [Group G0] [Fintype G0] (A : Formalism.IndefR.Arith.FormsL LL Ks WL W G0) (eC : G0 → LL),
    (∀ g h, eC (h * g * h⁻¹) = eC g) → (∀ g, IsIntegral ℤ ((Fintype.card G0 : LL) * eC g)) →
    (∀ g f, f ∈ A.MK → A.ρ g f ∈ A.MK) → ∀ (J0 : Subgroup G0) (lam0 : J0 →* LLˣ),
    ∀ x ∈ A.Mall J0 lam0, ((Fintype.card G0 : ℕ) : LL) • A.eOp eC x ∈ A.Mall J0 lam0 := by
  intro LL Ks _ _ _ _ _ WL _ _ _ _ _ _ _ _ W _ _ G0 _ _ A eC hcl hint hMK J0 lam0 x hx
  classical
  rw [FormsL.Mall, Submodule.mem_inf] at hx ⊢
  have hρspan : ∀ g, ∀ y ∈ Submodule.span (𝓞 LL) (A.MK : Set WL),
      A.ρ g y ∈ Submodule.span (𝓞 LL) (A.MK : Set WL) := by
    intro g y hy
    induction hy using Submodule.span_induction with
    | mem z hz => exact Submodule.subset_span (hMK g z hz)
    | zero => simp
    | add a b _ _ ha hb => rw [map_add (f := _)]; exact Submodule.add_mem _ ha hb
    | smul r a _ ha =>
        rw [← algebraMap_smul LL r a, LinearMap.map_smul, algebraMap_smul]
        exact Submodule.smul_mem _ r ha
  have hchi : ∀ g, IsIntegral ℤ (((A.chi g)⁻¹ : LLˣ) : LL) := by
    intro g
    have h1 : ((A.chi g)⁻¹) ^ (orderOf g) = 1 := by
      rw [← map_inv, ← map_pow, inv_pow, pow_orderOf_eq_one, inv_one, map_one]
    refine IsIntegral.of_pow (orderOf_pos g) ?_
    rw [← Units.val_pow_eq_pow_val, h1, Units.val_one]
    exact isIntegral_one
  have hchic : ∀ p g : G0, A.chi (p * g * p⁻¹) = A.chi g := by
    intro p g
    rw [map_mul, map_mul, map_inv, mul_right_comm, mul_inv_cancel, one_mul]
  constructor
  · rw [FormsL.eOp_apply, Finset.smul_sum]
    refine Submodule.sum_mem _ fun g _ => ?_
    rw [smul_smul]
    have hi : IsIntegral ℤ (((Fintype.card G0 : ℕ) : LL) * (eC g * ((A.chi g)⁻¹ : LLˣ))) := by
      rw [← mul_assoc]; exact (hint g).mul (hchi g)
    obtain ⟨r, hr⟩ : ∃ r : 𝓞 LL, algebraMap (𝓞 LL) LL r =
        ((Fintype.card G0 : ℕ) : LL) * (eC g * ((A.chi g)⁻¹ : LLˣ)) := ⟨⟨_, hi⟩, rfl⟩
    rw [← hr, algebraMap_smul]
    exact Submodule.smul_mem _ r (hρspan g x hx.1)
  · have hcomm : ∀ p : G0, A.ρ p (A.eOp eC x) = A.eOp eC (A.ρ p x) := by
      intro p
      set_option synthInstance.maxHeartbeats 100000 in
        rw [FormsL.eOp_apply, FormsL.eOp_apply, map_sum]
      simp only [LinearMap.map_smul]
      refine Fintype.sum_equiv (MulAut.conj p).toEquiv _ _ fun g => ?_
      simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply]
      rw [hcl g p, hchic p g, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
        inv_mul_cancel_right]
    intro p
    show A.ρ p (((Fintype.card G0 : ℕ) : LL) • A.eOp eC x) =
      ((A.chi p * lam0 p : LLˣ) : LL) • (((Fintype.card G0 : ℕ) : LL) • A.eOp eC x)
    rw [LinearMap.map_smul, hcomm, hx.2 p, LinearMap.map_smul, smul_comm]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardSmulTwistedProjectorMemIntegralFormsStatement
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_smul_twistedProjector_mem_integralForms : ∀ {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
    {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
    [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL] [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL]
    {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
    {G0 : Type} [Group G0] [Fintype G0] (A : Formalism.IndefR.Arith.FormsL LL Ks WL W G0) (eC : G0 → LL),
    (∀ g h, eC (h * g * h⁻¹) = eC g) → (∀ g, IsIntegral ℤ ((Fintype.card G0 : LL) * eC g)) →
    (∀ g f, f ∈ A.MK → A.ρ g f ∈ A.MK) → ∀ (J0 : Subgroup G0) (lam0 : J0 →* LLˣ),
    ∀ x ∈ A.Mall J0 lam0, ((Fintype.card G0 : ℕ) : LL) • A.eOp eC x ∈ A.Mall J0 lam0 := by
  first | exact @GlobalTheory.card_smul_eOp_mem_Mall | exact GlobalTheory.card_smul_eOp_mem_Mall | (intros; apply GlobalTheory.card_smul_eOp_mem_Mall <;> assumption)
end
end
