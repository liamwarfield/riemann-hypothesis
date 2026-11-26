module

public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMinorsMemInv

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SameBlockOfPosC
noncomputable section
namespace GlobalTheory.FockTensor
open Formalism.BasicNotions.TH Matrix

def sgnIx {p q : ℕ} : Ix p q → ℂ
  | .inl _ => 1
  | .inr _ => -1

theorem sgnIx_mul_self {p q : ℕ} (a : Ix p q) : sgnIx a * sgnIx a = 1 := by
  cases a <;> simp [sgnIx]

theorem star_sgnIx {p q : ℕ} (a : Ix p q) : star (sgnIx a) = sgnIx a := by
  cases a <;> simp [sgnIx]

theorem Jm_eq_diagonal (p q : ℕ) : Jm p q = Matrix.diagonal sgnIx := by
  unfold Jm Formalism.UG.Jpq
  ext (i | i) (j | j) <;> simp [sgnIx, Matrix.diagonal_apply, Matrix.one_apply] <;> split_ifs <;> simp

theorem adjZ_apply {p q : ℕ} (Z : Mat p q) (a b : Ix p q) :
    adjZ Z a b = sgnIx a * sgnIx b * star (Z b a) := by
  unfold adjZ
  rw [Jm_eq_diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply]
  ring

theorem adjZ_adjZ {p q : ℕ} (Z : Mat p q) : adjZ (adjZ Z) = Z := by
  ext a b
  rw [adjZ_apply, adjZ_apply, star_mul', star_mul', star_sgnIx, star_sgnIx, star_star]
  have ha := sgnIx_mul_self a
  have hb := sgnIx_mul_self b
  linear_combination (sgnIx b * sgnIx b * Z a b) * ha + Z a b * hb

theorem adjZ_add {p q : ℕ} (Y Z : Mat p q) : adjZ (Y + Z) = adjZ Y + adjZ Z := by
  ext a b
  simp only [adjZ_apply, Matrix.add_apply, star_add]
  ring

theorem adjZ_smul {p q : ℕ} (c : ℂ) (Z : Mat p q) : adjZ (c • Z) = star c • adjZ Z := by
  ext a b
  simp only [adjZ_apply, Matrix.smul_apply, smul_eq_mul, star_mul']
  ring

theorem adjZ_Eab {p q : ℕ} (a b : Ix p q) : adjZ (Eab a b) = (sgnIx a * sgnIx b) • Eab b a := by
  ext i j
  rw [adjZ_apply]
  simp only [Eab, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
  by_cases h : a = j ∧ b = i
  · obtain ⟨rfl, rfl⟩ := h
    rw [if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩, star_one]
    ring
  · have h' : ¬ (b = i ∧ a = j) := fun h'' => h ⟨h''.2, h''.1⟩
    rw [if_neg h, if_neg h', star_zero]
    ring

private theorem Jm_mul_JmRealPlaceTaylor (p q : ℕ) : Jm p q * Jm p q = 1 := by
  rw [Jm_eq_diagonal, Matrix.diagonal_mul_diagonal]
  have h : (fun a : Ix p q => sgnIx a * sgnIx a) = fun _ => 1 := funext sgnIx_mul_self
  rw [h, Matrix.diagonal_one]

theorem mem_upq_iff {p q : ℕ} (Z : Mat p q) : Z ∈ upq p q ↔ adjZ Z = -Z := by
  have hJ := Jm_mul_JmRealPlaceTaylor p q
  show Zᴴ * Jm p q + Jm p q * Z = 0 ↔ _
  unfold adjZ
  constructor
  · intro h
    have h2 : Jm p q * (Zᴴ * Jm p q + Jm p q * Z) = 0 := by rw [h, mul_zero]
    rw [mul_add, ← mul_assoc, ← mul_assoc, hJ, one_mul] at h2
    exact eq_neg_of_add_eq_zero_left h2
  · intro h
    have h2 : Jm p q * (Jm p q * Zᴴ * Jm p q) = Jm p q * (-Z) := by rw [h]
    rw [← mul_assoc, ← mul_assoc, hJ, one_mul, mul_neg] at h2
    rw [h2]
    abel

private theorem sameBlock_symm_twisted_operators {p q : ℕ} {a b : Ix p q} (h : sameBlock a b) : sameBlock b a := by
  cases a <;> cases b <;> exact h

theorem isKC_adjZ {p q : ℕ} {Z : Mat p q} (h : IsKC Z) : IsKC (adjZ Z) := by
  have h' : ∀ a b, ¬ sameBlock a b → Z a b = 0 := h
  intro a b hab
  have hba : ¬ sameBlock b a := fun hs => hab (sameBlock_symm_twisted_operators hs)
  rw [adjZ_apply, h' b a hba, star_zero, mul_zero]

theorem isKC_Eab {p q : ℕ} {a b : Ix p q} (h : sameBlock a b) : IsKC (Eab a b) := by
  intro i j hij
  simp only [Eab, Matrix.single_apply]
  rw [if_neg]
  rintro ⟨rfl, rfl⟩
  exact hij h

theorem sameBlock_self {p q : ℕ} (a : Ix p q) : sameBlock a a := by
  cases a <;> trivial

theorem sameBlock_of_posC {p q : ℕ} {a b : Ix p q} (h : posC a b) : sameBlock a b := by
  cases a <;> cases b <;> trivial

theorem exists_upq_add {p q : ℕ} (Z : Mat p q) :
    ∃ X ∈ upq p q, ∃ Y ∈ upq p q, Z = X + Complex.I • Y := by
  refine ⟨(1 / 2 : ℂ) • Z + (-1 / 2 : ℂ) • adjZ Z, ?_,
    (-Complex.I / 2) • Z + (-Complex.I / 2) • adjZ Z, ?_, ?_⟩
  · rw [mem_upq_iff, adjZ_add, adjZ_smul, adjZ_smul, adjZ_adjZ]
    have h1 : star (1 / 2 : ℂ) = 1 / 2 := by simp
    have h2 : star (-1 / 2 : ℂ) = -1 / 2 := by simp
    rw [h1, h2]
    module
  · rw [mem_upq_iff, adjZ_add, adjZ_smul, adjZ_smul, adjZ_adjZ]
    have h3 : star (-Complex.I / 2) = Complex.I / 2 := by simp
    rw [h3]
    module
  · rw [smul_add, smul_smul, smul_smul]
    have h4 : Complex.I * (-Complex.I / 2) = 1 / 2 := by
      ring_nf
      rw [Complex.I_sq]
      ring
    rw [h4]
    module

theorem hasDerivAt_orbit {p q : ℕ} {T : GrpData p q} (πU : URep T) {Y : Mat p q} (hY : Y ∈ upq p q)
    {x y : πU.H} (h : HasDerivAt (fun t : ℝ => πU.π (T.expt (t • Y)) x) y 0) (t : ℝ) :
    HasDerivAt (fun t : ℝ => πU.π (T.expt (t • Y)) x) (πU.π (T.expt (t • Y)) y) t := by
  have h0 : HasDerivAt (fun t : ℝ => πU.π (T.expt (t • Y)) x) y (t - t) := by
    rwa [sub_self]
  have h1 := HasDerivAt.comp_sub_const t t h0
  have h2 := ((πU.π (T.expt (t • Y))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h1
  simp only [ContinuousLinearMap.coe_restrictScalars'] at h2
  convert h2 using 1
  funext s
  have e : T.expt (s • Y) = T.expt (t • Y) * T.expt ((s - t) • Y) := by
    have hs : t + (s - t) = s := by ring
    rw [← T.expt_add Y hY, hs]
  simp only [Function.comp, e, map_mul]
  rfl

theorem inner_pi_pi {p q : ℕ} {T : GrpData p q} (πU : URep T) (g : T.G) (x y : πU.H) :
    inner ℂ (πU.π g x) (πU.π g y) = inner ℂ x y := by
  let e : πU.H →ₗᵢ[ℂ] πU.H := ⟨(πU.π g : πU.H →ₗ[ℂ] πU.H), πU.isom g⟩
  exact e.inner_map_map x y

theorem inner_pi_left {p q : ℕ} {T : GrpData p q} (πU : URep T) (g : T.G) (x y : πU.H) :
    inner ℂ (πU.π g x) y = inner ℂ x (πU.π g⁻¹ y) := by
  have e : πU.π g (πU.π g⁻¹ y) = y := by
    show (πU.π g * πU.π g⁻¹) y = y
    rw [← map_mul]
    simp
  have h := inner_pi_pi πU g x (πU.π g⁻¹ y)
  rwa [e] at h

end GlobalTheory.FockTensor
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralDetCharacterFockColumnSubstitutionEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralDetCharacterFockColumnSubstitutionEqZero
open Classical MeasureTheory

noncomputable section
namespace GlobalTheory.MinorFrame
open MvPolynomial

variable {ι : Type} [Fintype ι]

def scalAt {a : ℕ} (τ₀ : ι) (ζ : ℂ) : ι → Matrix (Fin a) (Fin a) ℂ := fun τ => if τ = τ₀ then ζ • 1 else 1

def degAt {d a : ℕ} (τ₀ : ι) (t : Var ι d a →₀ ℕ) : ℕ := t.sum fun y n => if y.1 = τ₀ then n else 0

theorem colSub_scalAt_X {d a : ℕ} (τ₀ : ι) (ζ : ℂ) (y : Var ι d a) :
    (∑ j' : Fin a, C (scalAt τ₀ ζ y.1 j' y.2.2) * (X (y.1, y.2.1, j') : Pol ι d a)) =
      C (if y.1 = τ₀ then ζ else 1) * X y := by
  obtain ⟨τ, i, j⟩ := y
  by_cases h : τ = τ₀
  · subst h
    rw [Finset.sum_eq_single j]
    · simp [scalAt, Matrix.smul_apply, Matrix.one_apply]
    · intro b _ hb
      simp [scalAt, Matrix.smul_apply, Matrix.one_apply, hb]
    · simp
  · simp [scalAt, h, Matrix.one_apply]

theorem colSub_scalAt_monomial {d a : ℕ} (τ₀ : ι) (ζ : ℂ) (t : Var ι d a →₀ ℕ) (c : ℂ) :
    colSub (scalAt τ₀ ζ) (monomial t c : Pol ι d a) = monomial t (c * ζ ^ degAt τ₀ t) := by
  unfold colSub
  rw [aeval_monomial]
  simp only [colSub_scalAt_X, mul_pow, Finsupp.prod_mul]
  have h1 : (t.prod fun y k => (C (if y.1 = τ₀ then ζ else 1) : Pol ι d a) ^ k) = C (ζ ^ degAt τ₀ t) := by
    unfold Finsupp.prod degAt Finsupp.sum
    rw [← Finset.prod_pow_eq_pow_sum, map_prod]
    refine Finset.prod_congr rfl fun y _ => ?_
    beta_reduce
    split_ifs <;> simp
  rw [h1, ← monomial_eq, algebraMap_eq, C_mul_monomial]

theorem degAt_le {d a : ℕ} (τ₀ : ι) (t : Var ι d a →₀ ℕ) : degAt τ₀ t ≤ t.sum fun _ e => e := by
  unfold degAt Finsupp.sum
  exact Finset.sum_le_sum fun y _ => by beta_reduce; split_ifs <;> omega

end GlobalTheory.MinorFrame

noncomputable section
namespace GlobalTheory.MinorFrame
open MvPolynomial

variable {ι : Type} [Fintype ι]

theorem colSub_mul {d a : ℕ} (A B : ι → Matrix (Fin a) (Fin a) ℂ) (P : Pol ι d a) :
    colSub (fun τ => A τ * B τ) P = colSub A (colSub B P) := by
  have : (colSub (fun τ => A τ * B τ) : Pol ι d a →ₐ[ℂ] Pol ι d a) = (colSub A).comp (colSub B) := by
    apply MvPolynomial.algHom_ext
    intro y
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [AlgHom.comp_apply, colSub, aeval_X, map_sum, map_mul, algHom_C, algebraMap_eq, Matrix.mul_apply,
      Finset.mul_sum, map_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    ring
  exact congrArg (fun φ : Pol ι d a →ₐ[ℂ] Pol ι d a => φ P) this

theorem sum_scalAt_eq_zero {d a : ℕ} (τ₀ : ι) (N : ℕ) (hN : 0 < N) (P : Pol ι d a) {ω : ℂ}
    (hω : IsPrimitiveRoot ω (N + P.totalDegree + 1)) :
    ∑ k ∈ Finset.range (N + P.totalDegree + 1), (ω ^ k) ^ N • colSub (scalAt τ₀ (ω ^ k)) P = 0 := by
  generalize hM : N + P.totalDegree + 1 = M at hω ⊢
  conv_lhs => rw [as_sum P]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, colSub_scalAt_monomial, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun t ht => ?_
  have hsum : ∑ k ∈ Finset.range M, (ω ^ (N + degAt τ₀ t)) ^ k = 0 := by
    have hne : ω ^ (N + degAt τ₀ t) ≠ 1 := by
      rw [Ne, hω.pow_eq_one_iff_dvd]
      intro hdvd
      have h1 := degAt_le τ₀ t
      have h2 := le_totalDegree ht
      have := Nat.le_of_dvd (by omega) hdvd
      omega
    rw [geom_sum_eq hne, ← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow, sub_self, zero_div]
  have : ∀ k ∈ Finset.range M,
      (ω ^ k) ^ N • (monomial t (AddMonoidAlgebra.coeff P t * (ω ^ k) ^ degAt τ₀ t) : Pol ι d a) =
        monomial t (AddMonoidAlgebra.coeff P t * (ω ^ (N + degAt τ₀ t)) ^ k) := by
    intro k _
    rw [smul_monomial, smul_eq_mul]
    congr 1
    rw [← pow_mul, ← pow_mul, ← pow_mul, show (N + degAt τ₀ t) * k = k * N + k * degAt τ₀ t by ring, pow_add]
    ring
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.sum_congr rfl this, ← map_sum, ← Finset.mul_sum, hsum, mul_zero, map_zero]

end GlobalTheory.MinorFrame

noncomputable section
namespace GlobalTheory.MinorFrame
open MvPolynomial

theorem prod_det_scalAt_zpow {ι : Type} [Fintype ι] {a : ℕ} (τ₀ : ι) (ζ : ℂ) (m : ι → ℤ) (n : ℕ)
    (hn : (n : ℤ) = m τ₀) : (∏ τ, (scalAt (a := a) τ₀ ζ τ).det ^ (m τ)) = ζ ^ (a * n) := by
  rw [Finset.prod_eq_single τ₀]
  · simp [scalAt, Matrix.det_smul, ← hn, zpow_natCast, pow_mul]
  · intro τ _ h
    simp [scalAt, h]
  · simp

theorem integral_detZpow_colSub_eq_zero :
    ∀ {ι : Type} [Fintype ι] (a d : ℕ) (m : ι → ℤ) (τ₀ : ι), 0 < a → 0 < m τ₀ → ∀ {K : Type} [Group K]
      [MeasurableSpace K] (ν : Measure K), IsProbabilityMeasure ν → ν.IsMulLeftInvariant →
    (∀ u : K, AEMeasurable (fun x => u * x) ν) →
    ∀ (ρ : K →* (ι → Matrix.unitaryGroup (Fin a) ℂ)),
      (∀ τ i j, Measurable fun g => (ρ g τ : Matrix (Fin a) (Fin a) ℂ) i j) →
      Function.Surjective ρ →
    ∀ (Λ : GlobalTheory.MinorFrame.Pol ι d a →ₗ[ℂ] ℂ) (P : GlobalTheory.MinorFrame.Pol ι d a),
      ∫ g, (∏ τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det ^ (m τ)) *
        Λ (GlobalTheory.MinorFrame.colSub (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ)) P) ∂ν = 0 := by
  intro ι _ a d m τ₀ ha hm K _ _ ν hν hinv hmeas ρ _ hρ Λ P
  set B : K → ι → Matrix (Fin a) (Fin a) ℂ := fun g τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ) with hB_def
  set c : K → ℂ := fun g => ∏ τ, (B g τ).det ^ (m τ) with hc_def
  set f : K → ℂ := fun g => c g * Λ (colSub (B g) P) with hf_def
  show ∫ g, f g ∂ν = 0
  by_cases hint : Integrable f ν
  swap
  · exact integral_undef hint

  have hinvar : ∀ u : K, Integrable (fun x => f (u * x)) ν ∧ ∫ x, f (u * x) ∂ν = ∫ x, f x ∂ν := by
    intro u
    have hmap : Measure.map (fun x => u * x) ν = ν := map_mul_left_eq_self ν u
    have hae : AEMeasurable (fun x => u * x) ν := hmeas u
    refine ⟨?_, ?_⟩
    · have : Integrable f (Measure.map (fun x => u * x) ν) := by rw [hmap]; exact hint
      exact this.comp_aemeasurable hae
    · have h := integral_map hae (f := f) (by rw [hmap]; exact hint.aestronglyMeasurable)
      rw [hmap] at h
      exact h.symm

  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = m τ₀ := ⟨(m τ₀).toNat, Int.toNat_of_nonneg hm.le⟩
  have hnpos : 0 < n := by omega
  set N := a * n with hN_def
  have hN : 0 < N := Nat.mul_pos ha hnpos
  set M := N + P.totalDegree + 1 with hM_def
  have hM0 : M ≠ 0 := by omega
  set ω := Complex.exp (2 * Real.pi * Complex.I / M) with hω_def
  have hω : IsPrimitiveRoot ω M := Complex.isPrimitiveRoot_exp M hM0
  have hmemU : ∀ k : ℕ, ((ω ^ k) • (1 : Matrix (Fin a) (Fin a) ℂ)) ∈ Matrix.unitaryGroup (Fin a) ℂ := by
    intro k
    have hnorm : ‖ω ^ k‖ = 1 := by rw [norm_pow, hω.norm'_eq_one hM0, one_pow]
    have hc : ω ^ k * star (ω ^ k) = 1 := by
      rw [RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]; norm_num
    rw [Matrix.mem_unitaryGroup_iff, star_smul, star_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul,
      hc, one_smul]
  let U : ℕ → ι → Matrix.unitaryGroup (Fin a) ℂ := fun k τ => if τ = τ₀ then ⟨(ω ^ k) • 1, hmemU k⟩ else 1
  have hU : ∀ k τ, (U k τ : Matrix (Fin a) (Fin a) ℂ) = scalAt τ₀ (ω ^ k) τ := by
    intro k τ
    simp only [U, scalAt]
    split_ifs <;> rfl
  choose u hu using fun k => hρ (U k)

  have hpt : ∀ k g, f (u k * g) = c g * Λ ((ω ^ k) ^ N • colSub (B g) (colSub (scalAt τ₀ (ω ^ k)) P)) := by
    intro k g
    have hBu : B (u k * g) = fun τ => B g τ * scalAt τ₀ (ω ^ k) τ := by
      funext τ
      simp only [hB_def, map_mul, Pi.mul_apply, hu k]
      rw [Submonoid.coe_mul, hU k τ]
      simp only [scalAt]
      split_ifs <;> simp [Matrix.smul_mul, Matrix.mul_smul]
    simp only [hf_def, hc_def]
    rw [hBu, colSub_mul, map_smul, smul_eq_mul]
    simp only [Matrix.det_mul, mul_zpow, Finset.prod_mul_distrib]
    rw [prod_det_scalAt_zpow τ₀ (ω ^ k) m n hn]
    ring
  have hsum0 : ∀ g, ∑ k ∈ Finset.range M, f (u k * g) = 0 := by
    intro g
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hpt, ← Finset.mul_sum, ← map_sum]
    have : ∑ k ∈ Finset.range M, (ω ^ k) ^ N • colSub (B g) (colSub (scalAt τ₀ (ω ^ k)) P) =
        colSub (B g) (∑ k ∈ Finset.range M, (ω ^ k) ^ N • colSub (scalAt τ₀ (ω ^ k)) P) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]; simp only [map_smul]
    rw [this, sum_scalAt_eq_zero τ₀ N hN P hω, map_zero, map_zero, mul_zero]
  have hkey : (M : ℂ) * ∫ x, f x ∂ν = 0 := by
    calc (M : ℂ) * ∫ x, f x ∂ν = ∑ k ∈ Finset.range M, ∫ x, f (u k * x) ∂ν := by
          rw [Finset.sum_congr rfl fun k _ => (hinvar (u k)).2, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = ∫ x, ∑ k ∈ Finset.range M, f (u k * x) ∂ν :=
          (MeasureTheory.integral_finsetSum _ fun k _ => (hinvar (u k)).1).symm
      _ = 0 := by simp [hsum0]
  exact (mul_eq_zero.1 hkey).resolve_left (by exact_mod_cast hM0)

end GlobalTheory.MinorFrame
end
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralDetCharacterFockColumnSubstitutionEqZeroStatement
open Classical MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_detCharacter_fockColumnSubstitution_eq_zero : ∀ {ι : Type} [Fintype ι] (a d : ℕ) (m : ι → ℤ) (τ₀ : ι), 0 < a → 0 < m τ₀ → ∀ {K : Type} [Group K] [MeasurableSpace K] (ν : Measure K), IsProbabilityMeasure ν → ν.IsMulLeftInvariant →
  (∀ g0 : K, AEMeasurable (g0 * ·) ν) →
  ∀ (ρ : K →* (ι → Matrix.unitaryGroup (Fin a) ℂ)), (∀ τ i j, Measurable fun g => (ρ g τ : Matrix (Fin a) (Fin a) ℂ) i j) →
    Function.Surjective ρ →
  ∀ (Λ : GlobalTheory.MinorFrame.Pol ι d a →ₗ[ℂ] ℂ) (P : GlobalTheory.MinorFrame.Pol ι d a),
    ∫ g, (∏ τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det ^ (m τ)) *
      Λ (GlobalTheory.MinorFrame.colSub (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ)) P) ∂ν = 0 := by
  first | exact @GlobalTheory.MinorFrame.integral_detZpow_colSub_eq_zero | exact GlobalTheory.MinorFrame.integral_detZpow_colSub_eq_zero | (intros; apply GlobalTheory.MinorFrame.integral_detZpow_colSub_eq_zero <;> assumption)
end
end
