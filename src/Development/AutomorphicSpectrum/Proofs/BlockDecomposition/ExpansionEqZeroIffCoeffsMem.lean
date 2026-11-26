module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPrimitiveCl
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerQuotientExists

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExpansionEqZeroIffCoeffsMem
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExpansionEqZeroIffCoeffsMem
set_option backward.isDefEq.respectTransparency false

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.ExpandKer

variable {l : ℕ} [Fact l.Prime] (A : PAlg l)

theorem dxi_mul (i j : ℕ) :
    A.dxi 1 i * A.dxi 1 j = ((i + j).choose i : A.Acr 1) * A.dxi 1 (i + j) := by
  obtain ⟨-, hmul, -⟩ := GlobalTheory.T.crystalline_filtration_multiplicative A
  change A.mkAcr 1 (A.dxi0 i) * A.mkAcr 1 (A.dxi0 j)
    = ((i + j).choose i : A.Acr 1) * A.mkAcr 1 (A.dxi0 (i + j))
  rw [← map_mul, hmul, map_mul, map_natCast]

theorem aTo1_pi : A.aTo1 A.pi = -A.dxi 1 1 := by
  obtain ⟨-, -, hfac, -⟩ := GlobalTheory.T.crystalline_filtration_multiplicative A
  have h1 : A.dxi0 1 = algebraMap A.W A.Acr0 A.xi := by
    simpa using hfac 1
  have h2 : A.dxi 1 1 = A.toAcr 1 A.xi := by
    change A.mkAcr 1 (A.dxi0 1) = A.mkAcr 1 (algebraMap A.W A.Acr0 A.xi)
    rw [h1]
  rw [h2, ← A.aTo1_coeff, A.xi_coeff_zero, map_neg, neg_neg]

theorem toAcr_teichmuller (b : A.A) : A.toAcr 1 (WittVector.teichmuller l b) = A.aTo1 b := by
  rw [← A.aTo1_coeff, WittVector.teichmuller_coeff_zero]

theorem exists_coprime {m : ℕ} (hm : l ∣ m) {j : ℕ} (hj : j < l) :
    ∃ c : ℕ, c.Coprime l ∧ A.dxi 1 1 ^ j * A.dxi 1 m = (c : A.Acr 1) * A.dxi 1 (m + j) := by
  have hp : l.Prime := Fact.out
  induction j with
  | zero => exact ⟨1, Nat.coprime_one_left l, by simp⟩
  | succ j ih =>
    obtain ⟨c, hc, hcj⟩ := ih (Nat.lt_of_succ_lt hj)
    have hnd : ¬ l ∣ m + j + 1 := by
      intro h
      have h2 : l ∣ j + 1 := by
        rw [Nat.add_assoc] at h
        exact (Nat.dvd_add_right hm).mp h
      have := Nat.le_of_dvd (Nat.succ_pos j) h2
      omega
    refine ⟨c * (m + j + 1), Nat.Coprime.mul_left hc ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnd).symm, ?_⟩
    rw [pow_succ', mul_assoc, hcj, mul_left_comm, dxi_mul A 1 (m + j), Nat.choose_one_right]
    have e : 1 + (m + j) = m + (j + 1) := by omega
    rw [e]
    push_cast
    ring

theorem mem_of_coprime_mul {I : Ideal (A.Acr 1)} {c : ℕ} (hc : c.Coprime l) {x : A.Acr 1}
    (h : (c : A.Acr 1) * x ∈ I) : x ∈ I := by
  have hl : ((l : ℕ) : A.Acr 1) = 0 := by
    have e : ((l : ℕ) : A.Acr 1) = A.toAcr 1 (l : A.W) := by rw [map_natCast]
    rw [e]
    change Ideal.Quotient.mk _ (algebraMap A.W A.Acr0 (l : A.W)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact Ideal.subset_span (by simp)
  have h1 : (1 : A.Acr 1) = (c : A.Acr 1) * (Nat.gcdA c l : A.Acr 1)
      + (l : A.Acr 1) * (Nat.gcdB c l : A.Acr 1) := by
    have h' := Nat.gcd_eq_gcd_ab c l
    rw [Nat.Coprime.gcd_eq_one hc, Nat.cast_one] at h'
    have h'' := congrArg (fun z : ℤ => (z : A.Acr 1)) h'
    push_cast at h''
    exact h''
  have hx : x = (Nat.gcdA c l : A.Acr 1) * ((c : A.Acr 1) * x) := by
    calc x = (1 : A.Acr 1) * x := (one_mul x).symm
      _ = _ := by rw [h1, hl]; ring
  rw [hx]
  exact I.mul_mem_left _ h

theorem inner_step (k : ℕ) {j : ℕ} (hj : j < l) (b : A.A)
    (h : A.aTo1 (A.pi ^ j * b) * A.dxi 1 (l * k) ∈ A.Fil 1 (l * k + j + 1)) :
    b ∈ Ideal.span {A.pi} := by
  obtain ⟨c, hc, hcj⟩ := exists_coprime A (dvd_mul_right l k) hj
  have hx : A.aTo1 b * A.dxi 1 (l * k + j) ∈ A.Fil 1 (l * k + j + 1) := by
    have e : A.aTo1 (A.pi ^ j * b) * A.dxi 1 (l * k)
        = (c : A.Acr 1) * ((-1) ^ j * (A.aTo1 b * A.dxi 1 (l * k + j))) := by
      rw [map_mul, map_pow, aTo1_pi A]
      calc (-A.dxi 1 1) ^ j * A.aTo1 b * A.dxi 1 (l * k)
          = (-1) ^ j * A.aTo1 b * (A.dxi 1 1 ^ j * A.dxi 1 (l * k)) := by ring
        _ = _ := by rw [hcj]; ring
    rw [e] at h
    have h2 := mem_of_coprime_mul A hc h
    have h3 : (-1 : A.Acr 1) ^ j * ((-1) ^ j * (A.aTo1 b * A.dxi 1 (l * k + j)))
        ∈ A.Fil 1 (l * k + j + 1) := Ideal.mul_mem_left _ _ h2
    have h4 : (-1 : A.Acr 1) ^ j * ((-1) ^ j * (A.aTo1 b * A.dxi 1 (l * k + j)))
        = A.aTo1 b * A.dxi 1 (l * k + j) := by
      rw [← mul_assoc, ← mul_pow]
      simp
    rwa [h4] at h3
  rw [← toAcr_teichmuller A b] at hx
  have hth := ((GlobalTheory.T.graded_filtration_generated_by_dividedXi A 1 (l * k + j)).2 (WittVector.teichmuller l b)).mp hx
  have hz : A.aToU1 b = 0 := by
    have e := A.sharpMap_coeff (WittVector.teichmuller l b)
    rw [WittVector.teichmuller_coeff_zero] at e
    rw [e, Ideal.Quotient.eq_zero_iff_mem]
    exact hth
  obtain ⟨-, hker⟩ := GlobalTheory.CompanionTheory.Untilt.sharp_map_surjective_ker A
  rw [← hker]
  exact RingHom.mem_ker.mpr hz

theorem term_eq_zero {a : A.A} (h : a ∈ Ideal.span {A.pi ^ l}) (m : ℕ) :
    A.aTo1 a * A.dxi 1 m = 0 := by
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp h
  obtain ⟨-, -, -, h4⟩ := GlobalTheory.T.expansion_surjective_additive_linear A
  rw [map_mul, mul_assoc, h4, mul_zero]

theorem term_mem (c : ℕ →₀ A.A) (h0 : A.expand c = 0) (k : ℕ)
    (hk : ∀ i < k, c i ∈ Ideal.span {A.pi ^ l}) :
    A.aTo1 (c k) * A.dxi 1 (l * k) ∈ A.Fil 1 (l * k + l) := by
  obtain ⟨-, hadd, -, -⟩ := GlobalTheory.T.expansion_surjective_additive_linear A
  obtain ⟨-, -, -, -, hmap, -⟩ := GlobalTheory.T.crystalline_filtration_multiplicative A
  have hdx : ∀ m, A.dxi 1 m ∈ A.Fil 1 m := fun m => by
    rw [hmap]
    change A.mkAcr 1 (A.dxi0 m) ∈ _
    apply Ideal.mem_map_of_mem
    unfold CrystallineSemistableComparison.PAlg.Fil0
    exact Ideal.subset_span ⟨m, le_rfl, rfl⟩
  have hanti : ∀ r s : ℕ, r ≤ s → A.Fil 1 s ≤ A.Fil 1 r := by
    intro r s hrs
    rw [hmap, hmap]
    apply Ideal.map_mono
    unfold CrystallineSemistableComparison.PAlg.Fil0
    apply Ideal.span_mono
    rintro z ⟨i, hi, rfl⟩
    exact ⟨i, le_trans hrs hi, rfl⟩
  have hsingle : A.expand (Finsupp.single k (c k)) = A.aTo1 (c k) * A.dxi 1 (l * k) := by
    unfold CrystallineSemistableComparison.PAlg.expand
    rw [Finsupp.sum_single_index]
    simp
  have herase : A.expand (c.erase k) ∈ A.Fil 1 (l * k + l) := by
    unfold CrystallineSemistableComparison.PAlg.expand
    rw [Finsupp.sum]
    apply Ideal.sum_mem
    intro i hi
    have hik : i ≠ k := by
      rintro rfl
      simp at hi
    rw [Finsupp.erase_ne hik]
    rcases lt_or_gt_of_ne hik with hlt | hgt
    · rw [term_eq_zero A (hk i hlt)]
      exact Ideal.zero_mem _
    · apply Ideal.mul_mem_left
      refine hanti _ _ ?_ (hdx (l * i))
      calc l * k + l = l * (k + 1) := by ring
        _ ≤ l * i := Nat.mul_le_mul (le_refl l) hgt
  have hsplit := hadd (Finsupp.single k (c k)) (c.erase k)
  rw [Finsupp.single_add_erase, h0, hsingle] at hsplit
  have e : A.aTo1 (c k) * A.dxi 1 (l * k) = -A.expand (c.erase k) := by
    rw [eq_neg_iff_add_eq_zero]
    exact hsplit.symm
  rw [e]
  exact (Ideal.neg_mem_iff _).mpr herase

theorem fil_anti {r s : ℕ} (h : r ≤ s) : A.Fil 1 s ≤ A.Fil 1 r := by
  obtain ⟨-, -, -, -, hmap, -⟩ := GlobalTheory.T.crystalline_filtration_multiplicative A
  rw [hmap, hmap]
  apply Ideal.map_mono
  unfold CrystallineSemistableComparison.PAlg.Fil0
  apply Ideal.span_mono
  rintro z ⟨i, hi, rfl⟩
  exact ⟨i, le_trans h hi, rfl⟩

theorem coeff_mem (c : ℕ →₀ A.A) (h0 : A.expand c = 0) (k : ℕ)
    (hk : ∀ i < k, c i ∈ Ideal.span {A.pi ^ l}) : c k ∈ Ideal.span {A.pi ^ l} := by
  have hT := term_mem A c h0 k hk
  have key : ∀ j, j ≤ l → c k ∈ Ideal.span {A.pi ^ j} := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp (ih (Nat.le_of_succ_le hj))
      have h1 : A.aTo1 (A.pi ^ j * b) * A.dxi 1 (l * k) ∈ A.Fil 1 (l * k + j + 1) := by
        rw [mul_comm (A.pi ^ j) b, hb]
        exact fil_anti A (by omega) hT
      obtain ⟨b', hb'⟩ := Ideal.mem_span_singleton'.mp (inner_step A k (Nat.lt_of_succ_le hj) b h1)
      rw [← hb, ← hb', pow_succ]
      exact Ideal.mem_span_singleton'.mpr ⟨b', by ring⟩
  exact key l le_rfl

theorem expand_eq_zero_iff : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (c : ℕ →₀ A.A),
    A.expand c = 0 ↔ ∀ k, c k ∈ Ideal.span {A.pi ^ l} := by
  intro l _ A c
  constructor
  · intro h0 k
    refine Nat.strong_induction_on k ?_
    intro k ih
    exact coeff_mem A c h0 k ih
  · intro h
    unfold CrystallineSemistableComparison.PAlg.expand
    rw [Finsupp.sum]
    apply Finset.sum_eq_zero
    intro i _
    exact term_eq_zero A (h i) _

end GlobalTheory.CompanionTheory.ExpandKer
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExpansionEqZeroIffCoeffsMemStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.expansion_eq_zero_iff_coeffs_mem : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (c : ℕ →₀ A.A), A.expand c = 0 ↔ ∀ k, c k ∈ Ideal.span {A.pi ^ l} := by
  first | exact @GlobalTheory.CompanionTheory.ExpandKer.expand_eq_zero_iff | exact GlobalTheory.CompanionTheory.ExpandKer.expand_eq_zero_iff | (intros; apply GlobalTheory.CompanionTheory.ExpandKer.expand_eq_zero_iff <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicStabilizerBlockUnit
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicStabilizerBlockUnit
open Matrix Topology Filter

noncomputable section

namespace GlobalTheory.CompanionTheory.LieStable

open scoped Matrix.Norms.Operator

variable {n : ℕ}

theorem hasDerivAt_conj_curve (X Y : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp (s • X) * Y * NormedSpace.exp (s • (-X)))
      (X * Y - Y * X) 0 := by
  have h₁ := hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0
  have h₂ := hasDerivAt_exp_smul_const (𝕂 := ℝ) (-X) 0
  have h : HasDerivAt (fun s : ℝ => NormedSpace.exp (s • X) * Y * NormedSpace.exp (s • (-X)))
      (NormedSpace.exp ((0 : ℝ) • X) * X * Y * NormedSpace.exp ((0 : ℝ) • (-X)) +
        NormedSpace.exp ((0 : ℝ) • X) * Y * (NormedSpace.exp ((0 : ℝ) • (-X)) * -X)) 0 :=
    (h₁.mul_const Y).fun_mul h₂
  refine h.congr_deriv ?_
  simp only [zero_smul, NormedSpace.exp_zero, one_mul, mul_one, mul_neg, sub_eq_add_neg]

theorem conj_mem {G : Set (Matrix (Fin n) (Fin n) ℂ)} (hG : GlobalTheory.LinRed.IsLinRed G)
    {𝔤 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)}
    (h𝔤 : ∀ X, X ∈ 𝔤 ↔ ∀ t : ℝ, NormedSpace.exp (t • X) ∈ G)
    {g Y : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ G) (hY : Y ∈ 𝔤) : g * Y * g⁻¹ ∈ 𝔤 := by
  obtain ⟨-, hmul, hunit, hinv, -, -, -⟩ := hG
  rw [h𝔤] at hY ⊢
  intro t
  have hconj : t • (g * Y * g⁻¹) = g * (t • Y) * g⁻¹ := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [hconj, Matrix.exp_conj g (t • Y) (hunit g hg)]
  exact hmul _ (hmul _ hg _ (hY t)) _ (hinv g hg)

theorem lieAlg_stable : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)}, GlobalTheory.LinRed.IsLinRed G →
    ∀ 𝔤 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ),
      (∀ X, X ∈ 𝔤 ↔ ∀ t : ℝ, NormedSpace.exp (t • X) ∈ G) →
      (∀ X ∈ 𝔤, Xᴴ ∈ 𝔤) ∧ ∀ X ∈ 𝔤, ∀ Y ∈ 𝔤, X * Y - Y * X ∈ 𝔤 := by
  intro n G hG 𝔤 h𝔤
  have hexp : ∀ X ∈ 𝔤, ∀ t : ℝ, NormedSpace.exp (t • X) ∈ G := fun X hX => (h𝔤 X).1 hX
  refine ⟨fun X hX => ?_, fun X hX Y hY => ?_⟩
  · obtain ⟨-, -, -, -, -, -, hstar⟩ := hG
    refine (h𝔤 _).2 fun t => ?_
    have ht : t • Xᴴ = (t • X)ᴴ := by
      rw [Matrix.conjTranspose_smul, star_trivial]
    rw [ht, Matrix.exp_conjTranspose]
    exact hstar _ (hexp X hX t)
  · have hmem : ∀ s : ℝ,
        NormedSpace.exp (s • X) * Y * NormedSpace.exp (s • (-X)) ∈ 𝔤 := by
      intro s
      rw [smul_neg, Matrix.exp_neg]
      exact GlobalTheory.CompanionTheory.LieStable.conj_mem hG h𝔤 (hexp X hX s) hY
    have hd := hasDerivAt_iff_tendsto_slope.1 (GlobalTheory.CompanionTheory.LieStable.hasDerivAt_conj_curve X Y)
    refine (Submodule.closed_of_finiteDimensional 𝔤).mem_of_tendsto hd
      (Filter.Eventually.of_forall fun s => ?_)
    rw [slope_def_module]
    exact 𝔤.smul_mem _ (𝔤.sub_mem (hmem s) (hmem 0))

end GlobalTheory.CompanionTheory.LieStable

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicStabilizerBlockUnitStatement
open Matrix Topology Filter
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_algebra_star_closed_bracket : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)}, GlobalTheory.LinRed.IsLinRed G → ∀ 𝔤 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ), (∀ X, X ∈ 𝔤 ↔ ∀ t : ℝ, NormedSpace.exp (t • X) ∈ G) → (∀ X ∈ 𝔤, Xᴴ ∈ 𝔤) ∧ ∀ X ∈ 𝔤, ∀ Y ∈ 𝔤, X * Y - Y * X ∈ 𝔤 := by
  first | exact @GlobalTheory.CompanionTheory.LieStable.lieAlg_stable | exact GlobalTheory.CompanionTheory.LieStable.lieAlg_stable | (intros; apply GlobalTheory.CompanionTheory.LieStable.lieAlg_stable <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsNormTheta2TailLeOfLeOne
open NumberField Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing SchwartzMap ContDiff
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Adele2 GroundTheory.Automorphic.GodementSection IdeleGroup

namespace GlobalTheory.CompanionTheory.EisRk1

section Majorant

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_iteratedFDeriv_dilate_le (f : 𝓢(E, ℝ)) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (n : ℕ)
    (x : E) :
    ‖iteratedFDeriv ℝ n (fun y ↦ f (a • y)) x‖ ≤ ‖iteratedFDeriv ℝ n f (a • x)‖ := by
  have hg : (fun y ↦ f (a • y)) = f ∘ (a • ContinuousLinearMap.id ℝ E) := rfl
  have hle : ‖a • ContinuousLinearMap.id ℝ E‖ ≤ 1 := by
    refine (norm_smul_le _ _).trans ?_
    rw [Real.norm_of_nonneg ha0]
    exact mul_le_one₀ ha1 (norm_nonneg _) ContinuousLinearMap.norm_id_le
  rw [hg, ContinuousLinearMap.iteratedFDeriv_comp_right _ (f.smooth ⊤) x
    (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  refine mul_le_of_le_one_right (norm_nonneg _) ?_
  exact Finset.prod_le_one₀ (fun _ _ ↦ norm_nonneg _) fun _ _ ↦ hle

theorem exists_schwartz_majorant [FiniteDimensional ℝ E] (φ : 𝓢(E, ℂ)) :
    ∃ Φ : 𝓢(E, ℂ), ∃ r : E → ℝ, (∀ y, Φ y = (r y : ℂ)) ∧ ∀ y, ‖φ y‖ ≤ r y := by
  let b : ContDiffBump (0 : E) := ⟨1, 2, one_pos, by norm_num⟩
  let χ : 𝓢(E, ℝ) := b.hasCompactSupport.toSchwartzMap b.contDiff
  have hχ0 : ∀ y, 0 ≤ χ y := fun y ↦ b.nonneg
  have hχ1 : ∀ y, χ y ≤ 1 := fun y ↦ b.le_one
  have hχb : ∀ y, ‖y‖ ≤ 1 → χ y = 1 := fun y hy ↦
    b.one_of_mem_closedBall (by simpa [b] using hy)
  have hAex : ∀ m : ℕ, ∃ A : ℝ, ∀ y, (1 + ‖y‖) ^ m * ‖φ y‖ ≤ A := fun m ↦
    ⟨_, fun y ↦ by
      simpa using SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (m, 0)) le_rfl le_rfl
        φ y⟩
  choose A hA using hAex
  have hA0 : ∀ m, 0 ≤ A m := fun m ↦
    (by positivity : 0 ≤ (1 + ‖(0 : E)‖) ^ m * ‖φ 0‖).trans (hA m 0)
  let c : ℕ → ℝ := fun k ↦ ⨅ m : ℕ, A m / ((2 : ℝ) ^ k) ^ m
  have hbdd : ∀ k : ℕ, BddBelow (Set.range fun m : ℕ ↦ A m / ((2 : ℝ) ^ k) ^ m) := fun k ↦
    ⟨0, by rintro _ ⟨m, rfl⟩; exact div_nonneg (hA0 m) (by positivity)⟩
  have hc0 : ∀ k, 0 ≤ c k := fun k ↦ le_ciInf fun m ↦ div_nonneg (hA0 m) (by positivity)
  have hcle : ∀ k m, c k ≤ A m / ((2 : ℝ) ^ k) ^ m := fun k m ↦ ciInf_le (hbdd k) m
  have hsum : ∀ m : ℕ, Summable fun k : ℕ ↦ c k * ((2 : ℝ) ^ (k + 1)) ^ m := by
    intro m
    refine Summable.of_nonneg_of_le (fun k ↦ mul_nonneg (hc0 k) (by positivity)) (fun k ↦ ?_)
      (summable_geometric_two.mul_left (A (m + 1) * 2 ^ m))
    have e1 : ((2 : ℝ) ^ (k + 1)) ^ m = ((2 : ℝ) ^ k) ^ m * 2 ^ m := by
      rw [pow_succ, mul_pow]
    have e2 : ((2 : ℝ) ^ k) ^ (m + 1) = ((2 : ℝ) ^ k) ^ m * 2 ^ k := by rw [pow_succ]
    calc c k * ((2 : ℝ) ^ (k + 1)) ^ m
        ≤ A (m + 1) / ((2 : ℝ) ^ k) ^ (m + 1) * ((2 : ℝ) ^ (k + 1)) ^ m := by
          gcongr
          exact hcle k (m + 1)
      _ = A (m + 1) * 2 ^ m * (1 / 2) ^ k := by
          rw [e1, e2, one_div, inv_pow]
          field_simp
  let a : ℕ → ℝ := fun k ↦ ((2 : ℝ) ^ (k + 1))⁻¹
  have ha0 : ∀ k, 0 ≤ a k := fun k ↦ by positivity
  have ha1 : ∀ k, a k ≤ 1 := fun k ↦ inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  let f : ℕ → E → ℝ := fun k y ↦ c k * χ (a k • y)
  have hfsm : ∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f k) := fun k ↦
    contDiff_const.mul ((χ.smooth ⊤).comp (contDiff_const.smul contDiff_id))
  choose D hD using fun (m n : ℕ) ↦ χ.decay' m n
  have hfd : ∀ (k m n : ℕ) (x : E),
      ‖x‖ ^ m * ‖iteratedFDeriv ℝ n (f k) x‖ ≤ c k * ((2 : ℝ) ^ (k + 1)) ^ m * D m n := by
    intro k m n x
    have e1 : iteratedFDeriv ℝ n (f k) x =
        c k • iteratedFDeriv ℝ n (fun y ↦ χ (a k • y)) x :=
      iteratedFDeriv_const_smul_apply (a := c k) (f := fun y ↦ χ (a k • y))
        (((χ.smooth ⊤).comp (contDiff_const.smul contDiff_id)).contDiffAt.of_le
          (by exact_mod_cast le_top))
    have e2 : ‖x‖ = (2 : ℝ) ^ (k + 1) * ‖a k • x‖ := by
      rw [norm_smul, Real.norm_of_nonneg (ha0 k), ← mul_assoc, mul_inv_cancel₀ (by positivity),
        one_mul]
    rw [e1, norm_smul, Real.norm_of_nonneg (hc0 k)]
    calc ‖x‖ ^ m * (c k * ‖iteratedFDeriv ℝ n (fun y ↦ χ (a k • y)) x‖)
        ≤ ‖x‖ ^ m * (c k * ‖iteratedFDeriv ℝ n χ (a k • x)‖) := by
          have := norm_iteratedFDeriv_dilate_le χ (ha0 k) (ha1 k) n x
          have := hc0 k
          gcongr
      _ = c k * ((2 : ℝ) ^ (k + 1)) ^ m *
            (‖a k • x‖ ^ m * ‖iteratedFDeriv ℝ n χ (a k • x)‖) := by
          rw [e2, mul_pow]
          ring
      _ ≤ c k * ((2 : ℝ) ^ (k + 1)) ^ m * D m n := by
          exact mul_le_mul_of_nonneg_left (hD m n (a k • x))
            (mul_nonneg (hc0 k) (by positivity))
  have hfv : ∀ (n k : ℕ) (x : E), ‖iteratedFDeriv ℝ n (f k) x‖ ≤ c k * D 0 n := by
    intro n k x
    simpa using hfd k 0 n x
  have hsv : ∀ n : ℕ, Summable fun k ↦ c k * D 0 n := fun n ↦ by
    simpa using (hsum 0).mul_right (D 0 n)
  have hsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun y ↦ ∑' k, f k y :=
    contDiff_tsum (v := fun n k ↦ c k * D 0 n) hfsm (fun n _ ↦ hsv n) fun n k x _ ↦ hfv n k x
  let Φr : 𝓢(E, ℝ) :=
    { toFun := fun y ↦ ∑' k, f k y
      smooth' := hsmooth
      decay' := by
        intro m n
        refine ⟨(∑' k, c k * ((2 : ℝ) ^ (k + 1)) ^ m) * D m n, fun x ↦ ?_⟩
        rw [iteratedFDeriv_tsum_apply (v := fun n k ↦ c k * D 0 n) hfsm (fun n _ ↦ hsv n)
          (fun n k x _ ↦ hfv n k x) (by exact_mod_cast le_top) x]
        have hs1 : Summable fun k ↦ ‖iteratedFDeriv ℝ n (f k) x‖ :=
          Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun k ↦ hfv n k x) (hsv n)
        have hs2 : Summable fun k ↦ c k * ((2 : ℝ) ^ (k + 1)) ^ m * D m n :=
          (hsum m).mul_right _
        calc ‖x‖ ^ m * ‖∑' k, iteratedFDeriv ℝ n (f k) x‖
            ≤ ‖x‖ ^ m * ∑' k, ‖iteratedFDeriv ℝ n (f k) x‖ := by
              gcongr
              exact norm_tsum_le_tsum_norm hs1
          _ = ∑' k, ‖x‖ ^ m * ‖iteratedFDeriv ℝ n (f k) x‖ := tsum_mul_left.symm
          _ ≤ ∑' k, c k * ((2 : ℝ) ^ (k + 1)) ^ m * D m n :=
              (hs1.mul_left _).tsum_le_tsum (fun k ↦ hfd k m n x) hs2
          _ = (∑' k, c k * ((2 : ℝ) ^ (k + 1)) ^ m) * D m n := tsum_mul_right }
  refine ⟨SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM Φr, Φr, fun y ↦ rfl, fun y ↦ ?_⟩
  have hf0 : ∀ k, 0 ≤ f k y := fun k ↦ mul_nonneg (hc0 k) (hχ0 _)
  have hfs : Summable fun k ↦ f k y := by
    refine Summable.of_nonneg_of_le hf0 (fun k ↦ ?_) (by simpa using hsum 0)
    exact mul_le_of_le_one_right (hc0 k) (hχ1 _)
  obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near (x := 1 + ‖y‖) (y := (2 : ℝ))
    (by linarith [norm_nonneg y]) (by norm_num)
  have h1 : ‖φ y‖ ≤ c k := by
    refine le_ciInf fun m ↦ ?_
    rw [le_div_iff₀ (by positivity), mul_comm]
    refine le_trans ?_ (hA m y)
    gcongr
  have h2 : f k y = c k := by
    have : χ (a k • y) = 1 := by
      refine hχb _ ?_
      rw [norm_smul, Real.norm_of_nonneg (ha0 k), inv_mul_le_iff₀ (by positivity), mul_one]
      linarith
    simp only [f, this, mul_one]
  calc ‖φ y‖ ≤ f k y := h2 ▸ h1
    _ ≤ ∑' k, f k y := hfs.le_tsum k fun j _ ↦ hf0 j

end Majorant

set_option maxSynthPendingDepth 1
set_option synthInstance.maxSize 1000

variable {K : Type _} [Field K] [NumberField K]

end GlobalTheory.CompanionTheory.EisRk1
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsDividedPowersOnReductions
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsDividedPowersOnReductions
set_option backward.isDefEq.respectTransparency false

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.PerfFil

theorem mem_span_pow_of_factorial_mul_eq {S : Type} [CommRing S] (hS : R.TF S) {l : ℕ}
    (hl : l.Prime) (n : ℕ) {x : S} (hx : x ∈ Ideal.span {(l : S) ^ n}) {k : ℕ} (hk : k ≠ 0)
    {y : S} (e : (k.factorial : S) * y = x ^ k) : y ∈ Ideal.span {(l : S) ^ n} := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  obtain ⟨x', rfl⟩ := Ideal.mem_span_singleton'.1 hx
  haveI := Fact.mk hl
  obtain ⟨v, m, hlm, hm⟩ := Nat.exists_eq_pow_mul_and_not_dvd k.factorial_ne_zero l hl.ne_one
  have hv : v < k := by
    have h1 : v ≤ multiplicity l k.factorial :=
      (Nat.pow_dvd_iff_le_multiplicity hl.ne_one k.factorial_ne_zero).1 ⟨m, hm⟩
    exact lt_of_le_of_lt h1 (multiplicity_factorial_lt_of_ne_zero l hk)
  obtain ⟨t, ht⟩ : ∃ t, n * k = n + v + t := by
    obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    refine ⟨n * k' - v, ?_⟩
    have : v ≤ n * k' := by nlinarith [Nat.lt_succ_iff.1 hv]
    rw [Nat.succ_eq_add_one, Nat.mul_add, Nat.mul_one]
    omega
  have hfac : (k.factorial : S) = (l : S) ^ v * (m : S) := by rw [hm]; push_cast; rfl
  have e2 : (l : S) ^ v * ((m : S) * y) = (l : S) ^ v * ((l : S) ^ n * ((l : S) ^ t * x' ^ k)) := by
    rw [← mul_assoc, ← hfac, e, mul_pow, ← pow_mul, ht, pow_add, pow_add]
    ring
  have hr : (l : S) ^ v ∈ nonZeroDivisors S := pow_mem (hS l hl.ne_zero) v
  have e3 : (m : S) * y = (l : S) ^ n * ((l : S) ^ t * x' ^ k) := by
    have h0 : (l : S) ^ v * ((m : S) * y - (l : S) ^ n * ((l : S) ^ t * x' ^ k)) = 0 := by
      rw [mul_sub, e2, sub_self]
    exact sub_eq_zero.1 ((mem_nonZeroDivisors_iff_right.1 hr) _ (by rwa [mul_comm] at h0))
  have hc : IsCoprime (m : ℤ) ((l : ℤ) ^ n) := by
    apply IsCoprime.pow_right
    rw [Nat.isCoprime_iff_coprime]
    exact ((Nat.Prime.coprime_iff_not_dvd hl).2 hlm).symm
  obtain ⟨a, b, hab⟩ := hc
  have hab' : (a : S) * (m : S) + (b : S) * (l : S) ^ n = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → S) hab
  have hy : y = ((a : S) * ((l : S) ^ t * x' ^ k) + (b : S) * y) * (l : S) ^ n := by
    calc y = ((a : S) * (m : S) + (b : S) * (l : S) ^ n) * y := by rw [hab', one_mul]
      _ = (a : S) * ((m : S) * y) + (b : S) * (l : S) ^ n * y := by ring
      _ = _ := by rw [e3]; ring
  rw [hy]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

theorem exists_dividedPowers_map_mkAcr {l : ℕ} [hl : Fact l.Prime] (A : PAlg l) (n : ℕ)
    (I : Ideal A.Acr0) (hI : R.PdI I) (K : Ideal (A.Acr n)) (hK : K = I.map (A.mkAcr n)) :
    ∃ δ : DividedPowers K, R.IsPd (A.mkAcr n) I δ := by
  subst hK
  exact GlobalTheory.CompanionTheory.PdTF.exists_dividedPowers_map_quotient A.acris_torsion_free I
    (Ideal.span {(l : A.Acr0) ^ n}) hI
    fun x _ hx k hk y e => mem_span_pow_of_factorial_mul_eq A.acris_torsion_free hl.out n hx hk e

theorem exists_dividedPowers_fil_pfil : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ),
    (∃ δ : DividedPowers (A.Fil n 1), R.IsPd (A.mkAcr n) (A.Fil0 1) δ) ∧
      ∃ δ : DividedPowers (A.PFil n), R.IsPd (A.mkAcr n) A.PFil0 δ := by
  intro l _ A n
  obtain ⟨-, -, -, -, h1, h2, -⟩ := GlobalTheory.T.crystalline_filtration_multiplicative A
  obtain ⟨p1, p2, -⟩ := GlobalTheory.T.filtration_divided_power_structures A
  exact ⟨exists_dividedPowers_map_mkAcr A n _ p1 _ (h1 n 1),
    exists_dividedPowers_map_mkAcr A n _ p2 _ (h2 n)⟩

end GlobalTheory.CompanionTheory.PerfFil
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsDividedPowersOnReductionsStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_divided_powers_on_reductions : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ), (∃ δ : DividedPowers (A.Fil n 1), R.IsPd (A.mkAcr n) (A.Fil0 1) δ) ∧ ∃ δ : DividedPowers (A.PFil n), R.IsPd (A.mkAcr n) A.PFil0 δ := by
  first | exact @GlobalTheory.CompanionTheory.PerfFil.exists_dividedPowers_fil_pfil | exact GlobalTheory.CompanionTheory.PerfFil.exists_dividedPowers_fil_pfil | (intros; apply GlobalTheory.CompanionTheory.PerfFil.exists_dividedPowers_fil_pfil <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuotientMapsSurjectiveWithKernels
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuotientMapsSurjectiveWithKernels
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.Untilt

theorem dxi_zero {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ) : A.dxi n 0 = 1 := by
  have h : A.dxi0 0 = 1 := Subtype.ext (by simp [PAlg.dxi0, dpw])
  rw [PAlg.dxi, h, map_one]

theorem exists_toAcr_sub_mem {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ) (z : A.Acr n) :
    ∃ w : A.W, z - A.toAcr n w ∈ A.Fil n 1 := by
  have h0 : z ∈ A.Fil n 0 := by
    rw [((GlobalTheory.T.crystalline_filtration_multiplicative A).2.2.2.2.2.2.1 n)]; trivial
  obtain ⟨w, hw⟩ := (GlobalTheory.T.graded_filtration_generated_by_dividedXi A n 0).1 z h0
  refine ⟨w, ?_⟩
  simpa [dxi_zero] using hw

theorem toAcr_mem_fil_iff {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ) (w : A.W) :
    A.toAcr n w ∈ A.Fil n 1 ↔ A.th w ∈ Ideal.span {(l : A.U) ^ n} := by
  have h := (GlobalTheory.T.graded_filtration_generated_by_dividedXi A n 0).2 w
  simpa [dxi_zero] using h

theorem uToQ_surjective {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ) :
    Function.Surjective (A.uToQ n) := by
  intro y
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨w, hw⟩ := exists_toAcr_sub_mem A n z
  exact ⟨A.th w, (Ideal.Quotient.eq.2 hw).symm⟩

theorem ker_uToQ {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ) :
    RingHom.ker (A.uToQ n) = Ideal.span {(l : A.U) ^ n} := by
  ext x
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective x
  change A.th w ∈ _ ↔ A.th w ∈ _
  rw [RingHom.mem_ker, uToQ_th, Ideal.Quotient.eq_zero_iff_mem, toAcr_mem_fil_iff]

theorem uToPQ_surjective {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ) :
    Function.Surjective (A.uToPQ n) := by
  intro y
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨w, hw⟩ := exists_toAcr_sub_mem A n z
  have h : z - A.toAcr n w ∈ A.PFil n := Ideal.mem_sup_right hw
  exact ⟨A.th w, (Ideal.Quotient.eq.2 h).symm⟩

theorem ker_uToPQ {l : ℕ} [Fact l.Prime] (A : PAlg l) {n : ℕ} (hn : n ≠ 0) :
    RingHom.ker (A.uToPQ n) = Ideal.span {(l : A.U)} := by
  apply le_antisymm
  · intro x hx
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective x
    change A.th w ∈ _
    have h : A.toAcr n w ∈ A.PFil n := Ideal.Quotient.eq_zero_iff_mem.1 hx
    obtain ⟨u, hu, z, hz, e⟩ := Submodule.mem_sup.1 h
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hu
    obtain ⟨w', hw'⟩ := exists_toAcr_sub_mem A n a
    have h1 : A.toAcr n (w - (l : A.W) * w') ∈ A.Fil n 1 := by
      have e' : A.toAcr n (w - (l : A.W) * w') = (a - A.toAcr n w') * (l : A.Acr n) + z := by
        rw [map_sub, map_mul, map_natCast, ← e]; ring
      rw [e']
      exact add_mem (Ideal.mul_mem_right _ _ hw') hz
    have h2 := (toAcr_mem_fil_iff A n _).1 h1
    have h3 : A.th (w - (l : A.W) * w') ∈ Ideal.span {(l : A.U)} :=
      Ideal.span_singleton_le_span_singleton.2 (dvd_pow_self _ hn) h2
    have h4 : A.th w = A.th (w - (l : A.W) * w') + (l : A.U) * A.th w' := by
      rw [map_sub, map_mul, map_natCast]; ring
    rw [h4]
    exact add_mem h3 (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
  · rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, map_natCast,
      ← map_natCast (Ideal.Quotient.mk (A.PFil n))]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _))

theorem uToQ_main : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ), Function.Surjective (A.uToQ n) ∧
    RingHom.ker (A.uToQ n) = Ideal.span {(l : A.U) ^ n} ∧ Function.Surjective (A.uToPQ n) ∧
    (n ≠ 0 → RingHom.ker (A.uToPQ n) = Ideal.span {(l : A.U)}) :=
  fun A n => ⟨uToQ_surjective A n, ker_uToQ A n, uToPQ_surjective A n, fun hn => ker_uToPQ A hn⟩

end GlobalTheory.CompanionTheory.Untilt
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuotientMapsSurjectiveWithKernelsStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotient_maps_surjective_with_kernels : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ), Function.Surjective (A.uToQ n) ∧ RingHom.ker (A.uToQ n) = Ideal.span {(l : A.U) ^ n} ∧ Function.Surjective (A.uToPQ n) ∧ (n ≠ 0 → RingHom.ker (A.uToPQ n) = Ideal.span {(l : A.U)}) := by
  first | exact @GlobalTheory.CompanionTheory.Untilt.uToQ_main | exact GlobalTheory.CompanionTheory.Untilt.uToQ_main | (intros; apply GlobalTheory.CompanionTheory.Untilt.uToQ_main <;> assumption)
end
end
