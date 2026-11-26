module

public import Development.WeilBound.CoreStatements.SesquilinearFractions.ExistsOrthogonalLocalBasisExtension
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocalBasisGramDeterminantBound
public import Development.WeilBound.CoreStatements.SesquilinearFractions.GramSignatureOrthogonalSplit
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.PeriodHermitianTypeCompatibility
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsLocalBasisStatement

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.SesquilinearFractions.UltrametricNormProdSubLt
open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace PositivityTheory.Xgf

section Ultra

variable {A : Type} [NormedField A] [IsUltrametricDist A]

theorem norm_sign_smul {I : Type} [Fintype I] [DecidableEq I] (σ : Equiv.Perm I) (x : A) :
    ‖Equiv.Perm.sign σ • x‖ = ‖x‖ := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h, Units.smul_def]

theorem ultrametric_norm_sum_lt {ι : Type} (s : Finset ι) (f : ι → A) {C : ℝ} (hC : 0 < C) (h : ∀ i ∈ s, ‖f i‖ < C) :
    ‖∑ i ∈ s, f i‖ < C := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simpa using hC
  obtain ⟨i, hi, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty hs f
  exact hle.trans_lt (h i hi)

theorem ultrametric_norm_prod_sub_lt {ι : Type} (s : Finset ι) (a b : ι → A) {r : ℝ} (hr : 0 < r) (ha : ∀ i ∈ s, ‖a i‖ ≤ r)
    (hb : ∀ i ∈ s, ‖b i‖ ≤ r) (hab : ∀ i ∈ s, ‖a i - b i‖ < r) :
    ‖∏ i ∈ s, a i - ∏ i ∈ s, b i‖ < r ^ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.card_insert_of_notMem hj]
    have ih' := ih (fun i hi => ha i (Finset.mem_insert_of_mem hi)) (fun i hi => hb i (Finset.mem_insert_of_mem hi))
      (fun i hi => hab i (Finset.mem_insert_of_mem hi))
    have e : a j * ∏ i ∈ s, a i - b j * ∏ i ∈ s, b i =
        a j * (∏ i ∈ s, a i - ∏ i ∈ s, b i) + (a j - b j) * ∏ i ∈ s, b i := by ring
    rw [e]
    have hpb : ‖∏ i ∈ s, b i‖ ≤ r ^ s.card := by
      rw [norm_prod]
      calc ∏ i ∈ s, ‖b i‖ ≤ ∏ _i ∈ s, r :=
            Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i hi => hb i (Finset.mem_insert_of_mem hi)
        _ = r ^ s.card := Finset.prod_const r
    have hpos : 0 < r ^ (s.card + 1) := pow_pos hr _
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
    · rw [norm_mul, pow_succ']
      rcases (norm_nonneg (a j)).eq_or_lt with h0 | h0
      · rw [← h0, zero_mul]; exact pow_pos hr _ |>.trans_le (by rw [pow_succ'])
      · calc ‖a j‖ * ‖∏ i ∈ s, a i - ∏ i ∈ s, b i‖ < ‖a j‖ * r ^ s.card := mul_lt_mul_of_pos_left ih' h0
          _ ≤ r * r ^ s.card := mul_le_mul_of_nonneg_right (ha j (Finset.mem_insert_self _ _)) (pow_nonneg hr.le _)
    · rw [norm_mul, pow_succ']
      exact mul_lt_mul_of_lt_of_le_of_nonneg_of_pos (hab j (Finset.mem_insert_self _ _)) hpb (norm_nonneg _)
        (pow_pos hr _)

end Ultra

theorem ultrametric_det_norm_stable : ∀ (A : Type) [NormedField A] [IsUltrametricDist A] (I : Type) [Fintype I] [DecidableEq I] (M M' : Matrix I I A) (r : ℝ), 0 < r → (∀ a b, ‖M a b‖ ≤ r) → (∀ a b, ‖M' a b - M a b‖ < r) → ‖M.det‖ = r ^ Fintype.card I → ‖M'.det‖ = r ^ Fintype.card I := by
  intro A _ _ I _ _ M M' r hr hM hM' hdet
  have hM'b : ∀ a b, ‖M' a b‖ ≤ r := fun a b => by
    have := IsUltrametricDist.norm_add_le_max (M' a b - M a b) (M a b)
    rw [sub_add_cancel] at this
    exact this.trans (max_le (hM' a b).le (hM a b))
  have hdiff : ‖M'.det - M.det‖ < r ^ Fintype.card I := by
    rw [Matrix.det_apply, Matrix.det_apply, ← Finset.sum_sub_distrib]
    refine ultrametric_norm_sum_lt _ _ (pow_pos hr _) fun σ _ => ?_
    rw [← smul_sub, norm_sign_smul, ← Finset.card_univ]
    exact ultrametric_norm_prod_sub_lt _ _ _ hr (fun i _ => hM'b _ _) (fun i _ => hM _ _) fun i _ => hM' _ _
  have e : M'.det = M.det + (M'.det - M.det) := by ring
  rw [e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hdet]; exact hdiff.ne'), hdet]
  exact max_eq_left hdiff.le

theorem negDef_block_of_posDef : ∀ (p q : ℕ) (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin q) (Fin q) ℂ) (C : Matrix (Fin q) (Fin p ⊕ Fin q) ℂ), A.PosDef → B.IsHermitian → (-(C * Matrix.fromBlocks A 0 0 B * Cᴴ)).PosDef → (-B).PosDef := by
  intro p q A B C hA hB hC
  let C1 : Matrix (Fin q) (Fin p) ℂ := fun a i => C a (Sum.inl i)
  let C2 : Matrix (Fin q) (Fin q) ℂ := fun a i => C a (Sum.inr i)
  have hsplit : C * Matrix.fromBlocks A 0 0 B * Cᴴ = C1 * A * C1ᴴ + C2 * B * C2ᴴ := by
    have hCe : C = Matrix.fromCols C1 C2 := by ext a (i | i) <;> rfl
    rw [hCe, Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.fromCols_mul_fromBlocks,
      Matrix.fromCols_mul_fromRows]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  have hP : (C2 * (-B) * C2ᴴ).PosDef := by
    have e : C2 * (-B) * C2ᴴ = -(C * Matrix.fromBlocks A 0 0 B * Cᴴ) + C1 * A * C1ᴴ := by
      rw [hsplit]; noncomm_ring
    rw [e]
    exact hC.add_posSemidef (hA.posSemidef.mul_mul_conjTranspose_same C1)
  have hinj : Function.Injective (C2ᴴ).mulVec := by
    intro x y hxy
    by_contra hne
    have hz : x - y ≠ 0 := sub_ne_zero.mpr hne
    have h0 : (C2ᴴ) *ᵥ (x - y) = 0 := by rw [Matrix.mulVec_sub, hxy, sub_self]
    have := hP.dotProduct_mulVec_pos hz
    rw [← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero, dotProduct_zero] at this
    exact lt_irrefl _ this
  have hU : IsUnit (C2ᴴ) := Matrix.mulVec_injective_iff_isUnit.mp hinj
  have hG : C2ᴴ * (C2ᴴ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hU)
  have hGinj : Function.Injective ((C2ᴴ)⁻¹).mulVec := fun x y hxy => by
    have := congrArg (C2ᴴ).mulVec hxy
    rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hG, Matrix.one_mulVec, Matrix.one_mulVec] at this
  have key := hP.conjTranspose_mul_mul_same (B := (C2ᴴ)⁻¹) hGinj
  have h1 : ((C2ᴴ)⁻¹)ᴴ * C2 = 1 := by
    have := congrArg Matrix.conjTranspose hG
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_one] at this
  have e : ((C2ᴴ)⁻¹)ᴴ * (C2 * -B * C2ᴴ) * (C2ᴴ)⁻¹ = -B := by
    calc ((C2ᴴ)⁻¹)ᴴ * (C2 * -B * C2ᴴ) * (C2ᴴ)⁻¹ = (((C2ᴴ)⁻¹)ᴴ * C2) * -B * (C2ᴴ * (C2ᴴ)⁻¹) := by
          simp only [Matrix.mul_assoc]
      _ = -B := by rw [h1, hG, Matrix.one_mul, Matrix.mul_one]
  rwa [e] at key

end PositivityTheory.Xgf
end

section -- merged from Development.WeilBound.CoreStatements.SesquilinearFractions.ExistsIntegralPosDefPerturbation
section -- merged from Development.WeilBound.CoreStatements.SesquilinearFractions.ExistsIntegerNearConjVector
open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace PositivityTheory.Xgf

theorem exists_integer_near_conj_vector : ∀ (E : Type) [Field E] [NumberField E], ∃ B : ℝ, ∀ c : (E →+* ℂ) → ℂ, (∀ τ, c (ComplexEmbedding.conjugate τ) = starRingEnd ℂ (c τ)) → ∃ a : 𝓞 E, ∀ τ : E →+* ℂ, ‖τ (a : E) - c τ‖ ≤ B := by
  intro E _ _
  classical
  obtain ⟨bC, hv⟩ : ∃ bC : Module.Basis (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) ℂ ((E →+* ℂ) → ℂ),
      ∀ i (τ : E →+* ℂ), bC i τ = τ (RingOfIntegers.basis E i : E) :=
    ⟨canonicalEmbedding.latticeBasis E, fun i τ => by
      rw [canonicalEmbedding.latticeBasis_apply, canonicalEmbedding.apply_at, integralBasis_apply]⟩
  refine ⟨∑ τ : E →+* ℂ, ∑ i, ‖τ (RingOfIntegers.basis E i : E)‖, fun c hc => ?_⟩
  have hsum : c = ∑ i, bC.repr c i • bC i := (bC.sum_repr c).symm
  have hcτ : ∀ τ : E →+* ℂ, c τ = ∑ i, bC.repr c i * τ (RingOfIntegers.basis E i : E) := by
    intro τ
    conv_lhs => rw [hsum]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hv]
  have hconj : ∀ τ : E →+* ℂ,
      ∑ i, starRingEnd ℂ (bC.repr c i) * τ (RingOfIntegers.basis E i : E) = c τ := by
    intro τ
    have h1 := hc τ
    rw [hcτ (ComplexEmbedding.conjugate τ)] at h1
    have h2 := congrArg (starRingEnd ℂ) h1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Complex.conj_conj, map_sum] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]
  have hli := Fintype.linearIndependent_iff.mp bC.linearIndependent
    (fun i => bC.repr c i - starRingEnd ℂ (bC.repr c i)) (by
      funext τ
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hv, sub_mul,
        Finset.sum_sub_distrib]
      rw [hconj τ, ← hcτ τ, sub_self])
  have hreal : ∀ i, (bC.repr c i).im = 0 := by
    intro i
    have h3 := congrArg Complex.im (hli i)
    rw [Complex.sub_im, Complex.conj_im, sub_neg_eq_add, Complex.zero_im] at h3
    linarith
  obtain ⟨x, hx⟩ : ∃ x : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → ℝ, ∀ i, bC.repr c i = (x i : ℂ) :=
    ⟨fun i => (bC.repr c i).re, fun i => Complex.ext (by simp) (by simp [hreal i])⟩
  refine ⟨∑ i, round (x i) • RingOfIntegers.basis E i, fun τ => ?_⟩
  have hτa : τ ((∑ i, round (x i) • RingOfIntegers.basis E i : 𝓞 E) : E) =
      ∑ i, (round (x i) : ℂ) * τ (RingOfIntegers.basis E i : E) := by
    change (τ.comp (algebraMap (𝓞 E) E)) (∑ i, round (x i) • RingOfIntegers.basis E i) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, zsmul_eq_mul]
    rfl
  have hcx : c τ = ∑ i, (x i : ℂ) * τ (RingOfIntegers.basis E i : E) := by
    rw [hcτ τ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hx i]
  rw [hτa, hcx, ← Finset.sum_sub_distrib]
  calc ‖∑ i, ((round (x i) : ℂ) * τ (RingOfIntegers.basis E i : E) -
          (x i : ℂ) * τ (RingOfIntegers.basis E i : E))‖
      ≤ ∑ i, ‖(round (x i) : ℂ) * τ (RingOfIntegers.basis E i : E) -
          (x i : ℂ) * τ (RingOfIntegers.basis E i : E)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖τ (RingOfIntegers.basis E i : E)‖ := Finset.sum_le_sum fun i _ => by
        rw [← sub_mul, norm_mul]
        have hr : ‖(round (x i) : ℂ) - (x i : ℂ)‖ ≤ 1 := by
          have h := abs_sub_round (x i)
          rw [show ((round (x i) : ℤ) : ℂ) - ((x i : ℝ) : ℂ) = (((round (x i) : ℝ) - x i : ℝ) : ℂ) by
            push_cast; ring, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
          linarith
        calc ‖(round (x i) : ℂ) - (x i : ℂ)‖ * ‖τ (RingOfIntegers.basis E i : E)‖
            ≤ 1 * ‖τ (RingOfIntegers.basis E i : E)‖ := mul_le_mul_of_nonneg_right hr (norm_nonneg _)
          _ = ‖τ (RingOfIntegers.basis E i : E)‖ := one_mul _
    _ ≤ ∑ τ' : E →+* ℂ, ∑ i, ‖τ' (RingOfIntegers.basis E i : E)‖ :=
        Finset.single_le_sum (f := fun τ' : E →+* ℂ => ∑ i, ‖τ' (RingOfIntegers.basis E i : E)‖)
          (fun τ' _ => Finset.sum_nonneg fun i _ => norm_nonneg _) (Finset.mem_univ τ)

end PositivityTheory.Xgf

end
end

open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace PositivityTheory.Xgf

theorem complexEmbedding_conjugate_conjugate {E : Type} [Field E] (τ : E →+* ℂ) :
    ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ := star_star τ

private theorem eventually_posDef_add_mul_conjTranspose {I J : Type} [Fintype I] [Fintype J] [DecidableEq I]
    (C : Matrix I J ℂ) (M : Matrix J J ℂ) (hM : M.IsHermitian) (h : (C * M * Cᴴ).PosDef) :
    ∀ᶠ D in nhds (0 : Matrix I J ℂ), ((C + D) * M * (C + D)ᴴ).PosDef := by
  let g : Matrix I J ℂ × (I → ℂ) → ℝ := fun p =>
    (star p.2 ⬝ᵥ (((C + p.1) * M * (C + p.1)ᴴ) *ᵥ p.2)).re
  have hg : Continuous g := by
    refine Complex.continuous_re.comp ?_
    refine Continuous.dotProduct (continuous_star.comp continuous_snd) ?_
    refine Continuous.matrix_mulVec ?_ continuous_snd
    refine Continuous.matrix_mul ?_ ?_
    · exact (continuous_const.add continuous_fst).matrix_mul continuous_const
    · exact (continuous_const.add continuous_fst).matrix_conjTranspose
  have hK : IsCompact (Metric.sphere (0 : I → ℂ) 1) := isCompact_sphere 0 1
  have key : ∀ᶠ D in nhds (0 : Matrix I J ℂ), ∀ u ∈ Metric.sphere (0 : I → ℂ) 1, 0 < g (D, u) := by
    apply hK.eventually_forall_of_forall_eventually
    intro u hu
    have hu0 : u ≠ 0 := by
      rintro rfl
      simp at hu
    have h0 : 0 < g (0, u) := by
      have hp := h.dotProduct_mulVec_pos hu0
      have hp' := (Complex.lt_def.mp hp).1
      simpa [g] using hp'
    exact hg.continuousAt.eventually (lt_mem_nhds h0)
  filter_upwards [key] with D hD
  have hH : ((C + D) * M * (C + D)ᴴ).IsHermitian := isHermitian_mul_mul_conjTranspose _ hM
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨hH, fun x hx => ?_⟩
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  set u : I → ℂ := ((‖x‖⁻¹ : ℝ) : ℂ) • x with hu_def
  have hu : u ∈ Metric.sphere (0 : I → ℂ) 1 := by
    rw [mem_sphere_zero_iff_norm, hu_def, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hr), inv_mul_cancel₀ hr.ne']
  have hx' : x = ((‖x‖ : ℝ) : ℂ) • u := by
    rw [hu_def, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hr.ne', Complex.ofReal_one, one_smul]
  have hpos := hD u hu
  rw [Complex.lt_def]
  refine ⟨?_, (hH.im_star_dotProduct_mulVec_self x).symm⟩
  rw [hx', star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct]
  simp only [smul_eq_mul, Complex.star_def, Complex.conj_ofReal, Complex.re_ofReal_mul, Complex.zero_re]
  exact mul_pos hr (mul_pos hr hpos)

theorem exists_integral_posDef_perturbation : ∀ (E : Type) [Field E] [NumberField E] (Ψ : Set (E →+* ℂ)) (I J : Type) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] (M : (E →+* ℂ) → Matrix J J ℂ) (C : (E →+* ℂ) → Matrix I J ℂ) (X₀ : Matrix I J (𝓞 E)) (n : ℕ), n ≠ 0 → (∀ τ ∈ Ψ, ComplexEmbedding.conjugate τ ∉ Ψ) → (∀ τ ∈ Ψ, (M τ).IsHermitian ∧ (C τ * M τ * (C τ)ᴴ).PosDef) → ∃ Y : Matrix I J (𝓞 E), ∀ τ ∈ Ψ, (((X₀ + n • Y).map fun a => τ (a : E)) * M τ * ((X₀ + n • Y).map fun a => τ (a : E))ᴴ).PosDef := by
  intro E _ _ Ψ I J _ _ _ _ M C X₀ n hn hΨ hpos
  classical
  obtain ⟨B, hB⟩ := exists_integer_near_conj_vector E
  let f : ℕ → I → J → (E →+* ℂ) → ℂ := fun k i j τ => ((k : ℂ) * C τ i j - τ (X₀ i j : E)) / n
  let c : ℕ → I → J → (E →+* ℂ) → ℂ := fun k i j σ =>
    if σ ∈ Ψ then f k i j σ
    else if ComplexEmbedding.conjugate σ ∈ Ψ then starRingEnd ℂ (f k i j (ComplexEmbedding.conjugate σ))
    else 0
  have hc : ∀ k i j σ, c k i j (ComplexEmbedding.conjugate σ) = starRingEnd ℂ (c k i j σ) := by
    intro k i j σ
    by_cases h1 : σ ∈ Ψ
    · have h2 : ComplexEmbedding.conjugate σ ∉ Ψ := hΨ σ h1
      simp [c, h1, h2, complexEmbedding_conjugate_conjugate]
    · by_cases h2 : ComplexEmbedding.conjugate σ ∈ Ψ
      · simp [c, h1, h2]
      · simp [c, h1, h2, complexEmbedding_conjugate_conjugate]
  choose a ha using fun (k : ℕ) (i : I) (j : J) => hB (c k i j) (hc k i j)
  let D : ℕ → (E →+* ℂ) → Matrix I J ℂ := fun k τ =>
    Matrix.of fun i j => ((n : ℂ) / k) * (τ (a k i j : E) - c k i j τ)
  have hX : ∀ k : ℕ, k ≠ 0 → ∀ τ ∈ Ψ,
      ((X₀ + n • Matrix.of (a k)).map fun x => τ (x : E)) = (k : ℂ) • (C τ + D k τ) := by
    intro k hk τ hτ
    ext i j
    have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, D, c, f,
      if_pos hτ, smul_eq_mul]
    push_cast
    simp only [map_add (f := _), map_nsmul, nsmul_eq_mul, map_mul, map_natCast]
    field_simp
    ring
  have hD : ∀ τ, Filter.Tendsto (fun k : ℕ => D k τ) Filter.atTop (nhds 0) := by
    intro τ
    refine tendsto_pi_nhds.mpr (fun i => tendsto_pi_nhds.mpr (fun j => ?_))
    have hb : Filter.Tendsto (fun k : ℕ => (n : ℝ) * B / k) Filter.atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
    refine squeeze_zero_norm' (Filter.Eventually.of_forall fun k => ?_) hb
    calc ‖D k τ i j‖ = ((n : ℝ) / k) * ‖τ (a k i j : E) - c k i j τ‖ := by
          simp only [D, Matrix.of_apply, norm_mul, norm_div, Complex.norm_natCast]
      _ ≤ ((n : ℝ) / k) * B := mul_le_mul_of_nonneg_left (ha k i j τ) (by positivity)
      _ = (n : ℝ) * B / k := by ring
  have hev : ∀ τ ∈ Ψ, ∀ᶠ k in Filter.atTop,
      ((C τ + D k τ) * M τ * (C τ + D k τ)ᴴ).PosDef := fun τ hτ =>
    (hD τ).eventually (eventually_posDef_add_mul_conjTranspose (C τ) (M τ) (hpos τ hτ).1 (hpos τ hτ).2)
  have hall : ∀ᶠ k in Filter.atTop, ∀ τ ∈ Ψ,
      ((C τ + D k τ) * M τ * (C τ + D k τ)ᴴ).PosDef :=
    (Filter.eventually_all_finite (Set.toFinite Ψ)).mpr hev
  obtain ⟨k, hk1, hk2⟩ := (hall.and (Filter.eventually_ne_atTop 0)).exists
  refine ⟨Matrix.of (a k), fun τ hτ => ?_⟩
  rw [hX k hk2 τ hτ]
  have hkpos : (0 : ℂ) < (k : ℂ) := by exact_mod_cast Nat.pos_of_ne_zero hk2
  have h2 := (hk1 τ hτ).smul (mul_pos hkpos hkpos)
  convert h2 using 1
  simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, star_natCast]

end PositivityTheory.Xgf

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsOrthogonalLocalBasis
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsOrthogonalLocalBasis
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.exists_orthogonal_local_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (p q : ℕ) (ℓ : Nat.Primes) (x' : Fin p → D.La), p + q = D.p + D.q → (gramE D x').det ≠ 0 → (∀ j : E →+* ℂ_[ℓ], Real.log ‖j (gramE D x').det‖ = -(p : ℝ) * logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))) → ∃ x : Fin p ⊕ Fin q → D.La, x ∘ Sum.inl = x' ∧ IsLocBasis (𝓞 E) ℓ x ∧ ∀ a b, sesq D (x (.inl a)) (x (.inr b)) = 0 := by
  exact @PositivityTheory.Xgf.exists_orthogonal_local_basis
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsOrthogonalLocalBasisStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orthogonal_local_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (p q : ℕ) (ℓ : Nat.Primes) (x' : Fin p → D.La), p + q = D.p + D.q → (gramE D x').det ≠ 0 → (∀ j : E →+* ℂ_[ℓ], Real.log ‖j (gramE D x').det‖ = -(p : ℝ) * logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))) → ∃ x : Fin p ⊕ Fin q → D.La, x ∘ Sum.inl = x' ∧ IsLocBasis (𝓞 E) ℓ x ∧ ∀ a b, sesq D (x (.inl a)) (x (.inr b)) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Relay.exists_orthogonal_local_basis | exact GlobalTheory.CompanionTheory.Relay.exists_orthogonal_local_basis | (intros; apply GlobalTheory.CompanionTheory.Relay.exists_orthogonal_local_basis <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GramSignatureOrthogonalSplit
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GramSignatureOrthogonalSplit
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.gram_signature_orthogonal_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (p q : ℕ) (x : Fin p ⊕ Fin q → D.La), IsTypeFn H p q ty → p + q = D.p + D.q → LinearIndependent (𝓞 E) x → (∀ a b, sesq D (x (.inl a)) (x (.inr b)) = 0) → (∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 → ((gramE D (x ∘ Sum.inl)).map fun a => Complex.I * τ a).PosDef ∧ (-((gramE D (x ∘ Sum.inr)).map fun a => Complex.I * τ a)).PosDef) → ∃ (P : D.La →+ (Fin g → ℂ)) (hP : IsPeriod D ty P), IsPure hP x := by
  first | exact @PositivityTheory.Xgf.gram_signature_orthogonal_split | exact PositivityTheory.Xgf.gram_signature_orthogonal_split
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GramSignatureOrthogonalSplitStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_signature_orthogonal_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (p q : ℕ) (x : Fin p ⊕ Fin q → D.La), IsTypeFn H p q ty → p + q = D.p + D.q → LinearIndependent (𝓞 E) x → (∀ a b, sesq D (x (.inl a)) (x (.inr b)) = 0) → (∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 → ((gramE D (x ∘ Sum.inl)).map fun a => Complex.I * τ a).PosDef ∧ (-((gramE D (x ∘ Sum.inr)).map fun a => Complex.I * τ a)).PosDef) → ∃ (P : D.La →+ (Fin g → ℂ)) (hP : IsPeriod D ty P), IsPure hP x := by
  first | exact @GlobalTheory.CompanionTheory.Relay.gram_signature_orthogonal_split | exact GlobalTheory.CompanionTheory.Relay.gram_signature_orthogonal_split | (intros; apply GlobalTheory.CompanionTheory.Relay.gram_signature_orthogonal_split <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PeriodGramHermitianSignature
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PeriodGramHermitianSignature
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fl.SignTau

open GlobalTheory.CompanionTheory.Ar.Flat.RiemannTau

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem sum_type {g n : ℕ} (ty : Fin g → (E →+* ℂ)) (σ : E →+* ℂ) (e : Fin n ≃ {i // ty i = σ}) (f : Fin g → ℂ)
    (hf : ∀ j, ty j ≠ σ → f j = 0) : ∑ j, f j = ∑ a, f (e a) := by
  classical
  have h1 : ∑ a, f (e a) = ∑ i : {i // ty i = σ}, f i := Equiv.sum_comp e (fun i : {i // ty i = σ} => f i)
  rw [h1, ← Finset.sum_subtype (p := fun j => ty j = σ) (Finset.univ.filter fun j => ty j = σ) (by simp) f,
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with h
  · rfl
  · exact hf j h

theorem hermForm_tyPart {g n : ℕ} (ty : Fin g → (E →+* ℂ)) (σ : E →+* ℂ) (e : Fin n ≃ {i // ty i = σ})
    (M : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    hermForm M (tyPart ty σ z) (tyPart ty σ w) =
      ∑ a, ∑ b, z (e a) * M (e a) (e b) * star (w (e b)) := by
  classical
  rw [hermForm_eq_sum]
  have h1 : ∀ j, ty j ≠ σ → ∑ k, tyPart ty σ z j * M j k * star (tyPart ty σ w k) = 0 := by
    intro j hj
    apply Finset.sum_eq_zero
    intro k _
    simp [tyPart, hj]
  rw [sum_type ty σ e _ h1]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h2 : ∀ k, ty k ≠ σ → tyPart ty σ z (e a) * M (e a) k * star (tyPart ty σ w k) = 0 := by
    intro k hk
    simp [tyPart, hk]
  rw [sum_type ty σ e _ h2]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp [tyPart, (e a).2, (e b).2]

theorem star_hermForm {g : ℕ} {M : Matrix (Fin g) (Fin g) ℂ} (hM : M.IsHermitian) (z w : Fin g → ℂ) :
    star (hermForm M z w) = hermForm M w z := by
  rw [hermForm_eq_sum, hermForm_eq_sum]
  simp only [star_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [star_mul', star_mul', star_star, hM.apply]
  ring

theorem posDef_of_hermForm {g : ℕ} {M : Matrix (Fin g) (Fin g) ℂ} (hM : M.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm M z z).re) : M.PosDef := by
  refine ⟨hM, fun x hx => ?_⟩
  have hx' : star (⇑x) ≠ 0 := by
    intro h0
    apply hx
    ext i
    simpa using congrFun h0 i
  have h1 := hpos (star ⇑x) hx'
  have h2 : (starRingEnd ℂ) (hermForm M (star ⇑x) (star ⇑x)) = hermForm M (star ⇑x) (star ⇑x) :=
    star_hermForm hM _ _
  have h3 : (x.sum fun i xi => x.sum fun j xj => star xi * M i j * xj) =
      ∑ i, ∑ j, star (x i) * M i j * x j := by
    rw [Finsupp.sum_fintype x (fun i xi => x.sum fun j xj => star xi * M i j * xj)
      (fun i => by simp [Finsupp.sum])]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Finsupp.sum_fintype x (fun j xj => star (x i) * M i j * xj) (fun j => by simp)
  have h4 : ∑ i, ∑ j, star (x i) * M i j * x j = hermForm M (star ⇑x) (star ⇑x) := by
    rw [hermForm_eq_sum]
    simp
  rw [h3, h4, Complex.lt_def]
  exact ⟨by simpa using h1, by simp [Complex.conj_eq_iff_im.mp h2]⟩

theorem fromCols_block {I : Type} [Fintype I] {p q : ℕ} (A : Matrix I (Fin p) ℂ) (B : Matrix I (Fin q) ℂ)
    (G₁ : Matrix (Fin p) (Fin p) ℂ) (G₂ : Matrix (Fin q) (Fin q) ℂ) :
    Matrix.fromCols A B * Matrix.fromBlocks G₁ 0 0 (-G₂) * (Matrix.fromCols A B)ᴴ =
      A * G₁ * Aᴴ - B * G₂ * Bᴴ := by
  rw [Matrix.fromCols_mul_fromBlocks, Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
    Matrix.fromCols_mul_fromRows]
  simp [sub_eq_add_neg]

private theorem add_mul_mul_conjTranspose_add_eq_of_two_smul {r p q : ℕ} (C : Matrix (Fin r) (Fin p ⊕ Fin q) ℂ)
    (V M N : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (key : V * ((2 : ℂ) • M) * Vᴴ = N) :
    (C * V + C * V) * M * (C * V + C * V)ᴴ = C * N * Cᴴ + C * N * Cᴴ := by
  rw [← key]
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.add_mul, Matrix.mul_add,
    Matrix.mul_smul, Matrix.smul_mul, two_smul, Matrix.mul_assoc]

theorem signature_of_factor {p q : ℕ} (M W : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)
    (G₁ : Matrix (Fin p) (Fin p) ℂ) (G₂ : Matrix (Fin q) (Fin q) ℂ) (h₁ : G₁.PosDef) (h₂ : G₂.PosDef)
    (hM : (2 : ℂ) • M = W * Matrix.fromBlocks G₁ 0 0 (-G₂) * Wᴴ) (hdet : M.det ≠ 0) :
    M.IsHermitian ∧ (∃ C : Matrix (Fin p) (Fin p ⊕ Fin q) ℂ, (C * M * Cᴴ).PosDef) ∧
      ∃ C : Matrix (Fin q) (Fin p ⊕ Fin q) ℂ, (-(C * M * Cᴴ)).PosDef := by
  have hN : (Matrix.fromBlocks G₁ 0 0 (-G₂))ᴴ = Matrix.fromBlocks G₁ 0 0 (-G₂) := by
    rw [Matrix.fromBlocks_conjTranspose, h₁.1.eq, Matrix.conjTranspose_neg, h₂.1.eq,
      Matrix.conjTranspose_zero, Matrix.conjTranspose_zero]
  have hMh : M.IsHermitian := by
    have h2 : ((2 : ℂ) • M)ᴴ = (2 : ℂ) • M := by
      rw [hM, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hN,
        Matrix.mul_assoc]
    rw [Matrix.conjTranspose_smul] at h2
    have h3 : (2 : ℂ) • Mᴴ = (2 : ℂ) • M := by simpa using h2
    exact smul_right_injective _ two_ne_zero h3
  have hW : IsUnit W.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    have h4 := congrArg Matrix.det hM
    rw [Matrix.det_smul, Matrix.det_mul, Matrix.det_mul, h0] at h4
    simp [hdet] at h4
  have hVW : W⁻¹ * W = 1 := Matrix.nonsing_inv_mul W hW
  have hWV : Wᴴ * (W⁻¹)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hVW, Matrix.conjTranspose_one]
  have key : W⁻¹ * ((2 : ℂ) • M) * (W⁻¹)ᴴ = Matrix.fromBlocks G₁ 0 0 (-G₂) := by
    rw [hM]
    calc W⁻¹ * (W * Matrix.fromBlocks G₁ 0 0 (-G₂) * Wᴴ) * (W⁻¹)ᴴ
        = (W⁻¹ * W) * Matrix.fromBlocks G₁ 0 0 (-G₂) * (Wᴴ * (W⁻¹)ᴴ) := by
          simp only [Matrix.mul_assoc]
      _ = Matrix.fromBlocks G₁ 0 0 (-G₂) := by rw [hVW, hWV, Matrix.one_mul, Matrix.mul_one]
  refine ⟨hMh, ⟨Matrix.fromCols (1 : Matrix (Fin p) (Fin p) ℂ) (0 : Matrix (Fin p) (Fin q) ℂ) * W⁻¹ +
      Matrix.fromCols (1 : Matrix (Fin p) (Fin p) ℂ) (0 : Matrix (Fin p) (Fin q) ℂ) * W⁻¹, ?_⟩,
    ⟨Matrix.fromCols (0 : Matrix (Fin q) (Fin p) ℂ) (1 : Matrix (Fin q) (Fin q) ℂ) * W⁻¹ +
      Matrix.fromCols (0 : Matrix (Fin q) (Fin p) ℂ) (1 : Matrix (Fin q) (Fin q) ℂ) * W⁻¹, ?_⟩⟩
  · rw [add_mul_mul_conjTranspose_add_eq_of_two_smul _ _ _ _ key, fromCols_block]
    simp only [Matrix.mul_one, Matrix.one_mul, Matrix.conjTranspose_one, Matrix.zero_mul, sub_zero]
    exact h₁.add h₁
  · rw [add_mul_mul_conjTranspose_add_eq_of_two_smul _ _ _ _ key, fromCols_block]
    simp only [Matrix.mul_one, Matrix.one_mul, Matrix.conjTranspose_one, Matrix.zero_mul, zero_sub,
      neg_add_rev, neg_neg]
    exact h₂.add h₂

theorem conj_cmHostRoot_ne_self (H : Host E) : starRingEnd ℂ H.rt0 ≠ H.rt0 := by
  intro h
  have him : H.rt0.im = 0 := Complex.conj_eq_iff_im.mp h
  have hre := congrArg Complex.re H.sqrt_neg_disc_sq
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  simp [sq, Complex.mul_re, him] at hre
  nlinarith [mul_self_nonneg H.rt0.re]

end GlobalTheory.CompanionTheory.Ar.Fl.SignTau

private theorem posDef_reindex_of_hermForm_re_pos {E : Type} [Field E] [NumberField E] [IsCMField E] {g n : ℕ}
    (ty : Fin g → (E →+* ℂ)) (σ : E →+* ℂ) (e : Fin n ≃ {i // ty i = σ})
    (Hm : Matrix (Fin g) (Fin g) ℂ) (hH : Hm.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) :
    (Matrix.of fun a b => Hm (e a) (e b)).PosDef := by
  classical
  apply GlobalTheory.CompanionTheory.Ar.Fl.SignTau.posDef_of_hermForm
  · ext a b
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply]
    exact hH.apply _ _
  · intro z hz
    let w : Fin g → ℂ := fun i => if h : ty i = σ then z (e.symm ⟨i, h⟩) else 0
    have hw : ∀ a, w (e a) = z a := fun a => by simp [w, (e a).2]
    have hw0 : ∀ i, ty i ≠ σ → w i = 0 := fun i hi => by simp [w, hi]
    have hwz : w ≠ 0 := by
      obtain ⟨a, ha⟩ := Function.ne_iff.mp hz
      exact fun h => ha (by simpa [h] using (hw a).symm)
    have key : hermForm Hm w w = hermForm (Matrix.of fun a b => Hm (e a) (e b)) z z := by
      rw [GlobalTheory.CompanionTheory.Ar.Flat.RiemannTau.hermForm_eq_sum, GlobalTheory.CompanionTheory.Ar.Flat.RiemannTau.hermForm_eq_sum]
      have h1 : ∀ j, ty j ≠ σ → ∑ k, w j * Hm j k * star (w k) = 0 := fun j hj => by
        simp [hw0 j hj]
      rw [GlobalTheory.CompanionTheory.Ar.Fl.SignTau.sum_type ty σ e _ h1]
      refine Finset.sum_congr rfl fun a _ => ?_
      have h2 : ∀ k, ty k ≠ σ → w (e a) * Hm (e a) k * star (w k) = 0 := fun k hk => by
        simp [hw0 k hk]
      rw [GlobalTheory.CompanionTheory.Ar.Fl.SignTau.sum_type ty σ e _ h2]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp [hw]
    rw [← key]
    exact hpos w hwz

theorem GlobalTheory.CompanionTheory.Ar.Fl.signature_tau_gram : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)) (p q : ℕ) (X : Fin p ⊕ Fin q → D.La) (τ : E →+* ℂ), IsPeriod D ty P → IsTypeFn H p q ty → LinearIndependent (𝓞 E) X → p + q = D.p + D.q → τ (H.rt : E) = H.rt0 → ((gramE D X).map fun a => Complex.I * τ a).IsHermitian ∧ (∃ C : Matrix (Fin p) (Fin p ⊕ Fin q) ℂ, (C * ((gramE D X).map fun a => Complex.I * τ a) * Cᴴ).PosDef) ∧ ∃ C : Matrix (Fin q) (Fin p ⊕ Fin q) ℂ, (-(C * ((gramE D X).map fun a => Complex.I * τ a) * Cᴴ)).PosDef := by
  intro E _ _ _ H D g ty P p q X τ hP hT hX hpq hτ
  obtain ⟨-, -, -, -, Hm, hH, hpos, hEF⟩ := id hP
  obtain ⟨-, hcomp, hC⟩ := GlobalTheory.CompanionTheory.Ar.Flat.riemann_tau_component E H D g ty P Hm hP hH hEF
  have hτc : ComplexEmbedding.conjugate τ (H.rt : E) ≠ H.rt0 := by
    rw [ComplexEmbedding.conjugate_coe_eq, hτ]
    exact GlobalTheory.CompanionTheory.Ar.Fl.SignTau.conj_cmHostRoot_ne_self H
  let e₁ : Fin p ≃ {i // ty i = τ} := (Finite.equivFinOfCardEq ((hT τ).1 hτ)).symm
  let e₂ : Fin q ≃ {i // ty i = ComplexEmbedding.conjugate τ} :=
    (Finite.equivFinOfCardEq ((hT (ComplexEmbedding.conjugate τ)).2 hτc)).symm
  let G₁ : Matrix (Fin p) (Fin p) ℂ := Matrix.of fun a b => Hm (e₁ a) (e₁ b)
  let G₂ : Matrix (Fin q) (Fin q) ℂ := (Matrix.of fun a b => Hm (e₂ a) (e₂ b))ᵀ
  let A : Matrix (Fin p ⊕ Fin q) (Fin p) ℂ := Matrix.of fun m a => P (X m) (e₁ a)
  let B : Matrix (Fin p ⊕ Fin q) (Fin q) ℂ := Matrix.of fun m b => star (P (X m) (e₂ b))
  have h₁ : G₁.PosDef := posDef_reindex_of_hermForm_re_pos ty τ e₁ Hm hH hpos
  have h₂ : G₂.PosDef := (posDef_reindex_of_hermForm_re_pos ty (ComplexEmbedding.conjugate τ) e₂ Hm hH hpos).transpose
  have hfac : (2 : ℂ) • ((gramE D X).map fun a => Complex.I * τ a) =
      Matrix.fromCols A B * Matrix.fromBlocks G₁ 0 0 (-G₂) * (Matrix.fromCols A B)ᴴ := by
    rw [GlobalTheory.CompanionTheory.Ar.Fl.SignTau.fromCols_block]
    ext m n
    have key := hcomp τ (X m) (X n)
    rw [GlobalTheory.CompanionTheory.Ar.Fl.SignTau.hermForm_tyPart ty τ e₁,
      GlobalTheory.CompanionTheory.Ar.Fl.SignTau.hermForm_tyPart ty (ComplexEmbedding.conjugate τ) e₂] at key
    have hA : (A * G₁ * Aᴴ) m n =
        ∑ a, ∑ b, P (X m) (e₁ a) * Hm (e₁ a) (e₁ b) * star (P (X n) (e₁ b)) := by
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, A, G₁, Finset.sum_mul]
      rw [Finset.sum_comm]
    have hB : (B * G₂ * Bᴴ) m n =
        star (∑ a, ∑ b, P (X m) (e₂ a) * Hm (e₂ a) (e₂ b) * star (P (X n) (e₂ b))) := by
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.transpose_apply, Matrix.of_apply, B, G₂,
        Finset.sum_mul, star_sum, star_mul', star_star]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [hH.apply]
    rw [Matrix.sub_apply, hA, hB, key]
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    rw [show gramE D X m n = sesq D (X m) (X n) from rfl]
    ring
  have hdetA : (gramE D X).det ≠ 0 := hC 0 (Fin p ⊕ Fin q) X (by simp [hpq]) hX
  have hdetM : ((gramE D X).map fun a => Complex.I * τ a).det ≠ 0 := by
    have hM' : ((gramE D X).map fun a => Complex.I * τ a) = Complex.I • (τ.mapMatrix (gramE D X)) := by
      ext m n
      simp [Matrix.map_apply]
    rw [hM', Matrix.det_smul, ← RingHom.map_det]
    exact mul_ne_zero (pow_ne_zero _ Complex.I_ne_zero) ((map_ne_zero τ).mpr hdetA)
  exact GlobalTheory.CompanionTheory.Ar.Fl.SignTau.signature_of_factor _ (Matrix.fromCols A B) G₁ G₂ h₁ h₂ hfac hdetM
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PeriodGramHermitianSignatureStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_gram_hermitian_signature : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)) (p q : ℕ) (X : Fin p ⊕ Fin q → D.La) (τ : E →+* ℂ), IsPeriod D ty P → IsTypeFn H p q ty → LinearIndependent (𝓞 E) X → p + q = D.p + D.q → τ (H.rt : E) = H.rt0 → ((gramE D X).map fun a => Complex.I * τ a).IsHermitian ∧ (∃ C : Matrix (Fin p) (Fin p ⊕ Fin q) ℂ, (C * ((gramE D X).map fun a => Complex.I * τ a) * Cᴴ).PosDef) ∧ ∃ C : Matrix (Fin q) (Fin p ⊕ Fin q) ℂ, (-(C * ((gramE D X).map fun a => Complex.I * τ a) * Cᴴ)).PosDef := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.signature_tau_gram | exact GlobalTheory.CompanionTheory.Ar.Fl.signature_tau_gram | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.signature_tau_gram <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsIntegralPosDefPerturbation
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsIntegralPosDefPerturbation
open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem frame_congr_posDef_on_places : ∀ (E : Type) [Field E] [NumberField E] (Ψ : Set (E →+* ℂ)) (I J : Type) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] (M : (E →+* ℂ) → Matrix J J ℂ) (C : (E →+* ℂ) → Matrix I J ℂ) (X₀ : Matrix I J (𝓞 E)) (n : ℕ), n ≠ 0 → (∀ τ ∈ Ψ, ComplexEmbedding.conjugate τ ∉ Ψ) → (∀ τ ∈ Ψ, (M τ).IsHermitian ∧ (C τ * M τ * (C τ)ᴴ).PosDef) → ∃ Y : Matrix I J (𝓞 E), ∀ τ ∈ Ψ, (((X₀ + n • Y).map fun a => τ (a : E)) * M τ * ((X₀ + n • Y).map fun a => τ (a : E))ᴴ).PosDef :=
  @PositivityTheory.Xgf.exists_integral_posDef_perturbation

end GlobalTheory.CompanionTheory.Ar.Fl
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsIntegralPosDefPerturbationStatement
open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_posDef_perturbation : ∀ (E : Type) [Field E] [NumberField E] (Ψ : Set (E →+* ℂ)) (I J : Type) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] (M : (E →+* ℂ) → Matrix J J ℂ) (C : (E →+* ℂ) → Matrix I J ℂ) (X₀ : Matrix I J (𝓞 E)) (n : ℕ), n ≠ 0 → (∀ τ ∈ Ψ, ComplexEmbedding.conjugate τ ∉ Ψ) → (∀ τ ∈ Ψ, (M τ).IsHermitian ∧ (C τ * M τ * (C τ)ᴴ).PosDef) → ∃ Y : Matrix I J (𝓞 E), ∀ τ ∈ Ψ, (((X₀ + n • Y).map fun a => τ (a : E)) * M τ * ((X₀ + n • Y).map fun a => τ (a : E))ᴴ).PosDef := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.frame_congr_posDef_on_places | exact GlobalTheory.CompanionTheory.Ar.Fl.frame_congr_posDef_on_places | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.frame_congr_posDef_on_places <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.NegDefBlockOfPosDef
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.NegDefBlockOfPosDef
open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl.Sylvester

theorem neg_posDef_of_compl_posDef : ∀ (p q : ℕ) (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin q) (Fin q) ℂ) (C : Matrix (Fin q) (Fin p ⊕ Fin q) ℂ), A.PosDef → B.IsHermitian → (-(C * Matrix.fromBlocks A 0 0 B * Cᴴ)).PosDef → (-B).PosDef :=
  @PositivityTheory.Xgf.negDef_block_of_posDef

end GlobalTheory.CompanionTheory.Ar.Fl.Sylvester
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.NegDefBlockOfPosDefStatement
open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.negDef_block_of_posDef : ∀ (p q : ℕ) (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin q) (Fin q) ℂ) (C : Matrix (Fin q) (Fin p ⊕ Fin q) ℂ), A.PosDef → B.IsHermitian → (-(C * Matrix.fromBlocks A 0 0 B * Cᴴ)).PosDef → (-B).PosDef := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.Sylvester.neg_posDef_of_compl_posDef | exact GlobalTheory.CompanionTheory.Ar.Fl.Sylvester.neg_posDef_of_compl_posDef | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.Sylvester.neg_posDef_of_compl_posDef <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.UltrametricDetNormStable
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.UltrametricDetNormStable
open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem norm_det_eq_of_entries_close : ∀ (A : Type) [NormedField A] [IsUltrametricDist A] (I : Type) [Fintype I] [DecidableEq I] (M M' : Matrix I I A) (r : ℝ), 0 < r → (∀ a b, ‖M a b‖ ≤ r) → (∀ a b, ‖M' a b - M a b‖ < r) → ‖M.det‖ = r ^ Fintype.card I → ‖M'.det‖ = r ^ Fintype.card I :=
  @PositivityTheory.Xgf.ultrametric_det_norm_stable

end GlobalTheory.CompanionTheory.Ar.Fl
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.UltrametricDetNormStableStatement
open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ultrametric_det_norm_stable : ∀ (A : Type) [NormedField A] [IsUltrametricDist A] (I : Type) [Fintype I] [DecidableEq I] (M M' : Matrix I I A) (r : ℝ), 0 < r → (∀ a b, ‖M a b‖ ≤ r) → (∀ a b, ‖M' a b - M a b‖ < r) → ‖M.det‖ = r ^ Fintype.card I → ‖M'.det‖ = r ^ Fintype.card I := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.norm_det_eq_of_entries_close | exact GlobalTheory.CompanionTheory.Ar.Fl.norm_det_eq_of_entries_close | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.norm_det_eq_of_entries_close <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PurePeriodLocalBasisExists
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fl.DSplit

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem norm_le_one_of_int {C : Type} [NormedField C] [IsUltrametricDist C] {x : C}
    (hx : @IsIntegral ℤ C _ _ (Ring.toIntAlgebra C) x) : ‖x‖ ≤ 1 := by
  have h : x ∈ (NormedField.valuation (K := C)).integer :=
    (Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral hx.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h

theorem norm_int_le (ℓ : Nat.Primes) (j : E →+* ℂ_[ℓ]) (b : 𝓞 E) : ‖j (b : E)‖ ≤ 1 :=
  norm_le_one_of_int (map_isIntegral_int j b.isIntegral_coe)

theorem norm_prime_lt (ℓ : Nat.Primes) : ‖(((ℓ : ℕ) : ℂ_[ℓ]))‖ < 1 := by
  have h : (((ℓ : ℕ) : ℂ_[ℓ])) = algebraMap ℚ_[ℓ] ℂ_[ℓ] ((ℓ : ℕ) : ℚ_[ℓ]) := by simp
  rw [h, norm_algebraMap', Padic.norm_p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast ℓ.2.one_lt)

theorem exists_bound (D : Datum H) (ℓ : Nat.Primes) (j : E →+* ℂ_[ℓ]) :
    ∃ r : ℝ, 0 < r ∧ Real.log r = -logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) ∧
      ∀ x y, ‖j (sesq D x y)‖ ≤ r := by
  have hinj : Function.Injective (j.comp (algebraMap (𝓞 E) E)) :=
    j.injective.comp (RingOfIntegers.coe_injective)
  obtain ⟨a, ha, ha0, -, hlog⟩ := GlobalTheory.T.padic_logIdeal_max_element E ℓ (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) hinj
    differentIdeal_ne_bot
  have hn : 0 < ‖j (a : E)‖ := by
    rw [norm_pos_iff]
    intro h
    exact ha0 (hinj (by simpa using h))
  refine ⟨‖j (a : E)‖⁻¹, inv_pos.2 hn, ?_, fun x y => ?_⟩
  · rw [Real.log_inv]
    exact congrArg Neg.neg hlog.symm
  · obtain ⟨b, hb⟩ := (GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D).2.2.2.2.2.2 a ha x y
    have h1 : ‖j (a : E)‖ * ‖j (sesq D x y)‖ = ‖j (b : E)‖ := by rw [← norm_mul, ← map_mul, hb]
    have h2 := norm_int_le ℓ j b
    rw [← h1] at h2
    rw [← one_div, le_div_iff₀ hn]
    linarith

theorem sesq_sum_left (D : Datum H) {J : Type} (s : Finset J) (f : J → D.La) (y : D.La) :
    sesq D (∑ m ∈ s, f m) y = ∑ m ∈ s, sesq D (f m) y := by
  let φ : D.La →+ E := AddMonoidHom.mk' (fun x => sesq D x y) (fun a b => (GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D).2.1 a b y)
  exact map_sum φ f s

theorem sesq_sum_right (D : Datum H) {J : Type} (s : Finset J) (f : J → D.La) (y : D.La) :
    sesq D y (∑ m ∈ s, f m) = ∑ m ∈ s, sesq D y (f m) := by
  let φ : D.La →+ E := AddMonoidHom.mk' (fun x => sesq D y x) (fun a b => (GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D).2.2.1 y a b)
  exact map_sum φ f s

theorem sesq_comb (D : Datum H) {J : Type} [Fintype J] (x : J → D.La) (u v : J → 𝓞 E) :
    sesq D (∑ m, u m • x m) (∑ n, v n • x n) =
      ∑ n, (∑ m, (u m : E) * sesq D (x m) (x n)) * IsCMField.complexConj E (v n : E) := by
  rw [sesq_sum_right]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [(GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D).2.2.2.2.1, sesq_sum_left, mul_comm]
  congr 1
  exact Finset.sum_congr rfl fun m _ => (GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D).2.2.2.1 _ _ _

theorem gram_comb_map (D : Datum H) (τ : E →+* ℂ) {I J : Type} [Fintype J] (x : J → D.La)
    (X : Matrix I J (𝓞 E)) :
    ((gramE D (fun a => ∑ m, X a m • x m)).map fun a => Complex.I * τ a) =
      (X.map fun a => τ (a : E)) * ((gramE D x).map fun a => Complex.I * τ a) * (X.map fun a => τ (a : E))ᴴ := by
  ext a b
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.map_apply, gramE, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, sesq_comb,
    map_sum, map_mul, Finset.mul_sum, Finset.sum_mul, IsCMField.complexEmbedding_complexConj, starRingEnd_apply]
  refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
  ring

theorem norm_diff_lt (D : Datum H) (ℓ : Nat.Primes) (j : E →+* ℂ_[ℓ]) {r : ℝ} (hr : 0 < r)
    (hb : ∀ x y, ‖j (sesq D x y)‖ ≤ r) (u u' v v' : D.La) :
    ‖j (sesq D (u + ((ℓ : ℕ) : 𝓞 E) • v) (u' + ((ℓ : ℕ) : 𝓞 E) • v')) - j (sesq D u u')‖ < r := by
  obtain ⟨-, hl, hr', hsl, hsr, -, -⟩ := GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D
  have hcast : ((((ℓ : ℕ) : 𝓞 E)) : E) = ((ℓ : ℕ) : E) := map_natCast (algebraMap (𝓞 E) E) _
  have e : j (sesq D (u + ((ℓ : ℕ) : 𝓞 E) • v) (u' + ((ℓ : ℕ) : 𝓞 E) • v')) - j (sesq D u u') =
      ((ℓ : ℕ) : ℂ_[ℓ]) * (j (sesq D v u') + j (sesq D u v') + ((ℓ : ℕ) : ℂ_[ℓ]) * j (sesq D v v')) := by
    rw [hl, hr', hr', hsl, hsl, hsr, hsr, hcast, map_natCast (IsCMField.complexConj E)]
    simp only [map_add (f := _), map_mul, map_natCast]
    ring
  have hc := norm_prime_lt ℓ
  have hc0 : 0 ≤ ‖(((ℓ : ℕ) : ℂ_[ℓ]))‖ := norm_nonneg _
  have h3 : ‖((ℓ : ℕ) : ℂ_[ℓ]) * j (sesq D v v')‖ ≤ r := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hc.le).trans (hb v v')
  have h4 : ‖j (sesq D v u') + j (sesq D u v') + ((ℓ : ℕ) : ℂ_[ℓ]) * j (sesq D v v')‖ ≤ r :=
    (IsUltrametricDist.norm_add_le_max _ _).trans (max_le
      ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hb _ _) (hb _ _))) h3)
  rw [e, norm_mul]
  calc _ ≤ ‖(((ℓ : ℕ) : ℂ_[ℓ]))‖ * r := mul_le_mul_of_nonneg_left h4 hc0
    _ < 1 * r := mul_lt_mul_of_pos_right hc hr
    _ = r := one_mul r

theorem conj_ne (τ : E →+* ℂ) (h : τ (H.rt : E) = H.rt0) :
    (ComplexEmbedding.conjugate τ) (H.rt : E) ≠ H.rt0 := by
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have hsq := H.sqrt_neg_disc_sq
  have him : H.rt0 ≠ 0 := by
    intro h0
    rw [h0] at hsq
    simp at hsq
    exact H.d_prime.ne_zero hsq
  have h1 : H.rt0.re * H.rt0.re - H.rt0.im * H.rt0.im = -(H.d : ℝ) := by
    have := congrArg Complex.re hsq
    simpa [pow_two] using this
  have h2 : H.rt0.re * H.rt0.im + H.rt0.im * H.rt0.re = 0 := by
    have := congrArg Complex.im hsq
    simpa [pow_two] using this
  have h3 : H.rt0.re * H.rt0.im = 0 := by linarith [mul_comm H.rt0.re H.rt0.im]
  have hre : H.rt0.re = 0 := by
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact h4
    · rw [h4] at h1
      nlinarith [mul_self_nonneg H.rt0.re]
  rw [ComplexEmbedding.conjugate_coe_eq, h]
  intro h5
  have h6 := congrArg Complex.im h5
  simp at h6
  exact him (Complex.ext hre (by simpa using (by linarith : H.rt0.im = 0)))

theorem exists_emb (E : Type) [Field E] [NumberField E] (ℓ : Nat.Primes) : Nonempty (E →+* ℂ_[ℓ]) :=
  ⟨(IsAlgClosed.lift : E →ₐ[ℚ] ℂ_[ℓ]).toRingHom⟩

theorem norm_det_close (D : Datum H) (p : ℕ) (ℓ : Nat.Primes) (x x' w : Fin p → D.La)
    (hx' : ∀ a, x' a = x a + ((ℓ : ℕ) : 𝓞 E) • w a) (hx0 : (gramE D x).det ≠ 0)
    (hxn : ∀ j : E →+* ℂ_[ℓ], Real.log ‖j (gramE D x).det‖ =
      -(p : ℝ) * logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))) :
    (gramE D x').det ≠ 0 ∧ ∀ j : E →+* ℂ_[ℓ], Real.log ‖j (gramE D x').det‖ =
      -(p : ℝ) * logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) := by
  have key : ∀ j : E →+* ℂ_[ℓ], 0 < ‖j (gramE D x').det‖ ∧ Real.log ‖j (gramE D x').det‖ =
      -(p : ℝ) * logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) := by
    intro j
    obtain ⟨r, hr, hlog, hb⟩ := exists_bound D ℓ j
    have hd0 : 0 < ‖j (gramE D x).det‖ := norm_pos_iff.2 ((map_ne_zero j).2 hx0)
    have hdet : ‖((gramE D x).map j).det‖ = r ^ Fintype.card (Fin p) := by
      have e : ((gramE D x).map j).det = j (gramE D x).det := (RingHom.map_det j _).symm
      rw [e, Fintype.card_fin, ← Real.exp_log hd0, hxn j, ← Real.exp_log (pow_pos hr p), Real.log_pow, hlog]
      congr 1
      ring
    have h := GlobalTheory.T.ultrametric_det_norm_stable ℂ_[ℓ] (Fin p) ((gramE D x).map j) ((gramE D x').map j) r hr
      (fun a b => hb _ _) (fun a b => by
        simp only [Matrix.map_apply, gramE, Matrix.of_apply, hx']
        exact norm_diff_lt D ℓ j hr hb _ _ _ _) hdet
    have e' : ((gramE D x').map j).det = j (gramE D x').det := (RingHom.map_det j _).symm
    rw [e', Fintype.card_fin] at h
    refine ⟨by rw [h]; exact pow_pos hr p, ?_⟩
    rw [h, Real.log_pow, hlog]
    ring
  obtain ⟨j⟩ := exists_emb E ℓ
  refine ⟨fun h0 => ?_, fun j => (key j).2⟩
  have := (key j).1
  rw [h0] at this
  simp at this

theorem neg_compl (D : Datum H) {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P₀ : D.La →+ (Fin g → ℂ)} {p q : ℕ}
    (hP₀ : IsPeriod D ty P₀) (hty : IsTypeFn H p q ty) (hpq : p + q = D.p + D.q)
    (x : Fin p ⊕ Fin q → D.La) (hli : LinearIndependent (𝓞 E) x)
    (horth : ∀ a b, sesq D (x (.inl a)) (x (.inr b)) = 0) (τ : E →+* ℂ) (hτ : τ (H.rt : E) = H.rt0)
    (hpos : ((gramE D (x ∘ Sum.inl)).map fun a => Complex.I * τ a).PosDef) :
    (-((gramE D (x ∘ Sum.inr)).map fun a => Complex.I * τ a)).PosDef := by
  obtain ⟨hH, -, C, hC⟩ := GlobalTheory.T.period_gram_hermitian_signature E H D g ty P₀ p q x τ hP₀ hty hli hpq hτ
  have hblk : ((gramE D x).map fun a => Complex.I * τ a) =
      Matrix.fromBlocks ((gramE D (x ∘ Sum.inl)).map fun a => Complex.I * τ a) 0 0
        ((gramE D (x ∘ Sum.inr)).map fun a => Complex.I * τ a) := by
    ext (a | a) (b | b)
    · simp [gramE]
    · simp [gramE, horth]
    · have h := (GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D).2.2.2.2.2.1 (x (.inl b)) (x (.inr a))
      simp [gramE, h, horth]
    · simp [gramE]
  rw [hblk] at hC
  refine GlobalTheory.T.negDef_block_of_posDef p q _ _ C hpos ?_ hC
  ext i k
  have h := congrFun (congrFun hH (.inr i)) (.inr k)
  simpa [gramE] using h

end GlobalTheory.CompanionTheory.Ar.Fl.DSplit

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem GlobalTheory.CompanionTheory.Ar.Fl.DSplit.exists_split_period : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P₀ : D.La →+ (Fin g → ℂ)) (p q : ℕ) (ℓ : Nat.Primes), IsPeriod D ty P₀ → IsTypeFn H p q ty → p + q = D.p + D.q → ∃ (P : D.La →+ (Fin g → ℂ)) (hP : IsPeriod D ty P) (x : Fin p ⊕ Fin q → D.La), IsLocBasis (𝓞 E) ℓ x ∧ IsPure hP x := by
  intro E _ _ _ H D g ty P₀ p q ℓ hP₀ hty hpq
  obtain ⟨x, hxb, hx0, hxn⟩ := GlobalTheory.T.local_basis_gram_determinant_bound E H D p q ℓ hpq
  have hli := hxb.1
  let Ψ : Set (E →+* ℂ) := {τ | τ (H.rt : E) = H.rt0}
  let M : (E →+* ℂ) → Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ :=
    fun τ => (gramE D x).map fun a => Complex.I * τ a
  have hC : ∀ τ : E →+* ℂ, ∃ C : Matrix (Fin p) (Fin p ⊕ Fin q) ℂ, τ ∈ Ψ → (C * M τ * Cᴴ).PosDef := by
    intro τ
    by_cases h : τ ∈ Ψ
    · obtain ⟨C, hC⟩ := (GlobalTheory.T.period_gram_hermitian_signature E H D g ty P₀ p q x τ hP₀ hty hli hpq h).2.1
      exact ⟨C, fun _ => hC⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose C hC using hC
  obtain ⟨Y, hY⟩ := GlobalTheory.T.exists_integral_posDef_perturbation E Ψ (Fin p) (Fin p ⊕ Fin q) M C (Matrix.fromCols 1 0) (ℓ : ℕ) ℓ.2.ne_zero
    (fun τ h => DSplit.conj_ne τ h)
    (fun τ h => ⟨(GlobalTheory.T.period_gram_hermitian_signature E H D g ty P₀ p q x τ hP₀ hty hli hpq h).1, hC τ h⟩)
  let X : Matrix (Fin p) (Fin p ⊕ Fin q) (𝓞 E) := Matrix.fromCols 1 0 + (ℓ : ℕ) • Y
  let x' : Fin p → D.La := fun a => ∑ m, X a m • x m
  let w : Fin p → D.La := fun a => ∑ m, Y a m • x m
  have hx' : ∀ a, x' a = (x ∘ Sum.inl) a + (((ℓ : ℕ) : 𝓞 E)) • w a := by
    intro a
    simp only [x', w, X, Matrix.add_apply, Matrix.smul_apply, add_smul, Finset.sum_add_distrib, Finset.smul_sum,
      nsmul_eq_mul, mul_smul, Function.comp]
    congr 1
    simp [Fintype.sum_sum_type, Matrix.one_apply, ite_smul]
  obtain ⟨hd0, hdn⟩ := DSplit.norm_det_close D p ℓ (x ∘ Sum.inl) x' w hx' hx0 hxn
  obtain ⟨x₂, hx₂, hb₂, horth⟩ := GlobalTheory.T.exists_orthogonal_local_basis E H D p q ℓ x' hpq hd0 hdn
  have hpos : ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 →
      ((gramE D (x₂ ∘ Sum.inl)).map fun a => Complex.I * τ a).PosDef := by
    intro τ hτ
    rw [hx₂, DSplit.gram_comb_map D τ x X]
    exact hY τ hτ
  obtain ⟨P, hP, hpure⟩ := GlobalTheory.T.gram_signature_orthogonal_split E H D g ty p q x₂ hty hpq hb₂.1 horth fun τ hτ =>
    ⟨hpos τ hτ, DSplit.neg_compl D hP₀ hty hpq x₂ hb₂.1 horth τ hτ (hpos τ hτ)⟩
  exact ⟨P, hP, x₂, hb₂, hpure⟩
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PurePeriodLocalBasisExistsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pure_period_local_basis_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P₀ : D.La →+ (Fin g → ℂ)) (p q : ℕ) (ℓ : Nat.Primes), IsPeriod D ty P₀ → IsTypeFn H p q ty → p + q = D.p + D.q → ∃ (P : D.La →+ (Fin g → ℂ)) (hP : IsPeriod D ty P) (x : Fin p ⊕ Fin q → D.La), IsLocBasis (𝓞 E) ℓ x ∧ IsPure hP x := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.DSplit.exists_split_period | exact GlobalTheory.CompanionTheory.Ar.Fl.DSplit.exists_split_period | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.DSplit.exists_split_period <;> assumption)
end
