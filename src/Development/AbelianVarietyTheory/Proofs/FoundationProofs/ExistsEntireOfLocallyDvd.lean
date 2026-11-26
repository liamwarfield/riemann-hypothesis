module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNsmulPaddedLatticeMemBasisProduct

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEntireOfLocallyDvd
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

open Filter Topology

namespace GlobalTheory.EvenTheta

theorem exists_entire_of_locally_dvd {F S : ℂ → ℂ} (hS : Dense {z | S z ≠ 0})
    (h : ∀ w, ∃ g : ℂ → ℂ, AnalyticAt ℂ g w ∧ ∀ᶠ z in 𝓝 w, F z = S z * g z) :
    ∃ G : ℂ → ℂ, Differentiable ℂ G ∧ ∀ z, F z = S z * G z := by
  choose g hg hF using h
  refine ⟨fun w => g w w, fun w => ?_, fun z => (hF z).self_of_nhds⟩
  refine (hg w).differentiableAt.congr_of_eventuallyEq ?_
  filter_upwards [(hg w).eventually_analyticAt, (hF w).eventually_nhds] with z h1 h2
  refine tendsto_nhds_unique_of_frequently_eq (hg z).continuousAt h1.continuousAt ?_
  have h3 : ∃ᶠ y in 𝓝 z, S y ≠ 0 := mem_closure_iff_frequently.1 (hS z)
  refine (h3.and_eventually (h2.and (hF z))).mono fun y hy => ?_
  exact mul_left_cancel₀ hy.1 (hy.2.2.symm.trans hy.2.1)

theorem IsLat.exists_sg_add {Λ : AddSubgroup ℂ} (h : IsLat Λ) {ω : ℂ} (hω : ω ∈ Λ) :
    ∃ c : ℂ → ℂ, Differentiable ℂ c ∧ ∀ z, sgStar Λ (z + ω) = c z * sgStar Λ z := by
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair Λ h
  rw [GlobalTheory.OddTheta.sgStar_eq L Λ hL]
  refine ⟨_, ?_, GlobalTheory.canonicalSigma_add L ((hL ω).1 hω)⟩
  unfold GlobalTheory.latticeForm
  fun_prop

theorem exists_eq_sg_sq_mul : ∀ Λ : AddSubgroup ℂ, IsLat Λ → ∀ (k : ℕ) (F : ℂ → ℂ), Differentiable ℂ F → (∀ z, F (-z) = F z) → F 0 = 0 → (∀ ω ∈ Λ, ∀ z, F (z + ω) * sgStar Λ z ^ (2 * (k + 1)) = F z * sgStar Λ (z + ω) ^ (2 * (k + 1))) → ∃ G : ℂ → ℂ, Differentiable ℂ G ∧ (∀ z, G (-z) = G z) ∧ (∀ z, F z = sgStar Λ z ^ 2 * G z) ∧ ∀ ω ∈ Λ, ∀ z, G (z + ω) * sgStar Λ z ^ (2 * k) = G z * sgStar Λ (z + ω) ^ (2 * k) := by
  intro Λ hΛ k F hF he h0 hlaw
  have hσ := hΛ.differentiable
  have hσc := hσ.continuous
  have hFc := hF.continuous
  have hne : ∀ z ∉ Λ, sgStar Λ z ≠ 0 := fun z hz => (hΛ.sg_eq_zero z).not.2 hz
  obtain ⟨h, hh, eh⟩ := GlobalTheory.exists_eq_add_sq_mul_of_even (hF.analyticAt 0) he
  have hu : AnalyticAt ℂ (dslope (sgStar Λ) 0) 0 :=
    (differentiableOn_univ.1
      ((Complex.differentiableOn_dslope univ_mem).2 hσ.differentiableOn)).analyticAt 0
  have hu0 : dslope (sgStar Λ) 0 0 ≠ 0 := by
    rw [dslope_same, (GlobalTheory.OddTheta.sgStar_laws Λ hΛ).1.2.1]
    exact one_ne_zero
  have eu : ∀ z, sgStar Λ z = z * dslope (sgStar Λ) 0 z := fun z => by
    have := sub_smul_dslope (sgStar Λ) 0 z
    rw [(hΛ.sg_eq_zero 0).2 Λ.zero_mem] at this
    simpa using this.symm
  obtain ⟨G, hG, eG⟩ := exists_entire_of_locally_dvd (F := F) (S := fun z => sgStar Λ z ^ 2)
    (hΛ.dense_compl.mono fun z hz => pow_ne_zero 2 (hne z hz)) fun w => by
      by_cases hw : w ∈ Λ
      · obtain ⟨c, hc, ec⟩ := hΛ.exists_sg_add hw
        have hcc := hc.continuous
        have eF : ∀ z, F (z + w) = c z ^ (2 * (k + 1)) * F z := fun z => by
          refine congrFun (Continuous.ext_on hΛ.dense_compl (f := fun z => F (z + w))
            (g := fun z => c z ^ (2 * (k + 1)) * F z) (by fun_prop) (by fun_prop) fun z hz => ?_) z
          refine mul_right_cancel₀ (pow_ne_zero (2 * (k + 1)) (hne z hz)) ?_
          beta_reduce
          rw [hlaw w hw, ec]
          ring
        have hs : AnalyticAt ℂ (fun y : ℂ => y - w) w := by fun_prop
        have ha : AnalyticAt ℂ
            (fun z => c z ^ (2 * k) * h z / dslope (sgStar Λ) 0 z ^ 2) 0 :=
          (((hc.analyticAt 0).pow _).mul hh).div (hu.pow 2) (pow_ne_zero 2 hu0)
        refine ⟨_, ha.comp_of_eq hs (sub_self w), ?_⟩
        filter_upwards [(hu.comp_of_eq hs (sub_self w)).continuousAt.eventually_ne
          (y := 0) (by simpa using hu0)] with y hy
        obtain ⟨z, rfl⟩ : ∃ z, y = z + w := ⟨y - w, by ring⟩
        simp only [Function.comp, add_sub_cancel_right] at hy ⊢
        rw [eF, ec, eh, h0, eu z]
        field_simp
        ring
      · refine ⟨fun z => F z / sgStar Λ z ^ 2, (hF.analyticAt w).div ((hσ.analyticAt w).pow 2)
          (pow_ne_zero 2 (hne w hw)), ?_⟩
        filter_upwards [hσc.continuousAt.eventually_ne (hne w hw)] with y hy
        field_simp
  have hGc := hG.continuous
  refine ⟨G, hG, fun z => ?_, eG, fun ω hω z => ?_⟩
  · refine congrFun (Continuous.ext_on hΛ.dense_compl (f := fun z => G (-z)) (by fun_prop) hGc
      fun z hz => ?_) z
    refine mul_left_cancel₀ (pow_ne_zero 2 (hne z hz)) ?_
    have h1 := eG (-z)
    rw [he, hΛ.sg_neg, neg_sq] at h1
    exact h1.symm.trans (eG z)
  · refine congrFun (Continuous.ext_on hΛ.dense_compl
      (f := fun z => G (z + ω) * sgStar Λ z ^ (2 * k))
      (g := fun z => G z * sgStar Λ (z + ω) ^ (2 * k)) (by fun_prop) (by fun_prop)
      fun z hz => ?_) z
    have hz' : z + ω ∉ Λ := fun h' => hz (by simpa using Λ.sub_mem h' hω)
    refine mul_left_cancel₀
      (mul_ne_zero (pow_ne_zero 2 (hne z hz)) (pow_ne_zero 2 (hne _ hz'))) ?_
    have h1 := hlaw ω hω z
    rw [eG z, eG (z + ω)] at h1
    beta_reduce at h1 ⊢
    linear_combination h1

end GlobalTheory.EvenTheta
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTraceOneEvenNormUnitAtTwo
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTraceOneEvenNormUnitAtTwo
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

namespace GlobalTheory.EvenTheta

theorem norm_eq_one_or_of_add_eq_one {L : Type*} [NormedField L] [IsUltrametricDist L] {b c : L}
    (h : b + c = 1) (hn : ‖b * c‖ < 1) : ‖b‖ = 1 ∨ ‖c‖ = 1 := by
  by_contra hne
  push_neg at hne
  obtain ⟨hb, hc⟩ := hne
  rw [norm_mul] at hn
  have h1 : ‖c‖ = max 1 ‖b‖ := by
    have : c = 1 + -b := by linear_combination h
    rw [this, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by simpa using hb.symm)]
    simp
  have h2 : ‖b‖ = max 1 ‖c‖ := by
    have : b = 1 + -c := by linear_combination h
    rw [this, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by simpa using hc.symm)]
    simp
  have h3 : 1 ≤ ‖c‖ := h1 ▸ le_max_left _ _
  have h4 : 1 ≤ ‖b‖ := h2 ▸ le_max_left _ _
  nlinarith

theorem norm_two_mul_natCast_lt_one (k : ℕ) : ‖((2 * k : ℕ) : ℂ_[2])‖ < 1 := by
  have h2 : ‖(2 : ℂ_[2])‖ < 1 := by
    have : (2 : ℂ_[2]) = algebraMap ℚ_[2] ℂ_[2] ((2 : ℕ) : ℚ_[2]) := by simp [map_ofNat]
    rw [this, norm_algebraMap']
    exact Padic.norm_p_lt_one
  have hk : ‖(k : ℂ_[2])‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ k
  push_cast
  rw [norm_mul]
  nlinarith [norm_nonneg (k : ℂ_[2]), norm_nonneg (2 : ℂ_[2])]

theorem exists_int_trace_one_unit_at_two :
    ∀ (D : D7) (lam : Qbar →+* ℂ_[2]), ∃ (a : 𝓞 D.host.K) (β : ℂ) (k : ℕ), D.host.φ₀ (((a : D.host.K) : D.host.E)) = β ∧ β ∈ Qbar ∧ ‖lamC lam β‖ = 1 ∧ β + starRingEnd ℂ β = 1 ∧ β * starRingEnd ℂ β = ((2 * k : ℕ) : ℂ) ∧ ∀ (Λ : AddSubgroup ℂ) (t₀ : ℂ), GL3Theta.IsTwoTorsionPointUnkilled D Λ t₀ → β * t₀ ∉ Λ ∧ (1 - β) * t₀ ∉ Λ := by
  intro D lam
  have hm : ∀ x, D.host.φ₀ x ∈ Qbar := fun x => by
    rw [mem_algebraicClosure_iff]
    exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom D.host.φ₀.toRatAlgHom
  obtain ⟨a, ha⟩ := GlobalTheory.NormSum.exists_integer_map_eq_w0 D
  have hd16 : D.host.d % 16 = 7 := D.host.hyp.2.2.2.1
  obtain ⟨k, hk⟩ : ∃ k : ℕ, D.host.d + 1 = 8 * k := ⟨(D.host.d + 1) / 8, by omega⟩
  have hk' : (D.host.d : ℂ) + 1 = 8 * (k : ℂ) := by exact_mod_cast hk
  have hs : ((Real.sqrt D.host.d : ℝ) : ℂ) ^ 2 = (D.host.d : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    simp
  have hw : StandardLatticesGL3.w0 D = (1 + Complex.I * (Real.sqrt D.host.d : ℂ)) / 2 := rfl
  have hw' : 1 - StandardLatticesGL3.w0 D = (1 - Complex.I * (Real.sqrt D.host.d : ℂ)) / 2 := by
    rw [hw]; ring
  have hc : starRingEnd ℂ (StandardLatticesGL3.w0 D) = 1 - StandardLatticesGL3.w0 D := by
    rw [hw', hw, map_div₀, map_add (f := _), map_mul, map_one, map_ofNat, Complex.conj_I, Complex.conj_ofReal]
    ring
  have hp : StandardLatticesGL3.w0 D * (1 - StandardLatticesGL3.w0 D) = ((2 * k : ℕ) : ℂ) := by
    rw [hw', hw]
    push_cast
    linear_combination (1 / 4 : ℂ) * hk' + (1 / 4 : ℂ) * hs
      - (1 / 4 : ℂ) * ((Real.sqrt D.host.d : ℝ) : ℂ) ^ 2 * Complex.I_sq
  have hQ : StandardLatticesGL3.w0 D ∈ Qbar := ha ▸ hm _
  have hQ' : 1 - StandardLatticesGL3.w0 D ∈ Qbar := Qbar.sub_mem Qbar.one_mem hQ
  have hadd : lamC lam (StandardLatticesGL3.w0 D) + lamC lam (1 - StandardLatticesGL3.w0 D) = 1 := by
    simp only [lamC, dif_pos hQ, dif_pos hQ']
    rw [← map_add (f := _), ← map_one lam]
    congr 1
    apply Subtype.ext
    simp
  have hmul : lamC lam (StandardLatticesGL3.w0 D) * lamC lam (1 - StandardLatticesGL3.w0 D) = ((2 * k : ℕ) : ℂ_[2]) := by
    simp only [lamC, dif_pos hQ, dif_pos hQ']
    rw [← map_mul, ← map_natCast lam]
    congr 1
    apply Subtype.ext
    exact hp.trans (by simp; exact Or.inl rfl)
  rcases norm_eq_one_or_of_add_eq_one hadd (hmul ▸ norm_two_mul_natCast_lt_one k) with h | h
  · refine ⟨a, StandardLatticesGL3.w0 D, k, ha, hQ, h, by rw [hc]; ring, by rw [hc, hp], ?_⟩
    intro Λ t ht
    exact ⟨ht.2.1, hw' ▸ ht.2.2⟩
  · refine ⟨1 - a, 1 - StandardLatticesGL3.w0 D, k, ?_, hQ', h, ?_, ?_, ?_⟩
    · rw [← ha]
      simp
    · rw [map_sub, map_one, hc]; ring
    · rw [map_sub, map_one, hc, ← hp]; ring
    · intro Λ t ht
      rw [sub_sub_cancel]
      exact ⟨hw' ▸ ht.2.2, ht.2.1⟩

end GlobalTheory.EvenTheta
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTraceOneEvenNormUnitAtTwoStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_traceOne_evenNorm_unit_at_two : ∀ (D : D7) (lam : Qbar →+* ℂ_[2]), ∃ (a : 𝓞 D.host.K) (β : ℂ) (k : ℕ), D.host.φ₀ (((a : D.host.K) : D.host.E)) = β ∧ β ∈ Qbar ∧ ‖lamC lam β‖ = 1 ∧ β + starRingEnd ℂ β = 1 ∧ β * starRingEnd ℂ β = ((2 * k : ℕ) : ℂ) ∧ ∀ (Λ : AddSubgroup ℂ) (t₀ : ℂ), GL3Theta.IsTwoTorsionPointUnkilled D Λ t₀ → β * t₀ ∉ Λ ∧ (1 - β) * t₀ ∉ Λ := by
  first | exact @GlobalTheory.EvenTheta.exists_int_trace_one_unit_at_two | exact GlobalTheory.EvenTheta.exists_int_trace_one_unit_at_two | (intros; apply GlobalTheory.EvenTheta.exists_int_trace_one_unit_at_two <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AdmissibleAtOfIrreducibleTame
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AdmissibleAtOfIrreducibleTame
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil.WdCocycle

section General

variable {D : D7} {T : Tor D} {N N' : ℕ}

theorem hf_add_left (x y z : VC D N N') : Hf D T (x + y) z = Hf D T x z + Hf D T y z := by
  simp only [Hf, Pi.add_apply, add_mul, Finset.sum_add_distrib, add_div]

theorem hf_add_right (x y z : VC D N N') : Hf D T x (y + z) = Hf D T x y + Hf D T x z := by
  simp only [Hf, Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib, add_div]

theorem hf_conj (x z : VC D N N') : Hf D T z x = (starRingEnd ℂ) (Hf D T x z) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Hf, map_div₀, map_sum, map_mul, Complex.conj_conj, Complex.conj_ofReal]
  congr 1
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

theorem wd_wd (x y : VC D N N') (F : VC D N N' → ℂ) :
    Wd D T x (Wd D T y F) = ee (-(w0 D * Hf D T x y).im) • Wd D T (x + y) F := by
  funext z
  have h1 : Hf D T x y = ((Hf D T x y).re : ℂ) + ((Hf D T x y).im : ℂ) * Complex.I := (Complex.re_add_im _).symm
  have h2 : Hf D T y x = ((Hf D T x y).re : ℂ) - ((Hf D T x y).im : ℂ) * Complex.I := by
    rw [hf_conj x y]
    apply Complex.ext <;> simp
  have h3 : (Hf D T y x).re = (Hf D T x y).re := by
    rw [hf_conj x y, Complex.conj_re]
  have h4 : (w0 D * Hf D T x y).im = ((Hf D T x y).im + Real.sqrt D.host.d * (Hf D T x y).re) / 2 := by
    have : w0 D = ((1 / 2 : ℝ) : ℂ) + ((Real.sqrt D.host.d / 2 : ℝ) : ℂ) * Complex.I := by
      rw [w0]; push_cast; ring
    rw [this]
    simp only [Complex.mul_im, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  have key : ee (qH D T x / 2) * ee (qH D T y / 2) *
      Complex.exp (-(Real.pi : ℂ) * Hf D T (z + x) y - (Real.pi : ℂ) * Hf D T y y / 2) *
      Complex.exp (-(Real.pi : ℂ) * Hf D T z x - (Real.pi : ℂ) * Hf D T x x / 2) =
      ee (-(w0 D * Hf D T x y).im) * ee (qH D T (x + y) / 2) *
      Complex.exp (-(Real.pi : ℂ) * Hf D T z (x + y) - (Real.pi : ℂ) * Hf D T (x + y) (x + y) / 2) := by
    simp only [ee, ← Complex.exp_add, qH]
    congr 1
    rw [h4]
    simp only [hf_add_left, hf_add_right, Complex.add_re, h3]
    rw [h2]
    generalize (Hf D T x y).re = a at h1 ⊢
    generalize (Hf D T x y).im = b at h1 ⊢
    rw [h1]
    push_cast
    ring
  simp only [Wd, U, wdPh, Pi.smul_apply, smul_eq_mul]
  rw [add_assoc z x y]
  linear_combination F (z + (x + y)) * key

end General

variable {D : D7}

theorem emb_conj (φ : D.host.E →+* ℂ) (x : D.host.E) : φ (D.host.conj x) = starRingEnd ℂ (φ x) :=
  D.host.conjE_apply φ x

theorem hf_pt (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} (z y : Matrix (Fin N') (Fin N) D.host.E) :
    Hf D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) (pt D (tor0 D cc δ) δ y) =
      ((‖δ‖ ^ 2 / area (lamOf D cc δ) : ℝ) : ℂ) * ∑ τ, embT D τ (∑ i, ∑ j, z i j * D.host.conj (y i j)) := by
  have h : δ * starRingEnd ℂ δ = (‖δ‖ : ℂ) ^ 2 := Complex.mul_conj' δ
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Hf, pt, embV, tor0, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, emb_conj]
  push_cast
  rw [← h, div_mul_eq_mul_div]
  congr 1
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

theorem pt_add (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} (z y : Matrix (Fin N') (Fin N) D.host.E) :
    pt D (tor0 D cc δ) δ (z + y) = pt D (tor0 D cc δ) δ z + pt D (tor0 D cc δ) δ y := by
  funext τ i j
  simp only [pt, embV, tor0, Pi.smul_apply, Pi.add_apply, Matrix.add_apply, smul_eq_mul, map_add (f := _), mul_add]

theorem wd_cocycle : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∃ w : 𝓞 D.host.E, w + sgO D w = 1 ∧ ∀ (N N' : ℕ) (z y : Matrix (Fin N') (Fin N) D.host.E), ee (-(Hf D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) (pt D (tor0 D cc δ) δ y)).im) = psi0 D cc δ (∑ i, ∑ j, z i j * D.host.conj (y i j)) ∧ pt D (tor0 D cc δ) δ (z + y) = pt D (tor0 D cc δ) δ z + pt D (tor0 D cc δ) δ y ∧ ∀ F, Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) (Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ y) F) = psi0 D cc δ (∑ i, ∑ j, (w : D.host.E) * z i j * D.host.conj (y i j)) • Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ (z + y)) F := by
  intro D hg cc δ _
  obtain ⟨a, ha⟩ := exists_integer_map_eq_w0 D
  let w : 𝓞 D.host.E := algebraMap (𝓞 D.host.K) (𝓞 D.host.E) a
  have hw : (w : D.host.E) = ((a : D.host.K) : D.host.E) := rfl
  have hτ : ∀ τ, embT D τ (w : D.host.E) = w0 D := fun τ => by
    rw [hw, ← ha]
    exact hg.1 τ _
  refine ⟨w, ?_, fun N N' z y => ⟨?_, pt_add cc δ z y, fun F => ?_⟩⟩
  · apply RingOfIntegers.ext
    apply D.host.φ₀.injective
    change D.host.φ₀ ((w : D.host.E) + D.host.conj (w : D.host.E)) = D.host.φ₀ 1
    rw [map_add (f := _), emb_conj, hw, ha, map_one, w0]
    simp only [map_div₀, map_add (f := _), map_mul, map_one, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
    ring
  · rw [hf_pt, psi0, Complex.im_ofReal_mul]
  · rw [wd_wd, pt_add, hf_pt, psi0]
    congr 3
    rw [mul_left_comm, Complex.im_ofReal_mul, Finset.mul_sum]
    congr 2
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [← hτ τ, ← map_mul]
    simp only [Finset.mul_sum, mul_assoc]

end GlobalTheory.FinWeil.WdCocycle
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AdmissibleAtOfIrreducibleTameStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_point_additive_form : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∃ w : 𝓞 D.host.E, w + sgO D w = 1 ∧ ∀ (N N' : ℕ) (z y : Matrix (Fin N') (Fin N) D.host.E), ee (-(Hf D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) (pt D (tor0 D cc δ) δ y)).im) = psi0 D cc δ (∑ i, ∑ j, z i j * D.host.conj (y i j)) ∧ pt D (tor0 D cc δ) δ (z + y) = pt D (tor0 D cc δ) δ z + pt D (tor0 D cc δ) δ y ∧ ∀ F, Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) (Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ y) F) = psi0 D cc δ (∑ i, ∑ j, (w : D.host.E) * z i j * D.host.conj (y i j)) • Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ (z + y)) F := by
  first | exact @GlobalTheory.FinWeil.WdCocycle.wd_cocycle | exact GlobalTheory.FinWeil.WdCocycle.wd_cocycle | (intros; apply GlobalTheory.FinWeil.WdCocycle.wd_cocycle <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsWeierstrassPSeries
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsWeierstrassPSeries
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

noncomputable section

namespace GlobalTheory.WpSeries

open PowerSeries

variable {K : Type} [Field K]

def euler (R : PowerSeries K) : PowerSeries K := X * derivativeFun R

theorem coeff_euler (R : PowerSeries K) (n : ℕ) : coeff n (euler R) = (n : K) * coeff n R := by
  cases n with
  | zero => simp [euler]
  | succ n =>
    rw [euler, coeff_succ_X_mul,
      show coeff n (derivativeFun R) = coeff (n + 1) R * ((n : K) + 1) from coeff_derivative R n]
    push_cast
    ring

theorem euler_one_add (R : PowerSeries K) : euler (1 + X * R) = X * (R + euler R) := by
  ext n
  cases n with
  | zero => simp [coeff_euler]
  | succ n =>
    simp only [coeff_euler, map_add (f := _), coeff_succ_X_mul, coeff_one]
    simp
    ring

def inv4 (R : PowerSeries K) : PowerSeries K := PowerSeries.mk fun n => coeff n R / (4 * ((n : K) + 2))

theorem inverseShiftedEulerOperatorFour_eq_iff [CharZero K] (R S : PowerSeries K) :
    inv4 S = R ↔ S = 4 * (2 * R + euler R) := by
  have h4 : (4 : PowerSeries K) = C 4 := (map_ofNat _ 4).symm
  have h2 : (2 : PowerSeries K) = C 2 := (map_ofNat _ 2).symm
  rw [PowerSeries.ext_iff, PowerSeries.ext_iff]
  refine forall_congr' fun n => ?_
  have hn : (4 * ((n : K) + 2)) ≠ 0 := by
    have : ((n : K) + 2) ≠ 0 := by exact_mod_cast (by omega : n + 2 ≠ 0)
    exact mul_ne_zero (by norm_num) this
  rw [inv4, coeff_mk, div_eq_iff hn, h4, h2, coeff_C_mul, map_add (f := _), coeff_C_mul, coeff_euler]
  constructor <;> intro h <;> rw [h] <;> ring

def rest (a b : K) (R : PowerSeries K) : PowerSeries K :=
  (euler R - R) ^ 2 - 12 * R ^ 2 - 4 * X * R ^ 3 + C a * X ^ 2 * (1 + X * R) + C b * X ^ 4

theorem contract (a b : K) (n : ℕ) (x y : PowerSeries K) (h : X ^ n ∣ x - y) :
    X ^ (n + 1) ∣ inv4 (X * rest a b x) - inv4 (X * rest a b y) := by
  have he : X ^ n ∣ euler x - euler y := by
    rw [X_pow_dvd_iff] at h ⊢
    intro m hm
    have := h m hm
    rw [map_sub, sub_eq_zero] at this
    rw [map_sub, coeff_euler, coeff_euler, this, sub_self]
  obtain ⟨u, hu⟩ := h
  obtain ⟨v, hv⟩ := he
  have hr : X ^ (n + 1) ∣ X * rest a b x - X * rest a b y := by
    refine ⟨(v - u) * (euler x - x + (euler y - y)) - 12 * u * (x + y)
      - 4 * X * u * (x ^ 2 + x * y + y ^ 2) + C a * X ^ 3 * u, ?_⟩
    unfold rest
    linear_combination X * (euler x - x + (euler y - y)) * hv +
      X * (-(euler x - x + (euler y - y)) - 12 * (x + y)
        - 4 * X * (x ^ 2 + x * y + y ^ 2) + C a * X ^ 3) * hu
  rw [X_pow_dvd_iff] at hr ⊢
  intro m hm
  have := hr m hm
  rw [map_sub, sub_eq_zero] at this
  rw [map_sub, inv4, inv4, coeff_mk, coeff_mk, this, sub_self]

theorem isWpSer_iff [CharZero K] (a b : K) (R : PowerSeries K) :
    IsWpSer a b (1 + X * R) ↔ inv4 (X * rest a b R) = R := by
  rw [inverseShiftedEulerOperatorFour_eq_iff]
  have he := euler_one_add R
  have hX : (X : PowerSeries K) ≠ 0 := X_ne_zero
  unfold IsWpSer
  change _ ∧ (euler (1 + X * R) - _) ^ 2 = _ ↔ _
  rw [he]
  unfold rest
  constructor
  · rintro ⟨-, h⟩
    apply mul_left_cancel₀ hX
    linear_combination h
  · intro h
    refine ⟨by simp, ?_⟩
    linear_combination X * h

theorem eq_one_add {P : PowerSeries K} (h : constantCoeff P = 1) : ∃ R, P = 1 + X * R := by
  obtain ⟨R, hR⟩ : X ∣ P - 1 := by rw [X_dvd_iff]; simp [h]
  exact ⟨R, by linear_combination hR⟩

theorem existsUnique_isWpSer :
    ∀ (K : Type) [Field K] [CharZero K] (a b : K), ∃! P : PowerSeries K, IsWpSer a b P := by
  intro K _ _ a b
  obtain ⟨R, hR⟩ := GlobalTheory.GenusOneDatum.exists_fixed_of_contract
    (fun R : PowerSeries K => inv4 (X * rest a b R)) (contract a b)
  refine ⟨1 + X * R, (isWpSer_iff a b R).2 hR, fun P hP => ?_⟩
  obtain ⟨S, rfl⟩ := eq_one_add hP.1
  have hS := (isWpSer_iff a b S).1 hP
  have hd : ∀ n : ℕ, X ^ n ∣ S - R := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := contract a b n S R ih
      rwa [hS, show inv4 (X * rest a b R) = R from hR] at this
  have : S = R := by
    ext n
    have := X_pow_dvd_iff.1 (hd (n + 1)) n (by omega)
    rwa [map_sub, sub_eq_zero] at this
  rw [this]

end GlobalTheory.WpSeries
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsWeierstrassPSeriesStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_isWeierstrassPSeries : ∀ (K : Type) [Field K] [CharZero K] (a b : K), ∃! P : PowerSeries K, IsWpSer a b P := by
  first | exact @GlobalTheory.WpSeries.existsUnique_isWpSer | exact GlobalTheory.WpSeries.existsUnique_isWpSer | (intros; apply GlobalTheory.WpSeries.existsUnique_isWpSer <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeanSquareEvenThetaConjugateLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeanSquareEvenThetaConjugateLattice
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
open MeasureTheory

noncomputable section

namespace GlobalTheory.MeanSquareConj

theorem mem_conj (Λ : AddSubgroup ℂ) (z : ℂ) :
    z ∈ Λ.map (starRingEnd ℂ).toAddMonoidHom ↔ (starRingEnd ℂ) z ∈ Λ := by
  rw [AddSubgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨_, h, by simp⟩

theorem area_conj (Λ : AddSubgroup ℂ) : area (Λ.map (starRingEnd ℂ).toAddMonoidHom) = area Λ := by
  unfold area
  congr 1
  ext a
  have e : ∀ x y : ℂ, |((starRingEnd ℂ) ((starRingEnd ℂ) x) * (starRingEnd ℂ) y).im| =
      |((starRingEnd ℂ) x * y).im| := by
    intro x y
    rw [← map_mul, Complex.conj_im, abs_neg]
  simp only [Set.mem_setOf_eq, mem_conj]
  constructor
  · rintro ⟨ha, x, hx, y, hy, rfl⟩
    exact ⟨ha, _, hx, _, hy, (e x y).symm⟩
  · rintro ⟨ha, x, hx, y, hy, rfl⟩
    exact ⟨ha, (starRingEnd ℂ) x, by simpa using hx, (starRingEnd ℂ) y, by simpa using hy, (e x y).symm⟩

theorem lattice_conj (Λ : AddSubgroup ℂ)
    (hΛ : ∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂}) :
    ∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧
      Λ.map (starRingEnd ℂ).toAddMonoidHom = AddSubgroup.closure {w₁, w₂} := by
  obtain ⟨w₁, w₂, hli, rfl⟩ := hΛ
  refine ⟨(starRingEnd ℂ) w₁, (starRingEnd ℂ) w₂, ?_, ?_⟩
  · rw [LinearIndependent.pair_iff] at hli ⊢
    intro s t h
    refine hli s t ?_
    have := congrArg (starRingEnd ℂ) h
    simpa using this
  · rw [AddMonoidHom.map_closure, Set.image_pair]
    rfl

theorem thetaTranslate_conjugateLattice (Λ : AddSubgroup ℂ) (G : ℂ → ℂ) (t z : ℂ) :
    U1 (Λ.map (starRingEnd ℂ).toAddMonoidHom) t (fun z => (starRingEnd ℂ) (G ((starRingEnd ℂ) z))) z =
      (starRingEnd ℂ) (U1 Λ ((starRingEnd ℂ) t) G ((starRingEnd ℂ) z)) := by
  unfold U1
  rw [area_conj, map_mul, ← Complex.exp_conj]
  simp only [map_add (f := _), map_sub, map_div₀, map_mul, map_neg, Complex.conj_ofReal, Complex.conj_conj, map_ofNat]

theorem sgStar_conj (Λ : AddSubgroup ℂ)
    (hΛ : ∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂}) :
    sgStar (Λ.map (starRingEnd ℂ).toAddMonoidHom) =
      fun z => (starRingEnd ℂ) (sgStar Λ ((starRingEnd ℂ) z)) := by
  obtain ⟨⟨hd, h1, -, hU⟩, -⟩ := GlobalTheory.OddTheta.sgStar_laws Λ hΛ
  obtain ⟨-, -, huniq, -⟩ := GlobalTheory.OddTheta.sgStar_laws _ (lattice_conj Λ hΛ)
  have hder : ∀ z, HasDerivAt (fun z => (starRingEnd ℂ) (sgStar Λ ((starRingEnd ℂ) z)))
      ((starRingEnd ℂ) (deriv (sgStar Λ) ((starRingEnd ℂ) z))) z := by
    intro z
    have := (hd ((starRingEnd ℂ) z)).hasDerivAt.conj_conj
    rw [Complex.conj_conj] at this
    exact this
  funext z
  have := huniq _ (fun z => (hder z).differentiableAt) (by
    intro ω hω z
    rw [thetaTranslate_conjugateLattice, hU _ ((mem_conj Λ ω).1 hω), map_mul]
    congr 1
    have e : (starRingEnd ℂ) (ω / 2) = (starRingEnd ℂ) ω / 2 := by
      rw [map_div₀, map_ofNat]
    simp only [mem_conj, e]
    split_ifs <;> simp) z
  rw [(hder 0).deriv, map_zero, h1, map_one, one_mul] at this
  exact this.symm

theorem evenTheta_conjugateLattice (Λ : AddSubgroup ℂ)
    (hΛ : ∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂}) (t z : ℂ) :
    GL3Theta.th0 (Λ.map (starRingEnd ℂ).toAddMonoidHom) ((starRingEnd ℂ) t) z =
      (starRingEnd ℂ) (GL3Theta.th0 Λ t ((starRingEnd ℂ) z)) := by
  unfold GL3Theta.th0
  rw [sgStar_conj Λ hΛ, thetaTranslate_conjugateLattice, thetaTranslate_conjugateLattice, map_div₀, map_zero, Complex.conj_conj]

theorem evenTheta_weightedNormSq_periodic (Λ : AddSubgroup ℂ)
    (hΛ : ∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂}) (t : ℂ)
    (x : ℂ) (hx : x ∈ Λ) (z : ℂ) :
    ‖GL3Theta.th0 Λ t (x + z)‖ ^ 2 * Real.exp (-Real.pi * ‖x + z‖ ^ 2 / area Λ) =
      ‖GL3Theta.th0 Λ t z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2 / area Λ) := by
  obtain ⟨⟨-, -, -, hU⟩, -⟩ := GlobalTheory.OddTheta.sgStar_laws Λ hΛ
  have hper : ∀ z, ‖sgStar Λ (z + x)‖ ^ 2 * Real.exp (-Real.pi * ‖z + x‖ ^ 2 / area Λ) =
      ‖sgStar Λ z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2 / area Λ) := by
    intro z
    rw [← GlobalTheory.GenusOneSup.thetaTranslation_weighted_normSq, hU x hx, norm_mul]
    split_ifs <;> simp
  unfold GL3Theta.th0
  simp only [norm_div, div_pow, div_mul_eq_mul_div]
  rw [GlobalTheory.GenusOneSup.thetaTranslation_weighted_normSq, GlobalTheory.GenusOneSup.thetaTranslation_weighted_normSq,
    show x + z + t = z + t + x by ring, hper]

theorem nrm1Sq_th0_map_conj_eq : ∀ (Λ : AddSubgroup ℂ), (∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂}) → ∀ t : ℂ, nrm1Sq (Λ.map (starRingEnd ℂ).toAddMonoidHom) (GL3Theta.th0 (Λ.map (starRingEnd ℂ).toAddMonoidHom) ((starRingEnd ℂ) t)) = nrm1Sq Λ (GL3Theta.th0 Λ t) := by
  intro Λ hΛ t
  have hex : ∀ A : AddSubgroup ℂ,
      (∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ A = AddSubgroup.closure {w₁, w₂}) →
      IsAddFundamentalDomain A
        (Classical.epsilon fun Fd : Set ℂ => IsAddFundamentalDomain A Fd volume) volume := by
    rintro A ⟨w₁, w₂, hli, rfl⟩
    obtain ⟨F, hF, -⟩ := GlobalTheory.GenusOneSup.exists_domain hli
    exact Classical.epsilon_spec (p := fun Fd : Set ℂ => IsAddFundamentalDomain _ Fd volume) ⟨F, hF⟩
  have hF := hex Λ hΛ
  have hF' := hex _ (lattice_conj Λ hΛ)
  have hcount : Countable Λ := by
    obtain ⟨w₁, w₂, -, h⟩ := hΛ
    have : (Λ : Set ℂ) ⊆ Set.range (fun p : ℤ × ℤ => p.1 • w₁ + p.2 • w₂) := by
      intro x hx
      rw [h] at hx
      obtain ⟨m, n, rfl⟩ := AddSubgroup.mem_closure_pair.1 hx
      exact ⟨(m, n), rfl⟩
    exact ((Set.countable_range _).mono this).to_subtype
  have : VAddInvariantMeasure Λ ℂ volume := ⟨fun γ s _ => measure_preimage_add volume (γ : ℂ) s⟩
  unfold nrm1Sq
  simp only
  set F := Classical.epsilon fun Fd : Set ℂ => IsAddFundamentalDomain Λ Fd volume
  set F' := Classical.epsilon fun Fd : Set ℂ =>
    IsAddFundamentalDomain (Λ.map (starRingEnd ℂ).toAddMonoidHom) Fd volume
  have hmp : MeasurePreserving (starRingEnd ℂ) volume volume := Complex.conjLIE.measurePreserving
  have hemb : MeasurableEmbedding (starRingEnd ℂ) := Complex.conjLIE.toHomeomorph.measurableEmbedding
  have hF2 : IsAddFundamentalDomain Λ ((starRingEnd ℂ) ⁻¹' F') volume := by
    refine hF'.preimage_of_equiv (f := starRingEnd ℂ)
      (e := fun y => (⟨(starRingEnd ℂ) y, (mem_conj Λ _).1 y.2⟩ : Λ))
      hmp.quasiMeasurePreserving ⟨?_, ?_⟩ ?_
    · intro x y h
      exact Subtype.ext (star_injective (congrArg Subtype.val h))
    · intro x
      exact ⟨⟨(starRingEnd ℂ) x, (mem_conj Λ _).2 (by simp)⟩, Subtype.ext (by simp)⟩
    · intro y x
      show (starRingEnd ℂ) ((starRingEnd ℂ) y + x) = (y : ℂ) + (starRingEnd ℂ) x
      simp
  rw [setAverage_eq, setAverage_eq, measureReal_def, measureReal_def, hF.measure_eq hF2,
    hF.setIntegral_eq hF2 (fun γ z => evenTheta_weightedNormSq_periodic Λ hΛ t γ γ.2 z), hmp.measure_preimage_emb hemb,
    ← hmp.setIntegral_preimage_emb hemb]
  simp only [evenTheta_conjugateLattice Λ hΛ, area_conj, Complex.conj_conj, Complex.norm_conj]

end GlobalTheory.MeanSquareConj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeanSquareEvenThetaConjugateLatticeStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.meanSquare_evenTheta_conjugateLattice : ∀ (Λ : AddSubgroup ℂ), (∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂}) → ∀ t : ℂ, nrm1Sq (Λ.map (starRingEnd ℂ).toAddMonoidHom) (GL3Theta.th0 (Λ.map (starRingEnd ℂ).toAddMonoidHom) ((starRingEnd ℂ) t)) = nrm1Sq Λ (GL3Theta.th0 Λ t) := by
  first | exact @GlobalTheory.MeanSquareConj.nrm1Sq_th0_map_conj_eq | exact GlobalTheory.MeanSquareConj.nrm1Sq_th0_map_conj_eq | (intros; apply GlobalTheory.MeanSquareConj.nrm1Sq_th0_map_conj_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTripleConstantEqCocycleSum
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslateCombinationCoefEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslateCombinationCoefEqZero
noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

namespace GlobalTheory.ThetaTranslateCoef

theorem sum_trivial_char_eq_zero {G ι : Type} [Monoid G] [Fintype ι] (κ : ι → (G →* ℂ)) (c : ι → ℂ)
    (h : ∀ y, ∑ i, c i * κ i y = 0) : ∑ i, (if κ i = 1 then c i else 0) = 0 := by
  have li := linearIndependent_monoidHom G ℂ
  rw [linearIndependent_iff] at li
  have h0 := li (∑ i, Finsupp.single (κ i) (c i)) (by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    funext y
    simp only [Finsupp.linearCombination_single, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    exact h y)
  have h1 := congrArg (fun l : (G →* ℂ) →₀ ℂ => l 1) h0
  simp only [Finsupp.finsetSum_apply, Finsupp.single_apply, Finsupp.coe_zero, Pi.zero_apply] at h1
  rw [← h1]
  exact Finset.sum_congr rfl fun i _ => by congr

def kap (D : D7) (T : Tor D) {N N' : ℕ} (A : AddSubgroup (VC D N N')) (z : VC D N N') :
    Multiplicative A →* ℂ where
  toFun y := bc D T ((Multiplicative.toAdd y : A) : VC D N N') z / bc D T z ((Multiplicative.toAdd y : A) : VC D N N')
  map_one' := by
    simp only [toAdd_one, ZeroMemClass.coe_zero, bc_zero_left, bc_zero_right, div_one]
  map_mul' x y := by
    simp only [toAdd_mul, AddMemClass.coe_add, bc_add_left, bc_add_right, mul_div_mul_comm]

theorem kap_eq_one_iff {D : D7} {T : Tor D} {N N' : ℕ} {A : AddSubgroup (VC D N N')} (h : Nice D T A)
    (z : VC D N N') : kap D T A z = 1 ↔ z ∈ A := by
  constructor
  · intro hk
    refine h.2.2 z fun y hy => ?_
    have := DFunLike.congr_fun hk (Multiplicative.ofAdd (⟨y, hy⟩ : A))
    change bc D T y z / bc D T z y = 1 at this
    exact ((div_eq_one_iff_eq (bc_ne_zero D T z y)).1 this).symm
  · intro hz
    refine MonoidHom.ext fun y => ?_
    change bc D T _ z / bc D T z _ = 1
    rw [h.2.1 _ (Multiplicative.toAdd y).2 z hz, h.2.1 z hz _ (Multiplicative.toAdd y).2, div_one]

theorem Wd_Wd_fixed (D : D7) (T : Tor D) {N N' : ℕ} (y z : VC D N N') (e : VC D N N' → ℂ)
    (he : Wd D T y e = e) : Wd D T y (Wd D T z e) = (bc D T y z / bc D T z y) • Wd D T z e := by
  have h1 := Wd_Wd D T z y e
  rw [he, add_comm] at h1
  rw [Wd_Wd]
  conv_rhs => rw [h1]
  rw [smul_smul, div_mul_cancel₀ _ (bc_ne_zero D T z y)]

def WdL (D : D7) (T : Tor D) {N N' : ℕ} (y : VC D N N') : (VC D N N' → ℂ) →ₗ[ℂ] (VC D N N' → ℂ) where
  toFun := Wd D T y
  map_add' := Wd_add D T y
  map_smul' := Wd_smul D T y

theorem coef_eq_zero : ∀ (D : D7) (T : Tor D) (N N' : ℕ) (A : AddSubgroup (VC D N N')), Nice D T A →
    ∀ e ∈ ThSp D T A, e ≠ 0 → ∀ (ι : Type) [Fintype ι] (a : ι → ℂ) (z : ι → VC D N N'),
      (∀ v, ∑ i, a i * Wd D T (z i) e v = 0) → ∑ i, (if z i ∈ A then a i else 0) = 0 := by
  intro D T N N' A hA e he hne ι _ a z hrel
  have hfix := ((hA.mem_ThSp e).1 he).2
  obtain ⟨v, hv⟩ := Function.ne_iff.1 hne
  have hsum : ∑ i, a i • Wd D T (z i) e = 0 := by
    funext w
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    exact hrel w
  have key := sum_trivial_char_eq_zero (fun i => kap D T A (z i)) (fun i => a i * Wd D T (z i) e v) (by
    intro y
    have h1 := congrArg (WdL D T ((Multiplicative.toAdd y : A) : VC D N N')) hsum
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_zero] at h1
    have h2 := congrFun h1 v
    rw [Finset.sum_apply, Pi.zero_apply] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul]
    change _ = a i * Wd D T _ (Wd D T (z i) e) v
    rw [Wd_Wd_fixed D T _ _ e (hfix _ (Multiplicative.toAdd y).2)]
    change a i * Wd D T (z i) e v * (bc D T _ _ / bc D T _ _) = a i * ((bc D T _ _ / bc D T _ _) * Wd D T (z i) e v)
    ring)
  have h3 : (∑ i, (if z i ∈ A then a i else 0)) * e v = 0 := by
    refine Eq.trans ?_ key
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hz : z i ∈ A
    · rw [if_pos hz, if_pos ((kap_eq_one_iff hA _).2 hz), hfix _ hz]
    · rw [if_neg hz, if_neg (fun h => hz ((kap_eq_one_iff hA _).1 h)), zero_mul]
  exact (mul_eq_zero.1 h3).resolve_right hv

end GlobalTheory.ThetaTranslateCoef
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslateCombinationCoefEqZeroStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaTranslate_combination_coef_eq_zero : ∀ (D : D7) (T : Tor D) (N N' : ℕ) (A : AddSubgroup (VC D N N')), Nice D T A → ∀ e ∈ ThSp D T A, e ≠ 0 → ∀ (ι : Type) [Fintype ι] (a : ι → ℂ) (z : ι → VC D N N'), (∀ v, ∑ i, a i * Wd D T (z i) e v = 0) → ∑ i, (if z i ∈ A then a i else 0) = 0 := by
  first | exact @GlobalTheory.ThetaTranslateCoef.coef_eq_zero | exact GlobalTheory.ThetaTranslateCoef.coef_eq_zero | (intros; apply GlobalTheory.ThetaTranslateCoef.coef_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTripleConstantEqCocycleSum
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

namespace GlobalTheory.TripleConstant

theorem Wd_mul_sum (D : D7) (T : Tor D) {N N' : ℕ} (y : VC D N N') (c : ℂ) {ι : Type} (s : Finset ι)
    (G : ι → VC D N N' → ℂ) (v : VC D N N') :
    Wd D T y (fun z => c * ∑ i ∈ s, G i z) v = c * ∑ i ∈ s, Wd D T y (G i) v := by
  simp only [Wd, U, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem out_mem_iff {V : Type} [AddCommGroup V] (A B : AddSubgroup V) (q : B ⧸ A.addSubgroupOf B) :
    ((Quotient.out q : B) : V) ∈ A ↔ q = 0 := by
  rw [← AddSubgroup.mem_addSubgroupOf, ← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.out_eq']

theorem mu_form : ∀ (D : D7) (T : Tor D) (N N' : ℕ) (A₁ A₂ A₃ : AddSubgroup (VC D N N')) (e : VC D N N' → ℂ) (μ : ℂ), Trip D T A₁ A₂ A₃ e μ → ∃ r : ℝ, 0 < r ∧ μ * (r : ℂ) = ∑ᶠ p : (A₃ ⧸ A₂.addSubgroupOf A₃) × (A₂ ⧸ A₁.addSubgroupOf A₂), (if ((Quotient.out p.1 : A₃) : VC D N N') + ((Quotient.out p.2 : A₂) : VC D N N') ∈ A₁ then bc D T ((Quotient.out p.1 : A₃) : VC D N N') ((Quotient.out p.2 : A₂) : VC D N N') else 0) := by
  intro D T N N' A₁ A₂ A₃ e μ h
  obtain ⟨h1, h2, h3, n12, n23, n13, he, he0, -, hI⟩ := h
  haveI f12 : Fintype (A₂ ⧸ A₁.addSubgroupOf A₂) := AddSubgroup.fintypeOfIndexNeZero n12
  haveI f23 : Fintype (A₃ ⧸ A₂.addSubgroupOf A₃) := AddSubgroup.fintypeOfIndexNeZero n23
  haveI f13 : Fintype (A₃ ⧸ A₁.addSubgroupOf A₃) := AddSubgroup.fintypeOfIndexNeZero n13
  rw [h3.Iop_eq A₂, h2.Iop_eq A₁, h3.Iop_eq A₁] at hI
  simp only [finsum_eq_sum_of_fintype] at hI ⊢
  have p12 : 0 < Real.sqrt ((A₁.addSubgroupOf A₂).index : ℝ) :=
    Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero n12))
  have p23 : 0 < Real.sqrt ((A₂.addSubgroupOf A₃).index : ℝ) :=
    Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero n23))
  have p13 : 0 < Real.sqrt ((A₁.addSubgroupOf A₃).index : ℝ) :=
    Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero n13))
  generalize Real.sqrt ((A₁.addSubgroupOf A₂).index : ℝ) = s12 at *
  generalize Real.sqrt ((A₂.addSubgroupOf A₃).index : ℝ) = s23 at *
  generalize Real.sqrt ((A₁.addSubgroupOf A₃).index : ℝ) = s13 at *
  have key := GlobalTheory.T.thetaTranslate_combination_coef_eq_zero D T N N' A₁ h1 e he he0
    (((A₃ ⧸ A₂.addSubgroupOf A₃) × (A₂ ⧸ A₁.addSubgroupOf A₂)) ⊕ (A₃ ⧸ A₁.addSubgroupOf A₃))
    (Sum.elim (fun p => (s23 : ℂ)⁻¹ * (s12 : ℂ)⁻¹ *
        bc D T ((Quotient.out p.1 : A₃) : VC D N N') ((Quotient.out p.2 : A₂) : VC D N N'))
      (fun _ => -(μ * (s13 : ℂ)⁻¹)))
    (Sum.elim (fun p => ((Quotient.out p.1 : A₃) : VC D N N') + ((Quotient.out p.2 : A₂) : VC D N N'))
      (fun q => ((Quotient.out q : A₃) : VC D N N'))) (by
      intro v
      have hv := congrFun hI v
      simp only [Wd_mul_sum, Wd_Wd, Pi.smul_apply, smul_eq_mul] at hv
      simp only [Finset.mul_sum] at hv
      simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.sum_prod_type, neg_mul,
        Finset.sum_neg_distrib, mul_assoc]
      rw [hv]; ring)
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, out_mem_iff, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at key
  refine ⟨s23 * s12 / s13, by positivity, ?_⟩
  have q12 : (s12 : ℂ) ≠ 0 := by exact_mod_cast p12.ne'
  have q23 : (s23 : ℂ) ≠ 0 := by exact_mod_cast p23.ne'
  have q13 : (s13 : ℂ) ≠ 0 := by exact_mod_cast p13.ne'
  have k2 := congrArg (fun t => (s23 : ℂ) * s12 * t) (add_neg_eq_zero.1 key)
  simp only [Finset.mul_sum] at k2
  have : μ * ((s23 * s12 / s13 : ℝ) : ℂ) = (s23 : ℂ) * s12 * (μ * (s13 : ℂ)⁻¹) := by
    push_cast; ring
  rw [this, ← k2]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hp : ((Quotient.out p.1 : A₃) : VC D N N') + ((Quotient.out p.2 : A₂) : VC D N N') ∈ A₁
  · simp only [hp, if_true]
    field_simp
  · simp only [hp, if_false, mul_zero]

end GlobalTheory.TripleConstant
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTripleConstantEqCocycleSumStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaTripleConstant_eq_cocycle_sum : ∀ (D : D7) (T : Tor D) (N N' : ℕ) (A₁ A₂ A₃ : AddSubgroup (VC D N N')) (e : VC D N N' → ℂ) (μ : ℂ), Trip D T A₁ A₂ A₃ e μ → ∃ r : ℝ, 0 < r ∧ μ * (r : ℂ) = ∑ᶠ p : (A₃ ⧸ A₂.addSubgroupOf A₃) × (A₂ ⧸ A₁.addSubgroupOf A₂), (if ((Quotient.out p.1 : A₃) : VC D N N') + ((Quotient.out p.2 : A₂) : VC D N N') ∈ A₁ then bc D T ((Quotient.out p.1 : A₃) : VC D N N') ((Quotient.out p.2 : A₂) : VC D N N') else 0) := by
  first | exact @GlobalTheory.TripleConstant.mu_form | exact GlobalTheory.TripleConstant.mu_form | (intros; apply GlobalTheory.TripleConstant.mu_form <;> assumption)
end
end
