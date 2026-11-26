module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergGLnGLmPartialLEqDivEntire
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergSameDegreeMeromorphicContinuation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCuspParamGoodRow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalLatticeTwistedTupleSpanTop

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormProdSatakeParametersUnitaryEqOne
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormProdSatakeParametersUnitaryEqOne
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW Filter Topology Formalism.UG GlobalTheory.RSNonvan

namespace GlobalTheory.RSNonvan

theorem norm_prod_sat_eq_one : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (σ : CG E a)
    (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ), σ.IsUnitary → σ.HasSat w B → ‖((B.prod : ℂˣ) : ℂ)‖ = 1 := by
  intro E _ _ _ a σ w B hu hB
  obtain ⟨ω, hωu, hω⟩ := hu
  induction σ using Quotient.inductionOn with | _ π => ?_
  change GlobalTheory.LFun.HasSatGL w (π.locRep w) B at hB
  change π.HasCentChar ω at hω
  obtain ⟨x, hx⟩ := hB.exists_vec
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.LFun.exists_isUnifV w
  have hϖ0 : ϖ ≠ 0 := fun h0 => by simp [IsUnifV, h0] at hϖ
  let u : (w.adicCompletion E)ˣ := Units.mk0 ϖ hϖ0
  let S : GL (Fin a) (w.adicCompletion E) := Matrix.GeneralLinearGroup.scalar (Fin a) u
  let K := GlobalTheory.LFun.KGL w (n := a)
  have hS : ((S : GL (Fin a) (w.adicCompletion E)) : Matrix (Fin a) (Fin a) (w.adicCompletion E)) = diagJ a ϖ a := by
    ext i j
    simp [S, u, diagJ, Matrix.GeneralLinearGroup.scalar, Matrix.diagonal_apply]
  have hT : Tj ℂ a (Ov E w) ϖ a = dosetInd ℂ K S := by
    unfold Tj dosetInd
    congr 1
    ext g
    simp only [Set.mem_setOf_eq, DoubleCoset.mem_doubleCoset, SetLike.mem_coe]
    refine exists_congr fun y => and_congr_right fun _ => exists_congr fun z => and_congr_right fun _ => ?_
    rw [Units.ext_iff, Units.val_mul, Units.val_mul, hS]
  have hc : ∀ g ∈ DoubleCoset.doubleCoset S (K : Set _) K, ∃! γ, γ ∈ ({S} : Finset _) ∧ γ⁻¹ * g ∈ K := by
    intro g hg
    obtain ⟨y, hy, z, hz, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hg
    refine ⟨S, ⟨Finset.mem_singleton_self _, ?_⟩, fun γ hγ => Finset.mem_singleton.1 hγ.1⟩
    have e : S⁻¹ * (y * S * z) = y * z := by
      rw [show y * S = S * y from (scalar_comm u y).symm]; group
    rw [e]
    exact K.mul_mem hy hz
  have hR : ∀ γ ∈ ({S} : Finset _), γ ∈ DoubleCoset.doubleCoset S (K : Set _) K := by
    intro γ hγ
    rw [Finset.mem_singleton.1 hγ]
    exact DoubleCoset.mem_doubleCoset.2 ⟨1, K.one_mem, 1, K.one_mem, by group⟩
  have h1 := hx.2.2.2 ϖ hϖ a le_rfl
  rw [hT, GlobalTheory.LFun.heckeVec_dosetInd hx.2.1 hR hc, Finset.sum_singleton] at h1
  have h2 : π.locRep w S x = ((ω.1 (finId E (Units.map (corner (sLoc E w)) u)) : ℂˣ) : ℂ) • x := by
    have e : locGL E a w S = Matrix.GeneralLinearGroup.scalar (Fin a) (Units.map (corner (sLoc E w)) u) :=
      cornerGL_scalar (sLoc E w) u
    change π.finPart (locGL E a w S) x = _
    rw [e]
    exact hω _ x
  rw [h2] at h1
  have h3 := smul_left_injective ℂ hx.1 h1
  have hcard : (B.map fun b : ℂˣ => (b : ℂ)).card = a := by rw [Multiset.card_map]; exact hx.2.2.1
  have h4 : GlobalTheory.LFun.satEig (qV E w) a B a = ((B.prod : ℂˣ) : ℂ) := by
    rw [GlobalTheory.LFun.satEig, sub_self, mul_zero, zero_div, Complex.cpow_zero, one_mul, Multiset.esymm, ← hcard,
      Multiset.powersetCard_self, Multiset.map_singleton, Multiset.sum_singleton]
    exact (map_multiset_prod (Units.coeHom ℂ) B).symm
  rw [← h4, ← h3]
  exact hωu _

end GlobalTheory.RSNonvan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormProdSatakeParametersUnitaryEqOneStatement
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW Filter Topology Formalism.UG GlobalTheory.RSNonvan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_prod_satakeParameters_unitary_eq_one : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (σ : CG E a) (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ), σ.IsUnitary → σ.HasSat w B → ‖((B.prod : ℂˣ) : ℂ)‖ = 1 := by
  first | (exact @GlobalTheory.RSNonvan.norm_prod_sat_eq_one) | (exact GlobalTheory.RSNonvan.norm_prod_sat_eq_one) | (intros; apply GlobalTheory.RSNonvan.norm_prod_sat_eq_one  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalRankinSelbergFactorConjTendstoOneNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalRankinSelbergFactorConjTendstoOneNeZero
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW Filter Topology Formalism.UG GlobalTheory.RSNonvan

namespace GlobalTheory.JSW

theorem locL_conj_tendsto_one_and_ne_zero : ∀ (q : ℕ) (A B : Multiset ℂˣ), 1 < q → (∀ α ∈ A, ‖(α : ℂ)‖ ^ 2 < (q : ℝ)) →
    (∀ β ∈ B, ‖(β : ℂ)‖ ^ 2 < (q : ℝ)) →
    Tendsto (fun x : ℝ => locL q A (B.map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) (𝓝[>] 1)
      (𝓝 (locL q A (B.map (Units.map (starRingEnd ℂ).toMonoidHom)) 1)) ∧
    locL q A (B.map (Units.map (starRingEnd ℂ).toMonoidHom)) 1 ≠ 0 := by
  intro q A B hq hA hB
  set B' := B.map (Units.map (starRingEnd ℂ).toMonoidHom) with hB'
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hqr : (1 : ℝ) < q := by exact_mod_cast hq

  have key : ∀ p ∈ A ×ˢ B', (1 - (p.1 : ℂ) * p.2 * (q : ℂ) ^ (-(1 : ℂ))) ≠ 0 := by
    intro p hp
    rw [Multiset.mem_product] at hp
    obtain ⟨h1, h2⟩ := hp
    rw [hB', Multiset.mem_map] at h2
    obtain ⟨β, hβ, hpe⟩ := h2
    rw [← hpe]
    have ha := hA _ h1
    have hb := hB _ hβ
    have hnb : ‖((Units.map (starRingEnd ℂ).toMonoidHom β : ℂˣ) : ℂ)‖ = ‖(β : ℂ)‖ := by
      simp [Units.coe_map]
    have hprod : ‖(p.1 : ℂ)‖ * ‖(β : ℂ)‖ < q := by
      have h0 : 0 ≤ ‖(p.1 : ℂ)‖ * ‖(β : ℂ)‖ := by positivity
      by_contra hc
      push_neg at hc
      have : (q : ℝ) * q ≤ (‖(p.1 : ℂ)‖ * ‖(β : ℂ)‖) * (‖(p.1 : ℂ)‖ * ‖(β : ℂ)‖) :=
        mul_le_mul hc hc (by positivity) h0
      have h3 : (‖(p.1 : ℂ)‖ * ‖(β : ℂ)‖) * (‖(p.1 : ℂ)‖ * ‖(β : ℂ)‖) = ‖(p.1 : ℂ)‖ ^ 2 * ‖(β : ℂ)‖ ^ 2 := by ring
      have h4 : ‖(p.1 : ℂ)‖ ^ 2 * ‖(β : ℂ)‖ ^ 2 < (q : ℝ) * q :=
        mul_lt_mul'' ha hb (by positivity) (by positivity)
      linarith
    intro h0
    have hz : (p.1 : ℂ) * ((Units.map (starRingEnd ℂ).toMonoidHom β : ℂˣ) : ℂ) * (q : ℂ) ^ (-(1 : ℂ)) = 1 := by
      linear_combination -h0
    have hn := congrArg norm hz
    rw [Complex.cpow_neg_one, norm_mul, norm_mul, hnb, norm_inv, Complex.norm_natCast, norm_one] at hn
    have hqpos : (0 : ℝ) < q := by linarith
    rw [mul_inv_eq_one₀ hqpos.ne'] at hn
    linarith
  constructor
  · have hc : ∀ p ∈ A ×ˢ B', Tendsto (fun x : ℝ => (1 - (p.1 : ℂ) * p.2 * (q : ℂ) ^ (-(x : ℂ)))⁻¹) (𝓝[>] 1)
        (𝓝 ((1 - (p.1 : ℂ) * p.2 * (q : ℂ) ^ (-((1 : ℝ) : ℂ)))⁻¹)) := by
      intro p hp
      apply Tendsto.mono_left _ nhdsWithin_le_nhds
      apply ContinuousAt.tendsto
      apply ContinuousAt.inv₀
      · apply ContinuousAt.sub continuousAt_const
        apply ContinuousAt.mul continuousAt_const
        apply ContinuousAt.const_cpow
        · exact (Complex.continuous_ofReal.neg).continuousAt
        · exact Or.inl hq0
      · simpa using key p hp
    have := tendsto_multiset_prod (A ×ˢ B') hc
    simpa [locL] using this
  · unfold locL
    apply Multiset.prod_ne_zero
    rw [Multiset.mem_map]
    rintro ⟨p, hp, h⟩
    exact inv_ne_zero (key p hp) h
end GlobalTheory.JSW
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalRankinSelbergFactorConjTendstoOneNeZeroStatement
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW Filter Topology Formalism.UG GlobalTheory.RSNonvan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localRankinSelbergFactor_conj_tendsto_one_ne_zero : ∀ (q : ℕ) (A B : Multiset ℂˣ), 1 < q → (∀ α ∈ A, ‖(α : ℂ)‖ ^ 2 < (q : ℝ)) → (∀ β ∈ B, ‖(β : ℂ)‖ ^ 2 < (q : ℝ)) → Tendsto (fun x : ℝ => locL q A (B.map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) (𝓝[>] 1) (𝓝 (locL q A (B.map (Units.map (starRingEnd ℂ).toMonoidHom)) 1)) ∧ locL q A (B.map (Units.map (starRingEnd ℂ).toMonoidHom)) 1 ≠ 0 := by
  first | (exact @GlobalTheory.JSW.locL_conj_tendsto_one_and_ne_zero) | (exact GlobalTheory.JSW.locL_conj_tendsto_one_and_ne_zero) | (intros; apply GlobalTheory.JSW.locL_conj_tendsto_one_and_ne_zero  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOneLeNormPsumMultiset
open Finset MvPolynomial

namespace GlobalTheory.PowerSumDiv

variable {σ : Type} [Fintype σ]

theorem eval_esymm_card (f : σ → ℂ) :
    MvPolynomial.eval f (esymm σ ℂ (Fintype.card σ)) = ∏ i, f i := by
  rw [← Finset.card_univ, esymm, Finset.powersetCard_self]
  simp

theorem eval_psum (f : σ → ℂ) (r : ℕ) : MvPolynomial.eval f (psum σ ℂ r) = ∑ i, f i ^ r := by
  simp [psum]

theorem norm_eval_esymm_le (f : σ → ℂ) {c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 1)
    (hp : ∀ r, 1 ≤ r → r ≤ Fintype.card σ → ‖∑ i, f i ^ r‖ ≤ c) :
    ∀ k, 1 ≤ k → k ≤ Fintype.card σ → ‖MvPolynomial.eval f (esymm σ ℂ k)‖ ≤ c := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk1 hkn
    have hN := congrArg (MvPolynomial.eval f) (MvPolynomial.mul_esymm_eq_sum σ ℂ k)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_mul, map_pow, map_neg, map_one, map_sum, map_natCast] at hN
    have hsub : (antidiagonal k).filter (fun a => a.1 < k) ⊆ (range k).image (fun j => (j, k - j)) := by
      intro a ha
      simp only [mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at ha
      simp only [mem_image, mem_range]
      exact ⟨a.1, ha.2, by ext <;> simp <;> omega⟩
    have hcard : ((antidiagonal k).filter (fun a => a.1 < k)).card ≤ k :=
      (card_le_card hsub).trans (card_image_le.trans (by simp))
    have hterm : ∀ a ∈ (antidiagonal k).filter (fun a => a.1 < k),
        ‖(-1 : ℂ) ^ a.1 * MvPolynomial.eval f (esymm σ ℂ a.1) * MvPolynomial.eval f (psum σ ℂ a.2)‖ ≤ c := by
      intro a ha
      simp only [mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at ha
      have he : ‖MvPolynomial.eval f (esymm σ ℂ a.1)‖ ≤ 1 := by
        rcases Nat.eq_zero_or_pos a.1 with h0 | h0
        · rw [h0, esymm_zero]; simp
        · exact (ih a.1 ha.2 h0 (by omega)).trans hc
      have hq : ‖MvPolynomial.eval f (psum σ ℂ a.2)‖ ≤ c := by
        rw [eval_psum]; exact hp _ (by omega) (by omega)
      rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      calc _ ≤ 1 * c := mul_le_mul he hq (norm_nonneg _) zero_le_one
        _ = c := one_mul c
    have hk : (0 : ℝ) < k := by exact_mod_cast hk1
    have h1 : (k : ℝ) * ‖MvPolynomial.eval f (esymm σ ℂ k)‖ ≤ k * c := by
      have := congrArg norm hN
      rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_natCast] at this
      rw [this]
      calc _ ≤ ∑ a ∈ (antidiagonal k).filter (fun a => a.1 < k), c := norm_sum_le_of_le _ hterm
        _ = ((antidiagonal k).filter (fun a => a.1 < k)).card * c := by rw [sum_const, nsmul_eq_mul]
        _ ≤ k * c := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hc0
    exact le_of_mul_le_mul_left h1 hk

theorem exists_one_le_norm_psum (f : σ → ℂ) (hn : 1 ≤ Fintype.card σ) (hf : ‖∏ i, f i‖ = 1) :
    ∃ r, 1 ≤ r ∧ r ≤ Fintype.card σ ∧ 1 ≤ ‖∑ i, f i ^ r‖ := by
  by_contra h
  push_neg at h
  have hne : (Icc 1 (Fintype.card σ)).Nonempty := ⟨1, by simp [hn]⟩
  set c := (Icc 1 (Fintype.card σ)).sup' hne (fun r => ‖∑ i, f i ^ r‖)
  have hc1 : c < 1 := by
    rw [Finset.sup'_lt_iff]
    intro r hr
    rw [mem_Icc] at hr
    exact h r hr.1 hr.2
  have hle : ∀ r, 1 ≤ r → r ≤ Fintype.card σ → ‖∑ i, f i ^ r‖ ≤ c := fun r h1 h2 =>
    Finset.le_sup' (fun r => ‖∑ i, f i ^ r‖) (by rw [mem_Icc]; exact ⟨h1, h2⟩)
  have hc0 : 0 ≤ c := (norm_nonneg _).trans (hle 1 le_rfl hn)
  have := norm_eval_esymm_le f hc0 hc1.le hle _ hn le_rfl
  rw [eval_esymm_card, hf] at this
  linarith

end GlobalTheory.PowerSumDiv

namespace GlobalTheory.PowerSumDiv

theorem exists_one_le_norm_psum_multiset (A : Multiset ℂ) (hA : 1 ≤ Multiset.card A) (h : ‖A.prod‖ = 1) :
    ∃ r, 1 ≤ r ∧ r ≤ Multiset.card A ∧ 1 ≤ ‖(A.map (· ^ r)).sum‖ := by
  set f : Fin A.toList.length → ℂ := A.toList.get
  have hA' : A = Finset.univ.val.map f := by
    rw [Fin.univ_val_map, List.ofFn_get, Multiset.coe_toList]
  have hc : Fintype.card (Fin A.toList.length) = Multiset.card A := by simp
  have hp : A.prod = ∏ i, f i := by rw [Finset.prod_eq_multiset_prod, ← hA']
  have hs : ∀ r, (A.map (· ^ r)).sum = ∑ i, f i ^ r := by
    intro r
    have e := congrArg (fun B : Multiset ℂ => (B.map (· ^ r)).sum) hA'
    rw [e, Finset.sum_eq_multiset_sum, Multiset.map_map]; rfl
  obtain ⟨r, h1, h2, h3⟩ := exists_one_le_norm_psum f (by rw [hc]; exact hA) (by rw [← hp]; exact h)
  exact ⟨r, h1, by rw [← hc]; exact h2, by rw [hs]; exact h3⟩

end GlobalTheory.PowerSumDiv

open NumberField IsDedekindDomain Filter Topology

namespace GlobalTheory.PowerSumDiv

theorem one_le_absNorm {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) :
    (1 : ℝ) ≤ (Ideal.absNorm w.asIdeal : ℝ) := by
  have : Ideal.absNorm w.asIdeal ≠ 0 := fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr this

theorem not_summable_inv_absNorm {E : Type} [Field E] [NumberField E] (S : Finset (HeightOneSpectrum (𝓞 E))) :
    ¬ Summable (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} => (Ideal.absNorm w.1.asIdeal : ℝ)⁻¹) := by
  intro hS
  have hU : Summable (fun w : HeightOneSpectrum (𝓞 E) => (Ideal.absNorm w.asIdeal : ℝ)⁻¹) :=
    (Finset.summable_compl_iff (f := fun w : HeightOneSpectrum (𝓞 E) => (Ideal.absNorm w.asIdeal : ℝ)⁻¹) S).mp hS
  set M := ∑' w : HeightOneSpectrum (𝓞 E), (Ideal.absNorm w.asIdeal : ℝ)⁻¹
  have hb : ∀ s : ℝ, 1 < s → NumberField.Set.primeIdealZetaSum (Set.univ : Set (HeightOneSpectrum (𝓞 E))) s ≤ M := by
    intro s hs
    have hle : ∀ w : HeightOneSpectrum (𝓞 E), (Ideal.absNorm w.asIdeal : ℝ) ^ (-s) ≤ (Ideal.absNorm w.asIdeal : ℝ)⁻¹ := by
      intro w
      rw [← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le (one_le_absNorm w) (by linarith)
    rw [NumberField.Set.primeIdealZetaSum_def,
      tsum_univ (fun w : HeightOneSpectrum (𝓞 E) => (Ideal.absNorm w.asIdeal : ℝ) ^ (-s))]
    exact Summable.tsum_le_tsum hle (hU.of_nonneg_of_le (fun _ => by positivity) hle) hU
  obtain ⟨s, hsM, hs1⟩ := (((ReciprocityTheory.Neutral.Bridge.tendsto_primeIdealZetaSum_univ E).eventually_gt_atTop M).and
    self_mem_nhdsWithin).exists
  exact absurd (hb s hs1) (not_le.mpr hsM)

theorem not_summable_psum_sq {E : Type} [Field E] [NumberField E] (N : ℕ) (hN : 1 ≤ N)
    (S : Finset (HeightOneSpectrum (𝓞 E))) (A : HeightOneSpectrum (𝓞 E) → Multiset ℂ)
    (hcard : ∀ w ∉ S, Multiset.card (A w) = N) (hprod : ∀ w ∉ S, ‖(A w).prod‖ = 1) {x : ℝ} (hx : x ≤ 1 / N) :
    ¬ Summable (fun p : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} × ℕ =>
      ‖((A p.1.1).map (· ^ (p.2 + 1))).sum‖ ^ 2 * (Ideal.absNorm p.1.1.asIdeal : ℝ) ^ (-(((p.2 : ℝ) + 1) * x)) /
        ((p.2 : ℝ) + 1)) := by
  intro hs
  have hex : ∀ w : {w : HeightOneSpectrum (𝓞 E) // w ∉ S},
      ∃ r, 1 ≤ r ∧ r ≤ N ∧ 1 ≤ ‖((A w.1).map (· ^ r)).sum‖ := by
    intro w
    have := exists_one_le_norm_psum_multiset (A w.1) (by rw [hcard w.1 w.2]; exact hN) (hprod w.1 w.2)
    rwa [hcard w.1 w.2] at this
  choose r hr1 hrN hr using hex
  set F := fun p : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} × ℕ =>
      ‖((A p.1.1).map (· ^ (p.2 + 1))).sum‖ ^ 2 * (Ideal.absNorm p.1.1.asIdeal : ℝ) ^ (-(((p.2 : ℝ) + 1) * x)) /
        ((p.2 : ℝ) + 1) with hF
  have hinj : Function.Injective (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} => (w, r w - 1)) :=
    fun a b h => congrArg Prod.fst h
  have h1 := hs.comp_injective hinj
  apply not_summable_inv_absNorm S
  refine (h1.mul_left (N : ℝ)).of_nonneg_of_le (fun _ => by positivity) (fun w => ?_)
  have hre : (((r w - 1 : ℕ) : ℝ) + 1) = (r w : ℝ) := by
    rw [Nat.cast_sub (hr1 w)]; push_cast; ring
  have hpow : r w - 1 + 1 = r w := Nat.sub_add_cancel (hr1 w)
  simp only [Function.comp_apply, hF, hre, hpow]
  have hq := one_le_absNorm w.1
  have hr0 : (0 : ℝ) < r w := by exact_mod_cast hr1 w
  have hrN' : (r w : ℝ) ≤ N := by exact_mod_cast hrN w
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hrx : (r w : ℝ) * x ≤ 1 := by
    calc (r w : ℝ) * x ≤ r w * (1 / N) := mul_le_mul_of_nonneg_left hx hr0.le
      _ = r w / N := by ring
      _ ≤ 1 := (div_le_one hN0).mpr hrN'
  have hqq : (Ideal.absNorm w.1.asIdeal : ℝ)⁻¹ ≤ (Ideal.absNorm w.1.asIdeal : ℝ) ^ (-((r w : ℝ) * x)) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hq (by linarith)
  have hP : 1 ≤ ‖((A w.1).map (· ^ r w)).sum‖ ^ 2 := one_le_pow₀ (hr w)
  have hQ0 : 0 ≤ (Ideal.absNorm w.1.asIdeal : ℝ) ^ (-((r w : ℝ) * x)) := by positivity
  have hNr : 1 ≤ (N : ℝ) / r w := (one_le_div hr0).mpr hrN'
  calc (Ideal.absNorm w.1.asIdeal : ℝ)⁻¹ ≤ (Ideal.absNorm w.1.asIdeal : ℝ) ^ (-((r w : ℝ) * x)) := hqq
    _ ≤ ((N : ℝ) / r w) * (‖((A w.1).map (· ^ r w)).sum‖ ^ 2 * (Ideal.absNorm w.1.asIdeal : ℝ) ^ (-((r w : ℝ) * x))) := by
        nlinarith [mul_le_mul hNr hP zero_le_one (by positivity : (0:ℝ) ≤ N / r w)]
    _ = _ := by field_simp

end GlobalTheory.PowerSumDiv

namespace GlobalTheory.PowerSumDiv

open NumberField IsDedekindDomain

end GlobalTheory.PowerSumDiv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GenDirichletHasSumIteratedDeriv
open MeasureTheory Complex Classical Filter Topology

namespace GlobalTheory

theorem genDirichlet_term_norm (a l : ℝ) (ha : 0 ≤ a) (z : ℂ) :
    ‖(a : ℂ) * Complex.exp (-(l : ℂ) * z)‖ = a * Real.exp (-l * z.re) := by
  rw [norm_mul, Complex.norm_real, Complex.norm_exp, Real.norm_of_nonneg ha]
  congr 2
  simp

theorem genDirichlet_summable_of_le {ι : Type} (a l : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hl : ∀ i, 0 ≤ l i) {y : ℝ} (hy : Summable (fun i => a i * Real.exp (-(l i) * y)))
    {z : ℂ} (hz : y ≤ z.re) :
    Summable (fun i => (a i : ℂ) * Complex.exp (-(l i : ℂ) * z)) := by
  refine Summable.of_norm_bounded hy (fun i => ?_)
  rw [genDirichlet_term_norm _ _ (ha i)]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith [hl i])) (ha i)

theorem genDirichlet_differentiableOn {ι : Type} (a l : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hl : ∀ i, 0 ≤ l i) (s : ℝ)
    (hs : ∀ y : ℝ, s < y → Summable (fun i => a i * Real.exp (-(l i) * y))) :
    DifferentiableOn ℂ (fun z : ℂ => ∑' i, (a i : ℂ) * Complex.exp (-(l i : ℂ) * z))
      {z : ℂ | s < z.re} := by
  intro z hz
  have hz' : s < z.re := hz
  have hU : IsOpen {w : ℂ | (s + z.re) / 2 < w.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hD : DifferentiableOn ℂ (fun z : ℂ => ∑' i, (a i : ℂ) * Complex.exp (-(l i : ℂ) * z))
      {w : ℂ | (s + z.re) / 2 < w.re} :=
    Complex.differentiableOn_tsum_of_summable_norm (hs ((s + z.re) / 2) (by linarith)) (fun i => by fun_prop) hU
      (fun i w hw => by
        have hw' : (s + z.re) / 2 < w.re := hw
        rw [genDirichlet_term_norm _ _ (ha i)]
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith [hl i])) (ha i))
  exact (hD.differentiableAt (hU.mem_nhds (show (s + z.re) / 2 < z.re by linarith))).differentiableWithinAt

theorem genDirichlet_summable_pow {ι : Type} (b μ : ι → ℝ) (hb : ∀ j, 0 ≤ b j) (hμ : ∀ j, 0 ≤ μ j)
    (t : ℝ) (h : ∀ σ : ℝ, t < σ → Summable (fun j => b j * Real.exp (-(μ j) * σ))) (n : ℕ) (σ : ℝ)
    (hσ : t < σ) :
    Summable (fun j => b j * μ j ^ n * Real.exp (-(μ j) * σ)) := by
  set δ := (σ - t) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have h1 := (h (σ - δ) (by rw [hδ]; linarith)).mul_left ((n.factorial : ℝ) / δ ^ n)
  refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) h1
  · have := hb j; have := hμ j; positivity
  · have h2 := Real.pow_div_factorial_le_exp (μ j * δ) (mul_nonneg (hμ j) hδ0.le) n
    have hf : (0:ℝ) < n.factorial := by positivity
    have h3 : μ j ^ n ≤ (n.factorial : ℝ) / δ ^ n * Real.exp (μ j * δ) := by
      rw [div_le_iff₀ hf, mul_pow] at h2
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      linarith
    have h4 : Real.exp (-(μ j) * (σ - δ)) = Real.exp (μ j * δ) * Real.exp (-(μ j) * σ) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [h4]
    have h5 : 0 ≤ b j * Real.exp (-(μ j) * σ) := mul_nonneg (hb j) (Real.exp_pos _).le
    calc b j * μ j ^ n * Real.exp (-(μ j) * σ) = μ j ^ n * (b j * Real.exp (-(μ j) * σ)) := by ring
      _ ≤ ((n.factorial : ℝ) / δ ^ n * Real.exp (μ j * δ)) * (b j * Real.exp (-(μ j) * σ)) :=
        mul_le_mul_of_nonneg_right h3 h5
      _ = _ := by ring

theorem genDirichlet_hasSum_iteratedDeriv {ι : Type} (b μ : ι → ℝ) (F : ℂ → ℂ)
    (hb : ∀ j, 0 ≤ b j) (hμ : ∀ j, 0 ≤ μ j) (t : ℝ)
    (h : ∀ s : ℂ, t < s.re → HasSum (fun j => (b j : ℂ) * Complex.exp (-(μ j : ℂ) * s)) (F s))
    (n : ℕ) (s : ℂ) (hs : t < s.re) :
    HasSum (fun j => (b j : ℂ) * (-(μ j : ℂ)) ^ n * Complex.exp (-(μ j : ℂ) * s))
      (iteratedDeriv n F s) := by
  have hreal : ∀ σ : ℝ, t < σ → Summable (fun j => b j * Real.exp (-(μ j) * σ)) := by
    intro σ hσ
    have := (h σ (by simpa using hσ)).summable
    rw [← Complex.summable_ofReal]
    convert this using 2
    push_cast; rfl
  induction n generalizing s with
  | zero => simpa using h s hs
  | succ n ih =>
    set σ := (t + s.re) / 2 with hσ
    have hσ1 : t < σ := by rw [hσ]; linarith
    have hσs : σ < s.re := by rw [hσ]; linarith
    have hU : IsOpen {w : ℂ | σ < w.re} := isOpen_lt continuous_const Complex.continuous_re
    have key := Complex.hasSum_deriv_of_summable_norm
      (F := fun j w => (b j : ℂ) * (-(μ j : ℂ)) ^ n * Complex.exp (-(μ j : ℂ) * w))
      (U := {w : ℂ | σ < w.re}) (z := s)
      (genDirichlet_summable_pow b μ hb hμ t hreal n σ hσ1)
      (fun j => by fun_prop) hU (fun j w hw => by
        have hw' : σ < w.re := hw
        rw [norm_mul, norm_mul, norm_pow, norm_neg, Complex.norm_real, Complex.norm_real,
          Complex.norm_exp, Real.norm_of_nonneg (hb j), Real.norm_of_nonneg (hμ j)]
        have h0 : 0 ≤ b j * μ j ^ n := mul_nonneg (hb j) (pow_nonneg (hμ j) n)
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) h0
        have := hμ j
        simp
        nlinarith) hσs
    have hev : (fun w : ℂ => ∑' j, (b j : ℂ) * (-(μ j : ℂ)) ^ n * Complex.exp (-(μ j : ℂ) * w))
        =ᶠ[nhds s] iteratedDeriv n F := by
      filter_upwards [hU.mem_nhds hσs] with w hw
      have hw' : σ < w.re := hw
      exact (ih w (by linarith)).tsum_eq
    rw [hev.deriv_eq, ← iteratedDeriv_succ] at key
    refine (congrArg (fun f => HasSum f _) (funext fun j => ?_)).mp key
    have : HasDerivAt (fun w : ℂ => (b j : ℂ) * (-(μ j : ℂ)) ^ n * Complex.exp (-(μ j : ℂ) * w))
        ((b j : ℂ) * (-(μ j : ℂ)) ^ n * (Complex.exp (-(μ j : ℂ) * s) * (-(μ j : ℂ) * 1))) s :=
      (((hasDerivAt_id s).const_mul (-(μ j : ℂ))).cexp).const_mul _
    rw [this.deriv]; ring

theorem genDirichlet_eqOn_ball_inter {F Φ : ℂ → ℂ} {T r s : ℝ} (hr : 0 < r) (hsT : s ≤ T)
    (hF : DifferentiableOn ℂ F (Metric.ball (T : ℂ) r))
    (hΦ : DifferentiableOn ℂ Φ {z : ℂ | s < z.re})
    (heq : ∀ y : ℝ, T < y → y < T + r → F y = Φ y) :
    ∀ z ∈ Metric.ball (T : ℂ) r ∩ {z : ℂ | s < z.re}, F z = Φ z := by
  have hU : IsOpen (Metric.ball (T : ℂ) r ∩ {z : ℂ | s < z.re}) :=
    Metric.isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_re)
  have hconv : Convex ℝ (Metric.ball (T : ℂ) r ∩ {z : ℂ | s < z.re}) :=
    (convex_ball _ _).inter (convex_halfSpace_re_gt s)
  have hFa : AnalyticOnNhd ℂ F (Metric.ball (T : ℂ) r ∩ {z : ℂ | s < z.re}) :=
    (hF.mono Set.inter_subset_left).analyticOnNhd hU
  have hΦa : AnalyticOnNhd ℂ Φ (Metric.ball (T : ℂ) r ∩ {z : ℂ | s < z.re}) :=
    (hΦ.mono Set.inter_subset_right).analyticOnNhd hU
  have hc : ((T + r / 2 : ℝ) : ℂ) ∈ Metric.ball (T : ℂ) r ∩ {z : ℂ | s < z.re} := by
    constructor
    · rw [Metric.mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_lt]
      constructor <;> linarith
    · show s < ((T + r / 2 : ℝ) : ℂ).re
      rw [Complex.ofReal_re]; linarith
  have hfreq : ∃ᶠ z in 𝓝[≠] ((T + r / 2 : ℝ) : ℂ), F z = Φ z := by
    have ht : Tendsto (fun y : ℝ => (y : ℂ)) (𝓝[>] (T + r / 2)) (𝓝[≠] ((T + r / 2 : ℝ) : ℂ)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · exact (Complex.continuous_ofReal.tendsto _).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with y hy
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Complex.ofReal_inj]
        exact ne_of_gt hy
    refine ht.frequently (Eventually.frequently ?_)
    have : Set.Ioo (T + r / 2) (T + r) ∈ 𝓝[>] (T + r / 2) := Ioo_mem_nhdsGT (by linarith)
    filter_upwards [this] with y hy
    exact heq y (by linarith [hy.1]) hy.2
  exact hFa.eqOn_of_preconnected_of_frequently_eq hΦa hconv.isPreconnected hc hfreq

theorem genDirichlet_landau_step {ι : Type} (a l : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hl : ∀ i, 0 ≤ l i)
    (F : ℂ → ℂ) (x₀ T : ℝ) (hT : x₀ < T) (hFa : AnalyticAt ℂ F (T : ℂ))
    (hP : ∀ y : ℝ, T < y → HasSum (fun i => (a i : ℂ) * Complex.exp (-(l i : ℂ) * y)) (F y)) :
    ∃ t, x₀ ≤ t ∧ t < T ∧
      ∀ y : ℝ, t < y → HasSum (fun i => (a i : ℂ) * Complex.exp (-(l i : ℂ) * y)) (F y) := by
  obtain ⟨r, hr, hFr⟩ := hFa.exists_ball_analyticOnNhd
  have hFd : DifferentiableOn ℂ F (Metric.ball (T : ℂ) r) := hFr.differentiableOn
  have hrealT : ∀ y : ℝ, T < y → Summable (fun i => a i * Real.exp (-(l i) * y)) := by
    intro y hy
    have := (hP y hy).summable
    rw [← Complex.summable_ofReal]
    convert this using 2
    push_cast; rfl
  obtain ⟨δ, hδ0, hδr, hδT⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ r / 4 ∧ δ ≤ (T - x₀) / 2 :=
    ⟨min (r / 4) ((T - x₀) / 2), lt_min (by linarith) (by linarith), min_le_left _ _,
      min_le_right _ _⟩
  have hΦT := genDirichlet_differentiableOn a l ha hl T hrealT
  have hEq1 := genDirichlet_eqOn_ball_inter hr le_rfl hFd hΦT
    (fun y hy _ => ((hP y hy).tsum_eq).symm)
  have hU : IsOpen (Metric.ball (T : ℂ) r ∩ {z : ℂ | T < z.re}) :=
    Metric.isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_re)
  have hcm : ((T + δ : ℝ) : ℂ) ∈ Metric.ball (T : ℂ) r ∩ {z : ℂ | T < z.re} := by
    constructor
    · rw [Metric.mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs, abs_lt]
      constructor <;> linarith
    · show T < ((T + δ : ℝ) : ℂ).re
      rw [Complex.ofReal_re]; linarith
  have hev : F =ᶠ[𝓝 ((T + δ : ℝ) : ℂ)]
      (fun z : ℂ => ∑' i, (a i : ℂ) * Complex.exp (-(l i : ℂ) * z)) := by
    filter_upwards [hU.mem_nhds hcm] with z hz using hEq1 z hz
  have hΦsum : ∀ s : ℂ, T < s.re → HasSum (fun i => (a i : ℂ) * Complex.exp (-(l i : ℂ) * s))
      ((fun z : ℂ => ∑' i, (a i : ℂ) * Complex.exp (-(l i : ℂ) * z)) s) :=
    fun s hs => (genDirichlet_summable_of_le a l ha hl (hrealT s.re hs) le_rfl).hasSum
  have hder : ∀ n : ℕ, HasSum (fun i => (a i : ℂ) * (-(l i : ℂ)) ^ n *
      Complex.exp (-(l i : ℂ) * ((T + δ : ℝ) : ℂ))) (iteratedDeriv n F ((T + δ : ℝ) : ℂ)) := by
    intro n
    rw [hev.iteratedDeriv_eq n]
    exact genDirichlet_hasSum_iteratedDeriv a l _ ha hl T hΦsum n _
      (by rw [Complex.ofReal_re]; linarith)
  have hball : Metric.ball ((T + δ : ℝ) : ℂ) (r - δ) ⊆ Metric.ball (T : ℂ) r := by
    intro z hz
    rw [Metric.mem_ball] at hz ⊢
    have hd : dist ((T + δ : ℝ) : ℂ) (T : ℂ) = δ := by
      rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        add_sub_cancel_left, abs_of_pos hδ0]
    calc dist z T ≤ dist z ((T + δ : ℝ) : ℂ) + dist ((T + δ : ℝ) : ℂ) (T : ℂ) := dist_triangle _ _ _
      _ < r := by linarith
  have hz : ((T - δ : ℝ) : ℂ) ∈ Metric.ball ((T + δ : ℝ) : ℂ) (r - δ) := by
    rw [Metric.mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, show T - δ - (T + δ) = -(2 * δ) by ring, abs_neg, abs_of_pos (by linarith)]
    linarith
  have hTay := Complex.hasSum_re (Complex.hasSum_taylorSeries_on_ball (hFd.mono hball) hz)
  have hj : ∀ j, HasSum (fun n : ℕ => a j * Real.exp (-(l j) * (T + δ)) *
      ((2 * δ * l j) ^ n / n.factorial)) (a j * Real.exp (-(l j) * (T - δ))) := by
    intro j
    have h1 := (NormedSpace.expSeries_div_hasSum_exp (2 * δ * l j)).mul_left
      (a j * Real.exp (-(l j) * (T + δ)))
    rw [← Real.exp_eq_exp_ℝ] at h1
    have e1 : a j * Real.exp (-(l j) * (T + δ)) * Real.exp (2 * δ * l j)
        = a j * Real.exp (-(l j) * (T - δ)) := by
      rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    rw [e1] at h1
    exact h1
  have hsumT : Summable (fun i => a i * Real.exp (-(l i) * (T - δ))) := by
    refine summable_of_sum_le (fun i => mul_nonneg (ha i) (Real.exp_pos _).le)
      (c := (F ((T - δ : ℝ) : ℂ)).re) (fun S => ?_)
    refine hasSum_le (fun n => ?_) (hasSum_sum (fun j _ => hj j)) hTay
    have h2 := (hder n).mul_left ((n.factorial : ℂ)⁻¹ * (((T - δ : ℝ) : ℂ) - ((T + δ : ℝ) : ℂ)) ^ n)
    have h3 := Complex.hasSum_re h2
    have e : ∀ j, ((n.factorial : ℂ)⁻¹ * (((T - δ : ℝ) : ℂ) - ((T + δ : ℝ) : ℂ)) ^ n *
        ((a j : ℂ) * (-(l j : ℂ)) ^ n * Complex.exp (-(l j : ℂ) * ((T + δ : ℝ) : ℂ)))).re
        = a j * Real.exp (-(l j) * (T + δ)) * ((2 * δ * l j) ^ n / n.factorial) := by
      intro j
      rw [← Complex.ofReal_re (a j * Real.exp (-(l j) * (T + δ)) * ((2 * δ * l j) ^ n / n.factorial))]
      congr 1
      push_cast
      have : (2 * (δ : ℂ) * (l j : ℂ)) ^ n = ((T : ℂ) - δ - (T + δ)) ^ n * (-(l j : ℂ)) ^ n := by
        rw [← mul_pow]; congr 1; ring
      rw [this]; ring
    simp only [e] at h3
    have h4 := sum_le_hasSum S (fun j _ => by have := ha j; have := hl j; positivity) h3
    simpa only [smul_eq_mul, mul_assoc] using h4
  have hrealTd : ∀ y : ℝ, T - δ < y → Summable (fun i => a i * Real.exp (-(l i) * y)) := by
    intro y hy
    refine Summable.of_nonneg_of_le (fun i => mul_nonneg (ha i) (Real.exp_pos _).le)
      (fun i => ?_) hsumT
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith [hl i])) (ha i)
  have hΦTd := genDirichlet_differentiableOn a l ha hl (T - δ) hrealTd
  have hEq2 := genDirichlet_eqOn_ball_inter hr (by linarith) hFd hΦTd
    (fun y hy _ => ((hP y hy).tsum_eq).symm)
  refine ⟨T - δ, by linarith, by linarith, fun y hy => ?_⟩
  rcases lt_or_ge T y with hyT | hyT
  · exact hP y hyT
  · have hs := (genDirichlet_summable_of_le a l ha hl (hrealTd y hy)
      (show y ≤ (y : ℂ).re by rw [Complex.ofReal_re])).hasSum
    have hmem : (y : ℂ) ∈ Metric.ball (T : ℂ) r ∩ {z : ℂ | T - δ < z.re} := by
      constructor
      · rw [Metric.mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real,
          Real.norm_eq_abs, abs_lt]
        constructor <;> linarith
      · show T - δ < (y : ℂ).re
        rw [Complex.ofReal_re]; exact hy
    rw [hEq2 y hmem]
    exact hs

theorem landau_hasSum_of_analyticAt (ι : Type) (a l : ι → ℝ) (x₀ x₁ : ℝ) (F : ℂ → ℂ)
    (ha : ∀ i, 0 ≤ a i) (hl : ∀ i, 0 ≤ l i) (hx : x₀ < x₁)
    (hF : ∀ x : ℝ, x₀ < x → AnalyticAt ℂ F (x : ℂ))
    (h : ∀ x : ℝ, x₁ < x → HasSum (fun i => (a i : ℂ) * Complex.exp (-(l i : ℂ) * x)) (F x)) :
    ∀ x : ℝ, x₀ < x → HasSum (fun i => (a i : ℂ) * Complex.exp (-(l i : ℂ) * x)) (F x) := by
  let S : Set ℝ := {t | x₀ ≤ t ∧ ∀ y : ℝ, t < y →
    HasSum (fun i => (a i : ℂ) * Complex.exp (-(l i : ℂ) * y)) (F y)}
  have hne : S.Nonempty := ⟨x₁, hx.le, h⟩
  have hbdd : BddBelow S := ⟨x₀, fun t ht => ht.1⟩
  have hT0 : x₀ ≤ sInf S := le_csInf hne (fun t ht => ht.1)
  have hPT : ∀ y : ℝ, sInf S < y →
      HasSum (fun i => (a i : ℂ) * Complex.exp (-(l i : ℂ) * y)) (F y) := by
    intro y hy
    obtain ⟨t, ht, hty⟩ := exists_lt_of_csInf_lt hne hy
    exact ht.2 y hty
  rcases eq_or_lt_of_le hT0 with hE | hlt
  · intro x hx0
    exact hPT x (by rw [← hE]; exact hx0)
  · obtain ⟨t, ht0, htT, hPt⟩ :=
      genDirichlet_landau_step a l ha hl F x₀ (sInf S) hlt (hF _ hlt) hPT
    exact absurd (csInf_le hbdd ⟨ht0, hPt⟩) (not_le.2 htT)

theorem landau_exp_hasSum_of_analyticAt (ι : Type) (a l : ι → ℝ) (x₀ x₁ : ℝ) (G : ℂ → ℂ)
    (ha : ∀ i, 0 ≤ a i) (hl : ∀ i, 0 ≤ l i) (hx : x₀ < x₁)
    (hG : ∀ x : ℝ, x₀ < x → AnalyticAt ℂ G (x : ℂ))
    (h : ∀ x : ℝ, x₁ < x → ∃ g : ℂ,
      HasSum (fun i => (a i : ℂ) * Complex.exp (-(l i : ℂ) * x)) g ∧ G x = Complex.exp g) :
    ∀ x : ℝ, x₀ < x → ∃ g : ℂ,
      HasSum (fun i => (a i : ℂ) * Complex.exp (-(l i : ℂ) * x)) g ∧ G x = Complex.exp g := by
  have alg : ∀ (x : ℂ) (p : Σ n : ℕ, Fin n → ι),
      (((∏ k, a (p.2 k)) / (p.1.factorial : ℝ) : ℝ) : ℂ) *
        Complex.exp (-((∑ k, l (p.2 k) : ℝ) : ℂ) * x)
      = (∏ k, (a (p.2 k) : ℂ) * Complex.exp (-(l (p.2 k) : ℂ) * x)) / (p.1.factorial : ℂ) := by
    intro x p
    rw [Finset.prod_mul_distrib, ← Complex.exp_sum]
    push_cast
    rw [neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
    simp only [neg_mul]
    ring
  have key := landau_hasSum_of_analyticAt (Σ n : ℕ, Fin n → ι)
    (fun p => (∏ k, a (p.2 k)) / (p.1.factorial : ℝ)) (fun p => ∑ k, l (p.2 k)) x₀ x₁ G
    (fun p => div_nonneg (Finset.prod_nonneg fun k _ => ha _) (Nat.cast_nonneg _))
    (fun p => Finset.sum_nonneg fun k _ => hl _) hx hG (by
      intro x hx1
      obtain ⟨g, hg, hGx⟩ := h x hx1
      rw [hGx]
      convert hasSum_tuple_prod_exp _ g hg using 1
      funext p
      exact alg _ p)
  intro x hx0
  have hk := key x hx0
  have hinj : Function.Injective (fun i : ι => (⟨1, fun _ => i⟩ : Σ n : ℕ, Fin n → ι)) := by
    intro i j hij
    have := eq_of_heq (Sigma.mk.inj hij).2
    exact congrFun this 0
  have hs : Summable (fun i => (a i : ℂ) * Complex.exp (-(l i : ℂ) * x)) := by
    have := hk.summable.comp_injective hinj
    refine this.congr fun i => ?_
    simp
  refine ⟨_, hs.hasSum, ?_⟩
  refine hk.unique ?_
  convert hasSum_tuple_prod_exp _ _ hs.hasSum using 1
  funext p
  exact alg _ p

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergPartialLTendstoNeZeroAtOne
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW Filter Topology Formalism.UG GlobalTheory.RSNonvan

namespace GlobalTheory.RSNonvan

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem analyticAt_dslope' {f : ℂ → ℂ} {ξ x : ℂ} (hx : AnalyticAt ℂ f x) : AnalyticAt ℂ (dslope f ξ) x := by
  by_cases h : x = ξ
  · subst h
    obtain ⟨p, hp⟩ := hx
    exact ⟨_, hp.has_fpower_series_dslope_fslope⟩
  · have h1 : AnalyticAt ℂ (fun t => (t - ξ)⁻¹ * (f t - f ξ)) x :=
      ((analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.2 h)).mul (hx.sub analyticAt_const)
    refine h1.congr ?_
    filter_upwards [dslope_eventuallyEq_slope_of_ne f h] with t ht
    rw [ht, slope_def_module, smul_eq_mul]

theorem hasProd_of_subset {ι : Type} [DecidableEq ι] (f : ι → ℂ) {T T' : Finset ι} (h : T ⊆ T') {b : ℂ}
    (hb : HasProd (fun w : {w // w ∉ T'} => f w.1) b) :
    HasProd (fun w : {w // w ∉ T} => f w.1) ((∏ w ∈ T' \ T, f w) * b) := by
  classical
  let s : Set {w // w ∉ T} := {w | w.1 ∈ T'}
  let e1 : (↑(T' \ T) : Set ι) ≃ s :=
    { toFun := fun w => ⟨⟨w.1, (Finset.mem_sdiff.1 (Finset.mem_coe.1 w.2)).2⟩, (Finset.mem_sdiff.1 (Finset.mem_coe.1 w.2)).1⟩
      invFun := fun w => ⟨w.1.1, Finset.mem_coe.2 (Finset.mem_sdiff.2 ⟨w.2, w.1.2⟩)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e2 : {w // w ∉ T'} ≃ (sᶜ : Set {w // w ∉ T}) :=
    { toFun := fun w => ⟨⟨w.1, fun hw => w.2 (h hw)⟩, w.2⟩
      invFun := fun w => ⟨w.1.1, w.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h1 : HasProd ((fun w : {w // w ∉ T} => f w.1) ∘ ((↑) : s → {w // w ∉ T})) (∏ w ∈ T' \ T, f w) :=
    (e1.hasProd_iff).1 (Finset.hasProd (T' \ T) f)
  have h2 : HasProd ((fun w : {w // w ∉ T} => f w.1) ∘ ((↑) : (sᶜ : Set {w // w ∉ T}) → {w // w ∉ T})) b :=
    (e2.hasProd_iff).1 hb
  exact h1.mul_compl h2

theorem sat_spec {a : ℕ} {π : CG E a} {w : HeightOneSpectrum (𝓞 E)} (h : ∃ B, π.HasSat w B) :
    π.HasSat w (sat π w) := by
  unfold sat
  rw [dite_eq_left h]
  exact h.choose_spec

theorem prod_map_val (B : Multiset ℂˣ) : (B.map (fun α : ℂˣ => (α : ℂ))).prod = ((B.prod : ℂˣ) : ℂ) := by
  induction B using Multiset.induction_on with
  | empty => simp
  | cons b B ih => simp [ih]

theorem offDiag : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a b : ℕ) (σ : CG E a) (σ' : CG E b), 1 ≤ a → 1 ≤ b → σ.IsUnitary → σ'.IsUnitary → (⟨a, σ⟩ : Σ a, CG E a) ≠ ⟨b, σ'⟩ → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), IsGood T → UnrOutside T σ → UnrOutside T σ' → ∃ G : ℂ → ℂ, (∀ x : ℝ, 0 < x → AnalyticAt ℂ G (x : ℂ)) ∧ ∀ x : ℝ, 1 < x → HasProd (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => lfac σ σ' (x : ℂ) w.1) (G x) := by
  intro E _ _ _ a b σ σ' ha hb hσ hσ' hne T hgood hU hU'
  rcases lt_trichotomy a b with hab | rfl | hab
  · obtain ⟨F, H, hF, hH, hHpos, hFH⟩ := GlobalTheory.T.rankinSelberg_GLn_GLm_partialL_eq_div_entire E b a σ' σ ha hab hσ' hσ T hgood.2 hU' hU
    refine ⟨fun z => starRingEnd ℂ (F (starRingEnd ℂ z) / H (starRingEnd ℂ z)), ?_, ?_⟩
    · intro x hx
      have hopen : IsOpen {z : ℂ | H (starRingEnd ℂ z) ≠ 0} :=
        isOpen_ne_fun (hH.continuous.comp Complex.continuous_conj) continuous_const
      have hxmem : (x : ℂ) ∈ {z : ℂ | H (starRingEnd ℂ z) ≠ 0} := by
        simp only [Set.mem_setOf_eq, Complex.conj_ofReal]
        intro h0
        have := (hHpos x).1
        rw [h0, Complex.zero_re] at this
        exact lt_irrefl 0 this
      refine DifferentiableOn.analyticAt (fun z hz => ?_) (hopen.mem_nhds hxmem)
      have hd : DifferentiableAt ℂ (fun u => F u / H u) (starRingEnd ℂ z) := (hF _).div (hH _) hz
      have := hd.conj_conj
      rw [Complex.conj_conj] at this
      exact this.differentiableWithinAt
    · intro x hx
      have hp := (GlobalTheory.T.localRankinSelberg_logarithm_formula.2 E a b σ σ' hσ hσ' T hU hU' x hx).2
      have e := GlobalTheory.T.partial_rankinSelberg_product_conj_swap_real E b a σ' σ hσ' hσ T hU' hU x hx
      have h2 : ∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, lfac σ' σ (x : ℂ) w.1 = F x / H x := (hFH x hx).tprod_eq
      have h3 : ∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, lfac σ σ' (x : ℂ) w.1 =
          starRingEnd ℂ (F (starRingEnd ℂ (x : ℂ)) / H (starRingEnd ℂ (x : ℂ))) := by
        rw [e, h2, Complex.conj_ofReal]
      beta_reduce
      rw [← h3]
      exact hp.multipliable.hasProd
  · have hne' : σ ≠ σ' := fun h => hne (by rw [h])
    obtain ⟨F, hFa, hF1, hF⟩ := GlobalTheory.T.rankinSelberg_sameDegree_meromorphic_continuation E a σ σ' ha hσ hσ' T hgood hU hU'
    refine ⟨dslope F 1, fun x hx => analyticAt_dslope' (hFa x hx), fun x hx => ?_⟩
    have hx1 : (x : ℂ) ≠ 1 := by exact_mod_cast hx.ne'
    have e : dslope F 1 (x : ℂ) = F x / ((x : ℂ) - 1) := by
      rw [dslope_of_ne _ hx1, slope_def_module, hF1 hne', sub_zero, smul_eq_mul, inv_mul_eq_div]
    rw [e]
    exact hF x hx
  · obtain ⟨F, H, hF, hH, hHpos, hFH⟩ := GlobalTheory.T.rankinSelberg_GLn_GLm_partialL_eq_div_entire E a b σ σ' hb hab hσ hσ' T hgood.2 hU hU'
    refine ⟨fun z => F z / H z, fun x hx => (hF.analyticAt _).div (hH.analyticAt _) ?_, fun x hx => hFH x hx⟩
    intro h0
    have := (hHpos x).1
    rw [h0, Complex.zero_re] at this
    exact lt_irrefl 0 this

theorem tendsto_of_analyticAt {G : ℂ → ℂ} (hG : AnalyticAt ℂ G 1) :
    Tendsto (fun x : ℝ => G x) (𝓝[>] 1) (𝓝 (G 1)) := by
  have h := hG.continuousAt.comp (x := (1 : ℝ)) (by simpa using Complex.continuous_ofReal.continuousAt)
  have h2 := h.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (1 : ℝ)))
  simp only [Function.comp_def, Complex.ofReal_one] at h2
  exact h2

theorem tendsto_partialL_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a b : ℕ) (σ : CG E a) (σ' : CG E b), 1 ≤ a → 1 ≤ b → σ.IsUnitary → σ'.IsUnitary → (⟨a, σ⟩ : Σ a, CG E a) ≠ ⟨b, σ'⟩ → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), UnrOutside T σ → UnrOutside T σ' → ∃ z : ℂ, z ≠ 0 ∧ Tendsto (fun x : ℝ => ∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, locL (Ideal.absNorm w.1.asIdeal) (sat σ w.1) ((sat σ' w.1).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) (𝓝[>] 1) (𝓝 z) := by
  intro E _ _ _ a b σ σ' ha hb hσ hσ' hne T hT hT'
  classical
  obtain ⟨T', hTT', hgood⟩ := GlobalTheory.T.exists_goodRankinSelbergPlaceSet_superset_totallyComplex E T
  have hU : UnrOutside T' σ := fun w hw => hT w fun h => hw (hTT' h)
  have hU' : UnrOutside T' σ' := fun w hw => hT' w fun h => hw (hTT' h)
  obtain ⟨G, hGa, hG⟩ := offDiag E a b σ σ' ha hb hσ hσ' hne T' hgood hU hU'
  obtain ⟨G', hG'a, hG'⟩ := offDiag E b a σ' σ hb ha hσ' hσ (Ne.symm hne) T' hgood hU' hU
  obtain ⟨D, hDa, -, hD⟩ := GlobalTheory.T.rankinSelberg_sameDegree_meromorphic_continuation E a σ σ ha hσ hσ T' hgood hU hU
  obtain ⟨D', hD'a, -, hD'⟩ := GlobalTheory.T.rankinSelberg_sameDegree_meromorphic_continuation E b σ' σ' hb hσ' hσ' T' hgood hU' hU'
  have hGa1 : AnalyticAt ℂ G 1 := by simpa using hGa 1 one_pos
  have hG'a1 : AnalyticAt ℂ G' 1 := by simpa using hG'a 1 one_pos
  have hlim : Tendsto (fun x : ℝ => ∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T'}, lfac σ σ' (x : ℂ) w.1)
      (𝓝[>] 1) (𝓝 (G 1)) :=
    (tendsto_of_analyticAt hGa1).congr' (eventually_nhdsWithin_of_forall fun x hx => ((hG x hx).tprod_eq).symm)
  have hG1 : G 1 ≠ 0 := by
    intro h0
    have hG'1 : G' 1 = 0 := by
      have hlimc : Tendsto (fun x : ℝ => G' x) (𝓝[>] 1) (𝓝 (starRingEnd ℂ (G 1))) := by
        refine ((Complex.continuous_conj.tendsto _).comp (tendsto_of_analyticAt hGa1)).congr'
          (eventually_nhdsWithin_of_forall fun x hx => ?_)
        have e := GlobalTheory.T.partial_rankinSelberg_product_conj_swap_real E a b σ σ' hσ hσ' T' hU hU' x hx
        simp only [Function.comp]
        rw [← (hG x hx).tprod_eq, ← (hG' x hx).tprod_eq, e]
      rw [tendsto_nhds_unique (tendsto_of_analyticAt hG'a1) hlimc, h0, map_zero]
    let P : ℂ → ℂ := fun z => D z * D' z * dslope G 1 z * dslope G' 1 z
    have hPa : ∀ x : ℝ, 0 < x → AnalyticAt ℂ P (x : ℂ) := fun x hx =>
      (((hDa x hx).mul (hD'a x hx)).mul (analyticAt_dslope' (hGa x hx))).mul (analyticAt_dslope' (hG'a x hx))
    have hP : ∀ x : ℝ, 1 < x → ∃ g : ℂ, HasSum (fun p : {w : HeightOneSpectrum (𝓞 E) // w ∉ T'} × ℕ =>
        ((dcoef σ σ' p.1.1 p.2 : ℝ) : ℂ) * Complex.exp (-((dexp p.1.1 p.2 : ℝ) : ℂ) * (x : ℂ))) g ∧ P x = Complex.exp g := by
      intro x hx
      obtain ⟨g, hg, he⟩ := GlobalTheory.T.dirichlet_series_exponential_sum_converges E a b σ σ' hσ hσ' T' hU hU' x hx
      refine ⟨g, hg, ?_⟩
      rw [← he, (hD x hx).tprod_eq, (hD' x hx).tprod_eq, (hG x hx).tprod_eq, (hG' x hx).tprod_eq]
      have hx1 : (x : ℂ) ≠ 1 := by exact_mod_cast hx.ne'
      have hx1' : (x : ℂ) - 1 ≠ 0 := sub_ne_zero.2 hx1
      have e1 : dslope G 1 (x : ℂ) = G x / ((x : ℂ) - 1) := by
        rw [dslope_of_ne _ hx1, slope_def_module, h0, sub_zero, smul_eq_mul, inv_mul_eq_div]
      have e2 : dslope G' 1 (x : ℂ) = G' x / ((x : ℂ) - 1) := by
        rw [dslope_of_ne _ hx1, slope_def_module, hG'1, sub_zero, smul_eq_mul, inv_mul_eq_div]
      simp only [P, e1, e2]
      field_simp
    have hN : (0 : ℝ) < 1 / ((a + b : ℕ) : ℝ) := by
      have : (0 : ℝ) < ((a + b : ℕ) : ℝ) := by exact_mod_cast (show 0 < a + b by omega)
      positivity
    obtain ⟨g, hg, -⟩ := GlobalTheory.landau_exp_hasSum_of_analyticAt ({w : HeightOneSpectrum (𝓞 E) // w ∉ T'} × ℕ)
      (fun p => dcoef σ σ' p.1.1 p.2) (fun p => dexp p.1.1 p.2) 0 1 P (fun p => dcoef_nonneg _ _ _ _)
      (fun p => dexp_nonneg _ _) one_pos hPa hP _ hN
    set y : ℝ := 1 / ((a + b : ℕ) : ℝ) with hy
    have hs : Summable (fun p : {w : HeightOneSpectrum (𝓞 E) // w ∉ T'} × ℕ =>
        dcoef σ σ' p.1.1 p.2 * Real.exp (-(dexp p.1.1 p.2) * y)) := by
      rw [← Complex.summable_ofReal]
      refine hg.summable.congr fun p => ?_
      push_cast
      rfl
    refine GlobalTheory.PowerSumDiv.not_summable_psum_sq (a + b) (by omega) T'
      (fun w => (sat σ w).map (fun α : ℂˣ => (α : ℂ)) + (sat σ' w).map (fun α : ℂˣ => (α : ℂ))) ?_ ?_ (le_of_eq hy) ?_
    · intro w hw
      rw [Multiset.card_add, Multiset.card_map, Multiset.card_map, (sat_spec (hU w hw)).card, (sat_spec (hU' w hw)).card]
    · intro w hw
      rw [Multiset.prod_add, norm_mul, prod_map_val, prod_map_val, GlobalTheory.T.norm_prod_satakeParameters_unitary_eq_one E a σ w _ hσ (sat_spec (hU w hw)),
        GlobalTheory.T.norm_prod_satakeParameters_unitary_eq_one E b σ' w _ hσ' (sat_spec (hU' w hw)), one_mul]
    · refine hs.congr fun p => ?_
      have hq : (0 : ℝ) < (Ideal.absNorm p.1.1.asIdeal : ℝ) := by
        have := NumberField.HeightOneSpectrum.one_lt_absNorm p.1.1
        have : (0 : ℝ) < ((Ideal.absNorm p.1.1.asIdeal : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < Ideal.absNorm p.1.1.asIdeal)
        exact this
      simp only [dcoef, dexp]
      rw [Real.rpow_def_of_pos hq]
      have : -(((p.2 : ℝ) + 1) * Real.log (Ideal.absNorm p.1.1.asIdeal : ℝ)) * y =
          Real.log (Ideal.absNorm p.1.1.asIdeal : ℝ) * -(((p.2 : ℝ) + 1) * y) := by ring
      rw [this]
      ring
  have hfac : ∀ w ∈ T' \ T, Tendsto (fun x : ℝ => lfac σ σ' (x : ℂ) w) (𝓝[>] 1) (𝓝 (lfac σ σ' 1 w)) ∧
      lfac σ σ' 1 w ≠ 0 := by
    intro w hw
    have hw2 := (Finset.mem_sdiff.1 hw).2
    exact GlobalTheory.T.localRankinSelbergFactor_conj_tendsto_one_ne_zero (Ideal.absNorm w.asIdeal) (sat σ w) (sat σ' w) (NumberField.HeightOneSpectrum.one_lt_absNorm w)
      (GlobalTheory.T.satakeParameter_normSq_lt_absNorm_unitaryCusp E a σ ha hσ T hT w hw2) (GlobalTheory.T.satakeParameter_normSq_lt_absNorm_unitaryCusp E b σ' hb hσ' T hT' w hw2)
  refine ⟨(∏ w ∈ T' \ T, lfac σ σ' 1 w) * G 1,
    mul_ne_zero (Finset.prod_ne_zero_iff.2 fun w hw => (hfac w hw).2) hG1, ?_⟩
  have hprodlim : Tendsto (fun x : ℝ => ∏ w ∈ T' \ T, lfac σ σ' (x : ℂ) w) (𝓝[>] 1)
      (𝓝 (∏ w ∈ T' \ T, lfac σ σ' 1 w)) := tendsto_finsetProd _ fun w hw => (hfac w hw).1
  refine (hprodlim.mul hlim).congr' (eventually_nhdsWithin_of_forall fun x hx => ?_)
  have hp := (GlobalTheory.T.localRankinSelberg_logarithm_formula.2 E a b σ σ' hσ hσ' T' hU hU' x hx).2
  have h1 := hasProd_of_subset (fun w => lfac σ σ' (x : ℂ) w) hTT' hp.multipliable.hasProd
  exact h1.tprod_eq.symm

end GlobalTheory.RSNonvan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergPartialLTendstoNeZeroAtOneStatement
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankinSelberg_partialL_tendsto_ne_zero_at_one : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a b : ℕ) (σ : CG E a) (σ' : CG E b), 1 ≤ a → 1 ≤ b → σ.IsUnitary → σ'.IsUnitary → (⟨a, σ⟩ : Σ a, CG E a) ≠ ⟨b, σ'⟩ → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), UnrOutside T σ → UnrOutside T σ' → ∃ z : ℂ, z ≠ 0 ∧ Tendsto (fun x : ℝ => ∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, locL (Ideal.absNorm w.1.asIdeal) (sat σ w.1) ((sat σ' w.1).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) (𝓝[>] 1) (𝓝 z) := by
  first | (exact @GlobalTheory.RSNonvan.tendsto_partialL_ne_zero) | (exact GlobalTheory.RSNonvan.tendsto_partialL_ne_zero) | (intros; apply GlobalTheory.RSNonvan.tendsto_partialL_ne_zero  <;> assumption)
end
