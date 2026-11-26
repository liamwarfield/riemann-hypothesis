module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeviFactorInverseModulusProperties
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TendstoSmallBallDensityOfSqueeze

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsNearestPointCosetOrthogonalLieAlgebra
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsNearestPointCosetOrthogonalLieAlgebra
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

noncomputable section

namespace GlobalTheory.IwConstMin

variable {n : ℕ}

private lemma hs_eq_re_trace' (X : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.hs X = ((X * Xᴴ).trace).re := by
  simp only [Formalism.REAL.hs, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

theorem hs_unitary_sub_one {u : Matrix (Fin n) (Fin n) ℂ} (hu : uᴴ * u = 1) :
    Formalism.REAL.hs (u - 1) = 2 * ((1 : Matrix (Fin n) (Fin n) ℂ).trace).re - 2 * (u.trace).re := by
  have h2 : u * uᴴ = 1 := mul_eq_one_comm.mp hu
  rw [hs_eq_re_trace', conjTranspose_sub, conjTranspose_one]
  have e : (u - 1) * (uᴴ - 1) = 1 - u - uᴴ + 1 := by
    rw [sub_mul, mul_sub, mul_sub, h2, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul]
    abel
  rw [e, trace_add, trace_sub, trace_sub, trace_conjTranspose]
  simp only [Complex.add_re, Complex.sub_re, Complex.star_def, Complex.conj_re]
  ring

theorem re_trace_eq_zero_of_max (X u : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ t : ℝ, ((NormedSpace.exp ((t : ℂ) • X) * u).trace).re ≤ (u.trace).re) : ((X * u).trace).re = 0 := by
  let _ : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  let φ : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap (Complex.reLm ∘ₗ Matrix.traceLinearMap (Fin n) ℝ ℂ)
  have hφ : ∀ M, φ M = (M.trace).re := fun M => rfl
  have hd : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • X) * u)
      (NormedSpace.exp ((0 : ℝ) • X) * X * u) 0 :=
    (hasDerivAt_exp_smul_const X (0 : ℝ)).mul_const u
  have hf : HasDerivAt (fun t : ℝ => φ (NormedSpace.exp (t • X) * u))
      (φ (NormedSpace.exp ((0 : ℝ) • X) * X * u)) 0 :=
    φ.hasFDerivAt.comp_hasDerivAt 0 hd
  have hmax : IsLocalMax (fun t : ℝ => φ (NormedSpace.exp (t • X) * u)) 0 := by
    refine Filter.Eventually.of_forall fun t => ?_
    simp only [hφ, zero_smul, NormedSpace.exp_zero, Matrix.one_mul]
    have := h t
    rwa [GlobalTheory.IwTangent.coe_smul_eq] at this
  have h0 := hmax.hasDerivAt_eq_zero hf
  simpa [hφ, NormedSpace.exp_zero] using h0

theorem uMat_mul' {ε : Fin n → Bool} (g h : Formalism.REAL.UJ ε) : uMat (g * h) = uMat g * uMat h := rfl

theorem maxK_mul {ε : Fin n → Bool} {g h : Formalism.REAL.UJ ε} (hg : g ∈ maxK ε) (hh : h ∈ maxK ε) : g * h ∈ maxK ε := by
  have hg' : (uMat g)ᴴ * uMat g = 1 := hg
  have hh' : (uMat h)ᴴ * uMat h = 1 := hh
  show (uMat (g * h))ᴴ * uMat (g * h) = 1
  rw [uMat_mul', conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (uMat g)ᴴ, hg',
    Matrix.one_mul, hh']

theorem exists_nearest : ∀ (n : ℕ) (ε : Fin n → Bool) (S : Set (Formalism.REAL.UJ ε)) (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), IsCut ε S E → S ⊆ maxK ε → (∀ i, (E i)ᴴ = -E i) → ∀ k ∈ maxK ε, ∃ l ∈ S, crd E (uMat (l * k) - 1) = 0 ∧ ∀ l' ∈ S, nrm (uMat (l * k) - 1) ≤ nrm (uMat (l' * k) - 1) := by
  intro n ε S d E hcut hSK hE k hk
  obtain ⟨H, hHS, hSc⟩ := IsCut.subgroup hcut
  have hmemS : ∀ g, g ∈ S ↔ g ∈ H := fun g => by rw [← hHS]; rfl
  have hcpt : IsCompact S := (isCompact_maxK ε).of_isClosed_subset hSc hSK
  have hne : S.Nonempty := ⟨1, (hmemS 1).2 H.one_mem⟩
  have hcont : Continuous fun l : Formalism.REAL.UJ ε => nrm (uMat (l * k) - 1) :=
    (continuous_nrm_uMat ε).comp (continuous_mul_const k)
  obtain ⟨l, hlS, hmin⟩ := hcpt.exists_isMinOn hne hcont.continuousOn
  refine ⟨l, hlS, ?_, fun l' hl' => hmin hl'⟩
  set w := uMat (l * k) with hw
  have hwK : l * k ∈ maxK ε := maxK_mul (hSK hlS) hk
  have hwU : wᴴ * w = 1 := hwK
  funext i
  have hflow := (GlobalTheory.IwTangent.lie_algebra_of_isCut n ε S d E hcut).1 (E i)
    (Submodule.subset_span ⟨i, rfl⟩)
  have hle : ∀ t : ℝ, ((NormedSpace.exp ((t : ℂ) • E i) * w).trace).re ≤ (w.trace).re := by
    intro t
    obtain ⟨g, hgS, hg⟩ := hflow t
    have hgl : g * l ∈ S := (hmemS _).2 (H.mul_mem ((hmemS _).1 hgS) ((hmemS _).1 hlS))
    have hv : uMat (g * l * k) = NormedSpace.exp ((t : ℂ) • E i) * w := by
      rw [mul_assoc, uMat_mul', hg]
    have hvK : (uMat (g * l * k))ᴴ * uMat (g * l * k) = 1 := maxK_mul (hSK hgl) hk
    have hn : nrm (w - 1) ≤ nrm (uMat (g * l * k) - 1) := hmin hgl
    have hsq : Formalism.REAL.hs (w - 1) ≤ Formalism.REAL.hs (uMat (g * l * k) - 1) := by
      rw [← nrm_sq, ← nrm_sq]
      exact pow_le_pow_left₀ (nrm_nonneg _) hn 2
    rw [hs_unitary_sub_one hwU, hs_unitary_sub_one hvK, hv] at hsq
    linarith
  have hz : ((E i * w).trace).re = 0 := re_trace_eq_zero_of_max (E i) w hle
  have htr : ((E i).trace).re = 0 := by
    have h1 := congrArg (fun M => (M.trace).re) (hE i)
    simp only [trace_conjTranspose, Complex.star_def, Complex.conj_re, trace_neg, Complex.neg_re] at h1
    linarith
  have hcomm : ((w * E i).trace).re = ((E i * w).trace).re := by rw [trace_mul_comm]
  show ((( w - 1) * (E i)ᴴ).trace).re = 0
  rw [hE i, sub_mul, Matrix.mul_neg, Matrix.mul_neg, Matrix.one_mul, trace_sub, trace_neg, trace_neg,
    Complex.sub_re, Complex.neg_re, Complex.neg_re, hcomm, hz, htr]
  simp

end GlobalTheory.IwConstMin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsNearestPointCosetOrthogonalLieAlgebraStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nearest_point_coset_orthogonal_lieAlgebra : ∀ (n : ℕ) (ε : Fin n → Bool) (S : Set (Formalism.REAL.UJ ε)) (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), IsCut ε S E → S ⊆ maxK ε → (∀ i, (E i)ᴴ = -E i) → ∀ k ∈ maxK ε, ∃ l ∈ S, crd E (uMat (l * k) - 1) = 0 ∧ ∀ l' ∈ S, nrm (uMat (l * k) - 1) ≤ nrm (uMat (l' * k) - 1) := by
  first | exact @GlobalTheory.IwConstMin.exists_nearest | exact GlobalTheory.IwConstMin.exists_nearest | (intros; apply GlobalTheory.IwConstMin.exists_nearest <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaSlabSqueezedBetweenBalls
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaSlabSqueezedBetweenBalls
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

namespace GlobalTheory.IwConst

theorem slab_arith_lower {a s r t η u v : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s) (hst : s < t) (hrt : r < t)
    (ht : t ≤ 1 / 24) (hη : 0 < η) (htη : 3 * t * (1 + η) ≤ η) (h1 : a < 1 / 8 + s + a * s)
    (h2 : a ≤ u + a ^ 2) (h3 : u ≤ v + a * s) (h4 : v ≤ r) : a ≤ (1 + η) * r := by

  have hs24 : s < 1 / 24 := lt_of_lt_of_le hst ht
  have hA : a < 4 / 23 := by nlinarith [mul_nonneg ha (sub_nonneg.2 hs24.le)]
  have hkey : a * (1 - s - a) ≤ r := by nlinarith
  have hgap : 433 / 552 ≤ 1 - s - a := by linarith
  have hat : a * (433 / 552) < t := by nlinarith [mul_le_mul_of_nonneg_left hgap ha]
  have hsum : (1 + η) * (s + a) ≤ η := by
    nlinarith [mul_le_mul_of_nonneg_left (show s + a ≤ 3 * t by linarith) (show (0 : ℝ) ≤ 1 + η by linarith)]
  nlinarith [mul_le_mul_of_nonneg_left hkey (show (0 : ℝ) ≤ 1 + η by linarith),
    mul_le_mul_of_nonneg_left hsum ha]

theorem slab_squeeze : ∀ (n : ℕ) (ε : Fin n → Bool) (S : Set (Formalism.REAL.UJ ε)) (d : ℕ)
    (E : Fin d → Matrix (Fin n) (Fin n) ℂ), IsCut ε S E → ∀ ρ η : ℝ, 0 < ρ → ρ ≤ 1 / 8 → 0 < η →
    ∃ t : ℝ, 0 < t ∧ ∀ r : ℝ, 0 < r → r < t → ∀ k : Formalism.REAL.UJ ε, nrm (uMat k - 1) < t →
      crd E (uMat k - 1) = 0 → ∀ l ∈ S, (l ∈ hsBall ε (r / (1 + η)) → l * k ∈ slab ε E ρ r) ∧
        (l * k ∈ slab ε E ρ r → l ∈ hsBall ε ((1 + η) * r)) := by
  intro n ε S d E hS ρ η hρ hρ8 hη
  have hON := hS.isON
  obtain ⟨t, ht0, ht24, htη, htρ⟩ : ∃ t : ℝ, 0 < t ∧ t ≤ 1 / 24 ∧ 3 * t * (1 + η) ≤ η ∧ 3 * t ≤ ρ := by
    refine ⟨min (1 / 24) (min (η / (3 * (1 + η))) (ρ / 3)),
      lt_min (by norm_num) (lt_min (by positivity) (by positivity)), min_le_left _ _, ?_, ?_⟩
    · have h : min (1 / 24) (min (η / (3 * (1 + η))) (ρ / 3)) * (3 * (1 + η)) ≤ η :=
        (le_div_iff₀ (by positivity)).1 (le_trans (min_le_right _ _) (min_le_left _ _))
      linarith
    · have h := le_trans (min_le_right (1 / 24 : ℝ) _) (min_le_right (η / (3 * (1 + η))) (ρ / 3))
      linarith
  refine ⟨t, ht0, ?_⟩
  intro r hr hrt k hk hk0 l hl

  have hmul : uMat (l * k) - 1 = (uMat l - 1) + (uMat k - 1) + (uMat l - 1) * (uMat k - 1) := by
    have e : uMat (l * k) = uMat l * uMat k := rfl
    rw [e]; noncomm_ring
  have hXY : nrm ((uMat l - 1) * (uMat k - 1)) ≤ nrm (uMat l - 1) * nrm (uMat k - 1) := nrm_mul_le _ _
  have ha0 := nrm_nonneg (uMat l - 1)
  have hs0 := nrm_nonneg (uMat k - 1)
  have htle : t ≤ η := by nlinarith
  constructor
  · intro hlB
    have ha : nrm (uMat l - 1) ≤ r / (1 + η) := hlB
    have ha' : nrm (uMat l - 1) * (1 + η) ≤ r := (le_div_iff₀ (by positivity)).1 ha
    refine ⟨?_, ?_⟩
    ·
      have h1 : nrm (uMat (l * k) - 1) ≤ nrm (uMat l - 1) + nrm (uMat k - 1) + nrm ((uMat l - 1) * (uMat k - 1)) := by
        rw [hmul]
        exact le_trans (nrm_add_le _ _) (by linarith [nrm_add_le (uMat l - 1) (uMat k - 1)])
      have hat : nrm (uMat l - 1) < t := by nlinarith
      have hprod : nrm (uMat l - 1) * nrm (uMat k - 1) ≤ t * t := by
        exact mul_le_mul hat.le hk.le hs0 ht0.le
      nlinarith
    ·
      have hc : crd E (uMat (l * k) - 1) = crd E (uMat l - 1) + crd E ((uMat l - 1) * (uMat k - 1)) := by
        rw [hmul, crd_add, crd_add, hk0, add_zero]
      have hlen : len (crd E (uMat (l * k) - 1)) ≤ nrm (uMat l - 1) + nrm (uMat l - 1) * nrm (uMat k - 1) := by
        rw [hc]
        exact le_trans (len_add_le _ _)
          (add_le_add (len_crd_le hON _) (le_trans (len_crd_le hON _) hXY))
      have hsη : nrm (uMat l - 1) * nrm (uMat k - 1) ≤ nrm (uMat l - 1) * η :=
        mul_le_mul_of_nonneg_left (by linarith) ha0
      show len (crd E (uMat (l * k) - 1)) ≤ r
      nlinarith
  · intro hslab
    obtain ⟨hZ, hv⟩ := hslab
    show nrm (uMat l - 1) ≤ (1 + η) * r
    have hX : uMat l - 1 = (uMat (l * k) - 1) - (uMat k - 1) - (uMat l - 1) * (uMat k - 1) := by
      rw [hmul]; abel

    have h1 : nrm (uMat l - 1) < 1 / 8 + nrm (uMat k - 1) + nrm (uMat l - 1) * nrm (uMat k - 1) := by
      have e := nrm_sub_le ((uMat (l * k) - 1) - (uMat k - 1)) ((uMat l - 1) * (uMat k - 1))
      have e' := nrm_sub_le (uMat (l * k) - 1) (uMat k - 1)
      rw [← hX] at e
      linarith

    have h2 : nrm (uMat l - 1) ≤ len (crd E (uMat l - 1)) + nrm (uMat l - 1) ^ 2 := by
      have hp := GlobalTheory.T.cutOut_subgroup_tangent_second_order_hilbertSchmidt n ε S d E hS l hl
      have e := nrm_add_le (cmb E (crd E (uMat l - 1))) (uMat l - 1 - cmb E (crd E (uMat l - 1)))
      rw [add_sub_cancel, nrm_cmb hON] at e
      linarith

    have h3 : len (crd E (uMat l - 1)) ≤ len (crd E (uMat (l * k) - 1)) + nrm (uMat l - 1) * nrm (uMat k - 1) := by
      have hc : crd E (uMat l - 1) = crd E (uMat (l * k) - 1) + -crd E ((uMat l - 1) * (uMat k - 1)) := by
        conv_lhs => rw [hX]
        rw [crd_sub, crd_sub, hk0, sub_zero, sub_eq_add_neg]
      rw [hc]
      refine le_trans (len_add_le _ _) (add_le_add le_rfl ?_)
      rw [len_neg]
      exact le_trans (len_crd_le hON _) hXY
    exact slab_arith_lower ha0 hs0 hk hrt ht24 hη htη (by linarith) h2 h3 hv

end GlobalTheory.IwConst
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaSlabSqueezedBetweenBallsStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawa_slab_squeezed_between_balls : ∀ (n : ℕ) (ε : Fin n → Bool) (S : Set (Formalism.REAL.UJ ε)) (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), IsCut ε S E → ∀ ρ η : ℝ, 0 < ρ → ρ ≤ 1 / 8 → 0 < η → ∃ t : ℝ, 0 < t ∧ ∀ r : ℝ, 0 < r → r < t → ∀ k : Formalism.REAL.UJ ε, nrm (uMat k - 1) < t → crd E (uMat k - 1) = 0 → ∀ l ∈ S, (l ∈ hsBall ε (r / (1 + η)) → l * k ∈ slab ε E ρ r) ∧ (l * k ∈ slab ε E ρ r → l ∈ hsBall ε ((1 + η) * r)) := by
  first | exact @GlobalTheory.IwConst.slab_squeeze | exact GlobalTheory.IwConst.slab_squeeze | (intros; apply GlobalTheory.IwConst.slab_squeeze <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaNearOneCompactNearLeviIntersection
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaNearOneCompactNearLeviIntersection
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

namespace GlobalTheory.IwConst.CloseLevi

variable {n : ℕ} {ε : Fin n → Bool}

theorem isClosed_stab {a : ℕ} (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) :
    IsClosed {g : Formalism.REAL.UJ ε | ∀ i, ∀ y ∈ W i, uMat g *ᵥ y ∈ W i} := by
  have hc : Continuous (fun g : Formalism.REAL.UJ ε => uMat g) := GlobalTheory.FlagLeviGroup.continuous_uMat
  have h : {g : Formalism.REAL.UJ ε | ∀ i, ∀ y ∈ W i, uMat g *ᵥ y ∈ W i} =
      ⋂ i, ⋂ y ∈ (W i : Set (Fin n → ℂ)),
        (fun g : Formalism.REAL.UJ ε => uMat g *ᵥ y) ⁻¹' (W i : Set (Fin n → ℂ)) := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
  rw [h]
  refine isClosed_iInter fun i => isClosed_biInter fun y _ => ?_
  exact (W i).closed_of_finiteDimensional.preimage (hc.matrix_mulVec continuous_const)

theorem mem_flagM_of_keeps {a : ℕ} (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) {l : Formalism.REAL.UJ ε}
    (hl : l ∈ maxK ε) (h : ∀ i, ∀ y ∈ W i, uMat l *ᵥ y ∈ W i) : l ∈ flagM ε W := by
  have hl' : (uMat l)ᴴ * uMat l = 1 := hl
  show ∀ i, ∀ y ∈ W i, uMat l *ᵥ y ∈ W i ∧ (uMat l)ᴴ *ᵥ y ∈ W i
  intro i y hy
  exact ⟨h i y hy, GlobalTheory.FlagLeviGroup.inv_keeps hl' (W i) (h i) y hy⟩

private theorem exists_unit_valuation_le_subset_nhds {G : Type} [Group G] [TopologicalSpace G] {f : G → ℝ}
    (hf : Continuous f) (h0 : ∀ g, 0 ≤ f g) (h1 : ∀ g, f g = 0 ↔ g = 1) (hB : IsCompact {g | f g ≤ 1})
    {O : Set G} (hO : IsOpen O) (h1O : (1 : G) ∈ O) : ∃ ρ : ℝ, 0 < ρ ∧ ∀ g, f g < ρ → g ∈ O := by
  have hC : IsCompact ({g | f g ≤ 1} ∩ Oᶜ) := hB.inter_right hO.isClosed_compl
  rcases ({g | f g ≤ 1} ∩ Oᶜ).eq_empty_or_nonempty with hE | hne
  · refine ⟨1, one_pos, fun g hg => ?_⟩
    by_contra hgO
    have hgC : g ∈ ({g | f g ≤ 1} ∩ Oᶜ) := ⟨le_of_lt hg, hgO⟩
    rw [hE] at hgC
    simpa using hgC
  · obtain ⟨c, ⟨_, hcO⟩, hmin⟩ := hC.exists_isMinOn hne hf.continuousOn
    have hc : 0 < f c := by
      rcases (h0 c).lt_or_eq with h | h
      · exact h
      · exfalso
        have hc1 : c = 1 := (h1 c).1 h.symm
        rw [hc1] at hcO
        exact absurd h1O hcO
    refine ⟨min 1 (f c), lt_min one_pos hc, fun g hg => ?_⟩
    by_contra hgO
    have hgC : g ∈ ({g | f g ≤ 1} ∩ Oᶜ) := ⟨(lt_of_lt_of_le hg (min_le_left _ _)).le, hgO⟩
    have hcg : f c ≤ f g := isMinOn_iff.1 hmin g hgC
    exact absurd (lt_of_lt_of_le hg (min_le_right _ _)) (not_lt.2 hcg)

theorem close_of_compact {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {f : G → ℝ}
    (hf : Continuous f) (h0 : ∀ g, 0 ≤ f g) (h1 : ∀ g, f g = 0 ↔ g = 1) (hB : IsCompact {g | f g ≤ 1})
    {K P L : Set G} (hK : IsCompact K) (hP : IsClosed P) (hL : ∀ k ∈ K, k⁻¹ ∈ P → k⁻¹ ∈ L) {t : ℝ} (ht : 0 < t) :
    ∃ r : ℝ, 0 < r ∧ ∀ p ∈ P, ∀ k ∈ K, f (p * k) ≤ r → ∃ l ∈ L, f (l * k) < t := by

  have hloc : ∀ k ∈ K, ∀ᶠ z : ℝ × G in nhds ((0 : ℝ), k),
      ∀ p ∈ P, f (p * z.2) ≤ z.1 → ∃ l ∈ L, f (l * z.2) < t := by
    intro k hk
    by_cases hkP : k⁻¹ ∈ P
    ·
      have hkL := hL k hk hkP
      have hc : Continuous fun x : G => f (k⁻¹ * x) := hf.comp (continuous_const.mul continuous_id)
      have hopen : IsOpen {x : G | f (k⁻¹ * x) < t} := isOpen_lt hc continuous_const
      have hmem : k ∈ {x : G | f (k⁻¹ * x) < t} := by
        show f (k⁻¹ * k) < t
        rw [inv_mul_cancel, (h1 1).2 rfl]
        exact ht
      have hev : ∀ᶠ z : ℝ × G in nhds ((0 : ℝ), k), z.2 ∈ {x : G | f (k⁻¹ * x) < t} :=
        (continuous_snd.tendsto ((0 : ℝ), k)).eventually_mem (hopen.mem_nhds hmem)
      filter_upwards [hev] with z hz
      intro p _ _
      exact ⟨k⁻¹, hkL, hz⟩
    ·
      have hcont : Continuous (fun q : G × G => q.1 * q.2⁻¹) := continuous_fst.mul continuous_snd.inv
      have hopen : IsOpen ((fun q : G × G => q.1 * q.2⁻¹) ⁻¹' Pᶜ) := hP.isOpen_compl.preimage hcont
      have hmem : ((1 : G), k) ∈ (fun q : G × G => q.1 * q.2⁻¹) ⁻¹' Pᶜ := by
        show (1 : G) * k⁻¹ ∈ Pᶜ
        rw [one_mul]
        exact hkP
      obtain ⟨O, V, hO, hV, h1O, hkV, hOV⟩ := isOpen_prod_iff.1 hopen 1 k hmem
      obtain ⟨ρ, hρ, hρO⟩ := exists_unit_valuation_le_subset_nhds hf h0 h1 hB hO h1O
      have e1 : ∀ᶠ z : ℝ × G in nhds ((0 : ℝ), k), z.1 < ρ :=
        (continuous_fst.tendsto ((0 : ℝ), k)).eventually (gt_mem_nhds hρ)
      have e2 : ∀ᶠ z : ℝ × G in nhds ((0 : ℝ), k), z.2 ∈ V :=
        (continuous_snd.tendsto ((0 : ℝ), k)).eventually_mem (hV.mem_nhds hkV)
      filter_upwards [e1, e2] with z hz1 hz2
      intro p hp hpz
      exfalso
      have hO' : p * z.2 ∈ O := hρO _ (lt_of_le_of_lt hpz hz1)
      have hmem' := hOV (Set.mk_mem_prod hO' hz2)
      simp only [Set.mem_preimage, mul_inv_cancel_right, Set.mem_compl_iff] at hmem'
      exact hmem' hp
  have hev := hK.eventually_forall_of_forall_eventually (x₀ := (0 : ℝ))
    (P := fun r x => ∀ p ∈ P, f (p * x) ≤ r → ∃ l ∈ L, f (l * x) < t) hloc
  have hpos : ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < r := eventually_mem_nhdsWithin
  obtain ⟨r, hr, hrK⟩ := (hpos.and (hev.filter_mono nhdsWithin_le_nhds)).exists
  exact ⟨r, hr, fun p hp k hk hpk => hrK k hk p hp hpk⟩

theorem nrm_uMat_eq_zero (g : Formalism.REAL.UJ ε) : nrm (uMat g - 1) = 0 ↔ g = 1 := by
  rw [nrm_eq_zero, sub_eq_zero]
  constructor
  · intro h
    apply Subtype.ext
    exact Units.ext h
  · rintro rfl
    exact GlobalTheory.FlagLeviGroup.uMat_one

theorem close_levi : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ)
    (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → ∀ t : ℝ, 0 < t → ∃ r : ℝ, 0 < r ∧
    ∀ u ∈ flagN ε W, ∀ m ∈ flagM ε W, ∀ k ∈ maxK ε, nrm (uMat (u * m * k) - 1) ≤ r →
      ∃ l ∈ maxK ε ∩ flagM ε W, nrm (uMat (l * k) - 1) < t := by
  intro n ε a j W hW t ht

  have hL : ∀ k ∈ maxK ε, k⁻¹ ∈ {g : Formalism.REAL.UJ ε | ∀ i, ∀ y ∈ W i, uMat g *ᵥ y ∈ W i} →
      k⁻¹ ∈ maxK ε ∩ flagM ε W := by
    intro k hk hkP
    have hk' : k⁻¹ ∈ maxK ε := (GlobalTheory.FlagLeviGroup.compactSub (ε := ε)).inv_mem hk
    exact Set.mem_inter hk' (mem_flagM_of_keeps W hk' hkP)
  obtain ⟨r, hr, hrP⟩ := close_of_compact (G := Formalism.REAL.UJ ε) (f := fun g => nrm (uMat g - 1))
    (continuous_nrm_uMat ε) (fun g => nrm_nonneg _) (fun g => nrm_uMat_eq_zero g) (isCompact_hsBall ε 1)
    (isCompact_maxK ε) (isClosed_stab W) hL ht
  refine ⟨r, hr, fun u hu m hm k hk hle => ?_⟩
  have hm' : ∀ i, ∀ y ∈ W i, uMat m *ᵥ y ∈ W i ∧ (uMat m)ᴴ *ᵥ y ∈ W i := hm
  have hum : u * m ∈ {g : Formalism.REAL.UJ ε | ∀ i, ∀ y ∈ W i, uMat g *ᵥ y ∈ W i} := by
    rw [Set.mem_setOf_eq]
    intro i y hy
    rw [GlobalTheory.FlagLeviGroup.uMat_mul, ← Matrix.mulVec_mulVec]
    exact GlobalTheory.FlagMeas.UnipRad.keeps hW u hu i _ (hm' i y hy).1
  exact hrP (u * m) hum k hk hle

end GlobalTheory.IwConst.CloseLevi
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaNearOneCompactNearLeviIntersectionStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawa_near_one_compact_near_levi_intersection : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → ∀ t : ℝ, 0 < t → ∃ r : ℝ, 0 < r ∧ ∀ u ∈ flagN ε W, ∀ m ∈ flagM ε W, ∀ k ∈ maxK ε, nrm (uMat (u * m * k) - 1) ≤ r → ∃ l ∈ maxK ε ∩ flagM ε W, nrm (uMat (l * k) - 1) < t := by
  first | exact @GlobalTheory.IwConst.CloseLevi.close_levi | exact GlobalTheory.IwConst.CloseLevi.close_levi | (intros; apply GlobalTheory.IwConst.CloseLevi.close_levi <;> assumption)
end
end

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

namespace GlobalTheory.IwConst

theorem slab_measure_squeeze : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → ∀ (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), IsCut ε (maxK ε ∩ flagM ε W) E → (∀ i, (E i)ᴴ = -E i) → ∀ ν : Measure (Formalism.REAL.UJ ε), ν (maxK ε ∩ flagM ε W)ᶜ = 0 → (∀ l ∈ maxK ε ∩ flagM ε W, ν.map (fun g => g * l) = ν) → ∀ ρ η : ℝ, 0 < ρ → ρ ≤ 1 / 8 → 0 < η → ∀ᶠ r in (nhdsWithin (0 : ℝ) (Set.Ioi 0)), ∀ u ∈ flagN ε W, ∀ m ∈ flagM ε W, ∀ k ∈ maxK ε, u * m * k ∈ hsBall ε r → ν (hsBall ε (r / (1 + η))) ≤ ν {l | l * k ∈ slab ε E ρ r} ∧ ν {l | l * k ∈ slab ε E ρ r} ≤ ν (hsBall ε ((1 + η) * r)) := by
  intro n ε a j W hW d E hcut hskew ν hν hinv ρ η hρ hρ8 hη
  set S := maxK ε ∩ flagM ε W with hS
  obtain ⟨t, ht, hsq⟩ := GlobalTheory.T.iwasawa_slab_squeezed_between_balls n ε S d E hcut ρ η hρ hρ8 hη
  obtain ⟨r0, hr0, hnear⟩ := GlobalTheory.T.iwasawa_near_one_compact_near_levi_intersection n ε a j W hW t ht
  have hmem : Set.Iio (min t r0) ∈ nhds (0 : ℝ) := Iio_mem_nhds (lt_min ht hr0)
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hmem] with r hr hr' u hu m hm k hk hball
  have hrpos : (0 : ℝ) < r := hr
  have hrlt : r < min t r0 := hr'
  have hrt : r < t := lt_of_lt_of_le hrlt (min_le_left _ _)
  have hrr0 : r < r0 := lt_of_lt_of_le hrlt (min_le_right _ _)

  have hb : nrm (uMat (u * m * k) - 1) ≤ r := hball
  obtain ⟨l0, hl0S, hl0⟩ := hnear u hu m hm k hk (le_trans hb hrr0.le)

  obtain ⟨l1, hl1S, hcrd, hmin⟩ := GlobalTheory.T.exists_nearest_point_coset_orthogonal_lieAlgebra n ε S d E hcut (fun x hx => hx.1) hskew k hk
  have hnrm : nrm (uMat (l1 * k) - 1) < t := lt_of_le_of_lt (hmin l0 hl0S) hl0
  have key := fun l (hl : l ∈ S) => hsq r hrpos hrt (l1 * k) hnrm hcrd l hl

  have hA : ν {l | l * k ∈ slab ε E ρ r} = ν {l | l * (l1 * k) ∈ slab ε E ρ r} := by
    calc ν {l | l * k ∈ slab ε E ρ r}
        = (ν.map (fun g => g * l1)) {l | l * k ∈ slab ε E ρ r} := by rw [hinv l1 hl1S]
      _ = ν ((fun g => g * l1) ⁻¹' {l | l * k ∈ slab ε E ρ r}) :=
          (Homeomorph.mulRight l1).toMeasurableEquiv.map_apply _
      _ = ν {l | l * (l1 * k) ∈ slab ε E ρ r} := by
          congr 1
          ext l
          simp only [Set.mem_preimage, Set.mem_setOf_eq, mul_assoc]
  rw [hA]
  constructor
  · calc ν (hsBall ε (r / (1 + η)))
        ≤ ν (hsBall ε (r / (1 + η)) ∩ S ∪ Sᶜ) := by
          apply measure_mono
          intro l hl
          by_cases h : l ∈ S
          · exact Or.inl ⟨hl, h⟩
          · exact Or.inr h
      _ ≤ ν (hsBall ε (r / (1 + η)) ∩ S) + ν Sᶜ := measure_union_le _ _
      _ = ν (hsBall ε (r / (1 + η)) ∩ S) := by rw [hν, add_zero]
      _ ≤ ν {l | l * (l1 * k) ∈ slab ε E ρ r} :=
          measure_mono (fun l hl => (key l hl.2).1 hl.1)
  · calc ν {l | l * (l1 * k) ∈ slab ε E ρ r}
        ≤ ν ({l | l * (l1 * k) ∈ slab ε E ρ r} ∩ S ∪ Sᶜ) := by
          apply measure_mono
          intro l hl
          by_cases h : l ∈ S
          · exact Or.inl ⟨hl, h⟩
          · exact Or.inr h
      _ ≤ ν ({l | l * (l1 * k) ∈ slab ε E ρ r} ∩ S) + ν Sᶜ := measure_union_le _ _
      _ = ν ({l | l * (l1 * k) ∈ slab ε E ρ r} ∩ S) := by rw [hν, add_zero]
      _ ≤ ν (hsBall ε ((1 + η) * r)) :=
          measure_mono (fun l hl => (key l hl.2).2 hl.1)

end GlobalTheory.IwConst
