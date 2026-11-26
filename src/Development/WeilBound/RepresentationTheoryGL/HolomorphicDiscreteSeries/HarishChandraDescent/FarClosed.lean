module

public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.HarishChandraDescent.AdjointSignSymmetry.SquareIdentityHolds
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.HarishChandraDescent.RootInnerBounds.RootBoundOfSquareIdentity
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.HarishChandraDescent.CasimirCommutation.CommCasimirCasimirK
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.HarishChandraDescent.CommutantLemma.CommutantHolds
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.HarishChandraDescent.SmoothTranslates.AdjointEquationHolds
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.HarishChandraDescent.IntegralWeights.IntegralWeightHolds
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.HarishChandraDescent.HalfSumRootsIntegrality.HarishChandraParameterHolds
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.HarishChandraDescent.RealInnerProducts.CasimirBoundOfInputs
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.HarishChandraDescent.IdentityLemma.IdentityHolds
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.HarishChandraDescent.DiscreteSeriesData.DiscreteSeriesDataHolds
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.HarishChandraDescent.SquareAbsoluteBounds.DiscreteSeriesBoundOfInputs
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.HarishChandraDescent.EmbeddingContinuity.BlockEmbedConjTranspose
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.HarishChandraDescent.TraceSingleMoments.SecondMomentOfBounds
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.HarishChandraDescent.NormDifferenceBounds.TrialOfInputs
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.HarishChandraDescent.FarWeightBounds.LargeParameterSqrtBound
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.HarishChandraDescent.IntegerLowerBounds.BaseOfFarModelsFrame

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.HarishChandraDescent.CasimirAdjoint.CasimirAdjointHolds
noncomputable section

open Finset Matrix

namespace PositivityTheory.RgHe3

open ReciprocityTheory.ChartRestriction.DS

namespace CasimirAdjoint

theorem ent {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) (a b c d : Fin n) :
    (g * Matrix.single a b (1 : ℂ) * g⁻¹ : Matrix (Fin n) (Fin n) ℂ) c d = g c a * g⁻¹ b d := by
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and, mul_ite, ite_mul]

private theorem reorder_lemma {ι X : Type} [Fintype ι] [AddCommMonoid X] (G : ι → ι → ι → ι → X) :
    ∑ x, ∑ y, ∑ z, ∑ w, G x y z w = ∑ z, ∑ w, ∑ x, ∑ y, G x y z w := by
  calc ∑ x, ∑ y, ∑ z, ∑ w, G x y z w = ∑ x, ∑ z, ∑ y, ∑ w, G x y z w :=
        Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ z, ∑ x, ∑ y, ∑ w, G x y z w := Finset.sum_comm
    _ = ∑ z, ∑ x, ∑ w, ∑ y, G x y z w :=
        Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ z, ∑ w, ∑ x, ∑ y, G x y z w :=
        Finset.sum_congr rfl fun z _ => Finset.sum_comm

theorem reorder {ι X : Type} [Fintype ι] [AddCommMonoid X] (F : ι → ι → ι → ι → ι → ι → X) :
    ∑ a, ∑ b, ∑ e, ∑ f, ∑ c, ∑ d, F a b c d e f = ∑ c, ∑ d, ∑ e, ∑ f, ∑ a, ∑ b, F a b c d e f := by
  calc ∑ a, ∑ b, ∑ e, ∑ f, ∑ c, ∑ d, F a b c d e f
        = ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ f, F a b c d e f :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
          reorder_lemma (fun e f c d => F a b c d e f)
    _ = ∑ c, ∑ d, ∑ a, ∑ b, ∑ e, ∑ f, F a b c d e f :=
        reorder_lemma (fun a b c d => ∑ e, ∑ f, F a b c d e f)
    _ = ∑ c, ∑ d, ∑ e, ∑ f, ∑ a, ∑ b, F a b c d e f :=
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ =>
          reorder_lemma (fun a b e f => F a b c d e f)

end CasimirAdjoint

open CasimirAdjoint in
theorem casimir_adjoint_holds : CasAd := by
  intro n M _ _ E g hg
  have h : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g hg
  have key : ∀ c d e f : Fin n, ∑ a, ∑ b, g c a * g⁻¹ b d * (g e b * g⁻¹ a f) =
      (1 : Matrix (Fin n) (Fin n) ℂ) c f * (1 : Matrix (Fin n) (Fin n) ℂ) e d := by
    intro c d e f
    rw [← h, Matrix.mul_apply, Matrix.mul_apply, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  simp only [actM, casimir, ent, Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm]
  refine (reorder (fun a b c d e f => (g c a * g⁻¹ b d * (g e b * g⁻¹ a f)) • (E c d * E e f))).trans ?_
  simp only [← Finset.sum_smul, key, Matrix.one_apply, ite_mul, one_mul, zero_mul, ite_smul,
    one_smul, zero_smul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
end PositivityTheory.RgHe3
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.HarishChandraDescent.PositiveNegativeWeights.PositiveNegativeHolds
noncomputable section

open scoped InnerProductSpace

namespace PositivityTheory.RgHe3

theorem positive_negative_holds : PosNeg := by
  intro H _ _ _ a ha
  refine ⟨cfc (fun x : ℝ => max x 0) a, cfc (fun x : ℝ => max (-x) 0) a, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← cfc_sub (fun x : ℝ => max x 0) (fun x : ℝ => max (-x) 0) a]
    conv_lhs => rw [← cfc_id' ℝ a]
    refine cfc_congr fun x _ => ?_
    exact (max_zero_sub_eq_self x).symm
  · rw [← cfc_mul (fun x : ℝ => max (-x) 0) (fun x : ℝ => max x 0) a]
    rw [← cfc_zero ℝ a]
    refine cfc_congr fun x _ => ?_
    rcases le_total x 0 with h | h
    · simp [max_eq_right h]
    · simp [max_eq_right (neg_nonpos.mpr h)]
  · intro x
    have hp : 0 ≤ cfc (fun x : ℝ => max x 0) a := cfc_nonneg fun y _ => le_max_right _ _
    exact ((ContinuousLinearMap.nonneg_iff_isPositive).mp hp).re_inner_nonneg_left x
  · intro x
    have hm : 0 ≤ cfc (fun x : ℝ => max (-x) 0) a := cfc_nonneg fun y _ => le_max_right _ _
    exact ((ContinuousLinearMap.nonneg_iff_isPositive).mp hm).re_inner_nonneg_left x
  · intro S hS
    exact ⟨hS.cfc_real _, hS.cfc_real _⟩

end PositivityTheory.RgHe3
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.HarishChandraDescent.FrobeniusSpanDescent.CasimirAndRootBounds
noncomputable section

open Finset
open scoped InnerProductSpace

namespace PositivityTheory.RgHe3

open ReciprocityTheory.ChartRestriction.DS

namespace DescentAux

variable {n : ℕ} {ε : Fin n → Bool} {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M]
  {E : Fin n → Fin n → Module.End ℂ M}

theorem re_cas_le (hSq : SqId) (hE : IsGlRep E) (hU : IsInfUnitary ε E) {L : Fin n → ℝ} {y : M}
    (hy : IsKHWVec ε E L y) : (⟪casimir E y, y⟫_ℂ).re ≤ casValK ε L * ‖y‖ ^ 2 := by
  unfold SqId ForAlg at hSq
  have hd := (hSq n ε M E hE hU y).2.1
  have hnn : 0 ≤ ∑ a : Fin n, ∑ b ∈ Finset.univ.filter (fun b => ε b ≠ ε a), ‖(E a b) y‖ ^ 2 :=
    Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => by positivity))
  have hK : (⟪casimirK ε E y, y⟫_ℂ).re = casValK ε L * ‖y‖ ^ 2 := by
    rw [casimirK_khwVec ε hE hy, inner_smul_left, inner_self_eq_norm_sq_to_K]
    simp [casValK]
    left
    norm_cast
  linarith

theorem abs_root_le (a b c : Fin n) : |root a b c| ≤ 1 := by
  unfold root
  simp only [Pi.sub_apply, Pi.single_apply]
  split_ifs <;> norm_num

theorem main (hSq : SqId) (hK : KIrrEx) (hD : Drop) (hE : IsGlRep E) (hU : IsInfUnitary ε E)
    (N : Submodule ℂ M) (hN : Stab E N) (μ L : Fin n → ℝ) (R τ s : ℝ) (J : ℕ) (w : ℝ)
    (hR : ∀ y ∈ N, (casValK ε L - R) * ‖y‖ ^ 2 ≤ (⟪casimir E y, y⟫_ℂ).re)
    (hτ : ∀ a b, a < b → τ ≤ μ a - μ b) (hJ : R < J * w)
    (hw : w ≤ 2 * (τ - 2 * (s + J)) - 2 * n - 2) :
    ∀ k : ℕ, k ≤ J → ∀ (L' : Fin n → ℝ), ∀ y ∈ N, y ≠ 0 → KFin ε E y → IsKHWVec ε E L' y →
      (∀ a, |L' a - μ a| ≤ s + ((J : ℝ) - (k : ℝ))) → casValK ε L' ≤ casValK ε L - ((J : ℝ) - (k : ℝ)) * w →
      ∃ (L'' : Fin n → ℝ) (V : Submodule ℂ M), (∀ a, |L'' a - μ a| ≤ s + J) ∧ IsKIrrHW ε E L'' V ∧
        NoDown ε E L'' V := by
  unfold KIrrEx ForAlg at hK
  intro k
  induction k with
  | zero =>
    intro _ L' y hyN hy0 _ hyHW _ hcas
    exfalso
    have h1 := hR y hyN
    have h2 := re_cas_le hSq hE hU hyHW
    have hpos : 0 < ‖y‖ ^ 2 := pow_pos (norm_pos_iff.mpr hy0) 2
    have hc : casValK ε L' ≤ casValK ε L - J * w := by simpa using hcas
    have : casValK ε L - R ≤ casValK ε L' := le_of_mul_le_mul_right (h1.trans h2) hpos
    linarith
  | succ k ih =>
    intro hk L' y hyN hy0 hyK hyHW hbd hcas
    obtain ⟨V, hVN, hIrr⟩ := hK n ε M E hE hU N hN L' y hyN hy0 hyK hyHW
    have hk0 : (0:ℝ) ≤ k := by positivity
    by_cases hND : NoDown ε E L' V
    · refine ⟨L', V, fun a => ?_, hIrr, hND⟩
      have := hbd a
      push_cast at this
      linarith
    · unfold NoDown at hND
      push_neg at hND
      obtain ⟨a, b, hab, _, v, hv, hvHW, hv0⟩ := hND
      apply ih (by omega) (L' - root a b) v
        (layer_le_of_stable hVN (fun c d u hu => hN c d u hu) 1 hv) hv0
        ⟨layer ε E V 1, finiteDimensional_layer hIrr.1 1, layer_kStable hE hIrr.2.1 1, hv⟩ hvHW
      · intro c
        have h1 := abs_le.mp (hbd c)
        have h2 := abs_le.mp (abs_root_le a b c)
        push_cast at h1
        simp only [Pi.sub_apply]
        rw [abs_le]
        constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
      · have hdrop := hD n ε L' a b hab.ne
        have ha := abs_le.mp (hbd a)
        have hb := abs_le.mp (hbd b)
        have ht := hτ a b hab
        push_cast at ha hb hcas
        nlinarith [ha.1, ha.2, hb.1, hb.2]

end DescentAux

theorem mem_span_of_frobenius_mem_span : SqId → KIrrEx → Drop → Descent := by
  unfold Descent ForAlg
  intro hSq hK hD n ε M _ _ E hE hU N hN μ L R τ s J hR hτ hs hJ y hyN hy0 hyK hyHW
  exact DescentAux.main hSq hK hD hE hU N hN μ L R τ s J _ hR hτ hJ le_rfl J le_rfl L y hyN hy0
    hyK hyHW (fun a => by simpa using hs a) (by simp)

end PositivityTheory.RgHe3
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.HarishChandraDescent.IrreducibleKTypes.KIrreducibleExistenceHolds
noncomputable section

open Finset
open scoped InnerProductSpace

namespace PositivityTheory.RgHe3

open ReciprocityTheory.ChartRestriction.DS

namespace KIrreducibleExistence

variable {n : ℕ} {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M}

theorem khw_proj (hU : IsKUnitary ε E) {S : Submodule ℂ M} [S.HasOrthogonalProjection] (hS : IsKStableSub ε E S)
    {L : Fin n → ℝ} {w : M} (hw : IsKHWVec ε E L w) : IsKHWVec ε E L (S.starProjection w) := by
  refine ⟨fun a => ?_, fun a b hab he => ?_⟩
  · rw [← starProjection_comm hU hS rfl, hw.1 a, map_smul]
  · rw [← starProjection_comm hU hS he, hw.2 a b hab he, map_zero]

theorem main (hU : IsInfUnitary ε E) (F : Submodule ℂ M) (hF : FiniteDimensional ℂ F)
    (hFk : IsKStableSub ε E F) (L : Fin n → ℝ) (y : M) (hyF : y ∈ F) (hy0 : y ≠ 0) (hy : IsKHWVec ε E L y) :
    ∃ V : Submodule ℂ M, V ≤ F ∧ IsKIrrHW ε E L V := by
  classical
  have hKU := isKUnitary_of_isInfUnitary hU
  let P : ℕ → Prop := fun k => ∃ S : Submodule ℂ M, S ≤ F ∧ IsKStableSub ε E S ∧ Module.finrank ℂ S = k ∧
    ∃ w ∈ S, w ≠ 0 ∧ IsKHWVec ε E L w
  have hP : ∃ k, P k := ⟨_, F, le_rfl, hFk, rfl, y, hyF, hy0, hy⟩
  obtain ⟨S, hSF, hSk, hSr, w, hwS, hw0, hw⟩ := Nat.find_spec hP
  have hmin : ∀ S' : Submodule ℂ M, S' ≤ F → IsKStableSub ε E S' → (∃ w ∈ S', w ≠ 0 ∧ IsKHWVec ε E L w) →
      Nat.find hP ≤ Module.finrank ℂ S' := fun S' h1 h2 h3 => Nat.find_min' hP ⟨S', h1, h2, rfl, h3⟩
  have hSfd : FiniteDimensional ℂ S := Submodule.finiteDimensional_of_le hSF
  refine ⟨S, hSF, hSfd, hSk, fun S' hS'S hS'k => ?_, w, hwS, hw0, hw⟩
  by_contra hne
  push Not at hne
  obtain ⟨h1, h2⟩ := hne
  have hS'fd : FiniteDimensional ℂ S' := Submodule.finiteDimensional_of_le hS'S
  have hlt : S' < S := lt_of_le_of_ne hS'S h2
  by_cases hw1 : S'.starProjection w = 0
  · have hwo : w ∈ S'ᗮ := by
      have := Submodule.sub_starProjection_mem_orthogonal (K := S') w
      rwa [hw1, sub_zero] at this
    set T : Submodule ℂ M := S'ᗮ ⊓ S with hT
    have hTk : IsKStableSub ε E T := fun a b h v hv =>
      ⟨orthogonal_kStable hKU hS'k a b h v hv.1, hSk a b h v hv.2⟩
    have hTS : T < S := by
      refine lt_of_le_of_ne inf_le_right fun hTe => h1 ?_
      have hle : S' ≤ S'ᗮ := hS'S.trans (hTe ▸ inf_le_left)
      exact (Submodule.orthogonal_disjoint S').eq_bot_of_le hle
    have h3 := hmin T (inf_le_right.trans hSF) hTk ⟨w, ⟨hwo, hwS⟩, hw0, hw⟩
    have h4 := Submodule.finrank_lt_finrank_of_lt hTS
    omega
  · have h3 := hmin S' (hS'S.trans hSF) hS'k
      ⟨S'.starProjection w, Submodule.starProjection_apply_mem S' w, hw1, khw_proj hKU hS'k hw⟩
    have h4 := Submodule.finrank_lt_finrank_of_lt hlt
    omega

end KIrreducibleExistence

theorem k_irreducible_existence_holds : KIrrEx := by
  intro n ε M _ _ E _ hU N hN L y hyN hy0 hyK hy
  obtain ⟨F, hF, hFk, hyF⟩ := hyK
  have hF' : FiniteDimensional ℂ (F ⊓ N : Submodule ℂ M) := Submodule.finiteDimensional_of_le inf_le_left
  have hFk' : IsKStableSub ε E (F ⊓ N) := fun a b h v hv => ⟨hFk a b h v hv.1, hN a b v hv.2⟩
  obtain ⟨V, hV, hVi⟩ := KIrreducibleExistence.main hU (F ⊓ N) hF' hFk' L y ⟨hyF, hyN⟩ hy0 hy
  exact ⟨V, hV.trans inf_le_right, hVi⟩

end PositivityTheory.RgHe3
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.HarishChandraDescent.ProjectionCommutation.InverseHolds
noncomputable section

open scoped InnerProductSpace

namespace PositivityTheory.RgHe3

namespace InverseCommuting

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem commute_proj (K : Submodule ℂ H) [K.HasOrthogonalProjection] (A : H →L[ℂ] H)
    (hA : ∀ x ∈ K, A x ∈ K) (hA' : ∀ x ∈ K, ContinuousLinearMap.adjoint A x ∈ K) :
    Commute K.starProjection A := by
  have hPmem : ∀ v : H, K.starProjection v ∈ K := by
    intro v
    rw [Submodule.starProjection_apply]
    exact Submodule.coe_mem _
  have hzero : ∀ v ∈ Kᗮ, K.starProjection v = 0 := by
    intro v hv
    rw [Submodule.starProjection_apply, Submodule.coe_eq_zero]
    exact Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal hv
  show K.starProjection * A = A * K.starProjection
  ext x
  simp only [ContinuousLinearMap.mul_apply]
  have hw : x - K.starProjection x ∈ Kᗮ := K.sub_starProjection_mem_orthogonal x
  have hAw : A (x - K.starProjection x) ∈ Kᗮ := by
    rw [Submodule.mem_orthogonal]
    intro k hk
    rw [← ContinuousLinearMap.adjoint_inner_left]
    exact (Submodule.mem_orthogonal _ _).1 hw _ (hA' k hk)
  have e1 : K.starProjection (A (K.starProjection x)) = A (K.starProjection x) :=
    Submodule.starProjection_eq_self_iff.2 (hA _ (hPmem x))
  have e2 := hzero _ hAw
  have hx : x = K.starProjection x + (x - K.starProjection x) := by abel
  calc K.starProjection (A x)
      = K.starProjection (A (K.starProjection x)) + K.starProjection (A (x - K.starProjection x)) := by
        conv_lhs => rw [hx]
        rw [map_add (f := _), map_add (f := _)]
    _ = A (K.starProjection x) := by rw [e1, e2, add_zero]

end InverseCommuting

open InverseCommuting

set_option maxHeartbeats 800000 in
theorem inverse_holds : Inv := by
  intro H _ _ _ D B ι U hD hB hnorm hadj hU hcomm
  let f : ↥D →ₗ[ℂ] H := D.subtype ∘ₗ B
  have hf_inj : Function.Injective f := by
    intro x y hxy
    have h1 : ‖x - y‖ ≤ ‖B (x - y)‖ := hnorm _
    have h0 : B (x - y) = 0 := by
      rw [map_sub]
      exact sub_eq_zero.2 (Subtype.ext hxy)
    rw [h0, norm_zero] at h1
    exact sub_eq_zero.1 (norm_le_zero_iff.1 h1)
  let R : Submodule ℂ H := LinearMap.range f
  let eqv : ↥D ≃ₗ[ℂ] ↥R := LinearEquiv.ofInjective f hf_inj
  have heqv : ∀ z : ↥D, ((eqv z : ↥R) : H) = ((B z : ↥D) : H) := fun z => LinearEquiv.ofInjective_apply f z
  let g₀ : ↥R →ₗ[ℂ] H := D.subtype ∘ₗ eqv.symm.toLinearMap
  have hg₀ : ∀ r : ↥R, ‖g₀ r‖ ≤ 1 * ‖r‖ := by
    intro r
    have h2 := heqv (eqv.symm r)
    rw [eqv.apply_symm_apply] at h2
    rw [one_mul]
    calc ‖g₀ r‖ = ‖eqv.symm r‖ := rfl
      _ ≤ ‖B (eqv.symm r)‖ := hnorm _
      _ = ‖(r : H)‖ := by
        show ‖((B (eqv.symm r) : ↥D) : H)‖ = ‖(r : H)‖
        rw [h2]
      _ = ‖r‖ := rfl
  let g : ↥R →L[ℂ] H := g₀.mkContinuous 1 hg₀
  have hgB : ∀ x : ↥D, g ⟨((B x : ↥D) : H), LinearMap.mem_range_self f x⟩ = x := by
    intro x
    show ((eqv.symm ⟨((B x : ↥D) : H), LinearMap.mem_range_self f x⟩ : ↥D) : H) = x
    congr 1
    apply eqv.injective
    rw [eqv.apply_symm_apply]
    apply Subtype.ext
    exact (heqv x).symm
  have hUR : ∀ i, ∀ v ∈ R, U i v ∈ R := by
    rintro i v ⟨x, rfl⟩
    obtain ⟨y, -, hy2⟩ := hU i x
    exact ⟨y, hy2⟩
  let K : Submodule ℂ H := R.topologicalClosure
  have hKcl : IsClosed (K : Set H) := R.isClosed_topologicalClosure
  have hUK : ∀ i, ∀ v ∈ K, U i v ∈ K := by
    intro i
    have hle : R ≤ K.comap (U i : H →ₗ[ℂ] H) := fun v hv => R.le_topologicalClosure (hUR i v hv)
    have hcl : IsClosed ((K.comap (U i : H →ₗ[ℂ] H) : Set H)) := hKcl.preimage (U i).continuous
    intro v hv
    exact Submodule.topologicalClosure_minimal R hle hcl hv
  haveI : IsClosed (K : Set H) := hKcl
  haveI : CompleteSpace K := IsClosed.completeSpace_coe
  have hPcomm : ∀ i, Commute K.starProjection (U i) := by
    intro i
    refine commute_proj K (U i) (hUK i) ?_
    intro v hv
    obtain ⟨j, hj⟩ := hadj i
    rw [hj]
    exact hUK j v hv
  have hDK : ∀ x : ↥D, (x : H) ∈ K := by
    intro x
    obtain ⟨y, hy1, hy2⟩ := hcomm K.starProjection hPcomm x
    have hBx : K.starProjection ((B x : ↥D) : H) = ((B x : ↥D) : H) :=
      Submodule.starProjection_eq_self_iff.2 (R.le_topologicalClosure ⟨x, rfl⟩)
    have hByx : B y = B x := Subtype.ext (hy2.trans hBx)
    have hyx : y = x := hf_inj (by
      show ((B y : ↥D) : H) = ((B x : ↥D) : H)
      rw [hByx])
    apply Submodule.starProjection_eq_self_iff.1
    rw [← hy1, hyx]
  have hKtop : K = ⊤ := by
    rw [eq_top_iff]
    have hsub : (D : Set H) ⊆ K := fun v hv => hDK ⟨v, hv⟩
    intro v _
    have hv : v ∈ closure (D : Set H) := by
      rw [hD.closure_eq]
      trivial
    exact (closure_minimal hsub hKcl) hv
  have hRd : Dense (R : Set H) := by
    rw [dense_iff_closure_eq, ← Submodule.topologicalClosure_coe]
    show ((K : Set H)) = Set.univ
    rw [hKtop]
    rfl
  have hRdense : DenseRange R.subtypeL := hRd.denseRange_val
  have hRui : IsUniformInducing R.subtypeL := isUniformEmbedding_subtype_val.isUniformInducing
  let T : H →L[ℂ] H := g.extend R.subtypeL
  have hT : ∀ r : ↥R, T r = g r := fun r => ContinuousLinearMap.extend_eq g hRdense hRui r
  have hTB : ∀ x : ↥D, T ((B x : ↥D) : H) = x := by
    intro x
    have h3 := hT ⟨((B x : ↥D) : H), LinearMap.mem_range_self f x⟩
    rw [hgB] at h3
    exact h3
  have base : ∀ x y : ↥D, ⟪T ((B x : ↥D) : H), ((B y : ↥D) : H)⟫_ℂ = ⟪((B x : ↥D) : H), T ((B y : ↥D) : H)⟫_ℂ := by
    intro x y
    rw [hTB, hTB]
    exact (hB x y).symm
  have step1 : ∀ (u : H) (y : ↥D), ⟪T u, ((B y : ↥D) : H)⟫_ℂ = ⟪u, T ((B y : ↥D) : H)⟫_ℂ := by
    intro u y
    have hfun := Continuous.ext_on hRd (T.continuous.inner continuous_const)
      (continuous_id.inner continuous_const)
      (f := fun u => ⟪T u, ((B y : ↥D) : H)⟫_ℂ) (g := fun u => ⟪u, T ((B y : ↥D) : H)⟫_ℂ)
      (by
        rintro _ ⟨x, rfl⟩
        exact base x y)
    exact congrFun hfun u
  have hsym : ∀ u v : H, ⟪T u, v⟫_ℂ = ⟪u, T v⟫_ℂ := by
    intro u v
    have hfun := Continuous.ext_on hRd (continuous_const.inner continuous_id)
      (continuous_const.inner T.continuous)
      (f := fun v => ⟪T u, v⟫_ℂ) (g := fun v => ⟪u, T v⟫_ℂ)
      (by
        rintro _ ⟨y, rfl⟩
        exact step1 u y)
    exact congrFun hfun v
  refine ⟨T, ?_, ?_, hTB⟩
  · show star T = T
    rw [ContinuousLinearMap.star_eq_adjoint]
    exact ((ContinuousLinearMap.eq_adjoint_iff T T).2 hsym).symm
  · intro i
    show T * U i = U i * T
    apply ContinuousLinearMap.coeFn_injective
    refine Continuous.ext_on hRd (T * U i).continuous (U i * T).continuous ?_
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, hy1, hy2⟩ := hU i x
    show T (U i ((B x : ↥D) : H)) = U i (T ((B x : ↥D) : H))
    rw [← hy2, hTB, hTB, hy1]

end PositivityTheory.RgHe3
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.HarishChandraDescent.MatrixEntryBounds.MatrixBoundHolds
noncomputable section

open Finset
open scoped InnerProductSpace

namespace PositivityTheory.RgHe3

open ReciprocityTheory.ChartRestriction.DS

theorem matrix_bound_holds : MatBd := by
  intro n ε M _ _ E _ _ Λ A v hv hA hoff Y
  have hsplit : actM E Y v - (∑ c : Fin n, Y c c * (Λ c : ℂ)) • v
      = ∑ a : Fin n, ∑ b : Fin n, Y a b • (E a b v - if a = b then (Λ a : ℂ) • v else 0) := by
    simp only [actM, LinearMap.sum_apply, LinearMap.smul_apply, smul_sub,
      Finset.sum_sub_distrib, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      Finset.sum_smul, mul_smul]
  rw [hsplit]
  have hb : ∀ a b : Fin n, ‖Y a b • (E a b v - if a = b then (Λ a : ℂ) • v else 0)‖
      ≤ ‖Y a b‖ * (A * ‖v‖) := by
    intro a b
    rw [norm_smul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    by_cases hab : a = b
    · subst hab
      simp [hv a]
      positivity
    · simp only [hab, if_false, sub_zero]
      exact hoff a b hab
  calc _ ≤ ∑ a : Fin n, ‖∑ b : Fin n, Y a b • (E a b v - if a = b then (Λ a : ℂ) • v else 0)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ a : Fin n, ∑ b : Fin n, ‖Y a b‖ * (A * ‖v‖) :=
        Finset.sum_le_sum fun a _ => (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => hb a b)
    _ = _ := by simp only [Finset.sum_mul, mul_assoc]

end PositivityTheory.RgHe3
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.HarishChandraDescent.MarkovInequality.MarkovInequalityHolds
noncomputable section

open scoped InnerProductSpace

namespace PositivityTheory.RgHe3

theorem markov_inequality_holds : Markov := by
  intro M _ _ u Z R hu hR hZ hpos x hx
  have e : ∀ (r : ℝ) (y : M), r • y = (r : ℂ) • y := fun r y =>
    (RCLike.real_smul_eq_coe_smul (K := ℂ) r y)
  have hv : u x ∈ Z := hZ x hx
  have hw : u (u x) ∈ Z := hZ _ hv
  have h1 := hpos (x - (R⁻¹ : ℂ) • u x) (Z.sub_mem hx (Z.smul_mem _ hv))
  have h2 := hpos (u x - (R⁻¹ : ℂ) • u (u x)) (Z.sub_mem hv (Z.smul_mem _ hw))
  simp only [e, map_add (f := _), map_sub, map_smul, add_sub_cancel_left, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, Complex.conj_ofReal,
    Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, ← Complex.ofReal_inv] at h1 h2 ⊢
  rw [hu (u x) x, hu (u (u x)) x, ← hu (u x) (u x)] at *
  rw [hu (u (u x)) (u x)] at h2
  generalize (⟪u x, x⟫_ℂ).re = p at *
  generalize (⟪u x, u x⟫_ℂ).re = a at *
  generalize (⟪u (u x), u x⟫_ℂ).re = q at *
  generalize (⟪u (u x), u (u x)⟫_ℂ).re = b at *
  generalize (⟪u (u (u x)), u (u x)⟫_ℂ).re = r at *
  have hR0 : R ≠ 0 := hR.ne'
  rw [le_div_iff₀ (by positivity)]
  have hs : R⁻¹ * R = 1 := inv_mul_cancel₀ hR0
  have hc : (R ^ 2)⁻¹ = R⁻¹ ^ 2 := (inv_pow R 2).symm
  rw [hc]
  have key : p + R⁻¹ ^ 2 * q + R⁻¹ ^ 2 * (q + R⁻¹ ^ 2 * r)
      - (R⁻¹ ^ 2 * a + R⁻¹ ^ 2 * (R⁻¹ ^ 2 * b)) * (2 * R)
      = (p - R⁻¹ * a - R⁻¹ * (a - R⁻¹ * q))
        + R⁻¹ ^ 2 * (q - R⁻¹ * b - R⁻¹ * (b - R⁻¹ * r)) := by
    linear_combination (-(2 * R⁻¹ * a + 2 * R⁻¹ ^ 3 * b)) * hs
  nlinarith [mul_nonneg (sq_nonneg R⁻¹) h2]

end PositivityTheory.RgHe3
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.HarishChandraDescent.ApproximationLemma.ApproximationOfSquareIdentity
noncomputable section

open Finset
open scoped InnerProductSpace

namespace PositivityTheory.RgHe3

open ReciprocityTheory.ChartRestriction.DS

namespace ApproximationSums

variable {n : ℕ} {ε : Fin n → Bool} {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M]
  {E : Fin n → Fin n → Module.End ℂ M}

theorem split_sum (a : Fin n) (x : M) :
    ∑ b, ‖E a b x‖ ^ 2 = ∑ b ∈ univ.filter (fun b => ε b = ε a), ‖E a b x‖ ^ 2 +
      ∑ b ∈ univ.filter (fun b => ε b ≠ ε a), ‖E a b x‖ ^ 2 := by
  exact (Finset.sum_filter_add_sum_filter_not univ (fun b => ε b = ε a) _).symm

theorem sum_sq_eq (hSq : SqId) (hE : IsGlRep E) (hU : IsInfUnitary ε E) (x : M) :
    ∑ a, ∑ b, ‖E a b x‖ ^ 2 = 2 * (⟪casimirK ε E x, x⟫_ℂ).re - (⟪casimir E x, x⟫_ℂ).re := by
  obtain ⟨h1, h2, -⟩ := hSq n ε M E hE hU x
  rw [Finset.sum_congr rfl fun a _ => split_sum (ε := ε) (E := E) a x, Finset.sum_add_distrib]
  linarith

end ApproximationSums

open ApproximationSums in
theorem approximation_of_square_identity : SqId → Approx := by
  intro hSq n ε M _ _ E hE hU c hc F hF hK η f hf
  haveI := hF
  have hPF : F.starProjection η ∈ F := F.starProjection_apply_mem η
  have hbound : ‖η - F.starProjection η‖ ≤ ‖η - f‖ := by
    rw [Submodule.starProjection_minimal (U := F) η]
    exact ciInf_le ⟨0, by rintro _ ⟨x, rfl⟩; exact norm_nonneg _⟩ (⟨f, hf⟩ : F)
  refine ⟨F.starProjection η, hPF, hbound, ?_⟩
  set P := F.starProjection η with hPdef
  set u := η - P with hu
  have hKF : ∀ v ∈ F, casimirK ε E v ∈ F := by
    intro v hv
    simp only [casimirK, LinearMap.sum_apply, Module.End.mul_apply]
    refine F.sum_mem (fun a _ => F.sum_mem (fun b hb => ?_))
    have hb' : ε b = ε a := (Finset.mem_filter.1 hb).2
    exact hK a b hb'.symm _ (hK b a hb' v hv)
  have horth : ∀ w ∈ F, ⟪w, u⟫_ℂ = 0 := fun w hw => by
    rw [inner_eq_zero_symm]
    exact Submodule.starProjection_inner_eq_zero (K := F) η w hw
  have hw : 2 • casimirK ε E P - (c : ℂ) • P ∈ F :=
    F.sub_mem (F.nsmul_mem (hKF P hPF) 2) (F.smul_mem _ hPF)
  have hsplit : 2 • casimirK ε E η - (c : ℂ) • η =
      (2 • casimirK ε E u - (c : ℂ) • u) + (2 • casimirK ε E P - (c : ℂ) • P) := by
    have he : η = u + P := by simp [hu]
    conv_lhs => rw [he]
    rw [map_add (f := _), smul_add, smul_add]
    abel
  have hkey : (∑ a, ∑ b, ‖E a b u‖ ^ 2) = (⟪2 • casimirK ε E η - (c : ℂ) • η, u⟫_ℂ).re := by
    rw [sum_sq_eq hSq hE hU u, hsplit, inner_add_left, horth _ hw, add_zero, inner_sub_left,
      two_nsmul, inner_add_left, hc u, Complex.sub_re, Complex.add_re]
    ring
  rw [hkey]
  refine le_trans (Complex.re_le_norm _) (le_trans (norm_inner_le_norm _ _) ?_)
  gcongr
  exact le_of_eq (by simp only [two_smul, two_nsmul])

end PositivityTheory.RgHe3
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.HarishChandraDescent.RhoAbsoluteBounds.AbsRhoCLe
noncomputable section

open Finset

namespace PositivityTheory.RgHe3.DropRoots

open ReciprocityTheory.ChartRestriction.DS

theorem abs_rhoC_le {n : ℕ} (ε : Fin n → Bool) (a : Fin n) : |rhoC ε a| ≤ (n : ℝ) / 2 := by
  unfold rhoC
  have h1 : ((univ.filter fun b => a < b ∧ ε b = ε a).card : ℝ) ≤ n := by
    exact_mod_cast (card_filter_le _ _).trans (by simp)
  have h2 : ((univ.filter fun b => b < a ∧ ε b = ε a).card : ℝ) ≤ n := by
    exact_mod_cast (card_filter_le _ _).trans (by simp)
  have h3 : (0 : ℝ) ≤ ((univ.filter fun b => a < b ∧ ε b = ε a).card : ℝ) := Nat.cast_nonneg _
  have h4 : (0 : ℝ) ≤ ((univ.filter fun b => b < a ∧ ε b = ε a).card : ℝ) := Nat.cast_nonneg _
  rw [abs_le]
  constructor <;> linarith

theorem dot_root {n : ℕ} (x : Fin n → ℝ) {a b : Fin n} (hab : a ≠ b) : dot x (root a b) = x a - x b := by
  simp [dot, root, Pi.single_apply, mul_sub, Finset.sum_sub_distrib]

end PositivityTheory.RgHe3.DropRoots

namespace PositivityTheory.RgHe3

open ReciprocityTheory.ChartRestriction.DS PositivityTheory.RgHe3.DropRoots

theorem drop_holds : Drop := by
  intro n ε L a b hab
  unfold casValK
  have e : L - root a b + rhoC ε = (L + rhoC ε) - root a b := by
    funext c; simp only [Pi.add_apply, Pi.sub_apply]; ring
  rw [e, nsq_sub', nsq_root hab, dot_root _ hab]
  have h1 := abs_rhoC_le ε a
  have h2 := abs_rhoC_le ε b
  simp only [Pi.add_apply]
  rw [abs_le] at h1 h2
  linarith [h1.1, h1.2, h2.1, h2.2]

end PositivityTheory.RgHe3
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.HarishChandraDescent.RealScalarParts.PartsOfSquareIdentity
noncomputable section

open Finset
open scoped InnerProductSpace

namespace PositivityTheory.RgHe3.RealScalarQuadraticForm

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {ε : Fin n → Bool} {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M]
  {E : Fin n → Fin n → Module.End ℂ M}

theorem re_smul_self (κ : ℝ) (y : M) : (⟪(κ : ℂ) • y, y⟫_ℂ).re = κ * ‖y‖ ^ 2 := by
  rw [inner_smul_left, inner_self_eq_norm_sq_to_K]
  simp [← Complex.ofReal_pow]

theorem norm_smul_sq (c : ℝ) (y : M) : ‖(c : ℂ) • y‖ ^ 2 = c ^ 2 * ‖y‖ ^ 2 := by
  rw [norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem pt {ν μ : Fin n → ℝ} {y : M} (hwt : IsWt E ν y) (a b : Fin n) :
    ‖E a b y - (if a = b then (μ a : ℂ) else 0) • y‖ ^ 2 =
      ‖E a b y‖ ^ 2 + if a = b then ((ν a - μ a) ^ 2 - ν a ^ 2) * ‖y‖ ^ 2 else 0 := by
  by_cases h : a = b
  · subst h
    rw [if_pos rfl, if_pos rfl, hwt a, ← sub_smul, ← Complex.ofReal_sub, norm_smul_sq, norm_smul_sq]
    ring
  · rw [if_neg h, if_neg h, zero_smul, sub_zero, add_zero]

theorem qf_eq {ν μ : Fin n → ℝ} {y : M} (hwt : IsWt E ν y) :
    qf E μ y = ∑ a, ∑ b, ‖E a b y‖ ^ 2 + (nsq (ν - μ) - nsq ν) * ‖y‖ ^ 2 := by
  unfold qf
  simp only [pt hwt, sum_add_distrib, sum_ite_eq, mem_univ, if_true]
  congr 1
  simp only [nsq, dot, Pi.sub_apply, ← sum_sub_distrib, sum_mul]
  exact sum_congr rfl fun a _ => by ring

theorem split_sum (f : Fin n → Fin n → ℝ) :
    ∑ a, ∑ b, f a b = ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a), f a b +
      ∑ a, ∑ b ∈ univ.filter (fun b => ε b ≠ ε a), f a b := by
  rw [← sum_add_distrib]
  exact sum_congr rfl fun a _ => (sum_filter_add_sum_filter_not univ (fun b => ε b = ε a) (f a)).symm

theorem diag_le {ν : Fin n → ℝ} {y : M} (hwt : IsWt E ν y) :
    nsq ν * ‖y‖ ^ 2 ≤ ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a), ‖E a b y‖ ^ 2 := by
  have h1 : nsq ν * ‖y‖ ^ 2 = ∑ a, ‖E a a y‖ ^ 2 := by
    simp only [nsq, dot, sum_mul]
    refine sum_congr rfl fun a _ => ?_
    rw [hwt a, norm_smul_sq]; ring
  rw [h1]
  refine sum_le_sum fun a _ => ?_
  exact single_le_sum (f := fun b => ‖E a b y‖ ^ 2) (fun _ _ => by positivity) (mem_filter.2 ⟨mem_univ a, rfl⟩)

end PositivityTheory.RgHe3.RealScalarQuadraticForm

namespace PositivityTheory.RgHe3

open ReciprocityTheory.ChartRestriction.DS

theorem parts_of_square_identity : SqId → Parts := by
  intro hsq n ε M _ _ E hG hU μ ν κ S y hg hq
  obtain ⟨h1, h2, -⟩ := hsq n ε M E hG hU y
  rw [hg.cas, RealScalarQuadraticForm.re_smul_self] at h1 h2
  have hqf := RealScalarQuadraticForm.qf_eq (μ := μ) hg.wt
  rw [RealScalarQuadraticForm.split_sum (ε := ε)] at hqf
  have hd := RealScalarQuadraticForm.diag_le (ε := ε) hg.wt
  have hD : 0 ≤ ∑ a, ∑ b ∈ univ.filter (fun b => ε b ≠ ε a), ‖E a b y‖ ^ 2 :=
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => by positivity
  have hN : 0 ≤ nsq (ν - μ) := by
    unfold nsq dot
    exact Finset.sum_nonneg fun a _ => mul_self_nonneg _
  have hy : 0 < ‖y‖ ^ 2 := by
    have := norm_pos_iff.2 hg.ne
    positivity
  refine ⟨?_, ?_, ?_⟩
  · refine le_of_mul_le_mul_right ?_ hy
    nlinarith
  · refine le_of_mul_le_mul_right ?_ hy
    nlinarith
  · nlinarith
end PositivityTheory.RgHe3
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.HarishChandraDescent.RootDotNonnegativity.AscentOfSquareIdentity
noncomputable section

open Finset
open scoped InnerProductSpace

namespace PositivityTheory.RgHe3

open ReciprocityTheory.ChartRestriction.DS

namespace AscentPotential

variable {n : ℕ} {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M]

theorem nsq_le_of_eig (hS : SqId) {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E)
    (hU : IsInfUnitary ε E) {ω : Fin n → ℝ} {κ : ℝ} {w : M} (hw0 : w ≠ 0) (hwt : IsWt E ω w)
    (hc : casimirK ε E w = (κ : ℂ) • w) : nsq ω ≤ κ := by
  have h := (hS n ε M E hE hU w).1
  rw [hc, inner_smul_left, inner_self_eq_norm_sq_to_K] at h
  simp only [Complex.conj_ofReal] at h
  have h1 : (((κ : ℂ) * ((‖w‖ : ℂ) ^ 2))).re = κ * ‖w‖ ^ 2 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  have h2 : ∑ a, ‖E a a w‖ ^ 2 ≤ ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a), ‖E a b w‖ ^ 2 := by
    refine Finset.sum_le_sum fun a _ => ?_
    exact Finset.single_le_sum (f := fun b => ‖E a b w‖ ^ 2) (fun _ _ => by positivity)
      (Finset.mem_filter.2 ⟨Finset.mem_univ a, rfl⟩)
  have h3 : ∑ a, ‖E a a w‖ ^ 2 = nsq ω * ‖w‖ ^ 2 := by
    unfold nsq dot
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hwt a, norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  have hw : 0 < ‖w‖ ^ 2 := by positivity
  have : nsq ω * ‖w‖ ^ 2 ≤ κ * ‖w‖ ^ 2 := by
    rw [← h3, ← h1]; exact h2.trans (le_of_eq h.symm)
  exact le_of_mul_le_mul_right this hw

def pot (ω : Fin n → ℝ) : ℝ := ∑ c : Fin n, ((c : ℕ) : ℝ) * ω c

theorem pot_root {a b : Fin n} (hab : a ≠ b) (ω : Fin n → ℝ) :
    pot (fun c => ω c + (if c = a then 1 else 0) - (if c = b then 1 else 0)) = pot ω + (a : ℕ) - (b : ℕ) := by
  unfold pot
  simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem pot_lower {ω : Fin n → ℝ} {κ : ℝ} (h : nsq ω ≤ κ) : -((n : ℝ) ^ 2 * (1 + |κ|)) ≤ pot ω := by
  unfold pot
  have hc : ∀ c : Fin n, -(((c : ℕ) : ℝ) * (1 + |κ|)) ≤ ((c : ℕ) : ℝ) * ω c := by
    intro c
    have h1 : ω c ^ 2 ≤ nsq ω := by
      unfold nsq dot
      exact Finset.single_le_sum (f := fun a => ω a * ω a) (fun _ _ => mul_self_nonneg _) (Finset.mem_univ c) |>.trans_eq' (by ring)
    have h2 : |ω c| ≤ 1 + |κ| := by
      have : ω c ^ 2 ≤ |κ| := h1.trans (h.trans (le_abs_self κ))
      nlinarith [abs_nonneg (ω c), sq_abs (ω c)]
    have h3 : (0 : ℝ) ≤ ((c : ℕ) : ℝ) := Nat.cast_nonneg _
    have := neg_abs_le (ω c)
    nlinarith
  have h4 : ∑ c : Fin n, ((c : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 := by
    calc ∑ c : Fin n, ((c : ℕ) : ℝ) ≤ ∑ _c : Fin n, (n : ℝ) :=
          Finset.sum_le_sum fun c _ => by exact_mod_cast c.2.le
      _ = (n : ℝ) ^ 2 := by simp [sq]
  calc -((n : ℝ) ^ 2 * (1 + |κ|)) ≤ -((∑ c : Fin n, ((c : ℕ) : ℝ)) * (1 + |κ|)) := by
        have : 0 ≤ 1 + |κ| := by positivity
        nlinarith
    _ = ∑ c : Fin n, -(((c : ℕ) : ℝ) * (1 + |κ|)) := by rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
    _ ≤ _ := Finset.sum_le_sum fun c _ => hc c

theorem dot_root_nonneg {μ : Fin n → ℝ} (hμ : Antitone μ) {a b : Fin n} (hab : a < b) :
    0 ≤ dot (fun c => (if c = a then (1 : ℝ) else 0) - (if c = b then 1 else 0)) μ := by
  unfold dot
  simp only [sub_mul, ite_mul, one_mul, zero_mul, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  linarith [hμ hab.le]

theorem main (hS : SqId) {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E)
    (hU : IsInfUnitary ε E) (N F : Submodule ℂ M) (hN : Stab E N) (hF : IsKStableSub ε E F) (μ ν : Fin n → ℝ) (κ : ℝ)
    (hμ : Antitone μ) :
    ∀ m : ℕ, ∀ (w : M) (ω : Fin n → ℝ), w ∈ N → w ∈ F → w ≠ 0 → IsWt E ω w → casimirK ε E w = (κ : ℂ) • w →
      0 ≤ dot (ω - ν) μ → pot ω + (n : ℝ) ^ 2 * (1 + |κ|) ≤ m →
      ∃ y' ∈ N, ∃ L : Fin n → ℝ, y' ∈ F ∧ y' ≠ 0 ∧ IsKHWVec ε E L y' ∧ casimirK ε E y' = (κ : ℂ) • y' ∧
        0 ≤ dot (L - ν) μ := by
  intro m
  induction m with
  | zero =>
    intro w ω hwN hwF hw0 hwt hc hd hm
    by_cases hhw : ∀ a b, a < b → ε a = ε b → E a b w = 0
    · exact ⟨w, hwN, ω, hwF, hw0, ⟨hwt, hhw⟩, hc, hd⟩
    · push_neg at hhw
      obtain ⟨a, b, hab, hε, hne⟩ := hhw
      exfalso
      set ω' : Fin n → ℝ := fun c => ω c + (if c = a then 1 else 0) - (if c = b then 1 else 0)
      have hwt' : IsWt E ω' (E a b w) := fun c => kUnit_weight_shift hE hwt hab.ne c
      have hc' : casimirK ε E (E a b w) = (κ : ℂ) • E a b w := by
        have := LinearMap.congr_fun (casimirK_comm ε hE a b hε) w
        simp only [Module.End.mul_apply] at this
        rw [this, hc, map_smul]
      have h1 := pot_lower (nsq_le_of_eig hS hE hU hne hwt' hc')
      have h2 := pot_root hab.ne ω
      have h3 : ((a : ℕ) : ℝ) + 1 ≤ (b : ℕ) := by exact_mod_cast hab
      push_cast at hm
      linarith
  | succ m ih =>
    intro w ω hwN hwF hw0 hwt hc hd hm
    by_cases hhw : ∀ a b, a < b → ε a = ε b → E a b w = 0
    · exact ⟨w, hwN, ω, hwF, hw0, ⟨hwt, hhw⟩, hc, hd⟩
    · push_neg at hhw
      obtain ⟨a, b, hab, hε, hne⟩ := hhw
      set ω' : Fin n → ℝ := fun c => ω c + (if c = a then 1 else 0) - (if c = b then 1 else 0) with hω'
      have hwt' : IsWt E ω' (E a b w) := fun c => kUnit_weight_shift hE hwt hab.ne c
      have hc' : casimirK ε E (E a b w) = (κ : ℂ) • E a b w := by
        have := LinearMap.congr_fun (casimirK_comm ε hE a b hε) w
        simp only [Module.End.mul_apply] at this
        rw [this, hc, map_smul]
      refine ih (E a b w) ω' (hN a b w hwN) (hF a b hε w hwF) hne hwt' hc' ?_ ?_
      · have e : ω' - ν = (ω - ν) + fun c => (if c = a then (1 : ℝ) else 0) - (if c = b then 1 else 0) := by
          funext c; simp only [hω', Pi.sub_apply, Pi.add_apply]; ring
        rw [e]
        have : dot ((ω - ν) + fun c => (if c = a then (1 : ℝ) else 0) - (if c = b then 1 else 0)) μ =
            dot (ω - ν) μ + dot (fun c => (if c = a then (1 : ℝ) else 0) - (if c = b then 1 else 0)) μ := by
          unfold dot; simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
        rw [this]
        linarith [dot_root_nonneg hμ hab]
      · have h2 := pot_root hab.ne ω
        have h3 : ((a : ℕ) : ℝ) + 1 ≤ (b : ℕ) := by exact_mod_cast hab
        push_cast at hm
        show pot ω' + _ ≤ _
        linarith

end AscentPotential

open AscentPotential in
theorem ascent_of_square_identity : SqId → Ascent := by
  intro hS n ε M _ _ E hE hU N hN μ ν κ S y hyN hy hμ hS1 hS2
  obtain ⟨F, hFd, hFk, hyF⟩ := hy.fin
  obtain ⟨y', hy'N, L, hy'F, hy'0, hhw, hc, hd⟩ :=
    main hS hE hU N F hN hFk μ ν κ hμ ⌈pot ν + (n : ℝ) ^ 2 * (1 + |κ|)⌉₊ y ν hyN hyF hy.ne hy.wt hy.cas
      (by simp [dot]) (Nat.le_ceil _)
  refine ⟨y', hy'N, L, hy'0, ⟨F, hFd, hFk, hy'F⟩, hhw, ?_, ?_⟩
  · have h1 := casimirK_khwVec ε hE hhw
    rw [hc] at h1
    have h2 : ((κ : ℂ) - ((nsq (L + rhoC ε) - nsq (rhoC ε) : ℝ) : ℂ)) • y' = 0 := by
      rw [sub_smul, h1, sub_self]
    rcases smul_eq_zero.1 h2 with h | h
    · have := sub_eq_zero.1 h
      unfold casValK
      exact_mod_cast this.symm
    · exact absurd h hy'0
  · have hL := nsq_le_of_eig hS hE hU hy'0 hhw.1 hc
    have e : nsq (L - μ) = nsq (ν - μ) + nsq L - nsq ν - 2 * dot (L - ν) μ := by
      unfold nsq dot
      simp only [Pi.sub_apply, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      ring
    rw [e]
    linarith

end PositivityTheory.RgHe3
end
end

namespace PositivityTheory.RgHe3

theorem far_closed : Far := by
  have hs : SqId := square_identity_holds
  have hadeq : AdEq := adjoint_equation_holds
  have htrial : Trial :=
    trial_of_inputs discrete_series_data_holds (second_moment_of_bounds (root_bound_of_square_identity hs) matrix_bound_holds hadeq) (approximation_of_square_identity hs)
      restriction_holds
  have hcore : Core :=
    discrete_series_bound_of_inputs (comp_proof hs) (parts_of_square_identity hs)
      (casimir_bound_of_inputs hs markov_inequality_holds positive_negative_holds inverse_holds commutant_holds hadeq casimir_adjoint_holds)
      (ascent_of_square_identity hs) (mem_span_of_frobenius_mem_span hs k_irreducible_existence_holds drop_holds) integral_weight_holds harish_chandra_parameter_holds
      identity_holds
  exact far_of_trial_bound htrial hcore

theorem base : PositivityTheory.RgHe.Models → PositivityTheory.RgHe.Frame → PositivityTheory.RgHe.Base := base_of_far_models_frame far_closed

end PositivityTheory.RgHe3
