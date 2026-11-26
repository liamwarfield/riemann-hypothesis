module

public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.CurveCountObjects
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSpanStepHomog
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwoBlockCycleExpand
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenDegAmple
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSerreGraded
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSmallSectionsNonzero
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSpanningExtension
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EvalSmulOfIsHomogeneousAlt

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PGoodChartZeroSet
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Finset
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomogIdeal mcPts segre scaleBlock scaleBlock_mem_zeroLocus)
open ComplexSets

namespace GoodChartZeroSet

section Lemmas

theorem eval_smul_of_isHomogeneous {τ : Type*} {φ : MvPolynomial τ ℂ} {n : ℕ} (hφ : φ.IsHomogeneous n)
    (c : ℂ) (w : τ → ℂ) : eval (c • w) φ = c ^ n * eval w φ :=
  _root_.UpperTheory.Reformulated.B.Ydc1.eval_smul_of_isHomogeneous hφ c w

theorem eval_homogenize {m : ℕ} (f : MvPolynomial (Fin m) ℂ) {D : ℕ} (hD : f.totalDegree ≤ D) (a : Fin m)
    (w : Fin m → ℂ) (hw : w a ≠ 0) :
    eval w (X a * ∑ d ∈ range (D + 1), X a ^ (D - d) * homogeneousComponent d f) =
      w a ^ (D + 1) * eval ((w a)⁻¹ • w) f := by
  have hf : f = ∑ d ∈ range (D + 1), homogeneousComponent d f := by
    conv_lhs => rw [← sum_homogeneousComponent f]
    refine Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun d _ hd' => ?_
    exact homogeneousComponent_eq_zero (n := d) (φ := f) (by simp at hd'; omega)
  conv_rhs => rw [hf]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_mul, map_sum, map_sum, eval_X, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdD : d ≤ D := by simp at hd; omega
  rw [eval_smul_of_isHomogeneous (homogeneousComponent_isHomogeneous d f), map_mul, map_pow, eval_X]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hdD
  rw [Nat.add_sub_cancel_left]
  have hinv : w a ^ d * (w a)⁻¹ ^ d = 1 := by rw [← mul_pow, mul_inv_cancel₀ hw, one_pow]
  linear_combination (-(w a * w a ^ k * eval w (homogeneousComponent d f))) * hinv

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


omit [∀ k, Fintype (ι k)] in
theorem segre_scaleBlock [DecidableEq K] (k0 : K) (c : ℂ) (z : (Σ k, ι k) → ℂ) :
    segre (scaleBlock k0 c z) = c • segre z := by
  funext j
  show ∏ k, (if k = k0 then c else 1) * z ⟨k, j k⟩ = c * ∏ k, z ⟨k, j k⟩
  rw [Finset.prod_mul_distrib]
  simp


open Classical in
def linForm {m e : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) : MvPolynomial (Fin m) ℂ :=
  ∑ a, C (Ψ (fun i' => if σ a = i' then (1 : ℂ) else 0) 0) * X a

theorem eval_linForm {m e : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (x : Fin m → ℂ) :
    eval x (linForm σ Ψ) = Ψ (fun i' => x (σ.symm i')) 0 := by
  classical
  rw [linForm]
  have hv : (fun i' => x (σ.symm i')) = ∑ a, x a • fun i' => if σ a = i' then (1 : ℂ) else 0 := by
    rw [pi_eq_sum_univ (fun i' => x (σ.symm i'))]
    exact (Equiv.sum_comp σ _).symm.trans (by simp)
  rw [hv]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul, map_mul, eval_C, eval_X]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [mul_comm]

theorem exists_segre_smul (P : Ideal (MRing ι)) (hP : IsMultiHomogIdeal P) {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts P) {c : ℂ} (hc : c ≠ 0) (hK : IsEmpty K → c = 1) :
    ∃ z' ∈ mcPts P, segre z' = c • segre z := by
  classical
  by_cases h : IsEmpty K
  · exact ⟨z, hz, by rw [hK h, one_smul]⟩
  · obtain ⟨k0⟩ := not_isEmpty_iff.1 h
    exact ⟨scaleBlock k0 c z, scaleBlock_mem_zeroLocus P hP k0 hc hz, segre_scaleBlock k0 c z⟩


omit [∀ k, Fintype (ι k)] in
theorem segre_of_isEmpty (hK : IsEmpty K) (z : (Σ k, ι k) → ℂ) (j : (k : K) → ι k) : segre z j = 1 := by
  simp [segre]

end Lemmas

theorem proof : Statement := by
  intro K _ ι _ P e m σ Ψ hP
  classical
  apply Set.Subset.antisymm
  swap
  · intro x hx q hq
    rw [projChartIdeal, mem_vanishingIdeal_iff] at hq
    exact hq x hx
  intro x hx
  have hv : ∀ q : MvPolynomial (Fin m) ℂ, (∀ y ∈ projChartSet P σ Ψ, eval y q = 0) → eval x q = 0 :=
    fun q hq => hx q (by rw [projChartIdeal, mem_vanishingIdeal_iff]; exact hq)
  have hseg : ∀ z : (Σ k, ι k) → ℂ, (fun i' => segre z (σ (σ.symm i'))) = segre z := fun z => by
    funext i'; rw [Equiv.apply_symm_apply]

  have hx1 : Ψ (fun i' => x (σ.symm i')) 0 = 1 := by
    have h := hv (linForm σ Ψ - 1) (by
      rintro _ ⟨z, -, hz1, rfl⟩
      rw [map_sub, eval_linForm, map_one, hseg, hz1, sub_self])
    rw [map_sub, eval_linForm, map_one] at h
    exact sub_eq_zero.1 h
  obtain ⟨a, ha⟩ : ∃ a, x a ≠ 0 := by
    by_contra h
    simp only [not_exists, ne_eq, not_not] at h
    have h0 : (fun i' => x (σ.symm i')) = 0 := funext fun i' => h _
    rw [h0, map_zero] at hx1
    exact zero_ne_one hx1

  have ha1 : IsEmpty K → x a = 1 := fun hK => by
    have h := hv (X a - 1) (by
      rintro _ ⟨z, -, -, rfl⟩
      simp [segre_of_isEmpty hK])
    simpa [sub_eq_zero] using h

  have hzero : (x a)⁻¹ • x ∈ zeroSet (segreChartIdeal P σ (σ a)) := by
    intro f hf
    rw [segreChartIdeal, mem_vanishingIdeal_iff] at hf
    have hg := hv (X a * ∑ d ∈ range (f.totalDegree + 1),
        X a ^ (f.totalDegree - d) * homogeneousComponent d f) (by
      rintro _ ⟨z, hz, -, rfl⟩
      by_cases h0 : segre z (σ a) = 0
      · simp [h0]
      · rw [eval_homogenize f le_rfl a _ h0]
        obtain ⟨z', hz', hz'e⟩ := exists_segre_smul P hP hz (inv_ne_zero h0)
          (fun hK => by rw [segre_of_isEmpty hK, inv_one])
        refine mul_eq_zero_of_right _ (hf _ ⟨z', hz', ?_, ?_⟩)
        · rw [hz'e, Pi.smul_apply, smul_eq_mul, inv_mul_cancel₀ h0]
        · funext b
          rw [hz'e]
          rfl)
    rw [eval_homogenize f le_rfl a x ha] at hg
    exact (mul_eq_zero.1 hg).resolve_left (pow_ne_zero _ ha)
  rw [SegreChartZeroSet.proof K ι P m σ (σ a) hP] at hzero
  obtain ⟨z', hz', -, hz'e⟩ := hzero
  obtain ⟨z, hz, hze⟩ := exists_segre_smul P hP hz' ha ha1
  have hxz : x = fun b => segre z (σ b) := by
    funext b
    have hb := congrFun hz'e b
    simp only [Pi.smul_apply, smul_eq_mul] at hb
    rw [hze, Pi.smul_apply, smul_eq_mul, ← hb, ← mul_assoc, mul_inv_cancel₀ ha, one_mul]
  refine ⟨z, hz, ?_, hxz⟩
  rw [← hseg z, ← hx1, hxz]

end GoodChartZeroSet

end GroundTheory.Heights₂.Heights
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveBoxCount
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.Inter

def CurveBoxCount.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (c : ∀ k, ι k) (R : Finset ((Σ k, ι k) → ℂ)),
    IsArithVar (mCoordIdeal y) 1 → Birational y → IsConjInvariantH A → (∀ k, y ⟨k, c k⟩ ≠ 0) →
    (∀ t ∈ R, t ∈ mcPts (mCoordIdeal y)) → (∀ z ∈ mcPts (mCoordIdeal y), ∃! t, t ∈ R ∧ SameOrbit z t) →
    ∃ C : ℝ, ∀ τ : ℕ, 1 ≤ τ →
      (τ : ℝ) * ∑ t ∈ R, Real.log (chartRadius A c t) + chartIndexLog y c A.a τ - C ≤
        smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) τ

namespace CurveBoxCount

end CurveBoxCount

end GroundTheory.Heights₂.Heights.Targets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PGoodChartModel
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar IsGoodProj mcPts segre segre_rel)
open ComplexSets MvPolynomial Matrix

namespace GoodChartModel

theorem homogeneousComponent_mem_leadIdeal {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {f : MvPolynomial (Fin n) ℂ} (hf : f ∈ J) {r : ℕ} (hr : f.totalDegree ≤ r) :
    homogeneousComponent r f ∈ leadIdeal J := by
  rcases hr.eq_or_lt with h | h
  · rw [← h]
    exact Ideal.subset_span ⟨f, hf, rfl⟩
  · rw [homogeneousComponent_eq_zero (n := r) (φ := f) h]
    exact zero_mem _

theorem eval_linPoly {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℂ) (r : Fin d) (x : Fin n → ℂ) :
    eval x (linPoly A r) = (A *ᵥ x) r := by
  simp [linPoly, Matrix.mulVec, dotProduct]

theorem pow_mem {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} {e m : ℕ} {σ : Fin m ≃ ((k : K) → ι k)}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ)
    {J : Ideal (MvPolynomial (Fin m) ℂ)} (hJ : projChartIdeal P σ Ψ ≤ J) (a : Fin m) :
    ∃ r : ℕ, (X a ^ r : MvPolynomial (Fin m) ℂ) ∈ leadIdeal J ⊔ linIdeal (chartProjMatrix σ Ψ) := by
  classical
  obtain ⟨r, hr, G, hG, hrel⟩ := segre_rel hP.2.1.2.1 Ψ hΨ (σ a)
  set A := chartProjMatrix σ Ψ with hA
  let Gx : Fin (e + 1) → MvPolynomial (Fin m) ℂ := fun j => rename σ.symm (G j)
  have hGx : ∀ j, (Gx j).totalDegree ≤ r - 1 := fun j => (totalDegree_rename_le _ _).trans (hG j)
  let f : MvPolynomial (Fin m) ℂ := X a ^ r - (Gx 0 + ∑ j : Fin e, Gx j.succ * linPoly A j)
  have hfJ : f ∈ J := by
    refine hJ ?_
    rw [projChartIdeal, MvPolynomial.mem_vanishingIdeal_iff]
    rintro _ ⟨z, hz, hz1, rfl⟩
    have hw : ((fun a => segre z (σ a)) ∘ σ.symm) = segre z := by
      funext i'
      simp
    have h := hrel z hz
    rw [Fin.sum_univ_succ, hz1, one_mul] at h
    change eval (fun a => segre z (σ a)) f = 0
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [f, Gx, map_sub, map_add (f := _), map_pow, map_sum, map_mul, eval_X, eval_rename, hw,
      eval_linPoly, hA, chartProjMatrix_mulVec]
    rw [h]
    simp [Equiv.apply_symm_apply, mul_comm]
  have hdeg : f.totalDegree ≤ r := by
    refine (totalDegree_sub _ _).trans (max_le (by rw [totalDegree_X_pow]) ?_)
    refine (totalDegree_add _ _).trans (max_le ((hGx 0).trans (Nat.sub_le _ _)) ?_)
    refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => ?_)
    refine (totalDegree_mul _ _).trans ?_
    have h1 := hGx j.succ
    have h2 := (isHomogeneous_linPoly A j).totalDegree_le
    omega
  have h1 : 1 ≤ r := hr
  have hX : homogeneousComponent r (X a ^ r : MvPolynomial (Fin m) ℂ) = X a ^ r := by
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule r _).2 (isHomogeneous_X_pow a r)),
      if_pos rfl]
  have h0 : homogeneousComponent r (Gx 0) = 0 :=
    homogeneousComponent_eq_zero (n := r) (φ := Gx 0) (by have := hGx 0; omega)
  have hcomp : homogeneousComponent r f =
      X a ^ r - ∑ j : Fin e, homogeneousComponent (r - 1) (Gx j.succ) * linPoly A j := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [f, map_sub, map_add (f := _), map_sum, hX, h0, zero_add,
      homogeneousComponent_mul_of_isHomogeneous_right _ _ (isHomogeneous_linPoly A _), h1, if_true]
  have hmem : homogeneousComponent r f + ∑ j : Fin e, homogeneousComponent (r - 1) (Gx j.succ) * linPoly A j ∈
      leadIdeal J ⊔ linIdeal A :=
    add_mem (Ideal.mem_sup_left (homogeneousComponent_mem_leadIdeal hfJ hdeg))
      (Ideal.mem_sup_right (Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)))
  rw [hcomp, sub_add_cancel] at hmem
  exact ⟨r, hmem⟩

end GoodChartModel

theorem GoodChartModel.proof (hZ : GoodChartZeroSet.Statement) (hD : GoodChartDim.Statement) :
    GoodChartModel.Statement := by
  intro K _ ι _ P e m σ Ψ hP hΨ
  refine ⟨hZ K ι P e m σ Ψ hP.2.1.2.1, fun J hJ => ?_⟩
  have hdim := hD K ι P e m σ Ψ hP J hJ
  have hfin : (projHom J (chartProjMatrix σ Ψ)).toRingHom.Finite := by
    have hrad : originIdeal m ≤ (leadIdeal J ⊔ linIdeal (chartProjMatrix σ Ψ)).radical := by
      refine Ideal.span_le.2 (Set.range_subset_iff.2 fun a => ?_)
      obtain ⟨r, hr⟩ := GoodChartModel.pow_mem hP hΨ hJ.1.2 a
      exact ⟨r, hr⟩
    obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg_radical hrad (IsNoetherian.noetherian _)
    exact ConeAvoidsFinite.proof m e N J _ hN
  exact ⟨hdim, ⟨FiniteProjHomInjective.proof m e J _ hJ.1.1 hdim hfin, hfin⟩⟩

end GroundTheory.Heights₂.Heights
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.MoriwakiHSFull
section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSublatticeDegree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open Module

theorem SublatticeDegree.proof (hExt : SublatticeExtension.Statement) (hSpan : SpanningExtension.Statement)
    (hCov : CovolumeLeGram.Statement) (hGram : GramContraction.Statement) : SublatticeDegree.Statement := by
  intro E E' _ _ R R' φ φ' _ _ _ _ ψ S C hφ hφ' hψ hnorm hS hSC hC
  obtain ⟨Ψ, hΨφ, hΨn, hΨi⟩ := hExt E E' R R' φ φ' ψ hφ hφ' hψ hnorm
  set Λ := imageLattice φ with hΛdef
  set Λ' := imageLattice φ' with hΛ'def
  have hC0 : 0 < C := by linarith

  have hrk : finrank ℤ Λ' = R' := by rw [ZLattice.rank ℝ Λ', finrank_euclideanSpace_fin]
  let b' : Basis (Fin R') ℤ Λ' := Module.finBasisOfFinrankEq ℤ Λ' hrk
  let u : Fin R' → EuclideanSpace ℝ (Fin R') := fun i => (b' i : EuclideanSpace ℝ (Fin R'))
  have hcov' : ZLattice.covolume Λ' = Real.sqrt (Matrix.gram ℝ u).det :=
    GroundTheory.Heights₂.Heights.covolume_eq_sqrt_det_gram Λ' b'
  have hu : LinearIndependent ℝ u := by
    have he : ⇑(b'.ofZLatticeBasis ℝ Λ') = u := funext fun i => b'.ofZLatticeBasis_apply ℝ Λ' i
    rw [← he]
    exact Basis.linearIndependent _
  have hv : LinearIndependent ℝ (Ψ ∘ u) := hu.map' Ψ (LinearMap.ker_eq_bot.2 hΨi)
  have hRR : R' ≤ R := by simpa using hv.fintype_card_le_finrank

  have hspan : Submodule.span ℝ (φ '' S) = ⊤ := by
    have h1 : (Λ : Set (EuclideanSpace ℝ (Fin R))) ⊆ Submodule.span ℝ (φ '' S) := by
      intro x hx
      obtain ⟨e, rfl⟩ := AddMonoidHom.mem_range.1 hx
      clear hx
      have he : e ∈ AddSubgroup.closure S := hS ▸ AddSubgroup.mem_top e
      induction he using AddSubgroup.closure_induction with
      | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
      | zero => simp
      | add x y _ _ hx hy => simpa using add_mem hx hy
      | neg x _ hx => simpa using neg_mem hx
    rw [eq_top_iff, ← (IsZLattice.span_top : Submodule.span ℝ (Λ : Set (EuclideanSpace ℝ (Fin R))) = ⊤)]
    exact Submodule.span_le.2 h1

  obtain ⟨w, hwS, hind⟩ := hSpan (EuclideanSpace ℝ (Fin R)) (Fin R') (Ψ ∘ u) (φ '' S) hv hspan
  have hcard : Fintype.card (Fin R' ⊕ Fin (finrank ℝ (EuclideanSpace ℝ (Fin R)) - Fintype.card (Fin R'))) = R := by
    simp only [Fintype.card_sum, Fintype.card_fin, finrank_euclideanSpace_fin]
    omega
  have hmem : ∀ i, Sum.elim (Ψ ∘ u) w i ∈ Λ := by
    rintro (i | j)
    · obtain ⟨e, he⟩ := AddMonoidHom.mem_range.1 (b' i).2
      refine AddMonoidHom.mem_range.2 ⟨ψ e, ?_⟩
      simp only [Sum.elim_inl, Function.comp_apply, u, ← he, hΨφ]
    · obtain ⟨s, _, hsw⟩ := hwS j
      simp only [Sum.elim_inr]
      rw [← hsw]
      exact AddMonoidHom.mem_range.2 ⟨s, rfl⟩
  have h1 := hCov R Λ _ (Sum.elim (Ψ ∘ u) w) hmem hind hcard
  have h2 := hGram (Fin R') _ (EuclideanSpace ℝ (Fin R)) Ψ u w hΨn

  have hw : ∀ j, ‖w j‖ ≤ C := fun j => by
    obtain ⟨s, hs, hsw⟩ := hwS j
    rw [← hsw]
    exact hSC s hs
  have hk : Fintype.card (Fin (finrank ℝ (EuclideanSpace ℝ (Fin R)) - Fintype.card (Fin R'))) ≤ R := by
    simp only [Fintype.card_fin, finrank_euclideanSpace_fin]
    omega
  have hprod : ∏ j, ‖w j‖ ^ 2 ≤ (C ^ R) ^ 2 := by
    calc ∏ j, ‖w j‖ ^ 2 ≤ ∏ _j, C ^ 2 :=
          Finset.prod_le_prod₀ (fun _ _ => by positivity) (fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hw j) 2)
      _ = (C ^ 2) ^ Fintype.card (Fin (finrank ℝ (EuclideanSpace ℝ (Fin R)) - Fintype.card (Fin R'))) := by
          rw [Finset.prod_const, Finset.card_univ]
      _ ≤ (C ^ 2) ^ R := pow_le_pow_right₀ (by nlinarith) hk
      _ = (C ^ R) ^ 2 := by ring
  have hpos' : 0 < ZLattice.covolume Λ' := ZLattice.covolume_pos Λ'
  have hpos : 0 < ZLattice.covolume Λ := ZLattice.covolume_pos Λ
  have hdu : 0 ≤ (Matrix.gram ℝ u).det := by
    rw [hcov'] at hpos'
    exact (Real.sqrt_pos.1 hpos').le
  have hmain : ZLattice.covolume Λ ≤ ZLattice.covolume Λ' * C ^ R := by
    calc ZLattice.covolume Λ ≤ Real.sqrt (Matrix.gram ℝ (Sum.elim (Ψ ∘ u) w)).det := h1
      _ ≤ Real.sqrt ((Matrix.gram ℝ u).det * (C ^ R) ^ 2) :=
          Real.sqrt_le_sqrt (h2.trans (mul_le_mul_of_nonneg_left hprod hdu))
      _ = ZLattice.covolume Λ' * C ^ R := by
          rw [Real.sqrt_mul hdu, Real.sqrt_sq (pow_pos hC0 R).le, hcov']
  have hlog := Real.log_le_log hpos hmain
  rw [Real.log_mul hpos'.ne' (pow_pos hC0 R).ne', Real.log_pow] at hlog
  linarith

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ExistsCoordNeZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

set_option linter.unusedSectionVars false

section G1SpanProof

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem chartLat_mul {y : (Σ k, ι k) → Ω} {a : K → ℤ} {n m : ℕ} {s t : Ω} (hs : s ∈ chartLat y a n)
    (ht : t ∈ chartLat y a m) : s * t ∈ chartLat y a (n + m) := by
  intro c hc
  have key : s * t * ∏ k, y ⟨k, c k⟩ ^ (-(((n + m : ℕ) : ℤ) * a k)) =
      (s * ∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k))) * (t * ∏ k, y ⟨k, c k⟩ ^ (-((m : ℤ) * a k))) := by
    have hp : ∏ k, y ⟨k, c k⟩ ^ (-(((n + m : ℕ) : ℤ) * a k)) =
        (∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k))) * ∏ k, y ⟨k, c k⟩ ^ (-((m : ℤ) * a k)) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← zpow_add₀ (hc k)]
      congr 1
      push_cast
      ring
    rw [hp]
    ring
  rw [key]
  exact mul_mem (hs c hc) (ht c hc)

theorem isBoundedH_mono {P : Ideal (MRing ι)} {y : (Σ k, ι k) → Ω} {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} {τ : ℕ} {C C' : ℝ} {s : Ω}
    (h : IsBoundedH P y A τ C s) (hC : C ≤ C') : IsBoundedH P y A τ C' s := by
  intro dg dh g h' z hg hh hdeg he hz
  refine (h dg dh g h' z hg hh hdeg he hz).trans ?_
  rw [mul_assoc, mul_assoc]
  exact mul_le_mul_of_nonneg_right hC (mul_nonneg (norm_nonneg _) (pow_nonneg (le_of_lt (A.pos z hz.1)) _))

theorem mul_monomial_bounded (hMul : SectionBoundedMul.Statement) {y : (Σ k, ι k) → Ω} {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} {q : ℕ}
    {w : Fin q → Ω} (hw : ∀ j, w j ∈ chartLat y A.a 1)
    (hsmall : ∀ j, IsSmallH (mCoordIdeal y) y A 1 (w j)) {x : Ω} {n : ℕ} {C : ℝ}
    (hx : x ∈ chartLat y A.a n) (hb : IsBoundedH (mCoordIdeal y) y A n C x) (μ : Fin q → ℕ) :
    x * ∏ j, w j ^ μ j ∈ chartLat y A.a (n + ∑ j, μ j) ∧
      IsBoundedH (mCoordIdeal y) y A (n + ∑ j, μ j) C (x * ∏ j, w j ^ μ j) := by
  have step : ∀ {x' : Ω} {n' : ℕ} (j : Fin q), x' ∈ chartLat y A.a n' →
      IsBoundedH (mCoordIdeal y) y A n' C x' →
      x' * w j ∈ chartLat y A.a (n' + 1) ∧ IsBoundedH (mCoordIdeal y) y A (n' + 1) C (x' * w j) := by
    intro x' n' j hx' hb'
    refine ⟨chartLat_mul hx' (hw j), ?_⟩
    have := hMul K ι Ω y A n' 1 C 1 x' (w j) hx' (hw j) hb' (isBoundedH_one_of_isSmallH (hsmall j))
    rwa [mul_one] at this
  have hpow : ∀ (j : Fin q) (k : ℕ) {x' : Ω} {n' : ℕ}, x' ∈ chartLat y A.a n' →
      IsBoundedH (mCoordIdeal y) y A n' C x' →
      x' * w j ^ k ∈ chartLat y A.a (n' + k) ∧ IsBoundedH (mCoordIdeal y) y A (n' + k) C (x' * w j ^ k) := by
    intro j k
    induction k with
    | zero => intro x' n' hx' hb'; simpa using ⟨hx', hb'⟩
    | succ k ih =>
      intro x' n' hx' hb'
      obtain ⟨h1, h2⟩ := ih hx' hb'
      have := step j h1 h2
      rw [pow_succ, ← mul_assoc, ← add_assoc]
      exact this
  have hS : ∀ S : Finset (Fin q), x * ∏ j ∈ S, w j ^ μ j ∈ chartLat y A.a (n + ∑ j ∈ S, μ j) ∧
      IsBoundedH (mCoordIdeal y) y A (n + ∑ j ∈ S, μ j) C (x * ∏ j ∈ S, w j ^ μ j) := by
    intro S
    classical
    induction S using Finset.induction_on with
    | empty => simpa using ⟨hx, hb⟩
    | insert a S ha ih =>
      obtain ⟨h1, h2⟩ := hpow a (μ a) ih.1 ih.2
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      have e1 : x * (w a ^ μ a * ∏ j ∈ S, w j ^ μ j) = (x * ∏ j ∈ S, w j ^ μ j) * w a ^ μ a := by ring
      have e2 : n + (μ a + ∑ j ∈ S, μ j) = n + ∑ j ∈ S, μ j + μ a := by ring
      rw [e1, e2]
      exact ⟨h1, h2⟩
  exact hS Finset.univ

theorem exists_coord_ne_zero {y : (Σ k, ι k) → Ω} {d : ℕ} (hV : IsArithVar (mCoordIdeal y) d) (k : K) :
    ∃ i, y ⟨k, i⟩ ≠ 0 := by
  obtain ⟨i, hi⟩ := hV.2.1.2.2 k
  refine ⟨i, fun h0 => hi ?_⟩
  show (X ⟨k, i⟩ : MRing ι) ∈ RingHom.ker (mConeMap y)
  rw [RingHom.mem_ker]
  simp [mConeMap, h0]

end G1SpanProof

theorem SuccessiveMinimaSpan.proof (hFin : SectionRingFinite.Statement) (hBd : SectionBounded.Statement)
    (hMul : SectionBoundedMul.Statement) : SuccessiveMinimaSpan.Statement := by
  intro K _ ι _ Ω _ _ y D A P0 _ hV _ hA
  obtain ⟨q, w, hw, hgen, hsmall⟩ := hA.gen
  obtain ⟨r, d, e, he, hspan⟩ :=
    hFin K ι Ω y A.a q w (exists_coord_ne_zero hV) hw hgen
  have hCe : ∀ i, ∃ C : ℝ, IsBoundedH (mCoordIdeal y) y A (d i) C (e i) := fun i =>
    hBd K ι Ω y A q w hw hgen hsmall (d i) (e i) (he i)
  choose Ce hCe using hCe
  refine ⟨∑ i, |Ce i|, fun n => le_antisymm ?_ ?_⟩
  · rw [AddSubgroup.closure_le]
    exact fun s hs => hs.1
  · refine (hspan n).trans (AddSubgroup.closure_mono ?_)
    rintro s ⟨i, μ, hn, rfl⟩
    obtain ⟨h1, h2⟩ := mul_monomial_bounded hMul hw hsmall (he i) (hCe i) μ
    rw [hn] at h1 h2
    refine ⟨h1, isBoundedH_mono h2 ?_⟩
    exact (le_abs_self _).trans
      (Finset.single_le_sum (f := fun i => |Ce i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel

theorem SublatticeDegree.full : SublatticeDegree.Statement :=
  SublatticeDegree.proof SublatticeExtension.proof SpanningExtension.proof CovolumeLeGram.proof
    GramContraction.proof

theorem SuccessiveMinimaSpan.of_leaves (hC : KH.CondStatement) (hR : RelSectionsLarge.Statement) : SuccessiveMinimaSpan.Statement :=
  SuccessiveMinimaSpan.proof
    (SectionRingFinite.proof (SectionLatticeFinite.proof hC)
      (SectionSpanStep.proof (SpanStepHomog.proof (SpanStepLocal.proof (RelLatticeFinite.proof hR)))
        SerreGraded.proof))
    SectionBounded.proof SectionBoundedMul.proof

end GroundTheory.Heights₂.Heights.Targets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveClosedPointChart
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def CurveClosedPointChart.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω), IsArithVar (mCoordIdeal y) 1 →
      ∀ m : Ideal (curveRing y), m.IsMaximal → ∃ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) ∧
        ∀ p : Σ k, ι k, ∃ a b : curveRing y, b ∉ m ∧ (b : Ω) * (y p / y ⟨p.1, c p.1⟩) = a

end GroundTheory.Heights₂.Heights.Targets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveRingFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def CurveRingFinite.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω), IsArithVar (mCoordIdeal y) 1 → Module.Finite ℤ (curveRing y)

end GroundTheory.Heights₂.Heights.Targets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PGenFibreChartDeg
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem GenFibreChartDeg.isMultiHomogIdeal_ker_rat {K' : Type} {ι' : K' → Type} [∀ k, Fintype (ι' k)]
    {Ω : Type} [Field Ω] [CharZero Ω] (x' : (Σ k', ι' k') → Ω)
    (h : IsMultiHomogIdeal (RingHom.ker (aeval x' : MRing ι' →ₐ[ℤ] Ω))) :
    IsMultiHomogIdeal (RingHom.ker (aeval x' : MRingOver ℚ ι' →ₐ[ℚ] Ω)) := by
  have hmap : ∀ g : MRing ι', aeval x' (qmap g) = aeval x' g := fun g => by
    rw [qmap, ← algebraMap_int_eq, MvPolynomial.aeval_map_algebraMap]
  have hker : RingHom.ker (aeval x' : MRingOver ℚ ι' →ₐ[ℚ] Ω) =
      (RingHom.ker (aeval x' : MRing ι' →ₐ[ℤ] Ω)).map qmap := by
    apply le_antisymm
    · intro f hf
      obtain ⟨N, hN, g, hg⟩ := exists_int_mul_eq_qmap f
      have hg0 : g ∈ RingHom.ker (aeval x' : MRing ι' →ₐ[ℤ] Ω) := by
        rw [RingHom.mem_ker, ← hmap, ← hg, map_mul, RingHom.mem_ker.mp hf, mul_zero]
      have hmem : (N : MRingOver ℚ ι') * f ∈ (RingHom.ker (aeval x' : MRing ι' →ₐ[ℤ] Ω)).map qmap := by
        rw [hg]
        exact Ideal.mem_map_of_mem _ hg0
      have hu : IsUnit (N : MRingOver ℚ ι') := by
        rw [show (N : MRingOver ℚ ι') = C (N : ℚ) by simp]
        exact (isUnit_iff_ne_zero.mpr (by exact_mod_cast hN)).map C
      have h2 := Ideal.mul_mem_left _ (↑hu.unit⁻¹ : MRingOver ℚ ι') hmem
      rwa [← mul_assoc, hu.val_inv_mul, one_mul] at h2
    · rw [Ideal.map_le_iff_le_comap]
      intro g hg
      rw [Ideal.mem_comap, RingHom.mem_ker, hmap]
      exact RingHom.mem_ker.mp hg
  rw [hker]
  obtain ⟨T, hT, hTe⟩ := h
  refine ⟨qmap '' T, ?_, by rw [hTe, Ideal.map_span]⟩
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨a, ha⟩ := hT f hf
  exact ⟨a, fun m hm k => ha m (MvPolynomial.support_map_subset _ f hm) k⟩

theorem GenFibreChartDeg.proof (hT : GroundTheory.Heights₂.Heights.Inter.ChartScalingIndep.Statement)
    (hC : GroundTheory.Heights₂.Heights.Inter.AdjoinIndepRelfinrank.Statement) : GenFibreChartDeg.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' G _ c i hv hP hc hi
  have : CharZero G.Φ := (algebraMap G.Φ G.Φ').charZero
  have hx'0 : ∀ k, G.x' (v ⟨k, c k⟩) ≠ 0 := fun k => by
    rw [G.compat]
    exact (map_ne_zero _).2 (hc k)

  have hex : ∀ k', ∃ j : ι' k', G.x' ⟨k', j⟩ ≠ 0 := by
    intro k'
    by_cases hk : k' ∈ Set.range κ
    · obtain ⟨k, rfl⟩ := hk
      have key : ∀ q : Σ k', ι' k', q.1 = κ k → G.x' q ≠ 0 → ∃ j : ι' (κ k), G.x' ⟨κ k, j⟩ ≠ 0 := by
        rintro ⟨a, j⟩ rfl h
        exact ⟨j, h⟩
      exact key _ (hv.2.2.1 _) (hx'0 k)
    · exact ⟨i ⟨k', hk⟩, hi ⟨k', hk⟩⟩
  choose i' hi' using hex

  let t : K → G.Φ' := fun k => G.x' ⟨κ k, i' (κ k)⟩
  let Φ₁ := (IsScalarTower.toAlgHom ℚ G.Φ G.Φ').fieldRange
  let F₁ := blockFnField G.x'
  let F₀ := blockFnField (G.x' ∘ v)
  let E := IntermediateField.adjoin ℚ (Set.range t)
  let S := Set.range fun q : Σ k : FibreBlock κ, fibreIdx ι' κ k => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, i q.1⟩
  have hF : ∀ p q : Σ k', ι' k', p.1 = q.1 → G.x' p / G.x' q ∈ F₁ :=
    fun p q h => IntermediateField.subset_adjoin _ _ ⟨p, q, h, rfl⟩
  have hF0 : ∀ p q : Σ k, ι k, p.1 = q.1 → G.x' (v p) / G.x' (v q) ∈ F₀ :=
    fun p q h => IntermediateField.subset_adjoin _ _ ⟨p, q, h, rfl⟩
  have hF01 : F₀ ≤ F₁ := IntermediateField.adjoin_le_iff.2 (by
    rintro _ ⟨p, q, h, rfl⟩
    exact hF (v p) (v q) (by rw [hv.2.2.1, hv.2.2.1, h]))
  have hmem : ∀ c, algebraMap G.Φ G.Φ' c ∈ Φ₁ := fun c => AlgHom.mem_fieldRange.2 ⟨c, rfl⟩

  have hchart : ∀ k, ∃ p₀ : Σ k, ι k, p₀.1 = k ∧ v p₀ = ⟨κ k, i' (κ k)⟩ := fun k => by
    obtain ⟨p₀, h⟩ := hv.2.2.2 ⟨κ k, i' (κ k)⟩ ⟨k, rfl⟩
    exact ⟨p₀, hv.1 ((hv.2.2.1 p₀).symm.trans (congrArg Sigma.fst h)), h⟩
  have ht1 : ∀ k, t k ∈ Φ₁ := fun k => by
    obtain ⟨p₀, -, h⟩ := hchart k
    show G.x' ⟨κ k, i' (κ k)⟩ ∈ Φ₁
    rw [← h, G.compat]
    exact hmem _
  have hrat : ∀ p : Σ k, ι k, G.x' (v p) / t p.1 ∈ F₀ := fun p => by
    obtain ⟨p₀, h1, h⟩ := hchart p.1
    show G.x' (v p) / G.x' ⟨κ p.1, i' (κ p.1)⟩ ∈ F₀
    rw [← h]
    exact hF0 p p₀ h1.symm

  have hΦ₁ : F₀ ⊔ E = Φ₁ := by
    refine le_antisymm (sup_le (IntermediateField.adjoin_le_iff.2 ?_) (IntermediateField.adjoin_le_iff.2 ?_)) ?_
    · rintro _ ⟨p, q, -, rfl⟩
      show G.x' (v p) / G.x' (v q) ∈ Φ₁
      rw [G.compat, G.compat]
      exact div_mem (hmem _) (hmem _)
    · rintro _ ⟨k, rfl⟩
      exact ht1 k
    · intro z hz
      obtain ⟨c, rfl⟩ := AlgHom.mem_fieldRange.1 hz
      obtain ⟨f, g, -, rfl⟩ := G.gen c
      have hpoly : ∀ f : MRing ι, algebraMap G.Φ G.Φ' (aeval G.x f) ∈ F₀ ⊔ E := by
        intro f
        induction f using MvPolynomial.induction_on with
        | C a =>
          rw [aeval_C, ← IsScalarTower.algebraMap_apply, algebraMap_int_eq, eq_intCast]
          exact intCast_mem _ a
        | add f g hf hg =>
          rw [map_add (f := _), map_add (f := _)]
          exact add_mem hf hg
        | mul_X f q hf =>
          rw [map_mul, map_mul, aeval_X, ← G.compat]
          refine mul_mem hf ?_
          rw [← div_mul_cancel₀ (G.x' (v q)) (hi' (κ q.1))]
          exact mul_mem ((le_sup_left : F₀ ≤ F₀ ⊔ E) (hrat q))
            ((le_sup_right : E ≤ F₀ ⊔ E) (IntermediateField.subset_adjoin _ _ ⟨q.1, rfl⟩))
      show IsScalarTower.toAlgHom ℚ G.Φ G.Φ' (aeval G.x f / aeval G.x g) ∈ F₀ ⊔ E
      rw [map_div₀]
      exact div_mem (hpoly f) (hpoly g)

  have hΦS : Φ₁ ⊔ IntermediateField.adjoin ℚ S = F₁ ⊔ E := by
    refine le_antisymm (sup_le ?_ ?_) (sup_le ?_ ?_)
    · rw [← hΦ₁]
      exact sup_le_sup_right hF01 E
    · refine (IntermediateField.adjoin_le_iff.2 ?_).trans le_sup_left
      rintro _ ⟨q, rfl⟩
      exact hF _ _ rfl
    · refine IntermediateField.adjoin_le_iff.2 ?_
      rintro _ ⟨⟨a, j⟩, ⟨b, l⟩, hab, rfl⟩
      dsimp only at hab
      subst hab
      by_cases ha : a ∈ Set.range κ
      · obtain ⟨k, rfl⟩ := ha
        obtain ⟨p, hp⟩ := hv.2.2.2 ⟨κ k, j⟩ ⟨k, rfl⟩
        obtain ⟨q, hq⟩ := hv.2.2.2 ⟨κ k, l⟩ ⟨k, rfl⟩
        have hpq : p.1 = q.1 := hv.1 ((hv.2.2.1 p).symm.trans
          ((congrArg Sigma.fst hp).trans ((congrArg Sigma.fst hq).symm.trans (hv.2.2.1 q))))
        rw [← hp, ← hq]
        exact (le_sup_left : Φ₁ ≤ _) (hΦ₁.le ((le_sup_left : F₀ ≤ F₀ ⊔ E) (hF0 p q hpq)))
      · rw [← div_div_div_cancel_right₀ (hi ⟨a, ha⟩) (G.x' ⟨a, j⟩) (G.x' ⟨a, l⟩)]
        refine (le_sup_right : IntermediateField.adjoin ℚ S ≤ _) (div_mem ?_ ?_)
        · exact IntermediateField.subset_adjoin _ _ ⟨⟨⟨a, ha⟩, j⟩, rfl⟩
        · exact IntermediateField.subset_adjoin _ _ ⟨⟨⟨a, ha⟩, l⟩, rfl⟩
    · rw [← hΦ₁]
      exact le_sup_right.trans le_sup_left

  have hy : IntermediateField.adjoin ℚ (Set.range fun q : Σ k', ι' k' => G.x' q / G.x' ⟨q.1, i' q.1⟩) = F₁ := by
    refine le_antisymm (IntermediateField.adjoin_le_iff.2 ?_) (IntermediateField.adjoin_le_iff.2 ?_)
    · rintro _ ⟨q, rfl⟩
      exact hF _ _ rfl
    · rintro _ ⟨⟨a, j⟩, ⟨b, l⟩, hab, rfl⟩
      dsimp only at hab
      subst hab
      rw [← div_div_div_cancel_right₀ (hi' a) (G.x' ⟨a, j⟩) (G.x' ⟨a, l⟩)]
      exact div_mem (IntermediateField.subset_adjoin _ _ ⟨⟨a, j⟩, rfl⟩)
        (IntermediateField.subset_adjoin _ _ ⟨⟨a, l⟩, rfl⟩)
  have hker := GenFibreChartDeg.isMultiHomogIdeal_ker_rat G.x' (by rw [G.genericFibre_ker_target]; exact hP)
  have hindep : AlgebraicIndependent F₁ t := by
    have key : ∀ L : IntermediateField ℚ G.Φ', L = F₁ → AlgebraicIndependent L t →
        AlgebraicIndependent F₁ t := by
      rintro L rfl h
      exact h
    exact key _ hy ((hT ℚ G.Φ' K' ι' G.x' i' hi' hker).comp κ hv.1)

  refine (GroundTheory.Heights₂.Heights.Inter.FinrankAdjoinRange.proof ℚ G.Φ G.Φ' S).trans ?_
  change IntermediateField.relfinrank Φ₁ (Φ₁ ⊔ IntermediateField.adjoin ℚ S) = _
  rw [hΦS, ← hΦ₁]
  exact hC ℚ G.Φ' F₀ F₁ K t hF01 hindep

end GroundTheory.Heights₂.Heights.Targets
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCoordRatioDeg
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace CoordRatioDeg

def ratioField {S M : Type*} [Field M] [CharZero M] (R : S → S → Prop) (z : S → M) : IntermediateField ℚ M :=
  IntermediateField.adjoin ℚ {t | ∃ p q, R p q ∧ t = z p / z q}

theorem ratioField_map {S M N : Type*} [Field M] [CharZero M] [Field N] [CharZero N] (R : S → S → Prop)
    (z : S → M) (f : M →ₐ[ℚ] N) : (ratioField R z).map f = ratioField R (f ∘ z) := by
  rw [ratioField, IntermediateField.adjoin_map, ratioField]
  congr 1
  ext t
  constructor
  · rintro ⟨_, ⟨p, q, h, rfl⟩, rfl⟩
    exact ⟨p, q, h, by simp⟩
  · rintro ⟨p, q, h, rfl⟩
    exact ⟨_, ⟨p, q, h, rfl⟩, by simp⟩

theorem ratioField_congr {S M : Type*} [Field M] [CharZero M] {R : S → S → Prop} {z w : S → M}
    (h : ∀ p q, R p q → z p / z q = w p / w q) : ratioField R z = ratioField R w := by
  unfold ratioField
  congr 1
  ext t
  constructor
  · rintro ⟨p, q, hpq, rfl⟩
    exact ⟨p, q, hpq, h p q hpq⟩
  · rintro ⟨p, q, hpq, rfl⟩
    exact ⟨p, q, hpq, (h p q hpq).symm⟩

theorem proof : CoordRatioDeg.Statement := by
  intro K _ ι _ K' _ ι' _ κ v Ω _ _ y Φ' _ _ x' hv hker
  let I : Ideal (MRing ι') := mCoordIdeal y
  let L := FractionRing (MvPolynomial K' Ω)
  have : CharZero L := charZero_of_injective_algebraMap (IsFractionRing.injective (MvPolynomial K' Ω) L)
  have h₁ : ∀ a ∈ I, (aeval x' : MRing ι' →ₐ[ℤ] Φ').toRingHom a = 0 := fun a ha => by
    rw [show I = _ from hker.symm] at ha
    exact RingHom.mem_ker.mp ha
  have h₂ : ∀ a ∈ I, (mConeMap y).toRingHom a = 0 := fun a ha => RingHom.mem_ker.mp ha
  let g₁ : MRing ι' ⧸ I →+* Φ' := Ideal.Quotient.lift I _ h₁
  have hg₁ : Function.Injective g₁ :=
    RingHom.lift_injective_of_ker_le_ideal I h₁ fun a ha => by
      change a ∈ mCoordIdeal y
      rw [← hker]
      exact ha
  let g₂ : MRing ι' ⧸ I →+* L := (algebraMap _ L).comp (Ideal.Quotient.lift I _ h₂)
  have hg₂ : Function.Injective g₂ :=
    (IsFractionRing.injective _ L).comp (RingHom.lift_injective_of_ker_le_ideal I h₂ fun a ha => ha)
  have : IsDomain (MRing ι' ⧸ I) := hg₁.isDomain g₁
  let F := FractionRing (MRing ι' ⧸ I)
  let f₁ : F →+* Φ' := IsFractionRing.lift hg₁
  have : CharZero F := ⟨fun m n h => by
    have h' := congrArg f₁ h
    rw [map_natCast, map_natCast] at h'
    exact_mod_cast h'⟩
  let f₂ : F →+* L := IsFractionRing.lift hg₂
  let xb : (Σ k', ι' k') → F := fun p => algebraMap _ F (Ideal.Quotient.mk I (X p))
  have e₁ : f₁.toRatAlgHom ∘ xb = x' := funext fun p => by
    simp [xb, f₁, g₁, IsFractionRing.lift_algebraMap]
  have e₂ : ∀ p, f₂ (xb p) = algebraMap _ L (C (y p) * X p.1) := fun p => by
    simp [xb, f₂, g₂, IsFractionRing.lift_algebraMap, mConeMap]
  let c : Ω →ₐ[ℚ] L := ((algebraMap (MvPolynomial K' Ω) L).comp C).toRatAlgHom
  have hT : ∀ k, algebraMap (MvPolynomial K' Ω) L (X k) ≠ 0 := fun k =>
    (map_ne_zero_iff _ (IsFractionRing.injective _ L)).mpr (X_ne_zero k)
  have hr : ∀ p q : Σ k', ι' k', p.1 = q.1 → f₂ (xb p) / f₂ (xb q) = c (y p) / c (y q) := by
    intro p q h
    rw [e₂, e₂, h, map_mul, map_mul, mul_div_mul_right _ _ (hT _)]
    rfl
  change IntermediateField.relfinrank (ratioField (fun p q : Σ k, ι k => p.1 = q.1) (x' ∘ v))
      (ratioField (fun p q : Σ k', ι' k' => p.1 = q.1) x') =
    IntermediateField.relfinrank (ratioField (fun p q : Σ k, ι k => p.1 = q.1) (y ∘ v))
      (ratioField (fun p q : Σ k', ι' k' => p.1 = q.1) y)
  rw [← IntermediateField.relfinrank_map_map _ _ c, ratioField_map, ratioField_map, ← e₁,
    Function.comp_assoc, ← ratioField_map, ← ratioField_map,
    IntermediateField.relfinrank_map_map,
    ← IntermediateField.relfinrank_map_map _ _ f₂.toRatAlgHom, ratioField_map, ratioField_map]
  congr 1
  · refine ratioField_congr fun p q h => ?_
    simpa using hr (v p) (v q) (by rw [hv.2.2.1, hv.2.2.1, h])
  · exact ratioField_congr fun p q h => by simpa using hr p q h

end CoordRatioDeg

end GroundTheory.Heights₂.Heights.Targets
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveVertIndex
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

def CurveVertIndex.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (s : MRing ι) (d : K → ℕ),
    IsArithVar (mCoordIdeal y) 1 → ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s d → s ∉ mCoordIdeal y →
      vertR (mCoordIdeal y) (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) s =
        Real.log (genIndex (chartLat y (fun k => (d k : ℤ)) 1) (curveMul y (aeval y s)))

namespace CurveVertIndex

end CurveVertIndex

end GroundTheory.Heights₂.Heights.Targets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveIndexLinear
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def CurveIndexLinear.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k),
    IsArithVar (mCoordIdeal y) 1 → (∀ k, y ⟨k, c k⟩ ≠ 0) →
      (∀ a a' : K → ℤ, chartIndexLog y c (a + a') 1 = chartIndexLog y c a 1 + chartIndexLog y c a' 1) ∧
      ∀ (a : K → ℤ) (τ : ℕ), chartIndexLog y c a τ = τ * chartIndexLog y c a 1

namespace CurveIndexLinear

end CurveIndexLinear

end GroundTheory.Heights₂.Heights.Targets
end
