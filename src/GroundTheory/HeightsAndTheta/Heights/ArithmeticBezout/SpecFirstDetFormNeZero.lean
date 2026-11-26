module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.Statements
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsMahler
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PHomogDimZeroPow
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PFundCycleBaseChange

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.SpecFirstDetFormNeZero
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ArithBezout

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Matrix

section Objects

variable {n : ℕ}



def specFirst {R : Type*} [CommRing R] {e : ℕ} (u : Fin n → R) :
    MvPolynomial (Fin (e + 1) × Fin n) R →ₐ[R] MvPolynomial (Fin e × Fin n) R :=
  aeval fun p => Fin.cases (motive := fun _ => MvPolynomial (Fin e × Fin n) R) (C (u p.2))
    (fun k => X (k, p.2)) p.1


end Objects


end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ArithBezout

end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsIncidenceZeroLocus
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def IncidenceZeroLocus.Statement : Prop :=
  ∀ (F : Type) [Field F] (n k : ℕ) (Q : Ideal (MvPolynomial (Fin n) F)), IsHomogIdeal Q →
    ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra F Ω] (v : Fin k × Fin n → Ω),
      (∀ g ∈ incIdeal Q k, aeval v g = 0) →
        ∃ y : Fin n → Ω, y ≠ 0 ∧ (∀ q ∈ Q, aeval y q = 0) ∧ ∀ i, ∑ j, v (i, j) * y j = 0

section Inhabitants

attribute [local instance] MvPolynomial.gradedAlgebra

end Inhabitants

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PFsLogSmul
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

theorem HermNorm.dualNorm_smul {n : ℕ} (h : HermNorm n) (t : ℂ) (y : Fin n → ℂ) :
    h.dualNorm (t • y) = ‖t‖ * h.dualNorm y := by
  unfold HermNorm.dualNorm
  rw [Matrix.mulVec_smul]
  have hs : (∑ i, ‖(t • ((h.mat)ᵀ⁻¹ *ᵥ y)) i‖ ^ 2) = ‖t‖ ^ 2 * ∑ i, ‖((h.mat)ᵀ⁻¹ *ᵥ y) i‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
  rw [hs, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChowFormBaseChange
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

theorem isHomogIdeal_map {R S : Type*} [CommRing R] [CommRing S] {n : ℕ} (φ : R →+* S)
    {I : Ideal (MvPolynomial (Fin n) R)} (hI : IsHomogIdeal I) :
    IsHomogIdeal (I.map (MvPolynomial.map φ)) := by
  rw [isHomogIdeal_iff] at hI ⊢
  obtain ⟨T, hT⟩ := (Ideal.IsHomogeneous.iff_exists _ _).mp hI
  rw [hT, Ideal.map_span]
  refine Ideal.homogeneous_span _ _ ?_
  rintro _ ⟨_, ⟨x, -, rfl⟩, rfl⟩
  obtain ⟨d, hd⟩ := x.2
  refine ⟨d, ?_⟩
  rw [mem_homogeneousSubmodule] at hd ⊢
  exact hd.map φ

theorem ChowFormBaseChange.proof (hRad : RadicalBaseChange.Statement)
    (hExt : ChowFormExtend.Statement) (hRed : ChowFormReduced.Statement) :
    ChowFormBaseChange.Statement := by
  intro K _ _ n k I f σ hI hf
  have hJ : IsHomogIdeal (I.map (MvPolynomial.map σ)) := isHomogIdeal_map σ hI.isHomog
  refine ⟨fun W hW => isProjPrime_of_mem_support_fundCycle hJ hW, ?_⟩
  exact hRed ℂ n k _ _ hJ (hRad K ℂ σ (Fin n) I hI.isPrime.isRadical) (hExt K ℂ σ n k I f hf)

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChowFormAssoc
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem ChowFormAssoc.proof : ChowFormAssoc.Statement := by
  intro F _ n k I g g' hg hg'
  have h1 : g ∣ g' := (hg.2 g').mp ((hg'.2 g').mpr dvd_rfl)
  have h2 : g' ∣ g := (hg'.2 g).mp ((hg.2 g).mpr dvd_rfl)
  obtain ⟨u, hu⟩ := associated_of_dvd_dvd h1 h2
  obtain ⟨c, hc, hcu⟩ :=
    (isUnit_iff_eq_C_of_isReduced (P := (u : MvPolynomial (Fin k × Fin n) F))).mp u.isUnit
  refine ⟨c, hc.ne_zero, ?_⟩
  rw [← hu, hcu, mul_comm]

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChowFormCycleSmul
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem ChowFormCycleSmul.proof : ChowFormCycleSmul.Statement := by
  intro F _ n k m Z f hZ
  obtain ⟨c, hc, g, hg, hf⟩ := hZ
  refine ⟨c ^ m, pow_ne_zero _ hc, g, fun W hW => hg W (Finsupp.support_smul hW), ?_⟩
  have hsub : (m • Z).support ⊆ Z.support := Finsupp.support_smul
  rw [Finset.prod_subset hsub (fun W _ hW => by rw [Finsupp.notMem_support_iff.mp hW, pow_zero]), hf,
    mul_pow, ← map_pow, ← Finset.prod_pow]
  congr 1
  refine Finset.prod_congr rfl fun W _ => ?_
  rw [Finsupp.smul_apply, smul_eq_mul, ← pow_mul, mul_comm]

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PAreaFormulaInj
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Module

open scoped ENNReal

theorem AreaFormulaInj.proof (h : AreaFormulaInjSet.Statement) : AreaFormulaInj.Statement := by
  classical
  intro E F _ _ _ _ _ _ _ _ _ _ k hk U A f g hU hf hAU hA hinj hg
  let f' : E → F := U.piecewise f (fun _ => 0)
  have hf'm : Measurable f' := hf.continuousOn.measurable_piecewise continuousOn_const hU.measurableSet
  have hEq : ∀ x ∈ A, f' x = f x := fun x hx => Set.piecewise_eq_of_mem _ _ _ (hAU hx)
  have hJ : Measurable fun x : E => ENNReal.ofReal (areaJacobian (fderiv ℝ f x : E →ₗ[ℝ] F)) :=
    ENNReal.measurable_ofReal.comp (continuous_areaJacobian.measurable.comp (measurable_fderiv ℝ f))
  let ρ : Measure E := ((μH[(k : ℝ)] : Measure E).restrict A).withDensity
    fun x : E => ENNReal.ofReal (areaJacobian (fderiv ℝ f x : E →ₗ[ℝ] F))
  have hmap : ρ.map f' = (μH[(k : ℝ)] : Measure F).restrict (f '' A) := by
    ext S hS
    have hpre : MeasurableSet (f' ⁻¹' S) := hf'm hS
    rw [Measure.map_apply hf'm hS, withDensity_apply _ hpre, Measure.restrict_restrict hpre,
      Measure.restrict_apply hS,
      ← h E F k hk U _ f hU hf (by exact fun x hx => hAU hx.2) (hpre.inter hA) (hinj.mono fun x hx => hx.2)]
    congr 1
    ext z
    constructor
    · rintro ⟨y, ⟨hyS, hyA⟩, rfl⟩
      exact ⟨by simpa [Set.mem_preimage, hEq y hyA] using hyS, y, hyA, rfl⟩
    · rintro ⟨hzS, y, hyA, rfl⟩
      exact ⟨y, ⟨by simpa [Set.mem_preimage, hEq y hyA] using hzS, hyA⟩, rfl⟩
  calc ∫⁻ y in f '' A, g y ∂(μH[(k : ℝ)]) = ∫⁻ z, g z ∂(ρ.map f') := by rw [hmap]
    _ = ∫⁻ x, g (f' x) ∂ρ := lintegral_map hg hf'm
    _ = ∫⁻ x in A, ENNReal.ofReal (areaJacobian (fderiv ℝ f x : E →ₗ[ℝ] F)) * g (f' x)
          ∂(μH[(k : ℝ)]) := lintegral_withDensity_eq_lintegral_mul _ hJ (hg.comp hf'm)
    _ = _ := setLIntegral_congr_fun hA fun x hx => by rw [hEq x hx, mul_comm]

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChowFormCycleAdd
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem ChowFormCycleAdd.proof (h1 : ChowFormAssoc.Statement) : ChowFormCycleAdd.Statement := by
  classical
  intro F _ n k Z₁ Z₂ f₁ f₂ ⟨c₁, hc₁, g₁, hg₁, hf₁⟩ ⟨c₂, hc₂, g₂, hg₂, hf₂⟩
  subst hf₁ hf₂
  let g : Ideal (MvPolynomial (Fin n) F) → MvPolynomial (Fin k × Fin n) F :=
    fun W => if W ∈ Z₁.support then g₁ W else g₂ W
  have hd : ∀ W, ∃ d : F, d ≠ 0 ∧ (W ∈ Z₂.support → g₂ W = C d * g W) := by
    intro W
    by_cases hW1 : W ∈ Z₁.support
    · by_cases hW2 : W ∈ Z₂.support
      · obtain ⟨d, hd, he⟩ := h1 F n k W (g₁ W) (g₂ W) (hg₁ W hW1) (hg₂ W hW2)
        exact ⟨d, hd, fun _ => by simp only [g, if_pos hW1, he]⟩
      · exact ⟨1, one_ne_zero, fun h => absurd h hW2⟩
    · exact ⟨1, one_ne_zero, fun _ => by simp only [g, if_neg hW1, map_one, one_mul]⟩
  choose d hd0 hdg using hd
  have hsupp : (Z₁ + Z₂).support = Z₁.support ∪ Z₂.support := by
    ext W
    simp only [Finsupp.mem_support_iff, Finset.mem_union, Finsupp.coe_add, Pi.add_apply, ne_eq,
      Nat.add_eq_zero_iff, not_and_or]
  refine ⟨c₁ * c₂ * ∏ W ∈ Z₂.support, d W ^ Z₂ W, ?_, g, ?_, ?_⟩
  · exact mul_ne_zero (mul_ne_zero hc₁ hc₂)
      (Finset.prod_ne_zero_iff.mpr fun W _ => pow_ne_zero _ (hd0 W))
  · intro W hW
    rw [hsupp, Finset.mem_union] at hW
    by_cases hW1 : W ∈ Z₁.support
    · simpa only [g, if_pos hW1] using hg₁ W hW1
    · simpa only [g, if_neg hW1] using hg₂ W (hW.resolve_left hW1)
  · have e1 : ∏ W ∈ Z₁.support, g₁ W ^ Z₁ W =
        ∏ W ∈ Z₁.support ∪ Z₂.support, g W ^ Z₁ W := by
      rw [← Finset.prod_subset Finset.subset_union_left (f := fun W => g W ^ Z₁ W)]
      · exact Finset.prod_congr rfl fun W hW => by simp only [g, if_pos hW]
      · intro W _ hW
        rw [Finsupp.mem_support_iff, not_not] at hW
        simp [hW]
    have e2 : ∏ W ∈ Z₂.support, g₂ W ^ Z₂ W =
        C (∏ W ∈ Z₂.support, d W ^ Z₂ W) * ∏ W ∈ Z₁.support ∪ Z₂.support, g W ^ Z₂ W := by
      rw [← Finset.prod_subset Finset.subset_union_right (f := fun W => g W ^ Z₂ W)]
      · rw [map_prod, ← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl fun W hW => by rw [hdg W hW, mul_pow, map_pow]
      · intro W _ hW
        rw [Finsupp.mem_support_iff, not_not] at hW
        simp [hW]
    rw [hsupp, e1, e2]
    simp only [Finsupp.coe_add, Pi.add_apply, pow_add, Finset.prod_mul_distrib, map_mul]
    ring

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PBallVolume
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

theorem BallVolume.proof : BallVolume.Statement := by
  intro n h
  have hcont : Continuous fun v : Fin n → ℂ => h.norm v := by
    simp only [HermNorm.norm, Matrix.mulVec, dotProduct]
    fun_prop
  have hopen : IsOpen (ballH h) := isOpen_lt hcont continuous_const
  have hzero : (0 : Fin n → ℂ) ∈ ballH h := by
    show h.norm 0 < 1
    simp [HermNorm.norm]
  have hR : 0 ≤ ∑ j', ∑ l, ‖h.mat⁻¹ j' l‖ :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hbdd : Bornology.IsBounded (ballH h) := by
    refine (Metric.isBounded_closedBall (x := (0 : Fin n → ℂ))
      (r := ∑ j', ∑ l, ‖h.mat⁻¹ j' l‖)).subset fun v hv => ?_
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hR]
    intro j
    exact norm_le_of_hermNorm_lt h hv j
  exact ⟨hopen.measure_pos volume ⟨0, hzero⟩, hbdd.measure_lt_top⟩

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PPointLine
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace PointLine

variable {n : ℕ}

theorem eval_smul_of_isHomogeneous {φ : MvPolynomial (Fin n) ℂ} {m : ℕ} (hφ : φ.IsHomogeneous m)
    (t : ℂ) (x : Fin n → ℂ) : eval (t • x) φ = t ^ m * eval x φ := by
  rw [eval_eq, eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg := hφ.degree_eq_sum_deg_support hd
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [← hdeg]
  ring

theorem smul_mem_zeroSet {W : Ideal (MvPolynomial (Fin n) ℂ)} (hW : IsHomogIdeal W)
    {x : Fin n → ℂ} (hx : ∀ q ∈ W, eval x q = 0) (t : ℂ) : ∀ q ∈ W, eval (t • x) q = 0 := by
  intro q hq
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← sum_homogeneousComponent q, map_sum]
  refine Finset.sum_eq_zero fun d _ => ?_
  rw [eval_smul_of_isHomogeneous (homogeneousComponent_isHomogeneous d q), hx _ (hW q hq d), mul_zero]

end PointLine


end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeIntegralLine
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix

noncomputable section

variable {n : ℕ}

theorem HermNorm.continuous_pointOf (h : HermNorm n) : Continuous h.pointOf := by
  unfold HermNorm.pointOf
  exact Continuous.matrix_mulVec continuous_const (continuous_pi fun i => by fun_prop)

theorem HermNorm.pointOf_eq_zero (h : HermNorm n) {y : EuclideanSpace ℂ (Fin n)}
    (hy : h.pointOf y = 0) : y = 0 := by
  have hu : IsUnit h.matᵀ := (Matrix.isUnit_iff_isUnit_det _).mpr (by rw [det_transpose]; exact h.isUnit_det)
  have hv : (fun i => y i) = 0 :=
    Matrix.mulVec_injective_iff_isUnit.mpr hu (by simpa [HermNorm.pointOf] using hy)
  ext i
  simpa using congrFun hv i

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PSpecFirstSwapMahler
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem specFirst_C_mul {n k : ℕ} (c : ℂ) (f : MvPolynomial (Fin (k + 1) × Fin n) ℂ) (u : Fin n → ℂ) :
    specFirst (C c * f) u = C c * specFirst f u := by
  unfold specFirst
  rw [map_mul, bind₁_C_right]

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PEvalSpecFirst
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem EvalSpecFirst.proof : EvalSpecFirst.Statement := by
  intro n k f v w
  change eval₂Hom (RingHom.id ℂ) w (bind₁ (specFirstVar v) f) =
    eval₂Hom (RingHom.id ℂ) (consGroup v w) f
  rw [eval₂Hom_bind₁]
  congr 2
  funext ij
  obtain ⟨i, j⟩ := ij
  induction i using Fin.cases with
  | zero => simp [specFirstVar, consGroup]
  | succ i => simp [specFirstVar, consGroup]

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PMahlerSectionOfConst
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

theorem MahlerSectionOfConst.proof (h1 : DefectAverage.Statement) (h2 : AdmissibleAENrm.Statement)
    (h3 : BallVolume.Statement) : MahlerSectionOfConst.Statement := by
  intro e hconst n δ h Z f u data hu
  set K := mahlerDefect h e Z f u with hK
  have hrel : ∀ W ∈ Z.support, IsRelevant W := fun W hW => (data.prime W hW).isRelevant
  have hae : (fun v => mahlerDefect h e Z f (nrmv h v)) =ᵐ[volume.restrict (ballH h)] fun _ => K := by
    filter_upwards [h2 n h Z hrel] with v hv
    exact hconst n δ h Z f (nrmv h v) u data hv hu
  have havg : ⨍ v in ballH h, mahlerDefect h e Z f (nrmv h v) = K := by
    rw [average_congr hae]
    obtain ⟨hpos, hfin⟩ := h3 n h
    exact setAverage_const hpos.ne' hfin.ne K
  have hmean := (h1 n e δ h Z f data).2
  rw [havg] at hmean
  have hK' : K = mahler h e (specFirst f u) - cycleIntegral h Z e (fsLog h u) := rfl
  linarith
end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PFsLogPointOf
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

theorem FsLogPointOf.proof : FsLogPointOf.Statement := by
  intro n h v y
  have hdet : IsUnit (h.matᵀ).det := by rw [Matrix.det_transpose]; exact h.isUnit_det
  have hd : h.dualNorm (h.pointOf y) = (HermNorm.std n).dualNorm (fun i => y i) := by
    simp only [HermNorm.dualNorm, HermNorm.pointOf, HermNorm.std, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec, Matrix.transpose_one, inv_one]
  have hn : (HermNorm.std n).norm (h.mat *ᵥ v) = h.norm v := by
    simp only [HermNorm.norm, HermNorm.std, Matrix.one_mulVec]
  have hs : ∑ j, v j * h.pointOf y j = ∑ i, (h.mat *ᵥ v) i * y i := by
    have := Matrix.dotProduct_mulVec v h.matᵀ (fun i => y i)
    rw [Matrix.vecMul_transpose] at this
    simpa [dotProduct, HermNorm.pointOf] using this
  unfold fsLog nrmv
  rw [hd, hn]
  simp only [mul_assoc, ← Finset.mul_sum, hs]

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PMahlerIntegrand
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

theorem ballProd_subset_polydisc {n k : ℕ} (h : HermNorm n) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ (v : Fin n → ℂ) (j : Fin n), ‖v j‖ ≤ C * h.norm v) :
    ballProd h k ⊆ LogInt.polydisc _ C := by
  intro u hu
  simp only [LogInt.polydisc, Set.mem_univ_pi, Metric.mem_closedBall, dist_zero_right]
  intro ij
  exact (hC (fun j => u (ij.1, j)) ij.2).trans (mul_le_of_le_one_right hC0 (hu ij.1).le)

theorem MahlerIntegrand.proof : MahlerIntegrand.Statement := by
  intro n k δ h f hf _
  obtain ⟨C, hC0, hC⟩ := h.li_exists_coord_le
  have e : nrmGroups h k = LogInt.normT h Finset.univ := by
    funext u ij
    simp [nrmGroups, LogInt.normT]
  rw [e]
  exact (LogInt.logNormT h C hC0 hC Finset.univ f hf).1.mono_set (ballProd_subset_polydisc h C hC0 hC)

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PCharacterised
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory NumberField

noncomputable section

theorem not_isChowForm_zero (hPt : ProjPrimeHasPoint.Statement) {F : Type} [Field F] {n : ℕ}
    {W : Ideal (MvPolynomial (Fin n) F)} (hW : IsProjPrime W) (g : MvPolynomial (Fin 0 × Fin n) F) :
    ¬ IsChowForm W 0 g := by
  intro hg
  obtain ⟨x, hx, hxW⟩ := hPt F n W hW
  have hunit : g ∣ 1 := by
    rw [eq_C_of_isEmpty g] at hg ⊢
    have hc : AddMonoidAlgebra.coeff g 0 ≠ 0 := fun h => hg.1 (by rw [h, map_zero])
    exact ⟨C (AddMonoidAlgebra.coeff g 0)⁻¹, by rw [← C_mul, mul_inv_cancel₀ hc, C_1]⟩
  have hinc : (fun _ => 0 : Fin 0 × Fin n → AlgebraicClosure F) ∈ incidence W 0 :=
    ⟨x, hx, hxW, fun i => i.elim0⟩
  have := (hg.2 1).mpr hunit _ hinc
  simp at this

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PFsLogMeasurable
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Matrix

theorem FsLogMeasurable.proof : FsLogMeasurable.Statement := by
  intro n h
  have hn : Continuous h.norm := by
    unfold HermNorm.norm
    fun_prop
  have hd : Continuous h.dualNorm := by
    unfold HermNorm.dualNorm
    fun_prop
  have hp : Continuous h.pointOf := by
    unfold HermNorm.pointOf
    fun_prop
  have hinv : Measurable fun v : Fin n → ℂ => ((h.norm v : ℝ) : ℂ)⁻¹ :=
    (Complex.continuous_ofReal.comp hn).measurable.inv
  have hv : Measurable fun p : (Fin n → ℂ) × EuclideanSpace ℂ (Fin n) => nrmv h p.1 := by
    unfold nrmv
    refine Measurable.of_eval fun j => ?_
    exact (hinv.comp measurable_fst).mul ((measurable_pi_apply j).comp measurable_fst)
  have hy : Measurable fun p : (Fin n → ℂ) × EuclideanSpace ℂ (Fin n) => h.pointOf p.2 :=
    hp.measurable.comp measurable_snd
  unfold fsLog
  refine Real.measurable_log.comp (Measurable.div ?_ (hd.measurable.comp hy))
  refine Measurable.norm ?_
  refine Finset.measurable_sum _ fun j _ => ?_
  exact ((measurable_pi_apply j).comp hv).mul ((measurable_pi_apply j).comp hy)

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PDefectAverage
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

theorem IsChowFormCycle.ne_zero {n k : ℕ} {Z : ProjCycle ℂ n} {f : MvPolynomial (Fin k × Fin n) ℂ}
    (hf : IsChowFormCycle Z k f) : f ≠ 0 := by
  obtain ⟨c, hc, g, hg, rfl⟩ := hf
  refine mul_ne_zero ?_ ?_
  · rw [Ne, MvPolynomial.C_eq_zero]; exact hc
  · rw [Finset.prod_ne_zero_iff]
    intro W hW
    exact pow_ne_zero _ (hg W hW).1

theorem DefectAverage.proof (h1 : MahlerAverageSplit.Statement) (h2 : CycleAverage.Statement) :
    DefectAverage.Statement := by
  intro n e δ h Z f hZ
  obtain ⟨hi1, hm1⟩ := h1 n e δ h f hZ.chow.ne_zero hZ.homog
  obtain ⟨hi2, hm2⟩ := h2 n e δ h Z f hZ
  have hi : IntegrableOn (fun v => mahlerDefect h e Z f (nrmv h v)) (ballH h) := by
    unfold mahlerDefect; exact hi1.sub hi2
  refine ⟨hi, ?_⟩
  have hsub : ⨍ v in ballH h, mahlerDefect h e Z f (nrmv h v) =
      (⨍ v in ballH h, mahler h e (specFirst f (nrmv h v))) -
        ⨍ v in ballH h, cycleIntegral h Z e (fsLog h (nrmv h v)) := by
    simp only [setAverage_eq, mahlerDefect]
    rw [integral_sub hi1 hi2, smul_sub]
  rw [hsub, ← hm1, hm2]
  ring

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PMahlerAverageSplit
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

noncomputable section

theorem mahler_specFirst_eq (h3 : EvalSpecFirst.Statement) {n e : ℕ} (h : HermNorm n)
    (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ) (v : Fin n → ℂ) :
    mahler h e (specFirst f v) =
      sphereMean h e (fun w => Real.log ‖eval (consGroup v w) f‖) := by
  unfold mahler
  congr 1
  funext w
  rw [h3]

theorem MahlerAverageSplit.proof (h1 : MahlerIntegrand.Statement) (h2 : SphereMeanFubini.Statement)
    (h3 : EvalSpecFirst.Statement) : MahlerAverageSplit.Statement := by
  intro n e δ h f hf hhom
  have hint := h1 n (e + 1) δ h f hf hhom
  obtain ⟨hI, hM⟩ := h2 n e h (fun u => Real.log ‖eval u f‖) hint
  have key : (fun v => mahler h e (specFirst f (nrmv h v))) =
      fun v => sphereMean h e (fun w => Real.log ‖eval (consGroup (nrmv h v) w) f‖) := by
    funext v
    exact mahler_specFirst_eq h3 h f (nrmv h v)
  rw [key]
  exact ⟨hI, hM⟩

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeFubini
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

noncomputable section

theorem ConeFubini.proof (h1 : BallVolume.Statement) : ConeFubini.Statement := by
  intro n h μ _ F c M hF hy
  obtain ⟨hpos, hfin⟩ := h1 n h
  have : IsFiniteMeasure (volume.restrict (ballH h)) := isFiniteMeasure_restrict.2 hfin.ne
  have hsm : StronglyMeasurable (Function.uncurry F) := hF.stronglyMeasurable

  have hint : Integrable (Function.uncurry F) ((volume.restrict (ballH h)).prod μ) := by
    rw [integrable_prod_iff' hsm.aestronglyMeasurable]
    refine ⟨hy.mono fun y hy => hy.1, ?_⟩
    refine Integrable.of_bound ?_ M ?_
    · exact (hsm.norm.integral_prod_left' (μ := volume.restrict (ballH h))).aestronglyMeasurable
    · filter_upwards [hy] with y hy
      have e : ∀ x, ‖Function.uncurry F (x, y)‖ = |F x y| := fun x => Real.norm_eq_abs _
      simp only [e]
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => abs_nonneg _)]
      exact hy.2.1
  refine ⟨hint.integral_prod_left, ?_⟩
  have hvol : (volume (ballH h)).toReal ≠ 0 := (ENNReal.toReal_pos hpos.ne' hfin.ne).ne'
  have hreal : volume.real (ballH h) = (volume (ballH h)).toReal := rfl

  have hin : ∀ᵐ y ∂μ, ∫ v in ballH h, F v y = c * (volume (ballH h)).toReal := by
    filter_upwards [hy] with y hy
    have e := hy.2.2
    rw [setAverage_eq, hreal, smul_eq_mul] at e
    field_simp at e ⊢
    linarith
  have hswap := integral_integral_swap hint
  rw [setAverage_eq, hreal, smul_eq_mul, hswap, integral_congr_ae hin, integral_const, smul_eq_mul]
  simp only [measureReal_def]
  field_simp
end
end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PFsLogAverage
set_option maxSynthPendingDepth 1

open MeasureTheory Matrix

namespace GroundTheory.Heights₂.Heights

theorem FsLogAverage.proof (h1 : BallAverageLinear.Statement) (h2 : FsLogPointOf.Statement)
    (h3 : SphereMeanLinearBall.Statement) (h4 : BallVolume.Statement) : FsLogAverage.Statement := by
  intro n h y hy
  set y' : Fin n → ℂ := fun i => y i with hy'def
  have hy' : y' ≠ 0 := by
    intro hz
    apply hy
    ext i
    exact congrFun hz i
  set φ : (Fin n → ℂ) → ℝ := fun w => fsLog (HermNorm.std n) (nrmv (HermNorm.std n) w) y' with hφ
  have hrw : (fun v => fsLog h (nrmv h v) (h.pointOf y)) = fun v => φ (h.mat *ᵥ v) := by
    funext v
    exact h2 n h v y
  obtain ⟨hint, hle, hmean⟩ := h3 n y' hy'
  have habs : (fun w => |φ w|) = fun w => -φ w := by
    funext w
    exact abs_of_nonpos (hle w)
  have hmeanAbs : ⨍ v in ballH h, |φ (h.mat *ᵥ v)| = (harmonic (n - 1) : ℝ) / 2 := by
    rw [(h1 n h (fun w => |φ w|)).2, habs]
    change (⨍ w in ballH (HermNorm.std n), (-φ) w) = _
    rw [average_neg, hmean]
    ring
  obtain ⟨_, hfin⟩ := h4 n h
  refine ⟨?_, ?_, ?_⟩
  · rw [hrw]
    exact (h1 n h φ).1.mpr hint
  · simp only [show ∀ v, fsLog h (nrmv h v) (h.pointOf y) = φ (h.mat *ᵥ v) from fun v => h2 n h v y]
    rw [← measure_smul_setAverage _ hfin.ne, hmeanAbs, smul_eq_mul, measureReal_def]
    ring
  · rw [hrw, (h1 n h φ).2]
    exact hmean

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PCycleAverage
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

noncomputable section

theorem CycleAverage.proof (h1 : ConeAverage.Statement) : CycleAverage.Statement := by
  intro n e δ h Z f hd
  obtain ⟨c, hc, g, hg, hf⟩ := hd.chow
  have hf0 : C c * ∏ W ∈ Z.support, g W ^ Z W ≠ 0 :=
    mul_ne_zero (C_ne_zero.mpr hc)
      (Finset.prod_ne_zero_iff.mpr fun W hW => pow_ne_zero _ (hg W hW).1)
  have hhom : IsMultiHomog δ (C c * ∏ W ∈ Z.support, g W ^ Z W) := hf ▸ hd.homog
  obtain ⟨δW, hδW, hsum⟩ :=
    exists_degrees_of_chowFormCycle (Nat.succ_pos e) Z c g hg hhom hf0
  have hW : ∀ W ∈ Z.support,
      IntegrableOn (fun v => coneIntegral h W e (fsLog h (nrmv h v))) (ballH h) ∧
        ⨍ v in ballH h, coneIntegral h W e (fsLog h (nrmv h v)) =
          -(δW W * (harmonic (n - 1) : ℝ)) / 2 :=
    fun W hm => h1 n e (δW W) h W (g W) (hd.prime W hm) (hg W hm) (hδW W hm)
  have hint : ∀ W ∈ Z.support,
      IntegrableOn (fun v => (Z W : ℝ) * coneIntegral h W e (fsLog h (nrmv h v))) (ballH h) :=
    fun W hm => (hW W hm).1.const_mul _
  unfold cycleIntegral
  refine ⟨integrable_finsetSum _ hint, ?_⟩
  rw [setAverage_eq, integral_finsetSum _ hint, Finset.smul_sum]
  have hterm : ∀ W ∈ Z.support,
      (volume.real (ballH h))⁻¹ • ∫ v in ballH h, (Z W : ℝ) * coneIntegral h W e (fsLog h (nrmv h v)) =
        (Z W : ℝ) * (-(δW W * (harmonic (n - 1) : ℝ)) / 2) := by
    intro W hm
    rw [integral_const_mul, ← (hW W hm).2, setAverage_eq, smul_eq_mul, smul_eq_mul]
    ring
  rw [Finset.sum_congr rfl hterm]
  have hδ : (δ : ℝ) = ∑ W ∈ Z.support, (Z W : ℝ) * (δW W : ℝ) := by
    rw [← hsum]; push_cast; rfl
  rw [hδ, Finset.sum_mul, ← Finset.sum_neg_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun W _ => ?_
  ring

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PAdmissibleAENrm
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix

noncomputable section

variable {n : ℕ}

theorem linForm_const_mul (c : ℂ) (v : Fin n → ℂ) :
    linForm (fun j => c * v j) = C c * linForm v := by
  simp only [linForm, Finset.mul_sum, map_mul, mul_assoc]

theorem HermNorm.norm_ne_zero (h : HermNorm n) {v : Fin n → ℂ} (hv : v ≠ 0) : h.norm v ≠ 0 := by
  intro h0
  apply hv
  have hs : ∑ i, ‖(h.mat *ᵥ v) i‖ ^ 2 = 0 :=
    (Real.sqrt_eq_zero (Finset.sum_nonneg fun i _ => sq_nonneg _)).mp h0
  have hm : h.mat *ᵥ v = 0 := by
    funext i
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ‖(h.mat *ᵥ v) i‖)).mp hs i
      (Finset.mem_univ i)
    simpa using this
  exact Matrix.eq_zero_of_mulVec_eq_zero h.isUnit_det.ne_zero hm

theorem IsAdmissible.nrmv (h : HermNorm n) {Z : ProjCycle ℂ n} {v : Fin n → ℂ}
    (hv : IsAdmissible Z v) : IsAdmissible Z (nrmv h v) := by
  intro W hW hmem
  apply hv W hW
  have hv0 : v ≠ 0 := by
    rintro rfl
    apply hv W hW
    simp [linForm]
  have hc : ((h.norm v : ℝ) : ℂ)⁻¹ ≠ 0 :=
    inv_ne_zero (Complex.ofReal_ne_zero.mpr (h.norm_ne_zero hv0))
  have hmem' : C ((h.norm v : ℝ) : ℂ)⁻¹ * linForm v ∈ W := by
    rw [← linForm_const_mul]; exact hmem
  have : linForm v = C (((h.norm v : ℝ) : ℂ)⁻¹)⁻¹ * (C ((h.norm v : ℝ) : ℂ)⁻¹ * linForm v) := by
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul]
  rw [this]
  exact W.mul_mem_left _ hmem'

theorem AdmissibleAENrm.proof (h1 : AdmissibleAE.Statement) : AdmissibleAENrm.Statement := by
  intro n h Z hrel
  exact ae_restrict_of_ae ((h1 n Z hrel).mono fun v hv => hv.nrmv h)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PDivCyclePrime
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {n : ℕ}

theorem isHomogeneous_of_mem_minimalPrimes {I P : Ideal (MvPolynomial (Fin n) ℂ)}
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin n) ℂ)) (hP : P ∈ I.minimalPrimes) :
    P.IsHomogeneous (homogeneousSubmodule (Fin n) ℂ) := by
  have hcore : (P.homogeneousCore (homogeneousSubmodule (Fin n) ℂ)).toIdeal.IsPrime :=
    hP.1.1.homogeneousCore
  have hle : I ≤ (P.homogeneousCore (homogeneousSubmodule (Fin n) ℂ)).toIdeal :=
    hI.toIdeal_homogeneousCore_eq_self.symm.trans_le (Ideal.homogeneousCore_mono _ hP.1.2)
  have hcoreP := Ideal.toIdeal_homogeneousCore_le (homogeneousSubmodule (Fin n) ℂ) P
  rw [Ideal.IsHomogeneous.iff_eq]
  exact le_antisymm hcoreP (hP.2 ⟨hcore, hle⟩ hcoreP)

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeBallFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

noncomputable section

theorem ConeBallFinite.proof (hMass : ConeIntegralMass.Statement) : ConeBallFinite.Statement := by
  intro n e h W f hW hf
  obtain ⟨δ, hδ1, hδ⟩ := hf.exists_multiHomog hW
  have hm := hMass n e δ h W f hW hf hδ
  rw [lt_top_iff_ne_top]
  intro hinf
  unfold coneIntegral at hm
  change (∫ y in coneBall h W, (1 : ℝ) ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ))) / _ =
    (δ : ℝ) at hm
  rw [setIntegral_const, measureReal_def, hinf, ENNReal.toReal_top, zero_smul, zero_div] at hm
  have hδ0 : (δ : ℝ) ≠ 0 := by exact_mod_cast (by omega : δ ≠ 0)
  exact hδ0 hm.symm

end

end GroundTheory.Heights₂.Heights
end
