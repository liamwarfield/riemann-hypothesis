module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrrParIffCuspidalProduct
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GelfandFlags.IntSmooth
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveSolutionExistence
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.RightHolRightHolEq
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwKerIffAverage

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ActEqSumOfKernel
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult

theorem act_eq_sum_of_kernel : LgFacts → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n) {ι : Type} [Fintype ι] (c : ι → ℂ) (ks : ι → Mat n → (E.V →L[ℂ] E.V)) (k : Mat n → (E.V →L[ℂ] E.V)) (f : Mat n → E.V), (∀ i, KReg (ks i)) → (∀ y ∈ GLs n, k y = ∑ i, c i • ks i y) → ContinuousOn f (GLs n) → ∀ x ∈ GLs n, act μ E k f x = ∑ i, c i • act μ E (ks i) f x := by
  intro hL n _ _ μ _ E ι _ c ks k f hks hk hf x hx
  haveI := FiniteDimensional.complete ℂ E.V
  have hval : ∀ y : G n, y.val ∈ GLs n := fun y => by
    have := (Matrix.isUnit_iff_isUnit_det _).1 y.isUnit
    exact this.ne_zero
  have hcv : Continuous (fun y : G n => y.val) := Units.continuous_val
  have hmul : ∀ y : G n, x * y.val ∈ GLs n := fun y => by
    have h1 : x.det ≠ 0 := hx
    have h2 : y.val.det ≠ 0 := hval y
    change (x * y.val).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero h1 h2
  have hint : ∀ i, Integrable (fun y : G n => ks i y.val (f (x * y.val))) μ := by
    intro i
    obtain ⟨hc, R, hR⟩ := hks i
    have hcont : Continuous (fun y : G n => ks i y.val (f (x * y.val))) := by
      have h1 : Continuous (fun y : G n => ks i y.val) :=
        hc.comp_continuous hcv hval
      have h2 : Continuous (fun y : G n => f (x * y.val)) :=
        hf.comp_continuous (continuous_const.mul hcv) hmul
      exact h1.clm_apply h2
    have hsupp : HasCompactSupport (fun y : G n => ks i y.val (f (x * y.val))) := by
      refine HasCompactSupport.intro ((hL n).2.2.2.2.1 R) ?_
      intro y hy
      have hy' : R < lg y.val := not_le.1 hy
      simp [hR y.val (hval y) hy']
    exact hcont.integrable_of_hasCompactSupport hsupp
  unfold act
  have hpt : (fun y : G n => k y.val (f (x * y.val)))
      = fun y : G n => ∑ i, c i • ks i y.val (f (x * y.val)) := by
    funext y
    rw [hk y.val (hval y)]
    simp [ContinuousLinearMap.sum_apply]
  have hi : ∀ i ∈ (Finset.univ : Finset ι),
      Integrable (fun y : G n => c i • ks i y.val (f (x * y.val))) μ :=
    fun i _ => (hint i).smul (c i)
  rw [hpt, MeasureTheory.integral_finsetSum _ hi]
  exact Finset.sum_congr rfl (fun i _ => integral_smul (c i) _)

end GlobalTheory.CompanionTheory.WaveMult
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelActionEquivariant
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelActionEquivariant
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult

theorem act_kReg_section : LgFacts → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n))
    [μ.IsHaarMeasure] (E : KMod n) (κ : Mat n → (E.V →L[ℂ] E.V)) (f : Mat n → E.V), KReg κ →
    ContinuousOn f (GLs n) →
    (∀ y ∈ GLs n, ∀ k₁ : Matrix.unitaryGroup (Fin n) ℂ, κ (k₁.1 * y) = E.ρ k₁ * κ y) →
    ContinuousOn (act μ E κ f) (GLs n) ∧
      ∀ x ∈ GLs n, ∀ k₂ : Matrix.unitaryGroup (Fin n) ℂ, act μ E κ f (x * k₂.1) = E.ρ k₂⁻¹ (act μ E κ f x) := by
  intro hL n _ _ μ _ E κ f hκ hf hleft
  obtain ⟨-, -, -, -, hcG, -, -⟩ := hL n
  obtain ⟨hkc, R, hR⟩ := hκ
  haveI : CompleteSpace E.V := FiniteDimensional.complete ℂ E.V
  have hval : ∀ y : G n, y.val ∈ GLs n := fun y => by
    have : IsUnit y.val.det := (Matrix.isUnit_iff_isUnit_det _).1 y.isUnit
    exact this.ne_zero
  have hmul : ∀ a ∈ GLs n, ∀ b ∈ GLs n, a * b ∈ GLs n := fun a ha b hb => by
    change (a * b).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero ha hb
  refine ⟨?_, fun x _ k₂ => ?_⟩
  · have hcv : Continuous (fun y : G n => y.val) := Units.continuous_val
    have h1 : ContinuousOn (fun p : Mat n × G n => κ p.2.val) (GLs n ×ˢ Set.univ) :=
      hkc.comp (hcv.comp continuous_snd).continuousOn (fun p _ => hval p.2)
    have h2 : ContinuousOn (fun p : Mat n × G n => f (p.1 * p.2.val)) (GLs n ×ˢ Set.univ) :=
      hf.comp (continuous_fst.mul (hcv.comp continuous_snd)).continuousOn
        (fun p hp => hmul _ hp.1 _ (hval _))
    have h3 : ContinuousOn (Function.uncurry fun (x : Mat n) (y : G n) => κ y.val (f (x * y.val)))
        (GLs n ×ˢ Set.univ) := h1.clm_apply h2
    exact continuousOn_integral_of_compact_support (hcG R) h3 (fun x y _ hy => by
      have : R < lg y.val := not_le.1 hy
      simp [hR _ (hval y) this])
  · have hk : k₂.1 * (k₂⁻¹).1 = 1 := congrArg Subtype.val (mul_inv_cancel k₂)
    have hk' : (k₂⁻¹).1 * k₂.1 = 1 := congrArg Subtype.val (inv_mul_cancel k₂)
    let g : G n := ⟨(k₂⁻¹).1, k₂.1, hk', hk⟩
    change ∫ y : G n, κ y.val (f (x * k₂.1 * y.val)) ∂μ = E.ρ k₂⁻¹ (∫ y : G n, κ y.val (f (x * y.val)) ∂μ)
    rw [← integral_mul_left_eq_self (fun y : G n => κ y.val (f (x * k₂.1 * y.val))) g]
    have hpt : ∀ y : G n, κ (g * y).val (f (x * k₂.1 * (g * y).val)) =
        E.ρ k₂⁻¹ (κ y.val (f (x * y.val))) := fun y => by
      have e1 : (g * y).val = (k₂⁻¹).1 * y.val := rfl
      have e2 : x * k₂.1 * ((k₂⁻¹).1 * y.val) = x * y.val := by
        rw [mul_assoc, ← mul_assoc k₂.1, hk, one_mul]
      rw [e1, e2, hleft _ (hval y) k₂⁻¹]
      rfl
    simp_rw [hpt]
    exact (E.ρ k₂⁻¹).integral_comp_comm'
      (AddMonoidHomClass.isometry_of_norm (E.ρ k₂⁻¹) (E.iso _)).antilipschitz _

end GlobalTheory.CompanionTheory.WaveMult
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelActionEquivariantStatement
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_action_equivariant : LgFacts → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n) (κ : Mat n → (E.V →L[ℂ] E.V)) (f : Mat n → E.V), KReg κ → ContinuousOn f (GLs n) → (∀ y ∈ GLs n, ∀ k₁ : Matrix.unitaryGroup (Fin n) ℂ, κ (k₁.1 * y) = E.ρ k₁ * κ y) → ContinuousOn (act μ E κ f) (GLs n) ∧ ∀ x ∈ GLs n, ∀ k₂ : Matrix.unitaryGroup (Fin n) ℂ, act μ E κ f (x * k₂.1) = E.ρ k₂⁻¹ (act μ E κ f x) := by
  first | exact @GlobalTheory.CompanionTheory.WaveMult.act_kReg_section | exact GlobalTheory.CompanionTheory.WaveMult.act_kReg_section | (intros; apply GlobalTheory.CompanionTheory.WaveMult.act_kReg_section <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubquotientEquivOfIrreducibleImage
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubquotientEquivOfIrreducibleImage
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL

namespace GlobalTheory.CompanionTheory.IsoSub

theorem nonempty_equiv_of_isotypic {A M T Q S : Type*} [Ring A] [AddCommGroup M] [Module A M]
    [AddCommGroup T] [Module A T] [AddCommGroup Q] [Module A Q] [AddCommGroup S] [Module A S]
    [IsSimpleModule A S] (h : isotypicComponent A M S = ⊤) (j : T →ₗ[A] M)
    (hj : Function.Injective j) (f : T →ₗ[A] Q) (hf : Function.Surjective f) :
    IsSimpleModule A Q → Nonempty (Q ≃ₗ[A] S) := by
  intro hQ
  have hiso : IsIsotypicOfType A M S := IsIsotypicOfType.of_isotypicComponent_eq_top h
  have hss : IsSemisimpleModule A M := by
    refine IsSemisimpleModule.of_sSup_simples_eq_top (top_le_iff.1 ?_)
    rw [← h]
    exact sSup_le_sSup fun m (hm : Nonempty (m ≃ₗ[A] S)) => IsSimpleModule.congr hm.some
  have hT : IsSemisimpleModule A T := IsSemisimpleModule.of_injective j hj
  obtain ⟨C, hC⟩ := exists_isCompl (LinearMap.ker f)
  let e₁ : C ≃ₗ[A] Q :=
    (Submodule.quotientEquivOfIsCompl _ _ hC).symm.trans (f.quotKerEquivOfSurjective hf)
  have hC' : IsSimpleModule A C := IsSimpleModule.congr e₁
  let e₂ : C ≃ₗ[A] C.map j := Submodule.equivMapOfInjective j hj C
  have hCj : IsSimpleModule A (C.map j) := IsSimpleModule.congr e₂.symm
  obtain ⟨e₃⟩ := hiso (C.map j)
  exact ⟨e₁.symm.trans (e₂.trans e₃)⟩

def inclusion {G Y : Type} [Group G] [AddCommGroup Y] [Module ℂ Y] {R : Representation ℂ G Y}
    (S : Subrepresentation R) : S.toRepresentation.IntertwiningMap R :=
  ⟨S.toSubmodule.subtype, fun _ => rfl⟩

theorem equiv_of_isSubquotient (G : Type) [Group G] (V Y W : Type) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup Y] [Module ℂ Y] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (R : Representation ℂ G Y) (σ : Representation ℂ G W)
    (hρ : ρ.IsIrreducible) (hσ : σ.IsIrreducible)
    (hR : ⨆ f : ρ.IntertwiningMap R, LinearMap.range f.toLinearMap = ⊤)
    (hsq : IsSubquotient σ R) : Nonempty (σ.Equiv ρ) := by
  have hρs : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule ρ).1 hρ
  have hσs : IsSimpleModule (MonoidAlgebra ℂ G) σ.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule σ).1 hσ
  have htop : Subrepresentation.asSubmodule (GlobalTheory.CuspFactor.spanRep R ρ) = ⊤ := by
    have hX : (GlobalTheory.CuspFactor.spanRep R ρ).toSubmodule = ⊤ := hR
    apply SetLike.coe_injective
    show ((GlobalTheory.CuspFactor.spanRep R ρ).toSubmodule : Set Y) = Set.univ
    rw [hX]
    first
      | rfl
      | exact Submodule.top_coe
      | simp
  have h : isotypicComponent (MonoidAlgebra ℂ G) R.asModule ρ.asModule = ⊤ := by
    rw [← GlobalTheory.CuspFactor.spanRep_asSubmodule R ρ hρ]
    exact htop
  obtain ⟨S, f, hf⟩ := hsq
  let j := Representation.IntertwiningMap.equivLinearMapAsModule _ _
    (GlobalTheory.CompanionTheory.IsoSub.inclusion S)
  have hj : Function.Injective j := by
    first
      | exact Subtype.val_injective
      | (intro x y hxy; exact Subtype.val_injective hxy)
  let f' := Representation.IntertwiningMap.equivLinearMapAsModule _ _ f
  have hf' : Function.Surjective f' := by
    first
      | exact hf
      | (intro y; obtain ⟨x, hx⟩ := hf y; exact ⟨x, hx⟩)
  exact (GlobalTheory.CuspFactor.nonempty_equiv_iff σ ρ).2
    (GlobalTheory.CompanionTheory.IsoSub.nonempty_equiv_of_isotypic h j hj f' hf' hσs)

end GlobalTheory.CompanionTheory.IsoSub
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubquotientEquivOfIrreducibleImageStatement
open GlobalTheory.PRep GlobalTheory.SmGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subquotient_equiv_of_irreducible_image : ∀ (G : Type) [Group G] (V Y W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup Y] [Module ℂ Y] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (R : Representation ℂ G Y) (σ : Representation ℂ G W), ρ.IsIrreducible → σ.IsIrreducible →
    (⨆ f : ρ.IntertwiningMap R, LinearMap.range f.toLinearMap = ⊤) → IsSubquotient σ R → Nonempty (σ.Equiv ρ) := by
  first | exact @GlobalTheory.CompanionTheory.IsoSub.equiv_of_isSubquotient | exact GlobalTheory.CompanionTheory.IsoSub.equiv_of_isSubquotient | (intros; apply GlobalTheory.CompanionTheory.IsoSub.equiv_of_isSubquotient <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LengthFunctionCompact
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LengthFunctionCompact
noncomputable section

open Matrix Finset

namespace GlobalTheory.CompanionTheory.LgBound

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem lgCpt : PositivityTheory.RgBcC.VC.LgCpt := by
  intro n R
  haveI : ProperSpace (Mat n) := FiniteDimensional.proper ℂ _
  let f : G n → ℝ := fun y => 1 + ∑ a, ∑ b, (‖y.val a b‖ ^ 2 + ‖(y⁻¹).val a b‖ ^ 2)
  have hinv : ∀ y : G n, (y.val)⁻¹ = (y⁻¹).val := fun y => (Matrix.coe_units_inv y).symm
  have hc1 : Continuous fun y : G n => y.val := Units.continuous_val
  have hc2 : Continuous fun y : G n => (y⁻¹).val := Units.continuous_val.comp continuous_inv
  have hfc : Continuous f := by
    refine continuous_const.add (continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => ?_)
    exact ((hc1.matrix_elem a b).norm.pow 2).add ((hc2.matrix_elem a b).norm.pow 2)
  have hsum : ∀ y : G n, 0 ≤ ∑ a, ∑ b, (‖y.val a b‖ ^ 2 + ‖(y⁻¹).val a b‖ ^ 2) := fun y =>
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => by positivity
  have hfpos : ∀ y, 0 < f y := fun y => by
    have := hsum y
    show 0 < 1 + _
    linarith
  have hS : {y : G n | lg y.val ≤ R} = f ⁻¹' Set.Iic (Real.exp R) := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Iic, lg, hinv]
    exact Real.log_le_iff_le_exp (hfpos y)
  rw [hS]
  have hclosed : IsClosed (f ⁻¹' Set.Iic (Real.exp R)) := isClosed_Iic.preimage hfc

  set r : ℝ := Real.exp R with hr
  have hr0 : 0 ≤ r + 1 := by positivity
  have hterm : ∀ y : G n, f y ≤ r → ∀ a b, ‖y.val a b‖ ^ 2 + ‖(y⁻¹).val a b‖ ^ 2 ≤ r := by
    intro y hy a b
    have h1 : ‖y.val a b‖ ^ 2 + ‖(y⁻¹).val a b‖ ^ 2 ≤ ∑ b, (‖y.val a b‖ ^ 2 + ‖(y⁻¹).val a b‖ ^ 2) :=
      Finset.single_le_sum (f := fun b => ‖y.val a b‖ ^ 2 + ‖(y⁻¹).val a b‖ ^ 2)
        (fun b _ => by positivity) (Finset.mem_univ b)
    have h2 : ∑ b, (‖y.val a b‖ ^ 2 + ‖(y⁻¹).val a b‖ ^ 2) ≤ ∑ a, ∑ b, (‖y.val a b‖ ^ 2 + ‖(y⁻¹).val a b‖ ^ 2) :=
      Finset.single_le_sum (f := fun a => ∑ b, (‖y.val a b‖ ^ 2 + ‖(y⁻¹).val a b‖ ^ 2))
        (fun a _ => Finset.sum_nonneg fun b _ => by positivity) (Finset.mem_univ a)
    have h3 : 1 + ∑ a, ∑ b, (‖y.val a b‖ ^ 2 + ‖(y⁻¹).val a b‖ ^ 2) ≤ r := hy
    linarith
  have hle : ∀ t : ℝ, 0 ≤ t → t ^ 2 ≤ r → t ≤ r + 1 := by
    intro t ht h
    nlinarith [sq_nonneg (t - 1)]
  have hb1 : ∀ y : G n, f y ≤ r → ‖y.val‖ ≤ r + 1 := by
    intro y hy
    refine (Matrix.norm_le_iff hr0).2 fun a b => hle _ (norm_nonneg _) ?_
    have := hterm y hy a b
    have h2 : 0 ≤ ‖(y⁻¹).val a b‖ ^ 2 := by positivity
    linarith
  have hb2 : ∀ y : G n, f y ≤ r → ‖(y⁻¹).val‖ ≤ r + 1 := by
    intro y hy
    refine (Matrix.norm_le_iff hr0).2 fun a b => hle _ (norm_nonneg _) ?_
    have := hterm y hy a b
    have h2 : 0 ≤ ‖y.val a b‖ ^ 2 := by positivity
    linarith
  have hball : IsCompact (Metric.closedBall (0 : Mat n) (r + 1)) := isCompact_closedBall _ _
  have hK : IsCompact ((fun p : Mat n × Mat n => (p.1, MulOpposite.op p.2)) ''
      (Metric.closedBall (0 : Mat n) (r + 1) ×ˢ Metric.closedBall (0 : Mat n) (r + 1))) :=
    (hball.prod hball).image (continuous_fst.prodMk (MulOpposite.continuous_op.comp continuous_snd))
  have hpre := (Units.isClosedEmbedding_embedProduct (α := Mat n)).isCompact_preimage hK
  refine hpre.of_isClosed_subset hclosed ?_
  intro y hy
  refine ⟨(y.val, (y⁻¹).val), ⟨?_, ?_⟩, rfl⟩
  · simpa using hb1 y hy
  · simpa using hb2 y hy

end GlobalTheory.CompanionTheory.LgBound
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LengthFunctionCompactStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.length_function_compact : PositivityTheory.RgBcC.VC.LgCpt := by
  first | exact @GlobalTheory.CompanionTheory.LgBound.lgCpt | exact GlobalTheory.CompanionTheory.LgBound.lgCpt | (intros; apply GlobalTheory.CompanionTheory.LgBound.lgCpt <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosureOperatorFacts
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosureOperatorFacts
noncomputable section

open MeasureTheory Matrix Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.FcCls

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} [MeasurableSpace (G n)]

theorem val_mem_GLs (y : G n) : y.val ∈ GLs n := by
  show Matrix.det y.val ≠ 0
  exact (Matrix.isUnits_det_units y).ne_zero

theorem cls_eq_toLp (μ : Measure (G n)) {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {f : Mat n → V} (hf : MemLp (fun y : G n => f y.val) 2 μ) : cls μ f = hf.toLp _ := by
  rw [cls, dite_eq_left hf]

theorem continuous_lift {V : Type} [TopologicalSpace V] {f : Mat n → V}
    (hf : ContinuousOn f (GLs n)) : Continuous (fun y : G n => f y.val) := by
  exact hf.comp_continuous Units.continuous_val (fun y => val_mem_GLs y)

theorem cls_congr (μ : Measure (G n)) {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {f f' : Mat n → V} (h : ∀ g ∈ GLs n, f g = f' g) : cls μ f = cls μ f' := by
  have hff : (fun y : G n => f y.val) = fun y => f' y.val := funext fun y => h _ (val_mem_GLs y)
  unfold cls
  rw [hff]

theorem cls_unique [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] {V : Type}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] {f f' : Mat n → V}
    (hc : ContinuousOn f (GLs n)) (hc' : ContinuousOn f' (GLs n))
    (hf : MemLp (fun y : G n => f y.val) 2 μ) (hf' : MemLp (fun y : G n => f' y.val) 2 μ)
    (h : cls μ f = cls μ f') : ∀ g ∈ GLs n, f g = f' g := by
  intro g hg
  rw [cls_eq_toLp (f := f) μ hf, cls_eq_toLp (f := f') μ hf'] at h
  have h1 := (MemLp.toLp_eq_toLp_iff hf hf').1 h
  have h2 := (Continuous.ae_eq_iff_eq μ (continuous_lift hc) (continuous_lift hc')).1 h1
  have hu : IsUnit (Matrix.det g) := isUnit_iff_ne_zero.2 hg
  exact congrFun h2 (Matrix.nonsingInvUnit g hu)

theorem cls_add_smul (μ : Measure (G n)) {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (a : ℂ) {f f' : Mat n → V} (hf : MemLp (fun y : G n => f y.val) 2 μ)
    (hf' : MemLp (fun y : G n => f' y.val) 2 μ) : cls μ (a • f + f') = a • cls μ f + cls μ f' := by
  have hs : MemLp (fun y : G n => (a • f + f') y.val) 2 μ := (hf.const_smul a).add hf'
  rw [cls_eq_toLp (f := a • f + f') μ hs, cls_eq_toLp (f := f) μ hf, cls_eq_toLp (f := f') μ hf',
    ← MemLp.toLp_const_smul, ← MemLp.toLp_add]
  rfl

theorem rR_cls [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] {V : Type}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] (hU : Unimod) (h : G n) {f : Mat n → V}
    (hf : MemLp (fun y : G n => f y.val) 2 μ) :
    rR μ V h (cls μ f) = cls μ (fun y => f (y * h.val)) := by
  have hmp : MeasurePreserving (fun y : G n => y * h) μ μ := by
    have := (hU n μ).1
    exact measurePreserving_mul_right μ h
  rw [cls_eq_toLp (f := f) μ hf,
    cls_eq_toLp (f := fun y => f (y * h.val)) μ (hf.comp_measurePreserving hmp)]
  unfold rR
  rw [dite_eq_left hmp]
  exact Lp.toLp_compMeasurePreserving hf hmp

theorem compLpL_cls (μ : Measure (G n)) {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : V →L[ℂ] V) {f : Mat n → V} (hf : MemLp (fun y : G n => f y.val) 2 μ) :
    A.compLpL 2 μ (cls μ f) = cls μ (fun y => A (f y)) := by
  have hA : MemLp (fun y : G n => A (f y.val)) 2 μ := A.comp_memLp' hf
  rw [cls_eq_toLp (f := f) μ hf, cls_eq_toLp (f := fun y => A (f y)) μ hA]
  apply Lp.ext
  filter_upwards [A.coeFn_compLpL (p := 2) (μ := μ) (hf.toLp _), MemLp.coeFn_toLp hf, MemLp.coeFn_toLp hA]
    with y h1 h2 h3
  rw [h1, h2, h3]

theorem clsFacts : ClsFacts := by
  intro n _ _ μ _ V _ _ hU
  exact ⟨fun f f' hc hc' hf hf' h => cls_unique μ hc hc' hf hf' h,
    fun a f f' hf hf' => cls_add_smul μ a hf hf',
    fun f f' h => cls_congr μ h,
    fun h f hf => rR_cls μ hU h hf,
    fun A f hf => compLpL_cls μ A hf⟩

end GlobalTheory.CompanionTheory.FcCls
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosureOperatorFactsStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closure_operator_facts : PositivityTheory.RgBcC.Fc.ClsFacts := by
  first | exact @GlobalTheory.CompanionTheory.FcCls.clsFacts | exact GlobalTheory.CompanionTheory.FcCls.clsFacts | (intros; apply GlobalTheory.CompanionTheory.FcCls.clsFacts <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableG
noncomputable section

open MeasureTheory Matrix Filter Topology
open scoped ContDiff
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveK GlobalTheory.CompanionTheory

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveK.Word

variable {n : ℕ}

section Defs

variable {L : Type} [NormedAddCommGroup L] [NormedSpace ℂ L]

structure Cl (K : Mat n → Mat n → L) : Prop where
  smooth : ContDiffOn ℝ ∞ (Function.uncurry K) (GLs n ×ˢ GLs n)
  supp : ∃ R, ∀ x ∈ GLs n, ∀ y ∈ GLs n, R + lg x < lg y → K x y = 0

def kK (k : Mat n → L) : Mat n → Mat n → L := fun x y => k (x⁻¹ * y)

def Iop {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [MeasurableSpace (G n)] (μ : Measure (G n))
    (K : Mat n → Mat n → (V →L[ℂ] V)) (φ : Mat n → V) : Mat n → V :=
  fun x => ∫ y : G n, K x y.val (φ y.val) ∂μ

end Defs

section ClB
variable {L : Type} [NormedAddCommGroup L] [NormedSpace ℂ L]

end ClB

section Lem
variable {L : Type} [NormedAddCommGroup L] [NormedSpace ℂ L]

theorem contDiff_ent (a b : Fin n) : ContDiff ℝ ∞ (fun y : Mat n => y a b) :=
  (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ a b)).contDiff

theorem contDiffOn_invMul : ContDiffOn ℝ ∞ (fun p : Mat n × Mat n => p.1⁻¹ * p.2) (GLs n ×ˢ GLs n) := by
  have hinv : ContDiffOn ℝ ∞ (fun p : Mat n × Mat n => p.1⁻¹) (GLs n ×ˢ GLs n) :=
    (ReciprocityTheory.ChartRestriction.DS.Lap.LemK.contDiffOn_inv_det_ne_zero.restrict_scalars ℝ).comp (f := Prod.fst) contDiff_fst.contDiffOn
      fun p hp => hp.1
  refine contDiffOn_pi.2 fun a => contDiffOn_pi.2 fun b => ?_
  simp only [Matrix.mul_apply]
  refine ContDiffOn.sum fun c _ => ContDiffOn.mul ?_ ?_
  · exact (contDiff_ent a c).comp_contDiffOn hinv
  · exact ((contDiff_ent c b).comp contDiff_snd).contDiffOn

theorem cl_kK (hL : LgFacts) {k : Mat n → L} (hk : ContDiffOn ℝ ∞ k (GLs n)) {R : ℝ}
    (hR : ∀ y ∈ GLs n, R < lg y → k y = 0) : Cl (kK k) := by
  refine ⟨hk.comp contDiffOn_invMul fun p hp => GlobalTheory.CompanionTheory.WaveAll.mul_mem_GLs (GlobalTheory.CompanionTheory.WaveMult.inv_mem_GLs hp.1) hp.2,
    R, fun x hx y hy hl => ?_⟩
  have hz := GlobalTheory.CompanionTheory.WaveAll.mul_mem_GLs (GlobalTheory.CompanionTheory.WaveMult.inv_mem_GLs hx) hy
  refine hR _ hz ?_
  have h := (hL n).1 x hx _ hz
  rw [Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_iff_ne_zero.2 hx)] at h
  linarith

end Lem

section Lem2
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]

end Lem2

section Lem3
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]

end Lem3

section Basic
variable {L : Type} [NormedAddCommGroup L] [NormedSpace ℂ L]

end Basic

section Pairs

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]

variable {μ} {φ : Mat n → V}

theorem act_eq_Iop (E : KMod n) (k : Mat n → (E.V →L[ℂ] E.V)) (f : Mat n → E.V) {x : Mat n} (hx : x ∈ GLs n) :
    act μ E k f x = Iop μ (kK k) f x := by
  let xG : G n := Matrix.GeneralLinearGroup.mkOfDetNeZero x hx
  have hv : xG.val = x := rfl
  have hdet : IsUnit x.det := isUnit_iff_ne_zero.2 hx
  have h := integral_mul_left_eq_self (μ := μ) (fun y : G n => k (x⁻¹ * y.val) (f y.val)) xG
  simp only [Iop, kK, act]
  rw [← h]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  simp only [Units.val_mul, hv, Matrix.nonsing_inv_mul_cancel_left _ _ hdet]

end Pairs

end GlobalTheory.CompanionTheory.WaveK.Word
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PositiveConeIsOpen
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PositiveConeIsOpen
noncomputable section

open MeasureTheory Matrix Topology Filter
open scoped ContDiff ENNReal ComplexOrder Pointwise

open PositivityTheory.RgTw (Mat G hb)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.ConeHaar

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ConeHaar.OpenCone

variable {n : ℕ}

theorem hOf_herm (v : Fin n × Fin n → ℝ) : (hOf v).IsHermitian := by
  show (hOf v)ᴴ = hOf v
  simp [hOf, conjTranspose_sum, conjTranspose_smul, GlobalTheory.CompanionTheory.TwistHomotopy.hb_conjTranspose]

theorem im_form {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.IsHermitian) (x : Fin n → ℂ) :
    (star x ⬝ᵥ M *ᵥ x).im = 0 := by
  have h : star (star x ⬝ᵥ M *ᵥ x) = star x ⬝ᵥ M *ᵥ x := by
    conv_rhs => rw [Matrix.star_dotProduct]
    rw [Matrix.star_mulVec, hM.eq, ← Matrix.dotProduct_mulVec]
  exact Complex.conj_eq_iff_im.mp h

theorem continuous_form :
    Continuous fun z : (Fin n × Fin n → ℝ) × (Fin n → ℂ) => (star z.2 ⬝ᵥ hOf z.1 *ᵥ z.2).re := by
  have hent : ∀ i j : Fin n, Continuous fun v : Fin n × Fin n → ℝ => hOf v i j := by
    intro i j
    have : (fun v : Fin n × Fin n → ℝ => hOf v i j) = fun v => ∑ p, (v p : ℂ) * hb p i j := by
      funext v
      simp [hOf, Matrix.sum_apply]
    rw [this]
    fun_prop
  have hent' : ∀ i j : Fin n,
      Continuous fun z : (Fin n × Fin n → ℝ) × (Fin n → ℂ) => hOf z.1 i j :=
    fun i j => (hent i j).comp continuous_fst
  simp only [dotProduct, mulVec, Pi.star_apply]
  refine Complex.continuous_re.comp ?_
  refine continuous_finsetSum _ fun i _ => ?_
  refine (continuous_star.comp ((continuous_apply i).comp continuous_snd)).mul ?_
  refine continuous_finsetSum _ fun j _ => ?_
  exact (hent' i j).mul ((continuous_apply j).comp continuous_snd)

theorem posDef_of_sphere {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.IsHermitian)
    (h : ∀ x ∈ Metric.sphere (0 : Fin n → ℂ) 1, 0 < (star x ⬝ᵥ M *ᵥ x).re) : M.PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.2 ⟨hM, fun x hx => ?_⟩
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  have hy : ((‖x‖⁻¹ : ℝ) : ℂ) • x ∈ Metric.sphere (0 : Fin n → ℂ) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul]
    simp [hn]
  have h1 := h _ hy
  have h2 : star (((‖x‖⁻¹ : ℝ) : ℂ) • x) ⬝ᵥ M *ᵥ (((‖x‖⁻¹ : ℝ) : ℂ) • x) =
      (((‖x‖⁻¹ ^ 2 : ℝ)) : ℂ) * (star x ⬝ᵥ M *ᵥ x) := by
    rw [star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct]
    simp [smul_eq_mul, pow_two]
    ring
  rw [h2, Complex.re_ofReal_mul] at h1
  have h3 : 0 < (star x ⬝ᵥ M *ᵥ x).re := by
    have : 0 < ‖x‖⁻¹ ^ 2 := by positivity
    exact (pos_iff_pos_of_mul_pos h1).1 this
  exact Complex.pos_iff.2 ⟨h3, (im_form hM x).symm⟩

end GlobalTheory.CompanionTheory.ConeHaar.OpenCone

namespace GlobalTheory.CompanionTheory.ConeHaar

open OpenCone

theorem isOpen_cone : ∀ n : ℕ, IsOpen (PositivityTheory.RgBcC.cone n) := by
  intro n
  rw [isOpen_iff_eventually]
  intro v hv
  have hpos : ∀ x ∈ Metric.sphere (0 : Fin n → ℂ) 1, 0 < (star x ⬝ᵥ hOf v *ᵥ x).re := by
    intro x hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp at hx
    have := (Matrix.posDef_iff_dotProduct_mulVec.1 hv).2 hx0
    exact (Complex.pos_iff.1 this).1
  have hev : ∀ᶠ w in 𝓝 v, ∀ x ∈ Metric.sphere (0 : Fin n → ℂ) 1,
      0 < (star x ⬝ᵥ hOf w *ᵥ x).re :=
    (isCompact_sphere (0 : Fin n → ℂ) 1).eventually_forall_of_forall_eventually fun x hx =>
      (continuous_form.continuousAt (x := (v, x))).eventually (lt_mem_nhds (hpos x hx))
  exact hev.mono fun w hw => posDef_of_sphere (hOf_herm w) hw

end GlobalTheory.CompanionTheory.ConeHaar
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PositiveConeIsOpenStatement
open MeasureTheory Matrix Topology Filter
open scoped ContDiff ENNReal ComplexOrder Pointwise
open PositivityTheory.RgTw (Mat G hb)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.ConeHaar
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.positive_cone_isOpen : ∀ n : ℕ, IsOpen (PositivityTheory.RgBcC.cone n) := by
  first | exact @GlobalTheory.CompanionTheory.ConeHaar.isOpen_cone | exact GlobalTheory.CompanionTheory.ConeHaar.isOpen_cone | (intros; apply GlobalTheory.CompanionTheory.ConeHaar.isOpen_cone <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CasimirOperatorFormula
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CasimirOperatorFormula
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.Casimir

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open PositivityTheory.RgBcC.Fc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem isOpen_GLs : IsOpen (GLs n) := by
  have hc : Continuous (fun g : Mat n => g.det) := Continuous.matrix_det continuous_id
  exact (isOpen_compl_singleton (x := (0 : ℂ))).preimage hc

theorem contDiff_mul_right (X : Mat n) : ContDiff ℝ ∞ (fun g : Mat n => g * X) :=
  ((LinearMap.mulRight ℝ X).toContinuousLinearMap).contDiff

theorem differentiableAt_Rd {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (X : Mat n) {g : Mat n}
    (hg : g ∈ GLs n) : DifferentiableAt ℝ (Rd X f) g := by
  have h1 := hf.fderiv_of_isOpen (m := 1) isOpen_GLs (by norm_cast)
  have h2 : ContDiffOn ℝ 1 (Rd X f) (GLs n) :=
    h1.clm_apply ((contDiff_mul_right X).contDiffOn.of_le (by norm_cast))
  exact (h2.contDiffAt (isOpen_GLs.mem_nhds hg)).differentiableAt (by norm_num)

theorem Rd_zero (X : Mat n) : Rd X (0 : Mat n → V) = 0 := by
  funext g
  have : fderiv ℝ (0 : Mat n → V) g = 0 := by
    simpa using fderiv_const_apply (𝕜 := ℝ) (x := g) (0 : V)
  simp [Rd, this]

theorem Eu_zero (s : Bool) (a b : Fin n) : Eu s a b (0 : Mat n → V) = 0 := by
  simp [Eu, Rd_zero]

theorem Epow_one (s : Bool) (c a : Fin n) (f : Mat n → V) : Epow s 1 c a f = Eu s c a f := by
  simp only [Epow]
  rw [Finset.sum_eq_single a]
  · simp
  · intro d _ hd
    simp [hd, Eu_zero]
  · simp

theorem Rd_comb (X : Mat n) (σ : ℂ) {u v : Mat n → V} {g : Mat n} (hu : DifferentiableAt ℝ u g)
    (hv : DifferentiableAt ℝ v g) :
    Rd X ((1 / 2 : ℂ) • (u + σ • v)) g = (1 / 2 : ℂ) • (Rd X u g + σ • Rd X v g) := by
  have hsv : DifferentiableAt ℝ (σ • v) g := hv.const_smul σ
  have h1 : fderiv ℝ ((1 / 2 : ℂ) • (u + σ • v)) g = (1 / 2 : ℂ) • fderiv ℝ (u + σ • v) g :=
    fderiv_const_smul (hu.add hsv) _
  have h2 : fderiv ℝ (u + σ • v) g = fderiv ℝ u g + fderiv ℝ (σ • v) g := fderiv_add hu hsv
  have h3 : fderiv ℝ (σ • v) g = σ • fderiv ℝ v g := fderiv_const_smul hv _
  show fderiv ℝ ((1 / 2 : ℂ) • (u + σ • v)) g (g * X) = _
  rw [h1, h2, h3]
  rfl

theorem comb_identity (P B C Q : V) :
    (2 : ℂ) • ((1 / 2 : ℂ) • ((1 / 2 : ℂ) • (P + (-Complex.I) • B) +
          (-Complex.I) • ((1 / 2 : ℂ) • (C + (-Complex.I) • Q))) +
        (1 / 2 : ℂ) • ((1 / 2 : ℂ) • (P + Complex.I • B) +
          Complex.I • ((1 / 2 : ℂ) • (C + Complex.I • Q)))) = P - Q := by
  match_scalars <;> ring_nf <;> simp [Complex.I_sq] <;> ring

theorem Eu_Eu {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (s : Bool) (a c : Fin n) {g : Mat n}
    (hg : g ∈ GLs n) :
    Eu s a c (Eu s c a f) g =
      (1 / 2 : ℂ) • ((1 / 2 : ℂ) • (Rd (Matrix.single a c 1) (Rd (Matrix.single c a 1) f) g +
            (if s then -Complex.I else Complex.I) •
              Rd (Matrix.single a c 1) (Rd (Matrix.single c a Complex.I) f) g) +
        (if s then -Complex.I else Complex.I) •
          ((1 / 2 : ℂ) • (Rd (Matrix.single a c Complex.I) (Rd (Matrix.single c a 1) f) g +
            (if s then -Complex.I else Complex.I) •
              Rd (Matrix.single a c Complex.I) (Rd (Matrix.single c a Complex.I) f) g))) := by
  have hu := differentiableAt_Rd hf (Matrix.single c a (1 : ℂ)) hg
  have hv := differentiableAt_Rd hf (Matrix.single c a Complex.I) hg
  have e := fun X : Mat n => Rd_comb X (if s then -Complex.I else Complex.I) hu hv
  show ((1 / 2 : ℂ) • (Rd (Matrix.single a c 1) (Eu s c a f) +
    (if s then -Complex.I else Complex.I) • Rd (Matrix.single a c Complex.I) (Eu s c a f))) g = _
  simp only [Pi.smul_apply, Pi.add_apply]
  have e' : ∀ X : Mat n, Rd X (Eu s c a f) g = _ := e
  rw [e', e']

theorem omFormula : OmFormula := by
  intro n V _ _ f hf g hg
  have hgel : ∀ s : Bool, gel s 2 f g = ∑ a, ∑ c, Eu s a c (Eu s c a f) g := by
    intro s
    simp only [gel, Finset.sum_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    have h2 : Epow s 2 a a f = ∑ c, Eu s a c (Epow s 1 c a f) := rfl
    simp only [h2, Finset.sum_apply, Epow_one]
  simp only [Om, Pi.smul_apply, Pi.add_apply, hgel]
  rw [← Finset.sum_add_distrib, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib, Finset.smul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Eu_Eu hf true a c hg, Eu_Eu hf false a c hg]
  have key := comb_identity (V := V)
    (Rd (Matrix.single a c 1) (Rd (Matrix.single c a 1) f) g)
    (Rd (Matrix.single a c 1) (Rd (Matrix.single c a Complex.I) f) g)
    (Rd (Matrix.single a c Complex.I) (Rd (Matrix.single c a 1) f) g)
    (Rd (Matrix.single a c Complex.I) (Rd (Matrix.single c a Complex.I) f) g)
  simp only [↓reduceIte, Bool.false_eq_true]
  exact key

end GlobalTheory.CompanionTheory.Casimir
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CasimirOperatorFormulaStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.casimir_operator_formula : PositivityTheory.RgBcC.Fc.OmFormula := by
  first | exact @GlobalTheory.CompanionTheory.Casimir.omFormula | exact GlobalTheory.CompanionTheory.Casimir.omFormula | (intros; apply GlobalTheory.CompanionTheory.Casimir.omFormula <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BumpConvolutionSupport
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BumpConvolutionSupport
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult

theorem hasCompactSupport_of_isBump {g : ℝ → ℝ} {T : ℝ} (hg : IsBump g T) : HasCompactSupport g := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) T) fun x hx => hg.2.2 x ?_
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, not_le] at hx
  exact hx

theorem isBump_gconv : ∀ (g g' : ℝ → ℝ) (T T' : ℝ), IsBump g T → IsBump g' T' → IsBump (gconv g g') (T + T') := by
  intro g g' T T' hg hg'
  refine ⟨?_, ?_, ?_⟩
  · have hconv : gconv g g' = MeasureTheory.convolution g g' (ContinuousLinearMap.mul ℝ ℝ) volume := by
      funext r
      simp [gconv, MeasureTheory.convolution]
    rw [hconv]
    exact (hasCompactSupport_of_isBump hg').contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
      hg.1.continuous.locallyIntegrable hg'.1
  · intro r
    unfold gconv
    calc ∫ t, g t * g' (-r - t) = ∫ t, g (-t) * g' (-r - -t) := (integral_neg_eq_self _ _).symm
      _ = ∫ t, g t * g' (r - t) := by
        congr 1
        funext t
        rw [hg.2.1 t, show -r - -t = -(r - t) by ring, hg'.2.1]
  · intro r hr
    have hzero : ∀ t, g t * g' (r - t) = 0 := by
      intro t
      by_cases ht : T < |t|
      · rw [hg.2.2 t ht, zero_mul]
      · rw [hg'.2.2 (r - t) ?_, mul_zero]
        have h1 := abs_sub_abs_le_abs_sub r t
        have ht' := not_lt.mp ht
        linarith
    simp [gconv, hzero]

end GlobalTheory.CompanionTheory.WaveMult
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BumpConvolutionSupportStatement
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bump_convolution_support : ∀ (g g' : ℝ → ℝ) (T T' : ℝ), IsBump g T → IsBump g' T' → IsBump (gconv g g') (T + T') := by
  first | exact @GlobalTheory.CompanionTheory.WaveMult.isBump_gconv | exact GlobalTheory.CompanionTheory.WaveMult.isBump_gconv | (intros; apply GlobalTheory.CompanionTheory.WaveMult.isBump_gconv <;> assumption)
end
end
