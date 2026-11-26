module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ConstantCoeffDpolyOfAdditiveTaylorPts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAffineCurveTateTwistCohomologyTwoSubsingleStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HigherDegreeClassDiesOnFinerEtaleNeighbourhood
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DpExpEqSumRangeOfVanish
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousIdeleCharLocalFactorization

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationPreimageValueRules
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationPreimageValueRules
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CechPer

theorem ex_add_lattice {A : Over (Sp ℂ)} [GrpObj A] {g : ℕ} {L : LB A.left} (u : HolUnif A L g) (l : u.Λ) (z : Fin g → ℂ) :
    u.ex (z + l) = u.ex z := by
  rw [u.ex_add, (u.ker l).2 l.2, _root_.mul_one]

theorem pre_val_rules : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), (∀ U, IsOpen (pre u.ex U)) ∧ (∀ U b, DifferentiableOn ℂ (val u.ex U b) (pre u.ex U)) ∧ (∀ U (l : u.Λ) (z : Fin g → ℂ), z + l ∈ pre u.ex U ↔ z ∈ pre u.ex U) ∧ (∀ U b (l : u.Λ) (z : Fin g → ℂ), val u.ex U b (z + l) = val u.ex U b z) ∧ (∀ U V, pre u.ex (U ⊓ V) = pre u.ex U ∩ pre u.ex V) ∧ (∀ U V, V ≤ U → pre u.ex V ⊆ pre u.ex U) ∧ (∀ (K : Type) (W : K → A.left.Opens) z, z ∈ pre u.ex (⨆ i, W i) ↔ ∃ i, z ∈ pre u.ex (W i)) ∧ (∀ U z, z ∈ pre u.ex U → ∃ W : A.left.affineOpens, W.1 ≤ U ∧ z ∈ pre u.ex W.1) ∧ (∀ U V (h : V ≤ U) (b : Sec (str A) U), ∀ z ∈ pre u.ex V, val u.ex V (Sec.res (str A) h b) z = val u.ex U b z) ∧ (∀ U, ∀ z ∈ pre u.ex U, ∃ e : Sec (str A) U →ₐ[ℂ] ℂ, ∀ b, val u.ex U b z = e b) ∧ (∀ U b z, z ∈ pre u.ex (A.left.basicOpen b) ↔ val u.ex U b z ≠ 0) ∧ ∀ z, z ∈ pre u.ex ⊤ := by
  intro A _ g L u
  refine ⟨fun U ↦ (u.hol U 0).1, fun U b ↦ (u.hol U b).2, fun U l z ↦ ?_, fun U b l z ↦ ?_, fun U V ↦ ?_,
    fun U V h z hz ↦ top_le_preimage_mono _ h hz, fun K W z ↦ ?_, fun U z hz ↦ ?_,
    fun U V h b z hz ↦ valAt'_map (u.ex z).left (homOfLE h).op b hz, fun U z hz ↦ ?_,
    fun U b z ↦ top_le_preimage_basicOpen_iff _ U b, fun z ↦ le_top (α := (Sp ℂ).Opens)⟩
  · simp only [pre, Set.mem_setOf_eq, ex_add_lattice]
  · simp only [val, ex_add_lattice]
  · ext z
    exact top_le_preimage_inf _ U V
  · refine (top_le_preimage_iff_mem (u.ex z).left _).trans (TopologicalSpace.Opens.mem_iSup.trans ?_)
    exact exists_congr fun i ↦ (top_le_preimage_iff_mem (u.ex z).left _).symm
  · have h1 := (top_le_preimage_iff_mem (u.ex z).left _).1 hz
    obtain ⟨W, hW, h2, h3⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 A.left.isBasis_affineOpens) h1
    exact ⟨⟨W, hW⟩, h3, (top_le_preimage_iff_mem (u.ex z).left _).2 h2⟩
  · refine ⟨{ toRingHom := valAtHom (u.ex z).left U hz, commutes' := fun a ↦ ?_ }, fun b ↦ valAt'_eq_valAtHom _ hz b⟩
    refine (valAt'_eq_valAtHom (u.ex z).left hz _).symm.trans ?_
    refine valAt'_constFn (u.ex z).left (str A) ?_ U a hz
    exact (congrArg _ (Category.comp_id _)).trans (Over.w (u.ex z))

end GlobalTheory.CechPer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationPreimageValueRulesStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisation_preimage_value_rules : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), (∀ U, IsOpen (pre u.ex U)) ∧ (∀ U b, DifferentiableOn ℂ (val u.ex U b) (pre u.ex U)) ∧ (∀ U (l : u.Λ) (z : Fin g → ℂ), z + l ∈ pre u.ex U ↔ z ∈ pre u.ex U) ∧ (∀ U b (l : u.Λ) (z : Fin g → ℂ), val u.ex U b (z + l) = val u.ex U b z) ∧ (∀ U V, pre u.ex (U ⊓ V) = pre u.ex U ∩ pre u.ex V) ∧ (∀ U V, V ≤ U → pre u.ex V ⊆ pre u.ex U) ∧ (∀ (K : Type) (W : K → A.left.Opens) z, z ∈ pre u.ex (⨆ i, W i) ↔ ∃ i, z ∈ pre u.ex (W i)) ∧ (∀ U z, z ∈ pre u.ex U → ∃ W : A.left.affineOpens, W.1 ≤ U ∧ z ∈ pre u.ex W.1) ∧ (∀ U V (h : V ≤ U) (b : Sec (str A) U), ∀ z ∈ pre u.ex V, val u.ex V (Sec.res (str A) h b) z = val u.ex U b z) ∧ (∀ U, ∀ z ∈ pre u.ex U, ∃ e : Sec (str A) U →ₐ[ℂ] ℂ, ∀ b, val u.ex U b z = e b) ∧ (∀ U b z, z ∈ pre u.ex (A.left.basicOpen b) ↔ val u.ex U b z ≠ 0) ∧ ∀ z, z ∈ pre u.ex ⊤ := by
  first | exact @GlobalTheory.CechPer.pre_val_rules | exact GlobalTheory.CechPer.pre_val_rules | (intros; apply GlobalTheory.CechPer.pre_val_rules <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorPolynomialEvalAlgebraFormalProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorPolynomialEvalAlgebraFormalProperties
set_option autoImplicit false

open Filter Topology

namespace GlobalTheory.PeriodFamily

section
variable {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D)

set_option autoImplicit false in
open Filter Topology in
variable {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D) in
theorem _root_.GlobalTheory.PeriodFamily.taylor_add_of_analyticAt (f g : (I → ℂ) → ℂ) (hf : AnalyticAt ℂ f 0)
    (hg : AnalyticAt ℂ g 0) :
    _root_.GlobalTheory.PeriodFamily.taylor N t (fun z ↦ f z + g z) =
      _root_.GlobalTheory.PeriodFamily.taylor N t f + _root_.GlobalTheory.PeriodFamily.taylor N t g := by
  unfold _root_.GlobalTheory.PeriodFamily.taylor
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← add_smul, show (fun z ↦ f z + g z) = f + g from rfl,
    iteratedFDeriv_add_apply hf.contDiffAt hg.contDiffAt, ContinuousMultilinearMap.add_apply, mul_add]

set_option autoImplicit false in
open Filter Topology in
variable {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D) in
theorem _root_.GlobalTheory.PeriodFamily.taylor_const_fun (c : ℂ) :
    _root_.GlobalTheory.PeriodFamily.taylor N t (fun _ ↦ c) = algebraMap ℂ D c := by
  unfold _root_.GlobalTheory.PeriodFamily.taylor
  rw [Finset.sum_range_succ', Finset.sum_eq_zero fun k _ => ?_]
  · simp [Algebra.algebraMap_eq_smul_one]
  · simp [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero k)]

set_option autoImplicit false in
open Filter Topology in
variable {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D) in
theorem _root_.GlobalTheory.PeriodFamily.taylor_congr_germ (f g : (I → ℂ) → ℂ) (h : f =ᶠ[𝓝 0] g) :
    _root_.GlobalTheory.PeriodFamily.taylor N t f = _root_.GlobalTheory.PeriodFamily.taylor N t g := by
  unfold _root_.GlobalTheory.PeriodFamily.taylor
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun s _ => ?_
  rw [(h.iteratedFDeriv ℂ k).eq_of_nhds]

set_option autoImplicit false in
open Filter Topology in
variable {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D) in
theorem _root_.GlobalTheory.PeriodFamily.taylor_sub_value_mem_span (f : (I → ℂ) → ℂ) :
    _root_.GlobalTheory.PeriodFamily.taylor N t f - algebraMap ℂ D (f 0) ∈ Ideal.span (Set.range t) := by
  unfold _root_.GlobalTheory.PeriodFamily.taylor
  rw [Finset.sum_range_succ']
  have h0 : ∑ s : Fin 0 → I, ((↑(Nat.factorial 0))⁻¹ * (iteratedFDeriv ℂ 0 f 0)
      fun a ↦ Pi.single (s a) 1) • ∏ a, t (s a) = algebraMap ℂ D (f 0) := by
    simp [Algebra.algebraMap_eq_smul_one]
  rw [h0, add_sub_cancel_right]
  refine Ideal.sum_mem _ fun k _ => Ideal.sum_mem _ fun s _ => ?_
  rw [Algebra.smul_def, Fin.prod_univ_succ]
  exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨s 0, rfl⟩))

end


set_option autoImplicit false in
open Filter Topology in
theorem _root_.GlobalTheory.PeriodFamily.taylor_formal_properties : ∀ {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D), (∀ f g : (I → ℂ) → ℂ, AnalyticAt ℂ f 0 → AnalyticAt ℂ g 0 → _root_.GlobalTheory.PeriodFamily.taylor N t (fun z ↦ f z + g z) = _root_.GlobalTheory.PeriodFamily.taylor N t f + _root_.GlobalTheory.PeriodFamily.taylor N t g) ∧ (∀ (c : ℂ) (f : (I → ℂ) → ℂ), AnalyticAt ℂ f 0 → _root_.GlobalTheory.PeriodFamily.taylor N t (fun z ↦ c * f z) = c • _root_.GlobalTheory.PeriodFamily.taylor N t f) ∧ (∀ c : ℂ, _root_.GlobalTheory.PeriodFamily.taylor N t (fun _ ↦ c) = algebraMap ℂ D c) ∧ (∀ f g : (I → ℂ) → ℂ, f =ᶠ[𝓝 0] g → _root_.GlobalTheory.PeriodFamily.taylor N t f = _root_.GlobalTheory.PeriodFamily.taylor N t g) ∧ (∀ (D' : Type) [CommRing D'] [Algebra ℂ D'] (ψ : D →ₐ[ℂ] D') (f : (I → ℂ) → ℂ), ψ (_root_.GlobalTheory.PeriodFamily.taylor N t f) = _root_.GlobalTheory.PeriodFamily.taylor N (fun i ↦ ψ (t i)) f) ∧ (∀ f : (I → ℂ) → ℂ, _root_.GlobalTheory.PeriodFamily.taylor N t f - algebraMap ℂ D (f 0) ∈ Ideal.span (Set.range t)) := by
  intro I _ _ D _ _ N t
  refine ⟨fun f g hf hg => _root_.GlobalTheory.PeriodFamily.taylor_add_of_analyticAt N t f g hf hg,
    fun c f hf => ?_, _root_.GlobalTheory.PeriodFamily.taylor_const_fun N t,
    _root_.GlobalTheory.PeriodFamily.taylor_congr_germ N t, fun D' _ _ ψ f => ?_,
    _root_.GlobalTheory.PeriodFamily.taylor_sub_value_mem_span N t⟩
  · unfold _root_.GlobalTheory.PeriodFamily.taylor
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [show (fun z ↦ c * f z) = fun z ↦ c • f z from rfl,
      iteratedFDeriv_const_smul_apply' hf.contDiffAt, ContinuousMultilinearMap.smul_apply,
      smul_eq_mul, smul_smul, mul_left_comm]
  · unfold _root_.GlobalTheory.PeriodFamily.taylor
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, map_prod]

end GlobalTheory.PeriodFamily
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorPolynomialEvalAlgebraFormalPropertiesStatement
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.taylorPolynomialEvalAlgebra_formal_properties : ∀ {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D), (∀ f g : (I → ℂ) → ℂ, AnalyticAt ℂ f 0 → AnalyticAt ℂ g 0 → GlobalTheory.PeriodFamily.taylor N t (fun z ↦ f z + g z) = GlobalTheory.PeriodFamily.taylor N t f + GlobalTheory.PeriodFamily.taylor N t g) ∧ (∀ (c : ℂ) (f : (I → ℂ) → ℂ), AnalyticAt ℂ f 0 → GlobalTheory.PeriodFamily.taylor N t (fun z ↦ c * f z) = c • GlobalTheory.PeriodFamily.taylor N t f) ∧ (∀ c : ℂ, GlobalTheory.PeriodFamily.taylor N t (fun _ ↦ c) = algebraMap ℂ D c) ∧ (∀ f g : (I → ℂ) → ℂ, f =ᶠ[𝓝 0] g → GlobalTheory.PeriodFamily.taylor N t f = GlobalTheory.PeriodFamily.taylor N t g) ∧ (∀ (D' : Type) [CommRing D'] [Algebra ℂ D'] (ψ : D →ₐ[ℂ] D') (f : (I → ℂ) → ℂ), ψ (GlobalTheory.PeriodFamily.taylor N t f) = GlobalTheory.PeriodFamily.taylor N (fun i ↦ ψ (t i)) f) ∧ (∀ f : (I → ℂ) → ℂ, GlobalTheory.PeriodFamily.taylor N t f - algebraMap ℂ D (f 0) ∈ Ideal.span (Set.range t)) := by
  first | exact @GlobalTheory.PeriodFamily.taylor_formal_properties | exact GlobalTheory.PeriodFamily.taylor_formal_properties | (intros; apply GlobalTheory.PeriodFamily.taylor_formal_properties <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedOneFormEvaluationRules
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedOneFormEvaluationRules
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CechPer

variable {A : Over (Sp ℂ)} [GrpObj A] {g : ℕ} {L : LB A.left}

theorem holUnif_ex_left_comp_str (u : HolUnif A L g) (w : Fin g → ℂ) : (u.ex w).left ≫ str A = 𝟙 (Sp ℂ) := by
  have := Over.w (u.ex w)
  simp [str, this]

theorem holUnif_val_algebraMap (u : HolUnif A L g) (U : A.left.Opens) (w : Fin g → ℂ) (hw : w ∈ pre u.ex U) (c : ℂ) :
    val u.ex U (algebraMap ℂ (Sec (str A) U) c) w = c := by
  show valAt' (u.ex w).left U (((str A).appLE ⊤ U le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom c)) = c
  rw [valAt'_appLE (u.ex w).left (str A) ⊤ U le_top _ hw, holUnif_ex_left_comp_str]
  exact valAt'_id_top c

theorem holUnif_val_mul (u : HolUnif A L g) (U : A.left.Opens) (a b : Sec (str A) U) :
    val u.ex U (a * b) = fun w => val u.ex U a w * val u.ex U b w :=
  funext fun w => valAt'_mul (u.ex w).left U a b

theorem holUnif_val_add (u : HolUnif A L g) (U : A.left.Opens) (a b : Sec (str A) U) :
    val u.ex U (a + b) = fun w => val u.ex U a w + val u.ex U b w :=
  funext fun w => valAt'_add (u.ex w).left U a b

theorem holUnif_differentiableAt_val (u : HolUnif A L g) (U : A.left.Opens) (b : Sec (str A) U) {z : Fin g → ℂ}
    (hz : z ∈ pre u.ex U) : DifferentiableAt ℂ (val u.ex U b) z :=
  (u.hol U b).2.differentiableAt (((u.hol U b).1).mem_nhds hz)

theorem exists_isEv (u : HolUnif A L g) (U : A.left.Opens) {z : Fin g → ℂ} (hz : z ∈ pre u.ex U) :
    ∃ E, IsEv u.ex U z E := by
  let N := (Fin g → ℂ) →L[ℂ] ℂ
  let e : Sec (str A) U →+* ℂ := valAtHom (u.ex z).left U hz
  have he : ∀ a, e a = val u.ex U a z := fun a => (valAt'_eq_valAtHom (u.ex z).left hz a).symm
  letI : Module (Sec (str A) U) N := Module.compHom N e
  haveI : IsScalarTower ℂ (Sec (str A) U) N := ⟨fun c a n => by
    show e (c • a) • n = c • (e a • n)
    rw [Algebra.smul_def, map_mul, mul_smul, he (algebraMap ℂ _ c), holUnif_val_algebraMap u U z hz]⟩
  have hc : ∀ (c : ℂ) (b : Sec (str A) U), val u.ex U (c • b) =ᶠ[nhds z] fun w => c * val u.ex U b w := by
    intro c b
    filter_upwards [((u.hol U b).1).mem_nhds hz] with w hw
    rw [Algebra.smul_def, holUnif_val_mul]
    exact congrArg (· * val u.ex U b w) (holUnif_val_algebraMap u U w hw c)
  let Dl : Sec (str A) U →ₗ[ℂ] N :=
    { toFun := fun b => fderiv ℂ (val u.ex U b) z
      map_add' := fun a b =>
        (congrArg (fun f => fderiv ℂ f z) (holUnif_val_add u U a b)).trans
          (fderiv_add (holUnif_differentiableAt_val u U a hz) (holUnif_differentiableAt_val u U b hz))
      map_smul' := fun c b =>
        (hc c b).fderiv_eq.trans (fderiv_const_mul (holUnif_differentiableAt_val u U b hz) c) }
  let D' : Derivation ℂ (Sec (str A) U) N :=
    { Dl with
      map_one_eq_zero' := by
        show fderiv ℂ (val u.ex U 1) z = 0
        have h1 : val u.ex U (1 : Sec (str A) U) =ᶠ[nhds z] fun _ => (1 : ℂ) := by
          filter_upwards [((u.hol U 1).1).mem_nhds hz] with w hw
          exact valAt'_one (u.ex w).left hw
        exact h1.fderiv_eq.trans (fderiv_const_apply 1)
      leibniz' := fun a b => by
        show fderiv ℂ (val u.ex U (a * b)) z = e a • fderiv ℂ (val u.ex U b) z + e b • fderiv ℂ (val u.ex U a) z
        rw [he, he]
        exact (congrArg (fun f => fderiv ℂ f z) (holUnif_val_mul u U a b)).trans
          (fderiv_mul (holUnif_differentiableAt_val u U a hz) (holUnif_differentiableAt_val u U b hz)) }
  refine ⟨D'.liftKaehlerDifferential.restrictScalars ℂ, fun a b => ?_⟩
  show D'.liftKaehlerDifferential (a • KaehlerDifferential.D ℂ (Sec (str A) U) b) = _
  rw [LinearMap.map_smul, Derivation.liftKaehlerDifferential_comp_D]
  show e a • fderiv ℂ (val u.ex U b) z = _
  rw [he]

theorem isEv_evForm (u : HolUnif A L g) (U : A.left.Opens) {z : Fin g → ℂ} (hz : z ∈ pre u.ex U) :
    IsEv u.ex U z (evForm u.ex U z) := by
  have h := exists_isEv u U hz
  rw [evForm, dite_eq_left h]
  exact h.choose_spec

theorem evForm_rules : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ (U : A.left.Opens),
    ∀ z ∈ pre u.ex U, IsEv u.ex U z (evForm u.ex U z) ∧
      (∀ (a : Sec (str A) U) ξ, evForm u.ex U z (a • ξ) = val u.ex U a z • evForm u.ex U z ξ) ∧
      ∀ b : Sec (str A) U, evForm u.ex U z (KaehlerDifferential.D ℂ _ b) = fderiv ℂ (val u.ex U b) z := by
  intro A _ g L u U z hz
  have hE := isEv_evForm u U hz
  have hone : val u.ex U (1 : Sec (str A) U) z = 1 := valAt'_one (u.ex z).left hz
  have hD : ∀ b : Sec (str A) U, evForm u.ex U z (KaehlerDifferential.D ℂ _ b) = fderiv ℂ (val u.ex U b) z := by
    intro b
    have := hE 1 b
    rwa [one_smul, hone, one_smul] at this
  refine ⟨hE, fun a ξ => ?_, hD⟩
  have hspan := KaehlerDifferential.span_range_derivation ℂ (Sec (str A) U)
  have hξ : ξ ∈ Submodule.span (Sec (str A) U) (Set.range (KaehlerDifferential.D ℂ (Sec (str A) U))) := by
    rw [hspan]; exact Submodule.mem_top
  revert a
  induction hξ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, rfl⟩ := hx
    intro a
    rw [hE a b, hD]
  | zero => intro a; simp
  | add x y _ _ hx hy => intro a; rw [smul_add, map_add (f := _), map_add (f := _), hx, hy, smul_add]
  | smul s x _ hx =>
    intro a
    rw [smul_smul, hx, hx, smul_smul, holUnif_val_mul]

end GlobalTheory.CechPer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedOneFormEvaluationRulesStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisedOneFormEvaluation_rules : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ (U : A.left.Opens), ∀ z ∈ pre u.ex U, IsEv u.ex U z (evForm u.ex U z) ∧ (∀ (a : Sec (str A) U) ξ, evForm u.ex U z (a • ξ) = val u.ex U a z • evForm u.ex U z ξ) ∧ ∀ b : Sec (str A) U, evForm u.ex U z (KaehlerDifferential.D ℂ _ b) = fderiv ℂ (val u.ex U b) z := by
  first | exact @GlobalTheory.CechPer.evForm_rules | exact GlobalTheory.CechPer.evForm_rules | (intros; apply GlobalTheory.CechPer.evForm_rules <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorHolomorphicExtOfValues
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorHolomorphicExtOfValues
open Filter Topology TopologicalSpace GlobalTheory.AnPer TensorProduct

namespace GlobalTheory


open Filter Topology in
open Filter Topology TopologicalSpace TensorProduct in
theorem _root_.GlobalTheory.tensor_hol_ext_of_values :
    ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Opens E) (D : Type) [CommRing D] [Algebra ℂ D] (x y : D ⊗[ℂ] _root_.GlobalTheory.AnPer.Hol W), (∀ (p : E) (hp : p ∈ W), Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (_root_.GlobalTheory.AnPer.Hol.ev p hp)) (fun _ _ ↦ Commute.all _ _) x = Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (_root_.GlobalTheory.AnPer.Hol.ev p hp)) (fun _ _ ↦ Commute.all _ _) y) → x = y := by
  intro E _ _ W D _ _ x y h
  classical
  rw [← sub_eq_zero]
  set z := x - y with hz
  have hzp : ∀ (p : E) (hp : p ∈ W), Algebra.TensorProduct.lift (AlgHom.id ℂ D)
      ((Algebra.ofId ℂ D).comp (_root_.GlobalTheory.AnPer.Hol.ev p hp))
      (fun _ _ ↦ Commute.all _ _) z = 0 := fun p hp => by
    rw [hz, map_sub, h p hp, sub_self]
  let b := Module.Free.chooseBasis ℂ D
  let e := TensorProduct.equivFinsuppOfBasisLeft (N := _root_.GlobalTheory.AnPer.Hol W) b
  have hc : ∀ i, e z i = 0 := by
    intro i
    apply _root_.GlobalTheory.AnPer.Hol.ext_fn
    intro p hp
    have hzero : (0 : _root_.GlobalTheory.AnPer.Hol W).fn p = 0 := by
      rw [← _root_.GlobalTheory.AnPer.Hol.ev_apply p hp, map_zero]
    have h0 := hzp p hp
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← e.symm_apply_apply z, TensorProduct.equivFinsuppOfBasisLeft_symm_apply, Finsupp.sum,
      map_sum] at h0
    simp only [Algebra.TensorProduct.lift_tmul, AlgHom.id_apply, AlgHom.comp_apply,
      _root_.GlobalTheory.AnPer.Hol.ev_apply, Algebra.ofId_apply] at h0
    have h1 : ∑ j ∈ (e z).support, (e z j).fn p • b j = 0 := by
      rw [← h0]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Algebra.smul_def, mul_comm]
    by_cases hi : i ∈ (e z).support
    · rw [linearIndependent_iff'.1 b.linearIndependent (e z).support (fun j => (e z j).fn p) h1 i hi,
        hzero]
    · rw [Finsupp.notMem_support_iff.1 hi]
  exact e.injective (by rw [map_zero]; exact Finsupp.ext hc)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorHolomorphicExtOfValuesStatement
open Filter Topology TopologicalSpace GlobalTheory.AnPer TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_holomorphic_ext_of_values : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Opens E) (D : Type) [CommRing D] [Algebra ℂ D] (x y : D ⊗[ℂ] Hol W), (∀ (p : E) (hp : p ∈ W), Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (Hol.ev p hp)) (fun _ _ ↦ Commute.all _ _) x = Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (Hol.ev p hp)) (fun _ _ ↦ Commute.all _ _) y) → x = y := by
  first | exact @GlobalTheory.tensor_hol_ext_of_values | exact GlobalTheory.tensor_hol_ext_of_values | (intros; apply GlobalTheory.tensor_hol_ext_of_values <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAffineCurveEtaleCohomologicalDimensionLeOn
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAffineCurveTateTwistCohomologySubsingleton
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MayerVietorisExactEtale
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainComplexExactSquare
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspReductionBound
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem chains_shortExact_of_free : ∀ (R : Type) [CommRing R] {X₁ X₂ X₃ X₄ : Scheme.{0}} (a : X₁ ⟶ X₂) (b : X₁ ⟶ X₃) (c : X₂ ⟶ X₄) (d : X₃ ⟶ X₄) (w₁ : biprod.lift ((free R).map (yoneda.map a)) (-(free R).map (yoneda.map b)) ≫ biprod.desc ((free R).map (yoneda.map c)) ((free R).map (yoneda.map d)) = 0) (w₂ : biprod.lift ((chains R).map (sch.map a)) (-(chains R).map (sch.map b)) ≫ biprod.desc ((chains R).map (sch.map c)) ((chains R).map (sch.map d)) = 0), (ShortComplex.mk _ _ w₁).ShortExact → (ShortComplex.mk _ _ w₂).ShortExact := by
  intro R _ X₁ X₂ X₃ X₄ a b c d w₁ w₂ h
  obtain ⟨hLE, hnat, -⟩ := chains_basic R
  have hm : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) (p : ℕ), ((chains R).map (sch.map f)).f (-(p : ℤ)) ≫ (chainsXIso R (sch.obj Y) p).hom =
      (chainsXIso R (sch.obj X) p).hom ≫ (free R).map (yoneda.map f) := fun f p => hnat (sch.map f) p
  let e : ∀ (X : Scheme.{0}) (p : ℕ), ((chains R).obj (sch.obj X)).X (-(p : ℤ)) ≅ (free R).obj (yoneda.obj X) :=
    fun X p => chainsXIso R (sch.obj X) p
  have he : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) (p : ℕ), ((chains R).map (sch.map f)).f (-(p : ℤ)) ≫ (e Y p).hom =
      (e X p).hom ≫ (free R).map (yoneda.map f) := fun f p => hm f p
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  rcases (show (∃ p : ℕ, n = -(p : ℤ)) ∨ 0 < n from by
    by_cases hn : 0 < n
    · exact Or.inr hn
    · exact Or.inl ⟨(-n).toNat, by omega⟩) with ⟨p, rfl⟩ | hn
  · have c1 : (e X₁ p).hom ≫ biprod.lift ((free R).map (yoneda.map a)) (-(free R).map (yoneda.map b)) =
        (biprod.lift ((chains R).map (sch.map a)) (-(chains R).map (sch.map b))).f (-(p : ℤ)) ≫
          ((HomologicalComplex.biprodXIso _ _ _).hom ≫ biprod.map (e X₂ p).hom (e X₃ p).hom) := by
      apply biprod.hom_ext
      · simp only [Category.assoc, biprod.map_fst, biprod.lift_fst, HomologicalComplex.biprodXIso_hom_fst_assoc]
        rw [← HomologicalComplex.comp_f_assoc, biprod.lift_fst, he]
      · simp only [Category.assoc, biprod.map_snd, biprod.lift_snd, HomologicalComplex.biprodXIso_hom_snd_assoc]
        rw [← HomologicalComplex.comp_f_assoc, biprod.lift_snd, HomologicalComplex.neg_f_apply, Preadditive.neg_comp, he,
          Preadditive.comp_neg]
    have c2 : ((HomologicalComplex.biprodXIso _ _ _).hom ≫ biprod.map (e X₂ p).hom (e X₃ p).hom) ≫
        biprod.desc ((free R).map (yoneda.map c)) ((free R).map (yoneda.map d)) =
        (biprod.desc ((chains R).map (sch.map c)) ((chains R).map (sch.map d))).f (-(p : ℤ)) ≫ (e X₄ p).hom := by
      rw [Category.assoc, ← Iso.eq_inv_comp]
      apply biprod.hom_ext'
      · simp only [biprod.inl_map_assoc, biprod.inl_desc, HomologicalComplex.inl_biprodXIso_inv_assoc]
        rw [← HomologicalComplex.comp_f_assoc, biprod.inl_desc, he]
      · simp only [biprod.inr_map_assoc, biprod.inr_desc, HomologicalComplex.inr_biprodXIso_inv_assoc]
        rw [← HomologicalComplex.comp_f_assoc, biprod.inr_desc, he]
    refine ShortComplex.shortExact_of_iso ?_ h
    refine (ShortComplex.isoMk (e X₁ p)
      (HomologicalComplex.biprodXIso _ _ _ ≪≫ biprod.mapIso (e X₂ p) (e X₃ p))
      (e X₄ p) ?_ ?_).symm
    · exact c1
    · exact c2
  · have z : ∀ X : Scheme.{0}, IsZero (((chains R).obj (sch.obj X)).X n) := fun X =>
      have := hLE (sch.obj X); CochainComplex.isZero_of_isStrictlyLE _ 0 n hn
    have z₂ : IsZero ((((chains R).obj (sch.obj X₂)) ⊞ ((chains R).obj (sch.obj X₃))).X n) :=
      IsZero.of_iso ((biprod_isZero_iff _ _).2 ⟨z X₂, z X₃⟩) (HomologicalComplex.biprodXIso _ _ _)
    exact
      { exact := ShortComplex.exact_of_isZero_X₂ _ z₂
        mono_f := ⟨fun _ _ _ => (z X₁).eq_of_tgt _ _⟩
        epi_g := ⟨fun _ _ _ => (z X₄).eq_of_src _ _⟩ }

end GlobalTheory.EtC
end

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chain_complex_exact_square : ∀ (R : Type) [CommRing R] {X₁ X₂ X₃ X₄ : Scheme.{0}} (a : X₁ ⟶ X₂) (b : X₁ ⟶ X₃) (c : X₂ ⟶ X₄) (d : X₃ ⟶ X₄) (w₁ : biprod.lift ((free R).map (yoneda.map a)) (-(free R).map (yoneda.map b)) ≫ biprod.desc ((free R).map (yoneda.map c)) ((free R).map (yoneda.map d)) = 0) (w₂ : biprod.lift ((chains R).map (sch.map a)) (-(chains R).map (sch.map b)) ≫ biprod.desc ((chains R).map (sch.map c)) ((chains R).map (sch.map d)) = 0), (ShortComplex.mk _ _ w₁).ShortExact → (ShortComplex.mk _ _ w₂).ShortExact := by
  first | (exact @GlobalTheory.EtC.chains_shortExact_of_free) | (exact GlobalTheory.EtC.chains_shortExact_of_free) | (intros; apply GlobalTheory.EtC.chains_shortExact_of_free <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MayerVietorisExactEtale
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.AffineCurveNbhd

noncomputable section
namespace GlobalTheory.EtC.ExcisionNat

abbrev C (R : Type) [CommRing R] (B : Type) [CommRing B] : Cx R := (chains R).obj (sp B)

abbrev Cm (R : Type) [CommRing R] {B B' : Type} [CommRing B] [CommRing B'] (g : B →+* B') : C R B' ⟶ C R B :=
  (chains R).map (spMap g)

theorem spMap_comp {B₀ B B' : Type} [CommRing B₀] [CommRing B] [CommRing B'] (h : B₀ →+* B) (g : B →+* B') :
    spMap g ≫ spMap h = spMap (g.comp h) := by
  simp only [spMap, ← Functor.map_comp, ← Spec.map_comp, CommRingCat.ofHom_comp]

theorem Cm_comp (R : Type) [CommRing R] {B₀ B B' : Type} [CommRing B₀] [CommRing B] [CommRing B'] (h : B₀ →+* B)
    (g : B →+* B') : Cm R g ≫ Cm R h = Cm R (g.comp h) := by
  rw [← Functor.map_comp, spMap_comp]

theorem awayMap_comp_algebraMap {A A' : Type} [CommRing A] [CommRing A'] [Algebra A A'] (f : A) :
    (Localization.awayMap (algebraMap A A') f).comp (algebraMap A (Localization.Away f)) =
      (algebraMap A' (Localization.Away (algebraMap A A' f))).comp (algebraMap A A') :=
  IsLocalization.map_comp _

theorem awayHom_comp_awayMap {A A' A'' : Type} [CommRing A] [CommRing A'] [CommRing A''] [Algebra A A']
    [Algebra A A''] (φ : A' →ₐ[A] A'') (f : A) :
    (awayHom φ f).comp (Localization.awayMap (algebraMap A A') f) = Localization.awayMap (algebraMap A A'') f := by
  apply IsLocalization.ringHom_ext (Submonoid.powers f)
  rw [RingHom.comp_assoc, awayMap_comp_algebraMap, ← RingHom.comp_assoc, awayHom_comp_algebraMap,
    awayMap_comp_algebraMap, RingHom.comp_assoc]
  congr 1
  exact RingHom.ext fun a => φ.commutes a

def exSC (R : Type) [CommRing R] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A) :
    ShortComplex (Cx R) :=
  ShortComplex.mk
    (biprod.lift (Cm R (Localization.awayMap (algebraMap A A') f))
      (-Cm R (algebraMap A' (Localization.Away (algebraMap A A' f)))))
    (biprod.desc (Cm R (algebraMap A (Localization.Away f))) (Cm R (algebraMap A A')))
    (by rw [biprod.lift_desc, Preadditive.neg_comp, Cm_comp, Cm_comp, awayMap_comp_algebraMap, add_neg_cancel])

theorem exSC_shortExact (R : Type) [CommRing R] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A']
    [Algebra.Etale A A'] (f : A) (hN : IsNbhd A A' f) : (exSC R A A' f).ShortExact := by
  refine GlobalTheory.T.chain_complex_exact_square R _ _ _ _ ?_ (exSC R A A' f).zero (GlobalTheory.T.freeEtaleSheaf_excision_shortExact R A A' f hN ?_)
  all_goals
    simp only [biprod.lift_desc, Preadditive.neg_comp, ← Functor.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      awayMap_comp_algebraMap, add_neg_cancel]

def exMap (R : Type) [CommRing R] {A A' A'' : Type} [CommRing A] [CommRing A'] [CommRing A''] [Algebra A A']
    [Algebra A A''] (φ : A' →ₐ[A] A'') (f : A) : exSC R A A'' f ⟶ exSC R A A' f where
  τ₁ := Cm R (awayHom φ f)
  τ₂ := biprod.map (𝟙 _) (Cm R φ.toRingHom)
  τ₃ := 𝟙 _
  comm₁₂ := by
    apply biprod.hom_ext
    · simp only [exSC, Category.assoc, biprod.lift_fst, biprod.map_fst, Category.comp_id, Cm_comp, awayHom_comp_awayMap]
    · simp only [exSC]
      rw [Category.assoc, Category.assoc, biprod.lift_snd, biprod.map_snd, ← Category.assoc, biprod.lift_snd,
        Preadditive.comp_neg, Preadditive.neg_comp, Cm_comp, Cm_comp, awayHom_comp_algebraMap]
  comm₂₃ := by
    apply biprod.hom_ext'
    · simp only [exSC, biprod.inl_map_assoc, Category.id_comp, biprod.inl_desc, Category.comp_id]
    · simp only [exSC, biprod.inr_map_assoc, biprod.inr_desc, Category.comp_id, Cm_comp]
      congr 2
      exact RingHom.ext fun a => φ.commutes a

theorem excision_natural : ∀ (q : ℕ) (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] [Algebra.Etale A A'] (f : A), IsNbhd A A' f → ∀ n i : ℤ, ∃ δ : Ht q (sp (Localization.Away (algebraMap A A' f))) n i →+ Ht q (sp A) (n + 1) i, Function.Exact δ (fun x : Ht q (sp A) (n + 1) i => (pull _ (spMap (algebraMap A (Localization.Away f))) _ _ x, pull _ (spMap (algebraMap A A')) _ _ x)) ∧ ∀ (A'' : Type) [CommRing A''] [Algebra A A''] [Algebra.Etale A A''] (φ : A' →ₐ[A] A''), IsNbhd A A'' f → ∀ z, pull _ (spMap (awayHom φ f)) _ _ z = 0 → δ z = 0 := by
  intro q A A' _ _ _ _ f hN n i
  have hI : ∀ k, Injective ((res (ZMod q) (tw q i)).X k) := fun k =>
    inferInstanceAs (Injective ((injectiveResolution (tw q i)).cochainComplex.X k))
  obtain ⟨d, hex, hnat⟩ := longExact_first_of_injective (ZMod q) (res (ZMod q) (tw q i)) hI
  have hS := exSC_shortExact (ZMod q) A A' f hN
  refine ⟨d (exSC (ZMod q) A A' f) hS n, ?_, ?_⟩
  · intro x
    refine Iff.trans ?_ ((hex _ hS n).2.2 x)
    have hb := (cpull_biprod_bijective (ZMod q) (C (ZMod q) (Localization.Away f)) (C (ZMod q) A')
      (res (ZMod q) (tw q i)) (n + 1)).1
    have e1 : pull (ZMod q) (spMap (algebraMap A (Localization.Away f))) (tw q i) (n + 1) x =
        cpull (biprod.inl : C (ZMod q) (Localization.Away f) ⟶ _) (res (ZMod q) (tw q i)) (n + 1)
          (cpull (exSC (ZMod q) A A' f).g (res (ZMod q) (tw q i)) (n + 1) x) := by
      have hc : (biprod.inl : C (ZMod q) (Localization.Away f) ⟶ C (ZMod q) (Localization.Away f) ⊞ C (ZMod q) A') ≫ (exSC (ZMod q) A A' f).g = Cm (ZMod q) (algebraMap A (Localization.Away f)) := biprod.inl_desc _ _
      refine Eq.trans ?_ ((ZcFun.main (ZMod q)).2.1 _ (exSC (ZMod q) A A' f).g _ _ x)
      exact (congrArg (fun m => cpull m (res (ZMod q) (tw q i)) (n + 1) x) hc).symm
    have e2 : pull (ZMod q) (spMap (algebraMap A A')) (tw q i) (n + 1) x =
        cpull (biprod.inr : C (ZMod q) A' ⟶ _) (res (ZMod q) (tw q i)) (n + 1)
          (cpull (exSC (ZMod q) A A' f).g (res (ZMod q) (tw q i)) (n + 1) x) := by
      have hc : (biprod.inr : C (ZMod q) A' ⟶ C (ZMod q) (Localization.Away f) ⊞ C (ZMod q) A') ≫ (exSC (ZMod q) A A' f).g = Cm (ZMod q) (algebraMap A A') := biprod.inr_desc _ _
      refine Eq.trans ?_ ((ZcFun.main (ZMod q)).2.1 _ (exSC (ZMod q) A A' f).g _ _ x)
      exact (congrArg (fun m => cpull m (res (ZMod q) (tw q i)) (n + 1) x) hc).symm
    change (_, _) = ((0, 0) : _ × _) ↔ _
    rw [e1, e2]
    obtain ⟨y, hy⟩ : ∃ y : CohomologyClass (C (ZMod q) (Localization.Away f) ⊞ C (ZMod q) A') (res (ZMod q) (tw q i)) (n + 1),
      y = cpull (exSC (ZMod q) A A' f).g (res (ZMod q) (tw q i)) (n + 1) x := ⟨_, rfl⟩
    rw [← hy]
    constructor
    · intro h
      apply hb
      dsimp only
      rw [h]
      exact Prod.ext (map_zero _).symm (map_zero _).symm
    · intro h
      rw [h]
      exact Prod.ext (map_zero _) (map_zero _)
  · intro A'' _ _ _ φ hN'' z hz
    have hS'' := exSC_shortExact (ZMod q) A A'' f hN''
    have h := hnat _ _ hS'' hS (exMap (ZMod q) φ f) n z
    have hz' : cpull (exMap (ZMod q) φ f).τ₁ (res (ZMod q) (tw q i)) n z = 0 := hz
    rw [hz', map_zero] at h
    have hid : cpull (exMap (ZMod q) φ f).τ₃ (res (ZMod q) (tw q i)) (n + 1) (d _ hS n z) = d _ hS n z :=
      ZcFun.cpull_id _ _ _ _
    rw [hid] at h
    exact h

end GlobalTheory.EtC.ExcisionNat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MayerVietorisExactEtaleStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GlobalTheory.AffineCurveNbhd
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mayer_vietoris_exact_etale : ∀ (q : ℕ) (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] [Algebra.Etale A A'] (f : A), IsNbhd A A' f → ∀ n i : ℤ, ∃ δ : Ht q (sp (Localization.Away (algebraMap A A' f))) n i →+ Ht q (sp A) (n + 1) i, Function.Exact δ (fun x : Ht q (sp A) (n + 1) i => (pull _ (spMap (algebraMap A (Localization.Away f))) _ _ x, pull _ (spMap (algebraMap A A')) _ _ x)) ∧ ∀ (A'' : Type) [CommRing A''] [Algebra A A''] [Algebra.Etale A A''] (φ : A' →ₐ[A] A''), IsNbhd A A'' f → ∀ z, pull _ (spMap (awayHom φ f)) _ _ z = 0 → δ z = 0 := by
  first | (exact @GlobalTheory.EtC.ExcisionNat.excision_natural) | (exact GlobalTheory.EtC.ExcisionNat.excision_natural) | (intros; apply GlobalTheory.EtC.ExcisionNat.excision_natural <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAffineCurveTateTwistCohomologySubsingleton
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GlobalTheory.AffineCurveNbhd

namespace GlobalTheory.EtC.AffineCurve

theorem subsingleton_of_three_le : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B]
    [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ n i : ℤ, 3 ≤ n →
    Subsingleton (Ht q (sp B) n i) := by
  intro q _ k B _ _ _ _ _ _ hq n i hn
  have hqB : IsUnit (q : B) := by simpa using hq.map (algebraMap k B)
  by_cases hB : IsField B
  · exact GlobalTheory.T.strictlyHenselianLocalRing_acyclic_every_sheaf (ZMod q) B (GlobalTheory.T.sH_of_isField_finiteType_of_isAlgClosed k B hB) (tw q i) n (by omega)
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by ring⟩
    suffices h : ∀ x : Ht q (sp B) (m + 1) i, x = 0 from ⟨fun x y => by rw [h x, h y]⟩
    intro x
    obtain ⟨_, _⟩ := GlobalTheory.T.exists_isAlgebraic_ratFunc_fractionRing_dedekind k B hB
    have hqK : IsUnit (q : FractionRing B) := by simpa using hqB.map (algebraMap B (FractionRing B))
    have h1 : pull _ (spMap (algebraMap B (FractionRing B))) _ _ x = 0 :=
      (GlobalTheory.T.etale_cohomology_vanishing_algebraic_over_ratFunc q k (FractionRing B) hqK (m + 1) i (by omega)).elim _ _
    obtain ⟨f, hf0, hfu, hxf⟩ := GlobalTheory.T.class_vanishes_away_nonzero_nonunit_domain q B hB hqB (m + 1) i x h1
    obtain ⟨A', _, _, _, hA', hxA'⟩ := GlobalTheory.T.etale_local_vanishing_cohomology q k B hq f hf0 hfu (m + 1) i (by omega) x
    obtain ⟨δ, hex, hkill⟩ := GlobalTheory.T.mayer_vietoris_exact_etale q B A' f hA' m i
    obtain ⟨z, rfl⟩ := (hex x).mp (by simp [hxf, hxA'])
    obtain ⟨A'', _, _, _, φ, hA'', hz⟩ := GlobalTheory.T.higherDegree_class_dies_on_finer_etaleNeighbourhood q k B hq f hf0 hfu A' hA' m i (by omega) z
    exact hkill A'' φ hA'' z hz

end GlobalTheory.EtC.AffineCurve
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAffineCurveTateTwistCohomologySubsingletonStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothAffineCurve_tateTwistCohomology_subsingleton_of_ge_three : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ n i : ℤ, 3 ≤ n → Subsingleton (Ht q (sp B) n i) := by
  first | (exact @GlobalTheory.EtC.AffineCurve.subsingleton_of_three_le) | (exact GlobalTheory.EtC.AffineCurve.subsingleton_of_three_le) | (intros; apply GlobalTheory.EtC.AffineCurve.subsingleton_of_three_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAffineCurveEtaleCohomologicalDimensionLeOn
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory

theorem EtC.etC_c2 : GlobalTheory.EtC.C2 := by
  intro q _ k B _ _ _ _ _ _ hq n i hn
  rcases eq_or_lt_of_le hn with h | h
  · subst h
    exact GlobalTheory.T.subsingleton_Ht_two_of_isDedekindDomain_of_isAlgClosed q k B hq i
  · exact GlobalTheory.T.smoothAffineCurve_tateTwistCohomology_subsingleton_of_ge_three q k B hq n i (by omega)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAffineCurveEtaleCohomologicalDimensionLeOnStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_affine_curve_etale_cohomologicalDimension_le_one : GlobalTheory.EtC.C2 := by
  first | (exact @GlobalTheory.EtC.etC_c2) | (exact GlobalTheory.EtC.etC_c2) | (intros; apply GlobalTheory.EtC.etC_c2  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistLocalToGlobalStrictlyHenselian
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistLocalToGlobalStrictlyHenselian
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem tateTwist_local_to_global_strictlyHenselian : B3 := by
  intro q Y X S f p _ _ _ _ _ i h
  exact GlobalTheory.T.etaleEquivalence_scheme_of_strictlyHenselian_stalks (ZMod q) (tw q i) (GlobalTheory.T.tateTwist_finitary q i) Y X S f p
    (fun O _ s hs => h O s hs.1)

end GlobalTheory.EtC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistLocalToGlobalStrictlyHenselianStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etC_b3 : GlobalTheory.EtC.B3 := by
  first | (exact @GlobalTheory.EtC.tateTwist_local_to_global_strictlyHenselian) | (exact GlobalTheory.EtC.tateTwist_local_to_global_strictlyHenselian) | (intros; apply GlobalTheory.EtC.tateTwist_local_to_global_strictlyHenselian  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodComparisonOfGaussManinPeriods
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PeriodFamily

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PeriodFamily

theorem periodComparison_of_gaussManinPeriods (h : GlobalTheory.Published.GaussManinPeriods) : GlobalTheory.Published.PeriodComparison := by
  obtain ⟨ε, h⟩ := h
  refine ⟨ε, fun A _ g hA hs L hL u ↦ ?_⟩
  have hp : IsGrpPullback A A (spMap ((AlgHom.id ℂ ℂ : ℂ →ₐ[ℂ] ℂ) : ℂ →+* ℂ)) (𝟙 _) :=
    haveI : IsMonHom (Iso.refl A).hom := inferInstanceAs (IsMonHom (𝟙 A))
    (isGrpPullback_of_iso (Iso.refl A)).congr (Cris.spMap_id ℂ).symm rfl
  obtain ⟨V, u', τ, Q', Q, -, -, -, hQ, -⟩ := h ℂ A g hA hs Empty Set.univ (fun _ ↦ AlgHom.id ℂ ℂ)
    isOpen_univ trivial (fun _ ↦ differentiableOn_const _) (fun _ ↦ A) (fun _ ↦ 𝟙 _) (fun _ ↦ hp)
    (fun _ ↦ GrpMor.of_isGrpPullback (isDPMorphism_of_eq_bot _ rfl _ _) (by simp) hp) (fun _ ↦ L) (fun _ ↦ hL)
    A (𝟙 _) hp L hL u
  exact ⟨Q, hQ⟩

end GlobalTheory.PeriodFamily
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFirstDeRhamHomologyHodgeFiltrationOfField
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFirstDeRhamHomologyHodgeFiltrationOfField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham

set_option autoImplicit false

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem finrank_HdR_Fil_of_field (HF : GlobalTheory.Published.AbelianDeRham.Free)
    (HH : GlobalTheory.Published.AbelianDeRham.Hodge) (k : Type) [Field k] (A : Over (Sp k)) [GrpObj A] (g : ℕ)
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) :
    FiniteDimensional k (HdR A) ∧ Module.finrank k (HdR A) = 2 * g ∧
      Module.finrank k (Fil A) = g := by
  obtain ⟨hfin, -, hrk⟩ := GlobalTheory.Published.AbelianDeRham.Free.prim HF hA hg
  obtain ⟨-, -, hfin1, -, hrk1⟩ := HH k A g hA hg
  have p : PrimeSpectrum k := IsLocalRing.closedPoint k
  have h1 : Module.finrank k (primDR A) = 2 * g := by
    have := hrk p
    rwa [Module.rankAtStalk_eq_finrank_of_free] at this
  have h2 : Module.finrank k (PrimitiveSubmodule A) = g := by
    have := hrk1 p
    rwa [Module.rankAtStalk_eq_finrank_of_free] at this
  have hd : Module.finrank k (HdR A) = 2 * g := by
    change Module.finrank k (Module.Dual k (primDR A)) = 2 * g
    rw [Subspace.dual_finrank_eq, h1]
  refine ⟨?_, hd, ?_⟩
  · change FiniteDimensional k (Module.Dual k (primDR A))
    infer_instance
  · have := Subspace.finrank_add_finrank_dualAnnihilator_eq (PrimitiveSubmodule A)
    rw [h2, h1] at this
    change Module.finrank k (PrimitiveSubmodule A).dualAnnihilator = g
    omega

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFirstDeRhamHomologyHodgeFiltrationOfFieldStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_firstDeRhamHomology_hodgeFiltration_of_field : GlobalTheory.Published.AbelianDeRham.Free → GlobalTheory.Published.AbelianDeRham.Hodge → ∀ (k : Type) [Field k] (A : Over (Sp k)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → FiniteDimensional k (HdR A) ∧ Module.finrank k (HdR A) = 2 * g ∧ Module.finrank k (Fil A) = g := by
  first | exact @GlobalTheory.finrank_HdR_Fil_of_field | exact GlobalTheory.finrank_HdR_Fil_of_field | (intros; apply GlobalTheory.finrank_HdR_Fil_of_field <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoOfBijectiveAffinePts
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open ReciprocityTheory.ChartRestriction.G.Semi (mulN)
open GlobalTheory.DeRham (spOver spOver_comp)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace PDiv

universe u

theorem mono_of_injective_affinePts {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hinj : ∀ (R : CommRingCat.{u}) (a b : Spec R ⟶ X), a ≫ f = b ≫ f → a = b) : Mono f :=
  ⟨fun {W} a b h => W.affineOpenCover.openCover.hom_ext a b fun i =>
    hinj (W.affineOpenCover.X i) (W.affineOpenCover.f i ≫ a) (W.affineOpenCover.f i ≫ b)
      ((Category.assoc _ _ _).trans ((congrArg _ h).trans (Category.assoc _ _ _).symm))⟩

theorem isIso_of_bijective_affinePts {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : ∀ (R : CommRingCat.{u}), Function.Bijective fun a : Spec R ⟶ X => a ≫ f) : IsIso f := by
  have hm : Mono f := mono_of_injective_affinePts f fun R a b e => (h R).1 e
  let 𝒰 : Y.OpenCover := Y.affineOpenCover.openCover
  have hs : ∀ i : 𝒰.I₀, ∃ a : 𝒰.X i ⟶ X, a ≫ f = 𝒰.f i := fun i =>
    (h (Y.affineOpenCover.X i)).2 (Y.affineOpenCover.f i)
  choose g hg using hs
  have hc : ∀ i j : 𝒰.I₀, pullback.fst (𝒰.f i) (𝒰.f j) ≫ g i = pullback.snd (𝒰.f i) (𝒰.f j) ≫ g j :=
    fun i j => (cancel_mono f).1 (by
      simp only [Category.assoc, hg]
      exact pullback.condition)
  let k : Y ⟶ X := 𝒰.glueMorphisms g hc
  have hk : k ≫ f = 𝟙 Y := 𝒰.hom_ext _ _ fun i => by
    have e := 𝒰.ι_glueMorphisms g hc i
    simp only [k, ← Category.assoc, e, hg, Category.comp_id]
  refine ⟨k, ?_, hk⟩
  exact (cancel_mono f).1 (by simp only [Category.assoc, hk, Category.comp_id, Category.id_comp])

end PDiv

end GlobalTheory

namespace GlobalTheory

namespace PDiv

variable {O : Type} [CommRing O]

theorem exists_spOver {B D : Type} [CommRing B] [Algebra O B] [CommRing D] [Algebra O D]
    (v : Over.mk (spMap (algebraMap O B)) ⟶ Over.mk (spMap (algebraMap O D))) :
    ∃ ψ : D →ₐ[O] B, spOver ψ = v := by
  let f : Sp B ⟶ Sp D := v.left
  let ψ₀ : D →+* B := (Spec.preimage f).hom
  have h0 : spMap ψ₀ = f := (congrArg Spec.map (CommRingCat.ofHom_hom _)).trans
    (Spec.map_preimage f)
  have e : CommRingCat.ofHom (ψ₀.comp (algebraMap O D)) = CommRingCat.ofHom (algebraMap O B) :=
    Spec.map_injective (by
      change spMap (ψ₀.comp (algebraMap O D)) = spMap (algebraMap O B)
      rw [Cris.spMap_comp, h0]
      exact Over.w v)
  have h1 : ψ₀.comp (algebraMap O D) = algebraMap O B := congrArg CommRingCat.Hom.hom e
  exact ⟨{ ψ₀ with commutes' := RingHom.congr_fun h1 }, Over.OverMorphism.ext h0⟩

theorem spMap_preimage_toAlgebra {R : CommRingCat.{0}} (s : Spec R ⟶ Sp O) :
    @spMap O R _ _ (@algebraMap O R _ _ (Spec.preimage s).hom.toAlgebra) = s :=
  (congrArg Spec.map (CommRingCat.ofHom_hom _)).trans (Spec.map_preimage s)

end PDiv

namespace PDivGroup.TorsionTower

open PDiv ReciprocityTheory.ChartRestriction.G.Semi

variable {p : ℕ} {O : Type} [CommRing O] {G : PDivGroup p O} {A : Over (Sp O)} [GrpObj A]
  (t : TorsionTower G A)

theorem y_comp_mulN (n : ℕ) : t.y n ≫ mulN A (p ^ n) = toUnit _ ≫ η[A] := by
  rw [GrpTangent.mulN_eq_pow, MonObj.comp_pow, Category.comp_id, t.y_pow]
  rfl

def toTorsion (n : ℕ) : SpAlg O (G.A n) ⟶ torsion A (p ^ n) :=
  pullback.lift (t.y n) (toUnit _) (t.y_comp_mulN n)

@[reassoc (attr := simp)] theorem toTorsion_ι (n : ℕ) :
    t.toTorsion n ≫ torsion.ι A (p ^ n) = t.y n :=
  pullback.lift_fst _ _ _

theorem toTorsion_left_injective (n : ℕ) (R : CommRingCat.{0}) :
    Function.Injective fun a : Spec R ⟶ (SpAlg O (G.A n)).left => a ≫ (t.toTorsion n).left := by
  intro a b e
  change a ≫ (t.toTorsion n).left = b ≫ (t.toTorsion n).left at e
  let s := a ≫ (SpAlg O (G.A n)).hom
  have hb : b ≫ (SpAlg O (G.A n)).hom = s := by
    simp only [s, ← Over.w (t.toTorsion n), ← Category.assoc, e]
  let _ : Algebra O R := (Spec.preimage s).hom.toAlgebra
  have hs : spMap (algebraMap O R) = s := spMap_preimage_toAlgebra s
  let a' : SpAlg O R ⟶ SpAlg O (G.A n) := Over.homMk a hs.symm
  let b' : SpAlg O R ⟶ SpAlg O (G.A n) := Over.homMk b (hb.trans hs.symm)
  obtain ⟨φ, hφ⟩ := exists_spOver a'
  obtain ⟨ψ, hψ⟩ := exists_spOver b'
  have hy : a' ≫ t.y n = b' ≫ t.y n := by
    have hab : a' ≫ t.toTorsion n = b' ≫ t.toTorsion n := Over.OverMorphism.ext e
    simpa only [Category.assoc, toTorsion_ι] using
      congrArg (fun q => q ≫ torsion.ι A (p ^ n)) hab
  rw [← hφ, ← hψ] at hy
  have h : φ = ψ := t.inj n R φ ψ hy
  exact congrArg Over.Hom.left (hφ.symm.trans ((congrArg spOver h).trans hψ))

theorem toTorsion_left_surjective (n : ℕ) (R : CommRingCat.{0}) :
    Function.Surjective fun a : Spec R ⟶ (SpAlg O (G.A n)).left => a ≫ (t.toTorsion n).left := by
  intro w
  let s := w ≫ (torsion A (p ^ n)).hom
  let _ : Algebra O R := (Spec.preimage s).hom.toAlgebra
  have hs : spMap (algebraMap O R) = s := spMap_preimage_toAlgebra s
  let z : SpAlg O R ⟶ torsion A (p ^ n) := Over.homMk w hs.symm
  have hx : (z ≫ torsion.ι A (p ^ n)) ^ p ^ n = 1 := by
    have hc : torsion.ι A (p ^ n) ≫ mulN A (p ^ n) = toUnit _ ≫ η[A] :=
      pullback.condition.trans (congrArg (· ≫ η[A]) (toUnit_unique _ _))
    rw [← Category.comp_id (z ≫ torsion.ι A (p ^ n)), ← MonObj.comp_pow,
      ← GrpTangent.mulN_eq_pow, Category.assoc, hc, ← Category.assoc]
    exact (congrArg (· ≫ η[A]) (toUnit_unique _ _)).trans rfl
  obtain ⟨φ, hφ⟩ := t.surj n R _ hx
  have e : spOver φ ≫ t.toTorsion n = z := by
    refine pullback.hom_ext ?_ (toUnit_unique _ _)
    change spOver φ ≫ t.toTorsion n ≫ torsion.ι A (p ^ n) = z ≫ torsion.ι A (p ^ n)
    rw [toTorsion_ι, hφ]
  exact ⟨(spOver φ).left, congrArg Over.Hom.left e⟩

instance isIso_toTorsion (n : ℕ) : IsIso (t.toTorsion n) := by
  have : IsIso ((Over.forget _).map (t.toTorsion n)) :=
    isIso_of_bijective_affinePts _ fun R =>
      ⟨t.toTorsion_left_injective n R, t.toTorsion_left_surjective n R⟩
  exact isIso_of_reflects_iso _ (Over.forget _)

def torsionIso (n : ℕ) : SpAlg O (G.A n) ≅ torsion A (p ^ n) :=
  haveI := t.isIso_toTorsion n
  asIso (t.toTorsion n)

@[reassoc (attr := simp)] theorem torsionIso_hom_ι (n : ℕ) :
    (t.torsionIso n).hom ≫ torsion.ι A (p ^ n) = t.y n :=
  t.toTorsion_ι n

theorem isPullback_y : ∀ (p : ℕ) (O : Type) [CommRing O] (G : GlobalTheory.PDivGroup p O) (A : Over (Sp O))
    [GrpObj A] (t : TorsionTower G A) (n : ℕ), IsPullback (t.y n) (toUnit _) (mulN A (p ^ n)) η[A] := by
  intro p O _ G A _ t n
  exact IsPullback.of_iso_pullback ⟨t.y_comp_mulN n⟩ (t.torsionIso n) (t.torsionIso_hom_ι n)
    (pullback.lift_snd _ _ _)

end PDivGroup.TorsionTower

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterRamifiedFinite
open NumberField IsDedekindDomain Formalism.L2.Host

namespace GlobalTheory.HCharRam

theorem ram_finite : ∀ (K : Type) [Field K] [NumberField K] (χ : HChar K),
    {w : HeightOneSpectrum (𝓞 K) | ¬ χ.UnrAt w}.Finite := by
  intro K _ _ χ
  exact Filter.eventually_cofinite.1 (GlobalTheory.HeckeSplit.eventually_unrAt χ.1 χ.2.1)

end GlobalTheory.HCharRam
end
