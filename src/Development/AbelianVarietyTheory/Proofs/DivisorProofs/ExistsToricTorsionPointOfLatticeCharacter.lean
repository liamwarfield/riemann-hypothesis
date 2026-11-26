module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndOnId
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieModelIsBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelPointPairsLowerBase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyClassifiedOfFaithfullyFlat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueEqAdicSumAtImageOfZeroPair
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionPointLiesOverAfterFieldExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTateSimilitudeHeckeTranslateGeometric
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSymmetricFunctionsDegreeFactorialBasicPrope

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsToricTorsionPointOfLatticeCharacter
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsToricTorsionPointOfLatticeCharacter
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical

namespace GlobalTheory.Poinc.Sep.Spz

theorem exists_torAt : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (U : Unif (maximalIdeal V) D A G) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (k : ℕ) (z : F), 1 ≤ k → z ^ k = 1 → ∀ c : D.toPre.X →+ ℤ, ∃ x : TFK (R := V) F ⟶ A.A, TorAt U F k z c x := by
  intro V _ _ _ hB G _ _ hG D A U F _ _ _ k z hk hz c
  obtain ⟨hAdm, hChar⟩ := hB
  haveI := hChar
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hz
    exact zero_ne_one hz
  let u : Fˣ := Units.mk0 z hz0
  let τ : Multiplicative D.toPre.X →* Fˣ :=
    (zpowersHom Fˣ u).comp (AddMonoidHom.toMultiplicative c)
  have hu : u ^ k = 1 := by
    ext; simp [u, hz]
  have hτ : τ ^ k = 1 := by
    refine MonoidHom.ext fun χ => ?_
    rw [MonoidHom.pow_apply, MonoidHom.one_apply]
    simp only [τ, MonoidHom.comp_apply, zpowersHom_apply]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu, one_zpow]
  obtain ⟨q, hy, hq⟩ := GlobalTheory.ZH.TorusPerp.exists_qkPt_tor (F := F) D.tau_bimult τ hτ
  obtain ⟨f, hf⟩ := GlobalTheory.TorsionIso.torsion_eq GlobalTheory.firstFiveLaws V (maximalIdeal V) hAdm D A G hG U F k hk
  refine ⟨f q, τ, q, fun χ => ?_, hy, hq, (hf.1 q (f q)).2 rfl⟩
  simp [τ, u]

end GlobalTheory.Poinc.Sep.Spz
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsToricTorsionPointOfLatticeCharacterStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_toric_torsion_point_of_lattice_character : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (U : Unif (maximalIdeal V) D A G) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (k : ℕ) (z : F), 1 ≤ k → z ^ k = 1 → ∀ c : D.toPre.X →+ ℤ, ∃ x : TFK (R := V) F ⟶ A.A, TorAt U F k z c x := by
  first | exact @GlobalTheory.Poinc.Sep.Spz.exists_torAt | exact GlobalTheory.Poinc.Sep.Spz.exists_torAt | (intros; apply GlobalTheory.Poinc.Sep.Spz.exists_torAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothCoefficientFormsClosedUnderOperations
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothCoefficientFormsClosedUnderOperations
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

theorem smooth_coeff_closure : ∀ (n : ℕ) (v : V n), (∀ γ : Alt n, (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr ((fun _ : V n => γ) x) S) v)) ∧ (∀ (J : Type) (s : Finset J) (α : J → V n → Alt n), (∀ j ∈ s, ∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (α j x) S) v) → (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (∑ j ∈ s, α j x) S) v)) ∧ (∀ (g : V n → ℂ) (α : V n → Alt n), ContDiffAt ℝ ∞ g v → (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (α x) S) v) → (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (g x • α x) S) v)) ∧ (∀ α β : V n → Alt n, (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (α x) S) v) → (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (β x) S) v) → (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (α x * β x) S) v)) := by
  intro n v
  have hc : ∀ γ : Alt n, (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr ((fun _ : V n => γ) x) S) v) :=
    fun γ S => contDiffAt_const
  have hs : ∀ (J : Type) (s : Finset J) (α : J → V n → Alt n), (∀ j ∈ s, ∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (α j x) S) v) → (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (∑ j ∈ s, α j x) S) v) := by
    intro J s α h S
    have heq : (fun x => (bas n).repr (∑ j ∈ s, α j x) S) =
        (fun x => ∑ j ∈ s, (bas n).repr (α j x) S) := by
      funext x
      rw [map_sum]
      exact Finset.sum_apply' (s := s) (f := fun j => (bas n).repr (α j x)) (i := S)
    rw [heq]
    exact ContDiffAt.sum fun j hj => h j hj S
  have hg : ∀ (g : V n → ℂ) (α : V n → Alt n), ContDiffAt ℝ ∞ g v → (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (α x) S) v) → (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (g x • α x) S) v) := by
    intro g α h1 h2 S
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact h1.mul (h2 S)
  refine ⟨hc, hs, hg, ?_⟩
  intro α β ha hb U
  have key : ∀ x, α x * β x = ∑ S, (bas n).repr (α x) S • ∑ T, (bas n).repr (β x) T • (bas n S * bas n T) := by
    intro x
    conv_lhs => rw [← (bas n).sum_repr (α x), ← (bas n).sum_repr (β x)]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [smul_mul_assoc, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [mul_smul_comm]
  simp only [key]
  refine hs _ Finset.univ (fun S x => (bas n).repr (α x) S • ∑ T, (bas n).repr (β x) T • (bas n S * bas n T)) (fun S _ => ?_) U
  refine hg _ _ (ha S) ?_
  refine hs _ Finset.univ (fun T x => (bas n).repr (β x) T • (bas n S * bas n T)) (fun T _ => ?_)
  exact hg _ (fun _ => bas n S * bas n T) (hb T) (hc _)

end GlobalTheory.ChernCalc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothCoefficientFormsClosedUnderOperationsStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_coefficient_forms_closed_under_operations : ∀ (n : ℕ) (v : V n), (∀ γ : Alt n, (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr ((fun _ : V n => γ) x) S) v)) ∧ (∀ (J : Type) (s : Finset J) (α : J → V n → Alt n), (∀ j ∈ s, ∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (α j x) S) v) → (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (∑ j ∈ s, α j x) S) v)) ∧ (∀ (g : V n → ℂ) (α : V n → Alt n), ContDiffAt ℝ ∞ g v → (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (α x) S) v) → (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (g x • α x) S) v)) ∧ (∀ α β : V n → Alt n, (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (α x) S) v) → (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (β x) S) v) → (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (α x * β x) S) v)) := by
  first | exact @GlobalTheory.ChernCalc.smooth_coeff_closure | exact GlobalTheory.ChernCalc.smooth_coeff_closure | (intros; apply GlobalTheory.ChernCalc.smooth_coeff_closure <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalNoetherianStalkFactorOfFieldPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalNoetherianStalkFactorOfFieldPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical

namespace GlobalTheory.Poinc.Sep.Spz

theorem exists_stalk_factor : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M : RatModel o Ω), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z → ∀ (R : Subalgebra o Ω) (K : Type) [Field K] (x : Sp K ⟶ M.Z) (yK : R →+* K), (∀ a ∈ R, a ∈ M.O (x (closedPoint K))) → (∀ a : R, yK a = M.val x a) → ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsNoetherianRing O) (_ : IsIntegrallyClosed O) (_ : Algebra O Ω) (_ : IsFractionRing O Ω) (xO : Sp O ⟶ M.Z) (u : R →+* O) (v : O →+* K), spMap (algebraMap O Ω) ≫ xO = M.pt ∧ (algebraMap O Ω).comp u = R.val.toRingHom ∧ spMap v ≫ xO = x ∧ v.comp u = yK := by
  intro o Ω _ _ _ _ M hN R K _ x yK hR hy
  haveI := ArithBase.ded (o := o) (Ω := Ω)
  haveI := M.lft
  haveI : IsLocallyNoetherian M.Z := LocallyOfFiniteType.isLocallyNoetherian M.s
  haveI : IsIntegrallyClosed (M.O (x (closedPoint K))) := RatModel.isIntegrallyClosed_O (M := M) hN _
  haveI : IsNoetherianRing (M.O (x (closedPoint K))) :=
    isNoetherianRing_of_ringEquiv _ (M.stalkEquiv (x (closedPoint K)))
  have h1 : CommRingCat.ofHom (M.stalkEquiv (x (closedPoint K))).toRingHom ≫
      CommRingCat.ofHom (algebraMap (M.O (x (closedPoint K))) Ω) =
      M.Z.presheaf.stalkSpecializes (M.pt_specializes (closedPoint Ω) (x (closedPoint K))) ≫
        Scheme.stalkClosedPointTo (R := CommRingCat.of Ω) M.pt := by
    ext a; rfl
  have h3 : CommRingCat.ofHom (M.stalkEquiv (x (closedPoint K))).toRingHom ≫
      CommRingCat.ofHom (RatModel.valLoc x (x (closedPoint K)) specializes_rfl) =
      M.Z.presheaf.stalkSpecializes (specializes_rfl (x := x (closedPoint K))) ≫
        Scheme.stalkClosedPointTo (R := CommRingCat.of K) x := by
    ext a; simp [RatModel.valLoc]
  refine ⟨M.O (x (closedPoint K)), inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, spMap (M.stalkEquiv (x (closedPoint K))).toRingHom ≫ M.Z.fromSpecStalk (x (closedPoint K)),
    (Subalgebra.inclusion (fun a ha => hR a ha) : R →ₐ[o] M.O (x (closedPoint K))).toRingHom,
    RatModel.valLoc x (x (closedPoint K)) specializes_rfl, ?_, ?_, ?_, ?_⟩
  · rw [← Category.assoc, spMap, spMap, ← Spec.map_comp, h1, Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  · ext a; rfl
  · rw [← Category.assoc, spMap, spMap, ← Spec.map_comp, h3, Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  · ext a
    simp [RatModel.valLoc_eq_val, hy]

end GlobalTheory.Poinc.Sep.Spz
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalNoetherianStalkFactorOfFieldPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normalNoetherianStalk_factor_of_fieldPoint : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M : RatModel o Ω), IsNormalScheme M.Z → ∀ (R : Subalgebra o Ω) (K : Type) [Field K] (x : Sp K ⟶ M.Z) (yK : R →+* K), (∀ a ∈ R, a ∈ M.O (x (closedPoint K))) → (∀ a : R, yK a = M.val x a) → ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsNoetherianRing O) (_ : IsIntegrallyClosed O) (_ : Algebra O Ω) (_ : IsFractionRing O Ω) (xO : Sp O ⟶ M.Z) (u : R →+* O) (v : O →+* K), spMap (algebraMap O Ω) ≫ xO = M.pt ∧ (algebraMap O Ω).comp u = R.val.toRingHom ∧ spMap v ≫ xO = x ∧ v.comp u = yK := by
  first | exact @GlobalTheory.Poinc.Sep.Spz.exists_stalk_factor | exact GlobalTheory.Poinc.Sep.Spz.exists_stalk_factor | (intros; apply GlobalTheory.Poinc.Sep.Spz.exists_stalk_factor <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormDensityPullbackMatchingCharts
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormDensityPullbackMatchingCharts
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MixPull

theorem hess_pull {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
    (π : Y ⟶ X) (hπ : π ≫ p = q) (A : MLine p σ) (c : AlgChart p σ D) (c' : AlgChart q σ D)
    (H : ∀ w ∈ c'.e.source, ptMap π hπ σ w ∈ c.e.source ∧ c'.e w = c.e (ptMap π hπ σ w))
    (z : CxPts q σ) (hz : z ∈ c'.e.source) :
    c'.hess (A.pull π hπ).φ (pick (A.pull π hπ).φ.isLB z) z = c.hess A.φ (pick A.φ.isLB (ptMap π hπ σ z)) (ptMap π hπ σ z) := by
  have hz' := (H z hz).1
  have hj := mem_of_mem_linComb (m := fun _ => PtsOver.map π hπ _ z) (fun _ => rfl)
    (mem_pick (A.φ.pull π hπ).isLB z) PUnit.unit
  rw [c.hess_eq A.cInf hz' hj (mem_pick _ _)]
  show c'.hess (A.φ.pull π hπ) _ z = _
  unfold AlgChart.hess
  rw [← (H z hz).2]
  refine ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr ?_
  filter_upwards [c'.e.open_target.mem_nhds (c'.e.map_source hz)] with v hv
  have hw := c'.e.map_target hv
  obtain ⟨h₁, h₂⟩ := H _ hw
  rw [c'.e.right_inv hv] at h₂
  have e₁ : c.e.symm v = PtsOver.map π hπ (spMap σ) (c'.e.symm v) := by
    exact (congrArg c.e.symm h₂).trans (c.e.left_inv h₁)
  rw [e₁]
  exact congrArg _ (A.φ.pull_φ π hπ _ _)

theorem dens_pull : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) (π : Y ⟶ X) (hπ : π ≫ p = q) (L : Fin D → MLine p σ) (c : AlgChart p σ D) (c' : AlgChart q σ D), (∀ w ∈ c'.e.source, ptMap π hπ σ w ∈ c.e.source ∧ c'.e w = c.e (ptMap π hπ σ w)) → ∀ w ∈ c'.e.source, dens (fun i => (L i).pull π hπ) c' w = dens L c (ptMap π hπ σ w) := by
  intro k _ X Y p q σ D π hπ L c c' H w hw
  have e : ∀ τ : Equiv.Perm (Fin D), (Matrix.of fun j l =>
      c'.hess ((fun i => (L i).pull π hπ) (τ l)).φ (pick ((fun i => (L i).pull π hπ) (τ l)).φ.isLB w) w j l) =
      Matrix.of fun j l => c.hess (L (τ l)).φ (pick (L (τ l)).φ.isLB (ptMap π hπ σ w)) (ptMap π hπ σ w) j l := by
    intro τ
    ext j l
    simp only [Matrix.of_apply]
    rw [hess_pull π hπ (L (τ l)) c c' H w hw]
  simp only [dens, e]

end GlobalTheory.MixPull
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormDensityPullbackMatchingChartsStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedChernFormDensity_pullback_matching_charts : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) (π : Y ⟶ X) (hπ : π ≫ p = q) (L : Fin D → MLine p σ) (c : AlgChart p σ D) (c' : AlgChart q σ D), (∀ w ∈ c'.e.source, ptMap π hπ σ w ∈ c.e.source ∧ c'.e w = c.e (ptMap π hπ σ w)) → ∀ w ∈ c'.e.source, dens (fun i => (L i).pull π hπ) c' w = dens L c (ptMap π hπ σ w) := by
  first | exact @GlobalTheory.MixPull.dens_pull | exact GlobalTheory.MixPull.dens_pull | (intros; apply GlobalTheory.MixPull.dens_pull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionGenericFiberPullbackLocalIso
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionGenericFiberPullbackLocalIso
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
open GlobalTheory.ArInt

set_option autoImplicit false
noncomputable section

theorem GlobalTheory.Mix.exists_sec_bc : ∀ (k K : Type) [CommRing k] [Field K] [Algebra k K] [IsFractionRing k K] (X G : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [IsIntegral G] [IsLocallyNoetherian G] (p : X ⟶ Sp k) (q : G ⟶ Sp K) (j : G ⟶ X) (hp : IsPullback j q p (spMap (algebraMap k K))) (τ : K →+* ℂ), (∀ x, IsIso (j.stalkMap x)) → ∀ (M : MLine p (τ.comp (algebraMap k K))) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s), j (genericPoint G) = genericPoint X → ∃ (s' : (M.bc hp.w τ).B.Sec) (hs' : genericPoint G ∈ nonzeroLocus s'), nonzeroLocus s' = j ⁻¹ᵁ nonzeroLocus s ∧ (∀ x, (divOfSec (M.bc hp.w τ).φ.isLB s' hs').mult x = (divOfSec M.φ.isLB s hs).mult (j x)) ∧ ∀ y, (M.bc hp.w τ).logSec s' y = M.logSec s (bcPt hp.w τ y) := by
  intro k K _ _ _ _ X G _ _ _ _ p q j hp τ hiso M s hs hj
  let s' : (M.bc hp.w τ).B.Sec := Cartier.secPull s j
  have hnz : nonzeroLocus s' = j ⁻¹ᵁ nonzeroLocus s := Cartier.nonzeroLocus_secPull s j
  have hs' : genericPoint G ∈ nonzeroLocus s' := by
    rw [hnz]
    show j (genericPoint G) ∈ nonzeroLocus s
    rw [hj]
    exact hs
  refine ⟨s', hs', hnz, fun x => ?_, fun y => ?_⟩
  · have := hiso x
    let e : X.presheaf.stalk (j x) ≃+* G.presheaf.stalk x :=
      (asIso (j.stalkMap x)).commRingCatIsoToRingEquiv
    have hc : Order.coheight x = Order.coheight (j x) := by
      have := ringKrullDim_eq_of_ringEquiv e
      rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight] at this
      exact_mod_cast this.symm
    by_cases h1 : Order.coheight x = 1
    swap
    · rw [not_not.1 (mt CartierDiv.coheight_eq_one_of_mult_ne_zero h1),
        not_not.1 (mt CartierDiv.coheight_eq_one_of_mult_ne_zero (hc ▸ h1))]
    obtain ⟨i, hi⟩ := Geo.Tor.exists_chart M.φ.isLB (j x)
    have h₁ : x ∈ (M.bc hp.w τ).B.U fun _ => i := Set.mem_iInter.2 fun _ => hi
    rw [mult_divOfSec h1 h₁, mult_divOfSec (hc ▸ h1) hi]
    have hg : G.presheaf.germ _ x h₁ (s'.f fun _ => i) =
        j.stalkMap x (X.presheaf.germ _ _ hi (s.f i)) := by
      rw [Scheme.Hom.germ_stalkMap_apply]
      exact TopCat.Presheaf.germ_res_apply _ _ _ _ _
    rw [hg]
    exact congrArg (fun n : ℕ∞ => ((n.toNat : ℕ) : ℤ)) (ord_map_ringEquiv e _)
  · have hy := mem_pick M.φ.isLB (bcPt hp.w τ y)
    have hy' : y ∈ ptsIn q τ ((M.bc hp.w τ).B.U fun _ => pick M.φ.isLB (bcPt hp.w τ y)) := by
      exact mem_ptsIn.2 (Set.mem_iInter.2 fun _ => mem_ptsIn.1 hy)
    have e1 : secVal q τ s' (fun _ => pick M.φ.isLB (bcPt hp.w τ y)) y =
        secVal p (τ.comp (algebraMap k K)) s (pick M.φ.isLB (bcPt hp.w τ y)) (bcPt hp.w τ y) := by
      exact (ev_res (Cartier.pull_U M.B j _).le hy' _).trans (valR_comp y.1 j _ _).symm
    simp only [MLine.logSec]
    rw [Weight.nsq_eq _ (secVal_mem s') hy', e1]
    simp [MLine.bc, Weight.linComb, Weight.nsq]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionGenericFiberPullbackLocalIsoStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_generic_fiber_pullback_local_iso : ∀ (k K : Type) [CommRing k] [Field K] [Algebra k K] [IsFractionRing k K] (X G : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [IsIntegral G] [IsLocallyNoetherian G] (p : X ⟶ Sp k) (q : G ⟶ Sp K) (j : G ⟶ X) (hp : IsPullback j q p (spMap (algebraMap k K))) (τ : K →+* ℂ), (∀ x, IsIso (j.stalkMap x)) → ∀ (M : MLine p (τ.comp (algebraMap k K))) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s), j (genericPoint G) = genericPoint X → ∃ (s' : (M.bc hp.w τ).B.Sec) (hs' : genericPoint G ∈ nonzeroLocus s'), nonzeroLocus s' = j ⁻¹ᵁ nonzeroLocus s ∧ (∀ x, (divOfSec (M.bc hp.w τ).φ.isLB s' hs').mult x = (divOfSec M.φ.isLB s hs).mult (j x)) ∧ ∀ y, (M.bc hp.w τ).logSec s' y = M.logSec s (bcPt hp.w τ y) := by
  first | exact @GlobalTheory.Mix.exists_sec_bc | exact GlobalTheory.Mix.exists_sec_bc | (intros; apply GlobalTheory.Mix.exists_sec_bc <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalLatticeIdentificationEqId
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalLatticeIdentificationEqId
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

namespace GlobalTheory.TInj

theorem lattice_iso_eq_of_tautPts : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) (ψ : InvFun ℤ) (m N n : ℕ) (ε : (Fin m ⊕ Fin N) → LinearMap.BilinForm ℤ (Fin T.r → ℤ)), 3 ≤ n → IsCone id ψ (fun k => ε (.inl k)) → (∀ x, x ≠ 0 → ∃ k, 0 < ε (.inl k) x x) → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D₁ D₂ : DegPre V) (ω₁ : W →+* V) (s₁ : (Fin m ⊕ Fin N) → V) (e₁ : D₁.X ≃+ (Fin T.r → ℤ)) (β₁ : D₁.P.A.left ⟶ T.B.left) (ββ₁ : (G2 D₁.P.A).left ⟶ (G2 T.B).left) (w₁ : LB.Iso (abelian₂ D₁.P.A D₁.P.L) ((abelian₂ T.B T.M.L).pull ββ₁)) (ω₂ : W →+* V) (s₂ : (Fin m ⊕ Fin N) → V) (e₂ : D₂.X ≃+ (Fin T.r → ℤ)) (β₂ : D₂.P.A.left ⟶ T.B.left) (ββ₂ : (G2 D₂.P.A).left ⟶ (G2 T.B).left) (w₂ : LB.Iso (abelian₂ D₂.P.A D₂.P.L) ((abelian₂ T.B T.M.L).pull ββ₂)) (b : D₁.P.A ⟶ D₂.P.A) (φ : D₁.X ≃+ D₂.X) (F : Type) [Field F] [Algebra (FractionRing V) F], D₁.TauBimult → D₂.TauBimult → From T ω₁ s₁ ε n D₁ e₁ β₁ ββ₁ w₁ → From T ω₂ s₂ ε n D₂ e₂ β₂ ββ₂ w₂ → (∀ k, s₁ (.inl k) ∈ maximalIdeal V ∧ s₁ (.inl k) ≠ 0) → (∀ k, IsUnit (s₁ (.inr k))) → (∀ k, s₂ (.inl k) ∈ maximalIdeal V ∧ s₂ (.inl k) ≠ 0) → (∀ k, IsUnit (s₂ (.inr k))) → Match D₁ D₂ b φ F → (∀ a : Fin T.r → ℤ, ∃ (p₁ : QkPt D₁ F n) (p₂ : QkPt D₂ F n), p₁.y = e₁.symm a ∧ TautPt T ω₁ s₁ ε n D₁ e₁ β₁ ββ₁ w₁ F a p₁.g ∧ p₂.y = e₂.symm a ∧ TautPt T ω₂ s₂ ε n D₂ e₂ β₂ ββ₂ w₂ F a p₂.g ∧ QImg b φ p₁ p₂) → ∀ y, e₂ (φ y) = e₁ y := by
  intro o W _ _ _ T ψ m N n ε hn hcone hdef V _ _ _ D₁ D₂ ω₁ s₁ e₁ β₁ ββ₁ w₁ ω₂ s₂ e₂ β₂ ββ₂ w₂ b φ F _ _ hτ₁ hτ₂ hF₁ hF₂
    hs₁ hu₁ hs₂ hu₂ hM hpts
  let ga : (Fin T.r → ℤ) ≃ₗ[ℤ] (Fin T.r → ℤ) := ((e₁.symm.trans φ).trans e₂).toIntLinearEquiv
  have hga : ∀ a, ga a = e₂ (φ (e₁.symm a)) := fun _ => rfl

  have hcong : ∀ a, GlobalTheory.Poinc.CongMod n (ga a) a := by
    intro a
    obtain ⟨p₁, p₂, hy₁, -, hy₂, -, p', hp', -, z, hz, -⟩ := hpts a
    have h : e₂ p₂.y = e₂ (φ p₁.y) + n • e₂ z := by rw [hz, map_add (f := _), hp', map_nsmul]
    rw [hy₂, hy₁, AddEquiv.apply_symm_apply] at h
    refine ⟨-(e₂ z), ?_⟩
    rw [smul_neg, eq_add_neg_iff_add_eq, hga]
    exact h.symm

  have hpu := GlobalTheory.T.tautologicalBase_matching_monomials_ratio_unit T ε n V D₁ D₂ ω₁ s₁ e₁ β₁ ββ₁ w₁ ω₂ s₂ e₂ β₂ ββ₂ w₂ b φ F hτ₁ hτ₂ hF₁ hF₂ hM
  have hab : ∀ a b, ∃ u : Vˣ, ∏ i, algebraMap V (FractionRing V) (s₂ i) ^ ((n : ℤ) * ε i (ga a) (ga b)) =
      algebraMap V (FractionRing V) u * ∏ i, algebraMap V (FractionRing V) (s₁ i) ^ ((n : ℤ) * ε i a b) := by
    intro a b
    obtain ⟨u, hu⟩ := hpu (e₁.symm a) (e₁.symm b)
    rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply] at hu
    exact ⟨u, hu⟩
  obtain ⟨c₁, c₂, hc₁, hc₂, hsum⟩ := GlobalTheory.T.monomials_differ_by_units_positive_boundaryCombination V T.r m N n (by omega) ε s₁ s₂ ga hs₁ hu₁ hs₂ hu₂ hab
  have hS := GlobalTheory.T.smoothCone_sum_generators_eq_of_common_interiorPoint ψ (Fin T.r → ℤ) m m (fun k => ε (.inl k)) (fun k => pull ga.toLinearMap (ε (.inl k))) hcone
    (hcone.pull_equiv ga) c₁ c₂ hc₁ hc₂ hsum

  have he : ∀ x y, (∑ k, ε (.inl k)) (ga x) (ga y) = (∑ k, ε (.inl k)) x y := by
    intro x y
    have h := LinearMap.congr_fun₂ hS x y
    simp only [LinearMap.sum_apply, pull_apply, LinearEquiv.coe_coe] at h ⊢
    exact h.symm
  have hpos : ∀ x, x ≠ 0 → 0 < (∑ k, ε (.inl k)) x x := by
    intro x hx
    obtain ⟨k, hk⟩ := hdef x hx
    simp only [LinearMap.sum_apply]
    exact Finset.sum_pos' (fun i _ => hcone.nonneg i x) ⟨k, Finset.mem_univ _, hk⟩
  have hrefl := GlobalTheory.Poinc.eq_refl_of_isometry_congMod (Fin T.r → ℤ) (∑ k, ε (.inl k)) hpos ga he n hn hcong
  intro y
  have h := DFunLike.congr_fun hrefl (e₁ y)
  rw [hga, AddEquiv.symm_apply_apply, LinearEquiv.refl_apply] at h
  exact h

end GlobalTheory.TInj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalLatticeIdentificationEqIdStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tautological_lattice_identification_eq_id : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) (ψ : InvFun ℤ) (m N n : ℕ) (ε : (Fin m ⊕ Fin N) → LinearMap.BilinForm ℤ (Fin T.r → ℤ)), 3 ≤ n → IsCone id ψ (fun k => ε (.inl k)) → (∀ x, x ≠ 0 → ∃ k, 0 < ε (.inl k) x x) → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D₁ D₂ : DegPre V) (ω₁ : W →+* V) (s₁ : (Fin m ⊕ Fin N) → V) (e₁ : D₁.X ≃+ (Fin T.r → ℤ)) (β₁ : D₁.P.A.left ⟶ T.B.left) (ββ₁ : (G2 D₁.P.A).left ⟶ (G2 T.B).left) (w₁ : LB.Iso (abelian₂ D₁.P.A D₁.P.L) ((abelian₂ T.B T.M.L).pull ββ₁)) (ω₂ : W →+* V) (s₂ : (Fin m ⊕ Fin N) → V) (e₂ : D₂.X ≃+ (Fin T.r → ℤ)) (β₂ : D₂.P.A.left ⟶ T.B.left) (ββ₂ : (G2 D₂.P.A).left ⟶ (G2 T.B).left) (w₂ : LB.Iso (abelian₂ D₂.P.A D₂.P.L) ((abelian₂ T.B T.M.L).pull ββ₂)) (b : D₁.P.A ⟶ D₂.P.A) (φ : D₁.X ≃+ D₂.X) (F : Type) [Field F] [Algebra (FractionRing V) F], D₁.TauBimult → D₂.TauBimult → From T ω₁ s₁ ε n D₁ e₁ β₁ ββ₁ w₁ → From T ω₂ s₂ ε n D₂ e₂ β₂ ββ₂ w₂ → (∀ k, s₁ (.inl k) ∈ maximalIdeal V ∧ s₁ (.inl k) ≠ 0) → (∀ k, IsUnit (s₁ (.inr k))) → (∀ k, s₂ (.inl k) ∈ maximalIdeal V ∧ s₂ (.inl k) ≠ 0) → (∀ k, IsUnit (s₂ (.inr k))) → Match D₁ D₂ b φ F → (∀ a : Fin T.r → ℤ, ∃ (p₁ : QkPt D₁ F n) (p₂ : QkPt D₂ F n), p₁.y = e₁.symm a ∧ TautPt T ω₁ s₁ ε n D₁ e₁ β₁ ββ₁ w₁ F a p₁.g ∧ p₂.y = e₂.symm a ∧ TautPt T ω₂ s₂ ε n D₂ e₂ β₂ ββ₂ w₂ F a p₂.g ∧ QImg b φ p₁ p₂) → ∀ y, e₂ (φ y) = e₁ y := by
  first | exact @GlobalTheory.TInj.lattice_iso_eq_of_tautPts | exact GlobalTheory.TInj.lattice_iso_eq_of_tautPts | (intros; apply GlobalTheory.TInj.lattice_iso_eq_of_tautPts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusPairOfTorsionPointOver
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusPairOfTorsionPointOver
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

open GlobalTheory.Poinc.Tors

noncomputable section

namespace GlobalTheory.Poinc.Sep.LiesPair

theorem exists_pair_of_liesOver : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V) D A G) (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ N : ℕ, 1 ≤ N → ∀ (g : GtPtF D.toPre (FractionRing V)) (w : Frm D.toPre (FractionRing V) 1 g.b) (x : TFK (R := V) (FractionRing V) ⟶ A.A) (fr : FrAt x), (∃ o, GtPtF.IsNsmul N g o ∧ o.IsZero) → w.IsGen → fr.IsGen → LiesOver U.toUnifPre w₀ g w x fr → ∃ p : QkPt D.toPre (FractionRing V) N, p.y = 0 ∧ p.g = g ∧ QkToAkU U.toUnifPre (FractionRing V) N p x := by
  intro V _ _ _ hCN D A G _ _ hG U w₀ hw₀ N hN g w x fr hg hw hfr hov
  haveI : CharZero V := hCN.2.2.2
  have hL : GlobalTheory.UT.LL := GlobalTheory.firstFiveLaws
  have hA : AdmBase V (maximalIdeal V) := ⟨hCN.1, inferInstance, hCN.2.1, hCN.2.2.1⟩
  have hB := D.tau_bimult
  obtain ⟨o, ho₁, ho₂⟩ := hg
  let p : QkPt D.toPre (FractionRing V) N :=
    ⟨0, g, o, ho₁, GlobalTheory.TorsionQk.isIota_zero hB ho₂⟩
  obtain ⟨pb, hp⟩ := qkExtExists V D.toPre (FractionRing V)
    (AlgebraicClosure (FractionRing V)) (algebraMap _ _) (fun r => by simp) N p
  let xb : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ A.A :=
    GlobalTheory.TorsionExt.fieldMap (FractionRing V) (AlgebraicClosure (FractionRing V)) ≫ x
  obtain ⟨wb, frb, hwb, hfrb, hlb⟩ := GlobalTheory.T.torusExtension_point_liesOver_after_field_extension V _ hA D A G hG U (AlgebraicClosure (FractionRing V)) w₀
    hw₀ g w x fr hw hfr hov xb rfl
  obtain ⟨f', f₁, -⟩ := GlobalTheory.TorsionIso.torsion_eq hL V _ hA D A G hG U (AlgebraicClosure (FractionRing V)) N hN
  have hq := (f₁ pb (f' pb)).2 rfl
  obtain ⟨w', fr', hw', hfr', hl'⟩ := GlobalTheory.Poinc.Tors.ValPair.liesOver_of_qkToAkU V _ hA D A G hG U
    (AlgebraicClosure (FractionRing V)) w₀ hw₀ _ hN pb (f' pb) hp.1 hq
  have hpb := (GlobalTheory.TorusExt.eq_gtExt_iff _ (RingHom.comp_id _) _ _).2 hp.2
  obtain ⟨wb₂, hwb₂, hlb₂⟩ : ∃ wb₂ : Frm D.toPre (AlgebraicClosure (FractionRing V)) 1 pb.g.b,
      wb₂.IsGen ∧ LiesOver U.toUnifPre w₀ pb.g wb₂ xb frb := by
    rw [hpb]
    exact ⟨wb, hwb, hlb⟩
  have e := GlobalTheory.Poinc.Tors.OneOver.eq_of_liesOver hL V _ hA D A G hG U (AlgebraicClosure (FractionRing V)) w₀ hw₀
    pb.g wb₂ w' xb (f' pb) frb fr' hwb₂ hw' hfrb hfr' hlb₂ hl'
  refine ⟨p, rfl, rfl, ?_⟩
  refine (GlobalTheory.TorsionExt.qkToAkU_iff_of_algebra hL.1.globalFns hL.1.kerPow U hN hp x).2 ?_
  rw [← e] at hq
  exact hq

end GlobalTheory.Poinc.Sep.LiesPair
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusPairOfTorsionPointOverStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

open GlobalTheory.Poinc.Tors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torus_pair_of_torsion_point_over : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V) D A G) (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ N : ℕ, 1 ≤ N → ∀ (g : GtPtF D.toPre (FractionRing V)) (w : Frm D.toPre (FractionRing V) 1 g.b) (x : TFK (R := V) (FractionRing V) ⟶ A.A) (fr : FrAt x), (∃ o, GtPtF.IsNsmul N g o ∧ o.IsZero) → w.IsGen → fr.IsGen → LiesOver U.toUnifPre w₀ g w x fr → ∃ p : QkPt D.toPre (FractionRing V) N, p.y = 0 ∧ p.g = g ∧ QkToAkU U.toUnifPre (FractionRing V) N p x := by
  first | exact @GlobalTheory.Poinc.Sep.LiesPair.exists_pair_of_liesOver | exact GlobalTheory.Poinc.Sep.LiesPair.exists_pair_of_liesOver | (intros; apply GlobalTheory.Poinc.Sep.LiesPair.exists_pair_of_liesOver <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelDbarAdditiveComplexLinearOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelDbarAdditiveComplexLinearOne
set_option autoImplicit false

open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

namespace GlobalTheory.CxForm.GlobLin

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

theorem loc_add (α β : A.Fld) (i : A.ι) : A.loc (α + β) i = fun v => A.loc α i v + A.loc β i v := by
  funext v
  unfold HolAtlas.loc
  split_ifs
  exacts [rfl, (add_zero _).symm]

theorem loc_smul (c : ℂ) (α : A.Fld) (i : A.ι) : A.loc (c • α) i = fun v => c • A.loc α i v := by
  funext v
  unfold HolAtlas.loc
  split_ifs
  exacts [rfl, (smul_zero _).symm]

theorem target_mem_nhds (x : A.Pt) : (A.e x.1.1).target ∈ 𝓝 x.crd :=
  (A.e x.1.1).open_target.mem_nhds (x.ch.map_source x.2)

theorem differentiableAt_coef {α : A.Fld} (h : A.IsForm α) (x : A.Pt) (S : Finset (Fin (n + n))) :
    DifferentiableAt ℝ (fun v => (bas n).repr (A.loc α x.1.1 v) S) x.crd :=
  ((h.smooth x.1.1 S).contDiffAt (target_mem_nhds A x)).differentiableAt (by simp)

theorem loc_one_eventuallyEq (x : A.Pt) : A.loc 1 x.1.1 =ᶠ[𝓝 x.crd] fun _ => 1 :=
  Filter.eventually_of_mem (target_mem_nhds A x) fun v hv => by
    rw [HolAtlas.loc, dite_eq_left hv]
    rfl

end GlobalTheory.CxForm.GlobLin


open GlobalTheory.CxForm.GlobLin in
theorem GlobalTheory.CxForm.HolAtlas.del_dbar_linear : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n),
    (A.del 1 = 0 ∧ A.dbar 1 = 0) ∧
    ∀ (c : ℂ) (α β : A.Fld), A.IsForm α → A.IsForm β →
      A.del (α + β) = A.del α + A.del β ∧ A.dbar (α + β) = A.dbar α + A.dbar β ∧
      A.del (c • α) = c • A.del α ∧ A.dbar (c • α) = c • A.dbar α := by
  intro M _ n A
  refine ⟨⟨funext fun x => ?_, funext fun x => ?_⟩, fun c α β hα hβ =>
    ⟨funext fun x => ?_, funext fun x => ?_, funext fun x => ?_, funext fun x => ?_⟩⟩
  all_goals obtain ⟨hadd, hsmul, -, hgerm, hconst⟩ := GlobalTheory.T.delOperatorAt_dbarOperatorAt_linear_local n x.crd
  · exact (hgerm _ _ (loc_one_eventuallyEq A x)).1.trans (hconst 1).1
  · exact (hgerm _ _ (loc_one_eventuallyEq A x)).2.trans (hconst 1).2
  · rw [HolAtlas.del, loc_add]
    exact (hadd _ _ (differentiableAt_coef A hα x) (differentiableAt_coef A hβ x)).1
  · rw [HolAtlas.dbar, loc_add]
    exact (hadd _ _ (differentiableAt_coef A hα x) (differentiableAt_coef A hβ x)).2
  · rw [HolAtlas.del, loc_smul]
    exact (hsmul _ c (differentiableAt_coef A hα x)).1
  · rw [HolAtlas.dbar, loc_smul]
    exact (hsmul _ c (differentiableAt_coef A hα x)).2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelDbarAdditiveComplexLinearOneStatement
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.del_dbar_additive_complexLinear_one : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n), (A.del 1 = 0 ∧ A.dbar 1 = 0) ∧
    ∀ (c : ℂ) (α β : A.Fld), A.IsForm α → A.IsForm β →
      A.del (α + β) = A.del α + A.del β ∧ A.dbar (α + β) = A.dbar α + A.dbar β ∧
      A.del (c • α) = c • A.del α ∧ A.dbar (c • α) = c • A.dbar α := by
  exact @GlobalTheory.CxForm.HolAtlas.del_dbar_linear
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricBiextensionHypPullbackOfGroupPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricBiextensionHypPullbackOfGroupPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.ActFin.QHypPull

theorem sq_comm {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} {φ : A'.left ⟶ A.left}
    {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left} (hs : IsSquare φ φ₂) {X : Scheme.{0}} (u' : X ⟶ (A' ⊗ A').left)
    (u : X ⟶ (A ⊗ A).left)
    (h1 : u' ≫ (fst A' A').left ≫ φ = u ≫ (fst A A).left) (h2 : u' ≫ (snd A' A').left ≫ φ = u ≫ (snd A A).left) :
    u' ≫ φ₂ = u := by
  apply pullback.hom_ext
  · show _ ≫ (fst A A).left = _ ≫ (fst A A).left
    rw [Category.assoc, hs.1, h1]
  · show _ ≫ (snd A A).left = _ ≫ (snd A A).left
    rw [Category.assoc, hs.2, h2]

end GlobalTheory.ActFin.QHypPull


open GlobalTheory.ActFin.QHypPull in
theorem GlobalTheory.ActFin.qHyp_pull_of_isGrpPullback : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (A : Over S) [GrpObj A] [IsCommMonObj A] (A' : Over S') [GrpObj A'] (φ : A'.left ⟶ A.left) (φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left) (Q : LB (A ⊗ A).left), IsGrpPullback A' A f φ → IsSquare φ φ₂ → QHyp A Q → QHyp A' (Q.pull φ₂) := by
  intro S S' f A _ _ A' _ φ φ₂ Q h hs hQ
  obtain ⟨hA, hL, ⟨t₁, ht₁⟩, ⟨t₂, ht₂⟩, hsym, hD⟩ := hQ
  haveI : IsCommMonObj A' := GlobalTheory.isCommMonObj_of_grpPullback S S' A A' f φ h
  have hone : (1 : A' ⟶ A').left ≫ φ = φ ≫ (1 : A ⟶ A).left := by
    rw [GlobalTheory.FlatModel.LiftW.one_left_comp_of_isGrpPullback h A', GlobalTheory.FlatModel.LiftW.one_left_eq,
      GlobalTheory.FlatModel.LiftW.one_left_eq, ← Category.assoc, h.1.w]
    rfl
  have fl : ∀ {T : Over S'} (a b : T ⟶ A'), (lift a b).left ≫ (fst A' A').left = a.left := fun a b => by
    rw [← Over.comp_left, lift_fst]
  have sl : ∀ {T : Over S'} (a b : T ⟶ A'), (lift a b).left ≫ (snd A' A').left = b.left := fun a b => by
    rw [← Over.comp_left, lift_snd]
  have fl' : ∀ {T : Over S} (a b : T ⟶ A), (lift a b).left ≫ (fst A A).left = a.left := fun a b => by
    rw [← Over.comp_left, lift_fst]
  have sl' : ∀ {T : Over S} (a b : T ⟶ A), (lift a b).left ≫ (snd A A).left = b.left := fun a b => by
    rw [← Over.comp_left, lift_snd]
  have e₁ : (lift (1 : A' ⟶ A') (𝟙 A')).left ≫ φ₂ = φ ≫ (lift (1 : A ⟶ A) (𝟙 A)).left :=
    sq_comm hs _ _ (by rw [← Category.assoc, fl, hone, Category.assoc, fl'])
      (by rw [← Category.assoc, sl, Category.assoc, sl']; rfl)
  have e₂ : (lift (𝟙 A') (1 : A' ⟶ A')).left ≫ φ₂ = φ ≫ (lift (𝟙 A) (1 : A ⟶ A)).left :=
    sq_comm hs _ _ (by rw [← Category.assoc, fl, Category.assoc, fl']; rfl)
      (by rw [← Category.assoc, sl, hone, Category.assoc, sl'])
  have e₃ : (lift (snd A' A') (fst A' A')).left ≫ φ₂ = φ₂ ≫ (lift (snd A A) (fst A A)).left :=
    sq_comm hs _ _ (by rw [← Category.assoc, fl, Category.assoc, fl', hs.2])
      (by rw [← Category.assoc, sl, Category.assoc, sl', hs.1])
  haveI := hA.proper
  refine ⟨⟨inferInstance, MorphismProperty.of_isPullback (P := @Smooth) h.1 hA.smooth,
    MorphismProperty.of_isPullback (P := @IsProper) h.1 hA.proper,
    MorphismProperty.of_isPullback (P := @GeometricallyConnected) h.1 hA.geomConnected⟩,
    pull_isLB hL φ₂, ?_, ?_, ?_, ?_⟩
  · exact gen_chartPull (chartPullLinComb Q φ₂ (fun _ : PUnit => (lift (1 : A' ⟶ A') (𝟙 A')).left)
      (fun _ => (lift (1 : A ⟶ A) (𝟙 A)).left) (fun _ => 1) φ (fun _ => e₁)) t₁ ht₁
  · exact gen_chartPull (chartPullLinComb Q φ₂ (fun _ : PUnit => (lift (𝟙 A') (1 : A' ⟶ A')).left)
      (fun _ => (lift (𝟙 A) (1 : A ⟶ A)).left) (fun _ => 1) φ (fun _ => e₂)) t₂ ht₂
  · exact LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull Q φ₂ φ₂ rfl) (chartPullLinComb Q φ₂
      (fun _ : PUnit => (lift (snd A' A') (fst A' A')).left) (fun _ => (lift (snd A A) (fst A A)).left)
      (fun _ => 1) φ₂ (fun _ => e₃)) hsym
  · exact GlobalTheory.DiagAmpleBC.relAmple_diag_pull S S' A hA Q hL hD f A' φ φ₂ h.1 hs
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricBiextensionHypPullbackOfGroupPullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetricBiextensionHyp_pullback_of_groupPullback : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (A : Over S) [GrpObj A] [IsCommMonObj A] (A' : Over S') [GrpObj A'] (φ : A'.left ⟶ A.left) (φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left) (Q : LB (A ⊗ A).left), IsGrpPullback A' A f φ → IsSquare φ φ₂ → QHyp A Q → QHyp A' (Q.pull φ₂) := by
  first | exact @GlobalTheory.ActFin.qHyp_pull_of_isGrpPullback | exact GlobalTheory.ActFin.qHyp_pull_of_isGrpPullback | (intros; apply GlobalTheory.ActFin.qHyp_pull_of_isGrpPullback <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightLatticeSpanEq
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.GenShift

open IsDedekindDomain ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw

section General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}
  {Z : Comp Xo c}

theorem exists_twPow (s : TwSec U x Z (wtOf Dw 0 1)) : ∀ n : ℕ, Nonempty (TwSec U x Z (wtOf Dw 0 (n : ℤ))) := by
  intro n
  induction n with
  | zero => exact ⟨(TwSec.const x s.pts 1 one_ne_zero).copy (by rw [Nat.cast_zero, wtOf_zero])⟩
  | succ n ih =>
    obtain ⟨t⟩ := ih
    exact ⟨(t.mul s).copy (by rw [← wtOf_add, add_zero, Nat.cast_succ])⟩


set_option maxHeartbeats 1000000 in
theorem span_latW_add (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) (G G₀ : WTZ E) (hG : Even G.2)
    (hs : ∀ Z : Comp Xo c, Nonempty (TwSec U x Z G₀))
    (h : Submodule.span c.F (latW U G : Set (cuspW Xo c U G)) = ⊤) :
    Submodule.span c.F (latW U (G + G₀) : Set (cuspW Xo c U (G + G₀))) = ⊤ := by
  classical
  haveI := CompFin.finite_comp Xo c
  haveI := Fintype.ofFinite (Comp Xo c)
  rw [eq_top_iff]
  intro F _
  have hF : F = ∑ Z : Comp Xo c,
      (⟨idem Z * (F : Rul Xo c), GlobalTheory.CompRestr.idem_mul_mem_cuspW hU Z F.2⟩ : cuspW Xo c U (G + G₀)) := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    exact (sum_idem_mul _).symm
  rw [hF]
  refine Submodule.sum_mem _ fun Z _ => ?_
  obtain ⟨s⟩ := hs Z
  obtain ⟨φ, -, -, hA, -⟩ := GlobalTheory.FlatTw.Mul.twSec_mulEquiv_integral E H Dw l Xo c r U x Z G₀ s G hG
  obtain ⟨a, ha0, hlo, -⟩ := GlobalTheory.FlatTw.Good.exists_twist_scalar s
  let p : cuspOn U Z (G + G₀) := ⟨idem Z * (F : Rul Xo c),
    GlobalTheory.CompRestr.idem_mul_mem_cuspW hU Z F.2, by rw [mul_comm]; exact mul_mem_suppOn _ (idem_mem_suppOn Z)⟩
  let g : cuspOn U Z G := φ.symm p
  have hmem : (⟨(g : Rul Xo c), g.2.1⟩ : cuspW Xo c U G) ∈ Submodule.span c.F (latW U G : Set (cuspW Xo c U G)) := by
    rw [h]; trivial
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 c.F)) c.F _ _ hmem
  rw [Submodule.span_eq, Submonoid.smul_def, ← algebraMap_smul c.F] at ht
  set d : c.F := algebraMap (𝓞 c.F) c.F t with hd
  have hd0 : d ≠ 0 := by simpa [hd] using nonZeroDivisors.ne_zero t.2
  have hf : d • g ∈ latOn U Z G := (mem_latOn U).2 ht
  have hq := hA a ha0 hlo (d • g) hf ((a * d) • p) (by
    simp only [g, map_smul, LinearEquiv.apply_symm_apply, Submodule.coe_smul, smul_smul])
  have hq' := (mem_latOn U).1 hq
  have had : a * d ≠ 0 := mul_ne_zero ha0 hd0
  have e : (⟨idem Z * (F : Rul Xo c), GlobalTheory.CompRestr.idem_mul_mem_cuspW hU Z F.2⟩ : cuspW Xo c U (G + G₀)) =
      (a * d)⁻¹ • (⟨(((a * d) • p : cuspOn U Z (G + G₀)) : Rul Xo c), ((a * d) • p).2.1⟩ : cuspW Xo c U (G + G₀)) := by
    apply Subtype.ext
    simp only [Submodule.coe_smul, smul_smul, inv_mul_cancel₀ had, one_smul, p]
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hq')

end General

end GlobalTheory.GenShift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeEqOneOfComp
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt GlobalTheory.VB GlobalTheory.GenSmoothCover

namespace GlobalTheory.GenRes

theorem bijective_residueFieldMap {A B : Scheme.{0}} (f : A ⟶ B) [SurjectiveOnStalks f] (x : A) :
    Function.Bijective (f.residueFieldMap x).hom := by
  refine ⟨RingHom.injective _, fun a => ?_⟩
  obtain ⟨b, rfl⟩ := A.residue_surjective x a
  obtain ⟨c, rfl⟩ := f.stalkMap_surjective x b
  exact ⟨B.residue _ c, congr($(Scheme.residue_residueFieldMap f x).hom c)⟩

theorem residueDegree_eq_one_of_comp {A B C : Scheme.{0}} (g : A ⟶ B) (c : B ⟶ C) (a : A)
    (h : Function.Bijective ((g ≫ c).residueFieldMap a).hom) : c.residueDegree (g a) = 1 := by
  rw [Scheme.residueFieldMap_comp] at h
  have hs : Function.Surjective (c.residueFieldMap (g a)).hom := fun y => by
    obtain ⟨x, hx⟩ := h.2 ((g.residueFieldMap a).hom y)
    exact ⟨x, (g.residueFieldMap a).hom.injective hx⟩
  have hb : Function.Bijective (c.residueFieldMap (g a)).hom := ⟨RingHom.injective _, hs⟩
  letI := (c.residueFieldMap (g a)).hom.toAlgebra
  unfold Scheme.Hom.residueDegree
  exact (LinearEquiv.finrank_eq (AlgEquiv.ofBijective (Algebra.ofId _ _) hb).toLinearEquiv).symm.trans
    (Module.finrank_self _)

theorem exists_birational_genSmooth : GlobalTheory.Published.Principalisation → ∀ (k : Type) [CommRing k] (X : Scheme.{0})
    [IsIntegral X] (p : X ⟶ Sp k) (d : ℕ), IsArithVar p d → ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (ρ : Y ⟶ X),
      IsArithVar (ρ ≫ p) d ∧ GenSmooth (ρ ≫ p) d ∧ ρ (genericPoint Y) = genericPoint X ∧
        ρ.residueDegree (genericPoint Y) = 1 := by
  intro hP k _ X _ p D h
  have := h.isDomain
  have := h.finite
  have := h.charZero_base
  have := h.isNoetherianRing
  let K := FractionRing k
  have G := IsPullback.of_hasPullback p (spMap (algebraMap k K))
  set f := pullback.fst p (spMap (algebraMap k K))
  set q := pullback.snd p (spMap (algebraMap k K))
  obtain ⟨_, hd, hf⟩ := genericFibre h G
  have hq : IsProjOver q := ProjSpace.isProjOver_of_isPullback_spMap _ G h.isProjOver
  obtain ⟨W, s, U, _, hsm, hW, hU, hiso⟩ := WeakRes.weak_resolution hP K _ q D hq hd
  have : IsProper q := CommonModel.isProper_of_isProjOver hq
  have : IsProper (s ≫ q) := CommonModel.isProper_of_isProjOver hW
  have hdW : topologicalKrullDim W = D :=
    (OpenDim.topologicalKrullDim_eq_of_isIso_restrict K _ W q (s ≫ q) s inferInstance inferInstance rfl U hU hiso).trans hd
  obtain ⟨Y, ρ, _, j, hj, hY, H, _, _⟩ := exists_closure h.isProjOver (s ≫ f) (s ≫ q)
    (by rw [Category.assoc, Category.assoc, G.w]) hW
  have : IsProper (ρ ≫ p) := CommonModel.isProper_of_isProjOver hY
  have : IsFinite (spMap (Int.castRingHom k)) := (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 h.finite)
  have H' := H.paste_vert (isPullback_rat k K)
  have : Flat (j ≫ (ρ ≫ p) ≫ spMap (Int.castRingHom k)) := flat_of_over_fractionField (K := ℚ) _ _ H'.w.symm
  have hfl : Flat ((ρ ≫ p) ≫ spMap (Int.castRingHom k)) := flat_of_schemeDominant_of_isDedekindDomain j _
  have hA : IsArithVar (ρ ≫ p) D :=
    ⟨h.isDomain, h.finite, ‹_›, hY, hfl, IntModel.topologicalKrullDim_eq_succ Int.not_isField H' hdW⟩
  obtain ⟨_, -, hjη⟩ := genericFibre hA H
  obtain ⟨x, hx⟩ := hU
  have : Nonempty (s ⁻¹ᵁ U : W.Opens).toScheme := ⟨inv (s ∣_ U) ⟨x, hx⟩⟩
  have : IsIntegral (s ⁻¹ᵁ U : W.Opens).toScheme := isIntegral_of_isOpenImmersion (s ⁻¹ᵁ U).ι
  have e : ((s ⁻¹ᵁ U).ι ≫ j) ≫ ρ = (s ∣_ U ≫ U.ι) ≫ f := by
    rw [Category.assoc, hj, morphismRestrict_ι, Category.assoc]
  have eη : ((s ⁻¹ᵁ U).ι ≫ j) (genericPoint _) = genericPoint Y := by
    rw [Scheme.Hom.comp_apply, genericPoint_eq_of_isOpenImmersion, hjη]
  have := IsPreimmersion.of_isLocalization (R := k) (S := K) (nonZeroDivisors k)
  have : IsPreimmersion f := MorphismProperty.of_isPullback G.flip this
  refine ⟨Y, ‹_›, ρ, hA, fun σ => ?_, ?_, ?_⟩
  · have : LocallyOfFinitePresentation (ρ ≫ p) := inferInstance
    exact ⟨⟨AlgChart (ρ ≫ p) σ D, id, ModelCharts.exists_chart H (RegGenSmooth.injective_of_charZero σ)⟩⟩
  · rw [← eη, ← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply, genericPoint_eq_of_isOpenImmersion, hf]
  · have : SurjectiveOnStalks (((s ⁻¹ᵁ U).ι ≫ j) ≫ ρ) := by rw [e]; infer_instance
    rw [← eη]
    exact residueDegree_eq_one_of_comp _ ρ _ (bijective_residueFieldMap _ _)

end GlobalTheory.GenRes
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusSpreadLatticeMapSurjective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusSpreadLatticeMapSurjective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Poinc.Sep.Spz

theorem pullback_map_eq_of_pullTorus_eq {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G']
    {p : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G p φ) {X : Type} [AddCommGroup X]
    (f g : splitTorus S X ⟶ G) (e : GlobalTheory.TorusPart.pullTorus h f = GlobalTheory.TorusPart.pullTorus h g) :
    (Over.pullback p).map f = (Over.pullback p).map g := by
  have k : GlobalTheory.SplitTorus.bcMap p X ≫ f.left = GlobalTheory.SplitTorus.bcMap p X ≫ g.left := by
    rw [← GlobalTheory.TorusPart.pullTorus_left h f, ← GlobalTheory.TorusPart.pullTorus_left h g, e]
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [Over.pullback_map_left, pullback.lift_fst]
    rw [← GlobalTheory.SplitTorus.bcIso_inv_bcMap, Category.assoc, Category.assoc, k]
  · simp only [Over.pullback_map_left, pullback.lift_snd]

theorem spread₂_surjective : ∀ (B : Scheme.{0}) (H : Over B) [GrpObj H] [IsCommMonObj H], IsSemiAbelian H → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], GlobalTheory.Mum.Base V₁ → ∀ (G₁ : Over (Sp V₁)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (D₁ : DegData V₁ (maximalIdeal V₁)) (A₁ : PolAV (Sp (FractionRing V₁))) (U₁ : Unif (maximalIdeal V₁) D₁ A₁ G₁) (ξ₁ : Sp V₁ ⟶ B) (β₁ : G₁.left ⟶ H.left), IsGrpPullback G₁ H ξ₁ β₁ → ∀ (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂], GlobalTheory.Mum.Base V₂ → ∀ (G₂ : Over (Sp V₂)) [GrpObj G₂] [IsCommMonObj G₂], IsSemiAbelian G₂ → ∀ (D₂ : DegData V₂ (maximalIdeal V₂)) (A₂ : PolAV (Sp (FractionRing V₂))) (U₂ : Unif (maximalIdeal V₂) D₂ A₂ G₂) (ξ₂ : Sp V₂ ⟶ B) (β₂ : G₂.left ⟶ H.left), IsGrpPullback G₂ H ξ₂ β₂ → ∀ ρ : D₂.toPre.X →+ D₁.toPre.X, Spread₂ H U₁ ξ₁ β₁ U₂ ξ₂ β₂ ρ → Function.Surjective ρ := by
  intro B H _ _ hH V₁ _ _ _ _ G₁ _ _ _ D₁ A₁ U₁ ξ₁ β₁ _ V₂ _ _ _ _ G₂ _ _ _ D₂ A₂ U₂ ξ₂ β₂ _ ρ hS
  obtain ⟨W, _, _, _, ψ, GW, _, _, φW, j, Ω, _, α, b₁, hb₁, GΩ, _, n, hn, n₁, hn₁, κ, _, c, b₂, hb₂, Gκ, _, m, hm,
    m₂, hm₂, hGW, hj, -, hc, -, -, -, -, hΩj, hκj⟩ := hS
  by_contra hρ
  have hM : ρ.range ≠ ⊤ := fun h => hρ (AddMonoidHom.range_eq_top.1 h)
  obtain ⟨F, _, _, l, hl0, hl⟩ := GlobalTheory.TorusOnto.exists_finite_quotient_ne_zero ρ.range hM
  have hlρ : l.comp ρ = 0 := AddMonoidHom.ext fun x => hl _ ⟨x, rfl⟩
  haveI := hj
  let f : splitTorus (Sp W) F ⟶ GW := GlobalTheory.SplitTorus.torusMap (Sp W) l ≫ j
  have e0 : (1 : splitTorus (Sp W) F ⟶ GW) = GlobalTheory.SplitTorus.torusMap (Sp W) (0 : D₁.toPre.X →+ F) ≫ j := by
    rw [GlobalTheory.SplitTorus.torusMap_zero, MonObj.one_comp]

  have hκ : GlobalTheory.TorusPart.pullTorus hm f = GlobalTheory.TorusPart.pullTorus hm 1 := by
    rw [e0, GlobalTheory.TorusPart.pullTorus_torusMap_comp, GlobalTheory.TorusPart.pullTorus_torusMap_comp, hκj, ← Category.assoc,
      ← Category.assoc, ← GlobalTheory.SplitTorus.torusMap_comp, ← GlobalTheory.SplitTorus.torusMap_comp, hlρ,
      AddMonoidHom.zero_comp]
  letI : Algebra W κ := c.toAlgebra
  letI : Algebra (ResidueField W) κ := (ResidueField.lift c).toAlgebra
  haveI : IsScalarTower W (ResidueField W) κ :=
    IsScalarTower.of_algebraMap_eq' (ResidueField.lift_comp_residue c).symm
  have hbc : (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange W κ).map f = (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange W κ).map 1 :=
    pullback_map_eq_of_pullTorus_eq hm f 1 hκ

  have hk := GlobalTheory.T.overSpecBaseChange_map_eq_of_fieldExtension W (ResidueField W) κ _ _ f 1 hbc
  have hsep : IsSeparated GW.hom :=
    (GlobalTheory.Mum.isSemiAbelian_of_isGrpPullback_square _ _ ψ H GW φW hGW hH).separated
  have hf1 : f = 1 := GlobalTheory.T.splitTorus_hom_ext_of_eq_mod_maximalIdeal_pow W F GW hsep f 1 (GlobalTheory.T.splitTorus_hom_pullback_quotient_pow_eq_one W F GW f inferInstance hk)

  have hf0 : GlobalTheory.SplitTorus.torusMap (Sp W) l ≫ j = GlobalTheory.SplitTorus.torusMap (Sp W) 0 ≫ j := hf1.trans e0
  have e2 := congrArg (GlobalTheory.TorusPart.pullTorus hn) hf0
  rw [GlobalTheory.TorusPart.pullTorus_torusMap_comp, GlobalTheory.TorusPart.pullTorus_torusMap_comp, hΩj] at e2
  haveI := (GlobalTheory.TorusPart.mono_gtTorus_and_factor (U₁.gt 0) hb₁ hn₁).1
  have e3 : GlobalTheory.SplitTorus.torusMap (Sp Ω) l = GlobalTheory.SplitTorus.torusMap (Sp Ω) 0 := (cancel_mono _).1 e2
  exact hl0 (GlobalTheory.SplitTorus.torusMap_injective e3)

end GlobalTheory.Poinc.Sep.Spz
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusSpreadLatticeMapSurjectiveStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_spread_lattice_map_surjective : ∀ (B : Scheme.{0}) (H : Over B) [GrpObj H] [IsCommMonObj H], IsSemiAbelian H → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], GlobalTheory.Mum.Base V₁ → ∀ (G₁ : Over (Sp V₁)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (D₁ : DegData V₁ (maximalIdeal V₁)) (A₁ : PolAV (Sp (FractionRing V₁))) (U₁ : Unif (maximalIdeal V₁) D₁ A₁ G₁) (ξ₁ : Sp V₁ ⟶ B) (β₁ : G₁.left ⟶ H.left), IsGrpPullback G₁ H ξ₁ β₁ → ∀ (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂], GlobalTheory.Mum.Base V₂ → ∀ (G₂ : Over (Sp V₂)) [GrpObj G₂] [IsCommMonObj G₂], IsSemiAbelian G₂ → ∀ (D₂ : DegData V₂ (maximalIdeal V₂)) (A₂ : PolAV (Sp (FractionRing V₂))) (U₂ : Unif (maximalIdeal V₂) D₂ A₂ G₂) (ξ₂ : Sp V₂ ⟶ B) (β₂ : G₂.left ⟶ H.left), IsGrpPullback G₂ H ξ₂ β₂ → ∀ ρ : D₂.toPre.X →+ D₁.toPre.X, Spread₂ H U₁ ξ₁ β₁ U₂ ξ₂ β₂ ρ → Function.Surjective ρ := by
  first | exact @GlobalTheory.Poinc.Sep.Spz.spread₂_surjective | exact GlobalTheory.Poinc.Sep.Spz.spread₂_surjective | (intros; apply GlobalTheory.Poinc.Sep.Spz.spread₂_surjective <;> assumption)
end
end
