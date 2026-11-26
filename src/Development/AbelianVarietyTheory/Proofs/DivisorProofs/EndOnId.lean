module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConstOfPolConst
public import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenEtaleChartCoveringComplexPoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernDensityPullbackWeightInLiftedChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupHomCharacterMapConstant

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndOnId
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.Sep.Spz

section Two

variable {B : Scheme.{0}} (H : Over B) [GrpObj H]
  {V₁ : Type} [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] {D₁ : DegData V₁ (maximalIdeal V₁)}
  {A₁ : PolAV (Sp (FractionRing V₁))} {G₁ : Over (Sp V₁)} [GrpObj G₁] [IsCommMonObj G₁]
  {V₂ : Type} [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂] {D₂ : DegData V₂ (maximalIdeal V₂)}
  {A₂ : PolAV (Sp (FractionRing V₂))} {G₂ : Over (Sp V₂)} [GrpObj G₂] [IsCommMonObj G₂]

def Spread₂ (U₁ : Unif (maximalIdeal V₁) D₁ A₁ G₁) (ξ₁ : Sp V₁ ⟶ B) (β₁ : G₁.left ⟶ H.left)
    (U₂ : Unif (maximalIdeal V₂) D₂ A₂ G₂) (ξ₂ : Sp V₂ ⟶ B) (β₂ : G₂.left ⟶ H.left)
    (ρ : D₂.toPre.X →+ D₁.toPre.X) : Prop :=
  ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (ψ : Sp W ⟶ B)
    (GW : Over (Sp W)) (_ : GrpObj GW) (_ : IsCommMonObj GW) (φW : GW.left ⟶ H.left)
    (j : splitTorus (Sp W) D₁.toPre.X ⟶ GW)
    (Ω : Type) (_ : Field Ω) (α : W →+* Ω) (b₁ : V₁ →+* Ω) (hb₁ : ∀ x ∈ maximalIdeal V₁ ^ (0 + 1), b₁ x = 0)
    (GΩ : Over (Sp Ω)) (_ : GrpObj GΩ) (n : GΩ.left ⟶ GW.left) (hn : IsGrpPullback GΩ GW (spMap α) n)
    (n₁ : GΩ.left ⟶ G₁.left) (hn₁ : IsGrpPullback GΩ G₁ (spMap b₁) n₁)
    (κ : Type) (_ : Field κ) (c : W →+* κ) (b₂ : V₂ →+* κ) (hb₂ : ∀ x ∈ maximalIdeal V₂ ^ (0 + 1), b₂ x = 0)
    (Gκ : Over (Sp κ)) (_ : GrpObj Gκ) (m : Gκ.left ⟶ GW.left) (hm : IsGrpPullback Gκ GW (spMap c) m)
    (m₂ : Gκ.left ⟶ G₂.left) (hm₂ : IsGrpPullback Gκ G₂ (spMap b₂) m₂),
    IsGrpPullback GW H ψ φW ∧ IsMonHom j ∧ Function.Injective α ∧ IsLocalHom c ∧
      spMap α ≫ ψ = spMap b₁ ≫ ξ₁ ∧ spMap c ≫ ψ = spMap b₂ ≫ ξ₂ ∧ n ≫ φW = n₁ ≫ β₁ ∧ m ≫ φW = m₂ ≫ β₂ ∧
      GlobalTheory.TorusPart.pullTorus hn j = GlobalTheory.TorusPart.gtTorus (U₁.gt 0) hb₁ hn₁ ∧
      GlobalTheory.TorusPart.pullTorus hm j = GlobalTheory.SplitTorus.torusMap _ ρ ≫ GlobalTheory.TorusPart.gtTorus (U₂.gt 0) hb₂ hm₂

def TorAt (U : Unif (maximalIdeal V₁) D₁ A₁ G₁) (F : Type) [Field F] [Algebra (FractionRing V₁) F] (k : ℕ) (z : F)
    (c : D₁.toPre.X →+ ℤ) (x : TFK (R := V₁) F ⟶ A₁.A) : Prop :=
  ∃ (τ : Multiplicative D₁.toPre.X →* Fˣ) (q : QkPt D₁.toPre F k),
    (∀ χ, (τ (Multiplicative.ofAdd χ) : F) = z ^ c χ) ∧ q.y = 0 ∧ IsTor τ q.g ∧ QkToAkU U.toUnifPre F k q x

end Two

section Model
open Classical

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {M : RatModel o Ω}
  {U₀ : M.Z.Opens} {EE : M.Lat S.J} (FinalForm : ZHOut ρ M U₀ EE)

def EndOn (f : ρ.P.A ⟶ ρ.P.A) (Fm : FinalForm.G ⟶ FinalForm.G) : Prop :=
  ((Over.pullback FinalForm.u₀).map f).left ≫ FinalForm.φ = FinalForm.φ ≫ Fm.left

def SecOn (a : S.Gam) (Wo : M.Z.Opens) (h : Wo.toScheme ⟶ FinalForm.G.left) : Prop :=
  h ≫ FinalForm.G.hom = Wo.ι ∧
    ∀ (x : Sp Ω ⟶ Wo.toScheme) (x' : Sp Ω ⟶ pullback ρ.P.A.hom FinalForm.u₀), x ≫ Wo.ι = M.pt → x' ≫ FinalForm.φ ≫ FinalForm.G.hom = M.pt →
      x' ≫ pullback.fst _ _ = spMap S.R.val.toRingHom ≫ (ρ.pt a).left → x ≫ h = x' ≫ FinalForm.φ

def Link {T : Scheme.{0}} (x : T ⟶ M.Z) (u : T ⟶ Sp S.R) (A : Over T) [GrpObj A] (φ : A.left ⟶ ρ.P.A.left)
    (gm : A.left ⟶ FinalForm.G.left) : Prop :=
  IsGrpPullback A FinalForm.G x gm ∧
    (∀ (f : ρ.P.A ⟶ ρ.P.A) (Fm : FinalForm.G ⟶ FinalForm.G), EndOn FinalForm f Fm → ∀ (T' : Scheme.{0}) (p p' : T' ⟶ A.left),
      p' ≫ A.hom = p ≫ A.hom → p' ≫ φ = p ≫ φ ≫ f.left → p' ≫ gm = p ≫ gm ≫ Fm.left) ∧
    ∀ (a : S.Gam) (Wo : M.Z.Opens) (h : Wo.toScheme ⟶ FinalForm.G.left), SecOn FinalForm a Wo h →
      ∀ (T' : Scheme.{0}) (p : T' ⟶ A.left) (x' : T' ⟶ Wo.toScheme), x' ≫ Wo.ι = p ≫ A.hom ≫ x →
        p ≫ φ = p ≫ A.hom ≫ u ≫ (ρ.pt a).left → p ≫ gm = x' ≫ h

theorem Link.pull {T T₁ : Scheme.{0}} {x : T ⟶ M.Z} {u : T ⟶ Sp S.R} {A : Over T} [GrpObj A] {φ : A.left ⟶ ρ.P.A.left}
    {gm : A.left ⟶ FinalForm.G.left} (h : Link FinalForm x u A φ gm) {v : T₁ ⟶ T} {A' : Over T₁} [GrpObj A'] {w : A'.left ⟶ A.left}
    (hw : IsGrpPullback A' A v w) : Link FinalForm (v ≫ x) (v ≫ u) A' (w ≫ φ) (w ≫ gm) := by
  have e : w ≫ A.hom = A'.hom ≫ v := hw.1.w
  refine ⟨hw.comp h.1, fun f Fm hf T' p p' h₁ h₂ => ?_, fun a Wo s hs T' p x' h₁ h₂ => ?_⟩
  · have := h.2.1 f Fm hf T' (p ≫ w) (p' ≫ w) (by rw [Category.assoc, Category.assoc, e, reassoc_of% h₁])
      (by simpa only [Category.assoc] using h₂)
    simpa only [Category.assoc] using this
  · have := h.2.2 a Wo s hs T' (p ≫ w) x' (by rw [h₁, Category.assoc, reassoc_of% e])
      (by rw [Category.assoc, Category.assoc, reassoc_of% e]; simpa only [Category.assoc] using h₂)
    simpa only [Category.assoc] using this

end Model

end GlobalTheory.Poinc.Sep.Spz
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NilpotentEvalCommutesSubstAndAlgebraMap
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NilpotentEvalCommutesSubstAndAlgebraMap
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory

theorem evA_subst_and_map : ∀ (k : Type) [CommRing k] (σ : Type) [Finite σ] (A : Type) [CommRing A] [Algebra k A], (∀ (τ : Type) [Finite τ] (φ : MvPowerSeries τ k →ₐ[k] A), (∀ t, IsNilpotent (φ (X t))) → ∀ a : σ → MvPowerSeries τ k, (∀ i, constantCoeff (a i) = 0) → ∀ (y : σ → A) (hy : ∀ i, IsNilpotent (y i)), (∀ i, φ (a i) = y i) → ∀ f : MvPowerSeries σ k, φ (subst a f) = evA k y hy f) ∧ ∀ (B : Type) [CommRing B] [Algebra k B] (g : A →ₐ[k] B) (x : σ → A) (hx : ∀ i, IsNilpotent (x i)) (y : σ → B) (hy : ∀ i, IsNilpotent (y i)), (∀ i, g (x i) = y i) → ∀ f : MvPowerSeries σ k, g (evA k x hx f) = evA k y hy f := by
  intro k _ σ _ A _ _
  refine ⟨?_, ?_⟩
  · intro τ _ φ _ a ha y hy hφa f
    have hs : HasSubst a := hasSubst_of_constantCoeff_zero ha
    have key : evA k y hy = φ.comp (substAlgHom hs) := by
      refine GlobalTheory.T.mvPowerSeries_algHom_ext_of_isNilpotent_X k σ A _ _ (fun i => ?_) (fun i => ?_)
      · rw [GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate k σ A y hy i]; exact hy i
      · rw [GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate k σ A y hy i, AlgHom.comp_apply, coe_substAlgHom, subst_X hs, hφa]
    rw [key, AlgHom.comp_apply, coe_substAlgHom]
  · intro B _ _ g x hx y hy hg f
    have key : evA k y hy = g.comp (evA k x hx) := by
      refine GlobalTheory.T.mvPowerSeries_algHom_ext_of_isNilpotent_X k σ B _ _ (fun i => ?_) (fun i => ?_)
      · rw [GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate k σ B y hy i]; exact hy i
      · rw [GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate k σ B y hy i, AlgHom.comp_apply, GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate k σ A x hx i, hg]
    rw [key, AlgHom.comp_apply]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NilpotentEvalCommutesSubstAndAlgebraMapStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap : ∀ (k : Type) [CommRing k] (σ : Type) [Finite σ] (A : Type) [CommRing A] [Algebra k A], (∀ (τ : Type) [Finite τ] (φ : MvPowerSeries τ k →ₐ[k] A), (∀ t, IsNilpotent (φ (X t))) → ∀ a : σ → MvPowerSeries τ k, (∀ i, constantCoeff (a i) = 0) → ∀ (y : σ → A) (hy : ∀ i, IsNilpotent (y i)), (∀ i, φ (a i) = y i) → ∀ f : MvPowerSeries σ k, φ (subst a f) = evA k y hy f) ∧ ∀ (B : Type) [CommRing B] [Algebra k B] (g : A →ₐ[k] B) (x : σ → A) (hx : ∀ i, IsNilpotent (x i)) (y : σ → B) (hy : ∀ i, IsNilpotent (y i)), (∀ i, g (x i) = y i) → ∀ f : MvPowerSeries σ k, g (evA k x hx f) = evA k y hy f := by
  first | exact @GlobalTheory.evA_subst_and_map | exact GlobalTheory.evA_subst_and_map | (intros; apply GlobalTheory.evA_subst_and_map <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelOperatorAtDbarOperatorAtLinearLocal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelOperatorAtDbarOperatorAtLinearLocal
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

noncomputable section

namespace GlobalTheory.CxForm

variable {n : ℕ}

theorem coefwise_add_of {T : (V n → ℂ) → ℂ} {F G : V n → Alt n}
    (h : ∀ S, T (fun x => (bas n).repr (F x) S + (bas n).repr (G x) S) =
      T (fun x => (bas n).repr (F x) S) + T (fun x => (bas n).repr (G x) S)) :
    coefwise T (fun x => F x + G x) = coefwise T F + coefwise T G := by
  simp only [coefwise, map_add (f := _), Finsupp.add_apply, h, add_smul, Finset.sum_add_distrib]

theorem coefwise_const_smul_of {T : (V n → ℂ) → ℂ} {F : V n → Alt n} (c : ℂ)
    (h : ∀ S, T (fun x => c • (bas n).repr (F x) S) = c • T (fun x => (bas n).repr (F x) S)) :
    coefwise T (fun x => c • F x) = c • coefwise T F := by
  simp only [coefwise, map_smul, Finsupp.smul_apply, h, Finset.smul_sum, smul_assoc]

theorem coefwise_sum_of {T : (V n → ℂ) → ℂ} {ι : Type} (t : Finset ι) {F : ι → V n → Alt n}
    (h : ∀ S, T (fun x => ∑ i ∈ t, (bas n).repr (F i x) S) = ∑ i ∈ t, T (fun x => (bas n).repr (F i x) S)) :
    coefwise T (fun x => ∑ i ∈ t, F i x) = ∑ i ∈ t, coefwise T (F i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [coefwise, map_sum, Finsupp.finsetSum_apply, h, Finset.sum_smul]
  exact Finset.sum_comm

theorem delAt_dbarAt_linear_local : ∀ (n : ℕ) (v : V n),
    (∀ F G : V n → Alt n, (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x) S) v) →
      (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (G x) S) v) →
      delAt (fun x => F x + G x) v = delAt F v + delAt G v ∧ dbarAt (fun x => F x + G x) v = dbarAt F v + dbarAt G v) ∧
    (∀ (F : V n → Alt n) (c : ℂ), (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x) S) v) →
      delAt (fun x => c • F x) v = c • delAt F v ∧ dbarAt (fun x => c • F x) v = c • dbarAt F v) ∧
    (∀ (ι : Type) (t : Finset ι) (F : ι → V n → Alt n),
      (∀ i ∈ t, ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F i x) S) v) →
      delAt (fun x => ∑ i ∈ t, F i x) v = ∑ i ∈ t, delAt (F i) v ∧ dbarAt (fun x => ∑ i ∈ t, F i x) v = ∑ i ∈ t, dbarAt (F i) v) ∧
    (∀ F G : V n → Alt n, F =ᶠ[𝓝 v] G → delAt F v = delAt G v ∧ dbarAt F v = dbarAt G v) ∧
    (∀ c : Alt n, delAt (fun _ => c) v = 0 ∧ dbarAt (fun _ => c) v = 0) := by
  intro n v
  refine ⟨fun F G hF hG => ⟨?_, ?_⟩, fun F c hF => ⟨?_, ?_⟩, fun ι t F hF => ⟨?_, ?_⟩, fun F G h => ⟨?_, ?_⟩,
    fun c => ⟨?_, ?_⟩⟩
  · rw [delAt, delAt, delAt, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [coefwise_add_of fun S => by rw [GlobalTheory.del_add (hF S) (hG S)]; rfl, mul_add]
  · rw [dbarAt, dbarAt, dbarAt, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [coefwise_add_of fun S => by rw [GlobalTheory.dbar_add (hF S) (hG S)]; rfl, mul_add]
  · rw [delAt, delAt, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [coefwise_const_smul_of c fun S => by rw [GlobalTheory.del_const_smul c (hF S)]; rfl, mul_smul_comm]
  · rw [dbarAt, dbarAt, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [coefwise_const_smul_of c fun S => by rw [GlobalTheory.dbar_const_smul c (hF S)]; rfl, mul_smul_comm]
  · simp only [delAt]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [coefwise_sum_of t fun S => by
      rw [GlobalTheory.del_sum fun i hi => hF i hi S, ContinuousLinearMap.sum_apply], Finset.mul_sum]
  · simp only [dbarAt]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [coefwise_sum_of t fun S => by
      rw [GlobalTheory.dbar_sum fun i hi => hF i hi S, ContinuousLinearMap.sum_apply], Finset.mul_sum]
  · have e (S) : del (fun x => (bas n).repr (F x) S) v = del (fun x => (bas n).repr (G x) S) v :=
      GlobalTheory.del_congr (h.fun_comp fun y => (bas n).repr y S)
    simp only [delAt, coefwise, e]
  · have e (S) : dbar (fun x => (bas n).repr (F x) S) v = dbar (fun x => (bas n).repr (G x) S) v :=
      GlobalTheory.dbar_congr (h.fun_comp fun y => (bas n).repr y S)
    simp only [dbarAt, coefwise, e]
  · simp [delAt, coefwise]
  · simp [dbarAt, coefwise]

end GlobalTheory.CxForm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelOperatorAtDbarOperatorAtLinearLocalStatement
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.delOperatorAt_dbarOperatorAt_linear_local : ∀ (n : ℕ) (v : V n),
    (∀ F G : V n → Alt n, (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x) S) v) →
      (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (G x) S) v) →
      delAt (fun x => F x + G x) v = delAt F v + delAt G v ∧ dbarAt (fun x => F x + G x) v = dbarAt F v + dbarAt G v) ∧
    (∀ (F : V n → Alt n) (c : ℂ), (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x) S) v) →
      delAt (fun x => c • F x) v = c • delAt F v ∧ dbarAt (fun x => c • F x) v = c • dbarAt F v) ∧
    (∀ (ι : Type) (t : Finset ι) (F : ι → V n → Alt n),
      (∀ i ∈ t, ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F i x) S) v) →
      delAt (fun x => ∑ i ∈ t, F i x) v = ∑ i ∈ t, delAt (F i) v ∧ dbarAt (fun x => ∑ i ∈ t, F i x) v = ∑ i ∈ t, dbarAt (F i) v) ∧
    (∀ F G : V n → Alt n, F =ᶠ[𝓝 v] G → delAt F v = delAt G v ∧ dbarAt F v = dbarAt G v) ∧
    (∀ c : Alt n, delAt (fun _ => c) v = 0 ∧ dbarAt (fun _ => c) v = 0) := by
  first | exact @GlobalTheory.CxForm.delAt_dbarAt_linear_local | exact GlobalTheory.CxForm.delAt_dbarAt_linear_local | (intros; apply GlobalTheory.CxForm.delAt_dbarAt_linear_local <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CounitCotangentClassPowerSeriesEvalAtNilpotent
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CounitCotangentClassPowerSeriesEvalAtNilpotent
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Katz

theorem coeff_single_one_mul {σ R : Type} [CommRing R] [DecidableEq σ] (i : σ) (f g : MvPowerSeries σ R) :
    coeff (Finsupp.single i 1) (f * g) =
      constantCoeff f * coeff (Finsupp.single i 1) g + coeff (Finsupp.single i 1) f * constantCoeff g := by
  rw [coeff_mul, Finsupp.antidiagonal_single, Finset.sum_map]
  rw [show (Finset.HasAntidiagonal.antidiagonal (1 : ℕ) : Finset (ℕ × ℕ)) = {(0, 1), (1, 0)} by decide]
  rw [Finset.sum_pair (by simp)]
  simp only [Function.Embedding.coe_prodMap, Prod.map_apply, Function.Embedding.coeFn_mk,
    Finsupp.single_zero, coeff_zero_eq_constantCoeff_apply]

theorem counit_dUnit_evA : ∀ (k : Type) [CommRing k] (d : ℕ) (A : Type) [CommRing A] [Bialgebra k A] (x : Fin d → A) (hx : ∀ i, IsNilpotent (x i)), (∀ i, Coalgebra.counit (R := k) (x i) = 0) → ∀ f : MvPowerSeries (Fin d) k, Coalgebra.counit (R := k) (evA k x hx f) = constantCoeff f ∧ dUnit (R := k) (evA k x hx f) = ∑ i, lin f i • dUnit (R := k) (x i) := by
  intro k _ d A _ _ x hx h0 f
  have hev : ∀ i, evA k x hx (X i) = x i := GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate k (Fin d) A x hx
  let c0 : MvPowerSeries (Fin d) k →ₐ[k] k :=
    { (constantCoeff : MvPowerSeries (Fin d) k →+* k) with
      commutes' := fun r => by simp [MvPowerSeries.algebraMap_apply] }
  have hc0 : ∀ g, c0 g = constantCoeff g := fun _ => rfl
  have h1 : (Bialgebra.counitAlgHom k A).comp (evA k x hx) = c0 :=
    GlobalTheory.T.mvPowerSeries_algHom_ext_of_isNilpotent_X k (Fin d) k _ _ (fun i => by simp [hev, h0]) (fun i => by simp [hev, h0, hc0])
  refine ⟨(AlgHom.congr_fun h1 f).trans (hc0 f), ?_⟩
  letI : Module kᵐᵒᵖ (Cot k A) := Module.compHom _ ((RingHom.id k).fromOpposite mul_comm)
  haveI : IsCentralScalar k (Cot k A) := ⟨fun _ _ => rfl⟩
  let D : MvPowerSeries (Fin d) k →ₗ[k] Cot k A :=
    ∑ i, LinearMap.smulRight (coeff (Finsupp.single i 1)) (dUnit (R := k) (x i))
  have hD : ∀ g, D g = ∑ i, lin g i • dUnit (R := k) (x i) := fun g => by simp [D, lin]
  have hlin1 : ∀ i, lin (1 : MvPowerSeries (Fin d) k) i = 0 := fun i => by
    simp [lin, coeff_one]
  have hlinmul : ∀ (a b : MvPowerSeries (Fin d) k) i,
      lin (a * b) i = constantCoeff a * lin b i + lin a i * constantCoeff b := fun a b i =>
    coeff_single_one_mul i a b
  let L : MvPowerSeries (Fin d) k →ₗ[k] TrivSqZeroExt k (Cot k A) :=
    (TrivSqZeroExt.inlAlgHom k k (Cot k A)).toLinearMap ∘ₗ c0.toLinearMap +
        TrivSqZeroExt.inrHom k (Cot k A) ∘ₗ D
  have hLf : ∀ g, (L g).fst = constantCoeff g := fun g => by simp [L, hc0]
  have hLs : ∀ g, (L g).snd = ∑ i, lin g i • dUnit (R := k) (x i) := fun g => by simp [L, hD, TrivSqZeroExt.snd_sum]
  let ψ : MvPowerSeries (Fin d) k →ₐ[k] TrivSqZeroExt k (Cot k A) :=
    AlgHom.ofLinearMap L
      (by ext <;> simp [hLf, hLs, hlin1])
      (fun a b => by
        ext
        · simp [hLf]
        · rw [TrivSqZeroExt.snd_mul, hLs, hLs, hLs, hLf, hLf]
          simp only [hlinmul, add_smul, mul_smul, Finset.smul_sum, Finset.sum_add_distrib]
          congr 1
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [op_smul_eq_smul, smul_comm])
  have hψf : ∀ g, (ψ g).snd = ∑ i, lin g i • dUnit (R := k) (x i) := hLs
  let φ : MvPowerSeries (Fin d) k →ₐ[k] TrivSqZeroExt k (Cot k A) :=
    (AugCot.toSqZero (Bialgebra.counitAlgHom k A) (LinearMap.id (M := Cot k A))).comp (evA k x hx)
  have hφf : ∀ g, (φ g).fst = Coalgebra.counit (R := k) (evA k x hx g) := fun g => by simp [φ]
  have hφs : ∀ g, (φ g).snd = dUnit (R := k) (evA k x hx g) := fun g => by simp [φ]
  have hlinX : ∀ i j, lin (X i : MvPowerSeries (Fin d) k) j = if j = i then 1 else 0 := fun i j => by
    simp [lin, coeff_X, Finsupp.single_left_inj one_ne_zero]
  have hφψ : φ = ψ := by
    refine GlobalTheory.T.mvPowerSeries_algHom_ext_of_isNilpotent_X k (Fin d) _ _ _ (fun i => ⟨2, ?_⟩) (fun i => ?_)
    · ext
      · simp [pow_two, hφf, hev, h0]
      · simp [pow_two, TrivSqZeroExt.snd_mul, hφf, hev, h0]
    · ext
      · rw [hφf, hev, h0]; exact (constantCoeff_X i).symm.trans (hLf (X i)).symm
      · rw [hφs, hψf, hev]
        simp [hlinX]
  rw [← hφs, ← hψf, hφψ]

end GlobalTheory.Katz
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CounitCotangentClassPowerSeriesEvalAtNilpotentStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.counit_cotangentClass_powerSeriesEvalAtNilpotent : ∀ (k : Type) [CommRing k] (d : ℕ) (A : Type) [CommRing A] [Bialgebra k A] (x : Fin d → A) (hx : ∀ i, IsNilpotent (x i)), (∀ i, Coalgebra.counit (R := k) (x i) = 0) → ∀ f : MvPowerSeries (Fin d) k, Coalgebra.counit (R := k) (evA k x hx f) = constantCoeff f ∧ dUnit (R := k) (evA k x hx f) = ∑ i, lin f i • dUnit (R := k) (x i) := by
  first | exact @GlobalTheory.Katz.counit_dUnit_evA | exact GlobalTheory.Katz.counit_dUnit_evA | (intros; apply GlobalTheory.Katz.counit_dUnit_evA <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumFConstMul
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

namespace GlobalTheory.Poinc.Sep

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}

def TorChar {X₁ : Setup F W i} {z₁ : X₁.M.Z} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}
    {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
    {X : Type} [AddCommGroup X] {m : ℕ} {t : Fin m → V} {δ : Fin m → LinearMap.BilinForm ℤ X}
    (𝔪 : UMem X₁ z₁ act V ev X t δ) (τ : X₁.S.Gam) (χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ) : Prop :=
  χ ^ (X₁.S.r * X₁.S.N) = 1 ∧ ∀ g₀ : GtPtF 𝔪.D.toPre (FractionRing V), IsTor χ g₀ →
    ∃ (p : QkPt 𝔪.D.toPre (FractionRing V) (X₁.S.r * X₁.S.N)) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A),
      p.y = 0 ∧ p.g = g₀ ∧ QkToAkU 𝔪.U.toUnifPre (FractionRing V) (X₁.S.r * X₁.S.N) p x ∧
      x.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left

def TransExp {X₁ : Setup F W i} {z₁ : X₁.M.Z} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}
    {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
    {X : Type} [AddCommGroup X] {m : ℕ} {t : Fin m → V} {δ : Fin m → LinearMap.BilinForm ℤ X}
    (𝔪 : UMem X₁ z₁ act V ev X t δ) (x₀ a τ : X₁.S.Gam) (e : ℕ) : Prop :=
  ∀ χ, TorChar 𝔪 τ χ → ∀ (C : Type) (lab : C → X₁.S.Gam) (T : (Fin 8 → X) → C → V), 𝔪.Terms x₀ lab T →
    ∀ c, lab c = a → ∀ (C' : Type) (lab' : C' → X₁.S.Gam) (T' : (Fin 8 → X) → C' → V), 𝔪.Terms x₀ lab' T' →
    ∀ c', lab' c' = a + τ → ∀ mu : Fin 8 → X,
      ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) * algebraMap V (FractionRing V) (T mu c) =
        𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ e)) * algebraMap V (FractionRing V) (T' mu c')

theorem sumF_const_mul {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {K : Type} [Field K]
    [Algebra (FractionRing R) K] {Ix : Type} {x : Ix → K} {s : K} (c : K) (h : SumF I K x s) :
    SumF I K (fun j => c * x j) (c * s) := by
  letI : Module R K := Module.compHom K (algebraMap R (FractionRing R))
  obtain ⟨N, hN, hs, hx, hlim⟩ := h
  let f : K →ₗ[R] K :=
    { toFun := fun y => c * y
      map_add' := fun y z => mul_add c y z
      map_smul' := fun r y => by
        change c * ((algebraMap R (FractionRing R) r : FractionRing R) • y) = (algebraMap R (FractionRing R) r : FractionRing R) • (c * y)
        rw [Algebra.smul_def, Algebra.smul_def]; ring }
  refine ⟨N.map f, hN.map f, ⟨s, hs, rfl⟩, fun j => ⟨x j, hx j, rfl⟩, fun k => ?_⟩
  obtain ⟨S, hS⟩ := hlim k
  refine ⟨S, fun T hT => ?_⟩
  have := Submodule.mem_map_of_mem (f := f) (hS T hT)
  rw [Submodule.map_smul''] at this
  convert this using 1
  change c * s - ∑ j ∈ T, c * x j = c * (s - ∑ j ∈ T, x j)
  rw [mul_sub, Finset.mul_sum]

end GlobalTheory.Poinc.Sep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelOperatorAtDbarOperatorAtLeibnizOfCommute
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelOperatorAtDbarOperatorAtLeibnizOfCommute
set_option autoImplicit false

noncomputable section

open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

namespace GlobalTheory.CxForm.FormMul

theorem leibniz_of_comm : ∀ (n : ℕ) (F G : V n → Alt n) (v : V n) (F' : Alt n),
    (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x) S) v) →
    (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (G x) S) v) →
    ((∀ a, dz a * F v = F' * dz a) → delAt (fun x => F x * G x) v = delAt F v * G v + F' * delAt G v) ∧
    ((∀ a, dzb a * F v = F' * dzb a) → dbarAt (fun x => F x * G x) v = dbarAt F v * G v + F' * dbarAt G v) := by
  intro n F G v F' hF hG
  refine ⟨fun h => ?_, fun h => ?_⟩
  · unfold delAt
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [coefwise_mul (T := fun f => del f v (coordVec a))
      (fun f hf => by rw [del_sum (fun p _ => hf p), ContinuousLinearMap.sum_apply])
      (fun f g hf hg => del_mul hf hg _) (fun c => by rw [del_const]; rfl) hF hG]
    simp only [mul_add, ← mul_assoc, h]
  · unfold dbarAt
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [coefwise_mul (T := fun f => dbar f v (coordVec a))
      (fun f hf => by rw [dbar_sum (fun p _ => hf p), ContinuousLinearMap.sum_apply])
      (fun f g hf hg => dbar_mul hf hg _) (fun c => by rw [dbar_const]; rfl) hF hG]
    simp only [mul_add, ← mul_assoc, h]

end GlobalTheory.CxForm.FormMul
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelOperatorAtDbarOperatorAtLeibnizOfCommuteStatement
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.delOperatorAt_dbarOperatorAt_leibniz_of_commute : ∀ (n : ℕ) (F G : V n → Alt n) (v : V n) (F' : Alt n),
    (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x) S) v) →
    (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (G x) S) v) →
    ((∀ a, dz a * F v = F' * dz a) → delAt (fun x => F x * G x) v = delAt F v * G v + F' * delAt G v) ∧
    ((∀ a, dzb a * F v = F' * dzb a) → dbarAt (fun x => F x * G x) v = dbarAt F v * G v + F' * dbarAt G v) := by
  first | exact @GlobalTheory.CxForm.FormMul.leibniz_of_comm | exact GlobalTheory.CxForm.FormMul.leibniz_of_comm | (intros; apply GlobalTheory.CxForm.FormMul.leibniz_of_comm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericDegreePullbackFormula
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open MeasureTheory GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.Points
open scoped ENNReal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GdegPullProof

theorem chernInt_one {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}
    {B : LB X} (φ : Weight p σ B) (D : ℕ) :
    φ.chernInt D Set.univ (fun _ => 1) =
      (φ.chernPart D 1 Set.univ).toReal - (φ.chernPart D (-1) Set.univ).toReal := by
  simp [Weight.chernInt, Measure.real]

theorem mass {k : Type} [CommRing k] {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {D : ℕ} (hX : IsArithVar p D) (hY : IsArithVar q D)
    (π : Y ⟶ X) (hπ : π ≫ p = q) (hη : π (genericPoint Y) = genericPoint X)
    (hδ : π.residueDegree (genericPoint Y) ≠ 0) (L : HermLB p) (σ : k →+* ℂ) (ε : ℤˣ) :
    ((L.φ σ).pull π hπ).chernPart D ε Set.univ =
      (π.residueDegree (genericPoint Y) : ℝ≥0∞) * (L.φ σ).chernPart D ε Set.univ := by
  obtain ⟨U, hUη, hU⟩ := GlobalTheory.T.exists_open_etaleChart_covering_complexPoints hX hY π hπ hη hδ
  obtain ⟨hcard, hchart, hlift⟩ := hU σ
  have hpre : PtsOver.map π hπ (spMap σ) ⁻¹' ptsIn p σ U = ptsIn q σ (π ⁻¹ᵁ U) := by
    ext z
    simp only [Set.mem_preimage, mem_ptsIn]
    rfl
  have hcY : (ptsIn q σ (π ⁻¹ᵁ U))ᶜ =
      {z : CxPts q σ | z.1 (IsLocalRing.closedPoint ℂ) ∈ ((π ⁻¹ᵁ U : Y.Opens) : Set Y)ᶜ} := by
    ext z
    simp [mem_ptsIn]
  have hcX : (ptsIn p σ U)ᶜ =
      {y : CxPts p σ | y.1 (IsLocalRing.closedPoint ℂ) ∈ ((U : X.Opens) : Set X)ᶜ} := by
    ext y
    simp [mem_ptsIn]
  have h0Y := GlobalTheory.T.chernPart_over_properClosed_eq_zero hY ((π ⁻¹ᵁ U : Y.Opens) : Set Y)ᶜ (π ⁻¹ᵁ U).isOpen.isClosed_compl
    (by simp [hη, hUη]) σ ((L.φ σ).pull π hπ) ε
  have h0X := GlobalTheory.T.chernPart_over_properClosed_eq_zero hX ((U : X.Opens) : Set X)ᶜ U.isOpen.isClosed_compl (by simp [hUη]) σ
    (L.φ σ) ε
  rw [← hcY] at h0Y
  rw [← hcX] at h0X
  have h3 := GlobalTheory.T.chernPart_preimage_of_finite_liftedChartCovering hX hY π hπ (L.φ σ) (L.cInf σ) ε (ptsIn p σ U) (isOpen_ptsIn U) _ hcard
    hchart hlift (fun c c' hc w hw => GlobalTheory.T.chernDensity_pullbackWeight_in_liftedChart π hπ (L.φ σ) (L.cInf σ) c c' hc w hw) _
    (isOpen_ptsIn U).measurableSet subset_rfl
  rw [hpre] at h3
  rw [← measure_add_measure_compl (isOpen_ptsIn (π ⁻¹ᵁ U)).measurableSet, h0Y, add_zero, h3,
    ← measure_add_measure_compl (isOpen_ptsIn (p := p) (σ := σ) U).measurableSet, h0X, add_zero]

end GlobalTheory.GdegPullProof

namespace GlobalTheory.CovTest

theorem gdegPull : GdegPull := by
  intro k _ X Y _ _ p q D hX hY π hπ hη hδ L
  have key : ∀ σ, ((L.pull π hπ).φ σ).chernInt D Set.univ (fun _ => 1) =
      (π.residueDegree (genericPoint Y) : ℝ) * (L.φ σ).chernInt D Set.univ (fun _ => 1) := by
    intro σ
    change ((L.φ σ).pull π hπ).chernInt D Set.univ (fun _ => 1) = _
    rw [GdegPullProof.chernInt_one, GdegPullProof.chernInt_one,
      GdegPullProof.mass hX hY π hπ hη hδ L σ 1, GdegPullProof.mass hX hY π hπ hη hδ L σ (-1),
      ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast, mul_sub]
  simp only [gdeg, chInt]
  simp_rw [key]
  rw [mul_finsum]

end GlobalTheory.CovTest

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedMemberDividingThetaConstantNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedMemberDividingThetaConstantNeZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

namespace GlobalTheory.Poinc.Sep

theorem UMem.yK_th_ne_zero : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ ≠ 0 := by
  intro g n F W Z i X₁ z₁ act V _ _ _ ev X _ m t δ 𝔪 x₀ hd h0
  obtain ⟨c, -, h⟩ := GlobalTheory.ZH.GoodOut.exists_th_notMem GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2 X₁.ρ
    ⟨RingHom.ker 𝔪.yK, RingHom.ker_isPrime 𝔪.yK⟩ 0
  refine h (RingHom.mem_ker.2 ?_)
  have sp : ∀ w, X₁.M.Z.fromSpecStalk z₁ w ⤳ z₁ := fun w => by
    have : X₁.M.Z.fromSpecStalk z₁ w ∈ Set.range (X₁.M.Z.fromSpecStalk z₁) := ⟨w, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  have hd' := hd.of_specializes
    (ξ := (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint (FractionRing V))) (sp _)
  have hs : ∀ w, (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) w ⤳
      (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint (FractionRing V)) :=
    RatModel.specializes_of_range_eq (RatModel.range_eq_singleton _ _)
  have e := RatModel.val_mul hs (hd'.2 (0 + c)) (𝔪.reg _ (X₁.S.th_mem x₀))
  rw [div_mul_cancel₀ _ hd.1] at e
  rw [𝔪.yK_eq] at h0 ⊢
  exact e.trans ((congrArg (_ * ·) h0).trans (mul_zero _))

end GlobalTheory.Poinc.Sep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedMemberDividingThetaConstantNeZeroStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisedMember_dividingThetaConstant_ne_zero : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ ≠ 0 := by
  first | exact @GlobalTheory.Poinc.Sep.UMem.yK_th_ne_zero | exact GlobalTheory.Poinc.Sep.UMem.yK_th_ne_zero | (intros; apply GlobalTheory.Poinc.Sep.UMem.yK_th_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackComplexFormsLinearMapComp
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackComplexFormsLinearMapComp
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

set_option autoImplicit false

namespace GlobalTheory.CxForm

theorem pull_comp_entry {k m n : ℕ} (L : V n →L[ℂ] V m) (L' : V m →L[ℂ] V k) (b : Fin n) (a : Fin k) :
    (L' (L (coordVec b))).ofLp a = ∑ c, (L (coordVec b)).ofLp c * (L' (coordVec c)).ofLp a := by
  have hx : L (coordVec b) = ∑ c, (L (coordVec b)).ofLp c • (coordVec c : V m) := by
    simpa [coordVec] using (EuclideanSpace.basisFun (Fin m) ℂ).sum_repr (L (coordVec b)) |>.symm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hx, map_sum]
  simp [map_smul, PiLp.smul_apply]
  simp [Pi.single_apply]

theorem pull_comp (k m n : ℕ) (L : V n →L[ℂ] V m) (L' : V m →L[ℂ] V k) (γ : Alt k) :
    pull (L'.comp L) γ = pull L (pull L' γ) := by
  have hM : (Matrix.fromBlocks (Matrix.of fun b a => ((L'.comp L) (coordVec b)).ofLp a) 0 0
        (Matrix.of fun b a => conj (((L'.comp L) (coordVec b)).ofLp a)) : Matrix (Fin n ⊕ Fin n) (Fin k ⊕ Fin k) ℂ) =
      Matrix.fromBlocks (Matrix.of fun b a => (L (coordVec b)).ofLp a) 0 0
        (Matrix.of fun b a => conj ((L (coordVec b)).ofLp a)) *
      Matrix.fromBlocks (Matrix.of fun b a => (L' (coordVec b)).ofLp a) 0 0
        (Matrix.of fun b a => conj ((L' (coordVec b)).ofLp a)) := by
    rw [Matrix.fromBlocks_multiply]
    congr 1
    · ext b a; simp only [Matrix.of_apply, ContinuousLinearMap.comp_apply, pull_comp_entry]
      simp [Matrix.mul_apply]
    · simp
    · simp
    · ext b a
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Matrix.mul_apply, Matrix.of_apply, ContinuousLinearMap.comp_apply, pull_comp_entry, map_sum, map_mul]
      simp [Matrix.mul_apply]
  simp only [pull]
  rw [hM, Matrix.toLin'_mul, ← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map]

end GlobalTheory.CxForm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackComplexFormsLinearMapCompStatement
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullbackComplexFormsLinearMap_comp : ∀ (k m n : ℕ) (L : V n →L[ℂ] V m) (L' : V m →L[ℂ] V k) (γ : Alt k), pull (L'.comp L) γ = pull L (pull L' γ) := by
  first | exact @GlobalTheory.CxForm.pull_comp | exact GlobalTheory.CxForm.pull_comp | (intros; apply GlobalTheory.CxForm.pull_comp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleDiagonalPullbackBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleDiagonalPullbackBaseChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot

noncomputable section
namespace GlobalTheory.DiagAmpleBC

theorem diag_comp {S T : Scheme.{0}} (A : Over S) (B : Over T) (β : B.left ⟶ A.left)
    (β₂ : (G2 B).left ⟶ (G2 A).left) (hs : IsSquare β β₂) :
    (lift (𝟙 B) (𝟙 B)).left ≫ β₂ = β ≫ (lift (𝟙 A) (𝟙 A)).left := by
  have h1 : (lift (𝟙 B) (𝟙 B)).left ≫ (fst B B).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_fst]; rfl
  have h2 : (lift (𝟙 A) (𝟙 A)).left ≫ (fst A A).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_fst]; rfl
  have h3 : (lift (𝟙 B) (𝟙 B)).left ≫ (snd B B).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_snd]; rfl
  have h4 : (lift (𝟙 A) (𝟙 A)).left ≫ (snd A A).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_snd]; rfl
  apply pullback.hom_ext
  · show _ ≫ (fst A A).left = _ ≫ (fst A A).left
    rw [Category.assoc, hs.1, ← Category.assoc, h1, Category.assoc, h2, Category.id_comp, Category.comp_id]
  · show _ ≫ (snd A A).left = _ ≫ (snd A A).left
    rw [Category.assoc, hs.2, ← Category.assoc, h3, Category.assoc, h4, Category.id_comp, Category.comp_id]

theorem relAmple_diag_pull : ∀ (S T : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (P : LB (G2 A).left), P.IsLB → RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (t : T ⟶ S) (B : Over T) (β : B.left ⟶ A.left) (β₂ : (G2 B).left ⟶ (G2 A).left), IsPullback β B.hom A.hom t → IsSquare β β₂ → RelAmple B ((P.pull β₂).pull (lift (𝟙 B) (𝟙 B)).left) := by
  intro S T A _ hA P hP hD t B β β₂ hpb hs
  haveI := hA.proper
  have e₁ : LBIso ((P.pull β₂).pull (lift (𝟙 B) (𝟙 B)).left) (P.pull ((lift (𝟙 B) (𝟙 B)).left ≫ β₂)) :=
    GlobalTheory.ZM.SiegPull.lbIso_pull_comp (GlobalTheory.lbIso_refl (pull_isLB hP β₂)) _
  have e₂ : LBIso ((P.pull (lift (𝟙 A) (𝟙 A)).left).pull β) (P.pull (β ≫ (lift (𝟙 A) (𝟙 A)).left)) :=
    GlobalTheory.ZM.SiegPull.lbIso_pull_comp (GlobalTheory.lbIso_refl (pull_isLB hP _)) _
  rw [diag_comp A B β β₂ hs] at e₁
  have e := LBIso.trans (pull_isLB (pull_isLB hP _) _) (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _) e₁ e₂.symm
  exact GlobalTheory.ModelAbLocus.relAmple_of_lbIso_pull hpb (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _) e hD

end GlobalTheory.DiagAmpleBC
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleDiagonalPullbackBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relAmple_diagonal_pullback_baseChange : ∀ (S T : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (P : LB (G2 A).left), P.IsLB → RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (t : T ⟶ S) (B : Over T) (β : B.left ⟶ A.left) (β₂ : (G2 B).left ⟶ (G2 A).left), IsPullback β B.hom A.hom t → IsSquare β β₂ → RelAmple B ((P.pull β₂).pull (lift (𝟙 B) (𝟙 B)).left) := by
  first | exact @GlobalTheory.DiagAmpleBC.relAmple_diag_pull | exact GlobalTheory.DiagAmpleBC.relAmple_diag_pull | (intros; apply GlobalTheory.DiagAmpleBC.relAmple_diag_pull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchIntegrableRegularVariety
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MeasureTheory Set Filter Topology Metric
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ChartGlue
open scoped ENNReal

namespace GlobalTheory.LogNormInt

theorem integrableOn_of_chart {M : Type} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M] {n : ℕ}
    (e : OpenPartialHomeomorph M (V n)) {μ : Measure M} {ρ : V n → ℝ≥0∞}
    (hμ : ∀ A, MeasurableSet A → A ⊆ e.source → μ A = ∫⁻ v in e '' A, ρ v)
    {A : Set M} (hA : MeasurableSet A) (hAs : A ⊆ e.source) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hρ : ∀ v ∈ e '' A, ρ v ≤ C) {f : M → ℝ} (hf : ContinuousOn f A)
    (hi : IntegrableOn (f ∘ e.symm) (e '' A)) : IntegrableOn f A μ := by
  have hm := measurableSet_image e hA hAs
  have hsub : e '' A ⊆ e.target := fun _ ⟨y, hy, h⟩ => h ▸ e.map_source (hAs hy)
  have hs : AEMeasurable e.symm (volume.restrict (e '' A)) :=
    (e.continuousOn_symm.mono hsub).aemeasurable hm
  have hle : μ.restrict A ≤ C • Measure.map e.symm (volume.restrict (e '' A)) := by
    refine Measure.le_iff.2 fun B hB => ?_
    have hBA := hB.inter hA
    have hm' := measurableSet_image e hBA (inter_subset_right.trans hAs)
    rw [Measure.restrict_apply hB, hμ _ hBA (inter_subset_right.trans hAs), Measure.smul_apply,
      Measure.map_apply_of_aemeasurable hs hB, Measure.restrict_apply' hm, smul_eq_mul]
    refine (setLIntegral_mono' hm' fun v hv => hρ v (image_mono inter_subset_right hv)).trans ?_
    rw [setLIntegral_const]
    gcongr
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨by rw [mem_preimage, e.left_inv (hAs hy.2)]; exact hy.1, mem_image_of_mem _ hy.2⟩
  refine ⟨hf.aestronglyMeasurable hA, ?_⟩
  refine (lintegral_mono' hle le_rfl).trans_lt ?_
  rw [lintegral_smul_measure, smul_eq_mul]
  exact ENNReal.mul_lt_top hC.lt_top ((lintegral_map_le _ hs).trans_lt hi.2)

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

theorem continuousAt_ratVal {f : X.functionField} {y : CxPts p σ} (hf : RegAt (under y) f) :
    ContinuousAt (fun z : CxPts p σ => ratVal f z) y := by
  obtain ⟨U, hU, a, rfl⟩ := hf.exists_fnOf
  have hn := (isOpen_ptsIn (p := p) (σ := σ) U).mem_nhds (mem_ptsIn.2 hU)
  refine ((continuousOn_ev a).continuousAt hn).congr ?_
  filter_upwards [hn] with z hz
  exact (ratVal_fnOf hz _ a).symm

theorem frequently_ne_zero (hσ : Function.Injective σ) (c : AlgChart p σ D) {U : X.Opens}
    {a : Γ(X, U)} (ha : a ≠ 0) {y : CxPts p σ} (hy : y ∈ c.e.source) (hU : y ∈ ptsIn p σ U) :
    ∃ᶠ v in 𝓝 (c.e y), (ev p σ U a ∘ c.e.symm) v ≠ 0 := by
  have : IsDomain k := hσ.isDomain σ
  have hg := gen_mem (mem_ptsIn.1 hU)
  have hb : genericPoint X ∈ X.basicOpen a := (unitAt_fnOf_iff hg hg a).1
    (unitAt_genericPoint ((map_ne_zero_iff _ (fnOf_injective U hg)).2 ha))
  have h := Measure.dense_of_ae (SemiPosBir.ae_mem hσ c (U := X.basicOpen a) ⟨_, hb⟩)
  have h₁ := mem_closure_iff_frequently.1 (h (c.e y))
  refine (h₁.and_eventually ((isOpen_over c.e (isOpen_ptsIn U)).mem_nhds (mem_over c.e hy hU))).mono ?_
  rintro v ⟨h₂, h₃⟩
  exact (mem_ptsIn_basicOpen h₃.2 a).1 (h₂ h₃.1)

theorem exists_integrableOn [SecondCountableTopology (CxPts p σ)] (hσ : Function.Injective σ)
    {A B : LB X} {ψ : Weight p σ A} (hψ : ψ.IsCInf) {φ : Weight p σ B} (hφ : φ.IsCInf)
    {r : B.ι → X.functionFieldˣ} (hr : IsRatSec B r) (ε : ℤˣ) (c : AlgChart p σ D) {y : CxPts p σ}
    (hy : y ∈ c.e.source) : ∃ O ∈ 𝓝 y, IntegrableOn (logNorm φ r)
      (offSupp p σ (divOfRatSec φ.isLB hr) ∩ O) (ψ.chernPart D ε) := by
  set i := pick φ.isLB y
  have hi : y ∈ ptsIn p σ (B.U i) := mem_pick _ y
  have hyU := c.source_subset hy
  have hg := gen_mem (mem_ptsIn.1 hyU)
  have : Nonempty c.U := ⟨⟨_, hg⟩⟩
  have := functionField_isFractionRing_of_isAffineOpen X c.U c.affine
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := Γ(X, c.U)) (r i : X.functionField)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  change fnOf c.U hg a / fnOf c.U hg b = _ at hab
  have hb1 : fnOf c.U hg b ≠ 0 := (map_ne_zero_iff _ (fnOf_injective _ hg)).2 hb0
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div] at hab
    exact (r i).ne_zero hab.symm
  have hT := (isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) c.U)).mem_nhds (mem_over c.e hy hyU)
  have hd (s : Γ(X, c.U)) : ∀ᶠ v in 𝓝 (c.e y), DifferentiableAt ℂ (ev p σ c.U s ∘ c.e.symm) v :=
    (c.holo _ s).eventually_differentiableAt hT
  obtain ⟨δ, hδ, hae, hint⟩ := exists_integrableOn_log_norm_div volume (hd a) (hd b)
    (frequently_ne_zero hσ c ha0 hy hyU) (frequently_ne_zero hσ c hb0 hy hyU)
  have hT' := (isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (B.U i))).mem_nhds (mem_over c.e hy hi)
  obtain ⟨η, hη, hηs⟩ := nhds_basis_closedBall.mem_iff.1 (inter_mem hT' (ball_mem_nhds _ hδ))
  have hcont : ContinuousOn (fun v => c.chernDens ψ (c.e.symm v)) c.e.target :=
    continuousOn_const.mul (Complex.continuous_re.comp_continuousOn
      ((Continuous.matrix_det continuous_id).comp_continuousOn
        ((GlobalTheory.MixDens.chernMat_isForm k X p σ D _ ψ hψ).2.1 c)))
  obtain ⟨C, hC⟩ := (isCompact_closedBall (c.e y) η).exists_bound_of_continuousOn
    (hcont.mono fun v hv => (hηs hv).1.1)
  set O := c.e.source ∩ c.e ⁻¹' ball (c.e y) η
  have hO : IsOpen O := c.e.continuousOn.isOpen_inter_preimage c.e.open_source isOpen_ball
  set S := offSupp p σ (divOfRatSec φ.isLB hr) ∩ O
  have hS : IsOpen S := (isOpen_offSupp _).inter hO
  have hSs : S ⊆ c.e.source := fun z hz => hz.2.1
  have him : c.e '' S ⊆ closedBall (c.e y) η := by
    rintro _ ⟨z, hz, rfl⟩
    exact ball_subset_closedBall hz.2.2
  have hSi (z) (hz : z ∈ S) : z ∈ ptsIn p σ (B.U i) := by
    have := (hηs (him (mem_image_of_mem _ hz))).1.2
    rwa [mem_preimage, c.e.left_inv (hSs hz)] at this
  have hm := measurableSet_image c.e hS.measurableSet hSs
  refine ⟨O, hO.mem_nhds ⟨hy, by exact Set.mem_preimage.mpr (mem_ball_self hη)⟩, integrableOn_of_chart c.e
    (fun A hA hAs => Weight.chernPart_apply hψ ε c hA hAs) hS.measurableSet hSs
    (C := ENNReal.ofReal C) ENNReal.ofReal_ne_top (fun v hv => ENNReal.ofReal_le_ofReal ?_) ?_ ?_⟩
  · have h := hC v (him hv)
    rw [Real.norm_eq_abs, abs_le] at h
    rcases Int.units_eq_one_or ε with rfl | rfl
    · simpa using h.2
    · simpa [neg_le] using h.1
  · refine ContinuousOn.congr (f := fun z => Real.log ‖ratVal (r i : X.functionField) z‖ - φ.φ i z / 2)
      (fun z hz => ContinuousAt.continuousWithinAt ?_) fun z hz => logNorm_eq φ hr hz.1 (hSi z hz)
    have hu := hr.unitAt φ.isLB hz.1 (hSi z hz)
    exact ((continuousAt_ratVal hu.regAt).norm.log (norm_ne_zero_iff.2 (ratVal_ne_zero hu))).sub
      ((hφ i z (hSi z hz)).continuousAt.div_const 2)
  · have hsub : c.e '' S ⊆ ball (c.e y) δ := fun v hv => (hηs (him hv)).2
    have h₁ : IntegrableOn (fun v => (φ.φ i ∘ c.e.symm) v / 2) (c.e '' S) :=
      (((((contDiffOn_chart (hφ i) c).continuousOn.mono fun v hv => (hηs hv).1).div_const
        2).integrableOn_compact (isCompact_closedBall _ _)).mono_set him)
    refine ((hint.mono_set hsub).sub h₁).congr ?_
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hae, ae_restrict_mem hm] with v hv hv'
    obtain ⟨z, hz, rfl⟩ := hv'
    have hzU := c.source_subset (hSs hz)
    have hu := hr.unitAt φ.isLB hz.1 (hSi z hz)
    have e := ratVal_mul hu.regAt (regAt_fnOf (mem_ptsIn.1 hzU) hg b)
    rw [← hab, div_mul_cancel₀ _ hb1, hab, ratVal_fnOf hzU, ratVal_fnOf hzU] at e
    simp only [Function.comp_apply, Pi.sub_apply, c.e.left_inv (hSs hz)] at hv ⊢
    rw [logNorm_eq φ hr hz.1 (hSi z hz), e, mul_div_cancel_right₀ _ hv.2]

end GlobalTheory.LogNormInt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithVarComplexPointsCompact
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open GlobalTheory.Cartier
open ReciprocityTheory.AnForm.M

namespace GlobalTheory

theorem IsArithVar.finite_emb_and_topology : ∀ {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {D : ℕ}, IsArithVar p D →
    Finite (k →+* ℂ) ∧ ∀ σ : k →+* ℂ, CompactSpace (CxPts p σ) ∧ T2Space (CxPts p σ) ∧
      SecondCountableTopology (CxPts p σ) := fun h =>
  ⟨h.finite_emb, fun σ => ⟨h.compactSpace σ, CxPts.t2Space_cxPts_of_isProjOver σ h.isProjOver,
    CxPts.secondCountableTopology_of_isProjOver σ h.isProjOver⟩⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReprEqZeroOfCardNe
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.LineForm

namespace GlobalTheory.PullTop

theorem repr_eq_zero_of_card_ne {R M I : Type*} [CommRing R] [AddCommGroup M] [Module R M] [LinearOrder I]
    (b : Module.Basis I R M) {k : ℕ} (x : ⋀[R]^k M) {S : Finset I} (hS : S.card ≠ k) :
    b.ExteriorAlgebra.repr (x : ExteriorAlgebra R M) S = 0 := by
  have h : (Finsupp.lapply S ∘ₗ b.ExteriorAlgebra.repr.toLinearMap ∘ₗ (⋀[R]^k M).subtype) = 0 := by
    refine (b.exteriorPower k).ext fun s => ?_
    have hs : (s : Finset I) ≠ S := fun e => hS (e ▸ s.2)
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, ← ExteriorAlgebra.basis_eq_coe_basis,
      LinearEquiv.coe_coe, Module.Basis.repr_self, Finsupp.lapply_apply, LinearMap.zero_apply]
    exact Finsupp.single_eq_of_ne' hs
  exact LinearMap.congr_fun h x

end GlobalTheory.PullTop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompLinearEquivIntertwiningStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.comp_linearEquiv_intertwining : ∀ (O : Type) [Ring O] (bar : O → O) (D : PLat O bar) (g : ℕ) (ρ ρ₂ : O →+* Matrix (Fin g) (Fin g) ℂ) (P : D.La →+ (Fin g → ℂ)) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), IsPeriod D ρ P → (∀ a z, h (ρ a *ᵥ z) = ρ₂ a *ᵥ h z) → IsPeriod D ρ₂ (h.toLinearMap.toAddMonoidHom.comp P) := by
  first | exact @GlobalTheory.PELU.IsPeriod.comp_linearEquiv | exact GlobalTheory.PELU.IsPeriod.comp_linearEquiv | (intros; apply GlobalTheory.PELU.IsPeriod.comp_linearEquiv <;> assumption)
end
