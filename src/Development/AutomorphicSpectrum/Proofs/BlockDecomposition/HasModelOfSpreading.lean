module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.CubeTheorem.LBSpreads
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilRepresentationContinuity
public import Development.WeilBound.CoreStatements.AutomorphicKernels.WeilSiegelFormula.WeilSiegelSchwartz.EcHeisSch
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetCellInvariantUnipotent
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NondegenerateCharacterCellFactorization

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasModelOfSpreading
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasModelOfSpreading
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.SpreadingModels

namespace GlobalTheory.CompanionTheory.CubeModels

theorem model_refine {R R₀ R₁ : Type} [CommRing R] [CommRing R₀] [CommRing R₁] {φ : R₀ →+* R}
    {ψ : R₀ →+* R₁} {φ₁ : R₁ →+* R} (e : φ₁.comp ψ = φ) (ft : Algebra.FiniteType ℤ R₁)
    {Y Y₀ : Scheme.{0}} {f : Y ⟶ Spec (CommRingCat.of R)} {f₀ : Y₀ ⟶ Spec (CommRingCat.of R₀)}
    {π : Y ⟶ Y₀} (hm : IsModel φ f f₀ π)
    (ρ : Y ⟶ pullback f₀ (Spec.map (CommRingCat.ofHom ψ)))
    (h₁ : ρ ≫ pullback.fst _ _ = π)
    (h₂ : ρ ≫ pullback.snd _ _ = f ≫ Spec.map (CommRingCat.ofHom φ₁)) :
    IsModel φ₁ f (pullback.snd f₀ (Spec.map (CommRingCat.ofHom ψ))) ρ := by
  obtain ⟨-, l, q, s, sq⟩ := hm
  have hc : Spec.map (CommRingCat.ofHom φ) =
      Spec.map (CommRingCat.ofHom φ₁) ≫ Spec.map (CommRingCat.ofHom ψ) := by
    subst e
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  refine ⟨ft, inferInstance, inferInstance, inferInstance, ?_⟩
  refine IsPullback.of_right (h₁₂ := pullback.fst f₀ (Spec.map (CommRingCat.ofHom ψ)))
    (v₁₃ := f₀) (h₂₂ := Spec.map (CommRingCat.ofHom ψ)) ?_ h₂ (IsPullback.of_hasPullback _ _)
  rw [h₁, ← hc]
  exact sq

def refineMap {R R₀ R₁ : Type} [CommRing R] [CommRing R₀] [CommRing R₁] {φ : R₀ →+* R}
    {ψ : R₀ →+* R₁} {φ₁ : R₁ →+* R} (e : φ₁.comp ψ = φ)
    {Y Y₀ : Scheme.{0}} {f : Y ⟶ Spec (CommRingCat.of R)} {f₀ : Y₀ ⟶ Spec (CommRingCat.of R₀)}
    {π : Y ⟶ Y₀} (hm : IsModel φ f f₀ π) :
    Y ⟶ pullback f₀ (Spec.map (CommRingCat.ofHom ψ)) :=
  pullback.lift π (f ≫ Spec.map (CommRingCat.ofHom φ₁)) (by
    have hc : Spec.map (CommRingCat.ofHom φ) =
        Spec.map (CommRingCat.ofHom φ₁) ≫ Spec.map (CommRingCat.ofHom ψ) := by
      subst e
      rw [CommRingCat.ofHom_comp, Spec.map_comp]
    rw [Category.assoc, ← hc]
    exact hm.2.2.2.2.w)

theorem model_refine' {R R₀ R₁ : Type} [CommRing R] [CommRing R₀] [CommRing R₁] {φ : R₀ →+* R}
    {ψ : R₀ →+* R₁} {φ₁ : R₁ →+* R} (e : φ₁.comp ψ = φ) (ft : Algebra.FiniteType ℤ R₁)
    {Y Y₀ : Scheme.{0}} {f : Y ⟶ Spec (CommRingCat.of R)} {f₀ : Y₀ ⟶ Spec (CommRingCat.of R₀)}
    {π : Y ⟶ Y₀} (hm : IsModel φ f f₀ π) :
    IsModel φ₁ f (pullback.snd f₀ (Spec.map (CommRingCat.ofHom ψ))) (refineMap e hm) :=
  model_refine e ft hm _ (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

theorem hasModel_of_spreads : GlobalTheory.SpreadingModels.SchemeModels → GlobalTheory.SpreadingModels.Spreads (fun _ _ f => Smooth f) →
    GlobalTheory.SpreadingModels.Spreads (fun _ _ f => IsProper f) → GlobalTheory.SpreadingModels.LBSpreads →
    ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)), Smooth f → IsProper f →
      ∀ M : LB Y, M.IsLB → GlobalTheory.SpreadingModels.HasModel f M := by
  intro hS hSm hPr hLB R _ Y f hsm hpr M hM
  obtain ⟨R₀, _, φ, Y₀, f₀, π, hm⟩ := hS R Y f inferInstance inferInstance inferInstance
  obtain ⟨R₁, _, ψ₁, φ₁, e₁, ft₁, sm₁⟩ := hSm R R₀ φ Y Y₀ f f₀ π hm hsm
  have m₁ := model_refine' e₁ ft₁ hm
  obtain ⟨R₂, _, ψ₂, φ₂, e₂, ft₂, pr₂⟩ := hPr R R₁ φ₁ Y _ f _ _ m₁ hpr
  have m₂ := model_refine' e₂ ft₂ m₁
  obtain ⟨R₃, _, ψ₃, φ₃, ρ, e₃, ft₃, r₁, r₂, M₃, hM₃, w, hw⟩ := hLB R R₂ φ₂ Y _ f _ _ m₂ M hM
  have m₃ := model_refine e₃ ft₃ m₂ ρ r₁ r₂
  have sm₁' : Smooth (pullback.snd f₀ (Spec.map (CommRingCat.ofHom ψ₁))) := sm₁
  have pr₂' : IsProper (pullback.snd (pullback.snd f₀ (Spec.map (CommRingCat.ofHom ψ₁)))
      (Spec.map (CommRingCat.ofHom ψ₂))) := pr₂
  refine ⟨R₃, inferInstance, Algebra.FiniteType.isNoetherianRing ℤ R₃, φ₃, _,
    pullback.snd (pullback.snd (pullback.snd f₀ (Spec.map (CommRingCat.ofHom ψ₁)))
      (Spec.map (CommRingCat.ofHom ψ₂))) (Spec.map (CommRingCat.ofHom ψ₃)), ρ,
    inferInstance, inferInstance, m₃.2.2.2.2, M₃, hM₃, w, hw⟩

end GlobalTheory.CompanionTheory.CubeModels
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasModelOfSpreadingStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.SpreadingModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.has_model_of_spreading : GlobalTheory.SpreadingModels.SchemeModels → GlobalTheory.SpreadingModels.Spreads (fun _ _ f => Smooth f) → GlobalTheory.SpreadingModels.Spreads (fun _ _ f => IsProper f) → GlobalTheory.SpreadingModels.LBSpreads → ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)), Smooth f → IsProper f → ∀ M : LB Y, M.IsLB → GlobalTheory.SpreadingModels.HasModel f M := by
  first | exact @GlobalTheory.CompanionTheory.CubeModels.hasModel_of_spreads | exact GlobalTheory.CompanionTheory.CubeModels.hasModel_of_spreads | (intros; apply GlobalTheory.CompanionTheory.CubeModels.hasModel_of_spreads <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilRepresentationContinuityStatement
open GlobalTheory.CompanionTheory.ThTot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_representation_continuity : WeilCont := by
  first | exact @GlobalTheory.CompanionTheory.ThTot.weilCont | exact GlobalTheory.CompanionTheory.ThTot.weilCont | (intros; apply GlobalTheory.CompanionTheory.ThTot.weilCont <;> assumption)
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinHeisenbergSchwartz
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinHeisenbergSchwartz
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.HeisSchwartz

theorem heisSch_holds : PositivityTheory.GramSchwartzFunctions.EC.HeisSch := PositivityTheory.RdEc.heisSch

end GlobalTheory.CompanionTheory.HeisSchwartz
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinHeisenbergSchwartzStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_heisenberg_schwartz : PositivityTheory.GramSchwartzFunctions.EC.HeisSch := by
  first | exact @GlobalTheory.CompanionTheory.HeisSchwartz.heisSch_holds | exact GlobalTheory.CompanionTheory.HeisSchwartz.heisSch_holds | (intros; apply GlobalTheory.CompanionTheory.HeisSchwartz.heisSch_holds <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreIntegralIntertwinesUnipotent
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreIntegralIntertwinesUnipotent
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibQ

section Abstract

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def mulVecHomeo {t : ℕ} (w : GL (Fin t) k) : (Fin t → k) ≃ₜ (Fin t → k) where
  toFun v := (w : Matrix (Fin t) (Fin t) k).mulVec v
  invFun v := ((w⁻¹ : GL (Fin t) k) : Matrix (Fin t) (Fin t) k).mulVec v
  left_inv v := by
    show ((w⁻¹ : GL (Fin t) k) : Matrix (Fin t) (Fin t) k).mulVec ((w : Matrix (Fin t) (Fin t) k).mulVec v) = v
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  right_inv v := by
    show (w : Matrix (Fin t) (Fin t) k).mulVec (((w⁻¹ : GL (Fin t) k) : Matrix (Fin t) (Fin t) k).mulVec v) = v
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  continuous_toFun := Continuous.matrix_mulVec continuous_const continuous_id
  continuous_invFun := Continuous.matrix_mulVec continuous_const continuous_id

theorem smInt_transform {t : ℕ} [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)]
    (μ : MeasureTheory.Measure (Fin t → k)) [μ.IsAddHaarMeasure]
    {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (Φ Ψ : (Fin t → k) → X) (B : X →ₗ[ℂ] Y) (A : Y →ₗ[ℂ] Y) (w : GL (Fin t) k)
    (lΦ : IsLocallyConstant Φ) (cΦ : HasCompactSupport Φ)
    (lΨ : IsLocallyConstant Ψ) (cΨ : HasCompactSupport Ψ)
    (h : ∀ v, B (Φ v) = A (B (Ψ (((w⁻¹ : GL (Fin t) k) : Matrix (Fin t) (Fin t) k).mulVec v)))) :
    B (smInt μ Φ) = ((detChar (Fin t) (absPow k (1 : ℂ)) w : ℂˣ) : ℂ) • A (B (smInt μ Ψ)) := by
  have lG : IsLocallyConstant (B ∘ Ψ) := lΨ.comp B
  have cG : HasCompactSupport (B ∘ Ψ) := cΨ.comp_left (map_zero B)
  have lGL : IsLocallyConstant ((B ∘ Ψ) ∘ (mulVecHomeo w⁻¹)) := lG.comp_continuous (mulVecHomeo w⁻¹).continuous
  have cGL : HasCompactSupport ((B ∘ Ψ) ∘ (mulVecHomeo w⁻¹)) := cG.comp_homeomorph (mulVecHomeo w⁻¹)
  calc B (smInt μ Φ) = smInt μ (B ∘ Φ) := (SmIntEl.smInt_linear μ B lΦ cΦ).symm
    _ = smInt μ (A ∘ ((B ∘ Ψ) ∘ (mulVecHomeo w⁻¹))) := congrArg (smInt μ) (funext h)
    _ = A (smInt μ ((B ∘ Ψ) ∘ (mulVecHomeo w⁻¹))) := SmIntEl.smInt_linear μ A lGL cGL
    _ = A (((detChar (Fin t) (absPow k (1 : ℂ)) w : ℂˣ) : ℂ) • smInt μ (B ∘ Ψ)) :=
        congrArg A (GlobalTheory.T.smooth_integral_linear_change k t μ w (B ∘ Ψ) lG cG)
    _ = ((detChar (Fin t) (absPow k (1 : ℂ)) w : ℂˣ) : ℂ) • A (smInt μ (B ∘ Ψ)) := map_smul A _ _
    _ = ((detChar (Fin t) (absPow k (1 : ℂ)) w : ℂˣ) : ℂ) • A (B (smInt μ Ψ)) :=
        congrArg (fun z => ((detChar (Fin t) (absPow k (1 : ℂ)) w : ℂˣ) : ℂ) • A z) (SmIntEl.smInt_linear μ B lΨ cΨ)

end Abstract

section Group

variable (k : Type) [Field k]

theorem point_eq (i t : ℕ) (q g : GL (Fin (i + t)) k) (y : Fin (i + t) → k) (x : Fin i → k) (u : Fin t → k)
    (hx : ((q⁻¹ : GL (Fin (i + t)) k) : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec y = topV k i t x + midV k i t u) :
    uM k (i + t) y * levi k (i + t) (q * g) =
      levi k (i + t) q * uM k (i + t) (topV k i t x) * (uM k (i + t) (midV k i t u) * levi k (i + t) g) := by
  have h := levi_mul_uM k (i + t) q⁻¹ y
  rw [hx, uM_add, map_inv] at h
  have h2 : uM k (i + t) y =
      levi k (i + t) q * (uM k (i + t) (topV k i t x) * uM k (i + t) (midV k i t u) * (levi k (i + t) q)⁻¹) :=
    inv_mul_eq_iff_eq_mul.mp h
  calc uM k (i + t) y * levi k (i + t) (q * g)
      = levi k (i + t) q * (uM k (i + t) (topV k i t x) * uM k (i + t) (midV k i t u) * (levi k (i + t) q)⁻¹) *
          (levi k (i + t) q * levi k (i + t) g) := by rw [map_mul, ← h2]
    _ = _ := by group

end Group

section Rep

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {i t : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem clT_extTensor (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W)
    (a : GL (Fin i) k) (x : Fin i → k) (w : GL (Fin t) k) (z : V ⊗[ℂ] W) :
    clT τ W (extTensor τ σ (levi k i a * uM k i x, w) z) =
      extTensor (psiMinus k τ) σ (a, w) (clT τ W z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul v u =>
    have e : (twKer τ (MirUin k i) 1).mkQ (τ (uM k i x) v) = (twKer τ (MirUin k i) 1).mkQ v := by
      refine (Submodule.Quotient.eq _).2 (Submodule.subset_span ⟨⟨uM k i x, uM_mem k i x⟩, v, ?_⟩)
      simp
    have e2 : (twKer τ (MirUin k i) 1).mkQ (τ (levi k i a * uM k i x) v) =
        psiMinus k τ a ((twKer τ (MirUin k i) 1).mkQ v) := by
      rw [← e, map_mul]
      rfl
    simp only [clT, extTensor_tmul, LinearMap.rTensor_tmul]
    rw [e2]

theorem fibV_mul (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W)
    (f : cIndSpace (HPG k i t) (hRep τ σ)) (q : Qp k i t) (g : GL (Fin (i + t)) k) (v u : Fin t → k) (x : Fin i → k)
    (hx : (((q : GL (Fin (i + t)) k)⁻¹ : GL (Fin (i + t)) k) : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec (midV k i t v) =
      topV k i t x + midV k i t u) :
    fibV f ((q : GL (Fin (i + t)) k) * g) v =
      extTensor τ σ (levi k i (qBlocks k i t q).1 * uM k i x, (qBlocks k i t q).2) (fibV f g u) := by
  obtain ⟨m1, p1⟩ := GlobalTheory.T.levi_block_mem_parabolic k i t q
  obtain ⟨m2, p2⟩ := GlobalTheory.T.unipotent_top_mem_parabolic k i t x
  have key := f.1.1.2 ((⟨_, m1⟩ : HPG k i t) * ⟨_, m2⟩) (uM k (i + t) (midV k i t u) * levi k (i + t) g)
  have e : pgProj k i t ((⟨_, m1⟩ : HPG k i t) * ⟨_, m2⟩) =
      (levi k i (qBlocks k i t q).1 * uM k i x, (qBlocks k i t q).2) := by
    rw [map_mul, p1, p2]
    simp
  calc fibV f ((q : GL (Fin (i + t)) k) * g) v
      = f.1.1.1 (levi k (i + t) (q : GL (Fin (i + t)) k) * uM k (i + t) (topV k i t x) *
          (uM k (i + t) (midV k i t u) * levi k (i + t) g)) :=
        congrArg f.1.1.1 (point_eq k i t _ g _ x u hx)
    _ = extTensor τ σ (pgProj k i t ((⟨_, m1⟩ : HPG k i t) * ⟨_, m2⟩)) (fibV f g u) := key
    _ = _ := congrArg (fun y => extTensor τ σ y (fibV f g u)) e

end Rep

theorem main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W), IsSmooth τ → IsSmooth σ → ∀ [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k)) [μ.IsAddHaarMeasure], ∀ (f : cIndSpace (HPG k i t) (hRep τ σ)) (q : Qp k i t) (g : GL (Fin (i + t)) k), fibInt μ f ((q : GL (Fin (i + t)) k) * g) = qRep τ σ q (fibInt μ f g) := by
  intro k _ _ _ _ i t V W _ _ _ _ τ σ hτ hσ _ _ μ _ f q g
  have h1 := GlobalTheory.T.fibre_function_locally_constant_compact k i t τ σ hτ hσ f ((q : GL (Fin (i + t)) k) * g)
  have h2 := GlobalTheory.T.fibre_function_locally_constant_compact k i t τ σ hτ hσ f g
  have hpt : ∀ v, clT τ W (fibV f ((q : GL (Fin (i + t)) k) * g) v) =
      extTensor (psiMinus k τ) σ ((qBlocks k i t q).1, (qBlocks k i t q).2)
        (clT τ W (fibV f g ((((qBlocks k i t q).2⁻¹ : GL (Fin t) k) : Matrix (Fin t) (Fin t) k).mulVec v))) := by
    intro v
    obtain ⟨x, hx⟩ := GlobalTheory.T.mulVec_mid_block_decomp k i t q⁻¹ v
    have hb : (qBlocks k i t q⁻¹).2 = (qBlocks k i t q).2⁻¹ := by
      rw [map_inv, Prod.snd_inv]
    rw [hb] at hx
    have e := fibV_mul τ σ f q g v _ x hx
    exact (congrArg (clT τ W) e).trans (clT_extTensor τ σ _ x _ _)
  exact smInt_transform μ _ _ (clT τ W)
    (extTensor (psiMinus k τ) σ ((qBlocks k i t q).1, (qBlocks k i t q).2)) (qBlocks k i t q).2
    h1.1 h1.2 h2.1 h2.2 hpt

end GlobalTheory.CompanionTheory.BZPsiPG.FibQ

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreIntegralIntertwinesUnipotentStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_integral_intertwines_unipotent : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W), IsSmooth τ → IsSmooth σ → ∀ [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k)) [μ.IsAddHaarMeasure], ∀ (f : cIndSpace (HPG k i t) (hRep τ σ)) (q : Qp k i t) (g : GL (Fin (i + t)) k), fibInt μ f ((q : GL (Fin (i + t)) k) * g) = qRep τ σ q (fibInt μ f g) := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.FibQ.main | exact GlobalTheory.CompanionTheory.BZPsiPG.FibQ.main | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.FibQ.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoefficientHeisenbergEquivariance
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionInvariantHeisenbergWeyl
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionInvariantHeisenbergWeyl
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE.LawW

open GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.PcB

variable {D : D7} {n ρ p : ℕ} {hn : ρ + p = n}

def qm (hn : ρ + p = n) (x : Mx D ρ p) : Mx D (n + n) (n + n) :=
  blk4 (bl hn 1 0 (adj x) 1) 0 0 (bl hn 1 (-x) 0 1)

theorem qm_mul_w (M : Maps D hn) (x : Mx D ρ p) :
    qm hn x * mat M.w = mat M.w * mat (M.nzx 0 x) := by
  rw [M.w_mat, M.nzx_mat, qm, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
  have hz : ((0 : hermA D ρ).1 : Mx D ρ ρ) = 0 := rfl
  rw [hz]
  simp only [bl, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, add_zero, zero_add, Matrix.neg_mul, neg_zero, neg_neg]
  congr 1
  · change _ = (Matrix.fromBlocks 0 0 (adj x) 0 + Matrix.fromBlocks 1 0 0 0).submatrix _ _
    rw [Matrix.fromBlocks_add]; simp
  · change _ = (Matrix.fromBlocks 0 (-x) 0 0 + Matrix.fromBlocks 0 0 0 1).submatrix _ _
    rw [Matrix.fromBlocks_add]; simp

theorem mat_conj (M : Maps D hn) (x : Mx D ρ p) : mat (M.w * M.nzx 0 x * M.w⁻¹) = qm hn x := by
  have h : mat M.w * mat M.w⁻¹ = 1 := by rw [← mat_mul, mul_inv_cancel, mat_one]
  calc mat (M.w * M.nzx 0 x * M.w⁻¹) = (mat M.w * mat (M.nzx 0 x)) * mat M.w⁻¹ := rfl
    _ = qm hn x * (mat M.w * mat M.w⁻¹) := by rw [← qm_mul_w, mul_assoc]
    _ = qm hn x := by rw [h, mul_one]

theorem exists_low (hn : ρ + p = n) (c : Mx D p ρ) :
    ∃ a : GL (Fin n) (AE D), a.1 = bl hn 1 0 c 1 :=
  ⟨⟨bl hn 1 0 c 1, bl hn 1 0 (-c) 1, by rw [lowerUnipotent_mul, add_neg_cancel, blockMatrix_one], by rw [lowerUnipotent_mul, neg_add_cancel, blockMatrix_one]⟩, rfl⟩

theorem det_low (hn : ρ + p = n) (c : Mx D p ρ) (a : GL (Fin n) (AE D)) (ha : a.1 = bl hn 1 0 c 1) :
    Matrix.GeneralLinearGroup.det a = 1 := by
  apply Units.ext
  change a.1.det = 1
  rw [ha, bl, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₁₂]
  simp

theorem blkA_qm (hn : ρ + p = n) (x : Mx D ρ p) : blkA (qm hn x) = bl hn 1 0 (adj x) 1 := by
  ext i j
  simp [qm, blkA, blk4, Matrix.toBlocks₁₁]

theorem law_w : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (χ : (AE D)ˣ →* Circle) (s : ℂ) (f : G D n → ℂ),
    IsLaw χ s f → ∀ (x : Mx D ρ p) (h : G D n), f (M.w * M.nzx 0 x * h) = f (M.w * h) := by
  intro D n ρ p hn M χ s f hf x h
  have hq := mat_conj M x
  have hP : M.w * M.nzx 0 x * M.w⁻¹ ∈ P D n := GlobalTheory.CompanionTheory.SwUnf.SmallCell.mem_siegelParabolic_of_lowerLeft_entries_eq_zero hq
  obtain ⟨a, ha⟩ := exists_low hn (adj x)
  have hA : blkA (mat (M.w * M.nzx 0 x * M.w⁻¹)) = a.1 := by rw [hq, blkA_qm, ha]
  have key := hf _ hP a hA (M.w * h)
  rw [det_low hn (adj x) a ha, map_one, map_one] at key
  have e : M.w * M.nzx 0 x * M.w⁻¹ * (M.w * h) = M.w * M.nzx 0 x * h := by group
  rw [e] at key
  simpa using key

end GlobalTheory.CompanionTheory.FJE.LawW
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionInvariantHeisenbergWeylStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.section_invariant_heisenberg_weyl : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (χ : (AE D)ˣ →* Circle) (s : ℂ) (f : G D n → ℂ), IsLaw χ s f → ∀ (x : Mx D ρ p) (h : G D n), f (M.w * M.nzx 0 x * h) = f (M.w * h) := by
  first | exact @GlobalTheory.CompanionTheory.FJE.LawW.law_w | exact GlobalTheory.CompanionTheory.FJE.LawW.law_w | (intros; apply GlobalTheory.CompanionTheory.FJE.LawW.law_w <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoefficientHeisenbergEquivariance
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE

theorem Wz_sh_nzx : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (m : Meas D ρ p)
    (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (b₀ : HermE D ρ) (χ : (AE D)ˣ →* Circle) (s : ℂ)
    (f : G D n → ℂ), IsLaw χ s f → ∀ (η : Mx D ρ p) (z : hermA D ρ) (x : Mx D ρ p) (h : G D n),
    Wz M m ψ b₀ f (M.sh η * (M.nzx z x * h)) =
      chz ψ b₀ z * GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x η * Wz M m ψ b₀ f (M.sh η * h) := by
  intro D n ρ p hn M m ψ hψ b₀ χ s f hf η z x h
  obtain ⟨hadd, hnorm, -, -⟩ := GlobalTheory.T.centre_character_properties ψ hψ b₀
  have hjc := GlobalTheory.T.centre_character_commutator ψ b₀ η x
  have hsh := GlobalTheory.T.shift_conj_heisenberg M η z x
  have hmul := GlobalTheory.T.unipotent_heisenberg_mul M
  have hw := GlobalTheory.T.section_invariant_heisenberg_weyl M χ s f hf
  have e1 : M.sh η * (M.nzx z x * h) = M.nzx (z + jc η x) x * (M.sh η * h) := by
    rw [← mul_assoc, hsh, mul_assoc]
  rw [e1]
  generalize M.sh η * h = h'
  have hc : chz ψ b₀ z * chv ψ b₀ x η = chz ψ b₀ (z + jc η x) := by rw [hadd, hjc]
  rw [hc]
  generalize z + jc η x = c
  have hcc : chz ψ b₀ c * conj (chz ψ b₀ c) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm c]
    simp
  have hconj : ∀ t, conj (chz ψ b₀ t) = conj (chz ψ b₀ (t + c)) * chz ψ b₀ c := by
    intro t
    have hh : conj (chz ψ b₀ (t + c)) * chz ψ b₀ c = conj (chz ψ b₀ t) * (chz ψ b₀ c * conj (chz ψ b₀ c)) := by
      rw [hadd, map_mul]; ring
    rw [hh, hcc, mul_one]
  have hpt : ∀ t : hermA D ρ, f (M.w * M.nzx t 0 * (M.nzx c x * h')) =
      f (M.w * M.nzx (t + c) 0 * h') := by
    intro t
    have e2 : M.w * M.nzx t 0 * (M.nzx c x * h') = M.w * M.nzx 0 x * (M.nzx (t + c) 0 * h') := by
      have a1 : M.nzx t 0 * M.nzx c x = M.nzx 0 x * M.nzx (t + c) 0 := by
        rw [hmul, hmul]; simp
      calc M.w * M.nzx t 0 * (M.nzx c x * h') = M.w * (M.nzx t 0 * M.nzx c x) * h' := by
            simp only [mul_assoc]
        _ = M.w * M.nzx 0 x * (M.nzx (t + c) 0 * h') := by
            rw [a1]; simp only [mul_assoc]
    rw [e2, hw, mul_assoc]
  haveI := m.hz.1
  haveI : ContinuousAdd (hermA D ρ) := ⟨Continuous.subtype_mk ((continuous_subtype_val.comp continuous_fst).add
    (continuous_subtype_val.comp continuous_snd)) _⟩
  haveI : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
  haveI : BorelSpace (hermA D ρ) := Subtype.borelSpace _
  haveI : MeasurableAdd (hermA D ρ) := ContinuousAdd.measurableAdd
  unfold Wz
  calc ∫ t, f (M.w * M.nzx t 0 * (M.nzx c x * h')) * conj (chz ψ b₀ t) ∂m.lz
      = ∫ t, (fun u => f (M.w * M.nzx u 0 * h') * (conj (chz ψ b₀ u) * chz ψ b₀ c)) (t + c) ∂m.lz := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        show f (M.w * M.nzx t 0 * (M.nzx c x * h')) * conj (chz ψ b₀ t) = f (M.w * M.nzx (t + c) 0 * h') * (conj (chz ψ b₀ (t + c)) * chz ψ b₀ c)
        rw [hpt, ← hconj]
    _ = ∫ u, f (M.w * M.nzx u 0 * h') * (conj (chz ψ b₀ u) * chz ψ b₀ c) ∂m.lz :=
        integral_add_right_eq_self (μ := m.lz)
          (fun u => f (M.w * M.nzx u 0 * h') * (conj (chz ψ b₀ u) * chz ψ b₀ c)) c
    _ = chz ψ b₀ c * ∫ u, f (M.w * M.nzx u 0 * h') * conj (chz ψ b₀ u) ∂m.lz := by
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
        show _ = _
        ring

end GlobalTheory.CompanionTheory.FJE
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoefficientHeisenbergEquivarianceStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coefficient_heisenberg_equivariance : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (b₀ : HermE D ρ) (χ : (AE D)ˣ →* Circle) (s : ℂ) (f : G D n → ℂ), IsLaw χ s f → ∀ (η : Mx D ρ p) (z : hermA D ρ) (x : Mx D ρ p) (h : G D n), Wz M m ψ b₀ f (M.sh η * (M.nzx z x * h)) = chz ψ b₀ z * GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x η * Wz M m ψ b₀ f (M.sh η * h) := by
  first | exact @GlobalTheory.CompanionTheory.FJE.Wz_sh_nzx | exact GlobalTheory.CompanionTheory.FJE.Wz_sh_nzx | (intros; apply GlobalTheory.CompanionTheory.FJE.Wz_sh_nzx <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoefficientUnipotentLeviInvariance
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoefficientUnipotentLeviInvariance
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.WzHeis

section Blocks
variable {R : Type} [CommRing R] {n ρ p : ℕ} (hn : ρ + p = n)

theorem block_mul₂ (a a' : Matrix (Fin ρ) (Fin ρ) R) (b b' : Matrix (Fin ρ) (Fin p) R)
    (c c' : Matrix (Fin p) (Fin ρ) R) (d d' : Matrix (Fin p) (Fin p) R) :
    bl hn a b c d * bl hn a' b' c' d' =
      bl hn (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  unfold bl
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem blockRowSubstitution_one : bl hn (1 : Matrix (Fin ρ) (Fin ρ) R) 0 0 1 = 1 := by
  unfold bl
  rw [Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

theorem bl_add (a a' : Matrix (Fin ρ) (Fin ρ) R) (b b' : Matrix (Fin ρ) (Fin p) R)
    (c c' : Matrix (Fin p) (Fin ρ) R) (d d' : Matrix (Fin p) (Fin p) R) :
    bl hn a b c d + bl hn a' b' c' d' = bl hn (a + a') (b + b') (c + c') (d + d') := by
  unfold bl
  rw [← Matrix.fromBlocks_add]
  rfl

theorem block_sub (a a' : Matrix (Fin ρ) (Fin ρ) R) (b b' : Matrix (Fin ρ) (Fin p) R)
    (c c' : Matrix (Fin p) (Fin ρ) R) (d d' : Matrix (Fin p) (Fin p) R) :
    bl hn a b c d - bl hn a' b' c' d' = bl hn (a - a') (b - b') (c - c') (d - d') := by
  ext i j
  simp only [bl, Matrix.sub_apply, Matrix.submatrix_apply]
  rcases (finSumFinEquiv.trans (finCongr hn)).symm i with i | i <;>
    rcases (finSumFinEquiv.trans (finCongr hn)).symm j with j | j <;> rfl

theorem blockMatrix_zero : bl hn (0 : Matrix (Fin ρ) (Fin ρ) R) 0 0 0 = 0 := by
  ext i j
  simp only [bl, Matrix.zero_apply, Matrix.submatrix_apply]
  rcases (finSumFinEquiv.trans (finCongr hn)).symm i with i | i <;>
    rcases (finSumFinEquiv.trans (finCongr hn)).symm j with j | j <;> rfl

theorem det_bl_lower (c : Matrix (Fin p) (Fin ρ) R) : (bl hn 1 0 c 1).det = 1 := by
  unfold bl
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₁₂]
  simp

end Blocks

variable {D : D7} {n ρ p : ℕ}

theorem adj_bl (hn : ρ + p = n) (a : Mx D ρ ρ) (b : Mx D ρ p) (c : Mx D p ρ) (d : Mx D p p) :
    adj (bl hn a b c d) = bl hn (adj a) (adj c) (adj b) (adj d) := by
  ext i j
  simp only [adj, bl, Matrix.transpose_apply, Matrix.map_apply, Matrix.submatrix_apply]
  rcases (finSumFinEquiv.trans (finCongr hn)).symm i with i | i <;>
    rcases (finSumFinEquiv.trans (finCongr hn)).symm j with j | j <;> rfl

open GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect

theorem chz_add (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ) (a b : hermA D ρ) :
    chz ψ b₀ (a + b) = chz ψ b₀ a * chz ψ b₀ b := by
  have e : chz ψ b₀ (a + b) = ψ (GlobalTheory.CompanionTheory.FourierN.pr b₀.1 (a.1 + b.1)) := rfl
  rw [e, GlobalTheory.CompanionTheory.FourierN.pr_add_right, AddChar.map_add_eq_mul]
  rfl

theorem conj_chz (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D ρ) (a b : hermA D ρ) :
    conj (chz ψ b₀ a) = conj (chz ψ b₀ (a + b)) * chz ψ b₀ b := by
  have hb : ‖chz ψ b₀ b‖ = 1 := hψ.2.1 _
  rw [chz_add, map_mul, mul_assoc, Complex.conj_mul', hb]
  simp

variable {hn : ρ + p = n} (M : Maps D hn)

theorem mat_u (g₁ : G D p) (b : Mx D p p) (hg : mat g₁ = blk4 1 b 0 1) (x₀ : Mx D ρ p) :
    mat (M.nzx 0 x₀ * M.emb g₁) = blk4 1 (bl hn 0 x₀ (adj x₀) b) 0 1 := by
  have h1 := M.emb_mat g₁ 1 b 0 1 hg
  rw [blockRowSubstitution_one, blockMatrix_zero] at h1
  rw [LeftInvSect.mat_mul, M.nzx_mat, h1, submatrix_fromBlocks_mul]
  simp [bl_add]

theorem nzx_comm (g₁ : G D p) (b : Mx D p p) (hg : mat g₁ = blk4 1 b 0 1) (x₀ : Mx D ρ p) (ζ z₀ : hermA D ρ) :
    M.nzx ζ 0 * (M.nzx z₀ x₀ * M.emb g₁) = (M.nzx 0 x₀ * M.emb g₁) * M.nzx (ζ + z₀) 0 := by
  have h1 := M.emb_mat g₁ 1 b 0 1 hg
  rw [blockRowSubstitution_one, blockMatrix_zero] at h1
  apply GlobalTheory.CompanionTheory.FourierN.mat_injective
  rw [LeftInvSect.mat_mul, LeftInvSect.mat_mul, LeftInvSect.mat_mul, mat_u M g₁ b hg, M.nzx_mat, M.nzx_mat, M.nzx_mat, h1]
  simp only [submatrix_fromBlocks_mul, bl_add, adj_zero, mul_one, one_mul, mul_zero, zero_mul, add_zero, zero_add]
  rw [show (ζ + z₀).1 = z₀.1 + ζ.1 from add_comm _ _]

theorem q_mat (g₁ : G D p) (b : Mx D p p) (hg : mat g₁ = blk4 1 b 0 1) (x₀ : Mx D ρ p) :
    ∃ (β δ : Mx D n n), mat (M.w * (M.nzx 0 x₀ * M.emb g₁) * M.w⁻¹) = blk4 (bl hn 1 0 (adj x₀) 1) β 0 δ := by
  have h := GlobalTheory.CompanionTheory.SwUnf.SmallCell.conj_block M.w (M.nzx 0 x₀ * M.emb g₁) M.w_mat (mat_u M g₁ b hg x₀)
  have hC : adj (bl hn (-1 : Mx D ρ ρ) 0 0 0) = bl hn (-1) 0 0 0 := by
    simp [adj_bl, adj_zero, adj_neg, adj_one]
  rw [hC] at h
  have e1 : (1 : Mx D n n) - bl hn 0 0 0 1 * bl hn 0 x₀ (adj x₀) b * bl hn (-1) 0 0 0 = bl hn 1 0 (adj x₀) 1 := by
    rw [← blockRowSubstitution_one hn]
    simp [block_mul₂, block_sub]
  have e2 : -(bl hn (-1 : Mx D ρ ρ) 0 0 0 * bl hn 0 x₀ (adj x₀) b * bl hn (-1) 0 0 0) = (0 : Mx D n n) := by
    simp [block_mul₂, blockMatrix_zero]
  rw [e1, e2] at h
  exact ⟨_, _, h⟩

theorem law_q (χ : (AE D)ˣ →* Circle) (z : ℂ) (f : G D n → ℂ) (hf : IsLaw χ z f) (g₁ : G D p) (b : Mx D p p)
    (hg : mat g₁ = blk4 1 b 0 1) (x₀ : Mx D ρ p) (v : G D n) :
    f (M.w * (M.nzx 0 x₀ * M.emb g₁) * M.w⁻¹ * v) = f v := by
  obtain ⟨β, δ, hq⟩ := q_mat M g₁ b hg x₀
  let a : GL (Fin n) (AE D) := ⟨bl hn 1 0 (adj x₀) 1, bl hn 1 0 (-adj x₀) 1,
    by simp [block_mul₂, blockRowSubstitution_one], by simp [block_mul₂, blockRowSubstitution_one]⟩
  have hdet : Matrix.GeneralLinearGroup.det a = 1 := Units.ext (det_bl_lower hn _)
  have hA : blkA (mat (M.w * (M.nzx 0 x₀ * M.emb g₁) * M.w⁻¹)) = a.1 := by
    rw [hq]
    simp [blkA, blk4, a]
  rw [hf _ (GlobalTheory.CompanionTheory.SwUnf.SmallCell.mem_siegelParabolic_of_lowerLeft_entries_eq_zero hq) a hA v, hdet, map_one, map_one]
  simp [npow]

theorem wz_heis : ∀ (D : D7) (n ρ p : ℕ) (hn : ρ + p = n) (M : Maps D hn) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ →
  ∀ (b₀ : HermE D ρ) (χ : (AE D)ˣ →* Circle) (z : ℂ) (f : G D n → ℂ), IsLaw χ z f → ∀ (g₁ : G D p) (b : Mx D p p),
  mat g₁ = blk4 1 b 0 1 → ∀ (z₀ : hermA D ρ) (x₀ : Mx D ρ p) (x : G D n),
    Wz M m ψ b₀ f (M.nzx z₀ x₀ * M.emb g₁ * x) = chz ψ b₀ z₀ * Wz M m ψ b₀ f x := by
  intro D n ρ p hn M m ψ hψ b₀ χ z f hf g₁ b hg z₀ x₀ x
  obtain ⟨i1, i2, i3, i4, -, -⟩ := GlobalTheory.TowerResNonzero.lattice_ratMx D ρ ρ
  haveI : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
  haveI : BorelSpace (hermA D ρ) := Subtype.borelSpace _
  haveI : SecondCountableTopology (hermA D ρ) := TopologicalSpace.Subtype.secondCountableTopology _
  obtain ⟨hlam, -, -⟩ := m.hz
  have step : ∀ ζ : hermA D ρ, f (M.w * M.nzx ζ 0 * (M.nzx z₀ x₀ * M.emb g₁ * x)) =
      f (M.w * M.nzx (ζ + z₀) 0 * x) := by
    intro ζ
    have e : M.w * M.nzx ζ 0 * (M.nzx z₀ x₀ * M.emb g₁ * x) =
        M.w * (M.nzx 0 x₀ * M.emb g₁) * M.w⁻¹ * (M.w * M.nzx (ζ + z₀) 0 * x) := by
      have h := nzx_comm M g₁ b hg x₀ ζ z₀
      calc M.w * M.nzx ζ 0 * (M.nzx z₀ x₀ * M.emb g₁ * x)
          = M.w * (M.nzx ζ 0 * (M.nzx z₀ x₀ * M.emb g₁)) * x := by group
        _ = M.w * ((M.nzx 0 x₀ * M.emb g₁) * M.nzx (ζ + z₀) 0) * x := by rw [h]
        _ = _ := by group
    rw [e, law_q M χ z f hf g₁ b hg x₀]
  unfold Wz
  calc ∫ ζ, f (M.w * M.nzx ζ 0 * (M.nzx z₀ x₀ * M.emb g₁ * x)) * conj (chz ψ b₀ ζ) ∂m.lz
      = ∫ ζ, (fun y => chz ψ b₀ z₀ * (f (M.w * M.nzx y 0 * x) * conj (chz ψ b₀ y))) (ζ + z₀) ∂m.lz := by
        refine integral_congr_ae (.of_forall fun ζ => ?_)
        show f (M.w * M.nzx ζ 0 * (M.nzx z₀ x₀ * M.emb g₁ * x)) * conj (chz ψ b₀ ζ) =
          chz ψ b₀ z₀ * (f (M.w * M.nzx (ζ + z₀) 0 * x) * conj (chz ψ b₀ (ζ + z₀)))
        rw [step, conj_chz ψ hψ b₀ ζ z₀]
        ring
    _ = ∫ y, chz ψ b₀ z₀ * (f (M.w * M.nzx y 0 * x) * conj (chz ψ b₀ y)) ∂m.lz :=
        integral_add_right_eq_self (μ := m.lz) (fun y => chz ψ b₀ z₀ * (f (M.w * M.nzx y 0 * x) * conj (chz ψ b₀ y))) z₀
    _ = _ := integral_const_mul _ _

end GlobalTheory.CompanionTheory.WzHeis
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoefficientUnipotentLeviInvarianceStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coefficient_unipotent_levi_invariance : ∀ (D : D7) (n ρ p : ℕ) (hn : ρ + p = n) (M : Maps D hn) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ →
  ∀ (b₀ : HermE D ρ) (χ : (AE D)ˣ →* Circle) (z : ℂ) (f : G D n → ℂ), IsLaw χ z f → ∀ (g₁ : G D p) (b : Mx D p p),
  mat g₁ = blk4 1 b 0 1 → ∀ (z₀ : hermA D ρ) (x₀ : Mx D ρ p) (x : G D n),
    Wz M m ψ b₀ f (M.nzx z₀ x₀ * M.emb g₁ * x) = chz ψ b₀ z₀ * Wz M m ψ b₀ f x := by
  first | exact @GlobalTheory.CompanionTheory.WzHeis.wz_heis | exact GlobalTheory.CompanionTheory.WzHeis.wz_heis | (intros; apply GlobalTheory.CompanionTheory.WzHeis.wz_heis <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarMeasureCosetNeZero
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarMeasureCosetNeZero
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibKer

theorem volume_cosetSet_ne_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (t : ℕ) [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k)) [μ.IsAddHaarMeasure] (c : k), c ≠ 0 → (((μ (cosetSet t c 0)).toReal : ℝ) : ℂ) ≠ 0 := by
  intro k _ _ _ _ t _ _ μ _ c hc
  have h0 : (0 : Fin t → k) ∈ cosetSet t c 0 := by
    show Multiplicative.ofAdd ((0 : Fin t → k) - 0) ∈ Lc t c
    rw [sub_zero, ofAdd_zero]
    exact one_mem _
  have hpos : 0 < μ (cosetSet t c 0) := (isClopen_cosetSet t c 0).isOpen.measure_pos μ ⟨0, h0⟩
  have hfin : μ (cosetSet t c 0) < ⊤ := (isCompact_cosetSet t hc 0).measure_lt_top
  rw [Complex.ofReal_ne_zero]
  exact (ENNReal.toReal_pos hpos.ne' hfin.ne).ne'

end GlobalTheory.CompanionTheory.BZPsiPG.FibKer
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarMeasureCosetNeZeroStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_measure_coset_ne_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (t : ℕ) [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k)) [μ.IsAddHaarMeasure] (c : k), c ≠ 0 → (((μ (cosetSet t c 0)).toReal : ℝ) : ℂ) ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.FibKer.volume_cosetSet_ne_zero | exact GlobalTheory.CompanionTheory.BZPsiPG.FibKer.volume_cosetSet_ne_zero | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.FibKer.volume_cosetSet_ne_zero <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedVanishingOnCompact
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedVanishingOnCompact
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibKer

theorem exists_hpg_mid_levi (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (i t : ℕ) (p : Mir k (i + t)) :
    ∃ h ∈ HPG k i t, ∃ κ ∈ GlobalTheory.SplitWeil.KO k (Fin (i + t)), ∃ v : Fin t → k,
      p = h * (uM k (i + t) (midV k i t v) * levi k (i + t) κ) := by
  obtain ⟨y, hy⟩ := GlobalTheory.CompanionTheory.BZPsiPG.exists_uM_of_mem k (i + t)
    (GlobalTheory.CompanionTheory.BZMirAdj.mem_of_mirProj_eq_one k (i + t)
      (p * (GlobalTheory.BZMir.levi k (i + t) (GlobalTheory.BZMir.mirabolicProjection k (i + t) p))⁻¹)
      (by rw [map_mul, map_inv, GlobalTheory.CompanionTheory.BZMirAdj.mirProj_levi, mul_inv_cancel]))
  have hp : p = GlobalTheory.CompanionTheory.BZPsiPG.uM k (i + t) y *
      GlobalTheory.BZMir.levi k (i + t) (GlobalTheory.BZMir.mirabolicProjection k (i + t) p) := by
    rw [← hy, inv_mul_cancel_right]
  obtain ⟨q, κ, hκ, hgq⟩ := GlobalTheory.T.iwasawa_decomp_parabolic_maximal_compact k i t (GlobalTheory.BZMir.mirabolicProjection k (i + t) p)
  obtain ⟨x, v, hxv⟩ := GlobalTheory.CompanionTheory.BZPsiPG.exists_top_mid k i t
    ((((q : GL (Fin (i + t)) k)⁻¹ : GL (Fin (i + t)) k) : Matrix (Fin (i + t)) (Fin (i + t)) k) *ᵥ y)
  obtain ⟨hq, -⟩ := GlobalTheory.T.levi_block_mem_parabolic k i t q
  obtain ⟨hx, -⟩ := GlobalTheory.T.unipotent_top_mem_parabolic k i t x
  refine ⟨GlobalTheory.BZMir.levi k (i + t) q * GlobalTheory.CompanionTheory.BZPsiPG.uM k (i + t) (GlobalTheory.CompanionTheory.BZPsiPG.topV k i t x),
    mul_mem hq hx, κ, hκ, v, ?_⟩
  have key : GlobalTheory.CompanionTheory.BZPsiPG.uM k (i + t) y * GlobalTheory.BZMir.levi k (i + t) q =
      GlobalTheory.BZMir.levi k (i + t) q * GlobalTheory.CompanionTheory.BZPsiPG.uM k (i + t)
        ((((q : GL (Fin (i + t)) k)⁻¹ : GL (Fin (i + t)) k) : Matrix (Fin (i + t)) (Fin (i + t)) k) *ᵥ y) := by
    rw [GlobalTheory.CompanionTheory.BZPsiPG.levi_mul_uM, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Matrix.one_mulVec]
  rw [hp, hgq, map_mul, ← mul_assoc (GlobalTheory.CompanionTheory.BZPsiPG.uM k (i + t) y), key, hxv,
    GlobalTheory.CompanionTheory.BZPsiPG.uM_add]
  simp only [mul_assoc]

theorem eq_zero_of_fibV_eq_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W)
    (a : cIndSpace (HPG k i t) (hRep τ σ)),
    (∀ κ ∈ GlobalTheory.SplitWeil.KO k (Fin (i + t)), fibV a κ = 0) → a = 0 := by
  intro k _ _ _ _ i t V W _ _ _ _ τ σ a ha
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext p
  obtain ⟨h, hh, κ, hκ, v, rfl⟩ := GlobalTheory.CompanionTheory.BZPsiPG.FibKer.exists_hpg_mid_levi k i t p
  have hfe : a.1.1.1 (h * (GlobalTheory.CompanionTheory.BZPsiPG.uM k (i + t) (GlobalTheory.CompanionTheory.BZPsiPG.midV k i t v) *
      GlobalTheory.BZMir.levi k (i + t) κ)) =
      GlobalTheory.CompanionTheory.BZPsiPG.hRep τ σ ⟨h, hh⟩ (a.1.1.1 (GlobalTheory.CompanionTheory.BZPsiPG.uM k (i + t)
        (GlobalTheory.CompanionTheory.BZPsiPG.midV k i t v) * GlobalTheory.BZMir.levi k (i + t) κ)) :=
    a.1.1.2 ⟨h, hh⟩ _
  have hz : a.1.1.1 (GlobalTheory.CompanionTheory.BZPsiPG.uM k (i + t) (GlobalTheory.CompanionTheory.BZPsiPG.midV k i t v) *
      GlobalTheory.BZMir.levi k (i + t) κ) = 0 := congrFun (ha κ hκ) v
  show a.1.1.1 _ = (0 : V ⊗[ℂ] W)
  rw [hfe, hz, map_zero]

end GlobalTheory.CompanionTheory.BZPsiPG.FibKer
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedVanishingOnCompactStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.induced_vanishing_on_compact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W) (a : cIndSpace (HPG k i t) (hRep τ σ)), (∀ κ ∈ GlobalTheory.SplitWeil.KO k (Fin (i + t)), fibV a κ = 0) → a = 0 := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.FibKer.eq_zero_of_fibV_eq_zero | exact GlobalTheory.CompanionTheory.BZPsiPG.FibKer.eq_zero_of_fibV_eq_zero | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.FibKer.eq_zero_of_fibV_eq_zero <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothTopRepresentation
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothTopRepresentation
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibKer.SmTop

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

def stabSub (ρ : Representation ℂ G V) (v : V) : Subgroup G where
  carrier := {g | ρ g v = v}
  mul_mem' := by
    intro a b ha hb
    show ρ (a * b) v = v
    rw [map_mul, Module.End.mul_apply]
    rw [show ρ b v = v from hb]
    exact ha
  one_mem' := by
    show ρ 1 v = v
    rw [map_one]
    rfl
  inv_mem' := by
    intro a ha
    show ρ a⁻¹ v = v
    have ha' : ρ a v = v := ha
    calc ρ a⁻¹ v = ρ a⁻¹ (ρ a v) := by rw [ha']
      _ = v := by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl

theorem stabSub_add_le (ρ : Representation ℂ G V) (x y : V) :
    stabSub ρ x ⊓ stabSub ρ y ≤ stabSub ρ (x + y) := by
  intro g hg
  show ρ g (x + y) = x + y
  have h1 : ρ g x = x := hg.1
  have h2 : ρ g y = y := hg.2
  rw [map_add (f := _), h1, h2]

end GlobalTheory.CompanionTheory.BZPsiPG.FibKer.SmTop

open GlobalTheory.CompanionTheory.BZPsiPG.FibKer.SmTop in
theorem GlobalTheory.CompanionTheory.BZPsiPG.FibKer.isSmooth_topRep : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V), IsSmooth τ → IsSmooth (topRep τ W) := by
  intro k _ _ _ _ i V W _ _ _ _ τ hτ v
  have hU : Continuous (uMh k i) := (GlobalTheory.T.continuous_levi_unipotent_proj k i).2.1.comp continuous_toAdd
  suffices h : IsOpen (stabSub (topRep τ W) v : Set (Multiplicative (Fin i → k))) from h
  induction v using TensorProduct.induction_on with
  | zero =>
    have : (stabSub (topRep τ W) 0 : Set (Multiplicative (Fin i → k))) = Set.univ := by
      ext g
      simp only [Set.mem_univ, iff_true]
      show topRep τ W g 0 = 0
      exact map_zero _
    rw [this]
    exact isOpen_univ
  | tmul a b =>
    have hle : (stabSub τ a).comap (uMh k i) ≤ stabSub (topRep τ W) (a ⊗ₜ[ℂ] b) := by
      intro g hg
      have hg' : τ (uM k i g.toAdd) a = a := hg
      show LinearMap.rTensor W (τ (uM k i g.toAdd)) (a ⊗ₜ[ℂ] b) = a ⊗ₜ[ℂ] b
      rw [LinearMap.rTensor_tmul, hg']
    refine Subgroup.isOpen_mono hle ?_
    exact (hτ a).preimage hU
  | add x y hx hy =>
    exact Subgroup.isOpen_mono (stabSub_add_le _ x y) (by rw [Subgroup.coe_inf]; exact hx.inter hy)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothTopRepresentationStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_top_representation : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V), IsSmooth τ → IsSmooth (topRep τ W) := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.FibKer.isSmooth_topRep | exact GlobalTheory.CompanionTheory.BZPsiPG.FibKer.isSmooth_topRep | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.FibKer.isSmooth_topRep <;> assumption)
end
end
