module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchrodingerThetaEqSchwartzBruhat

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeylElementActsOnSchrodingerByFourier
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelSectionWeylElementEqSchrodingerIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelSectionWeylElementEqSchrodingerIntegral
open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW

namespace GlobalTheory.Core.Rk.WeylValue

variable {D : D7}

theorem integral_periodise {m n : ℕ} {ν : Measure (Mx D m n)} {𝓨 : Set (Mx D m n)}
    (hν : IsCovolOne (ratMx D m n) ν 𝓨) (φ F : Mx D m n → ℂ) (hφ : Integrable φ ν)
    (hF : ∀ x, HasSum (fun ξ : Matrix (Fin m) (Fin n) D.host.E => φ (x + rat ξ)) (F x)) :
    ∫ x in 𝓨, F x ∂ν = ∫ x, φ x ∂ν := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := lattice_Mx D m n
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  haveI : Countable (ratMx D m n) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI := hν.1
  let e : Matrix (Fin m) (Fin n) D.host.E ≃ ratMx D m n :=
    Equiv.ofBijective (fun ξ => ⟨rat ξ, rat_mem ξ⟩)
      ⟨fun a b h => rat_injective (congrArg Subtype.val h), fun g => by
        obtain ⟨ξ, hξ⟩ := mem_ratMx.1 g.2
        exact ⟨ξ, Subtype.ext hξ⟩⟩
  have h1 : ∀ x, F x = ∑' g : ratMx D m n, φ (g +ᵥ x) := fun x => by
    rw [← (hF x).tsum_eq, ← e.tsum_eq]
    refine tsum_congr fun ξ => ?_
    show φ (x + rat ξ) = φ (rat ξ + x)
    rw [add_comm]
  simp only [h1]
  rw [hν.2.1.integral_eq_tsum'' φ hφ]
  refine integral_tsum (fun g => ?_) ?_
  · exact ((hφ.comp_add_left (g : Mx D m n)).aestronglyMeasurable).restrict
  · rw [← hν.2.1.lintegral_eq_tsum'' fun x => ‖φ x‖ₑ]
    exact hφ.2.ne

theorem pY_weyl (A : HSp D) {w : GA D (dblSp A)} (hw : IsWeyl A w) :
    ((dblDec A).pY ⬝ mt (dblSp A) w : Mx D A.rank (dblSp A).rank) = lowC A w ⬝ (dblDec A).pX := by
  have h0 : ((dblDec A).j0 ⬝ (dblDec A).p0 : Mx D (dblSp A).rank (dblSp A).rank) = 0 := by
    ext i j
    rw [Matrix.mul_apply]
    exact Finset.sum_eq_zero fun k _ => Fin.elim0 k
  have h1 := (dblDec A).sum_eq_one
  rw [h0, add_zero] at h1
  have h2 := hw.2
  rw [← Matrix.mul_assoc] at h2
  rw [← Matrix.mul_one ((dblDec A).pY ⬝ mt (dblSp A) w), ← h1, Matrix.mul_add, ← Matrix.mul_assoc _ (dblDec A).jY, h2,
    Matrix.zero_mul, add_zero, lowC]
  simp only [Matrix.mul_assoc]

theorem swSec_weyl : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle) (omh : WRep (dblSp A) B), IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ f, IsThetaFunO ψ (dblSp A) B f → ∀ w, IsWeyl A w → swSec A B omh ν 𝓨 f w = ∫ x, sch ψ A B ν 𝓨 f x ∂ν := by
  intro D ψ A B χB omh hω ν 𝓨 hν f hf w hw
  have hp := pY_weyl A hw
  have hm : lowC A w ∈ ratMx D A.rank A.rank :=
    ratMx_mul (rat_mem _) (ratMx_mul ((mem_GQ_iff _ _).1 hw.1) (rat_mem _))
  let n : Mx D A.rank A.rank := (dblDec A).pX ⬝ (mt (dblSp A) w⁻¹ ⬝ (dblDec A).jY)
  have hn : n ∈ ratMx D A.rank A.rank :=
    ratMx_mul (rat_mem _) (ratMx_mul ((mem_GQ_iff _ _).1 (inv_mem hw.1)) (rat_mem _))
  have hmn : lowC A w * n = 1 := by
    show lowC A w ⬝ ((dblDec A).pX ⬝ (mt (dblSp A) w⁻¹ ⬝ (dblDec A).jY)) = 1
    rw [← Matrix.mul_assoc, ← hp, Matrix.mul_assoc, ← Matrix.mul_assoc (mt (dblSp A) w), mt_mul_inv, Matrix.one_mul,
      HypDec.pY_jY]
  have h1 : ∀ z : WO A B, omh (w, 1) f (GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.lagr A B z) = f ((dblDec A).extX B (z ⬝ lowC A w)) := fun z => by
    rw [GlobalTheory.RatSubst.om_rat_left_apply D ψ _ _ _ _ omh hω f hf w hw.1, actO_eq, inv_inv, mt_one, Matrix.one_mul,
      ← extY_dblDec, HypDec.extY_apply, HypDec.extX_apply, Matrix.mul_assoc, hp, Matrix.mul_assoc]
  have hper : ∀ γ ∈ ratMx D B.rank A.rank, ∀ a, f ((dblDec A).extX B (γ + a)) = f ((dblDec A).extX B a) := by
    intro γ hγ a
    obtain ⟨δ, hδ⟩ : (dblDec A).extX B γ ∈ ratMx D _ _ := ratMx_mul hγ (rat_mem _)
    have h := hf.quasi δ ((dblDec A).extX B a)
    rw [show ratW B (dblSp A) δ = (dblDec A).extX B γ from hδ, HypDec.symplOH_extX_extX, neg_zero,
      AddChar.map_zero_eq_one, one_mul] at h
    rw [map_add (f := _), h]
  unfold swSec GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.evZero
  simp only [h1]
  have hchange : ∫ a in 𝓨, f ((dblDec A).extX B (a * lowC A w)) ∂ν =
      ∫ a in 𝓨, f ((dblDec A).extX B a) ∂ν := by
    obtain ⟨i1, i2, i3, i4, i5, -⟩ := lattice_Mx D B.rank A.rank
    let e : Mx D B.rank A.rank ≃+ Mx D B.rank A.rank :=
      { toFun := fun a => a * lowC A w
        invFun := fun a => a * n
        left_inv := fun a => by simp only [Matrix.mul_assoc, hmn, Matrix.mul_one]
        right_inv := fun a => by simp only [Matrix.mul_assoc, mul_eq_one_comm.1 hmn, Matrix.mul_one]
        map_add' := fun a b => Matrix.add_mul _ _ _ }
    have he : Continuous e := continuous_id.matrix_mul continuous_const
    have he' : Continuous e.symm := continuous_id.matrix_mul continuous_const
    have hr : ∀ x, e x ∈ ratMx D B.rank A.rank ↔ x ∈ ratMx D B.rank A.rank := fun x =>
      ⟨fun h => by
        have h2 := ratMx_mul h hn
        have h3 : e x * n = x := e.symm_apply_apply x
        rwa [h3] at h2,
       fun h => ratMx_mul h hm⟩
    obtain ⟨h1, hemb⟩ := GlobalTheory.Unf.ParCont.isCovolOne_map hν e he he' hr
    rw [← covolOne_integral_eq hν h1 (fun a => f ((dblDec A).extX B a)) hper,
      hemb.setIntegral_map, Set.preimage_image_eq _ e.injective]
    rfl
  refine hchange.trans ?_
  exact integral_periodise hν _ _ (GlobalTheory.T.doubledPairSchrodingerFunction_continuous_integrable D ψ hω.std A B ν 𝓨 hν f hf).2
    fun x => (GlobalTheory.T.doubledTheta_eq_sum_schrodingerFunction_periodisation D ψ hω.std A B ν 𝓨 hν f hf x).2

end GlobalTheory.Core.Rk.WeylValue
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelSectionWeylElementEqSchrodingerIntegralStatement
open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelSection_weylElement_eq_schrodingerIntegral : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle) (omh : WRep (dblSp A) B), IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ f, IsThetaFunO ψ (dblSp A) B f → ∀ w, IsWeyl A w → swSec A B omh ν 𝓨 f w = ∫ x, sch ψ A B ν 𝓨 f x ∂ν := by
  first | exact @GlobalTheory.Core.Rk.WeylValue.swSec_weyl | exact GlobalTheory.Core.Rk.WeylValue.swSec_weyl | (intros; apply GlobalTheory.Core.Rk.WeylValue.swSec_weyl <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeylElementActsOnSchrodingerByFourier
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StdUnn.WeylFourier

variable {D : D7}

theorem extX_mul_weyl {A B : HSp D} {w : GA D (dblSp A)} {b c : AE D}
    (hX : mt (dblSp A) w ⬝ (dblDec A).jX = -(b • (dblDec A).jY))
    (hY : mt (dblSp A) w ⬝ (dblDec A).jY = c • (dblDec A).jX) (x : Mx D B.rank A.rank) :
    (dblDec A).extX B x ⬝ mt (dblSp A) w = (dblDec A).extY B (c • x) := by
  refine (dblDec A).mat_ext ?_ (Matrix.ext fun _ j => Fin.elim0 j) ?_
  · simp only [HypDec.extX_apply, HypDec.extY_apply, Matrix.mul_assoc, hX, Matrix.mul_neg, Matrix.mul_smul]
    rw [(dblDec A).pX_jY, (dblDec A).pY_jX, Matrix.mul_zero, Matrix.mul_zero, smul_zero, neg_zero]
  · simp only [HypDec.extX_apply, HypDec.extY_apply, Matrix.mul_assoc, hY, Matrix.mul_smul]
    rw [(dblDec A).pX_jX, (dblDec A).pY_jY, Matrix.mul_one, Matrix.mul_one]

theorem symplO_extX_extY_smul {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (c : AE D) (x y : Mx D T.rank ρ) :
    symplO S T (d.extX T y) (d.extY T (c • x)) =
      trA (incA D D.host.xi0 * cA D c * Matrix.trace (GlobalTheory.StdUnn.inner T x y)) := by
  have h := d.hO_ext T y 0 0 (c • x) 0 0
  simp only [map_zero, zero_add, add_zero, hO_eq_trace S₀, Matrix.mul_zero, Matrix.trace_zero] at h
  rw [symplO_eq, h, show pairS T (0 : Mx D T.rank ρ) 0 = 0 by simp [pairS], add_zero, pairS, adj_smul,
    Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, ← mul_assoc]
  rfl

theorem sch_weyl : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle) (omh : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)), IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ μ : D.host.E, IsSkew μ → ∀ w : GA D (dblSp A), IsWeyl A w → mt (dblSp A) w ⬝ (dblDec A).jX = -(incA D μ • (dblDec A).jY) → mt (dblSp A) w ⬝ (dblDec A).jY = incA D μ⁻¹ • (dblDec A).jX → ∀ f, IsThetaFunO ψ (dblSp A) B f → ∀ x, sch ψ A B ν 𝓨 (omh (w, 1) f) x = ∫ y, sch ψ A B ν 𝓨 f y * ψ (trA (incA D (-D.host.xi0 / μ) * Matrix.trace (GlobalTheory.StdUnn.inner B x y))) ∂ν := by
  intro D ψ A B χB omh hW ν 𝓨 hν μ hμ w hw hX hY f hf x
  set u : WO (dblSp A) B := (dblDec A).extY B (incA D μ⁻¹ • x) with hu
  have hact : actO (dblSp A) B w 1 u = (dblDec A).extX B x := by
    rw [actO_eq, mt_one, Matrix.one_mul, hu, ← extX_mul_weyl hX hY x, Matrix.mul_assoc, mt_mul_inv, Matrix.mul_one]
  have hf₁ : IsThetaFunO ψ (dblSp A) B (heisO ψ (dblSp A) B u f) :=
    (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hW.std (dblSp A) B).1 u f hf
  have h1 : sch ψ A B ν 𝓨 (omh (w, 1) f) x = swSec A B omh ν 𝓨 (heisO ψ (dblSp A) B u f) w := by
    have h := congrFun (GlobalTheory.MixModel.Check.mixS_heis_extX (ψ := ψ) (dblDec A) ν 𝓨 (omh (w, 1) f) x 0) 0
    rw [zero_add, ← hact, ← hW.om_heis w 1 u f hf, mixS_dblDec_zero] at h
    exact h.symm
  rw [h1, GlobalTheory.T.siegelSection_weylElement_eq_schrodingerIntegral D ψ A B χB omh hW ν 𝓨 hν _ hf₁ w hw]
  refine congrArg _ (funext fun y => ?_)
  have hc : incA D D.host.xi0 * cA D (incA D μ⁻¹) = incA D (-D.host.xi0 / μ) := by
    rw [GlobalTheory.DualPairCheck.cA_incA, ← map_mul, star_inv₀, hμ.2, inv_neg, mul_neg, neg_div, div_eq_mul_inv]
  have h2 := GlobalTheory.MixModel.Check.mixS_heis_extY (dblDec A) hν hf (incA D μ⁻¹ • x) y 0
  rw [symplO_extX_extY_smul, hc, mul_comm] at h2
  exact h2

end GlobalTheory.StdUnn.WeylFourier

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeylElementActsOnSchrodingerByFourierStatement
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weylElement_acts_on_schrodinger_by_fourier : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle) (omh : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)), IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ μ : D.host.E, IsSkew μ → ∀ w : GA D (dblSp A), IsWeyl A w → mt (dblSp A) w ⬝ (dblDec A).jX = -(incA D μ • (dblDec A).jY) → mt (dblSp A) w ⬝ (dblDec A).jY = incA D μ⁻¹ • (dblDec A).jX → ∀ f, IsThetaFunO ψ (dblSp A) B f → ∀ x, sch ψ A B ν 𝓨 (omh (w, 1) f) x = ∫ y, sch ψ A B ν 𝓨 f y * ψ (trA (incA D (-D.host.xi0 / μ) * Matrix.trace (GlobalTheory.StdUnn.inner B x y))) ∂ν := by
  first | exact @GlobalTheory.StdUnn.WeylFourier.sch_weyl | exact GlobalTheory.StdUnn.WeylFourier.sch_weyl | (intros; apply GlobalTheory.StdUnn.WeylFourier.sch_weyl <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardUnitaryChartWeylElementRational
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardUnitaryChartWeylElementRational
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn

theorem weyl_cols {R : Type} [CommRing R] {n : ℕ} (X Y : Matrix (Fin (n + n)) (Fin n) R)
    (T M : Matrix (Fin (n + n)) (Fin (n + n)) R) (hT : T.submatrix id finSumFinEquiv = Matrix.fromCols X Y)
    (h : T * blk4 0 1 (-1) 0 = M * T) : M * X = -Y ∧ M * Y = X := by
  have hJ : (blk4 0 1 (-1) 0 : Matrix (Fin (n + n)) (Fin (n + n)) R).submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks 0 1 (-1) 0 := by
    simp [blk4]
  have h2 := congrArg (fun N : Matrix (Fin (n + n)) (Fin (n + n)) R => N.submatrix id finSumFinEquiv) h
  beta_reduce at h2
  rw [Matrix.submatrix_mul _ _ id finSumFinEquiv finSumFinEquiv finSumFinEquiv.bijective, hJ,
    Matrix.submatrix_mul _ _ id id finSumFinEquiv Function.bijective_id, Matrix.submatrix_id_id, hT,
    Matrix.fromCols_mul_fromBlocks, Matrix.mul_fromCols] at h2
  obtain ⟨hX, hY⟩ := Matrix.fromCols_inj h2
  simp only [Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg, zero_add, add_zero] at hX hY
  exact ⟨hX.symm, hY.symm⟩

theorem weyl_unscale {R : Type} [CommRing R] {k l m : ℕ} (M : Matrix (Fin k) (Fin l) R) (Y : Matrix (Fin l) (Fin m) R)
    (X : Matrix (Fin k) (Fin m) R) {a b : R} (hab : b * a = 1) (h : M * (a • Y) = X) : M * Y = b • X := by
  rw [← h, Matrix.mul_smul, smul_smul, hab, one_smul]

theorem weyl_kill {R : Type} [CommRing R] {k l m : ℕ} (P : Matrix (Fin k) (Fin l) R) (X Z : Matrix (Fin l) (Fin m) R)
    {b : R} (h : P * X = 0) (hZ : Z = b • X) : P * Z = 0 := by
  rw [hZ, Matrix.mul_smul, h, smul_zero]

theorem mem_GQ_of_hypDec {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (g : GA D S)
    (hX : mt S g ⬝ d.jX ∈ GlobalTheory.MixModel.ratMx D S.rank ρ) (h0 : mt S g ⬝ d.j0 ∈ GlobalTheory.MixModel.ratMx D S.rank S₀.rank)
    (hY : mt S g ⬝ d.jY ∈ GlobalTheory.MixModel.ratMx D S.rank ρ) : g ∈ GQ S := by
  rw [mem_GQ_iff, ← Matrix.mul_one (mt S g), ← d.sum_eq_one, Matrix.mul_add, Matrix.mul_add, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc]
  exact add_mem (add_mem (ratMx_mul hX (rat_mem _)) (ratMx_mul h0 (rat_mem _))) (ratMx_mul hY (rat_mem _))

theorem rat_Tm_cols {D : D7} (A : HSp D) (μ : D.host.E) :
    (rat (Tm A μ) : Mx D (A.rank + A.rank) (A.rank + A.rank)).submatrix id finSumFinEquiv =
      Matrix.fromCols (dblDec A).jX (incA D μ • (dblDec A).jY) := by
  funext i j
  rcases j with j | j
  · exact congrArg (fun s => incA D (Matrix.fromCols (dblDec A).e (μ • (dblDec A).e') i s))
      (finSumFinEquiv.symm_apply_apply (Sum.inl j))
  · exact (congrArg (fun s => incA D (Matrix.fromCols (dblDec A).e (μ • (dblDec A).e') i s))
      (finSumFinEquiv.symm_apply_apply (Sum.inr j))).trans (map_mul (incA D) μ _)

theorem chart_weyl : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ → ∀ g : GA D (dblSp A), mat (κ g) = blk4 0 1 (-1) 0 → IsWeyl A g ∧ mt (dblSp A) g ⬝ (dblDec A).jX = -(incA D μ • (dblDec A).jY) ∧ mt (dblSp A) g ⬝ (dblDec A).jY = incA D μ⁻¹ • (dblDec A).jX := by
  intro D A μ hμ κ hκ g hg
  have h := hκ g
  rw [hg] at h
  obtain ⟨e1, hY⟩ := weyl_cols _ _ _ _ (rat_Tm_cols A μ) h
  have hμ0 : incA D μ⁻¹ * incA D μ = 1 := by rw [← map_mul, inv_mul_cancel₀ hμ.1, map_one]
  have e2 := weyl_unscale _ _ _ hμ0 hY
  refine ⟨⟨mem_GQ_of_hypDec (dblDec A) g ?_ ?_ ?_, weyl_kill _ _ _ (dblDec A).pY_jX e2⟩, e1, e2⟩
  · exact Set.mem_of_eq_of_mem e1 (neg_mem (ratMx_smul μ (rat_mem (dblDec A).e')))
  · exact ⟨0, Matrix.ext fun _ j => Fin.elim0 j⟩
  · exact Set.mem_of_eq_of_mem e2 (ratMx_smul μ⁻¹ (rat_mem (dblDec A).e))

end GlobalTheory.StdUnn
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardUnitaryChartWeylElementRationalStatement
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardUnitaryChart_weylElement_rational : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ → ∀ g : GA D (dblSp A), mat (κ g) = blk4 0 1 (-1) 0 → IsWeyl A g ∧ mt (dblSp A) g ⬝ (dblDec A).jX = -(incA D μ • (dblDec A).jY) ∧ mt (dblSp A) g ⬝ (dblDec A).jY = incA D μ⁻¹ • (dblDec A).jX := by
  first | exact @GlobalTheory.StdUnn.chart_weyl | exact GlobalTheory.StdUnn.chart_weyl | (intros; apply GlobalTheory.StdUnn.chart_weyl <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeylFormulaStandardUnitaryGroupWeilDatum
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn.WeylStd

theorem trA_incA_mul (D : D7) (lam : D.host.F) (t : AE D) :
    trA (incA D (algebraMap D.host.F D.host.E lam) * t) = algebraMap D.host.F (AF D.host.F) lam * trA t := by
  have h : incA D (algebraMap D.host.F D.host.E lam) = algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) lam) := by
    show Algebra.TensorProduct.includeRight (algebraMap D.host.F D.host.E lam) = _
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply D.host.F (AF D.host.F) (AE D)]
  rw [h, ← Algebra.smul_def]
  show Algebra.trace (AF D.host.F) (AE D) (_ • t) = _
  rw [LinearMap.map_smul, smul_eq_mul]

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle) (omh : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)), IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ θ : InfFam D, IsInfFam θ → ∀ μ : D.host.E, IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ → ∀ omS : G D A.rank →* Module.End ℂ (schwartzA θ B.rank A.rank), IsTransport ψ θ A B ν 𝓨 omh κ omS → ∀ lam : D.host.F, algebraMap D.host.F D.host.E lam = -D.host.xi0 / μ → ∀ g : G D A.rank, mat g = blk4 0 1 (-1) 0 → ∀ Φ x, (omS g Φ).1 x = ∫ y, Φ.1 y * shift ψ lam (trA (Matrix.trace (GlobalTheory.StdUnn.inner B x y))) ∂ν := by
  intro D ψ A B χB omh hW ν 𝓨 hν θ hθ μ hμ κ hκ omS hT lam hlam g hg Φ x
  obtain ⟨f, hf, hΦ⟩ := (GlobalTheory.T.schrodingerTheta_eq_schwartzBruhat D ψ hW.std θ hθ A B ν 𝓨 hν).2.1 Φ.1 Φ.2
  have hw : mat (κ (κ.symm g)) = blk4 0 1 (-1) 0 := by rw [MulEquiv.apply_symm_apply]; exact hg
  obtain ⟨hW1, h1, h2⟩ := GlobalTheory.T.standardUnitaryChart_weylElement_rational D A μ hμ κ hκ (κ.symm g) hw
  have hg' := hT (κ.symm g) f hf Φ hΦ.symm
  rw [MulEquiv.apply_symm_apply] at hg'
  rw [hg', GlobalTheory.T.weylElement_acts_on_schrodinger_by_fourier D ψ A B χB omh hW ν 𝓨 hν μ hμ (κ.symm g) hW1 h1 h2 f hf x, ← hΦ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [shift, AddChar.mulShift_apply]
  rw [← hlam, trA_incA_mul]

end GlobalTheory.StdUnn.WeylStd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeylFormulaStandardUnitaryGroupWeilDatumStatement
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weyl_formula_standardUnitaryGroup_weilDatum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle) (omh : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)), IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ θ : InfFam D, IsInfFam θ → ∀ μ : D.host.E, IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ → ∀ omS : G D A.rank →* Module.End ℂ (schwartzA θ B.rank A.rank), IsTransport ψ θ A B ν 𝓨 omh κ omS → ∀ lam : D.host.F, algebraMap D.host.F D.host.E lam = -D.host.xi0 / μ → ∀ g : G D A.rank, mat g = blk4 0 1 (-1) 0 → ∀ Φ x, (omS g Φ).1 x = ∫ y, Φ.1 y * shift ψ lam (trA (Matrix.trace (GlobalTheory.StdUnn.inner B x y))) ∂ν := by
  first | exact @GlobalTheory.StdUnn.WeylStd.main | exact GlobalTheory.StdUnn.WeylStd.main | (intros; apply GlobalTheory.StdUnn.WeylStd.main <;> assumption)
end
