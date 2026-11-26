module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PolarMapContDiffAtBase
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ExpTop

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ContinuousThetaInf
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Metric NumberField Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal Formalism.MainNotions.S Formalism.L2.SG.AdBridge
open scoped TensorProduct Matrix

theorem contDiff_conj_exp {ι : Type} [Fintype ι] {n : ℕ}
    (L : EuclideanSpace ℝ ι →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ) (A B : Matrix (Fin n) (Fin n) ℂ) (y : Fin n → ℂ) :
    ContDiff ℝ 1 (fun x => (A * NormedSpace.exp (L x) * B) *ᵥ y) := by
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℝ _
  let Lc : EuclideanSpace ℝ ι →L[ℝ] Matrix (Fin n) (Fin n) ℂ := LinearMap.toContinuousLinearMap L
  let H : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] (Fin n → ℂ) :=
    { toFun := fun M => (A * M * B) *ᵥ y
      map_add' := fun M M' => by simp [Matrix.mul_add, Matrix.add_mul, Matrix.add_mulVec]
      map_smul' := fun c M => by
        simp only [RingHom.id_apply]
        rw [Matrix.mul_smul, Matrix.smul_mul]
        funext i
        simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, Pi.smul_apply, Finset.smul_sum, smul_mul_assoc] }
  let Hc : Matrix (Fin n) (Fin n) ℂ →L[ℝ] (Fin n → ℂ) := LinearMap.toContinuousLinearMap H
  have he : ContDiff ℝ 1 (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) :=
    contDiff_iff_contDiffAt.2 fun M => (NormedSpace.exp_analytic (𝕂 := ℝ) M).contDiffAt
  exact Hc.contDiff.comp (he.comp Lc.contDiff)

theorem theta_act {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (hb : AdBridgeIso X.B.I) (s : X.B.I.Ginf)
    (v : InfinitePlace X.B.I.F) (b : Fin (D.R.rS + 1 + D.R.rS)) (i : Fin X.B.I.n) :
    PI.AprimeInfU.thetaInf X v ((X.toInf hb s • Y0 X u') b i) =
      ((X.B.I.P v * uMat (s v) * (X.B.I.P v)⁻¹) *ᵥ fun j => X.B.I.φ v (tupH (frameOf X u') b j)) i := by
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  have hPu : IsUnit (X.B.I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (X.B.I.P_unit v)
  set Mm : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) :=
    ((HA.mat (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (X.toInf hb s) : GL (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) :
      Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) with hMm
  have hmap : Mm.map (PI.AprimeInfU.thetaInf X v) = X.B.I.P v * uMat (s v) * (X.B.I.P v)⁻¹ := by
    rw [uMat_toInf X hb s v, ← hMm]
    simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hPu, Matrix.one_mul]
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hPu, Matrix.mul_one]
  rw [← hmap]
  show PI.AprimeInfU.thetaInf X v ((Mm *ᵥ Y0 X u' b) i) = _
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show Y0 X u' b j = inclR (Ainf X.B.I.F) (tupH (frameOf X u') b j) from rfl, thetaInf_inclR]

theorem continuous_thetaInf {D : D7} (X : HidaSetting D) (v : InfinitePlace X.B.I.F) :
    Continuous (PI.AprimeInfU.thetaInf X v) := by
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  let σ : Ainf X.B.I.F →+* ℂ := PI.AprimeInfU.evInf X v
  have hσ : Continuous σ :=
    (InfinitePlace.Completion.isometry_extensionEmbedding v).continuous.comp (continuous_apply v)
  let φl : (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) →ₛₗ[σ] ℂ :=
    { toFun := PI.AprimeInfU.thetaInf X v
      map_add' := map_add _
      map_smul' := fun a y => by
        rw [Algebra.smul_def, map_mul, smul_eq_mul]
        congr 1
        show PI.AprimeInfU.thetaInf X v (a ⊗ₜ[X.B.I.F] (1 : X.B.I.E)) = _
        rw [thetaInf_tmul, map_one, mul_one] }
  exact IsModuleTopology.continuous_of_linearMapₛₗ hσ φl

theorem kapSm_holds : KapSm := by
  intro D X u' ψ hT μinf νinf fibInf hP hb c S ι _ L hc hL
  classical
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  haveI : IsTotallyReal X.B.I.F := X.B.I.cm.totReal
  let Φ : TupI X →+ (InfinitePlace X.B.I.F → Fin (D.R.rS + 1 + D.R.rS) → Fin X.B.I.n → ℂ) :=
    { toFun := fun Y v b i => PI.AprimeInfU.thetaInf X v (Y b i)
      map_zero' := by funext v b i; exact map_zero _
      map_add' := by intro Y Z; funext v b i; exact map_add _ _ _ }
  have hsa : ∀ z z', (tupCoord X).symm (z + z') = (tupCoord X).symm z + (tupCoord X).symm z' := by
    intro z z'; apply (tupCoord X).injective; rw [tupCoord_add]; simp
  let T0 : EuclideanSpace ℝ (KapI X) →+ TupI X :=
    { toFun := (tupCoord X).symm
      map_zero' := by
        have h := hsa 0 0
        rw [add_zero] at h
        simpa using h
      map_add' := hsa }
  let Ψ0 := Φ.comp T0
  have hc0 : Continuous Ψ0 := by
    refine continuous_pi fun v => continuous_pi fun b => continuous_pi fun i => ?_
    exact (continuous_thetaInf X v).comp ((continuous_apply i).comp ((continuous_apply b).comp
      (tupCoord X).symm.continuous))
  let Ψ := Ψ0.toRealLinearMap hc0
  have hΨ : ∀ z v b i, Ψ z v b i = PI.AprimeInfU.thetaInf X v ((tupCoord X).symm z b i) := fun _ _ _ _ => rfl
  have hinj : Function.Injective Ψ := by
    intro z z' h
    apply (tupCoord X).symm.injective
    funext b i
    have key : ∀ v, PI.AprimeInfU.thetaInf X v ((tupCoord X).symm z b i) =
        PI.AprimeInfU.thetaInf X v ((tupCoord X).symm z' b i) := by
      intro v
      rw [← hΨ, ← hΨ, h]
    exact sub_eq_zero.1 (thetaInf_inj X _ fun v => by rw [map_sub, key v, sub_self])
  have hcbi : Fintype.card (Module.Free.ChooseBasisIndex (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) = 2 := by
    rw [← Module.finrank_eq_card_chooseBasisIndex,
      Module.finrank_eq_card_basis (Algebra.TensorProduct.basis (Ainf X.B.I.F)
        (Module.finBasisOfFinrankEq X.B.I.F X.B.I.E X.B.I.cm.deg2)), Fintype.card_fin]
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (KapI X)) =
      Module.finrank ℝ (InfinitePlace X.B.I.F → Fin (D.R.rS + 1 + D.R.rS) → Fin X.B.I.n → ℂ) := by
    simp only [finrank_euclideanSpace, Fintype.card_prod, hcbi, Module.finrank_pi_fintype,
      Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ, smul_eq_mul, Fintype.card_fin]
    ring
  let Ψe := LinearMap.linearEquivOfInjective (Ψ : EuclideanSpace ℝ (KapI X) →ₗ[ℝ] _) hinj hdim
  have hΨe : ∀ Z : TupI X, tupCoord X Z = Ψe.symm (Φ Z) := by
    intro Z
    apply Ψe.injective
    rw [LinearEquiv.apply_symm_apply, LinearMap.linearEquivOfInjective_apply]
    show Φ (T0 (tupCoord X Z)) = Φ Z
    simp [T0]
  have hG : ∀ x v b, (fun i => Φ (kap0 X hb c L x • Y0 X u') v b i) =
      ((X.B.I.P v * uMat (c v)) * NormedSpace.exp (L x v) * (uMat (c v)⁻¹ * (X.B.I.P v)⁻¹)) *ᵥ
        fun j => X.B.I.φ v (tupH (frameOf X u') b j) := by
    intro x v b
    funext i
    show PI.AprimeInfU.thetaInf X v ((X.toInf hb (c * (fun w => expU (X.B.I.ε w) (L x w)) * c⁻¹) • Y0 X u') b i) = _
    rw [theta_act]
    have hu : uMat ((c * (fun w => expU (X.B.I.ε w) (L x w)) * c⁻¹) v) =
        uMat (c v) * NormedSpace.exp (L x v) * uMat (c v)⁻¹ := by
      have e := expU_val (X.B.I.ε v) (L x v) (hL.1 x v).1
      simp only [uMat, Pi.mul_apply, Pi.inv_apply, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul] at e ⊢
      rw [e]
    rw [hu]
    simp only [Matrix.mul_assoc]
  have hGc : ContDiff ℝ 1 (fun x => Φ (kap0 X hb c L x • Y0 X u')) := by
    refine contDiff_pi.2 fun v => contDiff_pi.2 fun b => ?_
    have e : (fun x => Φ (kap0 X hb c L x • Y0 X u') v b) = fun x =>
        ((X.B.I.P v * uMat (c v)) * NormedSpace.exp (((LinearMap.proj v : (InfinitePlace X.B.I.F →
          Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) →ₗ[ℝ] _) ∘ₗ L) x) * (uMat (c v)⁻¹ * (X.B.I.P v)⁻¹)) *ᵥ
          fun j => X.B.I.φ v (tupH (frameOf X u') b j) := by
      funext x
      exact hG x v b
    rw [e]
    exact contDiff_conj_exp _ _ _ _
  have hK : KapOrb X u' (kap0 X hb c L) = fun x => Ψe.symm (Φ (kap0 X hb c L x • Y0 X u')) := by
    funext x
    exact hΨe _
  rw [hK]
  have h1 : ContDiff ℝ 1 (fun y => Ψe.symm y) := Ψe.toContinuousLinearEquiv.symm.contDiff
  exact (h1.comp hGc).contDiffAt

end PI.AprimeInfW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.GoodChartExOfWitt
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Metric NumberField Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal Formalism.MainNotions.S
open scoped TensorProduct Matrix

def WittLin : Prop := ∀ {n m k : ℕ}, n = m + k → ∀ (ε : Fin n → Bool) (w : Fin m → Fin n → ℂ),
    LinearIndependent ℂ w →
    (∀ z : Fin n → ℂ, z ≠ 0 → (∀ b, star (w b) ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ z) = 0) →
      0 < (star z ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ z)).re) →
    ∃ (S : Finset (Fin n)) (c : Formalism.REAL.UJ ε), (S.card = k ∧ ∀ i ∈ S, ε i = true) ∧
      Submodule.span ℂ (Set.range fun b => uMat c⁻¹ *ᵥ w b) =
        Submodule.span ℂ ((fun i => (Pi.single i 1 : Fin n → ℂ)) '' (↑S)ᶜ)

def DimNK : Prop := ∀ {D : D7} (X : HidaSetting D), X.B.I.n = (D.R.rS + 1 + D.R.rS) + D.R.k

def LinIndW : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf
    fibInf, PushHyp X u' ψ hT μinf νinf fibInf → ∀ v : InfinitePlace X.B.I.F, LinearIndependent ℂ (wV X u' v)

def PerpPosV : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf
    fibInf, PushHyp X u' ψ hT μinf νinf fibInf → ∀ v : InfinitePlace X.B.I.F, ∀ z : Fin X.B.I.n → ℂ, z ≠ 0 →
      (∀ b, star (wV X u' v b) ⬝ᵥ (Formalism.REAL.Jm (X.B.I.ε v) *ᵥ z) = 0) →
      0 < (star z ⬝ᵥ (Formalism.REAL.Jm (X.B.I.ε v) *ᵥ z)).re

theorem dimNK_holds : DimNK := by
  intro D X
  rw [X.n_eq]
  have h1 := D.R.rS_two
  have h2 := D.R.r_eq
  omega

theorem gram_wV {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (v : InfinitePlace X.B.I.F) (b b' : Fin (D.R.rS + 1 + D.R.rS)) :
    star (wV X u' v b) ⬝ᵥ (Formalism.REAL.Jm (X.B.I.ε v) *ᵥ wV X u' v b') =
      X.B.I.φ v (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) b b') := by
  have hPu : IsUnit (X.B.I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (X.B.I.P_unit v)
  have hJ : ((X.B.I.P v)⁻¹)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * (X.B.I.P v)⁻¹ = X.B.I.J.map (X.B.I.φ v) := by
    rw [← X.B.I.P_spec v]
    have e1 : ((X.B.I.P v)⁻¹)ᴴ * (X.B.I.P v)ᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hPu, Matrix.conjTranspose_one]
    calc ((X.B.I.P v)⁻¹)ᴴ * ((X.B.I.P v)ᴴ * X.B.I.J.map (X.B.I.φ v) * X.B.I.P v) * (X.B.I.P v)⁻¹
        = (((X.B.I.P v)⁻¹)ᴴ * (X.B.I.P v)ᴴ) * X.B.I.J.map (X.B.I.φ v) * (X.B.I.P v * (X.B.I.P v)⁻¹) := by
          simp only [Matrix.mul_assoc]
      _ = X.B.I.J.map (X.B.I.φ v) := by
          rw [e1, Matrix.mul_nonsing_inv _ hPu, Matrix.one_mul, Matrix.mul_one]
  unfold wV
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hJ]
  have hσφ : ∀ a, X.B.I.φ v (X.B.I.cm.sig a) = star (X.B.I.φ v a) := fun a => X.B.I.cm.cmUnram.2.1 (X.B.I.φ v) a
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, gramE, hE, Formalism.UG.hform, map_sum, map_mul, Pi.star_apply,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show (X.B.I.cm.sig : X.B.I.E →+* X.B.I.E) (tupH (frameOf X u') b i) = X.B.I.cm.sig (tupH (frameOf X u') b i) from rfl,
    hσφ]
  ring

theorem linIndW_holds : LinIndW := by
  intro D X u' ψ hT μinf νinf fibInf hP v
  have hd := detNZ_holds X u' ψ hT μinf νinf fibInf hP
  set G : Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS)) ℂ :=
    (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (X.B.I.φ v) with hG
  have hGd : G.det ≠ 0 := by
    have e : G.det = X.B.I.φ v (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).det :=
      (RingHom.map_det (X.B.I.φ v) _).symm
    rw [e]
    exact (map_ne_zero _).2 hd
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hGg : G *ᵥ g = 0 := by
    funext b'
    have h0 := congrArg (fun z => star (wV X u' v b') ⬝ᵥ (Formalism.REAL.Jm (X.B.I.ε v) *ᵥ z)) hg
    simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul, smul_eq_mul,
      Matrix.mulVec_zero, dotProduct_zero] at h0
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    rw [← h0]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [gram_wV]
    simp only [hG, Matrix.map_apply]
    ring
  exact fun b => congrFun (Matrix.eq_zero_of_mulVec_eq_zero hGd hGg) b

theorem wittBlock_of (h0 : DimNK) (h1 : LinIndW) (h2 : PerpPosV) (h3 : WittLin) : WittBlock := by
  intro D X u' ψ hT μinf νinf fibInf hP v
  exact h3 (h0 X) (X.B.I.ε v) (wV X u' v) (h1 X u' ψ hT μinf νinf fibInf hP v)
    (h2 X u' ψ hT μinf νinf fibInf hP v)

theorem goodChartEx_of_witt (h1 : LinIndW) (h2 : PerpPosV) (h3 : WittLin) (hG : GrpStd) (hT : TupStd) :
    GoodChartEx :=
  goodChartEx_of_std (stdDataEx_of (stdConjEx_of_witt (wittBlock_of dimNK_holds h1 h2 h3))) hG hT

end PI.AprimeInfW
end
end
