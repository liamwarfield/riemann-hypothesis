module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.HeckeIntertwinersInert
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertPlaceHeckeDoubleCosetsInverseRepsLabel
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.SelfDualComap
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemIntMat

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeisenbergOrientedFiniteFixesFockPolynomialVecto
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeisenbergOrientedFiniteFixesFockPolynomialVecto
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3.FiniteHeis

variable {D : D7}

noncomputable def heisLin (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (u : WO S T) : Module.End ℂ (WO S T → ℂ) where
  toFun := heisO ψ S T u
  map_add' f g := by
    funext w
    simp only [heisO, Pi.add_apply, mul_add]
  map_smul' c f := by
    funext w
    simp only [heisO, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem lineAt_fin {θ : InfFam D} (hθ : IsInfFam θ) {S T : HSp D} (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (t : ℝ) :
    (show WO S T from lineAt θ τ z t).map (finPart D) = 0 :=
  (Classical.epsilon_spec (GlobalTheory.RealLineAt.lineAt_exists D θ hθ T.rank S.rank τ z)).2.1 t

theorem heisO_comm_real (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} {u x : WO S T} (hu : u.map (infPart D) = 0)
    (hx : x.map (finPart D) = 0) (g : WO S T → ℂ) :
    heisO ψ S T u (heisO ψ S T x g) = heisO ψ S T x (heisO ψ S T u g) := by
  rw [GlobalTheory.OrientedHeis.heisO_heisO, GlobalTheory.OrientedHeis.heisO_heisO, (GlobalTheory.OrientedHeis.symplOH_fin_real hu hx).1,
    (GlobalTheory.OrientedHeis.symplOH_fin_real hu hx).2, add_comm]

theorem heisO_dRho (ψ : AddChar (AF D.host.F) ℂ) {θ : InfFam D} (hθ : IsInfFam θ) {S T : HSp D} {u : WO S T}
    (hu : u.map (infPart D) = 0) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (g : WO S T → ℂ) :
    heisO ψ S T u (dRho (heisO ψ S T) θ τ z g) = dRho (heisO ψ S T) θ τ z (heisO ψ S T u g) := by
  funext x
  have e : (fun t : ℝ => heisO ψ S T (lineAt θ τ z t) (heisO ψ S T u g) x) =
      fun t : ℝ => ψ (symplOH S T x u) * heisO ψ S T (lineAt θ τ z t) g (x + u) := by
    funext t
    rw [← heisO_comm_real ψ hu (lineAt_fin hθ τ z t) g]
    rfl
  show ψ (symplOH S T x u) * deriv (fun t : ℝ => heisO ψ S T (lineAt θ τ z t) g (x + u)) 0 =
    deriv (fun t : ℝ => heisO ψ S T (lineAt θ τ z t) (heisO ψ S T u g) x) 0
  rw [e, deriv_const_mul_field]

theorem heisO_pureTensorO_of_finite : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsInfFam θ → ∀ sS sT BS BT f, (∀ φ, IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT f φ)) → ∀ u : WO S T, u.map (infPart D) = 0 → heisO ψ S T u f = f → ∀ φ, heisO ψ S T u (pureTensorO ψ θ S T sS sT BS BT f φ) = pureTensorO ψ θ S T sS sT BS BT f φ := by
  intro D ψ θ S T hθ sS sT BS BT f _ u hu hf φ
  have h := (GlobalTheory.OrientedHeis.pureTensorL_intertwine (fun _ => True) trivial (fun _ _ _ _ => trivial)
    (fun _ _ _ => trivial) (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT)
    (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT) (heisLin ψ S T u)
    (fun k g _ => ⟨trivial, ?_⟩) f trivial φ).2
  · have hf' : heisLin ψ S T u f = f := hf
    rw [hf'] at h
    exact h
  · obtain ⟨τ, i, j⟩ := k
    simp only [aPlusAll, aPlus, crea]
    rw [map_smul, map_sub, map_smul]
    show _ • (heisO ψ S T u (Datum.dRho _ _ _ _ _) - _ • heisO ψ S T u (Datum.dRho _ _ _ _ _)) = _
    rw [heisO_dRho ψ hθ hu, heisO_dRho ψ hθ hu]
    rfl

end GlobalTheory.Hk3.FiniteHeis
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeisenbergOrientedFiniteFixesFockPolynomialVectoStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergOriented_finite_fixes_fockPolynomialVectors : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsInfFam θ → ∀ sS sT BS BT f, (∀ φ, IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT f φ)) → ∀ u : WO S T, u.map (infPart D) = 0 → heisO ψ S T u f = f → ∀ φ, heisO ψ S T u (pureTensorO ψ θ S T sS sT BS BT f φ) = pureTensorO ψ θ S T sS sT BS BT f φ := by
  first | exact @GlobalTheory.Hk3.FiniteHeis.heisO_pureTensorO_of_finite | exact GlobalTheory.Hk3.FiniteHeis.heisO_pureTensorO_of_finite | (intros; apply GlobalTheory.Hk3.FiniteHeis.heisO_pureTensorO_of_finite <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeisenbergOperatorFixThetaDatumAwaySplitPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeisenbergOperatorFixThetaDatumAwaySplitPlaces
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3

variable {D : D7}

theorem symplO_half_off (S T : HSp D) {a : AE D} {x u : WO S T} (hx : IsHalf a x) (hu : ∀ i j, cA D a * u i j = 0) :
    symplO S T x u = 0 := by
  have h0 : cA D a • u = 0 := Matrix.ext fun i j => by
    show cA D a * u i j = 0
    exact hu i j
  rw [← (GlobalTheory.SplitScalar.isHalf_iff _ _).1 hx, GlobalTheory.SplitScalar.symplO_smul, h0, GlobalTheory.SplitScalar.symplO_zero_right]

theorem heisO_comm_off (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {a : AE D} {x u : WO S T} (hx : IsHalf a x)
    (hu : ∀ i j, cA D a * u i j = 0) (g : WO S T → ℂ) :
    heisO ψ S T u (heisO ψ S T x g) = heisO ψ S T x (heisO ψ S T u g) := by
  rw [GlobalTheory.SplitScalar.heisO_comm, GlobalTheory.SplitScalar.symplO_skew, symplO_half_off S T hx hu, neg_zero,
    AddChar.map_zero_eq_one, one_smul]

theorem heisO_fix_thetaAt_off : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (e : AE D) (Λ : AddSubgroup (WO S T))
    (c : ℂ) (f₀ Φ f : WO S T → ℂ), IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ c f₀ Φ f → ∀ u : WO S T,
    (∀ i j, e * u i j = 0 ∧ cA D e * u i j = 0) → heisO ψ S T u f₀ = f₀ → heisO ψ S T u f = f := by
  intro D ψ S T e Λ c f₀ Φ f h u hu hf₀
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := h
  have hm : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ c f₀ ((GlobalTheory.SplitScalar.heisL ψ S T u).comp Tm) :=
    { trans := fun Φ' hΦ' x hx => by
        simp only [LinearMap.comp_apply, GlobalTheory.SplitScalar.heisL_apply]
        rw [hTm.trans Φ' hΦ' x hx, heisO_comm_off ψ S T hx (fun i j => (hu i j).2)]
      modul := fun Φ' hΦ' y hy => by
        simp only [LinearMap.comp_apply, GlobalTheory.SplitScalar.heisL_apply]
        rw [hTm.modul Φ' hΦ' y hy,
          heisO_comm_off ψ S T hy (fun i j => by rw [GlobalTheory.DualPairCheck.cA_cA]; exact (hu i j).1)]
      vac := by
        simp only [LinearMap.comp_apply, GlobalTheory.SplitScalar.heisL_apply]
        rw [hTm.vac, hf₀] }
  have h1 := hall _ hm
  have h2 := hall _ hTm
  simp only [LinearMap.comp_apply, GlobalTheory.SplitScalar.heisL_apply] at h1
  rw [h2] at h1 ⊢
  exact h1.symm

end GlobalTheory.Hk3

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeisenbergOperatorFixThetaDatumAwaySplitPlacesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergOperator_fix_thetaDatum_away_splitPlaces : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (e : AE D) (Λ : AddSubgroup (WO S T)) (c : ℂ) (f₀ Φ f : WO S T → ℂ), IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ c f₀ Φ f → ∀ u : WO S T, (∀ i j, e * u i j = 0 ∧ cA D e * u i j = 0) → heisO ψ S T u f₀ = f₀ → heisO ψ S T u f = f := by
  first | exact @GlobalTheory.Hk3.heisO_fix_thetaAt_off | exact GlobalTheory.Hk3.heisO_fix_thetaAt_off | (intros; apply GlobalTheory.Hk3.heisO_fix_thetaAt_off <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodProjectorUnitaryFormsModelLaws
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodProjectorUnitaryFormsModelLaws
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3

theorem conv_map_idem {K : Type} [Field K] {H : Type} [Group H] [Fintype H] (z : MonoidAlgebra K H) (hz : z * z = z)
    (σ : K →+* ℂ) (g : H) : ∑ a, σ (z.coeff a) * σ (z.coeff (a⁻¹ * g)) = σ (z.coeff g) := by
  conv_rhs => rw [← hz]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [MonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_fintype _ _ (by simp), map_sum]
  simp [map_mul]

theorem coeff_conj_central {K : Type} [Field K] {H : Type} [Group H] (z : MonoidAlgebra K H)
    (hz : ∀ b, b * z = z * b) (g h : H) : z.coeff (g * h * g⁻¹) = z.coeff h := by
  have e := congrArg (fun y : MonoidAlgebra K H => y.coeff (g * h)) (hz (MonoidAlgebra.single g 1))
  simpa [mul_assoc] using e.symm

theorem sum_rep_idem {H : Type} [Group H] [Fintype H] {Y : Type} [AddCommGroup Y] [Module ℂ Y]
    (ρ : Representation ℂ H Y) (c : H → ℂ) (hc : ∀ g, ∑ a, c a * c (a⁻¹ * g) = c g) :
    (∑ g, c g • ρ g) * (∑ g, c g • ρ g) = ∑ g, c g • ρ g := by
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum, smul_mul_smul_comm, ← map_mul]
  calc ∑ a, ∑ b, (c a * c b) • ρ (a * b) = ∑ a, ∑ g, (c a * c (a⁻¹ * g)) • ρ g := by
        refine Finset.sum_congr rfl fun a _ => ?_
        exact Fintype.sum_equiv (Equiv.mulLeft a) _ _ fun b => by simp
    _ = ∑ g, (∑ a, c a * c (a⁻¹ * g)) • ρ g := by
        rw [Finset.sum_comm]; simp_rw [Finset.sum_smul]
    _ = ∑ g, c g • ρ g := by simp_rw [hc]

theorem sum_rep_comm {H : Type} [Group H] [Fintype H] {Y : Type} [AddCommGroup Y] [Module ℂ Y]
    (ρ : Representation ℂ H Y) (c : H → ℂ) (hc : ∀ g h, c (g * h * g⁻¹) = c h) (g : H) :
    Commute (∑ h, c h • ρ h) (ρ g) := by
  unfold Commute SemiconjBy
  rw [Finset.sum_mul, Finset.mul_sum]
  simp_rw [smul_mul_assoc, mul_smul_comm, ← map_mul]
  symm
  refine Fintype.sum_equiv (MulAut.conj g).toEquiv _ _ fun h => ?_
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply, hc]
  congr 2
  group

theorem eH_laws : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F → (∀ χ ∈ A.X, IsAbsIrrChar χ) → ∀ i, eH R i * eH R i = eH R i ∧ (∀ g, Commute (eH R i) (R.gW i (sg0 D A) g)) ∧ (∀ x, eH R i x = x ↔ (R.HW i _).e x ∈ R.Wat i (sg0 D A) R.triv) ∧ ∀ t y, eH R i (R.thG i t y) = R.thG i t y := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC hX i
  have hc : ∀ g, ∑ a, RealDat.eC (A := A) (sg0 D A) a * RealDat.eC (A := A) (sg0 D A) (a⁻¹ * g) =
      RealDat.eC (A := A) (sg0 D A) g := fun g => conv_map_idem _ (idemOf_mul_self A.X hX) (sg0 D A) g
  have hcc : ∀ g h, RealDat.eC (A := A) (sg0 D A) (g * h * g⁻¹) = RealDat.eC (A := A) (sg0 D A) h := fun g h => by
    unfold RealDat.eC
    rw [coeff_conj_central _ (fun b => idemOf_central A.X hX b) g h]
  have happ : ∀ x v, (R.HW i (sg0 D A)).e (eH R i x) v = R.eWf i (sg0 D A) ((R.HW i (sg0 D A)).e x v) := fun x v => by
    unfold eH RealDat.eWf gaL
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, MultilinearMap.sum_apply,
      MultilinearMap.smul_apply]
    refine Finset.sum_congr rfl fun g _ => congrArg _ ?_
    rw [hC.models.gW i (sg0 D A) g x]; rfl
  have hinj := (hC.models.HW i (sg0 D A)).1
  have hrange := (hC.models.HW i (sg0 D A)).2.1
  have hfix : ∀ x, eH R i x = x ↔ (R.HW i _).e x ∈ R.Wat i (sg0 D A) R.triv := fun x => by
    rw [RealDat.Wat, mem_goodPart]
    constructor
    · intro h
      refine ⟨?_, fun v => ?_⟩
      · have : (R.HW i (sg0 D A)).e x ∈ R.Wall i (sg0 D A) := hrange ▸ LinearMap.mem_range_self _ x
        exact this
      · rw [← happ, h]
    · rintro ⟨_, h⟩
      apply hinj
      refine MultilinearMap.ext fun v => ?_
      rw [happ, h]
  have hI : eH R i * eH R i = eH R i := sum_rep_idem _ _ hc
  refine ⟨hI, fun g => sum_rep_comm _ _ hcc g, hfix, fun t y => ?_⟩
  have hm := hC.thP.thF_mem i t y
  rw [← hrange] at hm
  obtain ⟨x0, hx0⟩ := hm
  have e1 : R.thG i t y = eH R i x0 := by
    apply hinj
    rw [hC.thP.thG i t y, ← hx0]
    refine MultilinearMap.ext fun v => ?_
    rw [happ]
    exact (postOn_apply _ _ _ _).symm
  rw [e1, ← Module.End.mul_apply, hI]

end GlobalTheory.Hk3
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodProjectorUnitaryFormsModelLawsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodProjector_unitaryFormsModel_laws : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F → (∀ χ ∈ A.X, IsAbsIrrChar χ) → ∀ i, eH R i * eH R i = eH R i ∧ (∀ g, Commute (eH R i) (R.gW i (sg0 D A) g)) ∧ (∀ x, eH R i x = x ↔ (R.HW i _).e x ∈ R.Wat i (sg0 D A) R.triv) ∧ ∀ t y, eH R i (R.thG i t y) = R.thG i t y := by
  first | exact @GlobalTheory.Hk3.eH_laws | exact GlobalTheory.Hk3.eH_laws | (intros; apply GlobalTheory.Hk3.eH_laws <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualAntitoneListIffInertPrimeHeckeExponents
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualAntitoneListIffInertPrimeHeckeExponents
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3

private theorem sorted_list_sign_split (d : List ℤ) (h : d.Pairwise (fun a b => b ≤ a)) :
    d = d.filter (fun x => decide (0 < x)) ++ d.filter (fun x => decide (x = 0)) ++ d.filter (fun x => decide (x < 0)) := by
  induction d with
  | nil => rfl
  | cons x t ih =>
    rw [List.pairwise_cons] at h
    obtain ⟨hx, ht⟩ := h
    have ih := ih ht
    rcases lt_trichotomy 0 x with hpos | hzero | hneg
    · have h1 : ¬ x = 0 := by omega
      have h2 : ¬ x < 0 := by omega
      rw [List.filter_cons_of_pos (by simp [hpos]), List.filter_cons_of_neg (by simp [h1]),
        List.filter_cons_of_neg (by simp [h2]), List.cons_append, List.cons_append, ← ih]
    · subst hzero
      have e1 : t.filter (fun x => decide (0 < x)) = [] := by
        rw [List.filter_eq_nil_iff]; intro y hy; simpa using hx y hy
      rw [e1, List.nil_append] at ih
      rw [List.filter_cons_of_neg (by simp), List.filter_cons_of_pos (by simp),
        List.filter_cons_of_neg (by simp), e1, List.nil_append, List.cons_append, ← ih]
    · have e1 : t.filter (fun x => decide (0 < x)) = [] := by
        rw [List.filter_eq_nil_iff]; intro y hy; have := hx y hy; simp; omega
      have e2 : t.filter (fun x => decide (x = 0)) = [] := by
        rw [List.filter_eq_nil_iff]; intro y hy; have := hx y hy; simp; omega
      have h1 : ¬ 0 < x := by omega
      have h2 : ¬ x = 0 := by omega
      rw [e1, e2, List.nil_append, List.nil_append] at ih
      rw [List.filter_cons_of_neg (by simp [h1]), List.filter_cons_of_neg (by simp [h2]),
        List.filter_cons_of_pos (by simp [hneg]), e1, e2, List.nil_append, List.nil_append, ← ih]

private theorem flatMap_singleton_natCast (l : List ℕ) : List.flatMap (fun a : ℕ => [(a : ℤ)]) l = l.map (fun a : ℕ => (a : ℤ)) := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, List.map_cons, ih]; rfl

private theorem label_list_eq_signed (n : ℕ) (s : List ℕ) : labIn n s =
    s.map (fun a : ℕ => (a : ℤ)) ++ List.replicate (n - 2 * s.length) 0 ++ (s.reverse.map fun a : ℕ => -(a : ℤ)) := by
  unfold labIn
  show List.map _ (List.flatMap (fun a : ℕ => [(a : ℤ)]) s) ++ _ ++
      List.map _ (List.flatMap (fun a : ℕ => [(a : ℤ)]) s.reverse) = _
  rw [flatMap_singleton_natCast, flatMap_singleton_natCast]
  simp [List.map_map, Function.comp_def]

theorem labIn_selfDual_iff : ∀ (n : ℕ) (d : List ℤ), (d.length = n ∧ d.Pairwise (fun a b => b ≤ a) ∧ dualLab d = d) ↔
    ∃ s : List ℕ, 2 * s.length ≤ n ∧ s.Pairwise (fun a b => b ≤ a) ∧ (∀ a ∈ s, 0 < a) ∧ d = labIn n s := by
  intro n d
  constructor
  · rintro ⟨hlen, hsort, hdual⟩
    have hsplit := sorted_list_sign_split d hsort
    set P := d.filter (fun x => decide (0 < x)) with hPdef
    set Z := d.filter (fun x => decide (x = 0)) with hZdef
    set N := d.filter (fun x => decide (x < 0)) with hNdef
    have hPN : P = (N.map Neg.neg).reverse := by
      have e : P = (dualLab d).filter (fun x => decide (0 < x)) := by rw [hdual]
      rw [e, dualLab, List.filter_reverse, List.filter_map, hNdef]
      congr 2
      apply List.filter_congr
      intro x _
      simp
    have hN : N = P.reverse.map Neg.neg := by
      rw [hPN, List.reverse_reverse, List.map_map]
      simp
    have hZ : Z = List.replicate Z.length 0 := by
      rw [List.eq_replicate_iff]
      refine ⟨rfl, ?_⟩
      intro b hb
      rw [hZdef] at hb
      simpa using (List.mem_filter.mp hb).2
    have hlenPN : N.length = P.length := by rw [hN, List.length_map, List.length_reverse]
    have hdlen : d.length = P.length + Z.length + N.length := by
      have := congrArg List.length hsplit
      simpa only [List.length_append] using this
    have hposP : ∀ x ∈ P, 0 < x := by
      intro x hx
      rw [hPdef] at hx
      simpa using (List.mem_filter.mp hx).2
    have hcast : (P.map Int.toNat).map (fun a : ℕ => (a : ℤ)) = P := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id P]
      apply List.map_congr_left
      intro x hx
      have := hposP x hx
      simp only [Function.comp_apply, id]
      omega
    refine ⟨P.map Int.toNat, ?_, ?_, ?_, ?_⟩
    · rw [List.length_map]; omega
    · have hPs : P.Pairwise (fun a b => b ≤ a) := hsort.filter _
      rw [List.pairwise_map]
      exact hPs.imp (fun h => Int.toNat_le_toNat h)
    · intro a ha
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
      have := hposP x hx
      omega
    · have hneg : ((P.map Int.toNat).reverse.map fun a : ℕ => -(a : ℤ)) = N := by
        rw [hN]
        conv_rhs => rw [← hcast]
        simp [List.map_reverse, List.map_map, Function.comp_def]
      have hZ' : Z = List.replicate (n - 2 * P.length) 0 := by
        rw [hZ]
        congr 1
        omega
      rw [label_list_eq_signed, hcast, List.length_map, hneg, ← hZ']
      exact hsplit
  · rintro ⟨s, hs, hsort, hpos, rfl⟩
    rw [label_list_eq_signed]
    refine ⟨?_, ?_, ?_⟩
    · simp only [List.length_append, List.length_map, List.length_replicate, List.length_reverse]
      omega
    · rw [List.pairwise_append, List.pairwise_append]
      refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
      · rw [List.pairwise_map]
        exact hsort.imp (fun h => by exact_mod_cast h)
      · rw [List.pairwise_replicate]
        right; exact le_refl _
      · intro a ha b hb
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
        rw [List.eq_of_mem_replicate hb]
        exact_mod_cast Nat.zero_le x
      · rw [List.pairwise_map, List.pairwise_reverse]
        refine hsort.imp (fun h => ?_)
        simp only [neg_le_neg_iff]
        exact_mod_cast h
      · intro a ha b hb
        obtain ⟨y, _, rfl⟩ := List.mem_map.mp hb
        have hb0 : -(y : ℤ) ≤ 0 := by simp
        rcases List.mem_append.mp ha with ha | ha
        · obtain ⟨x, _, rfl⟩ := List.mem_map.mp ha
          have : (0 : ℤ) ≤ x := by exact_mod_cast Nat.zero_le x
          omega
        · rw [List.eq_of_mem_replicate ha]
          exact hb0
    · simp [dualLab, List.map_append, List.reverse_append, List.map_reverse, List.map_map,
        Function.comp_def, List.map_replicate, List.reverse_replicate]

end GlobalTheory.Hk3
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualAntitoneListIffInertPrimeHeckeExponentsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDual_antitone_list_iff_inertPrimeHeckeExponents : ∀ (n : ℕ) (d : List ℤ), (d.length = n ∧ d.Pairwise (fun a b => b ≤ a) ∧ dualLab d = d) ↔ ∃ s : List ℕ, 2 * s.length ≤ n ∧ s.Pairwise (fun a b => b ≤ a) ∧ (∀ a ∈ s, 0 < a) ∧ d = labIn n s := by
  first | exact @GlobalTheory.Hk3.labIn_selfDual_iff | exact GlobalTheory.Hk3.labIn_selfDual_iff | (intros; apply GlobalTheory.Hk3.labIn_selfDual_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenvectorAdjointIntertwinerNormalOperators
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenvectorAdjointIntertwinerNormalOperators
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HkUp

theorem adjoint_apply_of_normal_eigen {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T : Module.End ℂ V) (hT : Commute T (LinearMap.adjoint T))
    (μ : ℂ) (v : V) (hv : T v = μ • v) :
    LinearMap.adjoint T v = (starRingEnd ℂ) μ • v := by
  set S : Module.End ℂ V := T - μ • LinearMap.id with hS
  have hSadj : LinearMap.adjoint S = LinearMap.adjoint T - (starRingEnd ℂ) μ • LinearMap.id := by
    rw [hS, map_sub, LinearMap.adjoint.map_smulₛₗ, LinearMap.adjoint_id]
  have hcomm : Commute S (LinearMap.adjoint S) := by
    rw [hSadj, hS]
    exact (((hT.sub_right (Commute.smul_right (Commute.one_right _) _)).sub_left
      ((Commute.one_left _).smul_left _ |>.sub_right (Commute.smul_right (Commute.one_right _) _))))
  have hSv : S v = 0 := by simp [hS, hv]
  have h0 : LinearMap.adjoint S v = 0 := by
    have : ⟪LinearMap.adjoint S v, LinearMap.adjoint S v⟫_ℂ = 0 := by
      rw [LinearMap.adjoint_inner_left, ← Module.End.mul_apply, hcomm.eq, Module.End.mul_apply,
        hSv, map_zero, inner_zero_right]
    exact inner_self_eq_zero.mp this
  rw [hSadj] at h0
  simpa [sub_eq_zero] using h0

theorem eigen_up_along_adjoint : ∀ {X E I : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] (Θ : X →ₗ[ℂ] E) (op : I → Module.End ℂ X) (h : I → Module.End ℂ E), (∀ i u, Θ (op i u) = h i (Θ u)) → (∀ i, Commute (op i) (LinearMap.adjoint (op i))) → (∀ i, Commute (h i) (LinearMap.adjoint (h i))) → ∀ i (l : ℂ) w, h i w = l • w → op i (LinearMap.adjoint Θ w) = l • LinearMap.adjoint Θ w := by
  intro X E I _ _ _ _ _ _ Θ op h hint hop hh i l w hw
  have hstar : LinearMap.adjoint (h i) w = (starRingEnd ℂ) l • w :=
    adjoint_apply_of_normal_eigen (h i) (hh i) l w hw

  have hcomp : Θ ∘ₗ op i = h i ∘ₗ Θ := LinearMap.ext (hint i)
  have hadj : LinearMap.adjoint (op i) ∘ₗ LinearMap.adjoint Θ
      = LinearMap.adjoint Θ ∘ₗ LinearMap.adjoint (h i) := by
    rw [← LinearMap.adjoint_comp, ← LinearMap.adjoint_comp, hcomp]
  have h1 : LinearMap.adjoint (op i) (LinearMap.adjoint Θ w)
      = (starRingEnd ℂ) l • LinearMap.adjoint Θ w := by
    have := LinearMap.congr_fun hadj w
    simp only [LinearMap.comp_apply] at this
    rw [this, hstar, map_smulₛₗ, RingHom.id_apply]
  have h2 := adjoint_apply_of_normal_eigen (LinearMap.adjoint (op i)) ?_ _ _ h1
  · simpa [LinearMap.adjoint_adjoint] using h2
  · rw [LinearMap.adjoint_adjoint]; exact (hop i).symm

end GlobalTheory.HkUp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenvectorAdjointIntertwinerNormalOperatorsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenvector_adjoint_intertwiner_normal_operators : ∀ {X E I : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] (Θ : X →ₗ[ℂ] E) (op : I → Module.End ℂ X) (h : I → Module.End ℂ E), (∀ i u, Θ (op i u) = h i (Θ u)) → (∀ i, Commute (op i) (LinearMap.adjoint (op i))) → (∀ i, Commute (h i) (LinearMap.adjoint (h i))) → ∀ i (l : ℂ) w, h i w = l • w → op i (LinearMap.adjoint Θ w) = l • LinearMap.adjoint Θ w := by
  first | exact @GlobalTheory.HkUp.eigen_up_along_adjoint | exact GlobalTheory.HkUp.eigen_up_along_adjoint | (intros; apply GlobalTheory.HkUp.eigen_up_along_adjoint <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsPrimeIdemOfInert
section -- merged from Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.InertLocalIndices
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH IsDedekindDomain NumberField Polynomial
open Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.InertLocalIndices

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def InertOver (v : HeightOneSpectrum (𝓞 D.host.F)) (P : Formalism.L2.DIV.Pl D.host.E) : Prop :=
  Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) v.asIdeal = P.asIdeal

def LocAt (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (x : Bridge.Gf V) : Prop :=
  ∀ v' : HeightOneSpectrum (𝓞 D.host.F), v' ≠ v →
    (Units.val (x : GL (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E))).map
      (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v') (AlgHom.id D.host.F D.host.E)) = 1

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

variable (R : RealDat D A Ks)

end GlobalTheory.IndefiniteRowSideFullHecke.InertLocalIndices

end
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField
open Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev
open scoped TensorProduct

namespace GlobalTheory.HeckeRowsCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Generic

theorem repr_map {F E A B ι : Type} [Field F] [Field E] [Algebra F E] [CommRing A] [CommRing B] [Algebra F A] [Algebra F B]
    (b : Module.Basis ι F E) (φ : A →ₐ[F] B) (z : A ⊗[F] E) (i : ι) :
    (Algebra.TensorProduct.basis B b).repr (Algebra.TensorProduct.map φ (AlgHom.id F E) z) i =
      φ ((Algebra.TensorProduct.basis A b).repr z i) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [Algebra.TensorProduct.basis_repr_tmul]
  | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]

theorem coord_eq_zero {F E A B ι : Type} [Field F] [Field E] [Algebra F E] [CommRing A] [CommRing B] [Algebra F A] [Algebra F B]
    (b : Module.Basis ι F E) (φ : A →ₐ[F] B) (z : A ⊗[F] E) (h : Algebra.TensorProduct.map φ (AlgHom.id F E) z = 0) (i : ι) :
    φ ((Algebra.TensorProduct.basis A b).repr z i) = 0 := by
  rw [← repr_map, h, map_zero, Finsupp.zero_apply]

theorem coord_eq_zero₂ {F E A B C ι : Type} [Field F] [Field E] [Algebra F E] [CommRing A] [CommRing B] [CommRing C] [Algebra F A]
    [Algebra F B] [Algebra F C] (b : Module.Basis ι F E) (φ : A →ₐ[F] B) (ψ : B →ₐ[F] C) (z : A ⊗[F] E)
    (h : Algebra.TensorProduct.map ψ (AlgHom.id F E) (Algebra.TensorProduct.map φ (AlgHom.id F E) z) = 0) (i : ι) :
    ψ (φ ((Algebra.TensorProduct.basis A b).repr z i)) = 0 := by
  rw [← repr_map, coord_eq_zero b ψ _ h]

theorem mul_eq_of_coord {F E A ι : Type} [Field F] [Field E] [Algebra F E] [CommRing A] [Algebra F A]
    (b : Module.Basis ι F E) (ε : A) (z : A ⊗[F] E)
    (h : ∀ i, ε * (Algebra.TensorProduct.basis A b).repr z i = (Algebra.TensorProduct.basis A b).repr z i) :
    algebraMap A (A ⊗[F] E) ε * z = z := by
  rw [← Algebra.smul_def]
  refine (Algebra.TensorProduct.basis A b).ext_elem fun i => ?_
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, h]

theorem pair_mul_eq {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {α : Af F} (a1 : evalV F v α = 1)
    (a : AF F) (e0 : fstA F a = 0) (e1 : ∀ v', v' ≠ v → evalV F v' (sndA F a) = 0) : pairA F 0 α * a = a := by
  refine Prod.ext ((zero_mul (fstA F a)).trans e0.symm) (FiniteAdeleRing.ext _ fun w => ?_)
  change evalV F w (α * sndA F a) = evalV F w (sndA F a)
  rw [map_mul]
  by_cases hw : w = v
  · subst hw
    rw [a1, one_mul]
  · rw [e1 w hw, mul_zero]

theorem map_eq_one_iff {R S : Type} [CommRing R] [CommRing S] (π : R →+* S) {n : ℕ} (m : Matrix (Fin n) (Fin n) R) :
    m.map π = 1 ↔ ∀ i j, π ((m - 1) i j) = 0 := by
  rw [← Matrix.ext_iff]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [Matrix.sub_apply, map_sub, sub_eq_zero, Matrix.map_apply, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

end Generic

variable {D : D7}

section Inert

variable {v : HeightOneSpectrum (𝓞 D.host.F)} {P : Pl D.host.E}

theorem under_eq (h : IndefiniteRowSideFullHecke.InertLocalIndices.InertOver v P) : P.under (𝓞 D.host.F) = v :=
  HeightOneSpectrum.ext (v.isMaximal.eq_of_le (P.under (𝓞 D.host.F)).isPrime.ne_top
    (Ideal.map_le_iff_le_comap.1 (le_of_eq h))).symm

theorem eq_of_under (h : IndefiniteRowSideFullHecke.InertLocalIndices.InertOver v P) {Q : Pl D.host.E} (hQ : Q.under (𝓞 D.host.F) = v) : Q = P := by
  refine (GlobalTheory.IdemSupport.eq_of_le ?_).symm
  rw [← (h : _ = P.asIdeal), Ideal.map_le_iff_le_comap, ← hQ]
  exact le_rfl

theorem isPrimeIdem_of_inert (h : IndefiniteRowSideFullHecke.InertLocalIndices.InertOver v P) {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) :
    IsPrimeIdem P (algebraMap _ (Formalism.L2.Theta.AE D) ε) (algebraMap _ _ ε) := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨h0, h1, h2⟩ := GlobalTheory.IdemSupport.place_comp hΦ hε
  exact Or.inr ⟨rfl, ⟨v, ε, hε, rfl⟩, (GlobalTheory.IdemSupport.tie_iff hΦ (GlobalTheory.IdemSupport.place_idem hΦ hε) h0 P).2
    ⟨h0, h1 P (under_eq h), fun Q hQ => h2 Q fun e => hQ (eq_of_under h e)⟩⟩

end Inert

section Local

variable (V : HSp D)

theorem locAt_iff (v : HeightOneSpectrum (𝓞 D.host.F)) (x : Bridge.Gf V) :
    IndefiniteRowSideFullHecke.HeckeIntertwinersInert.LocAt V v x ↔ IndefiniteRowSideFullHecke.InertLocalIndices.LocAt V v x := Iff.rfl

def cmp (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    Af D.host.F ⊗[D.host.F] D.host.E →+* Fv D.host.F v ⊗[D.host.F] D.host.E :=
  (Algebra.TensorProduct.map (evalV D.host.F v) (AlgHom.id D.host.F D.host.E)).toRingHom

def locGrp (v : HeightOneSpectrum (𝓞 D.host.F)) : Subgroup (Bridge.Gf V) :=
  ⨅ (v') (_ : v' ≠ v), ((Formalism.UG.bc (cmp D v')).comp (finHom V).range.subtype).ker

theorem mem_locGrp {v : HeightOneSpectrum (𝓞 D.host.F)} {x : Bridge.Gf V} : x ∈ locGrp V v ↔ IndefiniteRowSideFullHecke.InertLocalIndices.LocAt V v x := by
  simp only [locGrp, Subgroup.mem_iInf]
  exact forall₂_congr fun v' _ => ⟨fun h => congrArg Units.val h, fun h => Units.ext h⟩

abbrev fin : GA D V →* Bridge.Gf V := (finHom V).rangeRestrict

theorem idem_mul_eq {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) (z : Formalism.L2.Theta.AE D)
    (h0 : infPart D z = 0) (h1 : ∀ v', v' ≠ v → cmp D v' (finPart D z) = 0) : algebraMap _ (Formalism.L2.Theta.AE D) ε * z = z := by
  obtain ⟨α, rfl, a1, -⟩ := hε
  exact mul_eq_of_coord (Module.finBasis D.host.F D.host.E) _ z fun i => pair_mul_eq a1 _
    (coord_eq_zero _ (fstA D.host.F) z h0 i) fun v' hv => coord_eq_zero₂ _ (sndA D.host.F) (evalV D.host.F v') z (h1 v' hv) i

theorem suppF_iff {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) {g : GA D V}
    (hg : g ∈ GfC V) : SuppF V (algebraMap _ _ ε) g ↔ fin V g ∈ locGrp V v := by
  have key : ∀ v', (Units.val (finHom V g)).map (cmp D v') = (Formalism.L2.Theta.mt V g).map ((cmp D v').comp (finPart D)) :=
    fun _ => rfl
  rw [mem_locGrp]
  constructor
  · intro h v' hv
    refine (key v').trans ((map_eq_one_iff _ _).2 fun i j => ?_)
    obtain ⟨α, rfl, -, a0⟩ := hε
    have h2 : (cmp D v').comp (finPart D) (algebraMap _ (Formalism.L2.Theta.AE D) (pairA D.host.F 0 α)) = 0 := by
      change evalV D.host.F v' α ⊗ₜ[D.host.F] (1 : D.host.E) = 0
      rw [a0 v' hv, TensorProduct.zero_tmul]
    rw [← h i j, RingHom.map_mul, h2, zero_mul]
  · intro h i j
    have h0 : (Formalism.L2.Theta.mt V g).map (infPart D) = 1 := congrArg Units.val (MonoidHom.mem_ker.1 hg)
    exact idem_mul_eq hε _ ((map_eq_one_iff _ _).1 h0 i j)
      fun v' hv => (map_eq_one_iff _ _).1 ((key v').symm.trans (h v' hv)) i j

theorem fin_lift (x : Bridge.Gf V) : ∃ g ∈ GfC V, fin V g = x := by
  obtain ⟨x, g, rfl⟩ := x
  let f : Formalism.L2.Theta.AE D := algebraMap _ _ (pairA D.host.F 0 1)
  have hp : pairA D.host.F 0 1 * pairA D.host.F 0 1 = pairA D.host.F 0 1 :=
    Prod.ext (mul_zero (0 : Ainf D.host.F)) (mul_one (1 : Af D.host.F))
  have hff : f * f = f := by rw [← RingHom.map_mul, hp]
  obtain ⟨g₁, g₂, h₁, h₂, rfl⟩ := GlobalTheory.IdemSupport.exists_split V hff (GlobalTheory.IdemSupport.cA_algebraMap _) g
  have b : finHom V g₂ = 1 := by
    refine Units.ext ((map_eq_one_iff (finPart D) _).2 fun i j => ?_)
    have h3 : finPart D (1 - f) = 0 := by
      rw [RingHom.map_sub, RingHom.map_one, sub_eq_zero]
      rfl
    refine (congrArg (finPart D) (h₂ i j)).symm.trans ?_
    rw [RingHom.map_mul, h3, zero_mul]
  refine ⟨g₁, GlobalTheory.IdemSupport.mem_GfC_of_suppF V (TensorProduct.zero_tmul _ _) h₁, Subtype.ext ?_⟩
  show finHom V g₁ = finHom V (g₁ * g₂)
  rw [map_mul, b, mul_one]


end Local

section Compare

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}

end Compare

end GlobalTheory.HeckeRowsCompare

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CombOfTied
noncomputable section

namespace GlobalTheory.Ggeo.KerComb

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical

theorem comb_of_tied : Formalism.L2.KerInert.AlgTAll → ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), t.Hyp → ∀ u μ w, LevFree Y u μ w → ∀ i < D.R.m, ∀ c c', TaylorLogMetric.admitted D _ _ ((t.O u μ).lat i c).1 ((t.O u μ).lat (i + 1) c').1 ∧ TaylorLogMetric.IsComb D t.B.tor (t.B.eNat t.χ) (t.ent.lam w) ((t.O u μ).lat i c).1 ((t.O u μ).lat (i + 1) c').1 (TaylorLogMetric.pSer D (t.ent.lam w) ((t.O u μ).Th i c c')) := by
  intro hAlg D L hT Gi Gl K Y cX ex t hH u μ w hw i hi c c'
  have hEven : ∀ j, Even (D.R.N j) := fun j => D.R.k_even.add (D.R.t_odd.add_one.mul_left j)
  have hAdm : TaylorLogMetric.admitted D _ _ ((t.O u μ).lat i c).1 ((t.O u μ).lat (i + 1) c').1 :=
    ⟨hEven i, hEven (i + 1), ((t.O u μ).lat i c).2, ((t.O u μ).lat (i + 1) c').2⟩
  refine ⟨hAdm, ?_⟩
  have hTA : TransAlg D t.B.tor (t.B.eNat t.χ) :=
    transcendence_algebraic_eigen D t.cc t.δ t.B t.χ t.cc_ok t.δ_ok (KS.Lat.delta_ne t.cc_ok t.δ_ok) (t.B.stdOK t.cc_ok t.δ_ok)
      (hAlg D t.cc t.δ t.B t.χ t.cc_ok t.δ_ok t.χ_ok)
  have hS : D.what₂.places.resChar w ∉ (t.O u μ).S := by
    obtain ⟨h1, h2, h3⟩ := hw
    rw [t.O_S u μ]
    intro hm
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton, not_or] at h2 hm
    rcases hm with h | (h | h) | h
    exacts [h1 h, h2.1 h, h2.2 h, h3 h]
  have hA' := hAdm
  rw [t.O_lat u μ i c, t.O_lat u μ (i + 1) c'] at hA' ⊢
  rw [t.O_Th u μ i c c']
  exact first_kernel_law_reading D t.X u (D.chTw u μ) (t.rd u μ) t.seam t.amb t.cc t.δ (t.B.eNat t.χ) (t.O u μ).S i (hH u μ i hi) hTA c c' hA' _ (t.ent.lam w) hS

end GlobalTheory.Ggeo.KerComb
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitHeckeElementLabelZerosThenNegOnes
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitHeckeElementLabelZerosThenNegOnes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3Split

theorem splitLab_pairwise (n k : ℕ) : (splitLab n k).Pairwise (fun a b => b ≤ a) := by
  unfold splitLab
  rw [List.pairwise_append]
  refine ⟨by simp, by simp, fun a ha b hb => ?_⟩
  rw [List.eq_of_mem_replicate ha, List.eq_of_mem_replicate hb]
  norm_num

theorem isLabElt_of_isTEnv : ∀ {D : D7} (V : HSp D) {Pl0 : Type} (pl : Pl0 → Pl D.host.E) (ok : Set Pl0) (i : ok × ℕ) (x : Bridge.Gf V), (i.2 ≤ V.rank → isTEnv V pl ok i x → IsLabElt V (pl i.1) (splitLab V.rank i.2) x) ∧ (isLocEnv V pl ok i x → IsLocElt V (pl i.1) x) ∧ (splitLab V.rank i.2).Pairwise (fun a b => b ≤ a) := by
  intro D V Pl0 pl ok i x
  refine ⟨fun hk h => ?_, fun h => ?_, splitLab_pairwise _ _⟩
  · obtain ⟨α, ⟨e, ϖ, he, h1, h2, hα⟩, hx⟩ := h hk
    have hI : IsPrimeIdem (pl i.1) e (e + cA D e) := Or.inl ⟨he, rfl⟩
    have H := GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V
    obtain ⟨hf1, hf2, -⟩ := H.2.2.1 _ _ _ hI
    obtain ⟨⟨L, hL⟩, -⟩ := H.1 _ hf1 hf2
    exact ⟨e, e + cA D e, ϖ, α⁻¹, hI, h1, h2, inv_mem hα.1, hx, (hL _).1 (inv_mem ((hL _).2 hα.2.1)),
      GlobalTheory.SplitDivisors.divAt_inv_of_isHeckeElt V _ e ϖ _ α he h1 h2 hk hα⟩
  · obtain ⟨e, α, he, hα, hs, hx⟩ := h
    exact ⟨e, e + cA D e, α, Or.inl ⟨he, rfl⟩, hα, hx, hs⟩

end GlobalTheory.Hk3Split
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitHeckeElementLabelZerosThenNegOnesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_hecke_element_label_zeros_then_neg_ones : ∀ {D : D7} (V : HSp D) {Pl0 : Type} (pl : Pl0 → Pl D.host.E) (ok : Set Pl0) (i : ok × ℕ) (x : Bridge.Gf V), (i.2 ≤ V.rank → isTEnv V pl ok i x → IsLabElt V (pl i.1) (splitLab V.rank i.2) x) ∧ (isLocEnv V pl ok i x → IsLocElt V (pl i.1) x) ∧ (splitLab V.rank i.2).Pairwise (fun a b => b ≤ a) := by
  first | exact @GlobalTheory.Hk3Split.isLabElt_of_isTEnv | exact GlobalTheory.Hk3Split.isLabElt_of_isTEnv | (intros; apply GlobalTheory.Hk3Split.isLabElt_of_isTEnv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DvdPowZeroIff
noncomputable section

namespace GlobalTheory.Hk3.IntWitt

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

def DvdPow (ϖ : L) (k : ℕ) (a : L) : Prop := ∃ b ∈ Formalism.UG.intL L, a = ϖ ^ k * b

def IndepMod (ϖ : L) {ι : Type} [Fintype ι] {m : ℕ} (z : ι → Fin m → L) : Prop :=
  ∀ d : ι → L, (∀ i, d i ∈ Formalism.UG.intL L) → (∀ r, DvdPow ϖ 1 (∑ i, d i * z i r)) → ∀ i, DvdPow ϖ 1 (d i)

theorem dvdPow_zero_iff {ϖ a : L} : DvdPow ϖ 0 a ↔ a ∈ Formalism.UG.intL L := by
  constructor
  · rintro ⟨b, hb, rfl⟩; simpa using hb
  · intro h; exact ⟨a, h, by simp⟩

theorem dvdPow_add {ϖ a b : L} {k : ℕ} (ha : DvdPow ϖ k a) (hb : DvdPow ϖ k b) : DvdPow ϖ k (a + b) := by
  obtain ⟨c, hc, rfl⟩ := ha; obtain ⟨d, hd, rfl⟩ := hb
  exact ⟨c + d, (Formalism.UG.intL L).add_mem hc hd, by ring⟩

theorem dvdPow_neg {ϖ a : L} {k : ℕ} (ha : DvdPow ϖ k a) : DvdPow ϖ k (-a) := by
  obtain ⟨c, hc, rfl⟩ := ha
  exact ⟨-c, (Formalism.UG.intL L).neg_mem hc, by ring⟩

theorem dvdPow_sub {ϖ a b : L} {k : ℕ} (ha : DvdPow ϖ k a) (hb : DvdPow ϖ k b) : DvdPow ϖ k (a - b) := by
  rw [sub_eq_add_neg]; exact dvdPow_add ha (dvdPow_neg hb)

theorem dvdPow_zero (ϖ : L) (k : ℕ) : DvdPow ϖ k 0 := ⟨0, (Formalism.UG.intL L).zero_mem, by simp⟩

theorem dvdPow_mul_int {ϖ a c : L} {k : ℕ} (ha : DvdPow ϖ k a) (hc : c ∈ Formalism.UG.intL L) : DvdPow ϖ k (c * a) := by
  obtain ⟨b, hb, rfl⟩ := ha
  exact ⟨c * b, (Formalism.UG.intL L).mul_mem hc hb, by ring⟩

theorem dvdPow_sum {ϖ : L} {k : ℕ} {ι : Type} (s : Finset ι) (f : ι → L) (h : ∀ i ∈ s, DvdPow ϖ k (f i)) :
    DvdPow ϖ k (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using dvdPow_zero ϖ k
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact dvdPow_add (h j (Finset.mem_insert_self j s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem dvdPow_mono {ϖ a : L} {k l : ℕ} (hϖ : ϖ ∈ Formalism.UG.intL L) (hlk : l ≤ k) (ha : DvdPow ϖ k a) : DvdPow ϖ l a := by
  obtain ⟨b, hb, rfl⟩ := ha
  refine ⟨ϖ ^ (k - l) * b, (Formalism.UG.intL L).mul_mem ((Formalism.UG.intL L).pow_mem hϖ _) hb, ?_⟩
  rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hlk]

end GlobalTheory.Hk3.IntWitt

end
end
