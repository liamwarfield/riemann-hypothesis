module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalComponentContinuousIsoFixed
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepVectorLiftPairFlagLevelRealizedChain
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointHalfDatumStabilizerPairMove
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsInertTop
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PadOneMemSecondBlockTriangular
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelCoverFormsMulComponentFunction
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockVectorsKilledHeisenbergAverageIsotropic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIdempotentMulNatPowOfMul
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegralInverseAtSplitPlacesOfUnits

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockHarmonicValueSpaceMapEqDualWeylModuleFunctio
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockHarmonicValueSpaceMapEqDualWeylModuleFunctio
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
open MvPolynomial

namespace GlobalTheory.ExportSeries.Onto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {n : ℕ}

def coefLin (lam : D.what₂.Tau → DomWeight n) : Pol ℂ D.what₂.Tau n →ₗ[ℂ] (GLR D n → ℂ) where
  toFun F := coefFn (RingHom.id ℂ) lam F
  map_add' F G := by
    funext x
    simp only [coefFn, map_add (f := _), mul_add, Pi.add_apply]
  map_smul' c F := by
    funext x
    simp only [coefFn, smul_eq_C_mul, map_mul, eval₂Hom_C, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem coefFn_actP (lam : D.what₂.Tau → DomWeight n) (u : GLR D n) (F : Pol ℂ D.what₂.Tau n) (x : GLR D n) :
    coefFn (RingHom.id ℂ) lam (actP lam (invTrK u) F) x = coefFn (RingHom.id ℂ) lam F (u⁻¹ * x) := by
  have e1 : actP lam (invTrK u) F = detTwK lam (invTrK u) • trAct (invTrK u) F := rfl
  have e2 : (eval₂Hom (RingHom.id ℂ) (fun v : D.what₂.Tau × Fin n × Fin n => (x v.1).val v.2.1 v.2.2)).comp
        (trAct (invTrK u) : Pol ℂ D.what₂.Tau n →+* Pol ℂ D.what₂.Tau n) =
      eval₂Hom (RingHom.id ℂ) (fun v => ((u⁻¹ * x) v.1).val v.2.1 v.2.2) := by
    refine MvPolynomial.ringHom_ext (fun a => by simp [trAct, Formalism.GradedWeylDivisibility.blockAct]) fun v => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [RingHom.comp_apply, RingHom.coe_coe, trAct, Formalism.GradedWeylDivisibility.blockAct, aeval_X, map_sum, map_mul, eval₂Hom_C,
      eval₂Hom_X', Pi.mul_apply, Pi.inv_apply, Units.val_mul, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun b _ => rfl
  have e3 : (RingHom.id ℂ) (detTwK lam (invTrK u)) =
      ((detFam (fun τ => (lam τ).detShift) u⁻¹ : ℂˣ) : ℂ) := by
    simp only [detTwK, detPow, detFam, map_prod, MonoidHom.coe_mk, OneHom.coe_mk, Units.coe_prod, Units.val_zpow_eq_zpow_val,
      map_zpow₀, GeneralLinearGroup.val_det_apply]
    refine Finset.prod_congr rfl fun τ _ => ?_
    congr 1
    change (((u τ)⁻¹).valᵀ).det = _
    rw [det_transpose]
    rfl
  rw [coefFn, coefFn, e1, smul_eq_C_mul, map_mul, eval₂Hom_C, e3, ← e2, map_mul, Units.val_mul]
  simp only [RingHom.comp_apply, RingHom.coe_coe]
  ring

theorem invTrK_invTrK (g : GLR D n) : invTrK (invTrK g) = g := by
  funext τ
  exact Units.ext rfl

theorem map_harm_eq (D : D7) (m n : ℕ) (w : Weight D n) (B : GLR D n) (hw : w.Good) (hm : ∀ τ, w.p τ + w.q τ ≤ m) :
    (harm m w B).map (harmFn m w B) =
      Submodule.span ℂ {φ | ∃ F : VV ℂ w.lam, φ = coefFn (RingHom.id ℂ) w.lam (F : Pol ℂ D.what₂.Tau n)} := by
  obtain ⟨s, hs⟩ := GlobalTheory.T.fockMinorProduct_eq_sign_dualWeylExtremalVector D m n w B hw hm
  have hs0 : ((s : ℤ) : ℂ) ≠ 0 := by exact_mod_cast s.ne_zero
  have h1 : {φ | ∃ F : VV ℂ w.lam, φ = coefFn (RingHom.id ℂ) w.lam (F : Pol ℂ D.what₂.Tau n)} =
      ((VV ℂ w.lam).map (coefLin w.lam) : Set (GLR D n → ℂ)) := by
    ext φ
    constructor
    · rintro ⟨F, rfl⟩
      exact ⟨F, F.2, rfl⟩
    · rintro ⟨F, hF, rfl⟩
      exact ⟨⟨F, hF⟩, rfl⟩
  have key : ∀ u : GLR D n, harmFn m w B (fockGL m w B u (w.delta m)) =
      ((s : ℤ) : ℂ) • coefLin w.lam (actP w.lam (invTrK (u * B)) (ten fun τ => extremal ℂ n (w.lam τ))) := fun u => by
    funext x
    rw [harmFn_fockGL, hs, Pi.smul_apply, smul_eq_mul]
    congr 1
    change _ = coefFn _ _ _ _
    rw [coefFn_actP, _root_.mul_inv_rev, mul_assoc]
  rw [h1, Submodule.span_eq, GlobalTheory.OrbitSpan.VV_eq_span_orbit, harm, Submodule.map_span, Submodule.map_span]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
    rw [key]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ⟨_, rfl⟩, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
    have h2 := key (invTrK g * B⁻¹)
    rw [inv_mul_cancel_right, invTrK_invTrK] at h2
    refine (Submodule.smul_mem_iff _ hs0).1 ?_
    beta_reduce
    rw [← h2]
    exact Submodule.subset_span ⟨_, ⟨_, rfl⟩, rfl⟩

end GlobalTheory.ExportSeries.Onto

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockHarmonicValueSpaceMapEqDualWeylModuleFunctioStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockHarmonicValueSpace_map_eq_dualWeylModuleFunctions : ∀ (D : D7) (m n : ℕ) (w : Weight D n) (B : GLR D n), w.Good → (∀ τ, w.p τ + w.q τ ≤ m) → (harm m w B).map (harmFn m w B) = Submodule.span ℂ {φ | ∃ F : VV ℂ w.lam, φ = coefFn (RingHom.id ℂ) w.lam (F : Pol ℂ D.what₂.Tau n)} := by
  first | exact @GlobalTheory.ExportSeries.Onto.map_harm_eq | exact GlobalTheory.ExportSeries.Onto.map_harm_eq | (intros; apply GlobalTheory.ExportSeries.Onto.map_harm_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VacC
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum
  IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Links (PolF)
open Formalism.L2.NTheta (IsIdemAt)
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.ExportSeries.DualType

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.StepLaw (ResAt UnrOff)

variable {D : D7} {S T : HSp D}


open Classical in
def allP (B : Base S T) (Q : Finset (Pl D.host.E)) : Finset (Pl D.host.E) := B.G.Pg ∪ (B.de.Q ∪ Q)


open Classical in
def resP (B : Base S T) (ν : Twist D Circle) (PP : Pl D.host.E) : (kP PP)ˣ →* ℂˣ :=
  (if PP ∈ B.G.Pg then B.G.muC PP else 1) * B.de.locC PP * ν.locC PP

def vacC (B : Base S T) (ν : Twist D Circle) (g : GA D S) (h : GA D T) : ℂˣ :=
  ∏ PP ∈ allP B ν.Q, (resP B ν PP (GeneralLinearGroup.det (redFn B.F.βS PP (Lev.finE S g))))⁻¹ *
    resP B ν PP (GeneralLinearGroup.det (redFn B.F.βT PP (Lev.finE T h)))

end GlobalTheory.ExportSeries.DualType
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaCoefficientIsSchwartzBruhatUniformSplit
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaCoefficientIsSchwartzBruhatUniformSplit
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef

noncomputable section

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.DownLift.SplitCoef

variable {D : D7}

theorem symplO_nsmul_left_eq (S T : HSp D) (k : ℕ) (l x : WO S T) :
    symplO S T (k • l) x = symplO S T l (k • x) := by
  induction k with
  | zero => rw [zero_nsmul, zero_nsmul, GlobalTheory.PlaceModel.symplO_zero_left, GlobalTheory.PlaceModel.symplO_zero_right]
  | succ n ih => rw [succ_nsmul, succ_nsmul, GlobalTheory.PlaceModel.symplO_add_left, GlobalTheory.PlaceModel.symplO_add_right, ih]

theorem coef_isSBHalf_uniform : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ a : AE D, IsSplitIdem D a → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → (∃ k : ℕ, 0 < k ∧ (∀ u ∈ latH S T ΛS ΛT, IsHalf a u ∨ IsHalf (cA D a) u → heisO ψ S T (k • u) f = f) ∧ ∀ ℓ, InvForm ψ S T a ℓ → ∀ x, IsHalf a x → ℓ (heisO ψ S T x f) ≠ 0 → k • x ∈ latH S T ΛS ΛT) ∧ (∀ ℓ, InvForm ψ S T a ℓ → IsSBHalf a (latH S T ΛS ΛT) (coef ψ S T a ℓ f)) ∧ ∃ X : Finset (WO S T), (∀ x ∈ X, IsHalf a x) ∧ ∀ x, IsHalf a x → (∀ ℓ, InvForm ψ S T a ℓ → ℓ (heisO ψ S T x f) = 0) ∨ ∃ x₁ ∈ X, heisO ψ S T x f = heisO ψ S T x₁ f := by
  intro D ψ S T hψ ΛS ΛT hS hT a ha f hf
  classical
  have ha' := GlobalTheory.SplitScalar.isSplitIdem_conj ha
  have hd := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hψ hS hT).1
  have hstc : ∀ u ∈ latH S T ΛS ΛT, cA D a • u ∈ latH S T ΛS ΛT := fun u hu =>
    GlobalTheory.SplitScalar.idem_smul_mem ha'.1 u hu
  obtain ⟨U, hU, hUf⟩ := hf.level
  obtain ⟨k, hk, hkU⟩ := (GlobalTheory.LatLevel.level_of_generators D S T ΛS ΛT hS hT
    (GlobalTheory.LatFinGen.latO_finitely_generated D S T ΛS ΛT hS hT)).1 U hU
  have hinv : ∀ u ∈ latH S T ΛS ΛT, heisO ψ S T (k • u) f = f := fun u hu =>
    hUf _ (hkU u hu) (GlobalTheory.SplitScalar.latO_fin ((latH S T ΛS ΛT).nsmul_mem hu k))
  have hsupp : ∀ ℓ, InvForm ψ S T a ℓ → ∀ x, IsHalf a x → ℓ (heisO ψ S T x f) ≠ 0 → k • x ∈ latH S T ΛS ΛT := by
    intro ℓ hℓ x hx hne
    by_contra hn
    obtain ⟨l, hl, hlh, hlne⟩ := GlobalTheory.SplitScalar.exists_dual_half ha hd hstc
      (GlobalTheory.SplitScalar.isHalf_nsmul hx k) hn
    have h1 := hℓ (k • l) (GlobalTheory.SplitScalar.isHalf_nsmul hlh k) _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf x)
    rw [GlobalTheory.SplitScalar.heisO_comm, hinv l hl, map_smul, smul_eq_mul, symplO_nsmul_left_eq] at h1
    apply hlne
    have h2 : (ψ (symplO S T l (k • x)) - 1) * ℓ (heisO ψ S T x f) = 0 := by
      rw [sub_mul, h1, one_mul, sub_self]
    exact sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_right hne)
  have hcoef : ∀ ℓ, InvForm ψ S T a ℓ → IsSBHalf a (latH S T ΛS ΛT) (coef ψ S T a ℓ f) := by
    intro ℓ hℓ
    refine ⟨fun t ht => ?_, k, hk, fun u hu huh t => ?_, fun t ht => ?_⟩
    · by_contra hn
      exact ht (by simp only [coef, if_neg hn])
    · by_cases htt : IsHalf a t
      · have h2 : IsHalf a (t + k • u) := GlobalTheory.SplitScalar.isHalf_add htt (GlobalTheory.SplitScalar.isHalf_nsmul huh k)
        simp only [coef, if_pos htt, if_pos h2]
        rw [GlobalTheory.SplitScalar.heisO_add_of_orth ψ S T
          (GlobalTheory.SplitScalar.half_orth ha htt (GlobalTheory.SplitScalar.isHalf_nsmul huh k)), hinv u hu]
      · have h2 : ¬ IsHalf a (t + k • u) := fun h => htt (by
          have := GlobalTheory.SplitScalar.isHalf_sub h (GlobalTheory.SplitScalar.isHalf_nsmul huh k)
          rwa [add_sub_cancel_right] at this)
        simp only [coef, if_neg htt, if_neg h2]
    · have htt : IsHalf a t := by
        by_contra hn
        exact ht (by simp only [coef, if_neg hn])
      refine hsupp ℓ hℓ t htt ?_
      simpa only [coef, if_pos htt] using ht
  obtain ⟨R, hR, hRm⟩ := GlobalTheory.DiagLiftFix.half_finite_mod (S := S) (T := T) hS.1.fg hT.1.fg ha.1 (k * k)
    (Nat.mul_pos hk hk)
  have tf : Function.Injective fun t : WO S T => k • t := fun x y hxy => by
    rw [← GlobalTheory.PlaceModel.inv_smul_nsmul S T hk x, ← GlobalTheory.PlaceModel.inv_smul_nsmul S T hk y]
    exact congrArg _ hxy
  have hP : ((fun t : WO S T => k • t) ⁻¹' R).Finite := hR.preimage tf.injOn
  refine ⟨⟨k, hk, fun u hu _ => hinv u hu, hsupp⟩, hcoef, hP.toFinset.filter (fun x => IsHalf a x),
    fun x hx => (Finset.mem_filter.1 hx).2, fun x hx => ?_⟩
  by_cases hkx : k • x ∈ latH S T ΛS ΛT
  · right
    obtain ⟨r, hr, u, hu, e⟩ := hRm (k • x)
      ⟨hkx, (GlobalTheory.PlaceModel.isHalf_iff S T).1 (GlobalTheory.SplitScalar.isHalf_nsmul hx k)⟩
    have huh : IsHalf a u := (GlobalTheory.PlaceModel.isHalf_iff S T).2 hu.2
    have hxu : IsHalf a (x - k • u) := GlobalTheory.SplitScalar.isHalf_sub hx (GlobalTheory.SplitScalar.isHalf_nsmul huh k)
    refine ⟨x - k • u, Finset.mem_filter.2 ⟨hP.mem_toFinset.2 ?_, hxu⟩, ?_⟩
    · show k • (x - k • u) ∈ R
      rwa [smul_sub, e, smul_smul, add_sub_cancel_right]
    · conv_lhs => rw [show x = (x - k • u) + k • u by abel]
      rw [GlobalTheory.SplitScalar.heisO_add_of_orth ψ S T
        (GlobalTheory.SplitScalar.half_orth ha hxu (GlobalTheory.SplitScalar.isHalf_nsmul huh k)), hinv u hu.1]
  · left
    intro ℓ hℓ
    by_contra hne
    exact hkx (hsupp ℓ hℓ x hx hne)

end GlobalTheory.DownLift.SplitCoef

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaCoefficientIsSchwartzBruhatUniformSplitStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaCoefficient_isSchwartzBruhat_uniform_split : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ a : AE D, IsSplitIdem D a → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → (∃ k : ℕ, 0 < k ∧ (∀ u ∈ latH S T ΛS ΛT, IsHalf a u ∨ IsHalf (cA D a) u → heisO ψ S T (k • u) f = f) ∧ ∀ ℓ, InvForm ψ S T a ℓ → ∀ x, IsHalf a x → ℓ (heisO ψ S T x f) ≠ 0 → k • x ∈ latH S T ΛS ΛT) ∧ (∀ ℓ, InvForm ψ S T a ℓ → IsSBHalf a (latH S T ΛS ΛT) (coef ψ S T a ℓ f)) ∧ ∃ X : Finset (WO S T), (∀ x ∈ X, IsHalf a x) ∧ ∀ x, IsHalf a x → (∀ ℓ, InvForm ψ S T a ℓ → ℓ (heisO ψ S T x f) = 0) ∨ ∃ x₁ ∈ X, heisO ψ S T x f = heisO ψ S T x₁ f := by
  first | exact @GlobalTheory.DownLift.SplitCoef.coef_isSBHalf_uniform | exact GlobalTheory.DownLift.SplitCoef.coef_isSBHalf_uniform | (intros; apply GlobalTheory.DownLift.SplitCoef.coef_isSBHalf_uniform <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteAdeleCMMemIntegralOfIdempotent
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteAdeleCMMemIntegralOfIdempotent
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.IdemFin

theorem toEAf_mem_intAf_of_idem : ∀ {D : D7} {e : AE D}, e * e = e → toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  intro D e he
  have h1 : finPart D e * finPart D e = finPart D e := by rw [← map_mul, he]
  exact GlobalTheory.LevSplit.swapAE_int (GlobalTheory.AdIdem.idempotent_mem_intAE D _ h1)

end GlobalTheory.IdemFin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteAdeleCMMemIntegralOfIdempotentStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteAdeleCM_mem_integral_of_idempotent : ∀ {D : D7} {e : AE D}, e * e = e → toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  first | exact @GlobalTheory.IdemFin.toEAf_mem_intAf_of_idem | exact GlobalTheory.IdemFin.toEAf_mem_intAf_of_idem | (intros; apply GlobalTheory.IdemFin.toEAf_mem_intAf_of_idem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CurveOverOfRayIn
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.TwistRat.Field

theorem curveOver_of_rayIn : GlobalTheory.Published.RayClassFieldSt → ∀ (D : D7) (Q : Par D), Q.PinHost → ∀ (N : ℕ), 3 ≤ N →
    ∀ (Fc : IntermediateField ℚ ℂ) (σ : Fc →+* ℂ), RayIn D N σ.fieldRange → GlobalTheory.CompRat.CurveOver Q.H Fc N := by
  intro _ D Q hP N hN Fc σ hray
  obtain ⟨L, _, _, _, _, hL, j, -, hjv⟩ := hray

  have hC : GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField (algebraMap D.host.K L) N :=
    GlobalTheory.FieldSize.RayNorm.containsRayField_of_ray N hL.1 fun I hI hc => (hL.2.2 I hI hc).1

  let S : IntermediateField ℚ ℂ := σ.toRatAlgHom.fieldRange
  let e : Fc ≃ₐ[ℚ] S := AlgEquiv.ofInjectiveField σ.toRatAlgHom
  have hS : ∀ x, j x ∈ S := fun x => by
    obtain ⟨y, hy⟩ := hjv x
    exact ⟨y, hy⟩
  let j' : L →+* S := j.codRestrict S hS
  let ψ : L →+* ℂ := (algebraMap Fc ℂ).comp (((e.symm : S ≃+* Fc) : S →+* Fc).comp j')
  have hψ : ψ.toRatAlgHom.fieldRange ≤ Fc := by
    rintro _ ⟨x, rfl⟩
    exact (e.symm (j' x)).2

  have hsq : ∃ a : D.host.K, a ^ 2 = -(Q.H.d : D.host.K) := by
    refine ⟨⟨D.host.sqrtMinusD, Formalism.L2.Pj.LPb.sqrtMinusD_mem_K D⟩, ?_⟩
    rw [hP.1]
    apply Subtype.ext
    have hb : D.host.sqrtMinusD ^ 2 = -(D.host.d : D.host.E) := D.host.sqrtMinusD_sq
    simpa using hb
  obtain ⟨hW, hrt⟩ := GlobalTheory.FieldSize.WeberTransport.weberIn_of_containsRayField D.host.E Q.H D.host.K L
    (algebraMap D.host.K L) ψ (Formalism.L2.Pj.LPb.finrank_K D) hsq N hN hC
  refine (GlobalTheory.FinalJoin.CurveField.curveOver_of_weberIn D.host.E Q.H Fc N (by omega)).1 (hψ hrt) fun Λ hΛ => ?_
  obtain ⟨h1, h2⟩ := hW Λ hΛ
  exact ⟨hψ h1, fun s hs => hψ (h2 s hs)⟩

end GlobalTheory.TwistRat.Field
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsDetRootFinPartOne
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistFinPart

theorem eq_one_of_finPart_eq_one (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (h : ChrEq c χ)
    {n : ℕ} (hn : 0 < n) (ho : χ.OrderDvd n) (x : (AE D)ˣ) (hx : finPart D (x : AE D) = 1) : c x = 1 := by
  have key := GlobalTheory.HeckeFinTrivial.eq_one_of_trivial_on_finite D (c ^ n)
    ⟨h.1.1.pow n, fun x => by rw [MonoidHom.pow_apply, h.1.2 x, one_pow]⟩
    (GlobalTheory.CharOrderFin.char_pow_eq_one_of_orderDvd D c χ h n ho)
  obtain ⟨y, rfl⟩ := GlobalTheory.IdeleDiv.exists_pow_eq_of_finPart_eq_one D n hn x hx
  rw [map_pow]
  exact key y

theorem isDetRoot_mul' {D : D7} (V : HSp D) (g g' : GA D V) (x x' : (AE D)ˣ) (hx : IsDetRoot V g x)
    (hx' : IsDetRoot V g' x') : IsDetRoot V (g * g') (x * x') := by
  unfold IsDetRoot at *
  rw [Units.val_mul, (matHom V).map_mul, Units.val_mul, Matrix.det_mul, RingHom.map_mul]
  conv_lhs => rw [hx, hx']
  ring

theorem exists_isDetRoot_finPart_one {D : D7} (V : HSp D) (a : GA D V) (ha : finHom V a = 1) (z : (AE D)ˣ)
    (hz : IsDetRoot V a z) : ∃ y : (AE D)ˣ, finPart D (y : AE D) = 1 ∧ IsDetRoot V a y := by
  obtain ⟨y, hyi, hyf⟩ := GlobalTheory.PlaceIdem.parts_surj D (infPart D (z : AE D)) 1
  obtain ⟨y', hyi', hyf'⟩ := GlobalTheory.PlaceIdem.parts_surj D (infPart D ((z⁻¹ : (AE D)ˣ) : AE D)) 1
  have hyy : y * y' = 1 := GlobalTheory.PlaceIdem.parts_inj D _ _
    (by rw [RingHom.map_mul, hyi, hyi', ← RingHom.map_mul, Units.mul_inv, RingHom.map_one])
    (by rw [RingHom.map_mul, hyf, hyf', mul_one, RingHom.map_one])
  have hc : ∀ w : AE D, infPart D (sigR (AF D.host.F) D.sp.cm.sig w) =
      sigR (Ainf D.host.F) D.sp.cm.sig (infPart D w) := fun w => GlobalTheory.PlaceIdem.infPart_cA D w
  have hf : ∀ w : AE D, finPart D (sigR (AF D.host.F) D.sp.cm.sig w) =
      sigR (Af D.host.F) D.sp.cm.sig (finPart D w) := fun w => GlobalTheory.PlaceIdem.finPart_cA D w
  have e2 : finPart D (matHom V a).1.det = 1 := by
    have e : finPart D (matHom V a).1.det = (finHom V a).1.det := (finPart D).map_det _
    rw [e, ha]
    simp
  refine ⟨⟨y, y', hyy, by rw [mul_comm]; exact hyy⟩, hyf, ?_⟩
  show y = (matHom V a).1.det * sigR (AF D.host.F) D.sp.cm.sig y
  refine GlobalTheory.PlaceIdem.parts_inj D _ _ ?_ ?_
  · have h1 := congrArg (infPart D) hz
    unfold IsDetRoot at h1
    rw [RingHom.map_mul, hc] at h1
    rw [RingHom.map_mul, hc, hyi]
    exact h1
  · rw [RingHom.map_mul, hf, hyf, e2, RingHom.map_one, one_mul]

theorem eq_of_finHom_of_triv {D : D7} (V : HSp D) (χ : (AE D)ˣ →* Circle)
    (hχ : ∀ y : (AE D)ˣ, finPart D (y : AE D) = 1 → χ y = 1) (dd : GA D V → ℂ) (hd : MuVal V χ dd)
    (h h' : GA D V) (hh : finHom V h = finHom V h') : dd h = dd h' := by
  have ha : finHom V (h⁻¹ * h') = 1 := by rw [map_mul, map_inv, hh, inv_mul_cancel]
  obtain ⟨x, hx⟩ := hd.1 h
  obtain ⟨z, hz⟩ := hd.1 (h⁻¹ * h')
  obtain ⟨y, hy1, hy⟩ := exists_isDetRoot_finPart_one V _ ha z hz
  have hxy := isDetRoot_mul' V h (h⁻¹ * h') x y hx hy
  rw [mul_inv_cancel_left] at hxy
  rw [hd.2 h x hx, hd.2 h' _ hxy, map_mul, hχ y hy1, mul_one]

theorem twist_eq_of_finHom : ∀ (D : D7) (V : HSp D) (pd : ℕ) (k : Type) [Field k] (σ : k →+* ℂ)
    (δ : Formalism.L2.Host.HChar D.host.E) (δc : (AE D)ˣ →* Circle), IsTwist pd σ δ δc → ∀ dd : GA D V → ℂ,
    (MuVal V δc dd ∨ MuVal V δc⁻¹ dd) → ∀ h h' : GA D V, finHom V h = finHom V h' → dd h = dd h' := by
  intro D V pd k _ σ δ δc hT dd hdd h h' hh
  obtain ⟨hc, ⟨n, hn, ho⟩, -⟩ := hT
  have h1 : ∀ y : (AE D)ˣ, finPart D (y : AE D) = 1 → δc y = 1 := eq_one_of_finPart_eq_one D δc δ hc hn ho
  rcases hdd with hd | hd
  · exact eq_of_finHom_of_triv V δc h1 dd hd h h' hh
  · exact eq_of_finHom_of_triv V δc⁻¹ (fun y hy => by rw [MonoidHom.inv_apply, h1 y hy, inv_one]) dd hd h h' hh

end GlobalTheory.TwistFinPart
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIdempotentPlaceChartFiniteAdeles
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIdempotentPlaceChartFiniteAdeles
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef

namespace GlobalTheory.DownLift.SplitCoef

variable {D : D7}

theorem toEAf_idem_mul_eq_zero {e : AE D} (he : IsSplitIdem D e) (a : AE D) :
    toEAf D (e * a) = 0 ↔ e * a = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, map_zero]⟩
  apply GlobalTheory.SplitScalar.adele_ext
  · rw [map_mul, GlobalTheory.SplitScalar.infPart_splitIdem he, zero_mul, map_zero]
  · rw [map_zero]
    change (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E) (finPart D (e * a)) = 0 at h
    exact (map_eq_zero_iff _ (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).injective).1 h

theorem residue_eq_zero_iff_val_lt {v : HeightOneSpectrum (𝓞 D.host.F)} (o : GlobalTheory.SplitHecke.Ov D v) :
    IsLocalRing.residue (GlobalTheory.SplitHecke.Ov D v) o = 0 ↔ Valued.v (o : Fv D.host.F v) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
  exact ⟨fun h => lt_of_le_of_ne o.2 h, fun h => h.ne⟩


set_option maxHeartbeats 1000000 in
theorem exists_levChart : ∀ (D : D7) (e : AE D) (PP : Pl D.host.E), Formalism.L2.NTheta.IsIdemAt e PP →
    ∃ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : Formalism.IndefR.Lev.EAf D →+* Fv D.host.F v)
      (ι : kP PP ≃+* IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v)), LevChart e PP v φ ι := by
  intro D e PP he
  obtain ⟨v, π, hπ⟩ := GlobalTheory.SplitChart.exists_chart e he.1
  obtain ⟨φ, hφ, hres⟩ := GlobalTheory.ThetaSupport.exists_chart_levels he hπ
  obtain ⟨hi, hi1⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D e PP he
  have hπe : π e = 1 := by
    have h0 : π (1 - e) = 0 := (hπ.2.1 _).2 (by rw [mul_sub, mul_one, he.1.1, sub_self])
    rw [map_sub, map_one, sub_eq_zero] at h0
    exact h0.symm
  have hint_iff : ∀ a : AE D, toEAf D (e * a) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔
      π a ∈ v.adicCompletionIntegers D.host.F := by
    intro a
    rw [← GlobalTheory.SplitHecke.isInt_Ov, ← hπ.2.2.2 a]
    exact ⟨GlobalTheory.PlaceDatum.finPart_mem_of_toEAf, GlobalTheory.IdemRes.toEAf_mem_of_finPart⟩
  have hsurj : Function.Surjective φ := fun y => by
    obtain ⟨a, ha⟩ := hπ.1 y
    exact ⟨toEAf D a, by rw [hφ, ha]⟩
  have hint : ∀ s : Formalism.L2.Herm.intAf D.host.F D.host.E, φ s ∈ v.adicCompletionIntegers D.host.F := by
    intro s
    obtain ⟨a, ha⟩ := GlobalTheory.AdjDatumNe.toEAf_surjective (D := D) (s : Formalism.IndefR.Datum.EAf D)
    rw [← ha, hφ, ← hint_iff, map_mul, ha]
    exact mul_mem hi s.2
  let g : Formalism.L2.Herm.intAf D.host.F D.host.E →+* IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v) :=
    (IsLocalRing.residue (GlobalTheory.SplitHecke.Ov D v)).comp
      ((φ.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype).codRestrict (v.adicCompletionIntegers D.host.F) hint)
  have hg : ∀ s, g s = IsLocalRing.residue (GlobalTheory.SplitHecke.Ov D v) ⟨φ s, hint s⟩ := fun s => rfl
  have hrsurj : Function.Surjective (resS D.host.F PP) := fun q => by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
    exact ⟨_, resS_oToS PP x⟩
  have hker : RingHom.ker (resS D.host.F PP) ≤ RingHom.ker g := fun s hs => by
    rw [RingHom.mem_ker] at hs ⊢
    rw [hg, residue_eq_zero_iff_val_lt]
    exact hres s hs
  let ι₀ : kP PP →+* IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v) :=
    RingHom.liftOfRightInverse (resS D.host.F PP) (Function.surjInv hrsurj) (Function.rightInverse_surjInv hrsurj) ⟨g, hker⟩
  have hι₀ : ∀ s, ι₀ (resS D.host.F PP s) = g s := fun s =>
    RingHom.liftOfRightInverse_comp_apply _ _ _ _ s
  haveI := PP.isMaximal
  letI : Field (kP PP) := Ideal.Quotient.field PP.asIdeal
  have hbij : Function.Bijective ι₀ := by
    refine ⟨RingHom.injective ι₀, fun r => ?_⟩
    obtain ⟨o, rfl⟩ := IsLocalRing.residue_surjective r
    obtain ⟨z, hz⟩ := hsurj (o : Fv D.host.F v)
    obtain ⟨a, rfl⟩ := GlobalTheory.AdjDatumNe.toEAf_surjective (D := D) z
    have hm : toEAf D e * toEAf D a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
      rw [← map_mul, hint_iff, ← hφ, hz]
      exact o.2
    refine ⟨resS D.host.F PP ⟨_, hm⟩, ?_⟩
    rw [hι₀, hg]
    congr 1
    apply Subtype.ext
    show φ (toEAf D e * toEAf D a) = (o : Fv D.host.F v)
    rw [map_mul, hz, hφ e, hπe, one_mul]
  refine ⟨v, φ, RingEquiv.ofBijective ι₀ hbij, hsurj, fun z => ?_, fun z => ?_, fun s o ho => ?_⟩
  · obtain ⟨a, rfl⟩ := GlobalTheory.AdjDatumNe.toEAf_surjective (D := D) z
    rw [hφ, hπ.2.1, ← map_mul, toEAf_idem_mul_eq_zero he.1]
  · obtain ⟨a, rfl⟩ := GlobalTheory.AdjDatumNe.toEAf_surjective (D := D) z
    rw [← map_mul, hint_iff, hφ]
  · change ι₀ (resS D.host.F PP s) = _
    rw [hι₀, hg]
    congr 1
    exact Subtype.ext ho.symm

end GlobalTheory.DownLift.SplitCoef
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIdempotentPlaceChartFiniteAdelesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_idempotentPlaceChart_finiteAdeles : ∀ (D : D7) (e : AE D) (PP : Pl D.host.E), Formalism.L2.NTheta.IsIdemAt e PP → ∃ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : Formalism.IndefR.Lev.EAf D →+* Fv D.host.F v) (ι : kP PP ≃+* IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v)), LevChart e PP v φ ι := by
  first | exact @GlobalTheory.DownLift.SplitCoef.exists_levChart | exact GlobalTheory.DownLift.SplitCoef.exists_levChart | (intros; apply GlobalTheory.DownLift.SplitCoef.exists_levChart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceChartFiniteAdeleTensorLevels
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceChartFiniteAdeleTensorLevels
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.L2.NTheta (IsIdemAt IsHeckeElt)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChartLevels

theorem linIndep_rows_iff_map {k₁ k₂ : Type} [Field k₁] [Field k₂] (ι : k₁ →+* k₂) {m n : ℕ}
    (y : Matrix (Fin m) (Fin n) k₁) :
    LinearIndependent k₁ y.row ↔ LinearIndependent k₂ (y.map ι).row := by
  have key : ∀ {k : Type} [Field k] (y : Matrix (Fin m) (Fin n) k),
      LinearIndependent k y.row ↔ ∀ c : Fin m → k, c ᵥ* y = 0 → c = 0 := by
    intro k _ y
    rw [Fintype.linearIndependent_iff]
    have h : ∀ c : Fin m → k, ∑ i, c i • y.row i = c ᵥ* y := fun c => by
      ext j
      simp [Matrix.vecMul, dotProduct, Finset.sum_apply]
    simp only [h]
    exact ⟨fun H c hc => funext (H c hc), fun H c hc i => congrFun (H c hc) i⟩
  have inv : ∀ {k : Type} [Field k] (y : Matrix (Fin m) (Fin n) k),
      LinearIndependent k y.row → ∃ B : Matrix (Fin n) (Fin m) k, y * B = 1 := by
    intro k _ y hy
    rw [key] at hy
    obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.vecMulLinear y)
      (LinearMap.ker_eq_bot.2 fun a b hab => sub_eq_zero.1 (hy _ (by
        rw [Matrix.sub_vecMul]
        exact sub_eq_zero.2 hab)))
    refine ⟨(LinearMap.toMatrix' g)ᵀ, ?_⟩
    have hc : ∀ c : Fin m → k, c ᵥ* (y * (LinearMap.toMatrix' g)ᵀ) = c := fun c => by
      rw [← Matrix.vecMul_vecMul, Matrix.vecMul_transpose, LinearMap.toMatrix'_mulVec]
      exact congrArg (fun f => f c) hg
    refine Matrix.ext fun i j => ?_
    have := congrFun (hc (Pi.single i 1)) j
    rw [Matrix.single_one_vecMul] at this
    rw [Matrix.row_apply] at this
    rw [this, Matrix.one_apply, Pi.single_apply]
    simp only [eq_comm]
  constructor
  · intro hy
    obtain ⟨B, hB⟩ := inv y hy
    rw [key]
    intro c hc
    have : c ᵥ* ((y.map ι) * B.map ι) = c := by
      rw [← Matrix.map_mul, hB, Matrix.map_one _ ι.map_zero ι.map_one, Matrix.vecMul_one]
    rw [← Matrix.vecMul_vecMul, hc, Matrix.zero_vecMul] at this
    exact this.symm
  · intro hy
    rw [key] at hy ⊢
    intro c hc
    have h1 := hy (ι ∘ c) (funext fun j => by
      rw [← RingHom.map_vecMul, hc]
      simp)
    funext i
    exact ι.injective ((congrFun h1 i).trans ι.map_zero.symm)

variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)}

theorem residue_eq_zero_iff (x : GlobalTheory.SplitHecke.Ov D v) :
    IsLocalRing.residue (GlobalTheory.SplitHecke.Ov D v) x = 0 ↔ Valued.v (x : Fv D.host.F v) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  have hx : Valued.v (x : Fv D.host.F v) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 x.2
  constructor
  · intro hnu
    refine lt_of_le_of_ne hx fun h1 => hnu ?_
    have h0 : (x : Fv D.host.F v) ≠ 0 := fun h => by
      rw [h, map_zero] at h1
      exact zero_ne_one h1
    have hmem : (x : Fv D.host.F v)⁻¹ ∈ v.adicCompletionIntegers D.host.F :=
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (by rw [map_inv₀, h1, inv_one])
    refine IsUnit.of_mul_eq_one (a := x) ⟨_, hmem⟩ (Subtype.ext ?_)
    show (x : Fv D.host.F v) * (x : Fv D.host.F v)⁻¹ = 1
    exact mul_inv_cancel₀ h0
  · intro hlt hu
    obtain ⟨w, hw⟩ := hu.exists_right_inv
    have h2 := congrArg (fun t : GlobalTheory.SplitHecke.Ov D v => Valued.v (t : Fv D.host.F v)) hw
    have hw1 : Valued.v (w : Fv D.host.F v) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 w.2
    simp only [MulMemClass.coe_mul, map_mul, OneMemClass.coe_one, map_one] at h2
    have : Valued.v (x : Fv D.host.F v) * Valued.v (w : Fv D.host.F v) < 1 :=
      (mul_le_of_le_one_right' hw1).trans_lt hlt
    rw [h2] at this
    exact lt_irrefl _ this

theorem resS_surjective (PP : Pl D.host.E) : Function.Surjective (resS D.host.F PP) := by
  rw [resS, RingHom.coe_comp]
  exact (RingEquiv.surjective _).comp Ideal.Quotient.mk_surjective

end GlobalTheory.ChartLevels

namespace GlobalTheory.ChartLevels

theorem prim_map_eq {k₁ k₂ : Type} [Field k₁] [Field k₂] (ι : k₁ →+* k₂) {m n : ℕ}
    (y : Matrix (Fin m) (Fin n) k₁) : prim (y.map ι) = prim y := by
  unfold prim
  by_cases h : LinearIndependent k₁ y.row
  · rw [if_pos h, if_pos ((linIndep_rows_iff_map ι y).1 h)]
  · rw [if_neg h, if_neg (mt (linIndep_rows_iff_map ι y).2 h)]

theorem gl_map_inv_val {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {n : ℕ} (β : GL (Fin n) R) :
    ((Matrix.GeneralLinearGroup.map f β)⁻¹).1 = (β⁻¹).1.map f := by
  rw [← map_inv]
  rfl

end GlobalTheory.ChartLevels

namespace GlobalTheory.ChartLevels

theorem frame_of_baseFrame {D : D7} {e : AE D} {v : HeightOneSpectrum (𝓞 D.host.F)} {π : AE D →+* Fv D.host.F v}
    (φ : Datum.EAf D →+* Fv D.host.F v) (hφ : ∀ a, φ (toEAf D a) = π a)
    (hint : ∀ N : Datum.EAf D, toEAf D e * N ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔
      GlobalTheory.SplitHecke.IsInt (GlobalTheory.SplitHecke.Ov D v) (φ N))
    (V : HSp D) (β : GL (Fin V.rank) (Datum.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hβ : Lev.IsBaseFrame V β Λ 1) : GlobalTheory.SplitHecke.Frame V e π (Matrix.GeneralLinearGroup.map φ β) := by
  intro y
  have hL := (GlobalTheory.FinAdIdent.lamHat_good hβ (f := 1) ⟨mul_one 1, 1, by simp⟩).2
  have hL' : ∀ x, x ∈ Formalism.L2.NTheta.LamHat V ↔ (fun a => Lev.swapAE D (x a)) ∈ Formalism.L2.Herm.hatL Λ :=
    fun x => by simpa only [one_smul, one_mul] using hL x
  refine (hL' _).trans ((hβ.1 _).trans (forall_congr' fun i => ?_))
  have e2 : (fun a => Lev.swapAE D (finPart D (e * y a))) = toEAf D e • (fun a => toEAf D (y a)) := by
    funext a
    rw [Pi.smul_apply, smul_eq_mul, ← RingHom.map_mul]
    rfl
  have e4 : (φ ∘ fun a => toEAf D (y a)) = fun k => π (y k) := funext fun k => hφ (y k)
  rw [e2, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, hint, RingHom.map_mulVec, e4, gl_map_inv_val]

end GlobalTheory.ChartLevels

namespace GlobalTheory.ChartLevels

theorem chart_levels : ∀ (D : D7) (e : AE D) (P : Pl D.host.E) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), IsIdemAt e P → GlobalTheory.SplitHecke.Chart e v π → ∃ φ : Datum.EAf D →+* Fv D.host.F v, (∀ a, φ (toEAf D a) = π a) ∧ (∀ N : Datum.EAf D, toEAf D e * N ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ GlobalTheory.SplitHecke.IsInt (GlobalTheory.SplitHecke.Ov D v) (φ N)) ∧ (∀ (m n : ℕ) (N : Matrix (Fin m) (Fin n) (Datum.EAf D)), IsIntM N → ∀ z : Matrix (Fin m) (Fin n) (GlobalTheory.SplitHecke.Ov D v), z.map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)) = N.map φ → prim (redM P N) = prim (z.map (IsLocalRing.residue (GlobalTheory.SplitHecke.Ov D v)))) ∧ ∀ (V : HSp D) (β : GL (Fin V.rank) (Datum.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), Lev.IsBaseFrame V β Λ 1 → GlobalTheory.SplitHecke.Frame V e π (Matrix.GeneralLinearGroup.map φ β) := by
  intro D e P v π he hπ
  obtain ⟨φ, hφ, hres⟩ := GlobalTheory.ThetaSupport.exists_chart_levels he hπ
  obtain ⟨hi, -⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D e P he
  have hπe : π e = 1 := hπ.map_e he.1.1
  have hint : ∀ N : Datum.EAf D, toEAf D e * N ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔
      GlobalTheory.SplitHecke.IsInt (GlobalTheory.SplitHecke.Ov D v) (φ N) := by
    intro N
    obtain ⟨a, rfl⟩ := GlobalTheory.AdjDatumNe.toEAf_surjective (D := D) N
    rw [hφ, ← (hπ.2.2.2 a), ← RingHom.map_mul]
    exact ⟨GlobalTheory.PlaceDatum.finPart_mem_of_toEAf, GlobalTheory.IdemRes.toEAf_mem_of_finPart⟩
  refine ⟨φ, hφ, hint, ?_, ?_⟩
  · have hR : ∀ s : Formalism.L2.Herm.intAf D.host.F D.host.E, φ s ∈ v.adicCompletionIntegers D.host.F := fun s =>
      GlobalTheory.SplitHecke.isInt_Ov.1 ((hint s).1 (mul_mem hi s.2))
    let φR : Formalism.L2.Herm.intAf D.host.F D.host.E →+* GlobalTheory.SplitHecke.Ov D v :=
      (φ.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype).codRestrict (v.adicCompletionIntegers D.host.F) hR
    let ρ : Formalism.L2.Herm.intAf D.host.F D.host.E →+* IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v) :=
      (IsLocalRing.residue _).comp φR
    have hker : RingHom.ker (resS D.host.F P) ≤ RingHom.ker ρ := by
      intro s hs
      rw [RingHom.mem_ker] at hs ⊢
      exact (residue_eq_zero_iff (φR s)).2 (hres s hs)
    let ι : kP P →+* IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v) :=
      (resS D.host.F P).liftOfRightInverse _ (Function.rightInverse_surjInv (resS_surjective P)) ⟨ρ, hker⟩
    have hι : ∀ s, ι (resS D.host.F P s) = ρ s := fun s =>
      RingHom.liftOfRightInverse_comp_apply _ _ _ _ s
    intro m n N hN z hz
    have e1 : z.map (IsLocalRing.residue (GlobalTheory.SplitHecke.Ov D v)) = (redM P N).map ι := by
      ext i j
      have hzij : z i j = φR ⟨N i j, hN i j⟩ := Subtype.ext (congrFun (congrFun hz i) j)
      simp only [Matrix.map_apply, redM, dif_pos (hN i j), hι, hzij]
      rfl
    rw [e1]
    exact (prim_map_eq ι _).symm
  · exact frame_of_baseFrame φ hφ hint

end GlobalTheory.ChartLevels
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceChartFiniteAdeleTensorLevelsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.L2.NTheta (IsIdemAt IsHeckeElt)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlaceChart_finiteAdeleTensor_levels : ∀ (D : D7) (e : AE D) (P : Pl D.host.E) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), IsIdemAt e P → GlobalTheory.SplitHecke.Chart e v π → ∃ φ : Datum.EAf D →+* Fv D.host.F v, (∀ a, φ (toEAf D a) = π a) ∧ (∀ N : Datum.EAf D, toEAf D e * N ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ GlobalTheory.SplitHecke.IsInt (GlobalTheory.SplitHecke.Ov D v) (φ N)) ∧ (∀ (m n : ℕ) (N : Matrix (Fin m) (Fin n) (Datum.EAf D)), IsIntM N → ∀ z : Matrix (Fin m) (Fin n) (GlobalTheory.SplitHecke.Ov D v), z.map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)) = N.map φ → prim (redM P N) = prim (z.map (IsLocalRing.residue (GlobalTheory.SplitHecke.Ov D v)))) ∧ ∀ (V : HSp D) (β : GL (Fin V.rank) (Datum.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), Lev.IsBaseFrame V β Λ 1 → GlobalTheory.SplitHecke.Frame V e π (Matrix.GeneralLinearGroup.map φ β) := by
  first | exact @GlobalTheory.ChartLevels.chart_levels | exact GlobalTheory.ChartLevels.chart_levels | (intros; apply GlobalTheory.ChartLevels.chart_levels <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeStableUnderAction
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.LatKeep

variable {D : D7}

theorem intGL_mulVec_int {n : ℕ} (y : GL (Fin n) (Formalism.L2.Herm.intAf D.host.F D.host.E)) (v : Fin n → EAf D)
    (hv : ∀ i, v i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (i : Fin n) :
    (((Formalism.L2.DIV.intGL D.host.F D.host.E n y : GL (Fin n) (EAf D)) : Matrix (Fin n) (Fin n) (EAf D)) *ᵥ v) i ∈
      Formalism.L2.Herm.intAf D.host.F D.host.E := by
  simp only [Matrix.mulVec, dotProduct]
  refine sum_mem fun j _ => mul_mem ?_ (hv j)
  exact (y.val i j).2

theorem isFrame_mul_intGL {n : ℕ} {β : GL (Fin n) (EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    (hβ : Formalism.L2.DIV.IsFrame β Λ) (y : GL (Fin n) (Formalism.L2.Herm.intAf D.host.F D.host.E)) :
    Formalism.L2.DIV.IsFrame (β * Formalism.L2.DIV.intGL D.host.F D.host.E n y) Λ := by
  intro x
  rw [hβ x]
  have e1 : (((β * Formalism.L2.DIV.intGL D.host.F D.host.E n y)⁻¹ : GL (Fin n) (EAf D)) : Matrix (Fin n) (Fin n) (EAf D)) *ᵥ x
      = ((Formalism.L2.DIV.intGL D.host.F D.host.E n y⁻¹ : GL (Fin n) (EAf D)) : Matrix (Fin n) (Fin n) (EAf D)) *ᵥ
          (((β⁻¹ : GL (Fin n) (EAf D)) : Matrix (Fin n) (Fin n) (EAf D)) *ᵥ x) := by
    have hm : (β * Formalism.L2.DIV.intGL D.host.F D.host.E n y)⁻¹ = Formalism.L2.DIV.intGL D.host.F D.host.E n y⁻¹ * β⁻¹ := by
      rw [_root_.mul_inv_rev, MonoidHom.map_inv]
    rw [hm, Units.val_mul, Matrix.mulVec_mulVec]
  have e2 : ((β⁻¹ : GL (Fin n) (EAf D)) : Matrix (Fin n) (Fin n) (EAf D)) *ᵥ x
      = ((Formalism.L2.DIV.intGL D.host.F D.host.E n y : GL (Fin n) (EAf D)) : Matrix (Fin n) (Fin n) (EAf D)) *ᵥ
          ((((β * Formalism.L2.DIV.intGL D.host.F D.host.E n y)⁻¹ : GL (Fin n) (EAf D)) : Matrix (Fin n) (Fin n) (EAf D)) *ᵥ x) := by
    rw [e1, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one,
      Matrix.one_mulVec]
  constructor
  · intro h i
    rw [e1]
    exact intGL_mulVec_int _ _ h i
  · intro h i
    rw [e2]
    exact intGL_mulVec_int _ _ h i

end GlobalTheory.LatKeep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PureTensorOTransSumLin
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.SingleDatum

theorem pureTensorO_finsetSum {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) {ι : Type} (s : Finset ι) (a : ι → ℂ)
    (g : ι → WO S T → ℂ) (hg : ∀ i, IsThetaFunO ψ S T (g i)) (φ : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    IsThetaFunO ψ S T (∑ i ∈ s, a i • g i) ∧
      pureTensorO ψ θ S T sS sT BS BT (∑ i ∈ s, a i • g i) φ =
        ∑ i ∈ s, a i • pureTensorO ψ θ S T sS sT BS BT (g i) φ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    exact ⟨GlobalTheory.OrientedHeis.theta_zero, GlobalTheory.FockFiniteHeis.pureTensorO_zero ψ θ S T hψ hθ sS BS sT BT φ⟩
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    refine ⟨GlobalTheory.OrientedHeis.theta_add (GlobalTheory.OrientedHeis.theta_smul _ (hg i)) ih.1, ?_⟩
    rw [GlobalTheory.FockFiniteHeis.pureTensorO_lin ψ θ S T hψ hθ sS BS sT BT (a i) (hg i) ih.1 φ, ih.2]

theorem pureTensorO_transSum_lin : ∀ (D : D7) (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW s f₀ → ∀ (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) (l₂ : Geo.Tor.Level H) (e : AE D), IsHalfIdem l₂ e → ∀ [Fintype (Fin V.rank → LevQ Dw l₂)] (BV : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (BW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (w : (Fin V.rank → LevQ Dw l₂) → ℂ) (P : PolF D W.rank V.rank), pureTensorO ψ θ V W (fun _ => 1) s BV BW (transSum ψ V W l₂ ι e f₀ w) P = ∑ q, w q • pureTensorO ψ θ V W (fun _ => 1) s BV BW (transSum ψ V W l₂ ι e f₀ (fun q' => if q' = q then 1 else 0)) P := by
  intro D H Dw ψ θ V W χV χW om ΛV ΛW s f₀ hv ι l₂ e he _ BV BW w P
  have hψ : IsStdChar D ψ (-1) := hv.2.2.2.2.2.2.2.2.1
  have hθ : IsInfFam θ := hv.1.inf
  have hf₀ : IsThetaFunO ψ V W f₀ := hv.2.2.2.2.2.2.2.2.2.2
  have hinf : infPart D e = 0 := by
    obtain ⟨Q, hQ, -⟩ := he
    exact GlobalTheory.PlaceDatum.infPart_idemSum hQ
  have hpt : ∀ q, (levPoint V W l₂ ι e q).map (infPart D) = 0 := by
    intro q
    ext a b
    simp [levPoint, Matrix.map_apply, map_mul, hinf]
  have hth : ∀ q, IsThetaFunO ψ V W (heisO ψ V W (levPoint V W l₂ ι e q) f₀) := fun q =>
    ((GlobalTheory.FinTranslate.finite_translate D ψ θ V W hψ hθ f₀ hf₀).2 _ (hpt q)).1
  have key : ∀ w' : (Fin V.rank → LevQ Dw l₂) → ℂ,
      pureTensorO ψ θ V W (fun _ => 1) s BV BW (transSum ψ V W l₂ ι e f₀ w') P =
        ∑ q, (((Nat.card (Fin V.rank → LevQ Dw l₂) : ℂ))⁻¹ * w' q) •
          pureTensorO ψ θ V W (fun _ => 1) s BV BW (heisO ψ V W (levPoint V W l₂ ι e q) f₀) P := by
    intro w'
    have h1 : transSum ψ V W l₂ ι e f₀ w' = ∑ q, (((Nat.card (Fin V.rank → LevQ Dw l₂) : ℂ))⁻¹ * w' q) •
        heisO ψ V W (levPoint V W l₂ ι e q) f₀ := by
      unfold transSum
      rw [finsum_eq_sum_of_fintype, Finset.smul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [smul_smul]
    rw [h1]
    exact (pureTensorO_finsetSum hψ hθ (fun _ => 1) BV s BW Finset.univ _ _ hth P).2
  rw [key w]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [key, Finset.sum_eq_single q]
  · rw [if_pos rfl, mul_one, mul_comm, ← smul_smul]
  · intro b _ hb
    rw [if_neg hb, mul_zero, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ q) h

end GlobalTheory.SingleDatum

end
end
