module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitHeckePrimeOffLevelOfHeckeIndexPlace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLatticeStabilizerTwistAndLevelAway

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockMatrixCoefficientSplitsRealFiniteFactors
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockMatrixCoefficientSplitsRealFiniteFactors
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FockCoefSplit


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem actO_inf : ∀ (D : D7) (S T : HSp D) (a : GA D S) (b : GA D T), a ∈ GinfC S → b ∈ GinfC T →
    ∀ w : WO S T, w.map (infPart D) = 0 → actO S T a b w = w := by
  intro D S T a b ha hb w hw
  have hfb : (Formalism.L2.Theta.mt T b).map (finPart D) = 1 := by
    have h := congrArg (fun g : GL (Fin T.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) => g.val)
      (MonoidHom.mem_ker.1 hb)
    exact h
  have hfa : (Formalism.L2.Theta.mt S a⁻¹).map (finPart D) = 1 := by
    have h := congrArg (fun g : GL (Fin S.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) => g.val)
      (MonoidHom.mem_ker.1 (Subgroup.inv_mem _ ha))
    exact h
  have h0 : ∀ k j, infPart D (w k j) = 0 := fun k j => by
    have := congrFun (congrFun hw k) j
    simpa using this
  have e1 : Formalism.L2.Theta.mt T b * w = w := by
    ext i j
    refine GlobalTheory.UnitarySplit.parts_inj D _ _ ?_ ?_
    · set_option synthInstance.maxHeartbeats 100000 in
        rw [Matrix.mul_apply, map_sum]
      simp [map_mul, h0]
    · have h1 : ∀ k, finPart D (Formalism.L2.Theta.mt T b i k) = if i = k then 1 else 0 := fun k => by
        have := congrFun (congrFun hfb i) k
        simpa [Matrix.one_apply] using this
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Matrix.mul_apply, map_sum]
      simp [map_mul, h1]
  have e2 : w * Formalism.L2.Theta.mt S a⁻¹ = w := by
    ext i j
    refine GlobalTheory.UnitarySplit.parts_inj D _ _ ?_ ?_
    · set_option synthInstance.maxHeartbeats 100000 in
        rw [Matrix.mul_apply, map_sum]
      simp [map_mul, h0]
    · have h1 : ∀ k, finPart D (Formalism.L2.Theta.mt S a⁻¹ k j) = if k = j then 1 else 0 := fun k => by
        have := congrFun (congrFun hfa k) j
        simpa [Matrix.one_apply] using this
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Matrix.mul_apply, map_sum]
      simp [map_mul, h1]
  unfold actO
  rw [e1, e2]

open GlobalTheory.VacPairSchur GlobalTheory.RawLift

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

theorem om_heisO_inf {χS χT : (AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (hom : IsWeilDatumO ψ S T χS χT om) {a : GA D S} (ha : a ∈ GinfC S) {b : GA D T} (hb : b ∈ GinfC T)
    {w : WO S T} (hw : w.map (infPart D) = 0) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    om (a, b) (heisO ψ S T w f) = heisO ψ S T w (om (a, b) f) := by
  rw [hom.om_heis a b w f hf, actO_inf D S T a b ha hb w hw]

theorem fockVac_om_fin {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hom : IsWeilDatumO ψ S T χS χT om)
    (hθ : IsInfFam θ) {x : GA D S} (hx : x ∈ GfC S) {y : GA D T} (hy : y ∈ GfC T) (τ : D.what₂.Tau)
    (J : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (hv : IsFockVacAt (heisO ψ S T) θ τ J f) :
    IsFockVacAt (heisO ψ S T) θ τ J (om (x, y) f) := by
  have e : ∀ z : Matrix (Fin T.rank) (Fin S.rank) ℂ,
      compAt θ τ (Formalism.L2.Theta.mt T y) * z * compAt θ τ (Formalism.L2.Theta.mt S x⁻¹) = z := fun z => by
    rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hy, GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ (Subgroup.inv_mem _ hx),
      Matrix.one_mul, Matrix.mul_one]
  intro z
  have h := congrArg (om (x, y)) (hv z)
  unfold annih at h ⊢
  rw [map_add (f := _), map_smul, GlobalTheory.OrientedHeis.om_dRho hom hθ x y τ z hf, GlobalTheory.OrientedHeis.om_dRho hom hθ x y τ (J z) hf,
    e, e, map_zero] at h
  exact h

theorem om_fin_pureTensorO {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hom : IsWeilDatumO ψ S T χS χT om)
    (hθ : IsInfFam θ) (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) {x : GA D S} (hx : x ∈ GfC S) {y : GA D T}
    (hy : y ∈ GfC T) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (P : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    om (x, y) (pureTensorO ψ θ S T sS sT BS BT f P) = pureTensorO ψ θ S T sS sT BS BT (om (x, y) f) P :=
  (GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ S T χS χT om hom hθ sS sS BS BS sT sT BT BT x y
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hx, Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hy, Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hx, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hy, Matrix.one_mul]) f hf P).2

theorem l2_eq_star (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) (f g : WO S T → ℂ) :
    l2 μ 𝓕 f g = star (thetaIP μ 𝓕 f g) := by
  unfold l2 Formalism.IndefR.Lift.pet thetaIP
  change _ = (starRingEnd ℂ) (∫ w in 𝓕, star (f w) * g w ∂μ)
  rw [← integral_conj]
  congr 1
  funext w
  simp [mul_comm]

theorem pair_eq_inf : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → ∀ (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (pS pT : D.what₂.Tau → ℕ), (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → (∀ τ, IsONBasis (gramAt D S τ) (sS τ) (BS τ) (pS τ)) → (∀ τ, IsONBasis (gramAt D T τ) (sT τ) (BT τ) (pT τ)) → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ a ∈ GinfC S, ∀ b ∈ GinfC T, ∀ P P' : MvPolynomial (FVar D T.rank S.rank) ℂ, ∃ c : ℂ, ∀ f g : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) g) → thetaIP μ 𝓕 (om (a, b) (pureTensorO ψ θ S T sS sT BS BT f P)) (pureTensorO ψ θ S T sS sT BS BT g P') = c * thetaIP μ 𝓕 f g := by
  intro D ψ θ S T χS χT om hom hθ sS BS sT BT pS pT hcS hcT hoS hoT μ 𝓕 hcv a ha b hb P P'
  have hψ := hom.std
  have hμ := hcv.1
  have h𝓕 := hcv.2.1
  have thp : ∀ f, IsThetaFunO ψ S T f → ∀ Q, IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT f Q) :=
    fun f hf Q => GlobalTheory.Chain.InnerSteps.theta_pureTensorO hψ hθ sS BS sT BT hf Q
  have thom : ∀ f, IsThetaFunO ψ S T f → ∀ Q,
      IsThetaFunO ψ S T (om (a, b) (pureTensorO ψ θ S T sS sT BS BT f Q)) :=
    fun f hf Q => hom.om_pres _ _ (thp f hf Q)
  have key : ∀ f, IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → ∀ Q,
      thetaIP μ 𝓕 (pureTensorO ψ θ S T sS sT BS BT f Q) (pureTensorO ψ θ S T sS sT BS BT f Q) =
        GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockIp Q Q * (nrm2 μ 𝓕 f : ℂ) := by
    intro f hf vf Q
    rw [thetaIP_eq_ipO]
    exact GlobalTheory.FockIsometry.ipO_pureTensorO D ψ θ S T hψ hθ sS BS sT BT (fun τ => min (pS τ) S.rank)
      (fun τ => min (pT τ) T.rank) (fun τ => min_le_right _ _) (fun τ => min_le_right _ _) hcS hcT
      (fun τ => onb_min (hoS τ)) (fun τ => onb_min (hoT τ)) f hf vf μ 𝓕 hcv Q Q
  set Φ : (WO S T → ℂ) → (WO S T → ℂ) → ℂ := fun f g =>
    thetaIP μ 𝓕 (om (a, b) (pureTensorO ψ θ S T sS sT BS BT f P)) (pureTensorO ψ θ S T sS sT BS BT g P') with hΦ
  have hl : ∀ (z : ℂ) (f f' g : WO S T → ℂ), IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' → IsThetaFunO ψ S T g →
      (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f') → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) g) → Φ (z • f + f') g = star z * Φ f g + Φ f' g := by
    intro z f f' g hf hf' hg _ _ _
    simp only [hΦ]
    rw [pT_lin hψ hθ sS BS sT BT z hf hf' P, map_add (f := _), map_smul, thetaIP_eq_ipO, thetaIP_eq_ipO, thetaIP_eq_ipO,
      GlobalTheory.Size.ipO_add_right hψ hμ h𝓕 (thp g hg P') (GlobalTheory.OrientedHeis.theta_smul z (thom f hf P)) (thom f' hf' P),
      GlobalTheory.Size.ipO_smul_right]
    rfl
  have hr : ∀ (z : ℂ) (f g g' : WO S T → ℂ), IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → IsThetaFunO ψ S T g' →
      (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) g) → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) g') → Φ f (z • g + g') = z * Φ f g + Φ f g' := by
    intro z f g g' hf hg hg' _ _ _
    simp only [hΦ]
    rw [pT_lin hψ hθ sS BS sT BT z hg hg' P', thetaIP_eq_ipO, thetaIP_eq_ipO, thetaIP_eq_ipO,
      GlobalTheory.Size.ipO_add_left hψ hμ h𝓕 (GlobalTheory.OrientedHeis.theta_smul z (thp g hg P')) (thp g' hg' P') (thom f hf P),
      GlobalTheory.Size.ipO_smul_left]
  have hbd : ∃ C : ℝ, ∀ f g : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) g) →
      ‖Φ f g‖ ^ 2 ≤ C * (nrm2 μ 𝓕 f * nrm2 μ 𝓕 g) := by
    refine ⟨(GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockIp P P).re * (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockIp P' P').re, fun f g hf hg vf vg => ?_⟩
    simp only [hΦ]
    have h1 := cs hψ hcv (thom f hf P) (thp g hg P')
    rw [GlobalTheory.WeilPairing.thetaInner_weilRep D ψ S T χS χT om μ 𝓕 hom hcv _ _ _ (thp f hf P) (thp f hf P),
      key f hf vf P, key g hg vg P', Complex.re_mul_ofReal, Complex.re_mul_ofReal] at h1
    linarith
  have hi : ∀ w : WO S T, w.map (infPart D) = 0 → ∀ f g : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g →
      (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) g) → Φ (heisO ψ S T w f) (heisO ψ S T w g) = Φ f g := by
    intro w hw f g hf hg _ _
    simp only [hΦ]
    rw [pT_heisO hθ sS BS sT BT f hw, pT_heisO hθ sS BS sT BT g hw, om_heisO_inf hom ha hb hw (thp f hf P),
      thetaInner_heisenberg hψ hcv (thom f hf P) (thp g hg P')]
  exact GlobalTheory.T.schur_finiteHeisenberg_fockVacuumThetaFunctions D ψ θ S T hψ hθ sS sT hcS hcT μ 𝓕 hcv Φ hl hr hbd hi

end GlobalTheory.FockCoefSplit

namespace GlobalTheory.FockCoefSplit

open GlobalTheory.RawLift

theorem coef_split : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsInfFam θ → IsWeilDatumO ψ S T χS χT om → ∀ (μ : Measure (WO S T)) (𝓧 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓧 → ∀ (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∀ pS pT : D.what₂.Tau → ℕ, (∀ τ, IsONBasis (gramAt D S τ) (sS τ) (BS τ) (pS τ)) → (∀ τ, IsONBasis (gramAt D T τ) (sT τ) (BT τ) (pT τ)) → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → (∀ Q, IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT f Q)) → ∀ a ∈ GinfC S, ∀ b ∈ GinfC T, ∀ x ∈ GfC S, ∀ y ∈ GfC T, ∀ Q Q', l2 μ 𝓧 (om (x * a, y * b) (pureTensorO ψ θ S T sS sT BS BT f Q)) (pureTensorO ψ θ S T sS sT BS BT f Q') * l2 μ 𝓧 f f = l2 μ 𝓧 (om (a, b) (pureTensorO ψ θ S T sS sT BS BT f Q)) (pureTensorO ψ θ S T sS sT BS BT f Q') * l2 μ 𝓧 (om (x, y) f) f := by
  intro D ψ θ S T χS χT om hθ hom μ 𝓧 hcv sS BS sT BT hcS hcT pS pT hoS hoT f hf hvf hpt a ha b hb x hx y hy Q Q'
  obtain ⟨c, hc⟩ := pair_eq_inf D ψ θ S T χS χT om hom hθ sS BS sT BT pS pT hcS hcT hoS hoT μ 𝓧 hcv a ha b hb Q Q'
  have hx' : x⁻¹ ∈ GfC S := Subgroup.inv_mem _ hx
  have hy' : y⁻¹ ∈ GfC T := Subgroup.inv_mem _ hy
  have hg : IsThetaFunO ψ S T (om (x⁻¹, y⁻¹) f) := hom.om_pres _ _ hf
  have hvg : ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) (om (x⁻¹, y⁻¹) f) :=
    fun τ => fockVac_om_fin hom hθ hx' hy' τ _ hf (hvf τ)
  have inv : ∀ A B : WO S T → ℂ, IsThetaFunO ψ S T A → IsThetaFunO ψ S T B →
      thetaIP μ 𝓧 (om (x, y) A) B = thetaIP μ 𝓧 A (om (x⁻¹, y⁻¹) B) := by
    intro A B hA hB
    have e : om (x, y) (om (x⁻¹, y⁻¹) B) = B := by
      rw [← Module.End.mul_apply, ← map_mul,
        show ((x, y) * (x⁻¹, y⁻¹) : GA D S × GA D T) = 1 from mul_inv_cancel (x, y), map_one, Module.End.one_apply]
    calc thetaIP μ 𝓧 (om (x, y) A) B = thetaIP μ 𝓧 (om (x, y) A) (om (x, y) (om (x⁻¹, y⁻¹) B)) := by rw [e]
      _ = thetaIP μ 𝓧 A (om (x⁻¹, y⁻¹) B) :=
        GlobalTheory.WeilPairing.thetaInner_weilRep D ψ S T χS χT om μ 𝓧 hom hcv _ _ _ hA (hom.om_pres _ _ hB)
  have e1 : om (x * a, y * b) (pureTensorO ψ θ S T sS sT BS BT f Q) =
      om (x, y) (om (a, b) (pureTensorO ψ θ S T sS sT BS BT f Q)) := by
    rw [← Module.End.mul_apply, ← map_mul]
    rfl
  simp only [l2_eq_star]
  rw [← star_mul', ← star_mul']
  congr 1
  rw [e1, inv _ _ (hom.om_pres _ _ (hpt Q)) (hpt Q'), om_fin_pureTensorO hom hθ sS BS sT BT hx' hy' hf Q',
    hc f _ hf hg hvf hvg, inv _ _ hf hf, hc f f hf hf hvf hvf]
  ring

end GlobalTheory.FockCoefSplit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockMatrixCoefficientSplitsRealFiniteFactorsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockMatrixCoefficient_splits_real_finite_factors : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsInfFam θ → IsWeilDatumO ψ S T χS χT om → ∀ (μ : Measure (WO S T)) (𝓧 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓧 → ∀ (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∀ pS pT : D.what₂.Tau → ℕ, (∀ τ, IsONBasis (gramAt D S τ) (sS τ) (BS τ) (pS τ)) → (∀ τ, IsONBasis (gramAt D T τ) (sT τ) (BT τ) (pT τ)) → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → (∀ Q, IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT f Q)) → ∀ a ∈ GinfC S, ∀ b ∈ GinfC T, ∀ x ∈ GfC S, ∀ y ∈ GfC T, ∀ Q Q', l2 μ 𝓧 (om (x * a, y * b) (pureTensorO ψ θ S T sS sT BS BT f Q)) (pureTensorO ψ θ S T sS sT BS BT f Q') * l2 μ 𝓧 f f = l2 μ 𝓧 (om (a, b) (pureTensorO ψ θ S T sS sT BS BT f Q)) (pureTensorO ψ θ S T sS sT BS BT f Q') * l2 μ 𝓧 (om (x, y) f) f := by
  first | exact @GlobalTheory.FockCoefSplit.coef_split | exact GlobalTheory.FockCoefSplit.coef_split | (intros; apply GlobalTheory.FockCoefSplit.coef_split <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedChainRealZetaNonvanishing
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedChainRealZetaNonvanishing
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt

noncomputable section

namespace GlobalTheory.RealZetaTw


open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction in
theorem realZetaTw : GlobalTheory.Published.HarishChandraModules → ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ArchOnRecord D → RealZetaQ D := by
  intro hHC D hA hgap c w₁ hw k hk s s' hs hs' p hp m X hmX
  obtain ⟨hWexp, hvac⟩ := GlobalTheory.T.twisted_chain_step_weil_exponents_fock_vacuum D hgap c w₁ hw k hk s s' hs hs' p hp hk
  have hc : c.Is := hw.com
  obtain ⟨hr, -, hsI⟩ := hs
  obtain ⟨hr', -, hsI'⟩ := hs'
  have hspar : s.par = parB (Ptw D) k := hsI.par
  have hspar' : s'.par = parB (Ptw D) (k + 1) := hsI'.par
  have hsrank' : s'.V.rank = D.R.rankY (k + 1) := hsI'.rank
  obtain ⟨χS, χT, hW, hexp⟩ := hWexp
  have hCT := (hA.2 hgap).1
  have hfock : ∀ τ, IsFockAt c.ψ c.θ s.V s'.V τ (cart s.M τ) (cart s'.M τ) (onb s.M τ) (onb s'.M τ) p.f :=
    fun τ => ⟨hc.inf, isAdapted_model s.M τ, isAdapted_model s'.M τ, hvac.theta, hvac.ne, hvac.vac τ⟩
  have hSe : ∀ τ, alS D ⟨k, hk⟩ τ = expS D ⟨k, hk⟩ τ := by
    intro τ
    simp only [alS, expS]
    rcases Nat.even_or_odd k with h | h
    · simp [h, h.add_one]
    · have h1 : ¬ Odd (k + 1) := by rw [Nat.odd_add_one]; simpa using h
      have h2 : ¬ Even k := by simpa using h
      simp [h1, h2]
  have hTe : ∀ τ, alT D ⟨k, hk⟩ τ = expT D ⟨k, hk⟩ τ := by
    intro τ
    simp only [alT, expT]
    rcases Nat.even_or_odd k with h | h
    · simp [h, h.add_one]
    · have h1 : ¬ Odd (k + 1) := by rw [Nat.odd_add_one]; simpa using h
      have h2 : ¬ Even k := by simpa using h
      simp [h1, h2]
  have hpar : ∀ τ, s.par τ = parB (Ptw D) ((⟨k, hk⟩ : Fin D.R.m) : ℕ) τ := fun τ => by rw [hspar]
  have hpar' : ∀ τ, s'.par τ = parB (Ptw D) (((⟨k, hk⟩ : Fin D.R.m) : ℕ) + 1) τ := fun τ => by rw [hspar']
  have hLL := fun τ => (hCT ⟨k, hk⟩ τ s.V s'.V).2.1 c.ψ c.θ χS χT p.ω hW (by rw [hSe]; exact (hexp τ).1)
    (by rw [hTe]; exact (hexp τ).2) s.par s'.par s.M s'.M (hpar τ) (hpar' τ) _ _ p.f (hfock τ)
  have hZL := fun τ => (hCT ⟨k, hk⟩ τ s.V s'.V).2.2 c.ψ c.θ χS χT p.ω hW (by rw [hSe]; exact (hexp τ).1)
    (by rw [hTe]; exact (hexp τ).2) s.par s'.par s.M s'.M (hpar τ) (hpar' τ) _ _ p.f (hfock τ) m X hmX.1 hmX.2.1
  choose Φ hΦ using fun τ => (hLL τ).joint_ex
  choose w hwsm hwk hwhi using fun τ => GlobalTheory.T.exists_smooth_kFinite_unit_highestWeight_vector hHC D s.V s.par s.M τ
  refine ⟨glue Φ, fun τ => ⟨w τ, hwsm τ⟩, ?_⟩
  intro mR hmR
  set z : GinfC s.V → ℂ := zReal p m X (glue Φ) (fun τ => ⟨w τ, hwsm τ⟩) with hzdef
  have hfac := GlobalTheory.T.thetaInner_fockProduct_eq_prod_realPlaces D s.V s'.V s.par s'.par s.M s'.M c.θ c.ψ χS χT p.ω hc.inf hW m X hmX p.f hvac
  obtain ⟨cst, hcst, hhaar⟩ := GlobalTheory.T.integral_realUnitary_haar_eq_prod_Upq_haar D s.V s.par s.M c.θ hc.inf mR (fun τ => Formalism.REAL.muG (s.M.ε τ)) hmR
    (fun τ => inferInstance)
  have hZ := fun τ => hZL τ (Φ τ) (hΦ τ) ⟨w τ, hwk τ⟩ (hwhi τ) (Formalism.REAL.muG (s.M.ε τ)) inferInstance
  set i0 := ipTh m X p.f p.f with hi0
  set F : D.what₂.Tau → Matrix (Fin s.V.rank) (Fin s.V.rank) ℂ → ℂ := fun τ h =>
    ipTh m X (p.ω (atTau c.θ s.V τ h, 1) (ptAt c.ψ c.θ s.V s'.V τ (cart s.M τ) (cart s'.M τ) (onb s.M τ) (onb s'.M τ) p.f (Φ τ)))
      (ptAt c.ψ c.θ s.V s'.V τ (cart s.M τ) (cart s'.M τ) (onb s.M τ) (onb s'.M τ) p.f (Φ τ)) / i0 *
      conj ⟪(w τ : s.M.H τ), s.M.rep τ h (w τ)⟫_ℂ with hF
  have hrep : ∀ τ (Y : Matrix (Fin s.V.rank) (Fin s.V.rank) ℂ), s.M.rep τ (ofFr s.M τ Y) = s.M.σ τ Y := by
    intro τ Y
    have h1 : s.M.fr τ * (s.M.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (s.M.fr_unit τ))
    have : s.M.fr τ * ((s.M.fr τ)⁻¹ * Y * s.M.fr τ) * (s.M.fr τ)⁻¹ = Y := by
      calc s.M.fr τ * ((s.M.fr τ)⁻¹ * Y * s.M.fr τ) * (s.M.fr τ)⁻¹
          = (s.M.fr τ * (s.M.fr τ)⁻¹) * Y * (s.M.fr τ * (s.M.fr τ)⁻¹) := by simp only [Matrix.mul_assoc]
        _ = Y := by rw [h1]; simp
    simp only [DSModel.rep, ofFr, this]
  have hFu : ∀ τ (u : Formalism.REAL.UJ (s.M.ε τ)), F τ (ofFr s.M τ (umat u)) =
      ipTh m X (actSrc c.θ p.ω τ (ofFr s.M τ (umat u))
        (ptAt c.ψ c.θ s.V s'.V τ (cart s.M τ) (cart s'.M τ) (onb s.M τ) (onb s'.M τ) p.f (Φ τ)))
        (ptAt c.ψ c.θ s.V s'.V τ (cart s.M τ) (cart s'.M τ) (onb s.M τ) (onb s'.M τ) p.f (Φ τ)) *
        star (coefOn (s.M.σ τ) (w τ) (w τ) u) / i0 := by
    intro τ u
    simp only [hF, hrep, actSrc, coefOn, starRingEnd_apply]
    ring
  have hFint : ∀ τ, Integrable (fun u : Formalism.REAL.UJ (s.M.ε τ) => F τ (ofFr s.M τ (umat u))) (Formalism.REAL.muG (s.M.ε τ)) := by
    intro τ; simp_rw [hFu]; exact (hZ τ).2.1.div_const _
  have hFval : ∀ τ, ∃ r : ℝ, 0 < r ∧ ∫ u, F τ (ofFr s.M τ (umat u)) ∂(Formalism.REAL.muG (s.M.ε τ)) = (r : ℂ) / i0 := by
    intro τ
    obtain ⟨r, hr, hrI⟩ := (hZ τ).2.2.1
    refine ⟨r, hr, ?_⟩
    simp_rw [hFu]; rw [integral_div, hrI]
  choose r hr hrI using hFval
  have hi0 : i0 ≠ 0 := hfac.1
  have hz : ∀ g : GinfC s.V, z g = i0 * ∏ τ, F τ (Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig s.V.gram (c.θ τ) (g : GA D s.V)) := by
    intro g
    have h := hfac.2 Φ g g.2
    change ipTh m X (p.ω ((g : GA D s.V), 1) (ptOf c.ψ c.θ s.M s'.M p.f (glue Φ))) (ptOf c.ψ c.θ s.M s'.M p.f (glue Φ)) *
      conj (∏ τ, ⟪(w τ : s.M.H τ), s.M.rep τ (Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig s.V.gram (c.θ τ) (g : GA D s.V)) (w τ)⟫_ℂ) = _
    rw [h, map_prod, mul_assoc, ← Finset.prod_mul_distrib]
  obtain ⟨hIint, hIval⟩ := hhaar F hFint
  have hintz : ∫ g, z g ∂mR = i0 * ((cst : ℂ) * ∏ τ, ((r τ : ℂ) / i0)) := by
    simp_rw [hz]; rw [integral_const_mul, hIval]; simp_rw [hrI]
  refine ⟨?_, fun τ => hwk τ, ?_⟩
  · rw [hintz]
    exact mul_ne_zero hi0 (mul_ne_zero (by exact_mod_cast hcst.ne')
      (Finset.prod_ne_zero_iff.2 fun τ _ => div_ne_zero (by exact_mod_cast (hr τ).ne') hi0))
  · rintro a ⟨ha, hfr⟩
    refine ⟨0, div_pos (by exact_mod_cast D.R.t_odd.pos) two_pos, ?_⟩
    obtain ⟨C, hC⟩ := GlobalTheory.T.realMatrixCoeff_fockVectors_le_doublingHeight_pow D s.V s'.V s.par s'.par s.M s'.M c.θ c.ψ χS χT p.ω hc.inf hW m X hmX p.f hvac a ha hfr
      (glue Φ) (glue Φ)
    set mf : GinfC s.V → ℂ := fun g => conj (∏ τ, ⟪(w τ : s.M.H τ),
      s.M.rep τ (Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig s.V.gram (c.θ τ) (g : GA D s.V)) (w τ)⟫_ℂ) with hmf
    have hmint : Integrable mf mR := by
      obtain ⟨hI2, -⟩ := hhaar (fun τ h => conj ⟪(w τ : s.M.H τ), s.M.rep τ h (w τ)⟫_ℂ) (fun τ => by
        simp only [hrep]
        exact (hZ τ).1.norm.mono' (hZ τ).1.1.star (Filter.Eventually.of_forall fun x => (RCLike.norm_conj _).le))
      simpa [hmf, map_prod] using hI2
    set Hf : GinfC s.V → ℝ := fun g => ∏ w, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW s.V a w
      (GlobalTheory.AdelicU.projArch D.sp.cm.sig s.V.gram w (g : GA D s.V)) with hHf
    have hHc : Continuous Hf := continuous_finsetProd _ fun w _ =>
      (GlobalTheory.T.doublingHeightAtRealPlace_continuous_pos_le_one D s.V a ha w).1.comp ((GlobalTheory.AdelicU.continuous_projArch _ _ w).comp continuous_subtype_val)
    have hHpos : ∀ g, 0 < Hf g ∧ Hf g ≤ 1 := fun g =>
      ⟨Finset.prod_pos fun w _ => ((GlobalTheory.T.doublingHeightAtRealPlace_continuous_pos_le_one D s.V a ha w).2 _).1,
        Finset.prod_le_one₀ (fun w _ => ((GlobalTheory.T.doublingHeightAtRealPlace_continuous_pos_le_one D s.V a ha w).2 _).1.le)
          fun w _ => ((GlobalTheory.T.doublingHeightAtRealPlace_continuous_pos_le_one D s.V a ha w).2 _).2⟩
    have hzint : Integrable z mR :=
      (hIint.const_mul i0).congr (Filter.Eventually.of_forall fun g => (hz g).symm)
    have htb : D.R.t ≤ s'.V.rank := by
      rw [hsrank', Formalism.BasicNotions.Ranks.rankY]; nlinarith
    have hbd : ∀ g, ‖z g‖ ≤ C * Hf g ^ ((s'.V.rank : ℝ) / 2) * ‖mf g‖ := by
      intro g
      change ‖ipTh m X (p.ω ((g : GA D s.V), 1) (ptOf c.ψ c.θ s.M s'.M p.f (glue Φ))) (ptOf c.ψ c.θ s.M s'.M p.f (glue Φ)) *
        mf g‖ ≤ _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hC g g.2) (norm_nonneg _)
    exact GlobalTheory.T.integrable_mul_heightPow_of_bounded_factor mR z mf Hf C s'.V.rank D.R.t hzint hmint hHc hHpos htb hbd

end GlobalTheory.RealZetaTw

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedChainRealZetaNonvanishingStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedChain_realZeta_nonvanishing : GlobalTheory.Published.HarishChandraModules → ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ArchOnRecord D → RealZetaQ D := by
  first | exact @GlobalTheory.RealZetaTw.realZetaTw | exact GlobalTheory.RealZetaTw.realZetaTw | (intros; apply GlobalTheory.RealZetaTw.realZetaTw <;> assumption)
end
end
