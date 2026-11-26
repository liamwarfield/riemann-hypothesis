module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockCoefficientExtremalEqDiscreteSeries
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StrongApproximationDecomposition
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicConjugateCharacterStandardForms

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftPairingLowestWeightSchurPolarisation
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftPairingLowestWeightSchurPolarisation
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues

namespace GlobalTheory.CoefSchur

theorem sesq_eq_of_diag {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F G : E →ₗ[ℂ] E →ₗ⋆[ℂ] ℂ) (h : ∀ x, F x x = G x x) : F = G := by
  have h0 : ∀ x, (F - G) x x = 0 := fun x => by simp [h x]
  suffices hD : ∀ x y, (F - G) x y = 0 by
    ext x y
    have := hD x y
    simpa [sub_eq_zero] using this
  intro x y
  have h1 := h0 (x + y)
  have h2 := h0 (x + Complex.I • y)
  simp only [map_add (f := _), LinearMap.add_apply, LinearMap.map_smulₛₗ,
    LinearMap.smul_apply, smul_eq_mul, h0, Complex.conj_I, mul_zero, add_zero, zero_add] at h1 h2
  have hI := Complex.I_sq
  linear_combination (-(Complex.I) / 2 * Complex.I) * h1 + (Complex.I / 2) * h2 + ((F - G) x y) * hI

theorem schur_sesq {G : Type*} [Group G] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [Nontrivial E] (ρ : G →* Module.End ℂ E)
    (hu : ∀ h x y, ⟪ρ h x, ρ h y⟫_ℂ = ⟪x, y⟫_ℂ)
    (hirr : ∀ U : Submodule ℂ E, (∀ h, Submodule.map (ρ h) U ≤ U) → U = ⊥ ∨ U = ⊤)
    (B : E →ₗ[ℂ] E →ₗ⋆[ℂ] ℂ) (hB : ∀ h x y, B (ρ h x) (ρ h y) = B x y) :
    ∃ c : ℂ, ∀ x y, B x y = c * ⟪y, x⟫_ℂ := by
  classical
  let b := stdOrthonormalBasis ℂ E
  let A : E →ₗ[ℂ] E := ∑ i, (B.flip (b i)).smulRight (b i)
  have hA : ∀ x y, B x y = ⟪y, A x⟫_ℂ := by
    intro x y
    conv_lhs => rw [← b.sum_repr' y]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [A, map_sum, inner_sum, inner_smul_right, inner_conj_symm, mul_comm]
  have hcomm : ∀ h x, A (ρ h x) = ρ h (A x) := by
    intro h x
    apply ext_inner_left ℂ
    intro y
    have hy : ρ h (ρ h⁻¹ y) = y := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    calc ⟪y, A (ρ h x)⟫_ℂ = B (ρ h x) y := (hA _ _).symm
      _ = B (ρ h x) (ρ h (ρ h⁻¹ y)) := by rw [hy]
      _ = B x (ρ h⁻¹ y) := hB _ _ _
      _ = ⟪ρ h⁻¹ y, A x⟫_ℂ := hA _ _
      _ = ⟪ρ h (ρ h⁻¹ y), ρ h (A x)⟫_ℂ := (hu _ _ _).symm
      _ = ⟪y, ρ h (A x)⟫_ℂ := by rw [hy]
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue A
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  have hinv : ∀ h, Submodule.map (ρ h) (Module.End.eigenspace A c) ≤ Module.End.eigenspace A c := by
    rintro h _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff] at hx
    rw [Module.End.mem_eigenspace_iff, hcomm, hx, map_smul]
  have htop : Module.End.eigenspace A c = ⊤ := by
    rcases hirr _ hinv with h | h
    · exfalso
      have hmem : v ∈ Module.End.eigenspace A c := Module.End.mem_eigenspace_iff.mpr hv.apply_eq_smul
      rw [h, Submodule.mem_bot] at hmem
      exact hv.2 hmem
    · exact h
  refine ⟨c, fun x y => ?_⟩
  have hx : x ∈ Module.End.eigenspace A c := htop ▸ Submodule.mem_top
  rw [Module.End.mem_eigenspace_iff] at hx
  rw [hA, hx, inner_smul_right]

end GlobalTheory.CoefSchur

namespace GlobalTheory.CoefSchur

section
variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} {μ : Measure (WO S T)} {𝓧 : Set (WO S T)}

theorem integrable_mul_conj (hW : IsWeilDatumO ψ S T χS χT om) (hC : IsCovolOne (ratL T S) μ 𝓧)
    {a b : WO S T → ℂ} (ha : IsThetaFunO ψ S T a) (hb : IsThetaFunO ψ S T b) :
    Integrable (fun x => a x * (starRingEnd ℂ) (b x)) (μ.restrict 𝓧) := by
  refine (GlobalTheory.RawLift.FockCoef.integrable_pair hW hC hb ha).congr
    (Filter.Eventually.of_forall fun x => ?_)
  show star (b x) * a x = a x * (starRingEnd ℂ) (b x)
  rw [starRingEnd_apply, mul_comm]

theorem thetaFunctionPairing_weilAction_invariant (hW : IsWeilDatumO ψ S T χS χT om) (hC : IsCovolOne (ratL T S) μ 𝓧)
    (p : GA D S × GA D T) {a b : WO S T → ℂ} (ha : IsThetaFunO ψ S T a)
    (hb : IsThetaFunO ψ S T b) : l2 μ 𝓧 (om p a) (om p b) = l2 μ 𝓧 a b := by
  have key : ∀ f g : WO S T → ℂ, l2 μ 𝓧 f g = GlobalTheory.RawLift.thetaIP μ 𝓧 g f := by
    intro f g
    simp only [l2, Lift.pet, GlobalTheory.RawLift.thetaIP]
    congr 1
    funext x
    rw [starRingEnd_apply, mul_comm]
  rw [key, key, GlobalTheory.WeilPairing.thetaInner_weilRep D ψ S T χS χT om μ 𝓧 hW hC p b a hb ha]

noncomputable def thetaForm (hW : IsWeilDatumO ψ S T χS χT om) (hC : IsCovolOne (ratL T S) μ 𝓧)
    {E : Type*} [AddCommGroup E] [Module ℂ E] (a b : E →ₗ[ℂ] (WO S T → ℂ))
    (ha : ∀ x, IsThetaFunO ψ S T (a x)) (hb : ∀ y, IsThetaFunO ψ S T (b y)) :
    E →ₗ[ℂ] E →ₗ⋆[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun x y => l2 μ 𝓧 (a x) (b y))
    (fun x x' y => by
      simp only [map_add (f := _), l2, Lift.pet, Pi.add_apply, add_mul]
      exact integral_add (integrable_mul_conj hW hC (ha x) (hb y))
        (integrable_mul_conj hW hC (ha x') (hb y)))
    (fun c x y => by
      simp only [map_smul, l2, Lift.pet, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]
      exact integral_const_mul c _)
    (fun x y y' => by
      simp only [map_add (f := _), l2, Lift.pet, Pi.add_apply, mul_add]
      exact integral_add (integrable_mul_conj hW hC (ha x) (hb y))
        (integrable_mul_conj hW hC (ha x) (hb y')))
    (fun c x y => by
      simp only [map_smul, l2, Lift.pet, Pi.smul_apply, smul_eq_mul, map_mul]
      rw [← integral_const_mul]
      congr 1
      funext z
      ring)

theorem thetaForm_apply (hW : IsWeilDatumO ψ S T χS χT om) (hC : IsCovolOne (ratL T S) μ 𝓧)
    {E : Type*} [AddCommGroup E] [Module ℂ E] (a b : E →ₗ[ℂ] (WO S T → ℂ))
    (ha : ∀ x, IsThetaFunO ψ S T (a x)) (hb : ∀ y, IsThetaFunO ψ S T (b y)) (x y : E) :
    thetaForm hW hC a b ha hb x y = l2 μ 𝓧 (a x) (b y) := rfl

end

end GlobalTheory.CoefSchur

namespace GlobalTheory.CoefSchur

theorem realElt_one {D : D7} (θ : InfFam D) (hθ : IsInfFam θ) (T : HSp D) :
    realElt θ T 1 = 1 := by
  classical
  obtain ⟨L, -, hL2, -, -, -, hLat, -, -⟩ := GlobalTheory.RealLift.exists_real_lift D θ T hθ
  have h1UH : ∀ τ, (1 : Matrix (Fin T.rank) (Fin T.rank) ℂ) ∈ Formalism.QuantumDeterminants.UH (gramAt D T τ) := by
    intro τ; simp [Formalism.QuantumDeterminants.UH]
  have h1UG : (1 : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) ∈ GlobalTheory.HolDict.UG (gramAt D T) :=
    fun τ => h1UH τ
  have hL1 : L 1 = 1 := by
    have := hL2 1 h1UG 1 h1UG
    rw [mul_one] at this
    exact mul_left_cancel (a := L 1) (by rw [mul_one]; exact this.symm)
  have hat : ∀ τ, atTau θ T τ 1 = 1 := by
    intro τ; rw [hLat τ 1 (h1UH τ), Pi.mulSingle_one, hL1]
  simp [realElt, hat]

theorem thetaLiftPairing_lowestWeight_schur_polarisation_alt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsInfFam θ → IsWeilDatumO ψ S T χS χT om → ∀ (Sp : D.what₂.Tau → SPar) (M : DSModel T Sp), ∀ (μ : Measure (WO S T)) (𝓧 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓧 → ∀ c : CoefA S, c.Is → ∀ pt : PolF D T.rank S.rank →ₗ[ℂ] (WO S T → ℂ), (∀ P, IsThetaFunO ψ S T (pt P)) → ∀ (Δ : PolF D T.rank S.rank) (io : LowT M →ₗ[ℂ] c.W →ₗ[ℂ] PolF D T.rank S.rank), IsIoW θ M c om (fun P => pt P) Δ io → (∀ w : c.W, ∃ N : ℂ, ∀ g : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ, (∀ ρ, g ρ ∈ Formalism.QuantumDeterminants.UH (gramAt D T ρ)) → ∀ (e e' : ∀ ρ, lowT M ρ), l2 μ 𝓧 (om (1, realElt θ T g) (pt (io (PiTensorProduct.tprod ℂ e) w))) (pt (io (PiTensorProduct.tprod ℂ e') w)) = N * (∏ ρ, ⟪((e' ρ : M.sm ρ) : M.H ρ), M.rep ρ (g ρ) ((e ρ : M.sm ρ) : M.H ρ)⟫_ℂ)) → ∀ g : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ, (∀ ρ, g ρ ∈ Formalism.QuantumDeterminants.UH (gramAt D T ρ)) → ∀ (e e' : ∀ ρ, lowT M ρ) (w w' : c.W), l2 μ 𝓧 (om (1, realElt θ T g) (pt (io (PiTensorProduct.tprod ℂ e) w))) (pt (io (PiTensorProduct.tprod ℂ e') w')) = l2 μ 𝓧 (pt Δ) (pt Δ) * (∏ ρ, ⟪((e' ρ : M.sm ρ) : M.H ρ), M.rep ρ (g ρ) ((e ρ : M.sm ρ) : M.H ρ)⟫_ℂ) * ⟪w', w⟫_ℂ := by
  intro D ψ θ S T χS χT om hθ hW Sp M μ 𝓧 hC c hc pt hpt Δ io hio hN g hg e e' w w'
  obtain ⟨hio1, -, v₀, w₀, hv₀, hw₀, hΔ⟩ := hio
  haveI : Nontrivial c.W := hc.2.2.2.1
  have hr1 := realElt_one θ hθ T
  have hom1 : om (1, realElt θ T 1) = 1 := by rw [hr1]; exact map_one om
  have hth : ∀ p P, IsThetaFunO ψ S T (om p (pt P)) := fun p P => hW.om_pres p _ (hpt P)
  let b₀ : c.W →ₗ[ℂ] (WO S T → ℂ) := pt.comp (io (PiTensorProduct.tprod ℂ v₀))
  let B := thetaForm hW hC b₀ b₀ (fun _ => hpt _) (fun _ => hpt _)
  have hBinf : ∀ u ∈ GinfC S, ∀ x y, B (c.ρ u x) (c.ρ u y) = B x y := by
    intro u hu x y
    have hio1' : ∀ (x : LowT M) (w : c.W), om (u, 1) (pt (io x w)) = pt (io x (c.ρ u w)) := hio1 u hu
    simp only [B, thetaForm_apply, b₀, LinearMap.comp_apply]
    rw [← hio1', ← hio1']
    exact thetaFunctionPairing_weilAction_invariant hW hC _ (hpt _) (hpt _)
  have hBinv : ∀ h x y, B (c.ρ h x) (c.ρ h y) = B x y := by
    intro h x y
    obtain ⟨L, -, -, -, -, -, -, hdec, -⟩ := GlobalTheory.RealLift.exists_real_lift D θ S hθ
    obtain ⟨a, ha, u, hu, rfl⟩ := hdec h
    rw [map_mul, Module.End.mul_apply, Module.End.mul_apply, hc.1 a ha, Module.End.one_apply,
      Module.End.one_apply]
    exact hBinf u hu x y
  obtain ⟨lam, hlam⟩ := schur_sesq c.ρ hc.2.1 hc.2.2.2.2 B hBinv
  have hlam0 : lam = l2 μ 𝓧 (pt Δ) (pt Δ) := by
    have := hlam w₀ w₀
    simp only [B, thetaForm_apply, b₀, LinearMap.comp_apply, hΔ] at this
    rw [this, inner_self_eq_norm_sq_to_K, hw₀]; simp
  have hP0 : ∏ ρ, ⟪((v₀ ρ : M.sm ρ) : M.H ρ), M.rep ρ ((1 : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) ρ) ((v₀ ρ : M.sm ρ) : M.H ρ)⟫_ℂ = 1 := by
    apply Finset.prod_eq_one
    intro ρ _
    have hfr : M.fr ρ * (1 : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) ρ * (M.fr ρ)⁻¹ = 1 := by
      rw [Pi.one_apply, mul_one]
      exact Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (M.fr_unit ρ))
    have hσ : M.σ ρ 1 = 1 := (M.ds ρ).2.2.1.1.1
    rw [DSModel.rep, hfr, hσ, ContinuousLinearMap.one_apply, inner_self_eq_norm_sq_to_K, hv₀ ρ]; simp
  have h1mem : ∀ ρ, (1 : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) ρ ∈ Formalism.QuantumDeterminants.UH (gramAt D T ρ) := by
    intro ρ; simp [Formalism.QuantumDeterminants.UH]
  have hdiag : ∀ x : c.W, ∀ g : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ,
      (∀ ρ, g ρ ∈ Formalism.QuantumDeterminants.UH (gramAt D T ρ)) → ∀ e e' : ∀ ρ, lowT M ρ,
      l2 μ 𝓧 (om (1, realElt θ T g) (pt (io (PiTensorProduct.tprod ℂ e) x)))
        (pt (io (PiTensorProduct.tprod ℂ e') x)) = l2 μ 𝓧 (pt Δ) (pt Δ) *
        (∏ ρ, ⟪((e' ρ : M.sm ρ) : M.H ρ), M.rep ρ (g ρ) ((e ρ : M.sm ρ) : M.H ρ)⟫_ℂ) * ⟪x, x⟫_ℂ := by
    intro x g hg e e'
    obtain ⟨N, hNx⟩ := hN x
    have h1 := hNx 1 h1mem v₀ v₀
    rw [hP0, mul_one, hom1, Module.End.one_apply] at h1
    have hBx : B x x = N := h1
    rw [hlam, hlam0] at hBx
    rw [hNx g hg e e', ← hBx]; ring
  let F : c.W →ₗ[ℂ] c.W →ₗ⋆[ℂ] ℂ := thetaForm hW hC
    ((om (1, realElt θ T g)).comp (pt.comp (io (PiTensorProduct.tprod ℂ e))))
    (pt.comp (io (PiTensorProduct.tprod ℂ e'))) (fun _ => hth _ _) (fun _ => hpt _)
  let G : c.W →ₗ[ℂ] c.W →ₗ⋆[ℂ] ℂ := (l2 μ 𝓧 (pt Δ) (pt Δ) *
    ∏ ρ, ⟪((e' ρ : M.sm ρ) : M.H ρ), M.rep ρ (g ρ) ((e ρ : M.sm ρ) : M.H ρ)⟫_ℂ) • (innerₛₗ ℂ).flip
  have hFG := sesq_eq_of_diag F G (fun x => by
    simp only [F, G, thetaForm_apply, LinearMap.comp_apply, LinearMap.smul_apply,
      LinearMap.flip_apply, smul_eq_mul]
    exact hdiag x g hg e e')
  have := LinearMap.congr_fun₂ hFG w w'
  simp only [F, G, thetaForm_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    LinearMap.flip_apply, smul_eq_mul] at this
  exact this

end GlobalTheory.CoefSchur
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftPairingLowestWeightSchurPolarisationStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLiftPairing_lowestWeight_schur_polarisation : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsInfFam θ → IsWeilDatumO ψ S T χS χT om → ∀ (Sp : D.what₂.Tau → SPar) (M : DSModel T Sp), ∀ (μ : Measure (WO S T)) (𝓧 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓧 → ∀ c : CoefA S, c.Is → ∀ pt : PolF D T.rank S.rank →ₗ[ℂ] (WO S T → ℂ), (∀ P, IsThetaFunO ψ S T (pt P)) → ∀ (Δ : PolF D T.rank S.rank) (io : LowT M →ₗ[ℂ] c.W →ₗ[ℂ] PolF D T.rank S.rank), IsIoW θ M c om (fun P => pt P) Δ io → (∀ w : c.W, ∃ N : ℂ, ∀ g : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ, (∀ ρ, g ρ ∈ Formalism.QuantumDeterminants.UH (gramAt D T ρ)) → ∀ (e e' : ∀ ρ, lowT M ρ), l2 μ 𝓧 (om (1, realElt θ T g) (pt (io (PiTensorProduct.tprod ℂ e) w))) (pt (io (PiTensorProduct.tprod ℂ e') w)) = N * (∏ ρ, ⟪((e' ρ : M.sm ρ) : M.H ρ), M.rep ρ (g ρ) ((e ρ : M.sm ρ) : M.H ρ)⟫_ℂ)) → ∀ g : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ, (∀ ρ, g ρ ∈ Formalism.QuantumDeterminants.UH (gramAt D T ρ)) → ∀ (e e' : ∀ ρ, lowT M ρ) (w w' : c.W), l2 μ 𝓧 (om (1, realElt θ T g) (pt (io (PiTensorProduct.tprod ℂ e) w))) (pt (io (PiTensorProduct.tprod ℂ e') w')) = l2 μ 𝓧 (pt Δ) (pt Δ) * (∏ ρ, ⟪((e' ρ : M.sm ρ) : M.H ρ), M.rep ρ (g ρ) ((e ρ : M.sm ρ) : M.H ρ)⟫_ℂ) * ⟪w', w⟫_ℂ := by
  first | exact @GlobalTheory.CoefSchur.thetaLiftPairing_lowestWeight_schur_polarisation_alt | exact GlobalTheory.CoefSchur.thetaLiftPairing_lowestWeight_schur_polarisation_alt | (intros; apply GlobalTheory.CoefSchur.thetaLiftPairing_lowestWeight_schur_polarisation_alt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartLevelsKeepStandardLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartLevelsKeepStandardLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.KLat

section Gen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

abbrev IA (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    Subring (E ⊗[F] FiniteAdeleRing (𝓞 F) F) :=
  tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)

theorem inclE_mem_IA (r : 𝓞 E) : inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (r : E) ∈ IA F E :=
  Subring.subset_closure (Or.inl ⟨⟨(r : E), ⟨r, rfl⟩⟩, rfl⟩)

theorem sigR_mem_IA (σ : E →ₐ[F] E) {y : E ⊗[F] FiniteAdeleRing (𝓞 F) F} (hy : y ∈ IA F E) :
    Formalism.UG.sigR σ (FiniteAdeleRing (𝓞 F) F) y ∈ IA F E := by
  have h : IA F E ≤ (IA F E).comap (Formalism.UG.sigR σ (FiniteAdeleRing (𝓞 F) F)) := by
    refine Subring.closure_le.2 ?_
    rintro z (⟨⟨x, ⟨r, rfl⟩⟩, rfl⟩ | ⟨⟨w, hw⟩, rfl⟩)
    · have hi : IsIntegral ℤ (σ (algebraMap (𝓞 E) E r)) :=
        (NumberField.RingOfIntegers.isIntegral_coe r).map (RingHom.toIntAlgHom (σ : E →+* E))
      have e : Formalism.UG.sigR σ (FiniteAdeleRing (𝓞 F) F) ((algebraMap (𝓞 E) E r) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) =
          inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (((⟨_, hi⟩ : 𝓞 E) : E)) := rfl
      show Formalism.UG.sigR σ (FiniteAdeleRing (𝓞 F) F) ((algebraMap (𝓞 E) E r) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) ∈ IA F E
      rw [e]
      exact inclE_mem_IA (F := F) (⟨_, hi⟩ : 𝓞 E)
    · have e : Formalism.UG.sigR σ (FiniteAdeleRing (𝓞 F) F) ((1 : E) ⊗ₜ[F] (w : FiniteAdeleRing (𝓞 F) F)) = (1 : E) ⊗ₜ[F] (w : FiniteAdeleRing (𝓞 F) F) := by
        simp [Formalism.UG.sigR]
      show Formalism.UG.sigR σ (FiniteAdeleRing (𝓞 F) F) ((1 : E) ⊗ₜ[F] (w : FiniteAdeleRing (𝓞 F) F)) ∈ IA F E
      rw [e]
      exact Subring.subset_closure (Or.inr ⟨⟨w, hw⟩, rfl⟩)
  exact h hy

variable {n : ℕ}

def HatP (π : 𝓞 E) (x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F) : Prop :=
  ∀ j : Fin n, x j ∈ IA F E ∧
    (j.1 + 1 = n → ∃ s ∈ IA F E, x j = inclE (F := F) (FiniteAdeleRing (𝓞 F) F) ((π : 𝓞 E) : E) * s)

theorem hatP_of_mem (π : 𝓞 E) (L : Submodule (𝓞 E) (Fin n → E))
    (hL : ∀ x, x ∈ L → ∀ j : Fin n, ∃ r : 𝓞 E, x j = (r : E) ∧ (j.1 + 1 = n → π ∣ r))
    {x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F}
    (hx : x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (IA F E) L) : HatP π x := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨z, hz, rfl⟩ := hy
    intro j
    obtain ⟨r, hr, hd⟩ := hL z hz j
    refine ⟨by simp only [hr]; exact inclE_mem_IA r, fun hj => ?_⟩
    obtain ⟨t, rfl⟩ := hd hj
    refine ⟨_, inclE_mem_IA t, ?_⟩
    show inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (z j) = _
    rw [hr, ← map_mul]; rfl
  | zero => intro j; exact ⟨zero_mem _, fun _ => ⟨0, zero_mem _, by simp⟩⟩
  | add x y _ _ hx hy =>
    intro j
    obtain ⟨a1, a2⟩ := hx j
    obtain ⟨b1, b2⟩ := hy j
    refine ⟨add_mem a1 b1, fun hj => ?_⟩
    obtain ⟨s, hs, e⟩ := a2 hj
    obtain ⟨s', hs', e'⟩ := b2 hj
    exact ⟨s + s', add_mem hs hs', by simp only [Pi.add_apply, e, e', mul_add]⟩
  | smul c x _ hx =>
    intro j
    obtain ⟨a1, a2⟩ := hx j
    have ec : (c • x) j = (c : E ⊗[F] FiniteAdeleRing (𝓞 F) F) * x j := rfl
    refine ⟨by rw [ec]; exact mul_mem c.2 a1, fun hj => ?_⟩
    obtain ⟨s, hs, e⟩ := a2 hj
    exact ⟨(c : E ⊗[F] FiniteAdeleRing (𝓞 F) F) * s, mul_mem c.2 hs, by rw [ec, e]; ring⟩

end Gen

end GlobalTheory.KLat

namespace GlobalTheory.KLat

section Lev
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}

theorem inv_eq_cT {J : Matrix (Fin n) (Fin n) E} (hJ : J = 1) (lev : StepLevel F E σ J T f bad)
    {g : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} (hg : g ∈ lev.U) (a b : Fin n) :
    (g⁻¹ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)).1 a b = Formalism.UG.sigR σ (FiniteAdeleRing (𝓞 F) F) (g.1 b a) := by
  have hu := ((lev.U_eq g).1 hg).1
  have h : Formalism.UG.cT (Formalism.UG.sigR σ (FiniteAdeleRing (𝓞 F) F)) g.1 * (J.map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F))) * g.1 =
      J.map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) := hu
  rw [hJ, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at h
  have e : (g⁻¹ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)).1 = Formalism.UG.cT (Formalism.UG.sigR σ (FiniteAdeleRing (𝓞 F) F)) g.1 := by
    calc (g⁻¹ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)).1
        = (Formalism.UG.cT (Formalism.UG.sigR σ (FiniteAdeleRing (𝓞 F) F)) g.1 * g.1) * (g⁻¹ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)).1 := by
          rw [h, Matrix.one_mul]
      _ = _ := by rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  rw [e]
  rfl

variable (π : 𝓞 E) {J : Matrix (Fin n) (Fin n) E} (lev : StepLevel F E σ J T f bad)
  (hLb : ∀ x, x ∈ lev.Lb ↔ ∀ j : Fin n, ∃ r : 𝓞 E, x j = (r : E) ∧ (j.1 + 1 = n → π ∣ r))

include hLb in
theorem img_hatP {g : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} (hg : g ∈ lev.U) (y : Fin n → E) (hy : y ∈ lev.Lb) :
    HatP π (g.1 *ᵥ fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (y i)) :=
  hatP_of_mem π lev.Lb (fun x hx => (hLb x).1 hx)
    ((GlobalTheory.Mem.Col2.SameOff.stepLevel_stab lev g hg _).1 (Submodule.subset_span ⟨y, hy, rfl⟩))

theorem incl_single (j : Fin n) (c : E) :
    (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) ((Pi.single j c : Fin n → E) i)) =
      Pi.single j (inclE (F := F) (FiniteAdeleRing (𝓞 F) F) c) := by
  funext i
  by_cases hi : i = j
  · subst hi; simp
  · simp [hi]


include hLb in
theorem col_mem {g : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} (hg : g ∈ lev.U) (j : Fin n) (hj : ¬ j.1 + 1 = n)
    (a : Fin n) : g.1 a j ∈ IA F E := by
  have hy : (Pi.single j 1 : Fin n → E) ∈ lev.Lb := by
    refine (hLb _).2 fun k => ?_
    by_cases hk : k = j
    · subst hk; exact ⟨1, by simp, fun h => absurd h hj⟩
    · exact ⟨0, by simp [hk], fun _ => dvd_zero _⟩
  have h := (img_hatP π lev hLb hg _ hy a).1
  rw [incl_single, map_one, Matrix.mulVec_single_one] at h
  simpa using h

include hLb in
theorem pi_ne_zero (l : Fin n) (hl : l.1 + 1 = n) : π ≠ 0 := by
  intro h0
  have hsub : (lev.Lb : Set (Fin n → E)) ⊆ (LinearMap.ker (LinearMap.proj l : (Fin n → E) →ₗ[E] E) : Set (Fin n → E)) := by
    intro x hx
    obtain ⟨r, hr, hd⟩ := (hLb x).1 hx l
    have hr0 : r = 0 := by rw [h0] at hd; exact zero_dvd_iff.1 (hd hl)
    simp [LinearMap.mem_ker, hr, hr0]
  have h2 := Submodule.span_le.2 hsub
  rw [lev.Lb_span, top_le_iff] at h2
  have h1 : (Pi.single l 1 : Fin n → E) ∈ LinearMap.ker (LinearMap.proj l : (Fin n → E) →ₗ[E] E) := by
    rw [h2]; trivial
  simp at h1


include hLb in
theorem last_mem {g : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} (hg : g ∈ lev.U) (l : Fin n) (hl : l.1 + 1 = n) :
    g.1 l l ∈ IA F E := by
  have hy : (Pi.single l (π : E) : Fin n → E) ∈ lev.Lb := by
    refine (hLb _).2 fun k => ?_
    by_cases hk : k = l
    · subst hk; exact ⟨π, by simp, fun _ => dvd_rfl⟩
    · exact ⟨0, by simp [hk], fun _ => dvd_zero _⟩
  obtain ⟨s, hs, e⟩ := (img_hatP π lev hLb hg _ hy l).2 hl
  rw [incl_single, Matrix.mulVec_single] at e
  have hπ : (π : E) ≠ 0 := fun h => pi_ne_zero π lev hLb l hl (by exact_mod_cast h)
  have hu : IsUnit (inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (π : E)) := (IsUnit.mk0 _ hπ).map _
  have e2 : inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (π : E) * g.1 l l = inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (π : E) * s := by
    rw [mul_comm]; exact e
  rw [hu.mul_left_cancel e2]
  exact hs


include hLb in
theorem entry_mem (hJ : J = 1) {g : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} (hg : g ∈ lev.U) (a b : Fin n) :
    g.1 a b ∈ IA F E := by
  by_cases hb : b.1 + 1 = n
  · by_cases ha : a.1 + 1 = n
    · have hab : a = b := Fin.ext (by omega)
      subst hab
      exact last_mem π lev hLb hg a ha
    · have hi : g⁻¹ ∈ lev.U := inv_mem hg
      have e := inv_eq_cT hJ lev hi a b
      rw [inv_inv] at e
      rw [e]
      exact sigR_mem_IA σ (col_mem π lev hLb hi a ha b)
  · exact col_mem π lev hLb hg b hb a

theorem entry_memD {D : D7} {n : ℕ} {J : Matrix (Fin n) (Fin n) D.host.E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
    (π : 𝓞 D.host.E) (lev : StepLevel D.host.F D.host.E (sigD D) J T f bad)
    (hLb : ∀ x, x ∈ lev.Lb ↔ ∀ j : Fin n, ∃ r : 𝓞 D.host.E, x j = (r : D.host.E) ∧ (j.1 + 1 = n → π ∣ r))
    (hJ : J = 1) {g : GL (Fin n) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)} (hg : g ∈ lev.U) (a b : Fin n) :
    g.1 a b ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
  entry_mem π lev hLb hJ hg a b

end Lev

end GlobalTheory.KLat

namespace GlobalTheory.AdForm

theorem levels_keep_stdLat : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i ≤ B.R.m) β, ∀ k ∈ A.U i β, Moves _ (rankN (I.rec7 l Z) i hi) k (Formalism.L2.Col.stdLat B.fields.E _) := by
  intro B X I hI _ l Z u a Ch A hA i hi β k hk
  obtain ⟨-, κ, hκ⟩ := (hA.U i hi β k).1 hk
  have hV : ((I.rec7 l Z).sp.X i).gram = 1 := hI.gram_X i
  refine GlobalTheory.SplitDec.moves_std hV _ ?_
  have hJ : gramN (I.rec7 l Z) i hi = 1 := by
    unfold gramN
    rw [hV]
    simp
  have hLb := (hA.reads i hi).lb β
  intro p q
  have e : toEAf (I.rec7 l Z) (Formalism.L2.Theta.mt _ k p q) =
      finM _ (rankN (I.rec7 l Z) i hi) k (finCongr (rankN _ i hi) p) (finCongr (rankN _ i hi) q) := by
    simp [finM, Matrix.reindex_apply]
  rw [e, ← hκ]
  have hLb' : ∀ x, x ∈ (A.K i hi β).lev.Lb ↔ ∀ j : Fin ((I.rec7 l Z).R.N i), ∃ r : 𝓞 (I.rec7 l Z).host.E,
      x j = (r : (I.rec7 l Z).host.E) ∧ (j.1 + 1 = (I.rec7 l Z).R.N i → (X.piT u : 𝓞 (I.rec7 l Z).host.E) ∣ r) :=
    fun x => hLb x
  exact GlobalTheory.KLat.entry_memD _ (A.K i hi β).lev hLb' hJ κ.2 _ _

end GlobalTheory.AdForm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartLevelsKeepStandardLatticeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartLevels_keep_standardLattice : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i ≤ B.R.m) β, ∀ k ∈ A.U i β, Moves _ (rankN (I.rec7 l Z) i hi) k (Formalism.L2.Col.stdLat B.fields.E _) := by
  first | exact @GlobalTheory.AdForm.levels_keep_stdLat | exact GlobalTheory.AdForm.levels_keep_stdLat | (intros; apply GlobalTheory.AdForm.levels_keep_stdLat <;> assumption)
end
end
