module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RkLe
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntEasy

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EvalModelPolynomialOnStdFramesInjective
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EvalModelPolynomialOnStdFramesInjective
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem eq_zero_of_ev1_eq_zero_on_frames : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (i : ℕ) {n : ℕ} (h : (X.Pj i).m + 1 = n) (R : XR (X.Pj i) ℂ), (∀ f : Fr1 D n, ev1 X D pos i h R f = 0) → R = 0 := by
  intro p _ X D pos i n h R hR
  refine Formalism.L2.G.evC_inj (X.Pj i) h (posJ X D pos i) (fun _ => 1) (fun _ => 1) (fun _ => by simp) R ?_
  funext f
  exact hR f

end GlobalTheory.TwV.DelA
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EvalModelPolynomialOnStdFramesInjectiveStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evalModelPolynomialOnStdFrames_injective : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (i : ℕ) {n : ℕ} (h : (X.Pj i).m + 1 = n) (R : XR (X.Pj i) ℂ), (∀ f : Fr1 D n, ev1 X D pos i h R f = 0) → R = 0 := by
  first | exact @GlobalTheory.TwV.DelA.eq_zero_of_ev1_eq_zero_on_frames | exact GlobalTheory.TwV.DelA.eq_zero_of_ev1_eq_zero_on_frames | (intros; apply GlobalTheory.TwV.DelA.eq_zero_of_ev1_eq_zero_on_frames <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AnalyticOnNhdOfDifferentiableVc
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory

variable {D : D7}

theorem analyticOnNhd_of_differentiable_vc {N N' : ℕ} (H : TaylorLogMetric.VC D N N' → ℂ) (hH : Differentiable ℂ H) :
    AnalyticOnNhd ℂ H Set.univ := by
  let e : TaylorLogMetric.VC D N N' ≃L[ℂ] (Fin (Module.finrank ℂ (TaylorLogMetric.VC D N N')) → ℂ) :=
    ContinuousLinearEquiv.ofFinrankEq (by rw [Module.finrank_fin_fun])
  have h1 : AnalyticOnNhd ℂ (H ∘ e.symm) Set.univ :=
    ReciprocityTheory.AnForm.Osgood.osgood _ Set.univ (H ∘ e.symm) isOpen_univ
      (hH.comp e.symm.differentiable).differentiableOn
  have h2 : H = (H ∘ e.symm) ∘ e := by
    funext z
    simp
  rw [h2]
  exact h1.comp (e.toContinuousLinearMap.analyticOnNhd Set.univ) (Set.mapsTo_univ _ _)

theorem entire_algCoef_comb : ∀ (D : D7) {N N' m : ℕ} (c : Fin m → ℂ) (G : Fin m → TaylorLogMetric.VC D N N' → ℂ), (∀ k, c k ∈ TaylorLogMetric.Qbar) → (∀ k, Differentiable ℂ (G k) ∧ TaylorLogMetric.CoefIn D (G k) TaylorLogMetric.Qbar) → Differentiable ℂ (fun z => ∑ k, c k * G k z) ∧ TaylorLogMetric.CoefIn D (fun z => ∑ k, c k * G k z) TaylorLogMetric.Qbar := by
  intro D N N' m c G hc hG
  have hd : ∀ k, Differentiable ℂ (G k) := fun k => (hG k).1
  refine ⟨by fun_prop, fun α => ?_⟩
  have hsm : ∀ k (n : ℕ), ContDiff ℂ n (G k) := fun k n =>
    Formalism.L2.KerInert.ie_smooth (analyticOnNhd_of_differentiable_vc (G k) (hd k)) n
  rw [Formalism.L2.KerInert.ie_taylor_lin c G hsm α]
  exact sum_mem fun k _ => mul_mem (hc k) ((hG k).2 α)

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocSpCompanEq
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.CompSp

attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar in
theorem _root_.GlobalTheory.TwV.CompSp.locSp_compan_eq : ∀ {R : _root_.Formalism.BasicNotions.Ranks} {F E : Type} [Field F]
    [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (sp : _root_.Formalism.BasicNotions.Spaces R F E)
    (W K : Type) [CommRing W] [Field K] [Algebra W K] (ρ : E →+* K) {N : ℕ}
    (J : Matrix (Fin N) (Fin N) E) (a : 𝓞 E) (T : ℕ) (Λ : Submodule (𝓞 E) (Fin N → E)),
    IsUnit (T : W) → (∀ z ∈ _root_.Formalism.BasicNotions.dualSet (sp.cm.sig : E →+* E) J Λ, (T : E) • z ∈ Λ) →
      _root_.GlobalTheory.TwV.locSp W ρ (_root_.Formalism.L2.PairingIndexBounds.F.compan (sp := sp) J a Λ) =
        _root_.GlobalTheory.TwV.locSp W ρ Λ := by
  intro R F E _ _ _ _ _ _ sp W K _ _ _ ρ N J a T Λ hT hdual
  have hsub : Λ ≤ _root_.Formalism.L2.PairingIndexBounds.F.compan (sp := sp) J a Λ := by
    simp only [_root_.Formalism.L2.PairingIndexBounds.F.compan]
    exact le_sup_left
  have key : ∀ x ∈ _root_.Formalism.L2.PairingIndexBounds.F.compan (sp := sp) J a Λ, T • x ∈ Λ := by
    intro x hx
    let S : Submodule (𝓞 E) (Fin N → E) :=
      Λ.comap (T • LinearMap.id : (Fin N → E) →ₗ[𝓞 E] (Fin N → E))
    have hΛS : Λ ≤ S := fun y hy => by
      simp only [S, Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply]
      exact nsmul_mem hy T
    have hDS : Submodule.span (𝓞 E) (_root_.Formalism.BasicNotions.dualSet (sp.cm.sig : E →+* E) J Λ) ≤ S := by
      rw [Submodule.span_le]
      intro z hz
      simp only [S, SetLike.mem_coe, Submodule.mem_comap, LinearMap.smul_apply,
        LinearMap.id_apply]
      simpa [Nat.cast_smul_eq_nsmul] using hdual z hz
    have hle : _root_.Formalism.L2.PairingIndexBounds.F.compan (sp := sp) J a Λ ≤ S := by
      simp only [_root_.Formalism.L2.PairingIndexBounds.F.compan]
      exact sup_le hΛS (Submodule.smul_le_right.trans hDS)
    have := hle hx
    simpa [S] using this
  simp only [_root_.GlobalTheory.TwV.locSp]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨u, hu⟩ := hT
    have h1 : (fun k => ρ ((T • x) k)) ∈
        Submodule.span W ((fun x k ↦ ρ (x k)) '' (Λ : Set (Fin N → E))) :=
      Submodule.subset_span ⟨_, key x hx, rfl⟩
    have h2 : (fun k => ρ ((T • x) k)) = (u : W) • (fun k => ρ (x k)) := by
      funext k
      simp [hu, map_nsmul, Nat.cast_smul_eq_nsmul]
    have h3 := Submodule.smul_mem _ ((u⁻¹ : Wˣ) : W) h1
    rwa [h2, smul_smul, Units.inv_mul, one_smul] at h3
  · exact Submodule.span_mono (Set.image_mono hsub)

end GlobalTheory.TwV.CompSp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OperatorPolynomialCoeffsWeightExtendedByZero
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OperatorPolynomialCoeffsWeightExtendedByZero
noncomputable section

namespace GlobalTheory.TwV.DelA

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open MvPolynomial

theorem sum_castLE_of_vanish {M : Type} [AddCommMonoid M] {a b : ℕ} (h : a ≤ b) (F : Fin b → M)
    (hF : ∀ r : Fin b, a ≤ r.1 → F r = 0) : ∑ r, F r = ∑ r : Fin a, F (Fin.castLE h r) := by
  symm
  refine Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) _ _ ?_ (fun _ => rfl)
  intro r hr
  apply hF
  by_contra hlt
  exact hr ⟨⟨r.1, by omega⟩, rfl⟩

theorem polDY_colSub (D : D7) {N N' : ℕ} (hN : N ≤ N') (s : D.what₂.Tau → ℂ) (Q : MvPolynomial (GL3Theta.FrV D N) ℂ)
    (β : D.what₂.Tau → Matrix (Fin N') (Fin N') ℂ) (hβ : ∀ τ r c, c < r → β τ r c = 0) :
    MvPolynomial.map (colSub β : MvPolynomial (GL3Theta.FrV D N') ℂ →+* MvPolynomial (GL3Theta.FrV D N') ℂ) (polDY D s Q (N' := N')) =
      polDY D s (colSub (fun τ => (β τ).submatrix (Fin.castLE hN) (Fin.castLE hN)) Q) (N' := N') := by
  have e : (MvPolynomial.mapAlgHom (colSub β : MvPolynomial (GL3Theta.FrV D N') ℂ →ₐ[ℂ] MvPolynomial (GL3Theta.FrV D N') ℂ)).comp
      (aeval (fun k : GL3Theta.FrV D N => ∑ b : Fin N',
        C (C (s k.1) * (if h : (k.2.2 : ℕ) < N' then (X (k.1, b, ⟨k.2.2, h⟩) : MvPolynomial (GL3Theta.FrV D N') ℂ) else 0)) *
          X ((k.1, b, k.2.1) : GL3Theta.Idx D N N'))) =
      (aeval (fun k : GL3Theta.FrV D N => ∑ b : Fin N',
        C (C (s k.1) * (if h : (k.2.2 : ℕ) < N' then (X (k.1, b, ⟨k.2.2, h⟩) : MvPolynomial (GL3Theta.FrV D N') ℂ) else 0)) *
          X ((k.1, b, k.2.1) : GL3Theta.Idx D N N'))).comp (colSub (fun τ => (β τ).submatrix (Fin.castLE hN) (Fin.castLE hN))) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨τ, i, c⟩
    have hc : (c : ℕ) < N' := lt_of_lt_of_le c.2 hN
    have h1 : ∀ r : Fin N, (r : ℕ) < N' := fun r => lt_of_lt_of_le r.2 hN
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [AlgHom.comp_apply, aeval_X, colSub, dif_pos hc, dif_pos (h1 _), map_sum, map_mul, MvPolynomial.mapAlgHom_apply,
      map_X, map_C, algHom_C, algebraMap_eq, Matrix.submatrix_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [RingHom.coe_coe, aeval_C, aeval_X, map_sum, map_mul, algebraMap_eq, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    rw [sum_castLE_of_vanish hN]
    · refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun b _ => ?_
      simp only [Fin.castLE, MvPolynomial.algebraMap_apply, algebraMap_eq]
      ring
    · intro r hr
      refine Finset.sum_eq_zero fun b _ => ?_
      rw [hβ τ r ⟨c, hc⟩ (Fin.lt_def.2 (lt_of_lt_of_le c.2 hr))]
      simp
  exact DFunLike.congr_fun e Q

theorem wt_polDY_framePol : ∀ (D : D7) {N N' : ℕ}, N ≤ N' → ∀ (s : D.what₂.Tau → ℂ) (ν : D.what₂.Tau → Fin N → ℕ) (Q : MvPolynomial (GL3Theta.FrV D N) ℂ), Q ∈ WtPol ℂ ν → (∀ α, AddMonoidAlgebra.coeff (polDY D s Q (N' := N')) α ∈ WtPol ℂ (extNu N' ν)) ∧ ∀ Θ : TaylorLogMetric.VC D N N' → ℂ, framePol D s Q Θ ∈ WtPol ℂ (extNu N' ν) := by
  intro D N N' hN s ν Q hQ
  have hc : ∀ α, AddMonoidAlgebra.coeff (polDY D s Q (N' := N')) α ∈ WtPol ℂ (extNu N' ν) := by
    intro α β hβ
    have hβ0 : ∀ τ r c, c < r → β τ r c = 0 := fun τ r c h => (hβ τ).1 r c h
    have hB : IsBor (fun τ => (β τ).submatrix (Fin.castLE hN) (Fin.castLE hN)) :=
      fun τ => ⟨fun r c h => (hβ τ).1 _ _ h, fun r => (hβ τ).2 _⟩
    have e1 := congrArg (AddMonoidAlgebra.coeff · α) (polDY_colSub D hN s Q β hβ0)
    have e2 : ∀ (c : ℂ) (P : MvPolynomial (GL3Theta.FrV D N) ℂ), polDY D s (c • P) (N' := N') = c • polDY D s P (N' := N') :=
      fun c P => by unfold polDY; exact map_smul _ c P
    rw [MvPolynomial.coeff_map, hQ _ hB, e2, MvPolynomial.coeff_smul] at e1
    have e3 : (∏ τ, ∏ r, β τ r r ^ extNu N' ν τ r) = ∏ τ, ∏ r, (β τ).submatrix (Fin.castLE hN) (Fin.castLE hN) r r ^ ν τ r := by
      refine Finset.prod_congr rfl fun τ _ => ?_
      symm
      refine Fintype.prod_of_injective (Fin.castLE hN) (Fin.castLE_injective hN) _ _ ?_ ?_
      · intro r hr
        have hr' : ¬ (r : ℕ) < N := fun h => hr ⟨⟨r, h⟩, rfl⟩
        simp only [extNu, dif_neg hr', pow_zero]
      · intro r
        simp only [extNu, Matrix.submatrix_apply, Fin.coe_castLE, dif_pos r.2]
    rw [e3]
    exact e1
  refine ⟨hc, fun Θ => ?_⟩
  unfold framePol
  refine Submodule.sum_mem _ fun α _ => ?_
  rw [mul_comm, ← MvPolynomial.smul_eq_C_mul]
  exact Submodule.smul_mem _ _ (hc α)

end GlobalTheory.TwV.DelA

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OperatorPolynomialCoeffsWeightExtendedByZeroStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.operatorPolynomial_coeffs_weight_extended_by_zero : ∀ (D : D7) {N N' : ℕ}, N ≤ N' → ∀ (s : D.what₂.Tau → ℂ) (ν : D.what₂.Tau → Fin N → ℕ) (Q : MvPolynomial (GL3Theta.FrV D N) ℂ), Q ∈ WtPol ℂ ν → (∀ α, AddMonoidAlgebra.coeff (polDY D s Q (N' := N')) α ∈ WtPol ℂ (extNu N' ν)) ∧ ∀ Θ : TaylorLogMetric.VC D N N' → ℂ, framePol D s Q Θ ∈ WtPol ℂ (extNu N' ν) := by
  first | exact @GlobalTheory.TwV.DelA.wt_polDY_framePol | exact GlobalTheory.TwV.DelA.wt_polDY_framePol | (intros; apply GlobalTheory.TwV.DelA.wt_polDY_framePol <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EvalBasisCoordsAgainstBlockAction
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EvalBasisCoordsAgainstBlockAction
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.DelA

open Formalism.BasicNotions NumberField Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG
open Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Act

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (P : Places p O Kf)

theorem substR_substR (R : Type) [CommRing R] (G G' : ∀ v, Fin (P.n' v) → Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) R)
    (Q : XR P R) : substR P R G (substR P R G' Q) = substR P R (fun v s => G' v s * G v s) Q := by
  have hc : (substR P R G).comp (substR P R G') = substR P R (fun v s => G' v s * G v s) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨v, s, a, t⟩
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [AlgHom.comp_apply, substR, MvPolynomial.aeval_X, map_sum, map_mul, MvPolynomial.aeval_C,
      MvPolynomial.algebraMap_eq, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => ?_
    rw [← mul_assoc, ← MvPolynomial.C_mul]
  exact congrArg (fun φ : XR P R →ₐ[R] XR P R => φ Q) hc

theorem natActR_natActR (R : Type) [Field R] (g g' : ∀ v, Fin (P.n' v) → GL (Fin (P.m + 1)) R) (Q : XR P R) :
    natActR P R g (natActR P R g' Q) = natActR P R (fun v s => g v s * g' v s) Q := by
  unfold natActR
  simp only [LinearMap.smul_apply, AlgHom.toLinearMap_apply, map_smul, smul_smul, substR_substR]
  congr 1
  · rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [Units.val_mul, Matrix.det_mul, mul_zpow, mul_comm]

theorem natActR_one (R : Type) [Field R] (Q : XR P R) : natActR P R (fun _ _ => 1) Q = Q := by
  have hs : substR P R (fun _ _ => 1) = AlgHom.id R (XR P R) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨v, s, a, t⟩
    simp only [substR, MvPolynomial.aeval_X, AlgHom.coe_id, id_eq, Matrix.one_apply]
    simp [ite_mul, Finset.sum_ite_eq]
  unfold natActR
  simp only [inv_one, Units.val_one, Matrix.det_one, one_zpow, Finset.prod_const_one, one_smul,
    LinearMap.smul_apply, AlgHom.toLinearMap_apply]
  rw [hs]
  rfl

end Act

theorem invT_mul {k : Type} [Fintype k] [DecidableEq k] (A B : GL k ℂ) : invT (A * B) = invT A * invT B := by
  ext : 1
  simp only [invT, Units.val_mk, Units.val_mul, mul_inv_rev, Matrix.transpose_mul]

theorem invT_one {k : Type} [Fintype k] [DecidableEq k] : invT (1 : GL k ℂ) = 1 := by
  ext : 1
  simp [invT]

variable {p : ℕ} [Fact p.Prime]

theorem evC_crdB_actC (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (i : ℕ) {n : ℕ}
    (h : (X.Pj i).m + 1 = n) (Gr : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (B M : GL (Fin n) D.host.E)
    (V : XR (X.Pj i) ℂ) (z : Frames Gr) (f : Fr1 D n)
    (hf : ∀ τ, f.1 τ = (atR D (M * B⁻¹) τ : Matrix (Fin n) (Fin n) ℂ) * z.1 τ) :
    evC (X.Pj i) h (posJ X D pos i) Gr (crdB (embT D) B) V z = ev1 X D pos i h (actC X D pos i h M V) f ∧
      actC X D pos i h M (actC X D pos i h M⁻¹ V) = V := by
  have hcr : ∀ τ, crdB (embT D) B τ = (atR D B⁻¹ τ : Matrix (Fin n) (Fin n) ℂ) := fun τ => rfl
  let y : Fr1 D n := ⟨fun τ => crdB (embT D) B τ * z.1 τ, fun τ => by
    rw [Matrix.det_mul, hcr]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 (atR D B⁻¹ τ).isUnit).mul (z.2 τ)⟩
  refine ⟨?_, ?_⟩
  · have hz : ∀ v s, zAt (X.Pj i) h (posJ X D pos i) (crdB (embT D) B) z.1 v s =
        zAt (X.Pj i) h (posJ X D pos i) (fun _ => 1) y.1 v s := by
      intro v s
      simp only [zAt, y, one_mul]
    have h1 : evC (X.Pj i) h (posJ X D pos i) Gr (crdB (embT D) B) V z = ev1 X D pos i h V y := by
      show (∏ v, ∏ s : Fin ((X.Pj i).n' v), (_ : ℂ)) * (_ : ℂ) = (∏ v, ∏ s : Fin ((X.Pj i).n' v), (_ : ℂ)) * (_ : ℂ)
      simp only [hz]
    have hy : IsTr (fun τ => (atR D M τ : Matrix (Fin n) (Fin n) ℂ)) y f := by
      intro τ
      rw [hf τ]
      show _ = (atR D M τ : Matrix (Fin n) (Fin n) ℂ) * (crdB (embT D) B τ * z.1 τ)
      rw [hcr, ← Matrix.mul_assoc, ← Units.val_mul]
      unfold atR
      rw [map_mul]
    have h2 := evC_natAct (X.Pj i) h (posJ X D pos i) (fun _ => 1) (fun _ => 1) (atR D M) y f hy V
    rw [h1]
    exact h2.symm
  · unfold actC
    rw [natActR_natActR]
    have he : (fun v s => hAt (X.Pj i) h (posJ X D pos i) (fun _ => 1) (atR D M) v s *
        hAt (X.Pj i) h (posJ X D pos i) (fun _ => 1) (atR D M⁻¹) v s) = fun _ _ => 1 := by
      funext v s
      have hm : ∀ τ, ((1 : GL (Fin n) ℂ) * atR D M τ * (1 : GL (Fin n) ℂ)⁻¹) * ((1 : GL (Fin n) ℂ) * atR D M⁻¹ τ * (1 : GL (Fin n) ℂ)⁻¹) = (1 : GL (Fin n) ℂ) := by
        intro τ
        simp only [one_mul, inv_one, mul_one, atR, ← map_mul, mul_inv_cancel, map_one]
      unfold hAt
      split_ifs
      · rw [← map_mul, hm, map_one]
      · rw [← invT_mul, ← map_mul, hm, map_one, invT_one]
    rw [he, natActR_one]

end GlobalTheory.TwV.DelA

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EvalBasisCoordsAgainstBlockActionStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evalBasisCoords_against_blockAction : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (i : ℕ) {n : ℕ} (h : (X.Pj i).m + 1 = n) (Gr : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (B M : GL (Fin n) D.host.E) (V : XR (X.Pj i) ℂ) (z : Frames Gr) (f : Fr1 D n), (∀ τ, f.1 τ = (atR D (M * B⁻¹) τ : Matrix (Fin n) (Fin n) ℂ) * z.1 τ) → evC (X.Pj i) h (posJ X D pos i) Gr (crdB (embT D) B) V z = ev1 X D pos i h (actC X D pos i h M V) f ∧ actC X D pos i h M (actC X D pos i h M⁻¹ V) = V := by
  first | exact @GlobalTheory.TwV.DelA.evC_crdB_actC | exact GlobalTheory.TwV.DelA.evC_crdB_actC | (intros; apply GlobalTheory.TwV.DelA.evC_crdB_actC <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OperatorMatricesAtComplexPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OperatorMatricesAtComplexPoint
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TwV.DelA

open Matrix

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)
  (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) {j : ℕ} (hN : RankTie X D j)
  (d : D.what₂.Tau → Matrix (Fin (D.R.N j)) (Fin (D.R.N (j + 1))) ℂ)
  (f' : D.what₂.Tau → Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ)

theorem evD_yMat (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    (yMat X Kc j v s).map (evD X D pos ι hN d f') =
      ((zT X D pos f' (pos ⟨v, s⟩)).map ι).submatrix (Fin.cast hN.2.symm) (Fin.cast hN.2.symm) := by
  ext b t
  simp only [Matrix.map_apply, yMat, evD, MvPolynomial.eval₂Hom_C, RingHom.coe_comp, Function.comp_apply,
    MvPolynomial.eval_X, Matrix.submatrix_apply]
  rfl

theorem evD_dMat (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    (dMat X Kc j v s).map (evD X D pos ι hN d f') =
      ((d (pos ⟨v, s⟩)).map ι).submatrix (Fin.cast hN.1.symm) (Fin.cast hN.2.symm) := by
  ext a b
  simp only [Matrix.map_apply, dMat, evD, MvPolynomial.eval₂Hom_X', Matrix.submatrix_apply]

theorem zT_even (v : X.Pl) (s : Fin (X.G.P.n' v)) (hs : ¬ IsOddPos s) {n : ℕ} (g : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) :
    zT X D pos g (pos ⟨v, s⟩) = g (pos ⟨v, s⟩) := by
  rw [zT, Equiv.symm_apply_apply, if_neg hs]

theorem zT_odd (v : X.Pl) (s : Fin (X.G.P.n' v)) (hs : IsOddPos s) {n : ℕ} (g : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) :
    zT X D pos g (pos ⟨v, s⟩) = ((g (pos ⟨v, s⟩))⁻¹).transpose.submatrix id Fin.rev := by
  rw [zT, Equiv.symm_apply_apply, if_pos hs]

theorem adj_zT_odd (v : X.Pl) (s : Fin (X.G.P.n' v)) (hs : IsOddPos s) {n : ℕ} (g : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ)
    (hg : (g (pos ⟨v, s⟩)).det ≠ 0) :
    (zT X D pos g (pos ⟨v, s⟩)).adjugate =
      (zT X D pos g (pos ⟨v, s⟩)).det • (g (pos ⟨v, s⟩)).transpose.submatrix Fin.rev id := by
  set z := zT X D pos g (pos ⟨v, s⟩) with hz
  have hmul : z * (g (pos ⟨v, s⟩)).transpose.submatrix Fin.rev id = 1 := by
    rw [hz, zT_odd X D pos v s hs g]
    have h1 : ((g (pos ⟨v, s⟩))⁻¹).transpose.submatrix id Fin.rev * (g (pos ⟨v, s⟩)).transpose.submatrix Fin.rev id =
        (((g (pos ⟨v, s⟩))⁻¹).transpose * (g (pos ⟨v, s⟩)).transpose).submatrix id id :=
      Matrix.submatrix_mul_equiv _ _ _ Fin.revPerm _
    rw [h1, ← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hg)]
    simp
  have hdet : z.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hmul
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  rw [← Matrix.inv_eq_right_inv hmul, Matrix.inv_def, smul_smul, Ring.inverse_eq_inv', mul_inv_cancel₀ hdet, one_smul]

theorem evD_blockMats {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)
    (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (j : ℕ) (hN : RankTie X D j)
    (d : D.what₂.Tau → Matrix (Fin (D.R.N j)) (Fin (D.R.N (j + 1))) ℂ)
    (f' : D.what₂.Tau → Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ) :
    (∀ τ, (f' τ).det ≠ 0) → (∀ τ, (dfr X D hN d f' τ).det ≠ 0) → ∀ (v : X.Pl) (s : Fin (X.G.P.n' v)),
      evD X D pos ι hN d f' (yMat X Kc j v s).det = ι (zT X D pos f' (pos ⟨v, s⟩)).det ∧
      (¬ IsOddPos s → (dyMat X Kc j v s).map (evD X D pos ι hN d f') =
        ((dfr X D hN d f' (pos ⟨v, s⟩)).map ι).submatrix (Fin.cast hN.1.symm) (Fin.cast hN.1.symm)) ∧
      (IsOddPos s → (YtMat X Kc j v s).map (evD X D pos ι hN d f') =
        ι (zT X D pos f' (pos ⟨v, s⟩)).det • (((dfr X D hN d f' (pos ⟨v, s⟩)).transpose.submatrix Fin.rev id).map ι).submatrix
          (Fin.cast hN.1.symm) (Fin.cast hN.1.symm)) := by
  intro hf _ v s
  refine ⟨?_, ?_, ?_⟩
  · rw [RingHom.map_det, RingHom.mapMatrix_apply, evD_yMat, ι.map_det]
    exact Matrix.det_submatrix_equiv_self (finCongr hN.2.symm) _
  · intro hs
    rw [dyMat, ← Matrix.submatrix_map, Matrix.map_mul, evD_yMat, evD_dMat, zT_even X D pos v s hs]
    rw [show ((d (pos ⟨v, s⟩)).map ι).submatrix (Fin.cast hN.1.symm) (Fin.cast hN.2.symm) *
        ((f' (pos ⟨v, s⟩)).map ι).submatrix (Fin.cast hN.2.symm) (Fin.cast hN.2.symm) =
        ((d (pos ⟨v, s⟩)).map ι * (f' (pos ⟨v, s⟩)).map ι).submatrix (Fin.cast hN.1.symm) (Fin.cast hN.2.symm) from
      Matrix.submatrix_mul_equiv _ _ _ (finCongr hN.2.symm) _]
    rw [← Matrix.map_mul, Matrix.submatrix_submatrix, dfr, ← Matrix.submatrix_map, Matrix.submatrix_submatrix]
    ext a t
    rfl
  · intro hs
    have hz := hf (pos ⟨v, s⟩)
    have hY : (yMat X Kc j v s).adjugate.map (evD X D pos ι hN d f') =
        (((zT X D pos f' (pos ⟨v, s⟩)).det • (f' (pos ⟨v, s⟩)).transpose.submatrix Fin.rev id).map ι).submatrix
          (Fin.cast hN.2.symm) (Fin.cast hN.2.symm) := by
      have h1 : (yMat X Kc j v s).adjugate.map (evD X D pos ι hN d f') =
          ((yMat X Kc j v s).map (evD X D pos ι hN d f')).adjugate := RingHom.map_adjugate _ _
      rw [h1, evD_yMat, ← adj_zT_odd X D pos v s hs f' hz]
      rw [show (((zT X D pos f' (pos ⟨v, s⟩)).map ι).submatrix (Fin.cast hN.2.symm) (Fin.cast hN.2.symm)).adjugate =
          ((zT X D pos f' (pos ⟨v, s⟩)).map ι).adjugate.submatrix (Fin.cast hN.2.symm) (Fin.cast hN.2.symm) from
        Matrix.adjugate_submatrix_equiv_self (finCongr hN.2.symm) _]
      congr 1
      exact (RingHom.map_adjugate ι _).symm
    rw [YtMat, Matrix.map_mul, ← Matrix.submatrix_map, hY, Matrix.transpose_map, evD_dMat, Matrix.transpose_submatrix,
      Matrix.submatrix_submatrix]
    have hrev : ∀ t : Fin (NN X.G.P.m X.t j),
        Fin.rev (Fin.cast hN.2.symm (shiftI X j t)) = Fin.castLE (rk_le X D hN) (Fin.rev (Fin.cast hN.1.symm t)) := by
      intro t
      have h1 := hN.1
      have h2 := hN.2
      have h3 := rk_le X D hN
      have := t.isLt
      ext
      simp only [Fin.val_rev, Fin.coe_cast, Fin.coe_castLE, shiftI]
      omega
    ext t a
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.transpose_apply,
      Function.comp_apply, id, smul_eq_mul, dfr, map_mul, map_sum]
    rw [hrev, Finset.mul_sum]
    refine Fintype.sum_equiv (finCongr hN.2.symm) _ _ (fun b => ?_)
    simp only [finCongr_apply]
    ring

end GlobalTheory.TwV.DelA
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OperatorMatricesAtComplexPointStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.operatorMatrices_at_complexPoint : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (j : ℕ) (hN : RankTie X D j) (d : D.what₂.Tau → Matrix (Fin (D.R.N j)) (Fin (D.R.N (j + 1))) ℂ) (f' : D.what₂.Tau → Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ), (∀ τ, (f' τ).det ≠ 0) → (∀ τ, (dfr X D hN d f' τ).det ≠ 0) → ∀ (v : X.Pl) (s : Fin (X.G.P.n' v)), evD X D pos ι hN d f' (yMat X Kc j v s).det = ι (zT X D pos f' (pos ⟨v, s⟩)).det ∧ (¬ IsOddPos s → (dyMat X Kc j v s).map (evD X D pos ι hN d f') = ((dfr X D hN d f' (pos ⟨v, s⟩)).map ι).submatrix (Fin.cast hN.1.symm) (Fin.cast hN.1.symm)) ∧ (IsOddPos s → (YtMat X Kc j v s).map (evD X D pos ι hN d f') = ι (zT X D pos f' (pos ⟨v, s⟩)).det • (((dfr X D hN d f' (pos ⟨v, s⟩)).transpose.submatrix Fin.rev id).map ι).submatrix (Fin.cast hN.1.symm) (Fin.cast hN.1.symm)) := by
  first | exact @GlobalTheory.TwV.DelA.evD_blockMats | exact GlobalTheory.TwV.DelA.evD_blockMats | (intros; apply GlobalTheory.TwV.DelA.evD_blockMats <;> assumption)
end
end
