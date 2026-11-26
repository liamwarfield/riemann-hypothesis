module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelExtensionFirst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorForUnipotentMatrix
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdaptedPlaneConstant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBijectionRightInverse
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenContinuousInverse
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyLocalIntegralPointsMemOpenSubgroupDefi
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalStabilizerDoubledVacuumEigenvalueEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfTraceMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIntertwinerRepTrivialRealPoints
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictionLineOperatorSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalTwoFormEqSumWedgeGlobalOneForms

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockCoefficientMapExtremalEqPhaseSmulLetters
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefMapNormEquivariantBasisAlt
noncomputable section

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.OverCore


set_option maxHeartbeats 800000 in
theorem coefMap_norm_equivariant_basis : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → TieIn T R κ v₀ → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → ‖O.c0' O.hw‖ = 1 ∧ (∀ (γ : GQ (Vc D i)) (γE : GL (Fin (Vc D i).rank) D.host.E), Bridge.IsRatMat (Vc D i) γ γE → ∀ v, O.c0' (rhoM O.c' (fun τ => embF O.c' (tauE D τ)) (lamV D i) (γE : Matrix _ _ D.host.E) v) = (R.cV i).ρ γ (O.c0' v)) ∧ Submodule.span ℂ (Set.range O.c0') = ⊤ ∧ ∀ (m : ℕ) (b : Fin m → VsV D i O.c'.F), LinearIndependent O.c'.F b → LinearIndependent ℂ (fun j => O.c0' (b j)) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ _ _ i Tp tup O hP
  obtain ⟨gramR, c0R, c0L, hT, hc⟩ := hP.lift.c0
  have hσ := hP.lift.field
  have hE : ∀ v, O.c0' (GlobalTheory.AdTh.CoefExt.up O.jL (lamV D i) v) = c0L i v := by
    intro v
    obtain ⟨w, hw, h⟩ := hc v
    rw [show GlobalTheory.AdTh.CoefExt.up O.jL (lamV D i) v = w from Subtype.ext hw.symm]
    exact h
  obtain ⟨h1, h2, h3⟩ := hT.mapL i
  refine ⟨?_, ?_, GlobalTheory.AdTh.CoefExt.span_top (W := (R.cV i).W) hE h3,
    fun m b hb => GlobalTheory.AdTh.CoefExt.linearIndependent (W := (R.cV i).W) hE h2 b hb⟩
  · have hn := GlobalTheory.StdFrame.neg_eq_false_of_vStd D i hP.lift.std
    have hg : (D.sp.V ((i : ℕ) + 1)).gram = 1 := hP.lift.std.1
    let v : VsV D i D.what₂.LL := ⟨Formalism.L2.DIV.ten fun τ => Formalism.BasicNotions.extremal D.what₂.LL _ (lamV D i τ),
      GlobalTheory.Proof.TensorMapDescent.ten_mem _ _ fun τ => Formalism.GradedWeylDivisibility.hwMem _ _ _ le_rfl _ (Formalism.L2.DIV.natW_antitone _)⟩
    have hv : GlobalTheory.AdTh.CoefExt.up O.jL (lamV D i) v = O.hw := by
      apply Subtype.ext
      have hw := hP.io.1
      unfold hwOK at hw
      refine Eq.trans ?_ hw.symm
      show MvPolynomial.map O.jL (Formalism.L2.DIV.ten _) = _
      rw [GlobalTheory.Proof.TensorMapDescent.map_ten]
      congr 1
      funext τ
      exact Formalism.L2.DIV.map_extremal _ _ _
    have hG : (if D.sp.Vneg ((i : ℕ) + 1) then -(D.sp.V ((i : ℕ) + 1)).gram else (D.sp.V ((i : ℕ) + 1)).gram) = 1 := by
      rw [hn, hg]; rfl
    have hi := GlobalTheory.AdTh.inner_of_coefTie (hT.coefL i A.μ0) v v
    rw [hG] at hi
    replace hi := hi.trans ((congrArg D.what₂.embLL (GlobalTheory.AdTh.CoefExt.pairVr_extremal (labLL D) v rfl)).trans (map_one _))
    rw [← hv, hE]
    have hi' : inner ℂ (c0L i v : (R.cV i).W) (c0L i v : (R.cV i).W) = 1 := hi
    rw [inner_self_eq_norm_sq_to_K] at hi'
    have h4 : ‖(c0L i v : (R.cV i).W)‖ ^ 2 = 1 := by
      have h5 := congrArg norm hi'
      simpa using h5
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h4
  · intro γ γE hγ v
    have hu : IsUnit (γE.val).det := (Matrix.isUnit_iff_isUnit_det γE.val).1 γE.isUnit
    have hγE : Matrix.nonsingInvUnit γE.val hu = γE := Units.ext rfl
    have hemb : (fun τ => embF O.c' (tauE D τ)) = fun τ => O.jL.comp (labLL D τ) :=
      funext fun τ => (embV_eq_embF O.c' O.jL hσ τ).symm
    rw [rhoM, dite_eq_left hu, hγE, hemb]
    exact GlobalTheory.AdTh.CoefExt.equivariant (W := (R.cV i).W) hE ((R.cV i).ρ γ) (Formalism.L2.DIV.rhoVr (labLL D) (lamV D i) γE) _
      (GlobalTheory.AdTh.CoefExt.up_rhoVr O.jL (lamV D i) (labLL D) γE) (h1 γ γE hγ) v

end GlobalTheory.AdTh.OverCore

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockCoefficientMapExtremalEqPhaseSmulLetters
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdTh.PhaseMapCore
open GlobalTheory.AdTh.PhaseMap


set_option maxHeartbeats 1600000 in
theorem io_eq_phase_smul_core : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → TieIn T R κ v₀ → IoExt R → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → ∃ ka : ℂ, ‖ka‖ = 1 ∧ ∀ (lt : LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank → FVar D (Wc D i).rank (Vc D i).rank), (∀ ℓ, (lt ℓ).2.2 = ℓ.2.2 ∧ ((ℓ.1 = tauE D (lt ℓ).1 ∧ ((lt ℓ).2.1 : ℕ) = ℓ.2.1) ∨ (ℓ.1 = conjEmb (tauE D (lt ℓ).1) ∧ ((lt ℓ).2.1 : ℕ) = (T.Q.Dw ((i : ℕ) + 1)).p + ℓ.2.1))) → ∀ (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ), (∀ ρ, (u ρ : (R.MW i (sg0 D A)).sm ρ) = v₀ i (sg0 D A) ρ) → ∀ (t : T0) (v : VsV D i O.c'.F), R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ u) (O.c0' v)) = ka • pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (fun _ => 1) (onb (R.MW i (sg0 D A))) (R.vP i t) (MvPolynomial.rename lt (MvPolynomial.map (inC O.c') (O.io v))) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hR hT hE i Tp tup O hO
  have hstd := hO.lift.std
  have hθ : IsInfFam R.θ := hR.models.inf
  have hc : (R.cV i).Is := hR.models.cV i
  have hP := (GlobalTheory.AdTh.RecPairCore.isPair_record_core D G Pl0 T0 A _ R F hR i A.μ0 hstd).1
  have hψ := hP.weil.std
  have hF := fun t => GlobalTheory.AdTh.VecFockCore.vec_fock_core D G Pl0 T0 A _ R F hR i t hstd
  obtain ⟨f1, f2, f3, f4, f5⟩ := hF A.μ0
  obtain ⟨n1, n2, n3, n4⟩ := GlobalTheory.AdTh.OverCore.coefMap_norm_equivariant_basis D G Pl0 T0 A T R F κ v₀ hR hT i Tp tup O hO
  obtain ⟨r1, r2, -⟩ := GlobalTheory.RatGen.rational_points_generate D (Vc D i) (R.cV i) (hR.models.vpos i) hP.sigV hc
  obtain ⟨-, -, w1, w2, w3⟩ := GlobalTheory.WeightExponents.weight_exponents D T.Q hT.laws.pins _ (inR i) (κ i)
  have hty : IsTyp D T.Q.H := ⟨w1, w2⟩
  obtain ⟨d1, d2, -⟩ := hT.laws.pins.2.2.2 _ (inR i)
  have hsig : ∀ τ, (Wc D i).sig (tauE D τ) = D.R.sigW ((i : ℕ) + 1) := fun τ => D.sp.W_sigval _ (inR i).1 (inR i).2 _
  obtain ⟨-, cga, i1, i2, -, i3, -, -, i4, -⟩ := hO.io
  obtain ⟨u₀, w₀, hu₀, hw₀, hΔ⟩ : ExtremalVectorPairsToDelta R i (v₀ i (sg0 D A)) := (hT.hv₀ i (sg0 D A)).2 rfl (hE i)
  have hio := (hR.thP.ioP i A.μ0).1
  have hBV : ∀ τ, (R.BV i τ)ᴴ * R.BV i τ = 1 := fun τ => by
    obtain ⟨ε, hε, h1, -⟩ := hR.models.BV i τ
    rw [gramAt_one hP.std, Matrix.mul_one] at h1
    rw [h1, ← Matrix.diagonal_one]
    congr 1
    funext a
    rcases hε a with h | h
    · rw [h.1]; rfl
    · exact absurd a.2 (not_lt.2 h.2)
  have hon : ∀ τ, IsONBasis (gramAt D (Vc D i) τ) 1 1 (Vc D i).rank := fun τ =>
    ⟨fun _ => 1, fun a => Or.inl ⟨rfl, a.2⟩, by simp [gramAt_one hP.std], by simp⟩
  let PT := fun t => pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (fun _ => 1)
    (onb (R.MW i (sg0 D A))) (R.vP i t)
  have hsub : ∀ t (U : D.what₂.Tau → Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) ℂ), (∀ τ, (U τ)ᴴ * U τ = 1) → ∀ P,
      pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) U (onb (R.MW i (sg0 D A))) (R.vP i t) P =
        PT t (sub (fun τ => ((Wc D i).sig (tauE D τ)).1) U P) := fun t U hU P => by
    have h := GlobalTheory.AdTh.SourceBasis.pureTensorO_mul_source D R.ψ R.θ (Vc D i) (Wc D i) hψ hθ (fun _ => 1) U _ _ _ f5
      (fun τ => (trace_parity (f5 τ)).1) (fun τ => by simp) (fun τ => det_ne_zero (hU τ)) _ (hF t).1 P
    simp only [Matrix.one_mul] at h
    exact h
  have hinj : Function.Injective (PT A.μ0) :=
    GlobalTheory.FockVecInj.pureTensorO_injective D R.ψ R.θ (Vc D i) (Wc D i) hψ hθ _ _ _ _ _ _ f4 f3 hon f5 hP.sigV hP.sigW _ f1 f2
      (GlobalTheory.AdTh.VecNeCore.thetaVector_ne_zero_core D G Pl0 T0 A _ R F hR i hstd)
  obtain ⟨g, hg, hgB⟩ : ∃ g ∈ GinfC (Vc D i), ∀ τ, compAt R.θ τ (Formalism.L2.Theta.mt (Vc D i) g) = R.BV i τ :=
    (GlobalTheory.SmoothForms.RealPts.glue R.θ hθ (Vc D i)).2 (R.BV i) fun τ => by
      show (R.BV i τ)ᴴ * gramAt D (Vc D i) τ * R.BV i τ = gramAt D (Vc D i) τ
      rw [gramAt_one hP.std, Matrix.mul_one, hBV]
  obtain ⟨χ, hχ, hχg⟩ := om_real hP f4 f3 f5 f1 f2 hg
  rw [funext hgB] at hχg
  have hχ0 : χ ≠ 0 := fun h => by simp [h] at hχ
  let A₀ : (R.cV i).W →ₗ[ℂ] (WO (Vc D i) (Wc D i) → ℂ) :=
    pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A)))
      (R.vP i A.μ0) ∘ₗ R.ioP i (PiTensorProduct.tprod ℂ u₀)
  have hA₀ : ∀ a ∈ GinfC (Vc D i), ∀ w, A₀ ((R.cV i).ρ a w) = R.ωP i A.μ0 (a, 1) (A₀ w) :=
    fun a ha w => (hio a ha _ w).symm
  have hw₁ : A₀ ((R.cV i).ρ g⁻¹ (χ • w₀)) = PT A.μ0 (RealDat.Delta i) := by
    have h1 : A₀ (χ • w₀) = R.ωP i A.μ0 (g, 1) (PT A.μ0 (RealDat.Delta i)) := by
      rw [map_smul, hχg, ← hΔ]
      rfl
    rw [hA₀ _ (inv_mem hg), h1, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, inv_mul_cancel, mul_one]
    exact congrArg (fun T : Module.End ℂ _ => T _) (map_one (R.ωP i A.μ0))
  have hn₁ : ‖(R.cV i).ρ g⁻¹ (χ • w₀)‖ = 1 := by
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), hc.2.1, ← norm_eq_sqrt_re_inner, norm_smul, hχ, hw₀, mul_one]
  haveI := hc.2.2.2.1
  haveI : FiniteDimensional O.c'.F (VsV D i O.c'.F) := Module.Finite.of_basis (Formalism.L2.DIV.bVV O.c'.F (lamV D i))
  have main : ∀ lt : LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank → FVar D (Wc D i).rank (Vc D i).rank, IsLt lt →
      ∃ a : ℂ, a • (R.cV i).ρ g⁻¹ (χ • w₀) = O.c0' O.hw ∧ ∀ t v, R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ u₀) (O.c0' v)) =
        a • PT t (toF O.c' lt (O.io v)) := fun lt hl => by
    have hsm : ∀ (a : O.c'.F) P, toF O.c' lt (a • P) = (a : ℂ) • toF O.c' lt P := fun a P => by
      rw [MvPolynomial.smul_eq_C_mul, map_mul, toF_C, MvPolynomial.smul_eq_C_mul]
    set_option synthInstance.maxHeartbeats 400000 in
      obtain ⟨B₀, hB₀⟩ := exists_ext O.c0' n4
        { toFun := fun v => toF O.c' lt (O.io v)
          map_add' := fun v w => by rw [map_add (f := _), map_add (f := _)]
          map_smul' := fun a v => by rw [map_smul, hsm]; rfl }
    replace hB₀ : ∀ v, B₀ (O.c0' v) = toF O.c' lt (O.io v) := hB₀
    have hpG : toF O.c' lt (O.io O.hw) = RealDat.Delta i := by
      rw [i4]
      refine toF_pG O.c' hl hty i1 _ _ _ _ _ (fun τ => by rw [hsig, d1]) (fun τ => by rw [hsig, d2]) (fun τ k hk => ?_)
        fun τ k hk => ?_
      · rw [d1] at hk
        exact (w3 τ k).1.trans ((dif_pos hk).trans ((hT.kap i τ).1 ⟨k, hk⟩))
      · rw [d2] at hk
        exact (w3 τ k).2.trans ((dif_pos hk).trans ((hT.kap i τ).2.1 ⟨k, hk⟩))
    obtain ⟨a, ha, ha'⟩ := proportional ((R.cV i).ρ.comp (GQ (Vc D i)).subtype) _ r1 (fun γ hγ => hγ) r2 A₀ (PT A.μ0 ∘ₗ B₀)
      (fun γ => by
        obtain ⟨γE, a, k, h1, h2, h3, h4, h5, h6⟩ := rat_parts hθ hP.std γ
        obtain ⟨x, hx, hxa⟩ := om_real hP f4 f3 f5 f1 f2 h2
        have hx0 : x ≠ 0 := fun h => by simp [h] at hx
        have h7 : (R.cV i).ρ γ = (R.cV i).ρ a := by rw [h4, map_mul, hc.1 k h3, mul_one]
        refine ⟨R.ωP i A.μ0 (a, 1), (cga γE.val : ℂ) * x⁻¹, fun w => ?_, fun w => ?_⟩
        · show A₀ ((R.cV i).ρ γ w) = _
          rw [h7, hA₀ a h2]
        · have h8 : (PT A.μ0 ∘ₗ B₀) ∘ₗ (R.cV i).ρ γ =
              ((cga γE.val : ℂ) * x⁻¹) • (R.ωP i A.μ0 (a, 1) ∘ₗ (PT A.μ0 ∘ₗ B₀)) := by
            refine LinearMap.ext_on_range n3 fun v => ?_
            simp only [LinearMap.comp_apply, LinearMap.smul_apply]
            rw [← n2 γ γE h1, hB₀, hB₀, i3 _ h5, hsm, hxa, hsub _ _ (compAt_unitary hθ hP.std a), smul_smul,
              inv_mul_cancel_right₀ hx0, map_smul,
              toF_gaStar O.c' hl hty (fun τ => ((Wc D i).sig (tauE D τ)).1) (fun τ => by rw [hsig, d1]) _ _ h6]
          exact LinearMap.congr_fun h8 w)
      ((R.cV i).ρ g⁻¹ (χ • w₀)) (O.c0' O.hw) (by rw [hw₁, LinearMap.comp_apply, hB₀, hpG])
      (fun h => by
        rw [LinearMap.comp_apply, hB₀, map_eq_zero_iff _ hinj, map_eq_zero_iff _ (toF_injective O.c' hl hty),
          map_eq_zero_iff _ i2] at h
        rw [h, map_zero, norm_zero] at n1
        exact zero_ne_one n1)
    refine ⟨a, ha', fun t v => ?_⟩
    have h9 : sub (fun τ => ((Wc D i).sig (tauE D τ)).1) (R.BV i) (R.ioP i (PiTensorProduct.tprod ℂ u₀) (O.c0' v)) =
        a • toF O.c' lt (O.io v) := hinj (by rw [← hsub _ _ hBV, map_smul, ← hB₀]; exact ha _)
    rw [← map_smul, ← h9, ← hsub _ _ hBV]
    rfl
  by_cases hex : ∃ lt : LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank → FVar D (Wc D i).rank (Vc D i).rank, IsLt lt
  · obtain ⟨lt₀, hl₀⟩ := hex
    obtain ⟨a, ha, -⟩ := main lt₀ hl₀
    refine ⟨a, ?_, fun lt hl u hu t v => ?_⟩
    · rw [← n1, ← ha, norm_smul, hn₁, mul_one]
    · obtain rfl : u = u₀ := funext fun ρ => Subtype.ext ((hu ρ).trans (hu₀ ρ).symm)
      obtain ⟨b, hb, hb'⟩ := main lt hl
      obtain rfl : a = b := smul_left_injective ℂ (fun h => by simp [h] at hn₁) (ha.trans hb.symm)
      exact hb' t v
  · exact ⟨1, norm_one, fun lt hl => absurd ⟨lt, hl⟩ hex⟩

end GlobalTheory.AdTh.PhaseMapCore

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockCoefficientMapExtremalEqPhaseSmulLettersStatement
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockCoefficientMap_extremal_eq_phase_smul_letters : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → TieIn T R κ v₀ → IoExt R → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → ∃ ka : ℂ, ‖ka‖ = 1 ∧ ∀ (lt : LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank → FVar D (Wc D i).rank (Vc D i).rank), (∀ ℓ, (lt ℓ).2.2 = ℓ.2.2 ∧ ((ℓ.1 = tauE D (lt ℓ).1 ∧ ((lt ℓ).2.1 : ℕ) = ℓ.2.1) ∨ (ℓ.1 = conjEmb (tauE D (lt ℓ).1) ∧ ((lt ℓ).2.1 : ℕ) = (T.Q.Dw ((i : ℕ) + 1)).p + ℓ.2.1))) → ∀ (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ), (∀ ρ, (u ρ : (R.MW i (sg0 D A)).sm ρ) = v₀ i (sg0 D A) ρ) → ∀ (t : T0) (v : VsV D i O.c'.F), R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ u) (O.c0' v)) = ka • pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (fun _ => 1) (onb (R.MW i (sg0 D A))) (R.vP i t) (MvPolynomial.rename lt (MvPolynomial.map (inC O.c') (O.io v))) := by
  first | exact @GlobalTheory.AdTh.PhaseMapCore.io_eq_phase_smul_core | exact GlobalTheory.AdTh.PhaseMapCore.io_eq_phase_smul_core | (intros; apply GlobalTheory.AdTh.PhaseMapCore.io_eq_phase_smul_core <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceCharacterAndTranslationCoordsSurjectiv
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceCharacterAndTranslationCoordsSurjectiv
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)

namespace GlobalTheory.FlipOnto

theorem det_ne_zero_of_isSkew {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {B : Base F E} {n r s : ℕ} {X : Spc F E n} (hX : X.IsSkew σ B r s) : X.J.det ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have h := GlobalTheory.det_ne_zero_of_hasSig (hX.sig w)
  rw [Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at h
  intro h0
  exact h (by rw [h0, map_zero, mul_zero])

theorem det_ne_zero_of_isHerm {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {B : Base F E} {n r s : ℕ} {X : Spc F E n} (hX : X.IsHerm σ B r s) : X.J.det ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have h := GlobalTheory.det_ne_zero_of_hasSig (hX.sig w)
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det] at h
  intro h0
  exact h (by rw [h0, map_zero])

theorem isUnit_det_map {F E K : Type} [Field F] [Field E] [Field K] [Algebra F E] [Algebra F K] (t : E →ₐ[F] K)
    {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : J.det ≠ 0) : IsUnit (J.map t).det := by
  have : (J.map t).det = t J.det := by
    rw [← AlgHom.coe_toRingHom, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  rw [this, isUnit_iff_ne_zero]
  exact (map_ne_zero_iff _ t.toRingHom.injective).mpr hJ

theorem coX_coY_onto : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (n d r s r' s' : ℕ) (X : Spc F E n) (W : Spc F E d), X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (bb : GL (Fin n) (Fv F v)) (cc : GL (Fin d) (Fv F v)) (Z : Matrix (Fin n) (Fin d) (Fv F v)),
    (∃ z : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) z ∧ z.map (piW (t.comp σ)) = 0 ∧ GlobalTheory.FlipMatch.coX t bb cc z = Z) ∧
    (∃ z : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) z ∧ z.map (piW t) = 0 ∧ GlobalTheory.FlipMatch.coY σ X W t bb cc z = Z) := by
  intro F E _ _ _ _ _ σ B hB n d r s r' s' X W hX hW v t bb cc Z
  constructor
  · obtain ⟨u, hu, h0, h1⟩ := GlobalTheory.SplitComps.exists_mat_comps hB.cm v t (bb.1 * Z * cc.1ᵀ) 0
    refine ⟨u, hu, h1, ?_⟩
    have hc : cc.1ᵀ * (cc⁻¹).1ᵀ = 1 := by
      rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]
    unfold GlobalTheory.FlipMatch.coX
    rw [h0, Matrix.mul_assoc, Matrix.mul_assoc, hc, Matrix.mul_one, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  · have hA : IsUnit (bb.1ᵀ * X.J.map t).det := by
      rw [Matrix.det_mul, Matrix.det_transpose]
      exact (Units.isUnit (Matrix.GeneralLinearGroup.det bb)).mul (isUnit_det_map t (det_ne_zero_of_isHerm hX))
    have hC : IsUnit ((W.J.map t)ᵀ * cc.1).det := by
      rw [Matrix.det_mul, Matrix.det_transpose]
      exact (isUnit_det_map t (det_ne_zero_of_isSkew hW)).mul (Units.isUnit (Matrix.GeneralLinearGroup.det cc))
    obtain ⟨u, hu, h0, h1⟩ := GlobalTheory.SplitComps.exists_mat_comps hB.cm v t 0
      (-((bb.1ᵀ * X.J.map t)⁻¹ * Z * ((W.J.map t)ᵀ * cc.1)⁻¹))
    refine ⟨u, hu, h0, ?_⟩
    unfold GlobalTheory.FlipMatch.coY
    rw [h1]
    calc -(bb.1ᵀ * X.J.map t * -((bb.1ᵀ * X.J.map t)⁻¹ * Z * ((W.J.map t)ᵀ * cc.1)⁻¹) * (W.J.map t)ᵀ * cc.1)
        = (bb.1ᵀ * X.J.map t * (bb.1ᵀ * X.J.map t)⁻¹) * Z * (((W.J.map t)ᵀ * cc.1)⁻¹ * ((W.J.map t)ᵀ * cc.1)) := by
          simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
      _ = Z := by
          rw [Matrix.mul_nonsing_inv _ hA, Matrix.nonsing_inv_mul _ hC, Matrix.one_mul, Matrix.mul_one]

end GlobalTheory.FlipOnto
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceCharacterAndTranslationCoordsSurjectivStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_characterAndTranslationCoords_surjective : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (n d r s r' s' : ℕ) (X : Spc F E n) (W : Spc F E d), X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (bb : GL (Fin n) (Fv F v)) (cc : GL (Fin d) (Fv F v)) (Z : Matrix (Fin n) (Fin d) (Fv F v)),
    (∃ z : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) z ∧ z.map (piW (t.comp σ)) = 0 ∧ GlobalTheory.FlipMatch.coX t bb cc z = Z) ∧
    (∃ z : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) z ∧ z.map (piW t) = 0 ∧ GlobalTheory.FlipMatch.coY σ X W t bb cc z = Z) := by
  exact @GlobalTheory.FlipOnto.coX_coY_onto
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenBijectiveGoodModel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenBijectiveGoodModel
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open scoped Matrix ENNReal

noncomputable section

namespace GlobalTheory.ModelAdmUnconditional

open Filter
open scoped Classical

theorem model_admissible_iff_evaluation : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ M₁ : Model σ X W, M₁.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d, IsEv B M M₁ 1 1 ∅ e → Set.BijOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) →
    ∀ l : Fn F n d →ₗ[ℂ] ℂ, l ∈ (adeleClass F).adm (Fin n × Fin d) ↔ l ∘ₗ e ∈ (adeleClass F).adm (Fin n × Fin d) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP M₁ hM₁ e hE hbij l
  constructor
  · intro hl
    exact GlobalTheory.T.eigen_intertwiner_good_models F E σ B n d n d X W X W M M₁ 1 1 ∅ e hP.good hM₁ hE l hl
  · intro hl g hg
    obtain ⟨m, c, φ, hφ, hstd, rfl⟩ := GlobalTheory.MixEvAdm.sb_decomp F (Fin n × Fin d) g hg
    obtain ⟨ei, ev, -, hev, hloc⟩ := hE.loc
    have hbi : Function.Bijective ei :=
      ⟨GlobalTheory.T.weil_eigen_injective_extends F E σ B n d X W M M₁ hP.good e hbij.injOn ei ev (fun v => (hev v).1) hloc,
        GlobalTheory.T.weil_eigen_surjective_extends F E σ B n d X W M M₁ hP.good hM₁ e hbij.surjOn ei ev hev hloc⟩
    obtain ⟨S, hS⟩ := GlobalTheory.T.schwartz_bijection_right_inverse _ _ ei hbi
    have hpre : ∀ j v, ∃ ψ ∈ SB (Fin n × Fin d → Fv F v), ev v ψ = φ j v ∧ (φ j v = M₁.vac v → ψ = M.vac v) := by
      intro j v
      by_cases h : φ j v = M₁.vac v
      · exact ⟨M.vac v, (hP.good.vac v).1, (hev v).1.trans h.symm, fun _ => rfl⟩
      · have h2 : φ j v ∈ (SB (Fin n × Fin d → Fv F v)).map (ev v) := (hev v).2.symm ▸ hφ j v
        obtain ⟨ψ, hψ, hψe⟩ := Submodule.mem_map.1 h2
        exact ⟨ψ, hψ, hψe, fun h' => (h h').elim⟩
    choose ψ hψSB hψev hψvac using hpre
    have hψfam : ∀ j, ∀ᶠ v in cofinite, ψ j v = M.vac v := fun j =>
      ((hstd j).and hM₁.std).mono fun v hv => hψvac j v (hv.1.trans hv.2.symm)
    have hψstd : ∀ j, ∀ᶠ v in cofinite,
        ψ j v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := fun j =>
      ((hψfam j).and hP.good.std).mono fun v hv => hv.1.trans hv.2
    have hG : ∀ j, (fun y : Fin n × Fin d → Af F => ∏ᶠ v, ψ j v fun i => evalV F v (y i)) ∈
        SB (Fin n × Fin d → Af F) := fun j =>
      ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV _ (hψSB j) (hψstd j),
        GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod _ (hψSB j) (hψstd j)⟩
    choose Tj hTj using fun j => hl _ (hG j)
    refine ⟨∑ j, c j • (Tj j).comp S, fun f => ?_⟩
    have hsplit : pureA F (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ)
        (∑ j, c j • fun y => ∏ᶠ v, φ j v fun i => evalV F v (y i)) =
        ∑ j, c j • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (φ j) := by
      funext x
      simp only [pureA, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_left_comm]
      rfl
    have hφe : ∀ j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (φ j) =
        e (pureA F ((S f : SInf F _) : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ)
          (fun y => ∏ᶠ v, ψ j v fun i => evalV F v (y i))) := by
      intro j
      have h1 := hloc (S f) (ψ j) (hψSB j) (hψfam j)
      rw [hS] at h1
      have h2 : (fun v => ev v (ψ j v)) = φ j := funext fun v => hψev j v
      rw [h2] at h1
      exact h1.symm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hsplit, map_sum, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, hφe j]
    simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.coe_comp', Function.comp_apply]
    rw [← hTj j (S f)]
    rfl

end GlobalTheory.ModelAdmUnconditional
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenBijectiveGoodModelStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open scoped Matrix ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_eigen_bijective_good_model : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ M₁ : Model σ X W, M₁.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d, IsEv B M M₁ 1 1 ∅ e → Set.BijOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) →
    ∀ l : Fn F n d →ₗ[ℂ] ℂ, l ∈ (adeleClass F).adm (Fin n × Fin d) ↔ l ∘ₗ e ∈ (adeleClass F).adm (Fin n × Fin d) := by
  first | exact @GlobalTheory.ModelAdmUnconditional.model_admissible_iff_evaluation | exact GlobalTheory.ModelAdmUnconditional.model_admissible_iff_evaluation | (intros; apply GlobalTheory.ModelAdmUnconditional.model_admissible_iff_evaluation <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledVacuumEigenvalueEqOneInertPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledVacuumEigenvalueEqOneInertPlace
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.DblVacSiegelV
open GlobalTheory.DblVacSiegel

theorem eigen_eq_one_of_diag : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ (d' : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J)) (Fin a × Fin (a + a'))),
    (∀ x : Matrix (Fin a) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), d'.e xᵀ = G.M.co.e x) →
    ∀ (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J))) ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a'))))
      (omd : GlobalTheory.DblVac.UD σ G.V →* Module.End ℂ (((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → AF F) → ℂ)),
    IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) d' dd →
    IsUWeilSplit (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) B.ψ (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J)) dd (X.β / X.α) (diagCols (Fin a)) omd →
    ∀ r : (Fin a × Fin (a + a') → AF F) → ℂ, Rest (evFin F v) (G.M.vac v) r → tens (evFin F v) (G.M.vac v) r ≠ 0 →
    ∀ p ∈ GlobalTheory.DblVac.KD σ G.V v, p ∈ GlobalTheory.DblVac.PDiag σ G.V → ∀ μ : ℂ,
      omd p (boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x))) =
        μ • boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x)) → μ = 1 := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hw hv d' _ dd omd hdd hW r hr h0 p hp hpd μ hμ
  obtain ⟨t, ht₀⟩ := hpd
  have ht : GlobalTheory.DblVac.matD p * (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) =
      (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * (t : Matrix (Fin a) (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) := ht₀
  have hF := hT.base.cm.1
  set Ψ := tens (evFin F v) (G.M.vac v) r with hΨ
  change omd p (boxFun Ψ (fun x => star (Ψ x))) =
    μ • boxFun Ψ (fun x => star (Ψ x)) at hμ
  have hS := GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ Ψ hr.2 _ (GlobalTheory.SchAConj.star_mem_schA F _ Ψ hr.2)
  have hl := lDiag_box_ne_zero hF hr.2 h0
  have hS0 : (boxFun Ψ fun x => star (Ψ x)) ≠ 0 := fun h => hl (by rw [h, map_zero])
  have hn := norm_eq_one_of_eigen hF hW.2.1.unit hS hS0 hμ
  have hrule := hW.2.2 _ DiagForm.lDiag_adm (fun z φ hφ => by
    have e : z * (diagCols (Fin a) : Matrix _ _ (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))ᵀ = Matrix.fromCols z z := by
      rw [diagCols, Matrix.transpose_fromRows, Matrix.mul_fromCols, Matrix.transpose_one, Matrix.mul_one]
    rw [e, Darboux.rho, hdd]
    exact DiagForm.lDiag_schr B.ψ _ _ hφ) p t ht _ hS
  have hvec : ∀ (g : GlobalTheory.DblVac.UD σ G.V) (s : Matrix (Fin a) (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
      GlobalTheory.DblVac.matD g * (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * s → ∀ z,
      (GlobalTheory.DblVac.matD g *ᵥ Sum.elim z z) ∘ Sum.inl = s *ᵥ z := fun g s hs z => by
    have e : ∀ z : Fin a → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) *ᵥ z = Sum.elim z z := fun z => by
      rw [diagCols, Matrix.fromRows_mulVec, Matrix.one_mulVec]
    rw [← e, Matrix.mulVec_mulVec, hs, ← Matrix.mulVec_mulVec, e]
    rfl
  have ht' : GlobalTheory.DblVac.matD p⁻¹ * (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) =
      (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * ((t⁻¹ : GL (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin a) (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) := by
    have e1 : GlobalTheory.DblVac.matD p⁻¹ * GlobalTheory.DblVac.matD p = 1 := p.1.inv_mul
    calc _ = GlobalTheory.DblVac.matD p⁻¹ * ((diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * (t : Matrix (Fin a) (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) *
          ((t⁻¹ : GL (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin a) (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, t.mul_inv, Matrix.mul_one]
      _ = _ := by rw [← ht, ← Matrix.mul_assoc, e1, Matrix.one_mul]
  have hwT : w ∉ above E (X.T : Set (Pl (F := F))) := fun h => hv (by rw [← under_eq_of_isInertAt hw]; exact h)
  have hunr : UnrAt (X.β / X.α) w := by
    rw [div_eq_mul_inv]
    exact (hT.chars.unrβ w hwT).mul (hT.chars.unrα w hwT).inv
  have hβ : (X.β / X.α) (Matrix.GeneralLinearGroup.det t) = 1 := by
    refine chr_det_eq_one G.V hT.geo.hV.lat hw hunr t (fun u hu => ?_) fun z hz => ?_
    · have e1 : (GlobalTheory.DblVac.matD p - 1) * (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) =
          (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * ((t : Matrix (Fin a) (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) - 1) := by
        rw [Matrix.sub_mul, Matrix.mul_sub, ht, Matrix.one_mul, Matrix.mul_one]
      have e2 : (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * (u • ((t : Matrix (Fin a) (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) - 1)) = 0 := by
        rw [Matrix.mul_smul, ← e1, ← Matrix.smul_mul, hp.1 u hu, Matrix.zero_mul]
      rw [diagCols, Matrix.fromRows_mul, Matrix.one_mul] at e2
      ext i j
      exact congrFun (congrFun e2 (Sum.inl i)) j
    · have hz' := hp.2 (Sum.elim z z) ⟨hz, hz⟩
      exact ⟨hvec p _ ht z ▸ hz'.1.1, hvec p⁻¹ _ ht' z ▸ hz'.2.1⟩
  have he := congrArg (DiagForm.lDiag F (Fin a × Fin (a + a'))) hμ
  rw [map_smul, smul_eq_mul] at he
  have hrule := he.symm.trans hrule
  rw [hβ, Circle.coe_one, one_mul] at hrule
  have hμ' := mul_right_cancel₀ hl hrule
  rw [hμ', Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg _) _)] at hn
  rw [hμ', hn, Complex.ofReal_one]

end GlobalTheory.DblVacSiegelV
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledVacuumEigenvalueEqOneInertPlaceStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledVacuum_eigenvalue_eq_one_inertPlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ (d' : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J)) (Fin a × Fin (a + a'))),
    (∀ x : Matrix (Fin a) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), d'.e xᵀ = G.M.co.e x) →
    ∀ (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J))) ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a'))))
      (omd : GlobalTheory.DblVac.UD σ G.V →* Module.End ℂ (((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → AF F) → ℂ)),
    IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) d' dd →
    IsUWeilSplit (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) B.ψ (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J)) dd (X.β / X.α) (diagCols (Fin a)) omd →
    ∀ r : (Fin a × Fin (a + a') → AF F) → ℂ, Rest (evFin F v) (G.M.vac v) r → tens (evFin F v) (G.M.vac v) r ≠ 0 →
    ∀ p ∈ GlobalTheory.DblVac.KD σ G.V v, p ∈ GlobalTheory.DblVac.PDiag σ G.V → ∀ μ : ℂ,
      omd p (boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x))) =
        μ • boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x)) → μ = 1 := by
  first | exact @GlobalTheory.DblVacSiegelV.eigen_eq_one_of_diag | exact GlobalTheory.DblVacSiegelV.eigen_eq_one_of_diag | (intros; apply GlobalTheory.DblVacSiegelV.eigen_eq_one_of_diag <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCovolumeCommonAdelicFixatorOfColumns
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomeomorphColumnFixatorCoreUnitaryGroup
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomeomorphColumnFixatorCoreUnitaryGroup
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem fixFrames_equiv_core : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∃ e : GAd σ J₀ ≃ₜ* (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J)), ∀ g, g ∈ ratPts σ J₀ ↔ (e g : GAd σ J) ∈ ratPts σ J := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF
  obtain ⟨e, econt, eprop, erat⟩ := GlobalTheory.T.exists_continuous_core_unitaryGroup_embedding F E σ n J j m C D Z J₀ hF
  have hJ₀ := GlobalTheory.UAut.det_isUnit hF.herm₀
  set p0 : Matrix (Fin m) (Fin n) (AF F ⊗[F] E) := adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) with hp0
  have p0Z : p0 * adMat F Z = 1 := by
    rw [hp0, ← Matrix.map_mul, Matrix.mul_assoc, hF.zz, Matrix.nonsing_inv_mul _ hJ₀,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hrec : ∀ g, (matHom _ σ J₀ g).1 = p0 * (matHom _ σ J (e g)).1 * adMat F Z := fun g => by
    rw [Matrix.mul_assoc, (eprop g).2.2, ← Matrix.mul_assoc, p0Z, Matrix.one_mul]
  have inj : Function.Injective e := fun g h hgh => by
    apply matHom_injective _ σ J₀
    apply Units.ext
    rw [hrec g, hrec h, hgh]
  have DJx : ∀ x ∈ fixG σ J D, adMat F (cT (σ : E →+* E) D * J) * (matHom _ σ J x).1 =
      adMat F (cT (σ : E →+* E) D * J) := by
    intro x hx
    have h1 : (matHom _ σ J x⁻¹).1 * adMat F D = adMat F D * (1 : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) := by
      rw [Matrix.mul_one]; exact (fixG σ J D).inv_mem hx
    have := GlobalTheory.UAut.form_mul_of_mul_cols h1
    rwa [inv_inv, Formalism.UG.cT_one, Matrix.one_mul] at this
  have surj : ∀ x ∈ fixG σ J C ⊓ fixG σ J D, ∃ g, e g = x := by
    intro x hx
    have hxC : (matHom _ σ J x).1 * adMat F C = adMat F C := (Subgroup.mem_inf.1 hx).1
    have hxD : (matHom _ σ J x).1 * adMat F D = adMat F D := (Subgroup.mem_inf.1 hx).2
    obtain ⟨g₀, b, h1, h2, -, -⟩ := GlobalTheory.T.exists_coreIsometry_of_fixes_isotropicFrame F E σ n J j m C D Z J₀ hF x (Subgroup.mem_inf.1 hx).1
    have hb : b = 0 := by
      rw [h2, DJx x (Subgroup.mem_inf.1 hx).2, ← Matrix.map_mul, hF.dz, Matrix.map_zero _ (map_zero _)]
    have aC : (matHom _ σ J (e g₀)).1 * adMat F C = adMat F C := (eprop g₀).1
    have aD : (matHom _ σ J (e g₀)).1 * adMat F D = adMat F D := (eprop g₀).2.1
    refine ⟨g₀, eq_of_frame_cols F E σ n J j m C D Z J₀ hF _ _ ?_ ?_ ?_⟩
    · rw [aC, hxC]
    · rw [(eprop g₀).2.2, h1, hb, Matrix.mul_zero, add_zero]
    · rw [aD, hxD]
  let f : GAd σ J₀ →* ↥(fixG σ J C ⊓ fixG σ J D) :=
    e.codRestrict _ (fun g => Subgroup.mem_inf.2 ⟨(eprop g).1, (eprop g).2.1⟩)
  have fbij : Function.Bijective f :=
    ⟨fun g h hgh => inj (congrArg Subtype.val hgh), fun x =>
      let ⟨g, hg⟩ := surj x.1 x.2; ⟨g, Subtype.ext hg⟩⟩
  let me := MulEquiv.ofBijective f fbij
  have hme : ∀ x, e (me.symm x) = x.1 := fun x => congrArg Subtype.val (me.apply_symm_apply x)
  have cM : Continuous (matHom (AF F) σ J) := (isEmbedding_matHom (AF F) σ J).continuous
  have contInv : Continuous me.symm := by
    haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
    haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
    rw [(isEmbedding_matHom (AF F) σ J₀).continuous_iff, Units.continuous_iff]
    constructor
    · have : (Units.val ∘ (matHom (AF F) σ J₀ ∘ me.symm)) =
          fun x => p0 * (matHom _ σ J x.1).1 * adMat F Z := funext fun x => by
        simp only [Function.comp_apply]; rw [hrec, hme]
      rw [this]
      exact (continuous_const.matrix_mul (Units.continuous_val.comp (cM.comp continuous_subtype_val))).matrix_mul
        continuous_const
    · have : (fun x => (((matHom (AF F) σ J₀ ∘ me.symm) x)⁻¹ : GL _ _).val) =
          fun x => p0 * ((matHom _ σ J x.1)⁻¹ : GL _ _).1 * adMat F Z := funext fun x => by
        simp only [Function.comp_apply]
        rw [← map_inv (matHom _ σ J₀), ← map_inv me.symm, hrec, hme, Subgroup.coe_inv, map_inv]
      rw [this]
      exact (continuous_const.matrix_mul (Units.continuous_coe_inv.comp (cM.comp continuous_subtype_val))).matrix_mul
        continuous_const
  refine ⟨{ toMulEquiv := me, continuous_toFun := continuous_induced_rng.2 econt, continuous_invFun := contInv }, ?_⟩
  intro g
  change g ∈ ratPts σ J₀ ↔ e g ∈ ratPts σ J
  refine ⟨erat g, fun hg => ?_⟩
  obtain ⟨g₀, b, -, -, h3, h4⟩ := GlobalTheory.T.exists_coreIsometry_of_fixes_isotropicFrame F E σ n J j m C D Z J₀ hF (e g) (eprop g).1
  have : g₀ = g := matHom_injective _ σ J₀ (Units.ext (h3.trans (hrec g).symm))
  exact this ▸ h4 hg

end GlobalTheory.SphEis
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomeomorphColumnFixatorCoreUnitaryGroupStatement
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_homeomorph_columnFixator_coreUnitaryGroup : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∃ e : GAd σ J₀ ≃ₜ* (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J)), ∀ g, g ∈ ratPts σ J₀ ↔ (e g : GAd σ J) ∈ ratPts σ J := by
  first | exact @GlobalTheory.SphEis.fixFrames_equiv_core | exact GlobalTheory.SphEis.fixFrames_equiv_core | (intros; apply GlobalTheory.SphEis.fixFrames_equiv_core <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCovolumeCommonAdelicFixatorOfColumns
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem isClosed_fixG {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {k : ℕ} (C : Matrix (Fin n) (Fin k) E) :
    IsClosed ((fixG σ J C : Subgroup (GAd σ J)) : Set (GAd σ J)) := by
  obtain ⟨_, _⟩ := GlobalTheory.StdPar.ring_facts (F := F) (E := E)
  exact isClosed_eq (GlobalTheory.StdPar.continuous_mat.matrix_mul continuous_const) continuous_const

theorem finCovol_fixG : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ (π : Measure (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J))) (DM : Set (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J))), π.IsHaarMeasure → IsFundamentalDomain ((ratPts σ J).subgroupOf (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J))) DM π → π DM ≠ ⊤ := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF π DM hπ hDM
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_homeomorph_columnFixator_coreUnitaryGroup F E σ n J j m C D Z J₀ hF
  have hcl : IsClosed ((fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J)) : Set (GAd σ J)) :=
    (isClosed_fixG σ J C).inter (isClosed_fixG σ J D)
  haveI : LocallyCompactSpace (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J)) := hcl.locallyCompactSpace
  haveI : Countable (ratPts σ J₀) := inferInstance
  exact GlobalTheory.T.covolume_ne_top_of_continuousMulEquiv_subgroup (GAd σ J₀) _ e (ratPts σ J₀) _ (fun g => by rw [he g]; rfl)
    (fun μ hμ 𝓕 h𝓕 => GlobalTheory.T.finiteVolume_adelicUnitaryQuotient F E σ hF.cm m J₀ hF.herm₀ μ hμ 𝓕 h𝓕) π DM hπ hDM

end GlobalTheory.SphEis
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCovolumeCommonAdelicFixatorOfColumnsStatement
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteCovolume_common_adelicFixatorOfColumns : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ (π : Measure (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J))) (DM : Set (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J))), π.IsHaarMeasure → IsFundamentalDomain ((ratPts σ J).subgroupOf (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J))) DM π → π DM ≠ ⊤ := by
  first | exact @GlobalTheory.SphEis.finCovol_fixG | exact GlobalTheory.SphEis.finCovol_fixG | (intros; apply GlobalTheory.SphEis.finCovol_fixG <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeGlobalOneFormsClosed
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExteriorDerivGlobalOneFormEqSumWedge
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExteriorDerivGlobalOneFormEqSumWedge
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem dOne_glob_eq_wsum : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R),
    HasFrame F → CohomZeroIsConstants F → ∀ w : Glob1 F, ∃ (n : ℕ) (u v : Fin n → Glob1 F), ClRel F w u v := by
  intro R _ C _ F hF hH w
  obtain ⟨n, u, v, h⟩ := twoForm_eq_wsum R C F hF hH (fun T ↦ dOne R (F.obj T) (w.1 T))
    (fun T T' φ ↦ by rw [pOm_dOne, ← w.2 φ])
  exact ⟨n, u, v, fun T ↦ congrFun h T⟩

end GlobalTheory.AbCoh
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExteriorDerivGlobalOneFormEqSumWedgeStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exteriorDeriv_globalOneForm_eq_sum_wedge : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), HasFrame F → CohomZeroIsConstants F → ∀ w : Glob1 F, ∃ (n : ℕ) (u v : Fin n → Glob1 F), ClRel F w u v := by
  first | exact @GlobalTheory.AbCoh.dOne_glob_eq_wsum | exact GlobalTheory.AbCoh.dOne_glob_eq_wsum | (intros; apply GlobalTheory.AbCoh.dOne_glob_eq_wsum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExteriorDerivSumWedgeSemilinearPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExteriorDerivSumWedgeSemilinearPullback
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem clRel_pullForm : ∀ (R R' : Type) [CommRing R] [CommRing R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (σ : R →+* R') (φ : X' ⟶ X) (h : φ ≫ s = s' ≫ spMap σ) (w : GlobForm s) (n : ℕ) (u v : Fin n → GlobForm s), ClRel (OAff s) w u v → ClRel (OAff s') (GlobalTheory.CechDR.pullForm h w) (fun k ↦ GlobalTheory.CechDR.pullForm h (u k)) (fun k ↦ GlobalTheory.CechDR.pullForm h (v k)) := by
  intro R R' _ _ X X' s s' σ φ h w n u v hw T'
  have hp : ∀ (ω : GlobForm s) (p : Pair φ), (GlobalTheory.CechDR.pullForm h ω).1 (Opposite.op p.1.1) =
      (semiHom_secPull h p).m1 (ω.1 (Opposite.op p.1.2)) :=
    fun ω p ↦ ((isPullForm_iff.1 (isPullForm_pullForm h ω)) p).symm
  have hg : ∀ (ω : GlobForm s') {T T' : AffOp X'} (a : T ⟶ T'), p1 (OAff s') a (ω.1 T) = ω.1 T' :=
    fun ω _ _ a ↦ (ω.2 a).symm
  rw [← sub_eq_zero]
  refine twoForm_sep_of_basis s' (pairFst φ) (pair_cover_affine φ s') T' _ fun t a ↦ ?_
  rw [map_sub, sub_eq_zero, pOm_dOne, hg]
  have e1 : ∀ k, pOm (OAff s') 2 a (wedge R' _ ((GlobalTheory.CechDR.pullForm h (u k)).1 T')
      ((GlobalTheory.CechDR.pullForm h (v k)).1 T')) = wedge R' _ ((GlobalTheory.CechDR.pullForm h (u k)).1 ((pairFst φ).obj t))
      ((GlobalTheory.CechDR.pullForm h (v k)).1 ((pairFst φ).obj t)) := fun k ↦
    (pOm_wedge (OAff s') a _ _).trans (by rw [hg, hg])
  refine Eq.trans ?_ ((map_sum (pOm (OAff s') 2 a) _ _).trans (Finset.sum_congr rfl fun k _ ↦ e1 k)).symm
  have key : ∀ p : Pair φ, dOne R' (Sec s' p.1.1.1) ((GlobalTheory.CechDR.pullForm h w).1 (Opposite.op p.1.1)) =
      ∑ k, wedge R' (Sec s' p.1.1.1) ((GlobalTheory.CechDR.pullForm h (u k)).1 (Opposite.op p.1.1))
        ((GlobalTheory.CechDR.pullForm h (v k)).1 (Opposite.op p.1.1)) := by
    intro p
    calc dOne R' (Sec s' p.1.1.1) ((GlobalTheory.CechDR.pullForm h w).1 (Opposite.op p.1.1))
        = dOne R' (Sec s' p.1.1.1) ((semiHom_secPull h p).m1 (w.1 (Opposite.op p.1.2))) :=
          congrArg _ (hp w p)
      _ = (semiHom_secPull h p).mOm 2 (dOne R (Sec s p.1.2.1) (w.1 (Opposite.op p.1.2))) :=
          (SemiHom.mOm_dOne _ _).symm
      _ = (semiHom_secPull h p).mOm 2 (wsum (OAff s) u v (Opposite.op p.1.2)) :=
          congrArg ((semiHom_secPull h p).mOm 2) (hw (Opposite.op p.1.2))
      _ = (semiHom_secPull h p).mOm 2 (∑ k, wedge R (Sec s p.1.2.1) ((u k).1 (Opposite.op p.1.2))
            ((v k).1 (Opposite.op p.1.2))) := rfl
      _ = ∑ k, (semiHom_secPull h p).mOm 2 (wedge R (Sec s p.1.2.1) ((u k).1 (Opposite.op p.1.2))
            ((v k).1 (Opposite.op p.1.2))) := map_sum _ _ _
      _ = ∑ k, wedge R' (Sec s' p.1.1.1) ((semiHom_secPull h p).m1 ((u k).1 (Opposite.op p.1.2)))
            ((semiHom_secPull h p).m1 ((v k).1 (Opposite.op p.1.2))) :=
          Finset.sum_congr rfl fun k _ ↦ SemiHom.mOm_wedge (semiHom_secPull h p) ((u k).1 (Opposite.op p.1.2))
            ((v k).1 (Opposite.op p.1.2))
      _ = ∑ k, wedge R' (Sec s' p.1.1.1) ((GlobalTheory.CechDR.pullForm h (u k)).1 (Opposite.op p.1.1))
            ((GlobalTheory.CechDR.pullForm h (v k)).1 (Opposite.op p.1.1)) :=
          Finset.sum_congr rfl fun k _ ↦ congrArg₂ (fun a b ↦ wedge R' (Sec s' p.1.1.1) a b)
            (hp (u k) p).symm (hp (v k) p).symm
  exact key t.unop

end GlobalTheory.AbCoh
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExteriorDerivSumWedgeSemilinearPullbackStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exteriorDerivSumWedge_semilinearPullback : ∀ (R R' : Type) [CommRing R] [CommRing R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (σ : R →+* R') (φ : X' ⟶ X) (h : φ ≫ s = s' ≫ spMap σ) (w : GlobForm s) (n : ℕ) (u v : Fin n → GlobForm s), ClRel (OAff s) w u v → ClRel (OAff s') (GlobalTheory.CechDR.pullForm h w) (fun k ↦ GlobalTheory.CechDR.pullForm h (u k)) (fun k ↦ GlobalTheory.CechDR.pullForm h (v k)) := by
  first | exact @GlobalTheory.AbCoh.clRel_pullForm | exact GlobalTheory.AbCoh.clRel_pullForm | (intros; apply GlobalTheory.AbCoh.clRel_pullForm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeGlobalOneFormsClosed
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem closed1_eq_top_of_abelian : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ),
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → Closed1 (OAff A.hom) = ⊤ := by
  intro R _ A _ g hA hg
  obtain ⟨hF, h0, -, -⟩ := GlobalTheory.T.abelianScheme_oneFormFrame_and_square R A g hA hg
  have hP := GlobalTheory.T.abelianScheme_globalOneForms_primitive R A g hA hg
  rw [eq_top_iff]
  intro w _
  obtain ⟨n, u, v, hw⟩ := GlobalTheory.T.exteriorDeriv_globalOneForm_eq_sum_wedge R _ (OAff A.hom) hF h0 w
  have hμ : ClRel (OAff (A ⊗ A).hom) (pF μ[A] w) (fun k ↦ pF μ[A] (u k)) (fun k ↦ pF μ[A] (v k)) :=
    GlobalTheory.T.exteriorDerivSumWedge_semilinearPullback R R _ _ A.hom (A ⊗ A).hom (RingHom.id R) (μ[A]).left (ovw μ[A]) w n u v hw
  have h1 : ClRel (OAff (A ⊗ A).hom) (pF (fst A A) w) (fun k ↦ pF (fst A A) (u k))
      (fun k ↦ pF (fst A A) (v k)) :=
    GlobalTheory.T.exteriorDerivSumWedge_semilinearPullback R R _ _ A.hom (A ⊗ A).hom (RingHom.id R) (fst A A).left (ovw (fst A A)) w n u v hw
  have h2 : ClRel (OAff (A ⊗ A).hom) (pF (snd A A) w) (fun k ↦ pF (snd A A) (u k))
      (fun k ↦ pF (snd A A) (v k)) :=
    GlobalTheory.T.exteriorDerivSumWedge_semilinearPullback R R _ _ A.hom (A ⊗ A).hom (RingHom.id R) (snd A A).left (ovw (snd A A)) w n u v hw
  have hsum : wsum (OAff (A ⊗ A).hom) (fun k ↦ pF μ[A] (u k)) (fun k ↦ pF μ[A] (v k)) =
      wsum (OAff (A ⊗ A).hom) (fun k ↦ pF (fst A A) (u k)) (fun k ↦ pF (fst A A) (v k)) +
        wsum (OAff (A ⊗ A).hom) (fun k ↦ pF (snd A A) (u k)) (fun k ↦ pF (snd A A) (v k)) := by
    funext T
    have e := hP w
    calc _ = dOne R _ ((pF μ[A] w).1 T) := (hμ T).symm
      _ = dOne R _ ((pF (fst A A) w).1 T + (pF (snd A A) w).1 T) :=
          congrArg (fun x : GlobForm (A ⊗ A).hom ↦ dOne R _ (x.1 T)) e
      _ = dOne R _ ((pF (fst A A) w).1 T) + dOne R _ ((pF (snd A A) w).1 T) := map_add _ _ _
      _ = _ := congrArg₂ (· + ·) (h1 T) (h2 T)
  have hz := GlobalTheory.T.sum_wedge_primitive_oneForms_eq_zero_abelianScheme R A g hA hg n u v hsum
  exact fun T ↦ (hw T).trans (congrFun hz T)

end GlobalTheory.AbCoh
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeGlobalOneFormsClosedStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_globalOneForms_closed : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → Closed1 (OAff A.hom) = ⊤ := by
  first | exact @GlobalTheory.AbCoh.closed1_eq_top_of_abelian | exact GlobalTheory.AbCoh.closed1_eq_top_of_abelian | (intros; apply GlobalTheory.AbCoh.closed1_eq_top_of_abelian <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateWeilRepresentationSecond
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift GlobalTheory.GalOne

namespace GlobalTheory.GalOne

open GlobalTheory.VecInv Formalism.IndefR.Lev

theorem mu_detAt_eq_levChi {D : D7} {T0 : Type} {L : LevCh D T0} {μ0 : T0} (hL : L.Is μ0) (i : Fin D.R.m) (t : T0)
    (hQ : L.Q t = ∅) {P : Finset (Pl D.host.E)} {e : AE D} (hee : e * e = e)
    (hP : ∀ PP, PP ∈ P ↔ PP ∈ L.Pg ∨ PP ∈ L.Q t) (he : IsIdemSum e P) {κ : GA D (Vc D i)}
    (hκ : IsLevelLift (Vc D i) (L.βV i) (L.datVt i t) 1 κ) :
    ((L.mu t ((i : ℕ) + 1) (detAt e hee _ κ) : Circle) : ℂ) = levChi _ (L.βV i) (flagL (L.datVt i t)) κ := by
  have sV : finE (Vc D i) κ ∈ St (L.βV i) := parLev_St hκ.2.1
  have tg : ∀ PP ∈ L.Pg, redFn (L.βV i) PP (finE (Vc D i) κ) ∈ blockTri (blkOf D.R.r D.R.t) := fun PP h =>
    parLev_g hκ.2.1 h
  have one : ∀ PP ∈ L.Pg, upperLeftBlock (r_le_V i) (redFn (L.βV i) PP (finE (Vc D i) κ)) = 1 := fun PP h =>
    congrFun hκ.2.2 ⟨PP, h⟩
  obtain ⟨aV, haV, hrV⟩ := exists_det_int sV
  have mV := (mu_val hL t i hP he (detAt e hee _ κ) _ aV _ (isDetAt_detAt e hee _ κ) haV fun PP _ => hrV PP).1
  rw [levChi_flag_V i t tg, mV, hQ, Finset.prod_empty, Finset.prod_empty, one_mul]
  refine congrArg (fun z : ℂˣ => ((z * 1 : ℂˣ) : ℂ)) (Finset.prod_congr rfl fun PP h => ?_)
  rw [(GlobalTheory.T.det_twoDiagBlocks_properties _ _ _ 0 (r_le_V i) _).1 (blockTri_blkOf_le _ _ (tg PP h)), one PP h, map_one, one_mul]

theorem smul_of_splitFac {D : D7} {X ι : Type} {u v : X → ℂ} {c : ι → ℂ} {μ η : (AE D)ˣ →* Circle} {x y : (AE D)ˣ} {z : ℂ}
    (h : (∏ i ∈ (∅ : Finset ι), c i) • u = ((splitFacO μ (μ * η⁻¹) x y : Circle) : ℂ) • v) (hy : y = 1) (hη : η x = 1)
    (hz : ((μ x : Circle) : ℂ) = z) : u = z⁻¹ • v := by
  rwa [Finset.prod_empty, one_smul, splitFacO, MonoidHom.mul_apply, MonoidHom.inv_apply, hη, inv_one, mul_one, hy, map_one,
    mul_one, Circle.coe_inv, hz] at h

end GlobalTheory.GalOne
end
