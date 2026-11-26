module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemPrimitiveDeRhamCohomologyOfAdditivePeriods

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectivePeriodMapAbelianVarietyLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechClassOfQuasiPeriodicHolomorphicCover
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechDeRhamClassOfQuasiPeriodicFunctions
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedAlgebraicFormFderivUniformised
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamDerivativeEqZeroOfSymmetricFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamDerivativeEqZeroOfSymmetricFrame
set_option autoImplicit false

open KaehlerDifferential GlobalTheory.CechDR

namespace GlobalTheory.CechPer

theorem sum_symm_smul_wedge_eq_zero {B : Type} [CommRing B] [Algebra ℂ B] {g : ℕ}
    (ω : Fin g → Ω[B⁄ℂ]) (S : Fin g → Fin g → B) (hS : ∀ a b, S a b = S b a) :
    ∑ b, ∑ c, S b c • wedge ℂ B (ω b) (ω c) = 0 := by
  set X := ∑ b, ∑ c, S b c • wedge ℂ B (ω b) (ω c) with hX
  have h1 : X = -X := by
    conv_lhs => rw [hX, Finset.sum_comm]
    rw [hX, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    rw [wedge_swap (ω c) (ω b), hS c b, smul_neg]
  have h2 : (2 : B) • X = 0 := by
    rw [two_smul]; exact add_eq_zero_iff_eq_neg.mpr h1
  have h3 : algebraMap ℂ B (2⁻¹) * 2 = 1 := by
    rw [← map_ofNat (algebraMap ℂ B) 2, ← map_mul, inv_mul_cancel₀ two_ne_zero, map_one]
  calc X = (algebraMap ℂ B (2⁻¹) * 2) • X := by rw [h3, one_smul]
    _ = 0 := by rw [mul_smul, h2, smul_zero]

theorem dOne_eq_sum_of_frame {B : Type} [CommRing B] [Algebra ℂ B] {g : ℕ}
    (d : Fin g → Derivation ℂ B B) (ω : Fin g → Ω[B⁄ℂ])
    (hc : ∀ a b x, d a (d b x) = d b (d a x))
    (hf : ∀ ξ, ξ = ∑ a, (d a).liftKaehlerDifferential ξ • ω a) (ξ : Ω[B⁄ℂ]) :
    dOne ℂ B ξ = ∑ b, ∑ c, d b ((d c).liftKaehlerDifferential ξ) • wedge ℂ B (ω b) (ω c) := by
  induction ξ using ind1 with
  | h0 => simp
  | ha x y hx hy =>
    rw [map_add (f := _), hx, hy, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    rw [map_add (f := _), map_add (f := _), add_smul]
  | h x y =>
    have hD : ∀ z : B, D ℂ B z = ∑ a, d a z • ω a := fun z ↦ by
      simpa only [Derivation.liftKaehlerDifferential_comp_D] using hf (D ℂ B z)
    have h0 := sum_symm_smul_wedge_eq_zero ω (fun b c ↦ x * d b (d c y))
      (fun a b ↦ by rw [hc a b])
    have h1 : wedge ℂ B (D ℂ B x) (D ℂ B y) =
        ∑ b, ∑ c, (d c y * d b x) • wedge ℂ B (ω b) (ω c) := by
      rw [hD x, hD y, LinearMap.map_sum₂]
      refine Finset.sum_congr rfl fun b _ ↦ ?_
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun c _ ↦ ?_
      rw [map_smul, LinearMap.map_smul₂, mul_smul]
    rw [dOne_smul_D, h1, ← zero_add (∑ b, ∑ c, (d c y * d b x) • wedge ℂ B (ω b) (ω c)), ← h0,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    rw [map_smul, Derivation.liftKaehlerDifferential_comp_D, smul_eq_mul, Derivation.leibniz,
      smul_eq_mul, smul_eq_mul, add_smul]

theorem dOne_eq_zero_of_frame_of_symm : ∀ (B : Type) [CommRing B] [Algebra ℂ B] (g : ℕ) (d : Fin g → Derivation ℂ B B) (ω : Fin g → Ω[B⁄ℂ]), (∀ a b x, d a (d b x) = d b (d a x)) → (∀ a b, (d a).liftKaehlerDifferential (ω b) = if a = b then 1 else 0) → (∀ ξ, ξ = ∑ a, (d a).liftKaehlerDifferential ξ • ω a) → ∀ k : Fin g → B, (∀ a b, d a (k b) = d b (k a)) → dOne ℂ B (∑ a, k a • ω a) = 0 := by
  intro B _ _ g d ω hc hd hf k hk
  have hl : ∀ c, (d c).liftKaehlerDifferential (∑ a, k a • ω a) = k c := fun c ↦ by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, hd]
  rw [dOne_eq_sum_of_frame d ω hc hf]
  simp only [hl]
  exact sum_symm_smul_wedge_eq_zero ω (fun b c ↦ d b (k c)) hk

end GlobalTheory.CechPer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamDerivativeEqZeroOfSymmetricFrameStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deRhamDerivative_eq_zero_of_symmetric_frame : ∀ (B : Type) [CommRing B] [Algebra ℂ B] (g : ℕ) (d : Fin g → Derivation ℂ B B) (ω : Fin g → Ω[B⁄ℂ]), (∀ a b x, d a (d b x) = d b (d a x)) → (∀ a b, (d a).liftKaehlerDifferential (ω b) = if a = b then 1 else 0) → (∀ ξ, ξ = ∑ a, (d a).liftKaehlerDifferential ξ • ω a) → ∀ k : Fin g → B, (∀ a b, d a (k b) = d b (k a)) → dOne ℂ B (∑ a, k a • ω a) = 0 := by
  first | exact @GlobalTheory.CechPer.dOne_eq_zero_of_frame_of_symm | exact GlobalTheory.CechPer.dOne_eq_zero_of_frame_of_symm | (intros; apply GlobalTheory.CechPer.dOne_eq_zero_of_frame_of_symm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedAlgebraicFormFderivUniformised
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
open Filter Topology

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem clm_eq_sum_single_smul_proj {g : ℕ} (f : (Fin g → ℂ) →L[ℂ] ℂ) :
    f = ∑ a, f (Pi.single a 1) • (ContinuousLinearMap.proj a : (Fin g → ℂ) →L[ℂ] ℂ) := by
  refine ContinuousLinearMap.ext fun v ↦ ?_
  conv_lhs => rw [pi_eq_sum_univ' v]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, mul_comm]

theorem fderiv_partial_symm {g : ℕ} {s : Set (Fin g → ℂ)} (hs : IsOpen s) {h : (Fin g → ℂ) → ℂ}
    (hh : DifferentiableOn ℂ h s) {k : Fin g → (Fin g → ℂ) → ℂ} (hk : ∀ a, DifferentiableOn ℂ (k a) s)
    (e : ∀ a, ∀ z ∈ s, fderiv ℂ h z (Pi.single a 1) = k a z) (a b : Fin g) {z : Fin g → ℂ} (hz : z ∈ s) :
    fderiv ℂ (k b) z (Pi.single a 1) = fderiv ℂ (k a) z (Pi.single b 1) := by
  have hn : s ∈ 𝓝 z := hs.mem_nhds hz
  have h1 : ∀ᶠ y in 𝓝 z, HasFDerivAt h (fderiv ℂ h y) y := by
    filter_upwards [hn] with y hy using (hh.differentiableAt (hs.mem_nhds hy)).hasFDerivAt
  have h2 : fderiv ℂ h =ᶠ[𝓝 z]
      fun y ↦ ∑ c, k c y • (ContinuousLinearMap.proj c : (Fin g → ℂ) →L[ℂ] ℂ) := by
    filter_upwards [hn] with y hy
    rw [clm_eq_sum_single_smul_proj (fderiv ℂ h y)]
    exact Finset.sum_congr rfl fun c _ ↦ by rw [e c y hy]
  have h3 : DifferentiableAt ℂ (fderiv ℂ h) z := by
    refine DifferentiableAt.congr_of_eventuallyEq ?_ h2
    exact DifferentiableAt.fun_sum fun c _ ↦ ((hk c).differentiableAt hn).smul_const _
  have h4 : ∀ c v, fderiv ℂ (k c) z v = fderiv ℂ (fderiv ℂ h) z v (Pi.single c 1) := by
    intro c v
    have h5 : k c =ᶠ[𝓝 z] fun y ↦ fderiv ℂ h y (Pi.single c 1) := by
      filter_upwards [hn] with y hy using (e c y hy).symm
    rw [h5.fderiv_eq, fderiv_clm_apply h3 (differentiableAt_const _)]
    simp
  rw [h4, h4]
  exact second_derivative_symmetric_of_eventually h1 h3.hasFDerivAt _ _

theorem exists_closed_form_fderiv_eq (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g)
    (hA : IsAbelianScheme A) (U : A.left.affineOpens) (h : (Fin g → ℂ) → ℂ) (hh : DifferentiableOn ℂ h (pre u.ex U.1))
    (hr : ∀ a, IsReg u.ex U.1 fun z => fderiv ℂ h z (Pi.single a 1)) :
    ∃ ξ : Ω[Sec (str A) U.1⁄ℂ], dOne ℂ _ ξ = 0 ∧ ∀ z ∈ pre u.ex U.1, fderiv ℂ h z = evForm u.ex U.1 z ξ := by
  obtain ⟨hop, hdiff, -, -, -, -, -, -, -, halg, -, -⟩ := GlobalTheory.T.uniformisation_preimage_value_rules A g L u
  obtain ⟨d, ω, hcomm, hd, hdual, hspan, hev⟩ := GlobalTheory.T.kaehler_differentials_free_coordinate_forms_abelian A g L u hA U
  choose k₀ hk₀ using hr
  let k : Fin g → Sec (str A) U.1 := k₀
  have hk : ∀ a, ∀ z ∈ pre u.ex U.1, fderiv ℂ h z (Pi.single a 1) = val u.ex U.1 (k a) z := hk₀
  refine ⟨∑ a, k a • ω a, GlobalTheory.T.deRhamDerivative_eq_zero_of_symmetric_frame _ g d ω hcomm hdual hspan k fun a b ↦ ?_, fun z hz ↦ ?_⟩
  · have h0 : d a (k b) - d b (k a) = 0 := by
      refine GlobalTheory.T.eq_zero_of_val_eq_zero_abelian A g L u hA U.1 _ fun z hz ↦ ?_
      obtain ⟨e, he⟩ := halg U.1 z hz
      have h1 := he (d a (k b) - d b (k a))
      rw [map_sub, ← he (d a (k b)), ← he (d b (k a)), hd a _ z hz, hd b _ z hz,
        fderiv_partial_symm (hop U.1) hh (fun c ↦ hdiff U.1 (k c)) hk a b hz, sub_self] at h1
      exact h1
    exact sub_eq_zero.mp h0
  · rw [clm_eq_sum_single_smul_proj (fderiv ℂ h z), clm_eq_sum_single_smul_proj (evForm u.ex U.1 z _)]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    have h1 : (d a).liftKaehlerDifferential (∑ c, k c • ω c) = k a := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sum, hdual]
    rw [hev a _ z hz, h1, hk a z hz]

end GlobalTheory.CechPer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedAlgebraicFormFderivUniformisedStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_closed_algebraic_form_fderiv_uniformised : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (U : A.left.affineOpens) (h : (Fin g → ℂ) → ℂ), DifferentiableOn ℂ h (pre u.ex U.1) → (∀ a, IsReg u.ex U.1 fun z => fderiv ℂ h z (Pi.single a 1)) → ∃ ξ : Ω[Sec (str A) U.1⁄ℂ], dOne ℂ _ ξ = 0 ∧ ∀ z ∈ pre u.ex U.1, fderiv ℂ h z = evForm u.ex U.1 z ξ := by
  first | exact @GlobalTheory.CechPer.exists_closed_form_fderiv_eq | exact GlobalTheory.CechPer.exists_closed_form_fderiv_eq | (intros; apply GlobalTheory.CechPer.exists_closed_form_fderiv_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechDeRhamClassOfQuasiPeriodicFunctions
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.CechPer

theorem exists_isPer_of_quasiPeriodic : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (k : A.left.affineOpens → (Fin g → ℂ) → ℂ) (q : u.Λ → ℂ), (∀ U, DifferentiableOn ℂ (k U) (pre u.ex U.1)) → (∀ U V : A.left.affineOpens, V ≤ U → IsReg u.ex V.1 (k V - k U)) → (∀ U a, IsReg u.ex U.1 fun z => fderiv ℂ (k U) z (Pi.single a 1)) → (∀ U (l : u.Λ), ∀ z ∈ pre u.ex U.1, k U (z + l) = k U z + q l) → ∃ x, IsPer u.ex u.Λ x q := by
  intro A _ g L u hA k q hk hreg hder hper
  obtain ⟨hopen, hdiff, -, -, -, hmono, -, -, hres, hev, -, -⟩ := GlobalTheory.CechPer.pre_val_rules A g L u
  have hf : ∀ (U V : A.left.affineOpens) (_ : Opposite.op U ⟶ Opposite.op V), ∃ b : Sec (str A) V.1,
      ∀ z ∈ pre u.ex V.1, (k V - k U) z = val u.ex V.1 b z :=
    fun U V a => hreg U V (leOfHom a.unop)
  choose f hf using hf
  have hω : ∀ U : A.left.affineOpens, ∃ ξ : Ω[Sec (str A) U.1⁄ℂ], dOne ℂ _ ξ = 0 ∧
      ∀ z ∈ pre u.ex U.1, fderiv ℂ (k U) z = evForm u.ex U.1 z ξ :=
    fun U => GlobalTheory.T.exists_closed_algebraic_form_fderiv_uniformised A g L u hA U (k U) (hk U) (hder U)
  choose ω hωc hωe using hω
  have hsub : ∀ (U : A.left.Opens) (b b' : Sec (str A) U), ∀ z ∈ pre u.ex U,
      val u.ex U (b - b') z = val u.ex U b z - val u.ex U b' z := by
    intro U b b' z hz
    obtain ⟨e, he⟩ := hev U z hz
    exact (he _).trans ((map_sub e b b').trans (congrArg₂ (· - ·) (he b).symm (he b').symm))
  have hadd : ∀ (U : A.left.Opens) (b b' : Sec (str A) U), ∀ z ∈ pre u.ex U,
      val u.ex U (b + b') z = val u.ex U b z + val u.ex U b' z := by
    intro U b b' z hz
    obtain ⟨e, he⟩ := hev U z hz
    exact (he _).trans ((map_add e b b').trans (congrArg₂ (· + ·) (he b).symm (he b').symm))
  have hfun : ∀ (U V W : A.left.affineOpens) (φ : Opposite.op U ⟶ Opposite.op V) (ψ : Opposite.op V ⟶ Opposite.op W),
      f U W (φ ≫ ψ) = Sec.res (str A) (show W.1 ≤ V.1 from leOfHom ψ.unop) (f U V φ) + f V W ψ := by
    intro U V W φ ψ
    have hle : W.1 ≤ V.1 := leOfHom ψ.unop
    refine sub_eq_zero.1 (GlobalTheory.T.eq_zero_of_val_eq_zero_abelian A g L u hA W.1
      (f U W (φ ≫ ψ) - (Sec.res (str A) hle (f U V φ) + f V W ψ) : Sec (str A) W.1) fun z hz => ?_)
    have e1 := hsub W.1 (f U W (φ ≫ ψ)) (Sec.res (str A) hle (f U V φ) + f V W ψ) z hz
    have e2 := hadd W.1 (Sec.res (str A) hle (f U V φ)) (f V W ψ) z hz
    have e3 := hres V.1 W.1 hle (f U V φ) z hz
    have e4 := hf U W (φ ≫ ψ) z hz
    have e5 := hf U V φ z (hmono _ _ hle hz)
    have e6 := hf V W ψ z hz
    simp only [Pi.sub_apply] at e4 e5 e6
    linear_combination e1 - e2 - e3 - e4 + e5 + e6
  have hform : ∀ (U V : A.left.affineOpens) (φ : Opposite.op U ⟶ Opposite.op V),
      ω V = p1 (OAff (str A)) φ (ω U) + KaehlerDifferential.D ℂ (Sec (str A) V.1) (f U V φ) := by
    intro U V φ
    refine sub_eq_zero.1 (GlobalTheory.T.kaehlerOneForm_eq_zero_of_uniformised_values A g L u hA V _ fun z hz => ?_)
    have hle : V.1 ≤ U.1 := leOfHom φ.unop
    have hz' : z ∈ pre u.ex U.1 := hmono _ _ hle hz
    have e1 := GlobalTheory.T.evForm_restriction_eq A g L u U V φ (ω U) z hz
    have e2 := (GlobalTheory.T.uniformisedOneFormEvaluation_rules A g L u V.1 z hz).2.2 (f U V φ)
    have heq : k V =ᶠ[nhds z] k U + val u.ex V.1 (f U V φ) := by
      filter_upwards [(hopen _).mem_nhds hz] with w hw
      have := hf U V φ w hw
      simp only [Pi.sub_apply] at this
      simp only [Pi.add_apply]
      linear_combination this
    have e3 : fderiv ℂ (k V) z = fderiv ℂ (k U) z + fderiv ℂ (val u.ex V.1 (f U V φ)) z :=
      heq.fderiv_eq.trans (fderiv_add ((hk _).differentiableAt ((hopen _).mem_nhds hz'))
        ((hdiff _ _).differentiableAt ((hopen _).mem_nhds hz)))
    refine (map_sub (evForm u.ex V.1 z) _ _).trans (sub_eq_zero.2 ?_)
    refine Eq.trans ?_ (map_add (evForm u.ex V.1 z) _ _).symm
    exact (hωe V z hz).symm.trans (e3.trans (congrArg₂ (· + ·) ((hωe U z hz').trans e1.symm) e2.symm))
  let c0 : Tot1 (OAff (str A)) := (fun U V a => f U.unop V.unop a, fun U => ω U.unop)
  have hc : c0 ∈ cechDeRhamTotalCocyclesOne (OAff (str A)) :=
    mem_cechDeRhamTotalCocyclesOne_iff.2 ⟨fun T T' T'' φ ψ => hfun T.unop T'.unop T''.unop φ ψ, fun T T' φ => hform T.unop T'.unop φ,
      fun T => hωc T.unop⟩
  refine ⟨Hyp1.mk _ ⟨c0, hc⟩, ⟨c0, hc⟩, k, rfl, ⟨hk, fun U V a z hz => ?_, fun U z hz => hωe U z hz⟩, hper⟩
  have := hf U V a z hz
  simp only [Pi.sub_apply] at this
  change k V z = k U z + val u.ex V.1 (f U V a) z
  linear_combination this

end GlobalTheory.CechPer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechDeRhamClassOfQuasiPeriodicFunctionsStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cechDeRham_class_of_quasiPeriodic_functions : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (k : A.left.affineOpens → (Fin g → ℂ) → ℂ) (q : u.Λ → ℂ), (∀ U, DifferentiableOn ℂ (k U) (pre u.ex U.1)) → (∀ U V : A.left.affineOpens, V ≤ U → IsReg u.ex V.1 (k V - k U)) → (∀ U a, IsReg u.ex U.1 fun z => fderiv ℂ (k U) z (Pi.single a 1)) → (∀ U (l : u.Λ), ∀ z ∈ pre u.ex U.1, k U (z + l) = k U z + q l) → ∃ x, IsPer u.ex u.Λ x q := by
  first | exact @GlobalTheory.CechPer.exists_isPer_of_quasiPeriodic | exact GlobalTheory.CechPer.exists_isPer_of_quasiPeriodic | (intros; apply GlobalTheory.CechPer.exists_isPer_of_quasiPeriodic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechClassOfQuasiPeriodicHolomorphicCover
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
open Filter Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer.OfCover

theorem fderiv_congr_on {g : ℕ} {S : Set (Fin g → ℂ)} (hS : IsOpen S) {f f' : (Fin g → ℂ) → ℂ}
    (e : ∀ z ∈ S, f z = f' z) {z : Fin g → ℂ} (hz : z ∈ S) : fderiv ℂ f z = fderiv ℂ f' z :=
  Filter.EventuallyEq.fderiv_eq (Filter.eventually_of_mem (hS.mem_nhds hz) e)

theorem exists_isPer : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (K : Type) (W : K → A.left.Opens) (h : K → (Fin g → ℂ) → ℂ) (q : u.Λ → ℂ), ⨆ i, W i = ⊤ → (∀ i, DifferentiableOn ℂ (h i) (pre u.ex (W i))) → (∀ i j, IsReg u.ex (W i ⊓ W j) (h i - h j)) → (∀ i (l : u.Λ), ∀ z ∈ pre u.ex (W i), h i (z + l) = h i z + q l) → ∃ x, IsPer u.ex u.Λ x q := by
  intro A _ g L u hA K W h q hW hd hr hq
  obtain ⟨bo, bd, bp, bv, bi, bm, bs, -, -, -, -, bt⟩ := GlobalTheory.T.uniformisation_preimage_value_rules A g L u
  have ra := GlobalTheory.T.isRegularOnOpenUniformised_subalgebra_restrict A g L u
  have der := GlobalTheory.T.isRegular_fderiv_constant_vector_uniformised A g L u hA
  have glue := GlobalTheory.T.isRegularOnOpenUniformised_of_locally A g L u hA

  have dsub : ∀ (U : A.left.Opens) (k k' : (Fin g → ℂ) → ℂ) (w : Fin g → ℂ), DifferentiableOn ℂ k (pre u.ex U) →
      DifferentiableOn ℂ k' (pre u.ex U) → IsReg u.ex U (k - k') →
      IsReg u.ex U ((fun z => fderiv ℂ k z w) - fun z => fderiv ℂ k' z w) := by
    rintro U k k' w hk hk' ⟨b, hb⟩
    refine (ra U).2.2.1 _ _ (der U b w) fun z hz => ?_
    have e := fderiv_congr_on (bo U) hb hz
    rw [← e, fderiv_sub (hk.differentiableAt ((bo U).mem_nhds hz)) (hk'.differentiableAt ((bo U).mem_nhds hz))]
    rfl
  have hreg : ∀ (w : Fin g → ℂ) i, IsReg u.ex (W i) fun z => fderiv ℂ (h i) z w := by
    intro w
    refine GlobalTheory.T.isReg_of_periodic_of_isReg_sub' A g L u hA K W (fun i z => fderiv ℂ (h i) z w) hW (fun i => ?_) (fun i l z hz => ?_) fun i j => ?_
    · have := (GlobalTheory.SCV.analyticOnNhd_of_differentiableOn (bo (W i)) (hd i)).fderiv.differentiableOn
      exact this.clm_apply (differentiableOn_const w)
    · have e := fderiv_congr_on (bo (W i)) (f := fun z => h i (z + l)) (f' := fun z => h i z + q l) (hq i l) hz
      rw [fderiv_comp_add_right, fderiv_add_const] at e
      change fderiv ℂ (h i) (z + l) w = fderiv ℂ (h i) z w
      rw [e]
    · exact dsub _ _ _ w ((hd i).mono (bm _ _ inf_le_left)) ((hd j).mono (bm _ _ inf_le_right)) (hr i j)
  choose k hk using GlobalTheory.T.exists_regular_section_of_regular_differences A g L u hA K W h hW hr
  have cov : ∀ z, ∃ i, z ∈ pre u.ex (W i) := fun z => (bs K W z).1 (hW ▸ bt z)
  have kd : ∀ (U : A.left.affineOpens) i, DifferentiableOn ℂ (k U) (pre u.ex (U.1 ⊓ W i)) := fun U i => by
    have := ((ra _).2.2.2.2.1 _ (hk U i)).add ((hd i).mono (bm _ _ inf_le_right))
    simpa using this
  have mem : ∀ (U : A.left.Opens) z i, z ∈ pre u.ex U → z ∈ pre u.ex (W i) → z ∈ pre u.ex (U ⊓ W i) :=
    fun U z i h1 h2 => by rw [bi]; exact ⟨h1, h2⟩
  refine GlobalTheory.T.exists_cechDeRham_class_of_quasiPeriodic_functions A g L u hA k q (fun U z hz => ?_) (fun U V hVU => ?_) (fun U a => ?_) fun U l z hz => ?_
  · obtain ⟨i, hi⟩ := cov z
    exact ((kd U i).differentiableAt ((bo _).mem_nhds (mem _ _ _ hz hi))).differentiableWithinAt
  · refine glue _ _ fun z hz => ?_
    obtain ⟨i, hi⟩ := cov z
    refine ⟨V.1 ⊓ W i, inf_le_left, mem _ _ _ hz hi, ?_⟩
    have := ((ra _).2.1 _ _ (hk V i) ((ra _).2.2.2.1 _ (inf_le_inf_right (W i) (show V.1 ≤ U.1 from hVU)) _ (hk U i))).2.1
    simpa using this
  · refine glue _ _ fun z hz => ?_
    obtain ⟨i, hi⟩ := cov z
    refine ⟨U.1 ⊓ W i, inf_le_left, mem _ _ _ hz hi, ?_⟩
    have h1 := dsub _ _ _ (Pi.single a 1) (kd U i) ((hd i).mono (bm _ _ inf_le_right)) (hk U i)
    have h2 := (ra _).2.2.2.1 _ (inf_le_right : U.1 ⊓ W i ≤ W i) _ (hreg (Pi.single a 1) i)
    have := ((ra _).2.1 _ _ h1 h2).1
    simpa using this
  · obtain ⟨i, hi⟩ := cov z
    obtain ⟨b, hb⟩ := hk U i
    have h1 := hb z (mem _ _ _ hz hi)
    have h2 := hb (z + l) ((bp _ l z).2 (mem _ _ _ hz hi))
    rw [bv, Pi.sub_apply, hq i l z hi] at h2
    rw [Pi.sub_apply] at h1
    linear_combination h2 - h1

end GlobalTheory.CechPer.OfCover
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechClassOfQuasiPeriodicHolomorphicCoverStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cechClass_of_quasiPeriodic_holomorphic_cover : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (K : Type) (W : K → A.left.Opens) (h : K → (Fin g → ℂ) → ℂ) (q : u.Λ → ℂ), ⨆ i, W i = ⊤ → (∀ i, DifferentiableOn ℂ (h i) (pre u.ex (W i))) → (∀ i j, IsReg u.ex (W i ⊓ W j) (h i - h j)) → (∀ i (l : u.Λ), ∀ z ∈ pre u.ex (W i), h i (z + l) = h i z + q l) → ∃ x, IsPer u.ex u.Λ x q := by
  first | exact @GlobalTheory.CechPer.OfCover.exists_isPer | exact GlobalTheory.CechPer.OfCover.exists_isPer | (intros; apply GlobalTheory.CechPer.OfCover.exists_isPer <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppellHumbertFrameLogDerivativeQuasiPeriodic
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppellHumbertFrameLogDerivativeQuasiPeriodic
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.CechPer.LogDer

open Filter Topology

theorem logDer_mul {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {f c d : E → ℂ} {z : E}
    (h : f =ᶠ[𝓝 z] fun w => c w * d w) (hc : DifferentiableAt ℂ c z) (hd : DifferentiableAt ℂ d z)
    (hc0 : c z ≠ 0) (hd0 : d z ≠ 0) (v : E) :
    fderiv ℂ f z v / f z = fderiv ℂ c z v / c z + fderiv ℂ d z v / d z := by
  have hm : HasFDerivAt (fun w => c w * d w) (c z • fderiv ℂ d z + d z • fderiv ℂ c z) z :=
    hc.hasFDerivAt.mul hd.hasFDerivAt
  rw [h.fderiv_eq, hm.fderiv, h.eq_of_nhds]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  field_simp
  ring

theorem hasFDerivAt_factor {g : ℕ} (a b c : ℂ) (m z : Fin g → ℂ) :
    ∃ D : (Fin g → ℂ) →L[ℂ] ℂ, HasFDerivAt (fun w : Fin g → ℂ => a * Complex.exp (b * (w ⬝ᵥ m) + c)) D z ∧
      ∀ v, D v = a * Complex.exp (b * (z ⬝ᵥ m) + c) * (b * (v ⬝ᵥ m)) := by

  let ℓ : (Fin g → ℂ) →L[ℂ] ℂ := ∑ i, m i • ContinuousLinearMap.proj i
  have hℓ : ∀ w, ℓ w = w ⬝ᵥ m := by
    intro w
    simp [ℓ, dotProduct, mul_comm]
  have H := (((ℓ.hasFDerivAt (x := z)).const_mul b).add_const c).cexp.const_mul a
  have hfun : (fun w : Fin g → ℂ => a * Complex.exp (b * (w ⬝ᵥ m) + c)) = fun w => a * Complex.exp (b * ℓ w + c) := by
    funext w
    rw [hℓ]
  refine ⟨a • (Complex.exp (b * ℓ z + c) • (b • ℓ)), ?_, ?_⟩
  · rw [hfun]
    exact H
  · intro v
    simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, hℓ]
    ring

theorem main : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → L.IsLB → ∀ (H : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), u.IsAH H χ → ∀ v : Fin g → ℂ, (∀ i, DifferentiableOn ℂ (fun z => fderiv ℂ (u.fr i) z v / u.fr i z) (pre u.ex (L.U i))) ∧ (∀ i j, IsReg u.ex (L.U i ⊓ L.U j) ((fun z => fderiv ℂ (u.fr i) z v / u.fr i z) - fun z => fderiv ℂ (u.fr j) z v / u.fr j z)) ∧ ∀ i (l : u.Λ), ∀ z ∈ pre u.ex (L.U i), fderiv ℂ (u.fr i) (z + l) v / u.fr i (z + l) = fderiv ℂ (u.fr i) z v / u.fr i z - Real.pi * (v ⬝ᵥ H.mulVec (star (l : Fin g → ℂ))) := by
  intro A _ g L u hA _ H χ hAH v
  obtain ⟨hopen, hdval, hshift, -, hinf, -, -, -, -, hev, -, -⟩ := GlobalTheory.T.uniformisation_preimage_value_rules A g L u

  have hfrd : ∀ i, DifferentiableOn ℂ (u.fr i) (pre u.ex (L.U i)) := u.10
  have hfr0 : ∀ i, ∀ z ∈ pre u.ex (L.U i), u.fr i z ≠ 0 := fun i z hz => u.11 i z hz
  have hfrg : ∀ i j, ∀ z ∈ pre u.ex (L.U i ⊓ L.U j),
      u.fr i z = val u.ex (L.U i ⊓ L.U j) (L.g i j : Γ(A.left, L.U i ⊓ L.U j)) z * u.fr j z :=
    fun i j z hz => u.12 i j z hz
  have hfra : ∀ i, ∀ z ∈ pre u.ex (L.U i), DifferentiableAt ℂ (u.fr i) z :=
    fun i z hz => (hfrd i).differentiableAt ((hopen _).mem_nhds hz)
  refine ⟨?_, ?_, ?_⟩
  ·
    intro i z hz

    let e : ReciprocityTheory.L2DbarEstimates.V g ≃L[ℂ] (Fin g → ℂ) := EuclideanSpace.equiv (Fin g) ℂ
    have hpre : IsOpen (e ⁻¹' pre u.ex (L.U i)) := (hopen _).preimage e.continuous
    have hsm := ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn g (u.fr i ∘ e) _ hpre
      ((hfrd i).comp e.differentiableOn (fun y hy => hy))
    have hsm' : ContDiffOn ℂ (↑(⊤ : ℕ∞)) (u.fr i) (pre u.ex (L.U i)) := by
      have h2 := hsm.comp e.symm.contDiff.contDiffOn (fun y hy => by simpa using hy)
      have h3 : (u.fr i ∘ e) ∘ e.symm = u.fr i := by
        funext y
        simp
      rwa [h3] at h2
    have hca := (hsm'.contDiffAt ((hopen _).mem_nhds hz)).fderiv_right (m := 1)
      (by first | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤))
    have h1 : DifferentiableAt ℂ (fun w => fderiv ℂ (u.fr i) w v) z :=
      (hca.differentiableAt one_ne_zero).clm_apply (differentiableAt_const v)
    have h4 := h1.mul ((hfra i z hz).inv (hfr0 i z hz))
    simp only [div_eq_mul_inv]
    exact h4.differentiableWithinAt
  ·
    intro i j
    set U := L.U i ⊓ L.U j with hU
    set G : Γ(A.left, U) := (L.g i j).val with hG
    set G' : Γ(A.left, U) := ((L.g i j)⁻¹ : (Γ(A.left, U))ˣ).val with hG'
    obtain ⟨-, hring, hcongr, -, -, -⟩ := GlobalTheory.T.isRegularOnOpenUniformised_subalgebra_restrict A g L u U
    have hder : IsReg u.ex U fun z => fderiv ℂ (val u.ex U G) z v := GlobalTheory.T.isRegular_fderiv_constant_vector_uniformised A g L u hA U G v
    have hinv : IsReg u.ex U (val u.ex U G') := ⟨G', fun z _ => rfl⟩
    have hprod := (hring _ _ hder hinv).2.2
    refine hcongr _ _ hprod ?_
    intro z hz
    have hzij : z ∈ pre u.ex (L.U i) ∩ pre u.ex (L.U j) := by rw [← hinf]; exact hz
    have hGG : val u.ex U G z * val u.ex U G' z = 1 := by
      obtain ⟨e, he⟩ := hev U z hz
      have h1 : G * G' = 1 := Units.mul_inv _
      rw [he, he]
      exact (map_mul e G G').symm.trans ((congrArg e h1).trans (map_one e))
    have hG0 : val u.ex U G z ≠ 0 := left_ne_zero_of_mul_eq_one hGG
    have hev' : ∀ᶠ w in 𝓝 z, u.fr i w = val u.ex U G w * u.fr j w :=
      Filter.eventually_of_mem ((hopen U).mem_nhds hz) (fun w hw => hfrg i j w hw)
    have key := logDer_mul hev' ((hdval U G).differentiableAt ((hopen U).mem_nhds hz))
      (hfra j z hzij.2) hG0 (hfr0 j z hzij.2) v
    simp only [Pi.sub_apply, Pi.mul_apply]
    rw [key, eq_inv_of_mul_eq_one_right hGG]
    ring
  ·
    intro i l z hz
    set m := H.mulVec (star (l : Fin g → ℂ)) with hm
    have hzl : z + (l : Fin g → ℂ) ∈ pre u.ex (L.U i) := (hshift (L.U i) l z).2 hz
    have hχ : χ l ≠ 0 := by
      intro h0
      have := hAH.2.2.1 l
      rw [h0, norm_zero] at this
      exact zero_ne_one this
    obtain ⟨D, hD, hDv⟩ := hasFDerivAt_factor (χ l) (Real.pi : ℂ) ((Real.pi : ℂ) / 2 * ((l : Fin g → ℂ) ⬝ᵥ m)) m z
    have hev' : ∀ᶠ w in 𝓝 z, u.fr i w = (χ l * Complex.exp ((Real.pi : ℂ) * (w ⬝ᵥ m) + (Real.pi : ℂ) / 2 * ((l : Fin g → ℂ) ⬝ᵥ m))) * u.fr i (w + l) :=
      Filter.eventually_of_mem ((hopen _).mem_nhds hz) (fun w hw => hAH.2.2.2 l i w hw)
    have hdl : DifferentiableAt ℂ (fun w => u.fr i (w + l)) z :=
      (hfra i _ hzl).comp z (differentiableAt_id.add_const _)
    have key := logDer_mul hev' hD.differentiableAt hdl
      (mul_ne_zero hχ (Complex.exp_ne_zero _)) (hfr0 i _ hzl) v
    rw [hD.fderiv, hDv, fderiv_comp_add_right] at key
    have hE : χ l * Complex.exp ((Real.pi : ℂ) * (z ⬝ᵥ m) + (Real.pi : ℂ) / 2 * ((l : Fin g → ℂ) ⬝ᵥ m)) ≠ 0 :=
      mul_ne_zero hχ (Complex.exp_ne_zero _)
    rw [key, mul_div_cancel_left₀ _ hE]
    ring

end GlobalTheory.CechPer.LogDer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppellHumbertFrameLogDerivativeQuasiPeriodicStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.appell_humbert_frame_log_derivative_quasi_periodic : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → L.IsLB → ∀ (H : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), u.IsAH H χ → ∀ v : Fin g → ℂ, (∀ i, DifferentiableOn ℂ (fun z => fderiv ℂ (u.fr i) z v / u.fr i z) (pre u.ex (L.U i))) ∧ (∀ i j, IsReg u.ex (L.U i ⊓ L.U j) ((fun z => fderiv ℂ (u.fr i) z v / u.fr i z) - fun z => fderiv ℂ (u.fr j) z v / u.fr j z)) ∧ ∀ i (l : u.Λ), ∀ z ∈ pre u.ex (L.U i), fderiv ℂ (u.fr i) (z + l) v / u.fr i (z + l) = fderiv ℂ (u.fr i) z v / u.fr i z - Real.pi * (v ⬝ᵥ H.mulVec (star (l : Fin g → ℂ))) := by
  first | exact @GlobalTheory.CechPer.LogDer.main | exact GlobalTheory.CechPer.LogDer.main | (intros; apply GlobalTheory.CechPer.LogDer.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearSubPiHermitianOfLatticeAddHomStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearSubPiHermitianOfLatticeAddHom
open Complex Matrix

namespace GlobalTheory

theorem exists_linear_sub_pi_mul_form_of_addMonoidHom :
    ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (H : Matrix (Fin g) (Fin g) ℂ), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H.mulVec (star z)).re) → ∀ p : Λ →+ ℂ, ∃ (f : (Fin g → ℂ) →L[ℂ] ℂ) (v : Fin g → ℂ), ∀ l : Λ, p l = f l - Real.pi * (v ⬝ᵥ H.mulVec (star (l : Fin g → ℂ))) := by
  intro g Λ H _ hΛ hH p
  obtain ⟨F, hF⟩ := AppellHumbert.exists_real_extension Λ hΛ p
  have hinj : Function.Injective H.vecMulLinear := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro v hv
    by_contra h0
    have := hH v h0
    rw [dotProduct_mulVec] at this
    rw [vecMulLinear_apply] at hv
    simp [hv] at this
  have hsurj := LinearMap.injective_iff_surjective.1 hinj
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  let s : Fin g → ℂ := fun b => (F (Pi.single b 1) - I * F (Pi.single b I)) / 2
  let c : Fin g → ℂ := fun b => (F (Pi.single b 1) + I * F (Pi.single b I)) / 2
  have hsplit : ∀ u, F u = s ⬝ᵥ u + c ⬝ᵥ star u := by
    intro u
    conv_lhs => rw [AppellHumbert.eq_sum_re_im u]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_add (f := _), map_smul, dotProduct, ← Finset.sum_add_distrib,
      Pi.star_apply, real_smul, s, c]
    refine Finset.sum_congr rfl fun b _ => ?_
    have h1 : u b = (u b).re + (u b).im * I := (re_add_im _).symm
    have h2 : star (u b) = (u b).re - (u b).im * I := by
      apply Complex.ext <;> simp
    rw [h2]
    generalize (u b).re = x at *
    generalize (u b).im = y at *
    rw [h1]
    linear_combination (y * F (Pi.single b I)) * I_mul_I
  obtain ⟨v, hv⟩ := hsurj (-(Real.pi : ℂ)⁻¹ • c)
  rw [vecMulLinear_apply] at hv
  refine ⟨LinearMap.toContinuousLinearMap (dotProductBilin ℂ ℂ s), v, fun l => ?_⟩
  rw [← hF, hsplit, dotProduct_mulVec, hv, smul_dotProduct]
  simp only [LinearMap.coe_toContinuousLinearMap', dotProductBilin_apply_apply, smul_eq_mul]
  field_simp
  ring

end GlobalTheory
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linear_sub_pi_hermitian_of_lattice_addHom : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (H : Matrix (Fin g) (Fin g) ℂ), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H.mulVec (star z)).re) → ∀ p : Λ →+ ℂ, ∃ (f : (Fin g → ℂ) →L[ℂ] ℂ) (v : Fin g → ℂ), ∀ l : Λ, p l = f l - Real.pi * (v ⬝ᵥ H.mulVec (star (l : Fin g → ℂ))) := by
  first | exact @GlobalTheory.exists_linear_sub_pi_mul_form_of_addMonoidHom | exact GlobalTheory.exists_linear_sub_pi_mul_form_of_addMonoidHom | (intros; apply GlobalTheory.exists_linear_sub_pi_mul_form_of_addMonoidHom <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectivePeriodMapAbelianVarietyLattice
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PerSurj

theorem isPer_transport {A : Over (Sp ℂ)} {g : ℕ} (ex₀ : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ A))
    (Λ₀ : Submodule ℤ (Fin g → ℂ))
    (h₀ : ∀ p : Λ₀ →+ ℂ, ∃ x, IsPer ex₀ Λ₀ x p) :
    ∀ (ex : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ A)) (Λ : Submodule ℤ (Fin g → ℂ)),
      ex = ex₀ → Λ = Λ₀ → ∀ p : Λ →+ ℂ, ∃ x, IsPer ex Λ x p := by
  intro ex Λ hex hΛ
  subst hex hΛ
  exact h₀

theorem surj_of_isAH (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (M : LB A.left) (u : HolUnif A M g)
    (hA : IsAbelianScheme A) (hM : M.IsLB) (H : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) (hAH : u.IsAH H χ) :
    ∀ p : u.Λ →+ ℂ, ∃ x, IsPer u.ex u.Λ x p := by
  intro p
  obtain ⟨f, v, hfv⟩ := GlobalTheory.T.exists_linear_sub_pi_hermitian_of_lattice_addHom g u.Λ H u.discrete u.full hAH.2.1 p
  obtain ⟨hd, hr, hq⟩ := GlobalTheory.T.appell_humbert_frame_log_derivative_quasi_periodic A g M u hA hM H χ hAH v
  refine GlobalTheory.T.exists_cechClass_of_quasiPeriodic_holomorphic_cover A g M u hA M.ι M.U
    (fun i z => f z + fderiv ℂ (u.fr i) z v / u.fr i z) p hM.cover ?_ ?_ ?_
  · intro i
    exact f.differentiable.differentiableOn.add (hd i)
  · intro i j
    have : ((fun z => f z + fderiv ℂ (u.fr i) z v / u.fr i z) - fun z => f z + fderiv ℂ (u.fr j) z v / u.fr j z) =
        ((fun z => fderiv ℂ (u.fr i) z v / u.fr i z) - fun z => fderiv ℂ (u.fr j) z v / u.fr j z) := by
      funext z; simp only [Pi.sub_apply]; ring
    rw [this]; exact hr i j
  · intro i l z hz
    rw [hq i l z hz, map_add (f := _), hfv l]
    ring

theorem main : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ p : u.Λ →+ ℂ, ∃ x, IsPer u.ex u.Λ x p := by
  intro A _ g L u hA
  obtain ⟨M, u', H, χ, hM, hex, hΛ, hAH⟩ := GlobalTheory.AHExists.exists_isAH A g hA L u
  exact isPer_transport u'.ex u'.Λ (surj_of_isAH A g M u' hA hM H χ hAH) u.ex u.Λ hex.symm hΛ.symm

end GlobalTheory.PerSurj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectivePeriodMapAbelianVarietyLatticeStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.surjective_periodMap_abelianVariety_lattice : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ p : u.Λ →+ ℂ, ∃ x, IsPer u.ex u.Λ x p := by
  first | exact @GlobalTheory.PerSurj.main | exact GlobalTheory.PerSurj.main | (intros; apply GlobalTheory.PerSurj.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPerUnique
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCechDeRhamPeriodsZeroClassEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHolomorphicPrimitiveOfCechDeRhamPeriods
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHolomorphicPrimitiveOfCechDeRhamPeriods
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem exists_prim_of_isPer : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ x q,
    IsPer u.ex u.Λ x q → ∀ c, Hyp1.mk _ c = x → ∃ h, IsPrim u.ex c h ∧
      ∀ (U : A.left.affineOpens) (l : u.Λ), ∀ z ∈ pre u.ex U.1, h U (z + l) = h U z + q l := by
  intro A _ g L u x q hx c hc
  obtain ⟨hOpen, hDiff, -, hPer, -, -, -, -, hRes, hHom, -, -⟩ := GlobalTheory.CechPer.pre_val_rules A g L u
  obtain ⟨c₀, h₀, hc₀, ⟨p1, p2, p3⟩, hp⟩ := hx
  obtain ⟨b, hb⟩ := Hyp1.mk_eq_mk.1 (hc.trans hc₀.symm)
  have hval_add : ∀ (U : A.left.Opens) (s t : Sec (str A) U), ∀ z ∈ pre u.ex U,
      val u.ex U (s + t) z = val u.ex U s z + val u.ex U t z := by
    intro U s t z hz
    obtain ⟨e, he⟩ := hHom U z hz
    erw [he, he, he, map_add]
  have hval_sub : ∀ (U : A.left.Opens) (s t : Sec (str A) U), ∀ z ∈ pre u.ex U,
      val u.ex U (s - t) z = val u.ex U s z - val u.ex U t z := by
    intro U s t z hz
    obtain ⟨e, he⟩ := hHom U z hz
    erw [he, he, he, map_sub]
  have hcf : ∀ (U V : A.left.affineOpens) (a : Opposite.op U ⟶ Opposite.op V),
      c.1.1 (Opposite.op U) (Opposite.op V) a = c₀.1.1 (Opposite.op U) (Opposite.op V) a +
        (b (Opposite.op V) - Sec.res (str A) (leOfHom a.unop) (b (Opposite.op U))) := by
    intro U V a
    have := congrArg (fun y : Tot1 (OAff (str A)) ↦ y.1 (Opposite.op U) (Opposite.op V) a) hb
    simp only [dTot0_f] at this
    exact (eq_add_of_sub_eq' this.symm :)
  have hcω : ∀ U : A.left.affineOpens, c.1.2 (Opposite.op U) =
      c₀.1.2 (Opposite.op U) + KaehlerDifferential.D ℂ _ (b (Opposite.op U)) := by
    intro U
    have := congrArg (fun y : Tot1 (OAff (str A)) ↦ y.2 (Opposite.op U)) hb
    simp only [dTot0_ω] at this
    change _ = (c.1 - c₀.1).2 _ at this
    rw [this]
    change c.1.2 _ = c₀.1.2 _ + (c.1.2 _ - c₀.1.2 _)
    abel
  refine ⟨fun U z ↦ h₀ U z + val u.ex U.1 (b (Opposite.op U)) z, ⟨fun U ↦ ?_, fun U V a z hz ↦ ?_, fun U z hz ↦ ?_⟩,
    fun U l z hz ↦ ?_⟩
  · exact (p1 U).add (hDiff U.1 _)
  · have hle : V.1 ≤ U.1 := leOfHom a.unop
    have hr : val u.ex V.1 (Sec.res (str A) hle (b (Opposite.op U))) z = val u.ex U.1 (b (Opposite.op U)) z :=
      hRes U.1 V.1 hle _ z hz
    simp only
    rw [p2 U V a z hz, hcf U V a, hval_add _ _ _ z hz, hval_sub _ _ _ z hz, hr]
    ring
  · have hd₀ : DifferentiableAt ℂ (h₀ U) z := ((p1 U) z hz).differentiableAt ((hOpen U.1).mem_nhds hz)
    have hd₁ : DifferentiableAt ℂ (val u.ex U.1 (b (Opposite.op U))) z :=
      ((hDiff U.1 _) z hz).differentiableAt ((hOpen U.1).mem_nhds hz)
    obtain ⟨-, -, hD⟩ := GlobalTheory.T.uniformisedOneFormEvaluation_rules A g L u U.1 z hz
    change fderiv ℂ (h₀ U + val u.ex U.1 (b (Opposite.op U))) z = _
    rw [fderiv_add hd₀ hd₁, p3 U z hz, hcω U, map_add (f := _), hD]
  · simp only
    rw [hp U l z hz]
    erw [hPer]
    ring

end GlobalTheory.CechPer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHolomorphicPrimitiveOfCechDeRhamPeriodsStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_holomorphic_primitive_of_cechDeRham_periods : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ x q, IsPer u.ex u.Λ x q → ∀ c, Hyp1.mk _ c = x → ∃ h, IsPrim u.ex c h ∧ ∀ (U : A.left.affineOpens) (l : u.Λ), ∀ z ∈ pre u.ex U.1, h U (z + l) = h U z + q l := by
  first | exact @GlobalTheory.CechPer.exists_prim_of_isPer | exact GlobalTheory.CechPer.exists_prim_of_isPer | (intros; apply GlobalTheory.CechPer.exists_prim_of_isPer <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCechDeRhamPeriodsZeroClassEqZero
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem zero_periods_eq_zero : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ q, IsPer u.ex u.Λ 0 q → q = 0 := by
  intro A _ g L u q hq
  obtain ⟨hopen, -, hadd, -, hinf, -, -, hbasis, -, -, -, htop⟩ := GlobalTheory.T.uniformisation_preimage_value_rules A g L u
  obtain ⟨h, ⟨hdiff, hres0, hder0⟩, hper⟩ := GlobalTheory.T.exists_holomorphic_primitive_of_cechDeRham_periods A g L u 0 q hq 0 (map_zero _)
  have hres : ∀ (U V : A.left.affineOpens), V.1 ≤ U.1 → ∀ z ∈ pre u.ex V.1, h V z = h U z := by
    intro U V hVU z hz
    have := hres0 U V (homOfLE hVU).op z hz
    rw [this]
    change h U z + valAt' _ _ (0 : Γ(A.left, V.1)) = h U z
    unfold valAt' valAt
    split_ifs <;> simp
  have hder : ∀ (U : A.left.affineOpens), ∀ z ∈ pre u.ex U.1, fderiv ℂ (h U) z = 0 := by
    intro U z hz
    rw [hder0 U z hz]
    change evForm u.ex U.1 z 0 = 0
    simp
  have hex : ∀ z, ∃ U : A.left.affineOpens, z ∈ pre u.ex U.1 := fun z ↦ by
    obtain ⟨W, -, hW⟩ := hbasis ⊤ z (htop z)
    exact ⟨W, hW⟩
  choose Uz hUz using hex
  let G : (Fin g → ℂ) → ℂ := fun z ↦ h (Uz z) z
  have hG : ∀ (U : A.left.affineOpens), ∀ z ∈ pre u.ex U.1, G z = h U z := by
    intro U z hz
    obtain ⟨W, hWle, hW⟩ := hbasis (U.1 ⊓ (Uz z).1) z (by rw [hinf]; exact ⟨hz, hUz z⟩)
    have h1 := hres U W (hWle.trans inf_le_left) z hW
    have h2 := hres (Uz z) W (hWle.trans inf_le_right) z hW
    simp only [G]
    rw [← h1, ← h2]
  have hloc : ∀ z, G =ᶠ[nhds z] h (Uz z) := fun z ↦ by
    filter_upwards [(hopen _).mem_nhds (hUz z)] with w hw
    exact hG _ w hw
  have hGd : Differentiable ℂ G := fun z ↦
    (((hdiff (Uz z)).differentiableAt ((hopen _).mem_nhds (hUz z)))).congr_of_eventuallyEq (hloc z)
  have hGf : ∀ z, fderiv ℂ G z = 0 := fun z ↦ by
    rw [(hloc z).fderiv_eq]; exact hder _ z (hUz z)
  funext l
  have hl : (0 : Fin g → ℂ) + l ∈ pre u.ex (Uz 0).1 := (hadd _ l 0).2 (hUz 0)
  have e1 := hper (Uz 0) l 0 (hUz 0)
  have e2 := hG (Uz 0) _ hl
  have e3 := is_const_of_fderiv_eq_zero hGd hGf ((0 : Fin g → ℂ) + l) 0
  have e4 := hG (Uz 0) 0 (hUz 0)
  simp only [Pi.zero_apply]
  linear_combination -e1 - e2 + e3 + e4

end GlobalTheory.CechPer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCechDeRhamPeriodsZeroClassEqZeroStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasCechDeRhamPeriods_zero_class_eq_zero : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ q, IsPer u.ex u.Λ 0 q → q = 0 := by
  first | exact @GlobalTheory.CechPer.zero_periods_eq_zero | exact GlobalTheory.CechPer.zero_periods_eq_zero | (intros; apply GlobalTheory.CechPer.zero_periods_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPerUnique
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.CechPer.isPer_unique : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ x q q', IsPer u.ex u.Λ x q → IsPer u.ex u.Λ x q' → q = q' := by
  intro A _ g L u x q q' hq hq'
  have h := ((GlobalTheory.T.cechDeRhamPeriods_linear A g L u).1 x x q q' hq hq').2
  rw [sub_self] at h
  exact sub_eq_zero.mp (GlobalTheory.T.hasCechDeRhamPeriods_zero_class_eq_zero A g L u _ h)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPerUniqueStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPer_unique' : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ x q q', IsPer u.ex u.Λ x q → IsPer u.ex u.Λ x q' → q = q' := by
  first | exact @GlobalTheory.CechPer.isPer_unique | exact GlobalTheory.CechPer.isPer_unique | (intros; apply GlobalTheory.CechPer.isPer_unique <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeEvaluationSpanDualFinrank
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeEvaluationSpanDualFinrank
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem span_eval_eq_top_and_finrank_dual : ∀ (W : Type 1) [AddCommGroup W] [Module ℂ W] (Λ : Type) [AddCommGroup Λ] (n : ℕ) (b : Module.Basis (Fin n) ℤ Λ) (P : Λ →+ Module.Dual ℂ W), (∀ w, (∀ l, P l w = 0) → w = 0) → (∀ p : Λ →+ ℂ, ∃ w, ∀ l, P l w = p l) → Submodule.span ℂ (Set.range P) = ⊤ ∧ Module.finrank ℂ (Module.Dual ℂ W) = n := by
  intro W _ _ Λ _ n b P hinj hsurj
  let Φ : W →ₗ[ℂ] (Fin n → ℂ) := LinearMap.pi (fun i => P (b i))
  have hΦ : ∀ w i, Φ w i = P (b i) w := fun w i => rfl
  have h1 : Function.Injective Φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro w hw
    apply hinj
    intro l
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← b.sum_repr l, map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_zsmul, LinearMap.smul_apply, ← hΦ, hw]
    simp
  have h2 : Function.Surjective Φ := by
    intro v
    obtain ⟨w, hw⟩ := hsurj (b.constr ℤ v).toAddMonoidHom
    refine ⟨w, funext fun i => ?_⟩
    rw [hΦ, hw]
    simp
  let e : W ≃ₗ[ℂ] (Fin n → ℂ) := LinearEquiv.ofBijective Φ ⟨h1, h2⟩
  let c : Module.Basis (Fin n) ℂ W := Module.Basis.ofEquivFun e
  have hc : ∀ i, c.dualBasis i = P (b i) := by
    intro i
    ext w
    rw [Module.Basis.dualBasis_apply]
    exact hΦ w i
  refine ⟨?_, ?_⟩
  · rw [eq_top_iff, ← c.dualBasis.span_eq]
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨b i, (hc i).symm⟩
  · simpa using Module.finrank_eq_card_basis c.dualBasis

end GlobalTheory.CechPer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeEvaluationSpanDualFinrankStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeEvaluation_span_dual_finrank : ∀ (W : Type 1) [AddCommGroup W] [Module ℂ W] (Λ : Type) [AddCommGroup Λ] (n : ℕ) (b : Module.Basis (Fin n) ℤ Λ) (P : Λ →+ Module.Dual ℂ W), (∀ w, (∀ l, P l w = 0) → w = 0) → (∀ p : Λ →+ ℂ, ∃ w, ∀ l, P l w = p l) → Submodule.span ℂ (Set.range P) = ⊤ ∧ Module.finrank ℂ (Module.Dual ℂ W) = n := by
  first | exact @GlobalTheory.CechPer.span_eval_eq_top_and_finrank_dual | exact GlobalTheory.CechPer.span_eval_eq_top_and_finrank_dual | (intros; apply GlobalTheory.CechPer.span_eval_eq_top_and_finrank_dual <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisOfDiscreteOfSpanEqTopComplexPi
namespace GlobalTheory

theorem exists_basis_of_discrete_of_span_eq_top_complex_pi :
    ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ →
      Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
      ∃ b : Module.Basis (Fin (2 * g)) ℤ Λ,
        LinearIndependent ℝ (fun i => (b i : Fin g → ℂ)) ∧
          Submodule.span ℝ (Set.range fun i => (b i : Fin g → ℂ)) = ⊤ := by
  intro g Λ hd h
  haveI : IsZLattice ℝ Λ := ⟨h⟩
  haveI : Module.Free ℤ Λ := ZLattice.module_free ℝ Λ
  haveI : Module.Finite ℤ Λ := ZLattice.module_finite ℝ Λ
  have hr : Module.finrank ℤ Λ = 2 * g := by
    rw [ZLattice.rank ℝ Λ, Module.finrank_pi_fintype, Finset.sum_const, Complex.finrank_real_complex]
    simp [mul_comm]
  let b : Module.Basis (Fin (2 * g)) ℤ Λ := Module.finBasisOfFinrankEq ℤ Λ hr
  have e : (fun i => (b i : Fin g → ℂ)) = ⇑(b.ofZLatticeBasis ℝ Λ) := by
    funext i
    exact (Module.Basis.ofZLatticeBasis_apply ℝ Λ b i).symm
  refine ⟨b, ?_, ?_⟩
  · rw [e]; exact (b.ofZLatticeBasis ℝ Λ).linearIndependent
  · rw [e]; exact (b.ofZLatticeBasis ℝ Λ).span_eq

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodMapSpanTopAndFinrankFromCechPeriods
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem span_periods_eq_top_and_finrank : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ P : u.Λ →+ HdR A, (∀ c : primDR A, IsPer u.ex u.Λ (cmp1 (str A) c.1) fun l => P l c) → Submodule.span ℂ (Set.range P) = ⊤ ∧ Module.finrank ℂ (HdR A) = 2 * g := by
  intro A _ g L u hA P hP
  obtain ⟨b, -, -⟩ := GlobalTheory.exists_basis_of_discrete_of_span_eq_top_complex_pi g u.Λ u.discrete u.full
  refine GlobalTheory.T.latticeEvaluation_span_dual_finrank (primDR A) u.Λ (2 * g) b P (fun w hw ↦ ?_) (fun p ↦ ?_)
  · have h0 : (fun l ↦ P l w) = 0 := funext hw
    have h1 := hP w
    rw [h0] at h1
    have h2 := GlobalTheory.T.cechDeRham_class_eq_zero_of_periods_zero A g L u hA _ h1
    have h3 : w.1 = 0 := (GlobalTheory.T.bijective_cmp1_of_isAbelianScheme_over_complex A hA).1 (h2.trans (map_zero _).symm)
    exact Subtype.ext h3
  · obtain ⟨x, hx⟩ := GlobalTheory.T.surjective_periodMap_abelianVariety_lattice A g L u hA p
    obtain ⟨c, rfl⟩ := (GlobalTheory.T.bijective_cmp1_of_isAbelianScheme_over_complex A hA).2 x
    have hc := GlobalTheory.T.mem_primitiveDeRhamCohomology_of_additive_periods A g L u hA c p hx
    exact ⟨⟨c, hc⟩, fun l ↦ congrFun (GlobalTheory.T.isPer_unique' A g L u _ _ _ (hP ⟨c, hc⟩) hx) l⟩

end GlobalTheory.CechPer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodMapSpanTopAndFinrankFromCechPeriodsStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_map_span_top_and_finrank_from_cech_periods : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ P : u.Λ →+ HdR A, (∀ c : primDR A, IsPer u.ex u.Λ (cmp1 (str A) c.1) fun l => P l c) → Submodule.span ℂ (Set.range P) = ⊤ ∧ Module.finrank ℂ (HdR A) = 2 * g := by
  first | exact @GlobalTheory.CechPer.span_periods_eq_top_and_finrank | exact GlobalTheory.CechPer.span_periods_eq_top_and_finrank | (intros; apply GlobalTheory.CechPer.span_periods_eq_top_and_finrank <;> assumption)
end
