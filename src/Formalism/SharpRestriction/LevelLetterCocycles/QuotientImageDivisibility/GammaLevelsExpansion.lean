module

public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.CmpOfMemX

@[expose] public section

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.ExpPowSubOne
noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc PowerSeries Formalism.MainNotions.N.Pv.LocalLengthBound.Ser

section Div

variable {LL : Type} [Field LL] {V : Type} [AddCommGroup V] [Module LL V]

theorem div_exists {m : ℤ} {e : ℤ → V} (he : LB m e) (u : PowerSeries LL)
    (hu : constantCoeff u ≠ 0) (K : ℕ) :
    ∃ d : ℤ → V, LB (m - K) d ∧ smulS ((X * u) ^ K) d = e := by
  set e' : ℤ → V := fun k => e (k + K) with he'
  have hLB' : LB (m - K) e' := fun k hk => he _ (by omega)
  have huK : constantCoeff (u ^ K) ≠ 0 := by rw [map_pow]; exact pow_ne_zero _ hu
  refine ⟨smulS (u ^ K)⁻¹ e', LB_smulS hLB' _, ?_⟩
  rw [mul_pow, smulS_mul (LB_smulS hLB' _), ← smulS_mul hLB', PowerSeries.mul_inv_cancel _ huK,
    smulS_one hLB', smulS_X_pow hLB']
  funext k
  simp [he']

theorem div_unique {m : ℤ} {d d' : ℤ → V} (hd : LB m d) (hd' : LB m d') (u : PowerSeries LL)
    (hu : constantCoeff u ≠ 0) (K : ℕ) (h : smulS ((X * u) ^ K) d = smulS ((X * u) ^ K) d') :
    d = d' := by
  have huK : constantCoeff (u ^ K) ≠ 0 := by rw [map_pow]; exact pow_ne_zero _ hu
  have h0 : smulS ((X * u) ^ K) (d - d') = 0 := by
    rw [smulS_sub hd hd', h, sub_self]
  rw [mul_pow, smulS_mul (LB_sub hd hd'), smulS_X_pow (LB_smulS (LB_sub hd hd') _)] at h0
  have h1 : smulS (u ^ K) (d - d') = 0 := by
    funext k
    have := congrFun h0 (k + K)
    simpa using this
  have h2 := smulS_inv (LB_sub hd hd') (u ^ K) huK
  rw [h1] at h2
  have h3 : smulS (u ^ K)⁻¹ (0 : ℤ → V) = 0 := by
    funext k
    simp [smulS]
  rw [h3] at h2
  exact sub_eq_zero.1 h2.symm

end Div

section Zero

variable {LL : Type} [Field LL]

theorem exp_pow_sub_one (E : PowerSeries LL) (h0 : constantCoeff E = 1)
    (hd : PowerSeries.derivative (R := LL) E = E) (p : ℕ) :
    ∃ w : PowerSeries LL, E ^ p - 1 = X * w ∧ constantCoeff w = (p : LL) := by
  obtain ⟨E₁, hE₁⟩ : ∃ E₁, E = 1 + X * E₁ := by
    refine ⟨PowerSeries.mk fun j => coeff (j + 1) E, ?_⟩
    have := PowerSeries.eq_X_mul_shift_add_const E
    rw [h0, map_one, add_comm] at this
    exact this
  have hc1 : constantCoeff E₁ = 1 := by
    have h1 := congrArg (coeff 0) hd
    rw [PowerSeries.coeff_derivative] at h1
    have h2 : coeff 1 E = constantCoeff E₁ := by
      rw [hE₁]; simp
    simp only [zero_add, Nat.cast_zero, mul_one, coeff_zero_eq_constantCoeff_apply, h0] at h1
    rw [← h2]
    simpa using h1
  refine ⟨E₁ * ∑ j ∈ Finset.range p, (1 + X * E₁) ^ j, ?_, ?_⟩
  · rw [hE₁, ← mul_assoc]
    have g := geom_sum_mul (1 + X * E₁) p
    rw [add_sub_cancel_left] at g
    rw [← g, mul_comm]
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [map_mul, map_sum, hc1, one_mul]
      simp [map_pow]

end Zero

section Simple

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

variable (W : LocWach PD LL O v n)

theorem lev_q_simple (c : ZMod n) (ζ : LL) (hζ : IsPrimitiveRoot ζ PD.p) :
    ∃ u : PowerSeries LL, W.lev c ζ W.q = X * u ∧ constantCoeff u ≠ 0 := by
  have hp0 : (PD.p : LL) ≠ 0 := Formalism.MainNotions.UnusedSlot80.ArcF.p_ne_zero W
  obtain ⟨E, hE0, hEd, hE⟩ := W.lev_π c ζ ⟨1, by simpa using hζ⟩
  have hζ1 : ζ ≠ 1 := hζ.ne_one PD.hp.one_lt
  have hπq : (letπ : LetA O n) * W.q = (1 + letπ) ^ PD.p - 1 := by
    funext i
    simp only [letπ, LocWach.q, Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, Pi.add_apply, Pi.one_apply]
    exact W.q₀_def
  have hl := congrArg (W.lev c ζ) hπq
  rw [map_mul, map_sub, map_pow, map_add (f := _), map_one] at hl
  rw [hE, mul_pow, ← map_pow, hζ.pow_eq_one, map_one, one_mul] at hl
  obtain ⟨w, hw, hw0⟩ := exp_pow_sub_one E hE0 hEd PD.p
  rw [hw] at hl
  have hπc : constantCoeff (W.lev c ζ letπ) ≠ 0 := by
    have := congrArg constantCoeff hE
    rw [map_add (f := _), map_one, map_mul, constantCoeff_C, hE0, mul_one] at this
    intro h0
    rw [h0, add_zero] at this
    exact hζ1 this.symm
  refine ⟨w * (W.lev c ζ letπ)⁻¹, ?_, ?_⟩
  · have h2 : W.lev c ζ letπ * W.lev c ζ W.q * (W.lev c ζ letπ)⁻¹ =
        X * w * (W.lev c ζ letπ)⁻¹ := by rw [hl]
    rw [mul_comm (W.lev c ζ letπ), mul_assoc, PowerSeries.mul_inv_cancel _ hπc, mul_one] at h2
    rw [h2, mul_assoc]
  · rw [map_mul, hw0, PowerSeries.constantCoeff_inv]
    exact mul_ne_zero hp0 (inv_ne_zero hπc)

end Simple

end Formalism.MainNotions.N.Pv.LocalLengthBound
end
end

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc PowerSeries Formalism.MainNotions.N.Pv.LocalLengthBound.Ser TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

section Gam

variable (W : LocWach PD LL O v n)

theorem cc_φ₀ (f : PowerSeries O) : constantCoeff (W.φ₀ f) = constantCoeff f := by
  have e := PowerSeries.eq_X_mul_shift_add_const f
  have hC : ∀ r : O, W.φ₀ (C r) = C r := fun r => by
    have := W.φ₀.commutes r
    rwa [show (algebraMap O (PowerSeries O) r) = C r from rfl] at this
  conv_lhs => rw [e]
  rw [map_add (f := _), map_mul, W.φ₀_X, hC]
  simp

theorem gam_q [IsDomain O] (g : W.Gam) :
    ∃ v : LetA O n, W.γA g W.q = W.q * v ∧ IsUnit v := by
  obtain ⟨V, hV⟩ := PowerSeries.X_dvd_iff.mpr (W.γ₀_X g).1
  have hcV : constantCoeff V = (W.χΓ g : O) := by
    have := (W.γ₀_X g).2
    rw [hV, PowerSeries.coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply] at this
    exact this
  have hVu : IsUnit V := by
    rw [PowerSeries.isUnit_iff_constantCoeff, hcV]; exact Units.isUnit _
  have hφVu : IsUnit (W.φ₀ V) := by
    rw [PowerSeries.isUnit_iff_constantCoeff, cc_φ₀, hcV]; exact Units.isUnit _
  have key : W.q₀ * W.φ₀ V = V * W.γ₀ g W.q₀ := by
    have h := W.γ₀_comm g PowerSeries.X
    rw [hV, map_mul, W.φ₀_X, map_mul, hV] at h
    have h2 : PowerSeries.X * (W.q₀ * W.φ₀ V) = PowerSeries.X * (V * W.γ₀ g W.q₀) := by
      rw [← mul_assoc, ← mul_assoc]; exact h
    exact mul_left_cancel₀ PowerSeries.X_ne_zero h2
  obtain ⟨Vu, hVu'⟩ := hVu
  refine ⟨fun _ => W.φ₀ V * ((Vu⁻¹ : (PowerSeries O)ˣ) : PowerSeries O), ?_, ?_⟩
  · funext i
    show W.γ₀ g W.q₀ = W.q₀ * (W.φ₀ V * ((Vu⁻¹ : (PowerSeries O)ˣ) : PowerSeries O))
    rw [← mul_assoc, key, ← hVu', mul_comm (Vu : PowerSeries O), mul_assoc, Units.mul_inv, mul_one]
  · refine Pi.isUnit_iff.2 fun _ => hφVu.mul (Units.isUnit _)

end Gam

section ArithmeticCylinders

theorem cc_rescale {LL' : Type} [Field LL'] (χ : LL') (u : PowerSeries LL') :
    constantCoeff (PowerSeries.rescale χ u) = constantCoeff u := by
  rw [← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply,
    PowerSeries.coeff_rescale, pow_zero, one_mul]

variable (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem gamma_levels_expansion [IsDomain O] (hs : W.s = 1) (c : ZMod n) (ζ : LL)
    (hLv : ∀ (x : ↥(W.N T)) (k : ℤ), W.levN T c ζ x k ∈ Formalism.MainNotions.WachCoordinates.FilLev W T c 0 (-k))
    (χ : LL) (hχ0 : χ ≠ 0)
    (hγN : ∀ (x : W.DD T) (hx : x ∈ W.N T) (hγx : W.γ T x ∈ W.N T) (k : ℤ),
      W.levN T c ζ ⟨W.γ T x, hγx⟩ k = χ ^ k • W.levN T c ζ ⟨x, hx⟩ k)
    (hγA : ∀ f : LetA O n, W.lev c ζ (W.γA W.gam f) = PowerSeries.rescale χ (W.lev c ζ f))
    (u : PowerSeries LL) (hu : W.lev c ζ W.q = X * u) (hu0 : constantCoeff u ≠ 0)
    {K : ℕ} {w : W.DD T} (hwN : W.Q ^ K • w ∈ W.N T) (hγw : W.γ T w - w ∈ W.N T) :
    ∃ d : ℤ → T.V ⊗[Qp] BdR, (∃ m, LB m d) ∧
      W.levN T c ζ ⟨W.Q ^ K • w, hwN⟩ = smulS ((X * u) ^ K) d ∧
      ∀ i : ℤ, (χ ^ i - 1) • d i ∈ Formalism.MainNotions.WachCoordinates.FilLev W T c 0 (-i) := by
  have hQ : W.Q = W.q := Q_eq_q W hs
  set x : ↥(W.N T) := ⟨W.Q ^ K • w, hwN⟩ with hxdef
  obtain ⟨m₀, hm₀⟩ := W.levN_supp T c ζ x
  obtain ⟨d, hdLB, hde⟩ := div_exists (m := m₀) hm₀ u hu0 K
  refine ⟨d, ⟨_, hdLB⟩, hde.symm, ?_⟩

  obtain ⟨vv, hvv, hvu⟩ := gam_q W W.gam
  obtain ⟨vU, hvU⟩ := hvu
  set v' : LetA O n := ((vU⁻¹ : (LetA O n)ˣ) : LetA O n)

  have hlv : W.lev c ζ vv = PowerSeries.C χ * PowerSeries.rescale χ u * u⁻¹ := by
    have h1 := hγA W.q
    rw [hvv, map_mul, hu, map_mul, PowerSeries.rescale_X] at h1
    have h2 : X * (u * W.lev c ζ vv) = X * (PowerSeries.C χ * PowerSeries.rescale χ u) := by
      rw [← mul_assoc, h1]; ring
    have h3 := mul_left_cancel₀ PowerSeries.X_ne_zero h2
    rw [← h3, mul_comm u, mul_assoc, PowerSeries.mul_inv_cancel _ hu0, mul_one]
  have hv'vv : v' * vv = 1 := by rw [← hvU]; exact Units.inv_mul vU
  have hlv' : W.lev c ζ v' = PowerSeries.C χ⁻¹ * u * (PowerSeries.rescale χ u)⁻¹ := by
    have hr0 : constantCoeff (PowerSeries.rescale χ u) ≠ 0 := by
      rw [cc_rescale]; exact hu0
    have h1 : W.lev c ζ vv * W.lev c ζ v' = 1 := by
      rw [← map_mul, mul_comm, hv'vv, map_one]
    rw [hlv] at h1
    have hAA : (PowerSeries.C χ⁻¹ * u * (PowerSeries.rescale χ u)⁻¹) *
        (PowerSeries.C χ * PowerSeries.rescale χ u * u⁻¹) = 1 := by
      calc (PowerSeries.C χ⁻¹ * u * (PowerSeries.rescale χ u)⁻¹) *
            (PowerSeries.C χ * PowerSeries.rescale χ u * u⁻¹)
          = (PowerSeries.C χ⁻¹ * PowerSeries.C χ) * (u * u⁻¹) *
            ((PowerSeries.rescale χ u)⁻¹ * PowerSeries.rescale χ u) := by ring
        _ = 1 := by
          rw [← map_mul, inv_mul_cancel₀ hχ0, map_one, PowerSeries.mul_inv_cancel _ hu0,
            PowerSeries.inv_mul_cancel _ hr0]
          ring
    calc W.lev c ζ v' = ((PowerSeries.C χ⁻¹ * u * (PowerSeries.rescale χ u)⁻¹) *
          (PowerSeries.C χ * PowerSeries.rescale χ u * u⁻¹)) * W.lev c ζ v' := by rw [hAA, one_mul]
      _ = (PowerSeries.C χ⁻¹ * u * (PowerSeries.rescale χ u)⁻¹) *
          (PowerSeries.C χ * PowerSeries.rescale χ u * u⁻¹ * W.lev c ζ v') := by ring
      _ = _ := by rw [h1, mul_one]

  have hγx : W.γ T (W.Q ^ K • w) ∈ W.N T := W.N_Γ T W.gam _ hwN
  have hγw' : W.Q ^ K • W.γ T w = v' ^ K • W.γ T (W.Q ^ K • w) := by
    have e1 : W.γ T (W.Q ^ K • w) = W.γA W.gam (W.Q ^ K) • W.γ T w :=
      Formalism.MainNotions.UnusedSlot80.SatW.γD_smulA' W T W.gam _ w
    rw [e1, map_pow, hQ, hvv, smul_smul]
    congr 1
    calc W.q ^ K = (v' * vv) ^ K * W.q ^ K := by rw [hv'vv, one_pow, one_mul]
      _ = v' ^ K * (W.q * vv) ^ K := by ring
  have hQγN : W.Q ^ K • W.γ T w ∈ W.N T := by
    rw [hγw']; exact (W.N T).smul_mem _ hγx
  have hlevγ : W.levN T c ζ ⟨W.Q ^ K • W.γ T w, hQγN⟩ = smulS ((X * u) ^ K) (resc χ d) := by
    have e2 : (⟨W.Q ^ K • W.γ T w, hQγN⟩ : ↥(W.N T)) = v' ^ K • ⟨W.γ T (W.Q ^ K • w), hγx⟩ :=
      Subtype.ext hγw'
    have hLBγ : LB m₀ (W.levN T c ζ ⟨W.γ T (W.Q ^ K • w), hγx⟩) := fun k hk => by
      rw [hγN _ hwN hγx k, hm₀ k hk, smul_zero]
    rw [e2]
    have e3 : W.levN T c ζ (v' ^ K • ⟨W.γ T (W.Q ^ K • w), hγx⟩) =
        smulS (W.lev c ζ (v' ^ K)) (W.levN T c ζ ⟨W.γ T (W.Q ^ K • w), hγx⟩) :=
      funext fun k => W.levN_smul T c ζ _ _ k
    have e4 : W.levN T c ζ ⟨W.γ T (W.Q ^ K • w), hγx⟩ = resc χ (W.levN T c ζ x) :=
      funext fun k => hγN _ hwN hγx k
    rw [e3, e4, ← hde, ← smulS_rescale hdLB χ hχ0, ← smulS_mul (LB_resc hdLB χ), map_pow, hlv']
    congr 1
    rw [map_pow, map_mul, PowerSeries.rescale_X, ← mul_pow]
    congr 1
    have hr0 : constantCoeff (PowerSeries.rescale χ u) ≠ 0 := by
      rw [cc_rescale]; exact hu0
    have hC : PowerSeries.C χ⁻¹ * PowerSeries.C χ = (1 : PowerSeries LL) := by
      rw [← map_mul, inv_mul_cancel₀ hχ0, map_one]
    calc PowerSeries.C χ⁻¹ * u * (PowerSeries.rescale χ u)⁻¹ *
          (PowerSeries.C χ * X * PowerSeries.rescale χ u)
        = (PowerSeries.C χ⁻¹ * PowerSeries.C χ) *
          (PowerSeries.rescale χ u * (PowerSeries.rescale χ u)⁻¹) * (X * u) := by ring
      _ = X * u := by rw [hC, PowerSeries.mul_inv_cancel _ hr0]; ring

  have hdiffN : W.Q ^ K • (W.γ T w - w) ∈ W.N T := (W.N T).smul_mem _ hγw
  have hg : W.levN T c ζ ⟨W.Q ^ K • (W.γ T w - w), hdiffN⟩ =
      smulS ((X * u) ^ K) (W.levN T c ζ ⟨W.γ T w - w, hγw⟩) := by
    have e5 : (⟨W.Q ^ K • (W.γ T w - w), hdiffN⟩ : ↥(W.N T)) = W.Q ^ K • ⟨W.γ T w - w, hγw⟩ := rfl
    rw [e5]
    have := funext fun k => W.levN_smul T c ζ (W.Q ^ K) ⟨W.γ T w - w, hγw⟩ k
    rw [this, map_pow, hQ, hu]
    rfl
  have hsplit : (⟨W.Q ^ K • (W.γ T w - w), hdiffN⟩ : ↥(W.N T)) =
      ⟨W.Q ^ K • W.γ T w, hQγN⟩ - x := Subtype.ext (by simp [hxdef, smul_sub])
  rw [hsplit, map_sub, hlevγ] at hg
  obtain ⟨m₁, hm₁⟩ := W.levN_supp T c ζ ⟨W.γ T w - w, hγw⟩
  have hLBr := LB_resc hdLB χ
  have heq : resc χ d - d = W.levN T c ζ ⟨W.γ T w - w, hγw⟩ := by
    have hx' : W.levN T c ζ x = smulS ((X * u) ^ K) d := hde.symm
    rw [hx', ← smulS_sub hLBr hdLB] at hg
    exact div_unique (m := min (m₀ - K) m₁) (LB_mono (LB_sub hLBr hdLB) (min_le_left _ _))
      (LB_mono hm₁ (min_le_right _ _)) u hu0 K hg
  intro i
  have h := hLv ⟨W.γ T w - w, hγw⟩ i
  rw [← heq] at h
  simpa [resc, sub_smul] using h

end ArithmeticCylinders

end Formalism.MainNotions.N.Pv.LocalLengthBound
