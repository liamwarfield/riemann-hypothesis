module

public import Formalism.LocalToGlobal.GlobalTheory.GL3.IntegralityIffAwayAtD
public import Formalism.LocalToGlobal.InertKernelTheory.StatementAlg
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.InvarianceIffAdditiveMapsExist

@[expose] public section

section -- merged from Formalism.LocalToGlobal.PairingIndexBounds.PendingAdmissibility.LocalFDerivAdmissibility.RepRed
section -- merged from Formalism.LocalToGlobal.PairingIndexBounds.PendingAdmissibility.LocalFDerivAdmissibility.SubstInvFActS
section -- merged from Formalism.LocalToGlobal.PairingIndexBounds.PendingAdmissibility.LocalFDerivAdmissibility.AdmTwoPendantIff
section -- merged from Formalism.LocalToGlobal.PairingIndexBounds.PendingAdmissibility.LocalFDerivAdmissibility.CentralCharacterOfAdmTwo
section -- merged from Formalism.LocalToGlobal.PairingIndexBounds.PendingAdmissibility.LocalFDerivAdmissibility.CcMemOfK1loc
noncomputable section

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem

namespace Formalism.L2.PairingIndexBounds.PowerSeriesNecessity

variable {p : ℕ} [Fact p.Prime]

theorem cc_logF : PowerSeries.constantCoeff (logF p) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [logF, PowerSeries.coeff_mk]

theorem cc_logX {ι : Type} (K1 : Type) [Field K1] [Algebra (K0 p) K1] (i : ι) :
    MvPowerSeries.constantCoeff (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries ι K1)
      (PowerSeries.map (algebraMap (K0 p) K1) (logF p))) = 0 := by
  refine PowerSeries.constantCoeff_subst_eq_zero (by simp) _ ?_
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, cc_logF, map_zero]

theorem hasSubst_logX {ι : Type} [Finite ι] (K1 : Type) [Field K1] [Algebra (K0 p) K1] :
    MvPowerSeries.HasSubst (fun i : ι => PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries ι K1)
      (PowerSeries.map (algebraMap (K0 p) K1) (logF p))) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (cc_logX K1)

end Formalism.L2.PairingIndexBounds.PowerSeriesNecessity
end
end

noncomputable section

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend

namespace Formalism.L2.PairingIndexBounds.PowerSeriesNecessity

variable {p : ℕ} [Fact p.Prime]

theorem cc_resV {ι κ R : Type} [Semiring R] (f : κ → ι) (Th : MvPowerSeries ι R) :
    MvPowerSeries.constantCoeff (resV f Th) = MvPowerSeries.constantCoeff Th := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  show MvPowerSeries.coeff (Finsupp.mapDomain f 0) Th = _
  rw [Finsupp.mapDomain_zero]

end Formalism.L2.PairingIndexBounds.PowerSeriesNecessity
end
end

noncomputable section

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend

namespace Formalism.L2.PairingIndexBounds.PowerSeriesNecessity

variable {p : ℕ} [Fact p.Prime]

theorem subst_C_mul' {σ τ R : Type} [CommRing R] {a : σ → MvPowerSeries τ R} (ha : MvPowerSeries.HasSubst a) (c : R)
    (f : MvPowerSeries σ R) : MvPowerSeries.subst a (MvPowerSeries.C c * f) = MvPowerSeries.C c * MvPowerSeries.subst a f := by
  rw [← MvPowerSeries.smul_eq_C_mul, MvPowerSeries.subst_smul ha, MvPowerSeries.smul_eq_C_mul]

theorem K1gen_C_mul {ι : Type} [Fintype ι] {K1 : Type} [Field K1] [Algebra (Formalism.MainNotions.FormalGroupSystem.K0 p) K1] {R1 : Subring K1}
    {be : MvPowerSeries (Fin 2) (Formalism.MainNotions.FormalGroupSystem.K0 p)} {Th : MvPowerSeries (ι ⊕ ι) K1} {c : K1} (hc : c ∈ R1)
    (h : ExtensionGeneratorCondition p K1 R1 be Th) : ExtensionGeneratorCondition p K1 R1 be (MvPowerSeries.C c * Th) := by
  unfold ExtensionGeneratorCondition at h ⊢
  obtain ⟨Ph, U, hTh, hU, h1, h2, h3⟩ := h
  refine ⟨Ph, MvPowerSeries.C c * U, ?_, ?_, h1, h2, h3⟩
  · rw [hTh]
    ring
  · intro n
    have key : inParamK p K1 (MvPowerSeries.C c * U) = MvPowerSeries.C c * inParamK p K1 U := by
      unfold inParamK
      exact subst_C_mul' (hasSubst_logX K1) c U
    rw [key, MvPowerSeries.coeff_C_mul]
    exact R1.mul_mem hc (hU n)

theorem K1gen_C_mul_iff {ι : Type} [Fintype ι] {K1 : Type} [Field K1] [Algebra (Formalism.MainNotions.FormalGroupSystem.K0 p) K1] {R1 : Subring K1}
    {be : MvPowerSeries (Fin 2) (Formalism.MainNotions.FormalGroupSystem.K0 p)} {Th : MvPowerSeries (ι ⊕ ι) K1} {c : K1} (hc : c ∈ R1) (hc' : c⁻¹ ∈ R1)
    (hc0 : c ≠ 0) : ExtensionGeneratorCondition p K1 R1 be (MvPowerSeries.C c * Th) ↔ ExtensionGeneratorCondition p K1 R1 be Th := by
  constructor
  · intro h'
    have h2 := K1gen_C_mul hc' h'
    rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_mul] at h2
  · exact K1gen_C_mul hc

theorem adm_two_pendant_iff (D : Formalism.BasicNotions.D7) (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmbC X.G)
    (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (hst : FinStab X.Lv) {g : Formalism.MainNotions.GL3Theta.G1 p} (hLT : LTIso g) {T : Type}
    (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ T)
    (F : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p]) :
    letI := wittFractionAlgebraCp p
    letI := algKfC E.toCEmb
    adm2b D X (pendT X E hfin hst hLT pos F) ↔
      ∀ j < X.mm, ∀ (La : X.Lt j) (La' : X.Lt (j + 1)), (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup La'.2 →
        ∀ φ : Frm X j La La', ExtensionGeneratorCondition p ℂ_[p] (OcC p) (beLT hLT)
          (thA ℂ_[p] φ (SA X ℂ_[p] j (gamAt X j La.1 (delt X hfin j La.1 La.2))
            (thFOf X pos F j (La.1, (X.Lv.lev j La.1).smul (delt X hfin j La.1 La.2)⁻¹ La.2) La'))) := by
  let _ := wittFractionAlgebraCp p
  let _ := algKfC E.toCEmb
  have key : ∀ j (La : X.Lt j) (La' : X.Lt (j + 1)) (φ : Frm X j La La'),
      (pendT X E hfin hst hLT pos F).ThA j La La' φ = MvPowerSeries.C (chiN X ℂ_[p] hfin j La) *
        thA ℂ_[p] φ (SA X ℂ_[p] j (gamAt X j La.1 (delt X hfin j La.1 La.2))
          (thFOf X pos F j (La.1, (X.Lv.lev j La.1).smul (delt X hfin j La.1 La.2)⁻¹ La.2) La')) := by
    intro j La La' φ
    exact subst_C_mul' (hasSubst_invF ℂ_[p] φ) _ _
  have hn : ∀ j (La : X.Lt j), ‖chiN X ℂ_[p] hfin j La‖ = 1 := fun j La => norm_chiN X E.toCEmb hfin j La
  constructor
  · intro h j hj La La' hL hL' φ
    have h1 := h j hj La La' hL hL' φ
    change ExtensionGeneratorCondition p ℂ_[p] (OcC p) (beLT hLT) ((pendT X E hfin hst hLT pos F).ThA j La La' φ) at h1
    rw [key] at h1
    refine (K1gen_C_mul_iff ?_ ?_ ?_).1 h1
    · show ‖_‖ ≤ 1; rw [hn]
    · show ‖_‖ ≤ 1; rw [norm_inv, hn, inv_one]
    · intro h0; have := hn j La; rw [h0, norm_zero] at this; exact zero_ne_one this
  · intro h j hj La La' hL hL' φ
    change ExtensionGeneratorCondition p ℂ_[p] (OcC p) (beLT hLT) ((pendT X E hfin hst hLT pos F).ThA j La La' φ)
    rw [key]
    refine K1gen_C_mul ?_ (h j hj La La' hL hL' φ)
    show ‖_‖ ≤ 1; rw [hn]

end Formalism.L2.PairingIndexBounds.PowerSeriesNecessity
end
end

noncomputable section

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend
open scoped Kronecker Matrix

namespace Formalism.L2.PairingIndexBounds.PowerSeriesNecessity

variable {p : ℕ} [Fact p.Prime]

theorem latAt_smul (X : Sys p) (j : ℕ) (c : X.Lv.comp j) (γ : (X.Lv.lev j c).Γ) (L : (X.Pj j).Tup) (v : X.Pl) :
    X.latAt v j ((X.Lv.lev j c).smul γ L) =
      (X.latAt v j L).map ((Matrix.mulVecLin (gamAt X j c γ v : Matrix _ _ (X.G.P.Qq v))).restrictScalars (X.G.P.W v)) := by
  cases j <;> rfl

theorem map_map_inv {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq] {k : ℕ} (A : GL (Fin k) Qq)
    (M : Submodule W (Fin k → Qq)) :
    (M.map ((Matrix.mulVecLin (A : Matrix (Fin k) (Fin k) Qq)).restrictScalars W)).map
      ((Matrix.mulVecLin ((A⁻¹ : GL (Fin k) Qq) : Matrix (Fin k) (Fin k) Qq)).restrictScalars W) = M := by
  rw [← Submodule.map_comp]
  have hid : ((Matrix.mulVecLin ((A⁻¹ : GL (Fin k) Qq) : Matrix (Fin k) (Fin k) Qq)).restrictScalars W).comp
      ((Matrix.mulVecLin (A : Matrix (Fin k) (Fin k) Qq)).restrictScalars W) = LinearMap.id := by
    refine LinearMap.ext fun x => ?_
    simp [Matrix.mulVec_mulVec]
  rw [hid, Submodule.map_id]

def frmMove (X : Sys p) {j : ℕ} {La : X.Lt j} {La' : X.Lt (j + 1)} {L0 : (X.Pj j).Tup} (γ : (X.Lv.lev j La.1).Γ)
    (h : La.2 = (X.Lv.lev j La.1).smul γ L0) (φ : Frm X j La La') : Frm X j (La.1, L0) La' where
  g := fun v => (gamAt X j La.1 γ v)⁻¹ * φ.g v
  g' := φ.g'
  hg := fun v => by
    have h1 := φ.hg v
    rw [h, latAt_smul] at h1
    show X.latAt v j L0 = _
    rw [Units.val_mul, ← colSpan_mul, ← h1, map_map_inv]
  hg' := φ.hg'

def frmBack (X : Sys p) {j : ℕ} {La : X.Lt j} {La' : X.Lt (j + 1)} {L0 : (X.Pj j).Tup} (γ : (X.Lv.lev j La.1).Γ)
    (h : La.2 = (X.Lv.lev j La.1).smul γ L0) (φ0 : Frm X j (La.1, L0) La') : Frm X j La La' where
  g := fun v => gamAt X j La.1 γ v * φ0.g v
  g' := φ0.g'
  hg := fun v => by
    have h1 := φ0.hg v
    change X.latAt v j L0 = _ at h1
    rw [h, latAt_smul, h1, colSpan_mul, Units.val_mul]
  hg' := φ0.hg'

theorem frmMove_frmBack (X : Sys p) {j : ℕ} {La : X.Lt j} {La' : X.Lt (j + 1)} {L0 : (X.Pj j).Tup}
    (γ : (X.Lv.lev j La.1).Γ) (h : La.2 = (X.Lv.lev j La.1).smul γ L0) (φ0 : Frm X j (La.1, L0) La') :
    frmMove X γ h (frmBack X γ h φ0) = φ0 := by
  cases φ0 with
  | mk g g' hg hg' =>
    unfold frmMove frmBack
    congr 1
    funext v
    exact inv_mul_cancel_left _ _

theorem subst_invF_actS (X : Sys p) (Kc : Type) [Field Kc] [Algebra (Formalism.MainNotions.FormalGroupSystem.K0 p) Kc] [Algebra X.G.Kf Kc] {j : ℕ}
    {La : X.Lt j} {La' : X.Lt (j + 1)} {L0 : (X.Pj j).Tup} (γ : (X.Lv.lev j La.1).Γ)
    (h : La.2 = (X.Lv.lev j La.1).smul γ L0) (φ : Frm X j La La') (z : X.ZA j) :
    MvPowerSeries.subst (invF Kc φ) (actS X Kc j (gamAt X j La.1 γ) z) = invF Kc (frmMove X γ h φ) z := by
  have hI : MvPowerSeries.HasSubst (invF Kc φ) := by apply hasSubst_invF
  rcases z with ⟨v, s, a, b⟩
  have hQ : Qi Kc (frmMove X γ h φ) v s = Qi Kc φ v s := by
    unfold Qi
    rfl
  have hm : ∀ A B : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v),
      mAt X Kc j v s (A * B) = mAt X Kc j v s A * mAt X Kc j v s B := by
    intro A B
    unfold mAt
    rw [Matrix.map_mul, Matrix.submatrix_mul_equiv]
  simp only [actS, invF]
  simp_rw [← MvPowerSeries.smul_eq_C_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← MvPowerSeries.coe_substAlgHom hI, map_sum]
  simp_rw [map_smul, MvPowerSeries.coe_substAlgHom, MvPowerSeries.subst_X hI]
  simp only [invF]
  simp_rw [← MvPowerSeries.smul_eq_C_mul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ab' _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  rcases ab' with ⟨c, d⟩
  simp only [Matrix.kroneckerMap_apply, hQ]
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]
  congr 1
  unfold Pi
  try dsimp only [frmMove]
  by_cases ho : IsOddPos s
  · simp only [if_pos ho]
    rw [Units.val_mul, hm, Matrix.mul_apply]
  · simp only [if_neg ho, Matrix.transpose_apply]
    rw [mul_inv_rev, inv_inv, Units.val_mul, hm, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem thA_SA (X : Sys p) (Kc : Type) [Field Kc] [Algebra (Formalism.MainNotions.FormalGroupSystem.K0 p) Kc] [Algebra X.G.Kf Kc] {j : ℕ}
    {La : X.Lt j} {La' : X.Lt (j + 1)} {L0 : (X.Pj j).Tup} (γ : (X.Lv.lev j La.1).Γ)
    (h : La.2 = (X.Lv.lev j La.1).smul γ L0) (φ : Frm X j La La') (f : MvPowerSeries (X.ZA j) Kc) :
    thA Kc φ (SA X Kc j (gamAt X j La.1 γ) f) = thA Kc (frmMove X γ h φ) f := by
  have hI : MvPowerSeries.HasSubst (invF Kc φ) := by apply hasSubst_invF
  have hA : MvPowerSeries.HasSubst (actS X Kc j (gamAt X j La.1 γ)) := by apply hasSubst_actS
  unfold thA SA
  rw [MvPowerSeries.subst_comp_subst_apply hA hI]
  congr 1
  funext z
  exact subst_invF_actS X Kc γ h φ z

end Formalism.L2.PairingIndexBounds.PowerSeriesNecessity
end
end

noncomputable section

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend

namespace Formalism.L2.PairingIndexBounds.PowerSeriesNecessity

variable {p : ℕ} [Fact p.Prime]

def RepresentativeCondition (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmbC X.G) (hfin : ∀ j c, (X.Lv.lev j c).FinClasses)
    (be : MvPowerSeries (Fin 2) (Formalism.MainNotions.FormalGroupSystem.K0 p)) {T : Type} (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ T)
    (F : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p]) : Prop :=
  letI := wittFractionAlgebraCp p
  letI := algKfC E.toCEmb
  ∀ j < X.mm, ∀ (L0 : X.Lt j), L0 ∈ repOf X.Lv hfin j → ∀ La' : X.Lt (j + 1), (X.Pj (j + 1)).IsLatTup La'.2 →
    ∀ φ : Frm X j L0 La', ExtensionGeneratorCondition p ℂ_[p] (OcC p) be (thA ℂ_[p] φ (thFOf X pos F j L0 La'))

theorem adm_two_pendant_iff_representative (D : Formalism.BasicNotions.D7) (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmbC X.G)
    (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (hst : FinStab X.Lv) {g : Formalism.MainNotions.GL3Theta.G1 p} (hLT : LTIso g) {T : Type}
    (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ T)
    (F : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p]) :
    adm2b D X (pendT X E hfin hst hLT pos F) ↔ RepresentativeCondition X E hfin (beLT hLT) pos F := by
  letI := wittFractionAlgebraCp p
  letI := algKfC E.toCEmb
  rw [adm_two_pendant_iff]
  constructor
  · intro H
    dsimp only [RepresentativeCondition]
    intro j hj R hR La' hLa' φ
    have hlat : (X.Pj j).IsLatTup R.2 := repOf_lat (Lv := X.Lv) hfin j R hR
    have key := H j hj R La' hlat hLa'
    obtain ⟨L1, hL1, hL1'⟩ := delt_spec (X := X) (hfin := hfin) j R.1 R.2 hlat
    set δ := delt X hfin j R.1 R.2 with hδ
    obtain ⟨L2, _, huniq⟩ := repOf_ex (Lv := X.Lv) hfin j R.1 R.2 hlat
    have e1 : R.2 = L2 := huniq R.2 ⟨hR, 1, by rw [lsmul_one]⟩
    have e2 : L1 = L2 := huniq L1 ⟨hL1, δ, hL1'⟩
    have hS : (X.Lv.lev j R.1).smul δ⁻¹ R.2 = R.2 := by
      conv_lhs => rw [hL1']
      rw [lsmul_inv_lsmul, e2, e1]
    have hh : R.2 = (X.Lv.lev j R.1).smul δ ((X.Lv.lev j R.1).smul δ⁻¹ R.2) := by
      rw [lsmul_lsmul_inv]
    have key2 : ∀ ψ : Frm X j (R.1, (X.Lv.lev j R.1).smul δ⁻¹ R.2) La', ExtensionGeneratorCondition p ℂ_[p] (OcC p) (beLT hLT)
        (thA ℂ_[p] ψ (thFOf X pos F j (R.1, (X.Lv.lev j R.1).smul δ⁻¹ R.2) La')) := by
      intro ψ
      have h := key (frmBack X δ hh ψ)
      rw [thA_SA X ℂ_[p] δ hh] at h
      have hr : frmMove X δ hh (frmBack X δ hh ψ) = ψ := by
        cases ψ
        simp only [frmMove, frmBack, inv_mul_cancel_left]
      rw [hr] at h
      exact h
    rw [hS] at key2
    exact key2 φ
  · intro H j hj La La' hLa hLa' φ
    dsimp only [RepresentativeCondition] at H
    obtain ⟨L1, hL1, hL1'⟩ := delt_spec (X := X) (hfin := hfin) j La.1 La.2 hLa
    set δ := delt X hfin j La.1 La.2 with hδ
    have hS : (X.Lv.lev j La.1).smul δ⁻¹ La.2 = L1 := by
      conv_lhs => rw [hL1']
      rw [lsmul_inv_lsmul]
    have hh : La.2 = (X.Lv.lev j La.1).smul δ ((X.Lv.lev j La.1).smul δ⁻¹ La.2) := by
      rw [lsmul_lsmul_inv]
    rw [thA_SA X ℂ_[p] δ hh φ]
    have hrep : (La.1, (X.Lv.lev j La.1).smul δ⁻¹ La.2) ∈ repOf X.Lv hfin j := by
      rw [hS]
      exact hL1
    exact H j hj _ hrep La' hLa' (frmMove X δ hh φ)

end Formalism.L2.PairingIndexBounds.PowerSeriesNecessity
end
end

section -- merged from Formalism.LocalToGlobal.InertKernelTheory.StatementInt
noncomputable section

namespace Formalism.L2.KerInert

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

def IntFirst (D : D7) (T : Tor D) (e : FamE D) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (N N' : ℕ)
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) : Prop :=
  ∀ F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p], IsComb D T e lam L L' F →
    ∀ (C : WeierstrassCurve.VariableChange ℂ_[p]) (wq : PowerSeries ℂ_[p]) (r : ℕ)
      (b : Fin r → Matrix (Fin N') (Fin N) D.host.E),
      IsModel lam T.abelian₂ C → IsWq (C • wModel lam T.abelian₂) wq → LocBasis D p (YYl D L L') b →
      Orthonormal D b →
      IntegralMv (atLog D lam T.abelian₂ C wq b F * ePh lam T.abelian₂ C wq r)

def IntInert : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ χ : IdE D → ℂ, IsChi D χ →
    ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → jacobiSym (-(D.host.d : ℤ)) p = -1 →
    ∀ (lam : Qbar →+* ℂ_[p]) (N N' : ℕ)
      (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)),
      admitted D N N' L L' → IntFirst D B.tor (B.eNat χ) p lam N N' L L'

end Formalism.L2.KerInert
end
end

section -- merged from Formalism.LocalToGlobal.InertKernelTheory.DefsInt
noncomputable section

namespace Formalism.L2.KerInert

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

def IntS (D : D7) (T : Tor D) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {N N' : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) : Prop :=
  ∀ (C : WeierstrassCurve.VariableChange ℂ_[p]) (wq : PowerSeries ℂ_[p]) (r : ℕ)
      (b : Fin r → Matrix (Fin N') (Fin N) D.host.E),
      IsModel lam T.abelian₂ C → IsWq (C • wModel lam T.abelian₂) wq → LocBasis D p (YYl D L L') b →
      Orthonormal D b →
      IntegralMv (atLog D lam T.abelian₂ C wq b F * ePh lam T.abelian₂ C wq r)

def IntSome (D : D7) (T : Tor D) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {N N' : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) : Prop :=
  ∃ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), LocBasis D p (YYl D L L') b ∧ Orthonormal D b ∧
    ∀ (C : WeierstrassCurve.VariableChange ℂ_[p]) (wq : PowerSeries ℂ_[p]),
      IsModel lam T.abelian₂ C → IsWq (C • wModel lam T.abelian₂) wq →
      IntegralMv (atLog D lam T.abelian₂ C wq b F * ePh lam T.abelian₂ C wq r)

def AlgEnt (D : D7) {N N' : ℕ} (G : VC D N N' → ℂ) : Prop :=
  AnalyticOnNhd ℂ G Set.univ ∧ ∀ α : Mono D N N', taylor D G α ∈ Qbar

def tPull (D : D7) (T : Tor D) {N N' : ℕ} (γ : Matrix (Fin N) (Fin N) D.host.E)
    (γ' : Matrix (Fin N') (Fin N') D.host.E) (z : VC D N N') : VC D N N' :=
  fun τ => (Matrix.conjTranspose (γ'.map (T.emb τ)) * (Matrix.of (z τ)) * γ.map (T.emb τ) : Matrix _ _ ℂ)

def CombFact : Prop :=
  ∀ (D : D7) (T : Tor D) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (N N' : ℕ)
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (m : ℕ) (r : Fin m → ℂ_[p]) (F : Fin m → MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]),
    (∀ k, IsIntP (r k)) → (∀ k, IntS D T p lam L L' (F k)) →
    IntS D T p lam L L' (∑ k, algebraMap ℂ_[p] (MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) (r k) * F k)

def PairFact : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (p : ℕ) [Fact p.Prime] (N N' : ℕ)
    (L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)),
    EqAt D p L L₁ → EqAt D p L' L₁' →
      (∀ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E),
        LocBasis D p (YYl D L L') b → LocBasis D p (YYl D L₁ L₁') b) ∧
      (∀ t : VC D N N', TorsPrime D p (La D (tor0 D cc δ) L L') t → TorsPrime D p (La D (tor0 D cc δ) L₁ L₁') t)

def WeakApprox : Prop :=
  ∀ (D : D7) (p : ℕ) [Fact p.Prime], 5 ≤ p → jacobiSym (-(D.host.d : ℤ)) p = -1 →
    ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)),
    admitted D N N' L L' →
    letI := D.host.cmStar
    ∃ (γ : Matrix.unitaryGroup (Fin N) D.host.E) (γ' : Matrix.unitaryGroup (Fin N') D.host.E)
      (M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (M' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)),
      admitted D N N' M M' ∧ EqAt D p (Formalism.MainNotions.StandardLatticesGL3.stdL D N) M ∧ EqAt D p (Formalism.MainNotions.StandardLatticesGL3.stdL D N') M' ∧
      L = SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) M ∧
      L' = SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) M'

def PullTors : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (p : ℕ) [Fact p.Prime] (N N' : ℕ),
    letI := D.host.cmStar
    ∀ (γ : Matrix.unitaryGroup (Fin N) D.host.E) (γ' : Matrix.unitaryGroup (Fin N') D.host.E)
      (M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (M' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
      (t : VC D N N'),
      TorsPrime D p (La D (tor0 D cc δ) (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) M)
        (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) M')) t →
      TorsPrime D p (La D (tor0 D cc δ) M M')
        (tPull D (tor0 D cc δ) (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) t)

def PullFact : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (N N' : ℕ),
    letI := D.host.cmStar
    ∀ (γ : Matrix.unitaryGroup (Fin N) D.host.E) (γ' : Matrix.unitaryGroup (Fin N') D.host.E)
      (M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (M' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
      (t : VC D N N') (G : VC D N N' → ℂ),
      AlgEnt D (U D (tor0 D cc δ) (tPull D (tor0 D cc δ) (γ : Matrix (Fin N) (Fin N) D.host.E)
        (γ' : Matrix (Fin N') (Fin N') D.host.E) t) G) →
      IntS D (tor0 D cc δ) p lam M M' (pSer D lam (U D (tor0 D cc δ) (tPull D (tor0 D cc δ)
        (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) t) G)) →
      IntS D (tor0 D cc δ) p lam (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) M)
        (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) M')
        (pSer D lam (U D (tor0 D cc δ) t (pull D (tor0 D cc δ) (γ : Matrix (Fin N) (Fin N) D.host.E)
          (γ' : Matrix (Fin N') (Fin N') D.host.E) G)))

def AlgFact : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ χ : IdE D → ℂ, IsChi D χ →
    ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → jacobiSym (-(D.host.d : ℤ)) p = -1 → ∀ N N' : ℕ,
      (∀ (M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (M' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)),
        admitted D N N' M M' → EqAt D p (Formalism.MainNotions.StandardLatticesGL3.stdL D N) M → EqAt D p (Formalism.MainNotions.StandardLatticesGL3.stdL D N') M' →
        ∀ t : VC D N N', TorsPrime D p (La D B.tor M M') t → AlgEnt D (U D B.tor t (B.eNat χ N N' M M'))) ∧
      (∀ s : VC D N N', TorsPrime D p (La D B.tor (Formalism.MainNotions.StandardLatticesGL3.stdL D N) (Formalism.MainNotions.StandardLatticesGL3.stdL D N')) s →
        AlgEnt D (U D B.tor s (B.thZero N N')))

def PSerLin : Prop :=
  ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (N N' m : ℕ) (c : Fin m → ℂ) (G : Fin m → VC D N N' → ℂ),
    (∀ k, c k ∈ Qbar) → (∀ k, AlgEnt D (G k)) →
    pSer D lam (fun z => ∑ k, c k * G k z) =
      ∑ k, algebraMap ℂ_[p] (MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) (lamC lam (c k)) * pSer D lam (G k)

def StdStep : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ χ : IdE D → ℂ, IsChi D χ →
    ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → jacobiSym (-(D.host.d : ℤ)) p = -1 →
    ∀ (lam : Qbar →+* ℂ_[p]) (N N' : ℕ)
      (M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (M' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)),
      admitted D N N' M M' → EqAt D p (Formalism.MainNotions.StandardLatticesGL3.stdL D N) M → EqAt D p (Formalism.MainNotions.StandardLatticesGL3.stdL D N') M' →
      ∀ t : VC D N N', TorsPrime D p (La D B.tor M M') t →
      ∃ (m : ℕ) (c : Fin m → ℂ) (s : Fin m → VC D N N'),
        (∀ k, c k ∈ Qbar ∧ IsIntP (lamC lam (c k))) ∧
        (∀ k, TorsPrime D p (La D B.tor (Formalism.MainNotions.StandardLatticesGL3.stdL D N) (Formalism.MainNotions.StandardLatticesGL3.stdL D N')) (s k)) ∧
        U D B.tor t (B.eNat χ N N' M M') = fun z => ∑ k, c k * U D B.tor (s k) (B.thZero N N') z

def BasisInv : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → jacobiSym (-(D.host.d : ℤ)) p = -1 →
    ∀ (lam : Qbar →+* ℂ_[p]) (N N' : ℕ)
      (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
      (F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]),
      IntSome D (tor0 D cc δ) p lam L L' F → IntS D (tor0 D cc δ) p lam L L' F

def TensFact : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → jacobiSym (-(D.host.d : ℤ)) p = -1 → ∀ lam : Qbar →+* ℂ_[p],
    (∀ s : VC D 2 2, TorsPrime D p (La D B.tor (Formalism.MainNotions.StandardLatticesGL3.stdL D 2) (Formalism.MainNotions.StandardLatticesGL3.stdL D 2)) s →
      AlgEnt D (U D B.tor s (B.thZero 2 2)) ∧
      IntSome D B.tor p lam (Formalism.MainNotions.StandardLatticesGL3.stdL D 2) (Formalism.MainNotions.StandardLatticesGL3.stdL D 2) (pSer D lam (U D B.tor s (B.thZero 2 2))) ∧
      IntS D B.tor p lam (Formalism.MainNotions.StandardLatticesGL3.stdL D 2) (Formalism.MainNotions.StandardLatticesGL3.stdL D 2) (pSer D lam (U D B.tor s (B.thZero 2 2)))) →
    ∀ (N N' : ℕ), Even N → Even N' →
    ∀ s : VC D N N', TorsPrime D p (La D B.tor (Formalism.MainNotions.StandardLatticesGL3.stdL D N) (Formalism.MainNotions.StandardLatticesGL3.stdL D N')) s →
      IntSome D B.tor p lam (Formalism.MainNotions.StandardLatticesGL3.stdL D N) (Formalism.MainNotions.StandardLatticesGL3.stdL D N') (pSer D lam (U D B.tor s (B.thZero N N')))

def ThFourInt : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → jacobiSym (-(D.host.d : ℤ)) p = -1 → ∀ lam : Qbar →+* ℂ_[p],
    ∀ s : VC D 2 2, TorsPrime D p (La D B.tor (Formalism.MainNotions.StandardLatticesGL3.stdL D 2) (Formalism.MainNotions.StandardLatticesGL3.stdL D 2)) s →
      IntSome D B.tor p lam (Formalism.MainNotions.StandardLatticesGL3.stdL D 2) (Formalism.MainNotions.StandardLatticesGL3.stdL D 2) (pSer D lam (U D B.tor s (B.thZero 2 2)))

end Formalism.L2.KerInert
end
end

section -- merged from Formalism.LocalToGlobal.InertKernelTheory.StatementJets
noncomputable section

namespace Formalism.L2.KerInert

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

def OrthBasisExists : Prop :=
  ∀ (D : D7) (p : ℕ) [Fact p.Prime], 5 ≤ p → jacobiSym (-(D.host.d : ℤ)) p = -1 →
    ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)),
      admitted D N N' L L' →
      ∃ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), LocBasis D p (YYl D L L') b ∧ Orthonormal D b

end Formalism.L2.KerInert
end
end

section -- merged from Formalism.LocalToGlobal.InertKernelTheory.DefsRep
noncomputable section

namespace Formalism.L2.KerInert.Rep

open Formalism.MainNotions.FormalGroupSystem Formalism.L2.Th1.D Formalism.L2.Th1.Top Formalism.L2.KerInert.K1
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (cob UnrOK IsLawOfLog)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.G.Pend (k0ToC wittFractionAlgebraCp OcC Frm thA thFOf)
open Formalism.MainNotions.FormalGroupSystem (Sys)

def CurveAt (l : ℕ) [Fact l.Prime] (be : MvPowerSeries (Fin 2) (K0 l)) (g2 g3 ε s2 : MaximalUnramifiedExtension l) : Prop :=
  ‖g2‖ ≤ 1 ∧ ‖g3‖ ≤ 1 ∧ ‖ε‖ = 1 ∧ (∀ n, ‖PowerSeries.coeff n (thetaS l g2 g3 ε)‖ ≤ 1) ∧
    (∀ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, UnrOK (MaximalUnramifiedExtension l) l σ →
      ∀ α : MaximalUnramifiedExtension l, ‖α‖ = 1 → σ (σ α) = α → NormRel l σ (phFF l g2 g3 s2 ε) α) ∧
    MvPowerSeries.constantCoeff be = 0 ∧
    ∃ F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l), IsLawOfLog l F ∧
      Formalism.InvariantFactorPaths.G7.Simeq (MvPowerSeries.map (k0ToC l) (inParam l be))
        (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype (cob F (phFF l g2 g3 s2 ε)))

def OrthInt (l : ℕ) [Fact l.Prime] (g2 g3 s2 ε : MaximalUnramifiedExtension l) {ι : Type} [Fintype ι] [DecidableEq ι]
    (Th : MvPowerSeries (ι ⊕ ι) ℂ_[l]) : Prop :=
  ∃ (r : ℕ) (Θ : MvPowerSeries (Fin r) ℂ_[l]) (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (f f' : ι → Fin r → MaximalUnramifiedExtension l),
    UnrOK (MaximalUnramifiedExtension l) l σ ∧ IsHypPair σ f f' ∧ Th = MvPowerSeries.subst (hypLin l f f') Θ ∧
    Integral (mvExp (Formalism.L2.Th1.E.phSum (phL l g2 g3 s2 ε) : MvPowerSeries (Fin r) ℂ_[l]) *
      @inParamK l _ (Fin r) ℂ_[l] _ (wittFractionAlgebraCp l) Θ)

section Glob

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

def thOrth (D : D7) {N N' r : ℕ} {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (c : ℂ_[p])
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (F₀ : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) :
    MvPowerSeries (Fin r) ℂ_[p] :=
  MvPowerSeries.subst (fun k : D.what₂.Tau × Fin N' × Fin N =>
    ∑ i, MvPowerSeries.C (c * lamC lam (embT D k.1 (b i k.2.1 k.2.2))) * MvPowerSeries.X i) F₀

variable {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : Formalism.L2.G.Pend.CEmbC X.G)
    (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)
    (large₂ : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E))
    (Lg' : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))
    (F : ∀ j, X.Lt j → X.Lt (j + 1) →
      MvPowerSeries (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p])

end Glob

def DictInt (D : Formalism.BasicNotions.D7) {p : ℕ} [Fact p.Prime] (lam : Formalism.MainNotions.TaylorLogMetric.Qbar →+* ℂ_[p]) (Λ : AddSubgroup ℂ) (c : ℂ_[p])
    (g2 g3 s2 ε : MaximalUnramifiedExtension p) : Prop :=
  ∃ (C : WeierstrassCurve.VariableChange ℂ_[p]) (wq : PowerSeries ℂ_[p]),
    Formalism.MainNotions.TaylorLogMetric.IsModel lam Λ C ∧ Formalism.MainNotions.TaylorLogMetric.IsWq (C • Formalism.MainNotions.TaylorLogMetric.wModel lam Λ) wq ∧
    ∀ (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)
      (G : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]),
      Formalism.MainNotions.TaylorLogMetric.IntegralMv (Formalism.MainNotions.TaylorLogMetric.atLog D lam Λ C wq b G * Formalism.MainNotions.TaylorLogMetric.ePh lam Λ C wq r) →
      Integral (mvExp (Formalism.L2.Th1.E.phSum (phL p g2 g3 s2 ε) : MvPowerSeries (Fin r) ℂ_[p]) *
        @inParamK p _ (Fin r) ℂ_[p] _ (wittFractionAlgebraCp p) (thOrth D lam c b G))

end Formalism.L2.KerInert.Rep
end
end

section -- merged from Formalism.LocalToGlobal.InertKernelTheory.StatementLoc
section -- merged from Formalism.LocalToGlobal.PairingIndexBounds.PendingAdmissibility.LocalFDerivAdmissibility.AdmRed
noncomputable section

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend

namespace Formalism.L2.PairingIndexBounds.PowerSeriesNecessity

variable {p : ℕ} [Fact p.Prime]

theorem resV_C_mul {ι κ R : Type} [CommSemiring R] (f : κ → ι) (c : R) (Th : MvPowerSeries ι R) :
    resV f (MvPowerSeries.C c * Th) = MvPowerSeries.C c * resV f Th := by
  ext n
  show MvPowerSeries.coeff (Finsupp.mapDomain f n) (MvPowerSeries.C c * Th) =
    MvPowerSeries.coeff n (MvPowerSeries.C c * resV f Th)
  rw [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_C_mul]
  all_goals rfl

def LocalRepresentativeCondition (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmbC X.G) (hfin : ∀ j c, (X.Lv.lev j c).FinClasses)
    (be : MvPowerSeries (Fin 2) (Formalism.MainNotions.FormalGroupSystem.K0 p)) {T : Type} (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ T)
    (F : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p]) : Prop :=
  letI := wittFractionAlgebraCp p
  letI := algKfC E.toCEmb
  ∀ (v : X.Pl), ∀ j < X.mm, ∀ (L0 : X.Lt j), L0 ∈ repOf X.Lv hfin j → ∀ La' : X.Lt (j + 1), (X.Pj (j + 1)).IsLatTup La'.2 →
    ∀ φ : Frm X j L0 La', ExtensionLocalCondition p ℂ_[p] (OcC p) be
      (resV (Sum.map (fun e => (⟨v, e⟩ : X.EA j)) (fun e => (⟨v, e⟩ : X.EA j))) (thA ℂ_[p] φ (thFOf X pos F j L0 La')))

theorem adm_two_iff_local_representative (D : Formalism.BasicNotions.D7) (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmbC X.G)
    (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (hst : FinStab X.Lv) {g : Formalism.MainNotions.GL3Theta.G1 p} (hLT : LTIso g) {T : Type}
    (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ T)
    (F : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p]) :
    adm2 D X (pendT X E hfin hst hLT pos F) ↔ LocalRepresentativeCondition X E hfin (beLT hLT) pos F := by
  let _ := wittFractionAlgebraCp p
  let _ := algKfC E.toCEmb
  have key : ∀ v j (La : X.Lt j) (La' : X.Lt (j + 1)) (φ : Frm X j La La'),
      (pendT X E hfin hst hLT pos F).ThV v j La La' φ = MvPowerSeries.C (chiN X ℂ_[p] hfin j La) *
        resV (Sum.map (fun e => (⟨v, e⟩ : X.EA j)) (fun e => (⟨v, e⟩ : X.EA j)))
          (thA ℂ_[p] (frmMove X (delt X hfin j La.1 La.2) (lsmul_lsmul_inv _ _ _).symm φ)
            (thFOf X pos F j (La.1, (X.Lv.lev j La.1).smul (delt X hfin j La.1 La.2)⁻¹ La.2) La')) := by
    intro v j La La' φ
    rw [← thA_SA X ℂ_[p] (delt X hfin j La.1 La.2) (lsmul_lsmul_inv _ _ _).symm φ, ← resV_C_mul]
    show resV _ ((pendT X E hfin hst hLT pos F).ThA j La La' φ) = _
    congr 1
    exact subst_C_mul' (hasSubst_invF ℂ_[p] φ) _ _
  have hn : ∀ j (La : X.Lt j), ‖chiN X ℂ_[p] hfin j La‖ = 1 := fun j La => norm_chiN X E.toCEmb hfin j La
  have hu : ∀ j (La : X.Lt j), chiN X ℂ_[p] hfin j La ∈ OcC p ∧ (chiN X ℂ_[p] hfin j La)⁻¹ ∈ OcC p ∧
      chiN X ℂ_[p] hfin j La ≠ 0 := fun j La =>
    ⟨show ‖_‖ ≤ 1 by rw [hn], show ‖_‖ ≤ 1 by rw [norm_inv, hn, inv_one],
      fun h0 => by have := hn j La; rw [h0, norm_zero] at this; exact zero_ne_one this⟩
  constructor
  · rintro H v j hj ⟨c, L1⟩ h0 La' hL' φ0
    have hL0 : (X.Pj j).IsLatTup L1 := repOf_lat X.Lv hfin j (c, L1) h0
    have hh : L1 = (X.Lv.lev j c).smul (delt X hfin j c L1) ((X.Lv.lev j c).smul (delt X hfin j c L1)⁻¹ L1) :=
      (lsmul_lsmul_inv _ _ _).symm
    have A : ∀ φ' : Frm X j (c, (X.Lv.lev j c).smul (delt X hfin j c L1)⁻¹ L1) La',
        ExtensionLocalCondition p ℂ_[p] (OcC p) (beLT hLT) (resV (Sum.map (fun e => (⟨v, e⟩ : X.EA j)) (fun e => (⟨v, e⟩ : X.EA j)))
          (thA ℂ_[p] φ' (thFOf X pos F j (c, (X.Lv.lev j c).smul (delt X hfin j c L1)⁻¹ L1) La'))) := by
      intro φ'
      have H1 := H v j hj (c, L1) La' hL0 hL' (frmBack X (La := (c, L1)) (delt X hfin j c L1) hh φ')
      change ExtensionLocalCondition p ℂ_[p] (OcC p) (beLT hLT) ((pendT X E hfin hst hLT pos F).ThV v j (c, L1) La' _) at H1
      rw [key, frmMove_frmBack] at H1
      obtain ⟨hc, hc', hc0⟩ := hu j (c, L1)
      exact (K1gen_C_mul_iff (ι := Eidx _ _ _) hc hc' hc0).1 H1
    obtain ⟨L2, h2, e2⟩ := delt_spec X hfin j c L1 hL0
    have h21 : L2 = L1 := (repOf_ex X.Lv hfin j c L1 hL0).unique ⟨h2, _, e2⟩ ⟨h0, 1, (lsmul_one _ L1).symm⟩
    have e3 : (X.Lv.lev j c).smul (delt X hfin j c L1)⁻¹ L1 = L1 := by
      generalize delt X hfin j c L1 = d at e2 ⊢
      conv_lhs => rw [e2]
      rw [lsmul_inv_lsmul, h21]
    have B : ∀ L3 (_ : (X.Lv.lev j c).smul (delt X hfin j c L1)⁻¹ L1 = L3) (φ' : Frm X j (c, L3) La'),
        ExtensionLocalCondition p ℂ_[p] (OcC p) (beLT hLT) (resV (Sum.map (fun e => (⟨v, e⟩ : X.EA j)) (fun e => (⟨v, e⟩ : X.EA j)))
          (thA ℂ_[p] φ' (thFOf X pos F j (c, L3) La'))) := by
      intro L3 e
      subst e
      exact A
    exact B L1 e3 φ0
  · intro H v j hj La La' hL hL' φ
    change ExtensionLocalCondition p ℂ_[p] (OcC p) (beLT hLT) ((pendT X E hfin hst hLT pos F).ThV v j La La' φ)
    rw [key]
    obtain ⟨hc, -, -⟩ := hu j La
    refine K1gen_C_mul (ι := Eidx _ _ _) hc ?_
    obtain ⟨L1, h1, e1⟩ := delt_spec X hfin j La.1 La.2 hL
    have e2 : (X.Lv.lev j La.1).smul (delt X hfin j La.1 La.2)⁻¹ La.2 = L1 := by
      generalize delt X hfin j La.1 La.2 = d at e1 ⊢
      rw [e1, lsmul_inv_lsmul]
    generalize frmMove X (delt X hfin j La.1 La.2) (lsmul_lsmul_inv _ _ _).symm φ = φ0
    revert φ0
    rw [e2]
    intro φ0
    exact H v j hj (La.1, L1) h1 La' hL' φ0

theorem hasSubst_coordZA' (X : Sys p) (Kc : Type) [Field Kc] [Algebra (Formalism.MainNotions.FormalGroupSystem.K0 p) Kc] (j : ℕ) :
    MvPowerSeries.HasSubst (X.coordZA Kc j) := by
  refine MvPowerSeries.hasSubst_of_constantCoeff_zero fun e => ?_
  rcases e with ⟨v, r, a, b⟩ | ⟨v, r, a, b⟩ <;> simp [Formalism.MainNotions.FormalGroupSystem.Sys.coordZA]

theorem applyD_C_mul {σ τ Kc : Type} [Field Kc] (P : MvPolynomial σ (MvPolynomial τ ℤ)) (c : Kc)
    (f : MvPowerSeries σ Kc) : applyD P (MvPowerSeries.C c * f) = c • applyD P f := by
  rw [applyD, applyD, Finset.smul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [MvPowerSeries.coeff_C_mul, smul_smul]
  congr 1
  ring

def GeZ (x : ℂ_[p]) : Prop :=
  ∀ (a : ℤ) (b : ℕ), 0 < b → (a : ℝ) ≤ 0 * b → x ^ b * (p : ℂ_[p]) ^ (-a) ∈ OcC p

theorem geZ_mul_iff {c x : ℂ_[p]} (hc : ‖c‖ = 1) : GeZ (c * x) ↔ GeZ x := by
  have key : ∀ (a : ℤ) (b : ℕ), (c * x) ^ b * (p : ℂ_[p]) ^ (-a) ∈ OcC p ↔
      x ^ b * (p : ℂ_[p]) ^ (-a) ∈ OcC p := by
    intro a b
    have e : ‖(c * x) ^ b * (p : ℂ_[p]) ^ (-a)‖ = ‖x ^ b * (p : ℂ_[p]) ^ (-a)‖ := by
      rw [mul_pow, mul_assoc, norm_mul, norm_pow, hc, one_pow, one_mul]
    change ‖(c * x) ^ b * (p : ℂ_[p]) ^ (-a)‖ ≤ 1 ↔ ‖x ^ b * (p : ℂ_[p]) ^ (-a)‖ ≤ 1
    rw [e]
  unfold GeZ
  simp only [key]

def Adm3Rep (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmbC X.G) (hfin : ∀ j c, (X.Lv.lev j c).FinClasses)
    {T : Type} (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ T)
    (F : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p]) : Prop :=
  letI := wittFractionAlgebraCp p
  letI := algKfC E.toCEmb
  ∀ j < X.mm, ∀ (L0 : X.Lt j), L0 ∈ repOf X.Lv hfin j → ∀ La' : X.Lt (j + 1), (X.Pj (j + 1)).IsLatTup La'.2 →
    ∀ (φ : Frm X j L0 La') (I : X.ColCh j) (n : X.FrI j →₀ ℕ),
      GeZ (AddMonoidAlgebra.coeff (applyD (X.PI j I fun _ => 0) (X.ThZA ℂ_[p] j (thA ℂ_[p] φ (thFOf X pos F j L0 La')))) n)

theorem adm_three_iff_representative (D : Formalism.BasicNotions.D7) (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmbC X.G)
    (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (hst : FinStab X.Lv) {g : Formalism.MainNotions.GL3Theta.G1 p} (hLT : LTIso g) {T : Type}
    (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ T)
    (F : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p]) :
    adm3 D X (pendT X E hfin hst hLT pos F) ↔ Adm3Rep X E hfin pos F := by
  let _ := wittFractionAlgebraCp p
  let _ := algKfC E.toCEmb
  have key : ∀ j (La : X.Lt j) (La' : X.Lt (j + 1)) (φ : Frm X j La La') (I : X.ColCh j) (n : X.FrI j →₀ ℕ),
      AddMonoidAlgebra.coeff (applyD (X.PI j I fun _ => 0) (X.ThZA ℂ_[p] j ((pendT X E hfin hst hLT pos F).ThA j La La' φ))) n =
        chiN X ℂ_[p] hfin j La • AddMonoidAlgebra.coeff (applyD (X.PI j I fun _ => 0) (X.ThZA ℂ_[p] j
          (thA ℂ_[p] (frmMove X (delt X hfin j La.1 La.2) (lsmul_lsmul_inv _ _ _).symm φ)
            (thFOf X pos F j (La.1, (X.Lv.lev j La.1).smul (delt X hfin j La.1 La.2)⁻¹ La.2) La')))) n := by
    intro j La La' φ I n
    rw [← thA_SA X ℂ_[p] (delt X hfin j La.1 La.2) (lsmul_lsmul_inv _ _ _).symm φ, ← MvPolynomial.coeff_smul,
      ← applyD_C_mul, Sys.ThZA, Sys.ThZA, ← subst_C_mul' (hasSubst_coordZA' X ℂ_[p] j)]
    congr 3
    congr 1
    exact subst_C_mul' (hasSubst_invF ℂ_[p] φ) _ _
  have hn : ∀ j (La : X.Lt j), ‖chiN X ℂ_[p] hfin j La‖ = 1 := fun j La => norm_chiN X E.toCEmb hfin j La
  constructor
  · rintro H j hj ⟨c, L1⟩ h0 La' hL' φ0 I n
    have hL0 : (X.Pj j).IsLatTup L1 := repOf_lat X.Lv hfin j (c, L1) h0
    have hh : L1 = (X.Lv.lev j c).smul (delt X hfin j c L1) ((X.Lv.lev j c).smul (delt X hfin j c L1)⁻¹ L1) :=
      (lsmul_lsmul_inv _ _ _).symm
    have A : ∀ φ' : Frm X j (c, (X.Lv.lev j c).smul (delt X hfin j c L1)⁻¹ L1) La',
        GeZ (AddMonoidAlgebra.coeff (applyD (X.PI j I fun _ => 0) (X.ThZA ℂ_[p] j
          (thA ℂ_[p] φ' (thFOf X pos F j (c, (X.Lv.lev j c).smul (delt X hfin j c L1)⁻¹ L1) La')))) n) := by
      intro φ'
      have H1 := H j hj (c, L1) La' hL0 hL' (frmBack X (La := (c, L1)) (delt X hfin j c L1) hh φ') I n
      change GeZ _ at H1
      rw [key, frmMove_frmBack, smul_eq_mul, geZ_mul_iff (hn j (c, L1))] at H1
      exact H1
    obtain ⟨L2, h2, e2⟩ := delt_spec X hfin j c L1 hL0
    have h21 : L2 = L1 := (repOf_ex X.Lv hfin j c L1 hL0).unique ⟨h2, _, e2⟩ ⟨h0, 1, (lsmul_one _ L1).symm⟩
    have e3 : (X.Lv.lev j c).smul (delt X hfin j c L1)⁻¹ L1 = L1 := by
      generalize delt X hfin j c L1 = d at e2 ⊢
      conv_lhs => rw [e2]
      rw [lsmul_inv_lsmul, h21]
    have B : ∀ L3 (_ : (X.Lv.lev j c).smul (delt X hfin j c L1)⁻¹ L1 = L3) (φ' : Frm X j (c, L3) La'),
        GeZ (AddMonoidAlgebra.coeff (applyD (X.PI j I fun _ => 0) (X.ThZA ℂ_[p] j
          (thA ℂ_[p] φ' (thFOf X pos F j (c, L3) La')))) n) := by
      intro L3 e
      subst e
      exact A
    exact B L1 e3 φ0
  · intro H j hj La La' hL hL' φ I n
    change GeZ _
    rw [key, smul_eq_mul, geZ_mul_iff (hn j La)]
    obtain ⟨L1, h1, e1⟩ := delt_spec X hfin j La.1 La.2 hL
    have e2 : (X.Lv.lev j La.1).smul (delt X hfin j La.1 La.2)⁻¹ La.2 = L1 := by
      generalize delt X hfin j La.1 La.2 = d at e1 ⊢
      rw [e1, lsmul_inv_lsmul]
    generalize frmMove X (delt X hfin j La.1 La.2) (lsmul_lsmul_inv _ _ _).symm φ = φ0
    revert φ0
    rw [e2]
    intro φ0
    exact H j hj (La.1, L1) h1 La' hL' φ0 I n

end Formalism.L2.PairingIndexBounds.PowerSeriesNecessity
end
end

noncomputable section

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.PowerSeriesNecessity

namespace Formalism.L2.KerInert

def LowZC {p : ℕ} [Fact p.Prime] (X : Sys p) (be : MvPowerSeries (Fin 2) (Formalism.MainNotions.FormalGroupSystem.K0 p)) (j : ℕ) (v : X.Pl) : Prop :=
  letI := wittFractionAlgebraCp p
  ∀ U : MvPowerSeries (X.EA j ⊕ X.EA j) ℂ_[p], IntR (OcC p) (inParamK p ℂ_[p] U) →
    ∀ (I : X.ColCh j) (n : X.FrI j →₀ ℕ),
      GeZ (AddMonoidAlgebra.coeff (applyD (X.PIv j I v)
        (X.ThZA ℂ_[p] j (MvPowerSeries.map (algebraMap (Formalism.MainNotions.FormalGroupSystem.K0 p) ℂ_[p])
          (expS p (-(∑ e : Eidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)),
            sub2 p be (MvPowerSeries.X (Sum.inl (⟨v, e⟩ : X.EA j))) (MvPowerSeries.X (Sum.inr (⟨v, e⟩ : X.EA j)))))) * U))) n)

def FirstKernelLocalOfGeneral : Prop :=
  ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmbC X.G)
    (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (be : MvPowerSeries (Fin 2) (Formalism.MainNotions.FormalGroupSystem.K0 p)) {T : Type}
    (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ T)
    (F : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p]),
    RepresentativeCondition X E hfin be pos F → LocalRepresentativeCondition X E hfin be pos F

def Adm3OfK1LowerBound : Prop :=
  ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmbC X.G)
    (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (be : MvPowerSeries (Fin 2) (Formalism.MainNotions.FormalGroupSystem.K0 p)) {T : Type}
    (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ T)
    (F : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p]),
    (∀ j < X.mm, ∀ v, LowZC X be j v) → RepresentativeCondition X E hfin be pos F → Adm3Rep X E hfin pos F

end Formalism.L2.KerInert
end
end
