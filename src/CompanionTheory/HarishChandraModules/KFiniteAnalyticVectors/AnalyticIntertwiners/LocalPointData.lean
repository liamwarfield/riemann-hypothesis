module

public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.LogNormEstimates
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.HarishChandraThirdIndefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HarishChandraModulesIndefiniteUnitaryGroup

@[expose] public section

open Matrix WithLp
open scoped InnerProductSpace

noncomputable section

namespace CompanionTheory.D.gk.HC

open ReciprocityTheory.ChartRestriction.DS
open Formalism.BasicNotions.TH (GrpData URep GKMod Mat upq IsKC Eab wtSub hwSub posC KFin sameBlock)
open Formalism.MainNotions.SchurIrreducible (IsHCMod IrrU)

section Graph

open USum

variable {n : ℕ} {ε : Fin n → Bool} {H₁ H₂ : Type} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
  {σ₁ : Matrix (Fin n) (Fin n) ℂ → (H₁ →L[ℂ] H₁)} {σ₂ : Matrix (Fin n) (Fin n) ℂ → (H₂ →L[ℂ] H₂)}
  {D₁ : Submodule ℂ H₁} {D₂ : Submodule ℂ H₂}
  {E₁ : Fin n → Fin n → Module.End ℂ D₁} {E₂ : Fin n → Fin n → Module.End ℂ D₂}

theorem graphD [CompleteSpace H₁] [CompleteSpace H₂] (h₁ : IsURepOn (UJset ε) σ₁) (h₂ : IsURepOn (UJset ε) σ₂)
    (hD₁ : IsDerivedOn ε σ₁ D₁ E₁) (hD₂ : IsDerivedOn ε σ₂ D₂ E₂) {N : Type} [AddCommGroup N] [Module ℂ N]
    (F : Fin n → Fin n → Module.End ℂ N) (κ₁ : N →ₗ[ℂ] D₁) (κ₂ : N →ₗ[ℂ] D₂) (hi : Function.Injective κ₁)
    (e₁ : ∀ a b w, E₁ a b (κ₁ w) = κ₁ (F a b w)) (e₂ : ∀ a b w, E₂ a b (κ₂ w) = κ₂ (F a b w))
    {c : ℝ} (hc : ∀ v, casimir E₁ v = (c : ℂ) • v) (U : H₁ →L[ℂ] H₂) (hU : ∀ w, U (κ₁ w) = κ₂ w)
    {W : Submodule ℂ N} (hW : FiniteDimensional ℂ W) (hWK : IsKStableSub ε F W) {w : N} (hw : w ∈ W)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) : U (σ₁ g (κ₁ w)) = σ₂ g (κ₂ w) := _root_.GlobalTheory.HcPort.graphD (N := N) (c := c) (W := W) (w := w) (g := g) h₁ h₂ hD₁ hD₂ F κ₁ κ₂ hi e₁ e₂ hc U hU hW hWK hw hg

end Graph

section Twist

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem norm_detD {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.MainNotions.S.UJset ε) : ‖g.det‖ = 1 := by
  have hm : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := hg
  have hd := congrArg (fun A => ‖Matrix.det A‖) hm
  have hJ : ‖(Formalism.REAL.Jm ε).det‖ ≠ 0 := norm_ne_zero_iff.2
    ((Matrix.isUnit_iff_isUnit_det _).1 (IsUnit.of_mul_eq_one _ (Formalism.REAL.Jm_mul_self ε))).ne_zero
  simp only [Matrix.det_mul, Matrix.det_conjTranspose, norm_mul, norm_star] at hd
  have h2 : ‖g.det‖ ^ 2 = 1 := mul_right_cancel₀ hJ (by nlinarith)
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 h2

def twD (m : ℕ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H) :=
  fun g => g.det ^ m • σ g

theorem twD_rep (m : ℕ) (h : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) :
    Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) (twD m σ) := by
  refine ⟨⟨by simp [twD, h.1.1], fun a ha b hb => ?_⟩, fun g hg v => ?_, fun v => ?_⟩
  · simp only [twD]
    rw [h.1.2 a ha b hb, det_mul, mul_pow, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_smul]
  · simp only [twD, ContinuousLinearMap.smul_apply, norm_smul, norm_pow, norm_detD hg, one_pow, one_mul, h.2.1 g hg]
  · exact ((continuous_id.matrix_det).pow m).continuousOn.smul (h.2.2 v)

theorem twD_irr (m : ℕ) (h : Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) σ) :
    Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) (twD m σ) := fun S hS hinv => h S hS fun g hg v hv => by
  have h0 : g.det ^ m ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.1 (by rw [norm_detD hg]; exact one_ne_zero))
  exact (S.smul_mem_iff h0).1 (hinv g hg v hv)

theorem twD_kfin (m : ℕ) {v : H} (h : Formalism.MainNotions.S.IsKFin ε σ v) : Formalism.MainNotions.S.IsKFin ε (twD m σ) v := by
  obtain ⟨S, h1, h2, h3⟩ := h
  exact ⟨S, h1, h2, fun g hg u hu => S.smul_mem _ (h3 g hg u hu)⟩

end Twist

section Cover

variable {p q : ℕ} {T : GrpData p q} {πU : URep T} {M : GKMod p q} {io : M.V →ₗ[ℂ] πU.H}

theorem skewD (h : IsHCMod πU M io) : SkewD M io := fun Y hY v w => by
  have h1 := (h.2.2 Y hY v).inner ℂ (h.2.2 Y hY w)
  simp only [inner_piC, zero_smul, T.expt_zero, map_one, ContinuousLinearMap.one_apply] at h1
  have h2 := h1.unique (hasDerivAt_const _ _)
  linear_combination h2

theorem eigD (h : IsHCMod πU M io) {X : Mat p q} (hX : X ∈ upq p q) {v : M.V} {c : ℂ} (hv : M.act X v = c • v)
    (t : ℝ) : πU.π (T.expt (t • X)) (io v) = Complex.exp (c * t) • io v := _root_.GlobalTheory.HcPort.eigD (X := X) (v := v) (c := c) h hX hv t

theorem iE_memD (a : Formalism.BasicNotions.TH.Ix p q) : Complex.I • Eab a a ∈ upq p q :=
  mem_upq_of_adjZD (by
    rw [adjZ_smulD, adjZ_singleD a a (sameBlock_reflD a), show star Complex.I = -Complex.I from Complex.conj_I, neg_smul])

theorem exp_twoPiD (a : Formalism.BasicNotions.TH.Ix p q) :
    NormedSpace.exp (((2 * Real.pi : ℝ) : ℂ) • rx (Complex.I • Eab a a)) = 1 := _root_.GlobalTheory.HcPort.exp_twoPiD a

theorem signD (h : IsHCMod πU M io) {j : ℕ} {σ : Matrix (Fin (p + q)) (Fin (p + q)) ℂ → (πU.H →L[ℂ] πU.H)}
    (h1 : σ 1 = 1) (hex : ∀ X ∈ upq p q, inG (epq p q) (rx X) ∧ ∀ t : ℝ,
      πU.π (T.expt (t • X)) = Complex.exp ((j : ℂ) * (t * X.trace / 2)) • σ (NormedSpace.exp ((t : ℂ) • rx X)))
    (a : Formalism.BasicNotions.TH.Ix p q) {v : M.V} (hv0 : v ≠ 0) {c : ℂ} (hv : M.act (Eab a a) v = c • v) :
    Complex.exp (Complex.I * c * (2 * Real.pi : ℝ)) = (-1) ^ j := _root_.GlobalTheory.HcPort.signD (j := j) (σ := σ) (v := v) (c := c) h h1 hex a hv0 hv

theorem dictD (hS : KFSm) (h : IsHCMod πU M io) {j : ℕ} (m : ℕ)
    {σ : Matrix (Fin (p + q)) (Fin (p + q)) ℂ → (πU.H →L[ℂ] πU.H)}
    (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset (epq p q)) σ) (hσi : Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset (epq p q)) σ)
    (hkf : ∀ x, KFin T πU.π x ↔ Formalism.MainNotions.S.IsKFin (epq p q) σ x)
    (hex : ∀ X ∈ upq p q, inG (epq p q) (rx X) ∧ ∀ t : ℝ,
      πU.π (T.expt (t • X)) = Complex.exp ((j : ℂ) * (t * X.trace / 2)) • σ (NormedSpace.exp ((t : ℂ) • rx X))) :
    ∃ κ : M.V →ₗ[ℂ] smD (epq p q) (twD m σ), (∀ v, (κ v : πU.H) = io v) ∧ ∀ Z v,
      actM (smE (epq p q) (twD m σ)) (rx Z) (κ v) = κ (M.act Z v + (((m : ℂ) - j / 2) * Z.trace) • v) := by
  have hτ := twD_rep m hσ
  obtain ⟨hsm, -⟩ := hS _ _ _ (twD m σ) hτ (twD_irr m hσi)
  have hder := isDerivedOn_smE (ε := epq p q) (σ := twD m σ) hτ
  let κ : M.V →ₗ[ℂ] smD (epq p q) (twD m σ) :=
    io.codRestrict _ fun v => hsm _ (twD_kfin m ((hkf _).1 ((h.2.1 _).1 ⟨v, rfl⟩)))
  refine ⟨κ, fun _ => rfl, ?_⟩
  have key : ∀ Y ∈ upq p q, ∀ v, actLC (smE (epq p q) (twD m σ)) (rx Y) (κ v) =
      κ (M.act Y v + (((m : ℂ) - j / 2) * Y.trace) • v) := by
    intro Y hY v
    refine Subtype.ext ((hder.deriv _ (hex Y hY).1 (κ v)).unique ?_)
    have d1 : HasDerivAt (fun t : ℝ => (NormedSpace.exp (t • rx Y)).det) (rx Y).trace 0 :=
      PI.UnitaryCorollaryDerivatives.DjC.hasDerivAt_det_of_one _ _ (by simp) fun a b => PI.UnitaryCorollaryDerivatives.DjC.hasDerivAt_exp_entry (rx Y) a b
    have d2 := ((((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const Y.trace).div_const 2).const_mul (j : ℂ)).fun_neg.cexp
    have d3 := ((d1.fun_pow m).fun_mul d2).fun_smul (h.2.2 Y hY v)
    convert (preTransparency := .reducible) d3 using 1
    · funext t
      rw [(hex Y hY).2, ContinuousLinearMap.smul_apply, smul_smul, mul_assoc, ← Complex.exp_add]
      simp only [id, neg_add_cancel, Complex.exp_zero, mul_one, twD, ContinuousLinearMap.smul_apply, Complex.coe_smul]
      rfl
    · show io _ = _
      simp only [map_add (f := _), map_smul, id, zero_smul, NormedSpace.exp_zero, det_one, one_pow, Complex.ofReal_zero, zero_mul,
        zero_div, mul_zero, neg_zero, Complex.exp_zero, mul_one, one_mul, one_smul, T.expt_zero, map_one,
        ContinuousLinearMap.one_apply, trace_rxC, Complex.ofReal_one]
      congr 2
      ring
  intro Z v
  obtain ⟨Y₁, h₁, Y₂, h₂, e, -⟩ := upq_decC Z
  show actLC _ (rx Z) (κ v) = _
  rw [e, show rx (Y₁ + Complex.I • Y₂) = rx Y₁ + Complex.I • rx Y₂ from rfl]
  simp only [map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply, key Y₁ h₁, key Y₂ h₂, trace_add, trace_smul,
    smul_eq_mul]
  module

end Cover

theorem clause2_of (h1 : Clause1) (hS : KFSm) (hC : CasScal) (hDe : Descend) : Clause2 := _root_.GlobalTheory.HcPort.clause2_of h1 hS hC hDe

end CompanionTheory.D.gk.HC
