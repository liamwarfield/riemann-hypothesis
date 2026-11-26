module

public import CompanionTheory.AutomorphicTheory.SchurLimitBounds.ZuckermanDuality.Assemble
public import CompanionTheory.AutomorphicTheory.SchurLimitBounds.ZuckermanDuality.GeneratingFunctionPolynomial
public import CompanionTheory.AutomorphicTheory.KFiniteVectors.KDecay
public import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.CapelliEigenvalues.CoefEigOfInfChar
public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.UniformCoefficientBounds.CoefBoundUniform

@[expose] public section

section -- merged from CompanionTheory.AutomorphicTheory.ZuckermanCommutation.CapelliEigenvalues.CoefCC
open Matrix MeasureTheory Set
open scoped ContDiff InnerProductSpace

noncomputable section

namespace CompanionTheory.CapEig

open CompanionTheory.D.Upq.Sm Formalism.FourierDecayAlt CompanionTheory.LimBd.Main

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Deriv

variable {k r : ℕ} {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup E] [NormedSpace ℂ E] {G : Set (B.Mat k r)} {σ : B.Mat k r → (H →L[ℂ] H)}

def cf (σ : B.Mat k r → (H →L[ℂ] H)) (x₀ : E) (a b : H) (g : B.Mat k r) : E := ⟪a, σ g b⟫_ℂ • x₀

theorem rw_cf (h : RepOn G σ) (x₀ : E) (a : H) {b : H} (hb : IsSm G σ b) {f : B.Mat k r → E}
    (hf : ∀ g ∈ G, f g = cf σ x₀ a b g) :
    ∀ {v : List (B.Mat k r)}, LieW G v → ∀ g ∈ G, B.Rw v f g = cf σ x₀ a (dsW σ v b) g
  | [], _, g, hg => hf g hg
  | X :: v, hv, g, hg => by
    have hv' : LieW G v := fun Y hY => hv Y (List.mem_cons_of_mem _ hY)
    have hX := hv X List.mem_cons_self
    change deriv (fun t : ℝ => B.Rw v f (g * ex X t)) 0 = _
    have e : (fun t : ℝ => B.Rw v f (g * ex X t)) =
        fun t => ⟪a, σ g (σ (ex X t) (dsW σ v b))⟫_ℂ • x₀ := by
      ext1 t
      rw [rw_cf h x₀ a hb hf hv' _ (h.mul_mem _ hg _ (hX t)), cf, h.apply_mul hg (hX t)]
    rw [e]
    have h1 := ((hb.dsW h hv').differentiableAt h hX).hasDerivAt
    let L : H →L[ℝ] E := (((innerSL ℂ a).comp (σ g)).smulRight x₀).restrictScalars ℝ
    exact (L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1).deriv

theorem lw_cf (h : RepOn G σ) (hiso : ∀ g ∈ G, ∀ v, ‖σ g v‖ = ‖v‖) (x₀ : E) {a : H}
    (ha : IsSm G σ a) (b : H) {f : B.Mat k r → E} (hf : ∀ g ∈ G, f g = cf σ x₀ a b g) :
    ∀ {u : List (B.Mat k r)}, LieW G u → ∀ g ∈ G,
      u.foldr B.LdV f g = cf σ x₀ (dsW σ u a) b g
  | [], _, g, hg => hf g hg
  | X :: u, hu, g, hg => by
    have hu' : LieW G u := fun Y hY => hu Y (List.mem_cons_of_mem _ hY)
    have hX := hu X List.mem_cons_self
    change deriv (fun t : ℝ => u.foldr B.LdV f (NormedSpace.exp (-((t : ℂ) • X)) * g)) 0 = _
    have e : (fun t : ℝ => u.foldr B.LdV f (NormedSpace.exp (-((t : ℂ) • X)) * g)) =
        fun t => ⟪σ (ex X t) (dsW σ u a), σ g b⟫_ℂ • x₀ := by
      ext1 t
      have e1 : NormedSpace.exp (-((t : ℂ) • X)) = ex X (-t) := by simp [ex]
      rw [e1, lw_cf h hiso x₀ ha b hf hu' _ (h.mul_mem _ (hX _) _ hg), cf]
      let I : H →ₗᵢ[ℂ] H := ⟨σ (ex X t), hiso _ (hX t)⟩
      rw [← I.inner_map_map]
      change ⟪σ (ex X t) _, σ (ex X t) (σ (ex X (-t) * g) b)⟫_ℂ • x₀ = _
      rw [← h.apply_mul (hX t) (h.mul_mem _ (hX _) _ hg), ← Matrix.mul_assoc, ← ex_add,
        add_neg_cancel, ex_zero, Matrix.one_mul]
    rw [e]
    have h1 := ((ha.dsW h hu').differentiableAt h hX).hasDerivAt
    have h2 := (h1.inner ℂ (hasDerivAt_const (0 : ℝ) (σ g b))).smul_const x₀
    rw [h2.deriv]
    simp [cf, dsW_cons, ds]

end Deriv

theorem capelli_coefficient_smooth : CoefSmooth := by
  intro hK k r ε μ φ E _ _ T hφ g₀ hg₀
  obtain ⟨H, _, _, _, σ, v, w, hμ, hσ, hv, -, he⟩ := hφ
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hK k r ε μ H σ hμ hσ v hv g₀ hg₀
  refine ⟨U, fun x => (((innerSL ℂ w).smulRight T).restrictScalars ℝ) (F x), hU, hgU,
    (((innerSL ℂ w).smulRight T).restrictScalars ℝ).contDiff.comp_contDiffOn hF, fun g hg hgG => ?_⟩
  have e := hfF g hg hgG
  simp only at e
  simp [he g hgG, e]

theorem capelli_coefficient_continuity : CoefCC := by
  intro hK k r ε A h hD μ φ E _ _ x₀ m hφ hgap
  have hsm := capelli_coefficient_smooth hK k r ε μ φ E x₀ hφ
  obtain ⟨H, _, _, _, σ, v, w, hμ, hσ, hv, hw, he⟩ := hφ
  obtain ⟨P, ⟨⟨hP, hPJ⟩, -⟩, -, -, ⟨⟨h1, hm⟩, hiso, -⟩, -⟩ := id hσ
  obtain ⟨hc1, -⟩ := conj_facts hP hPJ
  have hG : PI.IsMatGroup (B.GV k r) := PI.QuotSetU.UnitaryGroupMassFormula.unitary_hermitian_group k r
  have hrep : RepOn (B.GV k r) σ := repOn_of_conj hP hPJ h1 hm
  have hiso' : ∀ g ∈ B.GV k r, ∀ v, ‖σ g v‖ = ‖v‖ := fun g hg v => by
    obtain ⟨b, hb, rfl⟩ := hc1 g hg
    exact hiso b hb v
  have good : ∀ {x : H}, PI.UpqRep.IsKFinHpk (k := k) (r := r) σ x → IsSm (B.GV k r) σ x ∧
      ∃ (T' : Submodule ℂ H) (C : ℝ), GoodSub (B.GV k r)
        (B.GV k r ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set _)) σ T' ∧ 0 ≤ C ∧
        ∀ W : List (B.Mat k r), LieW (B.GV k r) W → (∀ X ∈ W, ‖X‖ ≤ 1) → W.length ≤ m →
          dsW σ W x ∈ T' ∧ ‖dsW σ W x‖ ≤ C := by
    rintro x ⟨S, hS, hxS, hSK⟩
    have hT : GoodSub (B.GV k r) (B.GV k r ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set _))
        σ S := ⟨hS, fun v hv => hK k r ε μ H σ hμ hσ v ⟨S, hS, hv, hSK⟩, hSK⟩
    exact ⟨hT.sm x hxS, hT.words hG hrep inter_subset_left hxS m⟩
  obtain ⟨hvs, Tv, Cv, hTv, hCv, hWv⟩ := good hv
  obtain ⟨hws, Tw, Cw, hTw, hCw, hWw⟩ := good hw
  have := hTv.fin
  have := hTw.fin
  have hkf : ∀ a ∈ Tv ⊔ Tw, PI.UpqRep.IsKFinHpk (k := k) (r := r) σ a := by
    intro a ha
    refine ⟨Tv ⊔ Tw, inferInstance, ha, fun g hg x hx => ?_⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (hTv.stab g hg y hy) (hTw.stab g hg z hz)
  obtain ⟨C', hC', hb⟩ := coef_bound_uniform (G := B.GV k r) (σ := σ) (T := Tv ⊔ Tw)
    (ρ := fun g => (B.gN g ^ A)⁻¹) (fun g _ => inv_nonneg.2 (Real.rpow_nonneg (Real.sqrt_nonneg _) _))
    (fun a ha b hb => by
      obtain ⟨C, hd⟩ := hD μ H σ hμ hσ hgap b a (hkf b hb) (hkf a ha)
      refine ⟨C, fun g hg => ?_⟩
      have hp : 0 < B.gN g ^ A := Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hg)) A
      rw [← div_eq_mul_inv, le_div_iff₀ hp, mul_comm]
      exact hd g hg)
  refine ⟨C' * Cw * Cv * ‖x₀‖, fun g₀ hg₀ => ?_, fun u v' hu hv' huv g hg => ?_⟩
  · obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hsm g₀ hg₀
    exact ⟨U, F, hU, hgU, hF.of_le (by exact_mod_cast le_top), hfF⟩
  · have hlie : ∀ W : List (B.Mat k r), (∀ X ∈ W, B.unitLie k r X) →
        LieW (B.GV k r) W ∧ ∀ X ∈ W, ‖X‖ ≤ 1 := fun W hW =>
      ⟨fun X hX t => ex_mem_of_lie (hW X hX).1 t,
        fun X hX => (Matrix.norm_le_iff zero_le_one).2 (hW X hX).2⟩
    obtain ⟨hu1, hu2⟩ := hWw u (hlie u hu).1 (hlie u hu).2 (by omega)
    obtain ⟨hv1, hv2⟩ := hWv v' (hlie v' hv').1 (hlie v' hv').2 (by omega)
    have e : B.dLR u v' (fun g => φ g • x₀) g = cf σ x₀ (dsW σ u w) (dsW σ v' v) g :=
      lw_cf hrep hiso' x₀ hws _ (rw_cf hrep x₀ w hvs (fun g hg => by rw [he g hg]; rfl) (hlie v' hv').1)
        (hlie u hu).1 g hg
    rw [e, cf, norm_smul]
    have hp : 0 < B.gN g ^ A := Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hg)) A
    have h2 := hb _ (Submodule.mem_sup_right hu1) _ (Submodule.mem_sup_left hv1) g hg
    have h5 : 0 ≤ (B.gN g ^ A)⁻¹ := inv_nonneg.2 hp.le
    calc _ ≤ B.gN g ^ A * (C' * Cw * Cv * (B.gN g ^ A)⁻¹ * ‖x₀‖) := by
          gcongr
          exact h2.trans (by gcongr)
      _ = (B.gN g ^ A * (B.gN g ^ A)⁻¹) * (C' * Cw * Cv * ‖x₀‖) := by ring
      _ = _ := by rw [mul_inv_cancel₀ hp.ne', one_mul]

end CompanionTheory.CapEig

end
end

section -- merged from CompanionTheory.AutomorphicTheory.SchurLimitBounds.ZuckermanDuality.BetaAtInfinityZero
noncomputable section

namespace CompanionTheory.LimBd.Main

open Formalism.FourierDecayAlt PI.UpqRep Matrix CompanionTheory.LimBd.SchurHpk MeasureTheory
open scoped InnerProductSpace

theorem beta_at_infinity_zero : BetaInfZero := by
  intro k r Wp Wq _ _ _ _ _ _ D F F' h
  unfold B.betaInf B.betaInfTau
  refine integral_eq_zero_of_ae ?_
  filter_upwards [P.B5.ae_inSS D] with p hp
  have hχ : ∀ t, D.χ t ≠ 0 → t ≠ 0 := fun t ht h0 => by
    have := (D.χ_supp (subset_tsupport _ ht)).1
    rw [h0] at this
    norm_num at this
  have h0 : B.regBracket D F F' p = fun _ _ => 0 := by
    funext t₁ t₂
    unfold B.regBracket
    by_cases h1 : D.χ t₁ = 0
    · simp [h1]
    by_cases h2 : D.χ t₂ = 0
    · simp [h2]
    rw [h (B.dilation₂ (t₁, t₂) p) ⟨hp.1, P.B5.dil_mem_N t₁ (hχ _ h1) hp.2.1, hp.2.2.1,
      P.B5.dil_mem_N t₂ (hχ _ h2) hp.2.2.2⟩, mul_zero]
  simp [h0, B.oneMinusDD]

theorem inner_translate {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : B.Mat k r → (H →L[ℂ] H)} (hσ : IsURepOn (UH (Hpk k r)) σ) {a g b : B.Mat k r} (ha : a ∈ UH (Hpk k r))
    (hg : g ∈ UH (Hpk k r)) (hb : b ∈ UH (Hpk k r)) (v w : H) :
    ⟪w, σ (a * g * b) v⟫_ℂ = ⟪σ a⁻¹ w, σ g (σ b v)⟫_ℂ := by
  obtain ⟨hu, hai, hm⟩ := PI.UnitaryGroupMassFormula.CapelliEig.unitary_Hecke_group k r a ha
  let L : H →ₗᵢ[ℂ] H := ⟨(σ a : H →ₗ[ℂ] H), hσ.2.1 a ha⟩
  have e : σ a (σ a⁻¹ w) = w := by
    have := hσ.1.2 a ha _ hai
    rw [Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hu), hσ.1.1] at this
    exact (congrArg (fun T : H →L[ℂ] H => T w) this).symm
  rw [hσ.1.2 _ (hm g hg) b hb, hσ.1.2 a ha g hg, ← L.inner_map_map (σ a⁻¹ w)]
  show _ = ⟪σ a (σ a⁻¹ w), _⟫_ℂ
  rw [e]
  rfl

theorem phase_zero_alt : PhZero := by
  intro hE k r Wp Wq _ _ _ _ _ _ D ε μ μ' φ φ' T T' hφ hφ' hne p hp
  obtain ⟨H, i1, i2, i3, σ, v, w, hμ, hσ, -, -, hφG⟩ := hφ
  obtain ⟨H', j1, j2, j3, σ', v', w', hμ', hσ', -, -, hφG'⟩ := hφ'
  have hR := isURepOn_of_ds hσ
  have grp := PI.UnitaryGroupMassFormula.CapelliEig.unitary_Hecke_group k r
  set a : B.Mat k r := (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ with ha'
  set b : B.Mat k r := Matrix.of p.2.2 * Matrix.of p.2.1 with hb'
  have ha : a ∈ UH (Hpk k r) := (grp _ (grp _ hp.1.1).2.1).2.2 _ (grp _ hp.2.1.1).2.1
  have hb : b ∈ UH (Hpk k r) := (grp _ hp.2.2.2.1).2.2 _ hp.2.2.1.1
  have hμG : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) D.μG :=
    ⟨P.B5.haar_sigmaFinite D.haarG, D.haarG.ne_zero, D.haarG.conc, D.haarG.left⟩
  have hz := (schur_inequiv hσ hσ' (capelli_inequivalence hE k r ε ε μ μ' H H' σ σ' hμ hμ' hσ hσ' hne) hμG
    (σ b v) (σ a⁻¹ w) v' w').2
  set S : Wq →L[ℂ] Wp := (D.π (Matrix.of p.1.1)).comp (T.comp (D.π' (Matrix.of p.2.1)⁻¹))
  unfold B.Ph
  rw [← zero_mul (B.hsInner S T'), ← hz, ← integral_mul_const]
  refine integral_congr_ae ?_
  have hae : ∀ᵐ g ∂D.μG, Matrix.of g ∈ B.GV k r := D.haarG.conc
  filter_upwards [hae] with g hg
  have e1 : B.sgs p (Matrix.of g) = a * Matrix.of g * b := by
    simp only [B.sgs, ha', hb', Matrix.mul_assoc]
  have hm : a * Matrix.of g * b ∈ UH (Hpk k r) := (grp _ ((grp _ ha).2.2 _ hg)).2.2 _ hb
  have e2 : B.rho D p (fun g => φ g • T) (Matrix.of g) = φ (a * Matrix.of g * b) • S := by
    simp only [B.rho, e1, S, ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp]
  rw [e2, P.B6.hsInner_smul_left, P.B6.hsInner_smul_right, hφG _ hm, hφG' _ hg, inner_translate hR ha hg hb,
    ← mul_assoc]
  rfl

end CompanionTheory.LimBd.Main
end
end

noncomputable section

namespace CompanionTheory.LimBd.Main

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP

theorem span_powers : SpanPow := mul_mem_spanBox_of_gap

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

end CompanionTheory.LimBd.Main
