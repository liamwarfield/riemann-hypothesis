module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsClosedParabolicSubgroups
public import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.ConvAssoc
public import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.ContinuousAverage

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.ConvEig
open MeasureTheory Filter UpperTheory.Lit.Cusp
open scoped Topology

theorem UpperTheory.Lit.Cusp.conv_isEig :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (N : Set G) (a : ℝ → G) (f h : G → ℂ) (s C : ℝ),
      Integrable f μ → IsEig N a s C h → IsEig N a s ((∫ g, ‖f g‖ ∂μ) * C) (conv μ f h) := by
  intro G _ _ _ _ _ _ _ _ μ _ N a f h s C hf hh
  obtain ⟨hc, hb, hN, ha⟩ := hh
  have hbound : ∀ x g, ‖f g * h (g⁻¹ * x)‖ ≤ ‖f g‖ * C := fun x g => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hb _) (norm_nonneg _)
  have hint : Integrable (fun g => ‖f g‖ * C) μ := hf.norm.mul_const C
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold conv
    refine continuous_of_dominated (bound := fun g => ‖f g‖ * C) ?_ ?_ hint ?_
    · intro x
      refine hf.aestronglyMeasurable.mul ?_
      exact (hc.comp (continuous_inv.mul continuous_const)).aestronglyMeasurable
    · intro x
      exact Eventually.of_forall (hbound x)
    · refine Eventually.of_forall fun g => ?_
      exact continuous_const.mul (hc.comp (continuous_const.mul continuous_id))
  · intro x
    unfold conv
    rw [← integral_mul_const]
    exact norm_integral_le_of_norm_le hint (Eventually.of_forall (hbound x))
  · intro x m hm
    unfold conv
    simp only [← mul_assoc, hN _ m hm]
  · intro x t
    unfold conv
    rw [← integral_const_mul]
    congr 1
    funext g
    rw [← mul_assoc, ha]
    ring
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.IntegralCoefEqZero
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.FlagNW
open MeasureTheory Filter Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.FlagMeas GlobalTheory.RealInd UpperTheory.Lit.Cusp
open GlobalTheory.Dec (IsHaarSub IsIsoC NW IsSqIntIrr)
open scoped Topology InnerProductSpace

private theorem herm_eq_zero_iff {n : ℕ} (ε : Fin n → Bool) (x y : Fin n → ℂ) :
    Formalism.QuantumDeterminants.herm (Jm ε) x y = 0 ↔ star x ⬝ᵥ (Jm ε *ᵥ y) = 0 := by
  have e : Formalism.QuantumDeterminants.herm (Jm ε) x y = star (star x ⬝ᵥ (Jm ε *ᵥ y)) := by
    simp only [Formalism.QuantumDeterminants.herm, Jm, dotProduct, Matrix.mulVec_diagonal, star_sum, Pi.star_apply, star_mul', star_star]
    refine Finset.sum_congr rfl fun i _ => ?_
    cases ε i <;> simp <;> ring
  rw [e, star_eq_zero]

private theorem herm_keep {n : ℕ} {H g : Matrix (Fin n) (Fin n) ℂ} (hg : gᴴ * H * g = H) (x y : Fin n → ℂ) :
    Formalism.QuantumDeterminants.herm H (g *ᵥ x) (g *ᵥ y) = Formalism.QuantumDeterminants.herm H x y := by
  simp only [Formalism.QuantumDeterminants.herm]
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg]

theorem UpperTheory.Lit.Cusp.flagN_eq_NW :
    ∀ (n : ℕ) (ε : Fin n → Bool) (W : Submodule ℂ (Fin n → ℂ)), IsIsoC ε W →
      IsIsoFlag ε ![Module.finrank ℂ W] ![⊥, W] ∧ 1 ≤ Module.finrank ℂ W ∧ flagN ε ![⊥, W] = NW ε W ∧
        ∃ S : Subgroup (UJ ε), (S : Set (UJ ε)) = NW ε W := by
  intro n ε W hW
  have hl : (![⊥, W] : Fin (1 + 1) → Submodule ℂ (Fin n → ℂ)) (Fin.last 1) = W := rfl
  refine ⟨⟨rfl, ?_, ?_, ?_⟩, ?_, ?_, GlobalTheory.Dec.nwSub ε W, rfl⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · intro i
    fin_cases i
    show Module.finrank ℂ W = Module.finrank ℂ (⊥ : Submodule ℂ (Fin n → ℂ)) + Module.finrank ℂ W
    rw [finrank_bot, zero_add]
  · rw [hl]
    intro x hx y hy
    exact (herm_eq_zero_iff ε x y).1 (hW.2 x hx y hy)
  · exact Submodule.one_le_finrank_iff.2 hW.1
  · ext g
    have e : ∀ y, (umat g - 1) *ᵥ y = uMat g *ᵥ y - y := fun y => by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    simp only [flagN, NW, Set.mem_setOf_eq, hl, e]
    constructor
    · rintro ⟨h1, h2⟩
      have h1' : ∀ x ∈ W, uMat g *ᵥ x - x = 0 := fun x hx => (Submodule.mem_bot ℂ).1 (h1 0 x hx)
      refine ⟨h1', fun y hy => h2 y fun x hx => (herm_eq_zero_iff ε x y).1 (hy x hx), fun y x hx => ?_⟩
      have hg : (uMat g)ᴴ * Jm ε * uMat g = Jm ε := g.2
      have k := herm_keep hg x y
      rw [sub_eq_zero.1 (h1' x hx)] at k
      simp only [Formalism.QuantumDeterminants.herm, star_sub, sub_dotProduct] at k ⊢
      rw [k, sub_self]
    · rintro ⟨h1, h2, -⟩
      refine ⟨fun i y hy => ?_, fun y hy => h2 y fun x hx => (herm_eq_zero_iff ε x y).2 (hy x hx)⟩
      fin_cases i
      exact (Submodule.mem_bot ℂ).2 (h1 y hy)
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.ConvCoef
open MeasureTheory Filter Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.FlagMeas GlobalTheory.RealInd UpperTheory.Lit.Cusp
open GlobalTheory.Dec (IsHaarSub IsIsoC NW IsSqIntIrr)
open scoped Topology InnerProductSpace

theorem UpperTheory.Lit.Cusp.conv_coef :
    ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (d : ℝ), IsURepOn (UJset ε) σ → IsFdeg (muG ε) σ d → ∀ v a : H,
        Continuous (coefOn (ε := ε) σ a v) ∧
          ∀ x, conv (muG ε) (coefOn σ v v) (coefOn σ a v) x = ((‖v‖ ^ 2 / d : ℝ) : ℂ) * coefOn σ a v x := by
  intro n ε H _ _ σ d hrep hF v a
  obtain ⟨⟨_, hmul⟩, hiso, hcont⟩ := hrep
  have hinner : ∀ g ∈ UJset ε, ∀ x y : H, ⟪σ g x, σ g y⟫_ℂ = ⟪x, y⟫_ℂ := fun g hg x y =>
    LinearIsometry.inner_map_map ⟨(σ g).toLinearMap, hiso g hg⟩ x y
  have hmem : ∀ g : UJ ε, umat g ∈ UJset ε := fun g => g.2
  have hcoef : ∀ w z : H, Continuous (coefOn (ε := ε) σ w z) := by
    intro w z
    have hu : Continuous fun g : UJ ε => umat g :=
      Units.continuous_val.comp continuous_subtype_val
    have hs : Continuous fun g : UJ ε => σ (umat g) w :=
      (hcont w).comp_continuous hu hmem
    exact continuous_const.inner hs
  refine ⟨hcoef a v, fun x => ?_⟩
  have hback : ∀ (g : UJ ε) (y : H), σ (umat g) (σ (umat g⁻¹) y) = y := by
    intro g y
    have h := hmul _ (hmem g) _ (hmem g⁻¹)
    have hone : umat g * umat g⁻¹ = 1 := by
      show ((g * g⁻¹ : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ).val = 1
      rw [mul_inv_cancel]
      rfl
    rw [hone] at h
    have h1 : σ 1 = 1 := by assumption
    rw [h1] at h
    exact (congrArg (fun f : H →L[ℂ] H => f y) h).symm
  have key : ∀ g : UJ ε, coefOn σ v v g * coefOn σ a v (g⁻¹ * x) =
      coefOn σ v v g * star (coefOn σ v (σ (umat x) a) g) := by
    intro g
    congr 1
    simp only [coefOn]
    have hsplit : σ (umat (g⁻¹ * x)) a = σ (umat g⁻¹) (σ (umat x) a) := by
      rw [show umat (g⁻¹ * x) = umat g⁻¹ * umat x from rfl, hmul _ (hmem _) _ (hmem _)]
      rfl
    rw [hsplit]
    calc ⟪v, σ (umat g⁻¹) (σ (umat x) a)⟫_ℂ
        = ⟪σ (umat g) v, σ (umat g) (σ (umat g⁻¹) (σ (umat x) a))⟫_ℂ :=
          (hinner _ (hmem g) _ _).symm
      _ = ⟪σ (umat g) v, σ (umat x) a⟫_ℂ := by rw [hback]
      _ = star ⟪σ (umat x) a, σ (umat g) v⟫_ℂ := by
          rw [← inner_conj_symm]
          rfl
  show ∫ g, coefOn σ v v g * coefOn σ a v (g⁻¹ * x) ∂(muG ε) = _
  rw [show (fun g => coefOn σ v v g * coefOn σ a v (g⁻¹ * x)) =
      fun g => coefOn σ v v g * star (coefOn σ v (σ (umat x) a) g) from funext key,
    (hF.2 v v v (σ (umat x) a)).2, inner_self_eq_norm_sq_to_K]
  show _ = _ * ⟪v, σ (umat x) a⟫_ℂ
  push_cast
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_assoc, mul_comm]
  rw [mul_comm (_ * _) _, mul_comm ⟪v, σ (umat x) a⟫_ℂ, ← mul_assoc]
  rfl
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.Abstract
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.KillsOfIdem
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.OpLeHalf
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.Transl
open MeasureTheory Filter UpperTheory.Lit.Cusp
open scoped Topology

theorem UpperTheory.Lit.Cusp.transl_small :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (f : G → ℂ), Integrable f μ →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ b in 𝓝 (1 : G), ∫ g, ‖f (b * g) - f g‖ ∂μ ≤ ε := by
  intro G _ _ _ _ _ _ _ _ μ _ f hf ε hε
  haveI : Fact ((1 : ENNReal) ≠ ⊤) := ⟨ENNReal.one_ne_top⟩
  have hm : MemLp f 1 μ := memLp_one_iff_integrable.2 hf
  set F : Lp ℂ 1 μ := hm.toLp f with hF
  have hc : Continuous fun b : G => ‖(DomMulAct.mk b) • F - F‖ :=
    ((DomMulAct.continuous_mk.smul continuous_const).sub continuous_const).norm
  have h1 : ‖(DomMulAct.mk (1 : G)) • F - F‖ < ε := by
    have : (DomMulAct.mk (1 : G)) • F = F := one_smul Gᵈᵐᵃ F
    rw [this, sub_self, norm_zero]; exact hε
  have hev := hc.continuousAt.eventually_lt continuousAt_const h1
  filter_upwards [hev] with b hb
  refine le_of_eq_of_le ?_ hb.le
  rw [L1.norm_eq_integral_norm]
  refine integral_congr_ae ?_
  have hFf : F =ᵐ[μ] f := hm.coeFn_toLp
  have h2 : (fun g => F (b * g)) =ᵐ[μ] fun g => f (b * g) :=
    (measurePreserving_mul_left μ b).quasiMeasurePreserving.ae_eq_comp hFf
  filter_upwards [Lp.coeFn_sub ((DomMulAct.mk b) • F) F, DomMulAct.smul_Lp_ae_eq (DomMulAct.mk b) F, hFf, h2] with g e1 e2 e3 e4
  rw [e1, Pi.sub_apply, e2, e3, ← e4]
  rfl
end

open MeasureTheory Filter UpperTheory.Lit.Cusp
open scoped Topology

theorem UpperTheory.Lit.Cusp.opLe_half :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (N : Set G) (a : ℝ → G) (H : G → ℝ) (f : G → ℂ),
      IsRay N a H → Integrable f μ → ∃ s : ℝ, OpLe μ N a f s (1 / 2) := by
  intro G _ _ _ _ _ _ _ _ μ _ N a H f hR hf
  have hU := transl_small G μ f hf 1 one_pos
  have a0 : a 0 = 1 := by
    have := hR.add 0 0
    rw [add_zero] at this
    exact (mul_eq_left.mp this.symm)
  obtain ⟨D, hD, hk⟩ := hR.cpt
  have hc : Continuous fun p : ℝ × G => p.2 * a p.1 * p.2⁻¹ :=
    (continuous_snd.mul (hR.cont.comp continuous_fst)).mul continuous_snd.inv
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ k ∈ D, ∫ g, ‖f ((k * a t * k⁻¹) * g) - f g‖ ∂μ ≤ 1 := by
    apply hD.eventually_forall_of_forall_eventually
    intro k _
    have ht : Tendsto (fun p : ℝ × G => p.2 * a p.1 * p.2⁻¹) (𝓝 (0, k)) (𝓝 1) := by
      have := hc.tendsto (0, k)
      simpa [a0] using this
    exact ht.eventually hU
  have hev' : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ k ∈ D, ∫ g, ‖f ((k * a t * k⁻¹) * g) - f g‖ ∂μ ≤ 1 :=
    hev.filter_mono nhdsWithin_le_nhds
  obtain ⟨t, ht, htpos⟩ := (hev'.and self_mem_nhdsWithin).exists
  have htpos : 0 < t := htpos
  refine ⟨Real.pi / t, ?_⟩
  rintro C h ⟨hcont, hbd, hN, hE⟩ x
  obtain ⟨k, hkD, hk⟩ := hk x
  obtain ⟨m, hm, hkm⟩ := hk t
  have hb := ht k hkD
  set b := k * a t * k⁻¹ with hbdef
  have hneg : ∀ g, h (g⁻¹ * b * x) = - h (g⁻¹ * x) := by
    intro g
    have e : g⁻¹ * b * x = g⁻¹ * x * a t * m := by
      rw [mul_assoc, hkm]; simp only [mul_assoc]
    rw [e, hN _ m hm, hE]
    have : Real.pi / t * t = Real.pi := by field_simp
    rw [this, Complex.exp_pi_mul_I]; ring
  have h1 : ∫ g, f (b * g) * h (g⁻¹ * x) ∂μ = - conv μ f h x := by
    have := integral_mul_left_eq_self (μ := μ) (fun g => f g * h (g⁻¹ * b * x)) b
    simp only [mul_inv_rev, inv_mul_cancel_right] at this
    rw [this, conv, ← integral_neg]
    congr 1
    ext g
    rw [hneg]; ring
  have hfb : Integrable (fun g => f (b * g)) μ := hf.comp_mul_left b
  have hmeas : AEStronglyMeasurable (fun g => h (g⁻¹ * x)) μ :=
    (hcont.comp (continuous_inv.mul continuous_const)).aestronglyMeasurable
  have i1 : Integrable (fun g => f (b * g) * h (g⁻¹ * x)) μ :=
    hfb.mul_bdd hmeas (Eventually.of_forall fun g => hbd _)
  have i2 : Integrable (fun g => f g * h (g⁻¹ * x)) μ :=
    hf.mul_bdd hmeas (Eventually.of_forall fun g => hbd _)
  have h2 : ∫ g, (f (b * g) - f g) * h (g⁻¹ * x) ∂μ = -2 * conv μ f h x := by
    simp only [sub_mul]
    rw [integral_sub i1 i2, h1, conv]; ring
  have hC : 0 ≤ C := (norm_nonneg _).trans (hbd 1)
  have h3 : ‖∫ g, (f (b * g) - f g) * h (g⁻¹ * x) ∂μ‖ ≤ C := by
    calc _ ≤ ∫ g, ‖f (b * g) - f g‖ * C ∂μ := by
          apply norm_integral_le_of_norm_le ((hfb.sub hf).norm.mul_const C)
          refine Eventually.of_forall fun g => ?_
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hbd _) (norm_nonneg _)
      _ = (∫ g, ‖f (b * g) - f g‖ ∂μ) * C := integral_mul_const _ _
      _ ≤ 1 * C := mul_le_mul_of_nonneg_right hb hC
      _ = C := one_mul C
  rw [h2, norm_mul] at h3
  simp at h3
  linarith
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.ExistsCompactTail
open MeasureTheory Filter UpperTheory.Lit.Cusp
open scoped Topology

private theorem exists_compact_tail {G : Type} [TopologicalSpace G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) (f : G → ℂ)
    (hf : Integrable f μ) (ε : ℝ) (hε : 0 < ε) :
    ∃ D : Set G, IsCompact D ∧ ∫ g, Dᶜ.indicator (fun g => ‖f g‖) g ∂μ ≤ ε := by
  have hm : ∀ n, MeasurableSet (compactCovering G n)ᶜ := fun n =>
    (isCompact_compactCovering G n).isClosed.measurableSet.compl
  have ht : Tendsto (fun n => ∫ g, (compactCovering G n)ᶜ.indicator (fun g => ‖f g‖) g ∂μ) atTop
      (𝓝 (∫ _g, (0 : ℝ) ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun g => ‖f g‖)
      (fun n => (hf.norm.indicator (hm n)).aestronglyMeasurable) hf.norm (fun n => ?_) ?_
    · refine Eventually.of_forall fun g => ?_
      simpa using norm_indicator_le_norm_self (s := (compactCovering G n)ᶜ) (fun g => ‖f g‖) g
    · refine Eventually.of_forall fun g => ?_
      obtain ⟨n, hn⟩ := exists_mem_compactCovering g
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop n] with m hm'
      have : g ∈ compactCovering G m := compactCovering_subset G hm' hn
      simp [this]
  rw [integral_zero] at ht
  obtain ⟨n, hn⟩ := (ht.eventually (ge_mem_nhds hε)).exists
  exact ⟨_, isCompact_compactCovering G n, hn⟩

private theorem isEig_twist {G : Type} [Group G] [TopologicalSpace G] {N : Set G} {a : ℝ → G} {H : G → ℝ}
    (hr : IsRay N a H) {s s' C : ℝ} {h : G → ℂ} (hh : IsEig N a s' C h) :
    IsEig N a s C (fun g => Complex.exp (Complex.I * (((s - s') * H g : ℝ) : ℂ)) * h g) := by
  obtain ⟨h1, h2, h3, h4⟩ := hh
  have hH := hr.contH
  refine ⟨by fun_prop, fun g => ?_, fun g m hm => ?_, fun g t => ?_⟩
  · rw [norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]; exact h2 g
  · simp only [hr.inv g m hm, h3 g m hm]
  · simp only [hr.move g t, h4 g t]
    rw [← mul_assoc, ← mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
    congr 2
    push_cast
    ring

theorem UpperTheory.Lit.Cusp.opLe_near :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (N : Set G) (a : ℝ → G) (H : G → ℝ) (f : G → ℂ),
      IsRay N a H → Integrable f μ → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ s s' r : ℝ, |s - s'| < δ → OpLe μ N a f s r → OpLe μ N a f s' (r + ε) := by
  intro G _ _ _ _ _ _ _ _ μ _ N a H f hr hf ε hε
  obtain ⟨D, hD, hDε⟩ := exists_compact_tail μ f hf (ε / 4) (by positivity)
  obtain ⟨c, hc⟩ := hr.bdd D hD
  have hmD : MeasurableSet Dᶜ := hD.isClosed.measurableSet.compl
  set A : ℝ := ∫ g, ‖f g‖ ∂μ with hA
  have hA0 : 0 ≤ A := integral_nonneg fun g => norm_nonneg _
  set δ : ℝ := ε / 2 / ((|c| + 1) * (A + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδe : δ * ((|c| + 1) * (A + 1)) = ε / 2 := by rw [hδ]; field_simp
  refine ⟨δ, hδ0, fun s s' r hs hop C h hh x => ?_⟩
  have hC : 0 ≤ C := (norm_nonneg _).trans (hh.2.1 1)
  have ht := isEig_twist (s := s) hr hh
  have h1 := hop C _ ht x
  have hint : ∀ {t : ℝ} {k : G → ℂ}, IsEig N a t C k → Integrable (fun g => f g * k (g⁻¹ * x)) μ := by
    intro t k hk
    have hk1 := hk.1
    have hc : Continuous fun g : G => k (g⁻¹ * x) := by fun_prop
    exact hf.mul_bdd hc.aestronglyMeasurable (Eventually.of_forall fun g => hk.2.1 _)
  set u : ℂ := Complex.exp (Complex.I * ((-((s - s') * H x) : ℝ) : ℂ)) with hu
  have hu1 : ‖u‖ = 1 := Complex.norm_exp_I_mul_ofReal _
  set k : G → ℂ := fun g => Complex.exp (Complex.I * (((s - s') * H g : ℝ) : ℂ)) * h g with hk
  have hdiff : u * conv μ f k x - conv μ f h x
      = ∫ g, (u * (f g * k (g⁻¹ * x)) - f g * h (g⁻¹ * x)) ∂μ := by
    rw [integral_sub ((hint ht).const_mul u) (hint hh), integral_const_mul]
    rfl
  have hpt : ∀ g, ‖u * (f g * k (g⁻¹ * x)) - f g * h (g⁻¹ * x)‖
      ≤ C * (δ * (|c| + 1) * ‖f g‖ + 2 * Dᶜ.indicator (fun g => ‖f g‖) g) := by
    intro g
    have e : u * (f g * k (g⁻¹ * x)) - f g * h (g⁻¹ * x)
        = h (g⁻¹ * x) * ((Complex.exp (Complex.I * (((s - s') * (H (g⁻¹ * x) - H x) : ℝ) : ℂ)) - 1) * f g) := by
      have : Complex.exp (Complex.I * (((s - s') * (H (g⁻¹ * x) - H x) : ℝ) : ℂ))
          = u * Complex.exp (Complex.I * (((s - s') * H (g⁻¹ * x) : ℝ) : ℂ)) := by
        rw [hu, ← Complex.exp_add]; congr 1; push_cast; ring
      rw [this, hk]; ring
    rw [e, norm_mul, norm_mul]
    refine mul_le_mul (hh.2.1 _) ?_ (by positivity) hC
    by_cases hg : g ∈ D
    · have h2 := Real.norm_exp_I_mul_ofReal_sub_one_le (x := (s - s') * (H (g⁻¹ * x) - H x))
      have h3 : ‖(s - s') * (H (g⁻¹ * x) - H x)‖ ≤ δ * (|c| + 1) := by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul hs.le ((hc g hg x).trans (by linarith [le_abs_self c])) (abs_nonneg _) hδ0.le
      have h4 : Dᶜ.indicator (fun g => ‖f g‖) g = 0 := by simp [hg]
      rw [h4, mul_zero, add_zero]
      exact mul_le_mul_of_nonneg_right (h2.trans h3) (norm_nonneg _)
    · have h2 : ‖Complex.exp (Complex.I * (((s - s') * (H (g⁻¹ * x) - H x) : ℝ) : ℂ)) - 1‖ ≤ 2 := by
        refine (norm_sub_le _ _).trans ?_
        rw [Complex.norm_exp_I_mul_ofReal, norm_one]; norm_num
      have h4 : Dᶜ.indicator (fun g => ‖f g‖) g = ‖f g‖ := by simp [hg]
      rw [h4]
      have h5 := mul_le_mul_of_nonneg_right h2 (norm_nonneg (f g))
      have h6 : 0 ≤ δ * (|c| + 1) * ‖f g‖ := by positivity
      linarith
  have hi1 : Integrable (fun g => δ * (|c| + 1) * ‖f g‖) μ := hf.norm.const_mul _
  have hi2 : Integrable (fun g => 2 * Dᶜ.indicator (fun g => ‖f g‖) g) μ :=
    (hf.norm.indicator hmD).const_mul _
  have hb : ‖u * conv μ f k x - conv μ f h x‖ ≤ C * ε := by
    rw [hdiff]
    refine (norm_integral_le_of_norm_le ((hi1.add hi2).const_mul C) (Eventually.of_forall hpt)).trans ?_
    simp only [Pi.add_apply]
    rw [integral_const_mul, integral_add hi1 hi2, integral_const_mul, integral_const_mul, ← hA]
    refine mul_le_mul_of_nonneg_left ?_ hC
    have : 0 ≤ δ * (|c| + 1) := by positivity
    nlinarith
  have h2 : ‖u * conv μ f k x‖ ≤ r * C := by rw [norm_mul, hu1, one_mul]; exact h1
  have h3 : ‖conv μ f h x‖ ≤ ‖u * conv μ f k x‖ + ‖u * conv μ f k x - conv μ f h x‖ := by
    simpa using norm_sub_le (u * conv μ f k x) (u * conv μ f k x - conv μ f h x)
  linarith
end

open MeasureTheory Filter UpperTheory.Lit.Cusp
open scoped Topology

theorem UpperTheory.Lit.Cusp.kills_of_idem :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (N : Set G) (a : ℝ → G) (H : G → ℝ) (e : G → ℂ),
      IsRay N a H → Continuous e → Integrable e μ → (∀ x, conv μ e e x = e x) → Kills μ N a e := by
  intro G _ _ _ _ _ _ _ _ μ _ N a H e hR hc hi hid
  have step1 : ∀ s, OpLe μ N a e s (1 / 2) → OpLe μ N a e s 0 := by
    intro s hs
    have hk : ∀ k : ℕ, OpLe μ N a e s ((1 / 2) ^ (k + 1)) := by
      intro k
      induction k with
      | zero => simpa using hs
      | succ k ih =>
        intro C h hh x
        have h1 := conv_isEig G μ N a e h s C hi hh
        have h2 : IsEig N a s (1 / 2 * C) (conv μ e h) := ⟨h1.1, hs C h hh, h1.2.2.1, h1.2.2.2⟩
        have h3 := ih _ _ h2 x
        rw [← conv_assoc G μ e e h C hc hi hc hi hh.1 hh.2.1 hid x] at h3
        calc _ ≤ _ := h3
          _ = _ := by ring
    intro C h hh x
    have ht : Tendsto (fun k : ℕ => ((1 / 2 : ℝ) ^ (k + 1)) * C) atTop (𝓝 (0 * C)) :=
      ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
        (tendsto_add_atTop_nat 1)).mul_const C
    exact ge_of_tendsto' ht (fun k => hk k C h hh x)
  obtain ⟨δ, hδ, hnear⟩ := opLe_near G μ N a H e hR hi (1 / 2) (by norm_num)
  have step2 : ∀ s s', |s - s'| < δ → OpLe μ N a e s 0 → OpLe μ N a e s' 0 := by
    intro s s' hss hs
    have := hnear s s' 0 hss hs
    rw [zero_add] at this
    exact step1 s' this
  obtain ⟨s₀, hs₀⟩ := opLe_half G μ N a H e hR hi
  have h0 := step1 s₀ hs₀
  have step3 : ∀ n : ℕ, ∀ s, |s - s₀| ≤ n * (δ / 2) → OpLe μ N a e s 0 := by
    intro n
    induction n with
    | zero =>
      intro s hs
      have : s = s₀ := by
        have : |s - s₀| ≤ 0 := by simpa using hs
        linarith [abs_nonpos_iff.mp this]
      rw [this]; exact h0
    | succ n ih =>
      intro s hs
      have hn : (0 : ℝ) ≤ n * (δ / 2) := by positivity
      push_cast at hs
      rw [abs_le] at hs
      by_cases h1 : |s - s₀| ≤ n * (δ / 2)
      · exact ih s h1
      · rcases le_total s s₀ with h2 | h2
        · refine step2 (s₀ - n * (δ / 2)) s ?_ (ih _ ?_)
          · rw [abs_of_nonpos (by linarith), not_le] at h1
            rw [abs_lt]; constructor <;> nlinarith
          · rw [abs_le]; constructor <;> linarith
        · refine step2 (s₀ + n * (δ / 2)) s ?_ (ih _ ?_)
          · rw [abs_of_nonneg (by linarith), not_le] at h1
            rw [abs_lt]; constructor <;> nlinarith
          · rw [abs_le]; constructor <;> linarith
  intro s C h hh x
  obtain ⟨n, hn⟩ := exists_nat_ge (|s - s₀| / (δ / 2))
  rw [div_le_iff₀ (by positivity)] at hn
  have := step3 n s hn C h hh x
  rw [zero_mul] at this
  exact norm_le_zero_iff.mp this
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.Unfold
open MeasureTheory Filter UpperTheory.Lit.Cusp
open scoped Topology

theorem UpperTheory.Lit.Cusp.conv_average :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (N : Set G) (a : ℝ → G) (H : G → ℝ)
      (ν : Measure G) [IsFiniteMeasureOnCompacts ν], ν Nᶜ = 0 → (∀ m ∈ N, ν.map (fun x => m * x) = ν) →
      IsRay N a H → ∀ f ψ : G → ℂ, Continuous f → Integrable f μ → Continuous ψ → HasCompactSupport ψ → ∀ x,
        conv μ f (fun g => ∫ m, ψ (g * m) ∂ν) x = ∫ y, ψ y⁻¹ * ∫ m, f (x * m * y) ∂ν ∂μ := by
  intro G _ _ _ _ _ _ _ _ μ _ N a H ν _ hN hinv hray f ψ hf hfi hψ hψc x
  haveI : IsLocallyFiniteMeasure ν := inferInstance
  haveI : SigmaFinite ν := inferInstance
  have hn := isBand_of_compact G N a H ν hN hinv hray (fun g => ((‖ψ g‖ : ℝ) : ℂ))
    (Complex.continuous_ofReal.comp hψ.norm)
    (hψc.comp_left (g := fun z : ℂ => ((‖z‖ : ℝ) : ℂ)) (by simp))
  have hb := isBand_of_compact G N a H ν hN hinv hray ψ hψ hψc
  obtain ⟨⟨-, ⟨C, hC⟩, -, -⟩, -⟩ := hn
  have hC' : ∀ g, ∫ m, ‖ψ (g * m)‖ ∂ν ≤ C := by
    intro g
    have h := hC g
    simp only [integral_complex_ofReal, Complex.norm_real, Real.norm_eq_abs] at h
    exact (le_abs_self _).trans h
  have hc1 : Continuous (fun p : G × G => f p.1 * ψ (p.1⁻¹ * x * p.2)) := by fun_prop
  have h1 : Integrable (fun p : G × G => f p.1 * ψ (p.1⁻¹ * x * p.2)) (μ.prod ν) := by
    rw [integrable_prod_iff hc1.aestronglyMeasurable]
    refine ⟨Eventually.of_forall fun g => (hb.2 (g⁻¹ * x)).const_mul (f g), ?_⟩
    refine Integrable.mono' (hfi.norm.mul_const C)
      (hc1.norm.stronglyMeasurable.integral_prod_right' (ν := ν)).aestronglyMeasurable
      (Eventually.of_forall fun g => ?_)
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    simp only [norm_mul]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hC' _) (norm_nonneg _)
  have h2 := (integrable_prod_iff h1.swap.aestronglyMeasurable).1 h1.swap
  have key : ∀ m y : G, (x * m * y)⁻¹ * x * m = y⁻¹ := by
    intro m y; group
  have hc3 : Continuous (fun p : G × G => ψ p.2⁻¹ * f (x * p.1 * p.2)) := by fun_prop
  have h3 : Integrable (fun p : G × G => ψ p.2⁻¹ * f (x * p.1 * p.2)) (ν.prod μ) := by
    rw [integrable_prod_iff hc3.aestronglyMeasurable]
    refine ⟨h2.1.mono fun m hm => ?_, h2.2.congr (Eventually.of_forall fun m => ?_)⟩
    · have := hm.comp_mul_left (x * m)
      simpa only [Function.comp, Prod.swap, key, mul_comm (f _)] using this
    · have := integral_mul_left_eq_self (μ := μ) (fun g => ‖f g * ψ (g⁻¹ * x * m)‖) (x * m)
      simp only [key, mul_comm (f (x * m * _))] at this
      simpa only [Function.comp, Prod.swap] using this.symm
  calc conv μ f (fun g => ∫ m, ψ (g * m) ∂ν) x
      = ∫ g, ∫ m, f g * ψ (g⁻¹ * x * m) ∂ν ∂μ := by
        simp only [conv, integral_const_mul]
    _ = ∫ m, ∫ g, f g * ψ (g⁻¹ * x * m) ∂μ ∂ν := integral_integral_swap h1
    _ = ∫ m, ∫ y, ψ y⁻¹ * f (x * m * y) ∂μ ∂ν := by
        refine integral_congr_ae (Eventually.of_forall fun m => ?_)
        have := integral_mul_left_eq_self (μ := μ) (fun g => f g * ψ (g⁻¹ * x * m)) (x * m)
        simp only [key, mul_comm (f (x * m * _))] at this
        exact this.symm
    _ = ∫ y, ∫ m, ψ y⁻¹ * f (x * m * y) ∂ν ∂μ := integral_integral_swap h3
    _ = ∫ y, ψ y⁻¹ * ∫ m, f (x * m * y) ∂ν ∂μ := by
        simp only [integral_const_mul]
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.BandKill
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.EigBand
open MeasureTheory Filter UpperTheory.Lit.Cusp
open scoped Topology

theorem UpperTheory.Lit.Cusp.isEig_of_isBand :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] (N : Set G) (a : ℝ → G) (H : G → ℝ) (h : G → ℂ),
      IsRay N a H → IsBand N H h → ∀ s : ℝ, ∃ C : ℝ,
        IsEig N a s C (fun g => ∫ t : ℝ, Complex.exp (-((s * t : ℝ) * Complex.I)) * h (g * a t)) ∧
          ∀ g, Integrable (fun t : ℝ => h (g * a t)) ∧ ∫ t : ℝ, ‖h (g * a t)‖ ≤ C := by
  intro G _ _ _ _ _ _ N a H h hr hb s
  obtain ⟨hc, ⟨B, hB⟩, hN, ⟨R, hR⟩⟩ := hb
  have ha := hr.cont
  have hH := hr.contH
  have he1 : ∀ x : ℝ, ‖Complex.exp (-((x : ℂ) * Complex.I))‖ = 1 := fun x => by
    rw [← neg_mul, ← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I]
  have hsupp : ∀ g t, h (g * a t) ≠ 0 → |H g + t| ≤ R := fun g t hne => by
    have := hR _ hne
    rwa [hr.move] at this
  have hint : ∀ g, Integrable (fun t : ℝ => h (g * a t)) := by
    intro g
    refine Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_
    refine HasCompactSupport.intro (isCompact_Icc (a := -R - H g) (b := R - H g)) ?_
    intro t ht
    by_contra hne
    apply ht
    have := abs_le.mp (hsupp g t hne)
    constructor <;> linarith [this.1, this.2]
  have hbound : ∀ g, ∫ t : ℝ, ‖h (g * a t)‖ ≤ 2 * |R| * |B| := by
    intro g
    have hle : ∀ t, ‖h (g * a t)‖ ≤ (Set.Icc (-R - H g) (R - H g)).indicator (fun _ => |B|) t := by
      intro t
      by_cases hne : h (g * a t) = 0
      · rw [hne, norm_zero]
        exact Set.indicator_nonneg (fun _ _ => abs_nonneg _) _
      · have := abs_le.mp (hsupp g t hne)
        rw [Set.indicator_of_mem (by constructor <;> linarith [this.1, this.2])]
        exact (hB _).trans (le_abs_self B)
    refine (integral_mono (hint g).norm
      ((continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc) hle).trans ?_
    rw [integral_indicator_const _ measurableSet_Icc, smul_eq_mul, Real.volume_real_Icc]
    have h1 : max (R - H g - (-R - H g)) 0 ≤ 2 * |R| :=
      max_le (by linarith [le_abs_self R]) (by positivity)
    exact mul_le_mul_of_nonneg_right h1 (abs_nonneg B)
  have hshift : ∀ g, (∫ t : ℝ, Complex.exp (-((s * t : ℝ) * Complex.I)) * h (g * a t)) =
      Complex.exp (((s * H g : ℝ) : ℂ) * Complex.I) *
        ∫ t : ℝ, Complex.exp (-((s * t : ℝ) * Complex.I)) * h (g * a (t - H g)) := by
    intro g
    rw [← integral_const_mul]
    conv_lhs => rw [← integral_sub_right_eq_self _ (H g)]
    congr 1
    ext t
    rw [← mul_assoc, ← Complex.exp_add]
    congr 1
    congr 1
    push_cast
    ring
  have hΦ : Continuous fun g =>
      ∫ t : ℝ, Complex.exp (-((s * t : ℝ) * Complex.I)) * h (g * a (t - H g)) := by
    refine continuous_of_dominated (bound := (Set.Icc (-R) R).indicator (fun _ => |B|)) ?_ ?_ ?_ ?_
    · intro g
      exact (by fun_prop : Continuous fun t : ℝ =>
        Complex.exp (-((s * t : ℝ) * Complex.I)) * h (g * a (t - H g))).aestronglyMeasurable
    · intro g
      refine Eventually.of_forall fun t => ?_
      rw [norm_mul, he1, one_mul]
      by_cases hne : h (g * a (t - H g)) = 0
      · rw [hne, norm_zero]
        exact Set.indicator_nonneg (fun _ _ => abs_nonneg _) _
      · have := abs_le.mp (hsupp g _ hne)
        rw [Set.indicator_of_mem (by constructor <;> linarith [this.1, this.2])]
        exact (hB _).trans (le_abs_self B)
    · exact (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc
    · exact Eventually.of_forall fun t => by fun_prop
  refine ⟨2 * |R| * |B|, ⟨?_, ?_, ?_, ?_⟩, fun g => ⟨hint g, hbound g⟩⟩
  · rw [show (fun g => ∫ t : ℝ, Complex.exp (-((s * t : ℝ) * Complex.I)) * h (g * a t)) =
        fun g => Complex.exp (((s * H g : ℝ) : ℂ) * Complex.I) *
          ∫ t : ℝ, Complex.exp (-((s * t : ℝ) * Complex.I)) * h (g * a (t - H g)) from funext hshift]
    exact (Complex.continuous_exp.comp (by fun_prop)).mul hΦ
  · intro g
    refine (norm_integral_le_integral_norm _).trans (le_of_eq_of_le ?_ (hbound g))
    congr 1
    ext t
    rw [norm_mul, he1, one_mul]
  · intro g m hm
    beta_reduce
    congr 1
    ext t
    rw [show g * m * a t = g * a t * ((a t)⁻¹ * m * a t) by group, hN _ _ (hr.norm t m hm)]
  · intro g u
    beta_reduce
    rw [← integral_const_mul]
    conv_rhs => rw [← integral_add_left_eq_self _ u]
    congr 1
    ext t
    rw [mul_assoc g, ← hr.add, ← mul_assoc, ← Complex.exp_add]
    congr 1
    congr 1
    push_cast
    ring
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.Fourier
open MeasureTheory Filter UpperTheory.Lit.Cusp
open scoped Topology

open scoped FourierTransform in
theorem UpperTheory.Lit.Cusp.fourier_zero :
    ∀ u : ℝ → ℂ, Continuous u → Integrable u →
      (∀ s : ℝ, ∫ t : ℝ, Complex.exp (-((s * t : ℝ) * Complex.I)) * u t = 0) → ∀ t, u t = 0 := by
  intro u hc hi hz t
  have hF : 𝓕 u = 0 := by
    ext w
    rw [Real.fourier_real_eq_integral_exp_smul, Pi.zero_apply, ← hz (2 * Real.pi * w)]
    congr 1
    ext v
    rw [smul_eq_mul]
    congr 1
    congr 1
    push_cast
    ring
  have hinv := hc.fourierInv_fourier_eq hi (by rw [hF]; exact integrable_zero _ _ _)
  rw [← hinv, hF]
  simp [Real.fourierInv_eq]
end

open MeasureTheory Filter UpperTheory.Lit.Cusp
open scoped Topology

theorem UpperTheory.Lit.Cusp.conv_band :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (N : Set G) (a : ℝ → G) (H : G → ℝ) (f h : G → ℂ),
      IsRay N a H → Continuous f → Integrable f μ → Kills μ N a f → IsBand N H h → ∀ x, conv μ f h x = 0 := by
  intro G _ _ _ _ _ _ _ _ μ _ N a H f h hR hf hfi hK hB x
  have ha := hR.cont
  have hh : Continuous h := hB.1
  obtain ⟨B, hBd⟩ := hB.2.1
  obtain ⟨C, -, hC⟩ := isEig_of_isBand G N a H h hR hB 0
  have a0 : a 0 = 1 := by
    have := hR.add 0 0
    rw [add_zero] at this
    simpa using this
  have hFc : Continuous (fun p : G × ℝ => f p.1 * h (p.1⁻¹ * x * a p.2)) := by fun_prop
  have hF : Integrable (fun p : G × ℝ => f p.1 * h (p.1⁻¹ * x * a p.2)) (μ.prod volume) := by
    rw [integrable_prod_iff hFc.aestronglyMeasurable]
    refine ⟨Eventually.of_forall fun g => (hC (g⁻¹ * x)).1.const_mul (f g), ?_⟩
    refine Integrable.mono' (hfi.norm.mul_const C)
      (hFc.norm.aestronglyMeasurable.integral_prod_right') (Eventually.of_forall fun g => ?_)
    rw [Real.norm_of_nonneg (integral_nonneg fun t => norm_nonneg _)]
    simp only [norm_mul]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hC (g⁻¹ * x)).2 (norm_nonneg _)
  have huc : Continuous (fun t : ℝ => ∫ g, f g * h (g⁻¹ * x * a t) ∂μ) := by
    refine continuous_of_dominated (bound := fun g => ‖f g‖ * B) (fun t => ?_) (fun t => ?_)
      (hfi.norm.mul_const B) (Eventually.of_forall fun g => by fun_prop)
    · exact Continuous.aestronglyMeasurable (by fun_prop)
    · refine Eventually.of_forall fun g => ?_
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hBd _) (norm_nonneg _)
  have hui : Integrable (fun t : ℝ => ∫ g, f g * h (g⁻¹ * x * a t) ∂μ) := hF.integral_prod_right
  have key := fourier_zero _ huc hui (fun s => ?_) 0
  · simpa [a0, conv] using key
  obtain ⟨D, hE, -⟩ := isEig_of_isBand G N a H h hR hB s
  have h0 := hK s D _ hE x
  have hF' : Integrable (fun p : G × ℝ =>
      Complex.exp (-((s * p.2 : ℝ) * Complex.I)) * (f p.1 * h (p.1⁻¹ * x * a p.2))) (μ.prod volume) := by
    refine hF.bdd_mul (c := 1) (Continuous.aestronglyMeasurable (by fun_prop))
      (Eventually.of_forall fun p => ?_)
    rw [← neg_mul, ← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I]
  have hsw := integral_integral_swap (μ := μ) (ν := (volume : Measure ℝ))
    (f := fun g t => Complex.exp (-((s * t : ℝ) * Complex.I)) * (f g * h (g⁻¹ * x * a t))) hF'
  simp only [← integral_const_mul]
  rw [← hsw, ← h0, conv]
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  simp only [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  ring
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.EqZeroOfTest
open MeasureTheory Filter UpperTheory.Lit.Cusp
open scoped Topology

theorem UpperTheory.Lit.Cusp.eq_zero_of_test :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (F : G → ℂ), Continuous F →
      (∀ ψ : G → ℂ, Continuous ψ → HasCompactSupport ψ → ∫ y, ψ y⁻¹ * F y ∂μ = 0) → ∀ y, F y = 0 := by
  intro G _ _ _ _ _ _ _ _ μ _ F hF h y₀
  by_contra hy
  obtain ⟨χ, hχc, hχ0, hχy⟩ := exists_continuous_nonneg_pos y₀
  have hχcont : Continuous (fun y => χ y) := χ.continuous
  have hc1 : Continuous (fun y => (χ y : ℂ) * (starRingEnd ℂ) (F y)) :=
    (Complex.continuous_ofReal.comp hχcont).mul (Complex.continuous_conj.comp hF)
  have hs0 : HasCompactSupport (fun y => (χ y : ℂ)) :=
    hχc.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
  have hs1 : HasCompactSupport (fun y => (χ y : ℂ) * (starRingEnd ℂ) (F y)) :=
    hs0.mul_right (f' := fun y => (starRingEnd ℂ) (F y))
  have h1 := h (fun z => (χ z⁻¹ : ℂ) * (starRingEnd ℂ) (F z⁻¹)) (hc1.comp continuous_inv)
    (hs1.comp_homeomorph (Homeomorph.inv G))
  have h2 : ∀ y, (χ y⁻¹⁻¹ : ℂ) * (starRingEnd ℂ) (F y⁻¹⁻¹) * F y
      = ((χ y * ‖F y‖ ^ 2 : ℝ) : ℂ) := by
    intro y
    rw [inv_inv, mul_assoc, Complex.conj_mul']
    push_cast
    rfl
  simp only [h2] at h1
  rw [integral_complex_ofReal, Complex.ofReal_eq_zero] at h1
  have hc2 : Continuous (fun y => χ y * ‖F y‖ ^ 2) := hχcont.mul (hF.norm.pow 2)
  have hs2 : HasCompactSupport (fun y => χ y * ‖F y‖ ^ 2) :=
    hχc.mul_right (f' := fun y => ‖F y‖ ^ 2)
  have hpos := hc2.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := μ) (x := y₀) hs2
    (fun y => mul_nonneg (hχ0 y) (sq_nonneg _))
    (mul_ne_zero hχy (pow_ne_zero 2 (norm_ne_zero_iff.mpr hy)))
  exact hpos.ne' h1
end

open MeasureTheory Filter UpperTheory.Lit.Cusp
open scoped Topology

theorem UpperTheory.Lit.Cusp.average_eq_zero :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (N : Set G) (a : ℝ → G) (H : G → ℝ)
      (ν : Measure G) [IsFiniteMeasureOnCompacts ν], ν Nᶜ = 0 → (∀ m ∈ N, ν.map (fun x => m * x) = ν) →
      IsRay N a H → ∀ e f : G → ℂ, Continuous e → Integrable e μ → Continuous f → Integrable f μ →
        (∀ x, conv μ e e x = e x) → (∀ x, conv μ e f x = f x) →
        ∀ x, (Continuous fun y => ∫ m, f (x * m * y) ∂ν) → ∀ y, ∫ m, f (x * m * y) ∂ν = 0 := by
  intro G _ _ _ _ _ _ _ _ μ _ N a H ν _ hν hinv hray e f hec hei hfc hfi hee hef x hcont
  have hKe : Kills μ N a e := kills_of_idem G μ N a H e hray hec hei hee
  have hKf : Kills μ N a f := by
    intro s C h hh z
    rw [conv_assoc G μ e f h C hec hei hfc hfi hh.1 hh.2.1 hef z]
    exact hKe s _ _ (conv_isEig G μ N a f h s C hfi hh) z
  refine eq_zero_of_test G μ (fun y => ∫ m, f (x * m * y) ∂ν) hcont ?_
  intro ψ hψ hψc
  rw [← conv_average G μ N a H ν hν hinv hray f ψ hfc hfi hψ hψc x]
  exact conv_band G μ N a H f _ hray hfc hfi hKf
    (isBand_of_compact G N a H ν hν hinv hray ψ hψ hψc).1 x
end

open MeasureTheory Filter Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.FlagMeas GlobalTheory.RealInd UpperTheory.Lit.Cusp
open GlobalTheory.Dec (IsHaarSub IsIsoC NW IsSqIntIrr)
open scoped Topology InnerProductSpace

theorem UpperTheory.Lit.Cusp.integral_coef_eq_zero :
    ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsSqIntIrr ε σ → ∀ v a : H,
        Decays (coefOn (ε := ε) σ v v) → Decays (coefOn (ε := ε) σ a v) →
        ∀ W, IsIsoC ε W → ∀ ν : Measure (UJ ε), IsHaarSub (NW ε W) ν → ∀ x y : UJ ε,
          ∫ m, ⟪v, σ (umat (x * m * y)) a⟫_ℂ ∂ν = 0 := by
  intro n ε H _ _ σ hσ v a hvv hav W hW ν hν x y
  obtain ⟨hc, hn, hU, hI, hS⟩ := hσ
  obtain ⟨d, hd⟩ := GlobalTheory.T.schur_orthogonality_indefiniteUnitaryGroup n ε H σ hU hI hS
  have hd0 : 0 < d := hd.1
  by_cases hv : v = 0
  · subst hv
    simp
  have hv2 : (‖v‖ : ℝ) ^ 2 ≠ 0 := by positivity
  obtain ⟨hcvv, hconvvv⟩ := conv_coef n ε H σ d hU hd v v
  obtain ⟨hcav, hconvav⟩ := conv_coef n ε H σ d hU hd v a
  obtain ⟨hivv, -⟩ := continuous_average n ε _ hcvv hvv
  obtain ⟨hiav, hcontav⟩ := continuous_average n ε _ hcav hav
  obtain ⟨hν0, hνf, hνN, hνinv⟩ := hν
  haveI := hνf
  obtain ⟨hflag, h1, hNeq, S, hS⟩ := flagN_eq_NW n ε W hW
  obtain ⟨r, Hr, hr⟩ := exists_isRay n ε _ _ hflag (fun i => by fin_cases i; simpa using h1)
  rw [hNeq] at hr
  set k : ℂ := ((d / ‖v‖ ^ 2 : ℝ) : ℂ) with hk
  have hkc : k * ((‖v‖ ^ 2 / d : ℝ) : ℂ) = 1 := by
    rw [hk, ← Complex.ofReal_mul]
    rw [div_mul_div_comm, mul_comm d, div_self (mul_ne_zero hv2 hd0.ne')]
    simp
  have key := average_eq_zero (UJ ε) (muG ε) (NW ε W) r Hr ν hνN hνinv hr
    (fun g => k * coefOn σ v v g) (coefOn σ a v)
    (continuous_const.mul hcvv) (hivv.const_mul k) hcav hiav
    (by
      intro z
      simp only [conv] at hconvvv ⊢
      have := hconvvv z
      simp only [mul_assoc]
      rw [show (fun g => k * (coefOn σ v v g * (k * coefOn σ v v (g⁻¹ * z))))
          = fun g => (k * k) * (coefOn σ v v g * coefOn σ v v (g⁻¹ * z)) by
            funext g; ring]
      rw [MeasureTheory.integral_const_mul, this]
      linear_combination (k * coefOn σ v v z) * hkc)
    (by
      intro z
      simp only [conv] at hconvav ⊢
      have := hconvav z
      simp only [mul_assoc]
      rw [MeasureTheory.integral_const_mul, this]
      linear_combination (coefOn σ a v z) * hkc)
    x (hcontav S ν (by rw [hS]; exact ⟨hν0, hνf, hνN, hνinv⟩) x) y
  exact key
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace UpperTheory.Lit.Cusp

open GlobalTheory.FibreAtTau

theorem decays_of_decayAt {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) (v a : M.H τ)
    (h : DecayAt M τ v a (2 * V.rank ^ 2 + 1)) : Decays (Formalism.MainNotions.S.coefOn (ε := M.ε τ) (M.σ τ) a v) := by
  obtain ⟨C, hC⟩ := h
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  obtain ⟨-, hmul, -, -⟩ := isCompact_ball V.rank (M.ε τ)
  set c : ℝ := 1 + Real.sqrt (Formalism.REAL.hs (M.fr τ)) * Real.sqrt (Formalism.REAL.hs (M.fr τ)⁻¹) with hc
  refine ⟨c ^ (2 * V.rank ^ 2 + 1) * C, fun u => ?_⟩
  set g := (M.fr τ)⁻¹ * Formalism.MainNotions.S.umat u * M.fr τ with hg
  have hu : M.fr τ * g * (M.fr τ)⁻¹ = Formalism.MainNotions.S.umat u := by
    rw [hg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul,
      Matrix.mul_nonsing_inv_cancel_right _ _ hd]
  have hJ : (Formalism.MainNotions.S.umat u)ᴴ * Formalism.REAL.Jm (M.ε τ) * Formalism.MainNotions.S.umat u = Formalism.REAL.Jm (M.ε τ) := u.2
  have hfg : M.fr τ * g = Formalism.MainNotions.S.umat u * M.fr τ := by
    rw [hg, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hd]
  have hmem : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
    show gᴴ * gramAt D V τ * g = gramAt D V τ
    rw [← M.fr_gram τ]
    calc gᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) * g
        = (M.fr τ * g)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * g) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (M.fr τ)ᴴ * ((Formalism.MainNotions.S.umat u)ᴴ * Formalism.REAL.Jm (M.ε τ) * Formalism.MainNotions.S.umat u) * M.fr τ := by
          rw [hfg]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hJ]
  have h1 := hC g hmem
  have he : M.rep τ g = M.σ τ (Formalism.MainNotions.S.umat u) := by rw [DSModel.rep, hu]
  rw [he] at h1
  have hn : Real.sqrt (Formalism.REAL.hs (Formalism.MainNotions.S.umat u)) ≤
      Real.sqrt (Formalism.REAL.hs (M.fr τ)) * hsn g * Real.sqrt (Formalism.REAL.hs (M.fr τ)⁻¹) := by
    rw [← hu]
    exact (hmul _ _).trans (mul_le_mul_of_nonneg_right (hmul _ _) (Real.sqrt_nonneg _))
  have h0 : 0 ≤ hsn g := Real.sqrt_nonneg _
  have hp : 0 ≤ Real.sqrt (Formalism.REAL.hs (M.fr τ)) * Real.sqrt (Formalism.REAL.hs (M.fr τ)⁻¹) := by positivity
  have h2 : 1 + Real.sqrt (Formalism.REAL.hs (Formalism.MainNotions.S.umat u)) ≤ c * (1 + hsn g) := by rw [hc]; nlinarith
  have h3 : wt u ≤ c ^ (2 * V.rank ^ 2 + 1) * (1 + hsn g) ^ (2 * V.rank ^ 2 + 1) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) h2 _
  calc _ ≤ ‖⟪v, M.σ τ (Formalism.MainNotions.S.umat u) a⟫_ℂ‖ * (c ^ (2 * V.rank ^ 2 + 1) * (1 + hsn g) ^ (2 * V.rank ^ 2 + 1)) :=
        mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
    _ = c ^ (2 * V.rank ^ 2 + 1) * (‖⟪v, M.σ τ (Formalism.MainNotions.S.umat u) a⟫_ℂ‖ * (1 + hsn g) ^ (2 * V.rank ^ 2 + 1)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)

theorem fibre_integral_eq_zero : ∀ (D : D7) (θ : InfFam D), IsInfFam θ →
    ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D)))
    (v a : ∀ τ, M.H τ), (∀ τ, DecayAt M τ (v τ) (v τ) (2 * V.rank ^ 2 + 1)) → (∀ τ, DecayAt M τ (v τ) (a τ) (2 * V.rank ^ 2 + 1)) →
    ∀ (τ : D.what₂.Tau) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E), IsIsoFrame V C →
    ∃ P Q : Subgroup (NI V C), IsClosed (P : Set (NI V C)) ∧ IsClosed (Q : Set (NI V C)) ∧
      (∀ p ∈ P, ∀ q ∈ Q, p * q = q * p) ∧ (∀ h, ∃ p ∈ P, ∃ q ∈ Q, h = p * q) ∧ (∀ h, h ∈ P → h ∈ Q → h = 1) ∧
      ∀ ν : Measure P, ν.IsHaarMeasure → ∀ q ∈ Q, ∀ x y : GA D V,
        ∫ p, coef θ M K v a (x * (((p : NI V C) * q : NI V C) : GA D V) * y) ∂ν = 0 := by
  intro D θ hθ V S M K v a hv ha τ r C hC
  refine ⟨atP θ V C τ, offP θ V C τ, (L_closed θ hθ V C τ).1, (L_closed θ hθ V C τ).2, (L_comm θ hθ V C τ).1,
    L_decomp θ hθ V C hC τ, (L_comm θ hθ V C τ).2, ?_⟩
  intro ν hν q hq x y
  haveI : BorelSpace (GA D V) := ⟨rfl⟩
  haveI : BorelSpace (Formalism.REAL.UJ (M.ε τ)) := ⟨rfl⟩
  obtain ⟨E, hE⟩ := L_hom θ hθ V S M τ
  obtain ⟨W, hW, hemb, hrange⟩ := L_emb θ hθ V S M τ C hC E hE
  obtain ⟨R, hR⟩ := L_factor θ hθ V S M K v a τ C q hq x y
  let ι : atP θ V C τ →* Formalism.REAL.UJ (M.ε τ) := E.comp ((NI V C).subtype.comp (atP θ V C τ).subtype)
  have hι : Topology.IsClosedEmbedding ι := hemb
  have hmap := isHaarSub_map_closedEmb ι hι ⊤ isClosed_univ ν (isHaarSub_top ν)
  have hr : (((⊤ : Subgroup (atP θ V C τ)).map ι : Subgroup _) : Set _) = GlobalTheory.Dec.NW (M.ε τ) W := by
    rw [← MonoidHom.range_eq_map, MonoidHom.coe_range]
    exact hrange
  rw [hr] at hmap
  have hsq : GlobalTheory.Dec.IsSqIntIrr (M.ε τ) (M.σ τ) := by
    have hDS := M.ds τ
    exact ⟨hDS.1, hDS.2.1, hDS.2.2.1, hDS.2.2.2.1, hDS.2.2.2.2.1⟩
  have h0 := integral_coef_eq_zero V.rank (M.ε τ) (M.H τ) (M.σ τ) hsq (v τ) (a τ)
    (decays_of_decayAt M τ _ _ (hv τ)) (decays_of_decayAt M τ _ _ (ha τ)) W hW (ν.map ι) hmap (E x) (E y)
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have key : ∀ p : atP θ V C τ, coef θ M K v a (x * (((p : NI V C) * q : NI V C) : GA D V) * y) =
      ⟪v τ, M.σ τ (Formalism.MainNotions.S.umat (E x * ι p * E y)) (a τ)⟫_ℂ * R := by
    intro p
    rw [hR p p.2]
    congr 2
    show M.σ τ (M.fr τ * _ * (M.fr τ)⁻¹) (a τ) = M.σ τ _ (a τ)
    congr 2
    change M.fr τ * _ * (M.fr τ)⁻¹ = Formalism.MainNotions.S.umat (E x) * Formalism.MainNotions.S.umat (E ((p : NI V C) : GA D V)) * Formalism.MainNotions.S.umat (E y)
    rw [hE, hE, hE]
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hd]
  simp_rw [key]
  have hint := hι.measurableEmbedding.integral_map (μ := ν)
    (fun m => ⟪v τ, M.σ τ (Formalism.MainNotions.S.umat (E x * m * E y)) (a τ)⟫_ℂ)
  rw [integral_mul_const, ← hint, h0, zero_mul]

end UpperTheory.Lit.Cusp
