module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FinMuOfFiniteCovolume
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.NormBcharMulNfacRmul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivityHolds
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.WeightedHeightSupDriftOrthonormalFrames
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsSubspaceHeightGramDeterminant

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.KronHolPsiOf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.KronAssembly

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem chi_ne_zero {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) :
    X.χ la γ ≠ 0 := by
  obtain ⟨n, hn, h⟩ := X.χ_fin la
  intro h0
  have := h γ hγ
  rw [h0, zero_pow hn.ne'] at this
  exact zero_ne_one this

theorem exists_orth {r : ℕ} (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) {γ : GL (Fin r) E}
    (hγ : γ ∈ X.Γ) : ∃ x1, IsOrth X x1 ∧ ∃ b ∈ Bor X.Ψ r, ∃ b' ∈ Bor X.Ψ r,
      lact γ x = rmul x1 b ∧ x1 = lact γ (rmul x b') := by
  obtain ⟨x1, ho, b, hb, h⟩ := ortho_holds r X (lact γ x) (OntoS.dom_lact X hγ hx)
  refine ⟨x1, ho, b, hb, ExtFPf.invF X b, ExtFPf.invF_mem X hb, h, ?_⟩
  rw [FundSetPf.lact_rmul, h, ExtFPf.rmul_assoc, ExtFPf.rmul_invF X hb, ExtFPf.rmul_oneF]

theorem sec_ne_zero {r : ℕ} (X : Data E r) {L : Wt X.Ψ r} {w : Frame X.Ψ r → ℂ} (hw : X.IsSec L w)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) (h : w x ≠ 0) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ)
    {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) : w (lact γ (rmul x b)) ≠ 0 := by
  rw [hw.2.2 γ hγ _ (OntoS.dom_rmul X hx hb), hw.2.1 x hx b hb]
  exact mul_ne_zero (chi_ne_zero X L hγ) (mul_ne_zero (OntoE.bchar_ne X L hb) h)

end GlobalTheory.KronAssembly
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.PhlaBlockWtCpt
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.CurvMargin

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def blockWt {r : ℕ} (X : Data E r) : Wt X.Ψ r := fun _ i => if (i : ℕ) < X.p0 then 0 else 1

theorem tele_tail (L : ℕ → ℝ) (p : ℕ) : ∀ r : ℕ, p ≤ r →
    ∑ i ∈ Finset.range r, (if i < p then (0 : ℝ) else 1) * (L (i + 1) - L i) = L r - L p := by
  intro r hr
  induction r, hr using Nat.le_induction with
  | base =>
    rw [sub_self]
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [if_pos (Finset.mem_range.1 hi), zero_mul]
  | succ n hn ih =>
    rw [Finset.sum_range_succ, ih, if_neg (not_lt.2 hn)]
    ring

theorem phla_blockWt_cpt {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) (ho : IsOrth X x0)
    {z : V (nd X)} (hz : z ∈ OmF X x0) :
    phla X (blockWt X) (cpt X x0 z) = rhF X x0 z := by
  rw [IW.phla_eq X hz, rhF, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  set x := cpt X x0 z
  let L' : ℕ → ℝ := fun k => if h : k < r + 1 then IW.Lm X x τ ⟨k, h⟩ else 0
  have h1 : ∀ i : Fin r, IW.Lm X x τ i.succ = L' (i + 1) := fun i => by
    simp only [L', dif_pos (Nat.succ_lt_succ i.isLt)]; rfl
  have h2 : ∀ i : Fin r, IW.Lm X x τ i.castSucc = L' i := fun i => by
    simp only [L', dif_pos (Nat.lt_succ_of_lt i.isLt)]; rfl
  have hk : ∀ i : Fin r, ((blockWt X τ i : ℤ) : ℝ) = if (i : ℕ) < X.p0 then (0 : ℝ) else 1 :=
    fun i => by unfold blockWt; split_ifs <;> simp
  have hLr : L' r = 0 := by
    simp only [L', dif_pos (Nat.lt_succ_self r)]; exact IW.Lm_last_cpt X x0 ho z τ
  have hLp : L' X.p0 = Real.log ‖dmin X.Gm x τ ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩‖ := by
    simp only [L', dif_pos (Nat.lt_succ_of_le X.p0_le)]; rfl
  simp_rw [h1, h2, hk]
  rw [Fin.sum_univ_eq_sum_range
    (fun i => (if i < X.p0 then (0 : ℝ) else 1) * (L' (i + 1) - L' i)) r, tele_tail L' X.p0 r X.p0_le,
    hLr, hLp, zero_sub]

theorem leviRh_eq {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) (ho : IsOrth X x0)
    {z : V (nd X)} (hz : z ∈ OmF X x0) (ξ : Fin (nd X) → ℂ) :
    leviRh X x0 z ξ = leviM X (phla X (blockWt X)) x0 z ξ := by
  have hev : (fun w => ((rhF X x0 w : ℝ) : ℂ)) =ᶠ[𝓝 z]
      fun w => ((phla X (blockWt X) (cpt X x0 w) : ℝ) : ℂ) := by
    filter_upwards [(ExF.isOpen_OmF X x0).mem_nhds hz] with w hw
    rw [phla_blockWt_cpt X x0 ho hw]
  unfold leviRh leviM
  rw [leviV_congr hev]

theorem coeff_cases (p : ℕ) {a b : ℕ} (h : b < a) (u v : ℝ) :
    (a < p ∧ sgn p a * sgn p b * (v - u) = v - u) ∨
    (p ≤ b ∧ sgn p a * sgn p b * (v - u) = v - u) ∨
    (b < p ∧ p ≤ a ∧ sgn p a * sgn p b * (v - u) = u - v) := by
  unfold sgn
  by_cases ha : a < p
  · left; refine ⟨ha, ?_⟩; rw [if_pos ha, if_pos (h.trans ha)]; ring
  · by_cases hb : b < p
    · right; right; refine ⟨hb, not_lt.1 ha, ?_⟩; rw [if_neg ha, if_pos hb]; ring
    · right; left; refine ⟨not_lt.1 hb, ?_⟩; rw [if_neg ha, if_neg hb]; ring

theorem curv_and_margin :
    (∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (x : Frame X.Ψ r), IsOrth X x → ∀ ξ : Fin (nd X) → ℂ, leviM X (phla X la) x 0 ξ = ∑ e : Ent X, sgn X.p0 e.2.1.1 * sgn X.p0 e.2.1.2 * ((la e.1 e.2.1.2 : ℝ) - (la e.1 e.2.1.1 : ℝ)) * ‖ξ (Fintype.equivFin (Ent X) e)‖ ^ 2) →
    (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r) (z : V (nd X)), cpt X x0 z ∈ X.dom → ∃ (x1 : Frame X.Ψ r) (D : (Fin (nd X) → ℂ) →ₗ[ℂ] (Fin (nd X) → ℂ)), IsOrth X x1 ∧ Function.Injective D ∧ ∀ (la : Wt X.Ψ r) (ξ : Fin (nd X) → ℂ), leviM X (phla X la) x0 z ξ = leviM X (phla X la) x1 0 (D ξ)) →
    ((CurvGGStatement (E := E)) ∧ (∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (m : ℝ), (∀ τ (i j : Fin r), i ≤ j → (j : ℕ) < X.p0 → la τ j ≤ la τ i) → (∀ τ (i j : Fin r), X.p0 ≤ (i : ℕ) → i ≤ j → la τ j ≤ la τ i) → (∀ τ (i j : Fin r), (i : ℕ) < X.p0 → X.p0 ≤ (j : ℕ) → m ≤ (la τ j : ℝ) - (la τ i : ℝ)) → ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ, m * leviRh X x0 z ξ ≤ leviO X x0 (phla X la) z ξ)) := by
  intro hdiag htr
  refine ⟨fun r X la x0 z hz => ⟨fun hd ξ => ?_, fun hd ξ hξ => ?_⟩, ?_⟩
  · obtain ⟨x1, D, ho, -, hD⟩ := htr r X x0 z hz
    show 0 ≤ leviM X (phla X la) x0 z ξ
    rw [hD, hdiag r X la x1 ho]
    refine Finset.sum_nonneg fun e _ => mul_nonneg ?_ (by positivity)
    obtain ⟨τ, ⟨a, b⟩, hab⟩ := e
    obtain ⟨h1, h2, h3⟩ := hd τ
    have hab' : (b : ℕ) < a := hab
    rcases coeff_cases X.p0 hab' (la τ a : ℝ) (la τ b : ℝ) with ⟨h, e⟩ | ⟨h, e⟩ | ⟨h, h', e⟩
    · refine le_of_le_of_eq ?_ e.symm
      exact sub_nonneg.2 (Int.cast_le.2 (h1 b a (le_of_lt hab) h))
    · refine le_of_le_of_eq ?_ e.symm
      exact sub_nonneg.2 (Int.cast_le.2 (h2 b a h (le_of_lt hab)))
    · refine le_of_le_of_eq ?_ e.symm
      exact sub_nonneg.2 (Int.cast_le.2 (h3 b a h h'))
  · obtain ⟨x1, D, ho, hinj, hD⟩ := htr r X x0 z hz
    show 0 < leviM X (phla X la) x0 z ξ
    rw [hD, hdiag r X la x1 ho]
    have hpos : ∀ e : Ent X, 0 < sgn X.p0 e.2.1.1 * sgn X.p0 e.2.1.2 *
        ((la e.1 e.2.1.2 : ℝ) - (la e.1 e.2.1.1 : ℝ)) := by
      intro e
      obtain ⟨τ, ⟨a, b⟩, hab⟩ := e
      obtain ⟨h1, h2, h3⟩ := hd τ
      have hab' : (b : ℕ) < a := hab
      rcases coeff_cases X.p0 hab' (la τ a : ℝ) (la τ b : ℝ) with ⟨h, e⟩ | ⟨h, e⟩ | ⟨h, h', e⟩
      · refine lt_of_lt_of_eq ?_ e.symm
        exact sub_pos.2 (Int.cast_lt.2 (h1 b a hab h))
      · refine lt_of_lt_of_eq ?_ e.symm
        exact sub_pos.2 (Int.cast_lt.2 (h2 b a h hab))
      · refine lt_of_lt_of_eq ?_ e.symm
        exact sub_pos.2 (Int.cast_lt.2 (h3 b a h h'))
    have hne : D ξ ≠ 0 := fun h => hξ (hinj (h.trans (map_zero D).symm))
    obtain ⟨k, hk⟩ := Function.ne_iff.1 hne
    refine Finset.sum_pos' (fun e _ => mul_nonneg (hpos e).le (by positivity))
      ⟨(Fintype.equivFin (Ent X)).symm k, Finset.mem_univ _, mul_pos (hpos _) ?_⟩
    have hkk : (Fintype.equivFin (Ent X)) ((Fintype.equivFin (Ent X)).symm k) = k :=
      Equiv.apply_symm_apply (Fintype.equivFin (Ent X)) k
    refine pow_pos (norm_pos_iff.2 fun h => hk ?_) 2
    exact (congrArg (D ξ) hkk).symm.trans h
  · intro r X la m h1 h2 h3 x0 ho z hz ξ
    obtain ⟨x1, D, ho1, -, hD⟩ := htr r X x0 z hz
    rw [leviRh_eq X x0 ho hz, leviO, hD, hD, hdiag r X la x1 ho1, hdiag r X _ x1 ho1,
      Finset.mul_sum]
    refine Finset.sum_le_sum fun e _ => ?_
    rw [← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    obtain ⟨τ, ⟨a, b⟩, hab⟩ := e
    have hab' : (b : ℕ) < a := hab
    show m * (sgn X.p0 a * sgn X.p0 b * ((blockWt X τ b : ℝ) - (blockWt X τ a : ℝ))) ≤
      sgn X.p0 a * sgn X.p0 b * ((la τ b : ℝ) - (la τ a : ℝ))
    rcases coeff_cases X.p0 hab' (la τ a : ℝ) (la τ b : ℝ) with ⟨h, e⟩ | ⟨h, e⟩ | ⟨h, h', e⟩
    · rw [e]
      have := sub_nonneg.2 (Int.cast_le (R := ℝ).2 (h1 τ b a (le_of_lt hab) h))
      simpa [blockWt, h, hab'.trans h] using this
    · rw [e]
      have := sub_nonneg.2 (Int.cast_le (R := ℝ).2 (h2 τ b a h (le_of_lt hab)))
      simpa [blockWt, not_lt.2 h, not_lt.2 (h.trans hab'.le)] using this
    · rw [e]
      have := h3 τ b a h h'
      simpa [blockWt, sgn, h, not_lt.2 h'] using this

end GlobalTheory.CurvMargin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsStabiliserImageSubgroup
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.FiniteCovolume

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def uStabSubgroup {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) :
    Subgroup (GL (Fin r) E) where
  carrier := {γ | IsUStab G Λ γ}
  one_mem' := by simp [IsUStab]
  mul_mem' := fun {γ δ} hγ hδ => by
    refine ⟨fun x y => ?_, fun x => ?_⟩
    · rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hγ.1, hδ.1]
    · rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← hγ.2, ← hδ.2]
  inv_mem' := fun h => isUStab_inv h

theorem _root_.GlobalTheory.FiniteCovolume.exists_stabiliser_image_subgroup :
    (∀ (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → ∃ Γ : Subgroup H, ∀ g : H, g ∈ Γ ↔ (∃ γ : GL (Fin r) E, _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab X.Gm X.Λ γ ∧ ∀ τ : X.Ψ, ((((g : H) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (γ : Matrix (Fin r) (Fin r) E).map τ.1)) := by
  intro r X H _
  refine ⟨((_root_.GlobalTheory.FiniteCovolume.uStabSubgroup X.Gm X.Λ).map (_root_.GlobalTheory.FiniteCovolume.embGL X.Ψ)).comap
    H.subtype, fun g => ?_⟩
  simp only [Subgroup.mem_comap, Subgroup.mem_map, Subgroup.coe_subtype]
  constructor
  · rintro ⟨γ, hγ, hg⟩
    refine ⟨γ, hγ, fun τ => ?_⟩
    rw [← hg, _root_.GlobalTheory.FiniteCovolume.embGL_val]
  · rintro ⟨γ, hγ, hg⟩
    refine ⟨γ, hγ, funext fun τ => Units.ext ?_⟩
    rw [_root_.GlobalTheory.FiniteCovolume.embGL_val, hg]

end GlobalTheory.FiniteCovolume
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.LintegralFundSetInterLe
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.Unfold

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem lintegral_fundSet_inter_le : MeasInvStatement (E := E) → ∀ (r : ℕ) (X : Data E r) (x0 x1 : Frame X.Ψ r), IsOrth X x0 → IsOrth X x1 →
    ∀ FF, IsFundSet X x0 FF → ∀ φ : Frame X.Ψ r → ℝ≥0∞, Measurable φ →
    (∀ γ ∈ X.Γ, ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (lact γ (rmul x b)) = φ x) →
    ∀ N : Set (V (nd X)), MeasurableSet N → N ⊆ OmF X x1 →
    ∫⁻ z in FF ∩ {z | ∃ y ∈ N, ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, cpt X x0 z = lact γ (rmul (cpt X x1 y) b)},
      φ (cpt X x0 z) ∂muF X x0 ≤ ∫⁻ y in N, φ (cpt X x1 y) ∂muF X x1 := by
  intro hM r X x0 x1 ho0 ho1 FF hF φ hφ hinv N hN hNO
  classical
  have := FundSetPf.countable_GL (E := E) (r := r)
  have hc : Measurable (cpt X x0) := (FundSetPf.cont_cpt X x0).measurable
  have hφB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul x b) = φ x := fun x hx b hb => by
    have h := hinv 1 X.Γ.one_mem x hx b hb
    rwa [FundSetPf.lact_one] at h
  let ψ : Frame X.Ψ r → ℝ≥0∞ := (satFrames X x1 N).indicator φ
  have hψ : Measurable ψ := hφ.indicator (measurableSet_satFrames X ho1 hN hNO)
  have hψB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, ψ (rmul x b) = ψ x := by
    intro x hx b hb
    simp only [ψ, Set.indicator, rmul_mem_satFrames_iff X x1 N _ hb, hφB x hx b hb]
  have h1 : ∫⁻ y in N, φ (cpt X x1 y) ∂muF X x1 = ∫⁻ y, ψ (cpt X x1 y) ∂muF X x1 := by
    rw [← lintegral_indicator hN]
    refine lintegral_congr fun z => ?_
    simp only [ψ, Set.indicator, cpt_mem_satFrames_iff X ho1]
  rw [h1, ← hM r X x0 x1 ho0 ho1 ψ hψ hψB, lintegral_unfold hM r X x0 ho0 FF hF ψ hψ hψB]
  refine le_trans (setLIntegral_mono (g := fun z => ∑' γ : X.Γ, ψ (lact γ.1 (cpt X x0 z))) ?_ ?_)
    (lintegral_mono_set Set.inter_subset_left)
  · exact Measurable.tsum fun γ => (hψ.comp (continuous_lact X γ.1).measurable).comp hc
  · rintro z ⟨-, y, hy, γ, hγ, b, hb, h⟩
    refine le_trans (le_of_eq ?_) (ENNReal.le_tsum (⟨γ⁻¹, X.Γ.inv_mem hγ⟩ : X.Γ))
    have hm : rmul (cpt X x1 y) b ∈ satFrames X x1 N := ⟨y, hy, b, hb, rfl⟩
    show φ (cpt X x0 z) = ψ (lact γ⁻¹ (cpt X x0 z))
    rw [h, FundSetPf.lact_inv, hinv γ hγ _ (hNO hy) b hb]
    show _ = (satFrames X x1 N).indicator φ _
    rw [Set.indicator_of_mem hm, hφB _ (hNO hy) b hb]

end GlobalTheory.Unfold
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.DminCptEq
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.OrthNear

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem _root_.GlobalTheory.OrthNear.isOrth_x0F {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.x0F X) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.x0F _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth
  intro τ
  generalize_proofs h
  exact (h τ).choose_spec.2

private theorem mat_cpt_eq_mat_mul_mat_nmat {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r)
    (z : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) (τ : X.Ψ) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) τ = _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nmat X z) τ := rfl

private theorem gram_mul_apply_eq_sum {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (M N : Matrix (Fin r) (Fin r) ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ G (M * N) = Matrix.of fun a b =>
      ∑ c, ∑ d, N c a * _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ G M c d * starRingEnd ℂ (N d b) := by
  have hcol : ∀ a, _root_.ReciprocityTheory.ChartRestriction.G.FD.col (M * N) a = ∑ c, N c a • _root_.ReciprocityTheory.ChartRestriction.G.FD.col M c := by
    intro a
    rw [← _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.mulVec_eq_sum_col]
    ext k
    simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  ext a b
  simp only [_root_.ReciprocityTheory.ChartRestriction.G.FD.gram, Matrix.of_apply, hcol, _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC_sum_left, _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC_sum_right, _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC_smul_left, _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC_smul_right, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring

private theorem gram_chartCoord_orthonormal_indep_lemma {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r)
    {x y : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} (hx : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x) (hy : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X y)
    (z : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) (τ : X.Ψ) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) τ) = _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X y z) τ) := by
  have hx' : _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) = _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat y τ) :=
    (hx τ).trans (hy τ).symm
  rw [mat_cpt_eq_mat_mul_mat_nmat, mat_cpt_eq_mat_mul_mat_nmat, gram_mul_apply_eq_sum, gram_mul_apply_eq_sum, hx']

theorem _root_.GlobalTheory.OrthNear.dmin_cpt_eq {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) {x y : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} (hx : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x) (hy : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X y)
    (z : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) (τ : X.Ψ) (i : Fin (r + 1)) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) τ i = _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X y z) τ i := by
  simp only [_root_.ReciprocityTheory.ChartRestriction.G.FD.dmin, gram_chartCoord_orthonormal_indep_lemma X hx hy z τ]

private theorem densF_eq_of_isOrth {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) {x y : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r}
    (hx : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x) (hy : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X y) (z : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) :
    _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.densF X x z = _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.densF X y z := by
  simp only [_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.densF, _root_.GlobalTheory.OrthNear.dmin_cpt_eq X hx hy z]

private theorem nfac_cpt_eq_of_isOrth {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) {x y : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r}
    (hx : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x) (hy : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X y) (la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (z : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) :
    X.nfac la (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) = X.nfac la (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X y z) := by
  simp only [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.nfac, _root_.GlobalTheory.OrthNear.dmin_cpt_eq X hx hy z]

private theorem cpt_mem_dom_iff_of_isOrth {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) {x y : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r}
    (hx : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x) (hy : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X y) (z : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) :
    _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z ∈ X.dom ↔ _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X y z ∈ X.dom := by
  have hdet : ∀ τ : X.Ψ, (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) τ).det ≠ 0 ↔
      (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X y z) τ).det ≠ 0 := by
    intro τ
    rw [mat_cpt_eq_mat_mul_mat_nmat, mat_cpt_eq_mat_mul_mat_nmat, Matrix.det_mul, Matrix.det_mul]
    simp [_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExF.det_ne_of_orth X hx τ, _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExF.det_ne_of_orth X hy τ]
  simp only [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.dom, _root_.ReciprocityTheory.ChartRestriction.G.FD.GG, Set.mem_setOf_eq, hdet,
    _root_.GlobalTheory.OrthNear.dmin_cpt_eq X hx hy z]

theorem _root_.GlobalTheory.OrthNear.orthNear : (∀ (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r), ∃ ρ c C : ℝ, 0 < ρ ∧ 0 < c ∧ ∀ x, _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → ∀ z : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X), ‖z‖ < ρ → _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z ∈ X.dom ∧ c ≤ _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.densF X x z ∧ _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.densF X x z ≤ C ∧ c ≤ X.nfac la (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) ∧ X.nfac la (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) ≤ C) := by
  intro r X la
  set x0 := _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.x0F X
  have h0 : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x0 := _root_.GlobalTheory.OrthNear.isOrth_x0F X
  obtain ⟨ρ0, hρ0, hball⟩ := Metric.isOpen_iff.mp (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExF.isOpen_OmF X x0) 0 (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IW.zero_mem_OmF X x0 h0)
  set K := Metric.closedBall (0 : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) (ρ0 / 2)
  have hKsub : K ⊆ _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x0 :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hK : IsCompact K := isCompact_closedBall _ _
  have hKne : K.Nonempty := ⟨0, Metric.mem_closedBall_self (by linarith)⟩
  have hd : ContinuousOn (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.densF X x0) K := (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB.densF_continuousOn (X := X) (x0 := x0)).mono hKsub
  have hn : ContinuousOn (fun z => X.nfac la (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z)) K :=
    (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE.nfac_cont X x0 la).mono hKsub
  obtain ⟨z1, hz1, hmin1⟩ := hK.exists_isMinOn hKne hd
  obtain ⟨z2, hz2, hmin2⟩ := hK.exists_isMinOn hKne hn
  obtain ⟨C1, hC1⟩ := hK.exists_bound_of_continuousOn hd
  obtain ⟨C2, hC2⟩ := hK.exists_bound_of_continuousOn hn
  refine ⟨ρ0 / 2, min (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.densF X x0 z1) (X.nfac la (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z2)), max C1 C2,
    by linarith, lt_min (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB.densF_pos (hKsub hz1)) (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE.nfac_pos X x0 (hKsub hz2)), ?_⟩
  intro x hx z hz
  have hzK : z ∈ K := Metric.mem_closedBall.mpr (by rw [dist_zero_right]; exact hz.le)
  have hdom : _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z ∈ X.dom := hKsub hzK
  rw [densF_eq_of_isOrth X hx h0, nfac_cpt_eq_of_isOrth X hx h0,
    cpt_mem_dom_iff_of_isOrth X hx h0]
  exact ⟨hdom, (min_le_left _ _).trans (isMinOn_iff.mp hmin1 z hzK),
    (Real.le_norm_self _).trans ((hC1 z hzK).trans (le_max_left _ _)),
    (min_le_right _ _).trans (isMinOn_iff.mp hmin2 z hzK),
    (Real.le_norm_self _).trans ((hC2 z hzK).trans (le_max_right _ _))⟩

end GlobalTheory.OrthNear
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FjNormMulExpLeSupFlow
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

open MajorantConjugateTransfer TwoSidedBoostBounds MinimumGrowthBounds FractionalSliceDomains in
theorem fj_norm_mul_exp_le_sup_flow :
    (∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (F : Frame X.Ψ r → ℂ), X.IsSec la F → ∀ ξ, X.IsIso ξ → ∀ (ν : X.Ψ → ℝ), ∀ x ∈ X.dom, ∃ B : ℝ, 0 ≤ B ∧ ∀ (y : X.Ψ → ℝ) (M : ℝ), (∀ τ, 0 ≤ y τ) → (∀ u : X.Ψ → ℝ, (∀ τ, |u τ| ≤ B) → ‖F (X.flow ξ (fun τ => (u τ : ℂ) + (y τ : ℂ) * Complex.I) x)‖ ≤ M) → ‖X.fj la ξ ν F x‖ * Real.exp (-4 * Real.pi * ∑ τ, ν τ * y τ) ≤ M) := open ReciprocityTheory.ChartRestriction.G.FD.FractionalSliceDomains ReciprocityTheory.ChartRestriction.G.FD.MinimumGrowthBounds ReciprocityTheory.ChartRestriction.G.FD.TwoSidedBoostBounds in by
  intro r X la P hP ξ hξ ν x hx
  classical
  obtain ⟨bs, hω⟩ := FlowMeanContinuity.exists_basis X la
  have hωp : ∀ j, bs j ∈ X.periods la := by
    intro j
    have : bs j ∈ Submodule.span ℤ (Set.range bs) := Submodule.subset_span ⟨j, rfl⟩
    rw [hω] at this
    exact this
  have hrepr : ∀ (v : X.Ψ → ℝ) τ, ∑ j, bs.repr v j * bs j τ = v τ := by
    intro v τ
    conv_rhs => rw [← bs.sum_repr v]
    simp [Finset.sum_apply, mul_comm]
  have hB := Bω_nonneg X bs
  refine ⟨Bω X bs, hB, ?_⟩
  intro y M hy hM
  by_cases hf : ∀ j, ∃ k : ℤ, 2 * ∑ τ, ν τ * bs j τ = k
  swap
  · have h0 : X.fj la ξ ν P x = 0 := by
      unfold Data.fj
      rw [if_neg]
      intro hall
      exact hf fun j => hall _ (hωp j)
    rw [h0, norm_zero, zero_mul]
    exact (norm_nonneg _).trans (hM 0 fun τ => by simpa using hB)
  choose k hk using hf
  rw [FlowMeanContinuity.fj_eq_fourCoeff X la P hP hξ hx bs hω ν k hk]
  change ‖ReciprocityTheory.L2DbarEstimates.Y.fourCoeff (hfun X P ξ x bs) 0 k‖ * _ ≤ _
  have hm : ∀ τ, 0 < X.maj x τ (Data.emb τ.1 ξ) :=
    fun τ => X.maj_pos hx τ (emb_ne_zero τ.1 hξ.2.2)
  have hc := c_pos X
  set b' : Fin (Fintype.card X.Ψ) → ℝ := fun j => bs.repr y j with hb'
  have hb'ω : ∀ τ, ∑ j, b' j * bs j τ = y τ := hrepr y
  have hb'Ω : b' ∈ FractionalSliceDomains.Om X ξ x bs := by
    show (fun τ => ∑ j, b' j * bs j τ) ∈ AdmissibleHermitianColumns.admissibleImaginary X ξ x
    rw [mem_admissibleImaginary_iff X hx hξ]
    intro τ
    rw [hb'ω]
    have := hc τ; have := hm τ; have := hy τ
    positivity
  have hind := ReciprocityTheory.L2DbarEstimates.Y.four_indep (Fintype.card X.Ψ) (FractionalSliceDomains.Om X ξ x bs) (hfun X P ξ x bs)
    (Om_open_conn X bs hx).1 (Om_open_conn X bs hx).2 (hfun_diff X bs P la hP hx hξ)
    (hfun_periodic X bs P la hP hx hξ hω) 0 (zero_mem_Om X bs hx hξ) b' hb'Ω k
  rw [hind]
  have hslice : ∀ t : Fin (Fintype.card X.Ψ) → ℝ,
      ‖hfun X P ξ x bs (fun k => (t k : ℂ) + (b' k : ℂ) * Complex.I)‖ ≤ M := by
    intro t
    rw [slice_fract X bs P la hP hx hξ hω hb'Ω t]
    have h := hM (fun τ => ∑ j, Int.fract (t j) * bs j τ) (fun τ =>
      re_bound X bs _ (fun j => ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩) τ)
    unfold hfun
    convert h using 4
    funext τ
    rw [← hb'ω τ]
    push_cast
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hbd := ReciprocityTheory.L2DbarEstimates.Y.four_bound (Fintype.card X.Ψ) (hfun X P ξ x bs) b' k _ hslice
  have hsum : ∑ j, (k j : ℝ) * b' j = 2 * ∑ τ, ν τ * ∑ j, b' j * bs j τ := by
    simp only [← hk, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hsum] at hbd
  simp only [hb'ω] at hbd
  convert hbd using 3
  ring

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsDriftFunctionOrthonormalHermitianFrames
section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.HeightSupInvariantUnderHermitianLatticeAut
section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.HeightSupInvariantUnderHermitianLatticeAut
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace GlobalTheory

theorem height_sup_lact_invariant : (∀ (r : ℕ) (X : Data E r) (d : Frame X.Ψ r → Submodule E (Fin r → E) → ℝ), (∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → d x (Submodule.span E (Set.range w)) = ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ))) → ∀ (δ : ℝ) (α : ℕ → Frame X.Ψ r → ℝ), (∀ i ≤ r, ∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → IsLUB ((fun W => d x W ^ (-δ)) '' {W | Module.finrank E W = i}) (α i x)) → ∀ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ → ∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ i ≤ r, α i (lact γ x) = α i x) := by
  intro r X d hd δ α hα γ hγ x hx i hi
  obtain ⟨hx', hmap⟩ := HeightInv.height_lact r X d hd γ hγ x hx
  have hinj : ∀ g : GL (Fin r) E,
      Function.Injective (g : Matrix (Fin r) (Fin r) E).mulVecLin := by
    intro g v w hvw
    have h := congrArg (fun u => ((g⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ u) hvw
    simpa [Matrix.mulVec_mulVec] using h
  have hrank : ∀ (g : GL (Fin r) E) (W : Submodule E (Fin r → E)),
      Module.finrank E (W.map (g : Matrix (Fin r) (Fin r) E).mulVecLin) = Module.finrank E W :=
    fun g W => (Submodule.equivMapOfInjective _ (hinj g) W).finrank_eq.symm
  have hset : (fun W => d (lact γ x) W ^ (-δ)) '' {W | Module.finrank E W = i} =
      (fun W => d x W ^ (-δ)) '' {W | Module.finrank E W = i} := by
    ext y
    constructor
    · rintro ⟨W', hW', rfl⟩
      refine ⟨W'.map ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).mulVecLin, ?_, ?_⟩
      · simp only [Set.mem_ofPred_eq] at hW' ⊢
        rw [hrank, hW']
      · have hback : (W'.map ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).mulVecLin).map
            (γ : Matrix (Fin r) (Fin r) E).mulVecLin = W' := by
          rw [← Submodule.map_comp, ← Matrix.mulVecLin_mul, ← Units.val_mul, mul_inv_cancel,
            Units.val_one, Matrix.mulVecLin_one, Submodule.map_id]
        simp only
        rw [← hmap, hback]
    · rintro ⟨W, hW, rfl⟩
      refine ⟨W.map (γ : Matrix (Fin r) (Fin r) E).mulVecLin, ?_, ?_⟩
      · simp only [Set.mem_ofPred_eq] at hW ⊢
        rw [hrank, hW]
      · simp only
        rw [hmap]
  have h1 := hα i hi (lact γ x) hx'
  rw [hset] at h1
  exact h1.unique (hα i hi x hx)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.HeightSupInvariantUnderHermitianLatticeAutStatement
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
theorem _root_.GlobalTheory.T.heightSup_invariant_under_hermitianLattice_aut : (∀ (r : ℕ) (X : Data E r) (d : Frame X.Ψ r → Submodule E (Fin r → E) → ℝ), (∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → d x (Submodule.span E (Set.range w)) = ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ))) → ∀ (δ : ℝ) (α : ℕ → Frame X.Ψ r → ℝ), (∀ i ≤ r, ∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → IsLUB ((fun W => d x W ^ (-δ)) '' {W | Module.finrank E W = i}) (α i x)) → ∀ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ → ∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ i ≤ r, α i (lact γ x) = α i x) := by
  first | exact @GlobalTheory.height_sup_lact_invariant | exact GlobalTheory.height_sup_lact_invariant | (intros; apply GlobalTheory.height_sup_lact_invariant <;> assumption)
end
end

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace GlobalTheory

theorem lowerSemicontinuousOn_sum_pos_mul {Y : Type*} [TopologicalSpace Y] {s : Set Y}
    (I : Finset ℕ) (e : ℕ → ℝ) (he : ∀ i, 0 < e i) (α : ℕ → Y → ℝ)
    (hα : ∀ i ∈ I, LowerSemicontinuousOn (α i) s) :
    LowerSemicontinuousOn (fun x => ∑ i ∈ I, e i * α i x) s := by
  have key : ∀ i ∈ I, LowerSemicontinuousOn (fun x => e i * α i x) s := by
    intro i hi x hx y hy
    have h1 : y / e i < α i x := by
      rw [div_lt_iff₀ (he i)]
      linarith
    filter_upwards [hα i hi x hx (y / e i) h1] with z hz
    rw [gt_iff_lt, div_lt_iff₀ (he i)] at hz
    show y < e i * α i z
    linarith
  exact lowerSemicontinuousOn_sum key

theorem exists_drift_function_orthFrames : (∀ (r : ℕ) (X : Data E r), 0 < X.p0 → X.p0 < r → ∀ (τ0 : X.Ψ) (S : Finset (Matrix (Fin r) (Fin r) ℂ)), (∀ a ∈ S, a.IsHermitian ∧ a.det ≠ 0 ∧ a⁻¹ ∈ S) → (∀ W : Submodule ℂ (Fin r → ℂ), (∀ a ∈ S, ∀ v ∈ W, (a * a).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤) → (∀ a ∈ S, (a)ᵀ * (Matrix.diagonal fun k : Fin r => if (k : ℕ) < X.p0 then (1 : ℂ) else -1) * (a).map (starRingEnd ℂ) = (Matrix.diagonal fun k : Fin r => if (k : ℕ) < X.p0 then (1 : ℂ) else -1)) → ∃ (f : Frame X.Ψ r → ℝ) (c b : ℝ), 0 ≤ c ∧ c < 1 ∧ 0 ≤ b ∧ LowerSemicontinuousOn f {x | IsOrth X x} ∧ (∀ x, IsOrth X x → 0 ≤ f x) ∧ (∀ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ → ∀ x, IsOrth X x → f (lact γ x) = f x) ∧ (∀ x, IsOrth X x → ∑ a ∈ S, f (@Function.update X.Ψ (fun _ => Fin r → Fin r → ℂ) (Classical.decEq _) x τ0 (mat x τ0 * a⁻¹ : Matrix (Fin r) (Fin r) ℂ)) ≤ S.card * (c * f x + b)) ∧ ∀ M : ℝ, ∃ ε : ℝ, 0 < ε ∧ ∀ x, IsOrth X x → f x ≤ M → ε ≤ X.la1 x) := by
  intro r X hp0 hp0r τ0 S hS hirr hU
  obtain ⟨d, hd⟩ := GlobalTheory.T.exists_subspaceHeight_gramDeterminant r X
  obtain ⟨δ, hδ, hdrift⟩ := GlobalTheory.T.weighted_height_sup_drift_orthonormal_frames r X d hd τ0 S hS hirr hU
  obtain ⟨α, hlub, hlsc⟩ := exists_isLUB_height_rpow_lowerSemicontinuousOn r X d hd δ hδ
  obtain ⟨e, c, b, he, hc0, hc1, hb, hdr⟩ := hdrift α hlub
  have hdet : ∀ x, IsOrth X x → ∀ τ : X.Ψ, (mat x τ).det ≠ 0 := fun x hx => (GlobalTheory.T.majorant_eq_sum_norm_sq_orthonormalFrame r X x hx).1
  have hr : 0 < r := lt_trans hp0 hp0r
  have hlow : ∀ x, IsOrth X x → ∀ i ≤ r, ∀ W : Submodule E (Fin r → E),
      Module.finrank E W = i → 0 < d x W ∧ d x W ^ (-δ) ≤ α i x := by
    intro x hx i hi W hW
    obtain ⟨m, hm, hmW⟩ := GlobalTheory.T.exists_pos_le_latticeHeight_at_frame r X d hd x (hdet x hx)
    exact ⟨lt_of_lt_of_le hm (hmW W), (hlub i hi x (hdet x hx)).1 ⟨W, hW, rfl⟩⟩
  have hαnn : ∀ x, IsOrth X x → ∀ i ≤ r, 0 ≤ α i x := by
    intro x hx i hi
    obtain ⟨W, hW⟩ := exists_submodule_finrank_eq_of_le (K := E) hi
    obtain ⟨hpos, hle⟩ := hlow x hx i hi W hW
    exact le_trans (Real.rpow_nonneg hpos.le _) hle
  have hterm_nn : ∀ x, IsOrth X x → ∀ i ∈ Finset.Ioo 0 r, 0 ≤ e i * α i x := fun x hx i hi =>
    mul_nonneg (he i).le (hαnn x hx i (Finset.mem_Ioo.1 hi).2.le)
  refine ⟨fun x => ∑ i ∈ Finset.Ioo 0 r, e i * α i x, c, b, hc0, hc1, hb, ?_, ?_, ?_, hdr, ?_⟩
  · exact lowerSemicontinuousOn_sum_pos_mul _ e he α fun i hi =>
      (hlsc i (Finset.mem_Ioo.1 hi).2.le).mono fun x hx => hdet x hx
  · intro x hx
    exact Finset.sum_nonneg (hterm_nn x hx)
  · intro γ hγ x hx
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [GlobalTheory.T.heightSup_invariant_under_hermitianLattice_aut r X d hd δ α hlub γ hγ x (hdet x hx) i (Finset.mem_Ioo.1 hi).2.le]
  · intro M
    have h1 : (1 : ℕ) ∈ Finset.Ioo 0 r := Finset.mem_Ioo.2 ⟨Nat.one_pos, lt_of_le_of_lt hp0 hp0r⟩
    set K : ℝ := max (M / e 1) 1 with hK
    have hKpos : 0 < K := lt_of_lt_of_le one_pos (le_max_right _ _)
    obtain ⟨ε, hε, hεla⟩ := GlobalTheory.T.firstMinimum_lower_of_lineHeights r X d hd hr (K ^ (-1 / δ)) (Real.rpow_pos_of_pos hKpos _)
    refine ⟨ε, hε, fun x hx hfM => hεla x hx fun W hW => ?_⟩
    obtain ⟨hpos, hle⟩ := hlow x hx 1 (Finset.mem_Ioo.1 h1).2.le W hW
    have hsingle : e 1 * α 1 x ≤ M :=
      le_trans (Finset.single_le_sum (hterm_nn x hx) h1) hfM
    have hdK : d x W ^ (-δ) ≤ K := by
      refine le_trans hle (le_trans ?_ (le_max_left _ _))
      rw [le_div_iff₀ (he 1)]
      linarith
    have hpow : K ^ (-1 / δ) ≤ (d x W ^ (-δ)) ^ (-1 / δ) :=
      Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hpos _) hdK
        (div_nonpos_of_nonpos_of_nonneg (by norm_num) hδ.le)
    rwa [← Real.rpow_mul hpos.le, show -δ * (-1 / δ) = 1 by field_simp, Real.rpow_one] at hpow

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsLeNormDev
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.GrpSep

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

noncomputable def dev {Ψ : Finset (E →+* ℂ)} {r : ℕ} (x0 : Frame Ψ r) (γ : GL (Fin r) E) :
    Frame Ψ r :=
  fun τ => ((mat x0 τ)⁻¹ * (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x0 τ - 1 :
    Matrix (Fin r) (Fin r) ℂ)

noncomputable def shift {Ψ : Finset (E →+* ℂ)} {r : ℕ} (x0 M : Frame Ψ r) : Frame Ψ r :=
  fun τ => (mat x0 τ * (mat M τ + 1) : Matrix (Fin r) (Fin r) ℂ)

noncomputable def oneF (Ψ : Finset (E →+* ℂ)) (r : ℕ) : Frame Ψ r :=
  fun _ => (1 : Matrix (Fin r) (Fin r) ℂ)

end GlobalTheory.GrpSep

namespace GlobalTheory

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private lemma sgn_ne_zero_torus_haar_measure (p a : ℕ) : _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn p a ≠ 0 := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn; split_ifs <;> norm_num

private lemma det_mat_ne_zero_of_isOrth' {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) {x0 : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r}
    (h : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x0) (τ : X.Ψ) : (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ).det ≠ 0 := by
  intro h0
  have := congrArg Matrix.det (h τ)
  rw [_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.gram_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul, zero_mul,
    Matrix.det_diagonal] at this
  exact (Finset.prod_ne_zero_iff.mpr fun a _ => by exact_mod_cast sgn_ne_zero_torus_haar_measure X.p0 a) this.symm

private lemma mem_dom_of_isOrth {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) {x0 : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r}
    (h : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x0) : x0 ∈ X.dom := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.dom _root_.ReciprocityTheory.ChartRestriction.G.FD.GG
  refine fun τ => ⟨det_mat_ne_zero_of_isOrth' X h τ, fun i => ?_⟩
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin _root_.ReciprocityTheory.ChartRestriction.G.FD.lminor
  rw [h τ, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal]
  simp only [Function.comp_apply, Fin.coe_castLE]
  rw [← Complex.ofReal_prod, Complex.ofReal_re,
    Fin.prod_univ_eq_prod_range (fun j => _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 j) i]
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.psgn
  exact mul_self_pos.mpr (Finset.prod_ne_zero_iff.mpr fun a _ => sgn_ne_zero_torus_haar_measure X.p0 a)

private lemma continuous_shift' {Ψ : Finset (E →+* ℂ)} {r : ℕ} (x0 : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r) :
    Continuous (fun M : Ψ → Fin r → Fin r → ℂ =>
      (_root_.GlobalTheory.GrpSep.shift x0 M : Ψ → Fin r → Fin r → ℂ)) := by
  unfold _root_.GlobalTheory.GrpSep.shift _root_.ReciprocityTheory.ChartRestriction.G.FD.mat
  refine continuous_pi fun τ => ?_
  exact continuous_const.matrix_mul ((continuous_apply τ).add continuous_const)

private lemma shift_zero_torus_haar_measure {Ψ : Finset (E →+* ℂ)} {r : ℕ} (x0 : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r) :
    _root_.GlobalTheory.GrpSep.shift x0 0 = x0 := by
  funext τ
  change _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ * (0 + 1) = x0 τ
  rw [zero_add, Matrix.mul_one]; rfl

private lemma exists_pos_le_of_finite_pos {α : Type*} (S : Set α) (hS : S.Finite) (f : α → ℝ)
    (hf : ∀ a ∈ S, 0 < f a) : ∃ δ > 0, ∀ a ∈ S, δ ≤ f a := by
  rcases S.eq_empty_or_nonempty with h | h
  · exact ⟨1, one_pos, by simp [h]⟩
  · obtain ⟨a0, ha0, hmin⟩ := Set.exists_min_image S f hS h
    exact ⟨f a0, hf a0 ha0, hmin⟩

private lemma oneF_mem_bor {Ψ : Finset (E →+* ℂ)} {r : ℕ} :
    _root_.GlobalTheory.GrpSep.oneF Ψ r ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor Ψ r := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor
  refine fun τ => ⟨?_, fun a c h => ?_⟩
  · change (1 : Matrix (Fin r) (Fin r) ℂ).det ≠ 0
    simp
  · change (1 : Matrix (Fin r) (Fin r) ℂ) a c = 0
    exact Matrix.one_apply_ne h.ne'

private lemma shift_dev_eq_lact {Ψ : Finset (E →+* ℂ)} {r : ℕ} (x0 : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r)
    (hdet : ∀ τ, (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ).det ≠ 0) (γ : GL (Fin r) E) :
    _root_.GlobalTheory.GrpSep.shift x0 (_root_.GlobalTheory.GrpSep.dev x0 γ) = _root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ x0 := by
  funext τ
  change _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ * ((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ)⁻¹ * (γ : Matrix (Fin r) (Fin r) E).map τ.1 *
    _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ - 1 + 1) = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ
  rw [sub_add_cancel, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ (Ne.isUnit (hdet τ)), Matrix.one_mul]

private lemma rmul_oneF' {Ψ : Finset (E →+* ℂ)} {r : ℕ} (x0 : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x0 (_root_.GlobalTheory.GrpSep.oneF Ψ r) = x0 := by
  funext τ
  change (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ * 1 : Matrix (Fin r) (Fin r) ℂ) = _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ
  exact Matrix.mul_one _

theorem _root_.GlobalTheory.grpSep : ∀ (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x0 : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r),
    _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x0 → _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.PropDisc X →
    ∃ c : ℝ, 0 < c ∧ ∀ γ ∈ X.Γ, γ ≠ 1 → ∃ (τ : X.Ψ) (a b : Fin r),
      c ≤ ‖((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ)⁻¹ * (γ : Matrix (Fin r) (Fin r) E).map τ.1 * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ - 1) a b‖ := by
  intro r X x0 hO hP
  have hdom := mem_dom_of_isOrth X hO
  have hdet := det_mat_ne_zero_of_isOrth' X hO
  obtain ⟨U, hU, U', hU', hfin⟩ := hP x0 hdom x0 hdom
  have hV : (fun M : X.Ψ → Fin r → Fin r → ℂ =>
      (_root_.GlobalTheory.GrpSep.shift x0 M : X.Ψ → Fin r → Fin r → ℂ)) ⁻¹' U' ∈
      nhds (0 : X.Ψ → Fin r → Fin r → ℂ) :=
    (continuous_shift' x0).continuousAt.preimage_mem_nhds (by erw [shift_zero_torus_haar_measure]; exact hU')
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hV
  let S : Set (GL (Fin r) E) :=
    {γ | γ ∈ {γ | γ ∈ X.Γ ∧ ∃ u ∈ U, ∃ u' ∈ U', ∃ b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor X.Ψ r,
      _root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ u = _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul u' b} \ ({1} : Set (GL (Fin r) E))}
  obtain ⟨δ, hδ, hmin⟩ := exists_pos_le_of_finite_pos S (hfin.subset (fun _ h => Set.sdiff_subset h))
    (fun γ => ‖(_root_.GlobalTheory.GrpSep.dev x0 γ : X.Ψ → Fin r → Fin r → ℂ)‖) (by
      rintro γ ⟨hγ, h1⟩
      refine norm_pos_iff.mpr fun h0 => h1 (Set.mem_singleton_iff.mpr ?_)
      refine X.Γ_free γ hγ.1 x0 hdom (_root_.GlobalTheory.GrpSep.oneF X.Ψ r) oneF_mem_bor ?_
      rw [← shift_dev_eq_lact x0 hdet, rmul_oneF']
      exact (congrArg (_root_.GlobalTheory.GrpSep.shift x0) h0).trans (shift_zero_torus_haar_measure x0))
  refine ⟨min ε δ, lt_min hε hδ, fun γ hγ h1 => ?_⟩
  by_contra hcon
  push_neg at hcon
  have hlt : ‖(_root_.GlobalTheory.GrpSep.dev x0 γ : X.Ψ → Fin r → Fin r → ℂ)‖ < min ε δ := by
    refine (pi_norm_lt_iff (lt_min hε hδ)).mpr fun τ => (pi_norm_lt_iff (lt_min hε hδ)).mpr
      fun a => (pi_norm_lt_iff (lt_min hε hδ)).mpr fun b => hcon τ a b
  have hmem : _root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ x0 ∈ U' := by
    rw [← shift_dev_eq_lact x0 hdet]
    exact hball (mem_ball_zero_iff.mpr (hlt.trans_le (min_le_left _ _)))
  have hS := hmin γ ⟨⟨hγ, x0, mem_of_mem_nhds hU, _, hmem, _root_.GlobalTheory.GrpSep.oneF X.Ψ r,
    oneF_mem_bor, (rmul_oneF' _).symm⟩, h1⟩
  exact absurd hS (not_le.mpr (hlt.trans_le (min_le_right _ _)))

end GlobalTheory
end
