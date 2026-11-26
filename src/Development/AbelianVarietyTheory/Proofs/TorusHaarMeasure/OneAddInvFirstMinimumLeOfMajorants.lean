module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MinimumGrowthBounds

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.OneAddInvFirstMinimumLeOfMajorants
namespace GlobalTheory

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace CuspDecay

end CuspDecay

private lemma isUStab_one' {r : ℕ} (G : Matrix (Fin r) (Fin r) E)
    (L : Submodule (𝓞 E) (Fin r → E)) : _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab G L (1 : GL (Fin r) E) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab
  simp

private lemma lact_one_eq_self {Ψ : Finset (E →+* ℂ)} {r : ℕ} (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.lact (1 : GL (Fin r) E) x = x := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.lact
  funext τ
  simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.mat]
  rfl

private lemma one_div_la1_nonneg {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) :
    0 ≤ 1 / X.la1 x := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.la1
  exact one_div_nonneg.mpr (Real.sqrt_nonneg _)

private lemma one_div_mul_le_one_div_of_ratio_bounds {k c m0 m1 : ℝ} (hk : 0 < k) (hc : 0 < c)
    (hp : 0 < 1 / (c * m0)) (h1 : m0 ≤ k * m1) (h2 : m1 ≤ k * m0) :
    1 / k * (1 / (c * m0)) ≤ 1 / (c * m1) := by
  have hp' : 0 < c * m0 := one_div_pos.mp hp
  have hm0 : 0 < m0 := by
    by_contra h
    push_neg at h
    nlinarith
  have hm1 : 0 < m1 := by nlinarith
  rw [div_mul_div_comm, one_mul]
  apply one_div_le_one_div_of_le (mul_pos hc hm1)
  nlinarith [mul_le_mul_of_nonneg_left h2 hc.le]

private lemma mul_iInf_le_iInf_of_mul_le {ι : Type*} [Finite ι] {f g : ι → ℝ} {k : ℝ} (hk : 0 ≤ k)
    (h : ∀ i, k * g i ≤ f i) : k * ⨅ i, g i ≤ ⨅ i, f i := by
  cases isEmpty_or_nonempty ι with
  | inl _ => simp [Real.iInf_of_isEmpty]
  | inr _ =>
    exact le_ciInf fun i =>
      (mul_le_mul_of_nonneg_left (ciInf_le (Set.finite_range g).bddBelow i) hk).trans (h i)

private lemma one_add_one_div_sqrt_le_two_mul {s0 s1 k : ℝ} (hk : 0 < k) (hk2 : k ≤ 2) (hs0 : 0 ≤ s0)
    (h1 : s0 ≤ k * s1) (h2 : s1 ≤ k * s0) : 1 + 1 / √s1 ≤ 2 * (1 + 1 / √s0) := by
  rcases hs0.eq_or_lt with h | h
  · subst h
    have hs1 : s1 ≤ 0 := by simpa using h2
    simp [Real.sqrt_eq_zero'.mpr hs1]
  · have hs1 : 0 < s1 := by nlinarith
    have hu := Real.sqrt_pos.mpr h
    have hv := Real.sqrt_pos.mpr hs1
    have h4 : s0 ≤ 4 * s1 := by nlinarith
    have hle : √s0 ≤ 2 * √s1 := by
      rw [show (2 : ℝ) * √s1 = √(4 * s1) by
        rw [Real.sqrt_mul' _ hs1.le, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt h4
    have h3 : 1 / √s1 ≤ 2 / √s0 := by
      rw [div_le_div_iff₀ hv hu]
      linarith
    have h5 : 2 / √s0 = 2 * (1 / √s0) := by ring
    have h6 : 0 ≤ 1 / √s0 := by positivity
    linarith

private lemma exp_half_le_of_comparable_lemma_4 {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (ps : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℝ)
    {a θ C A' : ℝ} (ha : 0 ≤ a) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hps : ∀ x ∈ X.dom, ∀ ξ : Fin r → E, X.IsIso ξ → (∀ τ, 1 ≤ X.tt ξ x τ) →
      ps x ≤ C + A' * Real.log (1 + 1 / X.la1 x) -
        8 * Real.pi * (1 - 2 * ((1 - θ) / 4)) * a * ⨅ τ, X.tt ξ x τ)
    {x y : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} (hx : x ∈ X.dom) (hy : y ∈ X.dom) {ξ : Fin r → E} (hξ : X.IsIso ξ)
    (htt : ∀ τ, 2 ≤ X.tt ξ x τ)
    (hcmp : ∀ (τ : X.Ψ) (v : Fin r → ℂ), X.maj x τ v ≤ (1 + (1 - θ) / 2) * X.maj y τ v ∧
      X.maj y τ v ≤ (1 + (1 - θ) / 2) * X.maj x τ v) :
    Real.exp (ps y / 2) ≤ Real.exp ((C + |A'| * Real.log 2) / 2) *
      (1 + 1 / X.la1 x) ^ (|A'| / 2) * Real.exp (-4 * Real.pi * (θ * a) * ⨅ τ, X.tt ξ x τ) := by
  have hT0 : 0 ≤ ⨅ τ, X.tt ξ x τ := Real.iInf_nonneg fun τ => by linarith only [htt τ]
  have hla0 : 0 ≤ 1 / X.la1 x := one_div_la1_nonneg X x
  have htty : ∀ τ, 1 / (1 + (1 - θ) / 2) * X.tt ξ x τ ≤ X.tt ξ y τ := by
    intro τ
    have hpos := htt τ
    simp only [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.tt] at hpos ⊢
    exact one_div_mul_le_one_div_of_ratio_bounds (by linarith only [hθ1]) (_root_.ReciprocityTheory.ChartRestriction.G.FD.TwoSidedBoostBounds.c_pos X τ) (by linarith only [hpos])
      (hcmp τ _).1 (hcmp τ _).2
  have hty1 : ∀ τ, 1 ≤ X.tt ξ y τ := by
    intro τ
    have h1 := htty τ
    have h2 := htt τ
    have h3 : 1 ≤ 1 / (1 + (1 - θ) / 2) * X.tt ξ x τ := by
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by linarith only [hθ1])]
      linarith only [h2, hθ0]
    linarith only [h1, h3]
  have hTy : 1 / (1 + (1 - θ) / 2) * ⨅ τ, X.tt ξ x τ ≤ ⨅ τ, X.tt ξ y τ :=
    mul_iInf_le_iInf_of_mul_le (by positivity) htty
  have hsq := _root_.ReciprocityTheory.ChartRestriction.G.FD.MinimumGrowthBounds.minimumSq_two_sided_bounds X hx hy (k1 := 1 / (1 + (1 - θ) / 2)) (k2 := 1 + (1 - θ) / 2)
    (by positivity) (by linarith only [hθ1])
    (fun τ w => by
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by linarith only [hθ1])]
      linarith only [(hcmp τ w).1])
    (fun τ w => (hcmp τ w).2)
  have hL : 1 + 1 / X.la1 y ≤ 2 * (1 + 1 / X.la1 x) := by
    simp only [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.la1]
    refine one_add_one_div_sqrt_le_two_mul (k := 1 + (1 - θ) / 2) (by linarith only [hθ1]) (by linarith only [hθ0])
      (_root_.ReciprocityTheory.ChartRestriction.G.FD.MinimumGrowthBounds.minimumSq_nonneg X hx) ?_ hsq.2
    have h := hsq.1
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by linarith only [hθ1])] at h
    linarith only [h]
  have hly0 : 0 ≤ 1 / X.la1 y := one_div_la1_nonneg X y
  have hLy0 : 0 ≤ Real.log (1 + 1 / X.la1 y) := Real.log_nonneg (le_add_of_nonneg_right hly0)
  have hLyle : Real.log (1 + 1 / X.la1 y) ≤ Real.log 2 + Real.log (1 + 1 / X.la1 x) := by
    rw [← Real.log_mul (by norm_num) (ne_of_gt (by linarith only [hla0]))]
    exact Real.log_le_log (by linarith only [hly0]) hL
  have hpsy := hps y hy ξ hξ hty1
  have hA : A' * Real.log (1 + 1 / X.la1 y) ≤
      |A'| * (Real.log 2 + Real.log (1 + 1 / X.la1 x)) :=
    (mul_le_mul_of_nonneg_right (le_abs_self A') hLy0).trans
      (mul_le_mul_of_nonneg_left hLyle (abs_nonneg _))
  have hθε : θ * (1 + (1 - θ) / 2) ≤ 1 - 2 * ((1 - θ) / 4) := by nlinarith [sq_nonneg (θ - 1)]
  have hkey : θ * ⨅ τ, X.tt ξ x τ ≤ (1 - 2 * ((1 - θ) / 4)) * ⨅ τ, X.tt ξ y τ := by
    have h1 : θ * ⨅ τ, X.tt ξ x τ ≤
        (1 - 2 * ((1 - θ) / 4)) * (1 / (1 + (1 - θ) / 2) * ⨅ τ, X.tt ξ x τ) := by
      rw [← mul_assoc]
      apply mul_le_mul_of_nonneg_right _ hT0
      rw [mul_one_div, le_div_iff₀ (by linarith only [hθ1])]
      exact hθε
    exact h1.trans (mul_le_mul_of_nonneg_left hTy (by linarith only [hθ0]))
  have hexp : ps y / 2 ≤ (C + |A'| * Real.log 2) / 2 +
      Real.log (1 + 1 / X.la1 x) * (|A'| / 2) + -4 * Real.pi * (θ * a) * ⨅ τ, X.tt ξ x τ := by
    have h8 := mul_le_mul_of_nonneg_left hkey (by positivity : 0 ≤ 8 * Real.pi * a)
    linarith only [hpsy, hA, h8]
  calc Real.exp (ps y / 2)
      ≤ Real.exp ((C + |A'| * Real.log 2) / 2 +
          Real.log (1 + 1 / X.la1 x) * (|A'| / 2) + -4 * Real.pi * (θ * a) * ⨅ τ, X.tt ξ x τ) :=
        Real.exp_le_exp.mpr hexp
    _ = _ := by rw [Real.exp_add, Real.exp_add, Real.rpow_def_of_pos (by linarith only [hla0])]

theorem _root_.GlobalTheory.pnorm_le_exp_neg_tt_near_cusp :
    (∀ (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (ε : ℝ), 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ ∀ x, _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → ∀ z : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X), ‖z‖ < ρ → _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z ∈ X.dom ∧ ∀ (τ : X.Ψ) (v : Fin r → ℂ), X.maj x τ v ≤ (1 + ε) * X.maj (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) τ v ∧ X.maj (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) τ v ≤ (1 + ε) * X.maj x τ v) → (∀ (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (γ : GL (Fin r) E), _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab X.Gm X.Λ γ → ∀ x ∈ X.dom, ∀ b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor X.Ψ r, _root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b) ∈ X.dom ∧ ∀ (τ : X.Ψ) (v : Fin r → ℂ), X.maj (_root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b)) τ (Matrix.mulVec ((γ : Matrix (Fin r) (Fin r) E).map τ.1) v) = X.maj x τ v) → (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.NfacRmulStatement (E := E) ∧ _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.NfacLactStatement (E := E) ∧ _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.PnormInvStatement (E := E)) → (∀ (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (F : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ) (ps : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℝ) (a : ℝ), X.IsSec la F → _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.cfwM X ps a → 0 ≤ a → (∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∃ C : ℝ, ∀ x ∈ X.dom, _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → ENNReal.ofReal (X.pnorm la F x) ≤ ENNReal.ofReal C * ⨆ (z : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) (_ : ‖z‖ < ρ) (_ : _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z ∈ X.dom), ENNReal.ofReal (Real.exp (ps (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) / 2))) → ∀ θ a' : ℝ, 0 < θ → θ < 1 → a' = θ * a → ∃ C A : ℝ, 0 ≤ A ∧ ∀ x ∈ X.dom, ∀ ξ : Fin r → E, X.IsIso ξ → (∀ τ, 2 ≤ X.tt ξ x τ) → X.pnorm la F x ≤ C * (1 + 1 / X.la1 x) ^ A * Real.exp (-4 * Real.pi * a' * ⨅ τ, X.tt ξ x τ)) := by
  intro hcpt hinv hstat r X la F ps a hsec hcf ha hbound θ a' hθ0 hθ1 ha'
  obtain ⟨-, -, hpinv⟩ := hstat
  obtain ⟨ρ, hρ0, hρ1, hnear⟩ := hcpt r X ((1 - θ) / 2) (by linarith)
  obtain ⟨C₀, hC₀⟩ := hbound ρ hρ0 hρ1
  obtain ⟨C, A', hps⟩ := hcf.2 ((1 - θ) / 4) (by linarith) (by linarith)
  refine ⟨max C₀ 0 * Real.exp ((C + |A'| * Real.log 2) / 2), |A'| / 2, by positivity, ?_⟩
  intro x hx ξ hξ htt
  have hb : _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor X.Ψ r := _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf_mem X hx
  obtain ⟨hx₀, hmaj₀⟩ := hinv r X 1 (isUStab_one' _ _) x hx _ hb
  have hpn := hpinv r X la F hsec 1 (one_mem _) x hx _ hb
  rw [lact_one_eq_self] at hx₀ hmaj₀ hpn
  have horth : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x)) := _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.ortho_bOf X hx
  generalize _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) = x₀ at hx₀ hmaj₀ hpn horth
  have hmaj : ∀ τ v, X.maj x₀ τ v = X.maj x τ v := by
    intro τ v
    simpa using hmaj₀ τ v
  have htt₀ : ∀ τ, X.tt ξ x₀ τ = X.tt ξ x τ := by
    intro τ
    simp only [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.tt, hmaj]
  have hla : X.la1 x₀ = X.la1 x := by
    have h := _root_.ReciprocityTheory.ChartRestriction.G.FD.MinimumGrowthBounds.minimumSq_two_sided_bounds X hx hx₀ (k1 := 1) (k2 := 1) zero_le_one one_pos
      (fun τ w => by rw [hmaj, one_mul]) (fun τ w => by rw [hmaj, one_mul])
    simp only [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.la1]
    exact congrArg Real.sqrt (by linarith [h.1, h.2])
  have hT0 : 0 ≤ ⨅ τ, X.tt ξ x τ := Real.iInf_nonneg fun τ => by linarith only [htt τ]
  have hla0 : 0 ≤ 1 / X.la1 x := one_div_la1_nonneg X x
  have hsup : ⨆ (z : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) (_ : ‖z‖ < ρ) (_ : _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x₀ z ∈ X.dom),
      ENNReal.ofReal (Real.exp (ps (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x₀ z) / 2)) ≤
        ENNReal.ofReal (Real.exp ((C + |A'| * Real.log 2) / 2) * (1 + 1 / X.la1 x) ^ (|A'| / 2) *
          Real.exp (-4 * Real.pi * a' * ⨅ τ, X.tt ξ x τ)) := by
    refine iSup_le fun z => iSup_le fun hz => iSup_le fun _ => ENNReal.ofReal_le_ofReal ?_
    obtain ⟨hy, hcmp⟩ := hnear x₀ horth z hz
    have h := exp_half_le_of_comparable_lemma_4 X ps ha hθ0 hθ1 hps hx₀ hy hξ
      (fun τ => by rw [htt₀]; exact htt τ) hcmp
    rwa [hla, ← ha', iInf_congr htt₀] at h
  have hB0 : 0 ≤ Real.exp ((C + |A'| * Real.log 2) / 2) * (1 + 1 / X.la1 x) ^ (|A'| / 2) *
      Real.exp (-4 * Real.pi * a' * ⨅ τ, X.tt ξ x τ) :=
    mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (by linarith only [hla0]) _))
      (Real.exp_pos _).le
  have hfin := (hC₀ x₀ hx₀ horth).trans
    (mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_left C₀ 0)) hsup)
  rw [← ENNReal.ofReal_mul (le_max_right _ _), hpn,
    ENNReal.ofReal_le_ofReal_iff (mul_nonneg (le_max_right _ _) hB0)] at hfin
  calc X.pnorm la F x ≤ _ := hfin
    _ = _ := by ring

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.LeadMCoeffEqZero
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.LeadIndep

open Filter

theorem mem_multiLt {D a : ℕ} {α : Fin D → ℕ} : α ∈ multiLt D a ↔ ∑ k, α k < a := by
  simp only [multiLt, Finset.mem_biUnion, Finset.mem_range, Finset.Nat.mem_antidiagonalTuple]
  constructor
  · rintro ⟨e, he, rfl⟩
    exact he
  · intro h
    exact ⟨_, h, rfl⟩

private theorem sum_mul_pow_mul_prod_eq_div_pow {n δ : ℕ} (α : Fin n → ℕ) (c : Fin δ → ℂ) (Φv : Fin δ → ℂ)
    (σv : Fin n → ℂ) (w t : ℂ) (T d : ℕ) (ht : t ≠ 0) (hw : w ≠ 0)
    (hle : (∃ k, c k ≠ 0) → d ≤ ∑ q, α q) :
    (∑ k, c k * Φv k) * t ^ (∑ q, α q - d) * w ^ (∑ q, α q + (T - ∑ q, α q)) *
        ∏ q, (t⁻¹ * (σv q / w)) ^ α q =
      (∑ k, c k * (∏ q, σv q ^ α q) * w ^ (T - ∑ q, α q) * Φv k) / t ^ d := by
  by_cases hz : ∀ k, c k = 0
  · simp [hz]
  push Not at hz
  have hd := hle hz
  have hprod : ∏ q, (t⁻¹ * (σv q / w)) ^ α q = (t⁻¹ * w⁻¹) ^ (∑ q, α q) * ∏ q, σv q ^ α q := by
    rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun q _ => ?_
    rw [← mul_pow, div_eq_mul_inv]
    ring
  have hsum : ∑ k, c k * (∏ q, σv q ^ α q) * w ^ (T - ∑ q, α q) * Φv k =
      (∑ k, c k * Φv k) * (∏ q, σv q ^ α q) * w ^ (T - ∑ q, α q) := by
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hprod, hsum]
  generalize ∑ q, α q = s at hd ⊢
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hd
  rw [Nat.add_sub_cancel_left, eq_div_iff (pow_ne_zero d ht)]
  have key : (t⁻¹ * w⁻¹) ^ (d + e) * (t * w) ^ (d + e) = 1 := by
    rw [← mul_pow, show t⁻¹ * w⁻¹ * (t * w) = 1 by field_simp, one_pow]
  linear_combination ((∑ k, c k * Φv k) * (∏ q, σv q ^ α q) * w ^ (T - (d + e))) * key

theorem lowest_degree {n δ : ℕ} (U : Set (V n)) (hU : IsOpen U)
    (vP : V n) (hvP : vP ∈ U) (σ : Fin n → V n → ℂ) (wz : V n → ℂ) (Φ : Fin δ → V n → ℂ)
    (M : Finset (Fin n → ℕ)) (T m d : ℕ) (c : (Fin n → ℕ) → Fin δ → ℂ)
    (hσ : ∀ k, DifferentiableOn ℂ (σ k) U) (hw : DifferentiableOn ℂ wz U)
    (hΦ : ∀ k, DifferentiableOn ℂ (Φ k) U)
    (hσ0 : ∀ k, σ k vP = 0) (hw0 : wz vP ≠ 0)
    (hlow : ∀ α ∈ M, ∀ k, c α k ≠ 0 → d ≤ ∑ q, α q) (hdm : d < m)
    (hb : ∃ C : ℝ, ∀ᶠ v in 𝓝 vP, ‖∑ α ∈ M, ∑ k,
      c α k * (∏ q, σ q v ^ α q) * wz v ^ (T - ∑ q, α q) * Φ k v‖ ≤ C * ‖v - vP‖ ^ m)
    (h0 : V n) :
    ∑ α ∈ M, ((∑ k, c α k * Φ k vP) * 0 ^ (∑ q, α q - d) *
        wz vP ^ (∑ q, α q + (T - ∑ q, α q))) *
      ∏ q, (fderiv ℂ (fun v => WithLp.toLp 2 (fun k => σ k v / wz v)) vP h0) q ^ α q = 0 := by
  classical
  have hUn : U ∈ 𝓝 vP := hU.mem_nhds hvP
  have hwd : DifferentiableAt ℂ wz vP := hw.differentiableAt hUn
  have hΦc : ∀ k, ContinuousAt (Φ k) vP := fun k => ((hΦ k).differentiableAt hUn).continuousAt
  have hFd : DifferentiableAt ℂ (fun v => (WithLp.toLp 2 (fun k => σ k v / wz v) : V n)) vP := by
    have h1 : DifferentiableAt ℂ (fun v => fun k => σ k v / wz v) vP :=
      differentiableAt_pi.2 fun k => by
        simpa only [div_eq_mul_inv, Function.comp_def, Pi.mul_def] using
          ((hσ k).differentiableAt hUn).mul ((differentiableAt_inv hw0).comp vP hwd)
    exact (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => ℂ)).symm.differentiableAt.comp vP h1
  have hl : HasDerivAt (fun t : ℂ => vP + t • h0) h0 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const h0).const_add vP
  have hl0 : Tendsto (fun t : ℂ => vP + t • h0) (𝓝 0) (𝓝 vP) := by
    simpa using hl.continuousAt.tendsto
  have hl1 : Tendsto (fun t : ℂ => vP + t • h0) (𝓝[≠] 0) (𝓝 vP) := hl0.mono_left nhdsWithin_le_nhds
  have hFl : HasDerivAt (fun t : ℂ => (WithLp.toLp 2
      (fun k => σ k (vP + t • h0) / wz (vP + t • h0)) : V n))
      (fderiv ℂ (fun v => (WithLp.toLp 2 (fun k => σ k v / wz v) : V n)) vP h0) 0 := by
    have hF' : HasFDerivAt (fun v => (WithLp.toLp 2 (fun k => σ k v / wz v) : V n))
        (fderiv ℂ (fun v => (WithLp.toLp 2 (fun k => σ k v / wz v) : V n)) vP) (vP + (0 : ℂ) • h0) := by
      rw [zero_smul, add_zero]
      exact hFd.hasFDerivAt
    exact hF'.comp_hasDerivAt 0 hl
  have hcomp : ∀ q, Tendsto (fun t : ℂ => t⁻¹ * (σ q (vP + t • h0) / wz (vP + t • h0))) (𝓝[≠] 0)
      (𝓝 ((fderiv ℂ (fun v => (WithLp.toLp 2 (fun k => σ k v / wz v) : V n)) vP h0) q)) := by
    intro q
    have h2 := ((PiLp.continuous_apply 2 (fun _ : Fin n => ℂ) q).tendsto _).comp
      (hasDerivAt_iff_tendsto_slope.1 hFl)
    refine h2.congr' (Filter.Eventually.of_forall fun t => ?_)
    simp [slope_def_module, hσ0]
  have hlim : Tendsto (fun t : ℂ => ∑ α ∈ M, ((∑ k, c α k * Φ k (vP + t • h0)) * t ^ (∑ q, α q - d) *
        wz (vP + t • h0) ^ (∑ q, α q + (T - ∑ q, α q))) *
        ∏ q, (t⁻¹ * (σ q (vP + t • h0) / wz (vP + t • h0))) ^ α q) (𝓝[≠] 0)
      (𝓝 (∑ α ∈ M, ((∑ k, c α k * Φ k vP) * 0 ^ (∑ q, α q - d) *
        wz vP ^ (∑ q, α q + (T - ∑ q, α q))) *
        ∏ q, (fderiv ℂ (fun v => WithLp.toLp 2 (fun k => σ k v / wz v)) vP h0) q ^ α q)) := by
    refine tendsto_finsetSum _ fun α _ => ?_
    refine Tendsto.mul (Tendsto.mul (Tendsto.mul ?_ ?_) ?_) ?_
    · exact tendsto_finsetSum _ fun k _ => ((hΦc k).tendsto.comp hl1).const_mul _
    · exact ((continuous_pow _).tendsto (0 : ℂ)).mono_left nhdsWithin_le_nhds
    · exact (hwd.continuousAt.tendsto.comp hl1).pow _
    · exact tendsto_finsetProd _ fun q _ => (hcomp q).pow _
  have hwne : ∀ᶠ t in 𝓝[≠] (0 : ℂ), wz (vP + t • h0) ≠ 0 :=
    (hwd.continuousAt.tendsto.comp hl1).eventually_ne hw0
  have heq : (fun t : ℂ => (∑ α ∈ M, ∑ k, c α k * (∏ q, σ q (vP + t • h0) ^ α q) *
        wz (vP + t • h0) ^ (T - ∑ q, α q) * Φ k (vP + t • h0)) / t ^ d) =ᶠ[𝓝[≠] 0]
      (fun t : ℂ => ∑ α ∈ M, ((∑ k, c α k * Φ k (vP + t • h0)) * t ^ (∑ q, α q - d) *
        wz (vP + t • h0) ^ (∑ q, α q + (T - ∑ q, α q))) *
        ∏ q, (t⁻¹ * (σ q (vP + t • h0) / wz (vP + t • h0))) ^ α q) := by
    filter_upwards [hwne, self_mem_nhdsWithin] with t hwt ht
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun α hα => ?_
    rw [sum_mul_pow_mul_prod_eq_div_pow α (c α) (fun k => Φ k (vP + t • h0)) (fun q => σ q (vP + t • h0))
      (wz (vP + t • h0)) t T d ht hwt (fun ⟨k, hk⟩ => hlow α hα k hk)]
  obtain ⟨C, hC⟩ := hb
  have hzero : Tendsto (fun t : ℂ => (∑ α ∈ M, ∑ k, c α k * (∏ q, σ q (vP + t • h0) ^ α q) *
        wz (vP + t • h0) ^ (T - ∑ q, α q) * Φ k (vP + t • h0)) / t ^ d) (𝓝[≠] 0) (𝓝 0) := by
    have hbd : ∀ᶠ t in 𝓝[≠] (0 : ℂ), ‖(∑ α ∈ M, ∑ k, c α k * (∏ q, σ q (vP + t • h0) ^ α q) *
        wz (vP + t • h0) ^ (T - ∑ q, α q) * Φ k (vP + t • h0)) / t ^ d‖ ≤
        C * ‖h0‖ ^ m * ‖t‖ ^ (m - d) := by
      filter_upwards [hl1.eventually hC, self_mem_nhdsWithin] with t h1 ht
      have htn : 0 < ‖t‖ := norm_pos_iff.2 ht
      rw [add_sub_cancel_left, norm_smul] at h1
      rw [norm_div, norm_pow, div_le_iff₀ (pow_pos htn d)]
      calc _ ≤ C * (‖t‖ * ‖h0‖) ^ m := h1
        _ = C * ‖h0‖ ^ m * ‖t‖ ^ (m - d) * ‖t‖ ^ d := by
          rw [mul_pow, show ‖t‖ ^ m = ‖t‖ ^ (m - d) * ‖t‖ ^ d by
            rw [← pow_add, Nat.sub_add_cancel hdm.le]]
          ring
    refine squeeze_zero_norm' hbd ?_
    have h3 : Tendsto (fun t : ℂ => C * ‖h0‖ ^ m * ‖t‖ ^ (m - d)) (𝓝 0) (𝓝 (C * ‖h0‖ ^ m * ‖(0 : ℂ)‖ ^ (m - d))) :=
      ((continuous_norm.pow _).const_mul _).tendsto 0
    rw [norm_zero, zero_pow (Nat.sub_ne_zero_of_lt hdm), mul_zero] at h3
    exact h3.mono_left nhdsWithin_le_nhds
  exact tendsto_nhds_unique hlim (hzero.congr' heq)

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private theorem coeff_eq_zero_of_monomial_sum_eq_zero {n : ℕ} (M : Finset (Fin n → ℕ)) (B : (Fin n → ℕ) → ℂ)
    (h : ∀ y : V n, ∑ α ∈ M, B α * ∏ q, y q ^ α q = 0) : ∀ α ∈ M, B α = 0 := by
  classical
  let P : MvPolynomial (Fin n) ℂ :=
    ∑ α ∈ M, MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm α) (B α)
  have hP : P = 0 := by
    apply MvPolynomial.funext
    intro y
    have hy := h (WithLp.toLp 2 y)
    simp only at hy
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [P, map_zero, map_sum, MvPolynomial.eval_monomial]
    rw [← hy]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
    simp
  intro α hα
  have hc := congrArg (AddMonoidAlgebra.coeff · (Finsupp.equivFunOnFinite.symm α)) hP
  simp only [P, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, MvPolynomial.coeff_zero,
    (Finsupp.equivFunOnFinite).symm.injective.eq_iff] at hc
  rwa [Finset.sum_ite_eq' M α B, if_pos hα] at hc

theorem leadM_coeff_eq_zero : ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (G : Wt X.Ψ r) (T a δ : ℕ),
    ∀ (t : Fin δ → Frame X.Ψ r → ℂ), (∀ k, X.IsSec G (t k)) →
    (∀ u : Fin δ → ℂ, (∀ j, ∑ k, u k * t k (Fl.xs j) = 0) → u = 0) →
    ∀ cc : (Fin (nd X) → ℕ) → Fin δ → ℂ,
      (∀ j, (fun z : V (nd X) => leadM X Fl.s Fl.w0 t T a cc (cpt X (Fl.xs j) z)) =O[𝓝 0] fun z => ‖z‖ ^ a) →
      ∀ α ∈ multiLt (nd X) a, ∀ k, cc α k = 0 := by
  classical
  intro r X Xa Fl G T a δ t ht hind cc hO
  by_contra hne
  push Not at hne
  obtain ⟨α1, hα1, k1, hk1⟩ := hne
  set S := (multiLt (nd X) a).filter (fun α => ∃ k, cc α k ≠ 0) with hSdef
  have hS : S.Nonempty := ⟨α1, Finset.mem_filter.2 ⟨hα1, k1, hk1⟩⟩
  obtain ⟨α0, hα0S, hα0d⟩ := Finset.exists_mem_eq_inf' hS (fun α => ∑ q, α q)
  set d := S.inf' hS (fun α => ∑ q, α q) with hd
  have hα0M := (Finset.mem_filter.1 hα0S).1
  have hlow : ∀ α ∈ multiLt (nd X) a, ∀ k, cc α k ≠ 0 → d ≤ ∑ q, α q := fun α hα k hk =>
    Finset.inf'_le _ (Finset.mem_filter.2 ⟨hα, k, hk⟩)
  have hda : d < a := hα0d ▸ mem_multiLt.1 hα0M
  have key : ∀ j, ∀ α ∈ multiLt (nd X) a, ∑ q, α q = d → ∑ k, cc α k * t k (Fl.xs j) = 0 := by
    intro j
    have hdomo := ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain.isOpen_dom X
    have hcd : Differentiable ℂ (cpt X (Fl.xs j)) :=
      (ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB.cd_cpt X (Fl.xs j)).differentiable (by simp)
    have hc0 : cpt X (Fl.xs j) 0 = Fl.xs j := ReciprocityTheory.ChartRestriction.G.AR.Up.IW.cpt_zero X (Fl.xs j)
    have hUo : IsOpen (cpt X (Fl.xs j) ⁻¹' X.dom) := hdomo.preimage hcd.continuous
    have h0U : (0 : V (nd X)) ∈ cpt X (Fl.xs j) ⁻¹' X.dom := by
      simp only [Set.mem_preimage, hc0]
      exact Fl.xs_mem j
    have hcomp : ∀ P : Frame X.Ψ r → ℂ, DifferentiableOn ℂ P X.dom →
        DifferentiableOn ℂ (fun z => P (cpt X (Fl.xs j) z)) (cpt X (Fl.xs j) ⁻¹' X.dom) :=
      fun P hP z hz => ((hP.differentiableAt (hdomo.mem_nhds hz)).comp z
        (hcd z)).differentiableWithinAt
    have hs0 : ∀ k, Fl.s k (Fl.xs j) = 0 := by
      refine (Fl.S_eq (Fl.xs j) (Fl.xs_mem j)).2 ⟨j, 1, X.Γ.one_mem, nmat X 0, ?_, ?_⟩
      · intro τ
        have hm := ReciprocityTheory.ChartRestriction.G.AR.Up.IW.nmat_zero X τ
        refine ⟨by rw [hm]; simp, fun p c hpc => ?_⟩
        have := congrFun (congrFun hm p) c
        simp only [mat, Matrix.of_apply] at this
        rw [this, Matrix.one_apply_ne (ne_of_gt hpc)]
      · have hr : rmul (Fl.xs j) (nmat X 0) = Fl.xs j := hc0
        rw [hr]
        funext τ
        simp [lact, mat, Matrix.map_one]
        rfl
    have main := fun h0 => lowest_degree (cpt X (Fl.xs j) ⁻¹' X.dom) hUo 0 h0U
      (fun q z => Fl.s q (cpt X (Fl.xs j) z)) (fun z => Fl.w0 (cpt X (Fl.xs j) z))
      (fun k z => t k (cpt X (Fl.xs j) z)) (multiLt (nd X) a) T a d cc
      (fun q => hcomp _ (Fl.s_van q).1.1.1.1) (hcomp _ Fl.weightForm_vanishes.1.1.1.1)
      (fun k => hcomp _ (ht k).1) (fun q => by simp only [hc0, hs0])
      (by simp only [hc0]; exact Fl.w0_ne j) hlow hda
      (by
        obtain ⟨C, hC⟩ := (hO j).bound
        refine ⟨C, hC.mono fun z hz => ?_⟩
        simpa [leadM, monoM, norm_pow] using hz) h0
    simp only [hc0] at main
    have hsurj := ((Module.End.isUnit_iff _).1 ((LinearMap.isUnit_iff_isUnit_det _).2
      (isUnit_iff_ne_zero.2 (Fl.coord j)))).2
    have hB := coeff_eq_zero_of_monomial_sum_eq_zero (multiLt (nd X) a)
      (fun α => (∑ k, cc α k * t k (Fl.xs j)) * 0 ^ (∑ q, α q - d) *
        Fl.w0 (Fl.xs j) ^ (∑ q, α q + (T - ∑ q, α q))) (fun y => by
          obtain ⟨h0, hh0⟩ := hsurj y
          have := main h0
          rw [← hh0]
          exact this)
    intro α hα hαd
    have := hB α hα
    rw [hαd, Nat.sub_self, pow_zero, mul_one] at this
    exact (mul_eq_zero.1 this).resolve_right (pow_ne_zero _ (Fl.w0_ne j))
  have hu : cc α0 = 0 := hind (cc α0) (fun j => key j α0 hα0M hα0d.symm)
  obtain ⟨k, hk⟩ := (Finset.mem_filter.1 hα0S).2
  exact hk (congrFun hu k)

end GlobalTheory.LeadIndep
end
