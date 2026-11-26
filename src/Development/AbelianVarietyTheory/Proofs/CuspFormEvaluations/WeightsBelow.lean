module

public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfReducedInputs
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.EvaluationLemmaForNablaLevels
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LiftIndexPowFourLeDegree
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.WeightsBelow
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn

namespace GlobalTheory.RunWeights

theorem size_le_mul {D : D7} {j : ℕ} (x z : WeightFamilies.Wt D j) (c : ℕ) (hc : 1 ≤ c)
    (h1 : ∀ τ i, x.aP τ i ≤ c * z.aP τ i) (h2 : ∀ τ i, x.aM τ i ≤ c * z.aM τ i) (h3 : x.n ≤ c * z.n) :
    x.size ≤ (c : ℝ) * z.size := by
  have hK : (0 : ℝ) ≤ (D.R.f : ℝ) * ((max (D.R.sigW j).2 1 : ℕ) : ℝ) * (D.R.r : ℝ) := by positivity
  have hc1 : (1 : ℝ) ≤ c := by exact_mod_cast hc
  have hS : (∑ τ, ((∑ i, (x.aP τ i : ℝ)) + ∑ i, (x.aM τ i : ℝ))) ≤
      (c : ℝ) * ∑ τ, ((∑ i, (z.aP τ i : ℝ)) + ∑ i, (z.aM τ i : ℝ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun τ _ => ?_
    rw [mul_add, Finset.mul_sum, Finset.mul_sum]
    refine add_le_add (Finset.sum_le_sum fun i _ => ?_) (Finset.sum_le_sum fun i _ => ?_)
    · exact_mod_cast h1 τ i
    · exact_mod_cast h2 τ i
  have hn : (x.n : ℝ) ≤ (c : ℝ) * z.n := by exact_mod_cast h3
  have hKn := mul_le_mul_of_nonneg_left hn hK
  unfold WeightFamilies.Wt.size
  nlinarith

theorem DF_le {D : D7} {j : ℕ} (x z : WeightFamilies.Wt D j)
    (h1 : ∀ τ i, x.aP τ i ≤ z.aP τ i) (h2 : ∀ τ i, x.aM τ i ≤ z.aM τ i) : WeightAlgebra.DF x ≤ WeightAlgebra.DF z := by
  unfold WeightAlgebra.DF WeightAlgebra.degP
  exact Finset.sum_le_sum fun τ _ =>
    add_le_add (Finset.sum_le_sum fun i _ => h1 τ i) (Finset.sum_le_sum fun i _ => h2 τ i)

theorem weights_below : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), 1 ≤ j → FamilyHypotheses.HypPage large₂ X H C2 A2 CR CT ka wL wF Tn nP nW h0 → (∀ w ∈ ({wL, wF, X.wF0 wL wF, ka} : Set (WeightFamilies.Wt D j)), WeightAlgebra.DF w ≤ WeightAlgebra.DF ka ∧ w.n ≤ ka.n ∧ D.R.r ≤ w.n ∧ w.LastPos) ∧ (∀ w ∈ ({wF, X.wF0 wL wF, ka} : Set (WeightFamilies.Wt D j)), 8 * D.R.f * D.R.r + 4 ≤ w.n) ∧ (∀ w2, IsG2 wL wF w2 → WeightAlgebra.DF w2 ≤ WeightAlgebra.DF ka ∧ w2.n ≤ ka.n ∧ w2.size ≤ ((WeightFamilies.dimY D j : ℝ) + 4) * wL.size) ∧ (∀ w1, IsDoubledWeightWithShift wL w1 nW → WeightAlgebra.DF w1 ≤ WeightAlgebra.DF ka ∧ w1.n ≤ ka.n ∧ w1.size ≤ 2 * wL.size) := by
  intro D B P j X large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hj hH
  unfold FamilyHypotheses.HypPage at hH
  obtain ⟨_, hSet, _, _, _⟩ := hH
  unfold SetC at hSet
  obtain ⟨hkan, _, _, hh0, _, hlastP, _, _, _, hnP8, hnPW, _, _, hnV, hL, hF, _, hT0, hDT, h40, hDnW,
    h40n, _, _, _, hDom⟩ := hSet
  obtain ⟨hLn, hLP, _⟩ := hL
  obtain ⟨hFn, hFP, hFM⟩ := hF

  have kaP : ∀ τ i, ka.aP τ i = Tn * wL.aP τ i + wF.aP τ i := fun τ i => by
    have e := hFP τ i
    have e' : ((ka.aP τ i : ℕ) : ℤ) = ((Tn * wL.aP τ i + wF.aP τ i : ℕ) : ℤ) := by push_cast; linarith
    exact_mod_cast e'
  have kaM : ∀ τ i, ka.aM τ i = Tn * wL.aM τ i + wF.aM τ i := fun τ i => by
    have e := hFM τ i
    have e' : ((ka.aM τ i : ℕ) : ℤ) = ((Tn * wL.aM τ i + wF.aM τ i : ℕ) : ℤ) := by push_cast; linarith
    exact_mod_cast e'
  have kan : ka.n = nP + Tn * nW := by rw [hkan, hnV]
  have f0P : ∀ τ i, (X.wF0 wL wF).aP τ i = wF.aP τ i + WeightFamilies.dimY D j * wL.aP τ i := fun _ _ => rfl
  have f0M : ∀ τ i, (X.wF0 wL wF).aM τ i = wF.aM τ i + WeightFamilies.dimY D j * wL.aM τ i := fun _ _ => rfl
  have f0n : (X.wF0 wL wF).n = wF.n + WeightFamilies.dimY D j * wL.n := rfl
  have hT1 : 1 ≤ Tn := hT0
  have hT2 : 2 ≤ Tn := by omega
  have hD4 : WeightFamilies.dimY D j + 4 ≤ Tn := by omega

  have hf : 0 < D.R.f := by
    obtain ⟨hC, hCZ, _⟩ := hDom
    have hZ : (0 : ℝ) < Zb D large₂ := lt_of_lt_of_le (by positivity) hCZ
    unfold Zb at hZ
    rcases Nat.eq_zero_or_pos D.R.f with h | h
    · simp [h] at hZ
    · exact h
  have hrP : D.R.r ≤ nP := by
    have e : 8 * D.R.f * D.R.r = 8 * (D.R.f * D.R.r) := by ring
    have := Nat.mul_le_mul hf (le_refl D.R.r)
    omega

  have leKa : ∀ w : WeightFamilies.Wt D j, (∀ τ i, w.aP τ i ≤ ka.aP τ i) → (∀ τ i, w.aM τ i ≤ ka.aM τ i) →
      WeightAlgebra.DF w ≤ WeightAlgebra.DF ka := fun w a b => DF_le w ka a b

  have kaLast : ∀ τ (i : Fin (D.R.sigW j).1), i.1 + 1 = (D.R.sigW j).1 → 2 * Tn * Tn ≤ ka.aP τ i := by
    intro τ i hi
    have e := hlastP τ i hi
    have e' : (2 * (Tn : ℝ) * Tn) ≤ ka.aP τ i := by nlinarith
    exact_mod_cast e'

  have wLLast : ∀ τ (i : Fin (D.R.sigW j).1), i.1 + 1 = (D.R.sigW j).1 →
      1 ≤ wL.aP τ i ∧ ((Tn + WeightFamilies.dimY D j + 2 : ℕ) : ℤ) * wL.aP τ i ≤
        (ka.aP τ i : ℤ) - ((WeightFamilies.dimY D j : ℤ) + 2) * nW - 2 * D.R.r := by
    intro τ i hi
    have e := hLP τ i
    unfold gapZ at e
    rw [dite_eq_right (by omega), if_neg (by omega)] at e
    unfold Tp at e
    have hb : (0 : ℤ) < ((Tn + WeightFamilies.dimY D j + 2 : ℕ) : ℤ) := by positivity
    rw [Int.fdiv_eq_ediv, if_pos (Or.inl hb.le), sub_zero] at e
    have hk := kaLast τ i hi
    have hTT := Nat.mul_le_mul hT2 (le_refl Tn)
    constructor
    · have : (1 : ℤ) ≤ (wL.aP τ i : ℤ) := by
        rw [e, Int.le_ediv_iff_mul_le hb]
        have hk' : ((2 * Tn * Tn : ℕ) : ℤ) ≤ (ka.aP τ i : ℤ) := by exact_mod_cast hk
        have hTT' : ((2 * Tn : ℕ) : ℤ) ≤ ((Tn * Tn : ℕ) : ℤ) := by exact_mod_cast hTT
        have hDnW' : (((WeightFamilies.dimY D j + 2) * nW + 2 * D.R.r : ℕ) : ℤ) ≤ (Tn : ℤ) := by exact_mod_cast hDnW
        have hDT' : ((WeightFamilies.dimY D j : ℕ) : ℤ) ≤ (Tn : ℤ) := by exact_mod_cast hDT
        push_cast at hk' hTT' hDnW' hDT' ⊢
        nlinarith
      exact_mod_cast this
    · rw [e]
      exact Int.mul_ediv_self_le hb.ne'
  have wFLast : ∀ τ (i : Fin (D.R.sigW j).1), i.1 + 1 = (D.R.sigW j).1 → 1 ≤ wF.aP τ i := by
    intro τ i hi
    obtain ⟨_, h2⟩ := wLLast τ i hi
    have e := hFP τ i
    have h0' : (0 : ℤ) ≤ (WeightFamilies.dimY D j : ℤ) * wL.aP τ i := by positivity
    have h1' : (0 : ℤ) ≤ (WeightFamilies.dimY D j : ℤ) * nW := by positivity
    have h40' : (40 : ℤ) ≤ nW := by exact_mod_cast h40n
    have : (1 : ℤ) ≤ (wF.aP τ i : ℤ) := by
      push_cast at h2
      nlinarith
    exact_mod_cast this
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · refine ⟨leKa _ (fun τ i => ?_) (fun τ i => ?_), ?_, ?_, ?_⟩
      · have := Nat.mul_le_mul hT1 (le_refl (w.aP τ i)); rw [kaP]; omega
      · have := Nat.mul_le_mul hT1 (le_refl (w.aM τ i)); rw [kaM]; omega
      · have := Nat.mul_le_mul hT1 (le_refl nW); rw [kan, hLn]; omega
      · rw [hLn]; omega
      · intro τ i hi; exact (wLLast τ i hi).1
    · refine ⟨leKa _ (fun τ i => ?_) (fun τ i => ?_), ?_, ?_, ?_⟩
      · rw [kaP]; omega
      · rw [kaM]; omega
      · rw [kan, hFn]; omega
      · rw [hFn]; omega
      · intro τ i hi; exact wFLast τ i hi
    · refine ⟨leKa _ (fun τ i => ?_) (fun τ i => ?_), ?_, ?_, ?_⟩
      · have := Nat.mul_le_mul hDT (le_refl (wL.aP τ i)); rw [kaP, f0P]; omega
      · have := Nat.mul_le_mul hDT (le_refl (wL.aM τ i)); rw [kaM, f0M]; omega
      · have := Nat.mul_le_mul hDT (le_refl nW); rw [kan, f0n, hFn, hLn]; omega
      · rw [f0n, hFn]; omega
      · intro τ i hi
        have := wFLast τ i hi
        rw [f0P]; omega
    · refine ⟨le_refl _, le_refl _, ?_, ?_⟩
      · rw [kan]; omega
      · intro τ i hi
        have := kaLast τ i hi
        have hTT := Nat.mul_le_mul hT2 hT1
        have e : 2 * Tn * Tn = 2 * (Tn * Tn) := by ring
        omega
  · intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl
    · rw [hFn]; omega
    · rw [f0n, hFn]; omega
    · rw [kan]; omega
  · intro w2 hw2
    obtain ⟨h2n, h2P, h2M⟩ := hw2
    have bP : ∀ τ i, w2.aP τ i ≤ (WeightFamilies.dimY D j + 4) * wL.aP τ i := fun τ i => by
      have := h2P τ i; omega
    have bM : ∀ τ i, w2.aM τ i ≤ (WeightFamilies.dimY D j + 4) * wL.aM τ i := fun τ i => by
      have := h2M τ i; omega
    have bn : w2.n ≤ (WeightFamilies.dimY D j + 4) * wL.n := by omega
    refine ⟨leKa _ (fun τ i => ?_) (fun τ i => ?_), ?_, ?_⟩
    · have := Nat.mul_le_mul hD4 (le_refl (wL.aP τ i)); have := bP τ i; rw [kaP]; omega
    · have := Nat.mul_le_mul hD4 (le_refl (wL.aM τ i)); have := bM τ i; rw [kaM]; omega
    · have := Nat.mul_le_mul hD4 (le_refl nW); rw [kan]; rw [hLn] at bn; omega
    · have := size_le_mul w2 wL (WeightFamilies.dimY D j + 4) (by omega) bP bM bn
      push_cast at this
      exact this
  · intro w1 hw1
    obtain ⟨h1n, h1P, h1M⟩ := hw1
    have bn : w1.n ≤ 2 * wL.n := by omega
    refine ⟨leKa _ (fun τ i => ?_) (fun τ i => ?_), ?_, ?_⟩
    · have := Nat.mul_le_mul hT2 (le_refl (wL.aP τ i)); have := h1P τ i; rw [kaP]; omega
    · have := Nat.mul_le_mul hT2 (le_refl (wL.aM τ i)); have := h1M τ i; rw [kaM]; omega
    · have := Nat.mul_le_mul hT2 (le_refl nW); rw [kan]; rw [hLn] at bn; omega
    · have := size_le_mul w1 wL 2 (by norm_num) (fun τ i => (h1P τ i).le) (fun τ i => (h1M τ i).le) bn
      push_cast at this
      exact this

end GlobalTheory.RunWeights
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortValTotOfPinned
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShortDescent

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

def oneSim (D : Datum H) : Sim D where
  f _ := LinearMap.id
  ν _ := 1
  tower _ _ _ _ _ := ⟨0, by simp⟩
  inv _ _ := ⟨LinearMap.id, fun _ => ⟨⟨0, by simp⟩, ⟨0, by simp⟩⟩⟩
  mult _ _ _ _ := by simp

variable {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ}

theorem evR_eq_of_point_eq (d : DeltaDat Xo c n) {ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ} (hψ : d.PsiTie ψ)
    {k : Type} [Field k] [IsAlgClosed k] [Algebra d.c₂.F k] (y y' : FrPt d.Xo₂ d.c₂ k) (h : y'.x = y.x) :
    evR d.Xo₂ d.c₂ d.cδ y' = evR d.Xo₂ d.c₂ d.cδ y := by
  have e := hψ 1 (oneSim Dw) (Iso.refl _)
    ⟨by simp [oneSim], fun a => by simp [oneSim], fun a => ⟨0, by simp [oneSim]⟩⟩
    (fun a => ⟨0, by simp [oneSim]⟩)
    ⟨Category.id_comp _, GlobalTheory.LevelTwist.sabMapId _,
      fun _ => (Category.comp_id _).trans (Category.id_comp _).symm,
      fun _ => (Category.comp_id _).trans (Category.id_comp _).symm⟩
    (fun _ => rfl) k y y' (h.trans (Category.comp_id _).symm)
  simpa using e

theorem map_wchar {J : Type} [Fintype J] {K S T : Type} [Field K] [CommRing S] [Algebra K S] [CommRing T] [Algebra K T]
    (χ : S →ₐ[K] T) (e : J → ℕ) (t : J → Sˣ) :
    χ (wchar e t) = wchar e (fun i => Units.map (χ : S →* T) (t i)) := by
  simp [wchar, map_prod, map_pow]

end GlobalTheory.ShortDescent

namespace GlobalTheory


open ShortDescent in
theorem shortValTot_of_pinned : Laws → ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), @ToroidalLevelCompatibility E _ _ _ H Dw → EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) → AllTest Xo c → EvalWD (K := d.c₂.F) (fun S _ _ => FrPt d.Xo₂ d.c₂ S) (fun φ y z => FrMap φ y z) → AllTest d.Xo₂ d.c₂ → d.IsLev → d.l₂.A = l.A → (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) → (Dw.p + Dw.q ≤ n → ∃ ph ψ x₀, d.PhiPin ph ψ x₀ ∧ d.PsiTie ψ) → ∀ (nab : NabV Xo c) (bad nV : ℕ) (a : (E →+* ℂ) × ℕ → ℕ), ShortValTot Xo c nab bad nV a n d := by
  intro hL hC E _ _ _ H Dw l Xo c n d hN _ hAll hW₂ hAll₂ hLev hA hnab hpin nab bad nV a Λ N x0 P hU _ hT hO hX hP
  obtain ⟨_, hnab⟩ := hnab
  obtain ⟨hle, hmap⟩ := GlobalTheory.admissible_columns_le_and_harmonic_map_cover E H Dw l Xo c n d
  have hpin' := hpin (hle _ _ hX)
  have hP₂ := hmap a P hP.1
  obtain ⟨hex, -⟩ := GlobalTheory.T.shortThetaValue_existsUnique_natural_of_laws hL hC E H Dw d.l₂ d.Xo₂ d.c₂ d.nab₂ hnab n Λ N hU hT hO a _ hP₂ (d.w x0)
    (d.eF (betaH (Dw := Dw) c Λ))
  have hd := GlobalTheory.T.evaluation_lemma_for_nabla_levels hL hC E H Dw l Xo c n d hW₂ hAll₂ hN hLev hA hnab hpin' Λ N hU hT hO a _ hP₂ x0
    (d.eF (betaH (Dw := Dw) c Λ))
  obtain ⟨hlift, -, hbor⟩ := GlobalTheory.T.framedPoints_lift_to_levelCover hL E H Dw l Xo c n d
  obtain ⟨_, ψ, _, -, hψ⟩ := hpin'
  refine ⟨hex, fun p y => (hd p y).exists.choose, ⟨fun p q φ y z h => ?_, fun p t y y' h => ?_⟩, ?_⟩
  · refine (hd q z).unique (hd q z).exists.choose_spec ?_
    intro k _ _ _ _ hk χ w w₂ hw ho v hv
    exact (hd p y).exists.choose_spec k hk (χ.comp φ) w w₂ (GlobalTheory.FramedBaseChange.trans φ χ h hw) ho v hv
  · refine (hd p y').unique (hd p y').exists.choose_spec ?_
    intro k _ _ _ _ hk χ w' w₂' hw' ho' v' hv'
    obtain ⟨w, hw⟩ := GlobalTheory.FramedBaseChange.exists_frMap hL E H Dw l Xo c p.R k χ y
    have hb := frBorBC _ _ χ t y y' w w' h hw hw'
    obtain ⟨w₂, hx₂, ho⟩ := hlift k hk w w₂'.x (ho'.1.trans hb.1) w₂'.x_over
    have hb₂ := hbor k hk _ w w' w₂ w₂' ho ho' hx₂.symm hb
    obtain ⟨v, hv, -⟩ := hex k w₂
    have hv₂ := (GlobalTheory.thetaValue_weight hL hC E H Dw d.l₂ d.Xo₂ d.c₂ d.nab₂ hnab k w₂ w₂' _ hb₂ n a _).2 hP₂
      _ Λ _ N v hv
    have e := (hd p y).exists.choose_spec k hk χ w w₂ hw ho v hv
    rw [(hex k w₂').unique hv' hv₂, map_mul, map_wchar, evR_eq_of_point_eq d hψ w₂ w₂' hx₂.symm]
    refine (congrArg (_ * ·) e).trans ?_
    ring
  · intro k _ _ _ _ hk y y₂ ho
    obtain ⟨v, hv, -⟩ := hex k y₂
    refine ⟨v, hv, ?_⟩
    have hy := hAll k y
    unfold evR evalAt
    rw [dite_eq_left hy]
    exact (hd _ _).exists.choose_spec k hk _ y y₂ hy.choose_spec.choose_spec.choose_spec ho v hv

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ComponentModelWeightDimensionDictionary
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ComponentModelWeightDimensionDictionary
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares

noncomputable section

namespace GlobalTheory.Shares.WtDic

variable {D : D7}

theorem tauEmb_inj {t t' : D.what₂.Tau} (h : DV.tauEmb D t = DV.tauEmb D t') : t = t' :=
  D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))

theorem conjEmb_conjEmb {E : Type} [Field E] (τ : E →+* ℂ) : conjEmb (conjEmb τ) = τ :=
  RingHom.ext fun x => by simp [conjEmb]

theorem tauEmb_ne_conj (t t' : D.what₂.Tau) : DV.tauEmb D t ≠ conjEmb (DV.tauEmb D t') := by
  intro h
  have h1 : conjEmb (DV.tauEmb D t') =
      D.host.emb (((D.eTau t' : D.R.Psi) : D.R.GG) * D.R.cc) := by
    rw [Formalism.L2.Geo.emb_mul_cc_comp]
    refine RingHom.ext fun x => ?_
    exact (Formalism.MainNotions.WeightFamilies.emb_conj D (DV.tauEmb D t') x).symm
  have h2 := (Formalism.L2.Geo.exists_tauEmb_iff D _).1 ⟨t, (h.trans h1).symm⟩
  exact (Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem _).1 (D.eTau t').2 h2

theorem wtA_tau {j : ℕ} (w : WeightFamilies.Wt D j) (t : D.what₂.Tau) (i : ℕ) :
    wtA w (DV.tauEmb D t, i) = ext0 (w.aP t) i := by
  classical
  unfold wtA
  rw [Finset.sum_eq_single t]
  · simp [tauEmb_ne_conj]
  · intro t' _ ht'
    have : DV.tauEmb D t ≠ DV.tauEmb D t' := fun h => ht' (tauEmb_inj h).symm
    simp [tauEmb_ne_conj, this]
  · simp

theorem wtA_conj {j : ℕ} (w : WeightFamilies.Wt D j) (t : D.what₂.Tau) (i : ℕ) :
    wtA w (conjEmb (DV.tauEmb D t), i) = ext0 (w.aM t) i := by
  classical
  unfold wtA
  rw [Finset.sum_eq_single t]
  · simp [(tauEmb_ne_conj _ _).symm]
  · intro t' _ ht'
    have : conjEmb (DV.tauEmb D t) ≠ conjEmb (DV.tauEmb D t') := fun h => ht' (tauEmb_inj (by
      have := congrArg conjEmb h
      rwa [conjEmb_conjEmb, conjEmb_conjEmb] at this)).symm
    simp [(tauEmb_ne_conj _ _).symm, this]
  · simp

theorem matrixExtendByZero_mul {p : ℕ} (c : ℕ) (f : Fin p → ℕ) (i : ℕ) : ext0 (fun k => c * f k) i = c * ext0 f i := by
  unfold ext0; split_ifs <;> rfl

theorem wtA_wsmul {j : ℕ} (c : ℕ) (w : WeightFamilies.Wt D j) (x : (D.host.E →+* ℂ) × ℕ) :
    wtA (wsmul c w) x = c * wtA w x := by
  simp only [wtA, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  have h1 : ext0 ((wsmul c w).aP t) x.2 = c * ext0 (w.aP t) x.2 := matrixExtendByZero_mul _ _ _
  have h2 : ext0 ((wsmul c w).aM t) x.2 = c * ext0 (w.aM t) x.2 := matrixExtendByZero_mul _ _ _
  rw [h1, h2]
  split_ifs <;> ring

theorem wtA_wscalar (j n : ℕ) (hn : Even n) (x : (D.host.E →+* ℂ) × ℕ) : wtA (wscalar D j n hn) x = 0 := by
  simp only [wtA]
  refine Finset.sum_eq_zero fun t _ => ?_
  have h1 : ext0 ((wscalar D j n hn).aP t) x.2 = 0 := by unfold ext0; split_ifs <;> rfl
  have h2 : ext0 ((wscalar D j n hn).aM t) x.2 = 0 := by unfold ext0; split_ifs <;> rfl
  rw [h1, h2]
  simp

theorem laR_wadd (T : Top D) (j : ℕ) (k : (T.U j T.σ₀).Comp) (u u' : WeightFamilies.Wt D j) :
    laR T j (wadd u u') k = laR T j u k + laR T j u' k := by
  funext τ a
  have hn : (wadd u u').n / 2 = u.n / 2 + u'.n / 2 := by
    have h1 := u.n_even
    have h2 := u'.n_even
    rw [n_wadd]
    rw [Nat.even_iff] at h1 h2
    omega
  simp only [laR, laU, Pi.add_apply, wtA_wadd, hn]
  split_ifs <;> push_cast <;> ring

theorem laR_wsmul (T : Top D) (j : ℕ) (k : (T.U j T.σ₀).Comp) (m : ℕ) (u : WeightFamilies.Wt D j) :
    laR T j (wsmul m u) k = m • laR T j u k := by
  funext τ a
  have hn : (wsmul m u).n / 2 = m * (u.n / 2) := by
    obtain ⟨s, hs⟩ := u.n_even
    show m * u.n / 2 = _
    rw [hs, ← two_mul, Nat.mul_div_cancel_left _ two_pos, Nat.mul_left_comm, Nat.mul_div_cancel_left _ two_pos]
  simp only [laR, laU, Pi.smul_apply, wtA_wsmul, hn, nsmul_eq_mul]
  split_ifs <;> push_cast <;> ring

theorem card_lower (r : ℕ) : Fintype.card {p : Fin r × Fin r // p.2 < p.1} = r * (r - 1) / 2 := by
  have e : {p : Fin r × Fin r // p.2 < p.1} ≃ Σ a : Fin r, Finset.Iio a :=
    { toFun := fun p => ⟨p.1.1, p.1.2, Finset.mem_Iio.2 p.2⟩
      invFun := fun x => ⟨(x.1, x.2.1), Finset.mem_Iio.1 x.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  simp only [Fintype.card_coe, Fin.card_Iio]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) r, Finset.sum_range_id]

theorem choose_split (p q : ℕ) : (p + q) * (p + q - 1) / 2 = p * q + p * (p - 1) / 2 + q * (q - 1) / 2 := by
  rw [← Nat.choose_two_right, ← Nat.choose_two_right, ← Nat.choose_two_right]
  induction q with
  | zero => simp
  | succ q ih =>
    rw [← add_assoc, Nat.choose_succ_succ' (p + q) 1, Nat.choose_succ_succ' q 1, ih]
    simp only [Nat.choose_one_right]
    ring

theorem weights_dictionary : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (k : (T.U j T.σ₀).Comp), (∀ u u' : WeightFamilies.Wt D j, laR T j (wadd u u') k = laR T j u k + laR T j u' k) ∧ (∀ (m : ℕ) (u : WeightFamilies.Wt D j), laR T j (wsmul m u) k = m • laR T j u k) ∧ (∀ (u v : WeightFamilies.Wt D j) (m : ℕ), laR T j (addL u v m) k = laR T j u k + m • laR T j v k) ∧ (∀ i : ℕ, laR T j (etWt D j i) k = (i * (g0 D / 2)) • de2W ((T.U j T.σ₀).X k)) ∧ nd ((T.U j T.σ₀).X k) = WeightFamilies.dimY D j ∧ ((T.U j T.σ₀).X k).p0 = (D.R.sigW j).2 ∧ ((T.U j T.σ₀).X k).Ψ.card = D.R.f ∧ ∃ tt : ((T.U j T.σ₀).X k).Ψ ≃ D.what₂.Tau, ∀ (u : WeightFamilies.Wt D j) (τ : ((T.U j T.σ₀).X k).Ψ) (a : Fin D.R.r), laR T j u k τ a = if ((T.U j T.σ₀).X k).p0 ≤ (a : ℕ) then (ext0 (u.aP (tt τ)) ((a : ℕ) - ((T.U j T.σ₀).X k).p0) : ℤ) + ((u.n / 2 : ℕ) : ℤ) else -(ext0 (u.aM (tt τ)) (((T.U j T.σ₀).X k).p0 - 1 - (a : ℕ)) : ℤ) - ((u.n / 2 : ℕ) : ℤ) := by
  intro D T h j hj k
  obtain ⟨hr, hk, -⟩ := h.unf j hj T.σ₀ T.good_σ₀
  obtain ⟨hp0, hΨ⟩ := hk k
  obtain ⟨hp, hq, -⟩ := h.pins.2.2.2 j hj
  have hc : Fintype.card ((T.U j T.σ₀).X k).Ψ = D.R.f := by
    have h1 := GlobalTheory.RunIn.WtSize.two_mul_card_cm ((T.U j T.σ₀).X k)
    rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.PfTorusFrame.finrank_eq D] at h1
    omega
  refine ⟨laR_wadd T j k, laR_wsmul T j k, fun u v m => ?_, fun i => ?_, ?_, hp0.trans hq, ?_, ?_⟩
  · rw [addL, laR_wadd, laR_wsmul]
  · funext τ a
    have hn : (etWt D j i).n / 2 = i * (g0 D / 2) := by
      show g0 D * i / 2 = _
      unfold g0
      rw [mul_assoc 2, mul_assoc 2, Nat.mul_div_cancel_left _ two_pos, Nat.mul_div_cancel_left _ two_pos, mul_comm]
    have hw : ∀ x, wtA (etWt D j i) x = 0 := wtA_wscalar _ _ _
    simp only [laR, laU, Pi.smul_apply, hw, hn, nsmul_eq_mul, de2W]
    split_ifs <;> simp
  · rw [nd, Fintype.card_prod, hc, card_lower, WeightFamilies.dimY, ← choose_split, hr, hp, hq]
  · rw [← hc, Fintype.card_coe]
  · let f : D.what₂.Tau → ((T.U j T.σ₀).X k).Ψ := fun t => ⟨DV.tauEmb D t, (hΨ _).2 (h.pins.1.2.2.2 t)⟩
    have hf : Function.Bijective f := by
      refine ⟨fun t t' e => tauEmb_inj (congrArg Subtype.val e), fun τ => ?_⟩
      obtain ⟨t, ht⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.exists_tau_of_inPsi T.Q h.pins.1 τ.1 ((hΨ _).1 τ.2)
      exact ⟨t, Subtype.ext ht.symm⟩
    have hinv : ∀ τ, Function.invFun (relab T.Q.c T.σ₀) τ = τ := fun τ =>
      Function.leftInverse_invFun (GlobalTheory.RunIn.WtSize.relab_bijective T.Q.c T.σ₀).1 τ
    refine ⟨(Equiv.ofBijective f hf).symm, fun u τ a => ?_⟩
    obtain ⟨t, rfl⟩ := (Equiv.ofBijective f hf).surjective τ
    rw [Equiv.symm_apply_apply]
    have e : ((Equiv.ofBijective f hf) t).1 = DV.tauEmb D t := rfl
    simp only [laR, laU, hinv, e, wtA_tau, wtA_conj]

end GlobalTheory.Shares.WtDic
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ComponentModelWeightDimensionDictionaryStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.componentModelWeight_dimension_dictionary : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (k : (T.U j T.σ₀).Comp), (∀ u u' : WeightFamilies.Wt D j, laR T j (wadd u u') k = laR T j u k + laR T j u' k) ∧ (∀ (m : ℕ) (u : WeightFamilies.Wt D j), laR T j (wsmul m u) k = m • laR T j u k) ∧ (∀ (u v : WeightFamilies.Wt D j) (m : ℕ), laR T j (addL u v m) k = laR T j u k + m • laR T j v k) ∧ (∀ i : ℕ, laR T j (etWt D j i) k = (i * (g0 D / 2)) • de2W ((T.U j T.σ₀).X k)) ∧ nd ((T.U j T.σ₀).X k) = WeightFamilies.dimY D j ∧ ((T.U j T.σ₀).X k).p0 = (D.R.sigW j).2 ∧ ((T.U j T.σ₀).X k).Ψ.card = D.R.f ∧ ∃ tt : ((T.U j T.σ₀).X k).Ψ ≃ D.what₂.Tau, ∀ (u : WeightFamilies.Wt D j) (τ : ((T.U j T.σ₀).X k).Ψ) (a : Fin D.R.r), laR T j u k τ a = if ((T.U j T.σ₀).X k).p0 ≤ (a : ℕ) then (ext0 (u.aP (tt τ)) ((a : ℕ) - ((T.U j T.σ₀).X k).p0) : ℤ) + ((u.n / 2 : ℕ) : ℤ) else -(ext0 (u.aM (tt τ)) (((T.U j T.σ₀).X k).p0 - 1 - (a : ℕ)) : ℤ) - ((u.n / 2 : ℕ) : ℤ) := by
  first | exact @GlobalTheory.Shares.WtDic.weights_dictionary | exact GlobalTheory.Shares.WtDic.weights_dictionary | (intros; apply GlobalTheory.Shares.WtDic.weights_dictionary <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.GenericSectionsPolynomialDictionary
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.GenericSectionsPolynomialDictionary
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps GlobalTheory.Shares

namespace GlobalTheory.Shares.PolyDict

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j}

theorem ofWt_C {ι : Type} (u : WeightFamilies.Wt D j) (F : B.Cusp j u) :
    OfWt X u (MvPolynomial.C (X.inc u F) : MvPolynomial ι X.Forms) := by
  classical
  intro m
  rw [MvPolynomial.coeff_C]
  split_ifs
  · exact LinearMap.mem_range.mpr ⟨F, rfl⟩
  · exact Submodule.zero_mem _

theorem ofWt_sum {ι κ : Type} (u : WeightFamilies.Wt D j) (s : Finset κ) (p : κ → MvPolynomial ι X.Forms)
    (h : ∀ k ∈ s, OfWt X u (p k)) : OfWt X u (∑ k ∈ s, p k) := by
  intro m
  rw [MvPolynomial.coeff_sum]
  exact Submodule.sum_mem _ fun k hk => h k hk m

theorem ofWt_X_mul {ι : Type} (u : WeightFamilies.Wt D j) (i : ι) (p : MvPolynomial ι X.Forms) (h : OfWt X u p) :
    OfWt X u (MvPolynomial.X i * p) := by
  classical
  intro m
  rw [MvPolynomial.coeff_X_mul']
  split_ifs
  · exact h _
  · exact Submodule.zero_mem _

theorem ofWt_mul {ι : Type} (u u' : WeightFamilies.Wt D j) (p q : MvPolynomial ι X.Forms) (hp : OfWt X u p)
    (hq : OfWt X u' q) : OfWt X (wadd u u') (p * q) := by
  classical
  intro m
  rw [MvPolynomial.coeff_mul]
  refine Submodule.sum_mem _ fun x _ => ?_
  obtain ⟨F, hF⟩ := LinearMap.mem_range.mp (hp x.1)
  obtain ⟨G, hG⟩ := LinearMap.mem_range.mp (hq x.2)
  obtain ⟨H, hH⟩ := X.inc_mul u u' F G
  rw [← hF, ← hG, hH]
  exact LinearMap.mem_range_self _ _

theorem toRp_C (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) (F : X.Forms) :
    toRp X la N (MvPolynomial.C F) = emb X la N F := MvPolynomial.eval₂Hom_C _ _ _

theorem toRp_X (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) (p : Idx D j N) :
    toRp X la N (MvPolynomial.X p) = algebraMap (Op X la N) (Rp X la N) (Tv X la N p) := MvPolynomial.eval₂Hom_X' _ _ _

theorem toFn_C (R : Rdg X) {N : ℕ} (t : Idx D j N → ℂ) (F : X.Forms) :
    R.toFn t (MvPolynomial.C F) = R.ev F := MvPolynomial.eval₂Hom_C _ _ _

theorem toFn_X (R : Rdg X) {N : ℕ} (t : Idx D j N → ℂ) (p : Idx D j N) :
    R.toFn t (MvPolynomial.X p) = fun _ => t p := MvPolynomial.eval₂Hom_X' _ _ _

private lemma algebraMap_mul_mem_Vw (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) (u : WeightFamilies.Wt D j)
    (x : Op X la N) {v : Rp X la N} (hv : v ∈ Vw X la N u) :
    algebraMap (Op X la N) (Rp X la N) x * v ∈ Vw X la N u := by
  rw [IsScalarTower.algebraMap_apply (Op X la N) (Kp X la N) (Rp X la N), ← Algebra.smul_def]
  exact Submodule.smul_mem _ _ hv

theorem toRp_mem (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) (u : WeightFamilies.Wt D j)
    (p : MvPolynomial (Idx D j N) X.Forms) (hp : OfWt X u p) : toRp X la N p ∈ Vw X la N u := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [p.as_sum, map_sum]
  refine Submodule.sum_mem _ fun m _ => ?_
  obtain ⟨F, hF⟩ := LinearMap.mem_range.mp (hp m)
  have key : toRp X la N (MvPolynomial.monomial m (p.coeff m)) = emb X la N (p.coeff m) *
      m.prod fun n e => (algebraMap (Op X la N) (Rp X la N) (Tv X la N n)) ^ e := by
    rw [toRp, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_monomial]
  rw [key, ← hF, mul_comm]
  have hbase : emb X la N (X.inc u F) ∈ Vw X la N u := Submodule.subset_span ⟨F, rfl⟩
  suffices H : ∀ v ∈ Vw X la N u,
      (m.prod fun n e => (algebraMap (Op X la N) (Rp X la N) (Tv X la N n)) ^ e) * v ∈ Vw X la N u from
    H _ hbase
  unfold Finsupp.prod
  refine Finset.prod_induction _ (fun x => ∀ v ∈ Vw X la N u, x * v ∈ Vw X la N u) ?_ ?_ ?_
  · intro a b ha hb v hv
    rw [mul_assoc]
    exact ha _ (hb v hv)
  · intro v hv
    rwa [one_mul]
  · intro n _ v hv
    show algebraMap (Op X la N) (Rp X la N) (Tv X la N n) ^ (m n) * v ∈ _
    rw [← map_pow]
    exact algebraMap_mul_mem_Vw la N u _ hv

theorem toFn_mem (R : Rdg X) {N : ℕ} (t : Idx D j N → ℂ) (u : WeightFamilies.Wt D j)
    (p : MvPolynomial (Idx D j N) X.Forms) (hp : OfWt X u p) : R.toFn t p ∈ R.sp u Set.univ := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [p.as_sum, map_sum]
  refine Submodule.sum_mem _ fun m _ => ?_
  obtain ⟨F, hF⟩ := LinearMap.mem_range.mp (hp m)
  have key : R.toFn t (MvPolynomial.monomial m (p.coeff m)) = R.ev (p.coeff m) *
      m.prod fun n e => (fun _ : R.Y => t n) ^ e := by
    rw [Rdg.toFn, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_monomial]
  rw [key, ← hF, mul_comm]
  have hbase : R.ev (X.inc u F) ∈ R.sp u Set.univ := Submodule.subset_span ⟨F, Set.mem_univ _, rfl⟩
  suffices H : ∀ v ∈ R.sp u Set.univ,
      (m.prod fun n e => (fun _ : R.Y => t n) ^ e) * v ∈ R.sp u Set.univ from H _ hbase
  unfold Finsupp.prod
  refine Finset.prod_induction _ (fun x => ∀ v ∈ R.sp u Set.univ, x * v ∈ R.sp u Set.univ) ?_ ?_ ?_
  · intro a b ha hb v hv
    rw [mul_assoc]
    exact ha _ (hb v hv)
  · intro v hv
    rwa [one_mul]
  · intro n _ v hv
    show (fun _ : R.Y => t n) ^ (m n) * v ∈ _
    have hc : (fun _ : R.Y => t n) ^ (m n) * v = (t n ^ m n) • v := by
      funext y
      simp [Pi.pow_apply, Pi.mul_apply, Pi.smul_apply]
    rw [hc]
    exact Submodule.smul_mem _ _ hv

theorem sp_mul (R : Rdg X) (u u' : WeightFamilies.Wt D j) (f : R.Y → ℂ) (hf : f ∈ R.sp u Set.univ) (g : R.Y → ℂ)
    (hg : g ∈ R.sp u' Set.univ) : f * g ∈ R.sp (wadd u u') Set.univ := by
  have hfg := Submodule.mul_mem_mul hf hg
  simp only [Rdg.sp, Submodule.span_mul_span] at hfg ⊢
  refine Submodule.span_le.mpr ?_ hfg
  rintro _ ⟨_, ⟨F, -, rfl⟩, _, ⟨G, -, rfl⟩, rfl⟩
  obtain ⟨H, hH⟩ := X.inc_mul u u' F G
  show R.ev (X.inc u F) * R.ev (X.inc u' G) ∈ _
  rw [← map_mul R.ev, hH]
  exact Submodule.subset_span ⟨H, Set.mem_univ _, rfl⟩

theorem sp_span (R : Rdg X) (u : WeightFamilies.Wt D j) (s : Set (B.Cusp j u)) :
    R.sp u (Submodule.span B.KO s) = R.sp u s := by
  unfold Rdg.sp
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨F, hF, rfl⟩
    have hF' : F ∈ Submodule.span B.KO s := hF
    clear hF
    induction hF' using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero =>
      simp only [map_zero]
      exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      simp only [map_add (f := _)]
      exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      simp only [map_smul, R.ev_smul]
      exact Submodule.smul_mem _ _ hx
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

theorem sp_finrank (R : Rdg X) (u : WeightFamilies.Wt D j) (M : Submodule B.KO (B.Cusp j u)) :
    FiniteDimensional ℂ (R.sp u M) ∧ Module.finrank ℂ (R.sp u M) = Module.finrank B.KO M := by
  let b := Module.finBasis B.KO M
  have hli : LinearIndependent B.KO (fun i => (b i : B.Cusp j u)) :=
    b.linearIndependent.map' M.subtype (Submodule.ker_subtype M)
  have hli' := R.indep u _ _ hli
  have hspan : Submodule.span B.KO (Set.range fun i => (b i : B.Cusp j u)) = M := by
    rw [show (Set.range fun i => (b i : B.Cusp j u)) = M.subtype '' Set.range b from Set.range_comp _ _,
      Submodule.span_image, b.span_eq, Submodule.map_subtype_top]
  have hs := sp_span R u (Set.range fun i => (b i : B.Cusp j u))
  rw [hspan] at hs
  have e : R.sp u (M : Set (B.Cusp j u)) =
      Submodule.span ℂ (Set.range fun i => R.ev (X.inc u (b i : B.Cusp j u))) := by
    rw [hs]
    unfold Rdg.sp
    rw [← Set.range_comp]
    rfl
  rw [e]
  exact ⟨FiniteDimensional.span_of_finite ℂ (Set.finite_range _),
    (finrank_span_eq_card hli').trans (Fintype.card_fin _)⟩

end GlobalTheory.Shares.PolyDict

namespace GlobalTheory.Shares


open PolyDict in
theorem polyDictionary : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (R : Rdg X) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) (wL : WeightFamilies.Wt D j) (w : Fin N → B.Cusp j wL) (t : Idx D j N → ℂ), (∀ i, toRp X la N (∑ k, MvPolynomial.X (i, k) * MvPolynomial.C (X.inc wL (w k))) = sec X la w i ∧ R.toFn t (∑ k, MvPolynomial.X (i, k) * MvPolynomial.C (X.inc wL (w k))) = R.s w t i ∧ OfWt X wL (∑ k, MvPolynomial.X (i, k) * MvPolynomial.C (X.inc wL (w k)) : MvPolynomial (Idx D j N) X.Forms)) ∧ (∀ F, toRp X la N (MvPolynomial.C F) = emb X la N F ∧ R.toFn t (MvPolynomial.C F) = R.ev F) ∧ (∀ u (F : B.Cusp j u), OfWt X u (MvPolynomial.C (X.inc u F) : MvPolynomial (Idx D j N) X.Forms)) ∧ (∀ u u' (p q : MvPolynomial (Idx D j N) X.Forms), OfWt X u p → OfWt X u' q → OfWt X (wadd u u') (p * q)) ∧ (∀ u (p : MvPolynomial (Idx D j N) X.Forms), OfWt X u p → toRp X la N p ∈ Vw X la N u ∧ R.toFn t p ∈ R.sp u Set.univ) ∧ (∀ u u', ∀ f ∈ R.sp u Set.univ, ∀ g ∈ R.sp u' Set.univ, f * g ∈ R.sp (wadd u u') Set.univ) ∧ (∀ u (s : Set (B.Cusp j u)), R.sp u (Submodule.span B.KO s) = R.sp u s) ∧ (∀ u (M : Submodule B.KO (B.Cusp j u)), FiniteDimensional ℂ (R.sp u M) ∧ Module.finrank ℂ (R.sp u M) = Module.finrank B.KO M) := by
  intro D B P j X R la N wL w t
  refine ⟨fun i => ⟨?_, ?_, ?_⟩, fun F => ⟨PolyDict.toRp_C la N F, PolyDict.toFn_C R t F⟩,
    fun u F => PolyDict.ofWt_C u F, fun u u' p q hp hq => PolyDict.ofWt_mul u u' p q hp hq,
    fun u p hp => ⟨PolyDict.toRp_mem la N u p hp, PolyDict.toFn_mem R t u p hp⟩,
    fun u u' f hf g hg => PolyDict.sp_mul R u u' f hf g hg,
    fun u s => PolyDict.sp_span R u s, fun u M => PolyDict.sp_finrank R u M⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [map_sum]
      unfold Formalism.MainNotions.Gaps.EtaleWeightGaps.sec
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul, PolyDict.toRp_X, PolyDict.toRp_C, Algebra.smul_def,
        IsScalarTower.algebraMap_apply (Op X la N) (Kp X la N) (Rp X la N)]
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [map_sum]
      unfold Rdg.s
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul, PolyDict.toFn_X, PolyDict.toFn_C]
      funext y
      simp [Pi.mul_apply, Pi.smul_apply]
  · exact PolyDict.ofWt_sum wL _ _ fun k _ => PolyDict.ofWt_X_mul wL _ _ (PolyDict.ofWt_C wL (w k))

end GlobalTheory.Shares
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.GenericSectionsPolynomialDictionaryStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps GlobalTheory.Shares
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericSections_polynomial_dictionary : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (R : Rdg X) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) (wL : WeightFamilies.Wt D j) (w : Fin N → B.Cusp j wL) (t : Idx D j N → ℂ), (∀ i, toRp X la N (∑ k, MvPolynomial.X (i, k) * MvPolynomial.C (X.inc wL (w k))) = sec X la w i ∧ R.toFn t (∑ k, MvPolynomial.X (i, k) * MvPolynomial.C (X.inc wL (w k))) = R.s w t i ∧ OfWt X wL (∑ k, MvPolynomial.X (i, k) * MvPolynomial.C (X.inc wL (w k)) : MvPolynomial (Idx D j N) X.Forms)) ∧ (∀ F, toRp X la N (MvPolynomial.C F) = emb X la N F ∧ R.toFn t (MvPolynomial.C F) = R.ev F) ∧ (∀ u (F : B.Cusp j u), OfWt X u (MvPolynomial.C (X.inc u F) : MvPolynomial (Idx D j N) X.Forms)) ∧ (∀ u u' (p q : MvPolynomial (Idx D j N) X.Forms), OfWt X u p → OfWt X u' q → OfWt X (wadd u u') (p * q)) ∧ (∀ u (p : MvPolynomial (Idx D j N) X.Forms), OfWt X u p → toRp X la N p ∈ Vw X la N u ∧ R.toFn t p ∈ R.sp u Set.univ) ∧ (∀ u u', ∀ f ∈ R.sp u Set.univ, ∀ g ∈ R.sp u' Set.univ, f * g ∈ R.sp (wadd u u') Set.univ) ∧ (∀ u (s : Set (B.Cusp j u)), R.sp u (Submodule.span B.KO s) = R.sp u s) ∧ (∀ u (M : Submodule B.KO (B.Cusp j u)), FiniteDimensional ℂ (R.sp u M) ∧ Module.finrank ℂ (R.sp u M) = Module.finrank B.KO M) := by
  first | exact @GlobalTheory.Shares.polyDictionary | exact GlobalTheory.Shares.polyDictionary | (intros; apply GlobalTheory.Shares.polyDictionary <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.MemSpanCuspReadingsIffComponents
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.MemSpanCuspReadingsIffComponents
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares

namespace GlobalTheory.Shares

theorem spanMem_ssgt_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) {P : Frame X.Ψ r → ℂ} (hP : P ∈ X.SS la) : P ∈ X.SSgt la 0 := by
  refine ⟨hP, fun ξ hξ ν hν x hx => ?_⟩
  by_contra hne
  obtain ⟨⟨hsec, C, hC⟩, h0⟩ := hP
  have hpos := (moderateCoefficientPositivity_holds r X la P C 0 hsec (fun y hy => by simpa using hC y hy)).1 ξ hξ ν x hx hne
  have hsum : ∑ τ, ν τ = 0 := le_antisymm hν (Finset.sum_nonneg fun τ _ => hpos τ)
  have hz : ν = 0 := by
    funext τ
    exact (Finset.sum_eq_zero_iff_of_nonneg fun τ _ => hpos τ).1 hsum τ (Finset.mem_univ τ)
  subst hz
  exact hne (h0 ξ hξ x hx)

theorem spanMem_rdR {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (u : WeightFamilies.Wt D j)
    (F : (recB h.toLawsCore).Cusp j u) (k : (T.U j T.σ₀).Comp) :
    rdR h j F k ∈ ((T.U j T.σ₀).X k).SSgt (laR T j u k) 0 := by
  have hF : F.1 ∈ T.C j u := by
    rw [← cutR_eq T.C hj]; exact F.2
  exact spanMem_ssgt_zero _ _
    (ReciprocityTheory.ChartRestriction.G.PullbackSections.readings_holomorphic_cuspForms (U := T.U j) siegelSpaceAlgebra_holds T.good_σ₀ (wtA u) u.n ⟨F.1, hF⟩ k)

theorem span_readings_components : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (n : SecNorm (recB h.toLawsCore)) (R : Rdg (recPlusN h j hj n)) (e : R.Y ≃ DomPt T j), IsRdgU h j hj n R e → ∀ u : WeightFamilies.Wt D j, (∀ g ∈ R.sp u Set.univ, ∃ f : ∀ k : (T.U j T.σ₀).Comp, Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ, (∀ k, f k ∈ ((T.U j T.σ₀).X k).SSgt (laR T j u k) 0) ∧ ∀ y, g y = f (e y).1 (e y).2.1) ∧ (∀ (A : ∀ k : (T.U j T.σ₀).Comp, Set (Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ)) (s : Set ((recB h.toLawsCore).Cusp j u)), OntoBy h j u A s → ∀ f : ∀ k : (T.U j T.σ₀).Comp, Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ, (∀ k, f k ∈ A k) → (fun y => f (e y).1 (e y).2.1) ∈ R.sp u s) ∧ ∀ (F : (recB h.toLawsCore).Cusp j u) (k : (T.U j T.σ₀).Comp), rdR h j F k ∈ ((T.U j T.σ₀).X k).SSgt (laR T j u k) 0 := by
  intro D T h j hj n R e hR u
  refine ⟨fun g hg => ?_, fun A s hA f hf => ?_, fun F k => spanMem_rdR h j hj u F k⟩
  · unfold Rdg.sp at hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨F, -, rfl⟩ := hg
      exact ⟨fun k => rdR h j F k, fun k => spanMem_rdR h j hj u F k, fun y => hR.2 u F y⟩
    | zero =>
      exact ⟨fun _ => 0, fun k => (siegelSpaceAlgebra_holds _ _ (laR T j u k) (laR T j u k) 0).2.2.1.1, fun _ => rfl⟩
    | add g g' _ _ hg hg' =>
      obtain ⟨f, hf, e1⟩ := hg
      obtain ⟨f', hf', e2⟩ := hg'
      refine ⟨fun k => f k + f' k,
        fun k => (siegelSpaceAlgebra_holds _ _ (laR T j u k) (laR T j u k) 0).2.2.1.2.1 _ (hf k) _ (hf' k), fun y => ?_⟩
      simp only [Pi.add_apply, e1, e2]
    | smul a g _ hg =>
      obtain ⟨f, hf, e1⟩ := hg
      refine ⟨fun k => a • f k,
        fun k => (siegelSpaceAlgebra_holds _ _ (laR T j u k) (laR T j u k) 0).2.2.1.2.2 a _ (hf k), fun y => ?_⟩
      simp only [Pi.smul_apply, e1]
  · obtain ⟨m, a, F, hF, hsum⟩ := hA f hf
    have : (fun y => f (e y).1 (e y).2.1) = ∑ i, a i • R.ev ((recPlusN h j hj n).inc u (F i)) := by
      funext y
      rw [hsum _ _ (e y).2.2, Finset.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Pi.smul_apply, hR.2 u (F i) y, smul_eq_mul]
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨F i, hF i, rfl⟩)

end GlobalTheory.Shares
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.MemSpanCuspReadingsIffComponentsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_span_cuspReadings_iff_components : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (n : SecNorm (recB h.toLawsCore)) (R : Rdg (recPlusN h j hj n)) (e : R.Y ≃ DomPt T j), IsRdgU h j hj n R e → ∀ u : WeightFamilies.Wt D j, (∀ g ∈ R.sp u Set.univ, ∃ f : ∀ k : (T.U j T.σ₀).Comp, Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ, (∀ k, f k ∈ ((T.U j T.σ₀).X k).SSgt (laR T j u k) 0) ∧ ∀ y, g y = f (e y).1 (e y).2.1) ∧ (∀ (A : ∀ k : (T.U j T.σ₀).Comp, Set (Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ)) (s : Set ((recB h.toLawsCore).Cusp j u)), OntoBy h j u A s → ∀ f : ∀ k : (T.U j T.σ₀).Comp, Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ, (∀ k, f k ∈ A k) → (fun y => f (e y).1 (e y).2.1) ∈ R.sp u s) ∧ ∀ (F : (recB h.toLawsCore).Cusp j u) (k : (T.U j T.σ₀).Comp), rdR h j F k ∈ ((T.U j T.σ₀).X k).SSgt (laR T j u k) 0 := by
  first | exact @GlobalTheory.Shares.span_readings_components | exact GlobalTheory.Shares.span_readings_components | (intros; apply GlobalTheory.Shares.span_readings_components <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaRuleExistsAndEval
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory

theorem thetaRule_exists_and_eval : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (xx : Fin n → Dw.La) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n → (∃ f : Rul Xo c, IsThRule Xo c nab xx P f ∧ f ∈ sec Xo c a n) ∧ ∀ f : Rul Xo c, IsThRule Xo c nab xx P f → ∀ (k : Type) [Field k] [Algebra c.F k] (y : FrPt Xo c k), ThValAt Xo c nab y xx P (evR Xo c f y) := by
  intro hC E _ _ _ H Dw l Xo c _ nab hn a n xx P hP
  have hL : ReciprocityTheory.ChartRestriction.G.Out.Laws := GlobalTheory.abelianSchemeLaws_all.1
  have hT := GlobalTheory.thValTot_of_chartIndep hL hC E H Dw l Xo c nab hn
  refine ⟨?_, fun f hf k _ _ y => ?_⟩
  · obtain ⟨f, hf, -⟩ := existsUnique_thRule Xo c nab hT xx hP
    exact ⟨f, hf, GlobalTheory.thetaRule_mem_sec hL hC E H Dw l Xo c nab hn a n f ⟨xx, P, hP, hf⟩⟩
  · have h := GlobalTheory.Frames.allTest_of_secBaseChange hL.secBaseChange E H Dw l Xo c k y
    obtain ⟨w, hw, -⟩ := hT k y a n xx P hP
    have e : evR Xo c f y = w := by
      unfold evR Formalism.L2.Pj.evalAt
      rw [dite_eq_left h]
      exact GlobalTheory.thetaValue_natural hL hC E H Dw l Xo c nab hn _ _ _ _ y
        h.choose_spec.choose_spec.choose_spec a n xx P hP _ _ (hf _ _) hw
    rw [e]
    exact hw

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RamifiedPrimePowersSizeBounds
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RamifiedPrimePowersSizeBounds
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn

namespace GlobalTheory.RunIn

theorem pPow_size : ∀ (D : D7) (j : ℕ) (w : WeightFamilies.Wt D j), 1 ≤ D.host.q ∧ 1 ≤ D.host.d ∧ 0 ≤ Real.log (4 * ((D.R.f : ℝ) / 2) ^ 2 * D.host.q * D.host.d) ∧ 0 ≤ Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) ∧ (c2 D w : ℝ) * Real.log D.host.QS + (Formalism.MainNotions.DIV.Cons.cHalf w : ℝ) * Real.log D.host.q + (Formalism.MainNotions.DIV.Cons.cHalf w : ℝ) * Real.log D.host.d ≤ ((WeightAlgebra.DF w : ℝ) + 1) * Real.log (4 * ((D.R.f : ℝ) / 2) ^ 2 * D.host.q * D.host.d) ∧ ∀ a b c : ℕ, 1 ≤ pPow D a b c ∧ Real.log (pPow D a b c) = a * Real.log D.host.QS + b * Real.log D.host.q + c * Real.log D.host.d := by
  intro D j w
  have hq : 1 ≤ D.host.q := by have := D.host.qd_big.1; omega
  have hd : 1 ≤ D.host.d := by have := D.host.qd_big.2; omega
  have hqR : (1 : ℝ) ≤ D.host.q := by exact_mod_cast hq
  have hdR : (1 : ℝ) ≤ D.host.d := by exact_mod_cast hd
  have hlq : 0 ≤ Real.log D.host.q := Real.log_nonneg hqR
  have hld : 0 ≤ Real.log D.host.d := Real.log_nonneg hdR
  have hQ : (1 : ℝ) ≤ D.host.QS := by exact_mod_cast D.host.QS_pos
  have hl2 : 0 ≤ Real.log D.host.QS := Real.log_nonneg hQ
  have hQf : (D.host.QS : ℝ) ≤ 4 * ((D.R.f : ℝ) / 2) ^ 2 := by
    have h1 : (D.host.QS : ℝ) ≤ (D.R.n : ℝ) ^ 2 := by exact_mod_cast D.host.QS_le
    have h2 : (D.R.f : ℝ) = 2 * D.R.n := by unfold Ranks.f; push_cast; ring
    rw [h2]; nlinarith [sq_nonneg (D.R.n : ℝ)]
  have hlf : Real.log D.host.QS ≤ Real.log (4 * ((D.R.f : ℝ) / 2) ^ 2) := Real.log_le_log (by linarith) hQf
  have hlog : Real.log (4 * ((D.R.f : ℝ) / 2) ^ 2 * D.host.q * D.host.d) =
      Real.log (4 * ((D.R.f : ℝ) / 2) ^ 2) + Real.log D.host.q + Real.log D.host.d := by
    have h0 : (0 : ℝ) < 4 * ((D.R.f : ℝ) / 2) ^ 2 := by linarith
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul h0.ne' (by positivity)]
  have hD : (0 : ℝ) ≤ (WeightAlgebra.DF w : ℝ) := Nat.cast_nonneg _
  refine ⟨hq, hd, ?_, ?_, ?_, ?_⟩
  · rw [hlog]; linarith
  · apply Real.log_nonneg
    have h0 : (1 : ℝ) ≤ D.host.g 0 := by exact_mod_cast (D.host.g_prime 0).one_le
    have h1 : (1 : ℝ) ≤ D.host.g 1 := by exact_mod_cast (D.host.g_prime 1).one_le
    nlinarith
  · have hc2 : (c2 D w : ℝ) = (WeightAlgebra.DF w : ℝ) := rfl
    have hch : (Formalism.MainNotions.DIV.Cons.cHalf w : ℝ) ≤ (WeightAlgebra.DF w : ℝ) + 1 := by
      have h1 := (Nat.ceil_lt_add_one (show (0 : ℝ) ≤ (WeightAlgebra.DF w : ℝ) / 2 by positivity)).le
      unfold Formalism.MainNotions.DIV.Cons.cHalf
      linarith
    have a1 := mul_le_mul_of_nonneg_left hlf hD
    have a2 := mul_le_mul_of_nonneg_right hch hlq
    have a3 := mul_le_mul_of_nonneg_right hch hld
    rw [hlog, hc2]
    nlinarith
  · intro a b c
    have hQ0 : 0 < D.host.QS := D.host.QS_pos
    refine ⟨?_, ?_⟩
    · unfold pPow
      exact Nat.one_le_iff_ne_zero.mpr (by positivity)
    · unfold pPow
      push_cast
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_pow, Real.log_pow]

end GlobalTheory.RunIn
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RamifiedPrimePowersSizeBoundsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ramifiedPrimePowers_size_bounds : ∀ (D : D7) (j : ℕ) (w : WeightFamilies.Wt D j), 1 ≤ D.host.q ∧ 1 ≤ D.host.d ∧ 0 ≤ Real.log (4 * ((D.R.f : ℝ) / 2) ^ 2 * D.host.q * D.host.d) ∧ 0 ≤ Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) ∧ (c2 D w : ℝ) * Real.log D.host.QS + (Formalism.MainNotions.DIV.Cons.cHalf w : ℝ) * Real.log D.host.q + (Formalism.MainNotions.DIV.Cons.cHalf w : ℝ) * Real.log D.host.d ≤ ((WeightAlgebra.DF w : ℝ) + 1) * Real.log (4 * ((D.R.f : ℝ) / 2) ^ 2 * D.host.q * D.host.d) ∧ ∀ a b c : ℕ, 1 ≤ pPow D a b c ∧ Real.log (pPow D a b c) = a * Real.log D.host.QS + b * Real.log D.host.q + c * Real.log D.host.d := by
  first | exact @GlobalTheory.RunIn.pPow_size | exact GlobalTheory.RunIn.pPow_size | (intros; apply GlobalTheory.RunIn.pPow_size <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PageRowsOfLe
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn

namespace GlobalTheory

theorem pageRows_of_le : ∀ (D : D7) (large₂ : SizeData₂ D) (j : ℕ) (ka w : WeightFamilies.Wt D j), 0 ≤ large₂.sc.L → WeightAlgebra.DF w ≤ WeightAlgebra.DF ka → w.n ≤ ka.n → ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ ka → ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w := by
  intro D large₂ j ka w hL hd hn h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, ?_, ?_⟩
  · refine le_trans (Real.log_le_log (by positivity) ?_) h8
    have : ((WeightAlgebra.DF w : ℕ) : ℝ) ≤ ((WeightAlgebra.DF ka : ℕ) : ℝ) := by exact_mod_cast hd
    linarith
  · rcases Nat.eq_zero_or_pos w.n with h0 | h0
    · rw [h0]; simpa using hL
    · exact le_trans (Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast hn)) h9

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HalfLevelGeneratorNorm
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn GlobalTheory.BlockTh GlobalTheory.EtaAn ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.RunIn

theorem half_level_generator_norm :
    ∀ (D : D7) (T : Top D) (_h : LawsP T) (_EX : ErrX D), ∃ α : 𝓞 D.host.E, α * T.Q.H.bar α = (T.Q.l.M : 𝓞 D.host.E) ∧ T.Q.l.Mb = Ideal.span {T.Q.H.bar α} := by
  intro D T h _EX
  have hM : LawsM T.toCore := h.toLawsCore.toLawsM

  have hbb : ∀ x : 𝓞 D.host.E, T.Q.H.bar (T.Q.H.bar x) = x := by
    intro x
    rw [bar_core T.toCore, bar_core T.toCore, barE_barE]

  have hn : ∀ i, piOf T.toCore _EX i * T.Q.H.bar (piOf T.toCore _EX i) = (D.host.g i : 𝓞 D.host.E) := by
    intro i
    rw [bar_core T.toCore]
    exact piOf_mul_barE T.toCore _EX i
  set π₀ := piOf T.toCore _EX 0
  set π₁ := piOf T.toCore _EX 1
  refine ⟨T.Q.H.bar (π₀ * π₁), ?_, ?_⟩
  · rw [hbb, map_mul, level_M T.toCore hM]
    have h0 := hn 0
    have h1 := hn 1
    push_cast
    rw [← h0, ← h1]
    ring
  · rw [hbb, Mb_eq T.toCore hM, ← span_piOf T.toCore hM _EX 0, ← span_piOf T.toCore hM _EX 1,
      Ideal.span_singleton_mul_span_singleton]

end GlobalTheory.RunIn
end
