module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleArithHilbertSamuelOfPrincipalisation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionsLowerBoundAmpleMinusTwist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodHermitianLineBundlePair
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithNefVolumeUpperBoundStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiPullOfPrincipalisation

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSmallSecHermitianLineBundleArithVariety
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSmallSecHermitianLineBundleArithVariety
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.SmallFin

theorem smallSec_finite : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ M : HermLB p, M.smallSec.Finite := by
  intro k _ X _ p D hX M
  obtain ⟨P, hL, -⟩ := GlobalTheory.VolBr.exists_pair M M
  subst hL
  have hrep : P.Rep 1 0 P.L := (GlobalTheory.VolBr.Pair.rep_base k X p P).1
  obtain ⟨e, he, hrange, hnorm, -⟩ := GlobalTheory.VolBr.RepDict.rep_dict k X p P 1 0 P.L hrep
  have hfin : (P.Bl 1 0 1).Finite := GlobalTheory.T.hermLineBundlePair_sectionBall_finite k X p D hX P 1 0 1
  refine (hfin.preimage he.injOn).subset ?_
  intro u hu
  refine ⟨?_, fun σ y => ?_⟩
  · have hm : e u ∈ Set.range e := Set.mem_range_self u
    rw [hrange] at hm
    exact hm
  have h0 : 0 ≤ P.nu 1 0 σ y (e u) := by
    unfold Pair.nu; positivity
  have h1 : P.nu 1 0 σ y (e u) ^ 2 ≤ 1 := by
    rw [hnorm]; exact hu σ y
  exact (pow_le_one_iff_of_nonneg h0 two_ne_zero).1 h1

end GlobalTheory.SmallFin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSmallSecHermitianLineBundleArithVarietyStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_smallSec_hermitian_line_bundle_arith_variety : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ M : HermLB p, M.smallSec.Finite := by
  first | exact @GlobalTheory.SmallFin.smallSec_finite | exact GlobalTheory.SmallFin.smallSec_finite | (intros; apply GlobalTheory.SmallFin.smallSec_finite <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShiftSecondBundleNormPairNormBallGeneration
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShiftSecondBundleNormPairNormBallGeneration
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNef

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem shiftA_nu (P : Pair p) (u : ℝ) (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField) :
    (shiftA P u).nu a b σ y f = P.nu a b σ y f * Real.exp (-(b * u)) := by
  have e : (shiftA P u).nu a b σ y f = ‖ratVal (P.loc a b f (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y)) y‖ *
      Real.exp (-(a * (P.L.φ σ).φ (pick (P.L.φ σ).isLB y) y +
        b * ((P.A.φ σ).φ (pick (P.A.φ σ).isLB y) y + 2 * u)) / 2) := rfl
  rw [e, Pair.nu, mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem shiftA_Bl (P : Pair p) (u : ℝ) (a b : ℤ) (R : ℝ) :
    (shiftA P u).Bl a b R = P.Bl a b (R * Real.exp (b * u)) := by
  ext f
  simp only [Pair.Bl, Set.mem_setOf_eq, shiftA_H, shiftA_nu]
  refine and_congr_right fun _ => forall_congr' fun σ => forall_congr' fun y => ?_
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]

theorem genAt_shiftA (P : Pair p) (u : ℝ) (c : ℕ) (h : GenAt P c) : GenAt (shiftA P u) c := by
  obtain ⟨n, v, hv, hg⟩ := h
  refine ⟨n, v, fun i => by rw [shiftA_H]; exact hv i, fun σ y => ?_⟩
  obtain ⟨i, hi⟩ := hg σ y
  exact ⟨i, by rw [shiftA_nu]; exact mul_ne_zero hi (Real.exp_pos _).ne'⟩

theorem shiftA_props : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ (P : Pair p) (u : ℝ), (∀ (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField), (shiftA P u).nu a b σ y f = P.nu a b σ y f * Real.exp (-(b * u))) ∧ (∀ (a b : ℤ) (R : ℝ), (shiftA P u).Bl a b R = P.Bl a b (R * Real.exp (b * u))) ∧ (∀ c : ℕ, GenAt P c → GenAt (shiftA P u) c) :=
  fun _ _ _ _ _ P u => ⟨shiftA_nu P u, shiftA_Bl P u, genAt_shiftA P u⟩

end GlobalTheory.HSNef
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShiftSecondBundleNormPairNormBallGenerationStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shiftSecondBundleNormPair_norm_ball_generation : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ (P : Pair p) (u : ℝ), (∀ (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField), (shiftA P u).nu a b σ y f = P.nu a b σ y f * Real.exp (-(b * u))) ∧ (∀ (a b : ℤ) (R : ℝ), (shiftA P u).Bl a b R = P.Bl a b (R * Real.exp (b * u))) ∧ (∀ c : ℕ, GenAt P c → GenAt (shiftA P u) c) := by
  first | exact @GlobalTheory.HSNef.shiftA_props | exact GlobalTheory.HSNef.shiftA_props | (intros; apply GlobalTheory.HSNef.shiftA_props <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHilbertSamuelNefOfAmple
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHilbertSamuelLowerBoundSemiPosNefOnFibres
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodHermPairAdaptedTwist
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmallSectionAddMultipleAmpleAfterShift
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLBLeBySmallSectionOfRep
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLBLeBySmallSectionOfRep
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

namespace GlobalTheory.HSNef

theorem le_of_rep : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ (P : Pair p) (a b a' b' : ℤ) (M M' : HermLB p) (f : X.functionField), P.Rep a b M → P.Rep a' b' M' → f ≠ 0 → f ∈ P.Bl (a - a') (b - b') 1 → Le M' M := by
  intro k _ X _ p P a b a' b' M M' f hM hM' hf hB
  have hR : P.Rep (a - a') (b - b') (M.tens M'.dual) := by
    have h := Pair.rep_tens k X p P a b (-a') (-b') M M'.dual hM (Pair.rep_dual k X p P a' b' M' hM')
    simpa only [sub_eq_add_neg] using h
  obtain ⟨e, -, hrange, hnorm, hloc⟩ := RepDict.rep_dict k X p P _ _ _ hR
  have hfH : f ∈ (P.H (a - a') (b - b') : Set X.functionField) := hB.1
  rw [← hrange] at hfH
  obtain ⟨u, rfl⟩ := hfH
  refine (GlobalTheory.T.hermLBLeBySmallSection_iff_exists_smallSection_difference k X p M M').2 ⟨u, fun σ y => ?_, fun hu => ?_⟩
  · rw [← hnorm u σ y]
    have h0 : 0 ≤ P.nu (a - a') (b - b') σ y (e u) := by
      unfold Pair.nu; positivity
    exact pow_le_one₀ h0 (hB.2 σ y)
  · obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (P.L.isLB.cover.ge (Opens.mem_top (genericPoint X)))
    obtain ⟨j, hj⟩ := Opens.mem_iSup.1 (P.A.isLB.cover.ge (Opens.mem_top (genericPoint X)))
    have hne : P.loc (a - a') (b - b') (e u) i j ≠ 0 := by
      have h1 := (P.r i).ne_zero
      have h2 := (P.r' j).ne_zero
      simp only [Pair.loc]
      exact mul_ne_zero (mul_ne_zero hf (zpow_ne_zero _ h1)) (zpow_ne_zero _ h2)
    have hg := (hloc u (genericPoint X) i j hi hj).2 (unitAt_genericPoint hne)
    obtain ⟨c, hc⟩ := Opens.mem_iSup.1 ((M.tens M'.dual).isLB.cover.ge (Opens.mem_top (genericPoint X)))
    rw [mem_nonzeroLocus_iff u c hc, hu] at hg
    change genericPoint X ∈ X.basicOpen (0 : Γ(X, _)) at hg
    simp at hg

end GlobalTheory.HSNef
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLBLeBySmallSectionOfRepStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermLBLeBySmallSection_of_rep : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ (P : Pair p) (a b a' b' : ℤ) (M M' : HermLB p) (f : X.functionField), P.Rep a b M → P.Rep a' b' M' → f ≠ 0 → f ∈ P.Bl (a - a') (b - b') 1 → Le M' M := by
  first | exact @GlobalTheory.HSNef.le_of_rep | exact GlobalTheory.HSNef.le_of_rep | (intros; apply GlobalTheory.HSNef.le_of_rep <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmallSectionAddMultipleAmpleAfterShift
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef.TwistSmall

theorem mem_regular_sections_second_bundle_indep_first {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
    (P : Pair p) (L' : HermLB p) (r : L'.B.ι → X.functionFieldˣ) (hr : IsRatSec L'.B r)
    {s : X.functionField} (hs : s ∈ P.H 0 1) :
    s ∈ (⟨L', P.A, r, P.r', hr, P.hr'⟩ : Pair p).H 0 1 := by
  intro x i j _ hj
  have hx : x ∈ (⨆ i, P.L.B.U i) := by rw [P.L.isLB.cover]; trivial
  obtain ⟨i', hi'⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  simpa [Pair.loc] using hs x i' j hi' hj

theorem le_dual_pow_shift : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (P : Pair p) (N : HermLB p) (s : X.functionField), IsAmpleLB P.A.B → s ∈ P.H 0 1 → s ≠ 0 →
    ∃ c₁ : ℕ, ∀ c, c₁ ≤ c → 0 < c → ∃ u₀ : ℝ, ∀ u, u₀ ≤ u → Le (((shiftA P u).A.pow c).dual) N := by
  intro k _ X _ p D hX P N s hA hs hs0
  obtain ⟨rN, hrN⟩ := exists_isRatSec N.isLB
  let Q : Pair p := ⟨N, P.A, rN, P.r', hrN, P.hr'⟩
  obtain ⟨c₁, g, _, hg0, hg, -⟩ := GlobalTheory.T.exists_clear_denominators_ampleHermLineBundle k X p D hX Q hA 1 Empty (fun e => e.elim)
  refine ⟨c₁, fun c hc hc0 => ?_⟩
  have hsQ : s ∈ Q.H 0 1 := mem_regular_sections_second_bundle_indep_first P N rN hrN hs
  obtain ⟨hpow, -⟩ := NuPow.pow_mem_H_and_nu_pow k X p Q 0 1 s hsQ (c - c₁)
  obtain ⟨hf, -⟩ := NuMul.mul_mem_H_and_nu_mul k X p Q 1 c₁ _ _ g (s ^ (c - c₁)) hg hpow
  have e1 : (1 : ℤ) + ((c - c₁ : ℕ) : ℤ) * 0 = 1 := by ring
  have e2 : (c₁ : ℤ) + ((c - c₁ : ℕ) : ℤ) * 1 = c := by push_cast [Nat.cast_sub hc]; ring
  rw [e1, e2] at hf
  obtain ⟨w, _, hw⟩ := GlobalTheory.T.pairSection_mem_ball_exp_of_projArithVariety k X p D hX Q 1 c _ hf
  have hcpos : (0 : ℝ) < c := by exact_mod_cast hc0
  refine ⟨w / c, fun u hu => ?_⟩
  obtain ⟨-, hBl, -⟩ := GlobalTheory.T.shiftSecondBundleNormPair_norm_ball_generation k X p Q u
  have hwu : w ≤ (c : ℤ) * u := by
    have := (div_le_iff₀ hcpos).1 hu
    push_cast; linarith
  have hmem : g * s ^ (c - c₁) ∈ (shiftA Q u).Bl 1 c 1 := by
    rw [hBl, one_mul]
    exact ⟨hw.1, fun σ y => (hw.2 σ y).trans (Real.exp_le_exp.2 hwu)⟩
  have hne : g * s ^ (c - c₁) ≠ 0 := mul_ne_zero hg0 (pow_ne_zero _ hs0)
  have hrepN := (Pair.rep_base k X p (shiftA Q u)).1
  have hrepA := (Pair.rep_base k X p (shiftA Q u)).2.1
  have hpowA := Pair.rep_pow k X p (shiftA Q u) 0 1 _ c hrepA
  have hdual := Pair.rep_dual k X p (shiftA Q u) _ _ _ hpowA
  have e3 : (1 : ℤ) - -((c : ℤ) * 0) = 1 := by ring
  have e4 : (0 : ℤ) - -((c : ℤ) * 1) = c := by ring
  have hmem' : g * s ^ (c - c₁) ∈ (shiftA Q u).Bl (1 - -((c : ℤ) * 0)) (0 - -((c : ℤ) * 1)) 1 := by
    rw [e3, e4]; exact hmem
  exact GlobalTheory.T.hermLBLeBySmallSection_of_rep k X p (shiftA Q u) 1 0 _ _ N _ _ hrepN hdual hne hmem'

end GlobalTheory.HSNef.TwistSmall
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmallSectionAddMultipleAmpleAfterShiftStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_small_section_add_multiple_ample_after_shift : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (N : HermLB p) (s : X.functionField), IsAmpleLB P.A.B → s ∈ P.H 0 1 → s ≠ 0 → ∃ c₁ : ℕ, ∀ c, c₁ ≤ c → 0 < c → ∃ u₀ : ℝ, ∀ u, u₀ ≤ u → Le (((shiftA P u).A.pow c).dual) N := by
  first | exact @GlobalTheory.HSNef.TwistSmall.le_dual_pow_shift | exact GlobalTheory.HSNef.TwistSmall.le_dual_pow_shift | (intros; apply GlobalTheory.HSNef.TwistSmall.le_dual_pow_shift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsShiftSmallSectionCountRegimeFromRadiusOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsShiftSmallSectionCountRegimeFromRadiusOne
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem regime_shiftA : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ P : Pair p, IsAmpleLB P.A.B → P.A.SemiPos D → ∃ u₀ : ℝ, ∀ u, u₀ ≤ u → Regime (shiftA P u) D := by
  intro hA hHS k _ X _ p D hX P hamp hsemi
  obtain ⟨Φ, hΦ⟩ := ((hA.arExists k X p D hX).2 PUnit fun _ => P.A).1
  have hα := ((hA.arIso k X p D hX).2 PUnit _ Φ hΦ).1 PUnit.unit
  obtain ⟨t₀, ht₀⟩ := GlobalTheory.T.ampleArithHilbertSamuel_largeRadius_pair hHS k X p D hX P 0 1 0 0 P.A _ (Pair.rep_base k X p P).2.1 hamp hsemi hα
  refine ⟨t₀, fun u hu => ⟨Φ (MvPolynomial.X PUnit.unit ^ (D + 1)) / (D + 1).factorial + ((D : ℝ) + 1) * gdeg P.A D / (D + 1).factorial * u, ((D : ℝ) + 1) * gdeg P.A D / (D + 1).factorial, fun t ht => ?_⟩⟩
  have h := ht₀ (t + u) (by linarith)
  have e : ∀ m : ℕ, (shiftA P u).lc 0 m (Real.exp (t * m)) =
      P.lc ((m : ℤ) * 0 + 0) ((m : ℤ) * 1 + 0) (Real.exp ((t + u) * m)) := by
    intro m
    simp only [Pair.lc, (GlobalTheory.T.shiftSecondBundleNormPair_norm_ball_generation k X p P u).2.1, mul_zero, add_zero, mul_one, ← Real.exp_add]
    congr 4
    push_cast
    ring_nf
  have hfun : (fun m : ℕ => (shiftA P u).lc 0 m (Real.exp (t * m)) / (m : ℝ) ^ (D + 1)) =
      fun m : ℕ => P.lc ((m : ℤ) * 0 + 0) ((m : ℤ) * 1 + 0) (Real.exp ((t + u) * m)) / (m : ℝ) ^ (D + 1) :=
    funext fun m => by rw [e]
  rw [hfun]
  convert h using 2
  ring

end GlobalTheory.HSNef
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsShiftSmallSectionCountRegimeFromRadiusOneStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_shift_smallSectionCount_regime_from_radius_one : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ P : Pair p, IsAmpleLB P.A.B → P.A.SemiPos D → ∃ u₀ : ℝ, ∀ u, u₀ ≤ u → Regime (shiftA P u) D := by
  first | exact @GlobalTheory.HSNef.regime_shiftA | exact GlobalTheory.HSNef.regime_shiftA | (intros; apply GlobalTheory.HSNef.regime_shiftA <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalGenerationAmplePairMultiples
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalGenerationAmplePairMultiples
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef.AmpleGen

theorem exists_genAt_mul : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ P : Pair p, IsAmpleLB P.A.B → ∃ c₀ : ℕ, 0 < c₀ ∧ ∀ j : ℕ, GenAt P (c₀ * j) := by
  intro k _ X _ p D _ P hA
  obtain ⟨c, hc, N, s, hs⟩ := hA.exists_isGenerated_pow
  have hrep : P.Rep 0 (c : ℤ) (P.A.pow c) := by
    have := Pair.rep_pow k X p P 0 1 P.A c (Pair.rep_base k X p P).2.1
    simpa using this
  obtain ⟨e, -, hrange, hnu, -⟩ := RepDict.rep_dict k X p P 0 c (P.A.pow c) hrep
  have hmem : ∀ i, e (s i) ∈ P.H 0 c := fun i => by
    have : e (s i) ∈ Set.range e := ⟨s i, rfl⟩
    rw [hrange] at this
    exact this
  have hne : ∀ (σ : k →+* ℂ) (y : CxPts p σ), ∃ i, P.nu 0 c σ y (e (s i)) ≠ 0 := by
    intro σ y
    obtain ⟨i, hi⟩ := exists_mem_ptsIn hs y
    refine ⟨i, fun h0 => ?_⟩
    have h2 := hnu (s i) σ y
    have hpick := mem_pick ((P.A.pow c).φ σ).isLB y
    have hv := (secVal_ne_zero_iff (s i) hpick).2 hi
    have hpos : ((P.A.pow c).φ σ).nsq (secVal p σ (s i)) y ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (norm_ne_zero_iff.2 hv)) (Real.exp_pos _).ne'
    rw [h0] at h2
    exact hpos (by rw [← h2]; ring)
  refine ⟨c, hc, fun j => ⟨N, fun i => e (s i) ^ j, fun i => ?_, fun σ y => ?_⟩⟩
  · obtain ⟨h1, -⟩ := NuPow.pow_mem_H_and_nu_pow k X p P 0 c (e (s i)) (hmem i) j
    have e1 : (j : ℤ) * 0 = 0 := by ring
    have e2 : (j : ℤ) * c = ((c * j : ℕ) : ℤ) := by push_cast; ring
    rw [e1, e2] at h1
    exact h1
  · obtain ⟨i, hi⟩ := hne σ y
    obtain ⟨-, h2⟩ := NuPow.pow_mem_H_and_nu_pow k X p P 0 c (e (s i)) (hmem i) j
    have e1 : (j : ℤ) * 0 = 0 := by ring
    have e2 : (j : ℤ) * c = ((c * j : ℕ) : ℤ) := by push_cast; ring
    have h3 := h2 σ y
    rw [e1, e2] at h3
    exact ⟨i, by rw [h3]; exact pow_ne_zero _ hi⟩

end GlobalTheory.HSNef.AmpleGen
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalGenerationAmplePairMultiplesStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_globalGeneration_ample_pair_multiples : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ P : Pair p, IsAmpleLB P.A.B → ∃ c₀ : ℕ, 0 < c₀ ∧ ∀ j : ℕ, GenAt P (c₀ * j) := by
  first | exact @GlobalTheory.HSNef.AmpleGen.exists_genAt_mul | exact GlobalTheory.HSNef.AmpleGen.exists_genAt_mul | (intros; apply GlobalTheory.HSNef.AmpleGen.exists_genAt_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermPairSectionsGoodShiftSecondBundleNormPair
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermPairSectionsGoodShiftSecondBundleNormPair
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem nu_shiftA {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} (P : Pair p) (u : ℝ)
    (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField) :
    (shiftA P u).nu a b σ y f = P.nu a b σ y f * Real.exp (-(b * u)) := by
  change ‖ratVal (P.loc a b f (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y)) y‖ *
      Real.exp (-(a * (P.L.φ σ).φ (pick (P.L.φ σ).isLB y) y +
        b * ((P.A.φ σ).φ (pick (P.A.φ σ).isLB y) y + 2 * u)) / 2) = _
  rw [Pair.nu, mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem Bl_subset_shiftA {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} (P : Pair p) {u : ℝ}
    (hu : 0 ≤ u) (a b : ℤ) (hb : 0 ≤ b) {R : ℝ} {f : X.functionField} (hf : f ∈ P.Bl a b R) :
    f ∈ (shiftA P u).Bl a b R := by
  refine ⟨hf.1, fun σ y => ?_⟩
  rw [nu_shiftA]
  have h1 : Real.exp (-(b * u)) ≤ 1 := Real.exp_le_one_iff.2 (by
    have : (0 : ℝ) ≤ b := by exact_mod_cast hb
    nlinarith)
  have h0 : 0 ≤ P.nu a b σ y f := by unfold Pair.nu; positivity
  have h2 : R ≥ P.nu a b σ y f := hf.2 σ y
  nlinarith [Real.exp_pos (-(b * u))]

theorem good_shiftA : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
    ∀ (P : Pair p) (b : ℕ) (s t : X.functionField) (u : ℝ), 0 ≤ u → P.Good D b s t → (shiftA P u).Good D b s t := by
  intro k _ X _ p D hX P b s t u hu h
  exact
    { ample := h.ample
      nef := GlobalTheory.NefShift.isNef_shift_nonneg k X p D hX P.A u hu h.nef
      pos := h.pos
      s_mem := Bl_subset_shiftA P hu 0 1 zero_le_one h.s_mem
      s_ne := h.s_ne
      t_mem := Bl_subset_shiftA P hu (-1) b (Int.natCast_nonneg b) h.t_mem
      t_ne := h.t_ne
      reg := h.reg }

end GlobalTheory.HSNef
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermPairSectionsGoodShiftSecondBundleNormPairStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermPairSections_good_shiftSecondBundleNormPair : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (b : ℕ) (s t : X.functionField) (u : ℝ), 0 ≤ u → P.Good D b s t → (shiftA P u).Good D b s t := by
  first | exact @GlobalTheory.HSNef.good_shiftA | exact GlobalTheory.HSNef.good_shiftA | (intros; apply GlobalTheory.HSNef.good_shiftA <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodHermPairAdaptedTwist
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem exists_good_pair_twist : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ L N : HermLB p, ∃ (P : Pair p) (b : ℕ) (s t : X.functionField) (c : ℕ),
    P.L = L ∧ P.Good D b s t ∧ GenAt P c ∧ Regime P D ∧ Le ((P.A.pow c).dual) N := by
  intro hAC hHS k _ X _ p D hX L N
  obtain ⟨P₀, b, s, t, hL, hG⟩ := GlobalTheory.VolBr.exists_good_pair hAC k X p D hX L
  obtain ⟨c₀, hc₀, hgen⟩ := GlobalTheory.T.exists_globalGeneration_ample_pair_multiples k X p D hX P₀ hG.ample
  obtain ⟨c₁, hc₁⟩ := GlobalTheory.T.exists_small_section_add_multiple_ample_after_shift k X p D hX P₀ N s hG.ample hG.s_mem.1 hG.s_ne
  have hc : c₁ ≤ c₀ * (c₁ + 1) := by nlinarith
  have hcpos : 0 < c₀ * (c₁ + 1) := Nat.mul_pos hc₀ (Nat.succ_pos _)
  obtain ⟨u₁, hu₁⟩ := hc₁ (c₀ * (c₁ + 1)) hc hcpos
  obtain ⟨u₂, hu₂⟩ := GlobalTheory.T.exists_shift_smallSectionCount_regime_from_radius_one hAC hHS k X p D hX P₀ hG.ample hG.nef.semiPos
  refine ⟨shiftA P₀ (max 0 (max u₁ u₂)), b, s, t, c₀ * (c₁ + 1), hL, ?_, ?_, ?_, ?_⟩
  · exact GlobalTheory.T.hermPairSections_good_shiftSecondBundleNormPair k X p D hX P₀ b s t _ (le_max_left _ _) hG
  · exact (GlobalTheory.T.shiftSecondBundleNormPair_norm_ball_generation k X p P₀ _).2.2 _ (hgen (c₁ + 1))
  · exact hu₂ _ (le_trans (le_max_right _ _) (le_max_right _ _))
  · exact hu₁ _ (le_trans (le_max_left _ _) (le_max_right _ _))

end GlobalTheory.HSNef
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodHermPairAdaptedTwistStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_goodHermPair_adapted_twist : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ L N : HermLB p, ∃ (P : Pair p) (b : ℕ) (s t : X.functionField) (c : ℕ), P.L = L ∧ P.Good D b s t ∧ GenAt P c ∧ Regime P D ∧ Le ((P.A.pow c).dual) N := by
  first | exact @GlobalTheory.HSNef.exists_good_pair_twist | exact GlobalTheory.HSNef.exists_good_pair_twist | (intros; apply GlobalTheory.HSNef.exists_good_pair_twist <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EncardSmallSectionsLeOfHermLBLeBySmallSection
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EncardSmallSectionsLeOfHermLBLeBySmallSection
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNef.LeCard

theorem encard_smallSec_le : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k),
    ∀ A B : HermLB p, Le B A → B.smallSec.encard ≤ A.smallSec.encard := by
  intro k _ X _ p A B hBA
  obtain ⟨P, rfl, rfl, h1⟩ := hBA
  have hrep := Pair.rep_base k X p P
  have eL : P.L.smallSec.encard = (P.Bl 1 0 1).encard :=
    SmallBall.encard_eq_Bl P hrep.1 P.L.smallSec 1 zero_le_one fun u => by
      simp only [HermLB.smallSec, Set.mem_setOf_eq, one_pow]
  have eA : P.A.smallSec.encard = (P.Bl 0 1 1).encard :=
    SmallBall.encard_eq_Bl P hrep.2.1 P.A.smallSec 1 zero_le_one fun u => by
      simp only [HermLB.smallSec, Set.mem_setOf_eq, one_pow]
  rw [eL, eA]
  refine Set.encard_le_encard fun f hf => ?_
  have e := NuMul.mul_mem_H_and_nu_mul k X p P 1 (-1) 0 1 1 f h1.1 hf.1
  rw [one_mul, add_zero, neg_add_cancel] at e
  refine ⟨e.1, fun σ y => ?_⟩
  rw [e.2 σ y]
  calc P.nu 1 (-1) σ y 1 * P.nu 0 1 σ y f ≤ 1 * 1 :=
        mul_le_mul (h1.2 σ y) (hf.2 σ y) (SmallBall.nu_nonneg P 0 1 σ y f) zero_le_one
    _ = 1 := one_mul 1

end GlobalTheory.HSNef.LeCard
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EncardSmallSectionsLeOfHermLBLeBySmallSectionStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.encard_smallSections_le_of_hermLBLeBySmallSection : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ A B : HermLB p, Le B A → B.smallSec.encard ≤ A.smallSec.encard := by
  first | exact @GlobalTheory.HSNef.LeCard.encard_smallSec_le | exact GlobalTheory.HSNef.LeCard.encard_smallSec_le | (intros; apply GlobalTheory.HSNef.LeCard.encard_smallSec_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHilbertSamuelLowerBoundSemiPosNefOnFibres
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNef.LowerNef

theorem main : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L N : HermLB p) (a : ℝ), NefFib L → L.SemiPos D → L.IsSelfInter a → ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop, (a / (D + 1).factorial - ε) * (m : ℝ) ^ (D + 1) ≤ Real.log (((L.pow m).tens N).smallSec.ncard : ℝ) := by
  intro hAr hHS k _ X _ p D hX L N a hNef hSP hSI ε hε
  obtain ⟨P, b, s, t, c, hPL, hG, hGen, hReg, hLe⟩ := GlobalTheory.T.exists_goodHermPair_adapted_twist hAr hHS k X p D hX L N
  subst hPL
  have hlow := GlobalTheory.T.smallSections_lowerBound_ample_minus_twist hAr hHS k X p D hX P b s t hG c hGen hReg hNef hSP a hSI ε hε
  filter_upwards [hlow] with m hm
  obtain ⟨h1, h2, -⟩ := Pair.rep_base k X p P
  have hRep : P.Rep (m : ℤ) (-(c : ℤ)) ((P.L.pow m).tens ((P.A.pow c).dual)) := by
    have := Pair.rep_tens k X p P _ _ _ _ _ _ (Pair.rep_pow k X p P _ _ _ m h1)
      (Pair.rep_dual k X p P _ _ _ (Pair.rep_pow k X p P _ _ _ c h2))
    simpa using this
  have hE := SmallBall.encard_eq_Bl P hRep ((P.L.pow m).tens ((P.A.pow c).dual)).smallSec 1 zero_le_one fun u => by
    simp only [HermLB.smallSec, Set.mem_setOf_eq, one_pow]
  have hle := GlobalTheory.T.encard_smallSections_le_of_hermLBLeBySmallSection k X p _ _ ((GlobalTheory.T.hermLBLeBySmallSection_tensor_isometric_trans_shift k X p _ _ (P.L.pow m)).1 hLe)
  have hfin := GlobalTheory.T.finite_smallSec_hermitian_line_bundle_arith_variety k X p D hX ((P.L.pow m).tens N)
  have hBle : (P.Bl m (-c) 1).encard ≤ ((P.L.pow m).tens N).smallSec.encard := hE ▸ hle
  have hBfin : (P.Bl m (-c) 1).Finite :=
    Set.finite_of_encard_le_coe (hBle.trans_eq hfin.cast_ncard_eq.symm)
  have hone : (1 : ℕ∞) ≤ (P.Bl m (-c) 1).encard :=
    hE ▸ Set.one_le_encard_iff_nonempty.2 ⟨_, ((P.L.pow m).tens ((P.A.pow c).dual)).zero_mem_smallSec⟩
  have hc1 : 1 ≤ (P.Bl m (-c) 1).ncard := by
    have := hBfin.cast_ncard_eq ▸ hone
    exact_mod_cast this
  have hc2 : (P.Bl m (-c) 1).ncard ≤ ((P.L.pow m).tens N).smallSec.ncard := by
    have := hBfin.cast_ncard_eq ▸ hfin.cast_ncard_eq ▸ hBle
    exact_mod_cast this
  refine hm.trans ?_
  unfold Pair.lc
  exact Real.log_le_log (by exact_mod_cast hc1) (by exact_mod_cast hc2)

end GlobalTheory.HSNef.LowerNef
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHilbertSamuelLowerBoundSemiPosNefOnFibresStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithHilbertSamuel_lowerBound_semiPos_nefOnFibres : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L N : HermLB p) (a : ℝ), NefFib L → L.SemiPos D → L.IsSelfInter a → ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop, (a / (D + 1).factorial - ε) * (m : ℝ) ^ (D + 1) ≤ Real.log (((L.pow m).tens N).smallSec.ncard : ℝ) := by
  first | exact @GlobalTheory.HSNef.LowerNef.main | exact GlobalTheory.HSNef.LowerNef.main | (intros; apply GlobalTheory.HSNef.LowerNef.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHilbertSamuelNefOfAmple
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

namespace GlobalTheory.HSNef

theorem arithHilbertSamuel_of_ampleHS :
    GlobalTheory.Published.ArCalc → AmpleHS → SemiPull → GlobalTheory.Published.ArithHilbertSamuel := by
  intro hC hA hS k _ X _ p D hX L N a hL ha
  refine ⟨Eventually.of_forall fun m => GlobalTheory.T.finite_smallSec_hermitian_line_bundle_arith_variety k X p D hX _, ?_⟩
  refine Asymptotics.isLittleO_iff.2 fun c hc => ?_
  have hupper : ∀ᶠ m : ℕ in atTop,
      Real.log (((L.pow m).tens N).smallSec.ncard : ℝ) ≤
        (a / (D + 1).factorial + c) * (m : ℝ) ^ (D + 1) :=
    GlobalTheory.T.arith_nef_volume_upper_bound hC hA hS k X p D hX L N a hL ha c hc
  have hlower : ∀ᶠ m : ℕ in atTop,
      (a / (D + 1).factorial - c) * (m : ℝ) ^ (D + 1) ≤
        Real.log (((L.pow m).tens N).smallSec.ncard : ℝ) :=
    GlobalTheory.T.arithHilbertSamuel_lowerBound_semiPos_nefOnFibres hC hA k X p D hX L N a (nefFib_of_isNef hL) hL.semiPos ha c hc
  filter_upwards [hupper, hlower] with m h1 h2
  have hm : ‖(m : ℝ) ^ (D + 1)‖ = (m : ℝ) ^ (D + 1) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [Real.norm_eq_abs, hm, abs_le]
  constructor <;> linarith

end GlobalTheory.HSNef
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHilbertSamuelNefOfAmpleStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithHilbertSamuel_nef_of_ample : GlobalTheory.Published.ArCalc → AmpleHS → SemiPull → GlobalTheory.Published.ArithHilbertSamuel := by
  first | exact @GlobalTheory.HSNef.arithHilbertSamuel_of_ampleHS | exact GlobalTheory.HSNef.arithHilbertSamuel_of_ampleHS | (intros; apply GlobalTheory.HSNef.arithHilbertSamuel_of_ampleHS <;> assumption)
end
end

namespace GlobalTheory

theorem arithHilbertSamuel_of_principalisation :
    GlobalTheory.Published.Principalisation → GlobalTheory.Published.ArithHilbertSamuel :=
  fun h => GlobalTheory.T.arithHilbertSamuel_nef_of_ample (GlobalTheory.MixHt.arCalc_of_principalisation h) (GlobalTheory.T.ampleArithHilbertSamuel_of_principalisation h)
    (GlobalTheory.SemiPullAll.semiPull_of_principalisation h)

end GlobalTheory
