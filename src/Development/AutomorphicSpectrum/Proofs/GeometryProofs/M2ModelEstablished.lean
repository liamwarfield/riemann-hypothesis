module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FunctionFieldDegreeEq
public import Development.WeilBound.CoreStatements.HodgeTatePoints.CiGrDeg
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.EigenFlagSlopeBound
public import Development.WeilBound.CoreStatements.HodgeTatePoints.FamilyEx
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FamilyGivesConjugateLieData

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.CiIsDeg
set_option backward.isDefEq.respectTransparency false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace PositivityTheory.HtPt.Ci

theorem chart_block {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {B : Type} [Fintype B]
    {J : B → Type} {y : (Σ k, J k) → Ω} {c : (k : B) → J k} {p : Cpt ξ} (hc : InChart ξ (segre y) c p) (k : B) :
    y ⟨k, c k⟩ ≠ 0 ∧ ∀ j, y ⟨k, j⟩ / y ⟨k, c k⟩ ∈ regAt ξ p := by
  classical
  have h0 : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hc.1 k (Finset.mem_univ k)
  refine ⟨h0 k, fun j => ?_⟩
  have h1 := hc.2 (Function.update c k j)
  rw [Conj.segre, Conj.segre, ← Finset.prod_div_distrib, Finset.prod_eq_single k (fun l _ hl => by
    rw [Function.update_of_ne hl, div_self (h0 l)]) (by simp), Function.update_self] at h1
  exact h1

theorem isdeg_coord : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Field K] (C : ACurve K) (z : Spec (CommRingCat.of K) ⟶ X) (Y : CurveIn C z) (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (w : (Σ k, J k) → K) (Λ : Lat ξ Ω) (S : Set (Cpt ξ)) (a : B → ℤ) (e₀ : Ω) (h₀ : genPt ξ ⤳ centre z) (h : ∀ i, genPt ξ ⤳ centre (Y.x i)), CoordTie ℤ ξ (segre y) → CoordsAt ξ y z w → (⟨centre z, h₀⟩ : Cpt ξ) ∈ S → (∀ i, (⟨centre (Y.x i), h i⟩ : Cpt ξ) ∈ S) → Λ.IsDegOn S y a e₀ → Y.IsDeg Λ (coordDeg C w a) := by
  intro X Ω _ ξ K _ C z Y B _ J _ y w Λ S a e₀ h₀ h tie hw hz hS hΛ
  classical
  have hξ := tie.gen
  have hval : ∀ k c, w ⟨k, c⟩ ≠ 0 → y ⟨k, c⟩ ≠ 0 ∧ ∀ j, ValAt ξ z (y ⟨k, j⟩ / y ⟨k, c⟩) (w ⟨k, j⟩ / w ⟨k, c⟩) := by
    intro k c hc
    obtain ⟨h1, h2⟩ := hw.2 k c (IsUnit.mk0 _ hc)
    refine ⟨h1, fun j => ?_⟩
    obtain ⟨r, hr, e⟩ := h2 j
    rwa [e, mul_div_cancel_right₀ _ hc]
  choose c₀ hc₀ using hw.1
  replace hc₀ := fun k => (hc₀ k).ne_zero
  have ch₀ : InChart ξ (segre y) c₀ ⟨centre z, h₀⟩ := by
    refine ⟨Finset.prod_ne_zero_iff.2 fun k _ => (hval k _ (hc₀ k)).1, fun c' => ?_⟩
    rw [Conj.segre, Conj.segre, ← Finset.prod_div_distrib]
    exact prod_mem fun k _ => Val.mem ((hval k _ (hc₀ k)).2 _) h₀
  choose c hc using fun i => tie.cover ⟨centre (Y.x i), h i⟩
  have hint : ∀ i k j, ∃ ρ : K, C.v i ρ ≤ 1 ∧ ValAt ξ z (y ⟨k, j⟩ / y ⟨k, c i k⟩) ρ := by
    intro i k j
    obtain ⟨ρ, hρ⟩ := Val.of_mem ((chart_block (hc i) k).2 j)
    have := LieTangent.valAt_base hξ (C.v i).valuationSubring.subtype hρ
    rw [Y.gen i] at this
    exact ⟨_, ρ.2, this⟩
  have hne : ∀ i k, w ⟨k, c i k⟩ ≠ 0 := by
    intro i k h0
    obtain ⟨ρ, -, hρ⟩ := hint i k (c₀ k)
    have h1 := Val.mul hρ ((hval k _ (hc₀ k)).2 (c i k))
    rw [div_mul_div_cancel₀ (chart_block (hc i) k).1, div_self (hval k _ (hc₀ k)).1, h0, zero_div, mul_zero] at h1
    exact zero_ne_one (LieTangent.valAt_unique hξ h1 (Val.one h₀))
  have hsup : ∀ i k, (Finset.univ.sup fun j : J k => C.v i (w ⟨k, j⟩)) = C.v i (w ⟨k, c i k⟩) := by
    intro i k
    refine le_antisymm (Finset.sup_le fun j _ => ?_) (Finset.le_sup (f := fun j : J k => C.v i (w ⟨k, j⟩))
      (Finset.mem_univ _))
    obtain ⟨ρ, h1, hρ⟩ := hint i k j
    rw [LieTangent.valAt_unique hξ hρ ((hval k _ (hne i k)).2 j), map_div₀] at h1
    exact (div_le_one₀ ((C.v i).pos_iff.2 (hne i k))).1 h1
  have hgen : ∀ p ∈ S, ∀ c, InChart ξ (segre y) c p → Λ.IsGenAt p ((∏ k, y ⟨k, c k⟩ ^ a k) * e₀) := fun p hp c hc =>
    ⟨mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (chart_block hc k).1) hΛ.1, hΛ.2 p hp c hc⟩
  have hF : (⋃ q : {q : Σ k, J k // w q ≠ 0}, {i | C.v i (w q.1) ≠ 1}).Finite :=
    Set.finite_iUnion fun q => C.fin _ q.2
  have hgood : ∀ i ∉ hF.toFinset, ∀ q, w q ≠ 0 → C.v i (w q) = 1 := by
    intro i hi q hq
    by_contra hcon
    exact hi (hF.mem_toFinset.2 (Set.mem_iUnion.2 ⟨⟨q, hq⟩, hcon⟩))
  have hfs : ∀ f : C.I → ℤ, (∀ i ∉ hF.toFinset, f i = 0) → ∑ᶠ i, f i = ∑ i ∈ hF.toFinset, f i := fun f hf =>
    finsum_eq_sum_of_support_subset f fun i hi => by_contra fun hc => hi (hf i hc)
  have hr : ∀ i ∉ hF.toFinset, C.v i (∏ k, (w ⟨k, c i k⟩ / w ⟨k, c₀ k⟩) ^ a k) = 1 := by
    intro i hi
    simp only [map_prod, map_zpow₀, map_div₀, hgood i hi _ (hne i _), hgood i hi _ (hc₀ _), div_one, one_zpow,
      Finset.prod_const_one]
  refine ⟨h₀, h, _, _, fun i => ∏ k, (w ⟨k, c i k⟩ / w ⟨k, c₀ k⟩) ^ a k, hgen _ hz _ ch₀,
    fun i => hgen _ (hS i) _ (hc i), fun i => ⟨Finset.prod_ne_zero_iff.2 fun k _ =>
      zpow_ne_zero _ (div_ne_zero (hne i k) (hc₀ k)), ?_⟩, hF.subset fun i hi => ?_, ?_⟩
  · rw [mul_div_mul_right _ _ hΛ.1, ← Finset.prod_div_distrib]
    refine Val.prod h₀ _ fun k => ?_
    rw [← div_zpow]
    refine Val.zpow ((hval k _ (hc₀ k)).2 _) ?_ _
    rw [inv_div, inv_div]
    exact (hval k _ (hne i k)).2 _
  · by_contra hcon
    exact hi (hr i fun h' => hcon (hF.mem_toFinset.1 h'))
  · have hlog : ∀ i, WithZero.log (C.v i (∏ k, (w ⟨k, c i k⟩ / w ⟨k, c₀ k⟩) ^ a k)) =
        ∑ k, a k * (WithZero.log (C.v i (w ⟨k, c i k⟩)) - WithZero.log (C.v i (w ⟨k, c₀ k⟩))) := by
      intro i
      have key : ∀ T : Finset B, WithZero.log (C.v i (∏ k ∈ T, (w ⟨k, c i k⟩ / w ⟨k, c₀ k⟩) ^ a k)) =
          ∑ k ∈ T, a k * (WithZero.log (C.v i (w ⟨k, c i k⟩)) - WithZero.log (C.v i (w ⟨k, c₀ k⟩))) := by
        intro T
        induction T using Finset.induction_on with
        | empty => simp
        | insert k T hk ih =>
          rw [Finset.prod_insert hk, Finset.sum_insert hk, map_mul, WithZero.log_mul, ih, map_zpow₀,
            WithZero.log_zpow, map_div₀, WithZero.log_div, smul_eq_mul]
          · exact (Valuation.ne_zero_iff _).2 (hne i k)
          · exact (Valuation.ne_zero_iff _).2 (hc₀ k)
          · exact (Valuation.ne_zero_iff _).2 (zpow_ne_zero _ (div_ne_zero (hne i k) (hc₀ k)))
          · exact (Valuation.ne_zero_iff _).2 (Finset.prod_ne_zero_iff.2 fun k _ =>
              zpow_ne_zero _ (div_ne_zero (hne i k) (hc₀ k)))
      exact key _
    have hp : ∀ k, ∑ i ∈ hF.toFinset, (C.w i : ℤ) * WithZero.log (C.v i (w ⟨k, c₀ k⟩)) = 0 := fun k => by
      rw [← hfs _ fun i hi => by rw [hgood i hi _ (hc₀ k)]; simp]
      exact C.prod _ (hc₀ k)
    rw [hfs _ fun i hi => by rw [hr i hi]; simp]
    simp only [coordDeg, hsup, hlog, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hfs _ fun i hi => by rw [hgood i hi _ (hne i k)]; simp]
    simp only [mul_left_comm _ (a k), mul_sub, ← Finset.mul_sum, Finset.sum_sub_distrib, hp, mul_zero, sub_zero]

end PositivityTheory.HtPt.Ci
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.NefThresholdGapCondition
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.NefThresholdGapCondition
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.Conj.GapThreshold

theorem ent_of_lt {T : Type} [Fintype T] {N : ℕ} (mu : GlobalTheory.CompanionTheory.Ar.Top.Wt T N) (τ : T) {i : ℕ} (h : i < N) :
    GlobalTheory.CompanionTheory.Ar.Top.ent mu τ i = mu τ ⟨i, h⟩ := by
  unfold GlobalTheory.CompanionTheory.Ar.Top.ent
  rw [dif_pos h]

theorem abs_le_norm {T : Type} [Fintype T] {N : ℕ} (mu : GlobalTheory.CompanionTheory.Ar.Top.Wt T N) (τ : T) (i : Fin N) :
    |mu τ i| ≤ ‖mu‖ := by
  have h1 : ‖mu τ i‖ ≤ ‖mu τ‖ := norm_le_pi_norm (mu τ) i
  have h2 : ‖mu τ‖ ≤ ‖mu‖ := norm_le_pi_norm mu τ
  rw [Real.norm_eq_abs] at h1
  exact h1.trans h2

theorem gapCond_of_threshold {T : Type} [Fintype T] {N j p : ℕ} (mu : GlobalTheory.CompanionTheory.Ar.Top.Wt T N)
    (hp : 2 < p) (hj : 1 ≤ j) (hjN : j < N) (hd : GlobalTheory.CompanionTheory.Ar.Top.Dominant mu)
    (ht : GlobalTheory.CompanionTheory.Ar.Top.NefThreshold j p mu) :
    GapCond p j (N - j) (fun τ i => GlobalTheory.CompanionTheory.Ar.Top.ent mu τ (i - 1)) := by
  unfold GlobalTheory.CompanionTheory.Ar.Top.NefThreshold GlobalTheory.CompanionTheory.Ar.Top.gap at ht
  unfold GlobalTheory.CompanionTheory.Ar.Top.Dominant at hd
  have hp' : (0 : ℝ) < (p : ℝ) - 2 := by
    have : (2 : ℝ) < p := by exact_mod_cast hp
    linarith
  unfold GapCond
  refine ⟨?_, ‖mu‖, 4 * (Fintype.card T) * ‖mu‖ / ((p : ℝ) - 2), ?_, ?_, ?_⟩
  · intro τ i hi hiN
    have h1 : i < N := by omega
    have h0 : i - 1 < N := by omega
    simp only [Nat.add_sub_cancel]
    rw [ent_of_lt mu τ h1, ent_of_lt mu τ h0]
    exact hd τ ⟨i - 1, h0⟩ ⟨i, h1⟩ (Fin.mk_le_mk.2 (by omega))
  · intro τ i hi hiN
    have h0 : i - 1 < N := by omega
    simp only
    rw [ent_of_lt mu τ h0]
    exact abs_le_norm mu τ _
  · intro τ
    simp only [Nat.add_sub_cancel]
    rw [div_le_iff₀ hp']
    linarith [ht τ, mul_comm ((p : ℝ) - 2) (GlobalTheory.CompanionTheory.Ar.Top.ent mu τ (j - 1) - GlobalTheory.CompanionTheory.Ar.Top.ent mu τ j)]
  · have e : ((p : ℝ) - 2) * (4 * (Fintype.card T) * ‖mu‖ / ((p : ℝ) - 2)) = 4 * (Fintype.card T) * ‖mu‖ := by
      field_simp
    exact e.ge

theorem lmuNum_eq_sum {T : Type} [Fintype T] {N j : ℕ} (mu : GlobalTheory.CompanionTheory.Ar.Top.Wt T N)
    (x : T × Fin N → ℝ) (w l : T → ℕ → ℝ) (hjN : j < N)
    (hx : ∀ τ (i : Fin N), (i : ℕ) < j → x (τ, i) = w τ (i + 1) - w τ i)
    (hy : ∀ τ (i : Fin N), j ≤ (i : ℕ) → x (τ, i) = -(l τ (N - 1 - i + 1) - l τ (N - 1 - i))) :
    lmuNum j (N - j) (fun τ i => GlobalTheory.CompanionTheory.Ar.Top.ent mu τ (i - 1)) w l = ∑ r : T × Fin N, -mu r.1 r.2 * x r := by
  classical
  unfold lmuNum
  set xx : T → ℕ → ℝ := fun τ i => if h : i < N then x (τ, ⟨i, h⟩) else 0 with hxx
  have hrow : ∀ τ, ∑ i : Fin N, -mu τ i * x (τ, i) =
      ∑ i ∈ Finset.range N, -GlobalTheory.CompanionTheory.Ar.Top.ent mu τ i * xx τ i := by
    intro τ
    rw [← Fin.sum_univ_eq_sum_range (fun i => -GlobalTheory.CompanionTheory.Ar.Top.ent mu τ i * xx τ i) N]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hxx, dif_pos i.isLt, ent_of_lt mu τ i.isLt]
  rw [Fintype.sum_prod_type, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [hrow τ, ← Finset.sum_range_add_sum_Ico _ hjN.le, Finset.sum_Ico_eq_sum_range, neg_add]
  congr 1
  · rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hij : i < j := Finset.mem_range.1 hi
    have hiN : i < N := by omega
    have hx' := hx τ ⟨i, hiN⟩ hij
    simp only [hxx, dif_pos hiN, Nat.add_sub_cancel, hx']
    ring
  · rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hmj : m < N - j := Finset.mem_range.1 hm
    have hiN : j + m < N := by omega
    have hy' := hy τ ⟨j + m, hiN⟩ (by simp)
    have e1 : N - 1 - (j + m) + 1 = N - j - m := by omega
    have e2 : N - 1 - (j + m) = N - j - m - 1 := by omega
    simp only [hxx, dif_pos hiN, Nat.add_sub_cancel, hy']
    rw [e1, e2]
    ring

theorem gapCond_and_lmuNum : ∀ (T : Type) [Fintype T] (N j p : ℕ) (mu : GlobalTheory.CompanionTheory.Ar.Top.Wt T N) (x : T × Fin N → ℝ) (w l : T → ℕ → ℝ), 2 < p → 1 ≤ j → j < N → GlobalTheory.CompanionTheory.Ar.Top.Dominant mu → GlobalTheory.CompanionTheory.Ar.Top.NefThreshold j p mu → (∀ τ (i : Fin N), (i : ℕ) < j → x (τ, i) = w τ (i + 1) - w τ i) → (∀ τ (i : Fin N), j ≤ (i : ℕ) → x (τ, i) = -(l τ (N - 1 - i + 1) - l τ (N - 1 - i))) → GapCond p j (N - j) (fun τ i => GlobalTheory.CompanionTheory.Ar.Top.ent mu τ (i - 1)) ∧ lmuNum j (N - j) (fun τ i => GlobalTheory.CompanionTheory.Ar.Top.ent mu τ (i - 1)) w l = ∑ r : T × Fin N, -mu r.1 r.2 * x r := by
  intro T _ N j p mu x w l hp hj hjN hd ht hx hy
  exact ⟨gapCond_of_threshold mu hp hj hjN hd ht, lmuNum_eq_sum mu x w l hjN hx hy⟩

end GlobalTheory.CompanionTheory.Ar.Conj.GapThreshold
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.NefThresholdGapConditionStatement
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nef_threshold_gap_condition : ∀ (T : Type) [Fintype T] (N j p : ℕ) (mu : GlobalTheory.CompanionTheory.Ar.Top.Wt T N) (x : T × Fin N → ℝ) (w l : T → ℕ → ℝ), 2 < p → 1 ≤ j → j < N → GlobalTheory.CompanionTheory.Ar.Top.Dominant mu → GlobalTheory.CompanionTheory.Ar.Top.NefThreshold j p mu → (∀ τ (i : Fin N), (i : ℕ) < j → x (τ, i) = w τ (i + 1) - w τ i) → (∀ τ (i : Fin N), j ≤ (i : ℕ) → x (τ, i) = -(l τ (N - 1 - i + 1) - l τ (N - 1 - i))) → GapCond p j (N - j) (fun τ i => GlobalTheory.CompanionTheory.Ar.Top.ent mu τ (i - 1)) ∧ lmuNum j (N - j) (fun τ i => GlobalTheory.CompanionTheory.Ar.Top.ent mu τ (i - 1)) w l = ∑ r : T × Fin N, -mu r.1 r.2 * x r := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Conj.GapThreshold.gapCond_and_lmuNum | exact GlobalTheory.CompanionTheory.Ar.Conj.GapThreshold.gapCond_and_lmuNum | (intros; apply GlobalTheory.CompanionTheory.Ar.Conj.GapThreshold.gapCond_and_lmuNum <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.M2CurveEstablished
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CurveLieEigenDegree
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CurveFamilyFormalGerm
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CurveFamilyFormalGerm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.curve_family_formal_germ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0), PowFns t → ∀ (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (C : ACurve K) (z : Sp K ⟶ X0) (Y : CurveIn C z), (∀ i, FibPF t (GlobalTheory.CompanionTheory.Ar.centre (Y.x i))) → ∃ (d : ℕ) (F : Family C p d (𝓞 E)) (g : GermAt t z d), g.B = F.B ∧ ∀ i, ∃ gi : GermAt t (Y.x i) d, ∀ l, IsCombAtG t z g.tg (fun j => lin (F.φ i) 1 j l) (spMap (GlobalTheory.CompanionTheory.Ar.dualMap (C.v i).valuationSubring.subtype) ≫ gi.tg l) := by
  first | exact @PositivityTheory.HtPt.Cf.family_ex | exact PositivityTheory.HtPt.Cf.family_ex
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CurveFamilyFormalGermStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.curve_family_formal_germ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0), PowFns t → ∀ (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (C : ACurve K) (z : Sp K ⟶ X0) (Y : CurveIn C z), (∀ i, FibPF t (GlobalTheory.CompanionTheory.Ar.centre (Y.x i))) → ∃ (d : ℕ) (F : Family C p d (𝓞 E)) (g : GermAt t z d), g.B = F.B ∧ ∀ i, ∃ gi : GermAt t (Y.x i) d, ∀ l, IsCombAtG t z g.tg (fun j => lin (F.φ i) 1 j l) (spMap (GlobalTheory.CompanionTheory.Ar.dualMap (C.v i).valuationSubring.subtype) ≫ gi.tg l) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.curve_family_formal_germ | exact GlobalTheory.CompanionTheory.Relay.curve_family_formal_germ | (intros; apply GlobalTheory.CompanionTheory.Relay.curve_family_formal_germ <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CurveLieEigenDegree
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Conj.TopH2

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}}

theorem comp_one_over {G T T' : Over X0} [GrpObj G] (f : T' ⟶ T) : f ≫ (1 : T ⟶ G) = 1 := by
  show f ≫ (toUnit T ≫ η[G]) = toUnit T' ≫ η[G]
  rw [← Category.assoc, toUnit_unique (f ≫ toUnit T) (toUnit T')]

theorem comp_prod_ofFn {G T T' : Over X0} [GrpObj G] (f : T' ⟶ T) :
    ∀ {m : ℕ} (u : Fin m → (T ⟶ G)), f ≫ (List.ofFn u).prod = (List.ofFn fun l => f ≫ u l).prod
  | 0, u => by simp only [List.ofFn_zero, List.prod_nil]; exact comp_one_over f
  | m + 1, u => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, MonObj.comp_mul,
      comp_prod_ofFn f (fun l => u l.succ)]

theorem spMap_comp_eq {A B C D : Type} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    (a : B →+* C) (b : A →+* B) (c : D →+* C) (d : A →+* D) (h : a.comp b = c.comp d) :
    spMap a ≫ spMap b = spMap c ≫ spMap d := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h]

section Rings

variable {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R')

theorem dualMap_comp_algebraMap :
    (GlobalTheory.CompanionTheory.Ar.dualMap f).comp (algebraMap R (DualNumber R)) = (algebraMap R' (DualNumber R')).comp f := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem dualMap_comp_epsMul (c : R) :
    (GlobalTheory.CompanionTheory.Ar.dualMap f).comp (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul c) =
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul (f c)).comp (GlobalTheory.CompanionTheory.Ar.dualMap f) := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;>
    simp [GlobalTheory.CompanionTheory.Ar.dualMap, ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul, mul_comm]

theorem fst_comp_dualMap :
    (TrivSqZeroExt.fstHom R' R' R').toRingHom.comp (GlobalTheory.CompanionTheory.Ar.dualMap f) =
      f.comp (TrivSqZeroExt.fstHom R R R).toRingHom := by
  refine RingHom.ext fun a => ?_
  simp [GlobalTheory.CompanionTheory.Ar.dualMap]

end Rings

variable (t : SAB H X0)

theorem isTanAt_iff {S : Type} [CommRing S] (x : Sp S ⟶ X0) (w : GlobalTheory.CompanionTheory.Ar.epsAt x ⟶ t.G) :
    GlobalTheory.CompanionTheory.Ar.IsTanAt t.G x w ↔ IsTanAtG t x w.left :=
  ⟨fun h => ⟨Over.w w, h⟩, fun h => h.2⟩

theorem isTanAtG_map {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {x : Sp R ⟶ X0}
    {v : Sp (DualNumber R) ⟶ t.G.left} (h : IsTanAtG t x v) :
    IsTanAtG t (spMap f ≫ x) (spMap (GlobalTheory.CompanionTheory.Ar.dualMap f) ≫ v) := by
  refine ⟨?_, ?_⟩
  · rw [Category.assoc, h.1, ← Category.assoc, ← Category.assoc,
      spMap_comp_eq _ _ _ _ (dualMap_comp_algebraMap f)]
  · rw [← Category.assoc, spMap_comp_eq _ _ _ _ (fst_comp_dualMap f), Category.assoc, h.2]
    have := comp_one_over (G := t.G) (Over.homMk (U := Over.mk (spMap f ≫ x)) (V := Over.mk x) (spMap f) rfl)
    rw [← this, Over.comp_left]
    rfl

theorem isCombAtG_map {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {x : Sp R ⟶ X0} {m : ℕ}
    {v : Fin m → (Sp (DualNumber R) ⟶ t.G.left)} {cf : Fin m → R} {w : Sp (DualNumber R) ⟶ t.G.left}
    (h : IsCombAtG t x v cf w) :
    IsCombAtG t (spMap f ≫ x) (fun l => spMap (GlobalTheory.CompanionTheory.Ar.dualMap f) ≫ v l) (fun l => f (cf l))
      (spMap (GlobalTheory.CompanionTheory.Ar.dualMap f) ≫ w) := by
  obtain ⟨u, hu, hw⟩ := h
  let k : tEpsG (spMap f ≫ x) ⟶ tEpsG x := Over.homMk (spMap (GlobalTheory.CompanionTheory.Ar.dualMap f)) (by
    simp only [Over.mk_hom]
    rw [← Category.assoc, ← Category.assoc, spMap_comp_eq _ _ _ _ (dualMap_comp_algebraMap f)])
  refine ⟨fun l => k ≫ u l, fun l => ?_, ?_⟩
  · show spMap (GlobalTheory.CompanionTheory.Ar.dualMap f) ≫ (u l).left = _
    rw [hu l, ← Category.assoc, ← Category.assoc,
      spMap_comp_eq _ _ _ _ (dualMap_comp_epsMul f (cf l))]
  · rw [← comp_prod_ofFn, Over.comp_left, hw]
    rfl

theorem pt_sum {S : Type} [CommRing S] {x : Sp S ⟶ X0} {V : Type} [AddCommGroup V] [Module S V]
    (M : GlobalTheory.CompanionTheory.Ar.LieModel t.G x V) :
    ∀ {m : ℕ} (c : Fin m → V), (List.ofFn fun l => M.pt (c l)).prod = M.pt (∑ l, c l)
  | 0, c => by
    simp only [List.ofFn_zero, List.prod_nil, Finset.univ_eq_empty, Finset.sum_empty]
    have h := M.add 0 0
    rw [add_zero] at h
    exact (mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)).symm
  | m + 1, c => by
    rw [List.ofFn_succ, List.prod_cons, pt_sum M (fun l => c l.succ), Fin.sum_univ_succ, M.add]

theorem isCombAtG_iff_lie {S : Type} [CommRing S] {x : Sp S ⟶ X0} {V : Type} [AddCommGroup V] [Module S V]
    (M : GlobalTheory.CompanionTheory.Ar.LieModel t.G x V) {m : ℕ} (b : Fin m → V) (cf : Fin m → S)
    (w : Sp (DualNumber S) ⟶ t.G.left) :
    IsCombAtG t x (fun l => (M.pt (b l)).left) cf w ↔ w = (M.pt (∑ l, cf l • b l)).left := by
  constructor
  · rintro ⟨u, hu, hw⟩
    have hu' : u = fun l => M.pt (cf l • b l) :=
      funext fun l => Over.OverMorphism.ext (by rw [hu l, M.smul]; rfl)
    rw [← hw, hu', pt_sum]
  · intro hw
    exact ⟨fun l => M.pt (cf l • b l), fun l => by rw [M.smul]; rfl, by rw [pt_sum, hw]⟩

theorem lieLat_conjData : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0), PowFns t → ∀ (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (C : ACurve K) (z : Sp K ⟶ X0) (Y : CurveIn C z), Nonempty C.I → (∀ i, FibPF t (GlobalTheory.CompanionTheory.Ar.centre (Y.x i))) → ∀ (V : Type) [AddCommGroup V] [Module K V] (M : GlobalTheory.CompanionTheory.Ar.LieModel t.G z V) (r : 𝓞 E →+* Module.End K V), M.IsActOf t.act.act r → ∃ (d : ℕ) (D : ConjData C p (𝓞 E) d) (e : V ≃ₗ[K] (Fin d → K)), (∀ i v, v ∈ Y.lieLat M i ↔ e v ∈ D.lie i) ∧ ∀ a v, e (r a v) = (D.ρ a).mulVec (e v) := by
  intro E _ _ _ H _ hbar X0 t hPow K _ p _ _ C z Y hne hFib V _ _ M r hr
  obtain ⟨d, F, g, hgB, hfam⟩ := GlobalTheory.T.curve_family_formal_germ E H hbar X0 t hPow K p C z Y hFib
  obtain ⟨D, hDρ, hDlie⟩ := GlobalTheory.T.family_gives_conjugate_lie_data K C p d (𝓞 E) F hne
  obtain ⟨e, hecomb, heact⟩ := GlobalTheory.T.formal_germ_lie_basis E H hbar X0 t K z d g V M
  refine ⟨d, D, e, fun i v => ?_, fun a v => by rw [heact r hr a v, hDρ a, hgB]⟩
  obtain ⟨gi, hgi⟩ := hfam i
  obtain ⟨hΦΨ, hΨΦ, -⟩ := GlobalTheory.T.formal_isomorphism_transport K d (𝓞 E) F.B (F.BK i) (F.φ i) (F.ψ i) (F.lam i) (F.iso i)
  have hgen : spMap (C.v i).valuationSubring.subtype ≫ Y.x i = z := Y.gen i
  have htan : ∀ l, IsTanAtG t z (spMap (GlobalTheory.CompanionTheory.Ar.dualMap (C.v i).valuationSubring.subtype) ≫ gi.tg l) :=
    fun l => by
      have h0 := isTanAtG_map t (C.v i).valuationSubring.subtype (gi.tan l)
      rwa [hgen] at h0
  choose c hc using fun l => M.onto (Over.homMk _ (htan l).1) ((isTanAt_iff t z _).2 (htan l))
  have hcl : ∀ l, (M.pt (c l)).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap (C.v i).valuationSubring.subtype) ≫ gi.tg l :=
    fun l => by rw [hc l]; rfl
  have hec : ∀ l j, e (c l) j = lin (F.φ i) 1 j l := by
    intro l
    have hw : IsTanAtG t z (M.pt (c l)).left := (isTanAt_iff t z _).1 (M.tan _)
    have := (g.basis _ hw).unique (hecomb (c l)) (by rw [hcl]; exact hgi l)
    exact fun j => congrFun this j
  have key : ∀ (a : Fin d → (C.v i).valuationSubring)
      (w : Sp (DualNumber (C.v i).valuationSubring) ⟶ t.G.left), IsCombAtG t (Y.x i) gi.tg a w →
      spMap (GlobalTheory.CompanionTheory.Ar.dualMap (C.v i).valuationSubring.subtype) ≫ w = (M.pt (∑ l, (a l : K) • c l)).left ∧
        e (∑ l, (a l : K) • c l) = (lin (F.φ i) 1).mulVec (fun l => (a l : K)) := by
    intro a w hw
    refine ⟨?_, ?_⟩
    · have h1 := isCombAtG_map t (C.v i).valuationSubring.subtype hw
      rw [hgen] at h1
      have h2 : (fun l => spMap (GlobalTheory.CompanionTheory.Ar.dualMap (C.v i).valuationSubring.subtype) ≫ gi.tg l) =
          fun l => (M.pt (c l)).left := funext fun l => (hcl l).symm
      rw [h2] at h1
      exact (isCombAtG_iff_lie t M c _ _).1 h1
    · funext j
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sum, Matrix.mulVec, dotProduct, hec, mul_comm]
  constructor
  · intro hv
    have hsub : Y.lieLat M i ≤ (D.lie i).comap e.toLinearMap.toAddMonoidHom := by
      refine (AddSubgroup.closure_le _).2 ?_
      rintro v ⟨w, hw, hvw⟩
      obtain ⟨a, ha, -⟩ := gi.basis w.left ((isTanAt_iff t (Y.x i) w).1 hw)
      obtain ⟨hbc, hea⟩ := key a w.left ha
      have hv' : v = ∑ l, (a l : K) • c l := M.inj (Over.OverMorphism.ext (hvw.trans hbc))
      show e v ∈ D.lie i
      rw [hDlie, hv', hea, Matrix.mulVec_mulVec, hΨΦ, Matrix.one_mulVec]
      intro j
      exact (a j).2
    exact hsub hv
  · intro hv
    have hint : ∀ j, C.v i ((lin (F.ψ i) 1).mulVec (e v) j) ≤ 1 := (hDlie i (e v)).1 hv
    let a : Fin d → (C.v i).valuationSubring := fun j => ⟨_, hint j⟩
    obtain ⟨Vi, _, _, ⟨Mi⟩⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists X0 t.G (C.v i).valuationSubring (Y.x i)
    choose b hb using fun l =>
      Mi.onto (Over.homMk (gi.tg l) (gi.tan l).1) ((isTanAt_iff t (Y.x i) _).2 (gi.tan l))
    have hbl : ∀ l, (Mi.pt (b l)).left = gi.tg l := fun l => by rw [hb l]; rfl
    have hcomb : IsCombAtG t (Y.x i) gi.tg a (Mi.pt (∑ l, a l • b l)).left := by
      have h3 := (isCombAtG_iff_lie t Mi b a (Mi.pt (∑ l, a l • b l)).left).2 rfl
      have h2 : (fun l => (Mi.pt (b l)).left) = gi.tg := funext hbl
      rwa [h2] at h3
    obtain ⟨hbc, hea⟩ := key a _ hcomb
    have hsum : ∑ l, (a l : K) • c l = v := by
      apply e.injective
      rw [hea]
      show (lin (F.φ i) 1).mulVec ((lin (F.ψ i) 1).mulVec (e v)) = e v
      rw [Matrix.mulVec_mulVec, hΦΨ, Matrix.one_mulVec]
    refine AddSubgroup.subset_closure ⟨Mi.pt (∑ l, a l • b l), Mi.tan _, ?_⟩
    rw [← hsum]
    exact hbc.symm

end GlobalTheory.CompanionTheory.Ar.Conj.TopH2
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CurveLieEigenDegreeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.curve_lie_eigen_degree : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0), PowFns t → ∀ (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (C : ACurve K) (z : Sp K ⟶ X0) (Y : CurveIn C z), Nonempty C.I → (∀ i, FibPF t (GlobalTheory.CompanionTheory.Ar.centre (Y.x i))) → ∀ (V : Type) [AddCommGroup V] [Module K V] (M : GlobalTheory.CompanionTheory.Ar.LieModel t.G z V) (r : 𝓞 E →+* Module.End K V), M.IsActOf t.act.act r → ∃ (d : ℕ) (D : ConjData C p (𝓞 E) d) (e : V ≃ₗ[K] (Fin d → K)), (∀ i v, v ∈ Y.lieLat M i ↔ e v ∈ D.lie i) ∧ ∀ a v, e (r a v) = (D.ρ a).mulVec (e v) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Conj.TopH2.lieLat_conjData | exact GlobalTheory.CompanionTheory.Ar.Conj.TopH2.lieLat_conjData | (intros; apply GlobalTheory.CompanionTheory.Ar.Conj.TopH2.lieLat_conjData <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.M2CurveEstablished
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Conj.CurveDegreeNonneg

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

theorem subDeg_map {K : Type} [Field K] (C : ACurve K) {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {d : ℕ} (L : C.I → AddSubgroup V) (L' : C.I → AddSubgroup (Fin d → K))
    (e : V ≃ₗ[K] (Fin d → K)) (hL' : IsBun C L') (h : ∀ i v, v ∈ L i ↔ e v ∈ L' i)
    (U : Submodule K V) :
    subDeg C L' (U.map (e : V →ₗ[K] (Fin d → K))) = subDeg C L U := by
  have hb := (GlobalTheory.CompanionTheory.Ar.Crv.SubQuot.isBun_sub_quot K C (Fin d → K) L' (U.map (e : V →ₗ[K] (Fin d → K))) hL').1
  refine (GlobalTheory.CompanionTheory.Ar.Crv.DegEquiv.deg_equiv K C _ _ (sub C L' (U.map (e : V →ₗ[K] (Fin d → K)))) (sub C L U)
    (e.submoduleMap U).symm hb ?_).2.symm
  intro i x
  have hx : e ((e.submoduleMap U).symm x : V) = x := by
    have := (e.submoduleMap U).apply_symm_apply x
    exact congrArg Subtype.val this
  simp only [sub, AddSubgroup.mem_comap, LinearMap.toAddMonoidHom_coe, Submodule.subtype_apply]
  rw [h i, hx]

theorem mem_eigSp {K V O : Type} [Field K] [AddCommGroup V] [Module K V] [CommRing O]
    (r : O →+* Module.End K V) (σ : O →+* K) (v : V) :
    v ∈ eigSp r σ ↔ ∀ a, r a v = σ a • v := by
  simp [eigSp, Submodule.mem_iInf, sub_eq_zero]

theorem mem_eig {K V O : Type} [Field K] [AddCommGroup V] [Module K V]
    (ρ : O → V →ₗ[K] V) (χ : O → K) (v : V) :
    v ∈ eig ρ χ ↔ ∀ a, ρ a v = χ a • v := by
  simp [eig, Submodule.mem_iInf, sub_eq_zero]

theorem map_eigSp {K V O : Type} [Field K] [AddCommGroup V] [Module K V] [CommRing O] {d : ℕ}
    (r : O →+* Module.End K V) (ρ : O →+* Matrix (Fin d) (Fin d) K) (σ : O →+* K)
    (e : V ≃ₗ[K] (Fin d → K)) (h : ∀ a v, e (r a v) = (ρ a).mulVec (e v)) :
    (eigSp r σ).map (e : V →ₗ[K] (Fin d → K)) = eig (fun a => Matrix.toLin' (ρ a)) (fun a => σ a) := by
  ext y
  obtain ⟨v, rfl⟩ := e.surjective y
  have h1 : e v ∈ (eigSp r σ).map (e : V →ₗ[K] (Fin d → K)) ↔ v ∈ eigSp r σ := by
    constructor
    · rintro ⟨u, hu, huv⟩
      have : u = v := e.injective huv
      exact this ▸ hu
    · exact fun hv => ⟨v, hv, rfl⟩
  rw [h1, mem_eigSp, mem_eig]
  refine forall_congr' fun a => ?_
  rw [Matrix.toLin'_apply, ← h, ← map_smul]
  exact e.injective.eq_iff.symm

theorem m2Curve_holds : CurveSemiAbelianConjecture := by
  intro E _ _ _ H X0 t hpow k K _ _ _ p _ _ hp C z Y hne hk hfib V _ _ _ M r hact T _ χ hsplit hχ
    j q w W L hj hq hW0 hL0 hWj hLq hgap
  letI := H.starRing
  obtain ⟨d, D, e, hlie, her⟩ := GlobalTheory.T.curve_lie_eigen_degree E H (fun _ => rfl) X0 t hpow K p C z Y hne hfib V M r hact
  let f : V →ₗ[K] (Fin d → K) := e
  have key := GlobalTheory.T.eigen_flag_slope_bound K C p (𝓞 E) k (T ⊕ T) T χ d D Sum.inl Sum.inr j q w
    (fun τ i => (W τ i).map f) (fun τ i => (L τ i).map f) hp hsplit hk
    (by
      have : (Sum.elim Sum.inl Sum.inr : T ⊕ T → T ⊕ T) = id := by ext (x | x) <;> rfl
      rw [this]; exact Function.bijective_id)
    (fun τ a => hχ τ a) hj hq
    (fun τ => by simp [hW0 τ]) (fun τ => by simp [hL0 τ])
    (fun τ => by rw [hWj τ]; exact map_eigSp r D.ρ _ e her)
    (fun τ => by rw [hLq τ]; exact map_eigSp r D.ρ _ e her) hgap
  simpa only [subDeg_map C (Y.lieLat M) D.lie e D.lie_bun hlie, f] using key

end GlobalTheory.CompanionTheory.Ar.Conj.CurveDegreeNonneg
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.M2CurveEstablishedStatement
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.curveSemiAbelianConjecture : CurveSemiAbelianConjecture := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Conj.CurveDegreeNonneg.m2Curve_holds | exact GlobalTheory.CompanionTheory.Ar.Conj.CurveDegreeNonneg.m2Curve_holds | (intros; apply GlobalTheory.CompanionTheory.Ar.Conj.CurveDegreeNonneg.m2Curve_holds <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.M2ModelOfCurveBound
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CurveLieLatticeDegree
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CurveLieLatticeDegree
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.GrDeg

theorem grLine_deg_eq_sub : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Field K] (C : ACurve K) (z : Spec (CommRingCat.of K) ⟶ X) (Y : CurveIn C z) (G : Over X) [GrpObj G] [IsCommMonObj G] (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel G ξ V) (Vz : Type) [AddCommGroup Vz] [Module K Vz] [FiniteDimensional K Vz] (Mz : LieModel G z Vz) (h₀ : genPt ξ ⤳ centre z) (h : ∀ i, genPt ξ ⤳ centre (Y.x i)) (S : Set (Cpt ξ)) (L L' : Lat ξ V) (r r' : ℕ) (b₀ : Fin r → V) (U' : Submodule Ω V), IsCptGen ξ → Smooth G.hom → (⟨centre z, h₀⟩ : Cpt ξ) ∈ S → (∀ i, (⟨centre (Y.x i), h i⟩ : Cpt ξ) ∈ S) → LinearIndependent Ω b₀ → L.IsFlagVBOn S b₀ → L'.IsVBOn S r' U' → IsCompl (Submodule.span Ω (Set.range b₀)) U' → (∀ q ∈ S, M.lat q = L q ⊔ L' q) → ∃ W : ℕ → Submodule K Vz, W 0 = ⊥ ∧ W r = Submodule.span K {v | ∃ e ∈ L ⟨centre z, h₀⟩, M.ValAt z e (Mz.pt v)} ∧ ∀ s : Fin r, Y.IsDeg (L.gr b₀ s) (subDeg C (Y.lieLat Mz) (W (s + 1)) - subDeg C (Y.lieLat Mz) (W s)) :=
  PositivityTheory.HtPt.Ci.gr_deg

end GlobalTheory.CompanionTheory.Ar.GrDeg
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CurveLieLatticeDegreeStatement
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.curve_lie_lattice_degree : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Field K] (C : ACurve K) (z : Spec (CommRingCat.of K) ⟶ X) (Y : CurveIn C z) (G : Over X) [GrpObj G] [IsCommMonObj G] (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel G ξ V) (Vz : Type) [AddCommGroup Vz] [Module K Vz] [FiniteDimensional K Vz] (Mz : LieModel G z Vz) (h₀ : genPt ξ ⤳ centre z) (h : ∀ i, genPt ξ ⤳ centre (Y.x i)) (S : Set (Cpt ξ)) (L L' : Lat ξ V) (r r' : ℕ) (b₀ : Fin r → V) (U' : Submodule Ω V), IsCptGen ξ → Smooth G.hom → (⟨centre z, h₀⟩ : Cpt ξ) ∈ S → (∀ i, (⟨centre (Y.x i), h i⟩ : Cpt ξ) ∈ S) → LinearIndependent Ω b₀ → L.IsFlagVBOn S b₀ → L'.IsVBOn S r' U' → IsCompl (Submodule.span Ω (Set.range b₀)) U' → (∀ q ∈ S, M.lat q = L q ⊔ L' q) → ∃ W : ℕ → Submodule K Vz, W 0 = ⊥ ∧ W r = Submodule.span K {v | ∃ e ∈ L ⟨centre z, h₀⟩, M.ValAt z e (Mz.pt v)} ∧ ∀ s : Fin r, Y.IsDeg (L.gr b₀ s) (subDeg C (Y.lieLat Mz) (W (s + 1)) - subDeg C (Y.lieLat Mz) (W s)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GrDeg.grLine_deg_eq_sub | exact GlobalTheory.CompanionTheory.Ar.GrDeg.grLine_deg_eq_sub | (intros; apply GlobalTheory.CompanionTheory.Ar.GrDeg.grLine_deg_eq_sub <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CurveLieEigenDecomposition
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CurveLieEigenDecomposition
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.EigVal

theorem values_eigen_sheaves : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (k K : Type) [Field k] [Field K] [Algebra k K] (z : Spec (CommRingCat.of K) ⟶ X) (G : Over X) [GrpObj G] [IsCommMonObj G] (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel G ξ V) (Vz : Type) [AddCommGroup Vz] [Module K Vz] (Mz : LieModel G z Vz) (h₀ : genPt ξ ⤳ centre z) (O S : Type) [CommRing O] [Fintype S] (act : O → (G ⟶ G)) (r : O →+* Module.End Ω V) (rz : O →+* Module.End K Vz) (σ : S → (O →+* Ω)) (χ : S → (O →+* k)), IsCptGen ξ → Smooth G.hom → (∀ a, IsMonHom (act a)) → M.IsActOf act r → Mz.IsActOf act rz → IsSplit χ → (∀ s a, ValAt ξ z (σ s a) (algebraMap k K (χ s a))) → M.lat ⟨centre z, h₀⟩ = ⨆ s, M.eigLat r (σ s) ⟨centre z, h₀⟩ → ∀ s, Submodule.span K {v | ∃ e ∈ M.eigLat r (σ s) ⟨centre z, h₀⟩, M.ValAt z e (Mz.pt v)} = eigSp rz ((algebraMap k K).comp (χ s)) :=
  @PositivityTheory.HtPt.Ci.eig_val

end GlobalTheory.CompanionTheory.Ar.EigVal
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CurveLieEigenDecompositionStatement
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.curve_lie_eigen_decomposition : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (k K : Type) [Field k] [Field K] [Algebra k K] (z : Spec (CommRingCat.of K) ⟶ X) (G : Over X) [GrpObj G] [IsCommMonObj G] (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel G ξ V) (Vz : Type) [AddCommGroup Vz] [Module K Vz] (Mz : LieModel G z Vz) (h₀ : genPt ξ ⤳ centre z) (O S : Type) [CommRing O] [Fintype S] (act : O → (G ⟶ G)) (r : O →+* Module.End Ω V) (rz : O →+* Module.End K Vz) (σ : S → (O →+* Ω)) (χ : S → (O →+* k)), IsCptGen ξ → Smooth G.hom → (∀ a, IsMonHom (act a)) → M.IsActOf act r → Mz.IsActOf act rz → IsSplit χ → (∀ s a, ValAt ξ z (σ s a) (algebraMap k K (χ s a))) → M.lat ⟨centre z, h₀⟩ = ⨆ s, M.eigLat r (σ s) ⟨centre z, h₀⟩ → ∀ s, Submodule.span K {v | ∃ e ∈ M.eigLat r (σ s) ⟨centre z, h₀⟩, M.ValAt z e (Mz.pt v)} = eigSp rz ((algebraMap k K).comp (χ s)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.EigVal.values_eigen_sheaves | exact GlobalTheory.CompanionTheory.Ar.EigVal.values_eigen_sheaves | (intros; apply GlobalTheory.CompanionTheory.Ar.EigVal.values_eigen_sheaves <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CurveDegreeUnique
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CurveDegreeUnique
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.Crv

theorem curveIn_isDeg_unique_of_isCptGen : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Field K] (C : ACurve K) (z : Spec (CommRingCat.of K) ⟶ X) (Y : CurveIn C z) (Λ : Lat ξ Ω) (n n' : ℤ), IsCptGen ξ → Y.IsDeg Λ n → Y.IsDeg Λ n' → n = n' :=
  @PositivityTheory.HtPt.Ch.isdeg_unique

end GlobalTheory.CompanionTheory.Ar.Crv
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CurveDegreeUniqueStatement
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.curve_degree_unique : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Field K] (C : ACurve K) (z : Spec (CommRingCat.of K) ⟶ X) (Y : CurveIn C z) (Λ : Lat ξ Ω) (n n' : ℤ), IsCptGen ξ → Y.IsDeg Λ n → Y.IsDeg Λ n' → n = n' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Crv.curveIn_isDeg_unique_of_isCptGen | exact GlobalTheory.CompanionTheory.Ar.Crv.curveIn_isDeg_unique_of_isCptGen | (intros; apply GlobalTheory.CompanionTheory.Ar.Crv.curveIn_isDeg_unique_of_isCptGen <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CurveLatticeDegreeFormula
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CurveLatticeDegreeFormula
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.Crv

theorem isDeg_coordDeg : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Field K] (C : ACurve K) (z : Spec (CommRingCat.of K) ⟶ X) (Y : CurveIn C z) (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (w : (Σ k, J k) → K) (Λ : Lat ξ Ω) (S : Set (Cpt ξ)) (a : B → ℤ) (e₀ : Ω) (h₀ : genPt ξ ⤳ centre z) (h : ∀ i, genPt ξ ⤳ centre (Y.x i)), CoordTie ℤ ξ (segre y) → CoordsAt ξ y z w → (⟨centre z, h₀⟩ : Cpt ξ) ∈ S → (∀ i, (⟨centre (Y.x i), h i⟩ : Cpt ξ) ∈ S) → Λ.IsDegOn S y a e₀ → Y.IsDeg Λ (coordDeg C w a) :=
  PositivityTheory.HtPt.Ci.isdeg_coord

end GlobalTheory.CompanionTheory.Ar.Crv
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CurveLatticeDegreeFormulaStatement
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.curve_lattice_degree_formula : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Field K] (C : ACurve K) (z : Spec (CommRingCat.of K) ⟶ X) (Y : CurveIn C z) (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (w : (Σ k, J k) → K) (Λ : Lat ξ Ω) (S : Set (Cpt ξ)) (a : B → ℤ) (e₀ : Ω) (h₀ : genPt ξ ⤳ centre z) (h : ∀ i, genPt ξ ⤳ centre (Y.x i)), CoordTie ℤ ξ (segre y) → CoordsAt ξ y z w → (⟨centre z, h₀⟩ : Cpt ξ) ∈ S → (∀ i, (⟨centre (Y.x i), h i⟩ : Cpt ξ) ∈ S) → Λ.IsDegOn S y a e₀ → Y.IsDeg Λ (coordDeg C w a) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Crv.isDeg_coordDeg | exact GlobalTheory.CompanionTheory.Ar.Crv.isDeg_coordDeg | (intros; apply GlobalTheory.CompanionTheory.Ar.Crv.isDeg_coordDeg <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CurveThroughCoordinates
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CurveThroughCoordinates
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.curve_through_coordinates : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω), CoordTie ℤ ξ (segre y) → ∀ (K : Type) [Field K] (C : ACurve K) (w : (Σ k, J k) → K), mCoordIdeal y ≤ mCoordIdeal w → (∀ k, ∃ c, w ⟨k, c⟩ ≠ 0) → ∃ (z : Spec (CommRingCat.of K) ⟶ X) (Y : CurveIn C z) (h₀ : genPt ξ ⤳ centre z) (h : ∀ i, genPt ξ ⤳ centre (Y.x i)), CoordsAt ξ y z w ∧ ∀ p : ℕ, (p : K) = 0 → InFibre ξ p ⟨centre z, h₀⟩ ∧ ∀ i, InFibre ξ p ⟨centre (Y.x i), h i⟩ := by
  first | exact @PositivityTheory.HtPt.Ci.curve_in_cpt | exact PositivityTheory.HtPt.Ci.curve_in_cpt
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CurveThroughCoordinatesStatement
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.curve_through_coordinates : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω), CoordTie ℤ ξ (segre y) → ∀ (K : Type) [Field K] (C : ACurve K) (w : (Σ k, J k) → K), mCoordIdeal y ≤ mCoordIdeal w → (∀ k, ∃ c, w ⟨k, c⟩ ≠ 0) → ∃ (z : Spec (CommRingCat.of K) ⟶ X) (Y : CurveIn C z) (h₀ : genPt ξ ⤳ centre z) (h : ∀ i, genPt ξ ⤳ centre (Y.x i)), CoordsAt ξ y z w ∧ ∀ p : ℕ, (p : K) = 0 → InFibre ξ p ⟨centre z, h₀⟩ ∧ ∀ i, InFibre ξ p ⟨centre (Y.x i), h i⟩ := by
  first | exact @GlobalTheory.CompanionTheory.Relay.curve_through_coordinates | exact GlobalTheory.CompanionTheory.Relay.curve_through_coordinates | (intros; apply GlobalTheory.CompanionTheory.Relay.curve_through_coordinates <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FunctionFieldModelExists
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FunctionFieldModelExists
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.Crv.Field

theorem curve_field : ∀ (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (W : Ideal (MRing J)) (p : ℕ) [Fact p.Prime], IsMultiProjPrime W → charOf W = p → ringKrullDim (MRing J ⧸ W) = ((1 + Fintype.card B : ℕ) : WithBot ℕ∞) → ∃ (K : Type) (_ : Field K) (_ : Algebra (ZMod p) K) (_ : GroundTheory.FunctionField.IsFunctionField (ZMod p) K) (w : (Σ k, J k) → K), mCoordIdeal w = W ∧ Birational w ∧ ∀ k, ∃ c, w ⟨k, c⟩ ≠ 0 :=
  PositivityTheory.HtPt.Ci.curve_field

end GlobalTheory.CompanionTheory.Ar.Crv.Field
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FunctionFieldModelExistsStatement
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.function_field_model_exists : ∀ (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (W : Ideal (MRing J)) (p : ℕ) [Fact p.Prime], IsMultiProjPrime W → charOf W = p → ringKrullDim (MRing J ⧸ W) = ((1 + Fintype.card B : ℕ) : WithBot ℕ∞) → ∃ (K : Type) (_ : Field K) (_ : Algebra (ZMod p) K) (_ : GroundTheory.FunctionField.IsFunctionField (ZMod p) K) (w : (Σ k, J k) → K), mCoordIdeal w = W ∧ Birational w ∧ ∀ k, ∃ c, w ⟨k, c⟩ ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Crv.Field.curve_field | exact GlobalTheory.CompanionTheory.Ar.Crv.Field.curve_field | (intros; apply GlobalTheory.CompanionTheory.Ar.Crv.Field.curve_field <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.M2ModelOfCurveBound
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Conj.ModelNefness

theorem iSup_split {α I : Type} [CompleteLattice α] (f : I → α) (s₀ : I) :
    ⨆ s, f s = f s₀ ⊔ ⨆ s : {s // s ≠ s₀}, f s := by
  apply le_antisymm
  · refine iSup_le fun s => ?_
    by_cases h : s = s₀
    · subst h; exact le_sup_left
    · exact le_sup_of_le_right (le_iSup (fun s : {s // s ≠ s₀} => f s) ⟨s, h⟩)
  · exact sup_le (le_iSup f s₀) (iSup_le fun s => le_iSup f s.1)

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem isVBOn_iSup {E : Type} [AddCommGroup E] [Module Ω E] {I : Type} [Fintype I]
    (L : I → Lat ξ E) (T : Set (Cpt ξ)) (r : I → ℕ) (V : I → Submodule Ω E) (hV : iSupIndep V)
    (hL : ∀ s, (L s).IsVBOn T (r s) (V s)) :
    Lat.IsVBOn (ξ := ξ) (fun q => ⨆ s, L s q) T (∑ s, r s) (⨆ s, V s) := by
  classical
  intro p hp
  choose U hU b hb hfr using fun s => hL s p hp
  have hmem : ∀ (x : X) (s : Finset I), x ∈ s.inf U ↔ ∀ i ∈ s, x ∈ U i := by
    intro x s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => simp [Finset.inf_insert, ih]
  let e : (Σ s, Fin (r s)) ≃ Fin (∑ s, r s) := Fintype.equivFinOfCardEq (by simp [Fintype.card_sigma])
  let c : Fin (∑ s, r s) → E := fun i => b (e.symm i).1 (e.symm i).2
  have hsp : ∀ (A : Type) [Semiring A] [Module A E],
      Submodule.span A (Set.range c) = ⨆ s, Submodule.span A (Set.range (b s)) := by
    intro A _ _
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact (le_iSup (fun s => Submodule.span A (Set.range (b s))) (e.symm i).1)
        (Submodule.subset_span ⟨_, rfl⟩)
    · refine iSup_le fun s => ?_
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨e ⟨s, i⟩, congrArg (fun x : Σ s, Fin (r s) => b x.1 x.2) (e.symm_apply_apply ⟨s, i⟩)⟩
  have hli : LinearIndependent Ω c := by
    have h1 : LinearIndependent Ω fun ji : Σ s, Fin (r s) => b ji.1 ji.2 := by
      refine linearIndependent_iUnion_finite (fun s => (hfr s p hp (hU s)).1) fun i t _ hi => ?_
      rw [hb i]
      refine (hV i).mono_right (iSup₂_le fun s hs => ?_)
      rw [hb s]
      exact le_iSup₂_of_le s (fun h => hi (h ▸ hs)) le_rfl
    exact h1.comp e.symm e.symm.injective
  refine ⟨Finset.univ.inf U, (hmem _ _).2 fun s _ => hU s, c, ?_, fun q hq hqU => ⟨hli, ?_⟩⟩
  · rw [hsp Ω]
    exact iSup_congr hb
  · rw [hsp (regAt ξ q)]
    exact iSup_congr fun s => (hfr s q hq ((hmem _ _).1 hqU s (Finset.mem_univ s))).2

theorem unitAt_of_isUnit {q : Cpt ξ} {a : regAt ξ q} (h : IsUnit a) : unitAt ξ q (a : Ω) := by
  obtain ⟨u, rfl⟩ := h
  refine ⟨fun h0 => u.ne_zero (Subtype.ext h0), u.1.2, ?_⟩
  have : ((u : regAt ξ q) : Ω)⁻¹ = (((u⁻¹ : (regAt ξ q)ˣ) : regAt ξ q) : Ω) := by
    exact inv_eq_of_mul_eq_one_right (congrArg Subtype.val u.mul_inv)
  rw [this]
  exact (((u⁻¹ : (regAt ξ q)ˣ) : regAt ξ q)).2

theorem unitAt_int_of_fibre [CharZero Ω] {p : ℕ} (hp : p.Prime) (q : Cpt ξ) (hq : InFibre ξ p q) {d : ℤ}
    (hd : ¬ (p : ℤ) ∣ d) : unitAt ξ q (d : Ω) := by
  haveI := EigSplit.isLocalRing_regAt q
  obtain ⟨a, b, hab⟩ := ((Nat.prime_iff_prime_int.1 hp).coprime_iff_not_dvd).2 hd
  have hP : ¬ IsUnit ((p : ℕ) : regAt ξ q) := fun h => hq (by simpa using unitAt_of_isUnit h)
  have h1 : ((a : regAt ξ q) * (p : regAt ξ q)) + (b : regAt ξ q) * (d : regAt ξ q) = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → regAt ξ q) hab
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one h1 with h | h
  · exact absurd (isUnit_of_mul_isUnit_right h) hP
  · have e : ((d : regAt ξ q) : Ω) = (d : Ω) := map_intCast (regAt ξ q).subtype d
    rw [← e]
    exact unitAt_of_isUnit (isUnit_of_mul_isUnit_right (x := (b : regAt ξ q)) (by rwa [mul_comm] at h ⊢))

theorem charZero_of_isArithVar {B : Type} [Fintype B] {ι : B → Type} [∀ k, Fintype (ι k)] {y : (Σ k, ι k) → Ω} {d : ℕ}
    (h : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) d) : CharZero Ω := by
  obtain ⟨-, -, hh, -⟩ := h
  refine charZero_of_inj_zero fun n hn => ?_
  have h1 : (n : ℤ) ∈ (mCoordIdeal y).comap (MvPolynomial.C : ℤ →+* MRing ι) := by
    rw [Ideal.mem_comap, mCoordIdeal, RingHom.mem_ker]
    have : mConeMap y (MvPolynomial.C (n : ℤ)) = MvPolynomial.C (n : Ω) := by
      simpa using (mConeMap y).commutes (n : ℤ)
    simpa [hn] using this
  rw [show (mCoordIdeal y).comap (MvPolynomial.C : ℤ →+* MRing ι) = ⊥ from hh] at h1
  simpa using h1


open Module in
theorem flag_at (E : Type) [Field E] [NumberField E] [CharZero Ω] (hg : IsCptGen ξ)
    {K k : Type} [Field K] [Field k] [Algebra k K] (C : ACurve K) (z : Spec (CommRingCat.of K) ⟶ X) (Y : CurveIn C z)
    (G : Over X) [GrpObj G] [IsCommMonObj G] (hsm : Smooth G.hom) (act : OAct (𝓞 E) G)
    (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel G ξ V)
    (Vz : Type) [AddCommGroup Vz] [Module K Vz] [FiniteDimensional K Vz] (Mz : LieModel G z Vz)
    (r : 𝓞 E →+* Module.End Ω V) (rz : 𝓞 E →+* Module.End K Vz) (hr : M.IsActOf act.act r)
    (hrz : Mz.IsActOf act.act rz) (I : Type) [Fintype I] (σ : I → (𝓞 E →+* Ω)) (χ : I → (𝓞 E →+* k))
    (hσ : Function.Injective σ) (hcard : Fintype.card I = finrank ℚ E) (hχ : IsSplit χ)
    (h₀ : genPt ξ ⤳ centre z) (h : ∀ i, genPt ξ ⤳ centre (Y.x i)) (S : Set (Cpt ξ))
    (hz : (⟨centre z, h₀⟩ : Cpt ξ) ∈ S) (hS : ∀ i, (⟨centre (Y.x i), h i⟩ : Cpt ξ) ∈ S)
    (hreg : ∀ q ∈ S, ∀ s a, σ s a ∈ regAt ξ q) (hdisc : ∀ q ∈ S, unitAt ξ q ((discr E : ℤ) : Ω))
    (hval : ∀ s a, ValAt ξ z (σ s a) (algebraMap k K (χ s a)))
    (s₀ : I) {n : ℕ} (b : Fin n → V) (hb : LinearIndependent Ω b)
    (hspan : Submodule.span Ω (Set.range b) = eigSp r (σ s₀)) (hfl : (M.eigLat r (σ s₀)).IsFlagVBOn S b) :
    ∃ W : ℕ → Submodule K Vz, W 0 = ⊥ ∧ W n = eigSp rz ((algebraMap k K).comp (χ s₀)) ∧
      ∀ s : Fin n, Y.IsDeg ((M.eigLat r (σ s₀)).gr b s)
        (subDeg C (Y.lieLat Mz) (W (s + 1)) - subDeg C (Y.lieLat Mz) (W s)) := by
  classical
  have hvb : M.lat.IsVBOn S (finrank Ω V) ⊤ := fun p _ => by
    obtain ⟨U, hU, c, hc, hf⟩ := (GlobalTheory.T.lie_omega_lattice_vector_bundle X Ω ξ G V M hg hsm).1 p trivial
    exact ⟨U, hU, c, hc, fun q _ hq => hf q trivial hq⟩
  obtain ⟨hE, hsum⟩ := EigSplit.isVBOn_eigSp X Ω ξ V E r M.lat S _ I σ hg hσ hcard hvb
    (fun p _ a e he => LieStable.lat_stable X Ω ξ G V M _ act r hr p a e he) hreg hdisc
  have hint := GlobalTheory.T.eigenspace_decomposition_internal Ω V E r I σ hσ hcard
  have hind := hint.submodule_iSupIndep
  let U' : Submodule Ω V := ⨆ s : {s // s ≠ s₀}, eigSp r (σ s)
  let L' : Lat ξ V := fun q => ⨆ s : {s // s ≠ s₀}, M.eigLat r (σ s) q
  have hL' : L'.IsVBOn S (∑ s : {s // s ≠ s₀}, finrank Ω (eigSp r (σ s))) U' :=
    isVBOn_iSup (fun s : {s // s ≠ s₀} => M.eigLat r (σ s)) S _ (fun s => eigSp r (σ s))
      (hind.comp Subtype.val_injective) fun s => hE s
  have hcompl : IsCompl (Submodule.span Ω (Set.range b)) U' := by
    rw [hspan]
    refine ⟨(hind s₀).mono_right (iSup_le fun s => le_iSup₂_of_le s.1 s.2 le_rfl), ?_⟩
    rw [codisjoint_iff, ← iSup_split (fun s => eigSp r (σ s)) s₀]
    exact hint.submodule_iSup_eq_top
  have hlat : ∀ q ∈ S, M.lat q = M.eigLat r (σ s₀) q ⊔ L' q := fun q hq =>
    (hsum q hq).trans (iSup_split (fun s => M.eigLat r (σ s) q) s₀)
  obtain ⟨W, hW0, hWn, hdeg⟩ := GlobalTheory.T.curve_lie_lattice_degree X Ω ξ K C z Y G V M Vz Mz h₀ h S (M.eigLat r (σ s₀)) L' n _ b U'
    hg hsm hz hS hb hfl hL' hcompl hlat
  refine ⟨W, hW0, ?_, hdeg⟩
  rw [hWn]
  exact GlobalTheory.T.curve_lie_eigen_decomposition X Ω ξ k K z G V M Vz Mz h₀ (𝓞 E) I act.act r rz σ χ hg hsm act.hom hr hrz hχ hval
    (hsum _ hz) s₀

end GlobalTheory.CompanionTheory.Ar.Conj.ModelNefness

namespace GlobalTheory.CompanionTheory.Ar.Conj


open ModelNefness GlobalTheory.CompanionTheory.Ar.Top in
theorem m2Model_of_m2Curve : CurveSemiAbelianConjecture → RootLineDeRhamModel := by
  intro hC Ψ _ N M j p E _ _ _ H D hp hp2 hj hjN mu hdom hthr Wi hW
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hprime, hPW, hchar, hdim⟩ := hW
  haveI : CharZero M.Ω := charZero_of_isArithVar M.arith
  obtain ⟨K, _, _, _, w, hwW, hbir, hwk⟩ := GlobalTheory.T.function_field_model_exists M.K M.ι Wi p hprime hchar hdim
  obtain ⟨C, hFF, hne, hv⟩ := GlobalTheory.T.function_field_curve_exists (ZMod p) K
  haveI : CharP K p := charP_of_injective_algebraMap (algebraMap (ZMod p) K).injective p
  obtain ⟨z, Y, h₀, h, hco, hfib⟩ := GlobalTheory.T.curve_through_coordinates D.X M.Ω D.ξ M.K M.ι M.y D.tie K C w
    (by rw [hwW]; exact hPW) hwk
  obtain ⟨hz, hi⟩ := hfib p (CharP.cast_eq_zero K p)
  have hg : IsCptGen D.ξ := D.tie.gen
  obtain ⟨φ, hφ, -⟩ := ValHom.exists_valAt_hom D.X M.Ω D.ξ K z h₀ hg
  let σ' : Ψ ⊕ Ψ → (𝓞 E →+* regAt D.ξ ⟨centre z, h₀⟩) := fun s => (D.σ s).codRestrict _ (D.reg _ hz s)
  have hσ' : Function.Injective σ' := fun s s' e => D.σ_inj (RingHom.ext fun a =>
    congrArg Subtype.val (RingHom.congr_fun e a))
  have hcard : Fintype.card (Ψ ⊕ Ψ) = Module.finrank ℚ E := by
    rw [Fintype.card_sum, ← D.card]; ring
  obtain ⟨χ, hχ, hχv⟩ := GlobalTheory.T.split_characters_unramified E (regAt D.ξ ⟨centre z, h₀⟩) K (Ψ ⊕ Ψ) p σ' φ hσ' hcard D.unram
  have hval : ∀ s a, ValAt D.ξ z (D.σ s a) (algebraMap (algebraicClosure (ZMod p) K) K (χ s a)) := fun s a =>
    (hφ _ _).2 ⟨D.reg _ hz s a, (hχv s a).symm⟩
  have hconj : ∀ τ a, χ (Sum.inr τ) a = χ (Sum.inl τ) (H.bar a) := fun τ a => Subtype.ext (by
    rw [hχv, hχv]
    exact congrArg φ (Subtype.ext (D.conj τ a)))
  have hconst : ∀ i (c : algebraicClosure (ZMod p) K), C.v i (algebraMap _ K c) ≤ 1 := fun i c =>
    hv i _ (mem_algebraicClosure_iff.1 c.2)
  obtain ⟨Vz, _, _, ⟨Mz⟩⟩ := lieModel_exists D.X D.t.G K z
  haveI : Smooth D.t.G.hom := D.t.semi.smooth
  haveI : FiniteDimensional K Vz := (GlobalTheory.T.lie_model_finite_projective D.X D.t.G K z Vz Mz).1
  obtain ⟨rz, hrz, -⟩ := lieModel_exists_unique_act D.X D.t.G K z Vz Mz (𝓞 E) D.t.act.act D.t.act.hom
    D.t.act.one D.t.act.mul D.t.act.add
  have hreg : ∀ q ∈ {q | InFibre D.ξ p q}, ∀ s a, D.σ s a ∈ regAt D.ξ q := fun q hq s a => D.reg q hq s a
  have hdisc : ∀ q ∈ {q | InFibre D.ξ p q}, unitAt D.ξ q ((NumberField.discr E : ℤ) : M.Ω) := fun q hq =>
    unitAt_int_of_fibre hp q hq D.unram
  choose Wf hW0 hWj hdegW using fun τ => flag_at E hg C z Y D.t.G D.t.semi.smooth D.t.act D.V D.L Vz Mz D.r rz
    D.act hrz (Ψ ⊕ Ψ) D.σ χ D.σ_inj hcard hχ h₀ h {q | InFibre D.ξ p q} hz hi hreg hdisc hval (Sum.inl τ)
    (D.b₁ τ) (D.ind₁ τ).1 (D.ind₁ τ).2 (D.flag₁ τ)
  choose Lf hL0 hLq hdegL using fun τ => flag_at E hg C z Y D.t.G D.t.semi.smooth D.t.act D.V D.L Vz Mz D.r rz
    D.act hrz (Ψ ⊕ Ψ) D.σ χ D.σ_inj hcard hχ h₀ h {q | InFibre D.ξ p q} hz hi hreg hdisc hval (Sum.inr τ)
    (D.b₂ τ) (D.ind₂ τ).1 (D.ind₂ τ).2 (D.flag₂ τ)
  have hxdeg : ∀ r, geoNum 1 Wi (fun _ => M.xdeg r) = coordDeg C w (M.xdeg r) := fun r => by
    rw [← hwW]
    exact GlobalTheory.T.function_field_degree_eq M.K M.ι p K C w (M.xdeg r) hFF hbir hwk
  let x : Ψ × Fin N → ℝ := fun r => (geoNum 1 Wi (fun _ => M.xdeg r) : ℝ)
  let wd : Ψ → ℕ → ℝ := fun τ i => (subDeg C (Y.lieLat Mz) (Wf τ i) : ℝ)
  let ld : Ψ → ℕ → ℝ := fun τ i => (subDeg C (Y.lieLat Mz) (Lf τ i) : ℝ)
  have hx1 : ∀ τ (i : Fin N), (i : ℕ) < j → x (τ, i) = wd τ (i + 1) - wd τ i := by
    intro τ i hij
    obtain ⟨e₀, hdo⟩ := D.deg₁ τ i hij
    have h1 := GlobalTheory.T.curve_lattice_degree_formula D.X M.Ω D.ξ K C z Y M.K M.ι M.y w _ {q | InFibre D.ξ p q} _ e₀ h₀ h D.tie hco hz hi hdo
    have h2 := GlobalTheory.T.curve_degree_unique D.X M.Ω D.ξ K C z Y _ _ _ hg h1 (hdegW τ ⟨i, hij⟩)
    simp only [x, wd, hxdeg, h2]
    push_cast
    rfl
  have hx2 : ∀ τ (i : Fin N), j ≤ (i : ℕ) → x (τ, i) = -(ld τ (N - 1 - i + 1) - ld τ (N - 1 - i)) := by
    intro τ i hij
    have hlt : N - 1 - (i : ℕ) < N - j := by have := i.2; omega
    obtain ⟨e₀, hdo⟩ := D.deg₂ τ i hlt hij
    have h1 := GlobalTheory.T.curve_lattice_degree_formula D.X M.Ω D.ξ K C z Y M.K M.ι M.y w _ {q | InFibre D.ξ p q} _ e₀ h₀ h D.tie hco hz hi hdo
    have h2 := GlobalTheory.T.curve_degree_unique D.X M.Ω D.ξ K C z Y _ _ _ hg h1 (hdegL τ ⟨N - 1 - i, hlt⟩)
    have h3 : coordDeg C w (-M.xdeg (τ, i)) = -coordDeg C w (M.xdeg (τ, i)) := by
      simp [coordDeg]
    rw [h3] at h2
    have h4 : coordDeg C w (M.xdeg (τ, i)) = -(subDeg C (Y.lieLat Mz) (Lf τ (N - 1 - i + 1)) -
        subDeg C (Y.lieLat Mz) (Lf τ (N - 1 - i))) := by
      rw [← neg_eq_iff_eq_neg]; exact h2
    simp only [x, ld, hxdeg, h4]
    push_cast
    rfl
  obtain ⟨hgap, heq⟩ := GlobalTheory.T.nef_threshold_gap_condition Ψ N j p mu x wd ld hp2 hj hjN hdom hthr hx1 hx2
  have hfin := hC E H D.X D.t D.pow (algebraicClosure (ZMod p) K) K p hp2 C z Y hne hconst
    (fun i => D.fib ⟨_, h i⟩ (hi i)) Vz Mz rz hrz Ψ χ hχ hconj j (N - j) _ Wf Lf hj (by omega) hW0 hL0 hWj hLq hgap
  have hfin' : 0 ≤ ∑ r : Ψ × Fin N, -mu r.1 r.2 * x r := heq ▸ hfin
  have hcd : M.curveDeg mu 0 Wi = ∑ r : Ψ × Fin N, -mu r.1 r.2 * x r := by
    unfold RootModel.curveDeg
    rw [Fintype.sum_option]
    simp only [RootModel.coef, RootModel.line, M.x_deg, zero_div, zero_mul, zero_add, x]
  rw [hcd]
  exact hfin'

end GlobalTheory.CompanionTheory.Ar.Conj
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.M2ModelOfCurveBoundStatement
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rootLineDeRhamModel_of_curveSemiAbelian : CurveSemiAbelianConjecture → RootLineDeRhamModel := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Conj.m2Model_of_m2Curve | exact GlobalTheory.CompanionTheory.Ar.Conj.m2Model_of_m2Curve | (intros; apply GlobalTheory.CompanionTheory.Ar.Conj.m2Model_of_m2Curve <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.M2ModelEstablished
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.Conj

theorem m2Model_holds : RootLineDeRhamModel := GlobalTheory.T.rootLineDeRhamModel_of_curveSemiAbelian GlobalTheory.T.curveSemiAbelianConjecture

end GlobalTheory.CompanionTheory.Ar.Conj
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.M2ModelEstablishedStatement
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rootLineDeRhamModel_holds : RootLineDeRhamModel := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Conj.m2Model_holds | exact GlobalTheory.CompanionTheory.Ar.Conj.m2Model_holds | (intros; apply GlobalTheory.CompanionTheory.Ar.Conj.m2Model_holds <;> assumption)
end
