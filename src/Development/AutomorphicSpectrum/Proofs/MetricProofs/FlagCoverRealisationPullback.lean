module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentSwapSquareSystem
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.AlgebraicSquareBaseIntersection
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.WCoZero
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.MapAevalInt
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.MapsToTwoFlagFramesOrthogonalOfIsometry
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.LognormOrbit

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PluriharmonicCharts.XCSqsys
section -- merged from Development.WeilBound.CoreStatements.PluriharmonicCharts.XCWSec
section -- merged from Development.WeilBound.CoreStatements.PluriharmonicCharts.IsMultiHomogMonoX
open MvPolynomial Matrix ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Classical

noncomputable section

set_option linter.unusedSectionVars false

namespace PositivityTheory.Xgp.W

local instance (priority := 2000) intAlg5 {Φ : Type} [Field Φ] : Algebra ℤ (RatFunc Φ) := Ring.toIntAlgebra _

open GlobalTheory.CompanionTheory.Ar.PB.CovGraph.GenIdeal GlobalTheory.CompanionTheory.Ar.PB.WSq

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {L : Type} [Field L]

open GroundTheory.Heights₂.Heights.Inter

theorem div_eq_of_local {P Δ : Ideal (MRing ι)} (hPp : P.IsPrime) (hΔp : Δ.IsPrime) (hrel : IsRelevant Δ)
    (hPΔ : P ≤ Δ) {g h : MRing ι} (hgP : g ∉ P) (hhΔ : h ∉ Δ) (hgΔ : g ∈ Δ)
    (hsat : ∀ d ∈ Δ, ∃ u ∉ Δ, u * d ∈ P ⊔ Ideal.span {g})
    (key : ∀ W : Ideal (MRing ι), W.IsPrime → IsRelevant W → P ≤ W → ¬ Δ ≤ W →
      ∃ u v, u ∉ W ∧ v ∉ W ∧ u * g - v * h ∈ P) :
    divCycle P g = divCycle P h + Finsupp.single Δ 1 := by
  have hP : h ∉ P := fun hh => hhΔ (hPΔ hh)
  have hone : multAt (P ⊔ Ideal.span {g}) Δ = 1 := by
    unfold multAt
    rw [dite_eq_left hΔp, DiagonalOrderOne.length_eq_one_of_sat _ Δ
      (sup_le hPΔ ((Ideal.span_singleton_le_iff_mem _).2 hgΔ)) hsat]
    rfl
  have hJΔ : P ⊔ Ideal.span {g * h} ≤ Δ :=
    sup_le hPΔ ((Ideal.span_singleton_le_iff_mem _).mpr (Δ.mul_mem_right h hgΔ))
  have hΔ : Δ ∈ divSupp P (g * h) := by
    refine ⟨⟨⟨hΔp, hJΔ⟩, fun Q hQ hQΔ => ?_⟩, hrel⟩
    by_contra hΔQ
    have hPQ : P ≤ Q := le_sup_left.trans hQ.2
    obtain ⟨u, v, huQ, hvQ, hm⟩ :=
      key Q hQ.1 (fun k => (hrel k).imp fun _ hi hq' => hi (hQΔ hq')) hPQ hΔQ
    have hhQ : h ∉ Q := fun hh' => hhΔ (hQΔ hh')
    have hgQ : g ∈ Q :=
      (hQ.1.mem_or_mem (hQ.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))).resolve_right hhQ
    have hvh : v * h ∈ Q := by
      have e : v * h = u * g - (u * g - v * h) := by ring
      rw [e]
      exact Q.sub_mem (Q.mul_mem_left u hgQ) (hPQ hm)
    rcases hQ.1.mem_or_mem hvh with h1 | h1
    exacts [hvQ h1, hhQ h1]
  apply Finsupp.ext
  intro W
  have hcg := DiagonalDivisor.divCycle_eq_ite (s := g) hP W
  have hch := DiagonalDivisor.divCycle_eq_ite (s := h) hgP W
  rw [mul_comm h g] at hch
  rw [Finsupp.add_apply, hcg, hch, Finsupp.single_apply]
  by_cases hW : W ∈ divSupp P (g * h)
  · rw [if_pos hW, if_pos hW]
    have hWp : W.IsPrime := hW.1.1.1
    by_cases hWΔ : Δ = W
    · rw [if_pos hWΔ, ← hWΔ, hone, DiagonalOrder.multAt_eq_zero_of_not_le hΔp
        (fun hle => hhΔ (hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self h))))]
    · rw [if_neg hWΔ, add_zero]
      have hPW : P ≤ W := le_sup_left.trans hW.1.1.2
      have hΔW : ¬ Δ ≤ W := fun hle => hWΔ (le_antisymm hle (hW.1.2 ⟨hΔp, hJΔ⟩ hle))
      obtain ⟨u, v, hu, hv, hm⟩ := key W hWp hW.2 hPW hΔW
      exact DiagonalOrder.multAt_sup_span_eq hWp hPW hu hv hm
  · rw [if_neg hW, if_neg hW, if_neg (fun h' : Δ = W => hW (h' ▸ hΔ)), add_zero]

theorem exists_point (W : Ideal (MRing ι)) (hW : W.IsPrime) :
    ∃ (E : Type) (_ : Field E) (z : (Σ k, ι k) → E), ∀ f : MRing ι, aeval z f = 0 ↔ f ∈ W := by
  have gen : ∀ (E : Type) [Field E] (ρ : MRing ι →+* E) (f : MRing ι), aeval (fun q => ρ (X q)) f = ρ f := by
    intro E _ ρ f
    have e : (aeval (fun q => ρ (X q)) : MRing ι →ₐ[ℤ] E).toRingHom = ρ :=
      MvPolynomial.ringHom_ext (fun r => by simp) fun p => by simp
    exact RingHom.congr_fun e f
  let E := FractionRing (MRing ι ⧸ W)
  let ρ : MRing ι →+* E := (algebraMap (MRing ι ⧸ W) E).comp (Ideal.Quotient.mk W)
  refine ⟨E, inferInstance, fun q => ρ (X q), fun f => ?_⟩
  rw [gen E ρ f]
  exact (map_eq_zero_iff (algebraMap (MRing ι ⧸ W) E) (IsFractionRing.injective _ _)).trans
    Ideal.Quotient.eq_zero_iff_mem

def monoX (c : ∀ k, ι k) (d : K → ℕ) : MRing ι := ∏ k, X ⟨k, c k⟩ ^ d k

theorem isMultiHomog_monoX (c : ∀ k, ι k) (d : K → ℕ) : IsMultiHomog (monoX c d) d := by
  rw [← Bridge.isMultiHomog_iff]
  have := IsWeightedHomogeneous.prod (w := NumbersDVR.blockWeight ι) Finset.univ
    (fun k => (X ⟨k, c k⟩ : MRing ι) ^ d k) (fun k => d k • NumbersDVR.blockWeight ι ⟨k, c k⟩)
    (fun k _ => (isWeightedHomogeneous_X ℤ _ _).pow (d k))
  have e : ∑ k, d k • NumbersDVR.blockWeight ι ⟨k, c k⟩ = d := by
    funext k
    simp [NumbersDVR.blockWeight, Finset.sum_apply, Pi.single_apply]
  rw [e] at this
  exact this

theorem aeval_monoX (z : (Σ k, ι k) → L) (c : ∀ k, ι k) (d : K → ℕ) :
    aeval z (monoX c d) = ∏ k, z ⟨k, c k⟩ ^ d k := by
  simp [monoX]

theorem aeval_monoX_ne {z : (Σ k, ι k) → L} {c : ∀ k, ι k} (hc : ∀ k, z ⟨k, c k⟩ ≠ 0) (d : K → ℕ) :
    aeval z (monoX c d) ≠ 0 := by
  rw [aeval_monoX]
  exact Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)

theorem chartMono_mul {z : (Σ k, ι k) → L} {c : ∀ k, ι k} (hc : ∀ k, z ⟨k, c k⟩ ≠ 0) {dg dh : K → ℕ} {e : K → ℤ}
    (he : ∀ k, (dg k : ℤ) - dh k = e k) : chartMono z c e * aeval z (monoX c dh) = aeval z (monoX c dg) := by
  rw [aeval_monoX, aeval_monoX, chartMono, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← he, ← zpow_natCast, ← zpow_add₀ (hc k), sub_add_cancel, zpow_natCast]

theorem exists_rel {w : (Σ k, ι k) → Φ} {z : (Σ k, ι k) → L} (hz : IsPt w z) {c : ∀ k, ι k}
    (hc : ∀ k, z ⟨k, c k⟩ ≠ 0) {σ : Φ} {e : K → ℤ} {v : L} (hv : HasVal w z (σ / chartMono w c e) v)
    {g h : MRing ι} {dg dh : K → ℕ} (hg : IsMultiHomog g dg) (hh : IsMultiHomog h dh)
    (he : ∀ k, (dg k : ℤ) - dh k = e k) (hq : aeval w g = σ * aeval w h) :
    ∃ u u' : MRing ι, aeval z u ≠ 0 ∧ aeval z u' = v * chartMono z c e * aeval z u ∧
      u * g - u' * h ∈ mCoordIdeal w := by
  have hcw : ∀ k, w ⟨k, c k⟩ ≠ 0 := fun k => hz.coord_ne (hc k)
  obtain ⟨d, n, m, hn, hm, h0, e1, e2⟩ := hv
  refine ⟨m * monoX c dh, n * monoX c dg, ?_, ?_, ?_⟩
  · rw [map_mul]; exact mul_ne_zero h0 (aeval_monoX_ne hc _)
  · rw [map_mul, map_mul, e2, ← chartMono_mul hc he]; ring
  · have hd : IsMultiHomog (m * monoX c dh * g - n * monoX c dg * h) (d + dh + dg) := by
      refine GroundTheory.Heights₂.Heights.LowerBoundFree.isMultiHomog_sub
        (GroundTheory.Heights₂.Heights.LowerBoundFree.isMultiHomog_mul
          (GroundTheory.Heights₂.Heights.LowerBoundFree.isMultiHomog_mul hm (isMultiHomog_monoX _ _)) hg) ?_
      rw [add_right_comm]
      exact GroundTheory.Heights₂.Heights.LowerBoundFree.isMultiHomog_mul
        (GroundTheory.Heights₂.Heights.LowerBoundFree.isMultiHomog_mul hn (isMultiHomog_monoX _ _)) hh
    rw [mem_iff_of_homog hd]
    simp only [map_sub, map_mul, e1, hq, ← chartMono_mul hcw he]
    have := chartMono_ne hcw e
    field_simp
    ring

theorem congr_aeval {σ : Type} (O : Subring Φ) (a b : σ → Φ) (V : Φ) (ha : ∀ q, a q ∈ O) (hb : ∀ q, b q ∈ O)
    (hab : ∀ q, ∃ ρ ∈ O, a q - b q = ρ * V) (f : MvPolynomial σ ℤ) :
    aeval a f ∈ O ∧ ∃ ρ ∈ O, aeval a f - aeval b f = ρ * V := by
  induction f using MvPolynomial.induction_on with
  | C n => exact ⟨by simp, 0, zero_mem _, by simp⟩
  | add f g hf hg =>
    obtain ⟨h1, ρ, h2, h3⟩ := hf
    obtain ⟨h1', ρ', h2', h3'⟩ := hg
    exact ⟨by rw [map_add]; exact add_mem h1 h1', ρ + ρ', add_mem h2 h2', by
      rw [map_add (f := _), map_add (f := _)]; linear_combination h3 + h3'⟩
  | mul_X f q hf =>
    obtain ⟨h1, ρ, h2, h3⟩ := hf
    obtain ⟨ρ', h2', h3'⟩ := hab q
    refine ⟨by rw [map_mul, aeval_X]; exact mul_mem h1 (ha q), aeval a f * ρ' + ρ * b q,
      add_mem (mul_mem h1 h2') (mul_mem h2 (hb q)), ?_⟩
    rw [map_mul, map_mul, aeval_X, aeval_X]
    linear_combination (aeval a f) * h3' + b q * h3

variable {y : (Σ k, ι k) → Φ} {k₀ : K} {B : ι k₀ → Φ} {cf : Φ} {e : K → ℤ}

def totDeg (k₀ : K) (e : K → ℤ) : Option K → ℤ := fun o => o.elim 1 fun k => e k + if k = k₀ then 1 else 0

namespace PenFrame

variable {z : (Σ k, ι k) → L} {c : ∀ k, ι k} (Fr : PenFrame y k₀ B cf e z c)

theorem αA : ∑ m, Fr.α m * y ⟨k₀, m⟩ = Fr.ε⁻¹ := by
  have h := Fr.αp
  simp only [Fr.p_eq, mul_left_comm _ Fr.ε, ← Finset.mul_sum] at h
  exact eq_inv_of_mul_eq_one_right h

theorem βA : ∑ m, Fr.β m * y ⟨k₀, m⟩ = 0 := by
  have h := Fr.βp
  simp only [Fr.p_eq, mul_left_comm _ Fr.ε, ← Finset.mul_sum] at h
  exact (mul_eq_zero.1 h).resolve_left Fr.ε_ne

theorem αB : ∑ m, Fr.α m * B m = -(Fr.δ * Fr.ε⁻¹ * Fr.γ⁻¹) := by
  have h := Fr.αr
  simp only [Fr.r_eq, mul_add, Finset.sum_add_distrib, mul_left_comm _ Fr.γ, mul_left_comm _ Fr.δ, ← Finset.mul_sum,
    Fr.αA] at h
  have := Fr.γ_ne
  have h' : ∑ m, Fr.α m * B m = Fr.γ⁻¹ * (Fr.γ * ∑ m, Fr.α m * B m) := by rw [inv_mul_cancel_left₀ this]
  rw [h', eq_neg_of_add_eq_zero_left h]; ring

theorem βB : ∑ m, Fr.β m * B m = Fr.γ⁻¹ := by
  have h := Fr.βr
  simp only [Fr.r_eq, mul_add, Finset.sum_add_distrib, mul_left_comm _ Fr.γ, mul_left_comm _ Fr.δ, ← Finset.mul_sum,
    Fr.βA, mul_zero, add_zero] at h
  exact eq_inv_of_mul_eq_one_right h

end PenFrame

theorem pen_lin (μ : ι k₀ → Φ) (A : ι k₀ → Φ) (t : RatFunc Φ) :
    ∑ m, algebraMap Φ (RatFunc Φ) (μ m) * penCo y k₀ A B t ⟨none, m⟩ =
      algebraMap Φ (RatFunc Φ) (∑ m, μ m * A m) + t * algebraMap Φ (RatFunc Φ) (∑ m, μ m * B m) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [penCo, mul_add, Finset.sum_add_distrib, mul_left_comm _ t, ← Finset.mul_sum, ← map_mul, ← map_sum]

theorem local_data {z : (Σ o : Option K, ι (o.getD k₀)) → L}
    (hz : IsPt (penCo y k₀ (fun m => y ⟨k₀, m⟩) B RatFunc.X) z) {c : ∀ o, iW ι k₀ o} (hc : ∀ o, z ⟨o, c o⟩ ≠ 0)
    (Fr : PenFrame y k₀ B cf e (z ∘ v₀ k₀) fun k => c (some k)) :
    ∃ (η U V : RatFunc Φ) (Uv : L),
      HasVal (penCo y k₀ (fun m => y ⟨k₀, m⟩) B RatFunc.X) z η
        (Fr.sv * ∑ m, Fr.αv m * (z ⟨some k₀, m⟩ / z ⟨some k₀, c (some k₀)⟩)) ∧
      (∀ m, z ⟨some k₀, m⟩ / z ⟨some k₀, c (some k₀)⟩ =
        Fr.pv m * ∑ m, Fr.αv m * (z ⟨some k₀, m⟩ / z ⟨some k₀, c (some k₀)⟩)) ∧
      HasVal (penCo y k₀ (fun m => y ⟨k₀, m⟩) B RatFunc.X) z U Uv ∧
      HasVal (penCo y k₀ (fun m => y ⟨k₀, m⟩) B RatFunc.X) z V (∑ m, Fr.βv m * (z ⟨none, m⟩ / z ⟨none, c none⟩)) ∧
      (∀ m, penCo y k₀ (fun m => y ⟨k₀, m⟩) B RatFunc.X ⟨none, m⟩ /
          penCo y k₀ (fun m => y ⟨k₀, m⟩) B RatFunc.X ⟨none, c none⟩ =
        algebraMap Φ (RatFunc Φ) (Fr.p m) * U + algebraMap Φ (RatFunc Φ) (Fr.r m) * V) ∧
      RatFunc.X * algebraMap Φ (RatFunc Φ) cf /
        chartMono (penCo y k₀ (fun m => y ⟨k₀, m⟩) B RatFunc.X) c (totDeg k₀ e) = η * V := by
  set w := penCo y k₀ (fun m => y ⟨k₀, m⟩) B RatFunc.X with hw
  let φ := algebraMap Φ (RatFunc Φ)
  have hz0 : IsPt y (z ∘ v₀ k₀) := hz.comp (isBlockMap_initial_vertex k₀) φ rfl
  have pull : ∀ {s v}, HasVal y (z ∘ v₀ k₀) s v → HasVal w z (φ s) v := fun h => h.pull (isBlockMap_initial_vertex k₀) φ rfl
  have hcy : ∀ k, y ⟨k, c (some k)⟩ ≠ 0 := fun k => hz0.coord_ne (q := ⟨k, c (some k)⟩) (hc (some k))
  have hcw : w ⟨none, c none⟩ ≠ 0 := hz.coord_ne (hc none)
  have hε := Fr.ε_ne
  have hγ := Fr.γ_ne
  have hU₀ : HasVal y (z ∘ v₀ k₀) (∑ m, Fr.α m * (y ⟨k₀, m⟩ / y ⟨k₀, c (some k₀)⟩))
      (∑ m, Fr.αv m * (z ⟨some k₀, m⟩ / z ⟨some k₀, c (some k₀)⟩)) :=
    HasVal.sum _ fun m _ => (Fr.hα m).mul (hasVal_ratio hz0 m (c (some k₀)) (hc (some k₀)))
  have eU₀ : (∑ m, Fr.α m * (y ⟨k₀, m⟩ / y ⟨k₀, c (some k₀)⟩)) = Fr.ε⁻¹ / y ⟨k₀, c (some k₀)⟩ := by
    rw [← Fr.αA, Finset.sum_div]
    simp only [mul_div_assoc]
  rw [eU₀] at hU₀
  have lin : ∀ (μ : ι k₀ → Φ) (μv : ι k₀ → L), (∀ m, HasVal y (z ∘ v₀ k₀) (μ m) (μv m)) →
      HasVal w z ((φ (∑ m, μ m * y ⟨k₀, m⟩) + RatFunc.X * φ (∑ m, μ m * B m)) / w ⟨none, c none⟩)
        (∑ m, μv m * (z ⟨none, m⟩ / z ⟨none, c none⟩)) := fun μ μv h => by
    rw [← pen_lin (y := y), Finset.sum_div]
    simp only [mul_div_assoc]
    exact HasVal.sum _ fun m _ => (pull (h m)).mul (hasVal_ratio hz (k := none) m (c none) (hc none))
  have hU := lin _ _ Fr.hα
  have hV := lin _ _ Fr.hβ
  rw [Fr.αA, Fr.αB] at hU
  rw [Fr.βA, Fr.βB] at hV
  have hφε : φ Fr.ε ≠ 0 := (map_ne_zero φ).2 hε
  have hφγ : φ Fr.γ ≠ 0 := (map_ne_zero φ).2 hγ
  refine ⟨_, _, _, _, pull (Fr.hs.mul hU₀), fun m => ?_, hU, hV, fun m => ?_, ?_⟩
  · refine (hasVal_ratio hz0 m (c (some k₀)) (hc (some k₀))).unique hz0 ?_
    have := (Fr.hp m).mul hU₀
    rwa [Fr.p_eq, show Fr.ε * y ⟨k₀, m⟩ * (Fr.ε⁻¹ / y ⟨k₀, c (some k₀)⟩) = y ⟨k₀, m⟩ / y ⟨k₀, c (some k₀)⟩ by
      field_simp] at this
  · rw [Fr.p_eq, Fr.r_eq, show w ⟨none, m⟩ = φ (y ⟨k₀, m⟩) + RatFunc.X * φ (B m) from rfl]
    simp only [map_mul, map_add (f := _), map_neg, map_inv₀, map_zero]
    change _ = φ _ * φ _ * _ + (φ _ * φ _ + φ _ * φ _) * _
    field_simp
    ring
  · have e1 : chartMono w c (totDeg k₀ e) = w ⟨none, c none⟩ *
        (φ (chartMono y (fun k => c (some k)) e) * φ (y ⟨k₀, c (some k₀)⟩)) := by
      rw [chartMono, Fintype.prod_option, chartMono, map_prod]
      congr 1
      · exact zpow_one _
      · have : ∀ k, w ⟨some k, c (some k)⟩ ^ totDeg k₀ e (some k) = φ (y ⟨k, c (some k)⟩ ^ e k) *
            if k = k₀ then φ (y ⟨k₀, c (some k₀)⟩) else 1 := fun k => by
          show φ (y ⟨k, c (some k)⟩) ^ (e k + if k = k₀ then 1 else 0) = _
          rw [zpow_add₀ ((map_ne_zero φ).2 (hcy k)), map_zpow₀]
          split_ifs with h
          · subst h; rw [zpow_one]
          · rw [zpow_zero]
        simp only [this, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, if_true]
    have h1 : φ (chartMono y (fun k => c (some k)) e) ≠ 0 := (map_ne_zero φ).2 (chartMono_ne hcy e)
    have h2 : φ (y ⟨k₀, c (some k₀)⟩) ≠ 0 := (map_ne_zero φ).2 (hcy k₀)
    rw [e1]
    simp only [map_mul, map_div₀, map_inv₀, map_zero]
    change RatFunc.X * φ cf / _ = _
    field_simp
    ring

theorem isPt_diag {z : (Σ k, ι k) → L} (hz : IsPt y z) :
    IsPt (ext2 y k₀ fun m => y ⟨k₀, m⟩) (ext2 z k₀ fun m => z ⟨k₀, m⟩) := by
  let fold : (Σ o : Option K, ι (o.getD k₀)) → Σ k, ι k := fun q => ⟨q.1.getD k₀, q.2⟩
  have e1 : (ext2 y k₀ fun m => y ⟨k₀, m⟩) = y ∘ fold := by
    funext q
    rcases q with ⟨_ | k, m⟩ <;> rfl
  have e2 : (ext2 z k₀ fun m => z ⟨k₀, m⟩) = z ∘ fold := by
    funext q
    rcases q with ⟨_ | k, m⟩ <;> rfl
  rw [e1, e2]
  refine ⟨fun o => hz.1 (o.getD k₀), fun f hf => ?_⟩
  rw [← aeval_rename]
  refine hz.2 _ ?_
  have hf' : mConeMap (y ∘ fold) f = 0 := hf
  have e : (mConeMap y).comp (rename fold) = ((rename fun o : Option K => o.getD k₀).restrictScalars ℤ).comp
      (mConeMap (y ∘ fold)) := MvPolynomial.algHom_ext fun q => by simp [mConeMap, fold]
  have := DFunLike.congr_fun e f
  simp only [AlgHom.comp_apply, hf', map_zero] at this
  exact this

theorem sec_pen (h0 : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0)
    (hFr : ∀ (E : Type) [Field E] (z : (Σ k, ι k) → E), IsPt y z → ∀ c : ∀ k, ι k, (∀ k, z ⟨k, c k⟩ ≠ 0) →
      Nonempty (PenFrame y k₀ B cf e z c)) :
    ∃ (g h : MRing (iW ι k₀)) (dg dh : Option K → ℕ), IsMultiHomog g dg ∧ IsMultiHomog h dh ∧
      g ∉ mCoordIdeal (penCo y k₀ (fun m => y ⟨k₀, m⟩) B RatFunc.X) ∧
      h ∉ mCoordIdeal (penCo y k₀ (fun m => y ⟨k₀, m⟩) B RatFunc.X) ∧
      (∀ o, (dg o : ℤ) - dh o = totDeg k₀ e o) ∧
      aeval (penCo y k₀ (fun m => y ⟨k₀, m⟩) B RatFunc.X) g =
        RatFunc.X * algebraMap Φ (RatFunc Φ) cf * aeval (penCo y k₀ (fun m => y ⟨k₀, m⟩) B RatFunc.X) h ∧
      divCycle (mCoordIdeal (penCo y k₀ (fun m => y ⟨k₀, m⟩) B RatFunc.X)) g =
        divCycle (mCoordIdeal (penCo y k₀ (fun m => y ⟨k₀, m⟩) B RatFunc.X)) h +
          Finsupp.single (mCoordIdeal (ext2 y k₀ fun m => y ⟨k₀, m⟩)) 1 := by
  set w := penCo y k₀ (fun m => y ⟨k₀, m⟩) B RatFunc.X with hw
  set δ := ext2 y k₀ fun m => y ⟨k₀, m⟩ with hδ
  let φ := algebraMap Φ (RatFunc Φ)
  choose c₀ hc₀ using h0
  let c : ∀ o, iW ι k₀ o := fun o => c₀ (o.getD k₀)
  have hc : ∀ o, δ ⟨o, c o⟩ ≠ 0 := by
    rintro (_ | k)
    · exact hc₀ k₀
    · exact hc₀ k
  have hle : mCoordIdeal w ≤ mCoordIdeal δ := pen_le_zero _ _ _ _
  have hpt : IsPt w δ := ⟨fun o => ⟨c o, hc o⟩, fun f hf => aeval_eq_zero_of_mem (hle hf)⟩
  have hcw : ∀ o, w ⟨o, c o⟩ ≠ 0 := fun o => hpt.coord_ne (hc o)
  obtain ⟨Fr⟩ := hFr Φ y (isPt_self fun k => ⟨c₀ k, hc₀ k⟩) c₀ hc₀
  obtain ⟨η, U, V, Uv, hη, hp, hU, hV, hrel, hσ⟩ := local_data (cf := cf) (e := e) hpt hc Fr
  rw [← hw] at hη hU hV hrel hσ
  have hηv : (Fr.sv * ∑ m, Fr.αv m * (δ ⟨some k₀, m⟩ / δ ⟨some k₀, c (some k₀)⟩)) ≠ 0 := by
    refine mul_ne_zero Fr.sv_ne fun h => ?_
    have := hp (c (some k₀))
    rw [h, mul_zero, div_self (hc _)] at this
    exact one_ne_zero this
  have hV0 : (∑ m, Fr.βv m * (δ ⟨none, m⟩ / δ ⟨none, c none⟩)) = 0 := by
    simp only [← mul_div_assoc, ← Finset.sum_div, hasVal_self_eq (Fr.hβ _)]
    rw [show (∑ m, Fr.β m * δ ⟨none, m⟩) = 0 from Fr.βA, zero_div]
  rw [hV0] at hV
  have hcf : cf ≠ 0 := by
    rintro rfl
    exact Fr.hs.ne_zero (isPt_self fun k => ⟨c₀ k, hc₀ k⟩) Fr.sv_ne (by simp)
  have hσ0 : RatFunc.X * φ cf ≠ 0 := mul_ne_zero RatFunc.X_ne_zero ((map_ne_zero φ).2 hcf)
  obtain ⟨d, n, m, hn, hm, hm0, e1, e2⟩ := hη.mul hV
  let dp : Option K → ℕ := fun o => (totDeg k₀ e o).toNat
  let dm : Option K → ℕ := fun o => (-totDeg k₀ e o).toNat
  have hpm : ∀ o, (dp o : ℤ) - dm o = totDeg k₀ e o := fun o => Int.toNat_sub_toNat_neg _
  have hg := GroundTheory.Heights₂.Heights.LowerBoundFree.isMultiHomog_mul hn (isMultiHomog_monoX c dp)
  have hh := GroundTheory.Heights₂.Heights.LowerBoundFree.isMultiHomog_mul hm (isMultiHomog_monoX c dm)
  have hdeg : ∀ o, ((d + dp) o : ℤ) - (d + dm) o = totDeg k₀ e o := fun o => by
    rw [← hpm]; simp
  have hhδ : aeval δ (m * monoX c dm) ≠ 0 := by rw [map_mul]; exact mul_ne_zero hm0 (aeval_monoX_ne hc _)
  have hhw : aeval w (m * monoX c dm) ≠ 0 := hpt.aeval_ne hh hhδ
  have hmono := chartMono_ne hcw (totDeg k₀ e)
  have hq : aeval w (n * monoX c dp) = RatFunc.X * φ cf * aeval w (m * monoX c dm) := by
    rw [map_mul, map_mul, e1, ← hσ, ← chartMono_mul hcw hpm]
    change RatFunc.X * φ cf / _ * _ * _ = _
    field_simp
  set g := n * monoX c dp
  set h := m * monoX c dm
  have hgw : g ∉ mCoordIdeal w := fun hh' => mul_ne_zero hσ0 hhw (hq ▸ aeval_eq_zero_of_mem hh')
  have hΔp : (mCoordIdeal δ).IsPrime := RingHom.ker_isPrime _
  refine ⟨g, h, d + dp, d + dm, hg, hh, hgw, fun hh' => hhw (aeval_eq_zero_of_mem hh'), hdeg, hq, ?_⟩
  refine div_eq_of_local (RingHom.ker_isPrime _) hΔp (CoordinateConeArithVar.relevant δ c hc) hle hgw
    (fun hh' => hhδ (aeval_eq_zero_of_mem hh')) ((mem_iff_of_homog hg).2 (by
      rw [map_mul, e2, mul_zero, zero_mul, zero_mul])) ?_ ?_
  · let J : Ideal (MRing (iW ι k₀)) :=
      { carrier := {f | ∃ u ∉ mCoordIdeal δ, u * f ∈ mCoordIdeal w ⊔ Ideal.span {g}}
        add_mem' := by
          rintro a b ⟨u, hu, hua⟩ ⟨v, hv, hvb⟩
          refine ⟨u * v, fun hm => (hΔp.mem_or_mem hm).elim hu hv, ?_⟩
          have e' : u * v * (a + b) = v * (u * a) + u * (v * b) := by ring
          rw [e']
          exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hua) (Ideal.mul_mem_left _ _ hvb)
        zero_mem' := ⟨1, fun h1 => hΔp.ne_top ((Ideal.eq_top_iff_one _).2 h1), by simp⟩
        smul_mem' := by
          rintro a b ⟨u, hu, hub⟩
          refine ⟨u, hu, ?_⟩
          rw [smul_eq_mul, mul_left_comm]
          exact Ideal.mul_mem_left _ _ hub }
    refine mCoordIdeal_le_of_homog (J := J) fun f a hf hf0 => ?_
    have pull : ∀ {s v}, HasVal y y s v → φ s ∈ regO w δ := fun h =>
      ⟨_, HasVal.pull (isBlockMap_initial_vertex k₀) φ (y' := w) (z' := δ) rfl h⟩
    let sc : Option K → RatFunc Φ := fun o => o.elim (φ Fr.ε * U) fun k => (φ (y ⟨k, c₀ k⟩))⁻¹
    have hrat : ∀ q, CoordinateConeArithVar.ratioPt w c q ∈ regO w δ := fun q =>
      ⟨_, hasVal_ratio hpt q.2 (c q.1) (hc q.1)⟩
    have hb1 : ∀ m, sc none * (φ ∘ δ) ⟨none, m⟩ = φ (Fr.p m) * U := fun m => by
      rw [Fr.p_eq, map_mul]
      show φ Fr.ε * U * φ (y ⟨k₀, m⟩) = _
      ring
    have hb2 : ∀ k m, sc (some k) * (φ ∘ δ) ⟨some k, m⟩ = CoordinateConeArithVar.ratioPt w c ⟨some k, m⟩ := fun k m => by
      show (φ (y ⟨k, c₀ k⟩))⁻¹ * φ (y ⟨k, m⟩) = φ (y ⟨k, m⟩) / φ (y ⟨k, c₀ k⟩)
      rw [div_eq_mul_inv, mul_comm]
    obtain ⟨-, ρ, hρ, hρe⟩ := congr_aeval (regO w δ) (CoordinateConeArithVar.ratioPt w c)
      (fun q => sc q.1 * (φ ∘ δ) q) V hrat (by
        rintro ⟨_ | k, m⟩
        · exact hb1 m ▸ mul_mem (pull (Fr.hp m)) ⟨_, hU⟩
        · exact hb2 k m ▸ hrat _) (by
        rintro ⟨_ | k, m⟩
        · refine ⟨φ (Fr.r m), pull (Fr.hr m), ?_⟩
          rw [hb1 m, show CoordinateConeArithVar.ratioPt w c ⟨none, m⟩ = _ from hrel m]
          exact add_sub_cancel_left _ _
        · exact ⟨0, zero_mem _, by rw [hb2 k m, sub_self, zero_mul]⟩) f
    rw [aeval_scale' sc _ hf, CPts.aeval_comp_ringHom, hf0, map_zero, mul_zero, sub_zero, aeval_ratioPt hf] at hρe
    obtain ⟨ρv, hρ⟩ := hρ
    obtain ⟨d', n', m', hn', hm', hm0', e1', -⟩ := hρ.mul (hη.inv hpt hηv)
    have hη0 : η ≠ 0 := hη.ne_zero hpt hηv
    refine ⟨m' * monoX c (d + dp) * h, fun hh' => ?_, ?_⟩
    · have := aeval_eq_zero_of_mem hh'
      rw [map_mul, map_mul] at this
      exact mul_ne_zero (mul_ne_zero hm0' (aeval_monoX_ne hc _)) hhδ this
    · have hd : IsMultiHomog (m' * monoX c (d + dp) * h * f - n' * monoX c a * monoX c (d + dm) * g)
          (d' + (d + dp) + (d + dm) + a) := by
        refine GroundTheory.Heights₂.Heights.LowerBoundFree.isMultiHomog_sub
          (GroundTheory.Heights₂.Heights.LowerBoundFree.isMultiHomog_mul
            (GroundTheory.Heights₂.Heights.LowerBoundFree.isMultiHomog_mul
              (GroundTheory.Heights₂.Heights.LowerBoundFree.isMultiHomog_mul hm' (isMultiHomog_monoX _ _)) hh) hf) ?_
        rw [show d' + (d + dp) + (d + dm) + a = d' + a + (d + dm) + (d + dp) by ring]
        exact GroundTheory.Heights₂.Heights.LowerBoundFree.isMultiHomog_mul
          (GroundTheory.Heights₂.Heights.LowerBoundFree.isMultiHomog_mul
            (GroundTheory.Heights₂.Heights.LowerBoundFree.isMultiHomog_mul hn' (isMultiHomog_monoX _ _))
            (isMultiHomog_monoX _ _)) hg
      have hP : m' * monoX c (d + dp) * h * f - n' * monoX c a * monoX c (d + dm) * g ∈ mCoordIdeal w := by
        rw [mem_iff_of_homog hd]
        have h1 : aeval w f = aeval w (monoX c a) * (ρ * V) := by
          rw [← hρe, aeval_monoX, ← mul_assoc, ← Finset.prod_mul_distrib, Finset.prod_eq_one fun k _ => by
            rw [← mul_pow, mul_inv_cancel₀ (hcw k), one_pow], one_mul]
        have h2 : RatFunc.X * φ cf = η * V * chartMono w c (totDeg k₀ e) := by
          rw [← hσ]; exact (div_mul_cancel₀ _ hmono).symm
        rw [map_sub, map_mul _ _ f, map_mul _ _ g, map_mul _ _ h, map_mul _ m', map_mul _ (n' * _), map_mul _ n', h1, hq, h2, e1',
          ← chartMono_mul hcw hdeg]
        field_simp
        ring
      have e' : m' * monoX c (d + dp) * h * f = (m' * monoX c (d + dp) * h * f - n' * monoX c a * monoX c (d + dm) * g)
          + n' * monoX c a * monoX c (d + dm) * g := by ring
      rw [e']
      exact Ideal.add_mem _ (Ideal.mem_sup_left hP)
        (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self g)))
  · intro W hW hWr hPW hΔW
    obtain ⟨E, _, z, hz⟩ := exists_point W hW
    choose c' hc' using hWr
    have hc'' : ∀ o, z ⟨o, c' o⟩ ≠ 0 := fun o h => hc' o ((hz _).1 (by rwa [aeval_X]))
    have hzp : IsPt w z := ⟨fun o => ⟨c' o, hc'' o⟩, fun f hf => (hz f).2 (hPW hf)⟩
    have hz0 : IsPt y (z ∘ v₀ k₀) := hzp.comp (isBlockMap_initial_vertex k₀) φ rfl
    obtain ⟨Fr'⟩ := hFr E (z ∘ v₀ k₀) hz0 (fun k => c' (some k)) fun k => hc'' (some k)
    obtain ⟨η', U', V', Uv', hη', hp', hU', hV', hrel', hσ'⟩ := local_data (cf := cf) (e := e) hzp hc'' Fr'
    rw [← hw] at hη' hU' hV' hrel' hσ'
    set U₀ := ∑ m, Fr'.αv m * (z ⟨some k₀, m⟩ / z ⟨some k₀, c' (some k₀)⟩)
    set Vv := ∑ m, Fr'.βv m * (z ⟨none, m⟩ / z ⟨none, c' none⟩)
    have hU₀ : U₀ ≠ 0 := fun h => by
      have := hp' (c' (some k₀))
      rw [h, mul_zero, div_self (hc'' _)] at this
      exact one_ne_zero this
    have hVv : Vv ≠ 0 := fun h => hΔW <| by
      rw [h] at hV'
      have h1 : ∀ m, z ⟨none, m⟩ / z ⟨none, c' none⟩ = Fr'.pv m * Uv' := fun m => by
        refine (hasVal_ratio hzp (k := none) m (c' none) (hc'' none)).unique hzp ?_
        rw [hrel' m]
        simpa only [mul_zero, add_zero] using (((Fr'.hp m).pull (isBlockMap_initial_vertex k₀) φ (y' := w) rfl).mul hU').add
          (((Fr'.hr m).pull (isBlockMap_initial_vertex k₀) φ (y' := w) rfl).mul hV')
      let sc : Option K → E := fun o => o.elim (z ⟨none, c' none⟩ * Uv' / (U₀ * z ⟨some k₀, c' (some k₀)⟩)) fun _ => 1
      have h2 : z = fun q => sc q.1 * ext2 (z ∘ v₀ k₀) k₀ (fun m => (z ∘ v₀ k₀) ⟨k₀, m⟩) q := by
        funext q
        rcases q with ⟨_ | k, m⟩
        · show z ⟨none, m⟩ = z ⟨none, c' none⟩ * Uv' / (U₀ * z ⟨some k₀, c' (some k₀)⟩) * z ⟨some k₀, m⟩
          have a1 := (div_eq_iff (hc'' none)).1 (h1 m)
          have a2 := (div_eq_iff (hc'' (some k₀))).1 (hp' m)
          have a3 := hc'' (some k₀)
          rw [a1, a2]
          field_simp
        · exact (one_mul _).symm
      refine mCoordIdeal_le_of_homog fun f a hf hf0 => (hz f).1 ?_
      rw [h2, aeval_scale' sc _ hf, (isPt_diag hz0).2 f ((mem_iff_of_homog hf).2 hf0), mul_zero]
    obtain ⟨u, u', hu, hu', hm⟩ := exists_rel hzp hc'' (hσ' ▸ hη'.mul hV') hg hh hdeg hq
    refine ⟨u, u', fun h => hu ((hz _).2 h), fun h => ?_, hm⟩
    rw [(hz _).2 h] at hu'
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero Fr'.sv_ne hU₀) hVv) (chartMono_ne hc'' _)) hu hu'.symm

end PositivityTheory.Xgp.W
end
end

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

theorem PositivityTheory.Xgp.t_c_w_sec : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (d : ℕ) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → IsArithVar (mCoordIdeal y) (d + 2) → ∃ (g h : MRing fun o : Option K => ι (o.getD k₀)) (dg dh : Option K → ℕ), IsMultiHomog g dg ∧ IsMultiHomog h dh ∧ g ∉ mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X) ∧ h ∉ mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X) ∧ (∀ o : Option K, (dg o : ℤ) - dh o = o.elim 1 fun k => -(fun k => ∑ p, xiCoef τ a p * M.dy p k) k - (if M.blk (τ, a) = some k then 1 else 0)) ∧ aeval (M.wCo (τ, a) k₀ ca cb RatFunc.X) g = RatFunc.X * algebraMap Φ (RatFunc Φ) (∏ p, (if IsProperStep N j p.2 then 1 else algebraMap M.Ω Φ (M.lam p) * (if (p.2 : ℕ) + 1 = j then (if (a : ℕ) < j then minorIJ (M.g p.1) (wIdx N j) (wIdx N j) else 1) else minorIJ (M.g p.1) (omIdx N j) (omIdx N j))) ^ xiCoef τ a p) * aeval (M.wCo (τ, a) k₀ ca cb RatFunc.X) h ∧ divCycle (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) g = divCycle (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) h + Finsupp.single (mCoordIdeal (M.wCo (τ, a) k₀ ca cb 0)) 1 := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M d τ a b k₀ ca cb hb hab hk hca hcb _
  have hne : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := PositivityTheory.Xgp.W.blocks_of_model M
  obtain ⟨g, h, dg, dh, hg, hh, hgn, hhn, hdeg, haev, hdiv⟩ :=
    PositivityTheory.Xgp.W.sec_pen (B := PositivityTheory.Xgp.W.vecB M τ a k₀ ca cb) (cf := PositivityTheory.Xgp.W.cFac M τ a)
      (e := PositivityTheory.Xgp.W.eDeg M τ a k₀) hne
      (fun E _ z hz c hc => PositivityTheory.Xgp.W.exists_penFrame M hb hab hk hca hcb hz c hc)
  refine ⟨g, h, dg, dh, hg, hh, ?_⟩
  rw [PositivityTheory.Xgp.W.wCo_eq M hb hab hk hca hcb, PositivityTheory.Xgp.W.wCo_eq M hb hab hk hca hcb,
    PositivityTheory.Xgp.W.ideal_pen_zero]
  refine ⟨hgn, hhn, ?_, ?_, hdiv⟩
  · intro o
    rw [hdeg o]
    cases o with
    | none => rfl
    | some k =>
      simp only [PositivityTheory.Xgp.W.totDeg, PositivityTheory.Xgp.W.eDeg, Option.elim, hk, Option.some.injEq]
      by_cases hkk : k = k₀
      · subst hkk
        simp
        ring
      · simp [hkk, Ne.symm hkk]
  · have hI : (PositivityTheory.Xgp.W.intAlg5 : Algebra ℤ (RatFunc Φ)) = RatFunc.instAlgebraOfPolynomial Φ ℤ :=
      Subsingleton.elim _ _
    have key : ∀ f : MRing (PositivityTheory.Xgp.W.iW ι k₀),
        @aeval ℤ (RatFunc Φ) _ _ _ PositivityTheory.Xgp.W.intAlg5
          (PositivityTheory.Xgp.W.penCo y k₀ (fun m => y ⟨k₀, m⟩) (PositivityTheory.Xgp.W.vecB M τ a k₀ ca cb) RatFunc.X) f =
        @aeval ℤ (RatFunc Φ) _ _ _ (RatFunc.instAlgebraOfPolynomial Φ ℤ)
          (PositivityTheory.Xgp.W.penCo y k₀ (fun m => y ⟨k₀, m⟩) (PositivityTheory.Xgp.W.vecB M τ a k₀ ca cb) RatFunc.X) f := by
      intro f
      rw [hI]
    rw [key g, key h] at haev
    exact haev
end

section -- merged from Development.WeilBound.CoreStatements.PluriharmonicCharts.XCSwap
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

theorem PositivityTheory.Xgp.t_c_swap : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (τ : Ψ) (a b : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → ∃ (k₀ : K) (ca cb : Fin N), M.blk (τ, a) = some k₀ ∧ (ca : ℕ) = lastCol N j a ∧ (cb : ℕ) = ca + 1 ∧ ((ca : ℕ) < N - j ↔ (cb : ℕ) < N - j) ∧ (∑ p, xiCoef τ a p * M.dy p k₀) = -2 ∧ ∀ p, p ≠ (τ, a) → M.dy p k₀ = 0 := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M τ a b hab hcase
  have hjN := M.j_le
  have hbN := b.isLt
  have ha1 : (a : ℕ) + 1 ≠ j := by omega
  have ha2 : (a : ℕ) + 1 ≠ N := by omega
  have hprop : IsProperStep N j a := ⟨ha1, ha2⟩
  obtain ⟨k₀, hk₀⟩ : ∃ k₀, M.blk (τ, a) = some k₀ := by
    cases h : M.blk (τ, a) with
    | none => exact ((M.blk_none (τ, a)).1 h hprop).elim
    | some k => exact ⟨k, rfl⟩
  have hdy : ∀ p, M.dy p k₀ = if p = (τ, a) then 1 else 0 := by
    intro p
    unfold FlagModel.dy
    have hnot : ¬ ∀ p' : Ψ × Fin N, M.blk p' ≠ some k₀ := fun h => h (τ, a) hk₀
    rw [dite_eq_right hnot]
    by_cases hp : p = (τ, a)
    · subst hp
      simp [hk₀]
    · rw [if_neg hp, if_neg]
      intro h
      exact hp (M.blk_inj p (τ, a) k₀ h hk₀)
  have hlast : lastCol N j a < N ∧ lastCol N j a + 1 < N ∧
      (lastCol N j a < N - j ↔ lastCol N j a + 1 < N - j) := by
    unfold lastCol
    split_ifs with h <;> omega
  refine ⟨k₀, ⟨lastCol N j a, hlast.1⟩, ⟨lastCol N j a + 1, hlast.2.1⟩, hk₀, rfl, rfl, hlast.2.2, ?_, ?_⟩
  · simp only [hdy, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp [xiCoef]
  · intro p hp
    rw [hdy p, if_neg hp]
end

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section
namespace PositivityTheory.Xgp.c_sqsys

open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.CovMap PositivityTheory.Xgp.c_algsq

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}
variable {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] {Φ' : Type} [Field Φ'] {y' : (Σ k, ι' k) → Φ'}

variable {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} {n d : ℕ} {BM : BaseMetric M n} {FA : FlagAn BM d}
  {Cv : FlagCover M' M}

theorem lift_inj (FA : FlagAn BM d) {x x' : FA.Re.R.X} (h : SameOrbit (FA.Re.R.lift x x) (FA.Re.R.lift x' x')) :
    x = x' :=
  FA.Re.R.inj x x' (fun h => by
    have := h.2 1 (by rw [FA.J_top]; trivial)
    simp at this) h

theorem varpi_eq (CR : CovReal FA Cv) (hy : IsArithVar (mCoordIdeal y) (d + 2))
    (hy' : IsArithVar (mCoordIdeal y') (d + 2)) {z : (Σ k, ι' k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y'))
    {x₀ : FA.Re.R.X} (hi : IsImg Cv z (FA.Re.R.lift x₀ x₀)) : CR.ϖ z = FA.Re.π x₀ := by
  obtain ⟨x₁, hx₁⟩ := (GlobalTheory.T.flag_analytic_projection_bijective K ι Φ y Ψ N j M n d BM FA).2 (CR.ϖ z)
  have h1 : IsImg Cv z (FA.Re.R.lift x₁ x₁) := fun z₁ o F' F hF' hF hg' hg h hfl =>
    CR.flags z₁ (mem_mcPts_of_sameOrbit hy'.2.1.2.1 o hz) F' F hF' hF hg' hg h hfl x₁
      (hx₁.trans (CR.ϖ_torus z z₁ hz o).symm)
  rw [← hx₁, lift_inj FA (GlobalTheory.T.flag_cover_arithmetic_second K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv d hy hy' z hz _ _ h1 hi)]

theorem pot_pull (CR : CovReal FA Cv) (hy : IsArithVar (mCoordIdeal y) (d + 2))
    (hy' : IsArithVar (mCoordIdeal y') (d + 2)) {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)]
    {P J : Ideal (MRing ι₂)} {e : ℕ} (R : AnLogRes P J e) {κ : K' → K₂} {v : (Σ k, ι' k) → Σ k, ι₂ k}
    (hv : IsBlockMap κ v) (hP : ∀ z ∈ mcPts P, z ∘ v ∈ mcPts (mCoordIdeal y')) (g₀ : R.X → FA.Re.R.X)
    (hi : ∀ x, IsImg Cv (R.lift x x ∘ v) (FA.Re.R.lift (g₀ x) (g₀ x))) (p : Ψ × Fin N) (x : R.X) :
    LocRe R.A x fun u => Real.log ((CR.Re.ref p).h (R.lift x u ∘ v)) -
      (FA.S.th (some p)).φ (FA.Re.π (g₀ x)) (FA.Re.π (g₀ u)) := by
  have hg₀ : HoloMap R.A FA.Re.R.A g₀ := by
    refine GlobalTheory.T.log_resolution_map_locally_analytic _ _ _ _ _ _ _ _ _ _ FA.Re.R R g₀ FA.J_top fun x => ?_
    obtain ⟨V, f, hV, hzV, hf, hff⟩ := GlobalTheory.T.flag_cover_arithmetic_first K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv d hy hy' _
      (hP _ (R.mem x x (R.mem_U x)))
    refine ⟨(fun z => z ∘ v) ⁻¹' V, fun z => f (z ∘ v), hV.preimage (continuous_comp_idx v), hzV,
      fun z hz => (hf _ hz).comp (f := fun z => z ∘ v) (analytic_comp_idx v z), fun z' hz' x' hx' => ?_⟩
    exact GlobalTheory.T.flag_cover_arithmetic_second K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv d hy hy' _ (hP _ hz'.2) _ _ (hff _ ⟨hz'.1, hP _ hz'.2⟩).2
      ((hi x').orbit (FibreCount.comp_orbit hv hx') (Cj.sameOrbit_refl _))
  have hW : IsOpen (R.U x ∩ g₀ ⁻¹' FA.Re.R.U (g₀ x)) := (R.isOpen_U x).inter ((FA.Re.R.isOpen_U _).preimage hg₀.1)
  have L1 := pot_loc CR hy hy' (A := R.A) hW ⟨R.mem_U x, FA.Re.R.mem_U _⟩ (Z := fun u => R.lift x u ∘ v)
    (fun q => holo_mono (R.holo x (v q)) Set.inter_subset_left) (fun u hu => hP _ (R.mem x u hu.1))
    (Y := fun u => FA.Re.R.lift (g₀ x) (g₀ u))
    (fun q => holo_mono (GlobalTheory.CompanionTheory.Ar.PB.FA.BlockPot.holoOn_comp hg₀ (FA.Re.R.holo (g₀ x) q)) Set.inter_subset_right)
    (fun u hu => (FA.Re.R.mem _ _ hu.2).1)
    (fun u hu => (hi u).orbit (FibreCount.comp_orbit hv (R.compat x u u ⟨hu.1, R.mem_U u⟩))
      (FA.Re.R.compat _ _ _ ⟨hu.2, FA.Re.R.mem_U _⟩)) p
  have L2 : LocRe FA.Re.R.A (g₀ x) fun u => Real.log ((fsHerm ι (M.dy p)).h (FA.Re.R.lift (g₀ x) u)) -
      (FA.S.th (some p)).φ (FA.Re.π (g₀ x)) (FA.Re.π u) := by
    have := FA.Re.ref_pot (some p) (g₀ x) trivial
    rw [FA.ref_some] at this
    exact this
  exact (L1.add (L2.comp hg₀)).congr isOpen_univ trivial fun u _ => by ring

theorem log_comb {σ : Type} [Fintype σ] (A : σ → HermLine ι) (ε : σ → ℤ) {z : (Σ k, ι k) → ℂ}
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) : Real.log ((combLine A ε).h z) = ∑ p, (ε p : ℝ) * Real.log ((A p).h z) := by
  rw [combLine_h, Real.log_prod fun p _ => zpow_ne_zero _ ((A p).pos z hz).ne']
  simp only [Real.log_zpow]

end PositivityTheory.Xgp.c_sqsys

open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.CovMap PositivityTheory.Xgp.c_algsq PositivityTheory.Xgp.c_sqsys GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter in
theorem PositivityTheory.Xgp.t_c_sqsys : Inputs → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (CR : CovReal FA Cv), IsArithVar (mCoordIdeal y) (d + 2) → ∀ (τ : Ψ) (a b : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → Nonempty (SqSys CR.Re (τ, a) (xiCoef τ a)) := by
  intro hI K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA K' _ ι' _ Φ' _ y' M' Cv CR hy τ a b hb hab
  have hy' : IsArithVar (mCoordIdeal y') (d + 2) := CR.Re.arith
  obtain ⟨k₀, ca, cb, hk, hca, hcb, -, -, -⟩ := PositivityTheory.Xgp.t_c_swap K ι Φ y Ψ N j M τ a b hb hab
  obtain ⟨k₀', ca', cb', hk', hca', hcb', -, hxi', hdy'⟩ := PositivityTheory.Xgp.t_c_swap K' ι' Φ' y' Ψ N j M' τ a b hb hab
  obtain rfl : ca = ca' := Fin.ext (hca.trans hca'.symm)
  obtain rfl : cb = cb' := Fin.ext (hcb.trans hcb'.symm)
  have S : Sw M τ a b k₀ ca cb := ⟨hb, hab, hk, hca, hcb, PositivityTheory.Xgp.t_c_w_arith⟩
  have S' : Sw M' τ a b k₀' ca cb := ⟨hb, hab, hk', hca, hcb, PositivityTheory.Xgp.t_c_w_arith⟩
  obtain ⟨Q, RW, e, he, hde, hq0, hq1, -, hnorm⟩ :=
    GlobalTheory.T.flag_adjacent_swap_square_system hI K ι Φ y Ψ N j M n d BM FA τ a b k₀ ca cb hb hab hk hca hcb hy
  obtain ⟨g, h, dg, dh, hg, hh, hgn, hhn, hdeg, hq, hdiv⟩ :=
    PositivityTheory.Xgp.t_c_w_sec K' ι' Φ' y' Ψ N j M' d τ a b k₀' ca cb hb hab hk' hca hcb hy'
  have LC := PositivityTheory.Xgp.c_algsq.lc K' ι' Φ' y' Ψ N j M' d τ a b k₀' ca cb hb hab hk' hca hcb hy' g h dg dh hg hh hdeg hq
  obtain ⟨J, R', γ, br, hγ, hdegW, hrel⟩ := mapsTo_twoFlagFramesOrthogonal_of_isometry hI.2.1.1 Cv S S' hy hy' Q.SW.A RW e he hde
  have hxi : ∑ p, xiCoef τ a p * (CR.Re.ref p).a k₀' = -2 := by simpa only [CR.ref_deg] using hxi'
  have hdeg₁ : ∀ o : Option K', (dg o : ℤ) - dh o = o.elim 1 fun k => -(combLine CR.Re.ref (xiCoef τ a)).a k -
      (if M'.blk (τ, a) = some k then 1 else 0) := by simpa only [combLine_a, CR.ref_deg] using hdeg
  have hdeg₂ : ∀ o : Option K', (dg o : ℤ) - dh o =
      o.elim 1 fun k => -(∑ p, xiCoef τ a p * (CR.Re.ref p).a k) - if k₀' = k then 1 else 0 := by
    simpa only [combLine_a, hk', Option.some.injEq] using hdeg₁
  have hv₀ := Pts.isBlockMap_v₀ (ι := ι') k₀'
  have hv₁ := isBlockMap_v₁ (ι := ι') k₀'
  have hsurj := (GlobalTheory.T.flag_analytic_projection_bijective K ι Φ y Ψ N j M n d BM FA).2
  have o₀ : ∀ x x₀, FA.Re.π x₀ = Q.q 0 (e x) → SameOrbit (FA.Re.R.lift x₀ x₀) (fstPt k₀ (RW.lift x x)) := hq0
  have o₁ : ∀ x x₀, FA.Re.π x₀ = Q.q 1 (e x) → SameOrbit (FA.Re.R.lift x₀ x₀) (sndPt k₀ (RW.lift x x)) := by
    intro x x₀ hx
    obtain ⟨z₁, h1, h2, h3⟩ := hq1 x x₀ hx
    have : z₁ = sndPt k₀ (RW.lift x x) := by
      funext ⟨k, m⟩
      by_cases ek : k = k₀
      · subst ek
        rw [h3, Pts.snd_self]
      · rw [h2 ⟨k, m⟩ ek, Pts.snd_fst_ne ek]
        rfl
    exact this ▸ h1
  choose g₀ hg₀ using fun x => hsurj (Q.q 0 (e (γ x)))
  choose g₁ hg₁ using fun x => hsurj (Q.q 1 (e (γ x)))
  have i₀ : ∀ x, IsImg Cv (fstPt k₀' (R'.lift x x)) (FA.Re.R.lift (g₀ x) (g₀ x)) := fun x =>
    (hrel x).1.orbit (Cj.sameOrbit_refl _) (o₀ _ _ (hg₀ x))
  have i₁ : ∀ x, IsImg Cv (sndPt k₀' (R'.lift x x)) (FA.Re.R.lift (g₁ x) (g₁ x)) := fun x =>
    (hrel x).2.orbit (Cj.sameOrbit_refl _) (o₁ _ _ (hg₁ x))
  have mem : ∀ x, R'.lift x x ∈ mcPts _ := fun x => R'.mem x x (R'.mem_U x)
  have m₀ := fun x => fst_mem (mem x)
  have m₁ := fun x => S'.snd_mem hy' (mem x)
  have w₀ : ∀ x, CR.ϖ (fstPt k₀' (R'.lift x x)) = Q.q 0 (e (γ x)) := fun x =>
    (varpi_eq CR hy hy' (m₀ x) (i₀ x)).trans (hg₀ x)
  have w₁ : ∀ x, CR.ϖ (sndPt k₀' (R'.lift x x)) = Q.q 1 (e (γ x)) := fun x =>
    (varpi_eq CR hy hy' (m₁ x) (i₁ x)).trans (hg₁ x)
  have hπ : HoloMap R'.A Q.SW.A (e ∘ γ) := holoMap_comp hγ he
  let ReW : Realis Q.SW (mCoordIdeal (M'.wCo (τ, a) k₀' ca cb RatFunc.X)) :=
    { arith := S'.arith hy'
      J := J
      R := R'
      π := e ∘ γ
      holo := hπ
      deg := CR.Re.deg
      deg_pos := CR.Re.deg_pos
      br := br
      degree := by rw [CR.deg_eq]; exact hdegW
      ref := fun o => o.elim (pullHerm hv₁ (CR.Re.ref (τ, a))) fun p => pullHerm hv₀ (CR.Re.ref p)
      ref_smooth := fun o => by
        cases o with
        | none =>
          exact SqFirst.isSmoothHerm_of_pull hv₁ (CR.Re.ref_smooth _)
            (isPullHerm_pullHerm hv₁ _)
        | some p =>
          exact SqFirst.isSmoothHerm_of_pull hv₀ (CR.Re.ref_smooth _)
            (isPullHerm_pullHerm hv₀ _)
      ref_pot := fun o x _ => by
        cases o with
        | none =>
          have L1 := pot_pull CR hy hy' R' hv₁ (fun z hz => S'.snd_mem hy' hz) g₁ i₁ (τ, a) x
          have L2 := LocRe.comp hπ (show LocRe Q.SW.A ((e ∘ γ) x) _ from Q.th1 _ trivial)
          simp only [hg₁] at L1
          exact (L1.sub L2).congr isOpen_univ trivial fun u _ => by
            show _ - _ = _ - _ - (_ - _)
            exact (sub_sub_sub_cancel_right _ _ _).symm
        | some p =>
          have L1 := pot_pull CR hy hy' R' hv₀ (fun z hz => fst_mem hz) g₀ i₀ p x
          have L2 := LocRe.comp hπ (show LocRe Q.SW.A ((e ∘ γ) x) _ from Q.th0 p _ trivial)
          simp only [hg₀] at L1
          exact (L1.sub L2).congr isOpen_univ trivial fun u _ => by
            show _ - _ = _ - _ - (_ - _)
            exact (sub_sub_sub_cancel_right _ _ _).symm
      line := fun o t => o.elim (pullHerm hv₁ (CR.Re.line (τ, a) t)) fun p => pullHerm hv₀ (CR.Re.line p t)
      line_deg := fun o t => by
        cases o with
        | none => exact congrArg (pullDeg _) (CR.Re.line_deg _ t)
        | some p => exact congrArg (pullDeg _) (CR.Re.line_deg _ t)
      line_smooth := fun o t h0 h1 => by
        cases o with
        | none =>
          exact SqFirst.isSmoothHerm_of_pull hv₁ (CR.Re.line_smooth _ t h0 (h1.trans Q.t₀_le))
            (isPullHerm_pullHerm hv₁ _)
        | some p =>
          exact SqFirst.isSmoothHerm_of_pull hv₀ (CR.Re.line_smooth _ t h0 (h1.trans Q.t₀_le))
            (isPullHerm_pullHerm hv₀ _)
      line_eq := fun o t h0 h1 x => by
        cases o with
        | none =>
          have := CR.line_pt (τ, a) t h0 (h1.trans Q.t₀_le) _ (m₁ x)
          rw [w₁] at this
          rw [Q.phase_none_eq_comp_second_projection]
          exact this
        | some p =>
          have := CR.line_pt p t h0 (h1.trans Q.t₀_le) _ (m₀ x)
          rw [w₀] at this
          rw [Q.phase_some_eq_comp_first_projection]
          exact this }
  refine ⟨⟨k₀', Q, mkAlg M' hb hab hk' hca hcb hy' _ hxi g h dg dh hg hh hgn hhn hdeg₁ hdiv, ReW, rfl, ?_,
    fun p t => isPullHerm_pullHerm hv₀ _, fun t => isPullHerm_pullHerm hv₁ _,
    {x | eval (R'.lift x x) (map (Int.castRingHom ℂ) (g * h)) = 0}, ?_, ?_⟩⟩
  · intro p hp t
    refine ⟨by rw [CR.Re.line_deg, CR.ref_deg]; exact hdy' p hp, fun z z' hzz => CR.step p t z z' ?_ ?_⟩
    · exact funext fun q => hzz _ fun e => q.1.2 (τ, a) (hk'.trans (congrArg some e.symm))
    · exact fun k hk m => hzz _ fun e => hp (M'.blk_inj _ _ k hk (hk'.trans (congrArg some e.symm)))
  · exact HilbertSamuel.AnResNullForm.proof HilbertSamuel.NonvanishingDense.full _ _ _ _ _ R'.toAnRes (g * h) _
      (S'.arith hy') (CovMap.isMultiHomog_mul hg hh) fun hm => ((S'.arith hy').2.1.1.mem_or_mem hm).elim hgn hhn
  · intro t h0 h1 x hx
    have hx' : eval (R'.lift x x) (map (Int.castRingHom ℂ) g) * eval (R'.lift x x) (map (Int.castRingHom ℂ) h) ≠ 0 := by
      rw [← map_mul, ← map_mul]; exact hx
    have g0 := left_ne_zero_of_mul hx'
    have h0' := right_ne_zero_of_mul hx'
    obtain ⟨z₀, z₁, F, hm, s, hF, hG, oz₀, oz₁, hmb, hmd, hs, ex₀, ex₁, heq⟩ := norm_pt CR S' hy' hg hh hxi hdeg₂ LC
      (mem x) g0 h0' (fst_mem (RW.mem _ _ (RW.mem_U (γ x)))) (S.snd_mem hy (RW.mem _ _ (RW.mem_U (γ x))))
      (hrel x).1 (hrel x).2
    have hn : _ = normRhs M τ a F z₀ z₁ hm s := hnorm (γ x) z₀ z₁ F hm s hF hG
      (fun x₀ h => orbit_trans (o₀ _ _ h) (orbit_symm oz₀))
      (fun x₀ h => orbit_trans (o₁ _ _ h) (orbit_symm oz₁)) hmb hmd hs ex₀ ex₁
    show Real.log (‖eval (R'.lift x x) (map (Int.castRingHom ℂ) g)‖ / ‖eval (R'.lift x x) (map (Int.castRingHom ℂ) h)‖) +
      (Real.log ((combLine (fun p => CR.Re.line p t) (xiCoef τ a)).h (fstPt k₀' (R'.lift x x))) +
        Real.log ((combLine (fun p => CR.Re.line p t) (xiCoef τ a)).h (sndPt k₀' (R'.lift x x)))) / 2 =
      logNormSec Q.L' Q.v (e (γ x)) + Q.cst + (1 / 2) * ∑ p, (xiCoef τ a p : ℝ) *
        (FA.S.phT (some p) t (Q.q 0 (e (γ x))) + FA.S.phT (some p) t (Q.q 1 (e (γ x))))
    rw [hn, ← heq, lognorm, Real.log_div (norm_ne_zero_iff.2 g0) (norm_ne_zero_iff.2 h0'), log_comb _ _ (m₀ x).1,
      log_comb _ _ (m₁ x).1]
    simp only [fun p => CR.line_pt p t h0 (h1.trans Q.t₀_le) _ (m₀ x),
      fun p => CR.line_pt p t h0 (h1.trans Q.t₀_le) _ (m₁ x), w₀, w₁, mul_add, Finset.sum_add_distrib]
    ring
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverRealisationPullback
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.flag_cover_realisation_pullback : Inputs → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (CR : CovReal FA Cv), IsArithVar (mCoordIdeal y) (d + 2) → ∀ (τ : Ψ) (a b : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → Nonempty (SqSys CR.Re (τ, a) (xiCoef τ a)) := by
  first | exact @PositivityTheory.Xgp.t_c_sqsys | exact PositivityTheory.Xgp.t_c_sqsys
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverRealisationPullbackStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_cover_realisation_pullback : Inputs → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (CR : CovReal FA Cv), IsArithVar (mCoordIdeal y) (d + 2) → ∀ (τ : Ψ) (a b : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → Nonempty (SqSys CR.Re (τ, a) (xiCoef τ a)) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.flag_cover_realisation_pullback | exact GlobalTheory.CompanionTheory.Relay.flag_cover_realisation_pullback | (intros; apply GlobalTheory.CompanionTheory.Relay.flag_cover_realisation_pullback <;> assumption)
end
