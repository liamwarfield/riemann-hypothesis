module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsValueAtOfTorus
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HoloOnDivCongr
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorIJEqSubmatrix
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.LinearIndependentImg

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagDimensionIndexEquiv
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagDimensionIndexEquiv
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.ChartCount

theorem sum_range_eq_choose (m : ℕ) : ∑ i ∈ Finset.range m, i = m.choose 2 := by
  rw [Finset.sum_range_id, Nat.choose_two_right]

theorem card_row (N j : ℕ) (hj : j ≤ N) (a : Fin N) :
    Fintype.card {b : Fin N // b < a ∧ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)} =
      if (a : ℕ) < N - j then (a : ℕ) else (a : ℕ) - (N - j) := by
  rw [Fintype.card_subtype]
  have key : (Finset.univ.filter fun b : Fin N => b < a ∧ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)).map
      Fin.valEmbedding = Finset.Ico (if (a : ℕ) < N - j then 0 else N - j) (a : ℕ) := by
    ext x
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply, Finset.mem_Ico]
    constructor
    · rintro ⟨b, ⟨hba, hiff⟩, rfl⟩
      have hba' : (b : ℕ) < a := hba
      split_ifs with h
      · exact ⟨Nat.zero_le _, hba'⟩
      · exact ⟨Nat.le_of_not_lt (fun hb => h (hiff.mpr hb)), hba'⟩
    · rintro ⟨h1, h2⟩
      refine ⟨⟨x, lt_trans h2 a.isLt⟩, ⟨h2, ?_⟩, rfl⟩
      show (a : ℕ) < N - j ↔ x < N - j
      split_ifs at h1 with h
      · exact ⟨fun _ => lt_trans h2 h, fun _ => h⟩
      · exact ⟨fun h' => absurd h' h, fun h' => absurd h1 (Nat.not_le.mpr h')⟩
  rw [← Finset.card_map Fin.valEmbedding, key, Nat.card_Ico]
  split_ifs <;> simp

theorem card_pairs (N j : ℕ) (hj : j ≤ N) :
    Fintype.card {p : Fin N × Fin N // p.2 < p.1 ∧ ((p.1 : ℕ) < N - j ↔ (p.2 : ℕ) < N - j)} =
      j.choose 2 + (N - j).choose 2 := by
  rw [Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype
      (fun (a b : Fin N) => b < a ∧ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j))), Fintype.card_sigma]
  have h1 : ∀ a : Fin N, Fintype.card {b : Fin N // b < a ∧ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)} =
      if (a : ℕ) < N - j then (a : ℕ) else (a : ℕ) - (N - j) := card_row N j hj
  simp only [h1]
  have hs : ∑ a : Fin N, (if (a : ℕ) < N - j then (a : ℕ) else (a : ℕ) - (N - j)) =
      ∑ i ∈ Finset.range N, (if i < N - j then i else i - (N - j)) :=
    Fin.sum_univ_eq_sum_range (fun i => if i < N - j then i else i - (N - j)) N
  rw [hs]
  obtain ⟨M, rfl⟩ : ∃ M, N = M + j := ⟨N - j, by omega⟩
  have hM : M + j - j = M := by omega
  rw [hM, Finset.sum_range_add]
  have e1 : ∑ x ∈ Finset.range M, (if x < M then x else x - M) = ∑ x ∈ Finset.range M, x :=
    Finset.sum_congr rfl (fun x hx => if_pos (Finset.mem_range.mp hx))
  have e2 : ∑ x ∈ Finset.range j, (if M + x < M then M + x else M + x - M) =
      ∑ x ∈ Finset.range j, x :=
    Finset.sum_congr rfl (fun x _ => by rw [if_neg (by omega)]; omega)
  rw [e1, e2, sum_range_eq_choose, sum_range_eq_choose, add_comm]

theorem card_lowIdx (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (hj : j ≤ N) :
    Fintype.card (LowIdx Ψ N j) = Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) := by
  rw [← card_pairs N j hj, ← Fintype.card_prod]
  exact Fintype.card_congr
    { toFun := fun q => (q.1.1, ⟨q.1.2, q.2⟩)
      invFun := fun x => ⟨(x.1, x.2.1), x.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem nonempty_paramEquiv : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j n d : ℕ), j ≤ N →
    d + 1 = n + Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) →
    Nonempty (Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin (d + 2)) := by
  intro Ψ _ _ N j n d hj hd
  apply Fintype.card_eq.mp
  rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_fin, card_lowIdx Ψ N j hj,
    Fintype.card_unit, Fintype.card_fin]
  generalize Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) = t at hd ⊢
  omega

end GlobalTheory.CompanionTheory.Ar.PB.WMan.ChartCount
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagDimensionIndexEquivStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_dimension_index_equiv : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j n d : ℕ), j ≤ N → d + 1 = n + Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) → Nonempty (Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin (d + 2)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WMan.ChartCount.nonempty_paramEquiv | exact GlobalTheory.CompanionTheory.Ar.PB.WMan.ChartCount.nonempty_paramEquiv | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WMan.ChartCount.nonempty_paramEquiv <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.MaMeasureEqOfConst
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem maMeasure_eq_of_const {e : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X]
    (A : FinHolAtlas e X) (Φ Ψ : Fin e → LocPot X) (c : Fin e → ℝ)
    (h : ∀ i x y, (Ψ i).φ x y = (Φ i).φ x y + c i) : maMeasure A Ψ = maMeasure A Φ := by
  have hH : ∀ (F : (Fin e → ℂ) → ℝ) (a : ℝ) (y : Fin e → ℂ),
      hessC (fun z => F z + a) y = hessC F y := by
    intro F a y
    have h1 : fderiv ℝ (fun z => F z + a) = fderiv ℝ F := funext fun z => fderiv_add_const a
    unfold hessC
    rw [h1]
  have hD : ∀ j, locDens A Ψ j = locDens A Φ j := by
    intro j
    funext y
    unfold locDens maDens
    have hk : (fun k => hessC (fun y' => (Ψ k).φ ((A.chart j).symm y) ((A.chart j).symm y')) y) =
        fun k => hessC (fun y' => (Φ k).φ ((A.chart j).symm y) ((A.chart j).symm y')) y := by
      funext k
      simp only [h k]
      exact hH _ _ y
    rw [hk]
  unfold maMeasure
  simp only [hD]

theorem exists_pos_le_all {e : ℕ} (f : Fin e → ℝ) (hf : ∀ i, 0 < f i) (a : ℝ) (ha : 0 < a) :
    ∃ b : ℝ, 0 < b ∧ b ≤ a ∧ ∀ i, b ≤ f i := by
  have hne : (insert a (Finset.univ.image f)).Nonempty := Finset.insert_nonempty _ _
  refine ⟨_, (Finset.lt_min'_iff _ hne).2 fun x hx => ?_,
    Finset.min'_le _ _ (Finset.mem_insert_self _ _),
    fun i => Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem f (Finset.mem_univ i)))⟩
  rcases Finset.mem_insert.1 hx with rfl | hx
  · exact ha
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
    exact hf i

theorem tail_uniform : TailBoundStatement → ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (A : FinHolAtlas e X) (Θ L : LocPot X) (s : X → X → ℂ) {n : ℕ} (m : Fin n → ℕ) (W : Fin n → Set X), IsPotential A Θ → IsPosPot A Θ → IsPotential A L → IsSection A L s → IsSNC A L s m W → (∀ y, logNormSec L s y ≤ 0) → ∀ (th : Fin e → LocPot X) (ph : Fin e → X → ℝ) (phT : Fin e → ℝ → X → ℝ) (C₅ C t₀ : ℝ), (∀ i, IsSingWeight A L s (th i) (ph i) C₅) → (∀ i, IsRegFamily A Θ L s (th i) (ph i) (phT i) C t₀) → ∃ K t₁ : ℝ, 0 < t₁ ∧ (0 < t₀ → t₁ ≤ t₀) ∧ ∀ τ : Fin e → ℝ, (∀ i, 0 < τ i ∧ τ i ≤ t₁) → (∀ i, IsPotential A (th i + LocPot.ofFun (phT i (τ i)) + Θ) ∧ IsPsh A (th i + LocPot.ofFun (phT i (τ i)) + Θ)) ∧ ∀ R : ℝ, Real.exp 1 ≤ R → maMeasure A (fun i => th i + LocPot.ofFun (phT i (τ i)) + Θ) (bdry s ∪ {y | R ≤ rW L s y}) ≤ ENNReal.ofReal (K * Real.log R / R) ∧ ∫⁻ y in (bdry s)ᶜ ∩ {y | R ≤ rW L s y}, ENNReal.ofReal (Real.log (rW L s y)) ∂maMeasure A (fun i => th i + LocPot.ofFun (phT i (τ i)) + Θ) ≤ ENNReal.ofReal (K * Real.log R ^ 2 / R) := by
  intro hTB e X _ _ _ _ _ A Θ L s n m W hΘ hpos hL hS hSNC hnorm th ph phT C₅ C t₀ hW hR
  choose t₂ ht₂ ht₂₀ hfix using fun i =>
    fixedMember_base A Θ L s (th i) (ph i) (phT i) C₅ C t₀ hΘ hpos hnorm (hW i) (hR i)
  obtain ⟨a, ha, hε⟩ := epsT_small C
  obtain ⟨t₁, ht₁, ht₁a, ht₁0, ht₁2⟩ : ∃ t₁ : ℝ, 0 < t₁ ∧ t₁ ≤ a ∧ (0 < t₀ → t₁ ≤ t₀) ∧
      ∀ i, t₁ ≤ t₂ i := by
    obtain ⟨b, hb, hba, hbf⟩ := exists_pos_le_all t₂ ht₂ a ha
    by_cases h0 : 0 < t₀
    · exact ⟨min b t₀, lt_min hb h0, (min_le_left _ _).trans hba, fun _ => min_le_right _ _,
        fun i => (min_le_left _ _).trans (hbf i)⟩
    · exact ⟨b, hb, hba, fun h => absurd h h0, hbf⟩
  have hB := fun i => hfix i t₁ ht₁ (ht₁2 i)
  obtain ⟨Ct, hCt⟩ := hTB A (fun i => th i + LocPot.ofFun (phT i t₁) + Θ) L s m W
    (fun i => (hB i).1) (fun i => (hB i).2.2.1) hL hS hSNC hnorm
  have hC₁ : 0 ≤ |C₅| + |C| + 1 := by positivity
  refine ⟨Ct * (|C₅| + |C| + 1 + 3), t₁, ht₁, ht₁0, fun τ hτ => ⟨fun i => ?_, fun R hRe => ?_⟩⟩
  · have hτ0 : τ i ≤ t₀ := ((hτ i).2.trans (ht₁2 i)).trans (ht₂₀ i)
    obtain ⟨hsm, -, -, -, hpsh, -, -, -⟩ := (hR i).2.2 (τ i) (hτ i).1 hτ0
    have hth := (hW i).1
    have hεi := (abs_le.1 (hε (τ i) (hτ i).1 ((hτ i).2.trans ht₁a)).1).2
    refine ⟨isPotentialAdd A _ _ (isPotentialAdd A _ _ hth (isPotential_ofFun A _ hsm)) hΘ,
      isPsh_of_le A Θ (th i) (phT i (τ i)) hΘ hpos hth hsm (epsT C (τ i)) 1 0 (by linarith) hpsh _
        (fun x z hz => ⟨hz.1.1, hz.2⟩) (fun x z => ?_)⟩
    show (th i).φ x z + phT i (τ i) z + Θ.φ x z = _
    ring
  · have hL' := fun i => (hB i).2.2.2 (τ i) (hτ i).1 (hτ i).2
    have hm : maMeasure A (fun i => th i + LocPot.ofFun (phT i (τ i)) + Θ) =
        maMeasure A (fun i => (th i + LocPot.ofFun (phT i t₁) + Θ) +
          LocPot.ofFun (fun y => phT i (τ i) y - phT i t₁ y - C * epsT C t₁)) :=
      maMeasure_eq_of_const A _ _ (fun _ => C * epsT C t₁) fun i x y => by
        show (th i).φ x y + phT i (τ i) y + Θ.φ x y =
          (th i).φ x y + phT i t₁ y + Θ.φ x y +
            (phT i (τ i) y - phT i t₁ y - C * epsT C t₁) + C * epsT C t₁
        ring
    rw [hm]
    exact hCt (|C₅| + |C| + 1) (fun i y => phT i (τ i) y - phT i t₁ y - C * epsT C t₁) hC₁
      (fun i => (hL' i).1) (fun i => (hL' i).2.1)
      (fun i y hy => ⟨(hL' i).2.2.2 y hy, (hL' i).2.2.1 y⟩) R hRe

end GlobalTheory.CompanionTheory.Ar.Giv
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.UnipotentValueNeZero
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ValueNeZeroOfRegularUnit
noncomputable section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.ValNe

private theorem mConeMap_eq_C_aeval_mul_prod_X_pow_of_multiHomog {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {F : Type} [Field F]
    (w : (Σ k, ι k) → F) {h : MRing ι} {d : K → ℕ} (hh : IsMultiHomog h d) :
    mConeMap w h = MvPolynomial.C (MvPolynomial.aeval w h) * ∏ k, (MvPolynomial.X k : MvPolynomial K F) ^ d k := by
  have key : ∀ m ∈ h.support, (∏ p : (Σ k, ι k), (MvPolynomial.C (w p) * MvPolynomial.X p.1 : MvPolynomial K F) ^ m p)
      = MvPolynomial.C (∏ p, w p ^ m p) * ∏ k, (MvPolynomial.X k : MvPolynomial K F) ^ d k := by
    intro m hm
    simp only [mul_pow, Finset.prod_mul_distrib]
    congr 1
    · rw [map_prod]
      simp only [map_pow]
    · rw [Fintype.prod_sigma]
      refine Finset.prod_congr rfl fun k _ => ?_
      dsimp only
      rw [Finset.prod_pow_eq_pow_sum, hh m hm k]
  simp only [mConeMap, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq']
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [key m hm, map_mul, ← mul_assoc]
  congr 2

private theorem aeval_eq_eval_map_intCast {K : Type} {ι : K → Type} (w : (Σ k, ι k) → ℂ) (f : MRing ι) :
    MvPolynomial.aeval w f = MvPolynomial.eval w (MvPolynomial.map (Int.castRingHom ℂ) f) := by
  rw [MvPolynomial.eval_map, MvPolynomial.aeval_def, algebraMap_int_eq]

theorem exists_isValueAt_of_regAt {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    {x : (Σ k, ι k) → Ω} {t : Ω} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal x))
    (ht : RegAt x (mCoordIdeal z) t) : ∃ v, IsValueAt x t z v := by
  obtain ⟨d, g, h, hg, hh, hQ, he⟩ := ht
  have hz0 : MvPolynomial.eval z (MvPolynomial.map (Int.castRingHom ℂ) h) ≠ 0 := by
    intro h0
    apply hQ
    rw [mCoordIdeal, RingHom.mem_ker, mConeMap_eq_C_aeval_mul_prod_X_pow_of_multiHomog z hh, aeval_eq_eval_map_intCast, h0, map_zero, zero_mul]
  have hx0 : MvPolynomial.aeval x h ≠ 0 := by
    intro h0
    apply hz0
    exact hz.2 h (by rw [mCoordIdeal, RingHom.mem_ker, mConeMap_eq_C_aeval_mul_prod_X_pow_of_multiHomog x hh, h0, map_zero, zero_mul])
  refine ⟨MvPolynomial.eval z (MvPolynomial.map (Int.castRingHom ℂ) g) /
    MvPolynomial.eval z (MvPolynomial.map (Int.castRingHom ℂ) h), ?_⟩
  unfold IsValueAt
  exact ⟨d, g, h, hg, hh, hx0, he, hz0, rfl⟩

theorem valAt_ne_zero_of_regAt_inv : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (x : (Σ k, ι k) → Ω) (s : Ω) (z : (Σ k, ι k) → ℂ), z ∈ mcPts (mCoordIdeal x) → s ≠ 0 →
    RegAt x (mCoordIdeal z) s → RegAt x (mCoordIdeal z) s⁻¹ → valAt x s z ≠ 0 := by
  intro K _ ι _ Ω _ x s z hz hs h1 h2
  obtain ⟨v, hv⟩ := exists_isValueAt_of_regAt hz h1
  obtain ⟨w, hw⟩ := exists_isValueAt_of_regAt hz h2
  have hvw := isValueAt_mul hv hw
  rw [mul_inv_cancel₀ hs] at hvw
  have hone : IsValueAt x 1 z 1 := by
    unfold IsValueAt
    exact ⟨0, MvPolynomial.C 1, MvPolynomial.C 1, isMultiHomog_C_zero 1, isMultiHomog_C_zero 1,
      by simp, by simp, by simp, by simp⟩
  have h11 := isValueAt_unique hz hvw hone
  rw [valAt_eq hz hv]
  intro hv0
  rw [hv0, zero_mul] at h11
  exact zero_ne_one h11

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.ValNe
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.UnipotentValueNeZero
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.UpsNe

theorem upsVal_ne_zero : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n)  (l : Fin BM.q) (p : Ψ × Fin N) (b : BM.Rb.X), b ∈ BM.O l → M.blk p = none → upsVal BM l p b ≠ 0 := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM l p b hb hp
  obtain ⟨hne, hreg, hreg'⟩ := (BM.good l b hb).2.2 p hp
  exact ValNe.valAt_ne_zero_of_regAt_inv _ _ M.Ω M.x _ _ (BM.Rb.mem b b (BM.Rb.mem_U b)) hne hreg hreg'

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.UpsNe
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.UnipotentValueNeZeroStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_value_ne_zero : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n)  (l : Fin BM.q) (p : Ψ × Fin N) (b : BM.Rb.X), b ∈ BM.O l → M.blk p = none → upsVal BM l p b ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.UpsNe.upsVal_ne_zero | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.UpsNe.upsVal_ne_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.UpsNe.upsVal_ne_zero <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogBlockMetricOffBoundary
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogBlockMetricOffBoundary
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW.BaseLine

section Values

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem valAt_inv {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal x)) {s : Ω} (h0 : s ≠ 0)
    (hs : RegAt x (mCoordIdeal z) s) (hs' : RegAt x (mCoordIdeal z) s⁻¹) :
    valAt x s⁻¹ z = (valAt x s z)⁻¹ ∧ valAt x s z ≠ 0 := by
  obtain ⟨-, -, -, h1, hm⟩ := ValRing.regAt_valAt_ring K ι Ω x z hz
  have h := (hm s s⁻¹ hs hs').2.2.1
  rw [mul_inv_cancel₀ h0, h1] at h
  have hne : valAt x s z ≠ 0 := left_ne_zero_of_mul_eq_one h.symm
  exact ⟨eq_inv_of_mul_eq_one_right h.symm, hne⟩

theorem coord_ne_zero {z : (Σ k, ι k) → ℂ} {q : Σ k, ι k} (h : (X q : MRing ι) ∉ mCoordIdeal z) : z q ≠ 0 :=
  fun h0 => h (by
    show mConeMap z (X q) = 0
    rw [mConeMap, aeval_X, h0, map_zero, zero_mul])

end Values

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (l : Fin BM.q) (x₀ : BM.Rb.X) (z : (Σ k, ι k) → ℂ), M.blk p = none → x₀ ∈ BM.O l \ bdry BM.s → z ∈ mcPts (mCoordIdeal y) → SameOrbit (basePart M.blk z) (BM.Rb.lift x₀ x₀) → Real.log ((BM.hom p).h z) = blockPot j p.2 (BM.G l p.1 x₀) 1 + Real.log ‖baseMono M (BM.F l) p z * valAt M.x ((BM.F l).υ p)⁻¹ (basePart M.blk z)‖ := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM p l x₀ z hp hx hz hso
  have hgood : M.GoodAt (BM.F l) (mCoordIdeal (BM.Rb.lift x₀ x₀)) := BM.good l x₀ hx.1
  have hxb : BM.Rb.lift x₀ x₀ ∈ mcPts (mCoordIdeal M.x) := BM.Rb.mem x₀ x₀ (BM.Rb.mem_U x₀)
  obtain ⟨c, hc, hzc⟩ := id hso

  have hI : mCoordIdeal (basePart M.blk z) = mCoordIdeal (BM.Rb.lift x₀ x₀) := by
    rw [hzc]; exact TorusAct.mCoordIdeal_torus c hc _
  have hzb : basePart M.blk z ∈ mcPts (mCoordIdeal M.x) := by
    rw [hzc]
    exact ((TorusAct.main _ _ _ M.x _ c hc).2 hxb).1
  have hgood' : M.GoodAt (BM.F l) (mCoordIdeal (basePart M.blk z)) := by rw [hI]; exact hgood
  have hne : ∀ k : NonPluckerBlocks M.blk, basePart M.blk z ⟨k, (BM.F l).c k⟩ ≠ 0 := fun k => coord_ne_zero (hgood'.1 k)

  let t : K → ℂ := fun k => if h : ∀ p', M.blk p' ≠ some k then (basePart M.blk z ⟨⟨k, h⟩, (BM.F l).c ⟨k, h⟩⟩)⁻¹ else 1
  have htb : ∀ k : NonPluckerBlocks M.blk, t k.1 = (basePart M.blk z ⟨k, (BM.F l).c k⟩)⁻¹ := fun k => dif_pos k.2
  have ht1 : ∀ k, ¬ (∀ p', M.blk p' ≠ some k) → t k = 1 := fun k h => dif_neg h
  have ht : ∀ k, t k ≠ 0 := fun k => by
    by_cases h : ∀ p', M.blk p' ≠ some k
    · rw [htb ⟨k, h⟩]; exact inv_ne_zero (hne _)
    · rw [ht1 k h]; exact one_ne_zero
  let z₁ : (Σ k, ι k) → ℂ := fun q => t q.1 * z q
  have hz₁ : z₁ ∈ mcPts (mCoordIdeal y) := ((TorusAct.main _ _ _ y z t ht).2 hz).1
  have hb₁ : basePart M.blk z₁ = fun q : Σ k, baseIdx ι M.blk k => t q.1.1 * basePart M.blk z q := rfl
  have hval : valAt M.x ((BM.F l).υ p) (basePart M.blk z₁) = valAt M.x ((BM.F l).υ p) (basePart M.blk z) := by
    rw [hb₁]
    exact ((TorusAct.main _ _ _ M.x _ (fun k : NonPluckerBlocks M.blk => t k.1) fun k => ht _).2 hzb).2 _
  have hso₁ : SameOrbit (basePart M.blk z₁) (BM.Rb.lift x₀ x₀) :=
    ⟨fun k => t k.1 * c k, fun k => mul_ne_zero (ht _) (hc k), by
      rw [hb₁, hzc]; funext q; exact (mul_assoc _ _ _).symm⟩
  have hnorm : ∀ k, basePart M.blk z₁ ⟨k, (BM.F l).c k⟩ = 1 := fun k => by
    rw [hb₁]
    show t k.1 * _ = 1
    rw [htb k]
    exact inv_mul_cancel₀ (hne k)
  have hind := (BM.induced l x₀ hx p z₁ hz₁ hso₁ hnorm 1 isBlockDiag_one (by simp)).2 hp
  rw [hval] at hind

  have hscale : (BM.hom p).h z₁ = (∏ k, ‖t k‖ ^ M.dy p k) * (BM.hom p).h z := by
    have := (BM.hom p).smul t z ht
    rw [BM.hom_deg] at this
    exact this
  have hprod : (∏ k, ‖t k‖ ^ M.dy p k) = ‖baseMono M (BM.F l) p z‖⁻¹ := by
    have e := Fintype.prod_subtype_mul_prod_subtype (fun k : K => ∀ p', M.blk p' ≠ some k)
      (fun k : K => (‖t k‖ ^ M.dy p k : ℝ))
    rw [← e, Fintype.prod_eq_one (f := fun k : {k // ¬ ∀ p', M.blk p' ≠ some k} => ‖t k.1‖ ^ M.dy p k.1)
      (fun k => by rw [ht1 _ k.2]; simp), mul_one, baseMono, norm_prod, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr (by ext; simp) fun k _ => ?_
    show ‖t k.1‖ ^ M.dy p k.1 = (‖basePart M.blk z ⟨k, (BM.F l).c k⟩ ^ M.dy p k.1‖)⁻¹
    rw [htb k, norm_inv, norm_zpow, _root_.inv_zpow]

  obtain ⟨hu0, hu1, hu2⟩ := hgood'.2.2 p hp
  obtain ⟨hinv, hv0⟩ := valAt_inv hzb hu0 hu1 hu2
  have hmono : baseMono M (BM.F l) p z ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hne k)
  have hpos : 0 < (BM.hom p).h z := (BM.hom p).pos z hz.1
  rw [hscale, hprod, Real.log_mul (inv_ne_zero (norm_ne_zero_iff.2 hmono)) hpos.ne', Real.log_inv] at hind
  rw [hinv, norm_mul, norm_inv, Real.log_mul (norm_ne_zero_iff.2 hmono) (inv_ne_zero (norm_ne_zero_iff.2 hv0)),
    Real.log_inv]
  linarith

end GlobalTheory.CompanionTheory.Ar.PB.StepW.BaseLine
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogBlockMetricOffBoundaryStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_block_metric_off_boundary : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (l : Fin BM.q) (x₀ : BM.Rb.X) (z : (Σ k, ι k) → ℂ), M.blk p = none → x₀ ∈ BM.O l \ bdry BM.s → z ∈ mcPts (mCoordIdeal y) → SameOrbit (basePart M.blk z) (BM.Rb.lift x₀ x₀) → Real.log ((BM.hom p).h z) = blockPot j p.2 (BM.G l p.1 x₀) 1 + Real.log ‖baseMono M (BM.F l) p z * valAt M.x ((BM.F l).υ p)⁻¹ (basePart M.blk z)‖ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.StepW.BaseLine.main | exact GlobalTheory.CompanionTheory.Ar.PB.StepW.BaseLine.main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.StepW.BaseLine.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.OrbitChartTransitionAnalytic
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.OrbitChartTransitionAnalytic
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan

theorem exists_analyticAt_leftInverse {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F] {f : E → F} {u : E} (hf : AnalyticAt ℂ f u)
    (hk : (fderiv ℂ f u : E →ₗ[ℂ] F).ker = ⊥) :
    ∃ Λ : F → E, AnalyticAt ℂ Λ (f u) ∧ ∀ᶠ v in 𝓝 u, Λ (f v) = v := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℂ E
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hk
  let L : F →L[ℂ] E := LinearMap.toContinuousLinearMap g
  have hLf : ∀ x, L (fderiv ℂ f u x) = x := fun x => by
    have := LinearMap.congr_fun hg x
    simpa [L] using this
  let h : E → E := fun v => L (f v)
  have hh : AnalyticAt ℂ h u := (L.analyticAt (f u)).comp hf
  have hd : fderiv ℂ h u = ((ContinuousLinearEquiv.refl ℂ E : E ≃L[ℂ] E) : E →L[ℂ] E) := by
    have h1 : HasFDerivAt h (L.comp (fderiv ℂ f u)) u := L.hasFDerivAt.comp u hf.differentiableAt.hasFDerivAt
    rw [h1.fderiv]
    ext x
    simp [hLf]
  have hs : HasStrictFDerivAt h ((ContinuousLinearEquiv.refl ℂ E : E ≃L[ℂ] E) : E →L[ℂ] E) u := by
    have := hh.hasStrictFDerivAt
    rwa [hd] at this
  have hsrc : u ∈ (hs.toOpenPartialHomeomorph h).source := hs.mem_toOpenPartialHomeomorph_source
  have hcoe : ((hs.toOpenPartialHomeomorph h : OpenPartialHomeomorph E E) : E → E) = h :=
    hs.toOpenPartialHomeomorph_coe
  have han : AnalyticAt ℂ (hs.toOpenPartialHomeomorph h).symm (h u) := by
    have := (hs.toOpenPartialHomeomorph h).analyticAt_symm' (i := ContinuousLinearEquiv.refl ℂ E) hsrc
      (by rw [hcoe]; exact hh) (by rw [hcoe]; exact hd)
    rwa [hcoe] at this
  refine ⟨fun y => (hs.toOpenPartialHomeomorph h).symm (L y), ?_, ?_⟩
  · exact AnalyticAt.comp (f := fun y => L y) (g := (hs.toOpenPartialHomeomorph h).symm) han (L.analyticAt (f u))
  · filter_upwards [(hs.toOpenPartialHomeomorph h).open_source.mem_nhds hsrc] with v hv
    have := (hs.toOpenPartialHomeomorph h).left_inv hv
    rwa [hcoe] at this

section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem affCoord_congr_sameOrbit (p : (k : K) → ι k) {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    affCoord p z = affCoord p z' := by
  obtain ⟨c, hc, rfl⟩ := h
  funext q
  simp only [affCoord]
  exact mul_div_mul_left _ _ (hc q.1)

theorem OrbitChart.analyticAt_affCoord {P : Ideal (MRing ι)} {e : ℕ} (C : OrbitChart P e) {w : Fin e → ℂ}
    (hw : w ∈ C.D) (p : (k : K) → ι k) (hp : ∀ k, C.φ w ⟨k, p k⟩ ≠ 0) :
    AnalyticAt ℂ (fun w' => affCoord p (C.φ w')) w := by
  rw [analyticAt_pi_iff]
  intro q
  exact (C.holo q w hw).div (C.holo ⟨q.1, p q.1⟩ w hw) (hp q.1)

end

theorem OrbitChart.analyticOnNhd_transition (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) (e : ℕ) (C₁ C₂ : OrbitChart P e) :
    AnalyticOnNhd ℂ (fun w => C₂.ρ (C₁.φ w)) {w | w ∈ C₁.D ∧ C₁.φ w ∈ C₂.O} := by
  rintro w₀ ⟨hw₀, hO₀⟩
  obtain ⟨O', hO'o, hO'⟩ := C₂.O_open
  have hcont : ContinuousAt C₁.φ w₀ := continuousAt_pi.2 fun q => (C₁.holo q w₀ hw₀).continuousAt
  have hS : ∀ᶠ w in 𝓝 w₀, w ∈ C₁.D ∧ C₁.φ w ∈ C₂.O := by
    have h1 : ∀ᶠ w in 𝓝 w₀, w ∈ C₁.D := C₁.isOpen_D.mem_nhds hw₀
    have h2 : ∀ᶠ w in 𝓝 w₀, C₁.φ w ∈ O' :=
      hcont (hO'o.mem_nhds (by rw [hO'] at hO₀; exact hO₀.1))
    filter_upwards [h1, h2] with w a b
    exact ⟨a, by rw [hO']; exact ⟨b, C₁.mem w a⟩⟩
  have hTc : ContinuousAt (fun w => C₂.ρ (C₁.φ w)) w₀ := by
    have h1 : Tendsto C₁.φ (𝓝 w₀) (𝓝[C₂.O] (C₁.φ w₀)) :=
      tendsto_nhdsWithin_iff.2 ⟨hcont, hS.mono fun _ h => h.2⟩
    exact (C₂.ρ_cont _ hO₀).tendsto.comp h1
  choose p hp using (C₁.mem w₀ hw₀).1
  have hu₀ : C₂.ρ (C₁.φ w₀) ∈ C₂.D := C₂.ρ_mem _ hO₀
  have horb := C₂.φ_ρ _ hO₀
  have hne : ∀ k, C₂.φ (C₂.ρ (C₁.φ w₀)) ⟨k, p k⟩ ≠ 0 := by
    obtain ⟨c, hc, hz⟩ := horb
    intro k
    rw [hz]
    exact mul_ne_zero (hc k) (hp k)
  have hA₂ := C₂.analyticAt_affCoord hu₀ p hne
  have hA₁ := C₁.analyticAt_affCoord hw₀ p hp
  obtain ⟨Λ, hΛ, hΛl⟩ := exists_analyticAt_leftInverse hA₂ (C₂.immersion _ hu₀ p hne)
  have hval : affCoord p (C₂.φ (C₂.ρ (C₁.φ w₀))) = affCoord p (C₁.φ w₀) := affCoord_congr_sameOrbit p horb
  have hΛ' : AnalyticAt ℂ Λ (affCoord p (C₁.φ w₀)) := by
    have := hΛ
    simp only [hval] at this
    exact this
  have hcomp : AnalyticAt ℂ (fun w => Λ (affCoord p (C₁.φ w))) w₀ :=
    AnalyticAt.comp (f := fun w => affCoord p (C₁.φ w)) (g := Λ) hΛ' hA₁
  refine hcomp.congr ?_
  filter_upwards [hS, hTc.eventually hΛl] with w hw hl
  rw [← hl, affCoord_congr_sameOrbit p (C₂.φ_ρ _ hw.2)]

end GlobalTheory.CompanionTheory.Ar.PB.WMan
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.OrbitChartTransitionAnalyticStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbit_chart_transition_analytic : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ) (C₁ C₂ : OrbitChart P e), AnalyticOnNhd ℂ (fun w => C₂.ρ (C₁.φ w)) {w | w ∈ C₁.D ∧ C₁.φ w ∈ C₂.O} := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WMan.OrbitChart.analyticOnNhd_transition | exact GlobalTheory.CompanionTheory.Ar.PB.WMan.OrbitChart.analyticOnNhd_transition | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WMan.OrbitChart.analyticOnNhd_transition <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ElementaryFactorProperties
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ElementaryFactorProperties
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.Shear

variable {N : ℕ}

theorem shear_above {ca cb : Fin N} (hab : ca < cb) (t : ℂ) {x y : Fin N} (hxy : x < y) :
    (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) x y = 0 := by
  rw [SchurCalc.elem_apply, if_neg hxy.ne, if_neg, add_zero]
  rintro ⟨rfl, rfl⟩
  exact lt_asymm hab hxy

theorem shear_diag {ca cb : Fin N} (hab : ca < cb) (t : ℂ) (x : Fin N) :
    (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) x x = 1 := by
  rw [SchurCalc.elem_apply, if_pos rfl, if_neg, add_zero]
  rintro ⟨rfl, h⟩
  exact hab.ne h

theorem det_shear {ca cb : Fin N} (hab : ca < cb) (t : ℂ) :
    (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ).det = 1 := by
  rw [Matrix.det_of_lowerTriangular _ (fun x y h => shear_above hab t h)]
  exact Finset.prod_eq_one fun x _ => shear_diag hab t x

theorem minor_shear {ca cb : Fin N} (hab : ca < cb) (t : ℂ) (S : Finset (Fin N)) :
    minorIJ (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) S S = 1 := by
  have ht : ((1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ).submatrix (S.orderEmbOfFin rfl)
      (S.orderEmbOfFin rfl)).BlockTriangular OrderDual.toDual :=
    fun x y h => shear_above hab t ((S.orderEmbOfFin rfl).strictMono h)
  rw [MinorCalc.minorIJ_eq_det _ S S _ rfl rfl, Matrix.det_of_lowerTriangular _ ht]
  exact Finset.prod_eq_one fun x _ => shear_diag hab t _

theorem support_shear {ca cb : Fin N} (t : ℂ) {S : Finset (Fin N)} (hS : ca ∈ S → cb ∈ S) (k c : Fin N)
    (hc : c ∈ S) (hk : k ∉ S) : (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) k c = 0 := by
  have hne : k ≠ c := fun e => hk (e ▸ hc)
  rw [SchurCalc.elem_apply, if_neg hne, if_neg, add_zero]
  rintro ⟨rfl, rfl⟩
  exact hk (hS hc)

theorem minor_mul_shear {ca cb : Fin N} (hab : ca < cb) (t : ℂ) {S : Finset (Fin N)} (hS : ca ∈ S → cb ∈ S)
    (A : Matrix (Fin N) (Fin N) ℂ) (I : Finset (Fin N)) :
    minorIJ (A * (1 + Matrix.single cb ca t)) I S = minorIJ A I S := by
  rw [MinorCalc.minorIJ_mul_of_support _ _ _ _ (support_shear t hS), minor_shear hab, mul_one]

theorem minor_gram_shear {ca cb : Fin N} (hab : ca < cb) (t : ℂ) {S : Finset (Fin N)} (hS : ca ∈ S → cb ∈ S)
    (G h : Matrix (Fin N) (Fin N) ℂ) :
    minorIJ ((h * (1 + Matrix.single cb ca t))ᴴ * G * (h * (1 + Matrix.single cb ca t))) S S =
      minorIJ (hᴴ * G * h) S S := by
  obtain ⟨H, hH⟩ : ∃ H, H = hᴴ * G * h := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ : ∃ U : Matrix (Fin N) (Fin N) ℂ, U = 1 + Matrix.single cb ca t := ⟨_, rfl⟩
  have e : (h * U)ᴴ * G * (h * U) = (Uᴴ * H) * U := by
    rw [hH]
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  rw [← hU, ← hH, e, hU, minor_mul_shear hab t hS, ← hU]
  apply star_injective
  rw [← SchurCalc.minor_conjTranspose, ← SchurCalc.minor_conjTranspose, conjTranspose_mul,
    conjTranspose_conjTranspose, hU, minor_mul_shear hab t hS]

theorem shear_main : ∀ (N j : ℕ) (a b ca cb : Fin N) (t : ℂ), j ≤ N → (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → IsBlockDiag j (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) ∧ (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ).det = 1 ∧ (∀ h : Matrix (Fin N) (Fin N) ℂ, ∀ i, facOf N j a (h * (1 + Matrix.single cb ca t)) i = facOf N j a h i) ∧ ∀ G h : Matrix (Fin N) (Fin N) ℂ, ∀ i, i ≠ a → blockPot j i G (h * (1 + Matrix.single cb ca t)) = blockPot j i G h := by
  intro N j a b ca cb t hj hb hcase hca hcb
  have hab : ca < cb := Fin.lt_def.2 (by omega)
  have ha2 := a.2
  have hb2 := b.2
  have hcb2 := cb.2
  unfold lastCol at hca
  have hblock : (ca : ℕ) < N - j ↔ (cb : ℕ) < N - j := by
    rcases hcase with h | h
    · rw [if_pos (by omega)] at hca
      omega
    · rw [if_neg (by omega)] at hca
      omega
  have hw : ca ∈ wIdx N j → cb ∈ wIdx N j := by
    simp only [wIdx, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have ho : ca ∈ omIdx N j → cb ∈ omIdx N j := by
    simp only [omIdx, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hstep : ∀ i : Fin N, i ≠ a → ca ∈ stepCols N j i → cb ∈ stepCols N j i := by
    intro i hi
    have hia : (i : ℕ) ≠ a := fun e => hi (Fin.ext e)
    have hi2 := i.2
    simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hcase with h | h
    · rw [if_pos (by omega)] at hca
      split_ifs <;> omega
    · rw [if_neg (by omega)] at hca
      split_ifs <;> omega
  refine ⟨?_, det_shear hab t, ?_, ?_⟩
  · intro p q hpq
    rw [SchurCalc.elem_apply, if_neg (fun e => hpq (by rw [e])), if_neg, add_zero]
    rintro ⟨rfl, rfl⟩
    exact hpq hblock.symm
  · intro h i
    unfold facOf
    rw [minor_mul_shear hab t hw, minor_mul_shear hab t ho]
  · intro G h i hi
    unfold blockPot
    rw [minor_gram_shear hab t (hstep i hi)]

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.Shear
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ElementaryFactorPropertiesStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.elementary_factor_properties : ∀ (N j : ℕ) (a b ca cb : Fin N) (t : ℂ), j ≤ N → (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → IsBlockDiag j (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) ∧ (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ).det = 1 ∧ (∀ h : Matrix (Fin N) (Fin N) ℂ, ∀ i, facOf N j a (h * (1 + Matrix.single cb ca t)) i = facOf N j a h i) ∧ ∀ G h : Matrix (Fin N) (Fin N) ℂ, ∀ i, i ≠ a → blockPot j i G (h * (1 + Matrix.single cb ca t)) = blockPot j i G h := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.Shear.shear_main | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.Shear.shear_main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.Shear.shear_main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.AdaptedFamilyExistsOnEigenspace
section -- merged from Development.WeilBound.CoreStatements.PlurisubharmonicCones.OrthogonalFamilyAdaptedBasis
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights

namespace LevelTowerAlt

theorem exists_isOFamily {E L V : Type} [Field E] [NumberField E] [Field L] [CharZero L] [AddCommGroup V] [Module L V]
    (ρ : 𝓞 E →+* Module.End L V) (I : AddSubgroup V) (hst : ∀ a, ∀ x ∈ I, ρ a x ∈ I) {n : ℕ} (e : Fin n → V)
    (he : AddSubgroup.closure (Set.range e) = I) : ∃ (r : ℕ) (v : Fin r → V), IsOFamily ρ I v := by
  letI : Module (𝓞 E) V := Module.compHom V ρ
  have hρ : ∀ (a : 𝓞 E) (x : V), a • x = ρ a x := fun _ _ => rfl
  let N : Submodule (𝓞 E) V := Submodule.span (𝓞 E) (Set.range e)
  let N' : Submodule (𝓞 E) V := { I.toAddSubmonoid with smul_mem' := fun a x hx => hst a x hx }
  have hN : N.toAddSubgroup = I := by
    refine le_antisymm (fun x hx => ?_) ?_
    · have : N ≤ N' := Submodule.span_le.2 fun y hy => by
        change y ∈ I
        rw [← he]
        exact AddSubgroup.subset_closure hy
      exact this hx
    · rw [← he, AddSubgroup.closure_le]
      exact Submodule.subset_span
  haveI : Module.Finite (𝓞 E) N := Module.Finite.span_of_finite _ (Set.finite_range e)
  obtain ⟨y, hy⟩ := exists_linearIndependent_fin (K := E) (E := N)
  have hfin := finite_quotient_span hy (Fintype.card_fin _)
  refine ⟨_, fun i => (y i : V), fun i => ?_, fun a ha => ?_, ?_⟩
  · rw [← hN]
    exact (y i).2
  · funext i
    refine Fintype.linearIndependent_iff.1 hy a (Subtype.ext ?_) i
    simpa [hρ] using ha
  · have h1 : oSpan ρ (fun i => (y i : V)) =
        ((Submodule.span (𝓞 E) (Set.range y)).map N.subtype).toAddSubgroup := by
      ext x
      rw [TorPart.mem_oSpan_iff, Submodule.map_span, ← Set.range_comp, Submodule.mem_toAddSubgroup,
        Submodule.mem_span_range_iff_exists_fun]
      exact exists_congr fun c => eq_comm
    have h2 : ((Submodule.span (𝓞 E) (Set.range y)).map N.subtype).toAddSubgroup.relIndex N.toAddSubgroup =
        Nat.card (N ⧸ ((Submodule.span (𝓞 E) (Set.range y)).map N.subtype).comap N.subtype) := rfl
    rw [h1, ← hN, h2, Submodule.comap_map_eq_of_injective N.injective_subtype]
    exact Nat.card_pos.ne'

theorem exists_append {L V : Type} [Field L] [AddCommGroup V] [Module L V] [Module.Finite L V] {r : ℕ} {w : Fin r → V}
    (hw : LinearIndependent L w) (S : Set V) :
    ∃ (k : ℕ) (q : Fin k → V), (∀ c, q c ∈ S) ∧ LinearIndependent L (Fin.append w q) ∧
      S ⊆ Submodule.span L (Set.range (Fin.append w q)) := by
  set W := Submodule.span L (Set.range w) with hW
  obtain ⟨κ, a, -, hsp, hli⟩ := exists_linearIndependent' L (fun x : S => W.mkQ (x : V))
  haveI : Finite κ := hli.finite
  obtain ⟨k, ⟨e⟩⟩ := Finite.exists_equiv_fin κ
  refine ⟨k, fun c => (a (e.symm c) : V), fun c => (a _).2, ?_, fun x hx => ?_⟩
  · have h1 : LinearIndependent L fun i => (⟨w i, Submodule.subset_span ⟨i, rfl⟩⟩ : W) :=
      LinearIndependent.of_comp W.subtype hw
    have h2 := h1.sumElim_of_quotient (fun c => (a (e.symm c) : V)) (hli.comp e.symm e.symm.injective)
    have h3 := h2.comp finSumFinEquiv.symm finSumFinEquiv.symm.injective
    have h4 : Fin.append w (fun c => (a (e.symm c) : V)) =
        Sum.elim w (fun c => (a (e.symm c) : V)) ∘ finSumFinEquiv.symm := by
      funext i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp
    rw [h4]
    exact h3
  · have h1 : W.mkQ x ∈ Submodule.span L (Set.range ((fun x : S => W.mkQ (x : V)) ∘ a)) := by
      rw [hsp]
      exact Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩
    have h2 : Set.range ((fun x : S => W.mkQ (x : V)) ∘ a) = W.mkQ '' Set.range fun c => (a (e.symm c) : V) := by
      rw [← Set.range_comp, ← e.symm.surjective.range_comp]
      rfl
    rw [h2, ← Submodule.map_span, ← Submodule.mem_comap, Submodule.comap_map_mkQ] at h1
    rw [range_append, Submodule.span_union]
    exact h1

theorem orthogonal_family_adapted_basis : ∀ (E L Ψ : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Fintype Ψ] (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (A : LinPt E L Ψ V), 2 * Fintype.card Ψ = Module.finrank ℚ E → (∃ (r : ℕ) (v : Fin r → V), IsOFamily A.ρ A.I v) ∧ ∀ (r : ℕ) (v : Fin r → V), IsOFamily A.ρ A.I v → ∀ s, ∃ (k : ℕ) (q : Fin k → A.Λ), (∀ c, (q c : V) ∈ A.eig s) ∧ A.IsAdapted s v q ∧ r + k = Module.finrank L (eigSp A.ρ (A.σ s)) ∧ A.Bq.rank (A.img s) = k ∧ ∀ ι, 0 < A.gramDet ι q := by
  intro E L Ψ _ _ _ _ _ V _ _ _ _ A hΨ
  refine ⟨?_, fun r v hv s => ?_⟩
  · obtain ⟨n, e, -, he⟩ := A.I_basis
    exact exists_isOFamily A.ρ A.I A.I_stable e he
  haveI : Module.Finite L V := by
    obtain ⟨S, hS⟩ := A.fg
    refine ⟨S, ?_⟩
    rw [← A.span, ← hS, Submodule.span_span_of_tower]
  obtain ⟨h1, h2, h3, h4⟩ := tor_facts A hΨ hv s
  obtain ⟨k, q, hq, hli, hsp⟩ := exists_append h1 (A.eig s : Set V)
  have had : A.IsAdapted s v fun c => ⟨q c, (hq c).1⟩ := by
    refine ⟨hli, le_antisymm ?_ fun x hx => ?_⟩
    · rw [LinPt.fam, range_append, Submodule.span_le]
      rintro _ (⟨a, rfl⟩ | ⟨c, rfl⟩)
      · exact h2 a
      · exact (hq c).2
    · obtain ⟨c, hc, h5⟩ := exists_smul_mem_eig A s hx
      have hcL : algebraMap (𝓞 L) L c ≠ 0 := by
        rw [map_ne_zero_iff _ (IsFractionRing.injective (𝓞 L) L)]
        exact hc
      have h6 := hsp h5
      rw [← algebraMap_smul L c] at h6
      exact (Submodule.smul_mem_iff _ hcL).1 h6
  obtain ⟨h5, h6⟩ := sub_eig A had.2
  have h7 := relIndex_ne_zero had.1 h5 h6 h5
  rw [LinPt.fam, (index_split A had.1 h3 h4 hq).1] at h7
  have h8 := linearIndependent_img A had.1 h4 hq
  refine ⟨k, _, hq, had, ?_, (rank_img A h8 hq (right_ne_zero_of_mul h7)).1, fun ι => ?_⟩
  · rw [← had.2, finrank_span_eq_card had.1, Fintype.card_fin]
  · rw [gramDet_eq]
    exact gramDet_pos _ _ h8

end LevelTowerAlt
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.AdaptedFamilyExistsOnEigenspace
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.adapted_family_exists_on_eigenspace : ∀ (E L Ψ : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Fintype Ψ] (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (A : LinPt E L Ψ V), 2 * Fintype.card Ψ = Module.finrank ℚ E → (∃ (r : ℕ) (v : Fin r → V), IsOFamily A.ρ A.I v) ∧ ∀ (r : ℕ) (v : Fin r → V), IsOFamily A.ρ A.I v → ∀ s, ∃ (k : ℕ) (q : Fin k → A.Λ), (∀ c, (q c : V) ∈ A.eig s) ∧ A.IsAdapted s v q ∧ r + k = Module.finrank L (eigSp A.ρ (A.σ s)) ∧ A.Bq.rank (A.img s) = k ∧ ∀ ι, 0 < A.gramDet ι q := by
  first | exact @LevelTowerAlt.orthogonal_family_adapted_basis | exact LevelTowerAlt.orthogonal_family_adapted_basis
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.AdaptedFamilyExistsOnEigenspaceStatement
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adapted_family_exists_on_eigenspace : ∀ (E L Ψ : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Fintype Ψ] (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (A : LinPt E L Ψ V), 2 * Fintype.card Ψ = Module.finrank ℚ E → (∃ (r : ℕ) (v : Fin r → V), IsOFamily A.ρ A.I v) ∧ ∀ (r : ℕ) (v : Fin r → V), IsOFamily A.ρ A.I v → ∀ s, ∃ (k : ℕ) (q : Fin k → A.Λ), (∀ c, (q c : V) ∈ A.eig s) ∧ A.IsAdapted s v q ∧ r + k = Module.finrank L (eigSp A.ρ (A.σ s)) ∧ A.Bq.rank (A.img s) = k ∧ ∀ ι, 0 < A.gramDet ι q := by
  first | exact @GlobalTheory.CompanionTheory.Relay.adapted_family_exists_on_eigenspace | exact GlobalTheory.CompanionTheory.Relay.adapted_family_exists_on_eigenspace | (intros; apply GlobalTheory.CompanionTheory.Relay.adapted_family_exists_on_eigenspace <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LabelledDegreeEqLogIndex
section -- merged from Development.WeilBound.CoreStatements.PlurisubharmonicCones.LabelDegreeLogIndex
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights

theorem LevelTowerAlt.label_degree_log_index : ∀ (E L Ψ : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Fintype Ψ] (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (A : LinPt E L Ψ V) (r k : ℕ) (v : Fin r → V) (s : Ψ ⊕ Ψ) (q : Fin k → A.Λ), 2 * Fintype.card Ψ = Module.finrank ℚ E → IsOFamily A.ρ A.I v → (∀ c, (q c : V) ∈ A.eig s) → A.IsAdapted s v q → A.labDeg s (A.eig s) v q = logIdx (A.tor s) (fun a => eigComp A.ρ (A.σ s) (v a)) / Module.finrank ℚ L + A.Bq.normDegree (A.img s) := by
  intro E L Ψ _ _ _ _ _ V _ _ _ _ A r k v s q hΨ hv hq had
  obtain ⟨-, -, h3, h4⟩ := LevelTowerAlt.tor_facts A hΨ hv s
  obtain ⟨h5, h6⟩ := LevelTowerAlt.sub_eig A had.2
  have h7 := LevelTowerAlt.relIndex_ne_zero had.1 h5 h6 h5
  obtain ⟨e1, e2⟩ := LevelTowerAlt.index_split A had.1 h3 h4 hq
  rw [LinPt.fam, e1] at h7
  have h8 := (LevelTowerAlt.rank_img A (LevelTowerAlt.linearIndependent_img A had.1 h4 hq) hq (right_ne_zero_of_mul h7)).2
  rw [LinPt.labDeg, HermitianBundle.normDegree, h8, logIdx, logIdx, LinPt.fam, e1, e2, Nat.cast_mul,
    Real.log_mul (Nat.cast_ne_zero.2 (left_ne_zero_of_mul h7)) (Nat.cast_ne_zero.2 (right_ne_zero_of_mul h7))]
  ring
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LabelledDegreeEqLogIndex
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.labelled_degree_eq_log_index : ∀ (E L Ψ : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Fintype Ψ] (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (A : LinPt E L Ψ V) (r k : ℕ) (v : Fin r → V) (s : Ψ ⊕ Ψ) (q : Fin k → A.Λ), 2 * Fintype.card Ψ = Module.finrank ℚ E → IsOFamily A.ρ A.I v → (∀ c, (q c : V) ∈ A.eig s) → A.IsAdapted s v q → A.labDeg s (A.eig s) v q = logIdx (A.tor s) (fun a => eigComp A.ρ (A.σ s) (v a)) / Module.finrank ℚ L + A.Bq.normDegree (A.img s) := by
  first | exact @LevelTowerAlt.label_degree_log_index | exact LevelTowerAlt.label_degree_log_index
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LabelledDegreeEqLogIndexStatement
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.labelled_degree_eq_log_index : ∀ (E L Ψ : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Fintype Ψ] (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (A : LinPt E L Ψ V) (r k : ℕ) (v : Fin r → V) (s : Ψ ⊕ Ψ) (q : Fin k → A.Λ), 2 * Fintype.card Ψ = Module.finrank ℚ E → IsOFamily A.ρ A.I v → (∀ c, (q c : V) ∈ A.eig s) → A.IsAdapted s v q → A.labDeg s (A.eig s) v q = logIdx (A.tor s) (fun a => eigComp A.ρ (A.σ s) (v a)) / Module.finrank ℚ L + A.Bq.normDegree (A.img s) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.labelled_degree_eq_log_index | exact GlobalTheory.CompanionTheory.Relay.labelled_degree_eq_log_index | (intros; apply GlobalTheory.CompanionTheory.Relay.labelled_degree_eq_log_index <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoPointFibreChartSecond
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoPointFibreChartSecond
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem gramPlane_posDef : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (X : Type) (q : Fin 2 → X → FA.S.X) (Un : Set (Fin d → ℂ)) (Gn : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (ΦYn : (Fin (d + 1) → ℂ) → FA.S.X) (ΦWn : (Fin (d + 2) → ℂ) → X) (l : Fin BM.q) (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (bp : (Fin d → ℂ) → BM.Rb.X), IsOpen Un → IsFibreData FA τ a ca cb q Un Gn ΦYn ΦWn l H bp → ∀ w ∈ Un, (Gn w).PosDef := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA τ a b ca cb hb hab hca hcb X q Un Gn ΦYn ΦWn l H bp _ hF w hw
  unfold IsFibreData at hF
  obtain ⟨-, -, -, h4, h5, -, -⟩ := hF
  obtain ⟨hbp, hH⟩ := h4 w hw
  obtain ⟨hGbd, hGpd⟩ := BM.G_pos l τ (bp w) hbp
  obtain ⟨G₂, hG₂, hG₂eq, -⟩ := GlobalTheory.CompanionTheory.Ar.PB.norm_three_steps N j a b ca cb (BM.G l τ (bp w)) (H τ w)
    M.j_le hb hab hca hcb hGbd hGpd (hH τ).1 (hH τ).2
  have hEq : Gn w = G₂ := Matrix.ext fun r s => by rw [h5 w hw r s, hG₂eq r s]
  rw [hEq]
  exact hG₂

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoPointFibreChartSecondStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_point_fibre_chart_second : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (X : Type) (q : Fin 2 → X → FA.S.X) (Un : Set (Fin d → ℂ)) (Gn : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (ΦYn : (Fin (d + 1) → ℂ) → FA.S.X) (ΦWn : (Fin (d + 2) → ℂ) → X) (l : Fin BM.q) (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (bp : (Fin d → ℂ) → BM.Rb.X), IsOpen Un → IsFibreData FA τ a ca cb q Un Gn ΦYn ΦWn l H bp → ∀ w ∈ Un, (Gn w).PosDef := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.gramPlane_posDef | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.gramPlane_posDef | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.gramPlane_posDef <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.StepFactorNeZero
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.StepFactorNeZero
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem minor_ne_zero_of_support {N : ℕ} {h : Matrix (Fin N) (Fin N) ℂ} (hd : h.det ≠ 0) {I : Finset (Fin N)}
    (hs : ∀ k c, c ∈ I → k ∉ I → h k c = 0) : minorIJ h I I ≠ 0 := by
  have hu : IsUnit h := (Matrix.isUnit_iff_isUnit_det h).2 (isUnit_iff_ne_zero.2 hd)
  have hH : (hᴴ * (1 : Matrix (Fin N) (Fin N) ℂ) * h).PosDef := by
    rw [Matrix.mul_one]
    exact Matrix.PosDef.conjTranspose_mul_self h (Matrix.mulVec_injective_of_isUnit hu)
  have hq := SchurCalc.minor_pos hH I
  rw [SchurCalc.minor_gram (G := 1) (fun k c hc hk => Matrix.one_apply_ne (fun e => hk (e ▸ hc))) hs] at hq
  intro e
  simp [e] at hq

theorem facOf_ne_zero (N j : ℕ) (a i : Fin N) (h : Matrix (Fin N) (Fin N) ℂ) (hh : IsBlockDiag j h)
    (hd : h.det ≠ 0) : facOf N j a h i ≠ 0 := by
  unfold facOf
  split_ifs
  · exact minor_ne_zero_of_support hd (MinorCalc.support_wIdx hh)
  · exact one_ne_zero
  · exact minor_ne_zero_of_support hd (MinorCalc.support_omIdx hh)

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.StepFactorNeZeroStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.step_factor_ne_zero : ∀ (N j : ℕ) (a i : Fin N) (h : Matrix (Fin N) (Fin N) ℂ), IsBlockDiag j h → h.det ≠ 0 → facOf N j a h i ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.facOf_ne_zero | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.facOf_ne_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.facOf_ne_zero <;> assumption)
end
end
