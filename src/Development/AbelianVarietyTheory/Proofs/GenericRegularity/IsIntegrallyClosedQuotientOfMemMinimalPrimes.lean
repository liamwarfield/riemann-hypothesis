module

public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TheoremA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.DimensionQuotientBound
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Hadamard

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsIntegrallyClosedQuotientOfMemMinimalPrimes
namespace GlobalTheory

theorem exists_mul_eq_zero_of_mem_minimalPrimes_of_isDomain_atPrime {S : Type*} [CommRing S]
    {q : Ideal S} (hq : q ∈ minimalPrimes S) (m : Ideal S) [m.IsPrime] (hqm : q ≤ m)
    [IsDomain (Localization.AtPrime m)] {x : S} (hx : x ∈ q) :
    ∃ s : m.primeCompl, (s : S) * x = 0 := by
  have hPq : (⊥ : Ideal (Localization.AtPrime m)).comap (algebraMap S _) ≤ q := by
    intro y hy
    have hy0 : algebraMap S (Localization.AtPrime m) y = 0 := hy
    obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff m.primeCompl _ y).1 hy0
    have hsy : (s : S) * y ∈ q := by
      rw [hs]
      exact q.zero_mem
    have hsq : (s : S) ∉ q := fun h => s.2 (hqm h)
    exact (hq.1.1.mem_or_mem hsy).resolve_left hsq
  have hqP : q ≤ (⊥ : Ideal (Localization.AtPrime m)).comap (algebraMap S _) :=
    hq.2 ⟨Ideal.comap_isPrime _ _, bot_le⟩ hPq
  have hx0 : algebraMap S (Localization.AtPrime m) x = 0 := hqP hx
  exact (IsLocalization.map_eq_zero_iff m.primeCompl _ x).1 hx0

theorem isIntegrallyClosed_quotient_of_mem_minimalPrimes {S : Type*} [CommRing S]
    (hS : ∀ (m : Ideal S) [m.IsPrime],
      IsDomain (Localization.AtPrime m) ∧ IsIntegrallyClosed (Localization.AtPrime m))
    {q : Ideal S} (hq : q ∈ minimalPrimes S) : IsIntegrallyClosed (S ⧸ q) := by
  have : q.IsPrime := hq.1.1
  refine IsIntegrallyClosed.of_localization_maximal (fun M _ _ => ?_)
  let m : Ideal S := M.comap (Ideal.Quotient.mk q)
  have : m.IsPrime := Ideal.comap_isPrime _ _
  have hqm : q ≤ m := by
    intro x hx
    show Ideal.Quotient.mk q x ∈ M
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hx]
    exact M.zero_mem
  obtain ⟨hdom, hic⟩ := hS m
  have hker : ∀ x ∈ q, algebraMap S (Localization.AtPrime m) x = 0 := by
    intro x hx
    obtain ⟨s, hs⟩ := exists_mul_eq_zero_of_mem_minimalPrimes_of_isDomain_atPrime hq m hqm hx
    exact (IsLocalization.map_eq_zero_iff m.primeCompl _ x).2 ⟨s, hs⟩
  let : Algebra (S ⧸ q) (Localization.AtPrime m) :=
    (Ideal.Quotient.lift q (algebraMap S (Localization.AtPrime m)) hker).toAlgebra
  have hmk : ∀ a : S, algebraMap (S ⧸ q) (Localization.AtPrime m) (Ideal.Quotient.mk q a) =
      algebraMap S (Localization.AtPrime m) a := fun a => Ideal.Quotient.lift_mk _ _ _
  have : IsLocalization M.primeCompl (Localization.AtPrime m) := by
    refine (isLocalization_iff _ _).2 ⟨?_, ?_, ?_⟩
    · rintro ⟨y, hy⟩
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
      show IsUnit (algebraMap (S ⧸ q) (Localization.AtPrime m) (Ideal.Quotient.mk q s))
      rw [hmk]
      exact IsLocalization.map_units (Localization.AtPrime m) (⟨s, hy⟩ : m.primeCompl)
    · intro z
      obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj m.primeCompl z
      refine ⟨⟨Ideal.Quotient.mk q a, ⟨Ideal.Quotient.mk q s, s.2⟩⟩, ?_⟩
      show z * algebraMap (S ⧸ q) _ (Ideal.Quotient.mk q s) =
        algebraMap (S ⧸ q) _ (Ideal.Quotient.mk q a)
      rw [hmk, hmk]
      exact h
    · intro a b hab
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
      rw [hmk, hmk] at hab
      obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists m.primeCompl _).1 hab
      refine ⟨⟨Ideal.Quotient.mk q c, c.2⟩, ?_⟩
      show Ideal.Quotient.mk q c * Ideal.Quotient.mk q a =
        Ideal.Quotient.mk q c * Ideal.Quotient.mk q b
      rw [← map_mul, ← map_mul, hc]
  exact hic.of_equiv (IsLocalization.algEquiv M.primeCompl (Localization.AtPrime M)
    (Localization.AtPrime m)).toRingEquiv.symm

theorem isIntegrallyClosed_quotient_minimalPrime_of_smooth :
    ∀ (F S : Type) [Field F] [CommRing S] [Algebra F S] [Algebra.Smooth F S] (q : Ideal S),
      q ∈ minimalPrimes S → IsIntegrallyClosed (S ⧸ q) := by
  intro F S _ _ _ _ q hq
  refine isIntegrallyClosed_quotient_of_mem_minimalPrimes (fun m _ => ?_) hq
  exact isDomain_and_isIntegrallyClosed_atPrime_of_smooth F m (Localization.AtPrime m)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.PeriodCoordinatesFramesLiftTendsto
section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.PeriodCoordinatesFramesLiftTendsto
open NumberField Topology Filter ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix

namespace GlobalTheory.PeriodLift

theorem exists_matrix_lift {r : ℕ} {ι : Type} {𝓕 : Filter ι} (p : Fin r → Prop) [DecidablePred p]
    (A₀ : Matrix (Fin r) (Fin r) ℂ) (A : ι → Matrix (Fin r) (Fin r) ℂ)
    (h0 : A₀.det ≠ 0) (hA : ∀ᶠ n in 𝓕, (A n).det ≠ 0)
    (hc : ∀ a, p a → ∀ k, Tendsto (fun n => A n k a) 𝓕 (𝓝 (A₀ k a)))
    (hr : ∀ a, ¬ p a → ∀ k, Tendsto (fun n => (A n)⁻¹ a k) 𝓕 (𝓝 (A₀⁻¹ a k))) :
    ∃ B : ι → Matrix (Fin r) (Fin r) ℂ, Tendsto B 𝓕 (𝓝 A₀) ∧ ∀ᶠ n in 𝓕,
      (∀ a, p a → ∀ k, B n k a = A n k a) ∧ (∀ a, ¬ p a → ∀ k, (B n)⁻¹ a k = (A n)⁻¹ a k) := by
  set Q : ι → Matrix (Fin r) (Fin r) ℂ :=
    fun n => Matrix.of fun k a => if p a then A n k a else A₀ k a with hQdef
  set D : ι → Matrix (Fin r) (Fin r) ℂ :=
    fun n => Matrix.of fun a j =>
      if p a then (1 : Matrix (Fin r) (Fin r) ℂ) a j else ((A n)⁻¹ * Q n) a j with hDdef
  have hQe : ∀ k a, Tendsto (fun n => Q n k a) 𝓕 (𝓝 (A₀ k a)) := by
    intro k a
    by_cases h : p a
    · simpa [hQdef, h] using hc a h k
    · simpa [hQdef, h] using tendsto_const_nhds
  have hQ : Tendsto Q 𝓕 (𝓝 A₀) :=
    tendsto_pi_nhds.2 fun k => tendsto_pi_nhds.2 fun a => hQe k a
  have hD : Tendsto D 𝓕 (𝓝 1) := by
    refine tendsto_pi_nhds.2 fun a => tendsto_pi_nhds.2 fun j => ?_
    by_cases h : p a
    · simpa [hDdef, h] using tendsto_const_nhds
    · have e : (1 : Matrix (Fin r) (Fin r) ℂ) a j = ∑ k, A₀⁻¹ a k * A₀ k j := by
        rw [← Matrix.mul_apply, Matrix.nonsing_inv_mul _ (Ne.isUnit h0)]
      rw [e]
      simp only [hDdef, Matrix.of_apply, h, if_false, Matrix.mul_apply]
      exact tendsto_finsetSum _ fun k _ => (hr a h k).mul (hQe k j)
  have hdet : Continuous fun M : Matrix (Fin r) (Fin r) ℂ => M.det := continuous_id.matrix_det
  have hDi : Tendsto (fun n => (D n)⁻¹) 𝓕 (𝓝 1) := by
    have hc1 : ContinuousAt Inv.inv (1 : Matrix (Fin r) (Fin r) ℂ) := by
      apply continuousAt_matrix_inv
      rw [Matrix.det_one, Ring.inverse_eq_inv']
      exact continuousAt_inv₀ one_ne_zero
    have := hc1.tendsto.comp hD
    simpa [Function.comp_def] using this
  have hQd : ∀ᶠ n in 𝓕, (Q n).det ≠ 0 := ((hdet.tendsto _).comp hQ).eventually_ne h0
  have hDd : ∀ᶠ n in 𝓕, (D n).det ≠ 0 :=
    ((hdet.tendsto _).comp hD).eventually_ne (by simp)
  refine ⟨fun n => Q n * (D n)⁻¹, by simpa using hQ.mul hDi, ?_⟩
  filter_upwards [hA, hQd, hDd] with n hAn hQn hDn
  constructor
  · intro j hj k
    have hDj : ∀ i, D n i j = (1 : Matrix (Fin r) (Fin r) ℂ) i j := by
      intro i
      by_cases h : p i
      · simp [hDdef, h]
      · rw [← Matrix.nonsing_inv_mul _ (Ne.isUnit hAn)]
        simp [hDdef, hQdef, h, hj, Matrix.mul_apply]
    have e : (Q n * (D n)⁻¹ * D n) k j = (Q n * (D n)⁻¹ * (1 : Matrix (Fin r) (Fin r) ℂ)) k j := by
      rw [Matrix.mul_apply, Matrix.mul_apply]
      simp only [hDj]
    rw [Matrix.mul_one, Matrix.nonsing_inv_mul_cancel_right _ _ (Ne.isUnit hDn)] at e
    rw [← e]
    simp [hQdef, hj]
  · intro a ha k
    rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (Ne.isUnit hDn)]
    have e : ((A n)⁻¹ * Q n * (Q n)⁻¹) a k = (A n)⁻¹ a k := by
      rw [Matrix.mul_nonsing_inv_cancel_right _ _ (Ne.isUnit hQn)]
    rw [← e, Matrix.mul_apply, Matrix.mul_apply]
    simp [hDdef, ha]

theorem tendsto_of_span {E : Type} [Field E] {r : ℕ} {ι : Type} {𝓕 : Filter ι}
    (S : Set (Fin r → E)) (hS : Submodule.span E S = ⊤) (σ : E → ℂ)
    (Φ : ι → (Fin r → E) → ℂ) (Φ₀ : (Fin r → E) → ℂ)
    (ha : ∀ n v w, Φ n (v + w) = Φ n v + Φ n w) (ha₀ : ∀ v w, Φ₀ (v + w) = Φ₀ v + Φ₀ w)
    (hs : ∀ n (c : E) v, Φ n (c • v) = σ c * Φ n v) (hs₀ : ∀ (c : E) v, Φ₀ (c • v) = σ c * Φ₀ v)
    (hσ : σ 0 = 0)
    (h : ∀ v ∈ S, Tendsto (fun n => Φ n v) 𝓕 (𝓝 (Φ₀ v))) (v : Fin r → E) :
    Tendsto (fun n => Φ n v) 𝓕 (𝓝 (Φ₀ v)) := by
  have hv : v ∈ Submodule.span E S := hS ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero =>
    have e : (0 : Fin r → E) = (0 : E) • (0 : Fin r → E) := by simp
    rw [e]
    simp only [hs, hs₀, hσ, zero_mul]
    exact tendsto_const_nhds
  | add x y _ _ hx hy => simpa only [ha, ha₀] using hx.add hy
  | smul c x _ hx => simpa only [hs, hs₀] using hx.const_mul (σ c)

theorem hermC_emb_inv_col {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (hG : G.det ≠ 0) (u : Fin r → ℂ) (k : Fin r) :
    hermC τ G u (Data.emb τ fun b => cc (G⁻¹ b k)) = u k := by
  have e : ∀ a, ∑ b, u a * τ (G a b) * (starRingEnd ℂ) (τ (cc (G⁻¹ b k))) =
      u a * τ ((G * G⁻¹) a k) := by
    intro a
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Matrix.mul_apply, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [cc, IsCMField.complexEmbedding_complexConj, Complex.conj_conj, map_mul, mul_assoc]
  simp only [hermC, Data.emb, e]
  rw [Matrix.mul_nonsing_inv _ (Ne.isUnit hG)]
  simp [Matrix.one_apply, apply_ite τ]

theorem period_lift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (ι : Type) (𝓕 : Filter ι) (x₀ : Frame X.Ψ r) (x₁ : ι → Frame X.Ψ r), x₀ ∈ X.dom → (∀ᶠ n in 𝓕, x₁ n ∈ X.dom) → (∀ v ∈ X.Λ, ∀ (τ : X.Ψ) (a : Fin r), Tendsto (fun n => (if (a : ℕ) < X.p0 then hermC τ.1 X.Gm (col (mat (x₁ n) τ) a) (Data.emb τ.1 v) else ((mat (x₁ n) τ)⁻¹ *ᵥ Data.emb τ.1 v) a)) 𝓕 (𝓝 (if (a : ℕ) < X.p0 then hermC τ.1 X.Gm (col (mat x₀ τ) a) (Data.emb τ.1 v) else ((mat x₀ τ)⁻¹ *ᵥ Data.emb τ.1 v) a))) → ∀ V ∈ 𝓝 x₀, ∀ᶠ n in 𝓕, ∃ x ∈ V, ∀ (v : Fin r → E) (τ : X.Ψ) (a : Fin r), (if (a : ℕ) < X.p0 then hermC τ.1 X.Gm (col (mat x τ) a) (Data.emb τ.1 v) else ((mat x τ)⁻¹ *ᵥ Data.emb τ.1 v) a) = (if (a : ℕ) < X.p0 then hermC τ.1 X.Gm (col (mat (x₁ n) τ) a) (Data.emb τ.1 v) else ((mat (x₁ n) τ)⁻¹ *ᵥ Data.emb τ.1 v) a) := by
  intro E _ _ _ r X ι 𝓕 x₀ x₁ h0 h1 h V hV
  have key : ∀ τ : X.Ψ, ∃ B : ι → Matrix (Fin r) (Fin r) ℂ, Tendsto B 𝓕 (𝓝 (mat x₀ τ)) ∧
      ∀ᶠ n in 𝓕, (∀ a : Fin r, (a : ℕ) < X.p0 → ∀ k, B n k a = mat (x₁ n) τ k a) ∧
        (∀ a : Fin r, ¬ (a : ℕ) < X.p0 → ∀ k, (B n)⁻¹ a k = (mat (x₁ n) τ)⁻¹ a k) := by
    intro τ
    refine exists_matrix_lift (fun a : Fin r => (a : ℕ) < X.p0) (mat x₀ τ)
      (fun n => mat (x₁ n) τ) (h0 τ).1 (h1.mono fun n hn => (hn τ).1) ?_ ?_
    · intro a ha k
      have := tendsto_of_span (𝓕 := 𝓕) (X.Λ : Set (Fin r → E)) X.Λ_span
        (fun c => (starRingEnd ℂ) (τ.1 c))
        (fun n v => hermC τ.1 X.Gm (col (mat (x₁ n) τ) a) (Data.emb τ.1 v))
        (fun v => hermC τ.1 X.Gm (col (mat x₀ τ) a) (Data.emb τ.1 v))
        (by intros; simp [hermC, Data.emb, mul_add, Finset.sum_add_distrib])
        (by intros; simp [hermC, Data.emb, mul_add, Finset.sum_add_distrib])
        (by intros; simp [hermC, Data.emb, Finset.mul_sum, mul_left_comm])
        (by intros; simp [hermC, Data.emb, Finset.mul_sum, mul_left_comm])
        (by simp)
        (fun v hv => by simpa only [ha, if_true] using h v hv τ a)
        (fun b => cc (X.Gm⁻¹ b k))
      simpa only [hermC_emb_inv_col τ.1 X.Gm X.Gm_det, col] using this
    · intro a ha k
      have := tendsto_of_span (𝓕 := 𝓕) (X.Λ : Set (Fin r → E)) X.Λ_span
        (fun c => τ.1 c)
        (fun n v => ((mat (x₁ n) τ)⁻¹ *ᵥ Data.emb τ.1 v) a)
        (fun v => ((mat x₀ τ)⁻¹ *ᵥ Data.emb τ.1 v) a)
        (by intros; simp [Matrix.mulVec, dotProduct, Data.emb, mul_add, Finset.sum_add_distrib])
        (by intros; simp [Matrix.mulVec, dotProduct, Data.emb, mul_add, Finset.sum_add_distrib])
        (by intros; simp [Matrix.mulVec, dotProduct, Data.emb, Finset.mul_sum, mul_left_comm])
        (by intros; simp [Matrix.mulVec, dotProduct, Data.emb, Finset.mul_sum, mul_left_comm])
        (by simp)
        (fun v hv => by simpa only [ha, if_false] using h v hv τ a)
        (Pi.single k 1)
      simpa [Matrix.mulVec, dotProduct, Data.emb, Pi.single_apply, apply_ite τ.1] using this
  choose B hB hB' using key
  have hx : Tendsto (fun n => (fun τ => B τ n : Frame X.Ψ r)) 𝓕 (𝓝 x₀) :=
    tendsto_pi_nhds.2 fun τ => hB τ
  filter_upwards [hx.eventually_mem hV, eventually_all.2 hB'] with n hn hn'
  refine ⟨_, hn, fun v τ a => ?_⟩
  have hm : mat (fun τ => B τ n : Frame X.Ψ r) τ = B τ n := rfl
  rw [hm]
  by_cases ha : (a : ℕ) < X.p0
  · have : col (B τ n) a = col (mat (x₁ n) τ) a := funext fun k => (hn' τ).1 a ha k
    simp only [ha, if_true, this]
  · simp only [ha, if_false, Matrix.mulVec, dotProduct, (hn' τ).2 a ha]

end GlobalTheory.PeriodLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.PeriodCoordinatesFramesLiftTendstoStatement
open NumberField Topology Filter ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_coordinates_frames_lift_tendsto : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (ι : Type) (𝓕 : Filter ι) (x₀ : Frame X.Ψ r) (x₁ : ι → Frame X.Ψ r), x₀ ∈ X.dom → (∀ᶠ n in 𝓕, x₁ n ∈ X.dom) → (∀ v ∈ X.Λ, ∀ (τ : X.Ψ) (a : Fin r), Tendsto (fun n => (if (a : ℕ) < X.p0 then hermC τ.1 X.Gm (col (mat (x₁ n) τ) a) (Data.emb τ.1 v) else ((mat (x₁ n) τ)⁻¹ *ᵥ Data.emb τ.1 v) a)) 𝓕 (𝓝 (if (a : ℕ) < X.p0 then hermC τ.1 X.Gm (col (mat x₀ τ) a) (Data.emb τ.1 v) else ((mat x₀ τ)⁻¹ *ᵥ Data.emb τ.1 v) a))) → ∀ V ∈ 𝓝 x₀, ∀ᶠ n in 𝓕, ∃ x ∈ V, ∀ (v : Fin r → E) (τ : X.Ψ) (a : Fin r), (if (a : ℕ) < X.p0 then hermC τ.1 X.Gm (col (mat x τ) a) (Data.emb τ.1 v) else ((mat x τ)⁻¹ *ᵥ Data.emb τ.1 v) a) = (if (a : ℕ) < X.p0 then hermC τ.1 X.Gm (col (mat (x₁ n) τ) a) (Data.emb τ.1 v) else ((mat (x₁ n) τ)⁻¹ *ᵥ Data.emb τ.1 v) a) := by
  first | exact @GlobalTheory.PeriodLift.period_lift | exact GlobalTheory.PeriodLift.period_lift | (intros; apply GlobalTheory.PeriodLift.period_lift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsIntegralPointThrough
namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G.T0
open IsLocalRing

theorem exists_integral_point_through (O B : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [CharZero O]
    [CommRing B] [IsDomain B] [Algebra O B] [Algebra.FiniteType O B] [Module.Flat O B]
    (M : Ideal B) (hM : M.IsMaximal) (hsp : Ideal.map (algebraMap O B) (maximalIdeal O) ≤ M)
    (e : B) (he : e ≠ 0) :
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Algebra O V)
      (_ : Module.Finite O V) (φ : B →ₐ[O] V), φ e ≠ 0 ∧ ∀ x ∈ M, φ x ∈ maximalIdeal V := by
  classical
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hmO : maximalIdeal O = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing O B
  set w := algebraMap O B ϖ with hw

  have hw0 : w ≠ 0 := by
    intro h0
    have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := B)
      (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero)
    have h1 : ϖ • (1 : B) = ϖ • (0 : B) := by rw [Algebra.smul_def, mul_one, ← hw, h0, smul_zero]
    exact one_ne_zero (hreg h1)
  have hϖm : ϖ ∈ maximalIdeal O := by rw [hmO]; exact Ideal.mem_span_singleton_self ϖ
  have hwM : w ∈ M := hsp (Ideal.mem_map_of_mem _ hϖm)
  obtain ⟨q, hq, hqM, heq, hwq, hchain⟩ := DimensionQuotientBound.local_step M w e hwM hw0 he
  obtain ⟨s, hsM, hs⟩ := PrimeAvoidanceFibre.avoid M q w hchain

  let D := B ⧸ q
  have : IsDomain D := Ideal.Quotient.isDomain q
  let sb : D := Ideal.Quotient.mk q s
  have hsb : sb ≠ 0 := fun h => hsM (hqM (Ideal.Quotient.eq_zero_iff_mem.1 h))
  let D' := Localization.Away sb
  have hpow : Submonoid.powers sb ≤ nonZeroDivisors D := powers_le_nonZeroDivisors_of_noZeroDivisors hsb
  have : IsDomain D' := IsLocalization.isDomain_localization hpow
  have : IsNoetherianRing D' := IsLocalization.isNoetherianRing (Submonoid.powers sb) D' inferInstance
  have : Algebra.FiniteType O D :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ O q) Ideal.Quotient.mk_surjective
  have : Algebra.FiniteType O D' := inferInstance
  have hDinj : Function.Injective (algebraMap D D') := IsLocalization.injective D' hpow

  let f : B →+* D' := (algebraMap D D').comp (Ideal.Quotient.mk q)
  have hfO : ∀ c : O, algebraMap O D' c = f (algebraMap O B c) := fun c => by
    rw [IsScalarTower.algebraMap_apply O D D']; rfl
  have hcomapM : ∀ P : Ideal D', P.IsPrime → algebraMap O D' ϖ ∈ P → Ideal.comap f P = M := by
    intro P hP hwP
    refine hs _ (Ideal.comap_isPrime f P) (fun x hx => ?_) ?_ ?_
    · show algebraMap D D' (Ideal.Quotient.mk q x) ∈ P
      rw [Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero]; exact P.zero_mem
    · rw [Ideal.mem_comap, ← hfO]; exact hwP
    · intro hsP
      have hu : IsUnit (algebraMap D D' sb) := IsLocalization.map_units D' ⟨sb, Submonoid.mem_powers sb⟩
      exact hP.ne_top (Ideal.eq_top_of_isUnit_mem _ hsP hu)
  have huniq : ∀ P P' : Ideal D', P.IsPrime → P'.IsPrime → algebraMap O D' ϖ ∈ P →
      algebraMap O D' ϖ ∈ P' → P = P' := by
    intro P P' hP hP' hwP hwP'
    have e1 : Ideal.comap (Ideal.Quotient.mk q) (Ideal.comap (algebraMap D D') P) =
        Ideal.comap (Ideal.Quotient.mk q) (Ideal.comap (algebraMap D D') P') := by
      rw [Ideal.comap_comap, Ideal.comap_comap]
      exact (hcomapM P hP hwP).trans (hcomapM P' hP' hwP').symm
    have e2 := Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective e1
    rw [← IsLocalization.map_under (Submonoid.powers sb) D' P,
      ← IsLocalization.map_under (Submonoid.powers sb) D' P']
    exact congrArg _ e2
  have hex : ∃ P : Ideal D', P.IsPrime ∧ algebraMap O D' ϖ ∈ P := by
    let Mb := Ideal.map (Ideal.Quotient.mk q) M
    have hMb : Mb.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hqM)
    have hcMb : Ideal.comap (Ideal.Quotient.mk q) Mb = M := by
      rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
        Ideal.mk_ker, sup_eq_left.2 hqM]
    have hdisj : Disjoint (Submonoid.powers sb : Set D) Mb := by
      rw [Set.disjoint_left]
      rintro x ⟨n, rfl⟩ hx
      have : s ^ n ∈ M := by
        rw [← hcMb, Ideal.mem_comap, map_pow]; exact hx
      exact hsM (hM.isPrime.mem_of_pow_mem n this)
    refine ⟨Ideal.map (algebraMap D D') Mb,
      IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers sb) D' Mb hMb hdisj, ?_⟩
    rw [hfO]
    exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hwM)
  have hfin : Module.Finite O D' := PrimeAvoidanceFibre.finite_of_fibre ϖ hϖ hex huniq

  have hOinj : Function.Injective (algebraMap O D') := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    by_contra hne
    push Not at hne
    obtain ⟨c, hc, hc0⟩ := hne
    have hker : RingHom.ker (algebraMap O D') ≠ ⊥ := fun h =>
      hc0 ((RingHom.injective_iff_ker_eq_bot _).2 h (hc.trans (map_zero _).symm))
    have hkp : (RingHom.ker (algebraMap O D')).IsPrime := RingHom.ker_isPrime _
    have hkm : RingHom.ker (algebraMap O D') = maximalIdeal O :=
      IsLocalRing.eq_maximalIdeal (hkp.isMaximal hker)
    have hϖk : ϖ ∈ RingHom.ker (algebraMap O D') := by
      rw [hkm, hmO]; exact Ideal.mem_span_singleton_self ϖ
    rw [RingHom.mem_ker, hfO] at hϖk
    apply hwq
    have : algebraMap D D' (Ideal.Quotient.mk q w) = algebraMap D D' 0 := by rw [map_zero]; exact hϖk
    exact Ideal.Quotient.eq_zero_iff_mem.1 (hDinj this)
  have : FaithfulSMul O D' := (faithfulSMul_iff_algebraMap_injective O D').2 hOinj

  let K := FractionRing O
  let L := FractionRing D'
  have : FaithfulSMul O L := (faithfulSMul_iff_algebraMap_injective O L).2 (by
    rw [IsScalarTower.algebraMap_eq O D' L]
    exact (IsFractionRing.injective D' L).comp hOinj)
  let _ : Algebra K L := FractionRing.liftAlgebra O L
  have : IsScalarTower O K L := FractionRing.isScalarTower_liftAlgebra O L
  have : Algebra.IsIntegral O D' := Algebra.IsIntegral.of_finite O D'
  have : FiniteDimensional K L := Module.Finite.of_isLocalization O D' (nonZeroDivisors O)
  have : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective O K)
  have : Algebra.IsSeparable K L := inferInstance
  have hVfin : Module.Finite O (integralClosure O L) := IsIntegralClosure.finite O K L (integralClosure O L)
  have hdvr : IsDiscreteValuationRing (integralClosure O L) := FiniteAlgebraLocalCompletion.cl_dvr O K L

  let g1 : B →ₐ[O] D := Ideal.Quotient.mkₐ O q
  let g2 : D →ₐ[O] D' := IsScalarTower.toAlgHom O D D'
  let g3 : D' →ₐ[O] L := IsScalarTower.toAlgHom O D' L
  let g4 : D' →ₐ[O] integralClosure O L :=
    g3.codRestrict (integralClosure O L) fun x => (Algebra.IsIntegral.isIntegral x).map g3
  refine ⟨integralClosure O L, inferInstance, inferInstance, hdvr, inferInstance, hVfin,
    g4.comp (g2.comp g1), ?_, ?_⟩
  swap
  ·
    have hloc := FiniteAlgebraLocalCompletion.cl_isLocalHom O L
    let P : Ideal D' := Ideal.comap g4 (maximalIdeal (integralClosure O L))
    have hP : P.IsPrime := Ideal.comap_isPrime _ _
    have hϖP : algebraMap O D' ϖ ∈ P := by
      show g4 (algebraMap O D' ϖ) ∈ maximalIdeal (integralClosure O L)
      rw [g4.commutes]
      exact map_nonunit _ ϖ hϖm
    intro x hx
    rw [← hcomapM P hP hϖP] at hx
    exact hx
  intro h0
  have h1 : g3 (g2 (g1 e)) = 0 := congrArg Subtype.val h0
  have h2 : g2 (g1 e) = 0 := (IsFractionRing.injective D' L) (h1.trans (map_zero _).symm)
  have h3 : g1 e = 0 := hDinj (h2.trans (map_zero _).symm)
  exact heq (Ideal.Quotient.eq_zero_iff_mem.1 h3)

end GlobalTheory
end
