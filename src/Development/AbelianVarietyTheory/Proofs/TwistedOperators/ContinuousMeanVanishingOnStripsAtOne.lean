module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicInfFinSplitPeriodsUnimodular
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactSubgroupsActOnFockVectorsAllSignatures
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiExteriorTensorSmoothIrreducibleIsIrreducible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormFockLSqLe

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousMeanVanishingOnStripsAtOne
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousMeanVanishingOnStripsAtOne
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.StripVanish


set_option maxHeartbeats 1000000 in
theorem mean_eq_zero_of_strips : ∀ (D : D7) (W : HSp D) (vW : GlobalTheory.Unf.Vol W) (R K : Subgroup (GA D W)), IsClosed (R : Set (GA D W)) → (∀ a ∈ GinfC W, ∀ b ∈ GfC W, a * b ∈ R → a ∈ R ∧ b ∈ R) → K ≤ GfC W → IsCompact (K : Set (GA D W)) → IsOpen ((K.subgroupOf (GfC W) : Subgroup (GfC W)) : Set (GfC W)) → ∀ (μR : Measure R), μR.IsHaarMeasure → μR.IsInvInvariant → ∀ (𝓡 : Set R) (𝓑 : Set (GA D W)), IsFundamentalDomain ((GQ W ⊓ R).subgroupOf R) 𝓡 μR → IsFundamentalDomain (GQ W ⊓ R : Subgroup (GA D W)) 𝓑 vW.μ → ∀ f : GA D W → ℂ, Measurable f → (∀ γ ∈ GQ W ⊓ R, ∀ g, f (γ * g) = f g) → IntegrableOn f 𝓑 vW.μ → (∀ h, IntegrableOn (fun r : R => f (r * h)) 𝓡 μR) → (Continuous fun h => ∫ r in 𝓡, f ((r : GA D W) * h) ∂μR) → (∀ k ∈ K, ∀ g, f (g * k) = f g) → (∀ h, f h ≠ 0 → ∃ r ∈ R, ∃ a ∈ GinfC W, ∃ k ∈ K, h = r * a * k) → (∀ C : Set (GA D W), IsCompact C → C ⊆ GinfC W → MeasurableSet (strip W R C) ∧ ∫ h in 𝓑 ∩ strip W R C, f h ∂vW.μ = 0) → ∫ r in 𝓡, f r ∂μR = 0 := by
  intro D W vW R K hRc hsplit hKf hKc hKo μR hμR hμRinv 𝓡 𝓑 h𝓡 h𝓑 f hfm hfl hfi hfiR hTc hfK hsupp hstrip
  haveI := vW.haar
  haveI : LocallyCompactSpace R := hRc.locallyCompactSpace
  haveI : μR.IsMulRightInvariant := by rw [← Measure.inv_eq_self μR]; infer_instance
  obtain ⟨hinfC, -, hcomm, ⟨e, he⟩, -⟩ := GlobalTheory.AdelicSplit.adelic_split D W
  obtain ⟨hΓc, hΓd, -⟩ :=
    GlobalTheory.RationalSubgroupFund.countable_discrete_exists_fundamentalDomain D W (GQ W ⊓ R) inf_le_left
  set T : GA D W → ℂ := fun h => ∫ r in 𝓡, f ((r : GA D W) * h) ∂μR with hTdef
  have hQ := GlobalTheory.quot_fubini_mean (GA D W) vW.μ R (GQ W ⊓ R) inf_le_right hRc hΓc hΓd μR hμR 𝓡 𝓑 h𝓡 h𝓑 f hfm
    hfl hfi hfiR
  have hTl : ∀ s ∈ R, ∀ x, T (s * x) = T x := fun s hs x => hQ.left hs x
  have hTr : ∀ k ∈ K, ∀ x, T (x * k) = T x := by
    intro k hk x
    simp only [hTdef]
    congr 1
    funext r
    rw [← mul_assoc, hfK k hk]
  have h1 : T 1 = ∫ r in 𝓡, f (r : GA D W) ∂μR := by simp [hTdef]
  rw [← h1]
  by_contra hT1

  have hsupT : ∀ x, T x ≠ 0 → ∃ q ∈ R, ∃ a ∈ GinfC W, ∃ k ∈ K, x = q * a * k := by
    intro x hx
    by_contra hno
    apply hx
    have hz : ∀ r : R, f ((r : GA D W) * x) = 0 := by
      intro r
      by_contra hr
      obtain ⟨r₁, hr₁, a, ha, k, hk, hrx⟩ := hsupp _ hr
      refine hno ⟨(r : GA D W)⁻¹ * r₁, R.mul_mem (R.inv_mem r.2) hr₁, a, ha, k, hk, ?_⟩
      rw [show x = (r : GA D W)⁻¹ * ((r : GA D W) * x) by group, hrx]
      group
    simp [hTdef, hz]

  have hP : ∀ C : Set (GA D W), C ⊆ GinfC W → ∀ x ∈ strip W R C, T x ≠ 0 → ∃ c ∈ C, T x = T c := by
    rintro C hC x ⟨r, hr, c, hc, b, hb, rfl⟩ hx
    obtain ⟨q, hq, a, ha, k, hk, hx'⟩ := hsupT _ hx
    have hkb : k * b⁻¹ ∈ GfC W := (GfC W).mul_mem (hKf hk) ((GfC W).inv_mem hb)
    have hc' : c⁻¹ ∈ GinfC W := (GinfC W).inv_mem (hC hc)
    have hac : a * c⁻¹ ∈ GinfC W := (GinfC W).mul_mem ha hc'
    have e1 : c⁻¹ * (k * b⁻¹) = (k * b⁻¹) * c⁻¹ := hcomm _ hc' _ hkb
    have hmem : (a * c⁻¹) * (k * b⁻¹) ∈ R := by
      have : (a * c⁻¹) * (k * b⁻¹) = q⁻¹ * r := by
        calc (a * c⁻¹) * (k * b⁻¹) = a * (k * b⁻¹) * c⁻¹ := by rw [mul_assoc, e1, ← mul_assoc]
          _ = q⁻¹ * (q * a * k) * b⁻¹ * c⁻¹ := by group
          _ = q⁻¹ * (r * c * b) * b⁻¹ * c⁻¹ := by rw [hx']
          _ = q⁻¹ * r := by group
      rw [this]
      exact R.mul_mem (R.inv_mem hq) hr
    obtain ⟨hacR, -⟩ := hsplit _ hac _ hkb hmem
    refine ⟨c, hc, ?_⟩
    calc T (r * c * b) = T (q * (a * k)) := by rw [hx', mul_assoc]
      _ = T a := by rw [hTl q hq, hTr k hk]
      _ = T ((a * c⁻¹) * c) := by group
      _ = T c := hTl _ hacR c

  set U : Set (GA D W) := {h | (1 : ℝ) / 2 < (T h / T 1).re} with hUdef
  have hUo : IsOpen U := isOpen_lt continuous_const (Complex.continuous_re.comp (hTc.div_const (T 1)))
  have h1U : (1 : GA D W) ∈ U := by
    show (1 : ℝ) / 2 < (T 1 / T 1).re
    rw [div_self hT1]; norm_num
  haveI : LocallyCompactSpace (GinfC W) := hinfC.locallyCompactSpace
  have hU'o : IsOpen ((Subtype.val : GinfC W → GA D W) ⁻¹' U) := hUo.preimage continuous_subtype_val
  obtain ⟨C', hC'n, hC'U, hC'c⟩ :=
    local_compact_nhds (hU'o.mem_nhds (show ((1 : GinfC W) : GA D W) ∈ U from h1U))
  set C : Set (GA D W) := Subtype.val '' C' with hCdef
  have hCinf : C ⊆ GinfC W := by rintro _ ⟨y, -, rfl⟩; exact y.2
  have hCU : C ⊆ U := by rintro _ ⟨y, hy, rfl⟩; exact hC'U hy
  obtain ⟨hSm, hS0⟩ := hstrip C (hC'c.image continuous_subtype_val) hCinf
  set S := strip W R C with hSdef
  have hSinv : ∀ s ∈ R, ∀ x, s * x ∈ S ↔ x ∈ S := by
    intro s hs x
    constructor
    · rintro ⟨r, hr, c, hc, b, hb, hx⟩
      refine ⟨s⁻¹ * r, R.mul_mem (R.inv_mem hs) hr, c, hc, b, hb, ?_⟩
      rw [show x = s⁻¹ * (s * x) by group, hx]; group
    · rintro ⟨r, hr, c, hc, b, hb, rfl⟩
      exact ⟨s * r, R.mul_mem hs hr, c, hc, b, hb, by group⟩

  have hfSl : ∀ γ ∈ GQ W ⊓ R, ∀ g, S.indicator f (γ * g) = S.indicator f g := by
    intro γ hγ g
    by_cases hg : g ∈ S
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem ((hSinv γ hγ.2 g).2 hg), hfl γ hγ g]
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (mt (hSinv γ hγ.2 g).1 hg)]
  have hfSi : ∀ h, IntegrableOn (fun r : R => S.indicator f ((r : GA D W) * h)) 𝓡 μR := by
      intro h
      by_cases hh : h ∈ S
      · have : (fun r : R => S.indicator f ((r : GA D W) * h)) = fun r : R => f ((r : GA D W) * h) :=
          funext fun r => Set.indicator_of_mem ((hSinv _ r.2 h).2 hh) _
        rw [this]; exact hfiR h
      · have : (fun r : R => S.indicator f ((r : GA D W) * h)) = fun _ => 0 :=
          funext fun r => by simp [Set.indicator_apply, hSinv _ r.2 h, hh]
        rw [this]; exact integrableOn_zero
  have hQS := GlobalTheory.quot_fubini_mean (GA D W) vW.μ R (GQ W ⊓ R) inf_le_right hRc hΓc hΓd μR hμR 𝓡 𝓑 h𝓡 h𝓑
    (S.indicator f) (hfm.indicator hSm) hfSl (hfi.indicator hSm) hfSi
  have hQS' : IsQuotIntL1 μR vW.μ (S.indicator T) 0 := by
    have e1 : (fun h => ∫ r in 𝓡, S.indicator f ((r : GA D W) * h) ∂μR) = S.indicator T := by
      funext h
      by_cases hh : h ∈ S
      · rw [Set.indicator_of_mem hh]
        simp only [hTdef]
        congr 1; funext r
        exact Set.indicator_of_mem ((hSinv _ r.2 h).2 hh) _
      · simp [Set.indicator_apply, hSinv _ (Subtype.property _) h, hh]
    have e2 : ∫ g in 𝓑, S.indicator f g ∂vW.μ = 0 := by rw [setIntegral_indicator hSm, hS0]
    rw [e1, e2] at hQS
    exact hQS
  obtain ⟨β, -, hβ⟩ := GlobalTheory.Tw.exists_isCosetCutoff (μT := μR) hRc
  obtain ⟨hβi, hβ0⟩ := hQS'.cutoff hβ

  have hre : ∀ x, 0 ≤ (S.indicator T x / T 1).re ∧ (x ∈ S → T x ≠ 0 → (1 : ℝ) / 2 < (S.indicator T x / T 1).re) := by
    intro x
    by_cases hxS : x ∈ S
    · rw [Set.indicator_of_mem hxS]
      by_cases hx : T x = 0
      · simp [hx]
      · obtain ⟨c, hc, hTc'⟩ := hP C hCinf x hxS hx
        have h2 : (1 : ℝ) / 2 < (T x / T 1).re := by rw [hTc']; exact hCU hc
        exact ⟨by linarith, fun _ _ => h2⟩
    · simp [Set.indicator_of_notMem hxS, hxS]
  set φ : GA D W → ℝ := fun x => ((β x : ℝ) • S.indicator T x / T 1).re with hφdef
  have hφ : ∀ x, φ x = (β x : ℝ) * (S.indicator T x / T 1).re := by
    intro x
    simp only [hφdef, Complex.real_smul, mul_div_assoc, Complex.re_ofReal_mul]
  have hφnn : 0 ≤ φ := fun x => by rw [hφ]; exact mul_nonneg (NNReal.coe_nonneg _) (hre x).1
  have hφi : Integrable φ vW.μ := (hβi.div_const (T 1)).re
  have hφ0 : ∫ x, φ x ∂vW.μ = 0 := by
    have h := integral_re (hβi.div_const (T 1))
    simp only [RCLike.re_to_complex] at h
    simp only [hφdef]
    rw [h, integral_div, ← hβ0, zero_div, Complex.zero_re]
  have hφae := (integral_eq_zero_iff_of_nonneg hφnn hφi).1 hφ0
  set A : Set (GA D W) := S ∩ {x | T x ≠ 0} with hAdef
  have hAm : MeasurableSet A := hSm.inter (hTc.measurable (measurableSet_singleton (0 : ℂ)).compl)
  have hAinv : ∀ s ∈ R, ∀ x, s * x ∈ A ↔ x ∈ A := by
    intro s hs x
    simp only [hAdef, Set.mem_inter_iff, Set.mem_setOf_eq, hSinv s hs x, hTl s hs x]
  set g : GA D W → ENNReal := A.indicator fun x => (β x : ENNReal) with hgdef
  have hgm : Measurable g := hβ.1.coe_nnreal_ennreal.indicator hAm
  have hg0 : ∫⁻ x, g x ∂vW.μ = 0 := by
    rw [lintegral_eq_zero_iff hgm]
    filter_upwards [hφae] with x hx
    by_cases hxA : x ∈ A
    · have h2 := (hre x).2 hxA.1 hxA.2
      rw [Pi.zero_apply, hφ] at hx
      have : (β x : ℝ) = 0 := by
        rcases mul_eq_zero.1 hx with h | h
        · exact h
        · linarith
      simp [hgdef, Set.indicator_of_mem hxA, Pi.zero_apply, NNReal.coe_eq_zero.1 this]
    · simp [hgdef, Set.indicator_of_notMem hxA]

  have hA0 : vW.μ A = 0 := by
    have hmul : Measurable fun p : GA D W × R => (p.2 : GA D W) * p.1 :=
      (measurable_subtype_coe.comp measurable_snd).mul measurable_fst
    have e1 : vW.μ A = ∫⁻ x, ∫⁻ t : R, g ((t : GA D W) * x) ∂μR ∂vW.μ := by
      rw [← lintegral_indicator_one hAm]
      refine lintegral_congr fun x => ?_
      by_cases hxA : x ∈ A
      · have : ∀ t : R, g ((t : GA D W) * x) = β ((t : GA D W) * x) := fun t => by
          simp [hgdef, Set.indicator_of_mem ((hAinv _ t.2 x).2 hxA)]
        simp only [this, hβ.2 x, Set.indicator_of_mem hxA, Pi.one_apply]
      · have : ∀ t : R, g ((t : GA D W) * x) = 0 := fun t => by
          simp [hgdef, Set.indicator_of_notMem (mt (hAinv _ t.2 x).1 hxA)]
        simp [this, Set.indicator_of_notMem hxA]
    rw [e1, lintegral_lintegral_swap (f := fun x (t : R) => g ((t : GA D W) * x)) (hgm.comp hmul).aemeasurable]
    have e2 : ∀ t : R, ∫⁻ x, g ((t : GA D W) * x) ∂vW.μ = 0 := fun t => by
      rw [lintegral_mul_left_eq_self, hg0]
    simp [e2]

  set O : Set (GA D W) := e '' (interior C' ×ˢ ((K.subgroupOf (GfC W) : Subgroup (GfC W)) : Set (GfC W))) with hOdef
  have hOo : IsOpen O := e.isOpenMap _ (isOpen_interior.prod hKo)
  have h1O : (1 : GA D W) ∈ O :=
    ⟨(1, 1), ⟨mem_interior_iff_mem_nhds.2 hC'n, (K.subgroupOf (GfC W)).one_mem⟩, by rw [he]; simp⟩
  have hOA : O ⊆ A := by
    rintro _ ⟨p, ⟨hp1, hp2⟩, rfl⟩
    rw [he]
    have hk : (p.2 : GA D W) ∈ K := Subgroup.mem_subgroupOf.1 hp2
    refine ⟨⟨1, R.one_mem, p.1, ⟨p.1, interior_subset hp1, rfl⟩, p.2, p.2.2, by simp⟩, ?_⟩
    show T (p.1 * p.2) ≠ 0
    rw [hTr _ hk]
    intro h0
    have := hC'U (interior_subset hp1)
    simp only [Set.mem_preimage, hUdef, Set.mem_setOf_eq, h0, zero_div, Complex.zero_re] at this
    linarith
  have hpos := hOo.measure_pos vW.μ ⟨1, h1O⟩
  exact hpos.ne' (measure_mono_null hOA hA0)

end GlobalTheory.StripVanish
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousMeanVanishingOnStripsAtOneStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuousMean_vanishing_on_strips_at_one : ∀ (D : D7) (W : HSp D) (vW : GlobalTheory.Unf.Vol W) (R K : Subgroup (GA D W)), IsClosed (R : Set (GA D W)) → (∀ a ∈ GinfC W, ∀ b ∈ GfC W, a * b ∈ R → a ∈ R ∧ b ∈ R) → K ≤ GfC W → IsCompact (K : Set (GA D W)) → IsOpen ((K.subgroupOf (GfC W) : Subgroup (GfC W)) : Set (GfC W)) → ∀ (μR : Measure R), μR.IsHaarMeasure → μR.IsInvInvariant → ∀ (𝓡 : Set R) (𝓑 : Set (GA D W)), IsFundamentalDomain ((GQ W ⊓ R).subgroupOf R) 𝓡 μR → IsFundamentalDomain (GQ W ⊓ R : Subgroup (GA D W)) 𝓑 vW.μ → ∀ f : GA D W → ℂ, Measurable f → (∀ γ ∈ GQ W ⊓ R, ∀ g, f (γ * g) = f g) → IntegrableOn f 𝓑 vW.μ → (∀ h, IntegrableOn (fun r : R => f (r * h)) 𝓡 μR) → (Continuous fun h => ∫ r in 𝓡, f ((r : GA D W) * h) ∂μR) → (∀ k ∈ K, ∀ g, f (g * k) = f g) → (∀ h, f h ≠ 0 → ∃ r ∈ R, ∃ a ∈ GinfC W, ∃ k ∈ K, h = r * a * k) → (∀ C : Set (GA D W), IsCompact C → C ⊆ GinfC W → MeasurableSet (strip W R C) ∧ ∫ h in 𝓑 ∩ strip W R C, f h ∂vW.μ = 0) → ∫ r in 𝓡, f r ∂μR = 0 := by
  first | exact @GlobalTheory.StripVanish.mean_eq_zero_of_strips | exact GlobalTheory.StripVanish.mean_eq_zero_of_strips | (intros; apply GlobalTheory.StripVanish.mean_eq_zero_of_strips <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorFrameChangeSameCartan
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorFrameChangeSameCartan
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift

namespace GlobalTheory.FrameChange

variable {D : D7}

theorem sign_eq_of_ne_zero {n : ℕ} {ε ε' : Fin n → Bool} {x : Matrix (Fin n) (Fin n) ℂ}
    (h : Formalism.REAL.Jm ε * x = x * Formalism.REAL.Jm ε') {a i : Fin n} (hx : x a i ≠ 0) : ε a = ε' i := by
  have hc := congrFun (congrFun h a) i
  rw [Formalism.REAL.Jm, Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul] at hc
  by_contra hne
  apply hx
  cases h1 : ε a <;> cases h2 : ε' i <;> simp only [h1, h2] at hc hne
  · exact (hne trivial).elim
  · simp at hc; linear_combination -hc / 2
  · simp at hc; linear_combination hc / 2
  · exact (hne trivial).elim

theorem Jm_mul_fr {V : HSp D} (X Y : Fr V) (τ : D.what₂.Tau) (h : Y.cart τ = X.cart τ) :
    Formalism.REAL.Jm (X.ε τ) * (X.fr τ * (Y.fr τ)⁻¹) = X.fr τ * (Y.fr τ)⁻¹ * Formalism.REAL.Jm (Y.ε τ) := by
  unfold Fr.cart at h
  calc Formalism.REAL.Jm (X.ε τ) * (X.fr τ * (Y.fr τ)⁻¹)
      = (X.fr τ * (X.fr τ)⁻¹) * Formalism.REAL.Jm (X.ε τ) * (X.fr τ * (Y.fr τ)⁻¹) := by
        rw [GlobalTheory.CompactFockAction.fr_mul_inv, Matrix.one_mul]
    _ = X.fr τ * ((X.fr τ)⁻¹ * Formalism.REAL.Jm (X.ε τ) * X.fr τ) * (Y.fr τ)⁻¹ := by simp only [Matrix.mul_assoc]
    _ = X.fr τ * ((Y.fr τ)⁻¹ * Formalism.REAL.Jm (Y.ε τ) * Y.fr τ) * (Y.fr τ)⁻¹ := by rw [h]
    _ = X.fr τ * (Y.fr τ)⁻¹ * Formalism.REAL.Jm (Y.ε τ) * (Y.fr τ * (Y.fr τ)⁻¹) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [GlobalTheory.CompactFockAction.fr_mul_inv, Matrix.mul_one]

theorem fr_mul_inv_mul {V : HSp D} (X Y : Fr V) (τ : D.what₂.Tau) :
    X.fr τ * (Y.fr τ)⁻¹ * (Y.fr τ * (X.fr τ)⁻¹) = 1 := by
  calc X.fr τ * (Y.fr τ)⁻¹ * (Y.fr τ * (X.fr τ)⁻¹) = X.fr τ * ((Y.fr τ)⁻¹ * Y.fr τ) * (X.fr τ)⁻¹ := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [GlobalTheory.CompactFockAction.inv_mul_fr, Matrix.mul_one, GlobalTheory.CompactFockAction.fr_mul_inv]

section Coef

variable {V W : HSp D}

def coef (A A' : Fr V) (B B' : Fr W) (v : FVar D W.rank V.rank) (p : Fin W.rank × Fin V.rank) : ℂ :=
  if B'.ε v.1 v.2.1 = A'.ε v.1 v.2.2 then
    (B.fr v.1 * (B'.fr v.1)⁻¹) p.1 v.2.1 * (A'.fr v.1 * (A.fr v.1)⁻¹) v.2.2 p.2
  else starRingEnd ℂ ((B.fr v.1 * (B'.fr v.1)⁻¹) p.1 v.2.1 * (A'.fr v.1 * (A.fr v.1)⁻¹) v.2.2 p.2)

def sub (A A' : Fr V) (B B' : Fr W) : PolF D W.rank V.rank →ₐ[ℂ] PolF D W.rank V.rank :=
  MvPolynomial.aeval fun v => ∑ p, coef A A' B B' v p • (MvPolynomial.X (v.1, p.1, p.2) : PolF D W.rank V.rank)

end Coef

end GlobalTheory.FrameChange

namespace GlobalTheory.FrameChange

variable {D : D7} {V W : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}

theorem onb_eq (X Y : Fr V) (τ : D.what₂.Tau) : Y.onb τ = X.onb τ * (X.fr τ * (Y.fr τ)⁻¹) := by
  unfold Fr.onb
  rw [← Matrix.mul_assoc, GlobalTheory.CompactFockAction.inv_mul_fr, Matrix.one_mul]

theorem inv_fr_mul (X Y : Fr V) (τ : D.what₂.Tau) : (X.fr τ * (Y.fr τ)⁻¹)⁻¹ = Y.fr τ * (X.fr τ)⁻¹ :=
  Matrix.inv_eq_left_inv (fr_mul_inv_mul Y X τ)

theorem aPlusAll_change (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (A A' : Fr V) (B B' : Fr W)
    (hA : ∀ τ, A'.cart τ = A.cart τ) (hB : ∀ τ, B'.cart τ = B.cart τ) (v : FVar D W.rank V.rank)
    (g : WO V W → ℂ) (hg : IsThetaFunO ψ V W g) :
    aPlusAll (heisO ψ V W) θ (fun ρ => cplxO (A.cart ρ) (B.cart ρ)) A'.onb B'.onb v g =
      ∑ p, coef A A' B B' v p •
        aPlusAll (heisO ψ V W) θ (fun ρ => cplxO (A.cart ρ) (B.cart ρ)) A.onb B.onb (v.1, p.1, p.2) g := by
  obtain ⟨ρ, i, j⟩ := v
  simp only [aPlusAll]
  rw [onb_eq A A' ρ, onb_eq B B' ρ, GlobalTheory.FockBasis.unitMap_mul, inv_fr_mul,
    GlobalTheory.FockSubst.aPlus_dir_sum hψ hθ ρ _ _ hg, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [GlobalTheory.FockSubst.aPlus_dir_sum hψ hθ ρ _ _ hg]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [GlobalTheory.FockSubst.aPlus_dir_smul hψ hθ ρ _ _ hg _ _ (GlobalTheory.CompactFockAction.Jm_single A B ρ a b)]
  congr 1
  simp only [coef]
  by_cases hx : (B.fr ρ * (B'.fr ρ)⁻¹) a i * (A'.fr ρ * (A.fr ρ)⁻¹) j b = 0
  · simp [hx]
  · have h1 := sign_eq_of_ne_zero (Jm_mul_fr B B' ρ (hB ρ)) (left_ne_zero_of_mul hx)
    have h2 := sign_eq_of_ne_zero (Jm_mul_fr A' A ρ (hA ρ).symm) (right_ne_zero_of_mul hx)
    rw [h1, ← h2]
    simp only [decide_eq_true_eq]

theorem ptF_sub (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (A A' : Fr V) (B B' : Fr W)
    (hA : ∀ τ, A'.cart τ = A.cart τ) (hB : ∀ τ, B'.cart τ = B.cart τ) {f : WO V W → ℂ}
    (hf : IsThetaFunO ψ V W f) (Q : PolF D W.rank V.rank) :
    ptF ψ θ A' B' f Q = ptF ψ θ A B f (sub A A' B B' Q) := by
  have e1 : A'.cart = A.cart := funext hA
  have e2 : B'.cart = B.cart := funext hB
  have hS := GlobalTheory.CompactFockAction.cart_isCartanInv A
  have hT := GlobalTheory.CompactFockAction.cart_isCartanInv B
  unfold ptF pureTensorO sub
  rw [e1, e2]
  have hAt : ∀ X Y i f, IsThetaFunO ψ V W f →
      IsThetaFunO ψ V W (aPlusAll (heisO ψ V W) θ (fun ρ => cplxO (A.cart ρ) (B.cart ρ)) X Y i f) :=
    fun _ _ _ _ h => GlobalTheory.FockSubst.aPlus_th hψ hθ _ _ _ h
  have Aadd : ∀ X Y i f f', IsThetaFunO ψ V W f → IsThetaFunO ψ V W f' →
      aPlusAll (heisO ψ V W) θ (fun ρ => cplxO (A.cart ρ) (B.cart ρ)) X Y i (f + f') =
      aPlusAll (heisO ψ V W) θ (fun ρ => cplxO (A.cart ρ) (B.cart ρ)) X Y i f +
      aPlusAll (heisO ψ V W) θ (fun ρ => cplxO (A.cart ρ) (B.cart ρ)) X Y i f' :=
    fun _ _ _ _ _ h h' => GlobalTheory.FockSubst.aPlus_add hψ hθ _ _ _ h h'
  have Asm : ∀ X Y i (a : ℂ) f, IsThetaFunO ψ V W f →
      aPlusAll (heisO ψ V W) θ (fun ρ => cplxO (A.cart ρ) (B.cart ρ)) X Y i (a • f) =
      a • aPlusAll (heisO ψ V W) θ (fun ρ => cplxO (A.cart ρ) (B.cart ρ)) X Y i f :=
    fun _ _ _ a _ h => GlobalTheory.FockSubst.aPlus_smul hψ hθ _ _ _ a h
  have Ac : ∀ X Y i j f, IsThetaFunO ψ V W f →
      aPlusAll (heisO ψ V W) θ (fun ρ => cplxO (A.cart ρ) (B.cart ρ)) X Y i
        (aPlusAll (heisO ψ V W) θ (fun ρ => cplxO (A.cart ρ) (B.cart ρ)) X Y j f) =
      aPlusAll (heisO ψ V W) θ (fun ρ => cplxO (A.cart ρ) (B.cart ρ)) X Y j
        (aPlusAll (heisO ψ V W) θ (fun ρ => cplxO (A.cart ρ) (B.cart ρ)) X Y i f) :=
    fun _ _ i j _ h => GlobalTheory.FockSubst.aPlus_comm (sS := A.cart) (sT := B.cart) hψ hθ i.1 _ hS hT j.1 _ h
  exact GlobalTheory.FockSubst.pure_subst (P := IsThetaFunO ψ V W) (fun _ _ => GlobalTheory.OrientedHeis.theta_add)
    (fun a _ => GlobalTheory.OrientedHeis.theta_smul a) (hAt _ _) (Ac _ _) (Aadd _ _) (Asm _ _) (hAt _ _) (Ac _ _)
    (Aadd _ _) (Asm _ _) (coef A A' B B') (fun v p => (v.1, p.1, p.2))
    (aPlusAll_change hψ hθ A A' B B' hA hB) hf Q

end GlobalTheory.FrameChange

namespace GlobalTheory.FrameChange

variable {D : D7} {V W : HSp D}

theorem coef_comp (X X' : Fr V) (Y Y' : Fr W) (hX : ∀ τ, X'.cart τ = X.cart τ) (hY : ∀ τ, Y'.cart τ = Y.cart τ)
    (v : FVar D W.rank V.rank) (q : Fin W.rank × Fin V.rank) :
    ∑ p, coef X' X Y' Y v p * coef X X' Y Y' (v.1, p.1, p.2) q = if q = (v.2.1, v.2.2) then 1 else 0 := by
  obtain ⟨ρ, i, j⟩ := v

  have hK : ∀ c d, (∑ a, (Y'.fr ρ * (Y.fr ρ)⁻¹) a d * (Y.fr ρ * (Y'.fr ρ)⁻¹) c a) = if c = d then 1 else 0 := by
    intro c d
    have := congrFun (congrFun (fr_mul_inv_mul Y Y' ρ) c) d
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    rw [← this]
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  have hU : ∀ c d, (∑ b, (X.fr ρ * (X'.fr ρ)⁻¹) c b * (X'.fr ρ * (X.fr ρ)⁻¹) b d) = if c = d then 1 else 0 := by
    intro c d
    have := congrFun (congrFun (fr_mul_inv_mul X X' ρ) c) d
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    exact this
  have hprod : (∑ p : Fin W.rank × Fin V.rank, ((Y'.fr ρ * (Y.fr ρ)⁻¹) p.1 i * (X.fr ρ * (X'.fr ρ)⁻¹) j p.2) *
      ((Y.fr ρ * (Y'.fr ρ)⁻¹) q.1 p.1 * (X'.fr ρ * (X.fr ρ)⁻¹) p.2 q.2)) = if q = (i, j) then 1 else 0 := by
    rw [Fintype.sum_prod_type]
    have e : ∀ a b, ((Y'.fr ρ * (Y.fr ρ)⁻¹) a i * (X.fr ρ * (X'.fr ρ)⁻¹) j b) *
        ((Y.fr ρ * (Y'.fr ρ)⁻¹) q.1 a * (X'.fr ρ * (X.fr ρ)⁻¹) b q.2) =
        ((Y'.fr ρ * (Y.fr ρ)⁻¹) a i * (Y.fr ρ * (Y'.fr ρ)⁻¹) q.1 a) *
        ((X.fr ρ * (X'.fr ρ)⁻¹) j b * (X'.fr ρ * (X.fr ρ)⁻¹) b q.2) := fun a b => by ring
    simp only [e, ← Finset.mul_sum, ← Finset.sum_mul, hU, hK]
    obtain ⟨q1, q2⟩ := q
    by_cases h1 : q1 = i <;> by_cases h2 : j = q2 <;> (try simp [h1, h2]) <;> (try exact fun h => h1 h.symm) <;>
      (try exact fun h => h2 h.symm)

  have hterm : ∀ p : Fin W.rank × Fin V.rank, coef X' X Y' Y (ρ, i, j) p * coef X X' Y Y' (ρ, p.1, p.2) q =
      if Y.ε ρ i = X.ε ρ j then
        ((Y'.fr ρ * (Y.fr ρ)⁻¹) p.1 i * (X.fr ρ * (X'.fr ρ)⁻¹) j p.2) *
          ((Y.fr ρ * (Y'.fr ρ)⁻¹) q.1 p.1 * (X'.fr ρ * (X.fr ρ)⁻¹) p.2 q.2)
      else starRingEnd ℂ (((Y'.fr ρ * (Y.fr ρ)⁻¹) p.1 i * (X.fr ρ * (X'.fr ρ)⁻¹) j p.2) *
          ((Y.fr ρ * (Y'.fr ρ)⁻¹) q.1 p.1 * (X'.fr ρ * (X.fr ρ)⁻¹) p.2 q.2)) := by
    intro p
    simp only [coef]
    by_cases hx : (Y'.fr ρ * (Y.fr ρ)⁻¹) p.1 i * (X.fr ρ * (X'.fr ρ)⁻¹) j p.2 = 0
    · simp [hx]
    · have h1 := sign_eq_of_ne_zero (Jm_mul_fr Y' Y ρ (hY ρ).symm) (left_ne_zero_of_mul hx)
      have h2 := sign_eq_of_ne_zero (Jm_mul_fr X X' ρ (hX ρ)) (right_ne_zero_of_mul hx)
      rw [h1, ← h2]
      split_ifs <;> simp [map_mul]
  by_cases hs : Y.ε ρ i = X.ε ρ j
  · simp only [hterm, hs, if_true]
    exact hprod
  · simp only [hterm, hs, if_false]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, hprod]
    split_ifs <;> simp

theorem sub_comp (X X' : Fr V) (Y Y' : Fr W) (hX : ∀ τ, X'.cart τ = X.cart τ) (hY : ∀ τ, Y'.cart τ = Y.cart τ) :
    (sub X X' Y Y').comp (sub X' X Y' Y) = AlgHom.id ℂ (PolF D W.rank V.rank) := by
  refine MvPolynomial.algHom_ext fun v => ?_
  rw [AlgHom.comp_apply, AlgHom.id_apply]
  obtain ⟨ρ, i, j⟩ := v
  calc sub X X' Y Y' (sub X' X Y' Y (MvPolynomial.X (ρ, i, j)))
      = ∑ p : Fin W.rank × Fin V.rank, coef X' X Y' Y (ρ, i, j) p •
          ∑ q : Fin W.rank × Fin V.rank, coef X X' Y Y' (ρ, p.1, p.2) q •
            (MvPolynomial.X (ρ, q.1, q.2) : PolF D W.rank V.rank) := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [sub, MvPolynomial.aeval_X, map_sum, map_smul]
    _ = ∑ q : Fin W.rank × Fin V.rank, (∑ p : Fin W.rank × Fin V.rank,
          coef X' X Y' Y (ρ, i, j) p * coef X X' Y Y' (ρ, p.1, p.2) q) •
            (MvPolynomial.X (ρ, q.1, q.2) : PolF D W.rank V.rank) := by
        simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
        exact Finset.sum_comm
    _ = ∑ q : Fin W.rank × Fin V.rank, (if q = (i, j) then (1 : ℂ) else 0) •
            (MvPolynomial.X (ρ, q.1, q.2) : PolF D W.rank V.rank) := by
        simp only [coef_comp X X' Y Y' hX hY (ρ, i, j)]
    _ = MvPolynomial.X (ρ, i, j) := by
        rw [Finset.sum_eq_single (i, j)]
        · simp
        · intro q _ hq
          simp [hq]
        · simp

end GlobalTheory.FrameChange

namespace GlobalTheory.FrameChange

theorem ptF_frame_change : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (V W : HSp D) (A A' : Fr V) (B B' : Fr W), (∀ τ, A'.cart τ = A.cart τ) → (∀ τ, B'.cart τ = B.cart τ) → ∃ j : PolF D W.rank V.rank ≃ₗ[ℂ] PolF D W.rank V.rank, ∀ f, IsThetaFunO ψ V W f → ∀ P, ptF ψ θ A' B' f (j P) = ptF ψ θ A B f P := by
  intro D ψ θ hψ hθ V W A A' B B' hA hB
  let e : PolF D W.rank V.rank ≃ₐ[ℂ] PolF D W.rank V.rank :=
    AlgEquiv.ofAlgHom (sub A' A B' B) (sub A A' B B') (sub_comp A' A B' B (fun τ => (hA τ).symm) fun τ => (hB τ).symm)
      (sub_comp A A' B B' hA hB)
  refine ⟨e.toLinearEquiv, fun f hf P => ?_⟩
  exact (ptF_sub hψ hθ A' A B' B (fun τ => (hA τ).symm) (fun τ => (hB τ).symm) hf P).symm

end GlobalTheory.FrameChange

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorFrameChangeSameCartanStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockVector_frameChange_same_cartan : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (V W : HSp D) (A A' : Fr V) (B B' : Fr W), (∀ τ, A'.cart τ = A.cart τ) → (∀ τ, B'.cart τ = B.cart τ) → ∃ j : PolF D W.rank V.rank ≃ₗ[ℂ] PolF D W.rank V.rank, ∀ f, IsThetaFunO ψ V W f → ∀ P, ptF ψ θ A' B' f (j P) = ptF ψ θ A B f P := by
  first | exact @GlobalTheory.FrameChange.ptF_frame_change | exact GlobalTheory.FrameChange.ptF_frame_change | (intros; apply GlobalTheory.FrameChange.ptF_frame_change <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PoincareSumOverRationalHomThetaLawZeroCore
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PoincareSumOverRationalHomThetaLawZeroCore
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.BumpMix

namespace GlobalTheory.BumpMixQuasi

variable {D : D7}

theorem pair_add_left (T : HSp D) {ρ : ℕ} (x x' a : Mx D T.rank ρ) :
    trHalf D (pairS T (x + x') a) = trHalf D (pairS T x a) + trHalf D (pairS T x' a) := by
  rw [← map_add (f := _)]
  congr 1
  simp only [pairS, Matrix.mul_add, trace_add]

theorem pair_add_right (T : HSp D) {ρ : ℕ} (x a a' : Mx D T.rank ρ) :
    trHalf D (pairS T x (a + a')) = trHalf D (pairS T x a) + trHalf D (pairS T x a') := by
  rw [← map_add (f := _)]
  congr 1
  simp only [pairS, adj_add, Matrix.add_mul, trace_add]

theorem pair_sub_left (T : HSp D) {ρ : ℕ} (x x' a : Mx D T.rank ρ) :
    trHalf D (pairS T (x - x') a) = trHalf D (pairS T x a) - trHalf D (pairS T x' a) := by
  rw [eq_sub_iff_add_eq, ← pair_add_left, sub_add_cancel]

theorem pair_rat {S S₀ : HSp D} (T : HSp D) {ρ : ℕ} (d : HypDec S S₀ ρ) {x a : Mx D T.rank ρ}
    (hx : x ∈ ratMx D T.rank ρ) (ha : a ∈ ratMx D T.rank ρ) :
    ∃ c, trHalf D (pairS T x a) = algebraMap D.host.F (AF D.host.F) c := by
  rw [← d.symplOH_extX_extY]
  exact (GlobalTheory.OrientedFormLaws.symplOH_laws D S T).2.2.2.2.2.1 _ (ratMx_mul hx (rat_mem _)) _ (ratMx_mul ha (rat_mem _))

theorem symplOH_coords {S S₀ : HSp D} (T : HSp D) {ρ : ℕ} (d : HypDec S S₀ ρ) (h0 : S₀.rank = 0) (u w : WO S T) :
    symplOH S T u w = trHalf D (pairS T (u ⬝ d.jX) (w ⬝ d.jY)) - trHalf D (pairS T (w ⬝ d.jX) (u ⬝ d.jY)) := by
  have hz : ∀ v : WO S₀ T, v = 0 := fun v => by
    funext i j
    exact absurd j.2 (by omega)
  have e : ∀ v : WO S T, v = d.extX T (v ⬝ d.jX) + d.extY T (v ⬝ d.jY) := fun v => by
    have h := eq_coords d v
    rwa [hz (v ⬝ d.j0), map_zero, add_zero] at h
  conv_lhs => rw [e u, e w]
  rw [GlobalTheory.OrientedHeis.symplOH_add_left, GlobalTheory.OrientedHeis.symplOH_add_right, GlobalTheory.OrientedHeis.symplOH_add_right,
    d.symplOH_extX_extX, d.symplOH_extY_extY, d.symplOH_extX_extY, symplOH_Y_X]
  ring

theorem poinX_quasi : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), S₀.rank = 0 → ∀ (β : Mx D T.rank ρ → ℂ) (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (w : WO S T), poinX ψ d T β (ratW T S γ + w) = ψ (-(symplOH S T (ratW T S γ) w)) * poinX ψ d T β w := by
  intro D ψ hψ S S₀ T ρ d h0 β γ w
  obtain ⟨δ, hδ⟩ : (ratW T S γ : WO S T) ⬝ d.jX ∈ ratMx D T.rank ρ := ratMx_mul (rat_mem γ) (rat_mem _)
  have hδ' : (ratW T S γ : WO S T) ⬝ d.jX = rat δ := hδ.symm
  have ha : (ratW T S γ : WO S T) ⬝ d.jY ∈ ratMx D T.rank ρ := ratMx_mul (rat_mem γ) (rat_mem _)
  have eX : (ratW T S γ + w : WO S T) ⬝ d.jX = rat δ + w ⬝ d.jX := by
    rw [← hδ']; exact Matrix.add_mul _ _ _
  have eY : (ratW T S γ + w : WO S T) ⬝ d.jY = (ratW T S γ : WO S T) ⬝ d.jY + w ⬝ d.jY := Matrix.add_mul _ _ _
  rw [symplOH_coords T d h0, hδ']
  unfold poinX
  rw [eX, eY, ← (Equiv.subRight δ).tsum_eq, ← tsum_mul_left]
  generalize (ratW T S γ : WO S T) ⬝ d.jY = a at ha ⊢
  generalize w ⬝ d.jX = x
  generalize w ⬝ d.jY = y
  congr 1
  funext g
  rw [Equiv.subRight_apply, rat_sub]
  have e1 : rat δ + x + (rat g - rat δ) = x + rat g := by abel
  have e2 : rat δ + x + 2 • (rat g - rat δ) = x + 2 • rat g - rat δ := by
    rw [two_smul, two_smul]; abel
  have e3 : x + 2 • rat g - rat δ = x + (rat g + rat g - rat δ) := by
    rw [two_smul]; abel
  obtain ⟨c, hc⟩ := pair_rat T d (((ratMx D T.rank ρ).sub_mem ((ratMx D T.rank ρ).add_mem (rat_mem g) (rat_mem g))
    (rat_mem δ))) ha
  have e4 : trHalf D (pairS T (x + 2 • rat g - rat δ) (a + y)) =
      algebraMap D.host.F (AF D.host.F) c + (-(trHalf D (pairS T (rat δ) y) - trHalf D (pairS T x a)) +
        trHalf D (pairS T (x + 2 • rat g) y)) := by
    rw [pair_add_right, pair_sub_left T _ _ y, e3, pair_add_left T x _ a, hc]
    ring
  rw [e1, e2, e4, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, hψ.1.2.2.1 c]
  ring

end GlobalTheory.BumpMixQuasi

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PoincareSumOverRationalHomThetaLawZeroCoreStatement
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.BumpMix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.poincareSumOverRationalHom_thetaLaw_zeroCore : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), S₀.rank = 0 → ∀ (β : Mx D T.rank ρ → ℂ) (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (w : WO S T), poinX ψ d T β (ratW T S γ + w) = ψ (-(symplOH S T (ratW T S γ) w)) * poinX ψ d T β w := by
  first | exact @GlobalTheory.BumpMixQuasi.poinX_quasi | exact GlobalTheory.BumpMixQuasi.poinX_quasi | (intros; apply GlobalTheory.BumpMixQuasi.poinX_quasi <;> assumption)
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GaussianConjMonomialMomentEqTaylorCoefficient
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GaussianConjMonomialMomentEqTaylorCoefficient
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

noncomputable section

namespace GlobalTheory.FockMoment

variable {ι : Type} [Fintype ι] {a b : ℕ}

def unitPt (r : ι → ℝ) (u : DVar ι a b → ℂ) : VCx ι a b := fun τ β α => (r τ : ℂ)⁻¹ * u (τ, β, α)

def scalePt (r : ι → ℝ) (z : VCx ι a b) : DVar ι a b → ℂ := fun x => (r x.1 : ℂ) * z x.1 x.2.1 x.2.2

def scaleEquiv (r : ι → ℝ) (hr : ∀ τ, 0 < r τ) : VCx ι a b ≃ᵐ (DVar ι a b → ℂ) where
  toFun := scalePt r
  invFun := unitPt r
  left_inv z := by
    funext τ β α
    have : (r τ : ℂ) ≠ 0 := by exact_mod_cast (hr τ).ne'
    simp [unitPt, scalePt, this]
  right_inv u := by
    funext x
    have : (r x.1 : ℂ) ≠ 0 := by exact_mod_cast (hr x.1).ne'
    simp [unitPt, scalePt, this]
  measurable_toFun := (show Continuous (scalePt (a := a) (b := b) r) by unfold scalePt; fun_prop).measurable
  measurable_invFun := (show Continuous (unitPt (a := a) (b := b) r) by unfold unitPt; fun_prop).measurable

theorem scaleEquiv_apply (r : ι → ℝ) (hr : ∀ τ, 0 < r τ) (z : VCx ι a b) :
    scaleEquiv r hr z = scalePt r z := rfl

theorem unitPt_scalePt (r : ι → ℝ) (hr : ∀ τ, 0 < r τ) (z : VCx ι a b) :
    unitPt r (scalePt r z) = z := (scaleEquiv r hr).symm_apply_apply z

theorem volume_eq_smul_map (r : ι → ℝ) (hr : ∀ τ, 0 < r τ) :
    (volume : Measure (DVar ι a b → ℂ)) =
      ENNReal.ofReal (∏ x : DVar ι a b, r x.1 ^ 2) • (volume : Measure (VCx ι a b)).map (scaleEquiv r hr) := by
  rw [volume_pi]
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.smul_apply, Measure.map_apply (scaleEquiv r hr).measurable (MeasurableSet.univ_pi hs), smul_eq_mul]
  have e : (scaleEquiv r hr) ⁻¹' Set.univ.pi s = Set.univ.pi fun τ => Set.univ.pi fun β => Set.univ.pi fun α =>
      (fun w : ℂ => r τ • w) ⁻¹' s (τ, β, α) := by
    ext z
    simp [scaleEquiv_apply, scalePt, Set.mem_univ_pi, Prod.forall, Complex.real_smul]
  rw [e, volume_pi, Measure.pi_pi]
  simp_rw [volume_pi, Measure.pi_pi]
  rw [ENNReal.ofReal_prod_of_nonneg (fun x _ => sq_nonneg _)]
  simp_rw [Fintype.prod_prod_type]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun β _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun α _ => ?_
  rw [Measure.addHaar_preimage_smul _ (hr τ).ne', Complex.finrank_real_complex, ← mul_assoc,
    ← ENNReal.ofReal_mul (sq_nonneg _), abs_of_pos (by have := hr τ; positivity), mul_inv_cancel₀ (by have := hr τ; positivity),
    ENNReal.ofReal_one, one_mul]

theorem integral_unitPt (r : ι → ℝ) (hr : ∀ τ, 0 < r τ) (h : VCx ι a b → ℂ) :
    ∫ u : DVar ι a b → ℂ, h (unitPt r u) = ((∏ x : DVar ι a b, r x.1 ^ 2 : ℝ) : ℂ) * ∫ z, h z := by
  rw [volume_eq_smul_map r hr, integral_smul_measure, integral_map_equiv]
  have hP : 0 ≤ ∏ x : DVar ι a b, r x.1 ^ 2 := Finset.prod_nonneg fun _ _ => sq_nonneg _
  rw [ENNReal.toReal_ofReal hP, Complex.real_smul]
  simp only [scaleEquiv_apply, unitPt_scalePt r hr]

end GlobalTheory.FockMoment

namespace GlobalTheory.FockMoment

open Formalism.DimensionVariation (nsq mono cj mfact)

theorem gaussMoment : ∀ (ι : Type) [Fintype ι] (a b : ℕ) (c : ι → ℝ), (∀ τ, 0 < c τ) → ∀ G : VCx ι a b → ℂ, Differentiable ℂ G → (∃ M : ℝ, ∀ z, ‖G z‖ ≤ M * Real.exp (gq c z / 2)) → ∀ m : DVar ι a b →₀ ℕ, ∫ z, conjMono m z * (Real.exp (-gq c z) : ℂ) * G z = ((∏ τ, (Real.pi / c τ) ^ (a * b) : ℝ) : ℂ) * ((m.prod fun k n => (c k.1)⁻¹ ^ n : ℝ) : ℂ) * derivAt0 G m := by
  intro ι _ a b c hc G hG ⟨M, hM⟩ m
  classical
  set r : ι → ℝ := fun τ => Real.sqrt (c τ) with hr_def
  have hr : ∀ τ, 0 < r τ := fun τ => Real.sqrt_pos.2 (hc τ)
  have hr2 : ∀ τ, r τ ^ 2 = c τ := fun τ => Real.sq_sqrt (hc τ).le
  have hrC : ∀ τ, (r τ : ℂ) ≠ 0 := fun τ => by exact_mod_cast (hr τ).ne'
  set F : (DVar ι a b → ℂ) → ℂ := fun u => G fun τ β α => (r τ : ℂ)⁻¹ * u (τ, β, α) with hF_def
  have hFd : Differentiable ℂ F := hG.comp (by fun_prop)
  have hgq : ∀ u : DVar ι a b → ℂ, gq c (unitPt r u) = nsq u := by
    intro u
    simp only [gq, unitPt, nsq, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun α _ => ?_
    rw [norm_mul, mul_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, inv_pow, sq_abs, hr2, ← mul_assoc,
      mul_inv_cancel₀ (hc τ).ne', one_mul]
  have hmono : ∀ u : DVar ι a b → ℂ, conjMono m (unitPt r u) =
      (∏ x : DVar ι a b, ((r x.1 : ℂ)⁻¹) ^ m x) * mono (Formalism.DimensionVariation.cj u) m := by
    intro u
    rw [conjMono, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), mono, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun x _ => ?_
    simp [unitPt, Formalism.DimensionVariation.cj, mul_pow, Complex.conj_ofReal]
  have hgrow : ∀ u : DVar ι a b → ℂ, ‖F u‖ ≤ M * Real.exp (nsq u / 2) := fun u => by
    rw [← hgq u]; exact hM _
  have hfj := (Formalism.DimensionVariation.gaussianCoeffIntegral (DVar ι a b) F (GlobalTheory.IndefiniteRowSideFullHecke.TaylorCoefficientForms.taylorCoeff F) M hFd.continuous
    (GlobalTheory.JetFrameCompare.hasSum_taylorCoeff hFd) hgrow m).2
  have htj := GlobalTheory.JetBlock.taylor_jetC hG r hr (fun _ => 1) m
  simp only [Formalism.L2.Ker.jetC, one_pow, one_mul] at htj
  rw [Finsupp.prod_fintype _ _ (fun _ => rfl), Finset.prod_const_one, one_mul] at htj
  have hcov := integral_unitPt r hr (fun z => conjMono m z * (Real.exp (-gq c z) : ℂ) * G z)
  have hint : ∫ u : DVar ι a b → ℂ, conjMono m (unitPt r u) * (Real.exp (-gq c (unitPt r u)) : ℂ) * G (unitPt r u) =
      (∏ x : DVar ι a b, ((r x.1 : ℂ)⁻¹) ^ m x) * ∫ u, F u * mono (Formalism.DimensionVariation.cj u) m * (Real.exp (-(nsq u)) : ℂ) := by
    rw [← integral_const_mul]
    congr 1
    funext u
    have hFu : F u = G (unitPt r u) := rfl
    rw [hmono, hgq, hFu]
    ring
  rw [hint, hfj] at hcov
  have htj' : GlobalTheory.IndefiniteRowSideFullHecke.TaylorCoefficientForms.taylorCoeff F m * (mfact m : ℂ) * ∏ x : DVar ι a b, (r x.1 : ℂ) ^ m x = derivAt0 G m := htj
  have hPpos : 0 < ∏ x : DVar ι a b, r x.1 ^ 2 := Finset.prod_pos fun x _ => by have := hr x.1; positivity
  have hP : (∏ x : DVar ι a b, r x.1 ^ 2) = ∏ x : DVar ι a b, c x.1 := Finset.prod_congr rfl fun x _ => hr2 x.1
  have hpi : (∏ τ, (Real.pi / c τ) ^ (a * b) : ℝ) =
      Real.pi ^ Fintype.card (DVar ι a b) * (∏ x : DVar ι a b, r x.1 ^ 2)⁻¹ := by
    rw [hP]
    simp only [Fintype.prod_prod_type, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Fintype.card_prod]
    simp_rw [div_pow]
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, ← pow_mul, div_eq_mul_inv, mul_comm b a,
      mul_comm (a * b) (Fintype.card ι)]
  have hmp : ((m.prod fun k n => (c k.1)⁻¹ ^ n : ℝ) : ℂ) = (∏ x : DVar ι a b, ((r x.1 : ℂ)⁻¹) ^ m x) ^ 2 := by
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    push_cast
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun x _ => ?_
    rw [← hr2 x.1]
    push_cast
    ring
  have hPC : ((∏ x : DVar ι a b, r x.1 ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hPpos.ne'
  have hRR : (∏ x : DVar ι a b, (r x.1 : ℂ) ^ m x) * (∏ x : DVar ι a b, ((r x.1 : ℂ)⁻¹) ^ m x) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun x _ => by rw [← mul_pow, mul_inv_cancel₀ (hrC x.1), one_pow]
  have hPinv := mul_inv_cancel₀ hPC
  rw [hpi, hmp, ← htj']
  apply mul_left_cancel₀ hPC
  rw [← hcov, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_pow]
  set P := ((∏ x : DVar ι a b, r x.1 ^ 2 : ℝ) : ℂ) with hP_def
  set R := ∏ x : DVar ι a b, (r x.1 : ℂ) ^ m x with hR_def
  set Ri := ∏ x : DVar ι a b, ((r x.1 : ℂ)⁻¹) ^ m x with hRi_def
  set TM := GlobalTheory.IndefiniteRowSideFullHecke.TaylorCoefficientForms.taylorCoeff F m * (mfact m : ℂ) with hTM
  set K := (Real.pi : ℂ) ^ Fintype.card (DVar ι a b) with hK
  linear_combination (-(K * TM * Ri)) * hRR + (-(K * TM * Ri ^ 2 * R)) * hPinv
end GlobalTheory.FockMoment
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GaussianConjMonomialMomentEqTaylorCoefficientStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussian_conjMonomial_moment_eq_taylor_coefficient : ∀ (ι : Type) [Fintype ι] (a b : ℕ) (c : ι → ℝ), (∀ τ, 0 < c τ) → ∀ G : VCx ι a b → ℂ, Differentiable ℂ G → (∃ M : ℝ, ∀ z, ‖G z‖ ≤ M * Real.exp (gq c z / 2)) → ∀ m : DVar ι a b →₀ ℕ, ∫ z, conjMono m z * (Real.exp (-gq c z) : ℂ) * G z = ((∏ τ, (Real.pi / c τ) ^ (a * b) : ℝ) : ℂ) * ((m.prod fun k n => (c k.1)⁻¹ ^ n : ℝ) : ℂ) * derivAt0 G m := by
  first | exact @GlobalTheory.FockMoment.gaussMoment | exact GlobalTheory.FockMoment.gaussMoment | (intros; apply GlobalTheory.FockMoment.gaussMoment <;> assumption)
end
end
