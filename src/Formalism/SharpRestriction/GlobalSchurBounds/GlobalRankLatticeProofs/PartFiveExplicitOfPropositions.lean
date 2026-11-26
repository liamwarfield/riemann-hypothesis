module

public import Formalism.SharpRestriction.GlobalSchurBounds.TheoremThreeOfExplicitAndCompact
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.SecondPropositionEveryLocalisation
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.UnitaryKronecker

@[expose] public section

section -- merged from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.PartFiveExplicitOfPropositions
noncomputable section
namespace Formalism.MainNotions.StandardLattice
open NumberField Formalism.BasicNotions Finset

section P3
open Formalism.MainNotions.S MeasureTheory
open scoped InnerProductSpace

theorem signature_counts_ge_one (D : D7) : 1 ≤ pY D ∧ 1 ≤ qY D := by
  unfold pY qY
  simp only [Formalism.BasicNotions.Ranks.sigY0]
  have := D.R.m_add_three_le_k
  constructor <;> omega

end P3

theorem explicit_gap_le_general_gap (D : D7) (C ep0 : ℝ) (hC : 8192 ≤ C) : spectralGapLowerBound D ep0 ≤ gap3 D C ep0 := by
  unfold spectralGapLowerBound gap3
  have hr1 : (1 : ℝ) ≤ D.R.r := by
    have : 1 ≤ D.R.r := by
      simp only [Formalism.BasicNotions.Ranks.r]
      have := D.R.m_add_three_le_k
      omega
    exact_mod_cast this
  have hlog : 0 ≤ Real.log D.R.r := Real.log_nonneg hr1
  have hX : 0 ≤ (↑(min (pY D) (qY D)) : ℝ) * (↑(pY D) * ↑(qY D)) ^ 3 := by positivity
  apply div_le_div_of_nonneg_right ?_ (sq_nonneg ep0)
  have h1 : (8192 : ℝ) ≤ C * D.R.r := by nlinarith
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (mul_nonneg hX hlog)]

theorem weighted_log_sum_lower_bound (D : D7) (w : ℕ → D.what₂.Tau → ℝ) (w0 : ℝ) (hw0 : 0 < w0) (hpi : Real.pi ≤ D.host.v)
    (hw : ∀ ρ j, j < D.R.m → w0 ≤ w j ρ) :
    (D.R.m : ℝ) * Real.log w0 ≤
      ∑ j ∈ range D.R.m, (1 / (D.R.f : ℝ)) * ∑ ρ, Real.log (w j ρ * D.host.v / Real.pi) := by
  have hf : (0 : ℝ) < D.R.f := by exact_mod_cast degree_pos_alt D
  have hv : 1 ≤ D.host.v / Real.pi := (one_le_div Real.pi_pos).2 hpi
  have hterm : ∀ j, j < D.R.m → (Fintype.card D.what₂.Tau : ℝ) * Real.log w0 ≤
      ∑ ρ, Real.log (w j ρ * D.host.v / Real.pi) := by
    intro j hj
    rw [← nsmul_eq_mul, ← Finset.card_univ, ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro ρ _
    apply Real.log_le_log hw0
    rw [mul_div_assoc]
    calc w0 = w0 * 1 := (mul_one _).symm
      _ ≤ w j ρ * (D.host.v / Real.pi) :=
        mul_le_mul (hw ρ j hj) hv zero_le_one (by linarith [hw ρ j hj])
  rw [D.what₂.card_Tau] at hterm
  calc (D.R.m : ℝ) * Real.log w0 =
        ∑ j ∈ range D.R.m, (1 / (D.R.f : ℝ)) * ((D.R.f : ℝ) * Real.log w0) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, one_div, inv_mul_cancel_left₀ hf.ne']
    _ ≤ _ := Finset.sum_le_sum fun j hj =>
        mul_le_mul_of_nonneg_left (hterm j (Finset.mem_range.1 hj)) (by positivity)

theorem weights_ge_one_section_B (D : D7) (sc : Scale) (C0 Δ : ℝ) (w : ℕ → D.what₂.Tau → ℝ) (hB : DataB D sc C0 Δ w)
    (ρ : D.what₂.Tau) (j : ℕ) (hj : j < D.R.m) : 1 ≤ w j ρ := by
  obtain ⟨-, -, -, -, -, -, hΔ, -, -, -, -, -, hw, hwb, hb0, -⟩ := hB
  have hk : (1 : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k
    exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hx := sc.one_lt_alt
  have hbase : 1 ≤ bN D ρ 0 := by
    have h := (hb0 ρ).1
    rw [le_div_iff₀ (by linarith)] at h
    have h4 : (1 : ℝ) ≤ D.R.k * (4 * Δ) := by nlinarith
    have h5 : (D.R.k : ℝ) * (4 * Δ) ≤ D.R.k * (4 * Δ) * sc.x :=
      le_mul_of_one_le_right (by positivity) hx.le
    linarith
  have hmono : ∀ i, i < D.R.m → bN D ρ 0 ≤ bN D ρ i := by
    intro i
    induction i with
    | zero => intro _; exact le_rfl
    | succ i ih =>
      intro hi
      have h1 := ih (by omega)
      have h2 := (hw ρ i (by omega)).2.1
      have h3 := hwb ρ i hi
      linarith
  linarith [(hw ρ j hj).2.1, hmono j hj]

theorem eight_L_le_log_g (D : D7) (sc : Scale) (C0 Δ : ℝ) (w : ℕ → D.what₂.Tau → ℝ) (hB : DataB D sc C0 Δ w) (i : Fin 2) :
    8 * sc.L ≤ Real.log (D.host.g i : ℝ) := by
  obtain ⟨-, -, -, -, -, hg, -⟩ := hB
  have hk : (1 : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k
    exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hb : 0 < sc.b := Real.exp_pos _
  have h1 := (hg i).1
  have hpos : 0 < ((D.R.k : ℝ) * sc.b) ^ 8 := by positivity
  calc 8 * sc.L = Real.log (sc.b ^ 8) := by
        rw [Real.log_pow, Formalism.BasicNotions.Scale.b, Real.log_exp]
        norm_num
    _ ≤ Real.log (((D.R.k : ℝ) * sc.b) ^ 8) :=
        Real.log_le_log (by positivity) (pow_le_pow_left₀ hb.le (by nlinarith) 8)
    _ ≤ Real.log (D.host.g i : ℝ) := Real.log_le_log hpos h1

theorem corollary_five_four_of_explicit (D : D7) (sc : Scale) (C0 CY : ℝ) (h5 : Conclusion5Sharp D sc C0 CY) : VandermondeCountExplicit D sc C0 CY := by
  intro Δ w hA Γ hΓ u hT2 hf2 hT1 hT3
  have hB := hA.1
  have hg := three_le_level_of_section_B D sc C0 Δ w hB
  have hD := dual_degree_pos D hg
  have hd := dual_degree_word_pos D hg (massI_pos D D.R.k) u
  have hk := D.R.k_ge
  have hf : 1 ≤ D.R.f := le_trans one_le_two (le_trans D.R.two_le_m D.R.m_le_f)
  have hfk : 2 * D.R.f ≤ 2 ^ D.R.k := by
    have h3 : 2 ^ D.R.k = 2 * 2 ^ (D.R.k - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega
  have hX : Real.exp (logXuD D u) ^ (D.R.f * D.R.k) = DstarD D / duStarU D u := by
    have hfR : (0 : ℝ) < D.R.f := by exact_mod_cast hf
    have hkR : (0 : ℝ) < D.R.k := by exact_mod_cast (by omega : 0 < D.R.k)
    rw [← Real.exp_nat_mul]
    unfold logXuD logXu
    push_cast
    rw [show (D.R.f : ℝ) * D.R.k * (1 / ((D.R.f : ℝ) * D.R.k) * Real.log (DstarD D / duStarU D u)) =
      Real.log (DstarD D / duStarU D u) by field_simp]
    exact Real.exp_log (div_pos hD hd)
  have hT : (2 : ℝ) ≤ ((D.mem u).A.T : ℝ) := by exact_mod_cast hT2
  obtain ⟨c1, c2, c3, c4⟩ := Formalism.HermitianLattices.GenusMassVolumes.mass_corollary D.R.f D.R.k ((D.mem u).A.T : ℝ) (Real.exp (logXuD D u)) Γ
    (DstarD D) (duStarU D u) _ (logXuD D u) (logXuD D u) hf (by omega) hfk hT (Real.exp_pos _) hΓ hD hd hX
    hT1 hT3 rfl (by rw [Real.log_exp]) (by rw [Real.log_exp])
  have hL := scale_one_le_L sc
  have hlog2 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
  have hΓ0 : 0 < Γ := by linarith
  have eΓ : Γ ^ (-(2 : ℝ)) = (Γ⁻¹) ^ 2 := by
    rw [Real.rpow_neg hΓ0.le, Real.rpow_two, inv_pow]
  have l1 := (h5 Δ w hA u).1
  refine ⟨⟨by rw [eΓ]; exact c1, by rw [eΓ]; exact c2⟩, by linarith, by linarith, fun hG => ⟨c4, by linarith, ?_⟩⟩
  have hm : (44 : ℝ) ≤ D.R.m := by exact_mod_cast hA.2.2.2.1
  have s1 := weighted_log_sum_lower_bound D w 1 one_pos hB.1 (fun ρ j hj => weights_ge_one_section_B D sc C0 Δ w hB ρ j hj)
  rw [Real.log_one, mul_zero] at s1
  have s2 : 16 * sc.L ≤ ∑ i : Fin 2, Real.log (D.host.g i : ℝ) := by
    rw [Fin.sum_univ_two]
    have := eight_L_le_log_g D sc C0 Δ w hB 0
    have := eight_L_le_log_g D sc C0 Δ w hB 1
    linarith
  unfold lowS at l1
  have s3 : (D.R.m : ℝ) * (16 * sc.L) ≤ (D.R.m : ℝ) * ∑ i : Fin 2, Real.log (D.host.g i : ℝ) :=
    mul_le_mul_of_nonneg_left s2 (by linarith)
  nlinarith

theorem part_five_explicit_of_propositions (D : D7) (sc : Scale) (C0 CY : ℝ) (h5 : Conclusion5Sharp D sc C0 CY) (hv : VandermondeVariationExplicitBound D sc C0 CY) :
    VandermondeCountBound D sc C0 CY := ⟨h5, corollary_five_six_of_explicit D sc C0 CY h5, corollary_five_four_of_explicit D sc C0 CY h5, hv⟩

end Formalism.MainNotions.StandardLattice
end
end

section -- merged from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.LemmaOneEightOfPolarisation
noncomputable section

namespace Formalism.MainNotions.UnusedSlot33

open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.TwoAdicCyclotomicDecomposition Ideal IntermediateField
open scoped Pointwise
open Formalism.MainNotions.UnusedSlot33.SlopeTestRemainingChoices

namespace CMIdealEquivalence

theorem mult_ring {M : Type} [Field M] [NumberField M]
    (I : FractionalIdeal (nonZeroDivisors (𝓞 M)) M) (hI : I ≠ 0) (x : M) :
    (∀ y ∈ I, x * y ∈ I) ↔ IsIntegral ℤ x := by
  constructor
  · intro h
    have hi : IsIntegral (𝓞 M) x :=
      isIntegral_of_smul_mem_submodule (I : Submodule (𝓞 M) M)
        (fun h0 => hI (FractionalIdeal.coeToSubmodule_eq_bot.1 h0))
        (FractionalIdeal.fg_of_isNoetherianRing le_rfl I) x (fun n hn => h n hn)
    obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
    exact NumberField.RingOfIntegers.isIntegral_coe y
  · intro hx y hy
    have : (⟨x, hx⟩ : 𝓞 M) • y ∈ (I : Submodule (𝓞 M) M) :=
      Submodule.smul_mem (I : Submodule (𝓞 M) M) _ hy
    exact this

private theorem mem_one_iff'' {M : Type} [Field M] [NumberField M] (t : M) :
    t ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 M)) M) ↔ IsIntegral ℤ t := by
  rw [FractionalIdeal.mem_one_iff]
  constructor
  · rintro ⟨x', rfl⟩
    exact NumberField.RingOfIntegers.isIntegral_coe x'
  · intro h
    exact ⟨⟨t, h⟩, rfl⟩

private theorem integ_iff' {M : Type} [Field M] [NumberField M] (σ : M ≃ₐ[ℚ] M) (t : M) :
    IsIntegral ℤ (σ t) ↔ IsIntegral ℤ t :=
  isIntegral_algEquiv (σ.restrictScalars ℤ)

private theorem smul_ne_bot' {M : Type} [Field M] [NumberField M] (σ : M ≃ₐ[ℚ] M)
    (B : Ideal (𝓞 M)) (hB : B ≠ ⊥) : σ • B ≠ ⊥ := by
  intro h
  apply hB
  have h2 : σ⁻¹ • (σ • B) = σ⁻¹ • (⊥ : Ideal (𝓞 M)) := by rw [h]
  rwa [inv_smul_smul, Ideal.pointwise_smul_def, Ideal.map_bot] at h2

private theorem mem_inv_smul' {M : Type} [Field M] [NumberField M] (σ : M ≃ₐ[ℚ] M)
    (B : Ideal (𝓞 M)) (hB : B ≠ ⊥) (y : M) :
    σ y ∈ ((σ • B : Ideal (𝓞 M)) : FractionalIdeal (nonZeroDivisors (𝓞 M)) M)⁻¹ ↔
      y ∈ ((B : FractionalIdeal (nonZeroDivisors (𝓞 M)) M))⁻¹ := by
  have hc : ∀ b : 𝓞 M, algebraMap (𝓞 M) M (σ • b) = σ (algebraMap (𝓞 M) M b) := fun b => rfl
  have h1 : ((σ • B : Ideal (𝓞 M)) : FractionalIdeal (nonZeroDivisors (𝓞 M)) M) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (smul_ne_bot' σ B hB)
  have h2 : ((B : Ideal (𝓞 M)) : FractionalIdeal (nonZeroDivisors (𝓞 M)) M) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 hB
  rw [FractionalIdeal.mem_inv_iff h1, FractionalIdeal.mem_inv_iff h2]
  constructor
  · intro h z hz
    obtain ⟨b, hb, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hz
    have := h (σ (algebraMap (𝓞 M) M b)) ((FractionalIdeal.mem_coeIdeal _).2
      ⟨σ • b, Ideal.smul_mem_pointwise_smul σ b B hb, hc b⟩)
    rw [mem_one_iff'', ← map_mul, integ_iff'] at this
    rw [mem_one_iff'']
    exact this
  · intro h z hz
    obtain ⟨c, hc', rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hz
    have hb : σ⁻¹ • c ∈ B := Ideal.mem_pointwise_smul_iff_inv_smul_mem.1 hc'
    have := h _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨_, hb, rfl⟩)
    rw [mem_one_iff''] at this ⊢
    have e : algebraMap (𝓞 M) M c = σ (algebraMap (𝓞 M) M (σ⁻¹ • c)) := by
      rw [← hc, smul_inv_smul]
    rw [e, ← map_mul, integ_iff']
    exact this

theorem conj_conj (D : D7) (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  show (D.host.conj * D.host.conj) x = x
  rw [show D.host.conj * D.host.conj = 1 by
    simp only [Formalism.HC.HostRaw.conj, ← map_mul, Formalism.HC.Frame.cc_mul_cc, map_one]]
  rfl

theorem b_ne_bot (D : D7) : D.host.𝔟 ≠ ⊥ := by
  intro h
  have h2 := D.host.𝔟_spec.2
  rw [h, Ideal.pointwise_smul_def, Ideal.map_bot, bot_sup_eq] at h2
  exact bot_ne_top h2

theorem ordinary (D : D7) : ∀ p : ℕ, p.Prime →
    (primesOver (span {(p : ℤ)}) (𝓞 D.host.K)).ncard = 2 →
      ∀ P : Ideal (𝓞 D.host.E), P.IsPrime → P.LiesOver (span {(p : ℤ)}) →
        ∀ σ τ : D.host.E ≃ₐ[ℚ] D.host.E, τ ∈ MulAction.stabilizer (D.host.E ≃ₐ[ℚ] D.host.E) P →
          (D.host.galE (σ * τ) ∈ D.R.Psi ↔
            D.host.galE σ ∈ D.R.Psi) := by
  intro p hp hK P hP hl σ τ hτ
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := hP
  haveI := hl
  exact (D.host.der.ordinary p P).2 hK σ τ hτ

end CMIdealEquivalence

open CMIdealEquivalence

def PolPart (D : D7) : Prop :=
  ∀ cc : Ideal (𝓞 D.host.K), cc ≠ ⊥ →
    ∃ ξ : D.host.E, ξ ∈ D.host.K ∧ D.host.conj ξ = -ξ ∧ (∀ φ ∈ PhiEmb D, 0 < (φ ξ).im) ∧
      ∀ y : D.host.E,
        y ∈ ((Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc : Ideal (𝓞 D.host.E)) :
          FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) * D.host.AA0 ↔
        ∀ x ∈ ((Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc : Ideal (𝓞 D.host.E)) :
          FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) * D.host.AA0,
          Algebra.trace ℚ D.host.E (ξ * D.host.conj x * y) ∈ (algebraMap ℤ ℚ).range

theorem lemma_one_eight_of_polarisation (D : D7) (hPol : PolPart D) : Conclusion8 D := by
  have hb := b_ne_bot D
  have hσb : D.host.conj • D.host.𝔟 ≠ ⊥ := smul_ne_bot' D.host.conj _ hb
  have hb0 : ((D.host.𝔟 : Ideal (𝓞 D.host.E)) :
      FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 hb
  refine ⟨D.host.AA0, ((D.host.conj • D.host.𝔟 : Ideal (𝓞 D.host.E)) :
    FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)⁻¹, ?_, ?_, ?_, ordinary D⟩
  · intro x
    have hσσ : D.host.conj • D.host.conj • D.host.𝔟 = D.host.𝔟 := by
      rw [smul_smul, show D.host.conj * D.host.conj = 1 from AlgEquiv.ext (conj_conj D), one_smul]
    have h := mem_inv_smul' D.host.conj (D.host.conj • D.host.𝔟) hσb x
    rw [hσσ] at h
    exact h.symm
  · rw [D.host.𝔟_spec.1, FractionalIdeal.coeIdeal_mul, mul_inv]
    try rfl
  · intro cc hcc
    have hm : Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc ≠ ⊥ :=
      Ideal.map_ne_bot_of_ne_bot hcc
    have hne : ((Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc : Ideal (𝓞 D.host.E)) :
        FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) * D.host.AA0 ≠ 0 :=
      mul_ne_zero (FractionalIdeal.coeIdeal_ne_zero.2 hm) (inv_ne_zero hb0)
    exact ⟨fun x => mult_ring _ hne x, hPol cc hcc⟩

end Formalism.MainNotions.UnusedSlot33

end
end

section -- merged from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.NoThreeConsecutiveThickPlaces
noncomputable section

namespace Formalism.MainNotions.UnusedSlot33

open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.TwoAdicCyclotomicDecomposition Ideal
open Formalism.MainNotions.UnusedSlot33.SlopeTestRemainingChoices

def InertPart (D : D7) : Prop :=
  ∀ φ₀ : G0, (φ₀ = c0 ∨ φ₀ = sgc0) → ∀ h : HH D,
    (∀ p : ℕ, p.Prime → (span {(p : ℤ)}).ramificationIdxIn (𝓞 D.host.E) = 1 →
      frob D p = gOf D φ₀ h →
      ∀ 𝔭 : Ideal (𝓞 D.host.F), 𝔭.IsPrime → 𝔭.LiesOver (span {(p : ℤ)}) →
        (Inert D 𝔭 ↔ φ₀ = c0 ∧ Odd (addOrderOf h)))

theorem tau_one_mem_orbit_set (φ : Formalism.HC.Frame) (t : φ.A) : φ.tau1 t ∈ φ.Psi := by
  show φ.chD (φ.tau1 t) = 1
  rfl

private theorem neg_one_of_ne {x : ℤˣ} (h : x ≠ 1) : x = -1 := by
  rcases Int.units_eq_one_or x with hx | hx
  · exact absurd hx h
  · exact hx

private theorem no_three (R : Formalism.HC.Frame) {L : ℕ} (T : Finset ℕ) (hTr : ∀ s ∈ T, 4 * L * s < R.n0)
    (hTn : NoRel T L) (u0 : R.A) (hL : 3 ≤ L) (φ : R.GG) (hφ : φ ∉ R.Psi) (hφc : φ ≠ R.cc)
    (τ : R.GG) (hτ : τ ∈ R.Psi) (i : ℕ)
    (h0 : ∃ s ∈ T, Formalism.HC.Frame.placeOf (φ ^ i * τ) = R.tau2 (R.dig s + u0))
    (h1 : ∃ s ∈ T, Formalism.HC.Frame.placeOf (φ ^ (i + 1) * τ) = R.tau2 (R.dig s + u0))
    (h2 : ∃ s ∈ T, Formalism.HC.Frame.placeOf (φ ^ (i + 2) * τ) = R.tau2 (R.dig s + u0)) : False := by
  have key : ∀ (y : R.GG), (Formalism.HC.Frame.placeOf y).1.1 = -1 →
      (Formalism.HC.Frame.placeOf (φ * y)).1.1 = -1 → φ.1.1 = -1 := by
    intro y h0 h1
    have hφ2 : φ.1.2 = -1 := neg_one_of_ne hφ
    simp only [Formalism.HC.Frame.placeOf] at h0 h1
    rcases Int.units_eq_one_or y.1.2 with hy | hy
    · rw [if_pos hy] at h0
      have hm : (φ * y).1.2 = -1 := by
        simp [Prod.fst_mul, Prod.snd_mul, hφ2, hy]
      rw [if_neg (by rw [hm]; decide)] at h1
      simpa [Formalism.HC.Frame.cc, c0, Prod.fst_mul, Prod.snd_mul, h0] using h1
    · rw [if_neg (by rw [hy]; decide)] at h0
      have hm : (φ * y).1.2 = 1 := by
        simp [Prod.fst_mul, Prod.snd_mul, hφ2, hy]
      rw [if_pos hm] at h1
      have h0' : y.1.1 = 1 := by
        simpa [Formalism.HC.Frame.cc, c0, Prod.fst_mul, Prod.snd_mul] using h0
      simpa [Prod.fst_mul, h0'] using h1
  have hφ2 : φ.1.2 = -1 := neg_one_of_ne hφ
  obtain ⟨s1, hs1, e1⟩ := h0
  obtain ⟨s2, hs2, e2⟩ := h1
  obtain ⟨s3, hs3, e3⟩ := h2
  have hφ1 : φ.1.1 = -1 := key (φ ^ i * τ) (by rw [e1]; rfl)
    (by rw [← mul_assoc, ← pow_succ', e2]; rfl)
  have E : ∀ (k s : ℕ), Formalism.HC.Frame.placeOf (φ ^ k * τ) = R.tau2 (R.dig s + u0) →
      k • R.iotaInv φ.2 + R.iotaInv τ.2 = R.dig s + u0 := by
    intro k s hk
    have this : R.iotaInv (Formalism.HC.Frame.placeOf (φ ^ k * τ)).2 = R.iotaInv (R.tau2 (R.dig s + u0)).2 := by
      rw [hk]
    rw [Formalism.HC.Frame.placeOf_snd, Prod.snd_mul, Prod.pow_snd, Formalism.HC.Frame.iotaInv_mul,
      Formalism.HC.Frame.iotaInv_pow] at this
    change _ = R.iotaInv (R.iota _) at this
    rw [Formalism.HC.Frame.iotaInv_iota] at this
    exact this
  have E1 := E i s1 e1
  have E2 := E (i + 1) s2 e2
  have E3 := E (i + 2) s3 e3
  set x := R.iotaInv φ.2 with hxdef
  set T0 := R.iotaInv τ.2
  have hx1 : R.dig s2 - R.dig s1 = x := by
    have a : R.dig s2 = ((i + 1) • x + T0) - u0 := by rw [E2]; abel
    have b : R.dig s1 = (i • x + T0) - u0 := by rw [E1]; abel
    rw [a, b, succ_nsmul]
    abel
  have hx2 : R.dig s3 - R.dig s2 = x := by
    have a : R.dig s3 = ((i + 2) • x + T0) - u0 := by rw [E3]; abel
    have b : R.dig s2 = ((i + 1) • x + T0) - u0 := by rw [E2]; abel
    rw [a, b, show i + 2 = (i + 1) + 1 from rfl, succ_nsmul]
    abel
  have hx0 : x ≠ 0 := by
    intro h0
    apply hφc
    have h2 : φ.2 = 1 := (R.iotaInv_eq_zero_iff _).1 h0
    exact Prod.ext (Prod.ext hφ1 hφ2) h2
  have hzero : ((s1 : ℤ) + s3 - s2 - s2) • R.a0 = 0 := by
    rw [sub_zsmul, sub_zsmul, add_zsmul, natCast_zsmul, natCast_zsmul, natCast_zsmul]
    change R.dig s1 + R.dig s3 + -R.dig s2 + -R.dig s2 = 0
    have : R.dig s1 + R.dig s3 + -R.dig s2 + -R.dig s2 =
        (R.dig s3 - R.dig s2) - (R.dig s2 - R.dig s1) := by abel
    rw [this, hx1, hx2, sub_self]
  have hdvd : (R.n0 : ℤ) ∣ (s1 : ℤ) + s3 - s2 - s2 := addOrderOf_dvd_iff_zsmul_eq_zero.2 hzero
  have b1 := hTr s1 hs1
  have b2 := hTr s2 hs2
  have b3 := hTr s3 hs3
  have c1 : 12 * s1 ≤ 4 * L * s1 := Nat.mul_le_mul_right s1 (by omega)
  have c2 : 12 * s2 ≤ 4 * L * s2 := Nat.mul_le_mul_right s2 (by omega)
  have c3 : 12 * s3 ≤ 4 * L * s3 := Nat.mul_le_mul_right s3 (by omega)
  have habs : |(s1 : ℤ) + s3 - s2 - s2| < R.n0 := abs_lt.2 ⟨by omega, by omega⟩
  have hrel : (s1 : ℤ) + s3 - s2 - s2 = 0 := Int.eq_zero_of_abs_lt_dvd hdvd habs
  have n12 : s1 ≠ s2 := by
    rintro rfl
    exact hx0 (by rw [← hx1, sub_self])
  have n23 : s2 ≠ s3 := by
    rintro rfl
    exact hx0 (by rw [← hx2, sub_self])
  have n13 : s1 ≠ s3 := by
    rintro rfl
    apply n12
    omega
  apply hTn s1 hs1 s2 hs2 s3 hs3 n12 n13 n23 1 2 (by norm_num) (by norm_num; omega) (by norm_num)
    (by norm_num; omega) (by norm_num)
  linarith

theorem even_addOrderOf_of_h_ne_zero (D : D7) {h : D.R.A} (hh : D.R.h h ≠ 0) : Even (addOrderOf h) := by
  have h1 : addOrderOf (D.R.h h) ∣ addOrderOf h := addOrderOf_map_dvd D.R.h h
  have h2 : addOrderOf (D.R.h h) ∣ 2 ^ D.R.e := by
    have := D.R.orderOf_H_dvd (Additive.toMul (D.R.h h))
    rwa [← addOrderOf_ofMul_eq_orderOf, ofMul_toMul] at this
  have h3 : addOrderOf (D.R.h h) ≠ 1 := by
    intro hx
    apply hh
    have := addOrderOf_nsmul_eq_zero (D.R.h h)
    rwa [hx, one_nsmul] at this
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact h3 (by simpa using hk')
  rw [even_iff_two_dvd]
  refine dvd_trans ?_ h1
  rw [hk']
  exact dvd_pow_self 2 hk0

theorem cc_mem_zpowers_gOf (D : D7) (φ₀ : G0) (h : HH D) :
    D.R.cc ∈ Subgroup.zpowers (gOf D φ₀ h) ↔ φ₀ = c0 ∧ Odd (addOrderOf h) := by
  have hu : ∀ (u : ℤˣ) (k : ℤ), u ^ k = -1 → u = -1 ∧ Odd k := by
    intro u k huk
    rcases Int.units_eq_one_or u with rfl | rfl
    · rw [one_zpow] at huk
      exact absurd huk (by decide)
    · refine ⟨rfl, ?_⟩
      rcases Int.even_or_odd k with he | ho
      · rw [he.neg_one_zpow] at huk
        exact absurd huk (by decide)
      · exact ho
  have hc0sq : c0 ^ 2 = 1 := by
    ext <;> simp [c0]
  rw [Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, hk⟩
    have e1 : φ₀ ^ k = c0 := congrArg Prod.fst hk
    have e2 : (Multiplicative.ofAdd h) ^ k = 1 := congrArg Prod.snd hk
    have e2' : k • h = 0 := by
      have := congrArg Multiplicative.toAdd e2
      simpa using this
    have a1 := hu _ _ (congrArg Prod.fst e1)
    have a2 := hu _ _ (congrArg Prod.snd e1)
    refine ⟨Prod.ext a1.1 a2.1, ?_⟩
    have hd : (addOrderOf h : ℤ) ∣ k := addOrderOf_dvd_iff_zsmul_eq_zero.2 e2'
    have hd' : addOrderOf h ∣ k.natAbs := Int.natCast_dvd.1 hd
    exact Odd.of_dvd_nat (Int.natAbs_odd.2 a1.2) hd'
  · rintro ⟨rfl, hodd⟩
    refine ⟨(addOrderOf h : ℤ), ?_⟩
    refine Prod.ext ?_ ?_
    · change c0 ^ ((addOrderOf h : ℕ) : ℤ) = c0
      rw [zpow_natCast]
      obtain ⟨m, hm⟩ := hodd
      rw [hm, pow_succ, pow_mul, hc0sq, one_pow, one_mul]
    · change (Multiplicative.ofAdd h) ^ ((addOrderOf h : ℕ) : ℤ) = 1
      rw [zpow_natCast, ← ofAdd_nsmul, addOrderOf_nsmul_eq_zero, ofAdd_zero]

theorem lemma_one_three_of_inert (D : D7) (hI : InertPart D) : PointsLemma D := by
  intro φ₀ hφ₀ h
  have hg1 : (gOf D φ₀ h).1 = φ₀ := rfl
  have hsg : sgc0 = ((1 : ℤˣ), (-1 : ℤˣ)) := by
    ext <;> simp [sgc0, c0]
  have hg : (gOf D φ₀ h).1 = c0 ∨ (gOf D φ₀ h).1 = ((1 : ℤˣ), (-1 : ℤˣ)) := by
    rw [hg1, ← hsg]
    exact hφ₀
  have hchg : D.R.chD (gOf D φ₀ h) = -1 := by
    change φ₀.2 = -1
    rcases hφ₀ with rfl | rfl
    · rfl
    · rw [hsg]
  have hcc : D.R.chD D.R.cc = -1 := rfl
  refine ⟨?_, ?_, ?_, ?_, cc_mem_zpowers_gOf D φ₀ h, hI φ₀ hφ₀ h, ?_⟩
  · intro τ hτ i
    have hτ' : D.R.chD τ = 1 := hτ
    constructor
    · intro he
      show D.R.chD _ = 1
      rw [map_mul, map_pow, hchg, hτ', he.neg_one_pow, one_mul]
    · intro ho
      refine ⟨D.R.cc * ((gOf D φ₀ h) ^ i * τ), ?_, ?_⟩
      · show D.R.chD _ = 1
        rw [map_mul, map_mul, map_pow, hchg, hτ', ho.neg_one_pow, hcc]
        decide
      · rw [← mul_assoc, cc_mul_cc, one_mul]
  · intro t i
    have := (Formalism.HC.Frame.hostOrbitsPlaces (φ := D.R.toFrame) _ hg (D.R.tau1 t) (tau_one_mem_orbit_set D.R.toFrame t) i).1
    show D.R.iotaInv (Formalism.HC.Frame.placeOf _).2 = _
    rw [this, Formalism.HC.Frame.iotaInv_mul, Formalism.HC.Frame.iotaInv_pow]
    change i • D.R.iotaInv (D.R.iota h) + D.R.iotaInv (D.R.iota t) = t + i • h
    rw [Formalism.HC.Frame.iotaInv_iota, Formalism.HC.Frame.iotaInv_iota, add_comm]
  · intro hc t i
    have := (Formalism.HC.Frame.hostOrbitsPlaces (φ := D.R.toFrame) _ hg (D.R.tau1 t) (tau_one_mem_orbit_set D.R.toFrame t) i).2.1
      (by rw [hg1]; exact hc)
    rw [this]
    rfl
  · intro hs t i
    have := (Formalism.HC.Frame.hostOrbitsPlaces (φ := D.R.toFrame) _ hg (D.R.tau1 t) (tau_one_mem_orbit_set D.R.toFrame t) i).2.2
      (by rw [hg1, hs, hsg])
    rw [this]
    exact mul_one _
  · intro hc τ hτ
    refine ⟨?_, even_addOrderOf_of_h_ne_zero D⟩
    rw [Formalism.HC.Frame.hostOrbitCount (φ := D.R.toFrame) _ (by rw [hg1]; exact hc) τ hτ]
    exact orderOf_ofAdd_eq_addOrderOf h

theorem no_three_consecutive_thick_places (D : D7) : TorusPairsWithVariant D := by
  intro hL φ hφ hφc τ hτ i ⟨h0, h1, h2⟩
  have mem : ∀ g : D.R.GG, g ∈ thick D → ∃ s ∈ D.host.T2, g = D.R.tau2 (D.R.dig s + D.host.u0) := by
    intro g hg
    obtain ⟨s, hs, he⟩ := Finset.mem_image.1 hg
    exact ⟨s, hs, he.symm⟩
  exact no_three D.R.toFrame D.host.T2 D.host.second_set_range D.host.second_set_no_relation D.host.u0 hL φ hφ hφc τ hτ i
    (mem _ h0) (mem _ h1) (mem _ h2)

end Formalism.MainNotions.UnusedSlot33

end
end

section -- merged from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.LemmaOneSevenOfFiniteOrder
noncomputable section

open NumberField IsDedekindDomain TensorProduct

namespace Formalism.MainNotions.UnusedSlot33

open Formalism.BasicNotions

section Gen

variable {F E K : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  [Field K] [Algebra F K] [TopologicalSpace K] [IsTopologicalRing K]

theorem td_of_inj {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TotallyDisconnectedSpace Y] (f : X → Y) (hf : Continuous f) (hi : Function.Injective f) :
    TotallyDisconnectedSpace X := by
  refine ⟨fun s _ hs x hx y hy => hi ?_⟩
  exact TotallyDisconnectedSpace.isTotallyDisconnected_univ (f '' s) (Set.subset_univ _)
    (hs.image f hf.continuousOn) (Set.mem_image_of_mem f hx) (Set.mem_image_of_mem f hy)

theorem tens_finite :
    letI : Algebra K (E ⊗[F] K) := Algebra.TensorProduct.rightAlgebra
    Module.Finite K (E ⊗[F] K) := by
  letI : Algebra K (E ⊗[F] K) := Algebra.TensorProduct.rightAlgebra
  exact Module.Finite.equiv (R := K) (M := K ⊗[F] E) (N := E ⊗[F] K)
      { (TensorProduct.comm F K E) with
        map_smul' := fun c x => by
          induction x using TensorProduct.induction_on with
          | zero => simp
          | tmul a e =>
            simp [Algebra.smul_def, TensorProduct.smul_tmul']
            rw [show algebraMap K (E ⊗[F] K) c = (1 : E) ⊗ₜ[F] c from rfl,
              Algebra.TensorProduct.tmul_mul_tmul, one_mul]
          | add x y hx hy => simp_all [smul_add] }

theorem tens_topRing :
    letI := tensTop (F := F) (E := E) K
    IsTopologicalRing (E ⊗[F] K) := by
  letI : Algebra K (E ⊗[F] K) := Algebra.TensorProduct.rightAlgebra
  letI := tensTop (F := F) (E := E) K
  haveI : Module.Finite K (E ⊗[F] K) := tens_finite
  haveI : IsModuleTopology K (E ⊗[F] K) := ⟨rfl⟩
  exact IsModuleTopology.isTopologicalRing K (E ⊗[F] K)

theorem tens_td [TotallyDisconnectedSpace K] :
    letI := tensTop (F := F) (E := E) K
    TotallyDisconnectedSpace (E ⊗[F] K) := by
  letI : Algebra K (E ⊗[F] K) := Algebra.TensorProduct.rightAlgebra
  letI := tensTop (F := F) (E := E) K
  haveI : Module.Finite K (E ⊗[F] K) := tens_finite
  haveI : IsModuleTopology K (E ⊗[F] K) := ⟨rfl⟩
  let e := (Module.finBasis K (E ⊗[F] K)).equivFun
  exact td_of_inj e (IsModuleTopology.continuous_of_linearMap e.toLinearMap) e.injective

end Gen

section Steps

variable {F E : Type} [Field F] [Field E] [Algebra F E] {k : ℕ}

theorem inclE_injective (R : Type) [Field R] [Algebra F R] :
    Function.Injective (inclE (F := F) (E := E) R) := by
  exact (inclE (F := F) (E := E) R).injective

theorem bc_injective {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B)
    (hφ : Function.Injective φ) : Function.Injective (bc (ι := Fin k) φ) := by
  intro x y hxy
  apply Units.ext
  ext i j
  have h := congrArg (fun z : GL (Fin k) B => (z : Matrix (Fin k) (Fin k) B) i j) hxy
  simpa [bc, hφ.eq_iff] using h

theorem bc_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (φ : A →+* B)
    (ψ : B →+* C) (x : GL (Fin k) A) : bc ψ (bc φ x) = bc (ψ.comp φ) x := by
  apply Units.ext
  ext i j
  simp [bc]

theorem prV_inclE [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    (prV (E := E) v).comp (inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)) =
      inclE (F := F) (E := E) (v.adicCompletion F) := by
  ext x
  simp [prV, inclE]

theorem gl_topGroup {T : Type} [CommRing T] [TopologicalSpace T] [IsTopologicalRing T] :
    IsTopologicalGroup (GL (Fin k) T) := inferInstance

theorem gl_td {T : Type} [CommRing T] [TopologicalSpace T] [TotallyDisconnectedSpace T] :
    TotallyDisconnectedSpace (GL (Fin k) T) := by
  haveI : TotallyDisconnectedSpace (Matrix (Fin k) (Fin k) T) :=
    (inferInstance : TotallyDisconnectedSpace (Fin k → Fin k → T))
  exact td_of_inj (fun x : GL (Fin k) T => (x : Matrix (Fin k) (Fin k) T)) Units.continuous_val
    (fun a b hab => Units.ext hab)

theorem proG_order {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [TotallyDisconnectedSpace G] (g : ℕ) (hg : g.Prime) (Uw : Subgroup G) (h : IsProG g Uw)
    (x : G) (hx : x ∈ Uw) (hfin : IsOfFinOrder x) : ∃ m : ℕ, orderOf x = g ^ m := by
  classical
  obtain ⟨hc, hidx⟩ := h
  haveI : CompactSpace Uw := isCompact_iff_compactSpace.mp hc
  haveI : T1Space Uw := inferInstance
  let xu : Uw := ⟨x, hx⟩
  have hxu : orderOf xu = orderOf x := by
    exact Subgroup.orderOf_mk x hx
  have hnpos : 0 < orderOf x := hfin.orderOf_pos
  let Z : Finset Uw := (Finset.Ioo 0 (orderOf x)).image (fun j => xu ^ j)
  have hZ : IsOpen ((↑Z : Set Uw)ᶜ) := (Z.finite_toSet.isClosed).isOpen_compl
  have h1 : (1 : Uw) ∈ (↑Z : Set Uw)ᶜ := by
    intro hm
    obtain ⟨j, hj, hj1⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hm)
    obtain ⟨hj0, hjn⟩ := Finset.mem_Ioo.1 hj
    have := orderOf_le_of_pow_eq_one hj0 hj1
    omega
  obtain ⟨N, hN⟩ : ∃ N : OpenNormalSubgroup Uw, (N : Set Uw) ⊆ (↑Z : Set Uw)ᶜ := by
    haveI : T2Space Uw := inferInstance
    obtain ⟨H, hH⟩ :=
      ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one (G := ProfiniteGrp.of Uw) hZ h1
    exact ⟨H, hH⟩
  haveI hNn : N.toSubgroup.Normal := N.isNormal'
  obtain ⟨m, hm⟩ := hidx N.toSubgroup N.isOpen' hNn
  have hpow : xu ^ (g ^ m) ∈ N.toSubgroup := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← hm]
    exact pow_card_eq_one'
  have hdvd : orderOf x ∣ g ^ m := by
    by_contra hnd
    have hj0 : 0 < g ^ m % orderOf x :=
      Nat.pos_of_ne_zero (fun h0 => hnd (Nat.dvd_of_mod_eq_zero h0))
    have hjn : g ^ m % orderOf x < orderOf x := Nat.mod_lt _ hnpos
    have hmem : xu ^ (g ^ m % orderOf x) ∈ N.toSubgroup := by
      rw [← hxu, pow_mod_orderOf]
      exact hpow
    have hZm : xu ^ (g ^ m % orderOf x) ∈ (↑Z : Set Uw) :=
      Finset.mem_coe.2 (Finset.mem_image.2 ⟨_, Finset.mem_Ioo.2 ⟨hj0, hjn⟩, rfl⟩)
    exact hN hmem hZm
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hg).1 hdvd
  exact ⟨i, hi⟩

theorem step_pro {T : Type} [CommRing T] [TopologicalSpace T] [IsTopologicalRing T]
    [TotallyDisconnectedSpace T] (g : ℕ) (hg : g.Prime) (Uw : Subgroup (GL (Fin k) T))
    (h : IsProG g Uw) (x : GL (Fin k) T) (hx : x ∈ Uw) (hfin : IsOfFinOrder x) :
    ∃ m : ℕ, orderOf x = g ^ m := by
  haveI := gl_topGroup (k := k) (T := T)
  haveI := gl_td (k := k) (T := T)
  exact proG_order g hg Uw h x hx hfin

end Steps

def DefiniteUnitaryFiniteOrder (D : D7) : Prop :=
  ∀ σ : D.host.E →ₐ[D.host.F] D.host.E, (∀ x, σ x = D.host.conj x) →
  ∀ J : Matrix (Fin D.R.k) (Fin D.R.k) D.host.E, IsHerm (σ : D.host.E →+* D.host.E) J → IsDef σ J →
  letI := tensTop (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
  ∀ U : Subgroup (GL (Fin D.R.k) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)),
    U ≤ UPts σ J (FiniteAdeleRing (𝓞 D.host.F) D.host.F) →
    IsCompact (U : Set (GL (Fin D.R.k) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))) →
  ∀ y ∈ UPts σ J (FiniteAdeleRing (𝓞 D.host.F) D.host.F),
  ∀ γ ∈ UJ (σ : D.host.E →+* D.host.E) J,
    bc (inclE (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ ∈
      U.map (MulAut.conj y).toMonoidHom →
    IsOfFinOrder γ

set_option maxHeartbeats 1000000 in
theorem finiteModel_of_heckeEstimate (D : D7) (hF : DefiniteUnitaryFiniteOrder D) : division_rows_rational_lattice D := by
  intro σ hσ J hJ hD g hg hlt v hv U hU hUc _hUo Uw hUw hUUw y hy
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.mp hx1
  have hfin : IsOfFinOrder γ := hF σ hσ J hJ hD U hU hUc y hy γ hγ hx2
  obtain ⟨u, hu, hux⟩ := Subgroup.mem_map.mp hx2
  have hcomp : bc (prV v) (bc (inclE (F := D.host.F) (E := D.host.E)
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ) =
      bc (inclE (F := D.host.F) (E := D.host.E) (v.adicCompletion D.host.F)) γ := by
    rw [bc_comp, prV_inclE]
  have hordγ : orderOf (bc (inclE (F := D.host.F) (E := D.host.E) (v.adicCompletion D.host.F)) γ)
      = orderOf γ :=
    orderOf_injective (bc (ι := Fin D.R.k) (inclE (F := D.host.F) (E := D.host.E) (v.adicCompletion D.host.F)))
      (bc_injective _ (inclE_injective (F := D.host.F) (E := D.host.E) (v.adicCompletion D.host.F))) γ
  have hconj : bc (prV v) ((MulAut.conj y).toMonoidHom u) =
      MulAut.conj (bc (prV v) y) (bc (prV v) u) := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]
  have hord_u : orderOf (bc (prV v) u) = orderOf γ := by
    have e1 := MulEquiv.orderOf_eq (MulAut.conj (bc (prV v) y)) (bc (prV v) u)
    have e2 := congrArg (fun z => orderOf (bc (prV v) z)) hux
    have e3 := congrArg orderOf hcomp
    rw [← e1, ← hconj, e2, e3, hordγ]
  have hfin' : IsOfFinOrder (bc (prV v) u) := by
    rw [← orderOf_pos_iff, hord_u]
    exact hfin.orderOf_pos
  obtain ⟨m, hm⟩ := @step_pro D.R.k _ _
    (tensTop (F := D.host.F) (E := D.host.E) (v.adicCompletion D.host.F))
    (tens_topRing (F := D.host.F) (E := D.host.E) (K := v.adicCompletion D.host.F))
    (tens_td (F := D.host.F) (E := D.host.E) (K := v.adicCompletion D.host.F))
    g hg Uw hUw (bc (prV v) u) (hUUw u hu) hfin'
  rw [hord_u] at hm
  have hlt' : 4 * D.R.ord * D.R.k < g - 1 := by
    have h2 : 2 * D.R.f * D.R.k = 4 * D.R.ord * D.R.k := by
      have hf : D.R.f = 2 * D.R.ord := rfl
      rw [hf]
      ring
    omega
  have hΓ := Formalism.HC.HostAx.hostStab D.host.toHostAx D.R.k g hg hlt' (Subgroup.zpowers γ) (by
      intro δ hδ
      have hd : orderOf δ ∣ g ^ m := hm ▸ orderOf_dvd_of_mem_zpowers hδ
      obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hg).1 hd
      exact ⟨i, hi⟩)
  have h1 : γ = 1 := by
    have hm' : γ ∈ Subgroup.zpowers γ := Subgroup.mem_zpowers γ
    rw [hΓ] at hm'
    exact Subgroup.mem_bot.mp hm'
  rw [h1, map_one]

theorem totReal_emb {F : Type} [Field F] [IsTotallyReal F] (φ : F →+* ℂ) :
    ∃ r : F →+* ℝ, ∀ x, φ x = (r x : ℂ) := by
  have h : NumberField.ComplexEmbedding.IsReal φ := by
    exact NumberField.IsTotallyReal.complexEmbedding_isReal φ
  exact ⟨h.embedding, fun x => (h.coe_embedding_apply x).symm⟩

theorem finite_order_of_totally_real (hG : Formalism.MainNotions.Ext.FinOrdG) (D : D7) : DefiniteUnitaryFiniteOrder D := by
  intro σ _ J hJ hD U hU hUc y hy γ hγ hmem
  exact hG D.host.F D.host.E (fun φ => totReal_emb φ) σ D.R.k J hJ hD U hU hUc y hy γ hγ hmem

end Formalism.MainNotions.UnusedSlot33
end
end
