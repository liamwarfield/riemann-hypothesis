module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.IsMultiHomogRenameCoordPow
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StSegreChartZeroSet
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPowerBlock
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockResolutionMixedIntegral
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.CasChainA

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StPtsSemiPosMassFinite
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar IsGoodProj pot PBlk fsLine)

def PtsSemiPosMassFinite.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (N : Fin e → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι),
    IsArithVar P (e + 1) → IsGoodProj P Ψ → (∀ j, IsSmoothHerm (N j)) → (∀ j, Inter.IsSemiPosHerm (N j)) →
      ∫⁻ y, ENNReal.ofReal (ptsPosDens P Ψ (pot N) (fun _ => 1) y) < ⊤

end GroundTheory.Heights₂.Heights
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StSheetLift
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomogIdeal mcPts segre IsSheet PBlk)

def SheetLift.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (y : Fin e → ℂ)
    (h : (Fin e → ℂ) → ((k : K) → ι k) → ℂ),
    IsMultiHomogIdeal P →
    (∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ h y' ∧ (∃ z ∈ mcPts P, segre z = h y') ∧ Ψ (h y') = Fin.cons 1 y') →
      ∃ γ, IsSheet P Ψ y (h y) γ

end GroundTheory.Heights₂.Heights
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StChartConeLength
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsArithVar IsSectionOn divSupp IsHorizontal PBlk fsLine Xc)
open GroundTheory.Heights₂.Heights (segreChartIdeal segreChartComponents localMult)

def ChartConeLength.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n m : ℕ)
    (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (s : MRing ι),
    IsArithVar P (n + 2) → IsSectionOn P A s →
      ∀ W, W ∈ divSupp P s → IsHorizontal W → ∀ W' ∈ segreChartComponents W σ i,
        ∀ W'' ∈ (W.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes,
          W''.map (chartSubst σ i : MvPolynomial (Σ k, ι k) ℂ →+* MvPolynomial (Fin m) ℂ) ≤ W' →
            localMult (segreChartIdeal P σ i ⊔ Ideal.span {chartSection σ i s}) W' =
              localMult ((P ⊔ Ideal.span {s}).map (MvPolynomial.map (Int.castRingHom ℂ))) W''

end GroundTheory.Heights₂.Heights.Targets
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsIntegralProjIndep
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Filter
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar IsGoodProj IsSheet ptsIntegralAt sheetDensity
  fibre pot mcPts fibreFinite isOpen_blockNonzero)

section

variable {K : Type*} [Fintype K] {ι : K → Type*} {e : ℕ} {P : Ideal (MRing ι)}
  {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ}

theorem sheetDensity_neg (g : ((Σ k, ι k) → ℂ) → ℝ) (y : Fin e → ℂ) (w : ((k : K) → ι k) → ℂ) :
    sheetDensity P Ψ φ (fun z => -g z) y w = -sheetDensity P Ψ φ g y w := by
  unfold sheetDensity
  split_ifs <;> simp [neg_mul]

theorem sheetDensity_congr {g g' : ((Σ k, ι k) → ℂ) → ℝ} (h : ∀ z ∈ mcPts P, g z = g' z) (y : Fin e → ℂ)
    (w : ((k : K) → ι k) → ℂ) : sheetDensity P Ψ φ g y w = sheetDensity P Ψ φ g' y w := by
  unfold sheetDensity
  split_ifs with hγ
  · have hs : IsSheet P Ψ y w hγ.choose := hγ.choose_spec
    rw [h _ hs.2.self_of_nhds.2.1]
  · rfl

end

theorem PtsIntegralProjIndep.proof (hInt : PtsPosDensIntegrable.Statement)
    (hPos : PtsPosPartProjIndep.Statement) : PtsIntegralProjIndep.Statement := by
  intro K _ ι _ P e Ψ Ψ' L g hP hΨ hΨ' hL hg
  classical
  set S : Set ((Σ k, ι k) → ℂ) := {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} with hSdef
  set g₀ : ((Σ k, ι k) → ℂ) → ℝ := S.piecewise g 0 with hg₀def
  have hg₀m : Measurable g₀ :=
    hg.1.continuousOn.measurable_piecewise continuousOn_const isOpen_blockNonzero.measurableSet
  have hg₀inv : ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) →
      g₀ (fun p => c p.1 * z p) = g₀ z := by
    intro c z hc
    have hmem : (fun p : Σ k, ι k => c p.1 * z p) ∈ S ↔ z ∈ S := by
      simp only [hSdef, Set.mem_ofPred_eq, ne_eq, mul_eq_zero, hc, false_or]
    by_cases hz : z ∈ S
    · rw [hg₀def, Set.piecewise_eq_of_mem _ _ _ hz, Set.piecewise_eq_of_mem _ _ _ (hmem.2 hz), hg.2 c z hc]
    · rw [hg₀def, Set.piecewise_eq_of_notMem _ _ _ hz, Set.piecewise_eq_of_notMem _ _ _ (mt hmem.1 hz)]
      rfl
  have hag : ∀ z ∈ mcPts P, g z = g₀ z := fun z hz =>
    (Set.piecewise_eq_of_mem S _ _ (show z ∈ S from hz.1)).symm
  have hagn : ∀ z ∈ mcPts P, -g z = -g₀ z := fun z hz => by rw [hag z hz]
  have hneg : IsDegZeroSmooth (fun z => -g z) :=
    ⟨hg.1.neg, fun c z hc => by simp only [hg.2 c z hc]⟩
  have hnn : ∀ (Ψ₀ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (u : ((Σ k, ι k) → ℂ) → ℝ) y,
      0 ≤ ptsPosDens P Ψ₀ (pot L) u y := fun Ψ₀ u y =>
    finsum_nonneg fun w => finsum_nonneg fun _ => le_max_right _ _

  have key : ∀ Ψ₀ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj P Ψ₀ →
      ptsIntegralAt P Ψ₀ (pot L) g =
        (∫⁻ y, ENNReal.ofReal (ptsPosDens P Ψ₀ (pot L) g₀ y)).toReal -
          (∫⁻ y, ENNReal.ofReal (ptsPosDens P Ψ₀ (pot L) (fun z => -g₀ z) y)).toReal := by
    intro Ψ₀ h₀
    have hp := hInt K ι P e Ψ₀ L g hP h₀ hL hg
    have hn := hInt K ι P e Ψ₀ L (fun z => -g z) hP h₀ hL hneg
    have e₁ : ptsPosDens P Ψ₀ (pot L) g₀ = ptsPosDens P Ψ₀ (pot L) g := by
      funext y
      simp only [ptsPosDens, sheetDensity_congr (Ψ := Ψ₀) (φ := pot L) hag]
    have e₂ : ptsPosDens P Ψ₀ (pot L) (fun z => -g₀ z) = ptsPosDens P Ψ₀ (pot L) (fun z => -g z) := by
      funext y
      simp only [ptsPosDens, sheetDensity_congr (Ψ := Ψ₀) (φ := pot L) hagn]
    have hsplit : ∀ y, (∑ᶠ w ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ₀ y, sheetDensity P Ψ₀ (pot L) g y w) =
        ptsPosDens P Ψ₀ (pot L) g y - ptsPosDens P Ψ₀ (pot L) (fun z => -g z) y := by
      intro y
      have hF := fibreFinite K ι P e Ψ₀ hP h₀ y
      simp only [ptsPosDens, finsum_mem_eq_finite_toFinset_sum _ hF, sheetDensity_neg,
        ← Finset.sum_sub_distrib, max_zero_sub_max_neg_zero_eq_self]
    unfold ptsIntegralAt
    simp only [hsplit]
    rw [integral_sub hp hn, integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (hnn Ψ₀ g)) hp.1,
      integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (hnn Ψ₀ _)) hn.1, e₁, e₂]
  rw [key Ψ hΨ, key Ψ' hΨ', hPos K ι P e Ψ Ψ' L g₀ hP hΨ hΨ' hL hg₀m hg₀inv,
    hPos K ι P e Ψ Ψ' L (fun z => -g₀ z) hP hΨ hΨ' hL hg₀m.neg fun c z hc => by simp only [hg₀inv c z hc]]

end GroundTheory.Heights₂.Heights
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PNefCountAlongMultiples
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

namespace NefCountAlongMultiples

section Transport

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem count_shift_le {y : (Σ k, ι k) → Ω} {A N : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} {e : Ω} {C : ℝ} {p q n : ℕ}
    (he0 : e ≠ 0)
    (hmap : ∀ s : Ω, s ∈ chartLat y N.a n → s * e ^ (p * n) ∈ chartLat y A.a (q * n) ∧
      ∀ c : ℝ, IsBoundedH (mCoordIdeal y) y N n c s →
        IsBoundedH (mCoordIdeal y) y A (q * n) (c * Real.exp (((p * n : ℕ) : ℝ) * C)) (s * e ^ (p * n)))
    (hfin : {s : chartLat y A.a (q * n) | IsSmallH (mCoordIdeal y) y A (q * n) (s : Ω)}.Finite) :
    smallSectionCount (IsSmallH (mCoordIdeal y) y (HermLine.constShift N ((p : ℝ) * C)))
        (chartLat y (HermLine.constShift N ((p : ℝ) * C)).a) n ≤
      smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) (q * n) := by
  have hc : Real.exp (-((p : ℝ) * C)) ^ n * Real.exp (((p * n : ℕ) : ℝ) * C) = 1 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    convert Real.exp_zero using 2
    push_cast
    ring
  have hsm : ∀ s : {s : chartLat y (HermLine.constShift N ((p : ℝ) * C)).a n //
      IsSmallH (mCoordIdeal y) y (HermLine.constShift N ((p : ℝ) * C)) n (s : Ω)},
      (s.1 : Ω) * e ^ (p * n) ∈ chartLat y A.a (q * n) ∧
        IsSmallH (mCoordIdeal y) y A (q * n) ((s.1 : Ω) * e ^ (p * n)) := by
    rintro ⟨⟨x, hx⟩, hxs⟩
    have hxs' : IsSmallH (mCoordIdeal y) y (HermLine.constShift N ((p : ℝ) * C)) n x := hxs
    rw [constShift_a] at hx
    show x * e ^ (p * n) ∈ chartLat y A.a (q * n) ∧ IsSmallH (mCoordIdeal y) y A (q * n) (x * e ^ (p * n))
    obtain ⟨hm, hb⟩ := hmap x hx
    refine ⟨hm, fun dg dh g h z hg hh hdeg heq hz => ?_⟩
    have hB : IsBoundedH (mCoordIdeal y) y N n (Real.exp (-((p : ℝ) * C)) ^ n) x := by
      intro dg' dh' g' h' z' hg' hh' hdeg' heq' hz'
      have := hxs' dg' dh' g' h' z' hg' hh' (by rw [constShift_a]; exact hdeg') heq' hz'
      rw [constShift_h, mul_pow] at this
      exact this.trans (le_of_eq (by ring))
    have := hb _ hB dg dh g h z hg hh hdeg heq hz
    rwa [hc, one_mul] at this
  have : Finite {s : chartLat y A.a (q * n) // IsSmallH (mCoordIdeal y) y A (q * n) (s : Ω)} :=
    hfin.to_subtype
  have hcard : Nat.card {s : chartLat y (HermLine.constShift N ((p : ℝ) * C)).a n //
        IsSmallH (mCoordIdeal y) y (HermLine.constShift N ((p : ℝ) * C)) n (s : Ω)} ≤
      Nat.card {s : chartLat y A.a (q * n) // IsSmallH (mCoordIdeal y) y A (q * n) (s : Ω)} :=
    Nat.card_le_card_of_injective (fun s => ⟨⟨(s.1 : Ω) * e ^ (p * n), (hsm s).1⟩, (hsm s).2⟩) fun s s' h => by
      simp only [Subtype.mk.injEq] at h
      exact Subtype.ext (Subtype.ext (mul_right_cancel₀ (pow_ne_zero _ he0) h))
  unfold smallSectionCount
  rcases Nat.eq_zero_or_pos (Nat.card {s : chartLat y (HermLine.constShift N ((p : ℝ) * C)).a n //
      IsSmallH (mCoordIdeal y) y (HermLine.constShift N ((p : ℝ) * C)) n (s : Ω)}) with h0 | hpos
  · rw [h0, Nat.cast_zero, Real.log_zero]
    exact Real.log_natCast_nonneg _
  · exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hcard)

end Transport

theorem num_bound {T ε I G g C q : ℝ} {D : ℕ} (hε : 0 < ε) (hq : 0 < q) (hC : 0 ≤ C)
    (hI : |I / q ^ (D + 1) - T| < ε / 4) (hG : |G / q ^ D - g| < ε / 4)
    (hqC : ((D : ℝ) + 1) * C * (g + ε / 4) < q * (ε / 4)) :
    (T - ε) * q ^ (D + 1) + ε / 4 * q ^ (D + 1) ≤ I - ((D : ℝ) + 1) * (((1 : ℕ) : ℝ) * C) * G := by
  have hQ : 0 < q ^ (D + 1) := by positivity
  have hQD : 0 < q ^ D := by positivity
  rw [abs_sub_lt_iff] at hI hG
  have h1 : (T - ε / 4) * q ^ (D + 1) < I := (lt_div_iff₀ hQ).1 (by linarith [hI.2])
  have h2 : G < (g + ε / 4) * q ^ D := (div_lt_iff₀ hQD).1 (by linarith [hG.1])
  have h3 : ((D : ℝ) + 1) * (((1 : ℕ) : ℝ) * C) * G ≤ ((D : ℝ) + 1) * C * ((g + ε / 4) * q ^ D) := by
    rw [Nat.cast_one, one_mul]
    exact mul_le_mul_of_nonneg_left h2.le (by positivity)
  have h4 : ((D : ℝ) + 1) * C * ((g + ε / 4) * q ^ D) ≤ ε / 4 * q ^ (D + 1) :=
    calc ((D : ℝ) + 1) * C * ((g + ε / 4) * q ^ D) = (((D : ℝ) + 1) * C * (g + ε / 4)) * q ^ D := by ring
      _ ≤ (q * (ε / 4)) * q ^ D := (mul_lt_mul_of_pos_right hqC hQD).le
      _ = ε / 4 * q ^ (D + 1) := by ring
  nlinarith [mul_pos hε hQ]

theorem le_arithmeticVolume_of_alongMultiples {Ω : Type} [Field Ω] {Pr : ℕ → Ω → Prop} {La : ℕ → AddSubgroup Ω} {D : ℕ}
    {T Cp : ℝ} (hC : ∀ τ, smallSectionCount Pr La τ ≤ Cp * ((τ : ℝ) + 1) ^ (D + 1))
    (h : ∀ ε : ℝ, 0 < ε → ∃ a : ℕ, 1 ≤ a ∧ ∀ᶠ k : ℕ in atTop,
      (T - ε) * (((a * k : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) ≤ smallSectionCount Pr La (a * k)) :
    T ≤ arVolP Pr La 1 D := by
  obtain ⟨B, hB⟩ := NormCountBounded.norm_count_bounded D hC
  have hbdd : IsBoundedUnder (· ≤ ·) atTop (fun k : ℕ => smallSectionCount Pr La (1 * k) /
      (((1 * k : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ))) := by
    refine ⟨B, ?_⟩
    simpa using hB
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨a, ha, hev⟩ := h ε hε
  have hfreq : ∃ᶠ k : ℕ in atTop, T - ε ≤ smallSectionCount Pr La (1 * k) /
      (((1 * k : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) := by
    rw [frequently_atTop]
    intro N
    obtain ⟨k, hk⟩ := (hev.and (eventually_ge_atTop (N + 1))).exists
    refine ⟨a * k, le_trans (by omega) (Nat.le_mul_of_pos_left k ha), ?_⟩
    have hak : 0 < a * k := Nat.mul_pos ha (by omega)
    have hpos : (0 : ℝ) < ((a * k : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ) :=
      div_pos (pow_pos (by exact_mod_cast hak) _) (by exact_mod_cast Nat.factorial_pos _)
    rw [one_mul, le_div_iff₀ hpos]
    exact hk.1
  have := le_limsup_of_frequently_le hfreq hbdd
  unfold arVolP
  linarith

end NefCountAlongMultiples

end

end GroundTheory.Heights₂.Heights.Targets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsPosPartProjIndep
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar IsGoodProj mcPts segre fibre IsSheet sheetDensity
  pot fibreFinite)

theorem ptsPosDens_split {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {e : ℕ}
    {P : Ideal (MRing ι)} {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
    (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (g : ((Σ k, ι k) → ℂ) → ℝ) (E : ℕ → Set ((Σ k, ι k) → ℂ))
    (y : Fin e → ℂ) (hfin : (ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y).Finite) (hE : Pairwise (Function.onFun Disjoint E))
    (hcov : ∀ w ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y, (∃ γ, IsSheet P Ψ y w γ) → ∀ z ∈ mcPts P, segre z = w → ∃ k, z ∈ E k) :
    ENNReal.ofReal (ptsPosDens P Ψ φ g y) =
      ∑' k, ENNReal.ofReal (ptsPosDens P Ψ φ ((E k).indicator g) y) := by
  classical
  unfold ptsPosDens
  simp only [finsum_mem_eq_finite_toFinset_sum _ hfin]
  have hT0 : ∀ (g' : ((Σ k, ι k) → ℂ) → ℝ) w, 0 ≤ max (sheetDensity P Ψ φ g' y w) 0 :=
    fun _ _ => le_max_right _ _
  have hpt : ∀ w ∈ hfin.toFinset, ENNReal.ofReal (max (sheetDensity P Ψ φ g y w) 0) =
      ∑' k, ENNReal.ofReal (max (sheetDensity P Ψ φ ((E k).indicator g) y w) 0) := by
    intro w hw
    have hw' : w ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y := hfin.mem_toFinset.mp hw
    by_cases hs : ∃ γ, IsSheet P Ψ y w γ
    · have hz : hs.choose y ∈ mcPts P := hs.choose_spec.2.self_of_nhds.2.1
      obtain ⟨k₀, hk₀⟩ := hcov w hw' hs _ hz hs.choose_spec.1
      rw [tsum_eq_single k₀]
      · simp only [sheetDensity, dif_pos hs, Set.indicator_of_mem hk₀]
      · intro k hk
        have hxk : hs.choose y ∉ E k := fun hxk => Set.disjoint_left.mp (hE hk) hxk hk₀
        simp [sheetDensity, dif_pos hs, Set.indicator_of_notMem hxk]
    · simp [sheetDensity, dif_neg hs]
  rw [ENNReal.ofReal_sum_of_nonneg (fun w _ => hT0 g w), Finset.sum_congr rfl hpt,
    ← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  exact tsum_congr fun k => (ENNReal.ofReal_sum_of_nonneg (fun w _ => hT0 _ w)).symm

theorem PtsPosPartProjIndep.proof (hS : PtsSheetSimpleNull.Statement) (hO : PtsSheetOnlyNull.Statement)
    (hL : PtsPosPartLocal.Statement) (hM : PtsPosDensMeasurable.Statement) :
    PtsPosPartProjIndep.Statement := by
  intro K _ ι _ P e Ψ Ψ' L g hP hΨ hΨ' hLs hg hg0
  classical

  set Inv : Set ((Σ k, ι k) → ℂ) → Prop := fun S => ∀ (c : K → ℂ) (z' : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) →
    ((fun p => c p.1 * z' p) ∈ S ↔ z' ∈ S) with hInv

  set Q : ((Σ k, ι k) → ℂ) → Prop := fun z => z ∈ mcPts P ∧
    IsSimpleSheetPt P Ψ ((Ψ (segre z) 0)⁻¹ • segre z) ∧
    IsSimpleSheetPt P Ψ' ((Ψ' (segre z) 0)⁻¹ • segre z) with hQ
  have key : ∀ z, ∃ W : Set ((Σ k, ι k) → ℂ), IsOpen W ∧ Inv W ∧ (Q z → z ∈ W) ∧
      ∀ E, MeasurableSet E → Inv E → E ⊆ W →
        ∫⁻ y, ENNReal.ofReal (ptsPosDens P Ψ (pot L) (E.indicator g) y) =
          ∫⁻ y, ENNReal.ofReal (ptsPosDens P Ψ' (pot L) (E.indicator g) y) := by
    intro z
    by_cases hz : Q z
    · obtain ⟨W, hW, hzW, hWi, hWE⟩ := hL K ι P e Ψ Ψ' L g z hP hΨ hΨ' hLs hg hg0 hz.1 hz.2.1 hz.2.2
      exact ⟨W, hW, hWi, fun _ => hzW, hWE⟩
    · refine ⟨∅, isOpen_empty, fun _ _ _ => Iff.rfl, fun h => absurd h hz, fun E _ _ hE => ?_⟩
      rw [Set.subset_empty_iff.1 hE, Set.indicator_empty]
      simp [ptsPosDens, sheetDensity]
  choose W hWo hWi hzW hWE using key
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable W hWo
  obtain ⟨f, hf⟩ := (hTc.insert 0).exists_eq_range (Set.insert_nonempty 0 T)
  set E : ℕ → Set ((Σ k, ι k) → ℂ) := disjointed (fun k => W (f k)) with hE
  have hEm : ∀ k, MeasurableSet (E k) := MeasurableSet.disjointed fun k => (hWo (f k)).measurableSet
  have hEW : ∀ k, E k ⊆ W (f k) := disjointed_subset _
  have hEd : Pairwise (Function.onFun Disjoint E) := disjoint_disjointed _
  have hEi : ∀ k, Inv (E k) := by
    intro k c z' hc
    simp only [hE, disjointed_eq_inter_compl, Set.mem_inter_iff, Set.mem_iInter, Set.mem_compl_iff,
      hWi _ c z' hc]
  have hgE : ∀ k (c : K → ℂ) (z' : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) →
      (E k).indicator g (fun p => c p.1 * z' p) = (E k).indicator g z' := by
    intro k c z' hc
    simp only [Set.indicator_apply, hEi k c z' hc, hg0 c z' hc]
  have hcov : ∀ z, Q z → ∃ k, z ∈ E k := by
    intro z hq
    have : z ∈ ⋃ i ∈ T, W i := hTU ▸ Set.mem_iUnion.2 ⟨z, hzW z hq⟩
    obtain ⟨i, hiT, hzi⟩ := Set.mem_iUnion₂.1 this
    obtain ⟨m, rfl⟩ : i ∈ Set.range f := hf ▸ Set.mem_insert_of_mem 0 hiT
    have : z ∈ ⋃ k, E k := by
      rw [hE, iUnion_disjointed]
      exact Set.mem_iUnion.2 ⟨m, hzi⟩
    exact Set.mem_iUnion.1 this

  have hae : ∀ B B' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj P B → IsGoodProj P B' →
      (∀ z ∈ mcPts P, IsSimpleSheetPt P B ((B (segre z) 0)⁻¹ • segre z) →
        IsSimpleSheetPt P B' ((B' (segre z) 0)⁻¹ • segre z) → ∃ k, z ∈ E k) →
      ∀ᵐ y, ENNReal.ofReal (ptsPosDens P B (pot L) g y) =
        ∑' k, ENNReal.ofReal (ptsPosDens P B (pot L) ((E k).indicator g) y) := by
    intro B B' hB hB' hc
    have hnull := measure_union_null (hS K ι P e B hP hB) (hO K ι P e B B' hP hB hB')
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with y hy
    refine ptsPosDens_split _ _ E y (fibreFinite K ι P e B hP hB y) hEd fun w hw hs z hz hzw => ?_
    have hw1 : B w 0 = 1 := by
      obtain ⟨_, _, _, h⟩ := hw
      rw [h]
      rfl
    have hs1 : IsSimpleSheetPt P B w := by
      by_contra hn
      exact hy (Or.inl ⟨w, hw, hs, hn⟩)
    have hs2 : IsSimpleSheetPt P B' ((B' w 0)⁻¹ • w) := by
      by_contra hn
      exact hy (Or.inr ⟨w, hw, hs1, hn⟩)
    subst hzw
    refine hc z hz ?_ hs2
    rwa [hw1, inv_one, one_smul]
  have hint : ∀ B : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj P B →
      (∀ᵐ y, ENNReal.ofReal (ptsPosDens P B (pot L) g y) =
        ∑' k, ENNReal.ofReal (ptsPosDens P B (pot L) ((E k).indicator g) y)) →
      ∫⁻ y, ENNReal.ofReal (ptsPosDens P B (pot L) g y) =
        ∑' k, ∫⁻ y, ENNReal.ofReal (ptsPosDens P B (pot L) ((E k).indicator g) y) := by
    intro B hB h2
    rw [lintegral_congr_ae h2, lintegral_tsum fun k =>
      (hM K ι P e B L _ hP hB hLs (hg.indicator (hEm k)) (hgE k)).ennreal_ofReal]
  rw [hint Ψ hΨ (hae Ψ Ψ' hΨ hΨ' fun z hz h1 h2 => hcov z ⟨hz, h1, h2⟩),
    hint Ψ' hΨ' (hae Ψ' Ψ hΨ' hΨ fun z hz h1 h2 => hcov z ⟨hz, h2, h1⟩)]
  exact tsum_congr fun k => hWE (f k) (E k) (hEm k) (hEi k) (hEW k)

end GroundTheory.Heights₂.Heights
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsBilinear
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo
open scoped ContDiff

namespace PointsBilinear

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem contDiffAt_comp {D : ℕ} {u : ((Σ k, ι k) → ℂ) → ℝ} (hu : IsDegZeroSmooth u)
    {γ : (Fin D → ℂ) → (Σ k, ι k) → ℂ} {y : Fin D → ℂ}
    (hγ : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ γ y') (hy : ∀ k, ∃ i, γ y ⟨k, i⟩ ≠ 0) :
    ContDiffAt ℝ 2 (fun y' => u (γ y')) y := by
  obtain ⟨U, hU, hUo, hyU⟩ := eventually_nhds_iff.mp hγ
  have hdU : DifferentiableOn ℂ γ U := fun y' h => (hU y' h).differentiableWithinAt
  have hc : ContDiffAt ℝ ∞ γ y :=
    ((ReciprocityTheory.ChartRestriction.DS.S7.cca_contDiffOn hUo hdU).contDiffAt (hUo.mem_nhds hyU)).restrict_scalars ℝ
  have hρ : ContDiffAt ℝ ∞ u (γ y) := hu.1.contDiffAt (isOpen_blockNonzero.mem_nhds hy)
  exact_mod_cast (contDiffAt_infty.mp (hρ.comp y hc)) 2

theorem cxHessian_sum {D : ℕ} {T : Type} [Fintype T] (f : T → (Fin D → ℂ) → ℝ) {y : Fin D → ℂ}
    (hf : ∀ t, ∀ᶠ y' in 𝓝 y, ContDiffAt ℝ 2 (f t) y') :
    cxHessian (fun y' => ∑ t, f t y') y = ∑ t, cxHessian (f t) y := by
  have h1 : fderiv ℝ (fun y' => ∑ t, f t y') =ᶠ[𝓝 y] fun y' => ∑ t, fderiv ℝ (f t) y' := by
    filter_upwards [eventually_all.mpr hf] with y' hy'
    exact fderiv_fun_sum fun t _ => (hy' t).differentiableAt (by norm_num)
  have h2 : fderiv ℝ (fderiv ℝ (fun y' => ∑ t, f t y')) y = ∑ t, fderiv ℝ (fderiv ℝ (f t)) y := by
    rw [h1.fderiv_eq]
    exact fderiv_fun_sum fun t _ =>
      ((hf t).self_of_nhds.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  ext i j
  simp only [cxHessian, h2, FunLike.coe_sum, Finset.sum_apply, Matrix.sum_apply]
  push_cast
  rw [← Finset.sum_div]
  congr 1
  simp only [Finset.sum_add_distrib]
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]

theorem mixedDisc_update_sum {D : ℕ} {T : Type} [Fintype T] (A : Fin D → Matrix (Fin D) (Fin D) ℂ)
    (k : Fin D) (B : T → Matrix (Fin D) (Fin D) ℂ) :
    mixedDisc (Function.update A k (∑ t, B t)) = ∑ t, mixedDisc (Function.update A k (B t)) := by
  obtain ⟨M, hM⟩ := (by
    show ∃ F : MultilinearMap (RingHom.id ℂ)
        (fun _ : Fin D => Matrix (Fin D) (Fin D) ℂ) ℂ,
        ⇑F = _root_.ReciprocityTheory.AnForm.mdisc
    refine ⟨MultilinearMap.mk' _root_.ReciprocityTheory.AnForm.mdisc
      _root_.ReciprocityTheory.AnForm.A.mdisc_update_add ?_, rfl⟩
    intro A k c B
    simpa only [RingHom.id_apply, smul_eq_mul] using
      (_root_.ReciprocityTheory.AnForm.A.mdisc_update_smul A k c B))
  have e : ∀ C, mixedDisc (Function.update A k C) = M.toLinearMap A k C := fun C => by
    rw [MultilinearMap.toLinearMap_apply, hM]
    rfl
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [e, map_sum]

theorem cxHessian_cons {n : ℕ} (L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (f v : ((Σ k, ι k) → ℂ) → ℝ)
    (γ : (Fin (n + 1) → ℂ) → (Σ k, ι k) → ℂ) (y : Fin (n + 1) → ℂ) :
    (fun k => cxHessian
        (fun y' => (Fin.cons f (pot L) : Fin (n + 1) → ((Σ k, ι k) → ℂ) → ℝ) k (γ y')) y) =
      Function.update (fun k => cxHessian
        (fun y' => (Fin.cons v (pot L) : Fin (n + 1) → ((Σ k, ι k) → ℂ) → ℝ) k (γ y')) y) 0
        (cxHessian (fun y' => f (γ y')) y) := by
  funext k
  refine Fin.cases ?_ (fun j => ?_) k
  · rw [Function.update_self]
    simp only [Fin.cons_zero]
  · rw [Function.update_of_ne (Fin.succ_ne_zero j)]
    simp only [Fin.cons_succ]

theorem maDensity_cons_sum {n : ℕ} (L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) {T : Type} [Fintype T]
    {u : T → ((Σ k, ι k) → ℂ) → ℝ} (hu : ∀ t, IsDegZeroSmooth (u t))
    {γ : (Fin (n + 1) → ℂ) → (Σ k, ι k) → ℂ} {y : Fin (n + 1) → ℂ}
    (hγ : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ γ y' ∧ ∀ k, ∃ i, γ y' ⟨k, i⟩ ≠ 0) :
    maDensity (fun j y' => (Fin.cons (fun z => ∑ t, u t z) (pot L) :
        Fin (n + 1) → ((Σ k, ι k) → ℂ) → ℝ) j (γ y')) y =
      ∑ t, maDensity (fun j y' => (Fin.cons (u t) (pot L) :
        Fin (n + 1) → ((Σ k, ι k) → ℂ) → ℝ) j (γ y')) y := by
  have hev := hγ.eventually_nhds
  have hc : ∀ t, ∀ᶠ y' in 𝓝 y, ContDiffAt ℝ 2 (fun y'' => u t (γ y'')) y' := fun t => by
    filter_upwards [hev] with y' hy'
    exact contDiffAt_comp (hu t) (hy'.mono fun _ h => h.1) hy'.self_of_nhds.2
  have hH := cxHessian_sum (fun t y' => u t (γ y')) hc
  simp only [maDensity]
  rw [cxHessian_cons L _ (fun _ => 0) γ y]
  simp only [hH, mixedDisc_update_sum, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [cxHessian_cons L (u t) (fun _ => 0) γ y]


omit [∀ k, Fintype (ι k)] in
theorem sheetDensity_sum_left {n : ℕ} (P : Ideal (MRing ι))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (φ : Fin n → ((Σ k, ι k) → ℂ) → ℝ)
    {T : Type} [Fintype T] (u : T → ((Σ k, ι k) → ℂ) → ℝ) (y : Fin n → ℂ)
    (w : ((k : K) → ι k) → ℂ) :
    sheetDensity P Ψ φ (fun z => ∑ t, u t z) y w = ∑ t, sheetDensity P Ψ φ (u t) y w := by
  unfold sheetDensity
  by_cases h : ∃ γ, IsSheet P Ψ y w γ
  · simp only [dif_pos h, Finset.sum_mul]
  · simp only [dif_neg h, Finset.sum_const_zero]

theorem sheetDensity_sum_right {n : ℕ} (P : Ideal (MRing ι))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1 + 1) → ℂ)) (L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι)
    {T : Type} [Fintype T] {u : T → ((Σ k, ι k) → ℂ) → ℝ} (hu : ∀ t, IsDegZeroSmooth (u t))
    (g : ((Σ k, ι k) → ℂ) → ℝ) (y : Fin (n + 1) → ℂ) (w : ((k : K) → ι k) → ℂ) :
    sheetDensity P Ψ (Fin.cons (fun z => ∑ t, u t z) (pot L)) g y w =
      ∑ t, sheetDensity P Ψ (Fin.cons (u t) (pot L)) g y w := by
  unfold sheetDensity
  by_cases h : ∃ γ, IsSheet P Ψ y w γ
  · simp only [dif_pos h]
    have hγ : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ h.choose y' ∧ ∀ k, ∃ i, h.choose y' ⟨k, i⟩ ≠ 0 := by
      filter_upwards [h.choose_spec.2] with y' hy'
      exact ⟨hy'.1, hy'.2.1.1⟩
    rw [maDensity_cons_sum L hu hγ, Finset.mul_sum]
  · simp only [dif_neg h, Finset.sum_const_zero]

theorem finsum_mem_sum_comm {α T : Type*} [Fintype T] {S : Set α} (hS : S.Finite) (F : T → α → ℝ) :
    ∑ᶠ w ∈ S, ∑ t, F t w = ∑ t, ∑ᶠ w ∈ S, F t w := by
  rw [finsum_mem_eq_finite_toFinset_sum _ hS, Finset.sum_comm]
  exact Finset.sum_congr rfl fun t _ => (finsum_mem_eq_finite_toFinset_sum _ hS).symm

theorem isSmoothHerm_ofWeight {w : ((Σ k, ι k) → ℂ) → ℝ}
    (hw : ∀ (c : K → ℂ) z, (∀ k, c k ≠ 0) → w (fun p => c p.1 * z p) = w z)
    (hs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}) :
    IsSmoothHerm (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofWeight w hw) := by
  have e : (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofWeight w hw).h = fun z => Real.exp (-w z) := rfl
  unfold IsSmoothHerm
  rw [e]
  exact Real.contDiff_exp.comp_contDiffOn hs.neg

theorem integrable_fibreSum (hInt : PtsIntegrableStatement) {P : Ideal (MRing ι)} {n : ℕ}
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1 + 1) → ℂ)) (L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι)
    {f g : ((Σ k, ι k) → ℂ) → ℝ} (hP : IsArithVar P (n + 2)) (hΨ : IsGoodProj P Ψ)
    (hL : ∀ j, IsSmoothHerm (L j)) (hf : IsDegZeroSmooth f) (hg : IsDegZeroSmooth g) :
    Integrable (fun y => ∑ᶠ w ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y, sheetDensity P Ψ (Fin.cons f (pot L)) g y w) := by
  have hf' : ∀ (c : K → ℂ) z, (∀ k, c k ≠ 0) → -f (fun p => c p.1 * z p) = -f z :=
    fun c z hc => by simp only [hf.2 c z hc]
  have hF := isSmoothHerm_ofWeight (w := fun z => -f z) hf' hf.1.neg
  have hG := isSmoothHerm_ofWeight hg.2 hg.1
  have hLF : ∀ j, IsSmoothHerm ((Fin.cons (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofWeight (fun z => -f z) hf') L : Fin (n + 1) → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) j) := by
    intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · simpa only [Fin.cons_zero] using hF
    · simpa only [Fin.cons_succ] using hL j
  have hpot : pot (Fin.cons (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofWeight (fun z => -f z) hf') L : Fin (n + 1) → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) = Fin.cons f (pot L) := by
    funext j z
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [pot, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofWeight, Real.log_exp]
    · simp [pot]
  have hlog : logNorm (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofWeight g hg.2) 1 = g := by
    funext z
    simp [logNorm, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofWeight, Real.log_exp]
  have h1 : (1 : MRing ι) ∉ P := fun h => hP.2.1.1.ne_top ((Ideal.eq_top_iff_one P).mpr h)
  have hm : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (1 : MRing ι) (fun _ => 0) := by
    intro m hm k
    rw [MvPolynomial.support_one] at hm
    simp only [Finset.mem_singleton] at hm
    subst hm
    simp
  have hsec : IsSectionOn P (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofWeight g hg.2) 1 :=
    ⟨fun _ => 0, fun k => by simp [ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofWeight], hm, h1⟩
  have := hInt K ι P (n + 1) Ψ _ _ 1 hP hΨ hLF hG hsec
  rwa [hpot, hlog] at this

end PointsBilinear


open PointsBilinear in
theorem PtsBilinear.proof (hAbs : Inter.PtsAbsIntegrable.Statement) (hMeas : PtsSumMeasurable.Statement) :
    PtsBilinear.Statement := by
  have hInt := PtsIntegrable.of_found hAbs hMeas
  intro K _ ι _ P n L T _ u v hP hL hu hv
  unfold ptsIntegral
  by_cases hΨ : ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1 + 1) → ℂ), IsGoodProj P Ψ
  · simp only [dif_pos hΨ]
    have hfin := fibreFinite K ι P (n + 1) hΨ.choose hP hΨ.choose_spec
    unfold ptsIntegralAt
    constructor
    · rw [← integral_finsetSum _ fun t _ =>
        integrable_fibreSum hInt hΨ.choose L hP hΨ.choose_spec hL hv (hu t)]
      congr 1
      funext y
      rw [finsum_mem_congr rfl fun w _ => sheetDensity_sum_left P hΨ.choose _ u y w,
        finsum_mem_sum_comm (hfin y)]
    · rw [← integral_finsetSum _ fun t _ =>
        integrable_fibreSum hInt hΨ.choose L hP hΨ.choose_spec hL (hu t) hv]
      congr 1
      funext y
      rw [finsum_mem_congr rfl fun w _ => sheetDensity_sum_right P hΨ.choose L hu v y w,
        finsum_mem_sum_comm (hfin y)]
  · simp only [dif_neg hΨ, Finset.sum_const_zero, and_self]

end GroundTheory.Heights₂.Heights
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PMoriwakiBigCurve
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.Geo Filter

theorem chartLat_le_chartLatNm {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    (y : (Σ k, ι k) → Ω) (a : K → ℤ) (τ : ℕ) : chartLat y a τ ≤ chartLatNm y a τ := fun _ hs c hc =>
  (mem_integralClosure_iff _ _).mpr (isIntegral_algebraMap (R := chartRingZ y c) (A := Ω) (x := ⟨_, hs c hc⟩))

theorem MoriwakiBigCurve.proof (hL : CurveCountLower.Statement)
    (hPk : HilbertSamuel.SmallPacking.Statement) : MoriwakiBigCurve.Statement := by
  intro K _ ι _ Ω _ y A P0 II hII hP hB _ hS hC _ _
  set Q := IsSmallH (mCoordIdeal y) y A
  set La := chartLat y A.a
  set T := II K ι (mCoordIdeal y) (0 + 1) (fun _ => A)
  obtain ⟨C, hC⟩ := hL K ι Ω y A II hII hP hB hS.1 hC
  obtain ⟨C', hC'⟩ := (hPk K ι Ω y 0 A La hP hB hS.1 fun τ => chartLat_le_chartLatNm y A.a τ).2
  have h0 : ∀ τ, 0 ≤ smallSectionCount Q La τ := fun τ => Real.log_natCast_nonneg _
  have hf : (fun k : ℕ => smallSectionCount Q La (1 * k) / (((1 * k : ℕ) : ℝ) ^ (0 + 1) / ((0 + 1).factorial : ℝ))) =
      fun k : ℕ => smallSectionCount Q La k / k := by
    funext k
    simp
  unfold arVolP
  rw [hf]
  have hC'0 : 0 ≤ C' := by simpa using (h0 0).trans (hC' 0)
  have hbdd : IsBoundedUnder (· ≤ ·) atTop fun k : ℕ => smallSectionCount Q La k / k := by
    refine ⟨2 * C', eventually_map.mpr ((eventually_ge_atTop 1).mono fun k hk => ?_)⟩
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    show smallSectionCount Q La k / k ≤ 2 * C'
    rw [div_le_iff₀ (by linarith)]
    have h1 : smallSectionCount Q La k ≤ C' * ((k : ℝ) + 1) := by simpa using hC' k
    nlinarith
  refine le_of_forall_sub_le fun ε hε => le_limsup_of_frequently_le ?_ hbdd
  refine Eventually.frequently ((eventually_ge_atTop (⌈C / ε⌉₊ + 1)).mono fun k hk => ?_)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (Nat.le_add_left 1 _).trans hk
  have hkC : C ≤ ε * k := by
    have h1 : C / ε ≤ k := (Nat.le_ceil _).trans (by exact_mod_cast (Nat.le_succ _).trans hk)
    rwa [div_le_iff₀ hε, mul_comm] at h1
  have hτ : (k : ℝ) * T - C ≤ smallSectionCount Q La k := hC k ((Nat.le_add_left 1 _).trans hk)
  rw [le_div_iff₀ (by linarith)]
  show (T - ε) * k ≤ _
  nlinarith

end GroundTheory.Heights₂.Heights.Targets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PChartDivisorCompare
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar IsSectionOn ptsIntegral pot segre divSupp IsHorizontal
  multAt divSupp_finite divSuppArith)
open GroundTheory.Heights₂.Heights (varInt localMult IsDegZeroSmooth segreChartSet segreChartComponents chartLift
  SegreChartIntegral.Statement)

theorem segreChartSet_mono {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {P W : Ideal (MRing ι)}
    (h : P ≤ W) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) :
    segreChartSet W σ i ⊆ segreChartSet P σ i := by
  rintro _ ⟨z, ⟨hz1, hz2⟩, hzi, rfl⟩
  exact ⟨z, ⟨hz1, fun f hf => hz2 f (h hf)⟩, hzi, rfl⟩

theorem ptsIntegral_eq_sum_chart (hInt : SegreChartIntegral.Statement) (hPts : SegreChartIntegralPoints.Statement)
    {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {P W : Ideal (MRing ι)} {n m : ℕ}
    {σ : Fin m ≃ ((k : K) → ι k)} {i : (k : K) → ι k} {L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} {g : ((Σ k, ι k) → ℂ) → ℝ} {δ : ℝ}
    {G : (Fin m → ℂ) → ℝ} {Φ : Fin n → (Fin m → ℂ) → ℝ} (hW : IsArithVar W (n + 1)) (hPW : P ≤ W)
    (hL : ∀ j, IsSmoothHerm (L j)) (hg : IsDegZeroSmooth g) (hδ : 0 < δ)
    (hsupp : ∀ z, ‖segre z i‖ < δ * ‖segre z‖ → g z = 0)
    (hgerm : ∀ x ∈ segreChartSet P σ i,
      G =ᶠ[𝓝 x] g ∘ chartLift σ i ∧ ∀ j, Φ j =ᶠ[𝓝 x] pot L j ∘ chartLift σ i) :
    ptsIntegral W (pot L) g = ∑ W' ∈ segreChartComponents W σ i, varInt W' n G Φ := by
  have hsub := segreChartSet_mono hPW σ i
  cases n with
  | zero => exact hPts K ι W m σ i L g δ G Φ hW hg hδ hsupp fun x hx => (hgerm x (hsub hx)).1
  | succ e => exact hInt K ι W e m σ i L g δ G Φ hW hL hg hδ (Or.inl hsupp) fun x hx => hgerm x (hsub hx)

theorem ChartDivisorCompare.proof (hInt : SegreChartIntegral.Statement) (hPts : SegreChartIntegralPoints.Statement)
    (hComp : ChartDivisorComponents.Statement) (hLen : ChartDivisorLength.Statement) :
    ChartDivisorCompare.Statement := by
  classical
  intro K _ _ ι _ P n m σ i L A s g δ G Φ hP hL hs hg hδ hsupp hgerm
  obtain ⟨hmin, hdisj⟩ := hComp K ι P n m σ i A s hP hs
  have hfin : {W | W ∈ divSupp P s ∧ IsHorizontal W}.Finite := (divSupp_finite P s).subset fun _ h => h.1
  set S := hfin.toFinset with hS
  set T := S.biUnion fun W => segreChartComponents W σ i with hT
  have hA : ∀ J ∈ segreChartComponents P σ i,
      ∑ᶠ (W' : Ideal (MvPolynomial (Fin m) ℂ)) (_ : W' ∈ (J ⊔ Ideal.span {chartSection σ i s}).minimalPrimes),
          (localMult (J ⊔ Ideal.span {chartSection σ i s}) W' : ℝ) * varInt W' n G Φ =
        ∑ W' ∈ T, if J ≤ W' then
          (localMult (J ⊔ Ideal.span {chartSection σ i s}) W' : ℝ) * varInt W' n G Φ else 0 := by
    intro J hJ
    have hset : (J ⊔ Ideal.span {chartSection σ i s}).minimalPrimes = ↑(T.filter fun W' => J ≤ W') := by
      ext W'
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, hmin J hJ W', hT, hS, Finset.mem_biUnion,
        Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
      tauto
    rw [hset, finsum_mem_coe_finset, Finset.sum_filter]
  have hB : ∀ W ∈ S, ∀ W' ∈ segreChartComponents W σ i,
      ∑ J ∈ segreChartComponents P σ i, (if J ≤ W' then
          (localMult (J ⊔ Ideal.span {chartSection σ i s}) W' : ℝ) * varInt W' n G Φ else 0) =
        (multAt (P ⊔ Ideal.span {s}) W : ℝ) * varInt W' n G Φ := by
    intro W hW W' hW'
    rw [Set.Finite.mem_toFinset] at hW
    rw [← Finset.sum_filter, ← Finset.sum_mul, ← Nat.cast_sum, hLen K ι P n m σ i A s hP hs W hW.1 hW.2 W' hW']
  have hdisjT : (↑S : Set (Ideal (MRing ι))).PairwiseDisjoint fun W => segreChartComponents W σ i := by
    intro W₁ h₁ W₂ h₂ hne
    rw [Finset.mem_coe, Set.Finite.mem_toFinset] at h₁ h₂
    exact Finset.disjoint_left.2 fun W' hW₁ hW₂ => hne (hdisj W₁ W₂ h₁ h₂ W' hW₁ hW₂)
  rw [Finset.sum_congr rfl hA, Finset.sum_comm, Finset.sum_biUnion hdisjT,
    Finset.sum_congr rfl fun W hW => Finset.sum_congr rfl (hB W hW), eq_comm]
  refine (finsum_mem_eq_finite_toFinset_sum
    (fun W => (multAt (P ⊔ Ideal.span {s}) W : ℝ) * ptsIntegral W (pot L) g) hfin).trans ?_
  refine Finset.sum_congr rfl fun W hW => ?_
  rw [← Finset.mul_sum]
  rw [Set.Finite.mem_toFinset] at hW
  have hWv : IsArithVar W (n + 1) := (divSuppArith K ι P (n + 1) A s W hP hs hW.1).1 hW.2
  rw [ptsIntegral_eq_sum_chart hInt hPts hWv (le_sup_left.trans hW.1.1.1.2) hL hg hδ hsupp hgerm]

end GroundTheory.Heights₂.Heights.Targets
end
end
