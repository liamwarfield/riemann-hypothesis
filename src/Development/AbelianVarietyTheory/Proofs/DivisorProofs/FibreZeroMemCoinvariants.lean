module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldPlaceRestrictionExistsPow

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoinvariantOfLocallyConstantTwist
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoinvariantOfLocallyConstantTwist
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer

namespace GlobalTheory.RankFibreKer

theorem mem_coinv_of_finset_sum (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ν β : kˣ →* ℂˣ) (a b : ℕ) (Φ χ : Matrix (Fin a) (Fin (a + b)) k → ℂ)
    (R : Finset (GL (Fin a) k)) (hΦ : Φ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k)) (hχ : IsLocallyConstant χ)
    (h1 : ∀ Y, Φ Y = ∑ r ∈ R, χ ((r⁻¹).val * Y) * Φ Y)
    (h2 : ∀ Y, χ Y * ∑ r ∈ R, tw ν (a + b) r * Φ (r.val * Y) = 0) : Φ ∈ coinv ν β a (a + b) := by
  set H : GL (Fin a) k → Matrix (Fin a) (Fin (a + b)) k → ℂ :=
    fun r Y => χ Y * (tw ν (a + b) r * Φ (r.val * Y)) with hH
  have hHSB : ∀ r, H r ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k) := by
    intro r
    have hs : (fun Y => Φ (r.val * Y)) ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k) := by
      have := comp_mul_mem_SB r 1 hΦ
      simp only [Units.val_one, Matrix.mul_one] at this
      exact this
    obtain ⟨hs1, hs2⟩ := hs
    have e : H r = χ * ((fun _ => tw ν (a + b) r) * fun Y => Φ (r.val * Y)) := rfl
    rw [e]
    refine ⟨?_, ?_⟩
    · exact hχ.mul ((IsLocallyConstant.const _).mul hs1)
    · exact HasCompactSupport.mul_left (HasCompactSupport.mul_left hs2)
  have hom : ∀ r, omA ν β r 1 (H r) = fun Y => χ ((r⁻¹).val * Y) * Φ Y := by
    intro r
    funext Y
    rw [omA_one_apply]
    simp only [hH, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    field_simp [tw_ne_zero ν (a + b) r]
  have hsumH : ∑ r ∈ R, H r = 0 := by
    funext Y
    rw [Finset.sum_apply, Pi.zero_apply]
    simp only [hH, ← Finset.mul_sum]
    exact h2 Y
  have hΦeq : Φ = ∑ r ∈ R, (omA ν β r 1 (H r) - H r) := by
    rw [Finset.sum_sub_distrib, hsumH, sub_zero]
    funext Y
    rw [Finset.sum_apply]
    simp only [hom]
    exact h1 Y
  rw [hΦeq]
  refine Submodule.sum_mem _ fun r _ => Submodule.subset_span ⟨r, H r, hHSB r, rfl⟩

end GlobalTheory.RankFibreKer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoinvariantOfLocallyConstantTwistStatement
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coinvariant_of_locally_constant_twist : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ν β : kˣ →* ℂˣ) (a b : ℕ) (Φ χ : Matrix (Fin a) (Fin (a + b)) k → ℂ) (R : Finset (GL (Fin a) k)),
    Φ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k) → IsLocallyConstant χ →
    (∀ Y, Φ Y = ∑ r ∈ R, χ ((r⁻¹).val * Y) * Φ Y) →
    (∀ Y, χ Y * ∑ r ∈ R, tw ν (a + b) r * Φ (r.val * Y) = 0) → Φ ∈ coinv ν β a (a + b) := by
  first | exact @GlobalTheory.RankFibreKer.mem_coinv_of_finset_sum | exact GlobalTheory.RankFibreKer.mem_coinv_of_finset_sum | (intros; apply GlobalTheory.RankFibreKer.mem_coinv_of_finset_sum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SliceSectionHaarDecompositionStatement
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLocallyConstant_indicator_mul_slice : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ) (K : Subgroup (GL (Fin a) k)), IsOpen (K : Set (GL (Fin a) k)) → K ≤ KO k (Fin a) →
    (∀ Y : Matrix (Fin a) (Fin d) k, Y.rank = a ↔ ∃ J, minor Y J ≠ 0) →
    ∀ (s : Matrix (Fin a) (Fin d) k → GL (Fin a) k), ContinuousOn s {Y | Y.rank = a} →
    (∀ Y : Matrix (Fin a) (Fin d) k, Y.rank = a → ((s Y)⁻¹).val * Y ∈ slice (k := k) a d) →
    (∀ (Z : Matrix (Fin a) (Fin d) k) (g : GL (Fin a) k), Z ∈ slice (k := k) a d → g.val * Z ∈ slice (k := k) a d → g = 1) →
    IsLocallyConstant (Set.indicator {Y : Matrix (Fin a) (Fin d) k | ∃ x ∈ K, ∃ Z ∈ slice (k := k) a d, Y = x.val * Z}
      (1 : Matrix (Fin a) (Fin d) k → ℂ)) := by
  intro k _ _ _ _ a d K hKo hKO hrank s hs hsec huniq
  set T : Set (Matrix (Fin a) (Fin d) k) := {Y | ∃ x ∈ K, ∃ Z ∈ slice (k := k) a d, Y = x.val * Z} with hTdef
  set O : Set (Matrix (Fin a) (Fin d) k) := {Y | Y.rank = a} with hOdef
  have hmc : ∀ J : Fin a ↪ Fin d, Continuous fun Y : Matrix (Fin a) (Fin d) k => minor Y J := fun J => by
    unfold minor
    exact (continuous_id.matrix_submatrix id J).matrix_det

  have hT : ∀ Y ∈ O, (Y ∈ T ↔ s Y ∈ K) := by
    intro Y hY
    constructor
    · rintro ⟨x, hx, Z, hZ, rfl⟩
      have h1 : ((s (x.val * Z))⁻¹ * x).val * Z ∈ slice (k := k) a d := by
        rw [Units.val_mul, Matrix.mul_assoc]; exact hsec _ hY
      have h2 := huniq Z _ hZ h1
      have h3 : x = s (x.val * Z) := by
        have := congrArg (fun g => s (x.val * Z) * g) h2
        simpa [← mul_assoc] using this
      rw [← h3]; exact hx
    · intro h
      refine ⟨s Y, h, _, hsec Y hY, ?_⟩
      rw [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  have hTmin : ∀ Y ∈ T, ∃ J, valuation k (minor Y J) = 1 := by
    rintro Y ⟨x, hx, Z, ⟨J, hJ, -⟩, rfl⟩
    refine ⟨J, ?_⟩
    rw [minor_mul, minor, hJ, Matrix.det_one, mul_one]
    have := valuation_gdet_of_mem_KO (hKO hx)
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using this
  have hTO : T ⊆ O := by
    intro Y hY
    obtain ⟨J, hJ⟩ := hTmin Y hY
    refine (hrank Y).2 ⟨J, fun h => ?_⟩
    rw [h, map_zero] at hJ
    exact zero_ne_one hJ
  have hOopen : IsOpen O := by
    rw [isOpen_iff_mem_nhds]
    intro Y hY
    obtain ⟨J, hJ⟩ := (hrank Y).1 hY
    have hv : valuation k (minor Y J) ≠ 0 := by simpa using hJ
    have hn := (valuation k).locally_const hv
    have := (hmc J).continuousAt.preimage_mem_nhds hn
    refine Filter.mem_of_superset this fun Y' hY' => (hrank Y').2 ⟨J, fun h0 => ?_⟩
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, h0, map_zero] at hY'
    exact hv hY'.symm
  have hKc : IsClosed (K : Set (GL (Fin a) k)) := Subgroup.isClosed_of_isOpen K hKo
  have hTeq : T = O ∩ s ⁻¹' (K : Set (GL (Fin a) k)) := by
    ext Y
    constructor
    · intro h; exact ⟨hTO h, (hT Y (hTO h)).1 h⟩
    · rintro ⟨h1, h2⟩; exact (hT Y h1).2 h2
  have hTopen : IsOpen T := by
    rw [hTeq]; exact hs.isOpen_inter_preimage hOopen hKo
  have h0 : {x : k | valuation k x < 1} ∈ nhds (0 : k) := by
    have := (IsValuativeTopology.hasBasis_nhds_zero k).mem_of_mem (i := 1) trivial
    simpa using this
  have hTclosed : IsClosed T := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro Y hY
    by_cases hYO : Y ∈ O
    · have hsY : s Y ∉ K := fun h => hY ((hT Y hYO).2 h)
      have ho : IsOpen (O ∩ s ⁻¹' (K : Set (GL (Fin a) k))ᶜ) := hs.isOpen_inter_preimage hOopen hKc.isOpen_compl
      refine Filter.mem_of_superset (ho.mem_nhds ⟨hYO, hsY⟩) fun Y' hY' hT' => hY'.2 ?_
      exact (hT Y' hY'.1).1 hT'
    · have hz : ∀ J, minor Y J = 0 := by
        intro J; by_contra hne; exact hYO ((hrank Y).2 ⟨J, hne⟩)
      have hW : (⋂ J : Fin a ↪ Fin d, (fun Y' => minor Y' J) ⁻¹' {x : k | valuation k x < 1}) ∈ nhds Y := by
        refine Filter.iInter_mem.2 fun J => ?_
        refine (hmc J).continuousAt.preimage_mem_nhds ?_
        rw [hz J]; exact h0
      refine Filter.mem_of_superset hW fun Y' hY' hT' => ?_
      obtain ⟨J, hJ⟩ := hTmin Y' hT'
      have := Set.mem_iInter.1 hY' J
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, hJ] at this
      exact lt_irrefl _ this
  exact (LocallyConstant.indicator (1 : LocallyConstant _ ℂ) ⟨hTclosed, hTopen⟩).isLocallyConstant
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstMaximalMinorLocallyConstant
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstMaximalMinorLocallyConstant
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer

namespace GlobalTheory.RankFibreKer

theorem isFirstMax_eventually (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (a d : ℕ) (Y : Matrix (Fin a) (Fin d) k) (J : Fin a ↪ Fin d) :
    IsFirstMax Y J → ∀ᶠ Y' in nhds Y, IsFirstMax Y' J := by
  rintro ⟨h0, hle⟩
  have hm : valuation k (minor Y J) ≠ 0 := (Valuation.ne_zero_iff _).2 h0
  have hc : ∀ J' : Fin a ↪ Fin d, Continuous fun Y' : Matrix (Fin a) (Fin d) k => minor Y' J' := fun J' =>
    (continuous_id.matrix_submatrix id J').matrix_det
  have key : ∀ J' : Fin a ↪ Fin d, ∀ᶠ Y' in nhds Y,
      valuation k (minor Y' J') = valuation k (minor Y J') ∨
        (minor Y J' = 0 ∧ valuation k (minor Y' J') < valuation k (minor Y J)) := by
    intro J'
    by_cases hz : minor Y J' = 0
    · have hn : {x : k | valuation k x < ((Units.mk0 _ hm : (ValueGroupWithZero k)ˣ) : ValueGroupWithZero k)}
          ∈ nhds (0 : k) := (IsValuativeTopology.mem_nhds_zero_iff _).2 ⟨Units.mk0 _ hm, subset_rfl⟩
      have hca := (hc J').continuousAt (x := Y)
      rw [ContinuousAt, hz] at hca
      filter_upwards [hca hn] with Y' hY'
      exact Or.inr ⟨hz, hY'⟩
    · have hne : valuation k (minor Y J') ≠ 0 := (Valuation.ne_zero_iff _).2 hz
      filter_upwards [(hc J').continuousAt (x := Y) ((valuation k).locally_const hne)] with Y' hY'
      exact Or.inl hY'
  have hall := Filter.eventually_all.2 key
  filter_upwards [hall] with Y' hY'
  have hJ : valuation k (minor Y' J) = valuation k (minor Y J) := by
    rcases hY' J with h | ⟨h, -⟩
    · exact h
    · exact absurd h h0
  refine ⟨(Valuation.ne_zero_iff _).1 (hJ ▸ hm), fun J' => ?_⟩
  rw [hJ]
  rcases hY' J' with h | ⟨-, h⟩
  · rw [h]; exact hle J'
  · exact ⟨h.le, fun _ => h⟩

end GlobalTheory.RankFibreKer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstMaximalMinorLocallyConstantStatement
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.first_maximal_minor_locally_constant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ) (Y : Matrix (Fin a) (Fin d) k) (J : Fin a ↪ Fin d), IsFirstMax Y J →
    ∀ᶠ Y' in nhds Y, IsFirstMax Y' J := by
  first | exact @GlobalTheory.RankFibreKer.isFirstMax_eventually | exact GlobalTheory.RankFibreKer.isFirstMax_eventually | (intros; apply GlobalTheory.RankFibreKer.isFirstMax_eventually <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarIntegralOverCosetRepresentatives
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarIntegralOverCosetRepresentatives
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer
open scoped Pointwise

namespace GlobalTheory.HaarCosetSum

theorem integral_eq_vol_mul_sum_of_cosets :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (a : ℕ) (K : Subgroup (GL (Fin a) k)),
    IsOpen (K : Set (GL (Fin a) k)) → K ≤ KO k (Fin a) → ∀ F : GL (Fin a) k → ℂ,
    (∀ g x, x ∈ K → F (g * x) = F g) → ∀ R : Finset (GL (Fin a) k),
    (∀ r ∈ R, ∀ r' ∈ R, r⁻¹ * r' ∈ K → r = r') → (∀ g, F g ≠ 0 → ∃ r ∈ R, r⁻¹ * g ∈ K) →
    ∫ g, F g ∂(haarVol (KO k (Fin a))) = ((haarVol (KO k (Fin a))).real (K : Set (GL (Fin a) k)) : ℂ) * ∑ r ∈ R, F r := by
  intro k _ _ _ _ _ _ a K hKo hKle F hF R hR hsupp
  set μ := haarVol (KO k (Fin a)) with hμ
  have hKm : MeasurableSet (K : Set (GL (Fin a) k)) := hKo.measurableSet

  have hval : ∀ r g, r⁻¹ * g ∈ K → F g = F r := by
    intro r g h
    have := hF r (r⁻¹ * g) h
    rwa [mul_inv_cancel_left] at this

  have hpt : ∀ g, F g = ∑ r ∈ R, ((r • (K : Set (GL (Fin a) k))).indicator (fun _ => F r) g) := by
    intro g
    by_cases hg : F g = 0
    · rw [hg]
      refine (Finset.sum_eq_zero fun r _ => ?_).symm
      by_cases hm : g ∈ r • (K : Set (GL (Fin a) k))
      · rw [Set.indicator_of_mem hm, ← hval r g ((mem_leftCoset_iff r).1 hm), hg]
      · rw [Set.indicator_of_notMem hm]
    · obtain ⟨r₀, hr₀, hg₀⟩ := hsupp g hg
      rw [Finset.sum_eq_single r₀]
      · rw [Set.indicator_of_mem ((mem_leftCoset_iff r₀).2 hg₀), hval r₀ g hg₀]
      · intro r hr hne
        rw [Set.indicator_of_notMem]
        intro hm
        have h1 : r⁻¹ * g ∈ K := (mem_leftCoset_iff r).1 hm
        have h2 : r⁻¹ * r₀ ∈ K := by
          have := K.mul_mem h1 (K.inv_mem hg₀)
          simpa [mul_assoc] using this
        exact hne (hR r hr r₀ hr₀ h2)
      · intro h; exact absurd hr₀ h
  have hfin : μ (K : Set (GL (Fin a) k)) ≠ ⊤ :=
    ((measure_mono hKle).trans_lt isCompact_KO.measure_lt_top).ne
  have hcos : ∀ r : GL (Fin a) k, μ (r • (K : Set (GL (Fin a) k))) = μ K := fun r => measure_smul μ r _
  have hint : ∀ r ∈ R, Integrable ((r • (K : Set (GL (Fin a) k))).indicator (fun _ => F r)) μ := by
    intro r _
    rw [integrable_indicator_iff (hKm.const_smul r)]
    exact integrableOn_const (by rw [hcos]; exact hfin)
  calc ∫ g, F g ∂μ = ∫ g, ∑ r ∈ R, ((r • (K : Set (GL (Fin a) k))).indicator (fun _ => F r) g) ∂μ := by
          congr 1; funext g; exact hpt g
    _ = ∑ r ∈ R, ∫ g, ((r • (K : Set (GL (Fin a) k))).indicator (fun _ => F r) g) ∂μ :=
          MeasureTheory.integral_finsetSum R hint
    _ = ∑ r ∈ R, (μ.real (K : Set (GL (Fin a) k)) : ℂ) * F r := by
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [integral_indicator_const _ (hKm.const_smul r), Measure.real, hcos, ← Measure.real,
            Complex.real_smul]
    _ = _ := by rw [Finset.mul_sum]

end GlobalTheory.HaarCosetSum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarIntegralOverCosetRepresentativesStatement
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_integral_over_coset_representatives : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (a : ℕ) (K : Subgroup (GL (Fin a) k)),
    IsOpen (K : Set (GL (Fin a) k)) → K ≤ KO k (Fin a) → ∀ F : GL (Fin a) k → ℂ,
    (∀ g x, x ∈ K → F (g * x) = F g) → ∀ R : Finset (GL (Fin a) k),
    (∀ r ∈ R, ∀ r' ∈ R, r⁻¹ * r' ∈ K → r = r') → (∀ g, F g ≠ 0 → ∃ r ∈ R, r⁻¹ * g ∈ K) →
    ∫ g, F g ∂(haarVol (KO k (Fin a))) = ((haarVol (KO k (Fin a))).real (K : Set (GL (Fin a) k)) : ℂ) * ∑ r ∈ R, F r := by
  first | exact @GlobalTheory.HaarCosetSum.integral_eq_vol_mul_sum_of_cosets | exact GlobalTheory.HaarCosetSum.integral_eq_vol_mul_sum_of_cosets | (intros; apply GlobalTheory.HaarCosetSum.integral_eq_vol_mul_sum_of_cosets <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankIffNonzeroMinor
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankIffNonzeroMinor
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer

namespace GlobalTheory.RankFibreKer

theorem rank_eq_iff_exists_minor_ne_zero (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (a d : ℕ) (Y : Matrix (Fin a) (Fin d) k) :
    Y.rank = a ↔ ∃ J, minor Y J ≠ 0 := by
  constructor
  · intro hr
    obtain ⟨κ, f, hinj, hspan, hli⟩ := exists_linearIndependent' k Y.col
    haveI : Finite κ := Finite.of_injective f hinj
    haveI : Fintype κ := Fintype.ofFinite κ
    have hcard : Fintype.card κ = a := by
      rw [← finrank_span_eq_card hli, hspan, ← Matrix.rank_eq_finrank_span_cols, hr]
    let e : κ ≃ Fin a := Fintype.equivFinOfCardEq hcard
    let J : Fin a ↪ Fin d := ⟨f ∘ e.symm, hinj.comp e.symm.injective⟩
    refine ⟨J, ?_⟩
    have hc : (Y.submatrix id J).col = (Y.col ∘ f) ∘ e.symm := by
      funext j i; rfl
    have hli' : LinearIndependent k (Y.submatrix id J).col := by
      rw [hc]; exact hli.comp e.symm e.symm.injective
    have hu := Matrix.linearIndependent_cols_iff_isUnit.mp hli'
    exact ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero
  · rintro ⟨J, hJ⟩
    have hu : IsUnit (Y.submatrix id J) := (Matrix.isUnit_iff_isUnit_det _).mpr (Ne.isUnit hJ)
    have hli' := Matrix.linearIndependent_rows_iff_isUnit.mpr hu
    have hr : (Y.submatrix id J).row = (LinearMap.funLeft k k J) ∘ Y.row := by
      funext i j; rfl
    rw [hr] at hli'
    have hli := LinearIndependent.of_comp _ hli'
    rw [Matrix.rank_eq_finrank_span_row, finrank_span_eq_card hli, Fintype.card_fin]

end GlobalTheory.RankFibreKer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankIffNonzeroMinorStatement
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.full_rank_iff_nonzero_minor : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ) (Y : Matrix (Fin a) (Fin d) k), Y.rank = a ↔ ∃ J, minor Y J ≠ 0 := by
  first | exact @GlobalTheory.RankFibreKer.rank_eq_iff_exists_minor_ne_zero | exact GlobalTheory.RankFibreKer.rank_eq_iff_exists_minor_ne_zero | (intros; apply GlobalTheory.RankFibreKer.rank_eq_iff_exists_minor_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SliceStabilizerTrivialStatement
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.slice_stabilizer_trivial : ∀ (k : Type) [Field k]
    [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (a d : ℕ) (Z : Matrix (Fin a) (Fin d) k) (g : GL (Fin a) k),
    Z ∈ slice (k := k) a d → g.val * Z ∈ slice (k := k) a d → g = 1 := by
  rintro k _ _ _ _ a d Z g ⟨J, hJ, hZ⟩ ⟨J', hJ', hgZ⟩
  have hminor : minor Z J = 1 := by rw [minor, hJ, det_one]
  have hminor' : minor (g.val * Z) J' = 1 := by rw [minor, hJ', det_one]
  have hproduct : valuation k (g.val.det) * valuation k (minor Z J') = 1 := by
    rw [← map_mul, ← minor_mul, hminor', map_one]
  have hdet_le : valuation k (g.val.det) ≤ 1 := by
    have h := (hgZ J).1
    rwa [minor_mul, hminor, mul_one] at h
  have hslice : valuation k (minor Z J') = 1 := by
    refine le_antisymm (hZ J').1 ?_
    calc
      (1 : ValueGroupWithZero k) = valuation k (g.val.det) * valuation k (minor Z J') :=
        hproduct.symm
      _ ≤ 1 * valuation k (minor Z J') := mul_le_mul_of_nonneg_right hdet_le zero_le
      _ = valuation k (minor Z J') := one_mul _
  have hdet : valuation k (g.val.det) = 1 := by rwa [hslice, mul_one] at hproduct
  have hindices : J = J' := by
    rcases lt_trichotomy (idx J') (idx J) with h | h | h
    · exact absurd ((hZ J').2 h) (by rw [hslice]; exact lt_irrefl _)
    · exact (idx.injective h).symm
    · have hlt := (hgZ J).2 h
      rw [minor_mul, hminor, mul_one, hdet] at hlt
      exact absurd hlt (lt_irrefl _)
  subst J'
  have hsub : (g.val * Z).submatrix id J = g.val * Z.submatrix id J := by
    ext i j
    simp [Matrix.mul_apply, submatrix_apply]
  rw [hsub, hJ, Matrix.mul_one] at hJ'
  exact Units.ext hJ'
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousSliceSectionIntegralStatement
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer

open scoped Pointwise in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_slice_section_integral : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ) (Φ : Matrix (Fin a) (Fin d) k → ℂ), Φ ∈ fullRankSB (k := k) a d →
    ∀ (s : Matrix (Fin a) (Fin d) k → GL (Fin a) k), ContinuousOn s {Y | Y.rank = a} →
    (∀ Y : Matrix (Fin a) (Fin d) k, Y.rank = a → ((s Y)⁻¹).val * Y ∈ slice (k := k) a d) →
    (∀ (Z : Matrix (Fin a) (Fin d) k) (g : GL (Fin a) k), Z ∈ slice (k := k) a d → g.val * Z ∈ slice (k := k) a d → g = 1) →
    ∃ U ∈ nhds (1 : GL (Fin a) k), ∀ x ∈ U, ∀ (g : GL (Fin a) k), ∀ Z ∈ slice (k := k) a d,
      Φ (g.val * x.val * Z) = Φ (g.val * Z) := by
  intro k _ _ _ _ a d Φ hΦ s hs hsl huniq
  have hInvariant : ∃ U ∈ nhds (1 : GL (Fin a) k), ∀ x ∈ U, ∀ (g : GL (Fin a) k), ∀ Z ∈ slice (k := k) a d,
        Φ (g.val * x.val * Z) = Φ (g.val * Z) := by
    obtain ⟨⟨hlc, hcpt⟩, hrk⟩ := hΦ

    have hcl : IsClosed (Function.support Φ) := by
      have : Function.support Φ = (Φ ⁻¹' {0})ᶜ := by ext; simp
      rw [this, isClosed_compl_iff]; exact hlc.isOpen_fiber 0
    have hS : tsupport Φ ⊆ {Y | Y.rank = a} := by
      intro Y hY
      rw [tsupport, hcl.closure_eq] at hY
      by_contra h; exact hY (hrk Y h)
    set f : Matrix (Fin a) (Fin d) k → GL (Fin a) k × Matrix (Fin a) (Fin d) k :=
      fun Y => (s Y, ((s Y)⁻¹).val * Y) with hf
    have hfc : ContinuousOn f (tsupport Φ) := by
      have hs' := hs.mono hS
      refine ContinuousOn.prodMk hs' ?_
      exact (Continuous.matrix_mul continuous_fst continuous_snd).comp_continuousOn
        ((Units.continuous_val.comp_continuousOn hs'.inv).prodMk continuousOn_id)
    have hA : IsCompact (f '' tsupport Φ) := hcpt.image_of_continuousOn hfc
    set n : Set ((GL (Fin a) k × Matrix (Fin a) (Fin d) k) × GL (Fin a) k) :=
      {p | Φ (p.1.1.val * p.2.val * p.1.2) = Φ (p.1.1.val * p.1.2)} with hn
    have hno : IsOpen n := by
      have h1 : IsLocallyConstant (fun p : (GL (Fin a) k × Matrix (Fin a) (Fin d) k) × GL (Fin a) k =>
          Φ (p.1.1.val * p.2.val * p.1.2)) :=
        hlc.comp_continuous (by fun_prop)
      have h2 : IsLocallyConstant (fun p : (GL (Fin a) k × Matrix (Fin a) (Fin d) k) × GL (Fin a) k =>
          Φ (p.1.1.val * p.1.2)) :=
        hlc.comp_continuous (by fun_prop)
      exact (h1.prodMk h2) {q | q.1 = q.2}
    have hsub : (f '' tsupport Φ) ×ˢ ({1} : Set (GL (Fin a) k)) ⊆ n := by
      rintro ⟨⟨g, Z⟩, x⟩ ⟨_, hx⟩
      simp only [Set.mem_singleton_iff] at hx
      subst hx
      simp [hn]
    obtain ⟨u, v, -, hv, hAu, h1v, huv⟩ := generalized_tube_lemma hA isCompact_singleton hno hsub

    have key : ∀ (h : GL (Fin a) k) (Z : Matrix (Fin a) (Fin d) k), Z ∈ slice (k := k) a d → Φ (h.val * Z) ≠ 0 →
        (h, Z) ∈ f '' tsupport Φ := by
      intro h Z hZ hne
      have hY : h.val * Z ∈ tsupport Φ := subset_tsupport _ hne
      have hr := hS hY
      have e : (s (h.val * Z))⁻¹ * h = 1 := by
        apply huniq Z _ hZ
        have := hsl _ hr
        simpa [Units.val_mul, Matrix.mul_assoc] using this
      have e' : s (h.val * Z) = h := by
        have := congrArg (fun t => s (h.val * Z) * t) e
        simpa [mul_assoc] using this.symm
      refine ⟨h.val * Z, hY, ?_⟩
      simp only [hf, e', Prod.mk.injEq, true_and]
      rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
    refine ⟨v ∩ v⁻¹, Filter.inter_mem (hv.mem_nhds (h1v rfl)) ?_, ?_⟩
    · exact (hv.inv).mem_nhds (by simpa using h1v rfl)
    rintro x ⟨hxv, hxv'⟩ g Z hZ
    by_cases h0 : Φ (g.val * Z) ≠ 0
    · exact huv (Set.mk_mem_prod (hAu (key g Z hZ h0)) hxv)
    by_cases h0' : Φ (g.val * x.val * Z) ≠ 0
    · have hm : (g * x, Z) ∈ f '' tsupport Φ := key (g * x) Z hZ (by simpa [Units.val_mul] using h0')
      have := huv (Set.mk_mem_prod (hAu hm) (show x⁻¹ ∈ v from hxv'))
      simp only [hn, Set.mem_ofPred_eq] at this
      rw [Units.val_mul, Matrix.mul_assoc g.val x.val, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.mul_one] at this
      rw [this]
    push Not at h0 h0'
    rw [h0, h0']
  exact hInvariant
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalIntegralVanishesOfFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalIntegralVanishesOfFibre
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer

namespace GlobalTheory.RankFibreKer

theorem integral_tw_eq_zero_of_fibre_eq_zero :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν β : kˣ →* ℂˣ) (a b : ℕ) (Φ : Matrix (Fin a) (Fin (a + b)) k → ℂ),
    fibre ν β a b Φ = 0 → ∀ Y : Matrix (Fin a) (Fin (a + b)) k, Y.rank = a →
    ∫ g : GL (Fin a) k, Φ (g.val * Y) * tw ν (a + b) g ∂(haarVol (KO k (Fin a))) = 0 := by
  intro k _ _ _ _ _ _ ν β a b Φ hF Y hY
  obtain ⟨h, hYh⟩ := (rank_eq_card_iff_exists_frameMatrixFirstColumnBlock (k := k) finSumFinEquiv Y).1 (by rw [hY, Fintype.card_fin])
  have e := congrFun hF h
  have hC : (β (gdet h) : ℂ) * apow (gdet h) (-(a : ℂ) / 2) ≠ 0 :=
    mul_ne_zero (Units.ne_zero _) (apow_ne_zero _ _)
  have key : ∀ g : GL (Fin a) k, omA ν β 1 h Φ (g.val * X0 k finSumFinEquiv) * (ν (gdet g) : ℂ) *
      apow (gdet g) (((a + b : ℕ) : ℂ) / 2) = ((β (gdet h) : ℂ) * apow (gdet h) (-(a : ℂ) / 2)) *
      (Φ (g.val * Y) * tw ν (a + b) g) := by
    intro g
    have hm : g.val * Y = (((((1 : GL (Fin a) k)⁻¹).val * ((g.val * X0 k finSumFinEquiv : Matrix (Fin a) (Fin (a + b)) k))
        : Matrix (Fin a) (Fin (a + b)) k)) * (invT h).val : Matrix (Fin a) (Fin (a + b)) k) := by
      rw [inv_one, Units.val_one, Matrix.one_mul, hYh]
      exact (Matrix.mul_assoc _ _ _).symm
    rw [hm]
    simp only [omA, tw, Fintype.card_fin, map_one, inv_one, Units.val_one, apow_one]
    ring
  simp only [fibre, Pi.zero_apply, key, integral_const_mul] at e
  exact (mul_eq_zero.1 e).resolve_left hC

end GlobalTheory.RankFibreKer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalIntegralVanishesOfFibreStatement
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbital_integral_vanishes_of_fibre : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν β : kˣ →* ℂˣ) (a b : ℕ) (Φ : Matrix (Fin a) (Fin (a + b)) k → ℂ),
    fibre ν β a b Φ = 0 → ∀ Y : Matrix (Fin a) (Fin (a + b)) k, Y.rank = a →
    ∫ g : GL (Fin a) k, Φ (g.val * Y) * tw ν (a + b) g ∂(haarVol (KO k (Fin a))) = 0 := by
  first | exact @GlobalTheory.RankFibreKer.integral_tw_eq_zero_of_fibre_eq_zero | exact GlobalTheory.RankFibreKer.integral_tw_eq_zero_of_fibre_eq_zero | (intros; apply GlobalTheory.RankFibreKer.integral_tw_eq_zero_of_fibre_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionInverseIntoSlice
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionInverseIntoSlice
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer

namespace GlobalTheory.RankFibreKer

theorem eq_of_isFirstMax_of_isFirstMax {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a d : ℕ} {Y : Matrix (Fin a) (Fin d) k} {J J' : Fin a ↪ Fin d} (h : IsFirstMax Y J) (h' : IsFirstMax Y J') :
    J = J' := by
  apply idx.injective
  rcases lt_trichotomy (idx J) (idx J') with hl | he | hl
  · exact absurd ((h'.2 J).2 hl) (not_lt.2 (h.2 J').1)
  · exact he
  · exact absurd ((h.2 J').2 hl) (not_lt.2 (h'.2 J).1)

theorem sec_inv_mul_mem_slice : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ) (Y : Matrix (Fin a) (Fin d) k) (J : Fin a ↪ Fin d), IsFirstMax Y J →
    ((GlobalTheory.RankFibreKer.sec Y)⁻¹).val * Y ∈ slice (k := k) a d := by
  intro k _ _ _ _ a d Y J hJ
  have hex : ∃ J, IsFirstMax Y J := ⟨J, hJ⟩
  have hc : hex.choose = J := eq_of_isFirstMax_of_isFirstMax hex.choose_spec hJ
  have hs : (sec Y).val = Y.submatrix id J := by
    unfold sec
    rw [dite_eq_left hex]
    show Y.submatrix id hex.choose = _
    rw [hc]
  have hsub : (((sec Y)⁻¹).val * Y).submatrix id J = ((sec Y)⁻¹).val * Y.submatrix id J := by
    ext i j; simp [Matrix.mul_apply]
  have hdet : (((sec Y)⁻¹).val).det = (minor Y J)⁻¹ := by
    have e := congrArg Matrix.det (sec Y).inv_mul
    rw [Matrix.det_mul, Matrix.det_one, hs] at e
    exact eq_inv_of_mul_eq_one_left e
  refine ⟨J, ?_, fun J' => ?_⟩
  · rw [hsub, ← hs]; exact (sec Y).inv_mul
  · rw [minor_mul, hdet, map_mul, map_inv₀]
    have h0 : valuation k (minor Y J) ≠ 0 := by simpa using hJ.1
    constructor
    · rw [inv_mul_le_iff₀ (zero_lt_iff.2 h0), mul_one]; exact (hJ.2 J').1
    · intro hl
      rw [inv_mul_lt_iff₀ (zero_lt_iff.2 h0), mul_one]; exact (hJ.2 J').2 hl

end GlobalTheory.RankFibreKer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionInverseIntoSliceStatement
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.section_inverse_into_slice : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ) (Y : Matrix (Fin a) (Fin d) k) (J : Fin a ↪ Fin d), IsFirstMax Y J →
    ((sec Y)⁻¹).val * Y ∈ slice k a d := by
  first | exact @GlobalTheory.RankFibreKer.sec_inv_mul_mem_slice | exact GlobalTheory.RankFibreKer.sec_inv_mul_mem_slice | (intros; apply GlobalTheory.RankFibreKer.sec_inv_mul_mem_slice <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousSliceSectionMeasureStatement
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_slice_section_measure : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ) (Φ : Matrix (Fin a) (Fin d) k → ℂ), Φ ∈ fullRankSB (k := k) a d →
    ∀ (s : Matrix (Fin a) (Fin d) k → GL (Fin a) k), ContinuousOn s {Y | Y.rank = a} →
    (∀ Y : Matrix (Fin a) (Fin d) k, Y.rank = a → ((s Y)⁻¹).val * Y ∈ slice (k := k) a d) →
    (∀ (Z : Matrix (Fin a) (Fin d) k) (g : GL (Fin a) k), Z ∈ slice (k := k) a d → g.val * Z ∈ slice (k := k) a d → g = 1) →
    ∃ C : Set (GL (Fin a) k), IsCompact C ∧ ∀ (g : GL (Fin a) k) (Z : Matrix (Fin a) (Fin d) k), Z ∈ slice (k := k) a d →
      Φ (g.val * Z) ≠ 0 → g ∈ C := by
  intro k _ _ _ _ a d Φ hΦ s hs hsl huniq
  obtain ⟨⟨hlc, hcs⟩, hrank⟩ := hΦ
  have hclosed : IsClosed (Function.support Φ) :=
    (hlc.isClopen_fiber (0 : ℂ)).compl.isClosed
  have hsub : tsupport Φ ⊆ {Y | Y.rank = a} := by
    change closure (Function.support Φ) ⊆ _
    rw [hclosed.closure_eq]
    intro Y hY
    by_contra h
    exact hY (hrank Y h)
  refine ⟨s '' tsupport Φ, hcs.isCompact.image_of_continuousOn (hs.mono hsub), ?_⟩
  intro g Z hZ hne
  have hY : g.val * Z ∈ tsupport Φ := subset_tsupport _ hne
  have hslice : ((s (g.val * Z))⁻¹ * g).val * Z ∈ slice (k := k) a d := by
    rw [Units.val_mul, Matrix.mul_assoc]
    exact hsl _ (hsub hY)
  have heq := huniq Z _ hZ hslice
  rw [inv_mul_eq_one] at heq
  exact ⟨g.val * Z, hY, heq⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFirstMaximalMinor
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFirstMaximalMinor
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer

namespace GlobalTheory.RankFibreKer

theorem exists_isFirstMax : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (a d : ℕ) (Y : Matrix (Fin a) (Fin d) k),
    (∃ J, minor Y J ≠ 0) → ∃ J, IsFirstMax Y J := by
  intro k _ _ _ _ a d Y ⟨J0, hJ0⟩
  classical
  obtain ⟨M, -, hM⟩ := Finset.exists_max_image Finset.univ (fun J => valuation k (minor Y J))
    ⟨J0, Finset.mem_univ _⟩
  set S := Finset.univ.filter (fun J => valuation k (minor Y J) = valuation k (minor Y M)) with hS
  obtain ⟨J, hJS, hJmin⟩ := S.exists_min_image (fun J => idx J) ⟨M, by simp [S]⟩
  have hJ : valuation k (minor Y J) = valuation k (minor Y M) := (Finset.mem_filter.1 hJS).2
  refine ⟨J, ?_, fun J' => ⟨?_, fun hlt => ?_⟩⟩
  · intro h0
    apply hJ0
    have hM0 : valuation k (minor Y M) = 0 := by rw [← hJ, h0, map_zero]
    have h1 := hM J0 (Finset.mem_univ _)
    rw [hM0] at h1
    exact (Valuation.zero_iff _).1 (le_antisymm h1 zero_le')
  · rw [hJ]; exact hM J' (Finset.mem_univ _)
  · rw [hJ]
    refine lt_of_le_of_ne (hM J' (Finset.mem_univ _)) fun heq => ?_
    have := hJmin J' (by simp [S, heq])
    exact absurd hlt (not_lt.2 this)

end GlobalTheory.RankFibreKer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFirstMaximalMinorStatement
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_first_maximal_minor : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ) (Y : Matrix (Fin a) (Fin d) k), (∃ J, minor Y J ≠ 0) → ∃ J, IsFirstMax Y J := by
  first | exact @GlobalTheory.RankFibreKer.exists_isFirstMax | exact GlobalTheory.RankFibreKer.exists_isFirstMax | (intros; apply GlobalTheory.RankFibreKer.exists_isFirstMax <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreZeroMemCoinvariants
noncomputable section
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil

namespace GlobalTheory.RankFibreKer

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isFirstMax_unique {a d : ℕ} {Y : Matrix (Fin a) (Fin d) k} {J J' : Fin a ↪ Fin d} (h : IsFirstMax Y J)
    (h' : IsFirstMax Y J') : J = J' := by
  rcases lt_trichotomy (idx J) (idx J') with hl | he | hl
  · exact absurd ((h'.2 J).2 hl) (fun H => lt_irrefl _ (H.trans_le ((h.2 J').1)))
  · exact idx.injective he
  · exact absurd ((h.2 J').2 hl) (fun H => lt_irrefl _ (H.trans_le ((h'.2 J).1)))

theorem sec_val {a d : ℕ} {Y : Matrix (Fin a) (Fin d) k} {J : Fin a ↪ Fin d} (h : IsFirstMax Y J) :
    (sec Y).val = Y.submatrix id J := by
  have hex : ∃ J, IsFirstMax Y J := ⟨J, h⟩
  rw [sec, dite_eq_left hex]
  show Y.submatrix id hex.choose = _
  rw [isFirstMax_unique hex.choose_spec h]

theorem continuousOn_sec {a d : ℕ} : ContinuousOn (sec (k := k) (a := a) (d := d)) {Y | Y.rank = a} := by
  intro Y hY
  obtain ⟨J, hJ⟩ := GlobalTheory.T.exists_first_maximal_minor k a d Y ((GlobalTheory.T.full_rank_iff_nonzero_minor k a d Y).1 hY)
  rw [isEmbedding_val_GL.isInducing.continuousWithinAt_iff]
  refine ContinuousAt.continuousWithinAt ?_
  have hc : Continuous fun Y : Matrix (Fin a) (Fin d) k => Y.submatrix id J :=
    (continuous_id.matrix_submatrix id J)
  refine hc.continuousAt.congr ?_
  filter_upwards [GlobalTheory.T.first_maximal_minor_locally_constant k a d Y J hJ] with Y' hY'
  exact (sec_val hY').symm

theorem sec_mem_slice {a d : ℕ} (Y : Matrix (Fin a) (Fin d) k) (hY : Y.rank = a) :
    ((sec Y)⁻¹).val * Y ∈ slice k a d := by
  obtain ⟨J, hJ⟩ := GlobalTheory.T.exists_first_maximal_minor k a d Y ((GlobalTheory.T.full_rank_iff_nonzero_minor k a d Y).1 hY)
  exact GlobalTheory.T.section_inverse_into_slice k a d Y J hJ

theorem vol_ne_zero [MeasurableSpace k] [BorelSpace k] {a : ℕ} (K : Subgroup (GL (Fin a) k))
    (hK : IsOpen (K : Set (GL (Fin a) k))) (hKO : K ≤ KO k (Fin a)) :
    (haarVol (KO k (Fin a))).real (K : Set (GL (Fin a) k)) ≠ 0 := by
  have h0 : haarVol (KO k (Fin a)) (K : Set (GL (Fin a) k)) ≠ 0 :=
    (hK.measure_pos (haarVol (KO k (Fin a))) ⟨1, K.one_mem⟩).ne'
  have h1 : haarVol (KO k (Fin a)) (K : Set (GL (Fin a) k)) ≠ ⊤ :=
    ((measure_mono (μ := haarVol (KO k (Fin a))) (show (K : Set (GL (Fin a) k)) ⊆ KO k (Fin a) from hKO)).trans_lt
      (by rw [haarVol_self isOpen_KO le_rfl]; exact ENNReal.one_lt_top)).ne
  exact ENNReal.toReal_ne_zero.2 ⟨h0, h1⟩

theorem fibre_ker : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (a b : ℕ) (ν β : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν →
    GlobalTheory.SmGL.IsSmoothChar β → ∀ Φ ∈ GlobalTheory.RankFibre.fullRankSB k a (a + b),
    GlobalTheory.RankFibre.fibre ν β a b Φ = 0 → Φ ∈ GlobalTheory.RankFibre.coinv ν β a (a + b) := by
  intro k _ _ _ _ _ _ a b ν β hν _ Φ hΦ hfib
  have hun : ∀ (Z : Matrix (Fin a) (Fin (a + b)) k) (g : GL (Fin a) k), Z ∈ slice k a (a + b) →
      g.val * Z ∈ slice k a (a + b) → g = 1 := GlobalTheory.T.slice_stabilizer_trivial k a (a + b)
  have hsc := continuousOn_sec (k := k) (a := a) (d := a + b)
  have hsl := sec_mem_slice (k := k) (a := a) (d := a + b)
  obtain ⟨U, hU, hUf⟩ := GlobalTheory.T.continuous_slice_section_integral k a (a + b) Φ hΦ sec hsc hsl hun
  let Kf : Subgroup (GL (Fin a) k) :=
    { carrier := {x | ∀ g : GL (Fin a) k, ∀ Z ∈ slice k a (a + b), Φ (g.val * x.val * Z) = Φ (g.val * Z)}
      one_mem' := fun g Z _ => by simp
      mul_mem' := fun {x y} hx hy g Z hZ => by
        rw [Units.val_mul, ← Matrix.mul_assoc, ← Units.val_mul, hy (g * x) Z hZ, Units.val_mul, hx g Z hZ]
      inv_mem' := fun {x} hx g Z hZ => by
        have := hx (g * x⁻¹) Z hZ
        rw [Units.val_mul, Matrix.mul_assoc (g.val), ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.mul_one] at this
        exact this.symm }
  have hKf : IsOpen (Kf : Set (GL (Fin a) k)) := Subgroup.isOpen_of_mem_nhds Kf (g := 1)
    (Filter.mem_of_superset hU fun x hx g Z hZ => hUf x hx g Z hZ)
  let K : Subgroup (GL (Fin a) k) := KO k (Fin a) ⊓ (detChar (Fin a) ν).ker ⊓ Kf
  have hK : IsOpen (K : Set (GL (Fin a) k)) := (isOpen_KO.inter hν.detChar).inter hKf
  have hKO : K ≤ KO k (Fin a) := le_trans inf_le_left inf_le_left
  have htw : ∀ x ∈ K, tw ν (a + b) x = 1 := fun x hx => by
    have h1 : ν (gdet x) = 1 := hx.1.2
    simp [tw, h1, apow_of_valuation_eq_one (valuation_gdet_of_mem_KO hx.1.1)]
  have hright : ∀ (g x : GL (Fin a) k) (Z : Matrix (Fin a) (Fin (a + b)) k), x ∈ K → Z ∈ slice k a (a + b) →
      Φ (g.val * x.val * Z) = Φ (g.val * Z) := fun g x Z hx hZ => hx.2 g Z hZ
  obtain ⟨C, hC, hEC⟩ := GlobalTheory.T.continuous_slice_section_measure k a (a + b) Φ hΦ sec hsc hsl hun
  obtain ⟨R, hRd, hRc⟩ := GlobalTheory.T.compact_covered_by_open_cosets (GL (Fin a) k) K hK C hC
  set T : Set (Matrix (Fin a) (Fin (a + b)) k) := {Y | ∃ x ∈ K, ∃ Z ∈ slice k a (a + b), Y = x.val * Z} with hT
  have hrank : ∀ Y, Φ Y ≠ 0 → Y.rank = a := fun Y hY => by
    by_contra h; exact hY (hΦ.2 Y h)
  refine GlobalTheory.T.coinvariant_of_locally_constant_twist k ν β a b Φ (T.indicator 1) R hΦ.1
    (GlobalTheory.T.isLocallyConstant_indicator_mul_slice k a (a + b) K hK hKO (GlobalTheory.T.full_rank_iff_nonzero_minor k a (a + b)) sec hsc hsl hun) (fun Y => ?_) (fun Y => ?_)
  · by_cases hY : Φ Y = 0
    · simp [hY]
    obtain ⟨g, hg⟩ : ∃ g : GL (Fin a) k, (g⁻¹).val * Y ∈ slice k a (a + b) := ⟨sec Y, hsl Y (hrank Y hY)⟩
    set Z := (g⁻¹).val * Y with hZdef
    have hYZ : Y = g.val * Z := by rw [hZdef, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mul]
    obtain ⟨r, hr, hrg⟩ := hRc g (hEC g Z hg (hYZ ▸ hY))
    rw [Finset.sum_eq_single r]
    · rw [Set.indicator_of_mem, Pi.one_apply, one_mul]
      exact ⟨r⁻¹ * g, hrg, Z, hg, by rw [hYZ, Units.val_mul, Matrix.mul_assoc]⟩
    · intro r' hr' hne
      rw [Set.indicator_of_notMem, zero_mul]
      rintro ⟨x', hx', Z', hZ', he⟩
      have h1 : ((x'⁻¹ * r'⁻¹ * g : GL (Fin a) k)).val * Z ∈ slice k a (a + b) := by
        have : ((x'⁻¹ * r'⁻¹ * g : GL (Fin a) k)).val * Z = Z' := by
          simp only [Units.val_mul, Matrix.mul_assoc]
          rw [← hYZ, he, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
        rw [this]; exact hZ'
      have h2 := hun Z _ hg h1
      have h3 : g = r' * x' := by
        calc g = r' * x' * (x'⁻¹ * r'⁻¹ * g) := by group
          _ = r' * x' := by rw [h2, mul_one]
      exact hne (hRd r hr r' hr' (by
        have : r⁻¹ * r' = (r⁻¹ * g) * x'⁻¹ := by rw [h3]; group
        rw [this]; exact K.mul_mem hrg (K.inv_mem hx'))).symm
    · intro h; exact absurd hr h
  · by_cases hY : Y ∈ T
    · obtain ⟨x, hx, Z, hZ, rfl⟩ := hY
      rw [Set.indicator_of_mem (show x.val * Z ∈ T from ⟨x, hx, Z, hZ, rfl⟩), Pi.one_apply, one_mul]
      have e1 : ∀ r : GL (Fin a) k, Φ (r.val * (x.val * Z)) = Φ (r.val * Z) := fun r => by
        rw [← Matrix.mul_assoc]; exact hright r x Z hx hZ
      simp only [e1]
      have hZr : Z.rank = a := by
        obtain ⟨J, hJ, -⟩ := hZ
        exact (GlobalTheory.T.full_rank_iff_nonzero_minor k a (a + b) Z).2 ⟨J, by simp [minor, hJ]⟩
      have hint := GlobalTheory.T.haar_integral_over_coset_representatives k a K hK hKO (fun g => Φ (g.val * Z) * tw ν (a + b) g)
        (fun g x' hx' => by
          simp only [Units.val_mul, tw_mul, htw x' hx', mul_one]
          rw [hright g x' Z hx' hZ])
        R hRd (fun g hg => hRc g (hEC g Z hZ (left_ne_zero_of_mul hg)))
      rw [GlobalTheory.T.orbital_integral_vanishes_of_fibre k ν β a b Φ hfib Z hZr] at hint
      have hv := vol_ne_zero K hK hKO
      have := (mul_eq_zero.1 hint.symm).resolve_left (by exact_mod_cast hv)
      rw [← this]
      exact Finset.sum_congr rfl fun r _ => mul_comm _ _
    · simp [Set.indicator_of_notMem hY]

end GlobalTheory.RankFibreKer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreZeroMemCoinvariantsStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_zero_mem_coinvariants : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (a b : ℕ) (ν β : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν → GlobalTheory.SmGL.IsSmoothChar β → ∀ Φ ∈ GlobalTheory.RankFibre.fullRankSB (k := k) a (a + b), GlobalTheory.RankFibre.fibre ν β a b Φ = 0 → Φ ∈ GlobalTheory.RankFibre.coinv ν β a (a + b) := by
  first | exact @GlobalTheory.RankFibreKer.fibre_ker | exact GlobalTheory.RankFibreKer.fibre_ker | (intros; apply GlobalTheory.RankFibreKer.fibre_ker <;> assumption)
end
