module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.BoxInterEqEmpty

@[expose] public section

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.NeBotOfIsMaximal
section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.TendstoSumPeriodic
section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.TendstoSumCoset
section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MemIdealLatticeIff
section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.TendstoTsumDivPow
open Module MeasureTheory Filter Topology Bornology Pointwise ZLattice

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.LatSum

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
variable {ι : Type*} [Fintype ι]

theorem map_equivFun (μ : Measure E) [μ.IsAddHaarMeasure] (b : Basis ι ℤ L) :
    μ.map (b.ofZLatticeBasis ℝ L).equivFunL = ENNReal.ofReal (covolume L μ) • volume := by
  classical
  set e := (b.ofZLatticeBasis ℝ L).equivFunL with he
  have h := Measure.addHaarMeasure_unique (μ.map e) (TopologicalSpace.PositiveCompacts.piIcc01 ι)
  rw [addHaarMeasure_eq_volume_pi] at h
  have hF := ZLattice.isAddFundamentalDomain b μ
  have hc : (μ.map e) (TopologicalSpace.PositiveCompacts.piIcc01 ι) = ENNReal.ofReal (covolume L μ) := by
    have h1 : (μ.map e) (Set.univ.pi fun _ : ι => Set.Ico (0 : ℝ) 1) =
        (μ.map e) (TopologicalSpace.PositiveCompacts.piIcc01 ι) := by
      conv_lhs => rw [h]
      rw [Measure.smul_apply, Real.volume_pi_Ico]
      simp
    rw [← h1, Measure.map_apply e.continuous.measurable
      (MeasurableSet.univ_pi fun _ => measurableSet_Ico),
      covolume_eq_measure_fundamentalDomain L μ hF, measureReal_def,
      ENNReal.ofReal_toReal (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne]
    congr 1
    ext x
    simp [ZSpan.mem_fundamentalDomain, Set.mem_pi, he]
  rw [h, hc]

theorem tendsto_tsum_div_pow (μ : Measure E) [μ.IsAddHaarMeasure] {s : Set E} (hs₁ : IsBounded s)
    (hs₂ : MeasurableSet s) (hs₃ : μ (frontier s) = 0) {G : E → ℝ} (hG : Continuous G) :
    Tendsto (fun n : ℕ ↦ (∑' x : ↑(s ∩ (n : ℝ)⁻¹ • (L : Set E)), G x) / (n : ℝ) ^ finrank ℝ E)
      atTop (𝓝 ((∫ x in s, G x ∂μ) / covolume L μ)) := by
  classical

  let b := Module.Free.chooseBasis ℤ L
  let e := (b.ofZLatticeBasis ℝ L).equivFunL
  let eM := e.toHomeomorph.toMeasurableEquiv
  have heM : ∀ x, eM x = e x := fun _ => rfl
  have hcov : 0 < covolume L μ := ZLattice.covolume_pos L μ
  have hne : ENNReal.ofReal (covolume L μ) ≠ 0 := by simpa using hcov
  have hmap : μ.map eM = ENNReal.ofReal (covolume L μ) • volume := map_equivFun L μ b
  have hL : e '' (L : Set E) =
      (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Module.Free.ChooseBasisIndex ℤ L))) :
        Set (Module.Free.ChooseBasisIndex ℤ L → ℝ)) := by
    have hspan := b.ofZLatticeBasis_span ℝ L
    have hstep : e '' (L : Set E) = e '' (Submodule.span ℤ (Set.range (b.ofZLatticeBasis ℝ L)) : Set E) := by
      rw [hspan]
    rw [hstep]
    have hm := Submodule.map_coe (e.toLinearEquiv.toLinearMap.restrictScalars ℤ)
      (Submodule.span ℤ (Set.range (b.ofZLatticeBasis ℝ L)))
    rw [Submodule.map_span] at hm
    rw [show e '' (Submodule.span ℤ (Set.range (b.ofZLatticeBasis ℝ L)) : Set E) =
      ((e.toLinearEquiv.toLinearMap.restrictScalars ℤ) '' (Submodule.span ℤ (Set.range (b.ofZLatticeBasis ℝ L)) : Set E))
      from rfl, ← hm, ← Set.range_comp]
    have hfun : ⇑(e.toLinearEquiv.toLinearMap.restrictScalars ℤ) ∘ ⇑(b.ofZLatticeBasis ℝ L) =
        ⇑(Pi.basisFun ℝ (Module.Free.ChooseBasisIndex ℤ L)) := by
      funext i
      ext j
      by_cases h : j = i
      · subst h
        simp [e]
      · simp [e, h, Ne.symm h]
    rw [hfun]
  have himg : ∀ n : ℕ, e '' (s ∩ (n : ℝ)⁻¹ • (L : Set E)) =
      e '' s ∩ (n : ℝ)⁻¹ • (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Module.Free.ChooseBasisIndex ℤ L))) :
        Set (Module.Free.ChooseBasisIndex ℤ L → ℝ)) := by
    intro n
    rw [Set.image_inter e.injective, ← hL]
    congr 1
    ext y
    constructor
    · rintro ⟨x, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨e a, ⟨a, ha, rfl⟩, (e.map_smul _ a).symm⟩
    · rintro ⟨z, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨_ • a, ⟨a, ha, rfl⟩, e.map_smul _ a⟩
  have hsum : ∀ n : ℕ, (∑' x : ↑(s ∩ (n : ℝ)⁻¹ • (L : Set E)), G x) =
      ∑' y : ↑(e '' s ∩ (n : ℝ)⁻¹ • (Submodule.span ℤ
        (Set.range (Pi.basisFun ℝ (Module.Free.ChooseBasisIndex ℤ L))) :
          Set (Module.Free.ChooseBasisIndex ℤ L → ℝ))), G (e.symm y) := by
    intro n
    rw [← himg n, tsum_image (fun y => G (e.symm y)) e.injective.injOn]
    simp
  have hdim : finrank ℝ E = Fintype.card (Module.Free.ChooseBasisIndex ℤ L) := by
    rw [← ZLattice.rank ℝ L]
    exact Module.finrank_eq_card_chooseBasisIndex ℤ L
  have hpre : eM ⁻¹' (e '' s) = s := Set.preimage_image_eq s e.injective
  have hint : (∫ y in e '' s, G (e.symm y)) = (∫ x in s, G x ∂μ) / covolume L μ := by
    have h1 := setIntegral_map_equiv (μ := μ) eM (fun y => G (e.symm y)) (e '' s)
    rw [hpre, hmap, Measure.restrict_smul, integral_smul_measure, ENNReal.toReal_ofReal hcov.le] at h1
    simp only [heM, ContinuousLinearEquiv.symm_apply_apply] at h1
    rw [← h1, smul_eq_mul, mul_div_cancel_left₀ _ hcov.ne']
  have hfr : volume (frontier (e '' s)) = 0 := by
    have h2 := MeasurableEquiv.map_apply (μ := μ) eM (frontier (e '' s))
    have h3 : eM ⁻¹' frontier (e '' s) = frontier s := by
      have hfe : frontier (e '' s) = e '' frontier s := (e.toHomeomorph.image_frontier s).symm
      rw [hfe]
      exact Set.preimage_image_eq _ e.injective
    rw [h3, hs₃, hmap, Measure.smul_apply, smul_eq_mul] at h2
    exact (mul_eq_zero.1 h2).resolve_left hne
  have hlim := tendsto_tsum_div_pow_atTop_integral (e '' s) (fun y => G (e.symm y))
    (hG.comp e.symm.continuous) (e.lipschitzWith.isBounded_image hs₁)
    (eM.measurableSet_image.2 hs₂) hfr
  rw [hint] at hlim
  refine hlim.congr fun n => ?_
  rw [hsum n, hdim]

end Formalism.HermitianLattices.Ext.L3.LatSum
end
end

open NumberField Module Filter Topology MeasureTheory Pointwise
open scoped Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.BoxSum

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

def sBox (F : Type) [Field F] [NumberField F] : Set (mixedEmbedding.mixedSpace F) :=
  {x | ∀ w, 0 < x.1 w ∧ x.1 w ≤ 1}

def gW (F : Type) [Field F] [NumberField F] (m : ℕ) : mixedEmbedding.mixedSpace F → ℝ :=
  fun x => ∏ w, (x.1 w) ^ (m - 1)

theorem sBox_eq : sBox F = (Set.univ.pi fun _ => Set.Ioc (0 : ℝ) 1) ×ˢ Set.univ := by
  ext x; simp [sBox, Set.mem_pi]

theorem measurableSet_sBox : MeasurableSet (sBox F) := by
  rw [sBox_eq]
  exact (MeasurableSet.univ_pi fun _ => measurableSet_Ioc).prod MeasurableSet.univ

theorem convex_sBox : Convex ℝ (sBox F) := by
  rw [sBox_eq]
  exact (convex_pi fun _ _ => convex_Ioc _ _).prod convex_univ

theorem isBounded_sBox [IsTotallyReal F] : Bornology.IsBounded (sBox F) := by
  refine (Metric.isBounded_closedBall (x := 0) (r := 1)).subset fun x hx => ?_
  rw [mem_closedBall_zero_iff, Prod.norm_def, max_le_iff]
  constructor
  · rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro w
    rw [Real.norm_eq_abs, abs_of_pos (hx w).1]
    exact (hx w).2
  · rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro w
    exact absurd (IsTotallyReal.isReal w.1) (InfinitePlace.not_isReal_iff_isComplex.2 w.2)

theorem continuous_gW (m : ℕ) : Continuous (gW F m) := by
  unfold gW
  fun_prop

theorem integral_gW [IsTotallyReal F] {m : ℕ} (hm : 1 ≤ m) :
    ∫ x in sBox F, gW F m x = ((m : ℝ)⁻¹) ^ Fintype.card {w : InfinitePlace F // w.IsReal} := by
  have hE : IsEmpty {w : InfinitePlace F // w.IsComplex} :=
    ⟨fun w => absurd (IsTotallyReal.isReal w.1) (InfinitePlace.not_isReal_iff_isComplex.2 w.2)⟩
  have h1 : (volume : Measure ({w : InfinitePlace F // w.IsComplex} → ℂ)).real Set.univ = 1 := by
    rw [volume_pi, Measure.pi_of_empty]
    simp
  rw [sBox_eq, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  unfold gW
  rw [integral_fun_fst (f := fun y : {w : InfinitePlace F // w.IsReal} → ℝ => ∏ w, y w ^ (m - 1)),
    h1, one_smul, volume_pi, Measure.restrict_pi_pi,
    integral_fintype_prod_eq_prod (fun _ (y : ℝ) => y ^ (m - 1)), Finset.prod_const,
    Finset.card_univ]
  congr 1
  rw [← intervalIntegral.integral_of_le zero_le_one, integral_pow, Nat.cast_sub hm]
  simp

def fracU {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) : (FractionalIdeal (nonZeroDivisors (𝓞 F)) F)ˣ :=
  Units.mk0 (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (FractionalIdeal.coeIdeal_ne_zero.2 hI)

theorem mem_idealLattice_iff {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) (y : mixedEmbedding.mixedSpace F) :
    y ∈ mixedEmbedding.idealLattice F (fracU hI) ↔ ∃ n ∈ I, mixedEmbedding F (n : F) = y := by
  rw [mixedEmbedding.mem_idealLattice]
  constructor
  · rintro ⟨a, ha, rfl⟩
    have ha' : a ∈ (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := ha
    obtain ⟨n, hn, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 ha'
    exact ⟨n, hn, rfl⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨(n : F), (FractionalIdeal.mem_coeIdeal _).2 ⟨n, hn, rfl⟩, rfl⟩

theorem gW_smul (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (m : ℕ) {T : ℝ} {n : 𝓞 F}
    (hn : n ∈ boxSet K F T) (c : ℝ) :
    gW F m (c • mixedEmbedding F (n : F)) =
      (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1) * c ^ (Formalism.HermitianLatticesTheory.fDeg K * (m - 1)) := by
  unfold gW
  rw [absNorm_eq_prod_of_mem hK hF hn, ← Finset.prod_pow, pow_mul, ← card_real hK hF,
    ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [Prod.smul_fst, Pi.smul_apply, mixedEmbedding.mixedEmbedding_apply_isReal, smul_eq_mul, mul_pow,
    rEmb_apply, mul_comm]

theorem tsum_eq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (m : ℕ) {I : Ideal (𝓞 F)}
    (hI : I ≠ ⊥) {N : ℝ} (hN : 0 < N) :
    ∑' x : ↑(sBox F ∩ N⁻¹ • (mixedEmbedding.idealLattice F (fracU hI) : Set (mixedEmbedding.mixedSpace F))), gW F m x =
      (∑ᶠ n ∈ {n : 𝓞 F | n ∈ boxSet K F N ∧ n ∈ I},
        (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1)) * N⁻¹ ^ (Formalism.HermitianLatticesTheory.fDeg K * (m - 1)) := by
  have hfin : {n : 𝓞 F | n ∈ boxSet K F N ∧ n ∈ I}.Finite :=
    (finite_boxSet hK hF N).subset fun n hn => hn.1
  have hmem : ∀ n : {n : 𝓞 F | n ∈ boxSet K F N ∧ n ∈ I}, N⁻¹ • mixedEmbedding F ((n : 𝓞 F) : F) ∈
      sBox F ∩ N⁻¹ • (mixedEmbedding.idealLattice F (fracU hI) : Set (mixedEmbedding.mixedSpace F)) := by
    rintro ⟨n, hn, hnI⟩
    refine ⟨fun w => ?_, Set.smul_mem_smul_set ((mem_idealLattice_iff hI _).2 ⟨n, hnI, rfl⟩)⟩
    have h1 := (mem_boxSet_iff hK hF).1 hn w
    rw [Prod.smul_fst, Pi.smul_apply, mixedEmbedding.mixedEmbedding_apply_isReal, smul_eq_mul,
      ← rEmb_apply]
    refine ⟨mul_pos (inv_pos.2 hN) h1.1, ?_⟩
    rw [inv_mul_le_iff₀ hN, mul_one]
    exact h1.2
  let ε : {n : 𝓞 F | n ∈ boxSet K F N ∧ n ∈ I} →
      ↑(sBox F ∩ N⁻¹ • (mixedEmbedding.idealLattice F (fracU hI) : Set (mixedEmbedding.mixedSpace F))) := fun n => ⟨_, hmem n⟩
  have hε : Function.Bijective ε := by
    constructor
    · intro n n' h
      have h1 : N⁻¹ • mixedEmbedding F ((n : 𝓞 F) : F) = N⁻¹ • mixedEmbedding F ((n' : 𝓞 F) : F) :=
        congrArg Subtype.val h
      have h2 := smul_right_injective _ (inv_ne_zero hN.ne') h1
      exact Subtype.ext (RingOfIntegers.coe_injective (mixedEmbedding_injective F h2))
    · rintro ⟨x, hx, hxL⟩
      obtain ⟨y, hy, rfl⟩ := hxL
      obtain ⟨n, hnI, rfl⟩ := (mem_idealLattice_iff hI _).1 hy
      refine ⟨⟨n, (mem_boxSet_iff hK hF).2 fun w => ?_, hnI⟩, rfl⟩
      have h1 := hx w
      simp only [] at h1
      rw [Prod.smul_fst, Pi.smul_apply, mixedEmbedding.mixedEmbedding_apply_isReal, smul_eq_mul,
        ← rEmb_apply, inv_mul_le_iff₀ hN, mul_one] at h1
      exact ⟨(mul_pos_iff_of_pos_left (inv_pos.2 hN)).1 h1.1, h1.2⟩
  have : Finite {n : 𝓞 F | n ∈ boxSet K F N ∧ n ∈ I} := hfin
  rw [← (Equiv.ofBijective ε hε).tsum_eq, tsum_eq_finsum (Set.toFinite _), finsum_mem_mul,
    ← finsum_set_coe_eq_finsum_mem]
  refine finsum_congr fun n => ?_
  exact gW_smul hK hF m n.2.1 _

theorem tendsto_sum_ideal (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {m : ℕ} (hm : 1 ≤ m)
    {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) :
    Tendsto (fun j : ℕ => ((j : ℝ) ^ 2) ^ (-((Formalism.HermitianLatticesTheory.fDeg K * m : ℕ) : ℤ)) *
        ∑ᶠ n ∈ {n : 𝓞 F | n ∈ boxSet K F ((j : ℝ) ^ 2) ∧ n ∈ I},
          (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1))
      atTop (𝓝 ((m : ℝ) ^ (-(Formalism.HermitianLatticesTheory.fDeg K : ℤ)) /
        Real.sqrt ((2 * Formalism.HermitianLatticesTheory.vInv K) ^ Formalism.HermitianLatticesTheory.fDeg K) / (Ideal.absNorm I : ℝ))) := by
  have hR : IsTotallyReal F := QuadraticExtensionConjugation.isTotallyReal hK hF
  obtain ⟨-, hfr, hdisc⟩ := discrTower K F hK hF
  have key := LatSum.tendsto_tsum_div_pow (mixedEmbedding.idealLattice F (fracU hI)) volume
    isBounded_sBox measurableSet_sBox (convex_sBox.addHaar_frontier volume) (continuous_gW m)
  rw [integral_gW hm, card_real hK hF, mixedEmbedding.covolume_idealLattice,
    mixedEmbedding.finrank, hfr, IsTotallyReal.nrComplexPlaces_eq_zero, pow_zero, mul_one] at key
  have hsq : Tendsto (fun j : ℕ => j ^ 2) atTop atTop := tendsto_pow_atTop two_ne_zero
  have key2 := key.comp hsq
  have hlim : ((m : ℝ)⁻¹) ^ Formalism.HermitianLatticesTheory.fDeg K /
      (((FractionalIdeal.absNorm ((fracU hI : (FractionalIdeal (nonZeroDivisors (𝓞 F)) F)ˣ) :
        FractionalIdeal (nonZeroDivisors (𝓞 F)) F) : ℚ) : ℝ) * Real.sqrt |(discr F : ℝ)|) =
      (m : ℝ) ^ (-(Formalism.HermitianLatticesTheory.fDeg K : ℤ)) /
        Real.sqrt ((2 * Formalism.HermitianLatticesTheory.vInv K) ^ Formalism.HermitianLatticesTheory.fDeg K) / (Ideal.absNorm I : ℝ) := by
    have h1 : FractionalIdeal.absNorm ((fracU hI : (FractionalIdeal (nonZeroDivisors (𝓞 F)) F)ˣ) :
        FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = (Ideal.absNorm I : ℚ) :=
      FractionalIdeal.coeIdeal_absNorm I
    have h2 : |(discr F : ℝ)| = (2 * Formalism.HermitianLatticesTheory.vInv K) ^ Formalism.HermitianLatticesTheory.fDeg K := by
      rw [hdisc, abs_of_nonneg (pow_nonneg (mul_nonneg zero_le_two (vInv_pos K).le) _)]
    rw [h1, h2, zpow_neg, zpow_natCast, inv_pow, div_div, Rat.cast_natCast, mul_comm]
  rw [hlim] at key2
  refine Tendsto.congr' ?_ key2
  filter_upwards [eventually_gt_atTop 0] with j hj
  have hj' : (0 : ℝ) < (j : ℝ) ^ 2 := by positivity
  have hcast : ((j ^ 2 : ℕ) : ℝ) = (j : ℝ) ^ 2 := by push_cast; rfl
  have h3 := tsum_eq hK hF m hI (N := ((j ^ 2 : ℕ) : ℝ)) (by rw [hcast]; exact hj')
  rw [Function.comp_apply, h3, hcast, zpow_neg, zpow_natCast, inv_pow, div_eq_mul_inv, mul_assoc, ← mul_inv, ← pow_add, mul_comm]
  congr 3
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  ring

end Formalism.HermitianLattices.Ext.L3.BoxSum
end
end

open NumberField Module Filter Topology
open scoped Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.BoxSum

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem finite_box_inter (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (T : ℝ) (A : Set (𝓞 F)) :
    {n : 𝓞 F | n ∈ boxSet K F T ∧ n ∈ A}.Finite := (finite_boxSet hK hF T).subset fun _ hn => hn.1

theorem sum_le_sum_shift (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (m : ℕ) {A B : Set (𝓞 F)}
    {T T' : ℝ} (y : 𝓞 F) (hy0 : ∀ w, 0 ≤ rEmb w y) (hyT : ∀ w, rEmb w y + T ≤ T')
    (hAB : ∀ n ∈ A, n + y ∈ B) :
    ∑ᶠ n ∈ {n : 𝓞 F | n ∈ boxSet K F T ∧ n ∈ A}, (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1) ≤
      ∑ᶠ n ∈ {n : 𝓞 F | n ∈ boxSet K F T' ∧ n ∈ B},
        (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1) := by
  classical
  have hA := finite_box_inter hK hF T A
  have hB := finite_box_inter hK hF T' B
  rw [finsum_mem_eq_finite_toFinset_sum _ hA, finsum_mem_eq_finite_toFinset_sum _ hB]
  have key : ∀ n ∈ hA.toFinset, n + y ∈ hB.toFinset ∧
      (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1) ≤
        (Ideal.absNorm (Ideal.span {n + y}) : ℝ) ^ (m - 1) := by
    intro n hn
    rw [Set.Finite.mem_toFinset] at hn
    obtain ⟨hnb, hnA⟩ := hn
    have hb : ∀ w, 0 < rEmb w n ∧ rEmb w n ≤ T := (mem_boxSet_iff hK hF).1 hnb
    have hny : n + y ∈ boxSet K F T' := by
      rw [mem_boxSet_iff hK hF]
      intro w
      rw [map_add (f := _)]
      constructor
      · linarith [(hb w).1, hy0 w]
      · linarith [(hb w).2, hyT w]
    refine ⟨by rw [Set.Finite.mem_toFinset]; exact ⟨hny, hAB n hnA⟩, ?_⟩
    have hle : (Ideal.absNorm (Ideal.span {n}) : ℝ) ≤ (Ideal.absNorm (Ideal.span {n + y}) : ℝ) := by
      rw [absNorm_eq_prod_of_mem hK hF hnb, absNorm_eq_prod_of_mem hK hF hny]
      apply Finset.prod_le_prod₀
      · intro w _
        exact (hb w).1.le
      · intro w _
        rw [map_add (f := _)]
        linarith [hy0 w]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hle _
  calc ∑ n ∈ hA.toFinset, (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1)
      ≤ ∑ n ∈ hA.toFinset, (Ideal.absNorm (Ideal.span {n + y}) : ℝ) ^ (m - 1) :=
        Finset.sum_le_sum fun n hn => (key n hn).2
    _ = ∑ n ∈ hA.toFinset.image (· + y), (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1) := by
        rw [Finset.sum_image (fun a _ b _ h => add_right_cancel h)]
    _ ≤ ∑ n ∈ hB.toFinset, (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro x hx
          obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hx
          exact (key n hn).1
        · intro _ _ _
          positivity

theorem exists_shifts {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) (x₀ : 𝓞 F) :
    ∃ (y y' : 𝓞 F) (R : ℝ), (∀ w, 0 ≤ rEmb w y ∧ rEmb w y ≤ R) ∧ (∀ w, 0 ≤ rEmb w y' ∧ rEmb w y' ≤ R) ∧
      (∀ n, n - x₀ ∈ I → n + y ∈ I) ∧ ∀ n, n ∈ I → n + y' - x₀ ∈ I := by
  classical
  have hN0 : Ideal.absNorm I ≠ 0 := fun h => hI (Ideal.absNorm_eq_zero_iff.1 h)
  have hNmem : ((Ideal.absNorm I : ℕ) : 𝓞 F) ∈ I := Ideal.absNorm_mem I
  obtain ⟨C, hCw⟩ : ∃ C : ℝ, ∀ w : {w : InfinitePlace F // w.IsReal}, |rEmb w x₀| ≤ C :=
    ⟨∑ w : {w : InfinitePlace F // w.IsReal}, |rEmb w x₀|, fun w =>
      Finset.single_le_sum (f := fun w => |rEmb w x₀|) (fun _ _ => abs_nonneg _) (Finset.mem_univ w)⟩
  obtain ⟨c, hc⟩ := exists_nat_ge C
  have hN1 : (1 : ℝ) ≤ (Ideal.absNorm I : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 hN0
  have hcN : C ≤ ((c * Ideal.absNorm I : ℕ) : ℝ) := by
    push_cast
    have h0 : (0 : ℝ) ≤ c := Nat.cast_nonneg _
    nlinarith
  have hmem : ((c * Ideal.absNorm I : ℕ) : 𝓞 F) ∈ I := by
    rw [Nat.cast_mul]
    exact I.mul_mem_left _ hNmem
  refine ⟨((c * Ideal.absNorm I : ℕ) : 𝓞 F) - x₀, ((c * Ideal.absNorm I : ℕ) : 𝓞 F) + x₀,
    ((c * Ideal.absNorm I : ℕ) : ℝ) + C, ?_, ?_, ?_, ?_⟩
  · intro w
    rw [map_sub, map_natCast]
    have h := abs_le.1 (hCw w)
    constructor <;> linarith [h.1, h.2]
  · intro w
    rw [map_add (f := _), map_natCast]
    have h := abs_le.1 (hCw w)
    constructor <;> linarith [h.1, h.2]
  · intro n hn
    have e : n + (((c * Ideal.absNorm I : ℕ) : 𝓞 F) - x₀) =
        (n - x₀) + ((c * Ideal.absNorm I : ℕ) : 𝓞 F) := by ring
    rw [e]
    exact I.add_mem hn hmem
  · intro n hn
    have e : n + (((c * Ideal.absNorm I : ℕ) : 𝓞 F) + x₀) - x₀ =
        n + ((c * Ideal.absNorm I : ℕ) : 𝓞 F) := by ring
    rw [e]
    exact I.add_mem hn hmem

theorem tendsto_ratio (e : ℕ) :
    Tendsto (fun j : ℕ => (((j : ℝ) ^ 2) ^ e) / ((((j + 1 : ℕ) : ℝ) ^ 2) ^ e)) atTop (𝓝 1) := by
  have h1 : Tendsto (fun j : ℕ => (j : ℝ) / ((j + 1 : ℕ) : ℝ)) atTop (𝓝 1) := by
    refine (tendsto_natCast_div_add_atTop (1 : ℝ)).congr fun j => ?_
    push_cast
    rfl
  have h2 := (h1.pow 2).pow e
  simp only [one_pow] at h2
  exact h2.congr fun j => by rw [div_pow, div_pow]

private theorem tendsto_scaled_of_interleaved_tendsto (D : ℕ) {u v : ℕ → ℝ} {L : ℝ}
    (hv : Tendsto (fun j : ℕ => ((j : ℝ) ^ 2) ^ (-(D : ℤ)) * v j) atTop (𝓝 L))
    (hup : ∀ᶠ j in atTop, u j ≤ v (j + 1))
    (hlo : ∀ᶠ j in atTop, v j ≤ u (j + 1)) :
    Tendsto (fun j : ℕ => ((j : ℝ) ^ 2) ^ (-(D : ℤ)) * u j) atTop (𝓝 L) := by
  have hg : ∀ j : ℕ, ((j : ℝ) ^ 2) ^ (-(D : ℤ)) = (((j : ℝ) ^ 2) ^ D)⁻¹ := fun j => by
    rw [zpow_neg, zpow_natCast]
  simp only [hg] at hv ⊢
  have hs := tendsto_ratio D
  have hs1 : Tendsto (fun j : ℕ => ((((j + 1 : ℕ) : ℝ) ^ 2) ^ D) /
      ((((j + 1 + 1 : ℕ) : ℝ) ^ 2) ^ D)) atTop (𝓝 1) :=
    hs.comp (tendsto_add_atTop_nat 1)
  have ht : Tendsto (fun j : ℕ => ((((j + 1 + 1 : ℕ) : ℝ) ^ 2) ^ D) /
      ((((j + 1 : ℕ) : ℝ) ^ 2) ^ D)) atTop (𝓝 1) := by
    have h := hs1.inv₀ one_ne_zero
    simpa only [inv_div, inv_one] using h
  have hv2 : Tendsto (fun j : ℕ => ((((j + 1 + 1 : ℕ) : ℝ) ^ 2) ^ D)⁻¹ * v (j + 1 + 1))
      atTop (𝓝 L) :=
    (hv.comp (tendsto_add_atTop_nat 1)).comp (tendsto_add_atTop_nat 1)
  have lowT : Tendsto (fun j : ℕ => (((j : ℝ) ^ 2) ^ D) / ((((j + 1 : ℕ) : ℝ) ^ 2) ^ D) *
      ((((j : ℝ) ^ 2) ^ D)⁻¹ * v j)) atTop (𝓝 L) := by
    simpa only [one_mul] using hs.mul hv
  have upT : Tendsto (fun j : ℕ => ((((j + 1 + 1 : ℕ) : ℝ) ^ 2) ^ D) /
      ((((j + 1 : ℕ) : ℝ) ^ 2) ^ D) *
      (((((j + 1 + 1 : ℕ) : ℝ) ^ 2) ^ D)⁻¹ * v (j + 1 + 1))) atTop (𝓝 L) := by
    simpa only [one_mul] using ht.mul hv2
  have hup1 : ∀ᶠ j in atTop, u (j + 1) ≤ v (j + 1 + 1) := (tendsto_add_atTop_nat 1).eventually hup
  rw [← tendsto_add_atTop_iff_nat 1]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' lowT upT ?_ ?_
  · filter_upwards [hlo, eventually_ge_atTop 1] with j hj hj1
    have hj0 : ((j : ℝ) ^ 2) ^ D ≠ 0 :=
      pow_ne_zero _ (pow_ne_zero _ (Nat.cast_ne_zero.2 (by omega)))
    have hpos : 0 ≤ ((((j + 1 : ℕ) : ℝ) ^ 2) ^ D)⁻¹ := by positivity
    calc (((j : ℝ) ^ 2) ^ D) / ((((j + 1 : ℕ) : ℝ) ^ 2) ^ D) * ((((j : ℝ) ^ 2) ^ D)⁻¹ * v j)
        = ((((j + 1 : ℕ) : ℝ) ^ 2) ^ D)⁻¹ * v j := by
          rw [div_mul_eq_mul_div, ← mul_assoc, mul_inv_cancel₀ hj0, one_mul, div_eq_inv_mul]
      _ ≤ ((((j + 1 : ℕ) : ℝ) ^ 2) ^ D)⁻¹ * u (j + 1) := mul_le_mul_of_nonneg_left hj hpos
  · filter_upwards [hup1] with j hj
    have hpos : 0 ≤ ((((j + 1 : ℕ) : ℝ) ^ 2) ^ D)⁻¹ := by positivity
    have h0 : ((((j + 1 + 1 : ℕ) : ℝ) ^ 2) ^ D) ≠ 0 :=
      pow_ne_zero _ (pow_ne_zero _ (Nat.cast_ne_zero.2 (Nat.succ_ne_zero _)))
    calc ((((j + 1 : ℕ) : ℝ) ^ 2) ^ D)⁻¹ * u (j + 1)
        ≤ ((((j + 1 : ℕ) : ℝ) ^ 2) ^ D)⁻¹ * v (j + 1 + 1) := mul_le_mul_of_nonneg_left hj hpos
      _ = ((((j + 1 + 1 : ℕ) : ℝ) ^ 2) ^ D) / ((((j + 1 : ℕ) : ℝ) ^ 2) ^ D) *
          (((((j + 1 + 1 : ℕ) : ℝ) ^ 2) ^ D)⁻¹ * v (j + 1 + 1)) := by
          rw [div_mul_eq_mul_div, ← mul_assoc, mul_inv_cancel₀ h0, one_mul, div_eq_inv_mul]

theorem tendsto_sum_coset (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {m : ℕ} (hm : 1 ≤ m)
    {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) (x₀ : 𝓞 F) :
    Tendsto (fun j : ℕ => ((j : ℝ) ^ 2) ^ (-((Formalism.HermitianLatticesTheory.fDeg K * m : ℕ) : ℤ)) *
        ∑ᶠ n ∈ {n : 𝓞 F | n ∈ boxSet K F ((j : ℝ) ^ 2) ∧ n - x₀ ∈ I},
          (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1))
      atTop (𝓝 ((m : ℝ) ^ (-(Formalism.HermitianLatticesTheory.fDeg K : ℤ)) /
        Real.sqrt ((2 * Formalism.HermitianLatticesTheory.vInv K) ^ Formalism.HermitianLatticesTheory.fDeg K) / (Ideal.absNorm I : ℝ))) := by
  obtain ⟨y, y', R, hy, hy', hyI, hy'I⟩ := exists_shifts hI x₀
  obtain ⟨j0, hj0⟩ := exists_nat_ge R
  refine tendsto_scaled_of_interleaved_tendsto _ (tendsto_sum_ideal hK hF hm hI) ?_ ?_
  · filter_upwards [eventually_ge_atTop j0] with j hj
    have hRj : R ≤ (j : ℝ) := le_trans hj0 (by exact_mod_cast hj)
    refine sum_le_sum_shift hK hF m (A := {n | n - x₀ ∈ I}) (B := (I : Set (𝓞 F)))
      (T := (j : ℝ) ^ 2) (T' := ((j + 1 : ℕ) : ℝ) ^ 2) y (fun w => (hy w).1) ?_ ?_
    · intro w
      have h1 := (hy w).2
      have h2 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      push_cast
      nlinarith
    · intro n hn
      exact hyI n hn
  · filter_upwards [eventually_ge_atTop j0] with j hj
    have hRj : R ≤ (j : ℝ) := le_trans hj0 (by exact_mod_cast hj)
    refine sum_le_sum_shift hK hF m (A := (I : Set (𝓞 F))) (B := {n | n - x₀ ∈ I})
      (T := (j : ℝ) ^ 2) (T' := ((j + 1 : ℕ) : ℝ) ^ 2) y' (fun w => (hy' w).1) ?_ ?_
    · intro w
      have h1 := (hy' w).2
      have h2 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      push_cast
      nlinarith
    · intro n hn
      exact hy'I n hn

end Formalism.HermitianLattices.Ext.L3.BoxSum
end
end

open NumberField Module Filter Topology
open scoped Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.BoxSum

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem finite_quot {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) : Finite (𝓞 F ⧸ I) :=
  Ideal.finiteQuotientOfFreeOfNeBot I hI

theorem exists_crt {b 𝔞 : Ideal (𝓞 F)} (hco : b ⊔ 𝔞 = ⊤) (x₀ : 𝓞 F) (c : 𝓞 F ⧸ 𝔞) :
    ∃ x : 𝓞 F, x - x₀ ∈ b ∧ Ideal.Quotient.mk 𝔞 x = c := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective c
  have h1 : (1 : 𝓞 F) ∈ b ⊔ 𝔞 := by rw [hco]; exact Submodule.mem_top
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp h1
  refine ⟨x₀ * v + y * u, ?_, ?_⟩
  · have e : x₀ * v + y * u - x₀ = (y - x₀) * u := by linear_combination x₀ * huv
    rw [e]
    exact b.mul_mem_left _ hu
  · rw [Ideal.Quotient.eq]
    have e : x₀ * v + y * u - y = (x₀ - y) * v := by linear_combination y * huv
    rw [e]
    exact 𝔞.mul_mem_left _ hv

theorem sum_split (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (T : ℝ) {b 𝔞 : Ideal (𝓞 F)}
    [Fintype (𝓞 F ⧸ 𝔞)] (hco : b ⊔ 𝔞 = ⊤) (x₀ : 𝓞 F) (g : 𝓞 F → ℝ) (φ : 𝓞 F ⧸ 𝔞 → ℝ)
    (x : 𝓞 F ⧸ 𝔞 → 𝓞 F) (hx : ∀ c, x c - x₀ ∈ b ∧ Ideal.Quotient.mk 𝔞 (x c) = c) :
    ∑ᶠ n ∈ {n : 𝓞 F | n ∈ boxSet K F T ∧ n - x₀ ∈ b}, g n * φ (Ideal.Quotient.mk 𝔞 n) =
      ∑ c, φ c * ∑ᶠ n ∈ {n : 𝓞 F | n ∈ boxSet K F T ∧ n - x c ∈ b * 𝔞}, g n := by
  set S := {n : 𝓞 F | n ∈ boxSet K F T ∧ n - x₀ ∈ b} with hSdef
  have hS : S.Finite := finite_box_inter hK hF T {n | n - x₀ ∈ b}
  have hT : ∀ c, {n : 𝓞 F | n ∈ boxSet K F T ∧ n - x c ∈ b * 𝔞} = {n | n ∈ S ∧ Ideal.Quotient.mk 𝔞 n = c} := by
    intro c
    ext n
    simp only [Set.mem_setOf_eq, hSdef]
    rw [Ideal.mul_eq_inf_of_coprime hco, Ideal.mem_inf]
    constructor
    · rintro ⟨hn, h1, h2⟩
      refine ⟨⟨hn, ?_⟩, ?_⟩
      · have := b.add_mem h1 (hx c).1
        rwa [sub_add_sub_cancel] at this
      · rw [← (hx c).2]
        exact Ideal.Quotient.eq.mpr h2
    · rintro ⟨⟨hn, h1⟩, h2⟩
      refine ⟨hn, ?_, ?_⟩
      · have := b.sub_mem h1 (hx c).1
        rwa [sub_sub_sub_cancel_right] at this
      · rw [← (hx c).2] at h2
        exact Ideal.Quotient.eq.mp h2
  have hSc : ∀ c, ({n | n ∈ S ∧ Ideal.Quotient.mk 𝔞 n = c} : Set (𝓞 F)).Finite :=
    fun c => hS.subset fun n hn => hn.1
  rw [finsum_mem_eq_finite_toFinset_sum _ hS, ← Finset.sum_fiberwise hS.toFinset (Ideal.Quotient.mk 𝔞)]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [hT c, finsum_mem_eq_finite_toFinset_sum _ (hSc c), Finset.mul_sum]
  have e : (hSc c).toFinset = hS.toFinset.filter (fun n => Ideal.Quotient.mk 𝔞 n = c) := by
    ext n
    simp
  rw [e]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [(Finset.mem_filter.mp hn).2, mul_comm]

theorem tendsto_sum_periodic (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {m : ℕ} (hm : 1 ≤ m)
    (k : ℕ) (φ : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, (𝓞 F ⧸ 𝔭.1 ^ k) → ℝ)
    (S : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) :
    ∀ (b : Ideal (𝓞 F)), b ≠ ⊥ → (∀ 𝔭 ∈ S, b ⊔ 𝔭.1 = ⊤) → ∀ x₀ : 𝓞 F,
    Tendsto (fun j : ℕ => ((j : ℝ) ^ 2) ^ (-((Formalism.HermitianLatticesTheory.fDeg K * m : ℕ) : ℤ)) *
        ∑ᶠ n ∈ {n : 𝓞 F | n ∈ boxSet K F ((j : ℝ) ^ 2) ∧ n - x₀ ∈ b},
          (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1) *
            ∏ 𝔭 ∈ S, φ 𝔭 (Ideal.Quotient.mk (𝔭.1 ^ k) n))
      atTop (𝓝 ((m : ℝ) ^ (-(Formalism.HermitianLatticesTheory.fDeg K : ℤ)) /
        Real.sqrt ((2 * Formalism.HermitianLatticesTheory.vInv K) ^ Formalism.HermitianLatticesTheory.fDeg K) / (Ideal.absNorm b : ℝ) *
          ∏ 𝔭 ∈ S, ((Ideal.absNorm 𝔭.1 : ℝ) ^ (-(k : ℤ)) * ∑ᶠ c, φ 𝔭 c))) := by
  induction S using Finset.induction_on with
  | empty =>
    intro b hb _ x₀
    have := tendsto_sum_coset hK hF hm hb x₀
    simp only [Finset.prod_empty, mul_one]
    exact this
  | insert 𝔮 S' h𝔮S ih =>
    intro b hb hcop x₀
    have h𝔮0 : 𝔮.1 ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField 𝔮.2 (RingOfIntegers.not_isField F)
    have h𝔞0 : 𝔮.1 ^ k ≠ ⊥ := by
      have h0 : 𝔮.1 ≠ 0 := by simpa only [Ideal.zero_eq_bot] using h𝔮0
      simpa only [Ideal.zero_eq_bot] using pow_ne_zero k h0
    haveI : Fintype (𝓞 F ⧸ 𝔮.1 ^ k) := @Fintype.ofFinite _ (finite_quot h𝔞0)
    have hco : b ⊔ 𝔮.1 ^ k = ⊤ := by
      have h1 : IsCoprime b 𝔮.1 := Ideal.isCoprime_iff_sup_eq.mpr (hcop 𝔮 (Finset.mem_insert_self _ _))
      exact Ideal.isCoprime_iff_sup_eq.mp h1.pow_right
    choose x hx using fun c => exists_crt hco x₀ c
    have hb' : b * 𝔮.1 ^ k ≠ ⊥ := by
      have h0 : b ≠ 0 := by simpa only [Ideal.zero_eq_bot] using hb
      have h1 : 𝔮.1 ^ k ≠ 0 := by simpa only [Ideal.zero_eq_bot] using h𝔞0
      simpa only [Ideal.zero_eq_bot] using mul_ne_zero h0 h1
    have hcop' : ∀ 𝔭 ∈ S', b * 𝔮.1 ^ k ⊔ 𝔭.1 = ⊤ := by
      intro 𝔭 h𝔭
      have h1 : IsCoprime b 𝔭.1 := Ideal.isCoprime_iff_sup_eq.mpr (hcop 𝔭 (Finset.mem_insert_of_mem h𝔭))
      have hne : 𝔮.1 ≠ 𝔭.1 := fun e => h𝔮S ((Subtype.ext e : 𝔮 = 𝔭) ▸ h𝔭)
      have h2 : IsCoprime 𝔮.1 𝔭.1 := Ideal.isCoprime_iff_sup_eq.mpr (Ideal.IsMaximal.coprime_of_ne 𝔮.2 𝔭.2 hne)
      have h3 : IsCoprime (𝔮.1 ^ k) 𝔭.1 := h2.pow_left
      exact Ideal.isCoprime_iff_sup_eq.mp (h1.mul_left h3)
    have hlim := fun c => ih (b * 𝔮.1 ^ k) hb' hcop' (x c)

    have hsplit : ∀ j : ℕ, ∑ᶠ n ∈ {n : 𝓞 F | n ∈ boxSet K F ((j : ℝ) ^ 2) ∧ n - x₀ ∈ b},
        (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1) * ∏ 𝔭 ∈ insert 𝔮 S', φ 𝔭 (Ideal.Quotient.mk (𝔭.1 ^ k) n) =
        ∑ c, φ 𝔮 c * ∑ᶠ n ∈ {n : 𝓞 F | n ∈ boxSet K F ((j : ℝ) ^ 2) ∧ n - x c ∈ b * 𝔮.1 ^ k},
          (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1) * ∏ 𝔭 ∈ S', φ 𝔭 (Ideal.Quotient.mk (𝔭.1 ^ k) n) := by
      intro j
      rw [← sum_split hK hF _ hco x₀ (fun n => (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1) *
        ∏ 𝔭 ∈ S', φ 𝔭 (Ideal.Quotient.mk (𝔭.1 ^ k) n)) (φ 𝔮) x hx]
      refine finsum_mem_congr rfl fun n _ => ?_
      rw [Finset.prod_insert h𝔮S]
      ring
    have hT := tendsto_finsetSum (Finset.univ : Finset (𝓞 F ⧸ 𝔮.1 ^ k)) fun c _ => (hlim c).const_mul (φ 𝔮 c)
    convert (preTransparency := .reducible) hT using 1
    · funext j
      rw [hsplit j, Finset.mul_sum]
      exact Finset.sum_congr rfl fun c _ => by ring
    · congr 1
      rw [Finset.prod_insert h𝔮S, finsum_eq_sum_of_fintype]
      simp only [map_mul, map_pow, Nat.cast_mul, Nat.cast_pow, zpow_neg, zpow_natCast, Finset.mul_sum,
        Finset.sum_mul]
      refine Finset.sum_congr rfl fun c _ => ?_
      ring

end Formalism.HermitianLattices.Ext.L3.BoxSum
end
end

open NumberField Module Filter Topology
open scoped Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.BoxSum

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem vF_lt_of_notMem {𝔭 : Ideal (𝓞 F)} {n : 𝓞 F} {e : ℕ} (h : n ∉ 𝔭 ^ e) : vF 𝔭 n < e := by
  unfold vF
  have hne : ({e' : ℕ | n ∈ 𝔭 ^ e'} : Set ℕ).Nonempty := ⟨0, by simp⟩
  have hlt : ∀ k ∈ ({e' : ℕ | n ∈ 𝔭 ^ e'} : Set ℕ), k < e := by
    intro k hk
    by_contra hke
    push Not at hke
    exact h (Ideal.pow_le_pow_right hke hk)
  have hbdd : BddAbove ({e' : ℕ | n ∈ 𝔭 ^ e'} : Set ℕ) := ⟨e, fun k hk => (hlt k hk).le⟩
  exact hlt _ (Nat.sSup_mem hne hbdd)

theorem ne_bot_of_isMaximal {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : 𝔭 ≠ ⊥ := by
  haveI := h𝔭
  exact Ideal.IsMaximal.ne_bot_of_isIntegral_int 𝔭

theorem one_lt_absNorm {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : (1 : ℝ) < (Ideal.absNorm 𝔭 : ℝ) := by
  have h1 : Ideal.absNorm 𝔭 ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact h𝔭.ne_top
  have h0 : Ideal.absNorm 𝔭 ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact ne_bot_of_isMaximal h𝔭
  have h2 : 1 < Ideal.absNorm 𝔭 := by omega
  exact_mod_cast h2

end Formalism.HermitianLattices.Ext.L3.BoxSum
end
end

open NumberField Module Filter Topology
open scoped Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.BoxSum

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

private theorem abs_prod_sub_prod_le_of_bounded_differences {ι : Type*} (S : Finset ι) (x y C d : ι → ℝ)
    (hx : ∀ i ∈ S, |x i| ≤ C i) (hy : ∀ i ∈ S, |y i| ≤ C i)
    (hd : ∀ i ∈ S, x i ≠ y i → 1 ≤ d i) (hd0 : ∀ i ∈ S, 0 ≤ d i) :
    |∏ i ∈ S, x i - ∏ i ∈ S, y i| ≤ 2 * (∏ i ∈ S, C i) * ∑ i ∈ S, d i := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert p s hp ih =>
    rw [Finset.prod_insert hp, Finset.prod_insert hp, Finset.prod_insert hp, Finset.sum_insert hp]
    have ih' := ih (fun i hi => hx i (Finset.mem_insert_of_mem hi)) (fun i hi => hy i (Finset.mem_insert_of_mem hi))
      (fun i hi => hd i (Finset.mem_insert_of_mem hi)) (fun i hi => hd0 i (Finset.mem_insert_of_mem hi))
    have hxp := hx p (Finset.mem_insert_self p s)
    have hyp := hy p (Finset.mem_insert_self p s)
    have hdp := hd0 p (Finset.mem_insert_self p s)
    have hCp : 0 ≤ C p := le_trans (abs_nonneg _) hxp
    have hys : |∏ i ∈ s, y i| ≤ ∏ i ∈ s, C i := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) fun i hi => hy i (Finset.mem_insert_of_mem hi)
    have hdiff : |x p - y p| ≤ 2 * C p * d p := by
      by_cases h : x p = y p
      · rw [h, sub_self, abs_zero]
        exact mul_nonneg (by linarith) hdp
      · have h1 := hd p (Finset.mem_insert_self p s) h
        have h2 : |x p - y p| ≤ 2 * C p := by
          rw [abs_le] at hxp hyp ⊢
          constructor <;> linarith
        calc |x p - y p| ≤ 2 * C p := h2
          _ ≤ 2 * C p * d p := le_mul_of_one_le_right (by linarith) h1
    calc |x p * ∏ i ∈ s, x i - y p * ∏ i ∈ s, y i|
        = |x p * (∏ i ∈ s, x i - ∏ i ∈ s, y i) + (x p - y p) * ∏ i ∈ s, y i| := by
          congr 1
          ring
      _ ≤ |x p * (∏ i ∈ s, x i - ∏ i ∈ s, y i)| + |(x p - y p) * ∏ i ∈ s, y i| := abs_add_le _ _
      _ = |x p| * |∏ i ∈ s, x i - ∏ i ∈ s, y i| + |x p - y p| * |∏ i ∈ s, y i| := by
          rw [abs_mul, abs_mul]
      _ ≤ C p * (2 * (∏ i ∈ s, C i) * ∑ i ∈ s, d i) + (2 * C p * d p) * ∏ i ∈ s, C i :=
          add_le_add (mul_le_mul hxp ih' (abs_nonneg _) hCp)
            (mul_le_mul hdiff hys (abs_nonneg _) (mul_nonneg (by linarith) hdp))
      _ = 2 * (C p * ∏ i ∈ s, C i) * (d p + ∑ i ∈ s, d i) := by ring

theorem abs_prod_sub_le (S : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal})
    (a : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} → 𝓞 F → ℝ) (C : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} → ℝ)
    (c : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} → ℕ) (hbd : ∀ 𝔭 ∈ S, ∀ n, |a 𝔭 n| ≤ C 𝔭)
    (hcg : ∀ 𝔭 ∈ S, ∀ (n n' : 𝓞 F) (k : ℕ), n ≠ 0 → vF 𝔭.1 n + c 𝔭 ≤ k → n - n' ∈ 𝔭.1 ^ k →
      a 𝔭 n = a 𝔭 n') (k : ℕ) {n : 𝓞 F} (hn : n ≠ 0) :
    |∏ 𝔭 ∈ S, a 𝔭 n - ∏ 𝔭 ∈ S, a 𝔭 (Quotient.out (Ideal.Quotient.mk (𝔭.1 ^ k) n))| ≤
      2 * (∏ 𝔭 ∈ S, C 𝔭) * ∑ 𝔭 ∈ S, (if n ∈ 𝔭.1 ^ (k + 1 - c 𝔭) then 1 else 0) := by
  refine abs_prod_sub_prod_le_of_bounded_differences S _ _ C _ (fun 𝔭 h𝔭 => hbd 𝔭 h𝔭 n) (fun 𝔭 h𝔭 => hbd 𝔭 h𝔭 _) (fun 𝔭 h𝔭 hne => ?_)
    (fun 𝔭 _ => by split_ifs <;> norm_num)
  by_contra hlt
  have hni : n ∉ 𝔭.1 ^ (k + 1 - c 𝔭) := by
    intro hm
    rw [ite_eq_left hm] at hlt
    exact hlt le_rfl
  have hv := BoxSum.vF_lt_of_notMem hni
  have hk : vF 𝔭.1 n + c 𝔭 ≤ k := by omega
  apply hne
  refine hcg 𝔭 h𝔭 n _ k hn hk ?_
  rw [← Ideal.Quotient.eq, Ideal.Quotient.mk_out]

theorem tendsto_err (S : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) (A B : ℝ)
    (c : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} → ℕ) :
    Tendsto (fun k : ℕ => A * ∑ 𝔭 ∈ S, B / (Ideal.absNorm 𝔭.1 : ℝ) ^ (k + 1 - c 𝔭)) atTop (𝓝 0) := by
  have h0 : Tendsto (fun k : ℕ => ∑ 𝔭 ∈ S, B / (Ideal.absNorm 𝔭.1 : ℝ) ^ (k + 1 - c 𝔭)) atTop
      (𝓝 (∑ 𝔭 ∈ S, (0 : ℝ))) := by
    refine tendsto_finsetSum _ fun 𝔭 _ => ?_
    have hne : 𝔭.1 ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField 𝔭.2 (NumberField.RingOfIntegers.not_isField F)
    have h1 : Ideal.absNorm 𝔭.1 ≠ 1 := fun h => 𝔭.2.ne_top (Ideal.absNorm_eq_one_iff.1 h)
    have h2 : Ideal.absNorm 𝔭.1 ≠ 0 := fun h => hne (Ideal.absNorm_eq_zero_iff.1 h)
    have hgt : (1 : ℝ) < Ideal.absNorm 𝔭.1 := by
      have : 1 < Ideal.absNorm 𝔭.1 := by omega
      exact_mod_cast this
    refine tendsto_const_nhds.div_atTop ?_
    exact (tendsto_pow_atTop_atTop_of_one_lt hgt).comp
      ((tendsto_sub_atTop_nat (c 𝔭)).comp (tendsto_add_atTop_nat 1))
  simpa using h0.const_mul A

private theorem finsum_boxSet_inf_eq_sum_ite_mem (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (T : ℝ) (b I : Ideal (𝓞 F))
    (g : 𝓞 F → ℝ) (hb : {n : 𝓞 F | n ∈ boxSet K F T ∧ n ∈ b}.Finite) :
    ∑ᶠ n ∈ {n : 𝓞 F | n ∈ boxSet K F T ∧ n ∈ b ⊓ I}, g n =
      ∑ n ∈ hb.toFinset, if n ∈ I then g n else 0 := by
  classical
  have hfin : {n : 𝓞 F | n ∈ boxSet K F T ∧ n ∈ b ⊓ I}.Finite := finite_box_inter hK hF T _
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.sum_ite, Finset.sum_const_zero, add_zero]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext n
  simp only [Set.Finite.mem_toFinset, Finset.mem_filter, Set.mem_ofPred_eq, Submodule.mem_inf]
  tauto

private theorem local_density_error_le_of_bounded_congruent (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (m : ℕ)
    (S : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal})
    (a : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} → 𝓞 F → ℝ) (C : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} → ℝ)
    (c : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} → ℕ) (hbd : ∀ 𝔭 ∈ S, ∀ n, |a 𝔭 n| ≤ C 𝔭)
    (hcg : ∀ 𝔭 ∈ S, ∀ (n n' : 𝓞 F) (k : ℕ), n ≠ 0 → vF 𝔭.1 n + c 𝔭 ≤ k → n - n' ∈ 𝔭.1 ^ k →
      a 𝔭 n = a 𝔭 n') (b : Ideal (𝓞 F)) (T w : ℝ) (hw : 0 ≤ w) (k : ℕ) :
    |w * ∑ᶠ n ∈ {n : 𝓞 F | n ∈ boxSet K F T ∧ n ∈ b},
        (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1) * ∏ 𝔭 ∈ S, a 𝔭 n -
      w * ∑ᶠ n ∈ {n : 𝓞 F | n ∈ boxSet K F T ∧ n ∈ b},
        (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1) *
          ∏ 𝔭 ∈ S, a 𝔭 (Quotient.out (Ideal.Quotient.mk (𝔭.1 ^ k) n))| ≤
      2 * (∏ 𝔭 ∈ S, C 𝔭) * ∑ 𝔭 ∈ S, w * ∑ᶠ n ∈ {n : 𝓞 F | n ∈ boxSet K F T ∧ n ∈ b ⊓ 𝔭.1 ^ (k + 1 - c 𝔭)},
        (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1) := by
  classical
  have hfin : {n : 𝓞 F | n ∈ boxSet K F T ∧ n ∈ b}.Finite := finite_box_inter hK hF T _
  simp_rw [finsum_boxSet_inf_eq_sum_ite_mem hK hF T b _ _ hfin]
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin, ← mul_sub,
    ← Finset.sum_sub_distrib, abs_mul, abs_of_nonneg hw]
  have hWn : ∀ n : 𝓞 F, 0 ≤ (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1) := fun n => by positivity
  calc w * |∑ n ∈ hfin.toFinset, ((Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1) * ∏ 𝔭 ∈ S, a 𝔭 n -
        (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1) *
          ∏ 𝔭 ∈ S, a 𝔭 (Quotient.out (Ideal.Quotient.mk (𝔭.1 ^ k) n)))|
      ≤ w * ∑ n ∈ hfin.toFinset, (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1) *
          (2 * (∏ 𝔭 ∈ S, C 𝔭) * ∑ 𝔭 ∈ S, (if n ∈ 𝔭.1 ^ (k + 1 - c 𝔭) then 1 else 0)) := by
        refine mul_le_mul_of_nonneg_left (le_trans (Finset.abs_sum_le_sum_abs _ _)
          (Finset.sum_le_sum fun n hn => ?_)) hw
        rw [← mul_sub, abs_mul, abs_of_nonneg (hWn n)]
        exact mul_le_mul_of_nonneg_left (abs_prod_sub_le S a C c hbd hcg k
          (ne_zero_of_mem_boxSet (hfin.mem_toFinset.1 hn).1)) (hWn n)
    _ = 2 * (∏ 𝔭 ∈ S, C 𝔭) * ∑ 𝔭 ∈ S, w * ∑ n ∈ hfin.toFinset,
          (if n ∈ 𝔭.1 ^ (k + 1 - c 𝔭) then (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1) else 0) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun 𝔭 _ => Finset.sum_congr rfl fun n _ => ?_
        split_ifs <;> ring

theorem tendsto_sum_of_mean (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {m : ℕ} (hm : 1 ≤ m)
    (S : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal})
    (a : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} → 𝓞 F → ℝ) (C : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} → ℝ)
    (c : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} → ℕ) (hbd : ∀ 𝔭 ∈ S, ∀ n, |a 𝔭 n| ≤ C 𝔭)
    (hcg : ∀ 𝔭 ∈ S, ∀ (n n' : 𝓞 F) (k : ℕ), n ≠ 0 → vF 𝔭.1 n + c 𝔭 ≤ k → n - n' ∈ 𝔭.1 ^ k →
      a 𝔭 n = a 𝔭 n')
    (hmean : ∀ 𝔭 ∈ S, Tendsto (fun k : ℕ => (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(k : ℤ)) *
      ∑ᶠ n' : 𝓞 F ⧸ 𝔭.1 ^ k, a 𝔭 (Quotient.out n')) atTop (𝓝 1))
    {b : Ideal (𝓞 F)} (hb : b ≠ ⊥) (hbS : ∀ 𝔭 ∈ S, b ⊔ 𝔭.1 = ⊤) :
    Tendsto (fun j : ℕ => ((j : ℝ) ^ 2) ^ (-((Formalism.HermitianLatticesTheory.fDeg K * m : ℕ) : ℤ)) *
        ∑ᶠ n ∈ {n : 𝓞 F | n ∈ boxSet K F ((j : ℝ) ^ 2) ∧ n ∈ b},
          (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1) * ∏ 𝔭 ∈ S, a 𝔭 n)
      atTop (𝓝 ((m : ℝ) ^ (-(Formalism.HermitianLatticesTheory.fDeg K : ℤ)) /
        Real.sqrt ((2 * Formalism.HermitianLatticesTheory.vInv K) ^ Formalism.HermitianLatticesTheory.fDeg K) / (Ideal.absNorm b : ℝ))) := by
  classical
  obtain ⟨L1, hL1⟩ : ∃ L1 : ℝ, L1 = (m : ℝ) ^ (-(Formalism.HermitianLatticesTheory.fDeg K : ℤ)) /
      Real.sqrt ((2 * Formalism.HermitianLatticesTheory.vInv K) ^ Formalism.HermitianLatticesTheory.fDeg K) := ⟨_, rfl⟩
  rw [← hL1]
  have hL1n : 0 ≤ L1 := by
    rw [hL1]
    exact div_nonneg (zpow_nonneg (Nat.cast_nonneg _) _) (Real.sqrt_nonneg _)
  have hw : ∀ j : ℕ, 0 ≤ ((j : ℝ) ^ 2) ^ (-((Formalism.HermitianLatticesTheory.fDeg K * m : ℕ) : ℤ)) := fun j =>
    zpow_nonneg (sq_nonneg _) _
  have hC0 : 0 ≤ 2 * ∏ 𝔭 ∈ S, C 𝔭 :=
    mul_nonneg (by norm_num) (Finset.prod_nonneg fun 𝔭 h𝔭 => le_trans (abs_nonneg _) (hbd 𝔭 h𝔭 0))
  have hpos : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, 𝔭.1 ≠ ⊥ := fun 𝔭 =>
    Ring.ne_bot_of_isMaximal_of_not_isField 𝔭.2 (NumberField.RingOfIntegers.not_isField F)
  have hIne : ∀ (𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) (e : ℕ), b ⊓ 𝔭.1 ^ e ≠ ⊥ := by
    intro 𝔭 e h
    have h1 : b * 𝔭.1 ^ e ≤ b ⊓ 𝔭.1 ^ e := Ideal.mul_le_inf
    rw [h, le_bot_iff, ← Ideal.zero_eq_bot] at h1
    rcases mul_eq_zero.1 h1 with h2 | h2
    · exact hb (by rwa [Ideal.zero_eq_bot] at h2)
    · exact hpos 𝔭 (by rw [← Ideal.zero_eq_bot]; exact pow_eq_zero_iff'.1 h2 |>.1)
  have hNle : ∀ (𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) (e : ℕ),
      L1 / (Ideal.absNorm (b ⊓ 𝔭.1 ^ e) : ℝ) ≤ L1 / (Ideal.absNorm 𝔭.1 : ℝ) ^ e := by
    intro 𝔭 e
    have hd : Ideal.absNorm (𝔭.1 ^ e) ∣ Ideal.absNorm (b ⊓ 𝔭.1 ^ e) :=
      Ideal.absNorm_dvd_absNorm_of_le inf_le_right
    have hn0 : Ideal.absNorm (b ⊓ 𝔭.1 ^ e) ≠ 0 := fun h => hIne 𝔭 e (Ideal.absNorm_eq_zero_iff.1 h)
    have hp0 : Ideal.absNorm 𝔭.1 ≠ 0 := fun h => hpos 𝔭 (Ideal.absNorm_eq_zero_iff.1 h)
    have hle : Ideal.absNorm 𝔭.1 ^ e ≤ Ideal.absNorm (b ⊓ 𝔭.1 ^ e) := by
      rw [← map_pow]
      exact Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hd
    refine div_le_div_of_nonneg_left hL1n (by positivity) ?_
    exact_mod_cast hle
  have hμ : Tendsto (fun k : ℕ => L1 / (Ideal.absNorm b : ℝ) * ∏ 𝔭 ∈ S, ((Ideal.absNorm 𝔭.1 : ℝ) ^ (-(k : ℤ)) *
      ∑ᶠ n' : 𝓞 F ⧸ 𝔭.1 ^ k, a 𝔭 (Quotient.out n'))) atTop (𝓝 (L1 / (Ideal.absNorm b : ℝ) * 1)) := by
    have := tendsto_finsetProd S hmean
    simp only [Finset.prod_const_one] at this
    exact this.const_mul _
  have hErr := tendsto_err S (2 * ∏ 𝔭 ∈ S, C 𝔭) L1 c
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨K1, hK1⟩ := Metric.tendsto_atTop.1 hμ (ε / 4) (by linarith)
  obtain ⟨K2, hK2⟩ := Metric.tendsto_atTop.1 hErr (ε / 4) (by linarith)
  obtain ⟨k, hk1, hk2⟩ : ∃ k, K1 ≤ k ∧ K2 ≤ k := ⟨max K1 K2, le_max_left _ _, le_max_right _ _⟩
  have g1 := hK1 k hk1
  have g2 := hK2 k hk2
  rw [Real.dist_eq, mul_one] at g1
  rw [Real.dist_eq, sub_zero] at g2
  have hP := tendsto_sum_periodic hK hF hm k (fun 𝔭 q => a 𝔭 (Quotient.out q)) S b hb hbS 0
  simp only [sub_zero] at hP
  rw [← hL1] at hP
  have hE : Tendsto (fun j : ℕ => 2 * (∏ 𝔭 ∈ S, C 𝔭) * ∑ 𝔭 ∈ S, ((j : ℝ) ^ 2) ^ (-((Formalism.HermitianLatticesTheory.fDeg K * m : ℕ) : ℤ)) *
      ∑ᶠ n ∈ {n : 𝓞 F | n ∈ boxSet K F ((j : ℝ) ^ 2) ∧ n ∈ b ⊓ 𝔭.1 ^ (k + 1 - c 𝔭)},
        (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1)) atTop
      (𝓝 (2 * (∏ 𝔭 ∈ S, C 𝔭) * ∑ 𝔭 ∈ S, L1 / (Ideal.absNorm (b ⊓ 𝔭.1 ^ (k + 1 - c 𝔭)) : ℝ))) := by
    refine Tendsto.const_mul _ (tendsto_finsetSum S fun 𝔭 _ => ?_)
    have := tendsto_sum_ideal hK hF hm (hIne 𝔭 (k + 1 - c 𝔭))
    rwa [← hL1] at this
  obtain ⟨J1, hJ1⟩ := Metric.tendsto_atTop.1 hP (ε / 4) (by linarith)
  obtain ⟨J2, hJ2⟩ := Metric.tendsto_atTop.1 hE (ε / 4) (by linarith)
  refine ⟨max J1 J2, fun j hj => ?_⟩
  have d1 := hJ1 j (le_of_max_le_left hj)
  have d2 := hJ2 j (le_of_max_le_right hj)
  rw [Real.dist_eq] at d1 d2 ⊢
  have hcmp : 2 * (∏ 𝔭 ∈ S, C 𝔭) * ∑ 𝔭 ∈ S, L1 / (Ideal.absNorm (b ⊓ 𝔭.1 ^ (k + 1 - c 𝔭)) : ℝ) ≤
      2 * (∏ 𝔭 ∈ S, C 𝔭) * ∑ 𝔭 ∈ S, L1 / (Ideal.absNorm 𝔭.1 : ℝ) ^ (k + 1 - c 𝔭) :=
    mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun 𝔭 _ => hNle 𝔭 _) hC0
  have key := local_density_error_le_of_bounded_congruent hK hF m S a C c hbd hcg b ((j : ℝ) ^ 2) _ (hw j) k
  have t1 := abs_sub_le (((j : ℝ) ^ 2) ^ (-((Formalism.HermitianLatticesTheory.fDeg K * m : ℕ) : ℤ)) *
      ∑ᶠ n ∈ {n : 𝓞 F | n ∈ boxSet K F ((j : ℝ) ^ 2) ∧ n ∈ b},
        (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1) * ∏ 𝔭 ∈ S, a 𝔭 n)
    (((j : ℝ) ^ 2) ^ (-((Formalism.HermitianLatticesTheory.fDeg K * m : ℕ) : ℤ)) *
      ∑ᶠ n ∈ {n : 𝓞 F | n ∈ boxSet K F ((j : ℝ) ^ 2) ∧ n ∈ b},
        (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1) *
          ∏ 𝔭 ∈ S, a 𝔭 (Quotient.out (Ideal.Quotient.mk (𝔭.1 ^ k) n)))
    (L1 / (Ideal.absNorm b : ℝ))
  have t2 := abs_sub_le (((j : ℝ) ^ 2) ^ (-((Formalism.HermitianLatticesTheory.fDeg K * m : ℕ) : ℤ)) *
      ∑ᶠ n ∈ {n : 𝓞 F | n ∈ boxSet K F ((j : ℝ) ^ 2) ∧ n ∈ b},
        (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1) *
          ∏ 𝔭 ∈ S, a 𝔭 (Quotient.out (Ideal.Quotient.mk (𝔭.1 ^ k) n)))
    (L1 / (Ideal.absNorm b : ℝ) * ∏ 𝔭 ∈ S, ((Ideal.absNorm 𝔭.1 : ℝ) ^ (-(k : ℤ)) *
      ∑ᶠ n' : 𝓞 F ⧸ 𝔭.1 ^ k, a 𝔭 (Quotient.out n')))
    (L1 / (Ideal.absNorm b : ℝ))
  have d2' := (abs_lt.1 d2).2
  have g2' := (abs_lt.1 g2).2
  linarith

end Formalism.HermitianLattices.Ext.L3.BoxSum
