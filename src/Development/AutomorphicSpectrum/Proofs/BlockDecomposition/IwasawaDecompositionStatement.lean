module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JpUnif
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaDecompositionStatement
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaDecompositionStatement
@[expose] public section

noncomputable section

open Matrix

namespace GlobalTheory.CompanionTheory.Jp.Iw

section Ops

variable {O L ι : Type} [CommRing O] [Field L] [Algebra O L] [Fintype ι] [DecidableEq ι]

def admitted (O : Type) [CommRing O] [Algebra O L] (T : Finset ι) (k : GL ι L) : Prop :=
  (∃ κ : GL ι O, Matrix.GeneralLinearGroup.map (algebraMap O L) κ = k) ∧
    ∀ v : ι → L, (∀ i ∈ T, v i = 0) → v ᵥ* k.1 = v

lemma admitted.one (T : Finset ι) : admitted O T (1 : GL ι L) :=
  ⟨⟨1, map_one _⟩, fun v _ => by simp⟩

lemma admitted.mul {T : Finset ι} {k k' : GL ι L} (h : admitted O T k) (h' : admitted O T k') : admitted O T (k * k') := by
  obtain ⟨⟨κ, rfl⟩, f⟩ := h
  obtain ⟨⟨κ', rfl⟩, f'⟩ := h'
  refine ⟨⟨κ * κ', map_mul _ _ _⟩, fun v hv => ?_⟩
  rw [Units.val_mul, ← Matrix.vecMul_vecMul, f v hv, f' v hv]

lemma exists_transv {T : Finset ι} {i j : ι} (hi : i ∈ T) (hij : i ≠ j) (c : O) :
    ∃ k : GL ι L, admitted O T k ∧
      ∀ z : ι → L, z ᵥ* k.1 = z + Pi.single j (z i * algebraMap O L c) := by
  let κ : GL ι O := ⟨transvection i j c, transvection i j (-c),
    by simp [transvection_mul_transvection_same, hij], by simp [transvection_mul_transvection_same, hij]⟩
  have key : ∀ z : ι → L, z ᵥ* (Matrix.GeneralLinearGroup.map (algebraMap O L) κ).1 =
      z + Pi.single j (z i * algebraMap O L c) := by
    intro z
    have e : (Matrix.GeneralLinearGroup.map (algebraMap O L) κ).1 =
        1 + Matrix.single i j (algebraMap O L c) := by
      ext a b
      simp [κ, transvection, Matrix.one_apply, Matrix.single_apply, apply_ite (algebraMap O L)]
    rw [e, Matrix.vecMul_add, Matrix.vecMul_one]
    congr 1
    ext l
    by_cases h : l = j
    · subst h
      simp [Matrix.vecMul, dotProduct, Matrix.single_apply]
    · simp [Matrix.vecMul, dotProduct, Matrix.single_apply, h, Ne.symm h]
  exact ⟨_, ⟨⟨κ, rfl⟩, fun v hv => by rw [key, hv i hi]; simp⟩, key⟩

lemma exists_mul_or [IsDomain O] [ValuationRing O] [IsFractionRing O L] (a b : L) :
    (∃ c : O, b = algebraMap O L c * a) ∨ ∃ c : O, a = algebraMap O L c * b := by
  by_cases ha : a = 0
  · exact Or.inr ⟨0, by simp [ha]⟩
  by_cases hb : b = 0
  · exact Or.inl ⟨0, by simp [hb]⟩
  rcases ValuationRing.isInteger_or_isInteger O (b / a) with ⟨c, hc⟩ | ⟨c, hc⟩
  · refine Or.inl ⟨c, ?_⟩
    have hc' : algebraMap O L c = b / a := hc
    rw [hc']; field_simp
  · refine Or.inr ⟨c, ?_⟩
    have hc' : algebraMap O L c = (b / a)⁻¹ := hc
    rw [hc']; field_simp

lemma exists_clear [IsDomain O] [ValuationRing O] [IsFractionRing O L] {T : Finset ι} {j p : ι}
    (hj : j ∈ T) (hp : p ∈ T) (hjp : j ≠ p) (z : ι → L) :
    ∃ k : GL ι L, admitted O T k ∧ (z ᵥ* k.1) j = 0 ∧ ∀ l, l ≠ j → l ≠ p → (z ᵥ* k.1) l = z l := by
  rcases exists_mul_or (O := O) (z j) (z p) with ⟨c, hc⟩ | ⟨c, hc⟩
  · obtain ⟨k₁, a₁, h₁⟩ := exists_transv (O := O) (L := L) hj hjp (1 - c)
    obtain ⟨k₂, a₂, h₂⟩ := exists_transv (O := O) (L := L) hp hjp.symm (-1)
    refine ⟨k₁ * k₂, a₁.mul a₂, ?_, fun l hl hl' => ?_⟩
    · rw [Units.val_mul, ← Matrix.vecMul_vecMul, h₂, h₁]
      simp [Pi.single_apply, hjp, hjp.symm, hc]
      ring
    · rw [Units.val_mul, ← Matrix.vecMul_vecMul, h₂, h₁]
      simp [Pi.single_apply, hl, hl']
  · obtain ⟨k, a, h⟩ := exists_transv (O := O) (L := L) hp hjp.symm (-c)
    refine ⟨k, a, ?_, fun l hl _ => ?_⟩
    · rw [h]
      simp [hc]
      ring
    · rw [h]
      simp [Pi.single_apply, hl]

lemma exists_clear_set [IsDomain O] [ValuationRing O] [IsFractionRing O L] {T : Finset ι} {p : ι}
    (hp : p ∈ T) (z : ι → L) (s : Finset ι) (hs : s ⊆ T) (hps : p ∉ s) :
    ∃ k : GL ι L, admitted O T k ∧ ∀ l ∈ s, (z ᵥ* k.1) l = 0 := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1, admitted.one T, by simp⟩
  | insert a s ha ih =>
    obtain ⟨k, hk, h⟩ := ih ((Finset.subset_insert a s).trans hs)
      (fun hh => hps (Finset.mem_insert_of_mem hh))
    have hap : a ≠ p := fun e => hps (e ▸ Finset.mem_insert_self a s)
    obtain ⟨k', hk', h0, h1⟩ := exists_clear (O := O) (hs (Finset.mem_insert_self a s)) hp hap (z ᵥ* k.1)
    refine ⟨k * k', hk.mul hk', fun l hl => ?_⟩
    rw [Units.val_mul, ← Matrix.vecMul_vecMul]
    rcases Finset.mem_insert.1 hl with rfl | hl
    · exact h0
    · rw [h1 l (fun e => ha (e ▸ hl)) (fun e => hps (e ▸ Finset.mem_insert_of_mem hl))]
      exact h l hl

lemma exists_rows [IsDomain O] [ValuationRing O] [IsFractionRing O L] {ρ : Type} [DecidableEq ρ]
    (f : ρ → ι) (hf : Function.Injective f) (g : Matrix ι ι L) (S : Finset ρ) :
    ∃ κ : GL ι O, ∀ i ∈ S, ∀ c ∉ S.image f,
      (g * (Matrix.GeneralLinearGroup.map (algebraMap O L) κ).1) (f i) c = 0 := by
  induction S using Finset.induction_on with
  | empty => exact ⟨1, by simp⟩
  | insert a S ha ih =>
    obtain ⟨κ, h⟩ := ih
    have hpT : f a ∈ (S.image f)ᶜ := by
      simp only [Finset.mem_compl, Finset.mem_image, not_exists, not_and]
      exact fun x hx e => ha (hf e ▸ hx)
    obtain ⟨k, ⟨⟨κ', rfl⟩, fix⟩, hk⟩ := exists_clear_set (O := O) hpT
      ((g * (Matrix.GeneralLinearGroup.map (algebraMap O L) κ).1) (f a)) (((S.image f)ᶜ).erase (f a))
      (Finset.erase_subset _ _) (Finset.notMem_erase _ _)
    refine ⟨κ * κ', fun i hi c hc => ?_⟩
    have row : ∀ r, (g * (Matrix.GeneralLinearGroup.map (algebraMap O L) (κ * κ')).1) r =
        (g * (Matrix.GeneralLinearGroup.map (algebraMap O L) κ).1) r ᵥ*
          (Matrix.GeneralLinearGroup.map (algebraMap O L) κ').1 := by
      intro r
      rw [map_mul, Units.val_mul, ← Matrix.mul_assoc, Matrix.mul_apply_eq_vecMul]
    have hcS : c ∉ S.image f := fun e => hc (by
      rw [Finset.image_insert]; exact Finset.mem_insert_of_mem e)
    have hca : c ≠ f a := fun e => hc (by
      rw [Finset.image_insert, e]; exact Finset.mem_insert_self _ _)
    rw [row]
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact hk c (Finset.mem_erase.2 ⟨hca, Finset.mem_compl.2 hcS⟩)
    · rw [fix _ (fun l hl => h i hi l (Finset.mem_compl.1 hl))]
      exact h i hi c hcS

end Ops

theorem jpIw : JpIw := by
  intro O L _ _ _ _ _ _ n g
  obtain ⟨κ, h⟩ := exists_rows (O := O) (L := L) (ι := Ix n) (Sum.inr : Fin n → Ix n)
    Sum.inr_injective g.1 Finset.univ
  set k : GL (Ix n) L := inL κ with hk
  set G : Matrix (Ix n) (Ix n) L := (g * k).1 with hG
  have hC : G.toBlocks₂₁ = 0 := by
    ext i j
    exact h i (Finset.mem_univ _) (Sum.inl j) (by simp)
  have hGb : G = fromBlocks G.toBlocks₁₁ G.toBlocks₁₂ 0 G.toBlocks₂₂ := by
    rw [← hC, Matrix.fromBlocks_toBlocks]
  have hdet : G.toBlocks₁₁.det * G.toBlocks₂₂.det ≠ 0 := by
    rw [← Matrix.det_fromBlocks_zero₂₁ G.toBlocks₁₁ G.toBlocks₁₂ G.toBlocks₂₂, ← hGb]
    exact (Matrix.isUnits_det_units (g * k)).ne_zero
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ (left_ne_zero_of_mul hdet),
    Matrix.GeneralLinearGroup.mkOfDetNeZero _ (right_ne_zero_of_mul hdet), G.toBlocks₁₂, κ⁻¹, ?_⟩
  have hp : pM (Matrix.GeneralLinearGroup.mkOfDetNeZero _ (left_ne_zero_of_mul hdet))
      (Matrix.GeneralLinearGroup.mkOfDetNeZero _ (right_ne_zero_of_mul hdet)) G.toBlocks₁₂ = g * k := by
    apply Units.ext
    exact hGb.symm
  rw [hp, map_inv, ← hk, mul_inv_cancel_right]

end GlobalTheory.CompanionTheory.Jp.Iw

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaDecompositionStatementStatement
open GlobalTheory.CompanionTheory.Jp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawa_decomposition_statement : GlobalTheory.CompanionTheory.Jp.JpIw := by
  first | exact @GlobalTheory.CompanionTheory.Jp.Iw.jpIw | exact GlobalTheory.CompanionTheory.Jp.Iw.jpIw | (intros; apply GlobalTheory.CompanionTheory.Jp.Iw.jpIw <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasureUnitImage
open MeasureTheory Topology Filter GlobalTheory.CompanionTheory.NullFr
open scoped NNReal ENNReal Matrix

namespace GlobalTheory.CompanionTheory.NullFr.Packing

theorem exists_max_card {α : Type} (Q : Finset α → Prop) (B : ℕ) (h0 : ∃ P, Q P)
    (hB : ∀ P, Q P → P.card ≤ B) : ∃ P, Q P ∧ ∀ P', Q P' → P'.card ≤ P.card := by
  obtain ⟨P₀, hP₀⟩ := h0
  have hne : {n : ℕ | ∃ P, Q P ∧ P.card = n}.Nonempty := ⟨P₀.card, P₀, hP₀, rfl⟩
  have hbdd : BddAbove {n : ℕ | ∃ P, Q P ∧ P.card = n} := by
    refine ⟨B, ?_⟩
    rintro n ⟨P, hP, rfl⟩
    exact hB P hP
  obtain ⟨P, hP, hcard⟩ := Nat.sSup_mem hne hbdd
  refine ⟨P, hP, fun P' hP' => ?_⟩
  rw [hcard]
  exact le_csSup hbdd ⟨P', hP', rfl⟩

theorem measure_unit_image {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [T2Space A] [MeasurableSpace A] [BorelSpace A] {md : Aˣ →* ℝ≥0} (hmd : IsHaarMod md)
    (h : Measure A) [h.IsAddHaarMeasure] (u : Aˣ) {K : Set A} (hK : IsCompact K) :
    h ((fun x : A => (u : A) * x) '' K) = md u * h K := by
  have hc : Continuous fun x : A => (u : A) * x := continuous_const.mul continuous_id
  have hinj : Function.Injective fun x : A => (u : A) * x := fun x y hxy => by
    simpa using congrArg (fun z => ((u⁻¹ : Aˣ) : A) * z) hxy
  have hKu : IsCompact ((fun x : A => (u : A) * x) '' K) := hK.image hc
  have key := congrArg (fun μ : Measure A => μ ((fun x : A => (u : A) * x) '' K))
    (hmd h inferInstance u)
  rw [Measure.map_apply hc.measurable hKu.measurableSet, Set.preimage_image_eq _ hinj,
    Measure.smul_apply, smul_eq_mul] at key
  have hmd0 : ((md u : ℝ≥0) : ℝ≥0∞) ≠ 0 := by
    have h1 : md u * md u⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    intro h0
    rw [ENNReal.coe_eq_zero] at h0
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  rw [key, ← mul_assoc, ENNReal.mul_inv_cancel hmd0 ENNReal.coe_ne_top, one_mul]

theorem card_mul_le {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [T2Space A] [MeasurableSpace A] [BorelSpace A] {md : Aˣ →* ℝ≥0} (hmd : IsHaarMod md)
    (h : Measure A) [h.IsAddHaarMeasure] (u : Aˣ) {K L : Set A} (hK : IsCompact K) (P : Finset A)
    (hdisj : ∀ p ∈ P, ∀ q ∈ P, p ≠ q →
      Disjoint ((fun x : A => p + (u : A) * x) '' K) ((fun x : A => q + (u : A) * x) '' K))
    (hL : ∀ p ∈ P, ∀ w ∈ K, p + (u : A) * w ∈ L) :
    (P.card : ℝ≥0∞) * (md u * h K) ≤ h L := by
  classical
  have hcont : ∀ p : A, Continuous fun x : A => p + (u : A) * x := fun p =>
    continuous_const.add (continuous_const.mul continuous_id)
  have hmT : ∀ p : A, h ((fun x : A => p + (u : A) * x) '' K) = md u * h K := by
    intro p
    have e : (fun x : A => p + (u : A) * x) '' K =
        (fun y => -p + y) ⁻¹' ((fun x : A => (u : A) * x) '' K) := by
      ext y
      simp only [Set.mem_image, Set.mem_preimage]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, hx, by abel⟩
      · rintro ⟨x, hx, hxy⟩
        exact ⟨x, hx, by rw [hxy]; abel⟩
    rw [e, measure_preimage_add, GlobalTheory.CompanionTheory.NullFr.Packing.measure_unit_image hmd h u hK]
  have hsub : (⋃ p ∈ P, (fun x : A => p + (u : A) * x) '' K) ⊆ L := by
    refine Set.iUnion₂_subset fun p hp => ?_
    rintro _ ⟨w, hw, rfl⟩
    exact hL p hp w hw
  calc (P.card : ℝ≥0∞) * (md u * h K)
      = ∑ p ∈ P, h ((fun x : A => p + (u : A) * x) '' K) := by
        rw [Finset.sum_congr rfl (fun p _ => hmT p), Finset.sum_const, nsmul_eq_mul]
    _ = h (⋃ p ∈ P, (fun x : A => p + (u : A) * x) '' K) :=
        (measure_biUnion_finset (fun p hp q hq hpq => hdisj p hp q hq hpq)
          (fun p _ => (hK.image (hcont p)).measurableSet)).symm
    _ ≤ h L := measure_mono hsub

theorem net : ∀ {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [LocallyCompactSpace A] [T2Space A] [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A] (md : Aˣ →* ℝ≥0) (_ : IsHaarMod md) (f : A) (_ : f * f = f) (C U : Set A) (_ : IsCompact C) (_ : U ∈ 𝓝 (0 : A)),
    ∃ (κ : ℝ≥0) (V : Set A), V ∈ 𝓝 (0 : A) ∧ ∀ u : Aˣ, (1 - f) * (u : A) = 1 - f → f * (u : A) ∈ V →
      ∃ N : Finset A, (∀ p ∈ N, f * p = p ∧ p ∈ C) ∧ (N.card : ℝ≥0) * md u ≤ κ ∧
        ∀ c ∈ C, f * c = c → ∃ p ∈ N, ∃ w ∈ U, f * w = w ∧ c = p + u * w := by
  intro A _ _ _ _ _ _ _ _ md hmd f _ C U hC hU
  classical
  have hU' : U ∈ 𝓝 ((0 : A) - 0) := by rwa [sub_zero]
  have h0 : (fun p : A × A => p.1 - p.2) ⁻¹' U ∈ 𝓝 ((0 : A), (0 : A)) :=
    continuous_sub.tendsto ((0 : A), (0 : A)) hU'
  obtain ⟨W₁, hW₁, W₂, hW₂, hW⟩ := mem_nhds_prod_iff.1 h0
  obtain ⟨K, hK0, hKW, hK⟩ := local_compact_nhds (Filter.inter_mem hW₁ hW₂)
  have hKU : ∀ a ∈ K, ∀ b ∈ K, a - b ∈ U := fun a ha b hb =>
    hW (Set.mk_mem_prod (hKW ha).1 (hKW hb).2)
  obtain ⟨V, hV0, -, hV⟩ := local_compact_nhds (Filter.univ_mem : Set.univ ∈ 𝓝 (0 : A))
  obtain ⟨L, hLdef⟩ : ∃ L : Set A,
      L = (fun q : A × A × A => q.1 + q.2.1 * q.2.2 + (1 - f) * q.2.2) '' (C ×ˢ V ×ˢ K) :=
    ⟨_, rfl⟩
  have hLc : IsCompact L := by
    rw [hLdef]
    exact (hC.prod (hV.prod hK)).image (by fun_prop)
  obtain ⟨μ, hμ⟩ : ∃ μ : Measure A, μ.IsAddHaarMeasure := ⟨Measure.addHaar, inferInstance⟩
  have hKpos : 0 < μ K := Measure.measure_pos_of_mem_nhds μ hK0
  have hKfin : μ K < ⊤ := hK.measure_lt_top
  have hLfin : μ L < ⊤ := hLc.measure_lt_top
  refine ⟨(μ L / μ K).toNNReal, V, hV0, ?_⟩
  intro u hu1 hfu
  have hmd0 : md u ≠ 0 := by
    intro h0
    have h1 : md u * md u⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  have hm0 : (md u : ℝ≥0∞) * μ K ≠ 0 := mul_ne_zero (by exact_mod_cast hmd0) hKpos.ne'
  have hmtop : (md u : ℝ≥0∞) * μ K ≠ ⊤ := ENNReal.mul_ne_top ENNReal.coe_ne_top hKfin.ne
  have hLmem : ∀ P : Finset A, (∀ p ∈ P, f * p = p ∧ p ∈ C) →
      ∀ p ∈ P, ∀ w ∈ K, p + (u : A) * w ∈ L := by
    intro P hP p hp w hw
    rw [hLdef]
    refine ⟨(p, f * u, w), ⟨(hP p hp).2, hfu, hw⟩, ?_⟩
    show p + f * u * w + (1 - f) * w = p + u * w
    rw [← hu1]
    ring
  have hB : ∀ P : Finset A, ((∀ p ∈ P, f * p = p ∧ p ∈ C) ∧ ∀ p ∈ P, ∀ q ∈ P, p ≠ q →
      Disjoint ((fun x : A => p + (u : A) * x) '' K) ((fun x : A => q + (u : A) * x) '' K)) →
      P.card ≤ ⌈(μ L / ((md u : ℝ≥0∞) * μ K)).toReal⌉₊ := by
    intro P hP
    have hc := GlobalTheory.CompanionTheory.NullFr.Packing.card_mul_le hmd μ u hK P hP.2 (hLmem P hP.1)
    have h1 : (P.card : ℝ≥0∞) ≤ μ L / ((md u : ℝ≥0∞) * μ K) :=
      (ENNReal.le_div_iff_mul_le (Or.inl hm0) (Or.inl hmtop)).2 hc
    have h2 : (P.card : ℝ) ≤ (μ L / ((md u : ℝ≥0∞) * μ K)).toReal := by
      simpa using ENNReal.toReal_mono (ENNReal.div_ne_top hLfin.ne hm0) h1
    exact_mod_cast h2.trans (Nat.le_ceil _)
  obtain ⟨P, ⟨hPC, hPdisj⟩, hmax⟩ :=
    GlobalTheory.CompanionTheory.NullFr.Packing.exists_max_card (hB := hB) (h0 := ⟨∅, by simp⟩)
  refine ⟨P, hPC, ?_, ?_⟩
  · have hc := GlobalTheory.CompanionTheory.NullFr.Packing.card_mul_le hmd μ u hK P hPdisj (hLmem P hPC)
    have h2 : (((P.card : ℝ≥0) * md u : ℝ≥0) : ℝ≥0∞) ≤ μ L / μ K := by
      rw [ENNReal.le_div_iff_mul_le (Or.inl hKpos.ne') (Or.inl hKfin.ne)]
      push_cast
      rw [mul_assoc]
      exact hc
    calc (P.card : ℝ≥0) * md u = ((((P.card : ℝ≥0) * md u : ℝ≥0) : ℝ≥0∞)).toNNReal := by
          rw [ENNReal.toNNReal_coe]
      _ ≤ (μ L / μ K).toNNReal :=
          ENNReal.toNNReal_mono (ENNReal.div_ne_top hLfin.ne hKpos.ne') h2
  · intro c hc hfc
    by_cases hcP : c ∈ P
    · exact ⟨c, hcP, 0, mem_of_mem_nhds hU, by simp, by simp⟩
    · obtain ⟨p, hp, hpc⟩ : ∃ p ∈ P, ¬ Disjoint ((fun x : A => p + (u : A) * x) '' K)
          ((fun x : A => c + (u : A) * x) '' K) := by
        by_contra hcon
        push_neg at hcon
        have hQ : (∀ p ∈ insert c P, f * p = p ∧ p ∈ C) ∧ ∀ p ∈ insert c P, ∀ q ∈ insert c P,
            p ≠ q → Disjoint ((fun x : A => p + (u : A) * x) '' K)
              ((fun x : A => q + (u : A) * x) '' K) := by
          refine ⟨fun p hp => ?_, fun p hp q hq hpq => ?_⟩
          · rcases Finset.mem_insert.1 hp with rfl | hp'
            · exact ⟨hfc, hc⟩
            · exact hPC p hp'
          · rcases Finset.mem_insert.1 hp with rfl | hp' <;>
              rcases Finset.mem_insert.1 hq with rfl | hq'
            · exact absurd rfl hpq
            · exact (hcon q hq').symm
            · exact hcon p hp'
            · exact hPdisj p hp' q hq' hpq
        have hle := hmax _ hQ
        rw [Finset.card_insert_of_notMem hcP] at hle
        omega
      obtain ⟨x, ⟨k₁, hk₁, hx₁⟩, ⟨k₂, hk₂, hx₂⟩⟩ := Set.not_disjoint_iff.1 hpc
      have hx₁' : p + (u : A) * k₁ = x := hx₁
      have hx₂' : c + (u : A) * k₂ = x := hx₂
      have hw : (u : A) * (k₁ - k₂) = c - p := by linear_combination hx₁' - hx₂'
      have hfp : f * p = p := (hPC p hp).1
      refine ⟨p, hp, k₁ - k₂, hKU k₁ hk₁ k₂ hk₂, ?_, by rw [hw]; ring⟩
      calc f * (k₁ - k₂) = ((u⁻¹ : Aˣ) : A) * ((u : A) * (f * (k₁ - k₂))) := by simp
        _ = ((u⁻¹ : Aˣ) : A) * (f * ((u : A) * (k₁ - k₂))) := by ring
        _ = ((u⁻¹ : Aˣ) : A) * ((u : A) * (k₁ - k₂)) := by rw [hw, mul_sub f c p, hfc, hfp]
        _ = k₁ - k₂ := by simp

end GlobalTheory.CompanionTheory.NullFr.Packing
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReductionCorankEqRankLowerLeft
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReductionCorankEqRankLowerLeft
open Matrix GlobalTheory.CompanionTheory.Jp

noncomputable section

namespace GlobalTheory.CompanionTheory.Jp.RedRank

theorem rank_add_rank_eq {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {n : ℕ} {ϖ : O}
    (hϖ : Irreducible ϖ) (d E : Matrix (Fin n) (Fin n) O) (hdE : d * E = ϖ • (1 : Matrix (Fin n) (Fin n) O))
    (hEd : E * d = ϖ • (1 : Matrix (Fin n) (Fin n) O)) :
    (d.map (IsLocalRing.residue O)).rank + (E.map (IsLocalRing.residue O)).rank = n := by
  have hmax : IsLocalRing.maximalIdeal O = Ideal.span {ϖ} :=
    IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ |>.1 hϖ
  have hres : IsLocalRing.residue O ϖ = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff, hmax]
    exact Ideal.mem_span_singleton_self ϖ
  have hzero : d.map (IsLocalRing.residue O) * E.map (IsLocalRing.residue O) = 0 := by
    rw [← Matrix.map_mul, hdE]
    ext i j
    simp [hres]
  have hker : LinearMap.ker (d.map (IsLocalRing.residue O)).mulVecLin =
      LinearMap.range (E.map (IsLocalRing.residue O)).mulVecLin := by
    ext x
    constructor
    · intro hx
      have hx' : (d.map (IsLocalRing.residue O)) *ᵥ x = 0 := by simpa using hx
      choose x₀ hx₀ using fun i => IsLocalRing.residue_surjective (x i)
      have hxc : (IsLocalRing.residue O) ∘ x₀ = x := funext hx₀
      have hmem : ∀ i, ∃ y : O, y * ϖ = (d *ᵥ x₀) i := by
        intro i
        have h0 : IsLocalRing.residue O ((d *ᵥ x₀) i) = 0 := by
          rw [RingHom.map_mulVec, hxc, hx']
          rfl
        rw [IsLocalRing.residue_eq_zero_iff, hmax] at h0
        exact Ideal.mem_span_singleton'.1 h0
      choose y hy using hmem
      have hdx : d *ᵥ x₀ = ϖ • y := by
        ext i
        simp [← hy i, mul_comm]
      have hEx : ϖ • x₀ = ϖ • (E *ᵥ y) := by
        have h1 : E *ᵥ (d *ᵥ x₀) = ϖ • x₀ := by
          rw [Matrix.mulVec_mulVec, hEd, Matrix.smul_mulVec, Matrix.one_mulVec]
        rw [← h1, hdx, Matrix.mulVec_smul]
      have hxE : x₀ = E *ᵥ y := smul_right_injective _ hϖ.ne_zero hEx
      refine ⟨(IsLocalRing.residue O) ∘ y, ?_⟩
      ext i
      simp only [Matrix.mulVecLin_apply]
      rw [← RingHom.map_mulVec, ← hxE]
      exact hx₀ i
    · rintro ⟨y, rfl⟩
      simp [Matrix.mulVec_mulVec, hzero]
  have hrn := LinearMap.finrank_range_add_finrank_ker (d.map (IsLocalRing.residue O)).mulVecLin
  rw [hker] at hrn
  simpa [Matrix.rank] using hrn

theorem low_rows {R : Type} [CommRing R] {n : ℕ} (g : GL (Ix n) R) :
    lowerLeftBlock g * (g⁻¹).1.toBlocks₁₂ + dBlk g * (g⁻¹).1.toBlocks₂₂ = 1 := by
  have h : g.1 * (g⁻¹).1 = 1 := by rw [← Units.val_mul]; simp
  have e : fromBlocks g.1.toBlocks₁₁ g.1.toBlocks₁₂ g.1.toBlocks₂₁ g.1.toBlocks₂₂ *
      fromBlocks (g⁻¹).1.toBlocks₁₁ (g⁻¹).1.toBlocks₁₂ (g⁻¹).1.toBlocks₂₁ (g⁻¹).1.toBlocks₂₂ = 1 := by
    rw [fromBlocks_toBlocks, fromBlocks_toBlocks]; exact h
  rw [fromBlocks_multiply, ← fromBlocks_one] at e
  exact (Matrix.fromBlocks_inj.1 e).2.2.2

theorem scM_val {L : Type} [Field L] {n : ℕ} (w : Lˣ) : (scM (n := n) w).1 = (w : L) • (1 : Matrix (Fin n) (Fin n) L) := by
  ext i j
  simp [scM, Matrix.one_apply, Matrix.diagonal_apply]

theorem low_eq {L : Type} [Field L] {n : ℕ} (x : L) (X Y : Matrix (Ix n) (Ix n) L) (a b d : Matrix (Fin n) (Fin n) L)
    (h : X * fromBlocks 1 0 0 (x • (1 : Matrix (Fin n) (Fin n) L)) = fromBlocks a b 0 d * Y) :
    X.toBlocks₂₁ = d * Y.toBlocks₂₁ ∧ x • X.toBlocks₂₂ = d * Y.toBlocks₂₂ := by
  have e : fromBlocks X.toBlocks₁₁ X.toBlocks₁₂ X.toBlocks₂₁ X.toBlocks₂₂ *
        fromBlocks 1 0 0 (x • (1 : Matrix (Fin n) (Fin n) L)) =
      fromBlocks a b 0 d * fromBlocks Y.toBlocks₁₁ Y.toBlocks₁₂ Y.toBlocks₂₁ Y.toBlocks₂₂ := by
    rw [fromBlocks_toBlocks, fromBlocks_toBlocks]; exact h
  rw [fromBlocks_multiply, fromBlocks_multiply] at e
  obtain ⟨-, -, h3, h4⟩ := Matrix.fromBlocks_inj.1 e
  simp only [Matrix.mul_one, Matrix.mul_zero, add_zero, zero_add, Matrix.zero_mul, Matrix.mul_smul] at h3 h4
  exact ⟨h3, h4⟩

theorem exists_integral {O L : Type} [CommRing O] [Field L] (ι : O →+* L) (hι : Function.Injective ι) {n : ℕ} (ϖ : O)
    (C D C' D' Bi Di Bi' Di' : Matrix (Fin n) (Fin n) O) (h1 : C * Bi + D * Di = 1) (h2 : C' * Bi' + D' * Di' = 1)
    (dL dLi : Matrix (Fin n) (Fin n) L) (hd : dL * dLi = 1) (hd' : dLi * dL = 1)
    (hC : C.map ι = dL * C'.map ι) (hD : ι ϖ • D.map ι = dL * D'.map ι) :
    (C * Bi' + ϖ • (D * Di')) * (ϖ • (C' * Bi) + D' * Di) = ϖ • (1 : Matrix (Fin n) (Fin n) O) ∧
    (ϖ • (C' * Bi) + D' * Di) * (C * Bi' + ϖ • (D * Di')) = ϖ • (1 : Matrix (Fin n) (Fin n) O) ∧
    C = (C * Bi' + ϖ • (D * Di')) * C' ∧ (ϖ • (C' * Bi) + D' * Di) * D = D' := by
  have hinj : Function.Injective (ι.mapMatrix (m := Fin n)) := fun A B h => by
    ext i j
    exact hι (congrFun (congrFun h i) j)
  have hs : ∀ M : Matrix (Fin n) (Fin n) O, ι.mapMatrix (ϖ • M) = ι ϖ • ι.mapMatrix M := by
    intro M; ext i j; simp
  have hC' : ι.mapMatrix C = dL * ι.mapMatrix C' := hC
  have hD' : ι ϖ • ι.mapMatrix D = dL * ι.mapMatrix D' := hD
  have h1' : ι.mapMatrix C * ι.mapMatrix Bi + ι.mapMatrix D * ι.mapMatrix Di = 1 := by
    rw [← map_mul, ← map_mul, ← map_add (f := _), h1, map_one]
  have h2' : ι.mapMatrix C' * ι.mapMatrix Bi' + ι.mapMatrix D' * ι.mapMatrix Di' = 1 := by
    rw [← map_mul, ← map_mul, ← map_add (f := _), h2, map_one]
  have hCi : ι.mapMatrix C' = dLi * ι.mapMatrix C := by
    rw [hC', ← Matrix.mul_assoc, hd', Matrix.one_mul]
  have hDi : ι.mapMatrix D' = ι ϖ • (dLi * ι.mapMatrix D) := by
    rw [← Matrix.mul_smul, hD', ← Matrix.mul_assoc, hd', Matrix.one_mul]
  have hF : ι.mapMatrix (C * Bi' + ϖ • (D * Di')) = dL := by
    rw [map_add (f := _), hs, map_mul, map_mul, hC', ← Matrix.smul_mul, hD', Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_add,
      h2', Matrix.mul_one]
  have hG : ι.mapMatrix (ϖ • (C' * Bi) + D' * Di) = ι ϖ • dLi := by
    rw [map_add (f := _), hs, map_mul, map_mul, hCi, hDi, Matrix.smul_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← smul_add,
      ← Matrix.mul_add, h1', Matrix.mul_one]
  refine ⟨hinj ?_, hinj ?_, hinj ?_, hinj ?_⟩
  · rw [map_mul, hF, hG, hs, map_one, Matrix.mul_smul, hd]
  · rw [map_mul, hF, hG, hs, map_one, Matrix.smul_mul, hd']
  · rw [map_mul, hF, hC']
  · rw [map_mul, hG, Matrix.smul_mul, hDi]

theorem iD_eq_rank : ∀ (O L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field L] [Algebra O L] [IsFractionRing O L]
    (n : ℕ) (ϖ : O), Irreducible ϖ → ∀ w : Lˣ, (w : L) = algebraMap O L ϖ →
    ∀ (κ : GL (Ix n) O) (h : GL (Ix n) (IsLocalRing.ResidueField O)), IsRed (O := O) w κ h →
      iD h = (lowerLeftBlock (resK κ)).rank := by
  intro O L _ _ _ _ _ _ n ϖ hϖ w hw κ h hred
  obtain ⟨a, d, b, κ', hEq, rfl⟩ := hred
  have hv := congrArg Units.val hEq
  have hlow := low_eq (w : L) (κ.1.map (algebraMap O L)) (κ'.1.map (algebraMap O L)) a.1 b d.1 (by
    have : (tauM (n := n) w).1 = fromBlocks 1 0 0 ((w : L) • (1 : Matrix (Fin n) (Fin n) L)) := by
      simp [tauM, pM, scM_val]
    rw [← this]
    exact hv)
  have hres : IsLocalRing.residue O ϖ = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff, IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ |>.1 hϖ]
    exact Ideal.mem_span_singleton_self ϖ
  obtain ⟨e1, e2, e3, e4⟩ := exists_integral (algebraMap O L) (IsFractionRing.injective O L) ϖ
    (lowerLeftBlock κ) (dBlk κ) (lowerLeftBlock κ') (dBlk κ') (κ⁻¹).1.toBlocks₁₂ (κ⁻¹).1.toBlocks₂₂ (κ'⁻¹).1.toBlocks₁₂ (κ'⁻¹).1.toBlocks₂₂
    (low_rows κ) (low_rows κ') d.1 (d⁻¹).1 (by rw [← Units.val_mul]; simp) (by rw [← Units.val_mul]; simp)
    hlow.1 (by rw [← hw]; exact hlow.2)
  have hn := rank_add_rank_eq hϖ _ _ e1 e2
  set R := (IsLocalRing.residue O).mapMatrix (m := Fin n) with hR
  have hsz : ∀ M : Matrix (Fin n) (Fin n) O, R (ϖ • M) = 0 := by
    intro M; ext i j; simp [hR, hres]
  have hd0 : (lowerLeftBlock κ * (κ'⁻¹).1.toBlocks₁₂ + ϖ • (dBlk κ * (κ'⁻¹).1.toBlocks₂₂)).map (IsLocalRing.residue O) =
      R (lowerLeftBlock κ) * R (κ'⁻¹).1.toBlocks₁₂ := by
    change R _ = _
    rw [map_add (f := _), hsz, add_zero, map_mul]
  have hE0 : (ϖ • (lowerLeftBlock κ' * (κ⁻¹).1.toBlocks₁₂) + dBlk κ' * (κ⁻¹).1.toBlocks₂₂).map (IsLocalRing.residue O) =
      R (dBlk κ') * R (κ⁻¹).1.toBlocks₂₂ := by
    change R _ = _
    rw [map_add (f := _), hsz, zero_add, map_mul]
  have r1 : ((lowerLeftBlock κ * (κ'⁻¹).1.toBlocks₁₂ + ϖ • (dBlk κ * (κ'⁻¹).1.toBlocks₂₂)).map (IsLocalRing.residue O)).rank
      = (R (lowerLeftBlock κ)).rank := by
    apply le_antisymm
    · rw [hd0]; exact Matrix.rank_mul_le_left _ _
    · have : R (lowerLeftBlock κ) = (lowerLeftBlock κ * (κ'⁻¹).1.toBlocks₁₂ + ϖ • (dBlk κ * (κ'⁻¹).1.toBlocks₂₂)).map (IsLocalRing.residue O) *
          R (lowerLeftBlock κ') := by
        conv_lhs => rw [e3]
        rw [map_mul]; rfl
      rw [this]; exact Matrix.rank_mul_le_left _ _
  have r2 : ((ϖ • (lowerLeftBlock κ' * (κ⁻¹).1.toBlocks₁₂) + dBlk κ' * (κ⁻¹).1.toBlocks₂₂).map (IsLocalRing.residue O)).rank
      = (R (dBlk κ')).rank := by
    apply le_antisymm
    · rw [hE0]; exact Matrix.rank_mul_le_left _ _
    · have : R (dBlk κ') = (ϖ • (lowerLeftBlock κ' * (κ⁻¹).1.toBlocks₁₂) + dBlk κ' * (κ⁻¹).1.toBlocks₂₂).map (IsLocalRing.residue O) *
          R (dBlk κ) := by
        conv_lhs => rw [← e4]
        rw [map_mul]; rfl
      rw [this]; exact Matrix.rank_mul_le_left _ _
  rw [r1, r2] at hn
  have hc : lowerLeftBlock (resK κ) = R (lowerLeftBlock κ) := rfl
  have hdd : dBlk (resK κ') = R (dBlk κ') := rfl
  unfold iD
  rw [hc, hdd]
  omega

end GlobalTheory.CompanionTheory.Jp.RedRank

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReductionCorankEqRankLowerLeftStatement
open Matrix GlobalTheory.CompanionTheory.Jp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reduction_corank_eq_rank_lower_left : ∀ (O L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field L] [Algebra O L] [IsFractionRing O L]
    (n : ℕ) (ϖ : O), Irreducible ϖ → ∀ w : Lˣ, (w : L) = algebraMap O L ϖ →
    ∀ (κ : GL (Ix n) O) (h : GL (Ix n) (IsLocalRing.ResidueField O)), IsRed (O := O) w κ h →
      iD h = (lowerLeftBlock (resK κ)).rank := by
  first | exact @GlobalTheory.CompanionTheory.Jp.RedRank.iD_eq_rank | exact GlobalTheory.CompanionTheory.Jp.RedRank.iD_eq_rank | (intros; apply GlobalTheory.CompanionTheory.Jp.RedRank.iD_eq_rank <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WallLawOfSectionLaw
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WallLawOfSectionLaw
noncomputable section

open Filter Topology PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.RgEis

def cosMul {G : Type} [Group G] (P Γ : Subgroup G) (γ : Γ) : Cos P Γ ≃ Cos P Γ where
  toFun := Quotient.map (· * γ) (by
    intro x y h
    have h' : QuotientGroup.rightRel (P.subgroupOf Γ) x y := h
    show QuotientGroup.rightRel (P.subgroupOf Γ) (x * γ) (y * γ)
    rw [QuotientGroup.rightRel_apply] at h' ⊢
    simpa [mul_assoc] using h')
  invFun := Quotient.map (· * γ⁻¹) (by
    intro x y h
    have h' : QuotientGroup.rightRel (P.subgroupOf Γ) x y := h
    show QuotientGroup.rightRel (P.subgroupOf Γ) (x * γ⁻¹) (y * γ⁻¹)
    rw [QuotientGroup.rightRel_apply] at h' ⊢
    simpa [mul_assoc] using h')
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h x => simp [Quotient.map_mk]
  right_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h x => simp [Quotient.map_mk]

theorem rep_mk {G : Type} [Group G] {P Γ : Subgroup G} (x : Γ) :
    ∃ δ : G, δ ∈ Γ ∧ δ ∈ P ∧ rep (Quotient.mk _ x : Cos P Γ) = δ * x := by
  have h : QuotientGroup.rightRel (P.subgroupOf Γ) (Quotient.out (Quotient.mk _ x : Cos P Γ)) x :=
    Quotient.mk_out (s := QuotientGroup.rightRel (P.subgroupOf Γ)) x
  rw [QuotientGroup.rightRel_apply] at h
  refine ⟨((x * (Quotient.out (Quotient.mk _ x : Cos P Γ))⁻¹)⁻¹ : Γ), Subtype.property _, ?_, ?_⟩
  · exact (Subgroup.mem_subgroupOf.mp (inv_mem h))
  · simp [rep]

theorem tsum_rep_mul {G : Type} [Group G] {X : Type} [AddCommMonoid X] [TopologicalSpace X]
    {P Γ : Subgroup G} (F : G → X) (hF : ∀ δ ∈ Γ, δ ∈ P → ∀ x, F (δ * x) = F x) {γ : G} (hγ : γ ∈ Γ) (g : G) :
    ∑' q : Cos P Γ, F (rep q * (γ * g)) = ∑' q : Cos P Γ, F (rep q * g) := by
  rw [← Equiv.tsum_eq (cosMul P Γ ⟨γ, hγ⟩) (fun q : Cos P Γ => F (rep q * g))]
  refine tsum_congr fun q => ?_
  have hq : cosMul P Γ ⟨γ, hγ⟩ q = Quotient.mk _ (Quotient.out q * ⟨γ, hγ⟩) := by
    conv_lhs => rw [← Quotient.out_eq q]
    rfl
  obtain ⟨δ, h1, h2, h3⟩ := rep_mk (P := P) (Quotient.out q * (⟨γ, hγ⟩ : Γ))
  rw [hq, h3, mul_assoc δ, hF δ h1 h2]
  simp [rep, mul_assoc]

theorem norm_le_of_strip {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] {f : ℂ → X}
    (hf : Differentiable ℂ f) {a b B C : ℝ} (hab : a < b)
    (hB : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖f z‖ ≤ B) (ha : ∀ z : ℂ, z.re = a → ‖f z‖ ≤ C)
    (hb : ∀ z : ℂ, z.re = b → ‖f z‖ ≤ C) {z : ℂ} (h1 : a ≤ z.re) (h2 : z.re ≤ b) : ‖f z‖ ≤ C := by
  refine PhragmenLindelof.vertical_strip hf.diffContOnCl ?_ ha hb h1 h2
  refine ⟨0, div_pos Real.pi_pos (sub_pos.2 hab), 0, ?_⟩
  refine Asymptotics.IsBigO.of_bound B ?_
  filter_upwards [mem_inf_of_right (mem_principal_self _)] with w hw
  have := hB w hw.1.le hw.2.le
  simpa using this

theorem entire_eq {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] {f g : ℂ → X}
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) (R : ℝ) (h : ∀ z : ℂ, R < z.re → f z = g z) : f = g := by
  have hfa : AnalyticOnNhd ℂ f Set.univ := fun z _ => hf.analyticAt z
  have hga : AnalyticOnNhd ℂ g Set.univ := fun z _ => hg.analyticAt z
  refine hfa.eq_of_eventuallyEq hga (z₀ := ((R + 1 : ℝ) : ℂ)) ?_
  have hopen : IsOpen {z : ℂ | R < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hmem : ((R + 1 : ℝ) : ℂ) ∈ {z : ℂ | R < z.re} := by simp
  filter_upwards [hopen.mem_nhds hmem] with z hz using h z hz

theorem bound_left {A B p q n : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hp : 0 ≤ p) (hq : 0 ≤ q) (hn : 0 ≤ n) :
    A * p * n ≤ (A + B) * (p + q) * n := by
  refine mul_le_mul_of_nonneg_right ?_ hn
  nlinarith [mul_nonneg hA hq, mul_nonneg hB hp, mul_nonneg hB hq]

theorem bound_right {A B p q n : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hp : 0 ≤ p) (hq : 0 ≤ q) (hn : 0 ≤ n) :
    B * q * n ≤ (A + B) * (p + q) * n := by
  refine mul_le_mul_of_nonneg_right ?_ hn
  nlinarith [mul_nonneg hA hq, mul_nonneg hB hp, mul_nonneg hA hp]

section Sec

variable {G : Type} [Group G] [TopologicalSpace G] {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
  {Γ K P : Subgroup G} {c : G → ℂ} {ρ : K →* (W →L[ℂ] W)} {η : G → ℝ} {w : W}

theorem sec_left (hP : IsPar Γ K P c)
    (h : ∀ w ∈ secSp K P c ρ, ∀ p ∈ P, ∀ k : K, sec K P c ρ (p * k) w = c p • ρ k⁻¹ w)
    (hw : w ∈ secSp K P c ρ) {δ : G} (h1 : δ ∈ Γ) (h2 : δ ∈ P) (x : G) :
    sec K P c ρ (δ * x) w = sec K P c ρ x w := by
  obtain ⟨p, hp, k, hk, rfl⟩ := hP.iwa x
  have e := h w hw (δ * p) (mul_mem h2 hp) ⟨k, hk⟩
  have e' := h w hw p hp ⟨k, hk⟩
  simp only at e e'
  rw [← mul_assoc, e, e', hP.ch.mul δ h2 p hp, hP.ch.rat δ h1 h2, one_mul]

theorem sec_right (hP : IsPar Γ K P c)
    (h : ∀ w ∈ secSp K P c ρ, ∀ p ∈ P, ∀ k : K, sec K P c ρ (p * k) w = c p • ρ k⁻¹ w)
    (hw : w ∈ secSp K P c ρ) (x : G) (k : K) :
    sec K P c ρ (x * k) w = ρ k⁻¹ (sec K P c ρ x w) := by
  obtain ⟨p, hp, k', hk', rfl⟩ := hP.iwa x
  have e := h w hw p hp (⟨k', hk'⟩ * k)
  have e' := h w hw p hp ⟨k', hk'⟩
  simp only at e'
  have e2 : p * k' * (k : G) = p * (((⟨k', hk'⟩ : K) * k : K) : G) := by simp [mul_assoc]
  rw [e2, e, e', map_smul, mul_inv_rev, map_mul]
  rfl

theorem eis_mul_left (hP : IsPar Γ K P c)
    (h : ∀ w ∈ secSp K P c ρ, ∀ p ∈ P, ∀ k : K, sec K P c ρ (p * k) w = c p • ρ k⁻¹ w)
    (hη : IsHt Γ K P η) (hw : w ∈ secSp K P c ρ) (z : ℂ) {γ : G} (hγ : γ ∈ Γ) (g : G) :
    eis Γ K P c ρ (fun x => z * η x) (γ * g) w = eis Γ K P c ρ (fun x => z * η x) g w := by
  unfold eis
  refine tsum_rep_mul (fun x => Complex.exp (z * η x) • sec K P c ρ x w) ?_ hγ g
  intro δ h1 h2 x
  simp only [sec_left hP h hw h1 h2 x, hη.left δ h2 x, hη.rat δ h1 h2, zero_add]

theorem norm_term_le {M : ℝ} (hb : ∀ g (w : W), ‖sec K P c ρ g w‖ ≤ M * ‖w‖) {l : G → ℝ} {Λ : G → ℂ}
    (hΛ : ∀ x, (Λ x).re = l x) (x : G) (w : W) :
    ‖Complex.exp (Λ x) • sec K P c ρ x w‖ ≤ M * ‖w‖ * Real.exp (l x) := by
  rw [norm_smul, Complex.norm_exp, hΛ, mul_comm]
  exact mul_le_mul_of_nonneg_right (hb x w) (Real.exp_pos _).le

theorem summable_term [CompleteSpace W] {M : ℝ} (hb : ∀ g (w : W), ‖sec K P c ρ g w‖ ≤ M * ‖w‖) {l : G → ℝ}
    (hl : Conv Γ P l) {Λ : G → ℂ} (hΛ : ∀ x, (Λ x).re = l x) (g : G) (w : W) :
    Summable fun q : Cos P Γ => Complex.exp (Λ (rep q * g)) • sec K P c ρ (rep q * g) w :=
  Summable.of_norm_bounded ((hl g).mul_left (M * ‖w‖)) fun q => norm_term_le hb hΛ _ w

theorem norm_eis_le {M : ℝ} (hb : ∀ g (w : W), ‖sec K P c ρ g w‖ ≤ M * ‖w‖) {l : G → ℝ}
    (hl : Conv Γ P l) {Λ : G → ℂ} (hΛ : ∀ x, (Λ x).re = l x) (g : G) (w : W) :
    ‖eis Γ K P c ρ Λ g w‖ ≤ M * ‖w‖ * pos Γ P l g :=
  tsum_of_norm_bounded ((hl g).hasSum.mul_left (M * ‖w‖)) fun q => norm_term_le hb hΛ _ w

theorem pos_nonneg (l : G → ℝ) (g : G) : 0 ≤ pos Γ P l g :=
  tsum_nonneg fun _ => (Real.exp_pos _).le

theorem eis_mul_right [CompleteSpace W] (hP : IsPar Γ K P c)
    (h : ∀ w ∈ secSp K P c ρ, ∀ p ∈ P, ∀ k : K, sec K P c ρ (p * k) w = c p • ρ k⁻¹ w)
    {M : ℝ} (hb : ∀ g (w : W), ‖sec K P c ρ g w‖ ≤ M * ‖w‖)
    (hη : IsHt Γ K P η) (hw : w ∈ secSp K P c ρ) (z : ℂ) (hc : Conv Γ P fun g => z.re * η g) (g : G) (k : K) :
    eis Γ K P c ρ (fun x => z * η x) (g * k) w = ρ k⁻¹ (eis Γ K P c ρ (fun x => z * η x) g w) := by
  have hs := summable_term (Γ := Γ) (l := fun g => z.re * η g) (Λ := fun x => z * η x) hb hc
    (by intro x; simp) g w
  unfold eis
  rw [(ρ k⁻¹).map_tsum hs]
  refine tsum_congr fun q => ?_
  rw [← mul_assoc]
  beta_reduce
  rw [hη.right _ k k.2, sec_right hP h hw, map_smul]

end Sec

theorem wallLaw_of_secLaw : SecLaw → WallLaw := by
  intro hS
  intro G _ _ _ _ _ W _ _ _ K ρ hK hρ Γ P P' c η η' β L R D Op H hP hP' hη hη' hβ hW
  haveI : CompleteSpace W := FiniteDimensional.complete ℂ W
  obtain ⟨h1, -, Ms, hb⟩ := hS G W K ρ hK hρ Γ P c hP
  obtain ⟨-, -, Ms', hb'⟩ := hS G W K ρ hK hρ Γ P' c hP'
  have hdiff : ∀ (g : G) (w : L), Differentiable ℂ fun z => H z g w := fun g w =>
    (hW.hol g).clm_apply (differentiable_const _)
  refine ⟨?_, ?_, ?_⟩
  · intro z γ hγ g
    refine ContinuousLinearMap.ext fun w => ?_
    have e : (fun z => H z (γ * g) w) = fun z => H z g w := by
      refine entire_eq (hdiff _ w) (hdiff _ w) R fun z hz => ?_
      rw [hW.eqR z hz, hW.eqR z hz, eis_mul_left hP h1 hη (hW.le w.2) z hγ g]
    exact congrFun e z
  · intro z g k w
    have e : (fun z => H z (g * k) w) = fun z => ρ k⁻¹ (H z g w) := by
      refine entire_eq (hdiff _ w) ((ρ k⁻¹).differentiable.comp (hdiff g w)) R fun z hz => ?_
      rw [hW.eqR z hz, hW.eqR z hz, eis_mul_right hP h1 hb hη (hW.le w.2) z (hW.convR _ hz) g k, map_smul]
    exact congrFun e z
  · intro a b ha hb₀
    obtain ⟨MD, hD⟩ := hW.dEnt.2 a a
    obtain ⟨MO, hO⟩ := hW.op.2 b b hb₀
    refine ⟨|MD| * |Ms| + |Ms'| * |MO|, ?_⟩
    intro z hz1 hz2 g
    have hab : b < a := by linarith [hW.pos]
    obtain ⟨U, hU, B, hB⟩ := hW.bdd b a g
    have hg : g ∈ U := mem_of_mem_nhds hU
    have hp := pos_nonneg (Γ := Γ) (P := P) (fun x => a * η x) g
    have hq := pos_nonneg (Γ := Γ) (P := P') (fun x => β x - b * η' x) g
    have hA : 0 ≤ |MD| * |Ms| := by positivity
    have hB' : 0 ≤ |Ms'| * |MO| := by positivity
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
    refine norm_le_of_strip (f := fun z => H z g w) (B := B * ‖w‖) (hdiff g w) hab ?_ ?_ ?_ hz1 hz2
    · intro u hu1 hu2
      exact ((H u g).le_opNorm w).trans (mul_le_mul_of_nonneg_right (hB u hu1 hu2 g hg) (norm_nonneg _))
    · intro u hu
      have hO' := hO u hu.ge hu.le
      have hu' : u.re < -R := by rw [hu]; exact hb₀
      have e2 := norm_eis_le (Γ := Γ) hb' (l := fun x => β x - b * η' x) (hW.convL b hb₀)
        (Λ := fun x => (β x : ℂ) - u * η' x) (by intro x; simp [hu]) g (Op u w : W)
      have e3 : ‖(Op u w : W)‖ ≤ |MO| * ‖w‖ := by
        have : ‖(Op u w : W)‖ = ‖Op u w‖ := rfl
        rw [this]
        exact ((Op u).le_opNorm w).trans
          (mul_le_mul_of_nonneg_right (hO'.trans (le_abs_self _)) (norm_nonneg _))
      show ‖H u g w‖ ≤ _
      rw [hW.eqL u hu' g w]
      calc _ ≤ Ms' * ‖(Op u w : W)‖ * _ := e2
        _ ≤ |Ms'| * (|MO| * ‖w‖) * _ := by
            refine mul_le_mul_of_nonneg_right ?_ hq
            exact mul_le_mul (le_abs_self _) e3 (norm_nonneg _) (abs_nonneg _)
        _ = |Ms'| * |MO| * _ * ‖w‖ := by ring
        _ ≤ _ := bound_right hA hB' hp hq (norm_nonneg _)
    · intro u hu
      have hD' := hD u hu.ge hu.le
      have hu' : R < u.re := by rw [hu]; exact ha
      have e2 := norm_eis_le (Γ := Γ) hb (l := fun x => a * η x) (hW.convR a ha)
        (Λ := fun x => u * η x) (by intro x; simp [hu]) g (w : W)
      show ‖H u g w‖ ≤ _
      rw [hW.eqR u hu' g w, norm_smul]
      calc _ ≤ |MD| * (|Ms| * ‖w‖ * _) := by
            refine mul_le_mul (hD'.trans (le_abs_self _)) (e2.trans ?_) (norm_nonneg _) (abs_nonneg _)
            refine mul_le_mul_of_nonneg_right ?_ hp
            exact mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
        _ = |MD| * |Ms| * _ * ‖w‖ := by
            have : ‖w‖ = ‖(w : W)‖ := rfl
            ring
        _ ≤ _ := bound_left hA hB' hp hq (norm_nonneg _)

end GlobalTheory.CompanionTheory.RgEis
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WallLawOfSectionLawStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wall_law_of_section_law : PositivityTheory.RgEis.SecLaw → PositivityTheory.RgEis.WallLaw := by
  first | exact @GlobalTheory.CompanionTheory.RgEis.wallLaw_of_secLaw | exact GlobalTheory.CompanionTheory.RgEis.wallLaw_of_secLaw | (intros; apply GlobalTheory.CompanionTheory.RgEis.wallLaw_of_secLaw <;> assumption)
end
end
