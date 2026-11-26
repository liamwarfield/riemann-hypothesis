module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.WeilQuotientGlobalAssumptions

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.SiegelMeasureDefinition
noncomputable section

open MeasureTheory Measure Topology Set
open scoped ENNReal Pointwise

namespace QPK

section SM

variable {G : Type} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

lemma eq_one_of_eq_mul {c x : ℝ≥0∞} (h0 : x ≠ 0) (ht : x ≠ ⊤) (h : x = c * x) : c = 1 := by
  have h' : x * c = x * 1 := by rw [mul_one, mul_comm]; exact h.symm
  exact (ENNReal.mul_right_inj h0 ht).mp h'

lemma eq_one_of_mul_self {c : ℝ≥0∞} (h : c * c = 1) : c = 1 := by
  rcases lt_trichotomy c 1 with hlt | heq | hgt
  · have h1 : c * c ≤ c * 1 := by gcongr
    rw [mul_one] at h1
    exact absurd h (ne_of_lt (lt_of_le_of_lt h1 hlt))
  · exact heq
  · have h1 : c * 1 ≤ c * c := by gcongr
    rw [mul_one] at h1
    exact absurd h (ne_of_gt (lt_of_lt_of_le hgt h1))

lemma exists_pos_fin (μ : Measure G) [SigmaFinite μ] (h0 : μ ≠ 0) :
    ∃ A : Set G, μ A ≠ 0 ∧ μ A ≠ ⊤ := by
  by_contra hc
  push_neg at hc
  apply h0
  rw [← Measure.measure_univ_eq_zero, ← iUnion_spanningSets μ]
  apply measure_iUnion_null
  intro n
  by_contra hn
  exact (measure_spanningSets_lt_top μ n).ne (hc _ hn)

lemma map_inv_eq_self (K : Set G) (hc : IsClosed K) (hK : IsGrp K) (μ : Measure G)
    (hμ : InvOn μ K) (hR : ∀ s ∈ K, μ.map (fun x => x * s) = μ) :
    μ.map (fun x => x⁻¹) = μ := by
  obtain ⟨hsf, hne, hKc, hL⟩ := hμ
  have hmeas : Measurable (fun x : G => x⁻¹) := measurable_inv
  have hKm : MeasurableSet K := hc.measurableSet
  have hpre : (fun x : G => x⁻¹) ⁻¹' K = K := by
    ext x
    simp only [Set.mem_preimage]
    constructor
    · intro h
      have h2 := hK.2.2 _ h
      rwa [inv_inv] at h2
    · intro h
      exact hK.2.2 _ h
  have hpreC : (fun x : G => x⁻¹) ⁻¹' Kᶜ = Kᶜ := by
    rw [Set.preimage_compl, hpre]
  have hν : InvOn (μ.map (fun x => x⁻¹)) K := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact (MeasurableEquiv.inv G).sigmaFinite_map
    · exact (Measure.map_ne_zero_iff hmeas.aemeasurable).2 hne
    · rw [Measure.map_apply hmeas hKm.compl, hpreC, hKc]
    · intro t ht
      rw [Measure.map_map (measurable_const_mul t) hmeas]
      have e : (fun x : G => t * x) ∘ (fun x => x⁻¹) = (fun x => x⁻¹) ∘ (fun x => x * t⁻¹) := by
        funext x
        simp [mul_inv_rev]
      rw [e, ← Measure.map_map hmeas (measurable_mul_const t⁻¹), hR t⁻¹ (hK.2.2 t ht)]
  obtain ⟨c, hc0, hct, hceq⟩ := haar_measure_uniqueness G K hc hK _ _ hν ⟨hsf, hne, hKc, hL⟩
  have hinv2 : (μ.map (fun x : G => x⁻¹)).map (fun x => x⁻¹) = μ := by
    rw [Measure.map_map hmeas hmeas]
    have e : (fun x : G => x⁻¹) ∘ (fun x => x⁻¹) = id := by
      funext x
      simp
    rw [e, Measure.map_id]
  have hμc : μ = (c * c) • μ := by
    have h2 := hinv2
    rw [hceq, Measure.map_smul c hmeas.aemeasurable, hceq, smul_smul] at h2
    exact h2.symm
  haveI := hsf
  obtain ⟨A, hA0, hAt⟩ := exists_pos_fin μ hne
  have h3 : μ A = (c * c) * μ A := by
    have h4 := congrArg (fun m : Measure G => m A) hμc
    simpa only [Measure.smul_apply, smul_eq_mul] using h4
  have hcc : c * c = 1 := eq_one_of_eq_mul hA0 hAt h3
  rw [hceq, eq_one_of_mul_self hcc, one_smul]

lemma map_mul_right_eq_self (K : Set G) (hc : IsClosed K) (hK : IsGrp K) (μ : Measure G)
    (hμ : InvOn μ K) (hfin : μ K ≠ ⊤) (s : G) (hs : s ∈ K) :
    μ.map (fun x => x * s) = μ := by
  obtain ⟨hsf, hne, hKc, hL⟩ := hμ
  have hmeas : Measurable (fun x : G => x * s) := measurable_mul_const s
  have hKm : MeasurableSet K := hc.measurableSet
  have hpre : (fun x : G => x * s) ⁻¹' K = K := by
    ext x
    simp only [Set.mem_preimage]
    constructor
    · intro h
      have h2 := hK.2.1 _ h _ (hK.2.2 s hs)
      rwa [mul_assoc, mul_inv_cancel, mul_one] at h2
    · intro h
      exact hK.2.1 _ h _ hs
  have hpreC : (fun x : G => x * s) ⁻¹' Kᶜ = Kᶜ := by
    rw [Set.preimage_compl, hpre]
  have hν : InvOn (μ.map (fun x => x * s)) K := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact (MeasurableEquiv.mulRight s).sigmaFinite_map
    · exact (Measure.map_ne_zero_iff hmeas.aemeasurable).2 hne
    · rw [Measure.map_apply hmeas hKm.compl, hpreC, hKc]
    · intro t ht
      rw [Measure.map_map (measurable_const_mul t) hmeas]
      have e : (fun x : G => t * x) ∘ (fun x => x * s) = (fun x => x * s) ∘ (fun x => t * x) := by
        funext x
        simp [mul_assoc]
      rw [e, ← Measure.map_map hmeas (measurable_const_mul t), hL t ht]
  obtain ⟨c, hc0, hct, hceq⟩ := haar_measure_uniqueness G K hc hK _ _ hν ⟨hsf, hne, hKc, hL⟩
  have hμK : μ K ≠ 0 := by
    intro h0
    apply hne
    rw [← Measure.measure_univ_eq_zero, ← Set.union_compl_self K]
    exact measure_union_null h0 hKc
  have h1 : μ K = c * μ K := by
    have h2 := congrArg (fun m : Measure G => m K) hceq
    simp only [Measure.smul_apply, smul_eq_mul] at h2
    rwa [Measure.map_apply hmeas hKm, hpre] at h2
  have hc1 : c = 1 := eq_one_of_eq_mul hμK hfin h1
  rw [hceq, hc1, one_smul]

lemma map_mulSwap_eq (Q : Measure (G × G)) (g : G × G → G × G) (hg : MeasurePreserving g Q Q)
    (f : G → G) (hf : Measurable f) (h : ∀ p : G × G, f (p.2 * p.1) = (g p).2 * (g p).1) :
    (Q.map (fun p : G × G => p.2 * p.1)).map f = Q.map (fun p : G × G => p.2 * p.1) := by
  have hm : Measurable (fun p : G × G => p.2 * p.1) := measurable_snd.mul measurable_fst
  rw [Measure.map_map hf hm]
  have e : f ∘ (fun p : G × G => p.2 * p.1) = (fun p : G × G => p.2 * p.1) ∘ g := funext h
  rw [e, ← Measure.map_map hm hg.measurable, hg.map_eq]

end SM

theorem siegel_measure_definition : SMeas := by
  intro G _ _ _ _ _ _ _ _ N H hNc hHc hN hH hnorm hU μN μH hμN hfN hpN hμH hfH hpH hconj
  have : SigmaFinite μN := hμN.1
  have : SigmaFinite μH := hμH.1
  have : IsFiniteMeasureOnCompacts μN := hfN
  have : IsFiniteMeasureOnCompacts μH := hfH
  have hHcl : IsClosed H := hHc.isClosed
  have hRH : ∀ s ∈ H, μH.map (fun x => x * s) = μH := fun s hs =>
    map_mul_right_eq_self H hHcl hH μH hμH hHc.measure_lt_top.ne s hs
  have hRN : ∀ s ∈ N, μN.map (fun x => x * s) = μN :=
    hU μN hμN.1 hμN.2.1 hμN.2.2.1 hμN.2.2.2
  have hIH := map_inv_eq_self H hHcl hH μH hμH hRH
  have hIN := map_inv_eq_self N hNc hN μN hμN hRN
  have hm' : Measurable (fun p : G × G => p.2 * p.1) := measurable_snd.mul measurable_fst
  have hM : mulMap μN μH = (μH.prod μN).map (fun p : G × G => p.2 * p.1) := by
    have hm1 : Measurable (fun p : G × G => p.1 * p.2) := measurable_fst.mul measurable_snd
    unfold mulMap
    rw [← Measure.prod_swap (μ := μH) (ν := μN), Measure.map_map hm1 measurable_swap]
    rfl
  have hHae : ∀ᵐ k ∂μH, k ∈ H := by
    rw [ae_iff]
    exact hμH.2.2.1
  have hNae : ∀ᵐ n ∂μN, n ∈ N := by
    rw [ae_iff]
    exact hμN.2.2.1
  have hae : ∀ᵐ p ∂(μH.prod μN), p ∈ H ×ˢ N :=
    ((Measure.quasiMeasurePreserving_fst.ae hHae).and
      (Measure.quasiMeasurePreserving_snd.ae hNae)).mono fun p hp => Set.mem_prod.2 hp
  have hnull : (μH.prod μN) (H ×ˢ N)ᶜ = 0 := by
    rw [ae_iff] at hae
    exact hae
  have hSeq : prodSet N H = N * H := by
    ext x
    simp only [prodSet, Set.mem_mul, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨m, hm, h, hh, rfl⟩
      exact ⟨m, hm, h, hh, rfl⟩
    · rintro ⟨m, hm, h, hh, rfl⟩
      exact ⟨m, hm, h, hh, rfl⟩
  have hScl : IsClosed (prodSet N H) := by
    rw [hSeq]
    exact hNc.mul_right_of_isCompact hHc

  have hfin : IsFiniteMeasureOnCompacts (mulMap μN μH) := by
    refine ⟨fun L hL => ?_⟩
    rw [hM, Measure.map_apply hm' hL.isClosed.measurableSet]
    have hC : IsCompact (L * H⁻¹) := hL.mul hHc.inv
    have hsub : (fun p : G × G => p.2 * p.1) ⁻¹' L ⊆ (H ×ˢ (L * H⁻¹)) ∪ (H ×ˢ N)ᶜ := by
      intro p hp
      by_cases hp2 : p ∈ H ×ˢ N
      · left
        refine ⟨hp2.1, ?_⟩
        exact Set.mem_mul.2 ⟨p.2 * p.1, hp, p.1⁻¹, Set.inv_mem_inv.2 hp2.1, by group⟩
      · right
        exact hp2
    calc (μH.prod μN) ((fun p : G × G => p.2 * p.1) ⁻¹' L)
        ≤ (μH.prod μN) ((H ×ˢ (L * H⁻¹)) ∪ (H ×ˢ N)ᶜ) := measure_mono hsub
      _ ≤ (μH.prod μN) (H ×ˢ (L * H⁻¹)) + (μH.prod μN) (H ×ˢ N)ᶜ := measure_union_le _ _
      _ = μH H * μN (L * H⁻¹) := by rw [hnull, add_zero, Measure.prod_prod]
      _ < ⊤ := ENNReal.mul_lt_top hHc.measure_lt_top hC.measure_lt_top

  have hpos : PosOn (mulMap μN μH) (prodSet N H) := by
    rintro U hUo ⟨x, hxU, a, ha, b, hb, hx⟩
    rw [hM, Measure.map_apply hm' hUo.measurableSet]
    have hopen : IsOpen ((fun p : G × G => p.2 * p.1) ⁻¹' U) :=
      hUo.preimage (continuous_snd.mul continuous_fst)
    have hmem : (b, a) ∈ (fun p : G × G => p.2 * p.1) ⁻¹' U := by
      show a * b ∈ U
      rw [← hx]
      exact hxU
    obtain ⟨V₁, V₂, hV₁, hV₂, hb1, ha2, hsub⟩ := isOpen_prod_iff.1 hopen b a hmem
    intro h0
    have h1 : (μH.prod μN) (V₁ ×ˢ V₂) = 0 := measure_mono_null hsub h0
    rw [Measure.prod_prod] at h1
    rcases mul_eq_zero.1 h1 with h | h
    · exact hpH V₁ hV₁ ⟨b, hb1, hb⟩ h
    · exact hpN V₂ hV₂ ⟨a, ha2, ha⟩ h
  have hne : mulMap μN μH ≠ 0 := by
    have h1 := hpos univ isOpen_univ ⟨1, trivial, 1, hN.1, 1, hH.1, (mul_one 1).symm⟩
    intro h
    rw [h] at h1
    exact h1 rfl
  have hconc : mulMap μN μH (prodSet N H)ᶜ = 0 := by
    rw [hM, Measure.map_apply hm' hScl.measurableSet.compl]
    refine measure_mono_null ?_ hnull
    intro p hp
    simp only [mem_preimage, mem_compl_iff] at hp
    rw [mem_compl_iff]
    rintro ⟨h1, h2⟩
    exact hp ⟨p.2, h2, p.1, h1, rfl⟩

  have hleft : ∀ s ∈ prodSet N H, (mulMap μN μH).map (fun x => s * x) = mulMap μN μH := by
    rintro s ⟨a, ha, b, hb, rfl⟩
    have hg : MeasurePreserving (fun p : G × G => (b * p.1, a * (b * p.2 * b⁻¹)))
        (μH.prod μN) (μH.prod μN) := by
      refine MeasurePreserving.skew_product (f := fun x => b * x)
        (g := fun _ n => a * (b * n * b⁻¹)) ⟨measurable_const_mul b, hμH.2.2.2 b hb⟩
        (((measurable_snd.const_mul b).mul_const b⁻¹).const_mul a) (ae_of_all _ fun _ => ?_)
      have hcj : Measurable (fun x : G => b * x * b⁻¹) := (measurable_const_mul b).mul_const b⁻¹
      have e : μN.map (fun n => a * (b * n * b⁻¹)) =
          (μN.map (fun x => b * x * b⁻¹)).map (fun x => a * x) := by
        rw [Measure.map_map (measurable_const_mul a) hcj]
        rfl
      show μN.map (fun n => a * (b * n * b⁻¹)) = μN
      rw [e, hconj b hb, hμN.2.2.2 a ha]
    rw [hM]
    exact map_mulSwap_eq _ _ hg _ (measurable_const_mul _) (fun p => by simp only; group)

  have hright : ∀ s ∈ prodSet N H, (mulMap μN μH).map (fun x => x * s) = mulMap μN μH := by
    rintro s ⟨a, ha, b, hb, rfl⟩
    have hg : MeasurePreserving (fun p : G × G => (p.1 * b, p.2 * (p.1 * a * p.1⁻¹)))
        (μH.prod μN) (μH.prod μN) := by
      refine MeasurePreserving.skew_product (f := fun x => x * b)
        (g := fun k n => n * (k * a * k⁻¹)) ⟨measurable_mul_const b, hRH b hb⟩
        (measurable_snd.mul ((measurable_fst.mul_const a).mul measurable_fst.inv))
        (hHae.mono fun k hk => ?_)
      exact hRN _ (hnorm k hk a ha)
    rw [hM]
    exact map_mulSwap_eq _ _ hg _ (measurable_mul_const _) (fun p => by simp only; group)

  have hinv : (mulMap μN μH).map (fun x => x⁻¹) = mulMap μN μH := by
    have hg : MeasurePreserving (fun p : G × G => (p.1⁻¹, p.1⁻¹ * p.2⁻¹ * p.1))
        (μH.prod μN) (μH.prod μN) := by
      refine MeasurePreserving.skew_product (f := fun x => x⁻¹)
        (g := fun k n => k⁻¹ * n⁻¹ * k) ⟨measurable_inv, hIH⟩
        ((measurable_fst.inv.mul measurable_snd.inv).mul measurable_fst)
        (hHae.mono fun k hk => ?_)
      have hcj : Measurable (fun x : G => k⁻¹ * x * k⁻¹⁻¹) :=
        (measurable_const_mul _).mul_const _
      have e : μN.map (fun n => k⁻¹ * n⁻¹ * k) =
          (μN.map (fun x => x⁻¹)).map (fun x => k⁻¹ * x * k⁻¹⁻¹) := by
        rw [Measure.map_map hcj measurable_inv]
        simp only [Function.comp_def, inv_inv]
      show μN.map (fun n => k⁻¹ * n⁻¹ * k) = μN
      rw [e, hIN, hconj _ (hH.2.2 k hk)]
    rw [hM]
    exact map_mulSwap_eq _ _ hg _ measurable_inv (fun p => by simp only; group)
  have := hfin
  exact ⟨⟨inferInstance, hne, hconc, hleft⟩, hfin, hpos, hright, hinv⟩

end QPK
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.QuotProdKOf
namespace QPK

theorem quotProdK_of (hA : GlobAsm) (hU : HaarUniq) (hL : LocPack) : PI.QuotProdK.QuotProdK :=
  hA hU hL

end QPK
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.BruhatDecomposition
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace QPK

namespace Bru

variable {G : Type} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

theorem exists_cover :
    ∃ K : ℕ → Set G, (∀ n, IsCompact (K n)) ∧ ∀ x, ∃ n, x ∈ interior (K n) := by
  let K := CompactExhaustion.choice G
  refine ⟨K, fun n => K.isCompact n, fun x => ?_⟩
  obtain ⟨n, hn⟩ := K.exists_mem x
  exact ⟨n + 1, K.subset_interior_succ n hn⟩

def gf (μ : Measure G) (K : ℕ → Set G) (n : ℕ) (x : G) : ℝ≥0∞ :=
  μ ((fun s => s * x) ⁻¹' K n)

def Eset (μ : Measure G) (K : ℕ → Set G) (n : ℕ) : Set G :=
  {x | gf μ K n x ≠ 0 ∧ ∀ k < n, gf μ K k x = 0}

def bf (μ : Measure G) (K : ℕ → Set G) (x : G) : ℝ≥0∞ :=
  ∑' n, (Eset μ K n).indicator (fun y => (K n).indicator 1 y * (gf μ K n y)⁻¹) x

theorem gf_meas (μ : Measure G) [SFinite μ] (K : ℕ → Set G) (hK : ∀ n, IsClosed (K n)) (n : ℕ) :
    Measurable (gf μ K n) := by
  have hs : MeasurableSet ((fun p : G × G => p.2 * p.1) ⁻¹' K n) :=
    (hK n).measurableSet.preimage (measurable_snd.mul measurable_fst)
  first
  | exact measurable_measure_prodMk_left hs
  | exact measurable_measure_prod_mk_left hs

theorem gf_lt_top (μ : Measure G) [IsFiniteMeasureOnCompacts μ] (K : ℕ → Set G)
    (hK : ∀ n, IsCompact (K n)) (n : ℕ) (x : G) : gf μ K n x < ⊤ := by
  have h : IsCompact ((fun s => s * x) ⁻¹' K n) :=
    (Homeomorph.mulRight x).isCompact_preimage.2 (hK n)
  exact h.measure_lt_top

theorem gf_inv (μ : Measure G) (K : ℕ → Set G) (hK : ∀ n, IsClosed (K n)) (S : Set G)
    (hr : ∀ s ∈ S, μ.map (fun x => x * s) = μ) (n : ℕ) {t : G} (ht : t ∈ S) (x : G) :
    gf μ K n (t * x) = gf μ K n x := by
  have hm : MeasurableSet ((fun s => s * x) ⁻¹' K n) :=
    (hK n).measurableSet.preimage (measurable_mul_const x)
  show μ ((fun s => s * (t * x)) ⁻¹' K n) = μ ((fun s => s * x) ⁻¹' K n)
  calc μ ((fun s => s * (t * x)) ⁻¹' K n)
      = μ.map (fun s => s * t) ((fun s => s * x) ⁻¹' K n) := by
        rw [Measure.map_apply (measurable_mul_const t) hm]
        congr 1
        ext s
        simp [mul_assoc]
    _ = μ ((fun s => s * x) ⁻¹' K n) := by rw [hr t ht]

theorem gf_pos (μ : Measure G) (K : ℕ → Set G) (S : Set G) (h1 : (1 : G) ∈ S)
    (hpos : PosOn μ S) (n : ℕ) {x : G} (hx : x ∈ interior (K n)) : gf μ K n x ≠ 0 := by
  intro h0
  have hU : IsOpen ((fun s => s * x) ⁻¹' interior (K n)) :=
    isOpen_interior.preimage (continuous_mul_const x)
  have hne := hpos _ hU ⟨1, by simpa using hx, h1⟩
  exact hne (measure_mono_null (Set.preimage_mono interior_subset) h0)

theorem Eset_meas (μ : Measure G) [SFinite μ] (K : ℕ → Set G) (hK : ∀ n, IsClosed (K n))
    (n : ℕ) : MeasurableSet (Eset μ K n) := by
  have h1 : MeasurableSet {x | gf μ K n x ≠ 0} :=
    (gf_meas μ K hK n) (measurableSet_singleton 0).compl
  have h2 : MeasurableSet {x | ∀ k < n, gf μ K k x = 0} := by
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
      (gf_meas μ K hK k) (measurableSet_singleton 0)
  exact h1.inter h2

theorem Eset_unique {μ : Measure G} {K : ℕ → Set G} {x : G} {n m : ℕ}
    (hn : x ∈ Eset μ K n) (hm : x ∈ Eset μ K m) : n = m := by
  rcases lt_trichotomy n m with h | h | h
  · exact absurd (hm.2 n h) hn.1
  · exact h
  · exact absurd (hn.2 m h) hm.1

theorem Eset_exists (μ : Measure G) (K : ℕ → Set G) (x : G) (h : ∃ n, gf μ K n x ≠ 0) :
    ∃ n, x ∈ Eset μ K n := by
  classical
  refine ⟨Nat.find h, Nat.find_spec h, fun k hk => ?_⟩
  by_contra hc
  exact Nat.find_min h hk hc

theorem Eset_inv (μ : Measure G) (K : ℕ → Set G) (hK : ∀ n, IsClosed (K n)) (S : Set G)
    (hr : ∀ s ∈ S, μ.map (fun x => x * s) = μ) (n : ℕ) {t : G} (ht : t ∈ S) (x : G) :
    t * x ∈ Eset μ K n ↔ x ∈ Eset μ K n := by
  have h : ∀ k, gf μ K k (t * x) = gf μ K k x := fun k => gf_inv μ K hK S hr k ht x
  simp only [Eset, Set.mem_setOf_eq, h]

theorem bf_meas (μ : Measure G) [SFinite μ] (K : ℕ → Set G) (hK : ∀ n, IsClosed (K n)) :
    Measurable (bf μ K) := by
  unfold bf
  refine Measurable.tsum fun n => ?_
  refine Measurable.indicator ?_ (Eset_meas μ K hK n)
  exact (measurable_one.indicator (hK n).measurableSet).mul (gf_meas μ K hK n).inv

end Bru

open Bru in
theorem bruhat_decomposition' : Bruhat := by
  intro G _ _ _ _ _ _ _ _ S hS hG μ hinv hfin hpos hr
  obtain ⟨hsf, -, hSc, -⟩ := hinv
  haveI := hsf
  haveI := hfin
  obtain ⟨K, hKc, hKx⟩ := exists_cover (G := G)
  have hKcl : ∀ n, IsClosed (K n) := fun n => (hKc n).isClosed
  refine ⟨bf μ K, bf_meas μ K hKcl, fun x => ?_⟩
  obtain ⟨m, hm⟩ := hKx x
  obtain ⟨n, hn⟩ := Eset_exists μ K x ⟨m, gf_pos μ K S hG.1 hpos m hm⟩
  have hS' : ∀ᵐ s ∂μ, s ∈ S := ae_iff.2 hSc
  have hae : ∀ᵐ s ∂μ, bf μ K (s * x) = (K n).indicator 1 (s * x) * (gf μ K n x)⁻¹ := by
    filter_upwards [hS'] with s hs
    unfold bf
    rw [tsum_eq_single n]
    · rw [Set.indicator_of_mem ((Eset_inv μ K hKcl S hr n hs x).2 hn)]
      simp only [gf_inv μ K hKcl S hr n hs x]
    · intro k hk
      have hk' : s * x ∉ Eset μ K k := fun hk' =>
        hk (Eset_unique ((Eset_inv μ K hKcl S hr k hs x).1 hk') hn)
      first
      | exact Set.indicator_of_notMem hk' _
      | exact Set.indicator_of_not_mem hk' _
  have hmeas : Measurable fun s => (K n).indicator (1 : G → ℝ≥0∞) (s * x) :=
    (measurable_one.indicator (hKcl n).measurableSet).comp (measurable_mul_const x)
  have e1 : (fun s => (K n).indicator (1 : G → ℝ≥0∞) (s * x)) =
      ((fun s => s * x) ⁻¹' K n).indicator 1 := by
    ext s
    first
    | rfl
    | simp [Set.indicator_apply]
  rw [lintegral_congr_ae hae, lintegral_mul_const _ hmeas, e1,
    lintegral_indicator_one ((hKcl n).measurableSet.preimage (measurable_mul_const x))]
  exact ENNReal.mul_inv_cancel hn.1 (gf_lt_top μ K hKc n x).ne

end QPK
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.ProdSetIsClosed
noncomputable section

open MeasureTheory Set
open scoped ENNReal Pointwise

namespace QPK

section
variable {G : Type} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]

theorem prodSet_eq_mul (N H : Set G) : prodSet N H = N * H := by
  ext s
  simp only [prodSet, Set.mem_setOf_eq, Set.mem_mul]
  constructor
  · rintro ⟨m, hm, h, hh, rfl⟩
    exact ⟨m, hm, h, hh, rfl⟩
  · rintro ⟨m, hm, h, hh, rfl⟩
    exact ⟨m, hm, h, hh, rfl⟩

theorem prodSet_isClosed {N H : Set G} (hN : IsClosed N) (hH : IsCompact H) :
    IsClosed (prodSet N H) := by
  rw [prodSet_eq_mul]
  first
    | exact hN.mul_isCompact hH
    | exact IsClosed.mul_isCompact hN hH
    | exact hN.mul_right_of_isCompact hH
    | exact IsClosed.mul_right_of_isCompact hN hH
    | exact hN.mul_isCompact_right hH
    | exact (hN.smul_left_of_isCompact hH)

theorem prodSet_isGrp {N H : Set G} (hN : IsGrp N) (hH : IsGrp H)
    (hnorm : ∀ h ∈ H, ∀ m ∈ N, h * m * h⁻¹ ∈ N) : IsGrp (prodSet N H) := by
  obtain ⟨n1, nmul, ninv⟩ := hN
  obtain ⟨h1, hmul, hinv⟩ := hH
  refine ⟨⟨1, n1, 1, h1, (mul_one 1).symm⟩, ?_, ?_⟩
  · rintro _ ⟨m, hm, h, hh, rfl⟩ _ ⟨m', hm', h', hh', rfl⟩
    refine ⟨m * (h * m' * h⁻¹), nmul _ hm _ (hnorm h hh m' hm'), h * h', hmul _ hh _ hh', ?_⟩
    first
      | group
      | simp [mul_assoc]
  · rintro _ ⟨m, hm, h, hh, rfl⟩
    refine ⟨h⁻¹ * m⁻¹ * h⁻¹⁻¹, hnorm _ (hinv _ hh) _ (ninv _ hm), h⁻¹, hinv _ hh, ?_⟩
    first
      | group
      | simp [mul_assoc]
end

theorem locPack_of (hE : HaarExist) (hC : ConjInv) (hS : SMeas) (hB : Bruhat) (hW : LocWeil) :
    LocPack := by
  intro G _ _ _ _ _ _ _ _ muG _ N H hN hH gN gH hnorm hR
  obtain ⟨μN, hNinv, hNf, hNpos⟩ := hE G N hN gN
  obtain ⟨μH, hHinv, hHf, hHpos⟩ := hE G H hH.isClosed gH
  have hconj := hC G N H hN hH gN gH hnorm μN hNinv hNf hNpos
  obtain ⟨hPinv, hPf, hPpos, hPright, hPinvol⟩ :=
    hS G N H hN hH gN gH hnorm hR μN μH hNinv hNf hNpos hHinv hHf hHpos hconj
  obtain ⟨β, hβm, hβ⟩ := hB G (prodSet N H) (prodSet_isClosed hN hH) (prodSet_isGrp gN gH hnorm)
    (mulMap μN μH) hPinv hPf hPpos hPright
  refine ⟨μN, μH, β, hNinv, hHinv, hPinv, hβm, hβ, ?_⟩
  intro F hF
  haveI := hPf
  have hsf : SigmaFinite (mulMap μN μH) := by
    first
      | exact inferInstance
      | exact MeasureTheory.sigmaFinite_of_isFiniteMeasureOnCompacts _
  exact hW G muG (mulMap μN μH) hsf hPinvol β hβm hβ F hF

end QPK
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.LocalWeilRepresentation
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace QPK

theorem local_weil_representation : LocWeil := by
  intro G _ _ _ _ _ _ _ _ muG _ μ _ hinv β hβ hβ1 F hF
  have hFm : Measurable (fun p : G × G => F (p.1 * p.2)) := hF.comp measurable_mul
  have hin : Measurable (fun x => ∫⁻ s, F (s * x) ∂μ) := hFm.lintegral_prod_left'
  rw [lintegral_withDensity_eq_lintegral_mul _ hβ hin]
  simp only [Pi.mul_apply]
  have step1 : ∀ x, β x * ∫⁻ s, F (s * x) ∂μ = ∫⁻ s, β x * F (s * x) ∂μ := fun x =>
    (lintegral_const_mul (β x) (hF.comp (measurable_id.mul_const x))).symm
  simp_rw [step1]
  rw [lintegral_lintegral_swap (μ := muG) (ν := μ) (f := fun x s => β x * F (s * x))
    ((hβ.comp measurable_fst).mul (hF.comp (measurable_snd.mul measurable_fst))).aemeasurable]
  have step2 : ∀ s, ∫⁻ x, β x * F (s * x) ∂muG = ∫⁻ x, β (s⁻¹ * x) * F x ∂muG := by
    intro s
    have key := lintegral_mul_left_eq_self (μ := muG) (fun x => β (s⁻¹ * x) * F x) s
    simp only [inv_mul_cancel_left] at key
    exact key
  simp_rw [step2]
  rw [lintegral_lintegral_swap (μ := μ) (ν := muG) (f := fun s x => β (s⁻¹ * x) * F x)
    ((hβ.comp (measurable_fst.inv.mul measurable_snd)).mul (hF.comp measurable_snd)).aemeasurable]
  have step3 : ∀ x, ∫⁻ s, β (s⁻¹ * x) * F x ∂μ = F x := by
    intro x
    rw [lintegral_mul_const (F x) (f := fun s => β (s⁻¹ * x)) (hβ.comp (measurable_inv.mul_const x))]
    have hsym : ∫⁻ s, β (s⁻¹ * x) ∂μ = ∫⁻ s, β (s * x) ∂μ := by
      conv_rhs => rw [← hinv]
      rw [lintegral_map (f := fun s => β (s * x)) (hβ.comp (measurable_id.mul_const x)) measurable_inv]
    rw [hsym, hβ1 x, one_mul]
  simp_rw [step3]

end QPK
end
end

theorem quotient_product_compact : PI.QuotProdK.QuotProdK :=
  QPK.quotProdK_of QPK.weil_quotient_global_assumptions QPK.haar_measure_uniqueness
    (QPK.locPack_of QPK.haar_measure_existence QPK.conjugation_invariant_measure QPK.siegel_measure_definition QPK.bruhat_decomposition'
      QPK.local_weil_representation)
