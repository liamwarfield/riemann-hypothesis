module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.OneVanish

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.PClassVanish
open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc
open scoped Pointwise

namespace PositivityTheory.Rg.BcB.CV.ClassVanishing

open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4

theorem exists_haar_inv {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] [LocallyCompactSpace G] (hc : ∀ a b : G, a * b = b * a) :
    ∃ ν : Measure G, ν.IsHaarMeasure ∧ ν.IsInvInvariant := by
  letI : CommGroup G := { (inferInstance : Group G) with mul_comm := hc }
  exact ⟨Measure.haar, inferInstance, Measure.IsHaarMeasure.isInvInvariant_of_regular _⟩

theorem gamma_fin_zero (y : (Fin 0 → SignType) → ℝ) (a : Fin 0 → ℝ) : gam y a = 1 := by
  unfold gam gamOn
  rw [Finset.sum_eq_single (∅ : Finset (Fin 0 → SignType))]
  · simp
  · intro s hs hne
    exfalso
    apply hne
    simp only [Finset.mem_filter] at hs
    exact Finset.subset_empty.mp fun e he => absurd (Subsingleton.elim e 0 ▸ he) hs.2.1
  · intro h
    exfalso
    apply h
    simp [Finset.mem_filter]

theorem quot_congr {G : Type} [Group G] [MeasurableSpace G] (μ : Measure G) {H H' : Subgroup G} (h : H = H')
    (F : G → ℂ) : quotIntegral μ H Measure.count F = quotIntegral μ H' Measure.count F := by
  subst h; rfl

theorem quotL_congr {G : Type} [Group G] [MeasurableSpace G] (μ : Measure G) {H H' : Subgroup G} (h : H = H')
    (F : G → ENNReal) : quotLIntegral μ H Measure.count F = quotLIntegral μ H' Measure.count F := by
  subst h; rfl

end PositivityTheory.Rg.BcB.CV.ClassVanishing

open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 PositivityTheory.Rg.BcB.CV

theorem PositivityTheory.Rg.BcB.CV.pf_ClassVanish : PositivityTheory.Rg.BcB.D4.PairParam → PositivityTheory.Rg.BcB.D4.TorusChar → PositivityTheory.Rg.BcB.D4.ChiGam → PositivityTheory.Rg.BcB.D4.QuotStage → PositivityTheory.Rg.BcB.D4.RatDisc → PositivityTheory.Rg.BcB.SizeBasic → PositivityTheory.Rg.BcB.CV.QAdd → PositivityTheory.Rg.BcB.CV.Vfun → PositivityTheory.Rg.BcB.CV.AdTop → PositivityTheory.Rg.BcB.CV.CutInt → PositivityTheory.Rg.BcB.CV.Glob1 → PositivityTheory.Rg.BcB.CV.Glob2 → PositivityTheory.Rg.BcB.ClassVanish := by
  intro hPP hTC hCG hQS hRD hSB hQA hVf hAT hCI hG1 hG2
  intro E _ _ _ _ n
  obtain ⟨C₀, hC₀⟩ := hCG E n
  refine ⟨max 0 C₀, ?_⟩
  intro _ _ μ _ τ r φ d hφ hsz hvc hτ hreg hne
  obtain ⟨hLC, hT2, hSC, -, -, -⟩ := hAT E n
  haveI := hLC
  haveI := hT2
  haveI := hSC
  obtain ⟨m, Wof, hiso, huniq, hzero, hmeet, hmono, hperp⟩ := hPP E n d hreg
  obtain ⟨hcomm, a, hdegT, hadd, hrat0, hcont, hcpt⟩ := hTC E n d m Wof hiso huniq hzero hmeet hmono hreg
  obtain ⟨hle, hdisc, hclosed⟩ := hRD.1 E n d
  haveI : LocallyCompactSpace (adCent d) := hclosed.locallyCompactSpace
  haveI : BorelSpace (adCent d) := Subtype.borelSpace _
  haveI : SecondCountableTopology (adCent d) := TopologicalSpace.Subtype.secondCountableTopology _
  have hcommT : ∀ s t : adCent d, s * t = t * s := fun s t => Subtype.ext (hcomm s s.2 t t.2)
  obtain ⟨ν, hνH, hνI⟩ := ClassVanishing.exists_haar_inv hcommT
  haveI := hνH
  haveI := hνI
  have hmap : (ratIn d).map (adCent d).subtype = ratCent d := by
    rw [ratIn, Subgroup.subgroupOf_map_subtype, inf_of_le_left hle]
  set F : GA E n → ℂ := fun x => chiT τ x * φ (twConj (thetaA E n) x (ratGL E n d)) with hF
  obtain ⟨hFm, hFinv, hFfin⟩ := hCI E n μ τ φ d hφ
  have hstage := hQS (GA E n) μ (adCent d) ν (ratIn d) F hclosed hdisc hFm
    (fun g hg x => hFinv g (Subgroup.mem_subgroupOf.1 hg) x)
    (by rw [ClassVanishing.quotL_congr μ hmap]; exact hFfin)
  rw [ClassVanishing.quot_congr μ hmap] at hstage

  obtain ⟨V, hVdef⟩ : ∃ V : ((Fin m → SignType) → ℝ) → ℂ,
      V = fun y => quotIntegral ν (ratIn d) Measure.count fun t : adCent d => (gam y (a t) : ℂ) := ⟨_, rfl⟩
  have hcptT : ∀ M : ℝ, ∃ K : Set (adCent d), IsCompact K ∧ ∀ t : adCent d, (∀ i, |a t i| ≤ M) →
      t ∈ ((ratIn d : Subgroup (adCent d)) : Set (adCent d)) * K := by
    intro M
    obtain ⟨K, hK, hKt⟩ := hcpt M
    refine ⟨Subtype.val ⁻¹' K, hclosed.isClosedEmbedding_subtypeVal.isCompact_preimage hK, fun t ht => ?_⟩
    obtain ⟨g, hg, k, hk, hgk⟩ := Set.mem_mul.1 (hKt t t.2 ht)
    have hgA : g ∈ adCent d := hle hg
    have hkA : k ∈ adCent d := by
      have : k = g⁻¹ * t := by rw [← hgk]; group
      rw [this]; exact (adCent d).mul_mem ((adCent d).inv_mem hgA) t.2
    exact Set.mem_mul.2 ⟨⟨g, hgA⟩, hg, ⟨k, hkA⟩, hk, Subtype.ext hgk⟩
  obtain ⟨hVP, hVtr⟩ := hVf (adCent d) ν (ratIn d) m (fun t => a t) hcommT hdisc
    (continuousOn_iff_continuous_domRestrict.1 hcont) (fun s t => hadd s s.2 t t.2)
    (fun t ht => hrat0 t (Subgroup.mem_subgroupOf.1 ht)) hcptT
  rw [← hVdef] at hVP
  have hVinv : ∀ t ∈ adCent d, ∀ y, V (fun e => y e - sdot e (a t)) = V y := by
    intro t ht y
    have := hVtr y ⟨t, ht⟩
    rw [hVdef]
    exact this

  have hinner : ∀ x, (quotIntegral ν (ratIn d) Measure.count fun t : adCent d => F ((t : GA E n) * x)) =
      φ (twConj (thetaA E n) x (ratGL E n d)) * V (yOf τ Wof x) := by
    intro x
    have hpt : (fun t : adCent d => F ((t : GA E n) * x)) =
        fun t : adCent d => φ (twConj (thetaA E n) x (ratGL E n d)) * (gam (yOf τ Wof x) (a t) : ℂ) := by
      funext t
      show chiT τ ((t : GA E n) * x) * φ (twConj (thetaA E n) ((t : GA E n) * x) (ratGL E n d)) = _
      rw [twConj_mul_left (thetaA E n) (ratGL E n d) t.2 x]
      by_cases h0 : φ (twConj (thetaA E n) x (ratGL E n d)) = 0
      · simp [h0]
      · have h1 := hsz _ h0
        have h2 := (hSB E n).2.1 (twConj (thetaA E n) x (ratGL E n d))
        have hτ' : C₀ * (1 + logSize (twConj (thetaA E n) x (ratGL E n d))) ≤ τ :=
          calc C₀ * (1 + logSize (twConj (thetaA E n) x (ratGL E n d)))
              ≤ max 0 C₀ * (1 + logSize (twConj (thetaA E n) x (ratGL E n d))) :=
                mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith)
            _ ≤ max 0 C₀ * (1 + r) := mul_le_mul_of_nonneg_left (by linarith) (le_max_left _ _)
            _ ≤ τ := hτ
        exact (mul_comm _ _).trans
          (congrArg (fun z => φ (twConj (thetaA E n) x (ratGL E n d)) * z)
            (hC₀ d m Wof a hiso huniq hzero hmeet hmono hreg hdegT τ x hτ' t t.2))
    rw [hpt, (hQA (adCent d) ν (ratIn d) Measure.count).2.2 (φ (twConj (thetaA E n) x (ratGL E n d)))
      (fun t : adCent d => (gam (yOf τ Wof x) (a t) : ℂ)), hVdef]
  have hcut : cutTerm μ τ φ d = quotIntegral μ (adCent d) ν
      (fun x => φ (twConj (thetaA E n) x (ratGL E n d)) * V (yOf τ Wof x)) := by
    show quotIntegral μ (ratCent d) Measure.count F = _
    rw [hstage]
    congr 1
    funext x
    exact hinner x
  rw [hcut]
  by_cases hm : m = 0
  · subst hm
    have hV : ∀ y, V y = V 0 := fun y => by
      rw [hVdef]
      simp only [ClassVanishing.gamma_fin_zero]
    rw [show (fun x => φ (twConj (thetaA E n) x (ratGL E n d)) * V (yOf τ Wof x)) =
        fun x => V 0 * φ (twConj (thetaA E n) x (ratGL E n d)) from funext fun x => by rw [hV, mul_comm],
      (hQA (GA E n) μ (adCent d) ν).2.2 (V 0) (fun x => φ (twConj (thetaA E n) x (ratGL E n d))),
      hG1 E n μ d ν φ hreg hne hcomm hclosed hφ hvc, mul_zero]
  · exact hG2 E n m μ d ν Wof a V τ φ hm
      ⟨hreg, hiso, huniq, hzero, hmeet, hmono, hperp, hcomm, hclosed, hdegT⟩ hVP hVinv hφ hvc
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.PQProd
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ProdE
noncomputable def UpperTheory.Reformulated.B.DaGva8.prodE :
    {G₁ G₂ : Type} →
      [inst : Group G₁] →
        [inst_1 : TopologicalSpace G₁] →
          [inst_2 : Group G₂] →
            [inst_3 : TopologicalSpace G₂] → (T₁ : Subgroup G₁) → (T₂ : Subgroup G₂) → ↥T₁ × ↥T₂ ≃ₜ* ↥(T₁.prod T₂) :=
  fun {_ _} _ _ _ _ T₁ T₂ =>
    { toFun := fun x => ⟨(x.1.1, x.2.1), x.1.2, x.2.2⟩
      invFun := fun y => (⟨y.1.1, y.2.1⟩, ⟨y.1.2, y.2.2⟩)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      continuous_toFun :=
        ((continuous_subtype_val.comp continuous_fst).prodMk
          (continuous_subtype_val.comp continuous_snd)).subtype_mk _
      continuous_invFun :=
        ((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
          ((continuous_snd.comp continuous_subtype_val).subtype_mk _) }
end

noncomputable section

open MeasureTheory PositivityTheory.Rg.Tf.Loc

namespace PositivityTheory.Rg.BcB.CV.QuotientProduct

theorem exists_haar_inv (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (hc : ∀ a b : H, a * b = b * a) : ∃ ν : Measure H, ν.IsHaarMeasure ∧ ν.IsInvInvariant := by
  let inst : CommGroup H := { (inferInstance : Group H) with mul_comm := hc }
  exact ⟨Measure.haar, inferInstance,
    @Measure.IsHaarMeasure.isInvInvariant_of_regular H inst _ _ _ _ Measure.haar _ _ _⟩

noncomputable def prodE {G₁ G₂ : Type} [Group G₁] [TopologicalSpace G₁] [Group G₂] [TopologicalSpace G₂]
    (T₁ : Subgroup G₁) (T₂ : Subgroup G₂) : T₁ × T₂ ≃ₜ* T₁.prod T₂ :=
  _root_.UpperTheory.Reformulated.B.DaGva8.prodE T₁ T₂

def swapE (G₁ G₂ : Type) [Group G₁] [TopologicalSpace G₁] [Group G₂] [TopologicalSpace G₂] :
    G₁ × G₂ ≃ₜ* G₂ × G₁ where
  toFun := Prod.swap
  invFun := Prod.swap
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun := continuous_swap
  continuous_invFun := continuous_swap

theorem isClosed_prod {G₁ G₂ : Type} [Group G₁] [TopologicalSpace G₁] [Group G₂] [TopologicalSpace G₂]
    {T₁ : Subgroup G₁} {T₂ : Subgroup G₂} (h₁ : IsClosed (T₁ : Set G₁)) (h₂ : IsClosed (T₂ : Set G₂)) :
    IsClosed ((T₁.prod T₂ : Subgroup (G₁ × G₂)) : Set (G₁ × G₂)) := by
  rw [Subgroup.coe_prod]; exact h₁.prod h₂

theorem left (hQP : PositivityTheory.Rg.BcB.D4.QuotProd) (hQM : QMap)
    (G₁ : Type) [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [T2Space G₁]
    [SecondCountableTopology G₁] [MeasurableSpace G₁] [BorelSpace G₁]
    (G₂ : Type) [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] [LocallyCompactSpace G₂] [T2Space G₂]
    [SecondCountableTopology G₂] [MeasurableSpace G₂] [BorelSpace G₂] (μ₁ : Measure G₁) [μ₁.IsHaarMeasure]
    (μ₂ : Measure G₂) [μ₂.IsHaarMeasure]
    (T₁ : Subgroup G₁) (T₂ : Subgroup G₂) (ν : Measure (T₁.prod T₂)) [ν.IsHaarMeasure] [ν.IsInvInvariant]
    (F : G₁ × G₂ → ℂ) (hT₁ : IsClosed (T₁ : Set G₁)) (hT₂ : IsClosed (T₂ : Set G₂))
    (hc₁ : ∀ s ∈ T₁, ∀ t ∈ T₁, s * t = t * s) (hc₂ : ∀ s ∈ T₂, ∀ t ∈ T₂, s * t = t * s)
    (hF : Measurable F) (hFT : ∀ t ∈ T₁.prod T₂, ∀ x, F (t * x) = F x)
    (h : ∀ (ν₁ : Measure T₁) [ν₁.IsHaarMeasure] [ν₁.IsInvInvariant] x₂,
      quotIntegral μ₁ T₁ ν₁ (fun x₁ => F (x₁, x₂)) = 0) :
    quotIntegral (μ₁.prod μ₂) (T₁.prod T₂) ν F = 0 := by
  have : LocallyCompactSpace T₁ := hT₁.locallyCompactSpace
  have : LocallyCompactSpace T₂ := hT₂.locallyCompactSpace
  have : SecondCountableTopology T₁ := inferInstanceAs (SecondCountableTopology (T₁ : Set G₁))
  have : SecondCountableTopology T₂ := inferInstanceAs (SecondCountableTopology (T₂ : Set G₂))
  obtain ⟨ν₁, _, _⟩ := exists_haar_inv T₁ (fun a b => Subtype.ext (hc₁ a a.2 b b.2))
  obtain ⟨ν₂, _, _⟩ := exists_haar_inv T₂ (fun a b => Subtype.ext (hc₂ a a.2 b b.2))
  set E := prodE T₁ T₂
  have hE : Measurable E := E.continuous.measurable
  have hinvP : Measure.map Inv.inv (ν₁.prod ν₂) = ν₁.prod ν₂ := by
    have : (Inv.inv : T₁ × T₂ → T₁ × T₂) = Prod.map Inv.inv Inv.inv := rfl
    rw [this, ← Measure.map_prod_map _ _ continuous_inv.measurable continuous_inv.measurable,
      Measure.map_inv_eq_self, Measure.map_inv_eq_self]
  have : (Measure.map E (ν₁.prod ν₂)).IsInvInvariant := by
    constructor
    show Measure.map Inv.inv (Measure.map E (ν₁.prod ν₂)) = Measure.map E (ν₁.prod ν₂)
    rw [Measure.map_map continuous_inv.measurable hE]
    have : (Inv.inv ∘ ⇑E) = ⇑E ∘ Inv.inv := funext fun p => (map_inv E p).symm
    rw [this, ← Measure.map_map hE continuous_inv.measurable, hinvP]
  have hmap : (Measure.map E (ν₁.prod ν₂)).map
      (fun t : T₁.prod T₂ => ((⟨t.1.1, (Subgroup.mem_prod.1 t.2).1⟩, ⟨t.1.2, (Subgroup.mem_prod.1 t.2).2⟩) : T₁ × T₂)) =
      ν₁.prod ν₂ := by
    have : (fun t : T₁.prod T₂ => ((⟨t.1.1, (Subgroup.mem_prod.1 t.2).1⟩, ⟨t.1.2, (Subgroup.mem_prod.1 t.2).2⟩) : T₁ × T₂))
      = ⇑E.symm := rfl
    rw [this, Measure.map_map (show Measurable ⇑E.symm from E.symm.continuous.measurable) hE]
    have : (⇑E.symm ∘ ⇑E) = id := funext fun p => E.symm_apply_apply p
    rw [this, Measure.map_id]
  have h0 := hQP G₁ G₂ μ₁ μ₂ T₁ T₂ ν₁ ν₂ (Measure.map E (ν₁.prod ν₂)) F hF hmap hFT (fun x₂ => h ν₁ x₂)
  refine hQM (G₁ × G₂) (G₁ × G₂) (ContinuousMulEquiv.refl _) (μ₁.prod μ₂) (μ₁.prod μ₂) (T₁.prod T₂) (T₁.prod T₂)
    ν (Measure.map E (ν₁.prod ν₂)) F (isClosed_prod hT₁ hT₂) ?_ hF hFT h0
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩; exact hy
  · intro hx; exact ⟨x, hx, rfl⟩

end PositivityTheory.Rg.BcB.CV.QuotientProduct

namespace PositivityTheory.Rg.BcB.CV

open QuotientProduct in
theorem pf_QProd : PositivityTheory.Rg.BcB.D4.QuotProd → PositivityTheory.Rg.BcB.CV.QMap → PositivityTheory.Rg.BcB.CV.QProd := by
  intro hQP hQM G₁ _ _ _ _ _ _ _ _ G₂ _ _ _ _ _ _ _ _ μ₁ _ μ₂ _ T₁ T₂ ν _ _ F hT₁ hT₂ hc₁ hc₂ hF hFT hcase
  rcases hcase with h | h
  · exact left hQP hQM G₁ G₂ μ₁ μ₂ T₁ T₂ ν F hT₁ hT₂ hc₁ hc₂ hF hFT h
  · have hcl := isClosed_prod hT₂ hT₁
    have : LocallyCompactSpace (T₂.prod T₁) := hcl.locallyCompactSpace
    have : SecondCountableTopology (T₂.prod T₁) :=
      inferInstanceAs (SecondCountableTopology ((T₂.prod T₁ : Subgroup (G₂ × G₁)) : Set (G₂ × G₁)))
    obtain ⟨ν', _, _⟩ := exists_haar_inv (T₂.prod T₁) (fun a b => Subtype.ext (Prod.ext
      (hc₂ _ (Subgroup.mem_prod.1 a.2).1 _ (Subgroup.mem_prod.1 b.2).1)
      (hc₁ _ (Subgroup.mem_prod.1 a.2).2 _ (Subgroup.mem_prod.1 b.2).2)))
    set S := swapE G₁ G₂
    have hFT' : ∀ t ∈ T₂.prod T₁, ∀ x, F (S.symm (t * x)) = F (S.symm x) := by
      intro t ht x
      rw [map_mul]
      exact hFT _ (Subgroup.mem_prod.2 ⟨(Subgroup.mem_prod.1 ht).2, (Subgroup.mem_prod.1 ht).1⟩) _
    have h0 := left hQP hQM G₂ G₁ μ₂ μ₁ T₂ T₁ ν' (fun y => F (S.symm y)) hT₂ hT₁ hc₂ hc₁
      (hF.comp S.symm.continuous.measurable) hFT' (fun ν₂ _ _ x₁ => h ν₂ x₁)
    refine hQM (G₁ × G₂) (G₂ × G₁) S (μ₁.prod μ₂) (μ₂.prod μ₁) (T₁.prod T₂) (T₂.prod T₁)
      ν ν' F (isClosed_prod hT₁ hT₂) ?_ hF hFT h0
    ext ⟨a, b⟩
    simp only [Subgroup.mem_map, Subgroup.mem_prod]
    constructor
    · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, hxy⟩
      change (y, x) = (a, b) at hxy
      simp only [Prod.mk.injEq] at hxy
      obtain ⟨rfl, rfl⟩ := hxy
      exact ⟨hy, hx⟩
    · rintro ⟨ha, hb⟩
      exact ⟨(b, a), ⟨hb, ha⟩, rfl⟩

end PositivityTheory.Rg.BcB.CV
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.POneVanish
noncomputable section

open MeasureTheory PositivityTheory.Rg.Tf.Loc

namespace PositivityTheory.Rg.BcB.CV.FirstVanishingAlt

open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 PositivityTheory.Rg.BcB.CV

theorem twConj_mul_left {n : ℕ} (d t x : GL (Fin n) ℂ) (ht : t ∈ twCent (thC n) d) :
    twConj (thC n) (t * x) d = twConj (thC n) x d := by
  rw [mem_twCent] at ht
  simp only [twConj, map_mul]
  calc (t * x)⁻¹ * d * ((thC n) t * (thC n) x) = x⁻¹ * (t⁻¹ * d * (thC n) t) * (thC n) x := by group
    _ = x⁻¹ * d * (thC n) x := by rw [ht]

theorem sle_refl {m : ℕ} (e : Fin m → SignType) : SLe e e := fun _ _ => rfl

def zr {m : ℕ} (z : (Fin m → SignType) → ℝ) (s : Finset (Fin m → SignType)) : (Fin m → SignType) → ℝ :=
  fun e => if e ∈ s then z e else 0

theorem zr_insert {m : ℕ} (z y : (Fin m → SignType) → ℝ) {s : Finset (Fin m → SignType)} {e : Fin m → SignType}
    (he : e ∉ s) : y + zr z (insert e s) = Function.update (y + zr z s) e (y e + z e) := by
  funext e'
  by_cases h : e' = e
  · subst h; simp [zr]
  · simp [zr, h]

theorem zr_self {m : ℕ} (z y : (Fin m → SignType) → ℝ) {s : Finset (Fin m → SignType)} {e : Fin m → SignType}
    (he : e ∉ s) : y + zr z s = Function.update (y + zr z s) e (y e) := by
  funext e'
  by_cases h : e' = e
  · subst h; simp [zr, he]
  · simp [h]

theorem diff_step {m : ℕ} {V : ((Fin m → SignType) → ℝ) → ℂ} (hV : VP V) (z : (Fin m → SignType) → ℝ)
    (s : Finset (Fin m → SignType)) (e : Fin m → SignType) (he : e ∉ s) (y y' : (Fin m → SignType) → ℝ)
    (hyy : ∀ e', SLe e e' ∨ SLe e' e → y e' = y' e') :
    V (y + zr z (insert e s)) - V (y + zr z s) = V (y' + zr z (insert e s)) - V (y' + zr z s) := by
  have key : ∀ w : (Fin m → SignType) → ℝ, V (w + zr z (insert e s)) - V (w + zr z s) =
      V (Function.update (w + zr z s) e (w e + z e)) - V (Function.update (w + zr z s) e (w e)) := fun w => by
    rw [← zr_insert z w he, ← zr_self z w he]
  have hee : y e = y' e := hyy e (Or.inl (sle_refl e))
  rw [key y, key y', hee]
  exact hV.diff _ _ e _ _ (fun e' h => by simp only [Pi.add_apply, hyy e' h])

theorem good_V {n m : ℕ} [MeasurableSpace (GL (Fin n) ℂ)] [BorelSpace (GL (Fin n) ℂ)] {d : GL (Fin n) ℂ}
    {V : ((Fin m → SignType) → ℝ) → ℂ} {p : GL (Fin n) ℂ → (Fin m → SignType) → ℝ} (hV : VP V) (hL : LocFam d V p)
    (c : (Fin m → SignType) → ℝ) :
    Measurable (fun x => V (p x + c)) ∧ (∀ t ∈ twCent (thC n) d, ∀ x, V (p (t * x) + c) = V (p x + c)) ∧
      ∀ C : Set (GL (Fin n) ℂ), IsCompact C → ∃ B : ℝ, ∀ x ∈ C, ‖V (p x + c)‖ ≤ B := by
  refine ⟨hV.meas.comp (hL.cont.add continuous_const).measurable, fun t ht x => hL.tor t ht x c, fun C hC => ?_⟩
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn (f := fun x => p x + c) (hL.cont.add continuous_const).continuousOn
  obtain ⟨B, hB⟩ := hV.bdd M
  refine ⟨B, fun x hx => hB _ fun e => ?_⟩
  have := (norm_le_pi_norm (p x + c) e).trans (hM x hx)
  rwa [Real.norm_eq_abs] at this

end PositivityTheory.Rg.BcB.CV.FirstVanishingAlt

open PositivityTheory.Rg.BcB.CV.FirstVanishingAlt in
theorem PositivityTheory.Rg.BcB.CV.pf_OneVanish : PositivityTheory.Rg.BcB.LocVanish → PositivityTheory.Rg.BcB.D4.LocProper → PositivityTheory.Rg.BcB.CV.LocTor → PositivityTheory.Rg.BcB.CV.QInt → PositivityTheory.Rg.BcB.CV.QAdd → PositivityTheory.Rg.BcB.CV.OneVanish := by
  intro hLV hLP hLT hQI hQA n m _ _ μ _ d ν _ _ f V p z hsep hf hfs hfc hV hL hz0
  obtain ⟨hTc, -, hθc, hlc, hsc⟩ := hLT n d hsep
  have := hlc
  have := hsc
  have htc : Continuous (fun x : GL (Fin n) ℂ => twConj (thC n) x d) := by
    unfold twConj
    exact (continuous_inv.mul continuous_const).mul hθc
  obtain ⟨Bf, hBf⟩ := hf.bounded_above_of_compact_support hfs
  obtain ⟨C', hC', hsub⟩ := hLP n d hsep (tsupport f) hfs
  obtain ⟨A, -, hAI⟩ := hQI (GL (Fin n) ℂ) μ (twCent (thC n) d) ν C' hTc hC'
  have fin : ∀ g : GL (Fin n) ℂ → ℂ, Measurable g → (∀ t ∈ twCent (thC n) d, ∀ x, g (t * x) = g x) →
      (∀ C : Set (GL (Fin n) ℂ), IsCompact C → ∃ B : ℝ, ∀ x ∈ C, ‖g x‖ ≤ B) →
      Measurable (fun x => f (twConj (thC n) x d) * g x) ∧
      quotLIntegral μ (twCent (thC n) d) ν (fun x => ‖f (twConj (thC n) x d) * g x‖ₑ) ≠ ⊤ := by
    intro g hgm hgT hgb
    obtain ⟨Bg, hBg⟩ := hgb C' hC'
    have hm : Measurable (fun x => f (twConj (thC n) x d) * g x) := (hf.comp htc).measurable.mul hgm
    refine ⟨hm, (hAI _ (max Bf 0 * max Bg 0) (mul_nonneg (le_max_right _ _) (le_max_right _ _)) hm ?_ ?_ ?_).1⟩
    · intro t ht x
      rw [twConj_mul_left d t x ht, hgT t ht x]
    · intro x hx
      exact hsub (show twConj (thC n) x d ∈ tsupport f from
        subset_tsupport f (Function.mem_support.2 (left_ne_zero_of_mul hx)))
    · intro x hx
      rw [norm_mul]
      exact mul_le_mul ((hBf _).trans (le_max_left _ _)) ((hBg x hx).trans (le_max_left _ _)) (norm_nonneg _)
        (le_max_right _ _)
  have goodsub : ∀ c c' : (Fin m → SignType) → ℝ, Measurable (fun x => V (p x + c) - V (p x + c')) ∧
      (∀ t ∈ twCent (thC n) d, ∀ x, V (p (t * x) + c) - V (p (t * x) + c') = V (p x + c) - V (p x + c')) ∧
      ∀ C : Set (GL (Fin n) ℂ), IsCompact C → ∃ B : ℝ, ∀ x ∈ C, ‖V (p x + c) - V (p x + c')‖ ≤ B := by
    intro c c'
    obtain ⟨h1, h2, h3⟩ := good_V hV hL c
    obtain ⟨h1', h2', h3'⟩ := good_V hV hL c'
    refine ⟨h1.sub h1', fun t ht x => by rw [h2 t ht x, h2' t ht x], fun C hC => ?_⟩
    obtain ⟨B, hB⟩ := h3 C hC
    obtain ⟨B', hB'⟩ := h3' C hC
    exact ⟨B + B', fun x hx => (norm_sub_le _ _).trans (add_le_add (hB x hx) (hB' x hx))⟩
  have h0int : quotIntegral μ (twCent (thC n) d) ν (fun _ => (0 : ℂ)) = 0 := by
    simpa using (hQA (GL (Fin n) ℂ) μ (twCent (thC n) d) ν).2.2 0 (fun _ => 0)
  have main : ∀ s : Finset (Fin m → SignType), quotIntegral μ (twCent (thC n) d) ν
      (fun x => f (twConj (thC n) x d) * (V (p x + zr z s) - V (p x + 0))) = 0 := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · have h0 : zr z ∅ = 0 := by funext e; simp [zr]
      simp only [h0, sub_self, mul_zero]
      exact h0int
    · intro e s he ih
      have hFi := fin _ (goodsub (zr z (insert e s)) 0).1 (goodsub _ 0).2.1 (goodsub _ 0).2.2
      have hFs := fin _ (goodsub (zr z s) 0).1 (goodsub _ 0).2.1 (goodsub _ 0).2.2
      have hdiff : quotIntegral μ (twCent (thC n) d) ν
          (fun x => f (twConj (thC n) x d) * (V (p x + zr z (insert e s)) - V (p x + zr z s))) = 0 := by
        by_cases he0 : e = 0
        · subst he0
          have hzz : zr z (insert 0 s) = zr z s := by
            funext e'
            by_cases h : e' = 0
            · subst h; simp [zr, he, hz0]
            · simp [zr, h]
          simp only [hzz, sub_self, mul_zero]
          exact h0int
        · obtain ⟨W₁, W₂, ⟨hW1, hW12, hp1, hp2⟩, hnil⟩ := hL.nil e he0
          obtain ⟨hm, hTi, hb⟩ := goodsub (zr z (insert e s)) (zr z s)
          exact hLV n μ f (fun x => V (p x + zr z (insert e s)) - V (p x + zr z s)) d ν W₁ W₂ hf hfs hfc hsep
            hW1 hW12 hp1 hp2 hm hb (fun x k hk => by simp only [hL.cpt x k hk]) hTi
            (fun u hu x => diff_step hV z s e he _ _ (fun e' h => hnil u hu x e' h))
      have key : quotIntegral μ (twCent (thC n) d) ν
          (fun x => f (twConj (thC n) x d) * (V (p x + zr z (insert e s)) - V (p x + 0)) -
            f (twConj (thC n) x d) * (V (p x + zr z s) - V (p x + 0))) =
          quotIntegral μ (twCent (thC n) d) ν (fun x => f (twConj (thC n) x d) * (V (p x + zr z (insert e s)) - V (p x + 0))) -
          quotIntegral μ (twCent (thC n) d) ν (fun x => f (twConj (thC n) x d) * (V (p x + zr z s) - V (p x + 0))) :=
        (hQA (GL (Fin n) ℂ) μ (twCent (thC n) d) ν).2.1 _ _ hFi.1 hFs.1 hFi.2 hFs.2
      have hfun : (fun x => f (twConj (thC n) x d) * (V (p x + zr z (insert e s)) - V (p x + 0)) -
            f (twConj (thC n) x d) * (V (p x + zr z s) - V (p x + 0))) =
          fun x => f (twConj (thC n) x d) * (V (p x + zr z (insert e s)) - V (p x + zr z s)) := by
        funext x; ring
      rw [hfun, hdiff, ih, sub_zero] at key
      exact key.symm
  have hu : zr z Finset.univ = z := by funext e; simp [zr]
  have := main Finset.univ
  rw [hu] at this
  simpa using this
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.QuotIntegralMulRight
noncomputable section

open MeasureTheory PositivityTheory.Rg.Tf.Loc
open scoped ENNReal

namespace PositivityTheory.Rg.BcB.CV.VolumeFunction

open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4

theorem gam_abs_le {m : ℕ} (y : (Fin m → SignType) → ℝ) (a : Fin m → ℝ) :
    |gam y a| ≤ (Fintype.card (Finset (Fin m → SignType)) : ℝ) := by
  classical
  unfold gam gamOn
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ 1 ?_).trans ?_
  · intro s _
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, Finset.abs_prod]
    exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) (fun e _ => by split_ifs <;> simp)
  · rw [nsmul_eq_mul, mul_one]
    exact_mod_cast Finset.card_le_univ _

theorem map_count_equiv {H : Type*} [MeasurableSpace H] [MeasurableSingletonClass H] [Countable H]
    (e : H ≃ H) : Measure.map e (Measure.count : Measure H) = Measure.count := by
  ext s hs
  rw [Measure.map_apply (measurable_of_countable _) hs]
  have h : e ⁻¹' s = e.symm '' s := Set.ext fun x => ⟨fun hx => ⟨e x, hx, e.symm_apply_apply x⟩, by
    rintro ⟨y, hy, rfl⟩
    show e (e.symm y) ∈ s
    rw [e.apply_symm_apply]; exact hy⟩
  rw [h, Measure.count_injective_image e.symm.injective]

theorem count_isHaar {H : Type*} [Group H] [TopologicalSpace H] [DiscreteTopology H] [MeasurableSpace H]
    [MeasurableSingletonClass H] [Countable H] : (Measure.count : Measure H).IsHaarMeasure where
  lt_top_of_isCompact := fun _ hK => Measure.count_apply_lt_top.2 hK.finite_of_discrete
  map_mul_left_eq_self := fun g => map_count_equiv (Equiv.mulLeft g)
  open_pos := fun _ _ hU => by rw [Ne, Measure.count_eq_zero_iff]; exact hU.ne_empty

theorem count_isInv {H : Type*} [Group H] [MeasurableSpace H]
    [MeasurableSingletonClass H] [Countable H] : (Measure.count : Measure H).IsInvInvariant :=
  ⟨map_count_equiv (Equiv.inv H)⟩

theorem quotIntegral_mul_right (hNE : NormEq) {T : Type} [Group T] [TopologicalSpace T] [IsTopologicalGroup T]
    [LocallyCompactSpace T] [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T]
    (ν : Measure T) [ν.IsHaarMeasure] (hcomm : ∀ s t : T, s * t = t * s) (Γ : Subgroup T) (μΓ : Measure Γ)
    [SFinite μΓ] [μΓ.IsInvInvariant] (F : T → ℂ) (hF : Measurable F) (hinv : ∀ g ∈ Γ, ∀ t, F (g * t) = F t)
    (s : T) : quotIntegral ν Γ μΓ (fun t => F (t * s)) = quotIntegral ν Γ μΓ F := by
  unfold quotIntegral
  by_cases hρ : ∃ ρ, IsQuotNormaliser Γ μΓ ρ
  · rw [dif_pos hρ, dif_pos hρ]
    have hρn := hρ.choose_spec
    have : ν.IsMulRightInvariant := ⟨fun g => by
      have h : (fun x => x * g) = (fun x => g * x) := funext fun x => hcomm x g
      rw [h]; exact map_mul_left_eq_self ν g⟩
    have hρ' : IsQuotNormaliser Γ μΓ (fun t => hρ.choose (t * s⁻¹)) := by
      refine ⟨hρn.1.comp (measurable_mul_const _), fun g => ?_⟩
      show ∫⁻ h, hρ.choose ((h : T) * g * s⁻¹) ∂μΓ = 1
      simp only [mul_assoc]
      exact hρn.2 _
    have h1 := integral_mul_right_eq_self (μ := ν) (fun t => F t * ((hρ.choose (t * s⁻¹)).toReal : ℂ)) s
    simp only [mul_inv_cancel_right] at h1
    rw [h1]
    exact hNE T ν Γ μΓ F _ _ hF hinv hρ' hρn
  · rw [dif_neg hρ, dif_neg hρ]

end PositivityTheory.Rg.BcB.CV.VolumeFunction

namespace PositivityTheory.Rg.BcB.CV

open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 PositivityTheory.Rg.BcB.CV.VolumeFunction

theorem pf_Vfun : PositivityTheory.Rg.BcB.ChainSum → PositivityTheory.Rg.BcB.D4.RatDisc → PositivityTheory.Rg.BcB.D4.NormEq → PositivityTheory.Rg.BcB.CV.QInt →
    PositivityTheory.Rg.BcB.CV.QAdd → PositivityTheory.Rg.BcB.CV.Vfun := by
  intro hCS hRD hNE hQI hQA T _ _ _ _ _ _ _ _ ν _ Γ m a hcomm hdisc hac hadd hΓ hprop
  have := hdisc
  have : Countable Γ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hcl : IsClosed (Γ : Set T) := Subgroup.isClosed_of_discrete
  have : (Measure.count : Measure Γ).IsHaarMeasure := count_isHaar
  have : (Measure.count : Measure Γ).IsInvInvariant := count_isInv
  have hmeasF : ∀ y : (Fin m → SignType) → ℝ, Measurable fun t => (gam y (a t) : ℂ) := fun y =>
    Complex.measurable_ofReal.comp (((hCS m).2.2.1 y).comp hac.measurable)
  have hinv : ∀ y : (Fin m → SignType) → ℝ, ∀ g ∈ Γ, ∀ t, (gam y (a (g * t)) : ℂ) = (gam y (a t) : ℂ) := by
    intro y g hg t
    rw [hadd, hΓ g hg, zero_add]
  set K : ℝ := (Fintype.card (Finset (Fin m → SignType)) : ℝ) with hKdef
  have hK0 : 0 ≤ K := Nat.cast_nonneg _
  have key : ∀ M : ℝ, ∃ B : ℝ, ∀ y : (Fin m → SignType) → ℝ, (∀ e, |y e| ≤ M) →
      quotLIntegral ν Γ Measure.count (fun t => ‖(gam y (a t) : ℂ)‖ₑ) ≠ ⊤ ∧
        ‖quotIntegral ν Γ Measure.count (fun t => (gam y (a t) : ℂ))‖ ≤ B := by
    intro M
    obtain ⟨C, hC, hCm⟩ := hprop (2 * M)
    obtain ⟨A, _, hA⟩ := hQI T ν Γ Measure.count C hcl hC
    refine ⟨A * K, fun y hy => hA _ K hK0 (hmeasF y) (hinv y) ?_ ?_⟩
    · intro t ht
      apply hCm
      intro i
      exact (hCS m).2.1 y M (a t) hy (fun h => ht (by rw [h, Complex.ofReal_zero])) i
    · intro x _
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact gam_abs_le _ _
  have hfin : ∀ y : (Fin m → SignType) → ℝ,
      quotLIntegral ν Γ Measure.count (fun t => ‖(gam y (a t) : ℂ)‖ₑ) ≠ ⊤ := by
    intro y
    obtain ⟨B, hB⟩ := key (∑ e, |y e|)
    exact (hB y fun e => Finset.single_le_sum (f := fun e => |y e|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ e)).1
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · by_cases hρ : ∃ ρ, IsQuotNormaliser Γ (Measure.count : Measure Γ) ρ
    · simp only [quotIntegral, dif_pos hρ]
      have h2 : Measurable fun p : ((Fin m → SignType) → ℝ) × T => (p.1, a p.2) :=
        measurable_fst.prodMk (hac.measurable.comp measurable_snd)
      have hj : Measurable fun p : ((Fin m → SignType) → ℝ) × T =>
          (gam p.1 (a p.2) : ℂ) * ((hρ.choose p.2).toReal : ℂ) :=
        (Complex.measurable_ofReal.comp ((hRD.2 m).comp h2)).mul
          (Complex.measurable_ofReal.comp ((hρ.choose_spec.1.ennreal_toReal).comp measurable_snd))
      exact (hj.stronglyMeasurable.integral_prod_right' (ν := ν)).measurable
    · simp only [quotIntegral, dif_neg hρ]
      exact measurable_const
  · intro M
    obtain ⟨B, hB⟩ := key M
    exact ⟨B, fun y hy => (hB y hy).2⟩
  · intro y y' e s t h
    have hsub : ∀ u v : (Fin m → SignType) → ℝ,
        quotIntegral ν Γ Measure.count (fun x => (gam u (a x) : ℂ)) -
          quotIntegral ν Γ Measure.count (fun x => (gam v (a x) : ℂ)) =
        quotIntegral ν Γ Measure.count (fun x => ((gam u (a x) - gam v (a x) : ℝ) : ℂ)) := by
      intro u v
      rw [← (hQA T ν Γ Measure.count).2.1 _ _ (hmeasF u) (hmeasF v) (hfin u) (hfin v)]
      simp only [Complex.ofReal_sub]
    rw [hsub, hsub]
    congr 1
    funext x
    rw [(hCS m).2.2.2.2 y y' e s t (a x) h]
  · intro y s
    have hrew : ∀ t, (gam (fun e => y e - sdot e (a s)) (a t) : ℂ) = (gam y (a (t * s)) : ℂ) := by
      intro t
      have h := (hCS m).2.2.2.1 (fun e => y e - sdot e (a s)) (a t) (a s)
      simp only [sub_add_cancel] at h
      rw [hadd, h]
    simp only [hrew]
    exact quotIntegral_mul_right hNE ν hcomm Γ Measure.count _ (hmeasF y) (hinv y) s

end PositivityTheory.Rg.BcB.CV

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.LintegralIndicatorNeTop
noncomputable section

open MeasureTheory PositivityTheory.Rg.Tf.Loc
open scoped Pointwise ENNReal

namespace PositivityTheory.Rg.BcB.CV

namespace QuotientIntegral

theorem enorm_ofReal_toReal_le (r : ℝ≥0∞) : ‖((r.toReal : ℝ) : ℂ)‖ₑ ≤ r := by
  rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg]
  exact ENNReal.ofReal_toReal_le

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem lintegral_indicator_ne_top (μ : Measure G) [μ.IsHaarMeasure]
    (T : Subgroup G) (ν : Measure T) [ν.IsHaarMeasure] [ν.IsInvInvariant] {C : Set G}
    (hT : IsClosed (T : Set G)) (hC : IsCompact C) {ρ0 : G → ℝ≥0∞}
    (h0 : IsQuotNormaliser T ν ρ0) :
    ∫⁻ g, ((T : Set G) * C).indicator 1 g * ρ0 g ∂μ ≠ ⊤ := by
  classical
  have : LocallyCompactSpace T := hT.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology T := TopologicalSpace.Subtype.secondCountableTopology (T : Set G)
  have : SigmaCompactSpace T := inferInstance
  have : SFinite ν := inferInstance
  have hmcoe : Measurable (fun h : T => (h : G)) := measurable_subtype_coe
  have : ν.IsMulRightInvariant := by
    have : ν.inv.IsMulRightInvariant := inferInstance
    rwa [Measure.inv_eq_self] at this
  obtain ⟨U, hUc, hU1⟩ := exists_compact_mem_nhds (1 : G)
  set K : Set G := U * C with hKdef
  have hKc : IsCompact K := hUc.mul hC
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  set S : Set G := (T : Set G) * C with hSdef
  have hSm : MeasurableSet S := (hT.mul_right_of_isCompact hC).measurableSet
  have hSinv : ∀ t ∈ T, ∀ x, t * x ∈ S ↔ x ∈ S := by
    intro t ht x
    constructor
    · rintro ⟨s, hs, c, hc, hsc⟩
      exact ⟨t⁻¹ * s, T.mul_mem (T.inv_mem ht) hs, c, hc, by
        show t⁻¹ * s * c = x
        rw [mul_assoc, show s * c = t * x from hsc, inv_mul_cancel_left]⟩
    · rintro ⟨s, hs, c, hc, rfl⟩
      exact ⟨t * s, T.mul_mem ht hs, c, hc, mul_assoc _ _ _⟩
  have hKind : Measurable (K.indicator (1 : G → ℝ≥0∞)) := measurable_one.indicator hKm
  set I : G → ℝ≥0∞ := fun g => ∫⁻ h : T, K.indicator 1 ((h : G) * g) ∂ν with hIdef
  have hIm : Measurable I := by
    have : Measurable (fun p : G × T => K.indicator (1 : G → ℝ≥0∞) ((p.2 : G) * p.1)) :=
      hKind.comp ((hmcoe.comp measurable_snd).mul measurable_fst)
    exact this.lintegral_prod_right'
  have hIT : ∀ t ∈ T, ∀ g, I (t * g) = I g := by
    intro t ht g
    have := lintegral_mul_right_eq_self (μ := ν)
      (fun h : T => K.indicator (1 : G → ℝ≥0∞) ((h : G) * g)) ⟨t, ht⟩
    simp only [hIdef]
    rw [← this]
    refine lintegral_congr fun h => ?_
    simp [mul_assoc]
  set V : Set T := (fun h : T => (h : G)) ⁻¹' interior U with hVdef
  have hVm : MeasurableSet V := hmcoe measurableSet_interior
  have hVpos : ν V ≠ 0 := by
    have hVo : IsOpen V := isOpen_interior.preimage continuous_subtype_val
    have h1 : (1 : T) ∈ V := by
      show ((1 : T) : G) ∈ interior U
      simpa using mem_interior_iff_mem_nhds.mpr hU1
    exact (hVo.measure_pos ν ⟨1, h1⟩).ne'
  have hIC : ∀ g ∈ S, ν V ≤ I g := by
    rintro _ ⟨t, ht, c, hc, rfl⟩
    rw [hIT t ht c, ← lintegral_indicator_one hVm]
    refine lintegral_mono fun h => ?_
    by_cases hh : h ∈ V
    · have hK : (h : G) * c ∈ K := Set.mul_mem_mul (interior_subset hh) hc
      simp [hh, hK]
    · simp [Set.indicator_apply, hh]
  have hIfin : ∀ g, I g ≠ ⊤ := by
    intro g
    have hemb : Topology.IsClosedEmbedding (fun h : T => (h : G) * g) :=
      (Homeomorph.mulRight g).isClosedEmbedding.comp hT.isClosedEmbedding_subtypeVal
    have hmeas : Measurable (fun h : T => (h : G) * g) := hmcoe.mul_const g
    have : I g = ν ((fun h : T => (h : G) * g) ⁻¹' K) := by
      rw [← lintegral_indicator_one (hmeas hKm)]
      rfl
    rw [this]
    exact ((hemb.isCompact_preimage hKc).measure_lt_top).ne
  set ρ : G → ℝ≥0∞ := S.piecewise (fun g => K.indicator 1 g * (I g)⁻¹) ρ0 with hρdef
  have hρ : IsQuotNormaliser T ν ρ := by
    refine ⟨Measurable.piecewise hSm (hKind.mul hIm.inv) h0.1, fun g => ?_⟩
    by_cases hg : g ∈ S
    · have hmem : ∀ h : T, (h : G) * g ∈ S := fun h => (hSinv _ h.2 g).2 hg
      calc ∫⁻ h : T, ρ ((h : G) * g) ∂ν = ∫⁻ h : T, K.indicator 1 ((h : G) * g) * (I g)⁻¹ ∂ν := by
            refine lintegral_congr fun h => ?_
            simp only [hρdef, Set.piecewise_eq_of_mem _ _ _ (hmem h), hIT _ h.2]
        _ = I g * (I g)⁻¹ := lintegral_mul_const _ (hKind.comp (hmcoe.mul_const g))
        _ = 1 := ENNReal.mul_inv_cancel
              (ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.mpr hVpos) (hIC g hg))) (hIfin g)
    · have hmem : ∀ h : T, (h : G) * g ∉ S := fun h hh => hg ((hSinv _ h.2 g).1 hh)
      rw [← h0.2 g]
      refine lintegral_congr fun h => ?_
      simp only [hρdef, Set.piecewise_eq_of_notMem _ _ _ (hmem h)]
  have hF1 : Measurable (S.indicator (1 : G → ℝ≥0∞)) := measurable_one.indicator hSm
  have hFinv : ∀ h ∈ T, ∀ g, S.indicator (1 : G → ℝ≥0∞) (h * g) = S.indicator 1 g := by
    intro h hh g
    simp only [Set.indicator_apply, hSinv h hh g, Pi.one_apply]
  rw [lintegral_normaliser_eq hF1 hFinv h0 hρ]
  refine ne_of_lt (lt_of_le_of_lt (b := ∫⁻ g, K.indicator 1 g * (ν V)⁻¹ ∂μ)
    (lintegral_mono fun g => ?_) ?_)
  · by_cases hg : g ∈ S
    · simp only [Set.indicator_of_mem hg, Pi.one_apply, one_mul, hρdef,
        Set.piecewise_eq_of_mem _ _ _ hg]
      gcongr
      exact hIC g hg
    · simp [hg]
  · rw [lintegral_mul_const _ hKind, lintegral_indicator_one hKm]
    exact ENNReal.mul_lt_top hKc.measure_lt_top (ENNReal.inv_lt_top.mpr (pos_iff_ne_zero.mpr hVpos))

theorem main (μ : Measure G) [μ.IsHaarMeasure] (T : Subgroup G) (ν : Measure T) [ν.IsHaarMeasure]
    [ν.IsInvInvariant] (C : Set G) (hT : IsClosed (T : Set G)) (hC : IsCompact C) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (F : G → ℂ) (B : ℝ), 0 ≤ B → Measurable F →
      (∀ t ∈ T, ∀ x, F (t * x) = F x) → (∀ x, F x ≠ 0 → x ∈ (T : Set G) * C) →
      (∀ x ∈ C, ‖F x‖ ≤ B) → quotLIntegral μ T ν (fun x => ‖F x‖ₑ) ≠ ⊤ ∧
        ‖quotIntegral μ T ν F‖ ≤ A * B := by
  classical
  by_cases hex : ∃ ρ, IsQuotNormaliser T ν ρ
  · have h0 : IsQuotNormaliser T ν hex.choose := hex.choose_spec
    set S : Set G := (T : Set G) * C with hSdef
    have hL : ∫⁻ g, S.indicator 1 g * hex.choose g ∂μ ≠ ⊤ :=
      lintegral_indicator_ne_top μ T ν hT hC h0
    refine ⟨(∫⁻ g, S.indicator 1 g * hex.choose g ∂μ).toReal, ENNReal.toReal_nonneg,
      fun F B hB hF hFT hFS hFC => ?_⟩
    have hbound : ∀ g, ‖F g‖ₑ ≤ ENNReal.ofReal B * S.indicator 1 g := by
      intro g
      by_cases hg : g ∈ S
      · rw [Set.indicator_of_mem hg, Pi.one_apply, mul_one]
        obtain ⟨t, ht, c, hc, rfl⟩ := hg
        rw [hFT t ht c, ← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hFC c hc)
      · have : F g = 0 := by
          by_contra h
          exact hg (hFS g h)
        simp [this]
    have hle : ∫⁻ g, ‖F g‖ₑ * hex.choose g ∂μ ≤
        ENNReal.ofReal B * ∫⁻ g, S.indicator 1 g * hex.choose g ∂μ := by
      calc ∫⁻ g, ‖F g‖ₑ * hex.choose g ∂μ
          ≤ ∫⁻ g, ENNReal.ofReal B * (S.indicator 1 g * hex.choose g) ∂μ :=
            lintegral_mono fun g => by
              rw [← mul_assoc]
              gcongr
              exact hbound g
        _ = ENNReal.ofReal B * ∫⁻ g, S.indicator 1 g * hex.choose g ∂μ :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    have hne : ENNReal.ofReal B * ∫⁻ g, S.indicator 1 g * hex.choose g ∂μ ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hL
    have hfin : ∫⁻ g, ‖F g‖ₑ * hex.choose g ∂μ ≠ ⊤ := ne_top_of_le_ne_top hne hle
    refine ⟨by rw [quotLIntegral, dite_eq_left hex]; exact hfin, ?_⟩
    rw [quotIntegral, dite_eq_left hex]
    calc ‖∫ g, F g * ((hex.choose g).toReal : ℂ) ∂μ‖
        = ‖∫ g, F g * ((hex.choose g).toReal : ℂ) ∂μ‖ₑ.toReal := (toReal_enorm _).symm
      _ ≤ (∫⁻ g, ‖F g‖ₑ * hex.choose g ∂μ).toReal := by
          refine ENNReal.toReal_mono hfin ((enorm_integral_le_lintegral_enorm _).trans
            (lintegral_mono fun g => ?_))
          rw [enorm_mul]
          gcongr
          exact enorm_ofReal_toReal_le _
      _ ≤ (ENNReal.ofReal B * ∫⁻ g, S.indicator 1 g * hex.choose g ∂μ).toReal :=
          ENNReal.toReal_mono hne hle
      _ = (∫⁻ g, S.indicator 1 g * hex.choose g ∂μ).toReal * B := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hB, mul_comm]
  · refine ⟨0, le_rfl, fun F B _ _ _ _ _ => ?_⟩
    simp [quotLIntegral, quotIntegral, hex]

end QuotientIntegral

theorem pf_QInt : QInt := by
  intro G _ _ _ _ _ _ _ _ μ _ T ν _ _ C hT hC
  exact QuotientIntegral.main μ T ν C hT hC

end PositivityTheory.Rg.BcB.CV
end
end
