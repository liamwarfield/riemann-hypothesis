module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagFrameVectorMemCommonSubspace
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsDefiniteSpaceIsometryOfAdaptedPair
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowLatticeTermAdaptedNormalForm
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameAdaptedIsometryOfFixingBothFrames
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermDeterminedByFrameClassAndIsometry
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CmFieldSplitPlaceEqOfPlaceEq
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdaptedNormalFormRelevantTermProof
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EventuallyLocalLatticeCompletionEqCoordinateLatt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ClsOmNonneg
noncomputable section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.RowsConc
namespace GlobalTheory.TypeAsm.PerRow
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section
variable {D : D7} {X : HidaSetting D}

def frCls {Y : Full X} {u : D.what₂.Word} (Λ : Submodule (𝓞 D.host.E) (VS D).V) (t : GTu Y u) :
    Set (Formalism.HermitianLatticeCounting.S6.FlagD (HV D) D.R.rS) :=
  {G | GlobalTheory.DegAsm.FrEqv (F0 X u) Λ (Ft t) G}

def clsOm (Y : Full X) (u : D.what₂.Word) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (b : Set (Formalism.HermitianLatticeCounting.S6.FlagD (HV D) D.R.rS)) : ℝ :=
  if h : ∃ t : GTu Y u, t.lam = Λ ∧ frCls Λ t = b then omT h.choose else 0

theorem frCls_eq_iff (hK : Formalism.HermitianLatticesTheory.IsCMUnram D.host.E) {Y : Full X} {u : D.what₂.Word}
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (t t' : GTu Y u) :
    frCls Λ t = frCls Λ t' ↔ GlobalTheory.DegAsm.FrEqv (F0 X u) Λ (Ft t) (Ft t') := by
  have hE := (GlobalTheory.DegAsm.frEqv_invariants D.host.E (VS D).V (HV D) hK D.R.rS (F0 X u) (dI D) Λ).1
  constructor
  · intro h
    have : Ft t' ∈ frCls Λ t := by rw [h]; exact hE.refl _
    exact this
  · intro h
    ext G
    exact ⟨fun hG => hE.trans (hE.symm h) hG, fun hG => hE.trans h hG⟩

theorem clsOm_nonneg (Y : Full X) (u : D.what₂.Word) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (hK : Formalism.HermitianLatticesTheory.IsCMUnram D.host.E) (b : Set (Formalism.HermitianLatticeCounting.S6.FlagD (HV D) D.R.rS)) : 0 ≤ clsOm Y u Λ b := by
  unfold clsOm
  split_ifs with h
  · exact ((GlobalTheory.DegAsm.WeightInf.main D.host.E (VS D).V (HV D) hK D.R.rS).2 _ _ _ _).1
  · exact le_rfl

theorem clsOm_frCls (hK : Formalism.HermitianLatticesTheory.IsCMUnram D.host.E) {Y : Full X} {u : D.what₂.Word}
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (t : GTu Y u) (ht : t.lam = Λ) : clsOm Y u Λ (frCls Λ t) = omT t := by
  have hex : ∃ s : GTu Y u, s.lam = Λ ∧ frCls Λ s = frCls Λ t := ⟨t, ht, rfl⟩
  unfold clsOm
  rw [dite_eq_left hex]
  obtain ⟨h1, h2⟩ := hex.choose_spec
  have hq := (frCls_eq_iff hK Λ _ _).1 h2
  have := ((GlobalTheory.DegAsm.frEqv_invariants D.host.E (VS D).V (HV D) hK D.R.rS (F0 X u) (dI D) Λ).2 _ _ hq).1
  unfold omT
  rw [h1, ht]
  exact this
end

end GlobalTheory.TypeAsm.PerRow
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumPairsWeightMulClassLeMulSum
open scoped Classical

namespace GlobalTheory

theorem sum_pairs_weight_mul_class_le_mul_sum (α β : Type) (S : Finset (α × α)) (cls : α → β)
    (w : α → ℝ) (om : β → ℝ) (T₁ T₂ : Finset β) (hw : ∀ a, 0 ≤ w a) (hom : ∀ b, 0 ≤ om b)
    (hT : ∀ p ∈ S, cls p.1 ∈ T₁ ∧ cls p.2 ∈ T₂)
    (hinj : ∀ p ∈ S, ∀ q ∈ S, p.1 = q.1 → cls p.2 = cls q.2 → p = q)
    (hsum : ∀ b, ∑ a ∈ (S.image Prod.fst).filter (fun a => cls a = b), w a ≤ 1) :
    ∑ p ∈ S, w p.1 * (om (cls p.1) * om (cls p.2)) ≤ (∑ b ∈ T₁, om b) * ∑ b ∈ T₂, om b := by

  have key : ∀ b ∈ T₁ ×ˢ T₂,
      ∑ p ∈ S.filter (fun p => (cls p.1, cls p.2) = b), w p.1 * (om (cls p.1) * om (cls p.2))
        ≤ om b.1 * om b.2 := by
    intro b _
    set F := S.filter (fun p => (cls p.1, cls p.2) = b) with hF
    have h1 : ∑ p ∈ F, w p.1 * (om (cls p.1) * om (cls p.2))
        = (∑ p ∈ F, w p.1) * (om b.1 * om b.2) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl ?_
      intro p hp
      have e := (Finset.mem_filter.1 hp).2
      rw [← e]
    have h2 : ∑ p ∈ F, w p.1 = ∑ a ∈ F.image Prod.fst, w a := by
      rw [Finset.sum_image]
      intro p hp q hq hpq
      have ep := (Finset.mem_filter.1 hp).2
      have eq := (Finset.mem_filter.1 hq).2
      have hc : cls p.2 = cls q.2 := by
        have := congrArg Prod.snd (ep.trans eq.symm)
        simpa using this
      exact hinj p (Finset.mem_filter.1 hp).1 q (Finset.mem_filter.1 hq).1 hpq hc
    have h3 : F.image Prod.fst ⊆ (S.image Prod.fst).filter (fun a => cls a = b.1) := by
      intro a ha
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 ha
      have hp' := Finset.mem_filter.1 hp
      refine Finset.mem_filter.2 ⟨Finset.mem_image_of_mem _ hp'.1, ?_⟩
      have := congrArg Prod.fst hp'.2
      simpa using this
    have h4 : ∑ p ∈ F, w p.1 ≤ 1 := by
      rw [h2]
      exact (Finset.sum_le_sum_of_subset_of_nonneg h3 (fun a _ _ => hw a)).trans (hsum b.1)
    rw [h1]
    have hnn : 0 ≤ om b.1 * om b.2 := mul_nonneg (hom _) (hom _)
    calc (∑ p ∈ F, w p.1) * (om b.1 * om b.2) ≤ 1 * (om b.1 * om b.2) :=
          mul_le_mul_of_nonneg_right h4 hnn
      _ = om b.1 * om b.2 := one_mul _
  calc ∑ p ∈ S, w p.1 * (om (cls p.1) * om (cls p.2))
      = ∑ b ∈ T₁ ×ˢ T₂, ∑ p ∈ S.filter (fun p => (cls p.1, cls p.2) = b),
          w p.1 * (om (cls p.1) * om (cls p.2)) := by
        symm
        exact Finset.sum_fiberwise_of_maps_to (fun p hp => Finset.mem_product.2 (hT p hp)) _
    _ ≤ ∑ b ∈ T₁ ×ˢ T₂, om b.1 * om b.2 := Finset.sum_le_sum key
    _ = (∑ b ∈ T₁, om b) * ∑ b ∈ T₂, om b := by
      rw [Finset.sum_product, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [Finset.mul_sum]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumPairsDefiniteIsometryLeFrameClasses
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumPairsDefiniteIsometryLeFrameClasses
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.RowsConc GlobalTheory.TypeAsm GlobalTheory.TypeAsm.PerRow
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TypeAsm.PerRow

theorem sum_pairs_le_classes_pf : ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Std D large₂ →
    ∀ (W : Submodule D.host.E (VS D).V) (HW : Formalism.HermitianLatticeCounting.S6.HermSpace D.host.E W),
    GlobalTheory.DegAsm.IsEmb (F0 X u) HW W.subtype → ∀ (Λ : Submodule (𝓞 D.host.E) (VS D).V) (h : GTu Y u → (W ≃ₗ[D.host.E] W)),
    (∀ t ∈ relSet Y u, GlobalTheory.DegAsm.IsH (F0 X u) (Ft t) W.subtype t.lin (h t)) → ∀ (Sf : Finset (GTu Y u × GTu Y u)),
    (∀ p ∈ Sf, p ∈ (Y.tO u u).allPairs (relSet Y u) ∧ p.1.lam = Λ) →
    (∀ p ∈ Sf, ∀ q ∈ Sf, h p.1 * (h p.2)⁻¹ = h q.1 * (h q.2)⁻¹) →
    ∑ p ∈ Sf, wRow D (X.Fu u) p.1.lam' * (omT p.1 * omT p.2) ≤
      (∑ b ∈ Sf.image (fun p => frCls Λ p.1), clsOm Y u Λ b) * ∑ b ∈ Sf.image (fun p => frCls Λ p.2), clsOm Y u Λ b := by
  intro D large₂ X Y u hS W HW he Λ h hh Sf hSf hη
  obtain ⟨hK, -⟩ := GlobalTheory.T.unitaryHostFieldArithmeticConditions D large₂ hS
  have hlam : ∀ p ∈ Sf, p.2.lam = Λ ∧ p.2.lam' = p.1.lam' := by
    intro p hp
    obtain ⟨hl, hl', -⟩ := GlobalTheory.T.termsOverRow_compatible D X Y u p ⟨trivial, trivial, (hSf p hp).1.2.2⟩
    exact ⟨hl.symm.trans (hSf p hp).2, hl'.symm⟩
  have hL : ∑ p ∈ Sf, wRow D (X.Fu u) p.1.lam' * (omT p.1 * omT p.2) =
      ∑ p ∈ Sf, wRow D (X.Fu u) p.1.lam' * (clsOm Y u Λ (frCls Λ p.1) * clsOm Y u Λ (frCls Λ p.2)) := by
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [clsOm_frCls hK Λ p.1 (hSf p hp).2, clsOm_frCls hK Λ p.2 (hlam p hp).1]
  rw [hL]
  generalize hT1 : Sf.image (fun p => frCls Λ p.1) = T₁
  generalize hT2 : Sf.image (fun p => frCls Λ p.2) = T₂
  refine GlobalTheory.sum_pairs_weight_mul_class_le_mul_sum (GTu Y u) _ Sf (frCls Λ)
    (fun t => wRow D (X.Fu u) t.lam') (clsOm Y u Λ) T₁ T₂ ?_ (clsOm_nonneg Y u Λ hK) ?_ ?_ ?_
  · intro t
    show 0 ≤ wRow D (X.Fu u) t.lam'
    unfold wRow; positivity
  · intro p hp
    subst hT1 hT2
    exact ⟨Finset.mem_image.2 ⟨p, hp, rfl⟩, Finset.mem_image.2 ⟨p, hp, rfl⟩⟩
  · intro p hp q hq h1 hc
    have hrel2 : p.2 ∈ relSet Y u := (hSf p hp).1.2.1
    have hrelq : q.2 ∈ relSet Y u := (hSf q hq).1.2.1
    have hhe : h p.2 = h q.2 := by
      have e := hη p hp q hq
      rw [h1] at e
      have e2 := congrArg (fun g => (h q.1)⁻¹ * g) e
      simp only [inv_mul_cancel_left] at e2
      exact inv_injective e2
    have hfe := (frCls_eq_iff hK Λ p.2 q.2).1 hc
    have hl : p.2.lam = q.2.lam := ((hlam p hp).1).trans ((hlam q hq).1).symm
    obtain ⟨N, hN, -⟩ := GlobalTheory.T.exists_adaptedNormalForm_relevantTerm D large₂ X Y u hS p.2 hrel2
    have hfe' : GlobalTheory.DegAsm.FrEqv (F0 X u) p.2.lam (Ft p.2) (Ft q.2) := by rw [(hlam p hp).1]; exact hfe
    have := GlobalTheory.T.term_determined_by_frameClass_and_isometry D large₂ X Y u hS W HW he p.2 q.2 ⟨N, hN⟩ hl hfe' (h p.2) (hh p.2 hrel2)
      (by rw [hhe]; exact hh q.2 hrelq)
    exact Prod.ext h1 this
  · intro b
    have gen : ∀ s : Finset (GTu Y u), (∀ t ∈ s, t.lam = Λ ∧ frCls Λ t = b) →
        ∑ a ∈ s, wRow D (X.Fu u) a.lam' ≤ 1 := by
      intro s hmem
      rcases s.eq_empty_or_nonempty with he0 | ⟨t₀, ht₀⟩
      · rw [he0, Finset.sum_empty]; exact zero_le_one
      obtain ⟨hl0, hb0⟩ := hmem t₀ ht₀
      have hrel : ∀ t ∈ s, t₀.lam = t.lam ∧ GlobalTheory.DegAsm.FrEqv (F0 X u) t₀.lam (Ft t₀) (Ft t) := by
        intro t ht
        obtain ⟨hl, hb⟩ := hmem t ht
        refine ⟨hl0.trans hl.symm, ?_⟩
        rw [hl0]
        exact (frCls_eq_iff hK Λ t₀ t).1 (hb0.trans hb.symm)
      have hw : ∀ t ∈ s, wRow D (X.Fu u) t.lam' = wRow D (X.Fu u) t₀.lam' := by
        intro t ht
        obtain ⟨hl, hf⟩ := hrel t ht
        rw [(GlobalTheory.T.equivFramesSameSecondLatticeFiber_proof D large₂ X Y u hS t₀ t hl hf).1]
      rw [Finset.sum_congr rfl hw, Finset.sum_const, nsmul_eq_mul]
      exact GlobalTheory.T.frameClass_termCount_le_card_aut D large₂ X Y u hS t₀ s hrel
    refine gen _ fun t ht => ?_
    simp only [Finset.mem_filter, Finset.mem_image] at ht
    obtain ⟨⟨p, hp, rfl⟩, ht2⟩ := ht
    exact ⟨(hSf p hp).2, ht2⟩

end GlobalTheory.TypeAsm.PerRow
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumPairsDefiniteIsometryLeFrameClassesStatement
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.RowsConc GlobalTheory.TypeAsm GlobalTheory.TypeAsm.PerRow
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_pairs_definiteIsometry_le_frameClasses : ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Std D large₂ → ∀ (W : Submodule D.host.E (VS D).V) (HW : Formalism.HermitianLatticeCounting.S6.HermSpace D.host.E W), GlobalTheory.DegAsm.IsEmb (F0 X u) HW W.subtype → ∀ (Λ : Submodule (𝓞 D.host.E) (VS D).V) (h : GTu Y u → (W ≃ₗ[D.host.E] W)), (∀ t ∈ relSet Y u, GlobalTheory.DegAsm.IsH (F0 X u) (Ft t) W.subtype t.lin (h t)) → ∀ (Sf : Finset (GTu Y u × GTu Y u)), (∀ p ∈ Sf, p ∈ (Y.tO u u).allPairs (relSet Y u) ∧ p.1.lam = Λ) → (∀ p ∈ Sf, ∀ q ∈ Sf, h p.1 * (h p.2)⁻¹ = h q.1 * (h q.2)⁻¹) → ∑ p ∈ Sf, wRow D (X.Fu u) p.1.lam' * (omT p.1 * omT p.2) ≤ (∑ b ∈ Sf.image (fun p => frCls Λ p.1), clsOm Y u Λ b) * ∑ b ∈ Sf.image (fun p => frCls Λ p.2), clsOm Y u Λ b := by
  first | exact @GlobalTheory.TypeAsm.PerRow.sum_pairs_le_classes_pf | exact GlobalTheory.TypeAsm.PerRow.sum_pairs_le_classes_pf | (intros; apply GlobalTheory.TypeAsm.PerRow.sum_pairs_le_classes_pf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumFrameClassWeightsLeDatumBound
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumFrameClassWeightsLeDatumBound
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.RowsConc GlobalTheory.TypeAsm GlobalTheory.TypeAsm.PerRow
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TypeAsm.PerRow

theorem sum_clsOm_le_datBd : ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Std D large₂ → ∀ (W : Submodule D.host.E (VS D).V) (HW : Formalism.HermitianLatticeCounting.S6.HermSpace D.host.E W), GlobalTheory.DegAsm.IsEmb (F0 X u) HW W.subtype → ∀ (Λ : Submodule (𝓞 D.host.E) (VS D).V) (j x : ℕ) (δ : ℕ → D.host.E) (d : Submodule (𝓞 D.host.E) W × Submodule (𝓞 D.host.E) (W × W)) (N : GTu Y u → GlobalTheory.DegCnt.NF (HV D) D.R.rS) (A : Finset (GTu Y u)), A.Nonempty → (∀ t ∈ A, t ∈ relSet Y u ∧ t.lam = Λ ∧ jT t = j ∧ labT t = δ ∧ AdT t (N t) ∧ (N t).IsTerm (gS D) Λ ∧ (N t).gI (gS D) Λ = x ∧ GlobalTheory.DegAsm.datOf (F0 X u) (Ft t) W.subtype (gS D) Λ = d) → ∑ b ∈ A.image (frCls Λ), clsOm Y u Λ b ≤ GlobalTheory.DegAsm.datBd D.host.E D.R.k D.R.rS (k2Del D j δ) (DbL D j δ) (NT D u) x := by
  intro D large₂ X Y u hStd W HW he Λ j x δ d N A hA hT
  obtain ⟨hK, -, -, -, hf, -, -, -, -, -, hV, hg2, -⟩ := GlobalTheory.T.unitaryHostFieldArithmeticConditions D large₂ hStd
  have hgS : 1 ≤ gS D := by omega
  obtain ⟨t₀, ht₀⟩ := hA
  obtain ⟨-, -, hj0, hδ0, hAd0, hTm0, hg0, -⟩ := hT t₀ ht₀
  obtain ⟨-, -, hLDel, hLDb, -⟩ := GlobalTheory.T.adaptedNormalForm_normsMinors_eq_label D large₂ X Y u hStd t₀ (N t₀) hAd0
  obtain ⟨-, hx1, -, -, hfW⟩ := GlobalTheory.T.embeddedDatum_of_term_definiteSpace D.host.E (VS D).V W (HV D) HW W.subtype hK D.R.rS (F0 X u) (Ft t₀)
    (dI D) (N t₀) (gS D) Λ hgS he hAd0 hTm0
  obtain ⟨-, -, hDb1, hDel1, -⟩ := GlobalTheory.T.exists_star_stable_ideal_absorbing_minors D.host.E (VS D).V (HV D) hK D.R.rS (N t₀) (gS D) Λ hgS hTm0
  rw [hg0] at hx1
  rw [hLDel, hj0, hδ0] at hDel1
  rw [hLDb, hj0, hδ0] at hDb1
  let G : Set (Formalism.HermitianLatticeCounting.S6.FlagD (HV D) D.R.rS) → Formalism.HermitianLatticeCounting.S6.FlagD (HV D) D.R.rS := fun b =>
    if hb : ∃ t ∈ A, frCls Λ t = b then Ft hb.choose else F0 X u
  have hGb : ∀ b ∈ A.image (frCls Λ), ∃ t ∈ A, frCls Λ t = b ∧ G b = Ft t := by
    intro b hb
    have hb' : ∃ t ∈ A, frCls Λ t = b := Finset.mem_image.1 hb
    obtain ⟨h1, h2⟩ := hb'.choose_spec
    exact ⟨hb'.choose, h1, h2, by simp only [G, dif_pos hb']⟩
  have key := GlobalTheory.DegAsm.sum_weights_per_datum D.host.E (VS D).V W (HV D) HW W.subtype hK D.R.rS (F0 X u) (dI D)
    (gS D) j (Tu D u) x (fun l => star (δ l)) Λ d (k2Del D j δ) (DbL D j δ) (Set (Formalism.HermitianLatticeCounting.S6.FlagD (HV D) D.R.rS))
    (A.image (frCls Λ)) G hgS hx1 hDel1 hDb1 he ?_ ?_ ?_
  · have hsum : ∑ b ∈ A.image (frCls Λ), clsOm Y u Λ b =
        ∑ b ∈ A.image (frCls Λ), GlobalTheory.DegAsm.omI (F0 X u) (G b) (dI D) Λ := by
      refine Finset.sum_congr rfl fun b hb => ?_
      obtain ⟨t, ht, hbt, hG⟩ := hGb b hb
      obtain ⟨-, hlt, -⟩ := hT t ht
      rw [hG, ← hbt, clsOm_frCls hK Λ t hlt]
      unfold omT
      rw [hlt]
    rw [hsum]
    refine key.trans (le_of_eq ?_)
    rw [show Module.finrank D.host.E W = D.R.k by omega, hf]
    rfl
  · intro b hb
    obtain ⟨t, ht, -, hG⟩ := hGb b hb
    obtain ⟨-, -, hjt, hδt, hAdt, hTmt, hgt, -⟩ := hT t ht
    obtain ⟨a1, a2, a3, a4, -⟩ := GlobalTheory.T.adaptedNormalForm_normsMinors_eq_label D large₂ X Y u hStd t (N t) hAdt
    refine ⟨N t, ?_, hTmt, a1.trans hjt, a2, ?_, ?_, hgt⟩
    · rw [hG]; exact hAdt
    · rw [a3, hjt, hδt]
    · rw [a4, hjt, hδt]
  · intro b hb
    obtain ⟨t, ht, -, hG⟩ := hGb b hb
    obtain ⟨-, -, hjt, hδt, hAdt, -, -, hdt⟩ := hT t ht
    obtain ⟨-, -, -, -, a5⟩ := GlobalTheory.T.adaptedNormalForm_normsMinors_eq_label D large₂ X Y u hStd t (N t) hAdt
    refine ⟨?_, ?_⟩
    · rw [hG, ← hjt, a5, hδt]
    · rw [hG]; exact hdt
  · intro b hb b' hb' hE
    obtain ⟨t, -, hbt, hG⟩ := hGb b hb
    obtain ⟨t', -, hbt', hG'⟩ := hGb b' hb'
    rw [hG, hG'] at hE
    rw [← hbt, ← hbt']
    exact (frCls_eq_iff hK Λ t t').2 hE

end GlobalTheory.TypeAsm.PerRow
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumFrameClassWeightsLeDatumBoundStatement
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.RowsConc GlobalTheory.TypeAsm GlobalTheory.TypeAsm.PerRow
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_frameClassWeights_le_datumBound : ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Std D large₂ → ∀ (W : Submodule D.host.E (VS D).V) (HW : Formalism.HermitianLatticeCounting.S6.HermSpace D.host.E W), GlobalTheory.DegAsm.IsEmb (F0 X u) HW W.subtype → ∀ (Λ : Submodule (𝓞 D.host.E) (VS D).V) (j x : ℕ) (δ : ℕ → D.host.E) (d : Submodule (𝓞 D.host.E) W × Submodule (𝓞 D.host.E) (W × W)) (N : GTu Y u → GlobalTheory.DegCnt.NF (HV D) D.R.rS) (A : Finset (GTu Y u)), A.Nonempty → (∀ t ∈ A, t ∈ relSet Y u ∧ t.lam = Λ ∧ jT t = j ∧ labT t = δ ∧ AdT t (N t) ∧ (N t).IsTerm (gS D) Λ ∧ (N t).gI (gS D) Λ = x ∧ GlobalTheory.DegAsm.datOf (F0 X u) (Ft t) W.subtype (gS D) Λ = d) → ∑ b ∈ A.image (frCls Λ), clsOm Y u Λ b ≤ GlobalTheory.DegAsm.datBd D.host.E D.R.k D.R.rS (k2Del D j δ) (DbL D j δ) (NT D u) x := by
  first | exact @GlobalTheory.TypeAsm.PerRow.sum_clsOm_le_datBd | exact GlobalTheory.TypeAsm.PerRow.sum_clsOm_le_datBd | (intros; apply GlobalTheory.TypeAsm.PerRow.sum_clsOm_le_datBd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TripOfTerms
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.DegAsm.TermPair
open GlobalTheory.ModIdent GlobalTheory.DegAsm.AdaptInv
variable {K V W : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
  {H : Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ}

theorem perp_lift [FiniteDimensional K V] {F G : FlagD H r} {Λ : Submodule (𝓞 K) V} {g : ℕ} (hg : 1 ≤ g)
    (hU : IsUnimod H Λ) (h : IsAdm G F Λ (g : 𝓞 K)) {l : V} (hl : l ∈ Λ) (hp : ∀ x ∈ G.X, H.B x l = 0) :
    ∃ m ∈ Λ, l - (g : K) • m ∈ perp H F.X := by
  have hg0 : (g : K) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hdiv : ∀ x : ↥(Λ ⊓ rs (𝓞 K) F.X), IsIntegral ℤ ((g : K)⁻¹ * H.B x l) := by
    rintro ⟨x, hxΛ, hxS⟩
    obtain ⟨x', -, h1, h2⟩ := h (Fin.last r) 0 x hxΛ (by
      rw [zero_smul, sub_zero]; exact hxS)
    obtain ⟨n, hn, hxn⟩ := (mem_smulLat g Λ _).1 h2
    rw [zero_smul, sub_zero] at h1
    have a1 := hp x' h1
    have a5 : H.B (x' - x) l = g * H.B n l := by rw [hxn]; simp
    obtain ⟨c, hc⟩ := integral_of_unimod hU hn hl
    have : (g : K)⁻¹ * H.B x l = ((-c : 𝓞 K) : K) := by
      rw [inv_mul_eq_iff_eq_mul₀ hg0]
      change _ = (g : K) * (-(c : K))
      rw [hc]
      simp only [map_sub, LinearMap.sub_apply] at a5
      linear_combination a1 - a5
    show IsIntegral ℤ ((g : K)⁻¹ * H.B x l)
    rw [this]
    exact (-c).isIntegral_coe
  let φ : ↥(Λ ⊓ rs (𝓞 K) F.X) →ₗ[𝓞 K] 𝓞 K :=
    { toFun := fun x => ⟨(g : K)⁻¹ * H.B x l, hdiv x⟩
      map_add' := fun a b => by
        apply RingOfIntegers.ext
        show (g : K)⁻¹ * H.B ((a : V) + b) l = (g : K)⁻¹ * H.B a l + (g : K)⁻¹ * H.B b l
        simp [mul_add]
      map_smul' := fun a b => by
        apply RingOfIntegers.ext
        show (g : K)⁻¹ * H.B (a • (b : V)) l = algebraMap (𝓞 K) K a * ((g : K)⁻¹ * H.B b l)
        rw [← algebraMap_smul K a, map_smul, LinearMap.smul_apply, smul_eq_mul]
        ring }
  obtain ⟨m, hm, hφ⟩ := GlobalTheory.UnimodQuot.exists_lattice_rep H hU F.X φ
  refine ⟨m, hm, (mem_perp_iff H _ _).2 fun u hu => orth_symm ?_⟩
  have hΛ := (isLatMod_top_bot_iff Λ).1 hU.1
  have hfull : Submodule.IsFullLattice K Λ :=
    { toIsLattice := Submodule.IsLattice.of_fg K hΛ.1, span_eq_top := hΛ.2 }
  obtain ⟨s, hs⟩ := GlobalTheory.UnimodQuot.exists_smul_mem (K := K) hfull u
  have hs0 : algebraMap (𝓞 K) K s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
  have hs' : algebraMap (𝓞 K) K s • u ∈ Λ := by rw [algebraMap_smul]; exact hs
  have e : H.B (algebraMap (𝓞 K) K s • u) m = (g : K)⁻¹ * H.B (algebraMap (𝓞 K) K s • u) l :=
    hφ ⟨_, hs', F.X.smul_mem _ hu⟩
  rw [eq_inv_mul_iff_mul_eq₀ hg0] at e
  apply mul_left_cancel₀ hs0
  simp only [map_sub, map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, map_natCast,
    smul_eq_mul] at e ⊢
  linear_combination -e

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem mem_X_iff {F G : FlagD H r} {γ : V ≃ₗ[K] V} (hγ : ∀ a, G.e a = γ (F.e a)) (x : V) :
    γ x ∈ G.X ↔ x ∈ F.X := by
  have : G.X = F.X.map (γ : V →ₗ[K] V) := by
    unfold FlagD.X FlagD.Xa
    rw [Submodule.map_span, Set.image_image]
    simp only [hγ]
    rfl
  rw [this, Submodule.mem_map_equiv]
  simp

omit [NumberField K] [StarRing K] in
theorem mem_smul_iff (γ : V ≃ₗ[K] V) (Λ : Submodule (𝓞 K) V) (x : V) : γ x ∈ γ • Λ ↔ x ∈ Λ := by
  constructor
  · rintro ⟨y, hy, e⟩
    have : y = x := γ.injective e
    exact this ▸ hy
  · exact fun h => ⟨x, h, rfl⟩


omit [NumberField K] in
theorem mem_graph {F G : FlagD H r} {HW : Formalism.HermitianLatticeCounting.S6.HermSpace K W} {e : W →ₗ[K] V} (he : IsEmb F HW e)
    (hI : ∀ v ∈ F.X, (∀ w ∈ V0 F G, H.B v w = 0) → v ∈ G.X)
    (hlift : ∀ w : V, (∀ a : Fin (r + 1), H.B (F.e a) w = 0) → ∃ x ∈ F.X, ∀ v ∈ V0 F G, H.B v (w - x) = 0)
    {γ : V ≃ₗ[K] V} {h : W ≃ₗ[K] W} (hγ : ∀ a, G.e a = γ (F.e a)) (hh : IsH F G e γ h) (g : ℕ)
    (Λ' : Submodule (𝓞 K) V) (w v : W) :
    (h w, v) ∈ (datOf F G e g (γ • Λ')).2 ↔
      ∃ x ∈ Λ', ∃ m ∈ γ • Λ', e w - x ∈ F.X ∧ e v - (γ x + (g : K) • m) ∈ F.X := by
  obtain ⟨y, hy, hy1, hy2⟩ := hh w
  have hy' : ∀ u ∈ V0 F G, H.B y u = 0 := (mem_perp_iff H _ _).1 hy
  constructor
  · intro hm
    have hm' : (e (h w), e v) ∈ iotaGraph F G (γ • Λ') (g : 𝓞 K) ⊔ (rs (𝓞 K) F.X).prod (rs (𝓞 K) F.X) := hm
    obtain ⟨⟨a, b⟩, hab, ⟨s, t⟩, ⟨hs, ht⟩, hst⟩ := Submodule.mem_sup.1 hm'
    obtain ⟨e1, e2⟩ := Prod.mk.inj hst
    have hs : s ∈ F.X := hs
    have ht : t ∈ F.X := ht
    obtain ⟨ha, -, l, hl, m, hm, h1, h2⟩ := (mem_iota F G _ g a b).1 hab
    have ha' := ((mem_perp_lattice_flag_iff G F _ a).1 ha).1
    rw [jointSpan_comm] at ha'
    have k1 : y - a ∈ G.X := by
      refine hI _ ?_ fun u hu => by simp [hy' u hu, ha' u hu]
      have := F.X.add_mem hy1 hs
      rw [← e1] at this
      convert this using 1; abel
    refine ⟨γ.symm l, by rw [← mem_smul_iff γ]; simpa using hl, m, hm, ?_, ?_⟩
    · rw [← mem_X_iff hγ, map_sub, LinearEquiv.apply_symm_apply]
      have := G.X.sub_mem (G.X.add_mem k1 h1) hy2
      convert this using 1; abel
    · rw [LinearEquiv.apply_symm_apply, ← e2]
      have := F.X.add_mem h2 ht
      convert this using 1; abel
  · rintro ⟨x, hx, m, hm, h1, h2⟩
    have hx' := (mem_smul_iff γ Λ' x).2 hx
    obtain ⟨s, hs, hb⟩ := hlift (e v) ((he.2 _).2 (Submodule.mem_sup_left ⟨v, rfl⟩))
    have k1 : y - γ x ∈ G.X := by
      have := G.X.add_mem hy2 ((mem_X_iff hγ _).2 h1)
      rw [map_sub] at this
      convert this using 1; abel
    have k2 : e v - s - (γ x + (g : K) • m) ∈ F.X := by
      have := F.X.sub_mem h2 hs
      convert this using 1; abel
    show (e (h w), e v) ∈ iotaGraph F G (γ • Λ') (g : 𝓞 K) ⊔ (rs (𝓞 K) F.X).prod (rs (𝓞 K) F.X)
    refine Submodule.mem_sup.2 ⟨(y, e v - s), (mem_iota F G _ g _ _).2 ⟨?_, ?_, γ x, hx', m, hm, k1, k2⟩,
      (-(y - e (h w)), s), ⟨F.X.neg_mem hy1, hs⟩, by simp⟩
    · exact (mem_perp_lattice_flag_iff G F _ _).2 ⟨by rw [jointSpan_comm]; exact hy', _, hx', k1⟩
    · exact (mem_perp_lattice_flag_iff F G _ _).2 ⟨fun u hu => orth_symm (hb u hu), _,
        Submodule.add_mem _ hx' (gsmul_mem g hm), k2⟩

theorem geom [FiniteDimensional K V] (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {F G : FlagD H r} {𝔡 : Ideal (𝓞 K)} {N : NF H r}
    (hN : Adapt F G 𝔡 N) :
    (∀ v ∈ F.X, (∀ w ∈ V0 F G, H.B v w = 0) → v ∈ G.X) ∧
    (∀ w : V, (∀ a : Fin (r + 1), H.B (F.e a) w = 0) → ∃ x ∈ F.X, ∀ v ∈ V0 F G, H.B v (w - x) = 0) := by
  obtain ⟨-, h, h'⟩ := hN
  obtain ⟨-, -, -, h1, -, -, -, hl, -⟩ := (GlobalTheory.DegCnt.NF.geometry K V H hK r N).1
  rw [sitesCommonSpace_v0_eq_Vp h h'] at h1 hl
  rw [x_eq h] at hl
  refine ⟨fun v hv hw => ?_, fun w hw => hl w fun a => ?_⟩
  · have := ((h1 v (isotropicSpan_le_jointSpan_left F G hv)).1 hw).2
    rwa [x_eq h'] at this
  · have k : N.F.e a - F.e a ∈ F.X := xa_mono F (Nat.le_of_lt_succ a.2) (h a)
    have := orth_of_mem_X F (fun b => hw b.castSucc) k
    rw [map_sub, LinearMap.sub_apply, hw a, sub_zero] at this
    exact this

end GlobalTheory.DegAsm.TermPair

namespace GlobalTheory.DegAsm
open GlobalTheory.ModIdent TermPair

theorem trip_of_terms : ∀ (K V W : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) (HW : Formalism.HermitianLatticeCounting.S6.HermSpace K W) (e : W →ₗ[K] V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), ∀ (F G G' : FlagD H r) (𝔡 : Ideal (𝓞 K)) (N N' : NF H r) (g : ℕ) (Λ Λ' : Submodule (𝓞 K) V) (γ γ' : V ≃ₗ[K] V) (h h' : W ≃ₗ[K] W), 1 ≤ g → IsEmb F HW e → Adapt F G 𝔡 N → Adapt F G' 𝔡 N' → N.IsTerm g Λ → N'.IsTerm g Λ → γ ∈ isomGrp H → γ' ∈ isomGrp H → (∀ a, G.e a = γ (F.e a) ∧ G'.e a = γ' (F.e a)) → γ • Λ' = Λ → γ' • Λ' = Λ → IsH F G e γ h → IsH F G' e γ' h' → (∀ x ∈ Λ ⊓ rs (𝓞 K) (perp H F.X), γ' (γ.symm x) - x ∈ smulLat (g : 𝓞 K) Λ ⊔ (Λ ⊓ rs (𝓞 K) F.X)) → (datOf F G e g Λ, datOf F G' e g Λ, h * h'⁻¹) ∈ Trip HW g (lat0 F e Λ) r (N.gI g Λ) (N'.gI g Λ) := by
  intro K V W _ _ _ _ _ _ _ _ _ _ _ _ _ H HW e hK r F G G' 𝔡 N N' g Λ Λ' γ γ' h h' hg he hN hN' hT hT' hγ hγ' hE
    hΛ hΛ' hh hh' hβ
  obtain ⟨k, hk, -, hku, hkl⟩ := GlobalTheory.T.exists_definiteSpace_isometry_of_adapted_pair K V W H HW e hK r F G 𝔡 N γ he hN hγ fun a => (hE a).1
  obtain ⟨k', hk', -, hku', hkl'⟩ := GlobalTheory.T.exists_definiteSpace_isometry_of_adapted_pair K V W H HW e hK r F G' 𝔡 N' γ' he hN' hγ' fun a => (hE a).2
  obtain rfl := hku h hh
  obtain rfl := hku' h' hh'
  have d1 := hkl g Λ'
  have d2 := hkl' g Λ'
  rw [hΛ] at d1
  rw [hΛ'] at d2
  obtain ⟨⟨hU, hF, hG⟩, hA⟩ :=
    ((adapt_invariants K V H hK r F G 𝔡 N hN).2.2.2.2.2.2.2.2 g Λ).1.1 hT
  have hA' : IsAdm G F Λ (g : 𝓞 K) := by
    refine isAdm_symm (fun a => ?_) hA
    refine Fin.lastCases ?_ (fun b => ?_) a
    · rw [hF.2, hG.2]
    · rw [hF.1, hG.1]
  have key : ∀ w : W, ∀ x ∈ Λ', e w - x ∈ F.X → ∃ n ∈ Λ, γ' x - γ x - (g : K) • n ∈ F.X := by
    intro w x hx hw
    have hxΛ : γ x ∈ Λ := hΛ ▸ (mem_smul_iff γ Λ' x).2 hx
    have hp : ∀ u ∈ G.X, H.B u (γ x) = 0 := by
      intro u hu
      obtain ⟨u, rfl⟩ := γ.surjective u
      rw [mem_X_iff fun a => (hE a).1] at hu
      rw [(mem_isomGrp H γ).1 hγ]
      have a1 := X_iso F hu hw
      have a2 := orth_of_mem_X F (fun b => (he.2 (e w)).2 (Submodule.mem_sup_left ⟨w, rfl⟩) b.castSucc) hu
      rw [map_sub, a2] at a1
      simpa using a1
    obtain ⟨m, hm, hmp⟩ := perp_lift hg hU hA' hxΛ hp
    obtain ⟨s, hs, t, ⟨-, ht⟩, hst⟩ := Submodule.mem_sup.1 (hβ _ ⟨Λ.sub_mem hxΛ (gsmul_mem g hm), hmp⟩)
    obtain ⟨n, hn, rfl⟩ := (mem_smulLat g Λ s).1 hs
    have hm' : γ' (γ.symm m) ∈ Λ := by
      rw [← hΛ', mem_smul_iff, ← mem_smul_iff γ, hΛ]
      simpa using hm
    refine ⟨n + γ' (γ.symm m) - m, Λ.sub_mem (Λ.add_mem hn hm') hm, ?_⟩
    have ht : t ∈ F.X := ht
    convert ht using 1
    simp only [map_sub, map_smul, LinearEquiv.symm_apply_apply] at hst
    rw [smul_sub, smul_add, eq_sub_of_add_eq' hst]
    abel
  refine ⟨(GlobalTheory.T.embeddedDatum_of_term_definiteSpace K V W H HW e hK r F G 𝔡 N g Λ hg he hN hT).1,
    (GlobalTheory.T.embeddedDatum_of_term_definiteSpace K V W H HW e hK r F G' 𝔡 N' g Λ hg he hN' hT').1, mul_mem hk (inv_mem hk'), ?_, fun y v => ?_⟩
  · show imLat (h * h'⁻¹) (datOf F G' e g Λ).1 = (datOf F G e g Λ).1
    rw [d1, d2]
    unfold imLat
    rw [Formalism.HermitianLatticesTheory.genusBasic_gmap_mul, Formalism.HermitianLatticesTheory.genusBasic_gmap_inv]
  · obtain ⟨w, rfl⟩ := h'.surjective y
    have e1 := mem_graph he (geom hK hN).1 (geom hK hN).2 (fun a => (hE a).1) hh g Λ' w v
    have e2 := mem_graph he (geom hK hN').1 (geom hK hN').2 (fun a => (hE a).2) hh' g Λ' w v
    rw [hΛ] at e1
    rw [hΛ'] at e2
    have e3 : (h * h'⁻¹) (h' w) = h w := by simp
    show (h' w, v) ∈ (datOf F G' e g Λ).2 ↔ ((h * h'⁻¹) (h' w), v) ∈ (datOf F G e g Λ).2
    rw [e3, e1, e2]
    constructor
    · rintro ⟨x, hx, m, hm, h1, h2⟩
      obtain ⟨n, hn, h3⟩ := key w x hx h1
      refine ⟨x, hx, m + n, Λ.add_mem hm hn, h1, ?_⟩
      have := F.X.add_mem h2 h3
      convert this using 1
      rw [smul_add]; abel
    · rintro ⟨x, hx, m, hm, h1, h2⟩
      obtain ⟨n, hn, h3⟩ := key w x hx h1
      refine ⟨x, hx, m - n, Λ.sub_mem hm hn, h1, ?_⟩
      have := F.X.sub_mem h2 h3
      convert this using 1
      rw [smul_sub]; abel

end GlobalTheory.DegAsm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumFibreTwoIndexEncardBound
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumFibreTwoIndexEncardBound
open scoped ENNReal Classical

namespace GlobalTheory

theorem sum_fibre_two_index_bound : ∀ (α Θ : Type) (S : Finset α) (xf yf : α → ℕ) (Φ : α → Θ) (Tr : ℕ → ℕ → Set Θ) (f : α → ℝ) (B₁ B₂ : ℕ → ℝ) (R₁ R₂ : Finset ℕ), (∀ a ∈ S, 0 ≤ f a) → (∀ a ∈ S, xf a ∈ R₁ ∧ yf a ∈ R₂ ∧ Φ a ∈ Tr (xf a) (yf a)) → (∀ a ∈ S, ∑ b ∈ S.filter (fun b => Φ b = Φ a ∧ xf b = xf a ∧ yf b = yf a), f b ≤ B₁ (xf a) * B₂ (yf a)) → ENNReal.ofReal (∑ a ∈ S, f a) ≤ ∑ x ∈ R₁, ∑ y ∈ R₂, (((Tr x y).encard : ℕ∞) : ℝ≥0∞) * ENNReal.ofReal (B₁ x * B₂ y) := by
  intro α Θ S xf yf Φ Tr f B₁ B₂ R₁ R₂ hf hR hB
  rw [ENNReal.ofReal_sum_of_nonneg hf]
  have h1 : ∑ a ∈ S, ENNReal.ofReal (f a) = ∑ x ∈ R₁, ∑ y ∈ R₂,
      ∑ a ∈ (S.filter (fun a => xf a = x)).filter (fun a => yf a = y), ENNReal.ofReal (f a) := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := xf) (t := R₁) (fun a ha => (hR a ha).1)]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [← Finset.sum_fiberwise_of_maps_to (g := yf) (t := R₂)
      (fun a ha => (hR a (Finset.mem_filter.1 ha).1).2.1)]
  rw [h1]
  refine Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun y _ => ?_))
  have hmem : ∀ a ∈ (S.filter (fun a => xf a = x)).filter (fun a => yf a = y),
      a ∈ S ∧ xf a = x ∧ yf a = y := by
    intro a ha
    simp only [Finset.mem_filter] at ha
    exact ⟨ha.1.1, ha.1.2, ha.2⟩
  generalize hS' : (S.filter (fun a => xf a = x)).filter (fun a => yf a = y) = S' at hmem ⊢
  rw [← Finset.sum_fiberwise_of_maps_to (g := Φ) (t := S'.image Φ)
    (fun a ha => Finset.mem_image_of_mem Φ ha)]
  have hfib : ∀ t ∈ S'.image Φ, ∑ a ∈ S'.filter (fun a => Φ a = t), ENNReal.ofReal (f a)
      ≤ ENNReal.ofReal (B₁ x * B₂ y) := by
    intro t ht
    obtain ⟨a₀, ha₀, rfl⟩ := Finset.mem_image.1 ht
    obtain ⟨ha₀S, hx₀, hy₀⟩ := hmem a₀ ha₀
    have hsub : S'.filter (fun a => Φ a = Φ a₀)
        = S.filter (fun b => Φ b = Φ a₀ ∧ xf b = xf a₀ ∧ yf b = yf a₀) := by
      subst hS'
      ext b
      simp only [Finset.mem_filter]
      rw [hx₀, hy₀]
      tauto
    rw [hsub, ← ENNReal.ofReal_sum_of_nonneg (fun b hb => hf b (Finset.mem_filter.1 hb).1)]
    exact (ENNReal.ofReal_le_ofReal (hB a₀ ha₀S)).trans_eq (by rw [hx₀, hy₀])
  calc ∑ t ∈ S'.image Φ, ∑ a ∈ S'.filter (fun a => Φ a = t), ENNReal.ofReal (f a)
      ≤ ∑ t ∈ S'.image Φ, ENNReal.ofReal (B₁ x * B₂ y) := Finset.sum_le_sum hfib
    _ = ((S'.image Φ).card : ℝ≥0∞) * ENNReal.ofReal (B₁ x * B₂ y) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (((Tr x y).encard : ℕ∞) : ℝ≥0∞) * ENNReal.ofReal (B₁ x * B₂ y) := by
      gcongr
      have hsubT : ((S'.image Φ : Finset Θ) : Set Θ) ⊆ Tr x y := by
        intro t ht
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 ht)
        obtain ⟨haS, hxa, hya⟩ := hmem a ha
        have h := (hR a haS).2.2
        rw [hxa, hya] at h
        exact h
      have hc := Set.encard_le_encard hsubT
      rw [Set.encard_coe_eq_coe_finsetCard] at hc
      rw [← ENat.toENNReal_coe]
      exact ENat.toENNReal_le.2 hc

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumFibreTwoIndexEncardBoundStatement
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_fibre_two_index_encard_bound : ∀ (α Θ : Type) (S : Finset α) (xf yf : α → ℕ) (Φ : α → Θ) (Tr : ℕ → ℕ → Set Θ) (f : α → ℝ) (B₁ B₂ : ℕ → ℝ) (R₁ R₂ : Finset ℕ), (∀ a ∈ S, 0 ≤ f a) → (∀ a ∈ S, xf a ∈ R₁ ∧ yf a ∈ R₂ ∧ Φ a ∈ Tr (xf a) (yf a)) → (∀ a ∈ S, ∑ b ∈ S.filter (fun b => Φ b = Φ a ∧ xf b = xf a ∧ yf b = yf a), f b ≤ B₁ (xf a) * B₂ (yf a)) → ENNReal.ofReal (∑ a ∈ S, f a) ≤ ∑ x ∈ R₁, ∑ y ∈ R₂, (((Tr x y).encard : ℕ∞) : ℝ≥0∞) * ENNReal.ofReal (B₁ x * B₂ y) := by
  first | exact @GlobalTheory.sum_fibre_two_index_bound | exact GlobalTheory.sum_fibre_two_index_bound | (intros; apply GlobalTheory.sum_fibre_two_index_bound <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermPairsRowLatticeCountedViaEmbeddings
noncomputable section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.RowsConc
namespace GlobalTheory.TypeAsm.PerRow
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem sum_le_encard_fibres {α Θ : Type} (S : Finset α) (xf yf : α → ℕ) (Φ : α → Θ) (Tr : ℕ → ℕ → Set Θ) (f : α → ℝ)
    (B₁ B₂ : ℕ → ℝ) (R₁ R₂ : Finset ℕ) (hf : ∀ a ∈ S, 0 ≤ f a)
    (hR : ∀ a ∈ S, xf a ∈ R₁ ∧ yf a ∈ R₂ ∧ Φ a ∈ Tr (xf a) (yf a))
    (hB : ∀ a ∈ S, ∑ b ∈ S.filter (fun b => Φ b = Φ a ∧ xf b = xf a ∧ yf b = yf a), f b ≤ B₁ (xf a) * B₂ (yf a)) :
    ENNReal.ofReal (∑ a ∈ S, f a) ≤
      ∑ x ∈ R₁, ∑ y ∈ R₂, (((Tr x y).encard : ℕ∞) : ℝ≥0∞) * ENNReal.ofReal (B₁ x * B₂ y) :=
  GlobalTheory.T.sum_fibre_two_index_encard_bound α Θ S xf yf Φ Tr f B₁ B₂ R₁ R₂ hf hR hB

theorem sum_pairs_le_classes (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (hS : Std D large₂)
    (W : Submodule D.host.E (VS D).V) (HW : Formalism.HermitianLatticeCounting.S6.HermSpace D.host.E W)
    (he : GlobalTheory.DegAsm.IsEmb (F0 X u) HW W.subtype) (Λ : Submodule (𝓞 D.host.E) (VS D).V) (h : GTu Y u → (W ≃ₗ[D.host.E] W))
    (hh : ∀ t ∈ relSet Y u, GlobalTheory.DegAsm.IsH (F0 X u) (Ft t) W.subtype t.lin (h t)) (Sf : Finset (GTu Y u × GTu Y u))
    (hSf : ∀ p ∈ Sf, p ∈ (Y.tO u u).allPairs (relSet Y u) ∧ p.1.lam = Λ)
    (hη : ∀ p ∈ Sf, ∀ q ∈ Sf, h p.1 * (h p.2)⁻¹ = h q.1 * (h q.2)⁻¹) :
    ∑ p ∈ Sf, wRow D (X.Fu u) p.1.lam' * (omT p.1 * omT p.2) ≤
      (∑ b ∈ Sf.image (fun p => frCls Λ p.1), clsOm Y u Λ b) * ∑ b ∈ Sf.image (fun p => frCls Λ p.2), clsOm Y u Λ b :=
  GlobalTheory.T.sum_pairs_definiteIsometry_le_frameClasses D large₂ X Y u hS W HW he Λ h hh Sf hSf hη

theorem sum_classes_le (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (hS : Std D large₂)
    (W : Submodule D.host.E (VS D).V) (HW : Formalism.HermitianLatticeCounting.S6.HermSpace D.host.E W)
    (he : GlobalTheory.DegAsm.IsEmb (F0 X u) HW W.subtype) (Λ : Submodule (𝓞 D.host.E) (VS D).V) (j x : ℕ) (δ : ℕ → D.host.E)
    (d : Submodule (𝓞 D.host.E) W × Submodule (𝓞 D.host.E) (W × W)) (N : GTu Y u → GlobalTheory.DegCnt.NF (HV D) D.R.rS)
    (A : Finset (GTu Y u)) (hne : A.Nonempty)
    (hA : ∀ t ∈ A, t ∈ relSet Y u ∧ t.lam = Λ ∧ jT t = j ∧ labT t = δ ∧ AdT t (N t) ∧ (N t).IsTerm (gS D) Λ ∧
      (N t).gI (gS D) Λ = x ∧ GlobalTheory.DegAsm.datOf (F0 X u) (Ft t) W.subtype (gS D) Λ = d) :
    ∑ b ∈ A.image (frCls Λ), clsOm Y u Λ b ≤
      GlobalTheory.DegAsm.datBd D.host.E D.R.k D.R.rS (k2Del D j δ) (DbL D j δ) (NT D u) x :=
  GlobalTheory.T.sum_frameClassWeights_le_datumBound D large₂ X Y u hS W HW he Λ j x δ d N A hne hA

theorem termData (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (hS : Std D large₂)
    (W : Submodule D.host.E (VS D).V) (HW : Formalism.HermitianLatticeCounting.S6.HermSpace D.host.E W)
    (he : GlobalTheory.DegAsm.IsEmb (F0 X u) HW W.subtype) (t : GTu Y u) (ht : t ∈ relSet Y u) :
    ∃ (N : GlobalTheory.DegCnt.NF (HV D) D.R.rS) (h : W ≃ₗ[D.host.E] W), AdT t N ∧ N.IsTerm (gS D) t.lam ∧ N.j = jT t ∧
      N.T = Tu D u ∧ N.Del = k2Del D (jT t) (labT t) ∧ N.Db = DbL D (jT t) (labT t) ∧ 1 ≤ N.Del ∧ 1 ≤ N.Db ∧
      1 ≤ N.gI (gS D) t.lam ∧ (N.gI (gS D) t.lam : ℝ) ≤ N.Del ∧
      GlobalTheory.DegAsm.lab (F0 X u) (Ft t) (jT t) = (fun l => star (labT t l)) ∧
      h ∈ GlobalTheory.HermLat.isomGrp HW ∧ GlobalTheory.DegAsm.IsH (F0 X u) (Ft t) W.subtype t.lin h ∧
      Module.finrank D.host.E W = D.R.k := by
  obtain ⟨N, hA, hj, hT⟩ := GlobalTheory.T.exists_adaptedNormalForm_relevantTerm D large₂ X Y u hS t ht
  have hterm := GlobalTheory.T.rowLattice_term_adaptedNormalForm D large₂ X Y u hS t N hA
  obtain ⟨-, -, hDel, hDb, hlab⟩ := GlobalTheory.T.adaptedNormalForm_normsMinors_eq_label D large₂ X Y u hS t N hA
  obtain ⟨hK, -, -, -, -, -, -, -, -, -, hfin, hg2, -⟩ := GlobalTheory.T.unitaryHostFieldArithmeticConditions D large₂ hS
  have hg : 1 ≤ gS D := by omega
  obtain ⟨-, hx1, hxD, -, hdim⟩ := GlobalTheory.T.embeddedDatum_of_term_definiteSpace D.host.E (VS D).V W (HV D) HW W.subtype hK D.R.rS (F0 X u) (Ft t)
    (dI D) N (gS D) t.lam hg he hA hterm
  obtain ⟨𝔠, -, hDb1, hDel1, -⟩ := GlobalTheory.T.exists_star_stable_ideal_absorbing_minors D.host.E (VS D).V (HV D) hK D.R.rS N (gS D) t.lam hg hterm
  have hiso : t.lin ∈ GlobalTheory.HermLat.isomGrp (HV D) := fun x y => t.rep.2.2.1 x y
  obtain ⟨h, hh, hH, -, -⟩ := GlobalTheory.T.exists_definiteSpace_isometry_of_adapted_pair D.host.E (VS D).V W (HV D) HW W.subtype hK D.R.rS (F0 X u) (Ft t) (dI D) N
    t.lin he hA hiso (fun a => GlobalTheory.TypeAsm.FibProof.Ft_e t a)
  exact ⟨N, h, hA, hterm, hj, hT, hDel, hDb, hDel1, hDb1, hx1, hxD, hlab, hh, hH, by omega⟩

theorem pairTrip (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (hS : Std D large₂)
    (W : Submodule D.host.E (VS D).V) (HW : Formalism.HermitianLatticeCounting.S6.HermSpace D.host.E W)
    (he : GlobalTheory.DegAsm.IsEmb (F0 X u) HW W.subtype) (p : GTu Y u × GTu Y u) (hp : p ∈ (Y.tO u u).allPairs (relSet Y u))
    (N₁ N₂ : GlobalTheory.DegCnt.NF (HV D) D.R.rS) (h₁ h₂ : W ≃ₗ[D.host.E] W) (hA₁ : AdT p.1 N₁) (hA₂ : AdT p.2 N₂)
    (ht₁ : N₁.IsTerm (gS D) p.1.lam) (ht₂ : N₂.IsTerm (gS D) p.2.lam)
    (hH₁ : GlobalTheory.DegAsm.IsH (F0 X u) (Ft p.1) W.subtype p.1.lin h₁)
    (hH₂ : GlobalTheory.DegAsm.IsH (F0 X u) (Ft p.2) W.subtype p.2.lin h₂) :
    p.1.lam = p.2.lam ∧
      (GlobalTheory.DegAsm.datOf (F0 X u) (Ft p.1) W.subtype (gS D) p.1.lam,
        GlobalTheory.DegAsm.datOf (F0 X u) (Ft p.2) W.subtype (gS D) p.1.lam, h₁ * h₂⁻¹) ∈
        GlobalTheory.DegCnt.Trip HW (gS D) (GlobalTheory.DegAsm.lat0 (F0 X u) W.subtype p.1.lam) D.R.rS (N₁.gI (gS D) p.1.lam)
          (N₂.gI (gS D) p.1.lam) := by
  obtain ⟨hK, -, -, -, -, -, -, -, -, -, -, hg2, -⟩ := GlobalTheory.T.unitaryHostFieldArithmeticConditions D large₂ hS
  have hg : 1 ≤ gS D := by omega
  obtain ⟨hl, hl', hc⟩ := GlobalTheory.T.termsOverRow_compatible D X Y u p ⟨trivial, trivial, hp.2.2⟩
  refine ⟨hl, ?_⟩
  have hi₁ : p.1.lin ∈ GlobalTheory.HermLat.isomGrp (HV D) := fun x y => p.1.rep.2.2.1 x y
  have hi₂ : p.2.lin ∈ GlobalTheory.HermLat.isomGrp (HV D) := fun x y => p.2.rep.2.2.1 x y
  have hΛ₁ : p.1.lin • p.1.lam' = p.1.lam := by
    rw [← GlobalTheory.TypeAsm.FibProof.gmap_eq_smul]; exact p.1.rep.2.2.2.1
  have hΛ₂ : p.2.lin • p.1.lam' = p.1.lam := by
    rw [hl, hl', ← GlobalTheory.TypeAsm.FibProof.gmap_eq_smul]; exact p.2.rep.2.2.2.1
  rw [← hl] at ht₂
  exact GlobalTheory.DegAsm.trip_of_terms D.host.E (VS D).V W (HV D) HW W.subtype hK D.R.rS (F0 X u) (Ft p.1) (Ft p.2) (dI D)
    N₁ N₂ (gS D) p.1.lam p.1.lam' p.1.lin p.2.lin h₁ h₂ hg he hA₁ hA₂ ht₁ ht₂ hi₁ hi₂
    (fun a => ⟨GlobalTheory.TypeAsm.FibProof.Ft_e p.1 a, GlobalTheory.TypeAsm.FibProof.Ft_e p.2 a⟩) hΛ₁ hΛ₂ hH₁ hH₂ hc

end GlobalTheory.TypeAsm.PerRow

namespace GlobalTheory.TypeAsm
open PerRow

theorem perRowC : PerRowC := by
  intro D large₂ X Y u hS W HW he Λ j' j'' δ' δ'' S hS'
  rcases S.eq_empty_or_nonempty with rfl | ⟨p₀, hp₀⟩
  · simp
  obtain ⟨hK, -, -, -, -, -, -, -, -, -, -, hg2, -⟩ := GlobalTheory.T.unitaryHostFieldArithmeticConditions D large₂ hS
  obtain ⟨N₀, h₀, -⟩ := termData D large₂ X Y u hS W HW he p₀.1 (hS' p₀ hp₀).1.1
  have hdata : ∀ t : GTu Y u, ∃ (N : GlobalTheory.DegCnt.NF (HV D) D.R.rS) (h : W ≃ₗ[D.host.E] W), t ∈ relSet Y u →
      AdT t N ∧ N.IsTerm (gS D) t.lam ∧ N.j = jT t ∧
      N.T = Tu D u ∧ N.Del = k2Del D (jT t) (labT t) ∧ N.Db = DbL D (jT t) (labT t) ∧ 1 ≤ N.Del ∧ 1 ≤ N.Db ∧
      1 ≤ N.gI (gS D) t.lam ∧ (N.gI (gS D) t.lam : ℝ) ≤ N.Del ∧
      GlobalTheory.DegAsm.lab (F0 X u) (Ft t) (jT t) = (fun l => star (labT t l)) ∧
      h ∈ GlobalTheory.HermLat.isomGrp HW ∧ GlobalTheory.DegAsm.IsH (F0 X u) (Ft t) W.subtype t.lin h ∧
      Module.finrank D.host.E W = D.R.k := by
    intro t
    by_cases ht : t ∈ relSet Y u
    · obtain ⟨N, h, hp⟩ := termData D large₂ X Y u hS W HW he t ht
      exact ⟨N, h, fun _ => hp⟩
    · exact ⟨N₀, h₀, fun h => absurd h ht⟩
  choose N h hNh using hdata

  have hpair : ∀ p ∈ S, p.2.lam = Λ ∧
      (GlobalTheory.DegAsm.datOf (F0 X u) (Ft p.1) W.subtype (gS D) Λ,
        GlobalTheory.DegAsm.datOf (F0 X u) (Ft p.2) W.subtype (gS D) Λ, h p.1 * (h p.2)⁻¹) ∈
        GlobalTheory.DegCnt.Trip HW (gS D) (GlobalTheory.DegAsm.lat0 (F0 X u) W.subtype Λ) D.R.rS ((N p.1).gI (gS D) Λ)
          ((N p.2).gI (gS D) Λ) ∧
      (N p.1).gI (gS D) Λ ∈ Finset.Icc 1 ⌊k2Del D j' δ'⌋₊ ∧ (N p.2).gI (gS D) Λ ∈ Finset.Icc 1 ⌊k2Del D j'' δ''⌋₊ := by
    intro p hp
    obtain ⟨hpa, hl, hj1, hj2, hd1, hd2⟩ := hS' p hp
    obtain ⟨a1, a2, -, -, a5, -, -, -, a9, a10, -, -, a13, -⟩ := hNh p.1 hpa.1
    obtain ⟨b1, b2, -, -, b5, -, -, -, b9, b10, -, -, b13, -⟩ := hNh p.2 hpa.2.1
    obtain ⟨hl2, htr⟩ := pairTrip D large₂ X Y u hS W HW he p hpa (N p.1) (N p.2) (h p.1) (h p.2) a1 b1 a2 b2 a13 b13
    rw [hl] at htr hl2 a9 a10
    rw [← hl2] at b9 b10
    refine ⟨hl2.symm, htr, Finset.mem_Icc.2 ⟨a9, Nat.le_floor ?_⟩, Finset.mem_Icc.2 ⟨b9, Nat.le_floor ?_⟩⟩
    · rw [← hj1, ← hd1, ← a5]; exact a10
    · rw [← hj2, ← hd2, ← b5]; exact b10
  refine sum_le_encard_fibres S (fun p => (N p.1).gI (gS D) Λ) (fun p => (N p.2).gI (gS D) Λ)
    (fun p => (GlobalTheory.DegAsm.datOf (F0 X u) (Ft p.1) W.subtype (gS D) Λ,
        GlobalTheory.DegAsm.datOf (F0 X u) (Ft p.2) W.subtype (gS D) Λ, h p.1 * (h p.2)⁻¹))
    (fun x y => GlobalTheory.DegCnt.Trip HW (gS D) (GlobalTheory.DegAsm.lat0 (F0 X u) W.subtype Λ) D.R.rS x y)
    (fun p => wRow D (X.Fu u) p.1.lam' * (omT p.1 * omT p.2))
    (fun x => GlobalTheory.DegAsm.datBd D.host.E D.R.k D.R.rS (k2Del D j' δ') (DbL D j' δ') (NT D u) x)
    (fun x => GlobalTheory.DegAsm.datBd D.host.E D.R.k D.R.rS (k2Del D j'' δ'') (DbL D j'' δ'') (NT D u) x) _ _ ?_
    (fun p hp => ⟨(hpair p hp).2.2.1, (hpair p hp).2.2.2, (hpair p hp).2.1⟩) ?_
  · intro p _
    have hw : 0 ≤ wRow D (X.Fu u) p.1.lam' := by unfold wRow; positivity
    have ho : ∀ t : GTu Y u, 0 ≤ omT t := fun t =>
      ((GlobalTheory.DegAsm.WeightInf.main D.host.E (VS D).V (HV D) hK D.R.rS).2 _ _ _ _).1
    exact mul_nonneg hw (mul_nonneg (ho _) (ho _))
  · intro a ha
    have key : ∀ Sf : Finset (GTu Y u × GTu Y u), (∀ q ∈ Sf, q ∈ S ∧ GlobalTheory.DegAsm.datOf (F0 X u) (Ft q.1) W.subtype (gS D) Λ =
        GlobalTheory.DegAsm.datOf (F0 X u) (Ft a.1) W.subtype (gS D) Λ ∧
        GlobalTheory.DegAsm.datOf (F0 X u) (Ft q.2) W.subtype (gS D) Λ =
        GlobalTheory.DegAsm.datOf (F0 X u) (Ft a.2) W.subtype (gS D) Λ ∧ h q.1 * (h q.2)⁻¹ = h a.1 * (h a.2)⁻¹ ∧
        (N q.1).gI (gS D) Λ = (N a.1).gI (gS D) Λ ∧ (N q.2).gI (gS D) Λ = (N a.2).gI (gS D) Λ) → a ∈ Sf →
        ∑ p ∈ Sf, wRow D (X.Fu u) p.1.lam' * (omT p.1 * omT p.2) ≤
          GlobalTheory.DegAsm.datBd D.host.E D.R.k D.R.rS (k2Del D j' δ') (DbL D j' δ') (NT D u) ((N a.1).gI (gS D) Λ) *
          GlobalTheory.DegAsm.datBd D.host.E D.R.k D.R.rS (k2Del D j'' δ'') (DbL D j'' δ'') (NT D u) ((N a.2).gI (gS D) Λ) := by
      intro Sf hmem haf
      have h1 := sum_pairs_le_classes D large₂ X Y u hS W HW he Λ h (fun t ht => (hNh t ht).2.2.2.2.2.2.2.2.2.2.2.2.1) Sf
        (fun p hp => ⟨(hS' p (hmem p hp).1).1, (hS' p (hmem p hp).1).2.1⟩)
        (fun p hp q hq => ((hmem p hp).2.2.2.1).trans ((hmem q hq).2.2.2.1).symm)
      have hA1 : ∀ t ∈ Sf.image Prod.fst, t ∈ relSet Y u ∧ t.lam = Λ ∧ jT t = j' ∧ labT t = δ' ∧ AdT t (N t) ∧
          (N t).IsTerm (gS D) Λ ∧ (N t).gI (gS D) Λ = (N a.1).gI (gS D) Λ ∧
          GlobalTheory.DegAsm.datOf (F0 X u) (Ft t) W.subtype (gS D) Λ = GlobalTheory.DegAsm.datOf (F0 X u) (Ft a.1) W.subtype (gS D) Λ := by
        intro t ht
        obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 ht
        obtain ⟨hqS, c1, -, -, c4, -⟩ := hmem q hq
        obtain ⟨hpa, hl, hj1, -, hd1, -⟩ := hS' q hqS
        obtain ⟨a1, a2, -⟩ := hNh q.1 hpa.1
        rw [hl] at a2
        exact ⟨hpa.1, hl, hj1, hd1, a1, a2, c4, c1⟩
      have hA2 : ∀ t ∈ Sf.image Prod.snd, t ∈ relSet Y u ∧ t.lam = Λ ∧ jT t = j'' ∧ labT t = δ'' ∧ AdT t (N t) ∧
          (N t).IsTerm (gS D) Λ ∧ (N t).gI (gS D) Λ = (N a.2).gI (gS D) Λ ∧
          GlobalTheory.DegAsm.datOf (F0 X u) (Ft t) W.subtype (gS D) Λ = GlobalTheory.DegAsm.datOf (F0 X u) (Ft a.2) W.subtype (gS D) Λ := by
        intro t ht
        obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 ht
        obtain ⟨hqS, -, c2, -, -, c5⟩ := hmem q hq
        obtain ⟨hpa, -, -, hj2, -, hd2⟩ := hS' q hqS
        have hl2 := (hpair q hqS).1
        obtain ⟨b1, b2, -⟩ := hNh q.2 hpa.2.1
        rw [hl2] at b2
        exact ⟨hpa.2.1, hl2, hj2, hd2, b1, b2, c5, c2⟩
      have h2 := sum_classes_le D large₂ X Y u hS W HW he Λ j' _ δ' _ N (Sf.image Prod.fst) ⟨a.1, Finset.mem_image_of_mem _ haf⟩ hA1
      have h3 := sum_classes_le D large₂ X Y u hS W HW he Λ j'' _ δ'' _ N (Sf.image Prod.snd) ⟨a.2, Finset.mem_image_of_mem _ haf⟩ hA2
      rw [Finset.image_image] at h2 h3
      have n2 : 0 ≤ ∑ b ∈ Sf.image (fun p => frCls Λ p.2), clsOm Y u Λ b :=
        Finset.sum_nonneg fun b _ => clsOm_nonneg Y u Λ hK b
      have n1 : 0 ≤ ∑ b ∈ Sf.image (fun p => frCls Λ p.1), clsOm Y u Λ b :=
        Finset.sum_nonneg fun b _ => clsOm_nonneg Y u Λ hK b
      exact h1.trans (mul_le_mul h2 h3 n2 (n1.trans h2))

    rw [Finset.filter_congr_decidable]
    refine key _ (fun q hq => ?_) (Finset.mem_filter.2 ⟨ha, rfl, rfl, rfl⟩)
    obtain ⟨hqS, he1, he2, he3⟩ := Finset.mem_filter.1 hq
    obtain ⟨c1, c2⟩ := Prod.mk.inj he1
    obtain ⟨c2, c3⟩ := Prod.mk.inj c2
    exact ⟨hqS, c1, c2, c3, he2, he3⟩

end GlobalTheory.TypeAsm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermPairsRowLatticeCountedViaEmbeddingsStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.termPairs_rowLattice_counted_via_embeddings : GlobalTheory.TypeAsm.PerRowC := by
  first | exact @GlobalTheory.TypeAsm.perRowC | exact GlobalTheory.TypeAsm.perRowC | (intros; apply GlobalTheory.TypeAsm.perRowC <;> assumption)
end
