module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniquePlace
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlVolEqTsumSlabVol
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsCoordinatesInverseFirstColumnInfiniteGL
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalBlockFrameOfComplexFlag
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeftQuotientCovolumeWithDensityDetNormSq
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeNonzeroVectorPairNormalForms

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DetNormSqEqOneOfMemLatticeAut
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DetNormSqEqOneOfMemLatticeAut
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.OrbitTerm

namespace GlobalTheory.OrbitTerm

theorem _root_.GlobalTheory.OrbitTerm.detNorm_eq_one_of_mem_autGL : ∀ (E : Type) [Field E] [NumberField E],
    IsTotallyComplex E → ∀ (j : ℕ) (Λ : Submodule (𝓞 E) (Fin j → E)), Submodule.IsFullLattice E Λ →
      ∀ γ ∈ _root_.GlobalTheory.FlagMeas.autGL E j Λ, _root_.GlobalTheory.FlagMeas.detNorm E j γ = 1 := by
  intro E _ _ hE j Λ hΛ γ hγ
  obtain ⟨κ, hκ, hcov⟩ := (_root_.GlobalTheory.LatFacts.lattice_facts E hE j).1 Λ hΛ
  have hpos := _root_.GlobalTheory.OrbitTerm.detNorm_pos_of_mem_autGL hγ
  have h1 := (hcov γ hpos).2.1
  have h2 := (hcov (_root_.GlobalTheory.OrbitTerm.oneInf E j) (by
    rw [_root_.GlobalTheory.OrbitTerm.detNorm_oneInf]; exact one_pos)).2.1
  rw [_root_.GlobalTheory.OrbitTerm.detNorm_oneInf, div_one] at h2
  have hmul := _root_.GlobalTheory.FlagBase.Test.latAt_aut_mul E j Λ hγ (_root_.GlobalTheory.OrbitTerm.oneInf E j)
  rw [_root_.GlobalTheory.OrbitTerm.mul_oneInf] at hmul
  rw [hmul, h2] at h1
  field_simp at h1
  linarith

end GlobalTheory.OrbitTerm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DetNormSqEqOneOfMemLatticeAutStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.OrbitTerm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.detNorm_eq_one_of_mem_autGL_var : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ (j : ℕ) (Λ : Submodule (𝓞 E) (Fin j → E)), Submodule.IsFullLattice E Λ → ∀ γ ∈ autGL E j Λ, detNorm E j γ = 1 := by
  intro E _ _ hE j Λ hΛ γ hγ
  letI := hΛ
  exact GlobalTheory.OrbitTerm.detNorm_eq_one_of_mem_autGL E hE j Λ inferInstance γ hγ
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasureInterTranslateEqZeroOfCovolume
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasureInterTranslateEqZeroOfCovolume
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.OrbitTerm

namespace GlobalTheory.StrictDomain

theorem null_of_translate_disjoint {X : Type} [Mul X] [MeasurableSpace X] (S : Set X) (μ : Measure X)
    (U D : Set X) (hc : S.Countable) (hm : ∀ γ ∈ S, Measurable fun x => γ * x)
    (hinv : ∀ γ ∈ S, μ.map (fun x => γ * x) = μ)
    (hmul : ∀ γ ∈ S, ∀ δ ∈ S, ∃ ε ∈ S, ∀ x, ε * x = γ * (δ * x))
    (hi : ∀ γ ∈ S, ∃ δ ∈ S, (∀ x, δ * (γ * x) = x) ∧ ∀ x, γ * (δ * x) = x)
    (hU : MeasurableSet U) (hUS : ∀ γ ∈ S, ∀ x ∈ U, γ * x ∈ U) (hDU : D ⊆ U)
    (hcov : ∀ A, MeasurableSet A → A ⊆ U → (∀ γ ∈ S, ∀ x ∈ A, γ * x ∈ A) →
      covol S μ A = μ (A ∩ D))
    (γ : X) (hγ : γ ∈ S) (B : Set X) (hB : MeasurableSet B) (hfin : μ B ≠ ⊤)
    (hBD : B ⊆ D) (hBγ : ∀ x ∈ B, γ * x ∈ D) (hdis : ∀ x ∈ B, γ * x ∉ B) : μ B = 0 := by
  obtain ⟨δ, hδ, hδγ, hγδ⟩ := hi γ hγ
  set A : Set X := U ∩ ⋃ ε ∈ S, (fun x => ε * x) ⁻¹' B with hA
  have hmemA : ∀ x, x ∈ A ↔ x ∈ U ∧ ∃ ε ∈ S, ε * x ∈ B := by
    intro x
    simp [hA]
  have hAm : MeasurableSet A :=
    hU.inter (MeasurableSet.biUnion hc fun ε hε => hm ε hε hB)
  have hAinv : ∀ η ∈ S, ∀ x ∈ A, η * x ∈ A := by
    intro η hη x hx
    obtain ⟨hxU, ε, hε, hεx⟩ := (hmemA x).1 hx
    obtain ⟨η', hη', h1, -⟩ := hi η hη
    obtain ⟨κ, hκ, hκe⟩ := hmul ε hε η' hη'
    exact (hmemA _).2 ⟨hUS η hη x hxU, κ, hκ, by rw [hκe, h1]; exact hεx⟩
  have hle : μ (A ∩ D) ≤ μ B := by
    rw [← hcov A hAm Set.inter_subset_left hAinv]
    unfold covol
    exact iInf_le_of_le B (iInf_le_of_le hB (iInf_le_of_le (fun x hx => ((hmemA x).1 hx).2) le_rfl))
  set B' : Set X := (fun x => δ * x) ⁻¹' B with hB'
  have hB'm : MeasurableSet B' := hm δ hδ hB
  have hB'μ : μ B' = μ B := by
    rw [hB', ← Measure.map_apply (hm δ hδ) hB, hinv δ hδ]
  have hdj : Disjoint B B' := by
    rw [Set.disjoint_left]
    intro x hx hx'
    have := hdis _ hx'
    rw [hγδ] at this
    exact this hx
  have hsub : B ∪ B' ⊆ A ∩ D := by
    rintro x (hx | hx)
    · obtain ⟨κ, hκ, hκe⟩ := hmul δ hδ γ hγ
      exact ⟨(hmemA x).2 ⟨hDU (hBD hx), κ, hκ, by rw [hκe, hδγ]; exact hx⟩, hBD hx⟩
    · have hxD : x ∈ D := by
        have := hBγ _ hx
        rwa [hγδ] at this
      exact ⟨(hmemA x).2 ⟨hDU hxD, δ, hδ, hx⟩, hxD⟩
  have h2 : μ B + μ B ≤ μ B + 0 := by
    calc μ B + μ B = μ (B ∪ B') := by rw [measure_union hdj hB'm, hB'μ]
      _ ≤ μ (A ∩ D) := measure_mono hsub
      _ ≤ μ B + 0 := by rw [add_zero]; exact hle
  exact le_antisymm ((ENNReal.add_le_add_iff_left hfin).1 h2) zero_le

theorem measure_inter_translate_eq_zero : ∀ (X : Type) [Mul X] [MeasurableSpace X] [MeasurableSpace.CountablySeparated X] (S : Set X) (μ : Measure X) [SigmaFinite μ] (U D : Set X), S.Countable → (∀ γ ∈ S, Measurable fun x => γ * x) → (∀ γ ∈ S, μ.map (fun x => γ * x) = μ) → (∀ γ ∈ S, ∀ δ ∈ S, ∃ ε ∈ S, ∀ x, ε * x = γ * (δ * x)) → (∀ γ ∈ S, ∃ δ ∈ S, (∀ x, δ * (γ * x) = x) ∧ ∀ x, γ * (δ * x) = x) → MeasurableSet U → (∀ γ ∈ S, ∀ x ∈ U, γ * x ∈ U) → MeasurableSet D → D ⊆ U → (∀ A, MeasurableSet A → A ⊆ U → (∀ γ ∈ S, ∀ x ∈ A, γ * x ∈ A) → covol S μ A = μ (A ∩ D)) → ∀ γ ∈ S, (∀ x ∈ U, γ * x ≠ x) → μ {x | x ∈ D ∧ γ * x ∈ D} = 0 := by
  intro X _ _ _ S μ _ U D hc hm hinv hmul hi hU hUS hD hDU hcov γ hγ hfree
  obtain ⟨V, hVm, hV⟩ := exists_seq_separating X MeasurableSet.univ (Set.univ : Set X)
  have key : ∀ (W : Set X), MeasurableSet W → ∀ m : ℕ,
      μ (D ∩ (fun x => γ * x) ⁻¹' D ∩ W ∩ (fun x => γ * x) ⁻¹' Wᶜ ∩ spanningSets μ m) = 0 := by
    intro W hW m
    refine null_of_translate_disjoint S μ U D hc hm hinv hmul hi hU hUS hDU hcov γ hγ _
      ((((hD.inter (hm γ hγ hD)).inter hW).inter (hm γ hγ hW.compl)).inter
        (measurableSet_spanningSets μ m))
      (ne_top_of_le_ne_top (measure_spanningSets_lt_top μ m).ne
        (measure_mono Set.inter_subset_right)) ?_ ?_ ?_
    · intro x hx
      exact hx.1.1.1.1
    · intro x hx
      exact hx.1.1.1.2
    · intro x hx hx'
      exact hx.1.2 hx'.1.1.2
  have hsub : {x | x ∈ D ∧ γ * x ∈ D} ⊆ ⋃ n : ℕ, ⋃ m : ℕ,
      ((D ∩ (fun x => γ * x) ⁻¹' D ∩ V n ∩ (fun x => γ * x) ⁻¹' (V n)ᶜ ∩ spanningSets μ m) ∪
       (D ∩ (fun x => γ * x) ⁻¹' D ∩ (V n)ᶜ ∩ (fun x => γ * x) ⁻¹' (V n)ᶜᶜ ∩ spanningSets μ m)) := by
    rintro x ⟨hx, hγx⟩
    have hne := hfree x (hDU hx)
    obtain ⟨n, hn⟩ : ∃ n, ¬ (γ * x ∈ V n ↔ x ∈ V n) := by
      by_contra h
      push_neg at h
      exact hne (hV _ (Set.mem_univ _) _ (Set.mem_univ _) h)
    have hm' : x ∈ ⋃ m, spanningSets μ m := by rw [iUnion_spanningSets]; exact Set.mem_univ _
    obtain ⟨m, hm'⟩ := Set.mem_iUnion.1 hm'
    refine Set.mem_iUnion.2 ⟨n, Set.mem_iUnion.2 ⟨m, ?_⟩⟩
    by_cases hxV : x ∈ V n
    · exact Or.inl ⟨⟨⟨⟨hx, hγx⟩, hxV⟩, fun h => hn ⟨fun _ => hxV, fun _ => h⟩⟩, hm'⟩
    · exact Or.inr ⟨⟨⟨⟨hx, hγx⟩, hxV⟩, fun h => hn ⟨fun h' => (h h').elim, fun h' => (hxV h').elim⟩⟩, hm'⟩
  refine measure_mono_null hsub (measure_iUnion_null fun n => measure_iUnion_null fun m => ?_)
  exact measure_union_null (key _ (hVm n) m) (key _ (hVm n).compl m)

end GlobalTheory.StrictDomain
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasureInterTranslateEqZeroOfCovolumeStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.OrbitTerm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measure_inter_translate_eq_zero_of_covolume : ∀ (X : Type) [Mul X] [MeasurableSpace X] [MeasurableSpace.CountablySeparated X] (S : Set X) (μ : Measure X) [SigmaFinite μ] (U D : Set X), S.Countable → (∀ γ ∈ S, Measurable fun x => γ * x) → (∀ γ ∈ S, μ.map (fun x => γ * x) = μ) → (∀ γ ∈ S, ∀ δ ∈ S, ∃ ε ∈ S, ∀ x, ε * x = γ * (δ * x)) → (∀ γ ∈ S, ∃ δ ∈ S, (∀ x, δ * (γ * x) = x) ∧ ∀ x, γ * (δ * x) = x) → MeasurableSet U → (∀ γ ∈ S, ∀ x ∈ U, γ * x ∈ U) → MeasurableSet D → D ⊆ U → (∀ A, MeasurableSet A → A ⊆ U → (∀ γ ∈ S, ∀ x ∈ A, γ * x ∈ A) → covol S μ A = μ (A ∩ D)) → ∀ γ ∈ S, (∀ x ∈ U, γ * x ≠ x) → μ {x | x ∈ D ∧ γ * x ∈ D} = 0 := by
  first | exact @GlobalTheory.StrictDomain.measure_inter_translate_eq_zero | exact GlobalTheory.StrictDomain.measure_inter_translate_eq_zero | (intros; apply GlobalTheory.StrictDomain.measure_inter_translate_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralIoiCompConstDivChangeOfVar
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralIoiCompConstDivChangeOfVar
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.OrbitTerm

namespace GlobalTheory

theorem lintegral_Ioi_comp_const_div_mul_div :
    ∀ (κ : ℝ), 0 < κ → ∀ w : ℝ → ENNReal, Measurable w →
      ∫⁻ t in Set.Ioi (0 : ℝ), w (κ / t) * ENNReal.ofReal t / ENNReal.ofReal t =
        ENNReal.ofReal κ * ∫⁻ t in Set.Ioi (0 : ℝ), w t / ENNReal.ofReal (t ^ 2) := by
  intro κ hκ w _hw
  have hκ0 : κ ≠ 0 := ne_of_gt hκ
  have himg : (fun u : ℝ => κ / u) '' Set.Ioi (0 : ℝ) = Set.Ioi (0 : ℝ) := by
    ext t
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact div_pos hκ hu
    · intro ht
      have ht0 : t ≠ 0 := ne_of_gt (Set.mem_Ioi.mp ht)
      refine ⟨κ / t, div_pos hκ ht, ?_⟩
      show κ / (κ / t) = t
      field_simp
  have hderiv : ∀ u ∈ Set.Ioi (0 : ℝ),
      HasDerivWithinAt (fun u : ℝ => κ / u) (-(κ / u ^ 2)) (Set.Ioi (0 : ℝ)) u := by
    intro u hu
    have hu0 : u ≠ 0 := ne_of_gt (Set.mem_Ioi.mp hu)
    have h := ((hasDerivAt_inv hu0).const_mul κ).hasDerivWithinAt (s := Set.Ioi (0 : ℝ))
    have hfun : (fun u : ℝ => κ / u) = fun y => κ * y⁻¹ := by
      funext y
      rw [div_eq_mul_inv]
    rw [hfun]
    exact h.congr_deriv (by ring)
  have hinj : Set.InjOn (fun u : ℝ => κ / u) (Set.Ioi (0 : ℝ)) := by
    intro a ha b hb hab
    have ha0 : a ≠ 0 := ne_of_gt (Set.mem_Ioi.mp ha)
    have hb0 : b ≠ 0 := ne_of_gt (Set.mem_Ioi.mp hb)
    have hab' : κ / a = κ / b := hab
    field_simp at hab'
    exact hab'.symm
  rw [← himg, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hderiv hinj,
    himg, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr_ae ((ae_restrict_iff' measurableSet_Ioi).2
    (Filter.Eventually.of_forall fun u hu => ?_))
  have hu : 0 < u := Set.mem_Ioi.mp hu
  have hu0 : u ≠ 0 := ne_of_gt hu
  have hκu : 0 < κ / u := div_pos hκ hu
  have hsq : 0 < u ^ 2 := by positivity
  have hinv : κ / (κ / u) = u := by field_simp
  have habs : |(-(κ / u ^ 2))| = κ / u ^ 2 := by
    rw [abs_neg, abs_of_pos (div_pos hκ hsq)]
  have hne : ENNReal.ofReal (κ / u) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact hκu
  simp only [hinv, habs]
  rw [ENNReal.mul_div_cancel_right hne ENNReal.ofReal_ne_top, ENNReal.ofReal_div_of_pos hsq]
  simp only [div_eq_mul_inv]
  ring

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralIoiCompConstDivChangeOfVarStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.OrbitTerm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_Ioi_comp_const_div_change_of_var : ∀ (κ : ℝ), 0 < κ → ∀ w : ℝ → ENNReal, Measurable w → ∫⁻ t in Set.Ioi (0 : ℝ), w (κ / t) * ENNReal.ofReal t / ENNReal.ofReal t = ENNReal.ofReal κ * ∫⁻ t in Set.Ioi (0 : ℝ), w t / ENNReal.ofReal (t ^ 2) := by
  first | exact @GlobalTheory.lintegral_Ioi_comp_const_div_mul_div | exact GlobalTheory.lintegral_Ioi_comp_const_div_mul_div | (intros; apply GlobalTheory.lintegral_Ioi_comp_const_div_mul_div <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InfiniteLatticeCovolumeSplitLatticeProd
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InfiniteLatticeCovolumeSplitLatticeProd
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.OrbitTerm
open GlobalTheory.LatFacts Module

noncomputable section

namespace GlobalTheory.CovProd

variable (E : Type) [Field E] [NumberField E] (k : ℕ)

def splitVec : (VecInf E 1 × VecInf E k) ≃ₗ[ℝ] VecInf E (k + 1) where
  toFun p w := Fin.cons (p.1 w 0) (p.2 w)
  invFun x := (fun w _ => x w 0, fun w => Fin.tail (x w))
  map_add' p q := by
    funext w a
    refine Fin.cases ?_ (fun a => ?_) a <;> simp
  map_smul' c p := by
    funext w a
    refine Fin.cases ?_ (fun a => ?_) a <;> simp
  left_inv p := by
    refine Prod.ext ?_ ?_
    · funext w a
      rw [Subsingleton.elim a 0]
      simp
    · funext w
      simp
  right_inv x := by
    funext w
    simp

theorem mem_fd_prod {ι κ : Type} [Fintype ι] [Fintype κ] (b : Basis ι ℝ (VecInf E 1)) (c : Basis κ ℝ (VecInf E k))
    (x : VecInf E (k + 1)) :
    x ∈ ZSpan.fundamentalDomain ((b.prod c).map (splitVec E k)) ↔
      ((splitVec E k).symm x).1 ∈ ZSpan.fundamentalDomain b ∧
        ((splitVec E k).symm x).2 ∈ ZSpan.fundamentalDomain c := by
  rw [← ZSpan.map_fundamentalDomain, LinearEquiv.image_eq_preimage_symm, Set.mem_preimage,
    ZSpan.mem_fundamentalDomain, ZSpan.mem_fundamentalDomain, ZSpan.mem_fundamentalDomain, Sum.forall]
  simp only [Basis.prod_repr_inl, Basis.prod_repr_inr]

private theorem measurePreserving_splitVec_symm :
    MeasurePreserving (fun x : VecInf E (k + 1) => (splitVec E k).symm x) volume volume := by
  have h1 : MeasurePreserving
      (fun (x : InfinitePlace E → Fin (k + 1) → ℂ) w =>
        MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℂ) 0 (x w))
      (Measure.pi fun _ => Measure.pi fun _ => (volume : Measure ℂ))
      (Measure.pi fun _ => (volume : Measure ℂ).prod (Measure.pi fun _ : Fin k => (volume : Measure ℂ))) :=
    measurePreserving_pi _ _ fun _ => measurePreserving_piFinSuccAbove (fun _ => volume) 0
  have h2 := measurePreserving_arrowProdEquivProdArrow ℂ (Fin k → ℂ) (InfinitePlace E)
    (fun _ => (volume : Measure ℂ)) (fun _ => Measure.pi fun _ : Fin k => (volume : Measure ℂ))
  have h3 : MeasurePreserving
      (fun (y : InfinitePlace E → ℂ) w => (MeasurableEquiv.funUnique (Fin 1) ℂ).symm (y w))
      (Measure.pi fun _ => (volume : Measure ℂ))
      (Measure.pi fun _ => Measure.pi fun _ : Fin 1 => (volume : Measure ℂ)) :=
    measurePreserving_pi _ _ fun _ =>
      MeasurePreserving.symm _ (measurePreserving_funUnique (volume : Measure ℂ) (Fin 1))
  have h4 := (h3.prod (MeasurePreserving.id
    (Measure.pi fun _ : InfinitePlace E => Measure.pi fun _ : Fin k => (volume : Measure ℂ)))).comp (h2.comp h1)
  convert h4 using 1
  all_goals rfl

theorem covAt_prod (b : Basis (Idx E 1) ℝ (VecInf E 1)) (c : Basis (Idx E k) ℝ (VecInf E k)) :
    covAt E (k + 1) (Submodule.span ℤ (Set.range ((b.prod c).map (splitVec E k)))) =
      covAt E 1 (Submodule.span ℤ (Set.range b)) * covAt E k (Submodule.span ℤ (Set.range c)) := by
  rw [covAt_span, covAt_span, covAt_span]
  have hs : ZSpan.fundamentalDomain ((b.prod c).map (splitVec E k)) =
      (fun x => (splitVec E k).symm x) ⁻¹' (ZSpan.fundamentalDomain b ×ˢ ZSpan.fundamentalDomain c) := by
    ext x
    rw [mem_fd_prod]
    rfl
  have hm : MeasurableSet (ZSpan.fundamentalDomain b ×ˢ ZSpan.fundamentalDomain c) :=
    (ZSpan.fundamentalDomain_measurableSet b).prod (ZSpan.fundamentalDomain_measurableSet c)
  rw [hs, measureReal_def, (measurePreserving_splitVec_symm E k).measure_preimage hm.nullMeasurableSet,
    Measure.volume_eq_prod, Measure.prod_prod, ENNReal.toReal_mul, measureReal_def, measureReal_def]

theorem latAt_oneInf (j : ℕ) (Λ : Submodule (𝓞 E) (Fin j → E)) :
    latAt E j Λ (oneInf E j) = Submodule.span ℤ (emb E j '' (Λ : Set (Fin j → E))) := by
  simp only [latAt, of_oneInf, inv_one, one_mulVec]
  rfl

theorem span_prod {M N : Type} [AddCommGroup M] [AddCommGroup N] [Module ℝ M] [Module ℝ N] {ι κ : Type}
    (b : Basis ι ℝ M) (c : Basis κ ℝ N) :
    Submodule.span ℤ (Set.range (b.prod c)) =
      (Submodule.span ℤ (Set.range b)).prod (Submodule.span ℤ (Set.range c)) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rcases i with i | i
    · refine Submodule.mem_prod.2 ⟨?_, ?_⟩
      · rw [Basis.prod_apply_inl_fst]
        exact Submodule.subset_span ⟨i, rfl⟩
      · rw [Basis.prod_apply_inl_snd]
        exact zero_mem _
    · refine Submodule.mem_prod.2 ⟨?_, ?_⟩
      · rw [Basis.prod_apply_inr_fst]
        exact zero_mem _
      · rw [Basis.prod_apply_inr_snd]
        exact Submodule.subset_span ⟨i, rfl⟩
  · rintro ⟨x, y⟩ hxy
    rw [Submodule.mem_prod] at hxy
    have hx : Submodule.span ℤ (Set.range b) ≤
        (Submodule.span ℤ (Set.range (b.prod c))).comap (LinearMap.inl ℤ M N) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      refine Submodule.subset_span ⟨Sum.inl i, ?_⟩
      exact Prod.ext (Basis.prod_apply_inl_fst b c i) (Basis.prod_apply_inl_snd b c i)
    have hy : Submodule.span ℤ (Set.range c) ≤
        (Submodule.span ℤ (Set.range (b.prod c))).comap (LinearMap.inr ℤ M N) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      refine Submodule.subset_span ⟨Sum.inr i, ?_⟩
      exact Prod.ext (Basis.prod_apply_inr_fst b c i) (Basis.prod_apply_inr_snd b c i)
    have h := add_mem (Submodule.mem_comap.1 (hx hxy.1)) (Submodule.mem_comap.1 (hy hxy.2))
    simpa using h

theorem covAt_latAt_prod : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ (k : ℕ) (Λ : Submodule (𝓞 E) (Fin (k + 1) → E)) (Λ₀ : Submodule (𝓞 E) (Fin 1 → E)) (Λ' : Submodule (𝓞 E) (Fin k → E)), Submodule.IsFullLattice E Λ₀ → Submodule.IsFullLattice E Λ' → (∀ y, y ∈ Λ ↔ (fun _ => y 0) ∈ Λ₀ ∧ Fin.tail y ∈ Λ') → covAt E (k + 1) (latAt E (k + 1) Λ (oneInf E (k + 1))) = covAt E 1 (latAt E 1 Λ₀ (oneInf E 1)) * covAt E k (latAt E k Λ' (oneInf E k)) := by
  intro E _ _ hE k Λ Λ₀ Λ' h₀ h' hΛ
  rw [latAt_oneInf, latAt_oneInf, latAt_oneInf]
  obtain ⟨b, hb⟩ := exists_basis E 1 Λ₀ h₀
  obtain ⟨c, hc⟩ := exists_basis E k Λ' h'

  set s : (VecInf E 1 × VecInf E k) →ₗ[ℤ] VecInf E (k + 1) :=
    (splitVec E k).toLinearMap.restrictScalars ℤ with hs
  have hsv : ∀ p, s p = splitVec E k p := fun p => rfl

  have hemb : ∀ y : Fin (k + 1) → E,
      emb E (k + 1) y = s (emb E 1 (fun _ => y 0), emb E k (Fin.tail y)) := by
    intro y
    rw [hsv]
    funext w a
    refine Fin.cases ?_ (fun a => ?_) a
    · rfl
    · simp [splitVec, emb, Fin.tail]
  have key : Submodule.span ℤ (emb E (k + 1) '' (Λ : Set (Fin (k + 1) → E))) =
      Submodule.span ℤ (Set.range ((b.prod c).map (splitVec E k))) := by
    have hr : Set.range ((b.prod c).map (splitVec E k)) = s '' Set.range (b.prod c) := by
      rw [Basis.coe_map, Set.range_comp]
      rfl
    rw [hr, Submodule.span_image, span_prod, ← hb, ← hc]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨y, hy, rfl⟩
      have hy' := (hΛ y).1 hy
      refine Submodule.mem_map.2 ⟨(emb E 1 (fun _ => y 0), emb E k (Fin.tail y)),
        Submodule.mem_prod.2 ⟨Submodule.subset_span ⟨_, hy'.1, rfl⟩,
          Submodule.subset_span ⟨_, hy'.2, rfl⟩⟩, (hemb y).symm⟩
    · rw [Submodule.map_le_iff_le_comap]
      rintro ⟨u, v⟩ huv
      rw [Submodule.mem_prod] at huv
      have hu : Submodule.span ℤ (emb E 1 '' (Λ₀ : Set (Fin 1 → E))) ≤
          (Submodule.span ℤ (emb E (k + 1) '' (Λ : Set (Fin (k + 1) → E)))).comap
            (s.comp (LinearMap.inl ℤ _ _)) := by
        rw [Submodule.span_le]
        rintro _ ⟨z, hz, rfl⟩
        have hz0 : (fun _ : Fin 1 => z 0) = z := by
          funext i
          rw [Subsingleton.elim i 0]
        have hmem : (Fin.cons (z 0) (0 : Fin k → E) : Fin (k + 1) → E) ∈ Λ := by
          refine (hΛ _).2 ⟨?_, ?_⟩
          · simpa only [Fin.cons_zero] using hz0 ▸ hz
          · simpa only [Fin.tail_cons] using zero_mem Λ'
        refine Submodule.subset_span ⟨_, hmem, ?_⟩
        rw [hemb, Fin.tail_cons, map_zero]
        simp only [Fin.cons_zero, hz0, LinearMap.comp_apply, LinearMap.inl_apply]
      have hv : Submodule.span ℤ (emb E k '' (Λ' : Set (Fin k → E))) ≤
          (Submodule.span ℤ (emb E (k + 1) '' (Λ : Set (Fin (k + 1) → E)))).comap
            (s.comp (LinearMap.inr ℤ _ _)) := by
        rw [Submodule.span_le]
        rintro _ ⟨z, hz, rfl⟩
        have hmem : (Fin.cons 0 z : Fin (k + 1) → E) ∈ Λ := by
          refine (hΛ _).2 ⟨?_, ?_⟩
          · convert zero_mem Λ₀ using 1
            funext i
            simp
          · rw [Fin.tail_cons]
            exact hz
        refine Submodule.subset_span ⟨_, hmem, ?_⟩
        rw [hemb, Fin.tail_cons]
        simp only [Fin.cons_zero, LinearMap.comp_apply, LinearMap.inr_apply]
        congr 2
        exact map_zero (emb E 1)
      have h := add_mem (Submodule.mem_comap.1 (hu huv.1)) (Submodule.mem_comap.1 (hv huv.2))
      rw [Submodule.mem_comap]
      simpa [← map_add (f := _)] using h
  rw [key, hb, hc]
  exact covAt_prod E k b c

end GlobalTheory.CovProd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InfiniteLatticeCovolumeSplitLatticeProdStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.OrbitTerm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.infiniteLatticeCovolume_split_lattice_prod : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ (k : ℕ) (Λ : Submodule (𝓞 E) (Fin (k + 1) → E)) (Λ₀ : Submodule (𝓞 E) (Fin 1 → E)) (Λ' : Submodule (𝓞 E) (Fin k → E)), Submodule.IsFullLattice E Λ₀ → Submodule.IsFullLattice E Λ' → (∀ y, y ∈ Λ ↔ (fun _ => y 0) ∈ Λ₀ ∧ Fin.tail y ∈ Λ') → covAt E (k + 1) (latAt E (k + 1) Λ (oneInf E (k + 1))) = covAt E 1 (latAt E 1 Λ₀ (oneInf E 1)) * covAt E k (latAt E k Λ' (oneInf E k)) :=
  GlobalTheory.CovProd.covAt_latAt_prod
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemLatticeAutSplitIffFirstColSingle
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemLatticeAutSplitIffFirstColSingle
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.OrbitTerm

namespace GlobalTheory.OrbitTerm.SplitStab

variable {E : Type} [Field E] {k : ℕ}

theorem det_of_col (M : Matrix (Fin (k + 1)) (Fin (k + 1)) E)
    (h : ∀ a, M a 0 = if a = 0 then 1 else 0) : M.det = (M.submatrix Fin.succ Fin.succ).det := by
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp [h, Fin.succ_ne_zero]

theorem mulVec_zero_of_col (M : Matrix (Fin (k + 1)) (Fin (k + 1)) E)
    (h : ∀ a, M a 0 = if a = 0 then 1 else 0) (y : Fin (k + 1) → E) :
    (M *ᵥ y) 0 = y 0 + (fun b => M 0 (Fin.succ b)) ⬝ᵥ Fin.tail y := by
  have h0 : M 0 0 = 1 := by simpa using h 0
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, h0, Fin.tail]

theorem tail_mulVec_of_col (M : Matrix (Fin (k + 1)) (Fin (k + 1)) E)
    (h : ∀ a, M a 0 = if a = 0 then 1 else 0) (y : Fin (k + 1) → E) :
    Fin.tail (M *ᵥ y) = M.submatrix Fin.succ Fin.succ *ᵥ Fin.tail y := by
  funext b
  have hb : M b.succ 0 = 0 := by simpa [Fin.succ_ne_zero] using h b.succ
  simp [Fin.tail, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, hb, Matrix.submatrix]

theorem preserves_iff [NumberField E] (Λ : Submodule (𝓞 E) (Fin (k + 1) → E)) (Λ₀ : Submodule (𝓞 E) (Fin 1 → E))
    (Λ' : Submodule (𝓞 E) (Fin k → E)) (hΛ : ∀ y, y ∈ Λ ↔ (fun _ => y 0) ∈ Λ₀ ∧ Fin.tail y ∈ Λ')
    (M : Matrix (Fin (k + 1)) (Fin (k + 1)) E) (h : ∀ a, M a 0 = if a = 0 then 1 else 0) :
    (∀ y, M *ᵥ y ∈ Λ ↔ y ∈ Λ) ↔ (∀ y, M.submatrix Fin.succ Fin.succ *ᵥ y ∈ Λ' ↔ y ∈ Λ') ∧
      ∀ y ∈ Λ', (fun _ => (fun b => M 0 (Fin.succ b)) ⬝ᵥ y) ∈ Λ₀ := by
  have key : ∀ y : Fin (k + 1) → E, M *ᵥ y ∈ Λ ↔
      ((fun _ => y 0) + (fun _ => (fun b => M 0 (Fin.succ b)) ⬝ᵥ Fin.tail y) : Fin 1 → E) ∈ Λ₀ ∧
        M.submatrix Fin.succ Fin.succ *ᵥ Fin.tail y ∈ Λ' := by
    intro y
    rw [hΛ, mulVec_zero_of_col M h y, tail_mulVec_of_col M h y]
    exact Iff.rfl
  have hcons : ∀ (c : E) (z : Fin k → E),
      (Fin.cons c z : Fin (k + 1) → E) 0 = c ∧ Fin.tail (Fin.cons c z : Fin (k + 1) → E) = z :=
    fun c z => ⟨Fin.cons_zero _ _, Fin.tail_cons _ _⟩
  constructor
  · intro hM
    refine ⟨fun z => ⟨fun hz => ?_, fun hz => ?_⟩, fun z hz => ?_⟩
    ·
      set c : E := -((fun b => M 0 (Fin.succ b)) ⬝ᵥ z)
      have h1 : M *ᵥ (Fin.cons c z : Fin (k + 1) → E) ∈ Λ := by
        rw [key, (hcons c z).1, (hcons c z).2]
        refine ⟨?_, hz⟩
        have hz0 : ((fun _ => c) + (fun _ => (fun b => M 0 (Fin.succ b)) ⬝ᵥ z) : Fin 1 → E) = 0 := by
          funext i; simp [c]
        rw [hz0]; exact Λ₀.zero_mem
      have h2 := (hΛ _).1 ((hM _).1 h1)
      rw [(hcons c z).2] at h2
      exact h2.2
    · have h1 : (Fin.cons 0 z : Fin (k + 1) → E) ∈ Λ := by
        rw [hΛ, (hcons 0 z).1, (hcons 0 z).2]; exact ⟨Λ₀.zero_mem, hz⟩
      have h2 := (key _).1 ((hM _).2 h1)
      rw [(hcons 0 z).2] at h2
      exact h2.2
    · have h1 : (Fin.cons 0 z : Fin (k + 1) → E) ∈ Λ := by
        rw [hΛ, (hcons 0 z).1, (hcons 0 z).2]; exact ⟨Λ₀.zero_mem, hz⟩
      have h2 := ((key _).1 ((hM _).2 h1)).1
      rw [(hcons 0 z).1, (hcons 0 z).2] at h2
      have he : ((fun _ => (0 : E)) + (fun _ => (fun b => M 0 (Fin.succ b)) ⬝ᵥ z) : Fin 1 → E) =
          fun _ => (fun b => M 0 (Fin.succ b)) ⬝ᵥ z := by
        funext i; simp
      rwa [he] at h2
  · rintro ⟨hA, hr⟩ y
    rw [key, hΛ, hA]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(add_mem_cancel_right (hr _ h2)).1 h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨Λ₀.add_mem h1 (hr _ h2), h2⟩

end GlobalTheory.OrbitTerm.SplitStab

namespace GlobalTheory.OrbitTerm

open SplitStab in
theorem mem_autGL_split_iff : ∀ (E : Type) [Field E] [NumberField E] (k : ℕ) (Λ : Submodule (𝓞 E) (Fin (k + 1) → E)) (Λ₀ : Submodule (𝓞 E) (Fin 1 → E)) (Λ' : Submodule (𝓞 E) (Fin k → E)), (∀ y, y ∈ Λ ↔ (fun _ => y 0) ∈ Λ₀ ∧ Fin.tail y ∈ Λ') → ∀ x : MatInf E (k + 1), (∀ w a, x w a 0 = if a = 0 then 1 else 0) → (x ∈ autGL E (k + 1) Λ ↔ (fun w a b => x w a.succ b.succ) ∈ autGL E k Λ' ∧ ∃ τ : Fin k → E, (∀ y ∈ Λ', (fun _ => τ ⬝ᵥ y) ∈ Λ₀) ∧ ∀ w b, x w 0 b.succ = w.embedding (τ b)) := by
  intro E _ _ k Λ Λ₀ Λ' hΛ x hx
  obtain ⟨w₀⟩ : Nonempty (InfinitePlace E) := inferInstance
  simp only [autGL, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨γ, hγ, hxγ⟩
    have hcol : ∀ a, (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) E) a 0 = if a = 0 then 1 else 0 := by
      intro a
      apply w₀.embedding.injective
      rw [← hxγ w₀ a 0, hx w₀ a]
      split_ifs <;> simp
    have hdet : (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) E).det ≠ 0 := (Matrix.isUnits_det_units γ).ne_zero
    rw [det_of_col _ hcol] at hdet
    obtain ⟨hA, hr⟩ := (preserves_iff Λ Λ₀ Λ' hΛ _ hcol).1 hγ
    exact ⟨⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet, hA, fun w a b => hxγ w a.succ b.succ⟩,
      fun b => (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) E) 0 b.succ, hr, fun w b => hxγ w 0 b.succ⟩
  · rintro ⟨⟨γ', hγ', hxγ'⟩, τ, hτ, hxτ⟩

    obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin (k + 1)) (Fin (k + 1)) E,
        M = Matrix.of (Fin.cons (Fin.cons 1 τ : Fin (k + 1) → E)
          (fun a => (Fin.cons 0 ((γ' : Matrix (Fin k) (Fin k) E) a) : Fin (k + 1) → E)) :
            Fin (k + 1) → Fin (k + 1) → E) := ⟨_, rfl⟩
    have hcol : ∀ a, M a 0 = if a = 0 then 1 else 0 := by
      intro a
      rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨a, rfl⟩ <;> simp [hM, Fin.succ_ne_zero]
    have hsub : M.submatrix Fin.succ Fin.succ = (γ' : Matrix (Fin k) (Fin k) E) := by
      ext a b; simp [hM]
    have hrow : (fun b => M 0 (Fin.succ b)) = τ := by
      funext b; simp [hM]
    have hdet : M.det ≠ 0 := by
      rw [det_of_col M hcol, hsub]; exact (Matrix.isUnits_det_units γ').ne_zero
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M hdet, ?_, ?_⟩
    · show ∀ y, M *ᵥ y ∈ Λ ↔ y ∈ Λ
      refine (preserves_iff Λ Λ₀ Λ' hΛ M hcol).2 ⟨?_, ?_⟩
      · rw [hsub]; exact hγ'
      · rw [hrow]; exact hτ
    · intro w a b
      show x w a b = w.embedding (M a b)
      rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨a, rfl⟩ <;>
        rcases Fin.eq_zero_or_eq_succ b with rfl | ⟨b, rfl⟩
      · rw [hx]; simp [hM]
      · rw [hxτ]; simp [hM]
      · rw [hx]; simp [hM, Fin.succ_ne_zero]
      · refine (hxγ' w a b).trans ?_
        simp [hM]

end GlobalTheory.OrbitTerm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemLatticeAutSplitIffFirstColSingleStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.OrbitTerm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_latticeAut_split_iff_firstCol_single : ∀ (E : Type) [Field E] [NumberField E] (k : ℕ) (Λ : Submodule (𝓞 E) (Fin (k + 1) → E)) (Λ₀ : Submodule (𝓞 E) (Fin 1 → E)) (Λ' : Submodule (𝓞 E) (Fin k → E)), (∀ y, y ∈ Λ ↔ (fun _ => y 0) ∈ Λ₀ ∧ Fin.tail y ∈ Λ') → ∀ x : MatInf E (k + 1), (∀ w a, x w a 0 = if a = 0 then 1 else 0) → (x ∈ autGL E (k + 1) Λ ↔ (fun w a b => x w a.succ b.succ) ∈ autGL E k Λ' ∧ ∃ τ : Fin k → E, (∀ y ∈ Λ', (fun _ => τ ⬝ᵥ y) ∈ Λ₀) ∧ ∀ w b, x w 0 b.succ = w.embedding (τ b)) := by
  first | exact @GlobalTheory.OrbitTerm.mem_autGL_split_iff | exact GlobalTheory.OrbitTerm.mem_autGL_split_iff | (intros; apply GlobalTheory.OrbitTerm.mem_autGL_split_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LineLatticeMeanSinglePairOrbitContribution
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

noncomputable section

namespace GlobalTheory.OrbitTerm

variable {E : Type} [Field E] [NumberField E]

theorem mul_ne_self {j : ℕ} {γ x : MatInf E j} (hγ : γ ≠ oneInf E j) (hx : 0 < detNorm E j x) : γ * x ≠ x := by
  intro h
  refine hγ (matInf_ext fun w => ?_)
  have h1 : Matrix.of (γ w) * Matrix.of (x w) = Matrix.of (x w) := by rw [← of_mul, h]
  have hu : IsUnit (Matrix.of (x w)).det := IsUnit.mk0 _ ((detNorm_pos_iff x).1 hx w)
  rw [of_oneInf, ← Matrix.mul_nonsing_inv_cancel_right _ (Matrix.of (γ w)) hu, h1, Matrix.mul_nonsing_inv _ hu]

theorem exists_domain (hE : IsTotallyComplex E) {k : ℕ} (hk : 1 ≤ k) (Λ : Submodule (𝓞 E) (Fin k → E))
    (hΛ : Submodule.IsFullLattice E Λ) : ∃ D : Set (MatInf E k), MeasurableSet D ∧
      (∀ g, 0 < detNorm E k g → ∃ γ ∈ autGL E k Λ, γ * g ∈ D) ∧
      (∀ γ ∈ autGL E k Λ, γ ≠ oneInf E k → haarGL E k {x | x ∈ D ∧ γ * x ∈ D} = 0) ∧
      ∀ F : ℝ → ENNReal, Measurable F → ∫⁻ h in D, F (detNorm E k h) ∂(haarGL E k) =
        slabVol E k Λ * ∫⁻ t in Set.Ioi (0 : ℝ), F t / ENNReal.ofReal t := by
  obtain ⟨D, hDm, hDU, hcov, -, hint⟩ := GlobalTheory.T.exists_scalarStable_latticeAutomorphismFundamentalDomain E hE k Λ hΛ
  rw [haarGL_restrict hk] at hint
  have hUinv : ∀ γ ∈ autGL E k Λ, ∀ x ∈ {g | 0 < detNorm E k g}, γ * x ∈ {g | 0 < detNorm E k g} :=
    fun γ hγ x hx => by
      show 0 < detNorm E k (γ * x)
      rw [detNorm_mul]; exact mul_pos (detNorm_pos_of_mem_autGL hγ) hx
  refine ⟨D, hDm, hcov, fun γ hγ hne => ?_, fun F hF => ?_⟩
  · haveI : BorelSpace (Fin k → ℂ) := inferInstance
    haveI : BorelSpace (Fin k → Fin k → ℂ) := inferInstance
    haveI : BorelSpace (InfinitePlace E → Fin k → Fin k → ℂ) := inferInstance
    haveI : MeasurableSpace.CountablyGenerated (InfinitePlace E → Fin k → Fin k → ℂ) := inferInstance
    haveI : MeasurableSpace.SeparatesPoints (InfinitePlace E → Fin k → Fin k → ℂ) := inferInstance
    haveI : MeasurableSpace.CountablySeparated (MatInf E k) :=
      inferInstanceAs (MeasurableSpace.CountablySeparated (InfinitePlace E → Fin k → Fin k → ℂ))
    refine GlobalTheory.T.measure_inter_translate_eq_zero_of_covolume (MatInf E k) (autGL E k Λ) (haarGL E k) {g | 0 < detNorm E k g} D (countable_autGL Λ)
      (fun γ _ => measurable_mul_left γ) (fun γ hγ => GlobalTheory.T.map_infiniteGLHaarMeasure_mul_left E k γ (detNorm_pos_of_mem_autGL hγ))
      (fun γ hγ δ hδ => ⟨γ * δ, mul_mem_autGL hγ hδ, fun x => matInf_mul_assoc _ _ _⟩) (fun γ hγ => ?_)
      measurableSet_detNorm_pos hUinv hDm hDU (fun A hA hAU hAi => ?_) γ hγ fun x hx => mul_ne_self hne hx
    · obtain ⟨δ, hδ, h1, h2⟩ := exists_inv_mem_autGL hγ
      exact ⟨δ, hδ, fun x => by rw [← matInf_mul_assoc, h1, oneInf_mul],
        fun x => by rw [← matInf_mul_assoc, h2, oneInf_mul]⟩
    · have := hint (fun _ => 1) A (measurable_const.indicator measurableSet_detNorm_pos) (fun _ _ _ _ => rfl)
        hA hAU hAi
      rwa [setLIntegral_one, show (fun _ : MatInf E k => (1 : ENNReal)) = 1 from rfl, withDensity_one] at this
  · have h1 := hint (fun h => F (detNorm E k h)) {g | 0 < detNorm E k g}
      ((hF.comp measurable_detNorm).indicator measurableSet_detNorm_pos)
      (fun γ hγ g _ => by rw [detNorm_mul, GlobalTheory.T.detNorm_eq_one_of_mem_autGL_var E hE k Λ hΛ γ hγ, one_mul])
      measurableSet_detNorm_pos subset_rfl hUinv
    rw [Set.inter_eq_right.2 hDU, GlobalTheory.T.leftQuotientCovolume_withDensity_detNormSq E hE k hk Λ hΛ F hF] at h1
    exact h1.symm

def FixesFirst {k : ℕ} (x : MatInf E (k + 1)) : Prop := ∀ w a, x w a 0 = if a = 0 then 1 else 0

theorem fixesFirst_iff {k : ℕ} (x : MatInf E (k + 1)) :
    FixesFirst x ↔ ∀ w, Matrix.of (x w) *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
  refine forall_congr' fun w => ?_
  rw [funext_iff]
  refine forall_congr' fun a => ?_
  simp [Pi.single_apply]

theorem FixesFirst.mul {k : ℕ} {x y : MatInf E (k + 1)} (hx : FixesFirst x) (hy : FixesFirst y) :
    FixesFirst (x * y) := by
  rw [fixesFirst_iff] at hx hy ⊢
  intro w
  rw [of_mul, ← Matrix.mulVec_mulVec, hy, hx]

theorem FixesFirst.inv {k : ℕ} {x y : MatInf E (k + 1)} (hx : FixesFirst x) (h : y * x = oneInf E (k + 1)) :
    FixesFirst y := by
  rw [fixesFirst_iff] at hx ⊢
  intro w
  conv_lhs => rw [← hx w, Matrix.mulVec_mulVec, ← of_mul, h, of_oneInf, Matrix.one_mulVec]

theorem FixesFirst.inv_col {k : ℕ} {x : MatInf E (k + 1)} (hx : FixesFirst x) (hx' : 0 < detNorm E (k + 1) x)
    (g : MatInf E (k + 1)) :
    (fun u a => (Matrix.of ((x * g) u))⁻¹ a 0) = fun u a => (Matrix.of (g u))⁻¹ a 0 := by
  funext u a
  have hu : IsUnit (Matrix.of (x u)).det := IsUnit.mk0 _ ((detNorm_pos_iff x).1 hx' u)
  have h1 : (Matrix.of (x u))⁻¹ *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
    conv_lhs => rw [← (fixesFirst_iff x).1 hx u, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu,
      Matrix.one_mulVec]
  have h2 : (Matrix.of ((x * g) u))⁻¹ *ᵥ Pi.single 0 1 = (Matrix.of (g u))⁻¹ *ᵥ Pi.single 0 1 := by
    rw [of_mul, Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec, h1]
  simpa using congrFun h2 a

def blk {k : ℕ} (τ : VecInf E k) (β : MatInf E k) : MatInf E (k + 1) :=
  fun w => Fin.cons (Fin.cons 1 (τ w)) fun a => Fin.cons 0 (β w a)

theorem fixesFirst_blk {k : ℕ} (τ : VecInf E k) (β : MatInf E k) : FixesFirst (blk τ β) := by
  intro w a
  refine Fin.cases ?_ (fun a => ?_) a <;> simp [blk]

theorem measurable_inv_col {k : ℕ} :
    Measurable fun (g : MatInf E (k + 1)) => (fun u a => (Matrix.of (g u))⁻¹ a 0 : VecInf E (k + 1)) :=
  Measurable.of_eval fun u => Measurable.of_eval fun a => measurable_inv_entry u a 0

theorem map_withDensity_of_invariant {X : Type} [MeasurableSpace X] (μ : Measure X) {f : X → X}
    (hf : Measurable f) (hμ : μ.map f = μ) {G : X → ENNReal} (hG : Measurable G) (hGf : ∀ x, G (f x) = G x) :
    (μ.withDensity G).map f = μ.withDensity G := by
  ext s hs
  rw [Measure.map_apply hf hs, withDensity_apply _ (hf hs), withDensity_apply _ hs]
  conv_rhs => rw [← hμ, setLIntegral_map hs hG hf]
  simp only [hGf]

theorem covol_stabilizer (hE : IsTotallyComplex E) {k : ℕ} (hk : 1 ≤ k) (Λ : Submodule (𝓞 E) (Fin (k + 1) → E))
    (Λ₀ : Submodule (𝓞 E) (Fin 1 → E)) (Λ' : Submodule (𝓞 E) (Fin k → E)) (hΛ : Submodule.IsFullLattice E Λ)
    (hΛ₀ : Submodule.IsFullLattice E Λ₀) (hΛ' : Submodule.IsFullLattice E Λ')
    (hmem : ∀ y, y ∈ Λ ↔ (fun _ => y 0) ∈ Λ₀ ∧ Fin.tail y ∈ Λ') (f : ℝ → ENNReal) (hf : Measurable f)
    (Φ : VecInf E (k + 1) → ENNReal) (hΦ : Measurable Φ) :
    covol {x | x ∈ autGL E (k + 1) Λ ∧ FixesFirst x}
      ((haarGL E (k + 1)).withDensity fun g => f (detNorm E (k + 1) g) * Φ fun u a => (Matrix.of (g u))⁻¹ a 0)
      {g | 0 < detNorm E (k + 1) g} =
    (∫⁻ x, Φ x) * ENNReal.ofReal (covAt E 1 (latAt E 1 Λ₀ (oneInf E 1)) ^ k *
      (Formalism.HermitianLatticesTheory.vInv E ^ (Formalism.HermitianLatticesTheory.fDeg E * k) / covAt E k (latAt E k Λ' (oneInf E k)))) *
      (slabVol E k Λ' * ∫⁻ t in Set.Ioi (0 : ℝ), f t * ENNReal.ofReal t / ENNReal.ofReal t) := by
  obtain ⟨D', hD'm, hD'c, hD'd, hD'i⟩ := exists_domain hE hk Λ' hΛ'
  obtain ⟨P, hPm, hPv, hPc, hPd⟩ := GlobalTheory.T.exists_fundamentalDomain_embeddedRowsLattice E hE k Λ₀ Λ' hΛ₀ hΛ'
  obtain ⟨hh, TT, hhm, hTm, hdet, hequi, hint⟩ := GlobalTheory.T.exists_coordinates_inverseFirstColumn_infiniteGL E k hk
  have hstab := GlobalTheory.T.mem_latticeAut_split_iff_firstCol_single E k Λ Λ₀ Λ' hmem
  set G : MatInf E (k + 1) → ENNReal :=
    fun g => f (detNorm E (k + 1) g) * Φ fun u a => (Matrix.of (g u))⁻¹ a 0 with hG
  have hGm : Measurable G := (hf.comp measurable_detNorm).mul (hΦ.comp measurable_inv_col)
  set μ := (haarGL E (k + 1)).withDensity G with hμ
  set S : Set (MatInf E (k + 1)) := {x | x ∈ autGL E (k + 1) Λ ∧ FixesFirst x} with hS
  have hbox : ∀ (B : Set (MatInf E k)) (Q : Set (VecInf E k)), MeasurableSet B → MeasurableSet Q →
      μ {g | 0 < detNorm E (k + 1) g ∧ hh g ∈ B ∧ TT g ∈ Q} = (∫⁻ x, Φ x) * volume Q *
        ∫⁻ h in B, f (detNorm E k h) * ENNReal.ofReal (detNorm E k h) ∂(haarGL E k) := by
    intro B Q hB hQ
    have hm : MeasurableSet {g | 0 < detNorm E (k + 1) g ∧ hh g ∈ B ∧ TT g ∈ Q} :=
      measurableSet_detNorm_pos.inter ((hhm hB).inter (hTm hQ))
    have h1 := hint (B.indicator fun h => f (detNorm E k h)) (Q.indicator 1) Φ
      ((hf.comp measurable_detNorm).indicator hB) (measurable_const.indicator hQ) hΦ
    rw [lintegral_indicator_one hQ] at h1
    rw [hμ, withDensity_apply _ hm, ← lintegral_indicator hm, ← lintegral_indicator hB]
    have h2 : ∀ h, B.indicator (fun h => f (detNorm E k h) * ENNReal.ofReal (detNorm E k h)) h =
        B.indicator (fun h => f (detNorm E k h)) h * ENNReal.ofReal (detNorm E k h) := fun h => by
      by_cases hhB : h ∈ B <;> simp [hhB]
    simp only [h2]
    rw [← h1]
    refine lintegral_congr_ae ?_
    have hae : ∀ᵐ g ∂(haarGL E (k + 1)), g ∈ {g | 0 < detNorm E (k + 1) g} := haarGL_singular (by omega)
    filter_upwards [hae] with g hg
    have hg' : 0 < detNorm E (k + 1) g := hg
    by_cases h3 : hh g ∈ B <;> by_cases h4 : TT g ∈ Q <;> simp [Set.indicator, h3, h4, hg', hG, hdet g hg']
  have hSmul : ∀ γ ∈ S, ∀ δ ∈ S, γ * δ ∈ S := fun γ hγ δ hδ => ⟨mul_mem_autGL hγ.1 hδ.1, hγ.2.mul hδ.2⟩
  have hSinv : ∀ γ ∈ S, ∃ δ ∈ S, δ * γ = oneInf E (k + 1) ∧ γ * δ = oneInf E (k + 1) := fun γ hγ => by
    obtain ⟨δ, hδ, h1, h2⟩ := exists_inv_mem_autGL hγ.1
    exact ⟨δ, ⟨hδ, hγ.2.inv h1⟩, h1, h2⟩
  have hSpos : ∀ γ ∈ S, 0 < detNorm E (k + 1) γ := fun γ hγ => detNorm_pos_of_mem_autGL hγ.1
  have hμinv : ∀ γ ∈ S, μ.map (fun x => γ * x) = μ := fun γ hγ =>
    map_withDensity_of_invariant _ (measurable_mul_left γ) (GlobalTheory.T.map_infiniteGLHaarMeasure_mul_left E _ γ (hSpos γ hγ)) hGm fun x => by
      simp only [hG]
      rw [detNorm_mul, GlobalTheory.T.detNorm_eq_one_of_mem_autGL_var E hE _ Λ hΛ γ hγ.1, one_mul, hγ.2.inv_col (hSpos γ hγ)]
  set D : Set (MatInf E (k + 1)) := {g | 0 < detNorm E (k + 1) g ∧ hh g ∈ D' ∧ TT g ∈ P} with hD
  have hDm : MeasurableSet D := measurableSet_detNorm_pos.inter ((hhm hD'm).inter (hTm hPm))
  have hdis : ∀ γ ∈ S, γ ≠ oneInf E (k + 1) → μ {x | x ∈ D ∧ γ * x ∈ D} = 0 := by
    intro γ hγ hne
    obtain ⟨hβ, τ, hτ, hτγ⟩ := (hstab γ hγ.2).1 hγ.1
    set β : MatInf E k := fun w a b => γ w a.succ b.succ with hβdef
    by_cases hb : β = oneInf E k
    · have : {x | x ∈ D ∧ γ * x ∈ D} = ∅ := by
        refine Set.eq_empty_of_forall_notMem fun x hx => hne ?_
        obtain ⟨-, h2⟩ := hequi x γ hx.1.1 (hSpos γ hγ) hγ.2 β fun _ _ _ => rfl
        have h3 : TT (γ * x) = fun w b => TT x w b + w.embedding (τ b) := by
          funext w b
          have := congrFun (h2 w) b
          rw [hb, of_oneInf, Matrix.vecMul_one] at this
          rw [this, ← hτγ]; rfl
        have h4 : τ = 0 := hPd (TT x) τ hτ hx.1.2.2 (h3 ▸ hx.2.2.2)
        funext w a b
        refine Fin.cases ?_ (fun b => ?_) b
        · exact hγ.2 w a
        refine Fin.cases ?_ (fun a => ?_) a
        · rw [hτγ, h4]; simp [oneInf, (Fin.succ_ne_zero b).symm]
        · have := congrFun (congrFun (congrFun hb w) a) b
          simpa [oneInf] using this
      rw [this, measure_empty]
    · have hBm : MeasurableSet {x | x ∈ D' ∧ β * x ∈ D'} := hD'm.inter (measurable_mul_left β hD'm)
      have h0 := hbox _ Set.univ hBm MeasurableSet.univ
      rw [setLIntegral_measure_zero _ _ (hD'd β hβ hb), mul_zero] at h0
      refine measure_mono_null (fun x hx => ?_) h0
      obtain ⟨h1, -⟩ := hequi x γ hx.1.1 (hSpos γ hγ) hγ.2 β fun _ _ _ => rfl
      exact ⟨hx.1.1, ⟨hx.1.2.1, h1 ▸ hx.2.2.1⟩, trivial⟩
  rw [covol_eq_of_aedisjoint S μ {g | 0 < detNorm E (k + 1) g} D ((countable_autGL Λ).mono fun x hx => hx.1)
    (fun γ _ => measurable_mul_left γ) hμinv ?_ hDm (fun x hx => hx.1) ?_ ?_]
  · rw [hbox D' P hD'm hPm, hPv,
      hD'i (fun t => f t * ENNReal.ofReal t) (hf.mul ENNReal.measurable_ofReal)]
  · intro γ hγ
    obtain ⟨δ, hδ, h1, h2⟩ := hSinv γ hγ
    exact ⟨δ, hδ, fun x => by rw [← matInf_mul_assoc, h1, oneInf_mul],
      fun x => by rw [← matInf_mul_assoc, h2, oneInf_mul]⟩
  · intro g hg
    have hg' : 0 < detNorm E (k + 1) g := hg
    obtain ⟨β, hβ, hβD⟩ := hD'c (hh g) (by rw [hdet g hg']; exact hg')
    have hγ₁ : blk 0 β ∈ S := ⟨(hstab _ (fixesFirst_blk 0 β)).2 ⟨hβ, 0, fun y _ => by
      rw [zero_dotProduct]; exact Λ₀.zero_mem, fun w b => by simp [blk]⟩, fixesFirst_blk 0 β⟩
    have hg₁ : 0 < detNorm E (k + 1) (blk 0 β * g) := by
      rw [detNorm_mul]; exact mul_pos (hSpos _ hγ₁) hg'
    obtain ⟨h1, -⟩ := hequi g (blk 0 β) hg' (hSpos _ hγ₁) hγ₁.2 β fun _ _ _ => rfl
    obtain ⟨τ, hτ, hτP⟩ := hPc (TT (blk 0 β * g))
    have hγ₂ : blk (fun w b => w.embedding (τ b)) (oneInf E k) ∈ S :=
      ⟨(hstab _ (fixesFirst_blk _ _)).2 ⟨oneInf_mem_autGL Λ', τ, hτ, fun w b => rfl⟩, fixesFirst_blk _ _⟩
    obtain ⟨h2, h3⟩ := hequi (blk 0 β * g) _ hg₁ (hSpos _ hγ₂) hγ₂.2 (oneInf E k) fun _ _ _ => rfl
    refine ⟨_, hSmul _ hγ₂ _ hγ₁, ?_⟩
    rw [matInf_mul_assoc]
    refine ⟨by rw [detNorm_mul]; exact mul_pos (hSpos _ hγ₂) hg₁, by rw [h2, oneInf_mul, h1]; exact hβD, ?_⟩
    convert hτP using 1
    funext w b
    have := congrFun (h3 w) b
    rw [of_oneInf, Matrix.vecMul_one] at this
    exact this
  · intro γ hγ δ hδ hne
    obtain ⟨ε, hε, h1, h2⟩ := hSinv γ hγ
    have hne' : δ * ε ≠ oneInf E (k + 1) := fun h => hne (by
      rw [← oneInf_mul γ, ← h, matInf_mul_assoc, h1, mul_oneInf])
    have h0 := hdis _ (hSmul δ hδ ε hε) hne'
    have hm : MeasurableSet {x | x ∈ D ∧ δ * ε * x ∈ D} := hDm.inter (measurable_mul_left (δ * ε) hDm)
    rw [← hμinv γ hγ, Measure.map_apply (measurable_mul_left γ) hm] at h0
    refine measure_mono_null (fun x hx => ?_) h0
    refine ⟨hx.1, ?_⟩
    show δ * ε * (γ * x) ∈ D
    rw [matInf_mul_assoc, ← matInf_mul_assoc ε, h1, oneInf_mul]
    exact hx.2

theorem orbit_term : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ k : ℕ, 1 ≤ k → ∀ Lf : Ideal (𝓞 E) → Submodule (𝓞 E) (Fin k → E) → Submodule (𝓞 E) (Fin (k + 1) → E), (∀ 𝔞 Λ' y, y ∈ Lf 𝔞 Λ' ↔ (∀ t ∈ 𝔞, (t : E) * y 0 ∈ (algebraMap (𝓞 E) E).range) ∧ Fin.tail y ∈ Λ') → ∀ (w : ℝ → ENNReal) (Φ : VecInf E (k + 1) → ENNReal), Measurable w → Measurable Φ → ∀ (𝔞 : Ideal (𝓞 E)) (Λ' : Submodule (𝓞 E) (Fin k → E)), 𝔞 ≠ ⊥ → Submodule.IsFullLattice E Λ' → covol {x | x ∈ autGL E (k + 1) (Lf 𝔞 Λ') ∧ ∀ w a, x w a 0 = if a = 0 then 1 else 0} ((haarGL E (k + 1)).withDensity fun g => w (covAt E (k + 1) (latAt E (k + 1) (Lf 𝔞 Λ') g)) * Φ (fun u a => (Matrix.of (g u))⁻¹ a 0)) {g | 0 < detNorm E (k + 1) g} = slabVol E k Λ' * ENNReal.ofReal (Formalism.HermitianLatticesTheory.vInv E ^ (Formalism.HermitianLatticesTheory.fDeg E * (2 * k + 1)) * ((Ideal.absNorm 𝔞 : ℝ) ^ (k + 1))⁻¹) * (∫⁻ x, Φ x) * ∫⁻ t in Set.Ioi (0 : ℝ), w t / ENNReal.ofReal (t ^ 2) := by
  intro E _ _ hE k hk Lf hLf w Φ hw hΦ 𝔞 Λ' h𝔞 hΛ'
  obtain ⟨Λ₀, hmem₀, hΛ₀_lattice, hc₀⟩ := GlobalTheory.T.exists_lattice_covolume_inverse_ideal E hE 𝔞 h𝔞
  have hΛ₀ : Submodule.IsFullLattice E Λ₀ := by
    -- The inverse ideal contains 1, which spans the one-dimensional space over E.
    have hone : (fun _ : Fin 1 => (1 : E)) ∈ Λ₀ :=
      (hmem₀ _).2 fun t _ => ⟨t, by simp⟩
    refine { toIsLattice := hΛ₀_lattice, span_eq_top := eq_top_iff.mpr fun y _ => ?_ }
    have hy : y = y 0 • (fun _ : Fin 1 => (1 : E)) := by
      funext i
      simp [Subsingleton.elim i (0 : Fin 1)]
    rw [hy]
    exact (Submodule.span E _).smul_mem _ (Submodule.subset_span hone)
  have hΛ := ((GlobalTheory.T.lattice_nonzero_vector_pair_normal_forms E k Lf hLf).1 𝔞 Λ' h𝔞 hΛ').1
  have hmem : ∀ y, y ∈ Lf 𝔞 Λ' ↔ (fun _ => y 0) ∈ Λ₀ ∧ Fin.tail y ∈ Λ' := fun y => by rw [hLf, hmem₀]
  obtain ⟨κ, hκ, hκc⟩ := (GlobalTheory.T.translatedLatticeAtInfinity_full_covolume_dual E hE (k + 1)).1 _ hΛ
  obtain ⟨κ', hκ', hκ'c⟩ := (GlobalTheory.T.translatedLatticeAtInfinity_full_covolume_dual E hE k).1 _ hΛ'
  have e' : covAt E k (latAt E k Λ' (oneInf E k)) = κ' := by
    rw [(hκ'c _ (by rw [detNorm_oneInf]; exact one_pos)).2.1, detNorm_oneInf, div_one]
  have e : κ = Formalism.HermitianLatticesTheory.vInv E ^ Formalism.HermitianLatticesTheory.fDeg E / (Ideal.absNorm 𝔞 : ℝ) * κ' := by
    rw [← hc₀, ← e', ← GlobalTheory.T.infiniteLatticeCovolume_split_lattice_prod E hE k _ Λ₀ Λ' hΛ₀ hΛ' hmem,
      (hκc _ (by rw [detNorm_oneInf]; exact one_pos)).2.1, detNorm_oneInf, div_one]
  have hmain := covol_stabilizer hE hk _ Λ₀ Λ' hΛ hΛ₀ hΛ' hmem (fun t => w (κ / t))
    (hw.comp (measurable_const.div measurable_id)) Φ hΦ
  have hdens : ((haarGL E (k + 1)).withDensity fun g => w (covAt E (k + 1) (latAt E (k + 1) (Lf 𝔞 Λ') g)) *
      Φ (fun u a => (Matrix.of (g u))⁻¹ a 0)) = (haarGL E (k + 1)).withDensity fun g =>
      w (κ / detNorm E (k + 1) g) * Φ fun u a => (Matrix.of (g u))⁻¹ a 0 := by
    refine withDensity_congr_ae ?_
    have hae : ∀ᵐ g ∂(haarGL E (k + 1)), g ∈ {g | 0 < detNorm E (k + 1) g} := haarGL_singular (by omega)
    filter_upwards [hae] with g hg
    rw [(hκc g hg).2.1]
  rw [hdens]
  refine hmain.trans ?_
  rw [GlobalTheory.T.lintegral_Ioi_comp_const_div_change_of_var κ hκ w hw, hc₀, e']
  have hconst : ENNReal.ofReal (Formalism.HermitianLatticesTheory.vInv E ^ (Formalism.HermitianLatticesTheory.fDeg E * (2 * k + 1)) *
      ((Ideal.absNorm 𝔞 : ℝ) ^ (k + 1))⁻¹) =
      ENNReal.ofReal ((Formalism.HermitianLatticesTheory.vInv E ^ Formalism.HermitianLatticesTheory.fDeg E / (Ideal.absNorm 𝔞 : ℝ)) ^ k *
        (Formalism.HermitianLatticesTheory.vInv E ^ (Formalism.HermitianLatticesTheory.fDeg E * k) / κ')) * ENNReal.ofReal κ := by
    rw [← ENNReal.ofReal_mul' hκ.le, e]
    congr 1
    have hN : (Ideal.absNorm 𝔞 : ℝ) ≠ 0 := by
      exact_mod_cast fun h => h𝔞 (Ideal.absNorm_eq_zero_iff.1 h)
    generalize Formalism.HermitianLatticesTheory.vInv E = v
    generalize Formalism.HermitianLatticesTheory.fDeg E = n
    generalize (Ideal.absNorm 𝔞 : ℝ) = N at hN ⊢
    have hκ0 := hκ'.ne'
    rw [div_pow, ← pow_mul]
    field_simp
    ring
  rw [hconst]
  ring

end GlobalTheory.OrbitTerm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LineLatticeMeanSinglePairOrbitContributionStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineLatticeMean_single_pair_orbit_contribution : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ k : ℕ, 1 ≤ k → ∀ Lf : Ideal (𝓞 E) → Submodule (𝓞 E) (Fin k → E) → Submodule (𝓞 E) (Fin (k + 1) → E), (∀ 𝔞 Λ' y, y ∈ Lf 𝔞 Λ' ↔ (∀ t ∈ 𝔞, (t : E) * y 0 ∈ (algebraMap (𝓞 E) E).range) ∧ Fin.tail y ∈ Λ') → ∀ (w : ℝ → ENNReal) (Φ : VecInf E (k + 1) → ENNReal), Measurable w → Measurable Φ → ∀ (𝔞 : Ideal (𝓞 E)) (Λ' : Submodule (𝓞 E) (Fin k → E)), 𝔞 ≠ ⊥ → Submodule.IsFullLattice E Λ' → covol {x | x ∈ autGL E (k + 1) (Lf 𝔞 Λ') ∧ ∀ w a, x w a 0 = if a = 0 then 1 else 0} ((haarGL E (k + 1)).withDensity fun g => w (covAt E (k + 1) (latAt E (k + 1) (Lf 𝔞 Λ') g)) * Φ (fun u a => (Matrix.of (g u))⁻¹ a 0)) {g | 0 < detNorm E (k + 1) g} = slabVol E k Λ' * ENNReal.ofReal (Formalism.HermitianLatticesTheory.vInv E ^ (Formalism.HermitianLatticesTheory.fDeg E * (2 * k + 1)) * ((Ideal.absNorm 𝔞 : ℝ) ^ (k + 1))⁻¹) * (∫⁻ x, Φ x) * ∫⁻ t in Set.Ioi (0 : ℝ), w t / ENNReal.ofReal (t ^ 2) := by
  first | exact @GlobalTheory.OrbitTerm.orbit_term | exact GlobalTheory.OrbitTerm.orbit_term | (intros; apply GlobalTheory.OrbitTerm.orbit_term <;> assumption)
end
