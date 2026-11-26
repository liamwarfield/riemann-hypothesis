module

public import Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.AddCharHalfTraceTensorLatticeHeisenbergCocycle
public import Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.ExistsRationalDarbouxCoordinatesTensorHermitian

@[expose] public section

section -- merged from Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.EqAdeleSupportedAtFinitePlaceOfSupportedAt
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

namespace Tw.VacAny
open _root_.GlobalTheory _root_.GlobalTheory.VacAny

theorem eq_atPlace_of_at {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (a : AF F) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) a → a = GlobalTheory.EmbChart.atPlace v (GlobalTheory.AdelicU.evFin F v a) := by
  intro h
  have hu : GlobalTheory.AdelicU.evFin F v (1 - GlobalTheory.EmbChart.atPlace v 1) = 0 := by
    rw [map_sub, map_one, GlobalTheory.EmbChart.evFin_atPlace, sub_self]
  have h0 : (1 - GlobalTheory.EmbChart.atPlace v 1) • a = 0 := h _ hu
  rw [smul_eq_mul, sub_mul, one_mul, sub_eq_zero] at h0
  conv_lhs => rw [h0]
  rw [GlobalTheory.EmbChart.atPlace_mul_right, one_mul]

end Tw.VacAny
end

section -- merged from Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.ExistsSchroedingerEigenvectorCompactCocycle
section -- merged from Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.ExistsSchwartzBruhatSchroedingerFixedLocalField
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

noncomputable section

namespace Tw.SchrTestVec
open _root_.GlobalTheory

theorem exists_fixed_of_subgroup {K : Type} [CommRing K] [Invertible (2 : K)] [TopologicalSpace K] [IsTopologicalRing K]
    [T2Space K] {κ : Type} [Fintype κ] (ψ : AddChar K ℂ) (U₀ : Set K) (hU₀ : IsOpen U₀) (h0 : (0 : K) ∈ U₀)
    (hψ : ∀ t ∈ U₀, ψ t = 1) (B : AddSubgroup (κ → K)) (hBo : IsOpen (B : Set (κ → K)))
    (hBc : IsCompact (B : Set (κ → K))) :
    ∃ φ₁ ∈ GlobalTheory.WeilM.SB (κ → K), φ₁ ≠ 0 ∧
      ∃ U ∈ nhds (0 : (κ → K) × (κ → K)), ∀ w ∈ U, GlobalTheory.WeilM.schr ψ w φ₁ = φ₁ := by
  refine ⟨(B : Set (κ → K)).indicator fun _ => (1 : ℂ), ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    by_cases hx : x ∈ (B : Set (κ → K))
    · filter_upwards [hBo.mem_nhds hx] with y hy
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hy]
    · filter_upwards [hBc.isClosed.isOpen_compl.mem_nhds hx] with y hy
      rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hy]
  · exact HasCompactSupport.intro hBc fun x hx => Set.indicator_of_notMem hx _
  · intro h
    have := congrFun h 0
    rw [Set.indicator_of_mem (show (0 : κ → K) ∈ (B : Set (κ → K)) from B.zero_mem)] at this
    exact one_ne_zero this
  · have hc : Continuous fun z : ((κ → K) × (κ → K)) × (κ → K) =>
        z.2 ⬝ᵥ z.1.2 + ⅟(2 : K) * (z.1.1 ⬝ᵥ z.1.2) :=
      (continuous_snd.dotProduct continuous_fst.snd).add
        (continuous_const.mul (continuous_fst.fst.dotProduct continuous_fst.snd))
    have h1 : ∀ᶠ w : (κ → K) × (κ → K) in nhds 0, ∀ x ∈ (B : Set (κ → K)),
        x ⬝ᵥ w.2 + ⅟(2 : K) * (w.1 ⬝ᵥ w.2) ∈ U₀ := by
      refine hBc.eventually_forall_of_forall_eventually
        (P := fun (w : (κ → K) × (κ → K)) (x : κ → K) => x ⬝ᵥ w.2 + ⅟(2 : K) * (w.1 ⬝ᵥ w.2) ∈ U₀) fun x _ => ?_
      refine (hU₀.preimage hc).mem_nhds ?_
      simpa using h0
    have h2 : ∀ᶠ w : (κ → K) × (κ → K) in nhds 0, w.1 ∈ (B : Set (κ → K)) :=
      (hBo.preimage continuous_fst).mem_nhds B.zero_mem
    refine ⟨_, h1.and h2, fun w hw => ?_⟩
    obtain ⟨hw1, hw2⟩ := hw
    funext x
    show ψ (x ⬝ᵥ w.2 + ⅟(2 : K) * (w.1 ⬝ᵥ w.2)) * (B : Set (κ → K)).indicator (fun _ => (1 : ℂ)) (x + w.1) = _
    by_cases hx : x ∈ (B : Set (κ → K))
    · rw [hψ _ (hw1 x hx), one_mul, Set.indicator_of_mem hx,
        Set.indicator_of_mem (show x + w.1 ∈ (B : Set (κ → K)) from B.add_mem hx hw2)]
    · have hx' : x + w.1 ∉ (B : Set (κ → K)) := fun h => hx (by simpa using B.sub_mem h hw2)
      rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx', mul_zero]

theorem exists_fixed : ∀ {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (ψ : AddChar (Fv F v) ℂ),
    Continuous ψ → ∀ {κ : Type} [Fintype κ], ∃ φ₁ ∈ GlobalTheory.WeilM.SB (κ → Fv F v), φ₁ ≠ 0 ∧
      ∃ U ∈ nhds (0 : (κ → Fv F v) × (κ → Fv F v)), ∀ w ∈ U, GlobalTheory.WeilM.schr ψ w φ₁ = φ₁ := by
  intro F _ _ v ψ hψ κ _
  obtain ⟨U₀, hU₀⟩ := Tw.HeisLatVac.lc_exists_open_ker ψ hψ
  refine exists_fixed_of_subgroup ψ U₀ U₀.isOpen U₀.zero_mem hU₀
    (AddSubgroup.pi Set.univ fun _ => (v.adicCompletionIntegers F).toSubring.toAddSubgroup) ?_ ?_
  · exact isOpen_set_pi Set.finite_univ fun _ _ => Valued.isOpen_valuationSubring _
  · exact isCompact_univ_pi fun _ =>
      isCompact_iff_compactSpace.2 (GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v)

end Tw.SchrTestVec
end
end

section -- merged from Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.SchroedingerMemSchwartzBruhatFinitePlace
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

noncomputable section

namespace Tw.SchrSBFin
open _root_.GlobalTheory

theorem isLocallyConstant_addChar {K : Type} [AddCommGroup K] [TopologicalSpace K] [NonarchimedeanAddGroup K]
    (ψ : AddChar K ℂ) (hψ : Continuous ψ) : IsLocallyConstant ψ := by
  obtain ⟨U₀, hU₀⟩ := Tw.HeisLatVac.lc_exists_open_ker ψ hψ
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  rw [← map_add_left_nhds_zero, Filter.eventually_map]
  filter_upwards [U₀.mem_nhds_zero] with s hs
  rw [AddChar.map_add_eq_mul, hU₀ s hs, mul_one]

theorem schr_mem_SB_of {K : Type} [CommRing K] [Invertible (2 : K)] [TopologicalSpace K] [IsTopologicalRing K]
    [NonarchimedeanAddGroup K] (ψ : AddChar K ℂ) (hψ : Continuous ψ) {κ : Type} [Fintype κ]
    (w : (κ → K) × (κ → K)) (φ : (κ → K) → ℂ) (hφ : φ ∈ GlobalTheory.WeilM.SB (κ → K)) :
    GlobalTheory.WeilM.schr ψ w φ ∈ GlobalTheory.WeilM.SB (κ → K) := by
  obtain ⟨hlc, hcs⟩ := hφ
  have h1 : IsLocallyConstant fun x : κ → K => ψ (x ⬝ᵥ w.2 + ⅟(2 : K) * (w.1 ⬝ᵥ w.2)) :=
    (isLocallyConstant_addChar ψ hψ).comp_continuous
      ((continuous_id.dotProduct continuous_const).add continuous_const)
  have h2 : IsLocallyConstant fun x : κ → K => φ (x + w.1) := hlc.comp_continuous (continuous_id.add continuous_const)
  have h3 : HasCompactSupport fun x : κ → K => φ (x + w.1) := hcs.comp_homeomorph (Homeomorph.addRight w.1)
  exact ⟨h1.mul h2, h3.mul_left⟩

theorem schr_mem_SB : ∀ {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (ψ : AddChar (Fv F v) ℂ),
    Continuous ψ → ∀ {κ : Type} [Fintype κ] (w : (κ → Fv F v) × (κ → Fv F v)) (φ : (κ → Fv F v) → ℂ),
    φ ∈ GlobalTheory.WeilM.SB (κ → Fv F v) → GlobalTheory.WeilM.schr ψ w φ ∈ GlobalTheory.WeilM.SB (κ → Fv F v) := by
  intro F _ _ v ψ hψ κ _ w φ hφ
  exact schr_mem_SB_of ψ hψ w φ hφ

end Tw.SchrSBFin
end
end

section -- merged from Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.ExistsSubgroupSymplecticAnnihilatorLocalField
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

noncomputable section

namespace Tw.SympDualNbhd
open _root_.GlobalTheory

theorem exists_dual_nbhd : ∀ {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (ψ : AddChar (Fv F v) ℂ),
    Continuous ψ → ψ ≠ 1 → ∀ {κ : Type} [Fintype κ] (N : Set ((κ → Fv F v) × (κ → Fv F v))), N ∈ nhds 0 →
    ∃ Y : AddSubgroup ((κ → Fv F v) × (κ → Fv F v)),
      (∀ w' : (κ → Fv F v) × (κ → Fv F v), (∀ w ∈ Y, ψ (w'.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ w'.2) = 1) → w' ∈ N) ∧
      ∃ N' ∈ nhds (0 : (κ → Fv F v) × (κ → Fv F v)), ∀ w' ∈ N', ∀ w ∈ Y, ψ (w'.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ w'.2) = 1 := by
  intro F _ _ v ψ hψc hψ κ _ N hN
  obtain ⟨U₀, hU₀⟩ := Tw.HeisLatVac.lc_exists_open_ker ψ hψc
  obtain ⟨t₀, ht₀⟩ := AddChar.ne_one_iff.1 hψ
  have ht₀0 : t₀ ≠ 0 := by rintro rfl; exact ht₀ (AddChar.map_zero_eq_one ψ)
  haveI := GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v
  have hOc : IsCompact ((v.adicCompletionIntegers F : Set (Fv F v))) :=
    isCompact_iff_compactSpace.2 ‹_›
  set C : Set ((κ → Fv F v) × (κ → Fv F v)) :=
    Set.univ.pi (fun _ => (v.adicCompletionIntegers F : Set (Fv F v))) ×ˢ
      Set.univ.pi (fun _ => (v.adicCompletionIntegers F : Set (Fv F v))) with hC
  have hCc : IsCompact C := (isCompact_univ_pi fun _ => hOc).prod (isCompact_univ_pi fun _ => hOc)
  have hev : ∀ᶠ a in nhds (0 : Fv F v), ∀ w ∈ C, a • w ∈ N := by
    refine hCc.eventually_forall_of_forall_eventually fun w _ => ?_
    have h1 : Filter.Tendsto (fun z : Fv F v × ((κ → Fv F v) × (κ → Fv F v)) => z.1 • z.2)
        (nhds (0, w)) (nhds ((0 : Fv F v) • w)) := continuous_smul.continuousAt
    rw [zero_smul] at h1
    exact h1 hN
  haveI hne : (nhdsWithin (0 : Fv F v) {0}ᶜ).NeBot := by
    letI : NontriviallyNormedField (v.adicCompletion F) := Valued.toNontriviallyNormedField _ _
    exact NormedField.nhdsNE_neBot 0
  obtain ⟨a, haC, ha0⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (eventually_mem_nhdsWithin (a := (0 : Fv F v)) (s := {0}ᶜ))).exists
  have ha0' : a ≠ 0 := ha0
  set b : Fv F v := a * t₀⁻¹ with hb
  have hb0 : b ≠ 0 := mul_ne_zero ha0' (inv_ne_zero ht₀0)
  let Y : AddSubgroup ((κ → Fv F v) × (κ → Fv F v)) :=
    { carrier := {w | ∀ i, b * w.1 i ∈ v.adicCompletionIntegers F ∧ b * w.2 i ∈ v.adicCompletionIntegers F}
      add_mem' := fun {x y} hx hy i =>
        ⟨by simpa [mul_add] using add_mem (hx i).1 (hy i).1,
         by simpa [mul_add] using add_mem (hx i).2 (hy i).2⟩
      zero_mem' := fun i => by simp
      neg_mem' := fun {x} hx i =>
        ⟨by simpa [mul_neg] using neg_mem (hx i).1, by simpa [mul_neg] using neg_mem (hx i).2⟩ }
  have hYC : ∀ w ∈ Y, w ∈ (fun x => b⁻¹ • x) '' C := by
    intro w hw
    refine ⟨b • w, ?_, inv_smul_smul₀ hb0 w⟩
    simp only [hC, Set.mem_prod, Set.mem_univ_pi, SetLike.mem_coe]
    exact ⟨fun i => (hw i).1, fun i => (hw i).2⟩
  have hev2 : ∀ᶠ w' in nhds (0 : (κ → Fv F v) × (κ → Fv F v)), ∀ w ∈ (fun x => b⁻¹ • x) '' C,
      (w'.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ w'.2) ∈ (U₀ : Set (Fv F v)) := by
    refine (hCc.image (continuous_const_smul b⁻¹)).eventually_forall_of_forall_eventually fun w _ => ?_
    have hc : Continuous fun z : ((κ → Fv F v) × (κ → Fv F v)) × ((κ → Fv F v) × (κ → Fv F v)) =>
        z.1.1 ⬝ᵥ z.2.2 - z.2.1 ⬝ᵥ z.1.2 :=
      ((continuous_fst.fst).dotProduct continuous_snd.snd).sub
        ((continuous_snd.fst).dotProduct continuous_fst.snd)
    have h1 : Filter.Tendsto (fun z : ((κ → Fv F v) × (κ → Fv F v)) × ((κ → Fv F v) × (κ → Fv F v)) =>
        z.1.1 ⬝ᵥ z.2.2 - z.2.1 ⬝ᵥ z.1.2) (nhds ((0 : (κ → Fv F v) × (κ → Fv F v)), w)) (nhds 0) := by
      convert hc.tendsto ((0 : (κ → Fv F v) × (κ → Fv F v)), w) using 2
      simp
    exact h1 (U₀.isOpen.mem_nhds U₀.zero_mem)
  refine ⟨Y, ?_, _, hev2, fun w' hw' w hw => hU₀ _ (hw' w (hYC w hw))⟩
  intro w' hw'
  by_contra hN'
  have hnC : a⁻¹ • w' ∉ C := by
    intro h
    apply hN'
    have := haC _ h
    rwa [smul_inv_smul₀ ha0'] at this
  simp only [hC, Set.mem_prod, Set.mem_univ_pi, SetLike.mem_coe, not_and_or, not_forall] at hnC
  rcases hnC with ⟨i, hi⟩ | ⟨i, hi⟩
  · have ht : w'.1 i ≠ 0 := by
      intro h; apply hi; simp [h]
    have hinv : (a⁻¹ * w'.1 i)⁻¹ ∈ v.adicCompletionIntegers F :=
      (ValuationSubring.mem_or_inv_mem _ _).resolve_left (by simpa using hi)
    have hw : ((0 : κ → Fv F v), Pi.single i (t₀ / w'.1 i)) ∈ Y := by
      intro j
      refine ⟨by simp, ?_⟩
      by_cases hj : j = i
      · subst hj
        convert hinv using 1
        simp only [Pi.single_eq_same, hb]
        field_simp
      · simp [Pi.single_apply, hj]
    apply ht₀
    convert hw' _ hw using 2
    simp [dotProduct_single]
    field_simp
  · have ht : w'.2 i ≠ 0 := by
      intro h; apply hi; simp [h]
    have hinv : (a⁻¹ * w'.2 i)⁻¹ ∈ v.adicCompletionIntegers F :=
      (ValuationSubring.mem_or_inv_mem _ _).resolve_left (by simpa using hi)
    have hw : (Pi.single i (-(t₀ / w'.2 i)), (0 : κ → Fv F v)) ∈ Y := by
      intro j
      refine ⟨?_, by simp⟩
      by_cases hj : j = i
      · subst hj
        have := neg_mem hinv
        convert this using 1
        simp only [Pi.single_eq_same, hb]
        field_simp
      · simp [Pi.single_apply, hj]
    apply ht₀
    convert hw' _ hw using 2
    simp [single_dotProduct]
    field_simp
end Tw.SympDualNbhd
end
end

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

namespace Tw.VacLoc
open _root_.GlobalTheory

theorem exists_twisted_sum_ne_zero : ∀ {G Y X : Type} [AddCommGroup G] [Fintype G] [AddCommGroup Y] [AddCommGroup X] [Module ℂ X]
    (θ : Y → AddChar G ℂ), (∀ w w', θ (w + w') = θ w * θ w') → (∀ a : G, (∀ w, θ w a = 1) → a = 0) →
    ∀ c : G → X, c 0 ≠ 0 → ∃ w, ∑ a, θ w a • c a ≠ 0 := by
  intro G Y X _ _ _ _ _ θ hθ hsep c hc0
  classical
  by_contra hall
  push_neg at hall
  have h1 : θ 0 = 1 := by
    have := hθ 0 0
    rw [add_zero] at this
    exact mul_left_cancel (a := θ 0) (by rw [mul_one]; exact this.symm)
  let S : Subgroup (AddChar G ℂ) :=
    { carrier := Set.range θ
      one_mem' := ⟨0, h1⟩
      mul_mem' := by rintro _ _ ⟨w, rfl⟩ ⟨w', rfl⟩; exact ⟨w + w', hθ w w'⟩
      inv_mem' := by
        rintro _ ⟨w, rfl⟩
        exact ⟨-w, eq_inv_of_mul_eq_one_right (by rw [← hθ, add_neg_cancel, h1])⟩ }
  have key : ∀ a : G, a ≠ 0 → ∑ s : S, (s : AddChar G ℂ) a = 0 := by
    intro a ha
    obtain ⟨w, hw⟩ : ∃ w, θ w a ≠ 1 := by
      by_contra h
      push_neg at h
      exact ha (hsep a h)
    let s₀ : S := ⟨θ w, w, rfl⟩
    have e : ∑ s : S, (s : AddChar G ℂ) a = θ w a * ∑ s : S, (s : AddChar G ℂ) a := by
      rw [Finset.mul_sum]
      exact (Fintype.sum_equiv (Equiv.mulLeft s₀) (fun s => θ w a * (s : AddChar G ℂ) a)
        (fun s => (s : AddChar G ℂ) a) (fun s => by simp [s₀])).symm
    have h2 : (1 - θ w a) * ∑ s : S, (s : AddChar G ℂ) a = 0 := by rw [sub_mul, one_mul, ← e, sub_self]
    exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr (Ne.symm hw))
  have hsum : ∀ s : S, ∑ a, (s : AddChar G ℂ) a • c a = 0 := by
    rintro ⟨_, w, rfl⟩
    exact hall w
  have htot : ∑ s : S, ∑ a, (s : AddChar G ℂ) a • c a = (∑ s : S, (s : AddChar G ℂ) 0) • c 0 := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul]
    rw [Finset.sum_eq_single (0 : G)]
    · intro a _ ha; rw [key a ha, zero_smul]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [Finset.sum_congr rfl (fun s _ => hsum s), Finset.sum_const_zero] at htot
  simp only [AddChar.map_zero_eq_one, Finset.sum_const, Finset.card_univ] at htot
  have hcard : (Fintype.card S : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [nsmul_eq_mul, mul_one] at htot
  exact hc0 ((smul_eq_zero.mp htot.symm).resolve_left hcard)

theorem avg_fixed : ∀ {A X : Type} [AddCommGroup A] [AddCommGroup X] [Module ℂ X] (H : AddSubgroup A)
    [Fintype (A ⧸ H)] (π : A → X →ₗ[ℂ] X), (∀ a b x, π (a + b) x = π a (π b x)) →
    ∀ x₀ : X, (∀ h ∈ H, π h x₀ = x₀) → ∀ b : A,
      π b (∑ q : A ⧸ H, π (Quotient.out q) x₀) = ∑ q : A ⧸ H, π (Quotient.out q) x₀ := by
  intro A X _ _ _ H _ π hπ x₀ hx₀ b
  have hrep : ∀ a : A, π (Quotient.out (a : A ⧸ H)) x₀ = π a x₀ := by
    intro a
    have h : -a + Quotient.out (a : A ⧸ H) ∈ H :=
      QuotientAddGroup.eq.mp (QuotientAddGroup.out_eq' (a : A ⧸ H)).symm
    rw [show Quotient.out (a : A ⧸ H) = a + (-a + Quotient.out (a : A ⧸ H)) by abel, hπ, hx₀ _ h]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  calc ∑ q : A ⧸ H, π b (π (Quotient.out q) x₀) = ∑ q : A ⧸ H, π (b + Quotient.out q) x₀ :=
        Finset.sum_congr rfl fun q _ => (hπ _ _ _).symm
    _ = ∑ q : A ⧸ H, π (Quotient.out ((b : A ⧸ H) + q)) x₀ := by
        refine Finset.sum_congr rfl fun q _ => ?_
        conv_rhs => rw [← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.mk_add, hrep]
    _ = ∑ q : A ⧸ H, π (Quotient.out q) x₀ :=
        Fintype.sum_equiv (Equiv.addLeft (b : A ⧸ H)) _ _ (fun _ => rfl)

end Tw.VacLoc

namespace Tw.VacLoc
open _root_.GlobalTheory

open GlobalTheory.WeilM

section Schr

variable {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]

def schrL (w : (κ → R) × (κ → R)) : ((κ → R) → ℂ) →ₗ[ℂ] ((κ → R) → ℂ) where
  toFun := schr ψ w
  map_add' f g := by funext x; simp only [schr, Pi.add_apply]; ring
  map_smul' c f := by funext x; simp only [schr, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem schr_zero_vec (φ : (κ → R) → ℂ) : schr ψ 0 φ = φ := by
  funext x; simp [schr]

theorem schr_neg_schr (w : (κ → R) × (κ → R)) (φ : (κ → R) → ℂ) : schr ψ (-w) (schr ψ w φ) = φ := by
  rw [schr_schr, neg_add_cancel, schr_zero_vec]
  simp [neg_dotProduct, dotProduct_neg]

theorem schr_comm (v w : (κ → R) × (κ → R)) (φ : (κ → R) → ℂ) :
    schr ψ v (schr ψ w φ) = ψ (v.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ v.2) • schr ψ w (schr ψ v φ) := by
  funext x
  simp only [schr, Pi.smul_apply, smul_eq_mul, ← mul_assoc, ← AddChar.map_add_eq_mul, add_dotProduct]
  congr 1
  · congr 1; ring
  · congr 1; abel

end Schr


set_option maxHeartbeats 1000000 in
theorem exists_schr_eigen : ∀ {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (ψ : AddChar (Fv F v) ℂ), Continuous ψ → ψ ≠ 1 →
    ∀ {κ M : Type} [Fintype κ] [Fintype M] (u : M → (κ → Fv F v) × (κ → Fv F v))
      (χ : (M → v.adicCompletionIntegers F) → ℂ), Continuous χ →
      (∀ a : M → v.adicCompletionIntegers F, ∑ m, (a m : Fv F v) • u m = 0 → χ a = 1) →
      (∀ a b : M → v.adicCompletionIntegers F, χ (a + b) = χ a * χ b *
        ψ (-(⅟(2 : Fv F v) * ((∑ m, (a m : Fv F v) • u m).1 ⬝ᵥ (∑ m, (b m : Fv F v) • u m).2 -
          (∑ m, (b m : Fv F v) • u m).1 ⬝ᵥ (∑ m, (a m : Fv F v) • u m).2)))) →
      ∃ φ ∈ GlobalTheory.WeilM.SB (κ → Fv F v), φ ≠ 0 ∧
        ∀ a : M → v.adicCompletionIntegers F, GlobalTheory.WeilM.schr ψ (∑ m, (a m : Fv F v) • u m) φ = χ a • φ := by
  intro F _ _ v ψ hψc hψ1 κ M _ _ u χ hχc hker hco
  haveI := GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v
  let lamH : (M → v.adicCompletionIntegers F) →+ (κ → Fv F v) × (κ → Fv F v) :=
    { toFun := fun a => ∑ m, (a m : Fv F v) • u m
      map_zero' := by simp
      map_add' := fun a b => by simp [add_smul, Finset.sum_add_distrib] }
  have hlamc : Continuous lamH := by
    show Continuous fun a : M → v.adicCompletionIntegers F => ∑ m, (a m : Fv F v) • u m
    exact continuous_finsetSum _ fun m _ => by fun_prop
  have hχ0 : χ 0 = 1 := hker 0 (by simp)
  have hco' : ∀ a b, χ (a + b) = χ a * χ b *
      (ψ (⅟(2 : Fv F v) * ((lamH a).1 ⬝ᵥ (lamH b).2 - (lamH b).1 ⬝ᵥ (lamH a).2)))⁻¹ := fun a b => by
    rw [← AddChar.map_neg_eq_inv]; exact hco a b
  have hχne : ∀ a, χ a ≠ 0 := by
    intro a h
    have := hco a (-a)
    rw [add_neg_cancel, hχ0, h, zero_mul, zero_mul] at this
    exact one_ne_zero this

  let ε : (κ → Fv F v) × (κ → Fv F v) → (κ → Fv F v) × (κ → Fv F v) → ℂ :=
    fun x y => ψ (-(⅟(2 : Fv F v) * (x.1 ⬝ᵥ y.2 - y.1 ⬝ᵥ x.2)))
  have hε0 : ∀ x, ε x 0 = 1 := fun x => by simp [ε]
  obtain ⟨U₀, hU₀⟩ := Tw.HeisLatVac.lc_exists_open_ker ψ hψc
  have hεN : ∃ N ∈ nhds (0 : (κ → Fv F v) × (κ → Fv F v)), ∀ x ∈ N, ∀ y ∈ N, ε x y = 1 := by
    have hcont : Continuous fun p : ((κ → Fv F v) × (κ → Fv F v)) × ((κ → Fv F v) × (κ → Fv F v)) =>
        -(⅟(2 : Fv F v) * (p.1.1 ⬝ᵥ p.2.2 - p.2.1 ⬝ᵥ p.1.2)) :=
      (continuous_const.mul ((continuous_fst.fst.dotProduct continuous_snd.snd).sub
        (continuous_snd.fst.dotProduct continuous_fst.snd))).neg
    have hmem := (U₀.isOpen.preimage hcont).mem_nhds (x := ((0 : (κ → Fv F v) × (κ → Fv F v)), (0 : (κ → Fv F v) × (κ → Fv F v)))) (by simp)
    rw [nhds_prod_eq] at hmem
    obtain ⟨N, hN, hNN⟩ := Filter.mem_prod_self_iff.mp hmem
    refine ⟨N, hN, fun x hx y hy => ?_⟩
    have h1 := hNN (Set.mk_mem_prod hx hy)
    rw [Set.mem_preimage] at h1
    exact hU₀ _ h1
  obtain ⟨U, hU, hUχ⟩ := GlobalTheory.T.continuous_character_cocycle_trivial_near_zero lamH hlamc ε hεN hε0 χ hχc (fun a h => hker a h) (fun a b => hco a b)
  obtain ⟨φ₁, hφ₁SB, hφ₁0, U', hU', hU'φ⟩ := Tw.SchrTestVec.exists_fixed v ψ hψc (κ := κ)
  obtain ⟨Y, hYsep, N', hN', hN'Y⟩ := Tw.SympDualNbhd.exists_dual_nbhd v ψ hψc hψ1 (U ∩ U') (Filter.inter_mem hU hU')

  let β : (κ → Fv F v) × (κ → Fv F v) → (κ → Fv F v) × (κ → Fv F v) → ℂ :=
    fun w' w => ψ (w'.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ w'.2)
  have hβadd : ∀ w₁ w₂ w, β (w₁ + w₂) w = β w₁ w * β w₂ w := by
    intro w₁ w₂ w
    simp only [β, Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add, ← AddChar.map_add_eq_mul]
    congr 1; ring
  have hβadd' : ∀ w' w₁ w₂, β w' (w₁ + w₂) = β w' w₁ * β w' w₂ := by
    intro w' w₁ w₂
    simp only [β, Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add, ← AddChar.map_add_eq_mul]
    congr 1; ring
  have hβ0 : ∀ w, β 0 w = 1 := fun w => by simp [β]
  let Ks : AddSubgroup (M → v.adicCompletionIntegers F) :=
    { carrier := {a | ∀ w ∈ Y, β (lamH a) w = 1}
      zero_mem' := fun w _ => by rw [map_zero]; exact hβ0 w
      add_mem' := fun {a b} ha hb w hw => by rw [map_add (f := _), hβadd, ha w hw, hb w hw, one_mul]
      neg_mem' := fun {a} ha w hw => by
        have := hβadd (lamH a) (-(lamH a)) w
        rw [add_neg_cancel, ha w hw, one_mul, hβ0] at this
        show β (lamH (-a)) w = 1
        rw [map_neg]; exact this.symm }
  have hKs : ∀ a, a ∈ Ks ↔ ∀ w ∈ Y, β (lamH a) w = 1 := fun a => Iff.rfl
  have hKsopen : IsOpen (Ks : Set (M → v.adicCompletionIntegers F)) := by
    refine AddSubgroup.isOpen_of_mem_nhds Ks (g := 0) ?_
    have : lamH ⁻¹' N' ∈ nhds (0 : M → v.adicCompletionIntegers F) :=
      hlamc.continuousAt.preimage_mem_nhds (by rw [map_zero]; exact hN')
    exact Filter.mem_of_superset this fun a ha w hw => hN'Y _ ha w hw
  haveI : Finite ((M → v.adicCompletionIntegers F) ⧸ Ks) := AddSubgroup.quotient_finite_of_isOpen Ks hKsopen
  letI : Fintype ((M → v.adicCompletionIntegers F) ⧸ Ks) := Fintype.ofFinite _
  have hKsUU : ∀ a ∈ Ks, lamH a ∈ U ∩ U' := fun a ha => hYsep _ ha

  let πL : (M → v.adicCompletionIntegers F) → ((κ → Fv F v) → ℂ) →ₗ[ℂ] ((κ → Fv F v) → ℂ) :=
    fun a => (χ a)⁻¹ • schrL ψ (lamH a)
  have hπ : ∀ a φ, πL a φ = (χ a)⁻¹ • schr ψ (lamH a) φ := fun _ _ => rfl
  have hlin : ∀ (w : (κ → Fv F v) × (κ → Fv F v)) (c : ℂ) (f : (κ → Fv F v) → ℂ),
      schr ψ w (c • f) = c • schr ψ w f := fun w c f => (schrL ψ w).map_smul c f
  have hπmul : ∀ a b φ, πL (a + b) φ = πL a (πL b φ) := by
    intro a b φ
    rw [hπ, hπ, hπ, hlin, schr_schr, smul_smul, smul_smul, map_add (f := _)]
    congr 1
    rw [hco' a b, mul_inv, mul_inv, inv_inv]
  have hconj : ∀ a (w : (κ → Fv F v) × (κ → Fv F v)) φ,
      πL a (schr ψ w φ) = schr ψ w (β (lamH a) w • πL a φ) := by
    intro a w φ
    rw [hπ, hπ, schr_comm ψ (lamH a) w φ, hlin, hlin, smul_comm]
  have hπK : ∀ k ∈ Ks, πL k φ₁ = φ₁ := by
    intro k hk
    rw [hπ, hUχ k (hKsUU k hk).1, hU'φ _ (hKsUU k hk).2, inv_one, one_smul]

  have hper : ∀ {γ : Type} (f : (M → v.adicCompletionIntegers F) → γ),
      (∀ a, ∀ h ∈ Ks, f (a + h) = f a) → ∀ a : M → v.adicCompletionIntegers F, f (Quotient.out (a : (M → v.adicCompletionIntegers F) ⧸ Ks)) = f a := by
    intro γ f hf a
    have h : -a + Quotient.out (a : (M → v.adicCompletionIntegers F) ⧸ Ks) ∈ Ks :=
      QuotientAddGroup.eq.mp (QuotientAddGroup.out_eq' (a : (M → v.adicCompletionIntegers F) ⧸ Ks)).symm
    rw [show Quotient.out (a : (M → v.adicCompletionIntegers F) ⧸ Ks) =
      a + (-a + Quotient.out (a : (M → v.adicCompletionIntegers F) ⧸ Ks)) by abel]
    exact hf a _ h
  have hβper : ∀ w ∈ Y, ∀ a, ∀ h ∈ Ks, β (lamH (a + h)) w = β (lamH a) w := by
    intro w hw a h hh
    rw [map_add (f := _), hβadd, (hKs h).mp hh w hw, mul_one]
  have hout0 : Quotient.out (0 : (M → v.adicCompletionIntegers F) ⧸ Ks) ∈ Ks :=
    (QuotientAddGroup.eq_zero_iff _).mp (QuotientAddGroup.out_eq' 0)
  let θ : Y → AddChar ((M → v.adicCompletionIntegers F) ⧸ Ks) ℂ := fun w =>
    { toFun := fun q => β (lamH (Quotient.out q)) w
      map_zero_eq_one' := (hKs _).mp hout0 w w.2
      map_add_eq_mul' := by
        intro q q'
        induction q using QuotientAddGroup.induction_on with | H a => ?_
        induction q' using QuotientAddGroup.induction_on with | H b => ?_
        rw [← QuotientAddGroup.mk_add, hper (fun a => β (lamH a) w) (hβper w w.2),
          hper (fun a => β (lamH a) w) (hβper w w.2), hper (fun a => β (lamH a) w) (hβper w w.2), map_add, hβadd] }
  have hθ : ∀ w q, θ w q = β (lamH (Quotient.out q)) w := fun _ _ => rfl
  have hθadd : ∀ w w', θ (w + w') = θ w * θ w' := by
    intro w w'
    ext q
    rw [mul_apply, hθ, hθ, hθ, AddSubgroup.coe_add, hβadd']
  have hθsep : ∀ q, (∀ w, θ w q = 1) → q = 0 := by
    intro q hq
    induction q using QuotientAddGroup.induction_on with | H a => ?_
    refine (QuotientAddGroup.eq_zero_iff a).mpr ((hKs a).mpr fun w hw => ?_)
    have := hq ⟨w, hw⟩
    rwa [hθ, hper (fun a => β (lamH a) w) (hβper w hw)] at this
  let c : (M → v.adicCompletionIntegers F) ⧸ Ks → ((κ → Fv F v) → ℂ) := fun q => πL (Quotient.out q) φ₁
  have hc0 : c 0 ≠ 0 := by
    show πL (Quotient.out (0 : (M → v.adicCompletionIntegers F) ⧸ Ks)) φ₁ ≠ 0
    rw [hπK _ hout0]; exact hφ₁0
  obtain ⟨w₀, hw₀⟩ := exists_twisted_sum_ne_zero θ hθadd hθsep c hc0
  have hx₀ : ∀ h ∈ Ks, πL h (schr ψ (w₀ : (κ → Fv F v) × (κ → Fv F v)) φ₁) = schr ψ (w₀ : (κ → Fv F v) × (κ → Fv F v)) φ₁ := by
    intro h hh
    rw [hconj, hπK h hh, (hKs h).mp hh w₀ w₀.2, one_smul]
  have hsum : schr ψ (w₀ : (κ → Fv F v) × (κ → Fv F v)) (∑ q, θ w₀ q • c q) =
      ∑ q : (M → v.adicCompletionIntegers F) ⧸ Ks, πL (Quotient.out q) (schr ψ (w₀ : (κ → Fv F v) × (κ → Fv F v)) φ₁) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [show schr ψ (w₀ : (κ → Fv F v) × (κ → Fv F v)) (∑ q, θ w₀ q • c q) =
      ∑ q, schr ψ (w₀ : (κ → Fv F v) × (κ → Fv F v)) (θ w₀ q • c q) from map_sum (schrL ψ (w₀ : (κ → Fv F v) × (κ → Fv F v))) _ _]
    exact Finset.sum_congr rfl fun q _ => (hconj _ _ _).symm
  refine ⟨∑ q : (M → v.adicCompletionIntegers F) ⧸ Ks, πL (Quotient.out q) (schr ψ (w₀ : (κ → Fv F v) × (κ → Fv F v)) φ₁),
    ?_, ?_, fun a => ?_⟩
  · refine Submodule.sum_mem _ fun q _ => ?_
    rw [hπ]
    exact Submodule.smul_mem _ _ (Tw.SchrSBFin.schr_mem_SB v ψ hψc _ _ (Tw.SchrSBFin.schr_mem_SB v ψ hψc _ _ hφ₁SB))
  · rw [← hsum]
    intro h0
    apply hw₀
    have := congrArg (schr ψ (-(w₀ : (κ → Fv F v) × (κ → Fv F v)))) h0
    rw [schr_neg_schr] at this
    rw [this]
    exact (schrL ψ (-(w₀ : (κ → Fv F v) × (κ → Fv F v)))).map_zero
  · have hinv := avg_fixed Ks πL hπmul _ hx₀ a
    rw [hπ] at hinv
    show schr ψ (lamH a) _ = χ a • _
    calc schr ψ (lamH a) _ = χ a • ((χ a)⁻¹ • schr ψ (lamH a) (∑ q : (M → v.adicCompletionIntegers F) ⧸ Ks,
          πL (Quotient.out q) (schr ψ (w₀ : (κ → Fv F v) × (κ → Fv F v)) φ₁))) := by
          rw [smul_smul, mul_inv_cancel₀ (hχne a), one_smul]
      _ = _ := by rw [hinv]

end Tw.VacLoc
end

section -- merged from Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.TensorLatticeAtFinitePlaceEqIntegralSpanGenerato
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

namespace Tw.LatParam
open _root_.GlobalTheory

theorem vecMulVec_sum_zsmul {E : Type} [Field E] {n d kx ky : ℕ} (ex : Fin kx → Fin n → E) (fy : Fin ky → Fin d → E)
    (c : Fin kx → ℤ) (c' : Fin ky → ℤ) :
    Matrix.vecMulVec (∑ i, c i • ex i) (∑ j, c' j • fy j) =
      ∑ m : Fin kx × Fin ky, (c m.1 * c' m.2) • Matrix.vecMulVec (ex m.1) (fy m.2) := by
  ext a b
  simp only [Matrix.vecMulVec_apply, Finset.sum_apply, Matrix.sum_apply, Matrix.smul_apply,
    zsmul_eq_mul]
  rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.mul_apply, Pi.intCast_apply]
  push_cast
  ring

theorem latAtV_param : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ} (X : Spc F E n)
    (Y : Spc F E d), X.L.IsLattice E → Y.L.IsLattice E → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F),
    ∃ (M : Type) (_ : Fintype M) (g : M → Matrix (Fin n) (Fin d) E), ∀ γ,
      γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v ↔ ∃ a : M → v.adicCompletionIntegers F,
        γ = ∑ m, GlobalTheory.EmbChart.atPlace v (a m : Fv F v) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g m) := by
  intro F E _ _ _ _ _ n d X Y hX hY v
  classical
  obtain ⟨kx, ex, hex⟩ := Submodule.fg_iff_exists_fin_generating_family.1 (hX.fg.restrictScalars (R := ℤ))
  obtain ⟨ky, fy, hfy⟩ := Submodule.fg_iff_exists_fin_generating_family.1 (hY.fg.restrictScalars (R := ℤ))
  have memX : ∀ x, x ∈ X.L ↔ ∃ c : Fin kx → ℤ, ∑ i, c i • ex i = x := by
    intro x
    rw [← Submodule.restrictScalars_mem ℤ, ← hex, Submodule.mem_span_range_iff_exists_fun]
  have memY : ∀ y, y ∈ Y.L ↔ ∃ c : Fin ky → ℤ, ∑ j, c j • fy j = y := by
    intro y
    rw [← Submodule.restrictScalars_mem ℤ, ← hfy, Submodule.mem_span_range_iff_exists_fun]
  have exX : ∀ i, ex i ∈ X.L := by
    intro i
    have h := Submodule.subset_span (R := ℤ) (Set.mem_range_self (f := ex) i)
    rw [hex] at h
    exact (Submodule.restrictScalars_mem ℤ _ _).1 h
  have exY : ∀ j, fy j ∈ Y.L := by
    intro j
    have h := Submodule.subset_span (R := ℤ) (Set.mem_range_self (f := fy) j)
    rw [hfy] at h
    exact (Submodule.restrictScalars_mem ℤ _ _).1 h
  refine ⟨Fin kx × Fin ky, inferInstance, fun m => Matrix.vecMulVec (ex m.1) (fy m.2), ?_⟩
  intro γ
  let φ : Matrix (Fin n) (Fin d) E →+ Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :=
    (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (E := E) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F)).toAddMonoidHom.mapMatrix
  have hφ : ∀ J, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F J = φ J := fun J => rfl
  have hsupp : ∀ a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (⇑(GlobalTheory.AdelicU.evFin F v)) a →
      a = GlobalTheory.EmbChart.atPlace v (GlobalTheory.AdelicU.evFin F v a) := by
    intro a ha
    have h1 : GlobalTheory.AdelicU.evFin F v (1 - GlobalTheory.EmbChart.atPlace v 1) = 0 := by
      rw [map_sub, map_one, GlobalTheory.EmbChart.evFin_atPlace, sub_self]
    have h2 := ha _ h1
    rw [smul_eq_mul, sub_mul, one_mul, sub_eq_zero] at h2
    calc a = GlobalTheory.EmbChart.atPlace v 1 * a := h2
      _ = GlobalTheory.EmbChart.atPlace v (1 * GlobalTheory.AdelicU.evFin F v a) := GlobalTheory.EmbChart.atPlace_mul_right v 1 a
      _ = GlobalTheory.EmbChart.atPlace v (GlobalTheory.AdelicU.evFin F v a) := by rw [one_mul]
  have hdef : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v = AddSubgroup.closure {z |
      ∃ a, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (⇑(GlobalTheory.AdelicU.evFin F v)) a ∧
        (GlobalTheory.AdelicU.evFin F v) a ∈ IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers F v ∧
          ∃ x ∈ X.L, ∃ y ∈ Y.L, z = a • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (Matrix.vecMulVec x y)} := rfl
  rw [hdef]
  constructor
  · intro hγ
    induction hγ using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, hav, x, hx, y, hy, rfl⟩ := hz
      obtain ⟨c, rfl⟩ := (memX x).1 hx
      obtain ⟨c', rfl⟩ := (memY y).1 hy
      refine ⟨fun m => (c m.1 * c' m.2) • ⟨_, hav⟩, ?_⟩
      beta_reduce
      set_option synthInstance.maxHeartbeats 100000 in
        rw [vecMulVec_sum_zsmul, hφ, map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [map_zsmul, smul_comm, AddSubgroupClass.coe_zsmul, map_zsmul, smul_assoc, ← hsupp a ha, hφ]
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a + b, by simp [Finset.sum_add_distrib, add_smul]⟩
    | neg x _ hx =>
      obtain ⟨a, rfl⟩ := hx
      exact ⟨-a, by simp [neg_smul]⟩
  · rintro ⟨a, rfl⟩
    refine AddSubgroup.sum_mem _ fun m _ => AddSubgroup.subset_closure ?_
    refine ⟨GlobalTheory.EmbChart.atPlace v (a m), ?_, ?_, ex m.1, exX _, fy m.2, exY _, rfl⟩
    · intro u hu
      rw [smul_eq_mul, mul_comm, GlobalTheory.EmbChart.atPlace_mul_right, hu, mul_zero, map_zero]
    · rw [GlobalTheory.EmbChart.evFin_atPlace]
      exact (a m).2

end Tw.LatParam
end

section -- merged from Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.ContinuousAddCharSymplecticSelfPairingPlaceCoord
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

namespace Tw.ContSymp
open _root_.GlobalTheory

theorem continuous_psi_symp_atPlace : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (ψ : AddChar (AF F) ℂ), Continuous ψ → ∀ {n d : ℕ} (JA : Matrix (Fin n) (Fin n) E) (JB : Matrix (Fin d) (Fin d) E)
    (o : E) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) {M : Type} [Fintype M] (g : M → Matrix (Fin n) (Fin d) E),
    Continuous (fun a : M → v.adicCompletionIntegers F => ψ (⅟(2 : AF F) *
      GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) o) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JA)
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JB)
        (∑ m, GlobalTheory.EmbChart.atPlace v (a m : Fv F v) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g m))
        (∑ m, GlobalTheory.EmbChart.atPlace v (a m : Fv F v) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g m)))) := by
  intro F E _ _ _ _ _ σ ψ hψ n d JA JB o v M _ g
  have ht : ∀ m : M, Continuous (fun a : M → v.adicCompletionIntegers F =>
      GlobalTheory.EmbChart.atPlace v (a m : Fv F v)) :=
    fun m => (GlobalTheory.VacAny.continuous_atPlace v).comp (continuous_subtype_val.comp (continuous_apply m))
  refine hψ.comp ?_
  delta GlobalTheory.WeilM.symp GlobalTheory.WeilM.hTens
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.sum_apply, Matrix.smul_apply, map_sum, map_smul,
    Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_eq_mul]
  fun_prop

end Tw.ContSymp
end

section -- merged from Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.AdelicSchrodingerTensorEqLocalOfSupportedAt
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

namespace Tw.SchrLoc
open _root_.GlobalTheory

open GlobalTheory.VacAny

theorem eq_atPlace_of_at {F : Type} [Field F] [NumberField F] {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} {z : AF F}
    (hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) z) :
    z = GlobalTheory.EmbChart.atPlace v (GlobalTheory.AdelicU.evFin F v z) := by
  have h1 := hz (1 - GlobalTheory.EmbChart.atPlace v 1)
    (by rw [map_sub, map_one, GlobalTheory.EmbChart.evFin_atPlace, sub_self])
  rw [smul_eq_mul, sub_mul, one_mul, sub_eq_zero] at h1
  conv_lhs => rw [h1]
  rw [GlobalTheory.EmbChart.atPlace_mul_right, one_mul]

theorem schr_tens_of_at : ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) {κ : Type} [Fintype κ]
    (w : (κ → AF F) × (κ → AF F)), (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (w.1 i)) →
    (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (w.2 i)) → ∀ (φ : (κ → Fv F v) → ℂ) (r : (κ → AF F) → ℂ),
    (∀ x z : κ → AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) z → r (x + z) = r x) →
    GlobalTheory.WeilM.schr ψ w (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.AdelicU.evFin F v) φ r) =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.AdelicU.evFin F v)
        (GlobalTheory.WeilM.schr (GlobalTheory.VacAny.psiV ψ v) (fun i => GlobalTheory.AdelicU.evFin F v (w.1 i), fun i => GlobalTheory.AdelicU.evFin F v (w.2 i)) φ) r := by
  intro F _ _ ψ v κ _ w h1 h2 φ r hr
  funext x
  have hr' : r (x + w.1) = r x := hr x w.1 (fun u hu => funext fun i => h1 i u hu)
  have hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (x ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) :=
    fun u hu => by
      simp only [smul_eq_mul, mul_add, dotProduct, Finset.mul_sum]
      have hzero (i : κ) : u * w.2 i = 0 := h2 i u hu
      suffices (∑ i, u * (x i * w.2 i)) = 0 ∧
          (∑ i, u * (⅟(2 : AF F) * (w.1 i * w.2 i))) = 0 by
        rw [this.1, this.2, add_zero]
      constructor <;> apply Finset.sum_eq_zero <;> intro i hi
      · calc
          u * (x i * w.2 i) = x i * (u * w.2 i) := by ring
          _ = 0 := by rw [hzero, mul_zero]
      · calc
          u * (⅟(2 : AF F) * (w.1 i * w.2 i)) = (⅟(2 : AF F) * w.1 i) * (u * w.2 i) := by ring
          _ = 0 := by rw [hzero, mul_zero]
  simp only [GlobalTheory.WeilM.schr, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens]
  rw [hr', eq_atPlace_of_at hz, ← psiV_apply]
  have hinv : GlobalTheory.AdelicU.evFin F v (⅟(2 : AF F)) = ⅟(2 : Fv F v) := by
    refine (invOf_eq_right_inv ?_).symm
    have h : GlobalTheory.AdelicU.evFin F v (2 * ⅟(2 : AF F)) = 1 := by rw [mul_invOf_self, map_one]
    rwa [map_mul, map_ofNat] at h
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dotProduct, map_add (f := _), map_mul, map_sum, hinv, Pi.add_apply]
  simp only [mul_comm (⅟(2 : Fv F v))]
  rw [show (fun i => GlobalTheory.AdelicU.evFin F v (x i) + GlobalTheory.AdelicU.evFin F v (w.1 i)) =
    (fun i => GlobalTheory.AdelicU.evFin F v (x i)) + (fun i => GlobalTheory.AdelicU.evFin F v (w.1 i)) from rfl]
  ring

end Tw.SchrLoc
end

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

noncomputable section

namespace Tw.VacAny
open _root_.GlobalTheory _root_.GlobalTheory.VacAny

private theorem at_sum {F : Type} [Field F] [NumberField F]
    {v : HeightOneSpectrum (𝓞 F)} {ι : Type} (s : Finset ι) {f : ι → AF F}
    (h : ∀ i ∈ s, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (AdelicU.evFin F v) (f i)) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (AdelicU.evFin F v) (∑ i ∈ s, f i) := fun u hu => by
  rw [Finset.smul_sum]
  exact Finset.sum_eq_zero fun i hi => h i hi u hu

private theorem at_mul_right {F : Type} [Field F] [NumberField F]
    {v : HeightOneSpectrum (𝓞 F)} {a : AF F}
    (ha : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (AdelicU.evFin F v) a) (b : AF F) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (AdelicU.evFin F v) (a * b) := fun u hu => by
  rw [smul_eq_mul, ← mul_assoc, show u * a = 0 from ha u hu, zero_mul]

private theorem at_mul_left {F : Type} [Field F] [NumberField F]
    {v : HeightOneSpectrum (𝓞 F)} (a : AF F) {b : AF F}
    (hb : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (AdelicU.evFin F v) b) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (AdelicU.evFin F v) (a * b) := by
  rw [mul_comm]; exact at_mul_right hb a

private theorem at_neg {F : Type} [Field F] [NumberField F]
    {v : HeightOneSpectrum (𝓞 F)} {a : AF F} (ha : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (AdelicU.evFin F v) a) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (AdelicU.evFin F v) (-a) := fun u hu => by
  rw [smul_neg, ha u hu, neg_zero]

private theorem at_atPlace {F : Type} [Field F] [NumberField F]
    {v : HeightOneSpectrum (𝓞 F)} (t : Fv F v) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (AdelicU.evFin F v)
      (GlobalTheory.EmbChart.atPlace v t) := fun u hu => by
  rw [smul_eq_mul, mul_comm, GlobalTheory.EmbChart.atPlace_mul_right, hu, mul_zero, map_zero]

private theorem at_sub {F : Type} [Field F] [NumberField F]
    {v : HeightOneSpectrum (𝓞 F)} {a b : AF F}
    (ha : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (AdelicU.evFin F v) a)
    (hb : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (AdelicU.evFin F v) b) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (AdelicU.evFin F v) (a - b) :=
  fun u hu => by rw [smul_sub, ha u hu, hb u hu, sub_self]

private theorem evFin_invOf_two {F : Type} [Field F] [NumberField F]
    {v : HeightOneSpectrum (𝓞 F)} :
    AdelicU.evFin F v (⅟(2 : AF F)) = ⅟(2 : Fv F v) := by
  refine (invOf_eq_right_inv ?_).symm
  have h : AdelicU.evFin F v (2 * ⅟(2 : AF F)) = 1 := by rw [mul_invOf_self, map_one]
  rwa [map_mul, map_ofNat] at h

theorem exists_isVac_any_darboux : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : Base F E), B.IsGood σ → ∀ {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (r s r' s' : ℕ),
    X.IsHerm σ B r s → Y.IsSkew σ B r' s' → ∀ (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J)) (Fin n × Fin d)) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)),
    ∃ φ, Model.IsVac (Model.mk (σ := σ) (X := X) (W := Y) co (fun _ => 0) 0 ∅) B.ψ v φ := by
  intro F E _ _ _ _ _ σ B hB n d X Y r s r' s' hX hY co v
  obtain ⟨θ, hθ⟩ := Tw.exists_int_add_conj_eq_one_of_base_good B hB
  obtain ⟨M, _, g, hΓ⟩ := Tw.LatParam.latAtV_param X Y hX.lat.toIsLattice hY.lat.toIsLattice v
  let γf : (M → v.adicCompletionIntegers F) → Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :=
    fun a => ∑ m, GlobalTheory.EmbChart.atPlace v (a m : Fv F v) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g m)
  let u : M → (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v) := fun m =>
    (fun i => GlobalTheory.AdelicU.evFin F v ((co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g m))).1 i),
     fun i => GlobalTheory.AdelicU.evFin F v ((co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g m))).2 i))
  let χ : (M → v.adicCompletionIntegers F) → ℂ := fun a => B.ψ (⅟(2 : AF F) *
    GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) (θ : E)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) (γf a) (γf a))
  have he : ∀ a, co.e (γf a) =
      ∑ m, GlobalTheory.EmbChart.atPlace v (a m : Fv F v) • co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g m)) := by
    intro a
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [γf, map_sum, map_smul]
  have hcomp : ∀ a i, (co.e (γf a)).1 i =
      ∑ m, GlobalTheory.EmbChart.atPlace v (a m : Fv F v) * (co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g m))).1 i ∧
      (co.e (γf a)).2 i =
      ∑ m, GlobalTheory.EmbChart.atPlace v (a m : Fv F v) * (co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g m))).2 i := by
    intro a i
    rw [he]
    simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, smul_eq_mul]
  have hAt : ∀ a i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) ((co.e (γf a)).1 i) ∧
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) ((co.e (γf a)).2 i) := by
    intro a i
    rw [(hcomp a i).1, (hcomp a i).2]
    exact ⟨at_sum _ fun m _ => at_mul_right (at_atPlace _) _,
      at_sum _ fun m _ => at_mul_right (at_atPlace _) _⟩
  have hev : ∀ a, ((fun i => GlobalTheory.AdelicU.evFin F v ((co.e (γf a)).1 i)),
      (fun i => GlobalTheory.AdelicU.evFin F v ((co.e (γf a)).2 i))) = ∑ m, (a m : Fv F v) • u m := by
    intro a
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
    set_option synthInstance.maxHeartbeats 100000 in
      · simp [(hcomp a i).1, map_sum, map_mul, GlobalTheory.EmbChart.evFin_atPlace, Prod.fst_sum, Finset.sum_apply, u]
    set_option synthInstance.maxHeartbeats 100000 in
      · simp [(hcomp a i).2, map_sum, map_mul, GlobalTheory.EmbChart.evFin_atPlace, Prod.snd_sum, Finset.sum_apply, u]
  have hψ : ∀ z : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) z →
      B.ψ z = GlobalTheory.VacAny.psiV B.ψ v (GlobalTheory.AdelicU.evFin F v z) := fun z hz => by
    rw [GlobalTheory.VacAny.psiV_apply, ← Tw.VacAny.eq_atPlace_of_at v z hz]
  have hzero : ∀ a, ∑ m, (a m : Fv F v) • u m = 0 → γf a = 0 := by
    intro a h
    rw [← hev a] at h
    have h1 : co.e (γf a) = 0 := by
      refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
      · rw [Tw.VacAny.eq_atPlace_of_at v _ (hAt a i).1, show GlobalTheory.AdelicU.evFin F v ((co.e (γf a)).1 i) = 0 from
          congrFun (congrArg Prod.fst h) i, map_zero]
        rfl
      · rw [Tw.VacAny.eq_atPlace_of_at v _ (hAt a i).2, show GlobalTheory.AdelicU.evFin F v ((co.e (γf a)).2 i) = 0 from
          congrFun (congrArg Prod.snd h) i, map_zero]
        rfl
    exact co.e.map_eq_zero_iff.1 h1
  have hker : ∀ a, ∑ m, (a m : Fv F v) • u m = 0 → χ a = 1 := by
    intro a h
    simp only [χ, hzero a h]
    simp [GlobalTheory.WeilM.symp, GlobalTheory.WeilM.hTens]
  have hadd : ∀ a b, γf (a + b) = γf a + γf b := by
    intro a b
    simp only [γf]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [show (((a + b) m : v.adicCompletionIntegers F) : Fv F v) = (a m : Fv F v) + b m from rfl, map_add (f := _), add_smul]
  have hmem : ∀ a, γf a ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v := fun a => (hΓ _).2 ⟨a, rfl⟩
  have hdot : ∀ a b, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) ((co.e (γf a)).1 ⬝ᵥ (co.e (γf b)).2) ∧
      GlobalTheory.AdelicU.evFin F v ((co.e (γf a)).1 ⬝ᵥ (co.e (γf b)).2) =
        (∑ m, (a m : Fv F v) • u m).1 ⬝ᵥ (∑ m, (b m : Fv F v) • u m).2 := by
    intro a b
    refine ⟨at_sum _ fun i _ => at_mul_right (hAt a i).1 _, ?_⟩
    rw [← hev a, ← hev b]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [dotProduct, map_sum, map_mul]
  have hcoc : ∀ a b, χ (a + b) = χ a * χ b * GlobalTheory.VacAny.psiV B.ψ v
      (-(⅟(2 : Fv F v) * ((∑ m, (a m : Fv F v) • u m).1 ⬝ᵥ (∑ m, (b m : Fv F v) • u m).2 -
        (∑ m, (b m : Fv F v) • u m).1 ⬝ᵥ (∑ m, (a m : Fv F v) • u m).2))) := by
    intro a b
    simp only [χ]
    rw [hadd, Tw.VacCocycle.psi_half_symp_add B hB X Y r s r' s' hX hY θ hθ v _ (hmem a) _ (hmem b), co.form]
    congr 1
    have hz := at_neg (at_mul_left (⅟(2 : AF F))
      (at_sub (hdot a b).1 (hdot b a).1))
    rw [hψ _ hz, map_neg, map_mul, map_sub, (hdot a b).2, (hdot b a).2, evFin_invOf_two]
  obtain ⟨φ, hφSB, hφ0, hφ⟩ := Tw.VacLoc.exists_schr_eigen v (GlobalTheory.VacAny.psiV B.ψ v) (GlobalTheory.VacAny.continuous_psiV hB.std.1 v)
    (Tw.PsiNontriv.psiV_ne_one B.ψ hB.std v) u χ (Tw.ContSymp.continuous_psi_symp_atPlace σ B.ψ hB.std.1 X.J Y.J (θ : E) v g) hker hcoc
  refine ⟨φ, hφSB, hφ0, θ, hθ, ?_⟩
  intro γ hγ
  obtain ⟨a, rfl⟩ := (hΓ γ).1 hγ
  intro rr hrr
  show GlobalTheory.WeilM.schr B.ψ (co.e (γf a)) _ = _
  rw [Tw.SchrLoc.schr_tens_of_at B.ψ v (co.e (γf a)) (fun i => (hAt a i).1) (fun i => (hAt a i).2) φ rr hrr.1, hev a, hφ a]

end Tw.VacAny
