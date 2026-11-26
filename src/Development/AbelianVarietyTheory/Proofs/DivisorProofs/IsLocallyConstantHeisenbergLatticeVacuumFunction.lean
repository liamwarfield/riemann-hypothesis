module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantFinprodSchwartzBruhatFiniteAdel
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoFromNormalization
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankWEigenpartEqRowsFullHecke
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineCharactersGivenJumpsUnramifiedTwists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridLocalTensorPlacesOverSplitPlaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalDarbouxHermitianTensorAdeles
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PstAndWdAtOfIsRegAlg
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RankOneLocalComponentDet
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCuspidalOfIsSupercuspidal

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantHeisenbergLatticeVacuumFunction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsBisLast
namespace GlobalTheory.IsotropicVectorExistence

theorem key {z : ℂ} (k : ℕ) (h : ∀ n : ℕ, ‖z ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) :
    (3 / 2 : ℝ) ^ k * ‖z - 1‖ ≤ ‖z ^ (2 ^ k) - 1‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : z ^ (2 ^ (k + 1)) - 1 = (z ^ (2 ^ k) - 1) * (z ^ (2 ^ k) + 1) := by
      rw [show 2 ^ (k + 1) = 2 ^ k * 2 from pow_succ 2 k, pow_mul]; ring
    have h2 : (3 / 2 : ℝ) ≤ ‖z ^ (2 ^ k) + 1‖ := by
      have h3 : (2 : ℂ) = (z ^ (2 ^ k) + 1) - (z ^ (2 ^ k) - 1) := by ring
      have h4 : ‖(2 : ℂ)‖ ≤ ‖z ^ (2 ^ k) + 1‖ + ‖z ^ (2 ^ k) - 1‖ := by
        rw [h3]; exact norm_sub_le _ _
      have h5 : ‖(2 : ℂ)‖ = 2 := by norm_num
      have h6 := h (2 ^ k)
      linarith
    rw [e, norm_mul, pow_succ]
    calc (3 / 2 : ℝ) ^ k * (3 / 2) * ‖z - 1‖ = ((3 / 2) ^ k * ‖z - 1‖) * (3 / 2) := by ring
      _ ≤ ‖z ^ (2 ^ k) - 1‖ * ‖z ^ (2 ^ k) + 1‖ :=
        mul_le_mul ih h2 (by norm_num) (norm_nonneg _)

theorem main : ∀ {z : ℂ}, (∀ (n : ℕ), ‖z ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) → z = (1 : ℂ) := by
  intro z h
  by_contra hne
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / (2 * ‖z - 1‖)) (by norm_num : (1 : ℝ) < 3 / 2)
  rw [div_lt_iff₀ (by positivity)] at hk
  have a := key k h
  have b := h (2 ^ k)
  nlinarith

end GlobalTheory.IsotropicVectorExistence
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantHeisenbergLatticeVacuumFunction
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.HeisLatVac

theorem lc_pow_near_one {z : ℂ} (h : ∀ n : ℕ, ‖z ^ n - 1‖ < 1 / 2) : z = 1 := by
  first
  | exact @_root_.GlobalTheory.IsotropicVectorExistence.main
  | exact _root_.GlobalTheory.IsotropicVectorExistence.main
  | (apply _root_.GlobalTheory.IsotropicVectorExistence.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IsotropicVectorExistence.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IsotropicVectorExistence.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IsotropicVectorExistence.main ..)

theorem lc_exists_open_ker {K : Type} [AddCommGroup K] [TopologicalSpace K] [NonarchimedeanAddGroup K]
    (ψ₀ : AddChar K ℂ) (hψ : Continuous ψ₀) : ∃ U₀ : OpenAddSubgroup K, ∀ t ∈ U₀, ψ₀ t = 1 := by
  have hV : {t : K | ‖ψ₀ t - 1‖ < 1 / 2} ∈ nhds (0 : K) :=
    (isOpen_lt (hψ.sub continuous_const).norm continuous_const).mem_nhds (by simp)
  obtain ⟨V, hV⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ hV
  refine ⟨V, fun t ht => lc_pow_near_one fun n => ?_⟩
  rw [← AddChar.map_nsmul_eq_pow]
  exact hV (V.toAddSubgroup.nsmul_mem ht n)

theorem lc_val {K κ : Type} [CommRing K] [Invertible (2 : K)] [Fintype κ] (ψ₀ : AddChar K ℂ)
    (Λ : AddSubgroup ((κ → K) × (κ → K))) (χ : (κ → K) × (κ → K) → ℂ) (x₀ : κ → K)
    (hco : ∀ u ∈ Λ, ∀ u' ∈ Λ, χ (u + u') = χ u * χ u' * ψ₀ (⅟(2 : K) * (u.1 ⬝ᵥ u'.2 - u'.1 ⬝ᵥ u.2)))
    (hy : ∀ y : κ → K, ((0 : κ → K), y) ∈ Λ → χ (0, y) = ψ₀ (x₀ ⬝ᵥ y))
    (u : (κ → K) × (κ → K)) (hu : u ∈ Λ) :
    vacFn ψ₀ Λ χ x₀ (x₀ + u.1) = χ u * ψ₀ (-(x₀ ⬝ᵥ u.2) - ⅟(2 : K) * (u.1 ⬝ᵥ u.2)) := by
  have h : ∃ u' ∈ Λ, x₀ + u.1 = x₀ + u'.1 := ⟨u, hu, rfl⟩
  rw [vacFn, dite_eq_left h]
  obtain ⟨hw, hwe⟩ := h.choose_spec
  generalize h.choose = w at hw hwe ⊢
  have h1 : w.1 = u.1 := (add_left_cancel hwe).symm
  have hyΛ : ((0 : κ → K), w.2 - u.2) ∈ Λ := by
    have e : ((0 : κ → K), w.2 - u.2) = w - u := Prod.ext (by simp [h1]) rfl
    rw [e]; exact Λ.sub_mem hw hu
  have hwu : w = u + (0, w.2 - u.2) := Prod.ext (by simp [h1]) (by simp)
  have e2 : χ w = χ u * χ (0, w.2 - u.2) * ψ₀ (⅟(2 : K) * (u.1 ⬝ᵥ (w.2 - u.2) - (0 : κ → K) ⬝ᵥ u.2)) := by
    conv_lhs => rw [hwu]
    exact hco u hu _ hyΛ
  rw [e2, hy _ hyΛ, h1, mul_assoc, mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 2
  simp only [zero_dotProduct, sub_zero, dotProduct_sub]
  ring

theorem isLocallyConstant_vacFn {K κ : Type} [CommRing K] [Invertible (2 : K)] [Fintype κ] [TopologicalSpace K]
    [IsTopologicalRing K] [NonarchimedeanAddGroup K] (ψ₀ : AddChar K ℂ) (hψ : Continuous ψ₀)
    (Λ : AddSubgroup ((κ → K) × (κ → K))) (hΛ : IsOpen (Λ : Set ((κ → K) × (κ → K))))
    (χ : (κ → K) × (κ → K) → ℂ) (x₀ : κ → K)
    (hco : ∀ u ∈ Λ, ∀ u' ∈ Λ, χ (u + u') = χ u * χ u' * ψ₀ (⅟(2 : K) * (u.1 ⬝ᵥ u'.2 - u'.1 ⬝ᵥ u.2)))
    (hy : ∀ y : κ → K, ((0 : κ → K), y) ∈ Λ → χ (0, y) = ψ₀ (x₀ ⬝ᵥ y))
    (h2 : ∀ u ∈ Λ, χ (u + u) = 1) : IsLocallyConstant (vacFn ψ₀ Λ χ x₀) := by
  obtain ⟨U₀, hU₀⟩ := lc_exists_open_ker ψ₀ hψ
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  rw [← map_add_left_nhds_zero, Filter.eventually_map]
  by_cases hx : ∃ u ∈ Λ, x = x₀ + u.1
  · obtain ⟨u, hu, rfl⟩ := hx
    have hN : {s : κ → K | (⅟(2 : K) • s, (0 : κ → K)) ∈ Λ ∧ s ⬝ᵥ u.2 ∈ (U₀ : Set K)} ∈ nhds (0 : κ → K) := by
      refine IsOpen.mem_nhds ?_ ?_
      · refine (hΛ.preimage ?_).inter (U₀.isOpen.preimage ?_)
        · exact (continuous_id.const_smul (⅟(2 : K))).prodMk (continuous_const : Continuous fun _ : κ → K => (0 : κ → K))
        · exact continuous_id.dotProduct continuous_const
      · refine ⟨?_, ?_⟩
        · show (⅟(2 : K) • (0 : κ → K), (0 : κ → K)) ∈ Λ
          rw [smul_zero, Prod.mk_zero_zero]; exact Λ.zero_mem
        · show (0 : κ → K) ⬝ᵥ u.2 ∈ (U₀ : Set K)
          rw [zero_dotProduct]; exact U₀.zero_mem
    filter_upwards [hN] with s hs
    obtain ⟨hs1, hs2⟩ := hs
    have hs0 : (s, (0 : κ → K)) ∈ Λ := by
      have e : (s, (0 : κ → K)) = (⅟(2 : K) • s, (0 : κ → K)) + (⅟(2 : K) • s, (0 : κ → K)) := by
        refine Prod.ext ?_ (by simp)
        simp only [Prod.fst_add]
        rw [← add_smul, invOf_two_add_invOf_two, one_smul]
      rw [e]; exact Λ.add_mem hs1 hs1
    have hχs : χ (s, 0) = 1 := by
      have e : (s, (0 : κ → K)) = (⅟(2 : K) • s, (0 : κ → K)) + (⅟(2 : K) • s, (0 : κ → K)) := by
        refine Prod.ext ?_ (by simp)
        simp only [Prod.fst_add]
        rw [← add_smul, invOf_two_add_invOf_two, one_smul]
      rw [e]; exact h2 _ hs1
    have hx' : x₀ + u.1 + s = x₀ + (u + (s, 0)).1 := by simp [add_assoc]
    have hneg : ψ₀ (-(s ⬝ᵥ u.2)) = 1 := hU₀ _ (U₀.neg_mem hs2)
    rw [hx', lc_val ψ₀ Λ χ x₀ hco hy _ (Λ.add_mem hu hs0), lc_val ψ₀ Λ χ x₀ hco hy u hu,
      hco u hu _ hs0, hχs, mul_one, mul_assoc, ← AddChar.map_add_eq_mul]
    have key : ⅟(2 : K) * (u.1 ⬝ᵥ (s, (0 : κ → K)).2 - (s, (0 : κ → K)).1 ⬝ᵥ u.2) +
        (-(x₀ ⬝ᵥ (u + (s, 0)).2) - ⅟(2 : K) * ((u + (s, 0)).1 ⬝ᵥ (u + (s, 0)).2)) =
        -(s ⬝ᵥ u.2) + (-(x₀ ⬝ᵥ u.2) - ⅟(2 : K) * (u.1 ⬝ᵥ u.2)) := by
      simp only [Prod.fst_add, Prod.snd_add, add_zero, dotProduct_zero, add_dotProduct]
      linear_combination (-(s ⬝ᵥ u.2)) * (invOf_two_add_invOf_two : ⅟(2 : K) + ⅟(2 : K) = 1)
    rw [key, AddChar.map_add_eq_mul, hneg, one_mul]
  · have h0 : vacFn ψ₀ Λ χ x₀ x = 0 := by rw [vacFn, dite_eq_right hx]
    have hN : {s : κ → K | (s, (0 : κ → K)) ∈ Λ} ∈ nhds (0 : κ → K) := by
      refine IsOpen.mem_nhds (hΛ.preimage (continuous_id.prodMk (continuous_const : Continuous fun _ : κ → K => (0 : κ → K)))) ?_
      show ((0 : κ → K), (0 : κ → K)) ∈ Λ
      rw [Prod.mk_zero_zero]; exact Λ.zero_mem
    filter_upwards [hN] with s hs
    rw [h0, vacFn, dite_eq_right]
    rintro ⟨u, hu, e⟩
    refine hx ⟨u - (s, 0), Λ.sub_mem hu hs, ?_⟩
    simp only [Prod.fst_sub]
    rw [← add_sub_assoc, ← e, add_sub_cancel_right]

end GlobalTheory.HeisLatVac


open GlobalTheory.HeisLatVac in
theorem GlobalTheory.HeisLatVac.isLocallyConstant_vacFn_place : ∀ {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) {κ : Type} [Fintype κ]
    (ψ₀ : AddChar (Fv F v) ℂ), Continuous ψ₀ → ∀ (Λ : AddSubgroup ((κ → Fv F v) × (κ → Fv F v))),
    IsOpen (Λ : Set ((κ → Fv F v) × (κ → Fv F v))) →
    ∀ (χ : (κ → Fv F v) × (κ → Fv F v) → ℂ) (x₀ : κ → Fv F v),
    (∀ u ∈ Λ, ∀ u' ∈ Λ, χ (u + u') = χ u * χ u' * ψ₀ (⅟(2 : Fv F v) * (u.1 ⬝ᵥ u'.2 - u'.1 ⬝ᵥ u.2))) →
    (∀ y : κ → Fv F v, ((0 : κ → Fv F v), y) ∈ Λ → χ (0, y) = ψ₀ (x₀ ⬝ᵥ y)) →
    (∀ u ∈ Λ, χ (u + u) = 1) → IsLocallyConstant (GlobalTheory.HeisLatVac.vacFn ψ₀ Λ χ x₀) := by
  intro F _ _ v κ _ ψ₀ hψ Λ hΛ χ x₀ hco hy h2
  exact isLocallyConstant_vacFn ψ₀ hψ Λ hΛ χ x₀ hco hy h2
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantHeisenbergLatticeVacuumFunctionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open scoped GlobalTheory.VacAny

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLocallyConstant_heisenberg_lattice_vacuum_function : ∀ {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) {κ : Type} [Fintype κ]
    (ψ₀ : AddChar (Fv F v) ℂ), Continuous ψ₀ → ∀ (Λ : AddSubgroup ((κ → Fv F v) × (κ → Fv F v))),
    IsOpen (Λ : Set ((κ → Fv F v) × (κ → Fv F v))) →
    ∀ (χ : (κ → Fv F v) × (κ → Fv F v) → ℂ) (x₀ : κ → Fv F v),
    (∀ u ∈ Λ, ∀ u' ∈ Λ, χ (u + u') = χ u * χ u' * ψ₀ (⅟(2 : Fv F v) * (u.1 ⬝ᵥ u'.2 - u'.1 ⬝ᵥ u.2))) →
    (∀ y : κ → Fv F v, ((0 : κ → Fv F v), y) ∈ Λ → χ (0, y) = ψ₀ (x₀ ⬝ᵥ y)) →
    (∀ u ∈ Λ, χ (u + u) = 1) → IsLocallyConstant (GlobalTheory.HeisLatVac.vacFn ψ₀ Λ χ x₀) := by
  first | exact @GlobalTheory.HeisLatVac.isLocallyConstant_vacFn_place | exact GlobalTheory.HeisLatVac.isLocallyConstant_vacFn_place | (intros; apply GlobalTheory.HeisLatVac.isLocallyConstant_vacFn_place <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodPlaceTranslateCombinationLatticeIndica
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodPlaceTranslateCombinationLatticeIndica
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

noncomputable section

namespace GlobalTheory.CombAtGood

theorem pure_mem_schA : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ)
    (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ), (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) →
    (∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∈ GlobalTheory.WeilM.schA F κ := by
  intro F _ _ κ _ f φ hSB hstd
  have hg : (fun y : κ → FiniteAdeleRing (𝓞 F) F => ∏ᶠ v, φ v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)) ∈
      GlobalTheory.WeilM.SB _ := ⟨GlobalTheory.T.isLocallyConstant_finprod_schwartzBruhat_finiteAdeles φ hSB hstd, GlobalTheory.T.hasCompactSupport_finprod_schwartzBruhat_finiteAdeles φ hSB hstd⟩
  exact Submodule.subset_span ⟨f, _, hg, rfl⟩

theorem exists_translates_primFrame_conj {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {D : Type} [Fintype D] [DecidableEq D] (ν α : kˣ →* ℂˣ)
    (hν : ∀ x, ‖(ν x : ℂ)‖ = 1) {a' : ℕ} (hd : (a' : ℝ) - 1 < (Fintype.card D : ℝ) / 2)
    (Λ : Submodule 𝒪[k] (D → k)) (P : GL (Fin a') k) (c : ℂ) :
    ∃ z : GL (Fin a') k →₀ ℂ, zdeg z ≠ 0 ∧ ∀ Y : Matrix (Fin a') D k,
      (z.sum fun g c' => c' • omB ν α g 1 (fun Y => c * (matLat (Fin a') Λ : Set (Matrix (Fin a') D k)).indicator 1 (P.val * Y))) Y =
        c * {Y : Matrix (Fin a') D k | IsPrimFrame Λ Y}.indicator 1 (P.val * Y) := by
  classical
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.SplitFlip.exists_isUnif (k := k)
  obtain ⟨z₀, h1, h2⟩ := exists_translates_eq_primFrame_lat hϖ ν α Λ a'
  let Q : GL (Fin a') k := Matrix.GeneralLinearGroup.mkOfDetNeZero P.valᵀ (by
    rw [Matrix.det_transpose]; exact P.isUnit.map Matrix.detMonoidHom |>.ne_zero)
  let cj : GL (Fin a') k → GL (Fin a') k := fun g => Q * g * Q⁻¹
  refine ⟨z₀.mapDomain cj, ?_, fun Y => ?_⟩
  · rw [zdeg, Finsupp.sum_mapDomain_index (by simp) (by simp), h2]
    exact prod_primFactor_ne_zero (hν ϖ) hd
  · have hdet : ∀ g, gdet (cj g) = gdet g := fun g => by
      simp only [cj, map_mul, map_inv]; exact mul_inv_cancel_comm _ _
    have hPQ : P.val * (Q⁻¹).valᵀ = 1 := by
      have h := congrArg Matrix.transpose (congrArg Units.val (inv_mul_cancel Q))
      rw [Units.val_mul, Matrix.transpose_mul, Units.val_one, Matrix.transpose_one] at h
      exact h
    have htr : ∀ (g : GL (Fin a') k) (Y : Matrix (Fin a') D k), P.val * ((cj g).valᵀ * Y * (1 : GL D k).val) = g.valᵀ * (P.val * Y) := by
      intro g Y
      simp only [cj, Units.val_mul, Matrix.transpose_mul, Units.val_one, Matrix.mul_one]
      have hQ : Q.valᵀ = P.val := Matrix.transpose_transpose _
      rw [hQ, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPQ, Matrix.one_mul, Matrix.mul_assoc]
    have key : ∀ g (Y : Matrix (Fin a') D k), omB ν α (cj g) 1 (fun Y => c * (matLat (Fin a') Λ : Set (Matrix (Fin a') D k)).indicator 1 (P.val * Y)) Y =
        c * omB ν α g 1 ((matLat (Fin a') Λ : Set (Matrix (Fin a') D k)).indicator 1) (P.val * Y) := by
      intro g Y
      simp only [omB]
      rw [hdet, htr, Units.val_one, Matrix.mul_one]
      ring
    rw [Finsupp.sum_mapDomain_index (f := cj) (s := z₀)
      (h := fun g (c' : ℂ) => c' • omB ν α g 1 (fun Y => c * (matLat (Fin a') Λ : Set (Matrix (Fin a') D k)).indicator 1 (P.val * Y)))
      (fun _ => zero_smul ℂ _) (fun _ _ _ => add_smul _ _ _), ← h1]
    simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, key, Finset.mul_sum]
    exact Finset.sum_congr rfl fun g _ => by ring

theorem exists_comb_translates_mem_So : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {a a' : ℕ} (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a')
    (hM' : Γ.M'.IsGood B.ψ) (hlt : a' < a)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W) {H : Type} (κ : H → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Γ.V'.J)
    (ν α : (Fv F B.v₁)ˣ →* ℂˣ) (hν : ∀ x, ‖(ν x : ℂ)‖ = 1)
    (ι : ((Fin a' × Fin (a + a') → Fv F B.v₁) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F B.v₁) → ℂ))
    (hι : Γ.M'.IsLinBar B.ψ B.τ₁ 1 1 ι)
    (hact : ∀ g : GL (Fin a') (Fv F B.v₁), ∃ k : H, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ r, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin F B.v₁) φ r →
      ∃ φ₁ ∈ GlobalTheory.WeilM.SB _, om' (κ k, 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F B.v₁) φ r) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F B.v₁) φ₁ r ∧
        ι φ₁ = omB ν α g 1 (ι φ))
    {m : ℕ} (f : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a')))
    (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin a' × Fin (a + a') → Fv F v) → ℂ)
    (φ₀ : (Fin a' × Fin (a + a') → Fv F B.v₁) → ℂ)
    (hSB : ∀ k v, φ k v ∈ GlobalTheory.WeilM.SB _) (hvac : ∀ k, ∀ᶠ v in Filter.cofinite, φ k v = Γ.M'.vac v) (h₀ : ∀ k, φ k B.v₁ = φ₀)
    (P : GL (Fin a') (Fv F B.v₁)) (Λ : Submodule 𝒪[Fv F B.v₁] (Fin (a + a') → Fv F B.v₁)) (c : ℂ)
    (hφ₀ : ∀ Y, ι φ₀ Y = c * (matLat (Fin a') Λ : Set _).indicator 1 (P.val * Y)),
    ∃ z : H →₀ ℂ, zdeg z ≠ 0 ∧
      (z.sum fun k c => c • om' (κ k, 1) (∑ k, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f k) (φ k))) ∈ Γ.M'.So B.ψ B.τ₁ := by
  intro F E _ _ _ _ _ σ a a' B Γ hM' hlt om' H κ ν α hν ι hι hact m f φ φ₀ hSB hvac h₀ P Λ c hφ₀
  classical
  have hd : ((a' : ℕ) : ℝ) - 1 < (Fintype.card (Fin (a + a')) : ℝ) / 2 := by
    rw [Fintype.card_fin]; push_cast
    have : (a' : ℝ) + 1 ≤ a := by exact_mod_cast hlt
    linarith
  obtain ⟨z₁, hz₁, hz₁Y⟩ := exists_translates_primFrame_conj ν α hν hd Λ P c
  choose kf hkf using hact
  refine ⟨z₁.mapDomain kf, ?_, ?_⟩
  · rw [zdeg, Finsupp.sum_mapDomain_index (by simp) (by simp)]
    exact hz₁
  rw [Finsupp.sum_mapDomain_index (f := kf) (s := z₁)
    (h := fun k (c' : ℂ) => c' • om' (κ k, 1) (∑ k, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f k) (φ k)))
    (fun _ => zero_smul ℂ _) (fun _ _ _ => add_smul _ _ _)]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finsupp.sum, map_sum, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hstd : ∀ᶠ v in Filter.cofinite, φ i v = Set.indicator {x | ∀ j, x j ∈ v.adicCompletionIntegers F} 1 :=
    ((hvac i).and hM'.std).mono fun v h => h.1.trans h.2
  obtain ⟨r, hr, hrt⟩ := GlobalTheory.T.exists_factor_pureTensor_component_at_place (B.v₁) (f i) (φ i) hstd
  have hφ₀SB : φ₀ ∈ GlobalTheory.WeilM.SB _ := h₀ i ▸ hSB i B.v₁
  have hpure : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F B.v₁) φ₀ r := by
    rw [hrt, ← h₀ i, Function.update_eq_self]
  have hRest : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin F B.v₁) φ₀ r := ⟨hr, hpure ▸ pure_mem_schA (f i) (φ i) (hSB i) hstd⟩
  have hinj := (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model.IsLin.bij hι).injOn
  let φ₁ : GL (Fin a') (Fv F B.v₁) → _ := fun g =>
    Function.invFunOn ι (GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F B.v₁) : Set _) (omB ν α g 1 (ι φ₀))
  have hφ₁ : ∀ g, φ₁ g ∈ GlobalTheory.WeilM.SB _ ∧ ι (φ₁ g) = omB ν α g 1 (ι φ₀) ∧
      om' (κ (kf g), 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F B.v₁) φ₀ r) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F B.v₁) (φ₁ g) r := by
    intro g
    obtain ⟨ψ₁, hψ₁, he, hι₁⟩ := hkf g φ₀ hφ₀SB r hRest
    have hex : ∃ x ∈ (GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F B.v₁) : Set _), ι x = omB ν α g 1 (ι φ₀) :=
      ⟨ψ₁, hψ₁, hι₁⟩
    have hm := Function.invFunOn_mem hex
    have heq := Function.invFunOn_eq hex
    have h' : ψ₁ = φ₁ g := hinj hψ₁ hm (hι₁.trans heq.symm)
    exact ⟨hm, heq, h' ▸ he⟩
  set Φ₁ := ∑ g ∈ z₁.support, z₁ g • φ₁ g with hΦ₁
  have hΦ₁SB : Φ₁ ∈ GlobalTheory.WeilM.SB _ := Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (hφ₁ g).1
  have htens : ∀ (s : Finset (GL (Fin a') (Fv F B.v₁))) (w : GL (Fin a') (Fv F B.v₁) → ℂ),
      ∑ g ∈ s, w g • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F B.v₁) (φ₁ g) r =
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F B.v₁) (∑ g ∈ s, w g • φ₁ g) r := by
    intro s w
    funext x
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, mul_assoc]
  have hsum : ∑ g ∈ z₁.support, z₁ g • om' (κ (kf g), 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)) =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (Function.update (φ i) B.v₁ Φ₁) := by
    rw [← hrt, hpure, ← htens]
    exact Finset.sum_congr rfl fun g _ => by rw [(hφ₁ g).2.2]
  rw [hsum]
  refine Submodule.subset_span ⟨f i, Function.update (φ i) B.v₁ Φ₁, fun v => ?_, ?_, ?_, rfl⟩
  · by_cases hv : v = B.v₁
    · subst hv; rw [Function.update_self]; exact hΦ₁SB
    · rw [Function.update_of_ne hv]; exact hSB i v
  · filter_upwards [hvac i, Filter.eventually_cofinite_ne B.v₁] with v h1 h2
    rw [Function.update_of_ne h2, h1]
  · rw [Function.update_self]
    refine ⟨hΦ₁SB, ι, hι, fun Y hY => ?_⟩
    have hιΦ : ι Φ₁ = ∑ g ∈ z₁.support, z₁ g • omB ν α g 1 (ι φ₀) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hΦ₁, map_sum]
      exact Finset.sum_congr rfl fun g _ => by rw [map_smul, (hφ₁ g).2.1]
    have hιφ₀ : ι φ₀ = fun Y => c * (matLat (Fin a') Λ : Set (Matrix (Fin a') (Fin (a + a')) (Fv F B.v₁))).indicator 1 (P.val * Y) :=
      funext hφ₀
    have h3 := hz₁Y Y
    rw [hιφ₀] at hιΦ
    rw [hιΦ, ← hιφ₀]
    rw [← hιφ₀] at h3
    simp only [Finsupp.sum] at h3
    rw [h3, Set.indicator_of_notMem, mul_zero]
    intro hp
    apply hY
    have h4 := hp.1
    rwa [Matrix.rank_mul_eq_right_of_isUnit_det _ _ (P.isUnit.map Matrix.detMonoidHom), Fintype.card_fin] at h4

end GlobalTheory.CombAtGood

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodPlaceTranslateCombinationLatticeIndicaStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_goodPlace_translateCombination_latticeIndicator : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {a a' : ℕ} (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a')
    (hM' : Γ.M'.IsGood B.ψ) (hlt : a' < a)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W) {H : Type} (κ : H → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Γ.V'.J)
    (ν α : (Fv F B.v₁)ˣ →* ℂˣ) (hν : ∀ x, ‖(ν x : ℂ)‖ = 1)
    (ι : ((Fin a' × Fin (a + a') → Fv F B.v₁) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F B.v₁) → ℂ))
    (hι : Γ.M'.IsLinBar B.ψ B.τ₁ 1 1 ι)
    (hact : ∀ g : GL (Fin a') (Fv F B.v₁), ∃ k : H, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ r, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin F B.v₁) φ r →
      ∃ φ₁ ∈ GlobalTheory.WeilM.SB _, om' (κ k, 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F B.v₁) φ r) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F B.v₁) φ₁ r ∧
        ι φ₁ = omB ν α g 1 (ι φ))
    {m : ℕ} (f : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a')))
    (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin a' × Fin (a + a') → Fv F v) → ℂ)
    (φ₀ : (Fin a' × Fin (a + a') → Fv F B.v₁) → ℂ)
    (hSB : ∀ k v, φ k v ∈ GlobalTheory.WeilM.SB _) (hvac : ∀ k, ∀ᶠ v in Filter.cofinite, φ k v = Γ.M'.vac v) (h₀ : ∀ k, φ k B.v₁ = φ₀)
    (P : GL (Fin a') (Fv F B.v₁)) (Λ : Submodule 𝒪[Fv F B.v₁] (Fin (a + a') → Fv F B.v₁)) (c : ℂ)
    (hφ₀ : ∀ Y, ι φ₀ Y = c * (matLat (Fin a') Λ : Set _).indicator 1 (P.val * Y)),
    ∃ z : H →₀ ℂ, zdeg z ≠ 0 ∧
      (z.sum fun k c => c • om' (κ k, 1) (∑ k, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f k) (φ k))) ∈ Γ.M'.So B.ψ B.τ₁ := by
  first | exact @GlobalTheory.CombAtGood.exists_comb_translates_mem_So | exact GlobalTheory.CombAtGood.exists_comb_translates_mem_So | (intros; apply GlobalTheory.CombAtGood.exists_comb_translates_mem_So <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransferEigensystemPartsThreeLevelsOfMultEq
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsHeckeOpFullIffIndependentOfBlockLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsHeckeOpFullIffIndependentOfBlockLevel
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.HeckeLevelFree

theorem ne_under_of_offS {D : D7} {SF : Finset (HeightOneSpectrum (𝓞 D.host.F))} {Q : HeightOneSpectrum (𝓞 D.host.E)}
    (hQ : OffS D SF Q) {v : HeightOneSpectrum (𝓞 D.host.F)} (hv : v ∈ SF) :
    v ≠ HeightOneSpectrum.under (𝓞 D.host.F) Q := by
  intro hvq
  obtain ⟨x, hx, hy⟩ := hQ v hv
  have hx' : x ∈ (HeightOneSpectrum.under (𝓞 D.host.F) Q).asIdeal := hvq ▸ hx
  have hmem : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x ∈ Q.asIdeal := hx'
  refine hy (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x) ?_ hmem
  rfl

theorem rTup_eq_one {D : D7} {V : HSp D} (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    {SF : Finset (HeightOneSpectrum (𝓞 D.host.F))}
    (hPg : ∀ PP ∈ L.Pg, ∃ v ∈ SF, PP.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = v.asIdeal)
    {Q : HeightOneSpectrum (𝓞 D.host.E)} (hQ : OffS D SF Q) {e f : AE D} (hef : IsPrimeIdem Q e f)
    {g : GA D V} (hg : SuppF V f g) (hS : finE V g ∈ St β) : rTup β L (finE V g) = 1 := by
  have hproj : ∀ v ∈ SF, GlobalTheory.FinZeta.projV V v g = 1 := fun v hv =>
    (GlobalTheory.SuppLocal.suppF_local D V Q e f g hef hg).2 v (ne_under_of_offS hQ hv)
  funext PP
  obtain ⟨v, hv, hPv⟩ := hPg PP.1 PP.2
  have hu : HeightOneSpectrum.under (𝓞 D.host.F) PP.1 ∈ SF := by
    have : HeightOneSpectrum.under (𝓞 D.host.F) PP.1 = v := HeightOneSpectrum.ext hPv
    rw [this]; exact hv
  have hr := GlobalTheory.FinZeta.LevelOff.redFn_eq_one_of_proj β SF hS hproj hu
  show upperLeftBlock L.hr (redFn β PP.1 (finE V g)) = 1
  rw [hr]; exact blockDiagonalExtendByOnePrimeField_one _ _

theorem mem_and_chi {D : D7} {V : HSp D} (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (P P' : LevelP L.Pg L.r ℂ) {SF : Finset (HeightOneSpectrum (𝓞 D.host.F))}
    (hPg : ∀ PP ∈ L.Pg, ∃ v ∈ SF, PP.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = v.asIdeal)
    {Q : HeightOneSpectrum (𝓞 D.host.E)} (hQ : OffS D SF Q) {e f : AE D} (hef : IsPrimeIdem Q e f)
    {g : GA D V} (hg : SuppF V f g) (hJ : g ∈ levS V β (withP L P)) :
    g ∈ levS V β (withP L P') ∧ levChi V β (withP L P) g = levChi V β (withP L P') g := by
  obtain ⟨hG, hl⟩ := hJ
  have hpar : finE V g ∈ parLev D.sp.cm V.gram β (withP L P) := (mem_lev.1 hl).1
  have hS : finE V g ∈ St β := parLev_St hpar
  have h1 : rTup β L (finE V g) = 1 := rTup_eq_one β L hPg hQ hef hg hS
  refine ⟨⟨hG, mem_lev.2 ⟨hpar, ?_⟩⟩, ?_⟩
  · show rTup β L (finE V g) ∈ P'.H
    rw [h1]; exact Subgroup.one_mem _
  · unfold levChi
    rw [levFn_withP, levFn_withP, h1, blockDiagonalExtendByOnePrimeField_one, blockDiagonalExtendByOnePrimeField_one]

theorem isHeckeOpFull_imp {D : D7} {V : HSp D} (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (P P' : LevelP L.Pg L.r ℂ) (SF : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (hPg : ∀ PP ∈ L.Pg, ∃ v ∈ SF, PP.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = v.asIdeal)
    (Q : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ) (Rp : Finset (GA D V)) :
    Hecke₂ V (levS V β (withP L P)) (levChi V β (withP L P)) SF Q d Rp →
      Hecke₂ V (levS V β (withP L P')) (levChi V β (withP L P')) SF Q d Rp := by
  rintro ⟨e, f, ϖ, α, hQ, hef, h1, h2, h3, hK, hχ, h4, h5, h6, hR⟩
  have key := fun g (hg : SuppF V f g) (hJ : g ∈ levS V β (withP L P)) => mem_and_chi β L P P' hPg hQ hef hg hJ
  have key' := fun g (hg : SuppF V f g) (hJ : g ∈ levS V β (withP L P')) => mem_and_chi β L P' P hPg hQ hef hg hJ
  have hset : {k | k ∈ levS V β (withP L P) ∧ SuppF V f k} = {k | k ∈ levS V β (withP L P') ∧ SuppF V f k} := by
    ext k
    exact ⟨fun ⟨a, b⟩ => ⟨(key k b a).1, b⟩, fun ⟨a, b⟩ => ⟨(key' k b a).1, b⟩⟩
  refine ⟨e, f, ϖ, α, hQ, hef, h1, h2, h3, fun g hg => ?_, fun g hJ hg => ?_, h4, h5, h6, hset ▸ hR⟩
  · exact ⟨fun h => (hK g hg).1 ((key' g hg h).1), fun h => (key g hg ((hK g hg).2 h)).1⟩
  · have hJ0 := (key' g hg hJ).1
    rw [← (key g hg hJ0).2]
    exact hχ g hJ0 hg

theorem isHeckeOpFull_withP_iff : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (P P' : LevelP L.Pg L.r ℂ) (SF : Finset (HeightOneSpectrum (𝓞 D.host.F))), (∀ PP ∈ L.Pg, ∃ v ∈ SF, PP.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = v.asIdeal) → ∀ (Q : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ) (Rp : Finset (GA D V)), Hecke₂ V (levS V β (withP L P)) (levChi V β (withP L P)) SF Q d Rp ↔ Hecke₂ V (levS V β (withP L P')) (levChi V β (withP L P')) SF Q d Rp := by
  intro D V β L P P' SF hPg Q d Rp
  exact ⟨isHeckeOpFull_imp β L P P' SF hPg Q d Rp, isHeckeOpFull_imp β L P' P SF hPg Q d Rp⟩

end GlobalTheory.HeckeLevelFree
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsHeckeOpFullIffIndependentOfBlockLevelStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isHeckeOpFull_iff_independent_of_blockLevel : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (P P' : LevelP L.Pg L.r ℂ) (SF : Finset (HeightOneSpectrum (𝓞 D.host.F))), (∀ PP ∈ L.Pg, ∃ v ∈ SF, PP.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = v.asIdeal) → ∀ (Q : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ) (Rp : Finset (GA D V)), Hecke₂ V (levS V β (withP L P)) (levChi V β (withP L P)) SF Q d Rp ↔ Hecke₂ V (levS V β (withP L P')) (levChi V β (withP L P')) SF Q d Rp := by
  first | exact @GlobalTheory.HeckeLevelFree.isHeckeOpFull_withP_iff | exact GlobalTheory.HeckeLevelFree.isHeckeOpFull_withP_iff | (intros; apply GlobalTheory.HeckeLevelFree.isHeckeOpFull_withP_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransferEigensystemPartsThreeLevelsOfMultEq
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open Formalism.IndefR.Lev
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn
open GlobalTheory.Hk3 (Core IsSF SchurAll EEc Wcc)

namespace GlobalTheory.TrLevMult

theorem level_eq_trivial {E : Type} [Field E] [NumberField E] {Pg : Finset (Pl E)} {r : ℕ} {LL : Type} [CommRing LL]
    (L : LevelP Pg r LL) (h : L.H = ⊥) : L = LevelP.triv Pg r LL := by
  obtain ⟨H, chi⟩ := L
  simp only at h
  subst h
  unfold LevelP.triv
  congr 1
  ext x
  have hx : x = 1 := Subtype.ext (Subgroup.mem_bot.mp x.2)
  subst hx
  simp

theorem levPOf_bot_eq {D : D7} {G K : Type} [Group G] [Field K] {Pg : Finset (Pl D.host.E)} {r : ℕ} (eG : G ≃* G0 Pg r)
    (σ : K →+* ℂ) (ψ : (⊥ : Subgroup G) →* Kˣ) : levPOf eG σ ⊥ ψ = LevelP.triv Pg r ℂ := by
  apply level_eq_trivial
  show Subgroup.comap eG.symm.toMonoidHom ⊥ = ⊥
  ext x
  simp

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}

theorem pg_over {SF : Finset (HeightOneSpectrum (𝓞 D.host.F))} (hSF : IsSF R SF) : ∀ PP ∈ R.Pg, ∃ v ∈ SF,
    PP.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = v.asIdeal :=
  fun PP hPP => ⟨Formalism.IndefR.Fin.belowPl PP, (hSF _).2 ⟨PP, hPP, rfl⟩, rfl⟩

theorem trAt_of_dim (hC : Core R F) {SF} (hSF : IsSF R SF) (i : Fin D.R.m) (Pe Pw : LevelP R.Pg D.R.r ℂ)
    (hdim : ∀ c, Module.finrank ℂ (Wcc R SF i c ⊓ (R.Wat i (sg0 D A) Pw).comap (R.HW i _).e : Submodule ℂ _) =
      Module.finrank ℂ (EEc R SF c ⊓ (R.EEat Pe).comap R.HE.e : Submodule ℂ _)) :
    GlobalTheory.TrCopy.TRAt R SF i Pe Pw := by
  intro c
  have hE : R.EEat Pe ≤ R.EEat R.triv := GlobalTheory.PartDims.goodPart_le_flag (L := R.dat0 R.triv) R.θ _ rfl rfl _ _
  have hW : R.Wat i (sg0 D A) Pw ≤ R.Wat i (sg0 D A) R.triv :=
    GlobalTheory.PartDims.goodPart_le_flag (L := R.datWp i R.triv) R.θ _ rfl rfl _ _
  have kE : ∀ Q d B, Hecke₂ (Yc D 0) (levS _ (R.βY 0) (R.dat0 Pe)) (levChi _ (R.βY 0) (R.dat0 Pe)) SF Q d B ↔
      Hecke₂ (Yc D 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) SF Q d B :=
    GlobalTheory.T.isHeckeOpFull_iff_independent_of_blockLevel D (Yc D 0) (R.βY 0) (R.dat0 R.triv) Pe R.triv SF (pg_over hSF)
  have kW : ∀ Q d B, Hecke₂ (Wc D i) (levS _ (R.βW i) (R.datWp i Pw)) (levChi _ (R.βW i) (R.datWp i Pw)) SF Q d B ↔
      Hecke₂ (Wc D i) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) SF Q d B :=
    GlobalTheory.T.isHeckeOpFull_iff_independent_of_blockLevel D (Wc D i) (R.βW i) (R.datWp i R.triv) Pw R.triv SF (pg_over hSF)
  have eqE : GlobalTheory.TrCopy.partE R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 Pe)) (levChi _ (R.βY 0) (R.dat0 Pe)) R.e0 SF c =
      R.EEat Pe ⊓ partFull R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) SF
        (fun Q d => c Q (dualLab d)) := by
    ext x
    show (x ∈ partFull R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 Pe)) (levChi _ (R.βY 0) (R.dat0 Pe)) SF
        (fun Q d => c Q (dualLab d)) ∧ x ∈ R.EEat Pe) ↔ (x ∈ R.EEat Pe ∧ x ∈ partFull R.θ (R.MY 0)
        (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) SF (fun Q d => c Q (dualLab d)))
    simp only [partFull, Submodule.mem_inf, Submodule.mem_iInf]
    constructor
    · rintro ⟨⟨-, h1⟩, h2⟩
      exact ⟨h2, (hE h2).1, fun Q d B hB => h1 Q d B ((kE Q d B).2 hB)⟩
    · rintro ⟨h2, -, h1⟩
      exact ⟨⟨h2.1, fun Q d B hB => h1 Q d B ((kE Q d B).1 hB)⟩, h2⟩
  have eqW : GlobalTheory.TrCopy.partW R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i Pw)) (levChi _ (R.βW i) (R.datWp i Pw))
        (R.eWf i (sg0 D A)) SF c =
      R.Wat i (sg0 D A) Pw ⊓ partFull R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv))
        (levChi _ (R.βW i) (R.datWp i R.triv)) SF c := by
    ext x
    show (x ∈ partFull R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i Pw)) (levChi _ (R.βW i) (R.datWp i Pw)) SF c ∧
        x ∈ R.Wat i (sg0 D A) Pw) ↔ (x ∈ R.Wat i (sg0 D A) Pw ∧ x ∈ partFull R.θ (R.MW i (sg0 D A))
        (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) SF c)
    simp only [partFull, Submodule.mem_inf, Submodule.mem_iInf]
    constructor
    · rintro ⟨⟨-, h1⟩, h2⟩
      exact ⟨h2, (hW h2).1, fun Q d B hB => h1 Q d B ((kW Q d B).2 hB)⟩
    · rintro ⟨h2, -, h1⟩
      exact ⟨⟨h2.1, fun Q d B hB => h1 Q d B ((kW Q d B).1 hB)⟩, h2⟩
  have fE := GlobalTheory.PartDims.finrank_comap hC.models.HE (U := R.EEat Pe ⊓ partFull R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv))
    (levChi _ (R.βY 0) (R.dat0 R.triv)) SF (fun Q d => c Q (dualLab d))) (inf_le_left.trans hE)
  have fW := GlobalTheory.PartDims.finrank_comap (hC.models.HW i (sg0 D A)) (U := R.Wat i (sg0 D A) Pw ⊓
    partFull R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) SF c)
    (inf_le_left.trans (hW.trans inf_le_left))
  have cE : (R.EEat Pe ⊓ partFull R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv))
      (levChi _ (R.βY 0) (R.dat0 R.triv)) SF (fun Q d => c Q (dualLab d))).comap R.HE.e =
      EEc R SF c ⊓ (R.EEat Pe).comap R.HE.e := by
    ext x
    exact ⟨fun hx => ⟨hx.2, hx.1⟩, fun hx => ⟨hx.2, hx.1⟩⟩
  have cW : (R.Wat i (sg0 D A) Pw ⊓ partFull R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv))
      (levChi _ (R.βW i) (R.datWp i R.triv)) SF c).comap (R.HW i _).e =
      Wcc R SF i c ⊓ (R.Wat i (sg0 D A) Pw).comap (R.HW i _).e := by
    ext x
    exact ⟨fun hx => ⟨⟨hW hx.1, hx.2⟩, hx.1⟩, fun hx => ⟨hx.2, hx.1.2⟩⟩
  haveI := fE.2
  haveI := fW.2
  show Module.rank ℂ (GlobalTheory.TrCopy.partE R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 Pe)) (levChi _ (R.βY 0) (R.dat0 Pe)) R.e0 SF c) =
    Module.rank ℂ (GlobalTheory.TrCopy.partW R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i Pw)) (levChi _ (R.βW i) (R.datWp i Pw))
        (R.eWf i (sg0 D A)) SF c)
  rw [eqE, eqW, ← Module.finrank_eq_rank, ← Module.finrank_eq_rank, ← fE.1, ← fW.1, cE, cW, hdim c]

end GlobalTheory.TrLevMult


open GlobalTheory.TrLevMult in
theorem GlobalTheory.TrLevMult.trLev_of_multEq : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), ∀ s : ℕ, A.fam.Ok s → GlobalTheory.Hk3.Core R F → GlobalTheory.Hk3.SchurAll R → GoodStable A.X → GlobalTheory.CuspMult.CuspDecomp D → GlobalTheory.CuspMult.MultEq R → ∀ SF, GlobalTheory.Hk3.IsSF R SF → GlobalTheory.TrCopy.TRLev R F SF := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F s hs hC hS hX hD hM SF hSF
  have key : ∀ i (P : Subgroup G) (ψ : P →* D.what₂.LLˣ),
      GlobalTheory.TrCopy.TRAt R SF i (levPOf R.eG D.what₂.embLL P ψ) (levPOf R.eG (sg0 D A) P ψ⁻¹) :=
    fun i P ψ => trAt_of_dim hC hSF i _ _ (fun c => GlobalTheory.DimFull.dim_parts_full R F hs hC hS hX hD hM SF hSF P ψ i c)
  intro i
  refine ⟨?_, fun b => key i _ _⟩
  have h := key i ⊥ 1
  rwa [inv_one, levPOf_bot_eq, levPOf_bot_eq] at h

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransferEigensystemPartsThreeLevelsOfMultEqStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transfer_eigensystem_parts_three_levels_of_mult_eq : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), ∀ s : ℕ, A.fam.Ok s → GlobalTheory.Hk3.Core R F → GlobalTheory.Hk3.SchurAll R → GoodStable A.X → GlobalTheory.CuspMult.CuspDecomp D → GlobalTheory.CuspMult.MultEq R → ∀ SF, GlobalTheory.Hk3.IsSF R SF → GlobalTheory.TrCopy.TRLev R F SF := by
  first | exact @GlobalTheory.TrLevMult.trLev_of_multEq | exact GlobalTheory.TrLevMult.trLev_of_multEq | (intros; apply GlobalTheory.TrLevMult.trLev_of_multEq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromColsMemLatDbl
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.DblVacEigen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def latDbl {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (v : Pl (F := F)) : AddSubgroup (Matrix (Fin n) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) where
  carrier := {z | z.toCols₁ ∈ latAtV X W v ∧ z.toCols₂ ∈ latAtV X W v}
  add_mem' := fun {a b} ha hb => ⟨add_mem ha.1 hb.1, add_mem ha.2 hb.2⟩
  zero_mem' := ⟨zero_mem (latAtV X W v), zero_mem (latAtV X W v)⟩
  neg_mem' := fun {a} ha => ⟨neg_mem ha.1, neg_mem ha.2⟩

theorem mem_latDbl {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (v : Pl (F := F)) (z : Matrix (Fin n) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :
    z ∈ latDbl X W v ↔ z.toCols₁ ∈ latAtV X W v ∧ z.toCols₂ ∈ latAtV X W v := Iff.rfl

theorem fromCols_mem_latDbl {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (v : Pl (F := F)) {γ₁ γ₂ : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))}
    (h₁ : γ₁ ∈ latAtV X W v) (h₂ : γ₂ ∈ latAtV X W v) : Matrix.fromCols γ₁ γ₂ ∈ latDbl X W v := by
  rw [mem_latDbl, Matrix.toCols₁_fromCols, Matrix.toCols₂_fromCols]
  exact ⟨h₁, h₂⟩

theorem at_of_mem_latDbl {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (v : Pl (F := F)) {z : Matrix (Fin n) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))}
    (hz : z ∈ latDbl X W v) : At (evFin F v) z := by
  intro u hu
  have h1 := (GlobalTheory.LatVac.latAtV_at_stable X W v).1 _ hz.1 u hu
  have h2 := (GlobalTheory.LatVac.latAtV_at_stable X W v).1 _ hz.2 u hu
  ext i (j | j)
  · simpa using congrFun (congrFun h1 i) j
  · simpa using congrFun (congrFun h2 i) j

end GlobalTheory.DblVacEigen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticIsotropicPlaneVanishesAdelic
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.MixedLagr
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.MixedLagr

theorem hTens_vecMulVec {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A)
    {α β : Type} [Fintype α] [Fintype β] (JA : Matrix α α A) (JB : Matrix β β A) (a a' : α → A) (x x' : β → A) :
    hTens c JA JB (Matrix.vecMulVec a x) (Matrix.vecMulVec a' x') =
      (∑ i, ∑ k, a i * JA i k * c (a' k)) * ∑ j, ∑ l, x j * JB j l * c (x' l) := by
  simp only [hTens, Matrix.vecMulVec_apply, map_mul]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem symplectic_isotropic_plane_vanishes (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n d d₁ : ℕ) (JX : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin d) (Fin d) E) (H' : Plane E d d₁) :
    form σ JW H'.x H'.x = 0 → ∀ u ∈ (iso0 n H' : Set (Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))),
      ∀ u' ∈ (iso0 n H' : Set (Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))), symp (cA σ) (-1) (incM F JX) (incM F JW) u u' = 0 := by
  rintro h0 u ⟨a, rfl⟩ u' ⟨a', rfl⟩
  have hc : ∀ x : E, cA σ (inclR (F := F) (AF F) x) = inclR (F := F) (AF F) (σ x) := fun x => rfl
  have h : ∑ j, ∑ l, incV F H'.x j * incM F JW j l * cA σ (incV F H'.x l) = 0 := by
    have h1 := congrArg (inclR (F := F) (AF F)) h0
    rw [map_zero] at h1
    rw [← h1]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [form, incV, incM, Matrix.map_apply, hc, dotProduct, Matrix.mulVec, Finset.mul_sum, map_sum, map_mul, mul_assoc]
  rw [symp, hTens_vecMulVec, h, mul_zero, mul_zero, map_zero]

end GlobalTheory.MixedLagr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalDarbouxCoordinatesTensorHermitian
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalDarbouxCoordinatesTensorHermitian
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem GlobalTheory.RatDarboux.exists_rational_darboux_of_isGood : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : Base F E), B.IsGood σ → ∀ {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (r s r' s' : ℕ),
    X.IsHerm σ B r s → Y.IsSkew σ B r' s' → ∃ co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J)) (Fin n × Fin d), ∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F, co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F x) = (fun k => algebraMap F (AF F) (y k), fun k => algebraMap F (AF F) (z k)) :=
  fun B hB _ _ X Y r s r' s' hX hY => GlobalTheory.RatDarboux.exists_rational_darboux _ B X Y r s r' s' hB hX hY
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalDarbouxCoordinatesTensorHermitianStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_darboux_coordinates_tensor_hermitian : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : Base F E), B.IsGood σ → ∀ {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (r s r' s' : ℕ),
    X.IsHerm σ B r s → Y.IsSkew σ B r' s' → ∃ co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J)) (Fin n × Fin d), ∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F, co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F x) = (fun k => algebraMap F (AF F) (y k), fun k => algebraMap F (AF F) (z k)) := by
  first | exact @GlobalTheory.RatDarboux.exists_rational_darboux_of_isGood | exact GlobalTheory.RatDarboux.exists_rational_darboux_of_isGood | (intros; apply GlobalTheory.RatDarboux.exists_rational_darboux_of_isGood <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalInvTranspose
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.JHMult

namespace GlobalTheory.InvTransposeCusp

theorem invTranspose_invol {R : Type} [CommRing R] (n : ℕ) (g : GL (Fin n) R) :
    GlobalTheory.TypeTame.invTranspose n (GlobalTheory.TypeTame.invTranspose n g) = g := by
  apply Units.ext
  exact Matrix.transpose_transpose (g : Matrix (Fin n) (Fin n) R)

theorem isSupercuspidal_comp_invTranspose (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V) (hs : IsSupercuspidal π) :
    IsSupercuspidal (π.comp (GlobalTheory.TypeTame.invTranspose n)) := by
  have hcont := GlobalTheory.TypeTame.continuous_invTranspose (R := k) n
  obtain ⟨hsm, hc⟩ := hs
  refine ⟨fun v => (hsm v).preimage hcont, ?_⟩
  intro v l hl
  have hl' : l ∈ smoothPart π.dual := by
    show IsOpen {g | π.dual g l = l}
    have : {g | π.dual g l = l} = (GlobalTheory.TypeTame.invTranspose n) ⁻¹'
        {g | Representation.dual (π.comp (GlobalTheory.TypeTame.invTranspose n)) g l = l} := by
      ext g
      simp [Representation.dual, map_inv, invTranspose_invol]
    rw [this]
    exact hl.preimage hcont
  obtain ⟨C, hC, hCl⟩ := hc v l hl'
  refine ⟨(GlobalTheory.TypeTame.invTranspose n) '' C, hC.image hcont, fun g hg => ?_⟩
  obtain ⟨z, hz, c, hcC, hgc⟩ := hCl (GlobalTheory.TypeTame.invTranspose n g) hg
  refine ⟨GlobalTheory.TypeTame.invTranspose n z, ?_, GlobalTheory.TypeTame.invTranspose n c, ⟨c, hcC, rfl⟩, ?_⟩
  · rw [Subgroup.mem_center_iff]
    intro h
    have := Subgroup.mem_center_iff.1 hz (GlobalTheory.TypeTame.invTranspose n h)
    have h2 := congrArg (GlobalTheory.TypeTame.invTranspose n) this
    simpa [map_mul, invTranspose_invol] using h2
  · rw [← map_mul, ← hgc, invTranspose_invol]

theorem isCuspidal_comp_invTranspose : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsCuspidal π → IsCuspidal (π.comp (GlobalTheory.TypeTame.invTranspose n)) := by
  intro k _ _ _ _ n V _ _ π h
  exact GlobalTheory.SuperCusp.isCuspidal_of_isSupercuspidal k n V _
    (isSupercuspidal_comp_invTranspose k n V π
      (GlobalTheory.CuspCoef.isSupercuspidal_of_isCuspidal k n V π h))

end GlobalTheory.InvTransposeCusp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActsRhoOfAtInf
open scoped SchwartzMap Matrix TensorProduct Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ArchUniq

namespace GlobalTheory.ArchUniq

noncomputable def evIHom (F : Type) [Field F] [NumberField F] : AF F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp
    (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))

theorem evI_eq_evIHom {F : Type} [Field F] [NumberField F] (a : AF F) : evI F a = evIHom F a := rfl

theorem trace_evI_heis {F : Type} [Field F] [NumberField F] [Invertible (2 : AF F)] {κ : Type} [Fintype κ]
    (x a b : κ → AF F) :
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (x ⬝ᵥ b + ⅟(2 : AF F) * a ⬝ᵥ b)) =
      trP F κ (locV x) (locV b) + trP F κ (locV a) (locV b) / 2 := by
  have hdot : ∀ y : κ → AF F, evIHom F (y ⬝ᵥ b) = ∑ i, locV y i * locV b i := by
    intro y
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [dotProduct, map_sum, map_mul, locV, evI_eq_evIHom]
  have h2 : ∀ t : AF F, evIHom F (⅟(2 : AF F) * t) = (1 / 2 : ℝ) • evIHom F t := by
    intro t
    have h : (2 : ℝ) • evIHom F (⅟(2 : AF F) * t) = evIHom F t := by
      rw [two_smul, ← map_add (f := _), ← two_mul, ← mul_assoc, mul_invOf_self, one_mul]
    rw [← h, smul_smul]
    norm_num
  rw [evI_eq_evIHom, map_add (f := _), h2, hdot, hdot, map_add (f := _), map_smul, trP, trP, smul_eq_mul]
  ring

theorem acts_rho_of_at_inf : ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ {W' : Type} [AddCommGroup W'] [Module (AF F) W'] {Bf : W' → W' → AF F} {κ : Type} [Fintype κ]
      (dc : Darboux Bf κ) (w : W'), At (evI F) w → ∀ f f₁ : SInf F κ,
      ⇑f₁ = schrF (trP F κ) (locV (dc.e w).1, locV (dc.e w).2) ⇑f → Acts (evI F) (dc.rho ψ w) ⇑f ⇑f₁ := by
  intro F _ _ ψ hψ W' _ _ Bf κ _ dc w hw f f₁ hf r hr
  have hab : ∀ u : AF F, evI F u = 0 → u • dc.e w = 0 := fun u hu => by
    rw [← map_smul, hw u hu, map_zero]
  have ha : At (evI F) (dc.e w).1 := fun u hu => congrArg Prod.fst (hab u hu)
  have hb : At (evI F) (dc.e w).2 := fun u hu => congrArg Prod.snd (hab u hu)
  funext x
  have ht : At (evI F) (x ⬝ᵥ (dc.e w).2 + ⅟(2 : AF F) * (dc.e w).1 ⬝ᵥ (dc.e w).2) := fun u hu => by
    have h : ∀ y : κ → AF F, u * (y ⬝ᵥ (dc.e w).2) = 0 := fun y => by
      rw [← smul_eq_mul, ← dotProduct_smul, hb u hu, dotProduct_zero]
    rw [smul_eq_mul, mul_add, h, mul_left_comm, h, mul_zero, add_zero]
  have hloc : (fun i => evI F ((x + (dc.e w).1) i)) = locV x + locV (dc.e w).1 := by
    funext i
    simp only [Pi.add_apply, locV, evI_eq_evIHom, map_add (f := _)]
  simp only [Darboux.rho, schr, tens]
  rw [hψ.2.2 _ ht, trace_evI_heis, hr.1 x _ ha, hf, hloc, schrF]
  exact (mul_assoc _ _ _).symm

end GlobalTheory.ArchUniq
end
