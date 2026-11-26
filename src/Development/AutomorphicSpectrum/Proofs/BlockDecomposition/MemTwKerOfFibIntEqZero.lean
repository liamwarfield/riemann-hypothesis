module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqZeroOfEigOfMemTwKer
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasModelOfSpreading
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreFunctionUnipotentAction

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteJacquetKernelCommonLattice
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteJacquetKernelCommonLattice
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

noncomputable section

open ValuativeRel

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibKer

section Exhaust

variable {k : Type} [Field k] [ValuativeRel k]

theorem Lc_le_Lc_mul (n : ℕ) (c : k) {d : k} (hd : d ∈ 𝒪[k]) : Lc n c ≤ Lc n (c * d) := by
  intro y hy j
  have h : c * d * y.toAdd j = d * (c * y.toAdd j) := by ring
  rw [h]
  exact mul_mem hd (hy j)

theorem exists_integral_mul (y : k) : ∃ c : k, c ∈ 𝒪[k] ∧ c ≠ 0 ∧ c * y ∈ 𝒪[k] := by
  by_cases hy : y ∈ 𝒪[k]
  · exact ⟨1, one_mem _, one_ne_zero, by rwa [one_mul]⟩
  · have hy0 : y ≠ 0 := fun h => hy (h ▸ zero_mem _)
    refine ⟨y⁻¹, ?_, inv_ne_zero hy0, ?_⟩
    · rw [Valuation.mem_integer_iff] at hy ⊢
      rw [map_inv₀]
      exact inv_le_one_of_one_le₀ (le_of_lt (not_le.1 hy))
    · rw [inv_mul_cancel₀ hy0]
      exact one_mem _

theorem exists_mem_Lc (n : ℕ) (y : Multiplicative (Fin n → k)) :
    ∃ c : k, c ∈ 𝒪[k] ∧ c ≠ 0 ∧ y ∈ Lc n c := by
  choose f hf hf0 hfy using fun j => exists_integral_mul (y.toAdd j)
  refine ⟨∏ j, f j, prod_mem fun j _ => hf j, Finset.prod_ne_zero_iff.2 fun j _ => hf0 j, ?_⟩
  intro j
  have h : (∏ i, f i) * y.toAdd j = (∏ i ∈ Finset.univ.erase j, f i) * (f j * y.toAdd j) := by
    rw [← Finset.prod_erase_mul Finset.univ f (Finset.mem_univ j)]
    ring
  rw [h]
  exact mul_mem (prod_mem fun i _ => hf i) (hfy j)

variable {X : Type} [AddCommGroup X] [Module ℂ X]

theorem twKer_Lc_mono {n : ℕ} (ρ : Representation ℂ (Multiplicative (Fin n → k)) X) (c : k) {d : k}
    (hd : d ∈ 𝒪[k]) : twKer ρ (Lc n c) 1 ≤ twKer ρ (Lc n (c * d)) 1 := by
  refine Submodule.span_mono ?_
  rintro w ⟨m, v, rfl⟩
  exact ⟨⟨m.1, Lc_le_Lc_mul n c hd m.2⟩, v, rfl⟩

theorem exists_mem_twKer_Lc {n : ℕ} (ρ : Representation ℂ (Multiplicative (Fin n → k)) X) {x : X}
    (hx : x ∈ twKer ρ ⊤ 1) : ∃ c : k, c ∈ 𝒪[k] ∧ c ≠ 0 ∧ x ∈ twKer ρ (Lc n c) 1 := by
  induction hx using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨m, v, rfl⟩ := hw
    obtain ⟨c, hc, hc0, hm⟩ := exists_mem_Lc n m.1
    exact ⟨c, hc, hc0, Submodule.subset_span ⟨⟨m.1, hm⟩, v, rfl⟩⟩
  | zero => exact ⟨1, one_mem _, one_ne_zero, zero_mem _⟩
  | add a b _ _ ha hb =>
    obtain ⟨c, hc, hc0, hca⟩ := ha
    obtain ⟨d, hd, hd0, hdb⟩ := hb
    refine ⟨c * d, mul_mem hc hd, mul_ne_zero hc0 hd0, add_mem (twKer_Lc_mono ρ c hd hca) ?_⟩
    rw [mul_comm c d]
    exact twKer_Lc_mono ρ d hc hdb
  | smul a b _ hb =>
    obtain ⟨c, hc, hc0, hcb⟩ := hb
    exact ⟨c, hc, hc0, Submodule.smul_mem _ a hcb⟩

theorem exists_integral_finite_twKer_Lc {n : ℕ} (ρ : Representation ℂ (Multiplicative (Fin n → k)) X)
    {S : Set X} (hS : S.Finite) (h : ∀ x ∈ S, x ∈ twKer ρ ⊤ 1) :
    ∃ c : k, c ∈ 𝒪[k] ∧ c ≠ 0 ∧ ∀ x ∈ S, x ∈ twKer ρ (Lc n c) 1 := by
  induction S, hS using Set.Finite.induction_on with
  | empty => exact ⟨1, one_mem _, one_ne_zero, fun x hx => absurd hx (Set.notMem_empty x)⟩
  | @insert a s _ _ ih =>
    obtain ⟨c, hc, hc0, hcs⟩ := ih fun x hx => h x (Set.mem_insert_of_mem a hx)
    obtain ⟨d, hd, hd0, hda⟩ := exists_mem_twKer_Lc ρ (h a (Set.mem_insert a s))
    refine ⟨c * d, mul_mem hc hd, mul_ne_zero hc0 hd0, ?_⟩
    rintro x (rfl | hx)
    · rw [mul_comm c d]
      exact twKer_Lc_mono ρ d hc hda
    · exact twKer_Lc_mono ρ c hd (hcs x hx)

end Exhaust

theorem exists_Lc_finite_twKer :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) {X : Type} [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (Multiplicative (Fin n → k)) X) (S : Set X), S.Finite → (∀ x ∈ S, x ∈ twKer ρ ⊤ 1) → ∃ c : k, c ≠ 0 ∧ ∀ x ∈ S, x ∈ twKer ρ (Lc n c) 1 := by
  intro k _ _ _ _ n X _ _ ρ S hS h
  obtain ⟨c, -, hc0, hc⟩ := exists_integral_finite_twKer_Lc ρ hS h
  exact ⟨c, hc0, hc⟩

end GlobalTheory.CompanionTheory.BZPsiPG.FibKer
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteJacquetKernelCommonLatticeStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_jacquet_kernel_common_lattice : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) {X : Type} [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (Multiplicative (Fin n → k)) X) (S : Set X), S.Finite → (∀ x ∈ S, x ∈ twKer ρ ⊤ 1) → ∃ c : k, c ≠ 0 ∧ ∀ x ∈ S, x ∈ twKer ρ (Lc n c) 1 := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.FibKer.exists_Lc_finite_twKer | exact GlobalTheory.CompanionTheory.BZPsiPG.FibKer.exists_Lc_finite_twKer | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.FibKer.exists_Lc_finite_twKer <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothFibreAction
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothFibreAction
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibKer.SmFib

open Topology

theorem range_finite {X W : Type} [TopologicalSpace X] [AddCommGroup W] {φ : X → W}
    (hl : IsLocallyConstant φ) (hc : HasCompactSupport φ) : (Set.range φ).Finite := by
  have : CompactSpace (tsupport φ) := isCompact_iff_compactSpace.mp hc
  have h1 : (Set.range (φ ∘ ((↑) : tsupport φ → X))).Finite :=
    (hl.comp_continuous continuous_subtype_val).range_finite
  refine (h1.insert 0).subset ?_
  rintro _ ⟨x, rfl⟩
  by_cases hx : x ∈ tsupport φ
  · exact Or.inr ⟨⟨x, hx⟩, rfl⟩
  · exact Or.inl (image_eq_zero_of_notMem_tsupport hx)

theorem exists_nhds_translation_invariant {A Z : Type} [AddCommGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] [AddCommGroup Z] {φ : A → Z} (hl : IsLocallyConstant φ)
    (hc : HasCompactSupport φ) : ∃ N ∈ 𝓝 (0 : A), ∀ w ∈ N, ∀ v, φ (v + w) = φ v := by
  letI := IsTopologicalAddGroup.rightUniformSpace A
  haveI := isUniformAddGroup_of_addCommGroup (G := A)
  letI : UniformSpace Z := ⊥
  haveI : DiscreteTopology Z := ⟨rfl⟩
  have hu : UniformContinuous φ := hc.uniformContinuous_of_continuous hl.continuous
  have hid : {p : Z × Z | p.1 = p.2} ∈ _root_.uniformity Z := by
    have : _root_.uniformity Z = Filter.principal {p : Z × Z | p.1 = p.2} := rfl
    rw [this]
    exact Filter.mem_principal_self _
  have h1 := hu hid
  rw [Filter.mem_map, uniformity_eq_comap_nhds_zero A, Filter.mem_comap] at h1
  obtain ⟨N, hN, hsub⟩ := h1
  refine ⟨N, hN, fun w hw v => ?_⟩
  have h2 : (v, v + w) ∈ (fun x : A × A => x.2 - x.1) ⁻¹' N := by
    show v + w - v ∈ N
    simpa using hw
  exact (hsub h2).symm

theorem isOpen_stabiliser {G V : Type} [Group G] [TopologicalSpace G] [ContinuousMul G] [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ G V) (v : V) (h : {g | ρ g v = v} ∈ 𝓝 (1 : G)) :
    IsOpen {g | ρ g v = v} :=
  _root_.UpperTheory.Reformulated.B.Yhd4.main ρ v h

theorem isSmooth_fibAct (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (i t : ℕ) {Z : Type} [AddCommGroup Z] [Module ℂ Z]
    (ρ₀ : Representation ℂ (Multiplicative (Fin i → k)) Z) (hρ : IsSmooth ρ₀) :
    IsSmooth (fibAct t ρ₀) := by
  intro φ
  refine isOpen_stabiliser (fibAct t ρ₀) φ ?_
  have hU : (⋂ z ∈ Set.range φ.1, {g : Multiplicative (Fin i → k) | ρ₀ g z = z}) ∈ 𝓝 1 :=
    (Filter.biInter_mem (range_finite φ.2.1 φ.2.2)).2 fun z _ =>
      (hρ z).mem_nhds (show ρ₀ 1 z = z by rw [map_one, Module.End.one_apply])
  obtain ⟨N, hN, hinv⟩ := exists_nhds_translation_invariant φ.2.1 φ.2.2
  have hT : Continuous fun y : Multiplicative (Fin (i + t) → k) =>
      Multiplicative.ofAdd (topP i t y.toAdd) :=
    continuous_ofAdd.comp ((continuous_topP i t).comp continuous_toAdd)
  have hM : Continuous fun y : Multiplicative (Fin (i + t) → k) => middlePart i t y.toAdd :=
    (continuous_midP i t).comp continuous_toAdd
  have h1 := hT.continuousAt (x := 1) |>.preimage_mem_nhds (t := _) hU
  have h2 := hM.continuousAt (x := 1) |>.preimage_mem_nhds (t := _) hN
  refine Filter.mem_of_superset (Filter.inter_mem h1 h2) ?_
  rintro y ⟨hy1, hy2⟩
  apply Subtype.ext
  funext v
  show ρ₀ (Multiplicative.ofAdd (topP i t y.toAdd)) (φ.1 (v + middlePart i t y.toAdd)) = φ.1 v
  rw [hinv _ hy2 v]
  exact Set.mem_iInter₂.1 hy1 (φ.1 v) ⟨v, rfl⟩

end GlobalTheory.CompanionTheory.BZPsiPG.FibKer.SmFib

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothFibreActionStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_fibre_action : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {Z : Type} [AddCommGroup Z] [Module ℂ Z] (ρ₀ : Representation ℂ (Multiplicative (Fin i → k)) Z), IsSmooth ρ₀ → IsSmooth (fibAct t ρ₀) := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.FibKer.SmFib.isSmooth_fibAct | exact GlobalTheory.CompanionTheory.BZPsiPG.FibKer.SmFib.isSmooth_fibAct | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.FibKer.SmFib.isSmooth_fibAct <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetFunctionTranslateJacquetKernel
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetFunctionTranslateJacquetKernel
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibKer

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem topPart_append_zero (i t : ℕ) (a : Fin t → k) : topP i t (Fin.append (0 : Fin i → k) a) = 0 := by
  funext j
  exact Fin.append_left _ _ j

theorem middlePart_append_zero (i t : ℕ) (a : Fin t → k) : middlePart i t (Fin.append (0 : Fin i → k) a) = a := by
  funext j
  exact Fin.append_right _ _ j

theorem fibAct_cosetFn_translate (i t : ℕ) {Z : Type} [AddCommGroup Z] [Module ℂ Z]
    (ρ₀ : Representation ℂ (Multiplicative (Fin i → k)) Z) {c : k} (hc : c ≠ 0) (a : Fin t → k) (z : Z) :
    fibAct t ρ₀ (Multiplicative.ofAdd (Fin.append (0 : Fin i → k) a)) (cosetFn t hc a z) = cosetFn t hc 0 z := by
  apply Subtype.ext
  funext v
  have h1 : Multiplicative.ofAdd (topP i t (Fin.append (0 : Fin i → k) a)) = 1 :=
    congrArg Multiplicative.ofAdd (topPart_append_zero i t a)
  have h2 : (fibAct t ρ₀ (Multiplicative.ofAdd (Fin.append (0 : Fin i → k) a)) (cosetFn t hc a z)).1 v
      = ρ₀ (Multiplicative.ofAdd (topP i t (Fin.append (0 : Fin i → k) a)))
        ((cosetFn t hc a z).1 (v + middlePart i t (Fin.append (0 : Fin i → k) a))) := rfl
  rw [h2, h1, map_one, middlePart_append_zero]
  show (cosetSet t c a).indicator (fun _ => z) (v + a) = (cosetSet t c 0).indicator (fun _ => z) v
  have hs : (v + a ∈ cosetSet t c a) ↔ v ∈ cosetSet t c 0 := by
    have : v + a - a = v - 0 := by simp
    show Multiplicative.ofAdd (v + a - a) ∈ Lc t c ↔ Multiplicative.ofAdd (v - 0) ∈ Lc t c
    rw [this]
  classical
  by_cases hv : v ∈ cosetSet t c 0
  · rw [Set.indicator_of_mem hv, Set.indicator_of_mem (hs.2 hv)]
  · rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem (fun h => hv (hs.1 h))]

theorem cosetFn_sub_cosetFn_zero_mem_twKer : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {Z : Type} [AddCommGroup Z] [Module ℂ Z] (ρ₀ : Representation ℂ (Multiplicative (Fin i → k)) Z) (c : k) (hc : c ≠ 0) (a : Fin t → k) (z : Z), cosetFn t hc a z - cosetFn t hc 0 z ∈ twKer (fibAct t ρ₀) ⊤ 1 := by
  intro k _ _ _ _ i t Z _ _ ρ₀ c hc a z
  have hgen : cosetFn t hc 0 z - cosetFn t hc a z ∈ twKer (fibAct t ρ₀) ⊤ 1 := by
    refine Submodule.subset_span ⟨⟨Multiplicative.ofAdd (Fin.append (0 : Fin i → k) a), trivial⟩, cosetFn t hc a z, ?_⟩
    have h1 : (((1 : (⊤ : Subgroup (Multiplicative (Fin (i + t) → k))) →* ℂˣ)
        ⟨Multiplicative.ofAdd (Fin.append (0 : Fin i → k) a), trivial⟩ : ℂˣ) : ℂ) = 1 := rfl
    rw [h1, one_smul]
    exact congrArg (· - cosetFn t hc a z) (fibAct_cosetFn_translate i t ρ₀ hc a z).symm
  have := Submodule.neg_mem _ hgen
  rwa [neg_sub] at this

end GlobalTheory.CompanionTheory.BZPsiPG.FibKer

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetFunctionTranslateJacquetKernelStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coset_function_translate_jacquet_kernel : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {Z : Type} [AddCommGroup Z] [Module ℂ Z] (ρ₀ : Representation ℂ (Multiplicative (Fin i → k)) Z) (c : k) (hc : c ≠ 0) (a : Fin t → k) (z : Z), cosetFn t hc a z - cosetFn t hc 0 z ∈ twKer (fibAct t ρ₀) ⊤ 1 := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.FibKer.cosetFn_sub_cosetFn_zero_mem_twKer | exact GlobalTheory.CompanionTheory.BZPsiPG.FibKer.cosetFn_sub_cosetFn_zero_mem_twKer | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.FibKer.cosetFn_sub_cosetFn_zero_mem_twKer <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsLatticePeriodicity
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsLatticePeriodicity
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

noncomputable section

open ValuativeRel Topology Uniformity GlobalTheory.CompanionTheory.BZPsiPG.FibKer

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibKer.LatInv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_inv_integer_subset {W : Set k} (hW : W ∈ 𝓝 (0 : k)) :
    ∃ c : k, c ≠ 0 ∧ ∀ x, c * x ∈ 𝒪[k] → x ∈ W := by
  obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff _).1 hW
  obtain ⟨a, ha⟩ := ValuativeRel.valuation_surjective (γ : ValueGroupWithZero k)
  obtain ⟨w, hw0, hw1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp only [map_zero] at ha
    exact γ.ne_zero ha.symm
  have hd : a * w ≠ 0 := mul_ne_zero ha0 hw0
  refine ⟨(a * w)⁻¹, inv_ne_zero hd, fun x hx => hγ ?_⟩
  have h1 : valuation k ((a * w)⁻¹ * x) ≤ 1 := hx
  have h2 : valuation k x = valuation k (a * w) * valuation k ((a * w)⁻¹ * x) := by
    rw [← map_mul, mul_inv_cancel_left₀ hd]
  show valuation k x < γ
  calc valuation k x = valuation k (a * w) * valuation k ((a * w)⁻¹ * x) := h2
    _ ≤ valuation k (a * w) * 1 := mul_le_mul_right h1 _
    _ = γ * valuation k w := by rw [mul_one, map_mul, ha]
    _ < γ * 1 := mul_lt_mul_of_pos_left hw1 (zero_lt_iff.mpr γ.ne_zero)
    _ = γ := mul_one _

theorem exists_Lc_subset (t : ℕ) {W : Set (Fin t → k)} (hW : W ∈ 𝓝 (0 : Fin t → k)) :
    ∃ c : k, c ≠ 0 ∧ ∀ o ∈ Lc t c, o.toAdd ∈ W := by
  rw [nhds_pi, Filter.mem_pi] at hW
  obtain ⟨I, -, s, hs, hsub⟩ := hW
  have hU : (⋂ j, s j) ∈ 𝓝 (0 : k) := Filter.iInter_mem.2 hs
  obtain ⟨c, hc, h⟩ := exists_inv_integer_subset hU
  exact ⟨c, hc, fun o ho => hsub fun j _ => Set.mem_iInter.1 (h _ (ho j)) j⟩

theorem exists_Lc_invariant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (t : ℕ) {Z : Type} [AddCommGroup Z] [Module ℂ Z] (φ : (Fin t → k) → Z), IsLocallyConstant φ → HasCompactSupport φ → ∃ c : k, c ≠ 0 ∧ ∀ o ∈ Lc t c, ∀ v, φ (v + o.toAdd) = φ v := by
  intro k _ _ _ _ t Z _ _ φ hl hc
  letI uG : UniformSpace (Fin t → k) := IsTopologicalAddGroup.rightUniformSpace _
  haveI : IsUniformAddGroup (Fin t → k) := isUniformAddGroup_of_addCommGroup
  letI uZ : UniformSpace Z := ⊥
  have huc : UniformContinuous φ := hc.uniformContinuous_of_continuous hl.continuous
  have hmem : {p : (Fin t → k) × (Fin t → k) | φ p.1 = φ p.2} ∈ 𝓤 (Fin t → k) := by
    have h0 : {q : Z × Z | q.1 = q.2} ∈ 𝓤 Z := by
      show _ ∈ 𝓤[(⊥ : UniformSpace Z)]
      rw [bot_uniformity]
      exact Filter.mem_principal_self _
    exact huc h0
  rw [uniformity_eq_comap_nhds_zero, Filter.mem_comap] at hmem
  obtain ⟨W, hW, hsub⟩ := hmem
  obtain ⟨c, hc0, h⟩ := exists_Lc_subset t hW
  refine ⟨c, hc0, fun o ho v => ?_⟩
  have hv : (v, v + o.toAdd) ∈ (fun x : (Fin t → k) × (Fin t → k) => x.2 - x.1) ⁻¹' W := by
    show v + o.toAdd - v ∈ W
    rw [add_sub_cancel_left]
    exact h o ho
  exact (hsub hv).symm

end GlobalTheory.CompanionTheory.BZPsiPG.FibKer.LatInv

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsLatticePeriodicityStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lattice_periodicity : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (t : ℕ) {Z : Type} [AddCommGroup Z] [Module ℂ Z] (φ : (Fin t → k) → Z), IsLocallyConstant φ → HasCompactSupport φ → ∃ c : k, c ≠ 0 ∧ ∀ o ∈ Lc t c, ∀ v, φ (v + o.toAdd) = φ v := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.FibKer.LatInv.exists_Lc_invariant | exact GlobalTheory.CompanionTheory.BZPsiPG.FibKer.LatInv.exists_Lc_invariant | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.FibKer.LatInv.exists_Lc_invariant <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralCosetIndicatorSum
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralCosetIndicatorSum
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibKer.SmSum

theorem measure_cosetSet_eq {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (t : ℕ) [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)]
    (μ : MeasureTheory.Measure (Fin t → k)) [μ.IsAddHaarMeasure] (c : k) (a : Fin t → k) :
    μ (cosetSet t c a) = μ (cosetSet t c 0) := by
  have h : cosetSet t c a = (fun v => (-a) + v) ⁻¹' cosetSet t c 0 := by
    ext v
    have e : v - a = (-a) + v - 0 := by abel
    show Multiplicative.ofAdd (v - a) ∈ Lc t c ↔ Multiplicative.ofAdd ((-a) + v - 0) ∈ Lc t c
    rw [e]
  rw [h]
  exact MeasureTheory.measure_preimage_add μ (-a) _

theorem smInt_sum_coset : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (t : ℕ) {Z : Type} [AddCommGroup Z] [Module ℂ Z] [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k)) [μ.IsAddHaarMeasure] (c : k), c ≠ 0 → ∀ (A : Finset (Fin t → k)) (z : (Fin t → k) → Z), smInt μ (fun v => ∑ a ∈ A, (cosetSet t c a).indicator (fun _ => z a) v) = (((μ (cosetSet t c 0)).toReal : ℝ) : ℂ) • ∑ a ∈ A, z a := by
  intro k _ _ _ _ t Z _ _ _ _ μ _ c hc A z
  classical
  have hmem : ∀ B : Finset (Fin t → k),
      (fun v => ∑ a ∈ B, (cosetSet t c a).indicator (fun _ => z a) v) ∈ fibM (Fin t → k) Z := by
    intro B
    have h := Submodule.sum_mem (fibM (Fin t → k) Z) (t := B)
      (f := fun a => (cosetSet t c a).indicator (fun _ => z a))
      (fun a _ => (cosetFn t hc a (z a)).2)
    have e : (fun v => ∑ a ∈ B, (cosetSet t c a).indicator (fun _ => z a) v) =
        ∑ a ∈ B, (cosetSet t c a).indicator (fun _ => z a) := by
      funext v
      rw [Finset.sum_apply]
    rw [e]
    exact h
  refine Finset.induction_on A ?_ ?_
  · have h := GlobalTheory.CompanionTheory.Rodier.SmIntEl.smInt_indicator μ (∅ : Set (Fin t → k)) (0 : Z)
    simpa using h
  · intro a B ha ih
    have e : (fun v => ∑ b ∈ insert a B, (cosetSet t c b).indicator (fun _ => z b) v) =
        (cosetSet t c a).indicator (fun _ => z a) +
          fun v => ∑ b ∈ B, (cosetSet t c b).indicator (fun _ => z b) v := by
      funext v
      rw [Finset.sum_insert ha]
      rfl
    have l₁ : IsLocallyConstant ((cosetSet t c a).indicator fun _ => z a) := (cosetFn t hc a (z a)).2.1
    have c₁ : HasCompactSupport ((cosetSet t c a).indicator fun _ => z a) := (cosetFn t hc a (z a)).2.2
    rw [e, GlobalTheory.CompanionTheory.Rodier.SmIntEl.smInt_add μ l₁ c₁ (hmem B).1 (hmem B).2, ih, GlobalTheory.CompanionTheory.Rodier.SmIntEl.smInt_indicator,
      measure_cosetSet_eq t μ c a, Finset.sum_insert ha, smul_add]

end GlobalTheory.CompanionTheory.BZPsiPG.FibKer.SmSum

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralCosetIndicatorSumStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_coset_indicator_sum : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (t : ℕ) {Z : Type} [AddCommGroup Z] [Module ℂ Z] [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k)) [μ.IsAddHaarMeasure] (c : k), c ≠ 0 → ∀ (A : Finset (Fin t → k)) (z : (Fin t → k) → Z), smInt μ (fun v => ∑ a ∈ A, (cosetSet t c a).indicator (fun _ => z a) v) = (((μ (cosetSet t c 0)).toReal : ℝ) : ℂ) • ∑ a ∈ A, z a := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.FibKer.SmSum.smInt_sum_coset | exact GlobalTheory.CompanionTheory.BZPsiPG.FibKer.SmSum.smInt_sum_coset | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.FibKer.SmSum.smInt_sum_coset <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosureKernelMemJacquetKernel
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosureKernelMemJacquetKernel
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibKer

theorem tmul_mem_twKer_topRep (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (i : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (τ : Representation ℂ (Mir k i) V) {w : V} (hw : w ∈ twKer τ (MirUin k i) 1) (b : W) :
    w ⊗ₜ[ℂ] b ∈ twKer (topRep τ W) ⊤ 1 := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨n, a, rfl⟩ := hw
    obtain ⟨x, hx⟩ := exists_uM_of_mem k i n.2
    refine Submodule.subset_span ⟨⟨Multiplicative.ofAdd x, Subgroup.mem_top _⟩, a ⊗ₜ[ℂ] b, ?_⟩
    have h1 : topRep τ W (Multiplicative.ofAdd x) (a ⊗ₜ[ℂ] b) = (τ (uM k i x) a) ⊗ₜ[ℂ] b := rfl
    simp only [MonoidHom.one_apply, Units.val_one, one_smul]
    rw [h1, hx, TensorProduct.sub_tmul]
  | zero => simp
  | add x y _ _ hx hy =>
    rw [TensorProduct.add_tmul]
    exact add_mem hx hy
  | smul c x _ hx =>
    rw [← TensorProduct.smul_tmul']
    exact Submodule.smul_mem _ c hx

theorem mem_twKer_topRep_of_clT_eq_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (z : V ⊗[ℂ] W), clT τ W z = 0 → z ∈ twKer (topRep τ W) ⊤ 1 := by
  intro k _ _ _ _ i V W _ _ _ _ τ z hz
  have hex : Function.Exact (twKer τ (MirUin k i) 1).subtype (twKer τ (MirUin k i) 1).mkQ :=
    LinearMap.exact_subtype_mkQ _
  obtain ⟨y, rfl⟩ := (rTensor_exact W hex (Submodule.mkQ_surjective _) z).1 hz
  clear hz
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul w b => exact tmul_mem_twKer_topRep k i τ w.2 b
  | add a b ha hb =>
    rw [map_add (f := _)]
    exact add_mem ha hb

end GlobalTheory.CompanionTheory.BZPsiPG.FibKer

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosureKernelMemJacquetKernelStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closure_kernel_mem_jacquet_kernel : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (z : V ⊗[ℂ] W), clT τ W z = 0 → z ∈ twKer (topRep τ W) ⊤ 1 := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.FibKer.mem_twKer_topRep_of_clT_eq_zero | exact GlobalTheory.CompanionTheory.BZPsiPG.FibKer.mem_twKer_topRep_of_clT_eq_zero | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.FibKer.mem_twKer_topRep_of_clT_eq_zero <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetKernelLatticeConjCompact
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetKernelLatticeConjCompact
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibKer.IntTwist

open ValuativeRel in
theorem mulH_inv_mem_Lc {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : ℕ} {c : k} {κ : GL (Fin n) k}
    (hκ : κ ∈ GlobalTheory.SplitWeil.KO k (Fin n)) {l : Multiplicative (Fin n → k)} (hl : l ∈ Lc n c) :
    mulH κ⁻¹ l ∈ Lc n c := by
  obtain ⟨g, rfl⟩ := hκ
  have hl' : ∀ i, c * l.toAdd i ∈ 𝒪[k] := hl
  have hent : ∀ a b, (((Matrix.GeneralLinearGroup.map (n := Fin n) (algebraMap 𝒪[k] k) g)⁻¹ :
      GL (Fin n) k) : Matrix (Fin n) (Fin n) k) a b ∈ 𝒪[k] := by
    intro a b
    rw [← map_inv]
    exact (((g⁻¹ : GL (Fin n) 𝒪[k]) : Matrix (Fin n) (Fin n) 𝒪[k]) a b).2
  show ∀ j, c * ((((Matrix.GeneralLinearGroup.map (n := Fin n) (algebraMap 𝒪[k] k) g)⁻¹ :
      GL (Fin n) k) : Matrix (Fin n) (Fin n) k) *ᵥ l.toAdd) j ∈ 𝒪[k]
  intro j
  rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine sum_mem fun i _ => ?_
  rw [mul_left_comm]
  exact mul_mem (hent j i) (hl' i)

theorem mulH_mulH_inv {k : Type} [Field k] {n : ℕ} (κ : GL (Fin n) k)
    (l : Multiplicative (Fin n → k)) : mulH κ (mulH κ⁻¹ l) = l := by
  show Multiplicative.ofAdd ((κ : Matrix (Fin n) (Fin n) k).mulVec
    (((κ⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec l.toAdd)) = l
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  rfl

theorem twKer_Lc_le_twist : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) {X : Type} [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (Multiplicative (Fin n → k)) X) (c : k) (κ : GL (Fin n) k), κ ∈ GlobalTheory.SplitWeil.KO k (Fin n) → ∀ x, x ∈ twKer ρ (Lc n c) 1 → x ∈ twKer (MonoidHom.comp ρ (mulH κ)) (Lc n c) 1 := by
  intro k _ _ _ _ n X _ _ ρ c κ hκ x hx
  unfold GlobalTheory.PRep.twKer at hx ⊢
  refine Submodule.span_le.2 ?_ hx
  rintro w ⟨m, v, rfl⟩
  apply Submodule.subset_span
  refine ⟨⟨mulH κ⁻¹ m, mulH_inv_mem_Lc hκ m.2⟩, v, ?_⟩
  simp [mulH_mulH_inv]

end GlobalTheory.CompanionTheory.BZPsiPG.FibKer.IntTwist
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetKernelLatticeConjCompactStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_kernel_lattice_conj_compact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) {X : Type} [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (Multiplicative (Fin n → k)) X) (c : k) (κ : GL (Fin n) k), κ ∈ GlobalTheory.SplitWeil.KO k (Fin n) → ∀ x, x ∈ twKer ρ (Lc n c) 1 → x ∈ twKer (MonoidHom.comp ρ (mulH κ)) (Lc n c) 1 := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.FibKer.IntTwist.twKer_Lc_le_twist | exact GlobalTheory.CompanionTheory.BZPsiPG.FibKer.IntTwist.twKer_Lc_le_twist | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.FibKer.IntTwist.twKer_Lc_le_twist <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocallyConstantCosetIndicatorSum
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocallyConstantCosetIndicatorSum
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibKer

section CosetDecomp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem self_mem_cosetSet_decomp (t : ℕ) (c : k) (a : Fin t → k) : a ∈ cosetSet t c a := by
  show Multiplicative.ofAdd (a - a) ∈ Lc t c
  rw [sub_self, ofAdd_zero]
  exact (Lc t c).one_mem

theorem cosetSet_symm_decomp {t : ℕ} {c : k} {a b : Fin t → k} (h : a ∈ cosetSet t c b) :
    b ∈ cosetSet t c a := by
  have h' : Multiplicative.ofAdd (a - b) ∈ Lc t c := h
  show Multiplicative.ofAdd (b - a) ∈ Lc t c
  rw [← neg_sub, ofAdd_neg]
  exact (Lc t c).inv_mem h'

theorem cosetSet_trans_decomp {t : ℕ} {c : k} {a b d : Fin t → k} (h : a ∈ cosetSet t c b)
    (h' : b ∈ cosetSet t c d) : a ∈ cosetSet t c d := by
  have h1 : Multiplicative.ofAdd (a - b) ∈ Lc t c := h
  have h2 : Multiplicative.ofAdd (b - d) ∈ Lc t c := h'
  show Multiplicative.ofAdd (a - d) ∈ Lc t c
  rw [← sub_add_sub_cancel a b d, ofAdd_add]
  exact (Lc t c).mul_mem h1 h2

theorem exists_coset_reps (t : ℕ) (c : k) (S : Finset (Fin t → k)) :
    ∃ A : Finset (Fin t → k), (∀ s ∈ S, ∃ a ∈ A, s ∈ cosetSet t c a) ∧
      ∀ a ∈ A, ∀ b ∈ A, a ∈ cosetSet t c b → a = b := by
  classical
  refine Finset.induction_on S ?_ ?_
  · exact ⟨∅, by simp, by simp⟩
  · intro x S _ ih
    obtain ⟨A, hcov, huniq⟩ := ih
    by_cases hex : ∃ a ∈ A, x ∈ cosetSet t c a
    · refine ⟨A, ?_, huniq⟩
      intro s hs
      rcases Finset.mem_insert.1 hs with hsx | hsS
      · rw [hsx]
        exact hex
      · exact hcov s hsS
    · push_neg at hex
      refine ⟨insert x A, ?_, ?_⟩
      · intro s hs
        rcases Finset.mem_insert.1 hs with hsx | hsS
        · exact ⟨x, Finset.mem_insert_self _ _, hsx ▸ self_mem_cosetSet_decomp t c x⟩
        · obtain ⟨a, ha, hsa⟩ := hcov s hsS
          exact ⟨a, Finset.mem_insert_of_mem ha, hsa⟩
      · intro a ha b hb hab
        rcases Finset.mem_insert.1 ha with hax | haA
        · rcases Finset.mem_insert.1 hb with hbx | hbA
          · rw [hax, hbx]
          · rw [hax] at hab
            exact absurd hab (hex b hbA)
        · rcases Finset.mem_insert.1 hb with hbx | hbA
          · rw [hbx] at hab
            exact absurd (cosetSet_symm_decomp hab) (hex a haA)
          · exact huniq a haA b hbA hab

end CosetDecomp

theorem eq_sum_coset_indicators : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (t : ℕ) {Z : Type} [AddCommGroup Z] [Module ℂ Z] (φ : (Fin t → k) → Z) (c : k), c ≠ 0 → HasCompactSupport φ → (∀ o ∈ Lc t c, ∀ v, φ (v + o.toAdd) = φ v) → ∃ A : Finset (Fin t → k), ∀ v, φ v = ∑ a ∈ A, (cosetSet t c a).indicator (fun _ => φ a) v := by
  intro k _ _ _ _ t Z _ _ φ c _ hφ hinv
  classical
  have hval : ∀ a v, v ∈ cosetSet t c a → φ v = φ a := by
    intro a v hv
    have := hinv (Multiplicative.ofAdd (v - a)) hv a
    simpa using this
  have hopen : ∀ a, IsOpen (cosetSet t c a) := by
    intro a
    open ValuativeRel in
    have e : cosetSet t c a = ⋂ j, (fun v : Fin t → k => c * (v j - a j)) ⁻¹' ((𝒪[k] : Subring k) : Set k) := by
      ext v
      simp only [Set.mem_iInter, Set.mem_preimage]
      exact Iff.rfl
    rw [e]
    exact isOpen_iInter_of_finite fun j => (SplitWeil.isOpen_int k).preimage (by fun_prop)
  obtain ⟨S, hS⟩ := hφ.elim_finite_subcover (fun a : tsupport φ => cosetSet t c a) (fun a => hopen a)
    (fun v hv => Set.mem_iUnion.2 ⟨⟨v, hv⟩, self_mem_cosetSet_decomp t c v⟩)
  obtain ⟨A, hAcov, hAuniq⟩ := exists_coset_reps t c (S.image Subtype.val)
  refine ⟨A, fun v => ?_⟩
  by_cases hv : ∃ a ∈ A, v ∈ cosetSet t c a
  · obtain ⟨a, ha, hva⟩ := hv
    rw [Finset.sum_eq_single a]
    · rw [Set.indicator_of_mem hva]
      exact hval a v hva
    · intro b hb hba
      rw [Set.indicator_of_notMem]
      intro hvb
      exact hba (hAuniq b hb a ha (cosetSet_trans_decomp (cosetSet_symm_decomp hvb) hva))
    · intro haA
      exact absurd ha haA
  · push_neg at hv
    rw [Finset.sum_eq_zero]
    · by_contra hne
      have hvs : v ∈ tsupport φ := subset_tsupport _ hne
      obtain ⟨s, hsS, hvs'⟩ := Set.mem_iUnion₂.1 (hS hvs)
      obtain ⟨a, ha, hsa⟩ := hAcov s (Finset.mem_image_of_mem _ hsS)
      exact hv a ha (cosetSet_trans_decomp hvs' hsa)
    · intro a ha
      exact Set.indicator_of_notMem (hv a ha) _

end GlobalTheory.CompanionTheory.BZPsiPG.FibKer
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocallyConstantCosetIndicatorSumStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locally_constant_coset_indicator_sum : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (t : ℕ) {Z : Type} [AddCommGroup Z] [Module ℂ Z] (φ : (Fin t → k) → Z) (c : k), c ≠ 0 → HasCompactSupport φ → (∀ o ∈ Lc t c, ∀ v, φ (v + o.toAdd) = φ v) → ∃ A : Finset (Fin t → k), ∀ v, φ v = ∑ a ∈ A, (cosetSet t c a).indicator (fun _ => φ a) v := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.FibKer.eq_sum_coset_indicators | exact GlobalTheory.CompanionTheory.BZPsiPG.FibKer.eq_sum_coset_indicators | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.FibKer.eq_sum_coset_indicators <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteFibreFunctionsCompactStatement
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteFibreFunctionsCompact
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibFin

theorem finite_image_of_rightInvariant {G X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (S : Subgroup G) (hS : IsOpen (S : Set G)) {K : Set G} (hK : IsCompact K) (F : G → X)
    (hF : ∀ g, ∀ s ∈ S, F (g * s) = F g) : (F '' K).Finite := by
  have hcover : K ⊆ ⋃ g : K, (fun x => (g : G) * x) '' (S : Set G) := by
    intro x hx
    exact Set.mem_iUnion.2 ⟨⟨x, hx⟩, 1, S.one_mem, mul_one x⟩
  obtain ⟨T, hT⟩ := hK.elim_finite_subcover (fun g : K => (fun x => (g : G) * x) '' (S : Set G))
    (fun g => (Homeomorph.mulLeft (g : G)).isOpenMap _ hS) hcover
  apply (T.finite_toSet.image (fun g : K => F g)).subset
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨g, hg, hxg⟩ := Set.mem_iUnion₂.1 (hT hx)
  obtain ⟨s, hs, rfl⟩ := hxg
  exact ⟨g, hg, (hF g s hs).symm⟩

theorem finite_fibV_image (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W)
    (f : cIndSpace (HPG k i t) (hRep τ σ)) :
    ((fun κ : GL (Fin (i + t)) k => fibV f κ) ''
      (GlobalTheory.SplitWeil.KO k (Fin (i + t)) : Set (GL (Fin (i + t)) k))).Finite := by
  have hst : IsOpen {m : GlobalTheory.BZMir.Mir k (i + t) | GlobalTheory.BZMir.Leib.prodPG τ σ m f = f} :=
    GlobalTheory.CompanionTheory.BZFun.isSmooth_cInd (GlobalTheory.BZMir.Leib.HPG k i t)
      (GlobalTheory.CompanionTheory.BZPsiPG.hRep τ σ) f
  let H : Subgroup (GL (Fin (i + t)) k) :=
    { carrier := {g | ∀ κ, GlobalTheory.CompanionTheory.BZPsiPG.fibV f (κ * g) = GlobalTheory.CompanionTheory.BZPsiPG.fibV f κ}
      mul_mem' := by
        intro a b ha hb κ
        have ha' : ∀ κ, GlobalTheory.CompanionTheory.BZPsiPG.fibV f (κ * a) = GlobalTheory.CompanionTheory.BZPsiPG.fibV f κ := ha
        have hb' : ∀ κ, GlobalTheory.CompanionTheory.BZPsiPG.fibV f (κ * b) = GlobalTheory.CompanionTheory.BZPsiPG.fibV f κ := hb
        rw [← mul_assoc, hb', ha']
      one_mem' := by
        intro κ
        rw [mul_one]
      inv_mem' := by
        intro a ha κ
        have ha' : ∀ κ, GlobalTheory.CompanionTheory.BZPsiPG.fibV f (κ * a) = GlobalTheory.CompanionTheory.BZPsiPG.fibV f κ := ha
        rw [← ha' (κ * a⁻¹), mul_assoc, inv_mul_cancel, mul_one] }
  have hcont := GlobalTheory.CompanionTheory.BZMirFun.continuous_levi k (i + t)
  have hO := hcont.isOpen_preimage _ hst
  have hone : (1 : GL (Fin (i + t)) k) ∈ GlobalTheory.BZMir.levi k (i + t) ⁻¹'
      {m : GlobalTheory.BZMir.Mir k (i + t) | GlobalTheory.BZMir.Leib.prodPG τ σ m f = f} := by
    show GlobalTheory.BZMir.Leib.prodPG τ σ (GlobalTheory.BZMir.levi k (i + t) 1) f = f
    rw [map_one, map_one]
    rfl
  have hsub : GlobalTheory.BZMir.levi k (i + t) ⁻¹'
      {m : GlobalTheory.BZMir.Mir k (i + t) | GlobalTheory.BZMir.Leib.prodPG τ σ m f = f} ⊆ (H : Set _) := by
    intro g hg κ
    have hg' : GlobalTheory.BZMir.Leib.prodPG τ σ (GlobalTheory.BZMir.levi k (i + t) g) f = f := hg
    funext v
    have h1 := congrArg (fun φ => GlobalTheory.CompanionTheory.BZPsiPG.fibV φ κ v) hg'
    simp only [GlobalTheory.CompanionTheory.BZPsiPG.fibV, map_mul, ← mul_assoc] at h1 ⊢
    exact h1
  have hHopen : IsOpen (H : Set (GL (Fin (i + t)) k)) :=
    Subgroup.isOpen_of_mem_nhds H (Filter.mem_of_superset (hO.mem_nhds hone) hsub)
  have hF : ∀ g : GL (Fin (i + t)) k, ∀ s ∈ H,
      GlobalTheory.CompanionTheory.BZPsiPG.fibV f (g * s) = GlobalTheory.CompanionTheory.BZPsiPG.fibV f g := fun g s hs => hs g
  exact GlobalTheory.CompanionTheory.BZPsiPG.FibFin.finite_image_of_rightInvariant H hHopen GlobalTheory.SplitFlip.isCompact_KO _ hF

end GlobalTheory.CompanionTheory.BZPsiPG.FibFin
end

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_fibre_functions_compact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W) (f : cIndSpace (HPG k i t) (hRep τ σ)), ((fun κ : GL (Fin (i + t)) k => fibV f κ) '' (GlobalTheory.SplitWeil.KO k (Fin (i + t)) : Set (GL (Fin (i + t)) k))).Finite := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.FibFin.finite_fibV_image | exact GlobalTheory.CompanionTheory.BZPsiPG.FibFin.finite_fibV_image | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.FibFin.finite_fibV_image <;> assumption)
end

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibKer

theorem mem_twKer_of_sum {G X ι : Type} [Group G] [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ G X)
    (N : Subgroup G) (T : Finset ι) (hT : T.Nonempty) (g : ι → N) (x : X) (hs : ∑ t ∈ T, ρ (g t : G) x = 0) :
    x ∈ twKer ρ N 1 := by
  have hc : (T.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hT.card_pos.ne'
  have hmem : ∀ t ∈ T, x - ρ (g t : G) x ∈ twKer ρ N 1 := by
    intro t _
    have hg : ρ (g t : G) x - (((1 : N →* ℂˣ) (g t) : ℂˣ) : ℂ) • x ∈ twKer ρ N 1 :=
      Submodule.subset_span ⟨g t, x, rfl⟩
    have := (twKer ρ N 1).neg_mem hg
    simpa using this
  have hs' : (T.card : ℂ) • x = ∑ t ∈ T, (x - ρ (g t : G) x) := by
    rw [Finset.sum_sub_distrib, hs, sub_zero, Finset.sum_const, Nat.cast_smul_eq_nsmul]
  have h1 : (T.card : ℂ) • x ∈ twKer ρ N 1 := by
    rw [hs']
    exact Submodule.sum_mem _ hmem
  exact ((twKer ρ N 1).smul_mem_iff hc).1 h1

theorem exists_reps {L : Type} [Group L] (K : Subgroup L) (hK : K.FiniteIndex) :
    ∃ T : Finset L, T.Nonempty ∧ ∀ x : L, ∃! t, t ∈ T ∧ t⁻¹ * x ∈ K := by
  classical
  haveI : Fintype (L ⧸ K) := Fintype.ofFinite _
  refine ⟨(Finset.univ : Finset (L ⧸ K)).image Quotient.out, ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ (QuotientGroup.mk 1))⟩, ?_⟩
  intro x
  refine ⟨(QuotientGroup.mk x : L ⧸ K).out, ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩, ?_⟩
  · exact QuotientGroup.eq.1 (QuotientGroup.out_eq' _)
  · rintro t ⟨ht, hx⟩
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 ht
    have : q = (QuotientGroup.mk x : L ⧸ K) := by
      rw [← QuotientGroup.out_eq' q]
      exact QuotientGroup.eq.2 hx
    rw [this]

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem continuous_mulH {n : ℕ} (κ : GL (Fin n) k) : Continuous (mulH κ) := by
  have : Continuous fun y : Fin n → k => (κ : Matrix (Fin n) (Fin n) k).mulVec y :=
    Continuous.matrix_mulVec continuous_const continuous_id
  exact continuous_ofAdd.comp (this.comp continuous_toAdd)

theorem continuous_uMh (n : ℕ) : Continuous (uMh k n) :=
  (GlobalTheory.T.continuous_levi_unipotent_proj k n).2.1.comp continuous_toAdd

theorem exists_sum_eq_zero_abs (n : ℕ) {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (ρ : Representation ℂ (Multiplicative (Fin n → k)) Y) (hρ : IsSmooth ρ)
    (ρ' : Representation ℂ (Multiplicative (Fin n → k)) X) (hρ' : IsSmooth ρ')
    (S : Set (GL (Fin n) k)) (hS : ∀ κ ∈ S, κ ∈ GlobalTheory.SplitWeil.KO k (Fin n))
    (F : GL (Fin n) k → X →ₗ[ℂ] Y)
    (hF : ∀ κ ∈ S, ∀ y x, F κ (ρ' y x) = ρ (mulH κ y) (F κ x))
    (hinj : ∀ x, (∀ κ ∈ S, F κ x = 0) → x = 0)
    (x : X) (hx : ∀ κ ∈ S, F κ x ∈ twKer ρ ⊤ 1) (hfin : ((fun κ => F κ x) '' S).Finite) :
    ∃ T : Finset (Multiplicative (Fin n → k)), T.Nonempty ∧ ∑ y ∈ T, ρ' y x = 0 := by
  classical
  obtain ⟨c, hc, hS'⟩ := GlobalTheory.T.finite_jacquet_kernel_common_lattice k n ρ _ hfin (by
    rintro _ ⟨κ, hκ, rfl⟩
    exact hx κ hκ)
  have hcomp : IsCompact (Lc n c : Set (Multiplicative (Fin n → k))) := isCompact_Lc n hc
  have hθ : IsOpen (((1 : Lc n c →* ℂˣ).ker : Subgroup (Lc n c)) : Set (Lc n c)) := by
    have : (((1 : Lc n c →* ℂˣ).ker : Subgroup (Lc n c)) : Set (Lc n c)) = Set.univ := by
      ext l
      simp [MonoidHom.mem_ker]
    rw [this]
    exact isOpen_univ
  set K := GlobalTheory.CompanionTheory.TwistedAverage.stabKer ρ' (Lc n c) 1 x with hK
  have hKo : IsOpen (K : Set (Lc n c)) := GlobalTheory.CompanionTheory.TwistedAverage.isOpen_stabKer hρ' _ _ hθ x
  have hKf : K.FiniteIndex := GlobalTheory.CompanionTheory.TwistedAverage.finiteIndex_stabKer hρ' hcomp _ hθ x
  obtain ⟨T, hTn, hT⟩ := exists_reps K hKf
  refine ⟨T.image Subtype.val, hTn.image _, ?_⟩
  rw [Finset.sum_image (fun a _ b _ h => Subtype.ext h)]
  refine hinj _ fun κ hκ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  have hsmooth : IsSmooth (MonoidHom.comp ρ (mulH κ)) := fun v =>
    (hρ v).preimage (continuous_mulH κ)
  have key := GlobalTheory.T.sum_over_compact_cosets_jacquet_kernel (MonoidHom.comp ρ (mulH κ)) hsmooth (Lc n c) hcomp (F κ x)
    (GlobalTheory.T.jacquet_kernel_lattice_conj_compact k n ρ c κ (hS κ hκ) _ (hS' _ ⟨κ, hκ, rfl⟩)) K T hKo
    (fun l hl => by
      have h1 : ρ' (l : Multiplicative (Fin n → k)) x = x := hl.1
      have h2 := hF κ hκ (l : Multiplicative (Fin n → k)) x
      rw [h1] at h2
      exact h2.symm) hT
  refine Eq.trans (Finset.sum_congr rfl fun l _ => ?_) key
  exact hF κ hκ _ x

theorem mem_twKer_fibAct (i t : ℕ) {Z : Type} [AddCommGroup Z] [Module ℂ Z]
    (ρ₀ : Representation ℂ (Multiplicative (Fin i → k)) Z)
    [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k)) [μ.IsAddHaarMeasure]
    (φ : fibM (Fin t → k) Z) (h : smInt μ φ.1 ∈ twKer ρ₀ ⊤ 1) : φ ∈ twKer (fibAct t ρ₀) ⊤ 1 := by
  classical
  obtain ⟨c, hc, hinv⟩ := GlobalTheory.T.exists_lattice_periodicity k t φ.1 φ.2.1 φ.2.2
  obtain ⟨A, hA⟩ := GlobalTheory.T.locally_constant_coset_indicator_sum k t φ.1 c hc φ.2.2 hinv
  have hφ : φ.1 = fun v => ∑ a ∈ A, (cosetSet t c a).indicator (fun _ => φ.1 a) v := funext hA
  have hsum : φ = ∑ a ∈ A, cosetFn t hc a (φ.1 a) := by
    apply Subtype.ext
    funext v
    rw [hA v, Submodule.coe_sum, Finset.sum_apply]
    rfl
  have hI := GlobalTheory.T.integral_coset_indicator_sum k t μ c hc A φ.1
  rw [← hφ] at hI
  rw [hI] at h
  have hz : ∑ a ∈ A, φ.1 a ∈ twKer ρ₀ ⊤ 1 := ((twKer ρ₀ ⊤ 1).smul_mem_iff (GlobalTheory.T.haar_measure_coset_ne_zero k t μ c hc)).1 h
  have h0 : cosetFn t hc 0 (∑ a ∈ A, φ.1 a) = ∑ a ∈ A, cosetFn t hc 0 (φ.1 a) := by
    apply Subtype.ext
    funext v
    rw [Submodule.coe_sum, Finset.sum_apply]
    have e : ∀ z : Z, (cosetFn t hc 0 z).1 v = (cosetSet t c 0).indicator (fun _ => z) v := fun _ => rfl
    simp only [e]
    by_cases hv : v ∈ cosetSet t c 0
    · simp only [Set.indicator_of_mem hv]
    · simp only [Set.indicator_of_notMem hv, Finset.sum_const_zero]
  have hd : φ - cosetFn t hc 0 (∑ a ∈ A, φ.1 a) ∈ twKer (fibAct t ρ₀) ⊤ 1 := by
    have e : φ - cosetFn t hc 0 (∑ a ∈ A, φ.1 a) = ∑ a ∈ A, (cosetFn t hc a (φ.1 a) - cosetFn t hc 0 (φ.1 a)) := by
      rw [h0, Finset.sum_sub_distrib, ← hsum]
    rw [e]
    exact Submodule.sum_mem _ fun a _ => GlobalTheory.T.coset_function_translate_jacquet_kernel k i t ρ₀ c hc a _
  have := (twKer (fibAct t ρ₀) ⊤ 1).add_mem hd (GlobalTheory.T.coset_function_jacquet_kernel k i t ρ₀ c hc _ hz)
  simpa using this

end

end GlobalTheory.CompanionTheory.BZPsiPG.FibKer

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibKer

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {i t : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def fibLin (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W) (hτ : IsSmooth τ) (hσ : IsSmooth σ)
    (κ : GL (Fin (i + t)) k) : cIndSpace (HPG k i t) (hRep τ σ) →ₗ[ℂ] fibM (Fin t → k) (V ⊗[ℂ] W) :=
  LinearMap.codRestrict (fibM (Fin t → k) (V ⊗[ℂ] W))
    (LinearMap.pi fun v => evL (τ := τ) (σ := σ) (uM k (i + t) (midV k i t v) * levi k (i + t) κ))
    (fun x => GlobalTheory.T.fibre_function_locally_constant_compact k i t τ σ hτ hσ x κ)

end

end GlobalTheory.CompanionTheory.BZPsiPG.FibKer

set_option maxHeartbeats 1000000 in
theorem GlobalTheory.CompanionTheory.BZPsiPG.FibKer.mem_twKer_of_fibInt_eq_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W), IsSmooth τ → IsSmooth σ → ∀ [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k)) [μ.IsAddHaarMeasure], ∀ f : cIndSpace (HPG k i t) (hRep τ σ), (∀ g, fibInt μ f g = 0) → f ∈ twKer (prodPG τ σ) (MirUin k (i + t)) 1 := by
  intro k _ _ _ _ i t V W _ _ _ _ τ σ hτ hσ _ _ μ _ f hf
  classical
  have hsm₀ : IsSmooth (topRep τ W) := GlobalTheory.T.smooth_top_representation k i τ hτ
  have hsm : IsSmooth (fibAct t (topRep τ W)) := GlobalTheory.T.smooth_fibre_action k i t (topRep τ W) hsm₀
  have hsmP : IsSmooth (MonoidHom.comp (prodPG τ σ) (uMh k (i + t))) := fun v =>
    (GlobalTheory.CompanionTheory.BZFun.isSmooth_cInd _ _ v).preimage (continuous_uMh (i + t))
  have hker : ∀ κ, fibLin τ σ hτ hσ κ f ∈ twKer (fibAct t (topRep τ W)) ⊤ 1 := fun κ =>
    mem_twKer_fibAct i t (topRep τ W) μ (fibLin τ σ hτ hσ κ f) (GlobalTheory.T.closure_kernel_mem_jacquet_kernel k i τ _ (hf κ))
  have hfin : ((fun κ => fibLin τ σ hτ hσ κ f) '' (GlobalTheory.SplitWeil.KO k (Fin (i + t)) : Set (GL (Fin (i + t)) k))).Finite := by
    refine Set.Finite.of_finite_image (f := Subtype.val) ?_ Subtype.val_injective.injOn
    rw [Set.image_image]
    exact GlobalTheory.T.finite_fibre_functions_compact k i t τ σ f
  have hF : ∀ κ ∈ (GlobalTheory.SplitWeil.KO k (Fin (i + t)) : Set (GL (Fin (i + t)) k)), ∀ y x,
      fibLin τ σ hτ hσ κ (MonoidHom.comp (prodPG τ σ) (uMh k (i + t)) y x) =
        fibAct t (topRep τ W) (mulH κ y) (fibLin τ σ hτ hσ κ x) := by
    intro κ _ y x
    apply Subtype.ext
    funext v
    exact GlobalTheory.T.fibre_function_unipotent_action k i t τ σ x y.toAdd κ v
  have hinj : ∀ x, (∀ κ ∈ (GlobalTheory.SplitWeil.KO k (Fin (i + t)) : Set (GL (Fin (i + t)) k)), fibLin τ σ hτ hσ κ x = 0) → x = 0 := by
    intro x hx
    exact GlobalTheory.T.induced_vanishing_on_compact k i t τ σ x fun κ hκ => congrArg Subtype.val (hx κ hκ)
  obtain ⟨T, hTn, hT⟩ := exists_sum_eq_zero_abs (i + t) (fibAct t (topRep τ W)) hsm
    (MonoidHom.comp (prodPG τ σ) (uMh k (i + t))) hsmP _ (fun _ h => h) (fibLin τ σ hτ hσ) hF hinj f
    (fun κ _ => hker κ) hfin
  exact mem_twKer_of_sum (prodPG τ σ) (MirUin k (i + t)) T hTn
    (fun y => ⟨uM k (i + t) y.toAdd, uM_mem k (i + t) y.toAdd⟩) f hT

end
