module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermModerateGrowth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlCSurjectiveAndLinearIndependentBLie

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupportedAtInfinityAdeleEqZeroOfComplexComponent
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupportedAtInfinityAdeleEqZeroOfComplexComponent
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section
namespace GlobalTheory.AdeleInfInj

theorem eq_zero_of_piInf_eq_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (emb : ∀ w : InfinitePlace F, EmbOver E w) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evI F) z →
    (∀ w, piInf (emb w) z = 0) → z = 0 := by
  intro F E _ _ _ _ _ σ cm emb z hz hinf
  have hx : ∃ x : E, x ∉ Set.range (algebraMap F E) := by
    by_contra hc
    push_neg at hc
    have h0 : (⊥ : Subalgebra F E) = ⊤ := eq_top_iff.2 fun y _ => Algebra.mem_bot.2 (hc y)
    have h1 := Subalgebra.bot_eq_top_iff_finrank_eq_one.1 h0
    rw [cm.2.2.1] at h1
    exact absurd h1 (by norm_num)
  obtain ⟨x, hx0⟩ := hx
  have li : LinearIndependent F ![(1 : E), x] := LinearIndependent.pair_iff.2 fun s t hst => by
    by_cases ht : t = 0
    · subst ht
      rw [zero_smul, add_zero, smul_eq_zero] at hst
      exact ⟨hst.resolve_right one_ne_zero, rfl⟩
    · exfalso
      apply hx0
      refine ⟨-(s / t), ?_⟩
      rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
      have htE : algebraMap F E t ≠ 0 := (map_ne_zero _).2 ht
      rw [map_neg, map_div₀, neg_div', div_eq_iff htE]
      linear_combination -hst
  let b : Module.Basis (Fin 2) F E := basisOfLinearIndependentOfCardEqFinrank li (by simp [cm.2.2.1])
  have hb0 : b 0 = 1 := by simp [b]
  have hb1 : b 1 = x := by simp [b]
  have him : ∀ τ : E →+* ℂ, (τ x).im ≠ 0 := fun τ h0 => by
    have hσx : σ x = x := τ.injective (by
      rw [cm.2.2.2]
      exact Complex.conj_eq_iff_im.2 h0)
    have hσ : ∀ y, σ y = y := by
      intro y
      have e := b.ext (f₁ := σ.toLinearMap) (f₂ := LinearMap.id) fun i => by
        fin_cases i
        · simp [hb0]
        · simp [hb1, hσx]
      exact LinearMap.congr_fun e y
    have := cm.2.1
    refine (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (InfinitePlace.mk τ)))
      (InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun y => ?_)))
    exact (cm.2.2.2 τ y).symm.trans (by rw [hσ y])
  let bA := Algebra.TensorProduct.basis (AF F) b
  have hz_eq : z = ∑ i, bA.repr z i ⊗ₜ[F] b i := by
    conv_lhs => rw [← bA.sum_repr z]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  let u : AF F := ((0 : Ainf F), (1 : Af F))
  have hfin : ∀ i, (bA.repr z i).2 = 0 := fun i => by
    have h1 : bA.repr (u • z) i = u * bA.repr z i := by rw [map_smul]; rfl
    rw [hz u (map_zero _), map_zero, Finsupp.zero_apply] at h1
    have h3 : (0 : Af F) = 1 * (bA.repr z i).2 := congrArg Prod.snd h1
    simpa using h3.symm
  have := cm.1
  have hinf' : ∀ w i, evInf F w (bA.repr z i) = 0 := fun w => by
    have hw := IsTotallyReal.isReal w
    have h := hinf w
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hz_eq, map_sum, Fin.sum_univ_two] at h
    change InfinitePlace.Completion.extensionEmbedding w (evInf F w (bA.repr z 0)) * (emb w).1 (b 0) +
      InfinitePlace.Completion.extensionEmbedding w (evInf F w (bA.repr z 1)) * (emb w).1 (b 1) = 0 at h
    rw [hb0, hb1, map_one, mul_one, ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw,
      ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw] at h
    set r0 := InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (evInf F w (bA.repr z 0)) with hr0
    set r1 := InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (evInf F w (bA.repr z 1)) with hr1
    have h1 : r1 = 0 := by
      have := congrArg Complex.im h
      simp at this
      exact this.resolve_right (him _)
    have h0 : r0 = 0 := by
      have := congrArg Complex.re h
      simpa [h1] using this
    intro i
    fin_cases i
    · exact (InfinitePlace.Completion.extensionEmbeddingOfIsReal hw).injective (h0.trans (map_zero _).symm)
    · exact (InfinitePlace.Completion.extensionEmbeddingOfIsReal hw).injective (h1.trans (map_zero _).symm)
  have hc : ∀ i, bA.repr z i = 0 := fun i => Prod.ext (funext fun w => hinf' w i) (hfin i)
  rw [hz_eq]
  simp [hc]

end GlobalTheory.AdeleInfInj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupportedAtInfinityAdeleEqZeroOfComplexComponentStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.supportedAtInfinity_adele_eq_zero_of_complexComponents : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (emb : ∀ w : InfinitePlace F, EmbOver E w) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evI F) z →
    (∀ w, piInf (emb w) z = 0) → z = 0 := by
  first | exact @GlobalTheory.AdeleInfInj.eq_zero_of_piInf_eq_zero | exact GlobalTheory.AdeleInfInj.eq_zero_of_piInf_eq_zero | (intros; apply GlobalTheory.AdeleInfInj.eq_zero_of_piInf_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactClosureZpowersIffBoundedEntries
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactClosureZpowersIffBoundedEntries
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb

noncomputable section

namespace GlobalTheory.PowersCompact

theorem ball_isCompact_isOpen {E : Type} [Field E] [NumberField E] (w : Pl E) (m : ℤ) :
    IsCompact {x : w.adicCompletion E | Valued.v x ≤ WithZero.exp m} ∧
      IsOpen {x : w.adicCompletion E | Valued.v x ≤ WithZero.exp m} := by
  obtain ⟨c, hc⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective E w (WithZero.exp m)
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc
    exact WithZero.exp_ne_zero hc.symm
  have hO : IsOpen (w.adicCompletionIntegers E : Set (w.adicCompletion E)) :=
    Valued.isOpen_valuationSubring _
  have hC : IsCompact (w.adicCompletionIntegers E : Set (w.adicCompletion E)) :=
    isCompact_iff_compactSpace.2 (GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers E w)
  have e : {x : w.adicCompletion E | Valued.v x ≤ WithZero.exp m} =
      (Homeomorph.mulLeft₀ c⁻¹ (inv_ne_zero hc0)) ⁻¹' (w.adicCompletionIntegers E) := by
    ext x
    change _ ↔ Valued.v (c⁻¹ * x) ≤ 1
    rw [map_mul, map_inv₀, hc, inv_mul_le_iff₀ WithZero.exp_pos, mul_one]
    exact Iff.rfl
  rw [e]
  exact ⟨(Homeomorph.isCompact_preimage _).2 hC, (Homeomorph.isOpen_preimage _).2 hO⟩

theorem exists_le_exp {E : Type} [Field E] [NumberField E] (w : Pl E) (x : w.adicCompletion E) :
    ∃ m : ℤ, Valued.v x ≤ WithZero.exp m := by
  by_cases hx : Valued.v x = 0
  · exact ⟨0, by rw [hx]; exact zero_le'⟩
  · exact ⟨WithZero.log (Valued.v x), (WithZero.exp_log hx).ge⟩

theorem isCompact_closure_zpowers_iff {E : Type} [Field E] [NumberField E] [IsCMField E]
    (w : Pl E) (n : ℕ) (H : Subgroup (GLw n w)) (hH : IsClosed (H : Set (GLw n w))) (s : H) :
    IsCompact (closure (Subgroup.zpowers s : Set H)) ↔ ∃ m : ℤ, ∀ k : ℤ, ∀ i j,
      Valued.v ((((s ^ k : H) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤
        WithZero.exp m := by
  let B : ℤ → Set (w.adicCompletion E) := fun m => {x | Valued.v x ≤ WithZero.exp m}
  constructor
  · intro hK
    have key : ∀ p : Fin n × Fin n, ∃ m : ℤ, ∀ u ∈ closure (Subgroup.zpowers s : Set H),
        Valued.v (((u : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) p.1 p.2) ≤
          WithZero.exp m := by
      intro p
      have hc : Continuous fun u : H =>
          (((u : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) p.1 p.2) :=
        (Units.continuous_val.comp continuous_subtype_val).matrix_elem p.1 p.2
      obtain ⟨m, hm⟩ := (hK.image hc).elim_directed_cover B
        (fun m => (ball_isCompact_isOpen w m).2)
        (by
          intro x _
          obtain ⟨m, hm⟩ := exists_le_exp w x
          exact Set.mem_iUnion.2 ⟨m, hm⟩)
        (by
          intro a b
          refine ⟨max a b, ?_, ?_⟩ <;> intro x hx <;>
            exact le_trans hx (WithZero.exp_le_exp.2 (by omega)))
      exact ⟨m, fun u hu => hm ⟨u, hu, rfl⟩⟩
    choose m hm using key
    obtain ⟨M, hM⟩ := (Set.finite_range m).bddAbove
    refine ⟨M, fun k i j => ?_⟩
    have h1 := hm (i, j) (s ^ k) (subset_closure (Subgroup.zpow_mem_zpowers s k))
    exact le_trans h1 (WithZero.exp_le_exp.2 (hM ⟨(i, j), rfl⟩))
  · rintro ⟨m, hm⟩
    let Bm : Set (Matrix (Fin n) (Fin n) (w.adicCompletion E)) := {A | ∀ i j, A i j ∈ B m}
    have hBm : IsCompact Bm := by
      have : Bm = Set.pi Set.univ (fun _ : Fin n => Set.pi Set.univ (fun _ : Fin n => B m)) := by
        ext A
        exact ⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ _) j (Set.mem_univ _)⟩
      rw [this]
      exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => (ball_isCompact_isOpen w m).1
    let f : H → Matrix (Fin n) (Fin n) (w.adicCompletion E) ×
        (Matrix (Fin n) (Fin n) (w.adicCompletion E))ᵐᵒᵖ :=
      Units.embedProduct _ ∘ Subtype.val
    have hf : Topology.IsClosedEmbedding f :=
      Units.isClosedEmbedding_embedProduct.comp hH.isClosedEmbedding_subtypeVal
    let K := Bm ×ˢ (MulOpposite.op '' Bm)
    have hKc : IsCompact K := hBm.prod (hBm.image MulOpposite.continuous_op)
    have hC : IsCompact (f ⁻¹' K) := hf.isCompact_preimage hKc
    have hsub : (Subgroup.zpowers s : Set H) ⊆ f ⁻¹' K := by
      intro x hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      refine ⟨fun i j => hm k i j, ⟨(((s ^ k : H) : GLw n w)⁻¹ : GLw n w), fun i j => ?_, rfl⟩⟩
      have h2 := hm (-k) i j
      rw [_root_.zpow_neg] at h2
      change Valued.v (_ : w.adicCompletion E) ≤ WithZero.exp m
      simpa using h2
    exact hC.of_isClosed_subset isClosed_closure (closure_minimal hsub hC.isClosed)

end GlobalTheory.PowersCompact
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactClosureZpowersIffBoundedEntriesStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompact_closure_zpowers_iff_bounded_entries : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (w : Pl E) (n : ℕ) (H : Subgroup (GLw n w)), IsClosed (H : Set (GLw n w)) → ∀ s : H, IsCompact (closure (Subgroup.zpowers s : Set H)) ↔ ∃ m : ℤ, ∀ k : ℤ, ∀ i j, Valued.v ((((s ^ k : H) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ WithZero.exp m := by
  first | exact @GlobalTheory.PowersCompact.isCompact_closure_zpowers_iff | exact GlobalTheory.PowersCompact.isCompact_closure_zpowers_iff | (intros; apply GlobalTheory.PowersCompact.isCompact_closure_zpowers_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermSliceLeviModerateGrowth
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermSliceLeviModerateGrowth
open NumberField MeasureTheory GlobalTheory.CuspRep

noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.LeviGA

namespace GlobalTheory.SliceTwo.Growth

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]


omit [_root_.NumberField.IsTotallyComplex E] in
theorem height_inv {a : ℕ} (y : GL (Fin a) (Cinf E)) : height y⁻¹ = height y := by
  unfold height; rw [inv_inv]; ring


omit [_root_.NumberField.IsTotallyComplex E] in
theorem height_mul_right_le {a : ℕ} (c : GL (Fin a) (Cinf E)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y, height (y * c) ≤ B * height y := by
  obtain ⟨B, hB, h⟩ := GlobalTheory.ConstTermGrowth.height_mul_left_le (E := E) (isCompact_singleton (x := c⁻¹))
  refine ⟨B, hB, fun y => ?_⟩
  have := h _ rfl y⁻¹
  rwa [← _root_.mul_inv_rev, height_inv, height_inv] at this


omit [_root_.NumberField.IsTotallyComplex E] in
theorem norm_toL_blkGL_one_le {a r : ℕ} (hr : r ≤ a) (y : GL (Fin (a - r)) (Cinf E)) :
    ‖toL (blkGL hr (1, y)).val‖ ≤ 1 + ‖toL y.val‖ := by
  have h0 : (0 : ℝ) ≤ 1 + ‖toL y.val‖ := by positivity
  refine (pi_norm_le_iff_of_nonneg h0).2 fun i => (pi_norm_le_iff_of_nonneg h0).2 fun j => ?_
  obtain ⟨i, rfl⟩ := (blkEquiv hr).surjective i
  obtain ⟨j, rfl⟩ := (blkEquiv hr).surjective j
  change ‖(blkGL hr (1, y) : Matrix (Fin a) (Fin a) (Cinf E)) (blkEquiv hr i) (blkEquiv hr j)‖ ≤ _
  rw [blkGL_apply]
  rcases i with i | i <;> rcases j with j | j
  · simp only [Matrix.fromBlocks_apply₁₁, Units.val_one]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.one_apply_eq]
      refine ((pi_norm_le_iff_of_nonneg zero_le_one).2 fun w => ?_).trans (by linarith [norm_nonneg (toL y.val)])
      simp
    · rw [Matrix.one_apply_ne hij, norm_zero]; exact h0
  · simp only [Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, norm_zero]; exact h0
  · simp only [Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, norm_zero]; exact h0
  · simp only [Matrix.fromBlocks_apply₂₂]
    exact ((norm_le_pi_norm (toL y.val i) j).trans (norm_le_pi_norm (toL y.val) i)).trans
      (by linarith)


omit [_root_.NumberField.IsTotallyComplex E] in
theorem height_blkGL_one_le {a r : ℕ} (hr : r ≤ a) (y : GL (Fin (a - r)) (Cinf E)) :
    height (blkGL hr (1, y)) ≤ 3 * height y := by
  have e : (blkGL hr (1, y))⁻¹ = blkGL hr (1, y⁻¹) := by
    rw [← map_inv, Prod.inv_mk, inv_one]
  have h1 := norm_toL_blkGL_one_le hr y
  have h2 := norm_toL_blkGL_one_le hr y⁻¹
  have n1 := norm_nonneg (toL y.val)
  have n2 := norm_nonneg (toL (y⁻¹).val)
  unfold height
  rw [e]
  linarith

end GlobalTheory.SliceTwo.Growth


open GlobalTheory.SliceTwo.Growth in
theorem GlobalTheory.SliceTwo.Growth.norm_slice_le : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ)
    (hr : r ≤ a) [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)]
    (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure →
    IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 → ∀ φ : Sm E a, IsAutForm φ →
    ∀ (m₁ : GA E r) (t : GL (Fin a) (Af E)) (κ : Kinf E a) (g : GA E (a - r)), ∃ (C : ℝ) (M : ℕ), ∀ y,
      ‖GlobalTheory.SliceTwo.slice E μ 𝓕 hr φ.1 m₁ t κ (g * infGL E (a - r) y)‖ ≤ C * height y ^ M := by
  intro E _ _ _ a r hr _ _ μ 𝓕 hμ hF h1 φ hφ m₁ t κ g
  obtain ⟨C, N, hC⟩ := GlobalTheory.ConstTermGrowth.norm_constTerm_le E a r μ 𝓕 hμ hF h1 φ hφ.left hφ.level hφ.growth
    (blkGL hr (m₁, g) * finGL E a t)
  obtain ⟨B, hB0, hB⟩ := height_mul_right_le (E := E) (Unitary.toUnits κ)
  refine ⟨|C| * (3 * B) ^ N, N, fun y => ?_⟩
  have e : GlobalTheory.SliceTwo.slice E μ 𝓕 hr φ.1 m₁ t κ (g * infGL E (a - r) y) =
      ∫ x in 𝓕, φ.1 (unip x * ((blkGL hr (m₁, g) * finGL E a t) *
        infGL E a (blkGL hr (1, y) * Unitary.toUnits κ))) ∂μ := by
    unfold GlobalTheory.SliceTwo.slice
    congr 1
    funext x
    congr 2
    rw [GlobalTheory.SliceTwo.blkGL_mul_infGL, map_mul]
    simp only [mul_assoc]
    rw [← mul_assoc (infGL E a (blkGL hr (1, y))) (finGL E a t), infGL_comm]
    simp only [mul_assoc]
  rw [e]
  refine (hC _).trans ?_
  have hy := one_le_height y
  have hb := one_le_height (blkGL hr (1, y) * Unitary.toUnits κ)
  have h3 : height (blkGL hr (1, y) * Unitary.toUnits κ) ≤ 3 * B * height y := by
    calc _ ≤ B * height (blkGL hr (1, y)) := hB _
      _ ≤ B * (3 * height y) := mul_le_mul_of_nonneg_left (height_blkGL_one_le hr y) hB0
      _ = 3 * B * height y := by ring
  calc C * height (blkGL hr (1, y) * Unitary.toUnits κ) ^ N
      ≤ |C| * height (blkGL hr (1, y) * Unitary.toUnits κ) ^ N :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg (by linarith) _)
    _ ≤ |C| * (3 * B * height y) ^ N :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) h3 _) (abs_nonneg C)
    _ = |C| * (3 * B) ^ N * height y ^ N := by ring

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermSliceLeviModerateGrowthStatement
open NumberField MeasureTheory GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_term_slice_levi_moderate_growth : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ) (hr : r ≤ a) [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 → ∀ φ : Sm E a, IsAutForm φ → ∀ (m₁ : GA E r) (t : GL (Fin a) (Af E)) (κ : Kinf E a) (g : GA E (a - r)), ∃ (C : ℝ) (M : ℕ), ∀ y, ‖GlobalTheory.SliceTwo.slice E μ 𝓕 hr φ.1 m₁ t κ (g * infGL E (a - r) y)‖ ≤ C * height y ^ M := by
  first | exact @GlobalTheory.SliceTwo.Growth.norm_slice_le | exact GlobalTheory.SliceTwo.Growth.norm_slice_le | (intros; apply GlobalTheory.SliceTwo.Growth.norm_slice_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeUNuInvEqOneOfCong
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.FunObj.SqNum.NuCond

open GlobalTheory.Mem.Col2.SplitChar
open GlobalTheory.Mem.Chr hiding HChar

theorem levelLe_mono {K : Type} [Field K] [NumberField K] {χ : HChar K} {v : HeightOneSpectrum (𝓞 K)} {a b : ℕ}
    (h : χ.LevelLe v a) (hab : a ≤ b) : χ.LevelLe v b :=
  fun x hx hle => h x hx (hle.trans (WithZero.exp_le_exp.2 (neg_le_neg (Nat.cast_le.2 hab))))

variable {D : D7}

theorem val_le_of_mem_pow {v : HeightOneSpectrum (𝓞 D.host.E)} {n : ℕ} {b : 𝓞 D.host.E} (hb : b ∈ v.asIdeal ^ n) :
    v.valuation D.host.E (b : D.host.E) ≤ WithZero.exp (-(n : ℤ)) := by
  show v.valuation D.host.E (algebraMap (𝓞 D.host.E) D.host.E b) ≤ _
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_le_pow_iff_dvd, Ideal.dvd_iff_le,
    Ideal.span_singleton_le_iff_mem]
  exact hb

theorem vl_le_of_mem_hatId {𝔪 : Ideal (𝓞 D.host.E)} {v : HeightOneSpectrum (𝓞 D.host.E)} {n : ℕ}
    (h𝔪 : ∀ b ∈ 𝔪, v.valuation D.host.E (b : D.host.E) ≤ WithZero.exp (-(n : ℤ))) {y : AE D} (hy : y ∈ hatId D 𝔪) :
    vl D v y ≤ WithZero.exp (-(n : ℤ)) := by
  induction hy using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨b, hb, s, hs, rfl⟩ := hx
    rw [map_mul, vl_inc]
    exact (mul_le_of_le_one_right' (vl_le hs v)).trans (h𝔪 b hb)
  | zero => rw [map_zero]; exact zero_le'
  | add x y _ _ hx hy => exact (Valuation.map_add _ _ _).trans (max_le hx hy)
  | neg x _ hx => rwa [Valuation.map_neg]

theorem condE_le {T : Type} {L : LevCh D T} (P : Places L) {s : HeightOneSpectrum (𝓞 D.host.F)} (hs : s ∈ P.S0) :
    condE P ≤ (P.w s).asIdeal ^ condExp P s :=
  Ideal.le_of_dvd (Finset.dvd_prod_of_mem _ hs)

end GlobalTheory.FunObj.SqNum.NuCond


open GlobalTheory.FunObj.SqNum.NuCond GlobalTheory.Mem.Col2.SplitChar in
theorem GlobalTheory.FunObj.SqNum.heckeU_nuInv_eq_one_of_cong : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ → ∀ (G : GridData L sc) (i j : Fin D.R.m) {N : ℕ} (χν : HeckeU D N), (∀ x, χν.f x = (nuH G μ₀ i j)⁻¹.1 (finIdl D x)) → ∀ u, IntU D u → (u : AE D) - 1 ∈ hatId D (condE G.pl * D.host.conj • condE G.pl) → χν.f u = 1 := by
  classical
  intro D T L sc μ₀ hL G i j N χν hχ u hu hm
  rw [hχ]
  have k1 : 1 ≤ D.R.m - (i : ℕ) := by omega
  have k2 : D.R.m - (i : ℕ) ≤ D.R.m := by omega
  obtain ⟨c, hc, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm D.R D.host
  obtain ⟨n, hn⟩ : ∃ n : HeightOneSpectrum (𝓞 D.host.E) → ℕ, ∀ v, n v =
      if v.under (𝓞 D.host.F) ∈ G.pl.S0 then condExp G.pl (v.under (𝓞 D.host.F)) else 0 := ⟨_, fun _ => rfl⟩
  have hlev : ∀ v, (nuH G μ₀ i j).LevelLe v (n v) := by
    intro v
    have hμ := L.C.isMu0 j
    rw [show nuH G μ₀ i j = L.C.mu0 j * L.xiH μ₀ / G.ch.chiH (D.R.m - i) from rfl, hL.xi_base, mul_one, div_eq_mul_inv]
    refine Formalism.L2.Host.HChar.LevelLe.mul ?_ (Formalism.L2.Host.HChar.LevelLe.inv ?_)
    · by_cases h : v.under (𝓞 D.host.F) ∈ G.pl.S0
      · refine levelLe_mono (hμ.tame v) ?_
        rw [hn v, if_pos h, condExp]
        split_ifs <;> omega
      · refine Formalism.L2.Host.HChar.UnrAt.levelLe (hμ.unr v fun k hk => h ?_) _
        rw [G.pl.mem_S0_of_sum_eq]
        right
        rw [S1_mem_OmF]
        have hk' : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (v.under (𝓞 D.host.F)).asIdeal := by
          show _ ∈ v.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))
          rw [Ideal.mem_comap, map_natCast]
          exact hk
        fin_cases k
        · exact Or.inl hk'
        · exact Or.inr (Or.inl hk')
    · by_cases h : v.under (𝓞 D.host.F) ∈ G.pl.S0
      · by_cases h0 : v.under (𝓞 D.host.F) = G.pl.v0
        · rw [hn v, if_pos h, condExp, if_pos h0]
          exact (G.ch.lev0 _ k1 k2 v h0).1
        · have h1 := (G.pl.mem_S0_of_sum_eq.1 h).resolve_left h0
          rw [hn v, if_pos h, condExp, if_neg h0]
          exact (G.ch.lev1 _ k1 k2 v h1).1
      · rw [hn v, if_neg h]
        exact Formalism.L2.Host.HChar.UnrAt.levelLe (G.ch.unr _ k1 k2 v h) 0
  have hval : ∀ v, vl D v ((u : AE D) - 1) ≤ WithZero.exp (-(n v : ℤ)) := by
    intro v
    by_cases h : v.under (𝓞 D.host.F) ∈ G.pl.S0
    · rw [hn v, if_pos h]
      refine vl_le_of_mem_hatId (fun b hb => ?_) hm
      have hw : (G.pl.w (v.under (𝓞 D.host.F))).under (𝓞 D.host.F) = v.under (𝓞 D.host.F) := G.pl.w_over _ h
      rcases (GlobalTheory.Mem.Chr.under_eq_iff_conjPl c hcm.rank hcm.ne (G.pl.w (v.under (𝓞 D.host.F))) v).1 hw.symm with e | e
      · have hb1 : b ∈ condE G.pl := Ideal.mul_le_left hb
        have hb2 := condE_le G.pl h hb1
        rw [← e] at hb2
        exact val_le_of_mem_pow hb2
      · have hb1 : b ∈ D.host.conj • condE G.pl := Ideal.mul_le_right hb
        rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hb1
        have hb2 := val_le_of_mem_pow (condE_le G.pl h hb1)
        have e2 := e (((D.host.conj⁻¹ • b : 𝓞 D.host.E)) : D.host.E)
        have e3 : c.toRingEquiv (((D.host.conj⁻¹ • b : 𝓞 D.host.E)) : D.host.E) = (b : D.host.E) := by
          show c _ = _
          rw [hc]
          show D.host.conj (D.host.conj⁻¹ (b : D.host.E)) = _
          exact AlgEquiv.apply_symm_apply _ _
        rw [e3] at e2
        rw [e2]
        exact hb2
    · rw [hn v, if_neg h, Nat.cast_zero, neg_zero, WithZero.exp_zero]
      exact vl_le (sub_mem hu.1 (one_mem _)) v
  have hU := finIdl_unit hu
  refine GlobalTheory.Mem.LocTriv.eq_one_of_local D.host.E _ (nuH G μ₀ i j)⁻¹.2.1 (finIdl D u) hU
    (fun w => by rw [finIdl_fst]; rfl) (fun v x hx => ?_)
  have hxu : Formalism.L2.Host.IsUnitAt v x := by
    show Valued.v (x : v.adicCompletion D.host.E) = 1
    rw [hx]
    exact hU v
  refine (hlev v).inv x hxu ?_
  rw [hx, vl_sub_one]
  exact hval v

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianMultiplicationFlatColumnsEval
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianMultiplicationFlatColumnsEval
set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory.HSShort.ColEval

theorem word_succ {K A : Type} [Field K] [AddCommGroup A] [Module K A] {N : ℕ}
    (mul : (Fin N → K) →ₗ[K] Module.End K A) {t : ℕ} (u : Fin (t + 1) → Fin N → K) :
    word mul u = mul (u 0) * word mul (fun i => u i.succ) := by
  simp [word, List.ofFn_succ]

theorem mul_eq_sum {K A : Type} [Field K] [AddCommGroup A] [Module K A] {N : ℕ}
    (mul : (Fin N → K) →ₗ[K] Module.End K A) (v : Fin N → K) :
    mul v = ∑ k, v k • mul (Pi.single k 1) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← map_smul]
  congr 1
  ext j
  simp [Pi.single_apply]

variable {F A : Type} [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A]
  [IsScalarTower (𝓞 F) F A] {S : Sys F A} {E A' : Type} [Field E] [Algebra F E] [AddCommGroup A'] [Module E A']
  {s : Fin S.D → Fin S.N → E} {δ : ℕ}

theorem mul_single_ι (Φ : S.Flat E A' s δ) (k : Fin S.N) (y : A) :
    Φ.mul (Pi.single k 1) (Φ.ι y) = Φ.ι (S.mul (Pi.single k 1) y) := by
  rw [← Φ.mul_ι]
  congr 2
  ext j
  by_cases h : j = k
  · subst h; simp
  · simp [Pi.single_apply, h]

theorem word_ι_expand (Φ : S.Flat E A' s δ) : ∀ (t : ℕ) (U : Fin t → Fin S.N → E) (z : A),
    word Φ.mul U (Φ.ι z) =
      ∑ e : Fin t → Fin S.N, (∏ q, U q (e q)) • Φ.ι (word S.mul (fun q => Pi.single (e q) (1 : F)) z)
  | 0, U, z => by simp [word]
  | t + 1, U, z => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [word_succ, Module.End.mul_apply, word_ι_expand Φ t, map_sum]
    rw [← (Fin.consEquiv fun _ : Fin (t + 1) => Fin S.N).sum_comp, Fintype.sum_prod_type]
    simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, word_succ,
      Module.End.mul_apply, map_smul, mul_eq_sum Φ.mul (U 0), LinearMap.sum_apply, LinearMap.smul_apply,
      mul_single_ι, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun e _ => ?_
    rw [mul_comm]

end GlobalTheory.HSShort.ColEval

namespace GlobalTheory.HSShort.ColEval

theorem columns_eval : ∀ (F A : Type) [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A] (S : Sys F A), S.Hyp → ∀ (E A' : Type) [Field E] [Algebra F E] [AddCommGroup A'] [Module E A'] (s : Fin S.D → Fin S.N → E) (δ : ℕ) (Φ : S.Flat E A' s δ) (d : ℕ) (b : Module.Basis (Fin d) F (S.V S.T)) (c : Fin d → A →ₗ[F] F), S.IsCo b c → ∃ c' : Fin d → A' →ₗ[E] E, (∀ x ∈ Submodule.span E (Φ.ι '' S.V S.T), ∑ i, c' i x • Φ.ι (b i) = x) ∧ ∀ (κ : S.Col) (u : Fin (S.D + 1) × Fin S.N → E), word Φ.mul (fun q k => u (κ.β q, k)) (Φ.ι κ.x) ∈ Submodule.span E (Φ.ι '' S.V S.T) ∧ ∀ i, aeval u (coordP S.mul (c i) κ.β (κ.x : A)) = c' i (word Φ.mul (fun q k => u (κ.β q, k)) (Φ.ι κ.x)) := by
  intro F A _ _ _ _ _ _ S hS E A' _ _ _ _ s δ Φ d b c hc
  set W := Submodule.span E (Φ.ι '' (S.V S.T : Set A)) with hW
  have hli : LinearIndependent E (fun i => Φ.ι (b i)) := Φ.indep d b b.linearIndependent
  have hιV : ∀ (y : A) (hy : y ∈ S.V S.T), Φ.ι y = ∑ i, algebraMap F E (b.repr ⟨y, hy⟩ i) • Φ.ι (b i) := by
    intro y hy
    conv_lhs => rw [show y = ((⟨y, hy⟩ : S.V S.T) : A) from rfl, ← b.sum_repr ⟨y, hy⟩]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Submodule.coe_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Submodule.coe_smul, LinearMap.map_smulₛₗ]
  have hWspan : W = Submodule.span E (Set.range fun i => Φ.ι (b i)) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨y, hy, rfl⟩
      rw [hιV y hy]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨b i, (b i).2, rfl⟩
  obtain ⟨g, hg⟩ := LinearMap.exists_extend
    ((Finsupp.linearEquivFunOnFinite E E (Fin d)).toLinearMap ∘ₗ (hli.repr ∘ₗ Submodule.inclusion (le_of_eq hWspan)))
  have h1 : ∀ x ∈ W, ∑ i, g x i • Φ.ι (b i) = x := by
    intro x hx
    have hx' : x ∈ Submodule.span E (Set.range fun i => Φ.ι (b i)) := hWspan ▸ hx
    have e1 := LinearMap.congr_fun hg ⟨x, hx⟩
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype, LinearEquiv.coe_coe] at e1
    rw [e1, show Submodule.inclusion (le_of_eq hWspan) ⟨x, hx⟩ = ⟨x, hx'⟩ from rfl]
    have e2 := hli.linearCombination_repr ⟨x, hx'⟩
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)] at e2
    simpa using e2
  have h2 : ∀ x ∈ W, ∀ a : Fin d → E, ∑ i, a i • Φ.ι (b i) = x → ∀ i, g x i = a i := by
    intro x hx a ha
    have h0 : ∑ i, (g x i - a i) • Φ.ι (b i) = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, h1 x hx, ha, sub_self]
    intro i
    exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hli _ h0 i)
  have h3 : ∀ (y : A) (hy : y ∈ S.V S.T) i, g (Φ.ι y) i = algebraMap F E (c i y) := by
    intro y hy i
    rw [h2 _ (Submodule.subset_span ⟨y, hy, rfl⟩) _ (hιV y hy).symm i]
    congr 1
    exact (hc i ⟨y, hy⟩).symm
  refine ⟨fun i => LinearMap.proj i ∘ₗ g, fun x hx => h1 x hx, fun κ u => ?_⟩
  have hmem : ∀ e : Fin κ.t → Fin S.N, word S.mul (fun q => Pi.single (e q) (1 : F)) (κ.x : A) ∈ S.V S.T := by
    intro e
    have := (GlobalTheory.HSShort.wordMem F A S hS κ.j κ.t (by rw [κ.add])).1 (fun q => Pi.single (e q) (1 : F)) κ.x κ.x.2
    rwa [κ.add] at this
  rw [word_ι_expand Φ κ.t]
  refine ⟨Submodule.sum_mem _ fun e _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hmem e, rfl⟩), fun i => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [coordP, map_sum, map_mul, aeval_C, map_prod, aeval_X, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.map_smul, LinearMap.coe_proj, Function.eval, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [h3 _ (hmem e) i, mul_comm]

end GlobalTheory.HSShort.ColEval
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianMultiplicationFlatColumnsEvalStatement
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianMultiplicationFlat_columns_eval : ∀ (F A : Type) [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A] (S : Sys F A), S.Hyp → ∀ (E A' : Type) [Field E] [Algebra F E] [AddCommGroup A'] [Module E A'] (s : Fin S.D → Fin S.N → E) (δ : ℕ) (Φ : S.Flat E A' s δ) (d : ℕ) (b : Module.Basis (Fin d) F (S.V S.T)) (c : Fin d → A →ₗ[F] F), S.IsCo b c → ∃ c' : Fin d → A' →ₗ[E] E, (∀ x ∈ Submodule.span E (Φ.ι '' S.V S.T), ∑ i, c' i x • Φ.ι (b i) = x) ∧ ∀ (κ : S.Col) (u : Fin (S.D + 1) × Fin S.N → E), word Φ.mul (fun q k => u (κ.β q, k)) (Φ.ι κ.x) ∈ Submodule.span E (Φ.ι '' S.V S.T) ∧ ∀ i, aeval u (coordP S.mul (c i) κ.β (κ.x : A)) = c' i (word Φ.mul (fun q k => u (κ.β q, k)) (Φ.ι κ.x)) := by
  first | exact @GlobalTheory.HSShort.ColEval.columns_eval | exact GlobalTheory.HSShort.ColEval.columns_eval | (intros; apply GlobalTheory.HSShort.ColEval.columns_eval <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalAddCharComponentTrivialIntegersEventually
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalAddCharComponentTrivialIntegersEventually
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.AdelicU GlobalTheory.WeilM

noncomputable section

namespace GlobalTheory

theorem eq_one_of_forall_norm_pow_sub_one_lt (w : ℂ) (h : ∀ n : ℕ, ‖w ^ n - 1‖ < 1 / 2) : w = 1 := by
  by_contra hw
  have hd : 0 < ‖w - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hw)
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ‖w - 1‖)
  have hre : ∀ k : ℕ, 1 / 2 < (w ^ k).re := by
    intro k
    have h1 := (Complex.abs_re_le_norm (w ^ k - 1)).trans_lt (h k)
    rw [Complex.sub_re, Complex.one_re] at h1
    linarith [(abs_lt.1 h1).1]
  have hsum : (N : ℝ) / 2 ≤ (∑ k ∈ Finset.range N, w ^ k).re := by
    rw [Complex.re_sum]
    have := Finset.sum_le_sum (s := Finset.range N) (fun k _ => (hre k).le)
    simpa [div_eq_mul_inv, mul_comm] using this
  have hnorm : (N : ℝ) / 2 ≤ ‖∑ k ∈ Finset.range N, w ^ k‖ :=
    hsum.trans (Complex.re_le_norm _)
  have hgeom : ‖∑ k ∈ Finset.range N, w ^ k‖ * ‖w - 1‖ < 1 / 2 := by
    rw [← norm_mul, geom_sum_mul]; exact h N
  have : (N : ℝ) / 2 * ‖w - 1‖ < 1 / 2 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hnorm hd.le) hgeom
  have h2 : (N : ℝ) * ‖w - 1‖ < 1 := by linarith
  rw [div_lt_iff₀ hd] at hN
  linarith


open Filter Topology in
theorem psiLoc_eventually_trivial_integers {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ)
    (hψ : Continuous ψ) :
    ∀ᶠ v in Filter.cofinite, ∀ x ∈ (v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F,
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.psiLoc ψ v x = 1 := by
  classical
  let ι : (∀ v : HeightOneSpectrum (𝓞 F), ↥(v.adicCompletionIntegers F)) → AF F := fun y =>
    LinearMap.inr F (Ainf F) (Af F)
      (RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
        (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite
        (fun v => ⟨(y v).1, (y v).2⟩))
  have hι : Continuous ι := by
    have hs : Continuous (fun y : (∀ v : HeightOneSpectrum (𝓞 F), ↥(v.adicCompletionIntegers F)) =>
        RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
          (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite
          (fun v => ⟨(y v).1, (y v).2⟩)) :=
      RestrictedProduct.isEmbedding_structureMap.continuous
    exact continuous_const.prodMk hs
  have hopen : IsOpen {y | ‖ψ (ι y) - 1‖ < 1 / 2} :=
    isOpen_lt ((hψ.comp hι).sub continuous_const).norm continuous_const
  have h0 : (0 : ∀ v : HeightOneSpectrum (𝓞 F), ↥(v.adicCompletionIntegers F)) ∈ {y | ‖ψ (ι y) - 1‖ < 1 / 2} := by
    have : ι 0 = 0 := by
      refine Prod.ext rfl ?_
      show RestrictedProduct.structureMap _ _ _ _ = (0 : Af F)
      refine af_ext fun w => ?_
      rfl
    simp [this, AddChar.map_zero_eq_one]
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.1 hopen 0 h0
  have key : ∀ v, v ∉ I → ∀ x ∈ v.adicCompletionIntegers F, ‖GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.psiLoc ψ v x - 1‖ < 1 / 2 := by
    intro v hv x hx
    let y : ∀ u : HeightOneSpectrum (𝓞 F), ↥(u.adicCompletionIntegers F) := Pi.single v ⟨x, hx⟩
    have hy : y ∈ (I : Set _).pi u := by
      intro a ha
      have hav : a ≠ v := fun e => hv (e ▸ ha)
      have : y a = 0 := Pi.single_eq_of_ne hav _
      rw [this]; exact (hu a ha).2
    have hmem := hsub hy
    have hιy : ι y = LinearMap.inr F (Ainf F) (Af F) (singleFin v x) := by
      refine congrArg (LinearMap.inr F (Ainf F) (Af F)) (af_ext fun w => ?_)
      by_cases e : w = v
      · subst e; rw [evalV_singleFin_self]
        show ((y w : w.adicCompletion F)) = x
        simp [y]
      · rw [evalV_singleFin_ne e]
        show ((y w : w.adicCompletion F)) = 0
        simp [y, Pi.single_eq_of_ne e]
    simpa [hιy, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.psiLoc] using hmem
  have hfin : {v : HeightOneSpectrum (𝓞 F) | ¬ ∀ x ∈ v.adicCompletionIntegers F,
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.psiLoc ψ v x = 1}.Finite := by
    refine (I.finite_toSet).subset fun v hv => ?_
    by_contra hvI
    apply hv
    intro x hx
    refine eq_one_of_forall_norm_pow_sub_one_lt _ fun n => ?_
    have hnx : n • x ∈ v.adicCompletionIntegers F := nsmul_mem hx n
    have := key v hvI (n • x) hnx
    have hpow : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.psiLoc ψ v (n • x) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.psiLoc ψ v x ^ n := by
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.psiLoc, map_nsmul]
      exact AddChar.map_nsmul_eq_pow ψ n _
    rwa [hpow] at this
  exact Filter.eventually_cofinite.2 hfin

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalAddCharComponentTrivialIntegersEventuallyStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.AdelicU GlobalTheory.WeilM

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localAddCharComponent_trivial_integers_eventually : ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), Continuous ψ →
    ∀ᶠ v in Filter.cofinite, ∀ x ∈ (v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.psiLoc ψ v x = 1 := by
  first | exact @GlobalTheory.psiLoc_eventually_trivial_integers | exact GlobalTheory.psiLoc_eventually_trivial_integers | (intros; apply GlobalTheory.psiLoc_eventually_trivial_integers <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralMatrixIffBoundedPowers
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralMatrixIffBoundedPowers
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb

namespace GlobalTheory.IntMatBound

variable (K : UQ) {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (e : K.E ≃+* L)

def boundSub (he : ∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) (n : ℕ) (m : ℤ) :
    Submodule K.O (Matrix (Fin n) (Fin n) K.E) where
  carrier := {X | ∀ i j, Valued.v (e (X i j)) ≤ WithZero.exp m}
  add_mem' := by
    intro X Y hX hY i j
    simp only [Matrix.add_apply, map_add (f := _)]
    exact Valuation.map_add_le _ (hX i j) (hY i j)
  zero_mem' := by
    intro i j
    simp
  smul_mem' := by
    intro c X hX i j
    simp only [Matrix.smul_apply, Algebra.smul_def, map_mul, Valuation.map_mul]
    have h1 : Valued.v (e (algebraMap K.O K.E c)) ≤ 1 := (he _).1 ⟨c, rfl⟩
    calc Valued.v (e (algebraMap K.O K.E c)) * Valued.v (e (X i j)) ≤ 1 * WithZero.exp m :=
          mul_le_mul' h1 (hX i j)
      _ = WithZero.exp m := one_mul _

theorem exists_bound (x : K.E) : ∃ m : ℤ, Valued.v (e x) ≤ WithZero.exp m := by
  by_cases h : Valued.v (e x) = 0
  · exact ⟨0, by rw [h]; exact zero_le'⟩
  · exact ⟨(Valued.v (e x)).log, (WithZero.exp_log h).ge⟩

theorem exists_unif (he : ∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) :
    ∃ ϖ : K.O, ϖ ≠ 0 ∧ Valued.v (e (algebraMap K.O K.E ϖ)) ≤ WithZero.exp (-1) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible K.O
  refine ⟨ϖ, hϖ.ne_zero, ?_⟩
  set w := Valued.v (e (algebraMap K.O K.E ϖ)) with hw
  have hE : algebraMap K.O K.E ϖ ≠ 0 := by
    intro h0
    exact hϖ.ne_zero (IsFractionRing.injective K.O K.E (by simpa using h0))
  have w0 : w ≠ 0 := by
    rw [hw, Valuation.ne_zero_iff]
    exact (map_ne_zero e).2 hE
  have w1 : w ≤ 1 := (he _).1 ⟨ϖ, rfl⟩
  have wne : w ≠ 1 := by
    intro h1
    have : Valued.v (e (algebraMap K.O K.E ϖ)⁻¹) ≤ 1 := by
      rw [map_inv₀, map_inv₀, ← hw, h1, inv_one]
    obtain ⟨u, hu⟩ := (he _).2 this
    apply hϖ.not_isUnit
    refine IsUnit.of_mul_eq_one (b := u) (IsFractionRing.injective K.O K.E ?_)
    rw [map_mul, hu, map_one, mul_inv_cancel₀ hE]
  have wlt : w < 1 := lt_of_le_of_ne w1 wne
  have hlog : w.log < 0 := by
    rw [← WithZero.exp_lt_exp, WithZero.exp_log w0, WithZero.exp_zero]
    exact wlt
  rw [← WithZero.exp_log w0, WithZero.exp_le_exp]
  omega

end GlobalTheory.IntMatBound

open GlobalTheory.IntMatBound in
theorem GlobalTheory.IntMatBound.isIntegral_iff_bounded : ∀ (K : UQ) {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (e : K.E ≃+* L), (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) K.E), IsIntegral K.O M ↔ ∃ m : ℤ, ∀ k : ℕ, ∀ i j, Valued.v (e ((M ^ k) i j)) ≤ WithZero.exp m := by
  intro K L _ _ e he n M
  constructor
  · intro hM
    obtain ⟨s, hs⟩ := hM.fg_adjoin_singleton
    have hb : ∀ p : s × Fin n × Fin n, ∃ m : ℤ, Valued.v (e ((p.1 : Matrix (Fin n) (Fin n) K.E) p.2.1 p.2.2)) ≤ WithZero.exp m :=
      fun p => exists_bound K e _
    choose f hf using hb
    obtain ⟨m, hm⟩ := (Set.finite_range f).bddAbove
    refine ⟨m, fun k i j => ?_⟩
    have hle : Submodule.span K.O (s : Set (Matrix (Fin n) (Fin n) K.E)) ≤ boundSub K e he n m := by
      rw [Submodule.span_le]
      intro X hX i j
      exact (hf ⟨⟨X, hX⟩, i, j⟩).trans (WithZero.exp_le_exp.2 (hm ⟨_, rfl⟩))
    have hk : M ^ k ∈ Submodule.span K.O (s : Set (Matrix (Fin n) (Fin n) K.E)) := by
      rw [hs]
      exact Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton K.O M) k
    exact hle hk i j
  · rintro ⟨m, hm⟩
    obtain ⟨ϖ, hϖ0, hϖ⟩ := exists_unif K e he
    have hE : algebraMap K.O K.E ϖ ≠ 0 := by
      intro h0
      exact hϖ0 (IsFractionRing.injective K.O K.E (by simpa using h0))
    set N := m.toNat with hN
    set y : K.E := (algebraMap K.O K.E ϖ)⁻¹ ^ N with hy
    set S : Submodule K.O (Matrix (Fin n) (Fin n) K.E) :=
      Submodule.span K.O (Set.range fun p : Fin n × Fin n => Matrix.single p.1 p.2 y) with hS
    have hmem : ∀ X : Matrix (Fin n) (Fin n) K.E, (∀ i j, Valued.v (e (X i j)) ≤ WithZero.exp m) → X ∈ S := by
      intro X hX
      rw [Matrix.matrix_eq_sum_single X]
      refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
      have hv : Valued.v (e ((algebraMap K.O K.E ϖ) ^ N * X i j)) ≤ 1 := by
        rw [map_mul, map_pow, Valuation.map_mul, Valuation.map_pow]
        calc Valued.v (e (algebraMap K.O K.E ϖ)) ^ N * Valued.v (e (X i j))
            ≤ WithZero.exp (-1) ^ N * WithZero.exp m := mul_le_mul' (pow_le_pow_left' hϖ N) (hX i j)
          _ = WithZero.exp (N • (-1 : ℤ) + m) := by rw [WithZero.exp_add, WithZero.exp_nsmul]
          _ ≤ WithZero.exp 0 := by
              rw [WithZero.exp_le_exp, nsmul_eq_mul, hN]
              omega
          _ = 1 := WithZero.exp_zero
      obtain ⟨c, hc⟩ := (he _).2 hv
      have : Matrix.single i j (X i j) = c • Matrix.single i j y := by
        rw [Matrix.smul_single, Algebra.smul_def, hc, hy, inv_pow, mul_assoc, mul_comm (X i j), ← mul_assoc,
          mul_inv_cancel₀ (pow_ne_zero _ hE), one_mul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, j), rfl⟩)
    have hSfg : S.FG := Submodule.fg_span (Set.finite_range _)
    have hle : Subalgebra.toSubmodule (Algebra.adjoin K.O {M}) ≤ S := by
      rw [Algebra.adjoin_eq_span, Submodule.span_le]
      rintro _ hx
      obtain ⟨k, rfl⟩ := Submonoid.mem_closure_singleton.1 hx
      exact hmem _ (hm k)
    haveI := isNoetherian_of_fg_of_noetherian S hSfg
    haveI := isNoetherian_of_le hle
    have hfg : (Subalgebra.toSubmodule (Algebra.adjoin K.O {M})).FG := Module.Finite.iff_fg.mp inferInstance
    exact IsIntegral.of_mem_of_fg _ hfg M (Algebra.self_mem_adjoin_singleton K.O M)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralMatrixIffBoundedPowersStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_matrix_iff_bounded_powers : ∀ (K : UQ) {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (e : K.E ≃+* L), (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) K.E), IsIntegral K.O M ↔ ∃ m : ℤ, ∀ k : ℕ, ∀ i j, Valued.v (e ((M ^ k) i j)) ≤ WithZero.exp m := by
  first | exact @GlobalTheory.IntMatBound.isIntegral_iff_bounded | exact GlobalTheory.IntMatBound.isIntegral_iff_bounded | (intros; apply GlobalTheory.IntMatBound.isIntegral_iff_bounded <;> assumption)
end
end
