module

public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.InjectiveOfSumEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGramMatricesCmUnitaryShimuraObject
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFixedPiTensor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsNormMapRingOfIntegersHomStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeImagesEigenLinesCmUnitaryShimuraObject
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegISupMapRankOneLatticeOfGram
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexISupMapEqPow
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexISupMapEqPow
open NumberField

namespace GlobalTheory.SumIndex

theorem relIndex_pi_pi_of {ι G : Type} [Fintype ι] [AddCommGroup G] (A B : ι → AddSubgroup G) :
    (AddSubgroup.pi Set.univ A).relIndex (AddSubgroup.pi Set.univ B) = ∏ i, (A i).relIndex (B i) := by
  let g : (∀ i, B i) →+ (AddSubgroup.pi Set.univ B) :=
    { toFun := fun v => ⟨fun i => (v i : G), fun i _ => (v i).2⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hg : Function.Surjective g := fun x => ⟨fun i => ⟨x.1 i, x.2 i (Set.mem_univ i)⟩, rfl⟩
  have hc : ((AddSubgroup.pi Set.univ A).addSubgroupOf (AddSubgroup.pi Set.univ B)).comap g =
      AddSubgroup.pi Set.univ fun i => (A i).addSubgroupOf (B i) := by
    ext v
    simp [g, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_pi]
  rw [AddSubgroup.relIndex, ← AddSubgroup.index_comap_of_surjective _ hg, hc]
  simp_rw [AddSubgroup.relIndex, AddSubgroup.index, ← Nat.card_pi]
  refine Nat.card_congr ((Quotient.congrRight (fun x y ↦ ?_)).trans (Setoid.piQuotientEquiv _).symm)
  rw [QuotientAddGroup.leftRel_pi]

theorem eq_zero_of_sum_eq_zero {ι R V : Type} [Fintype ι] [DecidableEq ι] [Ring R] [AddCommGroup V]
    [Module R V] (S : ι → Submodule R V) (hS : iSupIndep S) (y : ι → V) (hy : ∀ a, y a ∈ S a)
    (h0 : ∑ a, y a = 0) (b : ι) : y b = 0 := by
  have hb : y b = -∑ a ∈ Finset.univ.erase b, y a := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ b)] at h0
    exact eq_neg_of_add_eq_zero_left h0
  have hmem : y b ∈ ⨆ (a) (_ : a ≠ b), S a := by
    rw [hb]
    refine Submodule.neg_mem _ (Submodule.sum_mem _ fun a ha => ?_)
    exact Submodule.mem_iSup_of_mem a (Submodule.mem_iSup_of_mem (Finset.ne_of_mem_erase ha) (hy a))
  exact (Submodule.disjoint_def.1 (hS b)) _ (hy b) hmem

theorem relIndex_iSup_map_eq_pow : ∀ (K : Type) [Field K] [NumberField K] (W V : Type) [AddCommGroup W] [Module K W] [Module (𝓞 K) W]
  [IsScalarTower (𝓞 K) K W] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (p : ℕ)
  (M : Fin p → (W →ₗ[K] V)) (ℓ N : Submodule (𝓞 K) W), N ≤ ℓ → (∀ a, Function.Injective (M a)) →
  iSupIndep (fun a => Submodule.span K ((ℓ.map ((M a).restrictScalars (𝓞 K)) : Submodule (𝓞 K) V) : Set V)) →
  (⨆ a, N.map ((M a).restrictScalars (𝓞 K))).toAddSubgroup.relIndex
      (⨆ a, ℓ.map ((M a).restrictScalars (𝓞 K))).toAddSubgroup =
    (N.toAddSubgroup.relIndex ℓ.toAddSubgroup) ^ p := by
  intro K _ _ W V _ _ _ _ _ _ _ _ p M ℓ N hNℓ hinj hind
  classical
  let Φ : (Fin p → W) →ₗ[𝓞 K] V := ∑ a, ((M a).restrictScalars (𝓞 K)).comp (LinearMap.proj a)
  have hΦ : ∀ x, Φ x = ∑ a, M a (x a) := by intro x; simp [Φ]
  have himg : ∀ S : Submodule (𝓞 K) W, (Submodule.pi Set.univ (fun _ : Fin p => S)).map Φ =
      ⨆ a, S.map ((M a).restrictScalars (𝓞 K)) := by
    intro S
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      rw [hΦ]
      exact Submodule.sum_mem _ fun a _ => Submodule.mem_iSup_of_mem a ⟨x a, hx a (Set.mem_univ a), rfl⟩
    · refine iSup_le fun a => ?_
      rintro _ ⟨w, hw, rfl⟩
      refine ⟨Pi.single a w, ?_, ?_⟩
      · intro b _
        by_cases h : b = a
        · subst h; simpa using hw
        · simp [Pi.single_apply, h]
      · rw [hΦ, Finset.sum_eq_single a (fun b _ hb => by simp [Pi.single_apply, hb]) (by simp)]
        simp
  let Lp : Submodule (𝓞 K) (Fin p → W) := Submodule.pi Set.univ (fun _ => ℓ)
  let Np : Submodule (𝓞 K) (Fin p → W) := Submodule.pi Set.univ (fun _ => N)
  have hNL : Np ≤ Lp := fun x hx a ha => hNℓ (hx a ha)
  let g : Lp.toAddSubgroup →+ V := Φ.toAddMonoidHom.comp Lp.toAddSubgroup.subtype
  have hg : Function.Injective g := by
    refine (injective_iff_map_eq_zero g).2 fun z hz => ?_
    have h0 : ∑ a, M a (z.1 a) = 0 := by rw [← hΦ]; exact hz
    have hy := eq_zero_of_sum_eq_zero _ hind (fun a => M a (z.1 a))
      (fun a => Submodule.subset_span ⟨z.1 a, z.2 a (Set.mem_univ a), rfl⟩) h0
    exact Subtype.ext (funext fun a => by simpa using hinj a (by simpa using hy a))
  have hL' : (⨆ a, ℓ.map ((M a).restrictScalars (𝓞 K))).toAddSubgroup = (⊤ : AddSubgroup Lp.toAddSubgroup).map g := by
    rw [← himg]
    ext v
    simp [g, Lp]
  have hN' : (⨆ a, N.map ((M a).restrictScalars (𝓞 K))).toAddSubgroup =
      (Np.toAddSubgroup.addSubgroupOf Lp.toAddSubgroup).map g := by
    rw [← himg]
    ext v
    simp only [Submodule.mem_toAddSubgroup, Submodule.mem_map, AddSubgroup.mem_map,
      AddSubgroup.mem_addSubgroupOf, Subtype.exists]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hNL hx, hx, rfl⟩
    · rintro ⟨x, _, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
  rw [hL', hN', AddSubgroup.relIndex_map_map_of_injective _ _ hg, AddSubgroup.relIndex_top_right]
  change Np.toAddSubgroup.relIndex Lp.toAddSubgroup = _
  have e1 : Np.toAddSubgroup = AddSubgroup.pi Set.univ (fun _ : Fin p => N.toAddSubgroup) := by
    ext x; simp [Np, AddSubgroup.mem_pi, Submodule.mem_pi]
  have e2 : Lp.toAddSubgroup = AddSubgroup.pi Set.univ (fun _ : Fin p => ℓ.toAddSubgroup) := by
    ext x; simp [Lp, AddSubgroup.mem_pi, Submodule.mem_pi]
  rw [e1, e2, relIndex_pi_pi_of, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end GlobalTheory.SumIndex
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexISupMapEqPowStatement
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_iSup_map_eq_relIndex_pow : ∀ (K : Type) [Field K] [NumberField K] (W V : Type) [AddCommGroup W] [Module K W] [Module (𝓞 K) W]
  [IsScalarTower (𝓞 K) K W] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (p : ℕ)
  (M : Fin p → (W →ₗ[K] V)) (ℓ N : Submodule (𝓞 K) W), N ≤ ℓ → (∀ a, Function.Injective (M a)) →
  iSupIndep (fun a => Submodule.span K ((ℓ.map ((M a).restrictScalars (𝓞 K)) : Submodule (𝓞 K) V) : Set V)) →
  (⨆ a, N.map ((M a).restrictScalars (𝓞 K))).toAddSubgroup.relIndex
      (⨆ a, ℓ.map ((M a).restrictScalars (𝓞 K))).toAddSubgroup =
    (N.toAddSubgroup.relIndex ℓ.toAddSubgroup) ^ p := by
  first | exact @GlobalTheory.SumIndex.relIndex_iSup_map_eq_pow | exact GlobalTheory.SumIndex.relIndex_iSup_map_eq_pow | (intros; apply GlobalTheory.SumIndex.relIndex_iSup_map_eq_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegISupMapRankOneLatticeOfGram
open NumberField ReciprocityTheory.GeometryOfNumbersTheory

namespace GlobalTheory

open scoped ComplexOrder

theorem deg_iSup_map_of_gram : ∀ (K : Type) [Field K] [NumberField K] (W V : Type) [AddCommGroup W] [Module K W] [Module (𝓞 K) W]
  [IsScalarTower (𝓞 K) K W] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  (hW : HermFam K W) (hV : HermFam K V) (p : ℕ) (M : Fin p → (W →ₗ[K] V)) (ℓ : Submodule (𝓞 K) W)
  (y : Matrix (Fin p) (Fin p) K), ℓ.FG → latRank K ℓ = 1 → (∀ a, Function.Injective (M a)) →
  iSupIndep (fun a => Submodule.span K ((ℓ.map ((M a).restrictScalars (𝓞 K)) : Submodule (𝓞 K) V) : Set V)) →
  (∀ (s : K →+* ℂ) a b, ∀ c ∈ ℓ, hV.form s (M b c) (M a c) = s (y a b) * hW.form s c c) →
  y.det ≠ 0 ∧ deg hV (⨆ a, ℓ.map ((M a).restrictScalars (𝓞 K))) =
    p * deg hW ℓ - (∑ s : K →+* ℂ, Real.log ‖s y.det‖) / (2 * Module.finrank ℚ K) := by
  intro K _ _ W V _ _ _ _ _ _ _ _ hW hV p M ℓ y hfg hrk hinj hind hgram
  have hr : Module.finrank K (Submodule.span K (ℓ : Set W)) = 1 := hrk
  haveI : FiniteDimensional K (Submodule.span K (ℓ : Set W)) :=
    Module.finite_of_finrank_pos (by rw [hr]; norm_num)
  obtain ⟨c, hcℓ, hc0⟩ : ∃ c ∈ ℓ, c ≠ 0 := by
    by_contra hne
    push_neg at hne
    have h0 : Submodule.span K (ℓ : Set W) = ⊥ := by
      rw [Submodule.span_eq_bot]; intro x hx; exact hne x hx
    rw [h0, finrank_bot] at hr; exact zero_ne_one hr
  have hspan : (ℓ : Set W) ⊆ Submodule.span K {c} := by
    have hle : Submodule.span K {c} ≤ Submodule.span K (ℓ : Set W) :=
      Submodule.span_mono (Set.singleton_subset_iff.mpr hcℓ)
    have heq := Submodule.eq_of_le_of_finrank_eq hle (by rw [hr, finrank_span_singleton hc0])
    rw [heq]; exact Submodule.subset_span
  have hfℓ : IsFrame K ℓ ![c] := by
    refine ⟨fun i => by fin_cases i; simpa using hcℓ, ?_, ?_⟩
    · exact linearIndependent_unique_iff.mpr (by simpa using hc0)
    · intro x hx
      refine Submodule.span_mono ?_ (hspan hx)
      rintro _ rfl; exact ⟨0, rfl⟩
  set v : Fin p → V := fun a => M a c with hvdef
  have hvS : ∀ a, v a ∈ ℓ.map ((M a).restrictScalars (𝓞 K)) := fun a => ⟨c, hcℓ, rfl⟩
  have hfS : IsFrame K (⨆ a, ℓ.map ((M a).restrictScalars (𝓞 K))) v := by
    refine ⟨fun a => (le_iSup (fun a => ℓ.map ((M a).restrictScalars (𝓞 K))) a) (hvS a), ?_, ?_⟩
    · exact iSupIndep.linearIndependent _ hind (fun a => Submodule.subset_span (hvS a))
        (fun a h => hc0 (hinj a (h.trans (map_zero (M a)).symm)))
    · intro x hx
      have hle : (⨆ a, ℓ.map ((M a).restrictScalars (𝓞 K))) ≤
          (Submodule.span K (Set.range v)).restrictScalars (𝓞 K) := by
        refine iSup_le fun a => ?_
        rintro _ ⟨z, hz, rfl⟩
        obtain ⟨k, rfl⟩ := Submodule.mem_span_singleton.mp (hspan hz)
        rw [Submodule.restrictScalars_mem, LinearMap.restrictScalars_apply, LinearMap.map_smul]
        exact Submodule.smul_mem _ k (Submodule.subset_span ⟨a, rfl⟩)
      exact hle hx
  have hSfg : (⨆ a, ℓ.map ((M a).restrictScalars (𝓞 K))).FG :=
    Submodule.fg_iSup _ (fun a => hfg.map _)
  have hidx : (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.relIndex
      (⨆ a, ℓ.map ((M a).restrictScalars (𝓞 K))).toAddSubgroup =
      ((Submodule.span (𝓞 K) {c}).toAddSubgroup.relIndex ℓ.toAddSubgroup) ^ p := by
    have h1 : Submodule.span (𝓞 K) (Set.range v) =
        ⨆ a, (Submodule.span (𝓞 K) {c}).map ((M a).restrictScalars (𝓞 K)) := by
      rw [Submodule.span_range_eq_iSup]
      congr 1; funext a
      rw [Submodule.map_span, Set.image_singleton]; rfl
    rw [h1]
    exact GlobalTheory.T.relIndex_iSup_map_eq_relIndex_pow K W V p M ℓ _ ((Submodule.span_singleton_le_iff_mem _ _).mpr hcℓ) hinj hind
  have hgr : ∀ s : K →+* ℂ, hV.gram s v = hW.form s c c • (s.mapMatrix y).transpose := by
    intro s; ext i j
    simp [HermFam.gram, v, hgram s j i c hcℓ, mul_comm]
  have hdet : ∀ s : K →+* ℂ, (hV.gram s v).det = (hW.form s c c) ^ p * s y.det := by
    intro s; rw [hgr, Matrix.det_smul, Matrix.det_transpose, RingHom.map_det, Fintype.card_fin]
  have hpos : ∀ s : K →+* ℂ, 0 < (hV.gram s v).det := fun s => (hV.posDef s p v hfS.2.1).det_pos
  have hA1 : ∀ s : K →+* ℂ, 0 < hW.form s c c := fun s => by
    have := (hW.posDef s 1 ![c] hfℓ.2.1).det_pos
    simpa [Matrix.det_fin_one] using this
  have hAeq : ∀ s : K →+* ℂ, hW.form s c c = (((hW.form s c c).re : ℝ) : ℂ) := fun s =>
    Complex.ext (by simp) (by simp [← (Complex.pos_iff.mp (hA1 s)).2])
  have hkey : ∀ s : K →+* ℂ, 0 < (s y.det).re ∧ (s y.det).im = 0 ∧
      (hV.gram s v).det.re = (hW.form s c c).re ^ p * (s y.det).re := by
    intro s
    have h1 := Complex.pos_iff.mp (hpos s)
    have hA := (Complex.pos_iff.mp (hA1 s)).1
    rw [hdet s, hAeq s, ← Complex.ofReal_pow, Complex.re_ofReal_mul, Complex.im_ofReal_mul] at h1
    have hApow : 0 < (hW.form s c c).re ^ p := pow_pos hA p
    refine ⟨pos_of_mul_pos_right h1.1 hApow.le, ?_, ?_⟩
    · exact (mul_eq_zero.mp h1.2.symm).resolve_left hApow.ne'
    · rw [hdet s, hAeq s, ← Complex.ofReal_pow, Complex.re_ofReal_mul]; simp
  have hlogV : ∀ s : K →+* ℂ, Real.log (hV.gram s v).det.re =
      p * Real.log (hW.form s c c).re + Real.log ‖s y.det‖ := by
    intro s
    obtain ⟨hre, him, heq⟩ := hkey s
    have hn : ‖s y.det‖ = (s y.det).re := by
      rw [← Complex.abs_re_eq_norm.mpr him, abs_of_pos hre]
    rw [heq, hn, Real.log_mul (pow_pos (Complex.pos_iff.mp (hA1 s)).1 p).ne' hre.ne', Real.log_pow]
  have hlogW : ∀ s : K →+* ℂ, Real.log (hW.gram s ![c]).det.re = Real.log (hW.form s c c).re := by
    intro s; simp [HermFam.gram, Matrix.det_fin_one]
  refine ⟨?_, ?_⟩
  · obtain ⟨s⟩ : Nonempty (K →+* ℂ) := inferInstance
    intro h; have := (hkey s).1; rw [h, map_zero] at this; simp at this
  · rw [arakelovDegree_eq_degreeOfFamily hV hSfg hfS, arakelovDegree_eq_degreeOfFamily hW hfg hfℓ]
    unfold degreeOfFamily
    have hrg : Set.range ![c] = {c} := by ext x; simp [eq_comm]
    rw [hrg, hidx, Nat.cast_pow, Real.log_pow, Finset.sum_congr rfl (fun s _ => hlogV s),
      Finset.sum_congr rfl (fun s _ => hlogW s), Finset.sum_add_distrib, ← Finset.mul_sum]
    ring

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegISupMapRankOneLatticeOfGramStatement
open NumberField ReciprocityTheory.GeometryOfNumbersTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deg_iSup_map_rankOne_lattice_of_gram : ∀ (K : Type) [Field K] [NumberField K] (W V : Type) [AddCommGroup W] [Module K W] [Module (𝓞 K) W]
  [IsScalarTower (𝓞 K) K W] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  (hW : HermFam K W) (hV : HermFam K V) (p : ℕ) (M : Fin p → (W →ₗ[K] V)) (ℓ : Submodule (𝓞 K) W)
  (y : Matrix (Fin p) (Fin p) K), ℓ.FG → latRank K ℓ = 1 → (∀ a, Function.Injective (M a)) →
  iSupIndep (fun a => Submodule.span K ((ℓ.map ((M a).restrictScalars (𝓞 K)) : Submodule (𝓞 K) V) : Set V)) →
  (∀ (s : K →+* ℂ) a b, ∀ c ∈ ℓ, hV.form s (M b c) (M a c) = s (y a b) * hW.form s c c) →
  y.det ≠ 0 ∧ deg hV (⨆ a, ℓ.map ((M a).restrictScalars (𝓞 K))) =
    p * deg hW ℓ - (∑ s : K →+* ℂ, Real.log ‖s y.det‖) / (2 * Module.finrank ℚ K) := by
  first | exact @GlobalTheory.deg_iSup_map_of_gram | exact GlobalTheory.deg_iSup_map_of_gram | (intros; apply GlobalTheory.deg_iSup_map_of_gram <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanLogNormEmbeddingsRingHom
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanLogNormEmbeddingsRingHom
open NumberField

namespace GlobalTheory

theorem ringOfIntegers_ringHom_injective {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K]
    (σ : 𝓞 E →+* 𝓞 K) : Function.Injective σ := by
  rw [RingHom.injective_iff_ker_eq_bot]
  apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
  rw [eq_bot_iff]
  intro n hn
  rw [Ideal.mem_comap, RingHom.mem_ker] at hn
  simpa using hn

theorem sum_log_norm_embeddings {K : Type} [Field K] [NumberField K] (y : K) :
    ∑ s : K →+* ℂ, Real.log ‖s y‖ = Real.log |((Algebra.norm ℚ y : ℚ) : ℝ)| := by
  by_cases hy : y = 0
  · subst hy
    simp
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ y
  have h2 : ∏ s : K →+* ℂ, s y = ∏ s : K →ₐ[ℚ] ℂ, s y :=
    Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) _ _ (fun s => rfl)
  rw [← Real.log_prod (fun s _ => by simpa using hy), ← norm_prod, h2, ← h]
  congr 1
  rw [eq_ratCast, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]

theorem mean_log_norm_embeddings_ringHom :
    ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] (σ : 𝓞 E →+* 𝓞 K) (x : 𝓞 E),
  (∑ s : K →+* ℂ, Real.log ‖s (σ x : K)‖) / Module.finrank ℚ K =
    Real.log |((Algebra.norm ℚ (x : E) : ℚ) : ℝ)| / Module.finrank ℚ E := by
  intro E K _ _ _ _ σ x
  have hinj : Function.Injective ((algebraMap (𝓞 K) K).comp σ) :=
    (RingOfIntegers.coe_injective).comp (ringOfIntegers_ringHom_injective σ)
  let τ : E →+* K := IsFractionRing.lift hinj
  have hτ : τ (x : E) = (σ x : K) := IsFractionRing.lift_algebraMap hinj x
  letI : Algebra E K := τ.toAlgebra
  haveI : IsScalarTower ℚ E K := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  haveI : Module.Finite E K := Module.Finite.of_restrictScalars_finite ℚ E K
  have hx : (σ x : K) = algebraMap E K (x : E) := hτ.symm
  rw [sum_log_norm_embeddings, hx, ← Algebra.norm_norm (S := E), Algebra.norm_algebraMap, map_pow,
    ← Module.finrank_mul_finrank ℚ E K]
  have h1 : (Module.finrank ℚ E : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  have h2 : (Module.finrank E K : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  push_cast
  rw [abs_pow, Real.log_pow]
  field_simp

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanLogNormEmbeddingsRingHomStatement
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mean_log_norm_embeddings_ringHom_eq : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] (σ : 𝓞 E →+* 𝓞 K) (x : 𝓞 E),
  (∑ s : K →+* ℂ, Real.log ‖s (σ x : K)‖) / Module.finrank ℚ K =
    Real.log |((Algebra.norm ℚ (x : E) : ℚ) : ℝ)| / Module.finrank ℚ E := by
  first | exact @GlobalTheory.mean_log_norm_embeddings_ringHom | exact GlobalTheory.mean_log_norm_embeddings_ringHom | (intros; apply GlobalTheory.mean_log_norm_embeddings_ringHom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeImagesEigenLinesCmUnitaryShimuraObject
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM GlobalTheory.FlatCM

noncomputable section
namespace GlobalTheory.FlatCM.ImageDeg


open GlobalTheory.HermHom in
theorem form_diff_eq_pair : ThetaUnifAV → Out.Laws → ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P)
  (P' : Out.PolAV (Sp (𝓞 K))) (F' : GenFib P') (h : HermFam K (Fin F.P₀.g → K)) (h' : HermFam K (Fin F'.P₀.g → K))
  (f₁ f₂ : P.A ⟶ P'.A) (g : P.A ⟶ P.A) (M₁ M₂ : (Fin F.P₀.g → K) →ₗ[K] (Fin F'.P₀.g → K))
  (N : (Fin F.P₀.g → K) →ₗ[K] (Fin F.P₀.g → K)), F.IsHerm h → F'.IsHerm h' → IsMonHom f₁ → IsMonHom f₂ →
  IsMonHom g → LamEq P'.L f₁ f₂ P.L g (𝟙 P.A) → F.IsDiffOf F' f₁ M₁ → F.IsDiffOf F' f₂ M₂ → F.IsDiffOf F g N →
  ∀ s c c', h'.form s (M₂ c) (M₁ c') = h.form s c (N c') := by
  intro hU hL K _ _ P F P' F' h h' f₁ f₂ g M₁ M₂ N hh hh' hf₁ hf₂ hg hlam hM₁ hM₂ hN s c c'
  obtain ⟨Q, φ, t, u, Hm, χ, W, hφ, hA, hW, hform⟩ := hh s
  obtain ⟨Q', φ', t', u', Hm', χ', W', hφ', hA', hW', hform'⟩ := hh' s
  obtain ⟨-, a₀, ha₀, ea₀, da⟩ := GlobalTheory.T.existsUnique_differential_monHom_lieBasis K P F P' F' f₁ hf₁
  obtain ⟨-, b₀, hb₀, eb₀, db⟩ := GlobalTheory.T.existsUnique_differential_monHom_lieBasis K P F P' F' f₂ hf₂
  obtain ⟨-, g₀, hg₀, eg₀, dg⟩ := GlobalTheory.T.existsUnique_differential_monHom_lieBasis K P F P F g hg
  have hlam₀ : LamEq F'.P₀.L a₀ b₀ F.P₀.L g₀ (𝟙 F.P₀.A) :=
    lamEq_baseChange _ _ (spMap (algebraMap (𝓞 K) K)) P.A P.A P'.A P.A F.P₀.A F.P₀.A F'.P₀.A F.P₀.A
      F.φ F.φ F'.φ F.φ F.fib.2.1.1.w F.fib.2.1.1.w F'.fib.2.1 F.fib.2.1
      P'.L P.L F'.P₀.L F.P₀.L P'.isLB P.isLB F'.P₀.isLB F.P₀.isLB F'.fib.2.2 F.fib.2.2 f₁ f₂ g (𝟙 _) a₀ b₀ g₀ (𝟙 _)
      ea₀ eb₀ eg₀ (by simp) hlam
  obtain ⟨a₁, ha₁, ea⟩ := NormHom.exists_monHom_lift hφ.2.1 hφ'.2.1 a₀
  obtain ⟨b₁, hb₁, eb⟩ := NormHom.exists_monHom_lift hφ.2.1 hφ'.2.1 b₀
  obtain ⟨g₁, hg₁, eg⟩ := NormHom.exists_monHom_lift hφ.2.1 hφ.2.1 g₀
  obtain ⟨-, -, -, -, t₁, t₂, -⟩ := AHWeil.tangent_and_weil_of_isAH hU Q Q.g u Hm χ hA
  obtain ⟨-, -, -, -, t₁', t₂', -⟩ := AHWeil.tangent_and_weil_of_isAH hU Q' Q'.g u' Hm' χ' hA'
  obtain ⟨Φ₁, hΦ₁, -, hΦd₁, -⟩ :=
    HomLinear.exists_linear_of_isMonHom Q.A Q'.A Q.isAb Q'.isAb Q.L Q'.L Q.g Q'.g u u' t₁' t₂' a₁ ha₁
  obtain ⟨Φ₂, hΦ₂, -, hΦd₂, -⟩ :=
    HomLinear.exists_linear_of_isMonHom Q.A Q'.A Q.isAb Q'.isAb Q.L Q'.L Q.g Q'.g u u' t₁' t₂' b₁ hb₁
  obtain ⟨G, hG, -, hGd, -⟩ :=
    HomLinear.exists_linear_of_isMonHom Q.A Q.A Q.isAb Q.isAb Q.L Q.L Q.g Q.g u u t₁ t₂ g₁ hg₁
  have hlam₁ : LamEq Q'.L a₁ b₁ Q.L g₁ (𝟙 Q.A) :=
    lamEq_baseChange _ _ (spMap s) F.P₀.A F.P₀.A F'.P₀.A F.P₀.A Q.A Q.A Q'.A Q.A φ φ φ' φ
      hφ.2.1.1.w hφ.2.1.1.w hφ'.2.1 hφ.2.1
      F'.P₀.L F.P₀.L Q'.L Q.L F'.P₀.isLB F.P₀.isLB Q'.isLB Q.isLB hφ'.2.2 hφ.2.2 a₀ b₀ g₀ (𝟙 _) a₁ b₁ g₁ (𝟙 _)
      ea eb eg (by simp) hlam₀
  have hweil := weilEq_of_lamEq hL ℂ Q Q Q' Q a₁ b₁ g₁ (𝟙 _) ha₁ hb₁ hg₁ inferInstance hlam₁
  have hherm := (weilEq_iff_hermForm_eq hU hL Q Q Q' Q u u u' u Hm' Hm χ' χ hA' hA a₁ b₁ g₁ (𝟙 _) Φ₁ Φ₂ G
    LinearMap.id hΦ₁ hΦ₂ hG (fun z => by simp)).1 hweil
  have e₁ := map_comb s hφ.2.1 hφ'.2.1 u u' F.basis.1 F'.basis.1 hW hW' t₁' ea hΦd₁ (da M₁ hM₁ c')
  have e₂ := map_comb s hφ.2.1 hφ'.2.1 u u' F.basis.1 F'.basis.1 hW hW' t₁' eb hΦd₂ (db M₂ hM₂ c)
  have e₃ := map_comb s hφ.2.1 hφ.2.1 u u F.basis.1 F.basis.1 hW hW t₁ eg hGd (dg N hN c')
  rw [form_eq h' s Hm' W' _ hform', form_eq h s Hm W _ hform, ← e₁, ← e₂, ← e₃, hherm, LinearMap.id_apply]

theorem gram_images : ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K]
  [NumberField K] (σ₁ : K →+* ℂ) (A B : PAT H (Sp (𝓞 K))) (FA : GenFib A.pol) (FB : GenFib B.pol)
  (hA : HermFam K (Fin FA.P₀.g → K)) (hB : HermFam K (Fin FB.P₀.g → K)) (f₁ f₂ : A.t.G ⟶ B.t.G)
  (M₁ M₂ : (Fin FA.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K)) (g : 𝓞 E), FA.IsHerm hA → FB.IsHerm hB →
  IsMonHom f₁ → IsMonHom f₂ →
  WeilEq B.t.PP.L f₁ f₂ A.t.PP.L (A.t.act.act g) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) →
  FA.IsDiffOf FB f₁ M₁ → FA.IsDiffOf FB f₂ M₂ → ∀ (τ : 𝓞 E →+* 𝓞 K) (s : K →+* ℂ),
  ∀ c ∈ FA.eigLat A.t.act τ, hB.form s (M₂ c) (M₁ c) = s (τ g : K) * hA.form s c c := by
  intro hU hL E _ _ _ H K _ _ σ₁ A B FA FB hA hB f₁ f₂ M₁ M₂ g hhA hhB hf₁ hf₂ hw hM₁ hM₂ τ s c hc
  obtain ⟨r, hr, he⟩ := GlobalTheory.T.exists_lieRepresentation_eigenLattices K A.pol FA (𝓞 E) A.t.act
  have hg : IsMonHom (A.t.act.act g) := A.t.act.hom _
  have hinj : Function.Injective (σ₁.comp (algebraMap (𝓞 K) K)) :=
    σ₁.injective.comp (FaithfulSMul.algebraMap_injective (𝓞 K) K)
  have hlam := (GlobalTheory.T.cubeLBPairingIso_iff_weilPairingCompatible_over_ring hL (𝓞 K) A.pol A.pol B.pol A.pol f₁ f₂ (A.t.act.act g) (𝟙 _) hf₁ hf₂ hg inferInstance ℂ
    (σ₁.comp (algebraMap (𝓞 K) K))).2 inferInstance hinj hw
  have hf := form_diff_eq_pair hU hL K A.pol FA B.pol FB hA hB f₁ f₂ (A.t.act.act g) M₁ M₂ (r g) hhA hhB hf₁ hf₂ hg
    hlam hM₁ hM₂ (hr _) s c c
  have hev : r g c = (τ g : K) • c := ((he τ c).1.1 hc).2 _
  rw [hf]
  erw [hev]
  rw [HermFam.smul_right]

theorem side (hU : ThetaUnifAV) (hL : Out.Laws) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {K : Type} [Field K] [NumberField K] (σ₁ : K →+* ℂ) (A B : PAT H (Sp (𝓞 K))) (FA : GenFib A.pol)
    (FB : GenFib B.pol) (hA : HermFam K (Fin FA.P₀.g → K)) (hB : HermFam K (Fin FB.P₀.g → K)) {n : ℕ}
    (f : Fin n → (A.t.G ⟶ B.t.G)) (M : Fin n → ((Fin FA.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K)))
    (g : Matrix (Fin n) (Fin n) (𝓞 E)) (τ : 𝓞 E →+* 𝓞 K) (Ω : ℝ) (hhA : FA.IsHerm hA) (hhB : FB.IsHerm hB)
    (hf : ∀ a, IsMonHom (f a))
    (hw : ∀ a b, WeilEq B.t.PP.L (f a) (f b) A.t.PP.L (A.t.act.act (g a b)) (𝟙 _)
      (spMap (σ₁.comp (algebraMap (𝓞 K) K))))
    (hM : ∀ a, FA.IsDiffOf FB (f a) (M a)) (hr : latRank K (FA.eigLat A.t.act τ) = 1)
    (hi : ∀ a, Function.Injective (M a))
    (hind : iSupIndep (fun a => Submodule.span K
      (((FA.eigLat A.t.act τ).map ((M a).restrictScalars (𝓞 K)) : Submodule (𝓞 K) _) : Set (Fin FB.P₀.g → K))))
    (hΩ : 2 * deg hA (FA.eigLat A.t.act τ) = Ω) :
    g.det ≠ 0 ∧ deg hB (⨆ a, (FA.eigLat A.t.act τ).map ((M a).restrictScalars (𝓞 K))) =
      n * (Ω / 2) - Real.log |((Algebra.norm ℚ ((g.det : 𝓞 E) : E) : ℚ) : ℝ)| / (2 * Module.finrank ℚ E) := by
  set y : Matrix (Fin n) (Fin n) K := g.map fun x => (τ x : K) with hy
  have hgr : ∀ (s : K →+* ℂ) a b, ∀ c ∈ FA.eigLat A.t.act τ,
      hB.form s (M b c) (M a c) = s (y a b) * hA.form s c c := fun s a b c hc =>
    gram_images hU hL E H K σ₁ A B FA FB hA hB (f a) (f b) (M a) (M b) (g a b) hhA hhB (hf a) (hf b) (hw a b)
      (hM a) (hM b) τ s c hc
  obtain ⟨hne, hdeg⟩ := GlobalTheory.T.deg_iSup_map_rankOne_lattice_of_gram K _ _ hA hB n M _ y (GlobalTheory.CM.DegBound.eigLat_fg FA A.t.act τ) hr hi hind hgr
  have hdet : y.det = ((τ g.det : 𝓞 K) : K) := by
    rw [hy, show (fun x : 𝓞 E => (τ x : K)) = ⇑((algebraMap (𝓞 K) K).comp τ) from rfl, ← RingHom.mapMatrix_apply,
      ← RingHom.map_det]
    rfl
  refine ⟨fun h0 => hne (by rw [hdet, h0, map_zero]; rfl), ?_⟩
  have hn := GlobalTheory.T.mean_log_norm_embeddings_ringHom_eq E K τ g.det
  rw [hdeg, ← hΩ, hdet]
  have e : (∑ s : K →+* ℂ, Real.log ‖s ((τ g.det : 𝓞 K) : K)‖) / (2 * (Module.finrank ℚ K : ℝ)) =
      Real.log |((Algebra.norm ℚ ((g.det : 𝓞 E) : E) : ℚ) : ℝ)| / (2 * (Module.finrank ℚ E : ℝ)) := by
    rw [mul_comm (2 : ℝ), ← div_div, hn, div_div, mul_comm]
  rw [e]
  ring

theorem deg_images : CMCurve → ThetaUnifAV → Out.Laws → HomExtDvr → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p q : ℕ) (X : CMObj H K ρ σ₁ p q), ∀ [NeZero H.d] (χ : DirichletCharacter ℂ H.d), IsKroneckerChar χ → ∀ gP gQ, IsGram X gP gQ → ∀ (FP : GenFib (X.A true).pol) (FQ : GenFib (X.A false).pol) (FB : GenFib X.B.pol) (MP : Fin p → ((Fin FP.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K))) (MQ : Fin q → ((Fin FQ.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K))), IsDiffs FP FQ FB MP MQ → ∀ (h : HermFam K (Fin FB.P₀.g → K)), FB.IsHerm h → ∀ τ : 𝓞 E →+* 𝓞 K, τ H.rt = ρ → gP.det ≠ 0 ∧ gQ.det ≠ 0 ∧ deg h (subP FP FB MP τ) = p * ((logOm E χ).re / 2) - Real.log |((Algebra.norm ℚ ((gP.det : 𝓞 E) : E) : ℚ) : ℝ)| / (2 * Module.finrank ℚ E) ∧ deg h (subQ FQ FB MQ (τ.comp (H.bar : 𝓞 E →+* 𝓞 E))) = q * ((logOm E χ).re / 2) - Real.log |((Algebra.norm ℚ ((gQ.det : 𝓞 E) : E) : ℚ) : ℝ)| / (2 * Module.finrank ℚ E) := by
  intro hC hU hL hE E _ _ _ H K _ _ ρ σ₁ p q X _ χ hχ gP gQ hG FP FQ FB MP MQ hDf h hh τ hτ
  have hD : DegSt := PureDeg.degSt hC hU hL hE
  obtain ⟨hP, hhP⟩ := (LieMetric.exists_unique_isHerm hU hL K _ FP).1
  obtain ⟨hQ, hhQ⟩ := (LieMetric.exists_unique_isHerm hU hL K _ FQ).1
  have hρ : ρ ≠ 0 := fun h0 => by
    have := X.ρ_sq
    rw [h0] at this
    exact H.d_prime.ne_zero (by simpa using this)
  have hτ' : (τ.comp (H.bar : 𝓞 E →+* 𝓞 E)) H.rt = -ρ := by
    have e : (H.bar : 𝓞 E →+* 𝓞 E) H.rt = -H.rt := by simp
    rw [RingHom.comp_apply, e, map_neg, hτ]
  have hne : -ρ ≠ ρ := fun e => hρ (by
    have : (2 : 𝓞 K) * ρ = 0 := by linear_combination -e
    exact (mul_eq_zero.1 this).resolve_left two_ne_zero)
  let FA : ∀ b, GenFib (X.A b).pol := fun b => Bool.rec (motive := fun b => GenFib (X.A b).pol) FQ FP b
  let M : ∀ j : Fin p ⊕ Fin q, (Fin (FA j.isLeft).P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K) := fun j =>
    Sum.rec (motive := fun j => (Fin (FA j.isLeft).P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K)) MP MQ j
  have hM : ∀ j, (FA j.isLeft).IsDiffOf FB (X.φ j) (M j) := by
    rintro (a | a)
    exacts [hDf.1 a, hDf.2 a]
  obtain ⟨-, -, hinj, hind, -⟩ := Indep.letters_independent hU hL E H K ρ σ₁ p q X FA FB M hM
  have hrP := (GlobalTheory.T.lieAlgebra_eigenDecomposition_CM_signature E H K ρ (X.A true) FP 1 0 X.split X.typeP X.ρ_sq).1 τ
  have hrQ := (GlobalTheory.T.lieAlgebra_eigenDecomposition_CM_signature E H K ρ (X.A false) FQ 0 1 X.split X.typeM X.ρ_sq).1 (τ.comp (H.bar : 𝓞 E →+* 𝓞 E))
  rw [if_pos hτ] at hrP
  rw [if_neg (by rw [hτ']; exact hne)] at hrQ
  have hΩP : 2 * deg hP (FP.eigLat (X.A true).t.act τ) = (logOm E χ).re := by
    have := hD E H χ hχ K ρ (X.A true) X.split X.ρ_sq X.typeP FP hP hhP τ hτ
    rw [← this, Complex.ofReal_re]
  have hΩQ := NumInh.deg_conjugate_type hD hχ X FQ hhQ hτ'
  have hindP := iSupIndep.comp (f := fun a : Fin p => ((Sum.inl a : Fin p ⊕ Fin q), τ)) hind
    (fun a b e => Sum.inl_injective (congrArg Prod.fst e))
  have hindQ := iSupIndep.comp (f := fun a : Fin q => ((Sum.inr a : Fin p ⊕ Fin q), τ.comp (H.bar : 𝓞 E →+* 𝓞 E))) hind
    (fun a b e => Sum.inr_injective (congrArg Prod.fst e))
  obtain ⟨h1, h2⟩ := side hU hL σ₁ (X.A true) X.B FP FB hP h (fun a => phiP X a) MP gP τ _ hhP hh
    (fun a => (X.lin (Sum.inl a)).1) hG.1 hDf.1 hrP (fun a => hinj (Sum.inl a)) hindP hΩP
  obtain ⟨h3, h4⟩ := side hU hL σ₁ (X.A false) X.B FQ FB hQ h (fun a => phiQ X a) MQ gQ
    (τ.comp (H.bar : 𝓞 E →+* 𝓞 E)) _ hhQ hh (fun a => (X.lin (Sum.inr a)).1) hG.2 hDf.2 hrQ
    (fun a => hinj (Sum.inr a)) hindQ hΩQ
  exact ⟨h1, h3, h2, h4⟩

end GlobalTheory.FlatCM.ImageDeg

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeImagesEigenLinesCmUnitaryShimuraObjectStatement
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM GlobalTheory.FlatCM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degree_images_eigenLines_cmUnitaryShimuraObject : CMCurve → ThetaUnifAV → Out.Laws → HomExtDvr → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p q : ℕ) (X : CMObj H K ρ σ₁ p q), ∀ [NeZero H.d] (χ : DirichletCharacter ℂ H.d), IsKroneckerChar χ → ∀ gP gQ, IsGram X gP gQ → ∀ (FP : GenFib (X.A true).pol) (FQ : GenFib (X.A false).pol) (FB : GenFib X.B.pol) (MP : Fin p → ((Fin FP.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K))) (MQ : Fin q → ((Fin FQ.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K))), IsDiffs FP FQ FB MP MQ → ∀ (h : HermFam K (Fin FB.P₀.g → K)), FB.IsHerm h → ∀ τ : 𝓞 E →+* 𝓞 K, τ H.rt = ρ → gP.det ≠ 0 ∧ gQ.det ≠ 0 ∧ deg h (subP FP FB MP τ) = p * ((logOm E χ).re / 2) - Real.log |((Algebra.norm ℚ ((gP.det : 𝓞 E) : E) : ℚ) : ℝ)| / (2 * Module.finrank ℚ E) ∧ deg h (subQ FQ FB MQ (τ.comp (H.bar : 𝓞 E →+* 𝓞 E))) = q * ((logOm E χ).re / 2) - Real.log |((Algebra.norm ℚ ((gQ.det : 𝓞 E) : E) : ℚ) : ℝ)| / (2 * Module.finrank ℚ E) := by
  first | exact @GlobalTheory.FlatCM.ImageDeg.deg_images | exact GlobalTheory.FlatCM.ImageDeg.deg_images | (intros; apply GlobalTheory.FlatCM.ImageDeg.deg_images <;> assumption)
end
end

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM GlobalTheory.FlatCM

noncomputable section

namespace GlobalTheory.FlatCore.CMDiff

theorem latRank_iSup {K V ι : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] (N : ι → Submodule (𝓞 K) V)
    (hi : iSupIndep fun i => Submodule.span K (N i : Set V)) :
    latRank K (⨆ i, N i) = ∑ i, latRank K (N i) := by
  classical
  have hs : Submodule.span K ((⨆ i, N i : Submodule (𝓞 K) V) : Set V) = ⨆ i, Submodule.span K (N i : Set V) := by
    refine le_antisymm (Submodule.span_le.2 ?_) (iSup_le fun i => Submodule.span_mono ?_)
    · have : (⨆ i, N i) ≤ (⨆ i, Submodule.span K (N i : Set V)).restrictScalars (𝓞 K) :=
        iSup_le fun i => fun x hx => (le_iSup (fun i => Submodule.span K (N i : Set V)) i)
          (Submodule.subset_span hx)
      exact this
    · exact SetLike.coe_mono (le_iSup N i)
  unfold latRank
  rw [hs]
  have hinj : Function.Injective (DirectSum.coeLinearMap fun i => Submodule.span K (N i : Set V)) := by
    first
    | exact hi.dfinsupp_lsum_injective
    | exact (iSupIndep_iff_dfinsupp_lsum_injective _).1 hi
    | exact DirectSum.coeLinearMap_injective_of_iSupIndep hi
  rw [← DirectSum.range_coeLinearMap, LinearMap.finrank_range_of_inj hinj, Module.finrank_directSum]

end GlobalTheory.FlatCore.CMDiff

namespace GlobalTheory.FlatCore.CMDiff

end GlobalTheory.FlatCore.CMDiff

end
