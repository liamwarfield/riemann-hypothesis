module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactStandardMaximal

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZeroMemBoxF
noncomputable section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.RedCov.Simple

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def boxF (ρ : ℝ) : Set (AF F) :=
  {a | (∀ w : InfinitePlace F, ‖a.1 w‖ ≤ ρ) ∧ a.2 ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 F) F}

def boxE (ρ : ℝ) : Set (AF F ⊗[F] E) :=
  {x | ∀ k, (Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)).repr x k ∈ boxF F ρ}

end GlobalTheory.CompanionTheory.RedCov.Simple

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactHeightLowerBound
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactHeightLowerBound
set_option maxSynthPendingDepth 1

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.RedCov.Simple
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.RedCov.Simple

theorem exists_one_le_mul_hgt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (D : Set (GAd σ J)), IsCompact D → ∃ P : ℝ, 0 < P ∧ ∀ g ∈ D, ∀ v : Fin n → E, v ≠ 0 → 1 ≤ P * hgt σ J g v := by
  intro F E _ _ _ _ _ σ hCM n J D hD
  obtain ⟨-, -, h2, -⟩ := hCM
  haveI : Algebra.IsQuadraticExtension F E := ⟨h2⟩
  obtain ⟨P, hP, h⟩ := GroundTheory.Automorphic.Reduction.exists_adelicNorm_vecMul_le_mul
    (hD.image (Bridge.continuous_trG σ J).inv)
  refine ⟨P, hP, fun g hg v hv => ?_⟩
  have hc := Bridge.cvec_ne_zero (F := F) hv
  have e : GroundTheory.Automorphic.Reduction.ratVec (Bridge.cvec F v) ᵥ*
        (Bridge.trG σ J g).1 ᵥ* ((Bridge.trG σ J g)⁻¹).1 =
      GroundTheory.Automorphic.Reduction.ratVec (Bridge.cvec F v) := by
    rw [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]
  have h3 : GroundTheory.Automorphic.Reduction.adelicNorm (GroundTheory.Automorphic.Reduction.ratVec (Bridge.cvec F v) ᵥ*
        (Bridge.trG σ J g).1 ᵥ* ((Bridge.trG σ J g)⁻¹).1) ≤
      P * GroundTheory.Automorphic.Reduction.height (Bridge.trG σ J g) (Bridge.cvec F v) :=
    h _ ⟨g, hg, rfl⟩ _ (GroundTheory.Automorphic.Reduction.hasFiniteContent_height (Bridge.trG σ J g) hc)
  rw [e] at h3
  rw [Bridge.hgt_eq]
  exact (GroundTheory.Automorphic.Reduction.one_le_adelicNorm_ratVec hc).trans h3

end GlobalTheory.CompanionTheory.RedCov.Simple

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactHeightLowerBoundStatement
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.RedCov.Simple
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_height_lower_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (D : Set (GAd σ J)), IsCompact D → ∃ P : ℝ, 0 < P ∧ ∀ g ∈ D, ∀ v : Fin n → E, v ≠ 0 → 1 ≤ P * hgt σ J g v := by
  first | exact @GlobalTheory.CompanionTheory.RedCov.Simple.exists_one_le_mul_hgt | exact GlobalTheory.CompanionTheory.RedCov.Simple.exists_one_le_mul_hgt | (intros; apply GlobalTheory.CompanionTheory.RedCov.Simple.exists_one_le_mul_hgt <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactAdelicNormBounded
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactAdelicNormBounded
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.RedCov.Simple
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
open IsDedekindDomain

noncomputable section

namespace GlobalTheory.CompanionTheory.RedCov.Simple.NormBound

open GroundTheory.Automorphic.Reduction

theorem finprod_le_prod_of_le {α : Type*} {f b : α → ℝ} (S : Finset α) (h0 : ∀ a, 0 ≤ f a)
    (hS : ∀ a ∈ S, f a ≤ b a) (hb : ∀ a ∈ S, 1 ≤ b a) (h1 : ∀ a, a ∉ S → f a ≤ 1) :
    ∏ᶠ a, f a ≤ ∏ a ∈ S, b a := by
  classical
  have hone : (1 : ℝ) ≤ ∏ a ∈ S, b a := by
    have := Finset.prod_le_prod₀ (s := S) (f := fun _ => (1 : ℝ)) (g := b)
      (fun _ _ => zero_le_one) hb
    simpa using this
  by_cases hf : (Function.mulSupport f).Finite
  · set c : α → ℝ := fun a => if a ∈ S then b a else 1 with hc
    have hcs : Function.mulSupport c ⊆ (S : Set α) := fun a ha => by
      by_contra h
      exact ha (by simp only [hc]; exact if_neg fun h' => h (Finset.mem_coe.2 h'))
    have hcf : (Function.mulSupport c).Finite := S.finite_toSet.subset hcs
    have hle : ∏ᶠ a, f a ≤ ∏ᶠ a, c a :=
      finprod_le_finprod_of_nonneg hf hcf h0 fun a => by
        simp only [hc]
        split_ifs with h
        · exact hS a h
        · exact h1 a h
    rw [finprod_eq_prod_of_mulSupport_subset c hcs] at hle
    refine hle.trans (le_of_eq (Finset.prod_congr rfl fun a ha => ?_))
    simp only [hc]
    rw [if_pos ha]
  · rw [finprod_of_infinite_mulSupport hf]
    exact hone

variable {F : Type} [Field F] [NumberField F] {N : ℕ}

def integralOutside (S : Finset (HeightOneSpectrum (𝓞 F))) : Set (Fin N → AF F) :=
  {y | ∀ i, ∀ v, v ∉ S → (y i).2 v ∈ v.adicCompletionIntegers F}

theorem isOpen_integralOutside (S : Finset (HeightOneSpectrum (𝓞 F))) :
    IsOpen (integralOutside (N := N) S) := by
  have h := RestrictedProduct.isOpen_forall_imp_mem
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (fun v => Valued.isOpen_valuationSubring _) (p := fun v => v ∉ S)
  have h2 : IsOpen {a : AF F | ∀ v, v ∉ S → a.2 v ∈ v.adicCompletionIntegers F} :=
    h.preimage continuous_snd
  have : integralOutside (N := N) S = ⋂ i : Fin N, (fun y : Fin N → AF F => y i) ⁻¹'
      {a : AF F | ∀ v, v ∉ S → a.2 v ∈ v.adicCompletionIntegers F} := by
    ext y
    simp only [integralOutside, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
  rw [this]
  exact isOpen_iInter_of_finite fun i => h2.preimage (continuous_apply i)

theorem exists_mem_integralOutside (y : Fin N → AF F) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), y ∈ integralOutside S := by
  have h : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ∀ i, (y i).2 v ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.2 fun i => (y i).2.2
  have hfin := Filter.eventually_cofinite.1 h
  refine ⟨hfin.toFinset, fun i v hv => ?_⟩
  by_contra hc
  exact hv (hfin.mem_toFinset.2 fun h' => hc (h' i))

theorem exists_finset_subset_integralOutside {D : Set (Fin N → AF F)} (hD : IsCompact D) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), D ⊆ integralOutside S := by
  classical
  obtain ⟨T, hT⟩ := hD.elim_finite_subcover
    (fun S : Finset (HeightOneSpectrum (𝓞 F)) => integralOutside (N := N) S)
    isOpen_integralOutside (fun y _ => by
      obtain ⟨S, hS⟩ := exists_mem_integralOutside y
      exact Set.mem_iUnion.2 ⟨S, hS⟩)
  refine ⟨T.sup id, fun y hy i v hv => ?_⟩
  obtain ⟨S, hS, hyS⟩ := Set.mem_iUnion₂.1 (hT hy)
  exact hyS i v fun h => hv (Finset.mem_sup.2 ⟨S, hS, h⟩)

theorem norm_finComp_le_one {y : Fin N → AF F} {v : HeightOneSpectrum (𝓞 F)}
    (h : ∀ i, (y i).2 v ∈ v.adicCompletionIntegers F) : ‖finComp v y‖ ≤ 1 :=
  (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i =>
    (Valued.toNormedField.norm_le_one_iff).2
      ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (h i))

theorem continuous_euclidNorm_infComp (w : InfinitePlace F) :
    Continuous fun y : Fin N → AF F => euclidNorm (infComp w y) :=
  continuous_euclidNorm.comp (continuous_pi fun i =>
    (continuous_apply w).comp (continuous_fst.comp (continuous_apply i)))

theorem continuous_norm_finComp (v : HeightOneSpectrum (𝓞 F)) :
    Continuous fun y : Fin N → AF F => ‖finComp v y‖ :=
  (continuous_pi fun i => (RestrictedProduct.continuous_eval v).comp
    (continuous_snd.comp (continuous_apply i))).norm

end GlobalTheory.CompanionTheory.RedCov.Simple.NormBound

namespace GlobalTheory.CompanionTheory.RedCov.Simple


open GroundTheory.Automorphic.Reduction NormBound in
theorem exists_adelicNorm_le_of_isCompact :
    ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) (D : Set (Fin N → AF F)), IsCompact D →
      ∃ P : ℝ, 0 < P ∧ ∀ y ∈ D, GroundTheory.Automorphic.Reduction.adelicNorm y ≤ P := by
  intro F _ _ N D hD
  classical
  obtain ⟨S, hS⟩ := exists_finset_subset_integralOutside hD
  choose a ha1 ha using fun w : InfinitePlace F =>
    exists_one_le_bound hD (continuous_euclidNorm_infComp (N := N) w)
  choose b hb1 hb using fun v : HeightOneSpectrum (𝓞 F) =>
    exists_one_le_bound hD (continuous_norm_finComp (N := N) v)
  have hA : (1 : ℝ) ≤ ∏ w, a w ^ w.mult := by
    have := Finset.prod_le_prod₀ (s := Finset.univ) (f := fun _ : InfinitePlace F => (1 : ℝ))
      (g := fun w => a w ^ w.mult) (fun _ _ => zero_le_one)
      (fun w _ => one_le_pow₀ (ha1 w))
    simpa using this
  have hB : (1 : ℝ) ≤ ∏ v ∈ S, b v := by
    have := Finset.prod_le_prod₀ (s := S) (f := fun _ => (1 : ℝ)) (g := b)
      (fun _ _ => zero_le_one) (fun v _ => hb1 v)
    simpa using this
  refine ⟨(∏ w, a w ^ w.mult) * ∏ v ∈ S, b v, by positivity, fun y hy => ?_⟩
  refine mul_le_mul ?_ ?_ (finprod_nonneg fun _ => norm_nonneg _) (by positivity)
  · exact Finset.prod_le_prod₀ (fun w _ => pow_nonneg (euclidNorm_nonneg _) _)
      fun w _ => pow_le_pow_left₀ (euclidNorm_nonneg _) (ha w y hy) _
  · exact finprod_le_prod_of_le S (fun _ => norm_nonneg _) (fun v _ => hb v y hy)
      (fun v _ => hb1 v) fun v hv => norm_finComp_le_one fun i => hS hy i v hv

end GlobalTheory.CompanionTheory.RedCov.Simple

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactAdelicNormBoundedStatement
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.RedCov.Simple
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_adelic_norm_bounded : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) (D : Set (Fin N → AF F)), IsCompact D → ∃ P : ℝ, 0 < P ∧ ∀ y ∈ D, GroundTheory.Automorphic.Reduction.adelicNorm y ≤ P := by
  first | exact @GlobalTheory.CompanionTheory.RedCov.Simple.exists_adelicNorm_le_of_isCompact | exact GlobalTheory.CompanionTheory.RedCov.Simple.exists_adelicNorm_le_of_isCompact | (intros; apply GlobalTheory.CompanionTheory.RedCov.Simple.exists_adelicNorm_le_of_isCompact <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicBoxCompact
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicBoxCompact
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.RedCov.Simple
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.RedCov.Simple.BoxCpt

theorem properSpace_completion (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) :
    ProperSpace w.Completion := by
  have hi := NumberField.InfinitePlace.Completion.isometry_extensionEmbedding w
  have hce := hi.isClosedEmbedding
  refine ⟨fun x r => ?_⟩
  have e : Metric.closedBall x r = NumberField.InfinitePlace.Completion.extensionEmbedding w ⁻¹'
      Metric.closedBall (NumberField.InfinitePlace.Completion.extensionEmbedding w x) r := by
    ext y
    simp [Metric.mem_closedBall, hi.dist_eq]
  rw [e]
  exact hce.isCompact_preimage (isCompact_closedBall _ _)

theorem isCompact_boxF_one (F : Type) [Field F] [NumberField F] : IsCompact (boxF F 1) := by
  have h1 : IsCompact (Set.univ.pi fun w : InfinitePlace F => Metric.closedBall (0 : w.Completion) 1) := by
    haveI : ∀ w : InfinitePlace F, ProperSpace w.Completion := fun w => properSpace_completion F w
    exact isCompact_univ_pi fun w => isCompact_closedBall 0 1
  have h2 := GroundTheory.Global.isCompact_integralFiniteAdeles F
  have e : boxF F 1 = (Set.univ.pi fun w : InfinitePlace F => Metric.closedBall (0 : w.Completion) 1) ×ˢ
      (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) := by
    ext a
    simp only [boxF, Set.mem_setOf_eq]
    change _ ↔ (a.1 ∈ (Set.univ.pi fun w : InfinitePlace F => Metric.closedBall (0 : w.Completion) 1) ∧
      a.2 ∈ (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)))
    refine and_congr ⟨fun h => Set.mem_univ_pi.mpr fun w => ?_, fun h w => ?_⟩ Iff.rfl
    · simpa [Metric.mem_closedBall, dist_zero_right] using h w
    · simpa [Metric.mem_closedBall, dist_zero_right] using Set.mem_univ_pi.mp h w
  rw [e]
  exact h1.prod h2

theorem isCompact_boxE_one (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    IsCompact (boxE F E 1) := by
  set b := Algebra.TensorProduct.basis (AF F) (Module.finBasis F E) with hb
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (AF F ⊗[F] E) := IsModuleTopology.toContinuousAdd (AF F) _
  haveI : ContinuousSMul (AF F) (AF F ⊗[F] E) := inferInstance
  have hK : IsCompact (Set.univ.pi fun _ : Fin (Module.finrank F E) => boxF F 1) :=
    isCompact_univ_pi fun _ => isCompact_boxF_one F
  have hc : Continuous
      ((b.equivFun.symm : (Fin (Module.finrank F E) → AF F) →ₗ[AF F] AF F ⊗[F] E)) :=
    IsModuleTopology.continuous_of_linearMap _
  have e : boxE F E 1 = b.equivFun.symm '' (Set.univ.pi fun _ => boxF F 1) := by
    ext x
    simp only [boxE, Set.mem_setOf_eq, Set.mem_image, Set.mem_univ_pi, ← hb]
    constructor
    · intro hx
      exact ⟨b.equivFun x, fun k => by rw [Module.Basis.equivFun_apply]; exact hx k,
        b.equivFun.symm_apply_apply x⟩
    · rintro ⟨y, hy, rfl⟩ k
      have h : b.repr (b.equivFun.symm y) k = y k := by
        rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
      rw [h]
      exact hy k
  rw [e]
  exact hK.image hc

theorem main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    IsCompact (boxF F 1) ∧ IsCompact (boxE F E 1) := by
  intro F E _ _ _ _ _
  exact ⟨isCompact_boxF_one F, isCompact_boxE_one F E⟩

end GlobalTheory.CompanionTheory.RedCov.Simple.BoxCpt

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicBoxCompactStatement
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.RedCov.Simple
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_box_compact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], IsCompact (boxF F 1) ∧ IsCompact (boxE F E 1) := by
  first | exact @GlobalTheory.CompanionTheory.RedCov.Simple.BoxCpt.main | exact GlobalTheory.CompanionTheory.RedCov.Simple.BoxCpt.main | (intros; apply GlobalTheory.CompanionTheory.RedCov.Simple.BoxCpt.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicTensorRationalApproximation
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicTensorRationalApproximation
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.RedCov.Simple
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.RedCov.Simple.Dirichlet

theorem exists_nsmul_sub_mem {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    (S : AddSubgroup G) (K : Set G) (hK : IsCompact K) (hcov : ∀ x, ∃ γ ∈ S, x - γ ∈ K)
    (V : Set G) (hV : V ∈ nhds (0 : G)) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ b : G, ∃ q : ℕ, 1 ≤ q ∧ q ≤ N ∧ ∃ γ ∈ S, q • b - γ ∈ V := by
  open scoped Pointwise in
  obtain ⟨W, hWo, hW0, hWV⟩ := exists_open_nhds_zero_half hV
  set U : Set G := W ∩ -W with hUdef
  have hUo : IsOpen U := hWo.inter hWo.neg
  have hU0 : (0 : G) ∈ U := ⟨hW0, by simpa using hW0⟩
  have hUV : ∀ v ∈ U, ∀ w ∈ U, v - w ∈ V := by
    intro v hv w hw
    rw [sub_eq_add_neg]
    exact hWV v hv.1 (-w) (by simpa using hw.2)
  obtain ⟨t, ht⟩ := compact_covered_by_add_left_translates (V := U) hK
    (by rw [hUo.interior_eq]; exact ⟨0, hU0⟩)
  refine ⟨t.card + 1, le_add_self, fun b => ?_⟩
  have hx : ∀ m : Fin (t.card + 2), ∃ γ ∈ S, ∃ g ∈ t, g + (((m : ℕ) + 1) • b - γ) ∈ U := by
    intro m
    obtain ⟨γ, hγ, hγK⟩ := hcov (((m : ℕ) + 1) • b)
    have := ht hγK
    simp only [Set.mem_iUnion, Set.mem_preimage] at this
    obtain ⟨g, hg, hgU⟩ := this
    exact ⟨γ, hγ, g, hg, hgU⟩
  choose γ hγ g hg hgU using hx
  obtain ⟨i, j, hij, hg_eq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun m : Fin (t.card + 2) => (⟨g m, hg m⟩ : t)) (by simp)
  simp only [Subtype.mk.injEq] at hg_eq
  have key : ∀ i j : Fin (t.card + 2), (i : ℕ) < j → g i = g j →
      ∃ q : ℕ, 1 ≤ q ∧ q ≤ t.card + 1 ∧ ∃ γ' ∈ S, q • b - γ' ∈ V := by
    intro i j hlt hgij
    refine ⟨(j : ℕ) - i, by omega, by omega, γ j - γ i, S.sub_mem (hγ j) (hγ i), ?_⟩
    have h := hUV _ (hgU j) _ (hgU i)
    have e : (j : ℕ) + 1 = ((j : ℕ) - i) + ((i : ℕ) + 1) := by omega
    rw [e, add_nsmul, hgij] at h
    convert h using 1
    abel
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
  · exact key i j h hg_eq
  · exact key j i h hg_eq.symm

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem boxF_mem_nhds {ε : ℝ} (hε : 0 < ε) : boxF F ε ∈ nhds (0 : AF F) := by
  have hopen : IsOpen ({a : AF F | (∀ w : InfinitePlace F, ‖a.1 w‖ < ε)} ∩
      {a : AF F | a.2 ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 F) F}) := by
    refine IsOpen.inter ?_ ?_
    · simp only [Set.ofPred_forall]
      exact isOpen_iInter_of_finite fun w =>
        isOpen_lt (continuous_norm.comp ((continuous_apply w).comp continuous_fst)) continuous_const
    · exact GroundTheory.Global.isOpen_integralFiniteAdeles.preimage continuous_snd
  refine Filter.mem_of_superset (hopen.mem_nhds ⟨fun w => ?_, (zero_mem (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F) : _)⟩) ?_
  · show ‖(0 : AF F).1 w‖ < ε
    rw [show (0 : AF F).1 w = 0 from rfl, norm_zero]; exact hε
  · rintro a ⟨h1, h2⟩
    exact ⟨fun w => (h1 w).le, h2⟩

theorem repr_inclR (c : E) (k : Fin (Module.finrank F E)) :
    (Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)).repr (inclR (F := F) (AF F) c) k =
      algebraMap F (AF F) ((Module.finBasis F E).repr c k) := by
  have : inclR (F := F) (AF F) c = (1 : AF F) ⊗ₜ[F] c := rfl
  rw [this, Algebra.TensorProduct.basis_repr_tmul]
  simp

theorem exists_compact_pi (d : ℕ) :
    ∃ K : Set (Fin d → AF F), IsCompact K ∧ ∀ x : Fin d → AF F, ∃ f : Fin d → F,
      (x - fun k => algebraMap F (AF F) (f k)) ∈ K := by
  obtain ⟨C, hC, hx⟩ := GroundTheory.Global.exists_isCompact_forall_exists_sub_mem F
  refine ⟨Set.univ.pi fun _ => C ×ˢ (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set _),
    isCompact_univ_pi fun _ => hC.prod (GroundTheory.Global.isCompact_integralFiniteAdeles F), fun x => ?_⟩
  choose f hf using fun k => hx (x k)
  exact ⟨f, fun k _ => hf k⟩

theorem dirichlet (ε : ℝ) (hε : 0 < ε) : ∃ N : ℕ, 1 ≤ N ∧ ∀ b : AF F ⊗[F] E, ∃ q : ℕ, 1 ≤ q ∧ q ≤ N ∧
    ∃ c : E, (q : AF F ⊗[F] E) * b - inclR (F := F) (AF F) c ∈ boxE F E ε := by
  set d := Module.finrank F E
  let S : AddSubgroup (Fin d → AF F) :=
    (AddMonoidHom.compLeft (algebraMap F (AF F)).toAddMonoidHom (Fin d)).range
  obtain ⟨K, hK, hcov⟩ := exists_compact_pi F d
  have hV : (Set.univ.pi fun _ : Fin d => boxF F ε) ∈ nhds (0 : Fin d → AF F) :=
    set_pi_mem_nhds Set.finite_univ fun _ _ => boxF_mem_nhds F hε
  obtain ⟨N, hN, hb⟩ := exists_nsmul_sub_mem S K hK
    (fun x => by
      obtain ⟨f, hf⟩ := hcov x
      exact ⟨_, ⟨f, rfl⟩, hf⟩) _ hV
  refine ⟨N, hN, fun b => ?_⟩
  set B := Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)
  obtain ⟨q, hq1, hqN, γ, ⟨f, rfl⟩, hmem⟩ := hb (fun k => B.repr b k)
  refine ⟨q, hq1, hqN, (Module.finBasis F E).equivFun.symm f, fun k => ?_⟩
  have hk := hmem k (Set.mem_univ _)
  rw [← nsmul_eq_mul, map_sub, map_nsmul, Finsupp.sub_apply, Finsupp.smul_apply, repr_inclR]
  have hc : (Module.finBasis F E).repr ((Module.finBasis F E).equivFun.symm f) k = f k := by
    have := congrFun ((Module.finBasis F E).equivFun.apply_symm_apply f) k
    rwa [Module.Basis.equivFun_apply] at this
  rw [hc]
  simpa using hk

end GlobalTheory.CompanionTheory.RedCov.Simple.Dirichlet

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicTensorRationalApproximationStatement
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.RedCov.Simple
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_tensor_rational_approximation : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (ε : ℝ), 0 < ε → ∃ N : ℕ, 1 ≤ N ∧ ∀ b : AF F ⊗[F] E, ∃ q : ℕ, 1 ≤ q ∧ q ≤ N ∧ ∃ c : E, (q : AF F ⊗[F] E) * b - inclR (F := F) (AF F) c ∈ boxE F E ε := by
  first | exact @GlobalTheory.CompanionTheory.RedCov.Simple.Dirichlet.dirichlet | exact GlobalTheory.CompanionTheory.RedCov.Simple.Dirichlet.dirichlet | (intros; apply GlobalTheory.CompanionTheory.RedCov.Simple.Dirichlet.dirichlet <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReductionTheoryLowerBound
set_option linter.unusedSectionVars false

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open PositivityTheory.ThKEst (rId)
open PositivityTheory.ThKEst.Sieg (rId_add rId_zero' rId_snd rId_inf)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.RedCov.Simple

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ}

theorem ratV_sub (u v : Fin n → E) : ratV F (u - v) = ratV F u - ratV F v :=
  funext fun i => map_sub (inclR (F := F) (AF F)) _ _

theorem ratV_smul (c : E) (v : Fin n → E) : ratV F (c • v) = inclR (F := F) (AF F) c • ratV F v :=
  funext fun i => map_mul (inclR (F := F) (AF F)) _ _

theorem mulVec_col {m : ℕ} {M : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)} {X : Matrix (Fin n) (Fin m) E}
    {B : Matrix (Fin m) (Fin m) (AF F ⊗[F] E)} (hB : M * adMat F X = adMat F X * B) (j : Fin m) :
    M *ᵥ ratV F (Xᵀ j) = ∑ i, B i j • ratV F (Xᵀ i) := by
  funext k
  have e := congrFun (congrFun hB k) j
  simp only [Matrix.mul_apply] at e
  simp only [mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Eq.trans e (Finset.sum_congr rfl fun i _ => ?_)
  exact mul_comm _ _

theorem adelicNorm_rId [IsTotallyReal F] {N : ℕ} (c : ℝ) (y : Fin N → AF F) :
    GroundTheory.Automorphic.Reduction.adelicNorm (rId F c • y) =
      Real.exp (Module.finrank ℚ F * c) * GroundTheory.Automorphic.Reduction.adelicNorm y := by
  have hm : ∀ w : InfinitePlace F, w.mult = 1 := fun w => by
    rw [InfinitePlace.mult, if_pos (IsTotallyReal.isReal w)]
  have hw : ∀ w : InfinitePlace F, ‖(rId F c).1 w‖ = Real.exp c := fun w => norm_evInf_rId w c
  have hv : ∀ v, GroundTheory.Automorphic.Reduction.finComp v (rId F c • y) = GroundTheory.Automorphic.Reduction.finComp v y := fun v => by
    rw [GroundTheory.Automorphic.Reduction.finComp_smul, rId_snd]
    exact one_smul _ _
  simp only [GroundTheory.Automorphic.Reduction.adelicNorm, GroundTheory.Automorphic.Reduction.infComp_smul,
    GroundTheory.Automorphic.Reduction.euclidNorm_smul, hw, hm, pow_one, hv]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, card_infinitePlace, ← Real.exp_nat_mul, mul_assoc]

theorem hv_rId [IsTotallyReal F] (c : ℝ) (ξ : Fin n → AF F ⊗[F] E) :
    hv (algebraMap (AF F) (AF F ⊗[F] E) (rId F c) • ξ) = Real.exp (Module.finrank ℚ F * c) * hv ξ := by
  unfold hv
  rw [← adelicNorm_rId]
  congr 1
  funext p
  simp only [Pi.smul_apply, algebraMap_smul, map_smul, Finsupp.smul_apply]

theorem matHom_mul_val (g h : GAd σ J) :
    (matHom _ σ J (g * h)).1 = (matHom _ σ J g).1 * (matHom _ σ J h).1 := by
  rw [map_mul, Units.val_mul]

variable {X Y : Matrix (Fin n) (Fin (r + 1)) E} {a : (Fin (r + 1) → ℝ) → GAd σ J}

theorem torus_col (ha : IsTorus σ J X Y a) (t : Fin (r + 1) → ℝ) (i : Fin (r + 1)) :
    (matHom _ σ J (a t)).1 *ᵥ ratV F (Xᵀ i) = algebraMap (AF F) (AF F ⊗[F] E) (rId F (t i)) • ratV F (Xᵀ i) := by
  rw [mulVec_col (ha.onX t) i, Finset.sum_eq_single i]
  · rw [Matrix.diagonal_apply_eq]
  · intro k _ hk
    rw [Matrix.diagonal_apply_ne _ hk, zero_smul]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem torus_inv (ha : IsTorus σ J X Y a) (s : Fin (r + 1) → ℝ) : (a s)⁻¹ = a (-s) := by
  have h0 : a 0 = 1 := by
    have e := ha.add 0 0
    rw [add_zero] at e
    exact mul_left_cancel (e.symm.trans (mul_one _).symm)
  exact inv_eq_of_mul_eq_one_right (by rw [← ha.add, add_neg_cancel, h0])

theorem par_col_zero {M : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)} {B : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)}
    (hB : B.BlockTriangular id) (e : M * adMat F X = adMat F X * B) :
    M *ᵥ ratV F (Xᵀ 0) = B 0 0 • ratV F (Xᵀ 0) := by
  rw [mulVec_col e 0, Finset.sum_eq_single 0]
  · intro k _ hk
    rw [hB (show id (0 : Fin (r + 1)) < id k from Fin.pos_of_ne_zero hk), zero_smul]
  · intro hi
    exact absurd (Finset.mem_univ 0) hi

theorem par_col_one {M : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)} {B : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)}
    (hB : B.BlockTriangular id) (e : M * adMat F X = adMat F X * B) {j : Fin (r + 1)} (hj : j.val = 1) :
    M *ᵥ ratV F (Xᵀ j) = B 0 j • ratV F (Xᵀ 0) + B j j • ratV F (Xᵀ j) := by
  have hj0 : (0 : Fin (r + 1)) ≠ j := fun h => by rw [← h] at hj; simp at hj
  rw [mulVec_col e j, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin (r + 1))),
    Finset.sum_eq_single_of_mem j (Finset.mem_erase.2 ⟨hj0.symm, Finset.mem_univ _⟩)]
  intro k hk hkj
  have hk0 : k ≠ 0 := (Finset.mem_erase.1 hk).1
  have : j < k := by
    have h1 : k.val ≠ 0 := fun h => hk0 (Fin.ext h)
    have h2 : k.val ≠ 1 := fun h => hkj (Fin.ext (h.trans hj.symm))
    exact Fin.lt_def.2 (by omega)
  rw [hB (show id j < id k from this), zero_smul]

theorem hgt_line [IsTotallyReal F] (ha : IsTorus σ J X Y a) {ω : GAd σ J} (hω : ω⁻¹ ∈ minPar σ J X)
    (s : Fin (r + 1) → ℝ) (κ : GAd σ J) (e : E) :
    hgt σ J (ω * a s * κ) (e • Xᵀ 0) =
      Real.exp (Module.finrank ℚ F * (-s 0)) * hgt σ J (ω * κ) (e • Xᵀ 0) := by
  obtain ⟨B, hB, eB⟩ := hω
  have h1 := par_col_zero hB eB
  have h2 := torus_col ha (-s) 0
  have e1 : (ω * a s * κ)⁻¹ = κ⁻¹ * a (-s) * ω⁻¹ := by
    rw [← torus_inv ha]; group
  have e2 : (ω * κ)⁻¹ = κ⁻¹ * ω⁻¹ := by group
  unfold hgt
  rw [← hv_rId, e1, e2, matHom_mul_val, matHom_mul_val, matHom_mul_val, ratV_smul, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_smul, h1, Matrix.mulVec_smul, Matrix.mulVec_smul,
    Matrix.mulVec_smul, h2, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul]
  simp only [Pi.neg_apply]
  simp only [smul_smul]
  congr 1
  ring

theorem hgt_pair [IsTotallyReal F] (ha : IsTorus σ J X Y a) {ω : GAd σ J}
    {B : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)} (hB : B.BlockTriangular id)
    (eB : (matHom _ σ J ω⁻¹).1 * adMat F X = adMat F X * B) (s : Fin (r + 1) → ℝ) (κ : GAd σ J)
    {j : Fin (r + 1)} (hj : j.val = 1) (q : ℕ) (c : E) {b : AF F ⊗[F] E} (hb : B 0 0 * b = B 0 j) (t : ℝ) :
    hgt σ J (ω * a s * κ) ((q : E) • Xᵀ j - c • Xᵀ 0) =
      Real.exp (Module.finrank ℚ F * t) * hv ((matHom _ σ J κ⁻¹).1 *ᵥ
        ((B 0 0 * (algebraMap (AF F) (AF F ⊗[F] E) (rId F (-s 0 - t)) *
            ((q : AF F ⊗[F] E) * b - inclR (F := F) (AF F) c))) • ratV F (Xᵀ 0) +
          (B j j * algebraMap (AF F) (AF F ⊗[F] E) ((q : AF F) * rId F (-s j - t))) • ratV F (Xᵀ j))) := by
  have h1 := par_col_zero hB eB
  have h2 := par_col_one hB eB hj
  have h3 := torus_col ha (-s) 0
  have h4 := torus_col ha (-s) j
  have e1 : (ω * a s * κ)⁻¹ = κ⁻¹ * a (-s) * ω⁻¹ := by
    rw [← torus_inv ha]; group
  have hq : inclR (F := F) (AF F) (q : E) = (q : AF F ⊗[F] E) := map_natCast _ q
  have hR : ∀ x y : ℝ, algebraMap (AF F) (AF F ⊗[F] E) (rId F (x + y)) =
      algebraMap (AF F) (AF F ⊗[F] E) (rId F x) * algebraMap (AF F) (AF F ⊗[F] E) (rId F y) := fun x y => by
    rw [rId_add, map_mul]
  have r0 : algebraMap (AF F) (AF F ⊗[F] E) (rId F (-s 0)) =
      algebraMap (AF F) (AF F ⊗[F] E) (rId F t) * algebraMap (AF F) (AF F ⊗[F] E) (rId F (-s 0 - t)) := by
    rw [← hR]; congr 2; ring
  have r1 : algebraMap (AF F) (AF F ⊗[F] E) (rId F (-s j)) =
      algebraMap (AF F) (AF F ⊗[F] E) (rId F t) * algebraMap (AF F) (AF F ⊗[F] E) (rId F (-s j - t)) := by
    rw [← hR]; congr 2; ring
  have s1 : (matHom _ σ J ω⁻¹).1 *ᵥ ratV F ((q : E) • Xᵀ j - c • Xᵀ 0) =
      (B 0 0 * ((q : AF F ⊗[F] E) * b - inclR (F := F) (AF F) c)) • ratV F (Xᵀ 0) +
        ((q : AF F ⊗[F] E) * B j j) • ratV F (Xᵀ j) := by
    rw [ratV_sub, ratV_smul, ratV_smul, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, h1, h2, hq, ← hb]
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  unfold hgt
  rw [← hv_rId, e1, matHom_mul_val, matHom_mul_val, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, s1, Matrix.mulVec_add,
    Matrix.mulVec_smul, Matrix.mulVec_smul, h3, h4, ← Matrix.mulVec_smul]
  congr 2
  simp only [Pi.neg_apply, r0, r1, map_mul, map_natCast]
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem rId_mul_mem_boxF [IsTotallyReal F] {c ε ρ : ℝ} (h : Real.exp c * ε ≤ ρ) {y : AF F} (hy : y ∈ boxF F ε) :
    rId F c * y ∈ boxF F ρ := by
  refine ⟨fun w => ?_, ?_⟩
  · have e : (rId F c * y).1 w = (rId F c).1 w * y.1 w := rfl
    rw [e, norm_mul, show ‖(rId F c).1 w‖ = Real.exp c from norm_evInf_rId w c]
    exact (mul_le_mul_of_nonneg_left (hy.1 w) (Real.exp_pos c).le).trans h
  · have e : (rId F c * y).2 = y.2 := by
      rw [show (rId F c * y).2 = (rId F c).2 * y.2 from rfl, rId_snd, one_mul]
    rw [e]
    exact hy.2

theorem rId_mul_mem_boxE [IsTotallyReal F] {c ε ρ : ℝ} (h : Real.exp c * ε ≤ ρ) {y : AF F ⊗[F] E} (hy : y ∈ boxE F E ε) :
    algebraMap (AF F) (AF F ⊗[F] E) (rId F c) * y ∈ boxE F E ρ := fun k => by
  rw [← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul]
  exact rId_mul_mem_boxF h (hy k)

theorem natCast_mem_boxF (q : ℕ) : (q : AF F) ∈ boxF F q := by
  refine ⟨fun w => ?_, ?_⟩
  · have e : (q : AF F).1 w = (q : w.Completion) := rfl
    rw [e, ← (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _), map_natCast]
    simp
  · exact natCast_mem _ q

theorem continuous_coordVec : Continuous fun ξ : Fin n → AF F ⊗[F] E =>
    (fun p : Fin (Fintype.card (Fin n × Fin (Module.finrank F E))) =>
      (Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)).repr
        (ξ ((Fintype.equivFin (Fin n × Fin (Module.finrank F E))).symm p).1)
        ((Fintype.equivFin (Fin n × Fin (Module.finrank F E))).symm p).2) := by
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  refine continuous_pi fun p => ?_
  exact (IsModuleTopology.continuous_of_linearMap
    ((Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)).coord _)).comp (continuous_apply _)

theorem upper_bound (h : IsCMExt F E σ) (x₁ x₂ : Fin n → E) {A₁ A₂ : Set (AF F ⊗[F] E)} (hA₁ : IsCompact A₁)
    (hA₂ : IsCompact A₂) {C : Set (GAd σ J)} (hC : IsCompact C) :
    ∃ P : ℝ, 0 < P ∧ ∀ κ ∈ C, ∀ α₁ ∈ A₁, ∀ α₂ ∈ A₂, ∀ ζ ∈ boxE F E 1, ∀ z ∈ boxF F 1,
      hv ((matHom _ σ J κ⁻¹).1 *ᵥ ((α₁ * ζ) • ratV F x₁ + (α₂ * algebraMap (AF F) (AF F ⊗[F] E) z) • ratV F x₂)) ≤ P := by
  have := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  obtain ⟨hbF, hbE⟩ := GlobalTheory.T.adelic_box_compact F E
  have hcA : Continuous (algebraMap (AF F) (AF F ⊗[F] E)) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (AF F) (AF F ⊗[F] E))
  let Φ : GAd σ J × (AF F ⊗[F] E) × (AF F ⊗[F] E) × (AF F ⊗[F] E) × AF F → Fin n → AF F ⊗[F] E := fun t =>
    (matHom _ σ J t.1⁻¹).1 *ᵥ ((t.2.1 * t.2.2.2.1) • ratV F x₁ + (t.2.2.1 * algebraMap (AF F) (AF F ⊗[F] E) t.2.2.2.2) • ratV F x₂)
  have hΦ : Continuous Φ := by
    refine ((continuous_matHom_val (σ := σ) (J := J)).comp (continuous_inv.comp continuous_fst)).matrix_mulVec ?_
    refine continuous_pi fun i => ?_
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    fun_prop
  have hK := (hC.prod (hA₁.prod (hA₂.prod (hbE.prod hbF)))).image (continuous_coordVec.comp hΦ)
  obtain ⟨P, hP, hle⟩ := GlobalTheory.T.compact_adelic_norm_bounded F _ _ hK
  exact ⟨P, hP, fun κ hκ α₁ h₁ α₂ h₂ ζ hζ z hz =>
    hle _ ⟨(κ, α₁, α₂, ζ, z), ⟨hκ, h₁, h₂, hζ, hz⟩, rfl⟩⟩

open scoped Pointwise in
theorem simple_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsWittFrame σ J X Y → ∀ a, IsTorus σ J X Y a → ∀ (Ω C : Set (GAd σ J)), IsCompact Ω → Ω ⊆ minParOne σ J X → IsCompact C → ∃ M : ℝ, 0 < M ∧ ∀ ω ∈ Ω, ∀ s : Fin (r + 1) → ℝ, ∀ κ ∈ C, ∀ e : E, e ≠ 0 → NearMin σ J (ω * a s * κ) (e • Xᵀ 0) → ∀ j : Fin (r + 1), j.val = 1 → Real.exp (s j) ≤ M * Real.exp (s 0) := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW a ha Ω C hΩ hΩ1 hC
  haveI := h.1
  by_cases hr : ∃ j : Fin (r + 1), j.val = 1
  swap
  · exact ⟨1, one_pos, fun ω _ s κ _ e _ _ j hj => absurd ⟨j, hj⟩ hr⟩
  obtain ⟨j, hj⟩ := hr
  have hF := pfrA h hJ hW
  have := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  have hBc : Continuous fun p : GAd σ J => Bm σ J X Y p⁻¹ := continuous_Bm.comp continuous_inv
  have hA₁ : IsCompact ((fun p : GAd σ J => Bm σ J X Y p⁻¹ 0 0) '' Ω) := hΩ.image (hBc.matrix_elem 0 0)
  have hA₂ : IsCompact ((fun p : GAd σ J => Bm σ J X Y p⁻¹ j j) '' Ω) := hΩ.image (hBc.matrix_elem j j)
  obtain ⟨P, hP, hlow⟩ := GlobalTheory.T.compact_height_lower_bound F E σ h n J (Ω * C) (hΩ.mul hC)
  obtain ⟨P₄, hP₄, hup⟩ := upper_bound h (Xᵀ 0) (Xᵀ j) hA₁ hA₂ hC
  obtain ⟨K, hKdef⟩ : ∃ K, K = 2 * P * P₄ := ⟨_, rfl⟩
  have hK : 0 < K := by rw [hKdef]; positivity
  obtain ⟨ε, hεdef⟩ : ∃ ε, ε = 1 / (K + 1) := ⟨_, rfl⟩
  have hε : 0 < ε := by rw [hεdef]; positivity
  have hε1 : ε ≤ 1 := by
    rw [hεdef, div_le_one (by positivity)]
    linarith
  obtain ⟨d, hd⟩ : ∃ d, d = Module.finrank ℚ F := ⟨_, rfl⟩
  have hd0 : d ≠ 0 := by rw [hd]; exact Module.finrank_pos.ne'
  have hKε : K * ε ^ d < 1 := by
    have h1 : ε ^ d ≤ ε := pow_le_of_le_one hε.le hε1 hd0
    calc K * ε ^ d ≤ K * ε := mul_le_mul_of_nonneg_left h1 hK.le
      _ = K / (K + 1) := by rw [hεdef]; ring
      _ < 1 := by rw [div_lt_one (by positivity)]; linarith
  obtain ⟨N, hN1, hN⟩ := GlobalTheory.T.adelic_tensor_rational_approximation F E ε hε
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  refine ⟨(K + 1) * N, by positivity, ?_⟩
  intro ω hω s κ hκ e he hNM j' hj'
  rw [show j' = j from Fin.ext (hj'.trans hj.symm)]
  have m1 : ω ∈ minPar σ J X := minParOne_subset (hΩ1 hω)
  have m2 : ω⁻¹ ∈ minPar σ J X := inv_mem_minPar h hJ hW m1
  obtain ⟨hBt, eB⟩ := (mem_minPar_iff hF).1 m2
  obtain ⟨hBt', -⟩ := (mem_minPar_iff hF).1 m1
  have hu1 : Bm σ J X Y ω⁻¹ 0 0 * Bm σ J X Y ω 0 0 = 1 := by
    rw [← diag_mul_bt hBt hBt', ← Bm_mul hF m2 m1, inv_mul_cancel, Bm_one hF, Matrix.one_apply_eq]
  have hb : Bm σ J X Y ω⁻¹ 0 0 * (Bm σ J X Y ω⁻¹ 0 j * Bm σ J X Y ω 0 0) = Bm σ J X Y ω⁻¹ 0 j := by
    rw [mul_left_comm, hu1, mul_one]
  obtain ⟨q, hq1, hqN, c, hc⟩ := hN (Bm σ J X Y ω⁻¹ 0 j * Bm σ J X Y ω 0 0)
  have hq0 : (q : E) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)

  have hj0 : j ≠ 0 := fun e0 => by rw [e0] at hj; simp at hj
  have hyx : cT (σ : E →+* E) Y * J * X = 1 :=
    PFr.yx (s := (σ : E →+* E)) (Jm := J) (Xm := X) (Ym := Y)
      ⟨fun x => sigma_sigma h x, Matrix.ext fun i k => hJ.1 i k, hW.xx, hW.yy, hW.xy⟩
  have hcol : ∀ i k, ((cT (σ : E →+* E) Y * J) *ᵥ Xᵀ i) k = (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) k i := fun i k => by
    rw [← hyx]; rfl
  have hu0 : (q : E) • Xᵀ j - c • Xᵀ 0 ≠ 0 := fun h0 => by
    have e1 := congrFun (congrArg (fun v => (cT (σ : E →+* E) Y * J) *ᵥ v) h0) j
    simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_zero, Pi.sub_apply, Pi.smul_apply, hcol, smul_eq_mul,
      Matrix.one_apply_eq, Matrix.one_apply_ne hj0, mul_one, mul_zero, sub_zero, Pi.zero_apply] at e1
    exact hq0 e1
  let Bf := toLinearMapₛₗ₂' E (σ : E →+* E) (RingHom.id E) J
  have hBf : ∀ u v, Bf u v = ∑ i, ∑ j, σ (u i) * J i j * v j := fun u v => by
    simp only [Bf, toLinearMapₛₗ₂'_apply, smul_eq_mul, RingHom.id_apply, RingHom.coe_coe]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hg : ∀ i k, Bf (Xᵀ i) (Xᵀ k) = 0 := fun i k => by
    have e1 := gram_apply (σ := σ) (J := J) X X i k
    rw [hW.xx] at e1
    exact e1.symm
  have hiso : hE σ J ((q : E) • Xᵀ j - c • Xᵀ 0) ((q : E) • Xᵀ j - c • Xᵀ 0) = 0 := by
    refine (hBf _ _).symm.trans ?_
    simp only [map_sub, map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply, hg, smul_zero, mul_zero, sub_zero]
  have hNM' := hNM.2.2 _ hu0 hiso

  obtain ⟨A, hAdef⟩ : ∃ A, A = Real.exp (-s 0) := ⟨_, rfl⟩
  obtain ⟨D, hDdef⟩ : ∃ D, D = Real.exp (-s j) := ⟨_, rfl⟩
  have hA : 0 < A := hAdef ▸ Real.exp_pos _
  have hD : 0 < D := hDdef ▸ Real.exp_pos _
  obtain ⟨T, hTdef⟩ : ∃ T, T = max (ε * A) (N * D) := ⟨_, rfl⟩
  have hT1 : ε * A ≤ T := hTdef ▸ le_max_left _ _
  have hT2 : N * D ≤ T := hTdef ▸ le_max_right _ _
  have hT : 0 < T := lt_of_lt_of_le (by positivity) hT1
  have hexp : ∀ x : ℝ, Real.exp (x - Real.log T) = Real.exp x / T := fun x => by
    rw [Real.exp_sub, Real.exp_log hT]
  have hζ := rId_mul_mem_boxE (c := -s 0 - Real.log T) (ρ := 1) (by
    rw [hexp, ← hAdef, div_mul_eq_mul_div, div_le_one hT, mul_comm]; exact hT1) hc
  have hz : (q : AF F) * rId F (-s j - Real.log T) ∈ boxF F 1 := by
    rw [mul_comm]
    refine rId_mul_mem_boxF ?_ (natCast_mem_boxF q)
    rw [hexp, ← hDdef, div_mul_eq_mul_div, div_le_one hT, mul_comm]
    exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hqN) hD.le).trans hT2
  have hup' := hup κ hκ _ ⟨ω, hω, rfl⟩ _ ⟨ω, hω, rfl⟩ _ hζ _ hz
  have e1 := hgt_pair ha hBt eB s κ hj q c hb (Real.log T)
  have e2 := hgt_line ha m2 s κ e
  have hl := hlow (ω * κ) (Set.mul_mem_mul hω hκ) (e • Xᵀ 0) hNM.1
  rw [← hd] at e1 e2
  have eT : Real.exp (d * Real.log T) = T ^ d := by rw [Real.exp_nat_mul, Real.exp_log hT]
  have eA : Real.exp (d * (-s 0)) = A ^ d := by rw [Real.exp_nat_mul, hAdef]
  rw [eT] at e1
  rw [eA] at e2
  have hmain : A ^ d ≤ K * T ^ d := by
    calc A ^ d ≤ A ^ d * (P * hgt σ J (ω * κ) (e • Xᵀ 0)) := le_mul_of_one_le_right (by positivity) hl
      _ = P * hgt σ J (ω * a s * κ) (e • Xᵀ 0) := by rw [e2]; ring
      _ ≤ P * (2 * hgt σ J (ω * a s * κ) ((q : E) • Xᵀ j - c • Xᵀ 0)) := mul_le_mul_of_nonneg_left hNM' hP.le
      _ ≤ P * (2 * (T ^ d * P₄)) := by
          rw [e1]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hup' (by positivity))
            (by norm_num)) hP.le
      _ = K * T ^ d := by rw [hKdef]; ring
  rcases le_total (N * D) (ε * A) with hc1 | hc1
  · exfalso
    have eT' : T = ε * A := by rw [hTdef, max_eq_left hc1]
    rw [eT', mul_pow] at hmain
    have hAd : 0 < A ^ d := by positivity
    nlinarith
  · have eT' : T = N * D := by rw [hTdef, max_eq_right hc1]
    have h3 : A ≤ (K + 1) * N * D := by
      have h4 : K ≤ (K + 1) ^ d := by
        have : K + 1 ≤ (K + 1) ^ d := le_self_pow₀ (by linarith) hd0
        linarith
      have h5 : A ^ d ≤ ((K + 1) * N * D) ^ d := by
        rw [eT'] at hmain
        rw [mul_assoc, mul_pow]
        exact hmain.trans (mul_le_mul_of_nonneg_right h4 (by positivity))
      exact (pow_le_pow_iff_left₀ hA.le (by positivity) hd0).1 h5
    have e3 : A * Real.exp (s 0) = 1 := by rw [hAdef, ← Real.exp_add]; simp
    have e4 : D * Real.exp (s j) = 1 := by rw [hDdef, ← Real.exp_add]; simp
    calc Real.exp (s j) = Real.exp (s j) * (A * Real.exp (s 0)) := by rw [e3, mul_one]
      _ ≤ Real.exp (s j) * ((K + 1) * N * D * Real.exp (s 0)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le) (Real.exp_pos _).le
      _ = (K + 1) * N * Real.exp (s 0) * (D * Real.exp (s j)) := by ring
      _ = (K + 1) * N * Real.exp (s 0) := by rw [e4, mul_one]

end GlobalTheory.CompanionTheory.RedCov.Simple

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReductionTheoryLowerBoundStatement
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reduction_theory_lower_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsWittFrame σ J X Y → ∀ a, IsTorus σ J X Y a → ∀ (Ω C : Set (GAd σ J)), IsCompact Ω → Ω ⊆ minParOne σ J X → IsCompact C → ∃ M : ℝ, 0 < M ∧ ∀ ω ∈ Ω, ∀ s : Fin (r + 1) → ℝ, ∀ κ ∈ C, ∀ e : E, e ≠ 0 → NearMin σ J (ω * a s * κ) (e • Xᵀ 0) → ∀ j : Fin (r + 1), j.val = 1 → Real.exp (s j) ≤ M * Real.exp (s 0) := by
  first | exact @GlobalTheory.CompanionTheory.RedCov.Simple.simple_bound | exact GlobalTheory.CompanionTheory.RedCov.Simple.simple_bound | (intros; apply GlobalTheory.CompanionTheory.RedCov.Simple.simple_bound <;> assumption)
end
