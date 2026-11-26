module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Formalism.LocalToGlobal.HermitianForms.TiedSym
public import Formalism.LocalToGlobal.GroupLattices.DownNaturalLevelZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsSummableMajorantRationalVectorsLocallyUnif
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsSummableMajorantRationalVectorsLocallyUnif
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal

noncomputable section
namespace GlobalTheory.SumMaj
open scoped Classical
variable {F : Type} [Field F] [NumberField F] {N : ℕ}

theorem re_add (x y : Ainf F) (w : InfinitePlace F) : re (x + y) w = re x w + re y w := by
  show (InfinitePlace.Completion.extensionEmbedding w (x w + y w)).re = _
  rw [map_add (f := _), Complex.add_re]; rfl

theorem abs_re_algebraMap (hF : IsTotallyReal F) (x : F) (w : InfinitePlace F) :
    |re (algebraMap F (Ainf F) x) w| = w x := by
  unfold re
  have hw : w.IsReal := hF.isReal w
  rw [InfiniteAdeleRing.algebraMap_apply]
  rw [InfinitePlace.Completion.extensionEmbedding_coe]
  rw [← InfinitePlace.embedding_of_isReal_apply hw, Complex.ofReal_re]
  first
  | (rw [← Real.norm_eq_abs]; exact InfinitePlace.norm_embedding_of_isReal hw x)
  | simpa [Real.norm_eq_abs] using InfinitePlace.norm_embedding_of_isReal hw x

theorem sz_nonneg (u : Fin N → AF F) : 0 ≤ sz u :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem sz_sub_le (u y : Fin N → AF F) : sz u - sz y ≤ sz (u + y) := by
  unfold sz
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun l _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun w _ => ?_
  have h : re (inf (u + y) l) w = re (inf u l) w + re (inf y l) w := by
    rw [← re_add]; congr 1
  rw [h]
  have := abs_sub_abs_le_abs_sub (re (inf u l) w) (-(re (inf y l) w))
  simpa [abs_neg, sub_neg_eq_add] using this

theorem continuous_sz : Continuous (sz : (Fin N → AF F) → ℝ) := by
  unfold sz
  refine continuous_finsetSum _ fun l _ => continuous_finsetSum _ fun w _ => ?_
  have h1 : Continuous fun u : Fin N → AF F => inf u l := by
    show Continuous fun u : Fin N → AF F => (u l).1
    exact continuous_fst.comp (continuous_apply l)
  have h2 : Continuous fun x : Ainf F => re x w :=
    Complex.continuous_re.comp ((InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp
      (continuous_apply w))
  exact continuous_abs.comp (h2.comp h1)

theorem continuous_fin : Continuous (fin : (Fin N → AF F) → Fin N → Af F) := by
  refine continuous_pi fun l => ?_
  show Continuous fun u : Fin N → AF F => (u l).2
  exact continuous_snd.comp (continuous_apply l)

theorem fin_add (u y : Fin N → AF F) : fin (u + y) = fin u + fin y := by
  funext l; simp [fin, map_add (f := _)]

theorem inf_rat (ξ : Fin N → F) (l : Fin N) : inf (rat ξ) l = algebraMap F (Ainf F) (ξ l) := by
  simp [inf, rat]

theorem fin_rat (ξ : Fin N → F) (l : Fin N) : fin (rat ξ) l = algebraMap F (Af F) (ξ l) := by
  simp [fin, rat]

theorem norm_le_sz (hF : IsTotallyReal F) (ξ : Fin N → F) :
    ‖(fun l => mixedEmbedding F (ξ l))‖ ≤ sz (rat ξ) := by
  refine (pi_norm_le_iff_of_nonneg (sz_nonneg _)).2 fun l => ?_
  classical
  rw [mixedEmbedding.norm_eq_sup'_normAtPlace]
  refine Finset.sup'_le _ _ fun w _ => ?_
  rw [mixedEmbedding.normAtPlace_apply]
  unfold sz
  calc w (ξ l) = |re (inf (rat ξ) l) w| := by rw [inf_rat, abs_re_algebraMap hF]
    _ ≤ ∑ w', |re (inf (rat ξ) l) w'| :=
        Finset.single_le_sum (f := fun w' => |re (inf (rat ξ) l) w'|) (fun _ _ => abs_nonneg _)
          (Finset.mem_univ w)
    _ ≤ _ := Finset.single_le_sum (f := fun l' => ∑ w', |re (inf (rat ξ) l') w'|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ l)

theorem finrank_le_of_discrete {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] : Module.finrank ℤ L ≤ Module.finrank ℝ E := by
  let E' := Submodule.span ℝ (L : Set E)
  let L' : Submodule ℤ E' := ZLattice.comap ℝ L E'.subtype
  haveI : DiscreteTopology L' :=
    ZLattice.comap_discreteTopology _ _ (by fun_prop) Subtype.val_injective
  haveI : IsZLattice ℝ L' :=
    ⟨Submodule.map_injective_of_injective E'.subtype_injective (by simp [E', L'])⟩
  let e : L' ≃ₗ[ℤ] L := Submodule.comapSubtypeEquivOfLe (p := L) (q := E'.restrictScalars ℤ)
    Submodule.subset_span
  rw [← e.finrank_eq, ZLattice.rank ℝ L']
  exact Submodule.finrank_le E'

end GlobalTheory.SumMaj

namespace GlobalTheory.SumMaj
open scoped Classical

theorem summable_majorant : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ), IsTotallyReal F →
    ∀ K : Set (Fin N → Af F), IsCompact K → ∃ k : ℕ, ∀ ω : Set (Fin N → AF F), IsCompact ω →
      ∃ c : (Fin N → F) → ℝ, Summable c ∧ (∀ ξ, 0 ≤ c ξ) ∧
        ∀ ξ, ∀ y ∈ ω, fin (rat ξ + y) ∈ K → 1 ≤ c ξ * (1 + sz (rat ξ + y)) ^ k := by
  intro F _ _ N hF K hK
  refine ⟨Module.finrank ℝ (Fin N → mixedEmbedding.mixedSpace F) + 1, fun ω hω => ?_⟩
  set k := Module.finrank ℝ (Fin N → mixedEmbedding.mixedSpace F) + 1 with hk
  obtain ⟨B, hB⟩ := hω.bddAbove_image (continuous_sz (F := F) (N := N)).continuousOn
  set B0 := max B 0 with hB0
  have hB0n : 0 ≤ B0 := le_max_right _ _
  have hszB : ∀ y ∈ ω, sz y ≤ B0 := fun y hy => (hB ⟨y, hy, rfl⟩).trans (le_max_left _ _)
  set K' : Set (Fin N → Af F) := (fun p : (Fin N → Af F) × (Fin N → Af F) => p.1 - p.2) '' (K ×ˢ (fin '' ω))
    with hK'
  have hK'c : IsCompact K' :=
    (hK.prod (hω.image continuous_fin)).image (continuous_fst.sub continuous_snd)
  obtain ⟨M, hM0, hM⟩ := GlobalTheory.WeilM.exists_nat_mul_integral_of_isCompact F hK'c
  set S : Set (Fin N → F) := {ξ | fin (rat ξ) ∈ K'} with hS
  set c : (Fin N → F) → ℝ := S.indicator fun ξ => (1 + B0) ^ k / (1 + sz (rat ξ)) ^ k with hc
  have hc0 : ∀ ξ, 0 ≤ c ξ := fun ξ =>
    Set.indicator_nonneg (fun ξ _ => div_nonneg (pow_nonneg (by linarith) _)
      (pow_nonneg (by linarith [sz_nonneg (rat ξ)]) _)) ξ
  refine ⟨c, ?_, hc0, fun ξ y hy hξ => ?_⟩
  · haveI := GlobalTheory.WeilM.discreteTopology_denomLattice F (Fin N) hM0
    set L := GlobalTheory.WeilM.denomLattice F (Fin N) M with hL
    have memL : ∀ ξ ∈ S, (fun i => mixedEmbedding F (ξ i)) ∈ L := by
      intro ξ hξ i
      obtain ⟨y, hy⟩ := (GlobalTheory.IntegralFinAdele.integral_finiteAdele_properties F).2.2.2.1 ((M : F) * ξ i)
        fun v => by
          rw [map_mul, map_natCast]
          have := hM _ hξ i v
          rwa [fin_rat] at this
      refine ⟨y, ?_⟩
      have h2 := congrArg (mixedEmbedding F) hy
      rw [← nsmul_eq_mul, map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ] at h2
      exact h2.symm
    let j : S → L := fun ξ => ⟨_, memL ξ.1 ξ.2⟩
    have hj : Function.Injective j := fun a b h => Subtype.ext (funext fun i =>
      mixedEmbedding_injective F (congrFun (congrArg Subtype.val h) i))
    have hkL : Module.finrank ℤ L < k := Nat.lt_succ_of_le (finrank_le_of_discrete L)
    have hg : Summable fun z : L => ((1 + ‖z‖) ^ k)⁻¹ := by
      refine Summable.of_norm_bounded_eventually (ZLattice.summable_norm_pow_inv L k hkL) ?_
      refine (Set.finite_singleton (0 : L)).subset fun z hz => ?_
      by_contra h0
      apply hz
      show ‖((1 + ‖z‖) ^ k)⁻¹‖ ≤ ‖z‖⁻¹ ^ k
      have hz0 : 0 < ‖z‖ := norm_pos_iff.2 h0
      rw [Real.norm_of_nonneg (inv_nonneg.2 (pow_nonneg (by positivity) _)), inv_pow]
      exact inv_anti₀ (pow_pos hz0 _) (pow_le_pow_left₀ hz0.le (by linarith) _)
    refine ((Subtype.val_injective (p := fun ξ => ξ ∈ S)).summable_iff ?_).1 ?_
    · intro ξ hξ
      have : ξ ∉ S := fun h => hξ ⟨⟨ξ, h⟩, rfl⟩
      exact Set.indicator_of_notMem this _
    · refine Summable.of_nonneg_of_le (fun ξ => hc0 _) (fun ξ => ?_) ((hg.comp_injective hj).mul_left ((1 + B0) ^ k))
      show c ξ.1 ≤ (1 + B0) ^ k * ((1 + ‖j ξ‖) ^ k)⁻¹
      rw [hc, Set.indicator_of_mem ξ.2, div_eq_mul_inv]
      refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (by linarith) _)
      have hn : ‖j ξ‖ ≤ sz (rat ξ.1) := norm_le_sz hF ξ.1
      exact inv_anti₀ (pow_pos (by positivity) _) (pow_le_pow_left₀ (by positivity) (by linarith) _)
  · have hS' : ξ ∈ S := by
      refine ⟨(fin (rat ξ + y), fin y), ⟨hξ, y, hy, rfl⟩, ?_⟩
      simp [fin_add]
    rw [hc, Set.indicator_of_mem hS']
    have hs0 := sz_nonneg (rat ξ)
    have ht0 := sz_nonneg (rat ξ + y)
    have hst := sz_sub_le (rat ξ) y
    have hy0 := hszB y hy
    have key : 1 + sz (rat ξ) ≤ (1 + B0) * (1 + sz (rat ξ + y)) := by nlinarith
    rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos (by linarith) _), one_mul, ← mul_pow]
    exact pow_le_pow_left₀ (by linarith) key _

end GlobalTheory.SumMaj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsSummableMajorantRationalVectorsLocallyUnifStatement
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_summableMajorant_rationalVectors_locallyUniform : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ), IsTotallyReal F → ∀ K : Set (Fin N → Af F), IsCompact K → ∃ k : ℕ, ∀ ω : Set (Fin N → AF F), IsCompact ω → ∃ c : (Fin N → F) → ℝ, Summable c ∧ (∀ ξ, 0 ≤ c ξ) ∧ ∀ ξ, ∀ y ∈ ω, fin (rat ξ + y) ∈ K → 1 ≤ c ξ * (1 + sz (rat ξ + y)) ^ k := by
  first | exact @GlobalTheory.SumMaj.summable_majorant | exact GlobalTheory.SumMaj.summable_majorant | (intros; apply GlobalTheory.SumMaj.summable_majorant <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentTypeLevelCharacterFiniteOrderRootsOfUni
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelCharacterNoBlocksPthRootOfUnity
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelCharacterNoBlocksPthRootOfUnity
open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace GlobalTheory

theorem lamJ_zero_blocks_mem_range_and_pow_eq_one :
    ∀ (k K : Type) [Field k] [Field K] (s : K →+* ℂ) (p : ℕ), p.Prime → (p : k) = 0 → (∃ ζ : K, IsPrimitiveRoot ζ p) → ∀ (n : ℕ) (ψ : AddChar k ℂ) (χ : ℕ → MulChar k ℂ) (a t skip : ℕ) (M : Matrix (Fin n) (Fin n) k), (∃ r : K, s r = lamJ ψ χ a t 0 skip M) ∧ lamJ ψ χ a t 0 skip M ^ p = 1 := by
  intro k K _ _ s p hp hk ⟨ζ, hζ⟩ n ψ χ a t skip M
  have hψ : ∀ x : k, ψ x ^ p = 1 := fun x => by
    rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, hk, zero_mul, AddChar.map_zero_eq_one]
  have h : lamJ ψ χ a t 0 skip M ^ p = 1 := by
    unfold Formalism.L2.Forms.lamJ
    simp [hψ]
  exact ⟨complex_rootOfUnity_mem_range_of_isPrimitiveRoot K s p ζ hp.pos hζ _ h, h⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelCharacterNoBlocksPthRootOfUnityStatement
open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_character_no_blocks_pth_root_of_unity : ∀ (k K : Type) [Field k] [Field K] (s : K →+* ℂ) (p : ℕ), p.Prime → (p : k) = 0 → (∃ ζ : K, IsPrimitiveRoot ζ p) → ∀ (n : ℕ) (ψ : AddChar k ℂ) (χ : ℕ → MulChar k ℂ) (a t skip : ℕ) (M : Matrix (Fin n) (Fin n) k), (∃ r : K, s r = lamJ ψ χ a t 0 skip M) ∧ lamJ ψ χ a t 0 skip M ^ p = 1 := by
  first | exact @GlobalTheory.lamJ_zero_blocks_mem_range_and_pow_eq_one | exact GlobalTheory.lamJ_zero_blocks_mem_range_and_pow_eq_one | (intros; apply GlobalTheory.lamJ_zero_blocks_mem_range_and_pow_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentTypeLevelCharacterFiniteOrderRootsOfUni
open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace GlobalTheory

theorem natCast_residueField_completion_eq_zero (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (p : ℕ) (h : (p : 𝓞 F) ∈ v.asIdeal) : (p : kv F v) = 0 := by
  rw [← map_natCast (IsLocalRing.residue (v.adicCompletionIntegers F)), IsLocalRing.residue_eq_zero_iff]
  refine (Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (v.adicCompletion F) _))
    (a := (p : v.adicCompletionIntegers F))).2 ?_
  have h1 : ((p : v.adicCompletionIntegers F) : v.adicCompletion F) =
      algebraMap F (v.adicCompletion F) ((p : 𝓞 F) : F) := by
    simp
  rw [h1]
  have h2 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v ((p : 𝓞 F) : F)
  have h3 := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) v (p : 𝓞 F)).2 h
  exact h2.trans_lt h3

theorem unipotent_type_character_finite_order : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (S : StepLevel F E σ J T f bad) (gp : Fin 2 → ℕ) (G : GLoc F E σ gp) (a t skip fc : ℕ) (zl : Bool) (_ : GLev S G a t 0 skip fc zl) (K : Type) [Field K] (s : K →+* ℂ), (∀ i, (gp i).Prime) → (∀ i, ∃ ζ : K, IsPrimitiveRoot ζ (gp i)) → ∃ N : ℕ, 0 < N ∧ ∀ x : S.U, ((S.chi x : ℂˣ) : ℂ) ^ N = 1 ∧ ∃ r : K, s r = ((S.chi x : ℂˣ) : ℂ) := by
  intro F E _ _ _ _ _ σ n J T f bad S gp G a t skip fc zl L K _ s hp hζ
  refine ⟨gp 0 * gp 1, Nat.mul_pos (hp 0).pos (hp 1).pos, fun x => ?_⟩
  rw [L.chi_eq x]
  let P : ℂ → Prop := fun z => z ^ (gp 0 * gp 1) = 1 ∧ ∃ r : K, s r = z
  have h1 : P 1 := ⟨one_pow _, 1, map_one s⟩
  have hm : ∀ y z, P y → P z → P (y * z) := by
    rintro y z ⟨hy, r, rfl⟩ ⟨hz, q, rfl⟩
    exact ⟨by rw [mul_pow, hy, hz, one_mul], r * q, map_mul s r q⟩
  change P _
  refine Finset.prod_induction _ P hm h1 fun i _ => ?_
  refine finprod_induction P h1 hm fun v => ?_
  refine finprod_induction P h1 hm fun h => ?_
  obtain ⟨⟨r, hr⟩, hpow⟩ := GlobalTheory.T.level_character_no_blocks_pth_root_of_unity (kv F v) K s (gp i) (hp i)
    (natCast_residueField_completion_eq_zero F v (gp i) h) (hζ i) n (G.psi0 i v h) (G.chiB i v h) a t skip
    (redM F v (G.mat i v h (L.fr i v h) (bc (prV (E := E) v) x.1)))
  refine ⟨?_, r⁻¹, by rw [map_inv₀, hr]⟩
  have hd : gp i ∣ gp 0 * gp 1 := by
    fin_cases i
    · exact dvd_mul_right _ _
    · exact dvd_mul_left _ _
  obtain ⟨c, hc⟩ := hd
  rw [inv_pow, hc, pow_mul, hpow, one_pow, inv_one]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentTypeLevelCharacterFiniteOrderRootsOfUniStatement
open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotentTypeLevel_character_finiteOrder_rootsOfUnity : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (S : StepLevel F E σ J T f bad) (gp : Fin 2 → ℕ) (G : GLoc F E σ gp) (a t skip fc : ℕ) (zl : Bool) (_ : GLev S G a t 0 skip fc zl) (K : Type) [Field K] (s : K →+* ℂ), (∀ i, (gp i).Prime) → (∀ i, ∃ ζ : K, IsPrimitiveRoot ζ (gp i)) → ∃ N : ℕ, 0 < N ∧ ∀ x : S.U, ((S.chi x : ℂˣ) : ℂ) ^ N = 1 ∧ ∃ r : K, s r = ((S.chi x : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.unipotent_type_character_finite_order | exact GlobalTheory.unipotent_type_character_finite_order | (intros; apply GlobalTheory.unipotent_type_character_finite_order <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CardResidueFieldTotallyRealTypePrime
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CardResidueFieldTotallyRealTypePrime
open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace GlobalTheory.SplitResidueCard

theorem absNorm_eq_of_ncard {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime)
    (h : {v : HeightOneSpectrum (𝓞 E) | ((p : ℕ) : 𝓞 E) ∈ v.asIdeal}.ncard = Module.finrank ℚ E)
    {w : Ideal (𝓞 E)} (hwp : w.IsPrime) (hw : ((p : ℕ) : 𝓞 E) ∈ w) :
    Ideal.absNorm w = p := by
  classical
  obtain ⟨hc, -⟩ := Formalism.MainNotions.ModuliIntegralCharts.H1.GSplit.split_of_ncard hp h
  set I : Ideal (𝓞 E) := Ideal.span {((p : ℕ) : 𝓞 E)} with hI
  have hI0 : I ≠ ⊥ := by
    rw [hI, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  set M := UniqueFactorizationMonoid.normalizedFactors I with hM
  have hN : Ideal.absNorm I = p ^ Module.finrank ℚ E := by
    rw [hI, Ideal.absNorm_span_singleton]
    have : ((p : ℕ) : 𝓞 E) = algebraMap ℤ (𝓞 E) (p : ℤ) := by simp
    rw [this, Algebra.norm_algebraMap, RingOfIntegers.rank]
    simp
  have hprod : M.prod = I := Ideal.prod_normalizedFactors_eq_self hI0
  have hge : ∀ P ∈ M, p ≤ Ideal.absNorm P := by
    intro P hP
    obtain ⟨hPp, hIP⟩ := (Ideal.mem_normalizedFactors_iff hI0).1 hP
    have hd : Ideal.absNorm P ∣ p ^ Module.finrank ℚ E := hN ▸ Ideal.absNorm_dvd_absNorm_of_le hIP
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 hd
    have h1 : Ideal.absNorm P ≠ 1 := by rw [Ne, Ideal.absNorm_eq_one_iff]; exact hPp.ne_top
    rw [hj] at h1 ⊢
    exact Nat.le_self_pow (by rintro rfl; simp at h1) p
  have hwM : w ∈ M := (Ideal.mem_normalizedFactors_iff hI0).2
    ⟨hwp, by rw [hI, Ideal.span_singleton_le_iff_mem]; exact hw⟩
  refine le_antisymm ?_ (hge _ hwM)
  obtain ⟨M', hM'⟩ := Multiset.exists_cons_of_mem hwM
  have h2 : p ^ M'.card ≤ (M'.map Ideal.absNorm).prod := by
    have := Multiset.pow_card_le_prod (s := M'.map Ideal.absNorm) (a := p) (fun x hx => by
      obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.1 hx
      exact hge P (hM' ▸ Multiset.mem_cons_of_mem hP))
    simpa using this
  have h3 : Ideal.absNorm w * (M'.map Ideal.absNorm).prod = p * p ^ M'.card := by
    rw [← pow_succ', ← Multiset.card_cons w, ← hM', hc, ← hN, ← hprod, hM', Multiset.prod_cons, map_mul,
      map_multiset_prod]
  by_contra hlt
  push Not at hlt
  have hpos : 0 < p ^ M'.card := pow_pos hp.pos _
  nlinarith

theorem card_quotient_of_ncard {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {p : ℕ} (hp : p.Prime)
    (h : {v : HeightOneSpectrum (𝓞 E) | ((p : ℕ) : 𝓞 E) ∈ v.asIdeal}.ncard = Module.finrank ℚ E)
    (v : HeightOneSpectrum (𝓞 F)) (hv : ((p : ℕ) : 𝓞 F) ∈ v.asIdeal) :
    Nat.card (𝓞 F ⧸ v.asIdeal) = p := by
  have := v.isPrime
  have := v.isMaximal
  obtain ⟨w, hwm, hwo⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
  have hw : ((p : ℕ) : 𝓞 E) ∈ w := by
    have h1 : ((p : ℕ) : 𝓞 F) ∈ w.under (𝓞 F) := by rw [← hwo.over]; exact hv
    simpa using (show algebraMap (𝓞 F) (𝓞 E) (p : 𝓞 F) ∈ w from h1)
  have hN : Nat.card (𝓞 E ⧸ w) = p := by
    rw [← absNorm_eq_of_ncard hp h hwm.isPrime hw, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hd : Nat.card (𝓞 F ⧸ v.asIdeal) ∣ p := by
    rw [← hN]
    exact AddSubgroup.card_dvd_of_injective (algebraMap (𝓞 F ⧸ v.asIdeal) (𝓞 E ⧸ w)).toAddMonoidHom
      (FaithfulSMul.algebraMap_injective (𝓞 F ⧸ v.asIdeal) (𝓞 E ⧸ w))
  refine ((Nat.dvd_prime hp).1 hd).resolve_left fun h1 => ?_
  have := (Nat.card_eq_one_iff_unique.1 h1).1
  exact not_subsingleton (𝓞 F ⧸ v.asIdeal) this

theorem card_kv : ∀ (D : D7) (i : Fin 2) (v : HeightOneSpectrum (𝓞 D.host.F)), (D.host.g i : 𝓞 D.host.F) ∈ v.asIdeal → Nat.card (kv D.host.F v) = D.host.g i := by
  intro D i v hv
  rw [← card_quotient_of_ncard (D.host.g_prime i) (D.nd.g_split i) v hv]
  have h := Formalism.UG.P.tjcosets_card_residue v
  rw [h]
  simp [qV, Ideal.absNorm_apply, Submodule.cardQuot_apply]

end GlobalTheory.SplitResidueCard
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CardResidueFieldTotallyRealTypePrimeStatement
open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_residue_field_totally_real_type_prime : ∀ (D : D7) (i : Fin 2) (v : HeightOneSpectrum (𝓞 D.host.F)), (D.host.g i : 𝓞 D.host.F) ∈ v.asIdeal → Nat.card (kv D.host.F v) = D.host.g i := by
  first | exact @GlobalTheory.SplitResidueCard.card_kv | exact GlobalTheory.SplitResidueCard.card_kv | (intros; apply GlobalTheory.SplitResidueCard.card_kv <;> assumption)
end
end
