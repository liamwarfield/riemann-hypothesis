module

public import GroundTheory.GlobalFields.FirstInequality
public import GroundTheory.GlobalFields.KummerTheory.KummerIndexLemma

@[expose] public section

section -- merged from GroundTheory.GlobalFields.SecondInequality.Statement
namespace GroundTheory.Global

open NumberField Module Polynomial IntermediateField

section GroupTheory

variable {G G' : Type*} [Group G] [Group G']

theorem enatCard_quotient_le_iff (H : Subgroup G) (n : ℕ) :
    ENat.card (G ⧸ H) ≤ n ↔ H.index ≠ 0 ∧ H.index ≤ n := by
  by_cases hf : Finite (G ⧸ H)
  · rw [ENat.card_eq_coe_natCard, Nat.cast_le]
    exact ⟨fun h ↦ ⟨Subgroup.index_ne_zero_of_finite, h⟩, fun h ↦ h.2⟩
  · have : Infinite (G ⧸ H) := not_finite_iff_infinite.1 hf
    rw [ENat.card_eq_top_of_infinite]
    refine ⟨fun h ↦ absurd h (by simp), fun h ↦ absurd h.1 ?_⟩
    rw [not_not, Subgroup.index, Nat.card_eq_zero_of_infinite]

theorem index_le_of_comap_le (f : G →* G') {H : Subgroup G} {H' : Subgroup G'}
    (hle : H'.comap f ≤ H) (hH' : H'.index ≠ 0) : H.index ≠ 0 ∧ H.index ≤ H'.index := by
  have h1 : (H'.comap f).index ≤ H'.index := by
    rw [Subgroup.index_comap, ← Subgroup.relIndex_top_right]
    exact Subgroup.relIndex_le_of_le_right le_top (by rwa [Subgroup.relIndex_top_right])
  have h2 : (H'.comap f).index ≠ 0 := by
    rw [Subgroup.index_comap]
    exact mt (Subgroup.relIndex_eq_zero_of_le_right le_top) (by rwa [Subgroup.relIndex_top_right])
  have h3 : H.index ∣ (H'.comap f).index := Subgroup.index_dvd_of_le hle
  exact ⟨fun h ↦ h2 (Nat.eq_zero_of_zero_dvd (h ▸ h3)), (Nat.le_of_dvd (Nat.pos_of_ne_zero h2) h3).trans h1⟩

theorem index_map_le (f : G →* G') {H : Subgroup G} (hH : H.index ≠ 0) (hf : f.range.index ≠ 0) :
    (H.map f).index ≠ 0 ∧ (H.map f).index ≤ f.range.index * H.index := by
  have h3 : (H ⊔ f.ker).index ∣ H.index := Subgroup.index_dvd_of_le le_sup_left
  have h4 : (H ⊔ f.ker).index ≠ 0 := fun h ↦ hH (Nat.eq_zero_of_zero_dvd (h ▸ h3))
  rw [Subgroup.index_map]
  refine ⟨mul_ne_zero h4 hf, ?_⟩
  rw [mul_comm]
  exact Nat.mul_le_mul_left _ (Nat.le_of_dvd (Nat.pos_of_ne_zero hH) h3)

theorem mem_of_pow_mem_of_coprime {H : Subgroup G} {x : G} {a b : ℕ} (hab : a.Coprime b)
    (ha : x ^ a ∈ H) (hb : x ^ b ∈ H) : x ∈ H := by
  have hg : ((a.gcd b : ℕ) : ℤ) = a * a.gcdA b + b * a.gcdB b := Nat.gcd_eq_gcd_ab a b
  rw [hab, Nat.cast_one] at hg
  have : x = (x ^ a) ^ a.gcdA b * (x ^ b) ^ a.gcdB b := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, ← hg, zpow_one]
  rw [this]
  exact mul_mem (zpow_mem ha _) (zpow_mem hb _)

theorem mul_comm_of_isCyclic [IsCyclic G] (a b : G) : a * b = b * a := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg a)
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg b)
  exact zpow_mul_comm g i j

end GroupTheory

def SecondInequalityRoots.{u} : Prop :=
  ∀ (K L : Type u) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)] (p : ℕ), p.Prime → HasEnoughRootsOfUnity K p →
    Module.finrank K L = p → ENat.card (IdeleClassGroup K ⧸ (ideleClassNorm K L).range) ≤ p

section Norms

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem pow_finrank_mem_range_ideleClassNorm (c : IdeleClassGroup K) :
    c ^ finrank K L ∈ (ideleClassNorm K L).range :=
  ⟨ideleClassMap K L c, ideleClassNorm_ideleClassMap c⟩

end Norms

end GroundTheory.Global
end

section -- merged from GroundTheory.GlobalFields.SecondInequality.PowFinrankMemRangeInfiniteLocalNorm
noncomputable section

namespace GroundTheory.Global

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField Module IntermediateField
open GroundTheory.ProfCoh IdeleGroup IdeleNorm SemiLocal
open scoped TensorProduct NumberField.LiesOver

section Splitting

variable {K : Type*} [Field K] {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity K n]

theorem algHom_mem_fieldRange_of_pow_eq {L F E : Type*} [Field L] [Field F] [Field E]
    [Algebra K L] [Algebra K F] [Algebra F E] [Algebra K E] [IsScalarTower K F E]
    {a : K} {α : L} (hα : α ^ n = algebraMap K L a) (hgen : K⟮α⟯ = ⊤) (ι : L →ₐ[K] E)
    {x : F} (hx : x ^ n = algebraMap K F a) (m : L) :
    ι m ∈ (algebraMap F E).fieldRange := by
  have hαr : ι α ∈ (algebraMap F E).fieldRange := by
    by_cases hx0 : x = 0
    · have ha : a = 0 := by
        rw [hx0, zero_pow (NeZero.ne n)] at hx
        exact (algebraMap K F).injective (by rw [← hx, map_zero])
      rw [ha, map_zero, pow_eq_zero_iff (NeZero.ne n)] at hα
      rw [hα, map_zero]
      exact zero_mem _
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K n
    have hζ' : IsPrimitiveRoot (algebraMap K E ζ) n :=
      hζ.map_of_injective (algebraMap K E).injective
    have hx0' : algebraMap F E x ≠ 0 := (map_ne_zero _).2 hx0
    have hpow : ι α ^ n = algebraMap F E x ^ n := by
      rw [← map_pow, hα, ι.commutes, ← map_pow, hx, ← IsScalarTower.algebraMap_apply]
    have hroot : (ι α / algebraMap F E x) ^ n = 1 := by
      rw [div_pow, hpow, div_self (pow_ne_zero _ hx0')]
    obtain ⟨k, -, hk⟩ := hζ'.eq_pow_of_pow_eq_one hroot
    refine ⟨algebraMap K F ζ ^ k * x, ?_⟩
    rw [map_mul, map_pow, ← IsScalarTower.algebraMap_apply, hk, div_mul_cancel₀ _ hx0']
  let J : IntermediateField K E := Subfield.toIntermediateField (algebraMap F E).fieldRange
    fun c ↦ ⟨algebraMap K F c, (IsScalarTower.algebraMap_apply K F E c).symm⟩
  have hle : K⟮α⟯ ≤ J.comap ι := adjoin_simple_le_iff.2 hαr
  rw [hgen] at hle
  exact hle (Set.mem_univ m)

variable [NumberField K] {L : Type*} [Field L] [NumberField L] [Algebra K L]

theorem splitsCompletely_of_pow_eq {a : K} {α : L} (hα : α ^ n = algebraMap K L a)
    (hgen : K⟮α⟯ = ⊤) (v : HeightOneSpectrum (𝓞 K))
    (h : ∃ x : v.adicCompletion K, x ^ n = algebraMap K (v.adicCompletion K) a) :
    SplitsCompletely L v := by
  obtain ⟨x, hx⟩ := h
  rw [splitsCompletely_iff_forall_finrank]
  intro w
  let g := (Pi.evalAlgHom (v.adicCompletion K) _ w).comp (tensorEquiv L v).toAlgHom
  exact finrank_eq_one_of_tensor_surjective g
    ((Function.surjective_eval w).comp (tensorEquiv L v).surjective)
    fun m ↦ algHom_mem_fieldRange_of_pow_eq hα hgen
      ((g.restrictScalars K).comp Algebra.TensorProduct.includeRight) hx m

end Splitting

section LocalNorms

variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L] [Algebra K L]

theorem pow_finrank_mem_range_finiteLocalNorm (v : HeightOneSpectrum (𝓞 K))
    (y : (v.adicCompletion K)ˣ) : y ^ finrank K L ∈ (finiteLocalNorm L v).range := by
  refine ⟨fun w ↦ Units.map (algebraMap (v.adicCompletion K) (w.1.adicCompletion L) :
    v.adicCompletion K →* w.1.adicCompletion L) y, ?_⟩
  apply Units.ext
  rw [coe_finiteLocalNorm, Units.val_pow_eq_pow_val, ← sum_finrank_eq L v,
    ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun w _ ↦ ?_
  rw [Units.coe_map]
  exact Algebra.norm_algebraMap (S := w.1.adicCompletion L) (y : v.adicCompletion K)

theorem pow_finrank_mem_range_infiniteLocalNorm (v : InfinitePlace K) (y : (v.Completion)ˣ) :
    y ^ finrank K L ∈ (infiniteLocalNorm L v).range := by
  classical
  refine ⟨fun w ↦ Units.map (algebraMap v.Completion (w : InfinitePlace L).Completion :
    v.Completion →* (w : InfinitePlace L).Completion) y, ?_⟩
  apply Units.ext
  rw [coe_infiniteLocalNorm, Units.val_pow_eq_pow_val, ← GroundTheory.Global.InfinitePlace.sum_finrank_completion (L := L) v,
    ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun w _ ↦ ?_
  rw [Units.coe_map]
  exact Algebra.norm_algebraMap (S := (w : InfinitePlace L).Completion) (y : v.Completion)

end LocalNorms

section Main

universe u

theorem not_mem_bot_of_adjoin_eq_top {K L : Type*} [Field K] [Field L] [Algebra K L] {α : L}
    (hgen : K⟮α⟯ = ⊤) (h1 : finrank K L ≠ 1) : α ∉ (⊥ : IntermediateField K L) := by
  intro hα
  have hbot : (⊤ : IntermediateField K L) = ⊥ := by
    rw [← hgen]
    exact adjoin_simple_eq_bot_iff.2 hα
  have := IntermediateField.finrank_eq_one_iff.2 hbot
  rw [IntermediateField.finrank_top'] at this
  exact h1 this

theorem FirstInequality.secondInequalityRoots (hFI : FirstInequality.{u}) :
    SecondInequalityRoots.{u} := by
  intro K L _ _ _ _ _ _ _ p hp hroots hdeg
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩

  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K p
  have hK : (primitiveRoots (finrank K L) K).Nonempty :=
    ⟨ζ, (mem_primitiveRoots finrank_pos).2 (hdeg ▸ hζ)⟩
  obtain ⟨α, ⟨a₀, ha₀⟩, hgen⟩ := exists_root_adjoin_eq_top_of_isCyclic K L hK
  rw [hdeg] at ha₀
  have h1 : finrank K L ≠ 1 := by rw [hdeg]; exact hp.ne_one
  have hαK := not_mem_bot_of_adjoin_eq_top hgen h1
  have ha₀0 : a₀ ≠ 0 := by
    rintro rfl
    rw [map_zero, eq_comm, pow_eq_zero_iff hp.ne_zero] at ha₀
    exact hαK (ha₀ ▸ zero_mem _)
  set a : Kˣ := Units.mk0 a₀ ha₀0 with ha_def
  have hα : α ^ p = algebraMap K L (a : K) := by rw [Units.val_mk0, ha₀]

  have hap : a ∉ unitsPow K p := by
    intro h
    obtain ⟨b, hb⟩ := mem_unitsPow.1 h
    have hb0 : algebraMap K L (b : K) ≠ 0 := (map_ne_zero _).2 b.ne_zero
    have hroot : (α / algebraMap K L (b : K)) ^ p = 1 := by
      rw [div_pow, hα, ← map_pow, ← Units.val_pow_eq_pow_val, hb,
        div_self ((map_ne_zero _).2 a.ne_zero)]
    have hζ' : IsPrimitiveRoot (algebraMap K L ζ) p :=
      hζ.map_of_injective (algebraMap K L).injective
    obtain ⟨k, -, hk⟩ := hζ'.eq_pow_of_pow_eq_one hroot
    refine hαK ⟨ζ ^ k * b, ?_⟩
    show algebraMap K L (ζ ^ k * (b : K)) = α
    rw [map_mul, map_pow, hk, div_mul_cancel₀ _ hb0]

  obtain ⟨S₀, hS₀⟩ := exists_finset_sup_sIdeles_eq_top (K := K)
  have hfp : {v : HeightOneSpectrum (𝓞 K) | (p : 𝓞 K) ∈ v.asIdeal}.Finite := by
    refine (Ideal.finite_factors (I := Ideal.span {(p : 𝓞 K)}) ?_).subset fun v hv ↦ ?_
    · rw [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast hp.ne_zero
    · exact Ideal.dvd_span_singleton.2 hv
  have hfa : {v : HeightOneSpectrum (𝓞 K) | ord v (diagonal K a) ≠ 0}.Finite :=
    eventually_ord_eq_zero (diagonal K a)
  set S : Finset (HeightOneSpectrum (𝓞 K)) := S₀ ∪ hfp.toFinset ∪ hfa.toFinset with hS
  have hpS : ∀ v, (p : 𝓞 K) ∈ v.asIdeal → v ∈ S := fun v hv ↦ by
    simp [S, hv]
  have hJ : (diagonal K).range ⊔ sIdeles (S : Set (HeightOneSpectrum (𝓞 K))) = ⊤ :=
    sup_sIdeles_eq_top_of_subset (fun v hv ↦ by simp [S, Finset.mem_coe.1 hv]) hS₀
  have haS : a ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K := by
    refine (diagonal_mem_sIdeles_iff _ a).1 fun v hv ↦ ?_
    by_contra h
    exact hv (by simp [S, h])

  obtain ⟨T, hST, -, haT, hidx⟩ := hFI.exists_places_index_map_powerSubgroup S hpS hJ haS hap

  have hnorm : powerSubgroup p (S : Set (HeightOneSpectrum (𝓞 K))) (T : Set (HeightOneSpectrum (𝓞 K))) ≤
      (ideleNorm K L).range := by
    intro x hx
    have hxST := powerSubgroup_le_sIdeles (S : Set (HeightOneSpectrum (𝓞 K)))
      (T : Set (HeightOneSpectrum (𝓞 K))) p hx
    obtain ⟨hxS, hxinf, -⟩ := (mem_localSubgroup _ _ _ _).1 hx
    refine mem_range_ideleNorm_of_forall x (fun v ↦ ?_) (fun w ↦ ?_)
    · by_cases hvS : v ∈ S
      · obtain ⟨y, hy⟩ := hxS v hvS
        rw [← hy, powMonoidHom_apply, ← hdeg]
        exact pow_finrank_mem_range_finiteLocalNorm v y
      by_cases hvT : v ∈ T
      · rw [range_finiteLocalNorm_eq_top_of_isFiniteSplit v ((splitsCompletely_iff_isFiniteSplit v).1
          (splitsCompletely_of_pow_eq hα hgen v (mem_unitsPowIn.1 (haT v hvT))))]
        exact Subgroup.mem_top _
      · obtain ⟨w⟩ := nonempty_placesOver L v
        have he : w.1.asIdeal.ramificationIdx (𝓞 K) = 1 :=
          Kummer.ramificationIdx_eq_one_of_pow_eq a hα hgen v (fun h ↦ hvS (hpS v h))
            (by rw [haS v hvS, WithZero.log_one]; exact dvd_zero _) w.1.asIdeal
        have hu : finiteProj v x ∈ (Submonoid.ofClass (v.adicCompletionIntegers K)).units := by
          have h := (mem_sIdeles_iff _).1 hxST v (by simp [hvS, hvT])
          rw [Submonoid.mem_units_iff, ← map_inv, coe_finiteProj, coe_finiteProj]
          exact ⟨h.1, h.2⟩
        rw [← map_integerUnitsOver_eq_of_ramificationIdx_eq_one v w he] at hu
        obtain ⟨z, -, hz⟩ := hu
        exact ⟨z, hz⟩
    · obtain ⟨y, hy⟩ := hxinf w
      rw [← hy, powMonoidHom_apply, ← hdeg]
      exact pow_finrank_mem_range_infiniteLocalNorm w y

  have hle : (powerSubgroup p (S : Set (HeightOneSpectrum (𝓞 K)))
      (T : Set (HeightOneSpectrum (𝓞 K)))).map (IdeleClassGroup.mk K) ≤
        (ideleClassNorm K L).range := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy⟩ := hnorm hx
    exact ⟨IdeleClassGroup.mk L y, by rw [ideleClassNorm_mk, hy]⟩
  have hdvd := Subgroup.index_dvd_of_le hle
  rw [hidx] at hdvd
  refine (enatCard_quotient_le_iff _ p).2 ⟨fun h ↦ ?_, Nat.le_of_dvd hp.pos hdvd⟩
  rw [h] at hdvd
  exact hp.ne_zero (Nat.eq_zero_of_zero_dvd hdvd)

end Main

end GroundTheory.Global
end
end

section -- merged from GroundTheory.GlobalFields.SecondInequality.Reduction
section -- merged from GroundTheory.GlobalFields.SecondInequality.PrimeDegree
namespace GroundTheory.Global

open NumberField Module Polynomial IntermediateField

universe u

section PrimeDegree

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem SecondInequalityRoots.index_le_of_prime (hR : SecondInequalityRoots.{u}) [IsGalois K L]
    {p : ℕ} (hp : p.Prime) (hL : finrank K L = p) :
    (ideleClassNorm K L).range.index ≠ 0 ∧ (ideleClassNorm K L).range.index ≤ p := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  let E := CyclotomicField p L
  let ζ : E := IsCyclotomicExtension.zeta p L E
  have hζ : IsPrimitiveRoot ζ p := IsCyclotomicExtension.zeta_spec p L E
  let K' : IntermediateField K E := K⟮ζ⟯

  have hroot : aeval ζ (cyclotomic p K) = 0 := by
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
    exact hζ.isRoot_cyclotomic hp.pos
  have hd_lt : finrank K K' < p := by
    rw [adjoin.finrank (Algebra.IsIntegral.isIntegral ζ)]
    have h1 := minpoly.degree_le_of_ne_zero K ζ (cyclotomic_ne_zero p K) hroot
    have h2 : (minpoly K ζ).natDegree ≤ (cyclotomic p K).natDegree := natDegree_le_natDegree h1
    rw [natDegree_cyclotomic, Nat.totient_prime hp] at h2
    have := hp.two_le
    omega
  have hd_pos : 0 < finrank K K' := finrank_pos
  have hcop : (finrank K K').Coprime p :=
    ((Nat.Prime.coprime_iff_not_dvd hp).2 (Nat.not_dvd_of_pos_of_lt hd_pos hd_lt)).symm

  let ζ' : K' := ⟨ζ, mem_adjoin_simple_self K ζ⟩
  have hζ' : IsPrimitiveRoot ζ' p :=
    (IsPrimitiveRoot.map_iff_of_injective (f := algebraMap K' E) (algebraMap K' E).injective).1 hζ
  have hroots : HasEnoughRootsOfUnity K' p := ⟨⟨ζ', hζ'⟩, rootsOfUnity.isCyclic K' p⟩

  obtain ⟨f, hfsep, hf⟩ := IsGalois.is_separable_splitting_field (F := K) (E := L)
  have := hf
  have : IsSplittingField L E ((cyclotomic p K).map (algebraMap K L)) := by
    rw [map_cyclotomic]
    exact IsCyclotomicExtension.splitting_field_cyclotomic p L E
  have : IsSplittingField K E (f * cyclotomic p K) :=
    IsSplittingField.mul (F := K) (K := L) (L := E) f (cyclotomic p K) hfsep.ne_zero (cyclotomic_ne_zero p K)
  have : IsGalois K E :=
    { to_isSeparable := inferInstance, to_normal := Normal.of_isSplittingField (f * cyclotomic p K) }
  have : IsGalois K' E := IsGalois.tower_top_of_isGalois K K' E

  let L' : IntermediateField K E := (IsScalarTower.toAlgHom K L E).fieldRange
  have hsup : K' ⊔ L' = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    have hx : x ∈ Algebra.adjoin L ({ζ} : Set E) := by
      rw [IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ]; trivial
    induction hx using Algebra.adjoin_induction with
    | mem y hy =>
      rw [Set.mem_singleton_iff.1 hy]
      exact le_sup_left (a := K') (mem_adjoin_simple_self K ζ)
    | algebraMap l => exact le_sup_right (b := L') ⟨l, rfl⟩
    | add _ _ _ _ h1 h2 => exact add_mem h1 h2
    | mul _ _ _ _ h1 h2 => exact mul_mem h1 h2
  have hL' : finrank K L' = p := by
    exact (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom K L E)).toLinearEquiv.finrank_eq.symm.trans hL

  have htow1 : finrank K K' * finrank K' E = finrank K E := finrank_mul_finrank K K' E
  have htow2 : finrank K L * finrank L E = finrank K E := finrank_mul_finrank K L E
  have hle : finrank K E ≤ finrank K K' * p := by
    have := finrank_sup_le K' L'
    rwa [hsup, finrank_top', hL'] at this
  have hdeg : finrank K' E = p := by
    have h1 : finrank K' E ≤ p := by
      rw [← htow1] at hle
      exact Nat.le_of_mul_le_mul_left hle hd_pos
    have h2 : p ∣ finrank K K' * finrank K' E := by
      rw [htow1, ← htow2, hL]
      exact dvd_mul_right p _
    have h3 : p ∣ finrank K' E := (Nat.Coprime.dvd_of_dvd_mul_left hcop.symm h2)
    exact le_antisymm h1 (Nat.le_of_dvd finrank_pos h3)
  have : IsCyclic (E ≃ₐ[K'] E) :=
    isCyclic_of_prime_card (p := p) (by rw [IsGalois.card_aut_eq_finrank, hdeg])

  have hE := (enatCard_quotient_le_iff _ p).1 (hR K' E p hp hroots hdeg)

  have hcomap : (ideleClassNorm K' E).range.comap (ideleClassMap K K') ≤
      (ideleClassNorm K L).range := by
    intro c hc
    obtain ⟨y, hy⟩ := hc
    refine mem_of_pow_mem_of_coprime hcop ?_ (hL ▸ pow_finrank_mem_range_ideleClassNorm c)
    refine ⟨ideleClassNorm L E y, ?_⟩
    rw [ideleClassNorm_ideleClassNorm, ← ideleClassNorm_ideleClassNorm (L := K'), hy,
      ideleClassNorm_ideleClassMap]
  have := index_le_of_comap_le (ideleClassMap K K') hcomap hE.1
  exact ⟨this.1, this.2.trans hE.2⟩

end PrimeDegree

end GroundTheory.Global
end

namespace GroundTheory.Global

open NumberField Module IntermediateField

universe u

def SecondInequality.{v} : Prop :=
  ∀ (K L : Type v) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)],
    ENat.card (IdeleClassGroup K ⧸ (ideleClassNorm K L).range) ≤ Module.finrank K L

theorem SecondInequalityRoots.index_le_of_finrank_eq (hR : SecondInequalityRoots.{u}) (n : ℕ) :
    ∀ (K L : Type u) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
      [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)], finrank K L = n →
      (ideleClassNorm K L).range.index ≠ 0 ∧ (ideleClassNorm K L).range.index ≤ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro K L _ _ _ _ _ _ _ hn
  have hn0 : 0 < n := hn ▸ finrank_pos
  by_cases h1 : n = 1
  ·
    have htop : (ideleClassNorm K L).range = ⊤ := by
      rw [eq_top_iff]
      intro c _
      have := pow_finrank_mem_range_ideleClassNorm (L := L) c
      rwa [hn, h1, pow_one] at this
    rw [htop, Subgroup.index_top]
    omega
  obtain ⟨q, hq, hqn⟩ := Nat.exists_prime_and_dvd h1
  have : Fact q.Prime := ⟨hq⟩
  have hcard : Nat.card (L ≃ₐ[K] L) = n := by rw [IsGalois.card_aut_eq_finrank, hn]
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' q (hcard ▸ hqn)

  let H : Subgroup (L ≃ₐ[K] L) := Subgroup.zpowers g
  have : H.Normal := ⟨fun a ha b ↦ by rwa [mul_comm_of_isCyclic b a, mul_inv_cancel_right]⟩
  let M : IntermediateField K L := fixedField H
  have hML : finrank M L = q := by
    rw [finrank_fixedField_eq_card, Nat.card_zpowers, hg]
  have hKM : finrank K M * q = n := by rw [← hML, finrank_mul_finrank, hn]
  have hm_lt : finrank K M < n := by
    have : 0 < finrank K M := finrank_pos
    calc finrank K M < finrank K M * 2 := by omega
      _ ≤ finrank K M * q := Nat.mul_le_mul_left _ hq.two_le
      _ = n := hKM

  have : IsGalois M L := IsGalois.tower_top_of_isGalois K M L
  have : IsCyclic (L ≃ₐ[M] L) :=
    isCyclic_of_prime_card (p := q) (by rw [IsGalois.card_aut_eq_finrank, hML])
  have : IsGalois K M := IsGalois.of_fixedField_normal_subgroup H
  have : IsCyclic (M ≃ₐ[K] M) :=
    isCyclic_of_surjective _ (AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := M) (E := L))
  have hM := ih (finrank K M) hm_lt K M rfl
  have hL := hR.index_le_of_prime (K := M) (L := L) hq hML

  have hcomp : (ideleClassNorm K M).comp (ideleClassNorm M L) = ideleClassNorm K L :=
    MonoidHom.ext fun c ↦ ideleClassNorm_ideleClassNorm c
  have hrange : (ideleClassNorm K L).range =
      (ideleClassNorm M L).range.map (ideleClassNorm K M) := by
    rw [MonoidHom.map_range, hcomp]
  have := index_map_le (ideleClassNorm K M) hL.1 hM.1
  rw [hrange]
  refine ⟨this.1, this.2.trans ?_⟩
  rw [← hKM]
  exact Nat.mul_le_mul hM.2 hL.2

theorem SecondInequalityRoots.secondInequality (hR : SecondInequalityRoots.{u}) :
    SecondInequality.{u} := by
  intro K L _ _ _ _ _ _ _
  exact (enatCard_quotient_le_iff _ _).2 (hR.index_le_of_finrank_eq _ K L rfl)

end GroundTheory.Global
end

namespace GroundTheory.Global

open NumberField GroundTheory.GroupCoh Module

universe u

theorem secondInequality : SecondInequality.{u} :=
  (firstInequality.{u}.secondInequalityRoots).secondInequality

section

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

theorem index_range_ideleClassNorm_eq_finrank [IsCyclic Gal(L/K)] :
    (ideleClassNorm K L).range.index = finrank K L := by
  obtain ⟨hge, hne⟩ := finrank_le_index_range_ideleClassNorm (K := K) (L := L)
  have hle := ((enatCard_quotient_le_iff _ _).1 (secondInequality.{u} K L)).2
  exact le_antisymm hle hge

theorem natCard_cycTateNegOne_ideleClassGroup (σ : Gal(L/K)) (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    Nat.card (CycTateNegOne (Representation.ofMulDistribMulAction Gal(L/K) (IdeleClassGroup L)) σ)
      = 1 := by
  have : IsCyclic Gal(L/K) := ⟨⟨σ, fun g ↦ Subgroup.mem_zpowers_iff.1 (hσ g)⟩⟩
  obtain ⟨h, hpos⟩ := index_range_ideleClassNorm σ hσ
  rw [index_range_ideleClassNorm_eq_finrank] at h
  have hn : 0 < finrank K L := finrank_pos
  have h' : finrank K L * 1 = finrank K L * _ := (mul_one _).trans h
  exact (Nat.eq_of_mul_eq_mul_left hn h').symm

theorem natCard_cycTateZero_ideleClassGroup_eq_finrank (σ : Gal(L/K))
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    Nat.card (CycTateZero (Representation.ofMulDistribMulAction Gal(L/K) (IdeleClassGroup L)) σ)
      = finrank K L := by
  have : IsCyclic Gal(L/K) := ⟨⟨σ, fun g ↦ Subgroup.mem_zpowers_iff.1 (hσ g)⟩⟩
  rw [natCard_cycTateZero_ideleClassGroup σ hσ, index_range_ideleClassNorm_eq_finrank]

theorem classFieldAxiom_ideleClassGroup (σ : Gal(L/K)) (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    Nat.card (CycTateZero (Representation.ofMulDistribMulAction Gal(L/K) (IdeleClassGroup L)) σ)
        = finrank K L ∧
      Nat.card (CycTateNegOne (Representation.ofMulDistribMulAction Gal(L/K) (IdeleClassGroup L)) σ)
        = 1 :=
  ⟨natCard_cycTateZero_ideleClassGroup_eq_finrank σ hσ, natCard_cycTateNegOne_ideleClassGroup σ hσ⟩

end

end GroundTheory.Global
