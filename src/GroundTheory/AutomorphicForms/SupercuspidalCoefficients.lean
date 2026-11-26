module

public import GroundTheory.AutomorphicForms.JacquetAdmissible
public import GroundTheory.AutomorphicForms.IwahoriFactorization
public import GroundTheory.AutomorphicForms.ReductionMahler

@[expose] public section

section -- merged from GroundTheory.AutomorphicForms.SupercuspidalCoefficients
noncomputable section

namespace GroundTheory.Automorphic

namespace Parabolic

open Matrix Iwasawa GLnLocal ValuativeRel Topology Filter Set
open scoped Pointwise

section General

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} {N M Nbar K : Subgroup G}

theorem mk_fixedProj_eq (hρ : IsSmooth ρ) (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))
    (hfact : ∀ k ∈ K, ∃ x ∈ K ⊓ N, ∃ y ∈ K ⊓ M, ∃ z ∈ K ⊓ Nbar, k = x * y * z)
    {w : V} (hwNbar : ∀ z ∈ K ⊓ Nbar, ρ z w = w)
    (hwM : ∀ y ∈ K ⊓ M, Representation.Coinvariants.mk (ρ.comp N.subtype) (ρ y w) =
      Representation.Coinvariants.mk (ρ.comp N.subtype) w) :
    Representation.Coinvariants.mk (ρ.comp N.subtype) (fixedProj ρ hρ hKc hKo w : V) =
      Representation.Coinvariants.mk (ρ.comp N.subtype) w := by
  classical
  have hterm : ∀ k ∈ K, Representation.Coinvariants.mk (ρ.comp N.subtype) (ρ k w) =
      Representation.Coinvariants.mk (ρ.comp N.subtype) w := by
    intro k hk
    obtain ⟨x, hx, y, hy, z, hz, rfl⟩ := hfact k hk
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hwNbar z hz,
      mk_apply_of_mem ρ N (Subgroup.mem_inf.1 hx).2, hwM y hy]
  obtain ⟨N', -, -, hN'U, hnorm, hfin⟩ := exists_normal_subgroup hKc hKo
    ((hρ w).mem_nhds (one_mem (stabilizerOf ρ w)))
  have := Fintype.ofFinite (K ⧸ N'.subgroupOf K)
  have hw' : w ∈ fixedVectors ρ N' := fun k hk => hN'U hk
  set c : ℂ := (Fintype.card (K ⧸ N'.subgroupOf K) : ℂ)
  have hc : c ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hyK : c⁻¹ • cosetSum ρ K N' w ∈ fixedVectors ρ K :=
    Submodule.smul_mem _ _ (cosetSum_mem_fixedVectors ρ hnorm hw')
  have hey : fixedProj ρ hρ hKc hKo w = ⟨c⁻¹ • cosetSum ρ K N' w, hyK⟩ := by
    rw [fixedProj_eq_iff]
    have heq : w - c⁻¹ • cosetSum ρ K N' w =
        c⁻¹ • ∑ q : K ⧸ N'.subgroupOf K, (w - ρ ((Quotient.out q : K) : G) w) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, ← cosetSum_apply, smul_sub,
        ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]
    show w - c⁻¹ • cosetSum ρ K N' w ∈ coinvariantsKer ρ K
    rw [heq]
    refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun q _ => ?_)
    rw [← neg_sub]
    exact Submodule.neg_mem _ (sub_mem_coinvariantsKer (Quotient.out q).2 w)
  rw [hey]
  show Representation.Coinvariants.mk (ρ.comp N.subtype) (c⁻¹ • cosetSum ρ K N' w) = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_smul, cosetSum_apply, map_sum,
    Finset.sum_congr rfl fun q _ => hterm _ (Quotient.out q).2, Finset.sum_const,
    Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]

end General

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]

def IsSupercuspidal (π : Representation ℂ (GL (Fin n) F) V) : Prop :=
  ∀ γ : Fin n → ℕ, (∃ i j, γ i ≠ γ j) → Subsingleton (JacquetModule F n γ π)

def matrixCoeff (π : Representation ℂ (GL (Fin n) F) V) (v : V) (f : Module.Dual ℂ V)
    (g : GL (Fin n) F) : ℂ :=
  f (π g v)

def IsCompactModCenter (φ : GL (Fin n) F → ℂ) : Prop :=
  ∃ C : Set (GL (Fin n) F), IsCompact C ∧
    Function.support φ ⊆ (Subgroup.center (GL (Fin n) F) : Set (GL (Fin n) F)) * C

section Compact

variable {π : Representation ℂ (GL (Fin n) F) V}

theorem exists_finset_of_isSupercuspidal (hsc : IsSupercuspidal π) {S : Finset (Fin n)}
    (hS : ∃ i j, i ∈ S ∧ j ∉ S) (w : V) :
    ∃ U : Finset (GL (Fin n) F), (∀ u ∈ U, u ∈ unipotentRadical F n (splitFun S)) ∧
      w ∈ Submodule.span ℂ {y | ∃ u ∈ U, ∃ x, y = π u x - x} := by
  classical
  obtain ⟨i, j, hi, hj⟩ := hS
  have hsub := hsc (splitFun S) ⟨i, j, by simp [splitFun, hi, hj]⟩
  have hw : w ∈ Representation.Coinvariants.ker (π.comp (unipotentRadical F n (splitFun S)).subtype) :=
    (Representation.Coinvariants.mk_eq_zero _).1 (Subsingleton.elim _ _)
  obtain ⟨T, hT, hwT⟩ := Submodule.mem_span_finite_of_mem_span hw
  have hpre : ∀ y ∈ T, ∃ gv : unipotentRadical F n (splitFun S) × V,
      π (gv.1 : GL (Fin n) F) gv.2 - gv.2 = y := by
    intro y hy
    obtain ⟨gv, h⟩ := hT hy
    exact ⟨gv, h⟩
  choose! pre hpre using hpre
  refine ⟨T.image fun y => ((pre y).1 : GL (Fin n) F), ?_, ?_⟩
  · intro u hu
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hu
    exact (pre y).1.2
  · refine Submodule.span_mono ?_ hwT
    intro y hy
    exact ⟨((pre y).1 : GL (Fin n) F), Finset.mem_image_of_mem _ hy, (pre y).2, (hpre y hy).symm⟩

theorem diagPow_const_mem_center (c : ℤ) :
    Cartan.diagPow F n (fun _ => c) ∈ Subgroup.center (GL (Fin n) F) :=
  Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.2
    ⟨(uniformizer F : F) ^ c, by rw [Matrix.scalar_apply, Cartan.coe_diagPow]⟩

theorem isCompactModCenter_matrixCoeff (hπ : IsSmooth π) (hsc : IsSupercuspidal π) (v : V)
    {f : Module.Dual ℂ V} (hf : f ∈ smoothVectors (Representation.dual π)) :
    IsCompactModCenter (matrixCoeff π v f) := by
  classical
  obtain ⟨m₁, -, hm₁⟩ := (hasBasis_nhds_one F n).mem_iff.1 ((hπ v).mem_nhds (one_mem _))
  obtain ⟨m₂, -, hm₂⟩ := (hasBasis_nhds_one F n).mem_iff.1
    ((mem_smoothVectors.1 hf).mem_nhds (one_mem _))
  set m := max m₁ m₂
  set K := congruenceSubgroup F n m
  have hvK : v ∈ fixedVectors π K := fun k hk =>
    hm₁ (congruenceSubgroup_antitone F n (le_max_left _ _) hk)
  have hfK : ∀ k ∈ K, ∀ x, f (π k x) = f x := mem_fixedVectors_dual.1 fun k hk =>
    hm₂ (congruenceSubgroup_antitone F n (le_max_right _ _) hk)
  set K₀ := integralGL F n
  have : CompactSpace K₀ := isCompact_iff_compactSpace.1 (isCompact_integralGL F n)
  have hQ : Finite (K₀ ⧸ K.subgroupOf K₀) := by
    refine Subgroup.quotient_finite_of_isOpen _ ?_
    rw [Subgroup.coe_subgroupOf]
    exact (isOpen_congruenceSubgroup F n m).preimage continuous_subtype_val
  have := Fintype.ofFinite (K₀ ⧸ K.subgroupOf K₀)
  let R : Finset (GL (Fin n) F) :=
    Finset.univ.image fun q : K₀ ⧸ K.subgroupOf K₀ => ((Quotient.out q : K₀) : GL (Fin n) F)
  have hR : ∀ k ∈ K₀, ∃ r ∈ R, π k v = π r v := by
    intro k hk
    refine ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ (QuotientGroup.mk (⟨k, hk⟩ : K₀))), ?_⟩
    exact act_eq_of_mk_eq π hvK (a := ⟨k, hk⟩)
      (b := Quotient.out (QuotientGroup.mk (⟨k, hk⟩ : K₀) : K₀ ⧸ K.subgroupOf K₀))
      (QuotientGroup.out_eq' _).symm
  let V₂ : Finset V := R.image fun r => π r v
  have hU : ∀ S : Finset (Fin n), (∃ i j, i ∈ S ∧ j ∉ S) → ∀ w : V,
      ∃ U : Finset (GL (Fin n) F), (∀ u ∈ U, u ∈ unipotentRadical F n (splitFun S)) ∧
        w ∈ Submodule.span ℂ {y | ∃ u ∈ U, ∃ x, y = π u x - x} :=
    fun S hS w => exists_finset_of_isSupercuspidal hsc hS w
  choose! Uf hUf1 hUf2 using hU
  let Uall : Finset (GL (Fin n) F) := Finset.univ.biUnion fun S : Finset (Fin n) => V₂.biUnion (Uf S)
  obtain ⟨t, ht⟩ := exists_pow_mul_mem_of_isCompact F n
    ((Uall ∪ Uall.image fun u => u⁻¹ : Finset (GL (Fin n) F)) : Set (GL (Fin n) F)).toFinite.isCompact
  have hbu : ∀ u ∈ Uall, ∀ i j, (uniformizer F : F) ^ t * u i j ∈ 𝒪[F] :=
    fun u hu => ht _ (by simp [hu])
  have hbu' : ∀ u ∈ Uall, ∀ i j, (uniformizer F : F) ^ t * (u⁻¹ : GL (Fin n) F) i j ∈ 𝒪[F] :=
    fun u hu => ht _ (by simp only [Finset.coe_union, Finset.coe_image, Set.mem_union,
      Set.mem_image, Finset.mem_coe]; exact Or.inr ⟨u, hu, rfl⟩)
  set C : ℤ := ((t + m : ℕ) : ℤ) + 1 with hCdef
  have hC : ((t + m : ℕ) : ℤ) < C := lt_add_one _
  have hC0 : 0 < C := by positivity
  let Nset : Finset (Fin n → ℤ) := Fintype.piFinset fun _ => Finset.Icc 0 (n * C)
  let Cset : Set (GL (Fin n) F) := ⋃ ν ∈ (Nset : Set (Fin n → ℤ)),
    (fun p : GL (Fin n) F × GL (Fin n) F => p.1 * Cartan.diagPow F n ν * p.2) ''
      ((K₀ : Set (GL (Fin n) F)) ×ˢ (K₀ : Set (GL (Fin n) F)))
  have hCset : IsCompact Cset :=
    Nset.finite_toSet.isCompact_biUnion fun ν _ =>
      ((isCompact_integralGL F n).prod (isCompact_integralGL F n)).image (by fun_prop)
  refine ⟨Cset, hCset, fun g hg => ?_⟩
  rw [Function.mem_support] at hg
  obtain ⟨μ, -, k₁, hk₁, k₂, hk₂, rfl⟩ := Cartan.exists_eq_mul_diagPow_mul F n g
  obtain ⟨r₂, hr₂, hr₂v⟩ := hR k₂ hk₂
  have hwV : π r₂ v ∈ V₂ := Finset.mem_image_of_mem _ hr₂
  rcases gap_or_bounded (β := fun _ : Fin n => (0 : ℕ)) μ hC0 with
    ⟨θ, b, ⟨i, hib, hiθ⟩, ⟨j, hjb, hjθ⟩, hgap⟩ | hbd
  · exfalso
    apply hg
    set S : Finset (Fin n) :=
      Finset.univ.filter fun j => (fun _ : Fin n => (0 : ℕ)) j = b ∧ θ ≤ μ j with hSdef
    have hS : ∃ i j, i ∈ S ∧ j ∉ S :=
      ⟨i, j, by simp [S, hib, hiθ], by simp [S, hjb, not_le.2 hjθ]⟩
    have hsp := hUf2 S hS (π r₂ v)
    set a := Cartan.diagPow F n μ
    have hker : Submodule.span ℂ {y | ∃ u ∈ Uf S (π r₂ v), ∃ x, y = π u x - x} ≤
        LinearMap.ker (f ∘ₗ π k₁ ∘ₗ π a) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨u, hu, x, rfl⟩
      have huA : u ∈ Uall := Finset.mem_biUnion.2 ⟨S, Finset.mem_univ _,
        Finset.mem_biUnion.2 ⟨π r₂ v, hwV, hu⟩⟩
      have huN := hUf1 S hS (π r₂ v) u hu
      have hlev : ∀ w : GL (Fin n) F, w ∈ levi F n (fun _ : Fin n => (0 : ℕ)) :=
        fun w => mem_levi.2 fun i j h => absurd rfl h
      have hconj : a * u * a⁻¹ ∈ K :=
        diagPow_conj_mem_congruenceSubgroup hC (apply_eq_or_gap hgap (hlev u) huN)
          (apply_eq_or_gap hgap (hlev u⁻¹) ((unipotentRadical F n _).inv_mem huN))
          (hbu u huA) (hbu' u huA)
      have hconj' : k₁ * (a * u * a⁻¹) * k₁⁻¹ ∈ K := conj_mem_congruenceSubgroup F n hk₁ hconj
      simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
        map_sub]
      have h1 : π k₁ (π a (π u x)) = π (k₁ * (a * u * a⁻¹) * k₁⁻¹) (π k₁ (π a x)) := by
        simp only [← Module.End.mul_apply, ← map_mul]
        group
      rw [h1, hfK _ hconj', sub_self]
    have := hker hsp
    simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply] at this
    show f (π (k₁ * a * k₂) v) = 0
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hr₂v]
    exact this
  ·
    let c₀ : ℤ := if h : ∃ k : Fin n, True then
      (Finset.univ.image μ).min' ⟨_, Finset.mem_image_of_mem μ (Finset.mem_univ h.choose)⟩ else 0
    have hc₀le : ∀ k, c₀ ≤ μ k := by
      intro k
      simp only [c₀, dif_pos (⟨k, trivial⟩ : ∃ k : Fin n, True)]
      exact Finset.min'_le _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))
    have hc₀mem : ∀ j : Fin n, ∃ k, c₀ = μ k := by
      intro j
      simp only [c₀, dif_pos (⟨j, trivial⟩ : ∃ k : Fin n, True)]
      obtain ⟨k, -, hk⟩ := Finset.mem_image.1 (Finset.min'_mem (Finset.univ.image μ) _)
      exact ⟨k, hk.symm⟩
    let ν : Fin n → ℤ := μ - fun _ => c₀
    have hν : ν ∈ Nset := by
      rw [Fintype.mem_piFinset]
      intro j
      rw [Finset.mem_Icc]
      obtain ⟨k, hk⟩ := hc₀mem j
      have h1 := hc₀le j
      have h2 := hbd j k rfl
      constructor
      · show 0 ≤ μ j - c₀
        linarith
      · show μ j - c₀ ≤ n * C
        linarith
    have hμ : μ = (fun _ => c₀) + ν := by
      funext j
      simp [ν]
    have hz := diagPow_const_mem_center (F := F) (n := n) c₀
    refine Set.mem_mul.2 ⟨Cartan.diagPow F n (fun _ => c₀), hz, k₁ * Cartan.diagPow F n ν * k₂,
      Set.mem_biUnion hν ⟨(k₁, k₂), ⟨hk₁, hk₂⟩, rfl⟩, ?_⟩
    rw [hμ, diagPow_add, ← mul_assoc k₁, Subgroup.mem_center_iff.1 hz k₁]
    group

end Compact

section Converse

variable {π : Representation ℂ (GL (Fin n) F) V}

end Converse

end Parabolic

end GroundTheory.Automorphic
end
end

section -- merged from GroundTheory.AutomorphicForms.ReductionMeasure
open NumberField IsDedekindDomain Topology Filter Set MeasureTheory TopologicalSpace
open scoped NumberField.AdeleRing RestrictedProduct ENNReal

namespace GroundTheory.Automorphic

noncomputable section

namespace Reduction

variable {K : Type*} [Field K] [NumberField K]

instance secondCountableTopology_finiteAdeleRing :
    SecondCountableTopology (FiniteAdeleRing (𝓞 K) K) := by
  have := GroundTheory.Global.countable_numberField K
  have : ∀ v : HeightOneSpectrum (𝓞 K),
      SecondCountableTopology ↥(v.adicCompletionIntegers K : Set (v.adicCompletion K)) := fun v =>
    inferInstanceAs (SecondCountableTopology (v.adicCompletionIntegers K))
  have hemb := RestrictedProduct.isOpenEmbedding_structureMap
    (R := fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
    (A := fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
    (fun v => Valued.isOpen_valuationSubring (v.adicCompletion K))
  set O : Set (FiniteAdeleRing (𝓞 K) K) :=
    Set.range (RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
      (fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K))) cofinite) with hO
  have hOsc : SecondCountableTopology O :=
    hemb.toIsEmbedding.toHomeomorph.symm.isEmbedding.secondCountableTopology
  have hOopen : IsOpen O := hemb.isOpen_range
  have hOmem : ∀ x : FiniteAdeleRing (𝓞 K) K, x ∈ O ↔
      x ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 K) K := fun x => by
    constructor
    · rintro ⟨y, rfl⟩ v
      exact (y v).2
    · intro h
      exact ⟨fun v => ⟨x v, h v⟩, rfl⟩
  let U : K → Set (FiniteAdeleRing (𝓞 K) K) := fun k => (· - algebraMap K _ k) ⁻¹' O
  have hU : ∀ k, SecondCountableTopology (U k) := fun k => by
    have he : IsEmbedding (Set.codRestrict
        ((Homeomorph.subRight (algebraMap K (FiniteAdeleRing (𝓞 K) K) k)) ∘
          (Subtype.val : U k → FiniteAdeleRing (𝓞 K) K)) O fun x => x.2) :=
      ((Homeomorph.subRight (algebraMap K (FiniteAdeleRing (𝓞 K) K) k)).isEmbedding.comp
        IsEmbedding.subtypeVal).codRestrict _ _
    exact he.secondCountableTopology
  refine TopologicalSpace.secondCountableTopology_of_countable_cover (U := U)
    (fun k => hOopen.preimage (continuous_sub_right _)) ?_
  · refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ?_
    obtain ⟨k, hk⟩ := GroundTheory.Global.exists_sub_mem_integralFiniteAdeles x
    exact ⟨k, (hOmem _).2 hk⟩

instance secondCountableTopology_adeleRing : SecondCountableTopology 𝔸[K] :=
  inferInstanceAs (SecondCountableTopology (InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K))

instance secondCountableTopology_matrix {R : Type*} [TopologicalSpace R] [SecondCountableTopology R]
    {n : ℕ} : SecondCountableTopology (Matrix (Fin n) (Fin n) R) :=
  inferInstanceAs (SecondCountableTopology (Fin n → Fin n → R))

instance measurableSpace_adelicGL {n : ℕ} : MeasurableSpace (AdelicGLn.AdelicGL K n) := _root_.borel _

instance borelSpace_adelicGL {n : ℕ} : BorelSpace (AdelicGLn.AdelicGL K n) := ⟨rfl⟩

instance measurableSpace_finiteAdelicGL {n : ℕ} : MeasurableSpace (AdelicGLn.FiniteAdelicGL K n) :=
  _root_.borel _

instance borelSpace_finiteAdelicGL {n : ℕ} : BorelSpace (AdelicGLn.FiniteAdelicGL K n) := ⟨rfl⟩

instance measurableSpace_GL_infinitePlace {n : ℕ} (w : InfinitePlace K) :
    MeasurableSpace (GL (Fin n) w.Completion) :=
  _root_.borel _

instance borelSpace_GL_infinitePlace {n : ℕ} (w : InfinitePlace K) :
    BorelSpace (GL (Fin n) w.Completion) := ⟨rfl⟩

def infFinEquiv {n : ℕ} : AdelicGLn.AdelicGL K n ≃ₜ*
    (Π w : InfinitePlace K, GL (Fin n) w.Completion) × AdelicGLn.FiniteAdelicGL K n :=
  (AdelicGLn.prodEquiv K n).trans
    { toMulEquiv := MulEquiv.prodCongr (AdelicGLn.infiniteEquiv K n).toMulEquiv (MulEquiv.refl _)
      continuous_toFun :=
        ((AdelicGLn.infiniteEquiv K n).continuous.comp continuous_fst).prodMk continuous_snd
      continuous_invFun :=
        ((AdelicGLn.infiniteEquiv K n).symm.continuous.comp continuous_fst).prodMk continuous_snd }

set_option synthInstance.maxHeartbeats 200000 in
theorem measure_lt_top_of_forall_mem {n : ℕ} (μ : Measure (AdelicGLn.AdelicGL K n))
    [μ.IsHaarMeasure] {E : Set (AdelicGLn.AdelicGL K n)}
    (S : ∀ w : InfinitePlace K, Set (GL (Fin n) w.Completion))
    (hS : ∀ w, (Measure.haar : Measure (GL (Fin n) w.Completion)) (S w) < ⊤)
    {F : Set (AdelicGLn.FiniteAdelicGL K n)} (hF : IsCompact F)
    (hE : ∀ g ∈ E, (∀ w, infAt w g ∈ S w) ∧ (AdelicGLn.prodEquiv K n g).2 ∈ F) : μ E < ⊤ := by
  set e := infFinEquiv (K := K) (n := n) with he
  set ρ : Measure ((Π w : InfinitePlace K, GL (Fin n) w.Completion) × AdelicGLn.FiniteAdelicGL K n) :=
    (Measure.pi fun w => (Measure.haar : Measure (GL (Fin n) w.Completion))).prod
      (Measure.haar : Measure (AdelicGLn.FiniteAdelicGL K n)) with hρ
  have hν : (Measure.map e μ).IsHaarMeasure :=
    MulEquiv.isHaarMeasure_map μ e.toMulEquiv e.continuous e.symm.continuous
  have heq := Measure.isMulLeftInvariant_eq_smul (Measure.map e μ) ρ
  set T := (Set.univ.pi S) ×ˢ F with hT
  have hET : E ⊆ e ⁻¹' T := fun g hg => ⟨fun w _ => (hE g hg).1 w, (hE g hg).2⟩
  have hmap : μ (e ⁻¹' T) = Measure.map e μ T :=
    (e.toHomeomorph.toMeasurableEquiv.map_apply T).symm
  have hρT : ρ T = (∏ w, (Measure.haar : Measure (GL (Fin n) w.Completion)) (S w)) *
      (Measure.haar : Measure (AdelicGLn.FiniteAdelicGL K n)) F := by
    rw [hρ, hT, Measure.prod_prod, Measure.pi_pi]
  set c := (Measure.map e μ).haarScalarFactor ρ with hc
  calc μ E ≤ μ (e ⁻¹' T) := measure_mono hET
    _ = Measure.map e μ T := hmap
    _ = (c • ρ) T := by rw [← heq]
    _ < ⊤ := by
      rw [Measure.smul_apply, hρT, ENNReal.smul_def, smul_eq_mul]
      exact ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.mul_lt_top
        (ENNReal.prod_lt_top fun w _ => hS w) hF.measure_lt_top)

end Reduction

end

end GroundTheory.Automorphic
end

section -- merged from GroundTheory.AutomorphicForms.NormDetDiagUnitsPosRealToUnits
open NumberField IsDedekindDomain Topology Filter Set Matrix
open scoped NumberField.AdeleRing RestrictedProduct
open GroundTheory.Global GroundTheory.Global.IdeleGroup

namespace GroundTheory.Automorphic

noncomputable section

namespace Reduction

theorem eq_one_of_isCompact {G : Type*} [Group G] [TopologicalSpace G] {H : Subgroup G}
    (hH : IsCompact (H : Set G)) (f : G →* {r : ℝ // 0 < r}) (hf : Continuous fun g => (f g : ℝ))
    {h : G} (hh : h ∈ H) : f h = 1 := by
  obtain ⟨M, hM⟩ := hH.exists_bound_of_continuousOn hf.continuousOn
  have hbound : ∀ m : ℕ, (f h : ℝ) ^ m ≤ M ∧ ((f h : ℝ)⁻¹) ^ m ≤ M := fun m => by
    have h1 := hM (h ^ m) (pow_mem hh m)
    have h2 := hM ((h⁻¹) ^ m) (pow_mem (inv_mem hh) m)
    rw [map_pow, Positive.val_pow, Real.norm_eq_abs, abs_of_pos (pow_pos (f h).2 m)] at h1
    rw [map_pow, map_inv, Positive.val_pow, Positive.coe_inv, Real.norm_eq_abs,
      abs_of_pos (pow_pos (inv_pos.2 (f h).2) m)] at h2
    exact ⟨h1, h2⟩
  refine Subtype.ext ?_
  rw [Positive.val_one]
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h1 : 1 < (f h : ℝ)⁻¹ := (one_lt_inv₀ (f h).2).2 hlt
    obtain ⟨m, hm⟩ := (tendsto_pow_atTop_atTop_of_one_lt h1).eventually_gt_atTop M |>.exists
    exact absurd (hbound m).2 (not_le.2 hm)
  · obtain ⟨m, hm⟩ := (tendsto_pow_atTop_atTop_of_one_lt hgt).eventually_gt_atTop M |>.exists
    exact absurd (hbound m).1 (not_le.2 hm)

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

def normDet (w : InfinitePlace K) : GL (Fin n) w.Completion →* {r : ℝ // 0 < r} where
  toFun g := ⟨‖(g : Matrix (Fin n) (Fin n) w.Completion).det‖, norm_pos_iff.2 (by
    have := (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
    exact this.ne_zero)⟩
  map_one' := by ext; simp
  map_mul' g h := by ext; simp [Matrix.det_mul]

theorem continuous_normDet (w : InfinitePlace K) :
    Continuous fun g : GL (Fin n) w.Completion => (normDet (n := n) w g : ℝ) :=
  (Continuous.matrix_det (Units.continuous_val (M := Matrix (Fin n) (Fin n) w.Completion))).norm

theorem norm_det_of_mem_archCompact {w : InfinitePlace K} {k : GL (Fin n) w.Completion}
    (hk : k ∈ archCompact w) : ‖(k : Matrix (Fin n) (Fin n) w.Completion).det‖ = 1 := by
  have := eq_one_of_isCompact (isCompact_archCompact w) (normDet w) (continuous_normDet w) hk
  exact congrArg Subtype.val this

theorem norm_det_infAt_of_mem_maxCompact {k : AdelicGLn.AdelicGL K n} (hk : k ∈ maxCompact)
    (w : InfinitePlace K) : ‖(infAt w k : Matrix (Fin n) (Fin n) w.Completion).det‖ = 1 :=
  norm_det_of_mem_archCompact (hk.1 w)

theorem infAt_diagUnits (w : InfinitePlace K) (f : Fin n → IdeleGroup K) :
    infAt w (diagUnits n f) = diagUnits n (fun i => infiniteProj w (f i)) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [infAt_apply, coe_diagUnits, coe_diagUnits, diagonal_apply, diagonal_apply]
  split_ifs
  · rw [coe_infiniteProj]
  · rfl

theorem infAt_diagUnits_posIdele (w : InfinitePlace K) (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) :
    infAt w (diagUnits n fun i => posIdele (K := K) (r i) (hr i)) =
      diagUnits n (fun i => posRealToUnits w ⟨r i ^ w.mult, pow_pos (hr i) _⟩) := by
  rw [infAt_diagUnits]
  congr 1
  funext i
  exact infiniteProj_posIdele (r i) (hr i) w

theorem norm_posRealToUnits (w : InfinitePlace K) {r : ℝ} (hr : 0 < r) :
    ‖((posRealToUnits w ⟨r ^ w.mult, pow_pos hr _⟩ : (w.Completion)ˣ) : w.Completion)‖ = r := by
  have h := norm_posRealElem_pow w (pow_pos hr w.mult).le
  have hm : w.mult ≠ 0 := InfinitePlace.mult_ne_zero
  exact (pow_left_inj₀ (norm_nonneg _) hr.le hm).1 h

theorem norm_det_diagUnits_posRealToUnits (w : InfinitePlace K) (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) :
    ‖((diagUnits n (fun i => posRealToUnits w ⟨r i ^ w.mult, pow_pos (hr i) _⟩) :
      GL (Fin n) w.Completion) : Matrix (Fin n) (Fin n) w.Completion).det‖ = ∏ i, r i := by
  rw [coe_diagUnits, det_diagonal, norm_prod]
  exact Finset.prod_congr rfl fun i _ => norm_posRealToUnits w (hr i)

theorem prodEquiv_diagUnits_posIdele_snd (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) :
    (AdelicGLn.prodEquiv K n (diagUnits n fun i => posIdele (K := K) (r i) (hr i))).2 = 1 := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  rw [AdelicGLn.prodEquiv_apply_snd, coe_diagUnits, diagonal_apply]
  split_ifs with h
  · subst h
    refine RestrictedProduct.ext _ _ fun v => ?_
    have := posIdele_finite (K := K) (r a) (hr a) v
    exact this.trans (by simp; rfl)
  · rw [Units.val_one, Matrix.one_apply_ne h]
    rfl

end Reduction

end

end GroundTheory.Automorphic
end

section -- merged from GroundTheory.AutomorphicForms.ReductionSplitting
section -- merged from GroundTheory.PowerSubgroups.CountableNeighbourhoods.GLnPowerSubgroups
namespace GroundTheory.Variant₂.N1

open NumberField

section Splitting

variable {G P : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CommGroup P] [TopologicalSpace P]

def centralSplitting (φ : G →* P) (hφ : Continuous φ) (s : P →* G) (hs : Continuous s)
    (hsφ : ∀ p, φ (s p) = p) (hc : ∀ p g, s p * g = g * s p) (H : Subgroup G)
    (hH : ∀ g, g ∈ H ↔ φ g = 1) : G ≃ₜ* H × P where
  toFun g := (⟨g * (s (φ g))⁻¹, (hH _).2 (by rw [map_mul, map_inv, hsφ, mul_inv_cancel])⟩, φ g)
  invFun x := (x.1 : G) * s x.2
  left_inv g := by simp
  right_inv x := by
    obtain ⟨⟨h, hh⟩, p⟩ := x
    have h1 : φ h = 1 := (hH h).1 hh
    have h2 : φ (h * s p) = p := by rw [map_mul, h1, hsφ, one_mul]
    refine Prod.ext (Subtype.ext ?_) h2
    simp [h2]
  map_mul' g g' := by
    have hci : ∀ p g, (s p)⁻¹ * g = g * (s p)⁻¹ := fun p g => by
      rw [← map_inv]; exact hc p⁻¹ g
    refine Prod.ext (Subtype.ext ?_) (map_mul φ g g')
    simp only [map_mul, mul_inv_rev]
    rw [hci (φ g') (s (φ g))⁻¹]
    calc g * g' * ((s (φ g))⁻¹ * (s (φ g'))⁻¹)
        = g * (g' * (s (φ g))⁻¹) * (s (φ g'))⁻¹ := by simp only [mul_assoc]
      _ = g * ((s (φ g))⁻¹ * g') * (s (φ g'))⁻¹ := by rw [hci]
      _ = g * (s (φ g))⁻¹ * (g' * (s (φ g'))⁻¹) := by simp only [mul_assoc]
  continuous_toFun :=
    (Continuous.subtype_mk (continuous_id.mul ((hs.comp hφ).inv)) _).prodMk hφ
  continuous_invFun := (continuous_subtype_val.comp continuous_fst).mul (hs.comp continuous_snd)

end Splitting

section Section

variable {K : Type*} [Field K]


variable [NumberField K]





end Section

end GroundTheory.Variant₂.N1
end

open NumberField IsDedekindDomain Topology Filter Set Matrix MeasureTheory
open scoped NumberField.AdeleRing RestrictedProduct ENNReal
open GroundTheory.Global GroundTheory.Global.IdeleGroup

namespace GroundTheory.Automorphic

noncomputable section

namespace Reduction

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

def rpowHom (e : ℝ) : {r : ℝ // 0 < r} →* {r : ℝ // 0 < r} where
  toFun s := ⟨s.1 ^ e, Real.rpow_pos_of_pos s.2 e⟩
  map_one' := Subtype.ext (Real.one_rpow e)
  map_mul' s t := Subtype.ext (Real.mul_rpow s.2.le t.2.le)

theorem continuous_rpowHom (e : ℝ) : Continuous (rpowHom e) :=
  (continuous_subtype_val.rpow_const fun s => Or.inl s.2.ne').subtype_mk _


variable (K) in
def posIdeleHom : {r : ℝ // 0 < r} →* IdeleGroup K where
  toFun s := posIdele s.1 s.2
  map_one' := by
    unfold posIdele
    refine Finset.prod_eq_one fun w _ => ?_
    convert map_one (moduleSection (K := K) w)
    exact one_pow _
  map_mul' s t := by
    unfold posIdele
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [← map_mul]
    congr 1
    exact Subtype.ext (by simp only [Positive.val_mul, mul_pow])

theorem posIdeleHom_apply (s : {r : ℝ // 0 < r}) : posIdeleHom K s = posIdele s.1 s.2 := rfl

theorem continuous_posIdeleHom : Continuous (posIdeleHom K) :=
  continuous_posIdele_subtype


variable (K n) in
def scalarUnits : IdeleGroup K →* AdelicGLn.AdelicGL K n :=
  (diagUnits n).comp
    { toFun := fun u _ => u, map_one' := rfl, map_mul' := fun _ _ => rfl }

theorem scalarUnits_apply (u : IdeleGroup K) : scalarUnits K n u = diagUnits n fun _ => u := rfl

theorem continuous_scalarUnits : Continuous (scalarUnits K n) :=
  (continuous_diagUnits n).comp (continuous_pi fun _ => continuous_id)

theorem scalarUnits_mul_comm (u : IdeleGroup K) (g : AdelicGLn.AdelicGL K n) :
    scalarUnits K n u * g = g * scalarUnits K n u := by
  refine Units.ext ?_
  simp only [Units.val_mul, scalarUnits_apply, coe_diagUnits]
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm]


variable (K) in
def centralSection (n : ℕ) : {r : ℝ // 0 < r} →* AdelicGLn.AdelicGL K n :=
  (scalarUnits K n).comp ((posIdeleHom K).comp (rpowHom ((n * Module.finrank ℚ K : ℝ))⁻¹))

theorem continuous_centralSection : Continuous (centralSection K n) :=
  continuous_scalarUnits.comp (continuous_posIdeleHom.comp (continuous_rpowHom _))

theorem centralSection_mul_comm (s : {r : ℝ // 0 < r}) (g : AdelicGLn.AdelicGL K n) :
    centralSection K n s * g = g * centralSection K n s :=
  scalarUnits_mul_comm _ g


variable (K n) in
def detModule : AdelicGLn.AdelicGL K n →* {r : ℝ // 0 < r} :=
  (ideleModule K).comp (AdelicGLn.det K n)

theorem continuous_detModule : Continuous (detModule K n) :=
  continuous_ideleModule.comp (AdelicGLn.continuous_det K n)

theorem mem_normOneGL_iff_detModule {g : AdelicGLn.AdelicGL K n} :
    g ∈ normOneGL (K := K) (n := n) ↔ detModule K n g = 1 := by
  rw [mem_normOneGL]
  exact ⟨fun h => Subtype.ext (h.trans Positive.val_one.symm),
    fun h => (congrArg Subtype.val h).trans Positive.val_one⟩

theorem detModule_centralSection (hn : 0 < n) (s : {r : ℝ // 0 < r}) :
    detModule K n (centralSection K n s) = s := by
  refine Subtype.ext ?_
  have hd0 : 0 < Module.finrank ℚ K := Module.finrank_pos
  have h1 : (detModule K n (centralSection K n s) : ℝ) =
      ∏ _i : Fin n, (ideleModule K (posIdeleHom K (rpowHom ((n * Module.finrank ℚ K : ℝ))⁻¹ s)) : ℝ) := by
    rw [detModule, MonoidHom.comp_apply, centralSection, MonoidHom.comp_apply, MonoidHom.comp_apply,
      scalarUnits_apply, det_diagUnits, map_prod, coe_finset_prod_pos]
  rw [h1, Finset.prod_const, Finset.card_univ, Fintype.card_fin, posIdeleHom_apply,
    ideleModule_posIdele]
  change ((s.1 ^ ((n * Module.finrank ℚ K : ℝ))⁻¹) ^ Module.finrank ℚ K) ^ n = s.1
  rw [← pow_mul, ← Real.rpow_natCast, ← Real.rpow_mul s.2.le]
  have hne : (n * Module.finrank ℚ K : ℝ) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.2 hn.ne') (Nat.cast_ne_zero.2 hd0.ne')
  rw [show ((n * Module.finrank ℚ K : ℝ))⁻¹ * ((Module.finrank ℚ K * n : ℕ) : ℝ) = 1 by
    push_cast; field_simp, Real.rpow_one]

def glNormOneSplitting (hn : 0 < n) :
    AdelicGLn.AdelicGL K n ≃ₜ* normOneGL (K := K) (n := n) × {r : ℝ // 0 < r} :=
  GroundTheory.Variant₂.N1.centralSplitting (detModule K n) continuous_detModule (centralSection K n)
    continuous_centralSection (detModule_centralSection hn) centralSection_mul_comm (normOneGL (K := K) (n := n))
    (fun _ => mem_normOneGL_iff_detModule)

theorem exists_measure_eq_mul_measure_image (hn : 0 < n)
    [SecondCountableTopology (AdelicGLn.AdelicGL K n)] [MeasurableSpace (AdelicGLn.AdelicGL K n)]
    [BorelSpace (AdelicGLn.AdelicGL K n)]
    (μ₁ : Measure (normOneGL (K := K) (n := n))) [μ₁.IsHaarMeasure]
    (μ : Measure (AdelicGLn.AdelicGL K n)) [μ.IsHaarMeasure] :
    ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ ∀ E : Set (normOneGL (K := K) (n := n)), MeasurableSet E →
      μ₁ E = c * μ ((fun p : normOneGL (K := K) (n := n) × {r : ℝ // 0 < r} =>
        (p.1 : AdelicGLn.AdelicGL K n) * centralSection K n p.2) '' (E ×ˢ posRealUnitInterval)) := by
  have : SecondCountableTopology (normOneGL (K := K) (n := n)) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  set Φ : AdelicGLn.AdelicGL K n ≃ₜ* normOneGL (K := K) (n := n) × {r : ℝ // 0 < r} :=
    GroundTheory.Variant₂.N1.centralSplitting (detModule K n) continuous_detModule (centralSection K n)
      continuous_centralSection (detModule_centralSection hn) centralSection_mul_comm
      (normOneGL (K := K) (n := n)) (fun _ => mem_normOneGL_iff_detModule) with hΦ
  have hΦs : ∀ p : normOneGL (K := K) (n := n) × {r : ℝ // 0 < r},
      Φ.symm p = (p.1 : AdelicGLn.AdelicGL K n) * centralSection K n p.2 := fun p => rfl
  have hΦm : Measurable (Φ : AdelicGLn.AdelicGL K n → normOneGL (K := K) (n := n) × {r : ℝ // 0 < r}) :=
    Φ.continuous.measurable
  set lam : Measure (normOneGL (K := K) (n := n) × {r : ℝ // 0 < r}) := μ.map Φ with hlam
  have hlamH : lam.IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map μ Φ
  have hν : posRealMeasure posRealUnitInterval = 1 := posRealMeasure_posRealUnitInterval
  set ρ : Measure (normOneGL (K := K) (n := n)) :=
    Measure.map Prod.fst (lam.restrict (Set.univ ×ˢ posRealUnitInterval)) with hρ
  have hρH : ρ.IsHaarMeasure := isHaarMeasure_map_fst_restrict lam posRealMeasure hν
  have hμ₁ : μ₁ = Measure.haarScalarFactor μ₁ ρ • ρ := Measure.isMulLeftInvariant_eq_smul μ₁ ρ
  refine ⟨(Measure.haarScalarFactor μ₁ ρ : ℝ≥0∞), ENNReal.coe_ne_top, fun E hE => ?_⟩
  have hS : MeasurableSet posRealUnitInterval := measurableSet_posRealUnitInterval
  have hρE : ρ E = μ (Φ ⁻¹' (E ×ˢ posRealUnitInterval)) := by
    rw [hρ, Measure.map_apply measurable_fst hE, Measure.restrict_apply (measurable_fst hE),
      hlam, Measure.map_apply hΦm]
    · congr 1
      ext p
      simp [and_comm]
    · exact (measurable_fst hE).inter (MeasurableSet.univ.prod hS)
  have himg : Φ ⁻¹' (E ×ˢ posRealUnitInterval) =
      (fun p : normOneGL (K := K) (n := n) × {r : ℝ // 0 < r} =>
        (p.1 : AdelicGLn.AdelicGL K n) * centralSection K n p.2) '' (E ×ˢ posRealUnitInterval) := by
    ext g
    constructor
    · intro hg
      exact ⟨Φ g, hg, (hΦs (Φ g)).symm.trans (Φ.symm_apply_apply g)⟩
    · rintro ⟨p, hp, rfl⟩
      show Φ ((p.1 : AdelicGLn.AdelicGL K n) * centralSection K n p.2) ∈ E ×ˢ posRealUnitInterval
      rw [← hΦs p, ContinuousMulEquiv.apply_symm_apply]
      exact hp
  have h1 : μ₁ E = (Measure.haarScalarFactor μ₁ ρ • ρ) E :=
    congrArg (fun m : Measure (normOneGL (K := K) (n := n)) => m E) hμ₁
  rw [h1, Measure.smul_apply, hρE, himg, ENNReal.smul_def, smul_eq_mul]

end Reduction

end

end GroundTheory.Automorphic
end
