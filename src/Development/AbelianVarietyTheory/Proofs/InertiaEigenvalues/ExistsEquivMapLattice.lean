module

public import Formalism.SharpRestriction.LevelLetterCocycles.TwGood
public import Formalism.SharpRestriction.ParamsHeightRankConstant
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CommuteIsNilpotentOfUnipotent

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCharDescent
noncomputable section

open NumberField IsDedekindDomain
open scoped Pointwise

namespace GlobalTheory.TwistChoice

theorem exists_subbasis (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (W ι : Type) [AddCommGroup W]
    [Module O W] (x : ι → W) (htf : ∀ (c : O) (w : W), c ≠ 0 → c • w = 0 → w = 0)
    (hfg : (Submodule.span O (Set.range x)).FG) :
    ∃ S : Finset ι, LinearIndependent O (fun a : S => x a) ∧
      Submodule.span O (x '' S) = Submodule.span O (Set.range x) := by
  classical
  set N := Submodule.span O (Set.range x) with hN
  have hex : ∃ n : ℕ, ∃ S : Finset ι, S.card = n ∧ Submodule.span O (x '' (S : Set ι)) = N := by
    obtain ⟨T, hT⟩ := hfg
    have hc : ∀ t : T, ∃ c : ι →₀ O, (c.sum fun i a => a • x i) = (t : W) := by
      intro t
      have ht : (t : W) ∈ N := by rw [← hT]; exact Submodule.subset_span t.2
      exact (Finsupp.mem_span_range_iff_exists_finsupp).mp ht
    choose c hc using hc
    refine ⟨_, Finset.univ.biUnion (fun t => (c t).support), rfl, le_antisymm ?_ ?_⟩
    · exact Submodule.span_mono (Set.image_subset_range _ _)
    · rw [← hT, Submodule.span_le]
      intro t ht
      rw [show t = ((c ⟨t, ht⟩).sum fun i a => a • x i) from (hc ⟨t, ht⟩).symm, Finsupp.sum]
      refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
      exact ⟨i, Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨⟨t, ht⟩, Finset.mem_univ _, hi⟩), rfl⟩
  obtain ⟨S, hSc, hS⟩ := Nat.find_spec hex
  have hmin : ∀ S' : Finset ι, S'.card < S.card → Submodule.span O (x '' (S' : Set ι)) ≠ N := by
    intro S' hlt heq
    rw [hSc] at hlt
    exact Nat.find_min hex hlt ⟨S', rfl, heq⟩
  refine ⟨S, ?_, hS⟩
  rw [Fintype.linearIndependent_iff]
  intro g hg
  by_contra hne
  push Not at hne
  obtain ⟨i, hi⟩ := hne
  obtain ⟨b, -, hb⟩ := Finset.exists_min_image Finset.univ (fun a => IsDiscreteValuationRing.addVal O (g a)) ⟨i, Finset.mem_univ _⟩
  have hb0 : g b ≠ 0 := by
    intro h0
    have := hb i (Finset.mem_univ _)
    rw [h0, (IsDiscreteValuationRing.addVal_eq_top_iff).mpr rfl, top_le_iff, IsDiscreteValuationRing.addVal_eq_top_iff] at this
    exact hi this
  have hd : ∀ a, ∃ d : O, g a = g b * d := fun a =>
    (IsDiscreteValuationRing.addVal_le_iff_dvd).mp (hb a (Finset.mem_univ _))
  choose d hd using hd
  have hsum : (∑ a, d a • x a) = 0 := by
    apply htf (g b) _ hb0
    rw [Finset.smul_sum]
    simp_rw [smul_smul, ← hd]
    exact hg
  have hdb : d b = 1 := by
    have h1 : g b * 1 = g b * d b := by rw [mul_one, ← hd]
    exact (mul_left_cancel₀ hb0 h1).symm
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ b), hdb, one_smul] at hsum
  have hxb : x b ∈ Submodule.span O (x '' ((S.erase b : Finset ι) : Set ι)) := by
    rw [eq_neg_of_add_eq_zero_left hsum]
    refine Submodule.neg_mem _ (Submodule.sum_mem _ fun a ha => Submodule.smul_mem _ _ (Submodule.subset_span ?_))
    refine ⟨a, ?_, rfl⟩
    rw [Finset.coe_erase, Set.mem_sdiff, Set.mem_singleton_iff]
    refine ⟨a.2, fun h => (Finset.mem_erase.mp ha).1 (Subtype.ext h)⟩
  apply hmin (S.erase b) (Finset.card_erase_lt_of_mem b.2)
  apply le_antisymm
  · rw [← hS]
    exact Submodule.span_mono (Set.image_mono (Finset.coe_subset.mpr (Finset.erase_subset _ _)))
  · rw [← hS, Submodule.span_le]
    rintro _ ⟨a, ha, rfl⟩
    by_cases hab : a = b
    · rw [hab]; exact hxb
    · exact Submodule.subset_span ⟨a, by simp [hab, ha], rfl⟩

section Place

variable {L : Type} [Field L] [NumberField L] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem exists_intMap (e : L →+* FractionRing O) :
    ∃ φ : 𝓞 L →+* O, ∀ x : 𝓞 L, algebraMap O (FractionRing O) (φ x) = e (x : L) := by
  have hint : ∀ x : 𝓞 L, ∃ y : O, algebraMap O (FractionRing O) y = e (x : L) := by
    intro x
    have h2 : IsIntegral O (e (x : L)) :=
      IsIntegral.map_of_comp_eq (Int.castRingHom O) e (RingHom.ext_int _ _) (NumberField.RingOfIntegers.isIntegral_coe x)
    exact IsIntegrallyClosed.isIntegral_iff.mp h2
  have hinj : Function.Injective (algebraMap O (FractionRing O)) := IsFractionRing.injective O (FractionRing O)
  choose f hf using hint
  refine ⟨{ toFun := f, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, hf⟩
  · exact hinj (by simp [hf])
  · intro a b
    exact hinj (by simp [hf])
  · exact hinj (by simp [hf])
  · intro a b
    exact hinj (by simp [hf])

theorem induces_of_ideal (e : L →+* FractionRing O) (v : HeightOneSpectrum (𝓞 L))
    (h : ∀ x : 𝓞 L, x ∈ v.asIdeal ↔ ∃ y ∈ IsLocalRing.maximalIdeal O, algebraMap O (FractionRing O) y = e (x : L))
    (x : L) : v.valuation L x ≤ 1 ↔ e x ∈ (algebraMap O (FractionRing O)).range := by
  obtain ⟨φ, hφ⟩ := exists_intMap e
  have hinj : Function.Injective (algebraMap O (FractionRing O)) := IsFractionRing.injective O (FractionRing O)
  have hm : ∀ a : 𝓞 L, a ∈ v.asIdeal ↔ φ a ∈ IsLocalRing.maximalIdeal O := by
    intro a
    rw [h a]
    constructor
    · rintro ⟨y, hy, hye⟩
      rwa [← hinj (hye.trans (hφ a).symm)]
    · intro ha
      exact ⟨φ a, ha, hφ a⟩
  have he : ∀ a : 𝓞 L, e (algebraMap (𝓞 L) L a) = algebraMap O (FractionRing O) (φ a) := fun a => (hφ a).symm
  constructor
  · intro hx
    obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer (K := L) v x hx
    have hdv : (d : 𝓞 L) ∉ v.asIdeal := d.2
    have hd : IsUnit (φ d) := by
      by_contra hd
      exact hdv ((hm d).mpr ((IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hd)))
    refine ⟨φ n * ((hd.unit⁻¹ : Oˣ) : O), ?_⟩
    have h1 := congrArg e hnd
    rw [map_mul, he, he] at h1
    rw [map_mul, ← h1, mul_assoc, ← map_mul, IsUnit.mul_val_inv, map_one, mul_one]
  · rintro ⟨y, hy⟩
    by_contra hx
    obtain ⟨n, d, hnd | hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_or_mul_eq (K := L) v x
    · have hdv : (d : 𝓞 L) ∉ v.asIdeal := d.2
      apply hx
      have h1 := congrArg (v.valuation L) hnd
      rw [map_mul, (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := L) v).mpr hdv, mul_one] at h1
      rw [h1]
      exact HeightOneSpectrum.valuation_le_one (K := L) v n
    · have hdv : (d : 𝓞 L) ∉ v.asIdeal := d.2
      have hn : n ∈ v.asIdeal := by
        by_contra hn
        apply hx
        have h1 := congrArg (v.valuation L) hnd
        rw [map_mul, (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := L) v).mpr hn,
          (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := L) v).mpr hdv, mul_one] at h1
        exact h1.le
      have h2 := congrArg e hnd
      rw [map_mul, he, he, ← hy, ← map_mul] at h2
      have h3 := hinj h2
      apply hdv
      rw [hm, ← h3]
      exact Ideal.mul_mem_left _ y ((hm n).mp hn)

end Place

theorem exists_coeff_ext (L : Type) [Field L] [NumberField L] [IsGalois ℚ L] (L₀ : IntermediateField ℚ L)
    (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (i : L₀ →+* FractionRing W) (v : HeightOneSpectrum (𝓞 L))
    (h : ∀ x : 𝓞 L₀, algebraMap (𝓞 L₀) (𝓞 L) x ∈ v.asIdeal ↔
      ∃ y ∈ IsLocalRing.maximalIdeal W, algebraMap W (FractionRing W) y = i (x : L₀)) :
    ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O) (_ : Algebra W O)
      (e : L →+* FractionRing O), Function.Injective (algebraMap W O) ∧ Module.Finite W O ∧ IsLocalHom (algebraMap W O) ∧
      (∀ x : L, v.valuation L x ≤ 1 ↔ e x ∈ (algebraMap O (FractionRing O)).range) ∧
      ∀ (x : L₀) (y z : W), i x * algebraMap W (FractionRing W) z = algebraMap W (FractionRing W) y →
        e x * algebraMap O (FractionRing O) (algebraMap W O z) = algebraMap O (FractionRing O) (algebraMap W O y) := by
  classical
  obtain ⟨O, Kf, _, _, _, _, _, ι, j, w, eK, hfr, hcomp, hfin, -, -, hext⟩ :=
    GlobalTheory.exists_complete_dvr_ext_numberField_sqrt W (FractionRing W) L₀ L i (algebraMap L₀ L) 1
  let _ : Algebra W O := j.toAlgebra
  have : IsFractionRing O Kf := hfr
  let τ : Kf ≃ₐ[O] FractionRing O := IsLocalization.algEquiv (nonZeroDivisors O) Kf (FractionRing O)
  have hτ : ∀ y : O, τ (algebraMap O Kf y) = algebraMap O (FractionRing O) y := fun y => τ.commutes y
  let e1 : L →+* FractionRing O := (τ : Kf →+* FractionRing O).comp eK
  have hWinj : Function.Injective (algebraMap W (FractionRing W)) := IsFractionRing.injective W (FractionRing W)
  have hOinj : Function.Injective (algebraMap O (FractionRing O)) := IsFractionRing.injective O (FractionRing O)
  have hjinj : Function.Injective j := by
    intro a b hab
    apply hWinj
    apply ι.injective
    rw [hcomp, hcomp, hab]
  have hjfin : Module.Finite W O := hfin
  have hjint : Algebra.IsIntegral W O := inferInstance
  have : FaithfulSMul W O := (faithfulSMul_iff_algebraMap_injective W O).mpr hjinj
  have hjloc : IsLocalHom (algebraMap W O) := inferInstance
  have hjmem : ∀ a : W, j a ∈ IsLocalRing.maximalIdeal O ↔ a ∈ IsLocalRing.maximalIdeal W := by
    intro a
    rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff]
    exact not_congr (isUnit_map_iff (algebraMap W O) a)
  obtain ⟨ψ, hψ⟩ := exists_intMap (L := L₀) (O := W) i
  obtain ⟨φ1, hφ1⟩ := exists_intMap (L := L) (O := O) e1
  have hφψ : ∀ x : 𝓞 L₀, φ1 (algebraMap (𝓞 L₀) (𝓞 L) x) = j (ψ x) := by
    intro x
    apply hOinj
    rw [hφ1]
    have hc : (((algebraMap (𝓞 L₀) (𝓞 L) x : 𝓞 L) : L)) = algebraMap L₀ L (x : L₀) := rfl
    show τ (eK _) = _
    rw [hc, hext, ← hψ, hcomp, hτ]
  let P' : Ideal (𝓞 L) := (IsLocalRing.maximalIdeal O).comap φ1
  have hP'prime : P'.IsPrime := Ideal.comap_isPrime _ _
  let p : Ideal (𝓞 L₀) := v.asIdeal.comap (algebraMap (𝓞 L₀) (𝓞 L))
  have hover : P'.comap (algebraMap (𝓞 L₀) (𝓞 L)) = p := by
    ext x
    simp only [Ideal.mem_comap, P', p]
    rw [hφψ, hjmem, h x]
    constructor
    · intro hx
      exact ⟨ψ x, hx, hψ x⟩
    · rintro ⟨y, hy, hyx⟩
      rwa [← hWinj (hyx.trans (hψ x).symm)]
  have hv1 : v.asIdeal ∈ Ideal.primesOver p (𝓞 L) := ⟨v.isPrime, ⟨rfl⟩⟩
  have hP1 : P' ∈ Ideal.primesOver p (𝓞 L) := ⟨hP'prime, ⟨hover.symm⟩⟩
  obtain ⟨σ, hσ⟩ := Ideal.exists_comap_galRestrict_eq (𝓞 L₀) L₀ L (𝓞 L) hP1 hv1
  let e : L →+* FractionRing O := e1.comp (σ : L ≃ₐ[L₀] L).toRingHom
  have he_int : ∀ x : 𝓞 L, e (x : L) =
      algebraMap O (FractionRing O) (φ1 (galRestrict (𝓞 L₀) L₀ L (𝓞 L) σ x)) := by
    intro x
    rw [hφ1]
    show e1 (σ (algebraMap (𝓞 L) L x)) = e1 (algebraMap (𝓞 L) L (galRestrict (𝓞 L₀) L₀ L (𝓞 L) σ x))
    rw [algebraMap_galRestrict_apply]
  have hv' : ∀ x : 𝓞 L, x ∈ v.asIdeal ↔
      ∃ y ∈ IsLocalRing.maximalIdeal O, algebraMap O (FractionRing O) y = e (x : L) := by
    intro x
    rw [← hσ]
    simp only [P', Ideal.mem_comap]
    rw [he_int]
    constructor
    · intro hx
      exact ⟨_, hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      rwa [← hOinj hyx]
  refine ⟨O, inferInstance, inferInstance, inferInstance, j.toAlgebra, e, hjinj, hjfin, hjloc,
    fun x => induces_of_ideal e v hv' x, ?_⟩
  intro x y z hxyz
  have hσx : σ (algebraMap L₀ L x) = algebraMap L₀ L x := σ.commutes x
  have key : ι (i x) * algebraMap O Kf (j z) = algebraMap O Kf (j y) := by
    rw [← hcomp, ← hcomp, ← map_mul, hxyz]
  calc e ↑x * algebraMap O (FractionRing O) (algebraMap W O z)
      = τ (ι (i x) * algebraMap O Kf (j z)) := by
        rw [map_mul, hτ]
        show τ (eK (σ (algebraMap L₀ L x))) * _ = _
        rw [hσx, hext]
        try rfl
    _ = algebraMap O (FractionRing O) (algebraMap W O y) := by
        rw [key, hτ]
        try rfl

theorem exists_char_descent {L K G : Type} [Field L] [Field K] [Group G] (e : L →+* K) {n : ℕ} (hn : 0 < n) {z : L}
    (hz : IsPrimitiveRoot z n) (χ : G →* Kˣ) (hχ : ∀ g, χ g ^ n = 1) :
    ∃ ψ : G →* Lˣ, ∀ g, e (ψ g : L) = (χ g : K) := by
  have hinj : Function.Injective e := e.injective
  have : NeZero n := ⟨hn.ne'⟩
  have hez : IsPrimitiveRoot (e z) n := hz.map_of_injective hinj
  have key : ∀ g, ∃ u : Lˣ, e (u : L) = (χ g : K) := by
    intro g
    have h1 : (χ g : K) ^ n = 1 := by
      rw [← Units.val_pow_eq_pow_val, hχ g, Units.val_one]
    obtain ⟨i, -, hi⟩ := hez.eq_pow_of_pow_eq_one h1
    refine ⟨Units.mk0 (z ^ i) (pow_ne_zero _ (hz.ne_zero hn.ne')), ?_⟩
    rw [Units.val_mk0, map_pow, hi]
  choose f hf using key
  refine ⟨{ toFun := f, map_one' := ?_, map_mul' := ?_ }, hf⟩
  · exact Units.ext (hinj (by simp [hf]))
  · intro a b
    exact Units.ext (hinj (by simp [hf]))

end GlobalTheory.TwistChoice

end
end

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions
open scoped TensorProduct

namespace GlobalTheory.TwistChoice

section Semilinear

theorem exists_equiv_map_lattice {O K U U' : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Field K]
    [Algebra O K] [IsFractionRing O K] [AddCommGroup U] [Module K U] [Module O U] [IsScalarTower O K U]
    [AddCommGroup U'] [Module K U'] [Module O U'] [IsScalarTower O K U']
    (A : Submodule O U) (B : Submodule O U') [A.IsFullLattice K] [B.IsFullLattice K]
    (h : Module.finrank K U = Module.finrank K U') :
    ∃ g : U ≃ₗ[K] U', A.map (g.toLinearMap.restrictScalars O) = B := by
  have key : ∀ {V : Type} [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] (C : Submodule O V)
      [C.IsFullLattice K], ∃ c : Module.Basis (Fin (Module.finrank K V)) K V, Submodule.span O (Set.range c) = C := by
    intro V _ _ _ _ C _
    haveI := Submodule.IsLattice.free K C
    haveI := Submodule.IsLattice.finite K C
    let c₀ := Module.finBasis O C
    let c₁ := c₀.extendOfIsFullLattice K
    have hn : Module.finrank K V = Module.finrank O C := by
      rw [Module.finrank_eq_card_basis c₁, Fintype.card_fin]
    refine ⟨c₁.reindex (finCongr hn.symm), ?_⟩
    rw [Module.Basis.range_reindex]
    have h1 : Set.range c₁ = C.subtype '' Set.range c₀ := by
      rw [← Set.range_comp]
      congr 1
      funext i
      exact c₀.extendOfIsFullLattice_apply K i
    rw [h1, ← Submodule.map_span, c₀.span_eq, Submodule.map_top, Submodule.range_subtype]
  obtain ⟨a, ha⟩ := key A
  obtain ⟨b, hb⟩ := key B
  refine ⟨a.equiv b (finCongr h), ?_⟩
  rw [← ha, ← hb, Submodule.map_span, ← Set.range_comp, ← (finCongr h).surjective.range_comp b]
  congr 2
  funext i
  exact Module.Basis.equiv_apply _ _ _ _

theorem exists_semilinear {L V O K U : Type} [Field L] [AddCommGroup V] [Module L V] [Module.Finite L V]
    [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Field K] [Algebra O K] [IsFractionRing O K]
    [AddCommGroup U] [Module K U] [Module O U] [IsScalarTower O K U] (e : L →+* K)
    (S : Set V) (hS : S.Finite) (hspan : Submodule.span L S = ⊤) (B : Submodule O U) [B.IsFullLattice K]
    (h : Module.finrank L V = Module.finrank K U) :
    ∃ f : V →ₛₗ[e] U,
      (∀ (ι : Type) (b : Module.Basis ι L V), LinearIndependent K (fun i => f (b i)) ∧
        Submodule.span K (Set.range fun i => f (b i)) = ⊤) ∧ Submodule.span O (f '' S) = B := by
  classical
  let b₀ := Module.finBasis L V
  let f₀ : V →ₛₗ[e] (Fin (Module.finrank L V) → K) :=
    { toFun := fun x i => e (b₀.repr x i)
      map_add' := fun x y => by funext i; simp
      map_smul' := fun c x => by funext i; simp }
  have hf₀ : ∀ T : Set V, Submodule.span L T = ⊤ → Submodule.span K (f₀ '' T) = ⊤ := by
    intro T hT
    have h1 : ∀ x, f₀ x ∈ Submodule.span K (f₀ '' T) := fun x => by
      have hx : x ∈ Submodule.span L T := hT ▸ Submodule.mem_top
      induction hx using Submodule.span_induction with
      | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
      | zero => rw [map_zero]; exact Submodule.zero_mem _
      | add y z _ _ hy hz => rw [map_add (f := _)]; exact Submodule.add_mem _ hy hz
      | smul c y _ hy => rw [LinearMap.map_smulₛₗ]; exact Submodule.smul_mem _ _ hy
    apply eq_top_iff.mpr
    rw [← (Pi.basisFun K (Fin (Module.finrank L V))).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have heq : (Pi.basisFun K (Fin (Module.finrank L V))) i = f₀ (b₀ i) := by
      ext j
      simp [f₀, Pi.basisFun_apply, Pi.single_apply, Finsupp.single_apply, eq_comm]
    rw [heq]
    exact h1 (b₀ i)
  let A : Submodule O (Fin (Module.finrank L V) → K) := Submodule.span O (f₀ '' S)
  haveI : A.IsFullLattice K :=
    { toIsLattice := Submodule.IsLattice.of_fg _ (Submodule.fg_span (hS.image _))
      span_eq_top := by rw [show A = Submodule.span O (f₀ '' S) from rfl, Submodule.span_span_of_tower, hf₀ S hspan] }
  obtain ⟨g, hg⟩ := exists_equiv_map_lattice (K := K) A B (by rw [← h]; simp)
  refine ⟨g.toLinearMap.comp f₀, fun ι b => ?_, ?_⟩
  · haveI : Finite ι := Module.Finite.finite_basis b
    haveI := Fintype.ofFinite ι
    have h1 : Submodule.span K (Set.range fun i => (g.toLinearMap.comp f₀) (b i)) = ⊤ := by
      have h2 : (Set.range fun i => (g.toLinearMap.comp f₀) (b i)) = g.toLinearMap '' (f₀ '' Set.range b) := by
        rw [← Set.range_comp, ← Set.range_comp]; rfl
      rw [h2, ← Submodule.map_span, hf₀ _ b.span_eq, Submodule.map_top]
      exact g.range
    exact ⟨linearIndependent_of_top_le_span_of_card_eq_finrank h1.ge
      (by rw [← h, Module.finrank_eq_card_basis b]), h1⟩
  · rw [← hg, Submodule.map_span, Set.image_image]
    rfl

theorem form_gen {L V M ι : Type} [Field L] [AddCommGroup V] [Module L V] [AddCommGroup M] [Module ℂ M]
    [FiniteDimensional ℂ M] {σ : L →+* ℂ} (j : V →ₛₗ[σ] M) (b : Module.Basis ι L V)
    (hb : LinearIndependent ℂ (fun i => j (b i)) ∧ Submodule.span ℂ (Set.range fun i => j (b i)) = ⊤)
    (T : Finset M) (hT : Submodule.span ℂ (T : Set M) = ⊤) (hsub : ∀ x ∈ T, x ∈ Set.range j) :
    Module.Finite L V ∧ {x | j x ∈ T}.Finite ∧ Submodule.span L {x | j x ∈ T} = ⊤ := by
  haveI : Finite ι := hb.1.finite
  haveI := Fintype.ofFinite ι
  let B : Module.Basis ι ℂ M := Module.Basis.mk hb.1 hb.2.ge
  have hB : ∀ i, B i = j (b i) := fun i => by simp [B]
  have key : ∀ l : V →ₗ[L] L, ∃ l' : M →ₗ[ℂ] ℂ, ∀ x, l' (j x) = σ (l x) := fun l => by
    refine ⟨B.constr ℂ fun i => σ (l (b i)), fun x => ?_⟩
    conv_lhs => rw [← b.sum_repr x]
    conv_rhs => rw [← b.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, LinearMap.map_smulₛₗ, ← hB, Module.Basis.constr_basis, smul_eq_mul, map_mul, RingHom.id_apply]
  have hinj : Function.Injective j := fun x y hxy => by
    refine b.ext_elem fun i => σ.injective ?_
    obtain ⟨l', hl'⟩ := key (b.coord i)
    have h1 := hl' x
    rw [hxy, hl' y] at h1
    exact h1.symm
  refine ⟨Module.Finite.of_basis b, T.finite_toSet.preimage hinj.injOn, ?_⟩
  by_contra hne
  obtain ⟨l, hl0, hl⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  obtain ⟨l', hl'⟩ := key l
  have h1 : l' = 0 := by
    rw [← LinearMap.ker_eq_top, eq_top_iff, ← hT, Submodule.span_le]
    intro y hy
    obtain ⟨x, rfl⟩ := hsub y hy
    have hx : l x = 0 := hl (Submodule.subset_span hy)
    show l' (j x) = 0
    rw [hl', hx, map_zero]
  refine hl0 (LinearMap.ext fun x => σ.injective ?_)
  rw [← hl', h1]
  simp

theorem baseChange_lattice {A B V : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra A B]
    (hinj : Function.Injective (algebraMap A B)) [AddCommGroup V] [Module (FractionRing A) V] [Module A V]
    [IsScalarTower A (FractionRing A) V] (Λ : Submodule A V) (hfg : Λ.FG)
    (hspan : Submodule.span (FractionRing A) (Λ : Set V) = ⊤) :
    Module.finrank (FractionRing B) (FractionRing B ⊗[A] V) = Module.finrank (FractionRing A) V ∧
      (Submodule.span B ((TensorProduct.mk A (FractionRing B) V 1) '' (Λ : Set V))).IsFullLattice (FractionRing B) := by
  haveI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).2 hinj
  letI : Algebra (FractionRing A) (FractionRing B) := FractionRing.liftAlgebra A (FractionRing B)
  haveI : IsScalarTower A (FractionRing A) (FractionRing B) := FractionRing.isScalarTower_liftAlgebra A (FractionRing B)
  refine ⟨?_, { toIsLattice := Submodule.IsLattice.of_fg _ ?_, span_eq_top := ?_ }⟩
  · rw [← (TensorProduct.AlgebraTensorModule.cancelBaseChange A (FractionRing A) (FractionRing B) (FractionRing B) V).finrank_eq,
      Module.finrank_baseChange, (NChoice.fracEquiv A V).finrank_eq]
  · obtain ⟨T, rfl⟩ := hfg
    rw [← Submodule.map_coe, ← Submodule.span_image, Submodule.span_span_of_tower]
    exact Submodule.fg_span (T.finite_toSet.image _)

  · rw [Submodule.span_span_of_tower, eq_top_iff]
    rintro x -
    induction x using TensorProduct.induction_on with
    | zero => exact Submodule.zero_mem _
    | add y z hy hz => exact Submodule.add_mem _ hy hz
    | tmul a v =>
      obtain ⟨d, hd⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors A) (FractionRing A) (Λ : Set V) v
        (hspan ▸ Submodule.mem_top)
      rw [Submodule.span_eq] at hd
      have hd0 : algebraMap A (FractionRing B) d ≠ 0 :=
        (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective A (FractionRing B))).2 (nonZeroDivisors.coe_ne_zero d)
      have h1 : a ⊗ₜ[A] v = (a * (algebraMap A (FractionRing B) d)⁻¹) • ((1 : FractionRing B) ⊗ₜ[A] ((d : A) • v)) := by
        rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', Algebra.smul_def (d : A), mul_one, smul_eq_mul,
          mul_assoc, inv_mul_cancel₀ hd0, mul_one]
      rw [h1]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hd, rfl⟩)

end Semilinear

section Series

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}
  (Y : NExp D.R D.host D.what₂ D.LL0 N X) (E : IntegralHeckeForms.ExpDat Y)

theorem twOK_one (i : X.Tw) (k : ℕ) : IntegralHeckeForms.TwOK i k ∅ (1 : G D.host.E N.Om →* (X.Ok i k)ˣ) := by
  refine ⟨by simp, by simp, by rw [MonoidHom.ker_one, Subgroup.coe_top]; exact isOpen_univ, fun g g' _ => by simp, fun g => Subgroup.one_mem _, fun v A _ => by simp,
    fun v _ A _ σ _ => rfl⟩

theorem th_fg (h : IntegralHeckeForms.admT4 Y E) (i : X.Tw) (hi : X.NonzeroIndexPlace i) (j : ℕ) (hj : j ∈ Finset.Icc 1 D.R.m) (b : Bool) :
    (IntegralHeckeForms.Th Y i j b (IntegralHeckeForms.SgJ Y E i j b)).FG := by
  have h1 := h i hi j hj b 0 ∅ 1 (twOK_one i 0) _ subset_rfl
  haveI := X.Ok_fin i 0
  haveI : FaithfulSMul (X.O i) (X.Ok i 0) := (faithfulSMul_iff_algebraMap_injective _ _).2 (X.Ok_inj i 0)
  haveI : Module.FaithfullyFlat (X.O i) (X.Ok i 0) := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have h2 : (((Y.MtLat i j b 0 ∅ 1).map (Y.thP i j b 0 ∅ 1)).restrictScalars (X.O i)).FG :=
    ((Y.MtLat_fg i j b 0 ∅ 1).map _).restrictScalars
  let m := TensorProduct.mk (X.O i) (X.Ok i 0) (Y.Fm i j b) 1
  refine Submodule.fg_of_fg_map_injective m (Module.FaithfullyFlat.tensorProduct_mk_injective _) (h2.of_le ?_)
  rw [IntegralHeckeForms.Th, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
  refine h1 (Submodule.subset_span (Set.mem_iUnion₂.2 ⟨a, ha, ?_⟩))
  rw [Y.thPsi_one]
  rfl

theorem exists_basisOf (i : X.Tw) (j : ℕ) (b : Bool) (Sg : Set (Y.Dat i j b)) (h : (IntegralHeckeForms.Th Y i j b Sg).FG) :
    ∃ S : Finset (Y.Dat i j b), IntegralHeckeForms.BasisOf Y i j b Sg S := by
  classical
  have hr : Submodule.span (X.O i) (Set.range fun a : Sg => IntegralHeckeForms.AO Y i j b (Y.th i j b a)) =
      (IntegralHeckeForms.Th Y i j b Sg).map (IntegralHeckeForms.AO Y i j b) := by
    rw [IntegralHeckeForms.Th, Submodule.map_span, Set.image_image, Set.image_eq_range]
  obtain ⟨S, h1, h2⟩ := exists_subbasis (X.O i) (Y.Fm i j b) Sg (fun a => IntegralHeckeForms.AO Y i j b (Y.th i j b a))
    (fun c w hc hw => by
      rw [← algebraMap_smul (FractionRing (X.O i)) c w, smul_eq_zero] at hw
      exact hw.resolve_left ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hc))
    (hr ▸ h.map _)
  refine ⟨S.map (Function.Embedding.subtype _), ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨a', -, rfl⟩ := Finset.mem_map.1 ha
    exact a'.2
  · let e : S ≃ (S.map (Function.Embedding.subtype (· ∈ Sg)) : Finset _) :=
      Equiv.ofBijective (fun a => ⟨a.1.1, Finset.mem_map.2 ⟨a.1, a.2, rfl⟩⟩)
        ⟨fun a a' h => Subtype.ext (Subtype.ext (Subtype.mk.inj h)), fun ⟨y, hy⟩ => by
          obtain ⟨a, ha, rfl⟩ := Finset.mem_map.1 hy
          exact ⟨⟨a, ha⟩, rfl⟩⟩
    exact (linearIndependent_equiv e).1 h1
  · rw [← hr, ← h2, Finset.coe_map, Set.image_image]
    rfl

end Series

end GlobalTheory.TwistChoice

end
