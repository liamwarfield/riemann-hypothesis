module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.GoodPrimesProperties
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.NormByPlaces
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscAF

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FsumEqSum
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem fsum_eq_sum {α M : Type*} [AddCommMonoid M] (s : Set α) (S : Finset α) (f : α → M)
    (hS : ∀ x ∈ s, f x ≠ 0 → x ∈ S) :
    ∑ᶠ x ∈ s, f x = ∑ x ∈ S, s.indicator f x := by
  rw [finsum_mem_def]
  apply finsum_eq_sum_of_support_subset
  intro x hx
  simp only [Function.mem_support, ne_eq, Set.indicator_apply_eq_zero, Classical.not_imp] at hx
  exact hS x hx.1 hx.2

noncomputable def Emin (c : ι) (v : AddValuation (Ω c) (WithTop ℤ)) : ℤ :=
  ⨅ j : {j // d.w j c ≠ 0}, d.ord c v d.wL (d.w j c)

noncomputable def Ep (h : d.S1) (c : ι) (p : Ideal (KTp K d.D d.N)) : ℤ :=
  ∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.GoodP c p),
    (d.fze h c w : ℤ) * d.Emin c (d.Wres c w)

theorem hh_good_adm (hd : d.AxH 𝒜) (h : d.S1) {c : ι} {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne)
    {w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)} (hw : w ∈ d.GoodP c p) :
    d.admitted c (d.Wres c w) ∧ IsTrivOn K (d.Wres c w) := by
  rcases d.PlaceTrivialOrPositive hd h c p hp w hw.1 with h1 | h2
  · obtain ⟨a, ha, hne⟩ := hw.2
    exact absurd (h1 a ha) hne
  · exact ⟨h2.1, h2.2.1⟩

theorem good_finite (hd : d.AxH 𝒜) (h : d.S1) (c : ι) {p : Ideal (KTp K d.D d.N)}
    (hp : p ∈ d.HtOne) : (d.GoodP c p).Finite :=
  have hOverFinite : (d.OverP c p).Finite := by
    letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
    haveI : FiniteDimensional (d.KT c) (OmS (Ω c) d.D d.N) :=
      d.KT_finiteDimensional hd c
    let e : KTf K d.D d.N ≃+* d.KT c :=
      (d.KTtoS h c).rangeRestrictFieldEquiv.trans (RingEquiv.subfieldCongr (d.KTtoS_fieldRange h c))
    have he : (algebraMap (KTf K d.D d.N) (OmS (Ω c) d.D d.N)).comp e.symm.toRingHom =
        (RingEquiv.refl (OmS (Ω c) d.D d.N)).toRingHom.comp (algebraMap (d.KT c) (OmS (Ω c) d.D d.N)) := by
      refine RingHom.ext fun x => ?_
      change d.KTtoS h c (e.symm x) = (x : OmS (Ω c) d.D d.N)
      exact congrArg (fun u : d.KT c => (u : OmS (Ω c) d.D d.N)) (e.apply_symm_apply x)
    haveI : FiniteDimensional (KTf K d.D d.N) (OmS (Ω c) d.D d.N) :=
      Module.Finite.of_equiv_equiv e.symm (RingEquiv.refl _) he
    have hmap : ∀ x : KTp K d.D d.N,
        algebraMap (KTf K d.D d.N) (OmS (Ω c) d.D d.N)
          (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) x) = d.sH c x := by
      intro x
      exact IsFractionRing.lift_algebraMap (h c) x
    have hOver : d.OverP c p =
        HNm.OverR (R := KTp K d.D d.N) (F := KTf K d.D d.N)
          (L := OmS (Ω c) d.D d.N) p := by
      ext w
      simp only [Data.OverP, HNm.OverR, Set.mem_setOf_eq, hmap]
    obtain ⟨hprime, hh⟩ := hp
    haveI := hprime
    rw [hOver]
    exact (HNm.local_norm (R := KTp K d.D d.N) (F := KTf K d.D d.N)
      (L := OmS (Ω c) d.D d.N) p hh (d.gen p) (d.gen_span ⟨hprime, hh⟩) 1
      one_ne_zero).1
  hOverFinite.subset (fun _ hw => hw.1)

theorem w_mem_WW (hd : d.AxH 𝒜) (j : Fin (d.N + 1)) : d.w j ∈ d.WW := by
  rw [hd.WW_span]
  exact Submodule.subset_span ⟨j, rfl⟩

theorem Emin_nonneg (hd : d.AxH 𝒜) (c : ι) (v : AddValuation (Ω c) (WithTop ℤ)) (hv : d.admitted c v) :
    0 ≤ d.Emin c v := by
  haveI : Nonempty {j // d.w j c ≠ 0} := ⟨⟨d.jc c, hd.w_base c⟩⟩
  unfold Emin
  exact le_ciInf fun j => hd.ord_nonneg_WW c v hv (d.w j.1) (w_mem_WW d hd j.1) j.2

theorem nP_split (hd : d.AxH 𝒜) (h : d.S1) (c : ι) {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne)
    (f : A c) : d.nP h c d.wL f p = d.nPMM h c f p + d.Ep h c p := by
  unfold nP nPMM Ep
  rw [← finsum_mem_add_distrib (good_finite d hd h c hp)]
  refine finsum_congr fun w => finsum_congr fun _ => ?_
  simp only [ordMM, Emin]
  ring

theorem Ep_nonneg (hd : d.AxH 𝒜) (h : d.S1) (c : ι) {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne) :
    0 ≤ d.Ep h c p := by
  unfold Ep
  exact finsum_nonneg fun w => finsum_nonneg fun hw =>
    mul_nonneg (Nat.cast_nonneg _) (Emin_nonneg d hd c _ (hh_good_adm d hd h hp hw).1)

theorem nP_nonneg (hd : d.AxH 𝒜) (h : d.S1) (c : ι) {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne)
    (G : WT) (f : A c) (hf : ∀ v, d.admitted c v → 0 ≤ d.ord c v G f) : 0 ≤ d.nP h c G f p := by
  unfold nP
  exact finsum_nonneg fun w => finsum_nonneg fun hw =>
    mul_nonneg (Nat.cast_nonneg _) (hf _ (hh_good_adm d hd h hp hw).1)

theorem Ep_le (hd : d.AxH 𝒜) (h : d.S1) (hF1d : d.TrivialPlaceHyp) (c : ι) {p : Ideal (KTp K d.D d.N)}
    (hp : p ∈ d.HtOne) :
    (d.Ep h c p : ℝ) ≤ d.cc / (2 * d.i) * d.nP h c (d.n1 • d.wde) (d.et c) p := by
  have hs := d.good_finite hd h c hp
  unfold Ep nP
  rw [finsum_mem_eq_finite_toFinset_sum _ hs, finsum_mem_eq_finite_toFinset_sum _ hs]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun w hw => ?_
  rw [Set.Finite.mem_toFinset] at hw
  have ha := d.hh_good_adm hd h hp hw
  have := hF1d c _ ha.1 ha.2
  have hf : (0 : ℝ) ≤ d.fze h c w := Nat.cast_nonneg _
  calc (d.fze h c w : ℝ) * (d.Emin c (d.Wres c w) : ℝ)
      ≤ (d.fze h c w : ℝ) * (d.cc / (2 * d.i) * d.ord c (d.Wres c w) (d.n1 • d.wde) (d.et c)) :=
        mul_le_mul_of_nonneg_left this hf
    _ = _ := by ring

theorem Ep_ne (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (f : A c) (hf : f ∈ 𝒜 c d.wL) (hf0 : f ≠ 0) :
    {p | p ∈ d.HtOne ∧ d.Ep h c p ≠ 0}.Finite := by
  refine ((d.good_primes_properties hd h c).2.2.1 d.wL f hf hf0).union ((d.good_primes_properties hd h c).2.2.2 f hf hf0)
    |>.subset ?_
  rintro p ⟨hp, hE⟩
  by_contra hno
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_and, not_not] at hno
  have := d.nP_split hd h c hp f
  rw [hno.1 hp, hno.2 hp] at this
  omega

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscA
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscAG
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField IsDedekindDomain

theorem prod_zpow_eq {ι G : Type*} [CommGroupWithZero G] {x : G} (hx : x ≠ 0) (s : Finset ι)
    (f : ι → ℤ) : ∏ i ∈ s, x ^ f i = x ^ ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.prod_insert hj, Finset.sum_insert hj, ih, zpow_add₀ hx]

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem disc_at (hd : d.AxH 𝒜) (h : d.S1) (la : HeightOneSpectrum (𝓞 K)) :
    ∃ n t : ℕ, ∃ N : ℤ, (d.htOf hd h).Ila la = n ∧ d.NlaG h d.wF hd.a4.choose la = N ∧
      ∃ u : Op d.D d.N la, IsUnit u ∧ d.De hd h =
        (algebraMap K (KTf K d.D d.N) ((unif la : 𝓞 K) : K)) ^ (((2 * n + t : ℕ) : ℤ) - 2 * N) *
          OpToKT d.D d.N la u := by
  classical
  letI : ∀ c, Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := fun c => (d.KTtoS h c).toAlgebra
  letI : ∀ c, Algebra (Op d.D d.N la) (OmS (Ω c) d.D d.N) := fun c => d.algOp h la c
  letI := algOpKT (K := K) d.D d.N la
  haveI := Op_isDVR (K := K) d.D d.N la
  haveI := isFractionRing_Op (K := K) d.D d.N la
  have hF := fun c => d.comp_facts hd h la c
  haveI : ∀ c, IsScalarTower (Op d.D d.N la) (KTf K d.D d.N) (OmS (Ω c) d.D d.N) :=
    fun c => (hF c).2.1
  haveI : ∀ c, FiniteDimensional (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := fun c => (hF c).2.2.1
  haveI : ∀ c, Algebra.IsSeparable (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := fun c => (hF c).2.2.2.1
  let n : ∀ c, AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ) → ℤ := fun c w =>
    d.ord c (d.Wres c w) d.wF (hd.a4.choose c)
  choose g hg0 hgw hgiff using fun c => d.comp_g hd h la c (n c)
  have hset : d.AdmissibleOmegaFamiliesAtPrimeOfSection hd.a4.choose la =
      {y | ∀ c, g c * y c ∈ integralClosure (Op d.D d.N la) (OmS (Ω c) d.D d.N)} := by
    ext y
    simp only [AdmissibleOmegaFamiliesAtPrimeOfSection, Set.mem_setOf_eq]
    exact forall_congr' fun c => hgiff c (y c)
  have hb : ∀ k c, g c * d.bvecG hd.sel hd.a4.choose k c ∈
      integralClosure (Op d.D d.N la) (OmS (Ω c) d.D d.N) := fun k c =>
    (hgiff c _).mp (fun w hw => d.b_mem hd h la k c w hw)
  obtain ⟨nn, t, u, hlen, hdisc⟩ := HDiscLat.lattice_main (R := Op d.D d.N la)
    (F := KTf K d.D d.N) (unifOp_irreducible d.D d.N la) g hg0 (d.del_eq hd h)
    (d.bvecG hd.sel hd.a4.choose) hb (d.b_linIndep hd h)
  choose uN huN hN using fun c => d.comp_norm hd h la c (hg0 c) (n c) (hgw c)
  let Nc : ι → ℤ := fun c => ∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ))
    (_ : w ∈ d.PlOver la c), (d.fze h c w : ℤ) * n c w
  have hfin : ∀ c, (d.PlOver la c).Finite := fun c => by
    obtain ⟨i1, i2, i3, i4, i5, i6⟩ := hF c
    rw [d.plOver_eq h la c]
    exact ValPl.placesOver_finite (O := Op d.D d.N la) (F := KTf K d.D d.N)
      (L := OmS (Ω c) d.D d.N)
  refine ⟨nn, t, ∑ c, Nc c, ?_, ?_, ?_⟩
  · change Module.length (Op d.D d.N la)
      (↥(Submodule.span (Op d.D d.N la) (d.AdmissibleOmegaFamiliesAtPrimeOfSection hd.a4.choose la)) ⧸
        (Submodule.span (Op d.D d.N la) (Set.range (d.bvecG hd.sel hd.a4.choose))).comap
          (Submodule.span (Op d.D d.N la) (d.AdmissibleOmegaFamiliesAtPrimeOfSection hd.a4.choose la)).subtype) = nn
    rw [hset]
    exact hlen
  · simp only [NlaG, Nc]
    push_cast
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [finsum_mem_eq_finite_toFinset_sum _ (hfin c), finsum_mem_eq_finite_toFinset_sum _ (hfin c)]
    push_cast
    rfl
  · set X := OpToKT d.D d.N la (unifOp d.D d.N la) with hX
    have hX0 : X ≠ 0 := (map_ne_zero_iff _ (OpToKT_injective d.D d.N la)).mpr
      (unifOp_irreducible d.D d.N la).ne_zero
    let U : (Op d.D d.N la)ˣ := ∏ c, (huN c).unit
    have hprod : ∏ c, Algebra.norm (KTf K d.D d.N) (g c) =
        X ^ (∑ c, Nc c) * OpToKT d.D d.N la (U : Op d.D d.N la) := by
      rw [Finset.prod_congr rfl fun c _ => hN c, Finset.prod_mul_distrib, prod_zpow_eq hX0,
        ← map_prod]
      congr 2
      simp only [U, Units.coe_prod, IsUnit.unit_spec]
    rw [hprod] at hdisc
    refine ⟨↑(u * U⁻¹ * U⁻¹), Units.isUnit _, ?_⟩
    rw [algK_unif, ← hX]
    set V := OpToKT d.D d.N la (U : Op d.D d.N la)
    set V' := OpToKT d.D d.N la ((U⁻¹ : (Op d.D d.N la)ˣ) : Op d.D d.N la)
    have hU : V * V' = 1 := by
      simp only [V, V']
      rw [← map_mul, Units.mul_inv, map_one]
    set Y := X ^ (∑ c, Nc c)
    have hY : Y ≠ 0 := zpow_ne_zero _ hX0
    have h2 : X ^ (2 * ∑ c, Nc c) = Y ^ 2 := by
      rw [mul_comm, zpow_mul]
      norm_cast
    have hone : (Y * V) ^ 2 * ((Y ^ 2)⁻¹ * V' * V') = 1 := by
      calc (Y * V) ^ 2 * ((Y ^ 2)⁻¹ * V' * V') = (Y ^ 2 * (Y ^ 2)⁻¹) * ((V * V') * (V * V')) := by
            ring
        _ = 1 := by rw [mul_inv_cancel₀ (pow_ne_zero 2 hY), hU]; ring
    have hdisc' : d.De hd h * (Y * V) ^ 2 =
        OpToKT d.D d.N la ↑u * X ^ (2 * nn + t) := by
      rw [← map_pow, ← map_mul]
      exact hdisc
    rw [zpow_sub₀ hX0, zpow_natCast, h2, Units.val_mul, Units.val_mul, map_mul, map_mul]
    calc d.De hd h = d.De hd h * ((Y * V) ^ 2 * ((Y ^ 2)⁻¹ * V' * V')) := by rw [hone, mul_one]
      _ = (d.De hd h * (Y * V) ^ 2) * ((Y ^ 2)⁻¹ * V' * V') := by ring
      _ = _ := by rw [hdisc', div_eq_mul_inv]; ring

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem disc_lattice (hd : d.AxH 𝒜) (h : d.S1) :
    d.De hd h ≠ 0 ∧ ∀ la, (d.htOf hd h).Ila la ≠ ⊤ ∧
      2 * d.IL h hd.sel hd.a4.choose la ≤
        d.gOrd la (d.De hd h) + 2 * d.NlaG h d.wF hd.a4.choose la := by
  have key : ∀ la : IsDedekindDomain.HeightOneSpectrum (𝓞 K), (d.htOf hd h).Ila la ≠ ⊤ ∧ d.De hd h ≠ 0 ∧
      2 * d.IL h hd.sel hd.a4.choose la ≤
        d.gOrd la (d.De hd h) + 2 * d.NlaG h d.wF hd.a4.choose la := by
    intro la
    obtain ⟨n, t, N, hI, hN, u, hu, hDe⟩ := d.disc_at hd h la
    have hIL : d.IL h hd.sel hd.a4.choose la = (((d.htOf hd h).Ila la).toNat : ℝ) := rfl
    refine ⟨by rw [hI]; exact ENat.coe_ne_top n, ?_, ?_⟩
    · rw [hDe, algK_unif]
      exact mul_ne_zero (zpow_ne_zero _ ((map_ne_zero_iff _ (OpToKT_injective d.D d.N la)).mpr
        (unifOp_irreducible d.D d.N la).ne_zero))
        ((map_ne_zero_iff _ (OpToKT_injective d.D d.N la)).mpr hu.ne_zero)
    · rw [hIL, hI, d.gOrd_eq la hu hDe, hN, ENat.toNat_natCast]
      push_cast
      have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
      linarith
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 K)
  let la0 : IsDedekindDomain.HeightOneSpectrum (𝓞 K) :=
    ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField K)⟩
  exact ⟨(key la0).2.1, fun la => ⟨(key la).1, (key la).2.2⟩⟩

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end
