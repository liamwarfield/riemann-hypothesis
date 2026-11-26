module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.DePres
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.DiscProduct
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.DiscHadamard
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HFour

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.OmPoly
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FprodNeZero
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.UnitAtIntAt
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.DiscLocal
set_option linter.style.haveILetI false

namespace ReciprocityTheory.ChartRestriction.G.T0

namespace HDiscOmL

open IsDedekindDomain IsLocalRing Module

variable {R F : Type} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] [Field F]
  [Algebra R F] [IsFractionRing R F]
  {ι : Type} [Fintype ι] [DecidableEq ι] {L : ι → Type} [∀ c, Field (L c)] [∀ c, Algebra F (L c)]
  [∀ c, FiniteDimensional F (L c)] [∀ c, Algebra.IsSeparable F (L c)]

omit [IsDomain R] [UniqueFactorizationMonoid R] [IsFractionRing R F] in
theorem prod_zpow {κ G : Type*} [CommGroupWithZero G] {x : G} (hx : x ≠ 0) (s : Finset κ)
    (f : κ → ℤ) : ∏ i ∈ s, x ^ f i = x ^ ∑ i ∈ s, f i := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.prod_cons, Finset.sum_cons, ih, zpow_add₀ hx]

theorem disc_local (p : Ideal R) [p.IsPrime] (hp : p.height = 1) (g : R) (hg : p = Ideal.span {g})
    (n : ∀ c, AddValuation (L c) (WithTop ℤ) → ℤ)
    {m : ℕ} (hm : m = ∑ c, finrank F (L c)) (b : Fin m → ∀ c, L c) (hli : LinearIndependent F b)
    (hb : ∀ k c, ∀ w ∈ HNm.OverR (R := R) (F := F) (L := L c) p,
      0 ≤ w (b k c) + (n c w : WithTop ℤ)) :
    ∃ a s : R, s ∉ p ∧
      (Matrix.of fun k l : Fin m => ∑ c, Algebra.trace F (L c) (b k c * b l c)).det *
        algebraMap R F g ^ (2 * ∑ c, ∑ᶠ (w : AddValuation (L c) (WithTop ℤ))
          (_ : w ∈ HNm.OverR (R := R) (F := F) (L := L c) p), (HNm.fz (F := F) w : ℤ) * n c w) *
        algebraMap R F s =
        algebraMap R F a := by
  classical
  let O := Localization.AtPrime p
  letI : Algebra O F := IsLocalization.localizationAlgebraOfSubmonoidLe O F p.primeCompl
    (nonZeroDivisors R) (Ideal.primeCompl_le_nonZeroDivisors p)
  haveI : IsScalarTower R O F := IsLocalization.localization_isScalarTower_of_submonoid_le O F
    p.primeCompl (nonZeroDivisors R) (Ideal.primeCompl_le_nonZeroDivisors p)
  haveI : IsFractionRing O F :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization p.primeCompl O F
  obtain ⟨hdvr, hirr⟩ := ValUFD.loc_dvr p hp g hg
  haveI := hdvr
  letI : ∀ c, Algebra O (L c) := fun c => ((algebraMap F (L c)).comp (algebraMap O F)).toAlgebra
  haveI : ∀ c, IsScalarTower O F (L c) := fun c => IsScalarTower.of_algebraMap_eq' rfl
  letI : ∀ c, Algebra R (L c) := fun c => ((algebraMap F (L c)).comp (algebraMap R F)).toAlgebra
  haveI : ∀ c, IsScalarTower R O (L c) := fun c => IsScalarTower.of_algebraMap_eq (fun x => by
    show algebraMap F (L c) (algebraMap R F x) =
      algebraMap F (L c) (algebraMap O F (algebraMap R O x))
    rw [IsScalarTower.algebraMap_apply R O F x])
  have hded : ∀ c, IsDedekindDomain (integralClosure O (L c)) := fun c =>
    (ReciprocityTheory.MultiplicativeHeights.Closed.dedekindRank O F (L c)).1
  have hfr : ∀ c, IsFractionRing (integralClosure O (L c)) (L c) := fun c =>
    integralClosure.isFractionRing_of_finite_extension F (L c)
  have hset : ∀ c, ValPl.PlacesOver O (L c) = HNm.OverR (R := R) (F := F) (L := L c) p := fun c => by
    ext w
    simp only [ValPl.PlacesOver, HNm.OverR, Set.mem_ofPred_eq]
    rw [← ValPl.placesOver_iff_loc (R := R) p w]
    rfl
  have hG : ∀ c, ∃ gc : L c, gc ≠ 0 ∧ (∀ w ∈ ValPl.PlacesOver O (L c), w gc = n c w) ∧
      ∀ y, (∀ w ∈ ValPl.PlacesOver O (L c), 0 ≤ w y + (n c w : WithTop ℤ)) ↔
        gc * y ∈ integralClosure O (L c) := fun c => by
    haveI := hded c
    haveI := hfr c
    obtain ⟨gc, hg0, hgv⟩ := HDiscVal.exists_val_eq O F (n c)
    refine ⟨gc, hg0, hgv, fun y => ?_⟩
    rw [HDiscVal.mem_integralClosure_iff O F]
    refine forall₂_congr fun w hw => ?_
    rw [AddValuation.map_mul, hgv w hw, add_comm]
  choose gc hgc0 hgcv hgciff using hG
  have hbI : ∀ k c, gc c * b k c ∈ integralClosure O (L c) := fun k c =>
    (hgciff c _).mp (fun w hw => hb k c w (hset c ▸ hw))
  obtain ⟨nn, t, u, -, hdisc⟩ := HDiscLat.lattice_main (R := O) (F := F) hirr gc hgc0 hm b hbI hli
  set Nc : ι → ℤ := fun c => ∑ᶠ (w : AddValuation (L c) (WithTop ℤ))
    (_ : w ∈ HNm.OverR (R := R) (F := F) (L := L c) p), (HNm.fz (F := F) w : ℤ) * n c w with hNc
  have hN : ∀ c, ∃ uc : O, IsUnit uc ∧ Algebra.norm F (gc c) =
      algebraMap R F g ^ Nc c * algebraMap O F uc := fun c => by
    haveI := hded c
    haveI := hfr c
    obtain ⟨uc, huc, hn⟩ := ValPl.norm_eq_places (O := O) (F := F) (gc c) (hgc0 c) hirr
    refine ⟨uc, huc, ?_⟩
    rw [hn, ← IsScalarTower.algebraMap_apply R O F g, hset c]
    congr 2
    refine finsum_congr fun w => finsum_congr fun hw => ?_
    rw [← hset c] at hw
    rw [hgcv c w hw, WithTop.untopD_coe]
    rfl
  choose uc huc hNe using hN
  set X := algebraMap R F g with hX
  have hX0 : X ≠ 0 := by
    rw [hX, map_ne_zero_iff _ (IsFractionRing.injective R F)]
    rintro rfl
    have : p = ⊥ := by rw [hg, Ideal.span_singleton_eq_bot]
    subst this
    simp at hp
  let U : Oˣ := ∏ c, (huc c).unit
  have hprod : ∏ c, Algebra.norm F (gc c) = X ^ (∑ c, Nc c) * algebraMap O F (U : O) := by
    rw [Finset.prod_congr rfl fun c _ => hNe c, Finset.prod_mul_distrib, HDiscOmL.prod_zpow hX0,
      ← map_prod]
    congr 2
    simp only [U, Units.coe_prod, IsUnit.unit_spec]
  rw [hprod] at hdisc
  set Dt := (Matrix.of fun k l : Fin m => ∑ c, Algebra.trace F (L c) (b k c * b l c)).det with hDt
  obtain ⟨⟨a, s⟩, has⟩ := IsLocalization.mk'_surjective p.primeCompl
    ((u : O) * ((algebraMap R O g) ^ (2 * nn + t)) * ((U⁻¹ : Oˣ) : O) * ((U⁻¹ : Oˣ) : O))
  refine ⟨a, s, s.2, ?_⟩
  have hsF : algebraMap O F (IsLocalization.mk' O a s) * algebraMap R F s = algebraMap R F a := by
    rw [IsScalarTower.algebraMap_apply R O F s, IsScalarTower.algebraMap_apply R O F a, ← map_mul,
      IsLocalization.mk'_spec]
  simp only at has
  rw [← hsF, has]
  congr 1
  set V := algebraMap O F (U : O)
  set V' := algebraMap O F ((U⁻¹ : Oˣ) : O)
  have hU : V * V' = 1 := by
    simp only [V, V']
    rw [← map_mul, Units.mul_inv, map_one]
  have h2 : X ^ (2 * ∑ c, Nc c) = (X ^ (∑ c, Nc c)) ^ 2 := by
    rw [mul_comm, zpow_mul]
    norm_cast
  have e1 : algebraMap O F ((u : O) * (algebraMap R O g) ^ (2 * nn + t) * ((U⁻¹ : Oˣ) : O) *
      ((U⁻¹ : Oˣ) : O)) = algebraMap O F ((u : O) * (algebraMap R O g) ^ (2 * nn + t)) * V' * V' := by
    simp only [V', map_mul]
  rw [h2, e1, ← hdisc]
  calc Dt * (X ^ ∑ c, Nc c) ^ 2 = Dt * (X ^ ∑ c, Nc c) ^ 2 * (V * V') * (V * V') := by
        rw [hU]; ring
    _ = Dt * ((X ^ ∑ c, Nc c) * V) ^ 2 * V' * V' := by ring

end HDiscOmL

end ReciprocityTheory.ChartRestriction.G.T0
end

set_option linter.style.haveILetI false

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

namespace LocAt

variable {R F : Type*} [CommRing R] [IsDomain R] [Field F] [Algebra R F] [IsFractionRing R F]

def IntAt (p : Ideal R) (x : F) : Prop :=
  ∃ a s : R, s ∉ p ∧ x * algebraMap R F s = algebraMap R F a

def UnitAt (p : Ideal R) (x : F) : Prop :=
  ∃ a s : R, a ∉ p ∧ s ∉ p ∧ x * algebraMap R F s = algebraMap R F a

variable {p : Ideal R} [hP : p.IsPrime]
include hP

omit [IsDomain R] [IsFractionRing R F] in
theorem intAt_mul {x y : F} (hx : IntAt p x) (hy : IntAt p y) : IntAt p (x * y) := by
  obtain ⟨a, s, hs, hxs⟩ := hx
  obtain ⟨b, t, ht, hyt⟩ := hy
  refine ⟨a * b, s * t, fun h => (hP.mem_or_mem h).elim hs ht, ?_⟩
  rw [map_mul, map_mul, ← hxs, ← hyt]
  ring

omit [IsDomain R] [IsFractionRing R F] in
theorem unitAt_mul {x y : F} (hx : UnitAt p x) (hy : UnitAt p y) : UnitAt p (x * y) := by
  obtain ⟨a, s, ha, hs, hxs⟩ := hx
  obtain ⟨b, t, hb, ht, hyt⟩ := hy
  refine ⟨a * b, s * t, fun h => (hP.mem_or_mem h).elim ha hb,
    fun h => (hP.mem_or_mem h).elim hs ht, ?_⟩
  rw [map_mul, map_mul, ← hxs, ← hyt]
  ring

omit [IsDomain R] [IsFractionRing R F] in
theorem unitAt_one : UnitAt p (1 : F) := by
  have h1 : (1 : R) ∉ p := fun h => hP.ne_top ((Ideal.eq_top_iff_one p).mpr h)
  exact ⟨1, 1, h1, h1, by simp⟩

omit [IsDomain R] [IsFractionRing R F] in
theorem unitAt_intAt {x : F} (hx : UnitAt p x) : IntAt p x := by
  obtain ⟨a, s, _, hs, h⟩ := hx
  exact ⟨a, s, hs, h⟩

omit [IsDomain R] [IsFractionRing R F] in
theorem unitAt_alg {r : R} (hr : r ∉ p) : UnitAt p (algebraMap R F r) := by
  have h1 : (1 : R) ∉ p := fun h => hP.ne_top ((Ideal.eq_top_iff_one p).mpr h)
  exact ⟨r, 1, hr, h1, by simp⟩

theorem unitAt_inv {x : F} (hx : UnitAt p x) : UnitAt p x⁻¹ := by
  obtain ⟨a, s, ha, hs, h⟩ := hx
  refine ⟨s, a, hs, ha, ?_⟩
  have ha0 : algebraMap R F a ≠ 0 := by
    intro h0
    apply ha
    have h00 : a = 0 := IsFractionRing.injective R F (by rw [h0, map_zero])
    rw [h00]
    exact p.zero_mem
  have hx0 : x ≠ 0 := by
    rintro rfl
    apply ha0
    rw [← h, zero_mul]
  rw [← h, ← mul_assoc, inv_mul_cancel₀ hx0, one_mul]

omit [IsDomain R] [IsFractionRing R F] in
theorem unitAt_pow {x : F} (hx : UnitAt p x) (n : ℕ) : UnitAt p (x ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact unitAt_one
  | succ n ih => rw [pow_succ]; exact unitAt_mul ih hx

theorem unitAt_zpow {x : F} (hx : UnitAt p x) (n : ℤ) : UnitAt p (x ^ n) := by
  cases n with
  | ofNat n =>
    show UnitAt p (x ^ (n : ℤ))
    rw [zpow_natCast]
    exact unitAt_pow hx n
  | negSucc n =>
    rw [zpow_negSucc]
    exact unitAt_inv (unitAt_pow hx (n + 1))

omit [IsDomain R] [IsFractionRing R F] in
theorem unitAt_prod {κ : Type*} (s : Finset κ) (f : κ → F) (hf : ∀ i ∈ s, UnitAt p (f i)) :
    UnitAt p (∏ i ∈ s, f i) := by
  classical
  revert hf
  refine Finset.induction_on s ?_ ?_
  · intro _
    rw [Finset.prod_empty]
    exact unitAt_one
  · intro i s hi ih hf
    rw [Finset.prod_insert hi]
    exact unitAt_mul (hf i (Finset.mem_insert_self i s))
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

end LocAt

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem gen_prime' {q : Ideal (KTp K d.D d.N)} (hq : q ∈ d.HtOne) : Prime (d.gen q) :=
  ValUFD.gen_prime (fun p hp hh => d.gen_span ⟨hp, hh⟩) hq

theorem gen_not_mem {p q : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne) (hq : q ∈ d.HtOne)
    (hqp : q ≠ p) : d.gen q ∉ p := by
  intro hm
  rw [d.gen_span hp, Ideal.mem_span_singleton] at hm
  have e := (ValUFD.gen_dvd_iff (fun p hp hh => d.gen_span ⟨hp, hh⟩) hp (d.gen_prime' hq)).mp hm
  exact hqp (by rw [e, ← d.gen_span hq])

theorem split_at (E : Ideal (KTp K d.D d.N) → ℤ) (hE : {q | q ∈ d.HtOne ∧ E q ≠ 0}.Finite)
    {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne) :
    ∃ V : KTf K d.D d.N, LocAt.UnitAt p V ∧
      (∏ᶠ (q : Ideal (KTp K d.D d.N)) (_ : q ∈ d.HtOne),
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen q) ^ E q) =
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ E p * V := by
  haveI := hp.1
  have hfin : ((d.HtOne \ {p}) ∩ Function.mulSupport
      (fun q => algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen q) ^ E q)).Finite := by
    refine hE.subset ?_
    rintro q ⟨⟨hq, _⟩, hq1⟩
    refine ⟨hq, fun h0 => (Function.mem_mulSupport.mp hq1) ?_⟩
    simp [h0]
  refine ⟨∏ᶠ (q : Ideal (KTp K d.D d.N)) (_ : q ∈ d.HtOne \ {p}), algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen q) ^ E q, ?_, ?_⟩
  · rw [← finprod_mem_inter_mulSupport, finprod_mem_eq_finite_toFinset_prod _ hfin]
    apply LocAt.unitAt_prod
    intro q hq
    rw [Set.Finite.mem_toFinset] at hq
    obtain ⟨⟨hq1, hq2⟩, _⟩ := hq
    exact LocAt.unitAt_zpow
      (LocAt.unitAt_alg (d.gen_not_mem hp hq1 (fun h => hq2 (Set.mem_singleton_iff.mpr h)))) _
  · have hins : d.HtOne = insert p (d.HtOne \ {p}) := by
      ext x
      by_cases hx : x = p
      · subst hx
        simp [hp]
      · simp [hx]
    conv_lhs => rw [hins]
    rw [finprod_mem_insert' _ (by simp) hfin]

theorem b_mem_p (hd : d.AxH 𝒜) (h : d.S1) {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne)
    (k : Fin d.del) (c : ι) (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ))
    (hw : w ∈ d.GoodP c p) :
    0 ≤ w (d.bvecG hd.sel hd.a4.choose k c) +
      ((d.ord c (d.Wres c w) d.wF (hd.a4.choose c) : ℤ) : WithTop ℤ) := by
  classical
  obtain ⟨he, -, -⟩ := hd.a4.choose_spec
  obtain ⟨heF, he0⟩ := he c
  have hadm := d.good_adm hd h c hp hw
  have hthpF : d.thp (hd.sel k) c ∈ 𝒜 c d.wF := hd.thp_mem _ c
  obtain ⟨a, ha⟩ : ∃ a : Ω c, d.thp (hd.sel k) c = a • hd.a4.choose c := by
    have he0' : (⟨hd.a4.choose c, heF⟩ : 𝒜 c d.wF) ≠ 0 := by
      intro h0; exact he0 (congrArg Subtype.val h0)
    obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' _ he0').mp (hd.finrank_one c d.wF)
      ⟨_, hthpF⟩
    exact ⟨a, (congrArg Subtype.val ha).symm⟩
  have hb : d.bvecG hd.sel hd.a4.choose k c = algebraMap (Ω c) (OmS (Ω c) d.D d.N) a := by
    simp only [bvecG]
    rw [ValuationResidueLemmas.ratio_eq he0 ha]
  rw [hb]
  change 0 ≤ d.Wres c w a + _
  by_cases ha0 : a = 0
  · rw [ha0, AddValuation.map_zero, top_add]
    exact le_top
  have hth0 : d.thp (hd.sel k) c ≠ 0 := by
    rw [ha]; exact smul_ne_zero ha0 he0
  rw [← hd.ord_smul c _ hadm a heF he0 ha0, ← ha]
  have hmem : d.thp (hd.sel k) ∈ d.Thp := by
    rw [hd.Thp_span]; exact Submodule.subset_span ⟨_, rfl⟩
  exact_mod_cast hd.ord_nonneg_Thp c _ hadm _ hmem hth0

theorem de_local (hd : d.AxH 𝒜) (h : d.S1) {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne) :
    LocAt.IntAt p (d.De hd h * algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^
      (2 * ∑ c, d.nP h c d.wF (hd.a4.choose c) p)) := by
  classical
  letI : ∀ c, Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := fun c => (d.KTtoS h c).toAlgebra
  haveI : ∀ c, FiniteDimensional (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := fun c => by
    haveI := d.KT_finiteDimensional hd c
    let e : KTf K d.D d.N ≃+* d.KT c :=
      (d.KTtoS h c).rangeRestrictFieldEquiv.trans (RingEquiv.subfieldCongr (d.KTtoS_fieldRange h c))
    apply Module.Finite.of_equiv_equiv e.symm (RingEquiv.refl (OmS (Ω c) d.D d.N))
    refine RingHom.ext fun x => ?_
    change d.KTtoS h c (e.symm x) = (x : OmS (Ω c) d.D d.N)
    exact congrArg (fun y : d.KT c => (y : OmS (Ω c) d.D d.N)) (e.apply_symm_apply x)
  haveI : CharZero (KTf K d.D d.N) :=
    charZero_of_injective_algebraMap (algebraMap K (KTf K d.D d.N)).injective
  haveI : ∀ c, Algebra.IsSeparable (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := fun c =>
    Algebra.IsSeparable.of_integral _ _
  haveI := hp.1
  have hsH : ∀ c x, d.sH c x = algebraMap (KTf K d.D d.N) (OmS (Ω c) d.D d.N)
      (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) x) := fun c x =>
    (IsFractionRing.lift_algebraMap (A := KTp K d.D d.N) (g := (d.sH c).toRingHom) (h c) x).symm
  have hOver : ∀ c, d.OverP c p =
      HNm.OverR (R := KTp K d.D d.N) (F := KTf K d.D d.N)
        (L := OmS (Ω c) d.D d.N) p := by
    intro c; ext w; simp only [OverP, HNm.OverR, Set.mem_ofPred_eq, hsH]
  let n : ∀ c, AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ) → ℤ := fun c w =>
    if w ∈ d.GoodP c p then d.ord c (d.Wres c w) d.wF (hd.a4.choose c) else 0
  have hb : ∀ k c, ∀ w ∈ HNm.OverR (R := KTp K d.D d.N) (F := KTf K d.D d.N)
      (L := OmS (Ω c) d.D d.N) p,
      0 ≤ w (d.bvecG hd.sel hd.a4.choose k c) + (n c w : WithTop ℤ) := by
    intro k c w hw
    rw [← hOver c] at hw
    by_cases hg : w ∈ d.GoodP c p
    · simp only [n, if_pos hg]
      exact d.b_mem_p hd h hp k c w hg
    · simp only [n, if_neg hg, WithTop.coe_zero, add_zero]
      have hz : ∀ a : Ω c, a ≠ 0 → d.Wres c w a = 0 := fun a ha =>
        by_contra fun hne => hg ⟨hw, a, ha, hne⟩
      change 0 ≤ d.Wres c w _
      by_cases hr : ratio (Ω := Ω c) (d.thp (hd.sel k) c) (hd.a4.choose c) = 0
      · rw [hr, AddValuation.map_zero]; exact le_top
      · rw [hz _ hr]
  have hexp : ∀ c, (∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ))
      (_ : w ∈ HNm.OverR (R := KTp K d.D d.N) (F := KTf K d.D d.N)
        (L := OmS (Ω c) d.D d.N) p),
        (HNm.fz (F := KTf K d.D d.N) w : ℤ) * n c w) = d.nP h c d.wF (hd.a4.choose c) p := by
    intro c
    rw [← hOver c]
    simp only [nP]
    rw [finsum_mem_def, finsum_mem_def]
    refine finsum_congr fun w => ?_
    simp only [Set.indicator_apply, n]
    by_cases hg : w ∈ d.GoodP c p
    · have hg1 : w ∈ d.OverP c p := hg.1
      simp only [hg, hg1, if_true]
      rfl
    · simp only [hg, if_false, mul_zero, ite_self]
  open IsDedekindDomain IsLocalRing Module in
  have disc_local {R F : Type} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] [Field F]
        [Algebra R F] [IsFractionRing R F] {ι : Type} [Fintype ι] [DecidableEq ι]
        {L : ι → Type} [∀ c, Field (L c)] [∀ c, Algebra F (L c)]
        [∀ c, FiniteDimensional F (L c)] [∀ c, Algebra.IsSeparable F (L c)] (p : Ideal R) [p.IsPrime] (hp : p.height = 1) (g : R) (hg : p = Ideal.span {g})
      (n : ∀ c, AddValuation (L c) (WithTop ℤ) → ℤ)
      {m : ℕ} (hm : m = ∑ c, finrank F (L c)) (b : Fin m → ∀ c, L c) (hli : LinearIndependent F b)
      (hb : ∀ k c, ∀ w ∈ HNm.OverR (R := R) (F := F) (L := L c) p,
        0 ≤ w (b k c) + (n c w : WithTop ℤ)) :
      ∃ a s : R, s ∉ p ∧
        (Matrix.of fun k l : Fin m => ∑ c, Algebra.trace F (L c) (b k c * b l c)).det *
          algebraMap R F g ^ (2 * ∑ c, ∑ᶠ (w : AddValuation (L c) (WithTop ℤ))
            (_ : w ∈ HNm.OverR (R := R) (F := F) (L := L c) p), (HNm.fz (F := F) w : ℤ) * n c w) *
          algebraMap R F s =
          algebraMap R F a := by
    classical
    let O := Localization.AtPrime p
    letI : Algebra O F := IsLocalization.localizationAlgebraOfSubmonoidLe O F p.primeCompl
      (nonZeroDivisors R) (Ideal.primeCompl_le_nonZeroDivisors p)
    haveI : IsScalarTower R O F := IsLocalization.localization_isScalarTower_of_submonoid_le O F
      p.primeCompl (nonZeroDivisors R) (Ideal.primeCompl_le_nonZeroDivisors p)
    haveI : IsFractionRing O F :=
      IsFractionRing.isFractionRing_of_isDomain_of_isLocalization p.primeCompl O F
    obtain ⟨hdvr, hirr⟩ := ValUFD.loc_dvr p hp g hg
    haveI := hdvr
    letI : ∀ c, Algebra O (L c) := fun c => ((algebraMap F (L c)).comp (algebraMap O F)).toAlgebra
    haveI : ∀ c, IsScalarTower O F (L c) := fun c => IsScalarTower.of_algebraMap_eq' rfl
    letI : ∀ c, Algebra R (L c) := fun c => ((algebraMap F (L c)).comp (algebraMap R F)).toAlgebra
    haveI : ∀ c, IsScalarTower R O (L c) := fun c => IsScalarTower.of_algebraMap_eq (fun x => by
      show algebraMap F (L c) (algebraMap R F x) =
        algebraMap F (L c) (algebraMap O F (algebraMap R O x))
      rw [IsScalarTower.algebraMap_apply R O F x])
    have hded : ∀ c, IsDedekindDomain (integralClosure O (L c)) := fun c =>
      (ReciprocityTheory.MultiplicativeHeights.Closed.dedekindRank O F (L c)).1
    have hfr : ∀ c, IsFractionRing (integralClosure O (L c)) (L c) := fun c =>
      integralClosure.isFractionRing_of_finite_extension F (L c)
    have hset : ∀ c, ValPl.PlacesOver O (L c) = HNm.OverR (R := R) (F := F) (L := L c) p := fun c => by
      ext w
      simp only [ValPl.PlacesOver, HNm.OverR, Set.mem_ofPred_eq]
      rw [← ValPl.placesOver_iff_loc (R := R) p w]
      rfl
    have hG : ∀ c, ∃ gc : L c, gc ≠ 0 ∧ (∀ w ∈ ValPl.PlacesOver O (L c), w gc = n c w) ∧
        ∀ y, (∀ w ∈ ValPl.PlacesOver O (L c), 0 ≤ w y + (n c w : WithTop ℤ)) ↔
          gc * y ∈ integralClosure O (L c) := fun c => by
      haveI := hded c
      haveI := hfr c
      obtain ⟨gc, hg0, hgv⟩ := HDiscVal.exists_val_eq O F (n c)
      refine ⟨gc, hg0, hgv, fun y => ?_⟩
      rw [HDiscVal.mem_integralClosure_iff O F]
      refine forall₂_congr fun w hw => ?_
      rw [AddValuation.map_mul, hgv w hw, add_comm]
    choose gc hgc0 hgcv hgciff using hG
    have hbI : ∀ k c, gc c * b k c ∈ integralClosure O (L c) := fun k c =>
      (hgciff c _).mp (fun w hw => hb k c w (hset c ▸ hw))
    obtain ⟨nn, t, u, -, hdisc⟩ := HDiscLat.lattice_main (R := O) (F := F) hirr gc hgc0 hm b hbI hli
    set Nc : ι → ℤ := fun c => ∑ᶠ (w : AddValuation (L c) (WithTop ℤ))
      (_ : w ∈ HNm.OverR (R := R) (F := F) (L := L c) p), (HNm.fz (F := F) w : ℤ) * n c w with hNc
    have hN : ∀ c, ∃ uc : O, IsUnit uc ∧ Algebra.norm F (gc c) =
        algebraMap R F g ^ Nc c * algebraMap O F uc := fun c => by
      haveI := hded c
      haveI := hfr c
      obtain ⟨uc, huc, hn⟩ := ValPl.norm_eq_places (O := O) (F := F) (gc c) (hgc0 c) hirr
      refine ⟨uc, huc, ?_⟩
      rw [hn, ← IsScalarTower.algebraMap_apply R O F g, hset c]
      congr 2
      refine finsum_congr fun w => finsum_congr fun hw => ?_
      rw [← hset c] at hw
      rw [hgcv c w hw, WithTop.untopD_coe]
      rfl
    choose uc huc hNe using hN
    set X := algebraMap R F g with hX
    have hX0 : X ≠ 0 := by
      rw [hX, map_ne_zero_iff _ (IsFractionRing.injective R F)]
      rintro rfl
      have : p = ⊥ := by rw [hg, Ideal.span_singleton_eq_bot]
      subst this
      simp at hp
    let U : Oˣ := ∏ c, (huc c).unit
    have hprod : ∏ c, Algebra.norm F (gc c) = X ^ (∑ c, Nc c) * algebraMap O F (U : O) := by
      rw [Finset.prod_congr rfl fun c _ => hNe c, Finset.prod_mul_distrib, HDiscOmL.prod_zpow hX0,
        ← map_prod]
      congr 2
      simp only [U, Units.coe_prod, IsUnit.unit_spec]
    rw [hprod] at hdisc
    set Dt := (Matrix.of fun k l : Fin m => ∑ c, Algebra.trace F (L c) (b k c * b l c)).det with hDt
    obtain ⟨⟨a, s⟩, has⟩ := IsLocalization.mk'_surjective p.primeCompl
      ((u : O) * ((algebraMap R O g) ^ (2 * nn + t)) * ((U⁻¹ : Oˣ) : O) * ((U⁻¹ : Oˣ) : O))
    refine ⟨a, s, s.2, ?_⟩
    have hsF : algebraMap O F (IsLocalization.mk' O a s) * algebraMap R F s = algebraMap R F a := by
      rw [IsScalarTower.algebraMap_apply R O F s, IsScalarTower.algebraMap_apply R O F a, ← map_mul,
        IsLocalization.mk'_spec]
    simp only at has
    rw [← hsF, has]
    congr 1
    set V := algebraMap O F (U : O)
    set V' := algebraMap O F ((U⁻¹ : Oˣ) : O)
    have hU : V * V' = 1 := by
      simp only [V, V']
      rw [← map_mul, Units.mul_inv, map_one]
    have h2 : X ^ (2 * ∑ c, Nc c) = (X ^ (∑ c, Nc c)) ^ 2 := by
      rw [mul_comm, zpow_mul]
      norm_cast
    have e1 : algebraMap O F ((u : O) * (algebraMap R O g) ^ (2 * nn + t) * ((U⁻¹ : Oˣ) : O) *
        ((U⁻¹ : Oˣ) : O)) = algebraMap O F ((u : O) * (algebraMap R O g) ^ (2 * nn + t)) * V' * V' := by
      simp only [V', map_mul]
    rw [h2, e1, ← hdisc]
    calc Dt * (X ^ ∑ c, Nc c) ^ 2 = Dt * (X ^ ∑ c, Nc c) ^ 2 * (V * V') * (V * V') := by
          rw [hU]; ring
      _ = Dt * ((X ^ ∑ c, Nc c) * V) ^ 2 * V' * V' := by ring
  obtain ⟨a, s, hs, he⟩ := disc_local (R := KTp K d.D d.N) (F := KTf K d.D d.N)
    (L := fun c => OmS (Ω c) d.D d.N) p hp.2 (d.gen p) (d.gen_span hp) n (d.del_eq hd h)
    (d.bvecG hd.sel hd.a4.choose) (d.b_linIndep hd h) hb
  refine ⟨a, s, hs, ?_⟩
  rw [← he]
  simp only [hexp]
  rfl

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Hartogs
namespace ReciprocityTheory.ChartRestriction.G.T0

theorem ufd_mem_of_forall_prime {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (x : FractionRing R)
    (h : ∀ p : R, Prime p → ∃ a b : R, ¬ p ∣ b ∧ x * algebraMap R (FractionRing R) b =
      algebraMap R (FractionRing R) a) :
    ∃ a : R, x = algebraMap R (FractionRing R) a := by
  classical
  have key : ∀ c : R, c ≠ 0 → ∀ a0 : R, x * algebraMap R (FractionRing R) c =
      algebraMap R (FractionRing R) a0 → ∃ a : R, x = algebraMap R (FractionRing R) a := by
    intro c
    induction c using UniqueFactorizationMonoid.induction_on_prime with
    | h₁ => intro h0; exact absurd rfl h0
    | h₂ u hu =>
      intro _ a0 hx
      refine ⟨a0 * ↑(hu.unit⁻¹), ?_⟩
      have hu' : algebraMap R (FractionRing R) u * algebraMap R (FractionRing R) ↑(hu.unit⁻¹) = 1 := by
        rw [← map_mul]; simp
      calc x = x * (algebraMap R (FractionRing R) u * algebraMap R (FractionRing R) ↑(hu.unit⁻¹)) := by
              rw [hu', mul_one]
        _ = algebraMap R (FractionRing R) (a0 * ↑(hu.unit⁻¹)) := by rw [← mul_assoc, hx, map_mul]
    | h₃ c p hc hp ih =>
      intro _ a0 hx
      obtain ⟨a, b, hpb, hab⟩ := h p hp
      have hinj := IsFractionRing.injective R (FractionRing R)
      have e1 : a * (p * c) = a0 * b := by
        apply hinj
        simp only [map_mul] at hx hab ⊢
        linear_combination (-(algebraMap R (FractionRing R) p * algebraMap R (FractionRing R) c)) * hab +
          algebraMap R (FractionRing R) b * hx
      have hpa0 : p ∣ a0 := by
        have : p ∣ a0 * b := ⟨a * c, by rw [← e1]; ring⟩
        rcases hp.dvd_or_dvd this with h1 | h1
        · exact h1
        · exact absurd h1 hpb
      obtain ⟨a1, rfl⟩ := hpa0
      have hp0 : algebraMap R (FractionRing R) p ≠ 0 := by
        rw [Ne, ← map_zero (algebraMap R (FractionRing R))]
        exact fun h' => hp.ne_zero (hinj h')
      refine ih hc a1 ?_
      apply mul_left_cancel₀ hp0
      simp only [map_mul] at hx ⊢
      linear_combination hx
  obtain ⟨a0, c, hc, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
  refine key c hc0 a0 ?_
  rw [div_mul_cancel₀]
  rw [Ne, ← map_zero (algebraMap R (FractionRing R))]
  exact fun h' => hc0 (IsFractionRing.injective R (FractionRing R) h')

end ReciprocityTheory.ChartRestriction.G.T0
end

set_option linter.style.haveILetI false

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

private theorem gen_ne_zero_of_mem_htOne_heightData {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne) : d.gen p ≠ 0 := by
  obtain ⟨hpr, hht⟩ := hp
  have hne : p ≠ ⊥ := by
    rintro rfl
    first
      | (simp at hht; done)
      | (rw [Ideal.height_bot] at hht; exact zero_ne_one hht)
  obtain ⟨q, hqp, hq⟩ := hpr.exists_mem_prime_of_ne_bot hne
  have hqi : (Ideal.span {q}).IsPrime := (Ideal.span_singleton_prime hq.ne_zero).mpr hq
  have hle : Ideal.span {q} ≤ p := (Ideal.span_singleton_le_iff_mem p).mpr hqp
  have hbot : (⊥ : Ideal (KTp K d.D d.N)) < Ideal.span {q} :=
    bot_lt_iff_ne_bot.mpr (by simpa using hq.ne_zero)
  haveI := hpr
  haveI := hqi
  have hspan : Ideal.span {q} = p := by
    by_contra hne'
    have hlt : Ideal.span {q} < p := lt_of_le_of_ne hle hne'
    have h3 : (Ideal.span {q}).height < 1 := by
      have hp1 : p.height ≤ (1 : ℕ) := by rw [hht]; rfl
      exact (Ideal.height_le_iff.mp hp1) _ hqi hlt
    have h0 : (Ideal.span {q}).height ≤ (0 : ℕ) := by
      rw [ENat.lt_one_iff_eq_zero] at h3
      rw [h3]; rfl
    have h2 := (Ideal.height_le_iff.mp h0) ⊥ Ideal.isPrime_bot hbot
    first
      | (simp at h2; done)
      | exact absurd h2 (not_lt_of_ge bot_le)
      | exact ENat.not_lt_zero _ h2
  have hprin : p.IsPrincipal := ⟨⟨q, hspan.symm⟩⟩
  haveI := hprin
  simp only [Data.gen, dif_pos hprin]
  intro h0
  exact hne ((Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero p).mpr h0)

theorem fprod_ne_zero (E : Ideal (KTp K d.D d.N) → ℤ) (hE : {q | q ∈ d.HtOne ∧ E q ≠ 0}.Finite) :
    (∏ᶠ (q : Ideal (KTp K d.D d.N)) (_ : q ∈ d.HtOne),
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen q) ^ E q) ≠ 0 := by
  refine finprod_mem_induction (fun x => x ≠ 0) one_ne_zero (fun x y hx hy => mul_ne_zero hx hy) ?_
  intro q hq
  apply zpow_ne_zero
  have hg := gen_ne_zero_of_mem_htOne_heightData d hq
  first
    | exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hg
    | exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).mpr hg
    | exact (map_ne_zero_iff _ (NoZeroSMulDivisors.algebraMap_injective _ _)).mpr hg
    | (simpa using hg)

theorem sig_fprod (E : Ideal (KTp K d.D d.N) → ℤ) (hE : {q | q ∈ d.HtOne ∧ E q ≠ 0}.Finite)
    (hg : ∀ q ∈ d.HtOne, E q ≠ 0 → ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous
      (fun b : Fin (d.D + 1) => if b = 0 then 0 else d.dg (d.gen q)) (d.gen q))
    (bb : Fin (d.D + 1)) (u : Kˣ) :
    sigF (K := K) (D := d.D) (N := d.N) bb u (∏ᶠ (q : Ideal (KTp K d.D d.N)) (_ : q ∈ d.HtOne),
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen q) ^ E q) =
      algebraMap K (KTf K d.D d.N) (u : K) ^ (∑ᶠ (q : Ideal (KTp K d.D d.N)) (_ : q ∈ d.HtOne),
        E q * ((if bb = 0 then 0 else d.dg (d.gen q) : ℕ) : ℤ)) *
      ∏ᶠ (q : Ideal (KTp K d.D d.N)) (_ : q ∈ d.HtOne),
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen q) ^ E q := by
  classical
  have h1 : d.HtOne ∩ Function.mulSupport (fun q =>
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen q) ^ E q) ⊆ hE.toFinset := by
    rintro q ⟨hq, hs⟩
    rw [Set.Finite.coe_toFinset]
    exact ⟨hq, fun h0 => hs (by simp only [h0, zpow_zero])⟩
  have h1' : d.HtOne ∩ Function.support (fun q =>
      E q * ((if bb = 0 then 0 else d.dg (d.gen q) : ℕ) : ℤ)) ⊆ hE.toFinset := by
    rintro q ⟨hq, hs⟩
    rw [Set.Finite.coe_toFinset]
    exact ⟨hq, fun h0 => hs (by simp only [h0, zero_mul])⟩
  have h2 : (hE.toFinset : Set (Ideal (KTp K d.D d.N))) ⊆ d.HtOne := by
    intro q hq
    rw [Set.Finite.coe_toFinset] at hq
    exact hq.1
  rw [finprod_mem_eq_prod_of_subset _ h1 h2, finsum_mem_eq_sum_of_subset _ h1' h2, map_prod]
  have hκ : algebraMap K (KTf K d.D d.N) (u : K) ≠ 0 :=
    (map_ne_zero _).mpr u.ne_zero
  rw [← HDiscOmL.prod_zpow hκ, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun q hq => ?_
  have hq' : q ∈ d.HtOne ∧ E q ≠ 0 := by
    rw [Set.Finite.mem_toFinset] at hq
    exact hq
  have hs : sigP (N := d.N) bb u (d.gen q) =
      MvPolynomial.C ((u : K) ^ (if bb = 0 then 0 else d.dg (d.gen q))) * d.gen q :=
    scale_multiHomogeneous bb u (fun b : Fin (d.D + 1) => if b = 0 then 0 else d.dg (d.gen q))
      (d.gen q) (hg q hq'.1 hq'.2)
  have hs' : sigF (K := K) (D := d.D) (N := d.N) bb u
      (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen q)) =
      algebraMap K (KTf K d.D d.N) (u : K) ^ ((if bb = 0 then 0 else d.dg (d.gen q) : ℕ) : ℤ) *
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen q) := by
    rw [d.sigF_algebraMap, hs, map_mul, ← d.algebraMap_K_KTf, map_pow, zpow_natCast]
  rw [map_zpow₀, hs', mul_zpow, ← zpow_mul, mul_comm (E q)]

theorem om_is_poly (hd : d.AxH 𝒜) (h : d.S1) :
    ∃ Om : KTp K d.D d.N, algebraMap (KTp K d.D d.N) (KTf K d.D d.N) Om = d.omE hd h ∧ Om ≠ 0 ∧
      ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous
        (fun b : Fin (d.D + 1) => if b = 0 then 0 else 2 * (d.aG h d.wF hd.a4.choose).toNat) Om := by
  classical
  obtain ⟨he, -, -⟩ := hd.a4.choose_spec
  have hfin : ∀ c, {q | q ∈ d.HtOne ∧ d.nP h c d.wF (hd.a4.choose c) q ≠ 0}.Finite := fun c =>
    (d.good_primes_properties hd h c).2.2.1 d.wF (hd.a4.choose c) (he c).1 (he c).2

  have hint : ∀ p ∈ d.HtOne, LocAt.IntAt p (d.omE hd h) := by
    intro p hp
    haveI := hp.1
    have hs : ∀ c, ∃ V : KTf K d.D d.N, LocAt.UnitAt p V ∧
        (∏ᶠ (q : Ideal (KTp K d.D d.N)) (_ : q ∈ d.HtOne),
          algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen q) ^ d.nP h c d.wF (hd.a4.choose c) q) =
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ d.nP h c d.wF (hd.a4.choose c) p * V :=
      fun c => d.split_at _ (hfin c) hp
    choose V hV hVe using hs
    have hX0 : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (d.gen_prime' hp).ne_zero
    have hf : d.fDivE hd h = algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^
        (∑ c, d.nP h c d.wF (hd.a4.choose c) p) * ∏ c, V c := by
      simp only [fDivE]
      rw [Finset.prod_congr rfl fun c _ => hVe c, Finset.prod_mul_distrib, HDiscOmL.prod_zpow hX0]
    have h2 : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^
        (2 * ∑ c, d.nP h c d.wF (hd.a4.choose c) p) =
        (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^
          (∑ c, d.nP h c d.wF (hd.a4.choose c) p)) ^ 2 := by
      rw [mul_comm, zpow_mul]
      norm_cast
    have hom : d.omE hd h = (d.De hd h * algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^
        (2 * ∑ c, d.nP h c d.wF (hd.a4.choose c) p)) * (∏ c, V c) ^ 2 := by
      rw [omE, hf, h2]
      ring
    rw [hom]
    exact LocAt.intAt_mul (d.de_local hd h hp)
      (LocAt.unitAt_intAt (LocAt.unitAt_pow (LocAt.unitAt_prod _ _ fun c _ => hV c) 2))
  obtain ⟨Om, hOm⟩ := ufd_mem_of_forall_prime (R := KTp K d.D d.N) (d.omE hd h) (fun q hq => by
    have hp : Ideal.span {q} ∈ d.HtOne :=
      ⟨(Ideal.span_singleton_prime hq.ne_zero).mpr hq, ValUFD.height_span_prime hq⟩
    obtain ⟨a, s, hs, e⟩ := hint _ hp
    exact ⟨a, s, fun hdv => hs (Ideal.mem_span_singleton.mpr hdv), e⟩)

  have hf0 : d.fDivE hd h ≠ 0 := by
    simp only [fDivE]
    rw [Finset.prod_ne_zero_iff]
    exact fun c _ => d.fprod_ne_zero _ (hfin c)
  have hom0 : d.omE hd h ≠ 0 :=
    mul_ne_zero (d.disc_lattice hd h).1 (pow_ne_zero 2 hf0)
  have hOm0 : Om ≠ 0 := by
    rintro rfl
    rw [map_zero] at hOm
    exact hom0 hOm
  refine ⟨Om, hOm.symm, hOm0, ?_⟩

  obtain ⟨a, b, hb0, hab, m, -, ha, hbm⟩ := d.de_pres hd h
  have hsigDe : ∀ (bb : Fin (d.D + 1)) (u : Kˣ),
      sigF (K := K) (D := d.D) (N := d.N) bb u (d.De hd h) = d.De hd h := by
    intro bb u
    have e1 := congrArg (sigF (K := K) (D := d.D) (N := d.N) bb u) hab
    have sa : sigP (N := d.N) bb u a = MvPolynomial.C ((u : K) ^ m bb) * a :=
      scale_multiHomogeneous bb u m a ha
    have sb : sigP (N := d.N) bb u b = MvPolynomial.C ((u : K) ^ m bb) * b :=
      scale_multiHomogeneous bb u m b hbm
    rw [d.sigF_algebraMap, map_mul, d.sigF_algebraMap, sa, sb, map_mul, map_mul, hab,
      ← d.algebraMap_K_KTf] at e1
    have hC : algebraMap K (KTf K d.D d.N) ((u : K) ^ m bb) ≠ 0 :=
      (map_ne_zero _).mpr (pow_ne_zero _ u.ne_zero)
    have hB : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hb0
    apply mul_right_cancel₀ (mul_ne_zero hC hB)
    linear_combination -e1
  set Eb : Fin (d.D + 1) → ℤ := fun bb => ∑ c, ∑ᶠ (q : Ideal (KTp K d.D d.N)) (_ : q ∈ d.HtOne),
    d.nP h c d.wF (hd.a4.choose c) q * ((if bb = 0 then 0 else d.dg (d.gen q) : ℕ) : ℤ) with hEb
  have hsigf : ∀ (bb : Fin (d.D + 1)) (u : Kˣ),
      sigF (K := K) (D := d.D) (N := d.N) bb u (d.fDivE hd h) =
        algebraMap K (KTf K d.D d.N) (u : K) ^ Eb bb * d.fDivE hd h := by
    intro bb u
    have hκ : algebraMap K (KTf K d.D d.N) (u : K) ≠ 0 := (map_ne_zero _).mpr u.ne_zero
    simp only [fDivE, hEb]
    rw [map_prod, Finset.prod_congr rfl fun c _ => d.sig_fprod _ (hfin c) (fun q hq hn =>
      (d.good_primes_properties hd h c).2.1 q hq (by
        by_contra hno
        apply hn
        simp only [nP]
        rw [finsum_mem_def]
        refine finsum_eq_zero_of_forall_eq_zero fun w => ?_
        rw [Set.indicator_apply, if_neg (fun hw => hno ⟨w, hw⟩)])) bb u,
      Finset.prod_mul_distrib, HDiscOmL.prod_zpow hκ]
  have hEb : ∀ bb : Fin (d.D + 1), 2 * Eb bb =
      ((if bb = 0 then 0 else 2 * (d.aG h d.wF hd.a4.choose).toNat : ℕ) : ℤ) := by
    intro bb
    by_cases hbb : bb = 0
    · simp [hEb, hbb]
    · simp only [hEb, hbb, if_false]
      rw [Nat.cast_mul, Int.toNat_of_nonneg (d.aG_frame_nonneg hd h)]
      rfl
  intro s hs bb
  refine block_deg_of_scale bb _ Om (fun u => ?_) s hs
  apply IsFractionRing.injective (KTp K d.D d.N) (KTf K d.D d.N)
  change algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (sigP (N := d.N) bb u Om) =
    algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (MvPolynomial.C ((u : K) ^
      (if bb = 0 then 0 else 2 * (d.aG h d.wF hd.a4.choose).toNat)) * Om)
  rw [← d.sigF_algebraMap, map_mul, ← hOm, ← d.algebraMap_K_KTf, map_pow, ← zpow_natCast, ← hEb bb]
  have hk : algebraMap K (KTf K d.D d.N) (u : K) ^ (2 * Eb bb) =
      (algebraMap K (KTf K d.D d.N) (u : K) ^ Eb bb) ^ 2 := by
    rw [mul_comm, zpow_mul]
    norm_cast
  simp only [omE]
  rw [map_mul, map_pow, hsigDe, hsigf, hk]
  ring

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

theorem om_poly (hd : d.AxH 𝒜) (h : d.S1) :
    0 ≤ d.aG h d.wF hd.a4.choose ∧ (∃ a b : KTp K d.D d.N, d.IsPres hd h a b) ∧
    ∃ Om : KTp K d.D d.N, algebraMap (KTp K d.D d.N) (KTf K d.D d.N) Om = d.omE hd h ∧ Om ≠ 0 ∧
      ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous
        (fun b : Fin (d.D + 1) => if b = 0 then 0 else 2 * (d.aG h d.wF hd.a4.choose).toNat) Om := by
  exact ⟨d.aG_frame_nonneg hd h, d.de_pres hd h, d.om_is_poly hd h⟩

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

theorem disc_global (hd : d.AxH 𝒜) (h : d.S1) (hI2be : d.HeightIntegralBoundEstimate) (ta' : ∀ c, A c)
    (hta' : ∀ c, ta' c ∈ 𝒜 c d.wF ∧ ta' c ≠ 0) :
    (Function.support fun la => d.gOrd la (d.De hd h)).Finite ∧
    (Function.support fun la => d.NlaG h d.wF hd.a4.choose la).Finite ∧
    (∑ᶠ la, ((d.gOrd la (d.De hd h) : ℝ) + 2 * d.NlaG h d.wF hd.a4.choose la) * logNorm la) /
      (Module.finrank ℚ K : ℝ) ≤
      d.del * Real.log d.del +
        2 * ∑ k, meanK (fun sg => Real.log (d.supN sg d.wF (d.thp (hd.sel k)))) +
        2 * d.D * d.aG h d.wF ta' * (Real.log (d.N + 1 : ℕ) + 1 / 2) + 2 * d.Hgt h d.wF ta' := by
  obtain ⟨haG0, ⟨a, b, hab⟩, Om, hOm, hOm0, hOmH⟩ := d.om_poly hd h
  obtain ⟨hs1, hs2, heq⟩ := d.disc_product hd h hI2be a b hab Om hOm
  refine ⟨hs1, hs2, ?_⟩
  rw [heq]
  have ha4 : ∀ c, hd.a4.choose c ∈ 𝒜 c d.wF ∧ hd.a4.choose c ≠ 0 := by
    first
    | exact hd.a4.choose_spec
    | exact hd.a4.choose_spec.1
    | exact fun c => hd.a4.choose_spec.1 c
    | exact fun c => ⟨hd.a4.choose_spec.1 c, hd.a4.choose_spec.2 c⟩
  have hH : d.Hgt h d.wF hd.a4.choose = d.Hgt h d.wF ta' :=
    (d.h_ind hd h hI2be).1 d.wF hd.a4.choose ta' (by simp) ha4 hta'
  have haG : d.aG h d.wF hd.a4.choose = d.aG h d.wF ta' :=
    (d.arithDegree_additive hd h).1 d.wF hd.a4.choose ta' ha4 hta'
  have hcard : (0 : ℝ) < (Fintype.card (K →+* ℂ) : ℝ) := by
    have hc : 0 < Fintype.card (K →+* ℂ) := by
      first
      | (rw [NumberField.Embeddings.card]; exact Module.finrank_pos)
      | exact Fintype.card_pos
      | exact Fintype.card_pos_iff.mpr inferInstance
    exact_mod_cast hc
  have hmean : meanK (fun sg => d.mSgP sg a b - 2 * d.Nsg d.wF hd.a4.choose sg) ≤
      d.del * Real.log d.del +
        2 * ∑ k, meanK (fun sg => Real.log (d.supN sg d.wF (d.thp (hd.sel k)))) := by
    unfold meanK
    rw [div_le_iff₀ hcard]
    calc ∑ sg, (d.mSgP sg a b - 2 * d.Nsg d.wF hd.a4.choose sg)
        ≤ ∑ sg, (d.del * Real.log d.del +
            2 * ∑ k, Real.log (d.supN sg d.wF (d.thp (hd.sel k)))) :=
          Finset.sum_le_sum fun sg _ => d.disc_hadamard hd h hI2be a b hab sg
      _ = (d.del * Real.log d.del + 2 * ((∑ k, ∑ sg,
            Real.log (d.supN sg d.wF (d.thp (hd.sel k)))) / (Fintype.card (K →+* ℂ) : ℝ))) *
            (Fintype.card (K →+* ℂ) : ℝ) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            ← Finset.mul_sum, Finset.sum_comm, add_mul, mul_assoc (2 : ℝ),
            div_mul_cancel₀ _ hcard.ne']
          ring
      _ = _ := by rw [Finset.sum_div]
  have hh0 : -(ReciprocityTheory.MultiplicativeHeights.h0 Om) ≤
      2 * d.D * d.aG h d.wF hd.a4.choose * (Real.log (d.N + 1 : ℕ) + 1 / 2) := by
    have h1 := ReciprocityTheory.MultiplicativeHeights.Closed.sphere_height_lower_bound K (d.D + 1) (d.N + 1) _ Om (Nat.succ_pos _) hOm0 hOmH
    have ht : ((d.aG h d.wF hd.a4.choose).toNat : ℝ) = (d.aG h d.wF hd.a4.choose : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg haG0
    simp only [Fin.sum_univ_succ, Fin.succ_ne_zero, eq_self_iff_true, if_true, if_false,
      ite_true, ite_false, Nat.cast_zero, zero_mul, zero_add, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat] at h1
    rw [ht] at h1
    linear_combination h1
  rw [hH, ← haG]
  linarith [hmean, hh0]

end Data

end ReciprocityTheory.ChartRestriction.G.T0
