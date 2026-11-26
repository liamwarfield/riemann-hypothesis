module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.IntNsg
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HPlaces

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HeightProdPowMultiHomogeneous
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ValuationGenericRatioEqRestriction
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.OrdEqValuationRatioBaseAdd
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

noncomputable def translatedForm (x : Fin (d.N + 1) → K) (F : KTp K d.D d.N) : KTp K d.D d.N :=
  MvPolynomial.aeval (fun v : TVar d.D d.N =>
    if v.1 = 0 then MvPolynomial.C (x v.2) else MvPolynomial.X v) F

noncomputable def localHeightAtPrime (h : d.S1) (f : ∀ c, A c) (c : ι)
    (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : ℝ :=
  ∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.PlOver la c),
    (d.fze h c w : ℝ) * (d.ordMM c (d.Wres c w) (f c) : ℝ)

noncomputable def localHeightAtEmbedding (f : ∀ c, A c) (c : ι) (sg : K →+* ℂ) : ℝ :=
  ∫ z, (∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (fun i j => ReciprocityTheory.MultiplicativeHeights.spherePoint (z i) j)),
    -Real.log (d.nrm c d.wL (f c) P / d.be c P)) ∂(ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1))

def heightSubstitutionCondition (h : d.S1) (x : Fin (d.N + 1) → K) (c : ι) (F : KTp K d.D d.N) (κ : K) : Prop :=
  letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F * algebraMap K (KTf K d.D d.N) κ *
      Algebra.norm (KTf K d.D d.N) (algebraMap (Ω c) (OmS (Ω c) d.D d.N)
        (ratio (Ω := Ω c) (d.wx x c) (d.w (d.jc c) c))) =
    algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.translatedForm x F) *
      Algebra.norm (KTf K d.D d.N) (d.rationalBaseRow c)

theorem ratio_eq_of_eq_smul_field {Ω' V : Type*} [Field Ω'] [AddCommGroup V] [Module Ω' V] {f g : V}
    (hg : g ≠ 0) {a : Ω'} (hf : f = a • g) : ratio (Ω := Ω') f g = a := by
  classical
  have h : ∃ b : Ω', f = b • g := ⟨a, hf⟩
  unfold ratio
  rw [dite_eq_left h]
  exact smul_left_injective Ω' hg (h.choose_spec.symm.trans hf)

theorem eq_ratio_base_smul (hd : d.AxH 𝒜) (c : ι) {f : A c} (hf : f ∈ 𝒜 c d.wL) :
    f = ratio (Ω := Ω c) f (d.w (d.jc c) c) • d.w (d.jc c) c := by
  have hw := hd.w_mem (d.jc c) c
  have hw0 := hd.w_base c
  obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' (⟨_, hw⟩ : 𝒜 c d.wL)
    (by simpa using hw0)).1 (hd.finrank_one c d.wL) ⟨f, hf⟩
  have hfa : f = a • d.w (d.jc c) c := by
    have h1 := congrArg Subtype.val ha
    simp only [SetLike.val_smul] at h1
    exact h1.symm
  rw [ratio_eq_of_eq_smul_field hw0 hfa]
  exact hfa

theorem ratio_base_ne_zero (hd : d.AxH 𝒜) (c : ι) {f : A c} (hf : f ∈ 𝒜 c d.wL) (hf0 : f ≠ 0) :
    ratio (Ω := Ω c) f (d.w (d.jc c) c) ≠ 0 := by
  intro h0
  apply hf0
  rw [d.eq_ratio_base_smul hd c hf, h0, zero_smul]

theorem linearCombination_mem_section (hd : d.AxH 𝒜) (x : Fin (d.N + 1) → K) (c : ι) : d.wx x c ∈ 𝒜 c d.wL := by
  haveI := hd.tower c
  unfold wx
  rw [Finset.sum_apply]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [Pi.smul_apply, ← algebraMap_smul (Ω c) (x j)]
  exact Submodule.smul_mem _ _ (hd.w_mem j c)

theorem ord_eq_valuation_ratio_base_add (hd : d.AxH 𝒜) (c : ι) (v : AddValuation (Ω c) (WithTop ℤ)) (hv : d.admitted c v)
    {f : A c} (hf : f ∈ 𝒜 c d.wL) (hf0 : f ≠ 0) :
    ((d.ord c v d.wL f : ℤ) : WithTop ℤ) =
      v (ratio (Ω := Ω c) f (d.w (d.jc c) c)) + (d.ord c v d.wL (d.w (d.jc c) c) : WithTop ℤ) := by
  have hfa := d.eq_ratio_base_smul hd c hf
  have ha := d.ratio_base_ne_zero hd c hf hf0
  conv_lhs => rw [hfa]
  exact hd.ord_smul c v hv _ (hd.w_mem _ c) (hd.w_base c) ha

theorem eq_ratio_smul_of_mem (hd : d.AxH 𝒜) (c : ι) {f g : A c} (hf : f ∈ 𝒜 c d.wL) (hg : g ∈ 𝒜 c d.wL)
    (hg0 : g ≠ 0) : f = ratio (Ω := Ω c) f g • g := by
  obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' (⟨_, hg⟩ : 𝒜 c d.wL)
    (by simpa using hg0)).1 (hd.finrank_one c d.wL) ⟨f, hf⟩
  have hfa : f = a • g := by
    have h1 := congrArg Subtype.val ha
    simp only [SetLike.val_smul] at h1
    exact h1.symm
  rw [ratio_eq_of_eq_smul_field hg0 hfa]
  exact hfa

theorem ratio_ne_zero_of_ne_zero (hd : d.AxH 𝒜) (c : ι) {f g : A c} (hf : f ∈ 𝒜 c d.wL) (hg : g ∈ 𝒜 c d.wL)
    (hg0 : g ≠ 0) (hf0 : f ≠ 0) : ratio (Ω := Ω c) f g ≠ 0 := by
  intro h0
  apply hf0
  rw [d.eq_ratio_smul_of_mem hd c hf hg hg0, h0, zero_smul]

theorem ord_eq_valuation_ratio_add (hd : d.AxH 𝒜) (c : ι) (v : AddValuation (Ω c) (WithTop ℤ)) (hv : d.admitted c v)
    {f g : A c} (hf : f ∈ 𝒜 c d.wL) (hg : g ∈ 𝒜 c d.wL) (hg0 : g ≠ 0) (hf0 : f ≠ 0) :
    ((d.ord c v d.wL f : ℤ) : WithTop ℤ) =
      v (ratio (Ω := Ω c) f g) + (d.ord c v d.wL g : WithTop ℤ) := by
  have hfa := d.eq_ratio_smul_of_mem hd c hf hg hg0
  have ha := d.ratio_ne_zero_of_ne_zero hd c hf hg hg0 hf0
  conv_lhs => rw [hfa]
  exact hd.ord_smul c v hv _ hg hg0 ha

theorem ratio_mul_ratio_height (hd : d.AxH 𝒜) (c : ι) {f g e : A c} (hf : f ∈ 𝒜 c d.wL)
    (hg : g ∈ 𝒜 c d.wL) (he : e ∈ 𝒜 c d.wL) (hg0 : g ≠ 0) (he0 : e ≠ 0) :
    ratio (Ω := Ω c) f e = ratio (Ω := Ω c) f g * ratio (Ω := Ω c) g e := by
  have h1 := d.eq_ratio_smul_of_mem hd c hf hg hg0
  have h2 := d.eq_ratio_smul_of_mem hd c hg he he0
  apply ratio_eq_of_eq_smul_field he0
  rw [mul_smul, ← h2, ← h1]

theorem coe_untopD_of_ne_top {v : WithTop ℤ} (hv : v ≠ ⊤) : ((v.untopD 0 : ℤ) : WithTop ℤ) = v := by
  obtain ⟨x, rfl⟩ := WithTop.ne_top_iff_exists.1 hv
  rw [WithTop.untopD_coe]

theorem ordMinMax_eq_ratio_untop_sub (hd : d.AxH 𝒜) (c : ι) (v : AddValuation (Ω c) (WithTop ℤ)) (hv : d.admitted c v)
    (j0 : Fin (d.N + 1)) (hj0 : d.w j0 c ≠ 0)
    (hint : ∀ j, 0 ≤ v (ratio (Ω := Ω c) (d.w j c) (d.w j0 c)))
    {f : A c} (hf : f ∈ 𝒜 c d.wL) (hf0 : f ≠ 0) :
    d.ordMM c v f = (v (ratio (Ω := Ω c) f (d.w (d.jc c) c))).untopD 0 -
      (v (ratio (Ω := Ω c) (d.w j0 c) (d.w (d.jc c) c))).untopD 0 := by
  have key : ∀ {g : A c}, g ∈ 𝒜 c d.wL → g ≠ 0 → d.ord c v d.wL g =
      (v (ratio (Ω := Ω c) g (d.w (d.jc c) c))).untopD 0 + d.ord c v d.wL (d.w (d.jc c) c) := by
    intro g hg hg0
    have h := d.ord_eq_valuation_ratio_base_add hd c v hv hg hg0
    have hne : v (ratio (Ω := Ω c) g (d.w (d.jc c) c)) ≠ ⊤ := by
      rw [Ne, AddValuation.top_iff]
      exact d.ratio_base_ne_zero hd c hg hg0
    rw [← coe_untopD_of_ne_top hne, ← WithTop.coe_add] at h
    exact WithTop.coe_inj.1 h
  have hinf : (⨅ j : {j // d.w j c ≠ 0}, d.ord c v d.wL (d.w j c)) = d.ord c v d.wL (d.w j0 c) := by
    apply le_antisymm
    · exact ciInf_le (Set.finite_range _).bddBelow (⟨j0, hj0⟩ : {j // d.w j c ≠ 0})
    · haveI : Nonempty {j // d.w j c ≠ 0} := ⟨⟨j0, hj0⟩⟩
      refine le_ciInf fun j => ?_
      have h := d.ord_eq_valuation_ratio_add hd c v hv (hd.w_mem j.1 c) (hd.w_mem j0 c) hj0 j.2
      have hnn := hint j.1
      have hne : v (ratio (Ω := Ω c) (d.w j.1 c) (d.w j0 c)) ≠ ⊤ := by
        rw [Ne, AddValuation.top_iff]
        exact d.ratio_ne_zero_of_ne_zero hd c (hd.w_mem j.1 c) (hd.w_mem j0 c) hj0 j.2
      rw [← coe_untopD_of_ne_top hne, ← WithTop.coe_add] at h
      have h' := WithTop.coe_inj.1 h
      rw [← coe_untopD_of_ne_top hne] at hnn
      have h0 : 0 ≤ (v (ratio (Ω := Ω c) (d.w j.1 c) (d.w j0 c))).untopD 0 := by exact_mod_cast hnn
      omega
  unfold ordMM
  rw [hinf, key hf hf0, key (hd.w_mem j0 c) hj0]
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

theorem gen_ne_zero_of_htOne {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne) : d.gen p ≠ 0 := by
  intro h0
  exact d.x4v4_gen_ne hp (by rw [h0, map_zero])

theorem valuation_genericRatio_eq_restriction (hd : d.AxH 𝒜) (c : ι) (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ))
    (j0 : Fin (d.N + 1)) (hj0 : d.w j0 c ≠ 0)
    (hunit : w (∑ j, d.sH c (MvPolynomial.X (0, j)) *
      algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.w j c) (d.w j0 c))) = 0) :
    w (d.rationalBaseRow c) = d.Wres c w (ratio (Ω := Ω c) (d.w j0 c) (d.w (d.jc c) c)) := by
  have hg : d.w (d.jc c) c ≠ 0 := hd.w_base c
  have e0 : d.w j0 c = ratio (Ω := Ω c) (d.w j0 c) (d.w (d.jc c) c) • d.w (d.jc c) c :=
    d.x4v4_eq_smul hd c (hd.w_mem j0 c)
  have hr00 : ratio (Ω := Ω c) (d.w j0 c) (d.w (d.jc c) c) ≠ 0 := by
    intro h0
    apply hj0
    rw [e0, h0, zero_smul]
  have key : ∀ j, ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) =
      ratio (Ω := Ω c) (d.w j c) (d.w j0 c) * ratio (Ω := Ω c) (d.w j0 c) (d.w (d.jc c) c) := by
    intro j
    have ej : d.w j c = ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) • d.w (d.jc c) c :=
      d.x4v4_eq_smul hd c (hd.w_mem j c)
    have hrj : ratio (Ω := Ω c) (d.w j c) (d.w j0 c) =
        ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) / ratio (Ω := Ω c) (d.w j0 c) (d.w (d.jc c) c) := by
      apply x4v4_ratio_spec hj0
      calc d.w j c = ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) • d.w (d.jc c) c := ej
        _ = (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) / ratio (Ω := Ω c) (d.w j0 c) (d.w (d.jc c) c) *
              ratio (Ω := Ω c) (d.w j0 c) (d.w (d.jc c) c)) • d.w (d.jc c) c := by
            rw [div_mul_cancel₀ _ hr00]
        _ = (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) / ratio (Ω := Ω c) (d.w j0 c) (d.w (d.jc c) c)) •
              (ratio (Ω := Ω c) (d.w j0 c) (d.w (d.jc c) c) • d.w (d.jc c) c) := by
            rw [smul_smul]
        _ = _ := by rw [← e0]
    rw [hrj, div_mul_cancel₀ _ hr00]
  have hsum : d.rationalBaseRow c = (∑ j, d.sH c (MvPolynomial.X (0, j)) *
      algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.w j c) (d.w j0 c))) *
      algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.w j0 c) (d.w (d.jc c) c)) := by
    unfold Data.rationalBaseRow
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [key j, map_mul, mul_assoc]
  rw [hsum, AddValuation.map_mul, hunit, zero_add]
  first
    | rfl
    | simp [Data.Wres, AddValuation.comap_apply]

theorem ordMinMax_at_good_place (hd : d.AxH 𝒜) (c : ι) (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ))
    (hv : d.admitted c (d.Wres c w)) (j0 : Fin (d.N + 1)) (hj0 : d.w j0 c ≠ 0)
    (hint : ∀ j, 0 ≤ d.Wres c w (ratio (Ω := Ω c) (d.w j c) (d.w j0 c)))
    (hunit : w (∑ j, d.sH c (MvPolynomial.X (0, j)) *
      algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.w j c) (d.w j0 c))) = 0)
    {f : A c} (hf : f ∈ 𝒜 c d.wL) (hf0 : f ≠ 0) :
    d.ordMM c (d.Wres c w) f =
      (w (algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) f (d.w (d.jc c) c)))).untopD 0 -
        (w (d.rationalBaseRow c)).untopD 0 := by
  rw [d.ordMinMax_eq_ratio_untop_sub hd c _ hv j0 hj0 hint hf hf0, d.valuation_genericRatio_eq_restriction hd c w j0 hj0 hunit]
  rfl

theorem exists_ne_zero_of_finsum_mem_ne_zero' {α M : Type*} [AddCommMonoid M] {s : Set α} {f : α → M}
    (h : ∑ᶠ i ∈ s, f i ≠ 0) : ∃ i ∈ s, f i ≠ 0 := by
  by_contra hne
  push_neg at hne
  exact h (by rw [finsum_mem_congr rfl hne, finsum_mem_zero])

theorem multiplicity_split_finsum (hd : d.AxH 𝒜) (h : d.S1) (c : ι) {p : Ideal (KTp K d.D d.N)}
    (hp : p ∈ d.HtOne) {f : A c} (hf : f ∈ 𝒜 c d.wL) (hf0 : f ≠ 0) :
    d.nPMM h c f p =
      (∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.GoodP c p),
        (d.fze h c w : ℤ) * WithTop.untopD 0 (d.Wres c w (ratio (Ω := Ω c) f (d.w (d.jc c) c)))) +
      d.nPMM h c (d.w (d.jc c) c) p := by
  exact d.x4v4_split hd h c hp hf hf0

theorem algebraMap_gen_ne_zero {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne) :
    algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ≠ 0 := fun h => d.gen_ne_zero_of_htOne hp
  ((IsFractionRing.injective (KTp K d.D d.N) (KTf K d.D d.N)) (h.trans (map_zero _).symm))

theorem substituted_factorization_exists (hd : d.AxH 𝒜) (h : d.S1) (x : Fin (d.N + 1) → K)
    (hx : ∀ c, d.wx x c ≠ 0) (c : ι) (F : KTp K d.D d.N)
    (hF : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F = d.fZ h c) :
    ∃ κ : K, κ ≠ 0 ∧ d.heightSubstitutionCondition h x c F κ := by
  set a := ratio (Ω := Ω c) (d.wx x c) (d.w (d.jc c) c) with ha_def
  have hmem := d.linearCombination_mem_section hd x c
  have ha : a ≠ 0 := d.ratio_base_ne_zero hd c hmem (hx c)
  obtain ⟨κ1, hκ1, e1⟩ := d.SpecialFibreFactorization hd h c F hF x (hx c)
  obtain ⟨κ3, hκ3, e3⟩ := (d.norm_factorization hd h).1 c a ha
  set na : Ideal (KTp K d.D d.N) → ℤ := fun p =>
    ∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.GoodP c p),
      (d.fze h c w : ℤ) * WithTop.untopD 0 (d.Wres c w a) with hna
  have hsplit : ∀ p ∈ d.HtOne, d.nPMM h c (d.wx x c) p = na p + d.nPMM h c (d.w (d.jc c) c) p :=
    fun p hp => d.multiplicity_split_finsum hd h c hp hmem (hx c)
  have hyne : algebraMap (Ω c) (OmS (Ω c) d.D d.N) a ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap (Ω c) (OmS (Ω c) d.D d.N)).injective).mpr ha
  letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  haveI := d.KT_finiteDimensional hd c
  have hfr := d.KTtoS_fieldRange h c
  let e : (KTf K d.D d.N) ≃+* (d.KT c) :=
    ((d.KTtoS h c).rangeRestrictFieldEquiv).trans (RingEquiv.subfieldCongr hfr)
  have he : ∀ z, ((e z : d.KT c) : OmS (Ω c) d.D d.N) = d.KTtoS h c z := fun z => rfl
  have hc : (algebraMap (KTf K d.D d.N) (OmS (Ω c) d.D d.N)).comp e.symm.toRingHom =
      (RingEquiv.refl (OmS (Ω c) d.D d.N)).toRingHom.comp (algebraMap (d.KT c) (OmS (Ω c) d.D d.N)) := by
    refine RingHom.ext fun y => ?_
    show d.KTtoS h c (e.symm y) = (y : OmS (Ω c) d.D d.N)
    rw [← he, RingEquiv.apply_symm_apply]
  haveI : FiniteDimensional (KTf K d.D d.N) (OmS (Ω c) d.D d.N) :=
    Module.Finite.of_equiv_equiv e.symm (RingEquiv.refl _) hc
  have hmap : ∀ z : KTp K d.D d.N,
      algebraMap (KTf K d.D d.N) (OmS (Ω c) d.D d.N)
        (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) z) = d.sH c z := by
    intro z
    exact IsFractionRing.lift_algebraMap (h c) z
  have hOver : ∀ p, d.OverP c p =
      HNm.OverR (R := KTp K d.D d.N) (F := KTf K d.D d.N) (L := OmS (Ω c) d.D d.N) p := by
    intro p
    ext w
    simp only [Data.OverP, HNm.OverR, Set.mem_setOf_eq, hmap]
  have hset : {p | p ∈ d.HtOne ∧ ∃ w ∈ d.OverP c p, w (algebraMap (Ω c) (OmS (Ω c) d.D d.N) a) ≠ 0} =
      {p : Ideal (KTp K d.D d.N) | p.IsPrime ∧ p.height = 1 ∧
        ∃ w ∈ HNm.OverR (R := KTp K d.D d.N) (F := KTf K d.D d.N)
          (L := OmS (Ω c) d.D d.N) p,
          w (algebraMap (Ω c) (OmS (Ω c) d.D d.N) a) ≠ 0} := by
    ext p
    simp only [Set.mem_setOf_eq, Data.HtOne, hOver, and_assoc]
  have hSa : {p | p ∈ d.HtOne ∧ ∃ w ∈ d.OverP c p,
      w (algebraMap (Ω c) (OmS (Ω c) d.D d.N) a) ≠ 0}.Finite := by
    rw [hset]
    classical
    letI : Algebra (KTp K d.D d.N) (OmS (Ω c) d.D d.N) :=
      ((algebraMap (KTf K d.D d.N) (OmS (Ω c) d.D d.N)).comp
        (algebraMap (KTp K d.D d.N) (KTf K d.D d.N))).toAlgebra
    set_option synthInstance.maxHeartbeats 100000 in
    haveI : IsScalarTower (KTp K d.D d.N) (KTf K d.D d.N) (OmS (Ω c) d.D d.N) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let y := algebraMap (Ω c) (OmS (Ω c) d.D d.N) a
    have halg : ∀ z : OmS (Ω c) d.D d.N, IsAlgebraic (KTp K d.D d.N) z := fun z =>
      (IsFractionRing.isAlgebraic_iff (KTp K d.D d.N) (KTf K d.D d.N) (OmS (Ω c) d.D d.N)).mpr
        (Algebra.IsIntegral.isIntegral (R := KTf K d.D d.N) z).isAlgebraic
    obtain ⟨de, hde0, hde⟩ := (halg y).exists_integral_multiple
    obtain ⟨ei, hei0, hei⟩ := (halg y⁻¹).exists_integral_multiple
    have hprod0 : de * ei ≠ 0 := mul_ne_zero hde0 hei0
    have key : ∀ p : Ideal (KTp K d.D d.N), (∃ w ∈ HNm.OverR
        (R := KTp K d.D d.N) (F := KTf K d.D d.N) (L := OmS (Ω c) d.D d.N) p,
        w y ≠ 0) → de * ei ∈ p := by
      rintro p ⟨w, hw, hwy⟩
      simp only [HNm.OverR, Set.mem_setOf_eq] at hw
      by_contra hnot
      have hdep : de ∉ p := fun hd => hnot (p.mul_mem_right ei hd)
      have heip : ei ∉ p := fun he => hnot (p.mul_mem_left de he)
      have h0 : ∀ r : KTp K d.D d.N, 0 ≤ w
          (algebraMap (KTp K d.D d.N) (OmS (Ω c) d.D d.N) r) := fun r => (hw.2 r).1
      have hwde : w (algebraMap (KTp K d.D d.N) (OmS (Ω c) d.D d.N) de) = 0 :=
        le_antisymm (not_lt.mp fun hlt => hdep ((hw.2 de).2.mp hlt)) (hw.2 de).1
      have hwei : w (algebraMap (KTp K d.D d.N) (OmS (Ω c) d.D d.N) ei) = 0 :=
        le_antisymm (not_lt.mp fun hlt => heip ((hw.2 ei).2.mp hlt)) (hw.2 ei).1
      have h1 : 0 ≤ w (de • y) := HNm.nonneg_of_isIntegral w h0 hde
      have h2 : 0 ≤ w (ei • y⁻¹) := HNm.nonneg_of_isIntegral w h0 hei
      rw [Algebra.smul_def, AddValuation.map_mul, hwde, zero_add] at h1
      rw [Algebra.smul_def, AddValuation.map_mul, hwei, zero_add] at h2
      have h3 : w y + w y⁻¹ = 0 := by
        rw [← AddValuation.map_mul w y y⁻¹, mul_inv_cancel₀ hyne, AddValuation.map_one]
      exact hwy (HNm.wt_add_eq_zero h1 h2 h3)
    have hsub : {p : Ideal (KTp K d.D d.N) | p.IsPrime ∧ p.height = 1 ∧
        ∃ w ∈ HNm.OverR (R := KTp K d.D d.N) (F := KTf K d.D d.N)
          (L := OmS (Ω c) d.D d.N) p, w y ≠ 0} ⊆
        (fun q : KTp K d.D d.N => Ideal.span {q}) ''
          {q | q ∈ UniqueFactorizationMonoid.factors (de * ei)} := by
      rintro p ⟨hp, hh, hw⟩
      haveI := hp
      obtain ⟨g, hg, rfl⟩ := ValUFD.heightOne_principal p hh
      have hdvd : g ∣ de * ei := Ideal.mem_span_singleton.mp (key _ hw)
      obtain ⟨q, hq, hgq⟩ :=
        UniqueFactorizationMonoid.exists_mem_factors_of_dvd hprod0 hg.irreducible hdvd
      exact ⟨q, hq, Ideal.span_singleton_eq_span_singleton.mpr hgq.symm⟩
    exact ((Multiset.finite_toSet _).image _).subset hsub
  have hSj := (d.good_primes_properties hd h c).2.2.2 _ (hd.w_mem _ c) (hd.w_base c)
  set g : Ideal (KTp K d.D d.N) → KTf K d.D d.N := fun p =>
    algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) with hg
  have hfa : (d.HtOne ∩ Function.mulSupport fun p => g p ^ na p).Finite := by
    refine hSa.subset fun p hp => ⟨hp.1, ?_⟩
    have hn : na p ≠ 0 := by
      intro h0; apply hp.2; simp only [h0, zpow_zero]
    obtain ⟨w, hw, hne⟩ := exists_ne_zero_of_finsum_mem_ne_zero' hn
    refine ⟨w, hw.1, fun h0 => hne ?_⟩
    show (d.fze h c w : ℤ) * WithTop.untopD 0 (w _) = 0
    simp [h0]
  have hfj : (d.HtOne ∩ Function.mulSupport fun p => g p ^ d.nPMM h c (d.w (d.jc c) c) p).Finite := by
    refine hSj.subset fun p hp => ⟨hp.1, ?_⟩
    intro h0; apply hp.2; simp only [h0, zpow_zero]
  have hprod : (∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne), g p ^ d.nPMM h c (d.wx x c) p) =
      (∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne), g p ^ na p) *
        ∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne), g p ^ d.nPMM h c (d.w (d.jc c) c) p := by
    rw [← finprod_mem_mul_distrib' hfa hfj]
    refine finprod_mem_congr rfl fun p hp => ?_
    rw [hsplit p hp, zpow_add₀ (d.algebraMap_gen_ne_zero hp)]
  refine ⟨κ1 / κ3, div_ne_zero hκ1 hκ3, ?_⟩
  unfold heightSubstitutionCondition translatedForm
  rw [hF, e1, e3, hprod]
  unfold fZ
  have h3 : algebraMap K (KTf K d.D d.N) κ3 ≠ 0 := (map_ne_zero _).mpr hκ3
  rw [map_div₀]
  simp only [hg, hna]
  field_simp

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField ReciprocityTheory.MultiplicativeHeights

theorem isMultiHomogeneous_mul' {R : Type*} [CommSemiring R] {B n : ℕ} {a a' : Fin B → ℕ}
    {f g : MvPolynomial (Fin B × Fin n) R} (hf : IsMultiHomogeneous a f)
    (hg : IsMultiHomogeneous a' g) : IsMultiHomogeneous (a + a') (f * g) := by
  classical
  unfold IsMultiHomogeneous at *
  intro s hs b
  obtain ⟨s1, hs1, s2, hs2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul f g hs)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hf s1 hs1 b, hg s2 hs2 b]

theorem isMultiHomogeneous_one {R : Type*} [CommSemiring R] {B n : ℕ} :
    IsMultiHomogeneous (0 : Fin B → ℕ) (1 : MvPolynomial (Fin B × Fin n) R) := by
  classical
  unfold IsMultiHomogeneous
  intro s hs b
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_one] at hs
  split_ifs at hs with h
  · subst h
    simp
  · exact absurd rfl hs

theorem height_one_eq_zero {K : Type} [Field K] [NumberField K] {B n : ℕ} (hn : 0 < n) :
    h0 (1 : MvPolynomial (Fin B × Fin n) K) = 0 := by
  classical
  first
    | simp [h0, gaussAbs, blockSphereMean]
    | simp [h0, gaussAbs, blockSphereMean, MvPolynomial.support_one]

theorem height_pow_multiHomogeneous {K : Type} [Field K] [NumberField K] {B n : ℕ} (hn : 0 < n)
    {g : MvPolynomial (Fin B × Fin n) K} {a : Fin B → ℕ} (hg0 : g ≠ 0)
    (hg : IsMultiHomogeneous a g) (e : ℕ) :
    g ^ e ≠ 0 ∧ IsMultiHomogeneous (e • a) (g ^ e) ∧ h0 (g ^ e) = e * h0 g := by
  induction e with
  | zero => simp [height_one_eq_zero hn, isMultiHomogeneous_one]
  | succ e ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    refine ⟨pow_ne_zero _ hg0, ?_, ?_⟩
    · rw [pow_succ, succ_nsmul]; exact isMultiHomogeneous_mul' h2 hg
    · rw [pow_succ, (ReciprocityTheory.MultiplicativeHeights.Closed.gauss_height_additivity K B n _ _ _ _ hn h1 hg0 h2 hg).1, h3]
      push_cast; ring

theorem height_prod_pow_multiHomogeneous {K : Type} [Field K] [NumberField K] {B n : ℕ} (hn : 0 < n) {ι' : Type*}
    (T : Finset ι') (g : ι' → MvPolynomial (Fin B × Fin n) K) (e : ι' → ℕ)
    (hg : ∀ i ∈ T, g i ≠ 0 ∧ ∃ a, IsMultiHomogeneous a (g i)) :
    (∏ i ∈ T, g i ^ e i) ≠ 0 ∧ (∃ a, IsMultiHomogeneous a (∏ i ∈ T, g i ^ e i)) ∧
      h0 (∏ i ∈ T, g i ^ e i) = ∑ i ∈ T, (e i : ℝ) * h0 (g i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [height_one_eq_zero hn]; exact ⟨0, isMultiHomogeneous_one⟩
  | insert q T hq ih =>
    obtain ⟨h1, ⟨a1, h2⟩, h3⟩ := ih fun i hi => hg i (Finset.mem_insert_of_mem hi)
    obtain ⟨hq0, aq, hqa⟩ := hg q (Finset.mem_insert_self q T)
    obtain ⟨p1, p2, p3⟩ := height_pow_multiHomogeneous hn hq0 hqa (e q)
    rw [Finset.prod_insert hq, Finset.sum_insert hq]
    refine ⟨mul_ne_zero p1 h1, ⟨_, isMultiHomogeneous_mul' p2 h2⟩, ?_⟩
    rw [(ReciprocityTheory.MultiplicativeHeights.Closed.gauss_height_additivity K B n _ _ _ _ hn p1 h1 p2 h2).1, p3, h3]

namespace Data

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

variable (d : Data K ι Ω WT A)

private lemma ratio_eq_of_eq_smul' {Ω' V : Type*} [Field Ω'] [AddCommGroup V] [Module Ω' V] {f g : V} {a : Ω'}
    (hg : g ≠ 0) (h : f = a • g) : ratio f g = a := by
  have hex : ∃ b : Ω', f = b • g := ⟨a, h⟩
  unfold ratio
  rw [dite_eq_left hex]
  have hc := hex.choose_spec
  exact smul_left_injective Ω' hg (hc.symm.trans h)

theorem ratio_linearCombination_expand (hd : d.AxH 𝒜) (x : Fin (d.N + 1) → K) (c : ι) :
    ratio (Ω := Ω c) (d.wx x c) (d.w (d.jc c) c) =
      ∑ j, algebraMap K (Ω c) (x j) * ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) := by
  haveI := hd.tower c
  have hg : d.w (d.jc c) c ≠ 0 := hd.w_base c
  have hspan : ∀ f ∈ 𝒜 c d.wL, ∃ a : Ω c, f = a • d.w (d.jc c) c := by
    intro f hf
    have hne : (⟨d.w (d.jc c) c, hd.w_mem _ c⟩ : 𝒜 c d.wL) ≠ 0 := by
      intro h0
      exact hg (congrArg Subtype.val h0)
    obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' _ hne).mp (hd.finrank_one c d.wL) ⟨f, hf⟩
    exact ⟨a, (congrArg Subtype.val ha).symm⟩
  choose r hr using fun j => hspan (d.w j c) (hd.w_mem j c)
  have hrat : ∀ j, ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) = r j := fun j => ratio_eq_of_eq_smul' hg (hr j)
  simp only [hrat]
  apply ratio_eq_of_eq_smul' hg
  rw [Finset.sum_smul]
  unfold Data.wx
  rw [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [Pi.smul_apply, mul_smul, algebraMap_smul]
  conv_lhs => rw [hr j]

theorem untopD_le_untopD {u v : WithTop ℤ} (hu : u ≠ ⊤) (hv : v ≠ ⊤) (h : u ≤ v) :
    u.untopD 0 ≤ v.untopD 0 := by
  lift u to ℤ using hu
  lift v to ℤ using hv
  simpa using h

theorem ordMinMax_nonneg (hd : d.AxH 𝒜) (h : d.S1) (x : Fin (d.N + 1) → K) (c : ι)
    (hx : d.wx x c ≠ 0) {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne)
    {w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)} (hw : w ∈ d.GoodP c p) :
    0 ≤ d.ordMM c (d.Wres c w) (d.wx x c) := by
  rcases d.PlaceTrivialOrPositive hd h c p hp w hw.1 with htr | ⟨hA, htriv, j0, hj0, hint, _⟩
  · obtain ⟨a, ha, hne⟩ := hw.2
    exact absurd (htr a ha) hne
  have hmem := d.linearCombination_mem_section hd x c
  rw [d.ordMinMax_eq_ratio_untop_sub hd c _ hA j0 hj0 hint hmem hx, sub_nonneg]
  set v := d.Wres c w
  have hb := hd.w_base c
  have hm := hd.w_mem (d.jc c) c
  apply untopD_le_untopD (hA.1.1 _ (d.ratio_base_ne_zero hd c (hd.w_mem j0 c) hj0))
    (hA.1.1 _ (d.ratio_base_ne_zero hd c hmem hx))
  rw [d.ratio_linearCombination_expand hd x c]
  apply AddValuation.map_le_sum
  intro j _
  by_cases hxj : x j = 0
  · rw [hxj, map_zero, zero_mul, v.map_zero]; exact le_top
  rw [v.map_mul, htriv _ hxj, zero_add,
    d.ratio_mul_ratio_height hd c (hd.w_mem j c) (hd.w_mem j0 c) hm hj0 hb, v.map_mul]
  exact le_add_of_nonneg_left (hint j)

theorem multiplicity_nonneg (hd : d.AxH 𝒜) (h : d.S1) (x : Fin (d.N + 1) → K) (c : ι)
    (hx : d.wx x c ≠ 0) {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne) :
    0 ≤ d.nPMM h c (d.wx x c) p := by
  unfold Data.nPMM
  apply finsum_nonneg
  intro w
  apply finsum_nonneg
  intro hw
  refine mul_nonneg ?_ (d.ordMinMax_nonneg hd h x c hx hp hw)
  first
    | positivity
    | exact Nat.cast_nonneg _

theorem height_substituted_eq_finsum (hd : d.AxH 𝒜) (h : d.S1) (x : Fin (d.N + 1) → K)
    (hx : ∀ c, d.wx x c ≠ 0) (c : ι) (F : KTp K d.D d.N)
    (hF : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F = d.fZ h c) :
    d.translatedForm x F ≠ 0 ∧
    ∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
        (d.nPMM h c (d.wx x c) p : ℝ) * ReciprocityTheory.MultiplicativeHeights.h0 (d.gen p) =
      ReciprocityTheory.MultiplicativeHeights.h0 (d.translatedForm x F) := by
  classical
  have hmem := d.linearCombination_mem_section hd x c
  obtain ⟨κ1, hκ1, e1⟩ := d.SpecialFibreFactorization hd h c F hF x (hx c)
  have hS := (d.good_primes_properties hd h c).2.2.2 _ hmem (hx c)
  set T := hS.toFinset
  set n : Ideal (KTp K d.D d.N) → ℤ := fun p => d.nPMM h c (d.wx x c) p with hn
  have hT : ∀ p, p ∈ T ↔ p ∈ d.HtOne ∧ n p ≠ 0 := fun p => by rw [Set.Finite.mem_toFinset]; rfl
  have hgood : ∀ p ∈ T, d.gen p ≠ 0 ∧ ∃ a, IsMultiHomogeneous a (d.gen p) := by
    intro p hpT
    obtain ⟨hp, hnp⟩ := (hT p).mp hpT
    refine ⟨d.gen_ne_zero_of_htOne hp, _, (d.good_primes_properties hd h c).2.1 p hp ?_⟩
    obtain ⟨w, hw, _⟩ := exists_ne_zero_of_finsum_mem_ne_zero' hnp
    exact ⟨w, hw⟩
  set e : Ideal (KTp K d.D d.N) → ℕ := fun p => (n p).toNat with he
  have hne : ∀ p ∈ d.HtOne, n p = (e p : ℤ) := fun p hp =>
    (Int.toNat_of_nonneg (d.multiplicity_nonneg hd h x c (hx c) hp)).symm
  obtain ⟨P0, ⟨aP, hPm⟩, hPh⟩ := height_prod_pow_multiHomogeneous (K := K) (Nat.succ_pos d.N) T (fun p => d.gen p) e hgood
  have hprod : (∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ n p) =
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (∏ p ∈ T, d.gen p ^ e p) := by
    rw [finprod_mem_eq_prod_of_inter_mulSupport_eq _ (t := T), map_prod]
    · refine Finset.prod_congr rfl fun p hpT => ?_
      rw [hne p ((hT p).mp hpT).1, zpow_natCast, map_pow]
    · ext p
      simp only [Set.mem_inter_iff, Function.mem_mulSupport, Finset.mem_coe, hT]
      constructor
      · rintro ⟨hp, h1⟩
        refine ⟨⟨hp, fun h0 => h1 ?_⟩, h1⟩
        rw [h0, zpow_zero]
      · rintro ⟨⟨hp, _⟩, h1⟩; exact ⟨hp, h1⟩
  have hFx : d.translatedForm x F = MvPolynomial.C κ1 * ∏ p ∈ T, d.gen p ^ e p := by
    apply IsFractionRing.injective (KTp K d.D d.N) (KTf K d.D d.N)
    unfold translatedForm
    rw [e1, hprod, map_mul, ← MvPolynomial.algebraMap_eq,
      ← IsScalarTower.algebraMap_apply K (KTp K d.D d.N) (KTf K d.D d.N)]
  refine ⟨by rw [hFx]; exact mul_ne_zero (MvPolynomial.C_ne_zero.mpr hκ1) P0, ?_⟩
  rw [hFx, (ReciprocityTheory.MultiplicativeHeights.Closed.gauss_height_additivity K (d.D + 1) (d.N + 1) aP aP _ _ (Nat.succ_pos _) P0 P0 hPm hPm).2
    κ1 hκ1, hPh]
  rw [finsum_mem_eq_sum_of_inter_support_eq _ (t := T)]
  · refine Finset.sum_congr rfl fun p hpT => ?_
    rw [show ((d.nPMM h c (d.wx x c) p : ℤ) : ℝ) = ((e p : ℤ) : ℝ) from
      congrArg _ (hne p ((hT p).mp hpT).1)]
    simp
  · ext p
    simp only [Set.mem_inter_iff, Function.mem_support, Finset.mem_coe, hT]
    constructor
    · rintro ⟨hp, h1⟩
      refine ⟨⟨hp, fun h0 => h1 ?_⟩, h1⟩
      simp only [hn] at h0; rw [h0]; simp
    · rintro ⟨⟨hp, _⟩, h1⟩; exact ⟨hp, h1⟩

theorem fZ_and_substituted_ne_zero (hd : d.AxH 𝒜) (h : d.S1) (x : Fin (d.N + 1) → K)
    (hx : ∀ c, d.wx x c ≠ 0) (c : ι) (F : KTp K d.D d.N)
    (hF : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F = d.fZ h c) :
    F ≠ 0 ∧ d.translatedForm x F ≠ 0 := by
  have hne := (d.height_substituted_eq_finsum hd h x hx c F hF).1
  refine ⟨fun h0 => hne ?_, hne⟩
  rw [h0]
  first
    | simp [Data.translatedForm]
    | exact map_zero _

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MeasureTheory ReciprocityTheory.MultiplicativeHeights

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem eval_substituted_eq_eval_update (x : Fin (d.N + 1) → K) (F : KTp K d.D d.N) (sg : K →+* ℂ)
    (y : Fin (d.D + 1) × Fin (d.N + 1) → ℂ) :
    MvPolynomial.eval y (MvPolynomial.map sg (d.translatedForm x F)) =
      MvPolynomial.eval (fun v => if v.1 = 0 then sg (x v.2) else y v) (MvPolynomial.map sg F) := by
  unfold translatedForm
  induction F using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, MvPolynomial.aeval_X, MvPolynomial.map_X, MvPolynomial.eval_X]
    congr 1
    by_cases hv : v.1 = 0 <;> simp [hv]

theorem eval_substituted_shift_invariant (x : Fin (d.N + 1) → K) (F : KTp K d.D d.N) (sg : K →+* ℂ)
    (t0 : Fin (d.N + 1) → ℂ) (z : BlockSphere d.D (d.N + 1)) :
    MvPolynomial.eval (hintPt t0 z) (MvPolynomial.map sg (d.translatedForm x F)) =
      MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg (d.translatedForm x F)) := by
  rw [eval_substituted_eq_eval_update, eval_substituted_eq_eval_update]
  refine congrArg (fun y => MvPolynomial.eval y (MvPolynomial.map sg F)) (funext fun v => ?_)
  by_cases hv : v.1 = 0
  · simp only [hv, ↓reduceIte]
  · simp only [hv, ↓reduceIte]
    obtain ⟨a, b⟩ := v
    cases a using Fin.cases with
    | zero => exact absurd rfl hv
    | succ i => rfl

theorem sphereMean_substituted_eq_integral (x : Fin (d.N + 1) → K) (F : KTp K d.D d.N) (sg : K →+* ℂ) :
    blockSphereMean (d.D + 1) (d.N + 1) (MvPolynomial.map sg (d.translatedForm x F)) =
      ∫ z, Real.log ‖MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg (d.translatedForm x F))‖
        ∂(blockSphereProb d.D (d.N + 1)) := by
  have hpt : ∀ z : BlockSphere (d.D + 1) (d.N + 1),
      MvPolynomial.eval (blockPoint z) (MvPolynomial.map sg (d.translatedForm x F)) =
        MvPolynomial.eval (hintPt 0 (Fin.tail z)) (MvPolynomial.map sg (d.translatedForm x F)) := by
    intro z
    rw [← eval_substituted_shift_invariant d x F sg (spherePoint (z 0)) (Fin.tail z)]
    refine congrArg (fun y => MvPolynomial.eval y (MvPolynomial.map sg (d.translatedForm x F)))
      (funext fun v => ?_)
    obtain ⟨a, b⟩ := v
    cases a using Fin.cases with
    | zero => rfl
    | succ i => rfl
  have key : ∀ g : (Fin d.D → UnitSphereC (d.N + 1)) → ℝ,
      ∫ z, g (Fin.tail z) ∂(Measure.pi fun _ : Fin (d.D + 1) => sphereProb (d.N + 1)) =
        ∫ w, g w ∂(Measure.pi fun _ : Fin d.D => sphereProb (d.N + 1)) := by
    intro g
    haveI hpr : IsProbabilityMeasure (sphereProb (d.N + 1)) :=
      ReciprocityTheory.MultiplicativeHeights.isProbabilityMeasure_sphereProb (Nat.succ_pos _)
    haveI hfin : IsFiniteMeasure (sphereProb (d.N + 1)) :=
      ⟨by rw [MeasureTheory.measure_univ]; exact ENNReal.one_lt_top⟩
    haveI hsf : SigmaFinite (sphereProb (d.N + 1)) :=
      @MeasureTheory.IsFiniteMeasure.toSigmaFinite _ _ _ hfin
    haveI hsf' : ∀ i : Fin (d.D + 1), SigmaFinite ((fun _ : Fin (d.D + 1) => sphereProb (d.N + 1)) i) :=
      fun _ => hsf
    have hmp := MeasureTheory.measurePreserving_piFinSuccAbove
      (fun _ : Fin (d.D + 1) => sphereProb (d.N + 1)) 0
    calc ∫ z, g (Fin.tail z) ∂(Measure.pi fun _ : Fin (d.D + 1) => sphereProb (d.N + 1))
        = ∫ z, (fun p : UnitSphereC (d.N + 1) × (Fin d.D → UnitSphereC (d.N + 1)) => g p.2)
            (MeasurableEquiv.piFinSuccAbove (fun _ => UnitSphereC (d.N + 1)) 0 z)
            ∂(Measure.pi fun _ : Fin (d.D + 1) => sphereProb (d.N + 1)) := by
          congr 1
      _ = ∫ p, g p.2 ∂((sphereProb (d.N + 1)).prod
            (Measure.pi fun _ : Fin d.D => sphereProb (d.N + 1))) :=
          hmp.integral_comp' (fun p : UnitSphereC (d.N + 1) × (Fin d.D → UnitSphereC (d.N + 1)) => g p.2)
      _ = ∫ w, g w ∂(Measure.pi fun _ : Fin d.D => sphereProb (d.N + 1)) := by
          rw [MeasureTheory.integral_fun_snd]
          simp
  unfold blockSphereMean blockSphereProb
  simp_rw [hpt]
  exact key (fun w => Real.log ‖MvPolynomial.eval (hintPt 0 w) (MvPolynomial.map sg (d.translatedForm x F))‖)

theorem sphereMean_fubini {F : MvPolynomial (Fin (d.D + 1) × Fin (d.N + 1)) ℂ} {a : Fin (d.D + 1) → ℕ}
    (hF0 : F ≠ 0) (hF : IsMultiHomogeneous a F) :
    blockSphereMean (d.D + 1) (d.N + 1) F =
      ∫ z, (∫ s, Real.log ‖MvPolynomial.eval (hintPt (spherePoint s) z) F‖ ∂(sphereProb (d.N + 1)))
        ∂(blockSphereProb d.D (d.N + 1)) := by
  have hn : 0 < d.N + 1 := Nat.succ_pos _
  haveI := sphereMeasure_isProbability hn
  haveI := blockSphereMeasure_isProbability (B := d.D) hn
  set G : UnitSphereC (d.N + 1) × BlockSphere d.D (d.N + 1) → ℝ :=
    fun p => Real.log ‖MvPolynomial.eval (hintPt (spherePoint p.1) p.2) F‖ with hG
  have hmp := hint_mpSplit d.D (d.N + 1) hn
  have hint : Integrable G ((sphereProb (d.N + 1)).prod (blockSphereProb d.D (d.N + 1))) := by
    rw [← hmp.integrable_comp_emb
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d.D + 1) => UnitSphereC (d.N + 1)) 0).measurableEmbedding]
    refine (ReciprocityTheory.MultiplicativeHeights.Closed.sphereLogIntegrable (d.D + 1) (d.N + 1) a F hF0 hF).congr
      (Filter.Eventually.of_forall fun z => ?_)
    simp only [Function.comp_apply, hG]
    rw [hint_blockPoint_eq]
    rfl
  rw [← integral_prod_symm G hint]
  unfold blockSphereMean
  rw [← hmp.integral_comp
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d.D + 1) => UnitSphereC (d.N + 1)) 0).measurableEmbedding]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [hG]
  rw [hint_blockPoint_eq]
  rfl

end Data

end ReciprocityTheory.ChartRestriction.G.T0
