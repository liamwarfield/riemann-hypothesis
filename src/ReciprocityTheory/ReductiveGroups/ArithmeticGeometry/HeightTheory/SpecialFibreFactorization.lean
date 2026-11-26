module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.DecompBlock0
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.GeneratorNeZeroOfHeight
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.NormFactorizationClause

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.BasisBlock0
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

theorem basis_block0 (hd : d.AxH 𝒜) (h : d.S1) (c : ι) :
    letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra;
    ∃ (n : ℕ) (b : Module.Basis (Fin n) (KTf K d.D d.N) (OmS (Ω c) d.D d.N)) (Q0 : KTp K d.D d.N)
      (M : Fin (d.N + 1) → Matrix (Fin n) (Fin n) (KTp K d.D d.N)),
      Q0 ≠ 0 ∧ (∀ x, d.sub0 x Q0 = Q0) ∧ (∀ j a a' x, d.sub0 x (M j a a') = M j a a') ∧
      ∀ j, Algebra.leftMulMatrix b (algebraMap (Ω c) (OmS (Ω c) d.D d.N)
          (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c))) =
        (M j).map fun q => algebraMap (KTp K d.D d.N) (KTf K d.D d.N) q /
          algebraMap (KTp K d.D d.N) (KTf K d.D d.N) Q0 := by
  letI _inst : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  obtain ⟨L, E, _, _, _, _, eL, eE, hcomp, hconst, hLc⟩ := d.decomp_block0 hd h c
  letI iLY : Algebra (FractionRing (MvPolynomial (Fin (d.N + 1)) L))
      (FractionRing (MvPolynomial (Fin (d.N + 1)) E)) :=
    (VariableBasisExtension.liftY (L := L) (E := E) (σ := Fin (d.N + 1))).toAlgebra
  obtain ⟨b', _, hb'2⟩ := VariableBasisExtension.basis_extend (σ := Fin (d.N + 1)) (Module.finBasis L E)
  letI iFO : Algebra (FractionRing (MvPolynomial (Fin (d.N + 1)) L)) (OmS (Ω c) d.D d.N) :=
    ((d.KTtoS h c).comp eL.symm.toRingHom).toAlgebra
  have hback : ∀ q : FractionRing (MvPolynomial (Fin (d.N + 1)) L),
      eE.symm (VariableBasisExtension.liftY q) = d.KTtoS h c (eL.symm q) := by
    intro q
    have h1 := hcomp (eL.symm q)
    rw [RingEquiv.apply_symm_apply] at h1
    rw [← h1, RingEquiv.symm_apply_apply]
  let eEl : FractionRing (MvPolynomial (Fin (d.N + 1)) E) ≃ₗ[FractionRing (MvPolynomial (Fin (d.N + 1)) L)]
      OmS (Ω c) d.D d.N :=
    AddEquiv.toLinearEquiv eE.symm.toAddEquiv (by
      intro q x
      show eE.symm (q • x) = q • eE.symm x
      rw [Algebra.smul_def, Algebra.smul_def, map_mul]
      congr 1
      exact hback q)
  let B0 := b'.map eEl
  let B : Module.Basis (Fin (Module.finrank L E)) (KTf K d.D d.N) (OmS (Ω c) d.D d.N) :=
    B0.mapCoeffs eL.symm (fun q x => rfl)
  have htr : ∀ (y : OmS (Ω c) d.D d.N) a a', Algebra.leftMulMatrix B y a a' =
      eL.symm (Algebra.leftMulMatrix b' (eE y) a a') := by
    intro y a a'
    rw [Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul]
    have hy : eEl.symm (y * eEl (b' a')) = eE y * b' a' := by
      show eE (y * eE.symm (b' a')) = eE y * b' a'
      rw [map_mul, RingEquiv.apply_symm_apply]
    simp only [B]
    erw [Module.Basis.mapCoeffs_apply, Module.Basis.mapCoeffs_repr]
    simp only [LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply, Finsupp.mapRange.linearEquiv_apply,
      Finsupp.mapRange_apply, B0, Module.Basis.map_apply, Module.Basis.map_repr]
    rw [hy]
    exact rfl
  choose e he using hconst
  choose P Q hQ hPinv hQinv hPQ using hLc
  let mm : Fin (d.N + 1) × Fin (Module.finrank L E) × Fin (Module.finrank L E) → L := fun t =>
    Algebra.leftMulMatrix (Module.finBasis L E)
      (e (ratio (Ω := Ω c) (d.w t.1 c) (d.w (d.jc c) c))) t.2.1 t.2.2
  have hinj := IsFractionRing.injective (KTp K d.D d.N) (KTf K d.D d.N)
  have hne : ∀ t, algebraMap (KTp K d.D d.N) (KTf K d.D d.N)
      (∏ s ∈ Finset.univ.erase t, Q (mm s)) ≠ 0 := by
    intro t
    rw [map_ne_zero_iff _ hinj]
    exact Finset.prod_ne_zero_iff.mpr fun s _ => hQ _
  have hfrac : ∀ t, algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (P (mm t)) /
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (Q (mm t)) =
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (P (mm t) * ∏ s ∈ Finset.univ.erase t, Q (mm s)) /
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (∏ s, Q (mm s)) := by
    intro t
    rw [← Finset.mul_prod_erase Finset.univ (fun s => Q (mm s)) (Finset.mem_univ t), map_mul, map_mul,
      mul_div_mul_right _ _ (hne t)]
  have hLtoC : ∀ l : L, algebraMap L (FractionRing (MvPolynomial (Fin (d.N + 1)) L)) l =
      algebraMap (MvPolynomial (Fin (d.N + 1)) L) (FractionRing (MvPolynomial (Fin (d.N + 1)) L))
        (MvPolynomial.C l) := by
    intro l
    rw [IsScalarTower.algebraMap_apply L (MvPolynomial (Fin (d.N + 1)) L)
      (FractionRing (MvPolynomial (Fin (d.N + 1)) L)), MvPolynomial.algebraMap_eq]
  refine ⟨Module.finrank L E, B, ∏ s, Q (mm s),
    fun j => Matrix.of fun a a' => P (mm (j, a, a')) * ∏ s ∈ Finset.univ.erase (j, a, a'), Q (mm s),
    ?_, ?_, ?_, ?_⟩
  · exact Finset.prod_ne_zero_iff.mpr fun s _ => hQ _
  · intro x
    rw [map_prod]
    exact Finset.prod_congr rfl fun s _ => hQinv _ x
  · intro j a a' x
    simp only [Matrix.of_apply]
    rw [map_mul, map_prod, hPinv]
    congr 1
    exact Finset.prod_congr rfl fun s _ => hQinv _ x
  · intro j
    ext a a'
    simp only [Matrix.map_apply, Matrix.of_apply]
    rw [htr, he, hb'2, Matrix.map_apply, hLtoC, hPQ]
    exact hfrac (j, a, a')

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.X4v4RatioSpec
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

theorem x4v4_ratio_spec {Ω' V : Type*} [Field Ω'] [AddCommGroup V] [Module Ω' V] {f g : V}
    (hg : g ≠ 0) {a : Ω'} (hf : f = a • g) : ratio (Ω := Ω') f g = a := by
  have hex : ∃ b : Ω', f = b • g := ⟨a, hf⟩
  unfold ratio
  rw [dite_eq_left hex]
  have h2 : hex.choose • g = a • g := hex.choose_spec.symm.trans hf
  exact smul_left_injective Ω' hg h2

theorem x4v4_eq_smul (hd : d.AxH 𝒜) (c : ι) {f : A c} (hf : f ∈ 𝒜 c d.wL) :
    f = ratio (Ω := Ω c) f (d.w (d.jc c) c) • d.w (d.jc c) c := by
  have hw0 : d.w (d.jc c) c ≠ 0 := hd.w_base c
  have hv : (⟨d.w (d.jc c) c, hd.w_mem _ c⟩ : 𝒜 c d.wL) ≠ 0 := by
    intro h0
    apply hw0
    simpa using congrArg Subtype.val h0
  obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' _ hv).1 (hd.finrank_one c d.wL) ⟨f, hf⟩
  have hfa : f = a • d.w (d.jc c) c := by
    have h1 := congrArg Subtype.val ha
    simpa using h1.symm
  rw [x4v4_ratio_spec hw0 hfa]
  exact hfa

theorem x4v4_ratio_ne (hd : d.AxH 𝒜) (c : ι) {f : A c} (hf : f ∈ 𝒜 c d.wL) (hf0 : f ≠ 0) :
    ratio (Ω := Ω c) f (d.w (d.jc c) c) ≠ 0 := by
  intro h0
  apply hf0
  rw [x4v4_eq_smul d hd c hf, h0, zero_smul]

theorem x4v4_wx_mem (hd : d.AxH 𝒜) (x : Fin (d.N + 1) → K) (c : ι) : d.wx x c ∈ 𝒜 c d.wL := by
  haveI := hd.tower c
  have e : d.wx x c = ∑ j, x j • d.w j c := by
    simp only [Data.wx, Finset.sum_apply, Pi.smul_apply]
  rw [e]
  refine Submodule.sum_mem _ (fun j _ => ?_)
  rw [← algebraMap_smul (Ω c) (x j) (d.w j c)]
  exact Submodule.smul_mem _ _ (hd.w_mem j c)

theorem x4v4_gen_ne {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne) :
    algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ≠ 0 := by
  refine (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr ?_
  obtain ⟨hprime, hh⟩ := hp
  have hpr := UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hh
  unfold gen
  rw [dite_eq_left hpr]
  intro h0
  exact p.ne_bot_of_height_eq_one hh ((Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero p).mpr h0)

theorem x4v4_ordMM (hd : d.AxH 𝒜) (h : d.S1) (c : ι) {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne)
    {w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)} (hw : w ∈ d.GoodP c p) {f : A c}
    (hf : f ∈ 𝒜 c d.wL) (hf0 : f ≠ 0) :
    d.ordMM c (d.Wres c w) f = WithTop.untopD 0 (d.Wres c w (ratio (Ω := Ω c) f (d.w (d.jc c) c))) +
      d.ordMM c (d.Wres c w) (d.w (d.jc c) c) := by
  have hA := d.good_adm hd h c hp hw
  have e : ((d.ord c (d.Wres c w) d.wL f : ℤ) : WithTop ℤ) =
      d.Wres c w (ratio (Ω := Ω c) f (d.w (d.jc c) c)) +
        (d.ord c (d.Wres c w) d.wL (d.w (d.jc c) c) : WithTop ℤ) := by
    conv_lhs => rw [d.x4v4_eq_smul hd c hf]
    exact hd.ord_smul c _ hA _ (hd.w_mem _ _) (hd.w_base c) (d.x4v4_ratio_ne hd c hf hf0)
  have hfin : d.Wres c w (ratio (Ω := Ω c) f (d.w (d.jc c) c)) =
      ((d.ord c (d.Wres c w) d.wL f - d.ord c (d.Wres c w) d.wL (d.w (d.jc c) c) : ℤ) : WithTop ℤ) := by
    revert e
    generalize d.Wres c w (ratio (Ω := Ω c) f (d.w (d.jc c) c)) = t
    intro e
    induction t using WithTop.recTopCoe with
    | top => simp at e
    | coe t =>
      have e' : d.ord c (d.Wres c w) d.wL f = t + d.ord c (d.Wres c w) d.wL (d.w (d.jc c) c) := by
        exact_mod_cast e
      rw [e']
      congr 1
      ring
  unfold ordMM
  rw [hfin, WithTop.untopD_coe]
  ring

theorem x4v4_split (hd : d.AxH 𝒜) (h : d.S1) (c : ι) {p : Ideal (KTp K d.D d.N)}
    (hp : p ∈ d.HtOne) {f : A c} (hf : f ∈ 𝒜 c d.wL) (hf0 : f ≠ 0) :
    d.nPMM h c f p =
      (∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.GoodP c p),
        (d.fze h c w : ℤ) * WithTop.untopD 0 (d.Wres c w (ratio (Ω := Ω c) f (d.w (d.jc c) c)))) +
      d.nPMM h c (d.w (d.jc c) c) p := by
  have hfin := d.goodP_finite hd h c hp
  unfold nPMM
  rw [← finsum_mem_add_distrib hfin]
  refine finsum_mem_congr rfl fun w hw => ?_
  rw [d.x4v4_ordMM hd h c hp hw hf hf0]
  ring

theorem norm_ratio_pi (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (x : Fin (d.N + 1) → K)
    (hx : d.wx x c ≠ 0) :
    ∃ κ : K, κ ≠ 0 ∧
      (letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra;
        Algebra.norm (KTf K d.D d.N) (algebraMap (Ω c) (OmS (Ω c) d.D d.N)
            (ratio (Ω := Ω c) (d.wx x c) (d.w (d.jc c) c))) *
          ∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
            algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ d.nPMM h c (d.w (d.jc c) c) p =
        algebraMap K (KTf K d.D d.N) κ *
          ∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
            algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ d.nPMM h c (d.wx x c) p) := by
  classical
  have hmem := d.x4v4_wx_mem hd x c
  have hg0 := d.x4v4_ratio_ne hd c hmem hx
  obtain ⟨κ, hκ, hN⟩ := (d.norm_factorization hd h).1 c _ hg0
  refine ⟨κ, hκ, ?_⟩
  rw [hN, mul_assoc]
  congr 1
  set na : Ideal (KTp K d.D d.N) → ℤ := fun p =>
    ∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.GoodP c p),
      (d.fze h c w : ℤ) * WithTop.untopD 0
        (d.Wres c w (ratio (Ω := Ω c) (d.wx x c) (d.w (d.jc c) c))) with hna
  set G : Ideal (KTp K d.D d.N) → KTf K d.D d.N := fun p =>
    algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) with hG
  have hsplit : ∀ p ∈ d.HtOne, d.nPMM h c (d.wx x c) p = na p + d.nPMM h c (d.w (d.jc c) c) p :=
    fun p hp => d.x4v4_split hd h c hp hmem hx
  have hSx := (d.good_primes_properties hd h c).2.2.2 _ hmem hx
  have hSj := (d.good_primes_properties hd h c).2.2.2 _ (hd.w_mem _ c) (hd.w_base c)
  have hfa : (d.HtOne ∩ Function.mulSupport fun p => G p ^ na p).Finite := by
    refine (hSx.union hSj).subset fun p hp => ?_
    have hn : na p ≠ 0 := by
      intro h0; apply hp.2; simp only [h0, zpow_zero]
    by_contra hc
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_and, not_not] at hc
    apply hn
    have e := hsplit p hp.1
    rw [hc.1 hp.1, hc.2 hp.1] at e
    omega
  have hfj : (d.HtOne ∩ Function.mulSupport fun p => G p ^ d.nPMM h c (d.w (d.jc c) c) p).Finite := by
    refine hSj.subset fun p hp => ⟨hp.1, ?_⟩
    intro h0; apply hp.2; simp only [h0, zpow_zero]
  show (∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne), G p ^ na p) *
      (∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne), G p ^ d.nPMM h c (d.w (d.jc c) c) p) =
    ∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne), G p ^ d.nPMM h c (d.wx x c) p
  rw [← finprod_mem_mul_distrib' hfa hfj]
  refine finprod_mem_congr rfl fun p hp => ?_
  rw [hsplit p hp, zpow_add₀ (d.x4v4_gen_ne hp)]

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.SubstRowZeroFixOfDegreeZero
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

theorem substRowZero_fix_of_degree_zero (x : Fin (d.N + 1) → K) (q : KTp K d.D d.N)
    (hq : ∀ s ∈ q.support, ∑ j, s (0, j) = 0) : d.sub0 x q = q := by
  conv_lhs => rw [q.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  conv_rhs => rw [q.as_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have h0 : ∀ j, s (0, j) = 0 := fun j =>
    (Finset.sum_eq_zero_iff.mp (hq s hs)) j (Finset.mem_univ _)
  rw [MvPolynomial.aeval_monomial, MvPolynomial.monomial_eq, MvPolynomial.algebraMap_eq]
  congr 1
  refine Finsupp.prod_congr fun v hv => ?_
  have hv0 : v.1 ≠ 0 := by
    intro h1
    apply Finsupp.mem_support_iff.mp hv
    have e : ((0 : Fin (d.D + 1)), v.2) = v := Prod.ext h1.symm rfl
    rw [← e]
    exact h0 v.2
  simp [hv0]

theorem pi_free (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (f : A c) :
    ∃ Pp Pm : KTp K d.D d.N, Pm ≠ 0 ∧ (∀ x, d.sub0 x Pp = Pp) ∧ (∀ x, d.sub0 x Pm = Pm) ∧
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) Pp =
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) Pm *
          ∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
            algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ d.nPMM h c f p := by
  classical
  have hfix : ∀ p ∈ d.HtOne, d.nPMM h c f p ≠ 0 → ∀ x, d.sub0 x (d.gen p) = d.gen p := by
    intro p hp hn x
    have hw : ∃ w, w ∈ d.GoodP c p := by
      by_contra hno
      push_neg at hno
      exact hn (by simp [Data.nPMM, hno])
    have hm := d.GeneratorMultiHomogeneous hd h c p hp hw
    refine d.substRowZero_fix_of_degree_zero x (d.gen p) fun s hs => ?_
    simpa using hm s hs 0
  rw [finprod_mem_def, finprod_def]
  split_ifs with hfin
  · set T := hfin.toFinset with hT
    have hTmem : ∀ p ∈ T, p ∈ d.HtOne ∧ d.nPMM h c f p ≠ 0 := by
      intro p hpT
      have hpT' : p ∈ Function.mulSupport (d.HtOne.mulIndicator fun p =>
          (algebraMap (KTp K d.D d.N) (KTf K d.D d.N)) (d.gen p) ^ d.nPMM h c f p) :=
        (Set.Finite.mem_toFinset (hs := hfin)).mp hpT
      rw [Function.mem_mulSupport] at hpT'
      by_cases hp : p ∈ d.HtOne
      · refine ⟨hp, fun h0 => hpT' ?_⟩
        simp [Set.mulIndicator_of_mem hp, h0]
      · simp [hp] at hpT'
    refine ⟨∏ p ∈ T, d.gen p ^ (d.nPMM h c f p).toNat,
      ∏ p ∈ T, d.gen p ^ (-d.nPMM h c f p).toNat, ?_, ?_, ?_, ?_⟩
    · exact Finset.prod_ne_zero_iff.mpr fun p hp => pow_ne_zero _ (d.generator_ne_zero_of_height p (hTmem p hp).1)
    · intro x
      rw [map_prod]
      exact Finset.prod_congr rfl fun p hp => by
        rw [map_pow, hfix p (hTmem p hp).1 (hTmem p hp).2 x]
    · intro x
      rw [map_prod]
      exact Finset.prod_congr rfl fun p hp => by
        rw [map_pow, hfix p (hTmem p hp).1 (hTmem p hp).2 x]
    · rw [map_prod, map_prod, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun p hp => ?_
      rw [Set.mulIndicator_of_mem (hTmem p hp).1]
      have ha : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ≠ 0 := by
        rw [Ne, ← map_zero (algebraMap (KTp K d.D d.N) (KTf K d.D d.N)),
          (IsFractionRing.injective (KTp K d.D d.N) (KTf K d.D d.N)).eq_iff]
        exact d.generator_ne_zero_of_height p (hTmem p hp).1
      rw [map_pow, map_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ ha]
      congr 1
      omega
  · exact ⟨1, 1, one_ne_zero, fun x => map_one _, fun x => map_one _, by simp⟩

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.NormGenericRatioSpec
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

theorem hx4v2_ratio_smul {Ω V : Type*} [Field Ω] [AddCommGroup V] [Module Ω V] {g : V}
    (hg : g ≠ 0) (s : Ω) : ratio (Ω := Ω) (s • g) g = s := by
  unfold ratio
  have hex : ∃ a : Ω, s • g = a • g := ⟨s, rfl⟩
  rw [dite_eq_left hex]
  exact (smul_left_injective Ω hg hex.choose_spec).symm

theorem hx4v2_eq_ratio_smul {Ω V : Type*} [Field Ω] [AddCommGroup V] [Module Ω V]
    (W : Submodule Ω V) (hW : Module.finrank Ω W = 1) {f g : V} (hf : f ∈ W) (hgW : g ∈ W)
    (hg : g ≠ 0) : f = ratio (Ω := Ω) f g • g := by
  have hg' : (⟨g, hgW⟩ : W) ≠ 0 := fun e => hg (congrArg Subtype.val e)
  obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' (⟨g, hgW⟩ : W) hg').mp hW ⟨f, hf⟩
  have hex : ∃ a : Ω, f = a • g := ⟨a, (congrArg Subtype.val ha).symm⟩
  unfold ratio
  rw [dite_eq_left hex]
  exact hex.choose_spec

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem hx4v2_ratio_wx (hd : d.AxH 𝒜) (c : ι) (x : Fin (d.N + 1) → K) :
    ratio (Ω := Ω c) (d.wx x c) (d.w (d.jc c) c) =
      ∑ j, algebraMap K (Ω c) (x j) * ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) := by
  have := hd.tower c
  have hg := hd.w_base c
  have hrep : ∀ j, d.w j c = ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) • d.w (d.jc c) c :=
    fun j => hx4v2_eq_ratio_smul _ (hd.finrank_one c d.wL) (hd.w_mem j c) (hd.w_mem (d.jc c) c) hg
  have hsum : d.wx x c = (∑ j, algebraMap K (Ω c) (x j) *
      ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c)) • d.w (d.jc c) c := by
    simp only [Data.wx, Finset.sum_apply, Pi.smul_apply]
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    conv_lhs => rw [hrep j]
    rw [mul_smul, algebraMap_smul]
  rw [hsum, hx4v2_ratio_smul hg]

theorem norm_generic_ratio_spec (hd : d.AxH 𝒜) (h : d.S1) (c : ι) :
    ∃ P Q : KTp K d.D d.N, Q ≠ 0 ∧ (∀ x, d.sub0 x Q = Q) ∧
      (letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra;
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) P =
          algebraMap (KTp K d.D d.N) (KTf K d.D d.N) Q * Algebra.norm (KTf K d.D d.N) (d.rationalBaseRow c)) ∧
      ∀ x : Fin (d.N + 1) → K, d.wx x c ≠ 0 →
        (letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra;
          algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.sub0 x P) =
            algebraMap (KTp K d.D d.N) (KTf K d.D d.N) Q *
              Algebra.norm (KTf K d.D d.N) (algebraMap (Ω c) (OmS (Ω c) d.D d.N)
                (ratio (Ω := Ω c) (d.wx x c) (d.w (d.jc c) c)))) := by
  let _ : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  obtain ⟨n, b, Q0, M, hQ0, hQ0s, hMs, hM⟩ :=
    ReciprocityTheory.ChartRestriction.G.T0.Data.basis_block0 d hd h c
  let r : Fin (d.N + 1) → OmS (Ω c) d.D d.N := fun j =>
    algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c))
  let ι0 : KTp K d.D d.N →+* KTf K d.D d.N := algebraMap (KTp K d.D d.N) (KTf K d.D d.N)
  have hQ0' : ι0 Q0 ≠ 0 := fun e =>
    hQ0 (IsFractionRing.injective (KTp K d.D d.N) (KTf K d.D d.N) (by rw [e, map_zero]))
  have key : ∀ a : Fin (d.N + 1) → KTp K d.D d.N,
      Algebra.norm (KTf K d.D d.N) (∑ j, ι0 (a j) • r j) = ι0 (∑ j, a j • M j).det / ι0 Q0 ^ n := by
    intro a
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Algebra.norm_eq_matrix_det b, map_sum]
    simp_rw [map_smul]
    have hmat : (∑ j, ι0 (a j) • Algebra.leftMulMatrix b (r j)) =
        (ι0 Q0)⁻¹ • (∑ j, a j • M j).map ι0 := by
      ext i i'
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Matrix.smul_apply, Matrix.map_apply, Matrix.sum_apply, Matrix.sum_apply, map_sum,
        Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hM j, Matrix.smul_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul,
        smul_eq_mul, map_mul]
      ring
    rw [hmat, Matrix.det_smul, Fintype.card_fin]
    have hdet : ((∑ j, a j • M j).map ι0).det = ι0 (∑ j, a j • M j).det :=
      (RingHom.map_det ι0 _).symm
    rw [hdet, inv_pow, div_eq_mul_inv, mul_comm]
  have hw0 : d.rationalBaseRow c = ∑ j, ι0 (MvPolynomial.X ((0 : Fin (d.D + 1)), j) : KTp K d.D d.N) • r j := by
    simp only [Data.rationalBaseRow]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
    simp only [Data.KTtoS, ι0, IsFractionRing.lift_algebraMap, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, r]
  refine ⟨(∑ j, (MvPolynomial.X ((0 : Fin (d.D + 1)), j) : KTp K d.D d.N) • M j).det, Q0 ^ n, pow_ne_zero _ hQ0,
    fun x => by rw [map_pow, hQ0s], ?_, ?_⟩
  · show ι0 _ = ι0 (Q0 ^ n) * Algebra.norm (KTf K d.D d.N) (d.rationalBaseRow c)
    rw [hw0, key, map_pow]
    field_simp
  · intro x _
    have hs : d.sub0 x (∑ j, (MvPolynomial.X ((0 : Fin (d.D + 1)), j) : KTp K d.D d.N) • M j).det =
        (∑ j, (MvPolynomial.C (x j) : KTp K d.D d.N) • M j).det := by
      have hmd := RingHom.map_det (d.sub0 x : KTp K d.D d.N →+* KTp K d.D d.N)
        (∑ j, (MvPolynomial.X ((0 : Fin (d.D + 1)), j) : KTp K d.D d.N) • M j)
      rw [RingHom.coe_coe] at hmd
      rw [hmd]
      congr 1
      ext i i'
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply,
        smul_eq_mul, map_sum, map_mul, RingHom.coe_coe, hMs]
      simp
    have hr : algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.wx x c) (d.w (d.jc c) c)) =
        ∑ j, ι0 (MvPolynomial.C (x j) : KTp K d.D d.N) • r j := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [d.hx4v2_ratio_wx hd c x, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
      congr 1
      simp only [Data.KTtoS, ι0, IsFractionRing.lift_algebraMap, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe]
      rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]
      exact (IsScalarTower.algebraMap_apply K (Ω c) (OmS (Ω c) d.D d.N) (x j)).symm
    show ι0 _ = ι0 (Q0 ^ n) * _
    rw [hs, hr, key, map_pow]
    field_simp

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

theorem SpecialFibreFactorization (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (F : KTp K d.D d.N)
    (hF : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F = d.fZ h c)
    (x : Fin (d.N + 1) → K) (hx : d.wx x c ≠ 0) :
    ∃ κ : K, κ ≠ 0 ∧
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N)
        (MvPolynomial.aeval (fun v : TVar d.D d.N =>
          if v.1 = 0 then MvPolynomial.C (x v.2) else MvPolynomial.X v) F) =
      algebraMap K (KTf K d.D d.N) κ *
        ∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
          algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ d.nPMM h c (d.wx x c) p := by
  classical
  obtain ⟨P, Q, hQ0, hQx, hPQ, hspec⟩ := d.norm_generic_ratio_spec hd h c
  obtain ⟨Pp, Pm, hPm0, hPpx, hPmx, hPi⟩ := d.pi_free hd h c (d.w (d.jc c) c)
  obtain ⟨κ, hκ, hκeq⟩ := d.norm_ratio_pi hd h c x hx
  refine ⟨κ, hκ, ?_⟩
  have hφinj := IsFractionRing.injective (KTp K d.D d.N) (KTf K d.D d.N)
  have hpoly : Q * F * Pm = P * Pp := by
    apply hφinj
    simp only [map_mul]
    rw [hF, hPi, hPQ]
    simp only [fZ]
    ring
  have hsub := congrArg (d.sub0 x) hpoly
  simp only [map_mul, hQx, hPmx, hPpx] at hsub
  have hφ := congrArg (algebraMap (KTp K d.D d.N) (KTf K d.D d.N)) hsub
  simp only [map_mul] at hφ
  rw [hspec x hx, hPi] at hφ
  have hQ' : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) Q ≠ 0 :=
    (map_ne_zero_iff _ hφinj).mpr hQ0
  have hPm' : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) Pm ≠ 0 :=
    (map_ne_zero_iff _ hφinj).mpr hPm0
  rw [← hκeq]
  apply mul_left_cancel₀ (mul_ne_zero hQ' hPm')
  calc _ = algebraMap (KTp K d.D d.N) (KTf K d.D d.N) Q *
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.sub0 x F) *
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) Pm := by ring
    _ = _ := hφ
    _ = _ := by ring

end Data

end ReciprocityTheory.ChartRestriction.G.T0
