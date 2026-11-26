module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FsumEqSum
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HHINDC

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FiniteHeightFractionRepr
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.SphereMeanSubArchimedean
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.LogHeightDivMultihomogeneous
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.Closed MeasureTheory IsDedekindDomain
  ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity

section
variable {K : Type} [Field K] [NumberField K]

theorem uniformizer_abs_eq_inv_norm (la : HeightOneSpectrum (𝓞 K)) :
    FinitePlace.mk la ((Data.unif la : 𝓞 K) : K) = ((Ideal.absNorm la.asIdeal : ℕ) : ℝ)⁻¹ := by
  obtain ⟨h1, h2⟩ := unif_mem la
  have a1 : la.intValuation (Data.unif la) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) :=
    (la.intValuation_le_pow_iff_mem _ 1).2 (by rw [pow_one]; exact h1)
  have a2 : ¬ la.intValuation (Data.unif la) ≤ WithZero.exp (-((2 : ℕ) : ℤ)) :=
    fun h => h2 ((la.intValuation_le_pow_iff_mem _ 2).1 h)
  have hne : la.intValuation (Data.unif la) ≠ 0 := by
    intro h0; apply a2; rw [h0]; exact zero_le
  have hv : la.intValuation (Data.unif la) = WithZero.exp (-1 : ℤ) := by
    rw [← WithZero.exp_log hne] at a1 a2 ⊢
    rw [WithZero.exp_le_exp] at a1 a2
    congr 1
    push_cast at a1 a2
    omega
  rw [FinitePlace.mk_apply]
  have := FinitePlace.norm_embedding_int (K := K) (v := la) (Data.unif la)
  simp only [RingOfIntegers.coe_eq_algebraMap] at this ⊢
  rw [this, hv]
  rw [WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero, WithZero.log_exp]
  simp

theorem logHeight_div_multihomogeneous {B n : ℕ} {P Q R : MvPolynomial (Fin B × Fin n) K}
    (eQ eR : Fin B → ℕ) (hP : P ≠ 0) (hQ : Q ≠ 0) (hQm : IsMultiHomogeneous eQ Q)
    (hRm : IsMultiHomogeneous eR R) (hPQ : P * Q = R) :
    h0 P = h0 R - h0 Q := by
  have hR : R ≠ 0 := hPQ ▸ mul_ne_zero hP hQ
  have hfin : ∑ᶠ w : FinitePlace K, Real.log (gaussAbs w P) =
      (∑ᶠ w : FinitePlace K, Real.log (gaussAbs w R)) - ∑ᶠ w : FinitePlace K, Real.log (gaussAbs w Q) := by
    rw [← finsum_sub_distrib (gauss_abs_log_support_finite R hR) (gauss_abs_log_support_finite Q hQ)]
    refine finsum_congr fun w => ?_
    rw [← hPQ, gauss_abs_mul w P Q hP hQ,
      Real.log_mul (gauss_abs_pos_of_ne_zero w P hP).ne' (gauss_abs_pos_of_ne_zero w Q hQ).ne']
    ring
  have harch : ∀ σ : K →+* ℂ, blockSphereMean B n (MvPolynomial.map σ P) =
      blockSphereMean B n (MvPolynomial.map σ R) - blockSphereMean B n (MvPolynomial.map σ Q) := by
    intro σ
    have hs : ∀ F : MvPolynomial (Fin B × Fin n) K, F ≠ 0 → MvPolynomial.map σ F ≠ 0 := by
      intro F hF h'
      exact hF (MvPolynomial.map_injective σ σ.injective (by rw [h', map_zero]))
    have IR := sphereLogIntegrable B n eR _ (hs R hR) (isMultiHomogeneous_map_ring eR R hRm σ)
    have IQ := sphereLogIntegrable B n eQ _ (hs Q hQ) (isMultiHomogeneous_map_ring eQ Q hQm σ)
    have aR := ae_blockSphere_eval_ne_zero B n eR _ (hs R hR) (isMultiHomogeneous_map_ring eR R hRm σ)
    have aQ := ae_blockSphere_eval_ne_zero B n eQ _ (hs Q hQ) (isMultiHomogeneous_map_ring eQ Q hQm σ)
    unfold blockSphereMean
    rw [← integral_sub IR IQ]
    refine integral_congr_ae ?_
    filter_upwards [aR, aQ] with z hzR hzQ
    have hRe : MvPolynomial.eval (blockPoint z) (MvPolynomial.map σ R) =
        MvPolynomial.eval (blockPoint z) (MvPolynomial.map σ P) *
          MvPolynomial.eval (blockPoint z) (MvPolynomial.map σ Q) := by
      rw [← hPQ, map_mul, map_mul]
    have hzP : MvPolynomial.eval (blockPoint z) (MvPolynomial.map σ P) ≠ 0 := by
      intro h0; apply hzR; rw [hRe, h0, zero_mul]
    rw [hRe, norm_mul, Real.log_mul (norm_ne_zero_iff.2 hzP) (norm_ne_zero_iff.2 hzQ)]
    ring
  unfold h0
  rw [hfin, Finset.sum_congr rfl fun σ _ => harch σ, Finset.sum_sub_distrib]
  ring

end

end ReciprocityTheory.ChartRestriction.G.T0

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.Closed MeasureTheory IsDedekindDomain
  ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]

namespace Data

variable (d : Data K ι Ω WT A)

theorem log_gaussAbs_sub_of_fraction (la : HeightOneSpectrum (𝓞 K)) (a b : KTp K d.D d.N) (ha : a ≠ 0) (hb : b ≠ 0)
    (q : KTf K d.D d.N)
    (hq : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a = q * algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b) :
    Real.log (gaussAbs (FinitePlace.mk la) a) - Real.log (gaussAbs (FinitePlace.mk la) b) =
      -((d.gOrd la q : ℝ) * logNorm la) := by
  classical
  let _ := algOpKT (K := K) d.D d.N la
  have : IsFractionRing (Op d.D d.N la) (KTf K d.D d.N) := by
    let _ := algOTKT (K := K) d.D d.N
    let _ : Algebra (OT K d.D d.N) (KTp K d.D d.N) := MvPolynomial.algebraMvPolynomial
    have := IsScalarTower.of_algebraMap_eq' (R := OT K d.D d.N) (S := KTp K d.D d.N)
      (A := KTf K d.D d.N) rfl
    have := IsScalarTower.of_algebraMap_eq (R := OT K d.D d.N) (S := Op d.D d.N la)
      (A := KTf K d.D d.N) fun x => by
        change _ = OpToKT d.D d.N la (algebraMap _ _ x)
        rw [OpToKT, IsLocalization.lift_eq]
        rfl
    have := MvPolynomial.isLocalization (σ := TVar d.D d.N) (nonZeroDivisors (𝓞 K)) K
    have hinj : Function.Injective (algebraMap (OT K d.D d.N) (KTp K d.D d.N)) :=
      MvPolynomial.map_injective _ (IsFractionRing.injective (𝓞 K) K)
    have hmonoid : (nonZeroDivisors (KTp K d.D d.N)).comap
        (algebraMap (OT K d.D d.N) (KTp K d.D d.N)) = nonZeroDivisors (OT K d.D d.N) := by
      ext p
      simp only [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero]
      exact map_ne_zero_iff _ hinj
    have : IsFractionRing (OT K d.D d.N) (KTf K d.D d.N) := by
      rw [IsFractionRing, ← hmonoid]
      exact IsLocalization.localization_localization_isLocalization_of_has_all_units
        ((nonZeroDivisors (𝓞 K)).map (C (σ := TVar d.D d.N)))
        (nonZeroDivisors (KTp K d.D d.N)) (KTf K d.D d.N)
        (fun _ hu => hu.mem_nonZeroDivisors)
    exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (laT d.D d.N la).primeCompl
      (Op d.D d.N la) (KTf K d.D d.N)
  have := Op_isDVR (K := K) d.D d.N la
  have hinj := IsFractionRing.injective (KTp K d.D d.N) (KTf K d.D d.N)
  have hq0 : q ≠ 0 := by
    rintro rfl; rw [zero_mul] at hq; exact ha (hinj (by rw [hq, map_zero]))
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := Op d.D d.N la) q
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hx0 : x ≠ 0 := by rintro rfl; simp at hq0
  obtain ⟨n1, u1, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0
    (unifOp_irreducible d.D d.N la)
  obtain ⟨n2, u2, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy0
    (unifOp_irreducible d.D d.N la)
  set π := algebraMap K (KTf K d.D d.N) ((Data.unif la : 𝓞 K) : K) with hπdef
  have hπ : OpToKT d.D d.N la (unifOp d.D d.N la) = π := (algK_unif d.D d.N la).symm
  have hπ0 : π ≠ 0 := by
    rw [← hπ]
    exact (map_ne_zero_iff _ (OpToKT_injective d.D d.N la)).mpr (unifOp_irreducible d.D d.N la).ne_zero
  have hE : ∀ z : Op d.D d.N la, algebraMap (Op d.D d.N la) (KTf K d.D d.N) z = OpToKT d.D d.N la z :=
    fun _ => rfl
  have hU : ∀ u : (Op d.D d.N la)ˣ, OpToKT d.D d.N la (u : Op d.D d.N la) ≠ 0 := fun u =>
    (map_ne_zero_iff _ (OpToKT_injective d.D d.N la)).mpr u.ne_zero

  have hg : d.gOrd la (algebraMap (Op d.D d.N la) (KTf K d.D d.N) (↑u1 * unifOp d.D d.N la ^ n1) /
      algebraMap (Op d.D d.N la) (KTf K d.D d.N) (↑u2 * unifOp d.D d.N la ^ n2)) = (n1 : ℤ) - n2 := by
    refine d.gOrd_eq la (u := ((u1 * u2⁻¹ : (Op d.D d.N la)ˣ) : Op d.D d.N la)) (Units.isUnit _) ?_
    rw [hE, hE, map_mul, map_mul, map_pow, map_pow, hπ, Units.val_mul, map_mul,
      map_units_inv (OpToKT d.D d.N la) u2, zpow_sub₀ hπ0, zpow_natCast, zpow_natCast]
    have := hU u2
    field_simp
  rw [hg]

  obtain ⟨⟨x1, s1⟩, hu1⟩ := IsLocalization.mk'_surjective (laT d.D d.N la).primeCompl (u1 : Op d.D d.N la)
  obtain ⟨⟨x2, s2⟩, hu2⟩ := IsLocalization.mk'_surjective (laT d.D d.N la).primeCompl (u2 : Op d.D d.N la)
  dsimp only at hu1 hu2
  have hx1 : x1 ∈ (laT d.D d.N la).primeCompl :=
    (IsLocalization.AtPrime.isUnit_mk'_iff (Op d.D d.N la) (laT d.D d.N la) x1 s1).1 (hu1 ▸ u1.isUnit)
  have hx2 : x2 ∈ (laT d.D d.N la).primeCompl :=
    (IsLocalization.AtPrime.isUnit_mk'_iff (Op d.D d.N la) (laT d.D d.N la) x2 s2).1 (hu2 ▸ u2.isUnit)
  set g := (algebraMap (KTp K d.D d.N) (KTf K d.D d.N)).comp (OTtoKT K d.D d.N) with hgdef
  have hs1 : g x1 = g s1 * OpToKT d.D d.N la (u1 : Op d.D d.N la) := by
    rw [← hu1]; exact (IsLocalization.lift_mk'_spec _ _ _ _).1 rfl
  have hs2 : g x2 = g s2 * OpToKT d.D d.N la (u2 : Op d.D d.N la) := by
    rw [← hu2]; exact (IsLocalization.lift_mk'_spec _ _ _ _).1 rfl
  have hX : x2 * (s1 : OT K d.D d.N) ∈ (laT d.D d.N la).primeCompl :=
    (laT d.D d.N la).primeCompl.mul_mem hx2 s1.2
  have hY : x1 * (s2 : OT K d.D d.N) ∈ (laT d.D d.N la).primeCompl :=
    (laT d.D d.N la).primeCompl.mul_mem hx1 s2.2
  have hπC : π = algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (C ((Data.unif la : 𝓞 K) : K)) := by
    rw [hπdef, IsScalarTower.algebraMap_apply K (KTp K d.D d.N) (KTf K d.D d.N), MvPolynomial.algebraMap_eq]

  have hpoly : a * OTtoKT K d.D d.N (x2 * (s1 : OT K d.D d.N)) * C (((Data.unif la : 𝓞 K) : K) ^ n2) =
      C (((Data.unif la : 𝓞 K) : K) ^ n1) * OTtoKT K d.D d.N (x1 * (s2 : OT K d.D d.N)) * b := by
    apply hinj
    have hs1' : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (OTtoKT K d.D d.N x1) =
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (OTtoKT K d.D d.N (s1 : OT K d.D d.N)) *
          OpToKT d.D d.N la (u1 : Op d.D d.N la) := hs1
    have hs2' : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (OTtoKT K d.D d.N x2) =
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (OTtoKT K d.D d.N (s2 : OT K d.D d.N)) *
          OpToKT d.D d.N la (u2 : Op d.D d.N la) := hs2
    have e3 : ∀ m : ℕ, algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (C (((Data.unif la : 𝓞 K) : K) ^ m)) = π ^ m := by
      intro m; rw [hπC, MvPolynomial.C_pow, map_pow]
    simp only [map_mul, e3]
    rw [hq, hs1', hs2']
    simp only [hE, map_mul, map_pow, hπ]
    have := hU u2
    have := hπ0
    field_simp

  set w := FinitePlace.mk la
  have hXn : gaussAbs w (OTtoKT K d.D d.N (x2 * (s1 : OT K d.D d.N))) = 1 := gaussAbs_prim la _ hX
  have hYn : gaussAbs w (OTtoKT K d.D d.N (x1 * (s2 : OT K d.D d.N))) = 1 := gaussAbs_prim la _ hY
  have hX0 : OTtoKT K d.D d.N (x2 * (s1 : OT K d.D d.N)) ≠ 0 := by intro h0; rw [h0] at hXn; simp [gaussAbs] at hXn
  have hY0 : OTtoKT K d.D d.N (x1 * (s2 : OT K d.D d.N)) ≠ 0 := by intro h0; rw [h0] at hYn; simp [gaussAbs] at hYn
  have hN : (0 : ℝ) < ((Ideal.absNorm la.asIdeal : ℕ) : ℝ) := by
    have := NumberField.HeightOneSpectrum.one_lt_absNorm la
    exact_mod_cast (zero_lt_one.trans this)
  have hϖ0 : ((Data.unif la : 𝓞 K) : K) ≠ 0 := by
    intro h0; have := uniformizer_abs_eq_inv_norm la; rw [h0, map_zero] at this; exact (inv_pos.2 hN).ne' this.symm
  have hC0 : ∀ m : ℕ, (C (((Data.unif la : 𝓞 K) : K) ^ m) : KTp K d.D d.N) ≠ 0 := fun m => by
    rw [Ne, C_eq_zero]; exact pow_ne_zero _ hϖ0
  have key := congrArg (gaussAbs w) hpoly
  rw [gauss_abs_mul w _ _ (mul_ne_zero ha hX0) (hC0 n2), gauss_abs_mul w _ _ ha hX0,
    gauss_abs_mul w _ _ (mul_ne_zero (hC0 n1) hY0) hb, gauss_abs_mul w _ _ (hC0 n1) hY0,
    gaussAbs_C, gaussAbs_C, map_pow, map_pow, uniformizer_abs_eq_inv_norm la, hXn, hYn, mul_one, mul_one] at key
  have hA' := gauss_abs_pos_of_ne_zero w a ha
  have hB' := gauss_abs_pos_of_ne_zero w b hb
  have hlogN : logNorm la = Real.log ((Ideal.absNorm la.asIdeal : ℕ) : ℝ) := rfl
  have hl := congrArg Real.log key
  rw [Real.log_mul hA'.ne' (pow_ne_zero _ (inv_pos.2 hN).ne'),
    Real.log_mul (pow_ne_zero _ (inv_pos.2 hN).ne') hB'.ne', Real.log_pow, Real.log_pow, Real.log_inv] at hl
  rw [hlogN]
  push_cast
  linarith

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.Closed MeasureTheory IsDedekindDomain
  ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem eval_indep_of_first_block (q : KTp K d.D d.N) (m : Fin (d.D + 1) → ℕ) (hm0 : m 0 = 0)
    (hq : IsMultiHomogeneous m q) (sg : K →+* ℂ) (t0 : Fin (d.N + 1) → ℂ)
    (t : Fin d.D → Fin (d.N + 1) → ℂ) : d.evT sg t0 t q = d.evT sg 0 t q := by
  unfold evT
  rw [MvPolynomial.eval₂_eq', MvPolynomial.eval₂_eq']
  apply Finset.sum_congr rfl
  intro s hs
  congr 1
  apply Finset.prod_congr rfl
  rintro ⟨b, j⟩ _
  have hsum : ∑ j : Fin (d.N + 1), s (0, j) = 0 := by
    rw [hq s hs 0, hm0]
  cases b using Fin.cases with
  | zero =>
    have h0 : s (0, j) = 0 := (Finset.sum_eq_zero_iff.mp hsum) j (Finset.mem_univ _)
    simp [h0]
  | succ i => rfl

theorem sphereMean_sub_archimedean (a b : KTp K d.D d.N) (m : Fin (d.D + 1) → ℕ) (hm0 : m 0 = 0)
    (ha : a ≠ 0) (hb : b ≠ 0) (hma : IsMultiHomogeneous m a) (hmb : IsMultiHomogeneous m b)
    (sg : K →+* ℂ) :
    blockSphereMean (d.D + 1) (d.N + 1) (MvPolynomial.map sg a) -
      blockSphereMean (d.D + 1) (d.N + 1) (MvPolynomial.map sg b) = d.mSgP sg a b := by
  have hn : 0 < d.N + 1 := Nat.succ_pos _
  have hmp := hint_mpTail d.D (d.N + 1) hn
  have key : ∀ q : KTp K d.D d.N, q ≠ 0 → IsMultiHomogeneous m q →
      blockSphereMean (d.D + 1) (d.N + 1) (MvPolynomial.map sg q) =
        ∫ w, Real.log ‖d.evT sg 0 (d.tOf w) q‖ ∂(ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)) ∧
      Integrable (fun w => Real.log ‖d.evT sg 0 (d.tOf w) q‖)
        (ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)) := by
    intro q hq0 hq
    have hq0' : MvPolynomial.map sg q ≠ 0 := fun h =>
      hq0 (MvPolynomial.map_injective _ sg.injective (by rw [h, map_zero]))
    have hq' : IsMultiHomogeneous m (MvPolynomial.map sg q) :=
      fun s hs => hq s (MvPolynomial.support_map_subset _ _ hs)
    have hI := hint_logInt_tail hn hq0' hq' hm0 0
    have heq : ∀ w, d.evT sg 0 (d.tOf w) q =
        MvPolynomial.eval (hintPt 0 w) (MvPolynomial.map sg q) := by
      intro w
      rw [MvPolynomial.eval_map]
      rfl
    have hI' : Integrable (fun w => Real.log ‖d.evT sg 0 (d.tOf w) q‖)
        (ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)) := by
      simp only [heq]
      exact hI
    refine ⟨?_, hI'⟩
    have hpt : ∀ z : ReciprocityTheory.MultiplicativeHeights.BlockSphere (d.D + 1) (d.N + 1),
        Real.log ‖MvPolynomial.eval (ReciprocityTheory.MultiplicativeHeights.blockPoint z) (MvPolynomial.map sg q)‖ =
          Real.log ‖d.evT sg 0 (d.tOf (fun i : Fin d.D => z i.succ)) q‖ := by
      intro z
      have h1 : MvPolynomial.eval (ReciprocityTheory.MultiplicativeHeights.blockPoint z) (MvPolynomial.map sg q) =
          d.evT sg (fun j => ReciprocityTheory.MultiplicativeHeights.spherePoint (z 0) j)
            (d.tOf (fun i : Fin d.D => z i.succ)) q := by
        rw [MvPolynomial.eval_map]
        unfold evT
        congr 1
        funext v
        rcases v with ⟨b, j⟩
        cases b using Fin.cases with
        | zero => rfl
        | succ i => rfl
      rw [h1, d.eval_indep_of_first_block q m hm0 hq sg]
    unfold ReciprocityTheory.MultiplicativeHeights.blockSphereMean
    simp only [hpt]
    have h2 := MeasureTheory.integral_map (μ := ReciprocityTheory.MultiplicativeHeights.blockSphereProb (d.D + 1) (d.N + 1))
      hmp.measurable.aemeasurable (f := fun w => Real.log ‖d.evT sg 0 (d.tOf w) q‖)
      (by rw [hmp.map_eq]; exact hI'.aestronglyMeasurable)
    rw [hmp.map_eq] at h2
    exact h2.symm
  obtain ⟨ha1, ha2⟩ := key a ha hma
  obtain ⟨hb1, hb2⟩ := key b hb hmb
  rw [ha1, hb1, ← integral_sub ha2 hb2]
  rfl

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.Closed MeasureTheory IsDedekindDomain
  ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem gen_ne_zero_of_mem_htOne {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne) : d.gen p ≠ 0 := by
  obtain ⟨hpr, hh⟩ := hp
  haveI := hpr
  obtain ⟨g, hg, hpg⟩ := ValUFD.heightOne_principal p hh
  have hPr : p.IsPrincipal := ⟨⟨g, hpg⟩⟩
  unfold gen
  rw [dite_eq_left hPr]
  intro h0
  have hbot : p = ⊥ := (Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero p).2 h0
  rw [hbot] at hpg
  exact hg.ne_zero (Ideal.span_singleton_eq_bot.1 hpg.symm)

theorem finite_height_fraction_repr (hd : d.AxH 𝒜) (h : d.S1) :
    ∃ U V : KTp K d.D d.N, U ≠ 0 ∧ V ≠ 0 ∧ (∃ eU, IsMultiHomogeneous eU U) ∧
      (∃ eV, IsMultiHomogeneous eV V) ∧
      d.fDivE hd h * algebraMap (KTp K d.D d.N) (KTf K d.D d.N) V =
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) U ∧
      d.h0f h d.wF hd.a4.choose = h0 U - h0 V := by
  classical
  have hspec : ∀ c, hd.a4.choose c ∈ 𝒜 c d.wF ∧ hd.a4.choose c ≠ 0 := hd.a4.choose_spec.1
  have hfin : ∀ c, {p | p ∈ d.HtOne ∧ d.nP h c d.wF (hd.a4.choose c) p ≠ 0}.Finite := fun c =>
    (d.good_primes_properties hd h c).2.2.1 d.wF (hd.a4.choose c) (hspec c).1 (hspec c).2
  obtain ⟨T, hmemT⟩ : ∃ T : ι → Finset (Ideal (KTp K d.D d.N)),
      ∀ c p, p ∈ T c ↔ p ∈ d.HtOne ∧ d.nP h c d.wF (hd.a4.choose c) p ≠ 0 :=
    ⟨fun c => (hfin c).toFinset, fun c p => by simp⟩
  have hmemS : ∀ x ∈ Finset.univ.sigma T,
      x.2 ∈ d.HtOne ∧ d.nP h x.1 d.wF (hd.a4.choose x.1) x.2 ≠ 0 := by
    intro x hx
    rw [Finset.mem_sigma] at hx
    exact (hmemT _ _).1 hx.2
  have hne : ∀ x ∈ Finset.univ.sigma T, d.gen x.2 ≠ 0 := fun x hx => d.gen_ne_zero_of_mem_htOne (hmemS x hx).1
  have hmh : ∀ x ∈ Finset.univ.sigma T,
      IsMultiHomogeneous (fun b : Fin (d.D + 1) => if b = 0 then 0 else d.dg (d.gen x.2)) (d.gen x.2) := by
    intro x hx
    obtain ⟨hp, hn⟩ := hmemS x hx
    refine (d.good_primes_properties hd h x.1).2.1 x.2 hp ?_
    by_contra hw
    push_neg at hw
    apply hn
    simp [nP, hw]
  have halg : ∀ x ∈ Finset.univ.sigma T,
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen x.2) ≠ 0 := fun x hx =>
    (map_ne_zero_iff _ (IsFractionRing.injective (KTp K d.D d.N) (KTf K d.D d.N))).2 (hne x hx)
  have key : ∀ (a : KTf K d.D d.N), a ≠ 0 → ∀ m : ℤ, a ^ m * a ^ (-m).toNat = a ^ m.toNat := by
    intro a ha m
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ ha]
    congr 1
    omega
  refine ⟨∏ x ∈ Finset.univ.sigma T, d.gen x.2 ^ (d.nP h x.1 d.wF (hd.a4.choose x.1) x.2).toNat,
    ∏ x ∈ Finset.univ.sigma T, d.gen x.2 ^ (-d.nP h x.1 d.wF (hd.a4.choose x.1) x.2).toNat,
    Finset.prod_ne_zero_iff.2 fun x hx => pow_ne_zero _ (hne x hx),
    Finset.prod_ne_zero_iff.2 fun x hx => pow_ne_zero _ (hne x hx),
    ⟨_, HeightMultiplicativity.multi_prod _ _ _ fun x hx => HeightMultiplicativity.multi_pow (hmh x hx) _⟩,
    ⟨_, HeightMultiplicativity.multi_prod _ _ _ fun x hx => HeightMultiplicativity.multi_pow (hmh x hx) _⟩, ?_, ?_⟩
  · have hfac : ∀ c, (∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ d.nP h c d.wF (hd.a4.choose c) p) =
        ∏ p ∈ T c, algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^
          d.nP h c d.wF (hd.a4.choose c) p := by
      intro c
      apply finprod_mem_eq_prod_of_subset
      · rintro p ⟨hp, hp1⟩
        rw [Function.mem_mulSupport] at hp1
        rw [Finset.mem_coe, hmemT]
        exact ⟨hp, fun h0' => hp1 (by rw [h0', zpow_zero])⟩
      · intro p hp
        exact ((hmemT c p).1 hp).1
    have hf : d.fDivE hd h = ∏ x ∈ Finset.univ.sigma T,
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen x.2) ^ d.nP h x.1 d.wF (hd.a4.choose x.1) x.2 := by
      rw [Finset.prod_sigma]
      unfold fDivE
      exact Finset.prod_congr rfl fun c _ => hfac c
    rw [hf, map_prod, map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun x hx => ?_
    rw [map_pow, map_pow]
    exact key _ (halg x hx) _
  · have hsum : ∀ c, (∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
        (d.nP h c d.wF (hd.a4.choose c) p : ℝ) * h0 (d.gen p)) =
        ∑ p ∈ T c, (d.nP h c d.wF (hd.a4.choose c) p : ℝ) * h0 (d.gen p) := by
      intro c
      apply finsum_mem_eq_sum_of_subset
      · rintro p ⟨hp, hp1⟩
        rw [Function.mem_support] at hp1
        rw [Finset.mem_coe, hmemT]
        exact ⟨hp, fun h0' => hp1 (by rw [h0', Int.cast_zero, zero_mul])⟩
      · intro p hp
        exact ((hmemT c p).1 hp).1
    have hn0 : 0 < d.N + 1 := Nat.succ_pos _
    have hU : h0 (∏ x ∈ Finset.univ.sigma T,
        d.gen x.2 ^ (d.nP h x.1 d.wF (hd.a4.choose x.1) x.2).toNat) =
        ∑ x ∈ Finset.univ.sigma T,
          ((d.nP h x.1 d.wF (hd.a4.choose x.1) x.2).toNat : ℝ) * h0 (d.gen x.2) :=
      HeightMultiplicativity.logHeight_prod_pow (B := d.D + 1) (n := d.N + 1) hn0 (Finset.univ.sigma T)
        (fun x b => if b = 0 then 0 else d.dg (d.gen x.2)) (fun x => d.gen x.2) _ hne hmh
    have hV : h0 (∏ x ∈ Finset.univ.sigma T,
        d.gen x.2 ^ (-d.nP h x.1 d.wF (hd.a4.choose x.1) x.2).toNat) =
        ∑ x ∈ Finset.univ.sigma T,
          ((-d.nP h x.1 d.wF (hd.a4.choose x.1) x.2).toNat : ℝ) * h0 (d.gen x.2) :=
      HeightMultiplicativity.logHeight_prod_pow (B := d.D + 1) (n := d.N + 1) hn0 (Finset.univ.sigma T)
        (fun x b => if b = 0 then 0 else d.dg (d.gen x.2)) (fun x => d.gen x.2) _ hne hmh
    rw [hU, hV, ← Finset.sum_sub_distrib, Finset.sum_sigma]
    unfold h0f
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hsum c]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← sub_mul]
    congr 1
    exact_mod_cast (Int.toNat_sub_toNat_neg _).symm

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem disc_product (hd : d.AxH 𝒜) (h : d.S1) (hI2be : d.HeightIntegralBoundEstimate) (a b : KTp K d.D d.N)
    (hab : d.IsPres hd h a b) (Om : KTp K d.D d.N)
    (hOm : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) Om = d.omE hd h) :
    (Function.support fun la => d.gOrd la (d.De hd h)).Finite ∧
    (Function.support fun la => d.NlaG h d.wF hd.a4.choose la).Finite ∧
    (∑ᶠ la, ((d.gOrd la (d.De hd h) : ℝ) + 2 * d.NlaG h d.wF hd.a4.choose la) * logNorm la) /
        (Module.finrank ℚ K : ℝ) =
      meanK (fun sg => d.mSgP sg a b - 2 * d.Nsg d.wF hd.a4.choose sg) -
        ReciprocityTheory.MultiplicativeHeights.h0 Om + 2 * d.Hgt h d.wF hd.a4.choose := by
  classical
  set e := hd.a4.choose with hedef
  have he := hd.a4.choose_spec.1
  obtain ⟨hb0, hab', m, hm0, hma, hmb⟩ := hab
  have hDe : d.De hd h ≠ 0 := (d.disc_lattice hd h).1
  have hinj := IsFractionRing.injective (KTp K d.D d.N) (KTf K d.D d.N)
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at hab'
    exact mul_ne_zero hDe ((map_ne_zero_iff _ hinj).2 hb0) hab'.symm
  have hn : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have hcard : (Fintype.card (K →+* ℂ) : ℝ) = Module.finrank ℚ K := by
    exact_mod_cast NumberField.Embeddings.card K ℂ

  have hla : ∀ la, Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs (FinitePlace.mk la) a) -
      Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs (FinitePlace.mk la) b) =
        -((d.gOrd la (d.De hd h) : ℝ) * logNorm la) :=
    fun la => d.log_gaussAbs_sub_of_fraction la a b ha0 hb0 _ hab'
  have hlog : ∀ la : IsDedekindDomain.HeightOneSpectrum (𝓞 K), logNorm la ≠ 0 := fun la => by
    have h1 := NumberField.HeightOneSpectrum.one_lt_absNorm la
    exact (Real.log_pos (by exact_mod_cast h1)).ne'
  have hgfin : (Function.support fun la => d.gOrd la (d.De hd h)).Finite := by
    refine (((ReciprocityTheory.MultiplicativeHeights.gauss_abs_log_support_finite a ha0).union
      (ReciprocityTheory.MultiplicativeHeights.gauss_abs_log_support_finite b hb0)).preimage
      (FinitePlace.equivHeightOneSpectrum (K := K)).symm.injective.injOn).subset ?_
    intro la hla0
    have h1 : Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs (FinitePlace.mk la) a) -
        Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs (FinitePlace.mk la) b) ≠ 0 := by
      rw [hla]
      exact neg_ne_zero.2 (mul_ne_zero (by exact_mod_cast hla0) (hlog la))
    by_contra hn'
    apply h1
    simp only [Set.mem_preimage, Set.mem_union, Function.mem_support, not_or, not_not] at hn'
    change Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs (FinitePlace.mk la) a) = 0 ∧
      Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs (FinitePlace.mk la) b) = 0 at hn'
    rw [hn'.1, hn'.2, sub_zero]
  have hNfin : (Function.support fun la => d.NlaG h d.wF e la).Finite :=
    (Set.finite_iUnion fun c => d.la_fin hd h c (fun v => d.ord c v d.wF (e c))
      (hd.a3' c (he c).1 (he c).2)).subset (d.aNla_supp hd h (fun c v f => d.ord c v d.wF f) e)
  refine ⟨hgfin, hNfin, ?_⟩

  obtain ⟨U, V, hU0, hV0, ⟨eU, hUm⟩, ⟨eV, hVm⟩, hpres, hh0f⟩ := d.finite_height_fraction_repr hd h
  have hpoly : Om * (b * V ^ 2) = a * U ^ 2 := by
    apply hinj
    simp only [map_mul, map_pow]
    rw [hOm, omE, hab', ← hpres]
    ring
  have hOm0 : Om ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hpoly
    exact mul_ne_zero ha0 (pow_ne_zero _ hU0) hpoly.symm
  have hnp : 0 < d.N + 1 := Nat.succ_pos _
  have E1 : ReciprocityTheory.MultiplicativeHeights.h0 Om = ReciprocityTheory.MultiplicativeHeights.h0 a + 2 * ReciprocityTheory.MultiplicativeHeights.h0 U -
      (ReciprocityTheory.MultiplicativeHeights.h0 b + 2 * ReciprocityTheory.MultiplicativeHeights.h0 V) := by
    rw [logHeight_div_multihomogeneous _ _ hOm0 (mul_ne_zero hb0 (pow_ne_zero _ hV0))
      (multi_mul hmb (multi_pow hVm 2)) (multi_mul hma (multi_pow hUm 2)) hpoly,
      (ReciprocityTheory.MultiplicativeHeights.Closed.gauss_height_additivity K (d.D + 1) (d.N + 1) _ _ a (U ^ 2) hnp ha0 (pow_ne_zero _ hU0) hma
        (multi_pow hUm 2)).1,
      (ReciprocityTheory.MultiplicativeHeights.Closed.gauss_height_additivity K (d.D + 1) (d.N + 1) _ _ b (V ^ 2) hnp hb0 (pow_ne_zero _ hV0) hmb
        (multi_pow hVm 2)).1,
      h0_pow_of_isMultiHomogeneous hnp hU0 hUm, h0_pow_of_isMultiHomogeneous hnp hV0 hVm]
    push_cast; ring
  have E2 : ReciprocityTheory.MultiplicativeHeights.h0 a - ReciprocityTheory.MultiplicativeHeights.h0 b =
      (-(∑ᶠ la, (d.gOrd la (d.De hd h) : ℝ) * logNorm la) + ∑ sg, d.mSgP sg a b) /
        (Module.finrank ℚ K : ℝ) := by
    have hfinp : (∑ᶠ w : FinitePlace K, Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs w a)) -
        ∑ᶠ w : FinitePlace K, Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs w b) =
        -(∑ᶠ la, (d.gOrd la (d.De hd h) : ℝ) * logNorm la) := by
      rw [← finsum_sub_distrib (ReciprocityTheory.MultiplicativeHeights.gauss_abs_log_support_finite a ha0)
        (ReciprocityTheory.MultiplicativeHeights.gauss_abs_log_support_finite b hb0)]
      have := finsum_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := K)).symm
        (f := fun w => Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs w a) - Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs w b))
      rw [← this, ← finsum_neg_distrib]
      exact finsum_congr fun la => hla la
    have harch : ∑ sg : K →+* ℂ, ReciprocityTheory.MultiplicativeHeights.blockSphereMean (d.D + 1) (d.N + 1) (MvPolynomial.map sg a) -
        ∑ sg : K →+* ℂ, ReciprocityTheory.MultiplicativeHeights.blockSphereMean (d.D + 1) (d.N + 1) (MvPolynomial.map sg b) =
        ∑ sg, d.mSgP sg a b := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun sg _ => d.sphereMean_sub_archimedean a b m hm0 ha0 hb0 hma hmb sg
    unfold ReciprocityTheory.MultiplicativeHeights.h0
    rw [← hfinp, ← harch]
    ring
  have E4 : meanK (fun sg => d.mSgP sg a b - 2 * d.Nsg d.wF e sg) =
      (∑ sg, d.mSgP sg a b) / (Module.finrank ℚ K : ℝ) - 2 * meanK (d.Nsg d.wF e) := by
    unfold meanK
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hcard]
    ring
  have hsG : (Function.support fun la => (d.gOrd la (d.De hd h) : ℝ) * logNorm la).Finite :=
    hgfin.subset fun la hla0 => by
      intro h0; apply hla0; simp [h0]
  have hsN : (Function.support fun la => d.NlaG h d.wF e la * logNorm la).Finite :=
    hNfin.subset fun la hla0 => by
      intro h0; apply hla0; simp [h0]
  have E5 : (∑ᶠ la, ((d.gOrd la (d.De hd h) : ℝ) + 2 * d.NlaG h d.wF e la) * logNorm la) =
      (∑ᶠ la, (d.gOrd la (d.De hd h) : ℝ) * logNorm la) +
        2 * ∑ᶠ la, d.NlaG h d.wF e la * logNorm la := by
    rw [mul_finsum, ← finsum_add_distrib hsG (hsN.subset fun la hla0 => by
      intro h0; apply hla0; simp [h0])]
    exact finsum_congr fun la => by ring
  rw [E5, E4, Hgt, hh0f]
  have hn0 : (Module.finrank ℚ K : ℝ) ≠ 0 := hn.ne'
  linear_combination E1 + E2

end Data

end ReciprocityTheory.ChartRestriction.G.T0
