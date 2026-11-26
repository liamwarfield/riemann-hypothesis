module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoheightAddPointClosureDimEqDim
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorSimilitudeFixingPointEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteIffFiniteKer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReferenceExponentPrimeBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernTransgressionFormsFrameInvariant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesPresentationUpToOrderTensorProduct

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyMumfordClassBilinear
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyMumfordClassBilinear
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem lam_swap_of_comm {K : Type} [Field K] {A : AbVar K} (c : Pic A.X.left) {Y : Over (Sp K)} (x y : Y ⟶ A.X) :
    AbVar.lam c x y = AbVar.lam c y x := by
  rw [AbVar.lam, AbVar.lam, mul_comm x y]
  abel

noncomputable section

def lamLeftMonoidHom {K : Type} [Field K] (A : AbVar K) (c : Pic A.X.left) {Y : Over (Sp K)} (y : Y ⟶ A.X) :
    (Y ⟶ A.X) →* Multiplicative (Pic Y.left) :=
  MonoidHom.mk' (fun x => Multiplicative.ofAdd (AbVar.lam c x y)) (fun x x' => by
    rw [← ofAdd_add, lam_mul_left_of_cube])

theorem lam_bilinear : ∀ (K : Type) [Field K] (A : AbVar K) (c : Pic A.X.left) (Y : Over (Sp K)) (x y y' : Y ⟶ A.X) (n : ℤ), AbVar.lam c x (y * y') = AbVar.lam c x y + AbVar.lam c x y' ∧ AbVar.lam c 1 y = 0 ∧ AbVar.lam c x 1 = 0 ∧ AbVar.lam c (x ^ n) y = n • AbVar.lam c x y ∧ AbVar.lam c x (y ^ n) = n • AbVar.lam c x y := by
  intro K _ A c Y x y y' n
  have hL : ∀ x z : Y ⟶ A.X, ∀ m : ℤ, AbVar.lam c (x ^ m) z = m • AbVar.lam c x z := fun x z m => by
    have := map_zpow (lamLeftMonoidHom A c z) x m
    simpa [lamLeftMonoidHom] using congrArg Multiplicative.toAdd this
  have h1 : ∀ z : Y ⟶ A.X, AbVar.lam c 1 z = 0 := fun z => by
    simpa using hL 1 z 0
  refine ⟨?_, h1 y, ?_, hL x y n, ?_⟩
  · rw [lam_swap_of_comm c x, lam_swap_of_comm c x, lam_swap_of_comm c x, lam_mul_left_of_cube]
  · rw [lam_swap_of_comm]; exact h1 x
  · rw [lam_swap_of_comm, hL, lam_swap_of_comm]

end

end GlobalTheory.AV.AbVar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyMumfordClassBilinearStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianVarietyMumfordClass_bilinear : ∀ (K : Type) [Field K] (A : AbVar K) (c : Pic A.X.left) (Y : Over (Sp K)) (x y y' : Y ⟶ A.X) (n : ℤ), AbVar.lam c x (y * y') = AbVar.lam c x y + AbVar.lam c x y' ∧ AbVar.lam c 1 y = 0 ∧ AbVar.lam c x 1 = 0 ∧ AbVar.lam c (x ^ n) y = n • AbVar.lam c x y ∧ AbVar.lam c x (y ^ n) = n • AbVar.lam c x y := by
  first | (exact @GlobalTheory.AV.AbVar.lam_bilinear) | (exact GlobalTheory.AV.AbVar.lam_bilinear) | (intros; apply GlobalTheory.AV.AbVar.lam_bilinear  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatHermUnitConstant
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct

namespace GlobalTheory.LKGeo

variable {p : ℕ} [Fact p.Prime]

theorem isIntAf_zero : IsIntAf (0 : AfP p) := fun v => by rw [map_zero]; exact zero_mem _

theorem isIntAf_add {a b : AfP p} (ha : IsIntAf a) (hb : IsIntAf b) : IsIntAf (a + b) := fun v => by
  rw [map_add]; exact add_mem (ha v) (hb v)

theorem isIntAf_neg {a : AfP p} (ha : IsIntAf a) : IsIntAf (-a) := fun v => by
  rw [map_neg]; exact neg_mem (ha v)

theorem isIntAf_zsmul_mul (n : ℤ) {a b : AfP p} (ha : IsIntAf a) (hb : IsIntAf b) :
    IsIntAf ((n : ℚ) • (a * b)) := fun v => by
  rw [Int.cast_smul_eq_zsmul, map_zsmul, map_mul]
  exact zsmul_mem (mul_mem (ha v) (hb v)) n

theorem formInt_gen (D : Datum p) (a a' : AfP p) (x y : D.La) (ha : IsIntAf a) (ha' : IsIntAf a') :
    IsIntAf ((D.EF.baseChange ℚ).baseChange (AfP p) (a ⊗ₜ ((1 : ℚ) ⊗ₜ x)) (a' ⊗ₜ ((1 : ℚ) ⊗ₜ y))) := by
  rw [LinearMap.BilinForm.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul, _root_.mul_one, zsmul_eq_mul, _root_.mul_one]
  exact isIntAf_zsmul_mul _ ha ha'

theorem formInt_laHat : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (v w : AfP p ⊗[ℚ] VQ D), v ∈ LaHat D → w ∈ LaHat D →
    IsIntAf ((D.EF.baseChange ℚ).baseChange (AfP p) v w) := by
  intro p _ D v w hv hw
  set B := (D.EF.baseChange ℚ).baseChange (AfP p)

  have hgen : ∀ z ∈ {z | ∃ (a : AfP p) (x : D.La), IsIntAf a ∧ z = a ⊗ₜ ((1 : ℚ) ⊗ₜ x)},
      ∀ w ∈ LaHat D, IsIntAf (B z w) := by
    rintro z ⟨a, x, ha, rfl⟩ w hw
    induction hw using AddSubgroup.closure_induction with
    | mem w hw' =>
      obtain ⟨a', y, ha', rfl⟩ := hw'
      exact formInt_gen D a a' x y ha ha'
    | zero => rw [map_zero]; exact isIntAf_zero
    | add w₁ w₂ _ _ h₁ h₂ => rw [map_add (f := _)]; exact isIntAf_add h₁ h₂
    | neg w _ h => rw [map_neg]; exact isIntAf_neg h
  induction hv using AddSubgroup.closure_induction with
  | mem z hz => exact hgen z hz w hw
  | zero => rw [map_zero, LinearMap.zero_apply]; exact isIntAf_zero
  | add v₁ v₂ _ _ h₁ h₂ => rw [map_add (f := _), LinearMap.add_apply]; exact isIntAf_add h₁ h₂
  | neg v _ h => rw [map_neg, LinearMap.neg_apply]; exact isIntAf_neg h

end GlobalTheory.LKGeo
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuedIntCastLeIff
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace GlobalTheory.IntDvdAdele

theorem valued_intCast_le_iff (v : HeightOneSpectrum ℤ) (r : ℤ) (k : ℕ) :
    Valued.v ((r : v.adicCompletion ℚ)) ≤ WithZero.exp (-(k : ℤ)) ↔ r ∈ v.asIdeal ^ k := by
  have e : ((r : v.adicCompletion ℚ)) = algebraMap ℤ (v.adicCompletion ℚ) r := (eq_intCast _ r).symm
  rw [e, valuedAdicCompletion_eq_valuation, valuation_of_algebraMap, intValuation_le_pow_iff_mem]

def placeAt {p : ℕ} (l : ℕ) (hl : l.Prime) (hlp : l ≠ p) : AwayP p :=
  ⟨⟨Ideal.span {(l : ℤ)},
    (Ideal.span_singleton_prime (by exact_mod_cast hl.ne_zero)).2 (Nat.prime_iff_prime_int.mp hl),
    by simp [hl.ne_zero]⟩, by
    intro h
    have h' := Ideal.span_singleton_eq_span_singleton.1 h
    rw [Int.associated_iff_natAbs] at h'
    simp at h'
    exact hlp h'⟩

theorem placeAt_asIdeal {p : ℕ} (l : ℕ) (hl : l.Prime) (hlp : l ≠ p) :
    (placeAt (p := p) l hl hlp).1.asIdeal = Ideal.span {(l : ℤ)} := rfl

theorem dvd_of_eq_mul_int : ∀ (p : ℕ) [Fact p.Prime] (n : ℕ), 0 < n → n.Coprime p → ∀ (z : ℤ) (w : AfP p),
    IsIntAf w → (z : AfP p) = (n : AfP p) * w → (n : ℤ) ∣ z := by
  intro p _ n hn hcop z w hw hz
  rw [Int.natCast_dvd, Nat.dvd_iff_prime_pow_dvd_dvd]
  intro l k hl hlk
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have hl' : l.Prime := hl
  have hln : l ∣ n := (dvd_pow_self l hk.ne').trans hlk
  have hlp : l ≠ p := by
    rintro rfl
    have h1 : Nat.Coprime l l := Nat.Coprime.coprime_dvd_left hln hcop
    exact hl'.one_lt.ne' ((Nat.coprime_self l).1 h1)
  set v := placeAt (p := p) l hl' hlp
  have hzv := congrArg (AfP.eval v) hz
  rw [map_intCast, map_mul, map_natCast] at hzv
  have hwv : Valued.v (AfP.eval v w) ≤ 1 := hw v
  have hnv : Valued.v (((n : ℤ) : v.1.adicCompletion ℚ)) ≤ WithZero.exp (-(k : ℤ)) := by
    rw [valued_intCast_le_iff, placeAt_asIdeal, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact_mod_cast hlk
  have hzle : Valued.v ((z : v.1.adicCompletion ℚ)) ≤ WithZero.exp (-(k : ℤ)) := by
    rw [hzv, map_mul]
    calc Valued.v ((n : v.1.adicCompletion ℚ)) * Valued.v (AfP.eval v w)
        ≤ Valued.v ((n : v.1.adicCompletion ℚ)) * 1 := by gcongr
      _ = Valued.v (((n : ℤ) : v.1.adicCompletion ℚ)) := by rw [_root_.mul_one, Int.cast_natCast]
      _ ≤ _ := hnv
  rw [valued_intCast_le_iff, placeAt_asIdeal, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hzle
  have : ((l ^ k : ℕ) : ℤ) ∣ z := by exact_mod_cast hzle
  exact Int.natCast_dvd.1 this

end GlobalTheory.IntDvdAdele
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasIsFormPullbackHolomorphic
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasIsFormPullbackHolomorphic
set_option autoImplicit false

open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

namespace GlobalTheory.PullbackForm

variable {M M' : Type} [TopologicalSpace M] [TopologicalSpace M'] {n n' : ℕ} {A : HolAtlas M n} {A' : HolAtlas M' n'}

theorem isOpen_dom {f : M' → M} (hf : Continuous f) (j : A'.ι) (i : A.ι) :
    IsOpen ((A'.e j).target ∩ (A'.e j).symm ⁻¹' (f ⁻¹' (A.e i).source)) :=
  (A'.e j).isOpen_inter_preimage_symm ((A.e i).open_source.preimage hf)

theorem smooth_pullback {f : M' → M} {α : A.Fld} (hf : A.IsHolo A' f) (hα : A.IsForm α) (j : A'.ι)
    (S : Finset (Fin (n' + n'))) :
    ContDiffOn ℝ ∞ (fun v => (bas n').repr (A'.loc (A.pullback A' f α) j v) S) (A'.e j).target := by
  refine contDiffOn_of_locally_contDiffOn fun v hv => ?_
  obtain ⟨i, hi⟩ := A.cover (f ((A'.e j).symm v))
  have hU := isOpen_dom (A := A) (A' := A') hf.1 j i
  refine ⟨_, hU, ⟨hv, hi⟩, ?_⟩
  rw [Set.inter_eq_self_of_subset_right Set.inter_subset_left]
  have hτ := hf.2 j i
  have hτ' : ContDiffOn ℝ ∞ (A.e i ∘ f ∘ (A'.e j).symm)
      ((A'.e j).target ∩ (A'.e j).symm ⁻¹' (f ⁻¹' (A.e i).source)) :=
    (((GlobalTheory.SCV.analyticOnNhd_iff_differentiableOn hU).2 hτ).contDiffOn hU.uniqueDiffOn).restrict_scalars ℝ
  have key : ContDiffOn ℝ ∞ (fun w => ∑ T, (bas n).repr (A.loc α i ((A.e i ∘ f ∘ (A'.e j).symm) w)) T *
      (bas n').repr (pull (fderiv ℂ (A.e i ∘ f ∘ (A'.e j).symm) w) (bas n T)) S)
      ((A'.e j).target ∩ (A'.e j).symm ⁻¹' (f ⁻¹' (A.e i).source)) :=
    ContDiffOn.sum fun T _ => ((hα.smooth i T).comp hτ' fun w hw => (A.e i).map_source hw.2).mul
      (GlobalTheory.T.contDiffOn_repr_pullbackComplexForm_fderiv _ _ _ _ (bas n T) hU hτ S)
  refine key.congr fun w hw => ?_
  have h₁ : A'.loc (A.pullback A' f α) j w = pull (fderiv ℂ (A.e i ∘ f ∘ (A'.e j).symm) w)
      (A.loc α i ((A.e i ∘ f ∘ (A'.e j).symm) w)) := by
    rw [HolAtlas.loc, dite_eq_left hw.1]
    refine (GlobalTheory.T.holAtlas_pullback_eq_chart_expression M M' n n' A A' f α hf hα ⟨(j, (A'.e j).symm w), (A'.e j).map_target hw.1⟩ i hw.2).trans ?_
    refine (congrArg _ (A.loc_crd α ⟨(i, f ((A'.e j).symm w)), hw.2⟩).symm).trans ?_
    show pull (fderiv ℂ (A.e i ∘ f ∘ (A'.e j).symm) (A'.e j ((A'.e j).symm w))) _ = _
    rw [(A'.e j).right_inv hw.1]
    rfl
  rw [h₁]
  conv_lhs => rw [← (bas n).sum_repr (A.loc α i ((A.e i ∘ f ∘ (A'.e j).symm) w))]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]

theorem compat_pullback {f : M' → M} {α : A.Fld} (hf : A.IsHolo A' f) (hα : A.IsForm α) (x x' : A'.Pt)
    (h : x.pt = x'.pt) :
    A.pullback A' f α x = pull (fderiv ℂ (x'.ch ∘ x.ch.symm) x.crd) (A.pullback A' f α x') := by
  obtain ⟨⟨j, y⟩, hy⟩ := x
  obtain ⟨⟨j', y'⟩, hy'⟩ := x'
  obtain rfl : y = y' := h
  obtain ⟨i, hi⟩ := A.cover (f y)
  refine (GlobalTheory.T.holAtlas_pullback_eq_chart_expression M M' n n' A A' f α hf hα ⟨(j, y), hy⟩ i hi).trans (Eq.trans ?_
    (congrArg _ (GlobalTheory.T.holAtlas_pullback_eq_chart_expression M M' n n' A A' f α hf hα ⟨(j', y), hy'⟩ i hi).symm))
  rw [← GlobalTheory.T.pullbackComplexFormsLinearMap_comp]
  show pull (fderiv ℂ (A.e i ∘ f ∘ (A'.e j).symm) (A'.e j y)) _ =
    pull ((fderiv ℂ (A.e i ∘ f ∘ (A'.e j').symm) (A'.e j' y)).comp
      (fderiv ℂ (A'.e j' ∘ (A'.e j).symm) (A'.e j y))) _
  have e : (A'.e j).symm (A'.e j y) = y := (A'.e j).left_inv hy
  have e' : (A'.e j').symm (A'.e j' y) = y := (A'.e j').left_inv hy'
  have hW : (A'.e j).target ∩ (A'.e j).symm ⁻¹' (A'.e j').source ∈ 𝓝 (A'.e j y) :=
    ((A'.e j).isOpen_inter_preimage_symm (A'.e j').open_source).mem_nhds
      ⟨(A'.e j).map_source hy, by simpa only [Set.mem_preimage, e] using hy'⟩
  have d₁ : DifferentiableAt ℂ (A'.e j' ∘ (A'.e j).symm) (A'.e j y) := (A'.holo j j').differentiableAt hW
  have e₂ : (A'.e j' ∘ (A'.e j).symm) (A'.e j y) = A'.e j' y := congrArg _ e
  have d₂ : DifferentiableAt ℂ (A.e i ∘ f ∘ (A'.e j').symm) ((A'.e j' ∘ (A'.e j).symm) (A'.e j y)) := by
    rw [e₂]
    exact (hf.2 j' i).differentiableAt ((isOpen_dom hf.1 j' i).mem_nhds
      ⟨(A'.e j').map_source hy', by simpa only [Set.mem_preimage, e'] using hi⟩)
  have hc := fderiv_comp _ d₂ d₁
  rw [e₂] at hc
  rw [← hc]
  congr 2
  refine Filter.EventuallyEq.fderiv_eq (Filter.eventually_of_mem hW fun w hw => ?_)
  simp only [Function.comp_apply, (A'.e j').left_inv hw.2]

theorem isForm_pullback : ∀ (M M' : Type) [TopologicalSpace M] [TopologicalSpace M'] (n n' : ℕ) (A : HolAtlas M n)
    (A' : HolAtlas M' n') (f : M' → M) (α : A.Fld), A.IsHolo A' f → A.IsForm α → A'.IsForm (A.pullback A' f α) :=
  fun _ _ _ _ _ _ _ _ _ _ hf hα => ⟨smooth_pullback hf hα, compat_pullback hf hα⟩

end GlobalTheory.PullbackForm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasIsFormPullbackHolomorphicStatement
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holAtlas_isForm_pullback_holomorphic : ∀ (M M' : Type) [TopologicalSpace M] [TopologicalSpace M'] (n n' : ℕ) (A : HolAtlas M n) (A' : HolAtlas M' n')
    (f : M' → M) (α : A.Fld), A.IsHolo A' f → A.IsForm α → A'.IsForm (A.pullback A' f α) := by
  first | exact @GlobalTheory.PullbackForm.isForm_pullback | exact GlobalTheory.PullbackForm.isForm_pullback | (intros; apply GlobalTheory.PullbackForm.isForm_pullback <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeVectorBundlePullback
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LKGeo.LatDiv

variable {p : ℕ} [Fact p.Prime]

def intAf (p : ℕ) : AddSubgroup (AfP p) where
  carrier := {a | IsIntAf a}
  zero_mem' := fun v => by simp
  add_mem' := fun ha hb v => by
    rw [map_add]
    exact add_mem (ha v) (hb v)
  neg_mem' := fun ha v => by rw [map_neg]; exact neg_mem (ha v)

def extF (D : Datum p) (f : D.La →ₗ[ℤ] ℤ) : AfP p ⊗[ℚ] VQ D →ₗ[AfP p] AfP p :=
  LinearMap.liftBaseChange (AfP p)
    ((Algebra.linearMap ℚ (AfP p)) ∘ₗ LinearMap.liftBaseChange ℚ ((Algebra.linearMap ℤ ℚ) ∘ₗ f))

theorem extF_tmul (D : Datum p) (f : D.La →ₗ[ℤ] ℤ) (a : AfP p) (x : D.La) :
    extF D f (a ⊗ₜ ((1 : ℚ) ⊗ₜ x)) = a * ((f x : ℤ) : AfP p) := by
  simp [extF, LinearMap.liftBaseChange_tmul, Algebra.smul_def]

theorem extF_mem (D : Datum p) (f : D.La →ₗ[ℤ] ℤ) {w : AfP p ⊗[ℚ] VQ D} (hw : w ∈ LaHat D) :
    extF D f w ∈ intAf p := by
  induction hw using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, x, ha, rfl⟩ := hz
    intro v
    rw [extF_tmul, map_mul, map_intCast]
    exact mul_mem (ha v) (intCast_mem _ _)
  | zero => simpa using (intAf p).zero_mem
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

theorem int_dvd (D : Datum p) (f : D.La →ₗ[ℤ] ℤ) (x : D.La) (n : ℕ) (hn : 0 < n) (hnp : n.Coprime p)
    (w : AfP p ⊗[ℚ] VQ D) (hw : w ∈ LaHat D) (h : inAf D x = n • w) : (n : ℤ) ∣ f x := by
  have hb := extF_mem D f hw
  have e : ((f x : ℤ) : AfP p) = (n : AfP p) * extF D f w := by
    have := congrArg (extF D f) h
    rw [inAf, extF_tmul, _root_.one_mul, _root_.map_nsmul, nsmul_eq_mul] at this
    exact this
  set q : ℚ := (f x : ℚ) / n with hq
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hval : ∀ v : IsDedekindDomain.HeightOneSpectrum ℤ, v.valuation ℚ q ≤ 1 := by
    intro v
    by_cases hv : v.asIdeal = Ideal.span {(p : ℤ)}
    · have h1 : v.valuation ℚ (n : ℚ) = 1 := by
        have : (n : ℚ) = algebraMap ℤ ℚ (n : ℤ) := by simp
        rw [this, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
          IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff, hv, Ideal.mem_span_singleton]
        intro hd
        have : (p : ℤ) ∣ (n : ℤ) := hd
        have h2 : p ∣ n := by exact_mod_cast this
        have h3 : p ∣ Nat.gcd n p := Nat.dvd_gcd h2 dvd_rfl
        rw [hnp] at h3
        exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.1 h3)
      have h2 : v.valuation ℚ ((f x : ℤ) : ℚ) ≤ 1 := by
        rw [← eq_intCast (algebraMap ℤ ℚ), IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
        exact v.intValuation_le_one _
      rw [hq, map_div₀, h1, div_one]; exact h2
    · let v' : AwayP p := ⟨v, hv⟩
      have hbv := hb v'
      have e2 := congrArg (AfP.eval v') e
      rw [map_intCast, map_mul, map_natCast] at e2
      have hqv : algebraMap ℚ (v.adicCompletion ℚ) q = AfP.eval v' (extF D f w) := by
        have hn' : algebraMap ℚ (v.adicCompletion ℚ) (n : ℚ) ≠ 0 := (map_ne_zero _).2 hn0
        have : algebraMap ℚ (v.adicCompletion ℚ) q * algebraMap ℚ (v.adicCompletion ℚ) (n : ℚ) =
            ((f x : ℤ) : v.adicCompletion ℚ) := by
          rw [← map_mul, hq, div_mul_cancel₀ _ hn0, map_intCast]
        rw [← mul_left_inj' hn', this, e2, map_natCast]
        ring
      have hc : Valued.v (algebraMap ℚ (v.adicCompletion ℚ) q) = v.valuation ℚ q :=
        IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v q
      rw [← hc, hqv]
      exact (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 hbv
  obtain ⟨k, hk⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one ℚ q hval
  refine ⟨k, ?_⟩
  have : ((k : ℤ) : ℚ) = (f x : ℚ) / n := by rw [← eq_intCast (algebraMap ℤ ℚ)]; exact hk.trans hq
  have h4 : ((f x : ℤ) : ℚ) = ((n : ℤ) * k : ℤ) := by
    push_cast; rw [this]; field_simp
  exact_mod_cast h4

end GlobalTheory.LKGeo.LatDiv

namespace GlobalTheory.LKGeo.LatDiv

theorem eq_nsmul_of_inAf_eq_nsmul : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (x : D.La) (n : ℕ), 0 < n → n.Coprime p →
    ∀ w ∈ LaHat D, inAf D x = n • w → ∃ z, x = n • z := by
  intro p _ D x n hn hnp w hw h
  haveI := D.freeLa
  haveI := D.finLa
  let b := Module.Free.chooseBasis ℤ D.La
  have hd : ∀ i, (n : ℤ) ∣ b.coord i x := fun i => int_dvd D (b.coord i) x n hn hnp w hw h
  choose c hc using hd
  refine ⟨∑ i, c i • b i, ?_⟩
  conv_lhs => rw [← b.sum_repr x]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : b.repr x i = (n : ℤ) * c i := hc i
  rw [this, mul_smul]
  exact Nat.cast_smul_eq_nsmul ℤ n _

end GlobalTheory.LKGeo.LatDiv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlaggedBundleMetricSmoothUnitEtaleChart
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlaggedBundleMetricSmoothUnitEtaleChart
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

theorem isMetricFr_smoothUnitAt : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m k : ι → ℕ) (E : Fr (ratOf X) m k) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricFr E H → ∀ (y : CxPts X.str σ), ∀ A ∈ E.S (under y), ∀ τ, SmoothUnitAt (atlas X σ) (fun z => H A z τ) y ∧ ∀ c : AlgChart X.str σ X.dim, y ∈ c.e.source → ∀ᶠ v in 𝓝 (c.e y), MContDiffAt ∞ (fun u => H A (c.e.symm u) τ) v ∧ (H A (c.e.symm v) τ).PosDef := by
  intro F _ σ X ι _ m k E H hH y A hA τ
  set U : Set (CxPts X.str σ) := interior {z : CxPts X.str σ | A ∈ E.S (under z)} with hU
  have hyU : y ∈ U := mem_interior_iff_mem_nhds.2 (GlobalTheory.T.adaptedFrame_eventually_frame_near_complex_point F σ X ι m k E y A hA)
  have hUo : IsOpen U := isOpen_interior
  have hUS : ∀ z ∈ U, A ∈ E.S (under z) := fun z hz => interior_subset (s := {z : CxPts X.str σ | A ∈ E.S (under z)}) hz
  have key : ∀ c : AlgChart X.str σ X.dim, y ∈ c.e.source → ∀ᶠ v in 𝓝 (c.e y),
      MContDiffAt ∞ (fun u => H A (c.e.symm u) τ) v ∧ (H A (c.e.symm v) τ).PosDef := by
    intro c hc
    have ho : IsOpen (c.e.target ∩ c.e.symm ⁻¹' U) := c.e.isOpen_inter_preimage_symm hUo
    have hm : c.e y ∈ c.e.target ∩ c.e.symm ⁻¹' U :=
      ⟨c.e.map_source hc, by simpa [Set.mem_preimage, c.e.left_inv hc] using hyU⟩
    filter_upwards [ho.mem_nhds hm] with v hv
    refine ⟨fun i j => ?_, hH.posDef _ A (hUS _ hv.2) τ⟩
    have hre := contDiffOn_chart (S := U) (f := fun z => (H A z τ i j).re)
      (fun z hz => (hH.smooth z A (hUS z hz) τ i j).1) c
    have him := contDiffOn_chart (S := U) (f := fun z => (H A z τ i j).im)
      (fun z hz => (hH.smooth z A (hUS z hz) τ i j).2) c
    have h1 := (hre.contDiffAt (ho.mem_nhds hv))
    have h2 := (him.contDiffAt (ho.mem_nhds hv))
    have h3 : ContDiffAt ℝ ∞ (fun u => ((((H A (c.e.symm u) τ i j).re : ℝ) : ℂ) +
        (((H A (c.e.symm u) τ i j).im : ℝ) : ℂ) * Complex.I)) v :=
      (Complex.ofRealCLM.contDiff.contDiffAt.comp v h1).add
        ((Complex.ofRealCLM.contDiff.contDiffAt.comp v h2).mul contDiffAt_const)
    refine h3.congr_of_eventuallyEq (Eventually.of_forall fun u => ?_)
    simp [Complex.re_add_im]
  refine ⟨⟨?_, fun c hc => (key c hc).mono fun v hv => hv.1⟩, key⟩
  exact (Matrix.isUnit_iff_isUnit_det _).1 (hH.posDef y A hA τ).isUnit

end GlobalTheory.ChernCalc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlaggedBundleMetricSmoothUnitEtaleChartStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flaggedBundleMetric_smoothUnit_etaleChart : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m k : ι → ℕ) (E : Fr (ratOf X) m k) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricFr E H → ∀ (y : CxPts X.str σ), ∀ A ∈ E.S (under y), ∀ τ, SmoothUnitAt (atlas X σ) (fun z => H A z τ) y ∧ ∀ c : AlgChart X.str σ X.dim, y ∈ c.e.source → ∀ᶠ v in 𝓝 (c.e y), MContDiffAt ∞ (fun u => H A (c.e.symm u) τ) v ∧ (H A (c.e.symm v) τ).PosDef := by
  first | exact @GlobalTheory.ChernCalc.isMetricFr_smoothUnitAt | exact GlobalTheory.ChernCalc.isMetricFr_smoothUnitAt | (intros; apply GlobalTheory.ChernCalc.isMetricFr_smoothUnitAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveOfIsFiniteOfDimEqAbelianVarietyHom
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveOfIsFiniteOfDimEqAbelianVarietyHom
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem surjective_of_isFinite_of_dim_eq : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B),
    A.dim = B.dim → IsFinite f.hom.left → Surjective f.hom.left := by
  intro K _ A B f hdim hfin
  obtain ⟨hBi, -, -⟩ := GlobalTheory.T.abelianVariety_isIntegral_noetherian_compact K B
  set g := f.hom.left
  have eA : topologicalKrullDim A.X.left = Order.krullDim A.X.left :=
    Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := A.X.left))
  have eB : topologicalKrullDim B.X.left = Order.krullDim B.X.left :=
    Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := B.X.left))
  have dA := GlobalTheory.T.topologicalKrullDim_abVar_eq_dim K A
  have dB := GlobalTheory.T.topologicalKrullDim_abVar_eq_dim K B
  rw [eA] at dA
  rw [eB] at dB

  have hm : StrictMono (g : A.X.left → B.X.left) := by
    intro a b hab
    have h1 : g a ≤ g b := (show b ⤳ a from hab.1).map g.continuous
    refine lt_of_le_not_ge h1 fun h2 ↦ hab.2 ?_
    have e : g b = g a := ((show g b ⤳ g a from h1).antisymm h2).eq
    have hd := (g.isDiscrete_preimage_singleton (g a)).to_subtype
    have : (⟨b, e⟩ : g ⁻¹' {g a}) ⤳ ⟨a, rfl⟩ :=
      Topology.IsInducing.subtypeVal.specializes_iff.mp hab.1
    have hba : b = a := congrArg Subtype.val this.eq
    rw [hba]
  refine ⟨?_⟩
  by_contra hns
  have hη : genericPoint B.X.left ∉ Set.range g := by
    intro hη
    apply hns
    have hc : IsClosed (Set.range g) := g.isClosedMap.isClosed_range
    intro y
    exact (genericPoint_specializes y).mem_closed hc hη
  obtain ⟨l, hl⟩ := Order.le_krullDim_iff.1 dA.ge
  have hlast : (l.map g hm).last < genericPoint B.X.left := by
    refine lt_of_le_not_ge (genericPoint_specializes _) fun h2 ↦ hη ?_
    have e := ((genericPoint_specializes ((l.map g hm).last)).antisymm h2).eq
    rw [e, LTSeries.last_map]
    exact ⟨_, rfl⟩
  have := Order.LTSeries.length_le_krullDim ((l.map g hm).snoc _ hlast)
  rw [dB, RelSeries.snoc_length, LTSeries.map_length, hl, ← hdim] at this
  norm_cast at this
  omega

end GlobalTheory.AV.AbVar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveOfIsFiniteOfDimEqAbelianVarietyHomStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.surjective_of_isFinite_of_dim_eq_abelianVarietyHom : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), A.dim = B.dim → IsFinite f.hom.left → Surjective f.hom.left := by
  first | exact @GlobalTheory.AV.AbVar.surjective_of_isFinite_of_dim_eq | exact GlobalTheory.AV.AbVar.surjective_of_isFinite_of_dim_eq | (intros; apply GlobalTheory.AV.AbVar.surjective_of_isFinite_of_dim_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReferenceWeightOfTheta
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

namespace GlobalTheory.RefSum.ToWeight

theorem sum_padicValNat_log_le (N : ℕ) (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) :
    ∑ q ∈ S, (padicValNat q N : ℝ) * Real.log q ≤ Real.log N := by
  rw [Real.log_nat_eq_sum_factorization, Finsupp.sum]
  calc ∑ q ∈ S, (padicValNat q N : ℝ) * Real.log q = ∑ q ∈ S, (N.factorization q : ℝ) * Real.log q :=
        Finset.sum_congr rfl fun q hq => by rw [Nat.factorization_def N (hS q hq), Nat.padicValNat_def]
    _ ≤ ∑ q ∈ S ∪ N.factorization.support, (N.factorization q : ℝ) * Real.log q :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left fun q _ _ =>
          mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
    _ = _ := (Finset.sum_subset Finset.subset_union_right fun q _ hq => by
          rw [Finsupp.notMem_support_iff.1 hq]; simp).symm

theorem sum_different_le (E : Type) [Field E] [NumberField E] (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) :
    ∑ q ∈ S, (different_vp E q : ℝ) * Real.log q ≤ lrd E := by
  have hn : (0 : ℝ) < Module.finrank ℚ E := by exact_mod_cast Module.finrank_pos
  have h := sum_padicValNat_log_le (discr E).natAbs S hS
  have e1 : lrd E = Real.log ((discr E).natAbs : ℝ) / Module.finrank ℚ E := by
    unfold lrd
    rw [rootDiscr_def, Real.log_rpow (by exact_mod_cast abs_pos.2 (discr_ne_zero E)), Nat.cast_natAbs]
    field_simp
  rw [e1, le_div_iff₀ hn, Finset.sum_mul]
  refine le_of_eq_of_le (Finset.sum_congr rfl fun q _ => ?_) h
  unfold different_vp
  push_cast
  field_simp

theorem different_nonneg (E : Type) [Field E] [NumberField E] (q : ℕ) : (0 : ℝ) ≤ (different_vp E q : ℝ) := by
  unfold different_vp
  push_cast
  positivity

theorem primeSum_add (E : Type) [Field E] [NumberField E] {S B : Finset ℕ} {e : ℕ → ℝ} {s a : ℝ} (h : PrimeSum S e s)
    (hB : ∀ q ∈ B, q.Prime) (ha : 0 ≤ a) :
    PrimeSum (S ∪ B) (fun q => e q + if q ∈ B then a * (different_vp E q : ℝ) + 1 else 0) (s + (a * lrd E + logSum B)) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun q hq => (Finset.mem_union.1 hq).elim (h1 q) (hB q), fun q => add_nonneg (h2 q) ?_, fun q hq => ?_, ?_⟩
  · have := different_nonneg E q
    split_ifs
    · positivity
    · exact le_rfl
  · rw [Finset.mem_union, not_or] at hq
    simp [h3 q hq.1, hq.2]
  · simp only [add_mul, Finset.sum_add_distrib]
    refine add_le_add ?_ ?_
    · rw [← Finset.sum_subset Finset.subset_union_left fun q _ hq => by rw [h3 q hq, zero_mul]]
      exact h4
    · rw [← Finset.sum_subset Finset.subset_union_right fun q _ hq => by rw [if_neg hq, zero_mul]]
      rw [Finset.sum_congr rfl fun q hq => show (if q ∈ B then a * (different_vp E q : ℝ) + 1 else 0) * Real.log q =
        a * ((different_vp E q : ℝ) * Real.log q) + Real.log q by rw [if_pos hq]; ring,
        Finset.sum_add_distrib, ← Finset.mul_sum]
      exact add_le_add (mul_le_mul_of_nonneg_left (sum_different_le E B hB) ha) le_rfl

theorem size_le {f r l n m d σ c : ℝ} (hf : 1 ≤ f) (hr : 1 ≤ r) (hl : 1 ≤ l) (hm0 : 0 ≤ m) (hm : 2 * m ≤ n)
    (hn : n ≤ 20 * f * r ^ 2) (hd : d ≤ 3 * l) (hc : 0 ≤ c) (hσ : σ ≤ c * (f * r * l)) :
    m * (f * r) * d + σ ≤ (30 + c) * (f * r * l) ^ 12 := by
  have hz : 1 ≤ f * r * l := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hf hr) hl
  have h1 : f * r * l ≤ (f * r * l) ^ 12 := le_self_pow₀ hz (by norm_num)
  have h3 : (f * r * l) ^ 3 ≤ (f * r * l) ^ 12 := pow_le_pow_right₀ hz (by norm_num)
  have h4 : f ^ 2 * r ^ 3 * l ≤ f ^ 3 * r ^ 3 * l ^ 3 :=
    mul_le_mul (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hf (by norm_num)) (by positivity))
      (le_self_pow₀ hl (by norm_num)) (by positivity) (by positivity)
  have h5 : m * (f * r) * d ≤ m * (f * r) * (3 * l) := mul_le_mul_of_nonneg_left hd (by positivity)
  have h6 : m * (f * r * (3 * l)) ≤ 10 * f * r ^ 2 * (f * r * (3 * l)) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have h7 := mul_le_mul_of_nonneg_left h1 hc
  nlinarith

end GlobalTheory.RefSum.ToWeight

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelDbarCommPullbackOfSmoothDelDbar
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelDbarCommPullbackOfSmoothDelDbar
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CxForm.HolAtlas

variable {M M' : Type} [TopologicalSpace M] [TopologicalSpace M'] {n n' : ℕ} (A : HolAtlas M n) (A' : HolAtlas M' n')

theorem loc_pullback_eq {f : M' → M} {α : A.Fld} (hf : A.IsHolo A' f) (hα : A.IsForm α) (j : A'.ι) (i : A.ι) :
    IsOpen ((A'.e j).target ∩ (A'.e j).symm ⁻¹' (f ⁻¹' (A.e i).source)) ∧
    ∀ v ∈ (A'.e j).target ∩ (A'.e j).symm ⁻¹' (f ⁻¹' (A.e i).source),
      A'.loc (A.pullback A' f α) j v =
        pull (fderiv ℂ (A.e i ∘ f ∘ (A'.e j).symm) v) (A.loc α i ((A.e i ∘ f ∘ (A'.e j).symm) v)) := by
  refine ⟨(A'.e j).continuousOn_symm.isOpen_inter_preimage (A'.e j).open_target
    ((A.e i).open_source.preimage hf.1), fun v hv => ?_⟩
  have hs : (A'.e j).symm v ∈ (A'.e j).source := (A'.e j).map_target hv.1
  have hτ : (A.e i ∘ f ∘ (A'.e j).symm) v ∈ (A.e i).target := (A.e i).map_source hv.2
  rw [HolAtlas.loc, dite_eq_left hv.1, HolAtlas.loc, dite_eq_left hτ,
    GlobalTheory.T.holAtlas_pullback_eq_chart_expression M M' n n' A A' f α hf hα ⟨(j, (A'.e j).symm v), hs⟩ i hv.2]
  have hc : (A'.e j) ((A'.e j).symm v) = v := (A'.e j).right_inv hv.1
  simp only [Pt.crd, Pt.ch, Pt.pt, hc]
  congr 2
  exact Subtype.ext (Prod.ext rfl ((A.e i).left_inv hv.2).symm)

theorem pullback_del_dbar (f : M' → M) (α : A.Fld) (hf : A.IsHolo A' f) (hα : A.IsForm α) :
    A'.del (A.pullback A' f α) = A.pullback A' f (A.del α) ∧
      A'.dbar (A.pullback A' f α) = A.pullback A' f (A.dbar α) := by
  have key : ∀ x : A'.Pt, A'.del (A.pullback A' f α) x = A.pullback A' f (A.del α) x ∧
      A'.dbar (A.pullback A' f α) x = A.pullback A' f (A.dbar α) x := by
    intro x
    have hi : f x.pt ∈ (A.e (A.cover (f x.pt)).choose).source := (A.cover (f x.pt)).choose_spec
    obtain ⟨hU, hloc⟩ := loc_pullback_eq A A' hf hα x.1.1 (A.cover (f x.pt)).choose
    have hx : x.crd ∈ (A'.e x.1.1).target ∩ (A'.e x.1.1).symm ⁻¹' (f ⁻¹' (A.e (A.cover (f x.pt)).choose).source) := by
      refine ⟨(A'.e x.1.1).map_source x.2, ?_⟩
      show (A'.e x.1.1).symm (A'.e x.1.1 x.1.2) ∈ f ⁻¹' (A.e (A.cover (f x.pt)).choose).source
      rw [(A'.e x.1.1).left_inv x.2]
      exact hi
    have hτx : (A.e (A.cover (f x.pt)).choose ∘ f ∘ (A'.e x.1.1).symm) x.crd =
        A.e (A.cover (f x.pt)).choose (f x.pt) := by
      show A.e _ (f ((A'.e x.1.1).symm (A'.e x.1.1 x.1.2))) = _
      rw [(A'.e x.1.1).left_inv x.2]
    have hdiff : ∀ S, DifferentiableAt ℝ (fun y => (bas n).repr (A.loc α (A.cover (f x.pt)).choose y) S)
        ((A.e (A.cover (f x.pt)).choose ∘ f ∘ (A'.e x.1.1).symm) x.crd) := by
      intro S
      rw [hτx]
      exact ((hα.smooth _ S).differentiableOn (by simp)).differentiableAt
        ((A.e _).open_target.mem_nhds ((A.e _).map_source hi))
    have hc := GlobalTheory.T.del_dbar_chainRule_holomorphicPullback n' n _ _ (A.loc α (A.cover (f x.pt)).choose) x.crd hU hx (hf.2 x.1.1 _) hdiff
    have hl := (GlobalTheory.T.delOperatorAt_dbarOperatorAt_linear_local n' x.crd).2.2.2.1 _ _ (Filter.eventually_of_mem (hU.mem_nhds hx) hloc)
    rw [hτx] at hc
    exact ⟨(hl.1.trans hc.1 : _), (hl.2.trans hc.2 : _)⟩
  exact ⟨funext fun x => (key x).1, funext fun x => (key x).2⟩

end GlobalTheory.CxForm.HolAtlas

theorem GlobalTheory.CxForm.HolAtlas.del_dbar_comm_pullback : ∀ (M M' : Type) [TopologicalSpace M] [TopologicalSpace M'] (n n' : ℕ)
    (A : HolAtlas M n) (A' : HolAtlas M' n')
    (f : M' → M) (α : A.Fld), A.IsHolo A' f → A.IsForm α → A.IsForm (A.del α) → A.IsForm (A.dbar α) →
    A'.del (A.pullback A' f α) = A.pullback A' f (A.del α) ∧ A'.dbar (A.pullback A' f α) = A.pullback A' f (A.dbar α) :=
  fun _ _ _ _ _ _ A A' f α hf hα _ _ => HolAtlas.pullback_del_dbar A A' f α hf hα
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelDbarCommPullbackOfSmoothDelDbarStatement
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.del_dbar_comm_pullback_of_smooth_del_dbar : ∀ (M M' : Type) [TopologicalSpace M] [TopologicalSpace M'] (n n' : ℕ) (A : HolAtlas M n) (A' : HolAtlas M' n')
    (f : M' → M) (α : A.Fld), A.IsHolo A' f → A.IsForm α → A.IsForm (A.del α) → A.IsForm (A.dbar α) →
    A'.del (A.pullback A' f α) = A.pullback A' f (A.del α) ∧ A'.dbar (A.pullback A' f α) = A.pullback A' f (A.dbar α) := by
  first | exact @GlobalTheory.CxForm.HolAtlas.del_dbar_comm_pullback | exact GlobalTheory.CxForm.HolAtlas.del_dbar_comm_pullback | (intros; apply GlobalTheory.CxForm.HolAtlas.del_dbar_comm_pullback <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTranscendenceBasisFunctionFieldArithmeticVarie
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTranscendenceBasisFunctionFieldArithmeticVarie
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.ArithTrdeg

theorem trdeg_functionField_eq {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X]
    {p : X ⟶ Sp k} {D : ℕ} (h : IsArithVar p D) :
    Algebra.trdeg ℤ X.functionField = D := by
  have hft := DimCoheight.finiteType_of_isAmb (MixHt.isAmb_of_isArithVar h)
  have hc0 : CharZero Γ(X, ⊤) := (flat_int_iff_charZero _).1 h.flat

  have key : ∀ U : X.Opens, IsAffineOpen U → Nonempty U →
      ringKrullDim Γ(X, U) =
        ((Cardinal.toENat (Algebra.trdeg ℤ X.functionField) + 1 : ℕ∞) : WithBot ℕ∞) := by
    intro U hU hne
    have := hft U hU
    have := functionField_isFractionRing_of_isAffineOpen X U hU
    have : CharZero Γ(X, U) :=
      ((resG X (le_top : U ≤ ⊤)).charZero_iff (map_injective_of_isIntegral X _)).1 hc0
    have hinj : Function.Injective (algebraMap ℤ Γ(X, U)) := RingHom.injective_int _
    have : FaithfulSMul ℤ Γ(X, U) := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
    rw [IntFiniteTypeDim.ringKrullDim_eq_trdeg_add_one _ hinj,
      ← DimCoheight.trdeg_eq_of_isFractionRing ℤ Γ(X, U) X.functionField]
  have hdim : ((Cardinal.toENat (Algebra.trdeg ℤ X.functionField) + 1 : ℕ∞) : WithBot ℕ∞) =
      ((D + 1 : ℕ) : WithBot ℕ∞) := by
    rw [← h.dim_eq]
    apply le_antisymm
    · obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint X)) isOpen_univ
      have hU : IsAffineOpen U := hU
      rw [← key U hU ⟨⟨_, hxU⟩⟩, ← Published.dim_affineOpen hU]
      exact topologicalKrullDim_subspace_le X (U : Set X)
    · refine topologicalKrullDim_le_of_forall_exists_isOpen fun y => ?_
      obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
      have hU : IsAffineOpen U := hU
      refine ⟨(U : Set X), U.isOpen, hyU, ?_⟩
      rw [Published.dim_affineOpen hU, key U hU ⟨⟨y, hyU⟩⟩]
  have h2 : Cardinal.toENat (Algebra.trdeg ℤ X.functionField) = D := by
    have h3 : (Cardinal.toENat (Algebra.trdeg ℤ X.functionField) + 1 : ℕ∞) = ((D : ℕ∞) + 1) := by
      exact_mod_cast hdim
    exact (WithTop.add_right_cancel (ENat.one_ne_top) h3)
  exact Cardinal.toENat_eq_natCast.1 h2

theorem isTranscendenceBasis_functionField : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
    (∃ x : Fin D → X.functionField, IsTranscendenceBasis ℤ x) ∧
      ∀ x : Fin D → X.functionField, AlgebraicIndependent ℤ x → IsTranscendenceBasis ℤ x := by
  intro k _ X _ p D h
  have htr := trdeg_functionField_eq h
  refine ⟨?_, fun x hx => hx.isTranscendenceBasis_of_trdeg_le_of_finite (by rw [htr]; simp)⟩
  have : FaithfulSMul ℤ X.functionField := by
    have : CharZero X.functionField := by
      have hc0 : CharZero Γ(X, ⊤) := (flat_int_iff_charZero _).1 h.flat
      exact ((X.germToFunctionField ⊤).hom.charZero_iff (X.germToFunctionField_injective ⊤)).1 hc0
    exact (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.injective_int _)
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis ℤ X.functionField
  have hcard := hs.cardinalMk_eq_trdeg
  rw [htr] at hcard
  have : Finite s := Cardinal.lt_aleph0_iff_finite.1 (by rw [hcard]; exact Cardinal.natCast_lt_aleph0)
  have : Fintype s := Fintype.ofFinite s
  have e : s ≃ Fin D := Fintype.equivFinOfCardEq (by
    rw [Cardinal.mk_fintype] at hcard; exact_mod_cast hcard)
  exact ⟨_, hs.comp_equiv e.symm⟩

end GlobalTheory.ArithTrdeg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTranscendenceBasisFunctionFieldArithmeticVarieStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTranscendenceBasis_functionField_arithmeticVariety : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → (∃ x : Fin D → X.functionField, IsTranscendenceBasis ℤ x) ∧ ∀ x : Fin D → X.functionField, AlgebraicIndependent ℤ x → IsTranscendenceBasis ℤ x := by
  first | exact @GlobalTheory.ArithTrdeg.isTranscendenceBasis_functionField | exact GlobalTheory.ArithTrdeg.isTranscendenceBasis_functionField | (intros; apply GlobalTheory.ArithTrdeg.isTranscendenceBasis_functionField <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTranslA
noncomputable section

namespace GlobalTheory.UPel.HT.HeckeAd

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke

variable {S : Scheme.{0}} {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R}

def IsTranslA (f : D.La →+ D.La) (c k N : ℕ) {s : S ⟶ Sp R} (o : Obj b (N * k) s) (o' : Obj b N s)
    (ψ : o.A ⟶ o'.A) : Prop :=
  IsMonHom ψ ∧ (∀ a : D.O, o.act.act a ≫ ψ = ψ ≫ o'.act.act a) ∧ (∀ x, o'.eta x = o.eta (f x) ≫ ψ) ∧
    GlobalTheory.ZM.IsGaloisCover (heckeSubA o f N) (fun h => (transl h.1).left) ψ.left ∧
    Nonempty (LBIso (Hecke.lbPow o.P (k ^ 2 / c)) (o'.P.pull (sq2 ψ))) ∧ c ∣ k ^ 2

end GlobalTheory.UPel.HT.HeckeAd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankHopfAlgebraEqRangeMulKernel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankHopfAlgebraEqRangeMulKernel
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.Dieu

theorem finrank_eq_range_mul_ker : ∀ (k : Type) [Field k] (A : Type) [CommRing A] [HopfAlgebra k A]
    [IsCocomm k A] [Module.Finite k A] (C : Type) [CommRing C] [HopfAlgebra k C] [IsCocomm k C]
    [Module.Finite k C] (f : C →ₐc[k] A),
    Module.finrank k A = Module.finrank k (LinearMap.range (f : C →ₐ[k] A).toLinearMap) *
      Module.finrank k (A ⧸ kerIdeal f) := by
  intro k _ A _ _ _ _ C _ _ _ _ f
  rw [GlobalTheory.PDiv.finrank_eq_ker_mul_range k A C f, mul_comm]

end GlobalTheory.Dieu
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankHopfAlgebraEqRangeMulKernelStatement
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_hopfAlgebra_eq_range_mul_kernel : ∀ (k : Type) [Field k] (A : Type) [CommRing A] [HopfAlgebra k A] [IsCocomm k A] [Module.Finite k A] (C : Type) [CommRing C] [HopfAlgebra k C] [IsCocomm k C] [Module.Finite k C] (f : C →ₐc[k] A), Module.finrank k A = Module.finrank k (LinearMap.range (f : C →ₐ[k] A).toLinearMap) * Module.finrank k (A ⧸ kerIdeal f) := by
  first | exact @GlobalTheory.Dieu.finrank_eq_range_mul_ker | exact GlobalTheory.Dieu.finrank_eq_range_mul_ker | (intros; apply GlobalTheory.Dieu.finrank_eq_range_mul_ker <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfEvalCubeLevels
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfEvalCubeLevels
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz.Chart

theorem eq_zero_of_ev_cube : ∀ (p : ℕ) (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k) (c : Chart G d), (∀ n i, IsNilpotent ((Sum.elim (fun i => c.x n i ⊗ₜ[k] (1 : G.A n ⊗[k] G.A n)) (fun j => (1 : G.A n) ⊗ₜ[k] c.x₂ n j)) i)) ∧ ∀ f : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k, (∀ n (h : ∀ i, IsNilpotent ((Sum.elim (fun i => c.x n i ⊗ₜ[k] (1 : G.A n ⊗[k] G.A n)) (fun j => (1 : G.A n) ⊗ₜ[k] c.x₂ n j)) i)), evA k _ h f = 0) → f = 0 := by
  intro p k _ d G c
  have hnil : ∀ n i, IsNilpotent ((Sum.elim (fun i => c.x n i ⊗ₜ[k] (1 : G.A n ⊗[k] G.A n)) (fun j => (1 : G.A n) ⊗ₜ[k] c.x₂ n j)) i) := by
    intro n i
    cases i with
    | inl i => exact (c.nil n i).map (Algebra.TensorProduct.includeLeft (R := k) (S := k))
    | inr j => exact (c.nil₂ n j).map (Algebra.TensorProduct.includeRight (R := k))
  refine ⟨hnil, fun f hf => ?_⟩
  ext α
  obtain ⟨n, hn⟩ := c.presents.2 (α.degree + 1)
  have hs := c.presents.1 n
  have h2 := GlobalTheory.T.powerSeriesPresentation_up_to_order_tensorProduct k (Fin d) (Fin d) (G.A n) (G.A n) (c.x n) (c.nil n) (c.x n) (c.nil n)
    (c.nil₂ n) hs hs
  have h3 := GlobalTheory.T.powerSeriesPresentation_up_to_order_tensorProduct k (Fin d) (Fin d ⊕ Fin d) (G.A n) (G.A n ⊗[k] G.A n) (c.x n) (c.nil n)
    (c.x₂ n) (c.nil₂ n) (hnil n) hs h2.1
  have := (h3.2 (α.degree + 1) hn (h2.2 (α.degree + 1) hn hn) f (hf n (hnil n)) α (Nat.lt_succ_self _))
  simpa using this

end GlobalTheory.Katz.Chart
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfEvalCubeLevelsStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_eval_cube_levels : ∀ (p : ℕ) (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k) (c : Chart G d), (∀ n i, IsNilpotent ((Sum.elim (fun i => c.x n i ⊗ₜ[k] (1 : G.A n ⊗[k] G.A n)) (fun j => (1 : G.A n) ⊗ₜ[k] c.x₂ n j)) i)) ∧ ∀ f : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k, (∀ n (h : ∀ i, IsNilpotent ((Sum.elim (fun i => c.x n i ⊗ₜ[k] (1 : G.A n ⊗[k] G.A n)) (fun j => (1 : G.A n) ⊗ₜ[k] c.x₂ n j)) i)), evA k _ h f = 0) → f = 0 := by
  first | exact @GlobalTheory.Katz.Chart.eq_zero_of_ev_cube | exact GlobalTheory.Katz.Chart.eq_zero_of_ev_cube | (intros; apply GlobalTheory.Katz.Chart.eq_zero_of_ev_cube <;> assumption)
end
end
