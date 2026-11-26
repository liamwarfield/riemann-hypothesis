module

public import Development.AbelianVarietyTheory.Definitions.Foundations.HTLawAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnramifiedCocycleKillsRoots
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspFunctionalValueModPrimePowDiamondIndepende

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormLeOneOfIsIntegral
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries

namespace GlobalTheory.CoefCoord

variable {l : ℕ} [Fact l.Prime]

theorem norm_le_one_of_isIntegral (x : PadicAlgCl l) (h : IsIntegral ℤ_[l] x) : ‖x‖ ≤ 1 := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  change spectralValue (minpoly ℚ_[l] x) ≤ 1
  rw [spectralValue_le_one_iff (minpoly.monic hi)]
  intro n
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, Polynomial.coeff_map]
  exact PadicInt.norm_le_one _

theorem norm_le_one (c : Coef l) (x : c.O) : ‖(x : PadicAlgCl l)‖ ≤ 1 :=
  norm_le_one_of_isIntegral _
    ((isIntegral_algHom_iff c.O.val Subtype.val_injective).2 (Algebra.IsIntegral.isIntegral x))

theorem norm_unit (c : Coef l) (u : c.Oˣ) : ‖((u : c.O) : PadicAlgCl l)‖ = 1 := by
  have h1 := norm_le_one c u
  have h2 := norm_le_one c (↑u⁻¹ : c.O)
  have h3 : ((u : c.O) : PadicAlgCl l) * ((↑u⁻¹ : c.O) : PadicAlgCl l) = 1 := by
    rw [← Subalgebra.coe_mul, Units.mul_inv]; rfl
  have h4 := congrArg norm h3
  rw [norm_mul, norm_one] at h4
  have h5 : ‖((u : c.O) : PadicAlgCl l)‖ * ‖((↑u⁻¹ : c.O) : PadicAlgCl l)‖ ≤ ‖((u : c.O) : PadicAlgCl l)‖ :=
    mul_le_of_le_one_right (norm_nonneg _) h2
  linarith

theorem norm_natCast_lt_one : ‖((l : ℕ) : PadicAlgCl l)‖ < 1 := by
  rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)) l, PadicAlgCl.norm_extends, Padic.norm_p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)

theorem norm_algebraMap_padicInt (a : ℤ_[l]) : ‖algebraMap ℤ_[l] (PadicAlgCl l) a‖ = ‖a‖ := by
  show ‖algebraMap ℚ_[l] (PadicAlgCl l) (a : ℚ_[l])‖ = ‖a‖
  rw [PadicAlgCl.norm_extends]; rfl

theorem exists_eq_pow_mul (c : Coef l) (m : ℕ) (x : c.O)
    (hx : ‖(x : PadicAlgCl l)‖ ≤ ‖((l : ℕ) : PadicAlgCl l) ^ m‖) : ∃ z : c.O, x = (l : c.O) ^ m * z := by
  by_cases h0 : x = 0
  · exact ⟨0, by simp [h0]⟩
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible c.O
  obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hπ
  have hl0 : ((l : ℕ) : c.O) ≠ 0 := by
    intro h
    have h' := congrArg (fun y : c.O => (y : PadicAlgCl l)) h
    simp only [SubringClass.coe_natCast, ZeroMemClass.coe_zero] at h'
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) h'
  obtain ⟨e, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hπ
  set q := ‖(π : PadicAlgCl l)‖ with hqdef
  have hlq : ‖((l : ℕ) : PadicAlgCl l)‖ = q ^ e := by
    have h' := congrArg (fun y : c.O => ‖(y : PadicAlgCl l)‖) hw
    simp only [SubringClass.coe_natCast, Subalgebra.coe_mul, SubmonoidClass.coe_pow, norm_mul, norm_pow,
      norm_unit, one_mul] at h'
    exact h'
  have hq0 : 0 < q := by
    rw [hqdef, norm_pos_iff]
    intro h
    exact hπ.ne_zero (Subtype.ext h)
  have hq1 : q < 1 := by
    rcases (norm_le_one c π).lt_or_eq with h | h
    · exact h
    · exfalso
      have := (norm_natCast_lt_one (l := l))
      rw [hlq, hqdef, h, one_pow] at this
      exact lt_irrefl _ this
  have hxq : ‖(((u : c.O) * π ^ k : c.O) : PadicAlgCl l)‖ = q ^ k := by
    simp only [Subalgebra.coe_mul, SubmonoidClass.coe_pow, norm_mul, norm_pow, norm_unit, one_mul]
    rfl
  rw [hxq, norm_pow, hlq, ← pow_mul] at hx
  have hk : e * m ≤ k := (pow_le_pow_iff_right_of_lt_one₀ hq0 hq1).1 hx
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hk
  refine ⟨(u : c.O) * (↑w⁻¹ : c.O) ^ m * π ^ r, ?_⟩
  rw [hw]
  have h2 : ((w : c.O) * (↑w⁻¹ : c.O)) ^ m = 1 := by rw [Units.mul_inv, one_pow]
  linear_combination (-((u : c.O) * π ^ (e * m + r))) * h2

theorem norm_sub_val_le (m : ℕ) (a : ℤ_[l]) :
    ‖algebraMap ℤ_[l] (PadicAlgCl l) a - (((PadicInt.toZModPow m a).val : ℕ) : PadicAlgCl l)‖
      ≤ ‖((l : ℕ) : PadicAlgCl l) ^ m‖ := by
  have hk : a - (((PadicInt.toZModPow m a).val : ℕ) : ℤ_[l]) ∈ RingHom.ker (PadicInt.toZModPow (p := l) m) := by
    rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton'] at hk
  obtain ⟨t, ht⟩ := hk
  have e : algebraMap ℤ_[l] (PadicAlgCl l) a - (((PadicInt.toZModPow m a).val : ℕ) : PadicAlgCl l)
      = algebraMap ℤ_[l] (PadicAlgCl l) t * ((l : ℕ) : PadicAlgCl l) ^ m := by
    have := congrArg (algebraMap ℤ_[l] (PadicAlgCl l)) ht
    simp only [map_mul, map_pow, map_natCast, map_sub] at this
    rw [this]
  rw [e, norm_mul, norm_algebraMap_padicInt]
  exact mul_le_of_le_one_left (norm_nonneg _) (PadicInt.norm_le_one t)

theorem coe_eq_sum {ι : Type} [Fintype ι] (c : Coef l) (b : Module.Basis ι ℤ_[l] c.O) (y : c.O) :
    (y : PadicAlgCl l) = ∑ i, ((b i : c.O) : PadicAlgCl l) * algebraMap ℤ_[l] (PadicAlgCl l) (b.repr y i) := by
  conv_lhs => rw [← b.sum_repr y]
  rw [AddSubmonoidClass.coe_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Subalgebra.coe_smul, Algebra.smul_def, mul_comm]

theorem coord_mod_pow : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (m : ℕ), ∃ (ι : Type) (_ : Fintype ι) (o : ι → Qbar l)
    (crd : Qbar l → ι → ZMod (l ^ m)), (∀ i, o i ∈ c.O ∧ ‖o i‖ ≤ 1) ∧
    (∀ x ∈ c.O, ∀ y ∈ c.O, crd (x + y) = crd x + crd y) ∧ (∀ x ∈ c.O, Cg m x 0 → crd x = 0) ∧
    (∀ x ∈ c.O, Cg m x (∑ i, o i * ((crd x i).val : Qbar l))) ∧
    (∀ n : ι → ZMod (l ^ m), Cg m (∑ i, o i * ((n i).val : Qbar l)) 0 → n = 0) := by
  intro l _ c m
  classical
  let b := Module.Free.chooseBasis ℤ_[l] c.O
  let crd : Qbar l → Module.Free.ChooseBasisIndex ℤ_[l] c.O → ZMod (l ^ m) := fun x i =>
    if hx : x ∈ c.O then PadicInt.toZModPow m (b.repr ⟨x, hx⟩ i) else 0
  have hcrd : ∀ (x : Qbar l) (hx : x ∈ c.O) i, crd x i = PadicInt.toZModPow m (b.repr ⟨x, hx⟩ i) :=
    fun x hx i => dif_pos hx
  have hkill : ∀ x ∈ c.O, Cg m x 0 → crd x = 0 := by
    intro x hx h
    unfold Cg at h
    rw [sub_zero] at h
    obtain ⟨z, hz⟩ := exists_eq_pow_mul c m ⟨x, hx⟩ h
    funext i
    rw [hcrd x hx i, hz]
    have e : ((l : c.O) ^ m * z) = ((l : ℤ_[l]) ^ m) • z := by
      rw [Algebra.smul_def, map_pow, map_natCast]
    rw [e, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, map_pow, map_natCast, ← Nat.cast_pow,
      ZMod.natCast_self, zero_mul]
    rfl
  refine ⟨Module.Free.ChooseBasisIndex ℤ_[l] c.O, inferInstance, fun i => ((b i : c.O) : PadicAlgCl l), crd,
    fun i => ⟨(b i).2, norm_le_one c (b i)⟩, ?_, hkill, ?_, ?_⟩
  · intro x hx y hy
    funext i
    rw [hcrd _ (add_mem hx hy), Pi.add_apply, hcrd x hx, hcrd y hy,
      show (⟨x + y, add_mem hx hy⟩ : c.O) = ⟨x, hx⟩ + ⟨y, hy⟩ from rfl, map_add, Finsupp.add_apply, map_add]
  · intro x hx
    unfold Cg
    have hx' := coe_eq_sum c b ⟨x, hx⟩
    change x = _ at hx'
    simp only [hcrd x hx]
    rw [congrArg (fun t => t - _) hx', ← Finset.sum_sub_distrib]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => ?_
    rw [← mul_sub, norm_mul]
    exact (mul_le_mul (norm_le_one c (b i)) (norm_sub_val_le m _) (norm_nonneg _) zero_le_one).trans (by rw [one_mul])
  · intro n hn
    set y : Qbar l := ∑ i, ((b i : c.O) : PadicAlgCl l) * (((n i).val : ℕ) : Qbar l) with hydef
    have hy : y ∈ c.O := Subalgebra.sum_mem _ fun i _ => Subalgebra.mul_mem _ (b i).2 (Subalgebra.natCast_mem _ _)
    have hyb : (⟨y, hy⟩ : c.O) = ∑ i, (((n i).val : ℕ) : ℤ_[l]) • b i := by
      apply Subtype.ext
      rw [AddSubmonoidClass.coe_finsetSum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Subalgebra.coe_smul, Algebra.smul_def, map_natCast, mul_comm]
    have h0 := hkill y hy hn
    funext i
    have := congrFun h0 i
    rw [hcrd y hy i, hyb, b.repr_sum_self, map_natCast, ZMod.natCast_zmod_val] at this
    exact this

end GlobalTheory.CoefCoord
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormSubOnePowThreeLe
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col

namespace GlobalTheory.AmiceDist

variable {l : ℕ} [Fact l.Prime]

theorem sum_level (μ : ∀ r : ℕ, ZMod (l ^ r) → Qbar l)
    (hμ : ∀ r (x : ZMod (l ^ r)), μ r x = ∑ x' ∈ Finset.univ.filter
      (fun x' : ZMod (l ^ (r + 1)) => ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r)) x' = x), μ (r + 1) x')
    {r : ℕ} {z : Qbar l} (hz : z ^ (l ^ r) = 1) (R : ℕ) (hR : r ≤ R) :
    ∑ x : ZMod (l ^ R), μ R x * z ^ x.val = ∑ x : ZMod (l ^ r), μ r x * z ^ x.val := by
  induction R, hR using Nat.le_induction with
  | base => rfl
  | succ R hR ih =>
    rw [← ih]
    have hzR : z ^ (l ^ R) = 1 := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hR
      rw [pow_add, pow_mul, hz, one_pow]
    rw [← Finset.sum_fiberwise Finset.univ
      (fun x' : ZMod (l ^ (R + 1)) => ZMod.castHom (pow_dvd_pow l (Nat.le_succ R)) (ZMod (l ^ R)) x')]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hμ R x, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x' hx' => ?_
    rw [← (Finset.mem_filter.1 hx').2, ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast,
      ← pow_eq_pow_mod _ hzR]

theorem norm_trunc_binomial {w : Qbar l} (hw : ‖w‖ ≤ 1) (N k : ℕ) :
    ‖∑ n ∈ Finset.range N, (k.choose n : Qbar l) * w ^ n - (w + 1) ^ k‖ ≤ ‖w‖ ^ N := by
  have h1 : (w + 1) ^ k = ∑ n ∈ Finset.range (N + (k + 1)), (k.choose n : Qbar l) * w ^ n := by
    rw [add_pow]
    simp only [one_pow, mul_one]
    simp_rw [mul_comm (w ^ _)]
    refine Finset.sum_subset (Finset.range_mono (Nat.le_add_left _ _)) fun n _ hn => ?_
    rw [Nat.choose_eq_zero_of_lt (by simpa using hn)]
    simp
  rw [h1, Finset.sum_range_add, sub_add_cancel_left, norm_neg]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i _ => ?_
  rw [norm_mul, norm_pow]
  exact (mul_le_of_le_one_left (by positivity) (IsUltrametricDist.norm_natCast_le_one _ _)).trans
    (pow_le_pow_of_le_one (norm_nonneg _) hw (Nat.le_add_right _ _))

theorem norm_sub_one_le {r : ℕ} {z : Qbar l} (hz : z ^ (l ^ r) = 1) : ‖z - 1‖ ≤ 1 := by
  have h : ‖z‖ = 1 := by
    have h1 := congrArg norm hz
    rw [norm_pow, norm_one] at h1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)).1 h1
  rw [sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
  simp [h]

theorem norm_sub_one_pow_le {r : ℕ} {z : Qbar l} (hz : z ^ (l ^ r) = 1) : ‖z - 1‖ ^ (l ^ r) ≤ ‖((l : ℕ) : Qbar l)‖ := by
  have hw := norm_sub_one_le hz
  have h := (Commute.all (z - 1) 1).add_pow_prime_pow_eq (Fact.out : l.Prime) r
  rw [sub_add_cancel, hz] at h
  simp only [one_pow, mul_one] at h
  have h2 : (z - 1) ^ (l ^ r) = -((l : Qbar l) * (z - 1) *
      ∑ k ∈ Finset.Ioo 0 (l ^ r), (z - 1) ^ (k - 1) * (((l ^ r).choose k / l : ℕ) : Qbar l)) := by
    linear_combination -h
  rw [← norm_pow, h2, norm_neg, norm_mul, norm_mul]
  have h3 : ‖∑ k ∈ Finset.Ioo 0 (l ^ r), (z - 1) ^ (k - 1) * (((l ^ r).choose k / l : ℕ) : Qbar l)‖ ≤ 1 := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
    rw [norm_mul, norm_pow]
    exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) hw) (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ _)
  calc _ ≤ ‖((l : ℕ) : Qbar l)‖ * 1 * 1 := by gcongr
    _ = _ := by ring

theorem norm_sub_one_pow_three_le {r : ℕ} {z : Qbar l} (hz : z ^ (l ^ r) = 1) :
    ‖z - 1‖ ^ (l ^ (3 * r)) ≤ ‖((l : ℕ) : Qbar l) ^ (2 * r)‖ := by
  rw [show 3 * r = r + 2 * r by ring, pow_add, pow_mul, norm_pow]
  refine (pow_le_pow_left₀ (by positivity) (norm_sub_one_pow_le hz) _).trans ?_
  exact pow_le_pow_of_le_one (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ _)
    (Nat.lt_pow_self (Fact.out : l.Prime).one_lt).le

theorem amice : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (μ : ∀ r : ℕ, ZMod (l ^ r) → Qbar l), (∀ r x, μ r x ∈ c.O) →
    (∀ r (x : ZMod (l ^ r)), μ r x = ∑ x' ∈ Finset.univ.filter
      (fun x' : ZMod (l ^ (r + 1)) => ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r)) x' = x), μ (r + 1) x') →
    ∃ L : PowerSeries (Qbar l), (∀ n, L.coeff n ∈ c.O) ∧ ∀ r, 1 ≤ r → ∀ z : Qbar l, z ^ (l ^ r) = 1 →
      Cg (2 * r) (tval L (l ^ (3 * r)) z) (∑ x : ZMod (l ^ r), μ r x * z ^ x.val) := by
  intro l _ c μ hO hμ
  let a : ℕ → ℕ → Qbar l := fun n R => ∑ x : ZMod (l ^ R), μ R x * (x.val.choose n : Qbar l)
  have ha : ∀ n R, a n R ∈ c.O := fun n R => sum_mem fun x _ => mul_mem (hO R x) (natCast_mem _ _)
  have hlim : ∀ n, ∃ b ∈ c.O, Filter.Tendsto (a n) (Filter.hyperfilter ℕ) (nhds b) := by
    intro n
    obtain ⟨b, hb, h⟩ := (GlobalTheory.Coef.isCompact_O l c).ultrafilter_le_nhds ((Filter.hyperfilter ℕ).map (a n))
      (by
        rw [Filter.le_principal_iff]
        exact Filter.mem_map.2 (Filter.univ_mem' fun R => ha n R))
    exact ⟨b, hb, h⟩
  choose b hb hab using hlim
  refine ⟨PowerSeries.mk b, fun n => by simpa using hb n, fun r _ z hz => ?_⟩
  unfold Cg tval
  simp only [PowerSeries.coeff_mk]
  have ht : Filter.Tendsto (fun R => ‖∑ n ∈ Finset.range (l ^ (3 * r)), a n R * (z - 1) ^ n -
      ∑ x : ZMod (l ^ r), μ r x * z ^ x.val‖) (Filter.hyperfilter ℕ)
      (nhds ‖∑ n ∈ Finset.range (l ^ (3 * r)), b n * (z - 1) ^ n - ∑ x : ZMod (l ^ r), μ r x * z ^ x.val‖) :=
    ((tendsto_finsetSum _ fun n _ => (hab n).mul_const _).sub_const _).norm
  refine le_of_tendsto ht ?_
  have hev : ∀ᶠ R in (Filter.hyperfilter ℕ : Filter ℕ), r ≤ R :=
    Nat.hyperfilter_le_atTop (Filter.eventually_ge_atTop r)
  filter_upwards [hev] with R hR
  rw [← sum_level μ hμ hz R hR]
  simp only [a, Finset.sum_mul]
  rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun x _ => ?_
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, ← mul_sub, norm_mul]
  refine (mul_le_of_le_one_left (norm_nonneg _) (FirstDer.norm_le_one_of_mem c (hO R x))).trans ?_
  have h := norm_trunc_binomial (norm_sub_one_le hz) (l ^ (3 * r)) x.val
  rw [sub_add_cancel] at h
  exact h.trans (norm_sub_one_pow_three_le hz)

end GlobalTheory.AmiceDist
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ChSumSubCMul
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries

namespace GlobalTheory.KZ.Cmp

variable {l : ℕ} [Fact l.Prime]

def chSum (F : PowerSeries (Qbar l)) (m : ℕ) (z : Qbar l) (ψ : DirichletCharacter (Qbar l) (l ^ m)) : Qbar l :=
  ∑ b : (ZMod (l ^ m))ˣ, ψ b * tval F (l ^ (3 * m)) (z ^ (b : ZMod (l ^ m)).val)

def gSum (m : ℕ) (z : Qbar l) (ψ : DirichletCharacter (Qbar l) (l ^ m)) : Qbar l :=
  ∑ b : (ZMod (l ^ m))ˣ, ψ b * z ^ (b : ZMod (l ^ m)).val

def rSum (φ : DirichletCharacter (Qbar l) l) (e : ℕ) (F : PowerSeries (Qbar l)) (r : ℕ) (ξ : Qbar l) : Qbar l :=
  ∑ x ∈ (Finset.range (l ^ r)).filter (fun x => ¬ l ∣ x), φ (x : ZMod l) * ((x : Qbar l) ^ e) * mass F r ξ x

def InComp (φ : DirichletCharacter (Qbar l) l) (e : ℕ) {m : ℕ} (ψ : DirichletCharacter (Qbar l) (l ^ m)) : Prop :=
  ∀ b : (ZMod (l ^ m))ˣ, b ^ (l - 1) = 1 →
    ‖ψ⁻¹ (b : ZMod (l ^ m)) - (((b : ZMod (l ^ m)).val : Qbar l) ^ e) * φ (((b : ZMod (l ^ m)).val : ℕ) : ZMod l)‖ < 1

theorem tval_sub_C_mul (F G : PowerSeries (Qbar l)) (a : Qbar l) (N : ℕ) (z : Qbar l) :
    tval (F - PowerSeries.C a * G) N z = tval F N z - a * tval G N z := by
  unfold tval
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [map_sub, PowerSeries.coeff_C_mul]; ring

theorem tval_C_mul (G : PowerSeries (Qbar l)) (a : Qbar l) (N : ℕ) (z : Qbar l) :
    tval (PowerSeries.C a * G) N z = a * tval G N z := by
  unfold tval
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [PowerSeries.coeff_C_mul]; ring

end GlobalTheory.KZ.Cmp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsThBActSgDDiamIff
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

noncomputable section

namespace GlobalTheory.KZ

theorem isDiam_sgD_of_coprime {N l d : ℕ} (hl : l ≠ 0) (hd : Nat.Coprime d N) : IsDiam N l d (sgD N l d) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have h1 : d = 1 := Nat.coprime_zero_right d |>.1 hd
    subst h1
    refine Classical.epsilon_spec (p := IsDiam 0 l 1) ⟨1, ⟨?_, ?_⟩, ?_⟩
    · exact Subgroup.one_mem _
    · exact Subgroup.one_mem _
    · simp [en]
  · exact Betti.isDiam_sgD hN.ne' hl hd

theorem isDiam_mul {N l a d : ℕ} {s t : SL(2, ℤ)} (hs : IsDiam N l a s) (ht : IsDiam N l d t) :
    IsDiam N l (d * a) (s * t) := by
  obtain ⟨hs0, hsd⟩ := hs
  obtain ⟨ht0, htd⟩ := ht
  refine ⟨Subgroup.mul_mem _ hs0 ht0, ?_⟩
  have hsN := CongruenceSubgroup.Gamma0_mem.1 (Subgroup.mem_inf.1 hs0).1
  simp only [en] at hsd htd ⊢
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  push_cast
  rw [hsN, hsd, htd]
  ring

end GlobalTheory.KZ

theorem GlobalTheory.KZ.isThB_act_sgD_diam_iff : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ)
    (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime] (n w a d : ℕ), a.Coprime N → d.Coprime N →
    ∀ b : X.Fn l, b ∈ X.B N l w → ∀ φ : HahnSeries ℚ Ω,
  IsThB X A N l n (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) (X.diam N l a b)) φ ↔
    IsThB X A N l n (X.act l (sgD N l (d * a) : Matrix (Fin 2) (Fin 2) ℤ) b) φ := by
  intro Ω _ _ _ ε X A N l hl n w a d ha hd b hb φ
  have hl0 : l ≠ 0 := hl.out.ne_zero
  have hsa := GlobalTheory.KZ.isDiam_sgD_of_coprime (l := l) hl0 ha
  have hsd := GlobalTheory.KZ.isDiam_sgD_of_coprime (l := l) hl0 hd
  have hpos : ∀ g : SL(2, ℤ), 0 < (g : Matrix (Fin 2) (Fin 2) ℤ).det := fun g => by rw [g.det_coe]; exact one_pos
  have e : X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) (X.diam N l a b) =
      X.act l ((sgD N l a * sgD N l d : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) b := by
    rw [Matrix.SpecialLinearGroup.coe_mul, GlobalTheory.KZ.Tower.diam,
      GlobalTheory.KZ.Tower.act_act Ω ε X l _ _ (hpos _) (hpos _) b]
  rw [e]
  exact GlobalTheory.T.isCuspFunctionalValueModPrimePow_diamond_independent Ω ε X A N l n w (d * a) b hb _ (GlobalTheory.KZ.isDiam_mul hsa hsd) φ
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertiaFixedValuationEqZpowPrimeRatAlgClosure
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertiaFixedValuationEqZpowPrimeRatAlgClosure
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col

namespace GlobalTheory.InertiaFixedValue

open GlobalTheory.Published.AbVarRed IsLocalRing

theorem valuation_intCast_lt_one_iff {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : ValuationSubring Ω}
    (h : OverL l A) (n : ℤ) : A.valuation (n : Ω) < 1 ↔ (l : ℤ) ∣ n := by
  obtain ⟨v, hv, hl⟩ := h
  have hlZ : ((l : ℤ) : 𝓞 ℚ) ∈ v.asIdeal := by rw [Int.cast_natCast]; exact hl
  have hiff : (n : 𝓞 ℚ) ∈ v.asIdeal ↔ (l : ℤ) ∣ n := by
    constructor
    · intro hn
      by_contra hnd
      have hpr : Prime (l : ℤ) := Nat.prime_iff_prime_int.1 (Fact.out : l.Prime)
      obtain ⟨a, b, hab⟩ := (Irreducible.coprime_iff_not_dvd hpr.irreducible).2 hnd
      apply v.isPrime.ne_top
      rw [Ideal.eq_top_iff_one]
      have e : ((a * l + b * n : ℤ) : 𝓞 ℚ) = 1 := by rw [hab, Int.cast_one]
      rw [← e]
      push_cast
      exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ hlZ) (v.asIdeal.mul_mem_left _ hn)
    · rintro ⟨m, rfl⟩
      push_cast
      exact v.asIdeal.mul_mem_right _ (by exact_mod_cast hlZ)
  rw [← hiff, ← hv (n : 𝓞 ℚ)]
  simp

private theorem valuation_intCast_eq_one_of_not_dvd {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
    {A : ValuationSubring Ω} (h : OverL l A) (z : ℤ) (hz : ¬ (l : ℤ) ∣ z) : A.valuation (z : Ω) = 1 :=
  le_antisymm ((A.valuation_le_one_iff _).2 (intCast_mem A z))
    (not_lt.1 fun hlt => hz ((valuation_intCast_lt_one_iff h z).1 hlt))

private theorem not_dvd_den_of_valuation_le_one {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
    {A : ValuationSubring Ω} (h : OverL l A) (q : ℚ) (hq : A.valuation (algebraMap ℚ Ω q) ≤ 1) :
    ¬ (l : ℤ) ∣ (q.den : ℤ) := by
  intro hd

  have hn : ¬ (l : ℤ) ∣ q.num := by
    intro hn
    have h1 : l ∣ q.num.natAbs := Int.ofNat_dvd_left.1 hn
    have h2 : l ∣ q.den := by exact_mod_cast hd
    have h3 : l ∣ 1 := by
      have := Nat.dvd_gcd h1 h2
      rwa [Nat.Coprime.gcd_eq_one q.reduced] at this
    exact (Fact.out : l.Prime).ne_one (Nat.dvd_one.1 h3)
  have e0 : algebraMap ℚ Ω q * ((q.den : ℤ) : Ω) = (q.num : Ω) := by
    rw [← map_intCast (algebraMap ℚ Ω) (q.den : ℤ), ← map_intCast (algebraMap ℚ Ω) q.num, ← map_mul]
    congr 1
    rw [Int.cast_natCast]
    exact Rat.mul_den_eq_num q
  have e : A.valuation (algebraMap ℚ Ω q) * A.valuation ((q.den : ℤ) : Ω) = 1 := by
    rw [← map_mul, e0, valuation_intCast_eq_one_of_not_dvd h _ hn]
  have hlt : A.valuation ((q.den : ℤ) : Ω) < 1 := (valuation_intCast_lt_one_iff h _).2 hd
  have hlt1 : A.valuation (algebraMap ℚ Ω q) * A.valuation ((q.den : ℤ) : Ω) < 1 :=
    calc A.valuation (algebraMap ℚ Ω q) * A.valuation ((q.den : ℤ) : Ω)
        ≤ 1 * A.valuation ((q.den : ℤ) : Ω) := by gcongr
      _ = A.valuation ((q.den : ℤ) : Ω) := one_mul _
      _ < 1 := hlt
  rw [e] at hlt1
  exact lt_irrefl _ hlt1

theorem isAbove_of_overL {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : ValuationSubring Ω}
    (h : OverL l A) (R : Type) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra R ℚ] [IsFractionRing R ℚ]
    [Algebra ℤ R] [(Ideal.span {(l : ℤ)}).IsPrime] [IsLocalization.AtPrime R (Ideal.span {(l : ℤ)})] :
    IsAbove R ℚ A.toSubring := by
  unfold IsAbove
  have hcast : ∀ z : ℤ, algebraMap R ℚ (algebraMap ℤ R z) = z := fun z =>
    eq_intCast ((algebraMap R ℚ).comp (algebraMap ℤ R)) z
  have hs0 : ∀ s : (Ideal.span {(l : ℤ)}).primeCompl, ¬ (l : ℤ) ∣ (s : ℤ) := fun s hd =>
    Ideal.mem_primeCompl_iff.1 s.2 (Ideal.mem_span_singleton.2 hd)
  have hmk : ∀ (a : ℤ) (s : (Ideal.span {(l : ℤ)}).primeCompl),
      algebraMap R ℚ (IsLocalization.mk' R a s) = (a : ℚ) / ((s : ℤ) : ℚ) := by
    intro a s
    have hne : ((s : ℤ) : ℚ) ≠ 0 := by
      have : (s : ℤ) ≠ 0 := fun h0 => hs0 s (h0 ▸ dvd_zero _)
      exact_mod_cast this
    rw [eq_div_iff hne, ← hcast a, ← hcast (s : ℤ), ← map_mul, IsLocalization.mk'_spec]
  ext x
  rw [Subring.mem_comap, RingHom.mem_range]
  change algebraMap ℚ Ω x ∈ A ↔ _
  rw [← A.valuation_le_one_iff]
  constructor
  · intro hx
    have hden := not_dvd_den_of_valuation_le_one h x hx
    refine ⟨IsLocalization.mk' R x.num
      ⟨(x.den : ℤ), Ideal.mem_primeCompl_iff.2 fun hm => hden (Ideal.mem_span_singleton.1 hm)⟩, ?_⟩
    rw [hmk]
    push_cast
    exact Rat.num_div_den x
  · rintro ⟨r, rfl⟩
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Ideal.span {(l : ℤ)}).primeCompl r
    rw [hmk, map_div₀, map_intCast, map_intCast, map_div₀, valuation_intCast_eq_one_of_not_dvd h _ (hs0 s),
      div_one]
    exact (A.valuation_le_one_iff _).2 (intCast_mem A a)

theorem valuation_eq_zpow_of_fixed {R K Ω : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω]
    [IsSepClosure K Ω] (V : ValuationSubring Ω) (hV : IsAbove R K V.toSubring) {π : R} (hπ : Irreducible π)
    {c : Ω} (hc0 : c ≠ 0) (hc : c ∈ IntermediateField.fixedField (inertia K V)) :
    ∃ k : ℤ, V.valuation c = V.valuation (algebraMap K Ω (algebraMap R K π)) ^ k := by
  set p : Ω := algebraMap K Ω (algebraMap R K π) with hp
  have hpF : p ∈ IntermediateField.fixedField (inertia K V) := IntermediateField.algebraMap_mem _ _
  have hp0 : p ≠ 0 := by
    rw [hp, Ne, map_eq_zero_iff _ (algebraMap K Ω).injective,
      map_eq_zero_iff _ (IsFractionRing.injective R K)]
    exact hπ.ne_zero

  have hstep : ∀ n : ℕ, ∀ x : Ω, x ∈ IntermediateField.fixedField (inertia K V) → x ≠ 0 → x ∈ V →
      x / p ^ n ∉ V → ∃ k : ℕ, V.valuation x = V.valuation p ^ k := by
    intro n
    induction n with
    | zero =>
      intro x _ _ hxV hn
      rw [pow_zero, div_one] at hn
      exact absurd hxV hn
    | succ n ih =>
      intro x hxF hx0 hxV hn
      by_cases hxu : x ∈ V.nonunits
      · have hd : x / p ∈ V := GlobalTheory.FixInertUnram.div_uniformizer_mem R K Ω V hV π hπ x hxF hxu
        have hdn : x / p / p ^ n ∉ V := by rwa [div_div, ← pow_succ']
        obtain ⟨k, hk⟩ := ih (x / p) (div_mem hxF hpF) (div_ne_zero hx0 hp0) hd hdn
        refine ⟨k + 1, ?_⟩
        calc V.valuation x = V.valuation (x / p * p) := by rw [div_mul_cancel₀ x hp0]
          _ = V.valuation p ^ (k + 1) := by rw [map_mul, hk, pow_succ]
      · refine ⟨0, ?_⟩
        rw [pow_zero]
        exact le_antisymm ((V.valuation_le_one_iff x).2 hxV)
          (not_lt.1 fun hlt => hxu (V.mem_nonunits_iff.2 hlt))
  by_cases hcV : c ∈ V
  · obtain ⟨n, hn⟩ := GlobalTheory.not_mem_div_uniformizer_pow R K Ω V hV π hπ c hc0
    obtain ⟨k, hk⟩ := hstep n c hc hc0 hcV hn
    exact ⟨k, by rw [hk, zpow_natCast]⟩
  · have hi : c⁻¹ ∈ V := (V.mem_or_inv_mem c).resolve_left hcV
    obtain ⟨n, hn⟩ := GlobalTheory.not_mem_div_uniformizer_pow R K Ω V hV π hπ c⁻¹ (inv_ne_zero hc0)
    obtain ⟨k, hk⟩ := hstep n c⁻¹ (inv_mem hc) (inv_ne_zero hc0) hi hn
    refine ⟨-(k : ℤ), ?_⟩
    rw [zpow_neg, zpow_natCast, ← hk, map_inv₀, inv_inv]

theorem valuation_eq_zpow_of_ine_fixed : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (A : ValuationSubring Ω), OverL l A → ∀ c : Ω, c ≠ 0 → (∀ s ∈ Ine (F := ℚ) A, s c = c) →
    ∃ k : ℤ, A.valuation c = A.valuation (l : Ω) ^ k := by
  intro l _ Ω _ _ _ A hA c hc0 hc
  have hpr : Prime (l : ℤ) := Nat.prime_iff_prime_int.1 (Fact.out : l.Prime)
  have hne : Ideal.span {(l : ℤ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hM : (Ideal.span {(l : ℤ)}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hpr.irreducible
  have hP : (Ideal.span {(l : ℤ)}).IsPrime := hM.isPrime

  set B := A.comap (algebraMap ℚ Ω) with hB
  have hs0 : ∀ s : (Ideal.span {(l : ℤ)}).primeCompl, ¬ (l : ℤ) ∣ (s : ℤ) := fun s hd =>
    Ideal.mem_primeCompl_iff.1 s.2 (Ideal.mem_span_singleton.2 hd)
  have hloc : IsLocalization.AtPrime B (Ideal.span {(l : ℤ)}) := by
    refine ⟨⟨?_, ?_, ?_⟩⟩
    · intro s
      have hs' := hs0 s
      have hsq : ((s : ℤ) : ℚ) ≠ 0 := by
        have : (s : ℤ) ≠ 0 := fun h0 => hs' (h0 ▸ dvd_zero _)
        exact_mod_cast this
      have hinv : ((s : ℤ) : ℚ)⁻¹ ∈ B := by
        rw [hB, ValuationSubring.mem_comap, ← A.valuation_le_one_iff, map_inv₀, map_intCast, map_inv₀,
          valuation_intCast_eq_one_of_not_dvd hA _ hs', inv_one]
      refine IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext ?_)
      simp [hsq]
    · intro z
      have hz : A.valuation (algebraMap ℚ Ω (z : ℚ)) ≤ 1 :=
        (A.valuation_le_one_iff _).2 (ValuationSubring.mem_comap.1 z.2)
      have hden := not_dvd_den_of_valuation_le_one hA _ hz
      refine ⟨⟨(z : ℚ).num, ⟨((z : ℚ).den : ℤ),
        Ideal.mem_primeCompl_iff.2 fun hm => hden (Ideal.mem_span_singleton.1 hm)⟩⟩, Subtype.ext ?_⟩
      simp only [MulMemClass.coe_mul, eq_intCast, SubringClass.coe_intCast, Int.cast_natCast]
      exact Rat.mul_den_eq_num _
    · intro x y hxy
      refine ⟨1, ?_⟩
      have hq : (x : ℚ) = y := by
        have := congrArg (fun b : B => (b : ℚ)) hxy
        simpa using this
      simp only [OneMemClass.coe_one, one_mul]
      exact_mod_cast hq
  have : IsDiscreteValuationRing B :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain ℤ hne B
  have : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  have : Finite (ℤ ⧸ Ideal.span {(l : ℤ)}) := Finite.of_equiv _ (Int.quotientSpanNatEquivZMod l).symm.toEquiv
  have : Finite (ResidueField B) :=
    Finite.of_equiv _ (IsLocalization.AtPrime.equivQuotMaximalIdeal (Ideal.span {(l : ℤ)}) B).toEquiv
  have hAb : IsAbove B ℚ A.toSubring := isAbove_of_overL hA B
  have hirr : Irreducible (algebraMap ℤ B l) := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer,
      ← IsLocalization.AtPrime.map_eq_maximalIdeal (Ideal.span {(l : ℤ)}) B, Ideal.map_span,
      Set.image_singleton]

  have hs : ∀ σ ∈ inertia ℚ A, σ ∈ Ine (F := ℚ) A := by
    intro σ hσ
    rw [mem_Ine]
    unfold inertia at hσ
    obtain ⟨τ, hτ, rfl⟩ := Subgroup.mem_map.1 hσ
    refine ⟨τ.2, fun x hx => ?_⟩
    set a : A := ⟨x, (A.valuation_le_one_iff x).1 hx⟩
    have hfix : τ • IsLocalRing.residue A a = IsLocalRing.residue A a := by
      have := congrArg (fun f => f (IsLocalRing.residue A a)) (MonoidHom.mem_ker.1 hτ)
      simpa using this
    have h0 : IsLocalRing.residue A (τ • a - a) = 0 := by
      rw [map_sub, IsLocalRing.ResidueField.residue_smul, hfix, sub_self]
    have hm : τ • a - a ∈ IsLocalRing.maximalIdeal A := Ideal.Quotient.eq_zero_iff_mem.1 h0
    exact (A.valuation_lt_one_iff _).1 hm
  have hfixc : c ∈ IntermediateField.fixedField (inertia ℚ A) :=
    (IntermediateField.mem_fixedField_iff _ _).2 fun σ hσ => hc σ (hs σ hσ)
  obtain ⟨k, hk⟩ := valuation_eq_zpow_of_fixed A hAb hirr hc0 hfixc
  refine ⟨k, ?_⟩
  rw [hk]
  simp

end GlobalTheory.InertiaFixedValue
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertiaFixedValuationEqZpowPrimeRatAlgClosureStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertiaFixed_valuation_eq_zpow_prime_ratAlgClosure : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ c : Ω, c ≠ 0 → (∀ s ∈ Ine (F := ℚ) A, s c = c) → ∃ k : ℤ, A.valuation c = A.valuation (l : Ω) ^ k := by
  first | exact @GlobalTheory.InertiaFixedValue.valuation_eq_zpow_of_ine_fixed | exact GlobalTheory.InertiaFixedValue.valuation_eq_zpow_of_ine_fixed | (intros; apply GlobalTheory.InertiaFixedValue.valuation_eq_zpow_of_ine_fixed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemCycAlgOfPow
noncomputable section

open ReciprocityTheory.Gal Formalism.ConjugateSelfDual

namespace GlobalTheory.RecOne

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

def fixA (A : ValuationSubring Ω) : Subring A where
  carrier := {a | ∀ s ∈ Ine (F := ℚ) A, s (a : Ω) = a}
  one_mem' := fun s _ => by simp
  mul_mem' := fun {a b} ha hb s hs => by
    show s ((a : Ω) * (b : Ω)) = (a : Ω) * (b : Ω)
    rw [map_mul, ha s hs, hb s hs]
  zero_mem' := fun s _ => by simp
  add_mem' := fun {a b} ha hb s hs => by
    show s ((a : Ω) + (b : Ω)) = (a : Ω) + (b : Ω)
    rw [map_add (f := _), ha s hs, hb s hs]
  neg_mem' := fun {a} ha s hs => by
    show s (-(a : Ω)) = -(a : Ω)
    rw [map_neg, ha s hs]

theorem mem_fixA {A : ValuationSubring Ω} {a : A} : a ∈ fixA A ↔ ∀ s ∈ Ine (F := ℚ) A, s (a : Ω) = a := Iff.rfl

abbrev dA (A : ValuationSubring Ω) : Derivation (fixA A) A (KaehlerDifferential (fixA A) A) :=
  KaehlerDifferential.D (fixA A) A

def cycAlg (l : ℕ) (A : ValuationSubring Ω) : Subalgebra (fixA A) A :=
  Algebra.adjoin (fixA A) {z : A | ∃ n : ℕ, z ^ (l ^ n) = 1}

theorem mem_cycAlg_of_pow {l : ℕ} {A : ValuationSubring Ω} {z : A} {n : ℕ} (h : z ^ (l ^ n) = 1) :
    z ∈ cycAlg l A := Algebra.subset_adjoin ⟨n, h⟩

def ineCyc (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω) : Subgroup (G ℚ Ω) :=
  Ine (F := ℚ) A ⊓ (cycZ ℚ Ω l).ker

theorem mem_ineCyc {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {s : G ℚ Ω} :
    s ∈ ineCyc l A ↔ s ∈ Ine (F := ℚ) A ∧ cycZ ℚ Ω l s = 1 := Iff.rfl

abbrev FracA (A : ValuationSubring Ω) : Type := Ω ⧸ LinearMap.range (Algebra.linearMap A Ω)


omit [Algebra ℚ Ω] in
theorem mem_of_pow_mem (A : ValuationSubring Ω) {x : Ω} {n : ℕ} (hn : n ≠ 0)
    (h : x ^ n ∈ A) : x ∈ A := by
  rw [← A.valuation_le_one_iff] at h ⊢
  rw [map_pow] at h
  by_contra hx
  push_neg at hx
  exact absurd h (not_le.2 (one_lt_pow' hx hn))

end GlobalTheory.RecOne
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsClosedInertiaCyclotomicKernel
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousToZModPow
namespace GlobalTheory.ContinuousZModPow

theorem continuous_toZModPow (l : ℕ) [hl : Fact (Nat.Prime l)] (n : ℕ) :
    Continuous (⇑(PadicInt.toZModPow n) : ℤ_[l] → ZMod (l ^ n)) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  have hpos : (0 : ℝ) < (l : ℝ) ^ (-(n : ℤ)) := zpow_pos (by exact_mod_cast hl.out.pos) _
  have hev : ∀ᶠ y in nhds x, PadicInt.toZModPow n y = PadicInt.toZModPow n x := by
    filter_upwards [Metric.closedBall_mem_nhds x hpos] with y hy
    rw [Metric.mem_closedBall, dist_eq_norm, PadicInt.norm_le_pow_iff_mem_span_pow,
      ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, sub_eq_zero] at hy
    exact hy
  exact tendsto_nhds_of_eventually_eq hev

theorem main : ∀ (l : ℕ) [hl : Fact (Nat.Prime l)] (n : ℕ),
    Continuous (⇑(PadicInt.toZModPow n) : ℤ_[l] → ZMod (l ^ n)) := by
  intro l _ n
  exact continuous_toZModPow l n

end GlobalTheory.ContinuousZModPow
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsClosedInertiaCyclotomicKernel
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries

namespace GlobalTheory.InertiaClosed

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

theorem isOpen_setOf_apply [Algebra.IsAlgebraic ℚ Ω] (x : Ω) (P : Ω → Prop) :
    IsOpen {σ : G ℚ Ω | P (σ x)} := by
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {x}) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  have hH : ((IntermediateField.adjoin ℚ {x}).fixingSubgroup : Set (G ℚ Ω)) ∈ nhds (1 : G ℚ Ω) :=
    (IntermediateField.fixingSubgroup_isOpen _).mem_nhds (Subgroup.one_mem _)
  rw [isOpen_iff_mem_nhds]
  intro σ hσ
  rw [← map_mul_left_nhds_one σ]
  refine Filter.mem_map.2 (Filter.mem_of_superset hH fun τ hτ => ?_)
  have hτx : τ x = x :=
    (IntermediateField.mem_fixingSubgroup_iff _ _).1 hτ x (IntermediateField.mem_adjoin_simple_self ℚ x)
  show P ((σ * τ) x)
  rw [AlgEquiv.mul_apply, hτx]
  exact hσ

theorem isClosed_setOf_apply [Algebra.IsAlgebraic ℚ Ω] (x : Ω) (P : Ω → Prop) :
    IsClosed {σ : G ℚ Ω | P (σ x)} := by
  have h := isOpen_setOf_apply x (fun y => ¬ P y)
  rw [← isOpen_compl_iff]
  convert h using 1

theorem mem_dec_of_forall {A : ValuationSubring Ω} {σ : G ℚ Ω} (h : ∀ x, σ x ∈ A ↔ x ∈ A) :
    σ ∈ A.decompositionSubgroup ℚ := by
  show σ ∈ Dec (F := ℚ) A
  rw [mem_Dec]
  ext x
  rw [show x = σ ((σ⁻¹ : G ℚ Ω) x) from (mul_inv_apply x).symm, ← AlgEquiv.smul_def σ ((σ⁻¹ : G ℚ Ω) x),
    ValuationSubring.smul_mem_pointwise_smul_iff, AlgEquiv.smul_def, h]

theorem isClosed_Ine [Algebra.IsAlgebraic ℚ Ω] (A : ValuationSubring Ω) :
    IsClosed ((Ine (F := ℚ) A : Subgroup (G ℚ Ω)) : Set (G ℚ Ω)) := by
  have e : ((Ine (F := ℚ) A : Subgroup (G ℚ Ω)) : Set (G ℚ Ω)) =
      (⋂ x : Ω, {σ : G ℚ Ω | (σ x ∈ A ↔ x ∈ A)}) ∩
        ⋂ x : Ω, {σ : G ℚ Ω | A.valuation x ≤ 1 → A.valuation (σ x - x) < 1} := by
    ext σ
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq, SetLike.mem_coe]
    constructor
    · intro h
      exact ⟨fun x => apply_mem_iff_of_mem_Dec (F := ℚ) h.1 x, h.2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨mem_dec_of_forall h1, h2⟩
  rw [e]
  exact (isClosed_iInter fun x => isClosed_setOf_apply (Ω := Ω) x (fun y => (y ∈ A ↔ x ∈ A))).inter
    (isClosed_iInter fun x => isClosed_setOf_apply (Ω := Ω) x
      (fun y => A.valuation x ≤ 1 → A.valuation (y - x) < 1))

theorem continuous_toZModPow' (l : ℕ) [hl : Fact l.Prime] (n : ℕ) :
    Continuous (PadicInt.toZModPow (p := l) n) := by
  first
  | exact @_root_.GlobalTheory.ContinuousZModPow.main
  | exact _root_.GlobalTheory.ContinuousZModPow.main
  | (apply _root_.GlobalTheory.ContinuousZModPow.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.ContinuousZModPow.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ContinuousZModPow.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ContinuousZModPow.main ..)

theorem isClosed_ker_cycMod (l : ℕ) [Fact l.Prime] (m : ℕ) :
    IsClosed (((cycMod ℚ Ω l m).ker : Subgroup (G ℚ Ω)) : Set (G ℚ Ω)) := by
  have hc : Continuous fun σ : G ℚ Ω => PadicInt.toZModPow m ((cycZ ℚ Ω l σ : ℤ_[l]ˣ) : ℤ_[l]) :=
    (continuous_toZModPow' l m).comp (Units.continuous_val.comp (continuous_cycZ ℚ Ω l))
  have e : (((cycMod ℚ Ω l m).ker : Subgroup (G ℚ Ω)) : Set (G ℚ Ω)) =
      (fun σ : G ℚ Ω => PadicInt.toZModPow m ((cycZ ℚ Ω l σ : ℤ_[l]ˣ) : ℤ_[l])) ⁻¹' {1} := by
    ext σ
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, Set.mem_singleton_iff]
    rw [← Units.val_eq_one]
    rfl
  rw [e]
  exact (isClosed_discrete _).preimage hc

end GlobalTheory.InertiaClosed


open GlobalTheory.InertiaClosed in
theorem GlobalTheory.isClosed_Ine_inf_ker_cycMod : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω]
    [Algebra.IsAlgebraic ℚ Ω] (A : ValuationSubring Ω) (m : ℕ),
    IsClosed ((Ine (F := ℚ) A ⊓ (cycMod ℚ Ω l m).ker : Subgroup (G ℚ Ω)) : Set (G ℚ Ω)) := by
  intro l _ Ω _ _ _ A m
  rw [Subgroup.coe_inf]
  exact (isClosed_Ine A).inter (isClosed_ker_cycMod l m)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsClosedInertiaCyclotomicKernelStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosed_inertia_cyclotomic_kernel : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [Algebra.IsAlgebraic ℚ Ω] (A : ValuationSubring Ω) (m : ℕ), IsClosed ((Ine (F := ℚ) A ⊓ (cycMod ℚ Ω l m).ker : Subgroup (G ℚ Ω)) : Set (G ℚ Ω)) := by
  first | exact @GlobalTheory.isClosed_Ine_inf_ker_cycMod | exact GlobalTheory.isClosed_Ine_inf_ker_cycMod | (intros; apply GlobalTheory.isClosed_Ine_inf_ker_cycMod <;> assumption)
end
end
