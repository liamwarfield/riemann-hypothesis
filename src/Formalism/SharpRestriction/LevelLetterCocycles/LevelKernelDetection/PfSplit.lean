module

public import Formalism.SharpRestriction.LevelLetterCocycles.KillWinFromCut

@[expose] public section

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.ExistsInvariantLiftAverage
section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.BasisCombinationMemInvariants
section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.IdempotentMemInvariants
noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G Formalism.MainNotions.N.Ln03

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    [Fintype (K →ₐ[Qp] LL)]


variable (W) in
def k17e (i : ZMod n) : W.EE := algebraMap (LetA O n) W.EE (letE i)

theorem idempotent_mul_self_bis (i : ZMod n) : k17e W i * k17e W i = k17e W i := by
  rw [k17e, ← map_mul, letE_mul_self]

theorem idempotent_gamma_invariant (i : ZMod n) (g : W.Gam) : W.γE g (k17e W i) = k17e W i := by
  rw [k17e, W.γE_ext]
  exact congrArg (algebraMap (LetA O n) W.EE) (γA_letE W g i)

theorem idempotent_smul_eq_mul (i : ZMod n) (ε : W.EE) : (letE i : LetA O n) • ε = k17e W i * ε :=
  Algebra.smul_def _ _

theorem isUnit_of_isUnit_mod_l (x : W.EE)
    (h : IsUnit (Ideal.Quotient.mk (Ideal.span {((PD.p : ℕ) : W.EE)}) x)) : IsUnit x := by
  have hc := W.EE_complete
  obtain ⟨u, hu⟩ := h
  obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective (↑u⁻¹ : W.EE ⧸ Ideal.span {((PD.p : ℕ) : W.EE)})
  have h1 : x * w - 1 ∈ Ideal.span {((PD.p : ℕ) : W.EE)} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hw, ← hu, Units.mul_inv, map_one,
      sub_self]
  have h2 := Ideal.isUnit_of_sub_one_mem_jacobson_bot _
    (IsAdicComplete.le_jacobson_bot (I := Ideal.span {((PD.p : ℕ) : W.EE)}) h1)
  exact isUnit_of_mul_isUnit_left h2

theorem isUnit_of_unit_coefficient (hOloc : IsLocalRing O)
    (hOnil : ∀ c ∈ IsLocalRing.maximalIdeal O, ∃ (N : ℕ) (d : O), c ^ N = ((PD.p : ℕ) : O) * d)
    (i : ZMod n) (x : W.EE) (hx : k17e W i * x = x) (m : ℕ) (a : LetA O n)
    (ha : x * algebraMap (LetA O n) W.EE (letπ ^ m) - algebraMap (LetA O n) W.EE a ∈
      Ideal.span {((PD.p : ℕ) : W.EE) ^ 1})
    (hk : ∃ k, IsUnit (PowerSeries.coeff k (a i))) : IsUnit (x + (1 - k17e W i)) := by
  classical
  set k₀ := Nat.find hk with hk₀
  have hu₀ : IsUnit (PowerSeries.coeff k₀ (a i)) := Nat.find_spec hk
  have hlow : ∀ j < k₀, PowerSeries.coeff j (a i) ∈ IsLocalRing.maximalIdeal O := fun j hj =>
    (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 (Nat.find_min hk hj))
  obtain ⟨Lp, hLp⟩ : ∃ Lp : PowerSeries O, Lp = ∑ j ∈ Finset.range k₀,
    PowerSeries.C (PowerSeries.coeff j (a i)) * PowerSeries.X ^ j := ⟨_, rfl⟩
  have hcL : ∀ d, PowerSeries.coeff d Lp = if d < k₀ then PowerSeries.coeff d (a i) else 0 := by
    intro d
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hLp, map_sum, PowerSeries.coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_range]
  have hdvd : (PowerSeries.X : PowerSeries O) ^ k₀ ∣ a i - Lp := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro d hd
    rw [map_sub, hcL, if_pos hd, sub_self]
  obtain ⟨U, hU⟩ := hdvd
  have hUu : IsUnit U := by
    rw [PowerSeries.isUnit_iff_constantCoeff, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    have h1 := congrArg (PowerSeries.coeff k₀) hU
    rw [PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, map_sub, hcL,
      if_neg (lt_irrefl _), sub_zero] at h1
    rw [← h1]
    exact hu₀
  let δf : LetA O n := fun j => if j = i then 1 else PowerSeries.X ^ k₀
  let uf : LetA O n := fun j => if j = i then U else 1
  let γf : LetA O n := fun j => if j = i then PowerSeries.X ^ k₀ * U else 1
  have hγδ : γf * δf = letπ ^ k₀ * uf := by
    funext j
    by_cases h : j = i
    · simp [γf, δf, uf, letπ, h, mul_comm]
    · simp [γf, δf, uf, letπ, h]
  have huf : IsUnit uf := Pi.isUnit_iff.2 fun j => by
    by_cases h : j = i
    · simp [uf, h, hUu]
    · simp [uf, h]
  have hγ : IsUnit (algebraMap (LetA O n) W.EE γf) := by
    have h1 : IsUnit (algebraMap (LetA O n) W.EE (γf * δf)) := by
      rw [hγδ, map_mul, map_pow]
      exact (W.EE_π.pow _).mul (huf.map _)
    rw [map_mul] at h1
    exact isUnit_of_mul_isUnit_left h1
  let t : ℕ → LetA O n := fun j =>
    Pi.single i (PowerSeries.C (PowerSeries.coeff j (a i)) * PowerSeries.X ^ j)
  have hdec : (letE i : LetA O n) * a + (1 - letE i) = ∑ j ∈ Finset.range k₀, t j + γf := by
    funext j'
    by_cases h : j' = i
    · rw [h]
      have hsum : (∑ j ∈ Finset.range k₀, t j) i = Lp := by
        rw [hLp, Finset.sum_apply]
        simp [t]
      have hai : a i = Lp + PowerSeries.X ^ k₀ * U := by rw [← hU]; ring
      rw [show (∑ j ∈ Finset.range k₀, t j + γf) i = (∑ j ∈ Finset.range k₀, t j) i + γf i from rfl,
        hsum]
      simp [letE, γf, hai]
    · simp [t, γf, letE, Finset.sum_apply, h]
  set I := Ideal.span {((PD.p : ℕ) : W.EE)} with hI
  have hnil : ∀ j ∈ Finset.range k₀,
      IsNilpotent (Ideal.Quotient.mk I (algebraMap (LetA O n) W.EE (t j))) := by
    intro j hj
    obtain ⟨N, d, hNd⟩ := hOnil _ (hlow j (Finset.mem_range.1 hj))
    refine ⟨N + 1, ?_⟩
    have hpow : t j ^ (N + 1) = ((PD.p : ℕ) : LetA O n) *
        Pi.single i (PowerSeries.C (PowerSeries.coeff j (a i) * d) * PowerSeries.X ^ (j * (N + 1))) := by
      funext j'
      by_cases h : j' = i
      · subst h
        simp only [t, Pi.pow_apply, Pi.mul_apply, Pi.single_eq_same, Pi.natCast_apply]
        rw [mul_pow, ← map_pow, pow_succ, hNd, ← pow_mul]
        simp only [map_mul, map_natCast]
        ring
      · simp [t, h]
    rw [← map_pow, ← map_pow, Ideal.Quotient.eq_zero_iff_mem, hpow, map_mul, map_natCast]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  have hq : Ideal.Quotient.mk I (x * algebraMap (LetA O n) W.EE (letπ ^ m) + (1 - k17e W i)) =
      Ideal.Quotient.mk I (algebraMap (LetA O n) W.EE ((letE i : LetA O n) * a + (1 - letE i))) := by
    rw [Ideal.Quotient.eq]
    have h1 : x * algebraMap (LetA O n) W.EE (letπ ^ m) + (1 - k17e W i) -
        algebraMap (LetA O n) W.EE ((letE i : LetA O n) * a + (1 - letE i)) =
        k17e W i * (x * algebraMap (LetA O n) W.EE (letπ ^ m) - algebraMap (LetA O n) W.EE a) := by
      rw [map_add (f := _), map_mul, map_sub, map_one]
      simp only [k17e] at hx ⊢
      linear_combination (-(algebraMap (LetA O n) W.EE (letπ ^ m))) * hx
    rw [h1, hI, ← pow_one ((PD.p : ℕ) : W.EE)]
    exact Ideal.mul_mem_left _ _ ha
  have hunit : IsUnit (x * algebraMap (LetA O n) W.EE (letπ ^ m) + (1 - k17e W i)) := by
    apply isUnit_of_isUnit_mod_l
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hq, hdec, map_add (f := _), map_add (f := _), map_sum, map_sum]
    exact (isNilpotent_sum hnil).isUnit_add_right_of_commute (hγ.map _) (Commute.all _ _)
  have hprod : (x + (1 - k17e W i)) * (k17e W i * algebraMap (LetA O n) W.EE (letπ ^ m) +
      (1 - k17e W i)) = x * algebraMap (LetA O n) W.EE (letπ ^ m) + (1 - k17e W i) := by
    have he := idempotent_mul_self_bis (W := W) i
    linear_combination (algebraMap (LetA O n) W.EE (letπ ^ m) - 1) * hx -
      (algebraMap (LetA O n) W.EE (letπ ^ m) - 1) * he
  rw [← hprod] at hunit
  exact isUnit_of_mul_isUnit_left hunit

theorem local_corner_unit_dichotomy (hOloc : IsLocalRing O)
    (hOnil : ∀ c ∈ IsLocalRing.maximalIdeal O, ∃ (N : ℕ) (d : O), c ^ N = ((PD.p : ℕ) : O) * d)
    (i : ZMod n) (x : W.EE) (hx : k17e W i * x = x) :
    IsUnit (x + (1 - k17e W i)) ∨ IsUnit ((k17e W i - x) + (1 - k17e W i)) := by
  obtain ⟨a, m, ha⟩ := W.EE_dense x 1
  by_cases hk : ∃ k, IsUnit (PowerSeries.coeff k (a i))
  · exact Or.inl (isUnit_of_unit_coefficient hOloc hOnil i x hx m a (by simpa using ha) hk)
  · right
    push Not at hk
    have he := idempotent_mul_self_bis (W := W) i
    refine isUnit_of_unit_coefficient hOloc hOnil i _ (by linear_combination he - hx) m
      ((letE i : LetA O n) * letπ ^ m - a : LetA O n) ?_ ⟨m, ?_⟩
    · have h1 : (k17e W i - x) * algebraMap (LetA O n) W.EE (letπ ^ m) -
          algebraMap (LetA O n) W.EE ((letE i : LetA O n) * letπ ^ m - a) =
          -(x * algebraMap (LetA O n) W.EE (letπ ^ m) - algebraMap (LetA O n) W.EE a) := by
        rw [map_sub, map_mul]
        simp only [k17e]
        ring
      rw [h1]
      exact neg_mem (by simpa using ha)
    · have h1 : ((letE i : LetA O n) * letπ ^ m - a : LetA O n) i = PowerSeries.X ^ m - a i := by
        simp [letE, letπ]
      rw [h1, map_sub, PowerSeries.coeff_X_pow_self]
      have := hOloc
      exact IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ (mem_nonunits_iff.2 (hk m))


variable (W) in
def k17S : Subring W.EE where
  carrier := {ε | ∀ δ ∈ W.DelF, W.γE δ ε = ε}
  mul_mem' {a b} ha hb δ hδ := by rw [map_mul, ha δ hδ, hb δ hδ]
  one_mem' δ _ := map_one _
  add_mem' {a b} ha hb δ hδ := by rw [map_add (f := _), ha δ hδ, hb δ hδ]
  zero_mem' δ _ := map_zero _
  neg_mem' {a} ha δ hδ := by rw [map_neg, ha δ hδ]

theorem k17e_mem_k17S (i : ZMod n) : k17e W i ∈ k17S W := fun δ _ => idempotent_gamma_invariant i δ


variable (W) in
def idempotentInvariant (i : ZMod n) : k17S W := ⟨k17e W i, k17e_mem_k17S i⟩


variable (W) in
abbrev k17R (i : ZMod n) : Type := k17S W ⧸ Ideal.span {1 - idempotentInvariant W i}

theorem letterRing_mk_eq (i : ZMod n) {s s' : k17S W}
    (h : Ideal.Quotient.mk (Ideal.span {1 - idempotentInvariant W i}) s = Ideal.Quotient.mk _ s') :
    k17e W i * (s : W.EE) = k17e W i * s' := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 h)
  have h1 := congrArg (fun z : k17S W => k17e W i * (z : W.EE)) hc
  simp only [idempotentInvariant, AddSubgroupClass.coe_sub, MulMemClass.coe_mul, OneMemClass.coe_one] at h1
  have he := idempotent_mul_self_bis (W := W) i
  linear_combination -h1 - (c : W.EE) * he

theorem letterRing_mk_of_eq (i : ZMod n) {s s' : k17S W}
    (h : k17e W i * (s : W.EE) = k17e W i * s') :
    Ideal.Quotient.mk (Ideal.span {1 - idempotentInvariant W i}) s = Ideal.Quotient.mk _ s' := by
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton']
  refine ⟨s - s', Subtype.ext ?_⟩
  simp only [idempotentInvariant, AddSubgroupClass.coe_sub, MulMemClass.coe_mul, OneMemClass.coe_one]
  linear_combination -h

theorem letterRing_isUnit_of (i : ZMod n) (t : k17S W)
    (h : IsUnit (k17e W i * (t : W.EE) + (1 - k17e W i))) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {1 - idempotentInvariant W i}) t) := by
  obtain ⟨u, hu⟩ := h
  have hz : ∀ δ ∈ W.DelF, W.γE δ (u : W.EE) = u := by
    intro δ hδ
    rw [hu, map_add (f := _), map_mul, map_sub, map_one, idempotent_gamma_invariant, t.2 δ hδ]
  have hw : ∀ δ ∈ W.DelF, W.γE δ (↑u⁻¹ : W.EE) = ↑u⁻¹ := by
    intro δ hδ
    have h1 : W.γE δ (↑u⁻¹ : W.EE) * u = 1 := by
      conv_lhs => rw [← hz δ hδ]
      rw [← map_mul, Units.inv_mul, map_one]
    calc W.γE δ (↑u⁻¹ : W.EE) = W.γE δ (↑u⁻¹ : W.EE) * (u * ↑u⁻¹) := by rw [Units.mul_inv, mul_one]
      _ = ↑u⁻¹ := by rw [← mul_assoc, h1, one_mul]
  let w : k17S W := ⟨↑u⁻¹, hw⟩
  refine isUnit_iff_exists_inv.2 ⟨Ideal.Quotient.mk _ w, ?_⟩
  rw [← map_mul, ← map_one (Ideal.Quotient.mk (Ideal.span {1 - idempotentInvariant W i}))]
  apply letterRing_mk_of_eq
  have h1 : (u : W.EE) * ↑u⁻¹ = 1 := Units.mul_inv u
  rw [hu] at h1
  have he := idempotent_mul_self_bis (W := W) i
  simp only [w, MulMemClass.coe_mul, OneMemClass.coe_one]
  linear_combination (k17e W i) * h1 + ((↑u⁻¹ : W.EE) - (t : W.EE) * ↑u⁻¹) * he

theorem letterRing_isLocalRing (hOloc : IsLocalRing O)
    (hOnil : ∀ c ∈ IsLocalRing.maximalIdeal O, ∃ (N : ℕ) (d : O), c ^ N = ((PD.p : ℕ) : O) * d)
    (i : ZMod n) : IsLocalRing (k17R W i) := by
  have : Nontrivial (k17R W i) := by
    rw [Ideal.Quotient.nontrivial_iff]
    intro htop
    have h1 : (1 : k17S W) ∈ Ideal.span {1 - idempotentInvariant W i} := htop ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h1
    have h2 := congrArg (fun z : k17S W => (z : W.EE) * k17e W i) hc
    simp only [idempotentInvariant, AddSubgroupClass.coe_sub, MulMemClass.coe_mul, OneMemClass.coe_one, one_mul] at h2
    have he := idempotent_mul_self_bis (W := W) i
    have h3 : k17e W i = 0 := by linear_combination -h2 - (c : W.EE) * he
    have h4 : (letE i : LetA O n) = 0 := W.EE_inj (by rw [map_zero]; exact h3)
    have h5 := congrFun h4 i
    simp [letE] at h5
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun r => ?_
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective r
  have he := idempotent_mul_self_bis (W := W) i
  rcases local_corner_unit_dichotomy hOloc hOnil i (k17e W i * (s : W.EE)) (by rw [← mul_assoc, he]) with h | h
  · exact Or.inl (letterRing_isUnit_of i s h)
  · right
    rw [← map_one (Ideal.Quotient.mk (Ideal.span {1 - idempotentInvariant W i})), ← map_sub]
    apply letterRing_isUnit_of i (1 - s)
    convert h using 2
    simp only [AddSubgroupClass.coe_sub, OneMemClass.coe_one]
    ring

def letterRingValueFun (i : ZMod n) (r : k17R W i) : W.EE :=
  k17e W i * ((Ideal.Quotient.mk_surjective r).choose : W.EE)

theorem letterRingValueFun_mk (i : ZMod n) (s : k17S W) :
    letterRingValueFun i (Ideal.Quotient.mk (Ideal.span {1 - idempotentInvariant W i}) s) = k17e W i * s :=
  letterRing_mk_eq i (Ideal.Quotient.mk_surjective _).choose_spec


variable (W) in
def letterRingVal (i : ZMod n) : k17R W i →+ W.EE where
  toFun := letterRingValueFun i
  map_zero' := by
    rw [← map_zero (Ideal.Quotient.mk (Ideal.span {1 - idempotentInvariant W i})), letterRingValueFun_mk]
    simp
  map_add' r r' := by
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective r
    obtain ⟨s', rfl⟩ := Ideal.Quotient.mk_surjective r'
    rw [← map_add (f := _), letterRingValueFun_mk, letterRingValueFun_mk, letterRingValueFun_mk, AddMemClass.coe_add, mul_add]

theorem letterRing_val_mk (i : ZMod n) (s : k17S W) :
    letterRingVal W i (Ideal.Quotient.mk (Ideal.span {1 - idempotentInvariant W i}) s) = k17e W i * s :=
  letterRingValueFun_mk i s

theorem letterRing_val_mul (i : ZMod n) (r r' : k17R W i) :
    letterRingVal W i (r * r') = letterRingVal W i r * letterRingVal W i r' := by
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective r
  obtain ⟨s', rfl⟩ := Ideal.Quotient.mk_surjective r'
  rw [← map_mul, letterRing_val_mk, letterRing_val_mk, letterRing_val_mk, MulMemClass.coe_mul]
  have he := idempotent_mul_self_bis (W := W) i
  linear_combination (-(s : W.EE) * s') * he

theorem letterRing_val_one (i : ZMod n) : letterRingVal W i 1 = k17e W i := by
  rw [← map_one (Ideal.Quotient.mk (Ideal.span {1 - idempotentInvariant W i})), letterRing_val_mk, OneMemClass.coe_one, mul_one]

theorem letterRing_val_mem (i : ZMod n) (r : k17R W i) : letterRingVal W i r ∈ EEl W i := by
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective r
  rw [letterRing_val_mk]
  refine ⟨?_, fun δ hδ => ?_⟩
  · rw [idempotent_smul_eq_mul, ← mul_assoc, idempotent_mul_self_bis]
  · rw [map_mul, idempotent_gamma_invariant, s.2 δ hδ]

theorem letterRing_val_injective (i : ZMod n) : Function.Injective (letterRingVal W i) := by
  intro r r' h
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective r
  obtain ⟨s', rfl⟩ := Ideal.Quotient.mk_surjective r'
  rw [letterRing_val_mk, letterRing_val_mk] at h
  exact letterRing_mk_of_eq i h

theorem letterRing_val_surjective (i : ZMod n) (ε : W.EE) (hε : ε ∈ EEl W i) : ∃ r, letterRingVal W i r = ε := by
  refine ⟨Ideal.Quotient.mk _ ⟨ε, hε.2⟩, ?_⟩
  rw [letterRing_val_mk]
  have h1 := hε.1
  rw [idempotent_smul_eq_mul] at h1
  exact h1

end Formalism.MainNotions.N.Ln03.Pf
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.ExistsBasisOfSurjective
noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Module

private theorem exists_linear_rightInverse_of_surjective {R : Type} [CommRing R] {m₁ m₂ : ℕ}
    (f : (Fin m₁ → R) →ₗ[R] (Fin m₂ → R)) (hf : Function.Surjective f) :
    ∃ s : (Fin m₂ → R) →ₗ[R] (Fin m₁ → R), ∀ y, f (s y) = y := by
  refine ⟨(Pi.basisFun R (Fin m₂)).constr R (fun j => (hf (Pi.single j 1)).choose), ?_⟩
  have h : f ∘ₗ (Pi.basisFun R (Fin m₂)).constr R (fun j => (hf (Pi.single j 1)).choose)
      = LinearMap.id := by
    refine (Pi.basisFun R (Fin m₂)).ext fun j => ?_
    rw [LinearMap.comp_apply, Basis.constr_basis, LinearMap.id_apply, Pi.basisFun_apply]
    exact (hf (Pi.single j 1)).choose_spec
  intro y
  exact LinearMap.congr_fun h y

theorem exists_basis_of_surjective {R : Type} [CommRing R] [IsLocalRing R] {m₁ m₂ : ℕ}
    (f : (Fin m₁ → R) →ₗ[R] (Fin m₂ → R)) (hf : Function.Surjective f) :
    ∃ B : Module.Basis (Fin m₂ ⊕ Fin (m₁ - m₂)) R (Fin m₁ → R),
      (∀ j, f (B (Sum.inl j)) = Pi.single j 1) ∧ ∀ j, f (B (Sum.inr j)) = 0 := by
  obtain ⟨s, hs⟩ := exists_linear_rightInverse_of_surjective f hf
  have hfk : ∀ k : LinearMap.ker f, f (k : Fin m₁ → R) = 0 := fun k => LinearMap.mem_ker.mp k.2
  let q : (Fin m₁ → R) →ₗ[R] (Fin m₁ → R) := LinearMap.id - s ∘ₗ f
  have hq : ∀ x, q x = x - s (f x) := fun x => by
    first
    | rfl
    | simp [q]
  have hmem : ∀ x, q x ∈ LinearMap.ker f := fun x => by
    rw [hq, LinearMap.mem_ker, map_sub, hs, sub_self]
  let r : (Fin m₁ → R) →ₗ[R] LinearMap.ker f := LinearMap.codRestrict (LinearMap.ker f) q hmem
  have hr : ∀ x, (r x : Fin m₁ → R) = x - s (f x) := fun x => by
    first
    | exact hq x
    | simp [r, hq]
  have hrk : ∀ k : LinearMap.ker f, r k = k := fun k => by
    apply Subtype.ext
    rw [hr, hfk k, map_zero, sub_zero]
  have hfg : ∀ p : (Fin m₂ → R) × LinearMap.ker f, f (s p.1 + (p.2 : Fin m₁ → R)) = p.1 :=
    fun p => by rw [map_add (f := _), hs, hfk, add_zero]
  let g : (Fin m₂ → R) × LinearMap.ker f →ₗ[R] (Fin m₁ → R) :=
    LinearMap.coprod s (LinearMap.ker f).subtype
  let h : (Fin m₁ → R) →ₗ[R] (Fin m₂ → R) × LinearMap.ker f := LinearMap.prod f r
  have hg : ∀ p, g p = s p.1 + (p.2 : Fin m₁ → R) := fun p => by
    first
    | rfl
    | simp [g]
  have hh : ∀ x, h x = (f x, r x) := fun x => by
    first
    | rfl
    | simp [h]
  have h₁ : g ∘ₗ h = LinearMap.id := LinearMap.ext fun x => by
    rw [LinearMap.comp_apply, hh, hg, LinearMap.id_apply]
    show s (f x) + (r x : Fin m₁ → R) = x
    rw [hr]
    abel
  have h₂ : h ∘ₗ g = LinearMap.id := LinearMap.ext fun p => by
    rw [LinearMap.comp_apply, hg, hh, LinearMap.id_apply, hfg p]
    refine Prod.ext rfl (Subtype.ext ?_)
    show (r (s p.1 + (p.2 : Fin m₁ → R)) : Fin m₁ → R) = p.2
    rw [hr, hfg p]
    abel
  let e : ((Fin m₂ → R) × LinearMap.ker f) ≃ₗ[R] (Fin m₁ → R) := LinearEquiv.ofLinear g h h₁ h₂
  have he : ∀ p, f (e p) = p.1 := fun p => by
    show f (g p) = p.1
    rw [hg, hfg p]
  have hproj : Module.Projective R (LinearMap.ker f) :=
    Module.Projective.of_split (LinearMap.ker f).subtype r (LinearMap.ext fun k => by
      rw [LinearMap.comp_apply, Submodule.subtype_apply, hrk, LinearMap.id_apply])
  have hfin : Module.Finite R (LinearMap.ker f) :=
    Module.Finite.of_surjective r (fun k => ⟨k, hrk k⟩)
  have hfree : Module.Free R (LinearMap.ker f) := by
    first
    | exact Module.free_of_flat_of_isLocalRing
    | exact Module.free_of_projective_of_isLocalRing
    | infer_instance
  let bk := Module.Free.chooseBasis R (LinearMap.ker f)
  let bp := (Pi.basisFun R (Fin m₂)).prod bk
  let b := bp.map e
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex R (LinearMap.ker f)) = m₁ - m₂ := by
    have h1 := Module.finrank_eq_card_basis b
    rw [Module.finrank_fin_fun, Fintype.card_sum, Fintype.card_fin] at h1
    omega
  have hb : ∀ i, f (b i) = (bp i).1 := fun i => by
    rw [Basis.map_apply, he]
  refine ⟨b.reindex (Equiv.sumCongr (Equiv.refl _) (Fintype.equivFinOfCardEq hcard)),
    fun j => ?_, fun j => ?_⟩
  · rw [Basis.reindex_apply, hb]
    first
    | simp [bp, Basis.prod_apply]
    | simp [bp]
  · rw [Basis.reindex_apply, hb]
    first
    | simp [bp, Basis.prod_apply]
    | simp [bp]

end Formalism.MainNotions.N.Ln03.Pf
end
end

noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G Formalism.MainNotions.N.Ln03

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    [Fintype (K →ₐ[Qp] LL)]

variable {T : LocLat G Qp LL O} {r : ℕ}

theorem exists_EE_basis_of_lattice (hcr : IsCrys PD T.ρ) (b : Fin r → W.DD T) (hbN : ∀ j, b j ∈ W.N T)
    (huniq : ∀ x ∈ W.N T, ∃! a : Fin r → LetA O n, x = ∑ j, a j • b j) :
    ∃ B : Module.Basis (Fin r) W.EE (W.DD T), ∀ j, B j = b j := by
  let v : Fin r → W.N T := fun j => ⟨b j, hbN j⟩
  have hv : ∀ a : Fin r → LetA O n, ((∑ j, a j • v j : W.N T) : W.DD T) = ∑ j, a j • b j := by
    intro a
    simp [v]
  have hli : LinearIndependent (LetA O n) v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have h0 : (0 : W.DD T) = ∑ j, g j • b j := by rw [← hv, hg]; rfl
    obtain ⟨a, -, ha⟩ := huniq 0 (W.N T).zero_mem
    have e1 := ha g h0
    have e2 := ha 0 (by simp)
    exact congrFun (e1.trans e2.symm) j
  have hsp : ⊤ ≤ Submodule.span (LetA O n) (Set.range v) := by
    rintro ⟨x, hx⟩ -
    obtain ⟨a, ha, -⟩ := huniq x hx
    have hx' : (⟨x, hx⟩ : W.N T) = ∑ j, a j • v j := Subtype.ext (by rw [hv]; exact ha)
    rw [hx']
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  refine ⟨(W.N_base T hcr).basis (Module.Basis.mk hli hsp), fun j => ?_⟩
  rw [IsBaseChange.basis_apply, Module.Basis.mk_apply]
  rfl

variable (B : Module.Basis (Fin r) W.EE (W.DD T)) (hB : ∀ j, ∀ δ ∈ W.DelF, W.γD T δ (B j) = B j)

include hB in
theorem basis_repr_gamma (x : W.DD T) (δ : W.Gam) (hδ : δ ∈ W.DelF) (j : Fin r) :
    B.repr (W.γD T δ x) j = W.γE δ (B.repr x j) := by
  have h1 : W.γD T δ x = ∑ j, W.γE δ (B.repr x j) • B j := by
    conv_lhs => rw [← B.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [W.γD_smul, hB _ δ hδ]
  rw [h1, Module.Basis.repr_sum_self]

theorem basis_repr_idempotent_smul (x : W.DD T) (i : ZMod n) (j : Fin r) :
    B.repr ((letE i : LetA O n) • x) j = (letE i : LetA O n) • B.repr x j := by
  have h1 : (letE i : LetA O n) • x = ∑ j, ((letE i : LetA O n) • B.repr x j) • B j := by
    conv_lhs => rw [← B.sum_repr x]
    rw [Finset.smul_sum]
    simp only [smul_assoc]
  rw [h1, Module.Basis.repr_sum_self]


include hB in
theorem basis_repr_mem_letter (i : ZMod n) (x : W.DD T) (hx : x ∈ DDl W T i) (j : Fin r) :
    B.repr x j ∈ EEl W i := by
  refine ⟨?_, fun δ hδ => ?_⟩
  · rw [← basis_repr_idempotent_smul, hx.1]
  · rw [← basis_repr_gamma B hB x δ hδ, hx.2 δ hδ]


include hB in
theorem basis_combination_mem_invariants (i : ZMod n) (d : Fin r → W.EE) (hd : ∀ j, d j ∈ EEl W i) :
    ∑ j, d j • B j ∈ DDl W T i := by
  refine ⟨?_, fun δ hδ => ?_⟩
  · rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← smul_assoc, (hd j).1]
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [W.γD_smul, hB j δ hδ, (hd j).2 δ hδ]

theorem basis_coefficients_unique {c c' : Fin r → W.EE} (h : ∑ j, c j • B j = ∑ j, c' j • B j) : c = c' := by
  have h1 := Fintype.linearIndependent_iff.1 B.linearIndependent (c - c') (by
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, h, sub_self])
  funext j
  exact sub_eq_zero.1 (h1 j)

theorem exists_preimage_letter_ring (i : ZMod n) {κ : Type} (c : κ → W.EE) (hc : ∀ t, c t ∈ EEl W i) :
    ∃ a : κ → k17R W i, ∀ t, letterRingVal W i (a t) = c t :=
  ⟨fun t => (letterRing_val_surjective i (c t) (hc t)).choose, fun t => (letterRing_val_surjective i (c t) (hc t)).choose_spec⟩

theorem letter_coefficients_mul_mem {i : ZMod n} {a b : W.EE} (ha : a ∈ EEl W i) (hb : b ∈ EEl W i) :
    a * b ∈ EEl W i := by
  refine ⟨?_, fun δ hδ => ?_⟩
  · rw [← smul_mul_assoc, ha.1]
  · rw [map_mul, ha.2 δ hδ, hb.2 δ hδ]

theorem letterRing_mul_idempotent (i : ZMod n) (r : k17R W i) : letterRingVal W i r * k17e W i = letterRingVal W i r := by
  have h := (letterRing_val_mem i r).1
  rw [idempotent_smul_eq_mul] at h
  rw [mul_comm, h]

theorem letterRing_sum_mul {i : ZMod n} {ι : Type} [Fintype ι] (a : ι → k17R W i)
    (C : ι → Fin r → k17R W i) (l : Fin r) :
    ∑ t, letterRingVal W i (a t) * letterRingVal W i (C t l) = letterRingVal W i ((∑ t, a t • C t) l) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.sum_apply, map_sum]
  simp only [Pi.smul_apply, smul_eq_mul, letterRing_val_mul]


include hB in
theorem letter_invariants_basis (i : ZMod n) {ι : Type} [Fintype ι]
    (C : Module.Basis ι (k17R W i) (Fin r → k17R W i)) :
    LBasis W T i (fun t => ∑ l, letterRingVal W i (C t l) • B l) := by
  have hlc : ∀ c : ι → W.EE, lc (fun t => ∑ l, letterRingVal W i (C t l) • B l) c =
      ∑ l, (∑ t, c t * letterRingVal W i (C t l)) • B l := by
    intro c
    simp only [lc, Finset.smul_sum, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  refine ⟨fun c hc => ?_, fun c c' hc hc' h => ?_, fun x hx => ?_⟩
  · rw [hlc]
    exact basis_combination_mem_invariants B hB i _ fun l =>
      AddSubgroup.sum_mem _ fun t _ => letter_coefficients_mul_mem (hc t) (letterRing_val_mem i _)
  · obtain ⟨a, ha⟩ := exists_preimage_letter_ring i c hc
    obtain ⟨a', ha'⟩ := exists_preimage_letter_ring i c' hc'
    rw [hlc, hlc] at h
    have h1 := basis_coefficients_unique B h
    have h2 : ∑ t, a t • C t = ∑ t, a' t • C t := by
      funext l
      apply letterRing_val_injective i
      rw [← letterRing_sum_mul, ← letterRing_sum_mul]
      simp only [ha, ha']
      exact congrFun h1 l
    have h3 : a = a' := by
      have h4 := Fintype.linearIndependent_iff.1 C.linearIndependent (a - a') (by
        simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, h2, sub_self])
      funext t
      exact sub_eq_zero.1 (h4 t)
    funext t
    rw [← ha, ← ha', h3]
  · obtain ⟨u, hu⟩ := exists_preimage_letter_ring i (fun l => B.repr x l) (basis_repr_mem_letter B hB i x hx)
    refine ⟨fun t => letterRingVal W i (C.repr u t), fun t => letterRing_val_mem i _, ?_⟩
    rw [hlc]
    conv_rhs => rw [← B.sum_repr x]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [letterRing_sum_mul, C.sum_repr u, hu]

def k17f {i : ZMod n} {m₁ m₂ : ℕ} (μ : Fin m₁ → Fin m₂ → k17R W i) :
    (Fin m₁ → k17R W i) →ₗ[k17R W i] (Fin m₂ → k17R W i) where
  toFun u k := ∑ l, u l * μ l k
  map_add' u u' := by
    funext k
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' c u := by
    funext k
    simp [Finset.mul_sum, mul_assoc]

end Formalism.MainNotions.N.Ln03.Pf
end
end

noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G Formalism.MainNotions.N.Ln03

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    [Fintype (K →ₐ[Qp] LL)]

theorem finiteDelta_mul_mem {a b : W.Gam} (ha : a ∈ W.DelF) (hb : b ∈ W.DelF) : a * b ∈ W.DelF := by
  obtain ⟨k, hk, hak⟩ := (W.DelF_def a).1 ha
  obtain ⟨k', hk', hbk⟩ := (W.DelF_def b).1 hb
  refine (W.DelF_def _).2 ⟨k * k', Nat.mul_pos hk hk', ?_⟩
  rw [mul_pow, pow_mul, hak, one_pow, one_mul, mul_comm k k', pow_mul, hbk, one_pow]

theorem finiteDelta_inv_mem {a : W.Gam} (ha : a ∈ W.DelF) : a⁻¹ ∈ W.DelF := by
  obtain ⟨k, hk, hak⟩ := (W.DelF_def a).1 ha
  exact (W.DelF_def _).2 ⟨k, hk, by rw [inv_pow, hak, inv_one]⟩

theorem exists_basis_Delta_fixed_mem_N (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hs : W.s = 1) (hp2 : PD.p ≠ 2)
    (T : LocLat G Qp LL O) (hcr : IsCrys PD T.ρ) :
    ∃ (r : ℕ) (B : Module.Basis (Fin r) W.EE (W.DD T)),
      (∀ j, ∀ δ ∈ W.DelF, W.γD T δ (B j) = B j) ∧ ∀ j, B j ∈ W.N T := by
  obtain ⟨-, ⟨π', E, -, ⟨r, b, hbΔ, huniq, -⟩, -⟩, -⟩ := hP9 T hcr hs hp2
  have hb : ∀ j, b j ∈ W.N T ∧ ∀ δ ∈ W.DelF, W.γD T δ (b j) = b j := fun j =>
    (show b j ∈ W.N T ∧ ∀ δ ∈ W.DelF, W.γD T δ (b j) = b j from hbΔ j)
  obtain ⟨B, hB⟩ := exists_EE_basis_of_lattice hcr b (fun j => (hb j).1) huniq
  exact ⟨r, B, fun j δ hδ => by rw [hB]; exact (hb j).2 δ hδ, fun j => by rw [hB]; exact (hb j).1⟩

theorem isUnit_card_finiteDelta (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hs : W.s = 1) (hp2 : PD.p ≠ 2)
    (T : LocLat G Qp LL O) (hcr : IsCrys PD T.ρ) : IsUnit ((W.DelF.card : ℕ) : W.EE) := by
  have hcard := (hP9 T hcr hs hp2).1
  have h1 : (1 : W.Gam) ∈ W.DelF := (W.DelF_def 1).2 ⟨1, one_pos, one_pow 1⟩
  have hpos : 0 < W.DelF.card := Finset.card_pos.2 ⟨1, h1⟩
  have hp := PD.hp
  have hlt : W.DelF.card < PD.p := by
    rw [hcard]
    exact lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.sub_lt hp.pos one_pos)
  have hcop : Nat.Coprime W.DelF.card PD.p := Nat.coprime_comm.1
    ((Nat.Prime.coprime_iff_not_dvd hp).2 fun hd => absurd (Nat.le_of_dvd hpos hd) (not_le.2 hlt))
  have hb := Nat.gcd_eq_gcd_ab W.DelF.card PD.p
  rw [hcop.gcd_eq_one] at hb
  have hb' : ((W.DelF.card : ℕ) : W.EE) * (Nat.gcdA W.DelF.card PD.p : W.EE) =
      1 - ((PD.p : ℕ) : W.EE) * (Nat.gcdB W.DelF.card PD.p : W.EE) := by
    have h2 := congrArg (Int.cast : ℤ → W.EE) hb
    push_cast at h2
    linear_combination -h2
  have hu : IsUnit (1 - ((PD.p : ℕ) : W.EE) * (Nat.gcdB W.DelF.card PD.p : W.EE)) := by
    have hc := W.EE_complete
    apply Ideal.isUnit_of_sub_one_mem_jacobson_bot
    apply IsAdicComplete.le_jacobson_bot (I := Ideal.span {((PD.p : ℕ) : W.EE)})
    rw [sub_sub_cancel_left]
    exact (Ideal.neg_mem_iff _).2 (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))
  rw [← hb'] at hu
  exact isUnit_of_mul_isUnit_left hu

theorem exists_lift_of_onto (hs : W.s = 1) (hLem3 : Formalism.MainNotions.DeltaInvariantLattices.WachLatticeLengthLemma W)
    (hJ : ∀ T : LocLat G Qp LL O, CrysLat PD T → ∃ M h : ZMod n → ℕ, Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T M h)
    {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) (hc₁ : CrysLat PD T₁) (hc₂ : CrysLat PD T₂)
    (hon : F.Onto) (y : W.DD T₂) (hy : y ∈ W.N T₂) : ∃ w : W.DD T₁, W.map F w = y := by
  obtain ⟨M, h, hJ'⟩ := hJ T₁ hc₁
  have hL := (hLem3 T₁ T₂ F M h hc₁.2.2.2 hc₂.2.2.2 hon hJ').1
  have hX : W.X = letπ := by
    show (W.φA ^ (W.s - 1)) letπ = letπ
    rw [hs]
    rfl
  have hunit : IsUnit (algebraMap (LetA O n) W.EE (W.X ^ (⨆ j, (M j + h j)))) := by
    rw [hX, map_pow]
    exact W.EE_π.pow _
  have hi : ∀ i : ZMod n, ∃ v : W.DD T₁, W.map F v = (letE i : LetA O n) • y := by
    intro i
    obtain ⟨z, -, hz⟩ := hL i _ (Submodule.mem_map_of_mem (f := (letE i : LetA O n) • LinearMap.id) hy)
    refine ⟨(↑hunit.unit⁻¹ : W.EE) • z, ?_⟩
    have hz' : W.map F z = algebraMap (LetA O n) W.EE (W.X ^ (⨆ j, (M j + h j))) •
        (letE i : LetA O n) • y := by
      rw [algebraMap_smul]
      exact hz
    rw [map_smul, hz', smul_smul, hunit.val_inv_mul, one_smul]
  choose v hv using hi
  refine ⟨∑ i, v i, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [hv]
  rw [← Finset.sum_smul, sum_letE, one_smul]

theorem exists_invariant_lift_average (hcu : IsUnit ((W.DelF.card : ℕ) : W.EE)) {T₁ T₂ : LocLat G Qp LL O}
    (F : LatHom T₁.L T₂.L) (w : W.DD T₁) (y : W.DD T₂)
    (hy : ∀ δ ∈ W.DelF, W.γD T₂ δ y = y) (hw : W.map F w = y) :
    ∃ w' : W.DD T₁, (∀ δ ∈ W.DelF, W.γD T₁ δ w' = w') ∧ W.map F w' = y := by
  refine ⟨(↑hcu.unit⁻¹ : W.EE) • ∑ δ ∈ W.DelF, W.γD T₁ δ w, fun δ' hδ' => ?_, ?_⟩
  · have hγc : W.γE δ' ((W.DelF.card : ℕ) : W.EE) = ((W.DelF.card : ℕ) : W.EE) := map_natCast _ _
    have h1 : W.γE δ' (↑hcu.unit⁻¹ : W.EE) * ↑hcu.unit = 1 := by
      rw [IsUnit.unit_spec]
      calc W.γE δ' (↑hcu.unit⁻¹ : W.EE) * ((W.DelF.card : ℕ) : W.EE)
          = W.γE δ' (↑hcu.unit⁻¹ : W.EE) * W.γE δ' ((W.DelF.card : ℕ) : W.EE) := by rw [hγc]
        _ = W.γE δ' ((↑hcu.unit⁻¹ : W.EE) * ((W.DelF.card : ℕ) : W.EE)) := (map_mul _ _ _).symm
        _ = 1 := by rw [hcu.val_inv_mul, map_one]
    have hinv : W.γE δ' (↑hcu.unit⁻¹ : W.EE) = ↑hcu.unit⁻¹ := by
      calc W.γE δ' (↑hcu.unit⁻¹ : W.EE)
          = W.γE δ' (↑hcu.unit⁻¹ : W.EE) * (↑hcu.unit * ↑hcu.unit⁻¹) := by rw [Units.mul_inv, mul_one]
        _ = ↑hcu.unit⁻¹ := by rw [← mul_assoc, h1, one_mul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [W.γD_smul, hinv, map_sum]
    congr 1
    simp only [← W.γD_mul]
    exact Finset.sum_nbij' (fun δ => δ' * δ) (fun δ => δ'⁻¹ * δ)
      (fun δ hδ => finiteDelta_mul_mem hδ' hδ) (fun δ hδ => finiteDelta_mul_mem (finiteDelta_inv_mem hδ') hδ)
      (fun δ _ => by group) (fun δ _ => by group) (fun δ _ => rfl)
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_smul, map_sum]
    rw [Finset.sum_congr rfl fun δ hδ => by rw [W.map_γ, hw, hy δ hδ]]
    rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul W.EE, smul_smul, hcu.val_inv_mul, one_smul]

end Formalism.MainNotions.N.Ln03.Pf
end
end

noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G Formalism.MainNotions.N.Ln03

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    [Fintype (K →ₐ[Qp] LL)]

theorem unitStep_holds {e : W.DD W.one} (hUnitGen : UnitGen W e) (hCrysOne : IsCrys PD W.one.ρ) :
    UnitStep W e := by
  have hB := unitBasis_of hUnitGen hCrysOne
  have hγ : ∀ g, W.γD W.one g e = e := hUnitGen.2.2.1
  intro i
  refine ⟨?_, ?_, ?_⟩
  · intro c hc
    obtain ⟨hc1, hc2⟩ := hc ()
    simp only [lc, Fintype.sum_unique]
    refine ⟨?_, fun δ hδ => ?_⟩
    · rw [← smul_assoc, hc1]
    · rw [W.γD_smul, hγ, hc2 δ hδ]
  · intro c c' _ _ h
    simp only [lc, Fintype.sum_unique] at h
    funext u
    obtain ⟨ε, _, huniq⟩ := hB (c () • e)
    exact (huniq (c u) rfl).trans (huniq (c' u) h).symm
  · intro x hx
    obtain ⟨ε, hε, huniq⟩ := hB x
    obtain ⟨h1, h2⟩ := hx
    refine ⟨fun _ => ε, fun _ => ⟨?_, fun δ hδ => ?_⟩, ?_⟩
    · have hx' : x = ((letE i : LetA O n) • ε) • e := by
        rw [smul_assoc, ← hε, h1]
      exact huniq _ hx'
    · have hx' : x = W.γE δ ε • e := by
        conv_lhs => rw [← h2 δ hδ, hε]
        rw [W.γD_smul, hγ]
      exact huniq _ hx'
    · simp only [lc, Fintype.sum_unique]
      exact hε.symm

theorem splitStep_holds (hOloc : IsLocalRing O)
    (hOnil : ∀ c ∈ IsLocalRing.maximalIdeal O, ∃ (N : ℕ) (d : O), c ^ N = ((PD.p : ℕ) : O) * d)
    (hs : W.s = 1) (hp2 : PD.p ≠ 2) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hLem3 : Formalism.MainNotions.DeltaInvariantLattices.WachLatticeLengthLemma W)
    (hJ : ∀ T : LocLat G Qp LL O, CrysLat PD T → ∃ M h : ZMod n → ℕ, Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T M h) :
    SplitStep W := by
  intro T₁ T₂ F hc₁ hc₂ hon
  obtain ⟨m₁, B₁, hB₁, -⟩ := exists_basis_Delta_fixed_mem_N hP9 hs hp2 T₁ hc₁.2.2.2
  obtain ⟨m₂, B₂, hB₂, hB₂N⟩ := exists_basis_Delta_fixed_mem_N hP9 hs hp2 T₂ hc₂.2.2.2
  have hcu := isUnit_card_finiteDelta hP9 hs hp2 T₁ hc₁.2.2.2
  have hlift : ∀ k, ∃ w : W.DD T₁, (∀ δ ∈ W.DelF, W.γD T₁ δ w = w) ∧ W.map F w = B₂ k := by
    intro k
    obtain ⟨w₀, hw₀⟩ := exists_lift_of_onto hs hLem3 hJ F hc₁ hc₂ hon (B₂ k) (hB₂N k)
    exact exists_invariant_lift_average hcu F w₀ (B₂ k) (hB₂ k) hw₀
  choose w hwΔ hwF using hlift
  refine ⟨m₂, m₁ - m₂, fun i => ?_⟩
  have hloc := letterRing_isLocalRing (W := W) hOloc hOnil i
  set M : Fin m₁ → Fin m₂ → W.EE := fun l k => B₂.repr (W.map F (B₁ l)) k with hMdef
  have hMγ : ∀ l k, ∀ δ ∈ W.DelF, W.γE δ (M l k) = M l k := by
    intro l k δ hδ
    rw [hMdef, ← basis_repr_gamma B₂ hB₂ _ δ hδ, ← W.map_γ, hB₁ l δ hδ]
  have hM : ∀ l k, k17e W i * M l k ∈ EEl W i := by
    intro l k
    refine ⟨?_, fun δ hδ => ?_⟩
    · rw [idempotent_smul_eq_mul, ← mul_assoc, idempotent_mul_self_bis]
    · rw [map_mul, idempotent_gamma_invariant, hMγ l k δ hδ]
  choose μ hμ using fun l k => letterRing_val_surjective i _ (hM l k)
  have hcoef : ∀ (u : Fin m₁ → k17R W i) (k : Fin m₂),
      letterRingVal W i (k17f μ u k) = ∑ l, letterRingVal W i (u l) * M l k := by
    intro u k
    change letterRingVal W i (∑ l, u l * μ l k) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [letterRing_val_mul, hμ, ← mul_assoc, letterRing_mul_idempotent]
  have hmap : ∀ u : Fin m₁ → k17R W i, W.map F (∑ l, letterRingVal W i (u l) • B₁ l) =
      ∑ k, letterRingVal W i (k17f μ u k) • B₂ k := by
    intro u
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hcoef, Finset.sum_smul, map_sum, map_smul]
    have h1 : ∀ l, W.map F (B₁ l) = ∑ k, M l k • B₂ k := fun l => (B₂.sum_repr _).symm
    simp only [h1, Finset.smul_sum, smul_smul]
    exact Finset.sum_comm
  have hstd : ∀ k, ∃ u : Fin m₁ → k17R W i, k17f μ u = Pi.single k 1 := by
    intro k
    have hd : ∀ l, k17e W i * B₁.repr (w k) l ∈ EEl W i := by
      intro l
      refine ⟨?_, fun δ hδ => ?_⟩
      · rw [idempotent_smul_eq_mul, ← mul_assoc, idempotent_mul_self_bis]
      · rw [map_mul, idempotent_gamma_invariant, ← basis_repr_gamma B₁ hB₁ _ δ hδ, hwΔ k δ hδ]
    obtain ⟨u, hu⟩ := exists_preimage_letter_ring i _ hd
    refine ⟨u, funext fun k' => letterRing_val_injective i ?_⟩
    have h1 : ∑ l, letterRingVal W i (u l) • B₁ l = k17e W i • w k := by
      simp only [hu, ← smul_smul, ← Finset.smul_sum, B₁.sum_repr]
    have h2 := hmap u
    rw [h1, map_smul, hwF] at h2
    have h3 : k17e W i • B₂ k = ∑ k', letterRingVal W i ((Pi.single k 1 : Fin m₂ → k17R W i) k') • B₂ k' := by
      simp only [Pi.single_apply]
      simp only [apply_ite (letterRingVal W i), map_zero, letterRing_val_one, ite_smul, zero_smul]
      rw [Finset.sum_ite_eq']
      simp
    rw [h3] at h2
    exact congrFun (basis_coefficients_unique B₂ h2.symm) k'
  choose ν hν using hstd
  have hsurj : Function.Surjective (k17f μ) := by
    intro y
    refine ⟨∑ k, y k • ν k, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_smul, hν]
    funext k'
    simp [Finset.sum_apply, Pi.single_apply]
  obtain ⟨C, hCl, hCr⟩ := exists_basis_of_surjective (k17f μ) hsurj
  refine ⟨fun t => ∑ l, letterRingVal W i (C t l) • B₁ l,
    fun j => ∑ l, letterRingVal W i (Pi.basisFun (k17R W i) (Fin m₂) j l) • B₂ l,
    letter_invariants_basis B₁ hB₁ i C, letter_invariants_basis B₂ hB₂ i (Pi.basisFun _ _), fun j => ?_, fun j => ?_⟩
  · rw [hmap, hCl]
    simp only [Pi.basisFun_apply]
  · rw [hmap, hCr]
    simp

end Formalism.MainNotions.N.Ln03.Pf
