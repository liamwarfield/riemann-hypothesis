module

public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CayleyForm
public import Lemmata.GeneralBFactLeftVersion.Imports
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.IntegralEnvelopingPreservesLattice

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.RootWeights.LagrangeProjectorPreservesStable
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem mem_weightSpace_iff_diagonal (E : GLOps n K V) (mu : Fin n → ℤ) (x : V) :
    x ∈ weightSp E mu ↔ ∀ a, E a a x = (mu a : K) • x := by
  simp [weightSp, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]

theorem weightSpace_disjoint [CharZero K] (E : GLOps n K V) {mu ka : Fin n → ℤ} (h : mu ≠ ka) {x : V}
    (h1 : x ∈ weightSp E mu) (h2 : x ∈ weightSp E ka) : x = 0 := by
  obtain ⟨a, ha⟩ := Function.ne_iff.1 h
  have e1 := (mem_weightSpace_iff_diagonal E mu x).1 h1 a
  have e2 := (mem_weightSpace_iff_diagonal E ka x).1 h2 a
  rw [e1] at e2
  have e3 : ((mu a : K) - (ka a : K)) • x = 0 := by rw [sub_smul, e2, sub_self]
  rcases smul_eq_zero.1 e3 with h0 | h0
  · exact absurd (by exact_mod_cast sub_eq_zero.1 h0) ha
  · exact h0


open Classical in
def lagrangeFactor (E : GLOps n K V) (mu nu : Fin n → ℤ) : Module.End K V :=
  if h : nu = mu then 1 else
    (((mu (Classical.choose (Function.ne_iff.1 h)) : K) - (nu (Classical.choose (Function.ne_iff.1 h)) : K))⁻¹) •
      (E (Classical.choose (Function.ne_iff.1 h)) (Classical.choose (Function.ne_iff.1 h)) -
        (nu (Classical.choose (Function.ne_iff.1 h)) : K) • (1 : Module.End K V))

theorem lagrange_factor_acts_scalar (E : GLOps n K V) (mu nu ka : Fin n → ℤ) {x : V} (hx : x ∈ weightSp E ka) :
    ∃ c : K, lagrangeFactor E mu nu x = c • x := by
  unfold lagrangeFactor
  split_ifs with h
  · exact ⟨1, by simp⟩
  · set a := Classical.choose (Function.ne_iff.1 h)
    refine ⟨((mu a : K) - (nu a : K))⁻¹ * ((ka a : K) - (nu a : K)), ?_⟩
    simp only [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply]
    rw [(mem_weightSpace_iff_diagonal E ka x).1 hx a, ← sub_smul, smul_smul]

theorem lagrange_factor_fixes_weight [CharZero K] (E : GLOps n K V) (mu nu : Fin n → ℤ) {x : V} (hx : x ∈ weightSp E mu) :
    lagrangeFactor E mu nu x = x := by
  unfold lagrangeFactor
  split_ifs with h
  · simp
  · have ha := Classical.choose_spec (Function.ne_iff.1 h)
    set a := Classical.choose (Function.ne_iff.1 h)
    simp only [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply]
    rw [(mem_weightSpace_iff_diagonal E mu x).1 hx a, ← sub_smul, smul_smul, inv_mul_cancel₀, one_smul]
    intro h0
    exact ha (by exact_mod_cast (sub_eq_zero.1 h0).symm)

theorem lagrange_factor_kills_other (E : GLOps n K V) {mu nu : Fin n → ℤ} (h : nu ≠ mu) {x : V} (hx : x ∈ weightSp E nu) :
    lagrangeFactor E mu nu x = 0 := by
  unfold lagrangeFactor
  rw [dite_eq_right h]
  set a := Classical.choose (Function.ne_iff.1 h)
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply]
  rw [(mem_weightSpace_iff_diagonal E nu x).1 hx a, sub_self, smul_zero]

theorem lagrange_factor_preserves_stable (E : GLOps n K V) (mu nu : Fin n → ℤ) (U : Submodule K V)
    (hU : ∀ a, ∀ x ∈ U, E a a x ∈ U) {x : V} (hx : x ∈ U) : lagrangeFactor E mu nu x ∈ U := by
  unfold lagrangeFactor
  split_ifs with h
  · simpa using hx
  · simp only [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply]
    exact U.smul_mem _ (U.sub_mem (hU _ x hx) (U.smul_mem _ hx))

def lagrangeProjector (E : GLOps n K V) (mu : Fin n → ℤ) (L : List (Fin n → ℤ)) : Module.End K V :=
  (L.map fun nu => lagrangeFactor E mu nu).prod

theorem lagrange_projector_acts_scalar (E : GLOps n K V) (mu ka : Fin n → ℤ) (L : List (Fin n → ℤ)) {x : V}
    (hx : x ∈ weightSp E ka) : ∃ c : K, lagrangeProjector E mu L x = c • x := by
  induction L with
  | nil => exact ⟨1, by simp [lagrangeProjector]⟩
  | cons nu L ih =>
    obtain ⟨c, hc⟩ := ih
    obtain ⟨d, hd⟩ := lagrange_factor_acts_scalar E mu nu ka hx
    refine ⟨c * d, ?_⟩
    have : lagrangeProjector E mu (nu :: L) x = lagrangeFactor E mu nu (lagrangeProjector E mu L x) := by
      simp [lagrangeProjector, Module.End.mul_apply]
    rw [this, hc, map_smul, hd, smul_smul]

theorem lagrange_projector_fixes_weight [CharZero K] (E : GLOps n K V) (mu : Fin n → ℤ) (L : List (Fin n → ℤ)) {x : V}
    (hx : x ∈ weightSp E mu) : lagrangeProjector E mu L x = x := by
  induction L with
  | nil => simp [lagrangeProjector]
  | cons nu L ih =>
    have : lagrangeProjector E mu (nu :: L) x = lagrangeFactor E mu nu (lagrangeProjector E mu L x) := by
      simp [lagrangeProjector, Module.End.mul_apply]
    rw [this, ih, lagrange_factor_fixes_weight E mu nu hx]

theorem lagrange_projector_kills_other (E : GLOps n K V) {mu ka : Fin n → ℤ} (h : ka ≠ mu) (L : List (Fin n → ℤ)) (hL : ka ∈ L)
    {x : V} (hx : x ∈ weightSp E ka) : lagrangeProjector E mu L x = 0 := by
  induction L with
  | nil => simp at hL
  | cons nu L ih =>
    have e : lagrangeProjector E mu (nu :: L) x = lagrangeFactor E mu nu (lagrangeProjector E mu L x) := by
      simp [lagrangeProjector, Module.End.mul_apply]
    rw [e]
    rcases List.mem_cons.1 hL with rfl | hL'
    · obtain ⟨c, hc⟩ := lagrange_projector_acts_scalar E mu ka L hx
      rw [hc, map_smul, lagrange_factor_kills_other E h hx, smul_zero]
    · rw [ih hL', map_zero]

theorem lagrange_projector_preserves_stable (E : GLOps n K V) (mu : Fin n → ℤ) (L : List (Fin n → ℤ)) (U : Submodule K V)
    (hU : ∀ a, ∀ x ∈ U, E a a x ∈ U) {x : V} (hx : x ∈ U) : lagrangeProjector E mu L x ∈ U := by
  induction L with
  | nil => simpa [lagrangeProjector] using hx
  | cons nu L ih =>
    have e : lagrangeProjector E mu (nu :: L) x = lagrangeFactor E mu nu (lagrangeProjector E mu L x) := by
      simp [lagrangeProjector, Module.End.mul_apply]
    rw [e]
    exact lagrange_factor_preserves_stable E mu nu U hU ih

end

section

variable {n : ℕ} {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]

theorem sum_lagrange_projectors_eq_self (E : GLOps n K V) (t : Finset (Fin n → ℤ))
    (ht : (⊤ : Submodule K V) ≤ ⨆ mu ∈ t, weightSp E mu) (x : V) :
    ∑ mu ∈ t, lagrangeProjector E mu t.toList x = x := by
  have hx : x ∈ ⨆ mu ∈ t, weightSp E mu := ht Submodule.mem_top
  refine Submodule.iSup_induction (fun mu => ⨆ (_ : mu ∈ t), weightSp E mu)
    (motive := fun x => ∑ mu ∈ t, lagrangeProjector E mu t.toList x = x) hx ?_ ?_ ?_
  · intro ka y hy
    by_cases hk : ka ∈ t
    · have hy' : y ∈ weightSp E ka := by simpa [hk] using hy
      rw [Finset.sum_eq_single ka]
      · exact lagrange_projector_fixes_weight E ka _ hy'
      · intro mu _ hne
        exact lagrange_projector_kills_other E (Ne.symm hne) _ (by simpa using hk) hy'
      · intro h; exact absurd hk h
    · have : y = 0 := by simpa [hk] using hy
      simp [this]
  · simp
  · intro y z hy hz
    simp only [map_add (f := _), Finset.sum_add_distrib, hy, hz]

theorem lagrange_projector_mem_weightSpace (E : GLOps n K V) (t : Finset (Fin n → ℤ))
    (ht : (⊤ : Submodule K V) ≤ ⨆ mu ∈ t, weightSp E mu) (mu : Fin n → ℤ) (x : V) :
    lagrangeProjector E mu t.toList x ∈ weightSp E mu := by
  have hx : x ∈ ⨆ mu ∈ t, weightSp E mu := ht Submodule.mem_top
  refine Submodule.iSup_induction (fun mu => ⨆ (_ : mu ∈ t), weightSp E mu)
    (motive := fun x => lagrangeProjector E mu t.toList x ∈ weightSp E mu) hx ?_ ?_ ?_
  · intro ka y hy
    by_cases hk : ka ∈ t
    · have hy' : y ∈ weightSp E ka := by simpa [hk] using hy
      by_cases hkm : ka = mu
      · subst hkm
        rw [lagrange_projector_fixes_weight E ka _ hy']; exact hy'
      · rw [lagrange_projector_kills_other E hkm _ (by simpa using hk) hy']; exact Submodule.zero_mem _
    · have : y = 0 := by simpa [hk] using hy
      simp [this]
  · simp
  · intro y z hy hz
    rw [map_add (f := _)]; exact Submodule.add_mem _ hy hz

theorem nonzero_weight_mem_support (E : GLOps n K V) (t : Finset (Fin n → ℤ))
    (ht : (⊤ : Submodule K V) ≤ ⨆ mu ∈ t, weightSp E mu) {ka : Fin n → ℤ} {y : V}
    (hy : y ∈ weightSp E ka) (h0 : y ≠ 0) : ka ∈ t := by
  by_contra hk
  apply h0
  rw [← sum_lagrange_projectors_eq_self E t ht y]
  apply Finset.sum_eq_zero
  intro mu hmu
  obtain ⟨c, hc⟩ := lagrange_projector_acts_scalar E mu ka t.toList hy
  have h1 := lagrange_projector_mem_weightSpace E t ht mu y
  have h2 : lagrangeProjector E mu t.toList y ∈ weightSp E ka := by rw [hc]; exact Submodule.smul_mem _ _ hy
  exact weightSpace_disjoint E (by rintro rfl; exact hk hmu) h1 h2

theorem stable_subspace_has_weight_vector (E : GLOps n K V) (t : Finset (Fin n → ℤ))
    (ht : (⊤ : Submodule K V) ≤ ⨆ mu ∈ t, weightSp E mu) (U : Submodule K V)
    (hU : ∀ a, ∀ x ∈ U, E a a x ∈ U) (hne : U ≠ ⊥) :
    ∃ mu ∈ t, ∃ x ∈ U, x ≠ 0 ∧ x ∈ weightSp E mu := by
  obtain ⟨x, hx, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  by_contra hcon
  push Not at hcon
  apply h0
  rw [← sum_lagrange_projectors_eq_self E t ht x]
  apply Finset.sum_eq_zero
  intro mu hmu
  by_contra hP
  exact hcon mu hmu _ (lagrange_projector_preserves_stable E mu _ U hU hx) hP (lagrange_projector_mem_weightSpace E t ht mu x)

omit [CharZero K] in
theorem raising_shifts_weight_by_root (E : GLOps n K V)
    (hrel : ∀ a b c d, E a b * E c d - E c d * E a b = (if b = c then E a d else 0) - (if d = a then E c b else 0))
    {a b : Fin n} (hab : a ≠ b) {mu : Fin n → ℤ} {x : V} (hx : x ∈ weightSp E mu) :
    E a b x ∈ weightSp E (mu + rootW a b) := by
  rw [mem_weightSpace_iff_diagonal] at hx ⊢
  intro c
  have h := congrArg (fun f : Module.End K V => f x) (hrel c c a b)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  rw [hx c, map_smul, sub_eq_iff_eq_add] at h
  rw [h]
  by_cases hca : c = a
  · subst hca
    have hbc : ¬ b = c := fun h => hab h.symm
    simp only [if_true, if_neg hbc, LinearMap.zero_apply, sub_zero, rootW, Pi.add_apply, Pi.sub_apply,
      Pi.single_eq_same, Pi.single_eq_of_ne hab]
    push_cast
    rw [add_smul, one_smul, add_comm]
  · by_cases hcb : c = b
    · subst hcb
      simp only [if_neg hca, if_true, LinearMap.zero_apply, zero_sub, rootW, Pi.add_apply, Pi.sub_apply,
        Pi.single_eq_same, Pi.single_eq_of_ne hca]
      push_cast
      rw [add_smul, neg_smul, one_smul, add_comm]
    · have hbc : ¬ b = c := fun h => hcb h.symm
      simp only [if_neg hca, if_neg hbc, LinearMap.zero_apply, sub_zero, rootW, Pi.add_apply, Pi.sub_apply,
        Pi.single_eq_of_ne hca, Pi.single_eq_of_ne hcb, zero_add, add_zero]

def weightHeight (mu : Fin n → ℤ) : ℤ := ∑ c : Fin n, ((c : ℕ) : ℤ) * mu c

theorem weightHeight_add_root (mu : Fin n → ℤ) (a b : Fin n) :
    weightHeight (mu + rootW a b) = weightHeight mu + ((a : ℕ) : ℤ) - ((b : ℕ) : ℤ) := by
  simp [weightHeight, rootW, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, Pi.single_apply]
  ring

theorem exists_highest_weight_vector (E : GLOps n K V)
    (hrel : ∀ a b c d, E a b * E c d - E c d * E a b = (if b = c then E a d else 0) - (if d = a then E c b else 0))
    (t : Finset (Fin n → ℤ)) (ht : (⊤ : Submodule K V) ≤ ⨆ mu ∈ t, weightSp E mu) (U : Submodule K V)
    (hU : ∀ a b, ∀ x ∈ U, E a b x ∈ U) (hne : U ≠ ⊥) : ∃ mu, ∃ x ∈ U, IsHWV E mu x := by
  classical
  have hT : (t.filter (fun mu => ∃ x ∈ U, x ≠ 0 ∧ x ∈ weightSp E mu)).Nonempty := by
    obtain ⟨mu, hmu, h⟩ := stable_subspace_has_weight_vector E t ht U (fun a => hU a a) hne
    exact ⟨mu, Finset.mem_filter.2 ⟨hmu, h⟩⟩
  obtain ⟨mu, hmu, hmin⟩ := Finset.exists_min_image _ weightHeight hT
  obtain ⟨_, x, hxU, hx0, hxw⟩ := Finset.mem_filter.1 hmu
  refine ⟨mu, x, hxU, hx0, hxw, fun a b hab => ?_⟩
  by_contra hy
  have hw := raising_shifts_weight_by_root E hrel (ne_of_lt hab) hxw
  have hin := nonzero_weight_mem_support E t ht hw hy
  have h1 := hmin _ (Finset.mem_filter.2 ⟨hin, _, hU a b x hxU, hy, hw⟩)
  rw [weightHeight_add_root] at h1
  have h2 : ((a : ℕ) : ℤ) < ((b : ℕ) : ℤ) := by exact_mod_cast hab
  omega

omit [CharZero K] in
theorem isotypic_stable_under_operators (E : GLOps n K V) (mu : Fin n → ℤ) (a b : Fin n) {x : V} (hx : x ∈ isoSub E mu) :
    E a b x ∈ isoSub E mu := by
  first | exact UpperTheory.Reformulated.B.Qf30.isotypic_stable_under_operators .. | (apply UpperTheory.Reformulated.B.Qf30.isotypic_stable_under_operators <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qf30.isotypic_stable_under_operators <;> assumption) | (apply @UpperTheory.Reformulated.B.Qf30.isotypic_stable_under_operators <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qf30.isotypic_stable_under_operators <;> assumption) | (apply @UpperTheory.Reformulated.B.Qf30.isotypic_stable_under_operators <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qf30.isotypic_stable_under_operators n K V ‹_› ‹_› ‹_› E mu a b x hx | exact @UpperTheory.Reformulated.B.Qf30.isotypic_stable_under_operators n K V ‹_› ‹_› ‹_› E mu a b x | exact @UpperTheory.Reformulated.B.Qf30.isotypic_stable_under_operators n K V ‹_› ‹_› ‹_› E mu a b | exact @UpperTheory.Reformulated.B.Qf30.isotypic_stable_under_operators n K V ‹_› ‹_› ‹_› E mu a | exact @UpperTheory.Reformulated.B.Qf30.isotypic_stable_under_operators n K V ‹_› ‹_› ‹_› E mu | exact @UpperTheory.Reformulated.B.Qf30.isotypic_stable_under_operators n K V ‹_› ‹_› ‹_› E | exact @UpperTheory.Reformulated.B.Qf30.isotypic_stable_under_operators n K V ‹_› ‹_› ‹_› | exact @UpperTheory.Reformulated.B.Qf30.isotypic_stable_under_operators n K V ‹_› ‹_› | exact @UpperTheory.Reformulated.B.Qf30.isotypic_stable_under_operators n K V ‹_› | exact @UpperTheory.Reformulated.B.Qf30.isotypic_stable_under_operators n K V | exact @UpperTheory.Reformulated.B.Qf30.isotypic_stable_under_operators n K | exact @UpperTheory.Reformulated.B.Qf30.isotypic_stable_under_operators n

end

theorem isotypic_subspaces_span_top (D : Formalism.BasicNotions.D7) (h2 : adm2 D) (K V : Type) [Field K] [CharZero K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (n : ℕ) (E : GLOps n K V) (hE : IsGLRep E) :
    (⨆ mu : Fin n → ℤ, isoSub E mu) = ⊤ := by
  obtain ⟨hrel, _, hw⟩ := hE
  have hst : ∀ a b, ∀ x ∈ (⨆ mu : Fin n → ℤ, isoSub E mu), E a b x ∈ (⨆ mu : Fin n → ℤ, isoSub E mu) := by
    intro a b x hx
    refine Submodule.iSup_induction (fun mu => isoSub E mu)
      (motive := fun x => E a b x ∈ (⨆ mu : Fin n → ℤ, isoSub E mu)) hx ?_ ?_ ?_
    · intro mu y hy
      exact Submodule.mem_iSup_of_mem mu (isotypic_stable_under_operators E mu a b hy)
    · simp
    · intro y z hy hz
      rw [map_add (f := _)]; exact Submodule.add_mem _ hy hz
  obtain ⟨W', hc, hW'⟩ := h2 K V n E ⟨hrel, ‹_›, hw⟩ _ hst
  obtain ⟨t, ht⟩ := IsCompactElement.exists_finset_of_le_iSup
    ((Submodule.fg_iff_compact (⊤ : Submodule K V)).1 Module.Finite.fg_top)
    (fun mu => weightSp E mu) (le_of_eq hw.symm)
  have hbot : W' = ⊥ := by
    by_contra hne
    obtain ⟨mu, x, hxW, hx⟩ := exists_highest_weight_vector E hrel t ht W' hW' hne
    have h1 : x ∈ (⨆ mu : Fin n → ℤ, isoSub E mu) :=
      Submodule.mem_iSup_of_mem mu (Submodule.subset_span ⟨1, Submonoid.one_mem _, x, hx, rfl⟩)
    have h0 : x ∈ (⨆ mu : Fin n → ℤ, isoSub E mu) ⊓ W' := ⟨h1, hxW⟩
    rw [hc.inf_eq_bot] at h0
    exact hx.1 (by simpa using h0)
  have := hc.sup_eq_top
  rwa [hbot, sup_bot_eq] at this

theorem isotypic_projector_fixed_mem (D : Formalism.BasicNotions.D7) (h2 : adm2 D) : IsotypicProjectorFixedMem := by
  intro K V _ _ _ _ _ n E hE lam e he Y hY
  have hY' : Y ∈ (⨆ mu : Fin n → ℤ, isoSub E mu) := by
    rw [isotypic_subspaces_span_top D h2 K V n E hE]; exact Submodule.mem_top
  rw [← hY]
  refine Submodule.iSup_induction (fun mu => isoSub E mu) (motive := fun y => e y ∈ isoSub E lam) hY' ?_ ?_ ?_
  · intro mu y hy
    by_cases hm : mu = lam
    · subst hm
      rw [he.1 y hy]; exact hy
    · rw [he.2 mu hm y hy]; exact Submodule.zero_mem _
  · simp
  · intro y z hy hz
    rw [map_add (f := _)]; exact Submodule.add_mem _ hy hz

end Formalism.MainNotions.G.GLWeightTheory
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.RootWeights.IntegralEnvelopingPreservesStable
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem dvr_fraction_field_charZero {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (S : UniformizedDVR p O) (hp : p.Prime) : CharZero (KK O) := by
  haveI hc := ringChar.charP O
  have hO : CharZero O := by
    rcases CharP.char_is_prime_or_zero O (ringChar O) with hq | hq
    · exfalso
      by_cases hpq : p = ringChar O
      · apply S.p_ne
        rw [hpq]
        exact CharP.cast_eq_zero O (ringChar O)
      · have hcop : Nat.Coprime p (ringChar O) := (Nat.coprime_primes hp hq).mpr hpq
        have h := Nat.gcd_eq_gcd_ab p (ringChar O)
        rw [hcop.gcd_eq_one] at h
        have h' := congrArg (Int.cast : ℤ → O) h
        push_cast at h'
        rw [CharP.cast_eq_zero O (ringChar O), zero_mul, add_zero] at h'
        exact (IsLocalRing.mem_maximalIdeal _).mp S.p_mem (IsUnit.of_mul_eq_one _ h'.symm)
    · rw [hq] at hc
      exact CharP.charP_to_charZero O
  exact charZero_of_injective_algebraMap (IsFractionRing.injective O (KK O))

section

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem pow_preserves_stable (f : Module.End K V) (W : Submodule K V) (hf : ∀ x ∈ W, f x ∈ W) (k : ℕ) :
    ∀ x ∈ W, (f ^ k) x ∈ W := by
  intro x hx
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact hf _ ih

theorem list_prod_preserves_stable (l : List (Module.End K V)) (W : Submodule K V) (hl : ∀ f ∈ l, ∀ x ∈ W, f x ∈ W) :
    ∀ x ∈ W, l.prod x ∈ W := by
  revert hl
  induction l with
  | nil =>
    intro _ x hx
    simpa using hx
  | cons f l ih =>
    intro hl x hx
    rw [List.prod_cons, Module.End.mul_apply]
    exact hl f (List.mem_cons.mpr (Or.inl rfl)) _
      (ih (fun g hg => hl g (List.mem_cons.mpr (Or.inr hg))) x hx)

theorem integral_enveloping_preserves_stable (E : GLOps n K V) (W : Submodule K V) (hW : ∀ a b, ∀ x ∈ W, E a b x ∈ W) :
    ∀ u ∈ UZmon E, ∀ x ∈ W, u x ∈ W := by
  intro u hu
  induction hu using Submonoid.closure_induction with
  | mem u hu =>
    rcases hu with ⟨a, b, k, -, rfl⟩ | ⟨a, k, rfl⟩
    · intro x hx
      simp only [divPowE, LinearMap.smul_apply]
      exact W.smul_mem _ (pow_preserves_stable _ W (hW a b) k x hx)
    · intro x hx
      simp only [binomE, LinearMap.smul_apply]
      refine W.smul_mem _ (list_prod_preserves_stable _ W ?_ x hx)
      intro f hf
      rw [List.mem_map] at hf
      obtain ⟨j, -, rfl⟩ := hf
      intro y hy
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
      exact W.sub_mem (hW a a y hy) (W.smul_mem _ hy)
  | one =>
    intro x hx
    simpa using hx
  | mul u v _ _ hu hv =>
    intro x hx
    rw [Module.End.mul_apply]
    exact hu _ (hv _ hx)

theorem generated_subrep_operator_stable (E : GLOps n K V) (h : V) : ∀ a b, ∀ x ∈ generatedSubrep E h, E a b x ∈ generatedSubrep E h := by
  intro a b x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, hu, rfl⟩ := hx
    exact Submodule.subset_span
      ⟨E a b * u, Submonoid.mul_mem _ (Submonoid.subset_closure ⟨(a, b), rfl⟩) hu, rfl⟩
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add (f := _)]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [map_smul]
    exact Submodule.smul_mem _ c hx

theorem isHWV_mem_highestWeightSpace (E : GLOps n K V) (lam : Fin n → ℤ) (v : V) (hv : IsHWV E lam v) : v ∈ highestWeightVectors E lam := by
  refine Submodule.mem_inf.mpr ⟨hv.2.1, ?_⟩
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]
  exact fun a b hab => hv.2.2 a b hab

theorem highestWeight_mem_weightSpace (E : GLOps n K V) (lam : Fin n → ℤ) (v : V) (hv : v ∈ highestWeightVectors E lam) : v ∈ weightSp E lam :=
  (Submodule.mem_inf.mp hv).1

theorem weight_projection_generated_scalar (E : GLOps n K V) (lam : Fin n → ℤ) (π : Module.End K V) (hπ : IsWtProj E lam π) (h : V)
    (hh : h ∈ highestWeightVectors E lam)
    (hB : generatedSubrep E h ≤ Submodule.span K {h} ⊔
      ⨆ mu ∈ {mu : Fin n → ℤ | mu ≠ lam}, (weightSp E mu ⊓ generatedSubrep E h))
    (y : V) (hy : y ∈ generatedSubrep E h) : ∃ a : K, π y = a • h := by
  obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.mp (hB hy)
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hs
  have hker : (⨆ mu ∈ {mu : Fin n → ℤ | mu ≠ lam}, (weightSp E mu ⊓ generatedSubrep E h)) ≤ LinearMap.ker π := by
    refine iSup₂_le fun mu hmu => ?_
    intro z hz
    exact hπ.2 mu hmu z (Submodule.mem_inf.mp hz).1
  refine ⟨a, ?_⟩
  rw [map_add (f := _), LinearMap.mem_ker.mp (hker ht), add_zero, map_smul, hπ.1 h (highestWeight_mem_weightSpace E lam h hh)]

theorem isotypic_sum_generated_subreps (E : GLOps n K V) (lam : Fin n → ℤ) {k : ℕ} (h : Fin k → V)
    (hspan : highestWeightVectors E lam ≤ Submodule.span K (Set.range h)) (Y : V) (hY : Y ∈ isoSub E lam) :
    ∃ y : Fin k → V, (∀ j, y j ∈ generatedSubrep E (h j)) ∧ Y = ∑ j, y j := by
  induction hY using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, hu, v, hv, rfl⟩ := hx
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp (hspan (isHWV_mem_highestWeightSpace E lam v hv))
    refine ⟨fun j => c j • u (h j), fun j => Submodule.smul_mem _ _ (Submodule.subset_span ⟨u, hu, rfl⟩), ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hc, map_sum]
    simp only [map_smul]
  | zero => exact ⟨0, fun j => Submodule.zero_mem _, by simp⟩
  | add x z _ _ hx hz =>
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hz
    exact ⟨y + y', fun j => Submodule.add_mem _ (hy j) (hy' j), by simp [Finset.sum_add_distrib]⟩
  | smul a x _ hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨a • y, fun j => Submodule.smul_mem _ a (hy j), by simp [Finset.smul_sum]⟩

end

theorem isotypic_lattice_of_five_parts (D : Formalism.BasicNotions.D7) (hA : IsotypicProjectorFixedMem) (hB : GeneratedMultipleOfHWV) (hC1 : DualLatticeDivisibility) (hC2 : LatticeSubspaceBasis) (hD : GeneratedLatticeCorollary) :
    TranslateCorollaryField D := by
  intro p n' O _ _ _ S hG n _ V _ _ _ _ _ E hE M hM hMQ lam hlam e he π hπ c Y _ heY hyp
  have := dvr_fraction_field_charZero S hG.prime
  have hp0 : (p : KK O) ≠ 0 := by exact_mod_cast hG.prime.ne_zero
  have hpc : (p : KK O) ^ c ≠ 0 := zpow_ne_zero _ hp0
  have hYiso : Y ∈ isoSub E lam := hA (KK O) V n E hE lam e he Y heY
  obtain ⟨k, h, hh, hli, hspan, hint⟩ := hC2 O V M hM.2 hMQ (highestWeightVectors E lam)
  obtain ⟨y, hy, hYsum⟩ := isotypic_sum_generated_subreps E lam h hspan Y hYiso
  have hkey : ∀ j, ∀ u ∈ UZmon E, ∃ o : O, π (u (y j)) = ((p : KK O) ^ c * algebraMap O (KK O) o) • h j := by
    intro j0 u hu
    have hex : ∀ j, ∃ a : KK O, π (u (y j)) = a • h j := fun j =>
      weight_projection_generated_scalar E lam π hπ (h j) (hh j).2 (hB (KK O) V n E hE lam (h j) (hh j).2) _
        (integral_enveloping_preserves_stable E _ (generated_subrep_operator_stable E (h j)) u hu _ (hy j))
    choose a ha using hex
    have hz : π (u Y) = ∑ j, a j • h j := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hYsum, map_sum, map_sum]
      exact Finset.sum_congr rfl fun j _ => ha j
    obtain ⟨m, hmM, hm⟩ := hC1 O V M hM.2 hMQ ((p : KK O) ^ c) (π (u Y)) (hyp u hu)
    have hzHW : π (u Y) ∈ highestWeightVectors E lam := by
      rw [hz]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hh j).2
    have hmHW : m ∈ highestWeightVectors E lam := by
      have : m = ((p : KK O) ^ c)⁻¹ • π (u Y) := by rw [hm, smul_smul, inv_mul_cancel₀ hpc, one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ hzHW
    obtain ⟨o, ho⟩ := hint m hmM hmHW
    refine ⟨o j0, ?_⟩
    have hsum : ∑ j, (a j - (p : KK O) ^ c * algebraMap O (KK O) (o j)) • h j = 0 := by
      have h1 : ∑ j, ((p : KK O) ^ c * algebraMap O (KK O) (o j)) • h j = π (u Y) := by
        rw [hm, ho, Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [mul_smul, algebraMap_smul]
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [h1, hz, sub_self]
    have := Fintype.linearIndependent_iff.1 hli _ hsum j0
    rw [ha j0, sub_eq_zero.1 this]
  have hfin : ∀ j, ∃ m ∈ M, y j = ((p : KK O) ^ (c - ((N0 n * deF p n (ellWt lam) : ℕ) : ℤ))) • m := fun j =>
    hD p n' O S hG n V E hE M hM lam hlam π hπ (h j) (hh j).1 (hh j).2 (hli.ne_zero j) c (y j) (hy j) (hkey j)
  choose m hmM hm using hfin
  refine ⟨∑ j, m j, Submodule.sum_mem _ fun j _ => hmM j, ?_⟩
  rw [hYsum, Finset.smul_sum]
  exact Finset.sum_congr rfl fun j _ => hm j

end Formalism.MainNotions.G.GLWeightTheory
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.RootWeights.ExistsNonzeroMultipleMemLattice
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem finite_full_submodule_isLattice {O : Type} [CommRing O] [IsDomain O]
    {V : Type} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]
    (M : Submodule O V) (hfg : M.FG) (hM : MQ (K := KK O) M = ⊤) : Submodule.IsLattice (KK O) M :=
  Submodule.IsLattice.of_fg (KK O) hfg

theorem exists_nonzero_multiple_mem_lattice {O : Type} [CommRing O] [IsDomain O]
    {V : Type} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]
    (M : Submodule O V) (hM : MQ (K := KK O) M = ⊤) (x : V) : ∃ a : O, a ≠ 0 ∧ a • x ∈ M := by
  first | exact Bl.general_b_fact_left_version.goal1 .. | (apply Bl.general_b_fact_left_version.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_left_version.goal1 <;> assumption) | (apply @Bl.general_b_fact_left_version.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_left_version.goal1 <;> assumption) | (apply @Bl.general_b_fact_left_version.goal1 <;> first | assumption | infer_instance)

theorem dual_lattice_values_mem_scaled : DualLatticeDivisibility := by
  intro O _ _ _ V _ _ _ _ _ M hfg hM t z hz
  have : Submodule.IsFullLattice (KK O) M :=
    { toIsLattice := finite_full_submodule_isLattice M hfg hM
      span_eq_top := hM }
  have : Module.Free O M := Submodule.IsLattice.free (KK O) M
  have : Module.Finite O M := Submodule.IsLattice.finite (KK O) M
  let b := Module.finBasis O M
  let B := b.extendOfIsFullLattice (KK O)
  have hB : ∀ i, B i = ((b i : M) : V) := fun i =>
    Module.Basis.extendOfIsFullLattice_apply (KK O) b i
  have hcoord : ∀ i, ∀ x ∈ M, ∃ o : O, B.coord i x = algebraMap O (KK O) o := by
    intro i x hx
    refine ⟨b.repr ⟨x, hx⟩ i, ?_⟩
    have h1 : x = ∑ j, (algebraMap O (KK O) (b.repr ⟨x, hx⟩ j)) • B j := by
      have h2 := congrArg (fun y : M => (y : V)) (b.sum_repr ⟨x, hx⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
      refine h2.symm.trans ?_
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hB, algebraMap_smul]
    conv_lhs => rw [h1]
    simp [Module.Basis.coord_apply, Finsupp.single_apply, Algebra.algebraMap_eq_smul_one]
  choose o ho using fun i => hz (B.coord i) (hcoord i)
  refine ⟨∑ i, o i • ((b i : M) : V), M.sum_mem fun i _ => M.smul_mem _ (b i).2, ?_⟩
  rw [← B.sum_repr z, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := ho i
  rw [Module.Basis.coord_apply] at this
  rw [this, hB, mul_smul, algebraMap_smul]

theorem lattice_inter_subspace_basis : LatticeSubspaceBasis := by
  intro O _ _ _ V _ _ _ _ _ M hfg hM H
  let N : Submodule O H := M.comap (H.subtype.restrictScalars O)
  have hmemN : ∀ x : H, x ∈ N ↔ (x : V) ∈ M := fun x => Iff.rfl
  have hNoeM : IsNoetherian O M := isNoetherian_of_fg_of_noetherian M hfg
  let φ : N →ₗ[O] M :=
    { toFun := fun x => ⟨((x : H) : V), (hmemN x.1).1 x.2⟩
      map_add' := fun x y => rfl
      map_smul' := fun a x => rfl }
  have hφ : Function.Injective φ := by
    intro x y hxy
    have : ((x : H) : V) = ((y : H) : V) := congrArg (fun w : M => (w : V)) hxy
    exact Subtype.ext (Subtype.ext this)
  have hNoeN : IsNoetherian O N := isNoetherian_of_injective φ hφ
  have hNfg : N.FG := (Module.Finite.iff_fg).1 inferInstance
  have hNspan : Submodule.span (KK O) (N : Set H) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨a, ha, hax⟩ := exists_nonzero_multiple_mem_lattice M hM (x : V)
    have ha1 : algebraMap O (KK O) a ≠ 0 :=
      (map_ne_zero_iff (algebraMap O (KK O)) (IsFractionRing.injective O (KK O))).2 ha
    have hmem : a • x ∈ N := (hmemN _).2 (by simpa using hax)
    have hx : x = (algebraMap O (KK O) a)⁻¹ • (a • x) := by
      rw [← algebraMap_smul (KK O) a x, smul_smul, inv_mul_cancel₀ ha1, one_smul]
    rw [hx]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)
  have : Submodule.IsFullLattice (KK O) N :=
    { toIsLattice := Submodule.IsLattice.of_fg (KK O) hNfg
      span_eq_top := hNspan }
  have : Module.Free O N := Submodule.IsLattice.free (KK O) N
  let b := Module.finBasis O N
  let B := b.extendOfIsFullLattice (KK O)
  have hB : ∀ i, B i = ((b i : N) : H) := fun i =>
    Module.Basis.extendOfIsFullLattice_apply (KK O) b i
  refine ⟨Module.finrank O N, fun j => (((b j : N) : H) : V), fun j => ⟨(hmemN _).1 (b j).2, (b j : H).2⟩, ?_, ?_, ?_⟩
  · have h1 := B.linearIndependent.map' H.subtype (Submodule.ker_subtype H)
    have h2 : (fun j => (((b j : N) : H) : V)) = (H.subtype ∘ B) := by
      funext j
      simp [hB]
    rw [h2]
    exact h1
  · intro x hx
    have h1 := congrArg (fun y : H => (y : V)) (B.sum_repr ⟨x, hx⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h1
    rw [← h1]
    refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, ?_⟩)
    simp [hB]
  · intro x hxM hxH
    refine ⟨fun j => b.repr ⟨⟨x, hxH⟩, (hmemN _).2 hxM⟩ j, ?_⟩
    have h1 := congrArg (fun y : N => ((y : H) : V)) (b.sum_repr ⟨⟨x, hxH⟩, (hmemN _).2 hxM⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h1
    exact h1.symm

end Formalism.MainNotions.G.GLWeightTheory
end
end

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem isotypic_lattice_corollary (D : Formalism.BasicNotions.D7) (h2 : adm2 D) (h12 : NablaDeltaComparisonField D) : TranslateCorollaryField D :=
  isotypic_lattice_of_five_parts D (isotypic_projector_fixed_mem D h2) hwv_generated_multiple_of_hwv dual_lattice_values_mem_scaled lattice_inter_subspace_basis (generated_lattice_corollary_of_thm D h12 hwv_generated_multiple_of_hwv)

end Formalism.MainNotions.G.GLWeightTheory
