module

public import Formalism.SharpRestriction.GrowthBounds.CovariantDegrees

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.RootWeights.NontrivialIsotypicWeightZeroKilled
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def binomialDiagonalSubring (E : GLOps n K V) : Subring (Module.End K V) :=
  Subring.closure {u | ∃ a k, u = binomE E a k}

def OperatorsShiftWeightsByRoots (E : GLOps n K V) : Prop :=
  ∀ a b ν, ∀ x ∈ weightSp E ν, E a b x ∈ weightSp E (ν + rootW a b)

def WeightsBounded (E : GLOps n K V) : Prop :=
  ∃ m : ℕ, ∀ ν, weightSp E ν ≠ ⊥ → ∀ a, |ν a| ≤ (m : ℤ)

def WeightProjectionsIntegralBinomial (E : GLOps n K V) : Prop :=
  ∃ Θ : (Fin n → ℤ) → Module.End K V, (∀ μ, Θ μ ∈ binomialDiagonalSubring E) ∧
    ∀ μ ν, ∀ x ∈ weightSp E ν, Θ μ x = if ν = μ then x else 0

def IsotypicComponentsSpanModule (E : GLOps n K V) : Prop := (⨆ mu : Fin n → ℤ, isoSub E mu) = ⊤

def TrivialIsotypicIsInvariant (E : GLOps n K V) : Prop :=
  ∀ x ∈ isoSub E 0, x ∈ weightSp E 0 ∧ ∀ a b : Fin n, a < b → E a b x = 0

def NontrivialIsotypicWeightZeroKilled (E : GLOps n K V) : Prop :=
  ∀ (P π : Module.End K V), IsWtProj E 0 π → (∀ w ∈ weightSp E 0, w ∈ nMinus E → P w = 0) →
    ∀ mu, mu ≠ 0 → ∀ x ∈ isoSub E mu, P (π x) = 0

end Formalism.MainNotions.G.GLWeightTheory
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.RootWeights.ExtremalProjectorLatticeScaledMem
section -- merged from Formalism.SharpRestriction.GrowthBounds.RootWeights.DvrFractionFieldCharZeroPrime
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section Arith

variable {p : ℕ} {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem natCast_unit_of_coprime (S : UniformizedDVR p O) {c : ℕ} (hc : Nat.Coprime c p) : IsUnit (c : O) := by
  by_contra h
  have hc' : (c : O) ∈ IsLocalRing.maximalIdeal O :=
    (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 h)
  have key : ((c.gcd p : ℕ) : ℤ) = (c : ℤ) * c.gcdA p + (p : ℤ) * c.gcdB p := Nat.gcd_eq_gcd_ab c p
  rw [Nat.Coprime.gcd_eq_one hc, Nat.cast_one] at key
  have key' : (1 : O) = (c : O) * ((c.gcdA p : ℤ) : O) + (p : O) * ((c.gcdB p : ℤ) : O) := by
    have := congrArg (Int.cast : ℤ → O) key
    push_cast at this
    exact this
  have h1 : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
    rw [key']
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hc') (Ideal.mul_mem_right _ _ S.p_mem)
  exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 h1)

theorem dvr_charZero_of_prime (S : UniformizedDVR p O) (hp : p.Prime) : CharZero O := by
  refine charZero_of_inj_zero (fun n hn => ?_)
  by_contra hne
  obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hne p hp.ne_one
  rw [Nat.cast_mul, Nat.cast_pow] at hn
  have hpe : (p : O) ^ e ≠ 0 := pow_ne_zero _ S.p_ne
  have hm0 : (m : O) = 0 := (mul_eq_zero.1 hn).resolve_left hpe
  have hu := natCast_unit_of_coprime S ((Nat.Prime.coprime_iff_not_dvd hp).2 hm).symm
  rw [hm0] at hu
  exact not_isUnit_zero hu

theorem dvr_fraction_field_charZero_prime (S : UniformizedDVR p O) (hp : p.Prime) : CharZero (KK O) := by
  haveI := dvr_charZero_of_prime S hp
  refine charZero_of_inj_zero (fun n hn => ?_)
  have h1 : algebraMap O (KK O) (n : O) = algebraMap O (KK O) 0 := by
    rw [map_natCast, map_zero]; exact hn
  have h2 : (n : O) = 0 := IsFractionRing.injective O (KK O) h1
  exact_mod_cast h2

end Arith

section Order

end Order

end Formalism.MainNotions.G.GLWeightTheory
end
end

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section Wt

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem operator_pow_shifts_weight {E : GLOps n K V} (hs : OperatorsShiftWeightsByRoots E) (a b : Fin n) (ν : Fin n → ℤ) (k : ℕ) (x : V)
    (hx : x ∈ weightSp E ν) : ((E a b) ^ k) x ∈ weightSp E (ν + (k : ℤ) • rootW a b) := by
  unfold OperatorsShiftWeightsByRoots at hs
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    have h1 := hs a b _ _ ih
    convert h1 using 2
    rw [Nat.cast_succ, add_smul, one_smul, add_assoc]

end Wt

section Lattice

variable {p : ℕ} {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {n : ℕ} {V : Type*} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]

theorem binomial_subring_preserves_lattice {E : GLOps n (KK O) V} {M : Submodule O V} (hM : UZStable (O := O) E M)
    (u : Module.End (KK O) V) (hu : u ∈ binomialDiagonalSubring E) : ∀ x ∈ M, u x ∈ M := by
  unfold binomialDiagonalSubring at hu
  unfold UZStable at hM
  induction hu using Subring.closure_induction with
  | mem u hu => obtain ⟨a, k, rfl⟩ := hu; exact hM _ (Or.inr ⟨a, k, rfl⟩)
  | zero => intro x _; simp
  | one => intro x hx; simpa using hx
  | add u v _ _ hu hv => intro x hx; rw [LinearMap.add_apply]; exact M.add_mem (hu x hx) (hv x hx)
  | neg u _ hu => intro x hx; rw [LinearMap.neg_apply]; exact M.neg_mem (hu x hx)
  | mul u v _ _ hu hv => intro x hx; rw [Module.End.mul_apply]; exact hu _ (hv x hx)

end Lattice

end Formalism.MainNotions.G.GLWeightTheory
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.RootWeights.BinomialPreservesDiagonalStable
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section
variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem isotypic_stable_under_gl_operator (E : GLOps n K V) (mu : Fin n → ℤ) (a b : Fin n) :
    ∀ x ∈ isoSub E mu, E a b x ∈ isoSub E mu := by
  unfold isoSub
  intro x hx
  have hle : Submodule.span K {x | ∃ u ∈ Umon E, ∃ v, IsHWV E mu v ∧ x = u v} ≤
      (Submodule.span K {x | ∃ u ∈ Umon E, ∃ v, IsHWV E mu v ∧ x = u v}).comap (E a b) := by
    rw [Submodule.span_le]
    rintro y ⟨u, hu, v, hv, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap]
    apply Submodule.subset_span
    refine ⟨E a b * u, ?_, v, hv, rfl⟩
    unfold Umon at hu ⊢
    exact Submonoid.mul_mem _ (Submonoid.subset_closure ⟨(a, b), rfl⟩) hu
  exact hle hx

theorem isotypic_sum_stable_gl_operator (E : GLOps n K V) (a b : Fin n) :
    ∀ x ∈ (⨆ mu : Fin n → ℤ, isoSub E mu), E a b x ∈ (⨆ mu : Fin n → ℤ, isoSub E mu) := by
  intro x hx
  have hle : (⨆ mu : Fin n → ℤ, isoSub E mu) ≤ (⨆ mu : Fin n → ℤ, isoSub E mu).comap (E a b) :=
    iSup_le fun mu y hy =>
      Submodule.mem_comap.mpr (Submodule.mem_iSup_of_mem mu (isotypic_stable_under_gl_operator E mu a b y hy))
  exact hle hx

theorem list_prod_preserves_submodule (W : Submodule K V) (l : List (Module.End K V))
    (h : ∀ u ∈ l, ∀ x ∈ W, u x ∈ W) : ∀ x ∈ W, l.prod x ∈ W := by
  induction l with
  | nil =>
    intro x hx
    simpa using hx
  | cons u l ih =>
    intro x hx
    rw [List.prod_cons]
    show u (l.prod x) ∈ W
    exact h u (by simp) _ (ih (fun v hv => h v (by simp [hv])) x hx)

theorem binomial_preserves_diagonal_stable (E : GLOps n K V) (W : Submodule K V) (hW : ∀ a, ∀ x ∈ W, E a a x ∈ W)
    (a : Fin n) (k : ℕ) : ∀ x ∈ W, binomE E a k x ∈ W := by
  unfold binomE
  intro x hx
  rw [LinearMap.smul_apply]
  apply W.smul_mem
  refine list_prod_preserves_submodule W _ ?_ x hx
  intro u hu
  simp only [List.mem_map, List.mem_range] at hu
  obtain ⟨j, -, rfl⟩ := hu
  intro y hy
  simp only [LinearMap.sub_apply, LinearMap.smul_apply]
  exact W.sub_mem (hW a y hy) (W.smul_mem _ (by simpa using hy))

theorem binomial_subring_preserves_stable (E : GLOps n K V) (W : Submodule K V) (hW : ∀ a, ∀ x ∈ W, E a a x ∈ W)
    (u : Module.End K V) (hu : u ∈ binomialDiagonalSubring E) : ∀ x ∈ W, u x ∈ W := by
  unfold binomialDiagonalSubring at hu
  let S : Subring (Module.End K V) :=
    { carrier := {u | ∀ x ∈ W, u x ∈ W}
      mul_mem' := fun {u v} hu hv x hx => hu _ (hv x hx)
      one_mem' := fun x hx => hx
      add_mem' := fun {u v} hu hv x hx => W.add_mem (hu x hx) (hv x hx)
      zero_mem' := fun x _ => W.zero_mem
      neg_mem' := fun {u} hu x hx => W.neg_mem (hu x hx) }
  have hle : Subring.closure {u | ∃ a k, u = binomE E a k} ≤ S := by
    rw [Subring.closure_le]
    rintro v ⟨a, k, rfl⟩
    exact binomial_preserves_diagonal_stable E W hW a k
  intro x hx
  exact (hle hu : u ∈ S) x hx

theorem weight_projection_mem_weightSpace (E : GLOps n K V) (hE : IsGLRep E) (Θ : (Fin n → ℤ) → Module.End K V)
    (hΘ : ∀ μ ν, ∀ x ∈ weightSp E ν, Θ μ x = if ν = μ then x else 0) (μ : Fin n → ℤ) (x : V) :
    Θ μ x ∈ weightSp E μ := by
  unfold IsGLRep at hE
  have hx : x ∈ ⨆ ν, weightSp E ν := by
    rw [hE.2.2]
    exact Submodule.mem_top
  have hle : (⨆ ν, weightSp E ν) ≤ (weightSp E μ).comap (Θ μ) := by
    refine iSup_le fun ν y hy => ?_
    rw [Submodule.mem_comap, hΘ μ ν y hy]
    split_ifs with h
    · subst h
      exact hy
    · exact Submodule.zero_mem _
  exact hle hx

theorem sum_weight_projections_eq_self (E : GLOps n K V) (hE : IsGLRep E) (Θ : (Fin n → ℤ) → Module.End K V)
    (hΘ : ∀ μ ν, ∀ x ∈ weightSp E ν, Θ μ x = if ν = μ then x else 0) (box : Finset (Fin n → ℤ))
    (hbox : ∀ ν, weightSp E ν ≠ ⊥ → ν ∈ box) (x : V) : ∑ μ ∈ box, Θ μ x = x := by
  unfold IsGLRep at hE
  have hx : x ∈ ⨆ ν, weightSp E ν := by
    rw [hE.2.2]
    exact Submodule.mem_top
  have hle : (⨆ ν, weightSp E ν) ≤ LinearMap.ker ((∑ μ ∈ box, Θ μ) - 1) := by
    refine iSup_le fun ν y hy => ?_
    have hy' : ∀ μ, Θ μ y = if ν = μ then y else 0 := fun μ => hΘ μ ν y hy
    rw [LinearMap.mem_ker]
    by_cases hν : weightSp E ν = ⊥
    · have h0 : y = 0 := by
        rw [hν] at hy
        exact (Submodule.mem_bot K).mp hy
      subst h0
      simp
    · simp [hy', hbox ν hν]
  have h := hle hx
  rw [LinearMap.mem_ker] at h
  simpa [sub_eq_zero] using h

def negHeightFunctional (ν : Fin n → ℤ) : ℤ := - ∑ c : Fin n, ((c : ℕ) : ℤ) * ν c

theorem negHeight_add_root (ν : Fin n → ℤ) (a b : Fin n) :
    negHeightFunctional (ν + rootW a b) = negHeightFunctional ν + (((b : ℕ) : ℤ) - ((a : ℕ) : ℤ)) := by
  unfold negHeightFunctional rootW
  simp only [Pi.add_apply, Pi.sub_apply, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

end

theorem sum_isotypic_top_of_weight_data (D : Formalism.BasicNotions.D7) (h2 : adm2 D) {K V : Type} [Field K] [CharZero K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {n : ℕ} (E : GLOps n K V) (hE : IsGLRep E) (hs : OperatorsShiftWeightsByRoots E)
    (hb : WeightsBounded E) (hθ : WeightProjectionsIntegralBinomial E) : IsotypicComponentsSpanModule E := by
  classical
  unfold IsotypicComponentsSpanModule
  obtain ⟨W', hc, hW'⟩ := h2 K V n E hE (⨆ mu : Fin n → ℤ, isoSub E mu) (fun a b => isotypic_sum_stable_gl_operator E a b)
  by_contra hne
  have hW'ne : W' ≠ ⊥ := by
    intro h0
    rw [h0] at hc
    exact hne (by simpa using hc.sup_eq_top)
  obtain ⟨x, hxW', hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW'ne
  obtain ⟨m, hm⟩ := hb
  obtain ⟨Θ, hΘm, hΘ⟩ := hθ
  set box : Finset (Fin n → ℤ) := Fintype.piFinset (fun _ : Fin n => Finset.Icc (-(m : ℤ)) m) with hboxdef
  have hbox : ∀ ν, weightSp E ν ≠ ⊥ → ν ∈ box := by
    intro ν hν
    rw [hboxdef, Fintype.mem_piFinset]
    intro a
    rw [Finset.mem_Icc]
    exact abs_le.1 (hm ν hν a)
  have hsum := sum_weight_projections_eq_self E hE Θ hΘ box hbox x
  have hex : ∃ ν ∈ box, Θ ν x ≠ 0 := by
    apply Finset.exists_ne_zero_of_sum_ne_zero
    rw [hsum]; exact hx0
  set S : Finset (Fin n → ℤ) := box.filter (fun ν => W' ⊓ weightSp E ν ≠ ⊥) with hS
  have hSne : S.Nonempty := by
    obtain ⟨ν, hν, hν0⟩ := hex
    refine ⟨ν, ?_⟩
    rw [hS, Finset.mem_filter]
    refine ⟨hν, fun hbot => hν0 ?_⟩
    have : Θ ν x ∈ W' ⊓ weightSp E ν :=
      ⟨binomial_subring_preserves_stable E W' (fun a => hW' a a) (Θ ν) (hΘm ν) x hxW', weight_projection_mem_weightSpace E hE Θ hΘ ν x⟩
    rw [hbot] at this
    simpa using this
  obtain ⟨ν, hνS, hmax⟩ := Finset.exists_max_image S negHeightFunctional hSne
  rw [hS, Finset.mem_filter] at hνS
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hνS.2
  have hraise : ∀ a b : Fin n, a < b → E a b y = 0 := by
    intro a b hab
    by_contra hne0
    have hmem : E a b y ∈ W' ⊓ weightSp E (ν + rootW a b) := ⟨hW' a b y hy.1, hs a b ν y hy.2⟩
    have h1 : W' ⊓ weightSp E (ν + rootW a b) ≠ ⊥ := by
      intro hbot
      rw [hbot] at hmem
      exact hne0 (by simpa using hmem)
    have h2' : weightSp E (ν + rootW a b) ≠ ⊥ := by
      intro hbot
      rw [hbot] at h1
      exact h1 (by simp)
    have h3 : ν + rootW a b ∈ S := by
      rw [hS, Finset.mem_filter]
      exact ⟨hbox _ h2', h1⟩
    have h4 := hmax _ h3
    rw [negHeight_add_root] at h4
    have h5 : ((a : ℕ) : ℤ) < ((b : ℕ) : ℤ) := by exact_mod_cast hab
    linarith
  have hhw : IsHWV E ν y := ⟨hy0, hy.2, hraise⟩
  have hyiso : y ∈ isoSub E ν := Submodule.subset_span ⟨1, (Umon E).one_mem, y, hhw, rfl⟩
  have hyW : y ∈ (⨆ mu : Fin n → ℤ, isoSub E mu) := (le_iSup (fun mu : Fin n → ℤ => isoSub E mu) ν) hyiso
  have : y ∈ (⨆ mu : Fin n → ℤ, isoSub E mu) ⊓ W' := ⟨hyW, hy.1⟩
  rw [hc.inf_eq_bot] at this
  exact hy0 (by simpa using this)

end Formalism.MainNotions.G.GLWeightTheory
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.RootWeights.LoweringWordWeightOrNMinus
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem mem_weightSpace_iff_diag_eigen {E : GLOps n K V} {mu : Fin n → ℤ} {x : V} :
    x ∈ weightSp E mu ↔ ∀ a, E a a x = (mu a : K) • x := by
  unfold weightSp
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
  all_goals exact Iff.rfl

theorem weight_zero_lowering_kills_raising [CharZero K] [FiniteDimensional K V] {E : GLOps n K V} (hE : IsGLRep E) {v : V}
    (hv : v ∈ weightSp E 0) (a b : Fin n) (hab : a ≠ b) (he : E a b v = 0) : E b a v = 0 := by
  have hva : E a a v = 0 := by simpa using (mem_weightSpace_iff_diag_eigen.mp hv) a
  have hvb : E b b v = 0 := by simpa using (mem_weightSpace_iff_diag_eigen.mp hv) b
  have rAA : ∀ y, E a a (E b a y) = E b a (E a a y) - E b a y := by
    intro y
    have h := LinearMap.congr_fun (hE.1 a a b a) y
    rw [if_neg hab, if_pos rfl, LinearMap.sub_apply, LinearMap.sub_apply, LinearMap.zero_apply,
      zero_sub] at h
    rw [sub_eq_add_neg]
    exact sub_eq_iff_eq_add'.mp h
  have rBB : ∀ y, E b b (E b a y) = E b a (E b b y) + E b a y := by
    intro y
    have h := LinearMap.congr_fun (hE.1 b b b a) y
    rw [if_pos rfl, if_neg hab, LinearMap.sub_apply, LinearMap.sub_apply, LinearMap.zero_apply,
      sub_zero] at h
    exact sub_eq_iff_eq_add'.mp h
  have rEF : ∀ y, E a b (E b a y) = E b a (E a b y) + (E a a y - E b b y) := by
    intro y
    have h := LinearMap.congr_fun (hE.1 a b b a) y
    rw [if_pos rfl, if_pos rfl, LinearMap.sub_apply, LinearMap.sub_apply] at h
    exact sub_eq_iff_eq_add'.mp h
  have hstep : ∀ j : ℕ, E b a ((⇑(E b a))^[j] v) = (⇑(E b a))^[j+1] v :=
    fun j => (Function.iterate_succ_apply' _ j v).symm
  have hA : ∀ k : ℕ, E a a ((⇑(E b a))^[k] v) = -(k : K) • (⇑(E b a))^[k] v := by
    intro k
    induction k with
    | zero => simp [hva]
    | succ k ih =>
      rw [← hstep k, rAA, ih, map_smul]
      push_cast
      module
  have hB : ∀ k : ℕ, E b b ((⇑(E b a))^[k] v) = (k : K) • (⇑(E b a))^[k] v := by
    intro k
    induction k with
    | zero => simp [hvb]
    | succ k ih =>
      rw [← hstep k, rBB, ih, map_smul]
      push_cast
      module
  have hC : ∀ k : ℕ, E a b ((⇑(E b a))^[k+1] v) = -((k : K) * ((k : K) + 1)) • (⇑(E b a))^[k] v := by
    intro k
    induction k with
    | zero =>
      rw [← hstep 0, rEF]
      simp [he, hva, hvb]
    | succ k ih =>
      rw [← hstep (k+1), rEF, ih, map_smul, hstep k, hA (k+1), hB (k+1)]
      push_cast
      module
  have hex : ∃ k : ℕ, (⇑(E b a))^[k+1] v = 0 := by
    by_contra hne
    push_neg at hne
    have hli : LinearIndependent K (fun k : ℕ => (⇑(E b a))^[k+1] v) := by
      refine Module.End.eigenvectors_linearIndependent' (E a a)
        (fun k : ℕ => -(((k+1 : ℕ) : K))) ?_ _ ?_
      · intro i j hij
        simpa using hij
      · intro k
        rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
        exact ⟨hA (k+1), hne k⟩
    haveI := hli.finite
    exact not_finite ℕ
  have hdown : ∀ j : ℕ, (⇑(E b a))^[j+1] v = 0 → E b a v = 0 := by
    intro j
    induction j with
    | zero => intro h; simpa using h
    | succ j ih =>
      intro h
      apply ih
      have h2 := hC (j+1)
      rw [h, map_zero] at h2
      have hc : -(((j+1 : ℕ) : K) * (((j+1 : ℕ) : K) + 1)) ≠ 0 := by
        rw [neg_ne_zero]
        refine mul_ne_zero ?_ ?_
        · exact_mod_cast Nat.succ_ne_zero j
        · exact_mod_cast Nat.succ_ne_zero (j+1)
      exact (smul_eq_zero.mp h2.symm).resolve_left hc
  obtain ⟨k, hk⟩ := hex
  exact hdown k hk

def commonKernelOperators (E : GLOps n K V) : Submodule K V := ⨅ a, ⨅ b, LinearMap.ker (E a b)

theorem mem_common_kernel_iff {E : GLOps n K V} {x : V} : x ∈ commonKernelOperators E ↔ ∀ a b, E a b x = 0 := by
  simp only [commonKernelOperators, Submodule.mem_iInf, LinearMap.mem_ker]

theorem enveloping_preserves_common_kernel {E : GLOps n K V} {u : Module.End K V} (hu : u ∈ Umon E) :
    ∀ y ∈ commonKernelOperators E, u y ∈ commonKernelOperators E := by
  have hu' : u ∈ Submonoid.closure (Set.range fun ab : Fin n × Fin n => E ab.1 ab.2) := hu
  clear hu
  induction hu' using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨⟨a, b⟩, rfl⟩ := hx
    intro y hy
    show E a b y ∈ commonKernelOperators E
    rw [mem_common_kernel_iff.mp hy a b]
    exact zero_mem _
  | one => intro y hy; exact hy
  | mul x z _ _ ihx ihz => intro y hy; exact ihx _ (ihz y hy)

theorem trivial_isotypic_invariant_holds [CharZero K] [FiniteDimensional K V] {E : GLOps n K V} (hE : IsGLRep E) : TrivialIsotypicIsInvariant E := by
  have hle : isoSub E 0 ≤ commonKernelOperators E := by
    unfold isoSub
    rw [Submodule.span_le]
    rintro x ⟨u, hu, v, hv, rfl⟩
    refine enveloping_preserves_common_kernel hu v ?_
    rw [mem_common_kernel_iff]
    intro a b
    rcases lt_trichotomy a b with h | rfl | h
    · exact hv.2.2 a b h
    · simpa using (mem_weightSpace_iff_diag_eigen.mp hv.2.1) a
    · exact weight_zero_lowering_kills_raising hE hv.2.1 b a (ne_of_lt h) (hv.2.2 b a h)
  intro x hx
  have hx0 := mem_common_kernel_iff.mp (hle hx)
  refine ⟨mem_weightSpace_iff_diag_eigen.mpr fun a => ?_, fun a b _ => hx0 a b⟩
  simp [hx0 a a]

def loweringWordMonoid (E : GLOps n K V) : Submonoid (Module.End K V) :=
  Submonoid.closure {F | ∃ a b : Fin n, b < a ∧ F = E a b}

def loweringWordSpan (E : GLOps n K V) (v : V) : Submodule K V :=
  Submodule.span K {x | ∃ u ∈ loweringWordMonoid E, x = u v}

theorem lowering_word_span_lowering_stable {E : GLOps n K V} {v : V} {a b : Fin n} (hab : b < a) :
    ∀ y ∈ loweringWordSpan E v, E a b y ∈ loweringWordSpan E v := by
  intro y hy
  have key : loweringWordSpan E v ≤ (loweringWordSpan E v).comap (E a b) := by
    unfold loweringWordSpan
    rw [Submodule.span_le]
    rintro x ⟨u, hu, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap]
    exact Submodule.subset_span ⟨E a b * u, mul_mem (Submonoid.subset_closure ⟨a, b, hab, rfl⟩) hu, rfl⟩
  exact key hy

theorem lowering_word_span_operator_mem {E : GLOps n K V} (hE : IsGLRep E) {mu : Fin n → ℤ} {v : V} (hv : IsHWV E mu v)
    {u : Module.End K V} (hu : u ∈ loweringWordMonoid E) : ∀ c d, E c d (u v) ∈ loweringWordSpan E v := by
  have hmem : ∀ w ∈ loweringWordMonoid E, w v ∈ loweringWordSpan E v := fun w hw => Submodule.subset_span ⟨w, hw, rfl⟩
  have main : ∀ w ∈ loweringWordMonoid E, (∀ c d, E c d (w v) ∈ loweringWordSpan E v) →
      ∀ c d, E c d (u (w v)) ∈ loweringWordSpan E v := by
    have hu' : u ∈ Submonoid.closure {F | ∃ a b : Fin n, b < a ∧ F = E a b} := hu
    clear hu
    induction hu' using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨a, b, hab, rfl⟩ := hx
      intro w hw hwY c d
      have h := LinearMap.congr_fun (hE.1 c d a b) (w v)
      rw [LinearMap.sub_apply, LinearMap.sub_apply] at h
      have h2 := sub_eq_iff_eq_add.mp h
      rw [show E c d (E a b (w v)) = (E c d * E a b) (w v) from rfl, h2]
      refine add_mem (sub_mem ?_ ?_) (lowering_word_span_lowering_stable hab _ (hwY c d))
      · split_ifs
        · exact hwY c b
        · rw [LinearMap.zero_apply]; exact zero_mem _
      · split_ifs
        · exact hwY a d
        · rw [LinearMap.zero_apply]; exact zero_mem _
    | one => intro w hw hwY c d; exact hwY c d
    | mul x z _ hz ihx ihz =>
      intro w hw hwY c d
      exact ihx (z * w) (mul_mem hz hw) (ihz w hw hwY) c d
  have base : ∀ c d, E c d ((1 : Module.End K V) v) ∈ loweringWordSpan E v := by
    intro c d
    show E c d v ∈ _
    rcases lt_trichotomy c d with h | rfl | h
    · rw [hv.2.2 c d h]; exact zero_mem _
    · rw [(mem_weightSpace_iff_diag_eigen.mp hv.2.1) c]
      exact Submodule.smul_mem _ _ (hmem 1 (one_mem _))
    · exact hmem (E c d) (Submonoid.subset_closure ⟨c, d, h, rfl⟩)
  intro c d
  exact main 1 (one_mem _) base c d

theorem lowering_word_span_gl_stable {E : GLOps n K V} (hE : IsGLRep E) {mu : Fin n → ℤ} {v : V} (hv : IsHWV E mu v)
    (c d : Fin n) : ∀ y ∈ loweringWordSpan E v, E c d y ∈ loweringWordSpan E v := by
  intro y hy
  have key : loweringWordSpan E v ≤ (loweringWordSpan E v).comap (E c d) := by
    unfold loweringWordSpan
    rw [Submodule.span_le]
    rintro x ⟨u, hu, rfl⟩
    exact lowering_word_span_operator_mem hE hv hu c d
  exact key hy

theorem lowering_word_span_enveloping_stable {E : GLOps n K V} (hE : IsGLRep E) {mu : Fin n → ℤ} {v : V} (hv : IsHWV E mu v)
    {u : Module.End K V} (hu : u ∈ Umon E) : ∀ y ∈ loweringWordSpan E v, u y ∈ loweringWordSpan E v := by
  have hu' : u ∈ Submonoid.closure (Set.range fun ab : Fin n × Fin n => E ab.1 ab.2) := hu
  clear hu
  induction hu' using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨⟨a, b⟩, rfl⟩ := hx
    intro y hy
    exact lowering_word_span_gl_stable hE hv a b y hy
  | one => intro y hy; exact hy
  | mul x z _ _ ihx ihz => intro y hy; exact ihx _ (ihz y hy)

theorem lowering_word_weight_or_nMinus {E : GLOps n K V} (hs : OperatorsShiftWeightsByRoots E) {mu : Fin n → ℤ} {v : V}
    (hv : v ∈ weightSp E mu) {u : Module.End K V} (hu : u ∈ loweringWordMonoid E) :
    (∃ ν, u v ∈ weightSp E ν) ∧ (u v = v ∨ u v ∈ nMinus E) := by
  have hu' : u ∈ Submonoid.closure {F | ∃ a b : Fin n, b < a ∧ F = E a b} := hu
  clear hu
  induction hu' using Submonoid.closure_induction generalizing mu v with
  | mem x hx =>
    obtain ⟨a, b, hab, rfl⟩ := hx
    refine ⟨⟨mu + rootW a b, hs a b mu v hv⟩, Or.inr ?_⟩
    have hle : LinearMap.range (E a b) ≤ nMinus E := by
      unfold nMinus
      exact le_iSup_of_le a (le_iSup_of_le b (le_iSup_of_le hab le_rfl))
    exact hle (LinearMap.mem_range_self _ v)
  | one => exact ⟨⟨mu, hv⟩, Or.inl rfl⟩
  | mul x z _ _ ihx ihz =>
    obtain ⟨⟨ν, hν⟩, h1⟩ := ihz (mu := mu) (v := v) hv
    obtain ⟨⟨ν', hν'⟩, h2⟩ := ihx (mu := ν) (v := z v) hν
    refine ⟨⟨ν', hν'⟩, ?_⟩
    rcases h2 with h2 | h2
    · rcases h1 with h1 | h1
      · left; exact h2.trans h1
      · right
        rw [show (x * z) v = x (z v) from rfl, h2]
        exact h1
    · right; exact h2

theorem nontrivial_isotypic_weight_zero_killed {E : GLOps n K V} (hE : IsGLRep E) (hs : OperatorsShiftWeightsByRoots E) : NontrivialIsotypicWeightZeroKilled E := by
  intro P π hπ hP mu hmu x hx
  have hY : ∀ v, IsHWV E mu v → ∀ y ∈ loweringWordSpan E v, P (π y) = 0 := by
    intro v hv
    have key : loweringWordSpan E v ≤ LinearMap.ker (P * π) := by
      unfold loweringWordSpan
      rw [Submodule.span_le]
      rintro y ⟨w, hw, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      show P (π (w v)) = 0
      obtain ⟨⟨ν, hν⟩, h⟩ := lowering_word_weight_or_nMinus hs hv.2.1 hw
      rcases h with h | h
      · rw [h, hπ.2 mu hmu v hv.2.1, map_zero]
      · by_cases hν0 : ν = 0
        · subst hν0
          rw [hπ.1 _ hν]
          exact hP _ hν h
        · rw [hπ.2 ν hν0 _ hν, map_zero]
    intro y hy
    exact LinearMap.mem_ker.mp (key hy)
  have hiso : isoSub E mu ≤ LinearMap.ker (P * π) := by
    unfold isoSub
    rw [Submodule.span_le]
    rintro y ⟨u, hu, v, hv, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    show P (π (u v)) = 0
    exact hY v hv (u v) (lowering_word_span_enveloping_stable hE hv hu v (Submodule.subset_span ⟨1, one_mem _, rfl⟩))
  exact LinearMap.mem_ker.mp (hiso hx)

end Formalism.MainNotions.G.GLWeightTheory
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.RootWeights.MemWeightSpaceIffDiagonalEigen
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem mem_weightSpace_iff_diagonal_eigen (E : GLOps n K V) (mu : Fin n → ℤ) (x : V) :
    x ∈ weightSp E mu ↔ ∀ a, E a a x = (mu a : K) • x := by
  simp only [weightSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]

theorem gl_rep_shifts_weights {E : GLOps n K V} (hE : IsGLRep E) : OperatorsShiftWeightsByRoots E := by
  intro a b ν x hx
  rw [mem_weightSpace_iff_diagonal_eigen] at hx ⊢
  intro c
  have h1 := congrArg (fun T : Module.End K V => T x) (hE.1 c c a b)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, hx c, map_smul] at h1
  rw [sub_eq_iff_eq_add] at h1
  rw [h1]
  simp only [rootW, Pi.add_apply, Pi.sub_apply, Pi.single_apply]
  by_cases hca : c = a <;> by_cases hcb : c = b
  · subst hca; subst hcb; simp
  · subst hca
    have : ¬ b = c := fun h => hcb h.symm
    simp [hcb, this]; module
  · subst hcb
    simp [hca]; module
  · have : ¬ b = c := fun h => hcb h.symm
    simp [hca, hcb, this]

theorem findim_weights_bounded [CharZero K] [FiniteDimensional K V] (E : GLOps n K V) : WeightsBounded E := by
  classical
  have hfin : ∀ a, Set.Finite {t : ℤ | (E a a).HasEigenvalue (t : K)} := fun a =>
    (Module.End.finite_hasEigenvalue (E a a)).preimage
      (fun x _ y _ h => by exact_mod_cast h)
  have hT : Set.Finite (⋃ a, {t : ℤ | (E a a).HasEigenvalue (t : K)}) := Set.finite_iUnion hfin
  obtain ⟨m, hm⟩ := (hT.image Int.natAbs).bddAbove
  refine ⟨m, fun ν hν a => ?_⟩
  have hev : (E a a).HasEigenvalue ((ν a : ℤ) : K) := by
    rw [Module.End.hasEigenvalue_iff]
    obtain ⟨x, hx, hx0⟩ := Submodule.ne_bot_iff _ |>.mp hν
    rw [mem_weightSpace_iff_diagonal_eigen] at hx
    rw [Submodule.ne_bot_iff]
    exact ⟨x, Module.End.mem_eigenspace_iff.mpr (hx a), hx0⟩
  have := hm ⟨ν a, Set.mem_iUnion.mpr ⟨a, hev⟩, rfl⟩
  rw [Int.abs_eq_natAbs]
  exact_mod_cast this

theorem diagonal_list_prod_eigen_apply (E : GLOps n K V) (a : Fin n) (ν : Fin n → ℤ) (x : V) (hx : x ∈ weightSp E ν) (k : ℕ) :
    (((List.range k).map fun j : ℕ => E a a - (j : K) • (1 : Module.End K V)).prod) x =
      (∏ j ∈ Finset.range k, ((ν a : K) - (j : K))) • x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.prod_append, Finset.prod_range_succ]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
    rw [(mem_weightSpace_iff_diagonal_eigen E ν x).mp hx a, ← sub_smul, map_smul, ih, smul_smul, mul_comm]

theorem binomial_diagonal_apply_weight [CharZero K] (E : GLOps n K V) (a : Fin n) (ν : Fin n → ℤ) (x : V)
    (hx : x ∈ weightSp E ν) (k : ℕ) :
    binomE E a k x = ((Ring.choose (ν a) k : ℤ) : K) • x := by
  have hk : (k.factorial : K) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have hZ : (k.factorial : ℤ) * Ring.choose (ν a) k = ∏ j ∈ Finset.range k, (ν a - (j : ℤ)) := by
    rw [← descPochhammer_eval_eq_prod_range, Polynomial.eval_eq_smeval,
      Ring.descPochhammer_eq_factorial_smul_choose, nsmul_eq_mul]
  have hK : (k.factorial : K) * ((Ring.choose (ν a) k : ℤ) : K) =
      ∏ j ∈ Finset.range k, ((ν a : K) - (j : K)) := by
    have := congrArg (fun t : ℤ => (t : K)) hZ
    push_cast at this
    exact this
  rw [binomE, LinearMap.smul_apply, diagonal_list_prod_eigen_apply E a ν x hx k, ← hK, smul_smul,
    ← mul_assoc, inv_mul_cancel₀ hk, one_mul]

def ActsByIntegralPolynomial (E : GLOps n K V) (a : Fin n) (g : ℤ → ℤ) : Prop :=
  ∃ u ∈ binomialDiagonalSubring E, ∀ ν, ∀ x ∈ weightSp E ν, u x = ((g (ν a) : ℤ) : K) • x

theorem binomial_polynomial_acts_by_choose [CharZero K] (E : GLOps n K V) (a : Fin n) (i : ℕ) :
    ActsByIntegralPolynomial E a (fun z => Ring.choose z i) := ⟨binomE E a i, Subring.subset_closure ⟨a, i, rfl⟩,
    fun ν x hx => binomial_diagonal_apply_weight E a ν x hx i⟩

theorem action_zero (E : GLOps n K V) (a : Fin n) : ActsByIntegralPolynomial E a (fun _ => 0) := ⟨0, Subring.zero_mem _, fun ν x _ => by simp⟩

theorem binomial_polynomial_action_add {E : GLOps n K V} {a : Fin n} {g h : ℤ → ℤ} (hg : ActsByIntegralPolynomial E a g) (hh : ActsByIntegralPolynomial E a h) :
    ActsByIntegralPolynomial E a (fun z => g z + h z) := by
  obtain ⟨u, hu, hux⟩ := hg
  obtain ⟨v, hv, hvx⟩ := hh
  refine ⟨u + v, Subring.add_mem _ hu hv, fun ν x hx => ?_⟩
  rw [LinearMap.add_apply, hux ν x hx, hvx ν x hx, ← add_smul]
  congr 1
  push_cast
  ring

theorem action_mul_const {E : GLOps n K V} {a : Fin n} {g : ℤ → ℤ} (hg : ActsByIntegralPolynomial E a g) (c : ℤ) :
    ActsByIntegralPolynomial E a (fun z => g z * c) := by
  obtain ⟨u, hu, hux⟩ := hg
  refine ⟨u * ((c : Module.End K V)), Subring.mul_mem _ hu (intCast_mem (binomialDiagonalSubring E) c), fun ν x hx => ?_⟩
  rw [Module.End.mul_apply, Module.End.intCast_apply, map_zsmul, hux ν x hx,
    ← Int.cast_smul_eq_zsmul K, smul_smul]
  congr 1
  push_cast
  ring

theorem action_finset_sum {E : GLOps n K V} {a : Fin n} {ι : Type*} (s : Finset ι) (g : ι → ℤ → ℤ)
    (hg : ∀ i ∈ s, ActsByIntegralPolynomial E a (g i)) : ActsByIntegralPolynomial E a (fun z => ∑ i ∈ s, g i z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using action_zero E a
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact binomial_polynomial_action_add (hg i (Finset.mem_insert_self i s))
      (ih fun j hj => hg j (Finset.mem_insert_of_mem hj))

theorem binomial_shifted_action [CharZero K] (E : GLOps n K V) (a : Fin n) (m k : ℕ) :
    ActsByIntegralPolynomial E a (fun z => Ring.choose (z + (m : ℤ)) k) := by
  have h : (fun z : ℤ => Ring.choose (z + (m : ℤ)) k) = fun z =>
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal k, Ring.choose z ij.1 * Ring.choose (m : ℤ) ij.2 := by
    funext z
    exact Ring.add_choose_eq k (Commute.all z (m : ℤ))
  rw [h]
  exact action_finset_sum _ _ fun ij _ => action_mul_const (binomial_polynomial_acts_by_choose E a ij.1) _

private theorem exists_binomial_transform_inverse (f : ℕ → ℤ) (M : ℕ) : ∃ d : ℕ → ℤ, ∀ N ≤ M,
    ∑ k ∈ Finset.range (N + 1), (N.choose k : ℤ) * d k = f N := by
  induction M with
  | zero =>
    refine ⟨fun _ => f 0, fun N hN => ?_⟩
    obtain rfl : N = 0 := Nat.le_zero.mp hN
    simp
  | succ M ih =>
    obtain ⟨d, hd⟩ := ih
    set s := ∑ j ∈ Finset.range (M + 1), ((M + 1).choose j : ℤ) * d j with hs
    refine ⟨fun k => if k = M + 1 then f (M + 1) - s else d k, fun N hN => ?_⟩
    beta_reduce
    rcases Nat.lt_or_ge N (M + 1) with h | h
    · have e : ∑ k ∈ Finset.range (N + 1), (N.choose k : ℤ) * (if k = M + 1 then f (M + 1) - s else d k)
          = ∑ k ∈ Finset.range (N + 1), (N.choose k : ℤ) * d k :=
        Finset.sum_congr rfl fun k hk => by rw [if_neg (by simp at hk; omega)]
      rw [e, hd N (by omega)]
    · obtain rfl : N = M + 1 := by omega
      rw [Finset.sum_range_succ]
      have e : ∑ k ∈ Finset.range (M + 1), ((M + 1).choose k : ℤ) *
          (if k = M + 1 then f (M + 1) - s else d k) = s := by
        rw [hs]
        exact Finset.sum_congr rfl fun k hk => by rw [if_neg (by simp at hk; omega)]
      rw [e]
      simp

theorem newton_interpolation_indicator (m : ℕ) (c : ℤ) : ∃ d : ℕ → ℤ, ∀ z : ℤ, |z| ≤ (m : ℤ) →
    ∑ k ∈ range (2 * m + 1), Ring.choose (z + (m : ℤ)) k * d k = if z = c then 1 else 0 := by
  obtain ⟨d, hd⟩ := exists_binomial_transform_inverse (fun N => if (N : ℤ) - (m : ℤ) = c then 1 else 0) (2 * m)
  refine ⟨d, fun z hz => ?_⟩
  obtain ⟨h1, h2⟩ := abs_le.mp hz
  obtain ⟨N, hN⟩ : ∃ N : ℕ, z + (m : ℤ) = N := ⟨(z + m).toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
  have hN2 : N ≤ 2 * m := by omega
  rw [hN]
  have hc : ∀ k ∈ range (2 * m + 1), Ring.choose (N : ℤ) k * d k = (N.choose k : ℤ) * d k := by
    intro k _
    rw [Ring.choose_natCast]
  rw [Finset.sum_congr rfl hc, ← Finset.sum_range_add_sum_Ico _ (show N + 1 ≤ 2 * m + 1 by omega)]
  rw [Finset.sum_eq_zero (s := Finset.Ico (N + 1) (2 * m + 1)) (fun k hk => by
      rw [Nat.choose_eq_zero_of_lt (by simp at hk; omega)]; simp), add_zero, hd N hN2]
  obtain rfl : z = (N : ℤ) - m := by omega
  rfl

theorem binomial_indicator_exists [CharZero K] (E : GLOps n K V) (a : Fin n) (m : ℕ)
    (hm : ∀ ν, weightSp E ν ≠ ⊥ → ∀ a, |ν a| ≤ (m : ℤ)) (c : ℤ) :
    ∃ u ∈ binomialDiagonalSubring E, ∀ ν, ∀ x ∈ weightSp E ν, u x = if ν a = c then x else 0 := by
  obtain ⟨d, hd⟩ := newton_interpolation_indicator m c
  obtain ⟨u, hu, hux⟩ := action_finset_sum (E := E) (a := a) (range (2 * m + 1))
    (fun k z => Ring.choose (z + (m : ℤ)) k * d k)
    (fun k _ => action_mul_const (binomial_shifted_action E a m k) (d k))
  refine ⟨u, hu, fun ν x hx => ?_⟩
  rw [hux ν x hx]
  by_cases h0 : weightSp E ν = ⊥
  · have : x = 0 := by rw [h0] at hx; exact (Submodule.mem_bot K).mp hx
    subst this
    simp
  · simp only [hd (ν a) (hm ν h0 a)]
    split_ifs <;> simp

theorem weight_projections_integral_findim [CharZero K] [FiniteDimensional K V] (E : GLOps n K V) : WeightProjectionsIntegralBinomial E := by
  obtain ⟨m, hm⟩ := findim_weights_bounded E
  have h := fun (μ : Fin n → ℤ) (a : Fin n) => binomial_indicator_exists E a m hm (μ a)
  choose u hu hux using h
  refine ⟨fun μ => ((List.finRange n).map (u μ)).prod, fun μ => ?_, fun μ ν x hx => ?_⟩
  · apply Subring.list_prod_mem
    intro y hy
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hy
    exact hu μ a
  · have key : ∀ L : List (Fin n),
        (L.map (u μ)).prod x = if ∀ a ∈ L, ν a = μ a then x else 0 := by
      intro L
      induction L with
      | nil => simp
      | cons b L ih =>
        rw [List.map_cons, List.prod_cons, Module.End.mul_apply, ih]
        by_cases hL : ∀ a ∈ L, ν a = μ a
        · rw [if_pos hL, hux μ b ν x hx]
          by_cases hb : ν b = μ b
          · rw [if_pos hb, if_pos (fun a ha => by rcases List.mem_cons.mp ha with rfl | ha; exacts [hb, hL a ha])]
          · rw [if_neg hb, if_neg (fun h => hb (h b (List.mem_cons.mpr (Or.inl rfl))))]
        · rw [if_neg hL, map_zero, if_neg (fun h => hL fun a ha => h a (List.mem_cons_of_mem _ ha))]
    show ((List.finRange n).map (u μ)).prod x = _
    rw [key]
    by_cases h : ν = μ
    · subst h
      simp
    · rw [if_neg h, if_neg]
      intro h'
      exact h (funext fun a => h' a (List.mem_finRange a))

end Formalism.MainNotions.G.GLWeightTheory
end
end

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem invariant_projection_extremal_formula (D : Formalism.BasicNotions.D7) (h2 : adm2 D) (h5 : adm5 D) {K V : Type} [Field K] [CharZero K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {n : ℕ} (E : GLOps n K V) (hE : IsGLRep E)
    (Inv : Module.End K V) (hInv : IsInvProj E Inv) (π : Module.End K V) (hπ : IsWtProj E 0 π)
    (ord : List (Fin n × Fin n)) (hord : NormalOrder n ord) (T : ℕ) (hT : Module.finrank K V ≤ T) :
    Inv = pp E 0 ord T * π := by
  have hs := gl_rep_shifts_weights hE
  have htop := sum_isotypic_top_of_weight_data D h2 E hE hs (findim_weights_bounded E) (weight_projections_integral_findim E)
  have hinv := trivial_isotypic_invariant_holds hE
  have hkill := nontrivial_isotypic_weight_zero_killed hE hs
  obtain ⟨_, h5b, h5c⟩ := h5 K V n E hE 0 (by
    intro a b hab
    have : (a : ℕ) < (b : ℕ) := hab
    simp only [Pi.zero_apply]
    omega) ord hord T hT
  have hle : ∀ mu, isoSub E mu ≤ LinearMap.eqLocus Inv (pp E 0 ord T * π) := by
    intro mu x hx
    rw [LinearMap.mem_eqLocus, Module.End.mul_apply]
    by_cases hmu : mu = 0
    · subst hmu
      obtain ⟨hx0, hxr⟩ := hinv x hx
      rw [hInv.1 x hx, hπ.1 x hx0, h5c x hx0 hxr]
    · rw [hInv.2 mu hmu x hx, hkill _ π hπ h5b mu hmu x hx]
  have : (⊤ : Submodule K V) ≤ LinearMap.eqLocus Inv (pp E 0 ord T * π) := by
    rw [← htop]
    exact iSup_le hle
  exact LinearMap.ext fun x => this (Submodule.mem_top (x := x))

theorem root_multiple_apply_first {n : ℕ} (a b : Fin n) (hab : a ≠ b) (k : ℕ) : ((k : ℤ) • rootW a b) a = k := by
  simp [rootW, Pi.single_apply, hab]

end Formalism.MainNotions.G.GLWeightTheory
