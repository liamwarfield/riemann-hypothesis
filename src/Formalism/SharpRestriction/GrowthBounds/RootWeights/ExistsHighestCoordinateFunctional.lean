module

public import Formalism.SharpRestriction.GrowthBounds.CovariantDegrees

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.RootWeights.IrreducibleStableContainsEqTop
section -- merged from Formalism.SharpRestriction.GrowthBounds.RootWeights.HighestWeightLatticeOfFirstPart
section -- merged from Formalism.SharpRestriction.GrowthBounds.RootWeights.IntegralEnvelopingPreservesSubmodule
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem dvr_fraction_field_char_zero_prime {p : ℕ} {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (S : UniformizedDVR p O) (hp : p.Prime) : CharZero (KK O) := by
  obtain ⟨w, _, p_mem, p_ne, _⟩ := S
  haveI : CharZero O := by
    obtain ⟨q, hq⟩ := CharP.exists O
    rcases CharP.char_is_prime_or_zero O q with hqp | hq0
    · exfalso
      by_cases hdvd : q ∣ p
      · have hqp' : q = p := (Nat.prime_dvd_prime_iff_eq hqp hp).mp hdvd
        subst hqp'
        exact p_ne (CharP.cast_eq_zero O q)
      · have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hqp).mpr (fun h => hdvd (by subst h; exact dvd_rfl))
        have hu : IsUnit (p : ZMod q) := by
          rw [← ZMod.coe_unitOfCoprime p hcop]; exact Units.isUnit _
        have hu' : IsUnit (p : O) := by
          have h5 := hu.map (ZMod.castHom (dvd_refl q) O)
          simpa using h5
        exact (IsLocalRing.mem_maximalIdeal _).mp p_mem hu'
    · subst hq0
      exact CharP.charP_to_charZero O
  unfold KK
  exact charZero_of_injective_algebraMap (IsFractionRing.injective O (FractionRing O))

section field

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem mem_weightSpace_iff_diag_scalar {E : GLOps n K V} {mu : Fin n → ℤ} {x : V} :
    x ∈ weightSp E mu ↔ ∀ a, E a a x = (mu a : K) • x := by
  unfold weightSp
  simp [Submodule.mem_iInf, sub_eq_zero]

theorem inv_factorial_prod_eq_choose [CharZero K] (m : ℤ) (k : ℕ) :
    ((k.factorial : K)⁻¹) * ∏ j ∈ range k, ((m : K) - (j : K)) = ((Ring.choose m k : ℤ) : K) := by
  have h1 := Ring.descPochhammer_eq_factorial_smul_choose m k
  rw [← Polynomial.eval_eq_smeval, descPochhammer_eval_eq_prod_range, nsmul_eq_mul] at h1
  have h2 := congrArg (fun z : ℤ => (z : K)) h1
  push_cast at h2
  rw [h2, ← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)), one_mul]

theorem binomial_diagonal_on_weight [CharZero K] {E : GLOps n K V} {mu : Fin n → ℤ} {x : V} (hx : x ∈ weightSp E mu)
    (a : Fin n) (k : ℕ) : binomE E a k x = ((Ring.choose (mu a) k : ℤ) : K) • x := by
  have hx' := (mem_weightSpace_iff_diag_scalar.mp hx) a
  unfold binomE
  rw [LinearMap.smul_apply, ← inv_factorial_prod_eq_choose (mu a) k, mul_smul]
  congr 1
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.prod_append, Finset.prod_range_succ]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, Module.End.mul_apply,
      LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, hx']
    rw [← sub_smul, map_smul, ih, smul_smul]
    congr 1
    ring

def shiftedBinomialOperator (E : GLOps n K V) (a : Fin n) (c : ℤ) (d : ℕ) : Module.End K V :=
  ∑ ij ∈ antidiagonal d, ((Ring.choose c ij.2 : ℤ) : K) • binomE E a ij.1

theorem shifted_binomial_on_weight [CharZero K] {E : GLOps n K V} {mu : Fin n → ℤ} {x : V} (hx : x ∈ weightSp E mu)
    (a : Fin n) (c : ℤ) (d : ℕ) : shiftedBinomialOperator E a c d x = ((Ring.choose (mu a + c) d : ℤ) : K) • x := by
  unfold shiftedBinomialOperator
  rw [LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, binomial_diagonal_on_weight hx, smul_smul, ← Finset.sum_smul]
  congr 1
  rw [Ring.add_choose_eq d (Commute.all _ _)]
  push_cast
  apply Finset.sum_congr rfl
  intro ij _
  ring

end field

section lattice

variable {n : ℕ} {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {V : Type*} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]

theorem intCast_smul_mem_submodule (M : Submodule O V) (z : ℤ) {x : V} (hx : x ∈ M) : ((z : ℤ) : KK O) • x ∈ M := by
  rw [Int.cast_smul_eq_zsmul]
  exact zsmul_mem hx z

theorem shifted_binomial_preserves_lattice {E : GLOps n (KK O) V} {M : Submodule O V} (hM : UZStable (O := O) E M) (a : Fin n) (c : ℤ)
    (d : ℕ) {x : V} (hx : x ∈ M) : shiftedBinomialOperator E a c d x ∈ M := by
  unfold UZStable at hM
  unfold shiftedBinomialOperator
  rw [LinearMap.sum_apply]
  apply Submodule.sum_mem
  intro ij _
  rw [LinearMap.smul_apply]
  exact intCast_smul_mem_submodule M _ (hM _ (Or.inr ⟨a, ij.1, rfl⟩) x hx)

theorem lattice_stable_weight_separator [CharZero (KK O)] (E : GLOps n (KK O) V) {lam nu : Fin n → ℤ} (h : nu ≠ lam) :
    ∃ (T : Module.End (KK O) V) (g : (Fin n → ℤ) → ℤ), g lam = 1 ∧ g nu = 0 ∧
      (∀ mu, ∀ x ∈ weightSp E mu, T x = ((g mu : ℤ) : KK O) • x) ∧
      ∀ M : Submodule O V, UZStable (O := O) E M → ∀ x ∈ M, T x ∈ M := by
  have hex : ∃ a, nu a ≠ lam a := by
    by_contra hc
    push_neg at hc
    exact h (funext hc)
  obtain ⟨a, ha⟩ := hex
  rcases lt_or_gt_of_ne ha with hlt | hgt
  · obtain ⟨δ, hδ⟩ : ∃ δ : ℕ, lam a - nu a = δ := ⟨(lam a - nu a).toNat, by omega⟩
    refine ⟨shiftedBinomialOperator E a (-nu a) δ, fun mu => Ring.choose (mu a + -nu a) δ, ?_, ?_, ?_, ?_⟩
    · show Ring.choose (lam a + -nu a) δ = 1
      rw [show lam a + -nu a = (δ : ℤ) by omega, Ring.choose_natCast, Nat.choose_self, Nat.cast_one]
    · show Ring.choose (nu a + -nu a) δ = 0
      rw [show nu a + -nu a = ((0 : ℕ) : ℤ) by simp, Ring.choose_natCast,
        Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]
    · intro mu x hx
      exact shifted_binomial_on_weight hx a (-nu a) δ
    · exact fun M hM x hx => shifted_binomial_preserves_lattice hM a (-nu a) δ hx
  · obtain ⟨δ, hδ⟩ : ∃ δ : ℕ, nu a - lam a = δ := ⟨(nu a - lam a).toNat, by omega⟩
    refine ⟨1 - shiftedBinomialOperator E a (-lam a) δ, fun mu => 1 - Ring.choose (mu a + -lam a) δ, ?_, ?_, ?_, ?_⟩
    · show 1 - Ring.choose (lam a + -lam a) δ = 1
      rw [show lam a + -lam a = ((0 : ℕ) : ℤ) by simp, Ring.choose_natCast,
        Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, sub_zero]
    · show 1 - Ring.choose (nu a + -lam a) δ = 0
      rw [show nu a + -lam a = (δ : ℤ) by omega, Ring.choose_natCast, Nat.choose_self, Nat.cast_one, sub_self]
    · intro mu x hx
      rw [LinearMap.sub_apply, Module.End.one_apply, shifted_binomial_on_weight hx a (-lam a) δ]
      push_cast
      rw [sub_smul, one_smul]
    · intro M hM x hx
      rw [LinearMap.sub_apply, Module.End.one_apply]
      exact M.sub_mem hx (shifted_binomial_preserves_lattice hM a (-lam a) δ hx)

theorem lattice_weight_components_mem [CharZero (KK O)] (E : GLOps n (KK O) V) (M : Submodule O V) (hM : UZStable (O := O) E M)
    (lam : Fin n → ℤ) (F : Finset (Fin n → ℤ)) : lam ∉ F → ∀ (y0 : V) (f : (Fin n → ℤ) → V),
      y0 ∈ weightSp E lam → (∀ nu ∈ F, f nu ∈ weightSp E nu) → y0 + ∑ nu ∈ F, f nu ∈ M → y0 ∈ M := by
  induction F using Finset.induction_on with
  | empty =>
    intro _ y0 f _ _ hmem
    simpa using hmem
  | @insert a F ha ih =>
    intro hl y0 f hy0 hf hmem
    have hal : a ≠ lam := fun h => hl (h ▸ Finset.mem_insert_self a F)
    obtain ⟨T, g', hg1, hg0, hT, hTM⟩ := lattice_stable_weight_separator E hal
    have hlF : lam ∉ F := fun h => hl (Finset.mem_insert_of_mem h)
    have h2 := hTM M hM _ hmem
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_add (f := _), map_sum, Finset.sum_insert ha] at h2
    rw [hT lam y0 hy0, hg1, hT a (f a) (hf a (Finset.mem_insert_self a F)), hg0] at h2
    have h3 : ∀ nu ∈ F, T (f nu) = ((g' nu : ℤ) : KK O) • f nu :=
      fun nu hnu => hT nu (f nu) (hf nu (Finset.mem_insert_of_mem hnu))
    rw [Finset.sum_congr rfl h3] at h2
    simp only [Int.cast_one, one_smul, Int.cast_zero, zero_smul, zero_add] at h2
    exact ih hlF y0 (fun nu => ((g' nu : ℤ) : KK O) • f nu) hy0
      (fun nu hnu => Submodule.smul_mem _ _ (hf nu (Finset.mem_insert_of_mem hnu))) h2

theorem weight_component_decomposition (E : GLOps n (KK O) V) (hE : (⨆ mu : Fin n → ℤ, weightSp E mu) = ⊤) (lam : Fin n → ℤ) (y : V) :
    ∃ (y0 : V) (F : Finset (Fin n → ℤ)) (f : (Fin n → ℤ) → V), lam ∉ F ∧ y0 ∈ weightSp E lam ∧
      (∀ nu ∈ F, f nu ∈ weightSp E nu) ∧ y = y0 + ∑ nu ∈ F, f nu := by
  have hy : y ∈ ⨆ mu : Fin n → ℤ, weightSp E mu := by
    rw [hE]; exact Submodule.mem_top
  obtain ⟨c, hc, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ y).mp hy
  refine ⟨c lam, c.support.erase lam, c, by simp, hc lam, fun nu _ => hc nu, ?_⟩
  rw [← hsum]
  simp only [Finsupp.sum]
  by_cases h : lam ∈ c.support
  · exact (Finset.add_sum_erase _ _ h).symm
  · have h0 : c lam = 0 := by simpa using h
    rw [Finset.erase_eq_self.mpr h, h0, zero_add]

theorem integral_enveloping_preserves_submodule {E : GLOps n (KK O) V} {M : Submodule O V} (hM : UZStable (O := O) E M)
    {u : Module.End (KK O) V} (hu : u ∈ UZmon E) : ∀ x ∈ M, u x ∈ M := by
  unfold UZmon at hu
  unfold UZStable at hM
  induction hu using Submonoid.closure_induction with
  | mem u hu => exact hM u hu
  | one => intro x hx; exact hx
  | mul u v _ _ hu hv => intro x hx; exact hu _ (hv x hx)

theorem sum_other_weights_mem (E : GLOps n (KK O) V) (lam : Fin n → ℤ) (F : Finset (Fin n → ℤ)) (hl : lam ∉ F)
    (f : (Fin n → ℤ) → V) (hf : ∀ nu ∈ F, f nu ∈ weightSp E nu) : ∑ nu ∈ F, f nu ∈ otherWts E lam := by
  unfold otherWts
  apply Submodule.sum_mem
  intro nu hnu
  have hne : nu ≠ lam := fun h => hl (h ▸ hnu)
  exact (le_iSup₂ (f := fun mu (_ : mu ∈ {mu | mu ≠ lam}) => weightSp E mu) nu hne) (hf nu hnu)

theorem highest_weight_lattice_bounds [CharZero (KK O)] (E : GLOps n (KK O) V) (hE : (⨆ mu : Fin n → ℤ, weightSp E mu) = ⊤)
    (lam : Fin n → ℤ) (v : V) (M : Submodule O V) (hM : UZStable (O := O) E M)
    (hl : ∀ x, (x ∈ M ∧ x ∈ weightSp E lam) ↔ ∃ c : O, x = c • v) :
    Delta (O := O) E v ≤ M ∧ (M : Set V) ⊆ Nabla (O := O) E lam v := by
  unfold Delta Nabla
  have hv : v ∈ M := ((hl v).mpr ⟨1, (one_smul O v).symm⟩).1
  constructor
  · rw [Submodule.span_le]
    rintro x ⟨u, hu, rfl⟩
    exact integral_enveloping_preserves_submodule hM hu v hv
  · intro x hx u hu
    have hux : u x ∈ M := integral_enveloping_preserves_submodule hM hu x hx
    obtain ⟨y0, F, f, hlF, hy0, hf, hdec⟩ := weight_component_decomposition E hE lam (u x)
    have hy0M : y0 ∈ M := lattice_weight_components_mem E M hM lam F hlF y0 f hy0 hf (by rw [← hdec]; exact hux)
    obtain ⟨c, hc⟩ := (hl y0).mp ⟨hy0M, hy0⟩
    refine ⟨c, ?_⟩
    rw [algebraMap_smul, hdec, hc, add_sub_cancel_left]
    exact sum_other_weights_mem E lam F hlF f hf

end lattice

end Formalism.MainNotions.G.GLWeightTheory
end
end

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

def LatticeNablaDeltaBound : Prop :=
  ∀ (p n' : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (_S : UniformizedDVR p O),
    AdmissibleDVR p n' O →
    ∀ (n : ℕ) [NeZero n] (lam : Fin n → ℤ) (V : Type) [AddCommGroup V] [Module (KK O) V] [Module O V]
      [IsScalarTower O (KK O) V] (E : GLOps n (KK O) V) (v : V), IsIrrHW E lam v →
      (∀ x ∈ Nabla (O := O) E lam v, ((p : O) ^ (N0 n * deF p n (ellWt lam))) • x ∈ Delta (O := O) E v)

theorem highest_weight_lattice_of_first_part (D : Formalism.BasicNotions.D7) (h : LatticeNablaDeltaBound) : NablaDeltaComparisonField D := by
  intro p n' O _ _ _ S hR n _ lam V _ _ _ _ E v hI
  refine ⟨h p n' O S hR n lam V E v hI, ?_⟩
  intro M hM _ hl
  have := dvr_fraction_field_char_zero_prime S hR.prime
  exact highest_weight_lattice_bounds E hI.1.2.2 lam v M hM.1 hl

end Formalism.MainNotions.G.GLWeightTheory
end
end

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section hw

variable {n : ℕ} {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {V : Type*} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]

theorem gl_rep_commutation_apply {E : GLOps n (KK O) V} (hE : IsGLRep E) (a b c d : Fin n) (x : V) :
    E a b (E c d x) = E c d (E a b x) + (if b = c then E a d x else 0) - (if d = a then E c b x else 0) := by
  unfold IsGLRep at hE
  have h := LinearMap.congr_fun (hE.1 a b c d) x
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  have key : E a b (E c d x) = E c d (E a b x) +
      ((if b = c then E a d else 0) x - (if d = a then E c b else 0) x) := by
    rw [← h]; abel
  rw [key]
  split_ifs <;> (try simp only [LinearMap.zero_apply, sub_zero, add_zero, zero_sub]) <;> abel

theorem gl_rep_operator_weight_shift {E : GLOps n (KK O) V} (hE : IsGLRep E) {mu : Fin n → ℤ} {x : V} (hx : x ∈ weightSp E mu)
    (a b : Fin n) : E a b x ∈ weightSp E (mu + rootW a b) := by
  classical
  simp only [weightSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, sub_eq_zero] at hx ⊢
  intro c
  rw [gl_rep_commutation_apply hE c c a b x, hx c, map_smul]
  simp only [Pi.add_apply, rootW, Pi.sub_apply, Pi.single_apply]
  split_ifs <;> subst_vars <;>
    (try simp only [Int.cast_add, Int.cast_sub, Int.cast_one, Int.cast_zero, add_smul, sub_smul, one_smul,
      zero_smul, smul_zero, sub_zero, add_zero, zero_add, zero_sub]) <;> (try abel) <;> (try simp_all)

theorem mem_weight_sup_exists_finset_sum (E : GLOps n (KK O) V) (Pr : (Fin n → ℤ) → Prop) {x : V}
    (hx : x ∈ ⨆ mu, ⨆ (_ : Pr mu), weightSp E mu) :
    ∃ (F : Finset (Fin n → ℤ)) (f : (Fin n → ℤ) → V), (∀ mu ∈ F, Pr mu ∧ f mu ∈ weightSp E mu) ∧
      x = ∑ mu ∈ F, f mu := by
  classical
  let C : V → Prop := fun y => ∃ (F : Finset (Fin n → ℤ)) (f : (Fin n → ℤ) → V),
    (∀ mu ∈ F, Pr mu ∧ f mu ∈ weightSp E mu) ∧ y = ∑ mu ∈ F, f mu
  have hmem : ∀ mu, ∀ y ∈ ⨆ (_ : Pr mu), weightSp E mu, C y := by
    intro mu y hy
    dsimp only [C]
    by_cases hP : Pr mu
    · refine ⟨{mu}, fun _ => y, ?_, by simp⟩
      intro nu hnu
      rw [Finset.mem_singleton] at hnu
      subst hnu
      rw [iSup_pos hP] at hy
      exact ⟨hP, hy⟩
    · rw [iSup_neg hP] at hy
      refine ⟨∅, fun _ => 0, by simp, ?_⟩
      simp [(Submodule.mem_bot _).mp hy]
  have hzero : C 0 := ⟨∅, fun _ => 0, by simp, by simp⟩
  have hadd : ∀ y z, C y → C z → C (y + z) := by
    intro y z hy hz
    dsimp only [C] at hy hz ⊢
    obtain ⟨F1, f1, h1, rfl⟩ := hy
    obtain ⟨F2, f2, h2, rfl⟩ := hz
    refine ⟨F1 ∪ F2, fun mu => (if mu ∈ F1 then f1 mu else 0) + (if mu ∈ F2 then f2 mu else 0), ?_, ?_⟩
    · intro mu hmu
      have hPr : Pr mu := by
        rcases Finset.mem_union.mp hmu with h | h
        · exact (h1 mu h).1
        · exact (h2 mu h).1
      refine ⟨hPr, Submodule.add_mem _ ?_ ?_⟩
      · split_ifs with h
        · exact (h1 mu h).2
        · exact Submodule.zero_mem _
      · split_ifs with h
        · exact (h2 mu h).2
        · exact Submodule.zero_mem _
    · rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.sum_ite_mem,
        Finset.union_inter_cancel_left, Finset.union_inter_cancel_right]
  first
  | exact Submodule.iSup_induction (motive := C) _ hx hmem hzero hadd
  | exact Submodule.iSup_induction (C := C) _ hx hmem hzero hadd

theorem weight_support_sum_eq_zero [CharZero (KK O)] (E : GLOps n (KK O) V) (Pr : (Fin n → ℤ) → Prop) {nu : Fin n → ℤ} {x : V}
    (hx : x ∈ weightSp E nu) (hx2 : x ∈ ⨆ mu, ⨆ (_ : Pr mu), weightSp E mu) (hn : ¬ Pr nu) : x = 0 := by
  classical
  have hwt : ∀ (a : Fin n) (mu : Fin n → ℤ) (y : V), y ∈ weightSp E mu → E a a y = ((mu a : ℤ) : KK O) • y := by
    intro a mu y hy
    simp only [weightSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply, sub_eq_zero] at hy
    exact hy a
  have key : ∀ (F : Finset (Fin n → ℤ)) (f : (Fin n → ℤ) → V), (∀ mu ∈ F, mu ≠ nu) →
      (∀ mu ∈ F, f mu ∈ weightSp E mu) → ∑ mu ∈ F, f mu ∈ weightSp E nu → ∑ mu ∈ F, f mu = 0 := by
    intro F
    induction F using Finset.induction_on with
    | empty => intro f _ _ _; simp
    | insert mu0 F hmu0 ih =>
      intro f hF hw hs
      have hne : mu0 ≠ nu := hF mu0 (Finset.mem_insert_self _ _)
      obtain ⟨a, ha⟩ : ∃ a, mu0 a ≠ nu a := by
        by_contra h
        push_neg at h
        exact hne (funext h)
      let g : (Fin n → ℤ) → V := fun mu => (((mu a : ℤ) : KK O) - ((mu0 a : ℤ) : KK O)) • f mu
      have hES : ∑ mu ∈ insert mu0 F, E a a (f mu) = ∑ mu ∈ insert mu0 F, ((mu a : ℤ) : KK O) • f mu :=
        Finset.sum_congr rfl (fun mu hmu => hwt a mu (f mu) (hw mu hmu))
      have hkey : (((nu a : ℤ) : KK O) - ((mu0 a : ℤ) : KK O)) • ∑ mu ∈ insert mu0 F, f mu = ∑ mu ∈ F, g mu := by
        have h1 : E a a (∑ mu ∈ insert mu0 F, f mu) = ((nu a : ℤ) : KK O) • ∑ mu ∈ insert mu0 F, f mu :=
          hwt a nu _ hs
        set_option synthInstance.maxHeartbeats 100000 in
          rw [sub_smul, ← h1, map_sum, hES]
        simp only [g, sub_smul, Finset.sum_sub_distrib]
        rw [Finset.sum_insert hmu0, Finset.sum_insert hmu0, smul_add, Finset.smul_sum]
        abel
      have hg : ∀ mu ∈ F, g mu ∈ weightSp E mu := fun mu hmu =>
        Submodule.smul_mem _ _ (hw mu (Finset.mem_insert_of_mem hmu))
      have hF' : ∀ mu ∈ F, mu ≠ nu := fun mu hmu => hF mu (Finset.mem_insert_of_mem hmu)
      have hmemnu : ∑ mu ∈ F, g mu ∈ weightSp E nu := by
        rw [← hkey]
        exact Submodule.smul_mem _ _ hs
      have h0 := ih g hF' hg hmemnu
      rw [← hkey] at h0
      have hc : (((nu a : ℤ) : KK O) - ((mu0 a : ℤ) : KK O)) ≠ 0 := by
        rw [sub_ne_zero]
        exact fun h => ha (Int.cast_injective h).symm
      exact (smul_eq_zero.mp h0).resolve_left hc
  obtain ⟨F, f, hf, rfl⟩ := mem_weight_sup_exists_finset_sum E Pr hx2
  exact key F f (fun mu hmu h => hn (h ▸ (hf mu hmu).1)) (fun mu hmu => (hf mu hmu).2) hx

theorem stable_enveloping_monoid_mem {E : GLOps n (KK O) V} {W : Submodule (KK O) V} (hW : ∀ a b, ∀ y ∈ W, E a b y ∈ W)
    {u : Module.End (KK O) V} (hu : u ∈ Umon E) : ∀ x ∈ W, u x ∈ W := by
  intro x hx
  unfold Umon at hu
  induction hu using Submonoid.closure_induction generalizing x with
  | mem g hg =>
    obtain ⟨ab, rfl⟩ := hg
    exact hW ab.1 ab.2 x hx
  | one => simpa using hx
  | mul g g' _ _ ihg ihg' =>
    exact ihg _ (ihg' x hx)

theorem irreducible_stable_contains_eq_top {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V} (hI : IsIrrHW E lam v)
    {W : Submodule (KK O) V} (hW : ∀ a b, ∀ y ∈ W, E a b y ∈ W) (hv : v ∈ W) : W = ⊤ := by
  have hI' := hI
  unfold IsIrrHW at hI'
  apply eq_top_iff.mpr
  rw [← hI'.2.2.2, Submodule.span_le]
  rintro x ⟨u, hu, rfl⟩
  exact stable_enveloping_monoid_mem hW hu v hv

theorem irreducible_highest_weight_findim {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V} (hI : IsIrrHW E lam v) :
    FiniteDimensional (KK O) V := by
  have hI' := hI
  unfold IsIrrHW IsGLRep at hI'
  obtain ⟨W, hWf, hvW, hWst⟩ := hI'.1.2.1 v
  have hW : W = ⊤ := irreducible_stable_contains_eq_top hI hWst hvW
  subst hW
  exact LinearEquiv.finiteDimensional Submodule.topEquiv

def loweringOperatorMonoid (E : GLOps n (KK O) V) : Submonoid (Module.End (KK O) V) :=
  Submonoid.closure {g | ∃ a b : Fin n, b < a ∧ g = E a b}

theorem irreducible_lowering_span_top {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V} (hI : IsIrrHW E lam v) :
    Submodule.span (KK O) {x | ∃ u ∈ loweringOperatorMonoid E, x = u v} = ⊤ := by
  classical
  have hI' := hI
  unfold IsIrrHW IsHWV at hI'
  obtain ⟨hE, _, ⟨_, hvw, hraise⟩, _⟩ := hI'
  have hvw' : ∀ a, E a a v = ((lam a : ℤ) : KK O) • v := by
    simp only [weightSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply, sub_eq_zero] at hvw
    exact hvw
  have hvS : ∀ u ∈ loweringOperatorMonoid E, u v ∈ Submodule.span (KK O) {x | ∃ u ∈ loweringOperatorMonoid E, x = u v} := fun u hu => Submodule.subset_span ⟨u, hu, rfl⟩
  have hv1 : v ∈ Submodule.span (KK O) {x | ∃ u ∈ loweringOperatorMonoid E, x = u v} := hvS 1 (Submonoid.one_mem _)
  have hlow : ∀ c d : Fin n, d < c → ∀ y ∈ Submodule.span (KK O) {x | ∃ u ∈ loweringOperatorMonoid E, x = u v}, E c d y ∈ Submodule.span (KK O) {x | ∃ u ∈ loweringOperatorMonoid E, x = u v} := by
    intro c d hdc y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨u, hu, rfl⟩ := hz
      apply Submodule.subset_span
      refine ⟨E c d * u, Submonoid.mul_mem _ ?_ hu, rfl⟩
      unfold loweringOperatorMonoid
      exact Submonoid.subset_closure ⟨c, d, hdc, rfl⟩
    | zero => simp
    | add y z _ _ hy hz => rw [map_add (f := _)]; exact Submodule.add_mem _ hy hz
    | smul r y _ hy => rw [map_smul]; exact Submodule.smul_mem _ r hy
  have hall : ∀ u ∈ loweringOperatorMonoid E, ∀ a b, E a b (u v) ∈ Submodule.span (KK O) {x | ∃ u ∈ loweringOperatorMonoid E, x = u v} := by
    intro u hu
    unfold loweringOperatorMonoid at hu
    induction hu using Submonoid.closure_induction_left with
    | one =>
      intro a b
      rw [Module.End.one_apply]
      rcases lt_trichotomy a b with hab | rfl | hab
      · rw [hraise a b hab]
        exact Submodule.zero_mem _
      · rw [hvw' a]
        exact Submodule.smul_mem _ _ hv1
      · exact hlow a b hab v hv1
    | mul_left g hg u' _ ih =>
      intro a b
      obtain ⟨c, d, hdc, rfl⟩ := hg
      rw [Module.End.mul_apply, gl_rep_commutation_apply hE a b c d]
      refine Submodule.sub_mem _ (Submodule.add_mem _ (hlow c d hdc _ (ih a b)) ?_) ?_
      · split_ifs
        · exact ih a d
        · exact Submodule.zero_mem _
      · split_ifs
        · exact ih c b
        · exact Submodule.zero_mem _
  have hstab : ∀ a b, ∀ y ∈ Submodule.span (KK O) {x | ∃ u ∈ loweringOperatorMonoid E, x = u v}, E a b y ∈ Submodule.span (KK O) {x | ∃ u ∈ loweringOperatorMonoid E, x = u v} := by
    intro a b y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨u, hu, rfl⟩ := hz
      exact hall u hu a b
    | zero => simp
    | add y z _ _ hy hz => rw [map_add (f := _)]; exact Submodule.add_mem _ hy hz
    | smul r y _ hy => rw [map_smul]; exact Submodule.smul_mem _ r hy
  exact irreducible_stable_contains_eq_top hI hstab hv1

end hw

end Formalism.MainNotions.G.GLWeightTheory
end
end

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section hw

variable {n : ℕ} {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {V : Type*} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]

def weightHeightAscending (nu : Fin n → ℤ) : ℤ := ∑ c : Fin n, ((c : ℕ) : ℤ) * nu c

theorem weightHeightAscending_add_root (nu : Fin n → ℤ) (a b : Fin n) :
    weightHeightAscending (nu + rootW a b) = weightHeightAscending nu + (((a : ℕ) : ℤ) - ((b : ℕ) : ℤ)) := by
  unfold weightHeightAscending rootW
  simp only [Pi.add_apply, Pi.sub_apply, mul_add, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

theorem irreducible_lowering_word_weight [NeZero n] {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V} (hI : IsIrrHW E lam v)
    {u : Module.End (KK O) V} (hu : u ∈ loweringOperatorMonoid E) :
    ∃ nu, u v ∈ weightSp E nu ∧ ((nu = lam ∧ u v = v) ∨ weightHeightAscending lam < weightHeightAscending nu) ∧
      nu 0 ≤ lam 0 ∧ lam (lastIdx n) ≤ nu (lastIdx n) := by
  have hE : IsGLRep E := hI.1
  have hv : v ∈ weightSp E lam := hI.2.2.1.2.1
  unfold loweringOperatorMonoid at hu
  induction hu using Submonoid.closure_induction_left with
  | one => exact ⟨lam, hv, Or.inl ⟨rfl, rfl⟩, le_rfl, le_rfl⟩
  | mul_left g hg w _ ih =>
    obtain ⟨a, b, hba, rfl⟩ := hg
    obtain ⟨nu, hnu, hor, h0, hl⟩ := ih
    refine ⟨nu + rootW a b, gl_rep_operator_weight_shift hE hnu a b, Or.inr ?_, ?_, ?_⟩
    · have hab : ((b : ℕ) : ℤ) < ((a : ℕ) : ℤ) := by exact_mod_cast hba
      rw [weightHeightAscending_add_root]
      rcases hor with ⟨rfl, -⟩ | h
      · linarith
      · linarith
    · have ha0 : a ≠ 0 := by
        intro h; rw [h] at hba; exact absurd hba (Fin.not_lt_zero _)
      have : (nu + rootW a b) 0 ≤ nu 0 := by
        simp only [rootW, Pi.add_apply, Pi.sub_apply, Pi.single_apply, if_neg (Ne.symm ha0)]
        split_ifs <;> omega
      exact this.trans h0
    · have hbl : b ≠ lastIdx n := by
        intro h
        have : (a : ℕ) ≤ n - 1 := Nat.le_sub_one_of_lt a.isLt
        have hb : (b : ℕ) = n - 1 := by rw [h]; rfl
        have : (b : ℕ) < (a : ℕ) := hba
        omega
      have : nu (lastIdx n) ≤ (nu + rootW a b) (lastIdx n) := by
        simp only [rootW, Pi.add_apply, Pi.sub_apply, Pi.single_apply, if_neg (Ne.symm hbl)]
        split_ifs <;> omega
      exact hl.trans this

theorem top_le_line_sup_higher_weights [NeZero n] {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V} (hI : IsIrrHW E lam v) :
    (⊤ : Submodule (KK O) V) ≤ Submodule.span (KK O) {v} ⊔ ⨆ nu, ⨆ (_ : weightHeightAscending lam < weightHeightAscending nu), weightSp E nu := by
  rw [← irreducible_lowering_span_top hI, Submodule.span_le]
  rintro x ⟨u, hu, rfl⟩
  obtain ⟨nu, hnu, h1 | h1, -⟩ := irreducible_lowering_word_weight hI hu
  · rw [h1.2]
    exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self v)
  · exact Submodule.mem_sup_right (Submodule.mem_iSup_of_mem nu (Submodule.mem_iSup_of_mem h1 hnu))

theorem top_le_end_bounded_weights [NeZero n] {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V} (hI : IsIrrHW E lam v) :
    (⊤ : Submodule (KK O) V) ≤ ⨆ nu, ⨆ (_ : nu 0 ≤ lam 0 ∧ lam (lastIdx n) ≤ nu (lastIdx n)), weightSp E nu := by
  rw [← irreducible_lowering_span_top hI, Submodule.span_le]
  rintro x ⟨u, hu, rfl⟩
  obtain ⟨nu, hnu, -, h0, hl⟩ := irreducible_lowering_word_weight hI hu
  exact Submodule.mem_iSup_of_mem nu (Submodule.mem_iSup_of_mem ⟨h0, hl⟩ hnu)

theorem irreducible_weight_end_bounds [NeZero n] [CharZero (KK O)] {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V}
    (hI : IsIrrHW E lam v) {nu : Fin n → ℤ} {x : V} (hx : x ∈ weightSp E nu) (h0 : x ≠ 0) :
    nu 0 ≤ lam 0 ∧ lam (lastIdx n) ≤ nu (lastIdx n) := by
  by_contra hn
  exact h0 (weight_support_sum_eq_zero E (fun mu => mu 0 ≤ lam 0 ∧ lam (lastIdx n) ≤ mu (lastIdx n)) hx
    (top_le_end_bounded_weights hI Submodule.mem_top) hn)

theorem irreducible_highest_weight_line [NeZero n] [CharZero (KK O)] {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V}
    (hI : IsIrrHW E lam v) {x : V} (hx : x ∈ weightSp E lam) : ∃ c : KK O, x = c • v := by
  have hx2 := top_le_line_sup_higher_weights hI (Submodule.mem_top (x := x))
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx2
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
  have hv : v ∈ weightSp E lam := hI.2.2.1.2.1
  have hzw : z ∈ weightSp E lam := by
    have e : z = (c • v + z) - c • v := by abel
    rw [e]
    exact Submodule.sub_mem _ hx (Submodule.smul_mem _ c hv)
  have hz0 : z = 0 := weight_support_sum_eq_zero E (fun nu => weightHeightAscending lam < weightHeightAscending nu) hzw hz (lt_irrefl _)
  exact ⟨c, by rw [hz0, add_zero]⟩

theorem highest_line_isCompl_other_weights [NeZero n] [CharZero (KK O)] {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V}
    (hI : IsIrrHW E lam v) : IsCompl (Submodule.span (KK O) {v}) (otherWts E lam) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx hx2
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    exact weight_support_sum_eq_zero E (fun mu => mu ∈ {mu | mu ≠ lam}) (Submodule.smul_mem _ c hI.2.2.1.2.1) hx2
      (fun h => h rfl)
  · rw [codisjoint_iff, eq_top_iff, ← hI.1.2.2, iSup_le_iff]
    intro mu x hx
    by_cases h : mu = lam
    · subst h
      obtain ⟨c, rfl⟩ := irreducible_highest_weight_line hI hx
      exact Submodule.mem_sup_left (Submodule.smul_mem _ c (Submodule.mem_span_singleton_self v))
    · apply Submodule.mem_sup_right
      show x ∈ ⨆ mu ∈ {mu | mu ≠ lam}, weightSp E mu
      exact Submodule.mem_iSup_of_mem mu (Submodule.mem_iSup_of_mem h hx)

theorem exists_highest_coordinate_functional [NeZero n] [CharZero (KK O)] {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V}
    (hI : IsIrrHW E lam v) : ∃ xi : V →ₗ[KK O] KK O, xi v = 1 ∧ (∀ w ∈ otherWts E lam, xi w = 0) ∧
      ∀ x, x - xi x • v ∈ otherWts E lam := by
  have hc := highest_line_isCompl_other_weights hI
  have hv0 : v ≠ 0 := hI.2.2.1.1
  let P := Submodule.linearProjOfIsCompl _ _ hc
  let e := LinearEquiv.toSpanNonzeroSingleton (KK O) V v hv0
  refine ⟨e.symm.toLinearMap ∘ₗ P, ?_, ?_, ?_⟩
  · have h1 : P v = ⟨v, Submodule.mem_span_singleton_self v⟩ :=
      Submodule.linearProjOfIsCompl_apply_left hc ⟨v, Submodule.mem_span_singleton_self v⟩
    show e.symm (P v) = 1
    rw [h1, LinearEquiv.symm_apply_eq, LinearEquiv.toSpanNonzeroSingleton_one]
  · intro w hw
    have h2 : P w = 0 := Submodule.linearProjOfIsCompl_apply_right hc ⟨w, hw⟩
    show e.symm (P w) = 0
    rw [h2, map_zero]
  · intro x
    have h8 : ∀ s : KK O, ((e s : Submodule.span (KK O) {v}) : V) = s • v := fun s => by
      first
        | rfl
        | simp [e, LinearEquiv.toSpanNonzeroSingleton_apply]
    have h3 : (e.symm (P x)) • v = (P x : V) := by
      rw [← h8, LinearEquiv.apply_symm_apply]
    show x - (e.symm (P x)) • v ∈ otherWts E lam
    rw [h3]
    have hPP : P (P x : V) = P x := Submodule.linearProjOfIsCompl_apply_left hc (P x)
    have h5 : P (x - (P x : V)) = 0 := by
      rw [map_sub, hPP, sub_self]
    have h6 := LinearMap.mem_ker.mpr h5
    have h7 := Submodule.linearProjOfIsCompl_ker hc
    rw [SetLike.ext_iff] at h7
    exact (h7 _).mp h6

end hw

end Formalism.MainNotions.G.GLWeightTheory
