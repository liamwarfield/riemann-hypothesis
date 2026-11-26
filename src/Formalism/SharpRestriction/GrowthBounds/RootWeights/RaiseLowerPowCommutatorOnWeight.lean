module

public import Lemmata.ClearingDenominators.UmonLeUzmon
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.WeightEntriesBetweenExtremeHighest

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.RootWeights.HeisenbergDividedPowerExpansion
section -- merged from Formalism.SharpRestriction.GrowthBounds.RootWeights.RestAOfHighestVectorIntegrality
section -- merged from Formalism.SharpRestriction.GrowthBounds.RootWeights.ExistsScalarMultipleMemDelta
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section hw

variable {n : ℕ} {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {V : Type*} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]

theorem delta_le_nabla {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V}
    (hK : v ∈ Nabla (O := O) E lam v) : Delta (O := O) E v ≤ NablaSub (O := O) E lam v := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨u', hu', rfl⟩ u hu
  have := hK (u * u') (Submonoid.mul_mem _ hu hu')
  simpa using this

theorem integral_enveloping_span_top {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V} (hI : IsIrrHW E lam v) :
    Submodule.span (KK O) {x | ∃ u ∈ UZmon E, x = u v} = ⊤ := by
  rw [eq_top_iff, ← hI.2.2.2]
  refine Submodule.span_mono ?_
  rintro x ⟨u, hu, rfl⟩
  exact ⟨u, enveloping_le_integral_enveloping E hu, rfl⟩

theorem nabla_to_delta_maps_fg [NeZero n] [CharZero (KK O)] [FiniteDimensional (KK O) V] {E : GLOps n (KK O) V}
    {lam : Fin n → ℤ} {v : V} (hI : IsIrrHW E lam v)
    (hCR : ∀ W : Submodule (KK O) V, (∀ a b, ∀ x ∈ W, E a b x ∈ W) →
      ∃ W' : Submodule (KK O) V, IsCompl W W' ∧ ∀ a b, ∀ x ∈ W', E a b x ∈ W')
    {xi : V →ₗ[KK O] KK O} (h1 : xi v = 1)
    (h2 : ∀ w ∈ otherWts E lam, xi w = 0) (h3 : ∀ x, x - xi x • v ∈ otherWts E lam)
    (hK : v ∈ Nabla (O := O) E lam v) : (nablaToDeltaMaps (O := O) E lam v).FG := by
  refine lattice_fg_of_integral_functionals (O := O) (W := Module.End (KK O) V) _
    {φ | ∃ u ∈ UZmon E, ∃ u' ∈ UZmon E, φ = (xi ∘ₗ u) ∘ₗ LinearMap.applyₗ (u' v)} ?_ ?_
  · intro f hf
    have hz : ∀ u' ∈ UZmon E, f (u' v) = 0 := by
      intro u' hu'
      refine enveloping_coordinate_separates hI hCR h1 fun u hu => ?_
      have := hf _ ⟨u, hu, u', hu', rfl⟩
      simpa using this
    have hk : (⊤ : Submodule (KK O) V) ≤ LinearMap.ker f := by
      rw [← integral_enveloping_span_top hI]
      refine Submodule.span_le.2 ?_
      rintro x ⟨u, hu, rfl⟩
      exact hz u hu
    exact LinearMap.ext fun x => hk Submodule.mem_top
  · rintro φ ⟨u, hu, u', hu', rfl⟩ f hf
    have ha : u' v ∈ Nabla (O := O) E lam v := delta_le_nabla hK (Submodule.subset_span ⟨u', hu', rfl⟩)
    have hb : f (u' v) ∈ Nabla (O := O) E lam v := delta_le_nabla hK (hf _ ha)
    obtain ⟨c, hc⟩ := (mem_nabla_iff_coordinate_integral h1 h2 h3 _).1 hb u hu
    exact ⟨c, by simpa using hc⟩

theorem nabla_finitely_generated [NeZero n] [CharZero (KK O)] [FiniteDimensional (KK O) V] {E : GLOps n (KK O) V}
    {lam : Fin n → ℤ} {v : V} (hI : IsIrrHW E lam v)
    (hCR : ∀ W : Submodule (KK O) V, (∀ a b, ∀ x ∈ W, E a b x ∈ W) →
      ∃ W' : Submodule (KK O) V, IsCompl W W' ∧ ∀ a b, ∀ x ∈ W', E a b x ∈ W')
    {xi : V →ₗ[KK O] KK O} (h1 : xi v = 1)
    (h2 : ∀ w ∈ otherWts E lam, xi w = 0) (h3 : ∀ x, x - xi x • v ∈ otherWts E lam) :
    (NablaSub (O := O) E lam v).FG := by
  refine lattice_fg_of_integral_functionals (O := O) (W := V) _ {φ | ∃ u ∈ UZmon E, φ = xi ∘ₗ u} ?_ ?_
  · intro x hx
    refine enveloping_coordinate_separates hI hCR h1 fun u hu => ?_
    have := hx _ ⟨u, hu, rfl⟩
    simpa using this
  · rintro φ ⟨u, hu, rfl⟩ x hx
    obtain ⟨c, hc⟩ := (mem_nabla_iff_coordinate_integral h1 h2 h3 _).1 hx u hu
    exact ⟨c, by simpa using hc⟩

theorem exists_scalar_multiple_mem_delta {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V} (hI : IsIrrHW E lam v) (y : V) :
    ∃ o : O, o ≠ 0 ∧ o • y ∈ Delta (O := O) E v := by
  first | exact Bl.ClearingDenominators.goal1 .. | (apply Bl.ClearingDenominators.goal1 <;> assumption) | (intros; apply Bl.ClearingDenominators.goal1 <;> assumption) | (apply @Bl.ClearingDenominators.goal1 <;> assumption) | (intros; apply @Bl.ClearingDenominators.goal1 <;> assumption) | (apply @Bl.ClearingDenominators.goal1 <;> first | assumption | infer_instance)

theorem nabla_to_delta_maps_span_top [NeZero n] [CharZero (KK O)] [FiniteDimensional (KK O) V] {E : GLOps n (KK O) V}
    {lam : Fin n → ℤ} {v : V} (hI : IsIrrHW E lam v)
    (hfg : (NablaSub (O := O) E lam v).FG) : MQ (K := KK O) (nablaToDeltaMaps (O := O) E lam v) = ⊤ := by
  classical
  rw [eq_top_iff]
  intro f _
  obtain ⟨G, hG⟩ := hfg
  choose o ho ho' using exists_scalar_multiple_mem_delta (O := O) hI
  set c : O := ∏ g ∈ G, o (f g) with hc
  have hc0 : c ≠ 0 := prod_ne_zero_iff.2 fun g _ => ho _
  have hmem : c • f ∈ nablaToDeltaMaps (O := O) E lam v := by
    intro x hx
    have hx' : x ∈ Submodule.span O (G : Set V) := hG ▸ hx
    clear hx
    induction hx' using Submodule.span_induction with
    | mem g hg =>
      rw [LinearMap.smul_apply, hc, ← mul_prod_erase G _ hg, mul_comm, mul_smul]
      exact Submodule.smul_mem _ _ (ho' _)
    | zero => simp
    | add y z _ _ hy hz => rw [map_add (f := _)]; exact Submodule.add_mem _ hy hz
    | smul r y _ hy =>
      rw [← algebraMap_smul (KK O) r y, map_smul, algebraMap_smul]; exact Submodule.smul_mem _ _ hy
  have hc1 : algebraMap O (KK O) c ≠ 0 := by
    simpa using (IsFractionRing.injective O (KK O)).ne hc0
  have : f = (algebraMap O (KK O) c)⁻¹ • (c • f) := by
    rw [← algebraMap_smul (KK O) c f, smul_smul, inv_mul_cancel₀ hc1, one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

theorem coordinate_rank_one_mem_maps {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V} {xi : V →ₗ[KK O] KK O} (h1 : xi v = 1)
    (h2 : ∀ w ∈ otherWts E lam, xi w = 0) (h3 : ∀ x, x - xi x • v ∈ otherWts E lam) :
    xi.smulRight v ∈ nablaToDeltaMaps (O := O) E lam v := by
  intro x hx
  obtain ⟨c, hc⟩ := (mem_nabla_iff_coordinate_integral h1 h2 h3 _).1 hx 1 (Submonoid.one_mem _)
  rw [Module.End.one_apply] at hc
  rw [LinearMap.smulRight_apply, hc, algebraMap_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, Submonoid.one_mem _, rfl⟩)

end hw

end Formalism.MainNotions.G.GLWeightTheory
end
end

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

def HighestWeightVectorIntegrality : Prop :=
  ∀ (p n' : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (_S : UniformizedDVR p O),
    AdmissibleDVR p n' O →
    ∀ (n : ℕ) [NeZero n] (lam : Fin n → ℤ) (V : Type) [AddCommGroup V] [Module (KK O) V] [Module O V]
      [IsScalarTower O (KK O) V] (E : GLOps n (KK O) V) (v : V), IsIrrHW E lam v →
      v ∈ Nabla (O := O) E lam v

end Formalism.MainNotions.G.GLWeightTheory
end
end

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem weighted_sum_shift_recombine {K M : Type*} [Field K] [AddCommGroup M] [Module K M] (c c' r : ℕ → K) (B : ℕ → M) (k : ℕ)
    (h0 : c' 0 = c 0) (hs : ∀ j, j < k + 1 → c' (j + 1) = c (j + 1) + c j * r j) (hz : c (k + 1) = 0) :
    ∑ j ∈ range (k + 1), c j • (B j + r j • B (j + 1)) = ∑ j ∈ range (k + 2), c' j • B j := by
  rw [Finset.sum_range_succ' (fun j => c' j • B j), h0]
  have e1 : ∑ j ∈ range (k + 1), c' (j + 1) • B (j + 1) =
      ∑ j ∈ range (k + 1), (c (j + 1) • B (j + 1) + (c j * r j) • B (j + 1)) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [hs j (Finset.mem_range.mp hj), add_smul]
  rw [e1, Finset.sum_add_distrib]
  have e2 : ∑ j ∈ range (k + 1), c j • (B j + r j • B (j + 1)) =
      ∑ j ∈ range (k + 1), c j • B j + ∑ j ∈ range (k + 1), (c j * r j) • B (j + 1) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [smul_add, smul_smul]
  rw [e2]
  have e3 : ∑ j ∈ range (k + 1), c j • B j =
      c 0 • B 0 + ∑ j ∈ range (k + 1), c (j + 1) • B (j + 1) := by
    rw [Finset.sum_range_succ (fun j => c (j + 1) • B (j + 1)), hz, zero_smul, add_zero,
      Finset.sum_range_succ' (fun j => c j • B j)]
    abel
  rw [e3]
  abel

section Heisenberg₂

variable {K A : Type*} [Field K] [CharZero K] [Ring A] [Algebra K A]

theorem heisenberg_mul_pow_commutator {X Y Z : A} (hZ : X * Y = Y * X + Z) (hZY : Z * Y = Y * Z) (m : ℕ) :
    X * Y ^ m = Y ^ m * X + (m : K) • (Y ^ (m - 1) * Z) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have e1 : X * Y ^ (m + 1) = (X * Y ^ m) * Y := by rw [pow_succ, mul_assoc]
    have e2 : Y ^ (m - 1) * Z * Y = Y ^ (m - 1) * Y * Z := by rw [mul_assoc, hZY, ← mul_assoc]
    rw [e1, ih, add_mul, mul_assoc (Y ^ m) X Y, hZ, smul_mul_assoc, e2, mul_add, ← mul_assoc, ← pow_succ]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · rw [← pow_succ, Nat.sub_add_cancel hm]
      simp only [Nat.add_sub_cancel, Nat.cast_succ, add_smul, one_smul]
      abel

theorem heisenberg_pow_mul_pow_expansion {X Y Z : A} (hZ : X * Y = Y * X + Z) (hZY : Z * Y = Y * Z) (hZX : X * Z = Z * X) (k l : ℕ) :
    X ^ k * Y ^ l = ∑ j ∈ range (k + 1),
      (((k.choose j * l.descFactorial j : ℕ) : K)) • (Y ^ (l - j) * Z ^ j * X ^ (k - j)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hc : ∀ j : ℕ, Commute X (Z ^ j) := fun j => Commute.pow_right (show Commute X Z from hZX) j
    have step : ∀ j ∈ range (k + 1),
        X * ((((k.choose j * l.descFactorial j : ℕ)) : K) • (Y ^ (l - j) * Z ^ j * X ^ (k - j))) =
        (((k.choose j * l.descFactorial j : ℕ)) : K) • (Y ^ (l - j) * Z ^ j * X ^ (k + 1 - j) +
          (((l - j : ℕ)) : K) • (Y ^ (l - (j + 1)) * Z ^ (j + 1) * X ^ (k + 1 - (j + 1)))) := by
      intro j hj
      have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      rw [mul_smul_comm]
      congr 1
      rw [← mul_assoc, ← mul_assoc, heisenberg_mul_pow_commutator (K := K) hZ hZY (l - j), add_mul, add_mul,
        smul_mul_assoc, smul_mul_assoc]
      congr 1
      · simp only [mul_assoc]
        rw [← mul_assoc X (Z ^ j), (hc j).eq, mul_assoc (Z ^ j), ← pow_succ',
          show k - j + 1 = k + 1 - j by omega]
      · congr 1
        rw [show l - (j + 1) = l - j - 1 by omega, show k + 1 - (j + 1) = k - j by omega,
          mul_assoc (Y ^ (l - j - 1)) Z, ← pow_succ']
    rw [pow_succ', mul_assoc, ih, Finset.mul_sum, Finset.sum_congr rfl step]
    exact weighted_sum_shift_recombine (fun j => ((k.choose j * l.descFactorial j : ℕ) : K))
      (fun j => (((k + 1).choose j * l.descFactorial j : ℕ) : K)) (fun j => ((l - j : ℕ) : K))
      (fun j => Y ^ (l - j) * Z ^ j * X ^ (k + 1 - j)) k (by simp)
      (fun j _ => by
        have e : (k + 1).choose (j + 1) * l.descFactorial (j + 1) =
            k.choose (j + 1) * l.descFactorial (j + 1) + k.choose j * l.descFactorial j * (l - j) := by
          rw [Nat.choose_succ_succ, Nat.descFactorial_succ]; ring
        rw [e]
        push_cast
        ring)
      (by simp [Nat.choose_succ_self])

def dividedPower (K : Type*) [Field K] {A : Type*} [Ring A] [Algebra K A] (X : A) (k : ℕ) : A := ((k.factorial : K)⁻¹) • X ^ k

theorem heisenberg_dividedPower_expansion {X Y Z : A} (hZ : X * Y = Y * X + Z) (hZY : Z * Y = Y * Z) (hZX : X * Z = Z * X) (k l : ℕ) :
    dividedPower K X k * dividedPower K Y l = ∑ j ∈ range (k + 1),
      if j ≤ l then dividedPower K Y (l - j) * dividedPower K Z j * dividedPower K X (k - j) else 0 := by
  unfold dividedPower
  rw [smul_mul_smul_comm, heisenberg_pow_mul_pow_expansion (K := K) hZ hZY hZX, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  split_ifs with hjl
  · rw [smul_smul, smul_mul_smul_comm, smul_mul_smul_comm]
    congr 1
    have h1 : ((k.factorial : ℕ) : K) = (k.choose j : K) * j.factorial * (k - j).factorial := by
      exact_mod_cast (Nat.choose_mul_factorial_mul_factorial hjk).symm
    have h2 : ((l.factorial : ℕ) : K) = ((l - j).factorial : K) * l.descFactorial j := by
      exact_mod_cast (Nat.factorial_mul_descFactorial hjl).symm
    have h3 : (k.choose j : K) ≠ 0 := by exact_mod_cast (Nat.choose_pos hjk).ne'
    have h4 : (l.descFactorial j : K) ≠ 0 := by
      exact_mod_cast (Nat.descFactorial_eq_zero_iff_lt.not.mpr (by omega))
    have h5 : (j.factorial : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have h6 : ((k - j).factorial : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have h7 : ((l - j).factorial : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    rw [h1, h2]
    push_cast
    field_simp
  · have h0 : l.descFactorial j = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
    simp [h0]

end Heisenberg₂

end Formalism.MainNotions.G.GLWeightTheory
end
end

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem descPochhammer_succ_eval_right (j : ℕ) (x : ℤ) :
    (descPochhammer ℤ (j + 1)).eval x = (descPochhammer ℤ j).eval x * (x - j) := by
  rw [descPochhammer_succ_right]
  simp

theorem descPochhammer_succ_eval_add_one (j : ℕ) (x : ℤ) :
    (descPochhammer ℤ (j + 1)).eval (x + 1) = (x + 1) * (descPochhammer ℤ j).eval x := by
  rw [descPochhammer_succ_left]
  simp

section hw

variable {n : ℕ} {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {V : Type*} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]

theorem raise_lower_commutator_on_weight {E : GLOps n (KK O) V} (hE : IsGLRep E) {a b : Fin n} {mu : Fin n → ℤ} {z : V}
    (hz : z ∈ weightSp E mu) : E a b (E b a z) = E b a (E a b z) + (((mu a - mu b : ℤ)) : KK O) • z := by
  have hz' : z ∈ ⨅ c, LinearMap.ker (E c c - ((mu c : ℤ) : KK O) • (1 : Module.End (KK O) V)) := hz
  have hw : ∀ c, E c c z = ((mu c : ℤ) : KK O) • z := by
    intro c
    have h := (Submodule.mem_iInf _).mp hz' c
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
      sub_eq_zero] at h
    exact h
  have hc := congrArg (fun f : Module.End (KK O) V => f z) (hE.1 a b b a)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, if_true, eq_self_iff_true] at hc
  rw [hw a, hw b] at hc
  rw [← sub_eq_iff_eq_add', hc, Int.cast_sub, sub_smul]

theorem raise_lower_pow_commutator_on_weight {E : GLOps n (KK O) V} (hE : IsGLRep E) {a b : Fin n} (hab : a ≠ b) {mu : Fin n → ℤ} {z : V}
    (hz : z ∈ weightSp E mu) (r : ℕ) :
    E a b (((E b a) ^ r) z) = ((E b a) ^ r) (E a b z) +
      ((r : KK O) * ((((mu a - mu b : ℤ)) : KK O) - r + 1)) • ((E b a) ^ (r - 1)) z := by
  induction r with
  | zero => simp
  | succ r ih =>
    have e1 : ∀ s x, E b a (((E b a) ^ s) x) = ((E b a) ^ (s + 1)) x := by
      intro s x
      rw [pow_succ', Module.End.mul_apply]
    have hy := integral_operator_pow_shifts_weight hE hz b a r
    have h0 := raise_lower_commutator_on_weight (a := a) (b := b) hE hy
    have hA : (mu + (r : ℤ) • rootW b a) a = mu a - r := by
      simp [rootW, Pi.single_apply, hab, hab.symm] <;> ring
    have hB : (mu + (r : ℤ) • rootW b a) b = mu b + r := by
      simp [rootW, Pi.single_apply, hab, hab.symm] <;> ring
    rw [hA, hB] at h0
    have e2 : ((r : KK O) * ((((mu a - mu b : ℤ)) : KK O) - r + 1)) • E b a (((E b a) ^ (r - 1)) z) =
        ((r : KK O) * ((((mu a - mu b : ℤ)) : KK O) - r + 1)) • ((E b a) ^ r) z := by
      rcases Nat.eq_zero_or_pos r with h | h
      · subst h
        simp
      · rw [e1, Nat.sub_add_cancel h]
    rw [← e1, h0, ih, map_add (f := _), map_smul, e1, e2, Nat.add_sub_cancel, add_assoc, ← add_smul]
    congr 2
    push_cast
    ring

theorem raise_pow_lower_pow_expansion {E : GLOps n (KK O) V} (hE : IsGLRep E) {a b : Fin n} (hab : a ≠ b) {nu : Fin n → ℤ} {y : V}
    (hy : y ∈ weightSp E nu) (k l : ℕ) :
    ((E a b) ^ k) (((E b a) ^ l) y) = ∑ j ∈ range (k + 1),
      ((((k.choose j * l.descFactorial j : ℕ)) : KK O) *
        (((descPochhammer ℤ j).eval (nu a - nu b + k - l) : ℤ) : KK O)) •
        ((E b a) ^ (l - j)) (((E a b) ^ (k - j)) y) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have step : ∀ j ∈ range (k + 1),
        E a b (((E b a) ^ (l - j)) (((E a b) ^ (k - j)) y)) =
          ((E b a) ^ (l - j)) (((E a b) ^ (k + 1 - j)) y) +
          (((l - j : ℕ) : KK O) * (((((nu + ((k - j : ℕ) : ℤ) • rootW a b) a -
              (nu + ((k - j : ℕ) : ℤ) • rootW a b) b : ℤ)) : KK O) - ((l - j : ℕ) : KK O) + 1)) •
            ((E b a) ^ (l - (j + 1))) (((E a b) ^ (k + 1 - (j + 1))) y) := by
      intro j hj
      have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have hw := integral_operator_pow_shifts_weight hE hy a b (k - j)
      rw [raise_lower_pow_commutator_on_weight hE hab hw (l - j)]
      congr 1
      · rw [← Module.End.mul_apply (E a b), ← pow_succ', show k - j + 1 = k + 1 - j by omega]
      · rw [show l - j - 1 = l - (j + 1) by omega, show k + 1 - (j + 1) = k - j by omega]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [pow_succ', Module.End.mul_apply, ih, map_sum]
    simp only [map_smul]
    refine (Finset.sum_congr rfl (fun j hj => ?_)).trans
      (weighted_sum_shift_recombine (fun j => ((k.choose j * l.descFactorial j : ℕ) : KK O) *
          (((descPochhammer ℤ j).eval (nu a - nu b + k - l) : ℤ) : KK O))
        (fun j => (((k + 1).choose j * l.descFactorial j : ℕ) : KK O) *
          (((descPochhammer ℤ j).eval (nu a - nu b + ((k + 1 : ℕ) : ℤ) - l) : ℤ) : KK O))
        (fun j => ((l - j : ℕ) : KK O) * (((((nu + ((k - j : ℕ) : ℤ) • rootW a b) a -
              (nu + ((k - j : ℕ) : ℤ) • rootW a b) b : ℤ)) : KK O) - ((l - j : ℕ) : KK O) + 1))
        (fun j => ((E b a) ^ (l - j)) (((E a b) ^ (k + 1 - j)) y)) k ?_ ?_ ?_)
    · beta_reduce
      rw [step j hj]
    · simp
    · intro j hj
      beta_reduce
      have hjk : j ≤ k := Nat.lt_succ_iff.mp hj
      have hA : (nu + ((k - j : ℕ) : ℤ) • rootW a b) a = nu a + ((k - j : ℕ) : ℤ) := by
        simp [rootW, Pi.single_apply, hab, hab.symm]
      have hB : (nu + ((k - j : ℕ) : ℤ) • rootW a b) b = nu b - ((k - j : ℕ) : ℤ) := by
        simp [rootW, Pi.single_apply, hab, hab.symm] <;> ring
      rw [hA, hB]
      have hx : nu a - nu b + ((k + 1 : ℕ) : ℤ) - (l : ℤ) = (nu a - nu b + (k : ℤ) - (l : ℤ)) + 1 := by
        push_cast
        ring
      rw [hx, descPochhammer_succ_eval_add_one, descPochhammer_succ_eval_right, Nat.choose_succ_succ, Nat.descFactorial_succ]
      have hch : (k.choose (j + 1) : KK O) * ((j : KK O) + 1) = (k.choose j : KK O) * ((k : KK O) - j) := by
        have := congrArg (Nat.cast : ℕ → KK O) (Nat.choose_succ_right_eq k j)
        push_cast [hjk] at this
        exact this
      generalize (descPochhammer ℤ j).eval (nu a - nu b + (k : ℤ) - (l : ℤ)) = P
      by_cases hjl : j ≤ l
      · push_cast [hjk, hjl]
        linear_combination (((l : KK O) - j) * (l.descFactorial j : KK O) * (P : KK O)) * hch
      · have h0 : l.descFactorial j = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
        have h0' : l - j = 0 := by omega
        simp [h0, h0']
    · simp [Nat.choose_succ_self]

theorem raise_lower_dividedPower_binomial [CharZero (KK O)] {E : GLOps n (KK O) V} (hE : IsGLRep E) {a b : Fin n} (hab : a ≠ b)
    {nu : Fin n → ℤ} {y : V} (hy : y ∈ weightSp E nu) (k l : ℕ) :
    divPowE E a b k (divPowE E b a l y) = ∑ j ∈ range (k + 1),
      if j ≤ l then ((Ring.choose (nu a - nu b + k - l) j : ℤ) : KK O) •
        divPowE E b a (l - j) (divPowE E a b (k - j) y) else 0 := by
  simp only [divPowE, LinearMap.smul_apply, map_smul]
  rw [raise_pow_lower_pow_expansion hE hab hy k l, Finset.smul_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  split_ifs with hjl
  · simp only [smul_smul]
    congr 1
    have hP : (descPochhammer ℤ j).eval (nu a - nu b + (k : ℤ) - (l : ℤ)) =
        (j.factorial : ℤ) * Ring.choose (nu a - nu b + (k : ℤ) - (l : ℤ)) j := by
      first
      | rw [Polynomial.eval_eq_smeval, Ring.descPochhammer_eq_factorial_smul_choose, nsmul_eq_mul]
      | (rw [Ring.choose]; simp)
    rw [hP]
    have h1 : ((k.factorial : ℕ) : KK O) = (k.choose j : KK O) * j.factorial * (k - j).factorial := by
      exact_mod_cast (Nat.choose_mul_factorial_mul_factorial hjk).symm
    have h2 : ((l.factorial : ℕ) : KK O) = ((l - j).factorial : KK O) * l.descFactorial j := by
      exact_mod_cast (Nat.factorial_mul_descFactorial hjl).symm
    have h3 : (k.choose j : KK O) ≠ 0 := by exact_mod_cast (Nat.choose_pos hjk).ne'
    have h4 : (l.descFactorial j : KK O) ≠ 0 := by
      exact_mod_cast (Nat.descFactorial_eq_zero_iff_lt.not.mpr (by omega))
    have h5 : (j.factorial : KK O) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have h6 : ((k - j).factorial : KK O) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have h7 : ((l - j).factorial : KK O) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    rw [h1, h2]
    push_cast
    field_simp
  · have h0 : l.descFactorial j = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
    simp [h0]

end hw

end Formalism.MainNotions.G.GLWeightTheory
