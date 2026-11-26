module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwBernFaith
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.MultiTwo
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.SymOfVieta

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkSum
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkFaith
open MvPolynomial Equiv UpperTheory.V.AlgebraTools.Hk

private theorem X_sub_ne {R : Type} [CommRing R] [IsDomain R] {n : ℕ} (q : R) {i j : Fin n} (h : i ≠ j) :
    (X i - C q * X j : MvPolynomial (Fin n) R) ≠ 0 := by
  intro h0
  have := congrArg (AddMonoidAlgebra.coeff · (Finsupp.single i 1)) h0
  simp [MvPolynomial.coeff_X', MvPolynomial.coeff_C_mul, Finsupp.single_left_inj, h, Ne.symm h] at this

theorem UpperTheory.V.AlgebraTools.hkFaith :
    ∀ (R : Type) [CommRing R] [IsDomain R] (n : ℕ) (q : R) (H : Type) [Ring H] [Algebra R H] (b : Bern n q H), b.Faithful → ∀ c : Perm (Fin n) → MvPolynomial (Fin n) R,
      (∀ x : MvPolynomial (Fin n) R, (∑ u, b.th (c u) * b.T u) * b.th x * b.one = 0) → c = 0 := by
  classical
  intro R _ _ n q H _ _ b hfaith c hc
  let K := FractionRing (MvPolynomial (Fin n) R)
  have hinj := IsFractionRing.injective (MvPolynomial (Fin n) R) K
  choose F hF1 hF2 hF3 using fun u => UpperTheory.V.AlgebraTools.hkAct R n q H b K u
  choose Y hY1 hY2 using hF1
  have key : ∀ x : MvPolynomial (Fin n) R,
      ∑ v, (∑ u, algebraMap (MvPolynomial (Fin n) R) K (c u) * F u v) *
        algebraMap (MvPolynomial (Fin n) R) K (rename v x) = 0 := by
    intro x
    have h1 : b.th (∑ u, c u * Y u x) * b.one = 0 := by
      calc b.th (∑ u, c u * Y u x) * b.one
          = ∑ u, b.th (c u) * (b.th (Y u x) * b.one) := by
            set_option synthInstance.maxHeartbeats 100000 in
              rw [map_sum, Finset.sum_mul]; simp [map_mul, mul_assoc]
        _ = ∑ u, b.th (c u) * (b.T u * b.th x * b.one) := by simp [hY1]
        _ = (∑ u, b.th (c u) * b.T u) * b.th x * b.one := by
            rw [Finset.sum_mul, Finset.sum_mul]; simp [mul_assoc]
        _ = 0 := hc x
    have h2 := congrArg (algebraMap (MvPolynomial (Fin n) R) K) (hfaith _ h1)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_zero] at h2
    simp_rw [map_mul, hY2, Finset.mul_sum] at h2
    rw [Finset.sum_comm] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun u _ => ?_
    ring
  have hD := UpperTheory.V.AlgebraTools.hkDedekind R n K _ key
  by_contra hne
  obtain ⟨w0, hw0⟩ : ∃ w, c w ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hne (funext hall)
  obtain ⟨w, hwS, hmax⟩ := (Finset.univ.filter (fun u => c u ≠ 0)).exists_max_image invN
    ⟨w0, by simp [hw0]⟩
  have hcw : c w ≠ 0 := by simpa using hwS
  have hw := congrFun hD w
  simp only [Pi.zero_apply] at hw
  rw [Finset.sum_eq_single w] at hw
  · apply mul_ne_zero _ _ hw
    · exact fun h => hcw (hinj (by rw [h, map_zero]))
    · rw [hF2 w]
      refine Finset.prod_ne_zero_iff.mpr fun p hp => ?_
      have hlt : p.1 < p.2 := by
        simp [invSet, pairs] at hp
        exact hp.1
      have hpne : p.1 ≠ p.2 := ne_of_lt hlt
      refine div_ne_zero ?_ ?_
      · exact fun h => X_sub_ne q hpne (hinj (by rw [h, map_zero]))
      · intro h
        apply X_sub_ne (1 : R) hpne
        apply hinj
        simpa using h
  · intro u _ hu
    by_cases hcu : c u = 0
    · simp [hcu]
    · rw [hF3 u w (fun h => hu h.symm) (hmax u (by simp [hcu])), mul_zero]
  · simp
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkSpan
open MvPolynomial Equiv UpperTheory.V.AlgebraTools.Hk

theorem UpperTheory.V.AlgebraTools.hkSpan :
    ∀ (R : Type) [CommRing R] (n : ℕ) (q : R) (H : Type) [Ring H] [Algebra R H] (b : Bern n q H) (w : Perm (Fin n)) (c : Perm (Fin n) → MvPolynomial (Fin n) R),
      ∃ c' : Perm (Fin n) → MvPolynomial (Fin n) R, b.T w * ∑ u, b.th (c u) * b.T u = ∑ u, b.th (c' u) * b.T u := by
  intro R _ n q H _ _ b
  classical
  let S : Submodule R H :=
    { carrier := {h | ∃ c' : Perm (Fin n) → MvPolynomial (Fin n) R, h = ∑ u, b.th (c' u) * b.T u}
      add_mem' := by
        rintro _ _ ⟨c₁, rfl⟩ ⟨c₂, rfl⟩
        exact ⟨c₁ + c₂, by simp [add_mul, Finset.sum_add_distrib]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro r _ ⟨c₁, rfl⟩
        exact ⟨r • c₁, by simp [Finset.smul_sum]⟩ }
  have hone : ∀ x u, b.th x * b.T u ∈ S := by
    intro x u
    refine ⟨Pi.single u x, ?_⟩
    rw [Finset.sum_eq_single u]
    · simp
    · intro v _ hv
      simp [Pi.single_eq_of_ne hv]
    · simp
  have hTT : ∀ a c : Fin n, a.val + 1 = c.val → ∀ x u, b.th x * (b.T (swap a c) * b.T u) ∈ S := by
    intro a c hac x u
    by_cases hlt : u⁻¹ a < u⁻¹ c
    · rw [← b.T_mul a c hac u hlt]
      exact hone _ _
    · have hne : u⁻¹ c ≠ u⁻¹ a := by
        intro e
        have := (u⁻¹).injective e
        rw [this] at hac
        omega
      have hw' : (swap a c * u)⁻¹ a < (swap a c * u)⁻¹ c := by
        rw [mul_inv_rev, swap_inv, Perm.mul_apply, Perm.mul_apply, swap_apply_left, swap_apply_right]
        exact lt_of_le_of_ne (not_lt.mp hlt) hne
      have e := b.T_mul a c hac _ hw'
      rw [swap_mul_self_mul] at e
      have e2 : b.T (swap a c) * b.T u = (q - 1) • b.T u + q • b.T (swap a c * u) := by
        calc b.T (swap a c) * b.T u = (b.T (swap a c) * b.T (swap a c)) * b.T (swap a c * u) := by
              rw [mul_assoc, ← e]
          _ = (q - 1) • b.T u + q • b.T (swap a c * u) := by
              rw [b.T_sq a c hac, add_mul, smul_mul_assoc, smul_mul_assoc, one_mul, ← e]
      rw [e2, mul_add, mul_smul_comm, mul_smul_comm]
      exact S.add_mem (S.smul_mem _ (hone _ _)) (S.smul_mem _ (hone _ _))
  have hs : ∀ a c : Fin n, a.val + 1 = c.val → ∀ h ∈ S, b.T (swap a c) * h ∈ S := by
    rintro a c hac _ ⟨c₁, rfl⟩
    rw [Finset.mul_sum]
    refine S.sum_mem fun u _ => ?_
    obtain ⟨y, -, hy⟩ := (UpperTheory.V.AlgebraTools.hkBern R n q H b).1 a c hac (c₁ u)
    rw [← mul_assoc, hy, add_mul, smul_mul_assoc, mul_assoc]
    exact S.add_mem (hTT a c hac _ _) (S.smul_mem _ (hone _ _))
  have key : ∀ w, ∀ h ∈ S, b.T w * h ∈ S := by
    refine UpperTheory.V.AlgebraTools.hkInd n _ ?_ ?_
    · intro h hh
      rwa [b.T_one, one_mul]
    · intro a c hac w hw ih h hh
      rw [b.T_mul a c hac w hw, mul_assoc]
      exact hs a c hac _ (ih h hh)
  intro w c
  exact key w _ ⟨c, rfl⟩
end

open MvPolynomial Equiv UpperTheory.V.AlgebraTools.Hk

theorem UpperTheory.V.AlgebraTools.hkSum :
    ∀ (R : Type) [CommRing R] [IsDomain R] (n : ℕ) (q : R) (H : Type) [Ring H] [Algebra R H] (b : Bern n q H), b.Faithful → ∀ (ι : Type) [Fintype ι] (a c : ι → MvPolynomial (Fin n) R), IsDual a c →
      ∑ i, b.th (a i) * b.one * b.th (c i) = b.th (NN n q) := by
  intro R _ _ n q H _ _ b hb ι _ a c hd
  classical
  let S : H → Prop := fun h => ∃ e : Perm (Fin n) → MvPolynomial (Fin n) R,
    ∑ u, b.th (e u) * b.T u = h
  have S_zero : S 0 := ⟨0, by simp⟩
  have S_add : ∀ h₁ h₂, S h₁ → S h₂ → S (h₁ + h₂) := by
    rintro h₁ h₂ ⟨e₁, rfl⟩ ⟨e₂, rfl⟩
    refine ⟨e₁ + e₂, ?_⟩
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    simp [add_mul]
  have S_sub : ∀ h₁ h₂, S h₁ → S h₂ → S (h₁ - h₂) := by
    rintro h₁ h₂ ⟨e₁, rfl⟩ ⟨e₂, rfl⟩
    refine ⟨e₁ - e₂, ?_⟩
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    simp [sub_mul]
  have S_sum : ∀ {κ : Type} (s : Finset κ) (f : κ → H), (∀ k ∈ s, S (f k)) → S (∑ k ∈ s, f k) :=
    fun s f hf => Finset.sum_induction f S S_add S_zero hf
  have S_th : ∀ x, S (b.th x) := by
    intro x
    refine ⟨fun u => if u = 1 then x else 0, ?_⟩
    rw [Finset.sum_eq_single (1 : Perm (Fin n))]
    · simp [b.T_one]
    · intro u _ hu
      simp [hu]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have S_T : ∀ w h, S h → S (b.T w * h) := by
    rintro w h ⟨e, rfl⟩
    obtain ⟨e', he'⟩ := UpperTheory.V.AlgebraTools.hkSpan R n q H b w e
    exact ⟨e', he'.symm⟩
  have S_thmul : ∀ x h, S h → S (b.th x * h) := by
    rintro x h ⟨e, rfl⟩
    refine ⟨fun u => x * e u, ?_⟩
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [map_mul, mul_assoc]
  have hE : S (∑ i, b.th (a i) * b.one * b.th (c i)) := by
    refine S_sum _ _ fun i _ => ?_
    rw [mul_assoc, Bern.one, Finset.sum_mul]
    exact S_thmul _ _ (S_sum _ _ fun w _ => S_T _ _ (S_th _))
  obtain ⟨e, he⟩ := S_sub _ _ hE (S_th (NN n q))
  have hx : ∀ x, (∑ i, b.th (a i) * b.one * b.th (c i)) * b.th x * b.one
      = b.th (NN n q * x) * b.one := by
    intro x
    rw [Finset.sum_mul, Finset.sum_mul]
    have step : ∀ i, b.th (a i) * b.one * b.th (c i) * b.th x * b.one
        = b.th (a i * dd (c i * (NN n q * x))) * b.one := by
      intro i
      have hs := UpperTheory.V.AlgebraTools.hkSandwich R n q H b hb (c i * x)
      calc b.th (a i) * b.one * b.th (c i) * b.th x * b.one
          = b.th (a i) * (b.one * b.th (c i * x) * b.one) := by
            rw [map_mul]
            simp only [mul_assoc]
        _ = b.th (a i) * (b.th (dd (NN n q * (c i * x))) * b.one) := by rw [hs]
        _ = b.th (a i * dd (c i * (NN n q * x))) * b.one := by
            rw [map_mul, mul_left_comm (NN n q) (c i) x, mul_assoc]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_congr rfl fun i _ => step i, ← Finset.sum_mul, ← map_sum,
      (UpperTheory.V.AlgebraTools.hkDualExp R n ι a c hd (NN n q * x)).1]
  have he0 := UpperTheory.V.AlgebraTools.hkFaith R n q H b hb e (fun x => by
    rw [he, sub_mul, sub_mul, hx x, ← map_mul, sub_self])
  rw [he0] at he
  simp only [Pi.zero_apply, map_zero, zero_mul, Finset.sum_const_zero] at he
  exact (sub_eq_zero.mp he.symm)
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MemFixedPiIff
@[reducible] noncomputable def UpperTheory.Reformulated.B.Gr29.Plc :
    (F : Type) → [Field F] → Type :=
    fun (F : Type) [Field F] ↦ IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)

@[reducible] noncomputable def UpperTheory.Reformulated.B.Gr29.GLw :
    {L : Type} → [inst : Field L] → [NumberField L] → ℕ → UpperTheory.Reformulated.B.Gr29.Plc L → Type :=
    fun {L : Type} [Field L] [NumberField L] (n : ℕ) (w : UpperTheory.Reformulated.B.Gr29.Plc L) ↦
      GL (Fin n) (IsDedekindDomain.HeightOneSpectrum.adicCompletion L w)

@[reducible] noncomputable def UpperTheory.Reformulated.B.Gr29.GV :
    {L : Type} → [inst : Field L] → [NumberField L] → ℕ → {V : Type} → (V → UpperTheory.Reformulated.B.Gr29.Plc L) → Type :=
    fun {L : Type} [Field L] [NumberField L] (n : ℕ) {V : Type} (S : V → UpperTheory.Reformulated.B.Gr29.Plc L) ↦
      (v : V) → UpperTheory.Reformulated.B.Gr29.GLw n (S v)

noncomputable def UpperTheory.Reformulated.B.Gr29.atJ :
    {L : Type} →
      [inst : Field L] →
        [inst_1 : NumberField L] →
          (n : ℕ) →
            {q : ℕ} →
              (w : Fin q → UpperTheory.Reformulated.B.Gr29.Plc L) → (j : Fin q) → UpperTheory.Reformulated.B.Gr29.GLw n (w j) →* UpperTheory.Reformulated.B.Gr29.GV n w :=
    fun {L : Type} [Field L] [NumberField L] (n : ℕ) {q : ℕ} (w : Fin q → UpperTheory.Reformulated.B.Gr29.Plc L) (j : Fin q) ↦
      MonoidHom.mulSingle (fun (j : Fin q) ↦ UpperTheory.Reformulated.B.Gr29.GLw n (w j)) j

private def UpperTheory.Reformulated.B.Gr29.stab {A P M : Type} [CommRing A] [Group P] [AddCommGroup M]
    [_root_.Module A M] (ρ : Representation A P M) (m : M) : Subgroup P where
  carrier := {g | ρ g m = m}
  mul_mem' := by
    intro a b ha hb
    have ha' : ρ a m = m := ha
    have hb' : ρ b m = m := hb
    change ρ (a * b) m = m
    rw [map_mul, Module.End.mul_apply, hb', ha']
  one_mem' := by
    change ρ 1 m = m
    rw [map_one, Module.End.one_apply]
  inv_mem' := by
    intro a ha
    have ha' : ρ a m = m := ha
    change ρ a⁻¹ m = m
    have h : ρ a⁻¹ (ρ a m) = m := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rwa [ha'] at h

private theorem UpperTheory.Reformulated.B.Gr29.mem_fixed_pi_iff {q : ℕ} {G : Fin q → Type} [∀ j, Group (G j)]
    {A M : Type} [CommRing A] [AddCommGroup M] [_root_.Module A M]
    (ρ : Representation A ((j : Fin q) → G j) M) (H : (j : Fin q) → Subgroup (G j)) (m : M) :
    m ∈ UpperTheory.Reformulated.B.SubgroupFixedSubmodule.fixd ρ (Subgroup.pi Set.univ H) ↔
      ∀ j : Fin q, m ∈ UpperTheory.Reformulated.B.SubgroupFixedSubmodule.fixd (MonoidHom.comp ρ (MonoidHom.mulSingle G j)) (H j) := by
  have key : m ∈ UpperTheory.Reformulated.B.SubgroupFixedSubmodule.fixd ρ (Subgroup.pi Set.univ H) ↔
      Subgroup.pi Set.univ H ≤ UpperTheory.Reformulated.B.Gr29.stab ρ m := Iff.rfl
  rw [key, Subgroup.pi_le_iff]
  refine forall_congr' fun j => ?_
  constructor
  · intro h k hk
    exact h (Subgroup.mem_map_of_mem _ hk)
  · rintro h _ ⟨k, hk, rfl⟩
    exact h k hk

theorem UpperTheory.Reformulated.B.Gr29.mem_pi :
    ∀ {L : Type} [inst : Field L] [inst_1 : NumberField L] {n q : ℕ} {w : Fin q → UpperTheory.Reformulated.B.Gr29.Plc L} {A M : Type}
      [inst_2 : CommRing A] [inst_3 : AddCommGroup M] [inst_4 : _root_.Module A M]
      (ρ : Representation A (UpperTheory.Reformulated.B.Gr29.GV n w) M) (H : (j : Fin q) → Subgroup (UpperTheory.Reformulated.B.Gr29.GLw n (w j)))
      (m : M),
      m ∈ UpperTheory.Reformulated.B.SubgroupFixedSubmodule.fixd ρ (Subgroup.pi Set.univ H) ↔
        ∀ (j : Fin q), m ∈ UpperTheory.Reformulated.B.SubgroupFixedSubmodule.fixd (MonoidHom.comp ρ (UpperTheory.Reformulated.B.Gr29.atJ n w j)) (H j) := by
  intro L _ _ n q w A M _ _ _ ρ H m
  exact UpperTheory.Reformulated.B.Gr29.mem_fixed_pi_iff (G := fun j : Fin q => UpperTheory.Reformulated.B.Gr29.GLw n (w j)) ρ H m
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.HkHypOf
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem dc_apply {A H M : Type} [CommRing A] [Group H] [AddCommGroup M] [Module A M]
    (ρ : Representation A H M) (K K' : Subgroup H) (x : H) (h : FinOrb K K' x) (m : M) :
    dc ρ K K' x m = ∑ᶠ q : MulAction.orbit K (x : H ⧸ K'), ρ (q : H ⧸ K').out m := by
  have : Finite (MulAction.orbit K (x : H ⧸ K')) := h
  have := Fintype.ofFinite (MulAction.orbit K (x : H ⧸ K'))
  rw [dc, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, LinearMap.sum_apply]

private theorem relIndex_ne {H : Type} [Group H] (K I : Subgroup H) (h : FinOrb K I 1) : I.relIndex K ≠ 0 := by
  have e : I.subgroupOf K = MulAction.stabilizer K ((1 : H) : H ⧸ I) := by
    ext g
    rw [Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff]
    change _ ↔ (g : H) ∈ MulAction.stabilizer H ((1 : H) : H ⧸ I)
    rw [MulAction.stabilizer_quotient]
  rw [Subgroup.relIndex, e, MulAction.index_stabilizer]
  exact Set.ncard_ne_zero_of_mem (MulAction.mem_orbit_self _) h

private theorem bern_ev {O H E : Type} [CommRing O] [IsDomain O] [Ring H] [Algebra O H] [Ring E] [Algebra O E] {n : ℕ} {q : O}
    (b : Hk.Bern n q H) (hF : b.Faithful) (ev : H →ₐ[O] E) :
    (∀ z : MvPolynomial (Fin n) O, z.IsSymmetric → ev b.one * ev.comp b.th z = ev.comp b.th z * ev b.one) ∧
      (∀ (ι : Type) [Fintype ι] (a c : ι → MvPolynomial (Fin n) O), Hk.IsDual a c →
        ∑ i, ev.comp b.th (a i) * ev b.one * ev.comp b.th (c i) = ev.comp b.th (Hk.NN n q)) ∧
      ∀ y, ev b.one * ev.comp b.th y * ev b.one = ev.comp b.th (Hk.dd (Hk.NN n q * y)) * ev b.one := by
  refine ⟨fun z hz => ?_, fun ι _ a c hd => ?_, fun y => ?_⟩
  · simp only [AlgHom.comp_apply, ← map_mul]
    congr 1
    rw [Hk.Bern.one, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun w _ => (hkBern O n _ _ b).2 z hz w
  · set_option synthInstance.maxHeartbeats 100000 in
      simp only [AlgHom.comp_apply, ← map_mul, ← map_sum]
    rw [hkSum O n _ _ b hF ι a c hd]
  · simp only [AlgHom.comp_apply]
    rw [← map_mul, ← map_mul, hkSandwich O n _ _ b hF y, map_mul]

private theorem ev_rel {O H E : Type} [CommRing O] [Ring H] [Algebra O H] [Ring E] [Algebra O E] (ev : H →ₐ[O] E)
    {a y z : H} {c : O} {y' z' : E} (h : a * y = c • z) (hy : ev y = y') (hz : ev z = z') : ev a * y' = c • z' := by
  rw [← hy, ← hz, ← map_mul, h, map_smul]

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private theorem bruh : ∀ g ∈ KO k (Fin n), ∃! w : Equiv.Perm (Fin n),
    ∃ a ∈ iwC k n ⊤, ∃ b ∈ iwC k n ⊤, g = a * pm k n w * b := by
  rw [(memIwC k n ⊤).2.1]
  exact (bruhatKO k n).2

private theorem iw_le : iwC k n ⊤ ≤ KO k (Fin n) := by
  rw [(memIwC k n ⊤).2.1]
  exact iwahori_le_KO k (Fin n)

private theorem dom_fund {x : kˣ} (hx : IsUnif x) (m : ℕ) : Dom (fun j : Fin n => x ^ fund n m j) := by
  have hx1 : valuation k (x : k) ≤ 1 := by
    obtain ⟨p, -, hp⟩ := hx
    rw [← hp]
    exact p.2
  intro j l hjl
  have hjl' : (j : ℕ) ≤ (l : ℕ) := hjl
  simp only [fund]
  by_cases h1 : (l : ℕ) < m
  · have h2 : (j : ℕ) < m := lt_of_le_of_lt hjl' h1
    simp [h1, h2]
  · by_cases h2 : (j : ℕ) < m
    · simpa [h1, h2] using hx1
    · simp [h1, h2]

private theorem fund_split {T : Type} [CommGroup T] (x : T) (i : Fin n) : (fun j : Fin n => x ^ fund n ((i : ℕ) + 1) j)
    = Pi.mulSingle i x * (fun j : Fin n => x ^ fund n (i : ℕ) j) := by
  funext j
  simp only [fund, Pi.mul_apply]
  by_cases hj : j = i
  · subst hj
    simp
  · have hne : (j : ℕ) ≠ (i : ℕ) := fun h => hj (Fin.ext h)
    rw [Pi.mulSingle_eq_of_ne hj, one_mul]
    by_cases h : (j : ℕ) < (i : ℕ)
    · have h' : (j : ℕ) < (i : ℕ) + 1 := by omega
      simp [h, h']
    · have h' : ¬ (j : ℕ) < (i : ℕ) + 1 := by omega
      simp [h, h']

private theorem dc_K {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (ρ : Representation A (GL (Fin n) k) M) :
    (∀ m ∈ fixd ρ (iwC k n ⊤), dc ρ (KO k (Fin n)) (iwC k n ⊤) 1 m ∈ fixd ρ (KO k (Fin n))) ∧
    ∀ m ∈ fixd ρ (KO k (Fin n)),
      dc ρ (KO k (Fin n)) (iwC k n ⊤) 1 m = ((iwC k n ⊤).relIndex (KO k (Fin n))) • m := by
  obtain ⟨hf, -, h3⟩ := hkTrace A _ M ρ _ _ iw_le _ (pm k n) (heckePairIwC k n ⊤).1 (bruhatKO k n).1 bruh
  have ha := (hkApply A _ M ρ _ _ 1 hf).1
  refine ⟨fun m hm => ?_, fun m hm => ?_⟩
  · rw [← ha ⟨m, hm⟩]
    exact Subtype.property _
  · have h := congrArg Subtype.val (h3 ⟨m, hm⟩)
    rw [trc, ha, Submodule.coe_smul, Nat.cast_smul_eq_nsmul] at h
    exact h

private theorem locO (O M : Type) [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M]
    (ρ : Representation O (GL (Fin n) k) M) {x : kˣ} (hx : IsUnif x) (hq : IsUnit (resCard k : O)) :
    ∃ (th : MvPolynomial (Fin n) O →ₐ[O] Module.End O (fixd ρ (iwC k n ⊤))) (E : Module.End O (fixd ρ (iwC k n ⊤))),
      (∀ v, (E v : M) = dc ρ (KO k (Fin n)) (iwC k n ⊤) 1 v) ∧
      (∀ i : Fin n, th (MvPolynomial.X i) * hk ρ (iwC k n ⊤) (pw x (fund n i)) =
        ((resCard k : O) ^ (i : ℕ)) • hk ρ (iwC k n ⊤) (pw x (fund n ((i : ℕ) + 1)))) ∧
      (∀ z : MvPolynomial (Fin n) O, z.IsSymmetric → E * th z = th z * E) ∧
      (∀ (ι : Type) [Fintype ι] (a b : ι → MvPolynomial (Fin n) O), Hk.IsDual a b →
        ∑ i, th (a i) * E * th (b i) = th (Hk.NN n (resCard k : O))) ∧
      ∀ y, E * th y * E = th (Hk.dd (Hk.NN n (resCard k : O) * y)) * E := by
  obtain ⟨b, hT, hX⟩ := bernHk k n O x hx hq
  have hF := bernFaith k n O x hx hq b hT hX
  obtain ⟨ev, hev⟩ := hkEv O _ M ρ _ (heckePairIwC k n ⊤).1
  obtain ⟨hf, h2, -⟩ := hkTrace O _ M ρ _ _ iw_le _ (pm k n) (heckePairIwC k n ⊤).1 (bruhatKO k n).1 bruh
  obtain ⟨g1, g2, g3⟩ := bern_ev b hF ev
  refine ⟨ev.comp b.th, ev b.one, fun v => ?_, fun i => ?_, g1, g2, g3⟩
  · have h : ev b.one = ∑ w, hk ρ (iwC k n ⊤) (pm k n w) :=
      (map_sum ev b.T Finset.univ).trans (Finset.sum_congr rfl fun w _ => (congrArg ev (hT w)).trans (hev _))
    rw [h, h2]
    exact (hkApply O _ M ρ _ _ 1 hf).1 v
  · exact ev_rel ev (hX i) (hev _) (hev _)

private theorem locA (O A M V : Type) [CommRing O] [IsDomain O] [CommRing A] [Algebra O A] [AddCommGroup M] [Module A M]
    [AddCommGroup V] [Module A V] (ρ : Representation A (GL (Fin n) k) M) {x : kˣ} (hx : IsUnif x)
    (hq : IsUnit (resCard k : O)) (tf : ∀ (c : ℕ) (m : M), c ≠ 0 → c • m = 0 → m = 0)
    (ι : V →ₗ[A] M) (hι : Function.Injective ι) (hI : ∀ v, ι v ∈ fixd ρ (iwC k n ⊤))
    (Θ : (Fin n → kˣ) →* (Module.End A V)ˣ)
    (hΘ : ∀ t, Dom t → ∀ v, ι ((Θ t).val v) = dc ρ (iwC k n ⊤) (iwC k n ⊤) (diagT k (Fin n) t) (ι v))
    (e : Module.End A V) (he : ∀ v, ι (e v) = dc ρ (KO k (Fin n)) (iwC k n ⊤) 1 (ι v))
    (φ : MvPolynomial (Fin n) O →+* Module.End A V)
    (hC : ∀ o v, φ (MvPolynomial.C o) v = algebraMap O A o • v)
    (hφ : ∀ i, φ (MvPolynomial.X i) = ((resCard k : A) ^ (i : ℕ)) • (Θ (Pi.mulSingle i x)).val) :
    (∀ z : MvPolynomial (Fin n) O, z.IsSymmetric → Commute e (φ z)) ∧
      (∀ (J : Type) [Fintype J] (a b : J → MvPolynomial (Fin n) O), Hk.IsDual a b →
        ∑ i, φ (a i) * e * φ (b i) = φ (Hk.NN n (resCard k : O))) ∧
      ∀ y v, ι v ∈ fixd ρ (KO k (Fin n)) → e (φ y v) = φ (Hk.dd (Hk.NN n (resCard k : O) * y)) v := by
  letI : Module O M := Module.compHom M (algebraMap O A)
  have hs : ∀ (o : O) (m : M), o • m = algebraMap O A o • m := fun _ _ => rfl
  let ρO : Representation O (GL (Fin n) k) M :=
    { toFun := fun g => { toFun := ρ g, map_add' := map_add _, map_smul' := fun o m => map_smul (ρ g) (algebraMap O A o) m }
      map_one' := LinearMap.ext fun m => LinearMap.congr_fun (map_one ρ) m
      map_mul' := fun g h => LinearMap.ext fun m => LinearMap.congr_fun (map_mul ρ g h) m }
  have hdc : ∀ K K' g, FinOrb K K' g → ∀ m, dc ρO K K' g m = dc ρ K K' g m := fun K K' g h m => by
    rw [dc_apply _ _ _ _ h, dc_apply _ _ _ _ h]; rfl
  obtain ⟨th, E, hE, hX, hsym, hsum, hsw⟩ := locO O M ρO hx hq
  have hP := heckePairIwC k n ⊤
  let j : V →+ fixd ρO (iwC k n ⊤) := ⟨⟨fun v => ⟨ι v, hI v⟩, Subtype.ext (map_zero ι)⟩, fun a b => Subtype.ext (map_add ι a b)⟩
  have hj : ∀ v, (j v : M) = ι v := fun _ => rfl
  have jinj : Function.Injective j := fun a b h => hι (congrArg Subtype.val h)
  have je : ∀ v, j (e v) = E (j v) := fun v => Subtype.ext (by rw [hE, hj, hj, he, hdc _ _ _ (hP.2.2 ⊤).2])
  have jΘ : ∀ m v, j ((Θ fun a => x ^ fund n m a).val v) = hk ρO (iwC k n ⊤) (pw x (fund n m)) (j v) := fun m v =>
    Subtype.ext (by
      rw [hj, hΘ _ (dom_fund hx m), ← hdc _ _ _ (hP.1 _)]
      exact ((hkApply O _ M ρO _ _ _ (hP.1 _)).1 (j v)).symm)
  have jX : ∀ i v, j (φ (MvPolynomial.X i) v) = th (MvPolynomial.X i) (j v) := by
    intro i v
    obtain ⟨u, rfl⟩ := ((Module.End.isUnit_iff _).1 (Θ fun a => x ^ fund n i a).isUnit).2 v
    have h := LinearMap.congr_fun (hX i) (j u)
    rw [Module.End.mul_apply, ← jΘ, LinearMap.smul_apply, ← jΘ, fund_split, map_mul, Units.val_mul,
      Module.End.mul_apply] at h
    rw [h, hφ]
    apply Subtype.ext
    rw [hj, LinearMap.smul_apply, map_smul, Submodule.coe_smul, hs, map_pow, map_natCast, hj]
  have jφ : ∀ z v, j (φ z v) = th z (j v) := by
    intro z
    induction z using MvPolynomial.induction_on with
    | C o =>
      intro v
      apply Subtype.ext
      rw [hC, hj, map_smul, ← MvPolynomial.algebraMap_eq, th.commutes, Module.algebraMap_end_apply, Submodule.coe_smul, hs, hj]
    | add p q hp hq => intro v; simp only [map_add (f := _), LinearMap.add_apply, hp, hq]
    | mul_X p i hp => intro v; simp only [map_mul, Module.End.mul_apply, hp, jX]
  refine ⟨fun z hz => LinearMap.ext fun v => jinj ?_, fun J _ a b hd => LinearMap.ext fun v => jinj ?_, fun y v hv => ?_⟩
  · simp only [Module.End.mul_apply, je, jφ]
    exact LinearMap.congr_fun (hsym z hz) _
  · rw [jφ, ← hsum J a b hd]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearMap.sum_apply, map_sum, Module.End.mul_apply, je, jφ]
  · have h1 : e v = ((iwC k n ⊤).relIndex (KO k (Fin n))) • v := hι (by rw [he, map_nsmul, (dc_K ρ).2 _ hv])
    have h2 : e (φ y (e v)) = φ (Hk.dd (Hk.NN n (resCard k : O) * y)) (e v) := jinj (by
      simp only [je, jφ]
      exact LinearMap.congr_fun (hsw y) _)
    rw [h1, map_nsmul, map_nsmul, map_nsmul, ← sub_eq_zero, ← nsmul_sub] at h2
    apply hι
    rw [← sub_eq_zero, ← map_sub]
    refine tf _ _ (relIndex_ne _ _ (hP.2.2 ⊤).2) ?_
    rw [← map_nsmul, h2, map_zero]

end Loc

private theorem comm_dc {A H M : Type} [CommRing A] [Group H] [AddCommGroup M] [Module A M]
    (ρ : Representation A H M) (K K' : Subgroup H) (x : H) (φ : Module.End A M) (h : ∀ g, Commute φ (ρ g)) :
    Commute φ (dc ρ K K' x) :=
  finsum_induction (fun e => Commute φ e) (Commute.zero_right φ) (fun _ _ h1 h2 => h1.add_right h2) fun _ => h _

private theorem lprod_mem {A V : Type} [CommRing A] [AddCommGroup V] [Module A V] (W : Submodule A V) (f : Module.End A V)
    (hf : ∀ v, f v ∈ W) (s : List (Module.End A V)) (hs : ∀ a ∈ s, ∀ v ∈ W, a v ∈ W) (h : f ∈ s) (v : V) : s.prod v ∈ W := by
  induction s with
  | nil => simp at h
  | cons a s ih =>
    rw [List.prod_cons, Module.End.mul_apply]
    rcases List.mem_cons.1 h with rfl | h'
    · exact hf _
    · exact hs a List.mem_cons_self _ (ih (fun b hb => hs b (List.mem_cons_of_mem _ hb)) h')

private theorem comm_unit {R : Type} [Monoid R] {e : R} {u v w : Rˣ} (h : w = u * v) (hw : Commute e w) (hv : Commute e v) :
    Commute e u := by
  have : u = w * v⁻¹ := by rw [h, mul_inv_cancel_right]
  rw [this, Units.val_mul]
  exact hw.mul_right hv.units_inv_right

private theorem stab {A G M : Type} [CommRing A] [Group G] [AddCommGroup M] [Module A M] (ρ : Representation A G M)
    (K : Subgroup G) (tf : ∀ (k : ℕ) (m : M), k ≠ 0 → k • m = 0 → m = 0) (U : Submodule A M) (e f : Module.End A U) (r : ℕ)
    (hr : r ≠ 0) (eK : ∀ v, (e v : M) ∈ fixd ρ K) (hf : Commute e f) (v : U) (h1 : (e v : M) = r • (v : M)) :
    (f v : M) ∈ fixd ρ K := by
  intro g hg
  have h1' : e v = r • v := Subtype.ext h1
  have h2 := eK (f v) g hg
  have h3 : e (f v) = r • f v := by
    rw [← map_nsmul, ← h1']
    exact LinearMap.congr_fun hf.eq v
  rw [h3, Submodule.coe_smul_of_tower, map_nsmul, ← sub_eq_zero, ← nsmul_sub] at h2
  exact sub_eq_zero.1 (tf r _ hr h2)

private theorem comm_res {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] {U : Submodule A M}
    {e f : Module.End A U} {e' f' : Module.End A M} (he : ∀ v, (e v : M) = e' v) (hf : ∀ v, (f v : M) = f' v)
    (h : Commute e' f') : Commute e f := by
  refine LinearMap.ext fun v => Subtype.ext ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, he, hf, hf, he]
  exact LinearMap.congr_fun h.eq _

private theorem emb_C {O A V : Type} [CommRing O] [CommRing A] [Algebra O A] [AddCommGroup V] [Module A V] {q n : ℕ}
    (act : PU A q n →ₐ[A] Module.End A V) (j : Fin q) (o : O) (v : V) :
    (act.toRingHom.comp (emb O A j)) (MvPolynomial.C o) v = algebraMap O A o • v := by
  have : emb O A (q := q) (n := n) j (MvPolynomial.C o) = algebraMap A _ (algebraMap O A o) := by simp [emb]
  exact (congrArg (fun p => act p v) this).trans (LinearMap.congr_fun (act.commutes _) v)

private theorem emb_X {O A V : Type} [CommRing O] [CommRing A] [Algebra O A] [AddCommGroup V] [Module A V] {q n : ℕ}
    (act : PU A q n →ₐ[A] Module.End A V) (j : Fin q) (i : Fin n) :
    (act.toRingHom.comp (emb O A j)) (MvPolynomial.X i) = act (MvPolynomial.X (j, i)) := by
  have : emb O A (q := q) (n := n) j (MvPolynomial.X i) = MvPolynomial.X (j, i) := by simp [emb]
  exact congrArg act this

section

variable {L : Type} [Field L] [NumberField L] {n q : ℕ} {w : Fin q → Plc L} {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
  (ρ : Representation A (GV n w) M)

private theorem comm_at {j j' : Fin q} (h : j ≠ j') (g : GLw n (w j)) (g' : GLw n (w j')) :
    Commute (ρ (atJ n w j g)) (ρ (atJ n w j' g')) :=
  (Pi.mulSingle_commute (f := fun j => GLw n (w j)) h g g').map ρ

private theorem comm_dd {j j' : Fin q} (h : j ≠ j') (K K' : Subgroup (GLw n (w j))) (g : GLw n (w j))
    (I I' : Subgroup (GLw n (w j'))) (g' : GLw n (w j')) :
    Commute (dc (ρ.comp (atJ n w j)) K K' g) (dc (ρ.comp (atJ n w j')) I I' g') :=
  comm_dc _ _ _ _ _ fun a' => (comm_dc _ _ _ _ _ fun a => comm_at ρ (Ne.symm h) a' a).symm

private theorem mem_pi (H : ∀ j, Subgroup (GLw n (w j))) (m : M) :
    m ∈ fixd ρ (Subgroup.pi Set.univ H) ↔ ∀ j, m ∈ fixd (ρ.comp (atJ n w j)) (H j) :=
  by apply _root_.UpperTheory.Reformulated.B.Gr29.mem_pi <;> assumption

private theorem pres (j : Fin q) : ∀ m ∈ fixd ρ (UC n w fun _ => ⊤),
    dc (ρ.comp (atJ n w j)) (KO _ (Fin n)) (iwC _ n ⊤) 1 m ∈ fixd ρ (UC n w fun _ => ⊤) := by
  intro m hm
  rw [UC, mem_pi] at hm ⊢
  intro j'
  by_cases e : j' = j
  · subst e
    exact fixd_anti _ iw_le ((dc_K _).1 m (hm _))
  · intro u hu
    have h1 := LinearMap.congr_fun (comm_dc (ρ.comp (atJ n w j)) (KO _ (Fin n)) (iwC _ n ⊤) 1 _
      fun g' => comm_at ρ e u g').eq m
    rw [Module.End.mul_apply, Module.End.mul_apply, show ρ (atJ n w j' u) m = m from hm j' u hu] at h1
    exact h1

private theorem memI (j : Fin q) (v : fixd ρ (UC n w fun _ => ⊤)) : (v : M) ∈ fixd (ρ.comp (atJ n w j)) (iwC _ n ⊤) :=
  (mem_pi ρ _ _).1 v.2 j

variable {ρ} {e : Fin q → Module.End A (fixd ρ (UC n w fun _ => ⊤))}
  (he : ∀ j v, (e j v : M) = dc (ρ.comp (atJ n w j)) (KO _ (Fin n)) (iwC _ n ⊤) 1 v)

include he

private theorem e_K (j : Fin q) (v : fixd ρ (UC n w fun _ => ⊤)) : (e j v : M) ∈ fixd (ρ.comp (atJ n w j)) (KO _ (Fin n)) := by
  rw [he]; exact (dc_K _).1 _ (memI ρ j v)

private theorem e_e (j j' : Fin q) : Commute (e j) (e j') := by
  by_cases h : j = j'
  · subst h; exact Commute.refl _
  · exact comm_res (he j) (he j') (comm_dd ρ h _ _ _ _ _ _)

private theorem fixed_vectors_stable_under_hecke_action (tf : ∀ (k : ℕ) (m : M), k ≠ 0 → k • m = 0 → m = 0) (j : Fin q)
    (f : Module.End A (fixd ρ (UC n w fun _ => ⊤))) (hf : Commute (e j) f) :
    ∀ v ∈ (fixd (ρ.comp (atJ n w j)) (KO _ (Fin n))).comap (fixd ρ (UC n w fun _ => ⊤)).subtype,
      f v ∈ (fixd (ρ.comp (atJ n w j)) (KO _ (Fin n))).comap (fixd ρ (UC n w fun _ => ⊤)).subtype := fun v hv =>
  stab _ _ tf _ (e j) f _ (relIndex_ne _ _ ((heckePairIwC _ n ⊤).2.2 ⊤).2) (e_K he j) hf v
    ((he j v).trans ((dc_K _).2 _ hv))

private theorem e_X {l : ℕ} {x δ : ∀ j, ((w j).adicCompletion L)ˣ} (T : ThData l ρ x δ) (hx : ∀ j, IsUnif (x j))
    (j j' : Fin q) (i : Fin n) (h : j ≠ j') : Commute (e j) (T.actw (MvPolynomial.X (j', i))) := by
  have eΘ : ∀ t, Dom t → Commute (e j) (T.Θw j' t).val := fun t ht =>
    comm_res (he j) (T.hw.1 j' t ht) (comm_dd ρ h _ _ _ _ _ _)
  rw [T.actw_u]
  exact Commute.smul_right (comm_unit ((congrArg (T.Θw j') (fund_split (x j') i)).trans (map_mul _ _ _))
    (eΘ _ (dom_fund (hx j') _)) (eΘ _ (dom_fund (hx j') _))) _

private theorem e_prod (tf : ∀ (k : ℕ) (m : M), k ≠ 0 → k • m = 0 → m = 0) (v : fixd ρ (UC n w fun _ => ⊤)) :
    ((List.ofFn e).prod v : M) ∈ fixd ρ (UK n w) := by
  refine (mem_pi ρ _ _).2 fun j => ?_
  refine lprod_mem ((fixd (ρ.comp (atJ n w j)) (KO _ (Fin n))).comap (fixd ρ (UC n w fun _ => ⊤)).subtype) (e j) (e_K he j) _
    (fun a ha => ?_) (List.mem_ofFn.2 ⟨j, rfl⟩) v
  obtain ⟨j', rfl⟩ := List.mem_ofFn.1 ha
  exact fixed_vectors_stable_under_hecke_action he tf j _ (e_e he j j')

end

theorem UpperTheory.V.Pa.Lev.hkHypOf :
    ∀ (L : Type) [Field L] [NumberField L] (n q : ℕ) (w : Fin q → Plc L) (l : ℕ) (O A M : Type) [CommRing O] [IsDomain O] [CommRing A] [Algebra O A] [AddCommGroup M] [Module A M] (ρ : Representation A (GV n w) M) (x δ : ∀ j, ((w j).adicCompletion L)ˣ) (T : ThData l ρ x δ), (∀ j, IsUnif (x j)) → (∀ j, IsUnit (qj w j : O)) → (∀ (k : ℕ) (m : M), k ≠ 0 → k • m = 0 → m = 0) → ∃ e : Fin q → Module.End A (fixd ρ (UC n w fun _ => ⊤)), HkHyp O (qj w) T.actw e (fun j => (fixd (ρ.comp (atJ n w j)) (KO _ (Fin n))).comap (fixd ρ (UC n w fun _ => ⊤)).subtype) ∧ ∀ v, ((List.ofFn e).prod v : M) ∈ fixd ρ (UK n w) := by
  intro L _ _ n q w l O A M _ _ _ _ _ _ ρ x δ T hx hq tf
  obtain ⟨e, he⟩ : ∃ e : Fin q → Module.End A (fixd ρ (UC n w fun _ => ⊤)), ∀ j v,
      (e j v : M) = dc (ρ.comp (atJ n w j)) (KO _ (Fin n)) (iwC _ n ⊤) 1 v :=
    ⟨fun j => LinearMap.restrict _ (pres ρ j), fun _ _ => rfl⟩
  have hloc := fun j => locA O A M (fixd ρ (UC n w fun _ => ⊤)) (ρ.comp (atJ n w j)) (hx j) (hq j) tf
    (fixd ρ (UC n w fun _ => ⊤)).subtype Subtype.val_injective (memI ρ j) (T.Θw j) (T.hw.1 j) (e j) (he j)
    (T.actw.toRingHom.comp (emb O A j)) (emb_C _ j) (fun i => (emb_X _ j i).trans (T.actw_u j i))
  exact ⟨e, ⟨e_e he, e_X he T hx, fun j => (hloc j).1, fun j => (hloc j).2.1,
    fun j j' i h => fixed_vectors_stable_under_hecke_action he tf j _ (e_X he T hx j j' i h),
    fun j j' _ => fixed_vectors_stable_under_hecke_action he tf j _ (e_e he j j'), fun j => (hloc j).2.2⟩, e_prod he tf⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.TwoMul
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem prod_pairs_dvd {A : Type} [CommRing A] {n : ℕ} (u : Fin n → A) (c : A) :
    ∏ p ∈ Hk.pairs n, (u p.2 - c * u p.1) ∣ ∏ i, ∏ i' ∈ Finset.univ.erase i, (u i - u i') * (u i - c * u i') := by
  have h1 : ∏ p ∈ Hk.pairs n, (u p.2 - c * u p.1) =
      ∏ i, ∏ i' ∈ Finset.univ.filter (fun i' => i' < i), (u i - c * u i') := by
    unfold Hk.pairs
    rw [Finset.prod_filter, ← Finset.univ_product_univ, Finset.prod_product_right]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Finset.prod_filter]
  rw [h1]
  refine Finset.prod_dvd_prod_of_dvd _ _ fun i _ => ?_
  refine (Finset.prod_dvd_prod_of_subset _ (Finset.univ.erase i) _ ?_).trans
    (Finset.prod_dvd_prod_of_dvd _ _ fun i' _ => dvd_mul_left _ _)
  intro i' hi'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi'
  simp [hi'.ne]

private theorem twoMaps_of_dvd {R B M V : Type} [CommRing R] [CommRing B] [AddCommGroup M] [Module B M] [AddCommGroup V]
    [Module R V] {q n : ℕ} (β : R →+* B) (P : Fin q → Polynomial B) (act : PU R q n →ₐ[R] Module.End R V) {f g : PU R q n}
    (hfg : f ∣ g) (h : TwoMaps (M := M) β P act f) : TwoMaps (M := M) β P act g := by
  obtain ⟨c, rfl⟩ := hfg
  obtain ⟨φ, ψ, h1, h2, h3, h4⟩ := h
  refine ⟨φ, ψ.comp (act c).toAddMonoidHom, h1, fun t v => ?_, fun v => ?_, fun z => ?_⟩
  · show ψ (act c (act t v)) = _ • ψ (act c v)
    rw [← h2, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_comm]
  · show φ (ψ (act c v)) = _
    rw [h3, map_mul, Module.End.mul_apply]
  · show ψ (act c (φ z)) = _
    rw [h2, h4, mul_comm f c, map_mul, map_mul, mul_smul]

theorem UpperTheory.V.Pa.Lev.twoMul :
    ∀ (O R B M V : Type) [CommRing O] [CommRing R] [Algebra O R] [CommRing B] [AddCommGroup M] [Module B M] [AddCommGroup V] [Module R V] (q n : ℕ) (β : R →+* B) (P : Fin q → Polynomial B) (act : PU R q n →ₐ[R] Module.End R V) (Nq : Fin q → ℕ), TwoMaps (M := M) β P act (∏ j, emb O R j (Hk.NN n (Nq j : O))) → TwoMaps (M := M) β P act (fEl Nq fun j i => MvPolynomial.X (j, i)) := by
  intro O R B M V _ _ _ _ _ _ _ _ q n β P act Nq h
  refine twoMaps_of_dvd β P act ?_ h
  unfold fEl
  refine Finset.prod_dvd_prod_of_dvd _ _ fun j _ => ?_
  have e : emb O R j (Hk.NN n (Nq j : O)) = ∏ p ∈ Hk.pairs n,
      ((MvPolynomial.X (j, p.2) : PU R q n) - (Nq j : PU R q n) * MvPolynomial.X (j, p.1)) := by
    unfold Hk.NN
    rw [map_prod]
    refine Finset.prod_congr rfl fun p _ => ?_
    simp [emb]
  rw [e]
  exact prod_pairs_dvd (fun i => (MvPolynomial.X (j, i) : PU R q n)) _
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem unit_card (l : ℕ) [hl : Fact l.Prime] (L : Type) [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L))
    (hw : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal) (O : Type) [CommRing O] [IsLocalRing O] [CharP (ResidueField O) l] :
    IsUnit (resCard (w.adicCompletion L) : O) := by
  rw [resCard_eq_normV]
  by_contra hn
  have h1 : residue O (normV w : O) = 0 := (residue_eq_zero_iff _).2 hn
  rw [map_natCast, CharP.cast_eq_zero_iff (ResidueField O) l] at h1
  have hmax := w.isMaximal
  letI : Field (𝓞 L ⧸ w.asIdeal) := Ideal.Quotient.field _
  have hfin : Finite (𝓞 L ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  letI := Fintype.ofFinite (𝓞 L ⧸ w.asIdeal)
  have h2 : l ∣ Fintype.card (𝓞 L ⧸ w.asIdeal) := by
    rw [← Nat.card_eq_fintype_card]; exact h1
  have h3 := (prime_dvd_char_iff_dvd_card (R := 𝓞 L ⧸ w.asIdeal) l).2 h2
  have h4 : ringChar (𝓞 L ⧸ w.asIdeal) = l :=
    ((Nat.prime_dvd_prime_iff_eq hl.out (CharP.char_is_prime (𝓞 L ⧸ w.asIdeal) _)).1 h3).symm
  apply hw
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← h4]
  exact ringChar.Nat.cast_ringChar

private theorem chi_monic {n : ℕ} {A G : Type} [CommRing A] [Nontrivial A] [Group G] (D : GDet n A G) (y : MonoidAlgebra A G) :
    (D.chi y).Monic ∧ (D.chi y).natDegree = n := by
  obtain ⟨h0, -, -, -, h1, h2, -⟩ := UpperTheory.V.CA.d_chi D.toDet y
  rw [Det.lam, pow_zero, one_mul, Nat.sub_zero] at h0
  rw [(UpperTheory.V.CA.d_toDet D y).1] at h0 h1 h2
  exact ⟨h1, le_antisymm h2 (Polynomial.le_natDegree_of_ne_zero (by rw [h0]; exact one_ne_zero))⟩

private theorem lam_comap {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (D : GDet n A G) (φ : H →* G)
    (i : ℕ) (g : H) : (D.comap φ).lam i (MonoidAlgebra.single g 1) = D.lam i (MonoidAlgebra.single (φ g) 1) := by
  have : (D.comap φ).chi (MonoidAlgebra.single g 1) = D.chi (MonoidAlgebra.single (φ g) 1) := by
    change D.D _ (MonoidAlgebra.mapDomainRingHom _ φ _) = D.D _ _
    congr 1
    rw [map_sub]
    simp
  rw [GDet.lam, GDet.lam, this]

private theorem lam_map {n : ℕ} {A A' G : Type} [CommRing A] [CommRing A'] [Group G] (D : GDet n A G) (f : A →+* A')
    (i : ℕ) (g : G) : (D.map f).lam i (MonoidAlgebra.single g 1) = f (D.lam i (MonoidAlgebra.single g 1)) := by
  have := ((UpperTheory.V.CA.d_gmap D).2.2.1 f (MonoidAlgebra.single g 1)).2 i
  rwa [MonoidAlgebra.mapRingHom_single, map_one] at this

private theorem fix_le {L : Type} [Field L] [NumberField L] {n q : ℕ} {w : Fin q → Plc L} {A M : Type} [CommRing A]
    [AddCommGroup M] [Module A M] (ρ : Representation A (GV n w) M) :
    fixd ρ (UK n w) ≤ fixd ρ (UC n w fun _ => ⊤) := by
  intro m hm u hu
  refine hm u fun j _ => ?_
  have h1 : iwC ((w j).adicCompletion L) n ⊤ ≤ KO _ (Fin n) := by
    rw [(memIwC _ n ⊤).2.1]
    exact iwahori_le_KO _ (Fin n)
  exact h1 (hu j trivial)

private theorem fix_at {L : Type} [Field L] [NumberField L] {n q : ℕ} {w : Fin q → Plc L} {A M : Type} [CommRing A]
    [AddCommGroup M] [Module A M] (ρ : Representation A (GV n w) M) (j : Fin q) :
    fixd ρ (UK n w) ≤ fixd (ρ.comp (atJ n w j)) (KO _ (Fin n)) := by
  intro m hm u hu
  refine hm (atJ n w j u) fun j' _ => ?_
  by_cases e : j' = j
  · subst e
    simpa [atJ] using hu
  · simp [atJ, Pi.mulSingle_eq_of_ne e]

private theorem two_gen (L : Type) [Field L] [NumberField L] (n q : ℕ) (w : Fin q → Plc L) (O A B M N : Type)
    [CommRing O] [IsDomain O] [CommRing A] [Algebra O A] [CommRing B] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module B N]
    (ρ : Representation A (GV n w) M) (β : A →+* B) (P : Fin q → Polynomial B)
    (act : PU A q n →ₐ[A] Module.End A (fixd ρ (UC n w fun _ => ⊤)))
    (e : Fin q → Module.End A (fixd ρ (UC n w fun _ => ⊤)))
    (H : HkHyp O (qj w) act e
      (fun j => (fixd (ρ.comp (atJ n w j)) (KO _ (Fin n))).comap (fixd ρ (UC n w fun _ => ⊤)).subtype))
    (he : ∀ v, ((List.ofFn e).prod v : M) ∈ fixd ρ (UK n w))
    (eM : fixd ρ (UK n w) ≃+ N) (hM : ∀ (t : A) m, eM (t • m) = β t • eM m)
    (hP : ∀ j, (P j).Monic ∧ (P j).natDegree = n) (c : Fin q → ℕ → A)
    (hc : ∀ j k, β (c j k) = (-1) ^ k * (P j).coeff (n - k))
    (hs : ∀ j k, k ≤ n → ∀ m : fixd ρ (UC n w fun _ => ⊤), (m : M) ∈ fixd ρ (UK n w) →
      act (emb ℤ A j (MvPolynomial.esymm (Fin n) ℤ k)) m = c j k • m) :
    TwoMaps (M := N) β P act (fEl (qj w) fun j i => MvPolynomial.X (j, i)) := by
  let inc : N →+ fixd ρ (UC n w fun _ => ⊤) :=
    (Submodule.inclusion (fix_le ρ)).toAddMonoidHom.comp eM.symm.toAddMonoidHom
  have hinc : ∀ m, (inc m : M) = eM.symm m := fun _ => rfl
  let t0 : fixd ρ (UC n w fun _ => ⊤) →ₗ[A] fixd ρ (UK n w) :=
    ((fixd ρ (UC n w fun _ => ⊤)).subtype.comp (List.ofFn e).prod).codRestrict _ he
  let tr : fixd ρ (UC n w fun _ => ⊤) →+ N := eM.toAddMonoidHom.comp t0.toAddMonoidHom
  have hβ : ∀ (t : A) m, inc (β t • m) = t • inc m := fun t m => Subtype.ext (by
    obtain ⟨m, rfl⟩ := eM.surjective m
    rw [← hM, Submodule.coe_smul, hinc, hinc, eM.symm_apply_apply, eM.symm_apply_apply, Submodule.coe_smul])
  refine twoMul O A B N _ q n β P act (qj w) (multiTwo O A B N _ q n (qj w) β P act e _ inc tr H (fun j => (hP j).1)
    (fun j => (hP j).2) ?_ hβ (fun v => Subtype.ext ?_) (fun j m => fix_at ρ j (eM.symm m).2) fun j k hk m => ?_)
  · intro a b hab
    have h1 := congrArg Subtype.val hab
    rw [hinc, hinc] at h1
    exact eM.symm.injective (Subtype.ext h1)
  · rw [hinc]
    exact congrArg Subtype.val (eM.symm_apply_apply (t0 v))
  · rw [hs j k hk (inc m) (eM.symm m).2, ← hc, hβ]

theorem UpperTheory.V.Pa.Lev.twoOf :
    LocP → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (V0 : s.Lev) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V0.frame O n) (B : UniversalOrdinaryDeterminantRing r) (J : Ideal B.B) (D : ℕ) (b : TWBase (pairOf B.u) J Empty D) (V : s.Lev) (h : (globOf r V).Hom (globOf r V0)) (q : ℕ) (w : Fin q → Plc L) (A : LevMod b h w) (x δ : ∀ j, ((w j).adicCompletion L)ˣ), (∀ j, ((l : ℕ) : 𝓞 L) ∉ (w j).asIdeal) → (∀ j, IsUnif (x j)) → (∀ j, IsGenMod _ (ellC l _) (δ j)) → ∀ (T : ThData l A.ρ x δ) (ph ta : Fin q → (globOf r V).G₀), LocOk A x δ ph ta → TwoMaps (M := b.M) A.β.toRingHom (fun j => (pairOf B.u).D.chi (MonoidAlgebra.single (h.p₀ (ph j)) 1)) T.actw (fEl (qj w) fun j i => MvPolynomial.X (j, i)) := by
  intro hP l _ L Ω _ _ _ _ _ _ s V0 O _ _ _ _ _ n r B J D b V h q w A x δ hl hx hδ T ph ta hok
  have hs := symOf hP l L Ω s V0 O n r B J D b V h q w A x δ hl hx hδ T ph ta hok
  have hch : CharP (ResidueField O) l := UpperTheory.V.Pa.IsCoef.char
  obtain ⟨ι, hι, -⟩ := hok
  obtain ⟨e, H, he⟩ := hkHypOf L n q w l O A.R A.P A.ρ x δ T hx (fun j => unit_card l L (w j) (hl j) O)
    (fun k m hk hm => hι m fun y => by
      have h1 := congrArg y.sp hm
      rw [map_nsmul, map_zero, ← Nat.cast_smul_eq_nsmul ℂ] at h1
      exact (smul_eq_zero.1 h1).resolve_left (Nat.cast_ne_zero.2 hk))
  refine two_gen L n q w O A.R B.B A.P b.M A.ρ A.β.toRingHom _ T.actw e H he A.eM A.eM_smul
    (fun j => chi_monic _ _) (fun j k => A.p.D.lam k (MonoidAlgebra.single (ph j) 1)) (fun j k => ?_) hs
  exact (lam_map A.p.D A.β.toRingHom k (ph j)).symm.trans
    ((congrArg (fun D' => GDet.lam D' k (MonoidAlgebra.single (ph j) 1)) A.β_pair.1).trans (lam_comap _ _ k _))
