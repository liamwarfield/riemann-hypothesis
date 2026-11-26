module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.ZNClosed
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.ModulusBounds.DetEqOfSurj

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.ModulusBounds.MemK
section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.ModulusBounds.MemStabIff
section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.ModulusBounds.EntIntegral
section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.ModulusBounds.IsClosedGz
noncomputable section

open Matrix Module ValuativeRel GroundTheory.Automorphic.GLnLocal

namespace PositivityTheory.RgUd.T.Nil.Orb.BModbound

open PositivityTheory.RgUd.T

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem isClosed_Gz (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : IsClosed (Gz Z : Set (GL (Fin n) k)) := by
  have : (Gz Z : Set (GL (Fin n) k)) = ⋂ a ∈ Z, {g : GL (Fin n) k | a * g.val = g.val * a} := by
    ext g; simp [Gz]
  rw [this]
  exact isClosed_biInter fun a _ => isClosed_eq (continuous_const.matrix_mul Units.continuous_val)
    (Units.continuous_val.matrix_mul continuous_const)

private theorem exists_uniformizer_pow_mul_valuation_le_one (a : k) : ∃ e : ℕ,
    valuation k (GroundTheory.Automorphic.GLnLocal.uniformizer k : k) ^ e * valuation k a ≤ 1 := by
  by_cases ha : valuation k a ≤ 1
  · exact ⟨0, by rw [pow_zero, one_mul]; exact ha⟩
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact ha (by rw [map_zero]; exact zero_le')
  have hinv : valuation k a⁻¹ ≤ 1 := by
    rw [map_inv₀]
    exact inv_le_one_of_one_le₀ (le_of_lt (not_le.mp ha))
  set b : 𝒪[k] := ⟨a⁻¹, hinv⟩ with hb
  have hb0 : b ≠ 0 := by
    intro h
    have h' : (b : k) = 0 := by rw [h]; rfl
    exact inv_ne_zero ha0 h'
  have hirr : Irreducible (GroundTheory.Automorphic.GLnLocal.uniformizer k) := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer]
    have h := maximalIdeal_pow_eq k 1
    rw [pow_one, pow_one] at h
    exact h
  obtain ⟨e, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hb0 hirr
  refine ⟨e, ?_⟩
  have h1 : valuation k (GroundTheory.Automorphic.GLnLocal.uniformizer k : k) ^ e ≤ valuation k a⁻¹ := by
    have h2 : (GroundTheory.Automorphic.GLnLocal.uniformizer k : k) ^ e = a⁻¹ * ((u : 𝒪[k]) : k) := by
      have h3 := congrArg (fun z : 𝒪[k] => (z : k)) hu
      simpa [hb] using h3.symm
    rw [← map_pow, h2, map_mul]
    calc _ ≤ valuation k a⁻¹ * 1 := mul_le_mul_right (u : 𝒪[k]).2 _
      _ = _ := mul_one _
  calc _ ≤ valuation k a⁻¹ * valuation k a := mul_le_mul_left h1 _
    _ = 1 := by rw [← map_mul, inv_mul_cancel₀ ha0, map_one]

private theorem mul_mul_apply_mem_integers_of_valuation_bounds (E : ℕ) (P Q y : Matrix (Fin n) (Fin n) k)
    (hP : ∀ i j, valuation k (GroundTheory.Automorphic.GLnLocal.uniformizer k : k) ^ E * valuation k (P i j) ≤ 1)
    (hQ : ∀ i j, valuation k (GroundTheory.Automorphic.GLnLocal.uniformizer k : k) ^ E * valuation k (Q i j) ≤ 1)
    (hy : ∀ i j, valuation k (y i j) ≤ valuation k (GroundTheory.Automorphic.GLnLocal.uniformizer k : k) ^ E *
      valuation k (GroundTheory.Automorphic.GLnLocal.uniformizer k : k) ^ E)
    (i j : Fin n) : (P * y * Q) i j ∈ 𝒪[k] := by
  set c := valuation k (GroundTheory.Automorphic.GLnLocal.uniformizer k : k) ^ E with hc
  rw [Matrix.mul_apply]
  refine sum_mem fun b _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul]
  refine sum_mem fun a _ => ?_
  show valuation k (P i a * y a b * Q b j) ≤ 1
  rw [map_mul, map_mul]
  calc valuation k (P i a) * valuation k (y a b) * valuation k (Q b j)
      ≤ valuation k (P i a) * (c * c) * valuation k (Q b j) :=
        mul_le_mul_left (mul_le_mul_right (hy a b) _) _
    _ = (c * valuation k (P i a)) * (c * valuation k (Q b j)) := by ac_rfl
    _ ≤ 1 * 1 := mul_le_mul' (hP i a) (hQ b j)
    _ = 1 := one_mul 1

theorem exists_level (g : GL (Fin n) k) : ∃ m : ℕ, 1 ≤ m ∧ ∀ u ∈ congruenceSubgroup k n m,
    g⁻¹ * u * g ∈ integralGL k n ∧ g * u * g⁻¹ ∈ integralGL k n := by
  classical
  choose e he using fun a : k => exists_uniformizer_pow_mul_valuation_le_one (k := k) a
  set A : Matrix (Fin n) (Fin n) k := (g : Matrix (Fin n) (Fin n) k) with hA
  set B : Matrix (Fin n) (Fin n) k := ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) with hB
  set E : ℕ := ∑ i, ∑ j, (e (A i j) + e (B i j)) with hE
  have hπ1 : valuation k (GroundTheory.Automorphic.GLnLocal.uniformizer k : k) ≤ 1 :=
    (GroundTheory.Automorphic.GLnLocal.uniformizer k).2
  have hbound : ∀ a : k, e a ≤ E →
      valuation k (GroundTheory.Automorphic.GLnLocal.uniformizer k : k) ^ E * valuation k a ≤ 1 := by
    intro a ha
    exact le_trans (mul_le_mul_left (pow_le_pow_right_of_le_one' hπ1 ha) _) (he a)
  have hrow : ∀ i j, e (A i j) + e (B i j) ≤ E := by
    intro i j
    calc e (A i j) + e (B i j) ≤ ∑ j', (e (A i j') + e (B i j')) :=
          Finset.single_le_sum (f := fun j' => e (A i j') + e (B i j'))
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      _ ≤ E := Finset.single_le_sum (f := fun i' => ∑ j', (e (A i' j') + e (B i' j')))
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have heA : ∀ i j, e (A i j) ≤ E := fun i j => le_trans (Nat.le_add_right _ _) (hrow i j)
  have heB : ∀ i j, e (B i j) ≤ E := fun i j => le_trans (Nat.le_add_left _ _) (hrow i j)
  have hBA : B * A = 1 := Units.inv_mul g
  have hAB : A * B = 1 := Units.mul_inv g
  have h1 : ∀ i j, (1 : Matrix (Fin n) (Fin n) k) i j ∈ 𝒪[k] := by
    intro i j
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  refine ⟨2 * E + 1, by omega, ?_⟩
  have hconj : ∀ w ∈ congruenceSubgroup k n (2 * E + 1), ∀ i j,
      ((g⁻¹ * w * g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j ∈ 𝒪[k] ∧
      ((g * w * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j ∈ 𝒪[k] := by
    intro w hw i j
    rw [mem_congruenceSubgroup_iff] at hw
    set y : Matrix (Fin n) (Fin n) k := (w : Matrix (Fin n) (Fin n) k) - 1 with hy
    have hw' : (w : Matrix (Fin n) (Fin n) k) = 1 + y := by rw [hy]; abel
    have hyb : ∀ a b, valuation k (y a b) ≤
        valuation k (GroundTheory.Automorphic.GLnLocal.uniformizer k : k) ^ E *
          valuation k (GroundTheory.Automorphic.GLnLocal.uniformizer k : k) ^ E := by
      intro a b
      rw [← pow_add]
      exact le_trans (hw.2 a b) (pow_le_pow_right_of_le_one' hπ1 (by omega))
    constructor
    · rw [Units.val_mul, Units.val_mul, ← hB, ← hA, hw', Matrix.mul_add, Matrix.add_mul,
        Matrix.mul_one, hBA, Matrix.add_apply]
      exact add_mem (h1 i j) (mul_mul_apply_mem_integers_of_valuation_bounds E B A y (fun i j => hbound _ (heB i j))
        (fun i j => hbound _ (heA i j)) hyb i j)
    · rw [Units.val_mul, Units.val_mul, ← hB, ← hA, hw', Matrix.mul_add, Matrix.add_mul,
        Matrix.mul_one, hAB, Matrix.add_apply]
      exact add_mem (h1 i j) (mul_mul_apply_mem_integers_of_valuation_bounds E A B y (fun i j => hbound _ (heA i j))
        (fun i j => hbound _ (heB i j)) hyb i j)
  intro u hu
  refine ⟨?_, ?_⟩
  · rw [mem_integralGL_iff]
    refine ⟨fun i j => (hconj u hu i j).1, fun i j => ?_⟩
    have hinv : (g⁻¹ * u * g)⁻¹ = g⁻¹ * u⁻¹ * g := by group
    rw [hinv]
    exact (hconj u⁻¹ (inv_mem hu) i j).1
  · rw [mem_integralGL_iff]
    refine ⟨fun i j => (hconj u hu i j).2, fun i j => ?_⟩
    have hinv : (g * u * g⁻¹)⁻¹ = g * u⁻¹ * g⁻¹ := by group
    rw [hinv]
    exact (hconj u⁻¹ (inv_mem hu) i j).2

theorem exists_unit (m : ℕ) (hm : 1 ≤ m) (x : Matrix (Fin n) (Fin n) k)
    (hx : ∀ i j, valuation k (x i j) ≤ valuation k (uniformizer k : k) ^ m) :
    ∃ u ∈ congruenceSubgroup k n m, u.val = 1 + x := by
  classical
  set π := GroundTheory.Automorphic.GLnLocal.uniformizer k with hπ
  have hπm : π ∈ 𝓂[k] := by
    have h := maximalIdeal_pow_eq k 1
    rw [pow_one, pow_one] at h
    rw [h]
    exact Ideal.subset_span rfl
  have hπ1 : valuation k (π : k) < 1 := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hπm
    exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp hπm
  have hle : ∀ i j, valuation k (x i j) < 1 := fun i j =>
    lt_of_le_of_lt (hx i j) (pow_lt_one₀ zero_le' hπ1 (by omega))
  let X : Matrix (Fin n) (Fin n) 𝒪[k] := fun i j => ⟨x i j, (hle i j).le⟩
  have hXm : ∀ i j, X i j ∈ 𝓂[k] := fun i j => by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.mpr (hle i j)
  have hdet : IsUnit (1 + X).det := by
    have h1 : (IsLocalRing.residue 𝒪[k]) (1 + X).det = 1 := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_add _ (map_add _),
        Matrix.map_one _ (map_zero _) (map_one _)]
      have h0 : X.map (IsLocalRing.residue 𝒪[k]) = 0 := by
        ext i j
        simpa [IsLocalRing.residue_eq_zero_iff] using hXm i j
      rw [h0, add_zero, Matrix.det_one]
    by_contra h
    have hm : (1 + X).det ∈ IsLocalRing.maximalIdeal 𝒪[k] := h
    rw [← IsLocalRing.residue_eq_zero_iff] at hm
    rw [hm] at h1
    exact zero_ne_one h1
  have hU : IsUnit (1 + X) := (Matrix.isUnit_iff_isUnit_det _).mpr hdet
  have hentry : ∀ i j, (((1 + X) i j : 𝒪[k]) : k) = (1 : Matrix (Fin n) (Fin n) k) i j + x i j := by
    intro i j
    show (((1 : Matrix (Fin n) (Fin n) 𝒪[k]) i j : 𝒪[k]) : k) + x i j = _
    congr 1
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  refine ⟨integralGLHom k n hU.unit, ?_, ?_⟩
  · rw [mem_congruenceSubgroup_iff]
    refine ⟨⟨hU.unit, rfl⟩, fun i j => ?_⟩
    rw [integralGLHom_apply, IsUnit.unit_spec, hentry, add_sub_cancel_left]
    exact hx i j
  · ext i j
    rw [integralGLHom_apply, IsUnit.unit_spec, hentry, Matrix.add_apply]

end PositivityTheory.RgUd.T.Nil.Orb.BModbound
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.ModulusBounds.RelIndexEq
namespace PositivityTheory.RgUd.T.Nil.Orb.BModbound

theorem relIndex_eq {k : Type} [Field k] {n : ℕ} (I J : AddSubgroup (Matrix (Fin n) (Fin n) k))
    (GI GJ : Subgroup (GL (Fin n) k)) (hJI : J ≤ I)
    (hGI : ∀ u : GL (Fin n) k, u ∈ GI ↔ u.val - 1 ∈ I)
    (hGJ : ∀ u : GL (Fin n) k, u ∈ GJ ↔ u.val - 1 ∈ J)
    (hsurj : ∀ x ∈ I, ∃ u : GL (Fin n) k, u.val = 1 + x)
    (hmul : ∀ u ∈ GI, ∀ y ∈ J, u.val * y ∈ J) :
    GJ.relIndex GI = J.relIndex I := by
  classical
  have hinv : ∀ x ∈ I, ∃ u : GL (Fin n) k, u ∈ GI ∧ u.val = 1 + x := fun x hx => by
    obtain ⟨u, hu⟩ := hsurj x hx
    refine ⟨u, (hGI u).2 ?_, hu⟩
    rw [hu, add_sub_cancel_left]
    exact hx
  let f : GI → I := fun u => ⟨u.1.val - 1, (hGI u.1).1 u.2⟩
  have hf_inj : Function.Injective f := by
    intro a b hab
    have h : a.1.val - 1 = b.1.val - 1 := congrArg Subtype.val hab
    exact Subtype.ext (Units.ext (sub_left_inj.mp h))
  have hf_surj : Function.Surjective f := by
    intro x
    obtain ⟨u, hu, hux⟩ := hinv x.1 x.2
    refine ⟨⟨u, hu⟩, Subtype.ext ?_⟩
    show u.val - 1 = x.1
    rw [hux, add_sub_cancel_left]
  let e : GI ≃ I := Equiv.ofBijective f ⟨hf_inj, hf_surj⟩
  have key : ∀ a b : GI, (QuotientGroup.leftRel (GJ.subgroupOf GI)) a b ↔
      (QuotientAddGroup.leftRel (J.addSubgroupOf I)) (e a) (e b) := by
    intro a b
    rw [QuotientGroup.leftRel_apply, QuotientAddGroup.leftRel_apply, Subgroup.mem_subgroupOf,
      AddSubgroup.mem_addSubgroupOf]
    show ((a.1⁻¹ * b.1 : GL (Fin n) k)) ∈ GJ ↔ -(a.1.val - 1) + (b.1.val - 1) ∈ J
    have h1 : -(a.1.val - 1) + (b.1.val - 1) = b.1.val - a.1.val := by abel
    rw [h1, hGJ, Units.val_mul]
    have ha : a.1⁻¹ ∈ GI := GI.inv_mem a.2
    constructor
    · intro h
      have h2 := hmul a.1 a.2 _ h
      have e2 : a.1.val * ((a.1⁻¹).val * b.1.val - 1) = b.1.val - a.1.val := by
        rw [mul_sub, ← mul_assoc, Units.mul_inv, one_mul, mul_one]
      rwa [e2] at h2
    · intro h
      have h2 := hmul a.1⁻¹ ha _ h
      have e2 : (a.1⁻¹).val * (b.1.val - a.1.val) = (a.1⁻¹).val * b.1.val - 1 := by
        rw [mul_sub, Units.inv_mul]
      rwa [e2] at h2
  have hc := Nat.card_congr (Quotient.congr e key)
  exact hc

end PositivityTheory.RgUd.T.Nil.Orb.BModbound
end

noncomputable section

set_option linter.unusedSectionVars false

open Matrix Module ValuativeRel MeasureTheory GroundTheory.Automorphic.GLnLocal

namespace PositivityTheory.RgUd.T.Nil.Orb.BModbound

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

def lat (V : Submodule k (Matrix (Fin n) (Fin n) k)) (γ : ValueGroupWithZero k) :
    AddSubgroup (Matrix (Fin n) (Fin n) k) where
  carrier := {y | y ∈ V ∧ ∀ i j, valuation k (y i j) ≤ γ}
  add_mem' {a b} ha hb := ⟨V.add_mem ha.1 hb.1, fun i j => by
    simp only [Matrix.add_apply]
    exact (Valuation.map_add _ _ _).trans (max_le (ha.2 i j) (hb.2 i j))⟩
  zero_mem' := ⟨V.zero_mem, fun i j => by simp⟩
  neg_mem' {a} ha := ⟨V.neg_mem ha.1, fun i j => by
    simp only [Matrix.neg_apply, Valuation.map_neg]
    exact ha.2 i j⟩

theorem mem_lat {V : Submodule k (Matrix (Fin n) (Fin n) k)} {γ : ValueGroupWithZero k}
    {y : Matrix (Fin n) (Fin n) k} : y ∈ lat V γ ↔ y ∈ V ∧ ∀ i j, valuation k (y i j) ≤ γ := Iff.rfl

def cj (g : GL (Fin n) k) (X : AddSubgroup (Matrix (Fin n) (Fin n) k)) : AddSubgroup (Matrix (Fin n) (Fin n) k) :=
  X.comap (adL g⁻¹).toAddMonoidHom

theorem mem_cj {g : GL (Fin n) k} {X : AddSubgroup (Matrix (Fin n) (Fin n) k)} {y : Matrix (Fin n) (Fin n) k} :
    y ∈ cj g X ↔ g⁻¹.val * y * g.val ∈ X := by
  simp [cj, adL_apply]

theorem adL_inv_adL (g : GL (Fin n) k) (y : Matrix (Fin n) (Fin n) k) : g⁻¹.val * (g.val * y * g⁻¹.val) * g.val = y := by
  simp [← mul_assoc]

theorem adL_adL_inv (g : GL (Fin n) k) (y : Matrix (Fin n) (Fin n) k) : g.val * (g⁻¹.val * y * g.val) * g⁻¹.val = y := by
  simp [← mul_assoc]

theorem ent_mul {γ : ValueGroupWithZero k} {a b : Matrix (Fin n) (Fin n) k} (ha : ∀ i j, valuation k (a i j) ≤ 1)
    (hb : ∀ i j, valuation k (b i j) ≤ γ) : ∀ i j, valuation k ((a * b) i j) ≤ γ := by
  intro i j
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun l _ => ?_
  rw [Valuation.map_mul]
  calc valuation k (a i l) * valuation k (b l j) ≤ 1 * γ := mul_le_mul' (ha i l) (hb l j)
    _ = γ := one_mul γ

theorem ent_integral {u : GL (Fin n) k} (hu : u ∈ integralGL k n) : ∀ i j, valuation k (u.val i j) ≤ 1 :=
  fun i j => ((mem_integralGL_iff k n).1 hu).1 i j

theorem mem_C_iff (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (y : Matrix (Fin n) (Fin n) k) :
    y ∈ (Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))).toSubmodule ↔ y ∈ Bz Z := by
  rw [Subalgebra.mem_toSubmodule, Subalgebra.mem_centralizer_iff]
  rfl

theorem mem_Gz_iff (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (u : GL (Fin n) k) :
    u ∈ Gz Z ↔ u.val - 1 ∈ Bz Z := by
  constructor
  · intro h a ha
    rw [mul_sub, sub_mul, h a ha, mul_one, one_mul]
  · intro h a ha
    have := h a ha
    rw [mul_sub, sub_mul, mul_one, one_mul] at this
    exact sub_left_inj.1 this

theorem Bz_mul (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) {a b : Matrix (Fin n) (Fin n) k} (ha : a ∈ Bz Z)
    (hb : b ∈ Bz Z) : a * b ∈ Bz Z := fun z hz => by
  rw [← mul_assoc, ha z hz, mul_assoc, hb z hz, mul_assoc]

theorem Bz_conj (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) {g : GL (Fin n) k} (hg : g ∈ Gz Z)
    {a : Matrix (Fin n) (Fin n) k} (ha : a ∈ Bz Z) : g.val * a * g⁻¹.val ∈ Bz Z := by
  have := cC_inv Z g hg a ((mem_C_iff Z a).2 ha)
  rw [adL_apply] at this
  exact (mem_C_iff Z _).1 this

theorem Gz_inv (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) {g : GL (Fin n) k} (hg : g ∈ Gz Z) : g⁻¹ ∈ Gz Z :=
  (GzS Z).inv_mem hg

end PositivityTheory.RgUd.T.Nil.Orb.BModbound
end
end

noncomputable section

set_option linter.unusedSectionVars false

open Matrix Module ValuativeRel MeasureTheory GroundTheory.Automorphic.GLnLocal

namespace PositivityTheory.RgUd.T.Nil.Orb.BModbound

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem conj_sub_one (g u : GL (Fin n) k) : (g⁻¹ * u * g).val - 1 = g⁻¹.val * (u.val - 1) * g.val := by
  simp only [Units.val_mul, mul_sub, sub_mul, mul_one, Units.inv_mul]

theorem mem_stab_iff (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (c : Matrix (Fin n) (Fin n) k)
    (p : Sp k n) (u : GL (Fin n) k) (hcu : u.val * c = c * u.val) (hu : u.val - 1 ∈ Bz Z) :
    u ∈ stab Z p ↔ u.val - 1 ∈ cS Z (p.1 - c) p.2 := by
  have e : (u.val - 1) * (p.1 - c) - (p.1 - c) * (u.val - 1) =
      (u.val * p.1 - p.1 * u.val) - (u.val * c - c * u.val) := by noncomm_ring
  rw [hcu, sub_self, sub_zero] at e
  have e1 : (u.val - 1) * (p.1 - c) = (p.1 - c) * (u.val - 1) ↔ u.val * p.1 = p.1 * u.val := by
    rw [← sub_eq_zero, e, sub_eq_zero]
  have e2 : u.val * p.1 * u⁻¹.val = p.1 ↔ u.val * p.1 = p.1 * u.val := by
    constructor
    · intro h
      calc u.val * p.1 = u.val * p.1 * u⁻¹.val * u.val := by simp [mul_assoc]
        _ = p.1 * u.val := by rw [h]
    · intro h
      rw [h, mul_assoc, Units.mul_inv, mul_one]
  have e3 : u.val *ᵥ p.2 = p.2 ↔ (u.val - 1) *ᵥ p.2 = 0 := by
    rw [sub_mulVec, one_mulVec, sub_eq_zero]
  show (u ∈ Gz Z ∧ act u p = p) ↔ _
  rw [mem_Gz_iff]
  simp only [act, Prod.ext_iff]
  constructor
  · rintro ⟨-, h1, h2⟩
    exact ⟨⟨hu, e1.2 (e2.1 h1)⟩, e3.1 h2⟩
  · rintro ⟨⟨-, h1⟩, h2⟩
    exact ⟨hu, e2.2 (e1.1 h1), e3.2 h2⟩

end PositivityTheory.RgUd.T.Nil.Orb.BModbound
end
end

noncomputable section

set_option linter.unusedSectionVars false

open Matrix Module ValuativeRel MeasureTheory GroundTheory.Automorphic.GLnLocal

namespace PositivityTheory.RgUd.T.Nil.Orb.BModbound

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem memK (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (m : ℕ) (hm : 1 ≤ m) (u : GL (Fin n) k) :
    u ∈ congruenceSubgroup k n m ⊓ GzS Z ↔
      u.val - 1 ∈ lat (Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))).toSubmodule
        (valuation k (uniformizer k : k) ^ m) := by
  rw [Subgroup.mem_inf, mem_lat, mem_C_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨(mem_Gz_iff Z u).1 h2, fun i j => ?_⟩
    have := ((mem_congruenceSubgroup_iff k n).1 h1).2 i j
    simpa [Matrix.sub_apply] using this
  · rintro ⟨h1, h2⟩
    obtain ⟨w, hw, hwv⟩ := exists_unit (k := k) m hm (u.val - 1) h2
    have : w = u := Units.ext (by rw [hwv]; abel)
    exact ⟨this ▸ hw, (mem_Gz_iff Z u).2 h1⟩

theorem memK' (K : Subgroup (GL (Fin n) k)) (g u : GL (Fin n) k) :
    u ∈ K.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * u * g ∈ K := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

end PositivityTheory.RgUd.T.Nil.Orb.BModbound
end
end

noncomputable section

set_option linter.unusedSectionVars false

open Matrix Module ValuativeRel MeasureTheory GroundTheory.Automorphic.GLnLocal

namespace PositivityTheory.RgUd.T.Nil.Orb.BModbound

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

def RatioP (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) : Prop :=
  ∀ (V : Submodule k (Matrix (Fin n) (Fin n) k)) (γ : ValueGroupWithZero k), γ ≠ 0 →
    ∀ (φ : V ≃ₗ[k] V) (X Y : AddSubgroup (Matrix (Fin n) (Fin n) k)),
    (∀ y, y ∈ X ↔ y ∈ V ∧ ∀ i j, valuation k (y i j) ≤ γ) →
    (∀ y, y ∈ Y ↔ ∃ x : V, (x : Matrix (Fin n) (Fin n) k) ∈ X ∧ ((φ x : V) : Matrix (Fin n) (Fin n) k) = y) →
    (X ⊓ Y).relIndex X ≠ 0 ∧ (X ⊓ Y).relIndex Y ≠ 0 ∧
      ((X ⊓ Y).relIndex Y : ℝ) / ((X ⊓ Y).relIndex X : ℝ) = (distribHaarChar k (LinearEquiv.det φ) : ℝ)

theorem adL_restrict_inj (g : GL (Fin n) k) (W : Submodule k (Matrix (Fin n) (Fin n) k))
    (hW : ∀ a ∈ W, adL g a ∈ W) : Function.Injective ((adL g).restrict hW) := by
  intro a b hab
  apply Subtype.ext
  have h := congrArg (fun z : W => g⁻¹.val * (z : Matrix (Fin n) (Fin n) k) * g.val) hab
  simp only [LinearMap.coe_restrict_apply, adL_apply, adL_inv_adL] at h
  exact h

theorem mem_cj_iff_exists (g : GL (Fin n) k) (W : Submodule k (Matrix (Fin n) (Fin n) k))
    (hW : ∀ a ∈ W, adL g a ∈ W) (γ : ValueGroupWithZero k) (y : Matrix (Fin n) (Fin n) k) :
    y ∈ cj g (lat W γ) ↔ ∃ z : W, (z : Matrix (Fin n) (Fin n) k) ∈ lat W γ ∧
      ((LinearEquiv.ofInjectiveEndo _ (adL_restrict_inj g W hW) z : W) : Matrix (Fin n) (Fin n) k) = y := by
  rw [mem_cj]
  constructor
  · intro h
    refine ⟨⟨_, (mem_lat.1 h).1⟩, h, ?_⟩
    rw [LinearEquiv.coe_ofInjectiveEndo, LinearMap.coe_restrict_apply, adL_apply, adL_adL_inv]
  · rintro ⟨z, hz, rfl⟩
    rw [LinearEquiv.coe_ofInjectiveEndo, LinearMap.coe_restrict_apply, adL_apply, adL_inv_adL]
    exact hz

theorem det_ofInjectiveEndo (g : GL (Fin n) k) (W : Submodule k (Matrix (Fin n) (Fin n) k))
    (hW : ∀ a ∈ W, adL g a ∈ W) :
    ((LinearEquiv.det (LinearEquiv.ofInjectiveEndo _ (adL_restrict_inj g W hW)) : kˣ) : k) =
      LinearMap.det ((adL g).restrict hW) := by
  rw [LinearEquiv.coe_det]
  congr 1

theorem comm_of_mem_cS (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (x : Matrix (Fin n) (Fin n) k)
    (v : Fin n → k) (u : GL (Fin n) k) (h : u.val - 1 ∈ cS Z x v) : u.val * x = x * u.val := by
  have h2 := h.1.2
  rw [sub_mul, mul_sub, one_mul, mul_one] at h2
  exact sub_left_inj.1 h2

end PositivityTheory.RgUd.T.Nil.Orb.BModbound
