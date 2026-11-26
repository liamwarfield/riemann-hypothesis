module

public import Mathlib

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MSplitDefs
noncomputable section

open Polynomial

namespace UpperTheory.V.AlgebraTools

variable {R κ : Type} [CommRing R] (P : κ → R[X]) (n : ℕ)

def mSplitIdeal : Ideal (MvPolynomial (κ × Fin n) R) :=
  Ideal.span (Set.range fun jk : κ × ℕ =>
    (∏ i : Fin n, (X - C (MvPolynomial.X (jk.1, i) : MvPolynomial (κ × Fin n) R)) -
      (P jk.1).map MvPolynomial.C).coeff jk.2)

abbrev MSplitAlg : Type := MvPolynomial (κ × Fin n) R ⧸ mSplitIdeal P n

def MSplitAlg.root (j : κ) (i : Fin n) : MSplitAlg P n := Ideal.Quotient.mk _ (MvPolynomial.X (j, i))

theorem MSplitAlg.prod_root (j : κ) :
    ∏ i : Fin n, (X - C (MSplitAlg.root P n j i)) = (P j).map (algebraMap R (MSplitAlg P n)) := by
  have h : (∏ i : Fin n, (X - C (MvPolynomial.X (j, i) : MvPolynomial (κ × Fin n) R)) -
      (P j).map MvPolynomial.C).map (Ideal.Quotient.mk (mSplitIdeal P n)) = 0 := by
    ext k
    rw [coeff_map, coeff_zero, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span ⟨(j, k), rfl⟩
  rw [Polynomial.map_sub, Polynomial.map_prod, Polynomial.map_map, sub_eq_zero] at h
  simp only [Polynomial.map_sub, map_X, map_C] at h
  exact h

def MSplitAlg.lift {A : Type} [CommRing A] [Algebra R A] (a : κ → Fin n → A)
    (h : ∀ j, ∏ i : Fin n, (X - C (a j i)) = (P j).map (algebraMap R A)) : MSplitAlg P n →ₐ[R] A :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval fun p : κ × Fin n => a p.1 p.2) fun x hx => by
    refine (Ideal.span_le (I := RingHom.ker
      (MvPolynomial.aeval fun p : κ × Fin n => a p.1 p.2 : MvPolynomial (κ × Fin n) R →ₐ[R] A))).2 ?_ hx
    rintro _ ⟨⟨j, k⟩, rfl⟩
    have h2 : (∏ i : Fin n, (X - C (MvPolynomial.X (j, i) : MvPolynomial (κ × Fin n) R)) -
        (P j).map MvPolynomial.C).map
        (MvPolynomial.aeval fun p : κ × Fin n => a p.1 p.2 : MvPolynomial (κ × Fin n) R →ₐ[R] A).toRingHom = 0 := by
      rw [Polynomial.map_sub, Polynomial.map_prod, Polynomial.map_map, sub_eq_zero]
      have h3 : (MvPolynomial.aeval fun p : κ × Fin n => a p.1 p.2 :
          MvPolynomial (κ × Fin n) R →ₐ[R] A).toRingHom.comp MvPolynomial.C = algebraMap R A :=
        RingHom.ext fun r => by simp
      rw [h3, ← h j]
      simp
    have h4 := congrArg (fun q => q.coeff k) h2
    simp only [coeff_map, coeff_zero] at h4
    exact h4

theorem MSplitAlg.lift_root {A : Type} [CommRing A] [Algebra R A] (a : κ → Fin n → A)
    (h : ∀ j, ∏ i : Fin n, (X - C (a j i)) = (P j).map (algebraMap R A)) (j : κ) (i : Fin n) :
    MSplitAlg.lift P n a h (MSplitAlg.root P n j i) = a j i :=
  MvPolynomial.aeval_X (fun p : κ × Fin n => a p.1 p.2) (j, i)

theorem MSplitAlg.hom_ext {A : Type} [CommRing A] [Algebra R A] {f g : MSplitAlg P n →ₐ[R] A}
    (h : ∀ j i, f (MSplitAlg.root P n j i) = g (MSplitAlg.root P n j i)) : f = g :=
  Ideal.Quotient.algHom_ext _ (MvPolynomial.algHom_ext fun p => h p.1 p.2)

end UpperTheory.V.AlgebraTools
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DualLattice
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DualLatticeDenominator
theorem UpperTheory.Reformulated.B.ExistsSmulMemOfIsLattice₂.dual_lattice_denom :
    ∀ {A : Type} [inst : CommRing A]
    [IsDomain A] {F V : Type} [inst_2 : Field F] [inst_3 : Algebra A F] [IsFractionRing A F] [inst_5 : AddCommGroup V]
    [inst_6 : _root_.Module F V] [inst_7 : _root_.Module A V] [inst_8 : IsScalarTower A F V] (Y : Submodule A V),
    Submodule.IsFullLattice F Y → ∀ (z : V), ∃ (a : A), a ≠ (0 : A) ∧ a • z ∈ Y := by
  intro A _ _ F V _ _ _ _ _ _ _ Y hY z
  have hz : z ∈ Submodule.span F (Y : Set V) := by
    rw [hY.span_eq_top]; exact Submodule.mem_top
  induction hz using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine Y.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact Y.smul_mem b hax
    · rw [mul_smul]; exact Y.smul_mem a hby
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨⟨d, hd⟩, n, hn⟩ := IsLocalization.exists_integer_multiple (nonZeroDivisors A) c
    refine ⟨a * d, mul_ne_zero ha (nonZeroDivisors.ne_zero hd), ?_⟩
    have h : (a * d) • c • x = n • a • x := by
      rw [mul_smul, ← smul_assoc d c x]
      have h2 : d • c = algebraMap A F n := hn.symm
      rw [h2, algebraMap_smul, smul_comm]
    rw [h]
    exact Y.smul_mem n hax
end

open Polynomial Matrix IsLocalRing TensorProduct

private theorem UpperTheory.V.AlgebraTools.dual_lattice_denom {A : Type} [CommRing A] [IsDomain A]
    {F V : Type} [Field F] [Algebra A F] [IsFractionRing A F] [AddCommGroup V] [Module F V]
    [Module A V] [IsScalarTower A F V] (Y : Submodule A V) (hY : Submodule.IsFullLattice F Y)
    (z : V) : ∃ a : A, a ≠ 0 ∧ a • z ∈ Y :=
  _root_.UpperTheory.Reformulated.B.ExistsSmulMemOfIsLattice₂.dual_lattice_denom Y hY z

private theorem UpperTheory.V.AlgebraTools.dual_lattice_pow {A : Type} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] (a : A) (ha : a ≠ 0) :
    ∃ s : ℕ, maximalIdeal A ^ s ≤ Ideal.span {a} := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  refine ⟨n, ?_⟩
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_singleton_le_span_singleton]
  exact (Units.isUnit u).mul_left_dvd.mpr dvd_rfl

theorem UpperTheory.V.AlgebraTools.dual_lattice :
    ∀ {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] {F V : Type} [Field F] [Algebra A F] [IsFractionRing A F] [AddCommGroup V] [Module F V] [Module A V] [IsScalarTower A F V] [Module.Finite F V] (Bf : LinearMap.BilinForm F V), Bf.IsSymm → Bf.Nondegenerate → ∀ Y : Submodule A V, Submodule.IsFullLattice F Y → Submodule.IsFullLattice F (Bf.dualSubmodule Y) ∧ Bf.dualSubmodule (Bf.dualSubmodule Y) = Y ∧ ∀ Z : Submodule A V, Submodule.IsLattice F Z → ∃ s : ℕ, maximalIdeal A ^ s • Z ≤ Y := by
  intro A _ _ _ F V _ _ _ _ _ _ _ _ Bf hs hn Y hY
  classical
  haveI : Module.Free A Y := Submodule.IsLattice.free F Y
  haveI : Module.Finite A Y := Submodule.IsLattice.finite F Y
  let b0 := Module.Free.chooseBasis A Y
  let b := b0.extendOfIsFullLattice F
  have hb : Submodule.span A (Set.range b) = Y := by
    have : (b : _ → V) = Y.subtype ∘ b0 := by
      funext i; simp [b]
    rw [this, Set.range_comp, ← Submodule.map_span, b0.span_eq, Submodule.map_top,
      Submodule.range_subtype]
  refine ⟨?_, ?_, ?_⟩
  · rw [← hb, LinearMap.BilinForm.dualSubmodule_span_of_basis Bf hn b]
    exact { toIsLattice := Submodule.IsLattice.of_fg _ (Submodule.fg_span (Set.finite_range _))
            span_eq_top := by rw [Submodule.span_span_of_tower, Module.Basis.span_eq] }
  · rw [← hb]
    exact LinearMap.BilinForm.dualSubmodule_dualSubmodule_of_basis Bf hn hs b
  · intro Z hZ
    have hfg := hZ.fg
    clear hZ
    induction Z, hfg using Submodule.fg_induction with
    | singleton x =>
      obtain ⟨a, ha, hax⟩ := UpperTheory.V.AlgebraTools.dual_lattice_denom Y hY x
      obtain ⟨s, hs⟩ := UpperTheory.V.AlgebraTools.dual_lattice_pow a ha
      refine ⟨s, (Submodule.smul_mono_left hs).trans ?_⟩
      refine Submodule.smul_le.mpr fun r hr y hy => ?_
      obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hr
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
      rw [mul_smul, smul_comm a c]
      exact Y.smul_mem _ (Y.smul_mem _ hax)
    | sup M N _ _ hM hN =>
      obtain ⟨s, hs⟩ := hM
      obtain ⟨t, ht⟩ := hN
      refine ⟨s + t, ?_⟩
      rw [Submodule.smul_sup]
      refine sup_le ?_ ?_
      · exact (Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_add_right s t))).trans hs
      · exact (Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_add_left t s))).trans ht
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaOverLift
open IsLocalRing

private theorem exists_field_lift {R S F K L : Type} [CommRing R] [CommRing S] [Algebra R S]
    [Field F] [Field K] [Field L] (c : F →+* K) (d : F →+* L) (a : R →+* F) (b : S →+* K)
    (hab : b.comp (algebraMap R S) = c.comp a)
    {ι : Type} (u : ι → S) (f : ι → Polynomial R) (hu : Algebra.adjoin R (Set.range u) = ⊤)
    (hf : ∀ i, (f i).Monic ∧ Polynomial.aeval (u i) (f i) = 0 ∧
      ((f i).map (d.comp a)).Splits) :
    ∃ ψ : S →+* L, ψ.comp (algebraMap R S) = d.comp a ∧
      RingHom.ker ψ = RingHom.ker b := by
  letI : Algebra F K := c.toAlgebra
  letI : Algebra F L := d.toAlgebra
  change b.comp (algebraMap R S) = (algebraMap F K).comp a at hab
  have hab' : ∀ r, b (algebraMap R S r) = algebraMap F K (a r) := fun r => RingHom.congr_fun hab r
  have hT : ∀ s ∈ Set.range (fun i => b (u i)),
      IsIntegral F s ∧ ((minpoly F s).map (algebraMap F L)).Splits := by
    rintro _ ⟨i, rfl⟩
    obtain ⟨h1, h2, h3⟩ := hf i
    have h4 : Polynomial.aeval (b (u i)) ((f i).map a) = 0 := by
      rw [Polynomial.aeval_def, Polynomial.eval₂_map, ← hab, ← Polynomial.hom_eval₂,
        ← Polynomial.aeval_def, h2, map_zero]
    refine ⟨⟨_, h1.map a, h4⟩, ?_⟩
    rw [← Polynomial.map_map] at h3
    exact h3.of_dvd ((h1.map a).map _).ne_zero (Polynomial.map_dvd _ (minpoly.dvd F _ h4))
  obtain ⟨φ⟩ := IntermediateField.nonempty_algHom_adjoin_of_splits hT
  have hmem : ∀ s : S, b s ∈ IntermediateField.adjoin F (Set.range (fun i => b (u i))) := by
    intro s
    have hs : s ∈ Algebra.adjoin R (Set.range u) := hu ▸ Algebra.mem_top
    induction hs using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩
    | algebraMap r => rw [hab']; exact IntermediateField.algebraMap_mem _ _
    | add y z _ _ hy hz => rw [map_add b]; exact add_mem hy hz
    | mul y z _ _ hy hz => rw [map_mul]; exact mul_mem hy hz
  let b' : S →+* IntermediateField.adjoin F (Set.range (fun i => b (u i))) :=
    b.codRestrict _ hmem
  refine ⟨φ.toRingHom.comp b', ?_, ?_⟩
  · ext r
    have : b' (algebraMap R S r) = algebraMap F _ (a r) := Subtype.ext (hab' r)
    change φ (b' (algebraMap R S r)) = algebraMap F L (a r)
    rw [this, AlgHom.commutes]
  · ext s
    rw [RingHom.mem_ker, RingHom.mem_ker]
    change φ (b' s) = 0 ↔ _
    rw [map_eq_zero_iff φ φ.toRingHom.injective]
    exact Subtype.ext_iff

theorem UpperTheory.V.AlgebraTools.exists_lift_ker_eq :
    ∀ (R S A : Type) [CommRing R] [CommRing S] [CommRing A] [IsDomain A] [Algebra R S] (x : R →+* A)
      (ι : Type) (u : ι → S) (f : ι → Polynomial R), Algebra.adjoin R (Set.range u) = ⊤ →
      (∀ i, (f i).Monic ∧ Polynomial.aeval (u i) (f i) = 0 ∧ ((f i).map x).Splits) →
      ∀ P : Ideal S, P.IsPrime → P.comap (algebraMap R S) = RingHom.ker x →
      ∃ x' : S →+* A, x'.comp (algebraMap R S) = x ∧ RingHom.ker x' = P := by
  intro R S A _ _ _ _ _ x ι u f hu hf P hP hPx
  haveI : (RingHom.ker x).IsPrime := RingHom.ker_isPrime x
  let j : A →+* FractionRing A := algebraMap A (FractionRing A)
  have hj : Function.Injective j := IsFractionRing.injective A (FractionRing A)
  let b : S →+* FractionRing (S ⧸ P) :=
    (algebraMap (S ⧸ P) (FractionRing (S ⧸ P))).comp (Ideal.Quotient.mk P)
  have hb : RingHom.ker b = P := by
    ext s
    rw [RingHom.mem_ker]
    change algebraMap (S ⧸ P) (FractionRing (S ⧸ P)) (Ideal.Quotient.mk P s) = 0 ↔ _
    rw [map_eq_zero_iff _ (IsFractionRing.injective (S ⧸ P) (FractionRing (S ⧸ P))),
      Ideal.Quotient.eq_zero_iff_mem]
  have hkb : RingHom.ker (b.comp (algebraMap R S)) = RingHom.ker x := by
    rw [← RingHom.comap_ker, hb, hPx]
  have hkj : RingHom.ker (j.comp x) = RingHom.ker x := by
    rw [← RingHom.comap_ker, (RingHom.injective_iff_ker_eq_bot j).1 hj]
    rfl
  let g₁ : R ⧸ RingHom.ker x →+* FractionRing (S ⧸ P) :=
    Ideal.Quotient.lift _ (b.comp (algebraMap R S)) (fun r hr => by
      rw [← hkb] at hr; exact hr)
  let g₂ : R ⧸ RingHom.ker x →+* FractionRing A :=
    Ideal.Quotient.lift _ (j.comp x) (fun r hr => by rw [← hkj] at hr; exact hr)
  have hg₁ : Function.Injective g₁ := RingHom.lift_injective_of_ker_le_ideal _ _ hkb.le
  have hg₂ : Function.Injective g₂ := RingHom.lift_injective_of_ker_le_ideal _ _ hkj.le
  let F := FractionRing (R ⧸ RingHom.ker x)
  let a : R →+* F := (algebraMap (R ⧸ RingHom.ker x) F).comp (Ideal.Quotient.mk _)
  obtain ⟨c, h1⟩ : ∃ c : F →+* FractionRing (S ⧸ P), b.comp (algebraMap R S) = c.comp a :=
    ⟨IsFractionRing.lift hg₁, RingHom.ext fun r =>
      ((IsFractionRing.lift_algebraMap (K := F) hg₁ (Ideal.Quotient.mk _ r)).trans
        (Ideal.Quotient.lift_mk _ _ _)).symm⟩
  obtain ⟨d, h2⟩ : ∃ d : F →+* FractionRing A, d.comp a = j.comp x :=
    ⟨IsFractionRing.lift hg₂, RingHom.ext fun r =>
      ((IsFractionRing.lift_algebraMap (K := F) hg₂ (Ideal.Quotient.mk _ r)).trans
        (Ideal.Quotient.lift_mk _ _ _))⟩
  obtain ⟨ψ, hψ1, hψ2⟩ := exists_field_lift c d a b h1 u f hu (fun i =>
    ⟨(hf i).1, (hf i).2.1, by rw [h2, ← Polynomial.map_map]; exact (hf i).2.2.map j⟩)
  rw [h2] at hψ1
  rw [hb] at hψ2
  have hmem : ∀ s : S, ψ s ∈ j.range := by
    intro s
    have hs : s ∈ Algebra.adjoin R (Set.range u) := hu ▸ Algebra.mem_top
    induction hs using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      obtain ⟨hm, h0, hsp⟩ := hf i
      have h4 : Polynomial.eval₂ j (ψ (u i)) ((f i).map x) = 0 := by
        rw [Polynomial.eval₂_map, ← hψ1, ← Polynomial.hom_eval₂,
          ← Polynomial.aeval_def, h0, map_zero]
      rw [hsp.eq_prod_roots_of_monic (hm.map x), Polynomial.eval₂_multiset_prod,
        Multiset.prod_eq_zero_iff, Multiset.map_map, Multiset.mem_map] at h4
      obtain ⟨c, -, hc⟩ := h4
      refine ⟨c, ?_⟩
      simp only [Function.comp_apply, Polynomial.eval₂_sub, Polynomial.eval₂_X,
        Polynomial.eval₂_C] at hc
      exact (sub_eq_zero.1 hc).symm
    | algebraMap r => exact ⟨x r, (RingHom.congr_fun hψ1 r).symm⟩
    | add y z _ _ hy hz => rw [map_add ψ]; exact add_mem hy hz
    | mul y z _ _ hy hz => rw [map_mul]; exact mul_mem hy hz
  choose g hg using hmem
  let x' : S →+* A :=
    { toFun := g
      map_one' := hj (by rw [hg, map_one, map_one])
      map_mul' := fun s t => hj (by rw [map_mul, hg, hg, hg, map_mul])
      map_zero' := hj (by rw [hg, map_zero, map_zero])
      map_add' := fun s t => hj (by rw [map_add (f := _), hg, hg, hg, map_add (f := _)]) }
  refine ⟨x', ?_, ?_⟩
  · ext r
    exact hj ((hg _).trans (RingHom.congr_fun hψ1 r))
  · ext s
    rw [← hψ2, RingHom.mem_ker, RingHom.mem_ker, ← hg, map_eq_zero_iff j hj]
    rfl
end
