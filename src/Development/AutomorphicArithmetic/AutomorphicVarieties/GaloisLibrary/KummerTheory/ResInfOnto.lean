module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.CardHomQZ
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.ShaInfl
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.NonemptyH0GlobalEquivGaloisImage

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ExtCocycle
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.VanishCyc
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem exists_level_pow_dvd_of_not_finOrder (l : ℕ) [hl : Fact l.Prime] (u : ℤ_[l]ˣ) (hu : ¬ IsOfFinOrder u) (a : ℕ) :
    ∃ j : ℕ, ∀ m : ℤ, PadicInt.toZModPow j ((u ^ m : ℤ_[l]ˣ) : ℤ_[l]) = 1 → (l : ℤ) ^ (a + 1) ∣ m := by
  by_contra h
  push_neg at h
  apply hu
  have hK : 0 < l ^ a * (l - 1) :=
    Nat.mul_pos (pow_pos hl.out.pos a) (Nat.sub_pos_of_lt hl.out.one_lt)
  refine isOfFinOrder_iff_pow_eq_one.mpr ⟨l ^ a * (l - 1), hK, ?_⟩
  apply Units.ext
  apply PadicInt.ext_of_toZModPow.mp
  intro j
  obtain ⟨m, hm, hnd⟩ := h j
  obtain ⟨w, hwdef⟩ : ∃ w : (ZMod (l ^ j))ˣ, w = Units.map (PadicInt.toZModPow j).toMonoidHom u :=
    ⟨_, rfl⟩
  have hw : ∀ n : ℤ, ((w ^ n : (ZMod (l ^ j))ˣ) : ZMod (l ^ j)) =
      PadicInt.toZModPow j ((u ^ n : ℤ_[l]ˣ) : ℤ_[l]) := by
    intro n
    rw [hwdef, ← map_zpow]
    rfl
  have hwm : w ^ m = 1 := by
    apply Units.ext
    rw [hw, hm, Units.val_one]
  have hom : (orderOf w : ℤ) ∣ m := orderOf_dvd_iff_zpow_eq_one.mpr hwm
  haveI : NeZero (l ^ j) := ⟨pow_ne_zero _ hl.out.ne_zero⟩
  have hcard : orderOf w ∣ (l ^ j).totient := by
    rw [← ZMod.card_units_eq_totient]
    exact orderOf_dvd_card
  have hdiv : orderOf w ∣ l ^ a * (l - 1) := by
    rcases j with _ | i
    · simp only [pow_zero, Nat.totient_one, Nat.dvd_one] at hcard
      rw [hcard]
      exact one_dvd _
    · rw [Nat.totient_prime_pow_succ hl.out] at hcard
      rw [← Nat.dvd_gcd_mul_iff_dvd_mul] at hcard
      obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow hl.out).mp (Nat.gcd_dvd_right (orderOf w) (l ^ i))
      have hba : b ≤ a := by
        by_contra hba
        push_neg at hba
        apply hnd
        have h1 : (l : ℤ) ^ b ∣ m := by
          have : l ^ b ∣ orderOf w := hb ▸ Nat.gcd_dvd_left _ _
          exact dvd_trans (by exact_mod_cast this) hom
        exact dvd_trans (pow_dvd_pow _ hba) h1
      rw [hb] at hcard
      exact hcard.trans (Nat.mul_dvd_mul_right (pow_dvd_pow l hba) _)
  have hwK : w ^ (l ^ a * (l - 1)) = 1 := orderOf_dvd_iff_pow_eq_one.mp hdiv
  have := hw ((l ^ a * (l - 1) : ℕ) : ℤ)
  rw [zpow_natCast, zpow_natCast, hwK, Units.val_one] at this
  rw [← this, Units.val_one, map_one]

private theorem exists_open_subgroup_cycZ_trivial_mod_pow (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (l : ℕ) [hl : Fact l.Prime] (j : ℕ) :
    ∃ H : Subgroup (G F Ω), IsOpen (H : Set (G F Ω)) ∧
      ∀ g ∈ H, PadicInt.toZModPow j ((cycZ F Ω l g : ℤ_[l]ˣ) : ℤ_[l]) = 1 := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : NeZero (l : Ω) := ⟨Nat.cast_ne_zero.mpr hl.out.ne_zero⟩
  haveI : NeZero (l ^ j) := ⟨pow_ne_zero _ hl.out.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ j)
  haveI : FiniteDimensional F (IntermediateField.adjoin F ({ζ} : Set Ω)) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral ζ)
  refine ⟨(IntermediateField.adjoin F ({ζ} : Set Ω)).fixingSubgroup,
    IntermediateField.fixingSubgroup_isOpen _, fun g hg => ?_⟩
  have hgζ : g ζ = ζ :=
    (IntermediateField.mem_fixingSubgroup_iff _ _).mp hg ζ (IntermediateField.mem_adjoin_simple_self F ζ)
  have hspec := cyclotomicCharacter.spec l (n := j) (MulSemiringAction.toRingAut (G F Ω) Ω g) ζ hζ.pow_eq_one
  change PadicInt.toZModPow j ((cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G F Ω) Ω g) : ℤ_[l]ˣ) : ℤ_[l]) = 1
  generalize PadicInt.toZModPow j ((cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G F Ω) Ω g) : ℤ_[l]ˣ) : ℤ_[l]) = z at hspec ⊢
  have h1 : ζ ^ 1 = ζ ^ z.val := by
    rw [pow_one, ← hspec]
    exact hgζ.symm
  have hu := hζ.isUnit_unit (NeZero.ne (l ^ j))
  have h1' : (hζ.isUnit (NeZero.ne (l ^ j))).unit ^ 1 = (hζ.isUnit (NeZero.ne (l ^ j))).unit ^ z.val := by
    apply Units.ext
    simpa using h1
  rw [pow_eq_pow_iff_modEq, ← hu.eq_orderOf] at h1'
  have h2 := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h1'.symm
  rw [ZMod.natCast_val, ZMod.cast_id', id, Nat.cast_one] at h2
  exact h2

theorem UpperTheory.V.Kum.vanishCyc :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] (φ : Uinf F Ω l → M) (γ : G F Ω), IsLocallyConstant φ → (∀ a b, φ (a * b) = φ a + φ b) → (∀ m : M, ∃ k : ℕ, l ^ k • m = 0) → ¬ IsOfFinOrder (cycZ F Ω l γ) →
    ∀ x : Uinf F Ω l, x.1 ∈ (Subgroup.zpowers γ).topologicalClosure → φ x = 0 := by
  intro F Ω _ _ _ _ _ l hl M _ φ γ hφ hmul htor hγ x hx
  have h1 : φ 1 = 0 := by simpa using hmul 1 1
  have hpow : ∀ y : Uinf F Ω l, ∀ n : ℕ, φ (y ^ n) = n • φ y := by
    intro y n
    induction n with
    | zero => simpa using h1
    | succ n ih => rw [pow_succ, hmul, ih, succ_nsmul]
  obtain ⟨W, hWo, hWeq⟩ := isOpen_induced_iff.mp (hφ.isOpen_fiber 0)
  have hW1 : (1 : G F Ω) ∈ W := by
    have : (1 : Uinf F Ω l) ∈ Subtype.val ⁻¹' W := by
      rw [hWeq]
      exact h1
    exact this
  obtain ⟨E, hE, hEW⟩ := (krullTopology_mem_nhds_one_iff F Ω W).mp (hWo.mem_nhds hW1)
  haveI := hE
  have hN : IsOpen (E.fixingSubgroup : Set (G F Ω)) := IntermediateField.fixingSubgroup_isOpen E
  have hNφ : ∀ y : Uinf F Ω l, y.1 ∈ E.fixingSubgroup → φ y = 0 := by
    intro y hy
    have : y ∈ Subtype.val ⁻¹' W := hEW hy
    rw [hWeq] at this
    exact this
  haveI : Finite (G F Ω ⧸ E.fixingSubgroup) := Subgroup.quotient_finite_of_isOpen _ hN
  obtain ⟨d, hd0, -, hdN⟩ := Subgroup.exists_pow_mem_of_index_ne_zero (Subgroup.index_ne_zero_of_finite (H := E.fixingSubgroup)) γ
  obtain ⟨a, d', hd'l, hdd⟩ := Nat.exists_eq_pow_mul_and_not_dvd hd0.ne' l hl.out.ne_one
  obtain ⟨j, hj⟩ := exists_level_pow_dvd_of_not_finOrder l (cycZ F Ω l γ) hγ a
  obtain ⟨H, hHo, hH⟩ := exists_open_subgroup_cycZ_trivial_mod_pow F Ω l j
  have ho : IsOpen ((fun g => x.1⁻¹ * g) ⁻¹' ((E.fixingSubgroup : Set (G F Ω)) ∩ (H : Set (G F Ω)))) :=
    (hN.inter hHo).preimage (continuous_const.mul continuous_id)
  have hxo : x.1 ∈ (fun g => x.1⁻¹ * g) ⁻¹' ((E.fixingSubgroup : Set (G F Ω)) ∩ (H : Set (G F Ω))) := by
    simp only [Set.mem_preimage, inv_mul_cancel, Set.mem_inter_iff, SetLike.mem_coe]
    exact ⟨one_mem _, one_mem _⟩
  have hx' : x.1 ∈ closure ((Subgroup.zpowers γ : Subgroup (G F Ω)) : Set (G F Ω)) := by
    rw [← Subgroup.topologicalClosure_coe]
    exact hx
  obtain ⟨g, hgo, hgz⟩ := mem_closure_iff.mp hx' _ ho hxo
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hgz
  obtain ⟨hνN, hνH⟩ := hgo
  have hcx : cycZ F Ω l x.1 = 1 := (Subgroup.mem_inf.mp x.2).2
  have hcyc : PadicInt.toZModPow j ((cycZ F Ω l γ ^ m : ℤ_[l]ˣ) : ℤ_[l]) = 1 := by
    have := hH _ hνH
    rwa [map_mul, map_inv, hcx, inv_one, one_mul, map_zpow] at this
  have hma : (l : ℤ) ^ a ∣ m := (pow_dvd_pow _ (Nat.le_succ a)).trans (hj m hcyc)
  have hcl : closure ((Subgroup.zpowers γ : Subgroup (G F Ω)) : Set (G F Ω)) ⊆ {y | y * γ = γ * y} := by
    apply closure_minimal
    · intro y hy
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact (Commute.self_zpow γ i).symm.eq
    · exact isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)
  have hxγ : Commute x.1 γ := hcl hx'
  have hxν : Commute x.1 (x.1⁻¹ * γ ^ m) := (Commute.refl x.1).inv_right.mul_right (hxγ.zpow_right m)
  have hexp : (γ ^ m) ^ d' = x.1 ^ d' * (x.1⁻¹ * γ ^ m) ^ d' := by
    rw [← hxν.mul_pow, mul_inv_cancel_left]
  have hγN : (γ ^ m) ^ d' ∈ E.fixingSubgroup := by
    obtain ⟨t, ht⟩ := hma
    have : (γ ^ m) ^ d' = (γ ^ d) ^ t := by
      rw [← zpow_natCast, ← zpow_mul, ← zpow_natCast, ← zpow_mul, ht, hdd]
      congr 1
      push_cast
      ring
    rw [this]
    exact zpow_mem hdN t
  have hxN : (x ^ d').1 ∈ E.fixingSubgroup := by
    have : (x ^ d').1 = (γ ^ m) ^ d' * ((x.1⁻¹ * γ ^ m) ^ d')⁻¹ := by
      rw [hexp, mul_inv_cancel_right]
      rfl
    rw [this]
    exact mul_mem hγN (inv_mem (pow_mem hνN d'))
  have h0 : d' • φ x = 0 := by
    rw [← hpow]
    exact hNφ _ hxN
  obtain ⟨k, hk⟩ := htor (φ x)
  have ho1 : addOrderOf (φ x) ∣ d' := addOrderOf_dvd_of_nsmul_eq_zero h0
  have ho2 : addOrderOf (φ x) ∣ l ^ k := addOrderOf_dvd_of_nsmul_eq_zero hk
  have hcop : Nat.Coprime d' (l ^ k) :=
    Nat.Coprime.pow_right _ (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hl.out).mpr hd'l))
  exact AddMonoid.addOrderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_one (by rw [← hcop.gcd_eq_one]; exact Nat.dvd_gcd ho1 ho2))
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem ext_of_prod {Γ R M : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    [T2Space Γ] [CommRing R] [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
    (ρ : Representation R Γ M) (C U : Subgroup Γ) [hN : U.Normal] (hC : IsClosed (C : Set Γ))
    (hU : IsClosed (U : Set Γ)) (hCU : ∀ g : Γ, ∃ p : C × U, p.1.1 * p.2.1 = g) (φ : U → M) (hρ : ContAction ρ)
    (htr : ∀ u ∈ U, ∀ m, ρ u m = m) (hφ : Continuous φ) (hadd : ∀ a b, φ (a * b) = φ a + φ b)
    (heq : ∀ (g : Γ) (u u' : U), u'.1 * g = g * u.1 → φ u' = ρ g (φ u)) (hv : ∀ x : U, x.1 ∈ C → φ x = 0) :
    ∃ z ∈ Z1 ρ, ∀ u : U, z u.1 = φ u := by
  classical
  obtain ⟨f, hf⟩ : ∃ f : C × U → Γ, ∀ p, f p = p.1.1 * p.2.1 := ⟨_, fun _ => rfl⟩
  have hwd : ∀ p q : C × U, f p = f q → ρ p.1.1 (φ p.2) = ρ q.1.1 (φ q.2) := by
    rintro ⟨⟨c, hc⟩, ⟨u, hu⟩⟩ ⟨⟨c', hc'⟩, ⟨u', hu'⟩⟩ h
    rw [hf, hf] at h
    change c * u = c' * u' at h
    change ρ c (φ ⟨u, hu⟩) = ρ c' (φ ⟨u', hu'⟩)
    have hw1 : c'⁻¹ * c = u' * u⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h, mul_inv_cancel_right]
    have hwC : c'⁻¹ * c ∈ C := C.mul_mem (C.inv_mem hc') hc
    have hwU : c'⁻¹ * c ∈ U := hw1 ▸ U.mul_mem hu' (U.inv_mem hu)
    have hφw : φ ⟨_, hwU⟩ = 0 := hv _ hwC
    have hu'eq : (⟨u', hu'⟩ : U) = ⟨_, hwU⟩ * ⟨u, hu⟩ := by
      ext
      simp [hw1]
    have h2 : φ ⟨u', hu'⟩ = φ ⟨u, hu⟩ := by rw [hu'eq, hadd, hφw, zero_add]
    rw [h2, show ρ c = ρ c' * ρ (c'⁻¹ * c) by rw [← map_mul, mul_inv_cancel_left],
      Module.End.mul_apply, htr _ hwU]
  choose s hs using hCU
  obtain ⟨z, hz⟩ : ∃ z : Γ → M, ∀ g, z g = ρ (s g).1.1 (φ (s g).2) := ⟨_, fun _ => rfl⟩
  have hzf : ∀ p : C × U, z (f p) = ρ p.1.1 (φ p.2) := by
    intro p
    rw [hz]
    exact hwd _ _ (by rw [hf, hs])
  haveI : CompactSpace C := isCompact_iff_compactSpace.mp hC.isCompact
  haveI : CompactSpace U := isCompact_iff_compactSpace.mp hU.isCompact
  have hfc : Continuous f := by
    have : f = fun p : C × U => p.1.1 * p.2.1 := funext hf
    rw [this]
    exact (continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  have hfs : Function.Surjective f := fun g => ⟨s g, by rw [hf, hs]⟩
  have hq : Topology.IsQuotientMap f := hfc.isClosedMap.isQuotientMap hfc hfs
  have hzc : Continuous z := by
    rw [hq.continuous_iff]
    have : z ∘ f = fun p : C × U => ρ p.1.1 (φ p.2) := funext hzf
    rw [this]
    exact hρ.comp ((continuous_subtype_val.comp continuous_fst).prodMk (hφ.comp continuous_snd))
  have hzU : ∀ u : U, z u.1 = φ u := by
    intro u
    have h1 := hzf (⟨1, C.one_mem⟩, u)
    rw [hf] at h1
    simpa using h1
  have hcoc : ∀ g h : Γ, z (g * h) = z g + ρ g (z h) := by
    intro g h
    obtain ⟨⟨⟨c, hc⟩, ⟨u, hu⟩⟩, rfl⟩ := hfs g
    obtain ⟨⟨⟨d, hd⟩, ⟨v, hv'⟩⟩, rfl⟩ := hfs h
    have hu0 : d⁻¹ * u * d ∈ U := by simpa using hN.conj_mem u hu d⁻¹
    have hprod : f (⟨c, hc⟩, ⟨u, hu⟩) * f (⟨d, hd⟩, ⟨v, hv'⟩)
        = f (⟨c * d, C.mul_mem hc hd⟩, ⟨d⁻¹ * u * d, hu0⟩ * ⟨v, hv'⟩) := by
      simp only [hf, Subgroup.coe_mul]
      group
    rw [hprod, hzf, hzf, hzf, hf]
    change ρ (c * d) (φ (⟨d⁻¹ * u * d, hu0⟩ * ⟨v, hv'⟩)) = ρ c (φ ⟨u, hu⟩) + ρ (c * u) (ρ d (φ ⟨v, hv'⟩))
    have hconj : φ ⟨u, hu⟩ = ρ d (φ ⟨d⁻¹ * u * d, hu0⟩) :=
      heq d ⟨d⁻¹ * u * d, hu0⟩ ⟨u, hu⟩ (by show u * d = d * (d⁻¹ * u * d); group)
    rw [hadd, map_add (f := _), hconj]
    simp only [map_mul, Module.End.mul_apply]
    rw [htr u hu]
  exact ⟨z, ⟨hzc, hcoc⟩, hzU⟩

theorem UpperTheory.V.Kum.extCocycle :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R (G F Ω) M) (φ : Uinf F Ω l → M), Procyc F Ω l → ContAction ρ → (∀ u ∈ Uinf F Ω l, ∀ m, ρ u m = m) → (∀ m : M, ∃ k : ℕ, l ^ k • m = 0) →
    IsLocallyConstant φ → (∀ a b, φ (a * b) = φ a + φ b) → (∀ g : G F Ω, φ ∈ conjCond (Uinf F Ω l) g.toRingEquiv (ρ g)) → ∃ z ∈ Z1 ρ, ∀ u : Uinf F Ω l, z u.1 = φ u := by
  intro F Ω _ _ _ _ _ l _ R M _ _ _ _ _ ρ φ hP hρ htr htors hloc hadd hconj
  classical
  have hVc : IsClosed ((cycZ F Ω l).range : Set ℤ_[l]ˣ) := by
    rw [MonoidHom.coe_range]
    exact (isCompact_range (continuous_cycZ F Ω l)).isClosed
  have hcond : l ≠ 2 ∨ (cycZ F Ω l).range ≤ KStar.TotallyRealRoots.princ l 2 := by
    rcases hP with h | h
    · exact Or.inl h
    · right
      rintro _ ⟨g, rfl⟩
      exact MonoidHom.mem_ker.mpr (h g)
  obtain ⟨γ0, hγ0, hgen⟩ := existsGen l _ hVc hcond
  obtain ⟨γ, rfl⟩ := hγ0
  have hnf : ¬ IsOfFinOrder (cycZ F Ω l γ) := by
    intro hfin
    obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp hfin
    have hS : ∀ u ∈ (cycZ F Ω l).range, u ^ n = 1 := by
      intro u hu
      have hsub : closure ((Subgroup.zpowers (cycZ F Ω l γ) : Subgroup ℤ_[l]ˣ) : Set ℤ_[l]ˣ)
          ⊆ {x | x ^ n = 1} := by
        apply closure_minimal
        · intro x hx
          obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
          show ((cycZ F Ω l γ) ^ k) ^ n = 1
          rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hpow, one_zpow]
        · exact isClosed_eq (continuous_pow n) continuous_const
      have h1 := hgen hu
      rw [← SetLike.mem_coe, Subgroup.topologicalClosure_coe] at h1
      exact hsub h1
    have htop : KStar.TotallyRealRoots.nu l (KStar.TotallyRealRoots.galImage l F) n = ⊤ := by
      rw [ENat.eq_top_iff_forall_ge]
      intro k
      rw [KStar.TotallyRealRoots.le_nu_iff_pow_mem_princ]
      intro u hu
      rw [KStar.TotallyRealRoots.mem_galImage_iff_of_equiv (RingEquiv.refl F) Ω] at hu
      obtain ⟨g, rfl⟩ := hu
      have h2 := hS (cyclotomicCharacter Ω l g.toRingEquiv) (MonoidHom.mem_range.mpr ⟨g, rfl⟩)
      rw [h2]
      exact Subgroup.one_mem _
    exact KStar.TotallyRealRoots.nu_ne_top KStar.TotallyRealRoots.isOpen_galImage hn.ne' htop
  haveI hN : (Uinf F Ω l).Normal := by
    show (⊤ ⊓ (cycZ F Ω l).ker).Normal
    infer_instance
  have hUc : IsClosed ((Uinf F Ω l : Subgroup (G F Ω)) : Set (G F Ω)) := by
    show IsClosed ((⊤ ⊓ (cycZ F Ω l).ker : Subgroup (G F Ω)) : Set (G F Ω))
    rw [Subgroup.coe_inf, Subgroup.coe_top, Set.univ_inter, MonoidHom.coe_ker]
    exact isClosed_singleton.preimage (continuous_cycZ F Ω l)
  have hCc := Subgroup.isClosed_topologicalClosure (Subgroup.zpowers γ)
  have hmemU : ∀ x : G F Ω, cycZ F Ω l x = 1 → x ∈ Uinf F Ω l := by
    intro x hx
    show x ∈ (⊤ ⊓ (cycZ F Ω l).ker : Subgroup (G F Ω))
    exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_top x, MonoidHom.mem_ker.mpr hx⟩
  have hCU : ∀ g : G F Ω, ∃ p : (Subgroup.zpowers γ).topologicalClosure × Uinf F Ω l,
      p.1.1 * p.2.1 = g := by
    intro g
    have himg : closure ((Subgroup.zpowers (cycZ F Ω l γ) : Subgroup ℤ_[l]ˣ) : Set ℤ_[l]ˣ)
        ⊆ (cycZ F Ω l) '' ((Subgroup.zpowers γ).topologicalClosure : Set (G F Ω)) := by
      apply closure_minimal
      · intro x hx
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
        exact ⟨γ ^ k, Subgroup.le_topologicalClosure _ (Subgroup.zpow_mem_zpowers γ k), map_zpow _ _ _⟩
      · exact (hCc.isCompact.image (continuous_cycZ F Ω l)).isClosed
    have hg := hgen (MonoidHom.mem_range.mpr ⟨g, rfl⟩)
    rw [← SetLike.mem_coe, Subgroup.topologicalClosure_coe] at hg
    obtain ⟨c, hc, hcg⟩ := himg hg
    refine ⟨(⟨c, hc⟩, ⟨c⁻¹ * g, hmemU _ ?_⟩), mul_inv_cancel_left c g⟩
    rw [map_mul, map_inv, hcg, inv_mul_cancel]
  have heq : ∀ (g : G F Ω) (u u' : Uinf F Ω l), u'.1 * g = g * u.1 → φ u' = ρ g (φ u) := by
    intro g u u' h
    apply hconj g u u'
    intro x
    have h3 := congrArg (fun e : G F Ω => e x) h
    simpa [AlgEquiv.mul_apply] using h3
  have hv : ∀ x : Uinf F Ω l, x.1 ∈ (Subgroup.zpowers γ).topologicalClosure → φ x = 0 :=
    fun x hx => vanishCyc F Ω l M φ γ hloc hadd htors hnf x hx
  exact ext_of_prod ρ _ _ hCc hUc hCU φ hρ htr hloc.continuous hadd heq hv
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem UpperTheory.V.Kum.decCob {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {l : ℕ} [Fact l.Prime] {e : ℤ} (he : e ≠ 0) (hP : Procyc F Ω l) {v : HeightOneSpectrum (𝓞 F)}
    {A : ValuationSubring Ω} (hv : v ∈ Above F l) (hA : IsPlaceOver A v) {z : G F Ω → QZ l}
    (hz : z ∈ Z1 (qzG F Ω l e)) (h0 : ∀ g ∈ Dec (F := F) A, cycZ F Ω l g = 1 → z g = 0) :
    ∃ m, ∀ g ∈ Dec (F := F) A, z g = qzG F Ω l e g m - m := by
  haveI : CompactSpace (Dec (F := F) A) := isCompact_iff_compactSpace.mp (isClosed_Dec A).isCompact
  let χ : Dec (F := F) A →* ℤ_[l]ˣ := (cycZ F Ω l).comp (Dec (F := F) A).subtype
  let ρ : Representation ℤ_[l] (Dec (F := F) A) (QZ l) := (qzG F Ω l e).comp (Dec (F := F) A).subtype
  have hV : IsClosed (decImage F l A : Set ℤ_[l]ˣ) := Subgroup.isClosed_of_isOpen _ (isOpen_decImage hv hA)
  have hVp : l ≠ 2 ∨ decImage F l A ≤ KStar.TotallyRealRoots.princ l 2 := by
    rcases hP with h | h
    · exact Or.inl h
    · right
      rintro _ ⟨g, -, rfl⟩
      have h1 := h g
      simp only [cycR, MonoidHom.comp_apply, Units.ext_iff, Units.coe_map, Units.val_one] at h1
      rw [KStar.TotallyRealRoots.mem_princ]
      have h2 : PadicInt.toZModPow 2 ((cycZ F Ω l g : ℤ_[l]) - 1) = 0 := by
        rw [map_sub, map_one]
        simpa using sub_eq_zero.mpr h1
      rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at h2
      exact_mod_cast h2
  obtain ⟨γ', hγ'V, hgen'⟩ := existsGen l (decImage F l A) hV hVp
  obtain ⟨γ, hγ, hγχ⟩ := Subgroup.mem_map.mp hγ'V
  have hq : Continuous fun p : G F Ω × QZ l => qzG F Ω l e p.1 p.2 := contAction_qzG e
  have hpm : Continuous fun p : Dec (F := F) A × QZ l => ((p.1 : G F Ω), p.2) :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have hρc0 := hq.comp hpm
  have hρc : ReciprocityTheory.Gal.ContAction ρ := by
    unfold ReciprocityTheory.Gal.ContAction
    refine hρc0.congr fun p => ?_
    simp only [ρ, Function.comp_apply, MonoidHom.comp_apply, Subgroup.coe_subtype]
  have hχc0 := (continuous_cycZ F Ω l).comp (continuous_subtype_val (p := fun g : G F Ω => g ∈ Dec (F := F) A))
  have hχc : Continuous χ := by
    refine hχc0.congr fun g => ?_
    simp only [χ, Function.comp_apply, MonoidHom.comp_apply, Subgroup.coe_subtype]
  have htriv : ∀ g, χ g = 1 → ∀ m, ρ g m = m := by
    intro g hg m
    simp only [χ, MonoidHom.comp_apply, Subgroup.coe_subtype] at hg
    simp only [ρ, MonoidHom.comp_apply, Subgroup.coe_subtype, qzG_apply, hg, one_zpow, Units.val_one, one_smul]
  have hgen : ∀ g, χ g ∈ (Subgroup.zpowers (χ ⟨γ, hγ⟩)).topologicalClosure := by
    intro g
    have h1 : χ ⟨γ, hγ⟩ = γ' := by
      simp only [χ, MonoidHom.comp_apply, Subgroup.coe_subtype]
      exact hγχ
    rw [h1]
    apply hgen'
    simp only [χ, MonoidHom.comp_apply, Subgroup.coe_subtype]
    exact Subgroup.mem_map_of_mem _ g.2
  have hne : (cycZ F Ω l γ) ^ (-e) ≠ 1 := by
    intro h1
    obtain ⟨g, hg, hg1⟩ := GlobalTheory.CycDec.exists_mem_Dec_cycZ_zpow_ne_one F Ω l v A hv hA (-e) (neg_ne_zero.mpr he)
    let K : Subgroup ℤ_[l]ˣ := (zpowGroupHom (-e) : ℤ_[l]ˣ →* ℤ_[l]ˣ).ker
    have hK : IsClosed (K : Set ℤ_[l]ˣ) := by
      have : (K : Set ℤ_[l]ˣ) = {x : ℤ_[l]ˣ | x ^ (-e) = 1} := by
        ext x
        simp [K]
      rw [this]
      exact isClosed_eq (continuous_zpow (-e)) continuous_const
    have hzK : Subgroup.zpowers γ' ≤ K := by
      rw [Subgroup.zpowers_le, MonoidHom.mem_ker, zpowGroupHom_apply, ← hγχ]
      exact h1
    have hmem := Subgroup.topologicalClosure_minimal _ hzK hK (hgen' (Subgroup.mem_map_of_mem _ hg))
    rw [MonoidHom.mem_ker, zpowGroupHom_apply] at hmem
    exact hg1 hmem
  have hsurj : Function.Surjective fun m => ρ ⟨γ, hγ⟩ m - m := by
    intro y
    have hu : ((cycZ F Ω l γ ^ (-e) : ℤ_[l]ˣ) : ℤ_[l]) - 1 ≠ 0 := by
      intro h0'
      exact hne (Units.val_eq_one.mp (sub_eq_zero.mp h0'))
    obtain ⟨x, hx⟩ := (qzBasic l).1 _ hu y
    refine ⟨x, ?_⟩
    simp only [ρ, MonoidHom.comp_apply, Subgroup.coe_subtype, qzG_apply]
    rw [← hx]
    simp only [sub_smul, one_smul]
  have hzr : (fun g : Dec (F := F) A => z g) ∈ Z1 ρ := by
    refine ⟨hz.1.comp continuous_subtype_val, fun a b => ?_⟩
    have := hz.2 a b
    simp only [ρ, MonoidHom.comp_apply, Subgroup.coe_subtype, Subgroup.coe_mul]
    exact this
  have hB := cobOfGen l (Dec (F := F) A) χ ℤ_[l] (QZ l) ρ ⟨γ, hγ⟩ hχc hρc htriv hgen hsurj _ hzr
    (fun g hg => h0 g g.2 (by simpa [χ] using hg))
  obtain ⟨m, hm⟩ := (mem_coboundaries1 ρ _).mp hB
  refine ⟨m, fun g hg => ?_⟩
  have := hm ⟨g, hg⟩
  simpa [ρ] using this

theorem UpperTheory.V.Kum.resInfOnto :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (D : LData F Ω l) (e : ℤ), e ≠ 0 → Procyc F Ω l → (Sha D e).map (resInf D e) = EqHom l (Uinf F Ω l) (qzG F Ω l e) := by
  intro F Ω _ _ _ _ _ l _ D e he hP
  apply le_antisymm (resInfMem F Ω l D e)
  intro φ hφ
  have hX := (Submodule.mem_inf.mp hφ).1
  have hC := (Submodule.mem_iInf _).mp (Submodule.mem_inf.mp hφ).2
  have hlc : IsLocallyConstant φ := hX.1
  have hadd : ∀ a b, φ (a * b) = φ a + φ b := hX.2.1
  have hIne : ∀ (A : ValuationSubring Ω) (u : Uinf F Ω l), (u : G F Ω) ∈ Ine A → φ u = 0 := hX.2.2.1
  have hDec : ∀ (A : ValuationSubring Ω), A.valuation (l : Ω) < 1 →
      ∀ u : Uinf F Ω l, (u : G F Ω) ∈ Dec A → φ u = 0 := hX.2.2.2
  have hmemU : ∀ g : G F Ω, cycZ F Ω l g = 1 → g ∈ Uinf F Ω l := by
    intro g hg
    simp only [Uinf, cycU, Subgroup.mem_inf, MonoidHom.mem_ker]
    exact ⟨Subgroup.mem_top g, hg⟩
  have htriv : ∀ u ∈ Uinf F Ω l, ∀ m, qzG F Ω l e u m = m := by
    intro u hu m
    simp only [Uinf, cycU, Subgroup.mem_inf, MonoidHom.mem_ker] at hu
    rw [qzG_apply, hu.2, one_zpow, Units.val_one, one_smul]
  obtain ⟨z, hz, hzφ⟩ := extCocycle F Ω l ℤ_[l] (QZ l) (qzG F Ω l e) φ hP (contAction_qzG e) htriv
    (qzBasic l).2.1 hlc hadd hC
  have hρ' : ∀ g m, ((qzTw D e).comp (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 F))))) g m = qzG F Ω l e g m := by
    intro g m
    rw [qzTw_comp_toGS]
  have hz' : z ∈ Z1 ((qzTw D e).comp (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 F))))) := by
    rw [qzTw_comp_toGS]
    exact hz
  have hsha := shaInfl F Ω D.S D.A D.hA ℤ_[l] (QZ l) (qzTw D e) (contTw F Ω l D e).1
  have hmk : (Submodule.Quotient.mk ⟨z, hz'⟩ : H1 ((qzTw D e).comp (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 F)))))) ∈
      ShaAbs ((qzTw D e).comp (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 F))))) (D.S : Set (HeightOneSpectrum (𝓞 F))) := by
    rw [mk_mem_ShaAbs]
    refine ⟨fun v hv A hA => ?_, fun v hv A hA => ⟨0, fun g hg => ?_⟩⟩
    · rw [D.hS] at hv
      have hAl : A.valuation (l : Ω) < 1 := ((placeDict F Ω).2.2.2 A v l hA).mpr hv
      obtain ⟨m, hm⟩ := decCob he hP hv hA hz (fun g hg hg1 => by
        rw [show z g = φ ⟨g, hmemU g hg1⟩ from hzφ ⟨g, hmemU g hg1⟩]
        exact hDec A hAl ⟨g, hmemU g hg1⟩ hg)
      refine ⟨m, fun g hg => ?_⟩
      rw [hρ']
      exact hm g hg
    · have hgN : g ∈ NS Ω (D.S : Set (HeightOneSpectrum (𝓞 F))) :=
        Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure
          (Set.mem_biUnion (x := v) hv (Set.mem_biUnion (x := A) hA hg)))
      have hg1 : cycZ F Ω l g = 1 := by
        rw [← DFunLike.congr_fun D.hchi g, MonoidHom.comp_apply]
        have : toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 F))) g = 1 := (QuotientGroup.eq_one_iff g).mpr hgN
        rw [this, map_one]
      simp only [map_zero, sub_zero]
      show z g = 0
      rw [show z g = φ ⟨g, hmemU g hg1⟩ from hzφ ⟨g, hmemU g hg1⟩]
      exact hIne A ⟨g, hmemU g hg1⟩ hg
  rw [← hsha] at hmk
  obtain ⟨y, hy, hyz⟩ := Submodule.mem_map.mp hmk
  refine Submodule.mem_map.mpr ⟨y, hy, ?_⟩
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  change Submodule.Quotient.mk (restrictCocycles1 (qzTw D e) (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 F)))) _ w) =
    Submodule.Quotient.mk ⟨z, hz'⟩ at hyz
  rw [Submodule.Quotient.eq, Submodule.mem_comap, Submodule.coe_subtype, mem_coboundaries1] at hyz
  obtain ⟨m, hm⟩ := hyz
  funext u
  have h1 := hm u
  rw [hρ', htriv u u.2, sub_self, Submodule.coe_sub, Pi.sub_apply, sub_eq_zero] at h1
  rw [resInf_mk, ← hzφ u]
  exact h1
