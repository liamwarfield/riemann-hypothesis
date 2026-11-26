module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.CycRepApply
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.CardTors
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.FinChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ShaFrom

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.AmbIndex
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.AmbHom
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.HomCyc
open UpperTheory.V.FW

private theorem card_hom_surj (l : ℕ) {G A : Type} [Group G] [Group A] (π : G →* A) (hπ : Function.Surjective π)
    (P : G → Prop) (hP : ∀ u, P u ↔ π u = 1) :
    Nat.card {φ : G → ZMod l // (∀ a b, φ (a * b) = φ a + φ b) ∧ ∀ u, P u → φ u = 0} =
      Nat.card (A →* Multiplicative (ZMod l)) := by
  have key : ∀ (φ : G → ZMod l), (∀ a b, φ (a * b) = φ a + φ b) → (∀ u, P u → φ u = 0) →
      ∀ x y, π x = π y → φ x = φ y := by
    intro φ hadd hker x y hxy
    have h0 : φ (y⁻¹ * x) = 0 := hker _ ((hP _).mpr (by rw [map_mul, map_inv, hxy, inv_mul_cancel]))
    calc φ x = φ (y * (y⁻¹ * x)) := by rw [mul_inv_cancel_left]
      _ = φ y := by rw [hadd, h0, add_zero]
  symm
  apply Nat.card_congr
  refine Equiv.ofBijective (fun f => ⟨fun g => Multiplicative.toAdd (f (π g)), ?_, ?_⟩) ⟨?_, ?_⟩
  · intro a b
    simp [map_mul]
  · intro u hu
    show Multiplicative.toAdd (f (π u)) = 0
    rw [(hP u).mp hu, map_one, toAdd_one]
  · intro f f' h
    ext a
    obtain ⟨g, rfl⟩ := hπ a
    have := congrArg (fun φ => φ.1 g) h
    simpa using this
  · rintro ⟨φ, hadd, hker⟩
    refine ⟨{ toFun := fun a => Multiplicative.ofAdd (φ (Function.surjInv hπ a)), map_one' := ?_, map_mul' := ?_ }, ?_⟩
    · show Multiplicative.ofAdd (φ (Function.surjInv hπ 1)) = 1
      rw [key φ hadd hker _ 1 (by rw [Function.surjInv_eq hπ, map_one]), hker 1 ((hP 1).mpr (map_one π)), ofAdd_zero]
    · intro a b
      show Multiplicative.ofAdd (φ (Function.surjInv hπ (a * b))) =
        Multiplicative.ofAdd (φ (Function.surjInv hπ a)) * Multiplicative.ofAdd (φ (Function.surjInv hπ b))
      have e : φ (Function.surjInv hπ (a * b)) = φ (Function.surjInv hπ a * Function.surjInv hπ b) :=
        key φ hadd hker _ _ (by simp only [map_mul, Function.surjInv_eq hπ])
      rw [e, hadd, ofAdd_add]
    · apply Subtype.ext
      funext g
      show Multiplicative.toAdd (Multiplicative.ofAdd (φ (Function.surjInv hπ (π g)))) = φ g
      rw [toAdd_ofAdd]
      exact key φ hadd hker _ _ (Function.surjInv_eq hπ _)

private theorem card_hom_sub_le (l : ℕ) [Fact l.Prime] (A : Type) [CommGroup A] [Finite A] (B : Subgroup A) :
    Nat.card (B →* Multiplicative (ZMod l)) ≤ Nat.card (A →* Multiplicative (ZMod l)) := by
  rw [(cardTors B).2 l, (cardTors A).2 l, (cardTors B).1 l, (cardTors A).1 l]
  refine Nat.card_le_card_of_injective (fun x => ⟨((x : B) : A), ?_⟩) ?_
  · have hx := x.2
    rw [MonoidHom.mem_ker] at hx ⊢
    simp only [powMonoidHom_apply] at hx ⊢
    rw [← Subgroup.coe_pow, hx, Subgroup.coe_one]
  · intro x y h
    apply Subtype.ext
    apply Subtype.ext
    simpa using congrArg Subtype.val h

theorem UpperTheory.V.FW.homCyc :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (U N : Subgroup Γ) [U.Normal] [N.Normal] [N.FiniteIndex], N ≤ U → IsCyclic (Γ ⧸ U) → (∀ g, ∀ u ∈ U, g * u * g⁻¹ * u⁻¹ ∈ N) → Nat.card {φ : U → ZMod l // (∀ a b, φ (a * b) = φ a + φ b) ∧ ∀ u : U, u.1 ∈ N → φ u = 0} ≤ Nat.card {φ : Γ → ZMod l // (∀ a b, φ (a * b) = φ a + φ b) ∧ ∀ u ∈ N, φ u = 0} := by
  intro l _ Γ _ U N _ _ _ hNU hcyc hcomm
  have hU : ∀ (h : Γ ⧸ N) (u : Γ), u ∈ U → Commute h (u : Γ ⧸ N) := by
    intro h u hu
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective h
    have := hcomm g u hu
    rw [← QuotientGroup.eq_one_iff] at this
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at this
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at this
    exact this
  obtain ⟨gU, hgen⟩ := IsCyclic.exists_generator (α := Γ ⧸ U)
  obtain ⟨g0, rfl⟩ := QuotientGroup.mk_surjective gU
  have hdecomp : ∀ x : Γ, ∃ i : ℤ, ∃ u ∈ U, x = g0 ^ i * u := by
    intro x
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hgen (x : Γ ⧸ U))
    refine ⟨i, (g0 ^ i)⁻¹ * x, ?_, (mul_inv_cancel_left _ _).symm⟩
    rw [← QuotientGroup.mk_zpow] at hi
    exact QuotientGroup.eq.mp hi
  have hcomm' : ∀ a b : Γ ⧸ N, a * b = b * a := by
    intro a b
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    obtain ⟨i, u1, hu1, rfl⟩ := hdecomp x
    obtain ⟨j, u2, hu2, rfl⟩ := hdecomp y
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_zpow]
    have c12 : Commute ((g0 : Γ ⧸ N) ^ i) ((g0 : Γ ⧸ N) ^ j) := Commute.zpow_zpow_self _ _ _
    apply Commute.eq
    exact Commute.mul_left (c12.mul_right (hU _ u2 hu2))
      (((hU _ u1 hu1).symm).mul_right (hU _ u2 hu2))
  letI : CommGroup (Γ ⧸ N) := { (inferInstance : Group (Γ ⧸ N)) with mul_comm := hcomm' }
  let f : U →* Γ ⧸ N := (QuotientGroup.mk' N).comp U.subtype
  have h1 := card_hom_surj l f.rangeRestrict f.rangeRestrict_surjective (fun u : U => u.1 ∈ N) (by
    intro u
    rw [← Subtype.coe_inj]
    simp [f, QuotientGroup.eq_one_iff])
  have h2 := card_hom_surj l (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) (fun u => u ∈ N)
    (by intro u; simp [QuotientGroup.eq_one_iff])
  beta_reduce at h1 h2
  rw [h1, h2]
  exact card_hom_sub_le l (Γ ⧸ N) f.range
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Stick UpperTheory.V.FW
open scoped nonZeroDivisors

private theorem aH_lc {H M : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [AddCommGroup M]
    (φ : H → M) (h : ∀ a b, φ (a * b) = φ a + φ b) (N : Set H) (hN : IsOpen N) (h1 : (1 : H) ∈ N)
    (h0 : ∀ u ∈ N, φ u = 0) : IsLocallyConstant φ := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have ho : IsOpen ((fun y => x⁻¹ * y) ⁻¹' N) := hN.preimage (by fun_prop)
  filter_upwards [ho.mem_nhds (show x ∈ (fun y => x⁻¹ * y) ⁻¹' N by simpa using h1)] with y hy
  have := h x (x⁻¹ * y)
  rw [h0 _ hy, add_zero, mul_inv_cancel_left] at this
  exact this

private theorem aH_one {H M : Type} [Group H] [AddCommGroup M]
    (φ : H → M) (h : ∀ a b, φ (a * b) = φ a + φ b) : φ 1 = 0 := by
  have := h 1 1
  rw [mul_one] at this
  exact left_eq_add.1 this

private theorem aH_inv {H M : Type} [Group H] [AddCommGroup M]
    (φ : H → M) (h : ∀ a b, φ (a * b) = φ a + φ b) (a : H) : φ a⁻¹ = -φ a := by
  have := h a⁻¹ a
  rw [inv_mul_cancel, aH_one φ h] at this
  exact eq_neg_of_add_eq_zero_left this.symm

private theorem aH_mem {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (l : ℕ)
    (U : Subgroup (G F Ω)) [hU : U.Normal] (φ : U → ZMod l) :
    φ ∈ EqHom 1 U (Formalism.GaloisCohomology.scalRep (ZMod l) (1 : G F Ω →* (ZMod l)ˣ)) ↔
      IsLocallyConstant φ ∧ (∀ a b, φ (a * b) = φ a + φ b) ∧
        (∀ (A : ValuationSubring Ω) (u : U), u.1 ∈ Ine (F := F) A → φ u = 0) ∧
        ∀ (g : G F Ω) (u : U), φ ⟨g * u * g⁻¹, hU.conj_mem _ u.2 g⟩ = φ u := by
  rw [EqHom, Submodule.mem_inf, Submodule.mem_iInf]
  constructor
  · rintro ⟨⟨h1, h2, h3, -⟩, h4⟩
    refine ⟨h1, h2, h3, fun g u => ?_⟩
    have := h4 g u ⟨g * u * g⁻¹, hU.conj_mem _ u.2 g⟩ (fun x => by
      show g (u.1 (g.symm (g x))) = g (u.1 x)
      rw [AlgEquiv.symm_apply_apply])
    rw [this, scalRep_apply]
    simp
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨⟨h1, h2, h3, fun A hA => ?_⟩, fun g u u' h => ?_⟩
    · simp at hA
    · rw [scalRep_apply, ← h4 g u]
      have : u' = ⟨g * u * g⁻¹, hU.conj_mem _ u.2 g⟩ := Subtype.ext (AlgEquiv.ext fun x => by
        have := h (g.symm x)
        rw [show g.toRingEquiv (g.symm x) = x from g.apply_symm_apply x] at this
        exact this)
      rw [this]
      simp

theorem UpperTheory.V.FW.ambHom :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] [IsGalois F K] (l : ℕ) [Fact l.Prime] (ζ : F), IsPrimitiveRoot ζ l → IsCyclic Gal(K/F) → (∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → Ine (F := F) A ≤ galOf F K Ω) → Finite (EqHom 1 (galOf F K Ω) (Formalism.GaloisCohomology.scalRep (ZMod l) (1 : G F Ω →* (ZMod l)ˣ))) → Nat.card (EqHom 1 (galOf F K Ω) (Formalism.GaloisCohomology.scalRep (ZMod l) (1 : G F Ω →* (ZMod l)ˣ))) ≤ Set.ncard {φ : G F Ω → ZMod l | IsLocallyConstant φ ∧ (∀ a b, φ (a * b) = φ a + φ b) ∧ ∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∀ g ∈ Ine (F := F) A, φ g = 0} := by
  intro F Ω _ _ _ _ _ K _ _ _ _ _ _ _ l hl ζ hζ hc hI hfin
  haveI : IsGalois F Ω := {}
  have hUo : IsOpen (galOf F K Ω : Set (G F Ω)) := (galEmbTop F K Ω).2.1
  have hcyc : IsCyclic (G F Ω ⧸ galOf F K Ω) := by
    obtain ⟨q1, q2, -⟩ := galQuot F K Ω
    have e := (QuotientGroup.quotientMulEquivOfEq q2.symm).trans (QuotientGroup.quotientKerEquivOfSurjective _ q1)
    exact isCyclic_of_surjective e.symm e.symm.surjective
  have hn : (galOf F K Ω).Normal := inferInstance
  set U := galOf F K Ω with hUdef
  have hm := aH_mem l U
  set E := EqHom 1 U (Formalism.GaloisCohomology.scalRep (ZMod l) (1 : G F Ω →* (ZMod l)ˣ)) with hE
  let N : Subgroup (G F Ω) :=
    { carrier := {g | ∃ h : g ∈ U, ∀ φ : E, φ.1 ⟨g, h⟩ = 0}
      one_mem' := ⟨U.one_mem, fun φ => aH_one φ.1 ((hm _).1 φ.2).2.1⟩
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨U.mul_mem ha hb, fun φ => ?_⟩
        have := ((hm _).1 φ.2).2.1 ⟨a, ha⟩ ⟨b, hb⟩
        rw [ha', hb', add_zero] at this
        exact this
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨U.inv_mem ha, fun φ => ?_⟩
        have := aH_inv φ.1 ((hm _).1 φ.2).2.1 ⟨a, ha⟩
        rw [ha', neg_zero] at this
        exact this }
  have hN : ∀ g, g ∈ N ↔ ∃ h : g ∈ U, ∀ φ : E, φ.1 ⟨g, h⟩ = 0 := fun _ => Iff.rfl
  haveI : N.Normal := ⟨fun u ⟨hu, hu'⟩ g => ⟨hn.conj_mem u hu g, fun φ =>
    (((hm _).1 φ.2).2.2.2 g ⟨u, hu⟩).trans (hu' φ)⟩⟩
  have hNo : IsOpen (N : Set (G F Ω)) := by
    have : (N : Set (G F Ω)) = Subtype.val '' (⋂ φ : E, φ.1 ⁻¹' {0}) := by
      ext g
      simp only [SetLike.mem_coe, hN, Set.mem_image, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun ⟨h, h'⟩ => ⟨⟨g, h⟩, h', rfl⟩, fun ⟨u, h, e⟩ => e ▸ ⟨u.2, h⟩⟩
    rw [this]
    exact hUo.isOpenMap_subtype_val _ (isOpen_iInter_of_finite fun φ => ((hm _).1 φ.2).1 _)
  haveI : Finite (G F Ω ⧸ N) := N.quotient_finite_of_isOpen hNo
  haveI : N.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hcomm : ∀ g, ∀ u ∈ U, g * u * g⁻¹ * u⁻¹ ∈ N := fun g u hu => by
    refine ⟨U.mul_mem (hn.conj_mem u hu g) (U.inv_mem hu), fun φ => ?_⟩
    obtain ⟨-, h2, -, h4⟩ := (hm _).1 φ.2
    have := h2 ⟨g * u * g⁻¹, hn.conj_mem u hu g⟩ (⟨u, hu⟩ : U)⁻¹
    rw [aH_inv φ.1 h2, h4 g ⟨u, hu⟩, add_neg_cancel] at this
    exact this
  have hIN : ∀ (A : ValuationSubring Ω) (u : U), u.1 ∈ Ine (F := F) A → u.1 ∈ N := fun A u hu =>
    ⟨u.2, fun φ => ((hm _).1 φ.2).2.2.1 A u hu⟩
  have key := homCyc l (G F Ω) U N (fun g h => h.1) hcyc hcomm
  have e1 : Nat.card E = Nat.card {φ : U → ZMod l // (∀ a b, φ (a * b) = φ a + φ b) ∧ ∀ u : U, u.1 ∈ N → φ u = 0} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun φ => ⟨fun h => ⟨((hm _).1 h).2.1, fun u hu => hu.2 ⟨φ, h⟩⟩, ?_⟩)
    rintro ⟨h2, h0⟩
    refine (hm _).2 ⟨aH_lc φ h2 (Subtype.val ⁻¹' N) (hNo.preimage continuous_subtype_val) N.one_mem h0, h2,
      fun A u hu => h0 u (hIN A u hu), fun g u => ?_⟩
    have := h2 ⟨g * u * g⁻¹, hn.conj_mem u u.2 g⟩ u⁻¹
    rw [aH_inv φ h2, h0 _ (hcomm g u u.2)] at this
    exact add_neg_eq_zero.1 this.symm
  have hf := finChar F Ω l l ζ hl.out.ne_zero hl.out.ne_zero hζ
  rw [e1]
  refine key.trans ?_
  rw [← Nat.card_coe_set_eq]
  haveI := hf.to_subtype
  refine Nat.card_le_card_of_injective (fun φ => ⟨φ.1, aH_lc φ.1 φ.2.1 N hNo N.one_mem φ.2.2, φ.2.1,
    fun A hA g hg => φ.2.2 g (hIN A ⟨g, hI A hA hg⟩ hg)⟩) fun a b h => Subtype.ext (Subtype.mk.inj h)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.IneCyc
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Stick UpperTheory.V.FW
open scoped nonZeroDivisors

private theorem iC_one {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {m : ℕ} (hm : m ≠ 0) {ζ : Ω}
    (h : ζ ^ m = 1) : A.valuation ζ = 1 := by
  have h1 : A.valuation ζ ^ m = 1 := by rw [← map_pow, h, map_one]
  exact (pow_eq_one_iff_left hm).1 h1

private theorem iC_pow {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {η : Ω} (h1 : A.valuation η = 1)
    (h : A.valuation (η - 1) < 1) (i : ℕ) : A.valuation (1 - η ^ i) < 1 := by
  induction i with
  | zero => simp
  | succ i ih =>
    have e : 1 - η ^ (i + 1) = η * (1 - η ^ i) - (η - 1) := by ring
    rw [e]
    refine A.valuation.map_sub_lt ?_ h
    rw [map_mul, h1, one_mul]; exact ih

private theorem iC_eta {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {m : ℕ} (hm : m ≠ 0)
    (hv : ¬ A.valuation (m : Ω) < 1) {η : Ω} (hη : η ^ m = 1) (h : A.valuation (η - 1) < 1) : η = 1 := by
  by_contra hne
  apply hv
  have hs : ∑ i ∈ Finset.range m, η ^ i = 0 := by
    have := mul_geom_sum η m
    rw [hη, sub_self] at this
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)
  have e : (m : Ω) = ∑ i ∈ Finset.range m, (1 - η ^ i) := by
    rw [Finset.sum_sub_distrib, hs]; simp
  rw [e]
  exact A.valuation.map_sum_lt one_ne_zero fun i _ => iC_pow A (iC_one A hm hη) h i

private theorem iC_ine (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (l : ℕ) [hl : Fact l.Prime] (A : ValuationSubring Ω) (hA : ¬ A.valuation (l : Ω) < 1) (g : G F Ω)
    (hg : g ∈ Ine (F := F) A) (k : ℕ) (ζ : Ω) (hζ : ζ ^ l ^ k = 1) : g ζ = ζ := by
  have hm : l ^ k ≠ 0 := pow_ne_zero _ hl.out.ne_zero
  have hv := iC_one A hm hζ
  have h0 : ζ ≠ 0 := by
    rintro rfl
    simp at hv
  have hl1 : A.valuation (l : Ω) = 1 :=
    le_antisymm ((A.valuation_le_one_iff _).2 (natCast_mem A l)) (not_lt.1 hA)
  have hA' : ¬ A.valuation ((l ^ k : ℕ) : Ω) < 1 := by
    rw [Nat.cast_pow, map_pow, hl1, one_pow]; exact lt_irrefl _
  have e : g ζ / ζ - 1 = (g ζ - ζ) / ζ := by field_simp
  have : g ζ / ζ = 1 := by
    refine iC_eta A hm hA' (by rw [div_pow, ← map_pow, hζ, map_one, div_one]) ?_
    rw [e, map_div₀, hv, div_one]; exact hg.2 ζ hv.le
  exact (div_eq_one_iff_eq h0).1 this

theorem UpperTheory.V.FW.ineCyc :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) [IsCyclotomicExtension {l ^ n} F K] (A : ValuationSubring Ω), ¬ A.valuation (l : Ω) < 1 → Ine (F := F) A ≤ galOf F K Ω := by
  intro F Ω _ _ _ _ _ K _ _ _ _ _ _ l _ n hc A hA g hg x
  have hx := IsCyclotomicExtension.adjoin_roots (S := {l ^ n}) (A := F) (B := K) x
  show g (algebraMap K Ω x) = algebraMap K Ω x
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨m, hm, -, hy⟩ := hy
    obtain rfl : m = l ^ n := hm
    exact iC_ine F Ω l A hA g hg n _ (by rw [← map_pow, hy, map_one])
  | algebraMap r => rw [← IsScalarTower.algebraMap_apply]; exact g.commutes r
  | add a b _ _ ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
  | mul a b _ _ ha hb => rw [map_mul, map_mul, ha, hb]
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Stick UpperTheory.V.FW
open scoped nonZeroDivisors

theorem UpperTheory.V.FW.amb :
    ∀ (F : Type) [Field F] [NumberField F] (l : ℕ) [Fact l.Prime] (ζ : F), IsPrimitiveRoot ζ l → ∃ B : ℕ, ∀ (n : ℕ) (K : Type) [Field K] [NumberField K] [Algebra F K] [IsCyclotomicExtension {l ^ n} F K] (τ : Gal(K/F)), IsTotallyComplex K → (∀ σ : Gal(K/F), σ ∈ Subgroup.zpowers τ) → (powR (Cl K) l ⊔ difR (clMap τ.toRingEquiv)).index ≤ B := by
  intro F _ _ l _ ζ hζ
  obtain ⟨Ω, _, _, hΩ⟩ : ∃ (Ω : Type) (_ : Field Ω) (_ : Algebra F Ω), IsAlgClosure F Ω :=
    ⟨AlgebraicClosure F, inferInstance, inferInstance, inferInstance⟩
  haveI : IsAlgClosed Ω := hΩ.isAlgClosed
  haveI : Algebra.IsAlgebraic F Ω := hΩ.isAlgebraic
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  refine ⟨{φ : G F Ω → ZMod l | IsLocallyConstant φ ∧ (∀ a b : G F Ω, φ (a * b) = φ a + φ b) ∧
      ∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∀ g ∈ Ine A, φ g = 0}.ncard,
    fun n K _ _ _ _ τ hK hτ => ?_⟩
  haveI hgal : IsGalois F K := IsCyclotomicExtension.isGalois (S := {l ^ n}) (K := F) (L := K)
  let e : K →ₐ[F] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  letI : Algebra K Ω := e.toRingHom.toAlgebra
  haveI : IsScalarTower F K Ω := IsScalarTower.of_algebraMap_eq (fun x => (e.commutes x).symm)
  haveI : Algebra.IsAlgebraic K Ω := Algebra.IsAlgebraic.tower_top (K := F) K
  haveI : IsAlgClosure K Ω := ⟨inferInstance, inferInstance⟩
  let ρ : Representation (ZMod l) (G F Ω) (ZMod l) := scalRep (ZMod l) 1
  have hcyc : IsCyclic Gal(K/F) := ⟨⟨τ, hτ⟩⟩
  have hpe := (pullEq F Ω K (galOf F K Ω) le_rfl 1 (ZMod l) (ZMod l) ρ one_ne_zero le_rfl (Or.inl hK)).1
  have hinj := (pullMem F Ω K (galOf F K Ω) le_rfl 1 (ZMod l) (ZMod l) one_ne_zero).2 le_rfl
  haveI hCfin : Finite (ClEq K 1 ρ) := Subtype.finite
  have hcardEq : Nat.card (EqHom 1 (galOf F K Ω) ρ) = Nat.card (ClEq K 1 ρ) := by
    rw [← hpe]
    exact Nat.card_congr (Submodule.equivMapOfInjective _ hinj _).toEquiv.symm
  have hEfin : Finite (EqHom 1 (galOf F K Ω) ρ) := by
    rw [← hpe]
    exact Finite.of_equiv _ (Submodule.equivMapOfInjective _ hinj _).toEquiv
  have hamb := ambHom F Ω K l ζ hζ hcyc (ineCyc F Ω K l n) hEfin
  set H := powR (Cl K) l ⊔ difR (clMap τ.toRingEquiv) with hH
  have hfix : ∀ c : Cl K, (QuotientGroup.mk (clMap τ.toRingEquiv c) : Cl K ⧸ H) = QuotientGroup.mk c := by
    intro c
    rw [QuotientGroup.eq]
    have h1 : c / clMap τ.toRingEquiv c ∈ H := le_sup_right (a := powR (Cl K) l) ⟨c, rfl⟩
    have h2 : (clMap τ.toRingEquiv c)⁻¹ * c = c / clMap τ.toRingEquiv c := by
      rw [div_eq_mul_inv, mul_comm]
    rw [h2]
    exact h1
  have hmulc : ∀ (a b : Gal(K/F)) (c : Cl K),
      clMap (a * b).toRingEquiv c = clMap a.toRingEquiv (clMap b.toRingEquiv c) :=
    fun a b c => clMap_trans b.toRingEquiv a.toRingEquiv c
  have hone1 : ∀ c : Cl K, clMap (1 : Gal(K/F)).toRingEquiv c = c := fun c => clMap_refl K c
  have hinv : ∀ d : Cl K, (QuotientGroup.mk (clMap τ⁻¹.toRingEquiv d) : Cl K ⧸ H) = QuotientGroup.mk d := by
    intro d
    have h3 : clMap τ.toRingEquiv (clMap τ⁻¹.toRingEquiv d) = d := by
      rw [← hmulc, mul_inv_cancel, hone1]
    conv_rhs => rw [← h3]
    rw [hfix]
  have hall : ∀ α : Gal(K/F), ∀ c : Cl K,
      (QuotientGroup.mk (clMap α.toRingEquiv c) : Cl K ⧸ H) = QuotientGroup.mk c := by
    intro α
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hτ α)
    induction k using Int.induction_on with
    | zero =>
      intro c
      rw [zpow_zero, hone1]
    | succ k ih =>
      intro c
      rw [zpow_add_one, hmulc, ih, hfix]
    | pred k ih =>
      intro c
      rw [zpow_sub_one, hmulc, ih, hinv]
  have hlift : ∀ (g : G F Ω) (τ' : K ≃+* K), IsLift τ' g.toRingEquiv → ∀ c : Cl K,
      (QuotientGroup.mk (clMap τ' c) : Cl K ⧸ H) = QuotientGroup.mk c := by
    intro g τ' hl c
    unfold IsLift at hl
    have hF : ∀ x : F, τ' (algebraMap F K x) = algebraMap F K x := by
      intro x
      apply (algebraMap K Ω).injective
      rw [← hl]
      show g (algebraMap K Ω (algebraMap F K x)) = algebraMap K Ω (algebraMap F K x)
      rw [← IsScalarTower.algebraMap_apply, AlgEquiv.commutes]
    let α : Gal(K/F) := AlgEquiv.ofRingEquiv (f := τ') hF
    have hα : α.toRingEquiv = τ' := RingEquiv.ext fun x => rfl
    rw [← hα]
    exact hall α c
  have hpowQ : powR (Cl K ⧸ H) l = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    unfold powR at hy
    obtain ⟨x, rfl⟩ := hy
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective x
    rw [Subgroup.mem_bot]
    show (QuotientGroup.mk c : Cl K ⧸ H) ^ l = 1
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact le_sup_left (b := difR (clMap τ.toRingEquiv)) ⟨c, rfl⟩
  have hcardQ : H.index = Nat.card (Cl K ⧸ H →* Multiplicative (ZMod l)) := by
    rw [(cardTors (Cl K ⧸ H)).2 l, hpowQ, Subgroup.index_bot]
    rfl
  let Φ : (Cl K ⧸ H →* Multiplicative (ZMod l)) → ClEq K 1 ρ := fun ψ =>
    ⟨fun c => Multiplicative.toAdd (ψ (QuotientGroup.mk c)), by
      unfold ClEq
      rw [Submodule.mem_inf, Submodule.mem_iInf]
      refine ⟨?_, fun g => ?_⟩
      · unfold ClDual
        refine ⟨fun a b => ?_, fun v hv => ?_⟩
        · beta_reduce
          rw [QuotientGroup.mk_mul, map_mul, toAdd_mul]
        · exfalso
          unfold Above at hv
          exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr (by simpa using hv))
      · unfold clCond
        intro τ' hl c
        beta_reduce
        rw [hlift g τ' hl c]
        simp [ρ, scalRep]⟩
  have hΦ : Function.Injective Φ := by
    intro ψ1 ψ2 h
    apply MonoidHom.ext
    intro x
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective x
    have h4 := congrFun (congrArg Subtype.val h) c
    exact Multiplicative.toAdd.injective h4
  calc H.index = Nat.card (Cl K ⧸ H →* Multiplicative (ZMod l)) := hcardQ
    _ ≤ Nat.card (ClEq K 1 ρ) := Nat.card_le_card_of_injective Φ hΦ
    _ = Nat.card (EqHom 1 (galOf F K Ω) ρ) := hcardEq.symm
    _ ≤ _ := hamb
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.RelCyc
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Stick UpperTheory.V.FW
open scoped nonZeroDivisors

private theorem UpperTheory.V.FW.relCyc_compat {m N : ℕ} [NeZero m] [NeZero N] (h : m ∣ N) (K : Type) [Field K] [NumberField K]
    [IsCyclotomicExtension {m} ℚ K] (C : Type) [Field C] [NumberField C] [IsCyclotomicExtension {N} ℚ C]
    (i : K →ₐ[ℚ] C) (a : (ZMod N)ˣ) (x : K) :
    sg N C a (i x) = i (sg m K (ZMod.unitsMap h a) x) := by
  have hz := IsCyclotomicExtension.zeta_spec m ℚ K
  have key : ((sg N C a : C →ₐ[ℚ] C)).comp i = i.comp (sg m K (ZMod.unitsMap h a) : K →ₐ[ℚ] K) := by
    apply (hz.powerBasis ℚ).algHom_ext
    rw [IsPrimitiveRoot.powerBasis_gen]
    set z := IsCyclotomicExtension.zeta m ℚ K
    have h1 : z ^ m = 1 := hz.pow_eq_one
    have h2 : (i z) ^ m = 1 := by rw [← map_pow, h1, map_one]
    have h3 : (i z) ^ N = 1 := by
      obtain ⟨k, rfl⟩ := h
      rw [pow_mul, h2, one_pow]
    change sg N C a (i z) = i (sg m K (ZMod.unitsMap h a) z)
    rw [sg_apply N C a h3, sg_apply m K _ h1, map_pow]
    have : ((ZMod.unitsMap h a : (ZMod m)ˣ) : ZMod m).val = (a : ZMod N).val % m := by
      rw [ZMod.unitsMap_val, ZMod.cast_eq_val, ZMod.val_natCast]
    rw [this]
    exact pow_eq_pow_mod _ h2
  exact DFunLike.congr_fun key x

theorem UpperTheory.V.FW.relCyc :
    ∀ (l f e n : ℕ) [NeZero (f * l ^ n)] (h : f * l ^ e ∣ f * l ^ n) (F : Type) [Field F] [NumberField F] [IsCyclotomicExtension {f * l ^ e} ℚ F] (L : Type) [Field L] [NumberField L] [IsCyclotomicExtension {f * l ^ n} ℚ L], f.Coprime l → ∃ _ : Algebra F L, IsCyclotomicExtension {l ^ n} F L ∧ (∀ σ : Gal(L/F), ∃ t ∈ (ZMod.unitsMap h).ker, σ.toRingEquiv = (sg (f * l ^ n) L t).toRingEquiv) ∧ ∀ t ∈ (ZMod.unitsMap h).ker, ∃ σ : Gal(L/F), σ.toRingEquiv = (sg (f * l ^ n) L t).toRingEquiv := by
  intro l f e n _ h F _ _ _ L _ _ _ hfl
  have hM : 0 < f * l ^ n := NeZero.pos _
  have hM0 : 0 < f * l ^ e := Nat.pos_of_dvd_of_pos h hM
  haveI : NeZero (f * l ^ e) := ⟨hM0.ne'⟩
  have hf : 0 < f := Nat.pos_of_mul_pos_right hM
  have hln : 0 < l ^ n := Nat.pos_of_mul_pos_left hM
  haveI : NeZero (l ^ n) := ⟨hln.ne'⟩
  have hζ := IsCyclotomicExtension.zeta_spec (f * l ^ n) ℚ L
  set ζ := IsCyclotomicExtension.zeta (f * l ^ n) ℚ L
  have hz := IsCyclotomicExtension.zeta_spec (f * l ^ e) ℚ F
  set z := IsCyclotomicExtension.zeta (f * l ^ e) ℚ F with hzdef
  obtain ⟨k, hk⟩ := id h
  have hk' : l ^ n = k * l ^ e := by
    apply Nat.eq_of_mul_eq_mul_left hf
    rw [hk]; ring
  obtain ⟨i, hi⟩ : ∃ i : F →ₐ[ℚ] L, i z = ζ ^ k := by
    have hξ : IsPrimitiveRoot (ζ ^ k) (f * l ^ e) := hζ.pow hM (by rw [hk, mul_comm])
    refine ⟨(hz.powerBasis ℚ).lift (ζ ^ k) ?_, ?_⟩
    · rw [IsPrimitiveRoot.powerBasis_gen, ← Polynomial.cyclotomic_eq_minpoly_rat hz hM0,
        Polynomial.cyclotomic_eq_minpoly_rat hξ hM0]
      exact minpoly.aeval ℚ _
    · exact (congrArg _ (IsPrimitiveRoot.powerBasis_gen ℚ hz).symm).trans ((hz.powerBasis ℚ).lift_gen (ζ ^ k) _)
  letI : Algebra F L := i.toRingHom.toAlgebra
  have hal : ∀ x, algebraMap F L x = i x := fun _ => rfl
  refine ⟨this, ?_, ?_, ?_⟩
  · have hη : IsPrimitiveRoot (ζ ^ f) (l ^ n) := hζ.pow hM rfl
    rw [IsCyclotomicExtension.iff_singleton]
    refine ⟨⟨_, hη⟩, fun x => ?_⟩
    set A := Algebra.adjoin F {b : L | b ^ l ^ n = 1}
    have h1 : ζ ^ f ∈ A := Algebra.subset_adjoin hη.pow_eq_one
    have h2 : ζ ^ l ^ n ∈ A := by
      rw [hk', pow_mul, ← hi, ← hal]
      exact A.pow_mem (A.algebraMap_mem z) _
    have h3 : ζ ∈ A := by
      have hc : Nat.Coprime f (l ^ n) := hfl.pow_right n
      have hc' : Nat.Coprime (f + l ^ n) (f * l ^ n) :=
        Nat.Coprime.mul_right (by simpa using hc.symm) (by simpa using hc)
      obtain ⟨a, -, ha⟩ := (hζ.pow_of_coprime _ hc').eq_pow_of_pow_eq_one hζ.pow_eq_one
      rw [← ha, pow_add]
      exact A.pow_mem (A.mul_mem h1 h2) a
    have h4 : Algebra.adjoin ℚ {ζ} = ⊤ := IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ
    have h5 : x ∈ Algebra.adjoin ℚ {ζ} := h4 ▸ Algebra.mem_top
    have h6 : Algebra.adjoin ℚ {ζ} ≤ A.restrictScalars ℚ := Algebra.adjoin_le (by simpa using h3)
    exact h6 h5
  · intro σ
    obtain ⟨t, ht⟩ := (sg (f * l ^ n) L).surjective (σ.restrictScalars ℚ)
    refine ⟨t, ?_, by rw [ht]; rfl⟩
    rw [MonoidHom.mem_ker, ← map_eq_one_iff _ (sg (f * l ^ e) F).injective]
    ext y
    apply i.injective
    have := relCyc_compat h F L i t y
    rw [ht] at this
    exact this.symm.trans (σ.commutes y)
  · intro t ht
    refine ⟨{ (sg (f * l ^ n) L t).toRingEquiv with commutes' := fun y => ?_ }, rfl⟩
    have := relCyc_compat h F L i t y
    rw [MonoidHom.mem_ker.1 ht, map_one] at this
    exact this
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Stick UpperTheory.V.FW
open scoped nonZeroDivisors

theorem UpperTheory.V.FW.ambCyc :
    ∀ (l : ℕ) [Fact l.Prime] (f : ℕ), f.Coprime l → ∃ B : ℕ, ∀ (n : ℕ) [NeZero (f * l ^ n)] (L : Type) [Field L] [NumberField L] [IsCyclotomicExtension {f * l ^ n} ℚ L] (γ : (ZMod (f * l ^ n))ˣ), 2 ≤ n → (γ : ZMod (f * l ^ n)) = 1 + f * l ^ ee l → (powR (Cl L) l ⊔ difR (clA (f * l ^ n) L γ)).index ≤ B := by
  intro l hl f hf
  have hl1 : 1 < l := hl.out.one_lt
  have hlpos : 0 < l := hl.out.pos
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [Nat.coprime_zero_left] at hf
    omega
  have hfpos : 0 < f := Nat.pos_of_ne_zero hf0
  have he1 : 1 ≤ ee l := by unfold ee; split_ifs <;> omega
  have he2 : ee l ≤ 2 := by unfold ee; split_ifs <;> omega
  haveI : NeZero (f * l ^ ee l) := ⟨by positivity⟩
  haveI : NeZero ((f * l ^ ee l : ℕ) : ℚ) := ⟨by exact_mod_cast (show f * l ^ ee l ≠ 0 by positivity)⟩
  haveI : IsCyclotomicExtension {f * l ^ ee l} ℚ (CyclotomicField (f * l ^ ee l) ℚ) := by
    convert CyclotomicField.isCyclotomicExtension (f * l ^ ee l) ℚ
    · rfl
  haveI : NumberField (CyclotomicField (f * l ^ ee l) ℚ) :=
    IsCyclotomicExtension.numberField {f * l ^ ee l} ℚ _
  obtain ⟨z, hz⟩ : ∃ z : CyclotomicField (f * l ^ ee l) ℚ, IsPrimitiveRoot z (f * l ^ ee l) :=
    ⟨_, IsCyclotomicExtension.zeta_spec _ ℚ _⟩
  have hsplit : f * l ^ ee l = l * (f * l ^ (ee l - 1)) := by
    rw [mul_comm l, mul_assoc, ← pow_succ, Nat.sub_add_cancel he1]
  have hzl : IsPrimitiveRoot (z ^ (f * l ^ (ee l - 1))) l := by
    have h := hz.pow_of_dvd (by positivity) (Dvd.intro_left l hsplit.symm)
    rwa [Nat.div_eq_of_eq_mul_left (by positivity) hsplit] at h
  obtain ⟨B, hB⟩ := amb (CyclotomicField (f * l ^ ee l) ℚ) l _ hzl
  refine ⟨B, ?_⟩
  intro n _ L _ _ _ γ hn hγ
  have hen : ee l ≤ n := le_trans he2 hn
  have h : f * l ^ ee l ∣ f * l ^ n := mul_dvd_mul_left f (pow_dvd_pow l hen)
  obtain ⟨alg, hcycL, hall, hex⟩ := relCyc l f (ee l) n h (CyclotomicField (f * l ^ ee l) ℚ) L hf
  obtain ⟨hker, -⟩ := gamGen l f n h γ hf hen hγ
  letI := alg
  haveI := hcycL
  have hγinv : γ⁻¹ ∈ (ZMod.unitsMap h).ker := by
    rw [hker]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers γ)
  obtain ⟨τ, hτ⟩ := hex γ⁻¹ hγinv
  have hbig : 2 < f * l ^ n := by
    have h4 : 4 ≤ l ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ l ^ 2 := Nat.pow_le_pow_left hl.out.two_le 2
        _ ≤ l ^ n := Nat.pow_le_pow_right hlpos hn
    nlinarith
  have htc : IsTotallyComplex L := IsCyclotomicExtension.Rat.isTotallyComplex (n := f * l ^ n) L hbig
  let ρF : Gal(L/CyclotomicField (f * l ^ ee l) ℚ) →* (L ≃+* L) :=
    { toFun := fun σ => σ.toRingEquiv, map_one' := rfl, map_mul' := fun _ _ => rfl }
  let ρQ : Gal(L/ℚ) →* (L ≃+* L) :=
    { toFun := fun σ => σ.toRingEquiv, map_one' := rfl, map_mul' := fun _ _ => rfl }
  have hgen : ∀ σ : Gal(L/CyclotomicField (f * l ^ ee l) ℚ), σ ∈ Subgroup.zpowers τ := by
    intro σ
    obtain ⟨t, ht, hσ⟩ := hall σ
    rw [hker] at ht
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
    refine Subgroup.mem_zpowers_iff.mpr ⟨-k, ?_⟩
    have e1 : ρF σ = ρQ (sg (f * l ^ n) L (γ ^ k)) := hσ
    have e2 : ρF τ = ρQ (sg (f * l ^ n) L γ⁻¹) := hτ
    have e3 : ρF σ = ρF (τ ^ (-k)) := by
      rw [e1, map_zpow ρF, e2, ← map_zpow, ← map_zpow, inv_zpow', neg_neg]
    exact AlgEquiv.ext fun x => (congrArg (fun r : L ≃+* L => r x) e3).symm
  have hcl : clA (f * l ^ n) L γ = clMap τ.toRingEquiv := by
    rw [hτ, map_inv]
    rfl
  rw [hcl]
  exact hB n L τ htc hgen
