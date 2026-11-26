module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ChainRuleAndJacobianCriterion
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationPolarisationsAgreeAtLevel
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompletedLaurentIsDVRStatement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsFOfIntegral

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CoeffRecoveryByTorsionAverages
namespace GlobalTheory.TorsRecov

theorem card_tors (F X : Type) [Field F] [IsAlgClosed F] [CharZero F] [AddCommGroup X]
    [Module.Free ℤ X] [Module.Finite ℤ X] (N : ℕ) (hN : 0 < N) :
    Nat.card {t : Multiplicative X →* Fˣ // t ^ N = 1} = N ^ Module.finrank ℤ X := by
  classical
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : NeZero (N : F) := ⟨by exact_mod_cast hN.ne'⟩
  let b := Module.Free.chooseBasis ℤ X
  let f : {t : Multiplicative X →* Fˣ // t ^ N = 1} →
      (Module.Free.ChooseBasisIndex ℤ X → rootsOfUnity N F) := fun t i =>
    ⟨t.1 (Multiplicative.ofAdd (b i)), by
      rw [mem_rootsOfUnity, ← MonoidHom.pow_apply, t.2, MonoidHom.one_apply]⟩
  have hrep : ∀ (t : Multiplicative X →* Fˣ) (x : X), t (Multiplicative.ofAdd x) =
      ∏ i, t (Multiplicative.ofAdd (b i)) ^ (b.repr x i) := by
    intro t x
    conv_lhs => rw [← b.sum_repr x]
    rw [ofAdd_sum, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [ofAdd_zsmul, map_zpow]
  have hf : Function.Bijective f := by
    constructor
    · intro s t h
      apply Subtype.ext
      refine MonoidHom.ext fun x => ?_
      have h1 := hrep s.1 x.toAdd
      have h2 := hrep t.1 x.toAdd
      rw [ofAdd_toAdd] at h1 h2
      rw [h1, h2]
      refine Finset.prod_congr rfl fun i _ => ?_
      have := congrArg Subtype.val (congrFun h i)
      simp only [f] at this
      rw [this]
    · intro u
      let t : Multiplicative X →* Fˣ :=
        { toFun := fun x => ∏ i, (u i : Fˣ) ^ (b.repr (Multiplicative.toAdd x) i)
          map_one' := by simp
          map_mul' := by
            intro x y
            simp [zpow_add, Finset.prod_mul_distrib] }
      have ht : t ^ N = 1 := by
        refine MonoidHom.ext fun x => ?_
        rw [MonoidHom.pow_apply, MonoidHom.one_apply]
        change (∏ i, (u i : Fˣ) ^ (b.repr (Multiplicative.toAdd x) i)) ^ N = 1
        rw [← Finset.prod_pow]
        refine Finset.prod_eq_one fun i _ => ?_
        have hu : (u i : Fˣ) ^ N = 1 := (mem_rootsOfUnity _ _).1 (u i).2
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu, one_zpow]
      refine ⟨⟨t, ht⟩, ?_⟩
      funext i
      apply Subtype.ext
      change ∏ j, (u j : Fˣ) ^ (b.repr (b i) j) = u i
      rw [Finset.prod_eq_single i]
      · simp
      · intro j _ hj
        simp [Finsupp.single_apply, hj.symm]
      · simp
  rw [Nat.card_congr (Equiv.ofBijective f hf), Nat.card_fun, HasEnoughRootsOfUnity.natCard_rootsOfUnity,
    Module.finrank_eq_card_chooseBasisIndex, Nat.card_eq_fintype_card]

open Classical in
theorem sum_tors (F X : Type) [Field F] [IsAlgClosed F] [CharZero F] [AddCommGroup X]
    [Module.Free ℤ X] [Module.Finite ℤ X] (N : ℕ) (hN : 0 < N)
    [Fintype {t : Multiplicative X →* Fˣ // t ^ N = 1}] (α β : X) :
    ∑ t : {t : Multiplicative X →* Fˣ // t ^ N = 1},
      ((t.1 (Multiplicative.ofAdd β))⁻¹).val * (t.1 (Multiplicative.ofAdd α)).val =
      if ∃ z, α = β + N • z then (N : F) ^ Module.finrank ℤ X else 0 := by
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : NeZero (N : F) := ⟨by exact_mod_cast hN.ne'⟩
  split_ifs with h
  · obtain ⟨z, rfl⟩ := h
    rw [Finset.sum_congr rfl (g := fun _ => (1 : F))]
    · rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, card_tors F X N hN]
      simp
    · intro t _
      rw [ofAdd_add, map_mul, ofAdd_nsmul, map_pow, ← MonoidHom.pow_apply, t.2]
      simp
  · obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot F N
    have : ∃ t₀ : Multiplicative X →* Fˣ, t₀ ^ N = 1 ∧
        t₀ (Multiplicative.ofAdd α) ≠ t₀ (Multiplicative.ofAdd β) := by
      by_contra hc
      push_neg at hc
      exact h (GlobalTheory.exists_eq_add_nsmul_of_torsion_characters_eq F X N ζ hN hζ α β hc)
    obtain ⟨t₀, h₀, hne⟩ := this
    have h₀' : t₀⁻¹ ^ N = 1 := by rw [inv_pow, h₀, inv_one]
    let e : {t : Multiplicative X →* Fˣ // t ^ N = 1} ≃ {t : Multiplicative X →* Fˣ // t ^ N = 1} :=
      { toFun := fun t => ⟨t₀ * t.1, by rw [mul_pow, h₀, t.2, mul_one]⟩
        invFun := fun t => ⟨t₀⁻¹ * t.1, by rw [mul_pow, h₀', t.2, mul_one]⟩
        left_inv := fun t => Subtype.ext (inv_mul_cancel_left _ _)
        right_inv := fun t => Subtype.ext (mul_inv_cancel_left _ _) }
    set s := ∑ t : {t : Multiplicative X →* Fˣ // t ^ N = 1},
      ((t.1 (Multiplicative.ofAdd β))⁻¹).val * (t.1 (Multiplicative.ofAdd α)).val with hs
    have h1 : s = (((t₀ (Multiplicative.ofAdd β))⁻¹).val * (t₀ (Multiplicative.ofAdd α)).val) * s := by
      conv_lhs => rw [hs, ← e.sum_comp]
      rw [hs, Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      simp only [e, Equiv.coe_fn_mk, MonoidHom.mul_apply, mul_inv, Units.val_mul]
      ring
    by_contra hs0
    apply hne
    have h2 : ((t₀ (Multiplicative.ofAdd β))⁻¹).val * (t₀ (Multiplicative.ofAdd α)).val = 1 :=
      mul_right_cancel₀ hs0 (by rw [← h1, one_mul])
    rw [← Units.val_mul, Units.val_eq_one, inv_mul_eq_one] at h2
    exact h2.symm

theorem eq_zero_of_div (X : Type) [AddCommGroup X] [Module.Free ℤ X] (n : ℕ) (hn : 2 ≤ n) (x : X)
    (h : ∀ k, ∃ z, x = n ^ k • z) : x = 0 := by
  let b := Module.Free.chooseBasis ℤ X
  apply b.repr.injective
  ext i
  rw [map_zero, Finsupp.zero_apply]
  obtain ⟨z, hz⟩ := h (b.repr x i).natAbs
  refine Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (d := ((n ^ (b.repr x i).natAbs : ℕ) : ℤ))
    ⟨b.repr z i, ?_⟩ ?_
  · conv_lhs => rw [hz]
    rw [map_nsmul, Finsupp.smul_apply, nsmul_eq_mul]
  · rw [Int.natAbs_natCast]
    exact Nat.lt_pow_self (by omega)

theorem class_mono (X : Type) [AddCommGroup X] (n : ℕ) (c : ℕ → X)
    (hc : ∀ k, ∃ z, c (k + 1) = c k + n ^ k • z) (α : X) (j k : ℕ) (hjk : j ≤ k)
    (h : ∃ z, α = c k + n ^ k • z) : ∃ z, α = c j + n ^ j • z := by
  induction k, hjk using Nat.le_induction with
  | base => exact h
  | succ k _ ih =>
    apply ih
    obtain ⟨z, hz⟩ := h
    obtain ⟨w, hw⟩ := hc k
    exact ⟨w + n • z, by rw [hz, hw, pow_succ, mul_smul, smul_add, add_assoc]⟩

theorem val_eq_zero_of_pow {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) (x : F) (N : ℕ)
    (hN : 0 < N) (h : x ^ N = 1) : v x = 0 := by
  have h1 : N • v x = 0 := by rw [← v.map_pow, h, v.map_one]
  have hx : x ≠ 0 := by
    rintro rfl
    rw [zero_pow hN.ne'] at h
    exact zero_ne_one h
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 ((v.ne_top_iff).2 hx)
  rw [← hr, ← WithTop.coe_nsmul, WithTop.coe_eq_zero, smul_eq_zero] at h1
  rw [← hr, h1.resolve_left hN.ne', WithTop.coe_zero]

theorem val_inv_pow {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) (x : F) (m : ℕ)
    (h : v x = 0) : v (x ^ m)⁻¹ = 0 := by
  have hx : x ≠ 0 := by
    rintro rfl
    rw [v.map_zero] at h
    exact WithTop.top_ne_zero h
  have h1 : v (x ^ m) = 0 := by rw [v.map_pow, h, smul_zero]
  have h2 := v.map_mul (x ^ m) (x ^ m)⁻¹
  rw [mul_inv_cancel₀ (pow_ne_zero _ hx), v.map_one, h1, zero_add] at h2
  exact h2.symm

end GlobalTheory.TorsRecov

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

theorem GlobalTheory.coeff_recovery_by_torsion_averages : ∀ (F : Type) [Field F] [IsAlgClosed F] [CharZero F] (v : AddValuation F (WithTop ℚ)) (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (n : ℕ), 2 ≤ n → v (n : F) = 0 → ∀ a : X → F, NullV v a → ∀ S : (Multiplicative X →* Fˣ) → F, (∀ t : Multiplicative X →* Fˣ, (∃ k, t ^ n ^ k = 1) → SumV v (fun α => (t (Multiplicative.ofAdd α)).val * a α) (S t)) → ∀ c : ℕ → X, (∀ k, ∃ z, c (k + 1) = c k + n ^ k • z) → ∀ (lim : F), ((∃ χ, (∀ k, ∃ z, χ = c k + n ^ k • z) ∧ lim = a χ) ∨ ((¬ ∃ χ, ∀ k, ∃ z, χ = c k + n ^ k • z) ∧ lim = 0)) → ∀ q : ℚ, ∃ k₀, ∀ k ≥ k₀, (q : WithTop ℚ) ≤ v (lim - ((n : F) ^ (k * Module.finrank ℤ X))⁻¹ * ∑ᶠ t : {t : Multiplicative X →* Fˣ // t ^ n ^ k = 1}, ((t.1 (Multiplicative.ofAdd (c k)))⁻¹).val * S t.1) := by
  intro F _ _ _ v X _ _ _ n hn hv a ha S hS c hc lim hlim q
  classical
  have hB : ∀ α : X, ∃ j : ℕ, (¬ ∀ k, ∃ z, α = c k + n ^ k • z) → ¬ ∃ z, α = c j + n ^ j • z := by
    intro α
    by_cases h : ∀ k, ∃ z, α = c k + n ^ k • z
    · exact ⟨0, fun h' => (h' h).elim⟩
    · obtain ⟨j, hj⟩ := not_forall.1 h
      exact ⟨j, fun _ => hj⟩
  choose j hj using hB
  refine ⟨(ha q).toFinset.sup j, fun k hk => ?_⟩
  have hN : 0 < n ^ k := pow_pos (by omega) k
  have hn0 : (n : F) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have key : ∀ α : X, (∃ z, α = c k + n ^ k • z) → (¬ ∀ k, ∃ z, α = c k + n ^ k • z) →
      (q : WithTop ℚ) ≤ v (a α) := by
    intro α h1 h2
    by_contra h3
    have h4 : α ∈ (ha q).toFinset := (ha q).mem_toFinset.2 (not_le.1 h3)
    exact hj α h2 (GlobalTheory.TorsRecov.class_mono X n c hc α _ k ((Finset.le_sup h4).trans hk) h1)
  haveI : Finite {t : Multiplicative X →* Fˣ // t ^ n ^ k = 1} :=
    Nat.finite_of_card_ne_zero (by
      rw [GlobalTheory.TorsRecov.card_tors F X _ hN]; exact pow_ne_zero _ hN.ne')
  letI := Fintype.ofFinite {t : Multiplicative X →* Fˣ // t ^ n ^ k = 1}
  rw [finsum_eq_sum_of_fintype]
  have hS' := fun t : {t : Multiplicative X →* Fˣ // t ^ n ^ k = 1} => hS t.1 ⟨k, t.2⟩ q
  choose S₀ hS₀ using hS'
  have main : ∀ T : Finset X, (∀ t, S₀ t ⊆ T) →
      (q : WithTop ℚ) ≤ v (lim - ∑ α ∈ T.filter (fun α => ∃ z, α = c k + n ^ k • z), a α) →
      (q : WithTop ℚ) ≤ v (lim - ((n : F) ^ (k * Module.finrank ℤ X))⁻¹ *
        ∑ t : {t : Multiplicative X →* Fˣ // t ^ n ^ k = 1},
          ((t.1 (Multiplicative.ofAdd (c k)))⁻¹).val * S t.1) := by
    intro T hT h
    have e1 : ∑ t : {t : Multiplicative X →* Fˣ // t ^ n ^ k = 1},
          ((t.1 (Multiplicative.ofAdd (c k)))⁻¹).val *
            ∑ α ∈ T, (t.1 (Multiplicative.ofAdd α)).val * a α =
        (n : F) ^ (k * Module.finrank ℤ X) *
          ∑ α ∈ T.filter (fun α => ∃ z, α = c k + n ^ k • z), a α := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm, Finset.sum_filter]
      refine Finset.sum_congr rfl fun α _ => ?_
      simp only [← _root_.mul_assoc]
      rw [← Finset.sum_mul, GlobalTheory.TorsRecov.sum_tors F X _ hN]
      split_ifs
      · rw [Nat.cast_pow, ← pow_mul]
      · rw [zero_mul]
    have e2 : lim - ((n : F) ^ (k * Module.finrank ℤ X))⁻¹ *
        ∑ t : {t : Multiplicative X →* Fˣ // t ^ n ^ k = 1},
          ((t.1 (Multiplicative.ofAdd (c k)))⁻¹).val * S t.1 =
        (lim - ∑ α ∈ T.filter (fun α => ∃ z, α = c k + n ^ k • z), a α) -
        ((n : F) ^ (k * Module.finrank ℤ X))⁻¹ *
        ∑ t : {t : Multiplicative X →* Fˣ // t ^ n ^ k = 1},
          ((t.1 (Multiplicative.ofAdd (c k)))⁻¹).val *
            (S t.1 - ∑ α ∈ T, (t.1 (Multiplicative.ofAdd α)).val * a α) := by
      simp only [mul_sub, Finset.sum_sub_distrib]
      rw [e1, inv_mul_cancel_left₀ (pow_ne_zero _ hn0)]
      ring
    rw [e2]
    refine v.map_le_sub h ?_
    rw [v.map_mul, GlobalTheory.TorsRecov.val_inv_pow v _ _ hv, zero_add]
    refine v.map_le_sum fun t _ => ?_
    rw [v.map_mul, GlobalTheory.TorsRecov.val_eq_zero_of_pow v _ _ hN, zero_add]
    · exact hS₀ t T (hT t)
    · rw [← Units.val_pow_eq_pow_val, inv_pow, ← MonoidHom.pow_apply, t.2]
      simp
  rcases hlim with ⟨χ, hχ, rfl⟩ | ⟨hno, rfl⟩
  · refine main (insert χ (Finset.univ.biUnion S₀)) (fun t => ?_) ?_
    · exact (Finset.subset_biUnion_of_mem S₀ (Finset.mem_univ t)).trans (Finset.subset_insert _ _)
    · rw [← Finset.add_sum_erase _ a (a := χ)
        (Finset.mem_filter.2 ⟨Finset.mem_insert_self _ _, hχ k⟩), sub_add_cancel_left, v.map_neg]
      refine v.map_le_sum fun α hα => ?_
      obtain ⟨h1, h2⟩ := Finset.mem_erase.1 hα
      refine key α (Finset.mem_filter.1 h2).2 fun h3 => h1 ?_
      rw [← sub_eq_zero]
      refine GlobalTheory.TorsRecov.eq_zero_of_div X n hn _ fun m => ?_
      obtain ⟨z, hz⟩ := h3 m
      obtain ⟨w, hw⟩ := hχ m
      exact ⟨z - w, by rw [hz, hw, smul_sub, add_sub_add_left_eq_sub]⟩
  · refine main (Finset.univ.biUnion S₀)
      (fun t => Finset.subset_biUnion_of_mem S₀ (Finset.mem_univ t)) ?_
    rw [zero_sub, v.map_neg]
    refine v.map_le_sum fun α hα => ?_
    exact key α (Finset.mem_filter.1 hα).2 fun h3 => hno ⟨α, h3⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EqOneOfGroupLike
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UU.UnitRigid

theorem coeff_inl_mul_inr {B X : Type} [CommRing B] [AddCommGroup X] (a b : AddMonoidAlgebra B X) (x y : X) :
    (AddMonoidAlgebra.mapDomainRingHom B (AddMonoidHom.inl X X) a *
      AddMonoidAlgebra.mapDomainRingHom B (AddMonoidHom.inr X X) b).coeff (x, y) = a.coeff x * b.coeff y := by
  classical
  induction a using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add a a' h h' => simp only [map_add (f := _), add_mul, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, h, h']
  | single p r =>
    induction b using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add b b' h h' => simp only [map_add (f := _), mul_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, h, h']
    | single q s =>
      simp only [AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain_single,
        AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
      by_cases h₁ : p = x <;> by_cases h₂ : q = y <;> simp [h₁, h₂]

theorem eq_one_of_groupLike {B X : Type} [CommRing B] [AddCommGroup X] (I : Ideal B) (hI : ∀ b ∈ I, IsNilpotent b)
    (g : AddMonoidAlgebra B X)
    (h : AddMonoidAlgebra.mapDomainRingHom B ((AddMonoidHom.id X).prod (AddMonoidHom.id X)) g =
      AddMonoidAlgebra.mapDomainRingHom B (AddMonoidHom.inl X X) g *
        AddMonoidAlgebra.mapDomainRingHom B (AddMonoidHom.inr X X) g)
    (h₁ : AddMonoidAlgebra.mapRingHom X (Ideal.Quotient.mk I) g = 1) : g = 1 := by
  classical
  have idem : ∀ x, IsIdempotentElem (g.coeff x) := fun x => by
    have e := congrArg (fun a => a.coeff (x, x)) h
    simp only [coeff_inl_mul_inr] at e
    refine e.symm.trans ?_
    exact Finsupp.mapDomain_apply_of_injective (f := fun x : X => (x, x)) (fun _ _ q => congrArg Prod.fst q) g.coeff x
  ext x
  have e := congrArg (fun a => a.coeff x) h₁
  simp only [AddMonoidAlgebra.coeff_mapRingHom, AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single,
    Finsupp.single_apply] at e ⊢
  split_ifs at e ⊢ with hx
  · have m : 1 - g.coeff x ∈ I := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, e, map_one, sub_self]
    exact (sub_eq_zero.1 ((idem x).one_sub.eq_zero_of_isNilpotent (hI _ m))).symm
  · exact (idem x).eq_zero_of_isNilpotent (hI _ (Ideal.Quotient.eq_zero_iff_mem.1 e))

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]

theorem chV_comp {Z Z' : Over S} (σ : Z' ⟶ Z) (t : Z ⟶ splitTorus S X) (χ : X) :
    (chV (σ ≫ t) χ).val = σ.left.appTop.hom (chV t χ).val := by
  rw [chV_val, chV_val, Rosenlicht.over_appTop_comp]

theorem point_ext {Z : Over S} {t t' : Z ⟶ splitTorus S X} (h : ∀ χ, (chV t χ).val = (chV t' χ).val) : t = t' :=
  (splitTorusPointsEquiv S X Z).injective (MonoidHom.ext fun a => Units.ext (h a.toAdd))

theorem exists_point (Z : Over S) (c : Multiplicative X →* Γ(Z.left, ⊤)) :
    ∃ t : Z ⟶ splitTorus S X, ∀ χ, (chV t χ).val = c (Multiplicative.ofAdd χ) :=
  ⟨(splitTorusPointsEquiv S X Z).symm c.toHomUnits, fun χ => by rw [chV, MulEquiv.apply_symm_apply]; rfl⟩

theorem exists_universal {Y W : Over S} [IsAffine W.left] (y : W ⟶ Y) (u : Γ((splitTorus S X ⊗ Y).left, ⊤)) :
    ∃ g : AddMonoidAlgebra Γ(W.left, ⊤) X, ∀ (Z : Over S) (s : Z ⟶ W) (t : Z ⟶ splitTorus S X)
      (θ : AddMonoidAlgebra Γ(W.left, ⊤) X →+* Γ(Z.left, ⊤)),
      (∀ b, θ (AddMonoidAlgebra.single 0 b) = s.left.appTop.hom b) →
      (∀ χ, θ (AddMonoidAlgebra.single χ 1) = (chV t χ).val) → (lift t (s ≫ y)).left.appTop.hom u = θ g := by
  obtain ⟨U, y₀, e, -, -, H⟩ := RingPoint.exists_ringPoint W (AddMonoidAlgebra Γ(W.left, ⊤) X)
    AddMonoidAlgebra.singleZeroRingHom
  obtain ⟨t₀, ht₀⟩ := exists_point U (e.symm.toMonoidHom.comp (AddMonoidAlgebra.of _ X))
  refine ⟨e ((lift t₀ (y₀ ≫ y)).left.appTop.hom u), fun Z s t θ h₁ h₂ => ?_⟩
  obtain ⟨σ, hσ, hθ⟩ := H Z s θ h₁
  have ht : σ ≫ t₀ = t := point_ext fun χ => by
    rw [chV_comp, hθ, ht₀, ← h₂]
    exact congrArg θ (e.apply_symm_apply _)
  rw [← hθ, ← ht, ← hσ, Category.assoc, ← comp_lift, Rosenlicht.over_appTop_comp]

theorem eq_one_affine {A : Type} [CommRing A] (J : Ideal A) (hJ : IsNilpotent J) {Y W : Over (Spec (CommRingCat.of A))}
    [IsAffine W.left] (u : Γ((splitTorus (Spec (CommRingCat.of A)) X ⊗ Y).left, ⊤))
    (hm : ∀ (Z : Over (Spec (CommRingCat.of A))) (t t' : Z ⟶ splitTorus _ X) (y : Z ⟶ Y),
      (lift (t * t') y).left.appTop.hom u = (lift t y).left.appTop.hom u * (lift t' y).left.appTop.hom u)
    (h₁ : ∀ (Z : Over (Spec (CommRingCat.of A))), (∃ s, s ≫ red J = Z.hom) → ∀ (t : Z ⟶ splitTorus _ X) (y : Z ⟶ Y),
      (lift t y).left.appTop.hom u = 1) (t : W ⟶ splitTorus _ X) (y : W ⟶ Y) : (lift t y).left.appTop.hom u = 1 := by
  obtain ⟨g, hg⟩ := exists_universal y u
  let I : Ideal Γ(W.left, ⊤) := J.map (RingPoint.strMap W)
  have hI : ∀ b ∈ I, IsNilpotent b := fun b hb => by
    obtain ⟨n, hn⟩ := hJ
    refine ⟨n, ?_⟩
    have := Ideal.pow_mem_pow hb n
    rw [← Ideal.map_pow, hn, Ideal.zero_eq_bot, Ideal.map_bot] at this
    exact this
  have one : g = 1 := by
    refine eq_one_of_groupLike I hI g ?_ ?_
    · obtain ⟨U, s, e, -, he, -⟩ := RingPoint.exists_ringPoint W (AddMonoidAlgebra Γ(W.left, ⊤) (X × X))
        AddMonoidAlgebra.singleZeroRingHom
      have key : ∀ (f : X →+ X × X) (t : U ⟶ splitTorus _ X),
          (∀ χ, (chV t χ).val = e.symm (AddMonoidAlgebra.single (f χ) 1)) →
          (lift t (s ≫ y)).left.appTop.hom u = e.symm (AddMonoidAlgebra.mapDomainRingHom _ f g) := fun f t ht =>
        hg U s t (e.symm.toRingHom.comp (AddMonoidAlgebra.mapDomainRingHom _ f))
          (fun b => e.symm_apply_eq.2 (by rw [he]; simp)) (fun χ => by rw [ht]; simp)
      obtain ⟨t₁, ht₁⟩ := exists_point U (e.symm.toMonoidHom.comp ((AddMonoidAlgebra.of _ (X × X)).comp
        (AddMonoidHom.toMultiplicative (AddMonoidHom.inl X X))))
      obtain ⟨t₂, ht₂⟩ := exists_point U (e.symm.toMonoidHom.comp ((AddMonoidAlgebra.of _ (X × X)).comp
        (AddMonoidHom.toMultiplicative (AddMonoidHom.inr X X))))
      have a₁ : ∀ χ, (chV t₁ χ).val = e.symm (AddMonoidAlgebra.single (AddMonoidHom.inl X X χ) 1) := ht₁
      have a₂ : ∀ χ, (chV t₂ χ).val = e.symm (AddMonoidAlgebra.single (AddMonoidHom.inr X X χ) 1) := ht₂
      apply e.symm.injective
      rw [map_mul, ← key _ t₁ a₁, ← key _ t₂ a₂, ← hm, key]
      intro χ
      rw [chV_mul, Units.val_mul, a₁, a₂, ← map_mul, AddMonoidAlgebra.single_mul_single]
      simp
    · obtain ⟨U, s, e, -, he, -⟩ := RingPoint.exists_ringPoint W (AddMonoidAlgebra (Γ(W.left, ⊤) ⧸ I) X)
        (AddMonoidAlgebra.singleZeroRingHom.comp (Ideal.Quotient.mk I))
      obtain ⟨t₁, ht₁⟩ := exists_point U (e.symm.toMonoidHom.comp (AddMonoidAlgebra.of _ X))
      have a₁ : ∀ χ, (chV t₁ χ).val = e.symm (AddMonoidAlgebra.single χ 1) := ht₁
      have hU : ∃ s, s ≫ red J = U.hom := (RingPoint.exists_comp_red_iff J U).2 fun a ha => by
        apply e.injective
        rw [← RingPoint.appTop_strMap s, he, RingHom.comp_apply,
          Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ ha), map_zero, map_zero]
      have k := hg U s t₁ (e.symm.toRingHom.comp (AddMonoidAlgebra.mapRingHom X (Ideal.Quotient.mk I)))
        (fun b => e.symm_apply_eq.2 (by rw [he]; simp)) (fun χ => by rw [a₁]; simp)
      apply e.symm.injective
      rw [map_one]
      exact k.symm.trans (h₁ U hU _ _)
  have k := hg W (𝟙 W) t (AddMonoidAlgebra.liftNCRingHom (RingHom.id _)
    ((Units.coeHom _).comp (splitTorusPointsEquiv _ X W t)) fun _ _ => Commute.all _ _)
    (fun b => by simp) (fun χ => by simp [chV])
  rwa [Category.id_comp, one, map_one] at k

theorem unit_eq_one : ∀ (A : Type) [CommRing A] (J : Ideal A), IsNilpotent J → ∀ (X : Type) [AddCommGroup X] (Y : Over (Spec (CommRingCat.of A))) (u : Γ((splitTorus (Spec (CommRingCat.of A)) X ⊗ Y).left, ⊤)ˣ), (∀ (Z : Over (Spec (CommRingCat.of A))) (t t' : Z ⟶ splitTorus _ X) (y : Z ⟶ Y) (z : Z.left), gm (lift (t * t') y).left z ⊤ u = gm (lift t y).left z ⊤ u * gm (lift t' y).left z ⊤ u) → (∀ (Z : Over (Spec (CommRingCat.of A))), (∃ s, s ≫ red J = Z.hom) → ∀ (t : Z ⟶ splitTorus _ X) (y : Z ⟶ Y) (z : Z.left), gm (lift t y).left z ⊤ u = 1) → u = 1 := by
  intro A _ J hJ X _ Y u hm h₁
  have hm' : ∀ (Z : Over (Spec (CommRingCat.of A))) (t t' : Z ⟶ splitTorus _ X) (y : Z ⟶ Y),
      (lift (t * t') y).left.appTop.hom u.val =
        (lift t y).left.appTop.hom u.val * (lift t' y).left.appTop.hom u.val := fun Z t t' y => by
    have e : Units.map (lift (t * t') y).left.appTop.hom.toMonoidHom u =
        Units.map (lift t y).left.appTop.hom.toMonoidHom u * Units.map (lift t' y).left.appTop.hom.toMonoidHom u :=
      unit_ext fun z _ => by rw [map_mul, ← gm_top, ← gm_top, ← gm_top, hm]
    exact congrArg Units.val e
  have h₁' : ∀ (Z : Over (Spec (CommRingCat.of A))), (∃ s, s ≫ red J = Z.hom) →
      ∀ (t : Z ⟶ splitTorus _ X) (y : Z ⟶ Y), (lift t y).left.appTop.hom u.val = 1 := fun Z hZ t y => by
    have e : Units.map (lift t y).left.appTop.hom.toMonoidHom u = 1 :=
      unit_ext fun z _ => by rw [map_one, ← gm_top, h₁ Z hZ]
    exact congrArg Units.val e
  refine unit_ext fun z _ => ?_
  let 𝒰 := (splitTorus (Spec (CommRingCat.of A)) X ⊗ Y).left.affineCover
  obtain ⟨i, w, rfl⟩ := 𝒰.exists_eq z
  let W : Over (Spec (CommRingCat.of A)) := Over.mk (𝒰.f i ≫ (splitTorus (Spec (CommRingCat.of A)) X ⊗ Y).hom)
  haveI : IsAffine W.left := inferInstanceAs (IsAffine (𝒰.X i))
  let κ : W ⟶ splitTorus (Spec (CommRingCat.of A)) X ⊗ Y := Over.homMk (𝒰.f i) rfl
  have e := eq_one_affine J hJ u.val hm' h₁' (κ ≫ fst _ _) (κ ≫ snd _ _)
  rw [lift_comp_fst_snd] at e
  have e' : Units.map (𝒰.f i).appTop.hom.toMonoidHom u = 1 := Units.ext e
  refine gm_inj (U := ⊤) (U' := ⊤) (𝒰.f i) w trivial trivial ?_
  rw [gm_top, e', map_one, map_one]

end GlobalTheory.UU.UnitRigid
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PowEqOneOfInjective
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ThetaSpecialise

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1 GlobalTheory.FieldBaseChange GlobalTheory.ThetaScalar
  GlobalTheory.ThetaBaseChange

section Pull

variable {X X' X'' Y Y' Y'' Y₁ Y₁' : Scheme.{0}} {L : LB X} {L' : LB X'} {L'' : LB X''} {Φ : X' ⟶ X} {Φ' : X'' ⟶ X'}
  {K : Type} [Fintype K] {ε : K → ℤ}

def IsPull {φ₁ : K → (Y₁ ⟶ X)} {φ : K → (Y ⟶ X)} (a : Y₁ ⟶ Y) (t : LB.Sec (LB.LinComb L φ₁ ε))
    (s : LB.Sec (LB.LinComb L φ ε)) : Prop :=
  (∀ κ, φ₁ κ = a ≫ φ κ) ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y₁) (z : Z) (j : K → L.ι), (∀ κ, φ₁ κ (r z) ∈ L.U (j κ)) →
    gs r z (LB.wchart L φ₁ j) (t.f j) = gs (r ≫ a) z (LB.wchart L φ j) (s.f j)

theorem isPull_pullOver {R R' : Type} [CommRing R] [CommRing R'] {φ : K → (Y ⟶ X)}
    {π : Y ⟶ Spec (CommRingCat.of R)} {π' : Y' ⟶ Spec (CommRingCat.of R')}
    {f : R →+* R'} {p : Y' ⟶ Y} (hp : p ≫ π = π' ≫ Spec.map (CommRingCat.ofHom f)) {φ' : K → (Y' ⟶ X)}
    (hφ : ∀ k, φ' k = p ≫ φ k) (s : SecOver π (LB.LinComb L φ ε)) : IsPull p (pullOver L ε hp hφ s) s := by
  unfold IsPull
  exact ⟨hφ, fun _ r z j hj => gs_pullOver hp hφ s r z j hj⟩

variable {φ : K → (Y ⟶ X)} {φ₁ : K → (Y₁ ⟶ X)} {φ₂ : K → (Y₁' ⟶ X)} {a : Y₁ ⟶ Y} {b : Y₁' ⟶ Y₁}
  {s : LB.Sec (LB.LinComb L φ ε)} {t : LB.Sec (LB.LinComb L φ₁ ε)} {v : LB.Sec (LB.LinComb L φ₂ ε)}

theorem IsPull.comp (h₁ : IsPull b v t) (h₂ : IsPull a t s) {c : Y₁' ⟶ Y} (hc : b ≫ a = c) : IsPull c v s := by
  unfold IsPull at h₁ h₂ ⊢
  obtain ⟨h₁φ, h₁g⟩ := h₁
  obtain ⟨h₂φ, h₂g⟩ := h₂
  subst hc
  refine ⟨fun κ => by rw [h₁φ κ, h₂φ κ, Category.assoc], fun Z r z j hj => ?_⟩
  rw [h₁g Z r z j hj, h₂g Z (r ≫ b) z j ?_, Category.assoc]
  intro κ
  have hκ := hj κ
  rw [h₁φ κ, Scheme.Hom.comp_apply] at hκ
  rwa [Scheme.Hom.comp_apply]

theorem IsPull.sval (h : IsPull a t s) {Z : Scheme.{0}} (r : Z ⟶ Y₁) {z : Z} {J} (hJ : Good L z J) :
    sval t r z J = sval s (r ≫ a) z J := by
  unfold IsPull at h
  have hmem : ∀ k, φ₁ k (r z) ∈ L.U (J (r ≫ φ₁ k)) := fun k => by
    simpa only [Scheme.Hom.comp_apply] using hJ (r ≫ φ₁ k)
  rw [sval_of t r z J (fun k => J (r ≫ φ₁ k)) (fun _ => rfl), h.2 Z r z _ hmem]
  exact (sval_of s (r ≫ a) z J _ (fun k => by rw [h.1 k, Category.assoc])).symm

theorem secScal_one_iff (hL : L.IsLB) : GeneratorPullback.SecScal L φ₁ ε t φ ε s a 1 ↔
    ∀ y J, Good L y J → Geo.Tor.sval s (𝟙 Y₁ ≫ a) y J = Geo.Tor.sval t (𝟙 Y₁) y J := by
  have h1 : ∀ y : Y₁, gs (𝟙 Y₁) y ⊤ (1 : Γ(Y₁, ⊤)) = 1 := fun y => by
    rw [gs_eq _ _ _ (by simp), map_one, map_one]
  simp only [secScal_iff_val hL, h1, _root_.one_mul]

theorem eq_pullOver_of_secScal (hL : L.IsLB) {R R' : Type} [CommRing R] [CommRing R']
    {π : Y ⟶ Spec (CommRingCat.of R)} {π' : Y₁ ⟶ Spec (CommRingCat.of R')}
    {f : R →+* R'} (hp : a ≫ π = π' ≫ Spec.map (CommRingCat.ofHom f)) (hφ : ∀ k, φ₁ k = a ≫ φ k)
    (h : GeneratorPullback.SecScal L φ₁ ε t φ ε s a 1) : pullOver L ε hp hφ s = t := by
  apply sec_ext' hL
  intro y J hJ
  rw [sval_pullOver hp hφ s (𝟙 Y₁) hJ]
  exact (secScal_one_iff hL).1 h y J hJ

variable {w : LB.Iso L' (L.pull Φ)} {φ' : K → (Y' ⟶ X')} {s' : LB.Sec (LB.LinComb L' φ' ε)}

theorem psec_iff_of_isPull {h₁ : Y' ⟶ Y₁} (hc : ∀ κ, φ' κ ≫ Φ = h₁ ≫ φ₁ κ) (H : IsPull a t s) {h : Y' ⟶ Y}
    (e : h₁ ≫ a = h) : PSec w φ' φ₁ ε h₁ s' t ↔ PSec w φ' φ ε h s' s := by
  unfold IsPull at H
  subst e
  unfold PSec
  refine forall_congr' fun Z => forall_congr' fun r => forall_congr' fun z => forall_congr' fun p =>
    forall_congr' fun q => imp_congr_right fun hp => imp_congr_right fun _ => ?_
  have hmem : ∀ κ, φ₁ κ ((r ≫ h₁) z) ∈ L.U (p κ) := fun κ => by
    have hκ := congrArg (fun g : Y' ⟶ X => g (r z)) (hc κ)
    simp only [Scheme.Hom.comp_apply] at hκ
    rw [Scheme.Hom.comp_apply, ← hκ]
    exact hp κ
  rw [H.2 Z (r ≫ h₁) z p hmem, Category.assoc]

theorem PSec.pull_left {h : Y' ⟶ Y} (H : PSec w φ' φ ε h s' s) {φ₁' : K → (Y₁' ⟶ X')} {a' : Y₁' ⟶ Y'}
    {t' : LB.Sec (LB.LinComb L' φ₁' ε)} (H' : IsPull a' t' s') : PSec w φ₁' φ ε (a' ≫ h) t' s := by
  unfold IsPull at H'
  unfold PSec at H ⊢
  intro Z r z p q hp hq
  have hp' : ∀ κ, Φ (φ' κ ((r ≫ a') z)) ∈ L.U (p κ) := fun κ => by
    have hκ := hp κ
    rw [H'.1 κ, Scheme.Hom.comp_apply] at hκ
    rwa [Scheme.Hom.comp_apply]
  have hq' : ∀ κ, φ' κ ((r ≫ a') z) ∈ L'.U (q κ) := fun κ => by
    have hκ := hq κ
    rw [H'.1 κ, Scheme.Hom.comp_apply] at hκ
    rwa [Scheme.Hom.comp_apply]
  have e : ∀ κ, r ≫ φ₁' κ = (r ≫ a') ≫ φ' κ := fun κ => by rw [H'.1 κ, Category.assoc]
  have key := H Z (r ≫ a') z p q hp' hq'
  rw [Category.assoc] at key
  rw [H'.2 Z r z q hq, key]
  simp only [e]

theorem PSec.cancel {w' : LB.Iso L'' (L'.pull Φ')} {w'' : LB.Iso L'' (L.pull (Φ' ≫ Φ))} (T : Tri w w' w'')
    (hL : L.IsLB) {φ'' : K → (Y'' ⟶ X'')} {h : Y' ⟶ Y} {h' : Y'' ⟶ Y'} (hc : ∀ k, φ'' k ≫ Φ' = h' ≫ φ' k)
    {s'' : LB.Sec (LB.LinComb L'' φ'' ε)} (H : PSec w φ' φ ε h s' s) (H'' : PSec w'' φ'' φ ε (h' ≫ h) s'' s) :
    PSec w' φ'' φ' ε h' s'' s' := by
  unfold Tri at T
  unfold PSec at H H'' ⊢
  intro Z r z p q hp hq
  obtain ⟨J, hJ, -⟩ := exists_good L hL z (K := Empty) Empty.elim Empty.elim (fun a => a.elim) (fun a => a.elim)
  set P : K → L.ι := fun κ => J (r ≫ φ'' κ ≫ Φ' ≫ Φ)
  have hPmem : ∀ κ, Φ (Φ' (φ'' κ (r z))) ∈ L.U (P κ) := fun κ => by
    simpa only [Scheme.Hom.comp_apply] using hJ (r ≫ φ'' κ ≫ Φ' ≫ Φ)
  have pt : ∀ κ, φ' κ (h' (r z)) = Φ' (φ'' κ (r z)) := fun κ => by
    have hκ := congrArg (fun g : Y'' ⟶ X' => g (r z)) (hc κ)
    simp only [Scheme.Hom.comp_apply] at hκ
    exact hκ.symm
  have hP' : ∀ κ, Φ (φ' κ ((r ≫ h') z)) ∈ L.U (P κ) := fun κ => by
    rw [Scheme.Hom.comp_apply, pt κ]; exact hPmem κ
  have hp' : ∀ κ, φ' κ ((r ≫ h') z) ∈ L'.U (p κ) := fun κ => by
    rw [Scheme.Hom.comp_apply, pt κ]; exact hp κ
  have hP'' : ∀ κ, (Φ' ≫ Φ) (φ'' κ (r z)) ∈ L.U (P κ) := fun κ => by
    rw [Scheme.Hom.comp_apply]; exact hPmem κ
  have e : ∀ κ, (r ≫ φ'' κ) ≫ Φ' = (r ≫ h') ≫ φ' κ := fun κ => by
    rw [Category.assoc, hc κ, Category.assoc]
  have hprod : (∏ κ, gw w'' (r ≫ φ'' κ) z (P κ) (q κ) ^ ε κ) =
      (∏ κ, gw w ((r ≫ h') ≫ φ' κ) z (P κ) (p κ) ^ ε κ) * ∏ κ, gw w' (r ≫ φ'' κ) z (p κ) (q κ) ^ ε κ := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun κ _ => ?_
    have m1 : Φ (Φ' ((r ≫ φ'' κ) z)) ∈ L.U (P κ) := by rw [Scheme.Hom.comp_apply]; exact hPmem κ
    have m2 : Φ' ((r ≫ φ'' κ) z) ∈ L'.U (p κ) := by rw [Scheme.Hom.comp_apply]; exact hp κ
    have m3 : (r ≫ φ'' κ) z ∈ L''.U (q κ) := by rw [Scheme.Hom.comp_apply]; exact hq κ
    rw [← mul_zpow, T Z (r ≫ φ'' κ) z (P κ) (p κ) (q κ) m1 m2 m3, e κ]
  have k1 := H Z (r ≫ h') z P p hP' hp'
  have k2 := H'' Z r z P q hP'' hq
  rw [Category.assoc] at k1
  rw [k1, hprod, Units.val_mul, _root_.mul_assoc] at k2
  exact (Units.mul_right_inj _).1 k2

end Pull

section Side

variable {S₀ S₁ : Scheme.{0}} {G : Over S₀} [GrpObj G] {A : Over S₁} [GrpObj A]
  {f : S₁ ⟶ S₀} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ) {S F : Type} [CommRing S] [CommRing F]
  {t : Spec (CommRingCat.of F) ⟶ S₁} {t₀ : Spec (CommRingCat.of S) ⟶ S₀} (g : S →+* F)
  (hτ : Spec.map (CommRingCat.ofHom g) ≫ t₀ = t ≫ f) {L₀ : LB G.left} {L₁ : LB A.left}


include hp hτ in
theorem exists_side_map (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (w : LB.Iso L₁ (L₀.pull φ)) (hw : w.IsGen) (k : ℤ)
    (x : Over.mk t ⟶ A) (θ₀ : ThetaGrp G L₀ k (Over.mk t₀))
    (hx : Spec.map (CommRingCat.ofHom g) ≫ θ₀.pt.left = x.left ≫ φ)
    (π₀ : (Over.mk t₀ ⊗ G).left ⟶ Spec (CommRingCat.of S)) (hπ₀ : π₀ = (fst (Over.mk t₀) G).left)
    (π : (Over.mk t ⊗ A).left ⟶ Spec (CommRingCat.of F)) (hπ : π = (fst (Over.mk t) A).left) :
    ∃ (θ : ThetaGrp A L₁ k (Over.mk t))
      (mv : SecOver π₀ (LPow G L₀ k (Over.mk t₀)) →ₛₗ[g] SecOver π (LPow A L₁ k (Over.mk t))), θ.pt = x ∧
      (∀ s s', IsActOf G L₀ k θ₀ s s' → IsActOf A L₁ k θ (mv s) (mv s')) ∧
      (∀ (s : LB.Sec (LPow G L₀ k (Over.mk t₀)))
        (σ : LB.Sec (LB.LinComb L₀ (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => k))),
        IsPull (φ₁ := fun _ : Fin 1 => (snd (Over.mk t₀) G).left) (snd (Over.mk t₀) G).left s σ →
        PSec w (fun _ : Fin 1 => (snd (Over.mk t) A).left) (fun _ => 𝟙 G.left) (fun _ => k)
          ((snd (Over.mk t) A).left ≫ φ) (mv s) σ) ∧
      (Flat G.hom → ∀ (n : ℕ) (c : Fin n → F), (∀ a : Fin n → S, ∑ i, g (a i) * c i = 0 → ∀ i, a i = 0) →
        ∀ a : Fin n → SecOver π₀ (LPow G L₀ k (Over.mk t₀)), ∑ i, c i • mv (a i) = 0 → ∀ i, a i = 0) := by
  subst hπ₀ hπ
  obtain ⟨ψ, hψpb, hψsnd, hψeq⟩ := exists_psi hp (T := Over.mk t) (T₀ := Over.mk t₀)
    (Spec.map (CommRingCat.ofHom g)) hτ
  obtain ⟨θ, hθpt, hact⟩ := exists_theta_side hp (T := Over.mk t) (T₀ := Over.mk t₀)
    (Spec.map (CommRingCat.ofHom g)) hτ hL₀ hL₁ w hw k x θ₀ hx hψeq
  obtain ⟨mv, hmv⟩ := exists_moveMap (w := w) (φ' := fun _ : Fin 1 => (snd (Over.mk t) A).left)
    (φ := fun _ : Fin 1 => (snd (Over.mk t₀) G).left) (ε := fun _ => k)
    (π := (fst (Over.mk t₀) G).left) (π' := (fst (Over.mk t) A).left) (fS := g)
    hL₀ hL₁ hw (fun _ => hψsnd.symm) hψpb.w
  refine ⟨θ, mv, hθpt, fun s s' hs => ?_, fun s σ hs => ?_, fun hflat n c hc a e i => ?_⟩
  · exact hact s s' (mv s) (mv s') ((hmv s (mv s)).2 rfl) ((hmv s' (mv s')).2 rfl) hs
  · exact (psec_iff_of_isPull (fun _ => hψsnd.symm) hs hψsnd).1 ((hmv s (mv s)).2 rfl)
  · have := hflat
    have hfl : Flat (fst (Over.mk t₀) G).left := by
      rw [Over.fst_left]
      infer_instance
    exact move_indep hL₀ hL₁ (fun _ => hψsnd.symm) hψpb mv (fun s => (hmv s (mv s)).2 rfl) n c hc a e i

end Side

section Fam

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F]

theorem isPull_famPull (hG : GlobalFnsSt) {k : ℕ} (F₀ : Fam D (FractionRing R) k) (α : D.X) (f : D.SecB k α)
    (h : GeneratorPullback.SecScal D.P.L (DegPre.famφ D (FractionRing R) α) (DegPre.famε k) (F₀.s α) (D.famφB α) (DegPre.famε k) f
      (DegPre.prB D (FractionRing R)).left 1) :
    IsPull (DegPre.prB D F).left ((famPull D (FractionRing R) F hG k F₀).s α) f := by
  have hL : D.P.L.IsLB := D.P.isLB
  have hpZ : (DegPre.prB D (FractionRing R)).left ≫ specZIsTerminal.from _ =
      specZIsTerminal.from _ ≫ Spec.map (CommRingCat.ofHom (RingHom.id ℤ)) :=
    specZIsTerminal.hom_ext _ _
  have hφE : ∀ i, DegPre.famφ D (FractionRing R) α i = (DegPre.prB D (FractionRing R)).left ≫ D.famφB α i :=
    famφ_prB D (FractionRing R) α
  have h₁ : IsPull (DegPre.prB D (FractionRing R)).left (F₀.s α) f := by
    have key := isPull_pullOver (L := D.P.L) (ε := DegPre.famε k) hpZ hφE f
    rwa [eq_pullOver_of_secScal hL hpZ hφE h] at key
  have h₂ := isPull_pullOver (L := D.P.L) (ε := DegPre.famε k) (isPullback_famMap D (FractionRing R) F).w
    (famφ_famMap D (FractionRing R) F α) (F₀.s α)
  have hc : (famMap D (FractionRing R) F).left ≫ (DegPre.prB D (FractionRing R)).left = (DegPre.prB D F).left := by
    rw [← Over.comp_left, famMap_snd]
  exact IsPull.comp h₂ h₁ hc

end Fam

section Points

theorem pow_eq_one_of_injective {S₀ : Scheme.{0}} {G : Over S₀} [GrpObj G] [IsSeparated G.hom] {S F : Type}
    [CommRing S] [IsDomain S] [CommRing F] {g : S →+* F} (hg : Function.Injective g)
    {t₀ : Spec (CommRingCat.of S) ⟶ S₀} {t : Spec (CommRingCat.of F) ⟶ S₀} (ρ : Over.mk t ⟶ Over.mk t₀)
    (hρ : ρ.left = Spec.map (CommRingCat.ofHom g)) (x : Over.mk t₀ ⟶ G) {k : ℕ} (h : (ρ ≫ x) ^ k = 1) :
    x ^ k = 1 := by
  have hdom : IsDominant (Spec.map (CommRingCat.ofHom g)) := by
    rw [isDominant_iff]
    have hd : DenseRange (PrimeSpectrum.comap g) := by
      rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical]
      intro a ha
      rw [RingHom.mem_ker] at ha
      have ha0 : a = 0 := hg (by rw [ha, map_zero])
      rw [ha0]
      exact zero_mem _
    exact hd
  have e : ρ ≫ x ^ k = ρ ≫ 1 := by rw [MonObj.comp_pow, h, MonObj.comp_one]
  have : IsReduced (Over.mk t₀).left := show IsReduced (Spec (CommRingCat.of S)) from inferInstance
  apply Over.OverMorphism.ext
  have e' := congrArg (fun m => m.left) e
  simp only [Over.comp_left, hρ] at e'
  exact ext_of_isDominant_of_isSeparated G.hom (by simp only [Over.w]) (Spec.map (CommRingCat.ofHom g)) e'

end Points

end GlobalTheory.ThetaSpecialise
end
end
