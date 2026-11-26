module

public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsIntegralTensorLeftOfSmoothGrpObj
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpFOfPull

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalEqZeroOfFaithfullyFlatBase
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem levelff_stalkMap_injective {X Y : Scheme.{0}} (f : X ⟶ Y) [Flat f] (x : X) :
    Function.Injective (f.stalkMap x).hom := by
  have h := Flat.stalkMap f x
  have hl : IsLocalHom (f.stalkMap x).hom := inferInstance
  algebraize [(f.stalkMap x).hom]
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) := hl
  have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := Y.presheaf.stalk (f x)) (B := X.presheaf.stalk x)
  exact FaithfulSMul.algebraMap_injective (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)

theorem levelff_gs_comp {X Y Z : Scheme.{0}} (p : Z ⟶ Y) (r : Y ⟶ X) (z : Z) (U : X.Opens) (h : r (p z) ∈ U)
    (a : Γ(X, U)) : gs (p ≫ r) z U a = (p.stalkMap z).hom (gs r (p z) U a) := by
  rw [← gs_pull p r z U h, gs_eq p z (r ⁻¹ᵁ U) h, gs_eq r (p z) U h]
  exact (Scheme.Hom.germ_stalkMap_apply p (r ⁻¹ᵁ U) z h _).symm

theorem sval_eq_zero_of_faithfullyFlat_base : ∀ (R W : Type) [CommRing R] [CommRing W] [Algebra R W] [Module.FaithfullyFlat R W] (I : Ideal R) (e : ℕ) (Y : Over (Spec (CommRingCat.of R))) (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (K : Type) [Fintype K] (φ : K → (Y.left ⟶ X)) (ε : K → ℤ) (d : LB.Sec (LB.LinComb L φ ε)), (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.left) (ω : Z ⟶ Spec (CommRingCat.of W)), ω ≫ Spec.map (CommRingCat.ofHom (algebraMap R W)) = r ≫ Y.hom → (∃ ρ : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))), ρ ≫ thick R I e = r ≫ Y.hom) → ∀ (z : Z) (J), Good L z J → sval d r z J = 0) → ∀ (Z : Scheme.{0}) (r : Z ⟶ Y.left), (∃ ρ : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))), ρ ≫ thick R I e = r ≫ Y.hom) → ∀ (z : Z) (J), Good L z J → sval d r z J = 0 := by
  intro R W _ _ _ _ I e Y X L hL K _ φ ε d H Z r hρ z J hJ
  let g : Spec (CommRingCat.of W) ⟶ Spec (CommRingCat.of R) := Spec.map (CommRingCat.ofHom (algebraMap R W))
  have hg : Flat g ∧ Surjective g := by
    refine (flat_and_surjective_SpecMap_iff _).2 ?_
    exact RingHom.faithfullyFlat_algebraMap_iff.2 inferInstance
  obtain ⟨_, _⟩ := hg
  let p : pullback (r ≫ Y.hom) g ⟶ Z := pullback.fst _ _
  have : Flat p := inferInstance
  have : Surjective p := inferInstance
  obtain ⟨z', rfl⟩ := p.surjective z
  obtain ⟨ρ, hρ⟩ := hρ
  choose J' hJ' using fun χ : pullback (r ≫ Y.hom) g ⟶ X => exists_chart hL (χ z')
  have h0 := H _ (p ≫ r) (pullback.snd _ _) (by rw [Category.assoc]; exact pullback.condition.symm)
    ⟨p ≫ ρ, by rw [Category.assoc, hρ, Category.assoc]⟩ z' J' hJ'
  have hm : r (p z') ∈ LB.wchart L φ (fun k => J (r ≫ φ k)) := hJ.mem φ r
  have h1 := sec_trans d (p ≫ r) z' (j := fun k => J (r ≫ φ k)) hm (Good.mem hJ' φ (p ≫ r))
  have h2 : gs (p ≫ r) z' (LB.wchart L φ (fun k => J (r ≫ φ k))) (d.f (fun k => J (r ≫ φ k))) = 0 :=
    h1.trans ((congrArg _ h0).trans (mul_zero _))
  apply levelff_stalkMap_injective p z'
  rw [map_zero]
  exact (levelff_gs_comp p r z' _ hm _).symm.trans h2

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFiniteExtensionPrimitiveResidue
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem isPrimitiveRoot_residue_of_isUnit {W : Type*} [CommRing W] [IsDomain W] [IsLocalRing W]
    {ζ : W} {N : ℕ} (hζ : IsPrimitiveRoot ζ N) (hN : IsUnit (N : W)) :
    IsPrimitiveRoot (IsLocalRing.residue W ζ) N := by
  refine ⟨by rw [← map_pow, hζ.pow_eq_one, map_one], fun l hl => hζ.dvd_of_pow_eq_one l ?_⟩
  by_contra hne
  have h1 : (ζ ^ l) ^ N = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have h2 : ∑ i ∈ Finset.range N, (ζ ^ l) ^ i = 0 := by
    have := geom_sum_mul (ζ ^ l) N
    rw [h1, sub_self] at this
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hne)
  have h3 := congrArg (IsLocalRing.residue W) h2
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_pow, hl, one_pow, map_zero, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one] at h3
  have h4 := hN.map (IsLocalRing.residue W)
  rw [map_natCast] at h4
  exact h4.ne_zero (by simpa using h3)

theorem exists_finite_extension_primitive_residue :
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [CharZero V], (∃ n : ℕ, n.Prime ∧ IsUnit (n : V)) ∧ ∀ (n j : ℕ), n.Prime → IsUnit (n : V) → ∃ (W : Type) (_ : CommRing W) (_ : IsLocalRing W) (_ : Algebra V W) (φ : TF (R := V) (AlgebraicClosure (FractionRing V)) ⟶ Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W)))) (ζ : W), (Module.Finite V W ∧ Module.Free V W ∧ IsDomain W ∧ IsLocalHom (algebraMap V W) ∧ IsAdicComplete ((IsLocalRing.maximalIdeal V).map (algebraMap V W)) W) ∧ Function.Injective φ.left.appTop.hom ∧ IsUnit (n : W) ∧ ζ ^ (n ^ j) = 1 ∧ IsPrimitiveRoot (IsLocalRing.residue W ζ) (n ^ j) := by
  intro V _ _ _ _ _
  refine ⟨?_, fun n j hn hu => ?_⟩
  · have h : IsUnit ((3 : V) + -2) := by norm_num
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add h with h | h
    · exact ⟨3, Nat.prime_three, by exact_mod_cast h⟩
    · exact ⟨2, Nat.prime_two, by exact_mod_cast (IsUnit.neg_iff _).1 h⟩
  · let F := AlgebraicClosure (FractionRing V)
    have hpos : 0 < n ^ j := pow_pos hn.pos j
    have : NeZero (n ^ j) := ⟨hpos.ne'⟩
    have : NeZero ((n ^ j : ℕ) : F) := inferInstance
    obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot F (n ^ j)
    let W : Subalgebra V F := Algebra.adjoin V {z}
    have hzW : z ∈ W := Algebra.subset_adjoin rfl
    have hfin : Module.Finite V W :=
      Algebra.finite_adjoin_simple_of_isIntegral
        ⟨Polynomial.X ^ (n ^ j) - Polynomial.C 1, Polynomial.monic_X_pow_sub_C _ hpos.ne', by
          simp [hz.pow_eq_one]⟩
    have : FaithfulSMul V W := (faithfulSMul_iff_algebraMap_injective V W).2 fun x y h =>
      IsFractionRing.injective V (FractionRing V) ((algebraMap (FractionRing V) F).injective
        (congrArg Subtype.val h))
    have hfree : Module.Free V W := Module.free_of_finite_type_torsion_free'
    have hW : IsLocalRing W := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isLocalRing_finite_domain (R := V) W
    have hloc : IsLocalHom (algebraMap V W) := inferInstance
    have hc := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isAdicComplete_finite_algebra (R := V) W
    have hζ : IsPrimitiveRoot (⟨z, hzW⟩ : W) (n ^ j) :=
      IsPrimitiveRoot.of_map_of_injective (f := W.val) hz Subtype.val_injective
    have hnW : IsUnit (n : W) := by simpa using hu.map (algebraMap V W)
    refine ⟨W, inferInstance, inferInstance, inferInstance,
      Over.homMk (Spec.map (CommRingCat.ofHom W.val.toRingHom)) ?_, ⟨z, hzW⟩,
      ⟨hfin, hfree, inferInstance, hloc, hc⟩, ?_, hnW, hζ.pow_eq_one,
      isPrimitiveRoot_residue_of_isUnit hζ (by exact_mod_cast hnW.pow j)⟩
    · change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← Spec.map_comp]
      rfl
    · change Function.Injective (Spec.map (CommRingCat.ofHom W.val.toRingHom)).appTop.hom
      have h := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom W.val.toRingHom)
      have hi : Function.Injective ((Spec.map (CommRingCat.ofHom W.val.toRingHom)).appTop ≫
          (Scheme.ΓSpecIso _).hom).hom := by
        rw [h, CommRingCat.hom_comp, RingHom.coe_comp]
        exact Subtype.val_injective.comp (Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv.injective
      rw [CommRingCat.hom_comp, RingHom.coe_comp] at hi
      exact hi.of_comp

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CoeffEqZeroOfSumSmulEqZeroOfSeparating
namespace GlobalTheory

theorem coeff_eq_zero_of_sum_smul_eq_zero_of_separating {Y A M : Type*} [CommRing A]
    [AddCommGroup M] [Module A M] (P : (Y → A) → Prop) (h1 : P 1)
    (hmul : ∀ t t', P t → P t' → P (t * t')) (s : Finset Y)
    (hsep : ∀ y ∈ s, ∀ z ∈ s, y ≠ z → ∃ t, P t ∧ IsUnit (t y - t z))
    (a : Y → M) (h : ∀ t, P t → ∑ y ∈ s, t y • a y = 0) : ∀ y ∈ s, a y = 0 := by
  classical
  induction s using Finset.strongInduction generalizing a with
  | H s ih =>
    intro y₀ hy₀
    by_cases hz : ∃ z ∈ s, z ≠ y₀
    · obtain ⟨z, hzs, hzy⟩ := hz
      obtain ⟨u, hu, hunit⟩ := hsep y₀ hy₀ z hzs (Ne.symm hzy)

      set b : Y → M := fun y => (u y - u z) • a y with hb
      have hbrel : ∀ t, P t → ∑ y ∈ s.erase z, t y • b y = 0 := by
        intro t ht
        rw [Finset.sum_erase s (by simp [hb])]
        have e : ∀ y, t y • b y = (t * u) y • a y - u z • (t y • a y) := by
          intro y
          simp only [hb, Pi.mul_apply, smul_smul, ← sub_smul]
          congr 1
          ring
        simp only [e, Finset.sum_sub_distrib, ← Finset.smul_sum, h t ht, h (t * u) (hmul t u ht hu),
          smul_zero, sub_zero]
      have hsub : s.erase z ⊂ s := Finset.erase_ssubset hzs
      have key := ih (s.erase z) hsub
        (fun y hy w hw hne => hsep y (Finset.mem_of_mem_erase hy) w (Finset.mem_of_mem_erase hw) hne)
        b hbrel y₀ (Finset.mem_erase.mpr ⟨Ne.symm hzy, hy₀⟩)
      exact (hunit.smul_eq_zero).mp key
    · push Not at hz
      have := h 1 h1
      rw [Finset.sum_eq_single_of_mem y₀ hy₀ (fun z hz' hne => absurd (hz z hz') hne)] at this
      simpa using this

theorem laurent_coeff_eq_zero_of_vanish_torsion :
    ∀ (Y : Type) [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y] (n : ℕ), n.Prime →
    ∀ s : Finset Y, ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (A : Type) [CommRing A] [IsLocalRing A] (ζ : A),
    IsUnit (n : A) → ζ ^ (n ^ j) = 1 → IsPrimitiveRoot (IsLocalRing.residue A ζ) (n ^ j) →
    ∀ (M : Type) [AddCommGroup M] [Module A M] (a : Y → M),
    (∀ t : Multiplicative Y →* Aˣ, (∀ y, t y ^ (n ^ j) = 1) →
      ∑ y ∈ s, (t (Multiplicative.ofAdd y) : A) • a y = 0) → ∀ y ∈ s, a y = 0 := by
  intro Y _ _ _ n hn s
  let b := Module.Free.chooseBasis ℤ Y

  refine ⟨∑ p ∈ s ×ˢ s, ∑ i, (b.repr (p.1 - p.2) i).natAbs, ?_⟩
  intro j hj A _ _ ζ _ hζ hprim M _ _ a ha
  have hN : n ^ j ≠ 0 := pow_ne_zero _ hn.ne_zero
  let u : Aˣ := Units.ofPowEqOne ζ (n ^ j) hζ hN
  have hu : u ^ (n ^ j) = 1 := Units.pow_ofPowEqOne hζ hN

  let χ : _ → Multiplicative Y →* Aˣ := fun i =>
    (zpowersHom Aˣ u).comp (AddMonoidHom.toMultiplicative (b.coord i).toAddMonoidHom)
  have hχ : ∀ i y, χ i (Multiplicative.ofAdd y) = u ^ (b.repr y i) := by
    intro i y
    simp [χ, zpowersHom]
  have hχord : ∀ i y, χ i y ^ (n ^ j) = 1 := by
    intro i y
    rw [show y = Multiplicative.ofAdd (Multiplicative.toAdd y) from rfl, hχ, ← zpow_natCast,
      ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu, one_zpow]
  let P : (Y → A) → Prop := fun f =>
    ∃ t : Multiplicative Y →* Aˣ, (∀ y, t y ^ (n ^ j) = 1) ∧ f = fun y => (t (Multiplicative.ofAdd y) : A)
  refine coeff_eq_zero_of_sum_smul_eq_zero_of_separating P ⟨1, fun _ => one_pow _, by funext; simp⟩
    ?_ s ?_ a ?_
  · rintro _ _ ⟨t, ht, rfl⟩ ⟨t', ht', rfl⟩
    exact ⟨t * t', fun y => by rw [MonoidHom.mul_apply, mul_pow, ht, ht', one_mul],
      by funext y; simp⟩
  · intro y hy z hz hyz
    have hw : b.repr (y - z) ≠ 0 := by
      rw [Ne, LinearEquiv.map_eq_zero_iff]
      exact sub_ne_zero.mpr hyz
    obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hw
    simp only [Finsupp.coe_zero, Pi.zero_apply] at hi
    refine ⟨_, ⟨χ i, hχord i, rfl⟩, ?_⟩
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, hχ, hχ, map_sub]
    let v : (IsLocalRing.ResidueField A)ˣ := Units.map (IsLocalRing.residue A).toMonoidHom u
    have hv : IsPrimitiveRoot v (n ^ j) := IsPrimitiveRoot.coe_units_iff.mp (by simpa [v, u] using hprim)
    have hres : ∀ k : ℤ, IsLocalRing.residue A ((u ^ k : Aˣ) : A) = ((v ^ k : _ˣ) : _) := by
      intro k
      rw [show v ^ k = Units.map (IsLocalRing.residue A).toMonoidHom (u ^ k) from (map_zpow _ u k).symm]
      rfl
    rw [hres, hres, sub_ne_zero, Ne, Units.val_inj, ← div_eq_one, div_eq_mul_inv, ← zpow_sub, ← Finsupp.sub_apply,
      ← map_sub, hv.zpow_eq_one_iff_dvd]
    intro hdvd
    apply hi
    apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd
    have h1 : (b.repr (y - z) i).natAbs ≤ ∑ p ∈ s ×ˢ s, ∑ i, (b.repr (p.1 - p.2) i).natAbs := by
      refine le_trans ?_ (Finset.single_le_sum (f := fun p : Y × Y => ∑ i, (b.repr (p.1 - p.2) i).natAbs)
        (fun _ _ => Nat.zero_le _) (show (y, z) ∈ s ×ˢ s from Finset.mem_product.mpr ⟨hy, hz⟩))
      exact Finset.single_le_sum (f := fun i => (b.repr (y - z) i).natAbs) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i)
    have h2 : j < n ^ j := Nat.lt_pow_self hn.one_lt
    simp only [Int.natAbs_natCast]
    omega
  · rintro _ ⟨t, ht, rfl⟩
    exact ha t ht

end GlobalTheory
end

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU.TwistNonvan

theorem sval_scale {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (c : Γ(Y, ⊤)) (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval (DVR.SecOps.secScale c s) r z J = gs r z ⊤ c * sval s r z J :=
  (gs_mul r z _ (hJ.mem _ r) _ _).trans (congrArg₂ (· * ·) (gs_res r z le_top (hJ.mem _ r) _) rfl)

theorem sval_zero {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (hs : ∀ j, s.f j = 0) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) : sval s r z J = 0 := by
  refine (congrArg (gs r z _) (hs _)).trans ((gs_eq r z _ (hJ.mem φ r) _).trans ?_)
  exact (congrArg _ (map_zero _)).trans (map_zero _)

theorem exists_constHom {W : Type} [CommRing W] {Y Z : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of W)) (r : Z ⟶ Y)
    (z : Z) : ∃ c : W →+* Z.presheaf.stalk z, ∀ w, gs r z ⊤ (scal p w) = c w :=
  ⟨((Z.presheaf.germ (r ⁻¹ᵁ ⊤) z trivial).hom.comp (r.app ⊤).hom).comp
    (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom), fun w => gs_eq r z ⊤ trivial _⟩

theorem sum_eq_zero {V : Type} [CommRing V] [IsDomain V] (I : Ideal V) (D : DegPre V) (k : ℕ) (α : D.X)
    {W : Type} [CommRing W] [Algebra V W] (a : Multiplicative D.X →* Wˣ)
    (f' : ∀ α, SecBT D (TA V W) k α) (g' : ∀ α, SecBT D (TA V W) 1 α) (h : ∀ α, SecBT D (TA V W) (k + 1) α)
    (hc : ConvT I (twist a f') (twist (a ^ k)⁻¹ g') h) (h0 : ∀ j, (h α).f j = 0) (e : ℕ)
    (Z : Over (Spec (CommRingCat.of V))) (r : Z ⟶ TA V W ⊗ D.P.A) (hl : Lvl I e Z.hom) (z : Z.left) (J)
    (hJ : Good D.P.L z J) (s : Finset D.X) (hs : ∀ β ∉ s, sval (f' β) r.left z J = 0)
    (c : W →+* Z.left.presheaf.stalk z) (hcw : ∀ w, gs r.left z ⊤ (scal (R := W) (fst (TA V W) D.P.A).left w) = c w) :
    ∑ β ∈ s, c (a (Multiplicative.ofAdd ((k + 1) • β - k • α))).val * (sval (f' β) r.left z J *
      sval (g' (α - β)) r.left z J *
      (cubV D.cub z J (toUnit Z ≫ D.c β) (toUnit Z ≫ D.c (α - β)) (r ≫ snd _ D.P.A)).val) = 0 := by
  classical
  obtain ⟨p, hp, hsum⟩ := hc α
  obtain ⟨s', hs'⟩ := hsum e
  obtain ⟨h₁, h₂⟩ := hs' Z.left r.left (by rw [Over.w r]; exact hl) z J hJ
  have hT : ∀ β, sval (p β) r.left z J = c (a (Multiplicative.ofAdd ((k + 1) • β - k • α))).val *
      (sval (f' β) r.left z J * sval (g' (α - β)) r.left z J *
      (cubV D.cub z J (toUnit Z ≫ D.c β) (toUnit Z ≫ D.c (α - β)) (r ≫ snd _ D.P.A)).val) := fun β => by
    have e₁ : a (Multiplicative.ofAdd ((k + 1) • β - k • α)) =
        a (Multiplicative.ofAdd β) * (a ^ k)⁻¹ (Multiplicative.ofAdd (α - β)) := by
      rw [MonoidHom.inv_apply, MonoidHom.pow_apply, ← map_pow, ← map_inv, ← map_mul]
      congr 1
      rw [← ofAdd_nsmul, ← ofAdd_neg, ← ofAdd_add]
      congr 1
      module
    rw [hp β Z r z J hJ, e₁, Units.val_mul, map_mul]
    unfold twist
    rw [sval_scale _ _ _ z hJ, sval_scale _ _ _ z hJ, hcw, hcw]
    ring
  rw [sval_zero _ h0 _ z hJ] at h₂
  rw [← Finset.sum_congr rfl (fun β _ => hT β)]
  rw [Finset.sum_subset (Finset.subset_union_left (s₂ := s')) (fun β _ hβ => by rw [hT β, hs β hβ]; ring),
    ← Finset.sum_subset (Finset.subset_union_right (s₁ := s)) (fun β _ hβ => h₁ β hβ)]
  exact h₂.symm

theorem exists_level {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] [IsNoetherianRing V] (D : DegPre V)
    {k l m : ℕ} {β ga α : D.X} (f : SecBT D (𝟙_ _) k β) (g : SecBT D (𝟙_ _) l ga) (p : SecBT D (𝟙_ _) m α)
    (hp : IsProdB f g p) (hf : ∃ j, f.f j ≠ 0) (hg : ∃ j, g.f j ≠ 0) :
    ∃ e : ℕ, ¬ ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ _ ⊗ D.P.A).left),
      Lvl (IsLocalRing.maximalIdeal V) e (r ≫ (𝟙_ _ ⊗ D.P.A).hom) → ∀ (z : Z) (J), Good D.P.L z J →
        sval p r z J = 0 := by
  have := D.P.isAb.smooth
  have := D.P.isAb.geomConnected
  have : IsIntegral (𝟙_ (Over (Spec (CommRingCat.of V)))).left :=
    (inferInstance : IsIntegral (Spec (CommRingCat.of V)))
  have : IsAffine (𝟙_ (Over (Spec (CommRingCat.of V)))).left :=
    (inferInstance : IsAffine (Spec (CommRingCat.of V)))
  let i : V ≃+* Γ((𝟙_ (Over (Spec (CommRingCat.of V)))).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of V)).symm.commRingCatIsoToRingEquiv
  have : IsNoetherianRing Γ((𝟙_ (Over (Spec (CommRingCat.of V)))).left, ⊤) := isNoetherianRing_of_ringEquiv V i
  have := GlobalTheory.isIntegral_tensor_left_of_smooth_grpObj _ D.P.A (𝟙_ _)
  obtain ⟨j, hj⟩ := GlobalTheory.exists_ne_zero_of_sval_eq_mul_unit _ _ D.P.L D.P.isLB _ _ _ _ _ _ _ _ _ f g p
    (fun y J hJ => ⟨_, hp (𝟙_ _ ⊗ D.P.A) (𝟙 _) y J hJ⟩) hf hg
  by_contra hne
  refine hj (GlobalTheory.sec_eq_zero_of_sval_finite_level V (IsLocalRing.maximalIdeal V) (𝟙_ _) D.P.A (fun r hr => ?_) _ D.P.L
    D.P.isLB _ _ _ p (fun e => by
      by_contra h
      exact hne ⟨e, h⟩) j)
  have e : scal (𝟙_ (Over (Spec (CommRingCat.of V)))).hom r = i r := rfl
  rw [e, Ideal.mem_jacobson_bot]
  intro y
  obtain ⟨y, rfl⟩ := i.surjective y
  rw [← IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, Ideal.mem_jacobson_bot] at hr
  have := (hr y).map i
  rwa [map_add, map_mul, map_one] at this

end GlobalTheory.UU.TwistNonvan

namespace GlobalTheory.UU
open TwistNonvan

theorem exists_twist_conv_ne_zero : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDVR V → ∀ (D : DegPre V) (k : ℕ) (f : ∀ α, SecBT D (𝟙_ _) k α) (g : ∀ α, SecBT D (𝟙_ _) 1 α) (α β₀ : D.X), NullFam (IsLocalRing.maximalIdeal V) f → (∃ j, (f β₀).f j ≠ 0) → (∃ j, (g (α - β₀)).f j ≠ 0) → ∃ (W : Type) (_ : CommRing W) (_ : IsLocalRing W) (_ : Algebra V W) (φ : TF (R := V) (Kbar V) ⟶ TA V W) (a : Multiplicative D.X →* Wˣ), FinExt V W ∧ Function.Injective φ.left.appTop.hom ∧ ∀ (f' : ∀ α, SecBT D (TA V W) k α) (g' : ∀ α, SecBT D (TA V W) 1 α) (h : ∀ α, SecBT D (TA V W) (k + 1) α), PullT (toUnit _) f f' → PullT (toUnit _) g g' → ConvT (IsLocalRing.maximalIdeal V) (twist a f') (twist (a ^ k)⁻¹ g') h → ∃ j, (h α).f j ≠ 0 := by
  intro V _ _ _ hV D k f g α β₀ hnull hf hg
  classical
  obtain ⟨hd, hcpl, hch⟩ := hV
  obtain ⟨p, hp⟩ := exists_isProdB V D (𝟙_ _) k 1 β₀ (α - β₀) α (by abel) (f β₀) (g (α - β₀))
  obtain ⟨e, he⟩ := exists_level D _ _ p hp hf hg
  obtain ⟨s₀, hs₀⟩ := hnull e
  obtain ⟨⟨n, hn, hnu⟩, hcyc⟩ := GlobalTheory.exists_finite_extension_primitive_residue V
  let u : D.X → D.X := fun β => (k + 1) • β - k • α
  have hu : Function.Injective u := fun x y hxy => by
    have h₁ : ((k + 1 : ℕ) : ℤ) • x = ((k + 1 : ℕ) : ℤ) • y := by
      rw [natCast_zsmul, natCast_zsmul]; exact sub_left_injective hxy
    exact smul_right_injective D.X (by positivity) h₁
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.laurent_coeff_eq_zero_of_vanish_torsion D.X n hn ((insert β₀ s₀).image u)
  obtain ⟨W, iW, iL, iA, φ, ζ, hW, hφ, hnW, hζ, hprim⟩ := hcyc n j₀ hn hnu
  by_contra hne
  have H : ∀ a : Multiplicative D.X →* Wˣ, ∃ (f' : ∀ α, SecBT D (TA V W) k α) (g' : ∀ α, SecBT D (TA V W) 1 α)
      (h : ∀ α, SecBT D (TA V W) (k + 1) α), PullT (toUnit _) f f' ∧ PullT (toUnit _) g g' ∧
      ConvT (IsLocalRing.maximalIdeal V) (twist a f') (twist (a ^ k)⁻¹ g') h ∧ ∀ j, (h α).f j = 0 := fun a => by
    by_contra hh
    refine hne ⟨W, iW, iL, iA, φ, a, hW, hφ, fun f' g' h h₁ h₂ h₃ => ?_⟩
    by_contra h₄
    exact hh ⟨f', g', h, h₁, h₂, h₃, fun j => by_contra fun h₅ => h₄ ⟨j, h₅⟩⟩
  obtain ⟨hfin, hfree, hdom, -, -⟩ := hW
  refine he (GlobalTheory.sval_eq_zero_of_faithfullyFlat_base V W (IsLocalRing.maximalIdeal V) e (𝟙_ _ ⊗ D.P.A) _ D.P.L
    D.P.isLB _ _ _ p ?_)
  intro Z r ω hω hl z J hJ
  let Z' : Over (Spec (CommRingCat.of V)) := Over.mk (r ≫ (𝟙_ _ ⊗ D.P.A).hom)
  let rr : Z' ⟶ 𝟙_ _ ⊗ D.P.A := Over.homMk r rfl
  let ωω : Z' ⟶ TA V W := Over.homMk ω hω
  let r' : Z' ⟶ TA V W ⊗ D.P.A := lift ωω (rr ≫ snd _ _)
  have e₁ : r' ≫ toUnit _ ▷ D.P.A = rr := by
    apply CartesianMonoidalCategory.hom_ext
    · exact toUnit_unique _ _
    · simp [r']
  have e₂ : r'.left ≫ (toUnit (TA V W) ▷ D.P.A).left = rr.left := congrArg (fun q => q.left) e₁
  have e₃ : r' ≫ snd _ _ = rr ≫ snd _ _ := lift_snd _ _
  obtain ⟨c, hc⟩ := exists_constHom (W := W) (fst (TA V W) D.P.A).left r'.left z
  let T : D.X → Z'.left.presheaf.stalk z := fun β => sval (f β) rr.left z J * sval (g (α - β)) rr.left z J *
      (cubV D.cub (T := Z') z J (toUnit Z' ≫ D.c β) (toUnit Z' ≫ D.c (α - β)) (rr ≫ snd _ D.P.A)).val
  have e₄ : sval p rr.left z J = T β₀ := hp Z' rr z J hJ
  letI : Module W (Z'.left.presheaf.stalk z) := Module.compHom _ c
  have key := hj₀ j₀ le_rfl W ζ hnW hζ hprim (Z'.left.presheaf.stalk z) (Function.extend u T 0) (fun a _ => by
    obtain ⟨f', g', h, h₁, h₂, h₃, h₄⟩ := H a
    have v₁ : ∀ β, sval (f' β) r'.left z J = sval (f β) rr.left z J := fun β =>
      (h₁ β _ r'.left z J hJ).trans (by rw [e₂])
    have v₂ : ∀ β, sval (g' β) r'.left z J = sval (g β) rr.left z J := fun β =>
      (h₂ β _ r'.left z J hJ).trans (by rw [e₂])
    have := sum_eq_zero _ D k α a f' g' h h₃ h₄ e Z' r' hl z J hJ (insert β₀ s₀) (fun β hβ =>
      (v₁ β).trans (hs₀ β (fun hb => hβ (Finset.mem_insert_of_mem hb)) Z r hl z J hJ)) c hc
    rw [Finset.sum_image (fun x _ y _ hxy => hu hxy)]
    refine Eq.trans (Finset.sum_congr rfl fun β _ => ?_) this
    rw [hu.extend_apply, v₁, v₂, e₃]
    rfl) (u β₀) (Finset.mem_image_of_mem _ (Finset.mem_insert_self _ _))
  rw [hu.extend_apply] at key
  exact e₄.trans key

end GlobalTheory.UU
