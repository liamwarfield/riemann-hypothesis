module

public import GroundTheory.ProfiniteCohomology.FilteredHomology

@[expose] public section

section -- merged from GroundTheory.ProfiniteCohomology.Factor
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open Filter Topology

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

theorem exists_openNormalSubgroup_pi_of_isLocallyConstant {ι X : Type*} [Finite ι]
    {f : (ι → G) → X} (hf : IsLocallyConstant f) :
    ∃ U : OpenNormalSubgroup G, ∀ x y : ι → G, (∀ i, (x i)⁻¹ * y i ∈ U) → f x = f y := by

  let O : OpenNormalSubgroup G → Set (ι → G) := fun U =>
    {y | ∀ y' : ι → G, (∀ i, (y i)⁻¹ * y' i ∈ U) → f y' = f y}
  have hO : ∀ U, IsOpen (O U) := by
    intro U
    rw [isOpen_iff_mem_nhds]
    intro y hy
    have hopen : IsOpen ((fun w : ι → G => fun i => (y i)⁻¹ * w i) ⁻¹'
        Set.univ.pi fun _ => (U : Set G)) :=
      (isOpen_set_pi Set.finite_univ fun _ _ => U.toOpenSubgroup.isOpen).preimage
        (continuous_pi fun i => continuous_const.mul (continuous_apply i))
    refine mem_of_superset (hopen.mem_nhds fun i _ => by simp) ?_
    intro w hw y' hy'
    have hw' : ∀ i, (y i)⁻¹ * w i ∈ U := fun i => hw i (Set.mem_univ i)
    have h1 : f y' = f y := hy y' fun i => by
      have := mul_mem (hw' i) (hy' i)
      rwa [mul_assoc, mul_inv_cancel_left] at this
    rw [h1, hy w hw']
  have hcover : Set.univ ⊆ ⋃ U, O U := by
    intro x _
    have hS : (fun w : ι → G => fun i => x i * w i) ⁻¹' (f ⁻¹' {f x}) ∈ 𝓝 (1 : ι → G) :=
      ((hf.isOpen_fiber (f x)).preimage
        (continuous_pi fun i => continuous_const.mul (continuous_apply i))).mem_nhds
        (by simp)
    obtain ⟨U, -, hU⟩ := (OpenNormalSubgroup.hasBasis_nhds_one_pi ι).mem_iff.mp hS
    refine Set.mem_iUnion.mpr ⟨U, fun y' hy' => ?_⟩
    have := hU (show (fun i => (x i)⁻¹ * y' i) ∈ Set.univ.pi fun _ => (U : Set G) from
      fun i _ => hy' i)
    simpa using this
  have hdir : Directed (· ⊆ ·) O := fun U V =>
    ⟨U ⊓ V, fun y hy y' hy' => hy y' fun i => (hy' i).1,
      fun y hy y' hy' => hy y' fun i => (hy' i).2⟩
  obtain ⟨U, hU⟩ := isCompact_univ.elim_directed_cover O hO hcover hdir
  exact ⟨U, fun x y hxy => (hU (Set.mem_univ x) y hxy).symm⟩

theorem exists_openNormalSubgroup_factor_of_isLocallyConstant {ι X : Type*} [Finite ι]
    {f : (ι → G) → X} (hf : IsLocallyConstant f) :
    ∃ (U : OpenNormalSubgroup G) (g : (ι → G ⧸ (U : Subgroup G)) → X),
      f = g ∘ fun x i => (x i : G ⧸ (U : Subgroup G)) := by
  obtain ⟨U, hU⟩ := exists_openNormalSubgroup_pi_of_isLocallyConstant hf
  refine ⟨U, fun q => f fun i => (q i).out, funext fun x => hU _ _ fun i => ?_⟩
  exact QuotientGroup.eq.mp (QuotientGroup.out_eq' (x i : G ⧸ (U : Subgroup G))).symm

theorem exists_openNormalSubgroup_fin_of_isLocallyConstant {n : ℕ} {X : Type*}
    {f : (Fin n → G) → X} (hf : IsLocallyConstant f) :
    ∃ U : OpenNormalSubgroup G, ∀ x y : Fin n → G, (∀ i, (x i)⁻¹ * y i ∈ U) → f x = f y :=
  exists_openNormalSubgroup_pi_of_isLocallyConstant hf

theorem exists_openNormalSubgroup_factor_fin_of_isLocallyConstant {n : ℕ} {X : Type*}
    {f : (Fin n → G) → X} (hf : IsLocallyConstant f) :
    ∃ (U : OpenNormalSubgroup G) (g : (Fin n → G ⧸ (U : Subgroup G)) → X),
      f = g ∘ fun x i => (x i : G ⧸ (U : Subgroup G)) :=
  exists_openNormalSubgroup_factor_of_isLocallyConstant hf

end GroundTheory.ProfCoh
end

section -- merged from GroundTheory.ProfiniteCohomology.OfNatRelIndexSupAntitone
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open Topology

variable {G : Type*} [Group G]

theorem inf_sup_normal_eq {X H U : Subgroup G} [U.Normal] (hUX : U ≤ X) :
    X ⊓ (H ⊔ U) = (X ⊓ H) ⊔ U := by
  refine le_antisymm (fun x hx => ?_) (sup_le (inf_le_inf_left _ le_sup_left) (le_inf hUX le_sup_right))
  obtain ⟨hxX, hxHU⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨h, hh, u, hu, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hxHU
  have hhX : h ∈ X := by
    have := X.mul_mem hxX (X.inv_mem (hUX hu))
    rwa [mul_inv_cancel_right] at this
  exact Subgroup.mul_mem_sup (Subgroup.mem_inf.mpr ⟨hhX, hh⟩) hu

theorem relIndex_sup_normal_eq {X H U : Subgroup G} [U.Normal] [U.FiniteIndex] (hUX : U ≤ X) :
    X.relIndex (H ⊔ U) = X.relIndex H := by
  have h1 := Subgroup.relIndex_inf_mul_relIndex U X (H ⊔ U)
  have h2 := Subgroup.relIndex_inf_mul_relIndex U X H
  rw [inf_eq_left.mpr hUX, Subgroup.relIndex_sup_right, inf_sup_normal_eq hUX,
    Subgroup.relIndex_sup_right] at h1
  rw [inf_eq_left.mpr hUX] at h2
  have hne : U.relIndex (X ⊓ H) ≠ 0 := fun h0 =>
    Subgroup.FiniteIndex.index_ne_zero (H := U)
      (Nat.eq_zero_of_zero_dvd (h0 ▸ Subgroup.relIndex_dvd_index_of_normal U (X ⊓ H)))
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne) (h1.trans h2.symm)

theorem index_sup_normal_eq_mul {K H U : Subgroup G} [U.Normal] [U.FiniteIndex] (hKH : K ≤ H) :
    (K ⊔ U).index = (H ⊔ U).index * (K ⊔ U).relIndex H := by
  rw [← Subgroup.relIndex_mul_index (sup_le_sup_right hKH U),
    relIndex_sup_normal_eq (le_sup_right : U ≤ K ⊔ U), mul_comm]

theorem sup_subgroupOf_eq {K H U : Subgroup G} [U.Normal] (hKH : K ≤ H) :
    (K ⊔ U).subgroupOf H = K.subgroupOf H ⊔ U.subgroupOf H := by
  refine le_antisymm (fun x hx => ?_)
    (sup_le (fun x hx => Subgroup.mem_subgroupOf.mpr ((le_sup_left : K ≤ K ⊔ U) (Subgroup.mem_subgroupOf.mp hx)))
      (fun x hx => Subgroup.mem_subgroupOf.mpr ((le_sup_right : U ≤ K ⊔ U) (Subgroup.mem_subgroupOf.mp hx))))
  rw [Subgroup.mem_subgroupOf] at hx
  obtain ⟨k, hk, u, hu, hku⟩ := Subgroup.mem_sup_of_normal_right.mp hx
  have hkH : k ∈ H := hKH hk
  have huH : u ∈ H := by
    have := H.mul_mem (H.inv_mem hkH) x.2
    rwa [← hku, inv_mul_cancel_left] at this
  have hx' : x = ⟨k, hkH⟩ * ⟨u, huH⟩ := Subtype.ext hku.symm
  rw [hx']
  exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mpr hk) (Subgroup.mem_subgroupOf.mpr hu)

variable [TopologicalSpace G]

noncomputable def superIndex (H : Subgroup G) : Supernatural :=
  ⨆ U : OpenNormalSubgroup G, Supernatural.ofNat (H ⊔ (U : Subgroup G)).index

noncomputable def superRelIndex (K H : Subgroup G) : Supernatural :=
  superIndex (K.subgroupOf H)

variable [IsTopologicalGroup G] [CompactSpace G]

instance OpenNormalSubgroup.finiteIndex (U : OpenNormalSubgroup G) :
    (U : Subgroup G).FiniteIndex :=
  Subgroup.finiteIndex_of_finite_quotient

theorem index_sup_ne_zero (H : Subgroup G) (U : OpenNormalSubgroup G) :
    (H ⊔ (U : Subgroup G)).index ≠ 0 :=
  fun h => Subgroup.FiniteIndex.index_ne_zero (H := (U : Subgroup G))
    (Nat.eq_zero_of_zero_dvd (h ▸ Subgroup.index_dvd_of_le le_sup_right))

theorem relIndex_sup_ne_zero (K H : Subgroup G) (U : OpenNormalSubgroup G) :
    (K ⊔ (U : Subgroup G)).relIndex H ≠ 0 :=
  fun h => Subgroup.FiniteIndex.index_ne_zero (H := (U : Subgroup G))
    (Nat.eq_zero_of_zero_dvd (h ▸ (Subgroup.relIndex_dvd_of_le_left H le_sup_right).trans
      (Subgroup.relIndex_dvd_index_of_normal (U : Subgroup G) H)))

theorem ofNat_index_sup_antitone (H : Subgroup G) {U V : OpenNormalSubgroup G} (h : U ≤ V) :
    Supernatural.ofNat (H ⊔ (V : Subgroup G)).index ≤
      Supernatural.ofNat (H ⊔ (U : Subgroup G)).index := by
  rw [← Supernatural.dvd_iff_le, Supernatural.ofNat_dvd_ofNat (index_sup_ne_zero H V)
    (index_sup_ne_zero H U)]
  exact Subgroup.index_dvd_of_le (sup_le_sup_left (fun x hx => h hx) H)

theorem ofNat_relIndex_sup_antitone (K H : Subgroup G) {U V : OpenNormalSubgroup G}
    (h : U ≤ V) :
    Supernatural.ofNat ((K ⊔ (V : Subgroup G)).relIndex H) ≤
      Supernatural.ofNat ((K ⊔ (U : Subgroup G)).relIndex H) := by
  rw [← Supernatural.dvd_iff_le, Supernatural.ofNat_dvd_ofNat (relIndex_sup_ne_zero K H V)
    (relIndex_sup_ne_zero K H U)]
  exact Subgroup.relIndex_dvd_of_le_left H (sup_le_sup_left (fun x hx => h hx) K)

theorem not_dvd_superIndex_iff (p : Nat.Primes) (H : Subgroup G) :
    ¬ Supernatural.ofNat p ∣ superIndex H ↔
      ∀ U : OpenNormalSubgroup G, ¬ (p : ℕ) ∣ (H ⊔ (U : Subgroup G)).index := by
  rw [superIndex, Supernatural.ofNat_prime_dvd_iSup_iff, not_exists]
  refine forall_congr' fun U => ?_
  rw [Supernatural.ofNat_dvd_ofNat p.prop.ne_zero (index_sup_ne_zero H U)]

theorem superRelIndex_eq_iSup [TotallyDisconnectedSpace G] {K H : Subgroup G} (hKH : K ≤ H) :
    superRelIndex K H =
      ⨆ U : OpenNormalSubgroup G, Supernatural.ofNat ((K ⊔ (U : Subgroup G)).relIndex H) := by

  let res : OpenNormalSubgroup G → OpenNormalSubgroup H := fun U =>
    { toSubgroup := (U : Subgroup G).subgroupOf H
      isOpen' := Subgroup.subgroupOf_isOpen H (U : Subgroup G) U.toOpenSubgroup.isOpen
      isNormal' := inferInstance }
  have hres : ∀ U : OpenNormalSubgroup G,
      K.subgroupOf H ⊔ ((res U : OpenNormalSubgroup H) : Subgroup H) =
        (K ⊔ (U : Subgroup G)).subgroupOf H :=
    fun U => (sup_subgroupOf_eq hKH).symm
  refine le_antisymm (iSup_le fun V => ?_) (iSup_le fun U => ?_)
  ·
    obtain ⟨W, hWo, hWV⟩ := isOpen_induced_iff.mp V.toOpenSubgroup.isOpen
    have h1W : (1 : G) ∈ W := by
      have : (1 : H) ∈ Subtype.val ⁻¹' W := hWV ▸ V.one_mem
      simpa using this
    obtain ⟨U, hUW⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hWo h1W
    refine le_iSup_of_le U ?_
    have hle : (K ⊔ (U : Subgroup G)).subgroupOf H ≤ K.subgroupOf H ⊔ (V : Subgroup H) := by
      rw [← hres U]
      refine sup_le_sup_left (fun x hx => ?_) _
      have : (x : G) ∈ W := hUW hx
      have : x ∈ Subtype.val ⁻¹' W := this
      rw [hWV] at this
      exact this
    have hne : ((K ⊔ (U : Subgroup G)).subgroupOf H).index ≠ 0 := relIndex_sup_ne_zero K H U
    show Supernatural.ofNat _ ≤ Supernatural.ofNat ((K ⊔ (U : Subgroup G)).subgroupOf H).index
    rw [← Supernatural.dvd_iff_le, Supernatural.ofNat_dvd_ofNat
      (fun h => hne (Nat.eq_zero_of_zero_dvd (h ▸ Subgroup.index_dvd_of_le hle))) hne]
    exact Subgroup.index_dvd_of_le hle
  · refine le_iSup_of_le (res U) ?_
    rw [hres U]
    exact le_rfl

theorem superIndex_of_isOpen [TotallyDisconnectedSpace G] {H : Subgroup G}
    (hH : IsOpen (H : Set G)) : superIndex H = Supernatural.ofNat H.index := by
  have : Finite (G ⧸ H) := Subgroup.quotient_finite_of_isOpen H hH
  have hne : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hH H.one_mem
  refine le_antisymm (iSup_le fun V => ?_) (le_iSup_of_le U ?_)
  · rw [← Supernatural.dvd_iff_le, Supernatural.ofNat_dvd_ofNat (index_sup_ne_zero H V) hne]
    exact Subgroup.index_dvd_of_le le_sup_left
  · rw [sup_eq_left.mpr (fun x hx => hU hx)]

theorem superIndex_eq_mul [TotallyDisconnectedSpace G] {K H : Subgroup G} (hKH : K ≤ H) :
    superIndex K = superIndex H * superRelIndex K H := by
  rw [superRelIndex_eq_iSup hKH, superIndex, superIndex,
    Supernatural.iSup_mul_iSup fun U V =>
      ⟨U ⊓ V, ofNat_index_sup_antitone H inf_le_left, ofNat_relIndex_sup_antitone K H inf_le_right⟩]
  refine iSup_congr fun U => ?_
  rw [index_sup_normal_eq_mul hKH, Supernatural.ofNat_mul (index_sup_ne_zero H U)
    (relIndex_sup_ne_zero K H U)]

theorem superIndex_dvd_of_le [TotallyDisconnectedSpace G] {K H : Subgroup G} (hKH : K ≤ H) :
    superIndex H ∣ superIndex K :=
  ⟨superRelIndex K H, superIndex_eq_mul hKH⟩

end GroundTheory.ProfCoh
end

section -- merged from GroundTheory.ProfiniteCohomology.TorsionDualFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open Function

namespace QZ

theorem finite_setOf_nsmul_eq_zero {n : ℕ} (hn : 0 < n) : {x : QZ | n • x = 0}.Finite :=
  AddCircle.finite_torsion (1 : ℚ) hn

noncomputable def toReal : QZ →+ AddCircle (1 : ℝ) :=
  (QuotientAddGroup.map (AddSubgroup.zmultiples (1 : ℚ)) (AddSubgroup.zmultiples (1 : ℝ))
    (Rat.castHom ℝ).toAddMonoidHom (by
      rw [AddSubgroup.zmultiples_le]
      exact ⟨1, by simp⟩)).comp toAddCircle.toAddMonoidHom

theorem toReal_mk (q : ℚ) : toReal (mk q) = ((q : ℝ) : AddCircle (1 : ℝ)) :=
  rfl

theorem toReal_injective : Injective toReal := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨q, rfl⟩ := mk_surjective x
  rw [toReal_mk, AddCircle.coe_eq_zero_iff] at hx
  obtain ⟨n, hn⟩ := hx
  rw [mk_eq_zero_iff]
  refine ⟨n, ?_⟩
  have : ((n : ℚ) : ℝ) = (q : ℝ) := by simpa using hn
  exact_mod_cast this

noncomputable def toComplex (x : QZ) : ℂ :=
  (AddCircle.toCircle (toReal x) : ℂ)

theorem toComplex_injective : Injective toComplex := fun _ _ h =>
  toReal_injective (AddCircle.injective_toCircle one_ne_zero (Circle.ext h))

@[simp]
theorem toComplex_zero : toComplex 0 = 1 := by
  simp [toComplex]

theorem toComplex_add (x y : QZ) : toComplex (x + y) = toComplex x * toComplex y := by
  simp [toComplex, AddCircle.toCircle_add]

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]

noncomputable def toAddChar (f : G →+ QZ) : AddChar G ℂ where
  toFun g := toComplex (f g)
  map_zero_eq_one' := by simp
  map_add_eq_mul' a b := by simp [toComplex_add]

theorem toAddChar_injective : Injective (toAddChar (G := G)) := fun _ _ h =>
  AddMonoidHom.ext fun a => toComplex_injective (DFunLike.congr_fun h a)

theorem exists_comp_eq_of_injective (i : G →+ H) (hi : Injective i) (f : G →+ QZ) :
    ∃ g : H →+ QZ, g.comp i = f := by
  obtain ⟨g, hg⟩ := (Module.Baer.of_divisible (AddCircle (1 : ℚ))).extension_property_addMonoidHom
    i hi (toAddCircle.toAddMonoidHom.comp f)
  refine ⟨toAddCircle.symm.toAddMonoidHom.comp g, AddMonoidHom.ext fun a => ?_⟩
  have h1 := DFunLike.congr_fun hg a
  simp only [AddMonoidHom.coe_comp, comp_apply, AddEquiv.coe_toAddMonoidHom] at h1 ⊢
  rw [h1, AddEquiv.symm_apply_apply]

theorem exists_comp_eq_of_ker_le (h : G →+ H) (χ : G →+ QZ) (hχ : h.ker ≤ χ.ker) :
    ∃ ψ : H →+ QZ, ψ.comp h = χ := by
  let χ₀ : h.range →+ QZ := (QuotientAddGroup.lift h.ker χ hχ).comp
    (QuotientAddGroup.quotientKerEquivRange h).symm.toAddMonoidHom
  obtain ⟨ψ, hψ⟩ := exists_comp_eq_of_injective h.range.subtype h.range.subtype_injective χ₀
  refine ⟨ψ, AddMonoidHom.ext fun a => ?_⟩
  have h1 := DFunLike.congr_fun hψ ⟨h a, a, rfl⟩
  have h2 : (QuotientAddGroup.quotientKerEquivRange h).symm ⟨h a, a, rfl⟩ =
      (a : G ⧸ h.ker) := by
    rw [AddEquiv.symm_apply_eq]
    rfl
  simp only [AddMonoidHom.coe_comp, comp_apply, AddSubgroup.coe_subtype, χ₀,
    AddEquiv.coe_toAddMonoidHom, h2] at h1
  simpa using h1

theorem exists_apply_ne_zero {a : G} (ha : a ≠ 0) : ∃ f : G →+ QZ, f a ≠ 0 := by
  obtain ⟨c, hc⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero ha
  refine ⟨toAddCircle.symm.toAddMonoidHom.comp (c : G →+ AddCircle (1 : ℚ)), fun h => hc ?_⟩
  exact (AddEquiv.map_eq_zero_iff toAddCircle.symm).mp h


variable (G) in
def evalHom : G →+ ((G →+ QZ) →+ QZ) where
  toFun a :=
    { toFun := fun f => f a
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  map_zero' := by ext f; simp
  map_add' a b := by ext f; simp

theorem evalHom_injective : Injective (evalHom (G := G)) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra hne
  obtain ⟨f, hf⟩ := exists_apply_ne_zero hne
  exact hf (DFunLike.congr_fun ha f)

instance [Finite G] : Finite (G →+ QZ) :=
  Finite.of_injective _ toAddChar_injective

theorem card_hom_le [Finite G] : Nat.card (G →+ QZ) ≤ Nat.card G := by
  have := Fintype.ofFinite G
  calc Nat.card (G →+ QZ) ≤ Nat.card (AddChar G ℂ) :=
        Nat.card_le_card_of_injective _ toAddChar_injective
    _ ≤ Nat.card G := by
        rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
        exact AddChar.card_addChar_le G ℂ

theorem card_hom [Finite G] : Nat.card (G →+ QZ) = Nat.card G :=
  card_hom_le.antisymm <| (Nat.card_le_card_of_injective _ evalHom_injective).trans card_hom_le


end QZ

namespace QZDual

variable {N : Type*} [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]

end QZDual

end GroundTheory.ProfCoh
end

section -- merged from GroundTheory.ProfiniteCohomology.KummerFinite
namespace GroundTheory.ProfCoh

open Polynomial

section Characters

variable {K : Type*} [Field K] {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity K n]

def monoidHomRootsOfUnityEquiv (G : Type*) [Group G] (hG : ∀ g : G, g ^ n = 1) :
    (G →* rootsOfUnity n K) ≃ (G →* Kˣ) where
  toFun φ := (rootsOfUnity n K).subtype.comp φ
  invFun ψ := ψ.codRestrict (rootsOfUnity n K) fun g => by
    rw [mem_rootsOfUnity, ← map_pow, hG g, map_one]
  left_inv φ := by ext; rfl
  right_inv ψ := by ext; rfl

lemma card_monoidHom_rootsOfUnity (G : Type*) [CommGroup G] [Finite G]
    (hG : ∀ g : G, g ^ n = 1) : Nat.card (G →* rootsOfUnity n K) = Nat.card G := by
  have : HasEnoughRootsOfUnity K (Monoid.exponent G) :=
    HasEnoughRootsOfUnity.of_dvd K (Monoid.exponent_dvd_of_forall_pow_eq_one hG)
  rw [Nat.card_congr (monoidHomRootsOfUnityEquiv G hG),
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity]

lemma finite_monoidHom_rootsOfUnity (G : Type*) [Group G] [Finite G] :
    Finite (G →* rootsOfUnity n K) :=
  .of_injective _ DFunLike.coe_injective

end Characters

section Finite

variable (K : Type*) [Field K] (n : ℕ) [NeZero n] [HasEnoughRootsOfUnity K n]
variable (L : Type*) [Field L] [Algebra K L]


omit [NeZero n] [HasEnoughRootsOfUnity K n] in
lemma kummerGroup_pow_eq_one (x : kummerGroup K n L) : x ^ n = 1 :=
  Subtype.ext (UnitsModPow.pow_eq_one K n x.1)

variable {K n L}


omit [NeZero n] [HasEnoughRootsOfUnity K n] in
lemma exists_eigenvector_of_character [FiniteDimensional K L] (χ : Gal(L/K) →* Kˣ) :
    ∃ β : Lˣ, ∀ σ : Gal(L/K), σ (β : L) = algebraMap K L (χ σ : K) * β := by
  let f : Gal(L/K) → Lˣ := fun σ => Units.map (algebraMap K L : K →* L) (χ σ)
  have hf : groupCohomology.IsMulCocycle₁ f := by
    intro g h
    ext
    simp only [f, map_mul, Units.val_mul, Units.coe_map, MonoidHom.coe_coe, AlgEquiv.smul_units_def,
      AlgEquiv.commutes]
    ring
  obtain ⟨β, hβ⟩ := groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units f hf
  refine ⟨β, fun σ => ?_⟩
  have := congrArg Units.val (hβ σ)
  simp only [AlgEquiv.smul_units_def, Units.val_div_eq_div_val, Units.coe_map, MonoidHom.coe_coe,
    f] at this
  rw [← this, div_mul_cancel₀ _ β.ne_zero]


omit [NeZero n] [HasEnoughRootsOfUnity K n] in
lemma exists_kummer_eigenvector [FiniteDimensional K L] [IsGalois K L]
    (hexp : Monoid.exponent Gal(L/K) ∣ n) (χ : Gal(L/K) →* Kˣ) :
    ∃ a : Kˣ, ∃ β : L, β ^ n = algebraMap K L a ∧
      ∀ σ : Gal(L/K), σ β = algebraMap K L (χ σ : K) * β := by
  obtain ⟨β, hβ⟩ := exists_eigenvector_of_character χ
  have hfix : ∀ σ : Gal(L/K), σ ((β : L) ^ n) = (β : L) ^ n := by
    intro σ
    rw [map_pow, hβ σ, mul_pow, ← map_pow, ← Units.val_pow_eq_pow_val, ← map_pow,
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hexp σ, map_one, Units.val_one, map_one, one_mul]
  obtain ⟨b, hb⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := K) _).mpr hfix
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [map_zero] at hb
    exact pow_ne_zero n β.ne_zero hb.symm
  exact ⟨Units.mk0 b hb0, β, hb.symm, hβ⟩

variable (K n L)

theorem kummerPairingRight_injective [FiniteDimensional K L] [IsGalois K L] :
    Function.Injective (kummerPairingRight K n L) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  obtain ⟨a, ha, α, hα⟩ := exists_rep x
  have hfix : ∀ σ : Gal(L/K), σ α = α := fun σ =>
    (kummerPairing_eq_one_iff σ x ha hα).mp (DFunLike.congr_fun hx σ)
  obtain ⟨b, rfl⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := K) α).mpr hfix
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_pow (NeZero.ne n)] at hα
    exact (map_ne_zero (algebraMap K L)).mpr a.ne_zero hα.symm
  have hba : (Units.mk0 b hb0) ^ n = a := by
    ext
    simpa using (algebraMap K L).injective (by simpa using hα)
  apply Subtype.ext
  rw [← ha, OneMemClass.coe_one, QuotientGroup.eq_one_iff]
  exact mem_unitsPow.mpr ⟨_, hba⟩

theorem kummerPairingLeft_injective [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)] (hexp : Monoid.exponent Gal(L/K) ∣ n) :
    Function.Injective (kummerPairingLeft K n L) := by
  let _ : CommGroup Gal(L/K) :=
    { (inferInstance : Group Gal(L/K)) with
      mul_comm := fun a b => (IsMulCommutative.is_comm (M := Gal(L/K))).comm a b }
  have : HasEnoughRootsOfUnity K (Monoid.exponent Gal(L/K)) := HasEnoughRootsOfUnity.of_dvd K hexp
  rw [injective_iff_map_eq_one]
  intro σ hσ
  by_contra hne
  obtain ⟨χ, hχ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity Gal(L/K) K hne
  obtain ⟨a, β, hβ, hχβ⟩ := exists_kummer_eigenvector hexp χ
  have hx : (a : UnitsModPow K n) ∈ kummerGroup K n L := mk_mem_kummerGroup.mpr ⟨β, hβ⟩
  have h1 : σ β = β :=
    (kummerPairing_eq_one_iff σ ⟨_, hx⟩ rfl hβ).mp (DFunLike.congr_fun hσ ⟨_, hx⟩)
  rw [hχβ σ] at h1
  have h2 : algebraMap K L (χ σ : K) = 1 :=
    mul_right_cancel₀ (ne_zero_of_pow_eq_algebraMap hβ) (h1.trans (one_mul β).symm)
  apply hχ
  ext
  simpa using (algebraMap K L).injective (h2.trans (map_one _).symm)

theorem kummerGroup_finite [FiniteDimensional K L] [IsGalois K L] :
    Finite (kummerGroup K n L) :=
  have := finite_monoidHom_rootsOfUnity (K := K) (n := n) Gal(L/K)
  Finite.of_injective _ (kummerPairingRight_injective K n L)

theorem card_kummerGroup [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)] (hexp : Monoid.exponent Gal(L/K) ∣ n) :
    Nat.card (kummerGroup K n L) = Module.finrank K L := by
  let _ : CommGroup Gal(L/K) :=
    { (inferInstance : Group Gal(L/K)) with
      mul_comm := fun a b => (IsMulCommutative.is_comm (M := Gal(L/K))).comm a b }
  have := kummerGroup_finite K n L
  have := finite_monoidHom_rootsOfUnity (K := K) (n := n) Gal(L/K)
  have := finite_monoidHom_rootsOfUnity (K := K) (n := n) (kummerGroup K n L)
  rw [← IsGalois.card_aut_eq_finrank]
  apply le_antisymm
  · calc Nat.card (kummerGroup K n L) ≤ Nat.card (Gal(L/K) →* rootsOfUnity n K) :=
          Nat.card_le_card_of_injective _ (kummerPairingRight_injective K n L)
      _ = Nat.card Gal(L/K) :=
          card_monoidHom_rootsOfUnity Gal(L/K) (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hexp)
  · calc Nat.card Gal(L/K) ≤ Nat.card (kummerGroup K n L →* rootsOfUnity n K) :=
          Nat.card_le_card_of_injective _ (kummerPairingLeft_injective K n L hexp)
      _ = Nat.card (kummerGroup K n L) :=
          card_monoidHom_rootsOfUnity (kummerGroup K n L) (kummerGroup_pow_eq_one K n L)

theorem kummerPairingLeft_bijective [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)] (hexp : Monoid.exponent Gal(L/K) ∣ n) :
    Function.Bijective (kummerPairingLeft K n L) := by
  have := kummerGroup_finite K n L
  have := finite_monoidHom_rootsOfUnity (K := K) (n := n) (kummerGroup K n L)
  rw [Nat.bijective_iff_injective_and_card]
  refine ⟨kummerPairingLeft_injective K n L hexp, ?_⟩
  rw [IsGalois.card_aut_eq_finrank, ← card_kummerGroup K n L hexp]
  exact (card_monoidHom_rootsOfUnity (kummerGroup K n L) (kummerGroup_pow_eq_one K n L)).symm

noncomputable def galEquivDual [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)] (hexp : Monoid.exponent Gal(L/K) ∣ n) :
    Gal(L/K) ≃* (kummerGroup K n L →* rootsOfUnity n K) :=
  MulEquiv.ofBijective _ (kummerPairingLeft_bijective K n L hexp)

end Finite

end GroundTheory.ProfCoh
end
