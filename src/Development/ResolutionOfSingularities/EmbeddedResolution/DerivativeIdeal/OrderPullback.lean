module

public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafSmoothPullback
public import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactIdeal

@[expose] public section

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderPullback
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

private theorem le_natCast_or_succ_le (a : ℕ∞) (r : ℕ) :
    a ≤ (r : ℕ∞) ∨ ((r + 1 : ℕ) : ℕ∞) ≤ a := by
  rcases eq_or_ne a ⊤ with rfl | ha
  · exact Or.inr le_top
  · obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.1 ha
    rcases Nat.lt_or_ge r m with hm | hm
    · exact Or.inr (by exact_mod_cast hm)
    · exact Or.inl (by exact_mod_cast hm)

private theorem germ_comp_appLE {X Y : Scheme.{u}} (h : Y ⟶ X) (U : X.Opens) (V : Y.Opens)
    (e : V ≤ h ⁻¹ᵁ U) (y : Y) (hy : y ∈ V) :
    (Y.presheaf.germ V y hy).hom.comp (h.appLE U V e).hom
      = (h.stalkMap y).hom.comp (X.presheaf.germ U (h.base y) (e hy)).hom := by
  have key : h.appLE U V e ≫ Y.presheaf.germ V y hy
      = X.presheaf.germ U (h.base y) (e hy) ≫ h.stalkMap y := by
    simp only [Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]
    exact (Scheme.Hom.germ_stalkMap ..).symm
  simpa only [CommRingCat.hom_comp] using congrArg CommRingCat.Hom.hom key

theorem stalkIdeal_comap {X Y : Scheme.{u}} (h : Y ⟶ X) (I : X.IdealSheafData) (y : Y) :
    stalkIdeal (I.comap h) y =
      Ideal.map (h.stalkMap y).hom (stalkIdeal I (h.base y)) := by
  obtain ⟨U, hU, hxU, -⟩ :=
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset
      (show h.base y ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨V, hV, hyV, e⟩ :=
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (show y ∈ h ⁻¹ᵁ U from hxU)
  have hcomp : (Y.presheaf.germ V y hyV).hom.comp (h.appLE U V e).hom
      = (h.stalkMap y).hom.comp (X.presheaf.germ U (h.base y) hxU).hom :=
    germ_comp_appLE h U V e y hyV
  rw [stalkIdeal_eq_map_germ (I.comap h) y ⟨V, hV⟩ hyV,
    stalkIdeal_eq_map_germ I (h.base y) ⟨U, hU⟩ hxU,
    Scheme.IdealSheafData.comap_ideal_eq_map_appLE I h ⟨U, hU⟩ ⟨V, hV⟩ e,
    Ideal.map_map, Ideal.map_map]
  exact congrArg (fun φ => Ideal.map φ (I.ideal ⟨U, hU⟩)) hcomp

theorem orderAt_le_orderAt_comap {X Y : Scheme.{u}} (h : Y ⟶ X) (I : X.IdealSheafData) (y : Y) :
    orderAt I (h.base y) ≤ orderAt (I.comap h) y := by
  refine ENat.forall_natCast_le_iff_le.mp fun n hn => ?_
  rw [le_orderAt_iff] at hn ⊢
  rw [stalkIdeal_comap]
  have hmono : Ideal.map (h.stalkMap y).hom (stalkIdeal I (h.base y))
      ≤ Ideal.map (h.stalkMap y).hom
        (IsLocalRing.maximalIdeal (X.presheaf.stalk (h.base y)) ^ n) := Ideal.map_mono hn
  exact le_trans hmono
    (le_trans (Ideal.map_pow ..).le
      (Ideal.pow_right_mono (IsLocalRing.map_maximalIdeal_le ..) n))

private theorem one_le_orderAt_of_one_le_orderAt_comap {X Y : Scheme.{u}} (h : Y ⟶ X) (J : X.IdealSheafData)
    (y : Y) (hy : (1 : ℕ∞) ≤ orderAt (J.comap h) y) : (1 : ℕ∞) ≤ orderAt J (h.base y) := by
  have h1 : ((1 : ℕ) : ℕ∞) ≤ orderAt (J.comap h) y := by exact_mod_cast hy
  suffices hs : ((1 : ℕ) : ℕ∞) ≤ orderAt J (h.base y) by exact_mod_cast hs
  rw [le_orderAt_iff] at h1 ⊢
  rw [stalkIdeal_comap, pow_one] at h1
  rw [pow_one]
  simpa only [IsLocalRing.maximalIdeal_comap] using
    Ideal.le_comap_map.trans (Ideal.comap_mono h1)

theorem orderAt_comap (k : Type u) [Field k] [CharZero k] {X Y : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (h : Y ⟶ X) [AlgebraicGeometry.Smooth h] (I : X.IdealSheafData) (y : Y) :
    orderAt (I.comap h) y = orderAt I (h.base y) := by
  have : LocallyOfFiniteType p := inferInstance
  have : LocallyOfFiniteType (h ≫ p) := inferInstance
  refine le_antisymm ?_ (orderAt_le_orderAt_comap h I y)
  rcases eq_or_ne (orderAt I (h.base y)) ⊤ with hI | hI
  · rw [hI]; exact le_top
  obtain ⟨r, hr⟩ := ENat.ne_top_iff_exists.1 hI
  rw [← hr]
  rcases le_natCast_or_succ_le (orderAt (I.comap h) y) r with hle | hlt
  · exact hle
  exfalso
  have h1 : ((1 : ℕ) : ℕ∞) ≤ orderAt (derivIdealSheafIterate k (h ≫ p) r (I.comap h)) y :=
    le_orderAt_derivIdealSheafIterate k (h ≫ p) (I.comap h) y 1 r (by
      rw [Nat.add_comm]; exact hlt)
  rw [derivIdealSheafIterate_comap k p h r I] at h1
  have h2 : (1 : ℕ∞) ≤ orderAt ((derivIdealSheafIterate k p r I).comap h) y := by exact_mod_cast h1
  have h3 := one_le_orderAt_of_one_le_orderAt_comap h (derivIdealSheafIterate k p r I) y h2
  have h4 : orderAt (derivIdealSheafIterate k p r I) (h.base y) = ((r - r : ℕ) : ℕ∞) :=
    orderAt_derivIdealSheafIterate_eq_sub k p I (h.base y) hr.symm (le_refl r)
  rw [h4, Nat.sub_self] at h3
  simp at h3

theorem orderAtLeastLocus_comap (k : Type u) [Field k] [CharZero k] {X Y : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (h : Y ⟶ X) [AlgebraicGeometry.Smooth h] (I : X.IdealSheafData) (m : ℕ) :
    orderAtLeastLocus (I.comap h) m = ⇑h.base ⁻¹' orderAtLeastLocus I m := by
  ext y
  simp only [Set.mem_preimage, mem_orderAtLeastLocus_iff, orderAt_comap k p h I y]

end FunctorialResolution.EmbeddedResolution
end

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivBalancedOrderLocus
universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

variable (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}}
  (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
  (I : X.IdealSheafData) (m : ℕ)

theorem orderAt_eq_zero_or_le_orderAt_of_isDerivBalanced
    (h : IsDerivBalanced k p I m) (x : X) :
    orderAt I x = 0 ∨ (m : ℕ∞) ≤ orderAt I x := by
  rcases Nat.eq_zero_or_pos m with rfl | hpos
  · right
    simp
  have hm1 : 1 ≤ m := hpos
  by_cases h0 : orderAt I x = 0
  · exact Or.inl h0
  right
  have hlt : m - 1 < m := by omega
  have hle : derivIdealSheafIterate k p (m - 1) I ^ m ≤ I ^ (m - (m - 1)) :=
    IsDerivBalanced.derivIdealSheafIterate_pow_le k p h hlt
  have hsub : m - (m - 1) = 1 := by omega
  rw [hsub, pow_one] at hle
  have hord : orderAt I x ≤ orderAt (derivIdealSheafIterate k p (m - 1) I ^ m) x :=
    orderAt_le_of_le hle x
  rw [orderAt_pow k p (derivIdealSheafIterate k p (m - 1) I) m x] at hord
  have hne : orderAt (derivIdealSheafIterate k p (m - 1) I) x ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hord
    exact h0 (le_antisymm hord (by exact zero_le))
  have hmem : x ∈ (derivIdealSheafIterate k p (m - 1) I).support := by
    by_contra hc
    exact hne ((orderAt_eq_zero_iff_not_mem_support _ x).mpr hc)
  have heq := support_derivIdealSheafIterate_eq_orderAtLeastLocus k p I hm1
  have hx : x ∈ orderAtLeastLocus I m := by
    rw [← heq]
    exact hmem
  exact (mem_orderAtLeastLocus_iff I m x).mp hx

theorem orderAtLeastLocus_eq_support_of_isDerivBalanced
    (h : IsDerivBalanced k p I m) (hm : 1 ≤ m) :
    orderAtLeastLocus I m = (I.support : Set X) := by
  ext x
  rw [mem_orderAtLeastLocus_iff]
  constructor
  · intro hx
    have h1 : (1 : ℕ∞) ≤ orderAt I x := le_trans (by exact_mod_cast hm) hx
    exact (one_le_orderAt_iff_mem_support I x).mp h1
  · intro hx
    have hx' : x ∈ I.support := hx
    have hne : orderAt I x ≠ 0 := fun h0 =>
      (orderAt_eq_zero_iff_not_mem_support I x).mp h0 hx'
    rcases orderAt_eq_zero_or_le_orderAt_of_isDerivBalanced k p I m h x with h0 | h0
    · exact absurd h0 hne
    · exact h0

end FunctorialResolution.EmbeddedResolution
end

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.PartialDerivativeIdeal
namespace FunctorialResolution.EmbeddedResolution

namespace EtaleCoordinates

variable (k : Type*) [CommRing k] (ι : Type*) (S : Type*) [CommRing S]
  [Algebra (MvPolynomial ι k) S] [Algebra k S] [IsScalarTower k (MvPolynomial ι k) S]
  [Algebra.FormallyEtale (MvPolynomial ι k) S]

theorem coord_smul_partialDeriv_mem_tangentDerivations (h : ι) :
    coord k ι S h • partialDeriv k ι S h ∈
      tangentDerivations k (Ideal.span ({coord k ι S h} : Set S)) :=
  smul_mem_tangentDerivations k (Ideal.span ({coord k ι S h} : Set S))
    (Ideal.mem_span_singleton_self (coord k ι S h)) (partialDeriv k ι S h)

theorem partialDeriv_mem_tangentDerivations_of_ne {i h : ι} (hih : i ≠ h) :
    partialDeriv k ι S i ∈ tangentDerivations k (Ideal.span ({coord k ι S h} : Set S)) := by
  rw [mem_tangentDerivations_span_singleton, partialDeriv_coord_of_ne k ι S i h hih]
  exact Submodule.zero_mem _

theorem coord_mul_partialDeriv_mem_logDerivIdeal (h : ι) (J : Ideal S) {g : S} (hg : g ∈ J) :
    coord k ι S h * partialDeriv k ι S h g ∈
      logDerivIdeal k (Ideal.span ({coord k ι S h} : Set S)) J := by
  have hmem := derivation_apply_mem_logDerivIdeal k (Ideal.span ({coord k ι S h} : Set S)) J
    (coord k ι S h • partialDeriv k ι S h)
    (coord_smul_partialDeriv_mem_tangentDerivations k ι S h) hg
  simpa [smul_eq_mul] using hmem

theorem partialDeriv_mem_logDerivIdeal_of_ne {i h : ι} (hih : i ≠ h) (J : Ideal S) {g : S}
    (hg : g ∈ J) :
    partialDeriv k ι S i g ∈ logDerivIdeal k (Ideal.span ({coord k ι S h} : Set S)) J :=
  derivation_apply_mem_logDerivIdeal k (Ideal.span ({coord k ι S h} : Set S)) J
    (partialDeriv k ι S i) (partialDeriv_mem_tangentDerivations_of_ne k ι S hih) hg

def partialDerivIdeal (h : ι) (J : Ideal S) : Ideal S :=
  J ⊔ Ideal.span {x : S | ∃ g ∈ J, partialDeriv k ι S h g = x}

private theorem partialDerivIdeal_def (h : ι) (J : Ideal S) :
    partialDerivIdeal k ι S h J =
      J ⊔ Ideal.span {x : S | ∃ g ∈ J, partialDeriv k ι S h g = x} := rfl

theorem le_partialDerivIdeal (h : ι) (J : Ideal S) : J ≤ partialDerivIdeal k ι S h J := by
  rw [partialDerivIdeal_def]
  exact le_sup_left

theorem partialDeriv_mem_partialDerivIdeal (h : ι) (J : Ideal S) {g : S} (hg : g ∈ J) :
    partialDeriv k ι S h g ∈ partialDerivIdeal k ι S h J := by
  rw [partialDerivIdeal_def]
  exact Submodule.mem_sup_right (Ideal.subset_span ⟨g, hg, rfl⟩)

theorem partialDerivIdeal_le_iff (h : ι) (J K : Ideal S) :
    partialDerivIdeal k ι S h J ≤ K ↔ J ≤ K ∧ ∀ g ∈ J, partialDeriv k ι S h g ∈ K := by
  rw [partialDerivIdeal_def, sup_le_iff, Ideal.span_le]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun g hg => h2 ⟨g, hg, rfl⟩⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    intro x hx
    obtain ⟨g, hg, rfl⟩ := hx
    exact h2 g hg

theorem partialDerivIdeal_le (h : ι) {J K : Ideal S} (hJK : J ≤ K)
    (hD : ∀ g ∈ J, partialDeriv k ι S h g ∈ K) : partialDerivIdeal k ι S h J ≤ K :=
  (partialDerivIdeal_le_iff k ι S h J K).mpr ⟨hJK, hD⟩

theorem partialDerivIdeal_mono (h : ι) : Monotone (partialDerivIdeal k ι S h) := by
  intro I J hIJ
  rw [partialDerivIdeal_le_iff]
  refine ⟨hIJ.trans (le_partialDerivIdeal k ι S h J), fun g hg => ?_⟩
  exact partialDeriv_mem_partialDerivIdeal k ι S h J (hIJ hg)

def partialDerivIdealIterate (h : ι) : ℕ → Ideal S → Ideal S
  | 0, J => J
  | l + 1, J => partialDerivIdeal k ι S h (partialDerivIdealIterate h l J)

theorem partialDerivIdealIterate_zero (h : ι) (J : Ideal S) :
    partialDerivIdealIterate k ι S h 0 J = J := rfl

theorem partialDerivIdealIterate_succ (h : ι) (l : ℕ) (J : Ideal S) :
    partialDerivIdealIterate k ι S h (l + 1) J =
      partialDerivIdeal k ι S h (partialDerivIdealIterate k ι S h l J) := rfl

private def evalDerivationAddHom (g : S) : Derivation k S S →+ S where
  toFun D := D g
  map_zero' := rfl
  map_add' _ _ := rfl

omit [Algebra (MvPolynomial ι k) S] [IsScalarTower k (MvPolynomial ι k) S]
  [Algebra.FormallyEtale (MvPolynomial ι k) S] in
private theorem derivation_sum_apply (s : Finset ι) (f : ι → Derivation k S S) (g : S) :
    (∑ i ∈ s, f i) g = ∑ i ∈ s, f i g :=
  map_sum (evalDerivationAddHom k S g) f s

theorem derivation_apply_eq_sum_partialDeriv [Fintype ι] (D : Derivation k S S) (g : S) :
    D g = ∑ i, D (coord k ι S i) * partialDeriv k ι S i g := by
  have h1 : D g = (∑ i, D (coord k ι S i) • partialDeriv k ι S i : Derivation k S S) g :=
    congrArg (fun E : Derivation k S S => E g) (eq_sum_smul_partialDeriv k ι S D)
  have h2 : (∑ i, D (coord k ι S i) • partialDeriv k ι S i : Derivation k S S) g
      = ∑ i, D (coord k ι S i) * partialDeriv k ι S i g :=
    derivation_sum_apply k ι S Finset.univ (fun i => D (coord k ι S i) • partialDeriv k ι S i) g
  exact h1.trans h2

private theorem derivIdeal_le_logDerivIdeal_sup_partialDerivIdeal [Fintype ι] (h : ι) (I : Ideal S) :
    derivIdeal k I ≤
      logDerivIdeal k (Ideal.span ({coord k ι S h} : Set S)) I ⊔ partialDerivIdeal k ι S h I := by
  rw [derivIdeal_le_iff]
  refine ⟨(le_logDerivIdeal k (Ideal.span ({coord k ι S h} : Set S)) I).trans le_sup_left, ?_⟩
  intro D g hg
  rw [derivation_apply_eq_sum_partialDeriv k ι S D g]
  refine Ideal.sum_mem _ ?_
  intro i _
  by_cases hi : i = h
  · rw [hi]
    exact Submodule.mem_sup_right
      (Ideal.mul_mem_left _ _ (partialDeriv_mem_partialDerivIdeal k ι S h I hg))
  · exact Submodule.mem_sup_left
      (Ideal.mul_mem_left _ _ (partialDeriv_mem_logDerivIdeal_of_ne k ι S hi I hg))

private def idealInfComapPartialDeriv (h : ι) (K : Ideal S) : Ideal S where
  carrier := {g : S | g ∈ K ∧ partialDeriv k ι S h g ∈ K}
  add_mem' := by
    intro a b ha hb
    obtain ⟨ha1, ha2⟩ := ha
    obtain ⟨hb1, hb2⟩ := hb
    refine ⟨Submodule.add_mem K ha1 hb1, ?_⟩
    rw [map_add (f := _)]
    exact Submodule.add_mem K ha2 hb2
  zero_mem' := by
    refine ⟨Submodule.zero_mem K, ?_⟩
    rw [map_zero]
    exact Submodule.zero_mem K
  smul_mem' := by
    intro c x hx
    obtain ⟨hx1, hx2⟩ := hx
    refine ⟨Ideal.mul_mem_left K c hx1, ?_⟩
    have hl : partialDeriv k ι S h (c * x)
        = c * partialDeriv k ι S h x + x * partialDeriv k ι S h c := by
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    show partialDeriv k ι S h (c * x) ∈ K
    rw [hl]
    exact Submodule.add_mem K (Ideal.mul_mem_left K c hx2) (Ideal.mul_mem_right _ K hx1)

private theorem mem_idealInfComapPartialDeriv_iff (h : ι) (K : Ideal S) (g : S) :
    g ∈ idealInfComapPartialDeriv k ι S h K ↔ g ∈ K ∧ partialDeriv k ι S h g ∈ K := Iff.rfl

private theorem partialDerivIdeal_logDerivIdeal_le [Fintype ι] [DecidableEq ι] (h : ι) (I : Ideal S) :
    partialDerivIdeal k ι S h
        (logDerivIdeal k (Ideal.span ({coord k ι S h} : Set S)) I) ≤
      logDerivIdeal k (Ideal.span ({coord k ι S h} : Set S)) (partialDerivIdeal k ι S h I) := by
  have key : logDerivIdeal k (Ideal.span ({coord k ι S h} : Set S)) I ≤
      idealInfComapPartialDeriv k ι S h
        (logDerivIdeal k (Ideal.span ({coord k ι S h} : Set S))
          (partialDerivIdeal k ι S h I)) := by
    rw [logDerivIdeal_le_iff]
    constructor
    · intro g hg
      rw [mem_idealInfComapPartialDeriv_iff]
      refine ⟨?_, ?_⟩
      · exact le_logDerivIdeal k _ _ (le_partialDerivIdeal k ι S h I hg)
      · exact le_logDerivIdeal k _ _ (partialDeriv_mem_partialDerivIdeal k ι S h I hg)
    · intro D hD y hy
      rw [mem_idealInfComapPartialDeriv_iff]
      have hDmem : D (coord k ι S h) ∈ Ideal.span ({coord k ι S h} : Set S) :=
        (mem_tangentDerivations_span_singleton k (coord k ι S h) D).mp hD
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hDmem
      refine ⟨?_, ?_⟩
      · exact logDerivIdeal_mono k _ (le_partialDerivIdeal k ι S h I)
          (derivation_apply_mem_logDerivIdeal k _ I D hD hy)
      · rw [derivation_apply_eq_sum_partialDeriv k ι S D y]
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        refine Ideal.sum_mem _ ?_
        intro i _
        rw [Derivation.leibniz]
        refine Submodule.add_mem _ ?_ ?_
        · by_cases hi : i = h
          · rw [hi, smul_eq_mul, ← hc, mul_assoc]
            refine Ideal.mul_mem_left _ _ ?_
            exact coord_mul_partialDeriv_mem_logDerivIdeal k ι S h
              (partialDerivIdeal k ι S h I)
              (partialDeriv_mem_partialDerivIdeal k ι S h I hy)
          · rw [smul_eq_mul, partialDeriv_comm k ι S h i y]
            refine Ideal.mul_mem_left _ _ ?_
            exact partialDeriv_mem_logDerivIdeal_of_ne k ι S hi
              (partialDerivIdeal k ι S h I)
              (partialDeriv_mem_partialDerivIdeal k ι S h I hy)
        · by_cases hi : i = h
          · rw [hi, smul_eq_mul]
            refine Ideal.mul_mem_right _ _ ?_
            exact le_logDerivIdeal k _ _ (partialDeriv_mem_partialDerivIdeal k ι S h I hy)
          · rw [smul_eq_mul]
            refine Ideal.mul_mem_right _ _ ?_
            exact logDerivIdeal_mono k _ (le_partialDerivIdeal k ι S h I)
              (partialDeriv_mem_logDerivIdeal_of_ne k ι S hi I hy)
  refine partialDerivIdeal_le k ι S h ?_ ?_
  · intro g hg
    exact ((mem_idealInfComapPartialDeriv_iff k ι S h _ g).mp (key hg)).1
  · intro g hg
    exact ((mem_idealInfComapPartialDeriv_iff k ι S h _ g).mp (key hg)).2

private theorem partialDerivIdeal_logDerivIdealIterate_le [Fintype ι] [DecidableEq ι] (h : ι) (m : ℕ)
    (I : Ideal S) :
    partialDerivIdeal k ι S h
        (logDerivIdealIterate k (Ideal.span ({coord k ι S h} : Set S)) m I) ≤
      logDerivIdealIterate k (Ideal.span ({coord k ι S h} : Set S)) m
        (partialDerivIdeal k ι S h I) := by
  induction m with
  | zero => exact le_of_eq (by simp only [logDerivIdealIterate_zero])
  | succ m ih =>
      rw [logDerivIdealIterate_succ, logDerivIdealIterate_succ]
      exact (partialDerivIdeal_logDerivIdeal_le k ι S h _).trans (logDerivIdeal_mono k _ ih)

theorem derivIdealIterate_le_iSup_logDerivIdealIterate_partialDerivIdealIterate [Fintype ι] [DecidableEq ι]
    (h : ι) (n : ℕ) (J : Ideal S) :
    derivIdealIterate k n J ≤
      ⨆ l, ⨆ _ : l ≤ n,
        logDerivIdealIterate k (Ideal.span ({coord k ι S h} : Set S)) (n - l)
          (partialDerivIdealIterate k ι S h l J) := by
  induction n with
  | zero =>
      rw [derivIdealIterate_zero]
      exact le_iSup₂ (f := fun m (_ : m ≤ 0) =>
        logDerivIdealIterate k (Ideal.span ({coord k ι S h} : Set S)) (0 - m)
          (partialDerivIdealIterate k ι S h m J)) 0 le_rfl
  | succ n ih =>
      rw [derivIdealIterate_succ]
      refine le_trans (derivIdeal_mono k ih) ?_
      refine le_trans (derivIdeal_iSup_le k _) ?_
      refine iSup_le fun l => ?_
      refine le_trans (derivIdeal_iSup_le k _) ?_
      refine iSup_le fun hl => ?_
      refine le_trans (derivIdeal_le_logDerivIdeal_sup_partialDerivIdeal k ι S h _) ?_
      refine sup_le ?_ ?_
      · rw [← logDerivIdealIterate_succ, show n - l + 1 = n + 1 - l from by omega]
        exact le_iSup₂ (f := fun m (_ : m ≤ n + 1) =>
          logDerivIdealIterate k (Ideal.span ({coord k ι S h} : Set S)) (n + 1 - m)
            (partialDerivIdealIterate k ι S h m J)) l (by omega)
      · refine le_trans (partialDerivIdeal_logDerivIdealIterate_le k ι S h (n - l) _) ?_
        rw [← partialDerivIdealIterate_succ, show n - l = n + 1 - (l + 1) from by omega]
        exact le_iSup₂ (f := fun m (_ : m ≤ n + 1) =>
          logDerivIdealIterate k (Ideal.span ({coord k ι S h} : Set S)) (n + 1 - m)
            (partialDerivIdealIterate k ι S h m J)) (l + 1) (by omega)

end EtaleCoordinates

end FunctorialResolution.EmbeddedResolution
end
