module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FormRightMem

@[expose] public section

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.RelIndexEqOfCover
namespace Formalism.HermitianLattices.Ext.L3.LIOrb

open Subgroup

variable {G : Type*} [Group G]

private theorem ncard_orbit_in_stabilizer_eq_relIndex {X Y : Type*} [MulAction G X] [MulAction G Y] (t : X) (y : Y) :
    {x : X | ∃ g : G, g • y = y ∧ g • t = x}.ncard =
      (MulAction.stabilizer G t).relIndex (MulAction.stabilizer G y) := by
  have h1 : MulAction.stabilizer (MulAction.stabilizer G y) t =
      (MulAction.stabilizer G t).subgroupOf (MulAction.stabilizer G y) := by
    ext g
    simp [Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff, Subgroup.smul_def]
  have h2 : MulAction.orbit (MulAction.stabilizer G y) t = {x : X | ∃ g : G, g • y = y ∧ g • t = x} := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨g, g.2, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, rfl⟩
  rw [Subgroup.relIndex, ← h1, MulAction.index_stabilizer, h2]

theorem relIndex_eq_of_cover (S C H' : Subgroup G) (h1 : H' ≤ S)
    (h2 : ∀ s ∈ S, ∃ t ∈ H', t * s ∈ C) : C.relIndex S = C.relIndex H' := by
  have hS := ncard_orbit_in_stabilizer_eq_relIndex (G := G) ((1 : G) : G ⧸ C) ((1 : G) : G ⧸ S)
  have hH := ncard_orbit_in_stabilizer_eq_relIndex (G := G) ((1 : G) : G ⧸ C) ((1 : G) : G ⧸ H')
  rw [MulAction.stabilizer_quotient, MulAction.stabilizer_quotient] at hS hH
  rw [← hS, ← hH]
  have hmem : ∀ (K : Subgroup G) (g : G), g • ((1 : G) : G ⧸ K) = ((1 : G) : G ⧸ K) ↔ g ∈ K :=
    fun K g => by rw [← MulAction.mem_stabilizer_iff, MulAction.stabilizer_quotient]
  congr 1
  ext x
  simp only [Set.mem_setOf_eq, hmem]
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨t, ht, htg⟩ := h2 g hg
    refine ⟨t⁻¹, H'.inv_mem ht, ?_⟩
    rw [MulAction.Quotient.smul_mk, MulAction.Quotient.smul_mk, QuotientGroup.eq]
    simpa using htg
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, h1 hg, rfl⟩

theorem index_tube (H S C H' : Subgroup G) (hS : S ≤ H) (hC : C ≤ H) (h1 : H' ≤ S)
    (h2 : ∀ s ∈ S, ∃ t ∈ H', t * s ∈ C) :
    S.relIndex H * C.relIndex H' = C.relIndex H * S.relIndex C := by
  rw [← relIndex_eq_of_cover S C H' h1 h2, ← inf_relIndex_right C S, ← inf_relIndex_right S C, mul_comm,
    relIndex_mul_relIndex _ _ _ inf_le_right hS, mul_comm, relIndex_mul_relIndex _ _ _ inf_le_right hC, inf_comm]

theorem relIndex_cocycle (A B C : Subgroup G) (hAC : C.relIndex A ≠ 0) (hBA : A.relIndex B ≠ 0)
    (hCB : B.relIndex C ≠ 0) :
    B.relIndex A * C.relIndex B * A.relIndex C = A.relIndex B * B.relIndex C * C.relIndex A := by
  have hBA' : B.relIndex A ≠ 0 := relIndex_ne_zero_trans hCB hAC
  have hAC' : A.relIndex C ≠ 0 := relIndex_ne_zero_trans hBA hCB
  have orbitMap_conj_smul_one := relIndex_inf_mul_relIndex C B A
  have orbitMap_conj_smul_two := relIndex_inf_mul_relIndex B C A
  have eB1 := relIndex_inf_mul_relIndex A C B
  have eB2 := relIndex_inf_mul_relIndex C A B
  have eC1 := relIndex_inf_mul_relIndex B A C
  have eC2 := relIndex_inf_mul_relIndex A B C
  have EA : C.relIndex (A ⊓ B) * B.relIndex A = B.relIndex (A ⊓ C) * C.relIndex A := by
    rw [inf_comm A B, inf_comm A C, orbitMap_conj_smul_one, orbitMap_conj_smul_two, inf_comm]
  have EB : A.relIndex (B ⊓ C) * C.relIndex B = C.relIndex (A ⊓ B) * A.relIndex B := by
    rw [inf_comm B C, eB1, eB2, inf_comm]
  have EC : B.relIndex (A ⊓ C) * A.relIndex C = A.relIndex (B ⊓ C) * B.relIndex C := by
    rw [eC1, eC2, inf_comm]
  have hu : C.relIndex (A ⊓ B) ≠ 0 := by
    rw [inf_comm]
    exact left_ne_zero_of_mul (by rw [orbitMap_conj_smul_one]; exact relIndex_inf_ne_zero hAC hBA')
  have hv : B.relIndex (A ⊓ C) ≠ 0 :=
    left_ne_zero_of_mul (by rw [eC1]; exact relIndex_inf_ne_zero hCB hAC')
  have hw : A.relIndex (B ⊓ C) ≠ 0 :=
    left_ne_zero_of_mul (by rw [eC2]; exact relIndex_inf_ne_zero hAC' hCB)
  apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (mul_ne_zero (mul_ne_zero hu hv) hw))
  calc C.relIndex (A ⊓ B) * B.relIndex (A ⊓ C) * A.relIndex (B ⊓ C) *
        (B.relIndex A * C.relIndex B * A.relIndex C)
      = (C.relIndex (A ⊓ B) * B.relIndex A) * (A.relIndex (B ⊓ C) * C.relIndex B) *
          (B.relIndex (A ⊓ C) * A.relIndex C) := by ring
    _ = (B.relIndex (A ⊓ C) * C.relIndex A) * (C.relIndex (A ⊓ B) * A.relIndex B) *
          (A.relIndex (B ⊓ C) * B.relIndex C) := by rw [EA, EB, EC]
    _ = _ := by ring

theorem ncard_biUnion_finset {ι X : Type*} (s : Finset ι) (f : ι → Set X)
    (hf : ∀ i ∈ s, (f i).Finite) (hd : (s : Set ι).PairwiseDisjoint f) :
    (⋃ i ∈ s, f i).ncard = ∑ i ∈ s, (f i).ncard := by
  classical
  revert hf hd
  refine Finset.induction_on s (by simp) ?_
  intro a s ha ih hf hd
  have hfa : (f a).Finite := hf a (Finset.mem_insert_self a s)
  have hfs : (⋃ i ∈ s, f i).Finite :=
    Set.Finite.biUnion s.finite_toSet fun i hi => hf i (Finset.mem_insert_of_mem hi)
  have hdisj : Disjoint (f a) (⋃ i ∈ s, f i) := by
    rw [Set.disjoint_iUnion₂_right]
    intro i hi
    exact hd (by simp) (by simp [hi]) (fun h => ha (h ▸ hi))
  rw [Finset.set_biUnion_insert, Finset.sum_insert ha, Set.ncard_union_eq hdisj hfa hfs,
    ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      (hd.subset (Finset.coe_subset.2 (Finset.subset_insert a s)))]

theorem ncard_orb {X Y : Type*} [MulAction G X] [MulAction G Y] (t : X) (y : Y) :
    {x : X | ∃ g : G, g • y = y ∧ g • t = x}.ncard =
      (MulAction.stabilizer G t).relIndex (MulAction.stabilizer G y) := by
  exact ncard_orbit_in_stabilizer_eq_relIndex t y

theorem sum_relIndex_fibre {X Y : Type*} [MulAction G X] [MulAction G Y] (π : X → Y)
    (hπ : ∀ (g : G) x, π (g • x) = g • π x) (A : Set X) (hA : ∀ g : G, ∀ x ∈ A, g • x ∈ A)
    (sX : Finset X) (sY : Finset Y) (hsX : ∀ x ∈ sX, x ∈ A ∧ π x ∈ sY)
    (hX : ∀ x ∈ A, ∃! t, t ∈ sX ∧ ∃ g : G, g • t = x)
    (hY : ∀ y ∈ sY, ∀ y' ∈ sY, (∃ g : G, g • y = y') → y = y')
    (hfin : ∀ x ∈ sX, (MulAction.stabilizer G x).relIndex (MulAction.stabilizer G (π x)) ≠ 0)
    (w : Y → ℝ) :
    ∑ x ∈ sX, ((MulAction.stabilizer G x).relIndex (MulAction.stabilizer G (π x)) : ℝ) * w (π x) =
      ∑ y ∈ sY, (Nat.card {x // x ∈ A ∧ π x = y} : ℝ) * w y := by
  classical
  have hcard : ∀ y ∈ sY, (Nat.card {x // x ∈ A ∧ π x = y} : ℝ) =
      ∑ t ∈ sX.filter (fun t => π t = y),
        ((MulAction.stabilizer G t).relIndex (MulAction.stabilizer G (π t)) : ℝ) := by
    intro y hy
    have hfib : {x | x ∈ A ∧ π x = y} =
        ⋃ t ∈ sX.filter (fun t => π t = y), {x : X | ∃ g : G, g • y = y ∧ g • t = x} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_filter, exists_prop]
      constructor
      · rintro ⟨hxA, hxy⟩
        obtain ⟨t, ⟨ht, g, hgt⟩, -⟩ := hX x hxA
        have h1 : π t = y := hY (π t) (hsX t ht).2 y hy ⟨g, by rw [← hπ, hgt, hxy]⟩
        refine ⟨t, ⟨ht, h1⟩, g, ?_, hgt⟩
        rw [← h1, ← hπ, hgt, hxy, h1]
      · rintro ⟨t, ⟨ht, h1⟩, g, hg, rfl⟩
        refine ⟨hA g t (hsX t ht).1, ?_⟩
        rw [hπ, h1, hg]
    have hfin' : ∀ t ∈ sX.filter (fun t => π t = y), {x : X | ∃ g : G, g • y = y ∧ g • t = x}.Finite := by
      intro t ht
      rw [Finset.mem_filter] at ht
      apply Set.finite_of_ncard_ne_zero
      rw [ncard_orb, ← ht.2]
      exact hfin t ht.1
    have hdisj : (↑(sX.filter (fun t => π t = y)) : Set X).PairwiseDisjoint
        (fun t => {x : X | ∃ g : G, g • y = y ∧ g • t = x}) := by
      intro t ht t' ht' hne
      refine Set.disjoint_left.2 ?_
      rintro x ⟨g, -, rfl⟩ ⟨g', -, hg'⟩
      rw [Finset.mem_coe, Finset.mem_filter] at ht ht'
      obtain ⟨t0, -, huniq⟩ := hX (g • t) (hA g t (hsX t ht.1).1)
      exact hne ((huniq t ⟨ht.1, g, rfl⟩).trans (huniq t' ⟨ht'.1, g', hg'⟩).symm)
    have hnc : Nat.card {x // x ∈ A ∧ π x = y} = ({x | x ∈ A ∧ π x = y} : Set X).ncard :=
      by exact (Set.ncard_ofPred _).symm
    rw [hnc, hfib, ncard_biUnion_finset _ _ hfin' hdisj]
    push_cast
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [Finset.mem_filter] at ht
    rw [ncard_orb, ht.2]
  symm
  calc ∑ y ∈ sY, (Nat.card {x // x ∈ A ∧ π x = y} : ℝ) * w y
      = ∑ y ∈ sY, ∑ t ∈ sX.filter (fun t => π t = y),
          ((MulAction.stabilizer G t).relIndex (MulAction.stabilizer G (π t)) : ℝ) * w (π t) := by
        refine Finset.sum_congr rfl fun y hy => ?_
        rw [hcard y hy, Finset.sum_mul]
        refine Finset.sum_congr rfl fun t ht => ?_
        rw [(Finset.mem_filter.1 ht).2]
    _ = _ := Finset.sum_fiberwise_of_maps_to (fun t ht => (hsX t ht).2) _

end Formalism.HermitianLattices.Ext.L3.LIOrb
end

open NumberField Module Filter

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.LIOrb

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem pow_smul_anti (𝔭 : Ideal (𝓞 F)) (A : Submodule (𝓞 K) V) {i j : ℕ} (hij : i ≤ j) :
    ((extP K 𝔭) ^ j • A : Submodule (𝓞 K) V) ≤ (extP K 𝔭) ^ i • A := Submodule.smul_mono_left (Ideal.pow_le_pow_right hij)

theorem exists_pow_smul_le {M₁ M₂ : Submodule (𝓞 K) V} (hM₁ : Submodule.IsLattice K M₁)
    (hM₂ : Submodule.IsFullLattice K M₂) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ r : ℕ, ((extP K 𝔭) ^ r • locF 𝔭 M₁ : Submodule (𝓞 K) V) ≤ locF 𝔭 M₂ := by
  have := h𝔭.isPrime
  obtain ⟨n, hn, hnx⟩ := LocF.exists_zsmul_le hM₁ hM₂
  have hc : ((n : ℤ) : 𝓞 F) ≠ 0 := by exact_mod_cast hn
  obtain ⟨r, u, hu, hdvd⟩ := D2.exists_mul_dvd h𝔭 hc
  refine ⟨r, ?_⟩
  have key : extP K 𝔭 ^ r ≤ (locF 𝔭 M₂).colon (locF 𝔭 M₁ : Set V) := by
    unfold extP
    rw [← Ideal.map_pow, Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Submodule.mem_colon]
    intro x hx
    obtain ⟨s, hs, hsx⟩ := (LocalSpans.mem_locF 𝔭 M₁ x).1 hx
    obtain ⟨d, hd⟩ := hdvd a ha
    refine (LocalSpans.mem_locF 𝔭 M₂ _).2
      ⟨u * s, fun h => (h𝔭.isPrime.mem_or_mem h).elim hu hs, ?_⟩
    have e : algebraMap (𝓞 F) (𝓞 K) (u * s) • algebraMap (𝓞 F) (𝓞 K) a • x =
        algebraMap (𝓞 F) (𝓞 K) d • (n • (algebraMap (𝓞 F) (𝓞 K) s • x)) := by
      rw [← LocF.algebraMap_intCast_smul (F := F) (K := K) n]
      simp only [smul_smul, ← map_mul]
      congr 2
      linear_combination s * hd
    rw [e]
    exact M₂.smul_mem _ (hnx _ hsx)
  rw [Submodule.smul_le]
  intro a ha x hx
  exact Submodule.mem_colon.1 (key ha) x hx

set_option linter.unusedVariables false in
theorem locF_inf {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {A B : Submodule (𝓞 K) V}
    (hA : locF 𝔭 A = A) (hB : locF 𝔭 B = B) : locF 𝔭 (A ⊓ B) = A ⊓ B := by
  apply le_antisymm
  · refine le_inf ?_ ?_
    · exact (LocF.locF_mono 𝔭 inf_le_left).trans hA.le
    · exact (LocF.locF_mono 𝔭 inf_le_right).trans hB.le
  · exact LocF.le_locF 𝔭 _

theorem locF_inf_locF {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (A B : Submodule (𝓞 K) V) :
    locF 𝔭 (A ⊓ B) = locF 𝔭 A ⊓ locF 𝔭 B := by
  have := h𝔭.isPrime
  apply le_antisymm
  · exact le_inf (LocF.locF_mono 𝔭 inf_le_left) (LocF.locF_mono 𝔭 inf_le_right)
  · rintro x ⟨h1, h2⟩
    obtain ⟨s, hs, hsx⟩ := (LocalSpans.mem_locF 𝔭 A x).1 h1
    obtain ⟨t, ht, htx⟩ := (LocalSpans.mem_locF 𝔭 B x).1 h2
    refine (LocalSpans.mem_locF 𝔭 _ x).2 ⟨s * t, fun h => (h𝔭.isPrime.mem_or_mem h).elim hs ht, ?_, ?_⟩
    · rw [mul_comm, map_mul, mul_smul]
      exact A.smul_mem _ hsx
    · rw [map_mul, mul_smul]
      exact B.smul_mem _ htx

theorem isLattice_inf {M₁ M₂ : Submodule (𝓞 K) V} (hM₁ : Submodule.IsLattice K M₁)
    (hM₂ : Submodule.IsLattice K M₂) : Submodule.IsLattice K (M₁ ⊓ M₂) := by
  have := hM₁
  exact Submodule.IsLattice.inf_left K M₁ M₂

theorem finite_quot_inf {M₁ M₂ : Submodule (𝓞 K) V} (hM₁ : Submodule.IsLattice K M₁)
    (hM₂ : Submodule.IsLattice K M₂) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) :
    Finite (↥(locF 𝔭 M₁ ⊓ locF 𝔭 M₂) ⧸
      ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥(locF 𝔭 M₁ ⊓ locF 𝔭 M₂))) := by
  rw [← locF_inf_locF h𝔭]
  exact finite_quot (isLattice_inf hM₁ hM₂) h𝔭 k

theorem apply_mem_of_mem_autSub {h : V →ₗ⋆[K] V →ₗ[K] K} {A : Submodule (𝓞 K) V} {g : V ≃ₗ[K] V}
    (hg : g ∈ autSub h A) {z : V} (hz : z ∈ A) : g z ∈ A := by
  have h2 : A.map ((g : V →ₗ[K] V).restrictScalars (𝓞 K)) = A := hg.2
  rw [← h2]
  exact Submodule.mem_map_of_mem hz

theorem apply_mem_smul_of_mem_autSub {h : V →ₗ⋆[K] V →ₗ[K] K} {A : Submodule (𝓞 K) V}
    {g : V ≃ₗ[K] V} (hg : g ∈ autSub h A) (I : Ideal (𝓞 K)) {z : V} (hz : z ∈ I • A) :
    g z ∈ I • A := by
  have h2 : A.map ((g : V →ₗ[K] V).restrictScalars (𝓞 K)) = A := hg.2
  have h1 : g z ∈ (I • A).map ((g : V →ₗ[K] V).restrictScalars (𝓞 K)) := Submodule.mem_map_of_mem hz
  rwa [Submodule.map_smul'', h2] at h1

theorem congr_apply_mem {M₁ M₂ : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    {r₁ r₂ j : ℕ} (h1 : ((extP K 𝔭) ^ r₁ • locF 𝔭 M₁ : Submodule (𝓞 K) V) ≤ locF 𝔭 M₂)
    (h2 : ((extP K 𝔭) ^ r₂ • locF 𝔭 M₂ : Submodule (𝓞 K) V) ≤ locF 𝔭 M₁) (hj : r₂ + r₁ ≤ j)
    (g : V ≃ₗ[K] V)
    (hg : ∀ z ∈ locF 𝔭 M₁, g z - z ∈ ((extP K 𝔭) ^ j • locF 𝔭 M₁ : Submodule (𝓞 K) V))
    {z : V} (hz : z ∈ locF 𝔭 M₂) : g z ∈ locF 𝔭 M₂ := by
  obtain ⟨π, hπ, hπ'⟩ := D2.exists_unif h𝔭
  have hz1 : algebraMap F K (π : F) ^ r₂ • z ∈ locF 𝔭 M₁ :=
    h2 ((D2.mem_smul_iff_unif h𝔭 hπ hπ' M₂).2 ⟨z, hz, rfl⟩)
  have h3 := pow_smul_anti 𝔭 (locF 𝔭 M₁) hj (hg _ hz1)
  rw [pow_add, Submodule.mul_smul] at h3
  have h4 := Submodule.smul_mono (le_refl (extP K 𝔭 ^ r₂)) h1 h3
  obtain ⟨w, hw, e⟩ := (D2.mem_smul_iff_unif h𝔭 hπ hπ' M₂).1 h4
  rw [map_smul, ← smul_sub] at e
  have e' : g z - z = w :=
    smul_right_injective V (pow_ne_zero r₂ (D2.unif_ne_zero (K := K) hπ')) e
  have : g z = w + z := by rw [← e']; abel
  rw [this]
  exact add_mem hw hz

theorem exists_congr_mem_autSub (h : V →ₗ⋆[K] V →ₗ[K] K) {M₁ M₂ : Submodule (𝓞 K) V}
    (hM₁ : Submodule.IsFullLattice K M₁) (hM₂ : Submodule.IsFullLattice K M₂) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) :
    ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ g ∈ autSub h (locF 𝔭 M₁),
      (∀ z ∈ locF 𝔭 M₁, g z - z ∈ ((extP K 𝔭) ^ j • locF 𝔭 M₁ : Submodule (𝓞 K) V)) →
      g ∈ autSub h (locF 𝔭 M₂) := by
  obtain ⟨r₁, h1⟩ := exists_pow_smul_le hM₁.toIsLattice hM₂ h𝔭
  obtain ⟨r₂, h2⟩ := exists_pow_smul_le hM₂.toIsLattice hM₁ h𝔭
  refine ⟨r₂ + r₁, fun j hj g hg hc => ⟨hg.1, ?_⟩⟩
  apply le_antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact congr_apply_mem h𝔭 h1 h2 hj g hc hz
  · intro x hx
    have hc' : ∀ z ∈ locF 𝔭 M₁,
        g.symm z - z ∈ ((extP K 𝔭) ^ j • locF 𝔭 M₁ : Submodule (𝓞 K) V) := by
      intro z hz
      have hz' : g.symm z ∈ locF 𝔭 M₁ := apply_mem_of_mem_autSub (inv_mem hg) hz
      have := neg_mem (hc _ hz')
      rwa [LinearEquiv.apply_symm_apply, neg_sub] at this
    exact ⟨g.symm x, congr_apply_mem h𝔭 h1 h2 hj g.symm hc' hx, by simp⟩

theorem orbCount_eq_relIndex (h : V →ₗ⋆[K] V →ₗ[K] K) (A B : Submodule (𝓞 K) V) :
    orbCount h A B = (autSub h B).relIndex (autSub h A) := by
  let _ : MulAction (V ≃ₗ[K] V) (Submodule (𝓞 K) V) :=
    { smul := fun g L => Formalism.HermitianLatticesTheory.gmap g L
      one_smul := autSub_gmap_one
      mul_smul := autSub_gmap_mul }
  have hst : MulAction.stabilizer ↥(autSub h A) B = (autSub h B).subgroupOf (autSub h A) := by
    ext g
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
    constructor
    · intro hg
      exact ⟨g.2.1, hg⟩
    · intro hg
      exact hg.2
  rw [Subgroup.relIndex, ← hst, Subgroup.index_eq_card,
    ← Nat.card_congr (MulAction.orbitEquivQuotientStabilizer _ B)]
  unfold orbCount
  refine Nat.card_congr (Equiv.subtypeEquivRight ?_)
  intro C
  constructor
  · rintro ⟨g, hg, hA, hB⟩
    exact ⟨⟨g, hg, hA⟩, hB⟩
  · rintro ⟨⟨g, hg, hA⟩, hB⟩
    exact ⟨g, hg, hA, hB⟩

theorem relIndex_ne_zero_of_map {G X : Type*} [Group G] [Finite X] (H Γ : Subgroup G) (f : H → X)
    (hf : ∀ a b : H, f a = f b → (a : G)⁻¹ * b ∈ Γ) : Γ.relIndex H ≠ 0 := by
  classical
  show (Γ.subgroupOf H).index ≠ 0
  have hfin : Finite (H ⧸ Γ.subgroupOf H) := by
    let g : Set.range f → H ⧸ Γ.subgroupOf H := fun x => QuotientGroup.mk x.2.choose
    apply Finite.of_surjective g
    intro q
    induction q using QuotientGroup.induction_on with
    | H a =>
      refine ⟨⟨f a, a, rfl⟩, ?_⟩
      show QuotientGroup.mk _ = QuotientGroup.mk a
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
      exact hf _ _ (⟨f a, a, rfl⟩ : Set.range f).2.choose_spec
  exact Subgroup.index_ne_zero_of_finite

def resA {h : V →ₗ⋆[K] V →ₗ[K] K} {A : Submodule (𝓞 K) V} (g : autSub h A) : ↥A →ₗ[𝓞 K] ↥A :=
  (((g : V ≃ₗ[K] V) : V →ₗ[K] V).restrictScalars (𝓞 K)).restrict
    (fun _ hz => apply_mem_of_mem_autSub g.2 hz)

def redA {h : V →ₗ⋆[K] V →ₗ[K] K} {A : Submodule (𝓞 K) V} (I : Ideal (𝓞 K)) (g : autSub h A) :
    (↥A ⧸ (I • ⊤ : Submodule (𝓞 K) ↥A)) →ₗ[𝓞 K] (↥A ⧸ (I • ⊤ : Submodule (𝓞 K) ↥A)) :=
  Submodule.mapQ _ _ (resA g) (by
    rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top)

theorem sub_mem_of_redA_eq {h : V →ₗ⋆[K] V →ₗ[K] K} {A : Submodule (𝓞 K) V} (I : Ideal (𝓞 K))
    {a b : autSub h A} (e : redA I a = redA I b) {z : V} (hz : z ∈ A) :
    (b : V ≃ₗ[K] V) z - (a : V ≃ₗ[K] V) z ∈ I • A := by
  have h1 := congrArg (fun φ => φ (Submodule.Quotient.mk (⟨z, hz⟩ : ↥A))) e
  simp only [redA, Submodule.mapQ_apply] at h1
  rw [eq_comm, Submodule.Quotient.eq] at h1
  have h2 := Submodule.mem_map_of_mem (f := A.subtype) h1
  rw [Submodule.map_smul'', Submodule.map_subtype_top] at h2
  simp only [Submodule.subtype_apply] at h2
  exact h2

theorem relIndex_autSub_ne_zero (h : V →ₗ⋆[K] V →ₗ[K] K) {M₁ M₂ : Submodule (𝓞 K) V}
    (hM₁ : Submodule.IsFullLattice K M₁) (hM₂ : Submodule.IsFullLattice K M₂) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) :
    (autSub h (locF 𝔭 M₂)).relIndex (autSub h (locF 𝔭 M₁)) ≠ 0 := by
  obtain ⟨j, hj⟩ := exists_congr_mem_autSub h hM₁ hM₂ h𝔭
  have := finite_quot hM₁.toIsLattice h𝔭 j
  have : Finite ((↥(locF 𝔭 M₁) ⧸ ((extP K 𝔭) ^ j • ⊤ : Submodule (𝓞 K) ↥(locF 𝔭 M₁))) →ₗ[𝓞 K]
      (↥(locF 𝔭 M₁) ⧸ ((extP K 𝔭) ^ j • ⊤ : Submodule (𝓞 K) ↥(locF 𝔭 M₁)))) :=
    Finite.of_injective _ DFunLike.coe_injective
  refine relIndex_ne_zero_of_map _ _ (redA (extP K 𝔭 ^ j)) fun a b e => ?_
  refine hj j le_rfl _ (mul_mem (inv_mem a.2) b.2) fun z hz => ?_
  have h1 := apply_mem_smul_of_mem_autSub (inv_mem a.2) _ (sub_mem_of_redA_eq _ e hz)
  have h2 : ((a : V ≃ₗ[K] V)⁻¹ * (b : V ≃ₗ[K] V)) z - z =
      (a : V ≃ₗ[K] V)⁻¹ ((b : V ≃ₗ[K] V) z - (a : V ≃ₗ[K] V) z) := by
    rw [map_sub]
    change _ = (a : V ≃ₗ[K] V).symm _ - (a : V ≃ₗ[K] V).symm _
    rw [LinearEquiv.symm_apply_apply]
    rfl
  rw [h2]
  exact h1

end Formalism.HermitianLattices.Ext.L3.LIOrb
