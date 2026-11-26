module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.InLZeroIff

@[expose] public section

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsIntegralLatOfForall
open NumberField Module Formalism.HermitianLattices.Ext.L3.SplitA

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.GoodGenusOrbits

variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

open UnimodularLocalization GoodPrimeTerms SplitBAux

theorem gmap_inj (g : V ≃ₗ[K] V) {A B : Submodule (𝓞 K) V} :
    Formalism.HermitianLatticesTheory.gmap g A = Formalism.HermitianLatticesTheory.gmap g B ↔ A = B :=
  (gmap_injective g).eq_iff

theorem fibLoc_gmap (hs : h.IsSymm) (S : VecSplit h h') (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F))
    {g' : V' ≃ₗ[K] V'} (hg' : g' ∈ Formalism.HermitianLatticesTheory.isom h') (T : Submodule (𝓞 K) V') :
    fibLoc S L 𝔭 (Formalism.HermitianLatticesTheory.gmap g' T) = fibLoc S L 𝔭 T := by
  have hG : extOf S g' ∈ Formalism.HermitianLatticesTheory.isom h := extOf_mem_isom hs S hg'
  let e : Submodule (𝓞 K) V ≃ Submodule (𝓞 K) V :=
    { toFun := Formalism.HermitianLatticesTheory.gmap (extOf S g')
      invFun := Formalism.HermitianLatticesTheory.gmap (extOf S g').symm
      left_inv := fun Λ => Formalism.HermitianLatticesTheory.isomAct_gmap_symm _ Λ
      right_inv := fun Λ => Formalism.HermitianLatticesTheory.isomAct_gmap_symm (extOf S g').symm Λ }
  unfold fibLoc
  refine (Nat.card_congr (Equiv.subtypeEquiv e ?_)).symm
  intro Λ
  change _ ↔ (locF 𝔭 (Formalism.HermitianLatticesTheory.gmap (extOf S g') Λ) = Formalism.HermitianLatticesTheory.gmap (extOf S g') Λ ∧
    (∃ g ∈ Formalism.HermitianLatticesTheory.isom h, Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L) = Formalism.HermitianLatticesTheory.gmap (extOf S g') Λ) ∧
    S.x₀ ∈ Formalism.HermitianLatticesTheory.gmap (extOf S g') Λ ∧
    S.cut (Formalism.HermitianLatticesTheory.gmap (extOf S g') Λ) = locF 𝔭 (Formalism.HermitianLatticesTheory.gmap g' T))
  rw [← LocalizedFibreSets.gmap_locF, gmap_inj, StabilizerLattices.cut_gmap_extOf, ← LocalizedFibreSets.gmap_locF, gmap_inj,
    Formalism.HermitianLatticesTheory.isomAct_mem_gmap, symm_fix (extOf_x₀ S g')]
  refine and_congr_right fun _ => and_congr_left fun _ => ?_
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨extOf S g' * g, Subgroup.mul_mem _ hG hg, autSub_gmap_mul _ _ _⟩
  · rintro ⟨g, hg, e1⟩
    refine ⟨(extOf S g')⁻¹ * g, Subgroup.mul_mem _ (Subgroup.inv_mem _ hG) hg, ?_⟩
    rw [autSub_gmap_mul, e1, ← autSub_gmap_mul, inv_mul_cancel, autSub_gmap_one]

theorem fibLoc_eq_of_rel (hs : h.IsSymm) (S : VecSplit h h') (L : Submodule (𝓞 K) V)
    {𝔭 : Ideal (𝓞 F)} {M M₁ : Submodule (𝓞 K) V'}
    (H : ∃ g ∈ Formalism.HermitianLatticesTheory.isom h', Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 M) = locF 𝔭 M₁) :
    fibLoc S L 𝔭 M₁ = fibLoc S L 𝔭 M := by
  obtain ⟨g, hg, e⟩ := H
  rw [← fibLoc_locF S L 𝔭 M₁, ← e, fibLoc_gmap hs S L 𝔭 hg, fibLoc_locF]

theorem sameGenus_iff (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (A B : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.SameGenus h A B ↔ ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal},
      ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, Formalism.HermitianLatticesTheory.gmap g (locF 𝔭.1 A) = locF 𝔭.1 B := by
  constructor
  · rintro H ⟨𝔭, h𝔭⟩
    obtain ⟨P, hP, rfl⟩ := LocalizedFibreSets.exists_max_over (K := K) h𝔭
    rw [locF_eq_loc hK hF hP, locF_eq_loc hK hF hP]
    exact H P hP
  · intro H P hP
    have hm : (P.comap (algebraMap (𝓞 F) (𝓞 K))).IsMaximal :=
      Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := 𝓞 F) P
    have := H ⟨_, hm⟩
    rwa [locF_eq_loc hK hF hP, locF_eq_loc hK hF hP] at this

theorem isIntegralLat_of_forall {W : Type} [AddCommGroup W] [Module K W] [Module (𝓞 K) W]
    [IsScalarTower (𝓞 K) K W] {h₀ : W →ₗ⋆[K] W →ₗ[K] K} {M : Submodule (𝓞 K) W}
    (H : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, IsIntegralAt 𝔭.1 h₀ (locF 𝔭.1 M)) :
    Formalism.HermitianLatticesTheory.IsIntegralLat h₀ M := by
  intro x hx y hy
  rw [← LocF.iInf_locF (F := F) (1 : Submodule (𝓞 K) K), Submodule.mem_iInf]
  exact fun 𝔭 => H 𝔭 x (LocF.le_locF _ _ hx) y (LocF.le_locF _ _ hy)

theorem isIntegralAt_gmap {𝔭 : Ideal (𝓞 F)} {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h)
    {T : Submodule (𝓞 K) V} (hT : IsIntegralAt 𝔭 h T) : IsIntegralAt 𝔭 h (Formalism.HermitianLatticesTheory.gmap g T) := by
  intro x hx y hy
  rw [Formalism.HermitianLatticesTheory.isomAct_mem_gmap] at hx hy
  rw [← isom_apply (symm_mem_isom hg)]
  exact hT _ hx _ hy

theorem tprod_natCast_ne_zero {ι : Type*} (f : ι → ℕ) (hf : ∀ i, f i ≠ 0) :
    (∏' i, (f i : ℝ)) ≠ 0 := by
  by_cases hm : Multipliable fun i => (f i : ℝ)
  · have h1 : (1 : ℝ) ≤ ∏' i, (f i : ℝ) := by
      refine ge_of_tendsto hm.hasProd (Filter.Eventually.of_forall fun s => ?_)
      have : (1 : ℝ) ≤ ((∏ i ∈ s, f i : ℕ) : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i _ => hf i)
      simpa using this
    linarith
  · rw [tprod_eq_one_of_not_multipliable hm]
    exact one_ne_zero

def Good (F : Type) [Field F] [NumberField F] [Algebra F K] (S : VecSplit h h')
    (L : Submodule (𝓞 K) V) (M : Submodule (𝓞 K) V') : Prop :=
  Submodule.IsLattice K M ∧ ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, fibLoc S L 𝔭.1 M ≠ 0

theorem Good.integral (hF : IsFixF K F) {S : VecSplit h h'} {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    {M : Submodule (𝓞 K) V'} (hM : Good F S L M) : Formalism.HermitianLatticesTheory.IsIntegralLat h' M := by
  apply isIntegralLat_of_forall (F := F)
  intro 𝔭
  obtain ⟨C, -, hCi, e⟩ := exists_lattice_of_fibLoc_ne_zero S hL hLi (hM.2 𝔭)
  rw [← e]
  exact isIntegralAt_locF 𝔭.2.isPrime hF hCi

private theorem exists_full_lattice_of_fibLoc_ne_zero (S : VecSplit h h')
    {L : Submodule (𝓞 K) V} (hL : Submodule.IsFullLattice K L) {𝔭 : Ideal (𝓞 F)}
    {T : Submodule (𝓞 K) V'} (hT : fibLoc S L 𝔭 T ≠ 0) :
    ∃ C : Submodule (𝓞 K) V', Submodule.IsFullLattice K C ∧ locF 𝔭 C = locF 𝔭 T := by
  obtain ⟨g, -, -, e⟩ := exists_of_fibLoc_ne_zero S hT
  have hLg : Submodule.IsFullLattice K (Formalism.HermitianLatticesTheory.gmap g L) := by
    refine { toIsLattice := Submodule.IsLattice.of_fg K (hL.fg.map _), span_eq_top := ?_ }
    change Submodule.span K ((g : V →ₗ[K] V) '' (L : Set V)) = ⊤
    rw [Submodule.span_image, hL.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
    exact g.surjective
  exact ⟨_, StabilizerLattices.isFullLattice_cut S hLg, e⟩

theorem Good.isFullLattice {S : VecSplit h h'} {L : Submodule (𝓞 K) V}
    {M : Submodule (𝓞 K) V'} (hM : Good F S L M) (hL : Submodule.IsFullLattice K L) :
    Submodule.IsFullLattice K M := by
  obtain ⟨𝔭, h𝔭⟩ := Ideal.exists_maximal (α := 𝓞 F)
  obtain ⟨C, hC, e⟩ := exists_full_lattice_of_fibLoc_ne_zero S hL (hM.2 ⟨𝔭, h𝔭⟩)
  refine { toIsLattice := hM.1, span_eq_top := ?_ }
  rw [eq_top_iff, ← hC.span_eq_top, Submodule.span_le]
  intro x hx
  have hx' : x ∈ locF 𝔭 M := e ▸ LocF.le_locF 𝔭 C hx
  obtain ⟨t, ht, htx⟩ := (LocF.mem_locF_iff h𝔭.isPrime M x).mp hx'
  have htK : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) ≠ 0 := by
    rw [map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K),
      map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K))]
    exact fun e₀ => ht (e₀ ▸ 𝔭.zero_mem)
  apply ((Submodule.span K (M : Set V')).smul_mem_iff htK).mp
  rw [algebraMap_smul]
  exact Submodule.subset_span htx

theorem Good.nonempty (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) {S : VecSplit h h'} {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    {M : Submodule (𝓞 K) V'} (hM : Good F S L M) : (fibG S L M).Nonempty := by
  letI := hL
  letI := hM.isFullLattice hL
  have h1 := card_fibG_eq_prod (F := F) (L := L) (Λ' := M) hK hF hs hd S inferInstance hLi inferInstance
  have h2 := tprod_natCast_ne_zero _ hM.2
  rw [← h1] at h2
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  apply h2
  rw [hne]
  simp

theorem Good.of_genus (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    {S : VecSplit h h'} {L : Submodule (𝓞 K) V} {M M₁ : Submodule (𝓞 K) V'}
    (hM : Good F S L M) (h1 : M₁ ∈ Formalism.HermitianLatticesTheory.genus h' M) : Good F S L M₁ :=
  ⟨h1.1.toIsLattice, fun 𝔭 => by
    rw [fibLoc_eq_of_rel hs S L ((sameGenus_iff hK hF M M₁).mp h1.2 𝔭)]
    exact hM.2 𝔭⟩

theorem exists_patch (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L)
    {A : Submodule (𝓞 K) V'} (hA : Submodule.IsFullLattice K A)
    (Z : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal})
    (τ : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} → Submodule (𝓞 K) V')
    (hτ : ∀ 𝔭 ∈ Z, locF 𝔭.1 (τ 𝔭) = τ 𝔭 ∧ fibLoc S L 𝔭.1 (τ 𝔭) ≠ 0)
    (hZ : ∀ 𝔭 ∉ Z, fibLoc S L 𝔭.1 A ≠ 0) :
    ∃ M, Good F S L M ∧ (∀ 𝔭 ∈ Z, locF 𝔭.1 M = τ 𝔭) ∧ ∀ 𝔭 ∉ Z, locF 𝔭.1 M = locF 𝔭.1 A := by
  obtain ⟨M, ⟨hMl, h1, h2⟩, -⟩ := exists_unique_patch hK hF hA Z τ (fun 𝔭 h𝔭 => by
    obtain ⟨C, hC, e⟩ := exists_full_lattice_of_fibLoc_ne_zero S hL (hτ 𝔭 h𝔭).2
    exact ⟨(hτ 𝔭 h𝔭).1, C, hC, e.trans (hτ 𝔭 h𝔭).1⟩)
  refine ⟨M, ⟨hMl, fun 𝔭 => ?_⟩, h1, h2⟩
  by_cases h𝔭 : 𝔭 ∈ Z
  · rw [fibLoc_congr S L (T' := τ 𝔭) (by rw [h1 𝔭 h𝔭, (hτ 𝔭 h𝔭).1])]
    exact (hτ 𝔭 h𝔭).2
  · rw [fibLoc_congr S L (h2 𝔭 h𝔭)]
    exact hZ 𝔭 h𝔭

open scoped Formalism.HermitianLattices.Ext.L3.StabilizerLattices in
theorem exists_locReps (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    {M₀ : Submodule (𝓞 K) V'} (hM₀ : Good F S L M₀) (𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) :
    ∃ s, IsLocReps S L 𝔭.1 s := by
  classical
  letI := hL
  obtain ⟨s', hs'⟩ := exists_fibReps (L := L) hK hs hd S inferInstance hLi
  let A : Set (Submodule (𝓞 K) V') :=
    {T | locF 𝔭.1 T = T ∧ IsIntegralAt 𝔭.1 h' T ∧ fibLoc S L 𝔭.1 T ≠ 0}
  have hA : ∀ g : Formalism.HermitianLatticesTheory.isom h', ∀ T ∈ A, g • T ∈ A := by
    rintro g T ⟨h1, h2, h3⟩
    refine ⟨?_, isIntegralAt_gmap g.2 h2, ?_⟩
    · change locF 𝔭.1 (Formalism.HermitianLatticesTheory.gmap g.1 T) = Formalism.HermitianLatticesTheory.gmap g.1 T
      rw [← LocalizedFibreSets.gmap_locF, h1]
    · change fibLoc S L 𝔭.1 (Formalism.HermitianLatticesTheory.gmap g.1 T) ≠ 0
      rwa [fibLoc_gmap hs S L 𝔭.1 g.2]
  obtain ⟨s, hs1, hs2⟩ := OrbSum.exists_reps_of_cover (G := Formalism.HermitianLatticesTheory.isom h') A hA
    {T | T ∈ A ∧ T ∈ s'.image (locF 𝔭.1)}
    ((s'.image (locF 𝔭.1)).finite_toSet.subset fun T hT => hT.2) (fun c hc => hc.1) (by
      intro T hT
      obtain ⟨M, hM, h1, -⟩ := exists_patch hK hF S hL (hM₀.isFullLattice hL) {𝔭} (fun _ => T)
        (fun 𝔮 h𝔮 => by
          rw [Finset.mem_singleton] at h𝔮
          subst h𝔮
          exact ⟨hT.1, hT.2.2⟩) (fun 𝔮 _ => hM₀.2 𝔮)
      obtain ⟨Λ₀, ⟨hΛ₀, g, hg, e⟩, -⟩ := hs'.2 M (hM.nonempty hK hF hs hd hL hLi)
      have e2 : (⟨g, hg⟩ : Formalism.HermitianLatticesTheory.isom h') • locF 𝔭.1 Λ₀ = T := by
        change Formalism.HermitianLatticesTheory.gmap g (locF 𝔭.1 Λ₀) = T
        rw [LocalizedFibreSets.gmap_locF, e, h1 𝔭 (Finset.mem_singleton_self _)]
      refine ⟨locF 𝔭.1 Λ₀, ⟨?_, Finset.mem_image_of_mem _ hΛ₀⟩, ⟨g, hg⟩, e2⟩
      have := hA (⟨g, hg⟩ : Formalism.HermitianLatticesTheory.isom h')⁻¹ T hT
      rwa [← e2, inv_smul_smul] at this)
  refine ⟨s, hs1, fun T h1 h2 h3 => ?_⟩
  obtain ⟨T₀, ⟨hT₀, g, hg⟩, hu⟩ := hs2 T ⟨h1, h2, h3⟩
  exact ⟨T₀, ⟨hT₀, g.1, g.2, hg⟩, fun T₁ ⟨h4, g₁, hg₁, e₁⟩ => hu T₁ ⟨h4, ⟨g₁, hg₁⟩, e₁⟩⟩

theorem isClassReps_filter (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    {s' : Finset (Submodule (𝓞 K) V')} (hs' : IsFibReps S L s')
    {M : Submodule (𝓞 K) V'} (hM : Good F S L M)
    [DecidablePred fun Λ' : Submodule (𝓞 K) V' => Formalism.HermitianLatticesTheory.SameGenus h' M Λ'] :
    Formalism.ThetaLiftIndependence.IsClassReps h' M (s'.filter fun Λ' => Formalism.HermitianLatticesTheory.SameGenus h' M Λ') := by
  obtain ⟨he, hi, -⟩ :=
    Formalism.HermitianLatticesTheory.genusBasic (𝓞 K) K V' h' (S.isSymm hs) Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range
  constructor
  · intro Λ' hΛ'
    rw [Finset.mem_filter] at hΛ'
    obtain ⟨Λ, hΛ, -, rfl⟩ := hs'.1 Λ' hΛ'.1
    exact ⟨StabilizerLattices.isFullLattice_cut S hΛ.1, hΛ'.2⟩
  · intro M₁ hM₁
    obtain ⟨Λ₀, ⟨hΛ₀, g, hg, e⟩, hu⟩ :=
      hs'.2 M₁ ((hM.of_genus hK hF hs hM₁).nonempty hK hF hs hd hL hLi)
    refine ⟨Λ₀, ⟨Finset.mem_filter.mpr ⟨hΛ₀, ?_⟩, g, hg, e⟩, ?_⟩
    · have h1 := hi Λ₀ g hg
      rw [e] at h1
      exact he.trans hM₁.2 (he.symm h1)
    · rintro Λ₁ ⟨h1, h2⟩
      exact hu Λ₁ ⟨(Finset.mem_filter.mp h1).1, h2⟩

end Formalism.HermitianLattices.Ext.L3.GoodGenusOrbits
end
end

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.SumLocRepsEq
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.BrB

section One

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

variable {h : V →ₗ⋆[K] V →ₗ[K] K}

theorem akCount_congr {A B : Submodule (𝓞 K) V} (e : ↥A ≃ₗ[𝓞 K] ↥B)
    (he : ∀ x y : ↥A, h (e x : V) (e y : V) = h (x : V) (y : V)) (𝔭 : Ideal (𝓞 F)) (k : ℕ) :
    akCount h B 𝔭 k = akCount h A 𝔭 k := by
  have hmap : ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥A).map (e : ↥A →ₗ[𝓞 K] ↥B) =
      ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥B) := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]
  let ε := Submodule.Quotient.equiv _ _ e hmap
  have hε : ∀ x : ↥A, ε (Submodule.Quotient.mk x) = Submodule.Quotient.mk (e x) := fun x => rfl
  unfold akCount
  refine (Nat.card_congr (Equiv.subtypeEquiv ε.conj.toEquiv ?_)).symm
  intro X
  have hX : ∀ x : ↥A, (ε.conj X) (Submodule.Quotient.mk (e x)) = ε (X (Submodule.Quotient.mk x)) := by
    intro x
    rw [LinearEquiv.conj_apply_apply, ← hε, LinearEquiv.symm_apply_apply]
  constructor
  · intro H x y x' y' h1 h2
    obtain ⟨x, rfl⟩ := e.surjective x
    obtain ⟨y, rfl⟩ := e.surjective y
    obtain ⟨x', rfl⟩ := e.surjective x'
    obtain ⟨y', rfl⟩ := e.surjective y'
    rw [he, he]
    refine H x y x' y' ?_ ?_
    · apply ε.injective
      rw [hε, ← hX]
      exact h1
    · apply ε.injective
      rw [hε, ← hX]
      exact h2
  · intro H x y x' y' h1 h2
    rw [← he, ← he x y]
    refine H (e x) (e y) (e x') (e y') ?_ ?_
    · change _ = (ε.conj X) _
      rw [hX, ← h1, hε]
    · change _ = (ε.conj X) _
      rw [hX, ← h2, hε]

theorem akCount_gmap {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) (T : Submodule (𝓞 K) V)
    (𝔭 : Ideal (𝓞 F)) (k : ℕ) : akCount h (Formalism.HermitianLatticesTheory.gmap g T) 𝔭 k = akCount h T 𝔭 k :=
  akCount_congr (A := T) (B := Formalism.HermitianLatticesTheory.gmap g T) ((g.restrictScalars (𝓞 K)).submoduleMap T)
    (fun x y => hg (x : V) (y : V)) 𝔭 k

theorem alphaL_gmap {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) (T : Submodule (𝓞 K) V)
    (𝔭 : Ideal (𝓞 F)) : alphaL h (Formalism.HermitianLatticesTheory.gmap g T) 𝔭 = alphaL h T 𝔭 := by
  unfold alphaL
  simp only [akCount_gmap hg]

end One

variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

theorem localFactor_map' {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) (T : Submodule (𝓞 K) V)
    (𝔭 : Ideal (𝓞 F)) : lamP h (Formalism.HermitianLatticesTheory.gmap g T) 𝔭 = lamP h T 𝔭 := by
  unfold lamP
  rw [UnimodularLocalization.vd_gmap hg, alphaL_gmap hg]

theorem sum_locReps_eq (hs : h.IsSymm) (S : VecSplit h h') (L : Submodule (𝓞 K) V)
    (𝔭 : Ideal (𝓞 F)) {s s' : Finset (Submodule (𝓞 K) V')} (hsr : IsLocReps S L 𝔭 s)
    (hsr' : IsLocReps S L 𝔭 s') :
    ∑ T ∈ s, (fibLoc S L 𝔭 T : ℝ) * lamP h' T 𝔭 = ∑ T ∈ s', (fibLoc S L 𝔭 T : ℝ) * lamP h' T 𝔭 := by
  have ex : ∀ T ∈ s, ∃! T₀, T₀ ∈ s' ∧ ∃ g ∈ Formalism.HermitianLatticesTheory.isom h', Formalism.HermitianLatticesTheory.gmap g T₀ = T :=
    fun T hT => hsr'.2 T (hsr.1 T hT).1 (hsr.1 T hT).2.1 (hsr.1 T hT).2.2
  refine Finset.sum_bij (fun T hT => (ex T hT).choose) ?_ ?_ ?_ ?_
  · exact fun T hT => (ex T hT).choose_spec.1.1
  · intro T₁ h1 T₂ h2 e
    obtain ⟨g₁, hg₁, e₁⟩ := (ex T₁ h1).choose_spec.1.2
    obtain ⟨g₂, hg₂, e₂⟩ := (ex T₂ h2).choose_spec.1.2
    simp only at e
    rw [← e] at e₂
    have hu := hsr.2 T₂ (hsr.1 T₂ h2).1 (hsr.1 T₂ h2).2.1 (hsr.1 T₂ h2).2.2
    refine hu.unique ⟨h1, g₂ * g₁⁻¹, Subgroup.mul_mem _ hg₂ (Subgroup.inv_mem _ hg₁), ?_⟩
      ⟨h2, 1, Subgroup.one_mem _, autSub_gmap_one _⟩
    rw [← e₁, ← autSub_gmap_mul, mul_assoc, inv_mul_cancel, mul_one, e₂]
  · intro T₀ h0
    obtain ⟨T, ⟨hT, g, hg, e⟩, -⟩ :=
      hsr.2 T₀ (hsr'.1 T₀ h0).1 (hsr'.1 T₀ h0).2.1 (hsr'.1 T₀ h0).2.2
    refine ⟨T, hT, ?_⟩
    refine (ex T hT).unique (ex T hT).choose_spec.1 ⟨h0, g⁻¹, Subgroup.inv_mem _ hg, ?_⟩
    rw [← e, ← autSub_gmap_mul, inv_mul_cancel, autSub_gmap_one]
  · intro T hT
    obtain ⟨g, hg, e⟩ := (ex T hT).choose_spec.1.2
    conv_lhs => rw [← e, GoodGenusOrbits.fibLoc_gmap hs S L 𝔭 hg, localFactor_map' hg]

theorem psiP_eq_sum' (hs : h.IsSymm) (S : VecSplit h h') (L : Submodule (𝓞 K) V)
    (𝔭 : Ideal (𝓞 F)) {s : Finset (Submodule (𝓞 K) V')} (hsr : IsLocReps S L 𝔭 s) :
    psiP S L 𝔭 = ∑ T ∈ s, (fibLoc S L 𝔭 T : ℝ) * lamP h' T 𝔭 := by
  have hex : ∃ s, IsLocReps S L 𝔭 s := ⟨s, hsr⟩
  unfold psiP
  rw [dite_eq_left hex]
  exact sum_locReps_eq hs S L 𝔭 hex.choose_spec hsr

end Formalism.HermitianLattices.Ext.L3.BrB
end
end

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsLatticeOfFibReps
open NumberField Module Formalism.HermitianLattices.Ext.L3.SplitA

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.LocalFactorEquality

variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

open UnimodularLocalization GoodPrimeTerms GoodGenusOrbits

theorem finite_vF_ne_zero {n : 𝓞 F} (hn : n ≠ 0) :
    {𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} | vF 𝔭.1 n ≠ 0}.Finite := by
  have hnF : ¬ IsField (𝓞 F) := NumberField.RingOfIntegers.not_isField F
  have hI : Ideal.span {n} ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  let f : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} → IsDedekindDomain.HeightOneSpectrum (𝓞 F) :=
    fun 𝔭 => ⟨𝔭.1, 𝔭.2.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField 𝔭.2 hnF⟩
  have hf : Function.Injective f := fun a b h =>
    Subtype.ext (congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal h)
  refine ((Ideal.finite_factors hI).preimage hf.injOn).subset ?_
  intro 𝔭 h𝔭
  simp only [Set.mem_setOf_eq, Set.mem_preimage] at h𝔭 ⊢
  show 𝔭.1 ∣ Ideal.span {n}
  rw [Ideal.dvd_span_singleton]
  by_contra hmem
  apply h𝔭
  unfold vF

  have hset : {e : ℕ | n ∈ 𝔭.1 ^ e} = {0} := by
    ext e
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro he
      by_contra h0
      exact hmem (Ideal.pow_le_self h0 he)
    · rintro rfl
      simp
  rw [hset, csSup_singleton]

theorem psiP_eq (S : VecSplit h h') (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F))
    (hex : ∃ s, IsLocReps S L 𝔭 s) :
    psiP S L 𝔭 = ∑ T ∈ hex.choose, (fibLoc S L 𝔭 T : ℝ) * lamP h' T 𝔭 := by
  unfold psiP
  rw [dite_eq_left hex]

theorem psiP_eq_zero (S : VecSplit h h') (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F))
    (H : ∀ T, fibLoc S L 𝔭 T = 0) : psiP S L 𝔭 = 0 := by
  unfold psiP
  split_ifs with hs
  · simp [H]
  · rfl

theorem card_fibG_eq_zero (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {Λ' : Submodule (𝓞 K) V'}
    (hΛ' : Submodule.IsFullLattice K Λ') (𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal})
    (H : fibLoc S L 𝔭.1 Λ' = 0) : (Nat.card (fibG S L Λ') : ℝ) = 0 := by
  letI := hL
  letI := hΛ'
  rw [card_fibG_eq_prod (L := L) (Λ' := Λ') hK hF hs hd S inferInstance hLi inferInstance]
  exact tprod_of_exists_eq_zero ⟨𝔭, by rw [H]; simp⟩

theorem isFullLattice_of_fibReps (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    {s' : Finset (Submodule (𝓞 K) V')} (hs' : IsFibReps S L s') {Λ' : Submodule (𝓞 K) V'}
    (hΛ' : Λ' ∈ s') : Submodule.IsFullLattice K Λ' := by
  obtain ⟨Λ, hΛ, -, rfl⟩ := hs'.1 Λ' hΛ'
  exact StabilizerLattices.isFullLattice_cut S hΛ.1

theorem exists_norm_eq (hF : IsFixF K F) (hs : h.IsSymm) (S : VecSplit h h')
    {L : Submodule (𝓞 K) V} (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    (H : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, ∃ T, fibLoc S L 𝔭.1 T ≠ 0) :
    ∃ n : 𝓞 F, h S.x₀ S.x₀ = algebraMap F K (n : F) := by

  have hloc : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal},
      h S.x₀ S.x₀ ∈ locF 𝔭.1 (1 : Submodule (𝓞 K) K) := by
    intro 𝔭
    obtain ⟨T, hT⟩ := H 𝔭
    obtain ⟨g, hg, hx, -⟩ := UnimodularLocalization.exists_of_fibLoc_ne_zero S hT
    exact GoodPrimeTerms.isIntegralAt_locF 𝔭.2.isPrime hF (UnimodularLocalization.isIntegralLat_gmap hg hLi) _ hx _ hx
  have h1 : h S.x₀ S.x₀ ∈ (1 : Submodule (𝓞 K) K) := by
    rw [← LocF.iInf_locF (F := F) (1 : Submodule (𝓞 K) K)]
    exact Submodule.mem_iInf _ |>.mpr hloc
  obtain ⟨y, hy⟩ := Submodule.mem_one.mp h1

  have hc : conjO K y = y := by
    apply FaithfulSMul.algebraMap_injective (𝓞 K) K
    rw [BallB.algebraMap_conjO, hy]
    simpa [starRingEnd_apply] using hs.eq S.x₀ S.x₀
  obtain ⟨t, ht⟩ := (conjO_eq_iff_mem_range hF y).mp hc
  exact ⟨t, by rw [← hy, ← ht]; rfl⟩


open Classical in
theorem sum_genus (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {c : ℝ}
    (hc : MassConst K F (finrank K V - 1) c)
    {s' : Finset (Submodule (𝓞 K) V')} (hs' : IsFibReps S L s')
    {A : Submodule (𝓞 K) V'} (hA : Submodule.IsLattice K A) (hAi : Formalism.HermitianLatticesTheory.IsIntegralLat h' A)
    (Z : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal})
    (hZ1 : ∀ 𝔭 ∉ Z, fibLoc S L 𝔭.1 A = 1) (hZ2 : ∀ 𝔭 ∉ Z, vd h' A 𝔭.1 = 0)
    {M : Submodule (𝓞 K) V'} (hM : Good F S L M) (hMA : ∀ 𝔭 ∉ Z, locF 𝔭.1 M = locF 𝔭.1 A) :
    ∑ Λ' ∈ s'.filter (fun Λ' => Formalism.HermitianLatticesTheory.SameGenus h' M Λ'),
        (Nat.card (fibG S L Λ') : ℝ) / (Nat.card (Formalism.ThetaLiftIndependence.autL h' Λ') : ℝ) =
      c * ∏ 𝔭 ∈ Z, ((fibLoc S L 𝔭.1 (locF 𝔭.1 M) : ℝ) * lamP h' (locF 𝔭.1 M) 𝔭.1) := by
  have hs2 := S.isSymm hs
  have hd2 := S.isTotPosDef hd
  letI := hL
  have hMi := hM.integral hF hL.toIsLattice hLi
  have hMfull := hM.isFullLattice hL
  have hmass : Formalism.HermitianLatticesTheory.mass h' M = ∑ Λ' ∈ s'.filter (fun Λ' => Formalism.HermitianLatticesTheory.SameGenus h' M Λ'),
      ((Nat.card (Formalism.ThetaLiftIndependence.autL h' Λ') : ℕ) : ℝ)⁻¹ :=
    (Formalism.HermitianLatticesTheory.massBasic K V' h' hs2 (StabilizerLattices.trace_pos hd2) M hMfull).2.1 _
      (isClassReps_filter (L := L) hK hF hs hd S inferInstance hLi hs' hM)
  have hfr : finrank K V' = finrank K V - 1 := by
    have := S.finrank_add_one
    omega
  have hmc := hc V' h' M hs2 hd2 hfr hMfull hMi
  have e1 : ∀ Λ' ∈ s'.filter (fun Λ' => Formalism.HermitianLatticesTheory.SameGenus h' M Λ'),
      (Nat.card (fibG S L Λ') : ℝ) / (Nat.card (Formalism.ThetaLiftIndependence.autL h' Λ') : ℝ) =
        (∏ 𝔭 ∈ Z, (fibLoc S L 𝔭.1 (locF 𝔭.1 M) : ℝ)) *
          ((Nat.card (Formalism.ThetaLiftIndependence.autL h' Λ') : ℕ) : ℝ)⁻¹ := by
    intro Λ' hΛ'
    rw [Finset.mem_filter] at hΛ'
    letI := isFullLattice_of_fibReps S hs' hΛ'.1
    rw [card_fibG_eq_prod (F := F) (L := L) (Λ' := Λ') hK hF hs hd S inferInstance hLi inferInstance,
      div_eq_mul_inv]
    congr 1
    have e2 : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal},
        fibLoc S L 𝔭.1 Λ' = fibLoc S L 𝔭.1 (locF 𝔭.1 M) := fun 𝔭 => by
      rw [fibLoc_eq_of_rel hs S L ((sameGenus_iff hK hF M Λ').mp hΛ'.2 𝔭), fibLoc_locF]
    simp only [e2]
    apply tprod_eq_prod
    intro 𝔭 h𝔭
    rw [fibLoc_locF, fibLoc_congr S L (hMA 𝔭 h𝔭), hZ1 𝔭 h𝔭, Nat.cast_one]
  rw [Finset.sum_congr rfl e1, ← Finset.mul_sum, ← hmass, hmc, Finset.prod_mul_distrib]
  have e3 : lamG F h' M = ∏ 𝔭 ∈ Z, lamP h' (locF 𝔭.1 M) 𝔭.1 := by
    unfold lamG
    have e4 : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal},
        lamP h' M 𝔭.1 = lamP h' (locF 𝔭.1 M) 𝔭.1 := fun 𝔭 =>
      (localFactor_localField hK hF hs2 hd2 hM.1 hMi 𝔭.2).symm
    simp only [e4]
    apply tprod_eq_prod
    intro 𝔭 h𝔭
    rw [← e4 𝔭]
    apply localMassFactor_of_valuation_eq_zero hK hF hs2 hd2 hMfull hMi 𝔭.2
    rw [← vd_locF hK hF hs2 hd2 hM.1 hMi 𝔭.2, hMA 𝔭 h𝔭,
      vd_locF hK hF hs2 hd2 hA hAi 𝔭.2, hZ2 𝔭 h𝔭]
  rw [e3]
  ring

end Formalism.HermitianLattices.Ext.L3.LocalFactorEquality
end
end

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsLocReps
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.BrB

section One

variable {K V : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem finite_between {N D : Submodule (𝓞 K) V} (hN : Submodule.IsFullLattice K N)
    (hD : Submodule.IsLattice K D) (hND : N ≤ D) :
    {Λ : Submodule (𝓞 K) V | N ≤ Λ ∧ Λ ≤ D}.Finite := by
  have h1 := Formalism.HermitianLatticesTheory.finIntermediate V N.toAddSubgroup D.toAddSubgroup hND ?_
  · refine Set.Finite.of_finite_image (f := Submodule.toAddSubgroup) (h1.subset ?_)
      (Submodule.toAddSubgroup_injective.injOn)
    rintro _ ⟨Λ, ⟨h2, h3⟩, rfl⟩
    exact ⟨h2, h3⟩
  · have f1 : Module.Finite (𝓞 K) D := Module.Finite.iff_fg.mpr hD.fg
    have f2 : Module.Finite ℤ D := Module.Finite.trans (𝓞 K) D
    have f3 : AddGroup.FG D.toAddSubgroup := Module.Finite.iff_addGroup_fg.mp f2
    obtain ⟨n, hn, hnx⟩ := LocF.exists_zsmul_le hD hN
    apply AddCommGroup.finite_of_fg_isAddTorsion
    intro x
    induction x using QuotientAddGroup.induction_on with
    | H q =>
      rw [isOfFinAddOrder_iff_zsmul_eq_zero]
      refine ⟨n, hn, ?_⟩
      rw [← QuotientAddGroup.mk_zsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
      exact hnx _ q.2

end One

variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

theorem finite_fibG (hs : h.IsSymm) (hd : IsTotPosDef h) (S : VecSplit h h')
    {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    {Λ' : Submodule (𝓞 K) V'} (hΛ' : Submodule.IsLattice K Λ') : (fibG S L Λ').Finite := by
  by_cases hne : (fibG S L Λ').Nonempty
  · obtain ⟨Λ, hΛ⟩ := hne
    have hCut := StabilizerLattices.isFullLattice_cut S hΛ.1.1
    rw [hΛ.2.2] at hCut
    have hN : Submodule.IsFullLattice K (S.adjoin Λ') := by
      refine { toIsLattice := (S.isLattice_adjoin_iff Λ').2 hΛ', span_eq_top := ?_ }
      rw [eq_top_iff]
      intro v _
      obtain ⟨c, a, rfl⟩ := S.cover v
      refine add_mem (Submodule.smul_mem _ c (Submodule.subset_span (S.x₀_mem_adjoin Λ'))) ?_
      have hle : Submodule.map S.ι (Submodule.span K (Λ' : Set V')) ≤
          Submodule.span K (S.adjoin Λ' : Set V) := by
        rw [Submodule.map_span]
        apply Submodule.span_mono
        rintro _ ⟨b, hb, rfl⟩
        exact Submodule.mem_sup_right (Submodule.mem_map_of_mem hb)
      have ha : a ∈ Submodule.span K (Λ' : Set V') := by
        rw [hCut.span_eq_top]
        exact Submodule.mem_top
      exact hle (Submodule.mem_map_of_mem ha)
    have hD := (Formalism.HermitianLatticesTheory.dualLattice (𝓞 K) K V h hs
      (UnimodularLocalization.nondegenerate hd)
      Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range _ hN).1
    have key : ∀ Λ ∈ fibG S L Λ', S.adjoin Λ' ≤ Λ ∧ Λ ≤ Formalism.HermitianLatticesTheory.dual h (S.adjoin Λ') := by
      rintro Λ ⟨hg, hx, hc⟩
      have hΛi : Formalism.HermitianLatticesTheory.IsIntegralLat h Λ :=
        ((Formalism.HermitianLatticesTheory.genusBasic (𝓞 K) K V h hs Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range).2.2 L Λ hL.fg hg.1.fg
          hg.2).2.mp hLi
      have := S.le_dual_of_mem hs hΛi hx
      rwa [hc] at this
    exact (finite_between hN hD.toIsLattice ((key Λ hΛ).1.trans (key Λ hΛ).2)).subset key
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]
    exact Set.finite_empty

theorem good_cut (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') {B : Submodule (𝓞 K) V}
    (hB : Submodule.IsFullLattice K B) (hBi : Formalism.HermitianLatticesTheory.IsIntegralLat h B) (hx : S.x₀ ∈ B) :
    GoodGenusOrbits.Good F S B (S.cut B) := by
  let hc := StabilizerLattices.isFullLattice_cut S hB
  refine ⟨inferInstance, fun 𝔮 h0 => ?_⟩
  have h1 := card_fibG_eq_prod (F := F) (L := B) (Λ' := S.cut B)
    hK hF hs hd S inferInstance hBi inferInstance
  rw [tprod_of_exists_eq_zero ⟨𝔮, by rw [h0]; simp⟩] at h1
  have hfin := finite_fibG hs hd S hB.toIsLattice hBi hc.toIsLattice
  have hmem : B ∈ fibG S B (S.cut B) :=
    ⟨⟨hB, (Formalism.HermitianLatticesTheory.genusBasic (𝓞 K) K V h hs Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range).1.refl B⟩, hx, rfl⟩
  have : Nat.card (fibG S B (S.cut B)) ≠ 0 := by
    have := hfin.to_subtype
    have : Nonempty (fibG S B (S.cut B)) := ⟨⟨B, hmem⟩⟩
    exact Nat.card_pos.ne'
  exact this (by exact_mod_cast h1)

def scaleSplit (S : VecSplit h h') (c : K) (hc : c ≠ 0) : VecSplit h h' where
  x₀ := c • S.x₀
  ι := S.ι
  inj := S.inj
  hx₀ := by
    rw [map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
    exact mul_ne_zero hc (mul_ne_zero ((map_ne_zero _).mpr hc) S.hx₀)
  isom := S.isom
  orth := fun a => by
    rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, S.orth, smul_zero]
  cover := fun v => by
    obtain ⟨d, a, rfl⟩ := S.cover v
    exact ⟨d / c, a, by rw [smul_smul, div_mul_cancel₀ _ hc]⟩

theorem fibLoc_scale (S : VecSplit h h') (L : Submodule (𝓞 K) V) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsPrime) {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) {t : 𝓞 F} (ht : t ∉ 𝔭)
    (hc : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) ≠ 0) (T : Submodule (𝓞 K) V') :
    fibLoc (scaleSplit S _ hc) (Formalism.HermitianLatticesTheory.gmap g L) 𝔭 T = fibLoc S L 𝔭 T := by
  unfold fibLoc
  refine Nat.card_congr (Equiv.subtypeEquivRight fun Λ => ?_)
  refine and_congr_right fun hΛ => and_congr ?_ (and_congr_left fun _ => ?_)
  · rw [← LocalizedFibreSets.gmap_locF]
    constructor
    · rintro ⟨g', hg', rfl⟩
      exact ⟨g' * g, Subgroup.mul_mem _ hg' hg, autSub_gmap_mul _ _ _⟩
    · rintro ⟨g', hg', rfl⟩
      refine ⟨g' * g⁻¹, Subgroup.mul_mem _ hg' (Subgroup.inv_mem _ hg), ?_⟩
      rw [← autSub_gmap_mul, mul_assoc, inv_mul_cancel, mul_one]
  · change algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) • S.x₀ ∈ Λ ↔ _
    rw [algebraMap_smul]
    constructor
    · intro hx
      rw [← hΛ]
      exact (LocF.mem_locF_iff h𝔭 Λ _).mpr ⟨t, ht, hx⟩
    · exact fun hx => Λ.smul_mem _ hx

theorem exists_locReps' (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) : ∃ s, IsLocReps S L 𝔭 s := by
  by_cases H : ∀ T, fibLoc S L 𝔭 T = 0
  · exact ⟨∅, fun T hT => absurd hT (Finset.notMem_empty T), fun T _ _ h3 => absurd (H T) h3⟩
  · push Not at H
    obtain ⟨T₁, hT₁⟩ := H
    obtain ⟨g, hg, hx, -⟩ := UnimodularLocalization.exists_of_fibLoc_ne_zero S hT₁
    obtain ⟨t, ht, hx⟩ := (LocF.mem_locF_iff h𝔭.isPrime _ _).mp hx
    have hc : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) ≠ 0 := by
      intro e
      have e1 : algebraMap (𝓞 F) (𝓞 K) t = 0 := Formalism.HermitianLatticesTheory.genusCovol_hinj (by rw [e, map_zero])
      have e2 : t = 0 := FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K) (by rw [e1, map_zero])
      exact ht (e2 ▸ 𝔭.zero_mem)
    let hB : Submodule.IsFullLattice K (Formalism.HermitianLatticesTheory.gmap g L) := by
      refine { toIsLattice := LocalizedFibreSets.isLattice_gmap g hL, span_eq_top := ?_ }
      change Submodule.span K ((g : V →ₗ[K] V) '' (L : Set V)) = ⊤
      rw [Submodule.span_image, hL.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
      exact g.surjective
    have hBi := UnimodularLocalization.isIntegralLat_gmap hg hLi
    have hgood := good_cut (F := F) hK hF hs hd (scaleSplit S _ hc) hB hBi
      (by change algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) • S.x₀ ∈ _
          rw [algebraMap_smul]; exact hx)
    obtain ⟨s, hs1⟩ := GoodGenusOrbits.exists_locReps (L := Formalism.HermitianLatticesTheory.gmap g L)
      hK hF hs hd (scaleSplit S _ hc) inferInstance hBi hgood ⟨𝔭, h𝔭⟩
    refine ⟨s, ?_⟩
    unfold IsLocReps at hs1 ⊢
    simpa only [fibLoc_scale S L h𝔭.isPrime hg ht hc] using hs1

end Formalism.HermitianLattices.Ext.L3.BrB
end
end

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LaurentAdjoinEqOfImageEq
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.WCB

section Alg

variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]

def skewY (h : V →ₗ⋆[K] V →ₗ[K] K) (u w : V) (θ : K) : V →ₗ[K] V :=
  (θ • h u - h w).smulRight u + (h u).smulRight w

theorem skewY_apply (h : V →ₗ⋆[K] V →ₗ[K] K) (u w : V) (θ : K) (z : V) :
    skewY h u w θ z = (θ * h u z - h w z) • u + h u z • w := by
  simp [skewY]

theorem skewY_skew {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (u w : V) {θ : K} (hθ : star θ = -θ)
    (a b : V) : h (skewY h u w θ a) b + h a (skewY h u w θ b) = 0 := by
  have e1 : star (h u a) = h a u := hs.eq u a
  have e2 : star (h w a) = h a w := hs.eq w a
  rw [skewY_apply, skewY_apply]
  simp only [map_add (f := _), map_smul, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    starRingEnd_apply, star_sub, star_mul', e1, e2, hθ]
  ring

theorem laurent_adjoin_eq_of_image_eq {h : V →ₗ⋆[K] V →ₗ[K] K} (han : ∀ x, h x x = 0 → x = 0) {Y : V →ₗ[K] V}
    (hY : ∀ a b, h (Y a) b + h a (Y b) = 0) {l m : K} (hm : star m = l) (hl : l + m = 1) {z : V}
    (hz : z = m • Y z) : z = 0 := by
  apply han
  have h1 : h z z = m * h z (Y z) := by
    have := congrArg (h z) hz
    rwa [map_smul, smul_eq_mul] at this
  have h2 : h z z = l * h (Y z) z := by
    have := congrArg (fun t => h t z) hz
    simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, hm] at this
    exact this
  have h3 := hY z z
  have h4 : h z (Y z) = 0 := by linear_combination (-(h z (Y z))) * hl - h1 + h2 + l * h3
  rw [h1, h4, mul_zero]

theorem exists_cayley [FiniteDimensional K V] {h : V →ₗ⋆[K] V →ₗ[K] K}
    (han : ∀ x, h x x = 0 → x = 0) {Y : V →ₗ[K] V} (hY : ∀ a b, h (Y a) b + h a (Y b) = 0) {l : K}
    (hl : l + star l = 1) :
    ∃ g : V ≃ₗ[K] V, g ∈ Formalism.HermitianLatticesTheory.isom h ∧ (∀ z, g (z - star l • Y z) = z + l • Y z) ∧
      (∀ z, ∃ z', z' - star l • Y z' = z) ∧ (∀ z, ∃ z', z' + l • Y z' = z) := by
  let S : V →ₗ[K] V := LinearMap.id - star l • Y
  let T : V →ₗ[K] V := LinearMap.id + l • Y
  have hS : Function.Injective S := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    have hz' : z - star l • Y z = 0 := hz
    exact laurent_adjoin_eq_of_image_eq han hY (star_star l) hl (sub_eq_zero.1 hz')
  have hT : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    have hz' : z + l • Y z = 0 := hz
    have hY' : ∀ a b, h ((-Y) a) b + h a ((-Y) b) = 0 := by
      intro a b
      simp only [LinearMap.neg_apply, map_neg]
      linear_combination (-1 : K) * hY a b
    refine laurent_adjoin_eq_of_image_eq (l := star l) (m := l) han hY' rfl (by rw [add_comm]; exact hl) ?_
    rw [LinearMap.neg_apply, smul_neg]
    exact eq_neg_of_add_eq_zero_left hz'
  let eS := LinearEquiv.ofInjectiveEndo S hS
  let eT := LinearEquiv.ofInjectiveEndo T hT
  have heS : ∀ z, eS z = z - star l • Y z := fun z => rfl
  have heT : ∀ z, eT z = z + l • Y z := fun z => rfl
  refine ⟨eS.symm.trans eT, ?_, ?_, ?_, ?_⟩
  · intro x y
    obtain ⟨a, rfl⟩ := eS.surjective x
    obtain ⟨b, rfl⟩ := eS.surjective y
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    rw [heS, heS, heT, heT]
    simp only [map_add (f := _), map_sub, map_smul, map_smulₛₗ, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_star]
    linear_combination (l + star l) * hY a b
  · intro z
    rw [← heS, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, heT]
  · intro z
    exact ⟨eS.symm z, by rw [← heS, LinearEquiv.apply_symm_apply]⟩
  · intro z
    exact ⟨eT.symm z, by rw [← heT, LinearEquiv.apply_symm_apply]⟩

end Alg

section Int

open WCA

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {𝔭 : Ideal (𝓞 F)} {A : Submodule (𝓞 K) V}

theorem skewY_mem (hp : 𝔭.IsPrime) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hA : Formalism.HermitianLatticesTheory.IsIntegralLat h A) {J : ℕ} {u w z : V} {θ : K} (hu : InL 𝔭 A 0 u)
    (hw : InL 𝔭 A J w) (hθ : InI 𝔭 J θ) (hz : InL 𝔭 A 0 z) : InL 𝔭 A J (skewY h u w θ z) := by
  rw [skewY_apply]
  refine InL.add hp ?_ ?_
  · refine (InL.smul hp (i := J) ?_ hu).mono (by omega)
    exact InI.sub hp ((hθ.mul hp (hu.form hp hF hA hz)).mono (by omega))
      ((hw.form hp hF hA hz).mono (by omega))
  · exact (InL.smul hp (hu.form hp hF hA hz) hw).mono (by omega)

theorem mem_of_resolvent (h𝔭 : 𝔭.IsMaximal) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hA : Formalism.HermitianLatticesTheory.IsIntegralLat h A) {u w z z' : V} {θ c : K} (hu : InL 𝔭 A 0 u)
    (hw : InL 𝔭 A 1 w) (hθ : InI 𝔭 1 θ) (hc : InI 𝔭 0 c) (hz : InL 𝔭 A 0 z)
    (e : z' - c • skewY h u w θ z' = z) : InL 𝔭 A 0 z' := by
  have hp := h𝔭.isPrime
  obtain ⟨b, hb⟩ : ∃ b : K, b = h u z' := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : K, a = θ * b - h w z' := ⟨_, rfl⟩
  have e' : z' = z + (c * a) • u + (c * b) • w := by
    rw [skewY_apply, ← hb, ← ha] at e
    rw [← e, smul_add, smul_smul, smul_smul]
    abel
  have eb : b = h u z + c * a * h u u + c * b * h u w := by
    conv_lhs => rw [hb, e']
    rw [map_add (f := _), map_add (f := _), map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have ew : h w z' = h w z + c * a * h w u + c * b * h w w := by
    conv_lhs => rw [e']
    rw [map_add (f := _), map_add (f := _), map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have Iν : InI 𝔭 0 (h u u) := hu.form hp hF hA hu
  have Ip : InI 𝔭 1 (h u w) := (hu.form hp hF hA hw).mono (by omega)
  have Ir : InI 𝔭 1 (h w u) := (hw.form hp hF hA hu).mono (by omega)
  have Is : InI 𝔭 1 (h w w) := (hw.form hp hF hA hw).mono (by omega)
  have Iβ : InI 𝔭 0 (h u z) := hu.form hp hF hA hz
  have Iγ : InI 𝔭 0 (h w z) := (hw.form hp hF hA hz).mono (by omega)
  have m01 : ∀ {x y : K}, InI 𝔭 0 x → InI 𝔭 1 y → InI 𝔭 1 (x * y) := fun hx hy =>
    (hx.mul hp hy).mono (by omega)
  have m00 : ∀ {x y : K}, InI 𝔭 0 x → InI 𝔭 0 y → InI 𝔭 0 (x * y) := fun hx hy => hx.mul hp hy
  have Icr : InI 𝔭 1 (c * h w u) := m01 hc Ir
  have Iκ : InI 𝔭 1 (θ - c * h w w) := hθ.sub hp (m01 hc Is)
  obtain ⟨hE1, IE1⟩ := InI.unit h𝔭 hF Icr
  have Iε : InI 𝔭 1 (c * h w u - c * h u w - c * h u w * (c * h w u)
      - c * h u u * (θ - c * h w w)) :=
    ((Icr.sub hp (m01 hc Ip)).sub hp (m01 (m00 hc (Ip.mono (by omega))) Icr)).sub hp
      (m01 (m00 hc Iν) Iκ)
  obtain ⟨hD, ID⟩ := InI.unit h𝔭 hF Iε
  have ea : a * (1 + c * h w u) = b * (θ - c * h w w) - h w z := by
    linear_combination ha - ew
  have ebD : b * (1 + (c * h w u - c * h u w - c * h u w * (c * h w u)
      - c * h u u * (θ - c * h w w))) = h u z * (1 + c * h w u) - c * h u u * h w z := by
    linear_combination (1 + c * h w u) * eb + c * h u u * ea
  have Ib : InI 𝔭 0 b := by
    rw [(eq_mul_inv_iff_mul_eq₀ hD).2 ebD]
    exact m00 ((m00 Iβ ((InI.one hp).add hp (Icr.mono (by omega)))).sub hp (m00 (m00 hc Iν) Iγ)) ID
  have Ia : InI 𝔭 0 a := by
    rw [(eq_mul_inv_iff_mul_eq₀ hE1).2 ea]
    exact m00 ((m00 Ib (Iκ.mono (by omega))).sub hp Iγ) IE1
  rw [e']
  have h1 : InL 𝔭 A 0 ((c * a) • u) := (InL.smul hp (m00 hc Ia) hu).mono (by omega)
  have h2 : InL 𝔭 A 0 ((c * b) • w) := (InL.smul hp (m00 hc Ib) hw).mono (by omega)
  exact (hz.add hp h1).add hp h2

end Int

end Formalism.HermitianLattices.Ext.L3.WCB
end
end
