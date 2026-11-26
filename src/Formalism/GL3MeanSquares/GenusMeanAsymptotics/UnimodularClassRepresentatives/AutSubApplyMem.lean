module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExtHomInjective

@[expose] public section

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ConjMemAutSub
open NumberField Module Filter

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.LIOrb.OrbF

theorem exists_reps {X : Type*} (r : X → X → Prop) (hr : Equivalence r) (A X₀ : Set X)
    (hfin : X₀.Finite) (hcov : ∀ x ∈ A, ∃ t ∈ X₀, r t x) :
    ∃ R : Finset X, (∀ t ∈ R, t ∈ X₀) ∧ ∀ x ∈ A, ∃! t, t ∈ R ∧ r t x := by
  classical
  let s : Setoid X := ⟨r, hr⟩
  let pick : Quotient s → X := fun c =>
    if H : ∃ t ∈ X₀, Quotient.mk s t = c then H.choose else Quotient.out c
  have hp1 : ∀ x ∈ X₀, pick (Quotient.mk s x) ∈ X₀ ∧
      Quotient.mk s (pick (Quotient.mk s x)) = Quotient.mk s x := by
    intro x hx
    have H : ∃ t ∈ X₀, Quotient.mk s t = Quotient.mk s x := ⟨x, hx, rfl⟩
    simp only [pick, dif_pos H]
    exact H.choose_spec
  refine ⟨hfin.toFinset.image (fun x => pick (Quotient.mk s x)), ?_, ?_⟩
  · intro t ht
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ht
    exact (hp1 x (hfin.mem_toFinset.mp hx)).1
  · intro x hx
    obtain ⟨t₀, ht₀, h0⟩ := hcov x hx
    refine ⟨pick (Quotient.mk s t₀),
      ⟨Finset.mem_image.mpr ⟨t₀, hfin.mem_toFinset.mpr ht₀, rfl⟩, ?_⟩, ?_⟩
    · exact hr.trans (Quotient.exact (hp1 t₀ ht₀).2) h0
    · rintro t' ⟨ht', h1⟩
      obtain ⟨x', hx', rfl⟩ := Finset.mem_image.mp ht'
      have e1 := (hp1 x' (hfin.mem_toFinset.mp hx')).2
      have e2 : Quotient.mk s x' = Quotient.mk s t₀ := by
        rw [← e1]
        exact Quotient.sound (hr.trans h1 (hr.symm h0))
      rw [e2]

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
variable {V' : Type} [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] [Module (𝓞 K) V']
  [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

@[reducible] def actV (S : VecSplit h h') : MulAction (Formalism.HermitianLatticesTheory.isom h') (Submodule (𝓞 K) V) where
  smul g M := Formalism.HermitianLatticesTheory.gmap (extHom S g.1) M
  one_smul M := by
    change Formalism.HermitianLatticesTheory.gmap (extHom S 1) M = M
    rw [map_one]
    exact autSub_gmap_one M
  mul_smul a b M := by
    change Formalism.HermitianLatticesTheory.gmap (extHom S (a.1 * b.1)) M = _
    rw [map_mul]
    exact autSub_gmap_mul _ _ _

@[reducible] def actV' (h' : V' →ₗ⋆[K] V' →ₗ[K] K) :
    MulAction (Formalism.HermitianLatticesTheory.isom h') (Submodule (𝓞 K) V') where
  smul g T := Formalism.HermitianLatticesTheory.gmap g.1 T
  one_smul T := autSub_gmap_one T
  mul_smul _ _ _ := autSub_gmap_mul _ _ _

theorem stab_actV (hs : h.IsSymm) (S : VecSplit h h') (M : Submodule (𝓞 K) V) :
    @MulAction.stabilizer _ _ _ (actV S) M = (autExt S M).subgroupOf (Formalism.HermitianLatticesTheory.isom h') := by
  ext g
  rw [Subgroup.mem_subgroupOf]
  constructor
  · intro e
    exact ⟨SplitBAux.extOf_mem_isom hs S g.2, e⟩
  · intro e
    exact e.2

theorem stab_actV' (T : Submodule (𝓞 K) V') :
    @MulAction.stabilizer _ _ _ (actV' h') T = (autSub h' T).subgroupOf (Formalism.HermitianLatticesTheory.isom h') := by
  ext g
  rw [Subgroup.mem_subgroupOf]
  exact ⟨fun hg => ⟨g.2, hg⟩, fun hg => hg.2⟩

theorem autSub_le_isom (h : V →ₗ⋆[K] V →ₗ[K] K) (A : Submodule (𝓞 K) V) :
    autSub h A ≤ Formalism.HermitianLatticesTheory.isom h := fun _ hg => hg.1

theorem relIndex_stab (hs : h.IsSymm) (S : VecSplit h h') (M : Submodule (𝓞 K) V) :
    (@MulAction.stabilizer _ _ _ (actV S) M).relIndex
      (@MulAction.stabilizer _ _ _ (actV' h') (S.cut M)) = oM S M := by
  rw [stab_actV hs, stab_actV', Subgroup.relIndex_subgroupOf (autSub_le_isom h' _)]
  rfl

theorem extOf_res (S : VecSplit h h') {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h)
    (hx : g S.x₀ = S.x₀) : SplitBAux.extOf S (SplitBAux.res S g hg hx) = g := by
  apply LinearEquiv.toLinearMap_injective
  apply SplitBAux.linearMap_ext S
  · change SplitBAux.extOf S _ S.x₀ = g S.x₀
    rw [SplitBAux.extOf_x₀, hx]
  · intro a
    change SplitBAux.extOf S _ (S.ι a) = g (S.ι a)
    rw [SplitBAux.extOf_ι, SplitBAux.res_spec]

theorem gmap_smul (g : V ≃ₗ[K] V) (I : Ideal (𝓞 K)) (A : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.gmap g (I • A) = I • Formalism.HermitianLatticesTheory.gmap g A := Submodule.map_smul'' _ _ _

theorem conj_mem_autSub {g u : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) {A : Submodule (𝓞 K) V}
    (hu : u ∈ autSub h A) : g * u * g⁻¹ ∈ autSub h (Formalism.HermitianLatticesTheory.gmap g A) := by
  refine ⟨mul_mem (mul_mem hg hu.1) (inv_mem hg), ?_⟩
  rw [autSub_gmap_mul, autSub_gmap_mul, ← autSub_gmap_mul g⁻¹ g, inv_mul_cancel, autSub_gmap_one, hu.2]

theorem conj_mem_autSub' {g u : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) {A : Submodule (𝓞 K) V}
    (hu : u ∈ autSub h (Formalism.HermitianLatticesTheory.gmap g A)) : g⁻¹ * u * g ∈ autSub h A := by
  refine ⟨mul_mem (mul_mem (inv_mem hg) hu.1) hg, ?_⟩
  rw [autSub_gmap_mul, autSub_gmap_mul, hu.2, ← autSub_gmap_mul, inv_mul_cancel, autSub_gmap_one]

theorem mem_tube_gmap {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) (A : Submodule (𝓞 K) V)
    (𝔭 : Ideal (𝓞 F)) (J : ℕ) (x y : V) :
    g y ∈ tube (autSub h (Formalism.HermitianLatticesTheory.gmap g A)) (Formalism.HermitianLatticesTheory.gmap g A) 𝔭 J x ↔
      y ∈ tube (autSub h A) A 𝔭 J (g.symm x) := by
  constructor
  · rintro ⟨u, hu, hm⟩
    refine ⟨g⁻¹ * u * g, conj_mem_autSub' hg hu, ?_⟩
    rw [← gmap_smul, Formalism.HermitianLatticesTheory.isomAct_mem_gmap, map_sub, g.symm_apply_apply] at hm
    change y - g.symm (u (g (g.symm x))) ∈ _
    rwa [g.apply_symm_apply]
  · rintro ⟨u, hu, hm⟩
    refine ⟨g * u * g⁻¹, conj_mem_autSub hg hu, ?_⟩
    rw [← gmap_smul, Formalism.HermitianLatticesTheory.isomAct_mem_gmap]
    change g.symm (g y - g (u (g.symm x))) ∈ _
    rwa [← map_sub, g.symm_apply_apply]

theorem image_tube {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) (A : Submodule (𝓞 K) V)
    (𝔭 : Ideal (𝓞 F)) (J : ℕ) (x : V) :
    g '' tube (autSub h A) A 𝔭 J (g.symm x) =
      tube (autSub h (Formalism.HermitianLatticesTheory.gmap g A)) (Formalism.HermitianLatticesTheory.gmap g A) 𝔭 J x := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (mem_tube_gmap hg A 𝔭 J x y).2 hy
  · intro hz
    refine ⟨g.symm z, (mem_tube_gmap hg A 𝔭 J x _).1 ?_, g.apply_symm_apply z⟩
    rwa [g.apply_symm_apply]

theorem cut_props (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm) (hd : IsTotPosDef h)
    (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h)
    (hx : S.x₀ ∈ Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L)) :
    locF 𝔭 (S.cut (Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L))) = S.cut (Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L)) ∧
      IsIntegralAt 𝔭 h' (S.cut (Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L))) ∧
      fibLoc S L 𝔭 (S.cut (Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L))) ≠ 0 := by
  rw [LocalizedFibreSets.gmap_locF] at hx ⊢
  rw [LocalizedFibreSets.cut_locF]
  refine ⟨LocalizedFibreSets.locF_idem _ _, GoodPrimeTerms.isIntegralAt_locF h𝔭.isPrime hF
    (UnimodularLocalization.isIntegralLat_cut S (UnimodularLocalization.isIntegralLat_gmap hg hLi)), ?_⟩
  rw [UnimodularLocalization.fibLoc_locF]
  obtain ⟨t, ht, hx⟩ := (LocF.mem_locF_iff h𝔭.isPrime _ _).mp hx
  have hc : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) ≠ 0 := by
    intro e
    have e1 : algebraMap (𝓞 F) (𝓞 K) t = 0 := Formalism.HermitianLatticesTheory.genusCovol_hinj (by rw [e, map_zero])
    have e2 : t = 0 := FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K) (by rw [e1, map_zero])
    exact ht (e2 ▸ 𝔭.zero_mem)
  have hmap : Submodule.IsFullLattice K (Formalism.HermitianLatticesTheory.gmap g L) := by
    refine { toIsLattice := LocalizedFibreSets.isLattice_gmap g hL, span_eq_top := ?_ }
    change Submodule.span K ((g : V →ₗ[K] V) '' (L : Set V)) = ⊤
    rw [Submodule.span_image, hL.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
    exact g.surjective
  have hgood := BrB.good_cut (F := F) hK hF hs hd (BrB.scaleSplit S _ hc)
    hmap (UnimodularLocalization.isIntegralLat_gmap hg hLi)
    (by change algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) • S.x₀ ∈ _
        rw [algebraMap_smul]; exact hx)
  have h1 := hgood.2 ⟨𝔭, h𝔭⟩
  rw [BrB.fibLoc_scale S L h𝔭.isPrime hg ht hc] at h1
  exact h1

end Formalism.HermitianLattices.Ext.L3.LIOrb.OrbF
end
end

open NumberField Module Filter

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.LIOrb.OrbF

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
variable {V' : Type} [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] [Module (𝓞 K) V']
  [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

theorem extOf_one (S : VecSplit h h') : SplitBAux.extOf S 1 = 1 := by
  rw [← extHom_apply, map_one]

theorem extOf_mul (S : VecSplit h h') (a b : V' ≃ₗ[K] V') :
    SplitBAux.extOf S (a * b) = SplitBAux.extOf S a * SplitBAux.extOf S b := by
  rw [← extHom_apply, ← extHom_apply, ← extHom_apply, map_mul]

theorem gmap_extOf_inv (S : VecSplit h h') (a : V' ≃ₗ[K] V') (M : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.gmap (SplitBAux.extOf S a) (Formalism.HermitianLatticesTheory.gmap (SplitBAux.extOf S a⁻¹) M) = M := by
  rw [← autSub_gmap_mul, ← extOf_mul, mul_inv_cancel, extOf_one, autSub_gmap_one]

theorem gmap_extOf_inv' (S : VecSplit h h') (a : V' ≃ₗ[K] V') (M : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.gmap (SplitBAux.extOf S a⁻¹) (Formalism.HermitianLatticesTheory.gmap (SplitBAux.extOf S a) M) = M := by
  rw [← autSub_gmap_mul, ← extOf_mul, inv_mul_cancel, extOf_one, autSub_gmap_one]

theorem orb_equiv (S : VecSplit h h') :
    Equivalence (fun M₁ M₂ : Submodule (𝓞 K) V =>
      ∃ g' ∈ Formalism.HermitianLatticesTheory.isom h', Formalism.HermitianLatticesTheory.gmap (SplitBAux.extOf S g') M₁ = M₂) := by
  refine ⟨fun M => ⟨1, one_mem _, by rw [extOf_one, autSub_gmap_one]⟩, ?_, ?_⟩
  · rintro M₁ M₂ ⟨g', hg', e⟩
    exact ⟨g'⁻¹, inv_mem hg', by rw [← e, gmap_extOf_inv']⟩
  · rintro M₁ M₂ M₃ ⟨g', hg', e⟩ ⟨g'', hg'', e'⟩
    exact ⟨g'' * g', mul_mem hg'' hg', by rw [extOf_mul, autSub_gmap_mul, e, e']⟩

theorem through_smul (hs : h.IsSymm) (S : VecSplit h h') {A M : Submodule (𝓞 K) V}
    {g' : V' ≃ₗ[K] V'} (hg' : g' ∈ Formalism.HermitianLatticesTheory.isom h')
    (hM : (∃ g ∈ Formalism.HermitianLatticesTheory.isom h, Formalism.HermitianLatticesTheory.gmap g A = M) ∧ S.x₀ ∈ M) :
    (∃ g ∈ Formalism.HermitianLatticesTheory.isom h, Formalism.HermitianLatticesTheory.gmap g A = Formalism.HermitianLatticesTheory.gmap (SplitBAux.extOf S g') M) ∧
      S.x₀ ∈ Formalism.HermitianLatticesTheory.gmap (SplitBAux.extOf S g') M := by
  obtain ⟨⟨g, hg, hgA⟩, hxM⟩ := hM
  refine ⟨⟨SplitBAux.extOf S g' * g, mul_mem (SplitBAux.extOf_mem_isom hs S hg') hg, ?_⟩, ?_⟩
  · rw [autSub_gmap_mul, hgA]
  · exact ⟨S.x₀, hxM, SplitBAux.extOf_x₀ S g'⟩

theorem tube_add (D : Subgroup (V ≃ₗ[K] V)) (A : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) {J k : ℕ}
    (hJk : J ≤ k) (x : V) {y z : V} (hy : y ∈ tube D A 𝔭 J x)
    (hz : z ∈ ((extP K 𝔭) ^ k • A : Submodule (𝓞 K) V)) : y + z ∈ tube D A 𝔭 J x := by
  obtain ⟨g, hg, hy'⟩ := hy
  refine ⟨g, hg, ?_⟩
  have hz' : z ∈ ((extP K 𝔭) ^ J • A : Submodule (𝓞 K) V) :=
    Submodule.smul_mono_left (Ideal.pow_le_pow_right hJk) hz
  have e : y + z - g x = (y - g x) + z := by abel
  rw [e]
  exact add_mem hy' hz'

theorem autSub_apply_mem {u : V ≃ₗ[K] V} {A : Submodule (𝓞 K) V} (hu : u ∈ autSub h A) {x : V}
    (hx : x ∈ A) : u x ∈ A := by
  have h2 : Formalism.HermitianLatticesTheory.gmap u A = A := hu.2
  rw [← h2]
  exact ⟨x, hx, rfl⟩

theorem same_orbit (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm) (hd : IsTotPosDef h)
    (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : n ≠ 0) (hx : h S.x₀ S.x₀ = algebraMap F K (n : F))
    {g₁ g₂ : V ≃ₗ[K] V} (hg₁ : g₁ ∈ Formalism.HermitianLatticesTheory.isom h) (hg₂ : g₂ ∈ Formalism.HermitianLatticesTheory.isom h)
    (hx₁ : S.x₀ ∈ Formalism.HermitianLatticesTheory.gmap g₁ (locF 𝔭 L)) (hx₂ : S.x₀ ∈ Formalism.HermitianLatticesTheory.gmap g₂ (locF 𝔭 L))
    {J : ℕ} (hJ : 4 * vF 𝔭 n + eA h (locF 𝔭 L) 𝔭 + 1 ≤ J) {y : V}
    (h1 : y ∈ tube (autSub h (locF 𝔭 L)) (locF 𝔭 L) 𝔭 J (g₁.symm S.x₀))
    (h2 : y ∈ tube (autSub h (locF 𝔭 L)) (locF 𝔭 L) 𝔭 J (g₂.symm S.x₀)) :
    ∃ g' ∈ Formalism.HermitianLatticesTheory.isom h', Formalism.HermitianLatticesTheory.gmap (SplitBAux.extOf S g') (Formalism.HermitianLatticesTheory.gmap g₁ (locF 𝔭 L)) =
      Formalism.HermitianLatticesTheory.gmap g₂ (locF 𝔭 L) := by
  have hx₁' : g₁.symm S.x₀ ∈ locF 𝔭 L := (Formalism.HermitianLatticesTheory.isomAct_mem_gmap g₁ (locF 𝔭 L) S.x₀).1 hx₁
  have hx₂' : g₂.symm S.x₀ ∈ locF 𝔭 L := (Formalism.HermitianLatticesTheory.isomAct_mem_gmap g₂ (locF 𝔭 L) S.x₀).1 hx₂
  obtain ⟨u₁, hu₁, hy₁⟩ := h1
  obtain ⟨u₂, hu₂, hy₂⟩ := h2
  have ha : u₁ (g₁.symm S.x₀) ∈ locF 𝔭 L := autSub_apply_mem hu₁ hx₁'
  have hb : u₂ (g₂.symm S.x₀) ∈ locF 𝔭 L := autSub_apply_mem hu₂ hx₂'
  have hna : h (u₁ (g₁.symm S.x₀)) (u₁ (g₁.symm S.x₀)) = algebraMap F K (n : F) := by
    rw [SplitBAux.isom_apply hu₁.1, SplitBAux.isom_apply (SplitBAux.symm_mem_isom hg₁), hx]
  have hnb : h (u₂ (g₂.symm S.x₀)) (u₂ (g₂.symm S.x₀)) = algebraMap F K (n : F) := by
    rw [SplitBAux.isom_apply hu₂.1, SplitBAux.isom_apply (SplitBAux.symm_mem_isom hg₂), hx]
  have hxy : u₂ (g₂.symm S.x₀) - u₁ (g₁.symm S.x₀) ∈
      ((extP K 𝔭) ^ J • (locF 𝔭 L) : Submodule (𝓞 K) V) := by
    have e : u₂ (g₂.symm S.x₀) - u₁ (g₁.symm S.x₀) =
        (y - u₁ (g₁.symm S.x₀)) - (y - u₂ (g₂.symm S.x₀)) := by abel
    rw [e]
    exact sub_mem hy₁ hy₂
  obtain ⟨w, hw, -, hwab⟩ := exists_isom_congr hK hF hs hd hL hLi h𝔭 hn ha hb hna hnb hJ hxy
  set G : V ≃ₗ[K] V := g₂ * u₂⁻¹ * w * u₁ * g₁⁻¹ with hGdef
  have hG : G ∈ Formalism.HermitianLatticesTheory.isom h :=
    mul_mem (mul_mem (mul_mem (mul_mem hg₂ (inv_mem hu₂.1)) hw.1) hu₁.1) (inv_mem hg₁)
  have hGx : G S.x₀ = S.x₀ := by
    change g₂ (u₂.symm (w (u₁ (g₁.symm S.x₀)))) = S.x₀
    rw [hwab, LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]
  refine ⟨SplitBAux.res S G hG hGx, SplitBAux.res_mem_isom S G hG hGx, ?_⟩
  rw [extOf_res, ← autSub_gmap_mul]
  have e : G * g₁ = g₂ * u₂⁻¹ * w * u₁ := by
    rw [hGdef, inv_mul_cancel_right]
  rw [e, autSub_gmap_mul, hu₁.2, autSub_gmap_mul, hw.2, autSub_gmap_mul, (inv_mem hu₂).2]

theorem exists_on_orbit (hs : h.IsSymm) (S : VecSplit h h') {A : Submodule (𝓞 K) V}
    {g γ : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom h)
    {g' : V' ≃ₗ[K] V'} (hg' : g' ∈ Formalism.HermitianLatticesTheory.isom h')
    (e : Formalism.HermitianLatticesTheory.gmap (SplitBAux.extOf S g') (Formalism.HermitianLatticesTheory.gmap γ A) = Formalism.HermitianLatticesTheory.gmap g A) {y : V}
    (hy : g y = S.x₀) : ∃ u ∈ autSub h A, u (γ.symm S.x₀) = y := by
  refine ⟨g⁻¹ * SplitBAux.extOf S g' * γ, ?_, ?_⟩
  · show _ ∈ Formalism.HermitianLatticesTheory.isom h ∧ _
    refine ⟨mul_mem (mul_mem (inv_mem hg) (SplitBAux.extOf_mem_isom hs S hg')) hγ, ?_⟩
    rw [autSub_gmap_mul, autSub_gmap_mul, e, ← autSub_gmap_mul, inv_mul_cancel, autSub_gmap_one]
  · rw [mul_apply_eq_comp, mul_apply_eq_comp, LinearEquiv.apply_symm_apply, SplitBAux.extOf_x₀,
      ← hy]
    exact g.symm_apply_apply y

end Formalism.HermitianLattices.Ext.L3.LIOrb.OrbF
