module

public import GroundTheory.ProfiniteCohomology.DiscreteModules.IsDiscreteRepIffForallExistsOpenNormalSubgroup
public import GroundTheory.ProfiniteCohomology.Factor

@[expose] public section

section -- merged from GroundTheory.ProfiniteCohomology.ContinuousCochains
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G]

def locallyConstantCochains (A : Rep.{u} k G) (n : ℕ) : Submodule k ((Fin n → G) → A) where
  carrier := {f | IsLocallyConstant f}
  zero_mem' := IsLocallyConstant.const 0
  add_mem' hf hg := IsLocallyConstant.add hf hg
  smul_mem' r _ hf := hf.comp (r • ·)

theorem mem_locallyConstantCochains (A : Rep.{u} k G) {n : ℕ} (f : (Fin n → G) → A) :
    f ∈ locallyConstantCochains A n ↔ IsLocallyConstant f :=
  Iff.rfl

variable [IsTopologicalGroup G]

theorem continuous_contractNth {n : ℕ} (j : Fin (n + 1)) :
    Continuous fun g : Fin (n + 1) → G => Fin.contractNth j (· * ·) g := by
  refine continuous_pi fun i => ?_
  simp only [Fin.contractNth]
  split_ifs
  · exact continuous_apply _
  · exact (continuous_apply _).mul (continuous_apply _)
  · exact continuous_apply _

theorem isLocallyConstant_d (A : Rep.{u} k G) [IsDiscreteRep A] {n : ℕ}
    {f : (Fin n → G) → A} (hf : IsLocallyConstant f) :
    IsLocallyConstant ((inhomogeneousCochains.d A n).hom f) := by
  have h1 : IsLocallyConstant fun g : Fin (n + 1) → G => A.ρ (g 0) (f fun i => g i.succ) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro g
    have htail : Continuous fun g : Fin (n + 1) → G => fun i : Fin n => g i.succ :=
      continuous_pi fun i => continuous_apply _
    have hev1 : ∀ᶠ y in nhds g, f (fun i => y i.succ) = f (fun i => g i.succ) :=
      htail.continuousAt.eventually (hf.eventually_eq _)
    have hev2 : ∀ᶠ y in nhds g,
        A.ρ (y 0) (f fun i => g i.succ) = A.ρ (g 0) (f fun i => g i.succ) :=
      (continuous_apply 0).continuousAt.eventually
        ((isLocallyConstant_apply A (f fun i => g i.succ)).eventually_eq (g 0))
    filter_upwards [hev1, hev2] with y h1 h2
    rw [h1, h2]
  have h2 : ∀ j : Fin (n + 1), IsLocallyConstant fun g : Fin (n + 1) → G =>
      (-1 : k) ^ ((j : ℕ) + 1) • f (Fin.contractNth j (· * ·) g) := fun j =>
    (hf.comp_continuous (continuous_contractNth j)).comp _
  have h3 : IsLocallyConstant fun g : Fin (n + 1) → G => Finset.univ.sum fun j : Fin (n + 1) =>
      (-1 : k) ^ ((j : ℕ) + 1) • f (Fin.contractNth j (· * ·) g) := by
    have : (fun g : Fin (n + 1) → G => Finset.univ.sum fun j : Fin (n + 1) =>
        (-1 : k) ^ ((j : ℕ) + 1) • f (Fin.contractNth j (· * ·) g)) =
        Finset.univ.sum fun j : Fin (n + 1) => fun g : Fin (n + 1) → G =>
          (-1 : k) ^ ((j : ℕ) + 1) • f (Fin.contractNth j (· * ·) g) := by
      ext g
      simp [Finset.sum_apply]
    rw [this]
    exact Finset.sum_induction _ IsLocallyConstant (fun _ _ ha hb => ha.add hb)
      (IsLocallyConstant.const 0) fun j _ => h2 j
  have : (inhomogeneousCochains.d A n).hom f = fun g =>
      A.ρ (g 0) (f fun i => g i.succ) + Finset.univ.sum fun j : Fin (n + 1) =>
        (-1 : k) ^ ((j : ℕ) + 1) • f (Fin.contractNth j (· * ·) g) := by
    ext g
    simp [inhomogeneousCochains.d_hom_apply]
  rw [this]
  exact h1.add h3

theorem d_mem_locallyConstantCochains (A : Rep.{u} k G) [IsDiscreteRep A] {n : ℕ}
    {f : (Fin n → G) → A} (hf : f ∈ locallyConstantCochains A n) :
    (inhomogeneousCochains.d A n).hom f ∈ locallyConstantCochains A (n + 1) :=
  isLocallyConstant_d A hf

noncomputable def dLocallyConstant (A : Rep.{u} k G) [IsDiscreteRep A] (n : ℕ) :
    ModuleCat.of k (locallyConstantCochains A n) ⟶
      ModuleCat.of k (locallyConstantCochains A (n + 1)) :=
  ModuleCat.ofHom ((inhomogeneousCochains.d A n).hom.restrict
    fun _ hf => d_mem_locallyConstantCochains A hf)

theorem dLocallyConstant_hom_apply (A : Rep.{u} k G) [IsDiscreteRep A] (n : ℕ)
    (f : locallyConstantCochains A n) :
    ((dLocallyConstant A n).hom f : (Fin (n + 1) → G) → A) =
      (inhomogeneousCochains.d A n).hom f :=
  rfl

theorem dLocallyConstant_comp (A : Rep.{u} k G) [IsDiscreteRep A] (n : ℕ) :
    dLocallyConstant A n ≫ dLocallyConstant A (n + 1) = 0 := by
  ext f : 2
  apply Subtype.ext
  have := congrArg (fun φ => φ.hom f.1) (inhomogeneousCochains.d_comp_d (A := A) (n := n))
  exact this

noncomputable def cochainsComplex (A : Rep.{u} k G) [IsDiscreteRep A] :
    CochainComplex (ModuleCat k) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of k (locallyConstantCochains A n))
    (fun n => dLocallyConstant A n) fun n => dLocallyConstant_comp A n

theorem cochainsComplex_d (A : Rep.{u} k G) [IsDiscreteRep A] (n : ℕ) :
    (cochainsComplex A).d n (n + 1) = dLocallyConstant A n := by
  simp [cochainsComplex]

noncomputable def cochainsComplexι (A : Rep.{u} k G) [IsDiscreteRep A] :
    cochainsComplex A ⟶ inhomogeneousCochains A :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (locallyConstantCochains A n).subtype) fun n => by
    rw [cochainsComplex_d, inhomogeneousCochains.d_def]
    ext f : 2
    rfl

instance (A : Rep.{u} k G) [IsDiscreteRep A] (n : ℕ) : Mono ((cochainsComplexι A).f n) :=
  (ModuleCat.mono_iff_injective _).2 Subtype.val_injective

noncomputable abbrev cocycles (A : Rep.{u} k G) [IsDiscreteRep A] (n : ℕ) : ModuleCat k :=
  (cochainsComplex A).cycles n

noncomputable def cohomology (A : Rep.{u} k G) [IsDiscreteRep A] (n : ℕ) : ModuleCat k :=
  (cochainsComplex A).homology n

noncomputable abbrev cohomologyπ (A : Rep.{u} k G) [IsDiscreteRep A] (n : ℕ) :
    cocycles A n ⟶ cohomology A n :=
  (cochainsComplex A).homologyπ n

end GroundTheory.ProfCoh
end

section -- merged from GroundTheory.ProfiniteCohomology.IsProPGroupSubgroupIffIsPGroupMap
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

variable {G : Type*} [Group G] [TopologicalSpace G]

def IsProPGroup (p : ℕ) (G : Type*) [Group G] [TopologicalSpace G] : Prop :=
  ∀ U : OpenNormalSubgroup G, IsPGroup p (G ⧸ (U : Subgroup G))

theorem isProPGroup_iff {p : ℕ} :
    IsProPGroup p G ↔ ∀ U : OpenNormalSubgroup G, ∀ g : G, ∃ k : ℕ, g ^ p ^ k ∈ U := by
  refine forall_congr' fun U => ⟨fun h g => ?_, fun h x => ?_⟩
  · obtain ⟨k, hk⟩ := h (g : G ⧸ (U : Subgroup G))
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hk
    exact hk
  · induction x using QuotientGroup.induction_on with
    | H g =>
      obtain ⟨k, hk⟩ := h g
      exact ⟨k, by rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact hk⟩


omit [TopologicalSpace G] in
theorem isPGroup_map_mk_iff {p : ℕ} (H U : Subgroup G) [U.Normal] :
    IsPGroup p (H.map (QuotientGroup.mk' U)) ↔ ∀ h ∈ H, ∃ k : ℕ, h ^ p ^ k ∈ U := by
  constructor
  · intro hp h hh
    obtain ⟨k, hk⟩ := hp ⟨QuotientGroup.mk' U h, Subgroup.mem_map_of_mem _ hh⟩
    refine ⟨k, ?_⟩
    have hk' := congrArg Subtype.val hk
    simp only [Subgroup.coe_pow, OneMemClass.coe_one, QuotientGroup.mk'_apply] at hk'
    rwa [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hk'
  · rintro h ⟨x, hx⟩
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨k, hk⟩ := h g hg
    refine ⟨k, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, OneMemClass.coe_one, QuotientGroup.mk'_apply]
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hk

variable [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]

theorem exists_subgroupOf_le {H : Subgroup G} (V : OpenNormalSubgroup H) :
    ∃ U : OpenNormalSubgroup G, (U : Subgroup G).subgroupOf H ≤ (V : Subgroup H) := by
  obtain ⟨W, hWo, hWV⟩ := isOpen_induced_iff.mp V.toOpenSubgroup.isOpen
  have h1W : (1 : G) ∈ W := by
    have : (1 : H) ∈ Subtype.val ⁻¹' W := hWV ▸ V.one_mem
    simpa using this
  obtain ⟨U, hUW⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hWo h1W
  refine ⟨U, fun x hx => ?_⟩
  have : (x : G) ∈ W := hUW hx
  have : x ∈ Subtype.val ⁻¹' W := this
  rw [hWV] at this
  exact this

theorem isProPGroup_subgroup_iff {p : ℕ} {H : Subgroup G} :
    IsProPGroup p H ↔ ∀ U : OpenNormalSubgroup G, ∀ h ∈ H, ∃ k : ℕ, h ^ p ^ k ∈ U := by
  rw [isProPGroup_iff]
  constructor
  · intro hH U h hh
    let U' : OpenNormalSubgroup H :=
      { toSubgroup := (U : Subgroup G).subgroupOf H
        isOpen' := Subgroup.subgroupOf_isOpen H (U : Subgroup G) U.toOpenSubgroup.isOpen
        isNormal' := inferInstance }
    obtain ⟨k, hk⟩ := hH U' ⟨h, hh⟩
    exact ⟨k, hk⟩
  · intro hH V g
    obtain ⟨U, hU⟩ := exists_subgroupOf_le V
    obtain ⟨k, hk⟩ := hH U g g.2
    exact ⟨k, hU (show (g ^ p ^ k : H) ∈ (U : Subgroup G).subgroupOf H from hk)⟩

theorem isProPGroup_subgroup_iff_isPGroup_map {p : ℕ} {H : Subgroup G} :
    IsProPGroup p H ↔
      ∀ U : OpenNormalSubgroup G, IsPGroup p (H.map (QuotientGroup.mk' (U : Subgroup G))) := by
  rw [isProPGroup_subgroup_iff]
  exact forall_congr' fun U => (isPGroup_map_mk_iff H (U : Subgroup G)).symm

theorem isProPGroup_bot (p : ℕ) : IsProPGroup p (⊥ : Subgroup G) := by
  rw [isProPGroup_subgroup_iff]
  intro U h hh
  rw [Subgroup.mem_bot.mp hh]
  exact ⟨0, by simp⟩

end GroundTheory.ProfCoh
end

section -- merged from GroundTheory.ProfiniteCohomology.CoinducedModules
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Filter Topology

universe u

section Translation

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

theorem eventually_forall_mul_eq {Y : Type*} (f : LocallyConstant G Y) :
    ∀ᶠ g in 𝓝 (1 : G), ∀ x : G, f (x * g) = f x := by
  have key := isCompact_univ.eventually_forall_of_forall_eventually (x₀ := (1 : G))
    (P := fun g x => f (x * g) = f x) (K := Set.univ) ?_
  · exact key.mono fun g hg x => hg x (Set.mem_univ x)
  intro y _
  have h1 := (f.isLocallyConstant.comp_continuous
    (continuous_snd.mul continuous_fst : Continuous fun z : G × G => z.2 * z.1)).eventually_eq
      ((1 : G), y)
  have h2 := (f.isLocallyConstant.comp_continuous
    (continuous_snd : Continuous fun z : G × G => z.2)).eventually_eq ((1 : G), y)
  filter_upwards [h1, h2] with z hz1 hz2
  change f (z.2 * z.1) = f (y * 1) at hz1
  change f z.2 = f y at hz2
  rw [hz1, hz2, mul_one]

end Translation

variable (k G : Type u) [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (X : Type u) [AddCommGroup X] [Module k X]

noncomputable def discreteCoindRep : Representation k G (LocallyConstant G X) where
  toFun g := LocallyConstant.comapₗ k (ContinuousMap.mulRight g)
  map_one' := by
    ext f x
    simp
  map_mul' g h := by
    ext f x
    simp [mul_assoc]

@[simp]
theorem discreteCoindRep_apply (g : G) (f : LocallyConstant G X) (x : G) :
    discreteCoindRep k G X g f x = f (x * g) :=
  rfl

noncomputable abbrev discreteCoind : Rep.{u} k G :=
  Rep.of (discreteCoindRep k G X)

instance isDiscreteRep_discreteCoind [CompactSpace G] : IsDiscreteRep (discreteCoind k G X) :=
  ⟨fun f => Subgroup.isOpen_of_mem_nhds (g := 1) _ <|
    Filter.mem_of_superset (eventually_forall_mul_eq f) fun g (hg : ∀ x, f (x * g) = f x) =>
      LocallyConstant.ext fun x => hg x⟩

noncomputable def coindEval : LocallyConstant G X →ₗ[k] X where
  toFun f := f 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl


section Embedding

variable {k G}

noncomputable def coindEmbedding (A : Rep.{u} k G) [IsDiscreteRep A] : A ⟶ discreteCoind k G A :=
  Rep.ofHom
    { toFun := fun a => ⟨fun g => A.ρ g a, isLocallyConstant_apply A a⟩
      map_add' := fun a b => LocallyConstant.ext fun g => map_add (A.ρ g) a b
      map_smul' := fun r a => LocallyConstant.ext fun g => map_smul (A.ρ g) r a
      isIntertwining' := fun h => LinearMap.ext fun a => LocallyConstant.ext fun x => by
        change A.ρ x (A.ρ h a) = A.ρ (x * h) a
        rw [map_mul, mul_apply_eq_comp] }

@[simp]
theorem coindEval_coindEmbedding (A : Rep.{u} k G) [IsDiscreteRep A] (a : A) :
    coindEval k G A ((coindEmbedding A).hom a) = a := by
  change A.ρ 1 a = a
  rw [map_one, one_apply_eq_self]

theorem coindEmbedding_injective (A : Rep.{u} k G) [IsDiscreteRep A] :
    Function.Injective (coindEmbedding A).hom :=
  Function.LeftInverse.injective (g := coindEval k G A) (coindEval_coindEmbedding A)

instance (A : Rep.{u} k G) [IsDiscreteRep A] : Mono (coindEmbedding A) :=
  (Rep.mono_iff_injective _).2 (coindEmbedding_injective A)

noncomputable def coindEmbeddingRange (A : Rep.{u} k G) [IsDiscreteRep A] :
    Submodule k (LocallyConstant G A) :=
  LinearMap.range (coindEmbedding A).hom.toLinearMap

theorem coindEmbeddingRange_le_comap (A : Rep.{u} k G) [IsDiscreteRep A] (g : G) :
    coindEmbeddingRange A ≤ (coindEmbeddingRange A).comap ((discreteCoind k G A).ρ g) := by
  rintro _ ⟨a, rfl⟩
  exact ⟨A.ρ g a, Rep.hom_comm_apply (coindEmbedding A) g a⟩

noncomputable abbrev coindCokernel (A : Rep.{u} k G) [IsDiscreteRep A] : Rep.{u} k G :=
  (discreteCoind k G A).quotient (coindEmbeddingRange A) (coindEmbeddingRange_le_comap A)

noncomputable abbrev coindCokernelπ (A : Rep.{u} k G) [IsDiscreteRep A] :
    discreteCoind k G A ⟶ coindCokernel A :=
  Rep.mkQ (discreteCoind k G A) (coindEmbeddingRange A) (coindEmbeddingRange_le_comap A)

instance isDiscreteRep_coindCokernel [CompactSpace G] (A : Rep.{u} k G) [IsDiscreteRep A] :
    IsDiscreteRep (coindCokernel A) :=
  isDiscreteRep_quotient (discreteCoind k G A) _ _

theorem coindEmbedding_comp_coindCokernelπ (A : Rep.{u} k G) [IsDiscreteRep A] :
    coindEmbedding A ≫ coindCokernelπ A = 0 := by
  ext a
  exact (Submodule.Quotient.mk_eq_zero _).2 ⟨a, rfl⟩

noncomputable def coindShortComplex (A : Rep.{u} k G) [IsDiscreteRep A] :
    ShortComplex (Rep.{u} k G) :=
  ShortComplex.mk (coindEmbedding A) (coindCokernelπ A) (coindEmbedding_comp_coindCokernelπ A)

theorem coindShortComplex_shortExact (A : Rep.{u} k G) [IsDiscreteRep A] :
    (coindShortComplex A).ShortExact := by
  apply ShortComplex.ShortExact.mk'
  · rw [← ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep.{u} k G) (ModuleCat.{u} k)),
      ShortComplex.moduleCat_exact_iff]
    intro f hf
    change Submodule.Quotient.mk (p := coindEmbeddingRange A) f = 0 at hf
    obtain ⟨a, ha⟩ := (Submodule.Quotient.mk_eq_zero _).1 hf
    exact ⟨a, ha⟩
  · change Mono (coindEmbedding A)
    infer_instance
  · exact (Rep.epi_iff_surjective _).2 (Submodule.mkQ_surjective _)

end Embedding

end GroundTheory.ProfCoh
end
