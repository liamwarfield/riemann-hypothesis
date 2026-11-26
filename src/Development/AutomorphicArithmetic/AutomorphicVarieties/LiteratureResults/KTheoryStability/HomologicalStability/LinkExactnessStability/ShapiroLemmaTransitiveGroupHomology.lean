module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.SeqChainExactAtMapIff

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.GroupHomologyDimensionShiftIsIso
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
namespace GlobalTheory.HomStab

theorem isIso_map_succ_of_shortExact : ∀ (k G H : Type) [CommRing k] [Group G] [Group H] (φ : H →* G) (X : ShortComplex (Rep k H)) (Y : ShortComplex (Rep k G)), X.ShortExact → Y.ShortExact → ∀ (u₁ : X.X₁ ⟶ Rep.res φ Y.X₁) (u₂ : X.X₂ ⟶ Rep.res φ Y.X₂) (u₃ : X.X₃ ⟶ Rep.res φ Y.X₃), (∀ a, u₂.hom (X.f.hom a) = Y.f.hom (u₁.hom a)) → (∀ a, u₃.hom (X.g.hom a) = Y.g.hom (u₂.hom a)) → ∀ n : ℕ, IsZero (groupHomology X.X₂ (n + 1)) → IsZero (groupHomology Y.X₂ (n + 1)) → IsIso (groupHomology.map φ u₁ n) → IsIso (groupHomology.map φ u₂ n) → IsIso (groupHomology.map φ u₃ (n + 1)) := by
  intro k G H _ _ _ φ X Y hX hY u₁ u₂ u₃ h12 h23 n hX2 hY2 hb hc
  have c12 : groupHomology.chainsMap φ u₁ ≫ (groupHomology.chainsFunctor k G).map Y.f =
      (groupHomology.chainsFunctor k H).map X.f ≫ groupHomology.chainsMap φ u₂ := by
    show groupHomology.chainsMap φ u₁ ≫ groupHomology.chainsMap (MonoidHom.id G) Y.f =
      groupHomology.chainsMap (MonoidHom.id H) X.f ≫ groupHomology.chainsMap φ u₂
    rw [← groupHomology.chainsMap_comp, ← groupHomology.chainsMap_comp]
    exact groupHomology.chainsMap_congr (by ext; rfl) (by ext a; simpa using (h12 a).symm)
  have c23 : groupHomology.chainsMap φ u₂ ≫ (groupHomology.chainsFunctor k G).map Y.g =
      (groupHomology.chainsFunctor k H).map X.g ≫ groupHomology.chainsMap φ u₃ := by
    show groupHomology.chainsMap φ u₂ ≫ groupHomology.chainsMap (MonoidHom.id G) Y.g =
      groupHomology.chainsMap (MonoidHom.id H) X.g ≫ groupHomology.chainsMap φ u₃
    rw [← groupHomology.chainsMap_comp, ← groupHomology.chainsMap_comp]
    exact groupHomology.chainsMap_congr (by ext; rfl) (by ext a; simpa using (h23 a).symm)
  let Φ : X.map (groupHomology.chainsFunctor k H) ⟶ Y.map (groupHomology.chainsFunctor k G) :=
    { τ₁ := groupHomology.chainsMap φ u₁
      τ₂ := groupHomology.chainsMap φ u₂
      τ₃ := groupHomology.chainsMap φ u₃
      comm₁₂ := c12
      comm₂₃ := c23 }
  have sX := groupHomology.map_chainsFunctor_shortExact hX
  have sY := groupHomology.map_chainsFunctor_shortExact hY
  have hnat := HomologicalComplex.HomologySequence.δ_naturality Φ sX sY (n + 1) n rfl
  have hf : groupHomology.map φ u₁ n ≫
      HomologicalComplex.homologyMap ((groupHomology.chainsFunctor k G).map Y.f) n =
      HomologicalComplex.homologyMap ((groupHomology.chainsFunctor k H).map X.f) n ≫
        groupHomology.map φ u₂ n := by
    have h := congrArg (HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.down ℕ) n).map c12
    exact ((HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.down ℕ) n).map_comp
      (groupHomology.chainsMap φ u₁) ((groupHomology.chainsFunctor k G).map Y.f)).symm.trans
      (h.trans ((HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.down ℕ) n).map_comp
        ((groupHomology.chainsFunctor k H).map X.f) (groupHomology.chainsMap φ u₂)))
  have hz := sY.δ_comp (n + 1) n rfl
  have monoX := groupHomology.mono_δ_of_isZero hX n hX2
  have monoY := groupHomology.mono_δ_of_isZero hY n hY2
  have exX := (ShortComplex.moduleCat_exact_iff _).mp (sX.homology_exact₁ (n + 1) n rfl)
  rw [ModuleCat.mono_iff_injective] at monoX monoY
  rw [ConcreteCategory.isIso_iff_bijective] at hb hc ⊢
  have e1 : ∀ x, ConcreteCategory.hom (groupHomology.map φ u₁ n)
      (ConcreteCategory.hom (groupHomology.δ hX (n + 1) n rfl) x) =
      ConcreteCategory.hom (groupHomology.δ hY (n + 1) n rfl)
        (ConcreteCategory.hom (groupHomology.map φ u₃ (n + 1)) x) := by
    intro x
    have h := ConcreteCategory.congr_hom hnat x
    exact h
  have e2 : ∀ x, ConcreteCategory.hom
      (HomologicalComplex.homologyMap ((groupHomology.chainsFunctor k G).map Y.f) n)
      (ConcreteCategory.hom (groupHomology.map φ u₁ n) x) =
      ConcreteCategory.hom (groupHomology.map φ u₂ n)
        (ConcreteCategory.hom
          (HomologicalComplex.homologyMap ((groupHomology.chainsFunctor k H).map X.f) n) x) := by
    intro x
    have h := ConcreteCategory.congr_hom hf x
    exact h
  have e3 : ∀ y, ConcreteCategory.hom
      (HomologicalComplex.homologyMap ((groupHomology.chainsFunctor k G).map Y.f) n)
      (ConcreteCategory.hom (groupHomology.δ hY (n + 1) n rfl) y) = 0 := by
    intro y
    have h := ConcreteCategory.congr_hom hz y
    exact h.trans rfl
  constructor
  · intro a b hab
    apply monoX
    apply hb.1
    rw [e1, e1, hab]
  · intro y
    obtain ⟨x1, hx1⟩ := hb.2 (ConcreteCategory.hom (groupHomology.δ hY (n + 1) n rfl) y)
    have h0 : ConcreteCategory.hom
        (HomologicalComplex.homologyMap ((groupHomology.chainsFunctor k H).map X.f) n) x1 = 0 := by
      apply hc.1
      rw [← e2, hx1, e3]
      exact (map_zero _).symm
    obtain ⟨x3, hx3⟩ := exX x1 h0
    refine ⟨x3, monoY ?_⟩
    exact (e1 x3).symm.trans ((congrArg _ hx3).trans hx1)

end GlobalTheory.HomStab

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
theorem _root_.GlobalTheory.T.groupHomology_dimension_shift_isIso : ∀ (k G H : Type) [CommRing k] [Group G] [Group H] (φ : H →* G) (X : ShortComplex (Rep k H)) (Y : ShortComplex (Rep k G)), X.ShortExact → Y.ShortExact → ∀ (u₁ : X.X₁ ⟶ Rep.res φ Y.X₁) (u₂ : X.X₂ ⟶ Rep.res φ Y.X₂) (u₃ : X.X₃ ⟶ Rep.res φ Y.X₃), (∀ a, u₂.hom (X.f.hom a) = Y.f.hom (u₁.hom a)) → (∀ a, u₃.hom (X.g.hom a) = Y.g.hom (u₂.hom a)) → ∀ n : ℕ, IsZero (groupHomology X.X₂ (n + 1)) → IsZero (groupHomology Y.X₂ (n + 1)) → IsIso (groupHomology.map φ u₁ n) → IsIso (groupHomology.map φ u₂ n) → IsIso (groupHomology.map φ u₃ (n + 1)) := by
  first
  | exact @GlobalTheory.HomStab.isIso_map_succ_of_shortExact
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.PermCoefPreservesShortExact
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

namespace GlobalTheory.HomStab

theorem permCoef_shortExact : ∀ (k G : Type) [CommRing k] [Group G] (X : Type) [MulAction G X] (S : ShortComplex (Rep k G)), S.ShortExact → ∃ h : permCoef X S.f ≫ permCoef X S.g = 0, (ShortComplex.mk (permCoef X S.f) (permCoef X S.g) h).ShortExact := by
  intro k G _ _ X _ S hS
  have hf : Function.Injective S.f.hom := (Rep.mono_iff_injective _).1 hS.mono_f
  have hg : Function.Surjective S.g.hom := (Rep.epi_iff_surjective _).1 hS.epi_g
  have hex : LinearMap.range S.f.hom.toLinearMap = LinearMap.ker S.g.hom.toLinearMap :=
    (hS.exact.map (forget₂ (Rep k G) (ModuleCat k))).moduleCat_range_eq_ker
  have hfg : ∀ a, S.g.hom (S.f.hom a) = 0 := fun a => by
    have := congrArg (fun φ => Rep.Hom.hom φ a) S.zero
    exact this
  have hz : permCoef X S.f ≫ permCoef X S.g = 0 := by
    ext x a y
    change S.g.hom (S.f.hom (Finsupp.single x a y)) = 0
    exact hfg _
  refine ⟨hz, ?_⟩
  have hm : Mono (permCoef X S.f) := by
    rw [Rep.mono_iff_injective]
    exact Finsupp.mapRange_injective _ (map_zero _) hf
  have he : Epi (permCoef X S.g) := by
    rw [Rep.epi_iff_surjective]
    exact Finsupp.mapRange_surjective _ (map_zero _) hg
  refine { exact := ?_ }
  rw [← ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep k G) (ModuleCat k)),
    ShortComplex.moduleCat_exact_iff_range_eq_ker]
  change (Finsupp.mapRange.linearMap S.f.hom.toLinearMap : (X →₀ S.X₁) →ₗ[k] (X →₀ S.X₂)).range =
    (Finsupp.mapRange.linearMap S.g.hom.toLinearMap : (X →₀ S.X₂) →ₗ[k] (X →₀ S.X₃)).ker
  rw [Finsupp.ker_mapRange, Finsupp.range_mapRange_linearMap _ (LinearMap.ker_eq_bot.2 hf), hex]

end GlobalTheory.HomStab

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
theorem _root_.GlobalTheory.T.permCoef_preserves_shortExact : ∀ (k G : Type) [CommRing k] [Group G] (X : Type) [MulAction G X] (S : ShortComplex (Rep k G)), S.ShortExact → ∃ h : permCoef X S.f ≫ permCoef X S.g = 0, (ShortComplex.mk (permCoef X S.f) (permCoef X S.g) h).ShortExact := by
  first
  | exact @GlobalTheory.HomStab.permCoef_shortExact
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ShapiroIsIsoGroupHomologyZero
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

namespace GlobalTheory.HomStab.ShapiroZero

theorem H0π_smul {k G : Type} [CommRing k] [Group G] (B : Rep k G) (g : G) (v : B.V) :
    (groupHomology.H0π B).hom (B.ρ g v) = (groupHomology.H0π B).hom v := by
  have e : ∀ w : B.V, (groupHomology.H0Iso B).hom.hom ((groupHomology.H0π B).hom w) =
      Representation.Coinvariants.mk B.ρ w :=
    fun w => congrArg (fun f => ModuleCat.Hom.hom f w) (groupHomology.H0π_comp_H0Iso_hom B)
  have hinj : Function.Injective (groupHomology.H0Iso B).hom.hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  apply hinj
  rw [e, e, Representation.Coinvariants.mk_self_apply]

theorem linkExactnessStability_hom_fact {k G : Type} [CommRing k] [Group G] (B : Rep k G) (v : B.V) :
    (groupHomology.H0Iso B).hom.hom ((groupHomology.H0π B).hom v) = Representation.Coinvariants.mk B.ρ v := by
  have h := congrArg (fun f => ModuleCat.Hom.hom f v) (groupHomology.H0π_comp_H0Iso_hom B)
  exact h

end GlobalTheory.HomStab.ShapiroZero


open GlobalTheory.HomStab.ShapiroZero in
theorem GlobalTheory.HomStab.isIso_map_ptMap_zero : ∀ (k G H X : Type) [CommRing k] [Group G] [Group H] [MulAction G X] (φ : H →* G) (x : X)
    (hx : ∀ h, φ h • x = x), φ.range = MulAction.stabilizer G x → (∀ y : X, ∃ g : G, g • x = y) →
    ∀ A : Rep k G, IsIso (groupHomology.map φ (ptMap φ x hx A) 0) := by
  intro k G H X _ _ _ _ φ x hx hrange htrans A
  choose s hs using htrans
  have stab : ∀ g : G, g • x = x → ∃ h : H, φ h = g := fun g hg => by
    have hmem : g ∈ φ.range := by
      rw [hrange]
      exact hg
    exact hmem
  have key : ∀ v : A.V, (groupHomology.map φ (ptMap φ x hx A) 0).hom
      ((groupHomology.H0π (Rep.res φ A)).hom v) =
      (groupHomology.H0π (permT X A)).hom (Finsupp.single x v) :=
    fun v => congrArg (fun f => ModuleCat.Hom.hom f v) (groupHomology.H0π_comp_map φ (ptMap φ x hx A))
  have resInv : ∀ (h : H) (b : A.V), (groupHomology.H0π (Rep.res φ A)).hom (A.ρ (φ h) b) =
      (groupHomology.H0π (Rep.res φ A)).hom b :=
    fun h b => GlobalTheory.HomStab.ShapiroZero.H0π_smul (Rep.res φ A) h b
  have permInv : ∀ (g : G) (w : (permT X A).V), (groupHomology.H0π (permT X A)).hom ((permT X A).ρ g w) =
      (groupHomology.H0π (permT X A)).hom w :=
    fun g w => GlobalTheory.HomStab.ShapiroZero.H0π_smul (permT X A) g w
  have piRes : Function.Surjective (groupHomology.H0π (Rep.res φ A)).hom :=
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  have piPerm : Function.Surjective (groupHomology.H0π (permT X A)).hom :=
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  have act : ∀ (g : G) (y : X) (a : A.V),
      (permT X A).ρ g (Finsupp.single y a) = Finsupp.single (g • y) (A.ρ g a) := by
    intro g y a
    simp [permT, permRep]
  let L : (X →₀ A.V) →ₗ[k] groupHomology (Rep.res φ A) 0 :=
    Finsupp.lsum k (fun y => (groupHomology.H0π (Rep.res φ A)).hom ∘ₗ (A.ρ (s y)⁻¹))
  have Lsingle : ∀ y a, L (Finsupp.single y a) = (groupHomology.H0π (Rep.res φ A)).hom (A.ρ (s y)⁻¹ a) := by
    intro y a
    simp [L]
  have hL : ∀ g : G, L ∘ₗ (permT X A).ρ g = L := by
    intro g
    ext y a
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
    rw [act, Lsingle, Lsingle]
    have ht : ((s (g • y))⁻¹ * g * s y) • x = x := by
      rw [mul_smul, mul_smul, hs y, inv_smul_eq_iff, hs]
    obtain ⟨h, hh⟩ := stab _ ht
    have e : A.ρ (s (g • y))⁻¹ (A.ρ g a) = A.ρ (φ h) (A.ρ (s y)⁻¹ a) := by
      rw [hh, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
      congr 2
      group
    rw [e, resInv]
  let N : groupHomology (permT X A) 0 →ₗ[k] groupHomology (Rep.res φ A) 0 :=
    Representation.Coinvariants.lift (permT X A).ρ L hL ∘ₗ (groupHomology.H0Iso (permT X A)).hom.hom
  have NM : ∀ v : A.V, N ((groupHomology.map φ (ptMap φ x hx A) 0).hom
      ((groupHomology.H0π (Rep.res φ A)).hom v)) = (groupHomology.H0π (Rep.res φ A)).hom v := by
    intro v
    rw [key]
    simp only [N, LinearMap.comp_apply]
    rw [GlobalTheory.HomStab.ShapiroZero.linkExactnessStability_hom_fact, Representation.Coinvariants.lift_mk, Lsingle]
    obtain ⟨h, hh⟩ := stab (s x)⁻¹ (by rw [inv_smul_eq_iff, hs])
    rw [← hh, resInv]
  rw [ConcreteCategory.isIso_iff_bijective]
  change Function.Bijective (groupHomology.map φ (ptMap φ x hx A) 0).hom
  refine ⟨?_, ?_⟩
  · intro a b hab
    obtain ⟨v, rfl⟩ := piRes a
    obtain ⟨w, rfl⟩ := piRes b
    have hN := congrArg N hab
    rw [NM, NM] at hN
    exact hN
  · intro z
    obtain ⟨w, rfl⟩ := piPerm z
    induction w using Finsupp.induction_linear with
    | zero => exact ⟨0, by simp⟩
    | add u w hu hw =>
      obtain ⟨a, ha⟩ := hu
      obtain ⟨b, hb⟩ := hw
      exact ⟨a + b, by rw [map_add (f := _), ha, hb, map_add (f := _)]⟩
    | single y a =>
      refine ⟨(groupHomology.H0π (Rep.res φ A)).hom (A.ρ (s y)⁻¹ a), ?_⟩
      rw [key, ← permInv (s y), act, hs, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
        Module.End.one_apply]

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
theorem _root_.GlobalTheory.T.shapiro_isIso_groupHomology_zero : ∀ (k G H X : Type) [CommRing k] [Group G] [Group H] [MulAction G X] (φ : H →* G) (x : X) (hx : ∀ h, φ h • x = x), φ.range = MulAction.stabilizer G x → (∀ y : X, ∃ g : G, g • x = y) → ∀ A : Rep k G, IsIso (groupHomology.map φ (ptMap φ x hx A) 0) := by
  first
  | exact @GlobalTheory.HomStab.isIso_map_ptMap_zero
  | exact @GlobalTheory.HomStab.ShapiroZero.linkExactnessStability_hom_fact
  | exact @GlobalTheory.HomStab.ShapiroZero.H0π_smul
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ProjectivePermTensorFree
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

noncomputable section

namespace GlobalTheory.HomStab

variable {k G : Type} [CommRing k] [Group G]

def freeSwap (G X ι : Type) [Group G] [MulAction G X] : (X × ι) × G ≃ (X × ι) × G where
  toFun p := ((p.2⁻¹ • p.1.1, p.1.2), p.2)
  invFun p := ((p.2 • p.1.1, p.1.2), p.2)
  left_inv p := by simp
  right_inv p := by simp

def freeLEquiv (k G X ι : Type) [CommRing k] [Group G] [MulAction G X] :
    (X →₀ ι →₀ MonoidAlgebra k G) ≃ₗ[k] ((X × ι) →₀ MonoidAlgebra k G) :=
  Finsupp.mapRange.linearEquiv (Finsupp.mapRange.linearEquiv (MonoidAlgebra.coeffLinearEquiv k)) ≪≫ₗ
    (Finsupp.curryLinearEquiv k).symm ≪≫ₗ (Finsupp.curryLinearEquiv k).symm ≪≫ₗ
    Finsupp.domLCongr (freeSwap G X ι) ≪≫ₗ Finsupp.curryLinearEquiv k ≪≫ₗ
    Finsupp.mapRange.linearEquiv (MonoidAlgebra.coeffLinearEquiv k).symm

theorem freeLEquiv_single (X ι : Type) [MulAction G X] (x : X) (i : ι) (g : G) (r : k) :
    freeLEquiv k G X ι (Finsupp.single x (Finsupp.single i (MonoidAlgebra.single g r))) =
      Finsupp.single (g⁻¹ • x, i) (MonoidAlgebra.single g r) := by
  simp [freeLEquiv, freeSwap]

def permFreeIso (k G : Type) [CommRing k] [Group G] (X ι : Type) [MulAction G X] :
    permT X (Rep.free k G ι) ≅ Rep.free k G (X × ι) :=
  Rep.mkIso { freeLEquiv k G X ι with
    isIntertwining' := fun h => by
      ext x i g : 4
      simp only [LinearMap.coe_comp, Function.comp_apply, Finsupp.lsingle_apply, MonoidAlgebra.lsingle_apply]
      rw [permRep_single]
      erw [Representation.free_single_single]
      simp [freeLEquiv_single, Representation.free_single_single, mul_smul] }

theorem main : ∀ (k G : Type) [CommRing k] [Group G] (X ι : Type) [MulAction G X],
    Projective (permT X (Rep.free k G ι)) := by
  intro k G _ _ X ι _
  exact Projective.of_iso (permFreeIso k G X ι).symm inferInstance

end GlobalTheory.HomStab

end

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
theorem _root_.GlobalTheory.T.projective_perm_tensor_free : ∀ (k G : Type) [CommRing k] [Group G] (X ι : Type) [MulAction G X], Projective (permT X (Rep.free k G ι)) := by
  first
  | exact @GlobalTheory.HomStab.main
  | exact @GlobalTheory.HomStab.freeLEquiv_single
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ProjectiveResFreeRepOfInjective
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

namespace GlobalTheory.HomStab

theorem resFunctor_isEquivalence_of_bijective {k G H : Type} [CommRing k] [Group G] [Group H]
    (ψ : H →* G) (hψ : Function.Bijective ψ) : (Rep.resFunctor (k := k) ψ).IsEquivalence := by
  let e : H ≃* G := MulEquiv.ofBijective ψ hψ
  haveI : (Rep.resFunctor (k := k) ψ).Full := Rep.full_res ψ hψ.2
  haveI : (Rep.resFunctor (k := k) ψ).EssSurj := ⟨fun N => ⟨Rep.of (N.ρ.comp e.symm.toMonoidHom),
    ⟨Rep.mkIso (.mk (LinearEquiv.refl k N.V) fun h => by
      ext x
      change N.ρ (e.symm (ψ h)) x = N.ρ h x
      have : e.symm (ψ h) = h := e.symm_apply_apply h
      rw [this])⟩⟩⟩
  exact { }

theorem projective_res_of_injective {k G H : Type} [CommRing k] [Group G] [Group H]
    (φ : H →* G) (hφ : Function.Injective φ) (P : Rep k G) [Projective P] :
    Projective (Rep.res φ P) := by
  let ψ : H →* φ.range := φ.rangeRestrict
  have hψ : Function.Bijective ψ := ⟨φ.rangeRestrict_injective_iff.2 hφ, φ.rangeRestrict_surjective⟩
  haveI := resFunctor_isEquivalence_of_bijective (k := k) ψ hψ
  have h1 : Projective (Rep.res φ.range.subtype P) :=
    (Rep.resFunctor (k := k) φ.range.subtype).projective_obj_of_projective (X := P) inferInstance
  have h2 : Projective (Rep.res ψ (Rep.res φ.range.subtype P)) :=
    (Rep.resFunctor (k := k) ψ).projective_obj_of_projective h1
  exact h2

end GlobalTheory.HomStab

theorem GlobalTheory.HomStab.projective_res_free_of_injective : ∀ (k G H : Type) [CommRing k] [Group G] [Group H] (φ : H →* G), Function.Injective φ → ∀ ι : Type, Projective (Rep.res φ (Rep.free k G ι)) := by
  intro k G H _ _ _ φ hφ ι
  exact GlobalTheory.HomStab.projective_res_of_injective φ hφ _

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
theorem _root_.GlobalTheory.T.projective_res_free_rep_of_injective : ∀ (k G H : Type) [CommRing k] [Group G] [Group H] (φ : H →* G), Function.Injective φ → ∀ ι : Type, Projective (Rep.res φ (Rep.free k G ι)) := by
  first
  | exact @GlobalTheory.HomStab.projective_res_free_of_injective
  | exact @GlobalTheory.HomStab.projective_res_of_injective
  | exact @GlobalTheory.HomStab.resFunctor_isEquivalence_of_bijective
end
end

open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

namespace GlobalTheory.HomStab

theorem shapiro_pt : ∀ (k G H X : Type) [CommRing k] [Group G] [Group H] [MulAction G X] (φ : H →* G) (x : X) (hx : ∀ h, φ h • x = x), Function.Injective φ → φ.range = MulAction.stabilizer G x → (∀ y : X, ∃ g : G, g • x = y) → (∀ (n : ℕ) (A : Rep k G), IsIso (groupHomology.map φ (ptMap φ x hx A) n)) ∧ ∀ n : ℕ, IsIso (ptH (k := k) φ x hx n) := by
  intro k G H X _ _ _ _ φ x hx hi hr ht
  have key : ∀ (n : ℕ) (A : Rep k G), IsIso (groupHomology.map φ (ptMap φ x hx A) n) := by
    intro n
    induction n with
    | zero => exact fun A => GlobalTheory.T.shapiro_isIso_groupHomology_zero k G H X φ x hx hr ht A
    | succ n ih =>
      intro A
      obtain ⟨ι, K, i, e, h, hS⟩ := GlobalTheory.T.exists_free_resolution_short_exact k G A
      have hX := hS.map_of_exact (Rep.resFunctor (k := k) φ)
      obtain ⟨hz, hY⟩ := GlobalTheory.T.permCoef_preserves_shortExact k G X _ hS
      refine GlobalTheory.T.groupHomology_dimension_shift_isIso k G H φ _ _ hX hY (ptMap φ x hx K) (ptMap φ x hx (Rep.free k G ι))
        (ptMap φ x hx A) ?_ ?_ n (GlobalTheory.T.projective_rep_groupHomology_pos_vanishes k H _ (GlobalTheory.T.projective_res_free_rep_of_injective k G H φ hi ι) n)
        (GlobalTheory.T.projective_rep_groupHomology_pos_vanishes k G _ (GlobalTheory.T.projective_perm_tensor_free k G X ι) n) (ih K) (ih _)
      · intro a
        exact (Finsupp.mapRange_single (hf := map_zero (Rep.Hom.hom i))).symm
      · intro a
        exact (Finsupp.mapRange_single (hf := map_zero (Rep.Hom.hom e))).symm
  exact ⟨key, fun n => key n (Rep.trivial k G k)⟩

end GlobalTheory.HomStab

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
theorem _root_.GlobalTheory.T.shapiro_lemma_transitive_groupHomology : ∀ (k G H X : Type) [CommRing k] [Group G] [Group H] [MulAction G X] (φ : H →* G) (x : X) (hx : ∀ h, φ h • x = x), Function.Injective φ → φ.range = MulAction.stabilizer G x → (∀ y : X, ∃ g : G, g • x = y) → (∀ (n : ℕ) (A : Rep k G), IsIso (groupHomology.map φ (ptMap φ x hx A) n)) ∧ ∀ n : ℕ, IsIso (ptH (k := k) φ x hx n) := by
  first
  | exact @GlobalTheory.HomStab.shapiro_pt
end
