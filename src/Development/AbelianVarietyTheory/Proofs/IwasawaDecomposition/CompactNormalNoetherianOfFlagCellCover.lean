module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsTanBasisOfUniqueCombination
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftThetaMapOrthogonalKernelEqRationalSpan
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMap
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RiemannExtensionOfLogGrowth

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompactNormalNoetherianOfFlagCellCover
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompactNormalNoetherianOfFlagCellCover
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.FlagEmb

theorem noetherianSpace_cell {X : Scheme.{0}} [IsLocallyNoetherian X] {T : Type} [Finite T] (m : T → ℕ)
    (U : X.affineOpens) : TopologicalSpace.NoetherianSpace (Sp (CR m U)) := by
  have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  have : IsNoetherianRing (CR m U) := inferInstance
  exact inferInstanceAs (TopologicalSpace.NoetherianSpace (PrimeSpectrum (CR m U)))

theorem compact_normal_noetherian_of_cells : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (T : Type) [Finite T] (m : T → ℕ) (B : Type) [Finite B] (V : B → X.affineOpens) (F : Scheme.{0}) (i : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ F)), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → (∀ b w, IsOpenImmersion (i b w)) → (∀ x : F, ∃ b w, x ∈ Set.range (i b w)) → CompactSpace F ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme F ∧ TopologicalSpace.NoetherianSpace F := by
  intro X _ T _ m B _ V F i hX hi hc
  have hN : TopologicalSpace.NoetherianSpace F := by
    have h1 : ∀ a : B × Pm m, TopologicalSpace.NoetherianSpace (Set.range (i a.1 a.2)) := fun a => by
      have := noetherianSpace_cell m (V a.1)
      exact TopologicalSpace.NoetherianSpace.range _ (i a.1 a.2).continuous
    have h2 := TopologicalSpace.NoetherianSpace.iUnion (fun a : B × Pm m => Set.range (i a.1 a.2))
    have h3 : (⋃ a : B × Pm m, Set.range (i a.1 a.2)) = Set.univ := by
      refine Set.eq_univ_of_forall fun x => ?_
      obtain ⟨b, w, h⟩ := hc x
      exact Set.mem_iUnion.2 ⟨(b, w), h⟩
    rw [h3] at h2
    exact TopologicalSpace.noetherian_univ_iff.1 h2
  refine ⟨inferInstance, fun x => ?_, hN⟩
  obtain ⟨b, w, y, rfl⟩ := hc x
  have := hi b w
  obtain ⟨_, _⟩ := (cell_smooth_normal X T m (V b) hX).2 y
  let e := (asIso ((i b w).stalkMap y)).commRingCatIsoToRingEquiv
  exact ⟨e.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e.symm⟩

end GlobalTheory.FlagEmb
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompactNormalNoetherianOfFlagCellCoverStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_normal_noetherian_of_flagCell_cover : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (T : Type) [Finite T] (m : T → ℕ) (B : Type) [Finite B] (V : B → X.affineOpens) (F : Scheme.{0}) (i : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ F)), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → (∀ b w, IsOpenImmersion (i b w)) → (∀ x : F, ∃ b w, x ∈ Set.range (i b w)) → CompactSpace F ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme F ∧ TopologicalSpace.NoetherianSpace F := by
  first | exact @GlobalTheory.FlagEmb.compact_normal_noetherian_of_cells | exact GlobalTheory.FlagEmb.compact_normal_noetherian_of_cells | (intros; apply GlobalTheory.FlagEmb.compact_normal_noetherian_of_cells <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCartierOnNormalizedBlowup
set_option autoImplicit false

noncomputable section

namespace GlobalTheory

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R _root_.Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
open Cartier

theorem EffCartierData.keepsRegular_of_dense {X' N : Scheme.{0}} (D : EffCartierData X')
    (ν : N ⟶ X') (hN : ∀ y : N, IsDomain (N.presheaf.stalk y))
    (hd : Dense {z : N | ν z ∉ D.idealSheaf.support}) : D.KeepsRegular ν := by
  intro i
  refine isRegularFn_iff_germ.2 fun y hy => ?_
  haveI := hN y
  refine mem_nonZeroDivisors_of_ne_zero fun h0 => ?_
  have e : (N.presheaf.germ (ν ⁻¹ᵁ D.U i) y hy).hom ((ν.app (D.U i)).hom (D.f i)) =
      (N.presheaf.germ (ν ⁻¹ᵁ D.U i) y hy).hom 0 := by rw [h0, map_zero]
  obtain ⟨W, hW, i₁, i₂, e'⟩ := N.presheaf.germ_eq y hy hy _ _ e
  obtain ⟨z, hzW, hzO⟩ := hd.inter_open_nonempty W W.isOpen ⟨y, hW⟩
  haveI := hN z
  have hzU : z ∈ ν ⁻¹ᵁ D.U i := i₁.le hzW
  have hz0 : (N.presheaf.germ _ z hzU).hom ((ν.app (D.U i)).hom (D.f i)) = 0 := by
    have := congrArg (N.presheaf.germ W z hzW).hom e'
    simpa using this
  have hunit : IsUnit ((X'.presheaf.germ (D.U i) (ν z) hzU).hom (D.f i)) := by
    have h1 : ν z ∈ X'.basicOpen (D.f i) := by
      by_contra h
      exact hzO ((D.mem_support_iff i hzU).2 h)
    exact (X'.mem_basicOpen _ _ hzU).1 h1
  have hu := hunit.map (ν.stalkMap z).hom
  rw [← EffCartierData.germ_app ν (D.f i) z hzU, hz0] at hu
  exact not_isUnit_zero hu

end GlobalTheory

namespace GlobalTheory

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R _root_.Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPluckerFlagEmbeddingOfProjectiveBase
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPluckerFlagEmbeddingOfProjectiveBase
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.FlagEmb

theorem span_plk_uvec_eq_top {X : Scheme.{0}} {T : Type} {m : T → ℕ} {M : ℕ} {U : X.affineOpens}
    {c D : Let m → Fin (M + 1) → Γ(X, U.1)} (h : LeftInv D c) (w : Pm m) (en : En m) :
    Ideal.span (Set.range (plk (uvec c w) en.2.1)) = ⊤ :=
  (Ideal.eq_top_iff_one _).2 (Ideal.mem_span_range_iff_exists_fun.2 ⟨_,
    (GlobalTheory.T.cauchyBinet_plucker_and_cellCoordinates.2 T m (CR m U) M _ _ w MvPolynomial.X
      (h.map (MvPolynomial.C : Γ(X, U.1) →+* CR m U))).1 en.1 en.2.1 en.2.2⟩)

theorem exists_isPlk : ∀ (O K : Type) [CommRing O] [Field K] (β : O →+* K) (X : Scheme.{0}) (s : X ⟶ Sp O)
    (T : Type) [Finite T] (m : T → ℕ) (M : ℕ) (B : Type) (V : B → X.affineOpens) (α : ∀ b, K →+* Γ(X, (V b).1))
    (c D : ∀ b, Let m → Fin (M + 1) → Γ(X, (V b).1)), IsProjOver s → IsCover β s V α c D →
    ∃ (P : Scheme.{0}) (p0 : P ⟶ X) (p : ∀ en : En m, P ⟶ PSpace O (plN M en.1))
      (h : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ P)), IsPlk β s V α c p0 p h := by
  intro O K _ _ β X s T _ m M B V α c D hs hC
  obtain ⟨P, p0, p, hP, hp, univ⟩ := GlobalTheory.T.exists_isProjOver_finite_fibreProduct O (En m) X s (fun en => PSpace O (plN M en.1))
    (fun en => PSpace.str O _) hs fun en => ⟨_, 𝟙 _, inferInstance, Category.id_comp _⟩
  have hb : ∀ b, cbase m (V b) ≫ s =
      spMap ((MvPolynomial.C : _ →+* CR m (V b)).comp ((α b).comp β)) := fun b => by
    rw [cbase, Category.assoc, hC.ovr b, ← Spec.map_comp]
    rfl
  have pt_str : ∀ {A : Type} [CommRing A] {N : ℕ} (c : O →+* A)
      (v : Fin (N + 1) → A) (hv : Ideal.span (Set.range v) = ⊤),
      pt c v hv ≫ PSpace.str O N = spMap c := by
    intro A _ N c v hv
    rw [pt, PSpace.str, ProjPoint.ofHom_toSpecZero_assoc, ← Spec.map_comp]
    congr 1
    ext1
    exact RingHom.ext fun r => MvPolynomial.eval₂Hom_C c v r
  choose h hh using fun (b : B) (w : Pm m) => (univ _ (cbase m (V b))
    (fun en => pt ((MvPolynomial.C : _ →+* CR m (V b)).comp ((α b).comp β)) (plk (uvec (c b) w) en.2.1)
      (span_plk_uvec_eq_top (hC.inv b) w en))
    fun en => (pt_str _ _ _).trans (hb b).symm).exists
  refine ⟨P, p0, p, h, ⟨fun b w => (hh b w).1, fun b w en => ⟨_, (hh b w).2 en⟩⟩, hP, hp, fun Z a a' h0 h1 => ?_⟩
  exact (univ Z (a ≫ p0) (fun en => a ≫ p en) fun en => by
    rw [Category.assoc, hp, Category.assoc]).unique ⟨rfl, fun _ => rfl⟩ ⟨h0.symm, fun en => (h1 en).symm⟩

end GlobalTheory.FlagEmb
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPluckerFlagEmbeddingOfProjectiveBaseStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pluckerFlagEmbedding_of_projective_base : ∀ (O K : Type) [CommRing O] [Field K] (β : O →+* K) (X : Scheme.{0}) (s : X ⟶ Sp O) (T : Type) [Finite T] (m : T → ℕ) (M : ℕ) (B : Type) (V : B → X.affineOpens) (α : ∀ b, K →+* Γ(X, (V b).1)) (c D : ∀ b, Let m → Fin (M + 1) → Γ(X, (V b).1)), IsProjOver s → IsCover β s V α c D → ∃ (P : Scheme.{0}) (p0 : P ⟶ X) (p : ∀ en : En m, P ⟶ PSpace O (plN M en.1)) (h : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ P)), IsPlk β s V α c p0 p h := by
  first | exact @GlobalTheory.FlagEmb.exists_isPlk | exact GlobalTheory.FlagEmb.exists_isPlk | (intros; apply GlobalTheory.FlagEmb.exists_isPlk <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CubicalWeilPairingTorsionConstHolomorphicFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CubicalWeilPairingTorsionConstHolomorphicFamily
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionPairFam


open HolTorsion in
theorem cubWeil_const_of_isHolTo : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (L : ReciprocityTheory.ChartRestriction.G.Semi.RigLB G) (c : ReciprocityTheory.ChartRestriction.G.Semi.CubicalStr G L) (m N : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (x x' : ∀ b, Over.mk (y b) ⟶ G) (ζ : ℂˣ) (b₀ b₁ : Fin m → ℂ), 0 < N → IsOpen B → IsPreconnected B → IsHolTo B (fun b => (x b).left) → IsHolTo B (fun b => (x' b).left) → (∀ b ∈ B, x b ^ N = 1 ∧ x' b ^ N = 1) → b₀ ∈ B → b₁ ∈ B → GlobalTheory.UU.CubWeil c N (x b₀) (x' b₀) (unitOn ζ) → GlobalTheory.UU.CubWeil c N (x b₁) (x' b₁) (unitOn ζ) := by
  intro X G _ _ L c m N B y x x' ζ b₀ b₁ hN _ hB hx hx' htor hb₀ hb₁ h₀
  let o : X ⟶ G.left := (η[G] : 𝟙_ (Over X) ⟶ G).left
  have ho : o ≫ G.hom = 𝟙 X := Over.w (η[G] : 𝟙_ (Over X) ⟶ G)
  let mk : G ⟶ G := (𝟙 G) ^ N
  have hkill : ∀ (T : Over X) (u : T ⟶ G), u ^ N = 1 ↔ u.left ≫ mk.left = T.hom ≫ o := by
    intro T u
    have e₁ : u.left ≫ mk.left = (u ^ N).left := by
      rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
    have e₂ : T.hom ≫ o = (1 : T ⟶ G).left := by
      rw [Hom.one_def, Over.comp_left, Over.toUnit_left]
    rw [e₁, e₂]
    exact ⟨fun h => by rw [h], fun h => Over.OverMorphism.ext h⟩
  let p := pullback.fst mk.left o
  let q := pullback.snd mk.left o
  have H : IsPullback p q mk.left o := IsPullback.of_hasPullback _ _
  have hpq : p ≫ G.hom = q := by
    rw [← Over.w mk, ← Category.assoc, H.w, Category.assoc, ho, Category.comp_id]
  have hy : IsHolTo B y := isHolTo_congr (isHolTo_comp hx G.hom) fun b _ => (Over.w (x b)).symm
  obtain ⟨a, ha, hab⟩ := exists_isHolTo_lift H hx hy (fun b hb => (hkill _ _).1 (htor b hb).1) hb₀
  obtain ⟨a', ha', hab'⟩ := exists_isHolTo_lift H hx' hy (fun b hb => (hkill _ _).1 (htor b hb).2) hb₀
  obtain ⟨z, hz, hzb⟩ := exists_isHolTo_lift (IsPullback.of_hasPullback q q) ha ha'
    (fun b hb => (hab b hb).2.trans (hab' b hb).2.symm) hb₀
  let T : Over X := Over.mk (pullback.fst q q ≫ q)
  let u : T ⟶ G := Over.homMk (pullback.fst q q ≫ p) (by
    show (pullback.fst q q ≫ p) ≫ G.hom = pullback.fst q q ≫ q
    rw [Category.assoc, hpq])
  let v : T ⟶ G := Over.homMk (pullback.snd q q ≫ p) (by
    show (pullback.snd q q ≫ p) ≫ G.hom = pullback.fst q q ≫ q
    rw [Category.assoc, hpq, pullback.condition])
  have hu : u ^ N = 1 := (hkill T u).2 (by
    show (pullback.fst q q ≫ p) ≫ _ = (pullback.fst q q ≫ q) ≫ o
    rw [Category.assoc, H.w, Category.assoc])
  have hv : v ^ N = 1 := (hkill T v).2 (by
    show (pullback.snd q q ≫ p) ≫ _ = (pullback.fst q q ≫ q) ≫ o
    rw [Category.assoc, H.w, pullback.condition, Category.assoc])
  obtain ⟨e, he, -⟩ := UU.existsUnique_cubWeil c hu hv
  have hek : e.val ^ N = 1 := congrArg Units.val he.pow_eq_one
  have hpull : ∀ w ∈ B, UU.CubWeil c N (x w) (x' w) (Units.map (z w).appTop.hom.toMonoidHom e) := by
    intro w hw
    let h : Over.mk (y w) ⟶ T := Over.homMk (z w) (by
      show z w ≫ pullback.fst q q ≫ q = y w
      rw [← Category.assoc, (hzb w hw).1, (hab w hw).2])
    have e₁ : h ≫ u = x w := Over.OverMorphism.ext (by
      show z w ≫ pullback.fst q q ≫ p = _
      rw [← Category.assoc, (hzb w hw).1, (hab w hw).1])
    have e₂ : h ≫ v = x' w := Over.OverMorphism.ext (by
      show z w ≫ pullback.snd q q ≫ p = _
      rw [← Category.assoc, (hzb w hw).2, (hab' w hw).1])
    have := he.comp h
    rw [e₁, e₂] at this
    exact this
  have e₀ : Units.map (z b₀).appTop.hom.toMonoidHom e = unitOn ζ := (hpull b₀ hb₀).unique h₀
  have e₁ : Units.map (z b₁).appTop.hom.toMonoidHom e = Units.map (z b₀).appTop.hom.toMonoidHom e :=
    Units.ext ((val_map_appTop (z b₁) e.val).trans
      ((congrArg _ (valAt'_eq_of_pow_eq_one hz hB hN hek hb₀ hb₁)).trans (val_map_appTop (z b₀) e.val).symm))
  have := hpull b₁ hb₁
  rw [e₁, e₀] at this
  exact this

end GlobalTheory.TorsionPairFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CubicalWeilPairingTorsionConstHolomorphicFamilyStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cubicalWeilPairing_torsion_const_holomorphic_family : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (L : ReciprocityTheory.ChartRestriction.G.Semi.RigLB G) (c : ReciprocityTheory.ChartRestriction.G.Semi.CubicalStr G L) (m N : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (x x' : ∀ b, Over.mk (y b) ⟶ G) (ζ : ℂˣ) (b₀ b₁ : Fin m → ℂ), 0 < N → IsOpen B → IsPreconnected B → IsHolTo B (fun b => (x b).left) → IsHolTo B (fun b => (x' b).left) → (∀ b ∈ B, x b ^ N = 1 ∧ x' b ^ N = 1) → b₀ ∈ B → b₁ ∈ B → GlobalTheory.UU.CubWeil c N (x b₀) (x' b₀) (unitOn ζ) → GlobalTheory.UU.CubWeil c N (x b₁) (x' b₁) (unitOn ζ) := by
  first | exact @GlobalTheory.TorsionPairFam.cubWeil_const_of_isHolTo | exact GlobalTheory.TorsionPairFam.cubWeil_const_of_isHolTo | (intros; apply GlobalTheory.TorsionPairFam.cubWeil_const_of_isHolTo <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LbIsoDetAffDetOm
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.GrCl GlobalTheory.Reg
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod
open GlobalTheory.Twist (resM resM_resM)

namespace GlobalTheory.HodgeCech

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

section Dual

variable {X : Scheme.{0}} (t : SAB H X) {S : Type} [CommRing S] {g : ℕ}

theorem tanLin_bijective (c : VB.Chart (LieVB.omega t.G) g) (x : Sp S ⟶ X) (h : ⊤ ≤ x ⁻¹ᵁ c.U) :
    Function.Bijective (tanLin t h c.e) := by
  refine ⟨tanLin_injective t h c.e le_rfl h (c.isFrame.res le_rfl), fun a => ?_⟩
  obtain ⟨v, ⟨hv, e⟩, -⟩ := GlobalTheory.TanFibre.existsUnique_tanEv E H X t S x c.U h g c.e c.isFrame a
  exact ⟨tanOf hv, funext e⟩

def dualBasis (c : VB.Chart (LieVB.omega t.G) g) (x : Sp S ⟶ X) (h : ⊤ ≤ x ⁻¹ᵁ c.U) :
    Module.Basis (Fin g) S (TanM x t.G) :=
  Module.Basis.ofEquivFun (LinearEquiv.ofBijective _ (tanLin_bijective t c x h))

theorem dualBasis_repr (c : VB.Chart (LieVB.omega t.G) g) (x : Sp S ⟶ X) (h : ⊤ ≤ x ⁻¹ᵁ c.U) (v : TanM x t.G)
    (i : Fin g) : (dualBasis t c x h).repr v i = tanLin t h c.e v i := rfl

theorem ev_detUnit (c c' : VB.Chart (LieVB.omega t.G) g) (x : Sp S ⟶ X) (h : ⊤ ≤ x ⁻¹ᵁ c.U) (h' : ⊤ ≤ x ⁻¹ᵁ c'.U)
    (hh : ⊤ ≤ x ⁻¹ᵁ (c.U ⊓ c'.U)) :
    ev x _ hh (c.isFrame.detUnit c'.isFrame inf_le_left inf_le_right).val =
      rdet ((dualBasis t c' x h').toMatrix (dualBasis t c x h)) := by
  show ev x _ hh ((c.isFrame.basis inf_le_left).det (c'.isFrame.basis inf_le_right)) = _
  rw [Module.Basis.det_apply, RingHom.map_det, rdet_self, ← Matrix.det_transpose]
  congr 1
  ext l i
  rw [Module.Basis.toMatrix_apply, dualBasis_repr, tanLin_apply, ← tanEv_resM t _ hh inf_le_right,
    sum_frMat c'.isFrame c.isFrame inf_le_right inf_le_left, tanEv_sum_smul]
  simp only [tanEv_resM t _ hh inf_le_left]
  have e : ∀ k, tanEv t (isTan_tv (dualBasis t c x h i)) h (c.e k) = if i = k then 1 else 0 := fun k => by
    rw [← tanLin_apply, ← dualBasis_repr, Module.Basis.repr_self, Finsupp.single_apply]
  simp only [e, mul_ite, _root_.mul_one, MulZeroClass.mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rfl

def detAff (t : SAB H X) (g : ℕ) : LB X :=
  ⟨{c : VB.Chart (LieVB.omega t.G) g // IsAffineOpen c.U}, fun c => c.1.U,
    fun c c' => c.1.isFrame.detUnit c'.1.isFrame inf_le_left inf_le_right⟩

theorem isLB_detAff (h : VB.IsVB (LieVB.omega t.G) g) : (detAff t g).IsLB := by
  refine ⟨top_le_iff.1 fun x _ => ?_, fun c => h.isLB_det.g_self c.1, fun c c' c'' => h.isLB_det.cocycle c.1 c'.1 c''.1⟩
  obtain ⟨U, e, hx, he⟩ := h x
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := U) (x := x) hx
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨V, _, he.res hVU⟩, hV⟩, hxV⟩

theorem lbIso_detAff (h : VB.IsVB (LieVB.omega t.G) g) : LBIso (detAff t g) (VB.det (LieVB.omega t.G) g) :=
  (VB.lbIso_det_of_frames (isLB_detAff t h) (fun c => c.1.e) (fun c => c.1.isFrame) fun _ _ => rfl).2

end Dual

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  (Y : Model Xo c β) {g : ℕ} {S : Type} [CommRing S]

theorem isAffineOpen_inf' {U V : Y.X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) : IsAffineOpen (U ⊓ V) := by
  have := projProper _ _ _ Y.proj
  have : Y.X.IsSeparated := ⟨by
    rw [← terminal.comp_from Y.s]
    infer_instance⟩
  exact hU.inf hV

variable {Y}

def pairDet (M : MChart Y) (a : (detAff Y.t g).ι) : Γ(Y.X, M.U ⊓ a.1.U)ˣ :=
  (isUnit_rdet_toMatrix (dualBasis Y.t a.1 (tau (isAffineOpen_inf' Y M.hU a.2)) (tau_le _ inf_le_right))
    (lieBasis M (tau (isAffineOpen_inf' Y M.hU a.2)) (tau_le _ inf_le_left))).unit

theorem ev_pairDet (M : MChart Y) (a : (detAff Y.t g).ι) (x : Sp S ⟶ Y.X) (h : ⊤ ≤ x ⁻¹ᵁ M.U) (h' : ⊤ ≤ x ⁻¹ᵁ a.1.U)
    (hh : ⊤ ≤ x ⁻¹ᵁ (M.U ⊓ a.1.U)) :
    ev x _ hh (pairDet M a).val = rdet ((dualBasis Y.t a.1 x h').toMatrix (lieBasis M x h)) := by
  have e : spMap (ev x _ hh) ≫ tau (isAffineOpen_inf' Y M.hU a.2) = x := spMap_ev x _ hh
  refine (map_rdet _ _).trans (congrArg rdet ?_)
  ext i j
  rw [Matrix.map_apply, Module.Basis.toMatrix_apply, Module.Basis.toMatrix_apply, dualBasis_repr, dualBasis_repr,
    ← tanPull_lieBasis M _ e (tau_le _ inf_le_left) h, tanLin_tanPull Y.t _ e (tau_le _ inf_le_right) h']
  rfl

variable (Y)

theorem lbIso_detAff_detOm : LBIso (detAff Y.t g) (detOm Y) := by
  refine ⟨⟨fun p => pairDet p.1 p.2⟩, fun p q => ?_⟩
  refine Eq.trans ?_ (mul_right_comm _ _ _)
  refine eq_mul_inv_of_mul_eq ?_
  refine Eq.trans ?_ (congrArg (· * _) (map_inv _ (detChg p.1 q.1)).symm)
  refine eq_inv_mul_of_mul_eq (Units.ext (ext_ev fun S _ z hz => ?_))
  have hp := le_preimage_mono inf_le_left hz
  have hq := le_preimage_mono inf_le_right hz
  have hp1 : ⊤ ≤ z ⁻¹ᵁ (p.1 : MChart Y).U := le_preimage_mono inf_le_left hp
  have hq1 : ⊤ ≤ z ⁻¹ᵁ (q.1 : MChart Y).U := le_preimage_mono inf_le_left hq
  have hp2 : ⊤ ≤ z ⁻¹ᵁ p.2.1.U := le_preimage_mono inf_le_right hp
  have hq2 : ⊤ ≤ z ⁻¹ᵁ q.2.1.U := le_preimage_mono inf_le_right hq
  refine (map_mul (ev z _ hz) _ _).trans ?_
  refine (congrArg₂ (· * ·) ((ev_res z _ hz (le_preimage_inf hp1 hq1) _).trans (ev_detChg _ _ z hp1 hq1 _))
    ((map_mul (ev z _ hz) _ _).trans (congrArg₂ (· * ·) ((ev_res z _ hz hp _).trans (ev_pairDet _ _ z hp1 hp2 hp))
      ((ev_res z _ hz (le_preimage_inf hp2 hq2) _).trans (ev_detUnit Y.t _ _ z hp2 hq2 _))))).trans
    (Eq.trans ?_ ((ev_res z _ hz hq _).trans (ev_pairDet _ _ z hq1 hq2 hq)).symm)
  rw [_root_.mul_comm, _root_.mul_comm (rdet _) (rdet _), rdet_toMatrix_mul, rdet_toMatrix_mul]

theorem lbIso_detOm_det (hO : (detOm Y).IsLB) (h : VB.IsVB (LieVB.omega Y.t.G) g) :
    LBIso (detOm Y) (VB.det (LieVB.omega Y.t.G) g) :=
  (lbIso_detAff_detOm Y).symm.trans hO (isLB_detAff Y.t h) h.isLB_det (lbIso_detAff Y.t h)

end GlobalTheory.HodgeCech
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.H0NeBotOfHorizontalFunction
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RiemannExtensionOfLogGrowthStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.riemann_extension_of_log_growth : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (U : Set V) (φ u : V → ℂ), IsOpen U → DifferentiableOn ℂ φ U → DifferentiableOn ℂ u {b ∈ U | φ b ≠ 0} → U ⊆ closure {b ∈ U | φ b ≠ 0} → (∀ b₀ ∈ U, ∃ (C : ℝ) (k : ℕ), ∀ᶠ b in 𝓝 b₀, φ b ≠ 0 → ‖u b‖ ≤ C * (1 + |Real.log ‖φ b‖|) ^ k) → ∃ u' : V → ℂ, DifferentiableOn ℂ u' U ∧ Set.EqOn u' u {b ∈ U | φ b ≠ 0} := by
  first | exact @GlobalTheory.LogExt.riemann_extension_log | exact GlobalTheory.LogExt.riemann_extension_log | (intros; apply GlobalTheory.LogExt.riemann_extension_log <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RiemannRochNeBotOfHolomorphicSectionNeBot
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RiemannRochNeBotOfHolomorphicSectionNeBot
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology

namespace GlobalTheory.ShFam.Hor

theorem riemannRoch_ne_bot_of_holomorphicSection_ne_bot : ∀ (F : Type) [Field F] (Y : GlobalTheory.ProjVar.Var F) (σ : F →+* ℂ)
    (R : AnRead Y.str σ Y.dim) (D : Y.Dv), R.holSec (Y.lb D) ≠ ⊥ → Y.H0 D ≠ ⊥ := by
  intro F _ Y σ R D hR hH
  refine hR ?_
  have P := GlobalTheory.Cartier.presents_toLB D
  have hs : ∀ s : (Y.lb D).Sec, s = 0 := fun s => by
    have hm : P.rat s ∈ Y.H0 D := P.rat_mem s
    rw [hH, Submodule.mem_bot] at hm
    exact P.rat_injective (hm.trans (map_zero P.rat).symm)
  have hx : ∀ x : SecC Y.str σ (Y.lb D), x = 0 := fun x => by
    have hle : Submodule.span ℂ (Set.range (SecC.of Y.str σ : (Y.lb D).Sec → _)) ≤ ⊥ :=
      Submodule.span_le.2 (by
        rintro _ ⟨s, rfl⟩
        rw [hs s, map_zero]
        exact zero_mem _)
    exact (Submodule.mem_bot ℂ).1 (hle (SecC.span_range_of.ge Submodule.mem_top))
  have hb := GlobalTheory.AnRead.bijective_valC Y.isProjOver R P.isLB
  refine (Submodule.eq_bot_iff _).2 fun f hf => ?_
  obtain ⟨x, hxf⟩ := hb.2 ⟨f, hf⟩
  rw [hx x, map_zero] at hxf
  exact (congrArg Subtype.val hxf).symm

end GlobalTheory.ShFam.Hor
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RiemannRochNeBotOfHolomorphicSectionNeBotStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.H0_ne_bot_of_holSec_ne_bot : ∀ (F : Type) [Field F] (Y : GlobalTheory.ProjVar.Var F) (σ : F →+* ℂ) (R : AnRead Y.str σ Y.dim) (D : Y.Dv), R.holSec (Y.lb D) ≠ ⊥ → Y.H0 D ≠ ⊥ := by
  first | exact @GlobalTheory.ShFam.Hor.riemannRoch_ne_bot_of_holomorphicSection_ne_bot | exact GlobalTheory.ShFam.Hor.riemannRoch_ne_bot_of_holomorphicSection_ne_bot | (intros; apply GlobalTheory.ShFam.Hor.riemannRoch_ne_bot_of_holomorphicSection_ne_bot <;> assumption)
end
end

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology
open Set GlobalTheory.CxPts GlobalTheory.Cartier.CartierDiv

namespace GlobalTheory.ShFam.Hor.Sec

section General

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {d : ℕ} {R : AnRead p σ d}
  {A : Set (CxPts p σ)}

theorem eqOn_of_dense (hA : Dense A) {T : Set (CxPts p σ)} (hT : IsOpen T) {f g : CxPts p σ → ℂ}
    (hf : R.HoloOn T f) (hg : R.HoloOn T g) (h : EqOn f g (T ∩ A)) : EqOn f g T :=
  h.of_subset_closure (hf.continuousOn hT) (hg.continuousOn hT) inter_subset_left (hA.open_subset_closure_inter hT)

theorem exists_holoOn_of_local (hA : Dense A) {S : Set (CxPts p σ)} {u : CxPts p σ → ℂ}
    (h : ∀ y ∈ S, ∃ (T : Set (CxPts p σ)) (f : CxPts p σ → ℂ), IsOpen T ∧ y ∈ T ∧ R.HoloOn T f ∧ EqOn f u (T ∩ A)) :
    ∃ f, R.HoloOn S f ∧ EqOn f u (S ∩ A) := by
  choose! T f hT hy hf he using h
  refine ⟨fun y => f y y, AnRead.holoOn_of_cover (T := fun y : S => T y) (fun y => hT y y.2)
    (fun y hS => ⟨⟨y, hS⟩, hy y hS⟩) fun y => ((hf y y.2).mono inter_subset_right).congr fun z hz => ?_,
    fun y hS => he y hS.1 ⟨hy y hS.1, hS.2⟩⟩
  exact eqOn_of_dense hA ((hT z hz.1).inter (hT y y.2)) ((hf z hz.1).mono inter_subset_left)
    ((hf y y.2).mono inter_subset_right)
    (fun w hw => (he z hz.1 ⟨hw.1.1, hw.2⟩).trans (he y y.2 ⟨hw.1.2, hw.2⟩).symm) ⟨hy z hz.1, hz.2⟩

theorem isHolTo_symm (c : AlgChart p σ d) {B : Set (ReciprocityTheory.L2DbarEstimates.V d)} (hB : IsOpen B) (h : B ⊆ c.e.target) :
    IsHolTo B fun b => (c.e.symm b).1 := fun U f => by
  refine ⟨?_, (c.holo U f).mono fun b hb => ⟨h hb.1, hb.2⟩⟩
  exact (c.e.continuousOn_symm.mono h).isOpen_inter_preimage hB (isOpen_ptsIn U)

variable [IsIntegral Y]

theorem ev_mul_eq {U V W : Y.Opens} {a : Γ(Y, U)} {b : Γ(Y, V)} {c : Γ(Y, W)} {y : CxPts p σ}
    (hU : y ∈ ptsIn p σ U) (hV : y ∈ ptsIn p σ V) (hW : y ∈ ptsIn p σ W)
    (h : ∀ h₁ h₂ h₃, fnOf U h₁ a * fnOf V h₂ b = fnOf W h₃ c) : ev p σ U a y * ev p σ V b y = ev p σ W c y := by
  have hy : y ∈ ptsIn p σ (U ⊓ V ⊓ W) := mem_ptsIn_inf.2 ⟨mem_ptsIn_inf.2 ⟨hU, hV⟩, hW⟩
  rw [← ev_res (inf_le_left.trans inf_le_left) hy, ← ev_res (inf_le_left.trans inf_le_right) hy,
    ← ev_res inf_le_right hy, ← ev_mul]
  congr 1
  exact fn_ext fun _ => by rw [map_mul, fnOf_resG, fnOf_resG, fnOf_resG, h]

theorem holSec_ne_bot [Nonempty (CxPts p σ)] (hA : Dense A) (D : CartierDiv Y) (W : Y → Y.Opens)
    (δ : Y → Y.functionFieldˣ) (hW : ∀ y, y ∈ W y) (hδ : ∀ y, ∀ y' ∈ W y, D.IsEqn y' (δ y))
    (u : Y → CxPts p σ → ℂ) (hu : ∀ y, R.HoloOn (ptsIn p σ (W y)) (u y))
    (h0 : ∀ y, ∀ z ∈ ptsIn p σ (W y) ∩ A, u y z ≠ 0)
    (hc : ∀ y y' (r : Γ(Y, W y ⊓ W y')), (∀ h, fnOf _ h r = (δ y : Y.functionField) / (δ y' : Y.functionField)) →
      ∀ z ∈ ptsIn p σ (W y ⊓ W y') ∩ A, u y z = ev p σ _ r z * u y' z) :
    R.holSec (toLB D) ≠ ⊥ := by
  choose r hr using fun (i : (toLB D).ι) (y : Y) => exists_unit_fnOf_eq (U := (toLB D).U i ⊓ W y)
    (f := (i.1.2 : Y.functionField) / (δ y : Y.functionField))
    fun x hx => (hδ y x hx.2).iff_unitAt.1 (i.2.2 x hx.1)
  let pt (z : CxPts p σ) : Y := z.1 (IsLocalRing.closedPoint ℂ)
  have hpt (z : CxPts p σ) : z ∈ ptsIn p σ (W (pt z)) := mem_ptsIn.2 (hW _)
  let s (i : (toLB D).ι) (z : CxPts p σ) : ℂ := ev p σ _ (r i (pt z)).val z * u (pt z) z
  have key {i y z} (hi : z ∈ ptsIn p σ ((toLB D).U i)) (hy : z ∈ ptsIn p σ (W y)) :
      s i z = ev p σ _ (r i y).val z * u y z := by
    obtain ⟨t, ht⟩ := exists_unit_fnOf_eq (U := W (pt z) ⊓ W y)
      (f := (δ (pt z) : Y.functionField) / (δ y : Y.functionField))
      fun x hx => (hδ y x hx.2).iff_unitAt.1 (hδ _ x hx.1)
    have hz := mem_ptsIn_inf.2 ⟨hpt z, hy⟩
    have e : u (pt z) z = ev p σ _ t.val z * u y z :=
      eqOn_of_dense (R := R) hA (isOpen_ptsIn _) ((hu _).mono (ptsIn_mono inf_le_left))
        ((R.holoOn_ev _ t.val).mul ((hu y).mono (ptsIn_mono inf_le_right))) (hc _ _ _ ht) hz
    rw [← ev_mul_eq (a := (r i (pt z)).val) (b := t.val) (mem_ptsIn_inf.2 ⟨hi, hpt z⟩) hz (mem_ptsIn_inf.2 ⟨hi, hy⟩)
      fun _ _ _ => by rw [hr, hr, ht, div_mul_div_cancel₀ (Units.ne_zero _)], _root_.mul_assoc, ← e]
  have hs : s ∈ R.holSec (toLB D) := by
    refine ⟨⟨fun i j z hi hj => ?_, fun i z hi => ?_⟩, fun i => ?_⟩
    · have e := ev_mul_eq (a := ((toLB D).g i j).val) (b := (r j (pt z)).val) (c := (r i (pt z)).val)
        (mem_ptsIn_inf.2 ⟨hi, hj⟩) (mem_ptsIn_inf.2 ⟨hj, hpt z⟩) (mem_ptsIn_inf.2 ⟨hi, hpt z⟩)
        fun _ _ _ => by rw [hr, hr, fnOf_toLB_g, div_mul_div_cancel₀ (Units.ne_zero _)]
      simp only [s]
      rw [← e, _root_.mul_assoc]
      rfl
    · simp only [s]
      rw [ev_of_notMem (fun h => hi (mem_ptsIn_inf.1 h).1), zero_mul]
    · exact AnRead.holoOn_of_cover (T := fun y => ptsIn p σ (W y)) (fun y => isOpen_ptsIn _)
        (fun z _ => ⟨_, hpt z⟩) fun y =>
        ((AnRead.holoOn_ev_of_subset (r i y).val fun _ => mem_ptsIn_inf.2).mul
          ((hu y).mono inter_subset_right)).congr fun z hz => key hz.1 hz.2
  obtain ⟨z, hz⟩ := hA.nonempty
  intro hb
  rw [hb, Submodule.mem_bot] at hs
  let i : (toLB D).ι := ⟨(W (pt z), δ (pt z)), gen_mem (hW _), hδ _⟩
  exact mul_ne_zero (ev_ne_zero (mem_ptsIn_inf.2 ⟨hpt z, hpt z⟩) (r i (pt z)).isUnit) (h0 _ z ⟨hpt z, hz⟩)
    (congrFun (congrFun hs i) z)

end General

section Flag

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {σ : c.F →+* ℂ}

theorem logGrowth_inv {h : CxFr Z σ → ℂ} (hg : LogGrowth h) : LogGrowth fun a => (h a)⁻¹ := fun x₀ => by
  obtain ⟨N, φ, h₁, h₂, h₃, h₄, h₅⟩ := hg x₀
  refine ⟨N, φ, h₁, h₂, h₃, h₄, fun V _ _ _ B a hB ha hN b₀ hb => ?_⟩
  obtain ⟨C, k, hk⟩ := h₅ V B a hB ha hN b₀ hb
  exact ⟨C, k, hk.mono fun b hb hi => ⟨(hb hi).2, by rw [inv_inv]; exact (hb hi).1⟩⟩

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ' : k →+* ℂ} {d : ℕ}

theorem inner_iff {π : Y ⟶ gen Z} {z : CxPts p σ'} {x : CxPts (genStr Z) σ} (h : x.1 = z.1 ≫ π) :
    Inner x ↔ z ∈ ptsIn p σ' (π ⁻¹ᵁ (genBd Z).compl) := by
  rw [Inner, h, mem_ptsIn]
  rfl

theorem exists_extension (R : AnRead p σ' d) (π : Y ⟶ gen Z)
    (hA : Dense (ptsIn p σ' (π ⁻¹ᵁ (genBd Z).compl))) {S : Set (CxPts p σ')} (hS : IsOpen S)
    {a : CxPts p σ' → CxFr Z σ} (ha : ∀ z ∈ S, (a z).1.1 = z.1 ≫ π)
    (hf : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (B : Set V)
      (x : V → CxPts p σ'), IsOpen B → IsHolTo B (fun b => (x b).1) → MapsTo x B S → HolFam B fun b => a (x b))
    {h : CxFr Z σ → ℂ}
    (hh : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (B : Set V)
      (a : V → CxFr Z σ), IsOpen B → HolFam B a → (∀ b ∈ B, Inner (a b).1) → DifferentiableOn ℂ (fun b => h (a b)) B)
    (hg : LogGrowth h) :
    ∃ f, R.HoloOn S f ∧ EqOn f (fun z => h (a z)) (S ∩ ptsIn p σ' (π ⁻¹ᵁ (genBd Z).compl)) := by
  refine exists_holoOn_of_local hA fun y hy => ?_
  obtain ⟨N, φ, hN, hyN, hφ, hφ0, hgr⟩ := hg (a y).1
  obtain ⟨N', hN', rfl⟩ := isOpen_induced_iff.1 hN
  obtain ⟨i, hi⟩ := R.cover y
  set c := R.chart i
  let T : Set (CxPts p σ') := S ∩ (fun z => z.1 ≫ π) ⁻¹' N'
  have hT : IsOpen T := hS.inter (hN'.preimage ((Points.continuous_comp π).comp continuous_subtype_val))
  have hTN (z) (hz : z ∈ T) : (a z).1 ∈ Subtype.val ⁻¹' N' := by
    rw [mem_preimage, ha z hz.1]; exact hz.2
  have hyT : y ∈ T := ⟨hy, by rw [mem_preimage, ← ha y hy]; exact hyN⟩
  let B := c.e.target ∩ c.e.symm ⁻¹' T
  have hB : IsOpen B := ChartGlue.isOpen_over c.e hT
  have hfam {B' : Set (ReciprocityTheory.L2DbarEstimates.V d)} (hB' : IsOpen B') (e : B' ⊆ B) : HolFam B' fun b => a (c.e.symm b) :=
    hf _ B' c.e.symm hB' (isHolTo_symm c hB' (e.trans inter_subset_left)) fun b hb => (e hb).2.1
  have hφB : DifferentiableOn ℂ (fun b => φ (a (c.e.symm b)).1) B :=
    hφ _ B (fun b => (a (c.e.symm b)).1) hB (hfam hB subset_rfl).1 fun b hb => hTN _ hb.2
  have hin (z) (hz : z ∈ T) : φ (a z).1 ≠ 0 ↔ z ∈ ptsIn p σ' (π ⁻¹ᵁ (genBd Z).compl) :=
    (hφ0 _ (hTN z hz)).trans (inner_iff (ha z hz.1))
  have hB' : IsOpen {b ∈ B | φ (a (c.e.symm b)).1 ≠ 0} :=
    hφB.continuousOn.isOpen_inter_preimage hB isOpen_ne
  obtain ⟨u, hu, he⟩ := GlobalTheory.T.riemann_extension_of_log_growth _ B _ (fun b => h (a (c.e.symm b))) hB hφB
    (hh _ _ _ hB' (hfam hB' (sep_subset _ _)) fun b hb => (hφ0 _ (hTN _ hb.1.2)).1 hb.2)
    (fun b hb => by
      have hs := c.e.map_target hb.1
      have h₁ := hA.open_subset_closure_inter (c.e.open_source.inter hT) ⟨hs, hb.2⟩
      have h₂ := (c.e.continuousAt hs).continuousWithinAt.mem_closure_image h₁
      rw [c.e.right_inv hb.1] at h₂
      refine closure_mono ?_ h₂
      rintro _ ⟨z, hz, rfl⟩
      refine ⟨ChartGlue.mem_over c.e hz.1.1 hz.1.2, ?_⟩
      rw [c.e.left_inv hz.1.1]
      exact (hin z hz.1.2).2 hz.2)
    fun b hb => by
      obtain ⟨C, n, hn⟩ := hgr _ B _ hB (hfam hB subset_rfl) (fun b hb => hTN _ hb.2) b hb
      refine ⟨C, n, ?_⟩
      filter_upwards [hn, hB.mem_nhds hb] with b' h₁ h₂ h₃
      exact (h₁ ((hφ0 _ (hTN _ h₂.2)).1 h₃)).1
  refine ⟨c.e.source ∩ T, u ∘ c.e, c.e.open_source.inter hT, ⟨hi, hyT⟩,
    AnRead.holoOn_of_chart c (hu.congr fun b hb => congrArg u (c.e.right_inv hb.1)), fun z hz => ?_⟩
  have := he (x := c.e z) ⟨ChartGlue.mem_over c.e hz.1.1 hz.1.2, by
    rw [c.e.left_inv hz.1.1]; exact (hin z hz.1.2).2 hz.2⟩
  simpa only [c.e.left_inv hz.1.1, Function.comp_apply] using this

end Flag

end GlobalTheory.ShFam.Hor.Sec
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlowupDivisorTrivialOnFibers
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory

theorem cechPic_sp_field_eq_zero (K : Type) [Field K] (c : GlobalTheory.CechPic.Pic (Sp K)) : c = 0 := by
  obtain ⟨L, hL, rfl⟩ := GlobalTheory.CechPic.cls_surj c
  exact (GlobalTheory.CechPic.cls_eq_zero_iff hL).2 (GlobalTheory.LB.exists_isGen_of_isLocalRing hL)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StalkSpecializesCompatRingMap
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Cartier

namespace GlobalTheory.TorRef

theorem stalkClosedPointTo_comp_spMap_specializes (X : Scheme.{0}) {R W : Type} [CommRing R] [IsLocalRing R]
    [CommRing W] [IsLocalRing W] (ξ : Sp R ⟶ X) (g : R →+* W)
    (hs : (spMap g ≫ ξ) (closedPoint W) ⤳ ξ (closedPoint R)) (a : X.presheaf.stalk (ξ (closedPoint R))) :
    (Scheme.stalkClosedPointTo (spMap g ≫ ξ)).hom ((X.presheaf.stalkSpecializes hs).hom a) =
      g ((Scheme.stalkClosedPointTo ξ).hom a) := by
  have key : X.presheaf.stalkSpecializes hs ≫ Scheme.stalkClosedPointTo (spMap g ≫ ξ) =
      Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom g := by
    apply Spec.map_injective
    rw [← cancel_mono (X.fromSpecStalk (ξ (closedPoint R))), Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.Spec_stalkClosedPointTo_fromSpecStalk,
      Spec.map_comp, Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  exact congrArg (fun q => q.hom a) key

end GlobalTheory.TorRef
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationScaledMultiple
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.TorRef.Scale

variable {X : Scheme.{0}}

theorem idlAlong_nsmul (D : EffCartierData X) (n : ℕ) {R : Type} [CommRing R] [IsLocalRing R] (ξ : Sp R ⟶ X) :
    idlAlong (D.nsmul n).idealSheaf ξ = idlAlong D.idealSheaf ξ ^ n := by
  obtain ⟨i, hi⟩ := D.exists_mem (ξ (IsLocalRing.closedPoint R))
  have h1 := (D.nsmul n).stalkId_idealSheaf i _ hi
  have h2 := D.stalkId_idealSheaf i _ hi
  have h3 : (X.presheaf.germ ((D.nsmul n).U i) (ξ (IsLocalRing.closedPoint R)) hi).hom ((D.nsmul n).f i) =
      ((X.presheaf.germ (D.U i) (ξ (IsLocalRing.closedPoint R)) hi).hom (D.f i)) ^ n :=
    map_pow _ _ _
  unfold idlAlong
  rw [h1, h3, h2, ← Ideal.map_pow, Ideal.span_singleton_pow]

end GlobalTheory.TorRef.Scale
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CodimOneGenerizationStalk
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Cartier

namespace GlobalTheory.LocalRingGeneralisation

theorem stalk_fromSpecStalk_equiv (X : Scheme.{0}) (x : X) (p : Ideal (X.presheaf.stalk x)) [p.IsPrime] :
    ∃ e : X.presheaf.stalk (X.fromSpecStalk x (⟨p, inferInstance⟩ : PrimeSpectrum (X.presheaf.stalk x))) ≃+*
        Localization.AtPrime p,
      ∀ (U : X.Opens) (hq : X.fromSpecStalk x (⟨p, inferInstance⟩ : PrimeSpectrum (X.presheaf.stalk x)) ∈ U)
        (hx : x ∈ U) (s : Γ(X, U)),
        e ((X.presheaf.germ U _ hq).hom s) =
          algebraMap (X.presheaf.stalk x) (Localization.AtPrime p) ((X.presheaf.germ U x hx).hom s) := by
  let y : Spec (X.presheaf.stalk x) := (⟨p, inferInstance⟩ : PrimeSpectrum (X.presheaf.stalk x))
  have := isIso_stalkMap_fromSpecStalk X x y
  refine ⟨(asIso ((X.fromSpecStalk x).stalkMap y) ≪≫ Spec.stalkIso _ y).commRingCatIsoToRingEquiv, ?_⟩
  intro U hq hx s
  have h1 := Scheme.Hom.germ_stalkMap_apply (X.fromSpecStalk x) U y hq s
  show (Spec.stalkIso _ y).hom ((X.fromSpecStalk x).stalkMap y ((X.presheaf.germ U _ hq).hom s)) = _
  rw [h1, Scheme.fromSpecStalk_app hx]
  have h2 := congrArg (fun f => f.hom ((Scheme.ΓSpecIso (X.presheaf.stalk x)).inv.hom ((X.presheaf.germ U x hx).hom s)))
    (Spec.germ_stalkMapIso_hom (R := X.presheaf.stalk x) (x := y))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
  rw [← CommRingCat.comp_apply (Scheme.ΓSpecIso (X.presheaf.stalk x)).inv (Scheme.ΓSpecIso (X.presheaf.stalk x)).hom,
    Iso.inv_hom_id, CommRingCat.id_apply] at h2
  rw [← h2]
  simp only [← CommRingCat.comp_apply, Category.assoc, TopCat.Presheaf.germ_res]
  erw [TopCat.Presheaf.germ_res]

end GlobalTheory.LocalRingGeneralisation
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartRingFormallyUnramified
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.GenFan

theorem formallyUnramified_residue_comp_of_isEtaleCompletion :
    ∀ (k : Type) [Field k] (m e : ℕ) [CharZero (ChartRing k m e)] {A : Type} [CommRing A] [IsLocalRing A]
      (φ : A →+* ChartRing k m e), IsEtaleCompletion φ → ((residue (ChartRing k m e)).comp φ).FormallyUnramified := by
  intro k _ m e _ A _ _ φ hφ
  obtain ⟨-, hmax, hfin⟩ := hφ
  haveI : IsLocalHom φ := by
    constructor
    intro a ha
    by_contra hna
    have h1 : a ∈ maximalIdeal A := (mem_maximalIdeal a).2 hna
    have h2 : φ a ∈ maximalIdeal (ChartRing k m e) := hmax ▸ Ideal.mem_map_of_mem φ h1
    exact (mem_maximalIdeal _).1 h2 ha
  rw [← ResidueField.map_comp_residue]
  refine RingHom.FormallyUnramified.comp (RingHom.FormallyUnramified.of_surjective residue_surjective) ?_
  have hfin' : (ResidueField.map φ).Finite := by
    rw [← ResidueField.map_comp_residue] at hfin
    exact RingHom.Finite.of_comp_finite hfin
  haveI : CharZero k := RingHom.charZero (algebraMap k (ChartRing k m e))
  haveI : CharZero (ResidueField (ChartRing k m e)) :=
    (RingHom.charZero_iff ((residue (ChartRing k m e)).comp (algebraMap k (ChartRing k m e))).injective).1 inferInstance
  haveI : CharZero (ResidueField A) := RingHom.charZero (ResidueField.map φ)
  letI := (ResidueField.map φ).toAlgebra
  haveI : Module.Finite (ResidueField A) (ResidueField (ChartRing k m e)) := hfin'
  haveI : Algebra.IsSeparable (ResidueField A) (ResidueField (ChartRing k m e)) := inferInstance
  exact Algebra.FormallyUnramified.of_isSeparable _ _

end GlobalTheory.GenFan
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RatLinearIndependentCoordsOfRealIndependent
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RatLinearIndependentCoordsOfRealIndependent
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem rowsInd_rat_of_real : ∀ (g r r₀ : ℕ) (lam : Fin r → Fin g → ℂ) (u : Fin r₀ → Fin g → ℂ) (A : Fin r₀ → Fin r → ℤ), LinearIndependent ℝ u → (∀ i, u i = ∑ m, A i m • lam m) → LinearIndependent ℚ (fun i j => (A i j : ℚ)) := by
  intro g r r₀ lam u A hu hA
  rw [Fintype.linearIndependent_iff] at hu ⊢
  intro c hc i
  have hc' : ∀ m, ∑ i, (c i : ℝ) * (A i m : ℝ) = 0 := by
    intro m
    have h1 := congrFun hc m
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1
    have h2 := congrArg (Rat.cast : ℚ → ℝ) h1
    push_cast at h2
    exact h2
  have hsum : ∑ i, (c i : ℝ) • u i = 0 := by
    have e : ∀ i, (c i : ℝ) • u i = ∑ m, ((c i : ℝ) * (A i m : ℝ)) • lam m := by
      intro i
      rw [hA i, Finset.smul_sum]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [← Int.cast_smul_eq_zsmul ℝ, smul_smul]
    simp_rw [e]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul, hc', zero_smul, Finset.sum_const_zero]
  have h3 := hu (fun i => (c i : ℝ)) hsum i
  exact_mod_cast h3

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RatLinearIndependentCoordsOfRealIndependentStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rat_linearIndependent_coords_of_real_independent : ∀ (g r r₀ : ℕ) (lam : Fin r → Fin g → ℂ) (u : Fin r₀ → Fin g → ℂ) (A : Fin r₀ → Fin r → ℤ), LinearIndependent ℝ u → (∀ i, u i = ∑ m, A i m • lam m) → LinearIndependent ℚ (fun i j => (A i j : ℚ)) := by
  first | exact @GlobalTheory.rowsInd_rat_of_real | exact GlobalTheory.rowsInd_rat_of_real | (intros; apply GlobalTheory.rowsInd_rat_of_real <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackAnalytic
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackAnalytic
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.ShFam.Hor.LogCh

theorem IsLatFam.pullback_analytic : ∀ (m n g : ℕ) (B : Set (Fin n → ℂ)) (B' : Set (Fin m → ℂ))
    (K : (Fin n → ℂ) → Set (Fin g → ℂ)) (φ : (Fin m → ℂ) → Fin n → ℂ),
    GlobalTheory.ShFam.Hor.LogCh.IsLatFam B K → IsOpen B' → AnalyticOnNhd ℂ φ B' → Set.MapsTo φ B' B →
      GlobalTheory.ShFam.Hor.LogCh.IsLatFam B' (fun b => K (φ b)) := by
  intro m n g B B' K φ hK hB' hφ hmaps
  obtain ⟨_, h2, h3, h4⟩ := hK
  let Ψ : (Fin m → ℂ) × (Fin g → ℂ) → (Fin n → ℂ) × (Fin g → ℂ) := fun q => (φ q.1, q.2)
  refine ⟨hB', fun b hb => h2 (φ b) (hmaps hb), ?_, ?_⟩
  · have hcont : ContinuousOn Ψ (B' ×ˢ (Set.univ : Set (Fin g → ℂ))) :=
      (hφ.continuousOn.comp continuousOn_fst
        (fun q (hq : q ∈ B' ×ˢ (Set.univ : Set (Fin g → ℂ))) => hq.1)).prodMk continuousOn_snd
    have hopen := hcont.isOpen_inter_preimage (hB'.prod isOpen_univ) h3
    convert hopen using 1
    ext q
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, and_true, Set.mem_preimage, Ψ]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, hmaps h1, h2⟩
    · rintro ⟨h1, _, h2⟩
      exact ⟨h1, h2⟩
  · intro b₀ hb₀ w₀ hw₀
    obtain ⟨ζ, hζ0, hζa, hev⟩ := h4 (φ b₀) (hmaps hb₀) w₀ hw₀
    refine ⟨fun b => ζ (φ b), hζ0, hζa.comp (hφ b₀ hb₀), ?_⟩
    have hΨ : ContinuousAt Ψ (b₀, w₀) :=
      ((hφ b₀ hb₀).continuousAt.comp continuousAt_fst).prodMk continuousAt_snd
    exact hΨ.tendsto.eventually hev

end GlobalTheory.ShFam.Hor.LogCh
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackAnalyticStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLatFam_comp_of_analyticOnNhd : ∀ (m n g : ℕ) (B : Set (Fin n → ℂ)) (B' : Set (Fin m → ℂ)) (K : (Fin n → ℂ) → Set (Fin g → ℂ)) (φ : (Fin m → ℂ) → Fin n → ℂ), GlobalTheory.ShFam.Hor.LogCh.IsLatFam B K → IsOpen B' → AnalyticOnNhd ℂ φ B' → Set.MapsTo φ B' B → GlobalTheory.ShFam.Hor.LogCh.IsLatFam B' (fun b => K (φ b)) := by
  first | exact @GlobalTheory.ShFam.Hor.LogCh.IsLatFam.pullback_analytic | exact GlobalTheory.ShFam.Hor.LogCh.IsLatFam.pullback_analytic | (intros; apply GlobalTheory.ShFam.Hor.LogCh.IsLatFam.pullback_analytic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EtaleCompletionCompIso
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.Member

theorem isEtaleCompletion_comp_bijective' {B A R : Type} [CommRing B] [IsLocalRing B] [CommRing A] [IsLocalRing A]
    [CommRing R] [IsLocalRing R] (e : B →+* A) (he : Function.Bijective e) (φ : A →+* R)
    (h : IsEtaleCompletion φ) : IsEtaleCompletion (φ.comp e) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨RingHom.Flat.comp (RingHom.Flat.of_bijective he) h1, ?_, ?_⟩
  · rw [← Ideal.map_map, IsLocalRing.map_maximalIdeal_of_surjective e he.2]
    exact h2
  · rw [← RingHom.comp_assoc]
    exact RingHom.Finite.comp h3 (RingHom.Finite.of_surjective e he.2)

theorem isEtaleCompletion_stalkClosedPointTo_comp_iso : ∀ {R : Type} [CommRing R] [IsLocalRing R] {X Y : Scheme.{0}} (ξ : Spec (CommRingCat.of R) ⟶ X) (g : X ⟶ Y) [IsIso g], IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → IsEtaleCompletion (Scheme.stalkClosedPointTo (ξ ≫ g)).hom := by
  intro R _ _ X Y ξ g _ h
  have hb : Function.Bijective (g.stalkMap (ξ (IsLocalRing.closedPoint (CommRingCat.of R)))).hom :=
    ConcreteCategory.bijective_of_isIso _
  rw [Scheme.stalkClosedPointTo_comp]
  exact isEtaleCompletion_comp_bijective' _ hb _ h

end GlobalTheory.Member
end
