module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SplitsAt
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj

section GtIso

variable {S : Scheme.{0}} {E : SplitExt S} {G₁ G₂ : Over S} [GrpObj G₁] [GrpObj G₂]

instance isMonHom_inv_of_iso (e : G₁ ≅ G₂) [IsMonHom e.hom] : IsMonHom e.inv where
  one_hom := by rw [← cancel_mono e.hom]; simp
  mul_hom := by
    rw [← cancel_mono e.hom]
    simp only [Category.assoc, IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc, Iso.inv_hom_id]

end GtIso

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArcSt
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi

def PullCubCompSt : Prop :=
  ∀ (S S' S'' : Scheme.{0}) (G : Over S) (G' : Over S') (G'' : Over S'') [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] [GrpObj G''] [IsCommMonObj G''] (m : CubeMap G' G) (m' : CubeMap G'' G') (n : CubeMap G'' G)
    (L : RigLB G) (L' : RigLB G') (L'' : RigLB G'') (c : CubicalStr G L) (c' : CubicalStr G' L')
    (c'' : CubicalStr G'' L''), n.F = m'.F ≫ m.F → n.F3 = m'.F3 ≫ m.F3 → n.e = m'.e ≫ m.e →
    m.IsPullCubical c' c → m'.IsPullCubical c'' c' → n.IsPullCubical c'' c

def PullCubCancelSt : Prop :=
  ∀ (S S' S'' : Scheme.{0}) (G : Over S) (G' : Over S') (G'' : Over S'') [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] [GrpObj G''] [IsCommMonObj G''] (m : CubeMap G' G) (m' : CubeMap G'' G') (n : CubeMap G'' G)
    (L : RigLB G) (L' : RigLB G') (L'' : RigLB G'') (c : CubicalStr G L) (c' : CubicalStr G' L')
    (c'' : CubicalStr G'' L''), n.F = m'.F ≫ m.F → n.F3 = m'.F3 ≫ m.F3 → n.e = m'.e ≫ m.e →
    m.IsPullCubical c' c → n.IsPullCubical c'' c → m'.IsPullCubical c'' c'

def SABCompSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' S'' : Scheme.{0}) (t : SAB H S)
    (t' : SAB H S') (t'' : SAB H S'') (f : S' ⟶ S) (g : S'' ⟶ S') (m : SABMap t' t f) (m' : SABMap t'' t' g),
    ∃ n : SABMap t'' t (g ≫ f), n.φ = m'.φ ≫ m.φ

def SABCancelSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' S'' : Scheme.{0}) (t : SAB H S)
    (t' : SAB H S') (t'' : SAB H S'') (f : S' ⟶ S) (g : S'' ⟶ S') (m : SABMap t' t f) (n : SABMap t'' t (g ≫ f)),
    ∃ m' : SABMap t'' t' g, n.φ = m'.φ ≫ m.φ

def AbLocusOneSt : Prop :=
  ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], IsSemiAbelian G → ∀ (K : Type) [Field K] (t : Sp K ⟶ S),
    IsProper (pullback.snd G.hom t) → Set.range t ⊆ abLocus G

def ProjProperSt : Prop :=
  ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R), IsProjOver f → IsProper f

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.GlobalFunctionsDvrPowers
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

open scoped CategoryTheory.Obj

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor.GlobalFunctionsDvrPowers

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

def pullPowIso {S S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S) :
    ∀ n : ℕ, (Over.pullback f).obj (powObj G n) ≅ powObj ((Over.pullback f).obj G) n
  | 0 => (Functor.Monoidal.εIso (Over.pullback f)).symm
  | n + 1 => (Functor.Monoidal.μIso (Over.pullback f) G (powObj G n)).symm ≪≫
      whiskerLeftIso ((Over.pullback f).obj G) (pullPowIso f G n)

theorem bijective_of_iso {S' : Scheme.{0}} {A B : Over S'} (e : A ≅ B)
    (h : Function.Bijective B.hom.appTop.hom) : Function.Bijective A.hom.appTop.hom := by
  have hw : A.hom = e.hom.left ≫ B.hom := (Over.w e.hom).symm
  rw [hw, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp]
  refine Function.Bijective.comp ?_ h
  refine Function.bijective_iff_has_inverse.2 ⟨(e.inv.left.appTop).hom, fun x => ?_, fun x => ?_⟩
  · show (e.hom.left.appTop ≫ e.inv.left.appTop).hom x = x
    rw [← Scheme.Hom.comp_appTop, ← Over.comp_left, e.inv_hom_id]
    simp
  · show (e.inv.left.appTop ≫ e.hom.left.appTop).hom x = x
    rw [← Scheme.Hom.comp_appTop, ← Over.comp_left, e.hom_inv_id]
    simp

theorem pull_powObj_globalFns (hGF : ReciprocityTheory.ChartRestriction.G.Out.GlobalFnsSt) {S S' : Scheme.{0}} (f : S' ⟶ S)
    (G : Over S) [GrpObj G] (hG : ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian G)
    [IsProper ((Over.pullback f).obj G).hom] (n : ℕ) :
    Function.Bijective ((Over.pullback f).obj (powObj G n)).hom.appTop.hom := by
  exact bijective_of_iso (pullPowIso f G n)
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms.globalFns_powObj hGF ((Over.pullback f).obj G)
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsSemiAbelian.pullback (f := f) (G := G) hG) n)

end ReciprocityTheory.ChartRestriction.G.Geo.Tor.GlobalFunctionsDvrPowers
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.GlobalFunctionsDvrGeneric
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor.GlobalFunctionsDvrGeneric

open ReciprocityTheory.ChartRestriction.G.Out

theorem powObj_props {S : Scheme.{0}} (G : Over S) [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom] :
    ∀ n : ℕ, Smooth (powObj G n).hom ∧ IsSeparated (powObj G n).hom ∧ QuasiCompact (powObj G n).hom := by
  intro n
  induction n with
  | zero =>
    change Smooth (𝟙 S) ∧ IsSeparated (𝟙 S) ∧ QuasiCompact (𝟙 S)
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  | succ n ih =>
    obtain ⟨hsmooth, hsep, hqc⟩ := ih
    change Smooth (G ⊗ powObj G n).hom ∧ IsSeparated (G ⊗ powObj G n).hom ∧
      QuasiCompact (G ⊗ powObj G n).hom
    rw [Over.tensorObj_hom, pullback.condition]
    exact ⟨inferInstance, inferInstance, inferInstance⟩

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

theorem appTop_spMap (v : V) :
    (spMap (algebraMap V (FractionRing V))).appTop ((Scheme.ΓSpecIso (CommRingCat.of V)).inv v) =
      (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).inv (algebraMap V (FractionRing V) v) := by
  have h := AlgebraicGeometry.Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap V (FractionRing V)))
  have h2 := congrArg (fun g => g.hom v) h
  first
  | exact h2.symm
  | simp
  | simpa using h2.symm

theorem bij_of_generic (A : Over (Sp V)) [GrpObj A] [Flat A.hom] [QuasiCompact A.hom] [QuasiSeparated A.hom]
    (hK : Function.Bijective ((Over.pullback (spMap (algebraMap V (FractionRing V)))).obj A).hom.appTop.hom) :
    Function.Bijective A.hom.appTop.hom := by
  classical
  have hψ : Function.Injective (pullback.fst A.hom (spMap (algebraMap V (FractionRing V)))).appTop :=
    GlobalFunctionsDvrOpen.appTop_fst_injective A.hom
  have hκ : Function.Bijective (pullback.snd A.hom (spMap (algebraMap V (FractionRing V)))).appTop := hK
  have he : (η[A]).left ≫ A.hom = 𝟙 _ := Over.w (η[A])
  have h1 : A.hom.appTop ≫ (η[A]).left.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, he, Scheme.Hom.id_appTop]
    rfl
  have hret : ∀ y, (η[A]).left.appTop (A.hom.appTop y) = y := fun y => by
    have := congrArg (fun φ => φ y) h1
    simpa only [CategoryTheory.comp_apply, CategoryTheory.id_apply] using this
  have hcomm : ∀ y, (pullback.fst A.hom (spMap (algebraMap V (FractionRing V)))).appTop (A.hom.appTop y) =
      (pullback.snd A.hom (spMap (algebraMap V (FractionRing V)))).appTop
        ((spMap (algebraMap V (FractionRing V))).appTop y) := fun y => by
    have h := congrArg Scheme.Hom.appTop (pullback.condition (f := A.hom) (g := spMap (algebraMap V (FractionRing V))))
    rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at h
    have := congrArg (fun φ => φ y) h
    simpa only [CategoryTheory.comp_apply] using this
  have hinj : Function.Injective A.hom.appTop := fun a b hab => by
    rw [← hret a, ← hret b, hab]
  refine ⟨hinj, fun a => ?_⟩
  obtain ⟨c, hc⟩ := hκ.2 ((pullback.fst A.hom (spMap (algebraMap V (FractionRing V)))).appTop a)
  set c' : FractionRing V := (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).hom c with hc'
  have hcc : c = (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).inv c' := by rw [hc', Iso.hom_inv_id_apply]
  by_cases h : ∃ v : V, algebraMap V (FractionRing V) v = c'
  · obtain ⟨v, hv⟩ := h
    refine ⟨(Scheme.ΓSpecIso (CommRingCat.of V)).inv v, hψ ?_⟩
    rw [hcomm, appTop_spMap, hv, ← hcc, hc]
  · exfalso
    have hc0 : c' ≠ 0 := fun h0 => h ⟨0, by rw [map_zero, h0]⟩
    obtain ⟨v, hv⟩ : ∃ v : V, algebraMap V (FractionRing V) v = c'⁻¹ := by
      rcases ValuationRing.isInteger_or_isInteger V c' with h' | h'
      · exact absurd h' h
      · exact h'
    have hvu : ¬ IsUnit v := by
      rintro ⟨u, rfl⟩
      apply h
      refine ⟨↑u⁻¹, ?_⟩
      rw [← inv_inv c', ← hv]
      refine (eq_inv_of_mul_eq_one_left ?_)
      rw [← map_mul, Units.inv_mul, map_one]
    have hone : a * A.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of V)).inv v) = 1 := by
      apply hψ
      rw [map_mul, map_one, hcomm, appTop_spMap, hv, ← hc, hcc, ← map_mul, ← map_mul, mul_inv_cancel₀ hc0, map_one,
        map_one]
    have hu : IsUnit (A.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of V)).inv v)) := ⟨⟨_, a, (mul_comm _ _).trans hone, hone⟩, rfl⟩
    have hu2 : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of V)).inv v) := by
      have := hu.map ((η[A]).left.appTop.hom)
      rwa [show (η[A]).left.appTop.hom (A.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of V)).inv v)) = (Scheme.ΓSpecIso (CommRingCat.of V)).inv v from hret _] at this
    apply hvu
    have := hu2.map (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom
    rwa [show (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv v) = v from
      Iso.inv_hom_id_apply (Scheme.ΓSpecIso (CommRingCat.of V)) v] at this

end ReciprocityTheory.ChartRestriction.G.Geo.Tor.GlobalFunctionsDvrGeneric
end
end
