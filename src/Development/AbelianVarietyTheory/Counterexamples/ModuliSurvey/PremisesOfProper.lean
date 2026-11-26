module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModuliConsequenceOfAbelianSchemeLaws
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegrality
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliFiniteSurjectiveOverGenericFamily
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.CubeMapTripleProductUnique

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsSabMapOfGroupIso
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExtendGenAndCorrOfGenericFibre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Exist

theorem extendGen : extendGenSt.{0} :=
  (GlobalTheory.cubical_extends_and_extendGen GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected
    GlobalTheory.GenExtend.existsUnique_gen_extend).2

end GlobalTheory.Exist
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.Exist.CubicalExtension

theorem exists_sabMap_of_groupIso : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (t t' : SAB H (Sp T)) (tK : SAB H (Sp K)) (m : SABMap tK t (spMap (algebraMap T K))) (m' : SABMap tK t' (spMap (algebraMap T K))) (ψ : t.G ≅ t'.G), IsMonHom ψ.hom → m.φ ≫ ψ.hom.left = m'.φ → (∀ a, t.act.act a ≫ ψ.hom = ψ.hom ≫ t'.act.act a) → ∃ n : SABMap t t' (𝟙 _), n.φ = ψ.hom.left :=
  sabMap_of_iso_of_extendGen GlobalTheory.Exist.extendGen

end GlobalTheory.Exist.CubicalExtension
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.ModelUniqueChecks

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem existsUnique_map (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
    [IsFractionRing V K] (t t' : SAB H (Sp V)) (tK : SAB H (Sp K)) (a : SABMap tK t (spMap (algebraMap V K)))
    (a' : SABMap tK t' (spMap (algebraMap V K))) :
    ∃! ψ : SABMap t t' (𝟙 (Sp V)), a.φ ≫ ψ.φ = a'.φ := by
  obtain ⟨_, _⟩ : QuasiCompact (spMap (algebraMap V K)) ∧ IsSchemeTheoreticallyDominant (spMap (algebraMap V K)) :=
    ExtUnique.spec_fractionRing V K
  obtain ⟨_, _⟩ := ExtUnique.flat_and_isSeparated_of_isSemiAbelian t.G t.semi
  obtain ⟨_, _⟩ := ExtUnique.flat_and_isSeparated_of_isSemiAbelian t'.G t'.semi
  obtain ⟨F, hF, hφ⟩ := TripleExt.exists_hom a.cart a'.cart
    (GlobalTheory.semiAbelian_hom_extends_uniquely_dvr V K t.G t'.G t.semi t'.semi)
  obtain ⟨F', -, hφ'⟩ := TripleExt.exists_hom a'.cart a.cart
    (GlobalTheory.semiAbelian_hom_extends_uniquely_dvr V K t'.G t.G t'.semi t.semi)
  have hiso : IsIso F := ExtUnique.isIso_of_isPullback a.cart.1 a'.cart.1 (Iso.refl _) F F'
    ((Category.id_comp _).trans hφ.symm) ((Category.id_comp _).trans hφ'.symm)
  have hact : ∀ x, t.act.act x ≫ F = F ≫ t'.act.act x := fun x =>
    ExtUnique.over_hom_ext_of_isPullback a.cart.1 (by
      rw [Over.comp_left, Over.comp_left, ← Category.assoc, ← a.act, Category.assoc, hφ, ← Category.assoc, hφ,
        a'.act])
  obtain ⟨n, hn⟩ := GlobalTheory.Exist.CubicalExtension.exists_sabMap_of_groupIso E H V K t t' tK a a'
    (asIso F) hF hφ hact
  refine ⟨n, (congrArg (a.φ ≫ ·) hn).trans hφ, fun n' hn' => SemiAbelianTripleChecks.sabMap_ext _ _ ?_⟩
  have w : n'.φ ≫ t'.G.hom = t.G.hom := n'.cart.1.w.trans (Category.comp_id _)
  have : Over.homMk n'.φ w = F := ExtUnique.over_hom_ext_of_isPullback a.cart.1 (hn'.trans hφ.symm)
  rw [hn]
  exact congrArg (fun z => z.left) this

theorem extV_holds : ExtVStatement := fun _ _ _ _ _ V _ _ _ _ t t' tK _ a a' =>
  (existsUnique_map V (FractionRing V) t t' tK a a').exists

end GlobalTheory.ModelUniqueChecks
