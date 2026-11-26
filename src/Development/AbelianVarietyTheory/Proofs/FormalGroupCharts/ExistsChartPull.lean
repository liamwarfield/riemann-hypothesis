module

public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.NuAlgLeOfCharts
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FrameSymmetryIffPullback
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IsCanonGaugeMapFB

@[expose] public section

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open IsDedekindDomain

namespace GlobalTheory.DepthExt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem grp_id {S : Scheme.{0}} (G : Over S) [GrpObj G] : IsGrpPullback G G (𝟙 _) (𝟙 _) :=
  ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun _ x y x₀ y₀ hx hy =>
    (mul_left_congr (Category.comp_id _) x₀ y₀ x y (hx.trans (Category.comp_id _))
      (hy.trans (Category.comp_id _))).trans (Category.comp_id _).symm⟩

section Tangent
variable {V V' : Type} [CommRing V] [CommRing V']

theorem comb_iff (t : SAB H (Sp V)) {m : ℕ} (v : Fin m → (epsR V ⟶ t.G)) (cf : Fin m → V) (w : epsR V ⟶ t.G) :
    IsLieComb cf v w ↔ IsCombAtG t (𝟙 _) (fun i => (v i).left) cf w.left := by
  simp only [Chart.comb_push (grp_id t.G), Category.comp_id]
  exact Iff.rfl

theorem tan_iff (t : SAB H (Sp V)) (w : epsR V ⟶ t.G) : IsTangent w ↔ IsTanAtG t (𝟙 _) w.left := by
  simp only [Chart.tan_push (grp_id t.G), Category.comp_id]
  exact ⟨fun h => ⟨(Over.w w).trans (Category.comp_id _).symm, h⟩, fun h => h.2⟩

variable (ψ : V →+* V') {t : SAB H (Sp V)} {t' : SAB H (Sp V')} (mp : SABMap t' t (spMap ψ))

end Tangent

end GlobalTheory.DepthExt
