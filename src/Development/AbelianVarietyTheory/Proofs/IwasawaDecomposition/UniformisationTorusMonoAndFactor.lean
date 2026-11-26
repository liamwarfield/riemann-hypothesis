module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
public import Formalism.LocalToGlobal.KernelLattices.TopPin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianChartComplexRationalIntegralForms
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesFourth
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsThetaChrTied
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFormSignIndependent
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFormScalarExtension
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFormHeckeEigen
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaDataLevelForms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignThird
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGridCharactersArchExponentsGapGtRank
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralShiftExists

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformisationTorusMonoAndFactor
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformisationTorusMonoAndFactor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TorusPart

theorem mono_gtTorus_and_factor {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {A : Type}
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A] {ρ : R →+* A} {D : Out.DegPre R} {e : ℕ}
    {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {G₀ : Over (Sp A)} [GrpObj G₀]
    {φ : G₀.left ⟶ G.left} (g : Out.GtCoord I D e G) (hρ : ∀ x ∈ I ^ (e + 1), ρ x = 0)
    (h : IsGrpPullback G₀ G (spMap ρ) φ) :
    Mono (gtTorus g hρ h) ∧ ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
      (i : splitTorus (Sp A) X ⟶ G₀), IsMonHom i →
        ∃ r : D.X →+ X, i = GlobalTheory.SplitTorus.torusMap _ r ≫ gtTorus g hρ h := by
  have := g.i_hom; have := g.q_hom; have := D.P.isAb.proper
  have : IsProper (Out.thickObj R I e D.P.A).hom := inferInstanceAs (IsProper (pullback.snd _ _))
  obtain ⟨q', hq', hk'⟩ := exists_isKernel_pullTorus (isGrpPullback_thickLift hρ h) g.i g.q g.isKernel
  have hk : IsPullback (gtTorus g hρ h) (toUnit _) q' η[_] := hk'
  have : IsProper ((Over.pullback (thickPt e hρ)).obj (Out.thickObj R I e D.P.A)).hom :=
    inferInstanceAs (IsProper (pullback.snd _ _))
  haveI : ConnectedSpace (Sp A) := GlobalTheory.SplitTorus.connectedSpace_of_isLocalRing A
  have hm : Mono (gtTorus g hρ h) := ⟨fun a b k => hk.hom_ext k (toUnit_unique _ _)⟩
  refine ⟨hm, fun X _ _ _ i hi => ?_⟩
  haveI := hi; haveI := hq'
  have ht : i ≫ q' = toUnit _ ≫ η[_] :=
    splitTorus_hom_proper_trivial_local A X _ (i ≫ q') inferInstance
  let u := hk.lift i (toUnit _) ht
  have hu : u ≫ gtTorus g hρ h = i := hk.lift_fst _ _ _
  have : IsMonHom u := Serre.isMonHom_of_mul_comp u fun T x y => by
    rw [← cancel_mono (gtTorus g hρ h), MonObj.mul_comp (x ≫ u), Category.assoc, Category.assoc,
      Category.assoc, hu, MonObj.mul_comp]
  obtain ⟨r, hr⟩ := GlobalTheory.SplitTorus.exists_eq_torusMap u
  exact ⟨r, by rw [← hr, hu]⟩

theorem mono_gtTorus_unif_and_factor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (t : SAB H (Sp R)) (P : PELUnif I t)
    (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (a : R →+* A) (e : ℕ) (ha : ∀ x ∈ I ^ (e + 1), a x = 0)
    (G₀ : Over (Sp A)) [GrpObj G₀] (φ : G₀.left ⟶ t.G.left) (h : IsGrpPullback G₀ t.G (spMap a) φ),
    Mono (GlobalTheory.TorusPart.gtTorus (P.U.gt e) ha h) ∧
    ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (i : splitTorus (Sp A) X ⟶ G₀), IsMonHom i →
      ∃ ρ : P.D.toPre.X →+ X, i = GlobalTheory.SplitTorus.torusMap _ ρ ≫ GlobalTheory.TorusPart.gtTorus (P.U.gt e) ha h := by
  intro E _ _ _ H R _ _ I t P A _ _ _ a e ha G₀ _ φ h
  exact mono_gtTorus_and_factor (P.U.gt e) ha h

end GlobalTheory.TorusPart
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformisationTorusMonoAndFactorStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisationTorus_mono_and_factor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (t : SAB H (Sp R)) (P : PELUnif I t)
    (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (a : R →+* A) (e : ℕ) (ha : ∀ x ∈ I ^ (e + 1), a x = 0)
    (G₀ : Over (Sp A)) [GrpObj G₀] (φ : G₀.left ⟶ t.G.left) (h : IsGrpPullback G₀ t.G (spMap a) φ),
    Mono (GlobalTheory.TorusPart.gtTorus (P.U.gt e) ha h) ∧
    ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (i : splitTorus (Sp A) X ⟶ G₀), IsMonHom i →
      ∃ ρ : P.D.toPre.X →+ X, i = GlobalTheory.SplitTorus.torusMap _ ρ ≫ GlobalTheory.TorusPart.gtTorus (P.U.gt e) ha h := by
  first | exact @GlobalTheory.TorusPart.mono_gtTorus_unif_and_factor | exact GlobalTheory.TorusPart.mono_gtTorus_unif_and_factor | (intros; apply GlobalTheory.TorusPart.mono_gtTorus_unif_and_factor <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothCommGroupSchemeEqOfPowEqOfClosedPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothCommGroupSchemeEqOfPowEqOfClosedPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.LocalRigid

theorem eq_of_diagonal_of_closedPoint {A : Type} [CommRing A] [IsLocalRing A] {X Y : Scheme.{0}} (f : X ⟶ Y)
    [IsOpenImmersion (pullback.diagonal f)] (a b : Sp A ⟶ X) (h : a ≫ f = b ≫ f)
    (κ : Type) [Field κ] (c : A →+* κ) [IsLocalHom c] (hc : spMap c ≫ a = spMap c ≫ b) : a = b := by
  let l : Sp A ⟶ pullback f f := pullback.lift a b h
  have hq : (spMap c ≫ a) ≫ pullback.diagonal f = spMap c ≫ l := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.diagonal_fst, Category.comp_id, Category.assoc, pullback.lift_fst]
    · rw [Category.assoc, pullback.diagonal_snd, Category.comp_id, Category.assoc, pullback.lift_snd, hc]
  let q : Sp κ ⟶ pullback (pullback.diagonal f) l := pullback.lift _ _ hq
  have hmem : (IsLocalRing.closedPoint A : Sp A) ∈ Set.range (pullback.snd (pullback.diagonal f) l) := by
    let pt : Sp κ := IsLocalRing.closedPoint κ
    refine ⟨q pt, ?_⟩
    have e : (q ≫ pullback.snd _ _) pt = spMap c pt := by rw [pullback.lift_snd]
    rw [Scheme.Hom.comp_apply] at e
    rw [e]
    exact IsLocalRing.comap_closedPoint c
  have hs : Function.Surjective (pullback.snd (pullback.diagonal f) l) := fun p =>
    (IsLocalRing.specializes_closedPoint (R := A) p).mem_open
      (pullback.snd (pullback.diagonal f) l).isOpenEmbedding.isOpen_range hmem
  have : Epi (pullback.snd (pullback.diagonal f) l).base := (TopCat.epi_iff_surjective _).2 hs
  have : IsIso (pullback.snd (pullback.diagonal f) l) := IsOpenImmersion.isIso _
  have hl : l = inv (pullback.snd (pullback.diagonal f) l) ≫ pullback.fst _ _ ≫ pullback.diagonal f := by
    rw [pullback.condition, IsIso.inv_hom_id_assoc]
  have ha : a = l ≫ pullback.fst f f := (pullback.lift_fst _ _ _).symm
  have hb : b = l ≫ pullback.snd f f := (pullback.lift_snd _ _ _).symm
  rw [ha, hb, hl]
  simp

end GlobalTheory.LocalRigid

namespace GlobalTheory.LocalRigid

theorem eq_of_pow_eq_of_closedPoint : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G], Smooth G.hom →
    ∀ (A : Type) [CommRing A] [IsLocalRing A] (s : Sp A ⟶ S) (k : ℕ), IsUnit (k : A) →
    ∀ (x y : Over.mk s ⟶ G), x ^ k = y ^ k →
    ∀ (κ : Type) [Field κ] (c : A →+* κ), IsLocalHom c → spMap c ≫ x.left = spMap c ≫ y.left → x = y := by
  intro S G _ _ hG A _ _ s k hk x y hxy κ _ c hc hxc
  haveI := hc
  let GA := (Over.pullback s).obj G
  haveI : Smooth GA.hom := inferInstanceAs (Smooth (pullback.snd G.hom s))
  have hu : IsUnit (k : Γ(Sp A, ⊤)) := by
    simpa using hk.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  haveI het : Etale (mulN GA k).left := GrpTangent.etale_mulN GA hu
  let e := TorsionLift.ptsEquiv s G (Over.mk (𝟙 (Sp A))) s (Category.id_comp s)
  have h1 : e.symm x ≫ mulN GA k = e.symm y ≫ mulN GA k := by
    rw [GrpTangent.comp_mulN, GrpTangent.comp_mulN, ← map_pow, ← map_pow, hxy]
  have h2 : (e.symm x).left ≫ (mulN GA k).left = (e.symm y).left ≫ (mulN GA k).left := by
    simpa using congrArg CommaMorphism.left h1
  have hfst : ∀ z, (e z).left = z.left ≫ pullback.fst G.hom s := fun z =>
    TorsionLift.ptsEquiv_left s G _ s (Category.id_comp s) z
  have h3 : spMap c ≫ (e.symm x).left = spMap c ≫ (e.symm y).left := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, ← hfst, ← hfst]
      simpa using hxc
    · have wx := Over.w (e.symm x)
      have wy := Over.w (e.symm y)
      rw [Category.assoc, Category.assoc]
      exact (congrArg (spMap c ≫ ·) wx).trans (congrArg (spMap c ≫ ·) wy).symm
  have h4 := eq_of_diagonal_of_closedPoint _ _ _ h2 κ c h3
  have h5 : e.symm x = e.symm y := Over.OverMorphism.ext h4
  simpa using congrArg e h5

end GlobalTheory.LocalRigid
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothCommGroupSchemeEqOfPowEqOfClosedPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothCommGroupScheme_eq_of_pow_eq_of_closedPoint : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G], Smooth G.hom →
    ∀ (A : Type) [CommRing A] [IsLocalRing A] (s : Sp A ⟶ S) (k : ℕ), IsUnit (k : A) →
    ∀ (x y : Over.mk s ⟶ G), x ^ k = y ^ k →
    ∀ (κ : Type) [Field κ] (c : A →+* κ), IsLocalHom c → spMap c ≫ x.left = spMap c ≫ y.left → x = y := by
  first | exact @GlobalTheory.LocalRigid.eq_of_pow_eq_of_closedPoint | exact GlobalTheory.LocalRigid.eq_of_pow_eq_of_closedPoint | (intros; apply GlobalTheory.LocalRigid.eq_of_pow_eq_of_closedPoint <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsChartsReadingStepZero
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsChartsReadingStepZero
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC.Chart0

open GlobalTheory.Mem.Col2.MemChart

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

abbrev lvG (a : I.ι) := levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) 0

abbrev lvQ (a : I.ι) := levQAt I.sel (I.tup a) (I.idx a) (I.Tp a) 0

def yT (u : B.Word) (a : I.ι) (c : (I.stp u a 0).Cl) : GA B (B.R.N 0) :=
  Classical.epsilon fun g : GA B (B.R.N 0) => PtOf (g * kStd X u (B.R.N 0)) (extTo I.SQ ((I.stp u a 0).rep c).1.1)

theorem yT_spec (hI : I.Ok) (u : B.Word) (a : I.ι) (c : (I.stp u a 0).Cl) :
    PtOf (yT I u a c * kStd X u (B.R.N 0)) (extTo I.SQ ((I.stp u a 0).rep c).1.1) := by
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_adelicPoint_decoratedLattice_allTwists I hI u _ (extTo I.SQ ((I.stp u a 0).rep c).1.1)
  exact Classical.epsilon_spec (p := fun g : GA B (B.R.N 0) => PtOf (g * kStd X u (B.R.N 0)) (extTo I.SQ ((I.stp u a 0).rep c).1.1))
    ⟨g * (kStd X u (B.R.N 0))⁻¹, by rwa [inv_mul_cancel_right]⟩

theorem cos0 {u : B.Word} {a : I.ι} (q q' : PtAt B.R I.sel (I.tup a) (I.cst a) u 0) : cosetIn q = cosetIn q' := by
  have key : ∀ q : PtAt B.R I.sel (I.tup a) (I.cst a) u 0, cosetIn q = fun _ => ∅ := fun q => by
    have h1 : q.1.2 = ∅ := by
      have := q.2
      rwa [ysAt_ys_of_ne _ _ _ (by have := B.R.two_le_m; omega)] at this
    funext P
    unfold cosetIn
    rw [h1]
    simp
  rw [key, key]

theorem stepZero_classes_bijective_decoratedLattice (hI : I.Ok) (u : B.Word) (a : I.ι) :
    Function.Bijective fun c : (I.stp u a 0).Cl =>
      decoCls (B.R.N 0) ((B.primes X).vT u) (B.primes X).vGs (colLev I.Ch 0).grp ((I.stp u a 0).rep c).1.1.deco := by
  letI := StepZero.idxUnique (hI.idx_ok a)
  have h := StepZero.clMap_bijective (Λ₀ := colLev I.Ch 0) ((I.Tp a).pref u 0) (fun _ => ⟨fun _ => 0, fun _ _ _ => le_rfl⟩)
    (StepZero.ysAt_zero I.sel (I.tup a) (I.cst a) (R := B.R)) (StepZero.levGAt_zero (I.Tp a) (hI.idx_ok a)) (StepZero.levQAt_zero (I.Tp a) (hI.idx_ok a))
  convert h using 1
  funext c
  have e := StepZero.clMap_cl (y := ysAt B.R I.sel (I.tup a) (I.cst a) 0) (Θ := lvQ I a) (Λ₀ := colLev I.Ch 0) ((I.Tp a).pref u 0) (fun _ => ⟨fun _ => 0, fun _ _ _ => le_rfl⟩)
    (StepZero.levGAt_zero (I.Tp a) (hI.idx_ok a)) c.1 ((I.stp u a 0).rep c)
  have e2 : (I.stp u a 0).cl c.1 ((I.stp u a 0).rep c) = c := by
    obtain ⟨b, q⟩ := c
    exact congrArg (Sigma.mk b) ((I.stp u a 0).rp_spec b q)
  rw [e2] at e
  exact e.symm

theorem stab_range0 (hI : I.Ok) (u : B.Word) (a : I.ι) (c : (I.stp u a 0).Cl) (γ : GL (Fin (B.R.N 0)) B.host.E) :
    γ ∈ (stM (lvG I a) (lvQ I a) ((I.Tp a).pref u 0) (I.pref u a 0) c).range ↔
      ∃ g : UF B.fields.E (B.R.N 0) × (colLev I.Ch 0).grp, ufGL B.fields.E (B.R.N 0) g.1 = γ ∧
        g • ((I.stp u a 0).rep c).1.1.deco = ((I.stp u a 0).rep c).1.1.deco := by
  have hL := hI.idx_ok a
  have hy := StepZero.ysAt_zero I.sel (I.tup a) (I.cst a) (R := B.R)
  constructor
  · rintro ⟨⟨g, hg⟩, rfl⟩
    refine ⟨StepZero.down (y := ysAt B.R I.sel (I.tup a) (I.cst a) 0) (Θ := lvQ I a) ((I.Tp a).pref u 0) (StepZero.levGAt_zero (I.Tp a) hL) c.1 g, rfl, ?_⟩
    exact (StepZero.deco_smul (y := ysAt B.R I.sel (I.tup a) (I.cst a) 0) (Θ := lvQ I a) _ (StepZero.levGAt_zero (I.Tp a) hL) c.1 g _).symm.trans (congrArg (fun q => q.1.1.deco) hg)
  · rintro ⟨g₀, rfl, hg⟩
    obtain ⟨g, h1, h2⟩ := StepZero.exists_lift ((I.Tp a).pref u 0) hy (StepZero.levGAt_zero (I.Tp a) hL)
      (StepZero.levQAt_zero (I.Tp a) hL) c.1 _ _ g₀ hg
    exact ⟨⟨g, h2⟩, congrArg (fun g => ufGL B.fields.E (B.R.N 0) g.1) h1⟩

theorem red0 (hI : I.Ok) (hPr : (B.primes X).Ok) (u : B.Word) (a : I.ι) (c : (I.stp u a 0).Cl) (x : GA B (B.R.N 0))
    (κ : (I.stp u a 0).G c.1) (h1 : (I.stp u a 0).gam c.1 κ = 1)
    (h2 : PtOf (yT I u a c * x * kStd X u (B.R.N 0)) ((I.stp u a 0).act c.1 κ ((I.stp u a 0).rep c)).1.1) :
    ∃ hJ : x ∈ J0 B.sp.cm (B.R.N 0) ((B.primes X).vT u), redG B.sp.cm (B.R.N 0) ((B.primes X).vT u) (B.primes X).vGs ⟨x, hJ⟩ = κ.2.1.1⁻¹ := by
  have hg := dia_of_pt hPr u (yT_spec I hI u a c)
  have hx := dia_of_pt hPr u h2
  have e1 : κ.1 = 1 := ufGL_inj B.sp.cm (B.R.N 0) (h1.trans (map_one _).symm)
  exact red_of_act B.sp.cm (B.R.N 0) (diaT (Pr := B.primes X) u) hg.1 hx.1 κ.2.1.1 (by
    rw [hg.2, hx.2]
    show ((κ.1, κ.2.1.1) : UF B.fields.E (B.R.N 0) × GLG (E := B.fields.E) (n := B.R.N 0) (SG := (B.primes X).vGs)) • _ = _
    rw [e1]
    rfl)

theorem lev0 (hI : I.Ok) (hPr : (B.primes X).Ok) (u : B.Word) (a : I.ι) (c : (I.stp u a 0).Cl) (x : GA B (B.R.N 0))
    (q : ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u 0) (h : PtOf (yT I u a c * x * kStd X u (B.R.N 0)) q) :
    x ∈ levU (F := B.host.F) B.sp.cm (B.R.N 0) ((B.primes X).vT u) (B.primes X).vGs (colLev I.Ch 0).grp ↔
      ∃ κ : (I.stp u a 0).G c.1, (I.stp u a 0).gam c.1 κ = 1 ∧ ((I.stp u a 0).act c.1 κ ((I.stp u a 0).rep c)).1.1 = q ∧
        cosetIn ((I.stp u a 0).act c.1 κ ((I.stp u a 0).rep c)) = cosetIn ((I.stp u a 0).rep c) := by
  have hL := hI.idx_ok a
  have hy := StepZero.ysAt_zero I.sel (I.tup a) (I.cst a) (R := B.R)
  have hΛ := StepZero.levGAt_zero (I.Tp a) hL
  have hΘ := StepZero.levQAt_zero (I.Tp a) hL
  have hg := dia_of_pt hPr u (yT_spec I hI u a c)
  have hx := dia_of_pt hPr u h
  constructor
  · intro hxU
    have h1 := act_of_mem B.sp.cm (B.R.N 0) _ (diaT (Pr := B.primes X) u) hg.1 ⟨x, hxU⟩
    rw [hg.2, hx.2] at h1
    obtain ⟨p, hp⟩ := exists_ptAt (R := B.R) I.sel (I.tup a) (I.cst a) q
    obtain ⟨g, h2, h3⟩ := StepZero.exists_lift ((I.Tp a).pref u 0) hy hΛ hΘ c.1 ((I.stp u a 0).rep c) p
      (1, (Formalism.L2.Col.levRed B.sp.cm (B.R.N 0) _ _ _ ⟨x, hxU⟩)⁻¹) (by rw [hp]; exact h1.symm)
    refine ⟨g, ?_, ?_, cos0 I _ _⟩
    · show ufGL B.fields.E (B.R.N 0) g.1 = 1
      rw [show g.1 = 1 from congrArg Prod.fst h2, map_one]
    · exact (congrArg (fun p : PtAt B.R I.sel (I.tup a) (I.cst a) u 0 => p.1.1) h3).trans hp
  · rintro ⟨κ, h1, h2, -⟩
    obtain ⟨hJ, hr⟩ := red0 I hI hPr u a c x κ h1 (h2 ▸ h)
    refine (mem_levU _ _ _ _ _).2 ⟨hJ, ?_⟩
    have key : ∀ (Λ' : LevFam B.fields.E B.fields.K (B.R.N 0) (B.primes X).vGs), Λ' = colLev I.Ch 0 → ∀ g : Λ'.grp,
        g.1 ∈ (colLev I.Ch 0).grp := by
      rintro _ rfl g
      exact g.2
    have hm : κ.2.1.1 ∈ (colLev I.Ch 0).grp := key _ (hΛ c.1) κ.2.1
    rw [hr]
    exact inv_mem hm

theorem chr0 (hI : I.Ok) (hPr : (B.primes X).Ok) (u : B.Word) (a : I.ι) (c : (I.stp u a 0).Cl) (x : GA B (B.R.N 0))
    (hxU : x ∈ levU (F := B.host.F) B.sp.cm (B.R.N 0) ((B.primes X).vT u) (B.primes X).vGs (colLev I.Ch 0).grp)
    (κ : (I.stp u a 0).G c.1) (h1 : (I.stp u a 0).gam c.1 κ = 1)
    (h2 : PtOf (yT I u a c * x * kStd X u (B.R.N 0)) ((I.stp u a 0).act c.1 κ ((I.stp u a 0).rep c)).1.1) :
    ((levTyp (F := B.host.F) (hc := B.sp.cm) ((Units.map B.embLL.toMonoidHom).comp (colLev I.Ch 0).chr) ⟨x, hxU⟩ : ℂˣ) : ℂ) =
      B.embLL (((I.stp u a 0).chr c.1 κ : B.LLˣ) : B.LL) := by
  have hL := hI.idx_ok a
  have hΛ := StepZero.levGAt_zero (I.Tp a) hL
  have hΘ := StepZero.levQAt_zero (I.Tp a) hL
  have hg := dia_of_pt hPr u (yT_spec I hI u a c)
  have hx := dia_of_pt hPr u h2
  have e1 : κ.1 = 1 := ufGL_inj B.sp.cm (B.R.N 0) (h1.trans (map_one _).symm)
  obtain ⟨hJ, hr⟩ := red_of_act B.sp.cm (B.R.N 0) (diaT (Pr := B.primes X) u) hg.1 hx.1 κ.2.1.1 (by
    rw [hg.2, hx.2]
    show ((κ.1, κ.2.1.1) : UF B.fields.E (B.R.N 0) × GLG (E := B.fields.E) (n := B.R.N 0) (SG := (B.primes X).vGs)) • _ = _
    rw [e1]
    rfl)
  have e2 : Formalism.L2.Col.levRed B.sp.cm (B.R.N 0) _ _ _ ⟨x, hxU⟩ = (⟨κ.2.1.1, hΛ c.1 ▸ κ.2.1.2⟩ : (colLev I.Ch 0).grp)⁻¹ :=
    Subtype.ext hr
  show ((Units.map B.embLL.toMonoidHom ((colLev I.Ch 0).chr (Formalism.L2.Col.levRed B.sp.cm (B.R.N 0) _ _ _ ⟨x, hxU⟩)))⁻¹ : ℂˣ).1 =
    B.embLL (((lvG I a c.1).chr κ.2.1 * (lvQ I a c.1).chr κ.2.2 : B.LLˣ) : B.LL)
  rw [e2, StepZero.chr_eq_one (hΘ c.1), mul_one, StepZero.chr_congr (hΛ c.1), map_inv, map_inv, inv_inv]
  rfl


set_option maxHeartbeats 1000000 in
theorem charts_zero : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι), ∃ (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : Type) (chOf : (I.stp u a 0).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad 0 (Nat.zero_le _) (fun c : {c // chOf c = β} => (I.chain l u a).stab 0 c.1) (fun c => latCrd (I.rec7 l Z) 0 (Nat.zero_le _) (I.latAt u a 0 c.1))), I.ReadsK l Z u a 0 (Nat.zero_le _) chOf K := by
  intro B X I hI hP l Z u a
  have hPr := l.pr
  have hX := GlobalTheory.Mem.FieldsLaws.fields_ok B
  have hi : 0 ≤ B.R.m := Nat.zero_le _
  obtain ⟨hg, -, hl⟩ := (GlobalTheory.T.trueColumn_spaces_standard_in_frameCoords I hI hP l Z).2.2.2 0 hi
  have hf : B.fields.f = B.R.f := (hPr.vT_card u).symm.trans (l.lev u I.mu0).card_ST
  have hL := hI.idx_ok a
  let chOf : (I.stp u a 0).Cl → Unit := fun _ => ()
  obtain ⟨lev, Y, SI, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := chart_exists (F := B.host.F) (E := B.host.E) B.sp.cm (B.R.N 0)
    (fun w => (colLev I.Ch 0 w).H) (f := B.R.f)
    (basePi_of_ok hX hPr u) (hPr.piT_norm u) (rls_vT_iff hX hPr u)
    (fun P hP => by simpa only [Ideal.absNorm_eq_natCard] using hPr.vT_norm u P hP) (rls_T_notUnder hPr u)
    (hf ▸ colBase_index (X := B.fields) B.sp.cm (B.R.N 0) hPr u) ((Units.map B.embLL.toMonoidHom).comp (colLev I.Ch 0).chr)
    (gramN (I.rec7 l Z) 0 hi) hg (badG (I.rec7 l Z)) (Set.ext fun v => (plUnder_vGs (X := B.fields) B.sp.cm hPr v).symm)
    (fun c : {c // chOf c = ()} => (I.stp u a 0).Stab c.1) (fun c => latCrd (I.rec7 l Z) 0 hi (I.latAt u a 0 c.1))
    (diaT (Pr := B.primes X) u) (fun c => ((I.stp u a 0).rep c.1).1.1.deco) (fun c => yT I u a c.1)
    (fun c => (dia_of_pt hPr u (yT_spec I hI u a c.1)).1) (fun c => (dia_of_pt hPr u (yT_spec I hI u a c.1)).2)
    ((stepZero_classes_bijective_decoratedLattice I hI u a).comp (Equiv.subtypeUnivEquiv fun _ => rfl).bijective) (fun c => (hl u a).1 c.1)
    (fun c => stM (lvG I a) (lvQ I a) _ _ c.1) (fun c => stM_inj (lvG I a) (lvQ I a) _ _ ((l.ch u a).step 0) c.1)
    (fun c γ => stab_range0 I hI u a c.1 γ)
  obtain ⟨k1, k2, k3⟩ := kStd_spec hPr u (B.R.N 0)
  letI := StepZero.idxUnique hL
  obtain ⟨q₀, -⟩ := exists_ptAt (R := B.R) I.sel (I.tup a) (I.cst a) (u := u) (j := 0) (DecoF.base _ _ _ _ _)
  refine ⟨badG (I.rec7 l Z), Unit, chOf, fun _ => ⟨lev, Y, h1, h2, SI, h3, h4⟩, fun _ => kStd X u (B.R.N 0),
    ⟨fun c c' => ⟨fun _ => ⟨Subsingleton.elim _ _, cos0 I _ _⟩, fun _ => rfl⟩,
      fun _ => ⟨(I.stp u a 0).cl default q₀, rfl⟩, fun β x => ?_, fun _ => k1, fun _ v hv _ _ => k2 v hv, fun _ => k3,
      fun c => ?_, fun c x q h => ?_, fun c x κ hκ h => ?_, fun c s => h9 _ _⟩⟩
  · exact (h5 ▸ Iff.rfl : x ∈ lev.Lb ↔ x ∈ baseLb B.fields.E (B.R.N 0) ((B.primes X).vT u)).trans (mem_baseLb hPr u _ x)
  · have e := h8 ⟨c, rfl⟩
    show PtOf ((Y ⟨c, rfl⟩).1 * kStd X u (B.R.N 0)) _
    rw [e]
    exact yT_spec I hI u a c
  · have e := h8 ⟨c, rfl⟩
    replace h : PtOf (yT I u a c * x * kStd X u (B.R.N 0)) q := e ▸ h
    exact (h6 ▸ Iff.rfl : x ∈ lev.U ↔ x ∈ levU (F := B.host.F) B.sp.cm (B.R.N 0) ((B.primes X).vT u) (B.primes X).vGs
      (colLev I.Ch 0).grp).trans (lev0 I hI hPr u a c x q h)
  · have e := h8 ⟨c, rfl⟩
    have hx : (id x.1 : GA B (B.R.N 0)) ∈ levU (F := B.host.F) B.sp.cm (B.R.N 0) ((B.primes X).vT u) (B.primes X).vGs
      (colLev I.Ch 0).grp := h6 ▸ x.2
    refine (congrArg Units.val (h7 x hx)).trans ?_
    exact chr0 I hI hPr u a c x.1 hx κ hκ (e ▸ h)

end GlobalTheory.Mem.Col2.TC.Chart0
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsChartsReadingStepZeroStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_charts_reading_step_zero : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι), ∃ (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : Type) (chOf : (I.stp u a 0).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad 0 (Nat.zero_le _) (fun c : {c // chOf c = β} => (I.chain l u a).stab 0 c.1) (fun c => latCrd (I.rec7 l Z) 0 (Nat.zero_le _) (I.latAt u a 0 c.1))), I.ReadsK l Z u a 0 (Nat.zero_le _) chOf K := by
  first | exact @GlobalTheory.Mem.Col2.TC.Chart0.charts_zero | exact GlobalTheory.Mem.Col2.TC.Chart0.charts_zero | (intros; apply GlobalTheory.Mem.Col2.TC.Chart0.charts_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsThetaFunOOfIsVacO
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.WeilParts

namespace GlobalTheory.OneMapRef

theorem mem_HHa_span {T : Type} (r : T → ℕ) (n : ℕ) (k : Type) [Field k] (cc : T → T) (isX : T → Prop) (a : T → ℕ → ℕ)
    {P : MvPolynomial (Letter T r n) k} (h : P ∈ Submodule.span k (HHa r n k cc isX a)) : P ∈ HHa r n k cc isX a := by
  classical
  induction h using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact ⟨zero_mem _, fun _ _ _ _ _ => map_zero _, fun m hm => by simp at hm⟩
  | add x y _ _ hx hy =>
    refine ⟨add_mem hx.1 hy.1, fun σ i i' hi t => by rw [map_add (f := _), hx.2.1 σ i i' hi t, hy.2.1 σ i i' hi t], fun m hm => ?_⟩
    rcases Finset.mem_union.1 (MvPolynomial.support_add hm) with h | h
    · exact hx.2.2 m h
    · exact hy.2.2 m h
  | smul c x _ hx =>
    exact ⟨Submodule.smul_mem _ c hx.1, fun σ i i' hi t => by rw [map_smul, hx.2.1 σ i i' hi t],
      fun m hm => hx.2.2 m (MvPolynomial.support_smul hm)⟩

section Marks

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {r : ℕ} {L : Lt E r} {mk : Dw.La →ₗ[𝓞 E] (Fin r → E)}

theorem isMark_sign (h : IsMark l L mk) (ε : ℤˣ) : IsMark l L ((ε : ℤ) • mk) := by
  rcases Int.units_eq_one_or ε with rfl | rfl
  · simpa using h
  · have e : ∀ a, (((-1 : ℤˣ) : ℤ) • mk) a = -mk a := fun a => by simp
    refine ⟨fun a => by rw [e]; exact neg_mem (h.mem a), fun a ha ⟨u, hu, hu'⟩ => h.inj a ha ⟨-u, neg_mem hu, ?_⟩,
      fun v hv => ?_⟩
    · rw [smul_neg, ← hu', e, neg_neg]
    · obtain ⟨a, ha, u, hu, hu'⟩ := h.surj v hv
      exact ⟨-a, neg_mem ha, u, hu, by rw [e, map_neg, neg_neg, hu']⟩


open CategoryTheory MonObj in
theorem marked_of_congr {Xo : Moduli Dw l} {c : Coeff l} [Algebra c.F ℂ] {g : ℕ} {X : Data E r}
    {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {idx : Fin g ≃ X.Ψ × Fin r} {e : Fin g ≃ Lt1 Dw} {x : Frame X.Ψ r}
    {y : FrPt Xo c ℂ} (A : AnFib X bas idx e x L y) {mk' : Dw.La →ₗ[𝓞 E] (Fin r → E)}
    (h : A.Marked mk) (hc : ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), ∃ u ∈ L, mk a = mk' a + l.M • u) :
    A.Marked mk' := by
  intro a ha
  obtain ⟨u, hu, e'⟩ := hc a ha
  have hM : (l.M : E) ≠ 0 := by have := l.three_le; exact_mod_cast (by omega : l.M ≠ 0)
  have hadd : ∀ u v, pv X idx x (u + v) = pv X idx x u + pv X idx x v := fun u v => by
    unfold pv; rw [per_add]; rfl
  rw [h a ha, e', smul_add, ← Nat.cast_smul_eq_nsmul E, inv_smul_smul₀ hM, hadd, A.ex_add,
    (A.ex_ker _).2 ⟨u, hu, rfl⟩, _root_.mul_one]

end Marks

theorem kernel_value {D : D7} {S T : HSp D} {r g : ℕ} {hr : T.rank = r} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
    {X : Data D.host.E r} {eT : D.what₂.Tau ≃ X.Ψ} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {idx : Fin g ≃ X.Ψ × Fin r}
    (hS : IsSet ψ θ S T hr X eT bas) {χS χT : (AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (hom : IsWeilDatumO ψ S T χS χT om) {q : ℕ} (hp : X.p0 = q) {Z : Fam T} (hZ : IsONeg T q Z) {h : GA D S} (hh : h ∈ GfC S)
    {γ : GA D T} (hγ : γ ∈ GQ T) (k : GA D T) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (Q : MvPolynomial (FVar D T.rank S.rank) ℂ) {φ : TF S.rank g} (hφ : GlobalTheory.SW.IsSB φ)
    (hz : Zak ψ θ hr eT bas idx (frOf hr eT (mvZ θ (γ * k) Z)) φ (om (h, γ * k) f)) {q0 : ℕ} (hq : X.p0 + q0 = r) :
    thetaKO om h k (fv ψ θ S T q Z f Q) = thP X hq bas idx φ (toP S hr eT hq Q) (frOf hr eT (mvZ θ (γ * k) Z)) := by
  subst hp
  obtain ⟨hZ', hc, -⟩ := (GlobalTheory.T.orthonormalNegFirstFamily_frame_cartan_move D S T r g hr ψ θ X eT bas idx hS Z hZ).2.2.2.2 (γ * k)
  have h1 := GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ S hh
  obtain ⟨h2, h3⟩ := GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ S T χS χT om hom hS.2.1 (fun _ => 1) (fun _ => 1) (fun _ => 1)
    (fun _ => 1) (cartZ T X.p0 Z) (cartZ T X.p0 (mvZ θ (γ * k) Z)) Z (mvZ θ (γ * k) Z) h (γ * k)
    (fun τ => by rw [h1]) hc (fun τ => by rw [h1, Matrix.mul_one]) (fun _ => rfl) f hf Q
  have h4 := (((GlobalTheory.T.adelicTheta_of_testFunction_exists_laws_fockVectors D S T r g hr ψ θ X eT bas idx hS _ hZ').1 φ hφ).2 _ hz).2.2.2.2.2.2 q0 hq Q
  rw [← h4]
  have h5 := hom.om_aut 1 (one_mem _) γ hγ _ (hom.om_pres (h, k) _ h2)
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, _root_.one_mul, h3] at h5
  exact h5.symm

theorem isThetaFunO_of_isVacO {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {sS : Fam S} {sT : Fam T}
    {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)} {f : WO S T → ℂ}
    (h : IsVacO ψ θ S T sS sT LS LT f) : IsThetaFunO ψ S T f := h.2.2

theorem thR_smul_of_prod {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} {X : Data E r}
    {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {idx : Fin g ≃ X.Ψ × Fin r} {x : Frame X.Ψ r} {v : TF n g}
    {th : (Fin g → ℂ) → ℂ} {κ : ℂ} (h : ∀ z : Fin n → Fin g → ℂ, ∏ b, th (z b) = κ * thA X bas idx v x z) (a : ℂ)
    (w : Ker.WR X n) :
    a * (Ker.gaussR X bas idx x (Ker.zR X idx x w) * ∏ b, th (Ker.zR X idx x w b)) = Ker.thR X bas idx ((a * κ) • v) x w := by
  rw [h]
  simp only [Ker.thR, thA, SW.thS, Pi.smul_apply, smul_eq_mul, _root_.mul_assoc, tsum_mul_left]
  ring

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {F : Face D A}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
  {i : Fin D.R.m}

def TermAt (O : OMDat T.toCore R i Unit (fun _ => A.μ0)) (ε : ℤˣ) : Prop :=
  ∀ (t : Unit) (h : O.Cl' t → GA D (Vc D i)) (J' : Subgroup (Bridge.Gf (Vc D i))), RepsR R i A.μ0 h (O.bad t) J' (O.Lh t) (O.gam t) (O.vol t) → ∀ (k : O.Cl' t) (g' : GA D (Wc D i)) (X : Data D.host.E D.R.r) (eT : D.what₂.Tau ≃ X.Ψ) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin D.R.r), IsSet R.ψ R.θ (Vc D i) (Wc D i) (rank_Wc i) X eT bas → X.p0 = (T.Q.Dw ((i : ℕ) + 1)).q → ∀ L : Lt D.host.E D.R.r, SelfD X L → latW (rank_Wc i) L = latG (Wc D i) g' → ∀ v : TF (Vc D i).rank g, IsVac X bas (T.Q.H.w0 : D.host.E) (tens (stdL D.host.E (Vc D i).rank) L) v → ∀ a : ℂ, Zak R.ψ R.θ (rank_Wc i) eT bas idx (frOf (rank_Wc i) eT (mvZ R.θ g' (baseZ R i))) (a • v) (R.ωP i A.μ0 (1, g') (R.vacP i)) → ∀ mk₂ : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E), (∀ b, mk₂ b ∈ L) → MarkAd (rank_Wc i) (O.dδ t).l₂ (iotaW T i) g' mk₂ → ∀ Y : (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (O.dδ t).l₂) → Matrix (Fin (Vc D i).rank) (Fin D.R.r) D.host.E, IsRoots (O.dδ t).l₂ L ((ε : ℤ) • mk₂) (O.Nc t k) Y → GlobalTheory.SW.IsSB (gphi X bas (T.Q.H.w0 : D.host.E) (O.La t k).La L v (fun q => inC O.c' (O.w t k q)) Y) ∧ Zak R.ψ R.θ (rank_Wc i) eT bas idx (frOf (rank_Wc i) eT (mvZ R.θ g' (baseZ R i))) ((a * inC O.c' (O.ep t k * ((((O.La t k).mIdx (O.Nc t k) D.R.r : O.c'.F))⁻¹ * ((Nat.card (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (O.dδ t).l₂) : O.c'.F))⁻¹ * ((O.La t k).zCard (O.Nc t k) D.R.r : O.c'.F)))) • gphi X bas (T.Q.H.w0 : D.host.E) (O.La t k).La L v (fun q => inC O.c' (O.w t k q)) Y) (R.ωP i A.μ0 (h k, g') (R.vP i A.μ0))

def IoAt (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (O : OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : ℂ)
    (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) : Prop :=
  ∀ x : VsV D i O.c'.F, ∃ Q : PolF D (Wc D i).rank (Vc D i).rank, (∀ f, IsThetaFunO R.ψ (Vc D i) (Wc D i) f → pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A))) f (R.ioP i (PiTensorProduct.tprod ℂ u) (O.c0' x)) = fv R.ψ R.θ (Vc D i) (Wc D i) (T.Q.Dw ((i : ℕ) + 1)).q (baseZ R i) f Q) ∧ ∀ (X : Data D.host.E D.R.r) (eT : D.what₂.Tau ≃ X.Ψ) (g : ℕ) (Dc : Dic (T.Q.Dw ((i : ℕ) + 1)) O.c' (inC O.c') X g (T.Q.Dw ((i : ℕ) + 1)).p (Vc D i).rank (wtA (κ i))), (∀ ρ, (eT ρ).1 = tauE D ρ) → MvPolynomial.C ph * toP (Vc D i) (rank_Wc i) eT Dc.hr Q = MvPolynomial.C ((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℝ) : ℂ) * MvPolynomial.rename Dc.eL (MvPolynomial.map (inC O.c') (O.io x))

def CovAt (O : OMDat T.toCore R i Unit (fun _ => A.μ0)) (c0 : ℂ) : Prop :=
  ∀ (ε : ℤˣ) (t : Unit) (g' : GA D (Wc D i)) (X : Data D.host.E D.R.r) (eT : D.what₂.Tau ≃ X.Ψ) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin D.R.r) (e : Fin g ≃ Lt1 (T.Q.Dw ((i : ℕ) + 1))), IsSet R.ψ R.θ (Vc D i) (Wc D i) (rank_Wc i) X eT bas → X.p0 = (T.Q.Dw ((i : ℕ) + 1)).q → Matched T.Q.c O.s0 X idx e → ∀ L : Lt D.host.E D.R.r, SelfD X L → latW (rank_Wc i) L = latG (Wc D i) g' → ∀ mk₂ : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E), (∀ b, mk₂ b ∈ L) → MarkAd (rank_Wc i) (O.dδ t).l₂ (iotaW T i) g' mk₂ → letI : Algebra (O.dδ t).c₂.F ℂ := ((inC O.c').comp ((O.dδ t).eF.symm : (O.dδ t).c₂.F →+* O.c'.F)).toAlgebra; ∀ (y₂ : FrPt (O.dδ t).Xo₂ (O.dδ t).c₂ ℂ) (A₂ : AnFib X bas idx e (frOf (rank_Wc i) eT (mvZ R.θ g' (baseZ R i))) L y₂), A₂.Marked ((ε : ℤ) • mk₂) → evR (O.dδ t).Xo₂ (O.dδ t).c₂ (O.dδ t).cδ y₂ = c0 * ((O.xi t (Matrix.GeneralLinearGroup.det (finHom (Wc D i) g')) : ℂˣ) : ℂ)

theorem io_mem (O : OMDat T.toCore R i Unit (fun _ => A.μ0))
    (hP : O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0)) (x : VsV D i O.c'.F) :
    O.io x ∈ HHa (T.Q.Dw ((i : ℕ) + 1)).mult (Vc D i).rank O.c'.F ComplexEmbedding.conjugate (InPsi T.Q.H)
      (fun τ j => wtA (κ i) (τ, j)) :=
  hP.io.2.elim fun _ h => mem_HHa_span _ _ _ _ _ _ (h.2.2.1 ▸ LinearMap.mem_range_self _ _)

end GlobalTheory.OneMapRef

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointDeterminantEqNormOneClassOfLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointDeterminantEqNormOneClassOfLevel
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.FullDt ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.FullDt

theorem adAt_eq_one_of_prV {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (P : HeightOneSpectrum (𝓞 E)) {z : AfE F E}
    (hz : Formalism.UG.prV (E := E) (P.under (𝓞 F)) z = 1) : adAt F P z = 1 := by
  set v := P.under (𝓞 F)
  have h1 : Formalism.UG.P.afsplitEps E v * z = Formalism.UG.P.afsplitEps E v := by
    rw [← Formalism.UG.P.afsplit_decomp, hz]
    rfl
  have h2 : Formalism.UG.P.afsplitEps E v = (1 : E) ⊗ₜ[F] Formalism.UG.P.afsplitI v (1 : v.adicCompletion F) := by
    rw [Formalism.UG.P.afsplitEps, Algebra.TensorProduct.one_def, Formalism.UG.P.afsplitIE_tmul]
  have h3 : adAt F P (Formalism.UG.P.afsplitEps E v) = 1 := by
    rw [h2, adAt_apply, GlobalTheory.Mem.ReadTwist.afIso_one_tmul (k := 1)]
    · simp
    · rw [Formalism.UG.P.afsplitI_self]; simp
  have h4 := congrArg (adAt F P) h1
  rwa [map_mul, h3, one_mul] at h4

theorem detPt_eq_u1Dt_of_level : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (n : ℕ) (ST SG Q SQ : Finset (HeightOneSpectrum (𝓞 H.E))) (p : DecoF H.E n ST SG Q) (y k : GL (Fin n) (AfE H.F H.E)) (x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H)), LevOk H SG SQ → IsPtOf (host_cmData R H) (y * k) (extTo SQ p) → k ∈ Formalism.L2.Herm.UstdAf (host_cmData R H) n → Formalism.L2.Herm.Carries k (stdLat H.E n) (stdLat H.E n) → (∀ P ∈ uSG SG SQ, Formalism.UG.bc (Formalism.UG.prV (E := H.E) (P.under (𝓞 H.F))) k = 1) → Matrix.GeneralLinearGroup.det x.1 = Matrix.GeneralLinearGroup.det y → detPt H SQ p = u1Dt H SQ x := by
  intro R H n ST SG Q SQ p y k x hl hp hk hc hbc hx
  obtain ⟨a, ha⟩ := exists_lift H x
  obtain ⟨b, hb⟩ := DetLift.exists_isDetLift R H n k hk
  have hab : IsDetLift (host_cmData R H) (y * k) (a * b) := by
    unfold IsDetLift at ha hb ⊢
    rw [map_mul, map_mul, ha, hb, hx, map_mul]
  have hK : b ∈ KDq H SQ := by
    refine mem_KDq_of_conj hl b (fun w => ?_) fun P hP => ?_
    · rw [DetSpec.val_compAt_eq hb ⟨stdLat_lattice, stdLat_unimodular⟩ hc (fr := fun _ => LinearEquiv.refl _ _)
        (fun _ _ => Iff.rfl) w]
      simp
    · have hdet : adAt H.F P (k : Matrix (Fin n) (Fin n) (AfE H.F H.E)).det = 1 := by
        refine adAt_eq_one_of_prV P ?_
        have h := congrArg (fun g => Matrix.det (Units.val g)) (hbc P hP)
        simp only [Formalism.UG.bc, Units.coe_map, Units.val_one, Matrix.det_one] at h
        rw [RingHom.map_det]
        exact h
      have hs0 : adAt H.F P (Formalism.UG.sigR (host_cmData R H).sig _ (finAf H.F H.E b : AfE H.F H.E)) ≠ 0 :=
        (((Units.isUnit (finAf H.F H.E b)).map (Formalism.UG.sigR (host_cmData R H).sig _)).map (adAt H.F P)).ne_zero
      rw [DetSpec.compAt_eq hb P, hdet, one_mul, div_self hs0, sub_self, map_zero]
      exact zero_lt_one
  rw [normOneFiniteAdeleDetClass_of_isDetLift H SQ x a ha, ← DetSpec.mk_eq_detPt R H n ST SG Q SQ p (y * k) (a * b) hl hp hab,
    QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff b).2 hK, mul_one]

end GlobalTheory.Mem.Col2.FullDt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointDeterminantEqNormOneClassOfLevelStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.FullDt ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pointDeterminant_eq_normOneClass_of_level : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (n : ℕ) (ST SG Q SQ : Finset (HeightOneSpectrum (𝓞 H.E))) (p : DecoF H.E n ST SG Q) (y k : GL (Fin n) (AfE H.F H.E)) (x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H)), LevOk H SG SQ → IsPtOf (host_cmData R H) (y * k) (extTo SQ p) → k ∈ Formalism.L2.Herm.UstdAf (host_cmData R H) n → Formalism.L2.Herm.Carries k (stdLat H.E n) (stdLat H.E n) → (∀ P ∈ uSG SG SQ, Formalism.UG.bc (Formalism.UG.prV (E := H.E) (P.under (𝓞 H.F))) k = 1) → Matrix.GeneralLinearGroup.det x.1 = Matrix.GeneralLinearGroup.det y → detPt H SQ p = u1Dt H SQ x := by
  first | exact @GlobalTheory.Mem.Col2.FullDt.detPt_eq_u1Dt_of_level | exact GlobalTheory.Mem.Col2.FullDt.detPt_eq_u1Dt_of_level | (intros; apply GlobalTheory.Mem.Col2.FullDt.detPt_eq_u1Dt_of_level <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetIdStdBot
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : Later B (I.cols l))

structure StdKerTie {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : G.Inst (I.rec7 l Z) L} {Gl : G.LatInst (I.rec7 l Z)}
    {K : G.Consts} {Y : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX} (t : KerEntTied ex) : Prop where
  X_eq : t.X = B.fields
  seam : HEq t.seam (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G)
  Pr : HEq t.Pr (B.primes X)
  Ch : HEq t.Ch I.Ch
  sel : HEq t.sel I.sel
  S : t.S = I.S
  word : HEq t.word fun u : B.Word => u
  tup : HEq t.tup I.tup
  cst : HEq t.cst I.cst
  idx : HEq t.idx I.idx
  m2 : t.m2 = B.R.m - 2
  glob : HEq t.glob I.glob
  amb : HEq t.amb (I.J.amb B t.χ)
  δ : t.δ = I.J.δ
  O : I.StdO l Z Y.Qp t.O

namespace StdKerEmpty

end StdKerEmpty

end GlobalTheory.Mem.Col2.TC

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemberLevelPrimeNotMemUnderLevelPrimes
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemberLevelPrimeNotMemUnderLevelPrimes
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.FullDt ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.LevTwist

theorem T_notMem_under_uSG : ∀ (B : Base) (X : PreX B.toPre) (I : ColIn B X), I.Ok → ∀ (u : B.Word)
    (P : HeightOneSpectrum (𝓞 B.host.E)), P ∈ uSG (B.primes X).vGs I.SQ →
    (B.T u : 𝓞 B.host.F) ∉ (P.under (𝓞 B.host.F)).asIdeal := by
  classical
  intro B X I hI u P hP hm
  have hPr := (GlobalTheory.BasePrimes.primes_ok B X).1
  have hE : (((B.primes X).T u : ℕ) : 𝓞 B.fields.E) ∈ P.asIdeal := by
    have h1 : ((B.T u : ℕ) : 𝓞 B.host.F) ∈ P.asIdeal.under (𝓞 B.host.F) := hm
    rw [Ideal.under_def, Ideal.mem_comap, map_natCast] at h1
    exact h1
  rcases Finset.mem_union.1 hP with h | h
  · exact T_notMem_vGs hPr u ⟨P, h⟩ hE
  · have hg := (good_of_mem hI h).2
    have e := (ReadTwist.plc_under_eq_iff (F := B.host.F) P (hPr.T_prime u)).2 hE
    refine hg.2.2 ?_
    rw [e]
    exact hI.T_mem u

end GlobalTheory.Mem.LevTwist
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemberLevelPrimeNotMemUnderLevelPrimesStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.FullDt ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.memberLevelPrime_not_mem_under_levelPrimes : ∀ (B : Base) (X : PreX B.toPre) (I : ColIn B X), I.Ok → ∀ (u : B.Word) (P : HeightOneSpectrum (𝓞 B.host.E)), P ∈ uSG (B.primes X).vGs I.SQ → (B.T u : 𝓞 B.host.F) ∉ (P.under (𝓞 B.host.F)).asIdeal := by
  first | exact @GlobalTheory.Mem.LevTwist.T_notMem_under_uSG | exact GlobalTheory.Mem.LevTwist.T_notMem_under_uSG | (intros; apply GlobalTheory.Mem.LevTwist.T_notMem_under_uSG <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelMapExtension
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PtId

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {F : Face D A}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
  {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}

def cmpConst (D : D7) (ka : ℂ) (δ : ℤˣ) (d : ℕ) : ℂ :=
  ka * (((δ : ℤ) : ℂ) ^ d * (-1) ^ d * ((Real.sqrt (2 * Real.pi * xiR D) : ℝ) : ℂ)⁻¹ ^ d)



theorem cmpConst_ne_zero {ka : ℂ} (hka : ka ≠ 0) (δ : ℤˣ) (d : ℕ) : cmpConst D ka δ d ≠ 0 := by
  have h1 : 0 < xiR D := norm_pos_iff.2 ((_root_.map_ne_zero _).2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D))
  have h2 : ((Real.sqrt (2 * Real.pi * xiR D) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (by positivity)).ne'
  have h3 : ((δ : ℤ) : ℂ) ≠ 0 := Int.cast_ne_zero.2 δ.ne_zero
  exact mul_ne_zero hka (mul_ne_zero (mul_ne_zero (pow_ne_zero _ h3) (pow_ne_zero _ (by norm_num))) (pow_ne_zero _ (inv_ne_zero h2)))


omit [Algebra T.Q.c.F D.what₂.LL] in
theorem ccIs_transport {θ : InfFam D} {V W : HSp D} {hr : W.rank = D.R.r} {j : ℕ} {σ σ' : T.Q.c.F →+* ℂ} (e : σ = σ')
    (hV : T.V j σ = W) (hV' : T.V j σ' = W) {om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {f₀ : WO V W → ℂ}
    {cst : (T.U j σ).Comp → ℂ}
    (h : CcIs θ V W hr (T.U j σ) (castDict hV (T.dict j σ)) (castDict hV (T.mu j σ)) (T.x₀ j σ) om f₀ cst) :
    ∃ cst' : (T.U j σ').Comp → ℂ,
      CcIs θ V W hr (T.U j σ') (castDict hV' (T.dict j σ')) (castDict hV' (T.mu j σ')) (T.x₀ j σ') om f₀ cst' ∧
      ∀ g, cst' (castDict hV' (T.dict j σ') g).1 = cst (castDict hV (T.dict j σ) g).1 := by
  subst e
  exact ⟨cst, h, fun _ => rfl⟩


end GlobalTheory.PtId
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtendSplitTorusHomOverDvr
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtendSplitTorusHomOverDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.TorusPart

theorem extend_torus_hom_dvr : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G],
    IsSemiAbelian G → ∀ (G₁ : Over (Sp (FractionRing V))) [GrpObj G₁] (φ₁ : G₁.left ⟶ G.left),
    IsGrpPullback G₁ G (spMap (algebraMap V (FractionRing V))) φ₁ → Nonempty (TorusExtension G₁) →
    ∀ (Ω : Type) [Field Ω] (α : FractionRing V →+* Ω) (G' : Over (Sp Ω)) [GrpObj G'] (φ : G'.left ⟶ G.left)
      (h : IsGrpPullback G' G (spMap (α.comp (algebraMap V (FractionRing V)))) φ)
      (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (i : splitTorus (Sp Ω) X ⟶ G'), IsMonHom i →
      ∃ j : splitTorus (Sp V) X ⟶ G, IsMonHom j ∧ GlobalTheory.TorusPart.pullTorus h j = i := by
  intro V _ _ _ G _ _ hG G₁ _ φ₁ h₁ hT Ω _ α G' _ φ h X _ _ _ i hi
  obtain ⟨T⟩ := hT
  letI := T.addCommGroup; letI := T.grpB
  haveI := T.free; haveI := T.finite
  have := T.i_hom; have := T.q_hom; have := T.isAbelian.proper
  set a := algebraMap V (FractionRing V)
  have ef : spMap (α.comp a) = spMap α ≫ spMap a := by
    rw [← Spec.map_comp]; rfl

  let ψ : G'.left ⟶ G₁.left := h₁.1.lift φ (G'.hom ≫ spMap α) (by
    rw [Category.assoc, ← ef]; exact h.1.w)
  have hψ : ψ ≫ φ₁ = φ := h₁.1.lift_fst _ _ _
  have h₂ : IsGrpPullback G' G₁ (spMap α) ψ :=
    h₁.cancel (h.congr ef hψ.symm) (h₁.1.lift_snd _ _ _)

  obtain ⟨q', hq', hk⟩ := exists_isKernel_pullTorus h₂ T.i T.q T.isKernel
  have : IsProper ((Over.pullback (spMap α)).obj T.B).hom :=
    inferInstanceAs (IsProper (pullback.snd _ _))
  have hiq : i ≫ q' = toUnit _ ≫ η[(Over.pullback (spMap α)).obj T.B] :=
    splitTorus_hom_proper_trivial_local Ω X _ (i ≫ q') inferInstance
  have : Mono (pullTorus h₂ T.i) := ⟨fun x y e => hk.hom_ext e (toUnit_unique _ _)⟩
  let u' := hk.lift i (toUnit _) hiq
  have hu' : u' ≫ pullTorus h₂ T.i = i := hk.lift_fst _ _ _
  have : IsMonHom u' := Serre.isMonHom_of_mul_comp u' fun S x y => by
    rw [← cancel_mono (pullTorus h₂ T.i), MonObj.mul_comp (x ≫ u'), Category.assoc, Category.assoc,
      Category.assoc, hu', MonObj.mul_comp]
  haveI : ConnectedSpace (Sp Ω) := SplitTorus.connectedSpace_of_isLocalRing Ω
  obtain ⟨u, hu⟩ := SplitTorus.exists_eq_torusMap u'

  obtain ⟨e, he, heφ⟩ := grpPullback_iso h₁ (isGrpPullback_pullback G (spMap a))
  let j₁ : splitTorus (Sp (FractionRing V)) X ⟶ G₁ := SplitTorus.torusMap _ u ≫ T.i
  have : IsMonHom j₁ := inferInstance
  let f := (SplitTorus.bcIso (spMap a) X).inv ≫ j₁ ≫ e.hom
  have : IsMonHom f := inferInstance
  obtain ⟨F, ⟨hF, hF'⟩, -⟩ := homExtension_semiAbelian_dvr V (FractionRing V) (splitTorus (Sp V) X) G
    inferInstance hG f inferInstance
  refine ⟨F, hF, ?_⟩
  have hj₁ : pullTorus h₁ F = j₁ := by
    rw [eq_comm, eq_pullTorus_iff]
    have k : f.left ≫ pullback.fst G.hom (spMap a) =
        pullback.fst (splitTorus (Sp V) X).hom (spMap a) ≫ F.left := by
      rw [← hF']; exact pullback.lift_fst _ _ _
    have k2 := congrArg ((SplitTorus.bcIso (spMap a) X).hom.left ≫ ·) k
    simp only [f, Over.comp_left, Category.assoc, heφ] at k2
    rw [← Category.assoc, ← Over.comp_left, Iso.hom_inv_id, Over.id_left, Category.id_comp,
      SplitTorus.bcIso_hom_fst_assoc] at k2
    exact k2
  rw [← pullTorus_pullTorus h₂ h₁ h ef hψ.symm, hj₁, pullTorus_torusMap_comp, ← hu, hu']

end GlobalTheory.TorusPart
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtendSplitTorusHomOverDvrStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extend_splitTorus_hom_over_dvr : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G],
    IsSemiAbelian G → ∀ (G₁ : Over (Sp (FractionRing V))) [GrpObj G₁] (φ₁ : G₁.left ⟶ G.left),
    IsGrpPullback G₁ G (spMap (algebraMap V (FractionRing V))) φ₁ → Nonempty (TorusExtension G₁) →
    ∀ (Ω : Type) [Field Ω] (α : FractionRing V →+* Ω) (G' : Over (Sp Ω)) [GrpObj G'] (φ : G'.left ⟶ G.left)
      (h : IsGrpPullback G' G (spMap (α.comp (algebraMap V (FractionRing V)))) φ)
      (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (i : splitTorus (Sp Ω) X ⟶ G'), IsMonHom i →
      ∃ j : splitTorus (Sp V) X ⟶ G, IsMonHom j ∧ GlobalTheory.TorusPart.pullTorus h j = i := by
  first | exact @GlobalTheory.TorusPart.extend_torus_hom_dvr | exact GlobalTheory.TorusPart.extend_torus_hom_dvr | (intros; apply GlobalTheory.TorusPart.extend_torus_hom_dvr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTorsionMapUniformisationGeneric
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTorsionMapUniformisationGeneric
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.GenTors

theorem exists_torsMap_generic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) [CharZero R], AdmBase R (maximalIdeal R) →
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k →
    ∃ f : QkPt P.D.toPre F k → (TF (R := R) F ⟶ t.G),
      (∀ q v, GlobalTheory.FlatTors.IsImage P F k q v ↔ v = (f q).left) ∧ (∀ q, f q ^ k = 1) ∧ (∀ x, x ^ k = 1 → ∃ q, f q = x) ∧
      (∀ p p' p'', QkAdd p p' p'' → f p'' = f p * f p') ∧
      (∀ p p' τ, p.y = 0 → GlobalTheory.UT.IsTor τ p.g →
        GlobalTheory.UU.CubWeil t.cub k (f p) (f p') (unitOn (τ (Multiplicative.ofAdd p'.y)))) ∧
      ∀ (σ : F →ₐ[FractionRing R] F) p p', QkExt σ.toRingHom p p' → (f p').left = spMap σ.toRingHom ≫ (f p).left := by
  intro E _ _ _ H R _ _ _ t P _ hR F _ _ _ k hk
  letI := H.starRing
  obtain ⟨f₀, h1, h2, -, h4, -, h6⟩ := GlobalTheory.FlatTors.torsionIso_holds E H R (maximalIdeal R) hR t P F k hk
  obtain ⟨g₁, g₂, -⟩ := GlobalTheory.Ex.GenericFibre.unif_generic P
  obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv g₁ (TFK (R := R) F) (jFK (R := R) F ≫ jK R) rfl
  have hpow : ∀ q, f₀ q ^ k = 1 := fun q => by
    obtain ⟨w, hw⟩ := P.U.toUnifPre.ext
    exact ((h1 q (f₀ q)).2 rfl w hw).1
  have hpow' : ∀ q, e (f₀ q) ^ k = 1 := fun q => by rw [← map_pow, hpow, map_one]
  refine ⟨fun q => e (f₀ q), ?_, hpow', ?_, ?_, ?_, ?_⟩
  · intro q v
    constructor
    · rintro ⟨a, ha, hq⟩
      rw [(h1 q a).1 hq] at ha
      rw [← ha, he]
    · intro hv
      exact ⟨f₀ q, by rw [hv, he], (h1 q (f₀ q)).2 rfl⟩
  · intro x hx
    obtain ⟨q, hq⟩ := h2 (e.symm x) (by rw [← map_pow, hx, map_one])
    exact ⟨q, by simp only [hq, MulEquiv.apply_symm_apply]⟩
  · intro p p' p'' h
    simp only [h4 p p' p'' h, map_mul]
  · intro p p' τ hy hτ
    have hw : WeilIs P.A.A P.A.L k (f₀ p) (f₀ p') (unitOn (τ (Multiplicative.ofAdd p'.y))) :=
      (h6 p p' _).1 (GlobalTheory.ZH.TorusPerp.weilQkIs_tor GlobalTheory.firstFiveLaws.1.globalFns p p' hy hτ)
    have hpr : IsProper (pullback.snd t.G.hom (jK R)) := by
      have := P.A.isAb.proper
      have := isIso_inv_left P.U.gen.symm
      have h : IsProper ((Over.pullback (jK R)).obj t.G).hom := by
        rw [← Over.w P.U.gen.symm.inv]; infer_instance
      exact h
    have one : ∀ c : Fˣ, GlobalTheory.UU.CubWeil t.cub k (e (f₀ p)) (e (f₀ p')) (unitOn c) →
        WeilIs P.A.A P.A.L (k : ℤ) (f₀ p) (f₀ p') (unitOn c) := fun c h =>
      (GlobalTheory.weilIs_iff_of_isGrpPullback_comm _ _ t.G P.A.A (jK R) _ t.PP.L P.A.L t.PP.isLB P.A.isLB g₁ g₂
        (TFK (R := R) F) k (f₀ p) (f₀ p') (e (f₀ p)) (e (f₀ p')) (unitOn c) (he _) (he _)).2
        (GlobalTheory.FlatTors.weilIs_of_cubWeil_of_proper (jK R) t.G t.semi hpr t.cub k (TFK (R := R) F) _ _ _ h)
    obtain ⟨ζ, hζ, -⟩ := (GlobalTheory.UU.cubWeil_basic _ t.G t.PP t.cub k _).1 (e (f₀ p)) (e (f₀ p')) (hpow' p) (hpow' p')
    obtain ⟨c, rfl⟩ : ∃ c : Fˣ, unitOn c = ζ :=
      ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom.toMonoidHom ζ,
        Units.ext ((Scheme.ΓSpecIso (CommRingCat.of F)).hom_inv_id_apply _)⟩
    have ec : c = τ (Multiplicative.ofAdd p'.y) :=
      GlobalTheory.weilIs_unique_fieldPoint _ P.A.A P.A.L P.A.isLB F _ k (f₀ p) (f₀ p') c _ (one c hζ) hw
    exact ec ▸ hζ
  · intro σ p p' hpp'
    obtain ⟨-, hx, hiff⟩ := GlobalTheory.UT.Cl.galois_holds R (maximalIdeal R) hR P.D P.A t.G t.semi P.U F F σ k hk p
    obtain ⟨x', hx'⟩ := hx (f₀ p)
    have e' : x' = f₀ p' := (h1 p' x').1 ((hiff p' (f₀ p) x' hpp' hx').1 ((h1 p (f₀ p)).2 rfl))
    subst e'
    rw [he, he, hx', Category.assoc]

end GlobalTheory.GenTors
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTorsionMapUniformisationGenericStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torsionMap_uniformisation_generic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) [CharZero R], AdmBase R (maximalIdeal R) →
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k →
    ∃ f : QkPt P.D.toPre F k → (TF (R := R) F ⟶ t.G),
      (∀ q v, GlobalTheory.FlatTors.IsImage P F k q v ↔ v = (f q).left) ∧ (∀ q, f q ^ k = 1) ∧ (∀ x, x ^ k = 1 → ∃ q, f q = x) ∧
      (∀ p p' p'', QkAdd p p' p'' → f p'' = f p * f p') ∧
      (∀ p p' τ, p.y = 0 → GlobalTheory.UT.IsTor τ p.g →
        GlobalTheory.UU.CubWeil t.cub k (f p) (f p') (unitOn (τ (Multiplicative.ofAdd p'.y)))) ∧
      ∀ (σ : F →ₐ[FractionRing R] F) p p', QkExt σ.toRingHom p p' → (f p').left = spMap σ.toRingHom ≫ (f p).left := by
  first | exact @GlobalTheory.GenTors.exists_torsMap_generic | exact GlobalTheory.GenTors.exists_torsMap_generic | (intros; apply GlobalTheory.GenTors.exists_torsMap_generic <;> assumption)
end
end
