module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDerivAt0CompLinear
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDVRReadingCentredValuation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepApplyEqSmulOfHalfIndicatorBase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemModelInteriorOfMemAbelianLocusPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisCoverQuotientFreeFiniteAction
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.PhiCOfNoIntegralForm
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CentredPointPhiPositive
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsUniformizingIntegralFrameExtension
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.UnifTrait
section Frames
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
end Frames
end GlobalTheory.UnifTrait
namespace GlobalTheory.UnifTrait
section Split
open IsLocalRing ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
end Split
end GlobalTheory.UnifTrait
namespace GlobalTheory.UnifTrait
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem exists_extension_integral_frame_uniformizer : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) (T : Formalism.L2.Pj.CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra; ∀ (P : FrPt Xo c T.Fr) (w : Sp T.V ⟶ TF.Y.X), spMap (algebraMap T.V T.Fr) ≫ w = TF.X.ptY P ≫ TF.X.π → ∃ (T' : Formalism.L2.Pj.CDVR) (i : T.Fr →+* T'.Fr) (j : T.V →+* T'.V) (r : ℕ) (y' : IntFr Xo c T' (i.comp io)) (G : SAB H (Sp T'.V)) (_ : SABMap G TF.Y.t (spMap j ≫ w)) (_ : PELUnif (IsLocalRing.maximalIdeal T'.V) G) (t' : SAB H (Sp T'.Fr)) (_ : letI := (i.comp io).toAlgebra; SABMap t' Xo.univ.t y'.1.x) (_ : SABMap t' G (spMap (algebraMap T'.V T'.Fr))), 0 < r ∧ (∀ x, Formalism.L2.Pj.vV T'.V (i x) = (r : ℤ) * Formalism.L2.Pj.vV T.V x) ∧ i.comp (algebraMap T.V T.Fr) = (algebraMap T'.V T'.Fr).comp j ∧ (∀ a ∈ IsLocalRing.maximalIdeal T.V, j a ∈ IsLocalRing.maximalIdeal T'.V) ∧ (letI := (i.comp io).toAlgebra; TF.X.ptY y'.1 = spMap i ≫ TF.X.ptY P) := by
  intro _ E _ _ _ H Dw l Xo c TF T io
  letI := io.toAlgebra
  intro P w hw
  have hz : FlagMod.frX P ≫ TF.Y.j = spMap (algebraMap T.V T.Fr) ≫ w := by
    rw [hw, (TF.X.lies_ptY P).1]
  have hzs : FlagMod.frX P ≫ pullback.snd _ _ = spMap io := FlagMod.frX_snd P
  obtain ⟨y₀, tt, hB⟩ := exists_intFr_frBor T io c.F (RingHom.id c.F) TF.Y w (FlagMod.frX P) hz hzs P
    (FlagMod.frX_fst P).symm
  obtain ⟨G₀, ⟨m₀⟩⟩ : ∃ G₀ : SAB H (Sp T.V), Nonempty (SABMap G₀ TF.Y.t w) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull w TF.Y.t
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨t₀, m1₀, m2₀, -⟩ := genFibre Xo c Out.CubePf.cubePull T io c.F (RingHom.id c.F) TF.Y w _ hz hzs G₀ m₀
  have : CharZero (ResidueField T.V) := charZero_residue_of_map T.V (w ≫ TF.Y.s)
  obtain ⟨W, _, _, _, _, _, hf, hi, hS⟩ := exists_split_baseChange T.V G₀.G G₀.semi
  have : CharZero W := charZero_of_injective_ringHom hi
  let T' : CDVR := { V := W }
  let j : T.V →+* T'.V := algebraMap T.V W
  have hfin : j.Finite := RingHom.finite_algebraMap.2 hf
  obtain ⟨i, r, hr0, hφ, hv, -⟩ := GlobalTheory.EtaVal.finite_extension_ramification_embedding T T' j hi hfin
  letI := (i.comp io).toAlgebra
  let ψ : T.Fr →ₐ[c.F] T'.Fr := { i with commutes' := fun _ => rfl }
  obtain ⟨z', hz'⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.abelianSchemeLaws_all.1.secBaseChange E H Dw l Xo c
    T.Fr T'.Fr ψ y₀.1
  let y' : IntFr Xo c T' (i.comp io) := ⟨z', GlobalTheory.NonIntegralFrameExample.spread_holds Xo c T'.Fr z',
    GlobalTheory.IntegralExt.integral_baseChange T T' io (i.comp io) j hi ψ hφ y₀.1 z' hz' y₀.2.2⟩
  obtain ⟨G, ⟨mG⟩⟩ : ∃ G : SAB H (Sp T'.V), Nonempty (SABMap G TF.Y.t (spMap j ≫ w)) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (spMap j ≫ w) TF.Y.t
    exact ⟨_, ⟨m⟩⟩
  have hι : i.comp (algebraMap T.V T.Fr) = (algebraMap T'.V T'.Fr).comp j := RingHom.ext hφ
  have hio : spMap (algebraMap T'.V T'.Fr) ≫ spMap j = spMap i ≫ spMap (algebraMap T.V T.Fr) := by
    rw [GlobalTheory.EtaVal.spMap_comp_spMap, GlobalTheory.EtaVal.spMap_comp_spMap, hι]
  have hz2 : (spMap i ≫ FlagMod.frX P) ≫ TF.Y.j = spMap (algebraMap T'.V T'.Fr) ≫ spMap j ≫ w := by
    rw [Category.assoc, hz, ← Category.assoc, ← hio, Category.assoc]
  have hzs2 : (spMap i ≫ FlagMod.frX P) ≫ pullback.snd _ _ = spMap (i.comp io) := by
    rw [Category.assoc, hzs, GlobalTheory.EtaVal.spMap_comp_spMap]
  obtain ⟨t', m1, m2, -⟩ := genFibre Xo c Out.CubePf.cubePull T' (i.comp io) c.F (RingHom.id c.F) TF.Y
    (spMap j ≫ w) _ hz2 hzs2 G mG
  have hx' : y'.1.x = (spMap i ≫ FlagMod.frX P) ≫ pullback.fst _ _ := by
    rw [Category.assoc, FlagMod.frX_fst, ← hB.1]
    exact hz'.1
  obtain ⟨Pu, -⟩ := GlobalTheory.IntegralExt.exists_unif_of_split T T' j i hφ m1₀ m2₀ (Category.assoc _ _ _) m1 m2 hS
  have hloc : IsLocalHom j := hfin.to_isIntegral.isLocalHom hi
  refine ⟨T', i, j, r, y', G, mG, Pu, t', (by rw [hx']; exact m1), m2, hr0, hv, hι, fun a ha => map_nonunit j a ha,
    ?_⟩
  rw [TF.X.ptY_frBor hB, ← TF.X.ptY_frMap hz']
end GlobalTheory.UnifTrait
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniformizing_integral_frame_extension : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) (T : Formalism.L2.Pj.CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra; ∀ (P : FrPt Xo c T.Fr) (w : Sp T.V ⟶ TF.Y.X), spMap (algebraMap T.V T.Fr) ≫ w = TF.X.ptY P ≫ TF.X.π → ∃ (T' : Formalism.L2.Pj.CDVR) (i : T.Fr →+* T'.Fr) (j : T.V →+* T'.V) (r : ℕ) (y' : IntFr Xo c T' (i.comp io)) (G : SAB H (Sp T'.V)) (_ : SABMap G TF.Y.t (spMap j ≫ w)) (_ : PELUnif (IsLocalRing.maximalIdeal T'.V) G) (t' : SAB H (Sp T'.Fr)) (_ : letI := (i.comp io).toAlgebra; SABMap t' Xo.univ.t y'.1.x) (_ : SABMap t' G (spMap (algebraMap T'.V T'.Fr))), 0 < r ∧ (∀ x, Formalism.L2.Pj.vV T'.V (i x) = (r : ℤ) * Formalism.L2.Pj.vV T.V x) ∧ i.comp (algebraMap T.V T.Fr) = (algebraMap T'.V T'.Fr).comp j ∧ (∀ a ∈ IsLocalRing.maximalIdeal T.V, j a ∈ IsLocalRing.maximalIdeal T'.V) ∧ (letI := (i.comp io).toAlgebra; TF.X.ptY y'.1 = spMap i ≫ TF.X.ptY P) := by
  first | exact @_root_.GlobalTheory.UnifTrait.exists_extension_integral_frame_uniformizer | exact _root_.GlobalTheory.UnifTrait.exists_extension_integral_frame_uniformizer | (intros; apply _root_.GlobalTheory.UnifTrait.exists_extension_integral_frame_uniformizer <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.PeriodMinimumPhiPos
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PeriodMinPos
theorem period_minimum_phi_pos : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (T : Formalism.L2.Pj.CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (φ : ℝ), GlobalTheory.SlopeRec.HasPhi y φ → ∀ (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (_ : letI := io.toAlgebra; SABMap t' Xo.univ.t y.1.x) (_ : SABMap t' G (spMap (algebraMap T.V T.Fr))), (IsLocalRing.closedPoint T.V : Sp T.V) ∉ abLocus G.G → 0 < φ := by
  intro _ E _ _ _ H Dw l Xo c T io y φ hφ G t' m1 m2 hG
  obtain ⟨G₀, t₀, m1₀, m2₀, P, ϖ, Q, β, hϖ, hQ, h0, hβ, rfl⟩ := hφ
  obtain ⟨m⟩ := GlobalTheory.SlopeRec.nonempty_sabMap_of_models m1 m2 m1₀ m2₀
  have hG₀ : (IsLocalRing.closedPoint T.V : Sp T.V) ∉ abLocus G₀.G := fun h =>
    hG ((abLocus_pullback abLocusOne G.semi m.cart.1 _).2 h)
  have hnt : ¬ Subsingleton P.D.toPre.X := fun h =>
    hG₀ ((GlobalTheory.TorRef.closed_mem_abLocus_iff T P).2 h)
  rw [not_subsingleton_iff_nontrivial] at hnt
  obtain ⟨a, ha⟩ := exists_ne (0 : P.D.toPre.X)
  have hQa : 1 ≤ Q a := ReciprocityTheory.ChartRestriction.G.DVR.QForm.Q_pos hϖ P.D hQ ha
  have hint : ∀ a c, ∃ z : ℤ, (β : P.D.toPre.X →ₗ[ℤ] P.D.toPre.X →ₗ[ℤ] ℝ) a c = z := by
    intro a c
    refine ⟨Q (a + c) - Q a - Q c, ?_⟩
    have h1 := hβ (a + c)
    have hs := β.2.1 c a
    simp only [map_add (f := _), LinearMap.add_apply] at h1
    rw [hβ a, hβ c] at h1
    push_cast
    linarith
  have hpos : ∀ a, 0 ≤ (β : P.D.toPre.X →ₗ[ℤ] P.D.toPre.X →ₗ[ℤ] ℝ) a a := fun a => by
    rw [hβ]; exact mul_nonneg zero_le_two (by exact_mod_cast h0 a)
  have hne : β ≠ 0 := fun e => by
    have h1 := hβ a
    rw [e] at h1
    have : (1 : ℝ) ≤ Q a := by exact_mod_cast hQa
    simp at h1
    linarith
  haveI : Module.Finite (𝓞 E) P.D.toPre.X := .of_restrictScalars_finite ℤ _ _
  haveI : Module.Projective (𝓞 E) P.D.toPre.X := GlobalTheory.Forms.projective_of_int (𝓞 E) P.D.toPre.X
  have h1 := GlobalTheory.LeastExponentProbe.one_le_phiC (fun _ => rfl) β hint hpos hne
  linarith
end GlobalTheory.PeriodMinPos
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.minimal_period_pos : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (T : Formalism.L2.Pj.CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (φ : ℝ), GlobalTheory.SlopeRec.HasPhi y φ → ∀ (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (_ : letI := io.toAlgebra; SABMap t' Xo.univ.t y.1.x) (_ : SABMap t' G (spMap (algebraMap T.V T.Fr))), (IsLocalRing.closedPoint T.V : Sp T.V) ∉ abLocus G.G → 0 < φ := by
  first | exact @_root_.GlobalTheory.PeriodMinPos.period_minimum_phi_pos | exact _root_.GlobalTheory.PeriodMinPos.period_minimum_phi_pos | (intros; apply _root_.GlobalTheory.PeriodMinPos.period_minimum_phi_pos <;> assumption)
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.DegVal
theorem degree_valuation_phi_pos (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) (Z : Comp Xo c)
    (y : Y₀ TF.X Z) (hy : y ∈ (U₀ TF.X Z : Set (Y₀ TF.X Z))ᶜ)
    (ν : Valuation ((Y₀ TF.X Z).presheaf.stalk y) (WithZero (Multiplicative ℤ))) (hν : Centred y ν) :
    ∃ φ : ℝ, 0 < φ ∧ PhiAt TF.X Z y ν φ := by
  obtain ⟨h1, h2, h3⟩ := hν
  haveI := GlobalTheory.T.charZero_stalk_compactFlagSpaceOverComponent TF Z y
  haveI : IsDomain ((Y₀ TF.X Z).presheaf.stalk y) := by
    refine @NoZeroDivisors.to_isDomain _ _ inferInstance ⟨fun {a b} hab => ?_⟩
    have := congrArg ν hab
    rw [map_mul, map_zero, mul_eq_zero] at this
    exact this.imp (h3 a) (h3 b)
  obtain ⟨T, g, ρ, hρ, hinj, hloc, hval⟩ := GlobalTheory.T.exists_completeDVR_reading_centredValuation _ ν h1 h2 h3
  have hz := GlobalTheory.T.traitGenericPoint_mem_compactFlagSpaceOpenPart TF Z y T.Fr ((algebraMap T.V T.Fr).comp g)
    ((IsFractionRing.injective T.V T.Fr).comp hinj)
  obtain ⟨io, hP'⟩ := GlobalTheory.T.exists_framedPoint_of_compactFlagSpaceOpenPart TF.X T.Fr _ hz
  letI := io.toAlgebra
  obtain ⟨P, hPz⟩ := hP'
  let w : Sp T.V ⟶ TF.Y.X :=
    Spec.map (CommRingCat.ofHom g) ≫ (Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z ≫ TF.X.π
  have hw : spMap (algebraMap T.V T.Fr) ≫ w = TF.X.ptY P ≫ TF.X.π := by
    rw [hPz]
    simp only [w, spMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  obtain ⟨T', i, j, r, y', G, m3, Pu, t', m1, m2, hr, hv, hij, hjloc, hpt⟩ := _root_.GlobalTheory.T.exists_uniformizing_integral_frame_extension hP TF T io P w hw
  obtain ⟨φT, hφT⟩ := GlobalTheory.SlopeRec.exists_hasPhi y' G t' m1 m2 Pu
  have hcl : ∀ {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B] (f : A →+* B),
      (∀ a ∈ IsLocalRing.maximalIdeal A, f a ∈ IsLocalRing.maximalIdeal B) →
      (Spec.map (CommRingCat.ofHom f)) (IsLocalRing.closedPoint B) = IsLocalRing.closedPoint A := by
    intro A B _ _ _ _ f hf
    have : IsLocalHom f := ⟨fun a ha => by
      by_contra h
      exact (IsLocalRing.mem_maximalIdeal _).1 (hf a ((IsLocalRing.mem_maximalIdeal _).2 h)) ha⟩
    exact IsLocalRing.comap_closedPoint f
  have hpos : 0 < φT := by
    refine _root_.GlobalTheory.T.minimal_period_pos hP T' _ y' φT hφT G t' m1 m2 fun hab => hy ?_
    have h := GlobalTheory.T.mem_modelInterior_of_mem_abelianLocus_pullback TF.Y _ _ G m3 _ hab
    have e1 : (spMap j) (IsLocalRing.closedPoint T'.V) = IsLocalRing.closedPoint T.V := hcl j hjloc
    have e2 : (Spec.map (CommRingCat.ofHom g)) (IsLocalRing.closedPoint T.V) =
        IsLocalRing.closedPoint ((Y₀ TF.X Z).presheaf.stalk y) := hcl g hloc
    change TF.X.π (inc₀ TF.X Z ((Y₀ TF.X Z).fromSpecStalk y
      ((Spec.map (CommRingCat.ofHom g)) ((spMap j) (IsLocalRing.closedPoint T'.V))))) ∈ _ at h
    rw [e1, e2, Scheme.fromSpecStalk_closedPoint] at h
    exact h
  refine ⟨(ρ / r) * φT, mul_pos (div_pos hρ (Nat.cast_pos.2 hr)) hpos, T', i.comp io, y', j.comp g, ρ / r, φT,
    div_pos hρ (Nat.cast_pos.2 hr), hφT, rfl, ?_, ?_⟩
  · letI := (i.comp io).toAlgebra
    rw [hpt, hPz, ← Category.assoc]
    congr 1
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    rw [← RingHom.comp_assoc, hij, RingHom.comp_assoc]
  · intro a ha
    rw [hval a ha]
    have e : algebraMap T'.V T'.Fr (j (g a)) = i (algebraMap T.V T.Fr (g a)) :=
      (RingHom.congr_fun hij (g a)).symm
    rw [RingHom.comp_apply, e, hv]
    have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
    push_cast
    field_simp
end GlobalTheory.DegVal
namespace GlobalTheory.DegVal
end GlobalTheory.DegVal
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.LevelSubgroupIndexBounded
section
noncomputable section
namespace GlobalTheory.CovTop.LevelIndex
open NumberField IsDedekindDomain Formalism.BasicNotions _root_.Formalism.L2.DIV
section Gen
variable {E : Type} [Field E] [NumberField E]
variable {F : Type} [Field F] [NumberField F] [StarRing E] [Algebra F E] {n : ℕ} {LL : Type} [CommRing LL]
end Gen
end GlobalTheory.CovTop.LevelIndex
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem GlobalTheory.CovTop.LevelIndex.level_index_le_bound : ∀ (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) (D : D7) (Tu : Type) (C : LevCh D Tu) (t0 : Tu) (hC : C.Is t0) (i : Fin D.R.m) (P : LevelP C.Pg D.R.r ℂ), GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.IndexBound C i P := by
  intro _ D Tu C t0 hC i P
  have hB : GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW C i (LevelP.full _ _ _) = parLev D.sp.cm (Wc D i).gram (C.βW i) (C.datWp i P) := by
    have e : C.datWp i (LevelP.full _ _ _) = { C.datWp i P with P := LevelP.full (C.datWp i P).Pg (C.datWp i P).r ℂ } := by
      simp only [LevCh.datWp, datY, if_true]
    rw [← GlobalTheory.CovTop.LevelIndex.lev_full, ← e]
  obtain ⟨h0, h1⟩ := GlobalTheory.CovTop.LevelIndex.relIndex_lev_le D.sp.cm (Wc D i).gram (C.βW i) (C.datWp i P) _ hB
  refine ⟨h0, ?_⟩
  have hfr : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    rw [D.host.finrank_cmField]
    unfold Ranks.f Ranks.n
    ring
  have hN : D.host.g 0 * D.host.g 1 ≠ 0 := mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
  have hg : ∀ PP ∈ C.Pg, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    intro PP hP
    obtain ⟨k, hk⟩ := (hC.Pg PP).1 hP
    have h0 := C.C.P.pb_over k
    rw [← hk] at h0
    have h2 : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ PP.asIdeal := h0
    rw [map_natCast] at h2
    rw [Nat.cast_mul]
    fin_cases k
    · exact Ideal.mul_mem_right _ _ h2
    · exact Ideal.mul_mem_left _ _ h2
  have h2 := GlobalTheory.CovTop.LevelIndex.prod_absNorm_le C.Pg hN hg
  have h3 := GlobalTheory.CovTop.LevelIndex.card_levelQuotientGroup_le_prod_absNorm_pow_sq C.Pg D.R.r
  have h4 : (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW C i P).relIndex (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW C i (LevelP.full _ _ _)) ≤
      (D.host.g 0 * D.host.g 1) ^ (2 * D.R.f * D.R.r ^ 2) := by
    rw [pow_mul, ← hfr]
    exact h1.trans (h3.trans (Nat.pow_le_pow_left h2 _))
  have h5 := Real.log_le_log (Nat.cast_pos.2 (Nat.pos_of_ne_zero h0)) (Nat.cast_le (α := ℝ).2 h4)
  refine h5.trans (le_of_eq ?_)
  push_cast
  rw [Real.log_pow]
  push_cast
  ring
end
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_subgroup_index_bounded : ∀ (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) (D : D7) (Tu : Type) (C : LevCh D Tu) (t0 : Tu) (hC : C.Is t0) (i : Fin D.R.m) (P : LevelP C.Pg D.R.r ℂ), GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.IndexBound C i P := by
  first | exact @_root_.GlobalTheory.CovTop.LevelIndex.level_index_le_bound | exact _root_.GlobalTheory.CovTop.LevelIndex.level_index_le_bound | (intros; apply _root_.GlobalTheory.CovTop.LevelIndex.level_index_le_bound <;> assumption)
end
end
