module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsMumfordFamOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundHolds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepApplyEqSmulOfHalfIndicatorBase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSubmoduleSecondFactor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSpace

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BalTau
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UTau0

section Bal

variable {R : Type} [CommRing R] {B : Over (Sp R)} [GrpObj B] [IsCommMonObj B] (M : RigLB B) (cub : CubicalStr B M)
  {O : Type} [CommRing O] [StarRing O] (act : RingAct B O) {X : Type} [AddCommGroup X] [Module O X]
  (c : X → (𝟙_ (Over (Sp R)) ⟶ B))

def BalTau (τ : ∀ y z : X, LB.Gen (LB.LinComb M.L (GlobalTheory.PolDeg.lamPts (c y) (c z)) GlobalTheory.PolDeg.negε)) : Prop :=
  (∀ y z, (τ y z).IsGen) ∧
  (∀ y y' z p J, Good M.L p J →
    val (τ (y + y') z) (𝟙 _) p J * cubV cub p J (c y) (c y') (c z) =
      val (τ y z) (𝟙 _) p J * val (τ y' z) (𝟙 _) p J) ∧
  (∀ y z z' p J, Good M.L p J →
    val (τ y (z + z')) (𝟙 _) p J * cubV cub p J (c z) (c z') (c y) =
      val (τ y z) (𝟙 _) p J * val (τ y z') (𝟙 _) p J) ∧
  (∀ (a : O) (u : LB.Gen (LB.LinComb M.L (rosatiφ B (act.act a) (act.act (star a))) rosatiε)), u.IsGen →
    LB.Gen.Corr M.L _ _ _ _ (LB.pullGen M.L _ _ u (zero2 B)) (LB.oneGen M.L) →
    ∀ y z p J, Good M.L p J →
      val (τ (a • y) z) (𝟙 _) p J * val u (lift (c y) (c z)).left p J = val (τ y (star a • z)) (𝟙 _) p J)

end Bal

section Psi

variable {R : Type} [CommRing R] [IsDomain R]

abbrev w0φ (D₀ : DegPre R) (f : D₀.P.A ⟶ D₀.P.A) : Fin 4 → (D₀.P.A.left ⟶ D₀.P.A.left) :=
  ![(padd D₀.P.A (𝟙 _) f).left, 𝟙 D₀.P.A.left, f.left, (toUnit D₀.P.A ≫ η[D₀.P.A]).left]

abbrev w0ε : Fin 4 → ℤ := ![1, -2, -1, 2]

def rigV (D₀ : DegPre R) (p : Sp R) (J : (Sp R ⟶ D₀.P.A.left) → D₀.P.L.ι) :=
  val (L := D₀.P.L) (φ := fun _ : PUnit => eSec D₀.P.A) (ε := fun _ => 1) D₀.rig (𝟙 _) p J

def tauV (D₀ : DegPre R)
    (ψ : ∀ y : D₀.X, LB.Gen (LB.LinComb D₀.P.L (K := PUnit) (fun _ => (D₀.c y).left) (fun _ => -1)))
    (p : Sp R) (J : (Sp R ⟶ D₀.P.A.left) → D₀.P.L.ι) (y z : D₀.X) :=
  val (ψ (y + z)) (𝟙 _) p J * (val (ψ y) (𝟙 _) p J)⁻¹ * (val (ψ z) (𝟙 _) p J)⁻¹ * (rigV D₀ p J)⁻¹

def RLaws (D₀ : DegPre R) {O : Type} [CommRing O] [StarRing O] [Module O D₀.X] (onB : D₀.P.OAct O) (w0 : O)
    (uw : LB.Gen (LB.LinComb D₀.P.L (w0φ D₀ (onB.act w0)) w0ε))
    (ψ : ∀ y : D₀.X, LB.Gen (LB.LinComb D₀.P.L (K := PUnit) (fun _ => (D₀.c y).left) (fun _ => -1))) : Prop :=
  (∀ y, (ψ y).IsGen) ∧
  (∀ y y' z p J, Good D₀.P.L p J →
    tauV D₀ ψ p J (y + y') z * cubV D₀.cub p J (D₀.c y) (D₀.c y') (D₀.c z) = tauV D₀ ψ p J y z * tauV D₀ ψ p J y' z) ∧
  (∀ y p J, Good D₀.P.L p J → val (ψ (-y)) (𝟙 _) p J * val D₀.sym (D₀.c y).left p J = val (ψ y) (𝟙 _) p J) ∧
  (∀ (a : O) (u : LB.Gen (LB.LinComb D₀.P.L (rosatiφ D₀.P.A (onB.act a) (onB.act (star a))) rosatiε)), u.IsGen →
    LB.Gen.Corr D₀.P.L _ _ _ _ (LB.pullGen D₀.P.L _ _ u (zero2 D₀.P.A)) (LB.oneGen D₀.P.L) →
    ∀ y z p J, Good D₀.P.L p J →
      tauV D₀ ψ p J (a • y) z * val u (lift (D₀.c y) (D₀.c z)).left p J = tauV D₀ ψ p J y (star a • z)) ∧
  (∀ y p J, Good D₀.P.L p J →
    tauV D₀ ψ p J y (w0 • y) * val uw (D₀.c y).left p J = val (ψ y) (𝟙 _) p J * rigV D₀ p J)

end Psi

end GlobalTheory.UTau0
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotientAbelianSchemeFiniteFlatSubgroup
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotientAbelianSchemeFiniteFlatSubgroup
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbQuotientAny

open GlobalTheory.AffineQuotient GlobalTheory.AbelianQuotient


set_option backward.isDefEq.respectTransparency false in
theorem exists_quotient_abelianScheme :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (H : Over (Sp R)) [GrpObj H] (i : H ⟶ A), IsAbelianScheme A → IsMonHom i → Mono i → IsFinite H.hom → Flat H.hom → ∃ (B : Over (Sp R)) (_ : GrpObj B) (q : A ⟶ B) (π : B ⟶ A), IsAbelianScheme B ∧ IsMonHom q ∧ IsFinite q.left ∧ Flat q.left ∧ Surjective q.left ∧ IsFinite π.left ∧ IsPullback ((fst H A ≫ i) * snd H A) (snd H A) q q := by
  intro R _ _ A _ H _ i hA _ _ _ _
  have := hA.comm
  have := hA.proper
  have := hA.smooth
  have := hA.geomConnected
  have : IsCommMonObj H := ⟨by
    rw [← cancel_mono i, Category.assoc, IsMonHom.mul_hom, ← BraidedCategory.braiding_naturality_assoc,
      IsCommMonObj.mul_comm]⟩
  obtain ⟨N, hN, hH⟩ := GlobalTheory.FiniteFlatKilled.main R H ‹_› ‹_›
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have := (GlobalTheory.AbTorsionAnyBase.isFinite_and_flat_mulA _ A hA N hN).1
  obtain ⟨Λ, _, _, _, _, e, _⟩ := exists_hopfAlgebra R H
  have hi : i ^ N = 1 := by
    rw [← Category.id_comp i, ← MonObj.pow_comp, hH, MonObj.one_comp]
  obtain ⟨Q, q, π, h₁, h₂, h₃, h₄, h₅⟩ := exists_quotient_hopf
    (GlobalTheory.HopfQuot.affine_quotient GlobalTheory.exists_basis_mem_of_span_eq_top_of_semilocal) (e.hom ≫ i)
    (mulA A N) (by
    rw [mulA, comp_pow, comp_pow, Category.comp_id, Category.comp_id, mul_pow, ← comp_pow,
      ← comp_pow i, hi, comp_one, comp_one, _root_.one_mul])
  have hq : IsPullback ((fst H A ≫ i) * snd H A) (snd H A) q q := by
    refine h₅.of_iso (whiskerRightIso e A) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
      <;> simp [comp_mul]
  obtain ⟨inst, hcomm, hhom, -⟩ := exists_grpObj i q hq
  refine ⟨Q, inst, q, π, ?_, hhom, h₂, h₃, h₄, h₁, hq⟩
  have : IsSeparated Q.hom := by rw [← Over.w π]; infer_instance
  have : LocallyOfFiniteType Q.hom := by rw [← Over.w π]; infer_instance
  have hw : q.left ≫ Q.hom = A.hom := Over.w q
  have := GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ A.hom
    hA.smooth hA.geomConnected
  have : Flat (q.left ≫ Q.hom) := by rw [hw]; infer_instance
  have : UniversallyClosed (q.left ≫ Q.hom) := by rw [hw]; infer_instance
  have : GeometricallyReduced (q.left ≫ Q.hom) := by rw [hw]; infer_instance
  have : GeometricallyConnected (q.left ≫ Q.hom) := by rw [hw]; infer_instance
  have := flat_of_comp_of_flat_of_surjective q.left Q.hom
  have := UniversallyClosed.of_comp_surjective q.left Q.hom
  have := geometricallyReduced_of_comp q.left Q.hom
  have : LocallyOfFinitePresentation Q.hom := inferInstance
  exact ⟨hcomm, smooth_of_grpObj_of_flat Q, ⟨⟩, geometricallyConnected_of_comp q.left Q.hom⟩

end GlobalTheory.AbQuotientAny
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotientAbelianSchemeFiniteFlatSubgroupStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_quotient_abelianScheme_finiteFlat_subgroup : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (H : Over (Sp R)) [GrpObj H] (i : H ⟶ A), IsAbelianScheme A → IsMonHom i → Mono i → IsFinite H.hom → Flat H.hom → ∃ (B : Over (Sp R)) (_ : GrpObj B) (q : A ⟶ B) (π : B ⟶ A), IsAbelianScheme B ∧ IsMonHom q ∧ IsFinite q.left ∧ Flat q.left ∧ Surjective q.left ∧ IsFinite π.left ∧ IsPullback ((fst H A ≫ i) * snd H A) (snd H A) q q := by
  first | exact @GlobalTheory.AbQuotientAny.exists_quotient_abelianScheme | exact GlobalTheory.AbQuotientAny.exists_quotient_abelianScheme | (intros; apply GlobalTheory.AbQuotientAny.exists_quotient_abelianScheme <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EffCartierComapOfIdlAlong
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj

namespace GlobalTheory.NormBlLift

theorem effCartier_comap_of_idlAlong {X : Scheme.{0}} (J : X.IdealSheafData) {R : Type} [CommRing R] [IsDomain R]
    [IsLocalRing R] (a : Sp R ⟶ X) (f : R) (hf : f ≠ 0) (hJ : idlAlong J a = Ideal.span {f}) :
    FinalTheorems.EffCartier (J.comap a) := by
  rw [idlAlong_eq_idealAlong, GlobalTheory.IndefiniteRowSideFullHecke.NormalisedBlowupCone.idealAlong] at hJ
  set e := (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv with he
  have hI : (J.comap a).ideal ⟨⊤, isAffineOpen_top _⟩ = Ideal.span {e.symm f} := by
    have h2 := congrArg (Ideal.map e.symm.toRingHom) hJ
    rw [Ideal.map_span, Set.image_singleton, Ideal.map_map] at h2
    have : e.symm.toRingHom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom = RingHom.id _ := by
      ext x; exact e.symm_apply_apply x
    rw [this, Ideal.map_id] at h2
    exact h2
  intro x
  refine ⟨⟨⊤, isAffineOpen_top _⟩, e.symm f, trivial, ?_, hI⟩
  rw [mem_nonZeroDivisors_iff]
  refine ⟨fun z hz => ?_, fun z hz => ?_⟩
  · apply e.injective
    have := congrArg e hz
    rw [map_mul, map_zero, e.apply_symm_apply] at this
    rw [map_zero]; exact (mul_eq_zero.1 this).resolve_left hf
  · apply e.injective
    have := congrArg e hz
    rw [map_mul, map_zero, e.apply_symm_apply] at this
    rw [map_zero]; exact (mul_eq_zero.1 this).resolve_right hf

end GlobalTheory.NormBlLift

namespace GlobalTheory.NormBlLift

theorem lift_normBl : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (Z S : Scheme.{0}) (i : F.X ⟶ Z) (π : S ⟶ Z) (j : F.X ⟶ S) [IsOpenImmersion j] [IsOpenImmersion i] (J : Z.IdealSheafData), IsNormBl π J → j ≫ π = i → π ⁻¹' Set.range i = Set.range j → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R] (a : Sp R ⟶ Z) (y : Sp (FractionRing R) ⟶ F.X), jK R ≫ a = y ≫ i → ∀ f : R, f ≠ 0 → idlAlong J a = Ideal.span {f} → ∃! ξ : Sp R ⟶ S, ξ ≫ π = a := by
  intro g n F Z S i π j _ _ J hN hji hpre R _ _ _ _ _ a y hy f hf hJ
  obtain ⟨-, S₀, π₀, ν, U, hB, hνπ, hfin, -, -, -⟩ := hN
  have hE : FinalTheorems.EffCartier (J.comap a) := effCartier_comap_of_idlAlong J a f hf hJ
  have hEK : FinalTheorems.EffCartier (J.comap (jK R ≫ a)) := by
    refine effCartier_comap_of_idlAlong J (jK R ≫ a) (algebraMap R (FractionRing R) f) ?_ ?_
    · exact (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hf
    · rw [show jK R = spMap (algebraMap R (FractionRing R)) from rfl, GlobalTheory.TraitOrder.idlAlong_comp, hJ,
        Ideal.map_span, Set.image_singleton]
  obtain ⟨b, hb, hbu⟩ := hB.2 _ a hE
  have hK : (y ≫ j) ≫ ν = jK R ≫ b := by
    refine (hB.2 _ _ hEK).unique ?_ ?_
    · rw [Category.assoc, Category.assoc, hνπ, hji, hy]
    · rw [Category.assoc, hb]
  have L := GlobalTheory.existsUnique_lift_spec_of_isLocalization (nonZeroDivisors R) le_rfl ν (y ≫ j) b hK
  obtain ⟨c, ⟨hc1, hc2⟩, -⟩ := L
  refine ⟨c, by show c ≫ π = a; rw [← hνπ, ← Category.assoc, hc2, hb], fun c' hc' => ?_⟩
  have h1 : c' ≫ ν = b := hbu _ (by show (c' ≫ ν) ≫ π₀ = a; rw [Category.assoc, hνπ]; exact hc')
  have hr : Set.range (jK R ≫ c') ⊆ Set.range j := by
    rintro _ ⟨w, rfl⟩
    rw [← hpre]
    show π ((jK R ≫ c') w) ∈ Set.range i
    rw [← Scheme.Hom.comp_apply, Category.assoc, hc', hy, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  have h2 : jK R ≫ c' = y ≫ j := by
    have hl := IsOpenImmersion.lift_fac j (jK R ≫ c') hr
    rw [← hl]
    congr 1
    rw [← cancel_mono i, ← hji, ← Category.assoc, hl, Category.assoc, hc', hy, hji]
  exact (GlobalTheory.existsUnique_lift_spec_of_isLocalization (nonZeroDivisors R) le_rfl ν (y ≫ j) b hK).unique ⟨h2, h1⟩ ⟨hc1, hc2⟩

end GlobalTheory.NormBlLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatDegreeLogFormAbsLe
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.CovTop.FlatSz

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}

theorem lrd_bounds {PP A M : ℝ} (hH : HostNum D L PP A M) :
    0 ≤ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd D.host.E ∧ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd D.host.E ≤ 2 * L.sc.L := by
  have hne : (discr D.host.E : ℝ) ≠ 0 := by exact_mod_cast NumberField.discr_ne_zero D.host.E
  have h1 : (1 : ℝ) ≤ |(discr D.host.E : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs (NumberField.discr_ne_zero D.host.E)
  have hlog0 : 0 ≤ Real.log |(discr D.host.E : ℝ)| := Real.log_nonneg h1
  have hf : (0 : ℝ) < D.R.f := by have := hH.f8; positivity
  have heq : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd D.host.E = Real.log |(discr D.host.E : ℝ)| / (2 * D.R.f) := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd, NumberField.rootDiscr_def, Int.cast_abs, Real.log_rpow (abs_pos.2 hne), hH.deg]
    push_cast
    ring
  rw [heq]
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (by positivity)]
  nlinarith [hH.disc]

theorem abs_flatDegVal_le (p : PtAt ex Csz) (i : Fin D.R.m) {PP A M : ℝ} (hH : HostNum D L PP A M) (hW : WtNum p i PP) :
    |GlobalTheory.FlatLine.flatDegVal (dat p i) (Formalism.L2.DIV.ofRecord D L p.Del p.h0).logOm| ≤ 9 * D.R.r * L.sc.L := by
  have hd : p.T.Q.H.d = D.host.d := p.fw.laws.pins.1.1
  have hpq : ((dat p i).p : ℝ) + (dat p i).q = D.R.r := by exact_mod_cast hW.sig.2.2
  have hom := hW.om
  have hL : 10 ≤ L.sc.L := hH.big.2.1
  have hld : Real.log (p.T.Q.H.d : ℝ) ≤ L.sc.L := by rw [hd]; exact hH.logd
  have hld0 : 0 ≤ Real.log (p.T.Q.H.d : ℝ) := Real.log_natCast_nonneg _
  obtain ⟨hr0, hr1⟩ := lrd_bounds hH
  unfold GlobalTheory.FlatLine.flatDegVal
  set a := (Formalism.L2.DIV.ofRecord D L p.Del p.h0).logOm
  set P : ℝ := ((dat p i).p : ℝ)
  set Q : ℝ := ((dat p i).q : ℝ)
  set u := Real.log (p.T.Q.H.d : ℝ)
  set v := GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd D.host.E
  have hP : 0 ≤ P := Nat.cast_nonneg _
  have hQ : 0 ≤ Q := Nat.cast_nonneg _
  have h1 : |(P - Q) / 2 * a| ≤ (P + Q) / 2 * (3 * L.sc.L) := by
    rw [abs_mul, abs_div, abs_two]
    refine mul_le_mul ?_ hom (abs_nonneg _) (by positivity)
    gcongr
    exact abs_le.2 ⟨by linarith, by linarith⟩
  have h2 : |Q * (u - v)| ≤ Q * (2 * L.sc.L) := by
    rw [abs_mul, abs_of_nonneg hQ]
    exact mul_le_mul_of_nonneg_left (abs_le.2 ⟨by linarith, by linarith⟩) hQ
  have h3 := abs_add_le ((P - Q) / 2 * a) (Q * (u - v))
  rw [hpq] at h1
  have hQr : Q ≤ D.R.r := by rw [← hpq]; linarith
  have hr : (0 : ℝ) ≤ D.R.r := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_right hQr (by linarith : (0 : ℝ) ≤ 2 * L.sc.L), mul_nonneg hr (by linarith : (0 : ℝ) ≤ L.sc.L)]

end GlobalTheory.CovTop.FlatSz

namespace GlobalTheory.CovTop.FlatSz

end GlobalTheory.CovTop.FlatSz

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleTrivialOfGeneratorFpqcDescent
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleTrivialOfGeneratorFpqcDescent
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw

namespace GlobalTheory.FlatDescent

theorem injective_app_of_flat {X Y : Scheme.{0}} (p : Y ⟶ X) [Flat p] [Surjective p] [QuasiCompact p]
    (U : X.Opens) : Function.Injective (p.app U) := by
  have := effectiveEpi_morphismRestrict p U
  intro a b hab
  have hb : Function.Bijective U.topIso.inv := ConcreteCategory.bijective_of_isIso _
  apply hb.1
  apply injective_appTop_of_epi (p ∣_ U)
  rw [appTop_morphismRestrict_apply, appTop_morphismRestrict_apply, hab]

theorem unit_ext_of_flat {X Y : Scheme.{0}} (p : Y ⟶ X) [Flat p] [Surjective p] [QuasiCompact p]
    {U : X.Opens} {a b : Γ(X, U)ˣ} (h : ∀ y : Y, p y ∈ U → gm p y U a = gm p y U b) : a = b := by
  have e : pullU p U a = pullU p U b := unit_ext fun y hy => by
    rw [gm_pull (𝟙 Y) p y U hy, gm_pull (𝟙 Y) p y U hy, Category.id_comp]
    exact h y hy
  exact Units.ext (injective_app_of_flat p U (congrArg Units.val e))

theorem exists_unit_of_gm_eq {X X' Z : Scheme.{0}} (f : X' ⟶ X) [Flat f] [Surjective f] [QuasiCompact f]
    {g₁ g₂ : Z ⟶ X'} (h : IsPullback g₁ g₂ f f) (U : X.Opens) (s : Γ(X', f ⁻¹ᵁ U)ˣ)
    (hs : ∀ z : Z, f (g₁ z) ∈ U → gm g₁ z _ s = gm g₂ z _ s) :
    ∃ a : Γ(X, U)ˣ, pullU f U a = s := by
  have hg : g₁ ⁻¹ᵁ f ⁻¹ᵁ U ≤ g₂ ⁻¹ᵁ f ⁻¹ᵁ U := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, h.w]
  have e : res le_rfl (pullU g₁ _ s) = res hg (pullU g₂ _ s) := unit_ext fun z hz => by
    rw [gm_res _ z _ hz, gm_res _ z _ hz, gm_pull (𝟙 Z) g₁ z _ hz, gm_pull (𝟙 Z) g₂ z _ (hg hz),
      Category.id_comp, Category.id_comp]
    exact hs z hz
  obtain ⟨a, ha, -⟩ := (existsUnique_app_eq_iff f h U _ rfl le_rfl hg s.val).2 (congrArg Units.val e)
  obtain ⟨a, rfl⟩ := (isUnit_app_iff f U a).1 (ha ▸ s.isUnit)
  exact ⟨a, Units.ext ha⟩

theorem triv_of_gen_descent : ∀ {X X' Z : Scheme.{0}} (M : LB X), M.IsLB → ∀ (f : X' ⟶ X), Flat f →
    Surjective f → QuasiCompact f → ∀ (g₁ g₂ : Z ⟶ X'), IsPullback g₁ g₂ f f →
    ∀ t : LB.Gen (M.pull f), t.IsGen →
    (∀ (z : Z) (J : (Z ⟶ X) → M.ι), Geo.Tor.Good M z J → val t g₁ z J = val t g₂ z J) → Triv M := by
  intro X X' Z M hM f _ _ _ g₁ g₂ h t ht hv
  have le : ∀ i, f ⁻¹ᵁ M.U i ≤ LB.wchart M (fun _ : PUnit => f) (fun _ => i) := fun i x hx =>
    Set.mem_iInter.2 fun _ => hx
  have ex : ∀ i, ∃ a : Γ(X, M.U i)ˣ, pullU f _ a = res (le i) (t.s fun _ => i) := fun i =>
    exists_unit_of_gm_eq f h (M.U i) _ fun z hz => by
      have hz₂ : f (g₂ z) ∈ M.U i := (congrArg (fun q : Z ⟶ X => q z ∈ M.U i) h.w).mp hz
      obtain ⟨J, hJ, eJ⟩ := exists_good M hM z (fun _ : PUnit => g₁ ≫ f) (fun _ => i)
        (fun _ _ _ => rfl) (fun _ => hz)
      have v := hv z J hJ
      rw [val_of t g₁ z J (fun _ => i) eJ,
        val_of t g₂ z J (fun _ => i) (fun k => h.w ▸ eJ k)] at v
      exact (gm_res g₁ z _ hz _).trans (v.trans (gm_res g₂ z _ hz₂ _).symm)
  choose a ha using ex
  have ga : ∀ i (y : X'), f y ∈ M.U i →
      gm f y (M.U i) (a i) = gm (𝟙 X') y (LB.wchart M (fun _ : PUnit => f) (fun _ => i)) (t.s fun _ => i) :=
    fun i y hy => by
      have := gm_pull (𝟙 X') f y (M.U i) hy (a i)
      rw [Category.id_comp, ha] at this
      exact this.symm.trans (gm_res (𝟙 X') y (le i) hy _)
  refine ⟨⟨a⟩, fun i j => unit_ext_of_flat f fun y hy => ?_⟩
  have c := gen_trans ht (𝟙 X') y (j := fun _ => i) (j' := fun _ => j) (le i hy.1) (le j hy.2)
  rw [← ga i y hy.1, ← ga j y hy.2, trF, Fintype.prod_unique, zpow_one, Category.id_comp] at c
  exact (gm_res f y _ hy _).trans (c.trans ((map_mul _ _ _).trans (congrArg _ (gm_res f y _ hy _))).symm)

end GlobalTheory.FlatDescent
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleTrivialOfGeneratorFpqcDescentStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundle_trivial_of_generator_fpqc_descent : ∀ {X X' Z : Scheme.{0}} (M : LB X), M.IsLB → ∀ (f : X' ⟶ X), Flat f → Surjective f → QuasiCompact f → ∀ (g₁ g₂ : Z ⟶ X'), IsPullback g₁ g₂ f f → ∀ t : LB.Gen (M.pull f), t.IsGen → (∀ (z : Z) (J : (Z ⟶ X) → M.ι), Geo.Tor.Good M z J → val t g₁ z J = val t g₂ z J) → Triv M := by
  first | exact @GlobalTheory.FlatDescent.triv_of_gen_descent | exact GlobalTheory.FlatDescent.triv_of_gen_descent | (intros; apply GlobalTheory.FlatDescent.triv_of_gen_descent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelCoinvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelCoinvariant
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

namespace GlobalTheory.KCoinvGood

theorem augAt_le_SB {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} (om : Rep σ Y W) (v : Pl (F := F)) : augAt om v ≤ SB _ :=
  Submodule.span_le.mpr fun _ ⟨_, _, _, hφ, _, hφ₁, _, e⟩ => e ▸ sub_mem hφ₁ hφ

theorem acts_zero {F : Type} [Field F] [NumberField F] {R κ : Type} [Zero R] [Fintype κ] (ev : AF F → R)
    (T : Module.End ℂ ((κ → AF F) → ℂ)) : Acts ev T 0 0 := fun r _ => by
  have e : tens ev (0 : (κ → R) → ℂ) r = 0 := funext fun x => by simp [tens]
  rw [e, map_zero]

theorem ker_eq_of {V P : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup P] [Module ℂ P] [Nontrivial P]
    (S A : Submodule ℂ V) (p : V →ₗ[ℂ] P) (hA : A ≤ LinearMap.ker p) (honto : S.map p = ⊤)
    (h : S ⊓ LinearMap.ker p = A ∨ S ⊓ LinearMap.ker p = S) : ∀ φ ∈ S, p φ = 0 ↔ φ ∈ A := by
  rcases h with h | h
  · intro φ hφ
    refine ⟨fun h0 => h ▸ ⟨hφ, h0⟩, fun hm => hA hm⟩
  · exfalso
    obtain ⟨x, hx⟩ := exists_ne (0 : P)
    have : x ∈ S.map p := honto ▸ Submodule.mem_top
    obtain ⟨y, hy, rfl⟩ := this
    have hy' : y ∈ S ⊓ LinearMap.ker p := by rw [h]; exact hy
    exact hx hy'.2

theorem factor_of {V P : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup P] [Module ℂ P]
    (S : Submodule ℂ V) (p : V →ₗ[ℂ] P) (l : V →ₗ[ℂ] ℂ) (honto : S.map p = ⊤) (hk : ∀ φ ∈ S, p φ = 0 → l φ = 0) :
    ∃ l₀ : P →ₗ[ℂ] ℂ, ∀ φ ∈ S, l φ = l₀ (p φ) := by
  set q := p.domRestrict S
  have hs : Function.Surjective q := by
    intro x
    have : x ∈ S.map p := honto ▸ Submodule.mem_top
    obtain ⟨y, hy, rfl⟩ := this
    exact ⟨⟨y, hy⟩, rfl⟩
  have hker : LinearMap.ker q ≤ LinearMap.ker (l.domRestrict S) := fun x hx => hk x.1 x.2 hx
  refine ⟨((LinearMap.ker q).liftQ (l.domRestrict S) hker).comp (q.quotKerEquivOfSurjective hs).symm.toLinearMap,
    fun φ hφ => ?_⟩
  have : (q.quotKerEquivOfSurjective hs).symm (p φ) = Submodule.Quotient.mk ⟨φ, hφ⟩ := by
    rw [LinearEquiv.symm_apply_eq]; rfl
  simp [this]

theorem kCoinv (hP : GlobalTheory.FunPr.Hypotheses₂) : GlobalTheory.ThK.KCoinv := by
  intro F E _ _ _ _ _ σ B a a' G X om om' R Rf hm
  have ht := hm.triple
  have hf := hm.fin
  refine ⟨fun v hv => ?_, GlobalTheory.T.weil_representation_preserves_space hP F E σ B a a' G X om om' ht⟩
  haveI := hf.nontriv v
  have hnr := GlobalTheory.T.character_at_uniformizer_not_root_of_unity F E σ B a a' G X om om' ht v hv
  have k1 : ∀ φ ∈ SB _, Rf.p v φ = 0 ↔ φ ∈ augAt om v :=
    ker_eq_of _ _ _ (hf.inv v) (hf.onto v) <|
      GlobalTheory.T.augmentation_submodule_first_factor hP F E σ B a a' G X om om' ht v hv hnr _ (le_inf (augAt_le_SB om v) (hf.inv v)) inf_le_left
        fun h hh φ hφ φ₁ hφ₁ hact => ⟨hφ₁, by
          have := hf.equiv v h hh φ hφ.1 0 (zero_mem _) φ₁ hφ₁ 0 (zero_mem _) hact (acts_zero _ _)
            (by rw [map_zero]; exact hφ.2)
          rw [map_zero] at this; exact this⟩
  have k2 : ∀ φ ∈ SB _, Rf.p' v φ = 0 ↔ φ ∈ augAt om' v :=
    ker_eq_of _ _ _ (hf.inv' v) (hf.onto' v) <|
      GlobalTheory.T.augmentation_submodule_second_factor hP F E σ B a a' G X om om' ht v hv hnr _ (le_inf (augAt_le_SB om' v) (hf.inv' v)) inf_le_left
        fun h hh φ hφ φ₁ hφ₁ hact => ⟨hφ₁, by
          have := hf.equiv v h hh 0 (zero_mem _) φ hφ.1 0 (zero_mem _) φ₁ hφ₁ (acts_zero _ _) hact
            (by rw [map_zero]; exact hφ.2.symm)
          rw [map_zero] at this; exact this.symm⟩
  refine ⟨k1, k2, fun t ξ => ?_, fun l hl => ?_⟩
  · have : ξ ∈ (SB _).map (Rf.p' v) := hf.onto' v ▸ Submodule.mem_top
    obtain ⟨φ, hφ, rfl⟩ := this
    obtain ⟨φ₀, h₀, hd⟩ := GlobalTheory.T.schwartz_bruhat_local_approximation hP F E σ B a a' G X om om' ht v hv hnr t φ hφ
    refine ⟨φ₀, h₀, ?_⟩
    have := hf.inv' v hd
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at this
    exact this.symm
  · exact factor_of _ _ _ (hf.onto' v) fun φ hφ h0 => hl ((k2 φ hφ).1 h0)

end GlobalTheory.KCoinvGood
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelCoinvariantStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_kernel_coinvariant : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.ThK.KCoinv := by
  first | exact @GlobalTheory.KCoinvGood.kCoinv | exact GlobalTheory.KCoinvGood.kCoinv | (intros; apply GlobalTheory.KCoinvGood.kCoinv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BiholomorphicLiftSystem
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime]

theorem Datum.algebraMap_injective (D : Datum p) (hm : D.m = 1) :
    Function.Injective (algebraMap (𝓞 D.F) D.O) := by
  haveI := D.freeO
  haveI := D.finO
  haveI : Nontrivial D.O := by
    apply Module.nontrivial_of_finrank_pos (R := ℤ)
    rw [D.rankO, hm]; simpa using Module.finrank_pos (R := ℚ) (M := D.F)
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra ha0
  have hF : (a : D.F) ≠ 0 := by exact_mod_cast ha0
  obtain ⟨y, hy0, hyint⟩ := IsAlgebraic.exists_integral_multiple
    (a.2.isAlgebraic.inv)
  set b : 𝓞 D.F := ⟨_, hyint⟩
  have hab : a * b = (y : 𝓞 D.F) := by
    apply RingOfIntegers.coe_injective
    simp only [map_mul, map_intCast]
    show (a : D.F) * ((y : ℤ) • (a : D.F)⁻¹) = _
    rw [zsmul_eq_mul]
    field_simp
  have h1 : algebraMap (𝓞 D.F) D.O (y : 𝓞 D.F) = 0 := by rw [← hab, map_mul, ha, zero_mul]
  rw [map_intCast] at h1
  have : (y : ℤ) • (1 : D.O) = 0 := by rw [zsmul_eq_mul, _root_.mul_one, h1]
  rcases smul_eq_zero.mp this with h | h
  · exact hy0 h
  · exact one_ne_zero h

theorem Datum.exists_zsmul_eq_algebraMap (D : Datum p) (hm : D.m = 1) (x : D.O) :
    ∃ e : ℤ, e ≠ 0 ∧ ∃ a : 𝓞 D.F, e • x = algebraMap (𝓞 D.F) D.O a := by
  haveI := D.freeO
  haveI := D.finO
  let f : 𝓞 D.F →ₗ[ℤ] D.O := (algebraMap (𝓞 D.F) D.O).toAddMonoidHom.toIntLinearMap
  have hf : Function.Injective f := D.algebraMap_injective hm
  let M := LinearMap.range f
  have h1 := rank_quotient_add_rank_of_isDomain M
  rw [rank_range_of_injective f hf, ← Module.finrank_eq_rank (R := ℤ) (M := 𝓞 D.F),
    ← Module.finrank_eq_rank (R := ℤ) (M := D.O), RingOfIntegers.rank, D.rankO, hm, one_pow,
    _root_.one_mul] at h1
  obtain ⟨k, hk⟩ := Cardinal.lt_aleph0.mp (Module.rank_lt_aleph0 (R := ℤ) (M := D.O ⧸ M))
  rw [hk] at h1
  norm_cast at h1
  have h0 : Module.rank ℤ (D.O ⧸ M) = 0 := by rw [hk]; norm_cast; omega
  obtain ⟨e, he, hex⟩ := (rank_eq_zero_iff.mp h0) (Submodule.Quotient.mk x)
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hex
  obtain ⟨a, ha⟩ := hex
  exact ⟨e, he, a, ha.symm⟩

theorem Datum.algebraMap_surjective_of_m_eq_one :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p), D.m = 1 → Function.Surjective (algebraMap (𝓞 D.F) D.O) := by
  intro p _ D hm x
  haveI := D.freeO
  haveI := D.finO
  obtain ⟨e, he, a, ha⟩ := D.exists_zsmul_eq_algebraMap hm x
  haveI : Algebra.IsIntegral ℤ D.O := Algebra.IsIntegral.of_finite ℤ D.O
  obtain ⟨P, hPm, hP⟩ := Algebra.IsIntegral.isIntegral (R := ℤ) x
  have h1 : Polynomial.aeval (algebraMap ℤ D.O e * x) (P.scaleRoots e) = 0 :=
    Polynomial.scaleRoots_aeval_eq_zero (by rwa [Polynomial.aeval_def])
  rw [← Algebra.smul_def, ha, Polynomial.aeval_algebraMap_apply] at h1
  have h2 : Polynomial.aeval a (P.scaleRoots e) = 0 :=
    D.algebraMap_injective hm (by rw [h1, map_zero])
  have he' : (e : D.F) ≠ 0 := by exact_mod_cast he
  have h4 : Polynomial.aeval (a : D.F) (P.scaleRoots e) = 0 := by
    have := congrArg (algebraMap (𝓞 D.F) D.F) h2
    rwa [← Polynomial.aeval_algebraMap_apply, map_zero] at this
  have h3 : Polynomial.eval₂ (algebraMap ℤ D.F) ((a : D.F) / e) P = 0 := by
    have := Polynomial.scaleRoots_eval₂_mul (p := P) (algebraMap ℤ D.F) ((a : D.F) / e) e
    rw [show algebraMap ℤ D.F e * ((a : D.F) / e) = (a : D.F) by
      rw [algebraMap_int_eq, eq_intCast]; field_simp] at this
    rw [← Polynomial.aeval_def, h4] at this
    exact (mul_eq_zero.mp this.symm).resolve_left (pow_ne_zero _ (by simpa using he'))
  have hint : IsIntegral ℤ ((a : D.F) / e) := ⟨P, hPm, h3⟩
  obtain ⟨a', ha'⟩ : ∃ a' : 𝓞 D.F, (a' : D.F) = (a : D.F) / e := ⟨⟨_, hint⟩, rfl⟩
  refine ⟨a', ?_⟩
  have hae : a = e • a' := by
    apply RingOfIntegers.coe_injective
    rw [zsmul_eq_mul, map_mul, map_intCast]
    change (a : D.F) = (e : D.F) * (a' : D.F)
    rw [ha']
    field_simp
  apply smul_right_injective D.O he
  change e • algebraMap (𝓞 D.F) D.O a' = e • x
  rw [ha, ← map_zsmul, ← hae]

end GlobalTheory.UPel.HT
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageRegSet
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

set_option autoImplicit false

namespace GlobalTheory.Desc.GaussPt

variable {Y X : Scheme.{0}} [IsIntegral Y] [IsIntegral X]

theorem theta_stalk {π : Y ⟶ X} {θ : X.functionField →+* Y.functionField} (h : PFF (𝟙 _) π θ) (y : Y)
    (a : X.presheaf.stalk (π y)) :
    θ (algebraMap _ X.functionField a) = algebraMap _ Y.functionField (π.stalkMap y a) := by
  obtain ⟨l, h₁, h₂⟩ := h
  rw [Category.comp_id] at h₁
  subst h₁
  let sY := Y.presheaf.stalkSpecializes (genericPoint_specializes y)
  let sX := X.presheaf.stalkSpecializes (genericPoint_specializes (π y))
  have e₁ : Spec.map sY ≫ Y.fromSpecStalk y = gp Y :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk _
  let t : X.presheaf.stalk (genericPoint X) ⟶ Y.presheaf.stalk (genericPoint Y) := CommRingCat.ofHom θ
  have e₂ : π.stalkMap y ≫ sY = sX ≫ t := by
    apply Spec.map_injective
    rw [← cancel_mono (X.fromSpecStalk (π y)), Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkMap_fromSpecStalk, ← Category.assoc, e₁, h₂, Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    rfl
  exact (congrArg (fun f => CommRingCat.Hom.hom f a) e₂).symm

theorem theta_fnOf {π : Y ⟶ X} {θ : X.functionField →+* Y.functionField} (h : PFF (𝟙 _) π θ)
    (U : X.Opens) (hU : genericPoint X ∈ U) (hU' : genericPoint Y ∈ π ⁻¹ᵁ U) (s : Γ(X, U)) :
    θ (fnOf U hU s) = fnOf (π ⁻¹ᵁ U) hU' (π.app U s) := by
  have hU'' : π (genericPoint Y) ∈ U := hU'
  rw [← algebraMap_germ (x := π (genericPoint Y)) hU'' s, theta_stalk h,
    Scheme.Hom.germ_stalkMap_apply]
  exact algebraMap_germ hU' _

theorem regAt_theta {π : Y ⟶ X} {θ : X.functionField →+* Y.functionField} (h : PFF (𝟙 _) π θ) (y : Y)
    {u : X.functionField} (hu : RegAt (π y) u) : RegAt y (θ u) := by
  obtain ⟨a, rfl⟩ := hu
  exact ⟨_, (theta_stalk h y a).symm⟩

theorem unitAt_theta {π : Y ⟶ X} {θ : X.functionField →+* Y.functionField} (h : PFF (𝟙 _) π θ) (y : Y)
    {u : X.functionField} (hu : UnitAt (π y) u) : UnitAt y (θ u) := by
  obtain ⟨a, ha, rfl⟩ := hu
  exact ⟨_, ha.map _, (theta_stalk h y a).symm⟩

theorem preimage_regSet {π : Y ⟶ X} [Flat π] {θ : X.functionField →+* Y.functionField}
    (h : PFF (𝟙 _) π θ) (y : Y) : θ ⁻¹' (regSet y) = regSet (π y) := by
  ext u
  refine ⟨fun ⟨c, hc⟩ => ?_, fun hu => regAt_theta h y hu⟩
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := X.presheaf.stalk (π y)) u
  have hb0 : algebraMap _ X.functionField b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  letI := (π.stalkMap y).hom.toAlgebra
  have : Module.Flat (X.presheaf.stalk (π y)) (Y.presheaf.stalk y) := Flat.stalkMap π y
  have : IsLocalHom (algebraMap (X.presheaf.stalk (π y)) (Y.presheaf.stalk y)) :=
    inferInstanceAs (IsLocalHom (π.stalkMap y).hom)
  have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := X.presheaf.stalk (π y))
    (B := Y.presheaf.stalk y)
  have e : π.stalkMap y a = c * π.stalkMap y b := by
    apply IsFractionRing.injective (Y.presheaf.stalk y) Y.functionField
    rw [map_mul, hc, ← theta_stalk h, ← theta_stalk h, ← map_mul, div_mul_cancel₀ _ hb0]
  have hm : a ∈ Ideal.span {b} := by
    rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := Y.presheaf.stalk y) (Ideal.span {b}),
      Ideal.mem_comap, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton']
    exact ⟨c, e.symm⟩
  obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.1 hm
  exact ⟨d, by rw [map_mul, mul_div_cancel_right₀ _ hb0]⟩

theorem spMap_cst {R : Type} [CommRing R] (p : X ⟶ Sp R) : spMap (GlobalTheory.Desc.cst p) = gp X ≫ p := by
  have h : p = X.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appTop) := by
    rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp]
    simp
  conv_rhs => rw [h, gp, ← Category.assoc, Scheme.fromSpecStalk_toSpecΓ, ← Spec.map_comp]
  rfl

theorem comp_cst {V : Scheme.{0}} {R R₁ : Type} [CommRing R] [CommRing R₁] {ρ : R →+* R₁} {p : X ⟶ Sp R}
    {q : Y ⟶ Sp R₁} {i : V ⟶ Y} {φ : V ⟶ X} {θ : X.functionField →+* Y.functionField} (h : PFF i φ θ)
    (w : φ ≫ p = (i ≫ q) ≫ spMap ρ) : θ.comp (GlobalTheory.Desc.cst p) = (GlobalTheory.Desc.cst q).comp ρ := by
  obtain ⟨l, h₁, h₂⟩ := h
  have : spMap (θ.comp (GlobalTheory.Desc.cst p)) = spMap ((GlobalTheory.Desc.cst q).comp ρ) := by
    have e1 : spMap (θ.comp (GlobalTheory.Desc.cst p)) = spMap θ ≫ spMap (GlobalTheory.Desc.cst p) := by
      rw [← Spec.map_comp]; rfl
    have e2 : spMap ((GlobalTheory.Desc.cst q).comp ρ) = spMap (GlobalTheory.Desc.cst q) ≫ spMap ρ := by
      rw [← Spec.map_comp]; rfl
    rw [e1, e2, spMap_cst, spMap_cst, ← Category.assoc, ← h₂, ← h₁]
    simp only [Category.assoc, w]
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective this)

theorem regAt_cst {R : Type} [CommRing R] (p : X ⟶ Sp R) (x : X) (r : R) : RegAt x (GlobalTheory.Desc.cst p r) :=
  regAt_fnOf (U := ⊤) trivial trivial _

theorem unitAt_cst_iff {R : Type} [CommRing R] (p : X ⟶ Sp R) (x : X) (r : R) :
    UnitAt x (GlobalTheory.Desc.cst p r) ↔ r ∉ (p x).asIdeal := by
  refine (unitAt_fnOf_iff (U := ⊤) trivial trivial _).trans ?_
  change x ∈ X.basicOpen (p.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)) ↔ _
  rw [← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine]
  rfl

end GlobalTheory.Desc.GaussPt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoOfIsClosedImmersion
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbMonoIso

open GlobalTheory.NearFibreIso

theorem fibre_isIso {R : Type} [CommRing R] {X Y : Scheme.{0}} (s : X ⟶ Sp R) (f : Y ⟶ X)
    [IsClosedImmersion f] [GeometricallyConnected s] [Surjective (f ≫ s)] {g g' : ℕ}
    (hg' : SmoothOfRelativeDimension g' s) (hg : SmoothOfRelativeDimension g (f ≫ s))
    (hle : g' ≤ g) (K : Type) [Field K] [Algebra R K] :
    IsIso (pullback.snd f (pullback.fst s (spMap (algebraMap R K)))) := by
  have H₁ := IsPullback.of_hasPullback f (pullback.fst s (spMap (algebraMap R K)))
  have H₂ := IsPullback.of_hasPullback s (spMap (algebraMap R K))
  have H := H₁.paste_vert H₂
  have h₁ : SmoothOfRelativeDimension g' (pullback.snd s (spMap (algebraMap R K))) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g').of_isPullback H₂ hg'
  have h₂ : SmoothOfRelativeDimension g (pullback.snd f (pullback.fst s (spMap (algebraMap R K))) ≫
      pullback.snd s (spMap (algebraMap R K))) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback H hg
  have : Surjective (pullback.snd f (pullback.fst s (spMap (algebraMap R K))) ≫
      pullback.snd s (spMap (algebraMap R K))) := MorphismProperty.of_isPullback H ‹_›
  have : Smooth s := hg'.smooth
  have : AlgebraicGeometry.IsIntegral (Limits.pullback s (spMap (algebraMap R K))) := GlobalTheory.isIntegral_of_isPullback_of_smooth H₂
  have : Smooth (pullback.snd f (pullback.fst s (spMap (algebraMap R K))) ≫
      pullback.snd s (spMap (algebraMap R K))) := h₂.smooth
  have : AlgebraicGeometry.IsReduced (Limits.pullback f (pullback.fst s (spMap (algebraMap R K)))) :=
    GlobalTheory.isReduced_of_smooth_of_isReduced (pullback.snd f (pullback.fst s (spMap (algebraMap R K))) ≫
      pullback.snd s (spMap (algebraMap R K)))
  have : Nonempty ↥(Limits.pullback (C := Scheme.{0}) f (pullback.fst s (spMap (algebraMap R K)))) := by
    obtain ⟨z, -⟩ := (pullback.snd f (pullback.fst s (spMap (algebraMap R K))) ≫
      pullback.snd s (spMap (algebraMap R K))).surjective (default : PrimeSpectrum K)
    exact ⟨z⟩
  exact GlobalTheory.DivisiblePart.isIso_of_dim_le _ _ h₁ h₂ hle

end GlobalTheory.AbMonoIso

namespace GlobalTheory.AbMonoIso

open GlobalTheory.NearFibreIso

theorem isIso_of_isClosedImmersion {S X Y : Scheme.{0}} [IsLocallyNoetherian S] (p : X ⟶ S)
    (f : Y ⟶ X) [IsClosedImmersion f] [GeometricallyConnected p] [Surjective (f ≫ p)]
    [Flat (f ≫ p)] {g g' : ℕ} (hg' : SmoothOfRelativeDimension g' p)
    (hg : SmoothOfRelativeDimension g (f ≫ p)) (hle : g' ≤ g) : IsIso f := by
  have : Smooth p := hg'.smooth
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have hn : ∀ y : X, Near f (MorphismProperty.isomorphisms _) y := by
    intro y
    obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (p y)) isOpen_univ
    replace hU : IsAffineOpen U := hU
    let j : Sp Γ(S, U) ⟶ S := hU.fromSpec
    obtain ⟨z, hz⟩ : p y ∈ Set.range j := by rw [hU.range_fromSpec]; exact hyU
    let gX := pullback.fst p j
    let s := pullback.snd p j
    let f' := pullback.snd f gX
    have HX := IsPullback.of_hasPullback p j
    have HY := IsPullback.of_hasPullback f gX
    have HYS := HY.paste_vert HX
    obtain ⟨y', hy', hy's⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := j) y z hz.symm
    have : IsLocallyNoetherian (Limits.pullback p j) := isLocallyNoetherian_of_isOpenImmersion gX
    have : Flat (f' ≫ s) := MorphismProperty.of_isPullback HYS ‹_›
    have : Surjective (f' ≫ s) := MorphismProperty.of_isPullback HYS ‹_›
    have h₁ : SmoothOfRelativeDimension g' s :=
      (smoothOfRelativeDimension_isStableUnderBaseChange g').of_isPullback HX hg'
    have h₂ : SmoothOfRelativeDimension g (f' ≫ s) :=
      (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback HYS hg
    have : IsProper f' := MorphismProperty.of_isPullback HY (inferInstanceAs (IsProper f))
    have : (s y').asIdeal.IsPrime := (s y').isPrime
    have := fibre_isIso s f' h₁ h₂ hle (s y').asIdeal.ResidueField
    have h := near_isIso_of_isProper s f' (s y').asIdeal.ResidueField y'
      (Ideal.ker_algebraMap_residueField (s y').asIdeal)
    have h' := Near.of_pullback f HY.flip h
    rwa [hy'] at h'
  have h := isIso_of_near f (𝟙 _) (fun y => by simpa using hn y)
  have e : f = inv (pullback.fst f (𝟙 X)) ≫ pullback.snd f (𝟙 X) := by
    rw [IsIso.eq_inv_comp, pullback.condition, Category.comp_id]
  rw [e]
  infer_instance

theorem isIso_of_mono : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (B B' : Over S) [GrpObj B] [GrpObj B'], IsAbelianScheme B → IsAbelianScheme B' → ∀ g g' : ℕ, SmoothOfRelativeDimension g B.hom → SmoothOfRelativeDimension g' B'.hom → g' ≤ g → ∀ x : B ⟶ B', IsMonHom x → Mono x → IsIso x := by
  intro S _ B B' _ _ hB hB' g g' hg hg' hle x _ _
  have := hB.proper
  have := hB.smooth
  have := hB'.proper
  have := hB'.geomConnected
  have : Mono x.left := inferInstanceAs (Mono ((Over.forget S).map x))
  have : IsProper (x.left ≫ B'.hom) := by rw [Over.w]; infer_instance
  have : IsProper x.left := IsProper.of_comp x.left B'.hom
  have : IsClosedImmersion x.left := (IsClosedImmersion.iff_isProper_and_mono _).2 ⟨‹_›, ‹_›⟩
  have hs : Surjective B.hom := ⟨fun t => ⟨(η[B] : 𝟙_ (Over S) ⟶ B).left t, by
    rw [← Scheme.Hom.comp_apply, Over.w]; rfl⟩⟩
  have : Surjective (x.left ≫ B'.hom) := by rw [Over.w]; exact hs
  have : Flat (x.left ≫ B'.hom) := by rw [Over.w]; infer_instance
  have : IsIso x.left :=
    isIso_of_isClosedImmersion B'.hom x.left hg' (by rw [Over.w]; exact hg) hle
  have : IsIso ((Over.forget _).map x) := ‹_›
  exact isIso_of_reflects_iso x (Over.forget _)

end GlobalTheory.AbMonoIso
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.Matched
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PinchLift

def GenOn {Y : Scheme.{0}} (L : LB Y) (O : Y.Opens) (s : ∀ k, Γ(Y, L.U k ⊓ O)ˣ) : Prop :=
  ∀ (k l : L.ι) (y : Y), y ∈ L.U k → y ∈ L.U l → y ∈ O →
    gm (𝟙 Y) y (L.U k ⊓ O) (s k) = gm (𝟙 Y) y (L.U k ⊓ L.U l) (L.g k l) * gm (𝟙 Y) y (L.U l ⊓ O) (s l)

def Matched {X' Z Z' : Scheme.{0}} (i' : Z' ⟶ X') (p' : Z' ⟶ Z) (L' : LB X') (LZ : LB Z)
    (w : LB.Iso (L'.pull i') (LZ.pull p')) (O' : X'.Opens) (OZ : Z.Opens) (s' : ∀ k, Γ(X', L'.U k ⊓ O')ˣ)
    (sZ : ∀ j, Γ(Z, LZ.U j ⊓ OZ)ˣ) : Prop :=
  ∀ (z : Z') (j : LZ.ι) (k : L'.ι), p' z ∈ LZ.U j → i' z ∈ L'.U k → p' z ∈ OZ → i' z ∈ O' →
    gm p' z (LZ.U j ⊓ OZ) (sZ j) =
      gm (𝟙 Z') z ((LZ.pull p').U (fun _ => j) ⊓ (L'.pull i').U (fun _ => k)) (w.s (fun _ => j, fun _ => k)) *
        gm i' z (L'.U k ⊓ O') (s' k)

end GlobalTheory.PinchLift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodOfFiniteSurjective
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.FiniteSurjDim

theorem eq_of_finite_surjective {k : Type} [Field k] {X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f] [Surjective f]
    (p : Y ⟶ Spec (CommRingCat.of k)) [Nonempty X] {a b : ℕ} (ha : SmoothOfRelativeDimension a (f ≫ p))
    (hb : SmoothOfRelativeDimension b p) : a = b := by
  have : Nonempty Y := ⟨f (Classical.arbitrary X)⟩
  have h1 := GlobalTheory.HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth (f ≫ p) a ha
  have h2 := GlobalTheory.HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth p b hb
  have c1 : topologicalKrullDim Y ≤ topologicalKrullDim X :=
    GlobalTheory.PosBaseChange.dim_le_of_isClosedMap f.isClosedMap f.surjective
  have c2 : topologicalKrullDim X ≤ topologicalKrullDim Y :=
    GlobalTheory.PosBaseChange.dim_le_of_isDiscrete f.continuous fun y => f.isDiscrete_preimage_singleton y
  rw [h1, h2] at c1 c2
  exact_mod_cast le_antisymm c2 c1

end GlobalTheory.FiniteSurjDim
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymmetricRigidifiedBundleBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymmetricRigidifiedBundleBaseChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.KeyVals

theorem isSymmetric_bL : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (R : Type) [CommRing R] (ξ : Sp R ⟶ S),
    L.IsSymmetric → (KeyVals.bL L ξ).IsSymmetric :=
  fun _ G _ _ L _ _ ξ h =>
    CubePf.sym_pull (cubeMapOf (isGrpPullback_pullback G ξ)) L (bL L ξ).isLB (bL L ξ).rigGen h

end GlobalTheory.KeyVals
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymmetricRigidifiedBundleBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSymmetric_rigidifiedBundleBaseChange : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (R : Type) [CommRing R] (ξ : Sp R ⟶ S),
    L.IsSymmetric → (KeyVals.bL L ξ).IsSymmetric := by
  first | exact @GlobalTheory.KeyVals.isSymmetric_bL | exact GlobalTheory.KeyVals.isSymmetric_bL | (intros; apply GlobalTheory.KeyVals.isSymmetric_bL <;> assumption)
end
end
