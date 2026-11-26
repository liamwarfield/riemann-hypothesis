module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionCoordinatesEqDegenerationSeriesStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LiftValuationIntegralNorm
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPelUnifPull
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolarisedAVIsoDescendsOfRationalThreeTorsion
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsStarNormLEOfIsCMField
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TwistedLabelsAllLevelsOfFourLe

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLinearUniformisationBaseChangeAdmissible
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLinearUniformisationBaseChangeAdmissible
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait

namespace GlobalTheory.Ex.Trait

theorem exists_pelUnif_baseChange : Laws → Laws3 → Laws4 → Laws5 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R'), AdmBase R I → AdmBase R' I' → ∀ g : R →+* R', Function.Injective g → I.map g ≤ I' → ∀ (t : SAB H (Sp R)) (P : PELUnif I t), ∃ (t' : SAB H (Sp R')) (_ : SABMap t' t (spMap g)) (P' : PELUnif I' t') (ψ : P'.D.toPre.P.A.left ⟶ P.D.toPre.P.A.left), IsGrpPullback P'.D.toPre.P.A P.D.toPre.P.A (spMap g) ψ := by
  intro h1 h3 h4 h5 E _ _ _ H R R' _ _ _ _ I I' hR hR' g hg hI t P
  obtain ⟨t', m₀, P', hD, -⟩ := GlobalTheory.ArcDataDescent.exists_pelUnif_pull h3.cubePull h1.polBaseChange h4.unifBaseChange h5
    hR hR' t P g hg hI
  have := hD.e_hom
  exact ⟨t', m₀, P', hD.e.hom.left ≫ pullback.fst P.D.toPre.P.A.hom (specOf g),
    ((isGrpPullback_of_iso hD.e).comp (isGrpPullback_pullback P.D.toPre.P.A (specOf g))).congr
      (Category.id_comp _) rfl⟩

end GlobalTheory.Ex.Trait
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLinearUniformisationBaseChangeAdmissibleStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linearUniformisation_baseChange_admissible : Laws → Laws3 → Laws4 → Laws5 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R'), AdmBase R I → AdmBase R' I' → ∀ g : R →+* R', Function.Injective g → I.map g ≤ I' → ∀ (t : SAB H (Sp R)) (P : PELUnif I t), ∃ (t' : SAB H (Sp R')) (_ : SABMap t' t (spMap g)) (P' : PELUnif I' t') (ψ : P'.D.toPre.P.A.left ⟶ P.D.toPre.P.A.left), IsGrpPullback P'.D.toPre.P.A P.D.toPre.P.A (spMap g) ψ := by
  first | exact @GlobalTheory.Ex.Trait.exists_pelUnif_baseChange | exact GlobalTheory.Ex.Trait.exists_pelUnif_baseChange | (intros; apply GlobalTheory.Ex.Trait.exists_pelUnif_baseChange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelIsoOfValuedAgreementOverField
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelIsoOfValuedAgreementOverField
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait

namespace GlobalTheory.FitMatch
open GlobalTheory.ArcPull GlobalTheory.ArcDataDescent

section General
variable {F F' : Type} [Field F] [Field F'] {B B₀ Y Y₀ : Scheme.{0}} {M : LB B} {M₀ : LB B₀} {φ : B ⟶ B₀}

theorem genRel_of_gauge {w : LB.Iso M (M₀.pull φ)} (hw : w.IsGen) {K : Type} [Fintype K] {pt : K → (Sp F ⟶ B)}
    {pt₀ : K → (Sp F ⟶ B₀)} {ε : K → ℤ} {t : LB.Gen (LB.LinComb M pt ε)} {t₀ : LB.Gen (LB.LinComb M₀ pt₀ ε)}
    (ht : t.IsGen) (ht₀ : t₀.IsGen) (x : Fˣ) (hp : ∀ k, pt k ≫ φ = pt₀ k) (z : Sp F) {J J'} (hJ : Good M₀ z J)
    (hJ' : Good M z J')
    (H : (∏ k, om w z J J' (pt k) ^ ε k) * val t (𝟙 _) z J' = Units.map (toStk z).toMonoidHom x * val t₀ (𝟙 _) z J) :
    GenRel w t t₀ (x : F) := by
  obtain rfl : (fun k => pt k ≫ φ) = pt₀ := funext hp
  refine (genRel_iff w t t₀ x z).2 ⟨hp, fun j j₀ h₀ h₁ => ?_⟩
  rw [val_of t _ z J' (fun k => J' (pt k)) (fun k => by rw [Category.id_comp]),
    val_of t₀ _ z J (fun k => J (pt k ≫ φ)) (fun k => by rw [Category.id_comp])] at H
  have m₀ : (𝟙 (Sp F) : Sp F ⟶ Sp F) z ∈ LB.wchart M₀ (fun k => pt k ≫ φ) j₀ := Set.mem_iInter.2 h₀
  have m₁ : (𝟙 (Sp F) : Sp F ⟶ Sp F) z ∈ LB.wchart M pt j := Set.mem_iInter.2 h₁
  have n₀ : (𝟙 (Sp F) : Sp F ⟶ Sp F) z ∈ LB.wchart M₀ (fun k => pt k ≫ φ) (fun k => J (pt k ≫ φ)) :=
    Set.mem_iInter.2 fun k => hJ (pt k ≫ φ)
  have n₁ : (𝟙 (Sp F) : Sp F ⟶ Sp F) z ∈ LB.wchart M pt (fun k => J' (pt k)) :=
    Set.mem_iInter.2 fun k => hJ' (pt k)
  have a := pw_trans ((isGen_iff w).1 hw) pt ε (𝟙 _) z m₀ n₀ m₁ n₁
  simp only [pw, Category.id_comp] at a
  have key : (∏ k, Geo.Tor.gw w (pt k) z (j₀ k) (j k) ^ ε k) * gm (𝟙 _) z (LB.wchart M pt j) (t.s j) =
      Units.map (toStk z).toMonoidHom x * gm (𝟙 _) z (LB.wchart M₀ (fun k => pt k ≫ φ) j₀) (t₀.s j₀) := by
    rw [a, gen_trans ht (𝟙 _) z m₁ n₁, gen_trans ht₀ (𝟙 _) z m₀ n₀]
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul H
    simp only [om, ofMul_mul, ofMul_inv] at e' ⊢
    linear_combination (norm := abel) e'
  exact congrArg Units.val key

theorem genRel_ext_iff (hM : M.IsLB) (hM₀ : M₀.IsLB) (w : LB.Iso M (M₀.pull φ)) {K : Type} [Fintype K]
    {pt : K → (Y ⟶ B)} {pt₀ : K → (Y₀ ⟶ B₀)} {ε : K → ℤ} {t : LB.Gen (LB.LinComb M pt ε)}
    {t₀ : LB.Gen (LB.LinComb M₀ pt₀ ε)} (ht : t.IsGen) (ht₀ : t₀.IsGen) (σ : F →+* F') (r : Sp F ⟶ Y) (r₀ : Sp F ⟶ Y₀)
    {s : Sp F' ⟶ Y} {s₀ : Sp F' ⟶ Y₀} (h : s = spMap σ ≫ r) (h₀ : s₀ = spMap σ ≫ r₀) (x : F) :
    GenRel w (LB.pullGen _ _ _ t s) (LB.pullGen _ _ _ t₀ s₀) (σ x) ↔
      GenRel w (LB.pullGen _ _ _ t r) (LB.pullGen _ _ _ t₀ r₀) x := by
  subst h h₀
  refine Iff.trans ?_ (genRel_pull_iff σ w (LB.pullGen _ _ _ t r) (LB.pullGen _ _ _ t₀ r₀) x)
  have p : (fun k => (spMap σ ≫ r) ≫ pt k) = fun k => spMap σ ≫ r ≫ pt k := funext fun _ => Category.assoc _ _ _
  have p₀ : (fun k => (spMap σ ≫ r₀) ≫ pt₀ k) = fun k => spMap σ ≫ r₀ ≫ pt₀ k := funext fun _ => Category.assoc _ _ _
  refine genRel_congr hM hM₀ w p p₀ (t := LB.pullGen _ _ _ t (spMap σ ≫ r))
    (t' := LB.pullGen _ _ _ (LB.pullGen _ _ _ t r) (spMap σ)) (t₀ := LB.pullGen _ _ _ t₀ (spMap σ ≫ r₀))
    (t₀' := LB.pullGen _ _ _ (LB.pullGen _ _ _ t₀ r₀) (spMap σ))
    (DVR.pullGen_isGen _ _ _ _ ht _) (DVR.pullGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _) _)
    (DVR.pullGen_isGen _ _ _ _ ht₀ _) (DVR.pullGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht₀ _) _)
    (fun y J hJ => ?_) (fun y J hJ => ?_) _ <;>
  rw [val_pull hJ, val_pull hJ, val_pull hJ, Category.assoc]

theorem toStk_vF {K : Type} [Fintype K] {pt : K → (Y ⟶ B)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb M pt ε)) (r : Sp F ⟶ Y)
    {z : Sp F} {J} (hJ : Good M z J) : toStk z (vF t r J) = (val t r z J).val :=
  toStk_valF r _ z (hJ.mem pt r) _
end General

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {D : DegPre R} {D' : DegPre R'}
  {f : R →+* R'} {C : Type} [Field C] [Algebra (FractionRing R) C] [Algebra (FractionRing R') C]

theorem tf_comp (hf : Along f C) : (TF (R := R') C).hom ≫ spMap f = (TF (R := R) C).hom :=
  (congrArg (· ≫ spMap f) (Geo.Tor.spMap_comp _ _).symm).trans ((Geo.Tor.spMap_comp _ _).symm.trans
    ((congrArg spMap (RingHom.ext fun x => hf x)).trans (Geo.Tor.spMap_comp _ _)))

theorem c_of_field (hf : Along f C) {ψ : D'.P.A.left ⟶ D.P.A.left} (gp : IsGrpPullback D'.P.A D.P.A (spMap f) ψ)
    (x : D'.X) (y : D.X) (h : (DegPre.cF D' C x).left ≫ ψ = (DegPre.cF D C y).left) :
    (D'.c x).left ≫ ψ = spMap f ≫ (D.c y).left := by
  have := D.P.isAb.proper
  let g : R' →+* C := (algebraMap (FractionRing R') C).comp (algebraMap R' _)
  have hg : Function.Injective g := (algebraMap (FractionRing R') C).injective.comp (IsFractionRing.injective _ _)
  have e : spMap g = (TF (R := R') C).hom := Geo.Tor.spMap_comp _ _
  refine ext_of_injective hg (X := Sp R') (π := spMap g) (p := 𝟙 _) (p' := 𝟙 _) (IsPullback.of_vert_isIso ⟨by simp⟩)
    D.P.A.hom ?_ ?_
  · rw [Category.assoc, gp.1.w, ← Category.assoc, Over.w, Category.assoc]
    exact (Category.id_comp _).trans ((Category.comp_id _).symm.trans (congrArg _ (Over.w (D.c y)).symm))
  · rw [e, ← Category.assoc _ (spMap f), tf_comp hf, ← Category.assoc]
    exact h

theorem genRel_field (hf : Along f C) {N N' : NumD C} (ν : NumOf D C N) (ν' : NumOf D' C N')
    {ψ : D'.P.A.left ⟶ D.P.A.left} (he : eSec D'.P.A ≫ ψ = spMap f ≫ eSec D.P.A) {w : LB.Iso D'.P.L (D.P.L.pull ψ)}
    (hw : w.IsGen) (hr : LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => 1)) D'.rig
      (rigPullOf ψ (spMap f) he D.P.L D.rig)) (x : N'.X) (y : N.X) (h s : Cˣ)
    (hc : (DegPre.cF D' C (ν'.eX x)).left ≫ ψ = (DegPre.cF D C (ν.eX y)).left)
    (hψ : N'.ψ x * h = N.ψ y * s) (hh : (h : C) * wVal ν' ν w (N'.c x) = wVal ν' ν w 1) :
    GenRel w (LB.pullGen _ _ _ (D'.psi (ν'.eX x)) (jFK (R := R') C)) (LB.pullGen _ _ _ (D.psi (ν.eX y)) (jFK (R := R) C))
      (s : C) := by
  have z : Sp C := (default : PrimeSpectrum C)
  have hJ : Good D.P.L z ν.J := fun p => (top_le_iff_mem _ _ z).1 (ν.good p)
  have hJ' : Good D'.P.L z ν'.J := fun p => (top_le_iff_mem _ _ z).1 (ν'.good p)
  have hv : ∀ a, toStk z (wVal ν' ν w a) = (om w z ν.J ν'.J (ν'.eA a).left).val := fun a =>
    toStk_valF _ ((D.P.L.pull ψ).U (fun _ => ν.J ((ν'.eA a).left ≫ ψ)) ⊓ D'.P.L.U (ν'.J (ν'.eA a).left)) z
      ⟨mem_pull.2 (hJ ((ν'.eA a).left ≫ ψ)), hJ' _⟩ _
  have c₀ : ∀ a, (DegPre.cF D C a).left = jFK (R := R) C ≫ D.xK a := fun a => Category.assoc _ _ _
  have c₁ : ∀ a, (DegPre.cF D' C a).left = jFK (R := R') C ≫ D'.xK a := fun a => Category.assoc _ _ _
  have pm := (maps_iff w _ (fun _ => eSec D.P.A) _ D'.rig D.rig (spMap f) _
    (rigPull_le ψ (spMap f) he D.P.L) (fun _ => rfl)).1 hr
  have e := pmaps_om (fun _ => he) pm (TF (R := R') C).hom z hJ hJ'
  rw [Fintype.prod_unique, zpow_one] at e
  replace e := (congrArg (fun q => val D.rig q z ν.J) (tf_comp hf).symm).trans e
  have a₀ := (congrArg (toStk z) (ν.ψ_eq y)).trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (toStk_vF _ _ hJ) ((toStk_vF _ _ hJ).trans (congrArg Units.val e))))
  have a₁ := (congrArg (toStk z) (ν'.ψ_eq x)).trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (toStk_vF _ _ hJ') (toStk_vF _ _ hJ')))
  have a₂ := congrArg (toStk z) hh
  rw [map_mul, hv, hv, ν'.c_eq, c₁, map_one] at a₂
  let U := Units.map (toStk z).toMonoidHom
  have b₀ : U (N.ψ y) = _ * (_ * _) := Units.ext a₀
  have b₁ : U (N'.ψ x) = _ * _ := Units.ext a₁
  have b₂ : U h * _ = om w z ν.J ν'.J ((TF (R := R') C).hom ≫ eSec D'.P.A) := Units.ext a₂
  have b₃ := congrArg U hψ
  rw [map_mul, map_mul, b₀, b₁, ← b₂] at b₃
  refine genRel_of_gauge hw (DVR.pullGen_isGen _ _ _ _ (D'.psi_gen _) _) (DVR.pullGen_isGen _ _ _ _ (D.psi_gen _) _) s
    (fun _ => (congrArg (· ≫ ψ) (c₁ _).symm).trans (hc.trans (c₀ _))) z hJ hJ' ?_
  rw [Fintype.prod_unique, val_pull hJ, val_pull hJ', Category.id_comp, Category.id_comp, zpow_neg_one]
  have e' := congrArg Additive.ofMul b₃
  apply Additive.ofMul.injective
  simp only [U, ofMul_mul, ofMul_inv] at e' ⊢
  linear_combination (norm := abel) e'

theorem match_of_fit : GlobalTheory.UT.LL → AllS fun {_} _ _ _ {H} {_} {_} {_} {_} _ {_} {_} _ _ {_} a {C} _ _ A u _ {_} M f {_} ν' J => ∀ u₀ : M.W, (u : C) = algebraMap (FractionRing M.W) C (algebraMap _ _ u₀) → ∀ ψ (he : eSec M.P.D.toPre.P.A ≫ ψ = spMap f ≫ eSec a.D₀.P.A) w e, Fit A u M f ν' J ψ w e → LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec M.P.D.toPre.P.A) (fun _ => 1)) M.P.D.toPre.rig (rigPullOf ψ (spMap f) he a.D₀.P.L a.D₀.rig) → (letI := H.starRing; ∀ x, (M.P.oD.onB.act x).left ≫ ψ = ψ ≫ (a.oa.onB.act x).left) → GlobalTheory.LN.Match a f u₀ M.P.D.toPre M.P.oD ψ he w e := by
  intro _ E _ _ _ H D l c O _ β O' _ _ _ b a C _ _ _ _ _ _ A u r o M f N' ν' J _ hf u₀ hu ψ he w e
    ⟨gp, hw, hp, hx, _, hh⟩ hr ha
  have hc : ∀ χ : A.N.X, (DegPre.cF M.P.D.toPre C (ν'.eX (J.e χ))).left ≫ ψ = (DegPre.cF a.D₀ C (A.ν.eX χ)).left :=
    fun χ => by
      rw [← ν'.c_eq, ← A.ν.c_eq]
      exact (congrArg (fun q => (ν'.eA q).left ≫ ψ) (J.c_eq χ)).trans (hp _)
  have inj : Function.Injective f := fun x y h => IsFractionRing.injective O' (FractionRing O')
    ((algebraMap (FractionRing O') C).injective ((hf x).symm.trans (by rw [h]; exact hf y)))
  refine ⟨gp, hw, hr, ha, fun y => ?_, fun F _ _ _ _ uF hF huF y => ?_⟩
  · obtain ⟨χ, rfl⟩ := A.ν.eX.surjective y
    rw [hx]
    exact c_of_field hf gp _ _ (hc χ)
  · obtain ⟨χ, rfl⟩ := A.ν.eX.surjective y
    have k := genRel_field hf A.ν ν' he hw hr (J.e χ) χ (J.h (A.N.c χ)) (u ^ (A.be.be χ χ / 2)) (hc χ) (J.ψ_eq χ)
      ((congrArg (fun q => (J.h (A.N.c χ) : C) * wVal ν' A.ν w q) (J.c_eq χ)).trans (hh _))
    have lift : ∀ (L : Type) [Field L] [Algebra (FractionRing M.W) L] [Algebra (FractionRing O') L], Along f L →
        jFK (R := O') L = spMap (algebraMap (FractionRing M.W) L) ≫ genMap inj := fun L _ _ _ h =>
      (congrArg spMap (IsLocalization.ringHom_ext (nonZeroDivisors O') (RingHom.ext fun x =>
        (h x).symm.trans (congrArg (algebraMap (FractionRing M.W) L) (fracMap_algebraMap inj x).symm)))).trans
        (Geo.Tor.spMap_comp _ _)
    have t := fun (L : Type) [Field L] [Algebra (FractionRing M.W) L] [Algebra (FractionRing O') L] (h : Along f L) =>
      genRel_ext_iff M.P.D.toPre.P.isLB a.D₀.P.isLB w (M.P.D.toPre.psi_gen (ν'.eX (J.e χ))) (a.D₀.psi_gen (A.ν.eX χ))
        (algebraMap (FractionRing M.W) L) (𝟙 _) (genMap inj) (s := jFK (R := M.W) L) (Category.comp_id _).symm (lift L h)
        (algebraMap M.W _ u₀ ^ (A.be.be χ χ / 2))
    rw [Units.val_zpow_eq_zpow_val, hu, ← map_zpow₀] at k
    have k' := (t F fun x => (hF x).symm).2 ((t C hf).1 k)
    rw [hx, huF, ← A.be_eq, ← map_zpow₀]
    exact k'

end GlobalTheory.FitMatch
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelIsoOfValuedAgreementOverFieldStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modelIso_of_valued_agreement_over_field : GlobalTheory.UT.LL → AllS fun {_} _ _ _ {H} {_} {_} {_} {_} _ {_} {_} _ _ {_} a {C} _ _ A u _ {_} M f {_} ν' J => ∀ u₀ : M.W, (u : C) = algebraMap (FractionRing M.W) C (algebraMap _ _ u₀) → ∀ ψ (he : eSec M.P.D.toPre.P.A ≫ ψ = spMap f ≫ eSec a.D₀.P.A) w e, Fit A u M f ν' J ψ w e → LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec M.P.D.toPre.P.A) (fun _ => 1)) M.P.D.toPre.rig (rigPullOf ψ (spMap f) he a.D₀.P.L a.D₀.rig) → (letI := H.starRing; ∀ x, (M.P.oD.onB.act x).left ≫ ψ = ψ ≫ (a.oa.onB.act x).left) → GlobalTheory.LN.Match a f u₀ M.P.D.toPre M.P.oD ψ he w e := by
  first | exact @GlobalTheory.FitMatch.match_of_fit | exact GlobalTheory.FitMatch.match_of_fit | (intros; apply GlobalTheory.FitMatch.match_of_fit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolarizedAbelianPullbackLineBundle
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolarizedAbelianPullbackLineBundle
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait

namespace GlobalTheory.Ex.Trait

theorem eq_of_comp_schemeDominant {W X Y Z : Scheme.{0}} {f g : X ⟶ Y} (s : Y ⟶ Z) [IsSeparated s] (h : f ≫ s = g ≫ s)
    (d : W ⟶ X) [IsSchemeTheoreticallyDominant d] (hU : d ≫ f = d ≫ g) : f = g := by
  let f' : Over.mk (f ≫ s) ⟶ Over.mk s := Over.homMk f
  let g' : Over.mk (f ≫ s) ⟶ Over.mk s := Over.homMk g h.symm
  haveI : IsSeparated (Over.mk s).hom := ‹IsSeparated s›
  let d' : Over.mk (d ≫ f ≫ s) ⟶ Over.mk (f ≫ s) := Over.homMk d
  have e : d' ≫ f' = d' ≫ g' := Over.OverMorphism.ext hU
  let l := equalizer.lift d' e
  have hd : d = l.left ≫ (equalizer.ι f' g').left := by
    rw [← Over.comp_left, equalizer.lift_ι]; rfl
  have hker : (equalizer.ι f' g').left.ker = ⊥ := by
    apply le_bot_iff.1
    calc _ ≤ (l.left ≫ (equalizer.ι f' g').left).ker := Scheme.Hom.le_ker_comp _ _
      _ = ⊥ := by rw [← hd]; exact d.ker_eq_bot
  haveI : IsIso (equalizer.ι f' g').left := IsClosedImmersion.isIso_iff_ker_eq_bot.2 hker
  have h0 : IsIso ((Over.forget Z).map (equalizer.ι f' g')) := (inferInstance : IsIso (equalizer.ι f' g').left)
  have : IsIso (equalizer.ι f' g') := isIso_of_reflects_iso _ (Over.forget Z)
  exact congrArg CommaMorphism.left ((cancel_epi (equalizer.ι f' g')).1 (equalizer.condition f' g'))

theorem schemeDominant_spec_of_injective {A B : Type} [CommRing A] [CommRing B] [_root_.IsReduced A] (φ : A →+* B)
    (hφ : Function.Injective φ) : IsSchemeTheoreticallyDominant (Spec.map (CommRingCat.ofHom φ)) := by
  haveI : IsDominant (Spec.map (CommRingCat.ofHom φ)) := by
    rw [isDominant_iff]
    show DenseRange (PrimeSpectrum.comap φ)
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical, (RingHom.injective_iff_ker_eq_bot φ).1 hφ]
    exact bot_le
  exact IsSchemeTheoreticallyDominant.of_isDominant _

theorem act_comm_of_torsion : Laws → EndDeterminedOnTorsionSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (S : Scheme.{0}) (s : Sp R ⟶ S) (B : PolAV (Sp R)) (B₀ : PolAV S) (ρ : letI := H.starRing; B.OAct (𝓞 E)) (ρ₀ : letI := H.starRing; B₀.OAct (𝓞 E)) (ψ : B.A.left ⟶ B₀.A.left), IsGrpPullback B.A B₀.A s ψ → LBIso B.L (B₀.L.pull ψ) → ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] [Algebra (FractionRing R) C] (n : ℕ), 2 ≤ n → ∀ x : 𝓞 E, (letI := H.starRing; (∀ (j : ℕ) (y : TF (R := R) C ⟶ B.A), y ^ n ^ j = 1 → (y ≫ ρ.act x).left ≫ ψ = y.left ≫ ψ ≫ (ρ₀.act x).left) → (ρ.act x).left ≫ ψ = ψ ≫ (ρ₀.act x).left) := by
  intro hL h₂ E _ _ _ H R _ _ _ S s B B₀ ρ ρ₀ ψ hψ hw C _ _ _ _ n hn x h
  letI := H.starRing
  obtain ⟨ρ', hρ'⟩ := polOActPull _ _ s B₀ B ψ hψ hw.symm (𝓞 E) ρ₀
  obtain ⟨P, g, hg, -, hm, ht⟩ := hL.polBaseChange _ _ (TF (R := R) C).hom B
  have gp : IsGrpPullback P.A B.A (TF (R := R) C).hom g := ⟨hg, fun T a b a₀ b₀ ha hb => by
    have e₁ : a₀ = toBase hg.w a := Over.OverMorphism.ext ha
    have e₂ : b₀ = toBase hg.w b := Over.OverMorphism.ext hb
    rw [e₁, e₂, ← hm]; rfl⟩
  obtain ⟨σ, hσ⟩ := polOActPull _ _ _ B P g gp ht (𝓞 E) ρ
  obtain ⟨σ', hσ'⟩ := polOActPull _ _ _ B P g gp ht (𝓞 E) ρ'
  obtain ⟨c, hc⟩ := exists_starNormLE_of_isCMField E (fun a => H.bar_eq a) x
  set j := 4 ^ P.g * P.g.factorial * (2 * c) with hj
  have hlt : j < (n ^ j) ^ 2 := (Nat.lt_pow_self hn).trans_le (Nat.le_self_pow two_ne_zero _)
  have key := h₂ P.g c (n ^ j) hlt C (Nat.cast_ne_zero.2 (by positivity)) P P rfl rfl (Iso.refl _)
    (ThetaPtDet.isPolIso_refl P) _ σ σ' x hc fun y hy => by
      let u : TF (R := R) C ⟶ Over.mk ((baseOver (Sp C)).hom ≫ (TF (R := R) C).hom) :=
        Over.homMk (𝟙 _) ((Category.id_comp _).trans (Category.id_comp _))
      let z : TF (R := R) C ⟶ B.A := u ≫ pushHom gp _ y
      have hz : z.left = y.left ≫ g := Category.id_comp _
      have hz' : z ^ n ^ j = 1 := by
        rw [← MonObj.comp_pow, ← map_pow, hy, map_one, MonObj.comp_one]
      have e := h j z hz'
      rw [← hρ', ← Category.assoc, ← Over.comp_left] at e
      have e' : (z ≫ ρ.act x).left = (z ≫ ρ'.act x).left := hψ.1.hom_ext e (by rw [Over.w, Over.w])
      rw [Iso.refl_hom, Category.comp_id, Category.id_comp]
      refine Over.OverMorphism.ext (hg.hom_ext ?_ (by rw [Over.w, Over.w]))
      rw [Over.comp_left _ _ _ z, Over.comp_left _ _ _ z, hz] at e'
      rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hσ, hσ']
      simpa only [Category.assoc] using e'
  rw [Iso.refl_hom, Category.comp_id, Category.id_comp] at key
  haveI : IsSchemeTheoreticallyDominant (jK R) := schemeDominant_spec_of_injective _ (IsFractionRing.injective R _)
  haveI : IsSchemeTheoreticallyDominant (jFK (R := R) C) := schemeDominant_spec_of_injective _ (RingHom.injective _)
  haveI : IsSchemeTheoreticallyDominant (TF (R := R) C).hom := by
    show IsSchemeTheoreticallyDominant (_ ≫ _); infer_instance
  haveI := B.isAb.proper
  haveI := B.isAb.smooth
  haveI : QuasiCompact (TF (R := R) C).hom := by
    show QuasiCompact (spMap (algebraMap (FractionRing R) C) ≫ spMap (algebraMap R (FractionRing R))); infer_instance
  haveI : IsSchemeTheoreticallyDominant g := IsSchemeTheoreticallyDominant.of_isPullback hg.flip
  rw [← hρ', eq_of_comp_schemeDominant B.A.hom ((Over.w (ρ.act x)).trans (Over.w (ρ'.act x)).symm) g
    (by rw [← hσ, ← hσ', key])]

end GlobalTheory.Ex.Trait
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolarizedAbelianPullbackLineBundleStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarized_abelian_pullback_line_bundle : Laws → EndDeterminedOnTorsionSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (S : Scheme.{0}) (s : Sp R ⟶ S) (B : PolAV (Sp R)) (B₀ : PolAV S) (ρ : letI := H.starRing; B.OAct (𝓞 E)) (ρ₀ : letI := H.starRing; B₀.OAct (𝓞 E)) (ψ : B.A.left ⟶ B₀.A.left), IsGrpPullback B.A B₀.A s ψ → LBIso B.L (B₀.L.pull ψ) → ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] [Algebra (FractionRing R) C] (n : ℕ), 2 ≤ n → ∀ x : 𝓞 E, (letI := H.starRing; (∀ (j : ℕ) (y : TF (R := R) C ⟶ B.A), y ^ n ^ j = 1 → (y ≫ ρ.act x).left ≫ ψ = y.left ≫ ψ ≫ (ρ₀.act x).left) → (ρ.act x).left ≫ ψ = ψ ≫ (ρ₀.act x).left) := by
  first | exact @GlobalTheory.Ex.Trait.act_comm_of_torsion | exact GlobalTheory.Ex.Trait.act_comm_of_torsion | (intros; apply GlobalTheory.Ex.Trait.act_comm_of_torsion <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ValuesIsoCommActionAbelianPartTorsion
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ValuesIsoCommActionAbelianPartTorsion
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait
noncomputable section
namespace GlobalTheory.Ex.ActPt

section
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem equiv_parts {k : ℕ} {p p' : QkPt D F k} (h : QkPt.Equiv D F p p') :
    ∃ z : D.X, p'.y = p.y + k • z ∧ p'.g.b = p.g.b * DegPre.cF D F z := by
  obtain ⟨z, h₁, g, h₂, h₃⟩ := h
  exact ⟨z, h₁, by rw [h₃.1, h₂.1]; rfl⟩

variable {O : Type} [CommRing O] [StarRing O] [Module O D.X] (oa : D.OAct O)

theorem mul_cF_act (x : O) (b : TF (R := R) F ⟶ D.P.A) (z : D.X) :
    (b * DegPre.cF D F z) ≫ oa.onB.act x = (b ≫ oa.onB.act x) * DegPre.cF D F (x • z) := by
  have := oa.onB.hom x
  rw [MonObj.mul_comp, DegPre.cF, DegPre.cF, oa.c_lin, Category.assoc]

theorem act_parts {k : ℕ} {x : O} {p p' : QkPt D F k} (h : QkAct oa x p p') :
    ∃ z : D.X, p'.y = x • p.y + k • z ∧ p'.g.b = (p.g.b ≫ oa.onB.act x) * DegPre.cF D F z := by
  obtain ⟨q, h₁, h₂, h₃⟩ := h
  obtain ⟨z, e₁, e₂⟩ := equiv_parts h₃
  exact ⟨z, by rw [e₁, h₁], by rw [e₂, h₂.1]⟩
end

theorem exists_image {C : Type} [CommRing C] {N N' : NumD C} (J : NumD.Iso N N') {k : ℕ} (p : N.QT k) :
    ∃ q : N'.QT k, q.1.1.toAdd = J.e p.1.1.toAdd ∧ J.Rel p.1.2 q.1.2 := by
  obtain ⟨h₁, h₂, h₃, -⟩ := NumD.hom_transport C C (RingHom.id C) N N' (TateInh.homOfIso J)
  obtain ⟨g, hg, -⟩ := h₁ p.1.2
  have hp : ∀ n : ℕ, (TateInh.homOfIso J).Rel (p.1.2 ^ n) (g ^ n) := fun n => by
    induction n with
    | zero => rw [pow_zero, pow_zero]; exact J.rel_one
    | succ n ih => rw [pow_succ, pow_succ]; exact h₂ _ _ _ _ ih hg
  have e := hp k
  rw [N.mem_QT.1 p.2] at e
  exact ⟨⟨(Multiplicative.ofAdd (J.e p.1.1.toAdd), g), (h₁ _).unique e (h₃ _)⟩, rfl, hg⟩

theorem main : GlobalTheory.UT.LL → BrGtSt → AllS fun {E} _ _ _ {H} {_} {_} {_} {_} _ {_} {_} _ _ {_} a {_} _ _ A u r {_} M _ {_} ν' J => M.P.TorsionIso → ∀ k : ℕ, 0 < k → Labels A u r M ν' J k → (∀ (x : 𝓞 E) y, ν'.eX (J.e (A.arc.act x y)) = x • ν'.eX (J.e y)) → ∀ (x : 𝓞 E) (y y' : A.N.A), y ^ k = 1 → (letI := H.starRing; A.ν.eA y' = A.ν.eA y ≫ a.oa.onB.act x → ν'.eA (J.φ y') = ν'.eA (J.φ y) ≫ M.P.oD.onB.act x) := by
  intro hL hB E _ _ _ H D l c O _ β O' _ _ _ b a C _ _ _ _ _ _ A u r o M f N' ν' J hr _ hT k hk hlab hlin x y y' hy hy'
  letI := H.starRing
  obtain ⟨-, -, -, -, B⟩ := hB O' a.D₀ a.even a.bimult C A.N A.ν
  obtain ⟨-, -, -, -, B'⟩ := hB M.W M.P.D.toPre M.P.D.psi_even M.P.D.tau_bimult C N' ν'
  obtain ⟨t, t₁, -, t₃, -, t₅, -⟩ := hT C k hk
  have im : ∀ w : D.La, ∃ p' : QkPt M.P.D.toPre C k, (t p').left = (o.I.ev k w).left ≫ M.φ ∧
      p'.y = ν'.eX (J.e (A.q k w).1.1.toAdd) ∧ p'.g.b = ν'.eA (J.φ (A.q k w).1.2.b) := fun w => by
    obtain ⟨p, hp, -⟩ := existsUnique_twRel A.be u (r k) (hr.pow hk) (A.q k w)
    obtain ⟨q, q₁, q₂⟩ := exists_image J p
    obtain ⟨p', hp'⟩ := (B' k).2.1 q
    let z : TFK (R := M.W) C ⟶ M.P.A.A := Over.homMk ((o.I.ev k w).left ≫ M.φ) (by
      rw [Category.assoc, M.cart.1.w, ← Category.assoc, Over.w]
      exact Category.id_comp _)
    have hz := (t₁ _ _).1 (hlab w p q p' z hp q₁ q₂ hp' rfl)
    refine ⟨p', by rw [← hz]; rfl, ?_, ?_⟩
    · rw [← hp'.1, q₁, hp.1]; rfl
    · rw [← hp'.2.1, q₂.1]; exact congrArg (fun s => ν'.eA (J.φ s)) hp.2.1
  obtain ⟨gm, hγ, hγ'⟩ := QStr.root_over A.N hk.ne' 1 y hy
  obtain ⟨p₀, hp₀⟩ := (B k).2.1 ⟨(1, gm), hγ'.trans A.N.io_zero.symm⟩
  obtain ⟨v, hv⟩ := A.I.onto k hk p₀
  obtain ⟨z₀, -, e₀⟩ := equiv_parts hv
  obtain ⟨z₁, d₁, e₁⟩ := act_parts a.oa (A.I.lin k hk x v)
  obtain ⟨p₁, a₁, b₁, c₁⟩ := im v
  obtain ⟨p₂, a₂, b₂, c₂⟩ := im (x • v)
  obtain ⟨p₃, h₃⟩ := qkAct_exists hL.1.globalFns M.P.D.tau_bimult M.P.oD x p₁
  have e₃ : t p₃ = t p₂ := by
    rw [t₅ _ _ _ h₃]
    ext1
    rw [a₂, o.I.lin, Over.comp_left, Over.comp_left, a₁, Category.assoc, Category.assoc, M.act]
  have h₂ : QkAct M.P.oD x p₁ p₂ :=
    (TorusExt.qkAct_iff_of_equiv M.P.D.tau_bimult hL.1.globalFns M.P.oD
      (qk_equiv_refl M.P.D.tau_bimult p₁) h₃).2
      ((t₃ _ _).1 e₃)
  obtain ⟨z₂, d₂, e₂⟩ := act_parts M.P.oD h₂
  obtain ⟨w₀, rfl⟩ := A.ν.eX.surjective z₀
  obtain ⟨w₁, rfl⟩ := A.ν.eX.surjective z₁
  rw [← (A.hq k v).1, ← (A.hq k (x • v)).1] at d₁
  rw [← (A.hq k v).2.1, ← (A.hq k (x • v)).2.1] at e₁
  rw [← (A.hq k v).2.1, ← hp₀.2.1] at e₀
  rw [b₁, b₂] at d₂
  rw [c₁, c₂] at e₂
  generalize (A.q k v).1.1.toAdd = s₁ at d₁ d₂
  generalize (A.q k (x • v)).1.1.toAdd = s₂ at d₁ d₂
  generalize (A.q k v).1.2.b = β₁ at e₀ e₁ e₂
  generalize (A.q k (x • v)).1.2.b = β₂ at e₁ e₂
  let e : A.N.X ≃+ N'.X := J.e
  let φ : A.N.A ≃* N'.A := J.φ
  have hc : ∀ χ, N'.c (e χ) = φ (A.N.c χ) := J.c_eq
  let act : A.N.X → A.N.X := fun s => A.ν.eX.symm (x • A.ν.eX s)
  have hl : ∀ s, ν'.eX (e (act s)) = x • ν'.eX (e s) := hlin x
  have ha : ∀ s, A.ν.eX (act s) = x • A.ν.eX s := fun s => A.ν.eX.apply_symm_apply _
  change ν'.eX (e s₂) = x • ν'.eX (e s₁) + k • z₂ at d₂
  change ν'.eA (φ β₂) = ν'.eA (φ β₁) ≫ _ * _ at e₂
  change ν'.eA (φ y') = ν'.eA (φ y) ≫ _
  have g₁ : s₂ = act s₁ + k • w₁ := A.ν.eX.injective (by rw [d₁, map_add (f := _), map_nsmul, ha])
  have g₂ : z₂ = ν'.eX (e w₁) := by
    rw [g₁, map_add (f := _), map_add (f := _), map_nsmul, map_nsmul, hl, add_right_inj, ← natCast_zsmul, ← natCast_zsmul] at d₂
    exact (smul_right_injective _ (Int.natCast_ne_zero.2 hk.ne') d₂).symm
  have g₀ : y = β₁ * A.N.c w₀ := A.ν.eA.injective (by rw [map_mul, A.ν.c_eq, ← e₀, hγ])
  have g₃ : y' * A.N.c w₁ = β₂ * A.N.c (act w₀) := A.ν.eA.injective (by
    rw [map_mul, map_mul, hy', g₀, map_mul, A.ν.c_eq, A.ν.c_eq, A.ν.c_eq, mul_cF_act, e₁, ha, mul_right_comm])
  have g₄ := congrArg (fun s => ν'.eA (φ s)) g₃
  simp only [map_mul, ← hc, ν'.c_eq, hl, e₂, ← g₂] at g₄
  rw [mul_right_comm, mul_left_inj] at g₄
  rw [g₄, g₀, map_mul, map_mul, ← hc, ν'.c_eq, mul_cF_act]

end GlobalTheory.Ex.ActPt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ValuesIsoCommActionAbelianPartTorsionStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuesIso_comm_action_abelianPart_torsion : GlobalTheory.UT.LL → BrGtSt → AllS fun {E} _ _ _ {H} {_} {_} {_} {_} _ {_} {_} _ _ {_} a {_} _ _ A u r {_} M _ {_} ν' J => M.P.TorsionIso → ∀ k : ℕ, 0 < k → Labels A u r M ν' J k → (∀ (x : 𝓞 E) y, ν'.eX (J.e (A.arc.act x y)) = x • ν'.eX (J.e y)) → ∀ (x : 𝓞 E) (y y' : A.N.A), y ^ k = 1 → (letI := H.starRing; A.ν.eA y' = A.ν.eA y ≫ a.oa.onB.act x → ν'.eA (J.φ y') = ν'.eA (J.φ y) ≫ M.P.oD.onB.act x) := by
  first | exact @GlobalTheory.Ex.ActPt.main | exact GlobalTheory.Ex.ActPt.main | (intros; apply GlobalTheory.Ex.ActPt.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LevelConditionValuedFieldTwistedUniformisation
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LevelConditionValuedFieldTwistedUniformisation
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait

noncomputable section
namespace GlobalTheory.Ex.Trait.LevelClause

theorem qEq_twist {O : Type} [CommRing O] {N : NumD O} {k : ℕ} (β : N.Form k) {u r : Oˣ} {j : ℕ} (h : r ^ j = u)
    {p q : N.QT j} {p' q' : (N.twist β u).QT j} (e : N.QEq p q) (hp : TwRel β u r p p') (hq : TwRel β u r q q') :
    (N.twist β u).QEq p' q' := by
  obtain ⟨z, h1, h2⟩ := e
  refine ⟨z, ?_, NumD.Gt.ext ?_ (funext fun (χ : N.X) => ?_)⟩
  · rw [hp.1, hq.1]; exact h1
  · rw [hq.2.1, h2, NumD.Gt.mul_b, NumD.Gt.mul_b, hp.2.1]; rfl
  · have e₁ : (N.twist β u).τ z χ = N.τ z χ * u ^ β.be z χ := N.twist_τ β u z χ
    have e₂ : r ^ β.be (p.1.1.toAdd + j • z) χ = r ^ β.be p.1.1.toAdd χ * u ^ β.be z χ := by
      rw [map_add (f := _), LinearMap.add_apply, map_nsmul, LinearMap.smul_apply, zpow_add, nsmul_eq_mul, zpow_mul,
        zpow_natCast, h]
    have e₃ : (p'.1.2 * (N.twist β u).io z).s χ =
        p'.1.2.s χ * (N.twist β u).τ z χ / N.θ (N.c χ) (show N.A from p'.1.2.b) (N.c z) := rfl
    refine (hq.2.2 χ).trans (Eq.trans ?_ e₃.symm)
    rw [h1, h2, e₁, e₂, hp.2.2 χ, hp.2.1, NumD.Gt.mul_s, NumD.io_s, NumD.io_b]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div]
    abel

theorem exists_image {O : Type} [CommRing O] {N N' : NumD O} (J : NumD.Iso N N') {k : ℕ} (p : N.QT k) :
    ∃ q : N'.QT k, q.1.1.toAdd = J.e p.1.1.toAdd ∧ J.Rel p.1.2 q.1.2 := by
  let I := NumD.Hom.ofIso J
  have hp : p.1.2 ^ k = N.io p.1.1.toAdd := p.2
  refine ⟨⟨(Multiplicative.ofAdd (J.e p.1.1.toAdd), I.img p.1.2), ?_⟩, rfl, I.rel_img _⟩
  have a := (I.rel_img p.1.2).pow k
  rw [hp] at a
  exact (I.rel_existsUnique _).unique a (I.rel_io _)

theorem qEq_image {O : Type} [CommRing O] {N N' : NumD O} (J : NumD.Iso N N') {k : ℕ} {p q : N.QT k} {p' q' : N'.QT k}
    (e : N.QEq p q) (hp : p'.1.1.toAdd = J.e p.1.1.toAdd) (hp' : J.Rel p.1.2 p'.1.2)
    (hq : q'.1.1.toAdd = J.e q.1.1.toAdd) (hq' : J.Rel q.1.2 q'.1.2) : N'.QEq p' q' := by
  obtain ⟨z, h1, h2⟩ := e
  let I := NumD.Hom.ofIso J
  refine ⟨J.e z, by rw [hq, hp, h1, map_add (f := _), map_nsmul], ?_⟩
  have a : I.Rel (p.1.2 * N.io z) (p'.1.2 * N'.io (J.e z)) := NumD.Hom.Rel.mul (I := I) hp' (I.rel_io z)
  rw [← h2] at a
  exact (I.rel_existsUnique _).unique (show I.Rel _ _ from hq') a

theorem genRel_of_gauge {F : Type} [Field F] {B B₀ : Scheme.{0}} {M : LB B} {M₀ : LB B₀}
    {φ : B ⟶ B₀} (w : LB.Iso M (M₀.pull φ)) (hw : w.IsGen) {K : Type} [Fintype K] {pt : K → (Sp F ⟶ B)}
    {pt₀ : K → (Sp F ⟶ B₀)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb M pt ε)) (ht : t.IsGen)
    (t₀ : LB.Gen (LB.LinComb M₀ pt₀ ε)) (ht₀ : t₀.IsGen) (x : F) (hpt : ∀ k, pt k ≫ φ = pt₀ k)
    (J : (Sp F ⟶ B₀) → M₀.ι) (J' : (Sp F ⟶ B) → M.ι) (gJ : ∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ M₀.U (J ψ)) (gJ' : ∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ M.U (J' ψ))
    (hv : (∏ k, valF (pt k) _ (w.s (fun _ => J (pt k ≫ φ), J' (pt k))).val ^ ε k) * vF t (𝟙 _) J' = x * vF t₀ (𝟙 _) J) :
    GenRel w t t₀ x := by
  obtain rfl : pt₀ = fun k => pt k ≫ φ := funext fun k => (hpt k).symm
  have z : Sp F := (default : PrimeSpectrum F)
  rw [genRel_iff w t t₀ x z]
  refine ⟨fun _ => rfl, fun j j₀ h₀ h₁ => ?_⟩
  have hJ := fun ψ => (top_le_iff_mem _ _ z).1 (gJ ψ)
  have hJ' := fun ψ => (top_le_iff_mem _ _ z).1 (gJ' ψ)
  have hp : (𝟙 (Sp F) : Sp F ⟶ Sp F) z ∈ LB.wchart M₀ (fun k => pt k ≫ φ) j₀ := Set.mem_iInter.2 h₀
  have hp' : (𝟙 (Sp F) : Sp F ⟶ Sp F) z ∈ LB.wchart M₀ (fun k => pt k ≫ φ) (fun k => J (𝟙 _ ≫ pt k ≫ φ)) :=
    Set.mem_iInter.2 fun k => hJ _
  have hq : (𝟙 (Sp F) : Sp F ⟶ Sp F) z ∈ LB.wchart M pt j := Set.mem_iInter.2 h₁
  have hq' : (𝟙 (Sp F) : Sp F ⟶ Sp F) z ∈ LB.wchart M pt (fun k => J' (𝟙 _ ≫ pt k)) := Set.mem_iInter.2 fun k => hJ' _
  have P1 := pw_trans ((isGen_iff w).1 hw) pt ε (𝟙 _) z hp hp' hq hq'
  have G1 := gen_trans ht (𝟙 _) z hq hq'
  have G0 := gen_trans ht₀ (𝟙 _) z hp hp'
  have a₃ : ∀ k, toStk z (valF (pt k) _ (w.s (fun _ => J (pt k ≫ φ), J' (pt k))).val) =
      (gw w (pt k) z (J (pt k ≫ φ)) (J' (pt k))).val := fun k =>
    toStk_valF (pt k) ((M₀.pull φ).U (fun _ => J (pt k ≫ φ)) ⊓ M.U (J' (pt k))) z ⟨mem_pull.2 (hJ (pt k ≫ φ)), hJ' _⟩ _
  have a₄ : toStk z (∏ k, valF (pt k) _ (w.s (fun _ => J (pt k ≫ φ), J' (pt k))).val ^ ε k) =
      (pw w pt ε (𝟙 _) z (fun k => J (𝟙 _ ≫ pt k ≫ φ)) (fun k => J' (𝟙 _ ≫ pt k))).val := by
    simp only [pw, Category.id_comp]
    rw [map_prod, Units.coe_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    have hu : valF (pt k) _ (w.s (fun _ => J (pt k ≫ φ), J' (pt k))).val ≠ 0 := fun h0 => by
      have := a₃ k
      rw [h0, map_zero] at this
      exact Units.ne_zero _ this.symm
    have e : Units.map (toStk z).toMonoidHom (Units.mk0 _ hu) = gw w (pt k) z _ _ := Units.ext (a₃ k)
    rw [← e, ← map_zpow]
    show _ = toStk z _
    rw [Units.val_zpow_eq_zpow_val, Units.val_mk0]
  have e' := congrArg (toStk z) hv
  rw [map_mul, map_mul, a₄] at e'
  have b₁ : toStk z (vF t (𝟙 _) J') = _ := toStk_valF _ _ z hq' _
  have b₀ : toStk z (vF t₀ (𝟙 _) J) = _ := toStk_valF _ _ z hp' _
  rw [b₁, b₀, ← Units.val_mul] at e'
  have hpw : (∏ k, gw w (pt k) z (j₀ k) (j k) ^ ε k) = pw w pt ε (𝟙 _) z j₀ j := by
    simp only [pw, Category.id_comp]
  have step : ∀ {U : Type} [CommGroup U] (a b c d : U), a * b⁻¹ * c * (b * d) = a * (c * d) := fun a b c d => by
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  rw [hpw, P1, G1, G0, step, Units.val_mul, e', Units.val_mul]
  exact mul_left_comm _ _ _

theorem gtφ_eq {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
    {N : NumD F} (ν : NumOf D F N) (b : N.A) (χ : N.X) (i : Fin 4) :
    DegPre.gtφ D F (ν.eA b) (ν.eX χ) i = (ν.eA (![N.c χ * b, N.c χ, b, 1] i)).left := by
  fin_cases i
  · show _ = (ν.eA (N.c χ * b)).left
    rw [map_mul, ν.c_eq]; rfl
  · show _ = (ν.eA (N.c χ)).left
    rw [ν.c_eq]; rfl
  · rfl
  · show _ = (ν.eA 1).left
    rw [map_one]; rfl

theorem level_clause : GlobalTheory.UT.LL → BrGtSt → AllS fun {_} _ _ _ {_} {D} {l} {_} {_} _ {_} {O'} _ _ {_} a {C} _ _ A u r {o} M f {_} ν' J => M.P.TorsionIso → ∀ ψ w e, Fit A u M f ν' J ψ w e → ∀ k : ℕ, 0 < k → k ∣ l.M' → Labels A u r M ν' J k → ∀ (p₀ : QkPt a.D₀ (FractionRing O') k) (v : D.La), (∀ p, QkExt (algebraMap _ C) p₀ p → QkPt.Equiv a.D₀ C p (A.I.ev k v)) → ∀ z : TFK (R := M.W) C ⟶ M.P.A.A, z.left = (o.I.ev k v).left ≫ M.φ → ∃ (q₀ : QkPt a.D₀ C k) (q : QkPt M.P.D.toPre C k), QkExt (algebraMap _ C) p₀ q₀ ∧ q.y = e q₀.y ∧ (∀ χ, GenRel w (q.g.s (e χ)) (q₀.g.s χ) ((u : C) ^ (a.be q₀.y χ / k))) ∧ M.P.ToA C k q z := by
  intro _ hBr E _ _ _ H D l c O _ β O' _ _ _ b a C _ _ _ _ _ _ A u r o M f N' ν' J hr _ hTI ψ w e hF k hk hkM hL p₀ v hp₀ z hz
  obtain ⟨-, hw, hA, hX, hne, hh⟩ := hF
  have hrk := hr.pow hk
  obtain ⟨q₀, hq₀, -⟩ := TorusExt.existsUnique_qkExt (F' := C) a.bimult (algebraMap (FractionRing O') C)
    (RingHom.ext fun _ => rfl) p₀
  obtain ⟨-, -, -, -, B₀⟩ := hBr O' a.D₀ a.even a.bimult C A.N A.ν
  obtain ⟨-, -, -, -, B₁⟩ := hBr M.W M.P.D.toPre M.P.D.psi_even M.P.D.tau_bimult C N' ν'
  obtain ⟨v₀, hv₀, -⟩ := (B₀ k).1 q₀
  have e₀ := ((B₀ k).2.2 _ _ _ _ hv₀ (A.hq k v)).1 (hp₀ q₀ hq₀)
  obtain ⟨t₀, ht₀, -⟩ := existsUnique_twRel A.be u (r k) hrk v₀
  obtain ⟨t₁, ht₁, -⟩ := existsUnique_twRel A.be u (r k) hrk (A.q k v)
  obtain ⟨s₀, hs₀, hs₀'⟩ := exists_image J t₀
  obtain ⟨s₁, hs₁, hs₁'⟩ := exists_image J t₁
  obtain ⟨q, hq⟩ := (B₁ k).2.1 s₀
  obtain ⟨p', hp'⟩ := (B₁ k).2.1 s₁
  have e₁ := ((B₁ k).2.2 _ _ _ _ hq hp').2 (qEq_image J (qEq_twist A.be hrk e₀ ht₀ ht₁) hs₀ hs₀' hs₁ hs₁')
  refine ⟨q₀, q, hq₀, ?_, fun χ => ?_, ?_⟩
  · rw [← hq.1, ← hv₀.1, hX, hs₀, ht₀.1]
    rfl
  · obtain ⟨χ, rfl⟩ := A.ν.eX.surjective χ
    have hb : q.g.b = ν'.eA (J.φ v₀.1.2.b) := by rw [← hq.2.1, hs₀'.1, ht₀.2.1]
    have hc : N'.c (J.e χ) = J.φ (A.N.c χ) := J.c_eq χ
    have g₁ : ∀ i, DegPre.gtφ M.P.D.toPre C q.g.b (e (A.ν.eX χ)) i =
        (ν'.eA (J.φ (![A.N.c χ * v₀.1.2.b, A.N.c χ, v₀.1.2.b, (1 : A.N.A)] i))).left := fun i => by
      rw [hb, hX, gtφ_eq, hc]
      fin_cases i
      · exact congrArg (fun x => (ν'.eA x).left) (map_mul J.φ _ _).symm
      · rfl
      · rfl
      · exact congrArg (fun x => (ν'.eA x).left) (map_one J.φ).symm
    refine genRel_of_gauge w hw _ (q.g.isGen _) _ (q₀.g.isGen _) _ (fun i => ?_) A.ν.J ν'.J A.ν.good ν'.good ?_
    · rw [g₁, hA, ← hv₀.2.1, gtφ_eq]
    · have g₂ : ∀ i, valF (DegPre.gtφ M.P.D.toPre C q.g.b (e (A.ν.eX χ)) i) _
          (w.s (fun _ => A.ν.J (DegPre.gtφ M.P.D.toPre C q.g.b (e (A.ν.eX χ)) i ≫ ψ),
            ν'.J (DegPre.gtφ M.P.D.toPre C q.g.b (e (A.ν.eX χ)) i))).val =
          wVal ν' A.ν w (J.φ (![A.N.c χ * v₀.1.2.b, A.N.c χ, v₀.1.2.b, (1 : A.N.A)] i)) := fun i =>
        congrArg (fun p : Sp C ⟶ M.P.D.toPre.P.A.left => valF p _ (w.s (fun _ => A.ν.J (p ≫ ψ), ν'.J p)).val) (g₁ i)
      have g₃ : vF (q.g.s (e (A.ν.eX χ))) (𝟙 (Sp C)) ν'.J = (s₀.1.2.s (J.e χ) : C) :=
        (congrArg (fun y => vF (q.g.s y) (𝟙 (Sp C)) ν'.J) (hX χ)).trans (hq.2.2 _).symm
      have g₄ := (hv₀.2.2 χ).symm
      have g₅ : (u : C) ^ (a.be q₀.y (A.ν.eX χ) / k) = (r k ^ A.be.be v₀.1.1.toAdd χ : Cˣ) := by
        rw [← hv₀.1, ← A.be_eq, ← hrk, Units.val_zpow_eq_zpow_val, Units.val_pow_eq_pow_val, ← zpow_natCast, ← zpow_mul,
          mul_comm, A.be.div_mul hkM]
      have g₆ : s₀.1.2.s (J.e χ) * J.h (A.N.c χ * v₀.1.2.b) =
          v₀.1.2.s χ * r k ^ A.be.be v₀.1.1.toAdd χ * J.h (A.N.c χ) * J.h v₀.1.2.b := by
        have := hs₀'.2 χ
        rw [ht₀.2.1, ht₀.2.2] at this
        exact this
      have g₇ := congrArg Units.val g₆
      simp only [Units.val_mul] at g₇
      refine (congrArg₂ (· * ·) (Finset.prod_congr rfl fun i _ => congrArg (· ^ _) (g₂ i)) g₃).trans
        (Eq.trans ?_ (congrArg₂ (· * ·) g₅ g₄).symm)
      rw [Fin.prod_univ_four]
      have alg : ∀ S S₀ ρ h₀ h₁ h₂ w₀ w₁ w₂ w₃ W : C, w₀ ≠ 0 → W ≠ 0 → h₀ * w₀ = W → h₁ * w₁ = W → h₂ * w₂ = W →
          w₃ = W → S * h₀ = S₀ * ρ * h₁ * h₂ →
          w₀ ^ (-1 : ℤ) * w₁ ^ (1 : ℤ) * w₂ ^ (1 : ℤ) * w₃ ^ (-1 : ℤ) * S = ρ * S₀ := by
        intro S S₀ ρ h₀ h₁ h₂ w₀ w₁ w₂ w₃ W n₀ nW a₀ a₁ a₂ a₃ a₄
        subst a₃
        simp only [zpow_neg, zpow_one]
        field_simp
        refine mul_left_cancel₀ nW ?_
        linear_combination (-(w₁ * w₂ * S)) * a₀ + (w₀ * w₁ * w₂) * a₄ + (S₀ * ρ * w₀ * h₂ * w₂) * a₁ +
          (S₀ * ρ * w₀ * w₃) * a₂
      exact alg _ _ _ _ _ _ _ _ _ _ _ (hne _) (hne 1) (hh _) (hh _) (hh _)
        (congrArg (wVal ν' A.ν w) (map_one J.φ)) g₇
  · obtain ⟨g, hg, -, hge, -⟩ := hTI C k hk
    exact (hg _ _).2 (((hg _ _).1 (hL v t₁ s₁ p' z ht₁ hs₁ hs₁' hp' hz)).trans ((hge _ _).2 e₁).symm)

end GlobalTheory.Ex.Trait.LevelClause
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LevelConditionValuedFieldTwistedUniformisationStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelCondition_valuedField_twistedUniformisation : GlobalTheory.UT.LL → BrGtSt → AllS fun {_} _ _ _ {_} {D} {l} {_} {_} _ {_} {O'} _ _ {_} a {C} _ _ A u r {o} M f {_} ν' J => M.P.TorsionIso → ∀ ψ w e, Fit A u M f ν' J ψ w e → ∀ k : ℕ, 0 < k → k ∣ l.M' → Labels A u r M ν' J k → ∀ (p₀ : QkPt a.D₀ (FractionRing O') k) (v : D.La), (∀ p, QkExt (algebraMap _ C) p₀ p → QkPt.Equiv a.D₀ C p (A.I.ev k v)) → ∀ z : TFK (R := M.W) C ⟶ M.P.A.A, z.left = (o.I.ev k v).left ≫ M.φ → ∃ (q₀ : QkPt a.D₀ C k) (q : QkPt M.P.D.toPre C k), QkExt (algebraMap _ C) p₀ q₀ ∧ q.y = e q₀.y ∧ (∀ χ, GenRel w (q.g.s (e χ)) (q₀.g.s χ) ((u : C) ^ (a.be q₀.y χ / k))) ∧ M.P.ToA C k q z := by
  first | exact @GlobalTheory.Ex.Trait.LevelClause.level_clause | exact GlobalTheory.Ex.Trait.LevelClause.level_clause | (intros; apply GlobalTheory.Ex.Trait.LevelClause.level_clause <;> assumption)
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait

noncomputable section
namespace GlobalTheory.Ex.Trait

theorem exists_odd_prime (C : Type) [NormedField C] [IsUltrametricDist C] :
    ∃ n : ℕ, n.Prime ∧ Odd n ∧ 3 ≤ n ∧ ‖(n : C)‖ = 1 := by
  by_cases h : ‖((3 : ℕ) : C)‖ = 1
  · exact ⟨3, Nat.prime_three, by decide, le_rfl, h⟩
  refine ⟨5, Nat.prime_five, by decide, by decide, ?_⟩
  by_contra h'
  have h3 := lt_of_le_of_ne (IsUltrametricDist.norm_natCast_le_one C 3) h
  have h5 := lt_of_le_of_ne (IsUltrametricDist.norm_natCast_le_one C 5) h'
  have e : (1 : C) = ((3 : ℕ) : C) + ((3 : ℕ) : C) + -((5 : ℕ) : C) := by push_cast; ring
  have := IsUltrametricDist.norm_add_le_max (((3 : ℕ) : C) + ((3 : ℕ) : C)) (-((5 : ℕ) : C))
  rw [← e, norm_one, norm_neg] at this
  have h6 := (IsUltrametricDist.norm_add_le_max ((3 : ℕ) : C) ((3 : ℕ) : C)).trans_lt (by rwa [max_self])
  exact absurd this (not_le.2 (max_lt h6 h5))

theorem admissible_base_of_complete_dvr {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (hV : GlobalTheory.LN.CDvr V) :
    AdmBase V (IsLocalRing.maximalIdeal V) :=
  haveI := hV.1
  ⟨inferInstance, inferInstance, inferInstance, hV.2.1⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem mono_j {V : ValuationSubring c.F} (Y : Model Xo c V.subtype) : Mono Y.j := by
  have : IsPreimmersion (spMap V.subtype) :=
    IsPreimmersion.of_isLocalization (R := V) (S := c.F) (nonZeroDivisors V)
  have := Y.jQ_open
  unfold Model.j
  infer_instance


set_option maxHeartbeats 1000000 in
theorem hasArcData_of_model (hV : HV) (h6 : Laws6) (hU : GlobalTheory.LN.UDvrSt) (hH : GlobalTheory.LN.HomExtSt) (hT : ThetaPtDeterminesSt)
    (hE : EndDeterminedOnTorsionSt) (hTU : ThetaUnifAV) {W₀ : ValuationSubring ℂ} (Y : Model Xo c (c.V W₀).subtype)
    {O' : Type} [CommRing O'] [IsDomain O'] [CharZero O'] {b : c.V W₀ →+* O'} {ϖ : O'}
    (a : ArcIn D l (c.V W₀).subtype O' b) (hB : GlobalTheory.LN.ArcBase O' ϖ) {C : Type} [NontriviallyNormedField C]
    [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C] [Algebra (FractionRing O') C] (A : Lift a C)
    {u : Cˣ} {r : ℕ → Cˣ} {o : Full D C} (M : Mdl o) (f : O' →+* M.W) (u₀ : M.W) (hI : A.ν.IntN)
    (hR : Realises o A.arc A.be u r) (hu₁ : ‖(u : C)‖ < 1)
    (hu : (u : C) = algebraMap (FractionRing M.W) C (algebraMap _ _ u₀)) (hf : Along f C) {χ : Sp M.W ⟶ Y.X}
    (m : SABMap M.t Y.t χ) {y : Sp (FractionRing M.W) ⟶ Xo.XF c} (hy : y ≫ Y.j = jK M.W ≫ χ)
    {φ₀ : o.P.A.left ⟶ Y.oF.t.G.left}
    (hφ : M.φ ≫ M.P.U.gen.inv.left ≫ pullback.fst M.t.G.hom (jK M.W) ≫ m.φ = φ₀ ≫ Y.m.φ)
    (hA : ∀ v, (o.I.ev l.A v).left ≫ φ₀ = (jFK (R := M.W) C ≫ y) ≫ (Y.oF.etaA v).left)
    (hM : ∀ v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
      (o.I.ev l.M v).left ≫ φ₀ = (jFK (R := M.W) C ≫ y) ≫ (Y.oF.eta v).left)
    (t₁ : RatTors M.P.D.toPre.P C 3)
    (t₂ : ∀ (B : PolAV (Sp M.W)) ψ, IsGrpPullback B.A a.D₀.P.A (spMap f) ψ → RatTors B C 3) :
    Y.HasArcData a (IsLocalRing.maximalIdeal M.W) f u₀ χ := by
  letI := H.starRing
  have hLL := hV.1
  obtain ⟨hL, hL2, hL3, hL4, hL5⟩ := hV.1
  have hGt : BrGtSt := GlobalTheory.T.torus_torsion_points_correspond_values
  have : IsNoetherianRing O' := by
    rcases hB with h | h
    · letI := h.1.toField; infer_instance
    · have := h.1; infer_instance
  have := M.cdv.1
  have := M.cdv.2.2
  have tors := GlobalTheory.T.torsionIso_of_linear_uniformisation_triple hV.1 hV.2.1 hV.2.2.1 hV.2.2.2.1 hV.2.2.2.2 E H M.W _ (admissible_base_of_complete_dvr M.cdv) M.t M.P
  obtain ⟨n, hn, hno, hn3, hn1⟩ := exists_odd_prime C
  obtain ⟨N', ν', J, hlin, hlab, DW, _, oW, φ, he, w₀, e₀, νW, hm, -, hpt, Φ, wΦ, -, hΦ, hwΦ, hΦpt, -⟩ :=
    GlobalTheory.T.lift_valuation_integral_norm hV h6 hU hH hT hE hTU E H D l Xo c W₀ Y O' b ϖ a hB C A u r o M f u₀ hI hR.1 hu₁ hu hf n hn hno hn1
      fun j => ⟨hR.2.2.1 _ (pow_pos hn.pos j), fun p hp => (hR.2.2.2 _ hno.pow p hp).2.1⟩
  obtain ⟨Ψ, hΨ, lΨ, pΨ⟩ := GlobalTheory.T.polarisedAVIso_descends_of_rational_threeTorsion hL hL2 hH M.W M.cdv C DW.P M.P.D.toPre.P (t₂ _ _ hm.1) t₁ Φ
    (νW.eA.symm.trans (J.φ.trans ν'.eA))  hΦ
    (fun x => by obtain ⟨x, rfl⟩ := νW.eA.surjective x; simpa using hΦpt x) ⟨wΦ, hwΦ⟩
  set ψ := Ψ.hom.left ≫ φ with hψ
  have gψ : IsGrpPullback M.P.D.toPre.P.A a.D₀.P.A (spMap f) ψ :=
    ((isGrpPullback_of_iso Ψ).comp hm.1).congr (Category.id_comp _) rfl
  have lψ : LBIso M.P.D.toPre.P.L (a.D₀.P.L.pull ψ) :=
    LBIso.trans M.P.D.toPre.P.isLB (pull_isLB DW.P.isLB _) (pull_isLB a.D₀.P.isLB _) lΨ
      (LBIso.chartPull (Geo.Tor.chartPullPull DW.P.L _ _ rfl)
        (chartPullSame a.D₀.P.L _ (fun _ : PUnit => φ) _ Ψ.hom.left fun _ => rfl) ⟨w₀, hm.2.1⟩)
  have pψ : ∀ x : A.N.A, (ν'.eA (J.φ x)).left ≫ ψ = (A.ν.eA x).left := fun x => by
    have e : ν'.eA (J.φ x) ≫ Ψ.hom = νW.eA x :=
      (congrArg (fun z => ν'.eA (J.φ z) ≫ Ψ.hom) (νW.eA.symm_apply_apply x)).symm.trans (pΨ (νW.eA x))
    rw [hψ, ← Category.assoc, ← Over.comp_left]
    exact (congrArg (fun z => CommaMorphism.left z ≫ φ) e).trans (hpt x)
  have heψ := GlobalTheory.PolBaseChange.eSec_comm gψ
  obtain ⟨w, hw, hrig⟩ := GlobalTheory.Unif.RigidifyIso.exists_rigidified_iso _ _ (spMap f) a.D₀.P.A M.P.D.toPre.P.A ψ heψ
    ⟨a.D₀.P.L, a.D₀.rig, a.D₀.P.isLB, a.D₀.rig_gen⟩
    ⟨M.P.D.toPre.P.L, M.P.D.toPre.rig, M.P.D.toPre.P.isLB, M.P.D.toPre.rig_gen⟩ lψ
  let e : a.D₀.X ≃ₗ[𝓞 E] M.P.D.toPre.X :=
    { A.ν.eX.symm.trans (J.e.trans ν'.eX) with
      map_smul' := fun x y => by
        obtain ⟨y, rfl⟩ := A.ν.eX.surjective y
        exact (hlin x y).trans (congrArg (fun z => x • ν'.eX (J.e z)) (A.ν.eX.symm_apply_apply y).symm) }
  have fit : Fit A u M f ν' J ψ w e :=
    ⟨gψ, hw, pψ, fun y => congrArg (fun z => ν'.eX (J.e z)) (A.ν.eX.symm_apply_apply y),
      GlobalTheory.T.isomorphismValues_cocycle_eq_bundleIso_value hL hL2 M.W O' f _ _ C hf N' A.N ν' A.ν ψ w J.toIso gψ hw pψ⟩
  have act : ∀ x, (M.P.oD.onB.act x).left ≫ ψ = ψ ≫ (a.oa.onB.act x).left := fun x => by
    refine GlobalTheory.T.polarized_abelian_pullback_line_bundle hL hE E H M.W _ _ _ _ M.P.oD.onB a.oa.onB ψ gψ lψ C n hn.two_le x fun j z hz => ?_
    obtain ⟨z, rfl⟩ := (J.φ.trans ν'.eA).surjective z
    have hz' : (z : A.N.A) ^ n ^ j = 1 := (J.φ.trans ν'.eA).injective (by rw [map_pow, map_one]; exact hz)
    have e₁ := GlobalTheory.T.valuesIso_comm_action_abelianPart_torsion hLL hGt E H D l c _ _ O' b a C A u r o M f N' ν' J hR.1 hf tors _ (pow_pos hn.pos j) (hlab j) hlin x z
      (A.ν.eA.symm (A.ν.eA z ≫ a.oa.onB.act x)) hz' (A.ν.eA.apply_symm_apply _)
    refine (congrArg (fun z => CommaMorphism.left z ≫ ψ) e₁.symm).trans ((pψ _).trans ?_)
    rw [MulEquiv.apply_symm_apply, Over.comp_left]
    exact (congrArg (· ≫ _) (pψ z).symm).trans (Category.assoc _ _ _)
  obtain ⟨s₁, s₂, s₃, s₄, s₅, s₆⟩ := GlobalTheory.T.modelIso_of_valued_agreement_over_field hLL E H D l c _ _ O' b a C A u r o M f N' ν' J hR.1 hf u₀ hu ψ heψ w e fit hrig act
  have lab := GlobalTheory.T.twistedLabels_all_levels_of_four_le hLL hGt E H D l c _ _ O' b a C A u r o M f N' ν' J hR.1 hf tors
    (GlobalTheory.T.twistedLabels_match_of_level_ge_four hLL (GlobalTheory.T.torsionCoordinates_eq_degenerationSeries hV hGt (GlobalTheory.T.families_values_correspond hL hL2)) hGt E H D l c _ _ O' b a C A u r o M f N' ν' J hR.1 hf tors
      hR n hno hn3 (hlab 2))
  refine ⟨M.t, m, M.P, ψ, heψ, w, e, s₁, s₂, s₃, s₄, s₅, fun F _ _ _ _ uF hF huF => ⟨s₆ F uF hF huF, ?_⟩⟩
  intro yF hyF k p₀ σ hσ q₀ q x h₀ hq hg hx
  have := mono_j Y
  obtain rfl : yF = jFK (R := M.W) F ≫ y := by rw [← cancel_mono Y.j, hyF, Category.assoc, hy]
  obtain ⟨hk, hkM, v, hv, hev⟩ : 0 < k ∧ k ∣ l.M' ∧ ∃ v, (∀ p, QkExt (algebraMap _ C) p₀ p → QkPt.Equiv a.D₀ C p (A.I.ev k v)) ∧
      (o.I.ev k v).left ≫ φ₀ = (jFK (R := M.W) C ≫ y) ≫ σ.left := by
    rcases hσ with ⟨rfl, v, h, rfl⟩ | ⟨rfl, v, hv, h, rfl⟩
    · obtain rfl := eq_of_heq h
      exact ⟨l.A_pos, Nat.dvd_lcm_right _ _, v, A.levA v, hA v⟩
    · obtain rfl := eq_of_heq h
      exact ⟨l.odd.pos, Nat.dvd_lcm_left _ _, v, A.levM v hv, hM v hv⟩
  have := M.P.U.gen_hom
  have gp : IsPullback (M.P.U.gen.inv.left ≫ pullback.fst M.t.G.hom (jK M.W) ≫ m.φ) M.P.A.A.hom Y.t.G.hom (jK M.W ≫ χ) := by
    have : IsMonHom M.P.U.gen.symm.hom := by show IsMonHom M.P.U.gen.inv; infer_instance
    exact (((isGrpPullback_of_iso M.P.U.gen.symm).comp ((isGrpPullback_pullback M.t.G (jK M.W)).comp m.cart)).congr
      (Category.id_comp _) rfl).1
  have hσw : (y ≫ σ.left ≫ Y.m.φ) ≫ Y.t.G.hom = 𝟙 _ ≫ jK M.W ≫ χ := by
    have e₁ : σ.left ≫ Y.oF.t.G.hom = 𝟙 _ := Over.w σ
    rw [Category.assoc, Category.assoc, Y.m.cart.1.w, reassoc_of% e₁, Category.id_comp, ← hy]; rfl
  let x₀ := gp.lift _ _ hσw
  have hx₀ : ∀ (K : Type) [Field K] [Algebra (FractionRing M.W) K] (z : Sp K ⟶ M.P.A.A.left),
      z ≫ M.P.A.A.hom = jFK (R := M.W) K → z ≫ M.P.U.gen.inv.left ≫ pullback.fst M.t.G.hom (jK M.W) ≫ m.φ =
        (jFK (R := M.W) K ≫ y) ≫ σ.left ≫ Y.m.φ → z = jFK (R := M.W) K ≫ x₀ := fun K _ _ z h₁ h₂ => by
    apply gp.hom_ext
    · rw [h₂, Category.assoc, Category.assoc (jFK (R := M.W) K), gp.lift_fst]
    · rw [h₁, Category.assoc, gp.lift_snd]; exact (Category.comp_id _).symm
  have hzw : ((o.I.ev k v).left ≫ M.φ) ≫ M.P.A.A.hom = jFK (R := M.W) C := by
    have e₁ : (o.I.ev k v).left ≫ o.P.A.hom = 𝟙 _ := Over.w _
    rw [Category.assoc, M.cart.1.w, reassoc_of% e₁]
  obtain ⟨q₁, q₂, a₁, a₂, a₃, a₄⟩ := GlobalTheory.T.levelCondition_valuedField_twistedUniformisation hLL hGt E H D l c _ _ O' b a C A u r o M f N' ν' J hR.1 hf tors ψ w e fit k hk hkM
    (lab k hk) p₀ v hv (Over.homMk ((o.I.ev k v).left ≫ M.φ) hzw) rfl
  refine GlobalTheory.T.levelCondition_of_one_algClosed_field hLL E H M.W O' _ (admissible_base_of_complete_dvr M.cdv) M.t M.P a.D₀ a.bimult f ψ w e.toAddEquiv s₁ s₂ k hk p₀
    (fun z => algebraMap M.W _ u₀ ^ (a.be p₀.y z / k)) x₀ C hf q₁ q₂ _ a₁ a₂ (fun z => ?_) ?_ a₄ F (fun x => (hF x).symm) q₀ q x
    h₀ hq (fun z => ?_) (hx₀ F _ (Over.w x) hx)
  · rw [map_zpow₀, ← hu, ← a₁.1]; exact a₃ z
  · refine hx₀ C _ hzw ?_
    change ((o.I.ev k v).left ≫ M.φ) ≫ _ = _
    rw [Category.assoc, hφ, ← Category.assoc, hev, Category.assoc]
  · rw [map_zpow₀, ← huF, ← h₀.1]; exact hg z

theorem eq_of_generic {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) {R : Type} [CommRing R] [IsDomain R]
    (C : Type) [Field C] [Algebra (FractionRing R) C] {x x' : Sp R ⟶ Y.X}
    (h : jFK (R := R) C ≫ jK R ≫ x = jFK (R := R) C ≫ jK R ≫ x') : x = x' := by
  have := projProper _ _ _ Y.proj
  have : Y.X.IsSeparated := ⟨by rw [← terminal.comp_from Y.s]; infer_instance⟩
  have : IsDominant (spMap ((algebraMap (FractionRing R) C).comp (algebraMap R _))) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (((RingHom.injective_iff_ker_eq_bot ((algebraMap (FractionRing R) C).comp (algebraMap R _))).1
      ((algebraMap (FractionRing R) C).injective.comp (IsFractionRing.injective R (FractionRing R)))).trans_le bot_le)⟩
  refine ext_of_isDominant (spMap ((algebraMap (FractionRing R) C).comp (algebraMap R _))) ?_
  rw [spMap_comp, Category.assoc, Category.assoc]
  exact h

theorem hasArcData_at_trait : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → AllA fun {E} _ _ _ {H} {D} {l} {Xo} {c} {W₀} Y {O'} _ _ {b} a => ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] (g : PowerSeries O' →+* R₁) (y₁ : Sp (FractionRing R₁) ⟶ Xo.XF c), Function.Injective g → g.Finite → IsIntegrallyClosed R₁ → RealAt Y a g y₁ → y₁ ≫ Y.j ≫ Y.s = jK R₁ ≫ spMap g ≫ spMap (PowerSeries.C (R := O')) ≫ spMap b → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R₁ →+* W) (gam : FractionRing R₁ →+* FractionRing W), (∀ r, gam (algebraMap R₁ _ r) = algebraMap W _ (φ r)) → ∀ χ : Sp W ⟶ Y.X, spMap gam ≫ y₁ ≫ Y.j = jK W ≫ χ → ¬ IsUnit (φ (g PowerSeries.X)) → ∃ (W' : Type) (_ : CommRing W') (_ : IsDomain W') (_ : IsLocalRing W') (io : W →+* W'), GlobalTheory.LN.CDvr W' ∧ Function.Injective io ∧ io.Finite ∧ Y.HasArcData a (IsLocalRing.maximalIdeal W') (io.comp (φ.comp (g.comp (PowerSeries.C (R := O'))))) (io (φ (g PowerSeries.X))) (spMap io ≫ χ) := by
  intro hV h6 hU hH hT hE hTU E _ _ _ H D l Xo c W₀ Y O' _ _ _ b ϖ a hB R₁ _ _ g y₁ hg _ _ hR hs W _ _ _ hW φ gam hgam χ hχ hu
  obtain ⟨hL, hL2, hL3, hL4, hL5⟩ := hV.1
  have := hW.1
  have := hW.2.2
  have hφ : Function.Injective φ := fun x y h => IsFractionRing.injective R₁ (FractionRing R₁) (gam.injective (by
    rw [hgam, hgam, h]))
  obtain ⟨C, _, _, _, _, _, -, -, hext⟩ := exists_complete_isAlgClosed_cExt W (FractionRing W)
  have : CharZero C := charZero_of_injective_ringHom (algebraMap (FractionRing W) C).injective
  set f₀ := φ.comp (g.comp (PowerSeries.C (R := O'))) with hf₀
  have inj₀ : Function.Injective f₀ := hφ.comp (hg.comp PowerSeries.C_injective)
  have injW : Function.Injective ((algebraMap (FractionRing W) C).comp (algebraMap W _)) :=
    (algebraMap (FractionRing W) C).injective.comp (IsFractionRing.injective W _)
  have injC : Function.Injective (((algebraMap (FractionRing W) C).comp (algebraMap W _)).comp f₀) := injW.comp inj₀
  letI : Algebra (FractionRing O') C := (IsFractionRing.lift (K := FractionRing O') injC).toAlgebra
  have al₀ : Along f₀ C := fun x => (IsFractionRing.lift_algebraMap injC x).symm
  have hu0 : algebraMap (FractionRing W) C (algebraMap W _ (φ (g PowerSeries.X))) ≠ 0 := fun h =>
    PowerSeries.X_ne_zero (hg (hφ (injW (h.trans (by simp)))))
  have hu1 := hext.2 _ ((IsLocalRing.mem_maximalIdeal _).2 hu)
  obtain ⟨A, r, o, hI, -, hF, hRe⟩ := hR.2 C ((algebraMap (FractionRing W) C).comp gam) (Units.mk0 _ hu0)
    (fun x => (al₀ x).symm.trans (congrArg _ (hgam _).symm)) (fun x => by
      rw [RingHom.comp_apply, hgam]; exact hext.1 _) (congrArg _ (hgam _).symm) hu1
  rw [spMap_comp, Category.assoc] at hF
  have sq : spMap gam ≫ jK R₁ = jK W ≫ spMap φ :=
    (spMap_comp _ gam).symm.trans ((congrArg spMap (RingHom.ext hgam)).trans (spMap_comp φ _))
  obtain ⟨M, f₁, χ₁, m₁, fin₁, al₁, hχ₁, -⟩ := GlobalTheory.T.moduli_model_ultrametric_points hV h6 hU hH hT hE hTU E H D l Xo c W₀ Y C W hW hext
    (FractionRing W) (algebraMap _ C) (fun _ => rfl) (spMap gam ≫ y₁) (f₀.comp b) (by
      have e : spMap (algebraMap (FractionRing W) (FractionRing W)) = 𝟙 _ := Spec.map_id _
      rw [e, Category.id_comp, Category.assoc, hs, reassoc_of% sq, hf₀, spMap_comp, spMap_comp, spMap_comp]
      simp only [Category.assoc]) o hF
  have inj₁ : Function.Injective f₁ := fun x y h => injW ((al₁ x).symm.trans (h ▸ al₁ y))
  obtain ⟨W₂, _, _, _, _, io, hW₂, inj₂, fin₂, loc₂, al₂, ext₂, t₁, t₂⟩ := GlobalTheory.T.exists_completeDVR_extension_torsion_rational hL M.W M.cdv C M.ext 3 (by decide)
    _ _ (𝟙 _) (spMap (f₁.comp f₀)) M.P.D.toPre.P a.D₀.P
  have := hW₂.1
  have := hW₂.2.2
  obtain ⟨t, m₀, P, ψ, gψ⟩ := GlobalTheory.T.exists_linearUniformisation_baseChange_admissible hL hL3 hL4 hL5 E H M.W W₂ _ _ (admissible_base_of_complete_dvr M.cdv) (admissible_base_of_complete_dvr hW₂) io inj₂
    (Ideal.map_le_iff_le_comap.2 fun x hx => map_nonunit io x hx) M.t M.P
  obtain ⟨m, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m₁ m₀
  have al : Along (io.comp f₁) C := fun x => (al₂ _).trans (al₁ x)
  have inj : Function.Injective ((algebraMap W₂ (FractionRing W₂)).comp (io.comp f₁)) :=
    (IsFractionRing.injective W₂ _).comp (inj₂.comp inj₁)
  let δ : FractionRing W →+* FractionRing W₂ := IsFractionRing.lift inj
  have hδ : ∀ x, δ (algebraMap W _ x) = algebraMap W₂ _ (io (f₁ x)) := IsFractionRing.lift_algebraMap inj
  have sq₂ : spMap δ ≫ jK W = jK W₂ ≫ spMap (io.comp f₁) :=
    (spMap_comp _ δ).symm.trans ((congrArg spMap (RingHom.ext hδ)).trans (spMap_comp _ _))
  have jδ : jFK (R := W₂) C ≫ spMap δ = spMap (algebraMap (FractionRing W) C) :=
    (spMap_comp δ _).symm.trans (congrArg spMap (IsLocalization.ringHom_ext (nonZeroDivisors W) (RingHom.ext fun x =>
      (congrArg (algebraMap (FractionRing W₂) C) (hδ x)).trans (al x))))
  have jio : jFK (R := W₂) C ≫ jK W₂ ≫ spMap io = jFK (R := M.W) C ≫ jK M.W :=
    ((congrArg (_ ≫ ·) (spMap_comp _ _).symm).trans (spMap_comp _ _).symm).trans
      ((congrArg spMap (RingHom.ext fun x => al₂ x)).trans (spMap_comp _ _))
  have hy : (spMap δ ≫ spMap gam ≫ y₁) ≫ Y.j = jK W₂ ≫ spMap (io.comp f₁) ≫ χ := by
    rw [Category.assoc, Category.assoc, hχ, reassoc_of% sq₂]
  have eχ : spMap io ≫ χ₁ = spMap (io.comp f₁) ≫ χ := by
    refine eq_of_generic Y C ?_
    rw [← hy, reassoc_of% jio, hχ₁, Category.assoc (spMap δ), reassoc_of% jδ]
  obtain ⟨φ₀, g₀, l₀, a₀, hA, hM, -⟩ := hF
  have ey : spMap (algebraMap (FractionRing W) C) ≫ spMap gam ≫ y₁ = jFK (R := W₂) C ≫ spMap δ ≫ spMap gam ≫ y₁ := by
    rw [reassoc_of% jδ]
  rw [ey] at g₀ hA hM
  rw [← eχ] at hy
  obtain ⟨φ₂, g₂, l₂, a₂, e₂⟩ := GlobalTheory.T.family_fibre_eq_uniformised_pullback_generic_fibre E H D l Xo c _ _ Y W₂ _ t _ m P C _ (by rw [Category.assoc, hy]) o φ₀ g₀ l₀ a₀
  let M₂ : Mdl o := ⟨W₂, hW₂, ext₂, t, P, φ₂, g₂, l₂, a₂⟩
  refine ⟨W₂, _, _, _, io.comp f₁, hW₂, inj₂.comp inj₁, fin₂.comp fin₁, ?_⟩
  rw [← eχ]
  exact hasArcData_of_model hV h6 hU hH hT hE hTU Y a hB A M₂ ((io.comp f₁).comp f₀) _ hI hRe hu1 (al _).symm
    (fun x => (al _).trans (al₀ x)) m hy e₂ hA hM (t₁ _ ψ (gψ.congr (Category.comp_id _).symm rfl))
    fun B ψ' h => t₂ B ψ' (h.congr (spMap_comp (f₁.comp f₀) io) rfl)

end GlobalTheory.Ex.Trait
end
