module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHasCls
public import Development.AbelianVarietyTheory.Definitions.Divisors.OfCore
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups
public import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.FormalDegreeUpperC
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.MainNotions Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows

namespace GlobalTheory.LowRow

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

def AdelC (F : Face D A) : Prop :=
  GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (b : ℝ), Sizes D i b → ∀ t : T, PrimeToHost R t →
  ∀ (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ), IsEmbOverK D σ s →
  ∀ P : LevelP R.Pg D.R.r ℂ, IsLocalLevel P →
  ∀ (cμ cη : (AE D)ˣ →* Circle) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ), IsConjChars R i t s cμ cη m →
  ∀ ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (Datum.WO (Vc D i) (Wc D i) → ℂ),
    Datum.IsWeilDatumO R.ψ (Vc D i) (Wc D i) cμ (cμ * cη⁻¹) ω →
  ∀ BW : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ,
    (∀ ρ, Datum.IsONBasis (gramAt D (Wc D i) ρ) (cart (R.MW i σ) ρ) (BW ρ) (pW D i ρ)) →
  ∀ f₀ f : Datum.WO (Vc D i) (Wc D i) → ℂ,
    IsLevelVec R.ψ R.θ (Vc D i) (Wc D i) (cart (R.MW i σ)) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i) (R.datWp i P) (R.Q t) m f₀ f →
    Lift.PtTheta R.ψ (Vc D i) (Wc D i) (ptAt R i σ BW f) →
  ∀ c : CoefA (Vc D i), c.Is →
  ∀ io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank,
    IsIoW R.θ (R.MW i σ) c ω (ptAt R i σ BW f) (deltaAtEmb D i σ) io →
  ∀ (ν : Measure (GA D (Vc D i))) (𝓕 : Set (GA D (Vc D i))),
    IsMeasDef (Vc D i) (lev D.sp.cm (Vc D i).gram (R.βV i) (datV i R.Pg (R.Q t) P m)) ν 𝓕 →
  ∀ (I : Type) [Fintype I] (y : I → Bridge.Gf (Vc D i)),
    Bridge.IsReps (Bridge.ratF (Vc D i)) (grpOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q t) P m)) y →
  ∀ HV : HMod (Bridge.Gf (Vc D i) → c.W),
    HV.Is (Bridge.AdForms (Bridge.ratF (Vc D i)) c.coef.ρ (grpOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q t) P m))
        (chrOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q t) P m)))
      (Bridge.adInner (Bridge.ratF (Vc D i)) (grpOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q t) P m)) y) →
    (∃ th, IsLift R i σ ω (ptAt R i σ BW f) c io ν 𝓕 HV th) ∧
    ∀ th, IsLift R i σ ω (ptAt R i σ BW f) c io ν 𝓕 HV th →
      ∀ ev : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ, typePart R i σ t P ev ≠ ⊥ →
        ∃ l : ℝ, 0 < l ∧ (∀ x ∈ typePart R i σ t P ev, th (adjLev P th x) = (l : ℂ) • x) ∧
          mainTerm D i σ - 8 * (D.R.f : ℝ) * (D.R.nV : ℝ) ^ 2 * Lp D b ≤ Real.log l

def LiftIsCuspC (F : Face D A) : Prop :=
  ForLiftDataC R F fun i t σ P m ω BW f c io =>
    ∀ (ν : Measure (GA D (Vc D i))) (𝓕 : Set (GA D (Vc D i))), IsMeasDef (Vc D i) (levV R i t P m) ν 𝓕 →
    ∀ φ ∈ Bridge.AdForms (Bridge.ratF (Vc D i)) c.coef.ρ (grpOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q t) P m))
        (chrOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q t) P m)),
      ∃ U ∈ R.Wall i σ, ∀ (v : ∀ ρ, lowT (R.MW i σ) ρ) (g : GA D (Wc D i)), U (fun ρ => v ρ) g =
        Lift.thetaPInt ν 𝓕 (fun g h f => Datum.thetaKO ω h g f) (ptAt R i σ BW f) io (c.ext φ) (PiTensorProduct.tprod ℂ v) g


open Datum in
def FiniteZetaC (F : Face D A) : Prop :=
  ForLiftDataC R F fun i t σ P _ ω _ f _ _ =>
    ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓧 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓧 →
    ∀ ev : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ, typePart R i σ t P ev ≠ ⊥ →
      ∃ x : HeightOneSpectrum (𝓞 D.host.E) → Fin D.R.r → ℂ,
        (∀ w a, ‖x w a‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (((D.R.r : ℝ) - 1) / 2 - (1 + (D.R.t : ℝ)) / 2)) ∧
        ∀ U₁ ∈ partFull R.θ (R.MW i σ) (levS _ (R.βW i) (R.datWp i P)) (Lev.levChi _ (R.βW i) (R.datWp i P)) (finS R t) ev,
        ∀ U₂ ∈ R.Wall i σ, ∀ v₁ v₂ : (R.MW i σ).Vec,
          HasSum (fun y : FinCos (Wc D i) (levW R i) =>
              l2 μ 𝓧 (ω (1, y.rep) f) f * starRingEnd ℂ (petW R i (rTr (Wc D i) y.rep (U₁ v₁)) (U₂ v₂)))
            ((Nat.card P.H : ℂ) * (nrm2 μ 𝓧 f : ℂ) * (eulerOff D (finS R t) x / (dOff D (finS R t) : ℂ)) *
              starRingEnd ℂ (petW R i (U₁ v₁) (U₂ v₂)))

def FormalDegreeUpperC (F : Face D A) : Prop :=
  ForLiftDataC R F fun i _ σ _ _ _ _ _ _ _ =>
    ∀ Fr : Frames (Wc D i), IsFrames (Wc D i) Fr → ∀ (ρ : D.what₂.Tau) (mR : Measure (Upq (Wc D i) ρ)), Lev.IsMinf mR →
    ∀ e : lowT (R.MW i σ) ρ, ‖((e : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)‖ = 1 →
      let k : Upq (Wc D i) ρ → ℝ := fun b => ‖⟪((e : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ),
        (R.MW i σ).rep ρ (realMat (Wc D i) Fr ρ b) ((e : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)⟫_ℂ‖ ^ 2
      Integrable k mR ∧ 0 < ∫ b, k b ∂mR ∧
        Real.log (∫ b, k b ∂mR)⁻¹ ≤
          2 + (D.R.r : ℝ) ^ 2 * Real.log (2 * Real.sqrt 2 * (D.R.r : ℝ) ^ 2 * D.R.nV * ((degAt D i σ ρ : ℝ) + 2))

def GalOut (i : Fin D.R.m) (ph : ℂ) : Prop :=
    (∀ x, ∃! y, GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsRatLift R i ph x y) ∧
    (∀ gramR c0R c0L,
      Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ)
        (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L →
      ∀ σ, GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK σ → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.ConjAt R i σ ph (c0L i)) ∧
    ∀ σ, ¬ GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK σ → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK ((starRingEnd ℂ).comp σ) ∧
      ∀ y y', ⟪(R.FW i).j σ y, (R.FW i).j σ y'⟫_ℂ =
        starRingEnd ℂ ⟪(R.FW i).j ((starRingEnd ℂ).comp σ) y, (R.FW i).j ((starRingEnd ℂ).comp σ) y'⟫_ℂ

def StdV (D : D7) : Prop := ∀ i : Fin D.R.m, (∀ a b, (Vc D i).hT ((Vc D i).frame a) ((Vc D i).frame b) = if a = b then 1 else 0) ∧
    (Vc D i).L0 = Submodule.span (𝓞 D.host.E) (Set.range (Vc D i).frame)

end

def ConjRatLift5 : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
    (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : ℂ),
    GlobalTheory.Core5 R F → IsStdChar D R.ψ (-1) → ∀ fw : FWTie T R κ v₀, BarTie fw → IoExt R → R.LUnif → (∀ i, OMPins T R κ v₀ O i) →
    ∀ i : Fin D.R.m, (O i).OneMapOf (κ i) (v₀ i (sg0 D A)) (T.cE ((i : ℕ) + 1) (O i).s0) ph →
     GalOut R i ph

end GlobalTheory.LowRow

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.QCoh

namespace GlobalTheory.FlagPush

def IsPull {Z W : Scheme.{0}} [IsIntegral Z] [IsIntegral W] (q : Z ⟶ W) [IsDominant q] (D : CartierDiv Z)
    (E : CartierDiv W) : Prop :=
  ∀ y b, E.IsEqn y b → ∀ x, q x = y → D.IsEqn x (Units.map (functionFieldMap q).toMonoidHom b)

variable {F : Type} [Field F]

structure Dbl (Y : Var F) where

  Z : Scheme.{0}
  [integral : IsIntegral Z]

  p₁ : Z ⟶ Y.X

  p₂ : Z ⟶ Y.X

  δ : Y.X ⟶ Z
  str_eq : p₁ ≫ Y.str = p₂ ≫ Y.str
  proj : IsProjOver (p₁ ≫ Y.str)
  closed : IsClosedImmersion δ
  δ₁ : δ ≫ p₁ = 𝟙 _
  δ₂ : δ ≫ p₂ = 𝟙 _
  diag : ∀ (K : Type) [Field K] (w : Sp K ⟶ Z), w ≫ p₁ = w ≫ p₂ → w (IsLocalRing.closedPoint K) ∈ Set.range δ

attribute [instance] Dbl.integral Dbl.closed

theorem isDominant_of_section {Z W : Scheme.{0}} {p : Z ⟶ W} {s : W ⟶ Z} (h : s ≫ p = 𝟙 _) : IsDominant p :=
  ⟨Function.Surjective.denseRange fun y => ⟨s y, by rw [← Scheme.Hom.comp_apply, h]; rfl⟩⟩

namespace Dbl

variable {Y : Var F} (W : Dbl Y)

instance : IsDominant W.p₁ := isDominant_of_section W.δ₁

instance : IsDominant W.p₂ := isDominant_of_section W.δ₂

def α₁ : Y.Fn →+* W.Z.functionField := functionFieldMap W.p₁

def α₂ : Y.Fn →+* W.Z.functionField := functionFieldMap W.p₂

def num {n : ℕ} (y : Fin n → CartierDiv W.Z) : ℤ :=
  letI := algebraΓOfHom (W.p₁ ≫ Y.str)
  interNum F (structureModule W.Z) fun i => toLB (y i)

def Small : Prop := topologicalKrullDim W.Z ≤ (Y.dim + 1 : ℕ)

def triv (Y : Var F) : Dbl Y where
  Z := Y.X
  p₁ := 𝟙 _
  p₂ := 𝟙 _
  δ := 𝟙 _
  str_eq := rfl
  proj := by rw [Category.id_comp]; exact Y.isProjOver
  closed := inferInstance
  δ₁ := Category.id_comp _
  δ₂ := Category.id_comp _
  diag _ _ _ _ := ⟨_, rfl⟩

end Dbl

section Square

open CategoryTheory.Limits

def Dbl.prod (Y : Var F) : Dbl Y where
  Z := pullback Y.str Y.str
  integral := by
    have : IsLocallyNoetherian Y.X := LocallyOfFiniteType.isLocallyNoetherian Y.str
    exact GeometricallyIntegral.isIntegral_of_isLocallyNoetherian (pullback.fst Y.str Y.str)
  p₁ := pullback.fst _ _
  p₂ := pullback.snd _ _
  δ := pullback.diagonal Y.str
  str_eq := pullback.condition
  proj := ProjSpace.isProjOver_pullback Y.isProjOver Y.isProjOver
  closed := inferInstance
  δ₁ := pullback.diagonal_fst _
  δ₂ := pullback.diagonal_snd _
  diag K _ w h := ⟨(w ≫ pullback.fst _ _) (IsLocalRing.closedPoint K), by
    have e : (w ≫ pullback.fst _ _) ≫ pullback.diagonal Y.str = w := by
      apply pullback.hom_ext <;> simp [h]
    exact (Scheme.Hom.comp_apply _ _ _).symm.trans
      (congrArg (fun u : Sp K ⟶ _ => u (IsLocalRing.closedPoint K)) e)⟩

theorem Dbl.prod_dim (Y : Var F) : topologicalKrullDim (Dbl.prod Y).Z = (Y.dim + Y.dim : ℕ) := by
  have h1 := smoothOfRelativeDimension_isStableUnderBaseChange.{0} Y.dim
  have : SmoothOfRelativeDimension Y.dim (pullback.fst Y.str Y.str) :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension Y.dim)
      (IsPullback.of_hasPullback Y.str Y.str).flip Y.smooth
  have : SmoothOfRelativeDimension (Y.dim + Y.dim) (pullback.fst Y.str Y.str ≫ Y.str) := inferInstance
  have := SmoothOfRelativeDimension.smooth Y.dim (pullback.fst Y.str Y.str)
  have : GeometricallyConnected (pullback.fst Y.str Y.str ≫ Y.str) := GeometricallyConnected.comp _ _
  obtain ⟨V, e, hd, -⟩ := Var.exists_iso (pullback.fst Y.str Y.str ≫ Y.str) (Y.dim + Y.dim) (Dbl.prod Y).proj
  rw [← hd, ← V.topologicalKrullDim_eq]
  exact IsHomeomorph.topologicalKrullDim_eq _ e.hom.homeomorph.isHomeomorph

theorem Dbl.prod_small (Y : Var F) (h : Y.dim ≤ 1) : (Dbl.prod Y).Small := by
  unfold Dbl.Small
  rw [Dbl.prod_dim]
  exact_mod_cast (by omega : Y.dim + Y.dim ≤ Y.dim + 1)

theorem Dbl.prod_ne (Y : Var F) (h : 0 < Y.dim) : (Dbl.prod Y).p₁ ≠ (Dbl.prod Y).p₂ := fun e => by
  have e' : pullback.fst Y.str Y.str = pullback.snd Y.str Y.str := e
  let i : pullback Y.str Y.str ≅ Y.X := ⟨pullback.fst _ _, pullback.diagonal Y.str,
    by apply pullback.hom_ext <;> simp [← e'], pullback.diagonal_fst _⟩
  have h2 := (IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso i).isHomeomorph).trans Y.topologicalKrullDim_eq
  have h3 := (Dbl.prod_dim Y).symm.trans h2
  have : Y.dim + Y.dim = Y.dim := by exact_mod_cast h3
  omega

end Square

def GenPair (Y : Var F) {K : Type} [Field K] (ψ₁ ψ₂ : Y.Fn →+* K) : Prop :=
  ψ₁.comp (algebraMap F Y.Fn) = ψ₂.comp (algebraMap F Y.Fn) ∧
    ∃ (V : ValuationSubring K) (v₁ v₂ : Sp V ⟶ Y.X), spMap (algebraMap V K) ≫ v₁ = spMap ψ₁ ≫ (ratOf Y).pt ∧
      spMap (algebraMap V K) ≫ v₂ = spMap ψ₂ ≫ (ratOf Y).pt ∧
      spMap (IsLocalRing.residue V) ≫ v₁ = spMap (IsLocalRing.residue V) ≫ v₂ ∧
      v₁ (IsLocalRing.closedPoint V) = genericPoint Y.X

variable {ι : Type} {m : ι → ℕ}

def AlmostLow (τ : ι) (a b : Fin (m τ)) {K : Type} [Field K] (C : Mat m K) : Prop :=
  (∀ σ, (C σ).det ≠ 0) ∧ C τ a b ≠ 0 ∧
    ∀ σ (i j : Fin (m σ)), i < j → ¬ ((⟨σ, i⟩ : Root m) = ⟨τ, a⟩ ∧ (⟨σ, j⟩ : Root m) = ⟨τ, b⟩) → C σ i j = 0


open Classical in
def shear (τ : ι) (a b : Fin (m τ)) {K : Type} [CommRing K] (t : K) : Mat m K := fun σ =>
  1 + Matrix.of fun i j => if (⟨σ, i⟩ : Root m) = ⟨τ, a⟩ ∧ (⟨σ, j⟩ : Root m) = ⟨τ, b⟩ then t else 0

def minor (τ : ι) (a b : Fin (m τ)) {K : Type} [CommRing K] (C : Mat m K) : K :=
  C τ a a * C τ b b - C τ a b * C τ b a

end GlobalTheory.FlagPush
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.CompEqOneIffPush
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (RingAct)
open scoped CategoryTheory.Obj NumberField
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IwLevel

variable {S S' : Scheme.{0}} {O : Type} [Ring O]

section Basic

variable {A A' A'' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] [GrpObj A'']
  [IsCommMonObj A'']

structure IsLin (ρ : RingAct A O) (ρ' : RingAct A' O) (f : A ⟶ A') : Prop where
  hom : IsMonHom f
  comm : ∀ a, ρ.act a ≫ f = f ≫ ρ'.act a

structure IsIsogDeg (f : A ⟶ A') (d : ℕ) : Prop where
  fin : IsFinite f.left
  flat : Flat f.left
  surj : Surjective f.left
  rank : ∀ y, f.left.finrank y = d

def KilledBy (ρ : RingAct A O) (𝔴 : Ideal O) {T : Over S} (x : T ⟶ A) : Prop :=
  ∀ a ∈ 𝔴, x ≫ ρ.act a = 1


omit [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] in
theorem IsIsogDeg.of_isIso (f : A ⟶ A') [IsIso f] : IsIsogDeg f 1 := by
  have : IsIso f.left := inferInstanceAs (IsIso ((Over.forget S).map f))
  exact ⟨inferInstance, inferInstance, inferInstance, congrFun (Scheme.Hom.finrank_eq_one_of_isIso _)⟩


omit [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] [GrpObj A''] [IsCommMonObj A''] in
theorem IsIsogDeg.comp {f : A ⟶ A'} {g : A' ⟶ A''} {d e : ℕ} (hf : IsIsogDeg f d) (hg : IsIsogDeg g e) :
    IsIsogDeg (f ≫ g) (d * e) := by
  have := hf.fin; have := hf.flat; have := hf.surj
  have := hg.fin; have := hg.flat; have := hg.surj
  refine ⟨?_, ?_, ?_, fun y => ?_⟩
  · rw [Over.comp_left]; infer_instance
  · rw [Over.comp_left]; infer_instance
  · rw [Over.comp_left]; infer_instance
  · rw [Over.comp_left, FinrankComp.finrank_comp_of_const _ _ d hf.rank, hg.rank]



omit [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] in
theorem IsIsogDeg.of_isPullback {C C' : Over S'} {f : A ⟶ A'} {g : C ⟶ C'} {d : ℕ} (hf : IsIsogDeg f d)
    {u : C.left ⟶ A.left} {v : C'.left ⟶ A'.left} (H : IsPullback u g.left f.left v) : IsIsogDeg g d := by
  have := hf.fin; have := hf.flat
  exact ⟨MorphismProperty.of_isPullback (P := @IsFinite) H hf.fin,
    MorphismProperty.of_isPullback (P := @Flat) H hf.flat,
    MorphismProperty.of_isPullback (P := @Surjective) H hf.surj,
    fun y => (Scheme.Hom.finrank_of_isPullback _ _ _ _ H y).trans (hf.rank _)⟩

abbrev ker (f : A ⟶ A') : Over S := pullback f η[A']


omit [GrpObj A] [IsCommMonObj A] [IsCommMonObj A'] in
theorem IsIsogDeg.ker {f : A ⟶ A'} {d : ℕ} (hf : IsIsogDeg f d) : IsIsogDeg (toUnit (ker f)) d := by
  rw [toUnit_unique (toUnit _) (pullback.snd f η[A'])]
  exact hf.of_isPullback ((IsPullback.of_hasPullback f η[A']).map (Over.forget S))

theorem killedBy_span (ρ : RingAct A O) (s : Set O) {T : Over S} (x : T ⟶ A) :
    KilledBy ρ (Ideal.span s) x ↔ ∀ a ∈ s, x ≫ ρ.act a = 1 := by
  refine ⟨fun h a ha => h a (Ideal.subset_span ha), fun h a ha => ?_⟩
  have hadd : ∀ a b, x ≫ ρ.act (a + b) = (x ≫ ρ.act a) * (x ≫ ρ.act b) := fun a b => by
    rw [ρ.map_add]; exact MonObj.comp_mul x _ _
  induction ha using Submodule.span_induction with
  | mem a ha => exact h a ha
  | zero =>
    have := hadd 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  | add a b _ _ ha hb => rw [hadd, ha, hb, _root_.mul_one]
  | smul c a _ ha =>
    have := ρ.hom c
    rw [smul_eq_mul, ρ.map_mul, ← Category.assoc, ha, MonObj.one_comp]

theorem comp_eq_one_iff_push {C C' : Over S'} [GrpObj C] [GrpObj C'] {f : S' ⟶ S} {u : C.left ⟶ A.left}
    {v : C'.left ⟶ A'.left} (hu : IsGrpPullback C A f u) (hv : IsGrpPullback C' A' f v) {g : A ⟶ A'} {g' : C ⟶ C'}
    (hg : g'.left ≫ v = u ≫ g.left) {T : Over S'} (x : T ⟶ C) :
    x ≫ g' = 1 ↔ pushHom hu T x ≫ g = 1 := by
  have e : pushHom hv T (x ≫ g') = pushHom hu T x ≫ g := Over.OverMorphism.ext (by
    change (x.left ≫ g'.left) ≫ v = (x.left ≫ u) ≫ g.left
    rw [Category.assoc, hg, Category.assoc])
  have inj : Function.Injective (pushHom hv T) := fun y z h => Over.OverMorphism.ext
    (hv.1.hom_ext (congrArg (fun q => q.left) h) (by rw [Over.w, Over.w]))
  rw [← e, map_eq_one_iff _ inj]

end Basic

variable {A : Over S} [GrpObj A] [IsCommMonObj A]

structure Chain (ρ : RingAct A O) (𝔴 : Ideal O) (d n : ℕ) where

  B : Fin (n + 1) → Over S
  [grp : ∀ i, GrpObj (B i)]
  [comm : ∀ i, IsCommMonObj (B i)]
  ab : ∀ i, IsAbelianScheme (B i)

  act : ∀ i, RingAct (B i) O

  φ : ∀ i : Fin n, B i.castSucc ⟶ B i.succ
  φ_lin : ∀ i, IsLin (act _) (act _) (φ i)
  φ_deg : ∀ i, IsIsogDeg (φ i) d

  π : ∀ i, A ⟶ B i
  π_zero_lin : IsLin ρ (act 0) (π 0)
  π_zero_iso : IsIso (π 0)
  π_succ : ∀ i : Fin n, π i.succ = π i.castSucc ≫ φ i
  ker_last : ∀ (T : Over S) (x : T ⟶ A), x ≫ π (Fin.last n) = 1 ↔ KilledBy ρ 𝔴 x

attribute [instance] Chain.grp Chain.comm

namespace Chain

variable {ρ : RingAct A O} {𝔴 : Ideal O} {d n : ℕ} (C : Chain ρ 𝔴 d n)

end Chain

structure ChainMap {A' : Over S'} [GrpObj A'] [IsCommMonObj A'] {ρ' : RingAct A' O} {ρ : RingAct A O}
    {𝔴 : Ideal O} {d n : ℕ} (C' : Chain ρ' 𝔴 d n) (C : Chain ρ 𝔴 d n) (f : S' ⟶ S) (u : A'.left ⟶ A.left) where

  ψ : ∀ i, (C'.B i).left ⟶ (C.B i).left
  cart : ∀ i, IsGrpPullback (C'.B i) (C.B i) f (ψ i)
  act : ∀ i a, ((C'.act i).act a).left ≫ ψ i = ψ i ≫ ((C.act i).act a).left
  π_comm : ∀ i, (C'.π i).left ≫ ψ i = u ≫ (C.π i).left

namespace ChainMap

variable {A' : Over S'} [GrpObj A'] [IsCommMonObj A'] {ρ' : RingAct A' O} {ρ : RingAct A O}
  {𝔴 : Ideal O} {d n : ℕ} {C' : Chain ρ' 𝔴 d n} {C : Chain ρ 𝔴 d n} {f : S' ⟶ S} {u : A'.left ⟶ A.left}

end ChainMap

section Unitary

variable {F : Type} [Field F] [NumberField F] [NumberField.IsCMField F] {D : UPel.Datum F} {p N : ℕ}

end Unitary

end GlobalTheory.IwLevel
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.ReadsOnlyOmegaFree
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.OnCmp

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)

open Classical

theorem rank_W_le_V : (Wc D i).rank ≤ (Vc D i).rank :=
  (D.sp.W_rank _ (Nat.le_add_left _ _) i.2).le.trans (r_le_V i)

theorem readsOnly_omegaFree (Q : Finset (Pl D.host.E)) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (y₀ : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP)) :
    ReadsOnly (R.Pg ∪ Q) (omegaFree R i Q ξR y₀) := by
  intro y y' h
  have hg : ∀ PP ∈ R.Pg, y PP = y' PP := fun PP hp => h PP (Finset.mem_union_left _ hp)
  have hq : ∀ PP ∈ Q, y PP = y' PP := fun PP hp => h PP (Finset.mem_union_right _ hp)
  unfold omegaFree
  congr 1
  · exact if_congr ⟨fun H PP hp => (hg PP hp) ▸ H PP hp, fun H PP hp => (hg PP hp).symm ▸ H PP hp⟩ rfl rfl
  · by_cases H : ∀ PP ∈ Q, IsUnit (topL (Wc D i).rank (y PP)).det
    · have H' : ∀ PP ∈ Q, IsUnit (topL (Wc D i).rank (y' PP)).det := fun PP hp => (hq PP hp) ▸ H PP hp
      rw [dite_eq_left H, dite_eq_left H']
      refine Finset.prod_congr rfl fun PP _ => ?_
      have : (H PP.1 PP.2).unit = (H' PP.1 PP.2).unit := by
        ext; simp [hq PP.1 PP.2]
      rw [this]
    · have H' : ¬ ∀ PP ∈ Q, IsUnit (topL (Wc D i).rank (y' PP)).det := fun H' =>
        H fun PP hp => (hq PP hp).symm ▸ H' PP hp
      rw [dite_eq_right H, dite_eq_right H']

end GlobalTheory.OnCmp

end
end
