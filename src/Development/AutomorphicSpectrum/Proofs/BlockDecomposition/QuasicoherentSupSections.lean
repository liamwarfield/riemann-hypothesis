module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowSubSuccLe
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZOpSmooth
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.CalcSteps
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DominantElementsGlValued

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuasicoherentSupSections
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuasicoherentSupSections
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE.SupSecs

variable {X : Scheme.{0}} {E : X.Modules}

def sumMap (S T : Subobject E) : (S : X.Modules) ⊞ (T : X.Modules) ⟶ E :=
  biprod.desc S.arrow T.arrow

theorem sup_eq_imageSubobject (S T : Subobject E) : S ⊔ T = imageSubobject (sumMap S T) := by
  apply le_antisymm
  · refine sup_le ?_ ?_
    · exact Subobject.le_of_comm (biprod.inl ≫ factorThruImageSubobject (sumMap S T))
        (by rw [Category.assoc, imageSubobject_arrow_comp, sumMap, biprod.inl_desc])
    · exact Subobject.le_of_comm (biprod.inr ≫ factorThruImageSubobject (sumMap S T))
        (by rw [Category.assoc, imageSubobject_arrow_comp, sumMap, biprod.inr_desc])
  · refine imageSubobject_le (sumMap S T)
      (biprod.desc (Subobject.ofLE S (S ⊔ T) le_sup_left)
        (Subobject.ofLE T (S ⊔ T) le_sup_right)) ?_
    apply biprod.hom_ext' <;> simp [sumMap]

theorem sumMap_app (S T : Subobject E) (V : X.Opens)
    (x : Γ((S : X.Modules) ⊞ (T : X.Modules), V)) :
    (sumMap S T).app V x =
      S.arrow.app V ((biprod.fst : (S : X.Modules) ⊞ (T : X.Modules) ⟶ _).app V x) +
        T.arrow.app V ((biprod.snd : (S : X.Modules) ⊞ (T : X.Modules) ⟶ _).app V x) := by
  have h : sumMap S T = biprod.fst ≫ S.arrow + biprod.snd ≫ T.arrow := by
    apply biprod.hom_ext' <;> simp [sumMap, Preadditive.comp_add]
  rw [h]
  rfl

theorem sumMap_app_add (S T : Subobject E) (V : X.Opens) (s : Γ((S : X.Modules), V))
    (t : Γ((T : X.Modules), V)) :
    (sumMap S T).app V
        ((biprod.inl : _ ⟶ (S : X.Modules) ⊞ (T : X.Modules)).app V s +
          (biprod.inr : _ ⟶ (S : X.Modules) ⊞ (T : X.Modules)).app V t) =
      S.arrow.app V s + T.arrow.app V t := by
  have hs : biprod.inl ≫ sumMap S T = S.arrow := by simp [sumMap]
  have ht : biprod.inr ≫ sumMap S T = T.arrow := by simp [sumMap]
  rw [map_add (f := _), GlobalTheory.QCoh.app_app, GlobalTheory.QCoh.app_app, hs, ht]

end GlobalTheory.CompanionTheory.GE.SupSecs

namespace GlobalTheory.CompanionTheory.GE


open SupSecs in
theorem supsecs {X : Scheme.{0}} {E : X.Modules} (hE : E.IsQuasicoherent) (S T : Subobject E)
    (hS : (S : X.Modules).IsQuasicoherent) (hT : (T : X.Modules).IsQuasicoherent) :
    ((S ⊔ T : Subobject E) : X.Modules).IsQuasicoherent ∧
      ∀ V : X.Opens, IsAffineOpen V →
        secs (S ⊔ T) V = {x | ∃ s ∈ secs S V, ∃ t ∈ secs T V, x = s + t} := by
  rw [SupSecs.sup_eq_imageSubobject]
  refine ⟨GlobalTheory.QCoh.isQuasicoherent_of_iso (imageSubobjectIso (SupSecs.sumMap S T)).symm, fun V hV ↦ ?_⟩
  have hr : secs (imageSubobject (SupSecs.sumMap S T)) V = Set.range ((SupSecs.sumMap S T).app V) := by
    have harrow : (imageSubobject (SupSecs.sumMap S T)).arrow =
        (imageSubobjectIso (SupSecs.sumMap S T)).hom ≫ image.ι (SupSecs.sumMap S T) :=
      (imageSubobject_arrow (SupSecs.sumMap S T)).symm
    ext y
    constructor
    · rintro ⟨a, rfl⟩
      obtain ⟨b, hb⟩ := GlobalTheory.QCoh.surjective_factorThruImage_app (SupSecs.sumMap S T) hV
        ((imageSubobjectIso (SupSecs.sumMap S T)).hom.app V a)
      refine ⟨b, ?_⟩
      rw [harrow, ← GlobalTheory.QCoh.app_app, ← hb, GlobalTheory.QCoh.app_app, image.fac]
    · rintro ⟨b, rfl⟩
      refine ⟨(factorThruImageSubobject (SupSecs.sumMap S T)).app V b, ?_⟩
      rw [GlobalTheory.QCoh.app_app, imageSubobject_arrow_comp]
  rw [hr]
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨_, ⟨_, rfl⟩, _, ⟨_, rfl⟩, SupSecs.sumMap_app S T V y⟩
  · rintro ⟨_, ⟨s, rfl⟩, _, ⟨t, rfl⟩, rfl⟩
    exact ⟨_, SupSecs.sumMap_app_add S T V s t⟩

end GlobalTheory.CompanionTheory.GE
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuasicoherentSupSectionsStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasicoherent_sup_sections : ∀ {X : Scheme.{0}} {E : X.Modules}, E.IsQuasicoherent → ∀ (S T : Subobject E), (S : X.Modules).IsQuasicoherent → (T : X.Modules).IsQuasicoherent → ((S ⊔ T : Subobject E) : X.Modules).IsQuasicoherent ∧ ∀ V : X.Opens, IsAffineOpen V → secs (S ⊔ T) V = {x | ∃ s ∈ secs S V, ∃ t ∈ secs T V, x = s + t} := by
  first | exact @GlobalTheory.CompanionTheory.GE.supsecs | exact GlobalTheory.CompanionTheory.GE.supsecs | (intros; apply GlobalTheory.CompanionTheory.GE.supsecs <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasPeriods
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.CompanionTheory.LTHodge

variable {l : ℕ} [Fact l.Prime]

def lineRep {K LL : FinExt l} (ψ : ↥(GK K) →* (↥LL.1)ˣ) :
    Representation ↥LL.1 ↥(GK K) (Fin 1 → ↥LL.1) :=
  ((Matrix.toLinAlgEquiv' : Matrix (Fin 1) (Fin 1) ↥LL.1 ≃ₐ[↥LL.1] _) : _ →* _).comp
    ((Units.coeHom _).comp ((PositivityTheory.HodgeLocalCharacter.HLC.toGL1 ↥LL.1).comp ψ))

def ltSeries {K : FinExt l} (π : ↥(OL K)) : PowerSeries ↥(OL K) :=
  PowerSeries.C π * PowerSeries.X + PowerSeries.X ^ Nat.card (↥(OL K) ⧸ Ideal.span {π})

def IsLTChar (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ) : Prop :=
  ∃ (π : ↥(OL K)) (z : ℕ → Om l), Irreducible π ∧ z 0 = 0 ∧ z 1 ≠ 0 ∧
    (∀ n, z (n + 1) ^ Nat.card (↥(OL K) ⧸ Ideal.span {π}) +
      (((π : ↥K.1) : Om l)) * z (n + 1) = z n) ∧
    ∀ (g : ↥(GK K)) (φ : PowerSeries ↥(OL K)), PowerSeries.constantCoeff φ = 0 →
      ((PowerSeries.coeff 1 φ : ↥(OL K)) : ↥K.1) = ((χ g : (↥K.1)ˣ) : ↥K.1) →
      PowerSeries.subst φ (ltSeries π) = PowerSeries.subst (ltSeries π) φ →
      ∀ n, HasSum (fun k : ℕ => (((PowerSeries.coeff k φ : ↥(OL K)) : ↥K.1) : Om l) * z n ^ k)
        ((g : GQ l) (z n))

def HasPeriods (P : LocPrime l) (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ) : Prop :=
  ∀ μ : ↥K.1 →ₐ[ℚ_[l]] Om l, ∃ y : P.R.BdR,
    (∀ (g : GQ l) (hg : g ∈ GK K), (∀ x : ↥K.1, g (μ x) = μ x) →
      P.actQdR g y = algebraMap (Om l) P.R.BdR (μ ((χ ⟨g, hg⟩ : (↥K.1)ˣ) : ↥K.1)) * y) ∧
    (μ = K.1.val → y ∈ (P.PD K).Fil 1 ∧ y ∉ (P.PD K).Fil 2) ∧
    (μ ≠ K.1.val → y ∈ (P.PD K).Fil 0 ∧ y ∉ (P.PD K).Fil 1)

end GlobalTheory.CompanionTheory.LTHodge
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RwAppend
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.PresSobA

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.SobGL.HaarDom

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

abbrev CLof (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] : Type :=
  E →L[ℝ] F

def expC (X : Mat n) (t : ℝ) : G n := (Matrix.isUnit_exp (t • X)).unit

theorem expC_val (X : Mat n) (t : ℝ) : (expC X t).val = NormedSpace.exp (t • X) := rfl

theorem expC_zero (X : Mat n) : expC X 0 = 1 := by
  apply Units.ext
  simp [expC_val]

def IsTest (φ : Mat n → ℝ) : Prop :=
  ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ GLs n

section Mol

variable [MeasurableSpace (G n)] (μ : Measure (G n))

def Mol {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (φ : Mat n → ℝ) (x : G n → V) (z : Mat n) : V :=
  ∫ u : G n, φ (z * (u⁻¹ : G n).val) • x u ∂μ

variable [BorelSpace (G n)] [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]

def lT (y : G n) : Lp V 2 μ →L[ℂ] Lp V 2 μ :=
  (Lp.compMeasurePreservingₗᵢ ℂ (fun z : G n => y⁻¹ * z) (measurePreserving_mul_left μ y⁻¹)).toContinuousLinearMap

def lConv (φ : Mat n → ℝ) (x : Lp V 2 μ) : Lp V 2 μ := ∫ y : G n, φ y.val • lT μ V y x ∂μ

variable {V}

theorem lT_coe (y : G n) (x : Lp V 2 μ) : lT μ V y x =ᵐ[μ] fun z => x (y⁻¹ * z) :=
  Lp.coeFn_compMeasurePreserving x (measurePreserving_mul_left μ y⁻¹)

theorem rR_coe (hU : Unimod) (h : G n) (x : Lp V 2 μ) : rR μ V h x =ᵐ[μ] fun z => x (z * h) := by
  haveI := (hU n μ).1
  have hm : MeasurePreserving (fun y : G n => y * h) μ μ := measurePreserving_mul_right μ h
  have : rR μ V h x = Lp.compMeasurePreserving (fun y : G n => y * h) hm x := by
    simp only [rR, dif_pos hm]
    rfl
  rw [this]
  exact Lp.coeFn_compMeasurePreserving x hm

theorem cls_of_ae {f : Mat n → V} {x : Lp V 2 μ} (h : (fun y : G n => f y.val) =ᵐ[μ] x) :
    MemLp (fun y : G n => f y.val) 2 μ ∧ cls μ f = x := by
  have hm : MemLp (fun y : G n => f y.val) 2 μ := (memLp_congr_ae h).2 (Lp.memLp x)
  refine ⟨hm, ?_⟩
  simp only [cls, dif_pos hm]
  exact Lp.ext (hm.coeFn_toLp.trans h)

theorem coe_cls {f : Mat n → V} (h : MemLp (fun y : G n => f y.val) 2 μ) :
    (cls μ f : G n → V) =ᵐ[μ] fun y => f y.val := by
  simp only [cls, dif_pos h]
  exact h.coeFn_toLp

end Mol

theorem isOpen_GLs : IsOpen (GLs n) := by
  have : Continuous fun g : Mat n => g.det := Continuous.matrix_det continuous_id
  exact isOpen_ne.preimage this

section Words

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem Rd_congr {f f' : Mat n → V} (h : ∀ z ∈ GLs n, f z = f' z) (X : Mat n) :
    ∀ z ∈ GLs n, Rd X f z = Rd X f' z := by
  intro z hz
  have : f =ᶠ[𝓝 z] f' := Filter.eventuallyEq_of_mem (isOpen_GLs.mem_nhds hz) h
  simp only [Rd, this.fderiv_eq]

theorem Rw_append (w w' : List (Bool × Fin n × Fin n)) (f : Mat n → V) :
    Rw (w ++ w') f = Rw w (Rw w' f) := by
  induction w with
  | nil => rfl
  | cons p w ih => simp only [List.cons_append, Rw, ih]

end Words

end GlobalTheory.CompanionTheory.PresSobA
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorRapid
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.KerFc

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def Rapid (h : C₀(ℝ, ℂ)) : Prop := ∀ m : ℕ, ∃ h' : C₀(ℝ, ℂ), ∀ y, h' y = (y : ℂ) ^ m * h y

def lTr {n : ℕ} {V : Type} (x : G n) (f : Mat n → V) : Mat n → V := fun y => f (x.val * y)

def secCls {n : ℕ} [MeasurableSpace (G n)] (μ : Measure (G n)) (E : KMod n) : Set (Lp E.V 2 μ) :=
  {x | ∃ f, Sob μ f ∧ IsSec E f ∧ cls μ f = x}

def Std {n : ℕ} [MeasurableSpace (G n)] (μ : Measure (G n)) (E : KMod n) [CompleteSpace E.V]
    {Ω : Msob μ E.V →ₗ[ℂ] Msob μ E.V} {T : Lp E.V 2 μ →L[ℂ] Lp E.V 2 μ}
    (F : FCalc (Lp E.V 2 μ) (Msob μ E.V) Ω T) (c : ℝ) : Prop :=
  LgFacts ∧ Unimod ∧ RCalc ∧ SobG ∧ AlgEst ∧ WaveSpeed ∧ WaveCpt ∧ CalcSteps ∧ SmoothOp ∧ PWdecay ∧
    (∀ x ∈ Msob μ E.V, ∃ f, Sob μ f ∧ cls μ f = x) ∧
    (∀ x y : Msob μ E.V, ⟪(Ω x : Lp E.V 2 μ), y⟫_ℂ = ⟪(x : Lp E.V 2 μ), Ω y⟫_ℂ) ∧
    (∀ x : Msob μ E.V, ∃ v : Msob μ E.V, (v : Lp E.V 2 μ) = T x ∧ (v : Lp E.V 2 μ) + (Ω (Ω v) : Lp E.V 2 μ) = x) ∧
    (∀ x : Msob μ E.V, T ((x : Lp E.V 2 μ) + (Ω (Ω x) : Lp E.V 2 μ)) = x) ∧
    (∀ (f : Mat n → E.V) (hf : cls μ f ∈ Msob μ E.V), Sob μ f → (Ω ⟨cls μ f, hf⟩ : Lp E.V 2 μ) = cls μ (Om f)) ∧
    ∀ f : Mat n → E.V, Sob μ f → IsSec E f → (⟪cls μ (Om f), cls μ f⟫_ℂ).re ≤ c * ‖cls μ f‖ ^ 2

def Row {n : ℕ} [MeasurableSpace (G n)] (μ : Measure (G n)) (E : KMod n) [CompleteSpace E.V]
    {Ω : Msob μ E.V →ₗ[ℂ] Msob μ E.V} {T : Lp E.V 2 μ →L[ℂ] Lp E.V 2 μ}
    (F : FCalc (Lp E.V 2 μ) (Msob μ E.V) Ω T) (h : C₀(ℝ, ℂ)) (v : E.V) (f : Mat n → E.V) : Prop :=
  Sob μ f ∧ IsSec E f ∧ ∀ φ f' : Mat n → E.V, Sob μ φ → IsSec E φ → Sob μ f' → IsSec E f' →
    cls μ f' = F.Φ h (cls μ φ) → ⟪cls μ f, cls μ φ⟫_ℂ = ⟪v, f' 1⟫_ℂ

def FactorRapid : Prop :=
  ∀ h : C₀(ℝ, ℂ), Rapid h → ∃ h₁ h₂ : C₀(ℝ, ℂ), Rapid h₁ ∧ Rapid h₂ ∧ Rapid (star h₂) ∧ h = h₁ * h₂

def EvAdj : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    [CompleteSpace E.V] (Ω : Msob μ E.V →ₗ[ℂ] Msob μ E.V) (T : Lp E.V 2 μ →L[ℂ] Lp E.V 2 μ)
    (F : FCalc (Lp E.V 2 μ) (Msob μ E.V) Ω T) (c : ℝ), Std μ E F c →
    ∀ h : C₀(ℝ, ℂ), Rapid h → ∀ v : E.V, ∃ κ ∈ closure (secCls μ E), ∀ φ f' : Mat n → E.V, Sob μ φ → IsSec E φ →
      Sob μ f' → IsSec E f' → cls μ f' = F.Φ h (cls μ φ) → ⟪κ, cls μ φ⟫_ℂ = ⟪v, f' 1⟫_ℂ

def RowExists : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    [CompleteSpace E.V] (Ω : Msob μ E.V →ₗ[ℂ] Msob μ E.V) (T : Lp E.V 2 μ →L[ℂ] Lp E.V 2 μ)
    (F : FCalc (Lp E.V 2 μ) (Msob μ E.V) Ω T) (c : ℝ), Std μ E F c →
    ∀ h : C₀(ℝ, ℂ), Rapid h → ∀ v : E.V, ∃ f, Row μ E F h v f

def RowMatrix : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    [CompleteSpace E.V] (Ω : Msob μ E.V →ₗ[ℂ] Msob μ E.V) (T : Lp E.V 2 μ →L[ℂ] Lp E.V 2 μ)
    (F : FCalc (Lp E.V 2 μ) (Msob μ E.V) Ω T) (c : ℝ), Std μ E F c →
    ∀ h : C₀(ℝ, ℂ), (∀ v : E.V, ∃ f, Row μ E F h v f) →
      ∃ A : Mat n → (E.V →L[ℂ] E.V), ∀ v, Row μ E F h v (fun y => A y v)

def AdjSmooth : Prop :=
  ∀ (W V : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] [CompleteSpace V] (A : W → (V →L[ℂ] V)) (s : Set W),
    (∀ v, ContDiffOn ℝ ∞ (fun y => A y v) s) → ContDiffOn ℝ ∞ (fun y => ContinuousLinearMap.adjoint (A y)) s

def LtSob : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type)
    [NormedAddCommGroup V] [InnerProductSpace ℂ V], LgFacts → Unimod → RCalc →
    ∀ (x : G n) (f : Mat n → V), Sob μ f → Sob μ (lTr x f) ∧ ∀ g ∈ GLs n, Om (lTr x f) g = Om f (x.val * g)

def LtComm : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    [CompleteSpace E.V] (Ω : Msob μ E.V →ₗ[ℂ] Msob μ E.V) (T : Lp E.V 2 μ →L[ℂ] Lp E.V 2 μ)
    (F : FCalc (Lp E.V 2 μ) (Msob μ E.V) Ω T) (c : ℝ), Std μ E F c →
    ∀ (h : C₀(ℝ, ℂ)) (x : G n) (f f' : Mat n → E.V), Sob μ f → Sob μ f' → cls μ f' = F.Φ h (cls μ f) →
      cls μ (lTr x f') = F.Φ h (cls μ (lTr x f))

def RowLeft : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    [CompleteSpace E.V] (Ω : Msob μ E.V →ₗ[ℂ] Msob μ E.V) (T : Lp E.V 2 μ →L[ℂ] Lp E.V 2 μ)
    (F : FCalc (Lp E.V 2 μ) (Msob μ E.V) Ω T) (c : ℝ), Std μ E F c →
    ∀ (h : C₀(ℝ, ℂ)) (A : Mat n → (E.V →L[ℂ] E.V)), Rapid h → (∀ v, Row μ E F h v (fun y => A y v)) →
      ∀ (k : Matrix.unitaryGroup (Fin n) ℂ), ∀ y ∈ GLs n, ∀ v, A (k.1 * y) v = A y (E.ρ k⁻¹ v)

def ActFormula : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    [CompleteSpace E.V] (Ω : Msob μ E.V →ₗ[ℂ] Msob μ E.V) (T : Lp E.V 2 μ →L[ℂ] Lp E.V 2 μ)
    (F : FCalc (Lp E.V 2 μ) (Msob μ E.V) Ω T) (c : ℝ), Std μ E F c →
    ∀ (h : C₀(ℝ, ℂ)) (A : Mat n → (E.V →L[ℂ] E.V)), (∀ v, Row μ E F h v (fun y => A y v)) →
      ∀ f ∈ CE E, Cpt f → ∀ f', Sob μ f' → IsSec E f' → cls μ f' = F.Φ h (cls μ f) →
        ∀ x ∈ GLs n, act μ E (fun y => ContinuousLinearMap.adjoint (A y)) f x = f' x

def WaveRep : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    [CompleteSpace E.V] (Ω : Msob μ E.V →ₗ[ℂ] Msob μ E.V) (T : Lp E.V 2 μ →L[ℂ] Lp E.V 2 μ)
    (F : FCalc (Lp E.V 2 μ) (Msob μ E.V) Ω T) (c : ℝ), Std μ E F c →
    ∀ f ∈ CE E, Cpt f → ∃ (N : ℕ) (b : Lp E.V 2 μ) (U : ℝ → Mat n → E.V), 1 ≤ N ∧ (T ^ N) b = cls μ f ∧ IsWave E U ∧
      (∀ x ∈ GLs n, U 0 x = f x) ∧ ∀ t, Sob μ (U t) ∧ cls μ (U t) = F.Φ (toC0 (wv c N 0 t)) b

def WaveUniq : Prop :=
  WaveSpeed → CalcSteps → RCalc → ∀ (n : ℕ) (E : KMod n) (u u' : ℝ → Mat n → E.V), IsWave E u → IsWave E u' →
    (∀ x ∈ GLs n, u 0 x = u' 0 x) → ∀ t, ∀ x ∈ GLs n, u t x = u' t x

def PhiRes : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    [CompleteSpace E.V] (Ω : Msob μ E.V →ₗ[ℂ] Msob μ E.V) (T : Lp E.V 2 μ →L[ℂ] Lp E.V 2 μ)
    (F : FCalc (Lp E.V 2 μ) (Msob μ E.V) Ω T) (c : ℝ), Std μ E F c →
    ∀ (g : ℝ → ℝ) (T₀ : ℝ), IsBump g T₀ → ∀ N : ℕ, 1 ≤ N →
      F.Φ (toC0 (fun y => ((((1 + y ^ 2) ^ N)⁻¹ : ℝ) : ℂ) * hg c g y)) = F.Φ (toC0 (hg c g)) * T ^ N

def WaveInt : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    [CompleteSpace E.V] (Ω : Msob μ E.V →ₗ[ℂ] Msob μ E.V) (T : Lp E.V 2 μ →L[ℂ] Lp E.V 2 μ)
    (F : FCalc (Lp E.V 2 μ) (Msob μ E.V) Ω T) (c : ℝ), Std μ E F c →
    ∀ (g : ℝ → ℝ) (T₀ : ℝ), IsBump g T₀ → ∀ (N : ℕ) (b : Lp E.V 2 μ) (U : ℝ → Mat n → E.V), 1 ≤ N → IsWave E U →
      (∀ t, Sob μ (U t) ∧ cls μ (U t) = F.Φ (toC0 (wv c N 0 t)) b) →
      ∀ f', Sob μ f' → cls μ f' = F.Φ (toC0 (fun y => ((((1 + y ^ 2) ^ N)⁻¹ : ℝ) : ℂ) * hg c g y)) b →
        ∀ x ∈ GLs n, ∫ t, (g t : ℂ) • U t x = f' x

def SupportRow : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    [CompleteSpace E.V] (Ω : Msob μ E.V →ₗ[ℂ] Msob μ E.V) (T : Lp E.V 2 μ →L[ℂ] Lp E.V 2 μ)
    (F : FCalc (Lp E.V 2 μ) (Msob μ E.V) Ω T) (c : ℝ), Std μ E F c →
    ∀ (g : ℝ → ℝ) (T₀ : ℝ) (h : C₀(ℝ, ℂ)), IsBump g T₀ → Rapid h →
      (∀ f ∈ CE E, Cpt f → ∀ u, IsWave E u → (∀ x ∈ GLs n, u 0 x = f x) → ∀ f', Sob μ f' → IsSec E f' →
        cls μ f' = F.Φ h (cls μ f) → ∀ x ∈ GLs n, ∫ t, (g t : ℂ) • u t x = f' x) →
      ∃ R : ℝ, ∀ (v : E.V) (f : Mat n → E.V), Row μ E F h v f → ∀ y ∈ GLs n, R < lg y → f y = 0

end GlobalTheory.CompanionTheory.KerFc
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdealPowerSubobjectSections
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdealPowerSubobjectSections
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE

lemma range_app_iso_comp {X : Scheme.{0}} {P Q E : X.Modules} (e : P ≅ Q) (f : Q ⟶ E)
    (V : X.Opens) : Set.range ((e.hom ≫ f).app V) = Set.range (f.app V) := by
  ext m
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨e.hom.app V x, by rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]⟩
  · rintro ⟨y, rfl⟩
    refine ⟨e.inv.app V y, ?_⟩
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, Iso.inv_hom_id_assoc]

theorem secs_powSub {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}}
    [X.Over (Spec (.of A))] (E : X.Modules) (hE : E.IsQuasicoherent) (n : ℕ) (V : X.Opens)
    (hV : IsAffineOpen V) :
    secs (powSub I E n) V =
      ((Ideal.map (toFunctions (A := A) V) (I ^ n) • ⊤ : Submodule Γ(X, V) Γ(E, V)) :
        Set Γ(E, V)) := by
  rw [← range_idealPowι_app I E hV n, ← range_app_iso_comp
    (Subobject.underlyingIso (idealPowι I E n)) (idealPowι I E n) V]
  unfold secs powSub
  rw [Subobject.underlyingIso_hom_comp_eq_mk]

end GlobalTheory.CompanionTheory.GE
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdealPowerSubobjectSectionsStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideal_power_subobject_sections : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] (E : X.Modules), E.IsQuasicoherent → ∀ (n : ℕ) (V : X.Opens), IsAffineOpen V → secs (powSub I E n) V = ((Ideal.map (toFunctions (A := A) V) (I ^ n) • ⊤ : Submodule Γ(X, V) Γ(E, V)) : Set Γ(E, V)) := by
  first | exact @GlobalTheory.CompanionTheory.GE.secs_powSub | exact GlobalTheory.CompanionTheory.GE.secs_powSub | (intros; apply GlobalTheory.CompanionTheory.GE.secs_powSub <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubobjectLeIffAffineSections
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubobjectLeIffAffineSections
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE

theorem hom_eq_zero_of_affineOpens {X : Scheme.{0}} {M N : X.Modules} (φ : M ⟶ N)
    (h : ∀ (U : X.affineOpens) (s : Γ(M, (U : X.Opens))), φ.app (U : X.Opens) s = 0) : φ = 0 := by
  apply Scheme.Modules.hom_ext
  intro U
  rw [Scheme.Modules.Hom.zero_app]
  let F : TopCat.Sheaf Ab X := ⟨N.presheaf, N.isSheaf⟩
  have key : ∀ s : Γ(M, U), φ.app U s = 0 := by
    intro s
    refine TopCat.Sheaf.eq_of_locally_eq' F
      (fun i : {V : X.affineOpens // (V : X.Opens) ≤ U} => (i.1 : X.Opens)) U
      (fun i => homOfLE i.2) ?_ _ _ ?_
    · refine fun x (hx : x ∈ U) => ?_
      obtain ⟨W, hW, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset hx
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨W, hW⟩, hWU⟩, hxW⟩
    · intro i
      have hnat := ConcreteCategory.congr_hom
        ((Scheme.Modules.Hom.mapPresheaf φ).naturality (homOfLE i.2).op) s
      simp only [ConcreteCategory.comp_apply] at hnat
      have h2 : N.presheaf.map (homOfLE i.2).op (φ.app U s) = 0 := by
        rw [← h i.1 (M.presheaf.map (homOfLE i.2).op s)]
        exact hnat.symm
      exact h2.trans (map_zero _).symm
  ext s
  simp [key s]

theorem le_iff_secs_subset {X : Scheme.{0}} {E : X.Modules} (S T : Subobject E) :
    S ≤ T ↔ ∀ U : X.affineOpens, secs S (U : X.Opens) ⊆ secs T (U : X.Opens) := by
  unfold GlobalTheory.CompanionTheory.GE.secs
  constructor
  · intro hST U x hx
    obtain ⟨s, rfl⟩ := hx
    refine ⟨(Subobject.ofLE S T hST).app (U : X.Opens) s, ?_⟩
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, Subobject.ofLE_arrow]
  · intro h
    have hzero : S.arrow ≫ cokernel.π T.arrow = 0 := by
      apply GlobalTheory.CompanionTheory.GE.hom_eq_zero_of_affineOpens
      intro U s
      obtain ⟨t, ht⟩ := h U (Set.mem_range_self s)
      rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, ← ht,
        ← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, cokernel.condition,
        Scheme.Modules.Hom.zero_app, AddCommGrpCat.zero_apply]
    exact Subobject.le_of_comm (Abelian.monoLift T.arrow S.arrow hzero)
      (Abelian.monoLift_comp _ _ _)

end GlobalTheory.CompanionTheory.GE
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubobjectLeIffAffineSectionsStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subobject_le_iff_affine_sections : ∀ {X : Scheme.{0}} {E : X.Modules} (S T : Subobject E), S ≤ T ↔ ∀ U : X.affineOpens, secs S (U : X.Opens) ⊆ secs T (U : X.Opens) := by
  first | exact @GlobalTheory.CompanionTheory.GE.le_iff_secs_subset | exact GlobalTheory.CompanionTheory.GE.le_iff_secs_subset | (intros; apply GlobalTheory.CompanionTheory.GE.le_iff_secs_subset <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowIdeal
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh TensorProduct

namespace GlobalTheory.CompanionTheory.GE

variable {X Z : Scheme.{0}}

def secsSub {E : X.Modules} (S : Subobject E) (V : X.Opens) : Submodule Γ(X, V) Γ(E, V) where
  carrier := secs S V
  add_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, map_add _ _ _⟩
  zero_mem' := ⟨0, map_zero _⟩
  smul_mem' := by
    rintro r _ ⟨a, rfl⟩
    exact ⟨r • a, Scheme.Modules.Hom.app_smul _ _ _⟩

def pullSys {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [Z.Over (Spec (.of A))]
    (φ : Z ⟶ X) (E : X.Modules) (S : ℕ → Subobject E) (e : ℕ) :
    Subobject ((Scheme.Modules.pullback φ).obj E) :=
  imageSubobject ((Scheme.Modules.pullback φ).map (S e).arrow) ⊔ powSub I _ (e + 1)

def adjMap (φ : Z ⟶ X) {E : X.Modules} (B : Subobject ((Scheme.Modules.pullback φ).obj E)) :
    E ⟶ (Scheme.Modules.pushforward φ).obj (cokernel B.arrow) :=
  (Scheme.Modules.pullbackPushforwardAdjunction φ).homEquiv E (cokernel B.arrow) (cokernel.π B.arrow)

def adjKer (φ : Z ⟶ X) {E : X.Modules} (B : Subobject ((Scheme.Modules.pullback φ).obj E)) :
    Subobject E :=
  kernelSubobject (adjMap φ B)

def ChartIn (φ : Z ⟶ X) (V : X.Opens) {N : Type} [AddCommGroup N] [Module Γ(X, V) N]
    (T : Submodule Γ(X, V) N) (x : N) : Prop :=
  ∀ (U : Z.Opens), IsAffineOpen U → ∀ h : U ≤ φ ⁻¹ᵁ V,
    letI : Algebra Γ(X, V) Γ(Z, U) := (φ.appLE V U h).hom.toAlgebra
    x ⊗ₜ[Γ(X, V)] (1 : Γ(Z, U)) ∈ LinearMap.range (T.subtype.rTensor Γ(Z, U))

def powIdeal (J₀ : X.IdealSheafData) (m : ℕ) : X.IdealSheafData where
  ideal U := J₀.ideal U ^ m
  map_ideal_basicOpen U f := by
    rw [Ideal.map_pow, J₀.map_ideal_basicOpen]
    rfl

end GlobalTheory.CompanionTheory.GE
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoherentSubobjectCoherent
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoherentSubobjectCoherent
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.GE

theorem isCoherent_subobject {X : Scheme.{0}} [IsLocallyNoetherian X] {E : X.Modules}
    (hE : IsCoherent E) (D : Subobject E) (hD : (D : X.Modules).IsQuasicoherent) :
    IsCoherent (D : X.Modules) := by
  have hEq := hE.1
  have hC : (cokernel D.arrow).IsQuasicoherent := inferInstance
  have hK : IsCoherent (kernel (cokernel.π D.arrow)) := isCoherent_kernel _ hE
  let e : (D : X.Modules) ≅ kernel (cokernel.π D.arrow) :=
    IsLimit.conePointUniqueUpToIso
      (Abelian.monoIsKernelOfCokernel (f := D.arrow)
        (CokernelCofork.ofπ _ (cokernel.condition D.arrow)) (cokernelIsCokernel _))
      (limit.isLimit _)
  refine ⟨hD, fun U hU => ?_⟩
  have := hK.2 U hU
  let f : Γ(kernel (cokernel.π D.arrow), U) →ₗ[Γ(X, U)] Γ((D : X.Modules), U) :=
    { toFun := e.inv.app U
      map_add' := map_add _
      map_smul' := Scheme.Modules.Hom.app_smul _ }
  exact Module.Finite.of_surjective f (bijective_app_of_iso e.symm U).2

end GlobalTheory.CompanionTheory.GE
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoherentSubobjectCoherentStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coherent_subobject_coherent : ∀ {X : Scheme.{0}} [IsLocallyNoetherian X] {E : X.Modules}, IsCoherent E → ∀ D : Subobject E, (D : X.Modules).IsQuasicoherent → IsCoherent (D : X.Modules) := by
  first | exact @GlobalTheory.CompanionTheory.GE.isCoherent_subobject | exact GlobalTheory.CompanionTheory.GE.isCoherent_subobject | (intros; apply GlobalTheory.CompanionTheory.GE.isCoherent_subobject <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemIwUIff
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct
open scoped Pointwise

noncomputable section

namespace GlobalTheory.CompanionTheory.SatPow

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}

theorem latK_mulVec {M : Matrix (Fin n) (Fin n) L} (h1 : ∀ i j, Valued.v (M i j) ≤ 1)
    (h2 : ∀ i j, j < i → Valued.v (M i j) < 1) (k : ℕ) {x : Fin n → L} (hx : x ∈ latK L n k) :
    M.mulVec x ∈ latK L n k := by
  have hx1 : ∀ j, Valued.v (x j) ≤ 1 := fun j => by
    have := hx j
    split_ifs at this with h
    · exact this
    · exact this.le
  intro i
  show if i.val < k then Valued.v ((M.mulVec x) i) ≤ 1 else Valued.v ((M.mulVec x) i) < 1
  have e : (M.mulVec x) i = ∑ j, M i j * x j := rfl
  rw [e]
  split_ifs with hik
  · refine Valuation.map_sum_le _ fun j _ => ?_
    rw [map_mul]
    exact (mul_le_of_le_one_right' (hx1 j)).trans (h1 i j)
  · refine Valuation.map_sum_lt _ one_ne_zero fun j _ => ?_
    rw [map_mul]
    by_cases hjk : j.val < k
    · have hji : j < i := by
        rw [Fin.lt_def]; omega
      exact (mul_le_of_le_one_right' (hx1 j)).trans_lt (h2 i j hji)
    · have := hx j
      rw [if_neg hjk] at this
      exact (mul_le_of_le_one_left' (h1 i j)).trans_lt this

theorem mem_iwU_iff (hσv : ∀ x, Valued.v (σ x) = Valued.v x) (g : GU σ n) :
    g ∈ IwU σ n ↔ (∀ i j, Valued.v (((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j) ≤ 1) ∧
      ∀ i j, j < i → Valued.v (((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j) < 1 := by
  constructor
  · intro hg
    have hg' : (g : GL (Fin n) L) ∈ IwGL L n := hg
    refine ⟨fun i j => GlobalTheory.CompanionTheory.KUFactsU.iwGL_entries hg' i j, fun i j hji => ?_⟩
    have h := (Subgroup.mem_iInf.1 hg') ⟨i.val, by omega⟩
    have hs : (Matrix.GeneralLinearGroup.toLin (g : GL (Fin n) L)) • latK L n i.val = latK L n i.val := h
    have he : (Pi.single j (1 : L) : Fin n → L) ∈ latK L n i.val := by
      intro k
      by_cases hk : k = j
      · subst hk
        have : k.val < i.val := hji
        simp [this]
      · have : (Pi.single j (1 : L) : Fin n → L) k = 0 := Pi.single_eq_of_ne hk _
        rw [this]
        split_ifs <;> simp
    have hm := Set.smul_mem_smul_set (a := Matrix.GeneralLinearGroup.toLin (g : GL (Fin n) L)) he
    rw [hs] at hm
    have hi := hm i
    rw [if_neg (lt_irrefl _)] at hi
    have e : ((Matrix.GeneralLinearGroup.toLin (g : GL (Fin n) L)) • (Pi.single j (1 : L) : Fin n → L)) i =
        ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j := by
      show (Matrix.mulVec ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (Pi.single j (1 : L) : Fin n → L)) i = _
      simp
    rwa [e] at hi
  · rintro ⟨h1, h2⟩
    have hinv := (GlobalTheory.LGrp.mem_GU_iff σ n (g : GL (Fin n) L)).1 g.2
    have h1' : ∀ i j, Valued.v (((g : GL (Fin n) L)⁻¹).val i j) ≤ 1 := fun i j => by
      rw [hinv, hσv]; exact h1 _ _
    have h2' : ∀ i j, j < i → Valued.v (((g : GL (Fin n) L)⁻¹).val i j) < 1 := fun i j hji => by
      rw [hinv, hσv]; exact h2 _ _ (Fin.rev_lt_rev.2 hji)
    show (g : GL (Fin n) L) ∈ IwGL L n
    refine Subgroup.mem_iInf.2 fun k => ?_
    show (Matrix.GeneralLinearGroup.toLin (g : GL (Fin n) L)) • latK L n k = latK L n k
    refine Set.Subset.antisymm ?_ fun x hx => ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact latK_mulVec h1 h2 k hy
    · refine ⟨((g : GL (Fin n) L)⁻¹).val.mulVec x, latK_mulVec h1' h2' k hx, ?_⟩
      show ((g : GL (Fin n) L)).val.mulVec (((g : GL (Fin n) L)⁻¹).val.mulVec x) = x
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

theorem iwU_diag (hσv : ∀ x, Valued.v (σ x) = Valued.v x) {g : GU σ n} (hg : g ∈ IwU σ n) (i : Fin n) :
    Valued.v (((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i) = 1 := by
  classical
  obtain ⟨h1, h2⟩ := (mem_iwU_iff hσv g).1 hg
  obtain ⟨k1, k2⟩ := (mem_iwU_iff hσv g⁻¹).1 (inv_mem hg)
  have hprod : (((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
      (((g⁻¹ : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) i i = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]; simp
  rw [Matrix.mul_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hprod
  have hrest : Valued.v (∑ j ∈ Finset.univ.erase i, ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j *
      (((g⁻¹ : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) j i) < 1 := by
    refine Valuation.map_sum_lt _ one_ne_zero fun j hj => ?_
    rw [map_mul]
    rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hj) with hji | hji
    · exact (mul_le_of_le_one_right' (k1 j i)).trans_lt (h2 i j hji)
    · exact (mul_le_of_le_one_left' (h1 i j)).trans_lt (k2 j i hji)
  have hmain : Valued.v (((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i *
      (((g⁻¹ : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i) = 1 := by
    have e : ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i *
        (((g⁻¹ : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i =
        1 - ∑ j ∈ Finset.univ.erase i, ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j *
          (((g⁻¹ : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) j i := by
      rw [← hprod]; ring
    rw [e, Valuation.map_sub_eq_of_lt_left _ (by simpa using hrest), map_one]
  rw [map_mul] at hmain
  refine le_antisymm (h1 i i) ?_
  calc (1 : WithZero (Multiplicative ℤ)) = _ := hmain.symm
    _ ≤ _ := mul_le_of_le_one_right' (k1 i i)

end GlobalTheory.CompanionTheory.SatPow

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DominantUnipotentContraction
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DominantUnipotentContraction
open GlobalTheory.PRep GlobalTheory.SmGL Matrix Formalism.UG PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.DomGLVal
open scoped Pointwise

noncomputable section

namespace GlobalTheory.CompanionTheory.DomUnitary

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} {σ : L →+* L}
variable (D : CassData (GU σ n))

theorem mem_J_iff (hJ : D.J = IwU σ n) (x : GU σ n) : x ∈ D.J ↔ (x : GL (Fin n) L) ∈ IwGL L n := by
  rw [hJ, IwU, Subgroup.mem_subgroupOf]

theorem upper_facts (hJ : D.J = IwU σ n) (hN : ∀ g : GU σ n, g ∈ D.N ↔ IsUniM (g : GL (Fin n) L))
    {x : GU σ n} (hx : x ∈ D.J ⊓ D.N) :
    IsUniM (x : GL (Fin n) L) ∧ IsUniM (x : GL (Fin n) L)⁻¹ ∧ Integ (x : GL (Fin n) L) ∧
      Integ (x : GL (Fin n) L)⁻¹ := by
  have h := (mem_IwGL_iff _).1 ((mem_J_iff D hJ x).1 hx.1)
  exact ⟨(hN _).1 hx.2, (hN _).1 (inv_mem hx.2), h.1, h.2⟩

theorem lower_facts (hJ : D.J = IwU σ n) (hNm : ∀ g : GU σ n, g ∈ D.Nm ↔ IsLowUniM (g : GL (Fin n) L))
    {x : GU σ n} (hx : x ∈ D.J ⊓ D.Nm) :
    IsLowUniM (x : GL (Fin n) L) ∧ IsLowUniM (x : GL (Fin n) L)⁻¹ ∧ Integ (x : GL (Fin n) L) ∧
      Integ (x : GL (Fin n) L)⁻¹ := by
  have h := (mem_IwGL_iff _).1 ((mem_J_iff D hJ x).1 hx.1)
  exact ⟨(hNm _).1 hx.2, (hNm _).1 (inv_mem hx.2), h.1, h.2⟩

theorem dom_core (hJ : D.J = IwU σ n) (hN : ∀ g : GU σ n, g ∈ D.N ↔ IsUniM (g : GL (Fin n) L))
    (hNm : ∀ g : GU σ n, g ∈ D.Nm ↔ IsLowUniM (g : GL (Fin n) L))
    (hT : ∀ g : GU σ n, g ∈ D.T ↔ IsDiagM (g : GL (Fin n) L)) (τ : GU σ n) (hτ : τ ∈ D.T)
    (hmono : ∀ i j : Fin n, i ≤ j → ordL (((τ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) j j) ≤
      ordL (((τ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i)) :
    (∀ x ∈ D.J ⊓ D.N, τ * x * τ⁻¹ ∈ D.J ⊓ D.N) ∧ (∀ x ∈ D.J ⊓ D.Nm, τ⁻¹ * x * τ ∈ D.J ⊓ D.Nm) ∧
      ∀ x ∈ D.J ⊓ D.T, τ * x * τ⁻¹ ∈ D.J ⊓ D.T ∧ τ⁻¹ * x * τ ∈ D.J ⊓ D.T := by
  obtain ⟨d, hd, hne, hdd⟩ : ∃ d : Fin n → L, ((τ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = Matrix.diagonal d ∧
      (∀ i, d i ≠ 0) ∧ ∀ i, ((τ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i = d i :=
    ⟨_, (diag_data ((hT _).1 hτ)).1, (diag_data ((hT _).1 hτ)).2, fun _ => rfl⟩
  have hmono' : ∀ i j, i ≤ j → ordL (d j) ≤ ordL (d i) := by simpa only [hdd] using hmono
  have hle : ∀ i j, i ≤ j → Valued.v (d i) * Valued.v (d j)⁻¹ ≤ 1 := fun i j hij =>
    ratio_le (hne j) (v_le_of_ordL_le (hne j) (hne i) (hmono' i j hij))
  have hle' : ∀ i j, j ≤ i → Valued.v (d i)⁻¹ * Valued.v ((d j)⁻¹)⁻¹ ≤ 1 := fun i j hij => by
    rw [inv_inv, mul_comm]
    exact hle j i hij
  have hs' := val_inv_diag hne hd
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨u1, u2, i1, i2⟩ := upper_facts D hJ hN hx
    have := up_mem hne hd u1 u2 (fun i j hij => valuation_triple_mul_le (hle i j hij.le) (i1.1 i j))
      (fun i j hij => valuation_triple_mul_le (hle i j hij.le) (i2.1 i j))
    exact ⟨(mem_J_iff D hJ _).2 this.1, (hN _).2 this.2⟩
  · obtain ⟨l1, l2, i1, i2⟩ := lower_facts D hJ hNm hx
    have := low_mem (fun i => inv_ne_zero (hne i)) hs' l1 l2
      (fun i j hij => valuation_triple_mul_lt_one (hle' i j hij.le) (i1.2 i j hij))
      (fun i j hij => valuation_triple_mul_lt_one (hle' i j hij.le) (i2.2 i j hij))
    rw [inv_inv] at this
    exact ⟨(mem_J_iff D hJ _).2 this.1, (hNm _).2 this.2⟩
  · obtain ⟨hdx, -⟩ := diag_data ((hT _).1 hx.2)
    have hc : τ * x = x * τ := by
      apply Subtype.ext
      apply Units.ext
      show ((τ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * ((x : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
        ((x : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * ((τ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)
      rw [hd, hdx, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      exact mul_comm _ _
    have e1 : τ * x * τ⁻¹ = x := by rw [hc, mul_inv_cancel_right]
    have e2 : τ⁻¹ * x * τ = x := by rw [mul_assoc, ← hc, inv_mul_cancel_left]
    rw [e1, e2]
    exact ⟨hx, hx⟩

theorem strict_core (hJ : D.J = IwU σ n) (hN : ∀ g : GU σ n, g ∈ D.N ↔ IsUniM (g : GL (Fin n) L))
    (hNm : ∀ g : GU σ n, g ∈ D.Nm ↔ IsLowUniM (g : GL (Fin n) L))
    (hT : ∀ g : GU σ n, g ∈ D.T ↔ IsDiagM (g : GL (Fin n) L)) (τ : GU σ n) (hτ : τ ∈ D.T)
    (hst : IsStrictDom (τ : GL (Fin n) L)) :
    (∀ x ∈ D.N, ∃ j : ℕ, τ ^ j * x * (τ ^ j)⁻¹ ∈ D.J ⊓ D.N) ∧
      ∀ U : Set (GU σ n), IsOpen U → (1 : GU σ n) ∈ U →
        ∃ j : ℕ, ∀ x ∈ D.J ⊓ D.Nm, (τ ^ j)⁻¹ * x * τ ^ j ∈ U := by
  obtain ⟨d, hd, hne, hdd⟩ : ∃ d : Fin n → L, ((τ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = Matrix.diagonal d ∧
      (∀ i, d i ≠ 0) ∧ ∀ i, ((τ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i = d i :=
    ⟨_, (diag_data ((hT _).1 hτ)).1, (diag_data ((hT _).1 hτ)).2, fun _ => rfl⟩
  have hst' : ∀ i j, i < j → ordL (d j) < ordL (d i) := by
    intro i j hij
    have := hst i j hij
    rwa [hdd, hdd] at this
  have hr : ∀ i j, i < j → ∀ m : ℕ, Valued.v (d i ^ m) * Valued.v (d j ^ m)⁻¹ ≤ cc ^ m := fun i j hij m =>
    ratio_pow_le (hne j) (v_le_of_ordL_lt (hne j) (hne i) (hst' i j hij)) m
  have hpow : ∀ m : ℕ, (((τ ^ m : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      Matrix.diagonal (fun i => d i ^ m) := fun m => by
    rw [SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val, hd, Matrix.diagonal_pow]
    rfl
  have hnep : ∀ m : ℕ, ∀ i, d i ^ m ≠ 0 := fun m i => pow_ne_zero _ (hne i)
  refine ⟨fun x hx => ?_, fun U hU h1 => ?_⟩
  · have u1 : IsUniM (x : GL (Fin n) L) := (hN _).1 hx
    have u2 : IsUniM (x : GL (Fin n) L)⁻¹ := (hN _).1 (inv_mem hx)
    choose f hf using fun p : Fin n × Fin n =>
      exists_pow_mul_le (Valued.v (((x : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) p.1 p.2))
    choose f' hf' using fun p : Fin n × Fin n =>
      exists_pow_mul_le (Valued.v ((((x : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) p.1 p.2))
    have hM : ∀ p, f p ≤ Finset.univ.sup f ⊔ Finset.univ.sup f' := fun p =>
      le_sup_of_le_left (Finset.le_sup (Finset.mem_univ p))
    have hM' : ∀ p, f' p ≤ Finset.univ.sup f ⊔ Finset.univ.sup f' := fun p =>
      le_sup_of_le_right (Finset.le_sup (Finset.mem_univ p))
    generalize Finset.univ.sup f ⊔ Finset.univ.sup f' = M at hM hM'
    have key : ∀ (y : L) (i j : Fin n), i < j → cc ^ M * Valued.v y ≤ 1 →
        Valued.v (d i ^ M * y * (d j ^ M)⁻¹) ≤ 1 := by
      intro y i j hij hy
      rw [map_mul, map_mul, mul_right_comm]
      have h2 := hr i j hij M
      calc Valued.v (d i ^ M) * Valued.v (d j ^ M)⁻¹ * Valued.v y ≤ cc ^ M * Valued.v y := by gcongr
        _ ≤ 1 := hy
    have := up_mem (hnep M) (hpow M) u1 u2
      (fun i j hij => key _ i j hij (hf (i, j) M (hM _)))
      (fun i j hij => key _ i j hij (hf' (i, j) M (hM' _)))
    exact ⟨M, (mem_J_iff D hJ _).2 this.1, (hN _).2 this.2⟩
  · obtain ⟨W, hW, rfl⟩ := isOpen_induced_iff.1 hU
    obtain ⟨m, hm⟩ := open_shrink W hW h1
    refine ⟨m, fun x hx => ?_⟩
    obtain ⟨l1, l2, i1, i2⟩ := lower_facts D hJ hNm hx
    have hs := val_inv_diag (hnep m) (hpow m)
    have hes : ∀ i, (d i ^ m)⁻¹ ≠ 0 := fun i => inv_ne_zero (hnep m i)
    have hb : ∀ a b, b < a → Valued.v (d a ^ m)⁻¹ * Valued.v ((d b ^ m)⁻¹)⁻¹ ≤ cc ^ m := fun a b hab => by
      rw [inv_inv, mul_comm]
      exact hr b a hab m
    have c1 := low_close hes hs l1 (B := cc ^ m) (fun a b hab => valuation_triple_mul_le (hb a b hab) (i1.1 a b))
    have c2 := low_close hes hs l2 (B := cc ^ m) (fun a b hab => valuation_triple_mul_le (hb a b hab) (i2.1 a b))
    have := hm _ c1 (by rw [GlobalTheory.CompanionTheory.DomGLVal.conj_inv]; exact c2)
    rw [inv_inv] at this
    exact this

theorem domU : PositivityTheory.SphericalProduct.DomU := by
  intro L _ _ _ ϖ σ q _ n D hJ hN hNm hT t
  refine ⟨fun h => dom_core D hJ hN hNm hT t t.2 h, fun h => ⟨?_, strict_core D hJ hN hNm hT t t.2 h⟩⟩
  exact dom_core D hJ hN hNm hT t t.2 fun i j hij => by
    rcases hij.lt_or_eq with hij | rfl
    · exact (h i j hij).le
    · exact le_rfl

end GlobalTheory.CompanionTheory.DomUnitary
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DominantUnipotentContractionStatement
open GlobalTheory.PRep GlobalTheory.SmGL Matrix Formalism.UG PositivityTheory.SphericalProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dominant_unipotent_contraction : PositivityTheory.SphericalProduct.DomU := by
  first | exact @GlobalTheory.CompanionTheory.DomUnitary.domU | exact GlobalTheory.CompanionTheory.DomUnitary.domU | (intros; apply GlobalTheory.CompanionTheory.DomUnitary.domU <;> assumption)
end
end
