module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmGaloisRepresentationCrystalline
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermModerateGrowth
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HarishChandraModulesIndefiniteUnitaryGroup
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingCompatibleAddSecondSlotComplexStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingAddRightComplex
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM

noncomputable section

namespace GlobalTheory.WeilEqAdd

theorem weilIs_mul_right {S : Scheme.{0}} (P : Out.PolAV S) (k : ℕ) {T : Over S} (x y y' : T ⟶ P.A)
    (c c' : Γ(T.left, ⊤)ˣ) (h : Out.WeilIs P.A P.L k x y c) (h' : Out.WeilIs P.A P.L k x y' c') :
    Out.WeilIs P.A P.L k x (y * y') (c * c') := by
  have h₁ := GlobalTheory.CommPairing.weilIs_symm P.isLB h
  have h₂ := GlobalTheory.CommPairing.weilIs_symm P.isLB h'
  have h₃ := GlobalTheory.CommPairing.weilIs_symm P.isLB
    (GlobalTheory.weilIs_mul_left GlobalTheory.globalFns_holds S P k T y y' x _ _ h₁ h₂)
  have e : (c⁻¹ * c'⁻¹)⁻¹ = c * c' := by rw [mul_inv, inv_inv, inv_inv, mul_comm]
  rwa [e] at h₃

end GlobalTheory.WeilEqAdd

namespace GlobalTheory


open WeilEqAdd in
theorem weilEq_mul_right_add : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K]
    [NumberField K] (σ₁ : K →+* ℂ) (A B : PAT H (Sp (𝓞 K))) (f g₁ g₂ : A.t.G ⟶ B.t.G), IsMonHom f → IsMonHom g₁ →
    IsMonHom g₂ → ∀ r₁ r₂ : 𝓞 E,
    WeilEq B.t.PP.L f g₁ A.t.PP.L (A.t.act.act r₁) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) →
    WeilEq B.t.PP.L f g₂ A.t.PP.L (A.t.act.act r₂) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) →
    WeilEq B.t.PP.L f (g₁ * g₂) A.t.PP.L (A.t.act.act (r₁ + r₂)) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := by
  intro E _ _ _ H K _ _ σ₁ A B f g₁ g₂ _ _ _ r₁ r₂ h₁ h₂ n x y c hn hx hy
  haveI : IsCommMonObj A.pol.A := A.ab.comm
  have hL : Out.Laws := GlobalTheory.firstFiveLaws.1
  have ex : ∀ r : 𝓞 E, ∃ u : ℂˣ,
      Out.WeilIs A.t.G A.t.PP.L n (x ≫ A.t.act.act r) (y ≫ 𝟙 _) (unitOn u) := by
    intro r
    haveI := A.t.act.hom r
    have hxr : (x ≫ A.t.act.act r) ^ n = 1 := by
      rw [← MonObj.pow_comp, hx, MonObj.one_comp]
    have hy' : (y ≫ 𝟙 _) ^ n = 1 := by rw [Category.comp_id]; exact hy
    exact GlobalTheory.TorsionGenerators.exists_weilIs hL A.pol (σ₁.comp (algebraMap (𝓞 K) K)) hxr hy'
  have um : ∀ a b : ℂˣ, unitOn (a * b) = unitOn a * unitOn b := fun a b => map_mul (Units.map _) a b
  obtain ⟨c₁, e₁⟩ := ex r₁
  obtain ⟨c₂, e₂⟩ := ex r₂
  have hA : Out.WeilIs A.t.G A.t.PP.L n (x ≫ A.t.act.act (r₁ + r₂)) (y ≫ 𝟙 _) (unitOn (c₁ * c₂)) := by
    rw [A.t.act.add, MonObj.comp_mul, um]
    exact GlobalTheory.weilIs_mul_left GlobalTheory.globalFns_holds _ A.pol n _ _ _ _ _ _ e₁ e₂
  have hB : Out.WeilIs B.t.G B.t.PP.L n (x ≫ f) (y ≫ (g₁ * g₂)) (unitOn (c₁ * c₂)) := by
    rw [MonObj.comp_mul, um]
    exact weilIs_mul_right B.pol n _ _ _ _ _ ((h₁ n x y c₁ hn hx hy).2 e₁) ((h₂ n x y c₂ hn hx hy).2 e₂)
  constructor
  · intro h
    obtain rfl := GlobalTheory.weilIs_unique_fieldPoint _ _ _ B.t.PP.isLB _ _ _ _ _ _ _ h hB
    exact hA
  · intro h
    obtain rfl := GlobalTheory.weilIs_unique_fieldPoint _ _ _ A.t.PP.isLB _ _ _ _ _ _ _ h hA
    exact hB

end GlobalTheory
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilPairingCompatible_add_second_position_complex : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K]
    [NumberField K] (σ₁ : K →+* ℂ) (A B : PAT H (Sp (𝓞 K))) (f g₁ g₂ : A.t.G ⟶ B.t.G), IsMonHom f → IsMonHom g₁ →
    IsMonHom g₂ → ∀ r₁ r₂ : 𝓞 E,
    WeilEq B.t.PP.L f g₁ A.t.PP.L (A.t.act.act r₁) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) →
    WeilEq B.t.PP.L f g₂ A.t.PP.L (A.t.act.act r₂) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) →
    WeilEq B.t.PP.L f (g₁ * g₂) A.t.PP.L (A.t.act.act (r₁ + r₂)) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := by
  first | exact @GlobalTheory.weilEq_mul_right_add | exact GlobalTheory.weilEq_mul_right_add | (intros; apply GlobalTheory.weilEq_mul_right_add <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPointMemStandardAndSkewLatticeOfEntriesMem
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPointMemStandardAndSkewLatticeOfEntriesMem
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)
open scoped nonZeroDivisors

namespace GlobalTheory.FunObj.SqNum

theorem pt_mem_of_entries_mem (D : D7) (δ : ℂ) (𝔪 : Ideal (𝓞 D.host.E)) {a d : ℕ}
    (w : Matrix (Fin d) (Fin a) D.host.E) (hw : ∀ i j, ∃ b ∈ 𝔪, w i j = (b : D.host.E)) :
    pt D (tor0 D ⊤ δ) δ w ∈ La0 D (tor0 D ⊤ δ) a d ∧
      pt D (tor0 D ⊤ δ) δ w ∈ La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d) := by
  have key : ∀ L' : Submodule (𝓞 D.host.E) (Fin d → D.host.E), (∀ x ∈ stdL D a, w.mulVec x ∈ L') →
      pt D (tor0 D ⊤ δ) δ w ∈ La D (tor0 D ⊤ δ) (stdL D a) L' := by
    intro L' hL'
    refine AddSubgroup.subset_closure ⟨δ, AddSubgroup.subset_closure ⟨1, trivial, by simp⟩, w, ?_, rfl⟩
    refine Submodule.subset_span ⟨1, ?_, w, Submodule.subset_span hL', (one_smul _ _).symm⟩
    refine FractionalIdeal.one_mem_inv_coe_ideal fun h => ?_
    have h2 := D.host.𝔟_spec.2
    rw [h, Ideal.smul_bot, sup_bot_eq] at h2
    exact bot_ne_top h2
  have hent : ∀ x ∈ stdL D a, ∀ i, w.mulVec x i ∈
      ((𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Submodule (𝓞 D.host.E) D.host.E) := by
    intro x hx i
    show ∑ j, w i j * x j ∈ _
    refine Submodule.sum_mem _ fun j _ => ?_
    obtain ⟨b, hb, hbw⟩ := hw i j
    obtain ⟨y, hy⟩ := Submodule.mem_one.1 (hx j trivial)
    refine (FractionalIdeal.mem_coeIdeal _).2 ⟨b * y, 𝔪.mul_mem_right y hb, ?_⟩
    rw [hbw, ← hy, map_mul]
  refine ⟨key _ fun x hx i _ => ?_, key _ fun x hx i _ => ?_⟩
  · have := (FractionalIdeal.coe_le_coe.2 FractionalIdeal.coeIdeal_le_one) (hent x hx i)
    rw [FractionalIdeal.coe_one] at this
    exact this
  · by_cases h𝔪 : 𝔪 = ⊥
    · have := hent x hx i
      rw [h𝔪, FractionalIdeal.coeIdeal_bot] at this
      have h0 : w.mulVec x i = 0 := by simpa using this
      rw [h0]
      exact zero_mem _
    · have hne : ((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := by
        rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
        intro h
        apply h𝔪
        have := congrArg (fun J : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • J) h
        simpa using this
      have hle : (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≤
          (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) /
            ((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
        rw [FractionalIdeal.le_div_iff_mul_le hne]
        first
        | exact mul_le_of_le_one_right' FractionalIdeal.coeIdeal_le_one
        | exact mul_le_of_le_one_right (zero_le _) FractionalIdeal.coeIdeal_le_one
        | exact (mul_le_mul_left FractionalIdeal.coeIdeal_le_one _).trans_eq (mul_one _)
        | exact (FractionalIdeal.mul_le_mul_left FractionalIdeal.coeIdeal_le_one _).trans_eq (mul_one _)
        | exact (mul_le_mul_of_nonneg_left FractionalIdeal.coeIdeal_le_one (zero_le _)).trans_eq (mul_one _)
      exact (FractionalIdeal.coe_le_coe.2 hle) (hent x hx i)

end GlobalTheory.FunObj.SqNum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPointMemStandardAndSkewLatticeOfEntriesMemStatement
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaPoint_mem_standard_and_skewLattice_of_entries_mem : ∀ (D : D7) (δ : ℂ) (𝔪 : Ideal (𝓞 D.host.E)) {a d : ℕ} (w : Matrix (Fin d) (Fin a) D.host.E), (∀ i j, ∃ b ∈ 𝔪, w i j = (b : D.host.E)) → pt D (tor0 D ⊤ δ) δ w ∈ La0 D (tor0 D ⊤ δ) a d ∧ pt D (tor0 D ⊤ δ) δ w ∈ La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d) := by
  first | exact @GlobalTheory.FunObj.SqNum.pt_mem_of_entries_mem | exact GlobalTheory.FunObj.SqNum.pt_mem_of_entries_mem | (intros; apply GlobalTheory.FunObj.SqNum.pt_mem_of_entries_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AvgFormApply
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.SiegelAvg

def IsHaarB {Y : Type} [AddGroup Y] [TopologicalSpace Y] (μ : @Measure Y (borel Y)) : Prop :=
  @Measure.IsAddHaarMeasure Y _ _ (borel Y) μ

variable {Y V : Type} [TopologicalSpace Y] [AddCommGroup V] [Module ℂ V]

def Conv (μ : @Measure Y (borel Y)) (L₁ : V →ₗ[ℂ] ℂ) (T : Y → V →ₗ[ℂ] V) (v : V) : Prop :=
  letI : MeasurableSpace Y := borel Y
  Integrable (fun y => L₁ (T y v)) μ

def convSub (μ : @Measure Y (borel Y)) (L₁ : V →ₗ[ℂ] ℂ) (T : Y → V →ₗ[ℂ] V) : Submodule ℂ V where
  carrier := {v | Conv μ L₁ T v}
  zero_mem' := by
    letI : MeasurableSpace Y := borel Y
    show Integrable (fun y => L₁ (T y 0)) μ
    simp only [map_zero]
    exact integrable_zero _ _ _
  add_mem' := by
    letI : MeasurableSpace Y := borel Y
    intro v w hv hw
    show Integrable (fun y => L₁ (T y (v + w))) μ
    simp only [map_add (f := _)]
    exact Integrable.add hv hw
  smul_mem' := by
    letI : MeasurableSpace Y := borel Y
    intro c v hv
    show Integrable (fun y => L₁ (T y (c • v))) μ
    simp only [map_smul, smul_eq_mul]
    exact Integrable.const_mul hv c

def avg0 (μ : @Measure Y (borel Y)) (L₁ : V →ₗ[ℂ] ℂ) (T : Y → V →ₗ[ℂ] V) : convSub μ L₁ T →ₗ[ℂ] ℂ where
  toFun v := letI : MeasurableSpace Y := borel Y; ∫ y, L₁ (T y (v : V)) ∂μ
  map_add' v w := by
    letI : MeasurableSpace Y := borel Y
    show ∫ y, L₁ (T y ((v : V) + w)) ∂μ = ∫ y, L₁ (T y v) ∂μ + ∫ y, L₁ (T y w) ∂μ
    simp only [map_add (f := _)]
    exact integral_add v.2 w.2
  map_smul' c v := by
    letI : MeasurableSpace Y := borel Y
    show ∫ y, L₁ (T y (c • (v : V))) ∂μ = c • ∫ y, L₁ (T y v) ∂μ
    simp only [map_smul, smul_eq_mul]
    exact integral_const_mul c _

def avgForm (μ : @Measure Y (borel Y)) (L₁ : V →ₗ[ℂ] ℂ) (T : Y → V →ₗ[ℂ] V) : V →ₗ[ℂ] ℂ :=
  (LinearMap.exists_extend (avg0 μ L₁ T)).choose

theorem avgForm_apply (μ : @Measure Y (borel Y)) (L₁ : V →ₗ[ℂ] ℂ) (T : Y → V →ₗ[ℂ] V) {v : V}
    (hv : Conv μ L₁ T v) :
    avgForm μ L₁ T v = (letI : MeasurableSpace Y := borel Y; ∫ y, L₁ (T y v) ∂μ) :=
  LinearMap.congr_fun (LinearMap.exists_extend (avg0 μ L₁ T)).choose_spec ⟨v, hv⟩

def schrL {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (w : (κ → R) × (κ → R)) : Module.End ℂ ((κ → R) → ℂ) where
  toFun := schr ψ w
  map_add' φ φ' := funext fun x => by simp only [schr, Pi.add_apply]; ring
  map_smul' c φ := funext fun x => by simp only [schr, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

def starFam {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {a b : ℕ}
    {Bf : Matrix (Fin a) (Fin b ⊕ Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → Matrix (Fin a) (Fin b ⊕ Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → AF F} {κ : Type} [Fintype κ]
    (dd : Darboux Bf κ) (ψ : AddChar (AF F) ℂ) (u : Fin a → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (y : Fin b → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :
    Module.End ℂ ((κ → AF F) → ℂ) :=
  schrL ψ (dd.e (Matrix.vecMulVec u (Sum.elim y y)))

theorem starFam_apply {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {a b : ℕ}
    {Bf : Matrix (Fin a) (Fin b ⊕ Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → Matrix (Fin a) (Fin b ⊕ Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → AF F} {κ : Type} [Fintype κ]
    (dd : Darboux Bf κ) (ψ : AddChar (AF F) ℂ) (u : Fin a → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (y : Fin b → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (φ : (κ → AF F) → ℂ) :
    starFam dd ψ u y φ = dd.rho ψ (Matrix.vecMulVec u (Sum.elim y y)) φ := rfl

end GlobalTheory.SiegelAvg

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLevelComponentsDoubleCosetsCongruence
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLevelComponentsDoubleCosetsCongruence
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal

noncomputable section

open IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevGeo.Reps

theorem core (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (r : ℕ) (hr : V.rank = r) (Comp : Type) (X : Comp → Data D.host.E r)
    (dict : GA D V → Σ k, Frame (X k).Ψ r) (Kf : Subgroup (GA D V))
    (th : ∀ c, (X c).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : ℕ)
    (hK : IsLevelK V M Kf) (hth : ∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) (hD : DictIsUnif V dict Kf th hr)
    (hm : ∀ k, ModelW V hr (X k)) :
    ∃ (G : Matrix (Fin r) (Fin r) D.host.E) (Λ : Submodule (𝓞 D.host.E) (Fin r → D.host.E))
      (g : Comp → Matrix (Fin r) (Fin r) (GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E))
      (Λk : Comp → Submodule (𝓞 D.host.E) (Fin r → D.host.E)) (u : Comp → (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ),
      GlobalTheory.UCls.SelfDualLat G Λ ∧
      (∀ k, (X k).Gm = G ∧ GlobalTheory.UCls.IsUA (IsCMField.complexConj D.host.E) G (g k) ∧
        (Λk k : Set (Fin r → D.host.E)) = GlobalTheory.AdLat.latOf (maximalRealSubfield D.host.E) (g k) (Λ : Set (Fin r → D.host.E)) ∧
        (Λk k).FG ∧ Submodule.span D.host.E (Λk k : Set (Fin r → D.host.E)) = ⊤ ∧
        (∀ τ ∈ (X k).Ψ, gram τ G (u k τ) = G.map τ) ∧
        (∀ γ ∈ (X k).Γ, ∃ γ' : GL (Fin r) D.host.E, (IsUStab G (Λk k) γ' ∧ ∀ x ∈ Λk k, ∃ y ∈ Λk k,
            (γ' : Matrix (Fin r) (Fin r) D.host.E).mulVec x - x = M • y) ∧
          ∀ τ ∈ (X k).Ψ, u k τ * (γ : Matrix (Fin r) (Fin r) D.host.E).map τ =
            (γ' : Matrix (Fin r) (Fin r) D.host.E).map τ * u k τ) ∧
        ∀ γ' : GL (Fin r) D.host.E, (IsUStab G (Λk k) γ' ∧ ∀ x ∈ Λk k, ∃ y ∈ Λk k,
            (γ' : Matrix (Fin r) (Fin r) D.host.E).mulVec x - x = M • y) →
          ∃ γ ∈ (X k).Γ, ∀ τ ∈ (X k).Ψ, u k τ * (γ : Matrix (Fin r) (Fin r) D.host.E).map τ =
            (γ' : Matrix (Fin r) (Fin r) D.host.E).map τ * u k τ) ∧
      ∀ k k', GlobalTheory.UCls.UEquiv (IsCMField.complexConj D.host.E) G (Λ : Set (Fin r → D.host.E)) M (g k) (g k') → k = k' := by
  subst hr
  classical
  obtain ⟨x0, hx0, hact⟩ := hD.2.2.1
  choose gA hgA using fun c => (hx0 c).2
  have hG : ∀ k, (X k).Gm = -(V.gram)ᵀ := fun k => by
    have := (hm k).1
    simpa [Matrix.reindex_apply] using this
  have hL := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  choose Λk hΛk using fun k => GlobalTheory.T.exists_lattice_rationalVectorsInAdelicTranslate D.host.F D.host.E V.rank (GlobalTheory.Member.latC V) (finHom V (gA k))
    hL.2.2.1 hL.2.2.2.1
  refine ⟨-(V.gram)ᵀ, GlobalTheory.Member.latC V, fun k => (finHom V (gA k)).1, Λk,
    fun k τ => if h : τ ∈ (X k).Ψ then archM V (th k ⟨τ, h⟩) (gA k) else 1, GlobalTheory.T.selfDualLattice_neg_transpose_gram D V, fun k => ?_, ?_⟩
  · refine ⟨hG k, GlobalTheory.T.finiteUnitaryPart_isInvertibleUnitaryAdelic D V (gA k), (hΛk k).1, (hΛk k).2.1, (hΛk k).2.2.1, ?_, ?_, ?_⟩
    · intro τ hτ
      simp only [dif_pos hτ]
      exact GlobalTheory.T.archimedeanMatrix_unitaryGroup_preserves_gram D V τ _ (hth k ⟨τ, hτ⟩) (gA k)
    · intro γ hγ
      obtain ⟨γ', h1, h2⟩ := GlobalTheory.T.arithmeticGroup_conj_rational_principalCongruence D V Comp X dict Kf th M x0 hK hth hD (fun c => (hx0 c).1) hact hG k (gA k)
        (hgA k) (Λk k) (hΛk k).1 γ hγ
      refine ⟨γ', h1, fun τ hτ => ?_⟩
      simp only [dif_pos hτ]
      exact h2 τ hτ
    · intro γ' hγ'
      obtain ⟨γ, hγ, h2⟩ := GlobalTheory.T.principalCongruence_conj_mem_arithmeticGroup D V Comp X dict Kf th M x0 hK hth hD (fun c => (hx0 c).1) hact hG k (gA k)
        (hgA k) (Λk k) (hΛk k).1 (hΛk k).2.2.2 γ' hγ'
      refine ⟨γ, hγ, fun τ hτ => ?_⟩
      simp only [dif_pos hτ]
      exact h2 τ hτ
  · exact GlobalTheory.T.componentRepresentatives_injective_doubleCoset D V Comp X dict Kf th M gA hK hth hD (fun k => by rw [hgA k])

end GlobalTheory.LevGeo.Reps

theorem GlobalTheory.LevGeo.Reps.components_double_cosets : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → ∀ σ, GoodEmb c σ → ∃ (G : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) (Λ : Submodule (𝓞 D.host.E) (Fin D.R.r → D.host.E)) (g : (U σ).Comp → Matrix (Fin D.R.r) (Fin D.R.r) (GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E)) (Λk : (U σ).Comp → Submodule (𝓞 D.host.E) (Fin D.R.r → D.host.E)) (u : (U σ).Comp → (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ), GlobalTheory.UCls.SelfDualLat G Λ ∧ (∀ k, ((U σ).X k).Gm = G ∧ GlobalTheory.UCls.IsUA (IsCMField.complexConj D.host.E) G (g k) ∧ (Λk k : Set (Fin D.R.r → D.host.E)) = GlobalTheory.AdLat.latOf (maximalRealSubfield D.host.E) (g k) (Λ : Set (Fin D.R.r → D.host.E)) ∧ (Λk k).FG ∧ Submodule.span D.host.E (Λk k : Set (Fin D.R.r → D.host.E)) = ⊤ ∧ (∀ τ ∈ ((U σ).X k).Ψ, gram τ G (u k τ) = G.map τ) ∧ (∀ γ ∈ ((U σ).X k).Γ, ∃ γ' : GL (Fin D.R.r) D.host.E, (IsUStab G (Λk k) γ' ∧ ∀ x ∈ Λk k, ∃ y ∈ Λk k, (γ' : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec x - x = l.M • y) ∧ ∀ τ ∈ ((U σ).X k).Ψ, u k τ * (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ = (γ' : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * u k τ) ∧ ∀ γ' : GL (Fin D.R.r) D.host.E, (IsUStab G (Λk k) γ' ∧ ∀ x ∈ Λk k, ∃ y ∈ Λk k, (γ' : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec x - x = l.M • y) → ∃ γ ∈ ((U σ).X k).Γ, ∀ τ ∈ ((U σ).X k).Ψ, u k τ * (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ = (γ' : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * u k τ) ∧ ∀ k k', GlobalTheory.UCls.UEquiv (IsCMField.complexConj D.host.E) G (Λ : Set (Fin D.R.r → D.host.E)) l.M (g k) (g k') → k = k' := by
  intro D j H Dw l Xo c U dict hL σ hσ
  obtain ⟨Kf, th, hr, hK, hth, hD, -⟩ := hL.dictU σ hσ
  obtain ⟨hr', hm⟩ := hL.modelW σ hσ
  exact GlobalTheory.LevGeo.Reps.core D (D.sp.W j) D.R.r hr (U σ).Comp (U σ).X (dict σ) Kf th l.M hK hth hD hm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLevelComponentsDoubleCosetsCongruenceStatement
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalLevel_components_doubleCosets_congruence : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → ∀ σ, GoodEmb c σ → ∃ (G : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) (Λ : Submodule (𝓞 D.host.E) (Fin D.R.r → D.host.E)) (g : (U σ).Comp → Matrix (Fin D.R.r) (Fin D.R.r) (GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E)) (Λk : (U σ).Comp → Submodule (𝓞 D.host.E) (Fin D.R.r → D.host.E)) (u : (U σ).Comp → (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ), GlobalTheory.UCls.SelfDualLat G Λ ∧ (∀ k, ((U σ).X k).Gm = G ∧ GlobalTheory.UCls.IsUA (IsCMField.complexConj D.host.E) G (g k) ∧ (Λk k : Set (Fin D.R.r → D.host.E)) = GlobalTheory.AdLat.latOf (maximalRealSubfield D.host.E) (g k) (Λ : Set (Fin D.R.r → D.host.E)) ∧ (Λk k).FG ∧ Submodule.span D.host.E (Λk k : Set (Fin D.R.r → D.host.E)) = ⊤ ∧ (∀ τ ∈ ((U σ).X k).Ψ, gram τ G (u k τ) = G.map τ) ∧ (∀ γ ∈ ((U σ).X k).Γ, ∃ γ' : GL (Fin D.R.r) D.host.E, (IsUStab G (Λk k) γ' ∧ ∀ x ∈ Λk k, ∃ y ∈ Λk k, (γ' : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec x - x = l.M • y) ∧ ∀ τ ∈ ((U σ).X k).Ψ, u k τ * (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ = (γ' : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * u k τ) ∧ ∀ γ' : GL (Fin D.R.r) D.host.E, (IsUStab G (Λk k) γ' ∧ ∀ x ∈ Λk k, ∃ y ∈ Λk k, (γ' : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec x - x = l.M • y) → ∃ γ ∈ ((U σ).X k).Γ, ∀ τ ∈ ((U σ).X k).Ψ, u k τ * (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ = (γ' : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * u k τ) ∧ ∀ k k', GlobalTheory.UCls.UEquiv (IsCMField.complexConj D.host.E) G (Λ : Set (Fin D.R.r → D.host.E)) l.M (g k) (g k') → k = k' := by
  first | exact @GlobalTheory.LevGeo.Reps.components_double_cosets | exact GlobalTheory.LevGeo.Reps.components_double_cosets | (intros; apply GlobalTheory.LevGeo.Reps.components_double_cosets <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFiniteVectorsIrreducibleUnitaryUnitaryGroupPQ
open Matrix

noncomputable section

namespace GlobalTheory.KFinLinkPort

open GlobalTheory.KFinVec
open ReciprocityTheory.ChartRestriction.DS (smD smE smE_apply isDerivedOn_smE dS dS_eq_actM actM)
open CompanionTheory.D.gk.HC (KF)

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem dRep_eq_dS (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (X : Matrix (Fin n) (Fin n) ℂ) (w : H) :
    Formalism.L2.Theta.dRep σ X w = dS σ X w := by
  unfold Formalism.L2.Theta.dRep dS
  congr 1

theorem isAdmissible_of [CompleteSpace H] (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ)
    (hirr : Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) σ) : IsAdmissible ε σ := by
  rintro S ⟨hf, -, hK, -⟩
  have hfin : FiniteDimensional ℂ (Formalism.MainNotions.BridgeCPX.eqImg (fun k : Formalism.REAL.KG ε => σ (Formalism.REAL.toMK k)) S) :=
    (CompanionTheory.HCMult.harish_chandra_multiplicity : Formalism.MainNotions.BridgeCPX.HCMult) n ε H σ hσ hirr S hf hK
  have hle : kIsotypic ε σ S ≤ Formalism.MainNotions.BridgeCPX.eqImg (fun k : Formalism.REAL.KG ε => σ (Formalism.REAL.toMK k)) S :=
    iSup_le fun T => le_sSup ⟨T.1, fun a v w h => T.2 _ a.2 v w h, rfl⟩
  exact Submodule.finiteDimensional_of_le hle

theorem isLieStable_of [CompleteSpace H] (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ)
    (hirr : Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) σ) : IsLieStable ε σ (kFinSub ε σ) := by
  intro X hX v hv
  obtain ⟨h1, h2⟩ := CompanionTheory.D.gk.HC.K_finite_smooth_vectors n ε H σ hσ hirr
  have hvS : v ∈ smD ε σ := h1 v hv
  rw [dRep_eq_dS]
  have e := dS_eq_actM (isDerivedOn_smE hσ) hX ⟨v, hvS⟩
  simp only [] at e
  rw [e]
  simp only [actM, LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul]
  exact Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ =>
    Submodule.smul_mem _ _ (h2 a b ⟨v, hvS⟩ hv)

theorem lieIrr_of [CompleteSpace H] (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ)
    (hirr : Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) σ) (S : Submodule ℂ H) (hS : S ≤ kFinSub ε σ)
    (hL : IsLieStable ε σ S) : S = ⊥ ∨ S = kFinSub ε σ := by
  obtain ⟨h1, -⟩ := CompanionTheory.D.gk.HC.K_finite_smooth_vectors n ε H σ hσ hirr
  let N : Submodule ℂ (smD ε σ) := S.comap (smD ε σ).subtype
  have hNK : (N : Set (smD ε σ)) ⊆ KF ε σ := fun v hv => hS hv
  have hst : ∀ a b, ∀ v ∈ N, smE ε σ a b v ∈ N := by
    intro a b v hv
    show ((smE ε σ a b v : smD ε σ) : H) ∈ S
    rw [smE_apply hσ]
    have e1 := hL _ (ReciprocityTheory.ChartRestriction.DS.SmDerA.inG_cpart1 ε (Matrix.single a b 1)) (v : H) hv
    have e2 := hL _ (ReciprocityTheory.ChartRestriction.DS.SmDerA.inG_cpart2 ε (Matrix.single a b 1)) (v : H) hv
    rw [dRep_eq_dS] at e1 e2
    exact S.add_mem e1 (S.smul_mem _ e2)
  rcases GlobalTheory.HcPort.uIrr n ε H σ hσ hirr N hNK hst with h | h
  · left
    refine eq_bot_iff.2 fun v hv => ?_
    have hvN : (⟨v, h1 v (hS hv)⟩ : smD ε σ) ∈ N := hv
    rw [h] at hvN
    have := (Submodule.mem_bot ℂ).1 hvN
    exact (Submodule.mem_bot ℂ).2 (congrArg Subtype.val this)
  · right
    refine le_antisymm hS fun v hv => ?_
    have hvK : (⟨v, h1 v hv⟩ : smD ε σ) ∈ KF ε σ := hv
    rw [← h] at hvK
    exact hvK

end GlobalTheory.KFinLinkPort

namespace GlobalTheory.KFinLinkPort

theorem kFiniteVectors_irreducibleUnitary_unitaryGroupPQ : GlobalTheory.Published.KFiniteVectorsUnitary := by
  intro n ε H _ _ _ _ σ hσ hirr
  exact ⟨GlobalTheory.KFinLinkPort.isAdmissible_of hσ hirr,
    GlobalTheory.HcPort.kFiniteVectors_analytic_indefiniteUnitary n ε H σ hσ hirr,
    GlobalTheory.T.dense_kFinite_vectors_unitaryGroupRep n ε H σ hσ,
    GlobalTheory.KFinLinkPort.isLieStable_of hσ hirr,
    fun S hS hL => GlobalTheory.KFinLinkPort.lieIrr_of hσ hirr S hS hL⟩

end GlobalTheory.KFinLinkPort

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFunOPosSigIff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.Grid (neg)
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.RallisBottom

variable {D : D7}

def posSig (A : HSp D) : HSp D := { A with sig := fun _ => (A.rank, 0) }

theorem posSig_sigOK {A : HSp D} (h : A.gram = 1) : (posSig A).SigOK := fun τ => by
  have e : (posSig A).gram.map τ = 1 := by
    show A.gram.map τ = 1
    rw [h]; exact Matrix.map_one _ (map_zero τ) (map_one τ)
  show Formalism.UG.HasSignature ((posSig A).gram.map τ) A.rank 0
  rw [e]
  exact GlobalTheory.Proof.GenusMassSignature.hasSignature_of_posDef Matrix.PosDef.one

theorem thetaFunO_posSig_iff {ψ : AddChar (AF D.host.F) ℂ} {A WW : HSp D} (f : WO (neg A) WW → ℂ) :
    IsThetaFunO ψ (neg (posSig A)) WW f ↔ IsThetaFunO ψ (neg A) WW f :=
  ⟨fun h => ⟨h.1, h.2, h.3, h.4⟩, fun h => ⟨h.1, h.2, h.3, h.4⟩⟩

theorem isWeil_posSig {ψ : AddChar (AF D.host.F) ℂ} {A WW : HSp D} {χA χW : (AE D)ˣ →* Circle} {ω : GlobalTheory.Grid.WRep A WW}
    (h : GlobalTheory.Grid.IsWeil ψ true A WW χA χW ω) : GlobalTheory.Grid.IsWeil ψ true (posSig A) WW χA χW ω := by
  unfold GlobalTheory.Grid.IsWeil at h ⊢
  exact
    { std := h.std
      hecS := h.hecS
      hecT := h.hecT
      resS := h.resS
      resT := h.resT
      om_pres := fun p f hf => (thetaFunO_posSig_iff (A := A) (WW := WW) _).2 (h.om_pres p f ((thetaFunO_posSig_iff (A := A) (WW := WW) f).1 hf))
      om_heis := fun g k w f hf => h.om_heis g k w f ((thetaFunO_posSig_iff (A := A) (WW := WW) f).1 hf)
      om_aut := fun γ hγ γ' hγ' f hf => h.om_aut γ hγ γ' hγ' f ((thetaFunO_posSig_iff (A := A) (WW := WW) f).1 hf)
      om_cont := fun f hf => h.om_cont f ((thetaFunO_posSig_iff (A := A) (WW := WW) f).1 hf)
      om_unit := fun μ 𝓕 h1 h2 p f hf => h.om_unit μ 𝓕 h1 h2 p f ((thetaFunO_posSig_iff (A := A) (WW := WW) f).1 hf)
      om_split := fun e he g k h1 h2 x y h3 h4 =>
        (h.om_split e he g k h1 h2 x y h3 h4).imp fun _ hr => ⟨hr.1, fun ℓ hℓ f hf =>
          hr.2 ℓ (fun u hu f hf => hℓ u hu f ((thetaFunO_posSig_iff (A := A) (WW := WW) f).2 hf)) f ((thetaFunO_posSig_iff (A := A) (WW := WW) f).1 hf)⟩ }

theorem isVacO_posSig {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {A WW : HSp D} {sA sW LA LW} {f : WO (neg A) WW → ℂ}
    (h : IsVacO ψ θ (neg A) WW sA sW LA LW f) : IsVacO ψ θ (neg (posSig A)) WW sA sW LA LW f :=
  ⟨h.1, ⟨h.2.inf, (thetaFunO_posSig_iff (A := A) (WW := WW) f).2 h.2.theta, h.2.lat, h.2.fock, h.2.norm⟩⟩

variable {T : Type}

def Tri.posSig {A A' WW : HSp D} (X : Tri T A A' WW) : Tri T (posSig A) A' WW :=
  ⟨⟨X.rA.Λ, X.rA.β, X.rA.s, X.rA.B⟩, X.rA', X.rW, X.ω, X.ω', X.vac, X.vac', X.e, X.c, X.f, X.f', X.m, X.fd, X.m', X.fd'⟩

variable {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}

theorem isBottomTri_posSig {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW} (hX : IsBottomTri W i j X) :
    IsBottomTri W i j (Tri.posSig X) := by
  refine ⟨hX.rank, hX.rank', hX.std, hX.std', hX.stdW, ?_⟩
  exact
    { rank := hX.is.rank
      rigA := hX.is.rigA
      rigA' := hX.is.rigA'
      rigW := hX.is.rigW
      weil := fun t => isWeil_posSig (hX.is.weil t)
      weil' := hX.is.weil'
      isVac := isVacO_posSig hX.is.isVac
      isVac' := hX.is.isVac'
      idem := hX.is.idem
      expo := hX.is.expo
      fst := hX.is.fst
      snd := hX.is.snd
      meas := hX.is.meas
      meas' := hX.is.meas' }

theorem sigOK_posSig {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW} (hX : IsBottomTri W i j X) :
    (posSig A).SigOK := posSig_sigOK hX.std.1

end GlobalTheory.RallisBottom

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdmissibleSubTop
open Matrix
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.PsCo.TrAdm

open ReciprocityTheory.ChartRestriction.DS CompanionTheory.D.gk.HC GlobalTheory.HcPort Formalism.MainNotions.S

section

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

def kfSub (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Submodule ℂ (smD ε σ) where
  carrier := KF ε σ
  add_mem' := by
    rintro a b ⟨S, hS, ha, hSK⟩ ⟨T, hT, hb, hTK⟩
    refine ⟨S ⊔ T, inferInstance, Submodule.add_mem_sup ha hb, fun g hg v hv => ?_⟩
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 hv
    rw [← hxy, map_add (f := _)]
    exact Submodule.add_mem_sup (hSK g hg x hx) (hTK g hg y hy)
  zero_mem' := ⟨⊥, inferInstance, Submodule.zero_mem _, fun g _ v hv => by
    rw [(Submodule.mem_bot ℂ).1 hv, map_zero]; exact Submodule.zero_mem _⟩
  smul_mem' := fun c _ ⟨S, hS, ha, hSK⟩ => ⟨S, hS, by simpa using S.smul_mem c ha, hSK⟩

theorem kStableSub_iSup {ι : Type} {E : Fin n → Fin n → Module.End ℂ (smD ε σ)} (S : ι → Submodule ℂ (smD ε σ))
    (h : ∀ i, IsKStableSub ε E (S i)) : IsKStableSub ε E (⨆ i, S i) := by
  intro a b hab x hx
  refine Submodule.iSup_induction S (motive := fun x => E a b x ∈ ⨆ i, S i) hx (fun i y hy => ?_) ?_ ?_
  · exact Submodule.mem_iSup_of_mem i (h i a b hab y hy)
  · simp
  · intro y z hy hz; rw [map_add (f := _)]; exact Submodule.add_mem _ hy hz

end

theorem isAdmissibleSub_top (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ)
    (hirr : Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) σ) : GlobalTheory.GKModule.IsAdmissibleSub ε σ ⊤ := by
  classical
  intro Λ
  have hD := isDerivedOn_smE hσ
  set A := {v : smD ε σ | v ∈ KF ε σ ∧ IsKHWVec ε (smE ε σ) Λ v}
  have hAf : FiniteDimensional ℂ (Submodule.span ℂ A) := uAdm n ε H σ hσ hirr Λ
  have hAK : Submodule.span ℂ A ≤ kfSub ε σ := Submodule.span_le.2 fun v hv => hv.1
  let b := Module.finBasis ℂ (Submodule.span ℂ A)
  let M : Submodule ℂ (smD ε σ) := ⨆ i, Formalism.REAL.kSpan ε (smE ε σ) (b i : smD ε σ)
  have hbi : ∀ i, FiniteDimensional ℂ (Formalism.REAL.kSpan ε (smE ε σ) (b i : smD ε σ)) ∧
      IsKStableSub ε (smE ε σ) (Formalism.REAL.kSpan ε (smE ε σ) (b i : smD ε σ)) := fun i =>
    kSpan_fin_B K_finite_smooth_vectors hσ hirr (hAK (b i).2)
  haveI : ∀ i, FiniteDimensional ℂ (Formalism.REAL.kSpan ε (smE ε σ) (b i : smD ε σ)) := fun i => (hbi i).1
  have hMf : FiniteDimensional ℂ M := Submodule.finiteDimensional_iSup _
  have hMK : IsKStableSub ε (smE ε σ) M := kStableSub_iSup _ fun i => (hbi i).2
  have hAM : Submodule.span ℂ A ≤ M := by
    intro x hx
    have h1 := congrArg (fun z : Submodule.span ℂ A => (z : smD ε σ)) (b.sum_repr ⟨x, hx⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h1
    rw [← h1]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.mem_iSup_of_mem i (Formalism.REAL.mem_compact_span_self _))
  let T : Submodule ℂ H := M.map (smD ε σ).subtype
  have hTf : FiniteDimensional ℂ T := Module.Finite.map _ _
  have hTK := kStable_of_isKStableSub hσ hD M hMf hMK
  refine Submodule.finiteDimensional_of_le (S₂ := T) (sSup_le fun S hS' => ?_)
  have hS := hS'.2
  obtain ⟨hSf, hSK, hirrS, -, -⟩ := id hS
  have hSD : S ≤ smD ε σ := fun v hv => (K_finite_smooth_vectors n ε H σ hσ hirr).1 v ⟨S, hSf, hv, hSK⟩
  obtain ⟨w, hwS, hw0, hwΛ⟩ := exists_isKHWVec_of_isKTypeOf hσ hD hS hSD
  have hwA : w ∈ A := ⟨⟨S, hSf, hwS, hSK⟩, hwΛ⟩
  have hwM : w ∈ M := hAM (Submodule.subset_span hwA)
  have hST : Formalism.MainNotions.S.IsKStableOn ε σ (S ⊓ T) := by
    intro g hg v hv
    refine ⟨hSK g hg v hv.1, ?_⟩
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hv.2
    obtain ⟨z, hz, hzeq⟩ := hTK g hg y hy
    exact Submodule.mem_map.2 ⟨z, hz, hzeq⟩
  rcases hirrS _ inf_le_left hST with h0 | hEq
  · exfalso
    have hmem : (w : H) ∈ S ⊓ T := ⟨hwS, Submodule.mem_map_of_mem hwM⟩
    rw [h0, Submodule.mem_bot] at hmem
    exact hw0 (Subtype.ext hmem)
  · rw [← hEq]; exact inf_le_right

end GlobalTheory.PsCo.TrAdm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFiniteModuleIrreducibleOfIrreducibleUnitaryRep
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFiniteModuleIrreducibleOfIrreducibleUnitaryRep
open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.KFinIrr

theorem smE_eq {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hK : IsKMod ε σ D E) (v : D) (hv : (v : H) ∈ ReciprocityTheory.ChartRestriction.DS.smD ε σ)
    (a b : Fin n) :
    ((ReciprocityTheory.ChartRestriction.DS.smE ε σ a b ⟨v, hv⟩ : ReciprocityTheory.ChartRestriction.DS.smD ε σ) : H) = ((E a b v : D) : H) := by
  have hσ' : ReciprocityTheory.ChartRestriction.DS.IsURepOn (ReciprocityTheory.ChartRestriction.DS.UJset ε) σ := hσ
  have key : ∀ X, ReciprocityTheory.ChartRestriction.DS.inG ε X →
      ReciprocityTheory.ChartRestriction.DS.dS σ X (v : H) = ∑ c, ∑ d, X c d • ((E c d v : D) : H) := fun X hX =>
    (hK.real X hX v).deriv
  rw [ReciprocityTheory.ChartRestriction.DS.smE_apply hσ']
  change ReciprocityTheory.ChartRestriction.DS.dS σ _ (v : H) + Complex.I • ReciprocityTheory.ChartRestriction.DS.dS σ _ (v : H) = _
  rw [key _ (ReciprocityTheory.ChartRestriction.DS.SmDerA.inG_cpart1 ε _), key _ (ReciprocityTheory.ChartRestriction.DS.SmDerA.inG_cpart2 ε _)]
  have hz : ∀ c d, ReciprocityTheory.ChartRestriction.DS.S7.cpart1 ε (Matrix.single a b 1) c d +
      Complex.I * ReciprocityTheory.ChartRestriction.DS.S7.cpart2 ε (Matrix.single a b 1) c d = Matrix.single a b (1 : ℂ) c d := by
    intro c d
    have := congrFun (congrFun (ReciprocityTheory.ChartRestriction.DS.SmDerA.cpart_decomp ε (Matrix.single a b 1)) c) d
    rw [this]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  calc _ = ∑ c, ∑ d, (ReciprocityTheory.ChartRestriction.DS.S7.cpart1 ε (Matrix.single a b 1) c d +
        Complex.I * ReciprocityTheory.ChartRestriction.DS.S7.cpart2 ε (Matrix.single a b 1) c d) • ((E c d v : D) : H) := by
          simp only [Finset.smul_sum, add_smul, Finset.sum_add_distrib, smul_smul]
    _ = ∑ c, ∑ d, Matrix.single a b (1 : ℂ) c d • ((E c d v : D) : H) := by simp only [hz]
    _ = ((E a b v : D) : H) := by
          simp [Matrix.single_apply, ite_smul, ite_and]

theorem kMod_irred : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D), CompleteSpace H → IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → IsKMod ε σ D E → ∀ N : Submodule ℂ D, (∀ a b, ∀ x ∈ N, E a b x ∈ N) → N = ⊥ ∨ N = ⊤ := by
  intro n ε H _ _ σ D E hc hσ hirr hK N hN
  haveI := hc
  have hle : D ≤ ReciprocityTheory.ChartRestriction.DS.smD ε σ := fun v hv =>
    (CompanionTheory.D.gk.HC.K_finite_smooth_vectors n ε H σ hσ hirr).1 v ((hK.mem v).1 hv)
  let ι : D →ₗ[ℂ] ReciprocityTheory.ChartRestriction.DS.smD ε σ := Submodule.inclusion hle
  have hι : Function.Injective ι := Submodule.inclusion_injective hle
  have hcomm : ∀ a b (x : D), ReciprocityTheory.ChartRestriction.DS.smE ε σ a b (ι x) = ι (E a b x) := fun a b x =>
    Subtype.ext (smE_eq hσ hK x (hle x.2) a b)
  let N' : Submodule ℂ (ReciprocityTheory.ChartRestriction.DS.smD ε σ) := N.map ι
  have hN'K : (N' : Set (ReciprocityTheory.ChartRestriction.DS.smD ε σ)) ⊆ CompanionTheory.D.gk.HC.KF ε σ := by
    rintro _ ⟨x, -, rfl⟩
    exact (hK.mem x).1 x.2
  have hN'st : ∀ a b, ∀ v ∈ N', ReciprocityTheory.ChartRestriction.DS.smE ε σ a b v ∈ N' := by
    rintro a b _ ⟨x, hx, rfl⟩
    rw [hcomm]
    exact ⟨_, hN a b x hx, rfl⟩
  rcases GlobalTheory.HcPort.uIrr n ε H σ hσ hirr N' hN'K hN'st with h | h
  · left
    rw [eq_bot_iff]
    intro x hx
    have hx' : ι x ∈ N' := ⟨x, hx, rfl⟩
    rw [h, Submodule.mem_bot] at hx'
    rw [Submodule.mem_bot]
    exact hι (by rw [hx', map_zero])
  · right
    rw [eq_top_iff]
    intro x _
    have hx' : ι x ∈ (N' : Set (ReciprocityTheory.ChartRestriction.DS.smD ε σ)) := by
      rw [h]
      exact (hK.mem x).1 x.2
    obtain ⟨y, hy, hyx⟩ := hx'
    rw [hι hyx] at hy
    exact hy

end GlobalTheory.KFinIrr
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFiniteModuleIrreducibleOfIrreducibleUnitaryRepStatement
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset)
open CompanionTheory.D.LK (IsKMod)

theorem GlobalTheory.T.kFiniteModule_irreducible_of_irreducible_unitaryRep :
    ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H)
      (E : Fin n → Fin n → Module.End ℂ D),
      CompleteSpace H → IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → IsKMod ε σ D E →
      ∀ N : Submodule ℂ D, (∀ a b, ∀ x ∈ N, E a b x ∈ N) → N = ⊥ ∨ N = ⊤ :=
  @GlobalTheory.KFinIrr.kMod_irred
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsNormEqUnderOfIdemAt
noncomputable section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open GlobalTheory.ChiGrid GlobalTheory.FunObj.SqNum

namespace GlobalTheory.FunObj.NormLevel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem absNorm_eq_under_of_idemAt {P : HeightOneSpectrum (𝓞 D.host.E)} {e : Formalism.L2.Theta.AE D}
    (he : Formalism.L2.NTheta.IsIdemAt e P) :
    Ideal.absNorm P.asIdeal = Ideal.absNorm (P.asIdeal.under (𝓞 D.host.F)) := by
  classical
  have hns := Formalism.IndefR.Fin.idemAt_split he
  let c : 𝓞 D.host.E ≃+* 𝓞 D.host.E := Formalism.DivisionValues.cO D.host.E
  have hc : ∀ x : 𝓞 D.host.E, ((c x : 𝓞 D.host.E) : D.host.E) = star (x : D.host.E) := fun x => rfl
  have hcc : ∀ x, c (c x) = x := fun x => RingOfIntegers.ext (by rw [hc, hc, star_star])
  have hcF : ∀ a : 𝓞 D.host.F, c (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a) = algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a :=
    fun a => RingOfIntegers.ext (by
      rw [hc]
      exact Formalism.IndefR.Eqv.star_algebraMapF D (a : D.host.F))
  let Q : Ideal (𝓞 D.host.E) := P.asIdeal.comap (c : 𝓞 D.host.E →+* 𝓞 D.host.E)
  have hQp : Q.IsPrime := Ideal.comap_isPrime _ _
  have hQv : Q.under (𝓞 D.host.F) = P.asIdeal.under (𝓞 D.host.F) := by
    ext a
    show c (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a) ∈ P.asIdeal ↔ algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a ∈ P.asIdeal
    rw [hcF]
  have hne : Q ≠ P.asIdeal := by
    intro h
    apply hns
    intro x hx
    have hx' : c x ∈ Q := by
      show c (c x) ∈ P.asIdeal
      rw [hcc]; exact hx
    rw [h] at hx'
    exact ⟨c x, hx', hc x⟩
  set p := P.asIdeal.under (𝓞 D.host.F) with hp
  have hp0 : p ≠ ⊥ := by
    obtain ⟨x, hxP, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
    exact Ideal.comap_ne_bot_of_integral_mem hx0 hxP (Algebra.IsIntegral.isIntegral x)
  have hpP : p.IsPrime := Ideal.IsPrime.comap _
  have hpM : p.IsMaximal := hpP.isMaximal hp0
  haveI hl1 : P.asIdeal.LiesOver p := ⟨rfl⟩
  haveI hl2 : Q.LiesOver p := ⟨hQv.symm⟩
  have hsum := Ideal.sum_ramification_inertia_eq_finrank p (𝓞 D.host.E)
  rw [← IsFractionRing.finrank_eq (𝓞 D.host.F) D.host.F (𝓞 D.host.E) D.host.E, D.sp.cm.deg2] at hsum
  let P1 : p.primesOver (𝓞 D.host.E) := ⟨P.asIdeal, P.isPrime, hl1⟩
  let Q1 : p.primesOver (𝓞 D.host.E) := ⟨Q, hQp, hl2⟩
  have h12 : P1 ≠ Q1 := fun h => hne (congrArg Subtype.val h).symm
  have hpos : ∀ R : p.primesOver (𝓞 D.host.E),
      1 ≤ R.1.ramificationIdx (𝓞 D.host.F) * R.1.inertiaDeg (𝓞 D.host.F) := fun R =>
    Nat.mul_pos (Ideal.ramificationIdx_pos _ _) (Ideal.inertiaDeg_pos _ _)
  have hle : P1.1.ramificationIdx (𝓞 D.host.F) * P1.1.inertiaDeg (𝓞 D.host.F) +
      Q1.1.ramificationIdx (𝓞 D.host.F) * Q1.1.inertiaDeg (𝓞 D.host.F) ≤ 2 := by
    rw [← hsum, ← Finset.sum_pair (f := fun R : p.primesOver (𝓞 D.host.E) =>
      R.1.ramificationIdx (𝓞 D.host.F) * R.1.inertiaDeg (𝓞 D.host.F)) h12]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have h1 := hpos P1
  have h2 := hpos Q1
  have hef : P.asIdeal.ramificationIdx (𝓞 D.host.F) * P.asIdeal.inertiaDeg (𝓞 D.host.F) = 1 := by
    change P1.1.ramificationIdx (𝓞 D.host.F) * P1.1.inertiaDeg (𝓞 D.host.F) = 1
    omega
  have hf : P.asIdeal.inertiaDeg (𝓞 D.host.F) = 1 := Nat.eq_one_of_mul_eq_one_left hef
  rw [← Ideal.absNorm_pow_inertiaDeg p P.asIdeal, hf, pow_one]

variable {T : Type} {L : LevCh D T}


open Classical in
theorem absNorm_w (P : Places L) {v : HeightOneSpectrum (𝓞 D.host.F)} (hv : v ∈ P.S0) :
    Ideal.absNorm (P.w v).asIdeal = Ideal.absNorm v.asIdeal := by
  have hv' : v ∈ insert P.v0 (S1 D) := by
    rcases P.mem_S0_of_sum_eq.1 hv with h | h
    · rw [h]; exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem h
  obtain ⟨e, he⟩ := P.w_split v hv'
  have hu : (P.w v).asIdeal.under (𝓞 D.host.F) = v.asIdeal := by
    rw [← HeightOneSpectrum.under_asIdeal, P.under_w hv]
  rw [absNorm_eq_under_of_idemAt he, hu]

theorem absNorm_condE : ∀ {D : D7} {T : Type} {L : LevCh D T} (P : Places L), Ideal.absNorm (GlobalTheory.FunObj.SqNum.condE P) = GlobalTheory.FunObj.SqNum.levQ P := by
  intro D T L P
  unfold GlobalTheory.FunObj.SqNum.condE GlobalTheory.FunObj.SqNum.levQ
  rw [map_prod]
  refine Finset.prod_congr rfl fun v hv => ?_
  rw [map_pow, absNorm_w P hv]

end GlobalTheory.FunObj.NormLevel

end
end
