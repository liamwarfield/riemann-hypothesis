module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteSupportMulLatticeStabilizer
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsKFiniteReproducingFunction
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KFiniteDecompositionAssembleRealPlaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivariantUnitConstantsGoodEmbedding
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOneParameterSubgroupTransposeGramRealPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealmapsIsomorphism
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleMixedModelBaseValueEquivariant
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsConvergeThetaFunctions

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspFormKFiniteApprox
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AveragedAutomorphicFunctionKFinite
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsContRepLeftRep
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta MeasureTheory Matrix

noncomputable section

namespace GlobalTheory.LeftRegularRepresentation

def leftRep {K : Type} [Group K] (F : Submodule ℂ (K → ℂ)) (hF : ∀ φ ∈ F, ∀ a : K, (fun k => φ (a * k)) ∈ F) :
    Representation ℂ K F where
  toFun a :=
    { toFun := fun φ => ⟨fun k => φ.1 (a⁻¹ * k), hF _ φ.2 _⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by
    ext φ k
    simp
  map_mul' a b := by
    ext φ k
    simp [mul_assoc]

theorem dual_mem_span {K : Type} (F : Submodule ℂ (K → ℂ)) [FiniteDimensional ℂ F] (ℓ : Module.Dual ℂ F) :
    ℓ ∈ Submodule.span ℂ (Set.range fun y : K => (LinearMap.proj y).comp F.subtype) := by
  have h : (Submodule.span ℂ (Set.range fun y : K =>
      ((LinearMap.proj y).comp F.subtype : Module.Dual ℂ F))) = ⊤ := by
    refine Submodule.span_eq_top_of_ne_zero fun z hz => ?_
    by_contra hc
    push Not at hc
    exact hz (Subtype.ext (funext fun y => hc _ ⟨y, rfl⟩))
  rw [h]
  trivial

theorem isContRep_leftRep {K : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    (F : Submodule ℂ (K → ℂ)) [FiniteDimensional ℂ F] (hF : ∀ φ ∈ F, ∀ a : K, (fun k => φ (a * k)) ∈ F)
    (hc : ∀ φ ∈ F, Continuous φ) : GlobalTheory.Published.AutFin.IsContRep (leftRep F hF) := by
  intro ℓ w
  induction dual_mem_span F ℓ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, rfl⟩ := hx
    exact (hc _ w.2).comp (continuous_inv.mul continuous_const)
  | zero => exact continuous_const
  | add x y _ _ hx hy => exact hx.add hy
  | smul a x _ hx => exact hx.const_smul a

theorem conv_mem {K : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsHaarMeasure]
    (F : Submodule ℂ (K → ℂ)) (hF : ∀ φ ∈ F, ∀ a : K, (fun k => φ (a * k)) ∈ F)
    (hc : ∀ φ ∈ F, Continuous φ) {e : K → ℂ} (he : e ∈ F) {f : K → ℂ} (hf : Continuous f) :
    (fun a => ∫ k, e k * f (a * k) ∂μ) ∈ GlobalTheory.Published.AutFin.coeffSpan (leftRep F hF) := by
  have hi : ∀ φ : F, Integrable (fun k => φ.1 k * f k) μ := fun φ =>
    ((hc _ φ.2).mul hf).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let ℓ : Module.Dual ℂ F :=
    { toFun := fun φ => ∫ k, φ.1 k * f k ∂μ
      map_add' := fun a b => by
        rw [← integral_add (hi a) (hi b)]
        simp only [Submodule.coe_add, Pi.add_apply, add_mul]
      map_smul' := fun c a => by
        simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]
        exact integral_const_mul _ _ }
  refine Submodule.subset_span ⟨ℓ, ⟨e, he⟩, funext fun a => ?_⟩
  change _ = ∫ k, e (a⁻¹ * k) * f k ∂μ
  rw [← integral_mul_left_eq_self (fun k => e (a⁻¹ * k) * f k) a]
  simp only [inv_mul_cancel_left]

theorem kFinAt_avg : ∀ (D : Formalism.BasicNotions.D7) (θ : Formalism.IndefR.Datum.InfFam D), Formalism.L2.Theta.IsInfFam θ → ∀ (N : GlobalTheory.Grid.Node D) (ψ : Formalism.L2.Theta.GA D (GlobalTheory.Grid.Node.V N) → ℂ), Formalism.L2.Theta.IsAutFunSm θ (GlobalTheory.Grid.Node.V N) ψ → ∀ (τ : Formalism.BasicNotions.Rows.Data.Tau (Formalism.BasicNotions.D7.what₂ D)) (e : ↥(Formalism.REAL.KG (Formalism.IndefR.Mult.DSModel.ε (GlobalTheory.Grid.Node.M N) τ)) → ℂ), GlobalTheory.TypeSum.KFinFun (Formalism.IndefR.Mult.DSModel.ε (GlobalTheory.Grid.Node.M N) τ) e → GlobalTheory.CuspKFin.KFinAt θ N τ (GlobalTheory.SeriesToClosure.avg θ (GlobalTheory.Grid.Node.V N) τ (Formalism.IndefR.Mult.DSModel.ε (GlobalTheory.Grid.Node.M N) τ) (Formalism.IndefR.Mult.DSModel.fr (GlobalTheory.Grid.Node.M N) τ) e ψ) := by
  intro D θ hθ N ψ hψ τ e he
  obtain ⟨F, hfd, heF, hc, hF⟩ := he
  haveI : IsTopologicalGroup (GA D N.V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have hP := N.M.fr_unit τ
  have hJ := N.M.fr_gram τ
  have hmem := GlobalTheory.Published.AutFin.conj_mem_UH hP hJ
  have hd : IsUnit (N.M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 hP
  have hK : Continuous fun k : Formalism.REAL.KG (N.M.ε τ) => Formalism.REAL.toMK k :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hk : Continuous (GlobalTheory.Published.AutFin.kAt θ N.V τ (N.M.ε τ) (N.M.fr τ)) :=
    (GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ N.V τ).comp_continuous
      ((continuous_const.matrix_mul hK).matrix_mul continuous_const) hmem
  have hmul : ∀ a b, GlobalTheory.Published.AutFin.kAt θ N.V τ (N.M.ε τ) (N.M.fr τ) (a * b) =
      GlobalTheory.Published.AutFin.kAt θ N.V τ (N.M.ε τ) (N.M.fr τ) a * GlobalTheory.Published.AutFin.kAt θ N.V τ (N.M.ε τ) (N.M.fr τ) b := by
    intro a b
    unfold GlobalTheory.Published.AutFin.kAt
    rw [← GlobalTheory.PointAtPlaceHom.atTau_mul hθ N.V τ (hmem a) (hmem b)]
    congr 1
    have e1 : Formalism.REAL.toMK (a * b) = Formalism.REAL.toMK a * Formalism.REAL.toMK b := rfl
    rw [e1]
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hd]
  refine ⟨F, inferInstance, inferInstance, hfd, leftRep F fun φ h a => (hF φ h a).1,
    isContRep_leftRep F _ hc, fun x => ?_⟩
  have h := conv_mem (Formalism.REAL.muK (N.M.ε τ)) F (fun φ h a => (hF φ h a).1) hc heF
    (f := fun k => ψ (x * GlobalTheory.Published.AutFin.kAt θ N.V τ (N.M.ε τ) (N.M.fr τ) k))
    (hψ.cont.comp (continuous_const.mul hk))
  simp only [hmul, ← mul_assoc] at h
  exact h

end GlobalTheory.LeftRegularRepresentation

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AveragedAutomorphicFunctionKFinite
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size

noncomputable section

namespace GlobalTheory.CuspKFinAvg

open Formalism.REAL Matrix

end GlobalTheory.CuspKFinAvg

namespace GlobalTheory.CuspKFin

open Formalism.REAL Matrix MeasureTheory

theorem kFinAt_avg : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (N : GlobalTheory.Grid.Node D) (ψ : GA D N.V → ℂ),
    IsAutFunSm θ N.V ψ → ∀ (τ : D.what₂.Tau) (e : Formalism.REAL.KG (N.M.ε τ) → ℂ), GlobalTheory.TypeSum.KFinFun (N.M.ε τ) e →
    GlobalTheory.CuspKFin.KFinAt θ N τ (GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) e ψ) := by
  first
  | exact @_root_.GlobalTheory.LeftRegularRepresentation.kFinAt_avg
  | exact _root_.GlobalTheory.LeftRegularRepresentation.kFinAt_avg
  | (apply _root_.GlobalTheory.LeftRegularRepresentation.kFinAt_avg <;> assumption)
  | (intros; apply _root_.GlobalTheory.LeftRegularRepresentation.kFinAt_avg <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LeftRegularRepresentation.kFinAt_avg <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LeftRegularRepresentation.kFinAt_avg ..)

end GlobalTheory.CuspKFin

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AveragedAutomorphicFunctionKFiniteStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.averaged_automorphic_function_K_finite : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (N : GlobalTheory.Grid.Node D) (ψ : GA D N.V → ℂ), IsAutFunSm θ N.V ψ → ∀ (τ : D.what₂.Tau) (e : Formalism.REAL.KG (N.M.ε τ) → ℂ), GlobalTheory.TypeSum.KFinFun (N.M.ε τ) e → GlobalTheory.CuspKFin.KFinAt θ N τ (GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) e ψ) := by
  first | exact @GlobalTheory.CuspKFin.kFinAt_avg | exact GlobalTheory.CuspKFin.kFinAt_avg | (intros; apply GlobalTheory.CuspKFin.kFinAt_avg <;> assumption)
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size

noncomputable section
namespace GlobalTheory.CuspKFinDecomp

theorem avg_lev : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (N : GlobalTheory.Grid.Node D) (ψ : GA D N.V → ℂ) (U : Subgroup (GA D N.V)), (∀ k ∈ U, k ∈ GfC N.V → ∀ g, ψ (g * k) = ψ g) → ∀ (τ : D.what₂.Tau) (e : Formalism.REAL.KG (N.M.ε τ) → ℂ), ∀ k ∈ U, k ∈ GfC N.V → ∀ g, GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) e ψ (g * k) = GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) e ψ g := by
  intro D θ hθ N ψ U hψ τ e k hk hkf g
  unfold GlobalTheory.SeriesToClosure.avg
  congr 1
  funext k'
  rw [mul_assoc, ← GlobalTheory.PointAtPlaceHom.comm_of_mem N.V (GlobalTheory.PointAtPlaceHom.atTau_mem N.V τ _) hkf, ← mul_assoc,
    hψ k hk hkf]

end GlobalTheory.CuspKFinDecomp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GeoAct
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GeometricAction


set_option maxHeartbeats 1000000 in
theorem geoAct : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), R.toLevCh.Is A.μ0 → R.IsModels → FWTie T R κ v₀ → (∀ i, OMPins T R κ v₀ O i) → EquivAll T R κ O → GeoAct T R κ v₀ := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ O hL hM fw hpins hall
  have ht : TieIn T R κ v₀ := ⟨fw.laws, fw.alg_eq, fw.kap, fw.hv₀, fw.chiR, fw.x0⟩
  refine GlobalTheory.GeoLevel.geoAct_of_eqAt ht hM.HW hM.gW O hpins ?_
  intro i σ hσ hV

  have hpb : T.pb = R.C.P.pb :=
    GlobalTheory.CoverHalf.primes_eq_of_halfIs T.toCore R fw.laws.toLawsM hL ((hpins i).2.tuple ()).half
  exact hall i σ hσ hV (GlobalTheory.T.exists_equivariant_unit_constants_goodEmbedding T R κ v₀ O hL ht hpb hpins i σ hσ hV)

end GlobalTheory.GeometricAction
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianSkewModelGood
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift

namespace GlobalTheory.KStableSums

def pureL {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ) :
    SInf F κ →ₗ[ℂ] ((κ → AF F) → ℂ) where
  toFun f := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ
  map_add' f g := by funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, add_mul]
  map_smul' a f := by funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]

theorem exists_sum_pure {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W)
    (ψ : AddChar (AF F) ℂ) (emb : ∀ w : InfinitePlace F, EmbOver E w) {Ψ : (Fin n × Fin d → AF F) → ℂ}
    (hΨ : Ψ ∈ GlobalTheory.SquareAgree.algD M ψ emb) :
    ∃ (m : ℕ) (f : Fin m → SInf F (Fin n × Fin d)) (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ),
      (∀ i, f i ∈ M.Pol ψ emb) ∧ (∀ i, (∀ v, φ i v ∈ GlobalTheory.WeilM.SB _) ∧ ∀ᶠ v in Filter.cofinite, φ i v = M.vac v) ∧
      Ψ = ∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i) := by
  obtain ⟨m, a, g, hg⟩ := Submodule.mem_span_set'.1 hΨ
  choose f φ hf hSB hev he using fun i => (g i).2
  refine ⟨m, fun i => a i • f i, φ, fun i => (M.Pol ψ emb).smul_mem _ (hf i), fun i => ⟨hSB i, hev i⟩, ?_⟩
  rw [← hg]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [he i]
  exact ((pureL (φ i)).map_smul (a i) (f i)).symm

def piEnd {V : Type} [AddCommGroup V] [Module ℂ V] (m : ℕ) (L : Module.End ℂ V) : Module.End ℂ (Fin m → V) :=
  LinearMap.pi fun i => L ∘ₗ LinearMap.proj i

theorem piEnd_apply {V : Type} [AddCommGroup V] [Module ℂ V] (m : ℕ) (L : Module.End ℂ V) (y : Fin m → V)
    (i : Fin m) : piEnd m L y i = L (y i) := rfl

theorem piEnd_pow_apply {V : Type} [AddCommGroup V] [Module ℂ V] (m : ℕ) (L : Module.End ℂ V) (k : ℕ)
    (y : Fin m → V) (i : Fin m) : (piEnd m L ^ k) y i = (L ^ k) (y i) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', Module.End.mul_apply, piEnd_apply, ih, pow_succ', Module.End.mul_apply]

theorem isExp_piEnd {V : Type} [AddCommGroup V] [Module ℂ V] {L U : Module.End ℂ V} (h : IsExp L U) (m : ℕ) :
    IsExp (piEnd m L) (piEnd m U) := by
  intro y l
  have hl : ∀ z : Fin m → V, l z = ∑ i, (l ∘ₗ LinearMap.single ℂ (fun _ : Fin m => V) i) (z i) := by
    intro z
    conv_lhs => rw [← Finset.univ_sum_single z]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum]
  have key : (fun k : ℕ => ((k.factorial : ℂ))⁻¹ * l ((piEnd m L ^ k) y)) =
      fun k => ∑ i, ((k.factorial : ℂ))⁻¹ * (l ∘ₗ LinearMap.single ℂ (fun _ : Fin m => V) i) ((L ^ k) (y i)) := by
    funext k
    rw [hl, Finset.mul_sum]
    simp only [piEnd_pow_apply]
  rw [key, hl]
  exact hasSum_sum fun i _ => h (y i) _

theorem exp_conj_rect {β ι : Type} [Fintype β] [DecidableEq β] [Fintype ι] [DecidableEq ι]
    (C : Matrix β ι ℂ) (A' : Matrix ι β ℂ) (hCA : C * A' = 1) (hAC : A' * C = 1) (Y : Matrix ι ι ℂ) :
    NormedSpace.exp (C * Y * A') = C * NormedSpace.exp Y * A' := by
  let f : Matrix ι ι ℂ →+* Matrix β β ℂ :=
    { toFun := fun X => C * X * A'
      map_one' := by simp [hCA]
      map_mul' := fun X Z => by
        calc C * (X * Z) * A' = C * X * (A' * C) * Z * A' := by rw [hAC, Matrix.mul_one]; simp only [Matrix.mul_assoc]
          _ = _ := by simp only [Matrix.mul_assoc]
      map_zero' := by simp
      map_add' := fun X Z => by simp [Matrix.mul_add, Matrix.add_mul] }
  have hf : Continuous f := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  open scoped Norms.Operator in
  exact (NormedSpace.map_exp f hf Y).symm

theorem atPl_zero {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)]
    [∀ i, Module ℂ (V i)] (w : ι) : atPl (V := V) w 0 = 0 := by
  unfold atPl
  exact (PiTensorProduct.mapMultilinear ℂ V V).map_update_zero (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w

theorem sumPl_single {ι : Type} [Fintype ι] [DecidableEq ι] {V : Type} [AddCommGroup V] [Module ℂ V] {κ : Type}
    [Fintype κ] (act : Matrix κ κ ℂ →ₗ[ℂ] Module.End ℂ V) (c : ι → ℂ) (w : ι) (Y : Matrix κ κ ℂ) :
    sumPl (V := fun _ : ι => V) (fun w' => act ((Pi.single w Y : ι → Matrix κ κ ℂ) w') +
        (c w' * ((Pi.single w Y : ι → Matrix κ κ ℂ) w').trace) • 1) =
      atPl (V := fun _ : ι => V) w (act Y + (c w * Y.trace) • 1) := by
  unfold sumPl
  rw [Finset.sum_eq_single w]
  · simp
  · intro w' _ hw'
    simp only [Pi.single_eq_of_ne hw', map_zero, Matrix.trace_zero, mul_zero, zero_smul, add_zero]
    exact atPl_zero w'
  · intro h; exact absurd (Finset.mem_univ w) h

theorem exists_line_upq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {β : Type} [Fintype β] [DecidableEq β] (R S : ℕ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (J : Matrix β β (AE F E)) (b : ℂ) (C : InfinitePlace F → Matrix β (Ix R S) ℂ) (θ : InfinitePlace F → Matrix β β ℂ)
    (hCM : IsCMExt F E σ) (hfr : ∀ w, IsFrame (b • J.map (piInf (τ w))) (C w)) (hθ : ∀ w, θ w * C w = C w * Jm R S)
    (k : UG (cA σ) J) (hk : At (evI F) ((k.1 : Matrix β β (AE F E)) - 1))
    (hkθ : ∀ w, Commute ((k.1 : Matrix β β (AE F E)).map (piInf (τ w))) (θ w)) :
    ∃ γ ∈ RLines (σ := σ) J, ∃ Y : InfinitePlace F → Matrix (Ix R S) (Ix R S) ℂ, IsGen τ C γ Y ∧ (∀ w, Y w ∈ upq R S) ∧
      (∀ w, IsKC (Y w)) ∧ γ (Multiplicative.ofAdd 1) = k := by
  open GlobalTheory.RealLift.KLineProof in
  have hu : (k.1 : Matrix β β (AE F E))ᵀ * J * (k.1 : Matrix β β (AE F E)).map (cA σ) = J := k.2
  have hloc : ∀ w, ∃ Y : Matrix (Ix R S) (Ix R S) ℂ, Y ∈ upq R S ∧ IsKC Y ∧
      C w * NormedSpace.exp Y = (k.1 : Matrix β β (AE F E)).map (piInf (τ w)) * C w := by
    intro w
    obtain ⟨A', hCA, hAC⟩ := GlobalTheory.RealLift.KLineProof.frame_inv (hfr w)
    refine GlobalTheory.RealLift.KLineProof.exists_gen_at (C w) A' hCA hAC (J.map (piInf (τ w))) b (hfr w).1 _ (θ w) ?_
      (hθ w) (hkθ w)
    have := congrArg (fun X => X.map (piInf (τ w))) hu
    simp only [Matrix.map_mul, GlobalTheory.RealLift.KLineProof.map_cA_map hCM, Matrix.transpose_map] at this
    exact this
  choose Y hY using hloc
  obtain ⟨γ, hγ, hgen⟩ := GlobalTheory.T.unitaryLieElements_generate_oneParamLines F E σ β R S τ J b C hCM hfr Y (fun w => (hY w).1)
  refine ⟨γ, hγ, Y, hgen, fun w => (hY w).1, fun w => (hY w).2.1, ?_⟩
  have hw : ∀ w, ((γ (Multiplicative.ofAdd 1)).1 : Matrix β β (AE F E)).map (piInf (τ w)) =
      (k.1 : Matrix β β (AE F E)).map (piInf (τ w)) := by
    intro w
    obtain ⟨A', hCA, -⟩ := GlobalTheory.RealLift.KLineProof.frame_inv (hfr w)
    have h1 := hgen 1 w
    rw [one_smul, (hY w).2.2] at h1
    calc _ = ((γ (Multiplicative.ofAdd 1)).1 : Matrix β β (AE F E)).map (piInf (τ w)) * C w * A' := by
          rw [Matrix.mul_assoc, hCA, Matrix.mul_one]
      _ = _ := by rw [h1, Matrix.mul_assoc, hCA, Matrix.mul_one]
  have hA1 := hγ.2 (Multiplicative.ofAdd 1)
  have hmat : ((γ (Multiplicative.ofAdd 1)).1 : Matrix β β (AE F E)) = k.1 := by
    ext i j
    rw [← sub_eq_zero]
    refine GlobalTheory.RealLift.KLineProof.eq_zero_of_piInf hCM τ _ ?_ ?_
    · intro u hu0
      have e1 := congrFun (congrFun (hA1 u hu0) i) j
      have e2 := congrFun (congrFun (hk u hu0) i) j
      simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.zero_apply, smul_sub] at e1 e2 ⊢
      rw [← sub_sub_sub_cancel_right _ _ (u • (1 : Matrix β β (AE F E)) i j), e1, e2, sub_zero]
    · intro w
      have := congrFun (congrFun (hw w) i) j
      simp only [Matrix.map_apply] at this
      rw [map_sub, this, sub_self]
  exact Subtype.ext (Units.ext hmat)


end GlobalTheory.KStableSums
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsKernelSum
open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PolKerCpt

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM GlobalTheory.AdelicU Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem pure_sub {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (f g : SInf F κ)
    (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f - g) φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ - GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ := by
  funext x
  simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, sub_mul]

end GlobalTheory.PolKerCpt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsKernelIntegral
open NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.PolKerLieV

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem exists_decomp {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n d : ℕ} {Y : Spc F E n} {Wd : Spc F E d} (M : Model σ Y Wd)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) ℂ) (emb : (w : InfinitePlace F) → GlobalTheory.AdelicU.EmbOver E w)
    {Φ : (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ} (hΦ : Φ ∈ GlobalTheory.SquareAgree.algD M ψ emb) :
    ∃ (T : Finset (Pl F)) (m : ℕ) (f : Fin m → SInf F (Fin n × Fin d))
      (φ : Fin m → (v : Pl F) → (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ),
      (∀ i, f i ∈ M.Pol ψ emb ∧ (∀ v, φ i v ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) ∧
        ∀ v ∉ T, φ i v = M.vac v) ∧
      Φ = ∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i) := by
  classical
  unfold GlobalTheory.SquareAgree.algD at hΦ
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, φ, hf, hφ, hv, rfl⟩ := hx
    have hfin := Filter.eventually_cofinite.1 hv
    refine ⟨hfin.toFinset, 1, fun _ => f, fun _ => φ, fun _ => ⟨hf, hφ, fun v hvT => ?_⟩, by simp⟩
    by_contra h
    exact hvT (hfin.mem_toFinset.2 h)
  | zero =>
    exact ⟨∅, 0, Fin.elim0, Fin.elim0, fun i => i.elim0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨T₁, m₁, f₁, φ₁, h₁, rfl⟩ := hx
    obtain ⟨T₂, m₂, f₂, φ₂, h₂, rfl⟩ := hy
    refine ⟨T₁ ∪ T₂, m₁ + m₂, Fin.append f₁ f₂, Fin.append φ₁ φ₂, fun i => ?_, ?_⟩
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simp only [Fin.append_left]
        exact ⟨(h₁ i).1, (h₁ i).2.1, fun v hv => (h₁ i).2.2 v (fun h => hv (Finset.mem_union_left _ h))⟩
      · simp only [Fin.append_right]
        exact ⟨(h₂ i).1, (h₂ i).2.1, fun v hv => (h₂ i).2.2 v (fun h => hv (Finset.mem_union_right _ h))⟩
    · rw [Fin.sum_univ_add]
      simp [Fin.append_left, Fin.append_right]
  | smul c x _ hx =>
    obtain ⟨T, m, f, φ, h, rfl⟩ := hx
    refine ⟨T, m, fun i => c • f i, φ, fun i => ⟨(M.Pol ψ emb).smul_mem c (h i).1, (h i).2⟩, ?_⟩
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    funext x
    simp only [Pi.smul_apply, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, SchwartzMap.smul_apply, smul_eq_mul, mul_assoc]

end GlobalTheory.PolKerLieV
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePlaceUnitaryPointKeepsZeroMatchedData
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePlaceUnitaryPointKeepsZeroMatchedData
open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PolKerFin

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM GlobalTheory.AdelicU Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem polZero_om_fin : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf → ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), ∀ h ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ G.W (GlobalTheory.AdelicU.evFin F v),
    ∀ Φ, GlobalTheory.PolKer.PolZero Bs G Xc R Rf (Φ) → GlobalTheory.PolKer.PolZero Bs G Xc R Rf (om (1, h) Φ) := by
  intro F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hM v h hh Φ hΦ
  classical
  obtain ⟨T, hXT, m, f, φ, hf, rfl, hz⟩ := hΦ
  have hP := GlobalTheory.ThK.RealUniq.isPair_V hM.triple
  have h1 : (1 : UA σ G.V.J) ∈ UAt σ G.V (evFin F v) := by
    intro u _
    show u • ((1 : UA σ G.V.J).1.1 - 1) = 0
    simp
  have hex : ∀ φ₀ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∃ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (1, h)) φ₀ φ₁ :=
    fun φ₀ hφ₀ => GlobalTheory.ThK.LocalOps.acts_exists hP v (1, h) h1 hh φ₀ hφ₀
  choose D hDSB hDA using hex
  have hex' : ∀ φ₀ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∃ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (1, h)) φ₀ φ₁ := fun φ₀ hφ₀ => ⟨D φ₀ hφ₀, hDSB φ₀ hφ₀, hDA φ₀ hφ₀⟩
  let Dl : SB (Fin a × Fin (a + a') → Fv F v) →ₗ[ℂ] SB (Fin a × Fin (a + a') → Fv F v) :=
    { toFun := fun x => ⟨D x.1 x.2, hDSB x.1 x.2⟩
      map_add' := fun x y => by
        apply Subtype.ext
        have hl := GlobalTheory.ThK.LocalOps.acts_lin v (om (1, h)) hex' x.2 y.2 (hDA x.1 x.2) (hDA y.1 y.2) 1 1
        simp only [one_smul] at hl
        exact GlobalTheory.ThK.LocalOps.acts_unique v _ (x + y).2 (hDA _ (x + y).2) hl
      map_smul' := fun c x => by
        apply Subtype.ext
        have hl := GlobalTheory.ThK.LocalOps.acts_lin v (om (1, h)) hex' x.2 x.2 (hDA x.1 x.2) (hDA x.1 x.2) c 0
        simp only [zero_smul, add_zero] at hl
        exact GlobalTheory.ThK.LocalOps.acts_unique v _ (c • x).2 (hDA _ (c • x).2) hl }
  let π : SB (Fin a × Fin (a + a') → Fv F v) →ₗ[ℂ] Rf.Pi v := (Rf.p v).comp (SB _).subtype
  have hsurj : Function.Surjective π := by
    intro y
    have hy : y ∈ (SB _).map (Rf.p v) := (hM.fin.onto v).symm ▸ Submodule.mem_top
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hy
    exact ⟨⟨x, hx⟩, rfl⟩
  have hA0 : Acts (evFin F v) (om' (1, h)) (0 : (Fin a' × Fin (a + a') → Fv F v) → ℂ) 0 := by
    intro r _
    have e : tens (evFin F v) (0 : (Fin a' × Fin (a + a') → Fv F v) → ℂ) r = 0 := by
      funext y; simp [tens]
    rw [e, map_zero]
  have hD : ∀ x, π x = 0 → π (Dl x) = 0 := by
    intro x hx
    have e := hM.fin.equiv v h hh x.1 x.2 0 (zero_mem _) (D x.1 x.2) (hDSB x.1 x.2) 0 (zero_mem _) (hDA x.1 x.2) hA0
      (by rw [map_zero]; exact hx)
    rw [map_zero] at e
    exact e
  let L : Rf.Pi v →ₗ[ℂ] Rf.Pi v := GlobalTheory.ThK.RealUniq.induced π hsurj Dl hD
  let ψ : Fin m → (Fin a × Fin (a + a') → Fv F v) → ℂ := fun i => D (φ i v) ((hf i).2.1 v)
  have hL : ∀ i, L (Rf.p v (φ i v)) = Rf.p v (ψ i) := fun i =>
    GlobalTheory.ThK.RealUniq.induced_apply π hsurj Dl hD ⟨φ i v, (hf i).2.1 v⟩
  let φ₂ : Fin m → ∀ w : Pl F, (Fin a × Fin (a + a') → Fv F w) → ℂ := fun i => Function.update (φ i) v (ψ i)
  have hstd : ∀ i, ∀ᶠ w in Filter.cofinite, φ i w = Set.indicator {x | ∀ j, x j ∈ w.adicCompletionIntegers F} 1 := by
    intro i
    filter_upwards [hM.triple.geo.hM.std, T.finite_toSet.compl_mem_cofinite] with w hw hwT
    rw [(hf i).2.2 w hwT, hw]
  have hpure : ∀ i, om (1, h) (pure (f i) (φ i)) = pure (f i) (φ₂ i) := by
    intro i
    obtain ⟨r, hr, hrt⟩ := GlobalTheory.PureFactor.exists_rest_factor v (f i) (φ i) (hstd i)
    have e1 : pure (f i) (φ i) = tens (evFin F v) (φ i v) r := by
      rw [hrt, Function.update_eq_self]
    have hRest : Rest (evFin F v) (φ i v) r :=
      ⟨hr, by rw [← e1]; exact GlobalTheory.TensUniq.pure_mem_schA _ _ (hf i).2.1 (hstd i)⟩
    rw [e1, hDA _ _ r hRest, hrt]
  have hv : v ∈ insert v T := Finset.mem_insert_self _ _
  have hTS : T ⊆ insert v T := Finset.subset_insert _ _
  refine ⟨insert v T, hXT.trans hTS, m, f, φ₂, fun i => ⟨(hf i).1, fun w => ?_, fun w hw => ?_⟩, ?_, ?_⟩
  · by_cases hwv : w = v
    · subst hwv
      simp only [φ₂, Function.update_self]
      exact hDSB _ _
    · simp only [φ₂, Function.update_of_ne hwv]
      exact (hf i).2.1 w
  · rw [Finset.mem_insert, not_or] at hw
    simp only [φ₂, Function.update_of_ne hw.1]
    exact (hf i).2.2 w hw.2
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => hpure i
  · have hz' := GlobalTheory.PolMatchLin.transport Bs G Xc om om' R Rf hM.fin hXT hTS f φ
      (fun j : Fin 0 => j.elim0 : Fin 0 → SInf F (Fin a' × Fin (a + a')))
      (fun j : Fin 0 => j.elim0 : Fin 0 → ∀ w : Pl F, (Fin a' × Fin (a + a') → Fv F w) → ℂ)
      (fun i => (hf i).2.2) (fun j => j.elim0) (by rw [hz]; simp)
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at hz'
    let Lw : ∀ u : (insert v T : Finset (Pl F)), Rf.Pi u →ₗ[ℂ] Rf.Pi u :=
      Function.update (fun _ => LinearMap.id) ⟨v, hv⟩ L
    have key := congrArg (LinearMap.lTensor R.Pi (PiTensorProduct.map Lw)) hz'
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_zero, map_sum] at key
    rw [← key]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.lTensor_tmul, PiTensorProduct.map_tprod]
    congr 2
    funext u
    by_cases hu : u = ⟨v, hv⟩
    · subst hu
      simp only [Lw, φ₂, Function.update_self]
      exact (hL i).symm
    · have hu' : u.1 ≠ v := fun e => hu (Subtype.ext e)
      simp only [Lw, φ₂, Function.update_of_ne hu, Function.update_of_ne hu', LinearMap.id_apply]

end GlobalTheory.PolKerFin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePlaceUnitaryPointKeepsZeroMatchedDataStatement
open NumberField IsDedekindDomain
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finitePlace_unitaryPoint_keeps_zeroMatchedData : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf → ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), ∀ h ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ G.W (GlobalTheory.AdelicU.evFin F v),
    ∀ Φ, GlobalTheory.PolKer.PolZero Bs G Xc R Rf (Φ) → GlobalTheory.PolKer.PolZero Bs G Xc R Rf (om (1, h) Φ) := by
  first | exact @GlobalTheory.PolKerFin.polZero_om_fin | exact GlobalTheory.PolKerFin.polZero_om_fin | (intros; apply GlobalTheory.PolKerFin.polZero_om_fin <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsLocalIdentity
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.ThK.PolMatchStep

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM GlobalTheory.AdelicU

section Local

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem acts_lin_eq (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (T : Module.End ℂ ((κ → AF F) → ℂ)) {φ ψ φ₁ ψ₁ χ : (κ → Fv F v) → ℂ}
    (hφ : φ ∈ SB (κ → Fv F v)) (hψ : ψ ∈ SB (κ → Fv F v)) (h₁ : Acts (evFin F v) T φ φ₁)
    (h₂ : Acts (evFin F v) T ψ ψ₁) (a b : ℂ) (h₃ : Acts (evFin F v) T (a • φ + b • ψ) χ) :
    χ = a • φ₁ + b • ψ₁ := by
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest κ v
  have hs : a • φ + b • ψ ∈ SB (κ → Fv F v) := add_mem ((SB _).smul_mem a hφ) ((SB _).smul_mem b hψ)
  have hlin : ∀ x y : (κ → Fv F v) → ℂ,
      tens (evFin F v) (a • x + b • y) R = a • tens (evFin F v) x R + b • tens (evFin F v) y R := by
    intro x y; funext z; simp only [tens, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  refine GlobalTheory.InertAvgDual.eq_of_tens_eq v hR0 (hR _ hs).1 ?_
  rw [← h₃ R (hR _ hs), hlin, map_add (f := _), map_smul, map_smul, h₁ R (hR _ hφ), h₂ R (hR _ hψ), hlin]

open Classical in
theorem pure_update (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ) (f : SInf F κ)
    (φ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F w) → ℂ) (hSB : ∀ w, φ w ∈ SB (κ → Fv F w))
    (hstd : ∀ᶠ w in Filter.cofinite, φ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1)
    {φ₁ : (κ → Fv F v) → ℂ} (hA : Acts (evFin F v) T (φ v) φ₁) :
    T (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (Function.update φ v φ₁) := by
  obtain ⟨r, hr, hrt⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φ hstd
  have e1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ = tens (evFin F v) (φ v) r := by rw [hrt, Function.update_eq_self]
  have hRest : Rest (evFin F v) (φ v) r := ⟨hr, by rw [← e1]; exact GlobalTheory.TensUniq.pure_mem_schA f φ hSB hstd⟩
  rw [e1, hA r hRest, hrt]

end Local

end GlobalTheory.ThK.PolMatchStep

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ShiftedTensorLatticePartMemLiftGroupPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ShiftedTensorLatticePartMemLiftGroupPoints
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.LiftLevel

variable {D : D7}

section SlopeTestRemainingChoices

open GlobalTheory.LatVac GlobalTheory.SplitScalar

def stO (x : 𝓞 D.host.E) : 𝓞 D.host.E :=
  ⟨star (x : D.host.E), (show IsIntegral ℤ (x : D.host.E) from x.2).map (starRingEnd D.host.E).toIntAlgHom⟩

theorem coe_stO (x : 𝓞 D.host.E) : ((stO x : 𝓞 D.host.E) : D.host.E) = star (x : D.host.E) := rfl

theorem mem_of_mem_conjI {P : Ideal (𝓞 D.host.E)} {x : 𝓞 D.host.E} (hx : x ∈ conjI P) : stO x ∈ P := by
  induction hx using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨b, hb, hab⟩ := ha
    have : stO a = b := by
      apply RingOfIntegers.ext
      rw [coe_stO, show (a : D.host.E) = star (b : D.host.E) from hab, star_star]
    rw [this]; exact hb
  | zero =>
    have : stO (0 : 𝓞 D.host.E) = 0 := RingOfIntegers.ext (by rw [coe_stO]; simp)
    rw [this]; exact zero_mem _
  | add a b _ _ ha hb =>
    have : stO (a + b) = stO a + stO b := RingOfIntegers.ext (by
      show star ((a : D.host.E) + b) = star (a : D.host.E) + star (b : D.host.E)
      exact star_add _ _)
    rw [this]; exact add_mem ha hb
  | smul r a _ ha =>
    have : stO (r • a) = stO r * stO a := RingOfIntegers.ext (by
      show star ((r : D.host.E) * a) = star (r : D.host.E) * star (a : D.host.E)
      exact star_mul' _ _)
    rw [this]; exact Ideal.mul_mem_left _ _ ha

theorem smul_mem_tens {n r : ℕ} {Λ : Lt D.host.E n} {L L' : Lt D.host.E r} (c : 𝓞 D.host.E)
    (h : ∀ u ∈ L, c • u ∈ L') {y : Matrix (Fin n) (Fin r) D.host.E} (hy : y ∈ tens Λ L) :
    (c : D.host.E) • y ∈ tens Λ L' := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨v, hv, u, hu, rfl⟩ := hy
    refine AddSubgroup.subset_closure ⟨v, hv, c • u, h u hu, ?_⟩
    rw [Matrix.vecMulVec_smul]
    rfl
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem smul_mem_hatA_of_int {S T : HSp D} {A : AddSubgroup (Matrix (Fin S.rank) (Fin T.rank) D.host.E)}
    (hA : ∀ o : 𝓞 D.host.E, ∀ y ∈ A, (o : D.host.E) • y ∈ A) {z : AE D} (hz : finPart D z ∈ intAE D)
    {u : WO S T} (hu : u ∈ hatA S T A) : z • u ∈ hatA S T A := by
  refine GlobalTheory.Ker.SignVac.hatA_induction (p := fun u => z • u ∈ hatA S T A) ?_ ?_ ?_ ?_ hu
  · intro α hα y hy
    have key : ∀ x ∈ intAE D,
        (Matrix.of fun i j => GlobalTheory.TensLatMove.emb D (x * (α ⊗ₜ[D.host.F] (yᵀ i j)))) ∈ hatA S T A := by
      intro x hx
      induction hx using AddSubgroup.closure_induction with
      | mem x hx =>
        obtain ⟨a, ha, o, rfl⟩ := hx
        have e1 : (Matrix.of fun i j => GlobalTheory.TensLatMove.emb D
            ((a ⊗ₜ[D.host.F] (o : D.host.E)) * (α ⊗ₜ[D.host.F] (yᵀ i j)))) =
            GlobalTheory.LatVac.finTens (a * α) (((o : D.host.E) • y)ᵀ) := by
          ext i j
          rw [Matrix.of_apply, Algebra.TensorProduct.tmul_mul_tmul, GlobalTheory.TensLatMove.emb_tmul]
          rfl
        rw [e1]
        exact GlobalTheory.Ker.SignVac.finTens_mem (mul_mem_intAf ha hα) (hA o y hy)
      | zero =>
        convert zero_mem (hatA S T A) using 1
        ext i j
        rw [Matrix.of_apply, zero_mul, LinearMap.map_zero, Matrix.zero_apply]
      | add x x' _ _ hx hx' =>
        convert add_mem hx hx' using 1
        ext i j
        rw [Matrix.add_apply, Matrix.of_apply, Matrix.of_apply, Matrix.of_apply, add_mul, LinearMap.map_add (f := _)]
      | neg x _ hx =>
        convert neg_mem hx using 1
        ext i j
        rw [Matrix.neg_apply, Matrix.of_apply, Matrix.of_apply, neg_mul, LinearMap.map_neg]
    convert key _ hz using 1
    ext i j
    rw [Matrix.of_apply, GlobalTheory.TensLatMove.emb_mul, GlobalTheory.TensLatMove.emb_tmul]
    rfl
  · rw [smul_zero]; exact zero_mem _
  · intro x y hx hy; rw [smul_add]; exact add_mem hx hy
  · intro x hx; rw [smul_neg]; exact neg_mem hx

end SlopeTestRemainingChoices

theorem partAt_eq_smul {S T : HSp D} (c : AE D) (x : WO S T) : partAt c x = c • x := by
  ext i j; rfl

theorem partAt_mem_liftL : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∀ (a : AE D) (k₀ : GA D S) (Λ' : Lt D.host.E S.rank), (∃ b : AE D, a * b = e) → GlobalTheory.LiftLevel.IsMover S T βS βT e a k₀ → GlobalTheory.LiftLevel.IsGen C βS βT Pg Q e a → IsMov (fmtC S k₀⁻¹) Λ' (stdL D.host.E S.rank) → ∀ Lv : GlobalTheory.SW.Level C.X, Lv.𝔪 = GlobalTheory.LiftLevel.liftI Pg Q → ∀ u ∈ hatA S T (tens Λ' (Lv.sh C.X.Λ)), GlobalTheory.LiftLevel.partAt (cA D e) u ∈ GlobalTheory.LiftLevel.liftL S T βS βT Pg Q e := by
  intro D S T C hn ΛT _ _ βS βT _ _ Pg Q ξ hPg _ e he a k₀ Λ' _ hMv hGen hMov Lv hLv u hu

  have hw : actO S T k₀⁻¹ 1 u ∈ hatA S T (tens (stdL D.host.E S.rank) (Lv.sh C.X.Λ)) :=
    (GlobalTheory.TensLatMove.mem_hatA_iff S T C.m.gS k₀⁻¹ 1 Λ' (stdL D.host.E S.rank) (Lv.sh C.X.Λ) (Lv.sh C.X.Λ) hMov
      (GlobalTheory.OneMapRef.Term.isMov_fmt_one _) _).2 ⟨u, hu, rfl⟩
  have hu' : actO S T k₀ 1 (actO S T k₀⁻¹ 1 u) = u := by
    have := GlobalTheory.AdelicLatMove.actO_actO_inv S T k₀ 1 u
    rwa [inv_one] at this
  generalize actO S T k₀⁻¹ 1 u = w at hw hu'

  have hm : Lv.𝔪 ⊔ conjI Lv.𝔪 = ⊤ := Ideal.isCoprime_iff_sup_eq.1 Lv.cop
  have h1 : (1 : 𝓞 D.host.E) ∈ Lv.𝔪 ⊔ conjI Lv.𝔪 := by rw [hm]; exact Submodule.mem_top
  obtain ⟨t, ht, c, hc, htc⟩ := Submodule.mem_sup.1 h1
  have hcP : ∀ PP ∈ Pg ∪ Q, conjI Lv.𝔪 ≤ PP.asIdeal := by
    intro PP hPP x hx
    have h2 := mem_of_mem_conjI hx
    rw [hLv, liftI] at h2
    have h3 : stO x ∈ conjI PP.asIdeal := Finset.inf_le (f := fun PP : Formalism.L2.DIV.Pl D.host.E => conjI PP.asIdeal)
      hPP (Ideal.prod_le_inf h2)
    have h4 := mem_of_mem_conjI h3
    have h5 : stO (stO x) = x := RingOfIntegers.ext (star_star _)
    rwa [h5] at h4
  have htP : ∀ PP ∈ Pg ∪ Q, t ∉ PP.asIdeal := by
    intro PP hPP htm
    have h6 : (1 : 𝓞 D.host.E) ∈ PP.asIdeal := htc ▸ add_mem htm (hcP PP hPP hc)
    exact PP.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h6)
  have hs : stO t ∈ conjI Lv.𝔪 := Ideal.subset_span ⟨t, ht, rfl⟩
  have ht0 : (t : D.host.E) ≠ 0 := by
    obtain ⟨PP, hPP⟩ := hPg
    intro h
    apply htP PP (Finset.mem_union_left _ hPP)
    have : t = 0 := RingOfIntegers.ext (h.trans rfl)
    rw [this]; exact zero_mem _
  have hs0 : ((stO t : 𝓞 D.host.E) : D.host.E) ≠ 0 := by rw [coe_stO]; exact star_ne_zero.2 ht0

  have hsL : ∀ v ∈ Lv.sh C.X.Λ, stO t • v ∈ Lv.𝔪 • C.X.Λ := fun v hv => hv _ hs
  have h0 : (pairA D.host.F 0 1 ⊗ₜ[D.host.F] ((stO t : 𝓞 D.host.E) : D.host.E) : AE D) • w ∈
      hatA S T (tens (stdL D.host.E S.rank) (Lv.𝔪 • C.X.Λ)) := by
    refine GlobalTheory.Ker.SignVac.hatA_induction (p := fun u => (pairA D.host.F 0 1 ⊗ₜ[D.host.F]
      ((stO t : 𝓞 D.host.E) : D.host.E) : AE D) • u ∈ hatA S T (tens (stdL D.host.E S.rank) (Lv.𝔪 • C.X.Λ)))
      ?_ ?_ ?_ ?_ hw
    · intro α hα y hy
      rw [GlobalTheory.LatVac.tmul_smul_finTens, one_mul, ← Matrix.transpose_smul]
      exact GlobalTheory.Ker.SignVac.finTens_mem hα (smul_mem_tens _ hsL hy)
    · rw [smul_zero]; exact zero_mem _
    · intro x y hx hy; rw [smul_add]; exact add_mem hx hy
    · intro x hx; rw [smul_neg]; exact neg_mem hx

  have hz1 : finPart D (cA D e * incA D (((stO t : 𝓞 D.host.E) : D.host.E)⁻¹)) ∈ intAE D := by
    have h7 := (GlobalTheory.FinPl.FrameLat.cA_int_iff (e * incA D ((t : D.host.E))⁻¹)).2
      (GlobalTheory.IdemSumInt.finPart_idemSum_mul_inv_mem D e (Pg ∪ Q) he t htP)
    rwa [map_mul, GlobalTheory.FinPl.FrameLat.cA_incA, star_inv₀] at h7
  have hA' : ∀ o : 𝓞 D.host.E, ∀ y ∈ tens (stdL D.host.E S.rank) (Lv.𝔪 • C.X.Λ),
      (o : D.host.E) • y ∈ tens (stdL D.host.E S.rank) (Lv.𝔪 • C.X.Λ) :=
    fun o y hy => smul_mem_tens o (fun u hu => Submodule.smul_mem _ o hu) hy
  have hx0 : partAt (cA D e) w ∈ hatA S T (tens (stdL D.host.E S.rank) (liftI Pg Q • C.X.Λ)) := by
    have e1 : partAt (cA D e) w = (cA D e * incA D (((stO t : 𝓞 D.host.E) : D.host.E)⁻¹)) •
        (pairA D.host.F 0 1 ⊗ₜ[D.host.F] ((stO t : 𝓞 D.host.E) : D.host.E) : AE D) • w := by
      rw [smul_smul, mul_assoc]
      have e2 : incA D (((stO t : 𝓞 D.host.E) : D.host.E)⁻¹) *
          (pairA D.host.F 0 1 ⊗ₜ[D.host.F] ((stO t : 𝓞 D.host.E) : D.host.E) : AE D) =
          pairA D.host.F 0 1 ⊗ₜ[D.host.F] (1 : D.host.E) := by
        change ((1 : AF D.host.F) ⊗ₜ[D.host.F] ((stO t : 𝓞 D.host.E) : D.host.E)⁻¹) * _ = _
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, inv_mul_cancel₀ hs0]
      rw [e2, mul_smul, GlobalTheory.Ker.SignVac.one_smul_hatA hw, partAt_eq_smul]
    rw [e1, ← hLv]
    exact smul_mem_hatA_of_int hA' hz1 h0

  have hidem : cA D e * cA D e = cA D e := by rw [← map_mul, GlobalTheory.PlaceVec.idemSum_mul_self he]
  have hhalf : IsHalf (cA D e) (partAt (cA D e) w) := fun i j => by
    change cA D e * (cA D e * w i j) = cA D e * w i j
    rw [← mul_assoc, hidem]
  obtain ⟨hI, hR⟩ := ((hGen _ hhalf).2).2 hx0
  have hmv := hMv.2.2 _ hhalf
  have hcomm : partAt (cA D e) u = actO S T k₀ 1 (partAt (cA D e) w) := by
    rw [partAt_eq_smul, partAt_eq_smul, ← hu']
    simp only [actO, Matrix.mul_smul, Matrix.smul_mul]
  rw [hcomm]
  refine ⟨GlobalTheory.WeilVacMove.isHalf_actO _ _ _ hhalf, ?_, fun PP hPP => ?_⟩
  · rw [hmv]; exact hI
  · rw [hmv]; exact hR PP hPP

end GlobalTheory.LiftLevel

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ShiftedTensorLatticePartMemLiftGroupPointsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shiftedTensorLatticePart_mem_liftLattice : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∀ (a : AE D) (k₀ : GA D S) (Λ' : Lt D.host.E S.rank), (∃ b : AE D, a * b = e) → GlobalTheory.LiftLevel.IsMover S T βS βT e a k₀ → GlobalTheory.LiftLevel.IsGen C βS βT Pg Q e a → IsMov (fmtC S k₀⁻¹) Λ' (stdL D.host.E S.rank) → ∀ Lv : GlobalTheory.SW.Level C.X, Lv.𝔪 = GlobalTheory.LiftLevel.liftI Pg Q → ∀ u ∈ hatA S T (tens Λ' (Lv.sh C.X.Λ)), GlobalTheory.LiftLevel.partAt (cA D e) u ∈ GlobalTheory.LiftLevel.liftL S T βS βT Pg Q e := by
  first | exact @GlobalTheory.LiftLevel.partAt_mem_liftL | exact GlobalTheory.LiftLevel.partAt_mem_liftL | (intros; apply GlobalTheory.LiftLevel.partAt_mem_liftL <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentSumOverFinitePlacesUnique
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentSumOverFinitePlacesUnique
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IdemSumUniq

theorem idemSum_unique : ∀ {D : D7} (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e e' : AE D), IsIdemSum e P → IsIdemSum e' P → e = e' := by
  intro D P e e' h h'
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := h
  obtain ⟨⟨es', hes', rfl⟩, -⟩ := h'
  exact Finset.sum_congr rfl fun PP hP =>
    (GlobalTheory.PlaceIdemUniq.idemAt_unique_orth D _ _ PP PP (hes PP hP) (hes' PP hP)).1 rfl

end GlobalTheory.IdemSumUniq
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentSumOverFinitePlacesUniqueStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotentSum_over_finite_places_unique : ∀ {D : D7} (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e e' : AE D), IsIdemSum e P → IsIdemSum e' P → e = e' := by
  first | exact @GlobalTheory.IdemSumUniq.idemSum_unique | exact GlobalTheory.IdemSumUniq.idemSum_unique | (intros; apply GlobalTheory.IdemSumUniq.idemSum_unique <;> assumption)
end
end
