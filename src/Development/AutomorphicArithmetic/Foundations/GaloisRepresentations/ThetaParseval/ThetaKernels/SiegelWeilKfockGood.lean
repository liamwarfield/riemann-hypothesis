module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.LiftExOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfockMem
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.RdEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilActDefs
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnitaryChartEquiv.CEquivApply
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.ContinuousCj
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.VacuumIwasawa.IsParOfFrame
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaBijections.JjMulJj

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfockGood
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFock
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem goodAwayEx_k : _root_.PositivityTheory.SiegelWeilFormula.GoodAwayEx_k := by
  intro F E _ _ _ _ _ σ d R w
  let g := (GlobalTheory.RealLift.intPts F (Fin d.m × Fin d.n × Fin 2)).indicator (1 : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ)
  have hg : g ∈ SB (Fin d.m × Fin d.n × Fin 2 → Af F) := GlobalTheory.RealLift.indicator_intPts_mem_SB
  let Ψ : Mx F E d.m d.n → ℂ := fun X =>
    (∏ w' ∈ Finset.univ.erase w, fP (1 : PX d.m d.n) (R.loc w' X)) * g fun k => (d.crd X k).2
  have hΨ : Ψ ∈ R.away w := Submodule.subset_span ⟨fun _ => 1, g, hg, rfl⟩
  refine ⟨Ψ, _root_.PositivityTheory.SiegelWeilFormula.KFock.away_inv_k R w Ψ hΨ, fun h0 => ?_, fun f hf => _root_.PositivityTheory.SiegelWeilFormula.KFock.tens_mem_k d R w f hf Ψ hΨ⟩
  have h1 := congrFun h0 0
  have hc : (fun k => (d.crd (0 : Mx F E d.m d.n) k).2) = 0 := by
    funext k
    unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.crd
    rw [Matrix.zero_apply, map_zero, Finsupp.zero_apply]
    rfl
  have hg0 : g (fun k => (d.crd (0 : Mx F E d.m d.n) k).2) = 1 := by
    rw [hc]
    exact Set.indicator_of_mem GlobalTheory.RealLift.zero_mem_intPts _
  have hp : (∏ w' ∈ Finset.univ.erase w, fP (1 : PX d.m d.n) (R.loc w' 0)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun w' _ => fP_one_ne _
  exact hp (by simpa [Ψ, hg0] using h1)
end PositivityTheory.SiegelWeilFormula.KFock
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKrdRD
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKrdRDFr
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Krd
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem epsEx_k : _root_.PositivityTheory.SiegelWeilFormula.Krd.EpsEx_k := by
  intro F E _ _ _ _ _ σ d
  obtain ⟨ε, hε⟩ := d.ok.frame.1
  refine ⟨ε, hε, ?_⟩
  have hss : ∀ x, σ (σ x) = x := PositivityTheory.ThKG.Tow.Levi.sig_sig d.cm
  have i : Fin d.n := ⟨0, d.ok.hn⟩
  have key : ∀ c : E, (∀ i j, σ (d.Y.J j i) = c * d.Y.J i j) → ((ε : ℤ) : E) = c := fun c hc => by
    have e := congrFun (congrFun (conjT_frame c d.Y.J hc hss d.b.1) (Sum.inl i)) (Sum.inr i)
    rw [hε] at e
    simpa [Matrix.fromBlocks] using e
  rcases d.ok.sign with ⟨hA, hY⟩ | ⟨hA, hY⟩
  · refine Or.inl ⟨hA, ?_⟩
    have e := key (-1) fun i j => by rw [hY, neg_one_mul]
    have e' : ((ε : ℤ) : E) = ((-1 : ℤ) : E) := by rw [e]; push_cast; rfl
    exact Units.ext (by simpa using Int.cast_injective (α := E) e')
  · refine Or.inr ⟨hA, ?_⟩
    have e := key 1 fun i j => by rw [hY, one_mul]
    have e' : ((ε : ℤ) : E) = ((1 : ℤ) : E) := by rw [e]; push_cast; rfl
    exact Units.ext (by simpa using Int.cast_injective (α := E) e')
theorem frEx_k : _root_.PositivityTheory.SiegelWeilFormula.Krd.FrEx_k := by
  intro F E _ _ _ _ _ σ d
  refine ⟨fun hA => ?_, fun hA => ?_⟩
  · choose fr sg hfr using fun w => frame_of_sig (hA.sig w) d.ok.aniso
    exact ⟨fr, sg, fun w => by rw [one_smul, hfr w]⟩
  · choose fr sg hfr using fun w => frame_of_sig (hA.sig w) d.ok.aniso
    refine ⟨fr, sg, fun w => ?_⟩
    rw [← hfr w, Matrix.mul_smul, Matrix.smul_mul]
end PositivityTheory.SiegelWeilFormula.Krd
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
namespace PositivityTheory.SiegelWeilFormula.Krd
theorem rdEx_k : _root_.PositivityTheory.SiegelWeilFormula.RDEx_k := _root_.PositivityTheory.SiegelWeilFormula.Krd.rdEx_of_k _root_.PositivityTheory.SiegelWeilFormula.Krd.epsEx_k _root_.PositivityTheory.SiegelWeilFormula.Krd.frEx_k _root_.PositivityTheory.SiegelWeilFormula.Krd.iotaEx_k
end PositivityTheory.SiegelWeilFormula.Krd
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKTunitMeas
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
namespace PositivityTheory.SiegelWeilFormula.KTunit
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid
open PositivityTheory.SiegelWeilFormula.TBij.Adp
local instance (priority := high)  {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] :
    MeasurableSpace (κ → AF F) := borel _
local instance  {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] : BorelSpace (κ → AF F) := ⟨rfl⟩
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
def cmap_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {κ : Type} (τ : κ ≃ _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) (X : Mx F E d.m d.n) : κ → AF F := fun k => d.crd X (τ k)
def cinv_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {κ : Type} (τ : κ ≃ _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) (c : κ → AF F) : Mx F E d.m d.n := d.cmb fun k => c (τ.symm k)
theorem cinv_cmap_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {κ : Type} (τ : κ ≃ _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) (X : Mx F E d.m d.n) : _root_.PositivityTheory.SiegelWeilFormula.KTunit.cinv_k d τ (_root_.PositivityTheory.SiegelWeilFormula.KTunit.cmap_k d τ X) = X := by
  have : (fun k => _root_.PositivityTheory.SiegelWeilFormula.KTunit.cmap_k d τ X (τ.symm k)) = d.crd X := funext fun k => by simp [_root_.PositivityTheory.SiegelWeilFormula.KTunit.cmap_k]
  rw [_root_.PositivityTheory.SiegelWeilFormula.KTunit.cinv_k, this, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.cmb_crd]
theorem cmap_cinv_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {κ : Type} (τ : κ ≃ _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) (c : κ → AF F) : _root_.PositivityTheory.SiegelWeilFormula.KTunit.cmap_k d τ (_root_.PositivityTheory.SiegelWeilFormula.KTunit.cinv_k d τ c) = c := by
  funext k
  simp [_root_.PositivityTheory.SiegelWeilFormula.KTunit.cmap_k, _root_.PositivityTheory.SiegelWeilFormula.KTunit.cinv_k, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.crd_cmb]
theorem cmap_add_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {κ : Type} (τ : κ ≃ _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) (X Y : Mx F E d.m d.n) :
    _root_.PositivityTheory.SiegelWeilFormula.KTunit.cmap_k d τ (X + Y) = _root_.PositivityTheory.SiegelWeilFormula.KTunit.cmap_k d τ X + _root_.PositivityTheory.SiegelWeilFormula.KTunit.cmap_k d τ Y := by
  funext k
  simp [_root_.PositivityTheory.SiegelWeilFormula.KTunit.cmap_k, _root_.PositivityTheory.SiegelWeilFormula.SD_k.crd, map_add (f := _)]
theorem cont_cmap_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {κ : Type} (τ : κ ≃ _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) : Continuous (_root_.PositivityTheory.SiegelWeilFormula.KTunit.cmap_k d τ) := by
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  have hr := (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ d.ok.good.cm (AF F)).2.2.2.2.2.2.1 2 d.bs
  refine continuous_pi fun k => ?_
  exact (continuous_apply (τ k).2.2).comp (hr.continuous.comp (continuous_id.matrix_elem (τ k).1 (τ k).2.1))
theorem cont_cinv_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {κ : Type} (τ : κ ≃ _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) : Continuous (_root_.PositivityTheory.SiegelWeilFormula.KTunit.cinv_k d τ) := by
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  have hr := (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ d.ok.good.cm (AF F)).2.2.2.2.2.2.1 2 d.bs
  set h := hr.homeomorph with hh
  have e : ∀ c i j, _root_.PositivityTheory.SiegelWeilFormula.KTunit.cinv_k d τ c i j = h.symm (fun l => c (τ.symm (i, j, l))) := fun c i j => by
    apply h.injective
    rw [Homeomorph.apply_symm_apply]
    funext l
    exact congrFun (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.crd_cmb d (fun k => c (τ.symm k))) (i, j, l)
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [e]
  exact h.symm.continuous.comp (continuous_pi fun l => continuous_apply _)
def cEquiv_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {κ : Type} (τ : κ ≃ _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) : Mx F E d.m d.n ≃ₜ+ (κ → AF F) where
  toFun := _root_.PositivityTheory.SiegelWeilFormula.KTunit.cmap_k d τ
  invFun := _root_.PositivityTheory.SiegelWeilFormula.KTunit.cinv_k d τ
  left_inv := _root_.PositivityTheory.SiegelWeilFormula.KTunit.cinv_cmap_k d τ
  right_inv := _root_.PositivityTheory.SiegelWeilFormula.KTunit.cmap_cinv_k d τ
  map_add' := _root_.PositivityTheory.SiegelWeilFormula.KTunit.cmap_add_k d τ
  continuous_toFun := _root_.PositivityTheory.SiegelWeilFormula.KTunit.cont_cmap_k d τ
  continuous_invFun := _root_.PositivityTheory.SiegelWeilFormula.KTunit.cont_cinv_k d τ
theorem map_haar_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {κ : Type} [Fintype κ] (τ : κ ≃ _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) (ν : Measure (Mx F E d.m d.n))
    (hν : ν.IsAddHaarMeasure) :
    (ν.map (_root_.PositivityTheory.SiegelWeilFormula.KTunit.cmap_k d τ)).IsAddHaarMeasure ∧
      ∀ f : (κ → AF F) → ℂ, ∫ X, f (_root_.PositivityTheory.SiegelWeilFormula.KTunit.cmap_k d τ X) ∂ν = ∫ y, f y ∂(ν.map (_root_.PositivityTheory.SiegelWeilFormula.KTunit.cmap_k d τ)) := by
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  have P := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ d.ok.good.cm (AF F)
  haveI : IsTopologicalRing (AE F E) := P.1
  haveI : BorelSpace (Mx F E d.m d.n) := P.2.2.2.2.2.2.2.1 d.m d.n
  haveI : IsTopologicalAddGroup (Mx F E d.m d.n) := inferInstance
  refine ⟨?_, fun f => ?_⟩
  · exact ContinuousAddEquiv.isAddHaarMeasure_map ν (_root_.PositivityTheory.SiegelWeilFormula.KTunit.cEquiv_k d τ)
  · have h := integral_map_equiv (μ := ν) (_root_.PositivityTheory.SiegelWeilFormula.KTunit.cEquiv_k d τ).toHomeomorph.toMeasurableEquiv f
    exact h.symm
end PositivityTheory.SiegelWeilFormula.KTunit
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ContinuousCjK
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Act.C1
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} {L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d} {uM : (Fin L.n → AE F E) → d.G} {ν : Measure (Fin L.n → AE F E)}
  {𝓤 : Set (Fin L.n → AE F E)} {nb : nA σ d.Y d.b → d.G}
def Ap_k (hU : L.UData uM ν 𝓤) (u : Fin L.n → AE F E) : Matrix (Fin d.n) (Fin d.n) (AE F E) := (hU.1 u).choose
theorem inFrame_uM_k (hU : L.UData uM ν 𝓤) (u : Fin L.n → AE F E) :
    inFrame d.b (uM u) = Matrix.fromBlocks (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L u) 0 0 (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU u) := (hU.1 u).choose_spec
theorem uM_add_k (hU : L.UData uM ν 𝓤) (u v : Fin L.n → AE F E) : uM (u + v) = uM u * uM v := by
  refine _root_.PositivityTheory.SiegelWeilFormula.Act.C1.blk_unique_k d (A₂ := _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU u * _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU v) (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.inFrame_uM_k hU (u + v)) ?_
  rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.inFrame_uM_k hU, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.inFrame_uM_k hU, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_mul_k]
theorem uM_zero_k (hU : L.UData uM ν 𝓤) : uM 0 = 1 := by
  refine _root_.PositivityTheory.SiegelWeilFormula.Act.C1.blk_unique_k d (A₂ := 1) (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.inFrame_uM_k hU 0) ?_
  rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_one, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_zero_k, Matrix.fromBlocks_one]
theorem uM_neg_k (hU : L.UData uM ν 𝓤) (u : Fin L.n → AE F E) : uM (-u) = (uM u)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← _root_.PositivityTheory.SiegelWeilFormula.Act.C1.uM_add_k hU, neg_add_cancel, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.uM_zero_k hU])
theorem Ap_neg_mul_k (hU : L.UData uM ν 𝓤) (u : Fin L.n → AE F E) : _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU (-u) * _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU u = 1 := by
  have h := congrArg (inFrame d.b) (show uM (-u) * uM u = 1 by rw [← _root_.PositivityTheory.SiegelWeilFormula.Act.C1.uM_add_k hU, neg_add_cancel, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.uM_zero_k hU])
  rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.inFrame_uM_k hU, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.inFrame_uM_k hU, Matrix.fromBlocks_multiply,
    GlobalTheory.EisBL.DoubledParabolic.inFrame_one, ← Matrix.fromBlocks_one] at h
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at h
  exact (Matrix.fromBlocks_inj.1 h).2.2.2
theorem frame_conj_k (hU : L.UData uM ν 𝓤) (hN : IsNMap d.b nb) (u : Fin L.n → AE F E) (β : nA σ d.Y d.b) :
    inFrame d.b ((uM u)⁻¹ * nb β * uM u) = Matrix.fromBlocks 1 (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L (-u) * β.1 * _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU u) 0 1 := by
  rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, ← _root_.PositivityTheory.SiegelWeilFormula.Act.C1.uM_neg_k hU, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.inFrame_uM_k hU, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.inFrame_uM_k hU, hN β,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_mul_k, neg_add_cancel, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_zero_k,
    _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_neg_mul_k hU]
theorem cj_mem_k (hU : L.UData uM ν 𝓤) (hN : IsNMap d.b nb) (u : Fin L.n → AE F E) (β : nA σ d.Y d.b) :
    _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L (-u) * β.1 * _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU u ∈ nA σ d.Y d.b :=
  AddSubgroup.subset_closure ⟨_, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.frame_conj_k hU hN u β⟩
def cj_k (hU : L.UData uM ν 𝓤) (hN : IsNMap d.b nb) (u : Fin L.n → AE F E) : nA σ d.Y d.b →+ nA σ d.Y d.b where
  toFun β := ⟨_, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_mem_k hU hN u β⟩
  map_zero' := Subtype.ext (by simp)
  map_add' β β' := Subtype.ext (by simp [Matrix.mul_add, Matrix.add_mul])
theorem cj_val_k (hU : L.UData uM ν 𝓤) (hN : IsNMap d.b nb) (u : Fin L.n → AE F E) (β : nA σ d.Y d.b) :
    (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU hN u β).1 = _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L (-u) * β.1 * _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU u := rfl
theorem nb_cj_k (hU : L.UData uM ν 𝓤) (hN : IsNMap d.b nb) (u : Fin L.n → AE F E) (β : nA σ d.Y d.b) :
    nb (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU hN u β) = (uM u)⁻¹ * nb β * uM u := by
  apply kunf.inFrame_injective d.b
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C1.frame_conj_k hU hN, hN]
  rfl
theorem cj_inv_k (hU : L.UData uM ν 𝓤) (hN : IsNMap d.b nb) (u : Fin L.n → AE F E) (β : nA σ d.Y d.b) :
    _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU hN (-u) (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU hN u β) = β := by
  apply Subtype.ext
  have h1 : _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L u * _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L (-u) = 1 := by rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_mul_k, add_neg_cancel, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_zero_k]
  have h2 : _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU u * _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU (-u) = 1 := by simpa using _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_neg_mul_k hU (-u)
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_val_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_val_k, neg_neg]
  calc _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L u * (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L (-u) * β.1 * _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU u) * _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU (-u)
      = (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L u * _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L (-u)) * β.1 * (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU u * _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU (-u)) := by simp only [Matrix.mul_assoc]
    _ = β.1 := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
theorem continuous_cj_k (hU : L.UData uM ν 𝓤) (hN : IsNMap d.b nb) (u : Fin L.n → AE F E) :
    Continuous (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU hN u) :=
  ((continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const).subtype_mk _
def cjE_k (hU : L.UData uM ν 𝓤) (hN : IsNMap d.b nb) (u : Fin L.n → AE F E) : nA σ d.Y d.b ≃ₜ+ nA σ d.Y d.b where
  toFun := _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU hN u
  invFun := _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU hN (-u)
  left_inv β := _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_inv_k hU hN u β
  right_inv β := by simpa using _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_inv_k hU hN (-u) β
  map_add' := map_add _
  continuous_toFun := _root_.PositivityTheory.SiegelWeilFormula.Act.C1.continuous_cj_k hU hN u
  continuous_invFun := _root_.PositivityTheory.SiegelWeilFormula.Act.C1.continuous_cj_k hU hN (-u)
end PositivityTheory.SiegelWeilFormula.Act.C1
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAvacIwaC
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Avac
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
open GlobalTheory.Doubling (absE)
theorem isPar_of_frame_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (p : d.G) (h21 : (inFrame d.b p).toBlocks₂₁ = 0) :
    ∃ t : GL (Fin d.n) (AE F E), IsPar p t ∧ (Matrix.GeneralLinearGroup.det t : AE F E) = (inFrame d.b p).toBlocks₁₁.det := by
  obtain ⟨-, tb, htb⟩ := d.ok.frame
  set M := inFrame d.b p with hM
  let E1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E) := Matrix.fromRows 1 0
  let DC : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E) := diagCols (Fin d.n)
  have htb' : d.b.1.toCols₁ = (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) E) * tb.1 := htb
  have hcol : ∀ N : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E), N * E1 = N.toCols₁ := by
    intro N
    ext i j
    simp [E1, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, Matrix.toCols₁]
  have h1 : incM F d.b.1 * E1 = incM F (d.b.1.toCols₁) := by
    rw [hcol]
    ext i j
    rfl
  have h2 : incM F ((diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) E) * tb.1) = DC * incM F tb.1 := by
    rw [incM_mul'']
    congr 1
    ext i j
    cases i <;> simp [DC, diagCols, incM, Matrix.one_apply, apply_ite] <;> split_ifs <;> simp_all
  have hb : incM F d.b.1 * E1 = DC * incM F tb.1 := h1.trans ((congrArg (incM F) htb').trans h2)
  have hTb : incM F tb.1 * incM F (tb⁻¹).1 = 1 := by
    rw [← incM_mul'', Units.mul_inv]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hTb' : incM F (tb⁻¹).1 * incM F tb.1 = 1 := by
    rw [← incM_mul'', Units.inv_mul]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hdc : DC = incM F d.b.1 * E1 * incM F (tb⁻¹).1 := by
    rw [hb, Matrix.mul_assoc, hTb, Matrix.mul_one]
  have hME : M * E1 = E1 * M.toBlocks₁₁ := by
    rw [hcol]
    ext i j
    cases i with
    | inl i => simp [E1, Matrix.toCols₁, Matrix.toBlocks₁₁, Matrix.mul_apply, Matrix.one_apply]
    | inr i =>
      have := congrFun (congrFun h21 i) j
      simp only [Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.zero_apply] at this
      simp [E1, Matrix.toCols₁, this, Matrix.mul_apply]
  have hBm : IsUnit (incM F d.b.1) := (Matrix.isUnit_iff_isUnit_det _).2
    (isUnit_iff_exists_inv.2 ⟨_, by rw [← Matrix.det_mul, _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_mul_inv_k d, Matrix.det_one]⟩)
  have hBi : IsUnit (incM F (d.b⁻¹).1) := (Matrix.isUnit_iff_isUnit_det _).2
    (isUnit_iff_exists_inv.2 ⟨_, by rw [← Matrix.det_mul, _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_inv_mul_k d, Matrix.det_one]⟩)
  have hug : IsUnit M := (hBi.mul (Units.isUnit p.1)).mul hBm
  have hgb : M = Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ 0 M.toBlocks₂₂ := by
    rw [← h21, Matrix.fromBlocks_toBlocks]
  have hdet : IsUnit (M.toBlocks₁₁.det * M.toBlocks₂₂.det) := by
    rw [← Matrix.det_fromBlocks_zero₂₁ M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₂, ← hgb]
    exact (Matrix.isUnit_iff_isUnit_det M).1 hug
  have hA : IsUnit M.toBlocks₁₁.det := isUnit_of_mul_isUnit_left hdet
  have hTbu : IsUnit (incM F tb.1).det :=
    isUnit_iff_exists_inv.2 ⟨_, by rw [← Matrix.det_mul, hTb, Matrix.det_one]⟩
  have hTbiu : IsUnit (incM F (tb⁻¹).1).det :=
    isUnit_iff_exists_inv.2 ⟨_, by rw [← Matrix.det_mul, hTb', Matrix.det_one]⟩
  have hu : IsUnit (incM F tb.1 * M.toBlocks₁₁ * incM F (tb⁻¹).1) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_mul, Matrix.det_mul]
    exact (hTbu.mul hA).mul hTbiu
  refine ⟨hu.unit, ?_, ?_⟩
  · show mat2 p * DC = DC * (hu.unit : Matrix (Fin d.n) (Fin d.n) (AE F E))
    rw [IsUnit.unit_spec, _root_.PositivityTheory.SiegelWeilFormula.KWhit.matrixRep_eq_frameConj_inFrame d p]
    change incM F d.b.1 * M * incM F (d.b⁻¹).1 * DC = DC * (incM F tb.1 * M.toBlocks₁₁ * incM F (tb⁻¹).1)
    rw [hdc]
    calc incM F d.b.1 * M * incM F (d.b⁻¹).1 * (incM F d.b.1 * E1 * incM F (tb⁻¹).1)
        = incM F d.b.1 * M * (incM F (d.b⁻¹).1 * incM F d.b.1) * E1 * incM F (tb⁻¹).1 := by
          simp only [Matrix.mul_assoc]
      _ = incM F d.b.1 * (M * E1) * incM F (tb⁻¹).1 := by
          rw [_root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_inv_mul_k d, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = incM F d.b.1 * E1 * (incM F (tb⁻¹).1 * incM F tb.1) * M.toBlocks₁₁ * incM F (tb⁻¹).1 := by
          rw [hME, hTb', Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]
  · rw [Matrix.GeneralLinearGroup.val_det_apply, IsUnit.unit_spec, Matrix.det_mul, Matrix.det_mul, mul_comm _ M.toBlocks₁₁.det,
      mul_assoc, ← Matrix.det_mul, hTb, Matrix.det_one, mul_one]
theorem a_mul_par_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {q : d.G} {t : GL (Fin d.n) (AE F E)} (hq : IsPar q t) (y : d.G) :
    d.a (q * y) = (absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) * d.a y := by
  obtain ⟨p, t', hp, k, hk, rfl⟩ := d.ok.hgt.iwa y
  rw [← mul_assoc, d.ok.hgt.val _ _ (KSplitP.isPar_mul hq hp) k hk, d.ok.hgt.val p t' hp k hk, map_mul, map_mul,
    NNReal.coe_mul]
end PositivityTheory.SiegelWeilFormula.Avac
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTbijMain
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.RatWeilOp
namespace PositivityTheory.SiegelWeilFormula.TBij
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace Adp
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.card_ix (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : Fintype.card d.κ = Fintype.card (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) := by
  rw [card_eq d.bs d.dd.e, Fintype.card_prod, Fintype.card_prod, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin,
    Fintype.card_fin]
  ring
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.core (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : ∃ (τ : d.κ ≃ _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) (e : ((d.κ → AF F) → ℂ) →ₗ[ℂ] d.Fn) (C : ℂ), C ≠ 0 ∧
    Set.BijOn e (schA F d.κ : Set _) (schA F d.κ : Set _) ∧
    (∀ l ∈ (adeleClass F).adm d.κ, l ∘ₗ e ∈ (adeleClass F).adm d.κ) ∧
    ∀ Ψ ∈ schA F d.κ, ∀ X, d.T (e Ψ) X = C * Ψ (fun k => d.crd X (τ k)) := by
  classical
  have hψ : IsStd d.B.ψ := d.ok.good.std
  have hF : IsTotallyReal F := d.ok.good.cm.1
  have hD := d.ok.dbl
  let τ : d.κ ≃ _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d := Fintype.equivOfCardEq (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.card_ix d)
  obtain ⟨a, ha, hact⟩ := exists_symp d.dd.e (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.c0 d τ) (fun w w' => by rw [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.symplecticForm_coordinates, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_eq]) (by
    rintro w ⟨y, z, h⟩
    obtain ⟨x, hx⟩ := rat_surj d.bs d.dd.e (fun x => hD.rat x) y z
    obtain rfl : w = incM F x := d.dd.e.injective (h.trans hx.symm)
    exact _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.coordinates_rational d τ x)
  set J := jj d.κ F with hJ
  set b := -(J * aᵀ * J) with hb
  have hba : b * a = 1 := by
    rw [hb, Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc aᵀ, ha, jj_mul_jj, neg_neg]
  have hab : a * b = 1 := mul_eq_one_comm.1 hba
  have hbs : bᵀ * J * b = J := by
    calc bᵀ * J * b = bᵀ * (aᵀ * J * a) * b := by rw [ha]
      _ = (a * b)ᵀ * J * (a * b) := by simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = J := by rw [hab, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
  obtain ⟨e, c, ei, ev, h⟩ := hasOp_of_symplectic hF hψ b hbs
  have hinv : ∀ w, act (b.map (algebraMap F (AF F))) (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.c0 d τ w) = d.dd.e w := fun w => by
    rw [hact w, ← act_mul, ← Matrix.map_mul, hba, Matrix.map_one _ (map_zero _) (map_one _), act_one']
  have hsurj : ∀ u, ∃ w, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.c0 d τ w = u := fun u => ⟨d.dd.e.symm (act (b.map (algebraMap F (AF F))) u), by
    rw [hact, LinearEquiv.apply_symm_apply, ← act_mul, ← Matrix.map_mul, hab,
      Matrix.map_one _ (map_zero _) (map_one _), act_one']⟩
  have hheis : ∀ w, ∀ Ψ ∈ schA F d.κ, e (schr d.B.ψ (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.c0 d τ w) Ψ) = d.dd.rho d.B.ψ w (e Ψ) := fun w Ψ hΨ => by
    rw [h.Heisenberg₂ _ Ψ hΨ, hinv]
    rfl
  have hadm := isOp_adm h d.l hD.adm
  obtain ⟨C, hC⟩ := GlobalTheory.T.character_invariant_adelic_form_eq_mul_eval_zero F d.B.ψ hψ d.κ (d.l ∘ₗ e) hadm (fun y φ hφ => by
    obtain ⟨w, hw⟩ := hsurj (0, y)
    obtain ⟨Z, rfl⟩ := _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.coordinates_fst_eq_zero d τ w (by rw [hw])
    have e1 : (fun x => d.B.ψ (x ⬝ᵥ y) * φ x) = schr d.B.ψ (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.c0 d τ (Z * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.dg d)ᵀ)) φ := by
      rw [hw]; funext x; simp [schr]
    rw [LinearMap.comp_apply, LinearMap.comp_apply, e1, hheis _ φ hφ]
    exact hD.kill Z _ (h.maps φ hφ))
  have hT : ∀ Ψ ∈ schA F d.κ, ∀ X, d.T (e Ψ) X = C * Ψ (fun k => d.crd X (τ k)) := fun Ψ hΨ X => by
    have h1 := hC _ (GlobalTheory.HeisSchA.schr_mem_schA d.B.ψ hψ (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.c0 d τ (X * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.yy d)ᵀ)) Ψ hΨ)
    rw [LinearMap.comp_apply, hheis _ Ψ hΨ, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.coordinates_frame] at h1
    rw [_root_.PositivityTheory.SiegelWeilFormula.SD_k.T, h1]
    simp [schr]
  refine ⟨τ, e, C, fun hC0 => ?_, h.bijOn hψ, fun l hl => isOp_adm h l hl, hT⟩
  obtain ⟨Φ, hΦ, hθ⟩ := GlobalTheory.ThetaSumNe.exists_mem_schA_thetaSum_ne_zero F d.κ
  obtain ⟨Ψ, hΨ, rfl⟩ := (h.bijOn hψ).surjOn hΦ
  have h0 : ∀ y : Matrix (Fin d.m) (Fin d.n) E,
      d.l (d.dd.rho d.B.ψ (incM F (Matrix.fromCols y (-y))) (e Ψ)) = 0 := fun y => by
    rw [← hheis _ Ψ hΨ]
    have := hC _ (GlobalTheory.HeisSchA.schr_mem_schA d.B.ψ hψ (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.c0 d τ (incM F (Matrix.fromCols y (-y)))) Ψ hΨ)
    rw [LinearMap.comp_apply] at this
    rw [this, hC0, zero_mul]
  have h2 := hD.theta (e Ψ) hΦ
  simp only [h0] at h2
  exact hθ (h2.unique hasSum_zero)
end Adp
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.tBij : _root_.PositivityTheory.SiegelWeilFormula.TBij_k := by
  intro F E _ _ _ _ _ σ d
  obtain ⟨τ, e, C, hC, hbij, -, hT⟩ := _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.core d
  have hcomp : ∀ Ψ ∈ schA F d.κ, (fun c => d.T (e Ψ) (d.cmb c)) = C • fun x : _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d → AF F => Ψ (x ∘ τ) :=
    fun Ψ hΨ => by
      funext c
      rw [hT Ψ hΨ, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.crd_cmb]
      rfl
  refine ⟨fun Φ hΦ => ?_, fun f hf => ?_, fun Φ hΦ h0 => ?_⟩
  · obtain ⟨Ψ, hΨ, rfl⟩ := hbij.surjOn hΦ
    show (fun c => d.T (e Ψ) (d.cmb c)) ∈ schA F (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d)
    rw [hcomp Ψ hΨ]
    exact Submodule.smul_mem _ C (comp_schA τ hΨ)
  · have hg : (fun c => f (d.cmb c)) ∈ schA F (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) := hf
    have hΨ : C⁻¹ • (fun x : d.κ → AF F => f (d.cmb (x ∘ τ.symm))) ∈ schA F d.κ :=
      Submodule.smul_mem _ _ (comp_schA τ.symm hg)
    refine ⟨e _, hbij.mapsTo hΨ, funext fun X => ?_⟩
    rw [hT _ hΨ]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← mul_assoc, mul_inv_cancel₀ hC, one_mul]
    congr 1
    conv_rhs => rw [← _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.cmb_crd d X]
    congr 1
    funext i
    simp
  · obtain ⟨Ψ, hΨ, rfl⟩ := hbij.surjOn hΦ
    have hz : Ψ = 0 := by
      funext v
      have := congrFun h0 (d.cmb (v ∘ τ.symm))
      rw [hT Ψ hΨ, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.crd_cmb] at this
      simpa [hC] using this
    rw [hz, map_zero]
end PositivityTheory.SiegelWeilFormula.TBij
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.FrameSignEqInvolutionScalar
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KWhit
open PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem rel_frame_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (ε : ℤˣ)
    (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) (y : d.G) :
    (inFrame d.b y)ᵀ * Matrix.fromBlocks 0 1 (((ε : ℤ) : AE F E) • 1) 0 * (inFrame d.b y).map (cA σ) =
      Matrix.fromBlocks 0 1 (((ε : ℤ) : AE F E) • 1) 0 := by
  have e1 : (incM F d.b.1).map (cA σ) = incM F (d.b.1.map σ) := by
    ext i j
    simp [incM, cA, inclR, Algebra.TensorProduct.map_tmul]
  have e2 : dbl (incM F d.Y.J) = incM F (dbl d.Y.J) := by
    simp [dbl, incM, Matrix.fromBlocks_map, Matrix.map_neg]
  have key : incM F (d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ) =
      (incM F d.b.1)ᵀ * incM F (dbl d.Y.J) * incM F (d.b.1.map σ) := by
    simp only [incM, Matrix.map_mul, Matrix.transpose_map]
  have hF : (incM F d.b.1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1).map (cA σ) =
      Matrix.fromBlocks 0 1 (((ε : ℤ) : AE F E) • 1) 0 := by
    rw [e1, e2, ← key, hε]
    simp only [incM, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero _), Matrix.map_one _ (map_zero _) (map_one _)]
    congr 1
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hM : (mat2 y)ᵀ * dbl (incM F d.Y.J) * (mat2 y).map (cA σ) = dbl (incM F d.Y.J) := y.2
  have := form_conj_in (cA σ).toRingHom (_root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_mul_inv_k d) hM
  rw [← hF]
  exact this
theorem rel_nA_cond_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (ε : ℤˣ)
    (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) (β : nA σ d.Y d.b) :
    β.1ᵀ + ((ε : ℤ) : AE F E) • β.1.map (cA σ) = 0 := by
  obtain ⟨β, hβ⟩ := β
  show βᵀ + ((ε : ℤ) : AE F E) • β.map (cA σ) = 0
  induction hβ using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨y, hy⟩ := hx
    have h := _root_.PositivityTheory.SiegelWeilFormula.KWhit.rel_frame_k d ε hε y
    rw [hy] at h
    simp only [Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.transpose_zero,
      Matrix.transpose_one, Matrix.map_zero _ (map_zero (cA σ)), Matrix.map_one _ (map_zero (cA σ)) (map_one (cA σ)),
      Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul,
      Matrix.fromBlocks_inj] at h
    rw [add_comm]
    have h4 := h.2.2.2
    rw [Matrix.smul_mul, Matrix.one_mul] at h4
    exact h4
  | zero => simp
  | add x y _ _ hx hy =>
    rw [Matrix.transpose_add, Matrix.map_add _ (map_add (cA σ)), smul_add]
    calc _ = (xᵀ + ((ε : ℤ) : AE F E) • x.map (cA σ)) + (yᵀ + ((ε : ℤ) : AE F E) • y.map (cA σ)) := by abel
      _ = 0 := by rw [hx, hy, add_zero]
  | neg x _ hx =>
    rw [Matrix.transpose_neg, Matrix.map_neg _ (map_neg (cA σ)), smul_neg, ← neg_add, hx, neg_zero]
theorem frameSign_eq_involution_scalar (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (hσ : ∀ x, σ (σ x) = x) (ε : ℤˣ)
    (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) (c : E)
    (hc : d.Y.J.map σ = c • d.Y.Jᵀ) (i : Fin d.n) : ((ε : ℤ) : E) = c := by
  have hD : (dbl d.Y.J).map σ = c • (dbl d.Y.J)ᵀ := by
    simp only [dbl, Matrix.fromBlocks_map, Matrix.fromBlocks_transpose, Matrix.fromBlocks_smul, hc,
      Matrix.map_neg _ (map_neg σ), Matrix.map_zero _ (map_zero σ), Matrix.transpose_zero, Matrix.transpose_neg,
      smul_zero, smul_neg]
  have hbb : (d.b.1.map σ).map σ = d.b.1 := by
    ext i j
    simp [hσ]
  have h1 := congrArg σ.mapMatrix hε
  simp only [map_mul, AlgHom.mapMatrix_apply, hD, hbb] at h1
  have h2 := congrArg Matrix.transpose h1
  simp only [Matrix.transpose_mul, Matrix.transpose_smul, Matrix.transpose_transpose, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.transpose_map] at h2
  rw [← Matrix.mul_assoc, hε] at h2
  have := congrFun (congrFun h2 (Sum.inr i)) (Sum.inl i)
  simp [Matrix.fromBlocks_map] at this
  have hε2 : ((ε : ℤ) : E) * ((ε : ℤ) : E) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
    simp
  calc ((ε : ℤ) : E) = ((ε : ℤ) : E) * (c * ((ε : ℤ) : E)) := by rw [this, mul_one]
    _ = c * (((ε : ℤ) : E) * ((ε : ℤ) : E)) := by ring
    _ = c := by rw [hε2, mul_one]
theorem rel_sign_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (ε : ℤˣ)
    (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) :
    ((∀ i j, σ (d.Y.J j i) = -d.Y.J i j) → ε = -1) ∧ ((∀ i j, σ (d.Y.J j i) = d.Y.J i j) → ε = 1) := by
  have hσ := rel_sigma_sigma d.ok.good.cm
  have i : Fin d.n := ⟨0, d.ok.hn⟩
  constructor
  · intro h
    have := _root_.PositivityTheory.SiegelWeilFormula.KWhit.frameSign_eq_involution_scalar d hσ ε hε (-1) (by ext a b; simp [h b a]) i
    exact Units.ext (Int.cast_injective (α := E) (by simpa using this))
  · intro h
    have := _root_.PositivityTheory.SiegelWeilFormula.KWhit.frameSign_eq_involution_scalar d hσ ε hε 1 (by ext a b; simp [h b a]) i
    exact Units.ext (Int.cast_injective (α := E) (by simpa using this))
theorem rel_eta_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (ε : ℤˣ)
    (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) :
    ∃ η : E, η ≠ 0 ∧ σ η = -(((ε : ℤ) : E) * η) ∧ ∀ i j, σ (η * d.A.J j i) = η * d.A.J i j := by
  rcases d.ok.sign with ⟨hA, hY⟩ | ⟨hA, hY⟩
  · have he := (_root_.PositivityTheory.SiegelWeilFormula.KWhit.rel_sign_k d ε hε).1 hY
    subst he
    refine ⟨1, one_ne_zero, by simp, fun i j => by simp [hA.herm i j]⟩
  · have he := (_root_.PositivityTheory.SiegelWeilFormula.KWhit.rel_sign_k d ε hε).2 hY
    subst he
    obtain ⟨η, hη, hση⟩ := rel_anti d.ok.good.cm
    refine ⟨η, hη, by simp [hση], fun i j => ?_⟩
    rw [map_mul, hση, hA.skew i j, neg_mul_neg]
end PositivityTheory.SiegelWeilFormula.KWhit
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAvacIwaB
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Avac
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
open GlobalTheory.Doubling (absE)
theorem par_frame_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (p : d.G) (h21 : (inFrame d.b p).toBlocks₂₁ = 0) :
    ∃ (n0 m0 : d.G) (A D : GL (Fin d.n) (AE F E)),
      inFrame d.b n0 = Matrix.fromBlocks 1 ((inFrame d.b p).toBlocks₁₂ * (inFrame d.b p).toBlocks₂₂⁻¹) 0 1 ∧
      inFrame d.b m0 = Matrix.fromBlocks A.1 0 0 D.1 ∧ A.1 = (inFrame d.b p).toBlocks₁₁ ∧
      D.1 = (inFrame d.b p).toBlocks₂₂ ∧ p = n0 * m0 := by
  set g := inFrame d.b p with hg
  set A := g.toBlocks₁₁
  set B := g.toBlocks₁₂
  set D := g.toBlocks₂₂
  have hgb : g = Matrix.fromBlocks A B 0 D := by rw [← h21, Matrix.fromBlocks_toBlocks]
  have hBm : IsUnit (incM F d.b.1) := (Matrix.isUnit_iff_isUnit_det _).2
    (isUnit_iff_exists_inv.2 ⟨_, by rw [← Matrix.det_mul, _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_mul_inv_k d, Matrix.det_one]⟩)
  have hBi : IsUnit (incM F (d.b⁻¹).1) := (Matrix.isUnit_iff_isUnit_det _).2
    (isUnit_iff_exists_inv.2 ⟨_, by rw [← Matrix.det_mul, _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_inv_mul_k d, Matrix.det_one]⟩)
  have hug : IsUnit g := (hBi.mul (Units.isUnit p.1)).mul hBm
  have hdet : IsUnit (A.det * D.det) := by
    rw [← Matrix.det_fromBlocks_zero₂₁ A B D, ← hgb]
    exact (Matrix.isUnit_iff_isUnit_det g).1 hug
  have hA : IsUnit A.det := isUnit_of_mul_isUnit_left hdet
  have hD : IsUnit D.det := isUnit_of_mul_isUnit_right hdet
  set Md : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) := Matrix.fromBlocks A 0 0 D with hMd_def
  have hMd : IsUnit Md := (Matrix.isUnit_iff_isUnit_det _).2 (by rw [hMd_def, Matrix.det_fromBlocks_zero₂₁]; exact hA.mul hD)
  obtain ⟨C', hC'⟩ := _root_.PositivityTheory.SiegelWeilFormula.KWhit.frame_form_k d
  have hP : (mat2 p)ᵀ * dbl (incM F d.Y.J) * (mat2 p).map (cA σ).toRingHom = dbl (incM F d.Y.J) := p.2
  have hgf := KWhit.form_conj_in (cA σ).toRingHom (_root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_mul_inv_k d) hP
  have hC'' : (incM F d.b.1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1).map (cA σ).toRingHom =
      Matrix.fromBlocks 0 1 C' 0 := hC'
  rw [hC''] at hgf
  have hgf' : gᵀ * Matrix.fromBlocks 0 1 C' 0 * g.map (cA σ).toRingHom = Matrix.fromBlocks 0 1 C' 0 := hgf
  rw [hgb] at hgf'
  have hMdf := KWhit.block_diag_form (cA σ).toRingHom A B D C' hgf'
  rw [← hC''] at hMdf
  have hM0mem := KWhit.form_conj_out (cA σ).toRingHom (_root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_mul_inv_k d) hMdf
  have hM0u : IsUnit (incM F d.b.1 * Md * incM F (d.b⁻¹).1) := (hBm.mul hMd).mul hBi
  let u : GL (Fin d.n ⊕ Fin d.n) (AE F E) := hM0u.unit
  have hu : (u : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) =
      incM F d.b.1 * Md * incM F (d.b⁻¹).1 := IsUnit.unit_spec hM0u
  have hmem : u ∈ UG (cA σ) (dbl (incM F d.Y.J)) := by
    show (u : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E))ᵀ * dbl (incM F d.Y.J) *
      (u : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)).map (cA σ) = dbl (incM F d.Y.J)
    rw [hu]
    exact hM0mem
  let m0 : d.G := ⟨u, hmem⟩
  have hm0 : inFrame d.b m0 = Md := by
    show incM F (d.b⁻¹).1 * (u : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) * incM F d.b.1 = Md
    rw [hu]
    simp only [← Matrix.mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_inv_mul_k d, Matrix.one_mul]
    rw [Matrix.mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_inv_mul_k d, Matrix.mul_one]
  have hAu := (Matrix.isUnit_iff_isUnit_det A).2 hA
  have hDu := (Matrix.isUnit_iff_isUnit_det D).2 hD
  refine ⟨p * m0⁻¹, m0, hAu.unit, hDu.unit, ?_, ?_, IsUnit.unit_spec hAu, IsUnit.unit_spec hDu,
    (inv_mul_cancel_right p m0).symm⟩
  · have e := _root_.PositivityTheory.SiegelWeilFormula.KWhit.inFrame_mul_k d (p * m0⁻¹) m0
    rw [inv_mul_cancel_right, hm0] at e
    apply (hMd.mul_left_inj).1
    rw [← e, ← hg, hgb, hMd_def, Matrix.fromBlocks_multiply]
    simp [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hD]
  · rw [hm0, IsUnit.unit_spec, IsUnit.unit_spec]
theorem q_T'_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (i₀ : Fin d.n) {q : d.G} {lam : (AE F E)ˣ} (hq : IsQ F E i₀ (inFrame d.b q) lam) :
    ∃ c : ℂ, ∀ Φ ∈ d.sch, ∀ X : Mx F E d.m d.n, (∀ a, X a i₀ = 0) → d.T (d.om q Φ) X = c * d.T Φ X := by
  set M := inFrame d.b q with hM
  obtain ⟨n0, m0, A, D, hn, hm, hA, hD, hp⟩ := _root_.PositivityTheory.SiegelWeilFormula.Avac.par_frame_k d q (isQ_21 hq)
  refine ⟨(d.χ (Matrix.GeneralLinearGroup.det A) : ℂ) *
    (((absE F E (Matrix.GeneralLinearGroup.det A) : ℝ) ^ ((d.m : ℝ) / 2) : ℝ) : ℂ), fun Φ hΦ X hX => ?_⟩
  have hD1 : ∀ j k, k ≠ i₀ → D.1 j k = (1 : Matrix (Fin d.n) (Fin d.n) (AE F E)) j k := by
    rw [hD]; exact isQ_22 hq
  have hDu : IsUnit M.toBlocks₂₂.det := by
    rw [← hD]; exact (Matrix.isUnit_iff_isUnit_det _).1 D.isUnit
  have hDi : ∀ j k, k ≠ i₀ → M.toBlocks₂₂⁻¹ j k = (1 : Matrix (Fin d.n) (Fin d.n) (AE F E)) j k :=
    inv_col (isQ_22 hq) (Matrix.nonsing_inv_mul _ hDu)
  have hβ : ∀ i j, i ≠ i₀ → j ≠ i₀ → (M.toBlocks₁₂ * M.toBlocks₂₂⁻¹) i j = 0 := by
    intro i j hi hj
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k = i₀
    · subst hk; rw [hDi _ _ hj, Matrix.one_apply_ne (Ne.symm hj), mul_zero]
    · rw [isQ_12 hq i k hi hk, zero_mul]
  have hG : ∀ i j, (i = i₀ ∨ j = i₀) → d.gram X X i j = 0 := by
    intro i j hij
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.gram, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
    refine Finset.sum_eq_zero fun b _ => ?_
    rcases hij with rfl | rfl
    · rw [Finset.sum_mul]
      refine Finset.sum_eq_zero fun a _ => ?_
      rw [hX a, zero_mul, zero_mul]
    · rw [hX b, map_zero, mul_zero]
  have htt : d.tt ((M.toBlocks₁₂ * M.toBlocks₂₂⁻¹) * d.gram X X) = 0 := by
    have : Matrix.trace ((M.toBlocks₁₂ * M.toBlocks₂₂⁻¹) * d.gram X X) = 0 := by
      simp only [Matrix.trace, Matrix.diag]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun j _ => ?_
      by_cases h : i = i₀ ∨ j = i₀
      · rw [hG j i (h.symm), mul_zero]
      · push_neg at h
        rw [hβ i j h.1 h.2, zero_mul]
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, this, map_zero]
  have hXD : X * (D⁻¹).1ᵀ = X := by
    have h1 : X * D.1ᵀ = X := by
      ext a j
      rw [Matrix.mul_apply]
      rw [Finset.sum_eq_single j]
      · rw [Matrix.transpose_apply]
        by_cases hj : j = i₀
        · subst hj; rw [hX a, zero_mul]
        · rw [hD1 j j hj, Matrix.one_apply_eq, mul_one]
      · intro k _ hk
        rw [Matrix.transpose_apply]
        by_cases hk0 : k = i₀
        · subst hk0; rw [hX a, zero_mul]
        · rw [hD1 j k hk0, Matrix.one_apply_ne (Ne.symm hk), mul_zero]
      · simp
    calc X * (D⁻¹).1ᵀ = X * D.1ᵀ * (D⁻¹).1ᵀ := by rw [h1]
      _ = X * ((D⁻¹).1 * D.1)ᵀ := by rw [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = X := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.transpose_one, Matrix.mul_one]
  have hm0s : d.om m0 Φ ∈ d.sch := _root_.PositivityTheory.SiegelWeilFormula.KWhit.om_mem_sch_k d m0 hΦ
  rw [hp, map_mul, Module.End.mul_apply, (hT.2.1 F E σ d _ hm0s).1 n0 _ hn X, htt, mul_zero, neg_zero,
    AddChar.map_zero_eq_one, one_mul, (hT.2.1 F E σ d Φ hΦ).2.1 m0 A D hm X, hXD]
end PositivityTheory.SiegelWeilFormula.Avac
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilActCut
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Act
def IndepDom_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d), ∀ s₁ f, IsSec d.K d.χ s₁ f → ∀ z : ℂ,
  (∀ nb lam 𝓖 𝓖₀, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖 → CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖₀ →
    ∀ uM ν 𝓤 𝓤₀, L.UData uM ν 𝓤 → L.UData uM ν 𝓤₀ → ∀ T T', L.IsSub T T' → ∀ x,
      ∫ u in 𝓤, fc d.B.ψ d.b nb lam 𝓖 (d.eis f s₁ z) T (uM u * x) ∂ν =
        ∫ u in 𝓤₀, fc d.B.ψ d.b nb lam 𝓖₀ (d.eis f s₁ z) T (uM u * x) ∂ν) ∧
  ∀ nb' lam' 𝓖' 𝓖'₀, CoefData (σ := σ) (Y := L.Y) L.b nb' lam' 𝓖' → CoefData (σ := σ) (Y := L.Y) L.b nb' lam' 𝓖'₀ →
    ∀ T' x, _root_.PositivityTheory.SiegelWeilFormula.Act.first_k L f s₁ z nb' lam' 𝓖' T' x = _root_.PositivityTheory.SiegelWeilFormula.Act.first_k L f s₁ z nb' lam' 𝓖'₀ T' x
def CptDom_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ),
  (∀ nb lam 𝓖, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖 →
    ∃ 𝓖₀, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖₀ ∧ IsCompact (closure 𝓖₀)) ∧
  ∀ L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d, ∀ uM ν 𝓤, L.UData uM ν 𝓤 → ∃ 𝓤₀, L.UData uM ν 𝓤₀ ∧ IsCompact (closure 𝓤₀)
def AbsConv_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d), ∀ s₁ f, IsSec d.K d.χ s₁ f → d.Eis f s₁ → ∃ t : ℝ, ∀ z : ℂ, t < z.re →
  ∀ nb lam 𝓖, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖 → IsCompact (closure 𝓖) →
  ∀ uM ν 𝓤, L.UData uM ν 𝓤 → IsCompact (closure 𝓤) → ∀ (T : nF σ d.Y d.b) (x : d.G),
    (∀ q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d, Integrable (_root_.PositivityTheory.SiegelWeilFormula.Act.kq_k L f s₁ z nb T uM (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q) x) ((ν.restrict 𝓤).prod (lam.restrict 𝓖))) ∧
    Summable fun q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d => ∫ p, ‖_root_.PositivityTheory.SiegelWeilFormula.Act.kq_k L f s₁ z nb T uM (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q) x p‖ ∂((ν.restrict 𝓤).prod (lam.restrict 𝓖))
def FirstEq_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d), ∀ s₁ f, IsSec d.K d.χ s₁ f → d.Eis f s₁ → ∃ t : ℝ, ∀ z : ℂ, t < z.re →
  ∀ nb lam 𝓖, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖 → IsCompact (closure 𝓖) →
  ∀ nb' lam' 𝓖', CoefData (σ := σ) (Y := L.Y) L.b nb' lam' 𝓖' → IsCompact (closure 𝓖') →
  ∀ uM ν 𝓤, L.UData uM ν 𝓤 → IsCompact (closure 𝓤) → ∀ T T', L.IsSub T T' → ∀ x,
    ∑' q : {q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d // _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q)}, _root_.PositivityTheory.SiegelWeilFormula.Act.tm_k L f s₁ z nb lam 𝓖 T uM ν 𝓤 (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q.1) x = _root_.PositivityTheory.SiegelWeilFormula.Act.first_k L f s₁ z nb' lam' 𝓖' T' x
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} in
structure CLaw_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (w₁ : d.G) (cM : (Fin L.n → AE F E) × AF F → d.G)
    (κ : Measure ((Fin L.n → AE F E) × AF F)) : Prop where
  comm : ∀ w (τ : ℝ) (y : GR d.n) (g : G2 σ L.Y), IsDil (Pi.single L.i₀ 1) τ y → L.j g * R.ι w y = R.ι w y * L.j g
  wdil : ∀ w (τ : ℝ) (y : GR d.n), IsDil (Pi.single L.i₀ 1) τ y → ∃ p t, IsPar p t ∧
    (absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) = Real.exp (-(2 * τ)) ∧
    (d.χ (Matrix.GeneralLinearGroup.det t) : ℂ) = 1 ∧ w₁ * R.ι w y = p * w₁
  cdil : ∀ w (τ : ℝ) (y : GR d.n), IsDil (Pi.single L.i₀ 1) τ y →
    ∃ sc : ((Fin L.n → AE F E) × AF F) ≃ᵐ ((Fin L.n → AE F E) × AF F), (∀ c, cM c * R.ι w y = R.ι w y * cM (sc c)) ∧
      κ.map sc = ENNReal.ofReal (Real.exp (2 * d.n * τ)) • κ
def SecUnf_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d), ∀ s₁ f, IsSec d.K d.χ s₁ f → d.Eis f s₁ →
  ∃ t : ℝ, ∀ z : ℂ, t < z.re →
  ∀ nb lam 𝓖, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖 → IsCompact (closure 𝓖) →
  ∀ uM ν 𝓤, L.UData uM ν 𝓤 → IsCompact (closure 𝓤) → ∀ T T', L.IsSub T T' →
  ∀ nb' lam' 𝓖', CoefData (σ := σ) (Y := L.Y) L.b nb' lam' 𝓖' → IsCompact (closure 𝓖') →
  ∃ w₁ cM κ, _root_.PositivityTheory.SiegelWeilFormula.Act.CLaw_k R L w₁ cM κ ∧ ∃ K : ℂ, ∀ x,
    _root_.PositivityTheory.SiegelWeilFormula.Act.secondOrbitSection L f s₁ z nb lam 𝓖 T uM ν 𝓤 x = K * ∑' q' : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd, ∫ β in 𝓖',
      (∫ c, _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (w₁ * (cM c * (L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q' * nb' β) * x))) ∂κ) * d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T'.1.1 * β.1)))) ∂lam'
def SecLaw_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d), ∀ s₁ f, IsSec d.K d.χ s₁ f → d.Eis f s₁ →
  ∃ t : ℝ, ∀ z : ℂ, t < z.re →
  ∀ nb lam 𝓖, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖 → IsCompact (closure 𝓖) →
  ∀ uM ν 𝓤, L.UData uM ν 𝓤 → IsCompact (closure 𝓤) → ∀ T T', L.IsSub T T' →
  ∀ nb' lam' 𝓖', CoefData (σ := σ) (Y := L.Y) L.b nb' lam' 𝓖' → IsCompact (closure 𝓖') →
  ∀ w (τ : ℝ) (y : GR d.n) x, IsDil (Pi.single L.i₀ 1) τ y →
    _root_.PositivityTheory.SiegelWeilFormula.Act.secondOrbitSection L f s₁ z nb lam 𝓖 T uM ν 𝓤 (R.ι w y * x) = Complex.exp (τ * (d.n - 2 * z)) * _root_.PositivityTheory.SiegelWeilFormula.Act.secondOrbitSection L f s₁ z nb lam 𝓖 T uM ν 𝓤 x
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} in
theorem phz_par_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} {f : d.G → ℂ} {s₁ : ℂ} (hf : IsSec d.K d.χ s₁ f) (z : ℂ) {τ : ℝ} {p : d.G} {t : GL (Fin d.n) (AE F E)}
    (hp : IsPar p t) (ha : (absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) = Real.exp (-(2 * τ)))
    (hχ : (d.χ (Matrix.GeneralLinearGroup.det t) : ℂ) = 1) (g : d.G) :
    _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (p * g) = Complex.exp (-(τ * (2 * z + d.n))) * _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z g := by
  have hH : ((d.Ht (p * g) : ℝ) : ℂ) = (Real.exp (-(2 * τ)) : ℂ) * ((d.Ht g : ℝ) : ℂ) := by
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.Ht]
    rw [d.ok.hgt.mul hp, ha, Real.toNNReal_mul (Real.exp_pos _).le, NNReal.coe_mul, Real.coe_toNNReal _ (Real.exp_pos _).le,
      Complex.ofReal_mul]
  have he : ∀ w : ℂ, ((Real.exp (-(2 * τ)) : ℝ) : ℂ) ^ w = Complex.exp (-(2 * τ) * w) := by
    intro w
    rw [Complex.ofReal_exp, Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _), Complex.log_exp] <;> push_cast <;> simp [Real.pi_pos, Real.pi_pos.le]
  unfold _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k
  rw [hH, Complex.mul_cpow_ofReal_nonneg (Real.exp_pos _).le NNReal.zero_le_coe, hf.law p t g hp, hχ, ha, he, he,
    ← mul_assoc]
  have : Complex.exp (-(τ * (2 * z + d.n))) = Complex.exp (-(2 * τ) * (z - s₁)) * Complex.exp (-(2 * τ) * (s₁ + d.n / 2)) := by
    rw [← Complex.exp_add]; congr 1; ring
  rw [this]; ring
theorem secLaw_of_k : _root_.PositivityTheory.SiegelWeilFormula.Act.SecUnf_k → _root_.PositivityTheory.SiegelWeilFormula.Act.SecLaw_k := by
  intro hU F E _ _ _ _ _ σ d R L s₁ f hf he
  obtain ⟨t, ht⟩ := hU F E σ d R L s₁ f hf he
  refine ⟨t, fun z hz nb lam 𝓖 hc hcG uM ν 𝓤 hUd hcU T T' hTT' nb' lam' 𝓖' hc' hcG' w τ y x hy => ?_⟩
  obtain ⟨w₁, cM, κ, hL, K, hK⟩ := ht z hz nb lam 𝓖 hc hcG uM ν 𝓤 hUd hcU T T' hTT' nb' lam' 𝓖' hc' hcG'
  obtain ⟨p, tp, hp, ha, hχ, hw⟩ := hL.wdil w τ y hy
  obtain ⟨sc, hsc, hκ⟩ := hL.cdil w τ y hy
  have key : ∀ h : G2 σ L.Y, ∫ c, _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (w₁ * (cM c * (L.j h * (R.ι w y * x)))) ∂κ =
      Complex.exp (τ * (d.n - 2 * z)) * ∫ c, _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (w₁ * (cM c * (L.j h * x))) ∂κ := by
    intro h
    have h1 : ∀ c, w₁ * (cM c * (L.j h * (R.ι w y * x))) = p * (w₁ * (cM (sc c) * (L.j h * x))) := by
      intro c
      rw [← mul_assoc (L.j h), hL.comm w τ y h hy, mul_assoc, ← mul_assoc (cM c), hsc c, mul_assoc, ← mul_assoc w₁, hw,
        mul_assoc]
    simp_rw [h1, _root_.PositivityTheory.SiegelWeilFormula.Act.phz_par_k hf z hp ha hχ]
    rw [integral_const_mul, ← integral_map_equiv sc (fun c => _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (w₁ * (cM c * (L.j h * x)))), hκ,
      integral_smul_measure, ENNReal.toReal_ofReal (Real.exp_pos _).le, Complex.real_smul, ← mul_assoc]
    congr 1
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1; push_cast; ring
  rw [hK, hK]
  simp_rw [key, mul_assoc (Complex.exp _), integral_const_mul]
  rw [tsum_mul_left]; ring
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} in
theorem lhs_eq_tsum_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (f : d.G → ℂ) (s₁ z : ℂ) (nb : nA σ d.Y d.b → d.G) (lam : Measure (nA σ d.Y d.b))
    (𝓖 : Set (nA σ d.Y d.b)) (T : nF σ d.Y d.b) (uM : (Fin L.n → AE F E) → d.G) (ν : Measure (Fin L.n → AE F E))
    (𝓤 : Set (Fin L.n → AE F E)) (hν : ν 𝓤 = 1) (hlam : lam 𝓖 = 1) (x : d.G)
    (hi : ∀ q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d, Integrable (_root_.PositivityTheory.SiegelWeilFormula.Act.kq_k L f s₁ z nb T uM (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q) x) ((ν.restrict 𝓤).prod (lam.restrict 𝓖)))
    (hs : Summable fun q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d => ∫ p, ‖_root_.PositivityTheory.SiegelWeilFormula.Act.kq_k L f s₁ z nb T uM (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q) x p‖ ∂((ν.restrict 𝓤).prod (lam.restrict 𝓖))) :
    Summable (fun q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d => _root_.PositivityTheory.SiegelWeilFormula.Act.tm_k L f s₁ z nb lam 𝓖 T uM ν 𝓤 (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q) x) ∧
      ∫ u in 𝓤, fc d.B.ψ d.b nb lam 𝓖 (d.eis f s₁ z) T (uM u * x) ∂ν = ∑' q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d, _root_.PositivityTheory.SiegelWeilFormula.Act.tm_k L f s₁ z nb lam 𝓖 T uM ν 𝓤 (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q) x := by
  have : Countable (rat2 σ d.Y) := GlobalTheory.EisBL.DoubledGroupTopology.countable_rational_points_doubled σ d.Y
  have : Countable (_root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d) := Quotient.countable
  have : IsFiniteMeasure (ν.restrict 𝓤) := isFiniteMeasure_restrict.2 (by simp [hν])
  have : IsFiniteMeasure (lam.restrict 𝓖) := isFiniteMeasure_restrict.2 (by simp [hlam])
  obtain ⟨h1, h2⟩ := exch (fun q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d => _root_.PositivityTheory.SiegelWeilFormula.Act.kq_k L f s₁ z nb T uM (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q) x) hi hs
  have htm : ∀ q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d, _root_.PositivityTheory.SiegelWeilFormula.Act.tm_k L f s₁ z nb lam 𝓖 T uM ν 𝓤 (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q) x =
      ∫ u, ∫ v, _root_.PositivityTheory.SiegelWeilFormula.Act.kq_k L f s₁ z nb T uM (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q) x (u, v) ∂(lam.restrict 𝓖) ∂(ν.restrict 𝓤) := fun q => rfl
  simp_rw [htm]
  refine ⟨h1, ?_⟩
  rw [← h2]
  refine integral_congr_ae (ae_of_all _ fun u => integral_congr_ae (ae_of_all _ fun β => ?_))
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.eis, GlobalTheory.Eis.cosetSum, GlobalTheory.Eis.term, _root_.PositivityTheory.SiegelWeilFormula.Act.kq_k, _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k, _root_.PositivityTheory.SiegelWeilFormula.Act.rep_k]
  rw [tsum_mul_right]
  rfl
theorem ctSplit_of_parts_k : _root_.PositivityTheory.SiegelWeilFormula.Act.IndepDom_k → _root_.PositivityTheory.SiegelWeilFormula.Act.CptDom_k → _root_.PositivityTheory.SiegelWeilFormula.Act.AbsConv_k → _root_.PositivityTheory.SiegelWeilFormula.Act.FirstEq_k → _root_.PositivityTheory.SiegelWeilFormula.Act.SecLaw_k → _root_.PositivityTheory.SiegelWeilFormula.CTSplit_k := by
  intro hI hC hA hF hS F E _ _ _ _ _ σ d R L s₁ f hf he
  obtain ⟨tA, hA'⟩ := hA F E σ d L s₁ f hf he
  obtain ⟨tF, hF'⟩ := hF F E σ d L s₁ f hf he
  obtain ⟨tS, hS'⟩ := hS F E σ d R L s₁ f hf he
  refine ⟨max tA (max tF tS), fun z hz nb lam 𝓖 hc nb' lam' 𝓖' hc' uM ν 𝓤 hU T T' hTT' => ?_⟩
  have hzA : tA < z.re := lt_of_le_of_lt (le_max_left _ _) hz
  have hzF : tF < z.re := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hz
  have hzS : tS < z.re := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hz
  obtain ⟨𝓖₀, hc₀, hk₀⟩ := (hC F E σ d).1 nb lam 𝓖 hc
  obtain ⟨𝓤₀, hU₀, hkU⟩ := (hC F E σ d).2 L uM ν 𝓤 hU
  obtain ⟨𝓖'₀, hc'₀, hk'₀⟩ := (hC F E σ L.sd).1 nb' lam' 𝓖' hc'
  refine ⟨_root_.PositivityTheory.SiegelWeilFormula.Act.secondOrbitSection L f s₁ z nb lam 𝓖₀ T uM ν 𝓤₀, fun x => ?_, fun w τ y x hy =>
    hS' z hzS nb lam 𝓖₀ hc₀ hk₀ uM ν 𝓤₀ hU₀ hkU T T' hTT' nb' lam' 𝓖'₀ hc'₀ hk'₀ w τ y x hy⟩
  have e1 := (hI F E σ d L s₁ f hf z).1 nb lam 𝓖 𝓖₀ hc hc₀ uM ν 𝓤 𝓤₀ hU hU₀ T T' hTT' x
  have e2 := (hI F E σ d L s₁ f hf z).2 nb' lam' 𝓖' 𝓖'₀ hc' hc'₀ T' x
  have e3 := hF' z hzF nb lam 𝓖₀ hc₀ hk₀ nb' lam' 𝓖'₀ hc'₀ hk'₀ uM ν 𝓤₀ hU₀ hkU T T' hTT' x
  obtain ⟨hi, hs⟩ := hA' z hzA nb lam 𝓖₀ hc₀ hk₀ uM ν 𝓤₀ hU₀ hkU T x
  obtain ⟨hsum, e4⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.lhs_eq_tsum_k L f s₁ z nb lam 𝓖₀ T uM ν 𝓤₀ hU₀.2.2.2 hc₀.2.2.2 x hi hs
  change _ = _root_.PositivityTheory.SiegelWeilFormula.Act.first_k L f s₁ z nb' lam' 𝓖' T' x + _
  rw [e1, e2, ← e3, e4, ← hsum.tsum_subtype_add_tsum_subtype_compl {q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d | _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q)}]
  rfl
end PositivityTheory.SiegelWeilFormula.Act
end
end
end
