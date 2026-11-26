module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.ProdGenMem
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.FourierZero
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.ContinuousLoc
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKunfSec
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SingularHermitian.MatrixEqFrameConjugate
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.WhitAtCOneIff
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.VacuumIwasawa.VacCut

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfockMem
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFock
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem prodGen_mem_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (S : InfinitePlace F → 𝓢(Fin d.m → Fin d.n → ℂ, ℂ))
    (g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ) (hg : g ∈ SB (Fin d.m × Fin d.n × Fin 2 → Af F)) :
    (fun X => (∏ w, S w (R.loc w X)) * g fun k => (d.crd X k).2) ∈ d.schM := by
  obtain ⟨T, hT⟩ := piProdSch (InfinitePlace F) (Fin d.m → Fin d.n → ℂ) S
  obtain ⟨L, hL⟩ := _root_.PositivityTheory.SiegelWeilFormula.KFock.archEquiv_k d R
  rw [_root_.PositivityTheory.SiegelWeilFormula.SD_k.schM, Submodule.mem_comap]
  refine Submodule.subset_span ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L T, g, hg, ?_⟩
  funext c
  simp only [LinearMap.funLeft_apply, pureA, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp, hT, hL,
    _root_.PositivityTheory.SiegelWeilFormula.KFock.crd_cmb_k]
theorem fock_le_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : R.fock ≤ d.schM := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨P, g, hg, rfl⟩
  have h := _root_.PositivityTheory.SiegelWeilFormula.KFock.prodGen_mem_k d R (fun w => (isSw_fP (P w)).choose) g hg
  have e : (fun X => (∏ w, fP (P w) (R.loc w X)) * g fun k => (d.crd X k).2) =
      fun X => (∏ w, (isSw_fP (P w)).choose (R.loc w X)) * g fun k => (d.crd X k).2 := by
    funext X
    congr 1
    exact Finset.prod_congr rfl fun w _ => by rw [(isSw_fP (P w)).choose_spec]
  change _ ∈ d.schM
  rw [e]
  exact h
theorem tens_mem_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (f : (Fin d.m → Fin d.n → ℂ) → ℂ) (hf : IsSw f)
    (Ψ : Mx F E d.m d.n → ℂ) (hΨ : Ψ ∈ R.away w) : R.tens w f Ψ ∈ d.schM := by
  obtain ⟨φ, hφ⟩ := hf
  have h : R.away w ≤ d.schM.comap (_root_.PositivityTheory.SiegelWeilFormula.KFock.tensL_k R w f) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨P, g, hg, rfl⟩
    have h := _root_.PositivityTheory.SiegelWeilFormula.KFock.prodGen_mem_k d R (Function.update (fun w' => (isSw_fP (P w')).choose) w φ) g hg
    show R.tens w f _ ∈ d.schM
    convert h using 1
    funext X
    show f (R.loc w X) * ((∏ w' ∈ Finset.univ.erase w, fP (P w') (R.loc w' X)) * g fun k => (d.crd X k).2) =
      (∏ w', (Function.update (fun w' => (isSw_fP (P w')).choose) w φ w') (R.loc w' X)) * g fun k => (d.crd X k).2
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w), Function.update_self, hφ, mul_assoc]
    congr 2
    refine Finset.prod_congr rfl fun w' hw' => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hw'), (isSw_fP (P w')).choose_spec]
  exact h hΨ
end PositivityTheory.SiegelWeilFormula.KFock
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAstepDefs
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.AStep
structure Hyps_k : Prop where
  holLead : HolLead
  holT : HolT
  tAll : _root_.PositivityTheory.SiegelWeilFormula.TAll_k
  thetaCoef : _root_.PositivityTheory.SiegelWeilFormula.ThetaCoef_k
  auxEx : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties
  coefEx : _root_.PositivityTheory.SiegelWeilFormula.CoefEx_k
  fockMem : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k
  liftEx : _root_.PositivityTheory.SiegelWeilFormula.LiftEx_k
  locOpEx : _root_.PositivityTheory.SiegelWeilFormula.LocOpEx_k
  locInst : _root_.PositivityTheory.SiegelWeilFormula.LocInst_k
  gSplit : _root_.PositivityTheory.SiegelWeilFormula.GSplit_k
  polyKFin : _root_.PositivityTheory.SiegelWeilFormula.PolyKFin_k
  secK : _root_.PositivityTheory.SiegelWeilFormula.SecK_k
  eisWk : _root_.PositivityTheory.SiegelWeilFormula.EisWk_k
  lamBd : _root_.PositivityTheory.SiegelWeilFormula.LamBd_k
  lamSing : _root_.PositivityTheory.SiegelWeilFormula.LamSing_k
  fourierZero : _root_.PositivityTheory.SiegelWeilFormula.FourierZero_k
  unfold : _root_.PositivityTheory.SiegelWeilFormula.Unfold_k
  whitLow : _root_.PositivityTheory.SiegelWeilFormula.WhitLow_k
  vacK : _root_.PositivityTheory.SiegelWeilFormula.VacK_k
  iwaQ : _root_.PositivityTheory.SiegelWeilFormula.IwaQ_k
  cTSplit : _root_.PositivityTheory.SiegelWeilFormula.CTSplit_k
  uEx : _root_.PositivityTheory.SiegelWeilFormula.UEx_k
  fcConj : _root_.PositivityTheory.SiegelWeilFormula.FcConj_k
  orbRes : _root_.PositivityTheory.SiegelWeilFormula.OrbRes_k
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
def EData_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (f : d.G → ℂ) (s₁ s₀ : ℂ) (U : Set ℂ) (p : Polynomial ℂ) (Ê : ℂ → d.G → ℂ) (t : ℝ) : Prop :=
  IsOpen U ∧ IsRightDomain U ∧ s₀ ∈ U ∧ p ≠ 0 ∧
    (∀ g, DifferentiableOn ℂ (Ê · g) U) ∧ ContinuousOn (fun y : ℂ × d.G => Ê y.1 y.2) (U ×ˢ Set.univ) ∧
    (∀ z ∈ U, ∀ γ ∈ rat2 σ d.Y, ∀ g, Ê z (γ * g) = Ê z g) ∧
    ∀ z : ℂ, t < z.re → (∀ C : Set d.G, IsCompact C → ∃ u : GlobalTheory.Eis.Cosets (par2 σ d.Y) (rat2 σ d.Y) → ℝ, Summable u ∧
        ∀ g ∈ C, ∀ q, ‖GlobalTheory.Eis.term (par2 σ d.Y) (rat2 σ d.Y) (fun x => ((d.Ht x : ℝ) : ℂ) ^ (z - s₁) * f x) g q‖ ≤ u q) ∧
      ∀ g, Ê z g = p.eval z * d.eis f s₁ z g
def avg_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (uM : (Fin L.n → AE F E) → d.G) (ν : Measure (Fin L.n → AE F E)) (𝓤 : Set (Fin L.n → AE F E))
    (nb : nA σ d.Y d.b → d.G) (lam : Measure (nA σ d.Y d.b)) (𝓖 : Set (nA σ d.Y d.b)) (φ : d.G → ℂ) (T : nF σ d.Y d.b)
    (x : d.G) : ℂ :=
  ∫ u in 𝓤, fc d.B.ψ d.b nb lam 𝓖 φ T (uM u * x) ∂ν
def cOne_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (f : d.G → ℂ) (s₁ z : ℂ) (nb' : nA σ L.Y L.b → L.sd.G) (lam' : Measure (nA σ L.Y L.b))
    (𝓖' : Set (nA σ L.Y L.b)) (T' : nF σ L.Y L.b) (x : d.G) : ℂ :=
  fc d.B.ψ L.b nb' lam' 𝓖' (GlobalTheory.Eis.cosetSum (par2 σ L.Y) (rat2 σ L.Y) fun g =>
    ((d.Ht (L.j g * x) : ℝ) : ℂ) ^ (z - s₁) * f (L.j g * x)) T' 1
end PositivityTheory.SiegelWeilFormula.AStep
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfockFact
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFock
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
def cmpW_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (w : InfinitePlace F) : AddSubgroup (Mx F E d.m d.n) where
  carrier := {X | d.cw w X = 0}
  zero_mem' := by
    show d.cw w 0 = 0
    exact Matrix.map_zero _ (map_zero _)
  add_mem' := by
    intro X Z hX hZ
    show d.cw w (X + Z) = 0
    have e : d.cw w (X + Z) = d.cw w X + d.cw w Z := Matrix.map_add _ (map_add _) X Z
    rw [e, show d.cw w X = 0 from hX, show d.cw w Z = 0 from hZ, add_zero]
  neg_mem' := by
    intro X hX
    show d.cw w (-X) = 0
    have e : d.cw w (-X) = -d.cw w X := Matrix.map_neg _ (map_neg _) X
    rw [e, show d.cw w X = 0 from hX, neg_zero]
def IntFact_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
  (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (ν : Measure (Mx F E d.m d.n)), d.IsCov ν →
  ∃ (C : ℝ) (μ' : Measure (_root_.PositivityTheory.SiegelWeilFormula.KFock.cmpW_k d w)), 0 < C ∧ μ'.IsAddHaarMeasure ∧
    ∀ (f : (Fin d.m → Fin d.n → ℂ) → ℂ) (Ψ : Mx F E d.m d.n → ℂ),
      (∀ X Z, (∀ w', w' ≠ w → d.cw w' Z = 0) → finOne F • Z = 0 → Ψ (X + Z) = Ψ X) →
      ∫ X, R.tens w f Ψ X ∂ν = C * (∫ u, f u) * ∫ Z, Ψ Z.1 ∂μ'
section Split
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F)
theorem cw_add'_k (X Z : Mx F E d.m d.n) : d.cw w (X + Z) = d.cw w X + d.cw w Z := Matrix.map_add _ (map_add _) X Z
theorem cw_sub'_k (X Z : Mx F E d.m d.n) : d.cw w (X - Z) = d.cw w X - d.cw w Z := Matrix.map_sub _ (map_sub _) X Z
theorem loc_add'_k (X Z : Mx F E d.m d.n) : R.loc w (X + Z) = R.loc w X + R.loc w Z := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.RD_k.loc
  rw [_root_.PositivityTheory.SiegelWeilFormula.KFock.cw_add'_k, Matrix.mul_add]
  exact Matrix.map_add _ (fun a b => star_add a b) _ _
theorem loc_of_mem_k {b : Mx F E d.m d.n} (hb : b ∈ _root_.PositivityTheory.SiegelWeilFormula.KFock.cmpW_k d w) : R.loc w b = 0 := by
  have h : d.cw w b = 0 := hb
  unfold _root_.PositivityTheory.SiegelWeilFormula.RD_k.loc
  rw [h, Matrix.mul_zero]
  exact Matrix.map_zero _ (star_zero _)
theorem continuous_loc_k : Continuous (R.loc w) := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.RD_k.loc
  exact (continuous_const.matrix_mul (_root_.PositivityTheory.SiegelWeilFormula.Place.continuous_cw_k d w)).matrix_map continuous_star
end Split
theorem intFact_k : _root_.PositivityTheory.SiegelWeilFormula.KFock.IntFact_k := by
  intro F E _ _ _ _ _ σ d R w ν hν
  haveI := hν.1
  obtain ⟨i1, i2, i3, i4⟩ := (PositivityTheory.ThKCT.ideleTop F E).1
  haveI : BorelSpace (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalAddGroup (Mx F E d.m d.n) := inferInstanceAs (IsTopologicalAddGroup (Fin d.m → Fin d.n → AE F E))
  haveI : LocallyCompactSpace (Mx F E d.m d.n) := inferInstanceAs (LocallyCompactSpace (Fin d.m → Fin d.n → AE F E))
  haveI : SecondCountableTopology (Mx F E d.m d.n) :=
    inferInstanceAs (SecondCountableTopology (Fin d.m → Fin d.n → AE F E))
  haveI : BorelSpace (Mx F E d.m d.n) := inferInstanceAs (BorelSpace (Fin d.m → Fin d.n → AE F E))
  have hcl : IsClosed ((_root_.PositivityTheory.SiegelWeilFormula.KFock.cmpW_k d w : AddSubgroup (Mx F E d.m d.n)) : Set (Mx F E d.m d.n)) :=
    isClosed_eq (_root_.PositivityTheory.SiegelWeilFormula.Place.continuous_cw_k d w) continuous_const
  haveI : LocallyCompactSpace (_root_.PositivityTheory.SiegelWeilFormula.KFock.cmpW_k d w) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (_root_.PositivityTheory.SiegelWeilFormula.KFock.cmpW_k d w) :=
    TopologicalSpace.Subtype.secondCountableTopology ((_root_.PositivityTheory.SiegelWeilFormula.KFock.cmpW_k d w : AddSubgroup (Mx F E d.m d.n)) : Set (Mx F E d.m d.n))
  haveI : BorelSpace (_root_.PositivityTheory.SiegelWeilFormula.KFock.cmpW_k d w) := Subtype.borelSpace (fun x' => x' ∈ ((_root_.PositivityTheory.SiegelWeilFormula.KFock.cmpW_k d w : AddSubgroup (Mx F E d.m d.n)) : Set (Mx F E d.m d.n)))
  haveI := volume_isAddHaar d.m d.n
  obtain ⟨s, hsc, hs1, hs2, hsa, -⟩ := Place.exists_sec d.cm d.B.emb
  set fr : Matrix (Fin d.m) (Fin d.m) ℂ := (R.fr w).1 with hfr
  let U : (Fin d.m → Fin d.n → ℂ) → Matrix (Fin d.m) (Fin d.n) ℂ := fun u => fr * Matrix.of fun b j => star (u b j)
  let sW : (Fin d.m → Fin d.n → ℂ) → Mx F E d.m d.n := fun u i j => s fun w' => if w' = w then U u i j else 0
  have cw_sW : ∀ u, d.cw w (sW u) = U u := fun u => by
    ext i j
    show piInf (d.B.emb w) (s _) = U u i j
    rw [hs1, if_pos rfl]
  have cw_sW' : ∀ u w', w' ≠ w → d.cw w' (sW u) = 0 := fun u w' h => by
    ext i j
    show piInf (d.B.emb w') (s _) = 0
    rw [hs1, if_neg h]
  have fin_sW : ∀ u, finOne F • sW u = 0 := fun u => by
    ext i j
    show finOne F • s _ = 0
    exact hs2 _
  have inv_fr : ((R.fr w)⁻¹).1 * fr = 1 := Units.inv_mul (R.fr w)
  have fr_inv : fr * ((R.fr w)⁻¹).1 = 1 := Units.mul_inv (R.fr w)
  have loc_sW : ∀ u, R.loc w (sW u) = u := fun u => by
    unfold _root_.PositivityTheory.SiegelWeilFormula.RD_k.loc
    rw [cw_sW, ← Matrix.mul_assoc, inv_fr, Matrix.one_mul]
    ext a j
    simp
  have U_loc : ∀ X, U (R.loc w X) = d.cw w X := fun X => by
    simp only [U, _root_.PositivityTheory.SiegelWeilFormula.RD_k.loc]
    have : (Matrix.of fun b j => star ((((R.fr w)⁻¹).1 * d.cw w X).map star b j)) = ((R.fr w)⁻¹).1 * d.cw w X := by
      ext b j; simp
    rw [this, ← Matrix.mul_assoc, fr_inv, Matrix.one_mul]
  have U_add : ∀ u v, U (u + v) = U u + U v := fun u v => by
    simp only [U]
    rw [← Matrix.mul_add]
    congr 1
    ext b j
    simp [star_add]
  have sW_add : ∀ u v, sW (u + v) = sW u + sW v := fun u v => by
    ext i j
    show s _ = s _ + s _
    rw [← hsa]
    congr 1
    funext w'
    show _ = (if w' = w then U u i j else 0) + (if w' = w then U v i j else 0)
    by_cases h : w' = w
    · rw [if_pos h, if_pos h, if_pos h, U_add]; rfl
    · rw [if_neg h, if_neg h, if_neg h, add_zero]
  have hU : Continuous U := by
    simp only [U]
    exact continuous_const.matrix_mul (continuous_pi fun b => continuous_pi fun j =>
      continuous_star.comp ((continuous_apply j).comp (continuous_apply b)))
  have hsW : Continuous sW := by
    refine continuous_pi fun i => continuous_pi fun j => hsc.comp (continuous_pi fun w' => ?_)
    split_ifs
    · exact (continuous_apply j).comp ((continuous_apply i).comp hU)
    · exact continuous_const
  have mem : ∀ X, X - sW (R.loc w X) ∈ _root_.PositivityTheory.SiegelWeilFormula.KFock.cmpW_k d w := fun X => by
    show d.cw w (X - sW (R.loc w X)) = 0
    rw [_root_.PositivityTheory.SiegelWeilFormula.KFock.cw_sub'_k, cw_sW, U_loc, sub_self]
  let Φ : (Fin d.m → Fin d.n → ℂ) × _root_.PositivityTheory.SiegelWeilFormula.KFock.cmpW_k d w ≃ₜ+ Mx F E d.m d.n :=
    { toFun := fun p => sW p.1 + p.2.1
      invFun := fun X => (R.loc w X, ⟨X - sW (R.loc w X), mem X⟩)
      left_inv := fun p => by
        obtain ⟨u, b, hb⟩ := p
        have e1 : R.loc w (sW u + b) = u := by rw [_root_.PositivityTheory.SiegelWeilFormula.KFock.loc_add'_k, loc_sW, _root_.PositivityTheory.SiegelWeilFormula.KFock.loc_of_mem_k d R w hb, add_zero]
        refine Prod.ext e1 (Subtype.ext ?_)
        show sW u + b - sW (R.loc w (sW u + b)) = b
        rw [e1, add_sub_cancel_left]
      right_inv := fun X => by
        show sW (R.loc w X) + (X - sW (R.loc w X)) = X
        rw [add_sub_cancel]
      map_add' := fun p q => by
        show sW (p.1 + q.1) + (p.2.1 + q.2.1) = sW p.1 + p.2.1 + (sW q.1 + q.2.1)
        rw [sW_add]; abel
      continuous_toFun := (hsW.comp continuous_fst).add (continuous_subtype_val.comp continuous_snd)
      continuous_invFun := (_root_.PositivityTheory.SiegelWeilFormula.KFock.continuous_loc_k d R w).prodMk
        ((continuous_id.sub (hsW.comp (_root_.PositivityTheory.SiegelWeilFormula.KFock.continuous_loc_k d R w))).subtype_mk _) }
  obtain ⟨C, hC, hg⟩ := integral_split ν (volume : Measure (Fin d.m → Fin d.n → ℂ)) (Measure.addHaar : Measure (_root_.PositivityTheory.SiegelWeilFormula.KFock.cmpW_k d w)) Φ
  refine ⟨C, Measure.addHaar, hC, inferInstance, fun f Ψ hΨ => ?_⟩
  rw [hg]
  have e : ∀ p : (Fin d.m → Fin d.n → ℂ) × _root_.PositivityTheory.SiegelWeilFormula.KFock.cmpW_k d w, R.tens w f Ψ (Φ p) = f p.1 * Ψ p.2.1 := fun p => by
    obtain ⟨u, b, hb⟩ := p
    show f (R.loc w (sW u + b)) * Ψ (sW u + b) = f u * Ψ b
    rw [_root_.PositivityTheory.SiegelWeilFormula.KFock.loc_add'_k, loc_sW, _root_.PositivityTheory.SiegelWeilFormula.KFock.loc_of_mem_k d R w hb, add_zero, add_comm, hΨ b (sW u) (cw_sW' u) (fin_sW u)]
  simp_rw [e]
  have hp := integral_prod_mul (μ := (volume : Measure (Fin d.m → Fin d.n → ℂ))) (ν := (Measure.addHaar : Measure (_root_.PositivityTheory.SiegelWeilFormula.KFock.cmpW_k d w)))
    f (fun Z : _root_.PositivityTheory.SiegelWeilFormula.KFock.cmpW_k d w => Ψ Z.1)
  rw [hp, mul_assoc]
end PositivityTheory.SiegelWeilFormula.KFock
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfpDefs
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFP
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
abbrev Yf_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : Type := Fin d.m × Fin d.n × Fin 2 → Af F
abbrev Iw_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : Type := InfinitePlace F × Fin d.m × Fin d.n × Bool
abbrev Vw_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : Type := EuclideanSpace ℝ (_root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d)
def fin_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (X : Mx F E d.m d.n) : _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d := fun k => (d.crd X k).2
def arc_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (X : Mx F E d.m d.n) : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d :=
  (EuclideanSpace.equiv (_root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d) ℝ).symm fun i => if i.2.2.2 then (R.loc i.1 X i.2.1 i.2.2.1).re else (R.loc i.1 X i.2.1 i.2.2.1).im
def gau_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (X : Mx F E d.m d.n) : ℂ := ∏ w, fP (1 : PX d.m d.n) (R.loc w X)
def vac_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (g : _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d → ℂ) (X : Mx F E d.m d.n) : ℂ := _root_.PositivityTheory.SiegelWeilFormula.KFP.gau_k R X * g (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X)
theorem vac_mem_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {g : _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d → ℂ} (hg : g ∈ SB (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d)) : _root_.PositivityTheory.SiegelWeilFormula.KFP.vac_k R g ∈ R.fock :=
  Submodule.subset_span ⟨fun _ => 1, g, hg, rfl⟩
theorem exists_lift_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hF : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {g : _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d → ℂ} (hg : g ∈ SB (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d)) :
    ∃ Ω ∈ d.sch, d.T Ω = _root_.PositivityTheory.SiegelWeilFormula.KFP.vac_k R g :=
  (hT.1 F E σ d).2.1 _ ((hF F E σ d R).1 (_root_.PositivityTheory.SiegelWeilFormula.KFP.vac_mem_k R hg))
def zOf_k (u : _root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d → ℝ) : InfinitePlace F → Fin d.m → Fin d.n → ℂ :=
  fun w a j => ⟨u (w, a, j, true), u (w, a, j, false)⟩
theorem arc_eq_iff_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (X : Mx F E d.m d.n) (u : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d) :
    _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X = u ↔ ∀ w, R.loc w X = _root_.PositivityTheory.SiegelWeilFormula.KFP.zOf_k (EuclideanSpace.equiv (_root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d) ℝ u) w := by
  constructor
  · rintro rfl w
    funext a j
    apply Complex.ext
    · simp [_root_.PositivityTheory.SiegelWeilFormula.KFP.zOf_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k]
    · simp [_root_.PositivityTheory.SiegelWeilFormula.KFP.zOf_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k]
  · intro h
    apply (EuclideanSpace.equiv (_root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d) ℝ).injective
    funext i
    obtain ⟨w, a, j, b⟩ := i
    have hw := congrFun (congrFun (h w) a) j
    cases b
    · simp only [_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k, ContinuousLinearEquiv.apply_symm_apply, Bool.false_eq_true, ite_false]
      rw [hw]
      rfl
    · simp only [_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k, ContinuousLinearEquiv.apply_symm_apply, ite_true]
      rw [hw]
      rfl
theorem exists_jn_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (u : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d) (y : _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d) : ∃! X : Mx F E d.m d.n, _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X = u ∧ _root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X = y := by
  have crd_cmb (c : Fin d.m × Fin d.n × Fin 2 → AF F) : d.crd (d.cmb c) = c := by
    funext k
    obtain ⟨i, j, l⟩ := k
    simp only [SD_k.crd, SD_k.cmb]
    simpa only [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      using congrFun ((Algebra.TensorProduct.basis (AF F) d.bs).repr_sum_self fun k => c (i, j, k)) l
  have cmb_crd (X : Mx F E d.m d.n) : d.cmb (d.crd X) = X := by
    ext i j
    simp only [SD_k.crd, SD_k.cmb]
    simpa only [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      using (Algebra.TensorProduct.basis (AF F) d.bs).sum_repr (X i j)
  have archEquiv :
      ∃ L : (Fin d.m × Fin d.n × Fin 2 → mixedEmbedding.mixedSpace F) ≃L[ℝ] (InfinitePlace F → Fin d.m → Fin d.n → ℂ),
        ∀ (c : Fin d.m × Fin d.n × Fin 2 → AF F) (w : InfinitePlace F),
          L (fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F (c k).1) w = R.loc w (d.cmb c) := by
    have hcm : IsCMExt F E σ := d.ok.good.cm
    have : IsTotallyReal F := hcm.1
    have : IsTotallyComplex E := hcm.2.1
    have hr : ∀ w : InfinitePlace F, w.IsReal := fun w => IsTotallyReal.isReal w
    have detIm_ne (w : InfinitePlace F) :
        ((d.B.emb w).1 (d.bs 0)).im * ((d.B.emb w).1 (d.bs 1)).re -
        ((d.B.emb w).1 (d.bs 0)).re * ((d.B.emb w).1 (d.bs 1)).im ≠ 0 := by
      let τ : E →+* ℂ := (d.B.emb w).1
      have hreal : ∀ f : F, (τ (algebraMap F E f)).im = 0 := by
        intro f
        have e1 : τ (algebraMap F E f) = w.embedding f := RingHom.congr_fun (d.B.emb w).2 f
        have e3 : ComplexEmbedding.conjugate w.embedding = w.embedding :=
          ComplexEmbedding.isReal_iff.mp (InfinitePlace.isReal_iff.mp (hr w))
        have e4 := RingHom.congr_fun e3 f
        rw [ComplexEmbedding.conjugate_coe_eq] at e4
        rw [e1]
        exact Complex.conj_eq_iff_im.mp e4
      have hexp : ∀ e : E, τ e = τ (algebraMap F E (d.bs.repr e 0)) * τ (d.bs 0) +
          τ (algebraMap F E (d.bs.repr e 1)) * τ (d.bs 1) := by
        intro e
        conv_lhs => rw [← d.bs.sum_repr e]
        simp [Fin.sum_univ_two, Algebra.smul_def, map_add (f := _), map_mul]
      obtain ⟨e, he⟩ : ∃ e : E, (τ e).im ≠ 0 := by
        by_contra hne
        push Not at hne
        have hc : (InfinitePlace.mk τ).IsComplex := IsTotallyComplex.isComplex _
        rw [InfinitePlace.isComplex_mk_iff] at hc
        apply hc
        rw [ComplexEmbedding.isReal_iff]
        refine RingHom.ext fun x => ?_
        rw [ComplexEmbedding.conjugate_coe_eq]
        exact Complex.conj_eq_iff_im.mpr (hne x)
      intro hD
      apply he
      have h1 := hexp 1
      have h2 := hexp e
      set p := τ (algebraMap F E (d.bs.repr 1 0))
      set q := τ (algebraMap F E (d.bs.repr 1 1))
      set p' := τ (algebraMap F E (d.bs.repr e 0))
      set q' := τ (algebraMap F E (d.bs.repr e 1))
      have ip : p.im = 0 := hreal _
      have iq : q.im = 0 := hreal _
      have ip' : p'.im = 0 := hreal _
      have iq' : q'.im = 0 := hreal _
      rw [map_one] at h1
      have h1re := congrArg Complex.re h1
      have h1im := congrArg Complex.im h1
      have h2im := congrArg Complex.im h2
      simp only [Complex.one_re, Complex.one_im, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, ip, iq,
        ip', iq', zero_mul, sub_zero, add_zero] at h1re h1im h2im
      linear_combination -(p'.re * (τ (d.bs 0)).re + q'.re * (τ (d.bs 1)).re) * h1im - (p.re * q'.re - q.re * p'.re) * hD +
        (p'.re * (τ (d.bs 0)).im + q'.re * (τ (d.bs 1)).im) * h1re + h2im
    let coordinateMap :
        (Fin d.m × Fin d.n × Fin 2 → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (InfinitePlace F → Fin d.m → Fin d.n → ℂ) :=
        { toFun r w a j := star (∑ i, ((R.fr w)⁻¹).1 a i *
            ∑ l : Fin 2, (((r (i, j, l)).1 ⟨w, hr w⟩ : ℝ) : ℂ) * (d.B.emb w).1 (d.bs l))
          map_add' r s := by
            funext w a j
            simp only [Pi.add_apply, Prod.fst_add, Complex.ofReal_add, add_mul, Finset.sum_add_distrib, mul_add, star_add]
          map_smul' c r := by
            funext w a j
            simp only [Pi.smul_apply, RingHom.id_apply, Complex.real_smul, Prod.smul_fst, smul_eq_mul, Complex.ofReal_mul]
            conv_rhs => rw [show (c : ℂ) = star (c : ℂ) from (Complex.conj_ofReal c).symm, ← star_mul']
            congr 1
            simp only [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring }
    have hinj : Function.Injective coordinateMap := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro r hr0
      have hz : ∀ w i j, ∑ l : Fin 2, (((r (i, j, l)).1 ⟨w, hr w⟩ : ℝ) : ℂ) * (d.B.emb w).1 (d.bs l) = 0 := by
        intro w
        let Z : Matrix (Fin d.m) (Fin d.n) ℂ := fun i j => ∑ l : Fin 2, (((r (i, j, l)).1 ⟨w, hr w⟩ : ℝ) : ℂ) * (d.B.emb w).1 (d.bs l)
        have h1 : ((R.fr w)⁻¹).1 * Z = 0 := by
          ext a j
          have h := congrFun (congrFun (congrFun hr0 w) a) j
          have h' : star (∑ i, ((R.fr w)⁻¹).1 a i * Z i j) = 0 := h
          rw [star_eq_zero] at h'
          rw [Matrix.mul_apply]
          exact h'
        have h2 : Z = 0 := by
          have e : Z = (R.fr w).1 * (((R.fr w)⁻¹).1 * Z) := by
            rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
          rw [e, h1, Matrix.mul_zero]
        intro i j
        exact congrFun (congrFun h2 i) j
      funext k
      obtain ⟨i, j, l⟩ := k
      refine Prod.ext (funext fun v => ?_) (funext fun v => ?_)
      · have h := hz v.1 i j
        rw [Fin.sum_univ_two] at h
        have hi := _root_.PositivityTheory.SiegelWeilFormula.KFock.real_indep (detIm_ne v.1) h
        have ev : (⟨v.1, hr v.1⟩ : {w : InfinitePlace F // w.IsReal}) = v := Subtype.ext rfl
        rw [ev] at hi
        fin_cases l
        · exact hi.1
        · exact hi.2
      · exact absurd v.2 (InfinitePlace.not_isComplex_iff_isReal.mpr (hr v.1))
    have hdim : Module.finrank ℝ (Fin d.m × Fin d.n × Fin 2 → mixedEmbedding.mixedSpace F) =
        Module.finrank ℝ (InfinitePlace F → Fin d.m → Fin d.n → ℂ) := by
      simp only [Module.finrank_pi_fintype, mixedEmbedding.finrank, Complex.finrank_real_complex, Finset.sum_const,
        Finset.card_univ, smul_eq_mul, Fintype.card_prod, Fintype.card_fin]
      rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, ← InfinitePlace.card_add_two_mul_card_eq_rank,
        IsTotallyReal.nrComplexPlaces_eq_zero]
      ring
    have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
    refine ⟨(LinearEquiv.ofBijective coordinateMap ⟨hinj, hsurj⟩).toContinuousLinearEquiv, fun c w => ?_⟩
    funext a j
    show star (∑ i, ((R.fr w)⁻¹).1 a i * ∑ l : Fin 2,
        ((((InfiniteAdeleRing.ringEquiv_mixedSpace F (c (i, j, l)).1).1 ⟨w, hr w⟩ : ℝ) : ℂ) * (d.B.emb w).1 (d.bs l))) =
      star ((((R.fr w)⁻¹).1 * d.cw w (d.cmb c)) a j)
    rw [Matrix.mul_apply]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    show _ = piInf (d.B.emb w) (∑ l, c (i, j, l) ⊗ₜ[F] d.bs l)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [InfiniteAdeleRing.ringEquiv_mixedSpace_apply, InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply]
    rfl
  obtain ⟨L, hL⟩ := archEquiv
  set Z := _root_.PositivityTheory.SiegelWeilFormula.KFP.zOf_k (EuclideanSpace.equiv (_root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d) ℝ u) with hZ
  let cI := L.symm Z
  let c : Fin d.m × Fin d.n × Fin 2 → AF F := fun k =>
    (Prod.mk ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (cI k)) (y k) : AF F)
  have hc1 : (fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F (c k).1) = cI := by
    funext k
    exact RingEquiv.apply_symm_apply _ _
  refine ⟨d.cmb c, ⟨?_, ?_⟩, ?_⟩
  · rw [_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_eq_iff_k]
    intro w
    rw [← hL c w, hc1]
    show L (L.symm Z) w = Z w
    rw [ContinuousLinearEquiv.apply_symm_apply]
  · funext k
    show (d.crd (d.cmb c) k).2 = y k
    rw [crd_cmb]
  · rintro X ⟨hX1, hX2⟩
    rw [_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_eq_iff_k] at hX1
    have e1 : L (fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F (d.crd X k).1) = Z := by
      funext w
      rw [hL, cmb_crd]
      exact hX1 w
    have e2 : (fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F (d.crd X k).1) = cI := by
      have h := congrArg L.symm e1
      rwa [ContinuousLinearEquiv.symm_apply_apply] at h
    have e3 : d.crd X = c := by
      funext k
      refine Prod.ext ?_ ?_
      · apply (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective
        rw [congrFun e2 k]
        exact (congrFun hc1 k).symm
      · exact congrFun hX2 k
    rw [← e3, cmb_crd]
def jn_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (u : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d) (y : _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d) : Mx F E d.m d.n := (_root_.PositivityTheory.SiegelWeilFormula.KFP.exists_jn_k R u y).exists.choose
theorem arc_jn_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (u : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d) (y : _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d) : _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R (_root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R u y) = u := (_root_.PositivityTheory.SiegelWeilFormula.KFP.exists_jn_k R u y).exists.choose_spec.1
theorem fin_jn_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (u : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d) (y : _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d) : _root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d (_root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R u y) = y := (_root_.PositivityTheory.SiegelWeilFormula.KFP.exists_jn_k R u y).exists.choose_spec.2
theorem jn_arc_fin_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (X : Mx F E d.m d.n) : _root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R (_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X) (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X) = X :=
  ((_root_.PositivityTheory.SiegelWeilFormula.KFP.exists_jn_k R (_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X) (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X)).unique (_root_.PositivityTheory.SiegelWeilFormula.KFP.exists_jn_k R (_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X) (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X)).exists.choose_spec ⟨rfl, rfl⟩)
def hg_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (νf : Measure (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d)) (f : Mx F E d.m d.n → ℂ) (g : _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d → ℂ) (u : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d) : ℂ :=
  ∫ y, f (_root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R u y) * star (g y) ∂νf
def B_k (ν : Measure (Mx F E d.m d.n)) (Φ Ψ : d.Fn) : ℂ := ∫ X, d.T Φ X * star (d.T Ψ X) ∂ν
end PositivityTheory.SiegelWeilFormula.KFP
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKsingGrp
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KSing
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace UnitaryGroupBasics
theorem incM_b_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : incM F d.b.1 * incM F (d.b⁻¹).1 = 1 := by
  rw [← incM_mul, Units.mul_inv, incM_one]
theorem incM_b'_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : incM F (d.b⁻¹).1 * incM F d.b.1 = 1 := by
  rw [← incM_mul, Units.inv_mul, incM_one]
theorem inFrame_mul_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (x y : d.G) : inFrame d.b (x * y) = inFrame d.b x * inFrame d.b y := by
  unfold inFrame
  have e : mat2 (x * y) = mat2 x * mat2 y := rfl
  rw [e]
  calc incM F (d.b⁻¹).1 * (mat2 x * mat2 y) * incM F d.b.1
      = incM F (d.b⁻¹).1 * mat2 x * (incM F d.b.1 * incM F (d.b⁻¹).1) * mat2 y * incM F d.b.1 := by
        rw [_root_.PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.incM_b_k, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]
theorem inFrame_one_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : inFrame d.b (1 : d.G) = 1 := by
  unfold inFrame
  have e : mat2 (1 : d.G) = 1 := rfl
  rw [e, Matrix.mul_one, _root_.PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.incM_b'_k]
theorem matrixRep_eq_frameConj_inFrame (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (x : d.G) : mat2 x = incM F d.b.1 * inFrame d.b x * incM F (d.b⁻¹).1 := by
  unfold inFrame
  calc mat2 x = (incM F d.b.1 * incM F (d.b⁻¹).1) * mat2 x * (incM F d.b.1 * incM F (d.b⁻¹).1) := by
        rw [_root_.PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.incM_b_k, Matrix.one_mul, Matrix.mul_one]
    _ = _ := by simp only [Matrix.mul_assoc]
theorem inFrame_inj_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {x y : d.G} (h : inFrame d.b x = inFrame d.b y) : x = y := by
  have e : mat2 x = mat2 y := by rw [_root_.PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.matrixRep_eq_frameConj_inFrame d x, _root_.PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.matrixRep_eq_frameConj_inFrame d y, h]
  exact Subtype.ext (Units.ext e)
theorem cw_mul_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (w : InfinitePlace F) {p q r : Type} [Fintype q] (X : Matrix p q (AE F E))
    (Y : Matrix q r (AE F E)) : d.cw w (X * Y) = d.cw w X * d.cw w Y := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.cw; exact Matrix.map_mul
theorem cw_one_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (w : InfinitePlace F) {p : Type} [Fintype p] [DecidableEq p] :
    d.cw w (1 : Matrix p p (AE F E)) = 1 := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.cw; exact Matrix.map_one _ (map_zero _) (map_one _)
theorem comm_of_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (w : InfinitePlace F) (x u : d.G) (hx : d.cw w (inFrame d.b x) = 1)
    (hu : ∀ w', w' ≠ w → d.cw w' (inFrame d.b u) = 1) (hf : finOne F • inFrame d.b u = finOne F • 1) :
    x * u = u * x := by
  apply _root_.PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.inFrame_inj_k d
  rw [_root_.PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.inFrame_mul_k, _root_.PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.inFrame_mul_k]
  apply _root_.PositivityTheory.SiegelWeilFormula.Place.cw_ext_k d
  · intro w'
    rw [_root_.PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.cw_mul_k, _root_.PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.cw_mul_k]
    by_cases h : w' = w
    · subst h; rw [hx, Matrix.one_mul, Matrix.mul_one]
    · rw [hu w' h, Matrix.one_mul, Matrix.mul_one]
  · rw [fin_mul, fin_mul, hf, ← fin_mul, ← fin_mul, Matrix.mul_one, Matrix.one_mul]
end UnitaryGroupBasics
namespace UnitaryGroupBasics
variable {n : ℕ}
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem cw_transpose_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (w : InfinitePlace F) {p q : Type} (X : Matrix p q (AE F E)) :
    d.cw w Xᵀ = (d.cw w X)ᵀ := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.cw; exact Matrix.transpose_map.symm
theorem frame_adelic_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) :
    (incM F d.b.1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1).map (cA σ) =
      incM F (Matrix.fromBlocks 0 1 (((R.ε : ℤ) : E) • 1) 0 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) := by
  rw [← R.hε, incM_mul, incM_mul]
  have e1 : incM F d.b.1ᵀ = (incM F d.b.1)ᵀ := by unfold incM; exact Matrix.transpose_map
  have e2 : incM F (dbl d.Y.J) = dbl (incM F d.Y.J) := by
    ext i j; rcases i with i | i <;> rcases j with j | j <;> simp [incM, dbl]
  have e3 : incM F (d.b.1.map σ) = (incM F d.b.1).map (cA σ) := by
    ext i j; simp only [incM, Matrix.map_apply, cA_inclR]
  rw [e1, e2, e3]
theorem form_adelic_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (x : d.G) :
    (inFrame d.b x)ᵀ * ((incM F d.b.1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1).map (cA σ)) *
        (inFrame d.b x).map (cA σ) = (incM F d.b.1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1).map (cA σ) := by
  have hG : (mat2 x)ᵀ * dbl (incM F d.Y.J) * (mat2 x).map (cA σ) = dbl (incM F d.Y.J) := x.2
  have h1 : (incM F (d.b⁻¹).1)ᵀ * (incM F d.b.1)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, _root_.PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.incM_b_k, Matrix.transpose_one]
  have h2 : (incM F d.b.1).map (cA σ) * (incM F (d.b⁻¹).1).map (cA σ) = 1 := by
    rw [← mapc_mul, _root_.PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.incM_b_k, Matrix.map_one _ (map_zero _) (map_one _)]
  unfold inFrame
  rw [Matrix.transpose_mul, Matrix.transpose_mul, mapc_mul, mapc_mul]
  calc _ = (incM F d.b.1)ᵀ * (mat2 x)ᵀ * ((incM F (d.b⁻¹).1)ᵀ * (incM F d.b.1)ᵀ) * dbl (incM F d.Y.J) *
          ((incM F d.b.1).map (cA σ) * (incM F (d.b⁻¹).1).map (cA σ)) * (mat2 x).map (cA σ) *
          (incM F d.b.1).map (cA σ) := by simp only [Matrix.mul_assoc]
    _ = (incM F d.b.1)ᵀ * ((mat2 x)ᵀ * dbl (incM F d.Y.J) * (mat2 x).map (cA σ)) * (incM F d.b.1).map (cA σ) := by
          rw [h1, h2, Matrix.mul_one, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [hG]
theorem cw_Q_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) :
    d.cw w (incM F (Matrix.fromBlocks 0 1 (((R.ε : ℤ) : E) • 1) 0 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E)) =
      Krd.Qc d.n R.ε := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, incM, Krd.Qc, Matrix.one_apply, apply_ite, Matrix.smul_apply] <;> (intro h1 h2; exact absurd h1 h2)
theorem form_w_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (x : d.G) :
    (d.cw w (inFrame d.b x))ᵀ * Krd.Qc d.n R.ε * (d.cw w (inFrame d.b x)).map star = Krd.Qc d.n R.ε := by
  have h := congrArg (d.cw w) (_root_.PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.form_adelic_k d x)
  rw [_root_.PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.frame_adelic_k d R, _root_.PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.cw_mul_k, _root_.PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.cw_mul_k, _root_.PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.cw_Q_k, _root_.PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.cw_transpose_k, _root_.PositivityTheory.SiegelWeilFormula.Place.cw_cA_k] at h
  exact h
end UnitaryGroupBasics
open UnitaryGroupBasics in
theorem split_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (g : d.G) :
    ∃ (y : GR d.n) (x : d.G), g = R.ι w y * x ∧ ∀ y' : GR d.n, x * R.ι w y' = R.ι w y' * x := by
  have hζ0 := Krd.zeta_ne R.hζ
  obtain ⟨M, hM⟩ : ∃ M, M = d.cw w (inFrame d.b g) := ⟨_, rfl⟩
  have hY := Krd.inG_conj R.hζ M (hM ▸ _root_.PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.form_w_k d R w g)
  obtain ⟨y, hy⟩ : ∃ y : GR d.n, mR y = dZ d.n R.ζ * M * dZ d.n R.ζ⁻¹ := ⟨mkGR _ hY, rfl⟩
  refine ⟨y, (R.ι w y)⁻¹ * g, (mul_inv_cancel_left _ _).symm, fun y' => ?_⟩
  have hyw : d.cw w (inFrame d.b (R.ι w y)) = M := by
    have h := R.at_w w y
    rw [hy] at h
    calc d.cw w (inFrame d.b (R.ι w y))
        = dZ d.n R.ζ⁻¹ * (dZ d.n R.ζ * d.cw w (inFrame d.b (R.ι w y))) := by
          rw [← Matrix.mul_assoc, Krd.dZ_inv_mul hζ0, Matrix.one_mul]
      _ = dZ d.n R.ζ⁻¹ * (dZ d.n R.ζ * M * dZ d.n R.ζ⁻¹ * dZ d.n R.ζ) := by rw [h]
      _ = M := by
          simp only [Matrix.mul_assoc]
          rw [Krd.dZ_inv_mul hζ0, Matrix.mul_one, ← Matrix.mul_assoc, Krd.dZ_inv_mul hζ0, Matrix.one_mul]
  refine _root_.PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.comm_of_k d w _ _ ?_ (fun w' h => R.off_w w w' y' h) (R.off_f w y')
  have e1 : inFrame d.b (R.ι w y)⁻¹ * inFrame d.b (R.ι w y) = 1 := by
    rw [← _root_.PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.inFrame_mul_k, inv_mul_cancel, _root_.PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.inFrame_one_k]
  rw [_root_.PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.inFrame_mul_k, _root_.PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.cw_mul_k, ← hM, ← hyw, ← _root_.PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.cw_mul_k, e1, _root_.PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.cw_one_k]
namespace UnitaryGroupBasics
theorem cw_fromBlocks_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (w : InfinitePlace F) (B : Matrix (Fin d.n) (Fin d.n) (AE F E)) :
    d.cw w (Matrix.fromBlocks (1 : Matrix (Fin d.n) (Fin d.n) (AE F E)) B (0 : Matrix (Fin d.n) (Fin d.n) (AE F E)) 1) =
      Matrix.fromBlocks (1 : Matrix (Fin d.n) (Fin d.n) ℂ) (d.cw w B) (0 : Matrix (Fin d.n) (Fin d.n) ℂ) 1 := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.cw
  rw [Matrix.fromBlocks_map, Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_zero _ (map_zero _)]
theorem cw_toBlocks₁₂_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (w : InfinitePlace F) (X : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    d.cw w X.toBlocks₁₂ = (d.cw w X).toBlocks₁₂ := rfl
theorem piInf_trace_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (w : InfinitePlace F) (M : Matrix (Fin d.n) (Fin d.n) (AE F E)) :
    piInf (d.B.emb w) M.trace = (d.cw w M).trace := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, Matrix.trace, map_sum]
theorem cw_unip_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (u : GR d.n) (H : Matrix (Fin d.n) (Fin d.n) ℂ)
    (hu : mR u = nU H) : d.cw w (inFrame d.b (R.ι w u)) = Matrix.fromBlocks 1 (R.ζ • H) 0 1 := by
  have hζ0 := Krd.zeta_ne R.hζ
  have h := R.at_w w u
  rw [hu] at h
  calc d.cw w (inFrame d.b (R.ι w u)) = dZ d.n R.ζ⁻¹ * (dZ d.n R.ζ * d.cw w (inFrame d.b (R.ι w u))) := by
        rw [← Matrix.mul_assoc, Krd.dZ_inv_mul hζ0, Matrix.one_mul]
    _ = dZ d.n R.ζ⁻¹ * (nU H * dZ d.n R.ζ) := by rw [h]
    _ = _ := by simp [dZ, nU, Matrix.fromBlocks_multiply, smul_smul, inv_mul_cancel₀ hζ0, mul_inv_cancel₀ hζ0, Matrix.mul_smul]
end UnitaryGroupBasics
open UnitaryGroupBasics in
theorem nbw_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) {nb : nA σ d.Y d.b → d.G} (h : IsNMap d.b nb)
    (nr : (Fin d.n → Fin d.n → ℝ) → GR d.n) (hnr : ∀ x, mR (nr x) = nU (herm x)) :
    ∃ β : (Fin d.n → Fin d.n → ℝ) → nA σ d.Y d.b, Continuous β ∧ ∀ x, R.ι w (nr x) = nb (β x) := by
  have hP : ∀ x, inFrame d.b (R.ι w (nr x)) = Matrix.fromBlocks 1 (inFrame d.b (R.ι w (nr x))).toBlocks₁₂ 0 1 := by
    intro x
    apply _root_.PositivityTheory.SiegelWeilFormula.Place.cw_ext_k d
    · intro u
      rw [_root_.PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.cw_fromBlocks_k, _root_.PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.cw_toBlocks₁₂_k]
      by_cases hu : u = w
      · subst hu
        rw [_root_.PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.cw_unip_k d R u (nr x) _ (hnr x), Matrix.toBlocks_fromBlocks₁₂]
      · rw [R.off_w w u (nr x) hu, toBlocks₁₂_one, Matrix.fromBlocks_one]
    · rw [Matrix.fromBlocks_smul, fin_toBlocks₁₂, R.off_f w (nr x), ← fin_toBlocks₁₂, toBlocks₁₂_one, smul_zero]
      rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_smul, smul_zero]
  refine ⟨fun x => ⟨(inFrame d.b (R.ι w (nr x))).toBlocks₁₂, AddSubgroup.subset_closure ⟨R.ι w (nr x), hP x⟩⟩, ?_,
    fun x => _root_.PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.inFrame_inj_k d ?_⟩
  · haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
    have hm : Continuous fun g : d.G => mat2 g := Units.continuous_val.comp continuous_subtype_val
    have hi : Continuous fun g : d.G => inFrame d.b g := (continuous_const.matrix_mul hm).matrix_mul continuous_const
    have hc : Continuous fun x => inFrame d.b (R.ι w (nr x)) := hi.comp ((R.cont w).comp (continuous_nr nr hnr))
    refine Continuous.subtype_mk ?_ _
    exact continuous_pi fun i => continuous_pi fun j => hc.matrix_elem (Sum.inl i) (Sum.inr j)
  · rw [h]; exact hP x
open UnitaryGroupBasics in
theorem charW_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) {nb : nA σ d.Y d.b → d.G} (h : IsNMap d.b nb)
    (nr : (Fin d.n → Fin d.n → ℝ) → GR d.n) (hnr : ∀ x, mR (nr x) = nU (herm x))
    (β : (Fin d.n → Fin d.n → ℝ) → nA σ d.Y d.b) (hβ : ∀ x, R.ι w (nr x) = nb (β x)) (T : nF σ d.Y d.b) :
    ∃ β' : Matrix (Fin d.n) (Fin d.n) ℂ, β'.IsHermitian ∧ (T.1.1.det = 0 → β'.det = 0) ∧
      ∀ x, d.B.ψ (d.tt (T.1.1 * (β x).1)) = eTr β' x := by
  have hB : ∀ x, inFrame d.b (R.ι w (nr x)) = Matrix.fromBlocks 1 (β x).1 0 1 := fun x => by rw [hβ x, h]
  have hBw : ∀ x, d.cw w (β x).1 = R.ζ • herm x := fun x => by
    have e := _root_.PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.cw_unip_k d R w (nr x) _ (hnr x)
    rw [hB x, _root_.PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.cw_fromBlocks_k] at e
    exact (Matrix.fromBlocks_inj.1 e).2.1
  have hBu : ∀ x u, u ≠ w → d.cw u (β x).1 = 0 := fun x u hu => by
    have e := R.off_w w u (nr x) hu
    rw [hB x, _root_.PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.cw_fromBlocks_k, ← Matrix.fromBlocks_one] at e
    exact (Matrix.fromBlocks_inj.1 e).2.1
  have hBf : ∀ x, finOne F • (β x).1 = 0 := fun x => by
    have e := R.off_f w (nr x)
    rw [hB x, Matrix.fromBlocks_smul, ← Matrix.fromBlocks_one, Matrix.fromBlocks_smul] at e
    exact (Matrix.fromBlocks_inj.1 e).2.1.trans (smul_zero _)
  have hT : (d.cw w T.1.1)ᵀ + ((R.ε : ℤ) : ℂ) • (d.cw w T.1.1).map star = 0 := by
    refine AddSubgroup.closure_induction
      (p := fun β _ => (d.cw w β)ᵀ + ((R.ε : ℤ) : ℂ) • (d.cw w β).map star = 0) ?_ ?_ ?_ ?_ T.1.2
    · rintro β ⟨x, hx⟩
      have e := _root_.PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.form_w_k d R w x
      rw [hx, _root_.PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.cw_fromBlocks_k] at e
      simp [Krd.Qc, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply] at e
      rw [add_comm]
      exact e
    · ext i j; simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw]
    · intro a b _ _ ha hb
      ext i j
      have ea := congrFun (congrFun ha i) j
      have eb := congrFun (congrFun hb i) j
      simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw] at ea eb ⊢
      linear_combination ea + eb
    · intro a _ ha
      ext i j
      have ea := congrFun (congrFun ha i) j
      simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw] at ea ⊢
      linear_combination -ea
  obtain ⟨Tw, hTw⟩ : ∃ Tw, Tw = d.cw w T.1.1 := ⟨_, rfl⟩
  rw [← hTw] at hT
  have hAh : (R.ζ • Tw)ᴴ = R.ζ • Tw := by
    ext i j
    have e := congrFun (congrFun hT j) i
    simp only [Matrix.add_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.zero_apply,
      smul_eq_mul] at e
    rw [Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, star_mul']
    rcases R.hζ with ⟨hε, hζ⟩ | ⟨hε, hζ⟩
    · rw [hζ]; rw [hε] at e; simp at e ⊢; linear_combination -e
    · rw [hζ]; rw [hε] at e; simp at e ⊢; linear_combination (-Complex.I) * e
  refine ⟨-(2 : ℂ) • (R.ζ • Tw), ?_, fun h0 => ?_, fun x => ?_⟩
  · show (-(2 : ℂ) • (R.ζ • Tw))ᴴ = -(2 : ℂ) • (R.ζ • Tw)
    rw [Matrix.conjTranspose_smul, hAh]
    congr 1
    simp
  · have hd : Tw.det = 0 := by
      rw [hTw, show (d.cw w T.1.1).det = ((piInf (d.B.emb w)).mapMatrix T.1.1).det from rfl, ← RingHom.map_det, h0,
        map_zero]
    rw [Matrix.det_smul, Matrix.det_smul, hd]
    simp
  · have hf : finOne F • (T.1.1 * (β x).1).trace = 0 := by
      rw [← Matrix.trace_smul, ← Matrix.mul_smul, hBf x, Matrix.mul_zero, Matrix.trace_zero]
    have hw : ∀ u, u ≠ w → piInf (d.B.emb u) (T.1.1 * (β x).1).trace = 0 := fun u hu => by
      rw [_root_.PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.piInf_trace_k, _root_.PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.cw_mul_k, hBu x u hu, Matrix.mul_zero, Matrix.trace_zero]
    have hz := Place.psi_trace_at d.std d.cm d.B.emb w (T.1.1 * (β x).1).trace hf hw
    have hw' : piInf (d.B.emb w) (T.1.1 * (β x).1).trace = ((R.ζ • Tw) * herm x).trace := by
      rw [_root_.PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.piInf_trace_k, _root_.PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.cw_mul_k, hBw x, ← hTw, Matrix.mul_smul, Matrix.smul_mul]
    have hreal : ((((R.ζ • Tw) * herm x).trace).re : ℂ) = ((R.ζ • Tw) * herm x).trace := by
      have hs : star (((R.ζ • Tw) * herm x).trace) = ((R.ζ • Tw) * herm x).trace := by
        rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hAh, herm_conjTranspose', Matrix.trace_mul_comm]
      exact Complex.conj_eq_iff_re.1 hs
    have eR : (-(2 : ℂ) • (R.ζ • Tw) * herm x).trace = -2 * (R.ζ • Tw * herm x).trace := by
      rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
    unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.tt eTr
    rw [hz, hw', eR]
    generalize (R.ζ • Tw * herm x).trace = c at hreal ⊢
    congr 1
    push_cast
    rw [hreal]
    ring
end PositivityTheory.SiegelWeilFormula.KSing
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitMeasND
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KWhit
open PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem meas_detA_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : d.A.J.det ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have key : (d.A.J.map (d.B.emb w).1).det ≠ 0 := by
    rcases d.ok.sign with ⟨hA, -⟩ | ⟨hA, -⟩
    · exact meas_det_of_hasSig (hA.sig w)
    · have h := meas_det_of_hasSig (hA.sig w)
      rw [Matrix.det_smul] at h
      intro h0; exact h (by rw [h0, mul_zero])
  intro h0
  apply key
  have hm := RingHom.map_det (d.B.emb w).1 d.A.J
  rw [RingHom.mapMatrix_apply, h0, map_zero] at hm
  exact hm.symm
theorem meas_hermND'_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {η : E} (hη : η ≠ 0) (hh : ∀ i j, σ (η * d.A.J j i) = η * d.A.J i j) :
    HeckeCharacterZeroLocus.SiegelWeilU.IsHermND σ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) := by
  refine ⟨fun i j => ?_, ?_⟩
  · simp only [_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul]
    exact hh j i
  · rw [_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k, Matrix.det_transpose, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hη) (_root_.PositivityTheory.SiegelWeilFormula.KWhit.meas_detA_k d)
end PositivityTheory.SiegelWeilFormula.KWhit
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAvacVacCut
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Avac
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
def vg_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ) (X : Mx F E d.m d.n) : ℂ :=
  (∏ w, fP 1 (R.loc w X)) * g fun k => (d.crd X k).2
theorem vg_mem_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ} (hg : g ∈ SB _) : _root_.PositivityTheory.SiegelWeilFormula.Avac.vg_k R g ∈ R.vac :=
  Submodule.subset_span ⟨g, hg, rfl⟩
theorem vac_le_fock_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : R.vac ≤ R.fock := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨g, hg, rfl⟩
  exact Submodule.subset_span ⟨fun _ => 1, g, hg, rfl⟩
def Tl_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : d.Fn →ₗ[ℂ] (Mx F E d.m d.n → ℂ) where
  toFun := d.T
  map_add' Φ Ψ := funext fun X => by
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.T, Pi.add_apply, ← map_add (f := _)]
    congr 1
    funext z
    exact mul_add _ _ _
  map_smul' c Φ := funext fun X => by
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.T, Pi.smul_apply, RingHom.id_apply, ← map_smul]
    congr 1
    funext z
    exact mul_left_comm _ _ _
theorem T_inj_k (hB : _root_.PositivityTheory.SiegelWeilFormula.TBij_k) {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} {Φ Ψ : d.Fn} (hΦ : Φ ∈ d.sch) (hΨ : Ψ ∈ d.sch) (h : d.T Φ = d.T Ψ) : Φ = Ψ := by
  have e : d.T (Φ - Ψ) = 0 := by
    have := (_root_.PositivityTheory.SiegelWeilFormula.Avac.Tl_k d).map_sub Φ Ψ
    simp only [_root_.PositivityTheory.SiegelWeilFormula.Avac.Tl_k, LinearMap.coe_mk, AddHom.coe_mk] at this
    rw [this, h, sub_self]
  exact sub_eq_zero.1 ((hB F E σ d).2.2 _ (sub_mem hΦ hΨ) e)
end PositivityTheory.SiegelWeilFormula.Avac
end
end
end
