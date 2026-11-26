module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecaysOfMemSmoothSpan
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PropEOfAdmissible
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsotypicRowLocalSplitExists
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousIotaOQOfDataStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.ThetaPoisson GroundTheory.Global
open scoped ComplexConjugate nonZeroDivisors

namespace GlobalTheory.RSTheta

section Row

variable {R : Type} [CommRing R] {a : ℕ}

def rowMat (ℓ : Fin a) (y : Fin a → R) : Matrix (Fin a) (Fin a) R := (1 : Matrix (Fin a) (Fin a) R).updateRow ℓ y

theorem det_rowMat (ℓ : Fin a) (y : Fin a → R) : (rowMat ℓ y).det = y ℓ := by
  have h := det_updateRow_sum (1 : Matrix (Fin a) (Fin a) R) ℓ y
  have e : ∑ k, y k • (1 : Matrix (Fin a) (Fin a) R) k = y := by
    funext j
    simp [Matrix.one_apply, Finset.sum_apply]
  rw [e] at h
  simpa [rowMat] using h

theorem isUnit_rowMat_iff {ℓ : Fin a} {y : Fin a → R} : IsUnit (rowMat ℓ y) ↔ IsUnit (y ℓ) := by
  rw [isUnit_iff_isUnit_det, det_rowMat]


open Classical in
def rowGL (ℓ : Fin a) (y : Fin a → R) : GL (Fin a) R :=
  if h : IsUnit (y ℓ) then (isUnit_rowMat_iff.2 h).unit else 1

theorem val_rowGL {ℓ : Fin a} {y : Fin a → R} (h : IsUnit (y ℓ)) : (rowGL ℓ y).val = rowMat ℓ y := by
  rw [rowGL, dite_eq_left h, IsUnit.unit_spec]

theorem single_vecMul_rowGL {ℓ : Fin a} {y : Fin a → R} (h : IsUnit (y ℓ)) :
    Pi.single ℓ 1 ᵥ* (rowGL ℓ y).val = y := by
  rw [val_rowGL h, single_one_vecMul]
  exact updateRow_self

theorem rowGL_single (ℓ : Fin a) : rowGL ℓ (Pi.single ℓ (1 : R)) = 1 := by
  refine Units.ext ((val_rowGL (by simp)).trans ?_)
  have : (Pi.single ℓ 1 : Fin a → R) = (1 : Matrix (Fin a) (Fin a) R) ℓ := by
    funext j
    simp [Matrix.one_apply, Pi.single_apply, eq_comm]
  rw [rowMat, this]
  exact updateRow_eq_self _ _

end Row

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}


omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
variable (E) in
def rowSet (ℓ : Fin a) : Set (Fin a → Cinf E) := {u | ∀ w, u ℓ w ≠ 0}

omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
theorem isUnit_of_mem_rowSet {ℓ : Fin a} {u : Fin a → Cinf E} (h : u ∈ rowSet E ℓ) : IsUnit (u ℓ) :=
  Pi.isUnit_iff.2 fun w => (h w).isUnit

omit [_root_.NumberField.IsTotallyComplex E] in
theorem isOpen_rowSet (ℓ : Fin a) : IsOpen (rowSet E ℓ) := by
  rw [rowSet, Set.setOf_forall]
  exact isOpen_iInter_of_finite fun w => isOpen_ne_fun (by fun_prop) continuous_const


omit [_root_.NumberField.IsTotallyComplex E] in
theorem continuousOn_rowGL (ℓ : Fin a) : ContinuousOn (rowGL ℓ) (rowSet E ℓ) := by
  refine GlobalTheory.CuspQuot.isOpenEmbedding_val.isInducing.continuousOn_iff.2 ?_
  have h : Continuous fun u : Fin a → Cinf E => rowMat ℓ u := continuous_const.matrix_updateRow ℓ continuous_id
  exact h.continuousOn.congr fun u hu => val_rowGL (isUnit_of_mem_rowSet hu)

def rsInf (ℓ : Fin a) (φ φ' : GA E a → ℂ) (Φ : (Fin a → Cinf E) → ℂ) (g : GA E a) (u : Fin a → Cinf E) : ℂ :=
  φ (g * (infGL E a (rowGL ℓ u))⁻¹) * conj (φ' (g * (infGL E a (rowGL ℓ u))⁻¹)) * Φ u

def rsPsi (ℓ : Fin a) (φ φ' : GA E a → ℂ) (Φ : (Fin a → Cinf E) → ℂ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ)
    (η : Fin a → Af E) (g : GA E a) (y : Fin a → Ad E) : ℂ :=
  thetaFn (rsInf ℓ φ φ' Φ g) J η y

theorem rsPsi_ratGL_mul (ℓ : Fin a) {φ φ' : GA E a → ℂ} (h : ∀ γ g, φ (ratGL E a γ * g) = φ g)
    (h' : ∀ γ g, φ' (ratGL E a γ * g) = φ' g) (Φ : (Fin a → Cinf E) → ℂ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ)
    (η : Fin a → Af E) (γ : GL (Fin a) E) (g : GA E a) (y : Fin a → Ad E) :
    rsPsi ℓ φ φ' Φ J η (ratGL E a γ * g) y = rsPsi ℓ φ φ' Φ J η g y := by
  simp only [rsPsi, thetaFn, rsInf, mul_assoc, h, h']

theorem continuousOn_inv_rowGL (ℓ : Fin a) :
    ContinuousOn (fun u => (infGL E a (rowGL ℓ u))⁻¹) (rowSet E ℓ) :=
  (GlobalTheory.CuspQuot.continuous_infGL.comp_continuousOn (continuousOn_rowGL ℓ)).inv

theorem continuous_rsInf {ℓ : Fin a} {φ φ' : GA E a → ℂ} {Φ : (Fin a → Cinf E) → ℂ} (h : Continuous φ)
    (h' : Continuous φ') (hΦ : Continuous Φ) (hs : tsupport Φ ⊆ rowSet E ℓ) :
    Continuous fun p : GA E a × (Fin a → Cinf E) => rsInf ℓ φ φ' Φ p.1 p.2 := by
  refine continuous_iff_continuousAt.2 fun p => ?_
  by_cases hp : p.2 ∈ tsupport Φ
  · have h1 : ContinuousAt (fun p : GA E a × (Fin a → Cinf E) => p.1 * (infGL E a (rowGL ℓ p.2))⁻¹) p :=
      continuousAt_fst.mul (ContinuousAt.comp (f := Prod.snd)
        ((continuousOn_inv_rowGL ℓ).continuousAt ((isOpen_rowSet ℓ).mem_nhds (hs hp))) continuousAt_snd)
    exact ((h.continuousAt.comp h1).mul ((Complex.continuous_conj.comp h').continuousAt.comp h1)).mul
      (hΦ.comp continuous_snd).continuousAt
  · refine (continuousAt_const (y := (0 : ℂ))).congr ?_
    filter_upwards [continuousAt_snd.eventually (notMem_tsupport_iff_eventuallyEq.1 hp)] with q hq
    simp [rsInf, hq]

omit [_root_.NumberField.IsTotallyComplex E] in
theorem isOpen_latt (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) : IsOpen (latt a J) := by
  rw [latt, Set.setOf_forall]
  exact isOpen_iInter_of_finite fun i => (isOpen_idealFiniteAdeles J).preimage (continuous_apply i)

omit [_root_.NumberField.IsTotallyComplex E] in
theorem isCompact_latt (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) : IsCompact (latt a J) :=
  isCompact_pi_infinite fun _ => isCompact_idealFiniteAdeles J

omit [_root_.NumberField.IsTotallyComplex E] in
theorem isClosed_latt (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) : IsClosed (latt a J) := by
  rw [latt, Set.setOf_forall]
  exact isClosed_iInter fun i =>
    (AddSubgroup.isClosed_of_isOpen _ (isOpen_idealFiniteAdeles J)).preimage (continuous_apply i)

theorem continuous_rsPsi {ℓ : Fin a} {φ φ' : GA E a → ℂ} {Φ : (Fin a → Cinf E) → ℂ} (h : Continuous φ)
    (h' : Continuous φ') (hΦ : Continuous Φ) (hs : tsupport Φ ⊆ rowSet E ℓ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ)
    (η : Fin a → Af E) : Continuous fun p : GA E a × (Fin a → Ad E) => rsPsi ℓ φ φ' Φ J η p.1 p.2 := by
  have h1 : Continuous fun p : GA E a × (Fin a → Ad E) => (p.1, fun i => pInf E (p.2 i)) :=
    continuous_fst.prodMk (continuous_pi fun i =>
      GlobalTheory.ShortVecDecay.continuous_pInf.comp ((continuous_apply i).comp continuous_snd))
  have h2 : Continuous fun p : GA E a × (Fin a → Ad E) => (fun i => pFin E (p.2 i)) - η :=
    (continuous_pi fun i => (continuous_snd : Continuous (pFin E)).comp
      ((continuous_apply i).comp continuous_snd)).sub continuous_const
  have h3 : Continuous ((latt a J).indicator (1 : (Fin a → Af E) → ℂ)) :=
    (IsClopen.continuous_indicator ⟨isClosed_latt J, isOpen_latt J⟩ continuous_const)
  exact ((continuous_rsInf h h' hΦ hs).comp h1).mul (h3.comp h2)

theorem continuous_of_mem_smoothSpan {π : CuspSub E a} {F : GA E a → ℂ} (hF : F ∈ GlobalTheory.JSW.smoothSpan π) :
    Continuous F := by
  induction hF using Submodule.span_induction with
  | mem F hF =>
    have hS := GlobalTheory.ShortVecDecay.smoothSpan_le_Sm π (Submodule.subset_span hF)
    obtain ⟨f, φ, hf, hφ, rfl⟩ := hF
    refine ContAut.continuous_of_isOpen_stab E a ⟨_, hS⟩ (isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset
      ((π.cusp φ hφ).1.level.mem_nhds (by simp)) fun k hk => Subtype.ext (funext fun g => ?_)))
    have e : (fun x => φ.1 (x * finGL E a k)) = φ.1 := congrArg Subtype.val hk
    exact (GlobalTheory.JSW.smoothInf_rt_fin f φ.1 k g).symm.trans (by rw [e])
  | zero => exact continuous_const
  | add F G _ _ hF hG => exact hF.add hG
  | smul z F _ hF => exact hF.const_smul z

theorem continuous_of_mem_or {π : CuspSub E a} {φ : Sm E a} (h : φ ∈ π.V ∨ φ.1 ∈ GlobalTheory.JSW.smoothSpan π) :
    Continuous φ.1 :=
  h.elim (fun h => ContAut.continuous_of_isOpen_stab E a φ (π.cusp φ h).1.level) continuous_of_mem_smoothSpan

end GlobalTheory.RSTheta

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PotSemistableOfPotCrystallineDecompositionGroup
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PotSemistableOfPotCrystallineDecompositionGroup
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open TensorProduct Module GlobalTheory.Pst

namespace GlobalTheory.PstOfCrys

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P}

theorem mulV_crisIncl_comm {LL : Type} [Field LL] [Algebra ℚ_[l] LL] {V : Type} [AddCommGroup V] [Module LL V]
    [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V] (c : ↥(MaximalUnramifiedExtension l)) (x : P.R.B ⊗[ℚ_[l]] V) :
    mulV P LL V c (crisIncl P LL V (TensorProduct.comm ℚ_[l] P.R.B V x)) =
      crisIncl P LL V (TensorProduct.comm ℚ_[l] P.R.B V (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c • x)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b v =>
    rw [TensorProduct.smul_tmul', TensorProduct.comm_tmul, TensorProduct.comm_tmul, crisIncl_tmul, crisIncl_tmul,
      mulV_tmul, Polynomial.algebraMap_apply, smul_eq_mul, C_mul]
  | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]

theorem isPst_of_isCrys (T : LocTied l P AI) {K LL : FinExt l} {V : Type} [AddCommGroup V] [Module ↥LL.1 V]
    [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V]
    (ρ : Representation ↥LL.1 ↥(GK K) V) (hc : IsCrys (P.PD K) ρ) : IsPst P ρ := by
  haveI := LL.2
  haveI : FiniteDimensional ℚ_[l] V := Module.Finite.trans ↥LL.1 V
  haveI : IsDomain P.R.B := GlobalTheory.RegularRing.isDomain_of_tied T K
  have hf := GlobalTheory.Per.TiedRestrict.fracInv_of_tied T K
  obtain ⟨hdom, hreg, -⟩ := GlobalTheory.Pst.stRegular l P AI ⟨T⟩
  have hup := GlobalTheory.PstRank.rank_DpstUr_le P hdom hreg ρ
  obtain ⟨hfin, -⟩ := GlobalTheory.RegularRing.finite_le₀ (P.PD K) hf ρ
  have hd := (GlobalTheory.RegularRing.isCrys_iff_finrank (P.PD K) ρ).1 hc
  let e := set_option synthInstance.maxHeartbeats 200000 in
    Module.finBasisOfFinrankEq ↥(K0 K) _ hd
  have hB := GlobalTheory.RegularRing.indepB (P.PD K) hf ρ e e.linearIndependent
  have hmem : ∀ i, crisIncl P ↥LL.1 V (TensorProduct.comm ℚ_[l] P.R.B V (e i : P.R.B ⊗[ℚ_[l]] V)) ∈ Dpst P ρ := by
    intro i
    refine (mem_Dpst P ρ).mpr ⟨K, fun g _ => ?_⟩
    rw [stRep_crisIncl]
    congr 1
    exact (GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.mem_Dcris (PD := P.PD K) ρ _).1 (e i).2 g
  let y : Fin (finrank ℚ_[l] V) → DpstUr P ρ := fun i => toUr P ρ ⟨_, hmem i⟩
  have hli : LinearIndependent ↥(MaximalUnramifiedExtension l) y := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have h1 : (((toUr P ρ).symm (∑ j, c j • y j) : ↥(Dpst P ρ)) : V ⊗[ℚ_[l]] Bst P) = 0 := by
      rw [hc]; rfl
    have h2 : (((toUr P ρ).symm (∑ j, c j • y j) : ↥(Dpst P ρ)) : V ⊗[ℚ_[l]] Bst P) =
        crisIncl P ↥LL.1 V (TensorProduct.comm ℚ_[l] P.R.B V
          (∑ j, algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (c j) • (e j : P.R.B ⊗[ℚ_[l]] V))) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Submodule.coe_sum, map_sum, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← mulV_crisIncl_comm]
      rfl
    rw [h2] at h1
    have h3 : ∑ j, algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (c j) • (e j : P.R.B ⊗[ℚ_[l]] V) = 0 :=
      (TensorProduct.comm ℚ_[l] P.R.B V).injective
        (crisIncl_injective P (h1.trans (map_zero _).symm) |>.trans (map_zero _).symm)
    have h4 := Fintype.linearIndependent_iff.1 hB (fun j => algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (c j)) h3 i
    exact (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B).injective (h4.trans (map_zero _).symm)
  have hlow : (finrank ℚ_[l] V : Cardinal) ≤ Module.rank ↥(MaximalUnramifiedExtension l) (DpstUr P ρ) := by
    have := hli.cardinal_le_rank
    rwa [Cardinal.mk_fintype, Fintype.card_fin] at this
  have hV : Module.rank ℚ_[l] V = (finrank ℚ_[l] V : Cardinal) := (Module.finrank_eq_rank ℚ_[l] V).symm
  rw [IsPst, hV]
  exact le_antisymm hup hlow

end GlobalTheory.PstOfCrys

namespace GlobalTheory.PstOfCrys

theorem pst_of_pc : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (K' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).Kw.1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : ↥(GK (D.nbr i w hw).Kw)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).actB g (algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c) = algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c') (m : ℕ) (r : GE D.nd →* GL (Fin m) (D.nd.O i)), Continuous (fun g => ((r g : GL _ _) : Matrix (Fin m) (Fin m) (D.nd.O i))) → (pc (D.loc (D.nd.l i)) h hN hF hS).IsPotCrys ((D.nbr i w hw).rep (r.comp (decS D.nd w))) → GlobalTheory.Pst.IsPstAt (D.loc (D.nd.l i)) (D.nbr i w hw) (GlobalTheory.Pst.resDec D.nd.plOm.1 (mapRep (iotaOQ D.nd D.naut i) r) w) := by
  intro D i w hw K' h hN hF hS m r _ hpc
  let r' : ↥(Dec (F := D.host.E) (D.nd.plOm.1 w)) →* GL (Fin m) ↥(D.nbr i w hw).LL.1 :=
    mapRep (D.nbr i w hw).toLL (r.comp (decS D.nd w))
  have hmodel : IsModel (D.nbr i w hw)
      (resDec D.nd.plOm.1 (mapRep (iotaOQ D.nd D.naut i) r) w) (D.nbr i w hw).LL r' := by
    refine ⟨le_rfl, ?_⟩
    ext g a b
    exact ((D.loc_tie i w hw).1 _).symm
  refine ⟨(D.nbr i w hw).LL, r', hmodel, ?_⟩
  have hc := ((GlobalTheory.PcRes.main _ (D.loc (D.nd.l i)) _ K' (D.nbr i w hw).LL h hN hF hS _ _).2).1 hpc
  have hp := isPst_of_isCrys (D.locT (D.nd.l i)) _ hc
  exact (GlobalTheory.PstLaws.isPst_resTo_iff (D.loc (D.nd.l i)) _ h).1 hp

end GlobalTheory.PstOfCrys
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PotSemistableOfPotCrystallineDecompositionGroupStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.potSemistable_of_potCrystalline_decompositionGroup : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (K' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).Kw.1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : ↥(GK (D.nbr i w hw).Kw)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).actB g (algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c) = algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c') (m : ℕ) (r : GE D.nd →* GL (Fin m) (D.nd.O i)), Continuous (fun g => ((r g : GL _ _) : Matrix (Fin m) (Fin m) (D.nd.O i))) → (pc (D.loc (D.nd.l i)) h hN hF hS).IsPotCrys ((D.nbr i w hw).rep (r.comp (decS D.nd w))) → GlobalTheory.Pst.IsPstAt (D.loc (D.nd.l i)) (D.nbr i w hw) (GlobalTheory.Pst.resDec D.nd.plOm.1 (mapRep (iotaOQ D.nd D.naut i) r) w) := by
  first | exact @GlobalTheory.PstOfCrys.pst_of_pc | exact GlobalTheory.PstOfCrys.pst_of_pc | (intros; apply GlobalTheory.PstOfCrys.pst_of_pc <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameUniformizerPower
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.DepthZeroRankOneLabel

open ValuativeRel

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {g : ℕ} [Fact g.Prime]

theorem val_lt_iff (y : w.adicCompletion E) : valuation (w.adicCompletion E) y < 1 ↔ ‖y‖ < 1 := by
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := isEquiv (valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))
  rw [he.lt_one_iff_lt_one, Valued.toNormedField.norm_lt_one_iff]

theorem val_le_iff (y : w.adicCompletion E) : valuation (w.adicCompletion E) y ≤ 1 ↔ ‖y‖ ≤ 1 := by
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := isEquiv (valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))
  rw [he.le_one_iff_le_one, Valued.toNormedField.norm_le_one_iff]

theorem val_lt_of_mem {x : 𝓞 E} (hx : x ∈ w.asIdeal) :
    valuation (w.adicCompletion E) (algebraMap E (w.adicCompletion E) (x : E)) < 1 := by
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := isEquiv (valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))
  rw [he.lt_one_iff_lt_one]
  rw [adic_valued_algebraMap, RingOfIntegers.coe_eq_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_lt_one_iff_mem]
  exact hx

variable (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i)

include hi in
theorem val_int_le (z : ℤ_[g]) : valuation (w.adicCompletion E) (i (z : ℚ_[g])) ≤ 1 :=
  (val_le_iff _).2 (GlobalTheory.TypeRec.Model.emb_le w g i.toRingHom hi _ z.2)

include hi in
theorem val_int_lt (hw : ((g : ℕ) : 𝓞 E) ∈ w.asIdeal) (z : ℤ_[g]) (hz : PadicInt.toZMod z = 0) :
    valuation (w.adicCompletion E) (i (z : ℚ_[g])) < 1 := by
  have h1 : z ∈ RingHom.ker (PadicInt.toZMod (p := g)) := hz
  rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at h1
  obtain ⟨c, rfl⟩ := h1
  rw [PadicInt.coe_mul, map_mul, map_mul, PadicInt.coe_natCast, map_natCast]
  exact mul_lt_one_of_nonneg_of_lt_one_right (val_int_le i hi c) zero_le
    ((val_lt_iff _).2 (Formalism.BasicNotions.Examples₂.LocF.norm_l_lt w g hw))

include hi in
theorem exists_red (hw : ((g : ℕ) : 𝓞 E) ∈ w.asIdeal) (μ : (w.adicCompletion E)ˣ →* ℂˣ)
    (hT : GlobalTheory.SplitWeil.IsTame μ) :
    ∃ θ : (ZMod g)ˣ →* ℂˣ, ∀ z : ℤ_[g]ˣ, θ (Units.map (PadicInt.toZMod (p := g)).toMonoidHom z) =
      μ (Units.map i.toRingHom.toMonoidHom (Units.map (algebraMap ℤ_[g] ℚ_[g]).toMonoidHom z)) := by
  have hs := IsLocalRing.surjective_units_map_of_local_ringHom (PadicInt.toZMod (p := g))
    (ZMod.ringHom_surjective _) (IsLocalHom.of_surjective _ (ZMod.ringHom_surjective _))
  let f : ℤ_[g]ˣ →* (ZMod g)ˣ := Units.map (PadicInt.toZMod (p := g)).toMonoidHom
  let φ : ℤ_[g]ˣ →* ℂˣ :=
    μ.comp ((Units.map i.toRingHom.toMonoidHom).comp (Units.map (algebraMap ℤ_[g] ℚ_[g]).toMonoidHom))
  have hker : f.ker ≤ φ.ker := fun z hz => by
    rw [MonoidHom.mem_ker] at hz ⊢
    apply hT
    have h1 : PadicInt.toZMod ((z : ℤ_[g]) - 1) = 0 := by
      have e := congrArg Units.val hz
      rw [map_sub, map_one, sub_eq_zero]
      exact e
    have := val_int_lt i hi hw ((z : ℤ_[g]) - 1) h1
    simpa [φ] using this
  exact ⟨f.liftOfSurjective hs ⟨φ, hker⟩, fun z => MonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨φ, hker⟩ z⟩

end GlobalTheory.DepthZeroRankOneLabel

namespace GlobalTheory.DepthZeroRankOneLabel

open ValuativeRel GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {g : ℕ} [Fact g.Prime]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem inflates_units (i : ℚ_[g] ≃+* w.adicCompletion E) (θ : (ZMod g)ˣ →* ℂˣ) (χ : (w.adicCompletion E)ˣ →* ℂˣ)
    (hχ : GlobalTheory.SmGL.IsSmoothChar χ)
    (hθ : ∀ z : ℤ_[g]ˣ, θ (Units.map (PadicInt.toZMod (p := g)).toMonoidHom z) =
      χ (Units.map i.toRingHom.toMonoidHom (Units.map (algebraMap ℤ_[g] ℚ_[g]).toMonoidHom z))) :
    GlobalTheory.SerSys.TameGen.Inflates ((GlobalTheory.SmGL.IrrRep.det (Fin 1) χ hχ).ρ.comp (Matrix.GeneralLinearGroup.map i.toRingHom))
      (GlobalTheory.Published.DepthZeroModel.tauOne θ) := by
  refine ⟨LinearMap.id, fun e => (one_ne_zero : (1 : ℂ) ≠ 0) (LinearMap.congr_fun e (1 : ℂ)), fun k (v : ℂ) => ?_⟩
  have h1 : Matrix.GeneralLinearGroup.det (GlobalTheory.GLp.inc g 1 k) =
      Units.map (algebraMap ℤ_[g] ℚ_[g]).toMonoidHom (Matrix.GeneralLinearGroup.det k) := by
    ext; simp [GlobalTheory.GLp.inc, RingHom.map_det]
  have h2 : Matrix.GeneralLinearGroup.det (GlobalTheory.GLp.red g 1 k) =
      Units.map (PadicInt.toZMod (p := g)).toMonoidHom (Matrix.GeneralLinearGroup.det k) := by
    ext; simp [GlobalTheory.GLp.red, RingHom.map_det]
  have e2 : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g 1 k)) =
      Units.map i.toRingHom.toMonoidHom (Matrix.GeneralLinearGroup.det (GlobalTheory.GLp.inc g 1 k)) := by
    ext; simp
  change ((θ (Matrix.GeneralLinearGroup.det (GlobalTheory.GLp.red g 1 k)) : ℂˣ) : ℂ) • v =
    ((χ (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g 1 k))) : ℂˣ) : ℂ) • v
  rw [e2, h1, h2, hθ]

end GlobalTheory.DepthZeroRankOneLabel

namespace GlobalTheory.DepthZeroRankOneLabel

open GlobalTheory.TameRes

theorem residue_of_cong {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) (P : HeightOneSpectrum (𝓞 E)) (g : ℕ) [Fact g.Prime] (hAP : IsPlaceOver (F := E) A P)
    (hN : normV P = g) (hgP : ((g : ℕ) : 𝓞 E) ∈ P.asIdeal) (hgP2 : ((g : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2)
    (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g) (σ : G E Ω) (ζ : ℕ → Formalism.CyclotomicNorms.Fbar g)
    (hσ : σ ∈ Ine (F := E) A) (hζ : IsGenSys ζ) (hT : TameCoupled A κ σ ζ) (u ϖ : 𝓞 E) (π : Ω)
    (hϖ : ϖ ∈ P.asIdeal) (hϖ2 : ϖ ∉ P.asIdeal ^ 2) (hπ : π ^ (normV P - 1) = algebraMap E Ω (ϖ : E))
    (hv : A.valuation (σ π / π - algebraMap E Ω (u : E)) < 1) :
    ∃ a : ℕ, a.Coprime g ∧ u - (a : 𝓞 E) ∈ P.asIdeal ∧
      algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) (a : ZMod g) = ζ 1 := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  have hgp : g.Prime := Fact.out
  have hg2 : 2 ≤ g := hgp.two_le
  have hgΩ : ((g : ℕ) : Ω) ≠ 0 := Nat.cast_ne_zero.mpr hgp.ne_zero
  rw [hN] at hπ

  have hg1 : 0 < g - 1 := by omega
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq ((g : ℕ) : Ω) hg1
  have hy0 : y ≠ 0 := by rintro rfl; rw [zero_pow hg1.ne'] at hy; exact hgΩ hy.symm
  have hTy : redThrough A κ (σ y / y) = ζ 1 := hT 1 one_pos y (by rw [pow_one]; exact hy)
  have hϖ0 : algebraMap E Ω (ϖ : E) ≠ 0 := by
    rw [ne_eq, map_eq_zero, RingOfIntegers.coe_eq_zero_iff]
    rintro rfl; exact hϖ2 (zero_mem _)
  have hπ0 : π ≠ 0 := by rintro rfl; rw [zero_pow hg1.ne'] at hπ; exact hϖ0 hπ.symm
  have hϖg : A.valuation (algebraMap E Ω (ϖ : E)) = A.valuation ((g : ℕ) : Ω) := by
    have e : ((g : ℕ) : Ω) = algebraMap E Ω (((g : ℕ) : 𝓞 E) : E) := by simp
    rw [e]
    exact le_antisymm (val_le_of_unif hAP hϖ hgP hgP2) (val_le_of_unif hAP hgP hϖ hϖ2)
  have hπy : A.valuation π = A.valuation y := by
    have h1 : A.valuation π ^ (g - 1) = A.valuation y ^ (g - 1) := by
      rw [← map_pow, ← map_pow, hπ, hy, hϖg]
    exact (pow_left_inj₀ zero_le zero_le hg1.ne').mp h1
  have hvy0 : A.valuation y ≠ 0 := by simpa using hy0
  have hw1 : A.valuation (π / y) = 1 := by rw [map_div₀, hπy, div_self hvy0]
  have hwσ : A.valuation (σ (π / y) - π / y) < 1 := hσ.2 _ hw1.le
  have hσy0 : σ y ≠ 0 := fun h => hy0 (σ.injective (by rw [h, map_zero]))
  have key : σ π / π - σ y / y = (σ y / y) * ((σ (π / y) - π / y) / (π / y)) := by
    rw [map_div₀]
    field_simp
  have hq : A.valuation (σ y / y) ≤ 1 := (A.valuation_le_one_iff _).2 (tameQuot_mem A σ hg1 hgΩ hy)
  have h1 : A.valuation (σ π / π - σ y / y) < 1 := by
    rw [key, map_mul, map_div₀ A.valuation (σ (π / y) - π / y), hw1, div_one]
    calc A.valuation (σ y / y) * A.valuation (σ (π / y) - π / y)
        ≤ 1 * A.valuation (σ (π / y) - π / y) := by gcongr
      _ < 1 := by rw [one_mul]; exact hwσ

  obtain ⟨a, -, hua⟩ := exists_nat_sub_mem P g hN hgP u
  have hua' : A.valuation (algebraMap E Ω (u : E) - (a : Ω)) < 1 := by
    have := (hAP (u - (a : 𝓞 E))).2 hua
    simpa using this
  have h3 : A.valuation (σ y / y - (a : Ω)) < 1 := by
    have e : σ y / y - (a : Ω) = -(σ π / π - σ y / y) + (σ π / π - algebraMap E Ω (u : E)) +
        (algebraMap E Ω (u : E) - (a : Ω)) := by ring
    rw [e]
    refine Valuation.map_add_lt _ (Valuation.map_add_lt _ ?_ hv) hua'
    rw [Valuation.map_neg]; exact h1
  have haA : (a : Ω) ∈ A := by exact_mod_cast (natCast_mem A a)
  have hred : redThrough A κ (σ y / y) = (a : Formalism.CyclotomicNorms.Fbar g) := by
    rw [redThrough_eq_of_val_sub κ (tameQuot_mem A σ hg1 hgΩ hy) haA h3]
    unfold redThrough
    rw [dite_eq_left haA]
    have : (⟨(a : Ω), haA⟩ : A) = (a : A) := Subtype.ext (by simp)
    rw [this, map_natCast, map_natCast]
  have hz : ζ 1 = (a : Formalism.CyclotomicNorms.Fbar g) := by rw [← hTy, hred]
  refine ⟨a, ?_, hua, by rw [map_natCast, hz]⟩
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hgp]
  intro hd
  have h0 : (a : Formalism.CyclotomicNorms.Fbar g) = 0 := (CharP.cast_eq_zero_iff (Formalism.CyclotomicNorms.Fbar g) g a).2 hd
  have ho := (hζ 1 one_pos).1
  rw [hz, h0, pow_one] at ho
  have hz0 : orderOf (0 : Formalism.CyclotomicNorms.Fbar g) = 0 := by
    rw [orderOf_eq_zero_iff']
    intro n hn
    rw [zero_pow (Nat.pos_iff_ne_zero.mp hn)]
    exact zero_ne_one
  omega

end GlobalTheory.DepthZeroRankOneLabel

namespace GlobalTheory.DepthZeroRankOneLabel

def labDatum {g : ℕ} [Fact g.Prime] (t : Formalism.CyclotomicNorms.Fbar g →* ℂ)
    (ht : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y)
    (ζ : ℕ → Formalism.CyclotomicNorms.Fbar g) (hζ : IsGenSys ζ) : GlobalTheory.GLq.LabelDatum g where
  teich := t
  teich_inj := ht
  gen := ζ
  gen_order d hd := (hζ d hd).1
  gen_norm d e hd he := (hζ d hd).2 (d * e) (dvd_mul_right d e) (Nat.mul_pos hd he)

end GlobalTheory.DepthZeroRankOneLabel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DepthZeroOfHyp
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped Pointwise

namespace GlobalTheory.DepthZeroType

theorem isSplitPl_of_over (D : D7) (k : Fin 2) (w : PlE D.host) (hw : w ∈ placesOver D.host.E (D.host.g k)) :
    IsSplitPl D.host w := by
  haveI : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  have hP := (GlobalTheory.Mem.Chr.splitsC_place (p := D.host.g k) (D.host.g_prime k) (D.nd.g_split k) w hw).2.2
  by_contra hn
  have hle : ∀ x ∈ w.asIdeal, D.host.conj • x ∈ w.asIdeal := by
    intro x hx
    by_contra hy
    refine hn ⟨x, hx, fun y e hy' => hy ?_⟩
    have : y = D.host.conj • x := Subtype.ext e
    rwa [← this]
  refine GlobalTheory.TypePlace.conj_ne_one D.host (hP _ ?_)
  have h1 : D.host.conj • w.asIdeal ≤ w.asIdeal := by
    intro y hy
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hy
    simpa using hle _ hy
  have hm : (D.host.conj • w.asIdeal).IsMaximal :=
    Ideal.map_isMaximal_of_equiv (MulSemiringAction.toRingEquiv _ (𝓞 D.host.E) D.host.conj) (hp := w.isMaximal)
  exact hm.eq_of_le w.isMaximal.ne_top h1

theorem mem_Ine_of_wild (D : D7) (w : PlE D.host) {σ} (hσ : σ ∈ wildSet D.nd (D.nd.plOm.1 w)) :
    σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w) := GlobalTheory.TameGenPowers.wild_mem_Ine hσ

end GlobalTheory.DepthZeroType
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitCharacterUnitValue
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TupleCharAtType

theorem natCast_notMem {E : Type} [Field E] [NumberField E] {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h : p ≠ q)
    {v : HeightOneSpectrum (𝓞 E)} (hv : ((p : ℕ) : 𝓞 E) ∈ v.asIdeal) : ((q : ℕ) : 𝓞 E) ∉ v.asIdeal := fun hv' => by
  obtain ⟨s, t, hst⟩ : IsCoprime (p : 𝓞 E) (q : 𝓞 E) := Nat.Coprime.cast ((Nat.coprime_primes hp hq).2 h)
  apply v.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hst]
  exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ hv) (v.asIdeal.mul_mem_left _ hv')

theorem isUnitAt_of_notMem {E : Type} [Field E] [NumberField E] {v : HeightOneSpectrum (𝓞 E)} (u : 𝓞 E)
    (hu : (u : E) ≠ 0) (hv : u ∉ v.asIdeal) : IsUnitAt v (atFin v (Units.mk0 (u : E) hu)) := by
  show Valued.v ((u : E) : v.adicCompletion E) = 1
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_eq_one_iff.2 hv

end GlobalTheory.TupleCharAtType
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocDZOfSplitReg
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.DepthZeroAssembly

open GlobalTheory.WeilDeligne (WD Weil ineIncl TeichmullerInertiaLabelCondition Wild Wild_le_Ine)
open GlobalTheory.SplitRead.BlockParam (charPol_lpChar_of_unr twistIrr)

section Local

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {B : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver B w} {g : ℕ} [Fact g.Prime]

theorem lab_lpChar_of_unr (τ : AlgebraicClosure (ZMod g) →* ℂ) (γ : G E Ω) (x χ : WD h) (hx : x.unr)
    (hd : χ.lpDim = 1) (u : ZMod g) (hχ : WD.lab τ γ χ = X - C u) :
    WD.lab τ γ (x.lpChar χ) = (X - C u) ^ x.lpDim := by
  have H : TeichmullerInertiaLabelCondition B w τ γ := by
    by_contra H
    rw [WD.lab_of_not H] at hχ
    have := congrArg natDegree hχ
    rw [natDegree_one, natDegree_X_sub_C] at this
    exact zero_ne_one this
  have htχ : WD.tame χ := WD.tame_of_natDegree_lab (by rw [hχ, natDegree_X_sub_C, hd])
  have hc1 : ∀ σ : Ine (F := E) B, (σ : G E Ω) ∈ Wild E B → χ.charPol (ineIncl h σ) = X - C 1 := by
    intro σ hσ
    have := (WD.tame_iff_inePol χ).1 htχ σ hσ
    rw [WD.inePol_of_mem_Ine _ σ.2, hd, pow_one] at this
    rw [C_1]; exact this
  have hdim : (x.lpChar χ).lpDim = x.lpDim := by
    obtain ⟨σ, hσ⟩ : ∃ σ : Ine (F := E) B, (σ : G E Ω) ∈ Wild E B := ⟨1, (Wild E B).one_mem⟩
    have h1 := charPol_lpChar_of_unr x χ hx σ 1 (hc1 σ hσ)
    rw [← WD.charPol_natDegree (x.lpChar χ) (ineIncl h σ), h1, natDegree_pow, natDegree_X_sub_C, mul_one]
  have ht : WD.tame (x.lpChar χ) := by
    rw [WD.tame_iff_inePol]
    intro σ hσ
    rw [WD.inePol_of_mem_Ine _ (Wild_le_Ine hσ), hdim,
      charPol_lpChar_of_unr x χ hx ⟨σ, Wild_le_Ine hσ⟩ 1 (hc1 ⟨σ, Wild_le_Ine hσ⟩ hσ), C_1]
  set p := χ.charPol (ineIncl h ⟨γ, H.2.1⟩) with hp
  have hpm : p.Monic := WD.charPol_monic _ _
  have hpd : p.natDegree = 1 := by rw [hp, WD.charPol_natDegree, hd]
  have hpe : p = X - C (-p.coeff 0) := by rw [map_neg, sub_neg_eq_add]; exact hpm.eq_X_add_C hpd
  have hχ' := (WD.lab_eq_iff_of_tame H htχ).1 hχ
  have hr1 := WD.rootsBar_X_sub_C_pow u 1
  rw [pow_one, one_nsmul] at hr1
  rw [WD.inePol_of_mem_Ine _ H.2.1, ← hp, hpe, roots_X_sub_C, hr1,
    Multiset.map_singleton, Multiset.singleton_inj] at hχ'
  rw [WD.lab_eq_iff_of_tame H ht, WD.inePol_of_mem_Ine _ H.2.1,
    charPol_lpChar_of_unr x χ hx ⟨γ, H.2.1⟩ (-p.coeff 0) (hpe ▸ rfl), roots_pow, roots_X_sub_C,
    WD.rootsBar_X_sub_C_pow, Multiset.map_nsmul, Multiset.map_singleton, hχ'.2]
  exact ⟨(monic_X_sub_C u).pow _, rfl⟩

end Local

end GlobalTheory.DepthZeroAssembly

namespace GlobalTheory.DepthZeroAssembly

open GlobalTheory.WeilDeligne (WD)
open GlobalTheory.SplitRead.BlockParam (twistIrr)

theorem locDZ_of_split_reg : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7), SplitLoc hL D → RegLoc hL D → LocDZ hL D := by
  intro hL D hS hR k v χ hχ u π ρ f ht hlab hser hsq hnr hx
  obtain ⟨π₁, π₂, hsph, e, y, hy1, hy2⟩ := hS k v χ hχ u π ρ f ht hlab hser hnr hx
  obtain ⟨hm1, hl1⟩ := hR k v π₁ ρ f hser hsq ⟨y, hy1, hy2⟩
  have L : RecLaws (rcAt hL D (D.naut.plGw k v)) :=
    (GlobalTheory.CuspRep.ParLaws.isRec_locRec hL (D.nd.plOm.2 (D.naut.plGw k v))).recLaws
  have e' : Nonempty (π.π.Equiv (GlobalTheory.SmGL.prod₂ π₁.π (twistIrr π₂ χ hχ).π)) := e
  have e1 := L.prod D.R.r D.R.t π₁ (twistIrr π₂ χ hχ) π e'
  have e2 := L.twist D.R.t χ (Irr.ofDet 1 χ hχ) π₂ (twistIrr π₂ χ hχ) ⟨.refl _⟩ ⟨.refl _⟩
  have hu := (L.sph _ π₂).2 hsph
  refine ⟨?_, ?_⟩
  · rw [e1, WD.monomial_sum_iff, e2, WD.monomial_char_iff _ _ (L.dim _ _)]
    exact ⟨hm1, WD.unr_mono0 _ hu⟩
  · unfold labAt at hl1 hlab ⊢
    rw [e1, WD.lab_lpSum, e2, lab_lpChar_of_unr _ _ _ _ hu (L.dim _ _) u hlab, hl1, L.dim]

end GlobalTheory.DepthZeroAssembly
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPotSemistableIndependentOfInducingEmbedding
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPotSemistableIndependentOfInducingEmbedding
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

noncomputable section

namespace GlobalTheory.Pst.PstBridge

open GlobalTheory.Pst GlobalTheory.Pst.BridgeParam Formalism.MainNotions.N Module

section Rank

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]

theorem rank_le_of_conj {K K' : FinExt l} {g : GQ l} {ρ : Representation LL ↥(GK K) V}
    {ρ' : Representation LL ↥(GK K') V}
    (hρ : ∀ (h : ↥(GK K)) (h' : ↥(GK K')), (h' : GQ l) = g * h * g⁻¹ → ρ' h' = ρ h)
    (hK : ∀ x, x ∈ K.1 ↔ g x ∈ K'.1) :
    Module.rank ↥(MaximalUnramifiedExtension l) (DpstUr P ρ) ≤ Module.rank ↥(MaximalUnramifiedExtension l) (DpstUr P ρ') := by
  have hρ' : ∀ (h' : ↥(GK K')) (h : ↥(GK K)), (h : GQ l) = g⁻¹ * h' * g⁻¹⁻¹ → ρ h = ρ' h' :=
    fun h' h hh => (hρ h h' (by rw [hh]; group)).symm
  have hK' : ∀ x, x ∈ K'.1 ↔ g⁻¹ x ∈ K.1 := fun x => by
    rw [hK, show g (g⁻¹ x) = x from g.apply_symm_apply x]
  let i : ↥(MaximalUnramifiedExtension l) → ↥(MaximalUnramifiedExtension l) := fun c => ⟨g c, (BridgeInd.mem_Kur_iff g _).1 c.2⟩
  have hi : Function.Surjective i := fun c =>
    ⟨⟨g⁻¹ c, (BridgeInd.mem_Kur_iff g _).2 (by rw [show g (g⁻¹ (c : Om l)) = c from g.apply_symm_apply _]; exact c.2)⟩,
      Subtype.ext (g.apply_symm_apply _)⟩
  let j : DpstUr P ρ →+ DpstUr P ρ' :=
    (toUr P ρ').toAddMonoidHom.comp ((conjD P hρ hK).toAddMonoidHom.comp (toUr P ρ).symm.toAddMonoidHom)
  have hj : Function.Injective j := by
    intro x y hxy
    have hx : ∀ z : ↥(Dpst P ρ), conjD P hρ' hK' (conjD P hρ hK z) = z := fun z =>
      Subtype.ext (by
        have := LinearMap.congr_fun (conjV_conjV_inv P (LL := LL) (V := V) g⁻¹) z.1
        rw [inv_inv] at this
        exact this)
    have := congrArg (conjD P hρ' hK') hxy
    exact (hx x).symm.trans (this.trans (hx y))
  refine rank_le_of_surjective_injective i j hi hj fun c x => ?_
  exact conjD_mulD P hρ hK c (i c) rfl x

end Rank

theorem isPstAt_indep_bridge : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (O O' : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] [CommRing O'] [Algebra ℤ_[l] O'] [TopologicalSpace O'] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (Bw' : LocBridge l E Ω (Dec (F := E) A) O'), GlobalTheory.Pst.Induces Bw → GlobalTheory.Pst.Induces Bw' → ∀ (a : ℕ) (r : ↥(Dec (F := E) A) →* GL (Fin a) (Om l)), Continuous (fun g => ((r g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) → GlobalTheory.Pst.IsPstAt P Bw r → GlobalTheory.Pst.IsPstAt P Bw' r := by
  intro l _ P AI _ E Ω _ _ _ _ _ A O O' _ _ _ _ _ _ Bw Bw' hj hj' a r _ hr
  obtain ⟨L₁, r₁, hm₁, hV₁⟩ := hr
  let L₂ : FinExt l := supExt L₁ Bw'.LL
  have h₁ : L₁.1 ≤ L₂.1 := le_sup_left
  have h₂ : Bw'.LL.1 ≤ L₂.1 := le_sup_right
  let r₂ := mapRep (IntermediateField.inclusion h₁).toRingHom r₁
  have hW := GlobalTheory.PstExt.isPst_enlarge P Bw h₁ r₁ hV₁
  obtain ⟨g, hg, hK⟩ := BridgeInd.exists_conj Bw Bw' hj hj'
  have hρ := BridgeInd.repE_conj Bw Bw' hg L₂ r₂
  refine ⟨L₂, r₂, ⟨h₂, ?_⟩, ?_⟩
  · rw [← hm₁.2]
    ext x i k
    rfl
  · have e1 := rank_le_of_conj P hρ hK
    have hρ' : ∀ (h' : ↥(GK Bw'.Kw)) (h : ↥(GK Bw.Kw)), (h : GQ l) = g⁻¹ * h' * g⁻¹⁻¹ →
        Bw.repE L₂ r₂ h = Bw'.repE L₂ r₂ h' :=
      fun h' h hh => (hρ h h' (by rw [hh]; group)).symm
    have hK' : ∀ x, x ∈ Bw'.Kw.1 ↔ g⁻¹ x ∈ Bw.Kw.1 := fun x => by
      rw [hK, show g (g⁻¹ x) = x from g.apply_symm_apply x]
    have e2 := rank_le_of_conj P hρ' hK'
    unfold IsPst at hW ⊢
    rw [← hW]
    exact le_antisymm e2 e1

end GlobalTheory.Pst.PstBridge
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPotSemistableIndependentOfInducingEmbeddingStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPotSemistable_independent_of_inducingEmbedding : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (O O' : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] [CommRing O'] [Algebra ℤ_[l] O'] [TopologicalSpace O'] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (Bw' : LocBridge l E Ω (Dec (F := E) A) O'), GlobalTheory.Pst.Induces Bw → GlobalTheory.Pst.Induces Bw' → ∀ (a : ℕ) (r : ↥(Dec (F := E) A) →* GL (Fin a) (Om l)), Continuous (fun g => ((r g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) → GlobalTheory.Pst.IsPstAt P Bw r → GlobalTheory.Pst.IsPstAt P Bw' r := by
  first | exact @GlobalTheory.Pst.PstBridge.isPstAt_indep_bridge | exact GlobalTheory.Pst.PstBridge.isPstAt_indep_bridge | (intros; apply GlobalTheory.Pst.PstBridge.isPstAt_indep_bridge <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGlobalIntegerCongrTameGeneratorCharacter
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGlobalIntegerCongrTameGeneratorCharacter
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ChiTameUnit

theorem exists_int_cong_tg : ∀ (D : D7) (k : Fin 2) (v : D.nd.PlG k), ∃ (u : 𝓞 D.host.E) (hu : (u : D.host.E) ≠ 0), u ∉ (D.naut.plGw k v).asIdeal ∧ ∃ (ϖ : 𝓞 D.host.E) (π : D.nd.Om), ϖ ∈ (D.naut.plGw k v).asIdeal ∧ ϖ ∉ (D.naut.plGw k v).asIdeal ^ 2 ∧ π ^ (normV (D.naut.plGw k v) - 1) = algebraMap D.host.E D.nd.Om (ϖ : D.host.E) ∧ (D.nd.plOm.1 (D.naut.plGw k v)).valuation (D.ntypes.tg k v π / π - algebraMap D.host.E D.nd.Om (u : D.host.E)) < 1 := by
  intro D k v
  set w := D.naut.plGw k v with hw
  set A := D.nd.plOm.1 w with hAdef
  have hA : IsPlaceOver A w := D.nd.plOm.2 w
  have : IsAlgClosed D.nd.Om := IsAlgClosure.isAlgClosed D.host.E
  have hp : (D.host.g k).Prime := D.host.g_prime k
  have hN : normV w = D.host.g k := GlobalTheory.TameLabels.normV_eq_of_split hp (D.nd.g_split k) (D.naut.plGw_over k v)
  have hgw : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal := D.naut.plGw_over k v
  have hn : 0 < normV w - 1 := by rw [hN]; have := hp.two_le; omega
  obtain ⟨ϖ, h1, h2⟩ := SetLike.exists_of_lt
    (Ideal.pow_lt_self w.asIdeal w.ne_bot w.isPrime.ne_top 2 le_rfl)
  obtain ⟨π, hπ⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap D.host.E D.nd.Om (ϖ : D.host.E)) hn
  have hϖ0 : ϖ ≠ 0 := by rintro rfl; exact h2 (zero_mem _)
  have h0 : π ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne', eq_comm, map_eq_zero] at hπ
    exact hϖ0 (by simpa using hπ)
  set ζ := D.ntypes.tg k v π / π with hζ
  have hζn : ζ ^ (normV w - 1) = 1 := by
    rw [hζ, div_pow, ← map_pow, hπ, AlgEquiv.commutes, ← hπ, div_self (pow_ne_zero _ h0)]
  have hv1 : A.valuation ζ = 1 := by
    have heq : (A.valuation ζ) ^ (normV w - 1) = (1 : A.ValueGroup) ^ (normV w - 1) := by
      rw [← map_pow, hζn, map_one, one_pow]
    exact pow_left_injective hn.ne' heq

  have hζA : ζ ∈ A := (A.valuation_le_one_iff ζ).mp hv1.le
  haveI hcp : CharP (IsLocalRing.ResidueField A) (D.host.g k) := by
    refine (CharP.charP_iff_prime_eq_zero hp).2 ?_
    rw [← map_natCast (IsLocalRing.residue A), IsLocalRing.residue_eq_zero_iff,
      ValuationSubring.valuation_lt_one_iff]
    have := (hA _).mpr hgw
    simpa using this
  haveI : Fact (D.host.g k).Prime := ⟨hp⟩
  set z := IsLocalRing.residue A ⟨ζ, hζA⟩ with hz
  have hzp : z ^ (D.host.g k) - z = 0 := by
    have e : (⟨ζ, hζA⟩ : A) ^ (normV w - 1) = 1 := Subtype.ext (by simpa using hζn)
    have e2 : z ^ (normV w - 1) = 1 := by rw [hz, ← map_pow, e, map_one]
    rw [hN] at e2
    have : z ^ (D.host.g k) = z := by
      rw [← Nat.sub_add_cancel hp.one_lt.le, pow_succ, e2, one_mul]
    rw [this, sub_self]
  have hmon : (X ^ (D.host.g k) - X : (ZMod (D.host.g k))[X]).Monic :=
    monic_X_pow_sub (by rw [degree_X]; exact_mod_cast hp.one_lt)
  have hroots := FiniteField.roots_X_pow_card_sub_X (ZMod (D.host.g k))
  rw [ZMod.card] at hroots
  have hprod := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmon (by
    rw [hroots, Polynomial.natDegree_X_pow_sub_X hp.one_lt, Finset.card_val, Finset.card_univ,
      ZMod.card])
  have hev := congrArg (fun P => (P.map (ZMod.castHom (dvd_refl _) (IsLocalRing.ResidueField A))).eval z) hprod
  simp only [Polynomial.map_multiset_prod, Multiset.map_map, Function.comp_def, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_C, Polynomial.map_pow, eval_multiset_prod, Multiset.map_map, eval_sub, eval_X, eval_C, eval_pow, hzp] at hev
  obtain ⟨a, -, hy0⟩ := Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp hev)

  have hcong : A.valuation (ζ - ((a.val : ℕ) : D.nd.Om)) < 1 := by
    have : (⟨ζ, hζA⟩ : A) - ((a.val : ℕ) : A) ∈ IsLocalRing.maximalIdeal A := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, ← hz, map_natCast, ZMod.natCast_val]
      simpa using hy0
    rw [ValuationSubring.valuation_lt_one_iff] at this
    simpa [-ZMod.natCast_val] using this
  have hu : ((a.val : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := by
    intro hm
    have h3 := (hA _).mpr hm
    simp only [map_natCast] at h3
    have h4 := Valuation.map_add_lt _ hcong h3
    rw [sub_add_cancel, hv1] at h4
    exact lt_irrefl _ h4
  refine ⟨((a.val : ℕ) : 𝓞 D.host.E), ?_, hu, ϖ, π, h1, h2, hπ, ?_⟩
  · intro h
    apply hu
    have : ((a.val : ℕ) : 𝓞 D.host.E) = 0 := by exact_mod_cast h
    rw [this]; exact zero_mem _
  · have e : algebraMap D.host.E D.nd.Om (((a.val : ℕ) : 𝓞 D.host.E) : D.host.E) = ((a.val : ℕ) : D.nd.Om) := by
      simp only [RingOfIntegers.coe_eq_algebraMap, map_natCast]
    rw [e]
    exact hcong

end GlobalTheory.ChiTameUnit

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGlobalIntegerCongrTameGeneratorCharacterStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_globalInteger_congr_tameGenerator_character : ∀ (D : D7) (k : Fin 2) (v : D.nd.PlG k), ∃ (u : 𝓞 D.host.E) (hu : (u : D.host.E) ≠ 0), u ∉ (D.naut.plGw k v).asIdeal ∧ ∃ (ϖ : 𝓞 D.host.E) (π : D.nd.Om), ϖ ∈ (D.naut.plGw k v).asIdeal ∧ ϖ ∉ (D.naut.plGw k v).asIdeal ^ 2 ∧ π ^ (normV (D.naut.plGw k v) - 1) = algebraMap D.host.E D.nd.Om (ϖ : D.host.E) ∧ (D.nd.plOm.1 (D.naut.plGw k v)).valuation (D.ntypes.tg k v π / π - algebraMap D.host.E D.nd.Om (u : D.host.E)) < 1 := by
  first | exact @GlobalTheory.ChiTameUnit.exists_int_cong_tg | exact GlobalTheory.ChiTameUnit.exists_int_cong_tg | (intros; apply GlobalTheory.ChiTameUnit.exists_int_cong_tg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOfOverTwo
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.MuUnrTie

theorem eq_of_over_two {E : Type} [Field E] [NumberField E] {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (v : HeightOneSpectrum (𝓞 E)) (h1 : ((p : ℕ) : 𝓞 E) ∈ v.asIdeal) (h2 : ((q : ℕ) : 𝓞 E) ∈ v.asIdeal) : p = q := by
  by_contra hne
  have hc : Nat.Coprime p q := (Nat.coprime_primes hp hq).2 hne
  obtain ⟨a, b, h⟩ := (Nat.isCoprime_iff_coprime.2 hc).map (Int.castRingHom (𝓞 E))
  simp only [eq_intCast, Int.cast_natCast] at h
  apply v.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← h]
  exact add_mem (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)

theorem unrAt_inv {E : Type} [Field E] [NumberField E] {χ : HChar E} {w : HeightOneSpectrum (𝓞 E)}
    (h : χ.UnrAt w) : (χ⁻¹).UnrAt w := by
  exact HChar.UnrAt.inv h

end GlobalTheory.MuUnrTie
end
