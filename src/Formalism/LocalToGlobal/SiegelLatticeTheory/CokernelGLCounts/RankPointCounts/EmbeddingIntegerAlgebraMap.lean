module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarSteps
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.SecondCoordsAdaptedColumn
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LeadingMinorIntegrality
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteDimensionalDefiniteUnitaryLevelForms

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.EmbeddingIntegerAlgebraMap
noncomputable section

open scoped Classical
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc

namespace Formalism.L2.SG.Pf.LocalDenominators

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem conjF_invol (e : D.host.E) : D.conjF (D.conjF e) = e := by
  rw [D.conjF_eq, D.conjF_eq]
  exact D.embE.injective (by rw [D.embE_conj, D.embE_conj, star_star])

theorem conjF_fix (y : D.host.E) (h : D.conjF y = y) : y ∈ (algebraMap D.host.F D.host.E).range := by
  rw [D.conjF_eq] at h
  have hy := (Formalism.BasicNotions.Examples₂.conj_eq_self_iff D.host y).1 h
  exact ⟨⟨y, hy⟩, rfl⟩

theorem iE_mem_O_iff_D (p : PlF D) (x : D.host.E) :
    (D.s.atP p).ιE x ∈ (D.s.atP p).O ↔
      ∃ s : 𝓞 D.host.F, s ∉ p.asIdeal ∧ IsIntegral ℤ (algebraMap D.host.F D.host.E (s : D.host.F) * x) :=
  iE_mem_O_iff (D.s.atP p) conjF_invol conjF_fix x

theorem baseChange_smul₂ (p : PlF D) (c : D.host.E) (x : (VS D).V) :
    baseChange₂ D p (c • x : (VS D).V) = ((D.s.atP p).ιE c • (baseChange₂ D p x : Vp D p) : Vp D p) := by
  funext i
  show (D.s.atP p).ιE ((VS D).frame.repr (c • x) i) =
    (D.s.atP p).ιE c * (D.s.atP p).ιE ((VS D).frame.repr x i)
  rw [LinearEquiv.map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul]

def chat (p : PlF D) (w : (VS D).V →ₗ[D.host.E] D.host.E) (v : Vp D p) : (D.s.atP p).Ep :=
  ∑ j, (D.s.atP p).ιE (w ((VS D).frame j)) * v j

theorem chat_bcP (p : PlF D) (w : (VS D).V →ₗ[D.host.E] D.host.E) (y : (VS D).V) :
    chat p w (baseChange₂ D p y) = (D.s.atP p).ιE (w y) := by
  unfold chat
  conv_rhs => rw [← (VS D).frame.sum_repr y]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LinearMap.map_smul, smul_eq_mul, map_mul, mul_comm]
  rfl

theorem chat_add (p : PlF D) (w : (VS D).V →ₗ[D.host.E] D.host.E) (v v' : Vp D p) :
    chat p w (v + v') = chat p w v + chat p w v' := by
  simp only [chat, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem chat_smul (p : PlF D) (w : (VS D).V →ₗ[D.host.E] D.host.E) (a : (D.s.atP p).Ep) (v : Vp D p) :
    chat p w (a • v) = a * chat p w v := by
  simp only [chat, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem chat_zero (p : PlF D) (w : (VS D).V →ₗ[D.host.E] D.host.E) : chat p w 0 = 0 := by
  simp [chat]

theorem iE_t_inv_mem (p : PlF D) {t : 𝓞 D.host.F} (ht : t ∉ p.asIdeal) :
    algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (t : D.host.F))⁻¹ ∈ (D.s.atP p).O := by
  apply alg_mem_O
  rw [Valuation.mem_integer_iff, map_inv₀, iF_unit _ ht, inv_one]

theorem iF_t_ne (p : PlF D) {t : 𝓞 D.host.F} (ht : t ∉ p.asIdeal) : (D.s.atP p).ιF (t : D.host.F) ≠ 0 := by
  have h0 : t ≠ 0 := by
    rintro rfl
    exact ht p.asIdeal.zero_mem
  exact (map_ne_zero _).mpr (by simpa using h0)

section Dict

variable (Zd : LocDat D) (p : PlF D)

instance finVS : FiniteDimensional D.host.E (VS D).V := Module.Finite.of_basis (VS D).frame

theorem oE_smul (c : 𝓞 D.host.E) (x : (VS D).V) : c • x = ((c : D.host.E)) • x := by
  first
  | rfl
  | exact (algebraMap_smul D.host.E c x).symm

theorem oF_coe (t : 𝓞 D.host.F) :
    ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t : 𝓞 D.host.E) : D.host.E) = algebraMap D.host.F D.host.E (t : D.host.F) := by
  first
  | rfl
  | simp
  | exact (IsScalarTower.algebraMap_apply (𝓞 D.host.F) D.host.F D.host.E t).symm

theorem hO : (Zd.M p).L.O = (D.s.atP p).O := by
  exact (Zd.agree p).2.2.2.1

theorem smul_mem_localLattice {Λ : Submodule (𝓞 D.host.E) (VS D).V} {a : (D.s.atP p).Ep} (ha : a ∈ (D.s.atP p).O)
    {v : Vp D p} (hv : v ∈ lattice₂ D Zd.M p Λ) : a • v ∈ lattice₂ D Zd.M p Λ := by
  have ha' : a ∈ (Zd.M p).L.O := by
    rw [hO]
    exact ha
  exact (lattice₂ D Zd.M p Λ).smul_mem ⟨a, ha'⟩ hv

theorem coord_int {b : Module.Basis (Fin (Module.finrank D.host.E (VS D).V)) D.host.E (VS D).V} (i : Fin _)
    {z : (VS D).V} (hz : z ∈ Submodule.span (𝓞 D.host.E) (Set.range b)) : IsIntegral ℤ (b.coord i z) := by
  induction hz using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, rfl⟩ := hy
    rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs
    · exact isIntegral_one
    · exact isIntegral_zero
  | zero => simp [isIntegral_zero]
  | add x y _ _ hx hy =>
    rw [map_add (f := _)]
    exact hx.add hy
  | smul c y _ hy =>
    rw [oE_smul, map_smul, smul_eq_mul]
    exact (RingOfIntegers.isIntegral_coe c).mul hy

theorem baseChangeAt_mem_localLattice_iff {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : Submodule.IsFullLattice D.host.E Λ) (x : (VS D).V) :
    baseChange₂ D p x ∈ lattice₂ D Zd.M p Λ ↔ x ∈ Formalism.HermitianLattices.Ext.L3.locF p.asIdeal Λ := by
  haveI := p.isPrime
  constructor
  · intro hx
    obtain ⟨b, hbΛ, hbloc⟩ := Formalism.HermitianLattices.Ext.L3.LocalSpans.exists_basis_locF hΛ p.isMaximal
    have key : ∀ i, (D.s.atP p).ιE (b.coord i x) ∈ (D.s.atP p).O := by
      intro i
      have hcall : ∀ v ∈ lattice₂ D Zd.M p Λ, chat p (b.coord i) v ∈ (D.s.atP p).O := by
        intro v hv
        induction hv using Submodule.span_induction with
        | mem v hv =>
          obtain ⟨y, hy, rfl⟩ := hv
          rw [chat_bcP]
          have hy' : y ∈ Formalism.HermitianLattices.Ext.L3.locF p.asIdeal (Submodule.span (𝓞 D.host.E) (Set.range b)) := by
            rw [hbloc]; exact (Formalism.HermitianLattices.Ext.L3.LocalSpans.mem_locF p.asIdeal Λ y).2 ⟨1, fun h => p.isPrime.ne_top
              ((Ideal.eq_top_iff_one _).2 h), by simpa using hy⟩
          obtain ⟨t, ht, hty⟩ := (Formalism.HermitianLattices.Ext.L3.LocalSpans.mem_locF p.asIdeal _ y).1 hy'
          have hint := coord_int i hty
          rw [oE_smul, oF_coe, map_smul, smul_eq_mul] at hint
          have h1 := iE_int (D.s.atP p) hint
          rw [map_mul, iE_alg] at h1
          have e : (D.s.atP p).ιE (b.coord i y) =
              algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (t : D.host.F))⁻¹ *
              (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (t : D.host.F)) * (D.s.atP p).ιE (b.coord i y)) := by
            rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ (iF_t_ne p ht), map_one, one_mul]
          rw [e]
          exact (D.s.atP p).O.mul_mem (iE_t_inv_mem p ht) h1
        | zero => rw [chat_zero]; exact (D.s.atP p).O.zero_mem
        | add a c _ _ ha hc => rw [chat_add]; exact (D.s.atP p).O.add_mem ha hc
        | smul a v _ hv =>
          have ha : (a : (D.s.atP p).Ep) ∈ (D.s.atP p).O := by rw [← hO Zd p]; exact a.2
          have e : a • v = (a : (D.s.atP p).Ep) • v := rfl
          rw [e, chat_smul]
          exact (D.s.atP p).O.mul_mem ha hv
      have hc := hcall _ hx
      rwa [chat_bcP] at hc
    have hint : ∀ i, ∃ s : 𝓞 D.host.F, s ∉ p.asIdeal ∧
        IsIntegral ℤ (algebraMap D.host.F D.host.E (s : D.host.F) * b.coord i x) := fun i =>
      (iE_mem_O_iff_D p _).1 (key i)
    choose s hs hsi using hint
    set t : 𝓞 D.host.F := ∏ i, s i with htdef
    have ht : t ∉ p.asIdeal := by
      rw [htdef]
      intro h
      obtain ⟨i, -, hi⟩ := Ideal.IsPrime.prod_mem_iff.1 h
      exact hs i hi
    have hsF : ∀ j, IsIntegral ℤ (algebraMap D.host.F D.host.E (s j : D.host.F)) := fun j => by
      have := (s j).2
      exact (show IsIntegral ℤ ((s j : D.host.F)) from (s j).2).map (algebraMap D.host.F D.host.E).toIntAlgHom
    have hT : ∀ i, IsIntegral ℤ (algebraMap D.host.F D.host.E (t : D.host.F) * b.coord i x) := by
      intro i
      have e : algebraMap D.host.F D.host.E (t : D.host.F) =
          (∏ j ∈ Finset.univ.erase i, algebraMap D.host.F D.host.E (s j : D.host.F)) *
            algebraMap D.host.F D.host.E (s i : D.host.F) := by
        show algebraMap D.host.F D.host.E (algebraMap (𝓞 D.host.F) D.host.F t) = _
        rw [htdef, map_prod, map_prod, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
      rw [e, mul_assoc]
      refine IsIntegral.mul ?_ (hsi i)
      exact Finset.prod_induction _ (fun z => IsIntegral ℤ z) (fun a c ha hc => ha.mul hc) isIntegral_one
        (fun j _ => hsF j)
    have hx' : x ∈ Formalism.HermitianLattices.Ext.L3.locF p.asIdeal (Submodule.span (𝓞 D.host.E) (Set.range b)) := by
      refine (Formalism.HermitianLattices.Ext.L3.LocalSpans.mem_locF p.asIdeal _ x).2 ⟨t, ht, ?_⟩
      rw [oE_smul, oF_coe]
      have ex : x = ∑ i, b.repr x i • b i := (b.sum_repr x).symm
      rw [ex, Finset.smul_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [smul_smul]
      have hTi : IsIntegral ℤ (algebraMap D.host.F D.host.E (t : D.host.F) * b.repr x i) := hT i
      have hmem := Submodule.smul_mem (Submodule.span (𝓞 D.host.E) (Set.range b)) (⟨_, hTi⟩ : 𝓞 D.host.E)
        (Submodule.subset_span ⟨i, rfl⟩ : b i ∈ Submodule.span (𝓞 D.host.E) (Set.range b))
      convert hmem using 1
      exact (oE_smul (⟨_, hTi⟩ : 𝓞 D.host.E) (b i)).symm
    rwa [hbloc] at hx'
  · intro hx
    obtain ⟨t, ht, htx⟩ := (Formalism.HermitianLattices.Ext.L3.LocalSpans.mem_locF p.asIdeal Λ x).1 hx
    have h1 : baseChange₂ D p (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t • x) ∈ lattice₂ D Zd.M p Λ :=
      Submodule.subset_span ⟨_, htx, rfl⟩
    rw [oE_smul, oF_coe, baseChange_smul₂, iE_alg] at h1
    have e : baseChange₂ D p x = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (t : D.host.F))⁻¹ •
        (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (t : D.host.F)) • baseChange₂ D p x) := by
      rw [smul_smul, ← map_mul, inv_mul_cancel₀ (iF_t_ne p ht), map_one, one_smul]
    rw [e]
    exact smul_mem_localLattice Zd p (iE_t_inv_mem p ht) h1

end Dict

end Formalism.L2.SG.Pf.LocalDenominators
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXRed
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.LocOpenHolds
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ReductionImageEveryPlace
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ReductionImageOfBasis
noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm MassDataIdxRed MassDataIdxSpl Matrix
  MassDataIdxFrA
open scoped TensorProduct

section Loc

variable {D : D7} (X : HidaSetting D) (p : TypX X)

theorem oEpSplit_holds (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p) (hθ : IsSplitEquiv X p θ) :
    OEpSplit X p θ := by
  have hone : θ.symm (1, 1) = 1 := by rw [Prod.mk_one_one, map_one]
  have hsub : ∀ a b : FpX X p × FpX X p, θ.symm (a - b) = θ.symm a - θ.symm b := fun a b => map_sub _ _ _
  have hm : 1 - epsP X p ∈ OEp X p := imA_OEp_sub X p (imA_OEp_one X p) (imA_eps_mem X p)
  rcases PIW.MassDataColumns.theta_eps_cases X p θ hθ with h | h
  · have e1 : θ.symm (1, 0) = epsP X p := by rw [← h, AlgEquiv.symm_apply_apply]
    have e2 : θ.symm (0, 1) = 1 - epsP X p := by
      rw [← hone, ← e1, ← hsub]; congr 1; ext <;> simp
    exact ⟨e1 ▸ imA_eps_mem X p, e2 ▸ hm⟩
  · have e1 : θ.symm (0, 1) = epsP X p := by rw [← h, AlgEquiv.symm_apply_apply]
    have e2 : θ.symm (1, 0) = 1 - epsP X p := by
      rw [← hone, ← e1, ← hsub]; congr 1; ext <;> simp
    exact ⟨e2 ▸ hm, e1 ▸ imA_eps_mem X p⟩

def StAdaptBasisA : Prop :=
  ∃ θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p, IsSplitEquiv X p θ ∧
    ∃ Q : GL (IdxD D) (FpX X p), LatBasis X p θ (reindex₂ X p Q) ∧ AdaptA X p θ Q

theorem reduction_image_of_basis (hb : AdBridgeIso X.B.I) (h : StAdaptBasisA X p) : LevelReductionImage X hb p := by
  obtain ⟨θ, hθ, Q, hL, hA⟩ := h
  exact reduction_image_of_adapted_mod X p hb latCoreX_holds ⟨θ, hθ, oEpSplit_holds X p θ hθ, Q, hL, hA⟩

end Loc

end MassDataIdxSteps
end
end

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge

theorem stAdaptBasisA_holds {D : D7} (X : HidaSetting D) (p : TypX X) : StAdaptBasisA X p :=
  adaptA_holds X p

theorem reduction_image_every_place {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (p : TypX X) : LevelReductionImage X hb p :=
  reduction_image_of_basis X p hb (stAdaptBasisA_holds X p)

end MassDataIdxSteps
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.MassDataIndicesOfSteps
noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
open scoped ENNReal

theorem massDataIndices_of (hA : MeasAAll) (hB : MeasBAll) :
    ∀ {D : Formalism.BasicNotions.D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I)
      (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf) (u u' : D.what₂.Word)
      (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (L : Formalism.L2.SG.TypedSets.LocIn (Formalism.L2.SG.TypedSets.TypX X))
      (A : Formalism.L2.SG.TypedSets.AnIn), Formalism.L2.SG.TypedSets.InIndicesAt X hb hK FdN FdN' u u' X0 L A := by
  intro D X hb hK FdN FdN' u u' X0 L A hX p
  obtain ⟨i, hi, hi0, hμi⟩ := hA X hb hK FdN FdN' u u' hX p
  obtain ⟨j, hj, hj0, hμj, hB0, hBt⟩ := hB X hb hK FdN FdN' u u' hX p
  refine ⟨?_, ?_⟩
  · show (X.measG.μGv p.1 (KvX X p)).toReal =
      (ggC D.R.rS D.R.k (gOf p) : ℝ) / ((nnC D.R.rS D.R.k (gOf p) : ℝ) * (ukC D.R.k (gOf p) : ℝ)) *
        (X.measG.μGv p.1 (KppX X hb p)).toReal
    have h1 : (muP X p (KvX X p)).toReal = (i : ℝ) * (muP X p (KppX X hb p)).toReal := by
      rw [hμi, ENNReal.toReal_mul, ENNReal.toReal_natCast]
    rw [← hi, mul_div_assoc, div_self hi0, mul_one]
    exact h1
  · show (X.measG.μGv p.1 (KnatX X u p)).toReal / (X.measG.μGv p.1 (KvX X p)).toReal =
      (glkC D.R.k (gOf p) : ℝ) * (nnC D.R.rS D.R.k (gOf p) : ℝ) / (ggC D.R.rS D.R.k (gOf p) : ℝ)
    have h1 : (muP X p (KvX X p)).toReal = (j : ℝ) * (muP X p (KnatX X u p)).toReal := by
      rw [hμj, ENNReal.toReal_mul, ENNReal.toReal_natCast]
    have hpos : (muP X p (KnatX X u p)).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hB0, hBt⟩
    show (muP X p (KnatX X u p)).toReal / (muP X p (KvX X p)).toReal = _
    rw [h1, ← hj]
    rcases eq_or_ne (j : ℝ) 0 with h0 | h0
    · simp [h0]
    · rw [mul_comm (j : ℝ) (muP X p (KnatX X u p)).toReal, mul_comm (j : ℝ), div_mul_eq_div_div,
        div_self hpos, div_mul_eq_div_div, div_self hj0]

def LocAll : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (_hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
    (u u' : D.what₂.Word), HypX X hb FdN FdN' u u' → ∀ p : TypX X,
      StTop X p ∧ StK X p ∧ StRed X p ∧ StImA X hb p ∧ StImB X u p

theorem massDataIndices_of_haarIdx_redIdx_locAll (hH : HaarIdx) (hR : RedIdx) (hL : LocAll) :
    ∀ {D : Formalism.BasicNotions.D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I)
      (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf) (u u' : D.what₂.Word)
      (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (L : Formalism.L2.SG.TypedSets.LocIn (Formalism.L2.SG.TypedSets.TypX X))
      (A : Formalism.L2.SG.TypedSets.AnIn), Formalism.L2.SG.TypedSets.InIndicesAt X hb hK FdN FdN' u u' X0 L A :=
  massDataIndices_of
    (fun X hb hK FdN FdN' u u' hX p =>
      let h := hL X hb hK FdN FdN' u u' hX p
      measA_of X hb hH hR p h.1 h.2.1 h.2.2.1 h.2.2.2.1)
    (fun X hb hK FdN FdN' u u' hX p =>
      let h := hL X hb hK FdN FdN' u u' hX p
      measB_of X hH hR u p h.1 h.2.1 h.2.2.1 h.2.2.2.2)

theorem massDataIndices_of_locAll (hL : LocAll) :
    ∀ {D : Formalism.BasicNotions.D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I)
      (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf) (u u' : D.what₂.Word)
      (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (L : Formalism.L2.SG.TypedSets.LocIn (Formalism.L2.SG.TypedSets.TypX X))
      (A : Formalism.L2.SG.TypedSets.AnIn), Formalism.L2.SG.TypedSets.InIndicesAt X hb hK FdN FdN' u u' X0 L A := by
  have hH : HaarIdx := by
    exact haarIdx
  have hR : RedIdx := by
    exact redIdx
  intro D X
  exact massDataIndices_of_haarIdx_redIdx_locAll hH hR hL X

def LocOpen : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (_hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
    (u u' : D.what₂.Word), HypX X hb FdN FdN' u u' → ∀ p : TypX X,
      StK X p ∧ StRed X p ∧ StImA X hb p ∧ StImB X u p

theorem massDataIndices_of_locOpen (hL : LocOpen) :
    ∀ {D : Formalism.BasicNotions.D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I)
      (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf) (u u' : D.what₂.Word)
      (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (L : Formalism.L2.SG.TypedSets.LocIn (Formalism.L2.SG.TypedSets.TypX X))
      (A : Formalism.L2.SG.TypedSets.AnIn), Formalism.L2.SG.TypedSets.InIndicesAt X hb hK FdN FdN' u u' X0 L A := by
  exact massDataIndices_of_locAll (fun X hb hK FdN FdN' u u' hX p => ⟨stTop X p, hL X hb hK FdN FdN' u u' hX p⟩)

end MassDataIdxSteps
end
end

namespace MassDataIdxSteps

theorem locOpen_holds : LocOpen := fun X hb _hK _ _ u _ _ p =>
  ⟨stK_holds X p, stRed_of_embP X p (embP_holds X p), stImA_of X hb p (reduction_image_every_place X hb p),
    stImB_of_adaptQ X u p (stAdaptQ_holds X hb u p)⟩

end MassDataIdxSteps
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.MassDataIndices
theorem local_indices_at_instance : ∀ {D : Formalism.BasicNotions.D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf) (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (L : Formalism.L2.SG.TypedSets.LocIn (Formalism.L2.SG.TypedSets.TypX X)) (A : Formalism.L2.SG.TypedSets.AnIn), Formalism.L2.SG.TypedSets.InIndicesAt X hb hK FdN FdN' u u' X0 L A :=
  MassDataIdxSteps.massDataIndices_of_locOpen MassDataIdxSteps.locOpen_holds
end

namespace Formalism.L2.SG.Pf.MassDataX

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets

theorem stK_holds {D : D7} (X : HidaSetting D) (p : TypX X) : MassDataIdxSteps.StK X p :=
  MassDataIdxSteps.stK_holds X p

theorem stRed_holds {D : D7} (X : HidaSetting D) (p : TypX X) : MassDataIdxSteps.StRed X p :=
  MassDataIdxSteps.stRed_of_embP X p (MassDataIdxSteps.embP_holds X p)

theorem stImA_holds {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (p : TypX X) :
    MassDataIdxSteps.StImA X hb p :=
  MassDataIdxSteps.stImA_of X hb p (MassDataIdxSteps.reduction_image_every_place X hb p)

theorem stImB_holds {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (p : TypX X) :
    MassDataIdxSteps.StImB X u p :=
  MassDataIdxSteps.stImB_of_adaptQ X u p (MassDataIdxSteps.stAdaptQ_holds X hb u p)

theorem inIndicesAt_holds :
    ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
      (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (L : LocIn (TypX X)) (A : AnIn),
      InIndicesAt X hb hK FdN FdN' u u' X0 L A :=
  local_indices_at_instance

end Formalism.L2.SG.Pf.MassDataX
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CanonicalAnalyticData
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.TypedSets
  Formalism.L2.SG.MassDataConc Formalism.L2.SG.LocVol

namespace Formalism.L2.SG.NGAnalytic.MassDataLemmas

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Inst

variable {D : D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (Y : Full X) (u u' : D.what₂.Word)
  (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) (sd C Th : ℝ)
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
  (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
  (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)

abbrev anY : AnIn :=
  anOf (Y.tO u u') (Formalism.L2.SG.MassDataConc.kapN D * Formalism.L2.SG.RealObj.DisintegrationConstant X u u' 1) (Formalism.L2.SG.RealObj.degX X)
    ((locOf X u u' ψ).volZZ / (((locOf X u u' ψ).localVolumeArchimedean * ∏ p, (locOf X u u' ψ).localVolumeAtPlace p) * (locOf X u u' ψ).volPP) *
      ((locOf X u u' ψ).volPP * (Formalism.L2.SG.RealObj.IntC X u u' 1 / Formalism.L2.SG.MassDataConc.kapN D)))
    (Formalism.L2.SG.RealObj.IntC X u u' 1 / Formalism.L2.SG.MassDataConc.kapN D) (Formalism.L2.SG.RealObj.IntOO X u u' 1) sd C Th D.R.rS
    (Fintype.card (InfinitePlace X.B.I.F))
    ⟨KVOf X u u' vR Q (VConstants X u u' 1 i0 i0' (Y.FN u) (Y.FN u') νq),
      KtopVOf X u u' Y.M Y.δ (VConstants X u u' 1 i0 i0' (Y.FN u) (Y.FN u') νq)⟩

def FrameVolAt : Prop :=
  (bk X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq).unitLevelVolume / (bk X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq).volZZ =
    (2 * D.host.v) ^ (((D.R.f * (D.R.rS + 1) * (8 * D.R.rS ^ 2 + 10 * D.R.rS + 3) : ℕ) : ℝ) / 3) *
      (X.B.g : ℝ) ^ (D.R.f * (D.R.rS + 1) * (2 * D.R.rS + 3))

theorem kapN_pos (hg : 0 < (X.B.g : ℝ)) : 0 < Formalism.L2.SG.MassDataConc.kapN D := by
  unfold Formalism.L2.SG.MassDataConc.kapN
  have hr : 0 < D.host.rdE := by
    unfold Formalism.BasicNotions.Host.rdE
    apply Real.rpow_pos_of_pos
    exact abs_pos.2 (Int.cast_ne_zero.2 (NumberField.discr_ne_zero _))
  have hgS : 0 < (Formalism.MainNotions.S.Lat.gS D : ℝ) := by
    unfold Formalism.MainNotions.S.Lat.gS
    first
      | exact Nat.cast_pos.2 (Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos)
      | exact Nat.cast_pos.2 (Nat.mul_pos D.host.g_prime.1.pos D.host.g_prime.2.pos)
      | exact Nat.cast_pos.2 (Nat.mul_pos (D.host.g_prime 0).one_lt.le (D.host.g_prime 1).one_lt.le)
  positivity

theorem massDataValid_bk_of {large₂ : SizeData₂ D} {Cg cb Cw cT CT C0 C' Cl : ℝ} (hc : Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u')
    (hrd : 0 < 2 * D.host.v) (hg : 0 < (X.B.g : ℝ)) (hT : MassDataTie X hb X0 ψ)
    (hLS : InLevelSAt X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 (locOf X u u' ψ) (anY X Y u u' ψ sd C Th vR Q i0 i0' νq))
    (hMs : InMassesAt X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 (locOf X u u' ψ) (anY X Y u u' ψ sd C Th vR Q i0 i0' νq))
    (hCol : InColumnsAt X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 (locOf X u u' ψ) (anY X Y u u' ψ sd C Th vR Q i0 i0' νq))
    (hInd : InIndicesAt X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 (locOf X u u' ψ) (anY X Y u u' ψ sd C Th vR Q i0 i0' νq))
    (hVol : InVolumesAt X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 (locOf X u u' ψ) (anY X Y u u' ψ sd C Th vR Q i0 i0' νq))
    (hKpp : KppVolAt X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 (locOf X u u' ψ) (anY X Y u u' ψ sd C Th vR Q i0 i0' νq))
    (hTy : InTypedC X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') sd C Th vR Q Y.M Y.δ i0 i0' νq)
    (hPC : ProdConv X u u' ψ) (hPr : PrimX X u) (hPr' : PrimX X u') (hKap : KapX X u u')
    (hNu : Formalism.L2.SG.RealObj.InNuX X u u' 1) (hInf : Formalism.L2.SG.RealObj.InInfinityX X u u' 1)
    (hPos : (bk X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq).Pos)
    (hFV : FrameVolAt X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq) :
    ∃ Irat Ire : ℝ, MassDataAdmissible X Y u u' (bk X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq) Irat Ire := by
  obtain ⟨hM, hψ, hStd, hMC, hLC, -, hdet⟩ := hT
  have hH : HypX X hb (Y.FN u) (Y.FN u') u u' := ⟨hM, hc.2.2.1, Y.FN_fund u, Y.FN_fund u'⟩
  have hk := kapN_pos X hg
  have hDst : (bk X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq).Dstar = DstC X :=
    Formalism.L2.SG.IntegralApproximation.MassDataDstarX_holds X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') sd C Th vR Q Y.M Y.δ i0 i0' νq
      (locOf X u u' ψ) (anY X Y u u' ψ sd C Th vR Q i0 i0' νq) hH hKpp
  set B := bk X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq with hB
  have hCoo : 0 ≤ Formalism.L2.SG.RealObj.DisintegrationConstant X u u' 1 := by
    unfold Formalism.L2.SG.RealObj.DisintegrationConstant
    split_ifs with h
    · exact h.choose_spec.1.le
    · exact le_rfl
  have hdeg : 0 < B.deg := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := hPos
    exact h
  have hNI : PN.NormInputs B := by
    refine ⟨hPos, rfl, ?_, ?_, ?_, hLS hH, hMs hH, hCol hH, ?_, ?_, hInd hH⟩
    · show Formalism.L2.SG.RealObj.IntOO X u u' 1 =
        Formalism.L2.SG.MassDataConc.kapN D * Formalism.L2.SG.RealObj.DisintegrationConstant X u u' 1 *
          (Formalism.L2.SG.RealObj.IntC X u u' 1 / Formalism.L2.SG.MassDataConc.kapN D)
      unfold Formalism.L2.SG.RealObj.IntOO Formalism.L2.SG.RealObj.IntC
      rw [hNu, ENNReal.toReal_mul, ENNReal.toReal_ofReal hCoo]
      field_simp
    · show Formalism.L2.SG.RealObj.IntOO X u u' 1 ≤ 1 / Formalism.L2.SG.RealObj.degX X
      have hd : 0 < Formalism.L2.SG.RealObj.degX X := hdeg
      exact ENNReal.toReal_le_of_le_ofReal (by positivity) hInf.2.2
    · exact inVolumes_of_compat X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 (locOf X u u' ψ)
        (anY X Y u u' ψ sd C Th vR Q i0 i0' νq) hVol hH ⟨ψ, hψ, hStd, hMC⟩ hdet
    · exact inOrdinary_bCF X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') sd C Th vR Q Y.M Y.δ i0 i0' νq hPC
    · exact hTy hH hPC (locTieX_of X ψ u (hLC u) hPr) (locTieX_of X ψ u' (hLC u') hPr')
        (typFacts_of X u u' (Formalism.L2.SG.Pf.gSplitX_holds X) (tCongX X u u') hKap)
  have hLam : 0 < PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f *
      (2 * D.host.v) ^ (((D.R.f * D.R.rS * (D.R.rS + 1) * (8 * D.R.rS + 10) : ℕ) : ℝ) / 3) := by
    unfold PN.abelian₂
    exact mul_pos (pow_pos hrd _) (Real.rpow_pos_of_pos hrd _)
  refine ⟨(B.c0 * B.c0')⁻¹ * B.IntC / 2 ^ (D.R.f * (D.R.rS + 1)),
    (B.c0 * B.c0')⁻¹ * B.IntC / 2 ^ (D.R.f * (D.R.rS + 1)) /
      (PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f *
        (2 * D.host.v) ^ (((D.R.f * D.R.rS * (D.R.rS + 1) * (8 * D.R.rS + 10) : ℕ) : ℝ) / 3)), ?_, ?_, hNI, ?_⟩
  · exact Formalism.L2.SG.IntegralApproximation.Gam1TieC_holds X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ sd C Th vR Q Y.M Y.δ i0 i0' νq Y
  · show B.d * B.d' / B.Dstar = duC X Y u * duC X Y u' / DstC X
    rw [hDst]
    rfl
  · have hL1 : PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f ≠ 0 := by
      unfold PN.abelian₂; exact (pow_pos hrd _).ne'
    have hL2 : (2 * D.host.v) ^ (((D.R.f * D.R.rS * (D.R.rS + 1) * (8 * D.R.rS + 10) : ℕ) : ℝ) / 3) ≠ 0 :=
      (Real.rpow_pos_of_pos hrd _).ne'
    refine ⟨hrd, hg, hFV, ?_, ?_⟩
    · field_simp
    · field_simp

end Inst

section Closed

def pairSys0 {D : D7} (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂ :=
  ⟨Empty, Empty.elim, Empty.elim, fun p => p.elim, fun p => p.elim, fun _ => False⟩

def idx0 (D : D7) : Fin D.R.k := ⟨0, by have := D.R.m_add_three_le_k; omega⟩

abbrev bk0 {D : D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (Y : Full X) (u u' : D.what₂.Word)
    (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) :
    S3.MassData (TypX X) :=
  bk X hb Y u u' X0 ψ 0 0 1 (F0 := X.Fu u) (what₂ := Y.what₂ u) (fun _ => 0) (pairSys0 u u' (X.Fu u) (Y.what₂ u))
    (fun _ => idx0 D) (fun _ => idx0 D) (fun _ => 0)

abbrev canonicalAnalyticData {D : D7} (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) : AnIn :=
  anY X Y u u' ψ 0 0 1 (F0 := X.Fu u) (what₂ := Y.what₂ u) (fun _ => 0) (pairSys0 u u' (X.Fu u) (Y.what₂ u))
    (fun _ => idx0 D) (fun _ => idx0 D) (fun _ => 0)

def OnTied (P : ∀ (D : D7) (X : HidaSetting D), Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I → Full X → D.what₂.Word → D.what₂.Word →
    (Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) → AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ → Prop) : Prop :=
  ∀ (Cg cb Cw cT CT C0 C' Cl : ℝ) (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
    Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
    ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
      (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ), MassDataTie X hb X0 ψ → P D X hb Y u u' X0 ψ

end Closed

end Formalism.L2.SG.NGAnalytic.MassDataLemmas
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.BwdPairOfTermBeta
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Saturated

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open BwdCut

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

variable (u u' F0 what₂)

def BwdTerm' : Prop :=
  CtxP u u' F0 what₂ →
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    ∀ (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
      (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
      (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
      StarHyp Zd γ Z F'₂ φ φ' →
      ∀ Λ₂ ∈ GlobSet Zd γ F'₂ φ φ',
        (∃ n ∈ unipotentFrameFixers F0, (n : (VS D).V → (VS D).V) '' (Λ₂ : Set (VS D).V) = (γ.lam : Set (VS D).V)) →
        IsTerm Λ₂ (gS D) (lf D F0) (liftF F'₂) ∧ AdmWit Λ₂ (gS D) (lf D F0) (liftF F'₂) 1 ∧
          IsGeneric Λ₂ (gS D) (lf D F0) (liftF F'₂) ∧ FrameOK D Λ₂ (liftF F'₂)

variable {u u' F0 what₂}

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ZsVolGrp
noncomputable section

namespace Formalism.L2.SG.Pf.ZsVolGrp

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.ZsVolCut Matrix
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Uni

variable {R : Type*} [CommRing R] {n : ℕ}

theorem det_lo {l : Matrix (Fin n) (Fin n) R} (h1 : ∀ a, l a a = 1) (h2 : ∀ a b, a < b → l a b = 0) : l.det = 1 := by
  rw [Matrix.det_of_lowerTriangular l (fun i j hij => h2 i j hij)]
  exact Finset.prod_eq_one fun i _ => h1 i

theorem det_up {l : Matrix (Fin n) (Fin n) R} (h1 : ∀ a, l a a = 1) (h2 : ∀ a b, b < a → l a b = 0) : l.det = 1 := by
  rw [Matrix.det_of_upperTriangular (fun i j hij => h2 i j hij)]
  exact Finset.prod_eq_one fun i _ => h1 i

theorem inv_eq_adj {l : Matrix (Fin n) (Fin n) R} (h : l.det = 1) : l⁻¹ = l.adjugate := by
  rw [Matrix.inv_def, h, Ring.inverse_one, one_smul]

theorem adj_mem (S : Subring R) {l : Matrix (Fin n) (Fin n) R} (h : ∀ a b, l a b ∈ S) (i j : Fin n) :
    l.adjugate i j ∈ S := by
  let lS : Matrix (Fin n) (Fin n) S := fun a b => ⟨l a b, h a b⟩
  have e : l = S.subtype.mapMatrix lS := by
    ext a b
    rfl
  rw [e, ← RingHom.map_adjugate]
  exact (lS.adjugate i j).2

end Uni

section Int

variable {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E] [TopologicalSpace E]
  [MeasurableSpace E] (Mp : Loc.Model F E) {n : ℕ}

theorem intLow_one : Formalism.MainNotions.S.TieN.IntLow Mp (1 : Matrix (Fin n) (Fin n) E) :=
  ⟨fun a => by simp, fun a b h => by simp [Matrix.one_apply, h.ne], fun a b => by
    rw [Matrix.one_apply]; split_ifs
    · exact one_mem _
    · exact zero_mem _⟩

theorem intUp_one : Formalism.MainNotions.S.TieN.IntUp Mp (1 : Matrix (Fin n) (Fin n) E) :=
  ⟨fun a => by simp, fun a b h => by simp [Matrix.one_apply, h.ne'], fun a b => by
    rw [Matrix.one_apply]; split_ifs
    · exact one_mem _
    · exact zero_mem _⟩

theorem intLow_mul {l l' : Matrix (Fin n) (Fin n) E} (h : Formalism.MainNotions.S.TieN.IntLow Mp l)
    (h' : Formalism.MainNotions.S.TieN.IntLow Mp l') : Formalism.MainNotions.S.TieN.IntLow Mp (l * l') := by
  first | exact GlobalTheory.LowerIntegralMul.intLow_mul .. | (apply GlobalTheory.LowerIntegralMul.intLow_mul <;> assumption) | (intros; apply GlobalTheory.LowerIntegralMul.intLow_mul <;> assumption) | (apply @GlobalTheory.LowerIntegralMul.intLow_mul <;> assumption) | (intros; apply @GlobalTheory.LowerIntegralMul.intLow_mul <;> assumption) | (apply @GlobalTheory.LowerIntegralMul.intLow_mul <;> first | assumption | infer_instance) | exact @GlobalTheory.LowerIntegralMul.intLow_mul F E ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› Mp n l l' h h' | exact @GlobalTheory.LowerIntegralMul.intLow_mul F E ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› Mp n l l' h | exact @GlobalTheory.LowerIntegralMul.intLow_mul F E ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› Mp n l l' | exact @GlobalTheory.LowerIntegralMul.intLow_mul F E ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› Mp n l | exact @GlobalTheory.LowerIntegralMul.intLow_mul F E ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› Mp n | exact @GlobalTheory.LowerIntegralMul.intLow_mul F E ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› Mp | exact @GlobalTheory.LowerIntegralMul.intLow_mul F E ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @GlobalTheory.LowerIntegralMul.intLow_mul F E ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @GlobalTheory.LowerIntegralMul.intLow_mul F E ‹_› ‹_› ‹_› ‹_› ‹_› | exact @GlobalTheory.LowerIntegralMul.intLow_mul F E ‹_› ‹_› ‹_› ‹_› | exact @GlobalTheory.LowerIntegralMul.intLow_mul F E ‹_› ‹_› ‹_› | exact @GlobalTheory.LowerIntegralMul.intLow_mul F E ‹_› ‹_› | exact @GlobalTheory.LowerIntegralMul.intLow_mul F E ‹_› | exact @GlobalTheory.LowerIntegralMul.intLow_mul F E | exact @GlobalTheory.LowerIntegralMul.intLow_mul F

theorem intUp_mul {l l' : Matrix (Fin n) (Fin n) E} (h : Formalism.MainNotions.S.TieN.IntUp Mp l)
    (h' : Formalism.MainNotions.S.TieN.IntUp Mp l') : Formalism.MainNotions.S.TieN.IntUp Mp (l * l') := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨h1', h2', h3'⟩ := h'
  refine ⟨fun a => ?_, fun a b hab => ?_, fun a b => ?_⟩
  · rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [h1, h1', mul_one]
    · intro c _ hc
      rcases lt_or_gt_of_ne hc with h | h
      · rw [h2 a c h, zero_mul]
      · rw [h2' c a h, mul_zero]
    · simp
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    rcases lt_or_ge c a with h | h
    · rw [h2 a c h, zero_mul]
    · rw [h2' c b (lt_of_lt_of_le hab h), mul_zero]
  · rw [Matrix.mul_apply]
    exact sum_mem fun c _ => mul_mem (h3 a c) (h3' c b)

theorem intLow_inv {l : Matrix (Fin n) (Fin n) E} (h : Formalism.MainNotions.S.TieN.IntLow Mp l) :
    Formalism.MainNotions.S.TieN.IntLow Mp l⁻¹ ∧ l⁻¹ * l = 1 ∧ l * l⁻¹ = 1 := by
  obtain ⟨h1, h2, h3⟩ := h
  have hd := det_lo h1 h2
  have hu : IsUnit l.det := by rw [hd]; exact isUnit_one
  have hli : l⁻¹ * l = 1 := Matrix.nonsing_inv_mul l hu
  have hil : l * l⁻¹ = 1 := Matrix.mul_nonsing_inv l hu
  have := Matrix.invertibleOfIsUnitDet l hu
  have hb : l⁻¹.BlockTriangular OrderDual.toDual :=
    Matrix.blockTriangular_inv_of_blockTriangular (fun i j hij => h2 i j hij)
  have hz : ∀ a b, a < b → l⁻¹ a b = 0 := fun a b hab => hb hab
  refine ⟨⟨fun a => ?_, hz, fun a b => ?_⟩, hli, hil⟩
  · have e := congrFun (congrFun hil a) a
    rw [Matrix.mul_apply, Finset.sum_eq_single a, h1, one_mul] at e
    · simpa using e
    · intro c _ hc
      rcases lt_or_gt_of_ne hc with h | h
      · rw [hz c a h, mul_zero]
      · rw [h2 a c h, zero_mul]
    · simp
  · rw [inv_eq_adj hd]
    exact adj_mem Mp.R h3 a b

theorem intUp_inv {l : Matrix (Fin n) (Fin n) E} (h : Formalism.MainNotions.S.TieN.IntUp Mp l) :
    Formalism.MainNotions.S.TieN.IntUp Mp l⁻¹ ∧ l⁻¹ * l = 1 ∧ l * l⁻¹ = 1 := by
  obtain ⟨h1, h2, h3⟩ := h
  have hd := det_up h1 h2
  have hu : IsUnit l.det := by rw [hd]; exact isUnit_one
  have hli : l⁻¹ * l = 1 := Matrix.nonsing_inv_mul l hu
  have hil : l * l⁻¹ = 1 := Matrix.mul_nonsing_inv l hu
  have := Matrix.invertibleOfIsUnitDet l hu
  have hb : l⁻¹.BlockTriangular id :=
    Matrix.blockTriangular_inv_of_blockTriangular (fun i j hij => h2 i j hij)
  have hz : ∀ a b, b < a → l⁻¹ a b = 0 := fun a b hab => hb hab
  refine ⟨⟨fun a => ?_, hz, fun a b => ?_⟩, hli, hil⟩
  · have e := congrFun (congrFun hil a) a
    rw [Matrix.mul_apply, Finset.sum_eq_single a, h1, one_mul] at e
    · simpa using e
    · intro c _ hc
      rcases lt_or_gt_of_ne hc with h | h
      · rw [h2 a c h, zero_mul]
      · rw [hz c a h, mul_zero]
    · simp
  · rw [inv_eq_adj hd]
    exact adj_mem Mp.R h3 a b

end Int

theorem zhatOM_zhatOM {K : Type*} [CommRing K] {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    ZhatOM (ZhatOM Z) = Z := by
  ext a b
  simp only [ZhatOM]
  rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul]
  simp

end Formalism.L2.SG.Pf.ZsVolGrp

end
end
