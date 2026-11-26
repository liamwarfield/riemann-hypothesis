module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIrreducibleTwist
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeilRepresentationContinuous
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousSingleAt
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl ValuativeRel NumberField Filter
open IsDedekindDomain
open scoped TensorProduct RestrictedProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.FinPl.SplitPoint

open GlobalTheory.IdemModTwo GlobalTheory.SplitIdem GlobalTheory.SplitChart GlobalTheory.SplitHecke

open Classical in
theorem continuous_single_at (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (singleV F v) := by
  have hS : Filter.cofinite ≤ Filter.principal ({v}ᶜ : Set (HeightOneSpectrum (𝓞 F))) :=
    Filter.le_principal_iff.2 (Set.finite_singleton v).compl_mem_cofinite
  let f : v.adicCompletion F → Πʳ w : HeightOneSpectrum (𝓞 F),
      [w.adicCompletion F, w.adicCompletionIntegers F]_[Filter.principal ({v}ᶜ : Set _)] :=
    fun x => ⟨Pi.single (M := fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F) v x, by
      intro w hw
      have hw' : w ≠ v := hw
      simp only [Set.mem_ofPred_eq, Pi.single_eq_of_ne hw', SetLike.mem_coe]
      exact zero_mem _⟩
  have hf : Continuous f := RestrictedProduct.continuous_rng_of_principal.2 (continuous_single v)
  exact (RestrictedProduct.continuous_inclusion hS).comp hf

theorem continuous_eval_at (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (evalV F v) :=
  RestrictedProduct.continuous_eval (R := fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
    (A := fun w : HeightOneSpectrum (𝓞 F) => (w.adicCompletionIntegers F : Set (w.adicCompletion F))) v

theorem mem_integer_iff (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v) :
    a ∈ 𝒪[Fv F v] ↔ a ∈ v.adicCompletionIntegers F := by
  rw [Valuation.mem_integer_iff, ← map_one (valuation (Fv F v)), ← Valuation.Compatible.vle_iff_le,
    HeightOneSpectrum.mem_adicCompletionIntegers,
    ← map_one (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)))]
  exact Iff.rfl

variable {D : D7} {v : Pl D} {e : AE D}

theorem splitAt_of {ε : AF D.host.F} (h : IsSplitIdem D e) (hε : IsPlaceIdem D v ε)
    (he : e + cA D e = algebraMap (AF D.host.F) (AE D) ε) : SplitAt D v e := by
  obtain ⟨α, rfl, h3, h4⟩ := hε
  have : α = singleV D.host.F v 1 := af_ext _ fun w => by
    by_cases hw : w = v
    · subst hw; rw [h3, evalV_singleV_same]
    · rw [h4 w hw, evalV_singleV_ne _ v _ hw]
  subst this
  exact ⟨h.1, h.2.1, he⟩

def sec (D : D7) (v : Pl D) (e : AE D) : Fv D.host.F v →+ AE D :=
  AddMonoidHom.ofMapSub (fun a => fj D (singleV D.host.F v a) * e) fun x y => by
    rw [singleV_sub, map_sub, sub_mul]

theorem sec_apply (a : Fv D.host.F v) : sec D v e a = fj D (singleV D.host.F v a) * e := rfl

theorem continuous_sec : Continuous (sec D v e) := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  have h1 : Continuous fun x : Fv D.host.F v => pairA D.host.F 0 (singleV D.host.F v x) :=
    Continuous.prodMk continuous_const (continuous_single_at _ v)
  have h2 : Continuous (algebraMap (AF D.host.F) (AE D)) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (AF D.host.F) (AE D))
  exact (h2.comp h1).mul continuous_const

theorem continuous_comp (he : SplitAt D v e) : Continuous (comp he) := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  let σ : AF D.host.F →+* Fv D.host.F v := ((evalV D.host.F v).comp (sndA D.host.F)).toRingHom
  have hσ : Continuous σ := (continuous_eval_at _ v).comp continuous_snd
  let L : AE D →ₛₗ[σ] Fv D.host.F v :=
    { toFun := comp he
      map_add' := map_add _
      map_smul' := fun a x => by
        rw [Algebra.smul_def, map_mul, comp_algebraMap]
        rfl }
  exact IsModuleTopology.continuous_of_linearMapₛₗ hσ L

theorem exists_splitPt : ∀ (D : D7) (v : Pl D) (e : AE D) (ε : AF D.host.F), IsSplitIdem D e → IsPlaceIdem D v ε → e + cA D e = algebraMap (AF D.host.F) (AE D) ε → ∃ p : SplitPt D (Fv D.host.F v), p.e = e ∧ p.v = v := by
  intro D v e ε h hε hs
  have he : SplitAt D v e := splitAt_of h hε hs
  have hps : ∀ a, comp he (sec D v e a) = a := fun a => by
    rw [sec_apply, map_mul, comp_fj, comp_self, mul_one, evalV_singleV_same]
  have hsp : ∀ x, sec D v e (comp he x) = e * x := fun x => (sc_spec he x).symm
  refine ⟨{
    v := v
    e := e
    split := h
    above := ⟨ε, hε, hs⟩
    pr := comp he
    sec := sec D v e
    pr_sec := hps
    sec_pr := hsp
    cont_pr := continuous_comp he
    cont_sec := continuous_sec
    int_iff := fun a => ?_ }, rfl, rfl⟩
  have h1 := (chart_comp he).2.2.2 (sec D v e a)
  rw [← hsp, hps] at h1
  rw [h1, isInt_Ov, mem_integer_iff]

end GlobalTheory.FinPl.SplitPoint

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeCompletionSelfAnnihilatorAtPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeCompletionSelfAnnihilatorAtPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl IsDedekindDomain NumberField
open scoped TensorProduct

noncomputable section

set_option synthInstance.maxHeartbeats 160000

namespace GlobalTheory.SelfDualAt

variable {D : D7}


open Classical in
def indP (P : Pl D → Prop) : Af D.host.F :=
  ⟨fun v => if P v then 1 else 0, Filter.Eventually.of_forall fun v => by
    by_cases h : P v
    · simp only [h, if_true]; exact one_mem _
    · simp only [h, if_false]; exact zero_mem _⟩

open Classical in
theorem evalV_indP (P : Pl D → Prop) (v : Pl D) : evalV D.host.F v (indP P) = if P v then 1 else 0 := rfl

def cP (P : Pl D → Prop) : AF D.host.F := pairA D.host.F 0 (indP P)

theorem cA_alg (a : AF D.host.F) : cA D (algebraMap (AF D.host.F) (AE D) a) = algebraMap (AF D.host.F) (AE D) a := by
  change a ⊗ₜ[D.host.F] D.sp.cm.sig 1 = _
  rw [map_one]
  rfl

theorem hO_smul_swap (S T : HSp D) (c : AF D.host.F) (x y : WO S T) : hO S T x (c • y) = hO S T (c • x) y := by
  unfold hO
  simp only [Matrix.smul_apply, Algebra.smul_def, map_mul, cA_alg]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c' _ => Finset.sum_congr rfl fun d _ => by ring

theorem symplO_smul_swap (S T : HSp D) (c : AF D.host.F) (x y : WO S T) :
    symplO S T x (c • y) = symplO S T (c • x) y := by
  unfold symplO
  rw [hO_smul_swap]


set_option maxHeartbeats 800000 in
theorem compFin_repr (w : Pl D) (y : Af D.host.F ⊗[D.host.F] D.host.E) (k : Fin (Module.finrank D.host.F D.host.E)) :
    (Algebra.TensorProduct.basis (Fv D.host.F w) (Module.finBasis D.host.F D.host.E)).repr
        (GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w y) k =
      evalV D.host.F w ((Algebra.TensorProduct.basis (Af D.host.F) (Module.finBasis D.host.F D.host.E)).repr y k) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    have h : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w (a ⊗ₜ[D.host.F] e) = evalV D.host.F w a ⊗ₜ[D.host.F] e := rfl
    rw [h, Algebra.TensorProduct.basis_repr_tmul, Algebra.TensorProduct.basis_repr_tmul]
    simp [Finsupp.smul_apply, Finsupp.mapRange_apply, map_mul, AlgHom.commutes]
  | add x y hx hy =>
    simp only [RingHom.map_add (f := _), LinearEquiv.map_add (e := _), Finsupp.add_apply, hx, hy]
    exact (RingHom.map_add (evalV D.host.F w).toRingHom _ _).symm

theorem eq_zero_of_compFin (y : Af D.host.F ⊗[D.host.F] D.host.E) (h : ∀ w, GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w y = 0) :
    y = 0 := by
  have hr : (Algebra.TensorProduct.basis (Af D.host.F) (Module.finBasis D.host.F D.host.E)).repr y = 0 := by
    refine Finsupp.ext fun k => ?_
    have hk : ∀ w : Pl D, evalV D.host.F w
        ((Algebra.TensorProduct.basis (Af D.host.F) (Module.finBasis D.host.F D.host.E)).repr y k) = 0 := fun w => by
      rw [← compFin_repr, h w, map_zero]; rfl
    rw [Finsupp.zero_apply]
    refine FiniteAdeleRing.ext (R := 𝓞 D.host.F) D.host.F fun w => ?_
    exact hk w
  simpa using hr

set_option maxHeartbeats 800000 in
theorem compFin_alg_cP (P : Pl D → Prop) (w : Pl D) (hw : P w) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w (finPart D (algebraMap (AF D.host.F) (AE D) (cP P))) = 1 := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, GlobalTheory.LatVac.finPart_tmul]
  have h : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w (sndA D.host.F (cP P) ⊗ₜ[D.host.F] (1 : D.host.E)) =
      evalV D.host.F w (indP P) ⊗ₜ[D.host.F] (1 : D.host.E) := by
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
      AlgHom.id_apply]
    rfl
  rw [h, evalV_indP, if_pos hw]
  exact Algebra.TensorProduct.one_def.symm


set_option maxHeartbeats 800000 in
theorem algebraMap_placeIdempotent_mul (P : Pl D → Prop) (z : AE D) (hz : z ∈ idAt D P) :
    algebraMap (AF D.host.F) (AE D) (cP P) * z = z := by
  rw [idAt, Ideal.mem_inf, Ideal.mem_iInf] at hz
  obtain ⟨hinf, hfin⟩ := hz
  rw [RingHom.mem_ker] at hinf
  have h0 : (1 - algebraMap (AF D.host.F) (AE D) (cP P)) * z = 0 := by
    apply GlobalTheory.LatVac.eq_zero_of_parts
    · rw [RingHom.map_mul, hinf, mul_zero]
    · apply eq_zero_of_compFin
      intro w
      rw [RingHom.map_mul, RingHom.map_mul]
      by_cases hw : P w
      · rw [RingHom.map_sub, RingHom.map_sub, RingHom.map_one, RingHom.map_one, compFin_alg_cP P w hw, sub_self, zero_mul]
      · have h1 := hfin ⟨w, hw⟩
        rw [RingHom.mem_ker] at h1
        rw [show GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w (finPart D z) = compAt D w z from rfl, h1, mul_zero]
  rw [sub_mul, one_mul, sub_eq_zero] at h0
  exact h0.symm

theorem smul_mem_latO (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : Pl D → Prop) (y : WO S T) (hy : y ∈ latO S T LS LT fun _ => True) : cP P • y ∈ latO S T LS LT P := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hy
    apply AddSubgroup.subset_closure
    refine ⟨indP P * α, ?_, ?_, a, ha, s, hs, t, ht, ?_⟩
    · intro v
      rw [map_mul]
      refine mul_mem ?_ (hα v)
      rw [evalV_indP]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    · intro v hv
      rw [map_mul, evalV_indP, if_neg hv, zero_mul]
    · ext i j
      rw [Matrix.smul_apply, Matrix.of_apply, Matrix.of_apply, TensorProduct.smul_tmul', smul_eq_mul]
      congr 1
      refine Prod.ext ?_ ?_
      · show (0 : Ainf D.host.F) * 0 = 0
        rw [zero_mul]
      · rfl
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ h1 h2 => rw [smul_add]; exact add_mem h1 h2
  | neg x _ h => rw [smul_neg]; exact neg_mem h

theorem latO_ann_at : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∀ (P : Pl D → Prop) (u : WO S T), MxAt P u → (u ∈ latO S T (LS : Set _) (LT : Set _) P ↔ ∀ u' ∈ latO S T (LS : Set _) (LT : Set _) P, ψ (symplO S T u u') = 1) := by
  intro D ψ hψ S T LS LT hS hT P u hu
  have key := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T LS LT hψ hS hT).1
  have hinf : u.map (infPart D) = 0 := by
    ext i j
    have h := (Ideal.mem_inf.1 (hu i j)).1
    rw [RingHom.mem_ker] at h
    simpa using h
  have hle : latO S T (LS : Set _) (LT : Set _) P ≤ latO S T (LS : Set _) (LT : Set _) fun _ => True := by
    apply AddSubgroup.closure_mono
    rintro w ⟨α, hα, -, rest⟩
    exact ⟨α, hα, fun v h => (h trivial).elim, rest⟩
  have hfix : cP P • u = u := by
    ext i j
    rw [Matrix.smul_apply, Algebra.smul_def]
    exact algebraMap_placeIdempotent_mul P _ (hu i j)
  constructor
  · intro hm u' hu'
    exact (key u hinf).1 (hle hm) u' (hle hu')
  · intro hann
    have h2 : ∀ y ∈ latO S T (LS : Set _) (LT : Set _) (fun _ => True), ψ (symplO S T u y) = 1 := by
      intro y hy
      have h := hann _ (smul_mem_latO S T _ _ P y hy)
      rwa [symplO_smul_swap, hfix] at h
    rw [← hfix]
    exact smul_mem_latO S T _ _ P u ((key u hinf).2 h2)

end GlobalTheory.SelfDualAt

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeCompletionSelfAnnihilatorAtPlacesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homLatticeCompletion_self_annihilator_atPlaces : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∀ (P : Pl D → Prop) (u : WO S T), MxAt P u → (u ∈ latO S T (LS : Set _) (LT : Set _) P ↔ ∀ u' ∈ latO S T (LS : Set _) (LT : Set _) P, ψ (symplO S T u u') = 1) := by
  first | exact @GlobalTheory.SelfDualAt.latO_ann_at | exact GlobalTheory.SelfDualAt.latO_ann_at | (intros; apply GlobalTheory.SelfDualAt.latO_ann_at <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumThetaJointlyContinuous
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumThetaJointlyContinuous
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf

theorem jointCont_all : ∀ D : D7, JointCont D := by
  intro D ψ S T χS χT om hom f hf
  exact GlobalTheory.ThetaJointCont.continuous_om_oriented hom hf

end GlobalTheory.Unf
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumThetaJointlyContinuousStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilDatum_theta_jointlyContinuous : ∀ D : D7, JointCont D := by
  first | exact @GlobalTheory.Unf.jointCont_all | exact GlobalTheory.Unf.jointCont_all | (intros; apply GlobalTheory.Unf.jointCont_all <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlaceIdempotentActsOnSupportedAndOff
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlaceIdempotentActsOnSupportedAndOff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel ValuativeRel
open scoped Pointwise TensorProduct
open IsDedekindDomain NumberField

noncomputable section

namespace GlobalTheory.FinPl

theorem tensorProductBasis_repr_map_firstFactor {F E A B : Type} [Field F] [Field E] [Algebra F E] [CommRing A] [Algebra F A]
    [CommRing B] [Algebra F B] {ι : Type} (b : Module.Basis ι F E) (f : A →ₐ[F] B) (x : A ⊗[F] E) (i : ι) :
    (Algebra.TensorProduct.basis B b).repr (Algebra.TensorProduct.map f (AlgHom.id F E) x) i =
      f ((Algebra.TensorProduct.basis A b).repr x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [map_add (f := _), hx, hy]
  | tmul a m =>
    simp [Algebra.TensorProduct.basis_repr_tmul, Algebra.TensorProduct.map_tmul, Algebra.smul_def]

theorem CMAdele_eq_zero_of_infinite_and_finite_components_zero (D : D7) (a : AE D) (h0 : infPart D a = 0) (hw : ∀ w : Pl D, compAt D w a = 0) :
    a = 0 := by
  let b := Module.Free.chooseBasis D.host.F D.host.E
  let bA := Algebra.TensorProduct.basis (AF D.host.F) b
  suffices hc : ∀ i, bA.repr a i = 0 by
    apply bA.repr.injective
    ext i
    simpa using hc i
  intro i
  have h1 : fstA D.host.F (bA.repr a i) = 0 := by
    have := tensorProductBasis_repr_map_firstFactor b (fstA D.host.F) a i
    rw [← this]
    change (Algebra.TensorProduct.basis _ b).repr (infPart D a) i = 0
    rw [h0]; simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply]
  have h2 : ∀ w : Pl D, evalV D.host.F w (sndA D.host.F (bA.repr a i)) = 0 := by
    intro w
    have e1 := tensorProductBasis_repr_map_firstFactor b (sndA D.host.F) a i
    have e2 := tensorProductBasis_repr_map_firstFactor b (evalV D.host.F w)
      (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) a) i
    have hw' : Algebra.TensorProduct.map (evalV D.host.F w) (AlgHom.id D.host.F D.host.E)
        (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) a) = 0 := hw w
    rw [← e1, ← e2, hw', LinearEquiv.map_zero]
    rfl
  apply Prod.ext
  · exact h1
  · apply Subtype.ext
    funext w
    exact h2 w

theorem mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere (D : D7) (P : Pl D → Prop) (a : AE D) :
    a ∈ idAt D P ↔ infPart D a = 0 ∧ ∀ w : Pl D, ¬ P w → compAt D w a = 0 := by
  simp only [idAt, Submodule.mem_inf, Submodule.mem_iInf, RingHom.mem_ker, Subtype.forall]

theorem placeIdempotent_infinite_and_finite_components (D : D7) (v : Pl D) (ε : AF D.host.F) (α : Af D.host.F)
    (hε : ε = pairA D.host.F 0 α) :
    infPart D (algebraMap (AF D.host.F) (AE D) ε) = 0 ∧
      ∀ w : Pl D, compAt D w (algebraMap (AF D.host.F) (AE D) ε) = evalV D.host.F w α ⊗ₜ[D.host.F] (1 : D.host.E) := by
  have ha : algebraMap (AF D.host.F) (AE D) ε = ε ⊗ₜ[D.host.F] (1 : D.host.E) := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  refine ⟨?_, fun w => ?_⟩
  · rw [ha]
    change Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) (ε ⊗ₜ[D.host.F] (1 : D.host.E)) = 0
    rw [Algebra.TensorProduct.map_tmul, hε]
    exact TensorProduct.zero_tmul _ _
  · rw [ha]
    change Algebra.TensorProduct.map (evalV D.host.F w) (AlgHom.id D.host.F D.host.E)
      (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) (ε ⊗ₜ[D.host.F] (1 : D.host.E))) = _
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, hε]
    rfl

theorem mem_supportedAtPlace_iff_placeIdempotent_mul (D : D7) (v : Pl D) (e : AE D) (h0 : infPart D e = 0) (c1 : compAt D v e = 1)
    (c0 : ∀ w : Pl D, w ≠ v → compAt D w e = 0) (a : AE D) : a ∈ idAt D (· = v) ↔ e * a = a := by
  constructor
  · intro ha
    rw [mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere] at ha
    obtain ⟨ha0, haw⟩ := ha
    rw [← sub_eq_zero]
    apply CMAdele_eq_zero_of_infinite_and_finite_components_zero
    · rw [RingHom.map_sub, RingHom.map_mul, h0, ha0, zero_mul, sub_zero]
    · intro w
      rw [RingHom.map_sub, RingHom.map_mul]
      by_cases h : w = v
      · subst h; rw [c1, one_mul, sub_self]
      · rw [haw w h, mul_zero, sub_zero]
  · intro ha
    rw [mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere]
    refine ⟨?_, fun w hw' => ?_⟩
    · rw [← ha, RingHom.map_mul, h0, zero_mul]
    · rw [← ha, RingHom.map_mul, c0 w hw', zero_mul]

theorem placeIdempotent_mul_supportedOffPlace_eq_zero (D : D7) (v : Pl D) (e : AE D) (h0 : infPart D e = 0)
    (c0 : ∀ w : Pl D, w ≠ v → compAt D w e = 0) (a : AE D) (ha : a ∈ idAt D (· ≠ v)) : e * a = 0 := by
  rw [mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere] at ha
  obtain ⟨ha0, haw⟩ := ha
  apply CMAdele_eq_zero_of_infinite_and_finite_components_zero
  · rw [RingHom.map_mul, h0, zero_mul]
  · intro w
    rw [RingHom.map_mul]
    by_cases h : w = v
    · rw [haw w (fun h' => h' h), mul_zero]
    · rw [c0 w h, zero_mul]

theorem placeIdem_acts : ∀ (D : D7) (v : Pl D) (ε : AF D.host.F), IsPlaceIdem D v ε →
    (∀ a : AE D, a ∈ idAt D (· = v) ↔ algebraMap (AF D.host.F) (AE D) ε * a = a) ∧
    (∀ a : AE D, a ∈ idAt D (· ≠ v) → algebraMap (AF D.host.F) (AE D) ε * a = 0) := by
  intro D v ε ⟨α, hε, hv, hw⟩
  obtain ⟨h0, hc⟩ := placeIdempotent_infinite_and_finite_components D v ε α hε
  have c1 : compAt D v (algebraMap (AF D.host.F) (AE D) ε) = 1 := by
    rw [hc, hv]; rfl
  have c0 : ∀ w : Pl D, w ≠ v → compAt D w (algebraMap (AF D.host.F) (AE D) ε) = 0 := by
    intro w h; rw [hc, hw w h, TensorProduct.zero_tmul]
  exact ⟨mem_supportedAtPlace_iff_placeIdempotent_mul D v _ h0 c1 c0, placeIdempotent_mul_supportedOffPlace_eq_zero D v _ h0 c0⟩

end GlobalTheory.FinPl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlaceIdempotentActsOnSupportedAndOffStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel ValuativeRel
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.placeIdempotent_acts_on_supportedAndOff : ∀ (D : D7) (v : Pl D) (ε : AF D.host.F), IsPlaceIdem D v ε →
    (∀ a : AE D, a ∈ idAt D (· = v) ↔ algebraMap (AF D.host.F) (AE D) ε * a = a) ∧
    (∀ a : AE D, a ∈ idAt D (· ≠ v) → algebraMap (AF D.host.F) (AE D) ε * a = 0) := by
  first | exact @GlobalTheory.FinPl.placeIdem_acts | exact GlobalTheory.FinPl.placeIdem_acts | (intros; apply GlobalTheory.FinPl.placeIdem_acts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingPreservesSupportedUnitarySubgro
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel Matrix

namespace GlobalTheory.IwaPlace

variable {D : D7}

def hermAt (S : HSp D) (x y : Fin S.rank → AE D) : AE D := ∑ i, ∑ j, cA D (y i) * gA S i j * x j

def IsSDAt (S : HSp D) (v : Pl D) (Λ : AddSubgroup (Fin S.rank → AE D)) : Prop :=
  (∀ y ∈ Λ, ∀ i, y i ∈ idAt D (· = v)) ∧
    (∃ m : ℕ, 0 < m ∧ ∀ y : Fin S.rank → AE D, (∀ i, y i ∈ intAt D (· = v)) → (m : AE D) • y ∈ Λ) ∧
    ∀ y : Fin S.rank → AE D, (∀ i, y i ∈ idAt D (· = v)) → (y ∈ Λ ↔ ∀ x ∈ Λ, hermAt S y x ∈ intAt D (· = v))

theorem mem_congGrp_iff (V : HSp D) (I : Ideal (AE D)) (g : GA D V) :
    g ∈ congGrp V I ↔ ∀ i j, mt V g i j - (1 : Mx D V.rank V.rank) i j ∈ I := by
  unfold congGrp
  rw [MonoidHom.mem_ker]
  have e1 : ((1 : Mx D V.rank V.rank).map (Ideal.Quotient.mk I)) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have e2 : ((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I)).comp (matHom V) g).1 = (mt V g).map (Ideal.Quotient.mk I) := rfl
  constructor
  · intro h i j
    rw [← Ideal.Quotient.eq]
    have := congrArg (fun u : GL (Fin V.rank) (AE D ⧸ I) => u.1 i j) h
    simp only [e2, Units.val_one] at this
    rw [← e1] at this
    exact this
  · intro h
    ext i j
    rw [e2, Units.val_one, ← e1]
    exact Ideal.Quotient.eq.2 (h i j)

theorem mulVec_mem_idAt {P : Pl D → Prop} {m n : ℕ} (M : Matrix (Fin m) (Fin n) (AE D)) {y : Fin n → AE D}
    (hy : ∀ i, y i ∈ idAt D P) (i : Fin m) : (M *ᵥ y) i ∈ idAt D P :=
  by
  simp only [Matrix.mulVec, dotProduct]
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hy j)

theorem wittCoreEmbedding_preserves_supportedUnitarySubgroup {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {P : Pl D → Prop} {γ : GA D S₀}
    (hγ : γ ∈ grpAt S₀ P) : d.emb0 γ ∈ grpAt S P := by
  have hγ' := (mem_congGrp_iff S₀ (idAt D P) γ).1 hγ
  refine (mem_congGrp_iff S (idAt D P) _).2 fun i j => ?_
  have e : mt S (d.emb0 γ) - 1 = d.j0 ⬝ (mt S₀ γ - 1) ⬝ d.p0 := by
    rw [d.unitaryMatrix_wittCoreEmbedding, ← d.sum_eq_one, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
    abel
  rw [← Matrix.sub_apply, e, Matrix.mul_apply]
  refine Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ ?_
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (by rw [Matrix.sub_apply]; exact hγ' l k)

end GlobalTheory.IwaPlace

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousIntegralCompactAutomorphicQuotientPara
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousIntegralCompactAutomorphicQuotientPara
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.CocompactParam

theorem eventually_close {G P : Type*} [TopologicalSpace G] [TopologicalSpace P] (K : G → P → ℂ)
    (hK : Continuous (Function.uncurry K)) {C : Set G} (hC : IsCompact C) (p₀ : P) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ p in nhds p₀, ∀ g ∈ C, ‖K g p - K g p₀‖ < ε := by
  refine hC.eventually_forall_of_forall_eventually (P := fun p g => ‖K g p - K g p₀‖ < ε) fun g _ => ?_
  have h1 : Continuous fun z : P × G => K z.2 z.1 := hK.comp (continuous_snd.prodMk continuous_fst)
  have h2 : Continuous fun z : P × G => K z.2 p₀ := hK.comp (continuous_snd.prodMk continuous_const)
  have hc : Continuous fun z : P × G => ‖K z.2 z.1 - K z.2 p₀‖ := (h1.sub h2).norm
  exact hc.continuousAt.eventually_lt continuousAt_const (by simpa using hε)

theorem continuous_setIntegral_of_unif {G P : Type*} [MeasurableSpace G] [TopologicalSpace P] (μ : Measure G)
    (𝓕 : Set G) (hfin : μ 𝓕 < ⊤) (K : G → P → ℂ) (hint : ∀ p, IntegrableOn (fun g => K g p) 𝓕 μ)
    (hcl : ∀ p₀, ∀ ε : ℝ, 0 < ε → ∀ᶠ p in nhds p₀, ∀ g, ‖K g p - K g p₀‖ < ε) :
    Continuous fun p => ∫ g in 𝓕, K g p ∂μ := by
  refine continuous_iff_continuousAt.2 fun p₀ => Metric.tendsto_nhds.2 fun ε hε => ?_
  have hm : 0 ≤ μ.real 𝓕 := measureReal_nonneg
  have hδ : 0 < ε / (μ.real 𝓕 + 1) := by positivity
  filter_upwards [hcl p₀ _ hδ] with p hp
  rw [dist_eq_norm, ← integral_sub (hint p) (hint p₀)]
  refine lt_of_le_of_lt (norm_setIntegral_le_of_norm_le_const hfin fun g _ => (hp g).le) ?_
  rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
  nlinarith

theorem continuous_integral_param : ∀ (D : D7) (V : HSp D), CoCpt V → ∀ (v : Vol V) (P : Type) [TopologicalSpace P] (K : GA D V → P → ℂ), Continuous (Function.uncurry K) → (∀ γ ∈ GQ V, ∀ g p, K (γ * g) p = K g p) → (∀ p, IntegrableOn (fun g => K g p) v.𝓕 v.μ) ∧ (Continuous fun p => ∫ g in v.𝓕, K g p ∂v.μ) ∧ ∀ p₀, ∃ C : ℝ, ∀ᶠ p in nhds p₀, ∀ g, ‖K g p‖ ≤ C := by
  intro D V hV v P _ K hK hinv
  obtain ⟨C, hC, hcov⟩ := hV
  have hcov' : ∀ h : GA D V, ∃ γ ∈ GQ V, ∃ c ∈ C, h = γ * c := fun h => by
    obtain ⟨γ, hγ, hc⟩ := hcov h
    exact ⟨γ⁻¹, inv_mem hγ, γ * h, hc, by rw [inv_mul_cancel_left]⟩
  have hcont : ∀ p, Continuous fun g => K g p := fun p => hK.comp (continuous_id.prodMk continuous_const)
  have hint : ∀ p, IntegrableOn (fun g => K g p) v.𝓕 v.μ := fun p =>
    GlobalTheory.CocompactIntegrable.integrableOn_fundamentalDomain V v.μ v.𝓕 C v.haar v.fund hC hcov' _ (hcont p)
      fun γ hγ h => hinv γ hγ h p
  have hfin : v.μ v.𝓕 < ⊤ := by
    have h1 := GlobalTheory.CocompactIntegrable.integrableOn_fundamentalDomain V v.μ v.𝓕 C v.haar v.fund hC hcov'
      (fun _ => (1 : ℂ)) continuous_const fun _ _ _ => rfl
    simpa using (integrableOn_const_iff (C := (1 : ℂ))).1 h1
  have hcl : ∀ p₀, ∀ ε : ℝ, 0 < ε → ∀ᶠ p in nhds p₀, ∀ g, ‖K g p - K g p₀‖ < ε := fun p₀ ε hε => by
    filter_upwards [eventually_close K hK hC p₀ hε] with p hp g
    obtain ⟨γ, hγ, hc⟩ := hcov g
    have := hp _ hc
    rwa [hinv γ hγ, hinv γ hγ] at this
  refine ⟨hint, continuous_setIntegral_of_unif v.μ v.𝓕 hfin K hint hcl, fun p₀ => ?_⟩
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn (hcont p₀).continuousOn
  refine ⟨M + 1, ?_⟩
  filter_upwards [hcl p₀ 1 one_pos] with p hp g
  obtain ⟨γ, hγ, hc⟩ := hcov g
  have h0 := hM _ hc
  simp only [hinv γ hγ] at h0
  have := norm_sub_norm_le (K g p) (K g p₀)
  linarith [hp g]

end GlobalTheory.CocompactParam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousIntegralCompactAutomorphicQuotientParaStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_integral_compactAutomorphicQuotient_param : ∀ (D : D7) (V : HSp D), CoCpt V → ∀ (v : Vol V) (P : Type) [TopologicalSpace P] (K : GA D V → P → ℂ), Continuous (Function.uncurry K) → (∀ γ ∈ GQ V, ∀ g p, K (γ * g) p = K g p) → (∀ p, IntegrableOn (fun g => K g p) v.𝓕 v.μ) ∧ (Continuous fun p => ∫ g in v.𝓕, K g p ∂v.μ) ∧ ∀ p₀, ∃ C : ℝ, ∀ᶠ p in nhds p₀, ∀ g, ‖K g p‖ ≤ C := by
  first | exact @GlobalTheory.CocompactParam.continuous_integral_param | exact GlobalTheory.CocompactParam.continuous_integral_param | (intros; apply GlobalTheory.CocompactParam.continuous_integral_param <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingLevelsAndStepsHaarMeasuresExist
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingLevelsAndStepsHaarMeasuresExist
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.Unf.VolExist

theorem nonempty_vol {D : D7} (V : HSp D) : Nonempty (Vol V) := by
  obtain ⟨i1, i2, i3, i4, i5, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨-, 𝓕, h𝓕⟩ := GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D V
    (Measure.haar : Measure (GA D V)) inferInstance
  exact ⟨⟨Measure.haar, 𝓕, inferInstance, h𝓕⟩⟩

theorem nonempty_volN {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) : Nonempty (VolN d) :=
  let ⟨ν, 𝓝, h⟩ := GlobalTheory.Per.UnitN.exists_isUnitN D S ρ d.e (isIsoSub_e d)
  ⟨⟨ν, 𝓝, h⟩⟩

theorem nonempty_volM (D : D7) (m n : ℕ) : Nonempty (VolM D m n) :=
  let ⟨μ, 𝓕, h⟩ := exists_isCovolOne D m n
  ⟨⟨μ, 𝓕, h⟩⟩

theorem nonempty_volU (D : D7) (ρ : ℕ) : Nonempty (VolU D ρ) :=
  let ⟨ν, h⟩ := (GlobalTheory.UnitU.isUnitU_exists_unique_rightInvariant D ρ).1
  ⟨⟨ν, h⟩⟩

theorem measures_exist : ∀ D : D7, (∀ V : HSp D, Nonempty (Vol V)) ∧
    (∀ (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), Nonempty (VolN d)) ∧ (∀ m n, Nonempty (VolM D m n)) ∧
    ∀ ρ, Nonempty (VolU D ρ) :=
  fun D => ⟨nonempty_vol, fun _ _ _ d => nonempty_volN d, nonempty_volM D, nonempty_volU D⟩

end GlobalTheory.Unf.VolExist

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingLevelsAndStepsHaarMeasuresExistStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfoldingLevelsAndSteps_haarMeasures_exist : ∀ D : D7, (∀ V : HSp D, Nonempty (Vol V)) ∧ (∀ (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), Nonempty (VolN d)) ∧ (∀ m n, Nonempty (VolM D m n)) ∧ ∀ ρ, Nonempty (VolU D ρ) := by
  first | exact @GlobalTheory.Unf.VolExist.measures_exist | exact GlobalTheory.Unf.VolExist.measures_exist | (intros; apply GlobalTheory.Unf.VolExist.measures_exist <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianLinkMapAdditiveRationalEquivariant
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianLinkMapAdditiveRationalEquivariant
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.LinkKappa

open GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule (ofAdj)

variable {D : D7}

theorem infPart_conj (z : AE D) : infPart D (cA D z) = sigR (Ainf D.host.F) D.sp.cm.sig (infPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem finPart_conj (z : AE D) :
    finPart D (cA D z) = sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig (finPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem map_ofAdj_eq_zero {B : Type} [CommRing B] (φ : AE D →+* B) (hφ : ∀ z, φ z = 0 → φ (cA D z) = 0)
    (L S : HSp D) {z : Mx D L.rank S.rank} (hz : z.map φ = 0) : (ofAdj L S z).map φ = 0 := by
  have h1 : (adj z).map φ = 0 := by
    funext i j
    exact hφ (z j i) (congrFun (congrFun hz j) i)
  have h2 := map_mul_eq_zero_right φ (giA S) (map_mul_eq_zero_left φ h1 (gA L))
  funext i j
  have h3 : φ ((giA S ⬝ (adj z ⬝ gA L) : Mx D S.rank L.rank) i j) = 0 := congrFun (congrFun h2 i) j
  show φ (incA D (-D.host.xi0⁻¹) * (giA S ⬝ (adj z ⬝ gA L) : Mx D S.rank L.rank) i j) = 0
  rw [map_mul, h3, mul_zero]

theorem trace_mul_smul_middle_eq_smul_trace {R : Type} [CommRing R] {m n : ℕ} (c : R) (a : Matrix (Fin m) (Fin m) R)
    (b : Matrix (Fin m) (Fin n) R) (g : Matrix (Fin n) (Fin n) R) (y : Matrix (Fin n) (Fin m) R) :
    (a ⬝ (b ⬝ ((c • g) ⬝ y))).trace = c * (a ⬝ (b ⬝ (g ⬝ y))).trace := by
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul, trace_smul, smul_eq_mul]


set_option maxHeartbeats 1600000 in
theorem hO_ofAdj (L L' S : HSp D) (τ : Matrix (Fin L.rank) (Fin L'.rank) D.host.E) (c : D.host.E)
    (hτ : τᴴ ⬝ (L.gram ⬝ τ) = (c * (D.host.xi0 * star D.host.xi0)) • L'.gram) (x y : WO S L') :
    hO L S (ofAdj L S ((rat τ : Mx D L.rank L'.rank) ⬝ x))
      (ofAdj L S ((rat τ : Mx D L.rank L'.rank) ⬝ y)) = incA D c * hO S L' y x := by
  have h : adj (rat τ : Mx D L.rank L'.rank) ⬝ (gA L ⬝ (rat τ : Mx D L.rank L'.rank)) =
      incA D (c * (D.host.xi0 * star D.host.xi0)) • gA L' := by
    rw [gA, gA, ← rat_conjTranspose, ← rat_mul, ← rat_mul, ← rat_smul]; exact congrArg rat hτ
  have h' : adj (rat τ : Mx D L.rank L'.rank) ⬝ (gA L ⬝ ((rat τ : Mx D L.rank L'.rank) ⬝ y)) =
      (incA D (c * (D.host.xi0 * star D.host.xi0)) • gA L') ⬝ y := by
    rw [← h, Matrix.mul_assoc, Matrix.mul_assoc]
  rw [hO_eq_trace, hO_eq_trace, ofAdj, ofAdj]
  simp only [adj_smul, adj_mul, adj_adj, adj_gA, adj_giA, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc,
    giA_gA_cancel, gA_giA_cancel, trace_smul, smul_eq_mul]
  rw [trace_mul_comm (rat τ : Mx D L.rank L'.rank), Matrix.mul_assoc y, trace_mul_comm y]
  simp only [Matrix.mul_assoc]
  rw [h']
  have h0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
  have h1 : incA D c = incA D (-D.host.xi0⁻¹) *
      (cA D (incA D (-D.host.xi0⁻¹)) * incA D (c * (D.host.xi0 * star D.host.xi0))) := by
    rw [GlobalTheory.DualPairCheck.cA_incA, ← map_mul, ← map_mul]
    congr 1
    rw [star_neg, star_inv₀, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg]
    field_simp
  have h2 := trace_mul_smul_middle_eq_smul_trace (R := AE D) (incA D (c * (D.host.xi0 * star D.host.xi0))) (giA S) (adj x) (gA L') y
  rw [h1, mul_assoc, mul_assoc]
  exact congrArg (fun t => incA D (-D.host.xi0⁻¹) * (cA D (incA D (-D.host.xi0⁻¹)) * t)) h2

theorem ofAdj_add (L S : HSp D) (z z' : Mx D L.rank S.rank) : ofAdj L S (z + z') = ofAdj L S z + ofAdj L S z' := by
  rw [ofAdj, ofAdj, ofAdj, adj_add, Matrix.add_mul, Matrix.mul_add, smul_add]

theorem continuous_ofAdj (L S : HSp D) : Continuous (ofAdj L S) := by
  have h1 : Continuous fun z : Mx D L.rank S.rank => (adj z ⬝ gA L : Mx D S.rank L.rank) :=
    continuous_adj.matrix_mul continuous_const
  have h2 : Continuous fun z : Mx D L.rank S.rank => (giA S ⬝ (adj z ⬝ gA L) : Mx D S.rank L.rank) :=
    continuous_const.matrix_mul h1
  exact h2.const_smul (incA D (-D.host.xi0⁻¹))

theorem ofAdj_mem (L S : HSp D) {z : Mx D L.rank S.rank} (hz : z ∈ ratMx D L.rank S.rank) :
    ofAdj L S z ∈ ratMx D S.rank L.rank :=
  ratMx_smul _ (ratMx_mul (rat_mem S.gram⁻¹) (ratMx_mul (ratMx_adj hz) (rat_mem L.gram)))

theorem mt_inv_ofAdj (L S : HSp D) (g : GA D S) (z : Mx D L.rank S.rank) :
    mt S g⁻¹ ⬝ ofAdj L S z = ofAdj L S (z ⬝ mt S g) := by
  simp only [ofAdj, mt_inv, adj_mul, Matrix.mul_smul, Matrix.mul_assoc, gA_giA_cancel]

theorem ofAdj_mul_mt_inv (L S : HSp D) (g : GA D S) (z : Mx D L.rank S.rank) :
    ofAdj L S (z ⬝ mt S g⁻¹) = mt S g ⬝ ofAdj L S z := by
  rw [← mt_inv_ofAdj, inv_inv]

theorem symplO_ofAdj (L L' S : HSp D) (τ : Matrix (Fin L.rank) (Fin L'.rank) D.host.E) (ε : ℤ)
    (hτ : τᴴ ⬝ (L.gram ⬝ τ) = ((ε : D.host.E) * (D.host.xi0 * star D.host.xi0)) • L'.gram) (x y : WO S L') :
    symplO L S (ofAdj L S ((rat τ : Mx D L.rank L'.rank) ⬝ x))
      (ofAdj L S ((rat τ : Mx D L.rank L'.rank) ⬝ y)) = -((ε : AF D.host.F) * symplO S L' x y) := by
  rw [symplO_eq, hO_ofAdj L L' S τ _ hτ, ← mul_neg, ← GlobalTheory.OrientedHeis.symplO_skew, symplO_eq, map_intCast,
    mul_left_comm, ← zsmul_eq_mul, map_zsmul, zsmul_eq_mul]

theorem kappa_props : ∀ (D : D7) (L L' S : HSp D) (τ : Matrix (Fin L.rank) (Fin L'.rank) D.host.E) (ε : ℤ), τᴴ ⬝ (L.gram ⬝ τ) = ((ε : D.host.E) * (D.host.xi0 * star D.host.xi0)) • L'.gram → ∀ κ : WO S L' → WO L S, (∀ w, κ w = GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L'.rank) ⬝ w)) → (∀ w w', κ (w + w') = κ w + κ w') ∧ Continuous κ ∧ (∀ w ∈ ratMx D L'.rank S.rank, κ w ∈ ratMx D S.rank L.rank) ∧ (∀ (g : GA D S) (w : WO S L'), κ (w ⬝ mt S g⁻¹) = mt S g ⬝ κ w) ∧ (∀ w w', symplO L S (κ w) (κ w') = -((ε : AF D.host.F) * symplO S L' w w')) ∧ (∀ w, (w.map (infPart D) = 0 → (κ w).map (infPart D) = 0) ∧ (w.map (finPart D) = 0 → (κ w).map (finPart D) = 0)) := by
  intro D L L' S τ ε hτ κ hκ
  refine ⟨fun w w' => ?_, ?_, fun w hw => ?_, fun g w => ?_, fun w w' => ?_, fun w => ⟨fun hw => ?_, fun hw => ?_⟩⟩
  · rw [hκ, hκ, hκ, ← ofAdj_add]
    exact congrArg (ofAdj L S) (Matrix.mul_add (rat τ : Mx D L.rank L'.rank) w w')
  · have h : Continuous fun w : Mx D L'.rank S.rank => ((rat τ : Mx D L.rank L'.rank) ⬝ w : Mx D L.rank S.rank) :=
      continuous_const.matrix_mul continuous_id
    rw [funext hκ]
    exact (continuous_ofAdj L S).comp h
  · rw [hκ]
    exact ofAdj_mem L S (ratMx_mul (rat_mem τ) hw)
  · rw [hκ, hκ, ← ofAdj_mul_mt_inv]
    exact congrArg (ofAdj L S) (Matrix.mul_assoc (rat τ : Mx D L.rank L'.rank) w (mt S g⁻¹)).symm
  · rw [hκ, hκ]
    exact symplO_ofAdj L L' S τ ε hτ w w'
  · rw [hκ]
    exact map_ofAdj_eq_zero (infPart D) (fun z hz => by rw [infPart_conj, hz, map_zero]) L S
      (map_mul_eq_zero_right (infPart D) _ hw)
  · rw [hκ]
    exact map_ofAdj_eq_zero (finPart D) (fun z hz => by rw [finPart_conj, hz, map_zero]) L S
      (map_mul_eq_zero_right (finPart D) _ hw)

end GlobalTheory.LinkKappa

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianLinkMapAdditiveRationalEquivariantStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianLinkMap_additive_rational_equivariant : ∀ (D : D7) (L L' S : HSp D) (τ : Matrix (Fin L.rank) (Fin L'.rank) D.host.E) (ε : ℤ), τᴴ ⬝ (L.gram ⬝ τ) = ((ε : D.host.E) * (D.host.xi0 * star D.host.xi0)) • L'.gram → ∀ κ : WO S L' → WO L S, (∀ w, κ w = GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L'.rank) ⬝ w)) → (∀ w w', κ (w + w') = κ w + κ w') ∧ Continuous κ ∧ (∀ w ∈ ratMx D L'.rank S.rank, κ w ∈ ratMx D S.rank L.rank) ∧ (∀ (g : GA D S) (w : WO S L'), κ (w ⬝ mt S g⁻¹) = mt S g ⬝ κ w) ∧ (∀ w w', symplO L S (κ w) (κ w') = -((ε : AF D.host.F) * symplO S L' w w')) ∧ (∀ w, (w.map (infPart D) = 0 → (κ w).map (infPart D) = 0) ∧ (w.map (finPart D) = 0 → (κ w).map (finPart D) = 0)) := by
  first | exact @GlobalTheory.LinkKappa.kappa_props | exact GlobalTheory.LinkKappa.kappa_props | (intros; apply GlobalTheory.LinkKappa.kappa_props <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeCompletionAtPlacesMemCompletedHermitianLa
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeCompletionAtPlacesMemCompletedHermitianLa
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.LatVHat

theorem gen_mem (D : D7) (S : HSp D) (L : Lat S) (α : Af D.host.F) (hα : α ∈ intAf D.host.F) (x : Fin S.rank → D.host.E)
    (hx : x ∈ L) :
    (fun i => Formalism.IndefR.Lev.swapAE D (finPart D ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] ((1 : D.host.E) * x i)))) ∈
      Formalism.L2.Herm.hatL (F := D.host.F) L := by
  have hint : (1 : D.host.E) ⊗ₜ[D.host.F] α ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    apply Subring.subset_closure
    right
    refine ⟨⟨α, ?_⟩, rfl⟩
    intro v
    exact hα v
  have hgen : (fun i => Formalism.UG.inclE (F := D.host.F) (Af D.host.F) (x i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) L :=
    Submodule.subset_span ⟨x, hx, rfl⟩
  have := Submodule.smul_mem _ (⟨_, hint⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) hgen
  convert this using 1
  ext i
  show _ = ((1 : D.host.E) ⊗ₜ[D.host.F] α) * (x i ⊗ₜ[D.host.F] (1 : Af D.host.F))
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  rfl

theorem latV_mem_hatL : ∀ (D : D7) (S : HSp D) (L : Lat S) (P : Pl D → Prop) (y : Fin S.rank → AE D), y ∈ latV S L P →
    (fun i => Formalism.IndefR.Lev.swapAE D (finPart D (y i))) ∈ Formalism.L2.Herm.hatL (F := D.host.F) L := by
  intro D S L P y hy
  let Φ : (Fin S.rank → AE D) →+ (Fin S.rank → Formalism.IndefR.Lev.EAf D) :=
    AddMonoidHom.compLeft ((Formalism.IndefR.Lev.swapAE D).comp (finPart D)).toAddMonoidHom (Fin S.rank)
  have hle : latV S L P ≤ (Formalism.L2.Herm.hatL (F := D.host.F) L).toAddSubgroup.comap Φ := by
    unfold GlobalTheory.FinPl.latV GlobalTheory.FinPl.latMul
    rw [AddSubgroup.closure_le]
    rintro _ ⟨α, hα, -, a, ha, x, hx, rfl⟩
    rw [Set.mem_singleton_iff] at ha
    subst ha
    exact gen_mem D S L α hα x hx
  exact hle hy

end GlobalTheory.LatVHat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeCompletionAtPlacesMemCompletedHermitianLaStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeCompletionAtPlaces_mem_completedHermitianLattice : ∀ (D : D7) (S : HSp D) (L : Lat S) (P : Pl D → Prop) (y : Fin S.rank → AE D), y ∈ latV S L P → (fun i => Formalism.IndefR.Lev.swapAE D (finPart D (y i))) ∈ Formalism.L2.Herm.hatL (F := D.host.F) L := by
  first | exact @GlobalTheory.LatVHat.latV_mem_hatL | exact GlobalTheory.LatVHat.latV_mem_hatL | (intros; apply GlobalTheory.LatVHat.latV_mem_hatL <;> assumption)
end
end
