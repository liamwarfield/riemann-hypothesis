module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DivisionPairOfAdelicFormsFaceColumnsData
public import Formalism.LocalToGlobal.Divisibility.TupUsed
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalSatakeEqLanglandsQuotientUnramified
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedHolomorphicFormEqMultiplicitySpaceValue
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicCuspFormTransvectionConstantTermsZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableAtFoldrLineDer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertModelConjugationAntilinearBijection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesThird
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CopyLIntegral

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowConditionsAtCompanionFromReadings
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3


set_option maxHeartbeats 4000000 in
theorem rowConditions_at_companion_from_readings : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Yd cX) (x : TwIn ex) , (Lam3 x.Z → RowsHoldLam3 (divisionPairOfAdelicFormsFaceColumnsData x)) ∧ RowsHoldDcPt3 (divisionPairOfAdelicFormsFaceColumnsData x) ∧ DcPtG (divisionPairOfAdelicFormsFaceColumnsData x) ∧ (DivRows3 D x.A3 x.F.P0 x.F.ψ0 x.F.P1 x.F.ψ1 (zsOf x.R x.F) (s0Of x.R x.F) (s1Of x.R x.F) ex.p0 (colOf x.R x.F x.sEE) x.C.NuC (idsOf x.cG x.Z x.C) → DivRows3G (divisionPairOfAdelicFormsFaceColumnsData x)) := by
  intro D L hT Gi Gl K Yd cX ex x
  have hD : RowsHoldDcPt3 (divisionPairOfAdelicFormsFaceColumnsData x) := fun u t y F => x.C.pt u t y F
  exact ⟨fun h => h, hD, dcPtG_of hD, fun h => DivRows3.toG (P := divisionPairOfAdelicFormsFaceColumnsData x) h⟩

end GlobalTheory.Mem.R3
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftGroupFormsEqExtendedRationalFormsCompanion
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3.Reads

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {K : Formalism.MainNotions.G.Consts} {Yd : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Yd cX}


set_option maxHeartbeats 2000000 in
theorem liftGroupForms_eq_extended_rationalForms_companion (x : TwIn ex) : Formalism.IndefR.RecTie.MtRead x.R.toRealDat x.F.lv2 x.Y.tupT x.Y.hm x.Y.hTop x.Y.hinj x.Y.IL
    (twPOf (divisionPairOfAdelicFormsFaceColumnsData x) x.Y.tupT x.Y.tupTie) := by
  intro μ hμ i v
  have key : ∀ (t : x.T) (μ : D.what₂.Tup) (e : x.Y.tup t = μ) (hμ : Formalism.IndefR.RecTie.Used0 D μ) (e' : x.Y.tupT μ = t)
      (v : D.what₂.MtL μ ((i : ℕ) + 1)),
      HEq (x.Y.IL.jMt μ hμ i (D.what₂.jMt μ ((i : ℕ) + 1) v)).1
        (x.R.toRealDat.extV i t (x.R.toRealDat.jV i t (liftForm x.A3.A x.F.P0 x.F.ψ0 i t ((x.Y.eMt i t).symm (e.symm ▸ v))))) := by
    intro t μ e hμ e' v
    subst e
    have := x.Y.mtRead i t hμ ((x.Y.eMt i t).symm v)
    rw [LinearEquiv.apply_symm_apply] at this
    exact heq_of_eq this
  have := eq_of_heq (key _ μ (x.Y.tupTie μ hμ) hμ rfl v)
  rw [this]
  unfold twPOf
  rw [dite_eq_left hμ]
  rfl



end GlobalTheory.Mem.R3.Reads

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepVecExists
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceDatum

theorem stepVecExists : ∀ D : D7, StepVecExists D := by
  classical
  intro D ψ θ S T sS sT ΛS ΛT βS βT LS χj Q ξ hS hT _ _ _ ⟨e, he⟩ f₀ hf
  have hinf := infPart_idemSum he
  obtain ⟨K, hK, hC⟩ := exists_nsmul_of_frMapO
    (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull S ΛS hS)
    (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull T ΛT hT) βS βT
  obtain ⟨f, h⟩ := exists_isThetaAt hf.1 hS hT (idemSum_mul_self he) hinf
    (GlobalTheory.PlaceModelSum.placeModelExistsSum D ψ hf.1 S T ΛS ΛT hS hT _ e he f₀ hf.2.theta hf.2.lat).1
    (isSBHalf_of_red e _ (frMapO S T βS βT) (frMapO_add βS βT) (exists_den_frMapO hS.1.fg hT.1.fg βS βT)
      ⟨K, hK, fun t ht => hC t (infPart_of_half hinf ht)⟩ (LS.Pg ∪ Q)
      (fun y => omegaG LS χj y * omegaQ Q LS.r ξ 1 y) fun y y' h => by
        rw [omegaG_congr LS χj y y' fun PP hP => h PP (Finset.mem_union_left _ hP),
          omegaQ_congr Q LS.r ξ 1 y y' fun PP hP => h PP (Finset.mem_union_right _ hP)])
  exact ⟨f, hf, e, he, h⟩

end GlobalTheory.PlaceDatum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdMaximalCompactReductionProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdMaximalCompactReductionProperties
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MtRed

section Split

open ReciprocityTheory.Aut

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (s : SplitPlace E)

theorem i_mem (a : 𝓞 E) : s.i (a : E) ∈ s.v.adicCompletionIntegers (maximalRealSubfield E) :=
  (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (s.split_le_one a)

def iInt : 𝓞 E →+* s.v.adicCompletionIntegers (maximalRealSubfield E) :=
  ((s.i : E →+* s.v.adicCompletion (maximalRealSubfield E)).comp (algebraMap (𝓞 E) E)).codRestrict _ (i_mem s)

theorem mem_max_iff (x : s.v.adicCompletionIntegers (maximalRealSubfield E)) :
    x ∈ IsLocalRing.maximalIdeal (s.v.adicCompletionIntegers (maximalRealSubfield E)) ↔
      Valued.v (x : s.v.adicCompletion (maximalRealSubfield E)) < 1 :=
  Valuation.mem_maximalIdeal_iff _ _

def psiR : 𝓞 E →+* IsLocalRing.ResidueField (s.v.adicCompletionIntegers (maximalRealSubfield E)) :=
  (IsLocalRing.residue _).comp (iInt s)

theorem psiR_eq_zero (a : 𝓞 E) : psiR s a = 0 ↔ a ∈ s.w.asIdeal := by
  rw [psiR, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff, mem_max_iff]
  exact Iff.rfl

theorem psiR_surj : Function.Surjective (psiR s) := by
  intro y
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
  have hx : Valued.v (x : s.v.adicCompletion (maximalRealSubfield E)) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 x.2
  obtain ⟨a, ha⟩ := adic_exists_approx s.v _ hx
  refine ⟨algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) a, ?_⟩
  rw [psiR, RingHom.comp_apply, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, mem_max_iff]
  have e : ((iInt s (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) a) : s.v.adicCompletionIntegers (maximalRealSubfield E)) :
      s.v.adicCompletion (maximalRealSubfield E)) = algebraMap (𝓞 (maximalRealSubfield E)) (s.v.adicCompletion (maximalRealSubfield E)) a := by
    show s.i (((algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) a : 𝓞 E)) : E) = _
    rw [split_coe_algebraMap, AlgHom.commutes]; rfl
  rw [AddSubgroupClass.coe_sub, e, Valuation.map_sub_swap]
  exact ha

def kEqv : kP s.w ≃+* IsLocalRing.ResidueField (s.v.adicCompletionIntegers (maximalRealSubfield E)) :=
  RingEquiv.ofBijective (Ideal.Quotient.lift s.w.asIdeal (psiR s) fun a ha => (psiR_eq_zero s a).2 ha)
    ⟨by
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro q hq
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
      rw [Ideal.Quotient.lift_mk, psiR_eq_zero] at hq
      exact Ideal.Quotient.eq_zero_iff_mem.2 hq,
    fun y => by
      obtain ⟨a, rfl⟩ := psiR_surj s y
      exact ⟨Ideal.Quotient.mk s.w.asIdeal a, Ideal.Quotient.lift_mk _ _ _⟩⟩

def phiR : s.v.adicCompletionIntegers (maximalRealSubfield E) →+* kP s.w :=
  ((kEqv s).symm : _ →+* kP s.w).comp (IsLocalRing.residue _)

theorem phiR_surj : Function.Surjective (phiR s) :=
  (kEqv s).symm.surjective.comp IsLocalRing.residue_surjective

theorem phiR_eq_zero (x : s.v.adicCompletionIntegers (maximalRealSubfield E)) :
    phiR s x = 0 ↔ Valued.v (x : s.v.adicCompletion (maximalRealSubfield E)) < 1 := by
  rw [phiR, RingHom.comp_apply, RingEquiv.coe_toRingHom, map_eq_zero_iff _ (kEqv s).symm.injective,
    IsLocalRing.residue_eq_zero_iff, mem_max_iff]

theorem kEqv_mk (a : 𝓞 E) : kEqv s (Ideal.Quotient.mk s.w.asIdeal a) = psiR s a :=
  Ideal.Quotient.lift_mk s.w.asIdeal (psiR s) (fun a ha => (psiR_eq_zero s a).2 ha)

theorem phiR_i (a : 𝓞 E) : phiR s ⟨_, i_mem s a⟩ = Ideal.Quotient.mk s.w.asIdeal a := by
  rw [phiR, RingHom.comp_apply, RingEquiv.coe_toRingHom, RingEquiv.symm_apply_eq]
  rw [kEqv_mk]; rfl

theorem exists_approx (x : s.v.adicCompletionIntegers (maximalRealSubfield E)) :
    ∃ a : 𝓞 E, Valued.v ((x : s.v.adicCompletion (maximalRealSubfield E)) - s.i (a : E)) < 1 ∧
      phiR s x = Ideal.Quotient.mk s.w.asIdeal a := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (I := s.w.asIdeal) (phiR s x)
  refine ⟨a, ?_, ha.symm⟩
  have h : phiR s (x - ⟨_, i_mem s a⟩) = 0 := by
    rw [map_sub, phiR_i, ha, sub_self]
  have h2 := (phiR_eq_zero s _).1 h
  rwa [AddSubgroupClass.coe_sub] at h2

end Split

end GlobalTheory.MtRed

end

noncomputable section

namespace GlobalTheory.MtRed

variable (D : D7) (n : ℕ)

theorem km_mem_UA (κ : Formalism.AUTREP.GAf D.host.E n) : km D n κ ∈ UA D.sp.cm (1 : Matrix (Fin n) (Fin n) D.host.E) := by
  show Formalism.UG.cT (GlobalTheory.StdFrameExist.sgA D) (GlobalTheory.StdFrameExist.kmat κ).1 *
      (1 : Matrix (Fin n) (Fin n) D.host.E).map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) *
      (GlobalTheory.StdFrameExist.kmat κ).1 = (1 : Matrix (Fin n) (Fin n) D.host.E).map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F))
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, GlobalTheory.StdFrameExist.cT_kmat]

theorem km_mem_St_iff (κ : Formalism.AUTREP.GAf D.host.E n) :
    km D n κ ∈ Formalism.L2.DIV.St (1 : GL (Fin n) (EAf D)) ↔ κ ∈ ReciprocityTheory.Aut.Umax D.host.E n := by
  rw [GlobalTheory.StdFrameExist.mem_Umax_iff]
  constructor
  · rintro ⟨y, hy⟩ i j
    have e : (GlobalTheory.StdFrameExist.kmat κ).1 i j = ((y.1 i j : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) := by
      show (km D n κ).1 i j = _
      rw [← hy]
      simp [frGL, intGL, Formalism.UG.bc]
    rw [e]
    exact (y.1 i j).2
  · intro h
    have h' : GlobalTheory.StdFrameExist.IntM (GlobalTheory.StdFrameExist.SI D) (GlobalTheory.StdFrameExist.kmat κ⁻¹).1 :=
      (GlobalTheory.StdFrameExist.mem_Umax_iff _).1 (inv_mem ((GlobalTheory.StdFrameExist.mem_Umax_iff κ).2 h))
    have hm : (GlobalTheory.StdFrameExist.kmat κ).1 * (GlobalTheory.StdFrameExist.kmat κ⁻¹).1 = 1 := by
      rw [GlobalTheory.StdFrameExist.kmat_inv, Units.mul_inv]
    have hm' : (GlobalTheory.StdFrameExist.kmat κ⁻¹).1 * (GlobalTheory.StdFrameExist.kmat κ).1 = 1 := by
      rw [GlobalTheory.StdFrameExist.kmat_inv, Units.inv_mul]
    refine ⟨⟨Matrix.of fun i j => ⟨_, h i j⟩, Matrix.of fun i j => ⟨_, h' i j⟩, ?_, ?_⟩, ?_⟩
    · ext i j
      have := congrFun (congrFun hm i) j
      rw [Matrix.mul_apply] at this
      rw [Matrix.mul_apply]
      push_cast
      show ∑ x, (GlobalTheory.StdFrameExist.kmat κ).1 i x * (GlobalTheory.StdFrameExist.kmat κ⁻¹).1 x j = _
      rw [this, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    · ext i j
      have := congrFun (congrFun hm' i) j
      rw [Matrix.mul_apply] at this
      rw [Matrix.mul_apply]
      push_cast
      show ∑ x, (GlobalTheory.StdFrameExist.kmat κ⁻¹).1 i x * (GlobalTheory.StdFrameExist.kmat κ).1 x j = _
      rw [this, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    · apply Units.ext
      ext i j
      simp [frGL, intGL, Formalism.UG.bc]
      rfl

theorem red_eq_one (κ : Formalism.AUTREP.GAf D.host.E n) (hκ : κ ∈ ReciprocityTheory.Aut.Umax D.host.E n)
    (A : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)))) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)))
    (PP : Pl D.host.E) (hT : ReciprocityTheory.Aut.TrivOutside A κ) (hP : NG.OverPl PP v) (hv : v ∉ A) :
    redFn (1 : GL (Fin n) (EAf D)) PP (km D n κ) = 1 := by
  refine Formalism.L2.DIV.reduction_local D.host.F D.host.E n 1 PP v hP.symm _ ((km_mem_St_iff D n κ).2 hκ) ?_
  have h := hT v hv
  apply Units.ext
  ext i j
  have e := congrFun (congrFun h i) j
  rw [Matrix.map_apply] at e
  exact e

end GlobalTheory.MtRed

end

noncomputable section

namespace GlobalTheory.MtRed

variable (D : D7) (n : ℕ)

theorem red_split (κ : Formalism.AUTREP.GAf D.host.E n) (hκ : κ ∈ ReciprocityTheory.Aut.Umax D.host.E n)
    (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (a b : Fin n) :
    ∃ h : (s.loc n κ).val a b ∈ s.v.adicCompletionIntegers (maximalRealSubfield D.host.E),
      (redFn (1 : GL (Fin n) (EAf D)) s.w (km D n κ)).val a b = phiR s ⟨_, h⟩ := by
  obtain ⟨y, hy⟩ := (km_mem_St_iff D n κ).2 hκ
  have hz : (κ.1.val a b) ∈ ReciprocityTheory.Aut.ALint D.host.E := hκ a b
  have hz' := GlobalTheory.RowGood.tr_int rfl hz
  rw [GlobalTheory.RowGood.tr_rfl] at hz'
  have hmem : (s.loc n κ).val a b ∈ s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (GlobalTheory.RowGood.proj_le_one s hz')
  refine ⟨hmem, ?_⟩
  obtain ⟨c, hc, hφ⟩ := exists_approx s ⟨_, hmem⟩
  rw [hφ]
  have hyab : ((y.val a b : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) = κ.1.val a b := by
    have e : (km D n κ).1 a b = ((y.1 a b : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) := by
      rw [← hy]
      simp [frGL, intGL, Formalism.UG.bc]
    exact e.symm
  rw [← hy, redFn_frGL]
  have := GlobalTheory.RowGood.res_eq (rfl : maximalRealSubfield D.host.E = _) s (κ.1.val a b) (y.val a b)
    (by rw [GlobalTheory.RowGood.tr_rfl]; exact hyab) c hc
  exact this

end GlobalTheory.MtRed

end

namespace GlobalTheory.MtRed

theorem km_reduction : ∀ (D : D7) (n : ℕ), (∀ κ, km D n κ ∈ UA D.sp.cm (1 : Matrix (Fin n) (Fin n) D.host.E)) ∧ (∀ κ, km D n κ ∈ Formalism.L2.DIV.St (1 : GL (Fin n) (EAf D)) ↔ κ ∈ ReciprocityTheory.Aut.Umax D.host.E n) ∧ (∀ κ ∈ ReciprocityTheory.Aut.Umax D.host.E n, ∀ (A : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)))) (v) (PP : Pl D.host.E), ReciprocityTheory.Aut.TrivOutside A κ → NG.OverPl PP v → v ∉ A → redFn (1 : GL (Fin n) (EAf D)) PP (km D n κ) = 1) ∧ ∀ s : ReciprocityTheory.Aut.SplitPlace D.host.E, ∃ φ : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) →+* kP s.w, Function.Surjective φ ∧ (∀ x, φ x = 0 ↔ Valued.v (x : s.v.adicCompletion (maximalRealSubfield D.host.E)) < 1) ∧ (∀ a : 𝓞 D.host.E, ∃ h : s.i (a : D.host.E) ∈ s.v.adicCompletionIntegers (maximalRealSubfield D.host.E), φ ⟨_, h⟩ = Ideal.Quotient.mk _ a) ∧ ∀ κ ∈ ReciprocityTheory.Aut.Umax D.host.E n, ∀ a b, ∃ h : (s.loc n κ).val a b ∈ s.v.adicCompletionIntegers (maximalRealSubfield D.host.E), (redFn (1 : GL (Fin n) (EAf D)) s.w (km D n κ)).val a b = φ ⟨_, h⟩ := by
  intro D n
  exact ⟨km_mem_UA D n, km_mem_St_iff D n, fun κ hκ A v PP hT hP hv => red_eq_one D n κ hκ A v PP hT hP hv,
    fun s => ⟨phiR s, phiR_surj s, phiR_eq_zero s, fun a => ⟨i_mem s a, phiR_i s a⟩,
      fun κ hκ a b => red_split D n κ hκ s a b⟩⟩

end GlobalTheory.MtRed
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdMaximalCompactReductionPropertiesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stdMaximalCompact_reduction_properties : ∀ (D : D7) (n : ℕ), (∀ κ, km D n κ ∈ UA D.sp.cm (1 : Matrix (Fin n) (Fin n) D.host.E)) ∧ (∀ κ, km D n κ ∈ Formalism.L2.DIV.St (1 : GL (Fin n) (EAf D)) ↔ κ ∈ ReciprocityTheory.Aut.Umax D.host.E n) ∧ (∀ κ ∈ ReciprocityTheory.Aut.Umax D.host.E n, ∀ (A : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)))) (v) (PP : Pl D.host.E), ReciprocityTheory.Aut.TrivOutside A κ → NG.OverPl PP v → v ∉ A → redFn (1 : GL (Fin n) (EAf D)) PP (km D n κ) = 1) ∧ ∀ s : ReciprocityTheory.Aut.SplitPlace D.host.E, ∃ φ : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) →+* kP s.w, Function.Surjective φ ∧ (∀ x, φ x = 0 ↔ Valued.v (x : s.v.adicCompletion (maximalRealSubfield D.host.E)) < 1) ∧ (∀ a : 𝓞 D.host.E, ∃ h : s.i (a : D.host.E) ∈ s.v.adicCompletionIntegers (maximalRealSubfield D.host.E), φ ⟨_, h⟩ = Ideal.Quotient.mk _ a) ∧ ∀ κ ∈ ReciprocityTheory.Aut.Umax D.host.E n, ∀ a b, ∃ h : (s.loc n κ).val a b ∈ s.v.adicCompletionIntegers (maximalRealSubfield D.host.E), (redFn (1 : GL (Fin n) (EAf D)) s.w (km D n κ)).val a b = φ ⟨_, h⟩ := by
  first | exact @GlobalTheory.MtRed.km_reduction | exact GlobalTheory.MtRed.km_reduction | (intros; apply GlobalTheory.MtRed.km_reduction <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JEvExistsAndJEvBar
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CuspValues

theorem evEx_of_range {K C H X : Type} [Field K] [AddCommGroup C] [Module K C] [AddCommGroup H] [Module ℂ H]
    [AddCommGroup X] [Module ℂ X] (σ : K →+* ℂ) (ev : H →ₗ[ℂ] X) (hinj : Function.Injective ev) (φ : C →ₛₗ[σ] X)
    (h : ∀ f, φ f ∈ LinearMap.range ev) : EvEx σ ev φ := by
  choose x hx using h
  refine ⟨⟨⟨x, fun f f' => hinj ?_⟩, fun a f => hinj ?_⟩, hx⟩
  · rw [map_add (f := _), hx, hx, hx, map_add (f := _)]
  · exact (hx _).trans (by rw [φ.map_smulₛₗ, map_smul, hx])

theorem phiC_eq {D : D7} (T : CoreJ D) {j : ℕ} {σ : T.Q.c.F →+* ℂ} {W : HSp D} (hV : T.V j σ = W)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) :
    phiC T hV a f = (lieFac (T.Q.Dw j) (xiR D) a : ℂ) •
      adel W (castDict hV (T.dict j σ)) (muPin W (castDict hV (T.dict j σ)) (castDict hV (T.mu j σ)) (T.cE j σ))
        (rdU (T.U j σ) f) := by
  subst hV
  rfl

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

noncomputable def evLin {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
    (σ : D.what₂.LL →+* ℂ) (v : (R.MW i σ).Vec) : (R.HW i σ).H →ₗ[ℂ] (GA D (Wc D i) → ℂ) where
  toFun := evAt R i σ v
  map_add' a b := by simp [evAt]
  map_smul' c a := by simp [evAt]


set_option maxHeartbeats 1000000 in
theorem jEvExists (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
    (hL : R.toLevCh.Is A.μ0) (hM : R.IsModels) (ht : TieIn T R κ v₀) (hp : T.pb = R.C.P.pb) : JEvExists T R κ v₀ := by
  intro i σ hσ hV
  obtain ⟨hsh, -, w, hw⟩ := GlobalTheory.T.holomorphicShape_integralWeight_goodEmbedding D G Pl0 T0 A T R κ v₀ ht i σ hσ
  have hg := GlobalTheory.T.coreDictionary_good_at_good_embedding D G Pl0 T0 A T R κ v₀ hL hM ht hp i σ hσ hV w hw
  obtain ⟨-, hχ, hfin, -⟩ := GlobalTheory.T.realisation_principalLevel_eq_coreLevel_open D G Pl0 T0 A T R κ v₀ hL hM ht hp i σ hσ hV
  have hinj : Function.Injective (evLin R i σ (v₀ i σ)) :=
    GlobalTheory.EvalAtUnitVector.evInj T R v₀ hM.HW ht.hv₀ i σ hσ
  let ad := adel (Wc D i) (castDict hV (T.dict ((i : ℕ) + 1) (res T σ)))
    (muPin (Wc D i) (castDict hV (T.dict ((i : ℕ) + 1) (res T σ))) (castDict hV (T.mu ((i : ℕ) + 1) (res T σ)))
      (T.cE ((i : ℕ) + 1) (res T σ)))
  have key : holSub (T.U ((i : ℕ) + 1) (res T σ)).X (laU (T.U ((i : ℕ) + 1) (res T σ)) (wtA (κ i)) (κ i).n) ≤
      (LinearMap.range (evLin R i σ (v₀ i σ))).comap ad := by
    refine Submodule.span_le.2 fun P hP => ?_
    have h1 := GlobalTheory.T.holomorphicAdelicForm_of_boundedSection D R.θ _ _ _ w _ _ _ _ _ _ _ _ _ hsh hg P fun k => (hP k).1
    have h2 := GlobalTheory.T.adelicCuspForm_transvection_constantTerms_zero D R.θ _ _ _ w _ _ _ _ _ _ _ _ _ hsh hg P hP
    have h3 : GlobalTheory.HolDict.HolForm R.θ (R.MW i σ) w (levS _ (R.βW i) (R.datWp i R.triv))
        (Lev.levChi _ (R.βW i) (R.datWp i R.triv)) (ad P) :=
      ⟨h1.aut, h1.bdd, fun k hk g => by rw [hχ k hk]; exact h1.lev k hk g, h1.hol⟩
    obtain ⟨Tm, hT, hTv⟩ := GlobalTheory.T.boundedHolomorphicForm_eq_multiplicitySpace_value D R.θ _ _ (R.MW i σ) w (v₀ i σ) hM.inf hsh hw (ht.hv₀ i σ).1
      (GlobalTheory.HolDict.exists_finPair GlobalTheory.Mem.VolFin.finVol D _) _ _ _ hfin h3 h2
    have hmem : Tm ∈ R.Wall i σ := Submodule.subset_span hT
    rw [← (hM.HW i σ).2.1] at hmem
    obtain ⟨x, rfl⟩ := hmem
    exact ⟨x, hTv⟩
  let φ : Cu T κ i →ₛₗ[res T σ] (GA D (Wc D i) → ℂ) :=
    ((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) • ad).comp
      ((rdU (T.U ((i : ℕ) + 1) (res T σ))).comp (T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n).subtype)
  have h := evEx_of_range (res T σ) _ hinj φ fun f =>
    Submodule.smul_mem _ _ (key (((mem_cusp _ _ _ _ _ _).1 f.2).2 _ hσ))
  obtain ⟨j, hj⟩ := h
  exact ⟨j, fun f => (hj f).trans (phiC_eq T hV _ _).symm⟩

theorem jEvExists_and_jEvBar : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → R.IsModels → TieIn T R κ v₀ → T.pb = R.C.P.pb → JEvExists T R κ v₀ ∧ JEvBar T R κ := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ hL hM ht hp
  have h := jEvExists T R κ v₀ hL hM ht hp
  exact ⟨h, (GlobalTheory.T.hilbertModel_conjugation_antilinear_bijection D G Pl0 T0 A T R κ v₀ hM ht).2 h⟩

end GlobalTheory.CuspValues
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFormPeriodRelation
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

namespace GlobalTheory.OneMapRef.ClassScalar

open GlobalTheory.Ker

variable {D : D7}

theorem fmt_mul_inv (V : HSp D) (g : GA D V) : fmt V g * fmt V g⁻¹ = 1 := by
  simp only [fmt, Formalism.L2.Theta.mt]
  rw [← Matrix.map_mul, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem isMov_hLat (V : HSp D) (hL : Bridge.hLat V 1 = stdL D.host.E V.rank) (g : GA D V) :
    IsMov (fmt V g) (stdL D.host.E V.rank) (Bridge.hLat V (fin V g)) := by
  have hs : Submodule.span D.host.E (stdL D.host.E V.rank : Set (Fin V.rank → D.host.E)) = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun D.host.E (Fin V.rank)).span_eq]
    refine Submodule.span_mono ?_
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨i, (Pi.basisFun_apply _ _ i).symm⟩
  obtain ⟨⟨L, hL', hm⟩, h2⟩ := (isMov_laws D V.rank _ ⟨Submodule.fg_span (Set.finite_range _), hs⟩).2.2.2 _ _
    (fmt_mul_inv V g)
  have h3 := (isMov_laws D V.rank L hL').1
  have h4 : fmt V g⁻¹ * fmt V g = 1 := mul_eq_one_comm.1 (fmt_mul_inv V g)
  have key : Bridge.hLat V (fin V g) = L := by
    rw [Bridge.hLat, ← GlobalTheory.Equiv.StdSpace.identityClassLattice_eq_selfDualFrameLattice, hL, ← Submodule.span_eq L]
    congr 1
    ext x
    change fmt V g⁻¹ *ᵥ toAf x ∈ hatV (stdL D.host.E V.rank) ↔ x ∈ L
    rw [← h3, hm]
    constructor
    · intro hx
      exact ⟨_, hx, by rw [Matrix.mulVec_mulVec, fmt_mul_inv, Matrix.one_mulVec]⟩
    · rintro ⟨u, hu, e⟩
      rwa [e, Matrix.mulVec_mulVec, h4, Matrix.one_mulVec]
  rwa [key]

noncomputable abbrev cf (D : D7) : AfE D →+* AfE D := sigR (Af D.host.F) D.sp.cm.sig

theorem cf_cf (x : AfE D) : cf D (cf D x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero]
  | tmul a x => exact congrArg (fun t => a ⊗ₜ[D.host.F] t) (star_star x)
  | add x y hx hy => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), hx, hy]

theorem finPart_cA (x : AE D) : finPart D (cA D x) = cf D (finPart D x) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero, RingHom.map_zero]
  | tmul a x => rfl
  | add x y hx hy => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), RingHom.map_add (f := _), RingHom.map_add (f := _), hx, hy]

theorem conj_mem_hatV {k : ℕ} {L L' : Lt D.host.E k} (h : ∀ v ∈ L, (fun j => cc (v j)) ∈ L') {u : Fin k → AfE D}
    (hu : u ∈ hatV L) : cf D ∘ u ∈ hatV L' := by
  induction hu using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hy
    exact AddSubgroup.subset_closure ⟨a, ha, _, h x hx, rfl⟩
  | zero => convert (hatV L').zero_mem; funext i; exact RingHom.map_zero _
  | add a b _ _ ha hb => convert add_mem ha hb; funext i; exact RingHom.map_add _ _ _
  | neg a _ ha => convert neg_mem ha; funext i; exact RingHom.map_neg _ _

theorem isMov_conj {V : HSp D} {g : GA D V} {L L' : Lt D.host.E V.rank} (h : IsMov (fmt V g) (stdL D.host.E V.rank) L)
    (hc : ∀ v, v ∈ L' ↔ (fun j => cc (v j)) ∈ L) : IsMov (fmtC V g) (stdL D.host.E V.rank) L' := by
  have c4 : fmtC V g = (fmt V g).map (cf D) := by ext i j; exact finPart_cA _
  have c5 : ∀ v ∈ stdL D.host.E V.rank, (fun j => cc (v j)) ∈ stdL D.host.E V.rank := fun v hv => by
    rw [← GenLatCmp.std_eq, GenLatCmp.mem_std] at hv ⊢
    exact fun i => Base.isIntegral_cc (hv i)
  have c6 (u : Fin V.rank → AfE D) : cf D ∘ cf D ∘ u = u := funext fun i => cf_cf _
  have c7 (u : Fin V.rank → AfE D) : fmtC V g *ᵥ (cf D ∘ u) = cf D ∘ (fmt V g *ᵥ u) := by
    rw [c4]; funext i; exact (RingHom.map_mulVec (cf D) _ _ i).symm
  intro u
  constructor
  · intro hu
    obtain ⟨u₀, h0, e⟩ := (h _).1 (conj_mem_hatV (fun v hv => (hc v).1 hv) hu)
    exact ⟨_, conj_mem_hatV c5 h0, by rw [c7, ← e, c6]⟩
  · rintro ⟨u₀, h0, rfl⟩
    rw [← c6 u₀, c7]
    refine conj_mem_hatV (fun v hv => (hc _).2 ?_) ((h _).2 ⟨_, conj_mem_hatV c5 h0, rfl⟩)
    simpa [cc] using hv

theorem exists_isDetAt {e : AE D} (he : e * e = e) (V : HSp D) (g : GA D V) : ∃ y, IsDetAt e V g y :=
  ⟨Units.mkOfMulEqOne (e * (Formalism.L2.Theta.mt V g).det + (1 - e)) (e * cA D (Formalism.L2.Theta.mt V g).det + (1 - e)) (by
    linear_combination (e * e) * det_conj_mul V g +
      (2 - (Formalism.L2.Theta.mt V g).det - cA D (Formalism.L2.Theta.mt V g).det) * he), Units.val_mkOfMulEqOne _⟩


end GlobalTheory.OneMapRef.ClassScalar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSignatureDataSpan
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseChangeInfLatticeEqSubspace
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseChangeInfLatticeEqSubspace
open scoped TensorProduct

namespace GlobalTheory

theorem baseChange_inf_lattice_eq_subspace : ∀ {O V : Type} [CommRing O] [IsDomain O] [AddCommGroup V]
    [Module (FractionRing O) V] [Module O V]
    [IsScalarTower O (FractionRing O) V] (N : Submodule O V),
    Submodule.span (FractionRing O) (N : Set V) = ⊤ → ∀ (W : Submodule (FractionRing O) V),
    ∃ e : FractionRing O ⊗[O] ↥(N ⊓ W.restrictScalars O) →ₗ[FractionRing O] V,
      Function.Injective e ∧ LinearMap.range e = W ∧
      ∀ (c : FractionRing O) (x : ↥(N ⊓ W.restrictScalars O)), e (c ⊗ₜ[O] x) = c • (x : V) := by
  intro O V _ _ _ _ _ _ N hN W
  set K := FractionRing O
  have hV : IsBaseChange K (LinearMap.id : V →ₗ[O] V) :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors O) K _).1
      (isLocalizedModule_id (nonZeroDivisors O) V K)
  have hVt : ∀ (c : K) (v : V), hV.equiv (c ⊗ₜ[O] v) = c • v := fun c v => by
    rw [IsBaseChange.equiv_tmul]; rfl

  let fN : K ⊗[O] N →ₗ[K] V := hV.equiv.toLinearMap ∘ₗ N.subtype.baseChange K
  have hfN : ∀ y : N, fN (1 ⊗ₜ y) = y := fun y => by simp [fN, hVt]
  have hinjN : Function.Injective fN := hV.equiv.injective.comp
    (Module.Flat.lTensor_preserves_injective_linearMap (M := K) N.subtype N.injective_subtype)
  have hsurjN : Function.Surjective fN := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hN, Submodule.span_le]
    exact fun y hy => ⟨1 ⊗ₜ ⟨y, hy⟩, hfN _⟩
  have hbN : IsBaseChange K N.subtype :=
    IsBaseChange.of_equiv (LinearEquiv.ofBijective fN ⟨hinjN, hsurjN⟩) (fun y => hfN y)
  haveI hlN : IsLocalizedModule (nonZeroDivisors O) N.subtype :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors O) K N.subtype).2 hbN

  set N' := N ⊓ W.restrictScalars O
  let e : K ⊗[O] N' →ₗ[K] V := hV.equiv.toLinearMap ∘ₗ N'.subtype.baseChange K
  have het : ∀ (c : K) (x : N'), e (c ⊗ₜ[O] x) = c • (x : V) := fun c x => by
    simp [e, hVt]
  refine ⟨e, hV.equiv.injective.comp
    (Module.Flat.lTensor_preserves_injective_linearMap (M := K) N'.subtype N'.injective_subtype), ?_, het⟩
  apply le_antisymm
  · rintro _ ⟨t, rfl⟩
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul c x => rw [het]; exact W.smul_mem c x.2.2
    | add a b ha hb => rw [map_add (f := _)]; exact W.add_mem ha hb
  · intro v hv
    obtain ⟨⟨n, d⟩, hd⟩ := IsLocalizedModule.surj (nonZeroDivisors O) N.subtype v
    have hdv : (d : O) • v = (n : V) := hd
    have hdK : (d : O) • v = algebraMap O K d • v := (algebraMap_smul K (d : O) v).symm
    have hW : (n : V) ∈ W := by rw [← hdv, hdK]; exact W.smul_mem _ hv
    have hne : algebraMap O K d ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2
    refine ⟨(algebraMap O K d)⁻¹ ⊗ₜ[O] (⟨n, n.2, hW⟩ : N'), ?_⟩
    rw [het]
    show (algebraMap O K d)⁻¹ • (n : V) = v
    rw [← hdv, hdK, smul_smul, inv_mul_cancel₀ hne, one_smul]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseChangeInfLatticeEqSubspaceStatement
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_injective_baseChange_inf_restrictScalars_range_eq : ∀ {O V : Type} [CommRing O] [IsDomain O] [AddCommGroup V] [Module (FractionRing O) V] [Module O V]
    [IsScalarTower O (FractionRing O) V] (N : Submodule O V),
    Submodule.span (FractionRing O) (N : Set V) = ⊤ → ∀ (W : Submodule (FractionRing O) V),
    ∃ e : FractionRing O ⊗[O] ↥(N ⊓ W.restrictScalars O) →ₗ[FractionRing O] V,
      Function.Injective e ∧ LinearMap.range e = W ∧
      ∀ (c : FractionRing O) (x : ↥(N ⊓ W.restrictScalars O)), e (c ⊗ₜ[O] x) = c • (x : V) := by
  first | exact @GlobalTheory.baseChange_inf_lattice_eq_subspace | exact GlobalTheory.baseChange_inf_lattice_eq_subspace | (intros; apply GlobalTheory.baseChange_inf_lattice_eq_subspace <;> assumption)
end
end

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX
  GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.HeightCounting.FormsStep

theorem eigenvalue_integral_of_baseChange {O M : Type} [CommRing O] [IsDomain O] [IsIntegrallyClosed O]
    [AddCommGroup M] [Module O M] [Module.Finite O M] (f : Module.End O M)
    (x : FractionRing O ⊗[O] M) (hx : x ≠ 0) (c : FractionRing O)
    (h : f.baseChange (FractionRing O) x = c • x) : ∃ a : O, algebraMap O (FractionRing O) a = c := by
  obtain ⟨p, hp, hpf⟩ := LinearMap.exists_monic_and_aeval_eq_zero O f
  have hev : (Module.End.baseChangeHom O (FractionRing O) M f).HasEigenvector c x :=
    ⟨Module.End.mem_eigenspace_iff.mpr h, hx⟩
  have key := Module.End.aeval_apply_of_hasEigenvector (p := p.map (algebraMap O (FractionRing O))) hev
  rw [Polynomial.aeval_map_algebraMap, Polynomial.aeval_algHom_apply, hpf, map_zero,
    Polynomial.eval_map_algebraMap] at key
  have h0 : Polynomial.aeval c p = 0 := by
    by_contra hne
    exact hx ((smul_eq_zero.mp key.symm).resolve_left hne)
  exact IsIntegrallyClosed.isIntegral_iff.mp ⟨p, hp, by rwa [← Polynomial.aeval_def]⟩

section SigMake

variable (D : D7) (T : TwR D.LL0 D.nd) {S : RatDat D.ntw} (In : RatIn D S)

def sigVal (i : T.Tw) (k : ℕ) (P : PlE D.host) : Prop :=
  1 ≤ k ∧ k ≤ D.R.r ∧ IsSplitPl D.host P ∧ P ∉ T.S0 i

def sigLam (i : T.Tw) (j : ℕ) (b : Bool) (σ : D.what₂.FT) (k : ℕ) (P : PlE D.host) : FractionRing (T.O i) :=
  algebraMap (T.O i) (FractionRing (T.O i)) (cHkT D T i b P : T.O i) ^ k * readT D T i b (In.eig j σ k P)

def SigIdx (i : T.Tw) : Type :=
  {x : Fin (D.R.m + 1) × Bool × D.what₂.FT // 1 ≤ (x.1 : ℕ) ∧ D.what₂.isot (x.1 : ℕ) x.2.2 ≠ ⊥ ∧ D.nd.goodRow x.2.2 ∧
    ∀ k P, sigVal D T i k P → ∃ a : T.O i, algebraMap (T.O i) (FractionRing (T.O i)) a = sigLam D T In i x.1 x.2.1 x.2.2 k P}

instance finSigIdx (i : T.Tw) : Finite (SigIdx D T In i) := Subtype.finite


open Classical in
def sigEig (i : T.Tw) (x : SigIdx D T In i) (k : ℕ) (P : PlE D.host) : T.O i :=
  if h : sigVal D T i k P then (x.2.2.2.2 k P h).choose else 1

theorem sigEig_on (i : T.Tw) (x : SigIdx D T In i) (k : ℕ) (P : PlE D.host) (h : sigVal D T i k P) :
    algebraMap (T.O i) (FractionRing (T.O i)) (sigEig D T In i x k P) = sigLam D T In i x.1.1 x.1.2.1 x.1.2.2 k P := by
  unfold sigEig
  rw [dite_eq_left h]
  exact (x.2.2.2.2 k P h).choose_spec

theorem sigEig_off (i : T.Tw) (x : SigIdx D T In i) (k : ℕ) (P : PlE D.host) (h : ¬ sigVal D T i k P) :
    sigEig D T In i x k P = 1 := by
  unfold sigEig
  rw [dite_eq_right h]

def sigSys (i : T.Tw) (x : SigIdx D T In i) : ℕ × Bool × (ℕ → PlE D.host → T.O i) :=
  ((x.1.1 : ℕ), x.1.2.1, sigEig D T In i x)

def sigDataOf : SigData D T where
  Sig i := ↥(Set.range (sigSys D T In i))
  fin i := @Fintype.ofFinite _ (Set.finite_range (sigSys D T In i)).to_subtype
  jS i s := s.1.1
  jS_range i s := by
    obtain ⟨x, hx⟩ := s.2
    rw [← hx]
    exact ⟨x.2.1, Nat.lt_succ_iff.mp x.1.1.2⟩
  side i s := s.1.2.1
  hEig i s := s.1.2.2
  rowS i s := s.2.choose.1.2.2

end SigMake

theorem sigDataOf_spec (D : D7) (T : TwR D.LL0 D.nd) {S : RatDat D.ntw} (In : RatIn D S) (i : T.Tw)
    (s : (sigDataOf D T In).Sig i) :
    sigSys D T In i s.2.choose = s.1 := s.2.choose_spec

theorem hkB_coe_of_val (D : D7) (T : TwR D.LL0 D.nd) {S : RatDat D.ntw} (In : RatIn D S) (hst : HkStab D T S In)
    (i : T.Tw) (j : ℕ) (b : Bool) (k : ℕ) (P : PlE D.host) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (hv : sigVal D T i k P)
    (x : ↥(BI D T S In i j b)) :
    ((hkB D T S In hst i j b k P x : ↥(BI D T S In i j b)) : FmT D T S i j b) = hkT D T S In i j b k P x := by
  unfold hkB
  rw [dite_eq_left ⟨h1, h2, hv⟩]
  rfl

end GlobalTheory.HeightCounting.FormsStep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TranslatedStdLatticeLatticeComparisonRational
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TranslatedStdLatticeLatticeComparisonRational
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open Matrix

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.HLatStd

variable {D : D7} {V : HSp D}

def invM (h : Bridge.Gf V) : Matrix (Fin V.rank) (Fin V.rank) (EAf D) :=
  (Units.val ((h⁻¹ : Bridge.Gf V) : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E))).map (swapAE D)

def iv (x : Fin V.rank → D.host.E) : Fin V.rank → EAf D := fun i => x i ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F)

theorem mem_set_iff (hV : Seed.FrmC.StdLat V) (h : Bridge.Gf V) (x : Fin V.rank → D.host.E) :
    (Units.val ((h⁻¹ : Bridge.Gf V) : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E))).mulVec
          (fun i => (1 : Af D.host.F) ⊗ₜ[D.host.F] x i) ∈ latHat D.host.F D.host.E (L0c D V) ↔
      ∀ i, (invM h *ᵥ iv x) i ∈ GlobalTheory.StdFrameExist.SI D := by
  rw [GlobalTheory.StdFrameExist.latHat_iff hV]
  refine forall_congr' fun i => ?_
  rw [RingHom.map_mulVec]
  rfl

theorem iv_natCast_smul (N : ℕ) (x : Fin V.rank → D.host.E) : iv ((N : D.host.E) • x) = (N : EAf D) • iv x := by
  funext i
  simp only [iv, Pi.smul_apply, smul_eq_mul]
  rw [← map_natCast (Algebra.TensorProduct.includeLeftRingHom (R := D.host.F) (A := D.host.E)
    (B := Formalism.L2.Herm.Af D.host.F)) N]
  rw [Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one]

theorem iv_mem_of_int {x : Fin V.rank → D.host.E} (hx : ∀ i, IsIntegral ℤ (x i)) (i : Fin V.rank) :
    iv x i ∈ GlobalTheory.StdFrameExist.SI D := by
  obtain ⟨o, ho⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 D.host.E)).1 (hx i)
  show x i ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F) ∈ _
  rw [← ho]
  exact GlobalTheory.StdFrameExist.tmul_one_mem o

theorem int_of_iv_mem {e : D.host.E} (he : (e ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F) : EAf D) ∈ GlobalTheory.StdFrameExist.SI D) :
    IsIntegral ℤ e := by
  rw [← GlobalTheory.StdFrameExist.mem_ALint_iff] at he
  exact GlobalTheory.StabFin.isIntegral_of_mem e he

theorem mulVec_natCast_smul (M : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) (N : ℕ) (z : Fin V.rank → EAf D) :
    M *ᵥ ((N : EAf D) • z) = ((N : EAf D) • M) *ᵥ z := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem invM_mul (h : Bridge.Gf V) :
    (Units.val ((h : Bridge.Gf V) : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E))).map (swapAE D) * invM h = 1 := by
  rw [invM, ← Matrix.map_mul, ← Units.val_mul, Subgroup.coe_inv, mul_inv_cancel, Units.val_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem invM_hmul (h x : Bridge.Gf V) : invM (h * x) = invM x * invM h := by
  rw [invM, invM, invM, _root_.mul_inv_rev, Subgroup.coe_mul, Units.val_mul, Matrix.map_mul]

theorem fg_of_le_fg {R M : Type*} [CommRing R] [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    {P Q : Submodule R M} (hQ : Q.FG) (hPQ : P ≤ Q) : P.FG := by
  haveI := isNoetherian_of_fg_of_noetherian Q hQ
  have h1 : (P.comap Q.subtype).FG := IsNoetherian.noetherian _
  have h2 := h1.map Q.subtype
  rwa [Submodule.map_comap_subtype, inf_eq_right.mpr hPQ] at h2

theorem mem_hLat_of (hV : Seed.FrmC.StdLat V) (h : Bridge.Gf V) {x : Fin V.rank → D.host.E}
    (hx : ∀ i, (invM h *ᵥ iv x) i ∈ GlobalTheory.StdFrameExist.SI D) : x ∈ Bridge.hLat V h :=
  Submodule.subset_span ((mem_set_iff hV h x).2 hx)

theorem isLattice (hV : Seed.FrmC.StdLat V) (h : Bridge.Gf V) : Submodule.IsLattice D.host.E (Bridge.hLat V h) := by
  obtain ⟨N, hN, hNm⟩ := GlobalTheory.PlaceDatum.exists_den_matrix (GlobalTheory.StdFrameExist.SI D) GlobalTheory.PlaceDatum.exists_den_adele
    ((Units.val ((h : Bridge.Gf V) : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E))).map (swapAE D))
  obtain ⟨N₁, hN₁, hN₁m⟩ := GlobalTheory.PlaceDatum.exists_den_matrix (GlobalTheory.StdFrameExist.SI D) GlobalTheory.PlaceDatum.exists_den_adele
    (invM h)
  have hNE : (N : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  apply Submodule.IsLattice.of_fg D.host.E
  ·
    let T : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) :=
      Submodule.span (𝓞 D.host.E) (Set.range fun j : Fin V.rank => (N : D.host.E)⁻¹ • (Pi.single j (1 : D.host.E)))
    refine fg_of_le_fg (Q := T) (Submodule.fg_span (Set.finite_range _)) (Submodule.span_le.2 fun x hx => ?_)
    have hx' := (mem_set_iff hV h x).1 hx
    have hint : ∀ i, IsIntegral ℤ ((N : D.host.E) * x i) := by
      intro i
      refine int_of_iv_mem ?_
      have e1 : ((N : D.host.E) * x i) ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F) =
          (((N : EAf D) • (Units.val ((h : Bridge.Gf V) : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E))).map (swapAE D))
            *ᵥ (invM h *ᵥ iv x)) i := by
        rw [Matrix.smul_mulVec, Matrix.mulVec_mulVec, invM_mul, Matrix.one_mulVec, ← iv_natCast_smul]
        rfl
      rw [e1]
      exact GlobalTheory.StdFrameExist.intV (fun a b => by rw [Matrix.smul_apply, smul_eq_mul]; exact hNm a b) hx' i
    choose c hc using fun i => (IsIntegralClosure.isIntegral_iff (A := 𝓞 D.host.E)).1 (hint i)
    refine (Submodule.mem_span_range_iff_exists_fun (𝓞 D.host.E)).2 ⟨c, ?_⟩
    funext l
    rw [Finset.sum_apply, Finset.sum_eq_single l]
    · rw [Pi.smul_apply, Pi.smul_apply, Pi.single_eq_same, Algebra.smul_def, smul_eq_mul, mul_one, hc]
      field_simp
    · intro b _ hb
      rw [Pi.smul_apply, Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hb), smul_zero, smul_zero]
    · simp

theorem smul_mem_hLat_mul (hV : Seed.FrmC.StdLat V) (h x : Bridge.Gf V) (p : ℕ)
    (hp : ∀ a b, (p : EAf D) * swapAE D ((x⁻¹ : Bridge.Gf V).1.val a b) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    ∀ y ∈ Bridge.hLat V h, (p : 𝓞 D.host.E) • y ∈ Bridge.hLat V (h * x) := by
  have hA : GlobalTheory.StdFrameExist.IntM (GlobalTheory.StdFrameExist.SI D) ((p : EAf D) • invM x) := fun a b => by
    rw [Matrix.smul_apply, smul_eq_mul]; exact hp a b
  have key : ∀ y, (∀ i, (invM h *ᵥ iv y) i ∈ GlobalTheory.StdFrameExist.SI D) → (p : 𝓞 D.host.E) • y ∈ Bridge.hLat V (h * x) := by
    intro y hy
    refine mem_hLat_of hV _ fun i => ?_
    have e : (p : 𝓞 D.host.E) • y = (p : D.host.E) • y := by rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
    rw [e, iv_natCast_smul, mulVec_natCast_smul, invM_hmul, ← Matrix.smul_mul, ← Matrix.mulVec_mulVec]
    exact GlobalTheory.StdFrameExist.intV hA hy i
  intro y hy
  have hle : Bridge.hLat V h ≤ (Bridge.hLat V (h * x)).comap ((p : 𝓞 D.host.E) • LinearMap.id) :=
    Submodule.span_le.2 fun y hy => key y ((mem_set_iff hV h y).1 hy)
  exact hle hy

theorem ratF_val (γ : Formalism.L2.Theta.GQ V) (γE : GL (Fin V.rank) D.host.E) (hγ : Bridge.IsRatMat V γ γE) :
    Units.val ((Bridge.ratF V γ : Bridge.Gf V) : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) =
      γE.val.map (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Af D.host.F ⊗[D.host.F] D.host.E) := by
  show Units.val (finHom V (γ : GA D V)) = _
  rw [finHom, MonoidHom.comp_apply, hγ]
  ext i j
  simp only [Formalism.UG.bc, incA]
  show (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)) ((1 : AF D.host.F) ⊗ₜ[D.host.F] (γE.val i j)) =
    (1 : Af D.host.F) ⊗ₜ[D.host.F] γE.val i j
  rw [Algebra.TensorProduct.map_tmul, map_one]
  rfl

theorem gl_cancel {R : Type} [CommRing R] {n : ℕ} (a b : GL (Fin n) R) (v : Fin n → R) :
    Units.val (b * a)⁻¹ *ᵥ (b.val *ᵥ v) = Units.val a⁻¹ *ᵥ v := by
  rw [Matrix.mulVec_mulVec, _root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]

theorem vec_move (γ : Formalism.L2.Theta.GQ V) (γE : GL (Fin V.rank) D.host.E) (hγ : Bridge.IsRatMat V γ γE)
    (h : Bridge.Gf V) (y : Fin V.rank → D.host.E) :
    (Units.val ((Bridge.ratF V γ * h)⁻¹ : Bridge.Gf V).1) *ᵥ (fun i => (1 : Af D.host.F) ⊗ₜ[D.host.F] (γE.val *ᵥ y) i) =
      (Units.val (h⁻¹ : Bridge.Gf V).1) *ᵥ (fun i => (1 : Af D.host.F) ⊗ₜ[D.host.F] y i) := by
  have hv : (fun i => (1 : Af D.host.F) ⊗ₜ[D.host.F] (γE.val *ᵥ y) i) =
      Units.val ((Bridge.ratF V γ : Bridge.Gf V) : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) *ᵥ
        (fun i => (1 : Af D.host.F) ⊗ₜ[D.host.F] y i) := by
    rw [ratF_val γ γE hγ]
    funext i
    exact RingHom.map_mulVec (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Af D.host.F ⊗[D.host.F] D.host.E).toRingHom γE.val y i
  rw [hv]
  exact gl_cancel ((h : Bridge.Gf V) : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E))
    ((Bridge.ratF V γ : Bridge.Gf V) : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) _

theorem mulVec_mem_hLat (γ : Formalism.L2.Theta.GQ V) (γE : GL (Fin V.rank) D.host.E) (hγ : Bridge.IsRatMat V γ γE)
    (h : Bridge.Gf V) : ∀ y ∈ Bridge.hLat V h, γE.val *ᵥ y ∈ Bridge.hLat V (Bridge.ratF V γ * h) := by
  intro y hy
  have hle : Bridge.hLat V h ≤ (Bridge.hLat V (Bridge.ratF V γ * h)).comap
      ((Matrix.mulVecLin γE.val).restrictScalars (𝓞 D.host.E)) :=
    Submodule.span_le.2 fun y hy => Submodule.subset_span (show _ ∈ latHat D.host.F D.host.E (L0c D V) by
      rw [LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply, vec_move γ γE hγ h y]
      exact hy)
  exact hle hy

theorem isRatMat_inv (γ : Formalism.L2.Theta.GQ V) (γE : GL (Fin V.rank) D.host.E) (hγ : Bridge.IsRatMat V γ γE) :
    Bridge.IsRatMat V γ⁻¹ γE⁻¹ := by
  unfold Bridge.IsRatMat at *
  rw [Subgroup.coe_inv, map_inv, map_inv, hγ]

theorem mem_hLat_iff (γ : Formalism.L2.Theta.GQ V) (γE : GL (Fin V.rank) D.host.E) (hγ : Bridge.IsRatMat V γ γE)
    (h : Bridge.Gf V) (y : Fin V.rank → D.host.E) :
    y ∈ Bridge.hLat V h ↔ γE.val *ᵥ y ∈ Bridge.hLat V (Bridge.ratF V γ * h) := by
  refine ⟨mulVec_mem_hLat γ γE hγ h y, fun hy => ?_⟩
  have := mulVec_mem_hLat γ⁻¹ γE⁻¹ (isRatMat_inv γ γE hγ) _ _ hy
  have e1 : Units.val γE⁻¹ *ᵥ (γE.val *ᵥ y) = y := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have e2 : Bridge.ratF V γ⁻¹ * (Bridge.ratF V γ * h) = h := by rw [map_inv, inv_mul_cancel_left]
  rw [e1, e2] at this
  exact this

theorem hLat_props : ∀ (D : D7) (V : HSp D), Seed.FrmC.StdLat V → (∀ h, Submodule.IsLattice D.host.E (Bridge.hLat V h)) ∧ (∀ (h x : Bridge.Gf V) (p : ℕ), (∀ a b, (p : EAf D) * swapAE D ((x⁻¹ : Bridge.Gf V).1.val a b) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → ∀ y ∈ Bridge.hLat V h, (p : 𝓞 D.host.E) • y ∈ Bridge.hLat V (h * x)) ∧ ∀ (γ : Formalism.L2.Theta.GQ V) (γE : GL (Fin V.rank) D.host.E), Bridge.IsRatMat V γ γE → ∀ h y, y ∈ Bridge.hLat V h ↔ γE.val.mulVec y ∈ Bridge.hLat V (Bridge.ratF V γ * h) :=
  fun _ _ hV => ⟨isLattice hV, smul_mem_hLat_mul hV, mem_hLat_iff⟩

end GlobalTheory.HLatStd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TranslatedStdLatticeLatticeComparisonRationalStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translatedStdLattice_lattice_comparison_rational : ∀ (D : D7) (V : HSp D), Seed.FrmC.StdLat V → (∀ h, Submodule.IsLattice D.host.E (Bridge.hLat V h)) ∧ (∀ (h x : Bridge.Gf V) (p : ℕ), (∀ a b, (p : EAf D) * swapAE D ((x⁻¹ : Bridge.Gf V).1.val a b) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → ∀ y ∈ Bridge.hLat V h, (p : 𝓞 D.host.E) • y ∈ Bridge.hLat V (h * x)) ∧ ∀ (γ : Formalism.L2.Theta.GQ V) (γE : GL (Fin V.rank) D.host.E), Bridge.IsRatMat V γ γE → ∀ h y, y ∈ Bridge.hLat V h ↔ γE.val.mulVec y ∈ Bridge.hLat V (Bridge.ratF V γ * h) := by
  first | exact @GlobalTheory.HLatStd.hLat_props | exact GlobalTheory.HLatStd.hLat_props | (intros; apply GlobalTheory.HLatStd.hLat_props <;> assumption)
end
end
