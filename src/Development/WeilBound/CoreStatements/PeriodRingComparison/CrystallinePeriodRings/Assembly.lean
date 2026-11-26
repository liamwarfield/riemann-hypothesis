module

public import Development.WeilBound.CoreStatements.CrystallinePeriodRings.AinfMapSurjective
public import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.DeRham
public import Development.WeilBound.CoreStatements.PeriodRingComparison.RationalRingEquivalences.IsLogCore

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PeriodRingComparison.AinfAlgebraMaps.CAAlgebraMapGOC
noncomputable section

open GroundTheory.PAdicHodge
open Formalism.BasicNotions.Loc (GQ)

namespace Cmp6

variable (l : ℕ) [Fact l.Prime]

def gOC (g : GQ l) : OC l →+* OC l := MulSemiringAction.toRingHom (GQ l) (OC l) g

theorem smul_cp_eq (g : GQ l) (y : ℂ_[l]) : g • y = galCp (Formalism.Per6.toBot g) y := by
  refine UniformSpace.Completion.induction_on y
    (isClosed_eq (continuous_const_smul g) (continuous_galCp _)) fun a => ?_
  rw [Reformulated.AutPerF.padicComplex_smul_coe, galCp_coe]
  rfl

theorem coe_gOC (g : GQ l) (x : OC l) :
    ((gOC l g x : OC l) : ℂ_[l]) = galCp (Formalism.Per6.toBot g) (x : ℂ_[l]) :=
  smul_cp_eq l g x

theorem tiltMap_gOC (g : GQ l) : Reformulated.AutPerF.Tilt.map l (gOC l g) = PositivityTheory.LocInh.galT g := by
  refine RingHom.ext fun x => ?_
  apply Perfection.ext
  intro n
  change PreTilt.coeff n (Reformulated.AutPerF.Tilt.map l (gOC l g) x) =
    PreTilt.coeff n (PositivityTheory.LocInh.galT g x)
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (PreTilt.coeff n x)
  have h1 := PositivityTheory.LocInh.frob_coeff_tiltMap x n y hy.symm
  have h2 : PreTilt.coeff n (PositivityTheory.LocInh.galT g x) = (Formalism.Per6.modPEquiv l).symm
      (modPMap (galCp (Formalism.Per6.toBot g) : ℂ_[l] →+* ℂ_[l]) (AInf.norm_galCp_toRingHom (Formalism.Per6.toBot g))
        (PreTilt.coeff n (Formalism.Per6.tiltMap l x))) := rfl
  rw [h2, h1, modPMap_mk]
  rw [Reformulated.AutPerF.Tilt.coeff_map, ← hy, Ideal.quotientMap_mk]
  apply congrArg
  apply Subtype.ext
  exact coe_gOC l g y

theorem ainfMap_gOC (g : GQ l) (a : Reformulated.AutPerF.Ainf l (OC l)) :
    Formalism.Per6.ainfMap l (Reformulated.AutPerF.Ainf.map l (gOC l g) a) =
      Formalism.Per6.toBot g • Formalism.Per6.ainfMap l a := by
  rw [Reformulated.AutPerF.Ainf.map, tiltMap_gOC]
  refine WittVector.ext fun n => ?_
  rw [AInf.gal_smul_coeff]
  exact PositivityTheory.LocInh.tiltMap_tiltInv l _

theorem cA_algebraMap_gOC (g : GQ l) (w : Reformulated.AutPerF.Ainf l (OC l)) :
    cA l (Reformulated.AutPerF.Acris.map l (gOC l g) (algebraMap _ (Reformulated.AutPerF.Acris l (OC l)) w)) =
      ACris.galCris (Formalism.Per6.toBot g) (cA l (algebraMap _ (Reformulated.AutPerF.Acris l (OC l)) w)) := by
  rw [Reformulated.AutPerF.Acris.map_algebraMap, cA_algebraMap, cA_algebraMap, ainfMap_gOC,
    ← ACris.gal_smul_algebraMap, ACris.gal_smul_def]

theorem zero_ext {F G : Reformulated.AutPerF.AcrisZero l (OC l) →+* ACris.ACris ℂ_[l] l}
    (h : ∀ w : Reformulated.AutPerF.Ainf l (OC l), F (algebraMap _ _ w) = G (algebraMap _ _ w))
    (a : Reformulated.AutPerF.AcrisZero l (OC l)) : F a = G a := by
  obtain ⟨⟨w, _, k, rfl⟩, hw⟩ := IsLocalization.surj
    (Submonoid.powers (l : Reformulated.AutPerF.Ainf l (OC l))) (a : Reformulated.AutPerF.AinfInv l (OC l))
  have ha : a * (l : Reformulated.AutPerF.AcrisZero l (OC l)) ^ k = algebraMap _ _ w := by
    apply Subtype.ext
    simpa using hw
  have e : F a * (l : ACris.ACris ℂ_[l] l) ^ k = G a * (l : ACris.ACris ℂ_[l] l) ^ k := by
    calc F a * (l : ACris.ACris ℂ_[l] l) ^ k = F (a * (l : Reformulated.AutPerF.AcrisZero l (OC l)) ^ k) := by
          rw [map_mul, map_pow, map_natCast]
      _ = G (a * (l : Reformulated.AutPerF.AcrisZero l (OC l)) ^ k) := by rw [ha, h]
      _ = G a * (l : ACris.ACris ℂ_[l] l) ^ k := by rw [map_mul, map_pow, map_natCast]
  apply ACris.iota_injective (K := ℂ_[l]) (p := l)
  refine ((IsPerfectoidField.isUnit_natCast_p_bDeRhamPlus (K := ℂ_[l]) l).pow k).mul_right_cancel ?_
  have e' := congrArg (ACris.iota ℂ_[l] l) e
  rwa [map_mul, map_mul, map_pow, map_natCast] at e'

theorem cA_map_gal (g : GQ l) (x : Reformulated.AutPerF.Acris l (OC l)) :
    cA l (Reformulated.AutPerF.Acris.map l (gOC l g) x) = ACris.galCris (Formalism.Per6.toBot g) (cA l x) := by
  have key : (cA l).toRingHom.comp (Reformulated.AutPerF.Acris.map l (gOC l g)) =
      (ACris.galCris (Formalism.Per6.toBot g)).comp (cA l).toRingHom := by
    refine Reformulated.AutPerF.Acris.hom_ext fun a => ?_
    refine zero_ext l (F := ((cA l).toRingHom.comp (Reformulated.AutPerF.Acris.map l (gOC l g))).comp
      (algebraMap _ _)) (G := ((ACris.galCris (Formalism.Per6.toBot g)).comp (cA l).toRingHom).comp
      (algebraMap _ _)) (fun w => ?_) a
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    rw [← IsScalarTower.algebraMap_apply]
    exact cA_algebraMap_gOC l g w
  exact RingHom.congr_fun key x

end Cmp6
end
end

section -- merged from Development.WeilBound.CoreStatements.PeriodRingComparison.PrimitiveEpsilon.UntiltEpsilonEqOne
noncomputable section

open GroundTheory.PAdicHodge

namespace Cmp6

variable (l : ℕ) [Fact l.Prime]

theorem untilt_tiltMap (x : Reformulated.AutPerF.Tilt l (OC l)) :
    PreTilt.untilt (Formalism.Per6.tiltMap l x) = e l (PreTilt.untilt x) := by
  rw [← tiltMap_eq]
  exact Reformulated.AutPerF.Tilt.untilt_map (e l).toRingHom x

theorem untilt_epsilon_eq_one : PreTilt.untilt (PositivityTheory.LocInh.εO l) = (1 : OC l) := by
  apply (e l).injective
  rw [← untilt_tiltMap, PositivityTheory.LocInh.εO, PositivityTheory.LocInh.tiltMap_tiltInv, map_one]
  exact untilt_epsilon

def eps0 : Reformulated.AutPerF.tateModule l (OC l) := ⟨PositivityTheory.LocInh.εO l, untilt_epsilon_eq_one l⟩

theorem tiltMap_epsilon : Formalism.Per6.tiltMap l (eps0 l).1 = epsilon l := (PositivityTheory.LocInh.tiltMap_tiltInv l _)

theorem epsilon_isPrimitive : Reformulated.AutPerF.IsPrimitive (eps0 l) := by
  unfold Reformulated.AutPerF.IsPrimitive
  intro h
  have hne : PreTilt.untilt ((frobeniusEquiv (PreTilt (NC l) l) l).symm (epsilon l)) ≠ 1 := by
    rw [epsilon, AInf.frobeniusEquiv_symm_ofCompatible, IsPerfectoidField.untilt_ofCompatible]
    intro h
    exact rootSeq_one_ne_one (congrArg Subtype.val h)
  apply hne
  have h1 : Formalism.Per6.tiltMap l ((frobeniusEquiv (Reformulated.AutPerF.Tilt l (OC l)) l).symm (eps0 l).1) =
      (frobeniusEquiv (PreTilt (NC l) l) l).symm (epsilon l) := by
    rw [RingHom.map_frobeniusEquiv_symm, tiltMap_epsilon]
  rw [← h1, untilt_tiltMap, h, map_one]

end Cmp6
end
end

section -- merged from Development.WeilBound.CoreStatements.PeriodRingComparison.AinfInverseMaps.AinfInvMapGOC
section -- merged from Development.WeilBound.CoreStatements.PeriodRingComparison.PadicPeriodAlgebraMaps.CPAlgebraMapPadic
noncomputable section

open GroundTheory.PAdicHodge

namespace Cmp6

variable (l : ℕ) [Fact l.Prime]

def cP : Reformulated.AutPerF.BdRPlus l (OC l) ≃+* Formalism.Per6.BdRp l :=
  Reformulated.AutPerF.BdRPlus.mapEquiv l (e l)

theorem cP_apply (y : Reformulated.AutPerF.BdRPlus l (OC l)) :
    cP l y = Reformulated.AutPerF.BdRPlus.map l (e l).toRingHom y := rfl

theorem comparison_algebraMap_ainf (a : Reformulated.AutPerF.Ainf l (OC l)) :
    cP l (algebraMap _ (Reformulated.AutPerF.BdRPlus l (OC l)) a) = Formalism.Per6.aD l a := by
  rw [cP_apply, Reformulated.AutPerF.BdRPlus.map_algebraMap_ainf, ainfMap_eq]
  rfl

theorem awayEquiv_awayMap (z : Localization.Away ((l : ℕ) : OC l)) :
    IsPerfectoidField.awayEquiv (K := ℂ_[l]) l (Reformulated.AutPerF.awayMap l (e l).toRingHom z) =
      Reformulated.AutPerF.IsUnitBall.awayEquiv (PadicComplexInt l) l z := by
  have h : (IsPerfectoidField.awayEquiv (K := ℂ_[l]) l).toRingEquiv.toRingHom.comp
      (Reformulated.AutPerF.awayMap l (e l).toRingHom) =
      (Reformulated.AutPerF.IsUnitBall.awayEquiv (PadicComplexInt l) l).toRingEquiv.toRingHom := by
    refine IsLocalization.ringHom_ext (Submonoid.powers ((l : ℕ) : OC l)) (RingHom.ext fun x => ?_)
    simp only [RingHom.comp_apply]
    rw [Reformulated.AutPerF.awayMap_algebraMap]
    change IsPerfectoidField.awayEquiv (K := ℂ_[l]) l (algebraMap (NC l) _ (e l x)) =
      Reformulated.AutPerF.IsUnitBall.awayEquiv (PadicComplexInt l) l (algebraMap (OC l) _ x)
    rw [AlgEquiv.commutes, Reformulated.AutPerF.IsUnitBall.awayEquiv_algebraMap]
    rfl
  exact RingHom.congr_fun h z

theorem θD_cP (y : Reformulated.AutPerF.BdRPlus l (OC l)) :
    Formalism.Per6.θD l (cP l y) = Reformulated.AutPerF.BdRPlus.thetaC l (PadicComplexInt l) y := by
  change IsPerfectoidField.awayEquiv (K := ℂ_[l]) l
      (Reformulated.AutPerF.BdRPlus.theta l (NC l) (Reformulated.AutPerF.BdRPlus.map l (e l).toRingHom y)) = _
  rw [Reformulated.AutPerF.BdRPlus.theta_map, Reformulated.AutPerF.BdRPlus.thetaC_apply]
  exact awayEquiv_awayMap l _

end Cmp6
end
end

section -- merged from Development.WeilBound.CoreStatements.PeriodRingComparison.ThetaKernelDeRham.KerThetaEqSpanSymmTBdR
noncomputable section

open GroundTheory.PAdicHodge

namespace Cmp6

variable (l : ℕ) [Fact l.Prime]

def cPd : Reformulated.AutPerF.BdRPlus l (OC l) ≃+* Formalism.Per6.BdRp l := Reformulated.AutPerF.BdRPlus.mapEquiv l (e l)

def cD : Reformulated.AutPerF.BdR l (OC l) ≃+* Formalism.Per6.BdR l :=
  IsFractionRing.ringEquivOfRingEquiv (cPd l)

theorem cD_algebraMap (y : Reformulated.AutPerF.BdRPlus l (OC l)) :
    cD l (algebraMap _ _ y) = algebraMap (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l) (cPd l y) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ y

theorem ker_theta_eq_span_symm_tBdR :
    RingHom.ker (Reformulated.AutPerF.BdRPlus.theta l (OC l)) = Ideal.span {(cPd l).symm (tBdR l)} :=
  (Reformulated.AutPerF.BdRPlus.irreducible_iff _).1
    ((MulEquiv.irreducible_iff (f := (cPd l).symm)).2 irreducible_tBdR)

theorem fil_transport {A B K L : Type} [CommRing A] [CommRing B] [Field K] [Field L] [Algebra A K]
    [Algebra B L] (f : A ≃+* B) (F : K ≃+* L) (h : ∀ y, F (algebraMap A K y) = algebraMap B L (f y))
    (t : B) (a : ℤ) (x : K) :
    x ∈ Submodule.span A {algebraMap A K (f.symm t) ^ a} ↔
      F x ∈ Submodule.span B {algebraMap B L t ^ a} := by
  have ht : F (algebraMap A K (f.symm t) ^ a) = algebraMap B L t ^ a := by
    rw [map_zpow₀, h, RingEquiv.apply_symm_apply]
  rw [Submodule.mem_span_singleton, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨f c, by rw [Algebra.smul_def, Algebra.smul_def, map_mul, h, ht]⟩
  · rintro ⟨c, hc⟩
    refine ⟨f.symm c, F.injective ?_⟩
    rw [← hc, Algebra.smul_def, Algebra.smul_def, map_mul, h, ht, RingEquiv.apply_symm_apply]

theorem cD_fil (a : ℤ) (x : Reformulated.AutPerF.BdR l (OC l)) :
    x ∈ Reformulated.AutPerF.BdR.fil l (OC l) a ↔ cD l x ∈ Formalism.Per6.FilD l a := by
  have h1 : Formalism.Per6.FilD l a = Submodule.span (Formalism.Per6.BdRp l)
      {(algebraMap (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l) (tBdR l)) ^ a} := fil_eq_span_tBdR a
  rw [h1, Reformulated.AutPerF.BdR.fil_eq_span (ker_theta_eq_span_symm_tBdR l)]
  exact fil_transport (cPd l) (cD l) (cD_algebraMap l) (tBdR l) a x

end Cmp6
end
end

noncomputable section

open GroundTheory.PAdicHodge
open Formalism.BasicNotions.Loc (GQ)

namespace Cmp6

variable (l : ℕ) [Fact l.Prime]

theorem ainfInv_map_gOC (g : GQ l) (a : Reformulated.AutPerF.AinfInv l (OC l)) :
    Reformulated.AutPerF.AinfInv.map l ((e l).toRingHom.comp (gOC l g)) a =
      galAway (Formalism.Per6.toBot g) (Reformulated.AutPerF.AinfInv.map l (e l).toRingHom a) := by
  refine RingHom.congr_fun (Reformulated.AutPerF.AinfInv.hom_ext
    (f := Reformulated.AutPerF.AinfInv.map l ((e l).toRingHom.comp (gOC l g)))
    (g := (galAway (Formalism.Per6.toBot g)).comp (Reformulated.AutPerF.AinfInv.map l (e l).toRingHom))
    fun w => ?_) a
  rw [RingHom.comp_apply, Reformulated.AutPerF.AinfInv.map_algebraMap, Reformulated.AutPerF.AinfInv.map_algebraMap,
    galAway_algebraMap, ← Reformulated.AutPerF.Ainf.map_map, ainfMap_eq, ainfMap_gOC]

theorem comparison_map_galois (g : GQ l) (y : Reformulated.AutPerF.BdRPlus l (OC l)) :
    cP l (Reformulated.AutPerF.BdRPlus.map l (gOC l g) y) = Formalism.Per6.toBot g • cP l y := by
  rw [gal_smul_bdR_def]
  refine IsPerfectoidField.evalB_ext (K := ℂ_[l]) (p := l) fun n => ?_
  rw [evalB_galBdRHom]
  change Reformulated.AutPerF.BdRPlus.eval l (NC l) n (Reformulated.AutPerF.BdRPlus.map l (e l).toRingHom
      (Reformulated.AutPerF.BdRPlus.map l (gOC l g) y)) = galQuot (Formalism.Per6.toBot g) n
      (Reformulated.AutPerF.BdRPlus.eval l (NC l) n (Reformulated.AutPerF.BdRPlus.map l (e l).toRingHom y))
  rw [Reformulated.AutPerF.BdRPlus.map_map, Reformulated.AutPerF.BdRPlus.eval_map, Reformulated.AutPerF.BdRPlus.eval_map]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (Reformulated.AutPerF.BdRPlus.eval l (OC l) n y)
  rw [← ha, Ideal.quotientMap_mk, Ideal.quotientMap_mk, ainfInv_map_gOC]
  erw [galQuot_mk]

theorem cPoint_smul (g : GQ l) (y : Reformulated.AutPerF.BdRPlus l (OC l)) :
    cP l (g • y) = Formalism.Per6.toBot g • cP l y :=
  comparison_map_galois l g y

theorem cD_gal (g : GQ l) (x : Reformulated.AutPerF.BdR l (OC l)) :
    cD l (g • x) = Formalism.Per6.σD g (cD l x) := by
  have key : (cD l).toRingHom.comp (MulSemiringAction.toRingHom (GQ l) (Reformulated.AutPerF.BdR l (OC l)) g) =
      (Formalism.Per6.σD g).toRingHom.comp (cD l).toRingHom := by
    refine Reformulated.AutPerF.BdR.hom_ext fun y => ?_
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      MulSemiringAction.toRingHom_apply]
    rw [Reformulated.AutPerF.BdR.smul_algebraMap, cD_algebraMap, cD_algebraMap,
      PositivityTheory.LocInh.GaloisCommutant.σD_algebraMap]
    exact congrArg (algebraMap (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l)) (cPoint_smul l g y)
  exact RingHom.congr_fun key x

end Cmp6
end
end

section -- merged from Development.WeilBound.CoreStatements.PeriodRingComparison.TeichmullerLogarithm.LogEps
section -- merged from Development.WeilBound.CoreStatements.PeriodRingComparison.TeichmullerLogarithm.ZeroEquivLogTerm
noncomputable section

open GroundTheory.PAdicHodge
open _root_.WittVector

namespace Cmp6

variable (l : ℕ) [Fact l.Prime]

theorem periodT_congr {ε ε' : PreTilt (normInteger ℂ_[l]) l} (hε : PreTilt.untilt ε = 1)
    (hε' : PreTilt.untilt ε' = 1) (h : ε = ε') :
    ACris.periodT (K := ℂ_[l]) hε = ACris.periodT (K := ℂ_[l]) hε' := by
  subst h; rfl

theorem zeroEquiv_logTerm (u : Reformulated.AutPerF.Ainf l (NC l))
    (hu : Reformulated.AutPerF.Ainf.theta l (NC l) u = 1)
    (hx : u - 1 ∈ RingHom.ker (fontaineTheta (normInteger ℂ_[l]) l)) (n : ℕ) :
    zeroEquiv l (((-1) ^ n * (n.factorial : Reformulated.AutPerF.AcrisZero l (NC l))) *
        Reformulated.AutPerF.AcrisZero.gamma (n + 1) (u - 1) (by rw [map_sub, hu, map_one, sub_self])) =
      ACris.logTermZero hx n := by
  set_option synthInstance.maxHeartbeats 100000 in
  rw [ACris.logTermZero, map_mul, map_mul, map_pow, map_neg, map_one, map_natCast]
  congr 1
  apply Subtype.ext
  change Reformulated.AutPerF.AinfInv.gamma (n + 1)
      (algebraMap (Reformulated.AutPerF.Ainf l (NC l)) (Reformulated.AutPerF.AinfInv l (NC l)) (u - 1)) =
    ACris.dpow (n + 1) (u - 1)
  exact gamma_eq_dpow l (n + 1) (u - 1)


set_option maxHeartbeats 1000000 in
theorem acrisNHom_log (u : Reformulated.AutPerF.Ainf l (NC l))
    (hu : Reformulated.AutPerF.Ainf.theta l (NC l) u = 1)
    (hx : u - 1 ∈ RingHom.ker (fontaineTheta (normInteger ℂ_[l]) l)) :
    acrisNHom l (Reformulated.AutPerF.Acris.log u hu) = ACris.log hx := by
  symm
  apply ACris.log_eq_of_isAdicSum
  intro k
  refine ⟨l ^ k, fun M hM => ?_⟩
  have hsum : ∑ n ∈ Finset.range M, ACris.logTerm hx n =
      acrisNHom l (algebraMap _ (Reformulated.AutPerF.Acris l (NC l))
        (Reformulated.AutPerF.Acris.logPartial M u hu)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [acrisNHom_algebraMap, Reformulated.AutPerF.Acris.logPartial, map_sum, map_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [ACris.logTerm, zeroEquiv_logTerm l u hu hx n]
  rw [hsum, ← map_sub]
  obtain ⟨y, hy⟩ := (Reformulated.AutPerF.Acris.eval_eq_zero_iff k (Reformulated.AutPerF.Acris.log u hu -
      algebraMap _ (Reformulated.AutPerF.Acris l (NC l)) (Reformulated.AutPerF.Acris.logPartial M u hu))).1 (by
    rw [map_sub, Reformulated.AutPerF.Acris.eval_algebraMap, Reformulated.AutPerF.Acris.eval_log u hu hM, sub_self])
  rw [hy, map_mul, map_pow, map_natCast, Ideal.span_singleton_pow]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

theorem cA_logTeich (η : Reformulated.AutPerF.tateModule l (OC l))
    (h : PreTilt.untilt (Formalism.Per6.tiltMap l η.1) = 1) :
    cA l (Reformulated.AutPerF.Acris.logTeich η) = ACris.periodT h := by
  have hu : Reformulated.AutPerF.Ainf.theta l (NC l)
      (Reformulated.AutPerF.Ainf.teich l (Formalism.Per6.tiltMap l η.1)) = 1 := by
    rw [Reformulated.AutPerF.Ainf.theta_teich]; exact h
  rw [cA_apply, Reformulated.AutPerF.Acris.map_logTeich, Reformulated.AutPerF.Acris.logTeich,
    Reformulated.AutPerF.Acris.log_congr _ hu (by rw [Reformulated.AutPerF.tateModule.coe_map, tiltMap_eq])]
  exact acrisNHom_log l _ hu (ACris.mu_mem_ker h)

theorem cA_logTeich_eps (h0 : PreTilt.untilt (PositivityTheory.LocInh.εO l) = 1) :
    cA l (Reformulated.AutPerF.Acris.logTeich ⟨PositivityTheory.LocInh.εO l, h0⟩) = Formalism.Per6.tA l := by
  have h1 : Formalism.Per6.tiltMap l (PositivityTheory.LocInh.εO l) = epsilon l := PositivityTheory.LocInh.tiltMap_tiltInv l _
  have h : PreTilt.untilt (Formalism.Per6.tiltMap l (PositivityTheory.LocInh.εO l)) = 1 := by
    rw [h1]; exact untilt_epsilon (p := l)
  rw [cA_logTeich l ⟨PositivityTheory.LocInh.εO l, h0⟩ h]
  exact periodT_congr l h (untilt_epsilon (p := l)) h1

end Cmp6
end
end

noncomputable section

open GroundTheory.PAdicHodge

namespace Cmp6

variable (l : ℕ) [Fact l.Prime]

theorem acris_log_teichmuller_epsilon : cA l (Reformulated.AutPerF.Acris.logTeich (eps0 l)) = Formalism.Per6.tA l :=
  cA_logTeich_eps l (untilt_epsilon_eq_one l)

end Cmp6
end
end

section -- merged from Development.WeilBound.CoreStatements.PeriodRingComparison.CrystallinePeriodRings.BcrisPlusHomAlgebraMap
noncomputable section

open GroundTheory.PAdicHodge

namespace Cmp6

variable (l : ℕ) [Fact l.Prime]

theorem cA_symm_tA : (cA l).symm (Formalism.Per6.tA l) = Reformulated.AutPerF.Acris.logTeich (eps0 l) := by
  rw [← acris_log_teichmuller_epsilon, RingEquiv.symm_apply_apply]

theorem isUnit_bcris_l : IsUnit ((l : ℕ) : Formalism.Per6.Bcris l) := by
  simpa using PositivityTheory.LocInh.isUnit_cB_l l

def bcrisPlusHom : Reformulated.AutPerF.BcrisPlus l (OC l) →+* Formalism.Per6.Bcris l :=
  Reformulated.AutPerF.BcrisPlus.lift ((Formalism.Per6.cB l).comp (cA l).toRingHom) (isUnit_bcris_l l)

theorem bcrisPlusHom_algebraMap (x : Reformulated.AutPerF.Acris l (OC l)) :
    bcrisPlusHom l (algebraMap _ _ x) = Formalism.Per6.cB l (cA l x) :=
  Reformulated.AutPerF.BcrisPlus.lift_algebraMap _ _ x

theorem isUnit_cB_cA_logTeich {ε : Reformulated.AutPerF.tateModule l (OC l)} (hε : Reformulated.AutPerF.IsPrimitive ε) :
    IsUnit (Formalism.Per6.cB l (cA l (Reformulated.AutPerF.Acris.logTeich ε))) := by
  obtain ⟨a, rfl⟩ := (epsilon_isPrimitive l).exists_unit hε
  rw [Reformulated.AutPerF.Acris.logTeich_padicPow, ← cA_symm_tA, map_mul, RingEquiv.apply_symm_apply,
    map_mul]
  exact (((a.isUnit.map (algebraMap ℤ_[l] (Reformulated.AutPerF.Acris l (OC l)))).map (cA l)).map
    (Formalism.Per6.cB l)).mul (Formalism.Per6.Loc2.isUnit_right _ _)

def bcrisHom : Reformulated.AutPerF.Bcris l (OC l) →+* Formalism.Per6.Bcris l :=
  Reformulated.AutPerF.Bcris.lift (bcrisPlusHom l) (fun ε hε => by
    rw [bcrisPlusHom_algebraMap]
    exact isUnit_cB_cA_logTeich l hε)

theorem bcrisHom_algebraMap (x : Reformulated.AutPerF.Acris l (OC l)) :
    bcrisHom l (algebraMap _ _ x) = Formalism.Per6.cB l (cA l x) :=
  (Reformulated.AutPerF.Bcris.lift_algebraMap _ _ _).trans (bcrisPlusHom_algebraMap l x)

def bcrisInv : Formalism.Per6.Bcris l →+* Reformulated.AutPerF.Bcris l (OC l) :=
  Formalism.Per6.Loc2.lift
    ((algebraMap (Reformulated.AutPerF.Acris l (OC l)) (Reformulated.AutPerF.Bcris l (OC l))).comp (cA l).symm.toRingHom)
    (by
      rw [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, map_natCast,
        map_natCast]
      exact Reformulated.AutPerF.Bcris.isUnit_p (p := l) (R := OC l))
    (by
      rw [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, cA_symm_tA]
      exact Reformulated.AutPerF.Bcris.isUnit_logTeich (epsilon_isPrimitive l))

theorem bcrisInv_cB (x : ACris.ACris ℂ_[l] l) :
    bcrisInv l (Formalism.Per6.cB l x) = algebraMap _ (Reformulated.AutPerF.Bcris l (OC l)) ((cA l).symm x) :=
  Formalism.Per6.Loc2.lift_mk₀ _ _ _ x

theorem bcrisInv_bcrisHom (x : Reformulated.AutPerF.Bcris l (OC l)) : bcrisInv l (bcrisHom l x) = x := by
  have h : (bcrisInv l).comp (bcrisHom l) = RingHom.id _ := by
    refine Reformulated.AutPerF.Bcris.hom_ext fun y => ?_
    have h2 : ((bcrisInv l).comp (bcrisHom l)).comp
        (algebraMap (Reformulated.AutPerF.BcrisPlus l (OC l)) (Reformulated.AutPerF.Bcris l (OC l))) =
        (RingHom.id _).comp (algebraMap _ _) := by
      refine Reformulated.AutPerF.BcrisPlus.hom_ext fun z => ?_
      simp only [RingHom.comp_apply, RingHom.id_apply]
      change bcrisInv l (bcrisHom l (algebraMap (Reformulated.AutPerF.Acris l (OC l)) _ z)) =
        algebraMap (Reformulated.AutPerF.Acris l (OC l)) _ z
      rw [bcrisHom_algebraMap, bcrisInv_cB, RingEquiv.symm_apply_apply]
    exact RingHom.congr_fun h2 y
  exact RingHom.congr_fun h x

theorem bcrisHom_bcrisInv (x : Formalism.Per6.Bcris l) : bcrisHom l (bcrisInv l x) = x := by
  have h : (bcrisHom l).comp (bcrisInv l) = RingHom.id _ := by
    refine Formalism.Per6.Loc2.hom_ext fun y => ?_
    change bcrisHom l (bcrisInv l (Formalism.Per6.cB l y)) = Formalism.Per6.cB l y
    rw [bcrisInv_cB, bcrisHom_algebraMap, RingEquiv.apply_symm_apply]
  exact RingHom.congr_fun h x

def cBc : Reformulated.AutPerF.Bcris l (OC l) ≃+* Formalism.Per6.Bcris l :=
  RingEquiv.ofRingHom (bcrisHom l) (bcrisInv l) (RingHom.ext (bcrisHom_bcrisInv l))
    (RingHom.ext (bcrisInv_bcrisHom l))

theorem cBc_algebraMap (x : Reformulated.AutPerF.Acris l (OC l)) :
    cBc l (algebraMap _ _ x) = Formalism.Per6.cB l (cA l x) :=
  bcrisHom_algebraMap l x

theorem cBc_symm_cB (x : ACris.ACris ℂ_[l] l) :
    (cBc l).symm (Formalism.Per6.cB l x) = algebraMap _ (Reformulated.AutPerF.Bcris l (OC l)) ((cA l).symm x) :=
  bcrisInv_cB l x

end Cmp6
end
end

section -- merged from Development.WeilBound.CoreStatements.PeriodRingComparison.CrystallinePeriodRings.BcrisLogTeichmullerEqT
noncomputable section

open GroundTheory.PAdicHodge
open Formalism.BasicNotions.Loc (GQ)

namespace Cmp6

variable (l : ℕ) [Fact l.Prime]

theorem cBc_gal (g : GQ l) (b : Reformulated.AutPerF.Bcris l (OC l)) :
    cBc l (Reformulated.AutPerF.Bcris.map l (gOC l g) (Reformulated.AutPerF.toRingHom_injective g) b) =
      Formalism.Per6.σB g (cBc l b) := by
  have key : ((cBc l).toRingHom.comp
      (Reformulated.AutPerF.Bcris.map l (gOC l g) (Reformulated.AutPerF.toRingHom_injective g))).comp
        (cBc l).symm.toRingHom = Formalism.Per6.σB g :=
    PositivityTheory.LocInh.bcris_hom_ext fun y => by
      change cBc l (Reformulated.AutPerF.Bcris.map l (gOC l g) (Reformulated.AutPerF.toRingHom_injective g)
        ((cBc l).symm (Formalism.Per6.cB l y))) = _
      rw [cBc_symm_cB, Reformulated.AutPerF.Bcris.map_algebraMap_acris (gOC l g) (Reformulated.AutPerF.toRingHom_injective g),
        cBc_algebraMap, cA_map_gal,
        RingEquiv.apply_symm_apply]
      exact (PositivityTheory.LocInh.σB_cB g y).symm
  have h := RingHom.congr_fun key (cBc l b)
  change cBc l (Reformulated.AutPerF.Bcris.map l (gOC l g) (Reformulated.AutPerF.toRingHom_injective g)
    ((cBc l).symm (cBc l b))) = _ at h
  rwa [RingEquiv.symm_apply_apply] at h

theorem cBc_smul (g : GQ l) (b : Reformulated.AutPerF.Bcris l (OC l)) :
    cBc l (g • b) = Formalism.Per6.σB g (cBc l b) :=
  cBc_gal l g b

end Cmp6
end
end

section -- merged from Development.WeilBound.CoreStatements.PeriodRingComparison.CrystallinePeriodRings.BcFrob
noncomputable section

open GroundTheory.PAdicHodge

namespace Cmp6

variable (l : ℕ) [Fact l.Prime]

theorem bcris_hom_ext_acris {B : Type} [CommRing B] {f g : Reformulated.AutPerF.Bcris l (OC l) →+* B}
    (h : ∀ x : Reformulated.AutPerF.Acris l (OC l),
      f (algebraMap (Reformulated.AutPerF.Acris l (OC l)) (Reformulated.AutPerF.Bcris l (OC l)) x) =
        g (algebraMap (Reformulated.AutPerF.Acris l (OC l)) (Reformulated.AutPerF.Bcris l (OC l)) x)) : f = g := by
  apply Reformulated.AutPerF.Bcris.hom_ext
  intro z
  have h2 : f.comp (algebraMap (Reformulated.AutPerF.BcrisPlus l (OC l)) (Reformulated.AutPerF.Bcris l (OC l))) =
      g.comp (algebraMap (Reformulated.AutPerF.BcrisPlus l (OC l)) (Reformulated.AutPerF.Bcris l (OC l))) := by
    apply Reformulated.AutPerF.BcrisPlus.hom_ext
    intro y
    exact h y
  exact RingHom.congr_fun h2 z

theorem cBc_frob_of
    (hφ : ∀ x, cA l (Reformulated.AutPerF.Acris.frob l (OC l) x) =
      ACris.phi (K := ℂ_[l]) (p := l) (cA l x))
    (b : Reformulated.AutPerF.Bcris l (OC l)) :
    cBc l (Reformulated.AutPerF.Bcris.frob l (OC l) b) = Formalism.Per6.φB l (cBc l b) := by
  have h : (cBc l).toRingHom.comp (Reformulated.AutPerF.Bcris.frob l (OC l)) =
      (Formalism.Per6.φB l).comp (cBc l).toRingHom :=
    bcris_hom_ext_acris l fun x => by
      change cBc l (Reformulated.AutPerF.Bcris.frob l (OC l) _) = Formalism.Per6.φB l (cBc l _)
      rw [Reformulated.AutPerF.Bcris.frob_algebraMap_acris, cBc_algebraMap, cBc_algebraMap, hφ]
      exact (PositivityTheory.LocInh.φB_cB (cA l x)).symm
  exact RingHom.congr_fun h b

theorem cBc_aB (a : Reformulated.AutPerF.Ainf l (OC l)) :
    cBc l (algebraMap (Reformulated.AutPerF.Acris l (OC l)) (Reformulated.AutPerF.Bcris l (OC l))
      (algebraMap (Reformulated.AutPerF.Ainf l (OC l)) (Reformulated.AutPerF.Acris l (OC l)) a)) =
      Formalism.Per6.aB l a := by
  rw [cBc_algebraMap, cA_algebraMap]
  exact (PositivityTheory.LocInh.frob_aB_apply a).symm

theorem algebraMap_ainf_eq_zA (z : ℤ_[l]) :
    algebraMap ℤ_[l] (Reformulated.AutPerF.Ainf l (OC l)) z = Formalism.Per6.zA l z := rfl

theorem cBc_zB (z : ℤ_[l]) :
    cBc l (algebraMap ℚ_[l] (Reformulated.AutPerF.Bcris l (OC l)) (z : ℚ_[l])) = Formalism.Per6.zB l z := by
  have h : algebraMap ℤ_[l] (Reformulated.AutPerF.Acris l (OC l)) z =
      algebraMap (Reformulated.AutPerF.Ainf l (OC l)) (Reformulated.AutPerF.Acris l (OC l))
        (algebraMap ℤ_[l] (Reformulated.AutPerF.Ainf l (OC l)) z) := rfl
  rw [Reformulated.AutPerF.Bcris.algebraMap_padicInt, h, cBc_aB, algebraMap_ainf_eq_zA, Formalism.Per6.zB,
    RingHom.comp_apply]

end Cmp6
end
end

section -- merged from Development.WeilBound.CoreStatements.PeriodRingComparison.CrystallinePeriodRings.CAFrobAinf
noncomputable section
open GroundTheory.PAdicHodge
namespace Cmp6
variable (l : ℕ) [Fact l.Prime]

theorem cA_frob_ainf (w : Reformulated.AutPerF.Ainf l (OC l)) :
    cA l (Reformulated.AutPerF.Acris.frob l (OC l) (algebraMap (Reformulated.AutPerF.Ainf l (OC l)) (Reformulated.AutPerF.Acris l (OC l)) w)) =
      ACris.phi (K := ℂ_[l]) (p := l) (cA l (algebraMap (Reformulated.AutPerF.Ainf l (OC l)) (Reformulated.AutPerF.Acris l (OC l)) w)) := by
  rw [Reformulated.AutPerF.Acris.frob_algebraMap, cA_algebraMap, cA_algebraMap]
  have h : Formalism.Per6.ainfMap l (WittVector.frobenius w) =
      WittVector.frobenius (Formalism.Per6.ainfMap l w) := by
    ext n
    simp [Formalism.Per6.ainfMap, WittVector.map_coeff, WittVector.coeff_frobenius_charP]
  rw [ACris.phi_algebraMap]
  exact congrArg (algebraMap (AInf ℂ_[l] l) (ACris.ACris ℂ_[l] l)) h

theorem cA_frob (x : Reformulated.AutPerF.Acris l (OC l)) :
    cA l (Reformulated.AutPerF.Acris.frob l (OC l) x) = ACris.phi (K := ℂ_[l]) (p := l) (cA l x) := by
  have h : (cA l).toRingHom.comp (Reformulated.AutPerF.Acris.frob l (OC l)) =
      (ACris.phi (K := ℂ_[l]) (p := l)).comp (cA l).toRingHom := by
    refine Reformulated.AutPerF.Acris.hom_ext fun a => ?_
    have := zero_ext l
      (F := ((cA l).toRingHom.comp (Reformulated.AutPerF.Acris.frob l (OC l))).comp
        (algebraMap (Reformulated.AutPerF.AcrisZero l (OC l)) (Reformulated.AutPerF.Acris l (OC l))))
      (G := ((ACris.phi (K := ℂ_[l]) (p := l)).comp (cA l).toRingHom).comp
        (algebraMap (Reformulated.AutPerF.AcrisZero l (OC l)) (Reformulated.AutPerF.Acris l (OC l))))
      (fun w => by
        simp only [RingHom.comp_apply]
        rw [← IsScalarTower.algebraMap_apply]
        exact cA_frob_ainf l w) a
    simpa only [RingHom.comp_apply] using this
  exact RingHom.congr_fun h x

end Cmp6
end
end

noncomputable section

open GroundTheory.PAdicHodge Formalism.BasicNotions.Loc

namespace Cmp6

variable (l : ℕ) [Fact l.Prime]

theorem cPd_eq_cP : cPd l = cP l := rfl

theorem cD_zD (z : ℤ_[l]) :
    cD l (algebraMap ℚ_[l] (Reformulated.AutPerF.BdR l (OC l)) (z : ℚ_[l])) = Formalism.Per6.zD l z := by
  have h0 : algebraMap ℚ_[l] (Reformulated.AutPerF.AinfInv l (OC l)) (z : ℚ_[l]) =
      algebraMap (Reformulated.AutPerF.Ainf l (OC l)) (Reformulated.AutPerF.AinfInv l (OC l))
        (algebraMap ℤ_[l] (Reformulated.AutPerF.Ainf l (OC l)) z) :=
    Reformulated.AutPerF.padicLift_algebraMap l (algebraMap ℤ_[l] (Reformulated.AutPerF.AinfInv l (OC l)))
      (Reformulated.AutPerF.AinfInv.isUnit_p l (R := OC l)) z
  have h1 : algebraMap ℚ_[l] (Reformulated.AutPerF.BdR l (OC l)) (z : ℚ_[l]) =
      algebraMap (Reformulated.AutPerF.BdRPlus l (OC l)) (Reformulated.AutPerF.BdR l (OC l))
        (algebraMap (Reformulated.AutPerF.Ainf l (OC l)) (Reformulated.AutPerF.BdRPlus l (OC l))
          (algebraMap ℤ_[l] (Reformulated.AutPerF.Ainf l (OC l)) z)) := by
    change algebraMap (Reformulated.AutPerF.BdRPlus l (OC l)) (Reformulated.AutPerF.BdR l (OC l))
      (algebraMap (Reformulated.AutPerF.AinfInv l (OC l)) (Reformulated.AutPerF.BdRPlus l (OC l))
        (algebraMap ℚ_[l] (Reformulated.AutPerF.AinfInv l (OC l)) (z : ℚ_[l]))) = _
    rw [h0]
    rfl
  rw [h1, cD_algebraMap, cPd_eq_cP, comparison_algebraMap_ainf]
  rfl

theorem isLogA_iff_cP (ε : PreTilt ↥(PadicComplexInt l) l) (y : Reformulated.AutPerF.BdRPlus l (OC l)) :
    IsLogA l ε y ↔ Formalism.Per6.IsLog l ε (cP l y) :=
  isLogA_iff_of_compat l (cP l) (comparison_algebraMap_ainf l) (θD_cP l) ε y

theorem compat_native :
    (∀ z : ℤ_[l], cBc l (algebraMap ℚ_[l] (Reformulated.AutPerF.Bcris l (OC l)) (z : ℚ_[l])) = Formalism.Per6.zB l z) ∧
    (∀ z : ℤ_[l], cD l (algebraMap ℚ_[l] (Reformulated.AutPerF.BdR l (OC l)) (z : ℚ_[l])) = Formalism.Per6.zD l z) ∧
    (∀ y : Reformulated.AutPerF.BdRPlus l (OC l), cD l (algebraMap _ (Reformulated.AutPerF.BdR l (OC l)) y) =
      algebraMap (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l) (cP l y)) ∧
    (∀ y : Reformulated.AutPerF.BdRPlus l (OC l), Formalism.Per6.θD l (cP l y) =
      Reformulated.AutPerF.BdRPlus.thetaC l (PadicComplexInt l) y) ∧
    (∀ (g : GQ l) (b : Reformulated.AutPerF.Bcris l (OC l)), cBc l (g • b) = Formalism.Per6.σB g (cBc l b)) ∧
    (∀ (g : GQ l) (x : Reformulated.AutPerF.BdR l (OC l)), cD l (g • x) = Formalism.Per6.σD g (cD l x)) ∧
    (∀ b : Reformulated.AutPerF.Bcris l (OC l), cBc l (Reformulated.AutPerF.Bcris.frob l (OC l) b) = Formalism.Per6.φB l (cBc l b)) ∧
    (∀ (a : ℤ) (x : Reformulated.AutPerF.BdR l (OC l)), x ∈ Reformulated.AutPerF.BdR.fil l (OC l) a ↔ cD l x ∈ Formalism.Per6.FilD l a) ∧
    (∀ (ε : PreTilt ↥(PadicComplexInt l) l) (y : Reformulated.AutPerF.BdRPlus l (OC l)),
      IsLogA l ε y ↔ Formalism.Per6.IsLog l ε (cP l y)) ∧
    (∀ a : Reformulated.AutPerF.Ainf l (OC l), cBc l (algebraMap (Reformulated.AutPerF.Acris l (OC l)) (Reformulated.AutPerF.Bcris l (OC l))
      (algebraMap (Reformulated.AutPerF.Ainf l (OC l)) (Reformulated.AutPerF.Acris l (OC l)) a)) = Formalism.Per6.aB l a) :=
  ⟨cBc_zB l, cD_zD l, fun y => cD_algebraMap l y, θD_cP l, cBc_smul l, cD_gal l, cBc_frob_of l (cA_frob l), cD_fil l, isLogA_iff_cP l, cBc_aB l⟩

end Cmp6
