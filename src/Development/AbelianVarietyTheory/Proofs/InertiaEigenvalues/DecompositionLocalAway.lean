module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousTwistedDualRhoO
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsGenericOfIsLocComp
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ThetaDistributionHeisenbergInvariant
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseChangeSpehOfDiscreteSeries
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EquivContra
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TwistSeries
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SegmentLinkedShift
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSupportedAtSplitPlaceUnitaryMatrixEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicWhittakerEquivariantBumpMirabolic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugatePlaces
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecTExistsIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftLevelFormOrthogonalKilledByThetaMap
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.HkSupSizedOfHkSup

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecompositionLocalAway
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

noncomputable section
namespace GlobalTheory.CrysChiOne

variable {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
  {hw : w ∈ placesOver D.host.E (D.nd.l i)}

theorem locC_cont' (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (hM : Continuous fun g => M g) : Continuous fun g => TruncatedSeriesCountingIdentities.locC C M g := by
  refine continuous_matrix fun a b => ?_
  have h1 : Continuous fun g : Br.G D.nbr i w hw => M ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd) a b :=
    (hM.matrix_elem a b).comp (continuous_subtype_val.comp (Br.iota_cont D.nbr i w hw))
  have h2 : Continuous fun y : D.nd.O i => (((D.nbr i w hw).eO y : ↥(OL (D.nbr i w hw).LL)) :
      ↥(D.nbr i w hw).LL.1) := continuous_subtype_val.comp (D.nbr i w hw).eO_cont
  have h3 : Continuous fun y : ↥(D.nbr i w hw).LL.1 => C.inc y :=
    Continuous.subtype_mk continuous_subtype_val _
  exact h3.comp (h2.comp h1)

theorem sub_crys (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (hF : TruncatedSeriesCountingIdentities.FontaineAt (Br.PD D.loc D.nbr i w hw) ↥C.LL.1 ↥(OL C.LL))
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i)
    (hcr : IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r π))))
    (hcont : Continuous fun g => rO D.nd i r π g)
    {k : ℕ} (N : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hN : Continuous fun g => N g)
    (B : Matrix (Fin D.R.nV) (Fin k) (KK D.nd i)) (A : Matrix (Fin k) (Fin D.R.nV) (KK D.nd i))
    (hAB : A * B = 1)
    (hint : ∀ g, mapM (toK D.nd i) (rO D.nd i r π) g * B = B * mapM (toK D.nd i) N g) :
    IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C N)) := by
  let φ := GlobalTheory.HTW.RecS.Model.phiK i w hw C
  let Bt : Matrix (Fin D.R.nV) (Fin k) ↥C.LL.1 := B.map φ
  have hinj : Function.Injective Bt.mulVec := by
    have h1 : A.map φ * Bt = 1 := by
      rw [← Matrix.map_mul, hAB, Matrix.map_one _ (map_zero φ) (map_one φ)]
    intro u v huv
    have := congrArg (A.map φ).mulVec huv
    simpa only [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec] using this
  have hcN : ∀ (_ : Unit) (v : Fin k → ↥C.LL.1), Continuous fun g => (TruncatedSeriesCountingIdentities.locC C N g).mulVec v :=
    fun _ v => (locC_cont' C N hN).matrix_mulVec continuous_const
  have hcR : ∀ (_ : Unit) (v : Fin D.R.nV → ↥C.LL.1), Continuous fun g => (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r π) g).mulVec v :=
    fun _ v => (locC_cont' C _ hcont).matrix_mulVec continuous_const
  have hsub : IsSubOfSums (GRep.mat (Qp := ℚ_[D.nd.l i]) (O := ↥(OL C.LL)) (fun _ : Unit => TruncatedSeriesCountingIdentities.locC C N) hcN ()).ρ
      (fun _ : Unit => ⇑(TruncatedSeriesCountingIdentities.locC C (rO D.nd i r π))) := by
    refine ⟨1, fun _ => (), LinearMap.pi fun _ => Matrix.mulVecLin Bt, ?_, fun g v => ?_⟩
    · intro u v huv
      exact hinj (congrFun huv 0)
    · have key : ∀ (u : Fin k → ↥C.LL.1), Bt.mulVec ((TruncatedSeriesCountingIdentities.locC C N g).mulVec u) =
          (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r π) g).mulVec (Bt.mulVec u) := by
        intro u
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
        congr 1
        rw [GlobalTheory.HTW.RecS.Model.locC_eq_map, GlobalTheory.HTW.RecS.Model.locC_eq_map]
        simp only [Bt]
        rw [← Matrix.map_mul, ← Matrix.map_mul, hint]
      funext a
      exact key v
  exact (subsum_crys (fun _ : Unit => TruncatedSeriesCountingIdentities.locC C (rO D.nd i r π)) hcR hF (S := fun _ => Set.univ)
    (fun _ => hcr) (fun _ _ _ _ => Set.mem_univ _) _ hsub).1

def chiM (c : ℕ) : GE D.nd →* Matrix (Fin 1) (Fin 1) (D.nd.O i) :=
  twistM (1 : GE D.nd →* Matrix (Fin 1) (Fin 1) (D.nd.O i)) (chiU D.nd i c)

theorem decomp_rho (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (hd : TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r ρ π) :
    ∃ (B : Matrix (Fin D.R.nV) (Fin D.R.r) (KK D.nd i)) (A : Matrix (Fin D.R.r) (Fin D.R.nV) (KK D.nd i)),
      A * B = 1 ∧ ∀ g, mapM (toK D.nd i) (rO D.nd i r π) g * B = B * mapM (toK D.nd i) (rhoO D.nd i ρ π) g := by
  obtain ⟨e, he⟩ := hd
  refine ⟨LinearMap.toMatrix' (e.symm.toLinearMap ∘ₗ LinearMap.inl (KK D.nd i) _ _),
    LinearMap.toMatrix' (LinearMap.fst (KK D.nd i) _ _ ∘ₗ e.toLinearMap), ?_, fun g => ?_⟩
  · rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1
    refine LinearMap.ext fun v => ?_
    simp
  · apply Matrix.toLin'.injective
    refine LinearMap.ext fun u => ?_
    simp only [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', LinearMap.comp_apply, Matrix.toLin'_apply,
      LinearEquiv.coe_coe]
    apply e.injective
    rw [he]
    simp
    rfl

theorem decomp_chi (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (hd : TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r ρ π) :
    ∃ (B : Matrix (Fin D.R.nV) (Fin 1) (KK D.nd i)) (A : Matrix (Fin 1) (Fin D.R.nV) (KK D.nd i)),
      A * B = 1 ∧ ∀ g, mapM (toK D.nd i) (rO D.nd i r π) g * B = B * mapM (toK D.nd i) (chiM (D := D) (i := i) 1) g := by
  obtain ⟨e, he⟩ := hd
  have ht : 0 < D.R.t := by
    have := D.R.rank_add_five_le
    omega
  let c0 : Fin D.R.t := ⟨0, ht⟩
  let L : (Fin 1 → KK D.nd i) →ₗ[KK D.nd i] (Fin D.R.t → KK D.nd i) :=
    LinearMap.single (KK D.nd i) (fun _ => KK D.nd i) c0 ∘ₗ LinearMap.proj 0
  let L' : (Fin D.R.t → KK D.nd i) →ₗ[KK D.nd i] (Fin 1 → KK D.nd i) :=
    LinearMap.pi fun _ => LinearMap.proj c0
  refine ⟨LinearMap.toMatrix' (e.symm.toLinearMap ∘ₗ LinearMap.inr (KK D.nd i) _ _ ∘ₗ L),
    LinearMap.toMatrix' (L' ∘ₗ LinearMap.snd (KK D.nd i) _ _ ∘ₗ e.toLinearMap), ?_, fun g => ?_⟩
  · rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1
    refine LinearMap.ext fun v => ?_
    funext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    simp [L, L']
  · apply Matrix.toLin'.injective
    refine LinearMap.ext fun u => ?_
    simp only [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', LinearMap.comp_apply, Matrix.toLin'_apply,
      LinearEquiv.coe_coe]
    apply e.injective
    rw [he]
    simp only [LinearEquiv.apply_symm_apply, LinearMap.inr_apply]
    ext c
    · simp
    · simp only [L, LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.single_apply]
      by_cases hc : c = c0
      · subst hc
        simp [chiM, twistM, mapM, Matrix.mulVec, dotProduct, c0]
      · simp [Pi.single_apply, hc]

theorem chiM_cont (c : ℕ) : Continuous fun g => chiM (D := D) (i := i) c g := by
  have : (fun g => chiM (D := D) (i := i) c g) = fun g => ((D.nd.chi i c g : (D.nd.O i)ˣ) : D.nd.O i) • (1 : Matrix (Fin 1) (Fin 1) (D.nd.O i)) := by
    funext g
    simp [chiM, twistM]
  rw [this]
  exact (D.nd.chi_cont i c).smul continuous_const

theorem locC_chiM_apply (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (g : Br.G D.nbr i w hw) :
    TruncatedSeriesCountingIdentities.locC C (chiM (D := D) (i := i) 1) g 0 0 = ((TruncatedSeriesCountingIdentities.chi1C C g : (↥C.LL.1)ˣ) : ↥C.LL.1) := by
  simp [TruncatedSeriesCountingIdentities.locC, TruncatedSeriesCountingIdentities.chi1C, chiM, twistM, Br.loc, Br.locChi, Br.locM, Br.locO, Br.chiG, mapM, LocBridge.toLL]

theorem chi1inv_crys (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (hF : TruncatedSeriesCountingIdentities.FontaineAt (Br.PD D.loc D.nbr i w hw) ↥C.LL.1 ↥(OL C.LL))
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (hd : TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r ρ π)
    (hcr : IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r π))))
    (hcont : Continuous fun g => rO D.nd i r π g) :
    IsCrys (Br.PD D.loc D.nbr i w hw) (WeaklyAdmissibleFiltrations.charRep (TruncatedSeriesCountingIdentities.chi1C C)⁻¹) := by
  obtain ⟨B, A, hAB, hint⟩ := decomp_chi r ρ π hd
  have h1 : IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (chiM (D := D) (i := i) 1))) :=
    sub_crys C hF r π hcr hcont _ (chiM_cont 1) B A hAB hint
  have h2 := (GlobalTheory.HTW.Rec.tateDual_matRep_crys (D.loc (D.nd.l i)) (D.nbr i w hw).Kw C.LL
    (TruncatedSeriesCountingIdentities.locC C (chiM (D := D) (i := i) 1)) hF.2.2.1 (locC_cont' C _ (chiM_cont 1)) h1).2
  have h3 : IsCrys (Br.PD D.loc D.nbr i w hw)
      (WeaklyAdmissibleFiltrations.charRep ((TruncatedSeriesCountingIdentities.chi1C C)⁻¹ * cycLL (Br.PD D.loc D.nbr i w hw) ↥C.LL.1)) := by
    refine GlobalTheory.Cmp.WachMonoidal.isCrys_of_equiv _ (LinearEquiv.funUnique (Fin 1) ↥C.LL.1 ↥C.LL.1) ?_ h2
    intro g v
    simp only [LinearEquiv.funUnique_apply, Function.eval]
    change ((twistM (dualM (TruncatedSeriesCountingIdentities.locC C (chiM (D := D) (i := i) 1))) _ g).mulVec v) 0 = _
    simp [twistM, dualM, Matrix.mulVec, dotProduct, WeaklyAdmissibleFiltrations.charRep, locC_chiM_apply]
    left
    rw [mul_comm]
    rfl
  exact (GlobalTheory.BlockCrys.isCrys_mul_cyc _ _).1 h3

theorem twist_crys (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (hF : TruncatedSeriesCountingIdentities.FontaineAt (Br.PD D.loc D.nbr i w hw) ↥C.LL.1 ↥(OL C.LL))
    {k : ℕ} (M : Br.G D.nbr i w hw →* Matrix (Fin k) (Fin k) ↥C.LL.1) (χ : Br.G D.nbr i w hw →* (↥C.LL.1)ˣ)
    (hM : Continuous fun g => M g) (hM' : Continuous fun g => twistM M χ g)
    (hχ : IsCrys (Br.PD D.loc D.nbr i w hw) (WeaklyAdmissibleFiltrations.charRep χ))
    (hcr : IsCrys (Br.PD D.loc D.nbr i w hw) (matRep M)) :
    IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (twistM M χ)) := by
  have hc : ∀ (_ : Unit) (v : Fin k → ↥C.LL.1), Continuous fun g => (M g).mulVec v :=
    fun _ v => hM.matrix_mulVec continuous_const
  have hc' : ∀ (_ : Unit) (v : Fin k → ↥C.LL.1), Continuous fun g => (twistM M χ g).mulVec v :=
    fun _ v => hM'.matrix_mulVec continuous_const
  refine (hF.2.1 (GRep.mat (Qp := ℚ_[D.nd.l i]) (O := ↥(OL C.LL)) (fun _ : Unit => M) hc ())
    (GRep.mat (Qp := ℚ_[D.nd.l i]) (O := ↥(OL C.LL)) (fun _ : Unit => twistM M χ) hc' ()) χ
    ⟨LinearEquiv.refl _ _, fun g x => ?_⟩ hχ hcr).1
  have key : ∀ u : Fin k → ↥C.LL.1, (twistM M χ g).mulVec u = ((χ g : (↥C.LL.1)ˣ) : ↥C.LL.1) • (M g).mulVec u := by
    intro u
    ext j
    simp [twistM, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  exact key x

theorem locC_WpO (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))
    (π : D.nd.X i) :
    TruncatedSeriesCountingIdentities.locC C (WpO D.nd i ρ π) = twistM (TruncatedSeriesCountingIdentities.locC C (rhoO D.nd i ρ π)) (TruncatedSeriesCountingIdentities.chi1C C)⁻¹ := by
  apply MonoidHom.ext
  intro g
  apply Matrix.ext
  intro a b
  have key : ∀ u v : D.nd.O i, C.inc ((D.nbr i w hw).toLL (u * v)) =
      C.inc ((D.nbr i w hw).toLL u) * C.inc ((D.nbr i w hw).toLL v) := by
    intro u v
    rw [map_mul, map_mul]
  exact key _ _

theorem cyc_locC (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (g : Br.G D.nbr i w hw) :
    ((cycLL (Br.PD D.loc D.nbr i w hw) ↥C.LL.1 g : (↥C.LL.1)ˣ) : ↥C.LL.1) =
      C.inc ((D.nbr i w hw).toLL ((epsU D.nd i (decS D.nd w (Br.iota D.nbr i w hw g)) : (D.nd.O i)ˣ) : D.nd.O i)) := by
  have h := congrArg (fun u : (Br.LL D.nbr i w hw)ˣ => C.inc (u : Br.LL D.nbr i w hw))
    (GlobalTheory.CycBridge.locChi_epsU D i w hw g)
  refine Eq.trans ?_ h.symm
  exact ((IntermediateField.inclusion C.le).commutes _).symm

theorem locC_rDuO (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (x : D.nd.X i) :
    TruncatedSeriesCountingIdentities.locC C (rDuO D.nd i r x) =
      twistM (dualM (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x))) (cycLL (Br.PD D.loc D.nbr i w hw) ↥C.LL.1) := by
  ext g a b
  simp only [twistM, dualM, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.smul_apply, Matrix.transpose_apply,
    smul_eq_mul, cyc_locC]
  congr 1
  show C.inc ((D.nbr i w hw).toLL (rDuO D.nd i r x (decS D.nd w (Br.iota D.nbr i w hw g)) a b)) =
    C.inc ((D.nbr i w hw).toLL ((epsU D.nd i (decS D.nd w (Br.iota D.nbr i w hw g)) : (D.nd.O i)ˣ) : D.nd.O i)) *
      C.inc ((D.nbr i w hw).toLL (rTwO D.nd i r x (decS D.nd w (Br.iota D.nbr i w hw g⁻¹)) b a))
  rw [← map_mul, ← map_mul, map_inv, map_inv]
  congr 2
  all_goals (simp [rDuO, rTwO, T2O, WpO, twistM, dualM] <;> ring)

theorem locC_T2O (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))
    (π : D.nd.X i) :
    TruncatedSeriesCountingIdentities.locC C (T2O D.nd i ρ π) =
      twistM (dualM (TruncatedSeriesCountingIdentities.locC C (WpO D.nd i ρ π))) (cycLL (Br.PD D.loc D.nbr i w hw) ↥C.LL.1) := by
  ext g a b
  simp only [twistM, dualM, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.smul_apply, Matrix.transpose_apply,
    smul_eq_mul, cyc_locC]
  congr 1
  show C.inc ((D.nbr i w hw).toLL (T2O D.nd i ρ π (decS D.nd w (Br.iota D.nbr i w hw g)) a b)) =
    C.inc ((D.nbr i w hw).toLL ((epsU D.nd i (decS D.nd w (Br.iota D.nbr i w hw g)) : (D.nd.O i)ˣ) : D.nd.O i)) *
      C.inc ((D.nbr i w hw).toLL (WpO D.nd i ρ π (decS D.nd w (Br.iota D.nbr i w hw g⁻¹)) b a))
  rw [← map_mul, ← map_mul, map_inv, map_inv]
  congr 2
  all_goals (simp [rDuO, rTwO, T2O, WpO, twistM, dualM] <;> ring)

end GlobalTheory.CrysChiOne
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPsiLocNeOne
noncomputable section

open NumberField IsDedekindDomain Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep Formalism.UG

namespace GlobalTheory.StdCharConductor

variable (E : Type) [Field E] [NumberField E]

def psi : AddChar (Ad E) ℂ := Circle.coeHom.compAddChar (GroundTheory.Global.adelicChar E)

theorem psi_apply (x : Ad E) : psi E x = (GroundTheory.Global.adelicChar E x : ℂ) := rfl

variable {E}

theorem psi_loc (w : HeightOneSpectrum (𝓞 E)) (y : w.adicCompletion E) :
    psi E (sFin E (sLoc E w y)) = (GroundTheory.Global.localAdelicChar E w y : ℂ) := by
  classical
  rw [psi_apply, GroundTheory.Global.localAdelicChar_apply]
  congr 2

theorem psi_loc_eq_one_iff (w : HeightOneSpectrum (𝓞 E)) (y : w.adicCompletion E) :
    psi E (sFin E (sLoc E w y)) = 1 ↔ GroundTheory.Global.localAdelicChar E w y = 1 := by
  rw [psi_loc]
  exact Circle.coe_eq_one

theorem exists_psi_loc_ne_one (w : HeightOneSpectrum (𝓞 E)) :
    ∃ y : w.adicCompletion E, psi E (sFin E (sLoc E w y)) ≠ 1 := by
  by_contra h
  push Not at h
  refine GroundTheory.Global.localAdelicChar_ne_one (K := E) w (DFunLike.ext _ _ fun y => ?_)
  rw [AddChar.one_apply]
  exact (psi_loc_eq_one_iff w y).1 (h y)


variable (E) in
theorem stdPsi_psi : StdPsi (psi E) := by
  have hc : Continuous (psi E) := continuous_subtype_val.comp (GroundTheory.Global.continuous_adelicChar (K := E))
  have hr : ∀ c : E, psi E (algebraMap E (Ad E) c) = 1 := fun c => by
    rw [psi_apply, GroundTheory.Global.adelicChar_algebraMap]
    rfl
  have hne : psi E ≠ 1 := fun h => GroundTheory.Global.adelicChar_ne_one (K := E) (DFunLike.ext _ _ fun x => by
    have := DFunLike.congr_fun h x
    rw [psi_apply, AddChar.one_apply] at this
    rw [AddChar.one_apply]
    exact Circle.coe_eq_one.1 this)
  letI : Invertible (2 : E) := invertibleOfNonzero two_ne_zero
  letI : Invertible (2 : Ad E) := (Invertible.map (algebraMap E (Ad E)) 2).copy 2 (map_ofNat _ 2).symm
  have h := GlobalTheory.CompanionTheory.AdeleAnn.unitary_and_annihilator_eq E (psi E) hc hne hr
  exact ⟨hc, h.1, hr, h.2, exists_psi_loc_ne_one⟩

end GlobalTheory.StdCharConductor

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalComponentsThetaPull
open NumberField IsDedekindDomain Matrix Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.UG Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.BCWords GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.ThetaPull

noncomputable section

namespace GlobalTheory.ConjPairLoc

theorem irred_comp {G H V : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V)
    (φ : G →* H) (hφ : Function.Surjective φ) (h : ρ.IsIrreducible) :
    Representation.IsIrreducible (MonoidHom.comp ρ φ) := by
  let e : Subrepresentation (MonoidHom.comp ρ φ : Representation ℂ G V) ≃o Subrepresentation ρ :=
    { toFun := fun W => ⟨W.toSubmodule, fun g v hv => by
        obtain ⟨g, rfl⟩ := hφ g
        exact W.apply_mem_toSubmodule g hv⟩
      invFun := fun W => ⟨W.toSubmodule, fun g v hv => W.apply_mem_toSubmodule (φ g) hv⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  exact e.isSimpleOrder

theorem equiv_apply {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {τ : Representation ℂ G W} (e : ρ.Equiv τ) (g : G) (x : V) :
    e.toLinearEquiv (ρ g x) = τ g (e.toLinearEquiv x) :=
  LinearMap.congr_fun (e.isIntertwining' g) x

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem gl_ext {k k' : GL (Fin a) (Af E)}
    (h : ∀ v, GeneralLinearGroup.map (pLoc E v) k = GeneralLinearGroup.map (pLoc E v) k') : k = k' := by
  ext i j : 2
  exact FiniteAdeleRing.ext _ fun v => congrArg (fun g : GL (Fin a) (v.adicCompletion E) => g.val i j) (h v)

theorem conjFin_locGL (c : E ≃+* E) (v : HeightOneSpectrum (𝓞 E)) (g : GL (Fin a) ((conjSrc c v).adicCompletion E)) :
    GeneralLinearGroup.map (conjFin c) (locGL E a _ g) = locGL E a v (GeneralLinearGroup.map (conjLoc c v) g) := by
  refine gl_ext fun u => ?_
  have e : GeneralLinearGroup.map (pLoc E u) (GeneralLinearGroup.map (conjFin c) (locGL E a _ g)) =
      GeneralLinearGroup.map (conjLoc c u) (GeneralLinearGroup.map (pLoc E (conjSrc c u)) (locGL E a _ g)) := by
    ext i j
    rfl
  rw [e]
  by_cases h : u = v
  · subst h
    rw [pLoc_locGL, pLoc_locGL]
  · rw [pLoc_locGL_of_ne h, pLoc_locGL_of_ne (fun e => h (conjSrc_injective c e)), map_one]

theorem map_conjLoc_surjective [IsCMField E] (v : HeightOneSpectrum (𝓞 E)) :
    Function.Surjective (GeneralLinearGroup.map (n := Fin a) (conjLoc (IsCMField.complexConj E).toRingEquiv v)) := by
  intro g
  refine ⟨GeneralLinearGroup.map (pLoc E _) (GeneralLinearGroup.map (cFin E) (locGL E a v g)), ?_⟩
  conv_rhs => rw [← pLoc_locGL v g]
  ext i j : 2
  exact congrArg (pLoc E v) (cFin_cFin _)

end GlobalTheory.ConjPairLoc

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsRatConstMul
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SerRatRay

theorem isRat_const_mul {D : D7} (T : CoreJ D) (i : Fin D.R.m) {σ : T.Q.c.F →+* ℂ} (hV : T.V ((i : ℕ) + 1) σ = Wc D i)
    (C : Cover T ((i : ℕ) + 1) σ) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (φ : GA D (Wc D i) → ℂ) (c : ℂ)
    (h : IsRat T i hV C κ φ) (hc : c ∈ C.σ₂.fieldRange) : IsRat T i hV C κ (fun g => c * φ g) := by
  obtain ⟨φ', ⟨f₂, hf₂, rfl⟩, rfl⟩ := h
  obtain ⟨c', rfl⟩ := RingHom.mem_fieldRange.1 hc
  refine ⟨C.rd (wtA κ) (c' • f₂), ⟨c' • f₂, ⟨(sec _ _ _ _).smul_mem c' hf₂.1, ?_⟩, rfl⟩, ?_⟩
  · rw [map_smulₛₗ]
    exact Submodule.smul_mem _ _ hf₂.2
  · funext g
    simp only [castDict, Cover.rd, map_smulₛₗ, map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

end GlobalTheory.SerRatRay
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsExtensionCharacterTwist
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLanglandsClassificationTwistMultisegment
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLanglandsClassificationTwistMultisegment
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocGL

theorem isL_map_tw_of_isL : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [CharZero k] (𝔪 : Multiset (Segment k)) (x : IrrGL (k := k)) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ),
    IsL 𝔪 x.rep → IsL (𝔪.map fun Δ => Δ.tw χ hχ) (x.tw χ hχ).rep := by
  intro k _ _ _ _ _ 𝔪 x χ hχ h
  exact (h.tw χ hχ).of_equiv (x.twEquiv χ hχ)

end GlobalTheory.LocGL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLanglandsClassificationTwistMultisegmentStatement
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLanglandsClassification_twist_multisegment : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (𝔪 : Multiset (Segment k)) (x : IrrGL (k := k)) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ), IsL 𝔪 x.rep → IsL (𝔪.map fun Δ => Δ.tw χ hχ) (x.tw χ hχ).rep := by
  first | exact @GlobalTheory.LocGL.isL_map_tw_of_isL | exact GlobalTheory.LocGL.isL_map_tw_of_isL | (intros; apply GlobalTheory.LocGL.isL_map_tw_of_isL <;> assumption)
end
end

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands.ExtTwist

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem lpTwist_lpTwist_comm (x : WD h) (ξ η : Weil h →* ℂˣ) (hξ : WeilDeligne.IsSmooth ξ)
    (hη : WeilDeligne.IsSmooth η) : (x.lpTwist ξ hξ).lpTwist η hη = (x.lpTwist η hη).lpTwist ξ hξ := by
  obtain ⟨n, b, rfl⟩ := x.exists_rep
  simp only [WD.lpTwist_mk]
  exact WD.sound ⟨LinearEquiv.refl ℂ _, fun σ v => smul_comm (η σ : ℂ) (ξ σ : ℂ) (b.ρ σ v), fun v => rfl⟩

theorem hasCentralChar_ofChar {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) : HasCentralChar (IrrGL.ofChar χ hχ).rep χ := fun z v => by
  let φ := equivRep (IrrRep.det (Fin 1) χ hχ)
  obtain ⟨u, rfl⟩ := φ.toLinearEquiv.surjective v
  have h2 : GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 1) z) = z := by
    ext; simp [GeneralLinearGroup.scalar]
  have h3 : (IrrRep.det (Fin 1) χ hχ).ρ (GeneralLinearGroup.scalar (Fin 1) z) u = (χ z : ℂ) • u := by
    show (χ (GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 1) z)) : ℂ) • u = _
    rw [h2]
  show (IrrRep.det (Fin 1) χ hχ).cl.rep.ρ (GeneralLinearGroup.scalar (Fin 1) z) (φ.toIntertwiningMap u) =
    _ • φ.toIntertwiningMap u
  rw [← φ.toIntertwiningMap.isIntertwining, h3, map_smul]
  rfl

end GlobalTheory.LocLanglands.ExtTwist

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIdempotentElemIdemSf
noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep
open scoped ContDiff

namespace GlobalTheory.SchurExt

def idemHom {R : Type} [CommRing R] (e : R) (he : IsIdempotentElem e) : R →ₙ+* R where
  toFun x := e * x
  map_mul' x y := by
    change e * (x * y) = e * x * (e * y)
    calc e * (x * y) = (e * e) * (x * y) := by rw [he.eq]
      _ = e * x * (e * y) := by ring
  map_zero' := mul_zero e
  map_add' x y := mul_add e x y

variable {E : Type} [Field E] [NumberField E]


open Classical in
def idemSf (S : Finset (HeightOneSpectrum (𝓞 E))) : Af E :=
  ⟨fun w => if w ∈ S then 1 else 0, Filter.Eventually.of_forall fun w => by
    by_cases h : w ∈ S
    · simp only [h, if_true]; exact one_mem _
    · simp only [h, if_false]; exact zero_mem _⟩

theorem isIdempotentElem_idemSf (S : Finset (HeightOneSpectrum (𝓞 E))) : IsIdempotentElem (idemSf S) := by
  classical
  refine Subtype.ext (funext fun w => ?_)
  change (if w ∈ S then (1 : w.adicCompletion E) else 0) * (if w ∈ S then 1 else 0) = if w ∈ S then 1 else 0
  split_ifs <;> simp

def idemS (S : Finset (HeightOneSpectrum (𝓞 E))) : Ad E := ((1 : InfiniteAdeleRing E), idemSf S)

theorem isIdempotentElem_idemS (S : Finset (HeightOneSpectrum (𝓞 E))) : IsIdempotentElem (idemS S) :=
  Prod.ext (mul_one _) (isIdempotentElem_idemSf S).eq

def prS (S : Finset (HeightOneSpectrum (𝓞 E))) (a : ℕ) : GA E a →* GA E a :=
  cornerGL a (idemHom (idemS S) (isIdempotentElem_idemS S))

def prO (S : Finset (HeightOneSpectrum (𝓞 E))) (a : ℕ) : GA E a →* GA E a :=
  cornerGL a (idemHom (1 - idemS S) (isIdempotentElem_idemS S).one_sub)

def prSf (S : Finset (HeightOneSpectrum (𝓞 E))) (a : ℕ) : GL (Fin a) (Af E) →* GL (Fin a) (Af E) :=
  cornerGL a (idemHom (idemSf S) (isIdempotentElem_idemSf S))

def prOf (S : Finset (HeightOneSpectrum (𝓞 E))) (a : ℕ) : GL (Fin a) (Af E) →* GL (Fin a) (Af E) :=
  cornerGL a (idemHom (1 - idemSf S) (isIdempotentElem_idemSf S).one_sub)

def eqv (m r : ℕ) : Fin (m + r + 1 + 1) ≃ Fin (m + 1) ⊕ Fin (r + 1) :=
  (finCongr (by omega)).trans finSumFinEquiv.symm

section Blocks

variable {R : Type} [CommRing R] {m r : ℕ}

def blk (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) :
    Matrix (Fin (m + 1) ⊕ Fin (r + 1)) (Fin (m + 1) ⊕ Fin (r + 1)) R :=
  M.submatrix (eqv m r).symm (eqv m r).symm

def unblk (P : Matrix (Fin (m + 1) ⊕ Fin (r + 1)) (Fin (m + 1) ⊕ Fin (r + 1)) R) :
    Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R :=
  P.submatrix (eqv m r) (eqv m r)

def Aof (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) : Matrix (Fin (m + 1)) (Fin (m + 1)) R :=
  (blk M).toBlocks₁₁

def Bof (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) : Matrix (Fin (m + 1)) (Fin (r + 1)) R :=
  (blk M).toBlocks₁₂

def Cof (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) : Matrix (Fin (r + 1)) (Fin (m + 1)) R :=
  (blk M).toBlocks₂₁

def Dof (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) : Matrix (Fin (r + 1)) (Fin (r + 1)) R :=
  (blk M).toBlocks₂₂

def Xof (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) : Matrix (Fin (m + 1)) (Fin (r + 1)) R :=
  Bof M * (Dof M)⁻¹

def Yof (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) : Matrix (Fin (r + 1)) (Fin (m + 1)) R :=
  (Dof M)⁻¹ * Cof M

def Scof (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) : Matrix (Fin (m + 1)) (Fin (m + 1)) R :=
  Aof M - Bof M * (Dof M)⁻¹ * Cof M

theorem unblk_blk (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) : unblk (blk M) = M := by
  ext i j; simp [unblk, blk]

theorem blk_unblk (P : Matrix (Fin (m + 1) ⊕ Fin (r + 1)) (Fin (m + 1) ⊕ Fin (r + 1)) R) : blk (unblk P) = P := by
  ext i j; simp [unblk, blk]

end Blocks


open Classical in
def mkGL {R : Type} [CommRing R] {k : ℕ} (M : Matrix (Fin k) (Fin k) R) : GL (Fin k) R :=
  if h : IsUnit M.det then Matrix.nonsingInvUnit M h else 1

theorem coe_mkGL {R : Type} [CommRing R] {k : ℕ} {M : Matrix (Fin k) (Fin k) R} (h : IsUnit M.det) :
    ((mkGL M : GL (Fin k) R) : Matrix (Fin k) (Fin k) R) = M := by
  rw [mkGL, dite_eq_left h]; rfl

def psi (x : Ad E) : ℂ := (GroundTheory.Global.adelicChar E x : ℂ)

variable [_root_.NumberField.IsTotallyComplex E]

def chiF {m r : ℕ} (χ : (Fin (r + 1) → Fin (m + 1) → Cinf E) → ℝ) (Y : Matrix (Fin (r + 1)) (Fin (m + 1)) (Ad E)) : ℂ :=
  open Classical in
  (χ (fun i j => pInf E (Y i j)) : ℂ) *
    (if ∀ i j, pFin E (Y i j) ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E then 1 else 0)

def schurF {m r : ℕ} (β : GA E (m + 1) → ℂ) (b₁ : GA E (r + 1) → ℂ) (χ : (Fin (r + 1) → Fin (m + 1) → Cinf E) → ℝ)
    (g : GA E (m + r + 1 + 1)) : ℂ :=
  open Classical in
  if IsUnit (Dof (g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det then
    psi (Xof (g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) (Fin.last m) 0) *
      β (mkGL (Scof (g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)))) *
      b₁ (mkGL (Dof (g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)))) *
      chiF χ (Yof (g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)))
  else 0

def extB {m r : ℕ} (S : Finset (HeightOneSpectrum (𝓞 E))) (β : GA E (m + 1) → ℂ) (b₁ : GA E (r + 1) → ℂ)
    (χ : (Fin (r + 1) → Fin (m + 1) → Cinf E) → ℝ) (Φ : GA E (m + r + 1 + 1) → ℂ) (g : GA E (m + r + 1 + 1)) : ℂ :=
  schurF β b₁ χ (prS S _ g) * Φ (prO S _ g)

end GlobalTheory.SchurExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSplitPlacesDeclarationSplitRowPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSplitPlacesDeclarationSplitRowPrime
noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
open Classical

namespace GlobalTheory.SplitDecl

variable {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
  {hw : w ∈ placesOver D.host.E (D.nd.l i)}

theorem embTypeUc_iff (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw) :
    EmbeddingTypes.EmbTypeUc τ ↔ GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.EmbIn (N := D.nd) D.nbr i false w hw τ := by
  constructor
  · rintro ⟨h1, φ, hφ, h2⟩
    refine ⟨h1, (starRingEnd ℂ).comp φ, ?_, fun x y hy => by simpa using h2 x y hy⟩
    show ((starRingEnd ℂ).comp φ).comp (D.host.conj : D.host.E →+* D.host.E) ∈
      D.host.cmType
    have : ((starRingEnd ℂ).comp φ).comp (D.host.conj : D.host.E →+* D.host.E) = φ := by
      ext1 x
      simp [GlobalTheory.SplitRowProbe.conj_sqrt]
    rw [this]; exact hφ
  · rintro ⟨h1, ψ, hψ, h2⟩
    refine ⟨h1, ψ.comp (D.host.conj : D.host.E →+* D.host.E), hψ, fun x y hy => ?_⟩
    rw [h2 x y hy]
    simp [GlobalTheory.SplitRowProbe.conj_sqrt]

theorem embTypeUe_iff (ep : Bool) (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw) :
    EmbeddingTypes.EmbTypeUe ep τ ↔ GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.EmbIn (N := D.nd) D.nbr i ep w hw τ := by
  cases ep
  · simp only [EmbeddingTypes.EmbTypeUe, Bool.false_eq_true, if_false]
    exact embTypeUc_iff τ
  · simp only [EmbeddingTypes.EmbTypeUe, if_true]
    rfl

theorem plTypeUe_iff (ep : Bool) :
    EmbeddingTypes.PlTypeUe i w hw ep ↔ GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.PlIn (N := D.nd) D.nbr i ep w hw := by
  constructor
  · intro h
    exact ⟨GlobalTheory.SplitRowProbe.nonempty_emb D i w hw, fun τ => (embTypeUe_iff ep τ).1 (h τ)⟩
  · intro h τ
    exact (embTypeUe_iff ep τ).2 (h.2 τ)

theorem placesOver_finite (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p ≠ 0) :
    (placesOver E p).Finite := by
  have h0 : Ideal.span {((p : ℕ) : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  show v.asIdeal ∣ _
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv

def decl (D : D7) (i : D.nd.Loc) (hl : D.nd.l i ≠ 0) (ep : Bool) : TruncatedSeriesCountingIdentities.Decl D i where
  row := (placesOver_finite D.host.E (D.nd.l i) hl).toFinset.filter
    (fun v => v ∉ GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.columns (N := D.nd) D.nbr i ep)
  col := (placesOver_finite D.host.E (D.nd.l i) hl).toFinset.filter
    (fun v => v ∈ GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.columns (N := D.nd) D.nbr i ep)
  disj := by
    rw [Finset.disjoint_left]
    intro v h1 h2
    exact (Finset.mem_filter.1 h1).2 (Finset.mem_filter.1 h2).2
  cover := by
    intro v
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset]
    tauto

theorem mem_col (D : D7) (i : D.nd.Loc) (hl : D.nd.l i ≠ 0) (ep : Bool) (v) :
    v ∈ (decl D i hl ep).col ↔ v ∈ placesOver D.host.E (D.nd.l i) ∧
      v ∈ GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.columns (N := D.nd) D.nbr i ep := by
  simp [decl]

theorem mem_row (D : D7) (i : D.nd.Loc) (hl : D.nd.l i ≠ 0) (ep : Bool) (v) :
    v ∈ (decl D i hl ep).row ↔ v ∈ placesOver D.host.E (D.nd.l i) ∧
      v ∉ GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.columns (N := D.nd) D.nbr i ep := by
  simp [decl]

theorem main : ∀ (D : D7) (i : D.nd.Loc) (ep : Bool), GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.SplitRowPrime D.host (D.nd.l i) →
    (∃ dc : TruncatedSeriesCountingIdentities.Decl D i, EmbeddingTypes.hypDecl i dc ep) ∧ EmbeddingTypes.hypL i := by
  intro D i ep hs
  obtain ⟨hPl, hTy⟩ := GlobalTheory.SplitRowAll.splitRow_at D
  have hP := hPl _ hs
  have hT := hTy i hs
  have hl : D.nd.l i ≠ 0 := hs.1.ne_zero
  refine ⟨⟨decl D i hl ep, ?_, ?_⟩, ?_⟩
  · intro v hv
    rw [mem_col, plTypeUe_iff]
    constructor
    · rintro ⟨-, hv', h⟩
      exact h
    · intro h
      exact ⟨hv, hv, h⟩
  · intro v
    rw [mem_row]
    constructor
    · rintro ⟨hv, hnc⟩
      obtain ⟨-, ⟨v', hv', hc⟩, -⟩ := hP v hv
      have hx := (hT.2.2.2 ep).1 v hv v' hc
      have hv'c : v' ∈ GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.columns (N := D.nd) D.nbr i ep := by
        rcases hx with h | h
        · exact absurd h.1 hnc
        · exact h.1
      exact ⟨v', (mem_col D i hl ep v').2 ⟨hv', hv'c⟩, GlobalTheory.Proof.ConjugatePlaces.isConjPl_symm hc⟩
    · rintro ⟨u, hu, hc⟩
      obtain ⟨hu, huc⟩ := (mem_col D i hl ep u).1 hu
      obtain ⟨-, ⟨u', hu', hc'⟩, -⟩ := hP u hu
      have he : v = u' := GlobalTheory.Proof.ConjugatePlaces.isConjPl_unique hc hc'
      subst he
      refine ⟨hu', fun hvc => ?_⟩
      rcases (hT.2.2.2 ep).1 u hu v hc with h | h
      · exact h.2 hvc
      · exact h.2 huc
  · obtain ⟨-, h5, -, -, hg, hcls⟩ := hs
    exact ⟨le_trans (by norm_num) h5, Or.inl hcls, fun _ v hv => (hP v hv).1, hg 0, hg 1⟩

end GlobalTheory.SplitDecl

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSplitPlacesDeclarationSplitRowPrimeStatement
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_splitPlacesDeclaration_splitRowPrime : ∀ (D : D7) (i : D.nd.Loc) (ep : Bool), GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.SplitRowPrime D.host (D.nd.l i) → (∃ dc : TruncatedSeriesCountingIdentities.Decl D i, EmbeddingTypes.hypDecl i dc ep) ∧ EmbeddingTypes.hypL i := by
  first | exact @GlobalTheory.SplitDecl.main | exact GlobalTheory.SplitDecl.main | (intros; apply GlobalTheory.SplitDecl.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsExtensionCentralCharacter
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands

theorem prod_roots_prod_of_monic {ι : Type*} (s : Multiset ι) (p : ι → ℂ[X]) (hp : ∀ i, (p i).Monic) :
    (s.map p).prod.roots.prod = (s.map fun i => (p i).roots.prod).prod := by
  have h0 : (0 : ℂ[X]) ∉ s.map p := by
    rw [Multiset.mem_map]
    rintro ⟨i, -, hi⟩
    exact (hp i).ne_zero hi
  rw [Polynomial.roots_multiset_prod _ h0, Multiset.bind_map, Multiset.prod_bind]

end GlobalTheory.LocLanglands
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteIndexConj
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.CongIndex

theorem bounded_cover {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {J : Subgroup (GAf L n)}
    (hJ : IsBounded J) {M : ℕ} (hM : 0 < M) :
    ∃ F : Finset (GAf L n), ∀ κ ∈ J, ∃ f ∈ F, NG.Cong L n M (f⁻¹ * κ) := by
  classical
  obtain ⟨F0, hF0⟩ := hJ
  obtain ⟨F1, hF1⟩ := GlobalTheory.AlgFormsFin.exists_cover L n hM
  refine ⟨(F0 ×ˢ F1).image (fun p => p.1 * p.2), fun κ hκ => ?_⟩
  obtain ⟨f0, hf0, hu⟩ := hF0 κ hκ
  obtain ⟨j, hj, κ', hκ', e⟩ := hF1 _ hu
  refine ⟨f0 * j, Finset.mem_image.2 ⟨(f0, j), Finset.mem_product.2 ⟨hf0, hj⟩, rfl⟩, ?_⟩
  have h1 : (f0 * j)⁻¹ * κ = κ' := by
    rw [mul_inv_rev, mul_assoc, e, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [h1]
  exact hκ'

theorem finite_index_conj : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (J : Subgroup (GAf L n)),
    IsBounded J → ∀ (h : GAf L n) (N : ℕ), 0 < N →
      (∃ N' : ℕ, 0 < N' ∧ ∀ κ, NG.Cong L n N' κ → NG.Cong L n N (h⁻¹ * κ * h)) ∧
      (∃ F : Finset (GAf L n), ∀ κ ∈ J, ∃ f ∈ F, NG.Cong L n N (f⁻¹ * κ)) ∧
      IsBounded (J.map (MulAut.conj h).toMonoidHom) := by
  intro L _ _ _ n J hJ h N hN
  refine ⟨GlobalTheory.CongConjugate.congConj L n h N hN, bounded_cover hJ hN, ?_⟩
  classical
  obtain ⟨N', hN', hc⟩ := GlobalTheory.CongConjugate.congConj L n h⁻¹ 1 one_pos
  obtain ⟨F, hF⟩ := bounded_cover hJ hN'
  refine ⟨F.image (fun f => h * f * h⁻¹), fun x hx => ?_⟩
  obtain ⟨κ, hκ, rfl⟩ := Subgroup.mem_map.1 hx
  obtain ⟨f, hf, hcf⟩ := hF κ hκ
  refine ⟨h * f * h⁻¹, Finset.mem_image_of_mem _ hf, ?_⟩
  have hu := (hc _ hcf).1
  have e : (h * f * h⁻¹)⁻¹ * (MulAut.conj h).toMonoidHom κ = h⁻¹⁻¹ * (f⁻¹ * κ) * h⁻¹ := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left]
  rw [e]
  exact hu

end GlobalTheory.CongIndex

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelFunctionFiniteRange
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace GlobalTheory.HalfLatFin

theorem isHalf_of_nsmul {D : D7} {m n : ℕ} (e : AE D) {N : ℕ} (hN : 0 < N) {t t' w : Mx D m n}
    (ht : IsHalf e t) (ht' : IsHalf e t') (hw : t = t' + N • w) : IsHalf e w := by
  intro i j
  have h0 : t i j = t' i j + N • w i j := by
    have := congrFun (congrFun hw i) j
    simpa using this
  have hw' : N • w i j = t i j - t' i j := by rw [h0]; abel
  have h1 : (N : D.host.F) • (e * w i j - w i j) = 0 := by
    rw [Nat.cast_smul_eq_nsmul, smul_sub, ← mul_smul_comm, hw', mul_sub, ht i j, ht' i j, sub_self]
  exact sub_eq_zero.1 ((smul_eq_zero.1 h1).resolve_left (by exact_mod_cast hN.ne'))

end GlobalTheory.HalfLatFin

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHalfOfAuxiliarySplitLevel
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.MainNotions.StandardLattice Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.CoverRead

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HalfCharacter

theorem exists_half_of_auxiliary_split_level : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ pd : ℕ, GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.IsAuxiliarySplitSquarefreeLevel D T.Q.l.M pd →
  ∃ I : Ideal (𝓞 D.host.E), I = Ideal.span {x | x ∈ I ∧ x ∈ Algebra.adjoin ℤ {T.Q.H.w0}} ∧
    I * I.map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) = Ideal.span {(pd : 𝓞 D.host.E)} ∧
    I ⊔ I.map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) = ⊤ := by
  intro D T hJ pd haux
  obtain ⟨hodd, -, hjac, -, -⟩ := haux
  have hH : T.Q.PinHost := hJ.toLawsM.pins.1
  have hw : T.Q.H.w0 = w0E D := by
    have h1 := T.Q.H.two_weight_eq_one_add_root
    have h3 : T.Q.H.rt = rtE D := RingOfIntegers.ext hH.2.1
    rw [h3, ← two_w0E D] at h1
    exact mul_left_cancel₀ two_ne_zero h1
  have hb : (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) = bH D :=
    RingHom.ext fun a => RingOfIntegers.ext (T.Q.H.bar_eq a)
  have hsp : ∀ p ∈ pd.primeFactorsList, SplitOK D p := by
    intro p hp
    have hpr := Nat.prime_of_mem_primeFactorsList hp
    have hdvd := Nat.dvd_of_mem_primeFactorsList hp
    refine ⟨hpr, ?_, hjac p hpr hdvd⟩
    rintro rfl
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hdvd)
  have hpd0 : pd ≠ 0 := hodd.pos.ne'
  refine ⟨MbOf D pd.primeFactorsList, ?_, ?_, ?_⟩
  · rw [hw]; exact MbOf_fromK D _
  · rw [hb]
    have h := MbProd_of D pd.primeFactorsList hsp
    unfold MbProdLaw at h
    rw [h, Nat.prod_primeFactorsList hpd0]
  · rw [hb]; exact MbCop_of D _ hsp

end GlobalTheory.HalfCharacter
end
end
