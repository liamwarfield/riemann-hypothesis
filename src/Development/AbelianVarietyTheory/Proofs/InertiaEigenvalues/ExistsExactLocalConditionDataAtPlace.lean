module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetPointGood

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtendUnramEmb
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module Classical

theorem GlobalTheory.UseLoc.extendUnramEmb : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l), K.1 ≤ MaximalUnramifiedExtension l → ∀ e : ↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1, ∃ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, τ.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1) = e ∧ ∀ τ' : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, τ'.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1) = e → τ' = τ := by
  intro l _ K LL hK e
  have hsurj : Function.Surjective (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1) := by
    intro y
    refine ⟨⟨y.1, ⟨y.2, hK y.2⟩⟩, ?_⟩
    apply Subtype.ext
    rfl
  let φ : ↥(K0 K) ≃ₐ[ℚ_[l]] ↥K.1 :=
    AlgEquiv.ofBijective (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1)
      ⟨(IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1).toRingHom.injective, hsurj⟩
  refine ⟨e.comp φ.symm.toAlgHom, ?_, ?_⟩
  · ext x
    have : φ.symm (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1 x) = x := φ.symm_apply_apply x
    simp only [AlgHom.comp_apply]
    exact congrArg (fun z => ((e z : ↥LL.1) : Om l)) this
  · intro τ' hτ'
    ext y
    obtain ⟨x, rfl⟩ := hsurj y
    have h1 := congrArg (fun f : ↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1 => f x) hτ'
    simp only [AlgHom.comp_apply] at h1
    rw [h1]
    simp only [AlgHom.comp_apply]
    have : φ.symm (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1 x) = x := φ.symm_apply_apply x
    exact (congrArg (fun z => ((e z : ↥LL.1) : Om l)) this).symm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReflSBlockJIff
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module Classical

namespace GlobalTheory.UseLoc.JumpBlock

theorem reflS_blockJ_iff (D : D7) (q : ℚ) :
    AdmissibleParameterJ.refl D q ∈ AdmissibleParameterJ.blockJ D ↔ ∃ c : ℕ, c < D.R.t ∧ q = c := by
  simp only [AdmissibleParameterJ.refl, AdmissibleParameterJ.blockJ, Set.mem_setOf_eq]
  constructor
  · rintro ⟨c, hc, hq⟩
    refine ⟨D.R.t - 1 - c, by omega, ?_⟩
    have h1 : 1 ≤ D.R.t := by omega
    rw [Nat.cast_sub (by omega), Nat.cast_sub h1]
    push_cast
    linarith
  · rintro ⟨c, hc, hq⟩
    refine ⟨D.R.t - 1 - c, by omega, ?_⟩
    have h1 : 1 ≤ D.R.t := by omega
    rw [Nat.cast_sub (by omega), Nat.cast_sub h1]
    push_cast
    linarith

theorem jumps_iff : ∀ (D : D7) (up : Bool) (j : ℕ) (ρ : D.what₂.Tau) (q : ℚ),
    q ∈ AdmissibleParameterJ.JJ D up j ρ ↔ q ∈ AdmissibleParameterJ.JW D up j ρ ∨ ∃ c : ℕ, c < D.R.t ∧ q = c := by
  intro D up j ρ q
  cases up
  · simp only [AdmissibleParameterJ.JJ, AdmissibleParameterJ.JW, AdmissibleParameterJ.Jm, AdmissibleParameterJ.Jp, AdmissibleParameterJ.cloudT, AdmissibleParameterJ.lowT, AdmissibleParameterJ.reflS,
      Set.mem_union, Set.mem_setOf_eq, Bool.false_eq_true, if_false]
    rw [reflS_blockJ_iff]
  · simp only [AdmissibleParameterJ.JJ, AdmissibleParameterJ.JW, AdmissibleParameterJ.Jp, AdmissibleParameterJ.cloudT, AdmissibleParameterJ.lowT, AdmissibleParameterJ.blockJ,
      Set.mem_union, Set.mem_setOf_eq, if_true]

end GlobalTheory.UseLoc.JumpBlock
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniformiser
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module Classical

namespace GlobalTheory.UseLocUnif

theorem exists_uniformiser : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l), ∃ lam : ↥(OL LL), Irreducible lam := by
  intro l _ LL
  obtain ⟨hdvr, -⟩ := GlobalTheory.FinExtIntegers.dvr_complete LL
  exact IsDiscreteValuationRing.exists_irreducible ↥(OL LL)

end GlobalTheory.UseLocUnif
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteDimensionalKsOne
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module Classical

namespace GlobalTheory.UseLoc

theorem finiteDimensional_Ks_one {l : ℕ} [Fact l.Prime] (K : FinExt l) (hK : K.1 ≤ MaximalUnramifiedExtension l) :
    FiniteDimensional ℚ_[l] ↥(Ks K 1) := by
  have h0 : K0 K = K.1 := inf_eq_left.mpr hK
  have hK1 : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  have hl : 0 < l := (Fact.out : l.Prime).pos
  have hfin : ({x : Om l | x ^ (l ^ 1) = 1}).Finite := by
    apply ((Polynomial.nthRoots (l ^ 1) (1 : Om l)).toFinset.finite_toSet).subset
    intro x hx
    simp only [Set.mem_setOf_eq] at hx
    rw [Finset.mem_coe, Multiset.mem_toFinset]
    exact (Polynomial.mem_nthRoots (pow_pos hl 1)).2 hx
  haveI : Finite ({x : Om l | x ^ (l ^ 1) = 1}) := hfin.to_subtype
  have hA : FiniteDimensional ℚ_[l]
      ↥(IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ 1) = 1}) := by
    apply IntermediateField.finiteDimensional_adjoin
    intro x hx
    refine ⟨Polynomial.X ^ (l ^ 1) - 1, Polynomial.monic_X_pow_sub_C 1 (pow_pos hl 1).ne', ?_⟩
    simp only [Set.mem_setOf_eq] at hx
    simp only [pow_one] at hx
    simp [hx]
  unfold Ks
  rw [h0]
  infer_instance

theorem exists_caseA_enl : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)), D.nd.l i ∉ D.host.small → D.nd.l i ≠ D.host.q →
    D.nd.l i ≠ D.host.d → ∃ C : TruncatedSeriesCountingIdentities.CoefExt D i w hw, CaseA (D.nbr i w hw).Kw C.LL := by
  intro D i w hw hs hq hd
  have h2 : D.nd.l i ≠ 2 := UpperTheory.Small.ne_two D.host hs
  have hur : (D.nbr i w hw).Kw.1 ≤ MaximalUnramifiedExtension (D.nd.l i) := GlobalTheory.HubLoc.kw_le_Kur_all D i hs hq hd w hw
  haveI := finiteDimensional_Ks_one (D.nbr i w hw).Kw hur
  haveI : FiniteDimensional ℚ_[D.nd.l i] ↥(D.nbr i w hw).LL.1 := (D.nbr i w hw).LL.2
  let N : IntermediateField ℚ_[D.nd.l i] (Om (D.nd.l i)) :=
    IntermediateField.normalClosure ℚ_[D.nd.l i] ↥(Ks (D.nbr i w hw).Kw 1) (Om (D.nd.l i))
  haveI hN : FiniteDimensional ℚ_[D.nd.l i] ↥N := normalClosure.is_finiteDimensional _ _ _
  let LL : FinExt (D.nd.l i) := ⟨N ⊔ (D.nbr i w hw).LL.1, inferInstance⟩
  refine ⟨⟨LL, le_sup_right⟩, hur, h2, le_rfl, fun h => absurd h h2, ?_, ?_⟩
  · have h0 : K0 (D.nbr i w hw).Kw = (D.nbr i w hw).Kw.1 := inf_eq_left.mpr hur
    unfold Ks
    rw [h0]
    exact le_sup_left
  · intro τ x
    apply le_sup_left (b := (D.nbr i w hw).LL.1)
    exact AlgHom.fieldRange_le_normalClosure τ ⟨x, rfl⟩

end GlobalTheory.UseLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsTwistRepTwist
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module Classical

noncomputable section

namespace GlobalTheory.UseLoc.TwistCrysW

theorem isTwistRep_twist (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (k : ℕ)
    (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) :
    IsTwistRep (tableLineDegreeTwo.charL (LL := ↥C.LL.1) θ) (matRep (TruncatedSeriesCountingIdentities.locC C M)) (repV C (twistM (locOC C M) θ)) := by
  refine ⟨LinearEquiv.refl _ _, fun g v => ?_⟩
  have hent : ∀ a b, (mapM (algebraMap ↥(OL C.LL) ↥C.LL.1) (twistM (locOC C M) θ) g) a b =
      algebraMap ↥(OL C.LL) ↥C.LL.1 ((θ g : (↥(OL C.LL))ˣ) : ↥(OL C.LL)) * (TruncatedSeriesCountingIdentities.locC C M g) a b := by
    intro a b
    change algebraMap ↥(OL C.LL) ↥C.LL.1 (((θ g : (↥(OL C.LL))ˣ) : ↥(OL C.LL)) * (locOC C M g) a b) = _
    rw [map_mul]
    rfl
  change (mapM (algebraMap ↥(OL C.LL) ↥C.LL.1) (twistM (locOC C M) θ) g).mulVec v =
    algebraMap ↥(OL C.LL) ↥C.LL.1 ((θ g : (↥(OL C.LL))ˣ) : ↥(OL C.LL)) • (TruncatedSeriesCountingIdentities.locC C M g).mulVec v
  funext a
  simp only [Matrix.mulVec, dotProduct, hent, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem isCrys_and_multV : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (k : ℕ) (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ), IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C M)) → IsCrys (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (tableLineDegreeTwo.charL (LL := ↥C.LL.1) θ)) → IsCrys (Br.PD D.loc D.nbr i w hw) (repV C (twistM (locOC C M) θ)) ∧ ∀ (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1) (b : ℤ), multV (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (tableLineDegreeTwo.charL (LL := ↥C.LL.1) θ)) τ b ≠ 0 → ∀ a : ℤ, multV (Br.PD D.loc D.nbr i w hw) (repV C (twistM (locOC C M) θ)) τ (a + b) = multV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C M)) τ a := by
  intro D i w hw C k M θ hM hθ
  have key := GlobalTheory.TwistRepCrys.isCrys_and_multV_twist (D.nd.l i) (D.loc _) (D.locA _) (D.locT _) (D.nbr i w hw).Kw C.LL
    (Fin k → ↥C.LL.1) (matRep (TruncatedSeriesCountingIdentities.locC C M)) (Fin k → ↥C.LL.1) (repV C (twistM (locOC C M) θ))
    (tableLineDegreeTwo.charL (LL := ↥C.LL.1) θ) (isTwistRep_twist D i w hw C k M θ) hθ hM
  refine ⟨key.1, fun τ b hb a => key.2 τ a b ?_⟩
  exact (GlobalTheory.Per.JumpMult.jump_iff_mult_ne_zero (D.nd.l i) (D.loc _) (D.locA _) (D.locT _) (D.nbr i w hw).Kw C.LL
    ↥C.LL.1 (Formalism.WeaklyAdmissibleFiltrations.charRep (tableLineDegreeTwo.charL (LL := ↥C.LL.1) θ)) τ b).2.2.2 hb

end GlobalTheory.UseLoc.TwistCrysW
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IncLocChiEpsUZpow
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module Classical

noncomputable section
namespace GlobalTheory.UseLoc

variable {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}

theorem chiRat_eq_epsU_zpow (c : ℕ) (h1 : 1 ≤ c) (h2 : c ≤ D.R.t) : chiU D.nd i c * (chiU D.nd i 1)⁻¹ = epsU D.nd i ^ (-((c : ℤ) - 1)) := by
    show D.nd.chi i c * (D.nd.chi i 1)⁻¹ = _
    rw [D.nd.chi_def i c h1 h2, mul_inv_cancel_comm]
    rfl

theorem charL_chiOC_apply (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (χ : GE D.nd →* (D.nd.O i)ˣ) (g) : tableLineDegreeTwo.charL (LL := ↥C.LL.1) (chiOC C χ) g =
      Units.map C.inc.toMonoidHom (Br.locChi D.nbr i w hw χ g) := by
    apply Units.ext
    rfl

theorem inc_cycLL_apply (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (g) : Units.map C.inc.toMonoidHom (cycLL (Br.PD D.loc D.nbr i w hw) (Br.LL D.nbr i w hw) g) =
      cycLL (Br.PD D.loc D.nbr i w hw) ↥C.LL.1 g := by
    apply Units.ext
    exact (IntermediateField.inclusion C.le).commutes _

theorem locChi_zpow_apply (χ : GE D.nd →* (D.nd.O i)ˣ) (k : ℤ) (g) : Br.locChi D.nbr i w hw (χ ^ k) g = Br.locChi D.nbr i w hw χ g ^ k := by
    show Units.map _ ((χ ^ k) _) = (Units.map _ (χ _)) ^ k
    rw [MonoidHom.zpow_apply, map_zpow]

theorem charL_mul_apply (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (a b : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (g) : tableLineDegreeTwo.charL (LL := ↥C.LL.1) (a * b) g =
      tableLineDegreeTwo.charL (LL := ↥C.LL.1) a g * tableLineDegreeTwo.charL (LL := ↥C.LL.1) b g := by
    show Units.map _ ((a * b) g) = _
    rw [MonoidHom.mul_apply, map_mul]
    rfl

theorem locChi_one_apply (g : Br.G D.nbr i w hw) : Br.locChi D.nbr i w hw (1 : GE D.nd →* (D.nd.O i)ˣ) g = 1 := by
    simp [Br.locChi, Br.chiG]

theorem inc_locChi_epsU_zpow (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (g : Br.G D.nbr i w hw) (k : ℤ) :
    Units.map C.inc.toMonoidHom (Br.locChi D.nbr i w hw (epsU D.nd i) g ^ k) =
      cycLL (Br.PD D.loc D.nbr i w hw) ↥C.LL.1 g ^ k := by
  rw [map_zpow, ← inc_cycLL_apply C g, GlobalTheory.CycBridge.locChi_epsU D i w hw g]

theorem chiT_cyc : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (c : ℕ), 1 ≤ c → c ≤ D.R.t → ∀ g, tableLineDegreeTwo.charL (LL := ↥C.LL.1) (chiT C θ c) g = tableLineDegreeTwo.charL (LL := ↥C.LL.1) (chiT C θ 1) g * cycLL (Br.PD D.loc D.nbr i w hw) ↥C.LL.1 g ^ (-((c : ℤ) - 1)) := by
  intro D i w hw C θ c h1 h2 g
  have e1 : tableLineDegreeTwo.charL (LL := ↥C.LL.1) (chiOC C (chiU D.nd i c * (chiU D.nd i 1)⁻¹)) g =
      cycLL (Br.PD D.loc D.nbr i w hw) ↥C.LL.1 g ^ (-((c : ℤ) - 1)) := by
    rw [charL_chiOC_apply, chiRat_eq_epsU_zpow c h1 h2, locChi_zpow_apply, inc_locChi_epsU_zpow]
  have e0 : tableLineDegreeTwo.charL (LL := ↥C.LL.1) (chiOC C (chiU D.nd i 1 * (chiU D.nd i 1)⁻¹)) g = 1 := by
    rw [charL_chiOC_apply, mul_inv_cancel, locChi_one_apply]
    exact map_one _
  unfold chiT
  rw [charL_mul_apply, charL_mul_apply, e1, e0, one_mul]
  exact mul_comm _ _

end GlobalTheory.UseLoc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistMRepVCont
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module Classical

namespace GlobalTheory.UseLoc
theorem twistM_repV_cont : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (k : ℕ) (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ), (Continuous fun g => M g) → Continuous (fun g => ((tableLineDegreeTwo.charL (LL := ↥C.LL.1) θ g : (↥C.LL.1)ˣ) : ↥C.LL.1)) → ∀ x, Continuous fun g => repV C (twistM (locOC C M) θ) g x := by
  intro D i w hw C k M θ hM hθ x
  have hinc : Continuous fun y : ↥(OL (D.nbr i w hw).LL) => ((incO C.le y : ↥(OL C.LL)) : ↥C.LL.1) := by
    have e : (fun y : ↥(OL (D.nbr i w hw).LL) => ((incO C.le y : ↥(OL C.LL)) : ↥C.LL.1)) =
        fun y => IntermediateField.inclusion C.le y.1 := rfl
    rw [e]
    exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  have hmat : Continuous fun g => mapM (algebraMap ↥(OL C.LL) ↥C.LL.1) (twistM (locOC C M) θ) g := by
    refine continuous_matrix fun a b => ?_
    have h1 : Continuous fun g : Br.G D.nbr i w hw =>
        M ((decS D.nd w) ((Br.ι (D.nbr i w hw)) g)) a b :=
      (hM.matrix_elem a b).comp (continuous_subtype_val.comp (Br.ι_cont (D.nbr i w hw)))
    have h2 := hinc.comp ((D.nbr i w hw).eO_cont.comp h1)
    have e : (fun g => mapM (algebraMap ↥(OL C.LL) ↥C.LL.1) (twistM (locOC C M) θ) g a b) =
        fun g => ((tableLineDegreeTwo.charL (LL := ↥C.LL.1) θ g : (↥C.LL.1)ˣ) : ↥C.LL.1) *
          ((incO C.le ((D.nbr i w hw).eO (M ((decS D.nd w) ((Br.ι (D.nbr i w hw)) g)) a b)) : ↥(OL C.LL)) : ↥C.LL.1) := by
      funext g
      simp [mapM, twistM, locOC, Br.locO, tableLineDegreeTwo.charL, Matrix.smul_apply]
    rw [e]
    exact hθ.mul h2
  have e2 : (fun g => repV C (twistM (locOC C M) θ) g x) =
      fun g => (mapM (algebraMap ↥(OL C.LL) ↥C.LL.1) (twistM (locOC C M) θ) g).mulVec x := by
    funext g
    rfl
  rw [e2]
  exact hmat.matrix_mulVec continuous_const
end GlobalTheory.UseLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrysWpRTw
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module Classical

namespace GlobalTheory.UseLoc

theorem locC_rTwO {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
    {hw : w ∈ placesOver D.host.E (D.nd.l i)} (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (x : D.nd.X i) :
    TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x) = twistM (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x)) (TruncatedSeriesCountingIdentities.chi1C C)⁻¹ := by
  let ψ : D.nd.O i →+* ↥C.LL.1 := C.inc.comp (D.nbr i w hw).toLL
  let j : Br.G D.nbr i w hw →* GE D.nd := (decS D.nd w).comp (Br.iota D.nbr i w hw)
  refine MonoidHom.ext fun g => ?_
  refine Matrix.ext fun a b => ?_
  exact map_mul ψ (((chiU D.nd i 1)⁻¹ (j g) : (D.nd.O i)ˣ) : D.nd.O i) (rO D.nd i r x (j g) a b)

theorem crys_Wp_rTw : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw), GoodR D.nd i r → π ∈ D.nd.Z i → TruncatedSeriesCountingIdentities.admG2 i r ρ π → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π → IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (WpO D.nd i ρ π))) ∧ ∀ x, IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x))) := by
  intro D i r ρ π w hw C _ _ hG hd
  have h2 : ∀ x, IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x))) := by
    intro x
    rw [locC_rTwO]
    exact (hG w hw C).2 x
  refine ⟨?_, h2⟩
  obtain ⟨e, he⟩ := hd
  have hd' : ∃ e, GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsDecomp (t := D.R.t) (r π) (ρ π) (D.nd.chi i) e := by
    refine ⟨e, fun g u => ?_⟩
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.overK, GlobalTheory.SummandJumps.matRep_apply]
    exact he g u
  exact ((GlobalTheory.SummandJumps.main D i w hw (D.locT _) C.LL C.le r ρ π hd').1 (h2 π)).1

end GlobalTheory.UseLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JTilShiftBlock
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module Classical

namespace GlobalTheory

theorem jTil_shift_block : ∀ (l n t : ℕ) (h w η : ZMod n → ℕ) (typ : ZMod n → Bool) (U : ZMod n → Multiset ℤ), tableLineDegreeTwo.PositionHyps l n t h w η typ U → ∀ (a : ZMod n) (S : Set ℚ), (∀ b : ℤ, ((U a).count (b + w a) = 1 ↔ (b : ℚ) ∈ S) ∧ (U a).count (b + w a) ≤ 1) → ∀ b : ℤ, (if ((b : ℚ) ∈ S ∨ ∃ c : ℕ, c < t ∧ (b : ℚ) = c) then (1 : ℤ) else 0) = tableLineDegreeTwo.jTil U w t a (b + w a) := by
  intro l n t h w η typ U hS a S hU b
  have hsg : 0 ≤ tableLineDegreeTwo.sg n l h a := by
    unfold tableLineDegreeTwo.sg Formalism.WachCohomologyFacts.V2.sgN
    exact Int.floor_nonneg.mpr (tsum_nonneg fun j => by positivity)
  obtain ⟨_, _, _, hG, hB, _, hT2, _⟩ := hS a
  have hblk : (∃ c : ℕ, c < t ∧ (b : ℚ) = c) ↔ (0 ≤ b ∧ b ≤ (t : ℤ) - 1) := by
    constructor
    · rintro ⟨c, hc, hbc⟩
      have : b = (c : ℤ) := by exact_mod_cast hbc
      omega
    · rintro ⟨h0, h1⟩
      refine ⟨b.toNat, by omega, ?_⟩
      rw [← Int.cast_natCast, Int.toNat_of_nonneg h0]
  have hwin : ((w a : ℤ) ≤ b + w a ∧ b + w a ≤ (w a : ℤ) + t - 1) ↔ (0 ≤ b ∧ b ≤ (t : ℤ) - 1) := by
    constructor <;> rintro ⟨h0, h1⟩ <;> constructor <;> omega
  have hc1 := (hU b).2
  have hcS : (b : ℚ) ∈ S → (U a).count (b + w a) = 1 := (hU b).1.2
  have hcN : (b : ℚ) ∉ S → (U a).count (b + w a) = 0 := fun hn => by
    have := mt (hU b).1.1 hn
    omega
  have hboth : (b : ℚ) ∈ S → ¬ (0 ≤ b ∧ b ≤ (t : ℤ) - 1) := by
    rintro hbS ⟨h0, h1⟩
    have hmem : b + (w a : ℤ) ∈ U a := Multiset.count_pos.mp (by rw [hcS hbS]; omega)
    have hlow : b + (w a : ℤ) ∈ tableLineDegreeTwo.lows (typ a) (h a) (η a) (U a) := by
      unfold tableLineDegreeTwo.lows
      rw [Multiset.mem_filter]
      refine ⟨hmem, ?_⟩
      unfold Formalism.WachCohomologyFacts.V2.InWinN
      cases hty : typ a
      · have := hB hty
        simp only [Bool.false_eq_true, if_false]
        constructor <;> omega
      · have := hG hty
        simp only [if_true]
        constructor <;> omega
    have hy : b + (w a : ℤ) ∈ Formalism.WachCohomologyFacts.Top.GlobalTheory (w a) t := by
      unfold Formalism.WachCohomologyFacts.Top.GlobalTheory
      rw [Finset.mem_Icc]
      constructor <;> omega
    have := hT2 _ hlow _ hy
    rw [sub_self, abs_zero] at this
    linarith
  unfold tableLineDegreeTwo.jTil
  by_cases hbS : (b : ℚ) ∈ S
  · have hn := hboth hbS
    rw [if_pos (Or.inl hbS), if_neg (by rwa [hwin]), hcS hbS]
    simp
  · rw [hcN hbS]
    by_cases hbl : 0 ≤ b ∧ b ≤ (t : ℤ) - 1
    · rw [if_pos (Or.inr (hblk.2 hbl)), if_pos (hwin.2 hbl)]
      simp
    · rw [if_neg (by rintro (h1 | h1); exact hbS h1; exact hbl (hblk.1 h1)), if_neg (by rwa [hwin])]
      simp

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ScaleRootsProdIcc
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module Classical

noncomputable section
namespace GlobalTheory.UseLoc.InstPoly
open Polynomial

section Alg

theorem charpoly_smul_unit {R : Type} [CommRing R] [IsDomain R] [Infinite R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) {c : R} (hc : IsUnit c) :
    (c • M).charpoly = M.charpoly.scaleRoots c := by
  apply Polynomial.funext
  intro x
  obtain ⟨u, rfl⟩ := hc
  obtain ⟨y, rfl⟩ : ∃ y, x = (u : R) * y := ⟨((u⁻¹ : Rˣ) : R) * x, by rw [← mul_assoc, Units.mul_inv, one_mul]⟩
  rw [scaleRoots_eval_mul, Matrix.charpoly_natDegree_eq_dim, Matrix.eval_charpoly, Matrix.eval_charpoly,
    ← Matrix.det_smul, smul_sub]
  congr 2
  ext a b
  simp only [Matrix.smul_apply, Matrix.scalar_apply, Matrix.diagonal_apply, smul_eq_mul]
  split_ifs <;> simp

theorem scaleRoots_prod_Icc {R : Type} [CommRing R] [IsDomain R] (a : ℕ → R) (s : R) (S : Finset ℕ) :
    (∏ c ∈ S, (X - C (a c))).scaleRoots s = ∏ c ∈ S, (X - C (s * a c)) := by
  refine Finset.induction_on S ?_ ?_
  · simp
  · intro c S hc ih
    rw [Finset.prod_insert hc, Finset.prod_insert hc, mul_scaleRoots_of_noZeroDivisors, ih, X_sub_C_scaleRoots,
      mul_comm (a c) s]

theorem natDegree_blk {R : Type} [CommRing R] [Nontrivial R] {r : ℕ} (B : Matrix (Fin r) (Fin r) R)
    (a : ℕ → R) (t : ℕ) : (B.charpoly * ∏ c ∈ Finset.Icc 1 t, (X - C (a c))).natDegree = r + t := by
  rw [(Matrix.charpoly_monic B).natDegree_mul (monic_prod_of_monic _ _ fun c _ => monic_X_sub_C (a c)),
    Matrix.charpoly_natDegree_eq_dim, natDegree_prod_of_monic _ _ fun c _ => monic_X_sub_C (a c)]
  simp [natDegree_X_sub_C]

theorem scale_mem {R : Type} [CommRing R] (J : Ideal R) (p q : R[X]) (hdeg : p.natDegree = q.natDegree) (s : R)
    (h : ∀ k, (p - q).coeff k ∈ J) (k : ℕ) : (p.scaleRoots s - q.scaleRoots s).coeff k ∈ J := by
  rw [coeff_sub, coeff_scaleRoots, coeff_scaleRoots, hdeg, ← sub_mul]
  exact J.mul_mem_right _ (by simpa [coeff_sub] using h k)

theorem congr_mod {O S : Type} [CommRing O] [IsLocalRing O] [CommRing S] (f : O →+* S)
    (hf : ∀ a ∈ IsLocalRing.maximalIdeal O, f a = 0) {n r : ℕ} (A : Matrix (Fin n) (Fin n) O)
    (B : Matrix (Fin r) (Fin r) O) (χ : ℕ → O) (t : ℕ)
    (h : (A.map (IsLocalRing.residue O)).charpoly = (B.map (IsLocalRing.residue O)).charpoly *
      ∏ c ∈ Finset.Icc 1 t, (X - C (IsLocalRing.residue O (χ c)))) :
    A.charpoly.map f = (B.charpoly * ∏ c ∈ Finset.Icc 1 t, (X - C (χ c))).map f := by
  let ψ : IsLocalRing.ResidueField O →+* S := Ideal.Quotient.lift (IsLocalRing.maximalIdeal O) f hf
  have hfψ : ∀ p : O[X], p.map f = (p.map (IsLocalRing.residue O)).map ψ := fun p => by
    rw [Polynomial.map_map]
    exact congrArg (fun g : O →+* S => p.map g) (RingHom.ext fun a => rfl)
  rw [hfψ, hfψ, ← Matrix.charpoly_map, h]
  simp only [Polynomial.map_mul, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    Matrix.charpoly_map]

theorem mod_ideal {O R : Type} [CommRing O] [IsLocalRing O] [CommRing R] (φ : O →+* R) (J : Ideal R)
    (hφ : ∀ a ∈ IsLocalRing.maximalIdeal O, φ a ∈ J) {n r : ℕ} (A : Matrix (Fin n) (Fin n) O)
    (B : Matrix (Fin r) (Fin r) O) (χ : ℕ → O) (t : ℕ)
    (h : (A.map (IsLocalRing.residue O)).charpoly = (B.map (IsLocalRing.residue O)).charpoly *
      ∏ c ∈ Finset.Icc 1 t, (X - C (IsLocalRing.residue O (χ c)))) (k : ℕ) :
    ((A.map φ).charpoly - (B.map φ).charpoly * ∏ c ∈ Finset.Icc 1 t, (X - C (φ (χ c)))).coeff k ∈ J := by
  have H := congr_mod ((Ideal.Quotient.mk J).comp φ)
    (fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 (hφ a ha)) A B χ t h
  have e : (B.map φ).charpoly * ∏ c ∈ Finset.Icc 1 t, (X - C (φ (χ c))) =
      (B.charpoly * ∏ c ∈ Finset.Icc 1 t, (X - C (χ c))).map φ := by
    simp only [Polynomial.map_mul, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
      Matrix.charpoly_map]
  have H2 : (A.map φ).charpoly.map (Ideal.Quotient.mk J) =
      ((B.map φ).charpoly * ∏ c ∈ Finset.Icc 1 t, (X - C (φ (χ c)))).map (Ideal.Quotient.mk J) := by
    rw [e, Matrix.charpoly_map, Polynomial.map_map, Polynomial.map_map, H]
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← Polynomial.coeff_map, Polynomial.map_sub, H2, sub_self, coeff_zero]

end Alg

section Val
variable {l : ℕ} [Fact l.Prime]

theorem isUnit_of_incO {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) (x : ↥(OL LL)) (hx : IsUnit (incO h x)) :
    IsUnit x := by
  by_cases hx0 : x = 0
  · subst hx0
    rw [map_zero] at hx
    exact absurd hx not_isUnit_zero
  have hx0' : (x : ↥LL.1) ≠ 0 := fun e => hx0 (Subtype.ext e)
  obtain ⟨u, hu⟩ := hx
  have hinv : IsIntegral ℤ_[l] ((x : ↥LL.1)⁻¹) := by
    have hy : IsIntegral ℤ_[l] (((u⁻¹ : (↥(OL LL'))ˣ) : ↥(OL LL')) : ↥LL'.1) := (((u⁻¹ : (↥(OL LL'))ˣ) : ↥(OL LL'))).2
    have he : IntermediateField.inclusion h ((x : ↥LL.1)⁻¹) = (((u⁻¹ : (↥(OL LL'))ˣ) : ↥(OL LL')) : ↥LL'.1) := by
      rw [map_inv₀]
      have h1 : ((incO h x : ↥(OL LL')) : ↥LL'.1) = IntermediateField.inclusion h (x : ↥LL.1) := rfl
      rw [← h1, ← hu]
      have h2 : ((u : ↥(OL LL')) : ↥LL'.1) * (((u⁻¹ : (↥(OL LL'))ˣ) : ↥(OL LL')) : ↥LL'.1) = 1 := by
        rw [← Subalgebra.coe_mul, Units.mul_inv, Subalgebra.coe_one]
      exact inv_eq_of_mul_eq_one_right h2
    rw [← he] at hy
    exact (isIntegral_algHom_iff ((IntermediateField.inclusion h).restrictScalars ℤ_[l])
      (IntermediateField.inclusion h).injective).1 hy
  refine isUnit_iff_exists_inv.2 ⟨⟨(x : ↥LL.1)⁻¹, hinv⟩, Subtype.ext ?_⟩
  show (x : ↥LL.1) * (x : ↥LL.1)⁻¹ = 1
  exact mul_inv_cancel₀ hx0'

theorem dvd_of_not_isUnit (P : LocPrime l) (LL : FinExt l) {lam y : ↥(OL LL)} (hl : Irreducible lam)
    (hy : ¬ IsUnit y) : lam ∣ y := by
  by_cases hy0 : y = 0
  · rw [hy0]; exact dvd_zero lam
  have hl0 : (lam : ↥LL.1) ≠ 0 := fun e => hl.ne_zero (Subtype.ext e)
  have hy0' : (y : ↥LL.1) ≠ 0 := fun e => hy0 (Subtype.ext e)
  have hu0 : (y : ↥LL.1) / lam ≠ 0 := div_ne_zero hy0' hl0
  have key : 0 ≤ P.v LL ((y : ↥LL.1) / lam) ∨ 0 ≤ P.v LL ((y : ↥LL.1) / lam)⁻¹ := by
    by_contra hc
    push_neg at hc
    obtain ⟨h1, h2⟩ := hc
    have hs : P.v LL ((y : ↥LL.1) / lam) + P.v LL ((y : ↥LL.1) / lam)⁻¹ = 0 := by
      rw [← AddValuation.map_mul, mul_inv_cancel₀ hu0, AddValuation.map_one]
    obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt h1)
    obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt h2)
    rw [← ha] at h1 hs
    rw [← hb] at h2 hs
    have hab : a + b = 0 := by exact_mod_cast hs
    have ha' : a < 0 := by exact_mod_cast h1
    have hb' : b < 0 := by exact_mod_cast h2
    linarith
  rcases key with h | h
  · refine ⟨⟨(y : ↥LL.1) / lam, (P.v_O LL _).1 h⟩, Subtype.ext ?_⟩
    show (y : ↥LL.1) = lam * ((y : ↥LL.1) / lam)
    field_simp
  · have hlam : lam = y * ⟨((y : ↥LL.1) / lam)⁻¹, (P.v_O LL _).1 h⟩ := Subtype.ext (by
      show (lam : ↥LL.1) = y * ((y : ↥LL.1) / lam)⁻¹
      rw [inv_div]; field_simp)
    obtain ⟨z, hz⟩ : ∃ z : ↥(OL LL), lam = y * z := ⟨_, hlam⟩
    rcases hl.isUnit_or_isUnit hz with h' | h'
    · exact absurd h' hy
    · exact ⟨((h'.unit⁻¹ : (↥(OL LL))ˣ) : ↥(OL LL)), by rw [hz, mul_assoc, h'.mul_val_inv, mul_one]⟩

end Val
end GlobalTheory.UseLoc.InstPoly

namespace GlobalTheory.UseLoc.InstPoly
open Polynomial

set_option synthInstance.maxHeartbeats 200000 in
theorem core {R O : Type} [CommRing R] [IsDomain R] [Infinite R] [CommRing O] [IsLocalRing O]
    (φ : O →+* R) (lam : R) (hφ : ∀ a ∈ IsLocalRing.maximalIdeal O, lam ∣ φ a) {n r : ℕ}
    (A : Matrix (Fin n) (Fin n) O) (B : Matrix (Fin r) (Fin r) O) (χ : ℕ → O) (t : ℕ)
    (h : (A.map (IsLocalRing.residue O)).charpoly = (B.map (IsLocalRing.residue O)).charpoly *
      ∏ c ∈ Finset.Icc 1 t, (X - C (IsLocalRing.residue O (χ c))))
    (s : R) (hs : IsUnit s) (k : ℕ) :
    ∃ y, ((s • A.map φ).charpoly - (s • B.map φ).charpoly *
      ∏ c ∈ Finset.Icc 1 t, (X - C (s * φ (χ c)))).coeff k = lam * y := by
  have hn : n = r + t := by
    have h1 := congrArg natDegree h
    have h2 := natDegree_blk (B.map (IsLocalRing.residue O)) (fun c => IsLocalRing.residue O (χ c)) t
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at h1
    exact h1.trans h2
  rw [charpoly_smul_unit _ hs, charpoly_smul_unit _ hs, ← scaleRoots_prod_Icc (fun c => φ (χ c)) s,
    ← mul_scaleRoots_of_noZeroDivisors]
  have hdeg : (A.map φ).charpoly.natDegree =
      ((B.map φ).charpoly * ∏ c ∈ Finset.Icc 1 t, (X - C (φ (χ c)))).natDegree := by
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin, hn]
    exact (natDegree_blk (B.map φ) (fun c => φ (χ c)) t).symm
  have hmem := scale_mem (Ideal.span {lam}) _ _ hdeg s
    (mod_ideal φ (Ideal.span {lam}) (fun a ha => Ideal.mem_span_singleton.2 (hφ a ha)) A B χ t h) k
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hmem
  exact ⟨y, by rw [← hy, mul_comm]⟩

section Main
variable {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}

abbrev phiC (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) : D.nd.O i →+* ↥(OL C.LL) :=
  (incO C.le).comp (D.nbr i w hw).eO.toRingHom

theorem locOC_apply (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (g : Br.G D.nbr i w hw) :
    locOC C M g = (M (decS D.nd w (Br.iota D.nbr i w hw g))).map (phiC C) := rfl

theorem charpoly_repV (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) {k : ℕ} (N : Br.G D.nbr i w hw →* Matrix (Fin k) (Fin k) ↥(OL C.LL))
    (g : Br.G D.nbr i w hw) :
    LinearMap.charpoly (repV C N g) = (N g).charpoly.map (algebraMap ↥(OL C.LL) ↥C.LL.1) := by
  have h : LinearMap.charpoly (repV C N g) = ((N g).map (algebraMap ↥(OL C.LL) ↥C.LL.1)).charpoly :=
    Matrix.charpoly_toLin' _
  rw [h, Matrix.charpoly_map]

set_option synthInstance.maxHeartbeats 200000 in
theorem twist_locOC (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) {k : ℕ}
    (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (χ : GE D.nd →* (D.nd.O i)ˣ) (g : Br.G D.nbr i w hw) :
    twistM (locOC C (twistM M χ)) θ g =
      (((θ g : (↥(OL C.LL))ˣ) : ↥(OL C.LL)) *
        phiC C ((χ (decS D.nd w (Br.iota D.nbr i w hw g)) : (D.nd.O i)ˣ) : D.nd.O i)) •
        (M (decS D.nd w (Br.iota D.nbr i w hw g))).map (phiC C) := by
  ext p q
  simp only [twistM, MonoidHom.coe_mk, OneHom.coe_mk, locOC_apply, Matrix.smul_apply, Matrix.map_apply,
    smul_eq_mul, map_mul]
  ring

theorem chiOC_val (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (χ : GE D.nd →* (D.nd.O i)ˣ) (g : Br.G D.nbr i w hw) :
    ((chiOC C χ g : (↥(OL C.LL))ˣ) : ↥(OL C.LL)) =
      phiC C ((χ (decS D.nd w (Br.iota D.nbr i w hw g)) : (D.nd.O i)ˣ) : D.nd.O i) := rfl

set_option maxHeartbeats 1000000 in
theorem chiT_val (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (c : ℕ)
    (g : Br.G D.nbr i w hw) :
    ((chiT C θ c g : (↥(OL C.LL))ˣ) : ↥(OL C.LL)) =
      (((θ g : (↥(OL C.LL))ˣ) : ↥(OL C.LL)) *
        phiC C ((((chiU D.nd i 1)⁻¹ (decS D.nd w (Br.iota D.nbr i w hw g))) : (D.nd.O i)ˣ) : D.nd.O i)) *
      phiC C ((chiU D.nd i c (decS D.nd w (Br.iota D.nbr i w hw g)) : (D.nd.O i)ˣ) : D.nd.O i) := by
  have e : ((chiT C θ c g : (↥(OL C.LL))ˣ) : ↥(OL C.LL)) =
      ((chiOC C (chiU D.nd i c * (chiU D.nd i 1)⁻¹) g : (↥(OL C.LL))ˣ) : ↥(OL C.LL)) *
        ((θ g : (↥(OL C.LL))ˣ) : ↥(OL C.LL)) := rfl
  have e2 : ((((chiU D.nd i c * (chiU D.nd i 1)⁻¹) (decS D.nd w (Br.iota D.nbr i w hw g))) : (D.nd.O i)ˣ) : D.nd.O i)
      = ((chiU D.nd i c (decS D.nd w (Br.iota D.nbr i w hw g)) : (D.nd.O i)ˣ) : D.nd.O i) *
        ((((chiU D.nd i 1)⁻¹ (decS D.nd w (Br.iota D.nbr i w hw g))) : (D.nd.O i)ˣ) : D.nd.O i) := rfl
  rw [e, chiOC_val C (chiU D.nd i c * (chiU D.nd i 1)⁻¹) g, e2, map_mul]
  ring

end Main


set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 800000 in
theorem charpoly_congr : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (lam : ↥(OL C.LL)), Irreducible lam → TruncatedSeriesCountingIdentities.admG3 i r ρ π → ∀ (x : D.nd.X i) (g : Br.G D.nbr i w hw) (k : ℕ), ∃ y : ↥(OL C.LL), (LinearMap.charpoly (repV C (twistM (locOC C (rTwO D.nd i r x)) θ) g) - tableLineDegreeTwo.resPoly (repV C (twistM (locOC C (WpO D.nd i ρ π)) θ)) (chiT C θ) D.R.t g).coeff k = algebraMap (↥(OL C.LL)) (↥C.LL.1) (lam * y) := by
  intro D i r ρ π w hw C θ lam hlam hG3 x g k
  haveI : CharZero ↥C.LL.1 :=
    charZero_of_injective_algebraMap (algebraMap ℚ_[D.nd.l i] ↥C.LL.1).injective
  haveI : Infinite ↥(OL C.LL) := Infinite.of_injective (fun n : ℕ => (n : ↥(OL C.LL))) (fun a b hab => by
    have := congrArg (fun z : ↥(OL C.LL) => (z : ↥C.LL.1)) hab
    simpa using this)
  obtain ⟨s, hs_def⟩ : ∃ s : ↥(OL C.LL), s = ((θ g : (↥(OL C.LL))ˣ) : ↥(OL C.LL)) *
      phiC C ((((chiU D.nd i 1)⁻¹ (decS D.nd w (Br.iota D.nbr i w hw g))) : (D.nd.O i)ˣ) : D.nd.O i) := ⟨_, rfl⟩
  have hs : IsUnit s := hs_def ▸ (θ g).isUnit.mul ((Units.isUnit _).map (phiC C))
  have e1 : twistM (locOC C (rTwO D.nd i r x)) θ g =
      s • (rO D.nd i r x (decS D.nd w (Br.iota D.nbr i w hw g))).map (phiC C) := by
    rw [hs_def]; exact twist_locOC C θ (rO D.nd i r x) (chiU D.nd i 1)⁻¹ g
  have e2 : twistM (locOC C (WpO D.nd i ρ π)) θ g =
      s • (rhoO D.nd i ρ π (decS D.nd w (Br.iota D.nbr i w hw g))).map (phiC C) := by
    rw [hs_def]; exact twist_locOC C θ (rhoO D.nd i ρ π) (chiU D.nd i 1)⁻¹ g
  have hprod : ∏ c ∈ Finset.Icc 1 D.R.t, (X - Polynomial.C (((tableLineDegreeTwo.charL (LL := ↥C.LL.1) (chiT C θ c) g : (↥C.LL.1)ˣ)) : ↥C.LL.1)) =
      (∏ c ∈ Finset.Icc 1 D.R.t, (X - Polynomial.C (s * phiC C ((chiU D.nd i c (decS D.nd w (Br.iota D.nbr i w hw g)) :
        (D.nd.O i)ˣ) : D.nd.O i)))).map (algebraMap ↥(OL C.LL) ↥C.LL.1) := by
    rw [Polynomial.map_prod]
    refine Finset.prod_congr rfl fun c _ => ?_
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, hs_def, ← chiT_val]
    rfl
  have hφ : ∀ a ∈ IsLocalRing.maximalIdeal (D.nd.O i), lam ∣ phiC C a := by
    intro a ha
    apply dvd_of_not_isUnit (D.loc (D.nd.l i)) C.LL hlam
    intro hu
    have h1 := isUnit_of_incO C.le ((D.nbr i w hw).eO a) hu
    have h2 : IsUnit a := by simpa using h1.map (D.nbr i w hw).eO.symm
    exact (IsLocalRing.mem_maximalIdeal a).1 ha h2
  obtain ⟨y, hy⟩ := core (phiC C) lam hφ (rO D.nd i r x (decS D.nd w (Br.iota D.nbr i w hw g)))
    (rhoO D.nd i ρ π (decS D.nd w (Br.iota D.nbr i w hw g)))
    (fun c => ((chiU D.nd i c (decS D.nd w (Br.iota D.nbr i w hw g)) : (D.nd.O i)ˣ) : D.nd.O i)) D.R.t
    (hG3.2.1 x _) s hs k
  refine ⟨y, ?_⟩
  rw [charpoly_repV, e1, tableLineDegreeTwo.resPoly, charpoly_repV, e2, hprod, ← Polynomial.map_mul, ← Polynomial.map_sub,
    Polynomial.coeff_map, hy]

end GlobalTheory.UseLoc.InstPoly
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChiTContIsCrysMultV
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module Classical

noncomputable section

namespace GlobalTheory.UseLoc

theorem chiT_cont_isCrys_multV : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (c : ℕ), 1 ≤ c → c ≤ D.R.t → TruncatedSeriesCountingIdentities.admG2 i r ρ π → Continuous (fun g => ((tableLineDegreeTwo.charL (LL := ↥C.LL.1) θ g : (↥C.LL.1)ˣ) : ↥C.LL.1)) → IsCrys (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (tableLineDegreeTwo.charL (LL := ↥C.LL.1) θ)) → Continuous (fun g => ((tableLineDegreeTwo.charL (LL := ↥C.LL.1) (chiT C θ c) g : (↥C.LL.1)ˣ) : ↥C.LL.1)) ∧ IsCrys (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (tableLineDegreeTwo.charL (LL := ↥C.LL.1) (chiT C θ c))) ∧ ∀ (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1) (a : ℤ), multV (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (tableLineDegreeTwo.charL (LL := ↥C.LL.1) (chiT C θ c))) τ (a + ((c : ℤ) - 1)) = multV (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (tableLineDegreeTwo.charL (LL := ↥C.LL.1) θ)) τ a := by
  intro D i r ρ π w hw C θ c h1 h2 hG2 hθc hθ
  set ψ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ := chiOC C (chiU D.nd i c * (chiU D.nd i 1)⁻¹) with hψ
  have hsplit : ∀ g, ((tableLineDegreeTwo.charL (LL := ↥C.LL.1) (chiT C θ c) g : (↥C.LL.1)ˣ) : ↥C.LL.1) =
      ((tableLineDegreeTwo.charL (LL := ↥C.LL.1) ψ g : (↥C.LL.1)ˣ) : ↥C.LL.1) *
        ((tableLineDegreeTwo.charL (LL := ↥C.LL.1) θ g : (↥C.LL.1)ˣ) : ↥C.LL.1) := by
    intro g
    simp [tableLineDegreeTwo.charL, chiT, hψ]
  have hent : ∀ g, TruncatedSeriesCountingIdentities.locC C (chiRatO D.nd i c) g 0 0 =
      ((tableLineDegreeTwo.charL (LL := ↥C.LL.1) ψ g : (↥C.LL.1)ˣ) : ↥C.LL.1) := by
    intro g
    change TruncatedSeriesCountingIdentities.CoefExt.inc C (algebraMap _ _ ((D.nbr i w hw).eO
      (chiRatO D.nd i c (decS D.nd w (Br.iota D.nbr i w hw g)) 0 0))) = _
    rw [GlobalTheory.IndefiniteRowSideFullHecke.BlockCharactersCrystallineNonGaloisCusps.chiRatO_apply]
    rfl
  let f : (Fin 1 → ↥C.LL.1) ≃ₗ[↥C.LL.1] ↥C.LL.1 := LinearEquiv.funUnique (Fin 1) ↥C.LL.1 ↥C.LL.1
  have hf : ∀ g x, f (matRep (TruncatedSeriesCountingIdentities.locC C (chiRatO D.nd i c)) g x) =
      Formalism.WeaklyAdmissibleFiltrations.charRep (tableLineDegreeTwo.charL (LL := ↥C.LL.1) ψ) g (f x) := by
    intro g x
    show (TruncatedSeriesCountingIdentities.locC C (chiRatO D.nd i c) g).mulVec x 0 =
      ((tableLineDegreeTwo.charL (LL := ↥C.LL.1) ψ g : (↥C.LL.1)ˣ) : ↥C.LL.1) • x 0
    rw [Matrix.mulVec, dotProduct, Fin.sum_univ_one, hent, smul_eq_mul]
  have cψ : IsCrys (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (tableLineDegreeTwo.charL (LL := ↥C.LL.1) ψ)) :=
    GlobalTheory.Cmp.WachMonoidal.isCrys_of_equiv _ f hf (GlobalTheory.RestPtAssembly.chiRat_isCrys D i w hw C c h1 h2)
  have jψ : ∀ τ, IsJumpV (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (tableLineDegreeTwo.charL (LL := ↥C.LL.1) ψ)) τ ((c : ℤ) - 1) :=
    fun τ => GlobalTheory.HTW.isJumpV_of_injective _ _ _ f.toLinearMap f.injective hf τ _
      ((((hG2 w hw C).1.2.2.2.1 c h1 h2 τ ((c : ℤ) - 1))).2 rfl)
  have tw : IsTwistRep (tableLineDegreeTwo.charL (LL := ↥C.LL.1) ψ) (Formalism.WeaklyAdmissibleFiltrations.charRep (tableLineDegreeTwo.charL (LL := ↥C.LL.1) θ))
      (Formalism.WeaklyAdmissibleFiltrations.charRep (tableLineDegreeTwo.charL (LL := ↥C.LL.1) (chiT C θ c))) := by
    refine ⟨LinearEquiv.refl _ _, fun g x => ?_⟩
    simp only [Formalism.WeaklyAdmissibleFiltrations.charRep, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.smul_apply, LinearMap.id_apply,
      LinearEquiv.refl_apply, smul_eq_mul, hsplit]
    ring
  obtain ⟨hcr, hm⟩ := GlobalTheory.T.crystalline_twist_crystallineCharacter_jumps_shift (D.nd.l i) (D.loc (D.nd.l i)) (D.locA (D.nd.l i)) (D.locT (D.nd.l i))
    (D.nbr i w hw).Kw C.LL ↥C.LL.1 _ ↥C.LL.1 _ _ tw cψ hθ
  refine ⟨?_, hcr, fun τ a => hm τ a _ (jψ τ)⟩
  have hO : Continuous (fun h : GE D.nd => (((chiU D.nd i c * (chiU D.nd i 1)⁻¹) h : (D.nd.O i)ˣ) : D.nd.O i)) := by
    have e : (fun h : GE D.nd => (((chiU D.nd i c * (chiU D.nd i 1)⁻¹) h : (D.nd.O i)ˣ) : D.nd.O i)) =
        fun h => ((D.nd.chi i c h : (D.nd.O i)ˣ) : D.nd.O i) * ((D.nd.chi i 1 h⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) := by
      funext h
      simp [chiU, map_inv]
    rw [e]
    exact (D.nd.chi_cont i c).mul ((D.nd.chi_cont i 1).comp continuous_inv)
  have hi : Continuous (IntermediateField.inclusion C.le) :=
    continuous_induced_rng.2 continuous_subtype_val
  have hψc : Continuous fun g => ((tableLineDegreeTwo.charL (LL := ↥C.LL.1) ψ g : (↥C.LL.1)ˣ) : ↥C.LL.1) :=
    hi.comp (continuous_subtype_val.comp ((D.nbr i w hw).eO_cont.comp
      (hO.comp (continuous_subtype_val.comp (Br.iota_cont D.nbr i w hw)))))
  have e2 : (fun g => ((tableLineDegreeTwo.charL (LL := ↥C.LL.1) (chiT C θ c) g : (↥C.LL.1)ˣ) : ↥C.LL.1)) =
      fun g => ((tableLineDegreeTwo.charL (LL := ↥C.LL.1) ψ g : (↥C.LL.1)ˣ) : ↥C.LL.1) *
        ((tableLineDegreeTwo.charL (LL := ↥C.LL.1) θ g : (↥C.LL.1)ˣ) : ↥C.LL.1) := funext hsplit
  rw [e2]
  exact hψc.mul hθc

end GlobalTheory.UseLoc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsExactLocalConditionDataAtPlace
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module Classical

noncomputable section
namespace GlobalTheory.UseLocInst


set_option maxHeartbeats 1000000 in
theorem exists_setC : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))
    (π : D.nd.X i), tableLineDegreeTwo.adm20 D HW F → AdmissibleParameterJ.ConclusionJa D → GoodR D.nd i r → π ∈ D.nd.Z i → TruncatedSeriesCountingIdentities.admG2 i r ρ π →
    TruncatedSeriesCountingIdentities.admG3 i r ρ π → TruncatedSeriesCountingIdentities.FamilyContinuous i r → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π → TruncatedSeriesCountingIdentities.CyclotomicInertiaImage (D := D) i → 5 ≤ D.nd.l i →
    D.nd.l i ∉ D.host.small → D.nd.l i ≠ D.host.q → D.nd.l i ≠ D.host.d →
    (∀ (n : ℕ) [NeZero n] (up : ZMod n → Bool) (τ : ZMod n → D.what₂.Tau), ∃ (h w η : ZMod n → ℕ) (typ : ZMod n → Bool)
      (U : ZMod n → Multiset ℤ), tableLineDegreeTwo.PositionHyps (D.nd.l i) n D.R.t h w η typ U ∧ ∀ (a : ZMod n) (b : ℤ),
        ((U a).count (b + w a) = 1 ↔ (b : ℚ) ∈ AdmissibleParameterJ.JW D (up a) (D.nd.j i) (τ a)) ∧ (U a).count (b + w a) ≤ 1) →
    ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
      ∃ (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hA : CaseA (D.nbr i w hw).Kw C.LL) (lam : ↥(OL C.LL)) (_ : Irreducible lam)
        (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ)
        (h w' η : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → ℕ)
        (typ : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Bool)
        (U : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Multiset ℤ),
        SetC HW r ρ π C hA lam θ h w' η typ U := by
  intro D HW F i r ρ π hB3 hJa hGood hZ hG2 hG3 hCont hDec hEps h5 hsm hq hd hPosition w hw
  obtain ⟨C, hA⟩ := GlobalTheory.UseLoc.exists_caseA_enl D i w hw hsm hq hd
  obtain ⟨lam, hlam⟩ := GlobalTheory.UseLocUnif.exists_uniformiser (D.nd.l i) C.LL
  obtain ⟨ep, hJ⟩ := hJa
  have hτ : ∀ a : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)),
      ∃ τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1, tableLineDegreeTwo.Over (embC HW C hA) a τ ∧
        ∀ τ' : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1, tableLineDegreeTwo.Over (embC HW C hA) a τ' → τ' = τ :=
    fun a => GlobalTheory.UseLoc.extendUnramEmb (D.nd.l i) (D.nbr i w hw).Kw C.LL hA.1 (embC HW C hA a)
  choose τa _hτa hτu using hτ
  have hJτ := fun a => hJ i r hGood w hw C (τa a)
  choose gA ρA _hRead hX hW using hJτ
  haveI := (Br.PD D.loc D.nbr i w hw).finK₀
  haveI : NeZero (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) := ⟨Module.finrank_pos.ne'⟩
  obtain ⟨h, w', η, typ, U, hS, hU⟩ := hPosition _ (fun a => decide (AdmissibleParameterJ.TypeU D ep (gA a))) ρA
  obtain ⟨θ, hθc, hθcr, hθj⟩ := (hB3 (D.nd.l i) (D.nbr i w hw).Kw C.LL hA).1 (fun a => (w' a : ℤ))
  have hθj' : ∀ a τ, tableLineDegreeTwo.Over (embC HW C hA) a τ → ∀ b,
      multV (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (tableLineDegreeTwo.charL (LL := ↥C.LL.1) θ)) τ b =
        if b = (w' a : ℤ) then 1 else 0 := hθj
  have hθnz : ∀ a τ, tableLineDegreeTwo.Over (embC HW C hA) a τ →
      multV (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (tableLineDegreeTwo.charL (LL := ↥C.LL.1) θ)) τ (w' a) ≠ 0 := by
    intro a τ hO
    rw [hθj' a τ hO]
    simp
  have hWp : ∀ a τ, tableLineDegreeTwo.Over (embC HW C hA) a τ → ∀ b : ℤ,
      multV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (WpO D.nd i ρ π))) τ b =
        ((U a).count (b + w' a) : ℤ) := by
    intro a τ hO b
    rw [hτu a τ hO, ((hW a) ρ π hZ hDec b).2.1]
    obtain ⟨h1, h2⟩ := hU a b
    by_cases hb : ((b : ℤ) : ℚ) ∈ AdmissibleParameterJ.JW D (decide (AdmissibleParameterJ.TypeU D ep (gA a))) (D.nd.j i) (ρA a)
    · rw [if_pos hb, h1.2 hb]
      simp
    · rw [if_neg hb]
      have : (U a).count (b + w' a) ≠ 1 := fun e => hb (h1.1 e)
      omega
  have hL6 := GlobalTheory.UseLoc.crys_Wp_rTw D i r ρ π w hw C hGood hZ hG2 hDec
  have hL4 := GlobalTheory.UseLoc.TwistCrysW.isCrys_and_multV D i w hw C
  have hL5 := GlobalTheory.UseLoc.twistM_repV_cont D i w hw C
  have hWcont : Continuous fun g => WpO D.nd i ρ π g :=
    (GlobalTheory.Pass.stepSub_holds D i r ρ hGood π hDec {π} rfl).1.1
  refine ⟨C, hA, lam, hlam, θ, h, w', η, typ, U, ?_, ?_⟩
  · refine ⟨D.R.t_odd.pos, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Br.PD_p]
      exact hS
    · exact hL5 _ (WpO D.nd i ρ π) θ hWcont hθc
    · exact (hL4 _ (WpO D.nd i ρ π) θ hL6.1 hθcr).1
    · intro a τ hO b
      have e := (hL4 _ (WpO D.nd i ρ π) θ hL6.1 hθcr).2 τ (w' a) (hθnz a τ hO) (b - w' a)
      rw [sub_add_cancel] at e
      rw [e, hWp a τ hO, sub_add_cancel]
    · intro c hc
      obtain ⟨hc1, hc2⟩ := Finset.mem_Icc.1 hc
      obtain ⟨k1, k2, k3⟩ := GlobalTheory.UseLoc.chiT_cont_isCrys_multV D i r ρ π w hw C θ c hc1 hc2 hG2 hθc hθcr
      refine ⟨GlobalTheory.UseLoc.chiT_cyc D i w hw C θ c hc1 hc2, k1, k2, ?_⟩
      intro a τ hO b
      have e := k3 τ (b - ((c : ℤ) - 1))
      rw [sub_add_cancel b ((c : ℤ) - 1)] at e
      rw [e, hθj' a τ hO]
      split_ifs <;> omega
  · intro x
    refine ⟨hL5 _ (rTwO D.nd i r x) θ (GlobalTheory.Pass.FamCont.stepCont D i r hGood x).1 hθc,
      (hL4 _ (rTwO D.nd i r x) θ (hL6.2 x) hθcr).1, ?_,
      GlobalTheory.UseLoc.InstPoly.charpoly_congr D i r ρ π w hw C θ lam hlam hG3 x⟩
    intro a τ hO b
    have e := (hL4 _ (rTwO D.nd i r x) θ (hL6.2 x) hθcr).2 τ (w' a) (hθnz a τ hO) (b - w' a)
    rw [sub_add_cancel] at e
    rw [e, hτu a τ hO, ((hX a) x (b - w' a)).2.1]
    have e2 := GlobalTheory.jTil_shift_block (D.nd.l i) _ D.R.t h w' η typ U hS a
      (AdmissibleParameterJ.JW D (decide (AdmissibleParameterJ.TypeU D ep (gA a))) (D.nd.j i) (ρA a)) (hU a) (b - w' a)
    rw [sub_add_cancel] at e2
    rw [← e2]
    exact if_congr (GlobalTheory.UseLoc.JumpBlock.jumps_iff D _ _ _ _) rfl rfl

end GlobalTheory.UseLocInst
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsExactLocalConditionDataAtPlaceStatement
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_exactLocalConditionData_at_place : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))
    (π : D.nd.X i), tableLineDegreeTwo.adm20 D HW F → AdmissibleParameterJ.ConclusionJa D → GoodR D.nd i r → π ∈ D.nd.Z i → TruncatedSeriesCountingIdentities.admG2 i r ρ π →
    TruncatedSeriesCountingIdentities.admG3 i r ρ π → TruncatedSeriesCountingIdentities.FamilyContinuous i r → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π → TruncatedSeriesCountingIdentities.CyclotomicInertiaImage (D := D) i → 5 ≤ D.nd.l i →
    D.nd.l i ∉ D.host.small → D.nd.l i ≠ D.host.q → D.nd.l i ≠ D.host.d →
    (∀ (n : ℕ) [NeZero n] (up : ZMod n → Bool) (τ : ZMod n → D.what₂.Tau), ∃ (h w η : ZMod n → ℕ) (typ : ZMod n → Bool)
      (U : ZMod n → Multiset ℤ), tableLineDegreeTwo.PositionHyps (D.nd.l i) n D.R.t h w η typ U ∧ ∀ (a : ZMod n) (b : ℤ),
        ((U a).count (b + w a) = 1 ↔ (b : ℚ) ∈ AdmissibleParameterJ.JW D (up a) (D.nd.j i) (τ a)) ∧ (U a).count (b + w a) ≤ 1) →
    ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
      ∃ (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hA : CaseA (D.nbr i w hw).Kw C.LL) (lam : ↥(OL C.LL)) (_ : Irreducible lam)
        (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ)
        (h w' η : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → ℕ)
        (typ : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Bool)
        (U : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Multiset ℤ),
        SetC HW r ρ π C hA lam θ h w' η typ U := by
  first | exact @GlobalTheory.UseLocInst.exists_setC | exact GlobalTheory.UseLocInst.exists_setC | (intros; apply GlobalTheory.UseLocInst.exists_setC <;> assumption)
end
