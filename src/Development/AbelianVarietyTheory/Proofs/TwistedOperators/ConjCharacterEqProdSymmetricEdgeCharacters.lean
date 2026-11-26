module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsContinuousLeftInvariantRepConjugateTensor
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjIntertwinerPointValueSobolevContinuous
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteAdditiveCharNeOneAtEachPrime
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergArchimedeanDiffOperatorHasDerivAtFamil
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ResidueConjugatePlaceCharacterArgumentSignedSum

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelCharacterOnStabilizerEqProdResidueCharacter
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjInstanceCharacterEqProdResidueFieldAddChars
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjInstanceCharacterEqProdResidueFieldAddChars
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

noncomputable section
namespace GlobalTheory.SeeConjProd
open Formalism.L2.SG.InstExistsPf GlobalTheory.FlagBasis Formalism.L2.SG.HidaSetting
open scoped TensorProduct
variable {D : D7}

theorem sigInt_oToS (a : 𝓞 D.host.E) :
    sigInt (instOf D) (oToS D.host.F D.host.E a) = oToS D.host.F D.host.E (GlobalTheory.IdemSupport.cO D a) :=
  Subtype.ext (Formalism.L2.SG.Pf.unitaryCongruence.sigA_inclE (instOf D) (a : D.host.E))

theorem conjRes_mk (PP : Pl D.host.E) (x : 𝓞 D.host.E) :
    GlobalTheory.SeeConjChar.conjRes PP (Ideal.Quotient.mk PP.asIdeal x) =
      Ideal.Quotient.mk (GlobalTheory.IdemSupport.cP PP).asIdeal (GlobalTheory.IdemSupport.cO D x) := rfl

theorem conj_res_oToS (PP : Pl D.host.E) (a : 𝓞 D.host.E) :
    GlobalTheory.SeeConjChar.conjRes PP (resS D.host.F PP (sigInt (instOf D) (oToS D.host.F D.host.E a))) =
      Ideal.Quotient.mk (GlobalTheory.IdemSupport.cP PP).asIdeal a := by
  rw [sigInt_oToS, resS_oToS, conjRes_mk, GlobalTheory.IdemSupport.cO_cO]

theorem resS_cP (PP : Pl D.host.E) (s : Formalism.L2.Herm.intAf D.host.F D.host.E) :
    resS D.host.F (GlobalTheory.IdemSupport.cP PP) s =
      GlobalTheory.SeeConjChar.conjRes PP (resS D.host.F PP (sigInt (instOf D) s)) := by
  set f1 : Formalism.L2.Herm.intAf D.host.F D.host.E →+* kP (GlobalTheory.IdemSupport.cP PP) :=
    (GlobalTheory.SeeConjChar.conjRes PP).toRingHom.comp ((resS D.host.F PP).comp (sigInt (instOf D))) with hf
  have hf0 : ∀ x, f1 x = GlobalTheory.SeeConjChar.conjRes PP (resS D.host.F PP (sigInt (instOf D) x)) := fun x => rfl
  have hf1 : ∀ a, f1 (oToS D.host.F D.host.E a) = Ideal.Quotient.mk (GlobalTheory.IdemSupport.cP PP).asIdeal a :=
    fun a => (hf0 _).trans (conj_res_oToS PP a)
  have hker : idS D.host.F (GlobalTheory.IdemSupport.cP PP).asIdeal ≤ RingHom.ker f1 := by
    refine Ideal.map_le_iff_le_comap.2 fun c hc => ?_
    rw [Ideal.mem_comap, RingHom.mem_ker, hf1]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hc
  obtain ⟨a, ha⟩ := (cmpS_bij (F := D.host.F) (GlobalTheory.IdemSupport.cP PP).asIdeal (GlobalTheory.IdemSupport.cP PP).ne_bot).2
    (Ideal.Quotient.mk _ s)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  have e : Ideal.Quotient.mk (idS D.host.F (GlobalTheory.IdemSupport.cP PP).asIdeal) s =
      Ideal.Quotient.mk _ (oToS D.host.F D.host.E a) := ha.symm
  have hd : s - oToS D.host.F D.host.E a ∈ idS D.host.F (GlobalTheory.IdemSupport.cP PP).asIdeal := Ideal.Quotient.eq.1 e
  have hker2 : idS D.host.F (GlobalTheory.IdemSupport.cP PP).asIdeal ≤ RingHom.ker (resS D.host.F (GlobalTheory.IdemSupport.cP PP)) := by
    refine Ideal.map_le_iff_le_comap.2 fun c hc => ?_
    rw [Ideal.mem_comap, RingHom.mem_ker, resS_oToS]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hc
  have h2 : resS D.host.F (GlobalTheory.IdemSupport.cP PP) s = resS D.host.F (GlobalTheory.IdemSupport.cP PP) (oToS D.host.F D.host.E a) := by
    have := hker2 hd
    rwa [RingHom.mem_ker, map_sub, sub_eq_zero] at this
  have h1 : f1 s = f1 (oToS D.host.F D.host.E a) := by
    have := hker hd
    rwa [RingHom.mem_ker, map_sub, sub_eq_zero] at this
  exact h2.trans ((resS_oToS _ a).trans ((hf1 a).symm.trans (h1.symm.trans (hf0 s))))

theorem exists_addChar_ne_one (k : Type) [Field k] [Finite k] : ∃ ψ : AddChar k ℂ, ψ ≠ 1 := by
  have h1 : Multiplicative.ofAdd (1 : k) ≠ 1 := by
    intro h
    exact one_ne_zero (congrArg Multiplicative.toAdd h)
  obtain ⟨φ, hφ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity (Multiplicative k) ℂ h1
  let ψ : AddChar k ℂ :=
    { toFun := fun x => ((φ (Multiplicative.ofAdd x) : ℂˣ) : ℂ)
      map_zero_eq_one' := by simp
      map_add_eq_mul' := fun x y => by simp [ofAdd_add] }
  refine ⟨ψ, fun h => hφ (Units.ext ?_)⟩
  have := congrArg (fun χ : AddChar k ℂ => χ 1) h
  simpa [ψ] using this

theorem addChar_comp_ne_one {k k' : Type} [Field k] [Field k'] (ψ : AddChar k ℂ) (hψ : ψ ≠ 1) (a : k) (ha : a ≠ 0)
    (e : k' ≃+* k) : ψ.compAddMonoidHom ((AddMonoidHom.mulLeft a).comp e.toAddMonoidHom) ≠ 1 := by
  intro h
  apply hψ
  ext t
  have := congrArg (fun χ : AddChar k' ℂ => χ (e.symm (a⁻¹ * t))) h
  change ψ (a * e (e.symm (a⁻¹ * t))) = (1 : AddChar k' ℂ) (e.symm (a⁻¹ * t)) at this
  rw [RingEquiv.apply_symm_apply, ← mul_assoc, mul_inv_cancel₀ ha, one_mul, AddChar.one_apply] at this
  rw [this, AddChar.one_apply]

theorem cP_cP (P : Pl D.host.E) : GlobalTheory.IdemSupport.cP (GlobalTheory.IdemSupport.cP P) = P := by
  apply HeightOneSpectrum.ext
  ext x
  rw [GlobalTheory.IdemSupport.mem_cP, GlobalTheory.IdemSupport.mem_cP, GlobalTheory.IdemSupport.cO_cO]

theorem sigInt_sigInt (s : Formalism.L2.Herm.intAf D.host.F D.host.E) : sigInt (instOf D) (sigInt (instOf D) s) = s :=
  Subtype.ext (Formalism.L2.SG.Pf.unitaryCongruence.sigA_sigA (instOf D) s.1)

theorem conjRes_cP (PP : Pl D.host.E) (s : Formalism.L2.Herm.intAf D.host.F D.host.E) :
    GlobalTheory.SeeConjChar.conjRes (GlobalTheory.IdemSupport.cP PP) (resS D.host.F (GlobalTheory.IdemSupport.cP PP) s) =
      resS D.host.F (GlobalTheory.IdemSupport.cP (GlobalTheory.IdemSupport.cP PP)) (sigInt (instOf D) s) := by
  rw [resS_cP (GlobalTheory.IdemSupport.cP PP) (sigInt (instOf D) s), sigInt_sigInt]


open Classical in
theorem core (psiEf : (instOf D).E ⊗[(instOf D).F] Formalism.MainNotions.S.Af (instOf D).F → ℂ)
    (hadd : ∀ x y, psiEf (x + y) = psiEf x * psiEf y)
    (hint : ∀ x ∈ IntAf (instOf D).F (instOf D).E, psiEf x = 1)
    (hrat : ∀ x : (instOf D).E,
      psiEf (Formalism.UG.inclE (F := (instOf D).F) (Formalism.MainNotions.S.Af (instOf D).F) x) * psiEinf (instOf D) x = 1)
    (Pg : Finset (Pl D.host.E)) (hdiv : ∀ PP ∈ Pg, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal)
    (hcov : ∀ Q : Pl D.host.E, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal →
      ∃ PP ∈ Pg, Q = PP ∨ Q = GlobalTheory.IdemSupport.cP PP)
    (hnc : ∀ PP ∈ Pg, ∀ PP' ∈ Pg, ¬ IsConjPl (D := D) PP PP') :
    ∃ ψ : ∀ P : Pl D.host.E, AddChar (kP P) ℂ, (∀ PP ∈ Pg, ψ PP ≠ 1 ∧ ψ (GlobalTheory.IdemSupport.cP PP) ≠ 1) ∧
      ∀ s : Formalism.L2.Herm.intAf D.host.F D.host.E,
        psiEf (divN (instOf D) (D.host.g 0 * D.host.g 1) s.1) =
          ∏ PP ∈ Pg, ψ PP (resS D.host.F PP s) *
            ψ (GlobalTheory.IdemSupport.cP PP) (resS D.host.F (GlobalTheory.IdemSupport.cP PP) s) := by
  have hg : D.host.g 0 * D.host.g 1 ≠ 0 := mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
  have hN : ∀ s : Formalism.L2.Herm.intAf D.host.F D.host.E,
      (∀ PP ∈ Pg, resS D.host.F PP s = 0 ∧ resS D.host.F PP (sigInt (instOf D) s) = 0) →
      ZMod' (instOf D) (D.host.g 0 * D.host.g 1) s.1 := by
    intro s hs
    refine GlobalTheory.T.integralAdele_congr_zero_of_residues_squarefree (instOf D) _ hg (GlobalTheory.T.typePrimes_product_not_mem_sq_place D) s fun Q hQ => ?_
    obtain ⟨PP, hPP, rfl | rfl⟩ := hcov Q hQ
    · exact (hs _ hPP).1
    · exact (resS_cP PP s).trans (by rw [(hs _ hPP).2]; exact map_zero _)
  choose ψ0 hψ0 using fun P : Pl D.host.E => exists_addChar_ne_one (kP P)
  obtain ⟨a₁, a₂, ha, hχ⟩ := GlobalTheory.T.character_residueFields_eq_prod_genericShift D.host.E (Formalism.L2.Herm.intAf D.host.F D.host.E) Pg (fun PP => resS D.host.F PP)
    (fun PP => (resS D.host.F PP).comp (sigInt (instOf D)))
    (fun s => psiEf (divN (instOf D) (D.host.g 0 * D.host.g 1) s.1)) ψ0 (fun PP _ => hψ0 PP)
    (fun s t => (congrArg psiEf (Formalism.L2.SG.Pf.unitaryCongruence.divN_add (instOf D) (D.host.g 0 * D.host.g 1) s.1 t.1)).trans
      (hadd _ _))
    (fun s hs => by
      obtain ⟨t, ht, e⟩ := hN s hs
      have : divN (instOf D) (D.host.g 0 * D.host.g 1) s.1 = t :=
        (congrArg _ e).trans (Formalism.L2.SG.Pf.unitaryCongruence.divN_gmul _ _ hg t)
      show psiEf (divN (instOf D) (D.host.g 0 * D.host.g 1) s.1) = 1
      rw [this, hint t ht])
    (GlobalTheory.T.exists_integralAdele_prescribed_residues_and_conj D Pg hnc)
    (GlobalTheory.T.residueSupport_single_place_to_conjugatePair_position D Pg hdiv hnc (fun s => psiEf (divN (instOf D) (D.host.g 0 * D.host.g 1) s.1) ≠ 1)
      fun Q hQ => GlobalTheory.T.exists_finiteAdditiveChar_ne_one_at_each_prime D psiEf hadd hint hrat Q hQ)
  have hout : ∀ PP ∈ Pg, GlobalTheory.IdemSupport.cP PP ∉ Pg := fun PP hPP h =>
    hnc PP hPP _ h ((GlobalTheory.IdemSupport.isConjPl_iff _ _).2 rfl)
  let ψ : ∀ P : Pl D.host.E, AddChar (kP P) ℂ := fun P =>
    if P ∈ Pg then (ψ0 P).compAddMonoidHom ((AddMonoidHom.mulLeft (a₁ P)).comp (RingEquiv.refl (kP P)).toAddMonoidHom)
    else if GlobalTheory.IdemSupport.cP P ∈ Pg then (ψ0 (GlobalTheory.IdemSupport.cP P)).compAddMonoidHom
      ((AddMonoidHom.mulLeft (a₂ (GlobalTheory.IdemSupport.cP P))).comp (GlobalTheory.SeeConjChar.conjRes P).toAddMonoidHom)
    else 1
  have hψ1 : ∀ PP ∈ Pg, ψ PP = (ψ0 PP).compAddMonoidHom
      ((AddMonoidHom.mulLeft (a₁ PP)).comp (RingEquiv.refl (kP PP)).toAddMonoidHom) := fun PP hPP => if_pos hPP
  have hψ2 : ∀ PP ∈ Pg, ψ (GlobalTheory.IdemSupport.cP PP) = (ψ0 (GlobalTheory.IdemSupport.cP (GlobalTheory.IdemSupport.cP PP))).compAddMonoidHom
      ((AddMonoidHom.mulLeft (a₂ (GlobalTheory.IdemSupport.cP (GlobalTheory.IdemSupport.cP PP)))).comp
        (GlobalTheory.SeeConjChar.conjRes (GlobalTheory.IdemSupport.cP PP)).toAddMonoidHom) := fun PP hPP => by
    have h2 : GlobalTheory.IdemSupport.cP (GlobalTheory.IdemSupport.cP PP) ∈ Pg := by rw [cP_cP]; exact hPP
    exact (if_neg (hout PP hPP)).trans (if_pos h2)
  refine ⟨ψ, fun PP hPP => ⟨?_, ?_⟩, fun s => ?_⟩
  · rw [hψ1 PP hPP]
    exact addChar_comp_ne_one _ (hψ0 PP) _ (ha PP hPP).1 _
  · rw [hψ2 PP hPP]
    refine addChar_comp_ne_one _ (hψ0 _) _ ?_ _
    rw [cP_cP]
    exact (ha PP hPP).2
  · refine (hχ s).trans (Finset.prod_congr rfl fun PP hPP => ?_)
    refine (AddChar.map_add_eq_mul (ψ0 PP) _ _).trans (congrArg₂ (· * ·) ?_ ?_)
    · rw [hψ1 PP hPP]
      rfl
    rw [hψ2 PP hPP]
    show _ = ψ0 (GlobalTheory.IdemSupport.cP (GlobalTheory.IdemSupport.cP PP)) (a₂ (GlobalTheory.IdemSupport.cP (GlobalTheory.IdemSupport.cP PP)) *
      GlobalTheory.SeeConjChar.conjRes (GlobalTheory.IdemSupport.cP PP) (resS D.host.F (GlobalTheory.IdemSupport.cP PP) s))
    rw [conjRes_cP]
    have key : ∀ Q : Pl D.host.E, Q = PP → ψ0 Q (a₂ Q * resS D.host.F Q (sigInt (instOf D) s)) =
        ψ0 PP (a₂ PP * resS D.host.F PP (sigInt (instOf D) s)) := by
      rintro Q rfl
      rfl
    exact (key _ (cP_cP PP)).symm

theorem chiS_eq_prod : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (Pg : Finset (Pl D.host.E)), (∀ PP ∈ Pg, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → (∀ Q : Pl D.host.E, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal → ∃ PP ∈ Pg, Q = PP ∨ Q = GlobalTheory.IdemSupport.cP PP) → (∀ PP ∈ Pg, ∀ PP' ∈ Pg, ¬ IsConjPl (D := D) PP PP') → ∃ ψ : ∀ P : Pl D.host.E, AddChar (kP P) ℂ, (∀ PP ∈ Pg, ψ PP ≠ 1 ∧ ψ (GlobalTheory.IdemSupport.cP PP) ≠ 1) ∧ ∀ c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, GlobalTheory.SeeConjChar.chiS X h c = ∏ PP ∈ Pg, ψ PP (GlobalTheory.SeeConjChar.resT PP c) * ψ (GlobalTheory.IdemSupport.cP PP) (GlobalTheory.SeeConjChar.resT (GlobalTheory.IdemSupport.cP PP) c) := by
  intro D X h Pg hdiv hcov hnc
  have key : ∀ (I : AutInst) (hI : I = instOf D) (g : ℕ) (_ : g = D.host.g 0 * D.host.g 1)
      (psiEf : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F → ℂ) (_ : ∀ x y, psiEf (x + y) = psiEf x * psiEf y)
      (_ : ∀ x ∈ IntAf I.F I.E, psiEf x = 1)
      (_ : ∀ x : I.E, psiEf (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) x) * psiEinf I x = 1),
      ∃ ψ : ∀ P : Pl D.host.E, AddChar (kP P) ℂ, (∀ PP ∈ Pg, ψ PP ≠ 1 ∧ ψ (GlobalTheory.IdemSupport.cP PP) ≠ 1) ∧
        ∀ c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E,
          psiEf (divN I g (cast (congrArg (fun I : AutInst => TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F)) hI).symm c)) =
            ∏ PP ∈ Pg, ψ PP (GlobalTheory.SeeConjChar.resT PP c) *
              ψ (GlobalTheory.IdemSupport.cP PP) (GlobalTheory.SeeConjChar.resT (GlobalTheory.IdemSupport.cP PP) c) := by
    intro I hI g hg psiEf hadd hint hrat
    subst hI hg
    obtain ⟨ψ, hψ, hprod⟩ := core psiEf hadd hint hrat Pg hdiv hcov hnc
    refine ⟨ψ, hψ, fun c hc => ?_⟩
    have e1 : ∀ P : Pl D.host.E, GlobalTheory.SeeConjChar.resT P c = resS D.host.F P ⟨c, hc⟩ := fun P => dif_pos hc
    simp only [e1, cast_eq]
    exact hprod ⟨c, hc⟩
  exact key X.B.I h X.B.g X.g_eq X.psiEf X.psiEf_add X.psiEf_int X.psiEf_rat

end GlobalTheory.SeeConjProd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjInstanceCharacterEqProdResidueFieldAddCharsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjInstanceCharacter_eq_prod_residueField_addChars : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (Pg : Finset (Pl D.host.E)), (∀ PP ∈ Pg, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → (∀ Q : Pl D.host.E, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal → ∃ PP ∈ Pg, Q = PP ∨ Q = GlobalTheory.IdemSupport.cP PP) → (∀ PP ∈ Pg, ∀ PP' ∈ Pg, ¬ IsConjPl (D := D) PP PP') → ∃ ψ : ∀ P : Pl D.host.E, AddChar (kP P) ℂ, (∀ PP ∈ Pg, ψ PP ≠ 1 ∧ ψ (GlobalTheory.IdemSupport.cP PP) ≠ 1) ∧ ∀ c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, GlobalTheory.SeeConjChar.chiS X h c = ∏ PP ∈ Pg, ψ PP (GlobalTheory.SeeConjChar.resT PP c) * ψ (GlobalTheory.IdemSupport.cP PP) (GlobalTheory.SeeConjChar.resT (GlobalTheory.IdemSupport.cP PP) c) := by
  first | exact @GlobalTheory.SeeConjProd.chiS_eq_prod | exact GlobalTheory.SeeConjProd.chiS_eq_prod | (intros; apply GlobalTheory.SeeConjProd.chiS_eq_prod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelCharacterOnStabilizerEqProdResidueCharacter
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

namespace GlobalTheory.SeeConjChar

theorem levelCharacter_on_stabilizer_eq_prod_residue_characters : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → ∃ ψ : ∀ P : Pl D.host.E, AddChar (kP P) ℂ, (∀ PP ∈ R.Pg, ψ PP ≠ 1 ∧ ψ (GlobalTheory.IdemSupport.cP PP) ≠ 1) ∧ ∀ κ : GA D (Yc D 0), ((iotaX X h).toMulEquiv κ).2 ∈ X.B.I.Kset → X.chi2 ((iotaX X h).toMulEquiv κ).2 = ∏ PP ∈ R.Pg, ψ PP (GlobalTheory.SeeConjChar.resT PP (GlobalTheory.SeeConjChar.argT X h (finE (Yc D 0) κ))) * ψ (GlobalTheory.IdemSupport.cP PP) (GlobalTheory.SeeConjChar.resT (GlobalTheory.IdemSupport.cP PP) (GlobalTheory.SeeConjChar.argT X h (finE (Yc D 0) κ))) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h hL hG
  obtain ⟨hg, hcov⟩ := GlobalTheory.T.typePlaces_over_norm_and_cover_with_conjugates R hL
  obtain ⟨ψ, hψ, hprod⟩ := GlobalTheory.T.conjInstanceCharacter_eq_prod_residueField_addChars X h R.Pg hg hcov (GlobalTheory.T.levelPlaces_not_isConjPlace_realDat R F hL hG)
  refine ⟨ψ, hψ, fun κ hκ => ?_⟩
  obtain ⟨hi, he⟩ := GlobalTheory.T.otherInstanceCharacter_eq_conjInstancePsiValue_integral X h κ hκ
  rw [he, hprod _ hi]

end GlobalTheory.SeeConjChar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelCharacterOnStabilizerEqProdResidueCharacterStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelCharacter_on_stabilizer_eq_prod_residue_characters_alt : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → ∃ ψ : ∀ P : Pl D.host.E, AddChar (kP P) ℂ, (∀ PP ∈ R.Pg, ψ PP ≠ 1 ∧ ψ (GlobalTheory.IdemSupport.cP PP) ≠ 1) ∧ ∀ κ : GA D (Yc D 0), ((iotaX X h).toMulEquiv κ).2 ∈ X.B.I.Kset → X.chi2 ((iotaX X h).toMulEquiv κ).2 = ∏ PP ∈ R.Pg, ψ PP (GlobalTheory.SeeConjChar.resT PP (GlobalTheory.SeeConjChar.argT X h (finE (Yc D 0) κ))) * ψ (GlobalTheory.IdemSupport.cP PP) (GlobalTheory.SeeConjChar.resT (GlobalTheory.IdemSupport.cP PP) (GlobalTheory.SeeConjChar.argT X h (finE (Yc D 0) κ))) := by
  first | exact @GlobalTheory.SeeConjChar.levelCharacter_on_stabilizer_eq_prod_residue_characters | exact GlobalTheory.SeeConjChar.levelCharacter_on_stabilizer_eq_prod_residue_characters | (intros; apply GlobalTheory.SeeConjChar.levelCharacter_on_stabilizer_eq_prod_residue_characters <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ResidueLevelCharacterArgumentAtTypePlace
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ResidueLevelCharacterArgumentAtTypePlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

noncomputable section

namespace GlobalTheory.SeeResAt

open Classical Matrix GlobalTheory.SeeConjChar

section Ring

variable {A κ : Type} [CommRing A] [CommRing κ] {S : Subring A} (π : S →+* κ)

def resOf (x : A) : κ := if hx : x ∈ S then π ⟨x, hx⟩ else 0

theorem resOf_of_mem {x : A} (hx : x ∈ S) : resOf π x = π ⟨x, hx⟩ := dif_pos hx

theorem resOf_coe (x : S) : resOf π (x : A) = π x := dif_pos x.2

theorem resOf_zero : resOf π (0 : A) = 0 := by
  rw [resOf_of_mem π (zero_mem S)]; exact map_zero π

theorem resOf_one : resOf π (1 : A) = 1 := by
  rw [resOf_of_mem π (one_mem S)]; exact map_one π

theorem resOf_add {x y : A} (hx : x ∈ S) (hy : y ∈ S) : resOf π (x + y) = resOf π x + resOf π y := by
  rw [resOf_of_mem π hx, resOf_of_mem π hy, resOf_of_mem π (add_mem hx hy), ← map_add (f := _)]; rfl

theorem resOf_mul {x y : A} (hx : x ∈ S) (hy : y ∈ S) : resOf π (x * y) = resOf π x * resOf π y := by
  rw [resOf_of_mem π hx, resOf_of_mem π hy, resOf_of_mem π (mul_mem hx hy), ← map_mul]; rfl

theorem resOf_sum {ι : Type} (s : Finset ι) (f : ι → A) (hf : ∀ i, f i ∈ S) :
    resOf π (∑ i ∈ s, f i) = ∑ i ∈ s, resOf π (f i) := by
  induction s using Finset.induction_on with
  | empty => simpa using resOf_zero π
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, resOf_add π (hf a) (sum_mem fun i _ => hf i), ih]

theorem resOf_of_cong {g : ℕ} (hg : (g : κ) = 0) {x c : A} (hc : c ∈ S) (h : ∃ t ∈ S, x - c = (g : A) * t) :
    resOf π x = resOf π c := by
  obtain ⟨t, ht, e⟩ := h
  have e' : x = c + (g : A) * t := by rw [← e]; ring
  have hgS : (g : A) ∈ S := natCast_mem S g
  have h0 : resOf π (g : A) = 0 := by
    rw [resOf_of_mem π hgS, ← hg, ← map_natCast π g]
    congr 1
  rw [e', resOf_add π hc (mul_mem hgS ht), resOf_mul π hgS ht, h0, zero_mul, add_zero]

theorem lin_mulVec {n : ℕ} (φ : (Fin n → A) →ₗ[A] A) (B : Matrix (Fin n) (Fin n) A) (v : Fin n → A) :
    φ (B *ᵥ v) = ∑ l, φ (B *ᵥ Pi.single l 1) * v l := by
  have e : v = ∑ l, v l • (Pi.single l 1 : Fin n → A) := by
    funext i; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [e]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Matrix.mulVec_sum, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.mulVec_smul, map_smul, smul_eq_mul, mul_comm]

theorem resOf_frame {n : ℕ} (φ : (Fin n → A) →ₗ[A] A) (β : GL (Fin n) A)
    (hφ : ∀ v : Fin n → A, (∀ i, ((β⁻¹).val *ᵥ v) i ∈ S) → φ v ∈ S) (w : Fin n → Fin n → A)
    (hw : ∀ i j, ∃ hm : ((β⁻¹).val *ᵥ w j) i ∈ S, π ⟨_, hm⟩ = if i = j then 1 else 0)
    (y : Matrix (Fin n) (Fin n) S) (j : Fin n) :
    resOf π (φ ((β.val * y.map S.subtype * (β⁻¹).val) *ᵥ w j)) = ∑ l, resOf π (φ (w l)) * π (y l j) := by
  have hc : ∀ l, φ (β.val *ᵥ Pi.single l 1) ∈ S := fun l => hφ _ fun i => by
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Pi.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have key : ∀ v : Fin n → A, (∀ i, v i ∈ S) →
      resOf π (φ (β.val *ᵥ v)) = ∑ l, resOf π (φ (β.val *ᵥ Pi.single l 1)) * resOf π (v l) := by
    intro v hv
    rw [lin_mulVec, resOf_sum π _ _ fun l => mul_mem (hc l) (hv l)]
    exact Finset.sum_congr rfl fun l _ => resOf_mul π (hc l) (hv l)
  have hm : ∀ j i, ((β⁻¹).val *ᵥ w j) i ∈ S := fun j i => (hw i j).1
  have hr : ∀ j i, resOf π (((β⁻¹).val *ᵥ w j) i) = if i = j then 1 else 0 := fun j i => by
    rw [resOf_of_mem π (hm j i)]; exact (hw i j).2
  have hwl : ∀ l, resOf π (φ (w l)) = resOf π (φ (β.val *ᵥ Pi.single l 1)) := by
    intro l
    have e : w l = β.val *ᵥ ((β⁻¹).val *ᵥ w l) := by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    conv_lhs => rw [e]
    rw [key _ (hm l)]
    simp only [hr]
    simp
  have hy : ∀ l, (y.map S.subtype *ᵥ ((β⁻¹).val *ᵥ w j)) l = ∑ m, (y l m : A) * ((β⁻¹).val *ᵥ w j) m := fun l => rfl
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    key _ fun l => by rw [hy]; exact sum_mem fun m _ => mul_mem (y l m).2 (hm j m)]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hwl, hy, resOf_sum π _ _ fun m => mul_mem (y l m).2 (hm j m)]
  congr 1
  rw [Finset.sum_congr rfl fun m _ => resOf_mul π (y l m).2 (hm j m)]
  simp only [hr, resOf_coe]
  simp

end Ring

def nxtPos (ρ k a : ℕ) : ℕ := if a + 1 < ρ then a + 1 else ρ + k

theorem nxtPos_le (ρ k a : ℕ) : nxtPos ρ k a ≤ ρ + k := by
  unfold nxtPos; split_ifs <;> omega

theorem sum_symEdge {κ : Type} [CommRing κ] {r ρ k : ℕ} (hr : ρ + k < r) (s : Bool) (U : Fin r → Fin r → κ) :
    (∑ i, ∑ j, if symEdge ρ k i j then ((wA ρ k s i j : ℤ) : κ) * U i j else 0) =
      (∑ a : Fin ρ, U ⟨a.1, by omega⟩ ⟨nxtPos ρ k a.1, (nxtPos_le ρ k a.1).trans_lt hr⟩) +
        ∑ i : Fin k, if i.1 + 1 < k then (if s then U ⟨ρ + i.1, by omega⟩ ⟨ρ + i.1 + 1, by omega⟩ else 0) else 0 := by
  obtain ⟨t, rfl⟩ : ∃ t, r = ρ + (k + t) := ⟨r - (ρ + k), by omega⟩
  rw [Fin.sum_univ_add, Fin.sum_univ_add]
  have h3 : (∑ i : Fin t, ∑ j, if symEdge ρ k (Fin.natAdd ρ (Fin.natAdd k i)) j then
      ((wA ρ k s (Fin.natAdd ρ (Fin.natAdd k i)) j : ℤ) : κ) * U (Fin.natAdd ρ (Fin.natAdd k i)) j else 0) = 0 := by
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    have : wA ρ k s (Fin.natAdd ρ (Fin.natAdd k i)) j = 0 := by
      unfold wA
      rw [if_neg (by simp), if_neg (by simp; omega)]
    rw [this]; simp
  rw [h3, add_zero]
  congr 1
  · refine Finset.sum_congr rfl fun a _ => ?_
    have ha := a.2
    rw [Finset.sum_eq_single ⟨nxtPos ρ k a.1, (nxtPos_le ρ k a.1).trans_lt hr⟩]
    · rw [if_pos]
      · have : wA ρ k s (Fin.castAdd (k + t) a) ⟨nxtPos ρ k a.1, (nxtPos_le ρ k a.1).trans_lt hr⟩ = 1 := by
          unfold wA
          rw [if_pos (by simp)]
        rw [this, Int.cast_one, one_mul]
        rfl
      · unfold symEdge nxtPos
        simp only [Fin.val_castAdd]
        split_ifs <;> omega
    · intro j _ hj
      rw [if_neg]
      intro h
      apply hj
      apply Fin.ext
      unfold symEdge at h
      unfold nxtPos
      simp only [Fin.val_castAdd] at h ⊢
      split_ifs <;> omega
    · simp
  · refine Finset.sum_congr rfl fun i _ => ?_
    have hi := i.2
    have hw : ∀ j, wA ρ k s (Fin.natAdd ρ (Fin.castAdd t i)) j = if i.1 + 1 < k then (if s then 1 else 0) else 0 := by
      intro j
      unfold wA
      rw [if_neg (by simp)]
      simp only [Fin.val_natAdd, Fin.val_castAdd, add_assoc, add_lt_add_iff_left]
    simp only [hw]
    by_cases h : i.1 + 1 < k
    · simp only [if_pos h]
      rw [Finset.sum_eq_single ⟨ρ + i.1 + 1, by omega⟩]
      · rw [if_pos]
        · cases s
          · simp
          · simp only [if_true, Int.cast_one, one_mul]
            rfl
        · refine Or.inl ⟨rfl, ?_, ?_⟩ <;> simp only [Fin.val_natAdd, Fin.val_castAdd] <;> omega
      · intro j _ hj
        rw [if_neg]
        intro h
        apply hj
        apply Fin.ext
        unfold symEdge at h
        simp only [Fin.val_natAdd, Fin.val_castAdd] at h ⊢
        omega
      · simp
    · simp [if_neg h]

section Core

open Formalism.L2.SG.HidaSetting PI.UnitaryDimensionFormula.unitaryCongruence
open scoped TensorProduct

theorem flagV_e {M : Type} [Zero M] {ρ k n : ℕ} (e f : Fin ρ → M) (b : Fin k → M) (z : M) (a : Fin ρ)
    (l : Fin n) (hl : l.1 = nxtPos ρ k a.1) : flagV ρ k n e f b z l = nxt e z a := by
  unfold flagV nxt
  unfold nxtPos at hl
  by_cases h : a.1 + 1 < ρ
  · rw [if_pos h] at hl
    rw [dif_pos (by omega), dif_pos h]
    congr 1
    exact Fin.ext hl
  · rw [if_neg h] at hl
    rw [dite_eq_right (by omega), dite_eq_right (by omega), dif_pos hl, dite_eq_right h]

theorem flagV_b {M : Type} [Zero M] {ρ k n : ℕ} (e f : Fin ρ → M) (b : Fin k → M) (z : M) (i : Fin k)
    (l : Fin n) (hl : l.1 = ρ + i.1) : flagV ρ k n e f b z l = b i := by
  have := i.2
  unfold flagV
  rw [dite_eq_right (by omega), dif_pos (by omega)]
  congr 1
  exact Fin.ext (by simp only; omega)

theorem flagV_apply {M κ : Type} [Zero M] [Zero κ] {ρ k n : ℕ} (φ : M → κ) (e f : Fin ρ → M) (b : Fin k → M) (z : M)
    (c : ℕ → κ) (h0 : φ 0 = 0) (he : ∀ a, φ (e a) = c a.1) (hb : ∀ i, φ (b i) = c (ρ + i.1)) (hz : φ z = 0)
    (hf : ∀ a, φ (f a) = 0) (hc : ∀ m, ρ + k ≤ m → c m = 0) (l : Fin n) : φ (flagV ρ k n e f b z l) = c l.1 := by
  unfold flagV
  split_ifs with h1 h2 h3 h4
  · exact he _
  · rw [hb]; congr 1; simp only; omega
  · rw [hz, hc _ h3.ge]
  · rw [hf, hc _ (by omega)]
  · rw [h0, hc _ (by omega)]

theorem restrictedBlock_self_apply {κ : Type} [CommRing κ] {n : ℕ} (hr : n ≤ n) (u : GL (Fin n) κ) (i j : Fin n) :
    (upperLeftBlock hr u).val i j = u.val i j := by
  have hg : u ∈ blockTri (κ := κ) (n := n) (blk2 n) := by
    intro a b hab
    simp [blk2] at hab
  unfold upperLeftBlock
  rw [extendOne_of_mem _ hg]
  rfl

theorem core (I : AutInst) {κ : Type} [CommRing κ] (π : IntAf I.F I.E →+* κ) {g : ℕ} (hg : (g : κ) = 0)
    {ρ k r : ℕ} (hn : I.n = r) (hle : r ≤ I.n) (hr : ρ + k < r)
    (e f : Fin ρ → VA I) (z : VA I) (b bd : Fin k → VA I) (ew : I.E ⊗[I.F] Af I.F)
    (hint : (∀ a, e a ∈ I.Lf ∧ f a ∈ I.Lf) ∧ z ∈ I.Lf ∧ ∀ i, b i ∈ I.Lf ∧ bd i ∈ I.Lf)
    (hgram : ∀ a c, ZMod' I g (hA I (e a) (e c)) ∧ ZMod' I g (hA I (f a) (f c)) ∧
      ZMod' I g (hA I (e a) (f c) - if a = c then 1 else 0))
    (hz : ∀ a, ZMod' I g (hA I (e a) z) ∧ ZMod' I g (hA I (f a) z))
    (hW : ∀ i, ZMod' I g (hA I z (b i)) ∧ ZMod' I g (hA I z (bd i)) ∧
      ∀ a, ZMod' I g (hA I (e a) (b i)) ∧ ZMod' I g (hA I (f a) (b i)) ∧
        ZMod' I g (hA I (e a) (bd i)) ∧ ZMod' I g (hA I (f a) (bd i)))
    (hew : ew ∈ IntAf I.F I.E) (hbd : ∀ i, bd i = sigA I ew • bd i)
    (hdual : ∀ i j, ZMod' I g (hA I (bd i) (b j) - if i = j then ew else 0))
    (s : Bool) (hs1 : s = true → π ⟨ew, hew⟩ = 1) (hs0 : s = false → π ⟨ew, hew⟩ = 0)
    (β : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) (hβ : ∀ x, x ∈ I.Lf ↔ ∀ i, ((β⁻¹).val *ᵥ x) i ∈ IntAf I.F I.E)
    (w : Fin I.n → VA I)
    (hw1 : s = true → w = flagV ρ k I.n e f b z) (hw0 : s = false → w = flagV ρ k I.n e f (fun i => bd (Fin.rev i)) z)
    (hred : ∀ i j, ∃ hm : ((β⁻¹).val *ᵥ w j) i ∈ IntAf I.F I.E, π ⟨_, hm⟩ = if i = j then 1 else 0)
    (y : GL (Fin I.n) (IntAf I.F I.E)) (M : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F))
    (hM : M = β.val * y.val.map (IntAf I.F I.E).subtype * (β⁻¹).val) :
    resOf π ((∑ a, hA I (f a) (M *ᵥ nxt e z a)) +
      ∑ i : Fin k, if hi : i.1 + 1 < k then hA I (bd i) (M *ᵥ b ⟨i.1 + 1, hi⟩) else 0) =
    ∑ i : Fin r, ∑ j : Fin r, if symEdge ρ k i j then ((wA ρ k s i j : ℤ) : κ) *
      (upperLeftBlock hle (Formalism.UG.bc π y)).val i j else 0 := by
  subst hn
  refine Eq.trans ?_ (sum_symEdge hr s fun i j => (upperLeftBlock hle (Formalism.UG.bc π y)).val i j).symm
  simp only [restrictedBlock_self_apply]
  have hML : ∀ v ∈ I.Lf, M *ᵥ v ∈ I.Lf := by
    intro v hv
    rw [hβ] at hv ⊢
    intro i
    rw [hM, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul,
      ← Matrix.mulVec_mulVec]
    rw [Matrix.mulVec, dotProduct]
    exact Subring.sum_mem _ fun m _ => Subring.mul_mem _ (y.val i m).2 (hv m)
  have hnx : ∀ a, nxt e z a ∈ I.Lf := fun a => by
    unfold nxt
    split_ifs
    · exact (hint.1 _).1
    · exact hint.2.1
  have Z0 : ∀ {x}, ZMod' I g x → resOf π x = 0 := fun {x} hx => by
    rw [← resOf_zero π]
    exact resOf_of_cong π hg (zero_mem _) (by rw [sub_zero]; exact hx)
  have Z0' : ∀ {u v}, ZMod' I g (hA I u v) → resOf π (hA I v u) = 0 := fun {u v} hx => by
    rw [hA_symm]; exact Z0 (Z_sig I g hx)
  have hA0 : ∀ u, resOf π (hA I u 0) = 0 := fun u => by
    rw [← hL_apply, map_zero, resOf_zero]
  have gen : ∀ u ∈ I.Lf, ∀ p : Fin I.n, (∀ l, resOf π (hA I u (w l)) = if l.1 = p.1 then 1 else 0) →
      ∀ j, resOf π (hA I u (M *ᵥ w j)) = (Formalism.UG.bc π y).val p j := by
    intro u hu p hp j
    have := resOf_frame π (hL I u) β (fun v hv => hA_int I hu ((hβ v).2 hv)) w hred y.val j
    rw [← hM] at this
    simp only [hL_apply, hp, Fin.val_inj, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
      if_true] at this
    exact this
  have hfe : ∀ a c, resOf π (hA I (f a) (e c)) = if c.1 = a.1 then 1 else 0 := by
    intro a c
    have h1 := Z_sig I g (hgram c a).2.2
    rw [map_sub, ← hA_symm] at h1
    by_cases hca : c = a
    · rw [if_pos hca, map_one] at h1
      rw [if_pos (congrArg Fin.val hca), ← resOf_one π]
      exact resOf_of_cong π hg (one_mem _) h1
    · rw [if_neg hca, map_zero, sub_zero] at h1
      rw [if_neg fun h => hca (Fin.ext h)]
      exact Z0 h1
  have hF : ∀ a l, resOf π (hA I (f a) (w l)) = if l.1 = a.1 then 1 else 0 := by
    intro a l
    have ha := a.2
    have key : ∀ b' : Fin k → VA I, (∀ i, resOf π (hA I (f a) (b' i)) = 0) →
        resOf π (hA I (f a) (flagV ρ k I.n e f b' z l)) = if l.1 = a.1 then 1 else 0 := fun b' hb' =>
      flagV_apply (fun v => resOf π (hA I (f a) v)) e f b' z (fun m => if m = a.1 then 1 else 0) (hA0 _) (hfe a)
        (fun i => by rw [hb', if_neg (by omega)]) (Z0 (hz a).2) (fun c => Z0 (hgram a c).2.1)
        (fun m hm => if_neg (by omega)) l
    cases s
    · rw [hw0 rfl]; exact key _ fun i => Z0 ((hW _).2.2 a).2.2.2
    · rw [hw1 rfl]; exact key _ fun i => Z0 ((hW _).2.2 a).2.1
  have hwe : ∀ a : Fin ρ, nxt e z a = w ⟨nxtPos ρ k a.1, (nxtPos_le ρ k a.1).trans_lt hr⟩ := by
    intro a
    cases s
    · rw [hw0 rfl]; exact (flagV_e _ _ _ _ a _ rfl).symm
    · rw [hw1 rfl]; exact (flagV_e _ _ _ _ a _ rfl).symm
  have m1 : ∀ a, hA I (f a) (M *ᵥ nxt e z a) ∈ IntAf I.F I.E := fun a => hA_int I (hint.1 a).2 (hML _ (hnx a))
  have m2 : ∀ i : Fin k, (if hi : i.1 + 1 < k then hA I (bd i) (M *ᵥ b ⟨i.1 + 1, hi⟩) else 0) ∈ IntAf I.F I.E := by
    intro i
    split_ifs
    · exact hA_int I (hint.2.2 i).2 (hML _ (hint.2.2 _).1)
    · exact zero_mem _
  rw [resOf_add π (sum_mem fun a _ => m1 a) (sum_mem fun i _ => m2 i), resOf_sum π _ _ m1, resOf_sum π _ _ m2]
  congr 1
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [hwe a]
    exact gen _ (hint.1 a).2 ⟨a.1, by have := a.2; omega⟩ (hF a) _
  · refine Finset.sum_congr rfl fun i _ => ?_
    have hi' := i.2
    by_cases hi : i.1 + 1 < k
    · rw [dif_pos hi, if_pos hi]
      cases s
      · rw [hbd i, hA_smul_left, sigA_sigA,
          resOf_mul π hew (hA_int I (hint.2.2 i).2 (hML _ (hint.2.2 _).1)), resOf_of_mem π hew, hs0 rfl, zero_mul]
        simp
      · rw [if_pos rfl]
        have hb : b ⟨i.1 + 1, hi⟩ = w ⟨ρ + i.1 + 1, by omega⟩ := by
          rw [hw1 rfl]; exact (flagV_b _ _ _ _ _ _ rfl).symm
        rw [hb]
        refine gen _ (hint.2.2 i).2 ⟨ρ + i.1, by omega⟩ (fun l => ?_) _
        rw [hw1 rfl]
        refine flagV_apply (fun v => resOf π (hA I (bd i) v)) e f b z (fun m => if m = ρ + i.1 then 1 else 0) (hA0 _)
          (fun a => ?_) (fun j => ?_) (Z0' (hW i).2.1) (fun c => Z0' ((hW i).2.2 c).2.2.2)
          (fun m hm => if_neg (by omega)) l
        · have := a.2
          rw [if_neg (by omega)]
          exact Z0' ((hW i).2.2 a).2.2.1
        · have h1 := hdual i j
          by_cases hij : i = j
          · rw [if_pos hij] at h1
            rw [if_pos (by rw [hij]), ← hs1 rfl, ← resOf_of_mem π hew]
            exact resOf_of_cong π hg hew h1
          · rw [if_neg hij, sub_zero] at h1
            rw [if_neg fun h => hij (Fin.ext (by omega))]
            exact Z0 h1
    · rw [dite_eq_right hi, if_neg hi, resOf_zero]

end Core

theorem transport {I I' : AutInst} (h : I = I') {ρ k : ℕ}
    (P : ∀ I : AutInst, (Fin ρ → Formalism.L2.SG.HidaSetting.VA I) → (Fin ρ → Formalism.L2.SG.HidaSetting.VA I) → Formalism.L2.SG.HidaSetting.VA I →
      (Fin k → Formalism.L2.SG.HidaSetting.VA I) → (Fin k → Formalism.L2.SG.HidaSetting.VA I) → TensorProduct I.F I.E (Af I.F) → Prop)
    (e f : Fin ρ → Formalism.L2.SG.HidaSetting.VA I) (z : Formalism.L2.SG.HidaSetting.VA I) (b bd : Fin k → Formalism.L2.SG.HidaSetting.VA I)
    (ew : TensorProduct I.F I.E (Af I.F)) (hP : P I e f z b bd ew) :
    P I' (cast (congrArg (fun I : AutInst => Fin ρ → Formalism.L2.SG.HidaSetting.VA I) h) e)
      (cast (congrArg (fun I : AutInst => Fin ρ → Formalism.L2.SG.HidaSetting.VA I) h) f)
      (cast (congrArg (fun I : AutInst => Formalism.L2.SG.HidaSetting.VA I) h) z)
      (cast (congrArg (fun I : AutInst => Fin k → Formalism.L2.SG.HidaSetting.VA I) h) b)
      (cast (congrArg (fun I : AutInst => Fin k → Formalism.L2.SG.HidaSetting.VA I) h) bd)
      (cast (congrArg (fun I : AutInst => TensorProduct I.F I.E (Af I.F)) h) ew) := by
  subst h; exact hP

theorem cast_hA {I I' : AutInst} (h : I = I') (x y : Formalism.L2.SG.HidaSetting.VA I') :
    cast (congrArg (fun I : AutInst => TensorProduct I.F I.E (Af I.F)) h)
      (Formalism.L2.SG.HidaSetting.hA I (cast (congrArg (fun I : AutInst => Formalism.L2.SG.HidaSetting.VA I) h.symm) x)
        (cast (congrArg (fun I : AutInst => Formalism.L2.SG.HidaSetting.VA I) h.symm) y)) = Formalism.L2.SG.HidaSetting.hA I' x y := by
  subst h; rfl

theorem hT_eq {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (x y : Fin (Yc D 0).rank → EAf D) :
    hT X h x y = Formalism.L2.SG.HidaSetting.hA (Formalism.L2.SG.InstExistsPf.instOf D) x y := cast_hA h x y

theorem resS_of_cpt {D : D7} (PP : Pl D.host.E) {c : EAf D} (hc : c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (hcc : c * c = c) : (GlobalTheory.StdFrames.cpt PP c = 1 → resS D.host.F PP ⟨c, hc⟩ = 1) ∧
      (GlobalTheory.StdFrames.cpt PP c ≠ 1 → resS D.host.F PP ⟨c, hc⟩ = 0) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← sub_eq_zero, ← map_one (resS D.host.F PP), ← RingHom.map_sub]
    refine (GlobalTheory.AdIsom.resS_eq_zero_iff_cpt PP _).2 ?_
    rw [AddSubgroupClass.coe_sub, RingHom.map_sub]
    simp [h]
  · have h0 : GlobalTheory.StdFrames.cpt PP c * (GlobalTheory.StdFrames.cpt PP c - 1) = 0 := by
      rw [mul_sub, ← RingHom.map_mul, hcc, mul_one, sub_self]
    have h1 : GlobalTheory.StdFrames.cpt PP c = 0 := (mul_eq_zero.1 h0).resolve_right (sub_ne_zero.2 h)
    exact (GlobalTheory.AdIsom.resS_eq_zero_iff_cpt PP _).2 (by simp [h1])


open Formalism.L2.SG.HidaSetting in
theorem resT_argT : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → ∀ β : GL (Fin (Yc D 0).rank) (EAf D), IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → (∀ PP ∈ R.Pg, RedIs β PP (flagAt X h PP)) → ∀ PP ∈ R.Pg, ∀ κ : GA D (Yc D 0), finE (Yc D 0) κ ∈ St β → GlobalTheory.SeeConjChar.resT PP (GlobalTheory.SeeConjChar.argT X h (finE (Yc D 0) κ)) = ∑ i, ∑ j, if symEdge D.R.rS D.R.k i j then ((GlobalTheory.SeeConjChar.wA D.R.rS D.R.k (GlobalTheory.SeeConjChar.sideAt X h PP) i j : ℤ) : kP PP) * ((upperLeftBlock (r_le_Y (D := D) 0) (redFn β PP (finE (Yc D 0) κ)) : GL (Fin D.R.r) (kP PP)).val i j) else 0 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h hLev _ β hF hred PP hPP κ hκ
  obtain ⟨y, hy⟩ := hκ
  rw [← hy, redFn_frGL]
  have hg : ((X.B.g : ℕ) : kP PP) = 0 := by
    rw [X.g_eq, ← map_natCast (Ideal.Quotient.mk PP.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
    exact (places_over_g R hLev).1 PP hPP
  have hn : (Formalism.L2.SG.InstExistsPf.instOf D).n = D.R.r := h ▸ X.n_eq
  have hr : D.R.rS + D.R.k < D.R.r := by
    have := D.R.two_le_m
    unfold Ranks.r Ranks.rS
    omega
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := transport h (fun I e f z b bd ew =>
    ((∀ a, e a ∈ I.Lf ∧ f a ∈ I.Lf) ∧ z ∈ I.Lf ∧ ∀ i, b i ∈ I.Lf ∧ bd i ∈ I.Lf) ∧
    (∀ a c, ZMod' I X.B.g (hA I (e a) (e c)) ∧ ZMod' I X.B.g (hA I (f a) (f c)) ∧
      ZMod' I X.B.g (hA I (e a) (f c) - if a = c then 1 else 0)) ∧
    (∀ a, ZMod' I X.B.g (hA I (e a) z) ∧ ZMod' I X.B.g (hA I (f a) z)) ∧
    (∀ i, ZMod' I X.B.g (hA I z (b i)) ∧ ZMod' I X.B.g (hA I z (bd i)) ∧
      ∀ a, ZMod' I X.B.g (hA I (e a) (b i)) ∧ ZMod' I X.B.g (hA I (f a) (b i)) ∧
        ZMod' I X.B.g (hA I (e a) (bd i)) ∧ ZMod' I X.B.g (hA I (f a) (bd i))) ∧
    ew ∈ IntAf I.F I.E ∧ (∀ i, bd i = sigA I ew • bd i) ∧
    (∀ i j, ZMod' I X.B.g (hA I (bd i) (b j) - if i = j then ew else 0)) ∧ ew * ew = ew)
    X.e0 X.f0 X.z0 X.bw X.bwd X.ew
    ⟨X.vectorsInLattice, X.gramIntegral, X.formsAtZero.2, X.weightVectorsIntegral, X.ew_int, X.bwd_w, X.bw_dual, X.ew_idem⟩
  have hc := resS_of_cpt (D := D) PP (c := ewT X h) h5 h8
  have hβ : ∀ x, x ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf ↔ ∀ i, ((β⁻¹).val *ᵥ x) i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    intro x
    rw [GlobalTheory.SeeMatchOnto.Lf_eq]
    exact hF x
  have main := core (Formalism.L2.SG.InstExistsPf.instOf D) (resS D.host.F PP) hg hn (r_le_Y (D := D) 0) hr
    (e0T X h) (f0T X h) (z0T X h) (bwT X h) (bwdT X h) (ewT X h) h1 h2 h3 h4 h5 h6 h7 (sideAt X h PP)
    (fun hs => hc.1 (of_decide_eq_true hs)) (fun hs => hc.2 (of_decide_eq_false hs)) β hβ (flagAt X h PP)
    (fun hs => if_pos (of_decide_eq_true hs)) (fun hs => if_neg (of_decide_eq_false hs)) (hred PP hPP) y
    (frGL β y).val rfl
  unfold argT
  simp only [hT_eq]
  exact main

end GlobalTheory.SeeResAt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ResidueLevelCharacterArgumentAtTypePlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residue_levelCharacterArgument_at_typePlace : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → ∀ β : GL (Fin (Yc D 0).rank) (EAf D), IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → (∀ PP ∈ R.Pg, RedIs β PP (flagAt X h PP)) → ∀ PP ∈ R.Pg, ∀ κ : GA D (Yc D 0), finE (Yc D 0) κ ∈ St β → GlobalTheory.SeeConjChar.resT PP (GlobalTheory.SeeConjChar.argT X h (finE (Yc D 0) κ)) = ∑ i, ∑ j, if symEdge D.R.rS D.R.k i j then ((GlobalTheory.SeeConjChar.wA D.R.rS D.R.k (GlobalTheory.SeeConjChar.sideAt X h PP) i j : ℤ) : kP PP) * ((upperLeftBlock (r_le_Y (D := D) 0) (redFn β PP (finE (Yc D 0) κ)) : GL (Fin D.R.r) (kP PP)).val i j) else 0 := by
  first | exact @GlobalTheory.SeeResAt.resT_argT | exact GlobalTheory.SeeResAt.resT_argT | (intros; apply GlobalTheory.SeeResAt.resT_argT <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddCharEqMulShiftUnitOfIsFieldStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddCharEqMulShiftUnitOfIsField
namespace GlobalTheory.Twist

theorem addChar_eq_mulShift_unit_of_isField :
    ∀ {κf : Type} [CommRing κf] [Finite κf], IsField κf → ∀ ψ φ : AddChar κf ℂ, ψ ≠ 1 → φ ≠ 1 →
      ∃ c : κfˣ, ∀ t, φ t = ψ ((c : κf) * t) := by
  intro κf _ _ hF ψ φ hψ _
  classical
  let _ : Field κf := hF.toField
  have _ : Fintype κf := Fintype.ofFinite κf

  have hinj : Function.Injective ψ.mulShift :=
    AddChar.to_mulShift_inj_of_isPrimitive (AddChar.IsPrimitive.of_ne_one hψ)

  have hbij : Function.Bijective ψ.mulShift :=
    (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, AddChar.card_eq.symm⟩
  obtain ⟨a, ha⟩ := hbij.2 φ
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact ‹φ ≠ 1› (by rw [← ha, AddChar.mulShift_zero])
  refine ⟨Units.mk0 a ha0, fun t => ?_⟩
  rw [← ha, AddChar.mulShift_apply, Units.val_mk0]

end GlobalTheory.Twist
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_addChar_eq_mulShift_of_isField : ∀ {κf : Type} [CommRing κf] [Finite κf], IsField κf → ∀ ψ φ : AddChar κf ℂ, ψ ≠ 1 → φ ≠ 1 → ∃ c : κfˣ, ∀ t, φ t = ψ ((c : κf) * t) := by
  first | exact @GlobalTheory.Twist.addChar_eq_mulShift_unit_of_isField | exact GlobalTheory.Twist.addChar_eq_mulShift_unit_of_isField | (intros; apply GlobalTheory.Twist.addChar_eq_mulShift_unit_of_isField <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjCharacterEqProdSymmetricEdgeCharacters
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

theorem GlobalTheory.SeeConjChar.conjCharacter_eq_prod_symmetricEdge_characters : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → ∀ β : GL (Fin (Yc D 0).rank) (EAf D), IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → (∀ PP ∈ R.Pg, RedIs β PP (flagAt X h PP)) → ∃ (ψ' : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ) (a : ∀ PP : Pl D.host.E, Fin D.R.r → Fin D.R.r → (kP PP)ˣ), IsGenericPsi R.Pg ψ' ∧ ∀ κ : GA D (Yc D 0), finE (Yc D 0) κ ∈ St β → ((iotaX X h).toMulEquiv κ).2 ∈ X.K2 → star (X.chi2 ((iotaX X h).toMulEquiv κ).2) = ∏ PP ∈ R.Pg, ψ' PP (∑ i, ∑ j, if symEdge D.R.rS D.R.k i j then (a PP i j : kP PP) * ((upperLeftBlock (r_le_Y (D := D) 0) (redFn β PP (finE (Yc D 0) κ)) : GL (Fin D.R.r) (kP PP)).val i j) else 0) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h hIs hGrp β hβ hred
  classical
  obtain ⟨ψ, hψ, hdec⟩ := GlobalTheory.T.levelCharacter_on_stabilizer_eq_prod_residue_characters_alt R F X h hIs hGrp
  have hc : ∀ PP ∈ R.Pg, ∃ c : (kP PP)ˣ, ∀ t, ψ (GlobalTheory.IdemSupport.cP PP) (GlobalTheory.SeeConjChar.conjRes PP t) = ψ PP ((c : kP PP) * t) := by
    intro PP hP
    refine GlobalTheory.T.exists_unit_addChar_eq_mulShift_of_isField ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 PP.isMaximal) (ψ PP)
      ((ψ (GlobalTheory.IdemSupport.cP PP)).compAddMonoidHom (GlobalTheory.SeeConjChar.conjRes PP).toAddMonoidHom) (hψ PP hP).1 ?_
    intro h1
    apply (hψ PP hP).2
    ext t
    obtain ⟨s, rfl⟩ := (GlobalTheory.SeeConjChar.conjRes PP).surjective t
    have := congrArg (fun χ : AddChar (kP PP) ℂ => χ s) h1
    simpa using this
  choose! c hc using hc
  refine ⟨fun PP => (ψ PP).mulShift (-1), fun PP i j =>
    if (i.1 < D.R.rS ∨ (i.1 + 1 < D.R.rS + D.R.k ∧ GlobalTheory.SeeConjChar.sideAt X h PP = true)) then 1
    else if i.1 = D.R.rS + D.R.k then c PP else -c PP, ?_, ?_⟩
  · intro PP hP h1
    apply (hψ PP hP).1
    ext t
    have := congrArg (fun χ : AddChar (kP PP) ℂ => χ (-t)) h1
    simpa [AddChar.mulShift_apply] using this
  · intro κ hS hK2
    have hK : ((iotaX X h).toMulEquiv κ).2 ∈ X.B.I.Kset := (Formalism.L2.SG.Closed.level_subgroup_properties X).2.1 _ hK2
    rw [hdec κ hK, ← starRingEnd_apply, map_prod]
    refine Finset.prod_congr rfl fun PP hP => ?_
    rw [GlobalTheory.T.residue_levelCharacterArgument_at_typePlace R F X h hIs hGrp β hβ hred PP hP κ hS, GlobalTheory.T.residue_conjugatePlace_characterArgument_signedSum R F X h hIs hGrp β hβ hred PP hP κ hS hK2, hc PP hP,
      map_mul, ← AddChar.map_neg_eq_conj, ← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul, AddChar.mulShift_apply]
    congr 1
    rw [Finset.mul_sum, ← neg_add, ← Finset.sum_add_distrib, neg_one_mul]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with hE
    · unfold GlobalTheory.SeeConjChar.wA GlobalTheory.SeeConjChar.wB
      simp only [apply_ite (fun u : (kP PP)ˣ => (u : kP PP)), Units.val_one, Units.val_neg]
      split_ifs <;> first | (exfalso; tauto) | (push_cast; ring1) | omega | (simp_all <;> omega)
    · simp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjCharacterEqProdSymmetricEdgeCharactersStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjCharacter_eq_prod_symmetricEdge_characters_alt : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → ∀ β : GL (Fin (Yc D 0).rank) (EAf D), IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → (∀ PP ∈ R.Pg, RedIs β PP (flagAt X h PP)) → ∃ (ψ' : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ) (a : ∀ PP : Pl D.host.E, Fin D.R.r → Fin D.R.r → (kP PP)ˣ), IsGenericPsi R.Pg ψ' ∧ ∀ κ : GA D (Yc D 0), finE (Yc D 0) κ ∈ St β → ((iotaX X h).toMulEquiv κ).2 ∈ X.K2 → star (X.chi2 ((iotaX X h).toMulEquiv κ).2) = ∏ PP ∈ R.Pg, ψ' PP (∑ i, ∑ j, if symEdge D.R.rS D.R.k i j then (a PP i j : kP PP) * ((upperLeftBlock (r_le_Y (D := D) 0) (redFn β PP (finE (Yc D 0) κ)) : GL (Fin D.R.r) (kP PP)).val i j) else 0) := by
  first | exact @GlobalTheory.SeeConjChar.conjCharacter_eq_prod_symmetricEdge_characters | exact GlobalTheory.SeeConjChar.conjCharacter_eq_prod_symmetricEdge_characters | (intros; apply GlobalTheory.SeeConjChar.conjCharacter_eq_prod_symmetricEdge_characters <;> assumption)
end
