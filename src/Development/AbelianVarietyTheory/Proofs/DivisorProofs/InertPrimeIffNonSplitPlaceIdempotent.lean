module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformizationLawsOfGoodDeepCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzSeminormL2BoundStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilTransportArchimedeanSliceSobolevBounds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalFiniteDimensionalFinitePartsWeilTrans
public import Development.AbelianVarietyTheory.Definitions.Divisors.P22
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupDeterminantPowDepthBounds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWeilFunctionalLocalUniqueness
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMomentMatrixTransform
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.WtSubOneLe

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPrimeIffNonSplitPlaceIdempotent
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPrimeIffNonSplitPlaceIdempotent
open NumberField MeasureTheory IsDedekindDomain
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.BotClassDict (finQ)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.InertPlace

open GlobalTheory.IdemSupport

theorem inertQ_iff_cP {D : D7} {q : ℕ} (hq : q.Prime) (P : HeightOneSpectrum (𝓞 D.host.E))
    (hqP : (q : 𝓞 D.host.E) ∈ P.asIdeal) : Formalism.MainNotions.StandardLatticesGL3.InertQ D q ↔ cP P = P := by
  constructor
  · intro hI
    exact ((isConjPl_iff P P).1 (GlobalTheory.XiSplit.isConjPl_of_smul_eq (hI P.asIdeal P.isPrime P.ne_bot hqP))).symm
  · intro hc
    by_contra h
    exact GlobalTheory.NormSum.VacInt.conj_smul_ne D hq h P.asIdeal P.isPrime hqP
      (GlobalTheory.XiSplit.smul_eq_of_isConjPl ((isConjPl_iff P P).2 hc.symm))

theorem nonSplitAt_iff_cP {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {η : AF D.host.F}
    (hη : IsPlaceIdem D v η) (P : HeightOneSpectrum (𝓞 D.host.E)) (hP : P.under (𝓞 D.host.F) = v) :
    GlobalTheory.WeilParts.NonSplitAt D v η ↔ cP P = P := by
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  obtain ⟨h0, h1, h2⟩ := place_comp hΦ hη
  constructor
  · rintro ⟨-, hns⟩
    by_contra hc
    obtain ⟨e, f, h⟩ := exists_isPrimeIdem hΦ P
    obtain ⟨hd, ε, hε, hf⟩ := of_isPrimeIdem hΦ h
    rw [hP] at hε
    have hεη := placeIdem_unique hε hη
    subst hεη
    rcases h with ⟨h, rfl⟩ | ⟨rfl, -, -⟩
    · exact hns ⟨e, h.1, hf⟩
    · have hd' := delta_conj hΦ hd
      rw [hf, cA_algebraMap, ← hf] at hd'
      have := hd'.2.2 P (Ne.symm hc)
      rw [hd.2.1] at this
      exact one_ne_zero this
  · intro hc
    refine ⟨hη, ?_⟩
    rintro ⟨e, ⟨ee, ec, -⟩, hs⟩
    have he : e * algebraMap (AF D.host.F) (AE D) η = e := by
      rw [← hs, mul_add, ee, ec, add_zero]
    have hi : infPart D e = 0 := by
      rw [← he, RingHom.map_mul, h0, mul_zero]
    have hout : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), Q ≠ P → Φ e Q = 0 := by
      intro Q hQ
      have hQv : Q.under (𝓞 D.host.F) ≠ v := by
        intro hv
        rcases eq_or_eq_cP (hv.trans hP.symm) with h | h
        · exact hQ h
        · exact hQ (h.trans hc)
      rw [← he, ev_mul, h2 Q hQv, mul_zero]
    have hPP : Φ e P * Φ e P = Φ e P := by rw [← ev_mul, ee]
    have h01 : Φ e P = 0 ∨ Φ e P = 1 := by
      have : Φ e P * (Φ e P - 1) = 0 := by rw [mul_sub, hPP, mul_one, sub_self]
      rcases mul_eq_zero.1 this with h | h
      · exact Or.inl h
      · exact Or.inr (sub_eq_zero.1 h)
    rcases h01 with h | h
    · have e0 : e = 0 := by
        refine hΦ.ext e hi (FiniteAdeleRing.ext _ fun Q => ?_)
        by_cases hQ : Q = P
        · subst hQ; rw [h]; rfl
        · rw [hout Q hQ]; rfl
      have := h1 P hP
      rw [← hs, e0, map_zero, add_zero, ev_zero] at this
      exact zero_ne_one this
    · have hd : IsDelta Φ P e := ⟨hi, h, hout⟩
      have hd' := delta_conj hΦ hd
      rw [hc] at hd'
      have hce := delta_unique hΦ hd' hd
      rw [hce, ee] at ec
      rw [ec, ev_zero] at h
      exact zero_ne_one h

theorem inertQ_iff_nonSplitAt : ∀ (D : D7) (q : ℕ), q.Prime → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (η : AF D.host.F), IsPlaceIdem D v η →
    (q : 𝓞 D.host.F) ∈ v.asIdeal → (Formalism.MainNotions.StandardLatticesGL3.InertQ D q ↔ GlobalTheory.WeilParts.NonSplitAt D v η) := by
  intro D q hq v η hη hqv
  have := v.isPrime
  obtain ⟨Q, hQ, hl⟩ := (Ideal.nonempty_primesOver v.asIdeal (S := 𝓞 D.host.E)).some
  let P : HeightOneSpectrum (𝓞 D.host.E) := ⟨Q, hQ, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩
  have hP : P.under (𝓞 D.host.F) = v := HeightOneSpectrum.ext hl.over.symm
  have hqP : (q : 𝓞 D.host.E) ∈ P.asIdeal := by
    have h : (q : 𝓞 D.host.F) ∈ (P.under (𝓞 D.host.F)).asIdeal := by rw [hP]; exact hqv
    change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (q : 𝓞 D.host.F) ∈ P.asIdeal at h
    rwa [map_natCast] at h
  rw [inertQ_iff_cP hq P hqP, nonSplitAt_iff_cP hη P hP]

end GlobalTheory.InertPlace
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPrimeIffNonSplitPlaceIdempotentStatement
open NumberField MeasureTheory IsDedekindDomain
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.BotClassDict (finQ)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPrime_iff_nonSplitPlaceIdempotent : ∀ (D : D7) (q : ℕ), q.Prime → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (η : AF D.host.F), IsPlaceIdem D v η →
  (q : 𝓞 D.host.F) ∈ v.asIdeal → (Formalism.MainNotions.StandardLatticesGL3.InertQ D q ↔ GlobalTheory.WeilParts.NonSplitAt D v η) := by
  first | exact @GlobalTheory.InertPlace.inertQ_iff_nonSplitAt | exact GlobalTheory.InertPlace.inertQ_iff_nonSplitAt | (intros; apply GlobalTheory.InertPlace.inertQ_iff_nonSplitAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleSplittingPairIdentity
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleSplittingPairIdentity
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.DblScal.LocAt

theorem liftV_one_mul' {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (b : AF F) :
    GlobalTheory.LatVac.liftV v 1 * b = GlobalTheory.LatVac.liftV v (evFin F v b) := by
  refine Prod.ext ?_ ?_
  · exact zero_mul _
  · change GlobalTheory.AdelicU.singleFin v 1 * b.2 = GlobalTheory.AdelicU.singleFin v (evFin F v b)
    apply GlobalTheory.AdelicU.af_ext
    intro w
    rw [map_mul]
    by_cases hw : w = v
    · subst hw
      rw [GlobalTheory.AdelicU.evalV_singleFin_self, GlobalTheory.AdelicU.evalV_singleFin_self, one_mul]
      rfl
    · rw [GlobalTheory.AdelicU.evalV_singleFin_ne hw, GlobalTheory.AdelicU.evalV_singleFin_ne hw, zero_mul]

theorem schr_trans' {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) {κ : Type} [Fintype κ]
    (w : κ → AF F) (Φ : (κ → AF F) → ℂ) : GlobalTheory.WeilM.schr ψ (w, 0) Φ = fun y => Φ (y + w) := by
  funext y
  simp [GlobalTheory.WeilM.schr]

theorem acts_of_comm {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))
    (ψ : AddChar (AF F) ℂ) (hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) (T : Module.End ℂ ((κ → AF F) → ℂ))
    (hkeep : ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, T Φ ∈ GlobalTheory.WeilM.schA F κ)
    (hunit : ∀ μ : @MeasureTheory.Measure (κ → AF F) (borel _),
      @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∫⁻ y, ‖T Φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖Φ y‖ₑ ^ 2 ∂μ)
    (hcomm : ∀ u : AF F, evFin F v u = 0 → ∀ p q : κ → AF F, ∀ Φ ∈ GlobalTheory.WeilM.schA F κ,
      T (GlobalTheory.WeilM.schr ψ (u • p, u • q) Φ) = GlobalTheory.WeilM.schr ψ (u • p, u • q) (T Φ))
    (φ : (κ → Fv F v) → ℂ) (hφ : φ ∈ GlobalTheory.WeilM.SB (κ → Fv F v)) :
    ∃ φ₁ ∈ GlobalTheory.WeilM.SB (κ → Fv F v), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) T φ φ₁ := by
  have hfib := GlobalTheory.T.isometry_commuting_heisenberg_acts_fibrewise v ψ T hstd (GlobalTheory.T.standardAdelicAddChar_nontrivial_finitePlace ψ hstd) hkeep hunit hcomm
  have htr : ∀ u : AF F, evFin F v u = 0 → ∀ p : κ → AF F,
      ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, T (fun y => Φ (y + u • p)) = fun y => T Φ (y + u • p) := by
    intro u hu p Φ hΦ
    have h := hcomm u hu p 0 Φ hΦ
    rw [smul_zero, schr_trans', schr_trans'] at h
    exact h
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction κ v
  refine ⟨(R 0)⁻¹ • fun t => T (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ R) (fun i => GlobalTheory.LatVac.liftV v (t i)), ?_, ?_⟩
  · exact (GlobalTheory.WeilM.SB _).smul_mem (R 0)⁻¹ (GlobalTheory.T.adelicSchwartz_restrict_finitePlace_mem_schwartzBruhat v _ (hkeep _ (hR φ hφ).2))
  · intro r hr
    funext y
    set u : AF F := 1 - GlobalTheory.LatVac.liftV v 1 with hudef
    have hu : evFin F v u = 0 := by simp [hudef, GlobalTheory.LatVac.evFin_liftV]
    set p : κ → AF F := fun i => GlobalTheory.LatVac.liftV v (evFin F v (y i)) with hpdef
    have hyp : y + u • (-y) = p := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, hudef, hpdef]
      rw [← liftV_one_mul']
      ring
    have hpat : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) p := by
      intro u' hu'
      funext i
      exact GlobalTheory.LatVac.at_liftV v _ u' hu'
    set Φ₀ := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ R with hΦ₀
    set Φ₁ := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ r with hΦ₁
    set Φ₂ : (κ → AF F) → ℂ := (r y / R 0) • (fun w => Φ₀ (w + u • (-y))) with hΦ₂
    have hm₀ : Φ₀ ∈ GlobalTheory.WeilM.schA F _ := (hR φ hφ).2
    have hm₂ : Φ₂ ∈ GlobalTheory.WeilM.schA F _ := Submodule.smul_mem _ _ (GlobalTheory.T.adelicSchwartzSpace_translate_mem_of_mem _ _ hm₀)
    have hfz : ∀ z, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z → (Φ₁ - Φ₂) (y + z) = 0 := by
      intro z hz
      have e1 : r (y + z) = r y := hr.1 y z hz
      have e2 : y + z + u • (-y) = p + z := by rw [← hyp]; abel
      have hpz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) (p + z) := fun u' hu' => by
        rw [smul_add, hpat u' hu', hz u' hu', add_zero]
      have e3 : R (p + z) = R 0 := by simpa using (hR φ hφ).1 0 (p + z) hpz
      have e4 : (fun i => evFin F v ((y + z + u • (-y)) i)) = fun i => evFin F v ((y + z) i) := by
        funext i
        simp [hu]
      simp only [Pi.sub_apply, hΦ₂, hΦ₁, hΦ₀, Pi.smul_apply, smul_eq_mul, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens]
      rw [e4, e2, e3, e1]
      field_simp
      ring
    have h0 := hfib (Φ₁ - Φ₂) (sub_mem hr.2 hm₂) y hfz
    rw [map_sub, Pi.sub_apply, sub_eq_zero] at h0
    have h2 : T Φ₂ y = (r y / R 0) * T Φ₀ p := by
      rw [hΦ₂, map_smul, htr u hu (-y) Φ₀ hm₀, Pi.smul_apply, smul_eq_mul, hyp]
    rw [h0, h2]
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, hpdef, Pi.smul_apply, smul_eq_mul]
    field_simp

end GlobalTheory.DblScal.LocAt

namespace GlobalTheory.DblScal.LocAt

theorem locOps : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (dd : GlobalTheory.DblScal.DblCo σ X W) (omd : GlobalTheory.DblScal.DblRep σ (n := n) W),
      IsUSplitting (adeleClass F) B.ψ dd (actB (cA σ)) omd → ∀ v : Pl (F := F), GlobalTheory.DblScal.LocOps omd v := by
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP dd omd hS v g hg φ hφ
  refine acts_of_comm v B.ψ hP.base.std (omd g) (fun Φ hΦ => hS.pres g Φ hΦ)
    (fun μ hμ Φ hΦ => hS.unit μ hμ g Φ hΦ) ?_ φ hφ
  intro u hu p q Φ hΦ
  set w := dd.e.symm (p, q) with hw
  have he : dd.e (u • w) = (u • p, u • q) := by
    rw [LinearEquiv.map_smul, hw, LinearEquiv.apply_symm_apply, Prod.smul_mk]
  let G : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E) := ((g : GL (Fin d ⊕ Fin d) (AE F E)) : Matrix _ _ _)
  have h2 : u • (G - 1) = 0 := hg u hu
  have e2 : (u • w) * G.transpose = u • w := by
    have : (u • w) * G.transpose - u • w = w * (u • (G - 1)).transpose := by
      rw [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.transpose_sub, Matrix.transpose_one,
        Matrix.mul_sub, Matrix.mul_one, smul_sub]
    rw [h2, Matrix.transpose_zero, Matrix.mul_zero, sub_eq_zero] at this
    exact this
  have hact : actB (cA σ) g (u • w) = u • w := e2
  have h3 := hS.impl g (u • w) Φ hΦ
  simp only [GlobalTheory.WeilM.Darboux.rho, he, hact] at h3
  exact h3

end GlobalTheory.DblScal.LocAt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleSplittingPairIdentityStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.double_splitting_pair_identity : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (dd : GlobalTheory.DblScal.DblCo σ X W) (omd : GlobalTheory.DblScal.DblRep σ (n := n) W),
      IsUSplitting (adeleClass F) B.ψ dd (actB (cA σ)) omd → ∀ v : Pl (F := F), GlobalTheory.DblScal.LocOps omd v := by
  first | exact @GlobalTheory.DblScal.LocAt.locOps | exact GlobalTheory.DblScal.LocAt.locOps | (intros; apply GlobalTheory.DblScal.LocAt.locOps <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumTransportArchimedeanSliceSchwartzBounds
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationDarbouxCoordinatesStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_representation_darboux_coordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (ψ : AddChar (AF F) ℂ) (m n : ℕ) (JA : Matrix (Fin m) (Fin m) E) (JB : Matrix (Fin n) (Fin n) E) (ξ : AF F ⊗[F] E) (κ : Type) [Fintype κ]
    (co : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ξ ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB)) κ)
    (om : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) × UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB) →* Module.End ℂ ((κ → AF F) → ℂ)),
    (∀ p w, ∀ φ ∈ schA F κ, om p (co.rho ψ w φ) = co.rho ψ (actAB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) p w) (om p φ)) →
    ∃ M : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) × UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB) → ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) →ₗ[ℝ] ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)),
      (∀ p h, ∀ φ ∈ schA F κ,
        om p (schr ψ (GlobalTheory.WeilL2Words.archPair F (M p h)) φ) = schr ψ (GlobalTheory.WeilL2Words.archPair F h) (om p φ)) ∧
      ∀ h, Continuous fun p => M p h := by
  first | exact @GlobalTheory.ArchTransportDir.archDir_transport | exact GlobalTheory.ArchTransportDir.archDir_transport | (intros; apply GlobalTheory.ArchTransportDir.archDir_transport <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStandardArchimedeanAddCharOfIsStandardTraceAde
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStandardArchimedeanAddCharOfIsStandardTraceAde
noncomputable section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.WeilL2Words.StdArch

theorem supportedAtArchimedean_adeleOfMixedSpaceComponent (F : Type) [Field F] [NumberField F] (z : mixedEmbedding.mixedSpace F) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (GlobalTheory.WeilL2Words.arch1 F z) := by
  intro u hu
  have h : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.1 hu
  refine Prod.ext ?_ ?_
  · change u.1 * _ = 0
    rw [h, zero_mul]
  · exact mul_zero u.2

theorem evI_arch1 (F : Type) [Field F] [NumberField F] (z : mixedEmbedding.mixedSpace F) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (GlobalTheory.WeilL2Words.arch1 F z) = z :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply z

theorem isStdInf_of_isStd : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → GlobalTheory.WeilL2Words.IsStdInf F ψ := by
  intro F _ _ ψ hψ
  refine ⟨-(Algebra.trace ℝ (mixedEmbedding.mixedSpace F)), fun z hz => ?_, fun z => ?_⟩
  · by_contra h
    push_neg at h
    exact hz (GlobalTheory.ArchUniq.Coord.eq_zero_of_trace z fun b => by
      have := h b
      rw [LinearMap.neg_apply, neg_eq_zero] at this
      exact this)
  · rw [hψ.2.2 _ (supportedAtArchimedean_adeleOfMixedSpaceComponent F z), evI_arch1]
    simp only [LinearMap.neg_apply, Complex.ofReal_neg]
    ring_nf

end GlobalTheory.WeilL2Words.StdArch

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStandardArchimedeanAddCharOfIsStandardTraceAdeStatement
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isStandardArchimedeanAddChar_of_isStandardTraceAdelic : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → GlobalTheory.WeilL2Words.IsStdInf F ψ := by
  first | exact @GlobalTheory.WeilL2Words.StdArch.isStdInf_of_isStd | exact GlobalTheory.WeilL2Words.StdArch.isStdInf_of_isStd | (intros; apply GlobalTheory.WeilL2Words.StdArch.isStdInf_of_isStd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumTransportArchimedeanSliceSchwartzBounds
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical

theorem GlobalTheory.WeilContF.slice_bounds : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.IsHeckeCharF χT →
        Formalism.IndefR.DatumF.ResEtaF χS nS → Formalism.IndefR.DatumF.ResEtaF χT nT →
        ∀ ω : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ JT →* Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS nT → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
        ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
          ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
          ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
            (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
              co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
            ∀ om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ),
              GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ω om → ∀ Φ ∈ schA F κ, ∀ (y : κ → FiniteAdeleRing (𝓞 F) F) p0 (k n : ℕ), ∃ C : ℝ,
      ∀ᶠ p in nhds p0, ∀ x : κ → mixedEmbedding.mixedSpace F,
        ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun x => om p Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x‖ ≤ C := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hσ χS χT cS cT rS rT ω hω JA JB ξ hJA hJB κ _ co hco om htr Φ hΦ y p0 k n
  haveI : BorelSpace (κ → mixedEmbedding.mixedSpace F) := Pi.borelSpace
  haveI : MeasurableAdd (mixedEmbedding.mixedSpace F) := ContinuousAdd.measurableAdd
  haveI : (MeasureTheory.volume : MeasureTheory.Measure (κ → mixedEmbedding.mixedSpace F)).IsAddHaarMeasure :=
    MeasureTheory.Measure.pi.isAddHaarMeasure _
  have hI := GlobalTheory.T.transportedWeilDatum_CM_preserves_schwartz_heisenberg F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσ χS χT cS cT rS rT ω hω JA JB ξ hJA hJB κ co hco om htr
  have hU := GlobalTheory.T.isUnitaryOn_weilDatum_transport_adelicSchwartz F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσ χS χT cS cT rS rT ω hω JA JB ξ hJA hJB κ co hco om htr
  obtain ⟨M, himpl, hM⟩ := GlobalTheory.T.weil_representation_darboux_coordinates F E σ B.ψ nT nS JA JB ξ κ co om hI.2
  obtain ⟨μ, hμ, hiso⟩ := GlobalTheory.T.weil_representation_l2_isometry F κ om hI.1 hU
  have hfin := GlobalTheory.T.exists_local_finiteDimensional_finite_parts_weil_transport F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσ χS χT cS cT rS rT ω hω JA JB ξ hJA hJB κ co hco om htr Φ hΦ p0
  obtain ⟨N, C, hC, hsob⟩ := GlobalTheory.T.schwartz_seminorm_l2_bound (MeasureTheory.volume : MeasureTheory.Measure (κ → mixedEmbedding.mixedSpace F)) k n
  choose Bd hBd using fun i j => GlobalTheory.WeilL2Words.slice_l2_of (GlobalTheory.T.isStandardArchimedeanAddChar_of_isStandardTraceAdelic F B.ψ hB.std) om hI.1 M himpl hM μ hμ hiso hΦ p0 hfin y i j
  have hev : ∀ᶠ p in nhds p0, ∀ i ∈ Finset.range (N + 1), ∀ j ∈ Finset.range (N + 1),
      ∫ x, (‖x‖ ^ i * ‖iteratedFDeriv ℝ j (fun x => om p Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x‖) ^ 2 ≤ Bd i j :=
    (Filter.eventually_all_finset _).2 fun i _ => (Filter.eventually_all_finset _).2 fun j _ => hBd i j
  refine ⟨C * Real.sqrt (∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1), Bd i j), ?_⟩
  filter_upwards [hev] with p hp x
  obtain ⟨s, hs⟩ := GlobalTheory.WeilCont.exists_slice F (hI.1 p Φ hΦ) y
  have hfs : (fun x => om p Φ (GlobalTheory.WeilCont.adeleJoin F x y)) = ⇑s := funext fun x => (hs x).symm
  rw [hfs] at hp ⊢
  refine (hsob s x).trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) hC)
  exact Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hp i hi j hj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumTransportArchimedeanSliceSchwartzBoundsStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilDatumTransport_archimedeanSlice_schwartz_bounds : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.IsHeckeCharF χT →
        Formalism.IndefR.DatumF.ResEtaF χS nS → Formalism.IndefR.DatumF.ResEtaF χT nT →
        ∀ ω : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ JT →* Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS nT → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
        ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
          ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
          ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
            (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
              co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
            ∀ om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ),
              GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ω om → ∀ Φ ∈ schA F κ, ∀ (y : κ → FiniteAdeleRing (𝓞 F) F) p0 (k n : ℕ), ∃ C : ℝ,
      ∀ᶠ p in nhds p0, ∀ x : κ → mixedEmbedding.mixedSpace F,
        ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun x => om p Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x‖ ≤ C := by
  first | exact @GlobalTheory.WeilContF.slice_bounds | exact GlobalTheory.WeilContF.slice_bounds | (intros; apply GlobalTheory.WeilContF.slice_bounds <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorDepthBetweenZeroAndBound
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupDeterminantPowDepthEqZeroOfLtPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupDeterminantPowDepthEqZeroOfLtPrime
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.FGDepth

theorem val_natCast_nonneg {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) (n : ℕ) :
    0 ≤ v (n : C) := by
  induction n with
  | zero => simp
  | succ n ih =>
    push_cast
    exact (le_min ih (le_of_eq (AddValuation.map_one v).symm)).trans (AddValuation.map_add v _ _)

theorem val_intCast_nonneg {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) (n : ℤ) :
    0 ≤ v (n : C) := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · rw [Int.cast_natCast]
    exact val_natCast_nonneg v m
  · rw [Int.cast_neg, AddValuation.map_neg, Int.cast_natCast]
    exact val_natCast_nonneg v m

theorem val_natCast_eq_zero {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) (p : ℕ)
    (hp : p.Prime) (hv : v (p : C) = 1) (n : ℕ) (hn : ¬ p ∣ n) : v (n : C) = 0 := by
  have h0 := val_natCast_nonneg v n
  refine le_antisymm ?_ h0
  by_contra hlt
  rw [not_le] at hlt
  have hb := Nat.gcd_eq_gcd_ab p n
  rw [((Nat.Prime.coprime_iff_not_dvd hp).2 hn).gcd_eq_one, Nat.cast_one] at hb
  have key : (1 : C) = (p : C) * (Nat.gcdA p n : C) + (n : C) * (Nat.gcdB p n : C) := by
    have := congrArg (fun z : ℤ => (z : C)) hb
    push_cast at this
    exact this
  have one_pos' : (0 : WithTop ℝ) < 1 := by exact_mod_cast (zero_lt_one : (0 : ℝ) < 1)
  have h1 : 0 < v ((p : C) * (Nat.gcdA p n : C)) := by
    rw [AddValuation.map_mul, hv]
    exact add_pos_of_pos_of_nonneg one_pos' (val_intCast_nonneg v _)
  have h2 : 0 < v ((n : C) * (Nat.gcdB p n : C)) := by
    rw [AddValuation.map_mul]
    exact add_pos_of_pos_of_nonneg hlt (val_intCast_nonneg v _)
  have hsum := AddValuation.map_add v ((p : C) * (Nat.gcdA p n : C)) ((n : C) * (Nat.gcdB p n : C))
  rw [← key, AddValuation.map_one] at hsum
  exact absurd hsum (not_le.2 (lt_min h1 h2))

end GlobalTheory.FGDepth

namespace GlobalTheory.FGDepth

theorem detDepth_eq_zero_of_lt : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ), p.Prime → v (p : C) = 1 → ∀ (i d c : ℕ) (G : LogFGL v d) (u : Fin i → Fin d → C), IsSatFrame v u → c < p → detDepth G u c = 0 := by
  intro C _ _ v p hp hv i d c G u hu hc
  obtain ⟨hlo, hcont, -⟩ := GlobalTheory.T.formalGroupDeterminantPowDepth_bounds C v p hp hv i d c G u hu
  obtain ⟨-, -, hone, hrow⟩ := GlobalTheory.T.matrixVariablesDeterminantPow_monomial_shape C i c
  set α₀ : (Σ _ : Fin i, Fin i) →₀ ℕ := ∑ a : Fin i, Finsupp.single ⟨a, a⟩ c with hα₀
  have hmem : α₀ ∈ (detPow C i c).support := by
    rw [MvPolynomial.mem_support_iff, hone]
    exact one_ne_zero
  have hfact : v (mfact α₀ : C) = 0 := by
    have hcast : (mfact α₀ : C) = ((α₀.prod fun _ n => n.factorial : ℕ) : C) := by
      unfold mfact
      rw [Nat.cast_finsuppProd]
    rw [hcast]
    apply val_natCast_eq_zero v p hp hv
    intro hdvd
    rw [Finsupp.prod] at hdvd
    obtain ⟨x, -, hx⟩ := (Prime.dvd_finsetProd_iff hp.prime _).1 hdvd
    rw [hp.dvd_factorial] at hx
    obtain ⟨b, a⟩ := x
    have hle : α₀ ⟨b, a⟩ ≤ c := by
      rw [← (hrow α₀ hmem).1 a]
      exact Finset.single_le_sum (f := fun b' => α₀ ⟨b', a⟩) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ b)
    omega
  have hle : content v (detPow C i c) ≤ 0 := by
    unfold content
    refine (iInf₂_le α₀ hmem).trans (le_of_eq ?_)
    rw [hone, one_mul, hfact]
    rfl
  exact le_antisymm (hcont.trans hle) hlo

end GlobalTheory.FGDepth
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupDeterminantPowDepthEqZeroOfLtPrimeStatement
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalGroupDeterminantPowDepth_eq_zero_of_lt_prime : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ), p.Prime → v (p : C) = 1 → ∀ (i d c : ℕ) (G : LogFGL v d) (u : Fin i → Fin d → C), IsSatFrame v u → c < p → detDepth G u c = 0 := by
  first | exact @GlobalTheory.FGDepth.detDepth_eq_zero_of_lt | exact GlobalTheory.FGDepth.detDepth_eq_zero_of_lt | (intros; apply GlobalTheory.FGDepth.detDepth_eq_zero_of_lt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorDepthBetweenZeroAndBound
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)

namespace GlobalTheory.RefSum

theorem facBetween_zero_boundAll : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c), ∀ (f : Lt1 Dw) (k : ℕ), FacBetween Xo la f k 0 (boundAll p (rk f) k) ∧ (k < p → FacBetween Xo la f k 0 0) := by
  intro E _ _ _ H Dw l Xo c p _ la f k
  letI := H.starRing
  have hch : ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), Nonempty (IntegralChartA3 Xo c T io y) :=
    fun T io y => by
      obtain ⟨C, -⟩ := (@GlobalTheory.IntChartExists.intChart_exists E _ _ _ H Dw l Xo c H.starRing).2.2 (fun _ => rfl) T io y
      exact ⟨C⟩
  have hB : ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p),
      0 ≤ nuFacC Ch X f k ∧ nuFacC Ch X f k ≤ ((boundAll p (rk f) k : ℝ) : EReal) ∧ (k < p → nuFacC Ch X f k = 0) := by
    intro T io y Ch X
    have h1 := GlobalTheory.T.formalGroupDeterminantPowDepth_bounds X.C (vX_vp X) p Fact.out (vX_vp_p X) (rk f) _ k (fgl Ch X) (frame Ch X f)
      (isSatFrame_frame Ch X f)
    refine ⟨h1.1, ?_, fun hk => GlobalTheory.T.formalGroupDeterminantPowDepth_eq_zero_of_lt_prime X.C (vX_vp X) p Fact.out (vX_vp_p X) (rk f) _ k (fgl Ch X) (frame Ch X f)
      (isSatFrame_frame Ch X f) hk⟩
    have h2 := h1.2.2
    unfold boundAll
    exact h2
  have hmain : ∀ B : ℝ, (∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y)
      (X : ValExt T p), nuFacC Ch X f k ≤ (B : EReal)) → FacBetween Xo la f k 0 B := by
    intro B hb T io e ho y
    refine ⟨?_, fun _ => ?_⟩
    · rw [EReal.coe_zero]
      exact le_nuFac fun Ch X => (hB T io y Ch X).1
    · obtain ⟨Ch⟩ := hch T io y
      obtain ⟨X⟩ := nonempty_valExt_of_overLa la ho
      exact (nuFac_le Ch X f k).trans (hb T io y Ch X)
  refine ⟨hmain _ fun T io y Ch X => (hB T io y Ch X).2.1, fun hk => hmain 0 fun T io y Ch X => ?_⟩
  rw [(hB T io y Ch X).2.2 hk, EReal.coe_zero]

end GlobalTheory.RefSum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorDepthBetweenZeroAndBoundStatement
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.factorDepth_between_zero_and_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c), ∀ (f : Lt1 Dw) (k : ℕ), FacBetween Xo la f k 0 (boundAll p (rk f) k) ∧ (k < p → FacBetween Xo la f k 0 0) := by
  first | exact @GlobalTheory.RefSum.facBetween_zero_boundAll | exact GlobalTheory.RefSum.facBetween_zero_boundAll | (intros; apply GlobalTheory.RefSum.facBetween_zero_boundAll <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSupportedRuleOfFlagComponentSection
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSupportedRuleOfFlagComponentSection
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)}

theorem exists_j_of_mem_flagOpen (X : FlagCover Y) {y : X.YY} (hy : y ∈ flagOpen X) :
    ∃ x : Xo.XF c, X.π y = Y.j x := by
  obtain ⟨w, rfl⟩ := (opensRange_inc X).ge hy
  refine ⟨(pullback.snd X.π Y.j) w, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]

theorem j_mem_closure_iff {s : Set (Xo.XF c)} (hs : IsClosed s) (x : Xo.XF c) :
    Y.j x ∈ closure (Y.j '' s) ↔ x ∈ s :=
  Set.ext_iff.1 (Y.j.isOpenEmbedding.isOpenMap.preimage_closure_image Y.j.isOpenEmbedding.injective Y.j.continuous _ hs) x

section Ext

variable (X : FlagCover Y) (Z : Comp Xo c)

def openOn : X.YY.Opens := flagOpen X ⊓ X.π ⁻¹ᵁ barComp Y Z

def openOff : X.YY.Opens :=
  flagOpen X ⊓ X.π ⁻¹ᵁ ⟨(closure (Y.j '' (Z : Set (Xo.XF c))))ᶜ, isClosed_closure.isOpen_compl⟩

theorem flagOpen_le_sup : flagOpen X ≤ openOn X Z ⊔ openOff X Z := fun y hy => by
  obtain ⟨x, hx⟩ := exists_j_of_mem_flagOpen X hy
  by_cases hZ : x ∈ (Z : Set (Xo.XF c))
  · refine Or.inl ⟨hy, ?_⟩
    show X.π y ∈ barComp Y Z
    rw [hx]; exact (j_mem_barComp Z x).2 hZ
  · refine Or.inr ⟨hy, ?_⟩
    show X.π y ∉ closure (Y.j '' (Z : Set (Xo.XF c)))
    rw [hx, j_mem_closure_iff (isClosed_of_mem_irreducibleComponents _ Z.2)]
    exact hZ

theorem not_mem_openOn_openOff {y : X.YY} (h₁ : y ∈ openOn X Z) (h₂ : y ∈ openOff X Z) : False := by
  obtain ⟨x, hx⟩ := exists_j_of_mem_flagOpen X h₁.1
  have a : X.π y ∈ barComp Y Z := h₁.2
  have b : X.π y ∉ closure (Y.j '' (Z : Set (Xo.XF c))) := h₂.2
  rw [hx] at a b
  exact b (subset_closure ⟨x, (j_mem_barComp Z x).1 a, rfl⟩)

end Ext

section Glue

variable {X : FlagCover Y} {Z : Comp Xo c} {e : Ix Dw → ℤ}

theorem exists_extZero (m : H0 (str₀ X Z) (LL₀ X Z e) (U₀ X Z)) :
    ∃ m' : H0 (flagStr X) (X.LL e) (flagOpen X),
      H0.pull (inc₀ X Z) le_rfl m' = m ∧ ∀ (S : Type) [CommRing S] (x : Sp S ⟶ X.YY) (k : X.F.J)
        (hO : ⊤ ≤ x ⁻¹ᵁ flagOpen X) (hk : ⊤ ≤ x ⁻¹ᵁ X.F.U k), ⊤ ≤ x ⁻¹ᵁ openOff X Z →
        H0.val (B := X.LL e) x k hO hk m' = 0 := by
  have hiso : IsoOver (inc₀ X Z) (openOn X Z) := isoOver_of_isOpenImmersion _ (by
    rw [Scheme.Opens.opensRange_ι]; exact inf_le_right)
  have e₁ : U₀ X Z ≤ inc₀ X Z ⁻¹ᵁ openOn X Z := fun z hz => ⟨hz, z.2⟩
  have e₂ : inc₀ X Z ⁻¹ᵁ openOn X Z ≤ U₀ X Z := fun z hz => hz.1
  obtain ⟨m₁, hm₁⟩ := (hiso.bijective_pull (p := flagStr X) (X.F.isLB_LL e) e₁ e₂).2 m
  let W : Bool → X.YY.Opens := fun b => Bool.rec (openOff X Z) (openOn X Z) b
  have hW : ∀ b, W b ≤ flagOpen X := fun b => by cases b <;> exact inf_le_left
  have hc : flagOpen X ≤ iSup W := fun y hy => by
    rcases flagOpen_le_sup X Z hy with h | h
    · exact Opens.mem_iSup.2 ⟨true, h⟩
    · exact Opens.mem_iSup.2 ⟨false, h⟩
  let s : ∀ b, H0 (flagStr X) (X.LL e) (W b) := fun b => Bool.rec (motive := fun b => H0 (flagStr X) (X.LL e) (W b)) 0 m₁ b
  obtain ⟨m', hm'⟩ := GlobalTheory.LB.exists_mod_of_cover (F := GlobalTheory.LB.toMod (X.LL e)) W hW hc s (by
    rintro (_ | _) (_ | _)
    · rfl
    · exact H0.ext_germ (p := flagStr X) fun y hy => (not_mem_openOn_openOff X Z hy.2 hy.1).elim
    · exact H0.ext_germ (p := flagStr X) fun y hy => (not_mem_openOn_openOff X Z hy.1 hy.2).elim
    · rfl)
  have r₁ : H0.restr (p := flagStr X) (hW true) m' = m₁ := hm' true
  have r₂ : H0.restr (p := flagStr X) (hW false) m' = 0 := hm' false
  refine ⟨m', ?_, fun S _ x k hO hk hx => ?_⟩
  · have h₃ : H0.pull (p := flagStr X) (inc₀ X Z) e₁ (H0.restr (p := flagStr X) (hW true) m') =
        H0.pull (p := flagStr X) (inc₀ X Z) le_rfl m' := H0.pull_restr _ _ _ _
    rw [r₁] at h₃
    exact h₃.symm.trans hm₁
  · have a := GlobalTheory.TangentOrigin.evalPt_res x (inf_le_inf_right _ (hW false)) (GlobalTheory.FlagMod.le_preimage_inf hO hk)
      (GlobalTheory.FlagMod.le_preimage_inf hx hk) (H0.loc (p := flagStr X) m' k)
    refine a.symm.trans ?_
    change H0.val (B := X.LL e) x k hx hk (H0.restr (p := flagStr X) (hW false) m') = 0
    rw [r₂, map_zero]

end Glue

theorem exists_suppOn_sec₀_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (X : FlagCover Y) (Z : Comp Xo c) (e : Ix Dw → ℤ) (m : H0 (str₀ X Z) (LL₀ X Z e) (U₀ X Z)), ∃ f : GlobalTheory.AllWt.secZ Xo c e, (f : Rul Xo c) ∈ GlobalTheory.AllWt.suppOn Z ∧ sec₀ X Z e f = m := by
  intro E _ _ _ H Dw l Xo c Y X Z e m
  obtain ⟨m', h₁, h₂⟩ := exists_extZero m
  refine ⟨(secOf X e).symm m', ?_, ?_⟩
  · intro S _ _ y hy
    have hv : FlagCover.val (toSecO m') y = 0 := by
      refine (FlagCover.IsVal.eq_val fun S' _ _ ψ P' hP k hz Q t hQ ht => ?_).symm
      have hO := FlagMod.le_preimage_map (z := X.pt P') X.inc (top_le_inc X) le_top
      rw [map_zero, coef_toSecO _ _ _ _ hO, h₂ _ _ _ _ _ ?_, mul_zero]
      intro s _
      refine ⟨hO (Set.mem_univ s), ?_⟩
      show X.π ((X.pt P' ≫ X.inc) s) ∉ closure (Y.j '' (Z : Set (Xo.XF c)))
      rw [FlagCover.pt_inc, ← Scheme.Hom.comp_apply, (X.lies_ptY P').1, Scheme.Hom.comp_apply,
        j_mem_closure_iff (isClosed_of_mem_irreducibleComponents _ Z.2), ← FlagMod.frX_frMap hP,
        Scheme.Hom.comp_apply]
      exact hy _
    change evR Xo c (FlagCover.toRule (toSecO m')) y = 0
    by_cases hT : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y
    · rw [FlagCover.evR_toRule _ y hT, hv]
    · unfold evR evalAt
      rw [dite_eq_right hT]
  · show H0.pull (inc₀ X Z) le_rfl ((secOf X e) ((secOf X e).symm m')) = m
    rw [LinearEquiv.apply_symm_apply]
    exact h₁

end GlobalTheory.CompHS
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSupportedRuleOfFlagComponentSectionStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_supportedRule_of_flagComponentSection : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (X : FlagCover Y) (Z : Comp Xo c) (e : Ix Dw → ℤ) (m : H0 (str₀ X Z) (LL₀ X Z e) (U₀ X Z)), ∃ f : GlobalTheory.AllWt.secZ Xo c e, (f : Rul Xo c) ∈ GlobalTheory.AllWt.suppOn Z ∧ sec₀ X Z e f = m := by
  first | exact @GlobalTheory.CompHS.exists_suppOn_sec₀_eq | exact GlobalTheory.CompHS.exists_suppOn_sec₀_eq | (intros; apply GlobalTheory.CompHS.exists_suppOn_sec₀_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearModelUnitaryIntertwines
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearModelUnitaryIntertwines
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open GlobalTheory.LatVac GlobalTheory.MixedForm
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.SplitScalX

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl (F := F)}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

theorem lin_zero_basis (h : IsCMExt F E σ) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (χX χW : Chr F E)
    (om : Rep σ X W) (hW : M.IsWeil ψ χX χW om) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v))
    (ι : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) (Fv F v) → ℂ)) (hι : M.IsLinW ψ t b c ι)
    (g : UA σ X.J) (hg : g ∈ UAt σ X (evFin F v)) (y : (Fv F v)ˣ) (hy : (y : Fv F v) = ((mat g).map (piW (t.comp σ))).det)
    (φ φ₁ : (Fin n × Fin d → Fv F v) → ℂ) (hφ : φ ∈ SB (Fin n × Fin d → Fv F v))
    (hA : Acts (evFin F v) (om (g, 1)) φ φ₁) :
    ι φ₁ 0 = (chrW χW (t.comp σ) y : ℂ) * ((GlobalTheory.SplitWeil.nabs (Fv F v) y ^ ((d : ℝ) / 2) : ℝ) : ℂ) * ι φ 0 := by
  obtain ⟨Λ, hΛ, f, hf, hne⟩ := GlobalTheory.T.exists_translation_invariant_functional F v n d
  obtain ⟨φ₂, hφ₂, rfl⟩ := hι.bij.surjOn hf
  refine form_scalar h M ψ χX χW om hW t (LinearMap.proj 0 ∘ₗ ι) (conjForm (Λ ∘ₗ ι)) (fun w hw φ hφ => ?_)
    (fun w hw φ hφ => ?_) (star φ₂) (star_mem_SB hφ₂) ?_ g hg y hy φ φ₁ hφ hA
  · obtain ⟨u, hu, e1, e2⟩ := exists_at (v := v) M w
    have := hι.mult u hu ((e2 t).trans hw) φ hφ _ (GlobalTheory.SchrSB.schr_mem_SB ψ hψ.1 v _ φ hφ)
      (GlobalTheory.VacBridge.rho_acts_locCo M.co ψ v u hu φ) 0 (fun a _ => smul_zero a) (Matrix.map_zero _ (map_zero _))
    rw [e1] at this
    simpa [symp, hTens] using this
  · obtain ⟨u, hu, e1, e2⟩ := exists_at (v := v) M w
    have := hι.trans u hu ((e2 _).trans hw) _ (star_mem_SB hφ) _ (GlobalTheory.SchrSB.schr_mem_SB ψ hψ.1 v _ _ (star_mem_SB hφ))
      (GlobalTheory.VacBridge.rho_acts_locCo M.co ψ v u hu _)
    rw [e1] at this
    change star (Λ (ι _)) = star (Λ (ι _))
    rw [star_schr (psiAt ψ v) (fun x => GlobalTheory.StdCharFromIsStd.norm_psi hψ _), funext this,
      hΛ _ (hι.bij.mapsTo (star_mem_SB hφ))]
  · change star (Λ (ι (star (star φ₂)))) ≠ 0
    rwa [star_star, star_ne_zero]

theorem chrW_comp_conj (h : IsCMExt F E σ) {K : Subgroup (AF F)ˣ} {χ : Chr F E} {m : ℕ} (hχ : ResEtaPow K χ m)
    (t : E →ₐ[F] Fv F v) (x : (Fv F v)ˣ) : chrW χ (t.comp σ) x = (chrW χ t x)⁻¹ := by
  obtain ⟨ε, e1, e2, e3, e4, e5, e6, e7⟩ := exists_idem h t
  have e8 : piW (t.comp σ) ε = 0 := by simpa [e7] using congrArg (piW (t.comp σ)) e2
  have key : ∀ a a' : Fv F v, a * a' = 1 → (1 + ε * algebraMap (AF F) (AE F E) (liftV v (a - 1))) *
      (1 + ε * algebraMap (AF F) (AE F E) (liftV v (a' - 1))) = 1 := fun a a' haa => by
    have e : liftV v (a - 1) + liftV v (a' - 1) + liftV v (a - 1) * liftV v (a' - 1) = 0 := by
      rw [liftV_mul, evFin_liftV, ← map_add (f := _), ← map_add (f := _), show a - 1 + (a' - 1) + (a - 1) * (a' - 1) = 0 by
        linear_combination haa, map_zero]
    have e' := congrArg (algebraMap (AF F) (AE F E)) e
    rw [map_add (f := _), map_add (f := _), map_mul, map_zero] at e'
    linear_combination ε * e' + algebraMap (AF F) (AE F E) (liftV v (a - 1)) *
      algebraMap (AF F) (AE F E) (liftV v (a' - 1)) * e1
  have hat : ∀ a : Fv F v, At (evFin F v) (1 + ε * algebraMap (AF F) (AE F E) (liftV v a) - 1) := fun a u hu => by
    rw [add_sub_cancel_left, ← mul_smul_comm, Algebra.smul_def, ← map_mul,
      show u * liftV v a = 0 from at_liftV v a u hu, map_zero, mul_zero]
  let z : (AE F E)ˣ := ⟨_, _, key _ _ x.mul_inv, key _ _ x.inv_mul⟩
  have hz : At (evFin F v) ((z : AE F E) - 1) := hat _
  have hzi : At (evFin F v) (((z⁻¹ : (AE F E)ˣ) : AE F E) - 1) := hat _
  have z1 : piW t (z : AE F E) = x := by
    change piW t (1 + _) = _
    rw [map_add (f := _), map_mul, map_one, e5, piW_algebraMap, evFin_liftV]; ring
  have z2 : piW (t.comp σ) (z : AE F E) = 1 := by
    change piW _ (1 + _) = _
    rw [map_add (f := _), map_mul, map_one, e8, zero_mul, add_zero]
  obtain ⟨n1, n2⟩ := GlobalTheory.T.local_norm_unramified_factorization F E σ h v t z hz
  set a : (AF F)ˣ := Units.map (Algebra.norm (AF F) : AE F E →* AF F) z with ha
  have n1' : At (evFin F v) ((a : AF F) - 1) := n1
  have n2' : evFin F v (a : AF F) = x := by rw [← mul_one (x : Fv F v), ← z1, ← z2]; exact n2
  have h1 := hχ a
  rw [if_pos (Subgroup.mem_sup_right (MonoidHom.mem_range.mpr ⟨z, rfl⟩)), Circle.coe_eq_one] at h1
  set A : (AE F E)ˣ := Units.map (algebraMap (AF F) (AE F E) : AF F →* AE F E) a with hA
  have hAv : (A : AE F E) = algebraMap (AF F) (AE F E) a := rfl
  have w0 : At (evFin F v) (((A * z⁻¹ : (AE F E)ˣ) : AE F E) - 1) := fun u hu => by
    have a1 : u • ((A : AE F E) - 1) = 0 := by
      rw [hAv, ← map_one (algebraMap (AF F) (AE F E)), ← map_sub, Algebra.smul_def, ← map_mul,
        show u * ((a : AF F) - 1) = 0 from n1' u hu, map_zero]
    rw [Units.val_mul, show (A : AE F E) * (z⁻¹ : (AE F E)ˣ) - 1 =
      ((A : AE F E) - 1) * (z⁻¹ : (AE F E)ˣ) + ((z⁻¹ : (AE F E)ˣ) - 1) by ring, smul_add, ← smul_mul_assoc, a1,
      hzi u hu, zero_mul, add_zero]
  have zz : ∀ τ : E →ₐ[F] Fv F v, piW τ ((A * z⁻¹ : (AE F E)ˣ) : AE F E) * piW τ (z : AE F E) = x := fun τ => by
    rw [← map_mul, ← Units.val_mul, inv_mul_cancel_right, hAv, piW_algebraMap, n2']
  have w1 : piW t ((A * z⁻¹ : (AE F E)ˣ) : AE F E) = 1 := by
    have := zz t
    rw [z1] at this
    exact (mul_eq_right₀ x.ne_zero).1 this
  have w2 : piW (t.comp σ) ((A * z⁻¹ : (AE F E)ˣ) : AE F E) = x := by
    have := zz (t.comp σ)
    rwa [z2, mul_one] at this
  have c1 := GlobalTheory.T.local_character_norm_one_unit F E σ h χ v t z hz z2
  have c2 := GlobalTheory.T.local_character_norm_one_unit F E σ h χ v (t.comp σ) (A * z⁻¹) w0 (by rw [comp_conj_conj h]; exact w1)
  rw [show Units.map (piW t).toMonoidHom z = x from Units.ext z1] at c1
  rw [show Units.map (piW (t.comp σ)).toMonoidHom (A * z⁻¹) = x from Units.ext w2] at c2
  rw [c1, c2, map_mul, h1, one_mul, map_inv, map_inv]

theorem scalar_left : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)), ∀ ι, M.IsLinW B.ψ t b c ι →
    ∀ κ : UA σ X.J → ℂ, (∀ g ∈ UAt σ X (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v),
      Acts (evFin F v) (om (g, 1)) φ φ₁ → ι φ₁ = κ g • fun Y => ι φ (((locMat t b g)⁻¹ : GL (Fin n) (Fv F v)).val * Y)) →
    ∀ g ∈ UAt σ X (evFin F v), κ g = (chrW χW t (GlobalTheory.SplitFlip.gdet (locMat t b g)) : ℂ) *
      GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet (locMat t b g)) (-(d : ℂ) / 2) := by
  intro hP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hT v t b c ι hι κ hκ g hg
  have h := hT.base.cm
  have hJ : (X.J.map t).det ≠ 0 := by
    obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
    have h0 := GlobalTheory.LeviAtPlace.det_ne_zero_of_sig (hT.herm.sig (InfinitePlace.mk φ))
    have h1 : X.J.det ≠ 0 := fun e => h0 (by
      rw [show X.J.map _ = RingHom.mapMatrix _ X.J from rfl, ← RingHom.map_det, e, map_zero])
    rw [show X.J.map t = (t : E →+* Fv F v).mapMatrix X.J from rfl, ← RingHom.map_det]
    exact (map_ne_zero _).2 h1
  obtain ⟨φ, hφ, e⟩ := hι.bij.surjOn (indicator_intM_mem_SB (k := Fv F v) (R := Fin n) (D := Fin d))
  have hφ0 : ι φ 0 ≠ 0 := by
    rw [e, Set.indicator_of_mem (show (0 : Matrix (Fin n) (Fin d) (Fv F v)) ∈ intM (Fv F v) (Fin n) (Fin d) from
      fun _ _ => zero_mem _)]
    exact one_ne_zero
  set x : (Fv F v)ˣ := GlobalTheory.SplitFlip.gdet (locMat t b g) with hx
  have hx1 : (x : Fv F v) = ((mat g).map (piW t)).det := by
    change (locMat t b g).val.det = _
    rw [locMat_val, Matrix.det_mul, Matrix.det_mul, mul_right_comm, ← Matrix.det_mul, Units.inv_mul, Matrix.det_one,
      one_mul]
  have hx2 : ((x⁻¹ : (Fv F v)ˣ) : Fv F v) = ((mat g).map (piW (t.comp σ))).det := by
    have hu := congrArg Matrix.det (GlobalTheory.Div.CoordOpp.unit_map σ g t)
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, ← hx1, mul_right_comm, mul_eq_right₀ hJ] at hu
    exact Units.inv_eq_of_mul_eq_one_right hu
  obtain ⟨φ₁, ⟨hφ₁, hA⟩, -⟩ := (GlobalTheory.T.theta_action_exists hP F E σ B _ _ _ _ M _ _ om _ _ _ _ hT v).1 g hg 1 (fun u _ => by
      rw [show mat (1 : UA σ W.J) = 1 from rfl, sub_self, smul_zero]) φ hφ
  have k1 := lin_zero_basis h M B.ψ hT.base.std _ _ om hT.weil t b c ι hι g hg _ hx2 φ φ₁ hφ hA
  rw [hκ g hg φ hφ φ₁ hφ₁ hA, chrW_comp_conj h hT.resW, map_inv, inv_inv] at k1
  have k2 : ((GlobalTheory.SplitWeil.nabs (Fv F v) x⁻¹ ^ ((d : ℝ) / 2) : ℝ) : ℂ) = GlobalTheory.SplitFlip.apow x (-(d : ℂ) / 2) := by
    rw [neg_div, ← GlobalTheory.SplitFlip.apow_inv, GlobalTheory.SplitFlip.apow,
      Complex.ofReal_cpow (show 0 ≤ GlobalTheory.SplitWeil.nabs _ _ from NNReal.coe_nonneg _)]
    push_cast
    rfl
  rw [k2] at k1
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.mul_zero] at k1
  exact mul_right_cancel₀ hφ0 k1

end GlobalTheory.SplitScalX

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearModelUnitaryIntertwinesStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linear_model_unitary_intertwines : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)), ∀ ι, M.IsLinW B.ψ t b c ι →
    ∀ κ : UA σ X.J → ℂ, (∀ g ∈ UAt σ X (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v),
      Acts (evFin F v) (om (g, 1)) φ φ₁ → ι φ₁ = κ g • fun Y => ι φ (((locMat t b g)⁻¹ : GL (Fin n) (Fv F v)).val * Y)) →
    ∀ g ∈ UAt σ X (evFin F v), κ g = (chrW χW t (GlobalTheory.SplitFlip.gdet (locMat t b g)) : ℂ) *
      GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet (locMat t b g)) (-(d : ℂ) / 2) := by
  first | exact @GlobalTheory.SplitScalX.scalar_left | exact GlobalTheory.SplitScalX.scalar_left | (intros; apply GlobalTheory.SplitScalX.scalar_left <;> assumption)
end
end
