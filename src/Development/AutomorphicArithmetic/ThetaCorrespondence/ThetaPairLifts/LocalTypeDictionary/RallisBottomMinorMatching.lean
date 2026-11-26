module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTrianglePolynomialFactor
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedSquareLocalMatching
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedSquareThetaIntegralsEq
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaBottomFinitePlaceMatching
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaLiftVanishesOfIrreducibleDefect

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BottomDegreeMatchRealQuotient
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RealQuotientBottomInvariantsEquiv
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem GlobalTheory.RealQuotBot.real_quotient_invariants_equiv : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (A A' WW : HSp D) (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW) (a b : D.what₂.Tau → ℚ)
    (had : A.rank + A'.rank = WW.rank),
    (∀ τ, Formalism.UG.HasSignature (gramAt D A τ) A.rank 0) → (∀ τ, Formalism.UG.HasSignature (gramAt D A' τ) A'.rank 0) →
    (∀ τ, Formalism.UG.HasSignature (gramAt D WW τ) WW.rank 0) →
    (∃ α β, GlobalTheory.SquareComm.IsTriple A A' WW α β ∧ ∀ τ, HasInfExp D α τ (a τ) ∧ HasInfExp D β τ (b τ)) →
  ∀ (Pr : ModuleCat.{0} ℂ) (q : PolF D WW.rank A.rank →ₗ[ℂ] Pr) (q' : PolF D WW.rank A'.rank →ₗ[ℂ] Pr),
    Function.Surjective q → Function.Surjective q' →
    (∀ α β, GlobalTheory.SquareComm.IsTriple A A' WW α β → (∀ τ, HasInfExp D α τ (a τ) ∧ HasInfExp D β τ (b τ)) →
      (∃ ωA ωB Pi rf rl p p', GlobalTheory.SquareComm.IsMatch ψ θ FA FA' FW α β ωA ωB Pi rf rl p p') ∧
      ∀ ωA ωB Pi rf rl p p', GlobalTheory.SquareComm.IsMatch ψ θ FA FA' FW α β ωA ωB Pi rf rl p p' →
        ∃ (Pf : ModuleCat.{0} ℂ) (r : (WO A WW → ℂ) →ₗ[ℂ] Pf) (r' : (WO A' WW → ℂ) →ₗ[ℂ] Pf) (e : Pr ⊗[ℂ] Pf ≃ₗ[ℂ] Pi),
          (∀ x, ∃ f, GlobalTheory.SquareComm.IsFinF ψ θ true FA FW f ∧ r f = x) ∧
          (∀ x, ∃ f, GlobalTheory.SquareComm.IsFinF ψ θ false FA' FW f ∧ r' f = x) ∧
          (∀ f, GlobalTheory.SquareComm.IsFinF ψ θ true FA FW f → ∀ P, p (GlobalTheory.SquareComm.fockF ψ θ true FA FW f P) = e (q P ⊗ₜ r f)) ∧
          ∀ f, GlobalTheory.SquareComm.IsFinF ψ θ false FA' FW f → ∀ P,
            p' (GlobalTheory.SquareComm.fockF ψ θ false FA' FW f P) = e (q' P ⊗ₜ r' f)) →
    Nontrivial Pr ∧ ∃ (n₀ : D.what₂.Tau → ℕ) (σ : (D.what₂.Tau → Matrix (Fin WW.rank) (Fin WW.rank) ℂ) → Module.End ℂ Pr),
    (∀ (g : D.what₂.Tau → Matrix.unitaryGroup (Fin A.rank) ℂ) (P : PolF D WW.rank A.rank),
      q (GlobalTheory.MinorFrame.colSub (fun τ => (g τ : Matrix (Fin A.rank) (Fin A.rank) ℂ)) P) =
        GlobalTheory.MinorFrame.detChar n₀ (fun τ => (g τ : Matrix (Fin A.rank) (Fin A.rank) ℂ)) • q P) ∧
    (∀ (g : D.what₂.Tau → Matrix.unitaryGroup (Fin A'.rank) ℂ) (P : PolF D WW.rank A'.rank),
      q' (GlobalTheory.MinorFrame.colSub (fun τ => (g τ : Matrix (Fin A'.rank) (Fin A'.rank) ℂ)) P) =
        GlobalTheory.MinorFrame.detChar n₀ (fun τ => (g τ : Matrix (Fin A'.rank) (Fin A'.rank) ℂ)) • q' P) ∧
    (∀ (κ : D.what₂.Tau → Matrix.unitaryGroup (Fin WW.rank) ℂ), ∀ P ∈ GlobalTheory.MinorFrame.inv (ι := D.what₂.Tau) A.rank WW.rank n₀,
      q (GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ : Matrix (Fin WW.rank) (Fin WW.rank) ℂ).map (starRingEnd ℂ)) P) =
        σ (fun τ => (κ τ : Matrix (Fin WW.rank) (Fin WW.rank) ℂ)) (q P)) ∧
    (∀ (κ : D.what₂.Tau → Matrix.unitaryGroup (Fin WW.rank) ℂ), ∀ P ∈ GlobalTheory.MinorFrame.inv (ι := D.what₂.Tau) A'.rank WW.rank n₀,
      q' (GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ : Matrix (Fin WW.rank) (Fin WW.rank) ℂ)) P) =
        GlobalTheory.MinorFrame.detChar n₀ (fun τ => (κ τ : Matrix (Fin WW.rank) (Fin WW.rank) ℂ)) • σ (fun τ => (κ τ : Matrix (Fin WW.rank) (Fin WW.rank) ℂ)) (q' P)) := by
  intro hH hP hK hLM D ψ θ hψ hθ A A' WW FA FA' FW a b had hsA hsA' hsW hex Pr q q' hq hq' hfac
  obtain ⟨α, β, hT, hE⟩ := hex
  obtain ⟨⟨ωA, ωB, Pi, rf, rl, p, p', hm⟩, hfac2⟩ := hfac α β hT hE
  obtain ⟨Pf, r, r', e, hr, hr', hpA, hpB⟩ := hfac2 _ _ _ _ _ _ _ hm
  have hPi : Nontrivial Pi := hm.irred.1
  have hall : ¬ ∀ z : Pr ⊗[ℂ] Pf, z = 0 := by
    intro h
    obtain ⟨z, hz⟩ := exists_ne (0 : Pi)
    exact hz (by rw [← e.apply_symm_apply z, h (e.symm z), map_zero])
  have hPr : Nontrivial Pr := by
    by_contra hc
    rw [not_nontrivial_iff_subsingleton] at hc
    exact hall fun z => by
      induction z using TensorProduct.induction_on with
      | zero => rfl
      | tmul x y => rw [Subsingleton.elim x 0, TensorProduct.zero_tmul]
      | add u v hu hv => rw [hu, hv, add_zero]
  have hPf : Nontrivial Pf := by
    by_contra hc
    rw [not_nontrivial_iff_subsingleton] at hc
    exact hall fun z => by
      induction z using TensorProduct.induction_on with
      | zero => rfl
      | tmul x y => rw [Subsingleton.elim y 0, TensorProduct.tmul_zero]
      | add u v hu hv => rw [hu, hv, add_zero]
  obtain ⟨y, hy⟩ := exists_ne (0 : Pf)
  obtain ⟨f, hf, hfy⟩ := hr y
  obtain ⟨f', hf', hfy'⟩ := hr' y
  have hf0 : f ≠ 0 := by rintro rfl; exact hy (by rw [← hfy, map_zero])
  have canc : ∀ x x' : Pr, e (x ⊗ₜ y) = e (x' ⊗ₜ y) → x = x' := by
    intro x x' h
    by_contra hne
    have h2 : (x - x') ⊗ₜ[ℂ] y = 0 := by
      rw [TensorProduct.sub_tmul]; exact sub_eq_zero.2 (e.injective h)
    exact GlobalTheory.RealQuotBot.tmul_ne_zero (sub_ne_zero.2 hne) hy h2
  have sA := fun τ => GlobalTheory.T.diagonalHermitianFrame_signs_pos_of_definite D A FA τ (hsA τ)
  have sA' := fun τ => GlobalTheory.T.diagonalHermitianFrame_signs_pos_of_definite D A' FA' τ (hsA' τ)
  have sW := fun τ => GlobalTheory.T.diagonalHermitianFrame_signs_pos_of_definite D WW FW τ (hsW τ)
  obtain ⟨hTA, hcoA, -⟩ := GlobalTheory.RealQuot.oriented_maps D ψ θ hθ true A WW FA FW β (β / α) ωA b (fun τ => b τ - a τ) hm.weilA
    (fun τ => ⟨(hE τ).2, GlobalTheory.RealQuot.hasInfExp_div D α β τ (a τ) (b τ) (hE τ).1 (hE τ).2⟩) Pi rf rl p hm.mapA
  obtain ⟨hTB, hcoB, -⟩ := GlobalTheory.RealQuot.oriented_maps D ψ θ hθ false A' WW FA' FW α (α / β) ωB a (fun τ => a τ - b τ) hm.weilB
    (fun τ => ⟨(hE τ).1, GlobalTheory.RealQuot.hasInfExp_div D β α τ (b τ) (a τ) (hE τ).2 (hE τ).1⟩) Pi rf rl p' hm.mapB
  obtain ⟨n₀, hn₀⟩ := GlobalTheory.T.definiteBottomTriple_weight_natural D ψ θ A A' WW FA FW a b α β ωA hθ hsA hsW hT hE hm.weilA ⟨f, hf, hf0⟩
  have kA : GlobalTheory.RealQuot.coinv true FA FW (fun τ => b τ - a τ) ≤ LinearMap.ker q := by
    intro P hP
    have h := hcoA f hf P hP
    rw [hpA f hf P, hfy] at h
    rw [LinearMap.mem_ker]
    refine canc _ _ ?_
    rw [h, TensorProduct.zero_tmul, map_zero]
  have kB : GlobalTheory.RealQuot.coinv false FA' FW (fun τ => a τ - b τ) ≤ LinearMap.ker q' := by
    intro P hP
    have h := hcoB f' hf' P hP
    rw [hpB f' hf' P, hfy'] at h
    rw [LinearMap.mem_ker]
    refine canc _ _ ?_
    rw [h, TensorProduct.zero_tmul, map_zero]
  have hrel : ∀ P P', q P = q' P' → ∀ τ, ∀ Y ∈ lieAt WW τ,
      q (GlobalTheory.RealQuot.actT true FA FW b τ Y P) = q' (GlobalTheory.RealQuot.actT false FA' FW a τ Y P') := by
    intro P P' hPP τ Y hY
    have h1 := hTA f hf τ Y hY P
    have h2 := hTB f' hf' τ Y hY P'
    rw [hpA f hf, hpA f hf, hfy] at h1
    rw [hpB f' hf', hpB f' hf', hfy'] at h2
    refine canc _ _ ?_
    rw [h1, h2, hPP]
  have hrow := GlobalTheory.T.definite_bottom_row_transport_contragredient D A A' WW FA FA' FW b a n₀ Pr q q' sA sA' sW
    (fun τ => by
      have hc : ((A.rank : ℚ) + (A'.rank : ℚ)) = (WW.rank : ℚ) := by exact_mod_cast had
      rw [hn₀ τ, hc]) hrel
  have hdet : ∀ κ : D.what₂.Tau → Matrix.unitaryGroup (Fin WW.rank) ℂ,
      GlobalTheory.MinorFrame.detChar n₀ (fun τ => (κ τ : Matrix (Fin WW.rank) (Fin WW.rank) ℂ)) ≠ 0 := by
    intro κ
    unfold GlobalTheory.MinorFrame.detChar
    exact Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ (GlobalTheory.RealQuotBot.det_unitary_ne_zero (κ τ))
  let σ : (D.what₂.Tau → Matrix (Fin WW.rank) (Fin WW.rank) ℂ) → Module.End ℂ Pr := fun κ =>
    if h : LinearMap.ker q ≤ LinearMap.ker (q ∘ₗ (GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ).map (starRingEnd ℂ))).toLinearMap) then
      (LinearMap.ker q).liftQ _ h ∘ₗ (q.quotKerEquivOfSurjective hq).symm.toLinearMap else 0
  have hσ : ∀ (κ : D.what₂.Tau → Matrix.unitaryGroup (Fin WW.rank) ℂ) P,
      σ (fun τ => (κ τ : Matrix (Fin WW.rank) (Fin WW.rank) ℂ)) (q P) =
        q (GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ : Matrix (Fin WW.rank) (Fin WW.rank) ℂ).map (starRingEnd ℂ)) P) := by
    intro κ P
    have hk : LinearMap.ker q ≤ LinearMap.ker (q ∘ₗ (GlobalTheory.MinorFrame.rowSub
        (fun τ => (κ τ : Matrix (Fin WW.rank) (Fin WW.rank) ℂ).map (starRingEnd ℂ))).toLinearMap) := by
      intro P₀ hP₀
      rw [LinearMap.mem_ker] at hP₀ ⊢
      have h := hrow κ P₀ 0 (by rw [hP₀, map_zero])
      rw [map_zero, map_zero] at h
      exact (smul_eq_zero.1 h.symm).resolve_left (hdet κ)
    have e1 : (q.quotKerEquivOfSurjective hq).symm (q P) = Submodule.Quotient.mk P := by
      rw [LinearEquiv.symm_apply_eq, LinearMap.quotKerEquivOfSurjective_apply_mk]
    simp only [σ, dif_pos hk, LinearMap.comp_apply, LinearEquiv.coe_coe, e1, Submodule.liftQ_apply, AlgHom.toLinearMap_apply]
  refine ⟨hPr, n₀, σ, ?_, ?_, ?_, ?_⟩
  · exact GlobalTheory.T.columnSubstitution_unitary_of_kills_lieCoinvariants D true A WW FA FW (fun τ => b τ - a τ) n₀ Pr q sA sW (fun τ => by simp only [if_true]; exact hn₀ τ) kA
  · exact GlobalTheory.T.columnSubstitution_unitary_of_kills_lieCoinvariants D false A' WW FA' FW (fun τ => a τ - b τ) n₀ Pr q' sA' sW
      (fun τ => by simp only [Bool.false_eq_true, if_false]; rw [hn₀ τ]; ring) kB
  · intro κ P _
    rw [hσ]
  · intro κ P' _
    obtain ⟨P, hP⟩ := hq (q' P')
    rw [hrow κ P P' hP, ← hP, hσ]
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_quotient_bottom_invariants_equiv : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (A A' WW : HSp D) (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW) (a b : D.what₂.Tau → ℚ)
    (had : A.rank + A'.rank = WW.rank),
    (∀ τ, Formalism.UG.HasSignature (gramAt D A τ) A.rank 0) → (∀ τ, Formalism.UG.HasSignature (gramAt D A' τ) A'.rank 0) →
    (∀ τ, Formalism.UG.HasSignature (gramAt D WW τ) WW.rank 0) →
    (∃ α β, GlobalTheory.SquareComm.IsTriple A A' WW α β ∧ ∀ τ, HasInfExp D α τ (a τ) ∧ HasInfExp D β τ (b τ)) →
  ∀ (Pr : ModuleCat.{0} ℂ) (q : PolF D WW.rank A.rank →ₗ[ℂ] Pr) (q' : PolF D WW.rank A'.rank →ₗ[ℂ] Pr),
    Function.Surjective q → Function.Surjective q' →
    (∀ α β, GlobalTheory.SquareComm.IsTriple A A' WW α β → (∀ τ, HasInfExp D α τ (a τ) ∧ HasInfExp D β τ (b τ)) →
      (∃ ωA ωB Pi rf rl p p', GlobalTheory.SquareComm.IsMatch ψ θ FA FA' FW α β ωA ωB Pi rf rl p p') ∧
      ∀ ωA ωB Pi rf rl p p', GlobalTheory.SquareComm.IsMatch ψ θ FA FA' FW α β ωA ωB Pi rf rl p p' →
        ∃ (Pf : ModuleCat.{0} ℂ) (r : (WO A WW → ℂ) →ₗ[ℂ] Pf) (r' : (WO A' WW → ℂ) →ₗ[ℂ] Pf) (e : Pr ⊗[ℂ] Pf ≃ₗ[ℂ] Pi),
          (∀ x, ∃ f, GlobalTheory.SquareComm.IsFinF ψ θ true FA FW f ∧ r f = x) ∧
          (∀ x, ∃ f, GlobalTheory.SquareComm.IsFinF ψ θ false FA' FW f ∧ r' f = x) ∧
          (∀ f, GlobalTheory.SquareComm.IsFinF ψ θ true FA FW f → ∀ P, p (GlobalTheory.SquareComm.fockF ψ θ true FA FW f P) = e (q P ⊗ₜ r f)) ∧
          ∀ f, GlobalTheory.SquareComm.IsFinF ψ θ false FA' FW f → ∀ P,
            p' (GlobalTheory.SquareComm.fockF ψ θ false FA' FW f P) = e (q' P ⊗ₜ r' f)) →
    Nontrivial Pr ∧ ∃ (n₀ : D.what₂.Tau → ℕ) (σ : (D.what₂.Tau → Matrix (Fin WW.rank) (Fin WW.rank) ℂ) → Module.End ℂ Pr),
    (∀ (g : D.what₂.Tau → Matrix.unitaryGroup (Fin A.rank) ℂ) (P : PolF D WW.rank A.rank),
      q (GlobalTheory.MinorFrame.colSub (fun τ => (g τ : Matrix (Fin A.rank) (Fin A.rank) ℂ)) P) =
        GlobalTheory.MinorFrame.detChar n₀ (fun τ => (g τ : Matrix (Fin A.rank) (Fin A.rank) ℂ)) • q P) ∧
    (∀ (g : D.what₂.Tau → Matrix.unitaryGroup (Fin A'.rank) ℂ) (P : PolF D WW.rank A'.rank),
      q' (GlobalTheory.MinorFrame.colSub (fun τ => (g τ : Matrix (Fin A'.rank) (Fin A'.rank) ℂ)) P) =
        GlobalTheory.MinorFrame.detChar n₀ (fun τ => (g τ : Matrix (Fin A'.rank) (Fin A'.rank) ℂ)) • q' P) ∧
    (∀ (κ : D.what₂.Tau → Matrix.unitaryGroup (Fin WW.rank) ℂ), ∀ P ∈ GlobalTheory.MinorFrame.inv (ι := D.what₂.Tau) A.rank WW.rank n₀,
      q (GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ : Matrix (Fin WW.rank) (Fin WW.rank) ℂ).map (starRingEnd ℂ)) P) =
        σ (fun τ => (κ τ : Matrix (Fin WW.rank) (Fin WW.rank) ℂ)) (q P)) ∧
    (∀ (κ : D.what₂.Tau → Matrix.unitaryGroup (Fin WW.rank) ℂ), ∀ P ∈ GlobalTheory.MinorFrame.inv (ι := D.what₂.Tau) A'.rank WW.rank n₀,
      q' (GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ : Matrix (Fin WW.rank) (Fin WW.rank) ℂ)) P) =
        GlobalTheory.MinorFrame.detChar n₀ (fun τ => (κ τ : Matrix (Fin WW.rank) (Fin WW.rank) ℂ)) • σ (fun τ => (κ τ : Matrix (Fin WW.rank) (Fin WW.rank) ℂ)) (q' P)) := by
  first | exact @_root_.GlobalTheory.RealQuotBot.real_quotient_invariants_equiv | exact _root_.GlobalTheory.RealQuotBot.real_quotient_invariants_equiv | (intros; apply _root_.GlobalTheory.RealQuotBot.real_quotient_invariants_equiv <;> assumption)
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct
namespace GlobalTheory.BotMatch
theorem real_quotient_complement_minor : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (A A' WW : HSp D) (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW) (a b : D.what₂.Tau → ℚ)
    (had : A.rank + A'.rank = WW.rank),
    (∀ τ, Formalism.UG.HasSignature (gramAt D A τ) A.rank 0) → (∀ τ, Formalism.UG.HasSignature (gramAt D A' τ) A'.rank 0) →
    (∀ τ, Formalism.UG.HasSignature (gramAt D WW τ) WW.rank 0) →
    (∃ α β, GlobalTheory.SquareComm.IsTriple A A' WW α β ∧ ∀ τ, HasInfExp D α τ (a τ) ∧ HasInfExp D β τ (b τ)) →
  ∀ (Pr : ModuleCat.{0} ℂ) (q : PolF D WW.rank A.rank →ₗ[ℂ] Pr) (q' : PolF D WW.rank A'.rank →ₗ[ℂ] Pr),
    Function.Surjective q → Function.Surjective q' →
    (∀ α β, GlobalTheory.SquareComm.IsTriple A A' WW α β → (∀ τ, HasInfExp D α τ (a τ) ∧ HasInfExp D β τ (b τ)) →
      (∃ ωA ωB Pi rf rl p p', GlobalTheory.SquareComm.IsMatch ψ θ FA FA' FW α β ωA ωB Pi rf rl p p') ∧
      ∀ ωA ωB Pi rf rl p p', GlobalTheory.SquareComm.IsMatch ψ θ FA FA' FW α β ωA ωB Pi rf rl p p' →
        ∃ (Pf : ModuleCat.{0} ℂ) (r : (WO A WW → ℂ) →ₗ[ℂ] Pf) (r' : (WO A' WW → ℂ) →ₗ[ℂ] Pf) (e : Pr ⊗[ℂ] Pf ≃ₗ[ℂ] Pi),
          (∀ x, ∃ f, GlobalTheory.SquareComm.IsFinF ψ θ true FA FW f ∧ r f = x) ∧
          (∀ x, ∃ f, GlobalTheory.SquareComm.IsFinF ψ θ false FA' FW f ∧ r' f = x) ∧
          (∀ f, GlobalTheory.SquareComm.IsFinF ψ θ true FA FW f → ∀ P, p (GlobalTheory.SquareComm.fockF ψ θ true FA FW f P) = e (q P ⊗ₜ r f)) ∧
          ∀ f, GlobalTheory.SquareComm.IsFinF ψ θ false FA' FW f → ∀ P,
            p' (GlobalTheory.SquareComm.fockF ψ θ false FA' FW f P) = e (q' P ⊗ₜ r' f)) →
    ∃ ρ : ℂ, ρ ≠ 0 ∧ ∀ (n : D.what₂.Tau → ℕ) (T : Tup D A.rank WW.rank n), ∃ ε : ℤˣ,
      q (GlobalTheory.BotFormula.minorF rfl rfl T) = (ρ * ((ε : ℤ) : ℂ)) • q' (GlobalTheory.BotFormula.minorF rfl rfl (GlobalTheory.BotMatch.complTup D had T)) := by
  intro h1 h2 h3 h4 D ψ θ θ' hθ A A' WW FA FA' FW a b had hA hA' hW hex Pr q q' hq hq' hm
  obtain ⟨hnt, n₀, σ, i1, i2, i3, i4⟩ :=
    _root_.GlobalTheory.T.real_quotient_bottom_invariants_equiv h1 h2 h3 h4 D ψ θ θ' hθ A A' WW FA FA' FW a b had hA hA' hW hex Pr q q' hq hq' hm
  obtain ⟨α, β, ht, -⟩ := hex
  obtain ⟨p, r, -, h5, h6⟩ := ht.sig
  exact GlobalTheory.T.realQuotient_minor_eq_const_smul_complementMinor D had n₀ Pr q q' σ (by omega) (by omega) hnt hq hq' i1 i2 i3 i4
end GlobalTheory.BotMatch
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bottom_degree_match_real_quotient : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (A A' WW : HSp D) (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW) (a b : D.what₂.Tau → ℚ)
    (had : A.rank + A'.rank = WW.rank),
    (∀ τ, Formalism.UG.HasSignature (gramAt D A τ) A.rank 0) → (∀ τ, Formalism.UG.HasSignature (gramAt D A' τ) A'.rank 0) →
    (∀ τ, Formalism.UG.HasSignature (gramAt D WW τ) WW.rank 0) →
    (∃ α β, GlobalTheory.SquareComm.IsTriple A A' WW α β ∧ ∀ τ, HasInfExp D α τ (a τ) ∧ HasInfExp D β τ (b τ)) →
  ∀ (Pr : ModuleCat.{0} ℂ) (q : PolF D WW.rank A.rank →ₗ[ℂ] Pr) (q' : PolF D WW.rank A'.rank →ₗ[ℂ] Pr),
    Function.Surjective q → Function.Surjective q' →
    (∀ α β, GlobalTheory.SquareComm.IsTriple A A' WW α β → (∀ τ, HasInfExp D α τ (a τ) ∧ HasInfExp D β τ (b τ)) →
      (∃ ωA ωB Pi rf rl p p', GlobalTheory.SquareComm.IsMatch ψ θ FA FA' FW α β ωA ωB Pi rf rl p p') ∧
      ∀ ωA ωB Pi rf rl p p', GlobalTheory.SquareComm.IsMatch ψ θ FA FA' FW α β ωA ωB Pi rf rl p p' →
        ∃ (Pf : ModuleCat.{0} ℂ) (r : (WO A WW → ℂ) →ₗ[ℂ] Pf) (r' : (WO A' WW → ℂ) →ₗ[ℂ] Pf) (e : Pr ⊗[ℂ] Pf ≃ₗ[ℂ] Pi),
          (∀ x, ∃ f, GlobalTheory.SquareComm.IsFinF ψ θ true FA FW f ∧ r f = x) ∧
          (∀ x, ∃ f, GlobalTheory.SquareComm.IsFinF ψ θ false FA' FW f ∧ r' f = x) ∧
          (∀ f, GlobalTheory.SquareComm.IsFinF ψ θ true FA FW f → ∀ P, p (GlobalTheory.SquareComm.fockF ψ θ true FA FW f P) = e (q P ⊗ₜ r f)) ∧
          ∀ f, GlobalTheory.SquareComm.IsFinF ψ θ false FA' FW f → ∀ P,
            p' (GlobalTheory.SquareComm.fockF ψ θ false FA' FW f P) = e (q' P ⊗ₜ r' f)) →
    ∃ ρ : ℂ, ρ ≠ 0 ∧ ∀ (n : D.what₂.Tau → ℕ) (T : Tup D A.rank WW.rank n), ∃ ε : ℤˣ,
      q (GlobalTheory.BotFormula.minorF rfl rfl T) = (ρ * ((ε : ℤ) : ℂ)) • q' (GlobalTheory.BotFormula.minorF rfl rfl (GlobalTheory.BotMatch.complTup D had T)) := by
  first | exact @_root_.GlobalTheory.BotMatch.real_quotient_complement_minor | exact _root_.GlobalTheory.BotMatch.real_quotient_complement_minor | (intros; apply _root_.GlobalTheory.BotMatch.real_quotient_complement_minor <;> assumption)
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct
noncomputable section
namespace GlobalTheory.BotMatch
set_option maxHeartbeats 1000000 in
open GlobalTheory.SqTop GlobalTheory.SquareComm in
theorem theta_bottom_minor_match : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (c0 : T → ℂ), IsBottomTri W i j X → X.IsConst W.ψ W.θ c0 →
      ∃ κ₀ : ℂ, κ₀ ≠ 0 ∧ ∀ (s : T) (Q : ℕ) (δ t0 : ℂ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∀ (ea : P.a = A.rank) (ea' : P'.a = A'.rank) (ed : P.d = WW.rank) (ed' : P'.d = WW.rank),
        ∃ (M : Tup D P.a P.d P.n → Tup D P'.a P'.d P'.n → ℤ) (M' : Tup D P'.a P'.d P'.n → Tup D P.a P.d P.n → ℤ),
          (∀ T₁ T₂, ∑ T, M' T₁ T * M T T₂ = if T₁ = T₂ then 1 else 0) ∧
          ∀ (g : GA D WW) T, X.I W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T) g =
            κ₀ * c0 s * ∑ T', (M T T' : ℂ) * X.I' W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea' ed' T') g := by
  intro hP hK hM _ _
  have hH : GlobalTheory.Published.HoweDualityReal := hP.howeDualityReal
  have hLM := _root_.GlobalTheory.T.twisted_local_factors_match hH hP hK hM
  have hTA := _root_.GlobalTheory.T.twisted_square_theta_integrals_eq hP hK hM
  obtain ⟨CF1, H1⟩ := GlobalTheory.T.definiteBottom_dictionary_frames_exponents_kernel
  obtain ⟨CF2, H2⟩ := _root_.GlobalTheory.T.theta_bottom_finite_place_matching hH hP hK hM
  refine ⟨max CF1 CF2, fun ε CF hCF => ?_⟩
  obtain ⟨C1, x1, G1⟩ := H1 ε CF (le_trans (le_max_left _ _) hCF)
  obtain ⟨C2, x2, G2⟩ := H2 ε CF (le_trans (le_max_right _ _) hCF)
  refine ⟨max C1 C2, max x1 x2, fun C hC D large₂ he hx hR T Lc μ₀ hμ G W _ i j A A' WW X c0 hX hc => ?_⟩
  obtain ⟨FA, FA', FW, a, b, hdA, hdef, hdW, hD⟩ :=
    G1 C (le_trans (le_max_left _ _) hC) D large₂ he (le_trans (le_max_left _ _) hx) hR T Lc μ₀ hμ G W i j A A' WW X hX
  have hF := G2 C (le_trans (le_max_right _ _) hC) D large₂ he (le_trans (le_max_right _ _) hx) hR T Lc μ₀ hμ G W i j A A' WW X hX
  obtain ⟨Pr, q, q', hq, hq', hLMt⟩ := hLM D W.ψ W.θ W.ψ_std W.θ_is A A' WW FA FA' FW a b
  obtain ⟨ρ, hρ, hrel⟩ := _root_.GlobalTheory.T.bottom_degree_match_real_quotient hH hP hK hM D W.ψ W.θ W.ψ_std W.θ_is A A' WW FA FA' FW a b hX.is.rank hdA hdef hdW
    ⟨_, _, (hD μ₀).1, (hD μ₀).2.1⟩ Pr q q' hq hq' hLMt
  choose εf hεf using hrel
  have eI : ∀ t P, thetaInt (X.ω t) X.m X.fd (fockF W.ψ W.θ true FA FW (X.f t) P) = X.I W.ψ W.θ t P := fun t P => by
    funext h; simp only [thetaInt, Tri.I, (hD t).2.2.2.2.1]
  have eI' : ∀ t P, thetaInt (X.ω' t) X.m' X.fd' (fockF W.ψ W.θ false FA' FW (X.f' t) P) = X.I' W.ψ W.θ t P := fun t P => by
    funext h; simp only [thetaInt, Tri.I', (hD t).2.2.2.2.2]
  have iI' : ∀ t P h, IntegrableOn (fun g => thetaKO (X.ω' t) g h (fockF W.ψ W.θ false FA' FW (X.f' t) P)) X.fd' X.m' :=
    fun t P h => by simp only [(hD t).2.2.2.2.2]; exact (hX.integrable t).2 P h
  have key : ∀ t, (∀ P', q' P' = 0 → X.I' W.ψ W.θ t P' = 0) ∧
      ((∀ P', X.I' W.ψ W.θ t P' = 0) ∨ ∀ P', X.I' W.ψ W.θ t P' = 0 → q' P' = 0) ∧
      (∃ lam : ℂ, ∀ P P', q P = q' P' → X.I W.ψ W.θ t P = lam • X.I' W.ψ W.θ t P') := by
    intro t
    obtain ⟨hTr, hInf, hf, hf', -, -⟩ := hD t
    obtain ⟨hex, hfac⟩ := hLMt _ _ hTr hInf
    obtain ⟨Pm, rf, rl, p, p', hm⟩ := _root_.GlobalTheory.T.triple_weil_transfer_matching hH hP hK hM D W.ψ W.θ W.ψ_std W.θ_is A A' WW FA FA' FW _ _ hTr hex (X.ω t) (X.ω' t)
      (hX.is.weil t) (hX.is.weil' t)
    obtain ⟨Pf, r, r', e, -, -, hr, hr'⟩ := hfac _ _ _ _ _ _ _ hm
    obtain ⟨c, hc0, hc⟩ := hTA D W.ψ W.θ W.θ_is A A' WW FA FA' FW _ _ hTr X.m X.fd X.m' X.fd' hX.is.meas hX.is.meas'
      (X.ω t) (X.ω' t) Pm rf rl p p' hm
    have hrel := _root_.GlobalTheory.T.theta_integral_vanishes_on_finite_relations hP D W.ψ W.θ W.ψ_std W.θ_is A' WW FA' FW _ _ (X.ω' t) (hX.is.weil' t) hdef X.m' X.fd' hX.is.meas'
    have kerp' := finRel_le_ker p' hm.mapB.invf
    have memF : ∀ P', fockF W.ψ W.θ false FA' FW (X.f' t) P' ∈ algF W.ψ W.θ false FA' FW :=
      fun P' => Submodule.subset_span ⟨_, P', hf', rfl⟩
    have same : ∀ Ψ ∈ algF W.ψ W.θ false FA' FW, (∀ h, IntegrableOn (fun g => thetaKO (X.ω' t) g h Ψ) X.fd' X.m') →
        ∀ Φ₀, Ψ - Φ₀ ∈ finRel (X.ω' t) (algF W.ψ W.θ false FA' FW) → ModInt W.θ (X.ω' t) X.m' X.fd' Φ₀ →
        thetaInt (X.ω' t) X.m' X.fd' Ψ = thetaInt (X.ω' t) X.m' X.fd' Φ₀ := by
      intro Ψ _ hΨ Φ₀ hd hmod
      obtain ⟨N, K, hmod⟩ := hmod
      funext h
      have h0 := congrFun (hrel _ hd) h
      simp only [thetaInt, thetaKO_sub] at h0 ⊢
      rw [integral_sub (hΨ h) (hmod h).1] at h0
      exact sub_eq_zero.1 h0
    have kill : ∀ Ψ ∈ algF W.ψ W.θ false FA' FW, (∀ h, IntegrableOn (fun g => thetaKO (X.ω' t) g h Ψ) X.fd' X.m') →
        p' Ψ = 0 → thetaInt (X.ω' t) X.m' X.fd' Ψ = 0 := by
      intro Ψ hΨ hi hp
      obtain ⟨Φ₀, hΦ₀, hd, hmod, hI⟩ := hc Ψ hΨ
      have hp0 : p' Φ₀ = 0 := by
        have := kerp' hd
        rw [LinearMap.mem_ker, map_sub, hp, zero_sub, neg_eq_zero] at this
        exact this
      have h1 := hI 0 (zero_mem _) (by rw [map_zero, hp0])
      have h2 : thetaInt (X.ω t) X.m X.fd 0 = 0 := by funext h; simp [thetaInt, thetaKO_zero]
      rw [h2] at h1
      rw [same Ψ hΨ hi Φ₀ hd hmod]
      exact ((smul_eq_zero.1 h1.symm).resolve_left hc0)
    have hp'F : ∀ P', p' (fockF W.ψ W.θ false FA' FW (X.f' t) P') = e (q' P' ⊗ₜ r' (X.f' t)) := hr' _ hf'
    refine ⟨fun P' h0 => ?_, ?_, ?_⟩
    · rw [← eI']
      exact kill _ (memF P') (iI' t P') (by rw [hp'F, h0, TensorProduct.zero_tmul, map_zero])
    · by_cases hall : ∀ P', X.I' W.ψ W.θ t P' = 0
      · exact Or.inl hall
      refine Or.inr fun P' h0 => ?_
      by_contra hq0
      refine hall fun P'' => ?_
      rw [← eI']
      by_cases hy : r' (X.f' t) = 0
      · exact kill _ (memF P'') (iI' t P'') (by rw [hp'F, hy, TensorProduct.tmul_zero, map_zero])
      · have hne : p' (fockF W.ψ W.θ false FA' FW (X.f' t) P') ≠ 0 := by
          rw [hp'F]; exact e.map_ne_zero_iff.2 (tmul_ne_zero' hq0 hy)
        exact _root_.GlobalTheory.T.theta_lift_vanishes_of_irreducible_defect hH hP hK hM hTA D W.ψ W.θ W.ψ_std W.θ_is A A' WW FA FA' FW _ _ hTr hdA hdef hdW X.m X.fd X.m' X.fd'
          hX.is.meas hX.is.meas' (X.ω t) (X.ω' t) Pm rf rl p p' hm _ (memF P') hne (by rw [eI']; exact h0) _ (memF P'')
    · obtain ⟨κ, hκ⟩ := hF FA FA' FW t hf hf' Pm rf rl p p' hm Pr Pf q q' r r' e hq hq' hr hr'
      refine ⟨c * κ, fun P P' hPP => ?_⟩
      set Ψ := κ • fockF W.ψ W.θ false FA' FW (X.f' t) P' with hΨdef
      have hΨ : Ψ ∈ algF W.ψ W.θ false FA' FW := Submodule.smul_mem _ _ (memF P')
      have hΨi : ∀ h, IntegrableOn (fun g => thetaKO (X.ω' t) g h Ψ) X.fd' X.m' := fun h => by
        simp only [hΨdef, thetaKO_smul]; exact (iI' t P' h).const_mul κ
      obtain ⟨Φ₀, -, hd, hmod, hI⟩ := hc Ψ hΨ
      have hpp : p (fockF W.ψ W.θ true FA FW (X.f t) P) = p' Φ₀ := by
        have h1 : p' Φ₀ = p' Ψ := by
          have := kerp' hd
          rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at this
          exact this.symm
        rw [h1, hΨdef, map_smul, hp'F, hr _ hf, hκ, hPP, TensorProduct.tmul_smul, map_smul]
      have h2 := hI _ (Submodule.subset_span ⟨_, P, hf, rfl⟩) hpp
      rw [eI, ← same Ψ hΨ hΨi Φ₀ hd hmod] at h2
      rw [h2, ← eI', mul_smul]
      congr 1
      funext h
      simp [hΨdef, thetaInt, thetaKO_smul, integral_const_mul]
  choose hker hirr hlam using key
  let Il : T → PolF D WW.rank A'.rank →ₗ[ℂ] (GA D WW → ℂ) := fun t =>
    { toFun := fun P' => X.I' W.ψ W.θ t P'
      map_add' := fun P Q => by
        show X.I' W.ψ W.θ t (P + Q) = X.I' W.ψ W.θ t P + X.I' W.ψ W.θ t Q
        rw [← eI', ← eI', ← eI', map_add (f := _)]; funext h
        simp only [thetaInt, thetaKO_add, Pi.add_apply]
        exact integral_add (iI' t P h) (iI' t Q h)
      map_smul' := fun c P => by
        show X.I' W.ψ W.θ t (c • P) = c • X.I' W.ψ W.θ t P
        rw [← eI', ← eI', map_smul]; funext h
        simp [thetaInt, thetaKO_smul, integral_const_mul] }
  have hK : ∀ t, LinearMap.ker q' ≤ LinearMap.ker (Il t) := fun t P' h0 => hker t P' h0
  let J : T → (Pr →ₗ[ℂ] (GA D WW → ℂ)) := fun t =>
    ((LinearMap.ker q').liftQ (Il t) (hK t)) ∘ₗ (q'.quotKerEquivOfSurjective hq').symm.toLinearMap
  have hJ : ∀ t P', J t (q' P') = X.I' W.ψ W.θ t P' := fun t P' => by
    have : (q'.quotKerEquivOfSurjective hq').symm (q' P') = Submodule.Quotient.mk P' := by
      rw [LinearEquiv.symm_apply_eq]; exact (LinearMap.quotKerEquivOfSurjective_apply_mk _ _ _).symm
    simp only [J, LinearMap.comp_apply, LinearEquiv.coe_coe, this, Submodule.liftQ_apply]; rfl
  have hJI : ∀ t, ∃ lam : ℂ, ∀ P, X.I W.ψ W.θ t P = lam • J t (q P) := fun t => by
    obtain ⟨lam, hl⟩ := hlam t
    refine ⟨lam, fun P => ?_⟩
    obtain ⟨P', hP'⟩ := hq' (q P)
    rw [← hP', hJ]; exact hl P P' hP'.symm
  choose lam hlamJ using hJI
  obtain ⟨⟨t₁, ht₁⟩, P0, P0', hc⟩ := hc
  have hJne : ∀ t, J t (q' P0') ≠ 0 := fun t h0 => by
    obtain ⟨h, hh⟩ := (hc t).2.1
    exact hh (by rw [← hJ, h0]; rfl)
  have hq0 : q' P0' ≠ 0 := fun h0 => hJne t₁ (by rw [h0, map_zero])
  have hinj : ∀ t, Function.Injective (J t) := fun t => by
    rcases hirr t with h | h
    · exact absurd (by rw [hJ]; exact h P0') (hJne t)
    · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro x hx0
      obtain ⟨P', rfl⟩ := hq' x
      rw [hJ] at hx0
      exact h P' hx0
  have heq : ∀ t, lam t • q P0 = c0 t • q' P0' := fun t => by
    apply hinj t
    rw [map_smul, map_smul, ← hlamJ, hJ]
    funext h
    simp only [Pi.smul_apply, smul_eq_mul]
    exact (hc t).2.2 h
  have hlam1 : lam t₁ ≠ 0 := fun h0 => by
    have := heq t₁
    rw [h0, zero_smul] at this
    exact (smul_eq_zero.1 this.symm).elim ht₁ hq0
  set κ := c0 t₁ / lam t₁ with hκdef
  have hκ0 : κ ≠ 0 := div_ne_zero ht₁ hlam1
  have hqP0 : q P0 = κ • q' P0' := by
    rw [hκdef, div_eq_inv_mul, mul_smul, ← heq t₁, smul_smul, inv_mul_cancel₀ hlam1, one_smul]
  have hlc : ∀ t, lam t = c0 t / κ := fun t => by
    have h1 := heq t
    rw [hqP0, smul_smul, ← sub_eq_zero, ← sub_smul] at h1
    have h2 := (smul_eq_zero.1 h1).resolve_right hq0
    rw [eq_div_iff hκ0]; exact sub_eq_zero.1 h2
  refine ⟨ρ / κ, div_ne_zero hρ hκ0, fun s Q δ t0 P P' hB ea ea' ed ed' => ?_⟩
  have hn : P'.n = P.n := GlobalTheory.T.squareBottomPairs_weights_eq G s i j _ P P' hB
  have core : ∀ (a₁ a₁' d₁ d₁' : ℕ) (n n' : D.what₂.Tau → ℕ) (ea : a₁ = A.rank) (ea' : a₁' = A'.rank) (ed : d₁ = WW.rank)
      (ed' : d₁' = WW.rank) (hn : n' = n), ∃ (M : Tup D a₁ d₁ n → Tup D a₁' d₁' n' → ℤ) (M' : Tup D a₁' d₁' n' → Tup D a₁ d₁ n → ℤ),
        (∀ T₁ T₂, ∑ T, M' T₁ T * M T T₂ = if T₁ = T₂ then 1 else 0) ∧
        ∀ (g : GA D WW) T, X.I W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T) g =
          ρ / κ * c0 s * ∑ T', (M T T' : ℂ) * X.I' W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea' ed' T') g := by
    intro a₁ a₁' d₁ d₁' n n' ea ea' ed ed' hn
    subst ea ea' ed ed' hn
    obtain ⟨M, M', hMM, hMf⟩ := exists_signed_perm (complTup D hX.is.rank) (complTup_bijective D hX.is.rank) (εf _)
    refine ⟨M, M', fun T₁ T₂ => by rw [hMM T₁ T₂]; congr, fun g T => ?_⟩
    rw [hMf T (fun T' => X.I' W.ψ W.θ s (GlobalTheory.BotFormula.minorF rfl rfl T') g), hlamJ, hεf, map_smul, ← hJ, hlc]
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
  exact core P.a P'.a P.d P'.d P.n P'.n ea ea' ed ed' hn
end GlobalTheory.BotMatch
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rallis_bottom_minor_matching : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (c0 : T → ℂ), IsBottomTri W i j X → X.IsConst W.ψ W.θ c0 →
      ∃ κ₀ : ℂ, κ₀ ≠ 0 ∧ ∀ (s : T) (Q : ℕ) (δ t0 : ℂ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∀ (ea : P.a = A.rank) (ea' : P'.a = A'.rank) (ed : P.d = WW.rank) (ed' : P'.d = WW.rank),
        ∃ (M : Tup D P.a P.d P.n → Tup D P'.a P'.d P'.n → ℤ) (M' : Tup D P'.a P'.d P'.n → Tup D P.a P.d P.n → ℤ),
          (∀ T₁ T₂, ∑ T, M' T₁ T * M T T₂ = if T₁ = T₂ then 1 else 0) ∧
          ∀ (g : GA D WW) T, X.I W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T) g =
            κ₀ * c0 s * ∑ T', (M T T' : ℂ) * X.I' W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea' ed' T') g := by
  first | exact @_root_.GlobalTheory.BotMatch.theta_bottom_minor_match | exact _root_.GlobalTheory.BotMatch.theta_bottom_minor_match | (intros; apply _root_.GlobalTheory.BotMatch.theta_bottom_minor_match <;> assumption)
end
