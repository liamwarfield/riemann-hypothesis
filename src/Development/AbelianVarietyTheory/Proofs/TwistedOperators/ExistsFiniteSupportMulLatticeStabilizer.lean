module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompactOpenLatticeStabilizerAtPlaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDatumActionOfPair
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleTwistOfTwistingCharacter
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingEvaluation
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SqrtDivMulEqSqrtMul

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteSupportMulLatticeStabilizer
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteSupportMulLatticeStabilizer
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.TruncAway

open GlobalTheory.AdelicU

theorem exists_trunc_mul_inK : ∀ {D : D7} (V : HSp D) (L : GlobalTheory.FinPl.Lat V), L.FG → Submodule.span D.host.E (L : Set (Fin V.rank → D.host.E)) = ⊤ →
  ∀ (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (b : GA D V), ∃ (b' : GA D V) (P : Finset (HeightOneSpectrum (𝓞 D.host.F))),
    (∀ v ∉ P, GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v b' = 1) ∧ GlobalTheory.FinPl.InK V L (fun v => v ∉ S) (b'⁻¹ * b) := by
  intro D V L hfg hspan S b
  haveI : Submodule.IsLattice D.host.E L := Submodule.IsLattice.of_fg _ hfg
  haveI : Submodule.IsFullLattice D.host.E L := ⟨hspan⟩
  have hfin := Filter.eventually_cofinite.1 (eventually_proj_mem_stabLoc D.sp.cm.sig V.gram L b)
  classical
  let P : Finset (HeightOneSpectrum (𝓞 D.host.F)) := S ∪ hfin.toFinset
  let b' : GA D V := ofInf D.sp.cm.sig V.gram (projInf D.sp.cm.sig V.gram b) *
    embAt D.sp.cm.sig V.gram P (projAt D.sp.cm.sig V.gram P b)
  have hat := mem_atPts.1 (embAt_mem D.sp.cm.sig V.gram P (projAt D.sp.cm.sig V.gram P b))
  have hout : ∀ v ∉ P, proj D.sp.cm.sig V.gram v b' = 1 := fun v hv => by
    simp only [b', map_mul, proj_ofInf, one_mul]
    exact hat.2 v hv
  have hin : ∀ v ∈ P, proj D.sp.cm.sig V.gram v b' = proj D.sp.cm.sig V.gram v b := fun v hv => by
    simp only [b', map_mul, proj_ofInf, one_mul]
    exact proj_embAt D.sp.cm.sig V.gram P _ ⟨v, hv⟩
  have hinf : projInf D.sp.cm.sig V.gram b' = projInf D.sp.cm.sig V.gram b := by
    simp only [b', map_mul, projInf_ofInf, mem_finPts.1 hat.1, mul_one]
  refine ⟨b', P, hout, ?_, ?_⟩
  · rw [GlobalTheory.FinPl.KOpen.mem_grpAt_iff]
    refine ⟨mem_finPts.2 ?_, fun v hv => ?_⟩
    · rw [map_mul, map_inv, hinf, inv_mul_cancel]
    · have hvP : v ∈ P := Finset.mem_union_left _ (not_not.1 hv)
      rw [map_mul, map_inv, hin v hvP, inv_mul_cancel]
  · refine GlobalTheory.FinPl.KOpen.moves_of_levelOpen V L hfg _ (mem_levelOpen.2 fun v => ?_)
    by_cases hv : v ∈ P
    · rw [map_mul, map_inv, hin v hv, inv_mul_cancel]; exact one_mem _
    · rw [map_mul, map_inv, hout v hv, inv_one, one_mul]
      by_contra h
      exact hv (Finset.mem_union_right _ (hfin.mem_toFinset.2 h))

end GlobalTheory.TruncAway

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteSupportMulLatticeStabilizerStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteSupport_mul_latticeStabilizer : ∀ {D : D7} (V : HSp D) (L : GlobalTheory.FinPl.Lat V), L.FG → Submodule.span D.host.E (L : Set (Fin V.rank → D.host.E)) = ⊤ →
  ∀ (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (b : GA D V), ∃ (b' : GA D V) (P : Finset (HeightOneSpectrum (𝓞 D.host.F))),
    (∀ v ∉ P, GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v b' = 1) ∧ GlobalTheory.FinPl.InK V L (fun v => v ∉ S) (b'⁻¹ * b) := by
  first | exact @GlobalTheory.TruncAway.exists_trunc_mul_inK | exact GlobalTheory.TruncAway.exists_trunc_mul_inK | (intros; apply GlobalTheory.TruncAway.exists_trunc_mul_inK <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchrodingerThetaDatumHeisenbergOriented
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchrodingerThetaDatumHeisenbergOriented
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.SquareAgree.HeisCov

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem hTens_eq_trace {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) {α β : Type}
    [Fintype α] [Fintype β] (JA : Matrix α α A) (JB : Matrix β β A) (x y : Matrix α β A) :
    GlobalTheory.WeilM.hTens c JA JB x y = (xᵀ * JA * y.map c * JBᵀ).trace := by
  simp only [GlobalTheory.WeilM.hTens, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul]
  calc _ = ∑ j, ∑ i, ∑ k, ∑ l, x i j * JA i k * JB j l * c (y k l) := Finset.sum_comm
    _ = ∑ j, ∑ k, ∑ i, ∑ l, x i j * JA i k * JB j l * c (y k l) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ j, ∑ k, ∑ l, ∑ i, x i j * JA i k * JB j l * c (y k l) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ j, ∑ l, ∑ k, ∑ i, x i j * JA i k * JB j l * c (y k l) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
        Finset.sum_congr rfl fun _ _ => by ring

theorem hO_eq_trace (S T : HSp D) (x y : WO S T) :
    hO S T x y = Matrix.trace (HMul.hMul (HMul.hMul (HMul.hMul ((S.gram⁻¹).map (incA D))
      ((y : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (cA D))ᵀ) (T.gram.map (incA D)))
      (x : Matrix (Fin T.rank) (Fin S.rank) (AE D))) := by
  simp only [hO, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  calc ∑ b, ∑ c', ∑ d, incA D (S.gram⁻¹ a b) * cA D (y c' b) * incA D (T.gram c' d) * x d a
      = ∑ b, ∑ d, ∑ c', incA D (S.gram⁻¹ a b) * cA D (y c' b) * incA D (T.gram c' d) * x d a :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ d, ∑ b, ∑ c', incA D (S.gram⁻¹ a b) * cA D (y c' b) * incA D (T.gram c' d) * x d a := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun _ _ => Finset.sum_comm

theorem trace_mul_submatrix {A : Type} [CommRing A] {m d : ℕ} (e : Fin m ≃ Fin d) (P : Matrix (Fin d) (Fin d) A)
    (K : Matrix (Fin m) (Fin m) A) : (P * K.submatrix e.symm e.symm).trace = (P.submatrix e e * K).trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.submatrix_apply]
  rw [← Equiv.sum_comp e]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Equiv.sum_comp e]
  simp

theorem cA_inc (a : D.host.E) : cA D (incA D a) = incA D (star a) := by
  simp [cA, sigR, CMData.sig, inclR]; rfl

theorem gram_herm (S : HSp D) : S.gramᴴ = S.gram :=
  Matrix.ext fun _ _ => S.herm.eq _ _

theorem gram_map_herm (S : HSp D) : ((S.gram.map (incA D)).map (cA D))ᵀ = S.gram.map (incA D) := by
  refine Matrix.ext fun i j => ?_
  exact (cA_inc _).trans (congrArg (incA D) (congrFun (congrFun (gram_herm S) i) j))

theorem gram_inv_mul (T : HSp D) : T.gram⁻¹.map (incA D) * T.gram.map (incA D) = 1 := by
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (gram_det_ne _))]; simp

theorem hTens_eq_trace' {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) (c' : A →+* A)
    (hc : ∀ a, c a = c' a) {α β : Type} [Fintype α] [Fintype β] (JA : Matrix α α A) (JB : Matrix β β A)
    (x y : Matrix α β A) : GlobalTheory.WeilM.hTens c JA JB x y = (xᵀ * JA * y.map c' * JBᵀ).trace := by
  rw [hTens_eq_trace]
  congr 3
  ext i j
  exact hc _

end GlobalTheory.SquareAgree.HeisCov

namespace GlobalTheory.SquareAgree.HeisCov

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem sgn_gram (ε : Bool) (S : HSp D) : (sgn ε S).gram = (if ε then -1 else 1 : D.host.E) • S.gram := by
  cases ε <;> ext i j <;> simp [Formalism.BasicNotions.HSpace.gram]


set_option maxHeartbeats 1000000 in
theorem symp_eq (ε : Bool) (S X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d)
    (JV : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (JW : Matrix (Fin d) (Fin d) D.host.E)
    (hJ : JV = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : JW = D.host.xi0 • reindex e e X.gramᵀ)
    (cS : Matrix (Fin S.rank) (Fin d) (AE D) → WO S X)
    (hcS : ∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id)
      (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D)))
    (u w : Matrix (Fin S.rank) (Fin d) (AE D)) :
    GlobalTheory.WeilM.symp (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F JV)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F JW) u w = symplO (sgn ε S) X (cS u) (cS w) := by
  have hGs : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram) = (sgn ε S).gram.map (incA D) := by
    rw [← sgn_gram]; rfl
  have hJA : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F JV = -(sgn ε S).gram.map (incA D) := by
    rw [hJ, sgn_gram]
    cases ε <;> ext i j <;> simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM]
  have hJB : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F JW)ᵀ =
      incA D D.host.xi0 • (X.gram.map (incA D)).submatrix e.symm e.symm := by
    rw [hJW]; ext i j; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM]
  unfold GlobalTheory.WeilM.symp symplO
  rw [hTens_eq_trace' (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (cA D) (fun _ => rfl), hO_eq_trace, hcS, hcS, hGs, hJA, hJB]
  have hinv := gram_inv_mul (sgn ε S)
  have hh := gram_map_herm (sgn ε S)
  have hW : ((wᵀ.submatrix e id).map (cA D))ᵀ = (w.map (cA D)).submatrix id e := rfl
  congr 1
  rw [Matrix.map_mul, Matrix.transpose_mul, hh, ← Matrix.mul_assoc _ _ (((wᵀ.submatrix e id).map (cA D))ᵀ), hinv,
    Matrix.one_mul, hW]
  rw [Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_neg, Matrix.neg_mul, Matrix.neg_mul, Matrix.trace_neg,
    smul_eq_mul, trace_mul_submatrix, Matrix.submatrix_mul _ _ _ id _ Function.bijective_id,
    Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, Matrix.submatrix_id_id]
  rw [Matrix.mul_assoc (uᵀ.submatrix e id * _), Matrix.trace_mul_comm (uᵀ.submatrix e id * _)]
  ring

end GlobalTheory.SquareAgree.HeisCov

namespace GlobalTheory.SquareAgree.HeisCov

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem invOf_two' {D : D7} : ⅟(2 : AF D.host.F) = algebraMap D.host.F (AF D.host.F) (1 / 2) := by
  refine invOf_eq_right_inv ?_
  rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul, mul_one_div_cancel two_ne_zero, map_one]

theorem isDatum_rho : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig → Bs.ψ = ψ →
    ∀ (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ)
      (hJ : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : Ws.J = D.host.xi0 • reindex e e X.gramᵀ),
      Vs.IsHerm D.sp.cm.sig Bs r s → Ws.IsSkew D.sp.cm.sig Bs r' s' →
      (∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ)) →
    ∀ M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws, M.IsGood Bs.ψ →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
      ∀ (Φ : (Fin S.rank × Fin d → AF D.host.F) → ℂ) (f : WO S X → ℂ), IsDatum M ψ cS Φ f →
        ∀ w : Matrix (Fin S.rank) (Fin d) (AE D), IsDatum M ψ cS (M.co.rho ψ w Φ) (heisO ψ (sgn ε S) X (cS w) f) := by
  intro D ψ θ _ ε S X A B d e Bs hBs hψ Vs Ws r s r' s' hJ hJW _ _ _ M _ cS hcS Φ f hD w
  refine ⟨?_, fun u => ?_⟩
  · have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ := hψ ▸ hBs.std
    exact GlobalTheory.HeisSchA.rho_mem_schA M ψ hstd w Φ hD.1
  · rw [GlobalTheory.BigDat.rho_rho M.co ψ u w Φ, GlobalTheory.WeilM.thetaSum_smul, hD.2 (u + w)]
    unfold heisO symplOH
    rw [symp_eq ε S X e Vs.J Ws.J hJ hJW cS hcS u w, map_add (f := _), invOf_two']

end GlobalTheory.SquareAgree.HeisCov
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchrodingerThetaDatumHeisenbergOrientedStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schrodingerThetaDatum_heisenberg_oriented : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig → Bs.ψ = ψ →
    ∀ (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ)
      (hJ : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : Ws.J = D.host.xi0 • reindex e e X.gramᵀ),
      Vs.IsHerm D.sp.cm.sig Bs r s → Ws.IsSkew D.sp.cm.sig Bs r' s' →
      (∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ)) →
    ∀ M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws, M.IsGood Bs.ψ →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
      ∀ (Φ : (Fin S.rank × Fin d → AF D.host.F) → ℂ) (f : WO S X → ℂ), IsDatum M ψ cS Φ f →
        ∀ w : Matrix (Fin S.rank) (Fin d) (AE D), IsDatum M ψ cS (M.co.rho ψ w Φ) (heisO ψ (sgn ε S) X (cS w) f) := by
  first | exact @GlobalTheory.SquareAgree.HeisCov.isDatum_rho | exact GlobalTheory.SquareAgree.HeisCov.isDatum_rho | (intros; apply GlobalTheory.SquareAgree.HeisCov.isDatum_rho <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMultilinearColumnRowKernelPairing
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMultilinearColumnRowKernelPairing
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.LastVertexInv

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.ArrowMultilinear

section General

variable {V : ℕ → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)]

theorem chainTo_congr {k k' : ∀ j, V j →ₗ[ℂ] V (j + 1)} : ∀ n, (∀ j < n, k j = k' j) → chainTo k n = chainTo k' n
  | 0, _ => rfl
  | n + 1, h => by
    show k n ∘ₗ chainTo k n = k' n ∘ₗ chainTo k' n
    rw [h n (Nat.lt_succ_self n), chainTo_congr n fun j hj => h j (Nat.lt_succ_of_lt hj)]

theorem chain_multilinear : ∀ (m : ℕ) (A : Fin m → Type) [∀ j, AddCommGroup (A j)] [∀ j, Module ℂ (A j)]
    (k : ∀ j : Fin m, A j →ₗ[ℂ] (V j →ₗ[ℂ] V (j + 1))),
    ∃ M : (∀ j, A j) →ₘₗ[ℂ] (V 0 →ₗ[ℂ] V m), ∀ fs,
      M fs = chainTo (fun j => if h : j < m then k ⟨j, h⟩ (fs ⟨j, h⟩) else 0) m := by
  intro m
  induction m with
  | zero =>
    intro A _ _ k
    exact ⟨MultilinearMap.constOfIsEmpty (RingHom.id ℂ) A LinearMap.id, fun _ => rfl⟩
  | succ m ih =>
    intro A _ _ k
    obtain ⟨M, hM⟩ := ih (fun j => A j.castSucc) (fun j => k j.castSucc)
    let kl : A (Fin.last m) →ₗ[ℂ] (V m →ₗ[ℂ] V (m + 1)) := k (Fin.last m)
    refine ⟨MultilinearMap.uncurryRight
      (((LinearMap.llcomp ℂ (V 0) (V m) (V (m + 1)) ∘ₗ kl).flip).compMultilinearMap M), fun fs => ?_⟩
    show kl (fs (Fin.last m)) ∘ₗ M (Fin.init fs) = _ ∘ₗ chainTo _ m
    rw [hM]
    beta_reduce
    rw [dite_eq_left (Nat.lt_succ_self m)]
    congr 1
    refine chainTo_congr m fun j hj => ?_
    rw [dite_eq_left hj, dite_eq_left (Nat.lt_succ_of_lt hj)]
    rfl

theorem pair_multilinear {ι κ X Y : Type} {A : ι → Type} {B : κ → Type} [∀ j, AddCommGroup (A j)] [∀ j, Module ℂ (A j)]
    [∀ j, AddCommGroup (B j)] [∀ j, Module ℂ (B j)] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (β : X →ₗ[ℂ] Y →ₗ[ℂ] ℂ) (Ma : (∀ j, A j) →ₘₗ[ℂ] X) (Mb : (∀ j, B j) →ₘₗ[ℂ] Y) :
    ∃ M : (∀ j, A j) →ₘₗ[ℂ] ((∀ j, B j) →ₘₗ[ℂ] ℂ), ∀ a b, M a b = β (Ma a) (Mb b) := by
  let L : X →ₗ[ℂ] ((∀ j, B j) →ₘₗ[ℂ] ℂ) :=
    { toFun := fun x => (β x).compMultilinearMap Mb
      map_add' := fun x x' => by ext b; simp
      map_smul' := fun c x => by ext b; simp }
  exact ⟨L.compMultilinearMap Ma, fun _ _ => rfl⟩

theorem compl_multilinear {ι κ X Y P Q : Type} {A : ι → Type} {B : κ → Type} [∀ j, AddCommGroup (A j)] [∀ j, Module ℂ (A j)]
    [∀ j, AddCommGroup (B j)] [∀ j, Module ℂ (B j)] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup P] [Module ℂ P] [AddCommGroup Q] [Module ℂ Q]
    (β : X →ₗ[ℂ] Y →ₗ[ℂ] ℂ) (c : (∀ j, A j) → P →ₗ[ℂ] X) (r : (∀ j, B j) → Q →ₗ[ℂ] Y) (u : P) (v : Q)
    (hc : ∃ M : (∀ j, A j) →ₘₗ[ℂ] X, ∀ a, M a = c a u)
    (hr : ∃ M : (∀ j, B j) →ₘₗ[ℂ] Y, ∀ b, M b = r b v) :
    ∃ M : (∀ j, A j) →ₘₗ[ℂ] ((∀ j, B j) →ₘₗ[ℂ] ℂ), ∀ a b, M a b = β.compl₁₂ (c a) (r b) u v := by
  obtain ⟨Ma, ha⟩ := hc
  obtain ⟨Mb, hb⟩ := hr
  obtain ⟨M, hM⟩ := pair_multilinear β Ma Mb
  exact ⟨M, fun a b => by rw [hM, ha, hb, LinearMap.compl₁₂_apply]⟩

end General

section Jet

variable {ι : Type} [Fintype ι] {a b : ℕ}

theorem jetLin_add (J J' : (Formalism.L2.Ker.DVar ι a b →₀ ℕ) → ℂ) :
    Formalism.L2.Ker.jetLin (J + J') = Formalism.L2.Ker.jetLin J + Formalism.L2.Ker.jetLin J' := by
  refine (MvPolynomial.basisMonomials _ ℂ).ext fun m => ?_
  simp only [Formalism.L2.Ker.jetLin, LinearMap.add_apply, Module.Basis.constr_basis, Pi.add_apply, map_add (f := _)]

theorem jetLin_smul (c : ℂ) (J : (Formalism.L2.Ker.DVar ι a b →₀ ℕ) → ℂ) :
    Formalism.L2.Ker.jetLin (c • J) = c • Formalism.L2.Ker.jetLin J := by
  refine (MvPolynomial.basisMonomials _ ℂ).ext fun m => ?_
  simp only [Formalism.L2.Ker.jetLin, LinearMap.smul_apply, Module.Basis.constr_basis, Pi.smul_apply, map_smul]

end Jet

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem jetTab_add (W : G.Weil) (B : VertexFrames G) (p : Pair T) {f f' : WO (G.pS p) (G.pT p) → ℂ}
    (hf : IsThetaFunO W.ψ _ _ f) (hf' : IsThetaFunO W.ψ _ _ f') (x : FinPt G p.small) (y : FinPt G p.big) :
    jetTab W B p (f + f') x y = jetTab W B p f x y + jetTab W B p f' x y := by
  funext k
  simp only [jetTab, kerFin, fockIn, GridData.Weil.ker, thetaKO, Pi.add_apply]
  rw [GlobalTheory.SpecFac.pureTensorO_add W.ψ_std W.θ_is _ _ _ _ hf hf', map_add (f := _), Pi.add_apply]

theorem jetTab_smul (W : G.Weil) (B : VertexFrames G) (p : Pair T) (c : ℂ) (f : WO (G.pS p) (G.pT p) → ℂ)
    (x : FinPt G p.small) (y : FinPt G p.big) :
    jetTab W B p (c • f) x y = c • jetTab W B p f x y := by
  funext k
  simp only [jetTab, kerFin, fockIn, GridData.Weil.ker, thetaKO, Pi.smul_apply]
  rw [GlobalTheory.FiniteFock.pureTensorO_smul, map_smul, Pi.smul_apply]

def fockLin (W : G.Weil) (B : VertexFrames G) (p : Pair T) (x : FinPt G p.small) (y : FinPt G p.big) :
    thSub W p →ₗ[ℂ] (VV ℂ (wt G p.small) →ₗ[ℂ] VV ℂ (wt G p.big)) where
  toFun f := fockComp W B p f x y
  map_add' f f' := by
    ext1 v
    simp only [fockComp, Submodule.coe_add]
    rw [jetTab_add W B p f.2 f'.2]
    simp only [Formalism.L2.Ker.jetOp, Formalism.L2.Ker.jetMap, jetLin_add, LinearMap.comp_apply, LinearMap.add_apply, map_add (f := _)]
  map_smul' c f := by
    ext1 v
    simp only [fockComp, Submodule.coe_smul]
    rw [jetTab_smul]
    simp only [Formalism.L2.Ker.jetOp, Formalism.L2.Ker.jetMap, jetLin_smul, LinearMap.comp_apply, LinearMap.smul_apply, map_smul,
      RingHom.id_apply]

variable {W : G.Weil} {U : Set T}

theorem col_multilinear (S : GridChoice W U) (t : T) (x : ∀ j, FinPt G (.top j)) (Ψ₀ : VV ℂ (wt G (.top 0))) :
    ∃ M : (∀ j : Fin D.R.m, thSub W (.top t j)) →ₘₗ[ℂ] VV ℂ (wt G (.top D.R.m)),
      ∀ fs, M fs = colMapV S (fun j => (fs j : WO (G.pS (.top t j)) (G.pT (.top t j)) → ℂ)) x Ψ₀ := by
  obtain ⟨Mc, hc⟩ := chain_multilinear (V := fun j => VV ℂ (wt G (.top j))) D.R.m
    (fun j : Fin D.R.m => thSub W (.top t j))
    (fun j => S.Z.scal 1 (.top t j) • fockLin W S.N.frC (.top t j) (x j * S.N.u _) (x (j + 1) * S.N.u _))
  refine ⟨(LinearMap.applyₗ (R := ℂ) (rhoVr (tauE D) _ (S.N.fr (.top 0))⁻¹ Ψ₀)).compMultilinearMap Mc, fun fs => ?_⟩
  show Mc fs _ = _
  rw [hc]
  refine LinearMap.congr_fun (chainTo_congr (V := fun j => VV ℂ (wt G (.top j))) D.R.m fun j hj => ?_) _
  exact dite_congr rfl (fun _ => rfl) (fun _ => rfl)

theorem row_multilinear (S : GridChoice W U) (y : ∀ i, FinPt G (.grid i D.R.m))
    (F₀ : VV ℂ (listedWt G (.grid 0 D.R.m))) :
    ∃ M : (∀ i : Fin D.R.m, thSub W (.chi i D.R.m : Pair T)) →ₘₗ[ℂ] VV ℂ (wt G (.grid D.R.m D.R.m)),
      ∀ gs, M gs =
        rowMapV S (fun i => (gs i : WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ)) y F₀ := by
  obtain ⟨Mr, hr⟩ := chain_multilinear (V := fun i => VV ℂ (wt G (.grid i D.R.m))) D.R.m
    (fun i : Fin D.R.m => thSub W (.chi i D.R.m : Pair T))
    (fun i => S.Z.scal 1 (.chi i D.R.m : Pair T) •
      fockLin W S.N.frC (.chi i D.R.m : Pair T) (y i * S.N.u _) (y (i + 1) * S.N.u _))
  refine ⟨(LinearMap.applyₗ (R := ℂ)
    (rhoVr (tauE D) _ (S.N.fr (.grid 0 D.R.m))⁻¹ (funOf (listedWt G (.grid 0 D.R.m)) F₀))).compMultilinearMap Mr,
    fun gs => ?_⟩
  show Mr gs _ = _
  rw [hr]
  refine LinearMap.congr_fun (chainTo_congr (V := fun i => VV ℂ (wt G (.grid i D.R.m))) D.R.m fun j hj => ?_) _
  exact dite_congr rfl (fun _ => rfl) (fun _ => rfl)

theorem pairing_multilinear {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) (t : T) (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m))
    (Ψ₀ : VV ℂ (wt G (.top 0))) (F₀ : VV ℂ (listedWt G (.grid 0 D.R.m))) :
    ∃ M : (∀ j : Fin D.R.m, thSub W (.top t j)) →ₘₗ[ℂ]
        ((∀ i : Fin D.R.m, thSub W (.chi i D.R.m : Pair T)) →ₘₗ[ℂ] ℂ),
      ∀ fs gs, M fs gs = (brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m))).compl₁₂
        (colMapV S (fun j => (fs j : WO (G.pS (.top t j)) (G.pT (.top t j)) → ℂ)) x)
        (rowMapV S (fun i => (gs i : WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ)) y) Ψ₀ F₀ := by
  exact compl_multilinear (brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m)))
    (fun fs : ∀ j : Fin D.R.m, thSub W (.top t j) =>
      colMapV S (fun j => (fs j : WO (G.pS (.top t j)) (G.pT (.top t j)) → ℂ)) x)
    (fun gs : ∀ i : Fin D.R.m, thSub W (.chi i D.R.m : Pair T) =>
      rowMapV S (fun i => (gs i : WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ)) y) Ψ₀ F₀
    (col_multilinear S t x Ψ₀) (row_multilinear S y F₀)

end GlobalTheory.ArrowMultilinear
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMultilinearColumnRowKernelPairingStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.LastVertexInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_multilinear_columnRowKernelPairing : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) (t : T) (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) (Ψ₀ : VV ℂ (wt G (.top 0))) (F₀ : VV ℂ (listedWt G (.grid 0 D.R.m))),
    ∃ M : MultilinearMap (RingHom.id ℂ) (fun j : Fin D.R.m => thSub W (.top t j))
        (MultilinearMap (RingHom.id ℂ) (fun i : Fin D.R.m => thSub W (.chi i D.R.m : Pair T)) ℂ),
      ∀ fs gs, M fs gs = (brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m))).compl₁₂
        (colMapV S (fun j => (fs j : WO (G.pS (.top t j)) (G.pT (.top t j)) → ℂ)) x)
        (rowMapV S (fun i => (gs i : WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ)) y) Ψ₀ F₀ := by
  intro D T L sc G W U S t x y Ψ₀ F₀
  have chain {V : ℕ → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)] :
      ∀ (m : ℕ) (A : Fin m → Type) [∀ j, AddCommGroup (A j)] [∀ j, Module ℂ (A j)]
        (k : ∀ j : Fin m, A j →ₗ[ℂ] (V j →ₗ[ℂ] V (j + 1))),
        ∃ M : MultilinearMap (RingHom.id ℂ) A (V 0 →ₗ[ℂ] V m), ∀ fs,
          M fs = chainTo (fun j => if h : j < m then k ⟨j, h⟩ (fs ⟨j, h⟩) else 0) m := by
    intro m
    induction m with
    | zero =>
      intro A _ _ k
      exact ⟨MultilinearMap.constOfIsEmpty (RingHom.id ℂ) A LinearMap.id, fun _ => rfl⟩
    | succ m ih =>
      intro A _ _ k
      obtain ⟨M, hM⟩ := ih (fun j => A j.castSucc) (fun j => k j.castSucc)
      let kl : A (Fin.last m) →ₗ[ℂ] (V m →ₗ[ℂ] V (m + 1)) := k (Fin.last m)
      refine ⟨MultilinearMap.uncurryRight
        (((LinearMap.llcomp ℂ (V 0) (V m) (V (m + 1)) ∘ₗ kl).flip).compMultilinearMap M),
        fun fs => ?_⟩
      show kl (fs (Fin.last m)) ∘ₗ M (Fin.init fs) = _ ∘ₗ chainTo _ m
      rw [hM]
      beta_reduce
      rw [dite_eq_left (Nat.lt_succ_self m)]
      congr 1
      refine GlobalTheory.ArrowMultilinear.chainTo_congr m fun j hj => ?_
      rw [dite_eq_left hj, dite_eq_left (Nat.lt_succ_of_lt hj)]
      rfl
  obtain ⟨Mc, hc⟩ := chain (V := fun j => VV ℂ (wt G (.top j))) D.R.m
    (fun j : Fin D.R.m => thSub W (.top t j))
    (fun j => S.Z.scal 1 (.top t j) •
      GlobalTheory.ArrowMultilinear.fockLin W S.N.frC (.top t j)
        (x j * S.N.u _) (x (j + 1) * S.N.u _))
  obtain ⟨Mr, hr⟩ := chain (V := fun i => VV ℂ (wt G (.grid i D.R.m))) D.R.m
    (fun i : Fin D.R.m => thSub W (.chi i D.R.m : Pair T))
    (fun i => S.Z.scal 1 (.chi i D.R.m : Pair T) •
      GlobalTheory.ArrowMultilinear.fockLin W S.N.frC (.chi i D.R.m : Pair T)
        (y i * S.N.u _) (y (i + 1) * S.N.u _))
  let col := (LinearMap.applyₗ (R := ℂ) (rhoVr (tauE D) _ (S.N.fr (.top 0))⁻¹ Ψ₀)).compMultilinearMap Mc
  let row := (LinearMap.applyₗ (R := ℂ)
    (rhoVr (tauE D) _ (S.N.fr (.grid 0 D.R.m))⁻¹ (funOf (listedWt G (.grid 0 D.R.m)) F₀))).compMultilinearMap Mr
  have hcol (fs : ∀ j : Fin D.R.m, thSub W (.top t j)) :
      col fs = colMapV S (t := t) (fun j => (fs j : WO _ _ → ℂ)) x Ψ₀ := by
    show Mc fs _ = _
    rw [hc]
    refine LinearMap.congr_fun (GlobalTheory.ArrowMultilinear.chainTo_congr
      (V := fun j => VV ℂ (wt G (.top j))) D.R.m fun j hj => ?_) _
    exact dite_congr rfl (fun _ => rfl) (fun _ => rfl)
  have hrow (gs : ∀ i : Fin D.R.m, thSub W (.chi i D.R.m : Pair T)) :
      row gs = rowMapV S (fun i => (gs i : WO _ _ → ℂ)) y F₀ := by
    show Mr gs _ = _
    rw [hr]
    refine LinearMap.congr_fun (GlobalTheory.ArrowMultilinear.chainTo_congr
      (V := fun i => VV ℂ (wt G (.grid i D.R.m))) D.R.m fun j hj => ?_) _
    exact dite_congr rfl (fun _ => rfl) (fun _ => rfl)
  let β := brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m))
  let pairWithRow : VV ℂ (wt G (.top D.R.m)) →ₗ[ℂ]
      MultilinearMap (RingHom.id ℂ) (fun i : Fin D.R.m => thSub W (.chi i D.R.m : Pair T)) ℂ :=
    { toFun := fun v => (β v).compMultilinearMap row
      map_add' := fun v v' => by
        ext gs
        change β (v + v') (row gs) = β v (row gs) + β v' (row gs)
        simp only [map_add]
        rfl
      map_smul' := fun c v => by
        ext gs
        change β (c • v) (row gs) = c • β v (row gs)
        simp only [map_smul]
        rfl }
  refine ⟨pairWithRow.compMultilinearMap col, fun fs gs => ?_⟩
  show β (col fs) (row gs) = _
  rw [hcol, hrow]
  rfl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalizedKernelOfVectorSmul
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalizedKernelOfVectorSmul
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.TopZeroInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.TopZeroInv

theorem kkVec_smul : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) (p : Pair T) (c : ℂ) (f : WO (G.pS p) (G.pT p) → ℂ) (x : FinPt G p.small) (y : FinPt G p.big),
    kkVec S p (c • f) x y = c • kkVec S p f x y := by
  intro D T L sc G W U S p c f x y
  unfold GlobalTheory.TopZeroInv.kkVec fockComp
  have hT : jetTab W S.N.frC p (c • f) (x * S.N.u _) (y * S.N.u _) =
      c • jetTab W S.N.frC p f (x * S.N.u _) (y * S.N.u _) := by
    funext k
    simp only [jetTab, kerFin, fockIn, GlobalTheory.FiniteFock.pureTensorO_smul, Pi.smul_apply, smul_eq_mul,
      GlobalTheory.ChiGrid.GridData.Weil.ker, thetaKO, map_smul]
  have h := (GlobalTheory.JetIdentity.jetOpL (K := ℂ) (wt G p.small) (wt G p.big) (nuEnd G p)).map_smul c
    (jetTab W S.N.frC p f (x * S.N.u _) (y * S.N.u _))
  simp only [GlobalTheory.JetIdentity.jetOpL, LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply] at h
  rw [hT, h, smul_comm]

end GlobalTheory.TopZeroInv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalizedKernelOfVectorSmulStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.TopZeroInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalizedKernelOfVector_smul : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) (p : Pair T) (c : ℂ) (f : WO (G.pS p) (G.pT p) → ℂ) (x : FinPt G p.small) (y : FinPt G p.big),
    kkVec S p (c • f) x y = c • kkVec S p f x y := by
  first | exact @GlobalTheory.TopZeroInv.kkVec_smul | exact GlobalTheory.TopZeroInv.kkVec_smul | (intros; apply GlobalTheory.TopZeroInv.kkVec_smul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspFormsOfVertexTypeZeroMemAndSmulMem
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspFormsOfVertexTypeZeroMemAndSmulMem
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
open Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.SeriesToClosure GlobalTheory.PlaceDecomp GlobalTheory.KFinDecomp Matrix
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.PlaceDecomp

theorem cls_zero_smul : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (N : GlobalTheory.Grid.Node D) (U : Subgroup (GA D N.V)), (0 : GA D N.V → ℂ) ∈ Cls θ N U ∧ ∀ (c : ℂ) (f : GA D N.V → ℂ), f ∈ Cls θ N U → c • f ∈ Cls θ N U := by
  intro D θ _ N U
  refine ⟨⟨⟨Formalism.IndefR.Mult.isAutFunSm_zero θ N.V, Formalism.IndefR.Mult.isCuspFun_zero N.V, fun τ =>
      (GlobalTheory.TypeAtTest.isTypeAt_zero θ N.V).2
        ⟨N.M.H τ, _, _, N.M.σ τ, N.M.lam τ, N.M.ε τ, N.M.fr τ, N.M.enum τ, N.M.ds τ, N.M.fr_unit τ, N.M.fr_gram τ⟩⟩,
      fun _ _ _ _ => rfl⟩, fun c f hf => ?_⟩
  obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hf
  refine ⟨⟨Formalism.IndefR.Mult.isAutFunSm_smul θ N.V h1 c, Formalism.IndefR.Mult.isCuspFun_smul N.V h2 c,
    fun τ => GlobalTheory.Mem.Th.isTypeAt_smul c (h3 τ)⟩, fun k hk hk' g => ?_⟩
  simp only [Pi.smul_apply, h4 k hk hk' g]

end GlobalTheory.PlaceDecomp

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspFormsOfVertexTypeZeroMemAndSmulMemStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
open Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.SeriesToClosure GlobalTheory.PlaceDecomp GlobalTheory.KFinDecomp Matrix
open scoped InnerProductSpace

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspFormsOfVertexType_zero_mem_and_smul_mem : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (N : GlobalTheory.Grid.Node D) (U : Subgroup (GA D N.V)), (0 : GA D N.V → ℂ) ∈ Cls θ N U ∧ ∀ (c : ℂ) (f : GA D N.V → ℂ), f ∈ Cls θ N U → c • f ∈ Cls θ N U := by
  first | exact @GlobalTheory.PlaceDecomp.cls_zero_smul | exact GlobalTheory.PlaceDecomp.cls_zero_smul | (intros; apply GlobalTheory.PlaceDecomp.cls_zero_smul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalApproxFinitePointVacuumLevel
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Datum ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.NTheta (IsIdemAt)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.FinApprox

variable {D : D7}

def finRat (D : D7) : D.host.E →+ AE D := TensorProduct.mk D.host.F (AF D.host.F) D.host.E (pairA D.host.F 0 1)

theorem finRat_apply (a : D.host.E) : finRat D a = pairA D.host.F 0 1 ⊗ₜ[D.host.F] a := rfl

theorem finRat_eq (a : D.host.E) : incA D a - pairA D.host.F 1 0 ⊗ₜ[D.host.F] a = finRat D a := by
  have h1 : (1 : AF D.host.F) = pairA D.host.F 1 0 + pairA D.host.F 0 1 :=
    Prod.ext (add_zero (1 : Ainf D.host.F)).symm (zero_add (1 : Af D.host.F)).symm
  rw [finRat_apply]
  show (1 : AF D.host.F) ⊗ₜ[D.host.F] a - _ = _
  rw [h1, TensorProduct.add_tmul, add_sub_cancel_left]

private theorem infPart_tmul' (a : AF D.host.F) (e : D.host.E) :
    infPart D (a ⊗ₜ[D.host.F] e) = fstA D.host.F a ⊗ₜ[D.host.F] e := by
  show Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) (a ⊗ₜ[D.host.F] e) = _
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]

theorem infPart_finRat (a : D.host.E) : infPart D (finRat D a) = 0 := by
  rw [finRat_apply, infPart_tmul']
  have h0 : fstA D.host.F (pairA D.host.F 0 1) = 0 := rfl
  rw [h0, TensorProduct.zero_tmul]

private theorem exists_witt_eq_teich_add_p_teich_frob_symm_add_p_sq_mul (w : AE D) :
    w = ∑ i, (Algebra.TensorProduct.basis (AF D.host.F) (Module.finBasis D.host.F D.host.E)).repr w i ⊗ₜ[D.host.F] Module.finBasis D.host.F D.host.E i := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis (AF D.host.F) (Module.finBasis D.host.F D.host.E)).sum_repr w]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

private theorem fstA_basis_repr_eq_zero_of_infPart_eq_zero {z : AE D} (hz : infPart D z = 0) (i : Fin (Module.finrank D.host.F D.host.E)) :
    fstA D.host.F ((Algebra.TensorProduct.basis (AF D.host.F) (Module.finBasis D.host.F D.host.E)).repr z i) = 0 := by
  have h1 : infPart D z = ∑ j, fstA D.host.F ((Algebra.TensorProduct.basis (AF D.host.F) (Module.finBasis D.host.F D.host.E)).repr z j) •
      Algebra.TensorProduct.basis (Ainf D.host.F) (Module.finBasis D.host.F D.host.E) j := by
    conv_lhs => rw [exists_witt_eq_teich_add_p_teich_frob_symm_add_p_sq_mul z]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [infPart_tmul', Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have h2 := congrArg
    (fun v => (Algebra.TensorProduct.basis (Ainf D.host.F) (Module.finBasis D.host.F D.host.E)).repr v i) h1
  simp only [hz, map_zero, Finsupp.coe_zero, Pi.zero_apply, Module.Basis.repr_sum_self] at h2
  exact h2.symm

private theorem eq_sum_pairA_zero_tmul_finBasis_of_infPart_eq_zero {z : AE D} (hz : infPart D z = 0) :
    z = ∑ i, pairA D.host.F 0 (sndA D.host.F ((Algebra.TensorProduct.basis (AF D.host.F) (Module.finBasis D.host.F D.host.E)).repr z i)) ⊗ₜ[D.host.F] Module.finBasis D.host.F D.host.E i := by
  conv_lhs => rw [exists_witt_eq_teich_add_p_teich_frob_symm_add_p_sq_mul z]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  exact Prod.ext (fstA_basis_repr_eq_zero_of_infPart_eq_zero hz i) rfl

theorem mem_closure_finRat {z : AE D} (hz : infPart D z = 0) : z ∈ closure (Set.range (finRat D)) := by
  have hd : DenseRange (Pi.map fun _ : Fin (Module.finrank D.host.F D.host.E) =>
      ⇑(algebraMap D.host.F (Af D.host.F))) :=
    DenseRange.piMap fun _ => AdeleCharTwist.denseRange_fin
  have hc : Continuous fun y : Fin (Module.finrank D.host.F D.host.E) → Af D.host.F =>
      ∑ i, pairA D.host.F 0 (y i) ⊗ₜ[D.host.F] Module.finBasis D.host.F D.host.E i := by
    refine continuous_finsetSum _ fun i _ => ?_
    have h1 : Continuous fun a : AF D.host.F => a ⊗ₜ[D.host.F] Module.finBasis D.host.F D.host.E i := by
      have he : (fun a : AF D.host.F => a ⊗ₜ[D.host.F] Module.finBasis D.host.F D.host.E i) =
          fun a => a • ((1 : AF D.host.F) ⊗ₜ[D.host.F] Module.finBasis D.host.F D.host.E i) := by
        funext a
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [he]
      exact Continuous.smul (M := AF D.host.F) (X := AE D) continuous_id continuous_const
    have h2 : Continuous fun y : Fin (Module.finrank D.host.F D.host.E) → Af D.host.F => pairA D.host.F 0 (y i) := by
      show Continuous fun y : Fin (Module.finrank D.host.F D.host.E) → Af D.host.F => ((0 : Ainf D.host.F), y i)
      exact continuous_const.prodMk (continuous_apply i)
    exact h1.comp h2
  have hm : Set.MapsTo (fun y : Fin (Module.finrank D.host.F D.host.E) → Af D.host.F =>
      ∑ i, pairA D.host.F 0 (y i) ⊗ₜ[D.host.F] Module.finBasis D.host.F D.host.E i)
      (Set.range (Pi.map fun _ : Fin (Module.finrank D.host.F D.host.E) => ⇑(algebraMap D.host.F (Af D.host.F))))
      (Set.range (finRat D)) := by
    rintro _ ⟨q, rfl⟩
    refine ⟨∑ i, q i • Module.finBasis D.host.F D.host.E i, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [finRat_apply, ← TensorProduct.smul_tmul]
    congr 1
    exact Prod.ext (smul_zero (q i)) ((Algebra.smul_def (q i) (1 : Af D.host.F)).trans (mul_one _))
  have hz' := map_mem_closure hc (hd fun i => sndA D.host.F ((Algebra.TensorProduct.basis (AF D.host.F) (Module.finBasis D.host.F D.host.E)).repr z i)) hm
  rw [eq_sum_pairA_zero_tmul_finBasis_of_infPart_eq_zero hz]
  exact hz'

theorem mem_closure_mat {m n : ℕ} {y : Mx D m n} (hy : y.map (infPart D) = 0) :
    y ∈ closure (Set.range fun ℓ : Matrix (Fin m) (Fin n) D.host.E => (ℓ.map (finRat D) : Mx D m n)) := by
  have h1 : ∀ i j, y i j ∈ closure (Set.range (finRat D)) := fun i j =>
    mem_closure_finRat (by simpa using congrFun (congrFun hy i) j)
  have h2 : (y : Fin m → Fin n → AE D) ∈
      closure (Set.univ.pi fun _ : Fin m => Set.univ.pi fun _ : Fin n => Set.range (finRat D)) := by
    refine mem_closure_pi.mpr fun i _ => ?_
    refine mem_closure_pi.mpr fun j _ => ?_
    exact h1 i j
  refine closure_mono ?_ h2
  intro x hx
  have hx' : ∀ i j, ∃ a, finRat D a = x i j := fun i j => hx i (Set.mem_univ i) j (Set.mem_univ j)
  choose ℓ hℓ using hx'
  exact ⟨Matrix.of ℓ, by ext i j; exact hℓ i j⟩

theorem actO_fin {S T : HSp D} (g : GA D S) (h : GA D T) {x : WO S T} (hx : x.map (infPart D) = 0) :
    (actO S T g h x).map (infPart D) = 0 := by
  unfold actO
  rw [Matrix.map_mul, Matrix.map_mul, hx, Matrix.mul_zero, Matrix.zero_mul]

private theorem continuous_actO_one {S T : HSp D} (h : GA D T) : Continuous (actO S T 1 h) := by
  haveI := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  unfold actO
  fun_prop

theorem exists_approx {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (g : GA D T) {x : WO S T} (hx : x.map (infPart D) = 0) :
    ∃ (ℓ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (w : WO S T), w.map (infPart D) = 0 ∧ heisO ψ S T w f = f ∧
      x = actO S T 1 g⁻¹ (ratW T S ℓ - GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt S T ℓ) + w := by
  haveI := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  obtain ⟨U, hUo, hU⟩ := hf.level
  have hy : (actO S T 1 g x).map (infPart D) = 0 := actO_fin 1 g hx
  have hVo : IsOpen {v : WO S T | actO S T 1 g⁻¹ (actO S T 1 g x - v) ∈ U} :=
    hUo.preimage ((continuous_actO_one (S := S) g⁻¹).comp (continuous_const.sub continuous_id))
  have h0 : actO S T 1 g⁻¹ 0 = 0 := by
    have h00 := GlobalTheory.HeckeVacuum.act_sub g⁻¹ (0 : WO S T) 0
    rwa [sub_self, sub_self] at h00
  have hyV : actO S T 1 g x ∈ {v : WO S T | actO S T 1 g⁻¹ (actO S T 1 g x - v) ∈ U} := by
    show actO S T 1 g⁻¹ (actO S T 1 g x - actO S T 1 g x) ∈ U
    rw [sub_self, h0]
    exact U.zero_mem
  obtain ⟨_, hvV, ℓ, rfl⟩ := mem_closure_iff.mp (mem_closure_mat (m := T.rank) (n := S.rank) hy) _ hVo hyV
  have hrat : ratW T S ℓ - GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt S T ℓ = (ℓ.map (finRat D) : WO S T) := by
    ext i j
    exact finRat_eq (ℓ i j)
  have key : actO S T 1 g⁻¹ (ratW T S ℓ - GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt S T ℓ) =
      actO S T 1 g⁻¹ (ℓ.map (finRat D)) := congrArg _ hrat
  have hw : (actO S T 1 g⁻¹ (actO S T 1 g x - ℓ.map (finRat D))).map (infPart D) = 0 := by
    refine actO_fin 1 g⁻¹ ?_
    ext i j
    have hij : infPart D (actO S T 1 g x i j) = 0 := by simpa using congrFun (congrFun hy i) j
    simp [hij, infPart_finRat]
  refine ⟨ℓ, actO S T 1 g⁻¹ (actO S T 1 g x - ℓ.map (finRat D)), hw,
    hU (actO S T 1 g⁻¹ (actO S T 1 g x - ℓ.map (finRat D))) hvV hw, ?_⟩
  rw [key, GlobalTheory.HeckeVacuum.act_sub, add_sub_cancel, ← GlobalTheory.HeckeVacuum.act_mul, inv_mul_cancel,
    GlobalTheory.HeckeVacuum.act_one]

theorem exists_rat_approx : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F),
    R.toLevCh.Is A.μ0 → R.IsFam → R.IsThP → ∀ (i : Fin D.R.m) (g : GA D (Wc D i)) (x : WO (Vc D i) (Wc D i)),
    x.map (infPart D) = 0 → ∃ (ℓ : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E) (w : WO (Vc D i) (Wc D i)),
      w.map (infPart D) = 0 ∧ heisO R.ψ (Vc D i) (Wc D i) w (R.vacP i) = R.vacP i ∧
      x = actO (Vc D i) (Wc D i) 1 g⁻¹ (ratW (Wc D i) (Vc D i) ℓ - GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) ℓ) + w := by
  intro D G _ _ Pl0 T0 A T _ R _ _ hP i g x hx
  exact exists_approx (hP.vP i A.μ0).1.2.theta g hx

end GlobalTheory.FinApprox
end
end
