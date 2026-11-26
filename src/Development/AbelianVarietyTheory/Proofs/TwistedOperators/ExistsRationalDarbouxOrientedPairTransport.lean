module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyPcRatFMem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicIsometries
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedThetaSeriesRapidDecay
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsParPinsCanon
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.CurveOverOfRayField

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalDarbouxOrientedPairTransport
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalDarbouxOrientedPairTransport
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.SquareAgree

theorem hTens_eq_trace {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) {α β : Type} [Fintype α]
    [Fintype β] (JA : Matrix α α A) (JB : Matrix β β A) (x y : Matrix α β A) :
    GlobalTheory.WeilM.hTens c JA JB x y = (xᵀ * JA * y.map c * JBᵀ).trace := by
  simp only [GlobalTheory.WeilM.hTens, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  calc ∑ i, ∑ k, ∑ l, x i j * JA i k * JB j l * c (y k l)
      = ∑ i, ∑ l, ∑ k, x i j * JA i k * JB j l * c (y k l) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ l, ∑ i, ∑ k, x i j * JA i k * JB j l * c (y k l) := Finset.sum_comm
    _ = ∑ l, ∑ k, ∑ i, x i j * JA i k * JB j l * c (y k l) :=
        Finset.sum_congr rfl fun l _ => Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ =>
          Finset.sum_congr rfl fun i _ => ?_
        ring

theorem hTens_transpose_mul {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) {α β γ : Type}
    [Fintype α] [Fintype β] [Fintype γ] [DecidableEq β] (e : α ≃ γ) (K : Matrix α α A) {G H : Matrix β β A} (x : A)
    (hGH : H * G = 1) (hG : G.map c = Gᵀ) (u u' : Matrix β γ A) :
    GlobalTheory.WeilM.hTens c Kᵀ (x • H) (uᵀ.submatrix e id * G) (u'ᵀ.submatrix e id * G) =
      -GlobalTheory.WeilM.hTens c (-G) (x • reindex e e Kᵀ) u u' := by
  have hHG : Gᵀ * Hᵀ = 1 := by rw [← Matrix.transpose_mul, hGH, Matrix.transpose_one]
  have hmap : (u'ᵀ.submatrix e id * G).map c = (u'ᵀ.submatrix e id).map c * Gᵀ := by
    rw [← hG]
    exact Matrix.map_mul (f := (c : A →+* A))
  have hM : ((u'ᵀ.submatrix e id).map c)ᵀ * K * uᵀ.submatrix e id = u'.map c * reindex e e K * uᵀ := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.submatrix_apply, id,
      Matrix.reindex_apply]
    refine Fintype.sum_equiv e _ _ fun a => ?_
    congr 1
    exact Fintype.sum_equiv e _ _ fun b => by simp
  rw [hTens_eq_trace, hTens_eq_trace, hmap, Matrix.transpose_mul, Matrix.transpose_smul]
  calc (Gᵀ * (uᵀ.submatrix e id)ᵀ * Kᵀ * ((u'ᵀ.submatrix e id).map c * Gᵀ) * (x • Hᵀ)).trace
      = x * (Gᵀ * (uᵀ.submatrix e id)ᵀ * Kᵀ * (u'ᵀ.submatrix e id).map c * (Gᵀ * Hᵀ)).trace := by
        rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
        simp only [Matrix.mul_assoc]
    _ = x * (Gᵀ * (uᵀ.submatrix e id)ᵀ * Kᵀ * (u'ᵀ.submatrix e id).map c).trace := by
        rw [hHG, Matrix.mul_one]
    _ = x * (((u'ᵀ.submatrix e id).map c)ᵀ * K * uᵀ.submatrix e id * G).trace := by
        congr 1
        rw [← Matrix.trace_transpose]
        simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    _ = x * (u'.map c * reindex e e K * uᵀ * G).trace := by rw [hM]
    _ = x * (uᵀ * G * u'.map c * reindex e e K).trace := by
        rw [Matrix.mul_assoc (u'.map c * reindex e e K), Matrix.trace_mul_comm]
        simp only [Matrix.mul_assoc]
    _ = -((uᵀ * -G * u'.map c * (x • reindex e e Kᵀ)ᵀ).trace) := by
        rw [Matrix.transpose_smul, Matrix.transpose_reindex, Matrix.transpose_transpose, Matrix.mul_neg,
          Matrix.neg_mul, Matrix.neg_mul, Matrix.mul_smul, Matrix.trace_neg, Matrix.trace_smul, neg_neg,
          smul_eq_mul]

theorem exists_darboux_transpose_mul {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A)
    {α β γ κ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype κ] [DecidableEq β] (e : α ≃ γ) (K : Matrix α α A)
    {G H : Matrix β β A} (x : A) (hGH : H * G = 1) (hG : G.map c = Gᵀ) {JV JB : Matrix β β A} {JW : Matrix γ γ A}
    {JA : Matrix α α A} (hV : JV = -G) (hW : JW = x • reindex e e Kᵀ) (hA : JA = Kᵀ) (hB : JB = x • H)
    (M : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c (-1) JV JW) κ) (T : Matrix β γ A ≃+ Matrix α β A)
    (hT : ∀ u, T u = uᵀ.submatrix e id * G) :
    ∃ co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c 1 JA JB) κ, ∀ u, co.e (T u) = M.e u := by
  subst hV hW hA hB
  have hsmul : ∀ (r : R) (u : Matrix β γ A), T (r • u) = r • T u := by
    intro r u
    rw [hT, hT, Matrix.transpose_smul]
    exact Matrix.smul_mul r (uᵀ.submatrix e id) G
  have h1 : ∀ v, (T.toLinearEquiv hsmul).symm (T v) = v := fun v => (T.toLinearEquiv hsmul).symm_apply_apply v
  refine ⟨{ e := (T.toLinearEquiv hsmul).symm.trans M.e, form := ?_ }, ?_⟩
  · intro w w'
    obtain ⟨u, rfl⟩ := T.surjective w
    obtain ⟨u', rfl⟩ := T.surjective w'
    simp only [LinearEquiv.trans_apply]
    rw [h1, h1, ← M.form]
    simp only [GlobalTheory.WeilM.symp]
    rw [hT, hT, hTens_transpose_mul c e K x hGH hG, one_mul, neg_one_mul]
  · intro u
    simp only [LinearEquiv.trans_apply]
    rw [h1]

theorem map_transpose_inv_mul {E A : Type} [CommRing E] [CommRing A] (f : E →+* A) {α β γ : Type} [Fintype β]
    [DecidableEq β] (e : α ≃ γ) (x : Matrix α β E) {G : Matrix β β E} (hG : IsUnit G.det) :
    (((x * G⁻¹)ᵀ.submatrix id e.symm).map f)ᵀ.submatrix e id * G.map f = x.map f := by
  have h1 : (((x * G⁻¹)ᵀ.submatrix id e.symm).map f)ᵀ.submatrix e id = (x * G⁻¹).map f := by
    ext a b
    simp only [Matrix.map_apply, Matrix.transpose_apply, Matrix.submatrix_apply, id_eq, Equiv.symm_apply_apply]
  rw [h1, ← Matrix.map_mul, Matrix.mul_assoc, Matrix.nonsing_inv_mul G hG, Matrix.mul_one]

private theorem symp_smul_eq_symp_one_smul {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) {α β : Type}
    [Fintype α] [Fintype β] (ξ : A) (JA : Matrix α α A) (JB : Matrix β β A) (w w' : Matrix α β A) :
    GlobalTheory.WeilM.symp c ξ JA JB w w' = GlobalTheory.WeilM.symp c 1 JA (ξ • JB) w w' := by
  simp only [GlobalTheory.WeilM.symp, GlobalTheory.WeilM.hTens, one_mul, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun l _ => ?_
  ring


set_option maxHeartbeats 800000 in
theorem exists_darboux_transport : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
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
      ∃ (ξ : AF D.host.F ⊗[D.host.F] D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F X.gramᵀ)
          (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F JB)) (Fin S.rank × Fin d)),
        ξ • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F JB = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • (sgn ε S).gram⁻¹) ∧
        (∀ x : Matrix (Fin X.rank) (Fin S.rank) D.host.E, ∃ y z : Fin S.rank × Fin d → D.host.F,
          co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F x) =
            (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) ∧
        ∀ (Φ : (Fin S.rank × Fin d → AF D.host.F) → ℂ) (f : WO S X → ℂ),
          IsDatum M ψ cS Φ f ↔
            Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin S.rank × Fin d) ∧ GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ = f := by
  intro D ψ θ _ ε S X A B d e Bs _ _ Vs Ws r s r' s' hJ hJW hV _ _ M hM cS hcS
  have hsgn : (sgn ε S).gram = (if ε then -1 else 1 : D.host.E) • S.gram := by
    cases ε <;> ext i j <;> simp [Formalism.BasicNotions.HSpace.gram]
  have hdet : IsUnit (sgn ε S).gram.det := isUnit_iff_ne_zero.mpr (Formalism.L2.Theta.gram_det_ne _)
  have hG0 : (sgn ε S).gram = -Vs.J := by
    rw [hsgn, hJ]
    cases ε <;> simp
  have hmapc : ∀ {m n : Type} (J : Matrix m n D.host.E),
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F J).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) =
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (J.map D.sp.cm.sig) := by
    intro m n J
    ext i j
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR]
  have hGJ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Vs.J = -GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (sgn ε S).gram := by
    rw [hG0]
    ext i j
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM]
  have hG : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (sgn ε S).gram).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) =
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (sgn ε S).gram)ᵀ := by
    rw [hmapc, hG0]
    ext i j
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, hV.herm]
  have hGH : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F ((sgn ε S).gram)⁻¹ * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (sgn ε S).gram = 1 := by
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM]
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hdet, Matrix.map_one _ (map_zero _) (map_one _)]
  have hW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Ws.J = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := D.host.F) (AF D.host.F) D.host.xi0 •
      reindex e e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F X.gram)ᵀ := by
    rw [hJW]
    ext i j
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, Matrix.reindex_apply, map_mul]
  have hT : ∀ u, cS u = uᵀ.submatrix e id * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (sgn ε S).gram := by
    intro u
    rw [hcS u, hsgn]
  obtain ⟨co0, hco0⟩ := exists_darboux_transpose_mul (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) e
    (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F X.gram) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := D.host.F) (AF D.host.F) D.host.xi0)
    hGH hG hGJ hW rfl rfl M.co cS hT
  obtain ⟨co, hco⟩ : ∃ co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig)
      (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := D.host.F) (AF D.host.F) D.host.xi0)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F X.gramᵀ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F ((sgn ε S).gram)⁻¹))
      (Fin S.rank × Fin d), (∀ u, co.e (cS u) = M.co.e u) ∧ ∀ w, co.e w = co0.e w := by
    refine ⟨⟨co0.e, fun w w' => ?_⟩, hco0, fun _ => rfl⟩
    rw [← co0.form, symp_smul_eq_symp_one_smul]
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, Matrix.transpose_map]
  refine ⟨Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := D.host.F) (AF D.host.F) D.host.xi0, ((sgn ε S).gram)⁻¹, co, ?_, ?_, ?_⟩
  · ext i j
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, map_mul]
  · intro y
    obtain ⟨a, b, hab⟩ := hM.rat ((y * ((sgn ε S).gram)⁻¹)ᵀ.submatrix id e.symm)
    refine ⟨a, b, ?_⟩
    have hu : cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F ((y * ((sgn ε S).gram)⁻¹)ᵀ.submatrix id e.symm)) =
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F y := by
      rw [hT]
      exact map_transpose_inv_mul _ e y hdet
    rw [← hu, hco.1]
    exact hab
  · intro Φ f
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, funext fun w => ?_⟩
      obtain ⟨u, rfl⟩ := cS.surjective w
      rw [← h2 u]
      simp only [GlobalTheory.WeilSchrodinger.thetaTr, GlobalTheory.WeilM.Darboux.rho, hco.1 u]
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun u => ?_⟩
      rw [← h2]
      simp only [GlobalTheory.WeilSchrodinger.thetaTr, GlobalTheory.WeilM.Darboux.rho, hco.1 u]

end GlobalTheory.SquareAgree

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalDarbouxOrientedPairTransportStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_darboux_orientedPair_transport : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
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
      ∃ (ξ : AF D.host.F ⊗[D.host.F] D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F X.gramᵀ)
          (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F JB)) (Fin S.rank × Fin d)),
        ξ • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F JB = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • (sgn ε S).gram⁻¹) ∧
        (∀ x : Matrix (Fin X.rank) (Fin S.rank) D.host.E, ∃ y z : Fin S.rank × Fin d → D.host.F,
          co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F x) =
            (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) ∧
        ∀ (Φ : (Fin S.rank × Fin d → AF D.host.F) → ℂ) (f : WO S X → ℂ),
          IsDatum M ψ cS Φ f ↔
            Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin S.rank × Fin d) ∧ GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ = f := by
  first | exact @GlobalTheory.SquareAgree.exists_darboux_transport | exact GlobalTheory.SquareAgree.exists_darboux_transport | (intros; apply GlobalTheory.SquareAgree.exists_darboux_transport <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralUnfoldingVariablesMemFieldRange
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralUnfoldingVariablesMemFieldRange
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.LCIntegralField

variable {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]

def stab (f : X → ℂ) : AddSubgroup X where
  carrier := {v | ∀ y, f (y + v) = f y}
  zero_mem' := fun y => by simp
  add_mem' := by
    intro a b (ha : ∀ y, f (y + a) = f y) (hb : ∀ y, f (y + b) = f y) y
    show f (y + (a + b)) = f y
    rw [← add_assoc, hb, ha]
  neg_mem' := by
    intro a (ha : ∀ y, f (y + a) = f y) y
    show f (y + -a) = f y
    have := ha (y + -a)
    rw [neg_add_cancel_right] at this
    exact this.symm

theorem isOpen_stab {f : X → ℂ} (hf : IsLocallyConstant f) (hc : HasCompactSupport f) :
    IsOpen (stab f : Set X) := by
  classical
  have hT : IsCompact (tsupport f) := hc
  haveI : CompactSpace (tsupport f) := isCompact_iff_compactSpace.1 hT
  have hfin : (f '' tsupport f).Finite := by
    have := (hf.comp_continuous (continuous_subtype_val : Continuous (Subtype.val : tsupport f → X))).range_finite
    rwa [Set.range_comp, Subtype.range_coe] at this
  have key : ∀ c ∈ f '' tsupport f, c ≠ 0 → ∀ᶠ v in nhds (0 : X), ∀ y, f y = c → f (y + v) = c := by
    intro c _ hc0
    have hLT : f ⁻¹' {c} ⊆ tsupport f := fun y hy =>
      subset_tsupport f (by rw [Function.mem_support, show f y = c from hy]; exact hc0)
    have hLc : IsCompact (f ⁻¹' {c}) :=
      hT.of_isClosed_subset (isClosed_singleton.preimage hf.continuous) hLT
    obtain ⟨V, hV, hKV⟩ := compact_open_separated_add_right hLc (hf.isOpen_fiber c) subset_rfl
    filter_upwards [hV] with v hv y hy
    exact hKV (Set.add_mem_add hy hv)
  have h1 : ∀ᶠ v in nhds (0 : X), ∀ c ∈ f '' tsupport f, c ≠ 0 → ∀ y, f y = c → f (y + v) = c :=
    (Filter.eventually_all_finite hfin).2 fun c hc => by
      by_cases h0 : c = 0
      · exact Filter.Eventually.of_forall fun _ h => absurd h0 h
      · exact (key c hc h0).mono fun v hv _ => hv
  have h2 := (continuous_neg.tendsto' (0 : X) 0 neg_zero).eventually h1
  refine AddSubgroup.isOpen_of_mem_nhds (g := 0) _ ?_
  filter_upwards [h1, h2] with v hv hv'
  show ∀ y, f (y + v) = f y
  intro y
  by_cases hy : f y = 0
  · by_contra hne
    have hne' : f (y + v) ≠ 0 := by rw [hy] at hne; exact hne
    have hmem : f (y + v) ∈ f '' tsupport f := ⟨y + v, subset_tsupport f hne', rfl⟩
    have := hv' _ hmem hne' (y + v) rfl
    rw [add_neg_cancel_right] at this
    exact hne this.symm
  · exact hv (f y) ⟨y, subset_tsupport f hy, rfl⟩ hy y rfl

theorem discrete_quot (U : AddSubgroup X) (hU : IsOpen (U : Set X)) : DiscreteTopology (X ⧸ U) := by
  rw [discreteTopology_iff_isOpen_singleton]
  intro c
  induction c using QuotientAddGroup.induction_on with
  | H g =>
    have hpre : (QuotientAddGroup.mk : X → X ⧸ U) ⁻¹' {(g : X ⧸ U)} = (fun x => -g + x) ⁻¹' (U : Set X) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe]
      rw [eq_comm, QuotientAddGroup.eq]
    rw [← (QuotientAddGroup.isQuotientMap_mk (N := U)).isOpen_preimage, hpre]
    exact hU.preimage (continuous_const.add continuous_id)

theorem integral_eq_sum [MeasurableSpace X] [OpensMeasurableSpace X] [MeasurableAdd X] (μ : Measure X) [μ.IsAddLeftInvariant]
    (U : AddSubgroup X) (hU : IsOpen (U : Set X)) (hUfin : μ U ≠ ⊤) (g : X → ℂ)
    (hg : ∀ u ∈ U, ∀ y, g (y + u) = g y) (hc : HasCompactSupport g) :
    ∃ s : Finset X, ∫ y, g y ∂μ = (∑ γ ∈ s, g γ) * ((μ.real (U : Set X) : ℝ) : ℂ) := by
  classical
  haveI := discrete_quot U hU
  have hfin : ((QuotientAddGroup.mk : X → X ⧸ U) '' tsupport g).Finite :=
    (hc.isCompact.image QuotientAddGroup.continuous_mk).finite_of_discrete
  set T := hfin.toFinset with hT
  have hind : ∀ (c : X ⧸ U) y, (Quotient.out c : X) = (Quotient.out c : X) →
      (-(Quotient.out c) + y ∈ U ↔ c = (y : X ⧸ U)) := by
    intro c y _
    rw [← QuotientAddGroup.eq, QuotientAddGroup.out_eq']
  have hdec : g = fun y => ∑ c ∈ T,
      ((fun x => -(Quotient.out c) + x) ⁻¹' (U : Set X)).indicator (fun _ => g (Quotient.out c)) y := by
    funext y
    have key : ∀ c : X ⧸ U, ((fun x => -(Quotient.out c) + x) ⁻¹' (U : Set X)).indicator
        (fun _ => g (Quotient.out c)) y = if c = (y : X ⧸ U) then g y else 0 := by
      intro c
      by_cases h : c = (y : X ⧸ U)
      · rw [if_pos h, Set.indicator_of_mem (show y ∈ (fun x => -(Quotient.out c) + x) ⁻¹' (U : Set X) from (hind c y rfl).2 h)]
        have hm : -(Quotient.out c) + y ∈ U := (hind c y rfl).2 h
        have := hg _ hm (Quotient.out c)
        rw [add_neg_cancel_left] at this
        exact this.symm
      · rw [if_neg h, Set.indicator_of_notMem (show y ∉ (fun x => -(Quotient.out c) + x) ⁻¹' (U : Set X) from fun hm => h ((hind c y rfl).1 hm))]
    simp only [key]
    rw [Finset.sum_ite_eq']
    split_ifs with hmem
    · rfl
    · rw [hT, Set.Finite.mem_toFinset] at hmem
      exact image_eq_zero_of_notMem_tsupport (fun hs => hmem ⟨y, hs, rfl⟩)
  have hmeas : ∀ c : X ⧸ U, MeasurableSet ((fun x => -(Quotient.out c) + x) ⁻¹' (U : Set X)) := fun c =>
    (hU.preimage (continuous_const.add continuous_id)).measurableSet
  have hvol : ∀ c : X ⧸ U, μ ((fun x => -(Quotient.out c) + x) ⁻¹' (U : Set X)) = μ U := fun c =>
    measure_preimage_add μ _ _
  refine ⟨T.image Quotient.out, ?_⟩
  rw [Finset.sum_image (fun a _ b _ h => Quotient.out_injective h)]
  conv_lhs => rw [hdec]
  rw [integral_finsetSum]
  · rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [integral_indicator_const _ (hmeas c)]
    simp only [Measure.real, hvol, Complex.real_smul]
    ring
  · intro c _
    refine (integrable_indicator_iff (hmeas c)).2 (integrableOn_const ?_)
    rw [hvol]; exact hUfin

theorem integral_mem_range [MeasurableSpace X] [OpensMeasurableSpace X] [MeasurableAdd X] [T2Space X]
    (μ : Measure X) [μ.IsAddLeftInvariant] (H : Set X) (hHo : IsOpen H) (hHc : IsCompact H) (hH0 : (0 : X) ∈ H)
    (hμH : μ H = 1) {K : Type} [Field K] (σ : K →+* ℂ) (f : X → ℂ) (hf : IsLocallyConstant f)
    (hc : HasCompactSupport f) (hv : ∀ e, f e ∈ Set.range σ) : ∫ e, f e ∂μ ∈ Set.range σ := by
  classical
  set h : X → ℂ := H.indicator (fun _ => 1) with hh
  have hloc : IsLocallyConstant h := by
    refine (IsLocallyConstant.iff_exists_open _).2 fun x => ?_
    by_cases hx : x ∈ H
    · exact ⟨H, hHo, hx, fun y hy => by rw [hh, Set.indicator_of_mem hy, Set.indicator_of_mem hx]⟩
    · exact ⟨Hᶜ, hHc.isClosed.isOpen_compl, hx, fun y hy => by
        rw [hh, Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩
  have hch : HasCompactSupport h := HasCompactSupport.intro hHc fun x hx => Set.indicator_of_notMem hx _
  set U := stab f ⊓ stab h with hU
  have hUo : IsOpen (U : Set X) := by
    rw [hU, AddSubgroup.coe_inf]; exact (isOpen_stab hf hc).inter (isOpen_stab hloc hch)
  have hUH : (U : Set X) ⊆ H := by
    intro u hu
    have h1 := (AddSubgroup.mem_inf.1 hu).2 0
    rw [zero_add] at h1
    by_contra hn
    rw [hh, Set.indicator_of_notMem hn, Set.indicator_of_mem hH0] at h1
    exact zero_ne_one h1
  have hUfin : μ U ≠ ⊤ := ne_top_of_le_ne_top (by rw [hμH]; exact ENNReal.one_ne_top) (measure_mono hUH)
  obtain ⟨s, hs⟩ := integral_eq_sum μ U hUo hUfin f (fun u hu => (AddSubgroup.mem_inf.1 hu).1) hc
  obtain ⟨s', hs'⟩ := integral_eq_sum μ U hUo hUfin h (fun u hu => (AddSubgroup.mem_inf.1 hu).2) hch
  have hint : ∫ y, h y ∂μ = 1 := by
    rw [hh, integral_indicator_const _ hHo.measurableSet]
    simp [Measure.real, hμH]
  rw [hint] at hs'
  have hr := eq_inv_of_mul_eq_one_right hs'.symm
  rw [hs, hr, ← RingHom.coe_fieldRange]
  have hv' : ∀ e, f e ∈ σ.fieldRange := fun e => by rw [← SetLike.mem_coe, RingHom.coe_fieldRange]; exact hv e
  have hh' : ∀ e, h e ∈ σ.fieldRange := fun e => by
    rw [hh, Set.indicator_apply]; split_ifs
    · exact one_mem _
    · exact zero_mem _
  exact mul_mem (sum_mem fun γ _ => hv' γ) (inv_mem (sum_mem fun γ _ => hh' γ))

end GlobalTheory.LCIntegralField

namespace GlobalTheory.LCIntegralField
open GlobalTheory.FunObj ValuativeRel

theorem integral_vars_mem_range : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {G : GlobalTheory.SplitFlip.Grid k} (ν : MeasureTheory.Measure k), GlobalTheory.SplitWeil.IsUnitVol ν → ∀ {K : Type} [Field K] (σ : K →+* ℂ) (f : Vars G → ℂ), IsLocallyConstant f → HasCompactSupport f → (∀ e, f e ∈ Set.range σ) → ∫ e, f e ∂(varsVol G ν) ∈ Set.range σ := by
  intro k _ _ _ _ _ _ G ν hν K _ σ f hf hc hv
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  haveI := hν.1
  haveI : (varsVol G ν).IsAddLeftInvariant := by unfold varsVol; infer_instance
  refine integral_mem_range (varsVol G ν) (Set.univ.pi fun _ => Set.univ.pi fun _ => (𝒪[k] : Set k)) ?_ ?_ ?_ ?_
    σ f hf hc hv
  · exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => Model.isOpen_int
  · exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k 1
  · exact fun _ _ _ _ => zero_mem _
  · simp [varsVol, Measure.pi_pi, hν.2]

end GlobalTheory.LCIntegralField
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralUnfoldingVariablesMemFieldRangeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_unfolding_variables_mem_fieldRange : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {G : GlobalTheory.SplitFlip.Grid k} (ν : MeasureTheory.Measure k), GlobalTheory.SplitWeil.IsUnitVol ν → ∀ {K : Type} [Field K] (σ : K →+* ℂ) (f : Vars G → ℂ), IsLocallyConstant f → HasCompactSupport f → (∀ e, f e ∈ Set.range σ) → ∫ e, f e ∂(varsVol G ν) ∈ Set.range σ := by
  first | exact @GlobalTheory.LCIntegralField.integral_vars_mem_range | exact GlobalTheory.LCIntegralField.integral_vars_mem_range | (intros; apply GlobalTheory.LCIntegralField.integral_vars_mem_range <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchimedeanPairNegativeSymplecticPairing
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open scoped Classical TensorProduct

namespace GlobalTheory.WrongSignPair

open GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem piInf_tmul {w : InfinitePlace F} (τ : EmbOver E w) (a : AF F) (e : E) :
    piInf τ (a ⊗ₜ[F] e) = InfinitePlace.Completion.extensionEmbedding w (a.1 w) * τ.1 e := rfl

private theorem star_extensionEmbedding_eq (h : IsCMExt F E σ) {w : InfinitePlace F} (x : w.Completion) :
    star (InfinitePlace.Completion.extensionEmbedding w x) = InfinitePlace.Completion.extensionEmbedding w x := by
  have h' := h
  obtain ⟨hF, -⟩ := h'
  have hw : w.IsReal := hF.isReal w
  rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw]
  exact Complex.conj_ofReal _

theorem piInf_cA (h : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) (z : AE F E) :
    piInf τ (cA σ z) = star (piInf τ z) := by
  have hconj := h
  obtain ⟨-, -, -, hconj⟩ := hconj
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    have hz : cA σ (a ⊗ₜ[F] e) = a ⊗ₜ[F] σ e := by simp [cA]
    rw [hz, piInf_tmul, piInf_tmul, star_mul', star_extensionEmbedding_eq h, hconj]
  | add x y hx hy => simp only [map_add (f := _), hx, hy, star_add]

private theorem trace_pi_real_eq_sum {ι : Type} [Fintype ι] [DecidableEq ι] (f : ι → ℝ) :
    Algebra.trace ℝ (ι → ℝ) f = ∑ i, f i := by
  rw [Algebra.trace_eq_matrix_trace (Pi.basisFun ℝ ι), Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul]
  simp

theorem trace_evI [IsTotallyReal F] (a : AF F) :
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F a) =
      ∑ w : InfinitePlace F, (InfinitePlace.Completion.extensionEmbedding w (a.1 w)).re := by
  have hreal : ∀ v : InfinitePlace F, v.IsReal := IsTotallyReal.isReal
  haveI : IsEmpty {v : InfinitePlace F // v.IsComplex} :=
    ⟨fun v => (InfinitePlace.not_isReal_iff_isComplex.2 v.2) (hreal v.1)⟩
  rw [Algebra.trace_prod_apply]
  have h2 : (evI F a).2 = 0 := Subsingleton.elim _ _
  rw [h2, map_zero, add_zero, trace_pi_real_eq_sum]
  rw [← Fintype.sum_equiv (Equiv.subtypeUnivEquiv hreal) (fun v => (evI F a).1 v)
    (fun w => (InfinitePlace.Completion.extensionEmbedding w (a.1 w)).re) (fun v => ?_)]
  simp only [evI, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  show _ = (InfinitePlace.Completion.extensionEmbedding v.1 (a.1 v.1)).re
  rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply v.2, Complex.ofReal_re]

theorem trace_evI_trace (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (z : AE F E) :
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (Algebra.trace (AF F) (AE F E) z)) =
      ∑ w : InfinitePlace F, 2 * (piInf (τ w) z).re := by
  have hF : IsTotallyReal F := by
    have h' := h
    obtain ⟨hF, -⟩ := h'
    exact hF
  rw [trace_evI]
  refine Finset.sum_congr rfl fun w _ => ?_
  set t := Algebra.trace (AF F) (AE F E) z with ht
  have key : piInf (τ w) (algebraMap (AF F) (AE F E) t) = piInf (τ w) z + star (piInf (τ w) z) := by
    rw [ht, ← GlobalTheory.GaussMean.OneVec.add_sigR (AF F) h z, map_add (f := _), ← piInf_cA h]
    congr 2
  have hal : piInf (τ w) (algebraMap (AF F) (AE F E) t) =
      InfinitePlace.Completion.extensionEmbedding w (t.1 w) := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, piInf_tmul, map_one,
      mul_one]
  rw [hal] at key
  rw [key, Complex.add_re, Complex.star_def, Complex.conj_re]
  ring

private theorem piInf_inclR_twisted_operators {w : InfinitePlace F} (τ : EmbOver E w) (e : E) :
    piInf τ (inclR (F := F) (AF F) e) = τ.1 e := by
  have h1 : inclR (F := F) (AF F) e = (1 : AF F) ⊗ₜ[F] e := rfl
  have h2 : (1 : AF F).1 w = 1 := rfl
  rw [h1, piInf_tmul, h2, map_one, one_mul]

theorem piInf_hTens (h : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) {n d : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (K : Matrix (Fin d) (Fin d) E) (u u' : Matrix (Fin n) (Fin d) (AE F E)) :
    piInf τ (GlobalTheory.WeilM.hTens (cA σ) (incM F J) (incM F K) u u') =
      ∑ i, ∑ j, ∑ k, ∑ l, u.map (piInf τ) i j * J.map τ.1 i k * K.map τ.1 j l * star (u'.map (piInf τ) k l) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [GlobalTheory.WeilM.hTens, incM, Matrix.map_apply, map_sum, map_mul, piInf_cA h, piInf_inclR_twisted_operators]

theorem sum_rank_one {n d : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) (H : Matrix (Fin d) (Fin d) ℂ) (x x' : Fin n → ℂ)
    (y y' : Fin d → ℂ) :
    ∑ i, ∑ j, ∑ k, ∑ l, vecMulVec x y i j * G i k * H j l * star (((-Complex.I) • vecMulVec x' y') k l) =
      (x ⬝ᵥ G *ᵥ star x') * (y ⬝ᵥ (Complex.I • H) *ᵥ star y') := by
  have hI : star (-Complex.I) = Complex.I := by
    rw [star_neg]
    exact (congrArg Neg.neg Complex.conj_I).trans (neg_neg _)
  simp only [dotProduct, mulVec, Matrix.smul_apply, vecMulVec_apply, Pi.star_apply, smul_eq_mul, star_mul', hI,
    Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_comm.trans ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  refine (Finset.sum_congr rfl fun i _ => Finset.sum_comm).trans (Finset.sum_comm.trans ?_)
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  ring

private theorem star_dotProduct_mulVec_star_comm {n : ℕ} {G : Matrix (Fin n) (Fin n) ℂ} (hG : ∀ i j, star (G j i) = G i j)
    (u v : Fin n → ℂ) : star (u ⬝ᵥ G *ᵥ star v) = v ⬝ᵥ G *ᵥ star u := by
  simp only [dotProduct, mulVec, star_sum, star_mul', Pi.star_apply, star_star, Finset.mul_sum]
  first
  | (rw [Finset.sum_comm]
     refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
     rw [hG]; ring)
  | (refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
     rw [hG]; ring)

private theorem dotProduct_mulVec_star_invariant {n : ℕ} {G θ : Matrix (Fin n) (Fin n) ℂ} (hθ : θᵀ * G * θ.map star = G)
    (u v : Fin n → ℂ) : (θ *ᵥ u) ⬝ᵥ G *ᵥ star (θ *ᵥ v) = u ⬝ᵥ G *ᵥ star v := by
  have hs : star (θ *ᵥ v) = θ.map star *ᵥ star v := by
    ext i
    simp [mulVec, dotProduct, star_sum, star_mul']
  rw [hs, ← Matrix.vecMul_transpose θ u, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  simp only [hθ]

theorem majorant_im {n : ℕ} {G θ : Matrix (Fin n) (Fin n) ℂ} (hG : ∀ i j, star (G j i) = G i j) (h : IsCartan G θ)
    (x : Fin n → ℂ) : ((θ *ᵥ x) ⬝ᵥ G *ᵥ star x).im = 0 := by
  obtain ⟨h1, h2, -⟩ := h
  have e1 : (θ *ᵥ x) ⬝ᵥ G *ᵥ star x = x ⬝ᵥ G *ᵥ star (θ *ᵥ x) := by
    conv_lhs => rw [← dotProduct_mulVec_star_invariant h2 (θ *ᵥ x) x, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  rw [← star_dotProduct_mulVec_star_comm hG (θ *ᵥ x) x] at e1
  exact Complex.conj_eq_iff_im.mp e1.symm

private theorem mul_vecMulVec_mul_transpose' {n d : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin d) (Fin d) ℂ)
    (x : Fin n → ℂ) (y : Fin d → ℂ) : A * vecMulVec x y * Cᵀ = vecMulVec (A *ᵥ x) (C *ᵥ y) := by
  ext i j
  simp only [Matrix.mul_apply, vecMulVec_apply, mulVec, dotProduct, Matrix.transpose_apply, Finset.sum_mul,
    Finset.mul_sum]
  first
  | (rw [Finset.sum_comm]
     exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring)
  | exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

private theorem re_pos_im_zero_of_isCartan {n : ℕ} {G θ : Matrix (Fin n) (Fin n) ℂ} (hG : ∀ i j, star (G j i) = G i j)
    (h : IsCartan G θ) {x : Fin n → ℂ} (hx : x ≠ 0) :
    0 < (x ⬝ᵥ G *ᵥ star (θ *ᵥ x)).re ∧ (x ⬝ᵥ G *ᵥ star (θ *ᵥ x)).im = 0 := by
  have hi := majorant_im hG h x
  have hp := h.2.2 x hx
  rw [← star_dotProduct_mulVec_star_comm hG (θ *ᵥ x) x, Complex.star_def, Complex.conj_re, Complex.conj_im, hi, neg_zero]
  exact ⟨hp, rfl⟩

theorem exists_neg_pair : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (B : Base F E) {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (r s r' s' : ℕ),
    B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → 0 < n → 0 < d →
    ∀ (ε' : InfinitePlace F → ℤˣ) (w : InfinitePlace F), ε' w = -1 →
    ∃ u u' : Matrix (Fin n) (Fin d) (AE F E), At (evI F) u ∧ At (evI F) u' ∧
      (∀ w', u'.map (piInf (B.emb w')) =
        (((ε' w' : ℤ) : ℂ) * Complex.I) • (X.θ w' * u.map (piInf (B.emb w')) * (W.θ w')ᵀ)) ∧
      Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
        (evI F (GlobalTheory.WeilM.symp (cA σ) (-1) (incM F X.J) (incM F W.J) u u')) < 0 := by
  intro F E _ _ _ _ _ σ B n d X W r s r' s' hB hX hW hn hd ε' w hw
  have h : IsCMExt F E σ := hB.cm
  have hconj : ∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x) := by
    have h' := h
    obtain ⟨-, -, -, hconj⟩ := h'
    exact hconj
  have lift : ∀ c : InfinitePlace F → Matrix (Fin n) (Fin d) ℂ, ∃ z : Matrix (Fin n) (Fin d) (AE F E),
      At (evI F) z ∧ ∀ w', z.map (piInf (B.emb w')) = c w' := by
    intro c
    have hz := fun i j => GlobalTheory.ThK.exists_at_evI_piInf_eq F E σ h B.emb (fun w' => c w' i j)
    choose z hz1 hz2 using hz
    refine ⟨z, ?_, ?_⟩
    · intro a ha
      ext i j
      exact hz1 i j a ha
    · intro w'
      ext i j
      exact hz2 i j w'
  let x : Fin n → ℂ := Pi.single ⟨0, hn⟩ 1
  let y : Fin d → ℂ := Pi.single ⟨0, hd⟩ 1
  have hx : x ≠ 0 := by
    intro h0
    have := congrFun h0 ⟨0, hn⟩
    simp [x] at this
  have hy : y ≠ 0 := by
    intro h0
    have := congrFun h0 ⟨0, hd⟩
    simp [y] at this
  obtain ⟨u, hu1, hu2⟩ := lift (fun w' => if w' = w then vecMulVec x y else 0)
  obtain ⟨u', hu'1, hu'2⟩ := lift (fun w' => (((ε' w' : ℤ) : ℂ) * Complex.I) •
    (X.θ w' * (if w' = w then vecMulVec x y else 0) * (W.θ w')ᵀ))
  have hu : ∀ w', u.map (piInf (B.emb w')) = if w' = w then vecMulVec x y else 0 := fun w' => hu2 w'
  have hu' : ∀ w', u'.map (piInf (B.emb w')) = (((ε' w' : ℤ) : ℂ) * Complex.I) •
      (X.θ w' * (if w' = w then vecMulVec x y else 0) * (W.θ w')ᵀ) := fun w' => hu'2 w'
  refine ⟨u, u', hu1, hu'1, fun w' => by rw [hu' w', hu w'], ?_⟩
  have hJ : ∀ i j, star ((X.J.map (B.emb w).1) j i) = (X.J.map (B.emb w).1) i j := by
    intro i j
    simp only [Matrix.map_apply]
    rw [← hconj, hX.herm]
  have hI : star Complex.I = -Complex.I := Complex.conj_I
  have hK : ∀ i j, star ((Complex.I • W.J.map (B.emb w).1) j i) = (Complex.I • W.J.map (B.emb w).1) i j := by
    intro i j
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    rw [star_mul', hI, ← hconj, hW.skew, map_neg]
    ring
  obtain ⟨hPr, hPi⟩ := re_pos_im_zero_of_isCartan hJ (hX.cartan w) hx
  obtain ⟨hQr, hQi⟩ := re_pos_im_zero_of_isCartan hK (hW.cartan w) hy
  have hs : (((ε' w : ℤ) : ℂ) * Complex.I) = -Complex.I := by
    rw [hw]
    simp
  have hmain : piInf (B.emb w) (GlobalTheory.WeilM.hTens (cA σ) (incM F X.J) (incM F W.J) u u') =
      (x ⬝ᵥ (X.J.map (B.emb w).1) *ᵥ star (X.θ w *ᵥ x)) *
        (y ⬝ᵥ (Complex.I • W.J.map (B.emb w).1) *ᵥ star (W.θ w *ᵥ y)) := by
    rw [piInf_hTens h, hu w, hu' w, if_pos rfl, hs, mul_vecMulVec_mul_transpose', sum_rank_one]
  have hzero : ∀ w', w' ≠ w → piInf (B.emb w') (GlobalTheory.WeilM.hTens (cA σ) (incM F X.J) (incM F W.J) u u') = 0 := by
    intro w' hne
    rw [piInf_hTens h, hu w', if_neg hne]
    simp
  simp only [GlobalTheory.WeilM.symp]
  rw [trace_evI_trace h B.emb, Finset.sum_eq_single w]
  · rw [map_mul, map_neg, map_one, neg_one_mul, hmain, Complex.neg_re, Complex.mul_re, hPi, zero_mul, sub_zero]
    nlinarith [mul_pos hPr hQr]
  · intro w' _ hne
    rw [map_mul, hzero w' hne, mul_zero, Complex.zero_re, mul_zero]
  · intro hw'
    exact absurd (Finset.mem_univ w) hw'

end GlobalTheory.WrongSignPair
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalFormCoordinatesCoeffMemCoefficientField
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalFormCoordinatesCoeffMemCoefficientField
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim

namespace GlobalTheory.FormCoef

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem typeX_mem (R : RealDat D A Ks) (t : T) (M : Subfield ℂ)
    (hχ : ∀ i : Fin D.R.m, ∀ PP ∈ R.Pg, ∀ x, ((R.chi ((i : ℕ) + 1) PP x : ℂˣ) : ℂ) ∈ M)
    (hξ : ∀ PP ∈ R.Q t, ∀ x, ((R.xiR t PP x : ℂˣ) : ℂ) ∈ M) (k) :
    (((levEnv D.sp.X' R.βX (R.datXt t)).χ k : ℂˣ) : ℂ) ∈ M := by
  show levFn R.βX (Lev.flag1L (R.datXt t)) _ ∈ GlobalTheory.RationalValues.unitsIn M
  unfold levFn
  refine mul_mem (mul_mem ?_ (prod_mem fun PP hPP => prod_mem fun c hc => ?_)) (prod_mem fun PP hPP => ?_)
  · have h1 : ∀ x, ext1 (Lev.flag1L (R.datXt t)).P.H (Lev.flag1L (R.datXt t)).P.chi x = 1 := fun x => Lev.subgroupCharExtension_one_apply _ x
    rw [h1]
    exact one_mem _
  · have hc' : c < D.R.m := Finset.mem_range.1 hc
    exact show R.chi ((⟨c, hc'⟩ : Fin D.R.m) + 1 : ℕ) PP _ ∈ GlobalTheory.RationalValues.unitsIn M from hχ ⟨c, hc'⟩ PP hPP _
  · exact inv_mem (show R.xiR t PP _ ∈ GlobalTheory.RationalValues.unitsIn M from hξ PP hPP _)

end GlobalTheory.FormCoef

namespace GlobalTheory.FormCoef

attribute [local instance] Formalism.BasicNotions.Host.cmStar


set_option maxHeartbeats 1600000 in
theorem coeff_formC_mem : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A),
    HidaSetting large₂ R F → ch.Is → ch.FieldOK → ∀ (t : T) (x : A.fam.amb.FR t) (y : FinPt ch.G (.grid 0 D.R.m)) m,
      AddMonoidAlgebra.coeff (ch.S.formC t (R.jX t x) y).1 m ∈ Set.range D.what₂.embLL := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch large₂ F hS _ _ t x y m
  obtain ⟨gram, c₀, c₁, hT, hco⟩ := ch.S.co_is
  have hc := hS.core
  obtain ⟨k, v, hv⟩ := GlobalTheory.RationalValues.exists_ext_eq (R.B.R t).pres c₀ (GlobalTheory.RationalValues.coef_mem (hT.coefR t))
    (GlobalTheory.RationalValues.rho_mem hT.mapR) x (toXf y)
  have h0 : (R.HX t).e (R.jX t x) (toXf y) = (((levEnv D.sp.X' R.βX (R.datXt t)).χ k : ℂˣ) : ℂ) • c₀ v :=
    (congrFun (hc.models.jX t x) (toXf y)).trans hv
  have i0 : Fin D.R.m := ⟨0, by have := D.R.two_le_m; omega⟩
  obtain ⟨a, ha⟩ := typeX_mem R t D.what₂.embLL.fieldRange (GlobalTheory.RationalValues.chiVal_of_chiW R hc.grp.chiW)
    (GlobalTheory.RationalValues.xiR_mem R hc.lev hc.fam.pl_onto hc.fam.muVal hT.ok i0 t) k
  have h1 : ch.S.formC t (R.jX t x) y = ch.S.co (c₀ (a • v)) := by
    rw [SumChoice.formC, h0, map_smulₛₗ, ha]
  rw [h1, hco, ← MvPolynomial.map_rename, MvPolynomial.coeff_map]
  exact ⟨_, rfl⟩

end GlobalTheory.FormCoef
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalFormCoordinatesCoeffMemCoefficientFieldStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalForm_coordinates_coeff_mem_coefficientField : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A), HidaSetting large₂ R F → ch.Is → ch.FieldOK → ∀ (t : T) (x : A.fam.amb.FR t) (y : FinPt ch.G (.grid 0 D.R.m)) m, AddMonoidAlgebra.coeff (ch.S.formC t (R.jX t x) y).1 m ∈ Set.range D.what₂.embLL := by
  first | exact @GlobalTheory.FormCoef.coeff_formC_mem | exact GlobalTheory.FormCoef.coeff_formC_mem | (intros; apply GlobalTheory.FormCoef.coeff_formC_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicIsometriesObj
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Lev Formalism.IndefR.Links

namespace GlobalTheory.AdIsomObj

theorem adelicIsometries_obj (D : D7) : GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.AdelicIsometries D :=
  GlobalTheory.AdIsom.adelicIsometries D

theorem frames_exist (D : D7) (V : HSp D) (N : ℕ) : ∃ β Λ, IsSDFrame V β Λ N :=
  (adelicIsometries_obj D).2.2.2.2.2.2.2.2.2.2.2.1 V N

end GlobalTheory.AdIsomObj

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedThetaSeriesRapidDecayStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped Pointwise
open Formalism.IndefR.Datum
open GlobalTheory.Grid
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixed_theta_series_rapid_decay : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (θ : InfFam D), IsInfFam θ →
    ∀ (V X S₀ : HSp D) (r : ℕ) (d : GlobalTheory.MixModel.HypDec V S₀ r) (μ' : Measure (Mx D X.rank r))
    (𝓕' : Set (Mx D X.rank r)), IsCovolOne (GlobalTheory.MixModel.ratMx D X.rank r) μ' 𝓕' → ∀ N : ℕ,
    ∃ (k : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ Ψ : WO V X → ℂ, IsThetaFunO ψ V X Ψ → ∀ x : Mx D X.rank r,
      ‖d.mixS X ψ μ' 𝓕' Ψ x 0‖ₑ * ENNReal.ofReal ((1 + ∑ τ, ∑ i, ∑ j, ‖compAt θ τ x i j‖) ^ N) ≤
        ENNReal.ofReal C * GlobalTheory.Size.wordSum (GlobalTheory.Size.heisDer ψ θ) GlobalTheory.HeisTaylor.supN k Ψ := by
  first | exact @GlobalTheory.MixWeight.mixS_weight_le | exact GlobalTheory.MixWeight.mixS_weight_le | (intros; apply GlobalTheory.MixWeight.mixS_weight_le <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoverFieldOfContainsRayField
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistField

theorem coverField_of_containsRayField : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F), LawsJ T → R.toLevCh.Is A.μ0 → QGuard R → (∀ t, GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField (GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.embK D) (GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.tupLevel R t)) → GlobalTheory.TwistField.CoverField T R := by
  intro D G _ _ Pl0 T0 A T _ R hT hL hQ hray
  unfold GlobalTheory.TwistField.CoverField
  intro i t l₂ hdvd hM hA Xo₂ c₂ hc
  obtain ⟨hHost, hLev, -, -⟩ := hT.pins
  unfold Par.PinHost at hHost
  unfold Par.PinLevel at hLev

  have hn : GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.tupLevel R t = l₂.M := by
    rw [hM, hLev.1]
    rfl

  have hsq : ∃ a : D.host.K, a ^ 2 = -(T.Q.H.d : D.host.K) := by
    refine ⟨⟨D.host.sqrtMinusD, Formalism.L2.Pj.LPb.sqrtMinusD_mem_K D⟩, ?_⟩
    rw [hHost.1]
    apply Subtype.ext
    push_cast
    exact Formalism.BasicNotions.Host.sqrtMinusD_sq D.host
  have h3 : 3 ≤ GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.tupLevel R t := hn ▸ l₂.three_le

  have hW := (GlobalTheory.T.weberValues_mem_of_containsRayField D.host.E T.Q.H D.host.K D.what₂.LL (GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.embK D) D.what₂.embLL
    (Formalism.L2.Pj.LPb.finrank_K D) hsq _ h3 (hray t)).1
  refine GlobalTheory.T.geometricallyIrreducible_components_weberValues D T.Q hT.pins ((i : ℕ) + 1) ⟨by omega, by omega⟩ l₂ Xo₂ c₂
    (GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.tupLevel R t) (by omega) ?_ (Or.inl (hc ▸ hW))
  show Nat.lcm l₂.M l₂.A ∣ _
  rw [hA, Nat.lcm_one_right, hn]

end GlobalTheory.TwistField
end
