module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmulMemLatOIdem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDiagonalSiegelParabolicRule

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalSiegelHeisenbergInvariantFormUnique
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalSiegelHeisenbergInvariantFormUnique
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory

noncomputable section

namespace GlobalTheory.DiagSiegelUniq

open GlobalTheory.WeilM

theorem diagMat_eq_mul {A : Type} [CommRing A] {m n : ℕ} (w : Matrix (Fin m) (Fin n) A) :
    GlobalTheory.DiagSiegel.diagMat w =
      w * ((diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) A).submatrix finSumFinEquiv.symm id)ᵀ := by
  ext i j
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rcases j with j | j <;>
    simp only [GlobalTheory.DiagSiegel.diagMat, Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply,
      Equiv.symm_apply_apply, id] <;>
    simp [diagCols, Matrix.one_apply]

theorem transpose_transport (D : D7) (S T : HSp D) (ν : Measure (Formalism.IndefR.Datum.WO T S))
    (𝓕 : Set (Formalism.IndefR.Datum.WO T S)) (h : Formalism.IndefR.Datum.IsCovolOne (ratL S T) ν 𝓕) :
    ∃ (ν' : Measure (Formalism.IndefR.DatumF.WOF D.host.F D.host.E S.rank T.rank))
      (𝓕' : Set (Formalism.IndefR.DatumF.WOF D.host.F D.host.E S.rank T.rank)),
      ν'.IsAddHaarMeasure ∧ IsAddFundamentalDomain (Formalism.IndefR.DatumF.ratLF D.host.F D.host.E S.rank T.rank) 𝓕' ν' ∧
      ∀ f : Matrix (Fin T.rank) (Fin S.rank) (AF D.host.F ⊗[D.host.F] D.host.E) → ℂ,
        ∫ u in 𝓕', f u ∂ν' = ∫ w in 𝓕, f wᵀ ∂ν := by
  classical
  haveI : BorelSpace (Formalism.IndefR.Datum.WO T S) := ⟨rfl⟩
  haveI : BorelSpace (Formalism.IndefR.DatumF.WOF D.host.F D.host.E S.rank T.rank) := ⟨rfl⟩
  obtain ⟨hH, hF, -⟩ := h
  let e : Formalism.IndefR.Datum.WO T S ≃+ Formalism.IndefR.DatumF.WOF D.host.F D.host.E S.rank T.rank :=
    Matrix.transposeAddEquiv _ _ _
  have hc : Continuous e := Continuous.matrix_transpose continuous_id
  have hcs : Continuous e.symm := Continuous.matrix_transpose continuous_id
  let E' : Formalism.IndefR.Datum.WO T S ≃ᵐ Formalism.IndefR.DatumF.WOF D.host.F D.host.E S.rank T.rank :=
    (Homeomorph.mk e.toEquiv hc hcs).toMeasurableEquiv
  have hE' : ∀ w, E' w = wᵀ := fun _ => rfl
  let eG : Formalism.IndefR.DatumF.ratLF D.host.F D.host.E S.rank T.rank ≃ ratL S T :=
    { toFun := fun g => ⟨(g : Matrix (Fin T.rank) (Fin S.rank) _)ᵀ, by
        obtain ⟨γ, hγ⟩ := g.2
        exact ⟨γᵀ, by rw [← hγ]; rfl⟩⟩
      invFun := fun g => ⟨(g : Matrix (Fin S.rank) (Fin T.rank) _)ᵀ, by
        obtain ⟨γ, hγ⟩ := g.2
        exact ⟨γᵀ, by rw [← hγ]; rfl⟩⟩
      left_inv := fun g => Subtype.ext (Matrix.transpose_transpose _)
      right_inv := fun g => Subtype.ext (Matrix.transpose_transpose _) }
  refine ⟨ν.map E', E' '' 𝓕, ?_, ?_, fun f => ?_⟩
  · exact AddEquiv.isAddHaarMeasure_map ν e hc hcs
  · refine hF.image_of_equiv E'.toEquiv (E'.quasiMeasurePreserving_symm ν) eG fun g x => ?_
    show (((eG g : ratL S T) : Matrix (Fin S.rank) (Fin T.rank) _) + x)ᵀ = (g : Matrix (Fin T.rank) (Fin S.rank) _) + xᵀ
    rw [Matrix.transpose_add]
    exact congrArg (· + xᵀ) (Matrix.transpose_transpose _)
  · rw [E'.restrict_map, E'.preimage_image, MeasureTheory.integral_map_equiv]
    rfl

theorem lubinTateSeries_eq_of_coeff_one_eq (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D)
    (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (ξ : AF D.host.F ⊗[D.host.F] D.host.E)
    (hξ : ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹)) (κ : Type) [Fintype κ]
    (J' : Matrix (Fin (T.rank + T.rank)) (Fin (T.rank + T.rank)) (AF D.host.F ⊗[D.host.F] D.host.E))
    (hJ : incM D.host.F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG T.gram)ᵀ = J')
    (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ J' (incM D.host.F JB)) κ)
    (hrat : ∀ x : Matrix (Fin (T.rank + T.rank)) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
      co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i),
        fun i => algebraMap D.host.F (AF D.host.F) (z i)))
    (ν' : Measure (Formalism.IndefR.DatumF.WOF D.host.F D.host.E S.rank T.rank))
    (𝓕' : Set (Formalism.IndefR.DatumF.WOF D.host.F D.host.E S.rank T.rank)) (hν' : ν'.IsAddHaarMeasure)
    (h𝓕' : IsAddFundamentalDomain (Formalism.IndefR.DatumF.ratLF D.host.F D.host.E S.rank T.rank) 𝓕' ν')
    (l : ((κ → AF D.host.F) → ℂ) →ₗ[ℂ] ℂ) (hl : l ∈ (GlobalTheory.WeilM.adeleClass D.host.F).adm κ)
    (hinv : ∀ z : Matrix (Fin S.rank) (Fin T.rank) (AF D.host.F ⊗[D.host.F] D.host.E),
      ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ,
        l ((GlobalTheory.WeilSchrodinger.transD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) co).rho ψ
          (GlobalTheory.DiagSiegel.diagMat z) Φ) = l Φ) :
    ∃ c : ℂ, ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, l Φ = c * GlobalTheory.LagrTheta.lagrInt ν' 𝓕'
      ((diagCols (Fin T.rank) : Matrix (Fin T.rank ⊕ Fin T.rank) (Fin T.rank)
        (AF D.host.F ⊗[D.host.F] D.host.E)).submatrix finSumFinEquiv.symm id)
      (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ) := by
  subst hJ
  classical
  obtain ⟨v₁, -, -, ⟨τ₁⟩⟩ := GlobalTheory.TripleDarboux.exists_good_place D ∅
  let B : Base D.host.F D.host.E :=
    { ψ := ψ, emb := fun _ => Classical.arbitrary _, mα := 0, mβ := 0, P := ∅,
      τ := fun v => absurd v.2 (Finset.notMem_empty _), v₁ := v₁, τ₁ := τ₁ }
  have hB : B.IsGood D.sp.cm.sig :=
    GlobalTheory.TripleDarboux.base_isGood B hψ fun v hv => absurd hv (Finset.notMem_empty _)
  exact GlobalTheory.T.diagonalLagrangian_invariantForm_unique D.host.F D.host.E D.sp.cm.sig B hB S.rank T.rank S.gram T.gram
    (GlobalTheory.Doubling.isHermND_gram S) (GlobalTheory.Doubling.isHermND_gram T) D.host.xi0 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)
    (Formalism.L2.Pj.conj_xi0_alt D) JB ξ hξ κ co hrat ν' 𝓕' hν' h𝓕' l hl fun z Φ hΦ => by
      rw [← diagMat_eq_mul]
      exact hinv z Φ hΦ

theorem uniq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (ξ : AF D.host.F ⊗[D.host.F] D.host.E),
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ
            (incM D.host.F ((GlobalTheory.Doubling.dblSp T).gramᵀ)) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin (GlobalTheory.Doubling.dblSp T).rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i),
              fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ (ν : MeasureTheory.Measure (Formalism.IndefR.Datum.WO T S)) (𝓕 : Set (Formalism.IndefR.Datum.WO T S)),
            Formalism.IndefR.Datum.IsCovolOne (ratL S T) ν 𝓕 →
          ∀ l : ((κ → AF D.host.F) → ℂ) →ₗ[ℂ] ℂ, l ∈ (GlobalTheory.WeilM.adeleClass D.host.F).adm κ →
            (∀ z : Matrix (Fin S.rank) (Fin T.rank) (AF D.host.F ⊗[D.host.F] D.host.E),
              ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ,
                l ((GlobalTheory.WeilSchrodinger.transD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) co).rho ψ
                  (GlobalTheory.DiagSiegel.diagMat z) Φ) = l Φ) →
            ∃ c : ℂ, ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, l Φ = c * GlobalTheory.DiagSiegel.thetaDiagInt ν 𝓕
              (GlobalTheory.WeilSchrodinger.thetaTr D.host.F (GlobalTheory.WeilSchrodinger.transD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) co) ψ Φ) := by
  intro D ψ hψ S T JB ξ hξ κ _ co hrat ν 𝓕 hcov l hl hinv
  obtain ⟨ν', 𝓕', hν', h𝓕', hint⟩ := transpose_transport D S T ν 𝓕 hcov
  have hJ : incM D.host.F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG T.gram)ᵀ =
      incM D.host.F ((GlobalTheory.Doubling.dblSp T).gramᵀ) := by
    rw [← GlobalTheory.WeilSchrodinger.DblTargetF.reindex_dbl_incM (F := D.host.F) (J := T.gram) rfl,
      GlobalTheory.WeilSchrodinger.DblTarget.reindex_dbl_incM T rfl]
  obtain ⟨c, hc⟩ := lubinTateSeries_eq_of_coeff_one_eq D ψ hψ S T JB ξ hξ κ _ hJ co hrat ν' 𝓕' hν' h𝓕' l hl hinv
  refine ⟨c, fun Φ hΦ => ?_⟩
  rw [hc Φ hΦ, GlobalTheory.LagrTheta.lagrInt, hint, GlobalTheory.DiagSiegel.thetaDiagInt]
  congr 2
  funext w
  simp only [GlobalTheory.WeilSchrodinger.thetaTr, GlobalTheory.WeilSchrodinger.transD_rho,
    diagMat_eq_mul, Matrix.transpose_mul, Matrix.transpose_transpose]

end GlobalTheory.DiagSiegelUniq

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalSiegelHeisenbergInvariantFormUniqueStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagonalSiegel_heisenbergInvariant_form_unique : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (ξ : AF D.host.F ⊗[D.host.F] D.host.E),
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ
            (incM D.host.F ((GlobalTheory.Doubling.dblSp T).gramᵀ)) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin (GlobalTheory.Doubling.dblSp T).rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i),
              fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ (ν : MeasureTheory.Measure (Formalism.IndefR.Datum.WO T S)) (𝓕 : Set (Formalism.IndefR.Datum.WO T S)),
            Formalism.IndefR.Datum.IsCovolOne (ratL S T) ν 𝓕 →
          ∀ l : ((κ → AF D.host.F) → ℂ) →ₗ[ℂ] ℂ, l ∈ (GlobalTheory.WeilM.adeleClass D.host.F).adm κ →
            (∀ z : Matrix (Fin S.rank) (Fin T.rank) (AF D.host.F ⊗[D.host.F] D.host.E),
              ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ,
                l ((GlobalTheory.WeilSchrodinger.transD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) co).rho ψ
                  (GlobalTheory.DiagSiegel.diagMat z) Φ) = l Φ) →
            ∃ c : ℂ, ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, l Φ = c * GlobalTheory.DiagSiegel.thetaDiagInt ν 𝓕
              (GlobalTheory.WeilSchrodinger.thetaTr D.host.F (GlobalTheory.WeilSchrodinger.transD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) co) ψ Φ) := by
  first | exact @GlobalTheory.DiagSiegelUniq.uniq | exact GlobalTheory.DiagSiegelUniq.uniq | (intros; apply GlobalTheory.DiagSiegelUniq.uniq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDiagonalSiegelParabolicRuleStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaDiagonal_siegelParabolic_rule : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (ξ : AF D.host.F ⊗[D.host.F] D.host.E),
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ
            (incM D.host.F ((GlobalTheory.Doubling.dblSp T).gramᵀ)) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin (GlobalTheory.Doubling.dblSp T).rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i),
              fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ (ν : MeasureTheory.Measure (Formalism.IndefR.Datum.WO T S)) (𝓕 : Set (Formalism.IndefR.Datum.WO T S)),
            Formalism.IndefR.Datum.IsCovolOne (ratL S T) ν 𝓕 →
          ∀ (χS : (AE D)ˣ →* Circle), IsHeckeChar D χS → ResEta D χS S.rank →
          ∀ ωd : GA D S × GA D (GlobalTheory.Doubling.dblSp T) →* Module.End ℂ (Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ S (GlobalTheory.Doubling.dblSp T) χS 1 ωd →
          ∀ omp : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F ((GlobalTheory.Doubling.dblSp T).gramᵀ)) ×
              GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →*
                Module.End ℂ ((κ → AF D.host.F) → ℂ),
            GlobalTheory.WeilSchrodinger.IsTransport ψ co ωd omp →
          ∀ (p : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F ((GlobalTheory.Doubling.dblSp T).gramᵀ)))
            (t : GL (Fin T.rank) (AF D.host.F ⊗[D.host.F] D.host.E)),
            p.1.1 * (GlobalTheory.WeilM.diagCols (Fin T.rank) : Matrix (Fin T.rank ⊕ Fin T.rank) (Fin T.rank) (AE D)).submatrix
                finSumFinEquiv.symm id =
              (GlobalTheory.WeilM.diagCols (Fin T.rank) : Matrix (Fin T.rank ⊕ Fin T.rank) (Fin T.rank) (AE D)).submatrix
                finSumFinEquiv.symm id * t.1 →
          ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ,
            omp (p, 1) Φ ∈ GlobalTheory.WeilM.schA D.host.F κ ∧
            GlobalTheory.DiagSiegel.thetaDiagInt ν 𝓕 (GlobalTheory.WeilSchrodinger.thetaTr D.host.F
                         (GlobalTheory.WeilSchrodinger.transD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) co) ψ (omp (p, 1) Φ)) =
              GlobalTheory.DiagSiegel.ruleFac (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.adeleClass D.host.F) χS
                (Fintype.card (Fin S.rank)) t *
              GlobalTheory.DiagSiegel.thetaDiagInt ν 𝓕 (GlobalTheory.WeilSchrodinger.thetaTr D.host.F
                (GlobalTheory.WeilSchrodinger.transD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) co) ψ Φ) := by
  first | exact @GlobalTheory.DblTargetTheta.thetaDiag_rule | exact GlobalTheory.DblTargetTheta.thetaDiag_rule | (intros; apply GlobalTheory.DblTargetTheta.thetaDiag_rule <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelRuleTransportedWeilDatumDoubledTarget
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DblTargetSiegel

theorem mul_diagCols_transpose {X : Type} [CommRing X] {m n : ℕ} (z : Matrix (Fin m) (Fin n) X) :
    z * ((GlobalTheory.WeilM.diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) X).submatrix finSumFinEquiv.symm id)ᵀ =
      GlobalTheory.DiagSiegel.diagMat z := by
  ext i j
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  simp only [GlobalTheory.DiagSiegel.diagMat, Matrix.submatrix_apply, Equiv.symm_apply_apply, id, Matrix.mul_apply,
    Matrix.transpose_apply]
  rcases j with j | j <;> simp [GlobalTheory.WeilM.diagCols, Matrix.one_apply]

end GlobalTheory.DblTargetSiegel

set_option maxHeartbeats 1000000 in
theorem GlobalTheory.DblTargetSiegel.siegelRule_dblTarget : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS : (AE D)ˣ →* Circle), IsHeckeChar D χS → ResEta D χS S.rank →
      ∀ (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (ξ : AF D.host.F ⊗[D.host.F] D.host.E),
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ
            (incM D.host.F ((GlobalTheory.Doubling.dblSp T).gramᵀ)) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin (GlobalTheory.Doubling.dblSp T).rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i),
              fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ ωd : GA D S × GA D (GlobalTheory.Doubling.dblSp T) →* Module.End ℂ (Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ S (GlobalTheory.Doubling.dblSp T) χS 1 ωd →
          ∀ omp : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F ((GlobalTheory.Doubling.dblSp T).gramᵀ)) ×
              GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →*
                Module.End ℂ ((κ → AF D.host.F) → ℂ),
            GlobalTheory.WeilSchrodinger.IsTransport ψ co ωd omp →
            GlobalTheory.WeilM.SiegelRule (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.adeleClass D.host.F) ψ ξ (incM D.host.F JB)
              (incM D.host.F ((GlobalTheory.Doubling.dblSp T).gramᵀ)) (GlobalTheory.WeilSchrodinger.transD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) co) χS
              ((GlobalTheory.WeilM.diagCols (Fin T.rank) : Matrix (Fin T.rank ⊕ Fin T.rank) (Fin T.rank) (AE D)).submatrix
                finSumFinEquiv.symm id)
              (omp.comp (MonoidHom.inl _ _)) := by
  intro D ψ hψ S T χS hS rS JB ξ hξ κ _ co hco ωd hωd omp htr
  intro l hl hinv p t hpt φ hφ
  obtain ⟨ν, 𝓕, hν⟩ := GlobalTheory.Size.exists_isCovolOne (D := D) T S
  have hinv' : ∀ z : Matrix (Fin S.rank) (Fin T.rank) (AF D.host.F ⊗[D.host.F] D.host.E),
      ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ,
        l ((GlobalTheory.WeilSchrodinger.transD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) co).rho ψ
          (GlobalTheory.DiagSiegel.diagMat z) Φ) = l Φ := by
    intro z Φ hΦ
    have h1 := hinv z Φ hΦ
    rwa [GlobalTheory.DblTargetSiegel.mul_diagCols_transpose] at h1
  obtain ⟨c, hc⟩ := GlobalTheory.T.diagonalSiegel_heisenbergInvariant_form_unique D ψ hψ S T JB ξ hξ κ co hco ν 𝓕 hν l hl hinv'
  obtain ⟨hmem, hrule⟩ := GlobalTheory.T.thetaDiagonal_siegelParabolic_rule D ψ hψ S T JB ξ hξ κ co hco ν 𝓕 hν χS hS rS ωd hωd omp htr p t hpt φ hφ
  show l (omp (p, 1) φ) = _
  rw [hc _ hmem, hrule, hc _ hφ]
  simp only [GlobalTheory.DiagSiegel.ruleFac]
  ring

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelRuleTransportedWeilDatumDoubledTargetStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelRule_transported_weilDatum_doubledTarget : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS : (AE D)ˣ →* Circle), IsHeckeChar D χS → ResEta D χS S.rank →
      ∀ (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (ξ : AF D.host.F ⊗[D.host.F] D.host.E),
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ
            (incM D.host.F ((GlobalTheory.Doubling.dblSp T).gramᵀ)) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin (GlobalTheory.Doubling.dblSp T).rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i),
              fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ ωd : GA D S × GA D (GlobalTheory.Doubling.dblSp T) →* Module.End ℂ (Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ S (GlobalTheory.Doubling.dblSp T) χS 1 ωd →
          ∀ omp : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F ((GlobalTheory.Doubling.dblSp T).gramᵀ)) ×
              GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →*
                Module.End ℂ ((κ → AF D.host.F) → ℂ),
            GlobalTheory.WeilSchrodinger.IsTransport ψ co ωd omp →
            GlobalTheory.WeilM.SiegelRule (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.adeleClass D.host.F) ψ ξ (incM D.host.F JB)
              (incM D.host.F ((GlobalTheory.Doubling.dblSp T).gramᵀ)) (GlobalTheory.WeilSchrodinger.transD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) co) χS
              ((GlobalTheory.WeilM.diagCols (Fin T.rank) : Matrix (Fin T.rank ⊕ Fin T.rank) (Fin T.rank) (AE D)).submatrix
                finSumFinEquiv.symm id)
              (omp.comp (MonoidHom.inl _ _)) := by
  set_option maxHeartbeats 10000000 in
    exact @GlobalTheory.DblTargetSiegel.siegelRule_dblTarget
end
