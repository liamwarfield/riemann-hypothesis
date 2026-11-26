module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitRowsBarPhaseCompatibility
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfPartAlgebraMapLiftV
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RouteBigVertexKernelProductEqConstMulThetaKernel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPartRealisationWithScalarsCharOfWeak
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNormalisedTupleDataOverCoefficientField

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledStabilizerWeilOperatorTransportsLatticeEi
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledStabilizerWeilOperatorTransportsLatticeEi
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.DblVacTransport

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cols_mem {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (v : Pl (F := F))
    (h : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E))
    (hh : ∀ z ∈ GlobalTheory.DblVac.latD X v, h *ᵥ z ∈ GlobalTheory.DblVac.latD X v)
    {w₁ w₂ : Matrix (Fin n) (Fin d) (AE F E)} (hw₁ : w₁ ∈ latAtV X Y v) (hw₂ : w₂ ∈ latAtV X Y v) :
    ((Matrix.fromCols w₁ᵀ w₂ᵀ * hᵀ).toCols₁)ᵀ ∈ latAtV X Y v ∧
      ((Matrix.fromCols w₁ᵀ w₂ᵀ * hᵀ).toCols₂)ᵀ ∈ latAtV X Y v := by
  let T₁ : Matrix (Fin d) (Fin n ⊕ Fin n) (AE F E) →+ Matrix (Fin n) (Fin d) (AE F E) :=
    { toFun := fun γ => ((γ * hᵀ).toCols₁)ᵀ
      map_zero' := by ext i j; simp [Matrix.toCols₁]
      map_add' := fun γ γ' => by ext i j; simp [Matrix.toCols₁, Matrix.add_mul] }
  let T₂ : Matrix (Fin d) (Fin n ⊕ Fin n) (AE F E) →+ Matrix (Fin n) (Fin d) (AE F E) :=
    { toFun := fun γ => ((γ * hᵀ).toCols₂)ᵀ
      map_zero' := by ext i j; simp [Matrix.toCols₂]
      map_add' := fun γ γ' => by ext i j; simp [Matrix.toCols₂, Matrix.add_mul] }
  let S := (latAtV X Y v).comap T₁ ⊓ (latAtV X Y v).comap T₂
  have key : ∀ y ∈ Y.L, ∀ z ∈ GlobalTheory.DblVac.latD X v,
      Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (y i)) z ∈ S := by
    intro y hy z hz
    have hz' := hh z hz
    refine ⟨?_, ?_⟩
    · show ((Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (y i)) z * hᵀ).toCols₁)ᵀ ∈ latAtV X Y v
      have e : ((Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (y i)) z * hᵀ).toCols₁)ᵀ =
          Matrix.vecMulVec ((h *ᵥ z) ∘ Sum.inl) (fun i => inclR (F := F) (AF F) (y i)) := by
        rw [Matrix.vecMulVec_mul, Matrix.vecMul_transpose]
        ext i j
        simp [Matrix.toCols₁, Matrix.vecMulVec_apply, mul_comm]
      rw [e]
      exact GlobalTheory.VacTransportLeft.vecMulVec_mem_left X Y v hy hz'.1
    · show ((Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (y i)) z * hᵀ).toCols₂)ᵀ ∈ latAtV X Y v
      have e : ((Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (y i)) z * hᵀ).toCols₂)ᵀ =
          Matrix.vecMulVec ((h *ᵥ z) ∘ Sum.inr) (fun i => inclR (F := F) (AF F) (y i)) := by
        rw [Matrix.vecMulVec_mul, Matrix.vecMul_transpose]
        ext i j
        simp [Matrix.toCols₂, Matrix.vecMulVec_apply, mul_comm]
      rw [e]
      exact GlobalTheory.VacTransportLeft.vecMulVec_mem_left X Y v hy hz'.2
  let A₁ : Matrix (Fin n) (Fin d) (AE F E) →+ Matrix (Fin d) (Fin n ⊕ Fin n) (AE F E) :=
    { toFun := fun w => Matrix.fromCols wᵀ 0
      map_zero' := by ext i j; cases j <;> simp
      map_add' := fun w w' => by ext i j; cases j <;> simp }
  let A₂ : Matrix (Fin n) (Fin d) (AE F E) →+ Matrix (Fin d) (Fin n ⊕ Fin n) (AE F E) :=
    { toFun := fun w => Matrix.fromCols 0 wᵀ
      map_zero' := by ext i j; cases j <;> simp
      map_add' := fun w w' => by ext i j; cases j <;> simp }
  have hA₁ : latAtV X Y v ≤ S.comap A₁ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨a, ha, hai, x, hx, y, hy, rfl⟩
    have e : A₁ (a • incM F (Matrix.vecMulVec x y)) = Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (y i))
        (Sum.elim (a • fun i => inclR (F := F) (AF F) (x i)) 0) := by
      ext i j
      cases j with
      | inl j =>
        simp only [A₁, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.fromCols_apply_inl, Matrix.transpose_apply,
          Matrix.smul_apply, incM, Matrix.map_apply, Matrix.vecMulVec_apply, Sum.elim_inl, Pi.smul_apply, map_mul,
          Algebra.smul_def, Pi.mul_apply, Pi.algebraMap_apply]
        ring
      | inr j => simp [A₁, Matrix.vecMulVec_apply]
    show A₁ _ ∈ S
    rw [e]
    refine key y hy _ ⟨?_, ?_⟩
    · rw [Sum.elim_comp_inl]; exact AddSubgroup.subset_closure ⟨a, ha, hai, x, hx, rfl⟩
    · rw [Sum.elim_comp_inr]; exact zero_mem _
  have hA₂ : latAtV X Y v ≤ S.comap A₂ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨a, ha, hai, x, hx, y, hy, rfl⟩
    have e : A₂ (a • incM F (Matrix.vecMulVec x y)) = Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (y i))
        (Sum.elim 0 (a • fun i => inclR (F := F) (AF F) (x i))) := by
      ext i j
      cases j with
      | inl j => simp [A₂, Matrix.vecMulVec_apply]
      | inr j =>
        simp only [A₂, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.fromCols_apply_inr, Matrix.transpose_apply,
          Matrix.smul_apply, incM, Matrix.map_apply, Matrix.vecMulVec_apply, Sum.elim_inr, Pi.smul_apply, map_mul,
          Algebra.smul_def, Pi.mul_apply, Pi.algebraMap_apply]
        ring
    show A₂ _ ∈ S
    rw [e]
    refine key y hy _ ⟨?_, ?_⟩
    · rw [Sum.elim_comp_inl]; exact zero_mem _
    · rw [Sum.elim_comp_inr]; exact AddSubgroup.subset_closure ⟨a, ha, hai, x, hx, rfl⟩
  have hsum : Matrix.fromCols w₁ᵀ w₂ᵀ = A₁ w₁ + A₂ w₂ := by
    ext i j; cases j <;> simp [A₁, A₂]
  have hm : Matrix.fromCols w₁ᵀ w₂ᵀ ∈ S := hsum ▸ add_mem (hA₁ hw₁) (hA₂ hw₂)
  exact ⟨hm.1, hm.2⟩

theorem transport : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ (d' : Darboux (symp (cA σ) (-1 : AE F E) (incM F G.W.J) (incM F G.V.J)) (Fin a × Fin (a + a'))),
    (∀ x : Matrix (Fin a) (Fin (a + a')) (AE F E), d'.e xᵀ = G.M.co.e x) →
    ∀ (dd : Darboux (symp (cA σ) (-1 : AE F E) (incM F G.W.J) (dbl (incM F G.V.J))) ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')))),
    IsDblCoord (cA σ) (-1 : AE F E) (incM F G.W.J) (incM F G.V.J) d' dd →
    ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 →
    (∀ γ ∈ latAtV G.V G.W v, Acts (evFin F v) (G.M.co.rho B.ψ γ) (G.M.vac v)
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V.J) (incM F G.W.J) γ γ) • G.M.vac v)) →
    ∀ (omd : GlobalTheory.DblVac.UD σ G.V →* Module.End ℂ (((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → AF F) → ℂ)),
    IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1 : AE F E) (incM F G.W.J) (dbl (incM F G.V.J)) dd (X.β / X.α) (diagCols (Fin a)) omd →
    ∀ g ∈ GlobalTheory.DblVac.KD σ G.V v, ∀ φ ∈ SB ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → Fv F v), ∀ φ₁ ∈ SB ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → Fv F v),
    (∀ w₁ ∈ latAtV G.V G.W v, ∀ w₂ ∈ latAtV G.V G.W v,
      Acts (evFin F v) (dd.rho B.ψ (Matrix.fromCols w₁ᵀ w₂ᵀ)) φ
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.W.J) (dbl (incM F G.V.J))
          (Matrix.fromCols w₁ᵀ w₂ᵀ) (Matrix.fromCols w₁ᵀ w₂ᵀ)) • φ)) → Acts (evFin F v) (omd g) φ φ₁ →
    (∀ w₁ ∈ latAtV G.V G.W v, ∀ w₂ ∈ latAtV G.V G.W v,
      Acts (evFin F v) (dd.rho B.ψ (Matrix.fromCols w₁ᵀ w₂ᵀ)) φ₁
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.W.J) (dbl (incM F G.V.J))
          (Matrix.fromCols w₁ᵀ w₂ᵀ) (Matrix.fromCols w₁ᵀ w₂ᵀ)) • φ₁)) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' _ v w _ _ d' _ dd _ θ _ _ omd hsp g hg φ hφ φ₁ _ hfix hact w₁ hw₁ w₂ hw₂ r hr
  by_cases h0 : φ₁ = 0
  · subst h0
    funext x
    simp [Darboux.rho, schr, tens]
  have hr' : Rest (evFin F v) φ r := GlobalTheory.RestCofactor.rest_of_rest v φ₁ φ r h0 hφ hr
  obtain ⟨h1m, h2m⟩ := cols_mem G.V G.W v (GlobalTheory.DblVac.matD g⁻¹) (fun z hz => (hg.2 z hz).2) hw₁ hw₂
  have hsplit : Matrix.fromCols w₁ᵀ w₂ᵀ * (GlobalTheory.DblVac.matD g⁻¹)ᵀ =
      Matrix.fromCols (((Matrix.fromCols w₁ᵀ w₂ᵀ * (GlobalTheory.DblVac.matD g⁻¹)ᵀ).toCols₁)ᵀ)ᵀ
        (((Matrix.fromCols w₁ᵀ w₂ᵀ * (GlobalTheory.DblVac.matD g⁻¹)ᵀ).toCols₂)ᵀ)ᵀ := by
    rw [Matrix.transpose_transpose, Matrix.transpose_transpose, Matrix.fromCols_toCols]
  have hback : actB (cA σ) g (Matrix.fromCols w₁ᵀ w₂ᵀ * (GlobalTheory.DblVac.matD g⁻¹)ᵀ) = Matrix.fromCols w₁ᵀ w₂ᵀ := by
    change Matrix.fromCols w₁ᵀ w₂ᵀ * (GlobalTheory.DblVac.matD g⁻¹)ᵀ * (GlobalTheory.DblVac.matD g)ᵀ = _
    have e : GlobalTheory.DblVac.matD g * GlobalTheory.DblVac.matD g⁻¹ = 1 := Units.mul_inv g.1
    rw [Matrix.mul_assoc, ← Matrix.transpose_mul, e, Matrix.transpose_one, Matrix.mul_one]
  have hsy := GlobalTheory.VacTransport.symp_mul_transpose (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.W.J)
    (dbl (incM F G.V.J)) (GlobalTheory.DblVac.matD g⁻¹) (g⁻¹).2 (Matrix.fromCols w₁ᵀ w₂ᵀ) (Matrix.fromCols w₁ᵀ w₂ᵀ)
  have hf := hfix _ h1m _ h2m r hr'
  rw [← hsplit, hsy] at hf
  have h1 := hsp.2.1.impl g (Matrix.fromCols w₁ᵀ w₂ᵀ * (GlobalTheory.DblVac.matD g⁻¹)ᵀ) _ hr'.2
  rw [hback, hf, GlobalTheory.VacTransport.tens_smul, map_smul, hact r hr'] at h1
  rw [← h1, GlobalTheory.VacTransport.tens_smul]

end GlobalTheory.DblVacTransport

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledStabilizerWeilOperatorTransportsLatticeEiStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledStabilizer_weilOperator_transports_latticeEigen : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ (d' : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J)) (Fin a × Fin (a + a'))),
    (∀ x : Matrix (Fin a) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), d'.e xᵀ = G.M.co.e x) →
    ∀ (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J))) ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')))),
    IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) d' dd →
    ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 →
    (∀ γ ∈ latAtV G.V G.W v, Acts (evFin F v) (G.M.co.rho B.ψ γ) (G.M.vac v)
        (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ) • G.M.vac v)) →
    ∀ (omd : GlobalTheory.DblVac.UD σ G.V →* Module.End ℂ (((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → AF F) → ℂ)),
    IsUWeilSplit (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) B.ψ (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J)) dd (X.β / X.α) (diagCols (Fin a)) omd →
    ∀ g ∈ GlobalTheory.DblVac.KD σ G.V v, ∀ φ ∈ SB ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → Fv F v), ∀ φ₁ ∈ SB ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → Fv F v),
    (∀ w₁ ∈ latAtV G.V G.W v, ∀ w₂ ∈ latAtV G.V G.W v,
      Acts (evFin F v) (dd.rho B.ψ (Matrix.fromCols w₁ᵀ w₂ᵀ)) φ
        (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J))
          (Matrix.fromCols w₁ᵀ w₂ᵀ) (Matrix.fromCols w₁ᵀ w₂ᵀ)) • φ)) → Acts (evFin F v) (omd g) φ φ₁ →
    (∀ w₁ ∈ latAtV G.V G.W v, ∀ w₂ ∈ latAtV G.V G.W v,
      Acts (evFin F v) (dd.rho B.ψ (Matrix.fromCols w₁ᵀ w₂ᵀ)) φ₁
        (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J))
          (Matrix.fromCols w₁ᵀ w₂ᵀ) (Matrix.fromCols w₁ᵀ w₂ᵀ)) • φ₁)) := by
  first | exact @GlobalTheory.DblVacTransport.transport | exact GlobalTheory.DblVacTransport.transport | (intros; apply GlobalTheory.DblVacTransport.transport <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMatrixMomentSurjective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMatrixMomentSurjective
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LagrCoord

theorem det_ne_zero_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  have hD : (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1 : Matrix (Fin s) (Fin s) ℂ)).det ≠ 0 := by
    rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul, Matrix.det_neg, Matrix.det_one, mul_one]
    exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  intro h0
  apply hD
  rw [← hA, ← Matrix.det_submatrix_equiv_self e.symm,
    Matrix.submatrix_mul _ _ e.symm (id : Fin n → Fin n) e.symm Function.bijective_id,
    Matrix.submatrix_mul _ _ e.symm (id : Fin n → Fin n) id Function.bijective_id,
    Matrix.det_mul, Matrix.det_mul, Matrix.submatrix_id_id, h0, mul_zero, zero_mul]

theorem det_ne_zero_of_hasSig_smul {n r s : ℕ} {c : ℂ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig (c • M) r s) :
    M.det ≠ 0 := by
  intro h0
  apply det_ne_zero_of_hasSig h
  rw [Matrix.det_smul, h0, mul_zero]

theorem det_ne_zero_of_map {E : Type} [CommRing E] {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (f : E →+* ℂ)
    (h : (J.map f).det ≠ 0) : J.det ≠ 0 := by
  intro h0
  apply h
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]

theorem exists_coord : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (n d r s r' s' : ℕ) (X : Spc F E n) (W : Spc F E d), X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (Y : Matrix (Fin n) (Fin d) (Fv F v)), ∃ x : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
      At (evFin F v) x ∧ x.map (piW t) = 0 ∧ -((1 : GL (Fin n) (Fv F v)).1ᵀ * X.J.map t * (x).map (piW (t.comp σ)) * (W.J.map t)ᵀ * (1 : GL (Fin d) (Fv F v)).1) = Y := by
  intro F E _ _ _ _ _ σ B hB n d r s r' s' X W hX hW v t Y
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hXd : X.J.det ≠ 0 := det_ne_zero_of_map X.J (B.emb w).1 (det_ne_zero_of_hasSig (hX.sig w))
  have hWd : W.J.det ≠ 0 := det_ne_zero_of_map W.J (B.emb w).1 (det_ne_zero_of_hasSig_smul (hW.sig w))
  have ht : Function.Injective t := t.toRingHom.injective
  have hXt : IsUnit (X.J.map t).det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    apply hXd
    apply ht
    rw [map_zero, ← h0]
    exact (RingHom.map_det t.toRingHom X.J)
  have hWt : IsUnit ((W.J.map t)ᵀ).det := by
    rw [Matrix.det_transpose, isUnit_iff_ne_zero]
    intro h0
    apply hWd
    apply ht
    rw [map_zero, ← h0]
    exact (RingHom.map_det t.toRingHom W.J)
  obtain ⟨x, hxat, hx0, hx1⟩ := GlobalTheory.T.exists_splitPlace_adelicMatrix_given_components hB.cm v t (0 : Matrix (Fin n) (Fin d) (Fv F v))
    (-((X.J.map t)⁻¹ * Y * ((W.J.map t)ᵀ)⁻¹))
  refine ⟨x, hxat, hx0, ?_⟩
  rw [hx1]
  simp only [Units.val_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul, neg_neg]
  rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hWt, Matrix.mul_one,
    Matrix.mul_nonsing_inv_cancel_left _ _ hXt]

end GlobalTheory.LagrCoord
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMatrixMomentSurjectiveStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_matrix_moment_surjective : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (n d r s r' s' : ℕ) (X : Spc F E n) (W : Spc F E d), X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (Y : Matrix (Fin n) (Fin d) (Fv F v)), ∃ x : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
      At (evFin F v) x ∧ x.map (piW t) = 0 ∧ -((1 : GL (Fin n) (Fv F v)).1ᵀ * X.J.map t * (x).map (piW (t.comp σ)) * (W.J.map t)ᵀ * (1 : GL (Fin d) (Fv F v)).1) = Y := by
  first | exact @GlobalTheory.LagrCoord.exists_coord | exact GlobalTheory.LagrCoord.exists_coord | (intros; apply GlobalTheory.LagrCoord.exists_coord <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledVacuumLatticeStabilizerPreservesDoubledSp
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledVacuumLatticeStabilizerPreservesDoubledSp
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.DblVacEigen
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.DblVacStab

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

lemma vecMulVec_mul_transpose' {m k : Type} [Fintype k] {R : Type} [CommRing R] (p : m → R) (q : k → R)
    (M : Matrix k k R) : Matrix.vecMulVec p q * Mᵀ = Matrix.vecMulVec p (M *ᵥ q) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.transpose_apply, Matrix.mulVec, dotProduct,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

lemma vecMulVec_mem_latDbl {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (v : Pl (F := F)) {x : Fin n → E} (hx : x ∈ X.L)
    {q : Fin d ⊕ Fin d → AE F E} (hq : q ∈ GlobalTheory.DblVac.latD W v) :
    Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) q ∈ latDbl X W v := by
  refine ⟨?_, ?_⟩
  · have : (Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) q).toCols₁ =
        Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) (q ∘ Sum.inl) := by
      ext i j; simp [Matrix.toCols₁, Matrix.vecMulVec_apply]
    rw [this]; exact GlobalTheory.InertSphStab.vecMulVec_mem X W v hx hq.1
  · have : (Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) q).toCols₂ =
        Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) (q ∘ Sum.inr) := by
      ext i j; simp [Matrix.toCols₂, Matrix.vecMulVec_apply]
    rw [this]; exact GlobalTheory.InertSphStab.vecMulVec_mem X W v hx hq.2

theorem mul_transpose_mem_latDbl {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (v : Pl (F := F))
    (M : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E))
    (hM : ∀ q ∈ GlobalTheory.DblVac.latD W v, M *ᵥ q ∈ GlobalTheory.DblVac.latD W v) :
    ∀ γ ∈ latDbl X W v, γ * Mᵀ ∈ latDbl X W v := by

  let φ₁ : Matrix (Fin n) (Fin d) (AE F E) →+ Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E) :=
    AddMonoidHom.mk' (fun γ : Matrix (Fin n) (Fin d) (AE F E) =>
      (Matrix.fromCols γ 0 : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E)) * Mᵀ) (by
      intro a b; rw [← Matrix.add_mul]; congr 1; ext i (j | j) <;> simp)
  let φ₂ : Matrix (Fin n) (Fin d) (AE F E) →+ Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E) :=
    AddMonoidHom.mk' (fun γ : Matrix (Fin n) (Fin d) (AE F E) =>
      (Matrix.fromCols 0 γ : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E)) * Mᵀ) (by
      intro a b; rw [← Matrix.add_mul]; congr 1; ext i (j | j) <;> simp)
  have key : ∀ (φ : Matrix (Fin n) (Fin d) (AE F E) →+ Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E)),
      (∀ a : AF F, At (evFin F v) a → evFin F v a ∈ v.adicCompletionIntegers F → ∀ x ∈ X.L, ∀ y ∈ W.L,
        ∃ q ∈ GlobalTheory.DblVac.latD W v,
          φ (a • incM F (Matrix.vecMulVec x y)) = Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) q) →
      latAtV X W v ≤ (latDbl X W v).comap φ := by
    intro φ hφ
    refine (AddSubgroup.closure_le _).2 ?_
    rintro z ⟨a, ha, hai, x, hx, y, hy, rfl⟩
    obtain ⟨q, hq, he⟩ := hφ a ha hai x hx y hy
    show φ _ ∈ latDbl X W v
    rw [he]; exact vecMulVec_mem_latDbl X W v hx hq
  have gen : ∀ a : AF F, At (evFin F v) a → evFin F v a ∈ v.adicCompletionIntegers F → ∀ y ∈ W.L,
      (a • fun i => inclR (F := F) (AF F) (y i)) ∈ GlobalTheory.InertSph.latAt W v := fun a ha hai y hy =>
    AddSubgroup.subset_closure ⟨a, ha, hai, y, hy, rfl⟩
  have h₁ : latAtV X W v ≤ (latDbl X W v).comap φ₁ := by
    refine key φ₁ fun a ha hai x hx y hy => ⟨M *ᵥ Sum.elim (a • fun i => inclR (F := F) (AF F) (y i)) 0, hM _ ?_, ?_⟩
    · exact ⟨by simpa using gen a ha hai y hy, by simpa using (GlobalTheory.InertSph.latAt W v).zero_mem⟩
    · rw [← vecMulVec_mul_transpose']
      simp only [φ₁, AddMonoidHom.mk'_apply]
      congr 1
      rw [GlobalTheory.InertSphStab.incM_vecMulVec, GlobalTheory.InertSphStab.smul_vecMulVec]
      ext i (j | j) <;> simp [Matrix.vecMulVec_apply]
  have h₂ : latAtV X W v ≤ (latDbl X W v).comap φ₂ := by
    refine key φ₂ fun a ha hai x hx y hy => ⟨M *ᵥ Sum.elim 0 (a • fun i => inclR (F := F) (AF F) (y i)), hM _ ?_, ?_⟩
    · exact ⟨by simpa using (GlobalTheory.InertSph.latAt W v).zero_mem, by simpa using gen a ha hai y hy⟩
    · rw [← vecMulVec_mul_transpose']
      simp only [φ₂, AddMonoidHom.mk'_apply]
      congr 1
      rw [GlobalTheory.InertSphStab.incM_vecMulVec, GlobalTheory.InertSphStab.smul_vecMulVec]
      ext i (j | j) <;> simp [Matrix.vecMulVec_apply]
  intro γ hγ
  have hsplit : γ * Mᵀ = φ₁ γ.toCols₁ + φ₂ γ.toCols₂ := by
    simp only [φ₁, φ₂, AddMonoidHom.mk'_apply]
    rw [← Matrix.add_mul]
    congr 1
    ext i (j | j) <;> simp [Matrix.toCols₁, Matrix.toCols₂]
  rw [hsplit]
  exact (latDbl X W v).add_mem (h₁ hγ.1) (h₂ hγ.2)

end GlobalTheory.DblVacStab

theorem GlobalTheory.DblVac.kD_stab_latDbl : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n d : ℕ}
    (X : Spc F E n) (W : Spc F E d) (v : Pl (F := F)), ∀ g ∈ GlobalTheory.DblVac.KD σ W v, ∀ γ ∈ latDbl X W v,
      γ * (GlobalTheory.DblVac.matD g)ᵀ ∈ latDbl X W v ∧ γ * (GlobalTheory.DblVac.matD g⁻¹)ᵀ ∈ latDbl X W v := by
  intro F E _ _ _ _ _ σ n d X W v g hg γ hγ
  exact ⟨GlobalTheory.DblVacStab.mul_transpose_mem_latDbl X W v _ (fun q hq => (hg.2 q hq).1) γ hγ,
    GlobalTheory.DblVacStab.mul_transpose_mem_latDbl X W v _ (fun q hq => (hg.2 q hq).2) γ hγ⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledVacuumLatticeStabilizerPreservesDoubledSpStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.DblVacEigen
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledVacuumLatticeStabilizer_preserves_doubledSpaceLattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n d : ℕ}
    (X : Spc F E n) (W : Spc F E d) (v : Pl (F := F)), ∀ g ∈ GlobalTheory.DblVac.KD σ W v, ∀ γ ∈ latDbl X W v,
      γ * (GlobalTheory.DblVac.matD g)ᵀ ∈ latDbl X W v ∧ γ * (GlobalTheory.DblVac.matD g⁻¹)ᵀ ∈ latDbl X W v := by
  first | exact @GlobalTheory.DblVac.kD_stab_latDbl | exact GlobalTheory.DblVac.kD_stab_latDbl | (intros; apply GlobalTheory.DblVac.kD_stab_latDbl <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigRouteKernelIntegrableOnUnitaryQuotient
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareThetaTripleExistsSignatureRankAddLt
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareThetaTripleExistsSignatureRankAddLt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grid

namespace GlobalTheory.FunObj

theorem squareTriple_sig_rank_lt : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}
    (W : G.Weil) (t : T) (i j : Fin D.R.m) (hT : SquareTriple W t i j) (M : Vol G) (hM : M.Is t),
    ∃ p : ℕ, (∃ τ, Formalism.UG.HasSignature (gramAt D (G.V (.grid (i + 1) (j + 1))) τ) ((G.V (.grid (i + 1) (j + 1))).rank - p) p) ∧
      (G.V (.grid i (j + 1))).rank + (G.V (.grid (i + 1) j)).rank < 2 * ((G.V (.grid (i + 1) (j + 1))).rank - p) := by
  intro D T L sc G W t i j hT M hM
  obtain ⟨e, Bs, Γ, X, om, om', hX, hY, -⟩ := hT M hM
  let w : InfinitePlace D.host.F := Classical.arbitrary _
  obtain ⟨hrs, A, hA⟩ := hY.geo.hV.sig w
  obtain ⟨τ, hτ, -⟩ := hX.cart w
  refine ⟨Γ.p, ⟨τ, ?_⟩, ?_⟩
  · have hJ : Γ.V.J.map (Bs.emb w).1 = (gramAt D (G.V (.grid (↑i + 1) (↑j + 1))) τ).map (starRingEnd ℂ) := by
      ext k l
      simp [hX.JW, hτ, gramAt]
    rw [hJ] at hA
    generalize gramAt D (G.V (.grid (↑i + 1) (↑j + 1))) τ = J at hA ⊢
    have h' : (A.map (starRingEnd ℂ))ᵀ * J * A = Matrix.fromBlocks 1 0 0 (-1) := by
      have := congrArg (fun Z => Z.map (starRingEnd ℂ)) hA
      simp only [Matrix.map_mul, Matrix.transpose_map] at this
      have e1 : (J.map (starRingEnd ℂ)).map (starRingEnd ℂ) = J := by ext; simp
      have e2 : (A.map star).map (starRingEnd ℂ) = A := by ext; simp
      have e3 : (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin ((G.V (.grid (↑i + 1) (↑j + 1))).rank - Γ.p) ⊕ Fin Γ.p) (Fin ((G.V (.grid (↑i + 1) (↑j + 1))).rank - Γ.p) ⊕ Fin Γ.p) ℂ).map
          (starRingEnd ℂ) = Matrix.fromBlocks 1 0 0 (-1) := by
        ext (k | k) (l | l) <;> simp [Matrix.fromBlocks_map, Matrix.one_apply] <;> split_ifs <;> simp
      rw [e1, e2, e3] at this
      simpa only [Matrix.transpose_map] using this
    let f : Fin (G.V (.grid (↑i + 1) (↑j + 1))).rank ≃ Fin ((G.V (.grid (↑i + 1) (↑j + 1))).rank - Γ.p) ⊕ Fin Γ.p := (finSumFinEquiv.trans (finCongr hrs)).symm
    let P : Matrix (Fin ((G.V (.grid (↑i + 1) (↑j + 1))).rank - Γ.p) ⊕ Fin Γ.p) (Fin ((G.V (.grid (↑i + 1) (↑j + 1))).rank - Γ.p) ⊕ Fin Γ.p) ℂ := A.submatrix f.symm id
    have hP : Formalism.UG.cT (starRingEnd ℂ) P * J.reindex f f * P = Formalism.UG.Jpq ((G.V (.grid (↑i + 1) (↑j + 1))).rank - Γ.p) Γ.p := by
      have : Formalism.UG.cT (starRingEnd ℂ) P = (A.map (starRingEnd ℂ))ᵀ.submatrix id f.symm := by
        ext k l; rfl
      rw [this, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, h']
      rfl
    have hJJ : Formalism.UG.Jpq ((G.V (.grid (↑i + 1) (↑j + 1))).rank - Γ.p) Γ.p * Formalism.UG.Jpq ((G.V (.grid (↑i + 1) (↑j + 1))).rank - Γ.p) Γ.p = 1 := by
      simp [Formalism.UG.Jpq, Matrix.fromBlocks_multiply]
    have hl : (Formalism.UG.Jpq ((G.V (.grid (↑i + 1) (↑j + 1))).rank - Γ.p) Γ.p * (Formalism.UG.cT (starRingEnd ℂ) P * J.reindex f f)) * P = 1 := by
      rw [Matrix.mul_assoc, hP, hJJ]
    exact ⟨f, ⟨P, _, mul_eq_one_comm.mp hl, hl⟩, hP⟩
  · have h1 := Fintype.card_congr e
    simp only [Fintype.card_sum, Fintype.card_fin] at h1
    have h2 := hY.geo.lt
    have h3 := hY.geo.eBig
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.spV₁, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.spW₁, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.spW, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.spV] at h1 h2 h3
    omega

end GlobalTheory.FunObj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareThetaTripleExistsSignatureRankAddLtStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grid
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.squareThetaTriple_exists_signature_rank_add_lt : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}
    (W : G.Weil) (t : T) (i j : Fin D.R.m) (hT : SquareTriple W t i j) (M : Vol G) (hM : M.Is t),
    ∃ p : ℕ, (∃ τ, Formalism.UG.HasSignature (gramAt D (G.V (.grid (i + 1) (j + 1))) τ) ((G.V (.grid (i + 1) (j + 1))).rank - p) p) ∧
      (G.V (.grid i (j + 1))).rank + (G.V (.grid (i + 1) j)).rank < 2 * ((G.V (.grid (i + 1) (j + 1))).rank - p) := by
  first | exact @GlobalTheory.FunObj.squareTriple_sig_rank_lt | exact GlobalTheory.FunObj.squareTriple_sig_rank_lt | (intros; apply GlobalTheory.FunObj.squareTriple_sig_rank_lt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigRouteKernelIntegrableOnUnitaryQuotient
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grid

noncomputable section

namespace GlobalTheory.FunObj

theorem routeBig_kerBig_integrableOn : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (hWC : GlobalTheory.SquareSt.WeilConvergence) {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (hT : SquareTriple W t i j)
    (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j))),
    ∀ g : GA D (G.V (.grid i (j + 1))), IntegrableOn (kerBig W Θ g g₁) (M.fd (.grid (i + 1) (j + 1))) (M.ν (.grid (i + 1) (j + 1))) := by
  intro D T L sc G hWC μ₀ hL W B ρ t i j hT M hM Θ Θ' hΘ g₁ g
  have hHF : GlobalTheory.SquareComm.IsHaarFD _ (M.ν (.grid (i + 1) (j + 1))) (M.fd (.grid (i + 1) (j + 1))) :=
    (hM.vtx (.grid (i + 1) (j + 1)) ⟨i.2, j.2⟩).haar_fund
  obtain ⟨p, hsig, hrk⟩ := GlobalTheory.T.squareThetaTriple_exists_signature_rank_add_lt W t i j hT M hM
  have key : ∀ d ∈ Θ.support, Integrable (fun u => Θ d * (W.kerA (.right i (j + 1)) d.1.2 g u *
      W.kerA (.down t (i + 1) j) d.2 u g₁)) ((M.ν (.grid (i + 1) (j + 1))).restrict (M.fd (.grid (i + 1) (j + 1)))) := by
    intro d hd
    obtain ⟨ε, X, χ, χ', ω, hω, hX, Φ, hΦ, h, c, he⟩ := GlobalTheory.T.routeBigVertex_kernelProduct_eq_const_mul_thetaKernel hL W B ρ t i j hT M hM Θ Θ' hΘ d hd g g₁
    obtain ⟨N, C, hmi⟩ := hWC D W.ψ W.θ W.θ_is ε _ X χ χ' ω hω p hsig (hX ▸ hrk) _ _ hHF Φ hΦ
    refine Integrable.const_mul ?_ _
    simp_rw [he]
    exact ((hmi h).1).const_mul c
  have e : kerBig W Θ g g₁ = fun u => ∑ d ∈ Θ.support, Θ d * (W.kerA (.right i (j + 1)) d.1.2 g u *
      W.kerA (.down t (i + 1) j) d.2 u g₁) := by
    funext u; rfl
  rw [IntegrableOn, e]
  exact integrable_finsetSum _ key

end GlobalTheory.FunObj

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigRouteKernelIntegrableOnUnitaryQuotientStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bigRoute_kernel_integrableOn_unitary_quotient : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (hWC : GlobalTheory.SquareSt.WeilConvergence) {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (hT : SquareTriple W t i j)
    (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j))),
    ∀ g : GA D (G.V (.grid i (j + 1))), IntegrableOn (kerBig W Θ g g₁) (M.fd (.grid (i + 1) (j + 1))) (M.ν (.grid (i + 1) (j + 1))) := by
  first | exact @GlobalTheory.FunObj.routeBig_kerBig_integrableOn | exact GlobalTheory.FunObj.routeBig_kerBig_integrableOn | (intros; apply GlobalTheory.FunObj.routeBig_kerBig_integrableOn <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexFibreIsoUniversalGroupFramedPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexFibreIsoUniversalGroupFramedPoint
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
noncomputable section

namespace GlobalTheory.PtDeg

open Limits MonoidalCategory CartesianMonoidalCategory MonObj

theorem fibre_iso_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (ρ : E →+* ℂ) (v : Fin (Dw.mult ρ) → Fin F.P₀.g → K), GlobalTheory.PtDeg.FrameCoord y m1 m2 F ρ v → ∀ (σ : K →+* ℂ) (φ : K →ₐ[c.F] CAt (σ.comp (algebraMap c.F K))), (∀ a, toC (φ a) = σ a) → ∀ (z : FrPt Xo c (CAt (σ.comp (algebraMap c.F K)))), FrMap φ y z → ∀ (Q : ReciprocityTheory.ChartRestriction.G.Out.PolAV (Sp ℂ)) (ψ : Q.A.left ⟶ F.P₀.A.left) (v' : Fin F.P₀.g → (epsR ℂ ⟶ Q.A)), GlobalTheory.IsPolFibre σ F.P₀ Q ψ → (∀ i, GlobalTheory.IsVecOver σ ψ (F.v i) (v' i)) → ∀ (T : GlobalTheory.CM.PAT H (Sp ℂ)) (m : SABMap T.t Xo.univ.t z.x), ∃ f : Q.A ⟶ T.pol.A, IsMonHom f ∧ LBIso (lbPow (T.pol.L.pull f.left) 1) (lbPow Q.L 1) ∧ ∀ i (q : epsR ℂ ⟶ Q.A), IsLieComb (fun k => σ (v i k)) v' q → ∀ w' : epsR ℂ ⟶ T.pol.A, w'.left ≫ m.φ = z.u ρ i → q ≫ f = w' := by
  intro E _ _ _ H Dw l Xo c K _ _ _ y B t₀ m1 m2 F ρ v hFC σ φ hφ z hz Q ψ v' hQ hv' T m

  have hφσ : (φ.toRingHom : K →+* ℂ) = σ := RingHom.ext hφ
  have hbase : z.x = spMap σ ≫ y.x := by rw [hz.1, hφσ]; rfl

  have hcomp := hQ.2.1.comp F.fib.2.1
  have w0 : (ψ ≫ F.φ) ≫ B.t.G.hom = (Q.A.hom ≫ spMap σ) ≫ spMap (algebraMap (𝓞 K) K) := by
    rw [hcomp.1.w, Category.assoc]
  let χ₀ : Q.A.left ⟶ t₀.G.left := m2.cart.1.lift (ψ ≫ F.φ) (Q.A.hom ≫ spMap σ) w0
  have hχ₀2 : χ₀ ≫ m2.φ = ψ ≫ F.φ := m2.cart.1.lift_fst _ _ w0
  have hχ₀b : χ₀ ≫ t₀.G.hom = Q.A.hom ≫ spMap σ := m2.cart.1.lift_snd _ _ w0
  have hχ₀ : IsGrpPullback Q.A t₀.G (spMap σ) χ₀ := m2.cart.cancel (by rw [hχ₀2]; exact hcomp) hχ₀b
  have hχ := hχ₀.comp m1.cart
  have w1 : (χ₀ ≫ m1.φ) ≫ Xo.univ.t.G.hom = Q.A.hom ≫ z.x := by rw [hχ.1.w, hbase]
  let fl : Q.A.left ⟶ T.t.G.left := m.cart.1.lift (χ₀ ≫ m1.φ) Q.A.hom w1
  have hfl : fl ≫ m.φ = χ₀ ≫ m1.φ := m.cart.1.lift_fst _ _ w1
  have hflb : fl ≫ T.t.G.hom = Q.A.hom := m.cart.1.lift_snd _ _ w1
  let f : Q.A ⟶ T.pol.A := Over.homMk fl hflb
  refine ⟨f, ?_, ?_, ?_⟩
  ·
    refine GlobalTheory.DivisibleHom.isMonHom_of_mul_points f fun S x y => ?_
    apply Over.OverMorphism.ext
    apply m.cart.1.hom_ext
    · have e1 := hχ.2 S x y (pushPt hχ.1.w x) (pushPt hχ.1.w y) rfl rfl
      have e2 := m.cart.2 S (x ≫ f) (y ≫ f) (pushPt m.cart.1.w (x ≫ f)) (pushPt m.cart.1.w (y ≫ f)) rfl rfl
      rw [Over.comp_left, Category.assoc]
      change _ ≫ fl ≫ m.φ = _
      rw [hfl, ← e1, ← e2]
      refine mul_left_congr (by rw [hbase]) _ _ _ _ ?_ ?_
      · show x.left ≫ χ₀ ≫ m1.φ = (x.left ≫ fl) ≫ m.φ
        rw [Category.assoc, hfl]
      · show y.left ≫ χ₀ ≫ m1.φ = (y.left ≫ fl) ≫ m.φ
        rw [Category.assoc, hfl]
    · exact (Over.w ((x * y) ≫ f)).trans (Over.w ((x ≫ f) * (y ≫ f))).symm
  ·
    obtain ⟨wT, hwT, -⟩ := m.lin
    obtain ⟨w1', hw1', -⟩ := m1.lin
    obtain ⟨w2', hw2', -⟩ := m2.lin
    have hT : LBIso T.t.PP.L (Xo.univ.t.PP.L.pull m.φ) := ⟨wT, hwT⟩
    have h1 : LBIso t₀.PP.L (Xo.univ.t.PP.L.pull m1.φ) := ⟨w1', hw1'⟩
    have h2 : LBIso t₀.PP.L (B.t.PP.L.pull m2.φ) := ⟨w2', hw2'⟩
    have hT2 := GlobalTheory.CM.EllComp.lbIso_pull_comp hT.symm fl
    rw [hfl] at hT2
    have h3 := GlobalTheory.CM.EllComp.lbIso_pull_comp h1.symm χ₀
    have h4 := GlobalTheory.CM.EllComp.lbIso_pull_comp h2.symm χ₀
    rw [hχ₀2] at h4
    have h5 : LBIso (B.t.PP.L.pull (ψ ≫ F.φ)) (F.P₀.L.pull ψ) := GlobalTheory.CM.EllComp.lbIso_pull_comp F.fib.2.2 ψ
    have e45 := LBIso.trans (pull_isLB B.t.PP.isLB _) (pull_isLB F.P₀.isLB ψ) Q.isLB h5 hQ.2.2
    have e345 := LBIso.trans (pull_isLB t₀.PP.isLB χ₀) (pull_isLB B.t.PP.isLB _) Q.isLB h4.symm e45
    have e2345 := LBIso.trans (pull_isLB Xo.univ.t.PP.isLB _) (pull_isLB t₀.PP.isLB χ₀) Q.isLB h3 e345
    have main : LBIso (T.t.PP.L.pull fl) Q.L :=
      LBIso.trans (pull_isLB T.t.PP.isLB fl) (pull_isLB Xo.univ.t.PP.isLB _) Q.isLB hT2.symm e2345
    exact GlobalTheory.lbIso_lbPow main 1
  ·
    intro i q hq w' hw'
    obtain ⟨u, w, hu1, hu2, hw⟩ := hFC i
    haveI := GlobalTheory.ShFam.OpenReg.mono_spMap_algebraMap (𝓞 K) K
    have hFw : F.φ ≫ B.t.G.hom = F.P₀.A.hom ≫ spMap (algebraMap (𝓞 K) K) := F.fib.2.1.1.w
    have hu3 : u ≫ t₀.G.hom = spMap (algebraMap K (DualNumber K)) := by
      rw [← cancel_mono (spMap (algebraMap (𝓞 K) K))]
      calc (u ≫ t₀.G.hom) ≫ spMap (algebraMap (𝓞 K) K) = (u ≫ m2.φ) ≫ B.t.G.hom := by
            rw [Category.assoc, Category.assoc, m2.cart.1.w]
        _ = (w.left ≫ F.P₀.A.hom) ≫ spMap (algebraMap (𝓞 K) K) := by
            rw [hu2, Category.assoc, hFw, Category.assoc]
        _ = spMap (algebraMap K (DualNumber K)) ≫ spMap (algebraMap (𝓞 K) K) := by rw [Over.w w]; rfl
    obtain ⟨q', hq', -⟩ := GlobalTheory.existsUnique_isVecOver hQ.2.1.1 w
    have hq'c : IsLieComb (fun k => σ (v i k)) v' q' := by
      let d := ReciprocityTheory.ChartRestriction.G.Chart.dualMapR σ
      have dover : spMap d ≫ spMap (algebraMap K (DualNumber K)) =
          spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap σ := by
        rw [GlobalTheory.spMap_comp_spMap, GlobalTheory.spMap_comp_spMap]
        congr 1
        ext r <;> simp [d, ReciprocityTheory.ChartRestriction.G.Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
      have dscale (a : K) : spMap d ≫ spMap (epsScaleR a) =
          spMap (epsScaleR (σ a)) ≫ spMap d := by
        rw [GlobalTheory.spMap_comp_spMap, GlobalTheory.spMap_comp_spMap]
        congr 1
        ext r <;> simp [d, ReciprocityTheory.ChartRestriction.G.Chart.dualMapR, epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
      rw [GlobalTheory.ArcQ.NormalForm.isLieComb_iff] at hw ⊢
      let U : Over.mk ((epsR ℂ).hom ≫ spMap σ) ⟶ epsR K := Over.homMk (spMap d) dover
      have e₁ := map_list_prod (pushHom hQ.2.1 (epsR ℂ)) (List.ofFn fun k => GlobalTheory.ArcQ.NormalForm.sc (σ (v i k)) ≫ v' k)
      have e₂ := map_list_prod (ReciprocityTheory.ChartRestriction.G.Geo.Tor.preHom (G := F.P₀.A) U) (List.ofFn fun k => GlobalTheory.ArcQ.NormalForm.sc (v i k) ≫ F.v k)
      rw [List.map_ofFn] at e₁ e₂
      have e₃ : (pushHom hQ.2.1 (epsR ℂ)) ∘ (fun k => GlobalTheory.ArcQ.NormalForm.sc (σ (v i k)) ≫ v' k) =
          (ReciprocityTheory.ChartRestriction.G.Geo.Tor.preHom (G := F.P₀.A) U) ∘ fun k => GlobalTheory.ArcQ.NormalForm.sc (v i k) ≫ F.v k :=
        funext fun k => Over.OverMorphism.ext (by
          show (spMap (epsScaleR (σ (v i k))) ≫ (v' k).left) ≫ ψ =
            spMap d ≫ spMap (epsScaleR (v i k)) ≫ (F.v k).left
          rw [Category.assoc, hv', ← Category.assoc, ← Category.assoc, dscale])
      rw [e₃, ← e₂, ← hw] at e₁
      apply Over.OverMorphism.ext
      apply hQ.2.1.1.hom_ext
      · exact hq'.trans (congrArg (·.left) e₁).symm
      · rw [Over.w, Over.w]
    have hqq : q = q' := by
      obtain ⟨a, ha, rfl⟩ := hq
      obtain ⟨b, hb, rfl⟩ := hq'c
      have hab : a = b := funext fun k => Over.OverMorphism.ext ((ha k).trans (hb k).symm)
      rw [hab]
    subst hqq
    have key : q.left ≫ χ₀ = spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR σ) ≫ u := by
      apply m2.cart.1.hom_ext
      · rw [Category.assoc, hχ₀2, Category.assoc, hu2, ← Category.assoc, ← Category.assoc]
        exact congrArg (· ≫ F.φ) hq'
      · rw [Category.assoc, hχ₀b, Category.assoc, hu3, ← Category.assoc, Over.w q]
        show spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap σ = _
        rw [GlobalTheory.spMap_comp_spMap, GlobalTheory.spMap_comp_spMap]
        congr 1
        ext a <;> simp [ReciprocityTheory.ChartRestriction.G.Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
    apply Over.OverMorphism.ext
    apply m.cart.1.hom_ext
    · rw [hw', hz.2.1, ← hu1, hφσ]
      change (q.left ≫ fl) ≫ m.φ = _
      rw [Category.assoc, hfl, ← Category.assoc, key, Category.assoc]
      rfl
    · exact (Over.w (q ≫ f)).trans (Over.w w').symm

end GlobalTheory.PtDeg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexFibreIsoUniversalGroupFramedPointStatement
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complex_fibre_iso_universal_group_framed_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (ρ : E →+* ℂ) (v : Fin (Dw.mult ρ) → Fin F.P₀.g → K), GlobalTheory.PtDeg.FrameCoord y m1 m2 F ρ v → ∀ (σ : K →+* ℂ) (φ : K →ₐ[c.F] CAt (σ.comp (algebraMap c.F K))), (∀ a, toC (φ a) = σ a) → ∀ (z : FrPt Xo c (CAt (σ.comp (algebraMap c.F K)))), FrMap φ y z → ∀ (Q : ReciprocityTheory.ChartRestriction.G.Out.PolAV (Sp ℂ)) (ψ : Q.A.left ⟶ F.P₀.A.left) (v' : Fin F.P₀.g → (epsR ℂ ⟶ Q.A)), GlobalTheory.IsPolFibre σ F.P₀ Q ψ → (∀ i, GlobalTheory.IsVecOver σ ψ (F.v i) (v' i)) → ∀ (T : GlobalTheory.CM.PAT H (Sp ℂ)) (m : SABMap T.t Xo.univ.t z.x), ∃ f : Q.A ⟶ T.pol.A, IsMonHom f ∧ LBIso (lbPow (T.pol.L.pull f.left) 1) (lbPow Q.L 1) ∧ ∀ i (q : epsR ℂ ⟶ Q.A), IsLieComb (fun k => σ (v i k)) v' q → ∀ w' : epsR ℂ ⟶ T.pol.A, w'.left ≫ m.φ = z.u ρ i → q ≫ f = w' := by
  first | exact @GlobalTheory.PtDeg.fibre_iso_frame | exact GlobalTheory.PtDeg.fibre_iso_frame | (intros; apply GlobalTheory.PtDeg.fibre_iso_frame <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryDeterminantOpenImage
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryDeterminantOpenImage
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun MeasureTheory Topology
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.SkewLeviNear

open GlobalTheory.EmbChart GlobalTheory.LeviAtPlace GlobalTheory.SkewLevi

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {v : HeightOneSpectrum (𝓞 F)} {n : ℕ}

theorem continuous_atPlace : Continuous (atPlace (F := F) v) :=
  Continuous.prodMk continuous_const (GlobalTheory.AdelicU.continuous_singleFin v)

theorem continuous_linear_prod (f : Fv F v × Fv F v →ₗ[Fv F v] Fv F v) : Continuous f := by
  have e : ∀ p : Fv F v × Fv F v, f p = p.1 * f (1, 0) + p.2 * f (0, 1) := by
    intro p
    rw [← smul_eq_mul, ← smul_eq_mul, ← map_smul, ← map_smul, ← map_add (f := _)]
    congr 1
    ext <;> simp
  have : (f : Fv F v × Fv F v → Fv F v) = fun p => p.1 * f (1, 0) + p.2 * f (0, 1) := funext e
  rw [this]
  exact (continuous_fst.mul continuous_const).add (continuous_snd.mul continuous_const)

theorem continuous_tensAt_split (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) :
    Continuous fun p : Fv F v × Fv F v => tensAt E v ((splitAlgEquiv h t).symm p) := by
  let b := Module.Free.chooseBasis F E
  let bv := Algebra.TensorProduct.basis (Fv F v) b
  have key : ∀ y : TensorProduct F (Fv F v) E,
      tensAt E v y = ∑ i, atPlace v (bv.repr y i) • ((1 : AF F) ⊗ₜ[F] b i) := by
    intro y
    conv_lhs => rw [← bv.sum_repr y]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one, tensAt_tmul,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have : (fun p : Fv F v × Fv F v => tensAt E v ((splitAlgEquiv h t).symm p)) =
      fun p => ∑ i, atPlace v (bv.repr ((splitAlgEquiv h t).symm p) i) • ((1 : AF F) ⊗ₜ[F] b i) :=
    funext fun p => key _
  rw [this]
  have : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) (AE F E)
  have : ContinuousSMul (AF F) (AE F E) := IsModuleTopology.toContinuousSMul (AF F) (AE F E)
  refine continuous_finsetSum _ fun i _ => ?_
  have hc : Continuous fun p : Fv F v × Fv F v => atPlace v (bv.repr ((splitAlgEquiv h t).symm p) i) :=
    continuous_atPlace.comp (continuous_linear_prod ((bv.coord i).comp (splitAlgEquiv h t).symm.toLinearMap))
  exact hc.smul (continuous_const : Continuous fun _ : Fv F v × Fv F v => ((1 : AF F) ⊗ₜ[F] b i : AE F E))

end GlobalTheory.SkewLeviNear

namespace GlobalTheory.SkewLeviNear

open GlobalTheory.EmbChart GlobalTheory.LeviAtPlace GlobalTheory.SkewLevi

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {v : HeightOneSpectrum (𝓞 F)} {n : ℕ}

theorem continuous_lift_locMat (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (J : Matrix (Fin n) (Fin n) E) :
    Continuous fun g : GL (Fin n) (Fv F v) => lift v (locMat h t J g) := by
  have hc : Continuous fun g : GL (Fin n) (Fv F v) => conjComp t J g :=
    (continuous_const.matrix_mul Units.continuous_coe_inv.matrix_transpose).matrix_mul continuous_const
  refine continuous_matrix fun i j => ?_
  have e : (fun g : GL (Fin n) (Fv F v) => lift v (locMat h t J g) i j) = fun g : GL (Fin n) (Fv F v) =>
      (1 : Matrix (Fin n) (Fin n) (AE F E)) i j +
        (tensAt E v ((splitAlgEquiv h t).symm ((g : Matrix (Fin n) (Fin n) (Fv F v)) i j, conjComp t J g i j)) +
          -tensAt E v ((1 : Matrix (Fin n) (Fin n) (TensorProduct F (Fv F v) E)) i j)) := by
    funext g
    simp only [lift, ext0, Matrix.add_apply, Matrix.map_apply, Matrix.sub_apply, map_sub]
    rw [sub_eq_add_neg]
    rfl
  rw [e]
  have : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) (AE F E)
  refine continuous_const.add (Continuous.add ?_ continuous_const)
  refine (continuous_tensAt_split h t).comp (Continuous.prodMk ?_ ?_)
  · exact (Units.continuous_val.matrix_elem i j)
  · exact hc.matrix_elem i j

end GlobalTheory.SkewLeviNear

namespace GlobalTheory.SkewLeviNear

open GlobalTheory.EmbChart GlobalTheory.LeviAtPlace GlobalTheory.SkewLevi

theorem near_one_det : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v → ∀ (t : E →ₐ[F] Fv F v), ∀ U ∈ 𝓝 (1 : UA σ G.W.J), ∃ V ∈ 𝓝 (1 : (Fv F v)ˣ), ∀ x ∈ V,
      ∃ h ∈ UAt σ G.W (evFin F v), h ∈ U ∧ ((mat h).map (piW t)).det = (x : Fv F v) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v _ t U hU
  have h := hTr.base.cm
  have hJ : IsUnit (G.W.J.map t).det := by
    obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
    have h0 := det_ne_zero_of_sig (hTr.geo.hW.sig (InfinitePlace.mk φ))
    have h1 : G.W.J.det ≠ 0 := fun e => h0 (by
      rw [Matrix.det_smul, show G.W.J.map _ = RingHom.mapMatrix _ G.W.J from rfl, ← RingHom.map_det, e, map_zero,
        mul_zero])
    rw [show G.W.J.map t = (t : E →+* Fv F v).mapMatrix G.W.J from rfl, ← RingHom.map_det]
    exact isUnit_iff_ne_zero.2 ((map_ne_zero _).2 h1)
  let Ψ : GL (Fin (a + a')) (Fv F v) → UA σ G.W.J := fun g =>
    ⟨adelicGL h t G.W.J hJ g, lift_unitary v σ G.W.J _ (locMat_unitary_skew h t G.W.J hJ hTr.geo.hW.skew g)⟩
  have hΨc : Continuous Ψ := by
    refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨continuous_lift_locMat h t G.W.J, ?_⟩) _
    exact (continuous_lift_locMat h t G.W.J).comp continuous_inv
  have hΨ1 : Ψ 1 = 1 := Subtype.ext (Units.ext (by
    change lift v (LeviAtPlace.locMat h t G.W.J 1) = 1
    rw [locMat_one h t G.W.J hJ, lift_one]))
  have hΨt : ∀ g, (mat (Ψ g)).map (piW t) = g.1 := by
    intro g
    change (lift v (LeviAtPlace.locMat h t G.W.J g)).map (piW t) = g.1
    have key : (lift v (LeviAtPlace.locMat h t G.W.J g)).map (piW t) =
        (LeviAtPlace.locMat h t G.W.J g).map (splitProj t) := by
      conv_rhs => rw [← compFin_lift v (LeviAtPlace.locMat h t G.W.J g), Matrix.map_map]
      rfl
    rw [key]
    exact pairMat_fst h t _ _
  have i0 : Fin (a + a') := ⟨0, by have := hTr.geo.lt; omega⟩
  let D : (Fv F v)ˣ →* GL (Fin (a + a')) (Fv F v) :=
    Units.map ((Matrix.diagonalRingHom (Fin (a + a')) (Fv F v)).toMonoidHom.comp
      (MonoidHom.mulSingle (fun _ => Fv F v) i0))
  have hDv : ∀ x : (Fv F v)ˣ, ((D x : GL (Fin (a + a')) (Fv F v)) : Matrix (Fin (a + a')) (Fin (a + a')) (Fv F v)) =
      Matrix.diagonal (Pi.mulSingle i0 (x : Fv F v)) := fun x => rfl
  have hDc : Continuous D := by
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · have : (Units.val ∘ D) = fun x : (Fv F v)ˣ => Matrix.diagonal (Pi.mulSingle i0 (x : Fv F v)) := funext hDv
      rw [this]
      exact (continuous_mulSingle i0 |>.comp Units.continuous_val).matrix_diagonal
    · have : (fun x => ((D x)⁻¹ : GL (Fin (a + a')) (Fv F v)).1) =
          fun x : (Fv F v)ˣ => Matrix.diagonal (Pi.mulSingle i0 ((x⁻¹ : (Fv F v)ˣ) : Fv F v)) := by
        funext x; rw [← map_inv]; rfl
      rw [this]
      exact (continuous_mulSingle i0 |>.comp Units.continuous_coe_inv).matrix_diagonal
  have hf : Continuous fun x => Ψ (D x) := hΨc.comp hDc
  have hf1 : Ψ (D 1) = 1 := by rw [map_one, hΨ1]
  refine ⟨(fun x => Ψ (D x)) ⁻¹' U, hf.continuousAt.preimage_mem_nhds (by rw [hf1]; exact hU), fun x hx => ?_⟩
  refine ⟨Ψ (D x), lift_sub_one_at v _, hx, ?_⟩
  rw [hΨt, hDv, Matrix.det_diagonal]
  simp

end GlobalTheory.SkewLeviNear
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryDeterminantOpenImageStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun MeasureTheory Topology
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_determinant_open_image : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v → ∀ (t : E →ₐ[F] Fv F v), ∀ U ∈ 𝓝 (1 : UA σ G.W.J), ∃ V ∈ 𝓝 (1 : (Fv F v)ˣ), ∀ x ∈ V,
      ∃ h ∈ UAt σ G.W (evFin F v), h ∈ U ∧ ((mat h).map (piW t)).det = (x : Fv F v) := by
  first | exact @GlobalTheory.SkewLeviNear.near_one_det | exact GlobalTheory.SkewLeviNear.near_one_det | (intros; apply GlobalTheory.SkewLeviNear.near_one_det <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCharacterRationalValues
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open Formalism.IndefR.FWT GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.LevVal

theorem envV_chi_mem {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (h : R.Char F)
    (j : Fin D.R.m) (t : T0) (k : (GlobalTheory.TraceIncl.envV R j t).J) :
    ∃ a : D.what₂.LL, D.what₂.embLL a = (((GlobalTheory.TraceIncl.envV R j t).χ k : ℂˣ) : ℂ) := by
  obtain ⟨a, ha⟩ := hχ_of R j t
    (fun PP hP u => let ⟨a, ha⟩ := GlobalTheory.ConjForms.chi_mem R h.grp.chiW j PP hP u; ⟨a, ha.symm⟩)
    (fun PP hP u => let ⟨a, ha⟩ := GlobalTheory.PinsOverField.xiR_mem R h.lev h.fam t PP hP u; ⟨a, ha.symm⟩) k
  exact ⟨a, ha.symm⟩

end GlobalTheory.BigOn.LevVal
end
