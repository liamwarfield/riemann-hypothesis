module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformizationLawsOfGoodDeepCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearModelUnitaryConjugate

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTensorLocalVanish
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTensorLocalVanish
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.DblTrace

open Matrix

theorem hTens_dbl {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
    {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] (JA : Matrix α α E) (JB : Matrix β β E)
    (x y : Matrix α (β ⊕ β) E) :
    hTens c JA (dbl JB) x y = hTens c JA JB x.toCols₁ y.toCols₁ + hTens c JA (-JB) x.toCols₂ y.toCols₂ := by
  simp only [hTens, dbl, Fintype.sum_sum_type, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
    fromBlocks_apply₂₂, Matrix.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add, toCols₁, toCols₂,
    of_apply, ← Finset.sum_add_distrib]

theorem rhs_dbl {K : Type} [CommRing K] {m n : Type} [Fintype m] [Fintype n] (A : Matrix m m K)
    (X U : Matrix m (n ⊕ n) K) (B : Matrix n n K) :
    ∑ k, ∑ l, (-(A * X * (fromBlocks B 0 0 (-B))ᵀ)) k l * U k l =
      ∑ k, ∑ l, (-(A * X.toCols₁ * Bᵀ)) k l * U.toCols₁ k l +
        ∑ k, ∑ l, (-(A * X.toCols₂ * (-B)ᵀ)) k l * U.toCols₂ k l := by
  have hX : A * X = fromCols (A * X.toCols₁) (A * X.toCols₂) := by
    conv_lhs => rw [← fromCols_toCols X]
    rw [mul_fromCols]
  rw [hX, fromBlocks_transpose, fromCols_mul_fromBlocks]
  simp [Fintype.sum_sum_type, Finset.sum_add_distrib, toCols₁, toCols₂]
  ring

end GlobalTheory.DblTrace

open GlobalTheory.DblTrace in
theorem GlobalTheory.DblTrace.trace_pairing_dbl : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E},
    IsCMExt F E σ → ∀ {v : Pl (F := F)} (τ : E →ₐ[F] Fv F v) {m n : ℕ} (JA : Matrix (Fin m) (Fin m) E)
    (JB : Matrix (Fin n) (Fin n) E), (∀ i j, σ (JA j i) = JA i j) → (∀ i j, σ (JB j i) = -JB i j) →
    ∀ (x u : Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E)), x.map (piW τ) = 0 → u.map (piW (τ.comp σ)) = 0 →
    piW τ (hTens (cA σ) (incM F JA) (dbl (incM F JB)) x u) + piW (τ.comp σ) (hTens (cA σ) (incM F JA) (dbl (incM F JB)) x u) =
      ∑ k, ∑ l, (-(JA.map τ * x.map (piW (τ.comp σ)) * ((dbl JB).map τ)ᵀ)) k l * u.map (piW τ) k l := by
  intro F E _ _ _ _ _ σ hcm v τ m n JA JB hA hB x u hx hu
  have hneg : incM F (-JB) = -incM F JB := by
    simp [incM, Matrix.map_neg]
  have hB' : ∀ i j, σ ((-JB) j i) = -(-JB) i j := by
    intro i j; simp [hB]
  have h1 : x.toCols₁.map (piW τ) = 0 := by
    exact Matrix.ext fun i j => congrFun (congrFun hx i) (Sum.inl j)
  have h2 : u.toCols₁.map (piW (τ.comp σ)) = 0 := by
    exact Matrix.ext fun i j => congrFun (congrFun hu i) (Sum.inl j)
  have h3 : x.toCols₂.map (piW τ) = 0 := by
    exact Matrix.ext fun i j => congrFun (congrFun hx i) (Sum.inr j)
  have h4 : u.toCols₂.map (piW (τ.comp σ)) = 0 := by
    exact Matrix.ext fun i j => congrFun (congrFun hu i) (Sum.inr j)
  have hd : (dbl JB).map τ = Matrix.fromBlocks (JB.map τ) 0 0 (-(JB.map τ)) := by
    ext i j; rcases i with i | i <;> rcases j with j | j <;> simp [dbl]
  rw [hTens_dbl, ← hneg, map_add (f := _), map_add (f := _), add_add_add_comm, GlobalTheory.T.hermitianTensor_skewHermitian_split_symplectic_pair hcm τ JA JB hA hB _ _ h1 h2,
    GlobalTheory.T.hermitianTensor_skewHermitian_split_symplectic_pair hcm τ JA (-JB) hA hB' _ _ h3 h4, hd, rhs_dbl]
  have hm : (-JB).map τ = -(JB.map τ) := by ext i j; simp
  rw [hm]
  rfl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTensorLocalVanishStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_tensor_local_vanish : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E},
    IsCMExt F E σ → ∀ {v : Pl (F := F)} (τ : E →ₐ[F] Fv F v) {m n : ℕ} (JA : Matrix (Fin m) (Fin m) E)
    (JB : Matrix (Fin n) (Fin n) E), (∀ i j, σ (JA j i) = JA i j) → (∀ i j, σ (JB j i) = -JB i j) →
    ∀ (x u : Matrix (Fin m) (Fin n ⊕ Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), x.map (piW τ) = 0 → u.map (piW (τ.comp σ)) = 0 →
    piW τ (hTens (cA σ) (incM F JA) (dbl (incM F JB)) x u) + piW (τ.comp σ) (hTens (cA σ) (incM F JA) (dbl (incM F JB)) x u) =
      ∑ k, ∑ l, (-(JA.map τ * x.map (piW (τ.comp σ)) * ((dbl JB).map τ)ᵀ)) k l * u.map (piW τ) k l := by
  first | exact @GlobalTheory.DblTrace.trace_pairing_dbl | exact GlobalTheory.DblTrace.trace_pairing_dbl | (intros; apply GlobalTheory.DblTrace.trace_pairing_dbl <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepBijectionSchwartz
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepBijectionSchwartz
open Matrix

namespace GlobalTheory.SchurHeisReindex

variable {k : Type} [Field k] [TopologicalSpace k] {n : ℕ} {β : Type} [Fintype β] [DecidableEq β]

noncomputable def eL (k : Type) [Field k] (n : ℕ) (β : Type) [Fintype β] [DecidableEq β] :
    Matrix (Fin n) (Fin (Fintype.card β)) k ≃ₗ[k] Matrix (Fin n) β k :=
  Matrix.reindexLinearEquiv k k (Equiv.refl (Fin n)) (Fintype.equivFin β).symm

theorem eL_apply (C : Matrix (Fin n) (Fin (Fintype.card β)) k) (i : Fin n) (b : β) :
    eL k n β C i b = C i (Fintype.equivFin β b) := by
  simp [eL, reindexLinearEquiv_apply, reindex_apply, submatrix_apply]

theorem eL_symm_apply (D : Matrix (Fin n) β k) (i : Fin n) (j : Fin (Fintype.card β)) :
    (eL k n β).symm D i j = D i ((Fintype.equivFin β).symm j) := by
  simp [eL, reindexLinearEquiv_symm, reindexLinearEquiv_apply, reindex_apply, submatrix_apply]

theorem continuous_eL : Continuous (eL k n β) := by
  refine continuous_pi fun i => continuous_pi fun b => ?_
  simp only [eL_apply]
  exact (continuous_apply _).comp (continuous_apply i)

theorem continuous_eL_symm : Continuous (eL k n β).symm := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [eL_symm_apply]
  exact (continuous_apply _).comp (continuous_apply i)

noncomputable def eH (k : Type) [Field k] [TopologicalSpace k] (n : ℕ) (β : Type) [Fintype β] [DecidableEq β] :
    Matrix (Fin n) (Fin (Fintype.card β)) k ≃ₜ Matrix (Fin n) β k where
  toEquiv := (eL k n β).toEquiv
  continuous_toFun := continuous_eL
  continuous_invFun := continuous_eL_symm

theorem comp_mem_SB' {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : Y ≃ₜ X) {f : X → ℂ}
    (hf : f ∈ GlobalTheory.WeilM.SB X) : (f ∘ e) ∈ GlobalTheory.WeilM.SB Y :=
  ⟨hf.1.comp_continuous e.continuous, hf.2.comp_homeomorph e⟩

end GlobalTheory.SchurHeisReindex


open GlobalTheory.SchurHeisReindex in
theorem GlobalTheory.schur_heisenberg_linearModel_fintype : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
    {β : Type} [Fintype β] [DecidableEq β] {Xt : Type} [AddCommGroup Xt] [Module ℂ Xt] (V : Submodule ℂ Xt)
    (ψ0 : AddChar k ℂ), Continuous ψ0 → ψ0 ≠ 1 →
    ∀ (ι₁ : Xt →ₗ[ℂ] (Matrix (Fin n) β k → ℂ)) (ι₂ : Xt → Matrix (Fin n) β k → ℂ),
    Set.BijOn ι₁ (V : Set Xt) (GlobalTheory.WeilM.SB (Matrix (Fin n) β k) : Set _) →
    (∀ x ∈ V, ∀ y ∈ V, ∀ c : ℂ, ι₂ (c • x + y) = c • ι₂ x + ι₂ y) →
    ∀ (Tr : Matrix (Fin n) β k → Xt → Xt) (Mu : (Matrix (Fin n) β k →ₗ[k] k) → Xt → Xt),
    (∀ C, ∀ x ∈ V, Tr C x ∈ V ∧ ι₁ (Tr C x) = (fun Y => ι₁ x (Y + C)) ∧ ι₂ (Tr C x) = fun Y => ι₂ x (Y + C)) →
    (∀ l, ∀ x ∈ V, Mu l x ∈ V ∧ ι₁ (Mu l x) = (fun Y => ψ0 (l Y) * ι₁ x Y) ∧ ι₂ (Mu l x) = fun Y => ψ0 (l Y) * ι₂ x Y) →
    ∃ c : ℂ, ∀ x ∈ V, ι₂ x = c • ι₁ x := by
  intro k _ _ _ _ n β _ _ Xt _ _ V ψ0 hψc hψ1 ι₁ ι₂ hbij hlin Tr Mu hTr hMu
  set e := eL k n β with he
  let ι₁' : Xt →ₗ[ℂ] (Matrix (Fin n) (Fin (Fintype.card β)) k → ℂ) := LinearMap.funLeft ℂ ℂ e ∘ₗ ι₁
  have hι₁' : ∀ x, ι₁' x = ι₁ x ∘ e := fun x => rfl
  let ι₂' : Xt → Matrix (Fin n) (Fin (Fintype.card β)) k → ℂ := fun x => ι₂ x ∘ e
  have hsurj : Function.Surjective e := e.surjective
  have hbij' : Set.BijOn ι₁' (V : Set Xt) (GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin (Fintype.card β)) k) : Set _) := by
    refine ⟨fun x hx => ?_, fun x hx y hy hxy => ?_, fun f hf => ?_⟩
    · rw [hι₁']
      exact comp_mem_SB' (eH k n β) (hbij.1 hx)
    · apply hbij.2.1 hx hy
      rw [hι₁', hι₁'] at hxy
      funext Z
      obtain ⟨Y, rfl⟩ := hsurj Z
      exact congrFun hxy Y
    · have hf' : f ∘ (eH k n β).symm ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) β k) := comp_mem_SB' (eH k n β).symm hf
      obtain ⟨x, hx, hxf⟩ := hbij.2.2 hf'
      refine ⟨x, hx, ?_⟩
      rw [hι₁', hxf]
      funext Y
      show f ((eH k n β).symm (e Y)) = f Y
      exact congrArg f ((eL k n β).symm_apply_apply Y)
  have hlin' : ∀ x ∈ V, ∀ y ∈ V, ∀ c : ℂ, ι₂' (c • x + y) = c • ι₂' x + ι₂' y := by
    intro x hx y hy c
    funext Y
    simp [ι₂', hlin x hx y hy c]
  have hadd : ∀ Y C, e (Y + C) = e Y + e C := fun Y C => map_add e Y C
  obtain ⟨c, hc⟩ := GlobalTheory.T.eq_smul_of_commute_heisenberg_linearModel_schwartzBruhat V ψ0 hψc hψ1 ι₁' ι₂' hbij' hlin'
    (fun C => Tr (e C)) (fun l => Mu (l ∘ₗ e.symm.toLinearMap))
    (fun C x hx => by
      obtain ⟨h1, h2, h3⟩ := hTr (e C) x hx
      refine ⟨h1, ?_, ?_⟩
      · funext Y; simp [hι₁', h2, hadd]
      · funext Y; simp [ι₂', h3, hadd])
    (fun l x hx => by
      obtain ⟨h1, h2, h3⟩ := hMu (l ∘ₗ e.symm.toLinearMap) x hx
      refine ⟨h1, ?_, ?_⟩
      · funext Y; simp [hι₁', h2]
      · funext Y; simp [ι₂', h3])
  refine ⟨c, fun x hx => ?_⟩
  funext Z
  obtain ⟨Y, rfl⟩ := hsurj Z
  have := congrFun (hc x hx) Y
  simpa [ι₂', hι₁'] using this
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepBijectionSchwartzStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_rep_bijection_schwartz : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
    {β : Type} [Fintype β] [DecidableEq β] {Xt : Type} [AddCommGroup Xt] [Module ℂ Xt] (V : Submodule ℂ Xt)
    (ψ0 : AddChar k ℂ), Continuous ψ0 → ψ0 ≠ 1 →
    ∀ (ι₁ : Xt →ₗ[ℂ] (Matrix (Fin n) β k → ℂ)) (ι₂ : Xt → Matrix (Fin n) β k → ℂ),
    Set.BijOn ι₁ (V : Set Xt) (GlobalTheory.WeilM.SB (Matrix (Fin n) β k) : Set _) →
    (∀ x ∈ V, ∀ y ∈ V, ∀ c : ℂ, ι₂ (c • x + y) = c • ι₂ x + ι₂ y) →
    ∀ (Tr : Matrix (Fin n) β k → Xt → Xt) (Mu : (Matrix (Fin n) β k →ₗ[k] k) → Xt → Xt),
    (∀ C, ∀ x ∈ V, Tr C x ∈ V ∧ ι₁ (Tr C x) = (fun Y => ι₁ x (Y + C)) ∧ ι₂ (Tr C x) = fun Y => ι₂ x (Y + C)) →
    (∀ l, ∀ x ∈ V, Mu l x ∈ V ∧ ι₁ (Mu l x) = (fun Y => ψ0 (l Y) * ι₁ x Y) ∧ ι₂ (Mu l x) = fun Y => ψ0 (l Y) * ι₂ x Y) →
    ∃ c : ℂ, ∀ x ∈ V, ι₂ x = c • ι₁ x := by
  first | exact @GlobalTheory.schur_heisenberg_linearModel_fintype | exact GlobalTheory.schur_heisenberg_linearModel_fintype | (intros; apply GlobalTheory.schur_heisenberg_linearModel_fintype <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleScalingLocalIdentity
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open scoped Matrix
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.DblShape

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem at_hTens {σ : E →ₐ[F] E} {v : Pl (F := F)} {α β : Type} [Fintype α] [Fintype β] (JA : Matrix α α (AE F E))
    (JB : Matrix β β (AE F E)) (x u : Matrix α β (AE F E)) (hx : At (evFin F v) x) :
    At (evFin F v) ((-1 : AE F E) * hTens (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) JA JB x u) := by
  intro r hr
  have h : ∀ i j, r • x i j = 0 := fun i j => by
    have := congrFun (congrFun (hx r hr) i) j
    simpa using this
  rw [← mul_smul_comm]
  unfold hTens
  simp only [Finset.smul_sum, ← smul_mul_assoc, h, zero_mul, Finset.sum_const_zero, mul_zero]

theorem local_intertw {σ : E →ₐ[F] E} {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {JA : Matrix α α (AE F E)} {JB : Matrix β β (AE F E)} {κ : Type} [Fintype κ] {ψ : AddChar (AF F) ℂ}
    (dd : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) JA JB) κ) (omd : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) JB →* Module.End ℂ ((κ → AF F) → ℂ))
    (hS : IsUSplitting (adeleClass F) ψ dd (actB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ)) omd) (v : Pl (F := F)) (p : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) JB)
    (u : Matrix α β (AE F E)) (φ φ₁ φ₂ φ₃ φ₄ : (κ → Fv F v) → ℂ) (hφ : φ ∈ SB (κ → Fv F v))
    (hφ₁ : φ₁ ∈ SB (κ → Fv F v)) (hφ₂ : φ₂ ∈ SB (κ → Fv F v))
    (h1 : Acts (evFin F v) (dd.rho ψ u) φ φ₁) (h2 : Acts (evFin F v) (omd p) φ φ₂)
    (h3 : Acts (evFin F v) (omd p) φ₁ φ₃)
    (h4 : Acts (evFin F v) (dd.rho ψ (u * ((p : GL β (AE F E)) : Matrix β β (AE F E))ᵀ)) φ₂ φ₄) : φ₄ = φ₃ := by
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest κ v
  have hΦ : tens (evFin F v) φ R ∈ GlobalTheory.WeilM.schA F κ := (hR φ hφ).2
  have himpl := hS.impl p u (tens (evFin F v) φ R) hΦ
  have hact : actB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) p u = u * ((p : GL β (AE F E)) : Matrix β β (AE F E))ᵀ := rfl
  rw [hact] at himpl
  have key : tens (evFin F v) φ₄ R = tens (evFin F v) φ₃ R := by
    rw [← h4 R (hR φ₂ hφ₂), ← h2 R (hR φ hφ), ← himpl, h1 R (hR φ hφ), h3 R (hR φ₁ hφ₁)]
  funext t
  have hz : At (evFin F v) (fun i => GlobalTheory.LatVac.liftV v (t i)) := by
    intro u' hu'; funext i; exact GlobalTheory.LatVac.at_liftV v _ u' hu'
  have hRz : R (fun i => GlobalTheory.LatVac.liftV v (t i)) = R 0 := by
    simpa using (hR φ hφ).1 0 _ hz
  have := congrFun key (fun i => GlobalTheory.LatVac.liftV v (t i))
  simp only [tens, GlobalTheory.LatVac.evFin_liftV, hRz] at this
  exact mul_right_cancel₀ hR0 this

end GlobalTheory.DblShape

namespace GlobalTheory.DblShape

open GlobalTheory.DblScal

theorem shape_dbl : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v))
      (dd : GlobalTheory.DblScal.DblCo σ X W) (omd : GlobalTheory.DblScal.DblRep σ (n := n) W),
      IsUSplitting (adeleClass F) B.ψ dd (actB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ)) omd → GlobalTheory.DblScal.LocOps omd v →
      ∀ ιd, GlobalTheory.DblScal.IsLinD B.ψ dd t b c ιd → ∃ cd : GlobalTheory.DblScal.UD σ W.J → ℂ, GlobalTheory.DblScal.IsShapeD omd t c ιd cd := by
  intro hPr F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp v t b c dd omd hS hLoc ι hι
  have hcm : IsCMExt F E σ := hp.base.cm
  have hstd := hp.base.std
  have hψc : Continuous (GlobalTheory.LatVac.psiAt B.ψ v) := GlobalTheory.SchrSB.continuous_psiAt _ hstd.1 v
  have hψ1 : GlobalTheory.LatVac.psiAt B.ψ v ≠ 1 := GlobalTheory.PsiNontriv.psiAt_ne_one _ hstd v
  have hσσ : ∀ x : E, σ (σ x) = x := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
    intro x
    apply w.embedding.injective
    rw [hcm.2.2.2 w.embedding (σ x), hcm.2.2.2 w.embedding x, star_star]
  have hts : (t.comp σ).comp σ = t := AlgHom.ext fun x => by simp [hσσ]
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hdX : X.J.det ≠ 0 := by
    intro h0
    apply GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (hp.herm.sig w)
    have e : (X.J.map (B.emb w).1).det = (B.emb w).1 X.J.det := (RingHom.map_det _ _).symm
    rw [e, h0, map_zero]
  have hdW : W.J.det ≠ 0 := by
    intro h0
    apply GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (hp.skew.sig w)
    have e : (W.J.map (B.emb w).1).det = (B.emb w).1 W.J.det := (RingHom.map_det _ _).symm
    rw [Matrix.det_smul, e, h0, map_zero, mul_zero]
  have hdD : (dbl W.J).det ≠ 0 := by
    rw [dbl, Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg]
    exact mul_ne_zero hdW (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) hdW)
  set D : GL (Fin d ⊕ Fin d) (Fv F v) := dsum c with hD
  set A0 : Matrix (Fin n) (Fin n) (Fv F v) := X.J.map (t.comp σ) with hA0
  set B0 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (Fv F v) := ((dbl W.J).map (t.comp σ))ᵀ with hB0
  set A : Matrix (Fin n) (Fin n) (Fv F v) := A0 * b.1 with hAdef
  set Bm : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (Fv F v) := D.1ᵀ * B0 with hBdef
  have hAu : IsUnit A.det := by
    have e : A0.det = ((t.comp σ : E →ₐ[F] Fv F v) : E →+* Fv F v) X.J.det := (RingHom.map_det _ _).symm
    rw [hAdef, Matrix.det_mul]
    refine IsUnit.mul ?_ (Matrix.isUnits_det_units b)
    rw [e]
    exact isUnit_iff_ne_zero.2 fun h => hdX (RingHom.injective ((t.comp σ : E →ₐ[F] Fv F v) : E →+* Fv F v) (by rw [map_zero]; exact h))
  have hBu : IsUnit Bm.det := by
    have e : ((dbl W.J).map (t.comp σ)).det = ((t.comp σ : E →ₐ[F] Fv F v) : E →+* Fv F v) (dbl W.J).det :=
      (RingHom.map_det _ _).symm
    rw [hBdef, Matrix.det_mul, Matrix.det_transpose, hB0, Matrix.det_transpose]
    refine IsUnit.mul (Matrix.isUnits_det_units D) ?_
    rw [e]
    exact isUnit_iff_ne_zero.2 fun h => hdD (RingHom.injective ((t.comp σ : E →ₐ[F] Fv F v) : E →+* Fv F v) (by rw [map_zero]; exact h))
  choose U hUat hU0 hU1 using fun (P₀ P₁ : Matrix (Fin n) (Fin d ⊕ Fin d) (Fv F v)) => GlobalTheory.T.exists_splitPlace_adelicMatrix_given_components hcm v t P₀ P₁
  let coF : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E) → Matrix (Fin n) (Fin d ⊕ Fin d) (Fv F v) :=
    fun u => (b⁻¹).1 * u.map (piW t) * (D⁻¹).1ᵀ
  have hcc : D.1ᵀ * (D⁻¹).1ᵀ = 1 := by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]
  have hcc' : (D⁻¹).1ᵀ * D.1ᵀ = 1 := by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
  have htr : ∀ u, At (evFin F v) u → u.map (piW (t.comp σ)) = 0 → ∀ φ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v),
      ∀ φ₁ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v), Acts (evFin F v) (dd.rho B.ψ u) φ φ₁ →
      ∀ Y, ι φ₁ Y = ι φ (Y + coF u) :=
    hι.trans
  have hmu : ∀ u, At (evFin F v) u → u.map (piW t) = 0 → ∀ φ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v),
      ∀ φ₁ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v), Acts (evFin F v) (dd.rho B.ψ u) φ φ₁ →
      ∀ x, At (evFin F v) x → x.map (piW (t.comp σ)) = 0 →
        ι φ₁ (coF x) = B.ψ (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J)) x u) * ι φ (coF x) :=
    hι.mult
  let xY : Matrix (Fin n) (Fin d ⊕ Fin d) (Fv F v) → Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E) :=
    fun Y => U (b.1 * Y * D.1ᵀ) 0
  have hcoY : ∀ Y, coF (xY Y) = Y := by
    intro Y
    simp only [coF, xY, hU0, Matrix.mul_assoc, hcc, Matrix.mul_one]
    rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  have hxt : ∀ x, x.map (piW t) = b.1 * coF x * D.1ᵀ := by
    intro x
    simp only [coF, Matrix.mul_assoc, hcc', Matrix.mul_one]
    rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  have hmatW : ∀ p : UD σ W.J, ((p : GL (Fin d ⊕ Fin d) (AE F E)) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)).map (piW t) =
      D.1 * (locMatD t c p).val * (D⁻¹).1 := by
    intro p
    have e : (locMatD t c p).val = (D⁻¹).1 *
        ((p : GL (Fin d ⊕ Fin d) (AE F E)) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)).map (piW t) * D.1 := rfl
    rw [e]
    simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  have hcoH : ∀ (u : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E)) (p : UD σ W.J),
      coF (u * ((p : GL (Fin d ⊕ Fin d) (AE F E)) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E))ᵀ) =
        coF u * (locMatD t c p).valᵀ := by
    intro u p
    simp only [coF]
    rw [Matrix.map_mul, Matrix.transpose_map, hmatW p]
    simp only [Matrix.transpose_mul, Matrix.mul_assoc, hcc, Matrix.mul_one]
  have hsymp : ∀ x u : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E), At (evFin F v) x → x.map (piW (t.comp σ)) = 0 →
      u.map (piW t) = 0 →
      B.ψ (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J)) x u) =
        GlobalTheory.LatVac.psiAt B.ψ v (∑ k, ∑ l, (A0 * x.map (piW t) * B0) k l * u.map (piW (t.comp σ)) k l) := by
    intro x u hx hx0 hu1
    have key := GlobalTheory.T.hermitian_tensor_local_vanish hcm (t.comp σ) X.J W.J hp.herm.herm hp.skew.skew x u hx0 (by rw [hts]; exact hu1)
    rw [hts] at key
    dsimp [cA, incM] at key
    unfold symp
    rw [GlobalTheory.T.adelicTrace_supportedAtSplitPlace hcm v t _ (at_hTens _ _ x u hx)]
    rw [map_mul, map_mul, map_neg, map_neg, map_one, map_one, neg_one_mul, neg_one_mul, ← neg_add, add_comm, key]
    show GlobalTheory.LatVac.psiAt B.ψ v _ = GlobalTheory.LatVac.psiAt B.ψ v _
    congr 1
    simp only [Matrix.neg_apply, neg_mul, Finset.sum_neg_distrib, neg_neg]
    rfl
  let Lm : (Matrix (Fin n) (Fin d ⊕ Fin d) (Fv F v) →ₗ[Fv F v] Fv F v) → Matrix (Fin n) (Fin d ⊕ Fin d) (Fv F v) :=
    fun l => Matrix.of fun k j => l (Matrix.single k j 1)
  let uM : (Matrix (Fin n) (Fin d ⊕ Fin d) (Fv F v) →ₗ[Fv F v] Fv F v) → Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E) :=
    fun l => U 0 ((A⁻¹)ᵀ * Lm l * (Bm⁻¹)ᵀ)
  have hMu : ∀ l x, At (evFin F v) x → x.map (piW (t.comp σ)) = 0 →
      B.ψ (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J)) x (uM l)) = GlobalTheory.LatVac.psiAt B.ψ v (l (coF x)) := by
    intro l x hx hx0
    rw [hsymp x (uM l) hx hx0 (hU0 _ _), hU1, hxt x]
    congr 1
    have e1 : A0 * (b.1 * coF x * D.1ᵀ) * B0 = A * coF x * Bm := by
      simp only [hAdef, hBdef, Matrix.mul_assoc]
    have e2 : Aᵀ * ((A⁻¹)ᵀ * Lm l * (Bm⁻¹)ᵀ) * Bmᵀ = Lm l := by
      have iA : Aᵀ * (A⁻¹)ᵀ = 1 := by rw [← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ hAu, Matrix.transpose_one]
      have iB : (Bm⁻¹)ᵀ * Bmᵀ = 1 := by rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hBu, Matrix.transpose_one]
      simp only [Matrix.mul_assoc]
      rw [iB, Matrix.mul_one, ← Matrix.mul_assoc, iA, Matrix.one_mul]
    rw [e1, GlobalTheory.LinWShape.frob_mul, e2, GlobalTheory.LinWShape.linForm_eq l (coF x)]
    rfl
  have hatR : ∀ (u : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E)) (N : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)),
      At (evFin F v) u → At (evFin F v) (u * N) := by
    intro u N hu r hr
    rw [← Matrix.smul_mul, hu r hr, Matrix.zero_mul]
  have hmain : ∀ p ∈ UDAt σ W.J (evFin F v), ∃ κ : ℂ, ∀ φ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v),
      (fun (Y : Matrix (Fin n) (Fin d ⊕ Fin d) (Fv F v)) => ι (locOp v (omd p) φ) (Y * (locMatD t c p).valᵀ)) = κ • ι φ := by
    intro p hpv
    set P : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E) :=
      ((p : GL (Fin d ⊕ Fin d) (AE F E)) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) with hP
    set Pinv : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E) :=
      (((p⁻¹ : UD σ W.J) : GL (Fin d ⊕ Fin d) (AE F E)) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) with hPi
    have hex : ∀ φ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v),
        ∃ φ₁, φ₁ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v) ∧ Acts (evFin F v) (omd p) φ φ₁ := by
      intro φ hφ
      obtain ⟨φ₁, h1, h2⟩ := hLoc p hpv φ hφ
      exact ⟨φ₁, h1, h2⟩
    have hSacts : ∀ φ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v), Acts (evFin F v) (omd p) φ (locOp v (omd p) φ) :=
      fun φ hφ => acts_locOp (hex φ hφ)
    have hSSB : ∀ φ, locOp v (omd p) φ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v) := fun φ => locOp_mem v _ φ
    have hsb := fun (u : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E)) (φ : (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v) → ℂ)
        (hφ : φ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v)) =>
      GlobalTheory.SchrSB.schr_mem_SB B.ψ hstd.1 v (GlobalTheory.LatVac.locCo dd v u) φ hφ
    have hint : ∀ (u : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E)), At (evFin F v) u →
        ∀ φ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v),
        locOp v (omd p) (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v u) φ) =
          schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v (u * Pᵀ)) (locOp v (omd p) φ) := by
      intro u hu φ hφ
      exact (local_intertw dd omd hS v p u φ _ _ _ _ hφ (hsb u φ hφ) (hSSB φ)
        (GlobalTheory.VacBridge.rho_acts_locCo dd B.ψ v u hu φ) (hSacts φ hφ) (hSacts _ (hsb u φ hφ))
        (GlobalTheory.VacBridge.rho_acts_locCo dd B.ψ v _ (hatR u _ hu) _)).symm
    have hinv2 : Pinvᵀ * Pᵀ = 1 := by
      rw [← Matrix.transpose_mul]
      have : ((p * p⁻¹ : UD σ W.J) : GL (Fin d ⊕ Fin d) (AE F E)).val = P * Pinv := rfl
      rw [← this, mul_inv_cancel]
      exact Matrix.transpose_one
    have hh' : (locMatD t c p).valᵀ * (locMatD t c p⁻¹).valᵀ = 1 := by
      rw [map_inv, ← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]
    have hlin : ∀ x ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v), ∀ y ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v), ∀ a : ℂ,
        (fun (Y : Matrix (Fin n) (Fin d ⊕ Fin d) (Fv F v)) => ι (locOp v (omd p) (a • x + y)) (Y * (locMatD t c p).valᵀ)) =
          a • (fun (Y : Matrix (Fin n) (Fin d ⊕ Fin d) (Fv F v)) => ι (locOp v (omd p) x) (Y * (locMatD t c p).valᵀ)) +
            (fun (Y : Matrix (Fin n) (Fin d ⊕ Fin d) (Fv F v)) => ι (locOp v (omd p) y) (Y * (locMatD t c p).valᵀ)) := by
      intro x hx y hy a
      have e := locOp_lin (omd p).isLinear hex a 1 hx hy
      rw [one_smul, one_smul] at e
      funext Y
      simp only [e, map_add (f := _), map_smul, Pi.add_apply, Pi.smul_apply]
    have htrS : ∀ C, ∀ x ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v),
        schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v (xY C)) x ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v) ∧
        ι (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v (xY C)) x) = (fun Y => ι x (Y + C)) ∧
        (fun (Y : Matrix (Fin n) (Fin d ⊕ Fin d) (Fv F v)) =>
          ι (locOp v (omd p) (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v (xY C)) x)) (Y * (locMatD t c p).valᵀ)) =
          fun (Y : Matrix (Fin n) (Fin d ⊕ Fin d) (Fv F v)) => ι (locOp v (omd p) x) ((Y + C) * (locMatD t c p).valᵀ) := by
      intro C x hx
      have hat := hUat (b.1 * C * D.1ᵀ) 0
      have hat' := hatR _ Pᵀ hat
      have h0' : (xY C * Pᵀ).map (piW (t.comp σ)) = 0 := by
        rw [Matrix.map_mul]; simp only [xY, hU1, Matrix.zero_mul]
      refine ⟨hsb _ x hx, ?_, ?_⟩
      · funext Y
        rw [htr (xY C) hat (hU1 _ _) x hx _ (hsb _ x hx) (GlobalTheory.VacBridge.rho_acts_locCo dd B.ψ v _ hat x) Y, hcoY]
      · funext Y
        rw [hint _ hat x hx, htr _ hat' h0' _ (hSSB x) _ (hsb _ _ (hSSB x))
          (GlobalTheory.VacBridge.rho_acts_locCo dd B.ψ v _ hat' _), hcoH, hcoY, Matrix.add_mul]
    have hmuS : ∀ l, ∀ x ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v),
        schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v (uM l)) x ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v) ∧
        ι (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v (uM l)) x) =
          (fun Y => GlobalTheory.LatVac.psiAt B.ψ v (l Y) * ι x Y) ∧
        (fun (Y : Matrix (Fin n) (Fin d ⊕ Fin d) (Fv F v)) =>
          ι (locOp v (omd p) (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v (uM l)) x)) (Y * (locMatD t c p).valᵀ)) =
          fun (Y : Matrix (Fin n) (Fin d ⊕ Fin d) (Fv F v)) =>
            GlobalTheory.LatVac.psiAt B.ψ v (l Y) * ι (locOp v (omd p) x) (Y * (locMatD t c p).valᵀ) := by
      intro l x hx
      have hat := hUat 0 ((A⁻¹)ᵀ * Lm l * (Bm⁻¹)ᵀ)
      have hat' := hatR _ Pᵀ hat
      have h1' : (uM l * Pᵀ).map (piW t) = 0 := by
        rw [Matrix.map_mul]; simp only [uM, hU0, Matrix.zero_mul]
      refine ⟨hsb _ x hx, ?_, ?_⟩
      · funext Y
        have e := hmu (uM l) hat (hU0 _ _) x hx _ (hsb _ x hx) (GlobalTheory.VacBridge.rho_acts_locCo dd B.ψ v _ hat x)
          (xY Y) (hUat _ _) (hU1 _ _)
        rw [hcoY] at e
        rw [e, hMu l (xY Y) (hUat _ _) (hU1 _ _), hcoY]
      · funext Y
        have hZ := hUat (b.1 * (Y * (locMatD t c p).valᵀ) * D.1ᵀ) 0
        have e := hmu _ hat' h1' _ (hSSB x) _ (hsb _ _ (hSSB x)) (GlobalTheory.VacBridge.rho_acts_locCo dd B.ψ v _ hat' _)
          (xY (Y * (locMatD t c p).valᵀ)) hZ (hU1 _ _)
        rw [hcoY] at e
        rw [hint _ hat x hx, e]
        congr 1
        have hs := GlobalTheory.DblVacEigen.SympAct.symp_actB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : AE F E) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J)) p
          (xY (Y * (locMatD t c p).valᵀ) * Pinvᵀ) (uM l)
        have ea : actB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) p (xY (Y * (locMatD t c p).valᵀ) * Pinvᵀ) = xY (Y * (locMatD t c p).valᵀ) := by
          show xY (Y * (locMatD t c p).valᵀ) * Pinvᵀ * Pᵀ = _
          rw [Matrix.mul_assoc, hinv2, Matrix.mul_one]
        have eb : actB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) p (uM l) = uM l * Pᵀ := rfl
        change symp _ _ _ _ ((xY (Y * (locMatD t c p).valᵀ) * Pinvᵀ) * Pᵀ) (uM l * Pᵀ) = _ at hs
        rw [Matrix.mul_assoc, hinv2, Matrix.mul_one] at hs
        have hx0 : (xY (Y * (locMatD t c p).valᵀ) * Pinvᵀ).map (piW (t.comp σ)) = 0 := by
          rw [Matrix.map_mul]; simp only [xY, hU1, Matrix.zero_mul]
        rw [hs, hMu l _ (hatR _ _ hZ) hx0, hcoH, hcoY, Matrix.mul_assoc, hh', Matrix.mul_one]
    exact GlobalTheory.T.weil_rep_bijection_schwartz (SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v)) (GlobalTheory.LatVac.psiAt B.ψ v) hψc hψ1 ι
      (fun φ Y => ι (locOp v (omd p) φ) (Y * (locMatD t c p).valᵀ)) hι.bij hlin
      (fun C φ => schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v (xY C)) φ)
      (fun l φ => schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v (uM l)) φ) htrS hmuS
  choose! κ hκ using hmain
  refine ⟨κ, fun p hpv φ hφ φ₁ hφ₁ hact => ?_⟩
  have e2 := hκ p hpv φ hφ
  rw [locOp_eq hφ hφ₁ hact] at e2
  funext Y
  have e3 := congrFun e2 (Y * (GlobalTheory.SplitFlip.invT (locMatD t c p)).val)
  simp only [Pi.smul_apply, smul_eq_mul] at e3 ⊢
  rw [GlobalTheory.SplitFlip.invT_val, Matrix.mul_assoc, ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one,
    Matrix.mul_one] at e3
  rw [GlobalTheory.SplitFlip.invT_val]
  exact e3

end GlobalTheory.DblShape
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleScalingLocalIdentityStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.double_scaling_local_identity : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v))
      (dd : GlobalTheory.DblScal.DblCo σ X W) (omd : GlobalTheory.DblScal.DblRep σ (n := n) W),
      IsUSplitting (adeleClass F) B.ψ dd (actB (cA σ)) omd → GlobalTheory.DblScal.LocOps omd v →
      ∀ ιd, GlobalTheory.DblScal.IsLinD B.ψ dd t b c ιd → ∃ cd : GlobalTheory.DblScal.UD σ W.J → ℂ, GlobalTheory.DblScal.IsShapeD omd t c ιd cd := by
  first | exact @GlobalTheory.DblShape.shape_dbl | exact GlobalTheory.DblShape.shape_dbl | (intros; apply GlobalTheory.DblShape.shape_dbl <;> assumption)
end
