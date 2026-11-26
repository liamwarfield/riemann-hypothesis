module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGridCharactersArchExponentsGapGtRank

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeSplitPlaceEqAddComponentParts
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeSplitPlaceEqAddComponentParts
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.SplitPlaceLat

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem tmul_smul_gen {n d : ℕ} (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (a : Fv F v) (o : 𝓞 E) (c : AF F) (x : Fin n → E)
    (y : Fin d → E) :
    ((GlobalTheory.LatVac.liftV v a ⊗ₜ[F] (o : E) : AE F E) • (c • incM F (Matrix.vecMulVec x y))) =
      (GlobalTheory.LatVac.liftV v a * c) • incM F (Matrix.vecMulVec (o • x) y) := by
  ext i j
  simp [incM, inclR, Matrix.vecMulVec_apply, Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.smul_tmul',
    Algebra.smul_def, mul_assoc]

theorem tmul_smul_mem {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) {a : Fv F v}
    (ha : a ∈ v.adicCompletionIntegers F) (o : 𝓞 E) :
    ∀ γ ∈ latAtV X Y v, ((GlobalTheory.LatVac.liftV v a ⊗ₜ[F] (o : E) : AE F E) • γ) ∈ latAtV X Y v := by
  intro γ hγ
  induction hγ using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨c, hc, hci, x, hx, y, hy, rfl⟩ := hz
    rw [tmul_smul_gen]
    refine AddSubgroup.subset_closure ⟨GlobalTheory.LatVac.liftV v a * c, ?_, ?_, o • x, X.L.smul_mem o hx, y, hy, rfl⟩
    · intro u hu
      rw [smul_eq_mul, mul_left_comm, ← smul_eq_mul u c, hc u hu, mul_zero]
    · rw [map_mul, GlobalTheory.LatVac.evFin_liftV]
      exact mul_mem ha hci
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem exists_lift {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))
    {y : Fv F v ⊗[F] E} (hy : y ∈ intLoc F E v) :
    ∃ e : AE F E, compFin F E v e = y ∧ ∀ γ ∈ latAtV X Y v, e • γ ∈ latAtV X Y v := by
  refine intLoc_induction (p := fun y => ∃ e : AE F E, compFin F E v e = y ∧ ∀ γ ∈ latAtV X Y v, e • γ ∈ latAtV X Y v)
    ?_ ?_ ?_ ?_ hy
  · intro a ha o
    refine ⟨GlobalTheory.LatVac.liftV v a ⊗ₜ[F] (o : E), ?_, tmul_smul_mem X Y v ha o⟩
    simp [compFin, GlobalTheory.LatVac.evFin_liftV]
  · exact ⟨0, map_zero _, fun γ _ => by rw [zero_smul]; exact zero_mem _⟩
  · intro y z hy hz
    obtain ⟨e, he, he'⟩ := hy
    obtain ⟨f, hf, hf'⟩ := hz
    exact ⟨e + f, by rw [map_add (f := _), he, hf], fun γ hγ => by rw [add_smul]; exact add_mem (he' γ hγ) (hf' γ hγ)⟩
  · intro y hy
    obtain ⟨e, he, he'⟩ := hy
    exact ⟨-e, by rw [map_neg, he], fun γ hγ => by rw [neg_smul]; exact neg_mem (he' γ hγ)⟩

theorem map_piW_smul {n d : ℕ} {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} (t : E →ₐ[F] Fv F v) (e : AE F E)
    (γ : Matrix (Fin n) (Fin d) (AE F E)) : (e • γ).map (piW t) = piW t e • γ.map (piW t) := by
  ext i j
  simp [Matrix.map_apply, Matrix.smul_apply, map_mul]

end GlobalTheory.SplitPlaceLat

namespace GlobalTheory.SplitPlaceLat

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

theorem latAtV_eq_add_parts : ∀ {D : D7} {a a' : ℕ} (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om')
    (L₁ : Submodule (𝓞 D.host.E) (Fin a' → D.host.E)) (L₂ : Submodule (𝓞 D.host.E) (Fin (a + a') → D.host.E)),
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
      ∃ γA ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
      ∃ γB ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
        γ = γA + γB ∧ γA.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW Bs.τ₁) = 0 ∧
          γB.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (Bs.τ₁.comp D.sp.cm.sig)) = 0 := by
  intro D a a' Bs Γ X om om' hTr L₁ L₂ γ hγ
  have h := hTr.base.cm
  obtain ⟨e, he, he'⟩ := GlobalTheory.SplitPlaceLat.exists_lift {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁
    (splitIdem_mem h Bs.τ₁)
  have p1 : piW Bs.τ₁ e = 1 := by
    change splitProj Bs.τ₁ (compFin _ _ _ e) = 1
    rw [he]; exact splitProj_splitIdem h _
  have p2 : piW (Bs.τ₁.comp D.sp.cm.sig) e = 0 := by
    change splitProj (Bs.τ₁.comp D.sp.cm.sig) (compFin _ _ _ e) = 0
    rw [he]; exact splitProj_comp_splitIdem h _
  refine ⟨γ - e • γ, sub_mem hγ (he' γ hγ), e • γ, he' γ hγ, (sub_add_cancel _ _).symm, ?_, ?_⟩
  · ext i j
    simp [Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, map_sub, map_mul, p1]
  · rw [GlobalTheory.SplitPlaceLat.map_piW_smul, p2, zero_smul]

end GlobalTheory.SplitPlaceLat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeSplitPlaceEqAddComponentPartsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorLatticeSplitPlace_eq_add_componentParts : ∀ {D : D7} {a a' : ℕ} (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om')
    (L₁ : Submodule (𝓞 D.host.E) (Fin a' → D.host.E)) (L₂ : Submodule (𝓞 D.host.E) (Fin (a + a') → D.host.E)),
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
      ∃ γA ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
      ∃ γB ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
        γ = γA + γB ∧ γA.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW Bs.τ₁) = 0 ∧
          γB.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (Bs.τ₁.comp D.sp.cm.sig)) = 0 := by
  first | exact @GlobalTheory.SplitPlaceLat.latAtV_eq_add_parts | exact GlobalTheory.SplitPlaceLat.latAtV_eq_add_parts | (intros; apply GlobalTheory.SplitPlaceLat.latAtV_eq_add_parts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitSupportedOppositeLagrangianCoordinate
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitSupportedOppositeLagrangianCoordinate
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.VacShape

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem det_ne_zero_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  have h1 : (A.submatrix id e.symm)ᵀ * M * (A.submatrix id e.symm).map star =
      (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1)).submatrix e.symm e.symm := by
    rw [← hA]
    ext i j
    simp [Matrix.mul_apply, Matrix.transpose_apply]
  have h2 : ((Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1)).submatrix e.symm e.symm).det ≠ 0 := by
    rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg]
    simp
  intro h0
  apply h2
  rw [← h1, Matrix.det_mul, Matrix.det_mul, h0]
  simp

theorem exists_at_coBar_eq : ∀ {D : D7} {a a' : ℕ} (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om')
    (Y : Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁)),
    ∃ x : Matrix (Fin a') (Fin (a + a')) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E)),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin D.host.F Bs.v₁) x ∧ x.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW Bs.τ₁) = 0 ∧ GlobalTheory.VacShape.coBar Bs Γ x = Y := by
  intro D a a' Bs Γ X om om' hTr Y
  have hcm := hTr.base.cm
  obtain ⟨w⟩ : Nonempty (InfinitePlace D.host.F) := inferInstance
  have hV : Γ.V'.J.det ≠ 0 := by
    intro h0
    apply det_ne_zero_of_hasSig (hTr.geo.hV'.sig w)
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
  have hW : Γ.W.J.det ≠ 0 := by
    intro h0
    apply det_ne_zero_of_hasSig (hTr.geo.hW.sig w)
    rw [Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero, mul_zero]
  have hV1 : IsUnit (Γ.V'.J.map Bs.τ₁).det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    apply hV
    apply (Bs.τ₁ : D.host.E →+* Fv D.host.F Bs.v₁).injective
    rw [map_zero, ← h0]
    exact RingHom.map_det (Bs.τ₁ : D.host.E →+* Fv D.host.F Bs.v₁) Γ.V'.J
  have hW1 : IsUnit ((Γ.W.J.map Bs.τ₁)ᵀ).det := by
    rw [Matrix.det_transpose, isUnit_iff_ne_zero]
    intro h0
    apply hW
    apply (Bs.τ₁ : D.host.E →+* Fv D.host.F Bs.v₁).injective
    rw [map_zero, ← h0]
    exact RingHom.map_det (Bs.τ₁ : D.host.E →+* Fv D.host.F Bs.v₁) Γ.W.J
  set J' := Γ.V'.J.map Bs.τ₁ with hJ'
  set JWt := (Γ.W.J.map Bs.τ₁)ᵀ with hJWt
  let Mx : Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁) := -(J'⁻¹ * Y * JWt⁻¹)
  obtain ⟨e₀, he₀⟩ := GlobalTheory.AdelicU.exists_cm_conj_ne hcm
  set d : Fv D.host.F Bs.v₁ := Bs.τ₁ (D.sp.cm.sig e₀) - Bs.τ₁ e₀ with hd
  have hd0 : d ≠ 0 := sub_ne_zero.2 fun e => he₀ ((Bs.τ₁ : D.host.E →+* Fv D.host.F Bs.v₁).injective e)
  let z : Fv D.host.F Bs.v₁ → AE D.host.F D.host.E := fun t =>
    GlobalTheory.LatVac.liftV Bs.v₁ (-t * Bs.τ₁ e₀ / d) ⊗ₜ[D.host.F] (1 : D.host.E) +
      GlobalTheory.LatVac.liftV Bs.v₁ (t / d) ⊗ₜ[D.host.F] e₀
  have hpi : ∀ (τ : D.host.E →ₐ[D.host.F] Fv D.host.F Bs.v₁) (x : AF D.host.F) (e : D.host.E),
      piW τ (x ⊗ₜ[D.host.F] e) = evFin D.host.F Bs.v₁ x * τ e := fun τ x e => by
    simp only [piW, compFin, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq]
    rfl
  have hz0 : ∀ t, piW Bs.τ₁ (z t) = 0 := fun t => by
    simp only [z, map_add (f := _), hpi, GlobalTheory.LatVac.evFin_liftV, map_one]
    field_simp
    ring
  have hz1 : ∀ t, piW (Bs.τ₁.comp D.sp.cm.sig) (z t) = t := fun t => by
    simp only [z, map_add (f := _), hpi, GlobalTheory.LatVac.evFin_liftV, map_one, AlgHom.comp_apply]
    rw [hd] at hd0 ⊢
    field_simp
    ring
  have hzA : ∀ t, At (evFin D.host.F Bs.v₁) (z t) := fun t u hu => by
    simp only [z, smul_add, TensorProduct.smul_tmul', GlobalTheory.LatVac.at_liftV _ _ u hu, TensorProduct.zero_tmul, add_zero]
  refine ⟨Mx.map z, fun u hu => ?_, ?_, ?_⟩
  · ext i j
    simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.zero_apply]
    exact hzA _ u hu
  · ext i j
    simp only [Matrix.map_apply, Matrix.zero_apply, hz0]
  · unfold coBar
    have hx : (Mx.map z).map (piW (Bs.τ₁.comp D.sp.cm.sig)) = Mx := by
      ext i j
      simp only [Matrix.map_apply, hz1]
    rw [hx]
    simp only [Units.val_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one, Mx]
    rw [← hJWt, Matrix.mul_neg, Matrix.neg_mul, neg_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hV1, Matrix.one_mul, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hW1, Matrix.mul_one]

end GlobalTheory.VacShape
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitSupportedOppositeLagrangianCoordinateStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_splitSupported_oppositeLagrangian_coordinate : ∀ {D : D7} {a a' : ℕ} (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om')
    (Y : Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁)),
    ∃ x : Matrix (Fin a') (Fin (a + a')) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E)),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin D.host.F Bs.v₁) x ∧ x.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW Bs.τ₁) = 0 ∧ GlobalTheory.VacShape.coBar Bs Γ x = Y := by
  first | exact @GlobalTheory.VacShape.exists_at_coBar_eq | exact GlobalTheory.VacShape.exists_at_coBar_eq | (intros; apply GlobalTheory.VacShape.exists_at_coBar_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatInvariantSupportedEqSmulVacuum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.VacUniq

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem schr_schr {K : Type} [CommRing K] [Invertible (2 : K)] (ψ : AddChar K ℂ) {κ : Type} [Fintype κ]
    (w w' : (κ → K) × (κ → K)) (φ : (κ → K) → ℂ) :
    schr ψ w (schr ψ w' φ) = ψ (⅟(2 : K) * (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2)) • schr ψ (w + w') φ := by
  funext x
  have key : (x ⬝ᵥ w.2 + ⅟(2 : K) * (w.1 ⬝ᵥ w.2)) + ((x + w.1) ⬝ᵥ w'.2 + ⅟(2 : K) * (w'.1 ⬝ᵥ w'.2)) =
      ⅟(2 : K) * (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2) +
        (x ⬝ᵥ (w + w').2 + ⅟(2 : K) * ((w + w').1 ⬝ᵥ (w + w').2)) := by
    have h2 : ⅟(2 : K) * 2 = 1 := invOf_mul_self 2
    simp only [Prod.fst_add, Prod.snd_add, dotProduct_add, add_dotProduct]
    linear_combination (-(w.1 ⬝ᵥ w'.2)) * h2
  show ψ _ * (ψ _ * φ (x + w.1 + w'.1)) = ψ _ * (ψ _ * φ (x + (w + w').1))
  rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, key, Prod.fst_add, add_assoc]

theorem acts_unique {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) {κ : Type} [Fintype κ] {φ : (κ → Fv F v) → ℂ}
    {r : (κ → AF F) → ℂ} (hr : Rest (evFin F v) φ r) {x₀ : κ → AF F} (hx₀ : r x₀ ≠ 0)
    (T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ) (φ₁ φ₂ : (κ → Fv F v) → ℂ)
    (h1 : Acts (evFin F v) T φ φ₁) (h2 : Acts (evFin F v) T φ φ₂) : φ₁ = φ₂ := by
  funext y
  set z : κ → AF F := fun i => GlobalTheory.LatVac.liftV v (y i - evFin F v (x₀ i)) with hz
  have hza : At (evFin F v) z := fun u hu => funext fun i => GlobalTheory.LatVac.at_liftV v _ u hu
  have hrx : r (x₀ + z) = r x₀ := hr.1 x₀ z hza
  have hy : (fun i => evFin F v ((x₀ + z) i)) = y := by
    funext i
    simp only [hz, Pi.add_apply, map_add (f := _), GlobalTheory.LatVac.evFin_liftV, add_sub_cancel]
  have e := congrFun ((h1 r hr).symm.trans (h2 r hr)) (x₀ + z)
  simp only [tens] at e
  rw [hrx, hy] at e
  exact mul_right_cancel₀ hx₀ e

theorem phase {V : Type} [AddCommGroup V] [Module ℂ V] {φ ψ S : V} {c χ : ℂ} (hne : φ ≠ 0)
    (h1 : φ = (c * χ) • φ) (h2 : ψ = c • S) : S = χ • ψ := by
  have hcχ : c * χ = 1 := by
    by_contra hne'
    have h4 : (c * χ - 1) • φ = 0 := by rw [sub_smul, ← h1, one_smul, sub_self]
    exact hne ((smul_eq_zero.mp h4).resolve_left (sub_ne_zero.mpr hne'))
  rw [h2, smul_smul, mul_comm, hcχ, one_smul]

theorem sa_bd_uniq : ∀ {D : D7} {a a' : ℕ} (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om') (L₁ : Submodule (𝓞 D.host.E) (Fin a' → D.host.E)) (L₂ : Submodule (𝓞 D.host.E) (Fin (a + a') → D.host.E))
    (θ : 𝓞 D.host.E) (hθ : (θ : D.host.E) + D.sp.cm.sig θ = 1)
    (ι : ((Fin a' × Fin (a + a') → Fv D.host.F Bs.v₁) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁) → ℂ)) (hι : Γ.M'.IsLinBar Bs.ψ Bs.τ₁ 1 1 ι)
    (φ₀ : (Fin a' × Fin (a + a') → Fv D.host.F Bs.v₁) → ℂ) (h0 : φ₀ ∈ GlobalTheory.WeilM.SB _) (hne : φ₀ ≠ 0)
    (hfix : (∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin D.host.F Bs.v₁) (Γ.M'.co.rho Bs.ψ γ) φ₀
            (Bs.ψ (⅟(2 : AF D.host.F) * symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (inclR (F := D.host.F) (AF D.host.F) (θ : D.host.E))
              (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) γ γ) • φ₀)))
    (huniq : ∀ ψ₀ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv D.host.F Bs.v₁), (∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin D.host.F Bs.v₁) (Γ.M'.co.rho Bs.ψ γ) ψ₀
            (Bs.ψ (⅟(2 : AF D.host.F) * symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (inclR (F := D.host.F) (AF D.host.F) (θ : D.host.E))
              (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) γ γ) • ψ₀)) → ∃ c : ℂ, ψ₀ = c • φ₀),
    ∀ g ∈ GlobalTheory.WeilM.SB (Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁)), (∀ s ∈ GlobalTheory.VacShape.Sa Bs Γ L₁ L₂, ∀ Y, g (Y + s) = g Y) →
      (∀ Y ∉ GlobalTheory.VacShape.Bd Bs Γ L₁ L₂, g Y = 0) → ∃ c : ℂ, g = c • ι φ₀ := by
  intro D a a' Bs Γ X om om' hTr L₁ L₂ θ hθ ι hι φ₀ h0 hne hfix huniq g hg hSa hBd
  have hψc : Continuous (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) := GlobalTheory.VacAny.continuous_psiV hTr.base.std.1 Bs.v₁
  have hSB : ∀ γ, ∀ φ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv D.host.F Bs.v₁),
      schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γ) φ ∈ GlobalTheory.WeilM.SB _ :=
    fun γ φ hφ => GlobalTheory.SchrSBFin.schr_mem_SB _ _ hψc _ _ hφ
  have hat : ∀ γ ∈ latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁, At (evFin D.host.F Bs.v₁) γ :=
    (GlobalTheory.LatVac.latAtV_at_stable _ _ _).1
  have hacts : ∀ γ, At (evFin D.host.F Bs.v₁) γ → ∀ φ, Acts (evFin D.host.F Bs.v₁) (Γ.M'.co.rho Bs.ψ γ) φ
      (schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γ) φ) :=
    fun γ hγ φ => GlobalTheory.VacBridge.rho_acts_locCo Γ.M'.co Bs.ψ Bs.v₁ γ hγ φ
  obtain ⟨r, hr, x₀, hx₀⟩ := GlobalTheory.T.exists_nonzero_complementary_adelicSchwartz_function Bs.v₁ φ₀ h0
  obtain ⟨χ, hχ⟩ : ∃ χ : Matrix (Fin a') (Fin (a + a')) (AE D.host.F D.host.E) → ℂ, ∀ γ, χ γ =
      Bs.ψ (⅟(2 : AF D.host.F) * symp (cA D.sp.cm.sig) (inclR (F := D.host.F) (AF D.host.F) (θ : D.host.E))
        (incM D.host.F Γ.V'.J) (incM D.host.F Γ.W.J) γ γ) := ⟨_, fun _ => rfl⟩
  have hφ₀ : ∀ γ ∈ latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
      schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γ) φ₀ = χ γ • φ₀ := by
    intro γ hγ
    rw [hχ]
    exact acts_unique Bs.v₁ hr hx₀ _ _ _ (hacts γ (hat γ hγ) φ₀) (hfix γ hγ)
  have hχ1 : ∀ u, At (evFin D.host.F Bs.v₁) u →
      (u.map (piW Bs.τ₁) = 0 ∨ u.map (piW (Bs.τ₁.comp D.sp.cm.sig)) = 0) → χ u = 1 := by
    intro u hu h
    rw [hχ, GlobalTheory.T.traceSymplectic_self_zero_splitSupported Bs Γ X om om' hTr u hu h, mul_zero, AddChar.map_zero_eq_one]
  obtain ⟨ψ₀, hψ₀, hιψ₀⟩ := hι.bij.surjOn hg
  have hA : ∀ γ ∈ latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁, γ.map (piW Bs.τ₁) = 0 →
      schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γ) ψ₀ = ψ₀ := by
    intro γ hγ h
    refine hι.bij.injOn (hSB γ ψ₀ hψ₀) hψ₀ ?_
    funext Y
    have ht : ι (schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γ) ψ₀) Y =
        ι ψ₀ (Y + GlobalTheory.VacShape.coBar Bs Γ γ) :=
      hι.trans γ (hat γ hγ) h ψ₀ hψ₀ _ (hSB γ ψ₀ hψ₀) (hacts γ (hat γ hγ) ψ₀) Y
    have hs : GlobalTheory.VacShape.coBar Bs Γ γ ∈ GlobalTheory.VacShape.Sa Bs Γ L₁ L₂ := ⟨γ, hγ, h, rfl⟩
    rw [ht, hιψ₀]
    exact hSa _ hs Y
  have hB : ∀ γ ∈ latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
      γ.map (piW (Bs.τ₁.comp D.sp.cm.sig)) = 0 →
      schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γ) ψ₀ = ψ₀ := by
    intro γ hγ h
    refine hι.bij.injOn (hSB γ ψ₀ hψ₀) hψ₀ ?_
    funext Y
    obtain ⟨x, hx, hx0, rfl⟩ := GlobalTheory.T.exists_splitSupported_oppositeLagrangian_coordinate Bs Γ X om om' hTr Y
    have hm : ι (schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γ) ψ₀) (GlobalTheory.VacShape.coBar Bs Γ x) =
        Bs.ψ (symp (cA D.sp.cm.sig) (-1) (incM D.host.F Γ.V'.J) (incM D.host.F Γ.W.J) x γ) *
          ι ψ₀ (GlobalTheory.VacShape.coBar Bs Γ x) :=
      hι.mult γ (hat γ hγ) h ψ₀ hψ₀ _ (hSB γ ψ₀ hψ₀) (hacts γ (hat γ hγ) ψ₀) x hx hx0
    rw [hm, hιψ₀]
    by_cases hY : GlobalTheory.VacShape.coBar Bs Γ x ∈ GlobalTheory.VacShape.Bd Bs Γ L₁ L₂
    · rw [hY x hx hx0 rfl γ hγ h, one_mul]
    · rw [hBd _ hY, mul_zero]
  have hfixψ : ∀ γ ∈ latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
      Acts (evFin D.host.F Bs.v₁) (Γ.M'.co.rho Bs.ψ γ) ψ₀
        (Bs.ψ (⅟(2 : AF D.host.F) * symp (cA D.sp.cm.sig) (inclR (F := D.host.F) (AF D.host.F) (θ : D.host.E))
          (incM D.host.F Γ.V'.J) (incM D.host.F Γ.W.J) γ γ) • ψ₀) := by
    intro γ hγ
    rw [← hχ]
    obtain ⟨γA, hγA, γB, hγB, rfl, hA0, hB0⟩ := GlobalTheory.T.tensorLatticeSplitPlace_eq_add_componentParts Bs Γ X om om' hTr L₁ L₂ γ hγ
    have e0 : GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ (γA + γB) =
        GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γA + GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γB := map_add _ _ _
    have hc := schr_schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γA)
      (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γB)
    have hφA : schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γA) φ₀ = φ₀ := by
      rw [hφ₀ γA hγA, hχ1 γA (hat γA hγA) (Or.inl hA0), one_smul]
    have hφB : schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γB) φ₀ = φ₀ := by
      rw [hφ₀ γB hγB, hχ1 γB (hat γB hγB) (Or.inr hB0), one_smul]
    have h1 := hc φ₀
    rw [hφB, hφA, ← e0, hφ₀ _ hγ, smul_smul] at h1
    have h2 := hc ψ₀
    rw [hB γB hγB hB0, hA γA hγA hA0, ← e0] at h2
    have key := phase hne h1 h2
    have := hacts _ (hat _ hγ) ψ₀
    rwa [key] at this
  obtain ⟨c, hc⟩ := huniq ψ₀ hψ₀ hfixψ
  exact ⟨c, by rw [← hιψ₀, hc, map_smul]⟩

end GlobalTheory.VacUniq

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatInvariantSupportedEqSmulVacuumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhat_invariant_supported_eq_smul_vacuum : ∀ {D : D7} {a a' : ℕ} (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om') (L₁ : Submodule (𝓞 D.host.E) (Fin a' → D.host.E)) (L₂ : Submodule (𝓞 D.host.E) (Fin (a + a') → D.host.E))
    (θ : 𝓞 D.host.E) (hθ : (θ : D.host.E) + D.sp.cm.sig θ = 1)
    (ι : ((Fin a' × Fin (a + a') → Fv D.host.F Bs.v₁) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁) → ℂ)) (hι : Γ.M'.IsLinBar Bs.ψ Bs.τ₁ 1 1 ι)
    (φ₀ : (Fin a' × Fin (a + a') → Fv D.host.F Bs.v₁) → ℂ) (h0 : φ₀ ∈ GlobalTheory.WeilM.SB _) (hne : φ₀ ≠ 0)
    (hfix : (∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin D.host.F Bs.v₁) (Γ.M'.co.rho Bs.ψ γ) φ₀
            (Bs.ψ (⅟(2 : AF D.host.F) * symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (inclR (F := D.host.F) (AF D.host.F) (θ : D.host.E))
              (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) γ γ) • φ₀)))
    (huniq : ∀ ψ₀ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv D.host.F Bs.v₁), (∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin D.host.F Bs.v₁) (Γ.M'.co.rho Bs.ψ γ) ψ₀
            (Bs.ψ (⅟(2 : AF D.host.F) * symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (inclR (F := D.host.F) (AF D.host.F) (θ : D.host.E))
              (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) γ γ) • ψ₀)) → ∃ c : ℂ, ψ₀ = c • φ₀),
    ∀ g ∈ GlobalTheory.WeilM.SB (Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁)), (∀ s ∈ GlobalTheory.VacShape.Sa Bs Γ L₁ L₂, ∀ Y, g (Y + s) = g Y) →
      (∀ Y ∉ GlobalTheory.VacShape.Bd Bs Γ L₁ L₂, g Y = 0) → ∃ c : ℂ, g = c • ι φ₀ := by
  first | exact @GlobalTheory.VacUniq.sa_bd_uniq | exact GlobalTheory.VacUniq.sa_bd_uniq | (intros; apply GlobalTheory.VacUniq.sa_bd_uniq <;> assumption)
end
