module

public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.BrExistsOfRestS
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.MulLatMulLat
public import Formalism.LocalToGlobal.GlobalTheory.ExistsUnitaryOneDetEq

@[expose] public section

section -- merged from Formalism.LocalToGlobal.GlobalTheory.BlockActions.HformSmulRightB
section -- merged from Formalism.LocalToGlobal.GlobalTheory.BlockActions.RestrictionSymmetric
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Matrix MvPolynomial NumberField

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

theorem brTen_blkRowS (Tf : FormsTiedSym D u Ch chOf) (G : D.what₂.Tau → GL (Fin (D.R.N D.R.m - 1)) ℂ)
    (P : MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ) :
    Formalism.L2.Ker.brTen D u (blkRow (fun τ => ((Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ _ _ (Nm_succ D.R) (G τ) : GL (Fin (D.R.N D.R.m)) ℂ) :
              Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) ℂ).transpose) P) =
      blkRow (fun τ => (G τ : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) ℂ).transpose) (Formalism.L2.Ker.brTen D u P) := by
  have hS : ∀ τ, Formalism.L2.Col.Br.SameShift (lamTr D u τ) (sgTr D u τ) :=
    fun τ => Formalism.L2.Ker.sameShiftTr D u τ (interlaceTr D u (sg_interlace Tf.valP) τ)
  rw [blkRow_eq_blk, blkRow_eq_blk]
  unfold Formalism.L2.Ker.brTen
  rw [Formalism.L2.Ker.ta_blk_comp, Formalism.L2.Ker.ta_blk_comp]
  have e : (fun τ => ⇑(Formalism.L2.Ker.brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ) ∘ₗ
      (Formalism.GradedWeylDivisibility.rowAct ℂ (n := D.R.N D.R.m) ((Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ _ _ (Nm_succ D.R) (G τ) : GL (Fin (D.R.N D.R.m)) ℂ) :
        Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) ℂ).transpose).toLinearMap)) =
      fun τ => ⇑((Formalism.GradedWeylDivisibility.rowAct ℂ (n := D.R.N D.R.m - 1) (G τ : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) ℂ).transpose).toLinearMap ∘ₗ
        Formalism.L2.Ker.brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ)) := by
    funext τ f
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply]
    exact brOne_rowAct (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ) (hS τ) (G τ) f
  rw [e]

theorem shift_lamT_sgTS (Tf : FormsTiedSym D u Ch chOf) (τ : D.what₂.Tau) :
    shiftOf (lamT u D.R.m) τ = shiftOf (sgT u) τ := by
  have hS : Formalism.L2.Col.Br.SameShift (lamTr D u τ) (sgTr D u τ) :=
    Formalism.L2.Ker.sameShiftTr D u τ (interlaceTr D u (sg_interlace Tf.valP) τ)
  have hk := D.R.m_add_three_le_k
  have hN : D.R.N D.R.m = D.R.k + D.R.m * (D.R.t + 1) := rfl
  have h1 : 0 < D.R.N D.R.m := by omega
  have h2 : 0 < D.R.N D.R.m - 1 := by omega
  have hS' : (sgTr D u τ).detShift = (lamTr D u τ).detShift := hS
  unfold lamTr sgTr at hS'
  rw [detShift_wSh _ _ h1, detShift_wSh _ _ h2] at hS'
  simp only [shiftOf, lamT, sgT]
  rw [detShift_shW _ _ h1, detShift_shW _ _ h2]
  unfold cTw at hS'
  omega

theorem exP_ofS (Tf : FormsTiedSym D u Ch chOf)
    (B : D.what₂.places.Pl → (D.fm u).clsP → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)
    (hB : ∀ w c, IsUnit (B w c).det) :
    ∀ w, ∀ φ ∈ (D.fm u).Fi D.R.m, ∀ c, ∃ P ∈ Formalism.L2.Forms.CSpan ((D.fm u).lam D.R.m),
    (∀ s, Tf.eWz ((D.mem u).P.evz φ) c s =
      fnOf _ (shiftOf (lamT u D.R.m)) (mZ u Tf.til.z0) P ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY s)) ∧
    ∀ z : (D.mem u).P.Wrow, Tf.valP.eW z c = fnOf _ (shiftOf (sgT u)) 1 (Formalism.L2.Ker.brTen D u P) →
      coPTS Tf B w z c = Formalism.L2.Ker.brTen D u (coMTS Tf B w c (φ ((D.fm u).til c))) := by
  intro w φ hφ c
  obtain ⟨P, hP, hv⟩ := val_repS Tf φ hφ c
  refine ⟨P, hP, hv, fun z hz => ?_⟩
  have hBc := hB w c
  have hU1 := atInf_inv_isUnit _ hBc
  have hbZ := bZ_isUnitS Tf
  have hbZg := bZg_isUnitS Tf (B w c) hBc
  have hU2 := atInf_inv_isUnit _ hbZg

  have hL : coPTS Tf B w z c = (∏ τ, ((1 : D.what₂.Tau → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) ℂ) τ *
      (atInf (Forms.embT D) (B w c)⁻¹ τ)⁻¹).det ^ shiftOf (sgT u) τ) •
      blkRow (fun τ => (1 : D.what₂.Tau → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) ℂ) τ *
        (atInf (Forms.embT D) (B w c)⁻¹ τ)⁻¹) (Formalism.L2.Ker.brTen D u P) := by
    have e1 : coPTS Tf B w z c = fnInv (gramC (gramP D) (Forms.embT D)) (shiftOf (sgT u)) (atInf (Forms.embT D) (B w c)⁻¹) (Tf.valP.eW z c) := rfl
    rw [e1, hz, fnOf_change _ _ (atInf (Forms.embT D) (B w c)⁻¹) 1 hU1, fnInv_fnOf _ _ _ hU1]

  have hM : trEvS Tf c (φ ((D.fm u).til c)) = fnOf _ (shiftOf (lamT u D.R.m)) (mZ u Tf.til.z0) P := by
    funext y
    rw [trEv_eqS, hv, Equiv.apply_symm_apply]
  have hR : coMTS Tf B w c (φ ((D.fm u).til c)) = (∏ τ, (atInf (Forms.embT D) (bZ u Tf.til.z0)⁻¹ τ *
      (atInf (Forms.embT D) (bZg u Tf.til.z0 (B w c))⁻¹ τ)⁻¹).det ^ shiftOf (lamT u D.R.m) τ) •
      blkRow (fun τ => atInf (Forms.embT D) (bZ u Tf.til.z0)⁻¹ τ * (atInf (Forms.embT D) (bZg u Tf.til.z0 (B w c))⁻¹ τ)⁻¹) P := by
    change fnInv (gramC (gramN D D.R.m _) (Forms.embT D)) (shiftOf (lamT u D.R.m)) (atInf (Forms.embT D) (bZg u Tf.til.z0 (B w c))⁻¹) (trEvS Tf c (φ ((D.fm u).til c))) = _
    rw [hM, mZ, fnOf_change _ _ (atInf (Forms.embT D) (bZg u Tf.til.z0 (B w c))⁻¹) (atInf (Forms.embT D) (bZ u Tf.til.z0)⁻¹) hU2,
      fnInv_fnOf _ _ _ hU2]
  have hKm : (fun τ => atInf (Forms.embT D) (bZ u Tf.til.z0)⁻¹ τ * (atInf (Forms.embT D) (bZg u Tf.til.z0 (B w c))⁻¹ τ)⁻¹) =
      fun τ => ((Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ _ _ (Nm_succ D.R) (glT (B w c) hBc τ) : GL (Fin (D.R.N D.R.m)) ℂ) : Matrix _ _ ℂ).transpose := by
    funext τ
    rw [embGL_glT, atInf_inv_inv _ hbZg, bZg_eq_mul]
    show (bZ u Tf.til.z0)⁻¹.map (Forms.embT D τ) * (bZ u Tf.til.z0 * dgE (B w c)).map (Forms.embT D τ) = _
    rw [← Matrix.map_mul, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hbZ, Matrix.one_mul]
  have hKp : (fun τ => (1 : D.what₂.Tau → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) ℂ) τ *
      (atInf (Forms.embT D) (B w c)⁻¹ τ)⁻¹) = fun τ => ((glT (B w c) hBc τ : GL (Fin (D.R.N D.R.m - 1)) ℂ) : Matrix _ _ ℂ).transpose := by
    funext τ
    rw [glT_val, Matrix.transpose_transpose, Pi.one_apply, Matrix.one_mul, atInf_inv_inv _ hBc]
    rfl
  rw [hL, hR, hKm, hKp, map_smul, brTen_blkRowS Tf]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  have h1 := congrFun hKm τ
  have h2 := congrFun hKp τ
  rw [h1, h2, shift_lamT_sgTS Tf τ, embGL_glT, glT_val, Matrix.det_transpose]
  unfold dgE
  rw [Matrix.reindex_apply, ← Matrix.submatrix_map, Matrix.det_submatrix_equiv_self, Matrix.fromBlocks_map,
    Matrix.map_zero _ (map_zero _), Matrix.map_zero _ (map_zero _), Matrix.map_one _ (map_zero _) (map_one _),
    Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one, Matrix.det_transpose]

structure RestrictionSymmetric (Tf : FormsTiedSym D u Ch chOf)
    (B : D.what₂.places.Pl → (D.fm u).clsP → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)
    (gP : D.what₂.places.Pl → (D.fm u).clsP → D.what₂.Tau → GL (Fin (D.R.N D.R.m - 1)) ℂ) : Prop where
  lat_co : ∀ w, ∀ x ∈ (D.fm u).S D.R.m w, ∀ c,
    coMTS Tf B w c ((D.fm u).emb D.R.m x ((D.fm u).til c)) ∈ Formalism.MainNotions.product_first_zeroth_parts.IntSpan D w ((D.fm u).lam D.R.m)
  pt_co : ∀ w, ∀ z ∈ (D.fm u).ptC, (∃ y ∈ (D.fm u).SP w, (D.fm u).ptEmb y = z) ↔
    ∀ c, coPTS Tf B w z c ∈ Formalism.MainNotions.product_first_zeroth_parts.IntSpan D w (D.fm u).sg
  ipV_co : ∀ w c, ∀ φ ∈ (D.fm u).Fi D.R.m,
    ((D.fm u).ipV D.R.m ((D.fm u).til c) (φ ((D.fm u).til c)) (φ ((D.fm u).til c))).re =
    (Formalism.MainNotions.product_first_zeroth_parts.nfAll ((D.fm u).lam D.R.m)
      (blk (fun τ => sqAct ℂ _ (lamTr D u τ) (gFull D u (gP w c τ))) (coMTS Tf B w c (φ ((D.fm u).til c))))
      (blk (fun τ => sqAct ℂ _ (lamTr D u τ) (gFull D u (gP w c τ))) (coMTS Tf B w c (φ ((D.fm u).til c))))).re
  re_petersson_self_eq_sum_coord : ∀ w, ∀ z ∈ (D.fm u).ptC, ((D.fm u).ipP z z).re = ∑ c, ((Nat.card ((D.fm u).stabilizer₂ c) : ℝ))⁻¹ *
    (Formalism.MainNotions.product_first_zeroth_parts.nfAll (D.fm u).sg (blk (fun τ => sqAct ℂ _ (sgTr D u τ) (gP w c τ)) (coPTS Tf B w z c))
      (blk (fun τ => sqAct ℂ _ (sgTr D u τ) (gP w c τ)) (coPTS Tf B w z c))).re

theorem pendRest_ofS (Tf : FormsTiedSym D u Ch chOf)
    (B : D.what₂.places.Pl → (D.fm u).clsP → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)
    (hB : ∀ w c, IsUnit (B w c).det)
    (gP : D.what₂.places.Pl → (D.fm u).clsP → D.what₂.Tau → GL (Fin (D.R.N D.R.m - 1)) ℂ) (h : RestrictionSymmetric Tf B gP) :
    PendRestS Tf B gP :=
  ⟨exP_ofS Tf B hB, h.lat_co, h.pt_co, h.ipV_co, h.re_petersson_self_eq_sum_coord⟩

theorem brExists_of_rest4S (Tf : FormsTiedSym D u Ch chOf) (hL : LowerSymmetricCompatible Tf)
    (B : D.what₂.places.Pl → (D.fm u).clsP → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)
    (hB : ∀ w c, IsUnit (B w c).det)
    (gP : D.what₂.places.Pl → (D.fm u).clsP → D.what₂.Tau → GL (Fin (D.R.N D.R.m - 1)) ℂ) (h : RestrictionSymmetric Tf B gP) :
    ∃ P : Pend D u, ArchimedeanSignatureMatching P :=
  brExists_of_restS Tf B hB hL gP (pendRest_ofS Tf B hB gP h)

theorem weightedInner_self_eq_sum_coords_of_orthonormal' (Tf : FormsTiedSym D u Ch chOf)
    (B : D.what₂.places.Pl → (D.fm u).clsP → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)
    (hB : ∀ w c, IsUnit (B w c).det) (o : FrP D) (ho : o.IsON) :
    ∀ w, ∀ z ∈ (D.fm u).ptC, ((D.fm u).ipP z z).re = ∑ c, ((Nat.card ((D.fm u).stabilizer₂ c) : ℝ))⁻¹ *
      (Formalism.MainNotions.product_first_zeroth_parts.nfAll (D.fm u).sg (blk (fun τ => sqAct ℂ _ (sgTr D u τ) (gPof B hB o w c τ)) (coPTS Tf B w z c))
        (blk (fun τ => sqAct ℂ _ (sgTr D u τ) (gPof B hB o w c τ)) (coPTS Tf B w z c))).re := by
  classical
  intro w z hz
  have hQ : ∀ c, blk (fun τ => sqAct ℂ _ (sgTr D u τ) (gPof B hB o w c τ)) (coPTS Tf B w z c) ∈ Formalism.L2.Forms.CSpan (D.fm u).sg := by
    intro c
    have h0 := coP_mem_of_isUnit_det' Tf B hB w z hz c
    rw [← cspan_sgTr] at h0
    have h1 := Formalism.L2.Ker.lc_blk_sqAct_mem _ (gPof B hB o w c) _ h0
    rw [cspan_sgTr] at h1
    exact h1
  have hE : ∀ c, Tf.valP.eW z c = fnOf _ (shiftOf (sgT u)) (fun τ => (o.1 τ)⁻¹)
      (blk (fun τ => sqAct ℂ _ (sgTr D u τ) (gPof B hB o w c τ)) (coPTS Tf B w z c)) := by
    intro c
    obtain ⟨Q, _, hq⟩ := eW_repS Tf (B w c) (hB w c) z hz c
    have hc : coPTS Tf B w z c = Q := by
      change fnInv _ _ _ (Tf.valP.eW z c) = Q
      rw [hq]
      exact fnInv_fnOf _ _ _ (atInf_inv_isUnit _ (hB w c)) Q
    have hs : shiftOf (sgT u) = fun τ => (sgTr D u τ).detShift := funext fun τ => (shift_sgTr τ).symm
    rw [hc, hq, hs, fnOf_sqAct _ (sgTr D u) (atInf (embT D) (B w c)⁻¹) o.1 o.2 _ (fun τ => rfl)]
  rw [Tf.valP.ipP o ho z z _ _ hQ hQ hE hE, Complex.re_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [show ((Nat.card ((D.fm u).stabilizer₂ c) : ℕ) : ℂ)⁻¹ = (((Nat.card ((D.fm u).stabilizer₂ c) : ℝ))⁻¹ : ℝ) by push_cast; rfl,
    Complex.re_ofReal_mul]
  rfl

end Formalism.L2.GlobalTheoryTheory.Br
end
end

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Matrix Formalism.UG

section Gen

variable {A : Type} [CommRing A]

theorem hform_reindexB {m n : Type} [Fintype m] [Fintype n] (σ : A →+* A) (e : m ≃ n) (J : Matrix m m A) (x y : m → A) :
    hform σ (J.reindex e e) (x ∘ e.symm) (y ∘ e.symm) = hform σ J x y := by
  unfold hform
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Function.comp_apply]
  rw [← e.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← e.sum_comp]
  simp only [Equiv.symm_apply_apply]

theorem hform_smul_leftB {n : Type} [Fintype n] (σ : A →+* A) (J : Matrix n n A) (s : A) (x y : n → A) :
    hform σ J (s • x) y = σ s * hform σ J x y := by
  unfold hform
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hform_smul_rightB {n : Type} [Fintype n] (σ : A →+* A) (J : Matrix n n A) (s : A) (x y : n → A) :
    hform σ J x (s • y) = s * hform σ J x y := by
  unfold hform
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem gramOf_apply {m n : Type} [Fintype m] [Fintype n] (σ : A →+* A) (M : Matrix m n A) (J : Matrix m m A) (a b : n) :
    ((M.map σ)ᵀ * J * M) a b = hform σ J (fun k => M k a) (fun k => M k b) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, hform, Finset.sum_mul]
  rw [Finset.sum_comm]

end Gen

variable (D : D7)

abbrev crdM : (D.sp.X D.R.m).V ≃ₗ[D.host.E] (Fin (D.R.N D.R.m) → D.host.E) :=
  letI := D.host.cmStar
  (D.sp.X D.R.m).frame.equivFun.trans
    (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankN D D.R.m le_rfl)).symm)

abbrev crdP : D.sp.X'.V ≃ₗ[D.host.E] (Fin (D.R.N D.R.m - 1) → D.host.E) :=
  letI := D.host.cmStar
  D.sp.X'.frame.equivFun.trans (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankP D)).symm)

theorem hform_frame (S : @HSpace D.host.E _ _ D.host.cmStar) (v w : S.V) :
    hform (sigD D : D.host.E →+* D.host.E) S.gram (S.frame.equivFun v) (S.frame.equivFun w) = S.hT v w := by
  letI := D.host.cmStar
  rw [Formalism.L2.GlobalTheoryTheory.TraceIntegrality.hT_expand]
  unfold hform
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Module.Basis.equivFun_apply, Module.Basis.equivFun_apply, mul_assoc]
  rfl

theorem hform_crdM (v w : (D.sp.X D.R.m).V) :
    hform (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl) (crdM D v) (crdM D w) = (D.sp.X D.R.m).hT v w := by
  letI := D.host.cmStar
  have e : ∀ x, crdM D x = (D.sp.X D.R.m).frame.equivFun x ∘ (finCongr (rankN D D.R.m le_rfl)).symm := fun x => rfl
  rw [e, e]
  unfold gramN
  rw [hform_reindexB, hform_frame]

theorem hform_crdP (v w : D.sp.X'.V) :
    hform (sigD D : D.host.E →+* D.host.E) (gramP D) (crdP D v) (crdP D w) = D.sp.X'.hT v w := by
  letI := D.host.cmStar
  have e : ∀ x, crdP D x = D.sp.X'.frame.equivFun x ∘ (finCongr (rankP D)).symm := fun x => rfl
  rw [e, e]
  unfold gramP
  rw [hform_reindexB, hform_frame]

theorem iXc_eq (x : Fin (D.R.N D.R.m - 1) → D.host.E) : iXc D x = crdM D (D.sp.iX' ((crdP D).symm x)) := rfl

theorem zc_eq : zc D = crdM D D.sp.z := rfl

theorem hform_iXc (x y : Fin (D.R.N D.R.m - 1) → D.host.E) :
    hform (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl) (iXc D x) (iXc D y) =
      hform (sigD D : D.host.E →+* D.host.E) (gramP D) x y := by
  letI := D.host.cmStar
  rw [iXc_eq, iXc_eq, hform_crdM, D.sp.iX'_isom, ← hform_crdP, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

theorem hform_iXc_zc (x : Fin (D.R.N D.R.m - 1) → D.host.E) :
    hform (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl) (iXc D x) (zc D) = 0 := by
  letI := D.host.cmStar
  rw [iXc_eq, zc_eq, hform_crdM]
  exact D.sp.z_orth _

theorem hform_zc_iXc (x : Fin (D.R.N D.R.m - 1) → D.host.E) :
    hform (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl) (zc D) (iXc D x) = 0 := by
  letI := D.host.cmStar
  rw [iXc_eq, zc_eq, hform_crdM, ← (D.sp.X D.R.m).herm.eq (D.sp.iX' _) D.sp.z, D.sp.z_orth, map_zero]

variable {D}

theorem gram_bZ {u : D.what₂.Word} (z0 : Fin (D.R.N D.R.m) → D.host.E) (hz : ∃ a : D.host.E, z0 = a • zc D)
    (hn : hform (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl) z0 z0 = ((D.mem u).A.T : D.host.E)) :
    ((bZ u z0).map (sigD D : D.host.E →+* D.host.E))ᵀ * gramN D D.R.m le_rfl * bZ u z0 =
      Matrix.reindex (finSumFinEquiv.trans (finCongr (Nm_succ D.R))) (finSumFinEquiv.trans (finCongr (Nm_succ D.R)))
        (Matrix.fromBlocks (gramP D) 0 0 (Matrix.of fun _ _ => ((D.mem u).A.T : D.host.E)⁻¹)) := by
  obtain ⟨a, rfl⟩ := hz
  have hT : ((D.mem u).A.T : D.host.E) ≠ 0 := Nat.cast_ne_zero.mpr (D.mem u).A.T_prime.ne_zero
  have hcol1 : ∀ i : Fin (D.R.N D.R.m - 1),
      (fun k => bZ u (a • zc D) k ((finSumFinEquiv.trans (finCongr (Nm_succ D.R))) (Sum.inl i))) = iXc D (Pi.single i 1) := by
    intro i
    funext k
    have hi : (((finSumFinEquiv.trans (finCongr (Nm_succ D.R))) (Sum.inl i) : Fin (D.R.N D.R.m)) : ℕ) < D.R.N D.R.m - 1 := by
      simp
    have hi' : (⟨_, hi⟩ : Fin (D.R.N D.R.m - 1)) = i := Fin.ext (by simp)
    simp only [bZ, dite_eq_left hi, hi', iXm, LinearMap.toMatrix'_apply]
  have hcol2 : ∀ j : Fin 1,
      (fun k => bZ u (a • zc D) k ((finSumFinEquiv.trans (finCongr (Nm_succ D.R))) (Sum.inr j))) =
        (a / ((D.mem u).A.T : D.host.E)) • zc D := by
    intro j
    funext k
    have hj : ¬ (((finSumFinEquiv.trans (finCongr (Nm_succ D.R))) (Sum.inr j) : Fin (D.R.N D.R.m)) : ℕ) < D.R.N D.R.m - 1 := by
      simp
    simp only [bZ, dite_eq_right hj, Pi.smul_apply, smul_eq_mul]
    ring
  ext x y
  obtain ⟨p, rfl⟩ := (finSumFinEquiv.trans (finCongr (Nm_succ D.R))).surjective x
  obtain ⟨q, rfl⟩ := (finSumFinEquiv.trans (finCongr (Nm_succ D.R))).surjective y
  rw [gramOf_apply, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rcases p with i | i <;> rcases q with j | j
  · rw [hcol1, hcol1, hform_iXc, Matrix.fromBlocks_apply₁₁]
    simp [hform, Pi.single_apply]
  · rw [hcol1, hcol2, hform_smul_rightB, hform_iXc_zc, mul_zero, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]
  · rw [hcol2, hcol1, hform_smul_leftB, hform_zc_iXc, mul_zero, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
  · have ha : hform (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl) (a • zc D) (a • zc D) =
        (sigD D : D.host.E →+* D.host.E) a * (a * hform (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl) (zc D) (zc D)) := by
      rw [hform_smul_leftB, hform_smul_rightB]
    rw [hcol2, hcol2, hform_smul_leftB, hform_smul_rightB, Matrix.fromBlocks_apply₂₂, Matrix.of_apply, map_div₀, map_natCast]
    rw [ha] at hn
    rw [show (sigD D : D.host.E →+* D.host.E) a / ((D.mem u).A.T : D.host.E) * (a / ((D.mem u).A.T : D.host.E) *
      hform (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl) (zc D) (zc D)) =
      ((sigD D : D.host.E →+* D.host.E) a * (a * hform (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl) (zc D) (zc D))) /
        (((D.mem u).A.T : D.host.E) * ((D.mem u).A.T : D.host.E)) by ring, hn]
    field_simp

end Formalism.L2.GlobalTheoryTheory.Br
end
end

section -- merged from Formalism.LocalToGlobal.GlobalTheory.BlockActions.ExistsOnOfPosDef
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Matrix Formalism.UG
open scoped ComplexOrder

theorem exists_on_of_posDef {k : ℕ} (H : Matrix (Fin k) (Fin k) ℂ) (hH : H.PosDef) :
    ∃ o : Matrix (Fin k) (Fin k) ℂ, IsUnit o.det ∧ oᴴ * H * o = 1 := by
  classical
  set U : Matrix (Fin k) (Fin k) ℂ := (hH.1.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ) with hUdef
  have hUU : star U * U = 1 := Unitary.star_mul_self_of_mem (hH.1.eigenvectorUnitary).2
  have hd : star U * H * U = diagonal (RCLike.ofReal ∘ hH.1.eigenvalues) := by
    have h := hH.1.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_star_apply] at h
    simpa [hUdef] using h
  let d : Fin k → ℂ := fun i => (((Real.sqrt (hH.1.eigenvalues i))⁻¹ : ℝ) : ℂ)
  have hpos : ∀ i, 0 < hH.1.eigenvalues i := fun i => hH.eigenvalues_pos i
  refine ⟨U * diagonal d, ?_, ?_⟩
  · rw [Matrix.det_mul, Matrix.det_diagonal]
    refine IsUnit.mul ?_ (IsUnit.mk0 _ (Finset.prod_ne_zero_iff.mpr fun i _ => ?_))
    · have h1 : U.det * (star U).det = 1 := by
        rw [← Matrix.det_mul, Unitary.mul_star_self_of_mem (hH.1.eigenvectorUnitary).2, Matrix.det_one]
      exact ⟨Units.mkOfMulEqOne _ _ h1, rfl⟩
    · simp only [d, ne_eq, Complex.ofReal_eq_zero, inv_eq_zero]
      exact (Real.sqrt_pos.mpr (hpos i)).ne'
  · rw [Matrix.conjTranspose_mul, Matrix.diagonal_conjTranspose, ← Matrix.star_eq_conjTranspose]
    have e : diagonal (star d) * star U * H * (U * diagonal d) = diagonal (star d) * (star U * H * U) * diagonal d := by
      simp only [Matrix.mul_assoc]
    rw [e, hd, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    have hs : Real.sqrt (hH.1.eigenvalues i) ≠ 0 := (Real.sqrt_pos.mpr (hpos i)).ne'
    have hr : (Real.sqrt (hH.1.eigenvalues i))⁻¹ * hH.1.eigenvalues i * (Real.sqrt (hH.1.eigenvalues i))⁻¹ = 1 := by
      rw [mul_comm ((Real.sqrt (hH.1.eigenvalues i))⁻¹) (hH.1.eigenvalues i), mul_assoc, ← mul_inv,
        Real.mul_self_sqrt (hpos i).le, mul_inv_cancel₀ (hpos i).ne']
    have h2 : (((Real.sqrt (hH.1.eigenvalues i))⁻¹ : ℝ) : ℂ) * ((hH.1.eigenvalues i : ℝ) : ℂ) *
        (((Real.sqrt (hH.1.eigenvalues i))⁻¹ : ℝ) : ℂ) = 1 := by exact_mod_cast hr
    simp only [d, Pi.star_apply, Function.comp_apply, Complex.star_def, Complex.conj_ofReal]
    exact h2

variable {D : D7}

theorem embT_sig (τ : D.what₂.Tau) (x : D.host.E) : embT D τ (sigD D x) = starRingEnd ℂ (embT D τ x) :=
  D.sp.cm.cmUnram.2.1 (embT D τ) x

theorem map_cT {m n : Type} (M : Matrix m n D.host.E) (τ : D.what₂.Tau) :
    ((M.map (sigD D : D.host.E →+* D.host.E))ᵀ).map (embT D τ) = (M.map (embT D τ))ᴴ := by
  ext i j
  simp only [Matrix.map_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply, RingHom.coe_coe]
  rw [embT_sig]
  rfl


variable (D) in
theorem gramP_eq : gramP D = ((iXm D).map (sigD D : D.host.E →+* D.host.E))ᵀ * gramN D D.R.m le_rfl * iXm D := by
  ext a b
  rw [gramOf_apply]
  have hc : ∀ i : Fin (D.R.N D.R.m - 1), (fun k => iXm D k i) = iXc D (Pi.single i 1) := by
    intro i; funext k; simp only [iXm, LinearMap.toMatrix'_apply]
  rw [hc, hc, hform_iXc]
  simp [hform, Pi.single_apply]


variable (D) in
theorem iXm_leftInv : ∃ L : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m)) D.host.E, L * iXm D = 1 := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (iXc D) (LinearMap.ker_eq_bot.mpr (iXc_injective D))
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  rw [iXm, ← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]

theorem gramP_posDef {Ch : ℕ → Type} {u : D.what₂.Word} {chOf : ∀ i, (D.mem u).C.cls i → Ch i} (Tf : FormsTiedSym D u Ch chOf)
    (τ : D.what₂.Tau) : (gramC (gramP D) (embT D) τ).PosDef := by
  obtain ⟨C, hC, -, -⟩ := (Tf.val D.R.m le_rfl (Or.inr rfl)).de
  have hC' : ((C.1.map (sigD D : D.host.E →+* D.host.E))ᵀ * C.1) = gramN D D.R.m le_rfl := hC
  obtain ⟨L, hL⟩ := iXm_leftInv D
  set A : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m - 1)) ℂ := (C.1 * iXm D).map (embT D τ) with hA
  have hG : gramC (gramP D) (embT D) τ = Aᴴ * A := by
    have e1 : ((iXm D).map (sigD D : D.host.E →+* D.host.E))ᵀ * (((C.1).map (sigD D : D.host.E →+* D.host.E))ᵀ * C.1) * iXm D =
        ((C.1 * iXm D).map (sigD D : D.host.E →+* D.host.E))ᵀ * (C.1 * iXm D) := by
      rw [Matrix.map_mul, Matrix.transpose_mul]
      simp only [Matrix.mul_assoc]
    simp only [gramC]
    rw [gramP_eq, ← hC', e1, Matrix.map_mul, map_cT, hA]
  have hinj : Function.Injective A.mulVec := by
    intro x y hxy
    have hCi : IsUnit C.1.det := (Matrix.isUnit_iff_isUnit_det _).mp C.isUnit
    have h1 : ((L * C.1⁻¹) * (C.1 * iXm D)).map (embT D τ) = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc C.1⁻¹, Matrix.nonsing_inv_mul _ hCi, Matrix.one_mul, hL,
        Matrix.map_one _ (map_zero _) (map_one _)]
    have h2 := congrArg (fun v => ((L * C.1⁻¹).map (embT D τ)) *ᵥ v) hxy
    simp only [Matrix.mulVec_mulVec, hA, ← Matrix.map_mul, h1, Matrix.one_mulVec] at h2
    exact h2
  rw [hG]
  exact Matrix.PosDef.conjTranspose_mul_self A hinj

theorem exists_onP {Ch : ℕ → Type} {u : D.what₂.Word} {chOf : ∀ i, (D.mem u).C.cls i → Ch i} (Tf : FormsTiedSym D u Ch chOf) :
    ∃ o : FrP D, ∀ τ, (o.1 τ)ᴴ * gramC (gramP D) (embT D) τ * o.1 τ = 1 := by
  have h := fun τ => exists_on_of_posDef (k := D.R.N D.R.m - 1) (gramC (gramP D) (embT D) τ) (gramP_posDef Tf τ)
  choose o ho1 ho2 using h
  exact ⟨⟨o, ho1⟩, ho2⟩

end Formalism.L2.GlobalTheoryTheory.Br
end
end

section -- merged from Formalism.LocalToGlobal.GlobalTheory.BlockActions.DefNOfFact
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.L2.Forms NumberField Formalism.UG Matrix

theorem span_of_cols {E : Type} [Field E] {N n : ℕ} (hN : n + 1 = N) (A : Matrix (Fin N) (Fin n) E) (z : Fin N → E)
    (hA : Function.Injective A.mulVec) (hz : ∀ x, A *ᵥ x ≠ z) :
    ∀ y, ∃ (x : Fin n → E) (s : E), y = A *ᵥ x + s • z := by
  subst hN
  intro y
  have hB := isUnit_det_cols rfl A z hA hz
  set B : Matrix (Fin (n + 1)) (Fin (n + 1)) E :=
    Matrix.of (fun a (b : Fin (n + 1)) => if hb : (b : ℕ) < n then A a ⟨b, hb⟩ else z a) with hBdef
  set w := B⁻¹ *ᵥ y with hw
  have hy : B *ᵥ w = y := by rw [hw, mulVec_mulVec, mul_nonsing_inv _ hB, one_mulVec]
  refine ⟨fun i => w (Fin.castSucc i), w (Fin.last n), ?_⟩
  rw [← hy]
  funext a
  simp only [hBdef, mulVec, dotProduct, Fin.sum_univ_castSucc, Pi.add_apply, Pi.smul_apply, smul_eq_mul, of_apply,
    Fin.val_castSucc, Fin.is_lt, dif_pos, Fin.val_last, lt_irrefl, dif_neg, not_false_eq_true, Fin.eta]
  ring

variable (D : D7)

theorem conj_sigD (φ : D.host.E →+* ℂ) (x : D.host.E) :
    φ ((sigD D : D.host.E →+* D.host.E) x) = (starRingEnd ℂ) (φ x) := by
  letI := D.host.cmStar
  exact D.sp.cm.cmUnram.2.1 φ x

theorem zc_not_range (x : Fin (D.R.N D.R.m - 1) → D.host.E) : iXm D *ᵥ x ≠ zc D := by
  letI := D.host.cmStar
  intro h
  have h1 := hform_iXc_zc D x
  simp only [iXm, LinearMap.toMatrix'_mulVec] at h
  rw [h, zc_eq, hform_crdM] at h1
  exact D.sp.z_anis h1

theorem span_iXc_zc : ∀ y, ∃ (x : Fin (D.R.N D.R.m - 1) → D.host.E) (s : D.host.E), y = iXc D x + s • zc D := by
  intro y
  obtain ⟨x, s, h⟩ := span_of_cols (Formalism.MainNotions.product_first_zeroth_parts.Nm_succ D.R) (iXm D) (zc D) (iXm_mulVec_injective D) (zc_not_range D) y
  refine ⟨x, s, ?_⟩
  rw [h]
  simp only [iXm, LinearMap.toMatrix'_mulVec]

variable {D}

theorem defN_of_fact {n : ℕ} (J : Matrix (Fin n) (Fin n) D.host.E) (C : GL (Fin n) D.host.E)
    (hC : cT (sigD D : D.host.E →+* D.host.E) C.1 * C.1 = J) (φ : D.host.E →+* ℂ) (x : Fin n → D.host.E) :
    ∃ r : ℝ, 0 ≤ r ∧ φ (hform (sigD D : D.host.E →+* D.host.E) J x x) = r ∧ (r = 0 → x = 0) := by
  have e1 : hform (sigD D : D.host.E →+* D.host.E) J x x =
      ∑ a, (sigD D : D.host.E →+* D.host.E) ((C.1 *ᵥ x) a) * (C.1 *ᵥ x) a := by
    rw [← hC, ← Matrix.mul_one (cT (sigD D : D.host.E →+* D.host.E) C.1), ← Formalism.L2.GlobalTheoryTheory.Comp.hform_mulVec_rect]
    simp only [hform, Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  refine ⟨∑ a, Complex.normSq (φ ((C.1 *ᵥ x) a)), Finset.sum_nonneg (fun a _ => Complex.normSq_nonneg _), ?_, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [e1, map_sum, Complex.ofReal_sum]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [map_mul, conj_sigD, Complex.normSq_eq_conj_mul_self]
  · intro h0
    have hz : C.1 *ᵥ x = 0 := by
      funext a
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => Complex.normSq_nonneg _)).mp h0 a (Finset.mem_univ _)
      rw [Complex.normSq_eq_zero, map_eq_zero] at this
      exact this
    have hCi : IsUnit C.1.det := (Matrix.isUnit_iff_isUnit_det _).mp C.isUnit
    calc x = C.1⁻¹ *ᵥ (C.1 *ᵥ x) := by rw [mulVec_mulVec, nonsing_inv_mul _ hCi, one_mulVec]
      _ = 0 := by rw [hz, mulVec_zero]

variable {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

theorem crdFacts_of (Tf : FormsTiedSym D u Ch chOf) : CrdFacts D := by
  obtain ⟨C, hC, -, -⟩ := (Tf.val D.R.m le_rfl (Or.inr rfl)).de
  exact
    { conj := conj_sigD D
      defN := fun φ x => defN_of_fact (gramN D D.R.m le_rfl) C hC φ x
      iso := hform_iXc D
      orth := fun x => ⟨hform_iXc_zc D x, hform_zc_iXc D x⟩
      span := span_iXc_zc D }

end Formalism.L2.GlobalTheoryTheory.Br
end
end
