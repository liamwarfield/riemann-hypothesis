module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.LamSMulVec

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.SumMapCompSub
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.FormCAddRight
noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.LocCnt0LAlg

variable {E : Type} [CommRing E] (O : Subring E) (cj : E →+* E) {r : ℕ}

theorem mem_relC_of_mk (hO : ∀ x ∈ O, cj x ∈ O) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O)
    (t t' : O) (u u' : Fin (r + 1) → O) (α β : O)
    (h : (Submodule.Quotient.mk u : MbMod Z) = α • bCls Z - (t * β) • eCl Z)
    (h' : (Submodule.Quotient.mk u' : MbMod (cjT O cj hO Z)) =
      β • bCls (cjT O cj hO Z) - (t' * α) • eCl (cjT O cj hO Z)) :
    (Sum.elim u u' : Ix r → O) ∈ relC O cj (Z.map O.subtype) t t' := by
  rw [bCls, eCl, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul,
    ← Submodule.Quotient.mk_sub, Submodule.Quotient.eq] at h h'
  obtain ⟨w, hw, hwe⟩ := (mem_headCols_iff _ _).1 h
  obtain ⟨v, hv, hve⟩ := (mem_headCols_iff _ _).1 h'
  rw [mem_relC_iff O cj hO Z t t']
  refine ⟨v + β • Pi.single (Fin.last r) 1, w + α • Pi.single (Fin.last r) 1, ?_, ?_⟩
  · have hl : ((v + β • Pi.single (Fin.last r) 1 : Fin (r + 1) → O)) (Fin.last r) = β := by simp [hv]
    rw [hl, Matrix.mulVec_add, Matrix.mulVec_smul, ← bvec_eq, ← hwe]
    show u = _
    abel
  · have hl : ((w + α • Pi.single (Fin.last r) 1 : Fin (r + 1) → O)) (Fin.last r) = α := by simp [hw]
    rw [hl, Matrix.mulVec_add, Matrix.mulVec_smul, ← bvec_eq, ← hve]
    show u' = _
    abel

theorem mem_relC_of_K (hO : ∀ x ∈ O, cj x ∈ O) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O)
    (t t' : O) (u u' : Fin (r + 1) → O) (hu : u ∈ headCols Z) (hu' : u' ∈ headCols (cjT O cj hO Z)) :
    (Sum.elim u u' : Ix r → O) ∈ relC O cj (Z.map O.subtype) t t' := by
  apply mem_relC_of_mk O cj hO Z t t' u u' 0 0
  · rw [(Submodule.Quotient.mk_eq_zero _).2 hu]; simp
  · rw [(Submodule.Quotient.mk_eq_zero _).2 hu']; simp

theorem gramC_herm (hcj : ∀ x, cj (cj x) = x) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : E)
    (hT : cj T = T) (hT' : cj T' = T') (k j : Ix r) :
    cj (gramC cj Z T T' k j) = gramC cj Z T T' j k := by
  rcases k with a | a <;> rcases j with b | b <;>
    simp [gramC, hcj, apply_ite cj, hT, hT', and_comm]

theorem formC_add_left (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : E) (Y Y' W : Ix r → O) :
    formC O cj Z T T' (Y + Y') W = formC O cj Z T T' Y W + formC O cj Z T T' Y' W := by
  simp [formC, add_mul, Finset.sum_add_distrib]

theorem formC_add_right (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : E) (Y W W' : Ix r → O) :
    formC O cj Z T T' Y (W + W') = formC O cj Z T T' Y W + formC O cj Z T T' Y W' := by
  simp [formC, mul_add, Finset.sum_add_distrib]

theorem formC_sub_left (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : E) (Y Y' W : Ix r → O) :
    formC O cj Z T T' (Y - Y') W = formC O cj Z T T' Y W - formC O cj Z T T' Y' W := by
  have := formC_add_left O cj Z T T' (Y - Y') Y' W
  rw [sub_add_cancel] at this
  rw [this]; ring

theorem formC_sub_right (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : E) (Y W W' : Ix r → O) :
    formC O cj Z T T' Y (W - W') = formC O cj Z T T' Y W - formC O cj Z T T' Y W' := by
  have := formC_add_right O cj Z T T' Y (W - W') W'
  rw [sub_add_cancel] at this
  rw [this]; ring

theorem formC_rel_left (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : E)
    (hG : IsUnit (gramC cj Z T T').det) (hO : ∀ x ∈ O, cj x ∈ O) (Y W : Ix r → O)
    (hY : Y ∈ relC O cj Z T T') : formC O cj Z T T' Y W ∈ O := by
  obtain ⟨c, hc⟩ := hY
  rw [formC_of_rel O cj Z T T' hG Y W (fun i => (c i : E)) hc]
  exact O.sum_mem fun j _ => O.mul_mem (c j).2 (hO _ (W j).2)

theorem formC_rel_right (hcj : ∀ x, cj (cj x) = x) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : E)
    (hT : cj T = T) (hT' : cj T' = T')
    (hG : IsUnit (gramC cj Z T T').det) (hO : ∀ x ∈ O, cj x ∈ O) (Y W : Ix r → O)
    (hW : W ∈ relC O cj Z T T') : formC O cj Z T T' Y W ∈ O := by
  obtain ⟨d, hd⟩ := hW
  have hinv := Matrix.nonsing_inv_mul (gramC cj Z T T') hG
  have key : ∀ i, ∑ j, (gramC cj Z T T')⁻¹ i j * cj (W j : E) = cj (d i : E) := by
    intro i
    have h1 : ∀ j, cj (W j : E) = ∑ k, cj (d k : E) * gramC cj Z T T' j k := by
      intro j
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hd j, map_sum]
      exact Finset.sum_congr rfl fun k _ => by rw [map_mul, gramC_herm cj hcj Z T T' hT hT']
    simp only [h1, Finset.mul_sum]
    rw [Finset.sum_comm]
    have h2 : ∀ k, ∑ j, (gramC cj Z T T')⁻¹ i j * (cj (d k : E) * gramC cj Z T T' j k) =
        cj (d k : E) * ((gramC cj Z T T')⁻¹ * gramC cj Z T T') i k := by
      intro k
      rw [Matrix.mul_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    simp only [h2, hinv, Matrix.one_apply]
    simp
  unfold formC
  have h3 : ∀ i, ∑ j, (Y i : E) * (gramC cj Z T T')⁻¹ i j * cj (W j : E) = (Y i : E) * cj (d i : E) := by
    intro i
    rw [← key i, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [h3]
  exact O.sum_mem fun i _ => O.mul_mem (Y i).2 (hO _ (d i).2)

end Formalism.L2.SG.LocalCountModules.LocCnt0LAlg
end
end

noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.LocCnt0LAlg

variable {E : Type} [CommRing E] (O : Subring E) (cj : E →+* E) {r : ℕ}

def liftOf {Z Z' : Matrix (Fin (r + 1)) (Fin (r + 1)) O} (f : MbMod Z →ₗ[O] MbMod Z') :
    (Fin (r + 1) → O) →ₗ[O] (Fin (r + 1) → O) :=
  (Module.projective_lifting_property (headCols Z').mkQ (f ∘ₗ (headCols Z).mkQ)
    (Submodule.mkQ_surjective _)).choose

theorem liftOf_spec {Z Z' : Matrix (Fin (r + 1)) (Fin (r + 1)) O} (f : MbMod Z →ₗ[O] MbMod Z')
    (y : Fin (r + 1) → O) :
    (Submodule.Quotient.mk (liftOf O f y) : MbMod Z') = f (Submodule.Quotient.mk y) := LinearMap.congr_fun (Module.projective_lifting_property (headCols Z').mkQ (f ∘ₗ (headCols Z).mkQ)
    (Submodule.mkQ_surjective _)).choose_spec y

def sumMap (g gs : (Fin (r + 1) → O) →ₗ[O] (Fin (r + 1) → O)) : (Ix r → O) →ₗ[O] (Ix r → O) where
  toFun Y := Sum.elim (g fun j => Y (Sum.inl j)) (gs fun j => Y (Sum.inr j))
  map_add' Y W := by
    have h1 : (fun j => (Y + W) (Sum.inl j)) = (fun j => Y (Sum.inl j)) + (fun j => W (Sum.inl j)) := rfl
    have h2 : (fun j => (Y + W) (Sum.inr j)) = (fun j => Y (Sum.inr j)) + (fun j => W (Sum.inr j)) := rfl
    rw [h1, h2, map_add (f := _), map_add (f := _)]
    funext i; cases i <;> rfl
  map_smul' c Y := by
    have h1 : (fun j => (c • Y) (Sum.inl j)) = c • (fun j => Y (Sum.inl j)) := rfl
    have h2 : (fun j => (c • Y) (Sum.inr j)) = c • (fun j => Y (Sum.inr j)) := rfl
    rw [h1, h2, map_smul, map_smul]
    funext i; cases i <;> rfl

theorem sumMap_apply (g gs : (Fin (r + 1) → O) →ₗ[O] (Fin (r + 1) → O)) (Y : Ix r → O) :
    sumMap O g gs Y = Sum.elim (g fun j => Y (Sum.inl j)) (gs fun j => Y (Sum.inr j)) := rfl

variable (hO : ∀ x ∈ O, cj x ∈ O) (t t' : O)
variable {Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) O}

theorem mk_gen (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (c₂ : Fin (r + 1) → O) (s : O) :
    (Submodule.Quotient.mk (Z.mulVec c₂ - s • Pi.single (Fin.last r) 1) : MbMod Z) =
      c₂ (Fin.last r) • bCls Z - s • eCl Z := by
  rw [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul]
  congr 1
  unfold bCls
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
  have hsum : Z.mulVec c₂ - c₂ (Fin.last r) • (fun i => Z i (Fin.last r)) =
      ∑ a : Fin r, c₂ a.castSucc • (fun i => Z i a.castSucc) := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Pi.sub_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    rw [Fin.sum_univ_castSucc]
    simp only [mul_comm]
    ring
  rw [hsum]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

theorem sumMap_le (γ : MbMod Z₁ →ₗ[O] MbMod Z₂)
    (γs : MbMod (cjT O cj hO Z₁) →ₗ[O] MbMod (cjT O cj hO Z₂))
    (hb : γ (bCls Z₁) = bCls Z₂) (he : γ (eCl Z₁) = eCl Z₂)
    (hbs : γs (bCls (cjT O cj hO Z₁)) = bCls (cjT O cj hO Z₂))
    (hes : γs (eCl (cjT O cj hO Z₁)) = eCl (cjT O cj hO Z₂)) :
    relC O cj (Z₁.map O.subtype) t t' ≤
      (relC O cj (Z₂.map O.subtype) t t').comap (sumMap O (liftOf O γ) (liftOf O γs)) := by
  intro Y hY
  rw [Submodule.mem_comap, sumMap_apply]
  obtain ⟨c₁, c₂, h1, h2⟩ := (mem_relC_iff O cj hO Z₁ t t' Y).1 hY
  refine mem_relC_of_mk O cj hO Z₂ t t' _ _ (c₂ (Fin.last r)) (c₁ (Fin.last r)) ?_ ?_
  · rw [liftOf_spec, h1, mk_gen, map_sub, map_smul, map_smul, hb, he]
  · rw [liftOf_spec, h2, mk_gen, map_sub, map_smul, map_smul, hbs, hes]

theorem sumMap_comp_sub (g gs g' gs' : (Fin (r + 1) → O) →ₗ[O] (Fin (r + 1) → O)) (Y : Ix r → O) :
    sumMap O g gs (sumMap O g' gs' Y) - Y =
      Sum.elim (g (g' fun j => Y (Sum.inl j)) - fun j => Y (Sum.inl j))
        (gs (gs' fun j => Y (Sum.inr j)) - fun j => Y (Sum.inr j)) := by
  funext i
  cases i <;> rfl

def thetaOf (hO : ∀ x ∈ O, cj x ∈ O) (t t' : O) (γ : MbMod Z₁ ≃ₗ[O] MbMod Z₂)
    (γs : MbMod (cjT O cj hO Z₁) ≃ₗ[O] MbMod (cjT O cj hO Z₂))
    (hb : γ (bCls Z₁) = bCls Z₂) (he : γ (eCl Z₁) = eCl Z₂)
    (hbs : γs (bCls (cjT O cj hO Z₁)) = bCls (cjT O cj hO Z₂))
    (hes : γs (eCl (cjT O cj hO Z₁)) = eCl (cjT O cj hO Z₂)) :
    DDc O cj (Z₁.map O.subtype) t t' ≃ₗ[O] DDc O cj (Z₂.map O.subtype) t t' :=
  LinearEquiv.ofLinear
    ((relC O cj (Z₁.map O.subtype) t t').mapQ _ (sumMap O (liftOf O γ.toLinearMap) (liftOf O γs.toLinearMap))
      (sumMap_le O cj hO t t' γ.toLinearMap γs.toLinearMap hb he hbs hes))
    ((relC O cj (Z₂.map O.subtype) t t').mapQ _
      (sumMap O (liftOf O γ.symm.toLinearMap) (liftOf O γs.symm.toLinearMap))
      (sumMap_le O cj hO t t' γ.symm.toLinearMap γs.symm.toLinearMap
        (by rw [LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_eq, hb])
        (by rw [LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_eq, he])
        (by rw [LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_eq, hbs])
        (by rw [LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_eq, hes])))
    (by
      refine LinearMap.ext fun m => ?_
      obtain ⟨Y, rfl⟩ := Submodule.Quotient.mk_surjective _ m
      simp only [LinearMap.comp_apply, Submodule.mapQ_apply, LinearMap.id_apply]
      rw [Submodule.Quotient.eq, sumMap_comp_sub]
      apply mem_relC_of_K
      · rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, liftOf_spec, liftOf_spec,
          sub_eq_zero]
        exact γ.apply_symm_apply _
      · rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, liftOf_spec, liftOf_spec,
          sub_eq_zero]
        exact γs.apply_symm_apply _)
    (by
      refine LinearMap.ext fun m => ?_
      obtain ⟨Y, rfl⟩ := Submodule.Quotient.mk_surjective _ m
      simp only [LinearMap.comp_apply, Submodule.mapQ_apply, LinearMap.id_apply]
      rw [Submodule.Quotient.eq, sumMap_comp_sub]
      apply mem_relC_of_K
      · rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, liftOf_spec, liftOf_spec,
          sub_eq_zero]
        exact γ.symm_apply_apply _
      · rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, liftOf_spec, liftOf_spec,
          sub_eq_zero]
        exact γs.symm_apply_apply _)

end Formalism.L2.SG.LocalCountModules.LocCnt0LAlg
end
end

noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.LocCnt0LAlg

variable {E : Type} [CommRing E] (O : Subring E) (cj : E →+* E) {r : ℕ}

theorem supp_inl (Y : Ix r → O) (h : ∀ a : Fin r, Y (Sum.inl a.castSucc) = 0) :
    (fun j => Y (Sum.inl j)) = Y (Sum.inl (Fin.last r)) • Pi.single (Fin.last r) 1 := by
  funext j
  induction j using Fin.lastCases with
  | last => simp
  | cast a => simp [h a, Pi.single_eq_of_ne (Fin.castSucc_lt_last a).ne]

theorem supp_inr (Y : Ix r → O) (h : ∀ a : Fin r, Y (Sum.inr a.castSucc) = 0) :
    (fun j => Y (Sum.inr j)) = Y (Sum.inr (Fin.last r)) • Pi.single (Fin.last r) 1 := by
  funext j
  induction j using Fin.lastCases with
  | last => simp
  | cast a => simp [h a, Pi.single_eq_of_ne (Fin.castSucc_lt_last a).ne]

theorem elim_eta (Y : Ix r → O) : Y = Sum.elim (fun j => Y (Sum.inl j)) (fun j => Y (Sum.inr j)) := by
  funext i
  cases i <;> rfl

theorem lift_e_mem {Z Z' : Matrix (Fin (r + 1)) (Fin (r + 1)) O} (f : MbMod Z →ₗ[O] MbMod Z')
    (he : f (eCl Z) = eCl Z') (s : O) :
    liftOf O f (s • Pi.single (Fin.last r) 1) - s • Pi.single (Fin.last r) 1 ∈ headCols Z' := by
  rw [← Submodule.Quotient.eq, liftOf_spec, Submodule.Quotient.mk_smul, Submodule.Quotient.mk_smul, map_smul]
  exact congrArg (s • ·) he

theorem lift_rep_mem {Z Z' : Matrix (Fin (r + 1)) (Fin (r + 1)) O} (f : MbMod Z ≃ₗ[O] MbMod Z')
    (y : Fin (r + 1) → O) (y₂ : Fin (r + 1) → O)
    (hy : (Submodule.Quotient.mk y : MbMod Z) = f.symm (Submodule.Quotient.mk y₂)) :
    liftOf O f.toLinearMap y - y₂ ∈ headCols Z' := by
  rw [← Submodule.Quotient.eq, liftOf_spec, hy, LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply]

end Formalism.L2.SG.LocalCountModules.LocCnt0LAlg
