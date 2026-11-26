module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarIsomG

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarGramPair
noncomputable section

open scoped Classical
open Matrix

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.FsLA

open Formalism.MainNotions.S

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E}

theorem lm_conjTranspose {N : ℕ} (A : Matrix (Fin N) (Fin N) E) (l : ℕ) :
    leadMinorE Aᴴ l = star (leadMinorE A l) := by
  unfold leadMinorE
  split_ifs with h
  · rw [← Matrix.conjTranspose_submatrix, Matrix.det_conjTranspose]
  · simp

theorem eq_of_mulVec_last {r : ℕ} (A : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (hA : A.det ≠ 0) (x : Fin (r + 1) → E)
    (c : E) (h : A *ᵥ x = c • Pi.single (Fin.last r) 1) :
    x = (c / A.det) • fun b => A.adjugate b (Fin.last r) := by
  have hx : x = A⁻¹ *ᵥ (c • Pi.single (Fin.last r) 1) := by
    rw [← h, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hA), Matrix.one_mulVec]
  rw [hx, Matrix.inv_def, Ring.inverse_eq_inv']
  ext b
  simp [Matrix.mulVec, dotProduct, Matrix.smul_apply, Pi.single_apply, div_eq_inv_mul]
  ring

theorem gram_pair_det {r : ℕ} {T T' : E} (F : FlagG S r T) (f₁ : Fin (r + 1) → S.V)
    (h1 : ∀ a b, (a ≠ Fin.last r ∨ b ≠ Fin.last r) → S.hT (f₁ a) (f₁ b) = 0)
    (h2 : S.hT (f₁ (Fin.last r)) (f₁ (Fin.last r)) = -T')
    (hZ₁ : (gram S f₁ F.fvec).det ≠ 0)
    (hG : (gram S f₁ F.fvec).det * star (gram S f₁ F.fvec).det -
      T * T' * (leadMinorE (gram S f₁ F.fvec) r * star (leadMinorE (gram S f₁ F.fvec) r)) ≠ 0) :
    (gram S (Sum.elim F.fvec f₁) (Sum.elim F.fvec f₁)).det ≠ 0 := by
  set f := F.fvec with hf
  set Z₁ := gram S f₁ f with hZ₁d
  set l := Fin.last r with hl
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  set α : Fin (r + 1) → E := fun a => v (Sum.inl a) with hα
  set β : Fin (r + 1) → E := fun b => v (Sum.inr b) with hβ
  have hrow : ∀ k, ∑ a, S.hT (Sum.elim f f₁ k) (f a) * α a + ∑ b, S.hT (Sum.elim f f₁ k) (f₁ b) * β b = 0 := by
    intro k
    have := congrFun hv k
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, gram, Sum.elim_inl, Sum.elim_inr,
      Pi.zero_apply] at this
    exact this
  have hΓ : ∀ a' (x : Fin (r + 1) → E), ∑ a, S.hT (f a') (f a) * x a = if a' = l then -T * x l else 0 := by
    intro a' x
    rw [Finset.sum_eq_single l]
    · split_ifs with h
      · subst h; rw [show S.hT (f l) (f l) = -T from gram_fvec_last F]
      · rw [show S.hT (f a') (f l) = 0 from gram_fvec_zero F _ _ (Or.inl h), zero_mul]
    · intro a _ ha; rw [show S.hT (f a') (f a) = 0 from gram_fvec_zero F _ _ (Or.inr ha), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hΓ' : ∀ b' (x : Fin (r + 1) → E), ∑ b, S.hT (f₁ b') (f₁ b) * x b = if b' = l then -T' * x l else 0 := by
    intro b' x
    rw [Finset.sum_eq_single l]
    · split_ifs with h
      · subst h; rw [h2]
      · rw [h1 _ _ (Or.inl h), zero_mul]
    · intro b _ hb; rw [h1 _ _ (Or.inr hb), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hZβ : Z₁ *ᵥ β = (T * α l) • Pi.single l 1 := by
    ext a'
    have e := hrow (Sum.inl a')
    simp only [Sum.elim_inl, hΓ] at e
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, Pi.single_apply, smul_eq_mul, hZ₁d, gram]
    split_ifs at e ⊢ with h
    · linear_combination e
    · linear_combination e
  have hZα : Z₁ᴴ *ᵥ α = (T' * β l) • Pi.single l 1 := by
    ext b'
    have e := hrow (Sum.inr b')
    simp only [Sum.elim_inr, hΓ'] at e
    have hc : ∀ a, S.hT (f₁ b') (f a) = Z₁ᴴ b' a := fun a => by
      rw [Matrix.conjTranspose_apply, hZ₁d, gram, ← (LinearMap.isSymm_def.1 S.herm) (f₁ b') (f a),
        starRingEnd_apply, star_star]
    simp only [hc] at e
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    split_ifs at e ⊢ with h
    · linear_combination e
    · linear_combination e
  have hZ₁h : Z₁ᴴ.det ≠ 0 := by rw [Matrix.det_conjTranspose]; exact star_ne_zero.2 hZ₁
  have eβ := eq_of_mulVec_last Z₁ hZ₁ β _ hZβ
  have eα := eq_of_mulVec_last Z₁ᴴ hZ₁h α _ hZα
  have eβl : β l = T * α l / Z₁.det * leadMinorE Z₁ r := by
    have := congrFun eβ l
    rw [this, Pi.smul_apply, smul_eq_mul, adj_last]
  have eαl : α l = T' * β l / star Z₁.det * star (leadMinorE Z₁ r) := by
    have := congrFun eα l
    rw [this, Pi.smul_apply, smul_eq_mul, adj_last, lm_conjTranspose, Matrix.det_conjTranspose]
  have hsZ : star Z₁.det ≠ 0 := star_ne_zero.2 hZ₁
  have hαl : α l = 0 := by
    have key : α l * (Z₁.det * star Z₁.det - T * T' * (leadMinorE Z₁ r * star (leadMinorE Z₁ r))) = 0 := by
      rw [eβl] at eαl
      field_simp at eαl
      linear_combination eαl
    rcases mul_eq_zero.1 key with h | h
    · exact h
    · exact absurd h hG
  have hβ0 : β = 0 := by rw [eβ, hαl, mul_zero, zero_div, zero_smul]
  have hβl : β l = 0 := by rw [hβ0]; rfl
  have hα0 : α = 0 := by rw [eα, hβl, mul_zero, zero_div, zero_smul]
  apply hv0
  funext k
  rcases k with a | b
  · exact congrFun hα0 a
  · exact congrFun hβ0 b

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.FsLA
end
end

noncomputable section

open scoped Classical
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

def starInU (γ : TermDef.Term D u u' F0 what₂) (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) : Prop :=
  ∀ b, frame F'₂ b ∈ Submodule.span D.host.E (Set.range (Sum.elim (frame (lf D F0)) (starFrame γ)))

def starOmL (f f' : Fin (D.R.rS + 1) → (VS D).V) : (VS D).V :=
  ∑ a, star ((starZh f f').adjugate (Fin.last D.R.rS) a) • f a

theorem star_frame_lead_minor (γ : TermDef.Term D u u' F0 what₂) (l : ℕ) :
    leadMinorE (starZh (frame (lf D F0)) (starFrame γ)) l = leadMinorE (ZhatL (lf D F0) (repF γ)) l := by
  obtain ⟨hξ1, hξ2⟩ := inv_unitri _ (admissibility_witness_unitriangular γ.lam (lf D F0) (repF γ)).1 (admissibility_witness_unitriangular γ.lam (lf D F0) (repF γ)).2
  have hZ : starZh (frame (lf D F0)) (starFrame γ) =
      1 * ZhatL (lf D F0) (repF γ) *
        (Matrix.of fun a b => (((admXi D γ.lam (lf D F0) (repF γ))⁻¹ a b : 𝓞 D.host.E) : D.host.E)) := by
    rw [Matrix.one_mul]
    exact FsLA.gram_comb_left (S := VS D) (frame (repF γ)) _ (frame (lf D F0))
  rw [hZ, Formalism.L2.SG.Pf.leadMinor_uni 1 _ _ (fun a c h => Matrix.one_apply_ne (ne_of_lt h))
    (fun a => Matrix.one_apply_eq a) (fun d b h => by simp [Matrix.of_apply, hξ1 d b h])
    (fun b => by simp [Matrix.of_apply, hξ2 b]) l]

theorem starG_ne (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)) (hγ : EligAt γ w) :
    (starZh (frame (lf D F0)) (starFrame γ)).det * star (starZh (frame (lf D F0)) (starFrame γ)).det -
      CntLocal.Tn u * ((Tu D u' : ℕ) : D.host.E) *
        (leadMinorE (starZh (frame (lf D F0)) (starFrame γ)) D.R.rS *
          star (leadMinorE (starZh (frame (lf D F0)) (starFrame γ)) D.R.rS)) ≠ 0 := by
  obtain ⟨-, hG⟩ := hγ.1
  obtain ⟨h2, h2e⟩ := starRepF_rep γ
  have hrel2 := (Formalism.L2.SG.Pf.double_coset_equivalence γ.lam (lf D F0) (PD D γ.lam (lf D F0) u') (Quot.out γ.cls)
    ⟨repF γ, h2⟩).1 ((Quot.out_eq γ.cls).trans h2e.symm)
  have hGv : Gval (lf D F0) (repF γ) ≠ 0 := by
    have he := Formalism.L2.SG.Pf.gval_rel (lf D F0) hrel2
    change Gval (lf D F0) (repF γ) = _ at he
    rw [he]; exact hG
  rw [← FsLA.leadMinorE_full, star_frame_lead_minor, star_frame_lead_minor]
  exact hGv

theorem starGlob (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) (hC : Ctx γ Z)
    (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (hZ : ZhatL (lf D F0) F'₂ = Z)
    (hU : starInU γ F'₂) :
    ∃ (g : (VS D).V ≃ₗ[D.host.E] (VS D).V) (y : Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1) → (VS D).V),
      (∀ x x', (VS D).hT (g x) (g x') = (VS D).hT x x') ∧ (∀ b, g (starFrame γ b) = frame F'₂ b) ∧
      (∀ v, g v = v + ∑ k, (VS D).hT (Sum.elim (frame (lf D F0)) (starFrame γ) k) v • y k) ∧
      star (starZh (frame (lf D F0)) (starFrame γ)).det • starOmL (frame (lf D F0)) (frame F'₂) -
        star Z.det • g (starOmL (frame (lf D F0)) (starFrame γ)) ∈ Xsp F'₂ := by
  obtain ⟨w, hγ, -⟩ := id hC
  obtain ⟨hZd, hZ₁d, hx⟩ := starMinors_holds u u' F0 what₂ γ Z hC
  set f := frame (lf D F0) with hf
  set f₁ := starFrame γ with hf₁
  set Z₁ := starZh f f₁ with hZ₁
  set F₂ := F'₂.fl with hF₂
  have hfF : f = F0.fvec := rfl
  have hf₂ : frame F'₂ = F₂.fvec := rfl
  have hZe : ∀ a b, (VS D).hT (f a) (F₂.fvec b) = Z a b := fun a b => by rw [← hZ]; rfl
  have hg2 : FsLA.gram (VS D) f F₂.fvec = Zᴴ := by
    refine Matrix.ext fun i j => ?_
    simp only [FsLA.gram, Matrix.conjTranspose_apply]
    rw [← hZe, ← (LinearMap.isSymm_def.1 (VS D).herm) (f j) (F₂.fvec i), starRingEnd_apply]
  have hZ1e : FsLA.gram (VS D) f₁ F0.fvec = Z₁ := rfl
  obtain ⟨hf1a, hf1b⟩ := star_frame_orthogonal γ
  have h1f : ∀ a b, (a ≠ Fin.last D.R.rS ∨ b ≠ Fin.last D.R.rS) → (VS D).hT (f a) (f b) = 0 :=
    fun a b h => FsLA.gram_fvec_zero F0 a b h
  have h2f : (VS D).hT (f (Fin.last D.R.rS)) (f (Fin.last D.R.rS)) = -CntLocal.Tn u := FsLA.gram_fvec_last F0
  have hdZ1h : Z₁ᴴ.det ≠ 0 := by rw [Matrix.det_conjTranspose]; exact star_ne_zero.2 hZ₁d
  have hdg2 : (FsLA.gram (VS D) f F₂.fvec).det ≠ 0 := by
    rw [hg2, Matrix.det_conjTranspose]; exact star_ne_zero.2 hZd
  have hx2 : leadMinorE (FsLA.gram (VS D) f F₂.fvec) D.R.rS * Z₁ᴴ.det =
      leadMinorE Z₁ᴴ D.R.rS * (FsLA.gram (VS D) f F₂.fvec).det := by
    rw [hg2, FsLA.lm_conjTranspose, FsLA.lm_conjTranspose, Matrix.det_conjTranspose, Matrix.det_conjTranspose,
      ← star_mul', ← star_mul', mul_comm (leadMinorE Z D.R.rS), hx, mul_comm]
  obtain ⟨F₃, hZ3, hom3, hsp3⟩ := FsLA.frame_la F₂ f h1f h2f Z₁ᴴ hdZ1h hdg2 hx2
  set h := F₃.fvec with hh
  set uu := Sum.elim f f₁ with huu
  set uu' := Sum.elim h F₂.fvec with huu'
  have hZ3e : ∀ a b, (VS D).hT (F₂.fvec a) (h b) = Z₁ᴴ a b := fun a b => congrFun (congrFun hZ3 a) b
  have k1 : ∀ a b, (VS D).hT (h a) (h b) = (VS D).hT (f a) (f b) := by
    intro a b
    by_cases hab : a ≠ Fin.last D.R.rS ∨ b ≠ Fin.last D.R.rS
    · exact (FsLA.gram_fvec_zero F₃ a b hab).trans (FsLA.gram_fvec_zero F0 a b hab).symm
    · push_neg at hab
      rw [hab.1, hab.2]
      exact (FsLA.gram_fvec_last F₃).trans (FsLA.gram_fvec_last F0).symm
  have k2 : ∀ a b, (VS D).hT (h a) (F₂.fvec b) = (VS D).hT (f a) (f₁ b) := by
    intro a b
    rw [← (LinearMap.isSymm_def.1 (VS D).herm) (F₂.fvec b) (h a), hZ3e, starRingEnd_apply,
      Matrix.conjTranspose_apply, star_star]
    rfl
  have k3 : ∀ a b, (VS D).hT (F₂.fvec a) (h b) = (VS D).hT (f₁ a) (f b) := by
    intro a b
    rw [hZ3e, Matrix.conjTranspose_apply, ← starRingEnd_apply]
    exact (LinearMap.isSymm_def.1 (VS D).herm) (f b) (f₁ a)
  have k4 : ∀ a b, (VS D).hT (F₂.fvec a) (F₂.fvec b) = (VS D).hT (f₁ a) (f₁ b) := by
    intro a b
    by_cases hab : a ≠ Fin.last D.R.rS ∨ b ≠ Fin.last D.R.rS
    · exact (FsLA.gram_fvec_zero F₂ a b hab).trans (hf1a a b hab).symm
    · push_neg at hab
      rw [hab.1, hab.2]
      exact (FsLA.gram_fvec_last F₂).trans hf1b.symm
  have hGr : FsLA.gram (VS D) uu' uu' = FsLA.gram (VS D) uu uu := by
    refine Matrix.ext fun i j => ?_
    rcases i with a | a <;> rcases j with b | b
    · exact k1 a b
    · exact k2 a b
    · exact k3 a b
    · exact k4 a b
  have hdet : (FsLA.gram (VS D) uu uu).det ≠ 0 :=
    FsLA.gram_pair_det F0 f₁ hf1a hf1b hZ₁d (starG_ne γ w hγ)
  have hsp : ∀ i, uu' i ∈ Submodule.span D.host.E (Set.range uu) := by
    have hsub : Set.range (Sum.elim F₂.fvec f) ⊆ Submodule.span D.host.E (Set.range uu) := by
      rintro _ ⟨k, rfl⟩
      rcases k with b | a
      · exact hU b
      · exact Submodule.subset_span ⟨Sum.inl a, rfl⟩
    intro i
    rcases i with a | b
    · exact Submodule.span_le.2 hsub (hsp3 a)
    · exact hU b
  obtain ⟨g, hiso, hgu, -, hform⟩ := FsLA.isom_ext uu uu' hGr hdet hsp
  refine ⟨g, fun k => ∑ m, (FsLA.gram (VS D) uu uu)⁻¹ m k • (uu' m - uu m), hiso, fun b => hgu (Sum.inr b),
    hform, ?_⟩

  have homf : FsLA.om (VS D) F₂.fvec f = starOmL f (frame F'₂) := by
    rw [FsLA.om, hg2, ← Matrix.adjugate_conjTranspose]
    simp only [starOmL, Matrix.conjTranspose_apply]
    rw [← hZ]
    rfl
  have homh : FsLA.om (VS D) F₂.fvec h = g (starOmL f f₁) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [FsLA.om, starOmL, map_sum, map_smul]
    have e : FsLA.gram (VS D) h F₂.fvec = Z₁ᴴ := hZ3
    rw [e]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Matrix.adjugate_conjTranspose, Matrix.conjTranspose_apply]
    congr 1
    exact (hgu (Sum.inl a)).symm
  have e1 : Z₁ᴴ.det = star Z₁.det := Matrix.det_conjTranspose _
  have e2 : (FsLA.gram (VS D) f F₂.fvec).det = star Z.det := by rw [hg2, Matrix.det_conjTranspose]
  rw [e1, e2, homf, homh] at hom3
  exact hom3

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
