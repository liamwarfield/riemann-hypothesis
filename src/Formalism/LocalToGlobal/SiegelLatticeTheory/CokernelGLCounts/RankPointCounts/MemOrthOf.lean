module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IdxRatioConjOfUnimod

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ZsVolFib
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ZsVolKey
noncomputable section

namespace Formalism.L2.SG.Pf.ZsVolKey

open Formalism.L2.SG.Pf.StabilizerIndexVolumes Matrix

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {r : ℕ} {T T' : E}

theorem act_inv (f : Fin (r + 1) → S.V) (s : S.V ≃ₗ[E] S.V) (P : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hP : P * P⁻¹ = 1) (hs : ∀ b, s (f b) = ∑ c, P c b • f c) (b : Fin (r + 1)) :
    s (∑ c, P⁻¹ c b • f c) = f b := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, hs, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  have h1 : ∀ d, ∑ c, P⁻¹ c b * P d c = (P * P⁻¹) d b := fun d => by
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun c _ => mul_comm _ _
  simp only [h1, hP, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

theorem up_inv_mul {P : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (hP : Formalism.MainNotions.S.IsUpUni P) : P * P⁻¹ = 1 := by
  have htri : P.BlockTriangular id := fun i j hij => (hP i j).1 hij
  have hdet : P.det = 1 := by
    rw [Matrix.det_of_upperTriangular htri]
    exact Finset.prod_eq_one fun i _ => (hP i i).2 rfl
  exact Matrix.mul_nonsing_inv P (by rw [hdet]; exact isUnit_one)

theorem eq_sL (F : Formalism.MainNotions.S.FlagG S r T) (F' : Formalism.MainNotions.S.FlagG S r T') (hG : IsUnit (gramOf (gg F F')).det)
    (s : S.V ≃ₗ[E] S.V) (hs : ∀ x y, S.hT (s x) (s y) = S.hT x y)
    (P Q : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (hP : Formalism.MainNotions.S.IsUpUni P) (hQ : Formalism.MainNotions.S.IsUpUni Q)
    (hsf : ∀ b, s (F.fvec b) = ∑ c, P c b • F.fvec c) (hsf' : ∀ b, s (F'.fvec b) = ∑ c, Q c b • F'.fvec c)
    (hsX : ∀ x, (∀ i, S.hT (F.e i) x = 0) → s x - x ∈ Submodule.span E (Set.range F.e)) (x : S.V) :
    s x = sL (gg F F') (UU P Q) x := by
  classical
  have hframe : ∀ m, s (gg F F' m) = sL (gg F F') (UU P Q) (gg F F' m) := by
    intro m
    cases m with
    | inl b =>
      show s (F.fvec b) = sL (gg F F') (UU P Q) (F.fvec b)
      rw [hsf, sL_frame (F := F) (F' := F') hG P Q b]
    | inr b =>
      show s (F'.fvec b) = sL (gg F F') (UU P Q) (F'.fvec b)
      rw [hsf', sL_frame' (F := F) (F' := F') hG P Q b]
  have hy : ∀ l, S.hT (gg F F' l) (x - ∑ m, cOf (gg F F') x m • gg F F' m) = 0 := by
    intro l
    have h1 := congrFun (gram_cOf (gg F F') hG x) l
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_sum, ← h1]
    simp only [map_smul, smul_eq_mul, Matrix.mulVec, dotProduct, gramOf]
    rw [sub_eq_zero]
    exact Finset.sum_congr rfl fun m _ => mul_comm _ _
  have hspan0 : ∀ w ∈ Submodule.span E (Set.range (gg F F')),
      S.hT w (x - ∑ m, cOf (gg F F') x m • gg F F' m) = 0 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨l, rfl⟩ := hv
      exact hy l
    | zero => rw [map_zero, LinearMap.zero_apply]
    | add a b _ _ ha hb => rw [map_add (f := _), LinearMap.add_apply, ha, hb, add_zero]
    | smul a v _ hv => rw [map_smulₛₗ, LinearMap.smul_apply, hv, smul_zero]
  have hpre : ∀ l, ∃ w ∈ Submodule.span E (Set.range (gg F F')), s w = gg F F' l := by
    intro l
    cases l with
    | inl b =>
      refine ⟨∑ c, P⁻¹ c b • F.fvec c, Submodule.sum_mem _ fun c _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inl c, rfl⟩), ?_⟩
      exact act_inv F.fvec s P (up_inv_mul hP) hsf b
    | inr b =>
      refine ⟨∑ c, Q⁻¹ c b • F'.fvec c, Submodule.sum_mem _ fun c _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr c, rfl⟩), ?_⟩
      exact act_inv F'.fvec s Q (up_inv_mul hQ) hsf' b
  have hsy : s (x - ∑ m, cOf (gg F F') x m • gg F F' m) = x - ∑ m, cOf (gg F F') x m • gg F F' m := by
    have hy' : ∀ i, S.hT (F.e i) (x - ∑ m, cOf (gg F F') x m • gg F F' m) = 0 := by
      intro i
      have h2 := hy (Sum.inl i.castSucc)
      simpa [gg, Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc] using h2
    have hmem := hsX _ hy'
    have hdspan : s (x - ∑ m, cOf (gg F F') x m • gg F F' m) - (x - ∑ m, cOf (gg F F') x m • gg F F' m) ∈
        Submodule.span E (Set.range (gg F F')) := by
      refine Submodule.span_mono ?_ hmem
      rintro _ ⟨i, rfl⟩
      exact ⟨Sum.inl i.castSucc, by simp [gg, Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc]⟩
    have hdperp : ∀ l, S.hT (gg F F' l)
        (s (x - ∑ m, cOf (gg F F') x m • gg F F' m) - (x - ∑ m, cOf (gg F F') x m • gg F F' m)) = 0 := by
      intro l
      obtain ⟨w, hw, hwl⟩ := hpre l
      rw [map_sub, hy l, sub_zero, ← hwl, hs, hspan0 w hw]
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hdspan
    have hc0 : cOf (gg F F') (s (x - ∑ m, cOf (gg F F') x m • gg F F' m) -
        (x - ∑ m, cOf (gg F F') x m • gg F F' m)) = 0 := by
      rw [cOf_eq]
      have hz : (fun l => S.hT (gg F F' l) (s (x - ∑ m, cOf (gg F F') x m • gg F F' m) -
          (x - ∑ m, cOf (gg F F') x m • gg F F' m))) = 0 := funext hdperp
      rw [hz, Matrix.mulVec_zero]
    have hca : cOf (gg F F') (∑ m, a m • gg F F' m) = a := by
      have h3 := cOf_comb (gg F F') hG 0 a
      rw [zero_add] at h3
      rw [h3]
      have h4 := cOf_smul (gg F F') 0 0
      rw [zero_smul, zero_smul] at h4
      rw [h4, zero_add]
    rw [ha] at hca
    rw [hc0] at hca
    rw [← sub_eq_zero, ← ha, ← hca]
    simp
  have hx : x = (x - ∑ m, cOf (gg F F') x m • gg F F' m) + ∑ m, cOf (gg F F') x m • gg F F' m := by
    rw [sub_add_cancel]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hx, map_add (f := _), map_add (f := _), map_sum, map_sum, hsy, sL_perp (F := F) (F' := F') hG _ hy]
  congr 1
  exact Finset.sum_congr rfl fun m _ => by rw [map_smul, map_smul, hframe m]

theorem nlam_of_frames (F : Formalism.MainNotions.S.FlagG S r T) (F' : Formalism.MainNotions.S.FlagG S r T') (hG : IsUnit (gramOf (gg F F')).det)
    (hZu : IsUnit (Formalism.MainNotions.S.Zhat F F').det)
    (s : S.V ≃ₗ[E] S.V) (hs : ∀ x y, S.hT (s x) (s y) = S.hT x y)
    (P Q : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (hP : Formalism.MainNotions.S.IsUpUni P) (hQ : Formalism.MainNotions.S.IsUpUni Q)
    (hsf : ∀ b, s (F.fvec b) = ∑ c, P c b • F.fvec c) (hsf' : ∀ b, s (F'.fvec b) = ∑ c, Q c b • F'.fvec c)
    (hsX : ∀ x, (∀ i, S.hT (F.e i) x = 0) → s x - x ∈ Submodule.span E (Set.range F.e)) :
    (∀ j, ∀ x ∈ F'.Xa (j + 1), s x - x ∈ F'.Xa j) ∧
      (∀ x, (∀ i, S.hT (F'.e i) x = 0) → s x - x ∈ Submodule.span E (Set.range F'.e)) := by
  have hQd : Q.det = 1 := by
    have htri : Q.BlockTriangular id := fun i j hij => (hQ i j).1 hij
    rw [Matrix.det_of_upperTriangular htri]
    exact Finset.prod_eq_one fun i _ => (hQ i i).2 rfl
  have hmat : P.conjTranspose * Formalism.MainNotions.S.Zhat F F' * Q = Formalism.MainNotions.S.Zhat F F' := by
    ext a b
    have h := hs (F.fvec a) (F'.fvec b)
    rw [hsf, hsf'] at h
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, map_smul, smul_eq_mul,
      Finset.mul_sum] at h
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Formalism.MainNotions.S.Zhat, Formalism.MainNotions.S.brS]
    rw [← h, Finset.sum_comm]
    simp only [Finset.sum_mul, RingHom.id_apply, starRingEnd_apply]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => by ring
  have hZH : IsUnit (Formalism.MainNotions.S.Zhat F F').conjTranspose.det := by
    rw [Matrix.det_conjTranspose]
    exact hZu.star
  have hQH : IsUnit Q.conjTranspose.det := by
    rw [Matrix.det_conjTranspose, hQd, star_one]
    exact isUnit_one
  have h2 : Q.conjTranspose * (Formalism.MainNotions.S.Zhat F F').conjTranspose * P = (Formalism.MainNotions.S.Zhat F F').conjTranspose := by
    have h3 := congrArg Matrix.conjTranspose hmat
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      ← Matrix.mul_assoc] at h3
  have e1 : (Formalism.MainNotions.S.Zhat F F').conjTranspose * P = (Q.conjTranspose)⁻¹ * (Formalism.MainNotions.S.Zhat F F').conjTranspose := by
    conv_rhs => rw [← h2]
    rw [Matrix.mul_assoc Q.conjTranspose, ← Matrix.mul_assoc (Q.conjTranspose)⁻¹, Matrix.nonsing_inv_mul _ hQH,
      Matrix.one_mul]
  have hrel : P = ((Formalism.MainNotions.S.Zhat F F').conjTranspose)⁻¹ * (Q.conjTranspose)⁻¹ * (Formalism.MainNotions.S.Zhat F F').conjTranspose := by
    rw [Matrix.mul_assoc, ← e1, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hZH, Matrix.one_mul]
  have hQl : Formalism.MainNotions.S.IsLoUni Q.conjTranspose := fun i j =>
    ⟨fun h => by simp [Matrix.conjTranspose_apply, (hQ j i).1 h],
     fun h => by subst h; simp [Matrix.conjTranspose_apply, (hQ i i).2 rfl]⟩
  refine ⟨fun j x hx => ?_, fun x hx => ?_⟩
  · rw [eq_sL F F' hG s hs P Q hP hQ hsf hsf' hsX x]
    exact sL_Xa' (F := F) (F' := F') hG hQ j x hx
  · rw [eq_sL F F' hG s hs P Q hP hQ hsf hsf' hsX x]
    exact sL_orth' (F := F) (F' := F') hG hQ hZH hrel (loUni_inv hQl).1 x hx

end Formalism.L2.SG.Pf.ZsVolKey

end
end

noncomputable section

namespace Formalism.L2.SG.Pf.ZsVolFib

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.PairVal Matrix
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

theorem act_mul (f : Fin (D.R.rS + 1) → (VS D).V) (s s' : (VS D).V ≃ₗ[D.host.E] (VS D).V) (A B : MatR D)
    (hs : ∀ b, s (f b) = ∑ c, A c b • f c) (hs' : ∀ b, s' (f b) = ∑ c, B c b • f c) (b : Fin (D.R.rS + 1)) :
    (s * s') (f b) = ∑ c, (A * B) c b • f c := by
  show s (s' (f b)) = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hs', map_sum]
  simp only [map_smul, hs, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← Finset.sum_smul, Matrix.mul_apply]
  congr 1
  exact Finset.sum_congr rfl fun c _ => mul_comm _ _

theorem act_inv' (f : Fin (D.R.rS + 1) → (VS D).V) (s : (VS D).V ≃ₗ[D.host.E] (VS D).V) (A : MatR D)
    (hA : IsUpUni A) (hs : ∀ b, s (f b) = ∑ c, A c b • f c) (b : Fin (D.R.rS + 1)) :
    s⁻¹ (f b) = ∑ c, A⁻¹ c b • f c := by
  apply s.injective
  show s (s.symm (f b)) = _
  rw [LinearEquiv.apply_symm_apply, Formalism.L2.SG.Pf.ZsVolKey.act_inv f s A (Formalism.L2.SG.Pf.ZsVolKey.up_inv_mul hA) hs b]

theorem act_one (f : Fin (D.R.rS + 1) → (VS D).V) (b : Fin (D.R.rS + 1)) :
    (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) (f b) = ∑ c, (1 : MatR D) c b • f c := by
  simp [Matrix.one_apply]

theorem nlam_one {T : D.host.E} (Λ : Submodule (𝓞 D.host.E) (VS D).V) (F : LFlag (D.sp.Y 0) D.R.rS T) :
    (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) ∈ NLam Λ F := by
  refine ⟨(Formalism.L2.SG.Pf.isAutLam_iff Λ 1).2 ⟨fun x y => rfl, fun x => Iff.rfl⟩, fun j x _ => ?_, fun x _ => ?_⟩
  · simp
  · simp

variable (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
  (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

def stabAutG (t : Term D u u' F0 what₂) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (L : MatR D)
    (hL : Formalism.MainNotions.S.IsLoUni L) (hT0 : ((Tu D u : ℕ) : D.host.E) ≠ 0) : Subgroup (GLR D) where
  carrier := stabAutSet D u u' F0 what₂ t F' L
  one_mem' := by
    refine ⟨1, ⟨nlam_one _ _, nlam_one _ _⟩, 1, act_one _, ?_⟩
    rw [Units.val_one, Matrix.conjTranspose_one, Matrix.mul_one,
      Matrix.nonsing_inv_mul _ (by rw [Formalism.L2.SG.Pf.StabilizerIndexVolumes.lo_det hL]; exact isUnit_one)]
  mul_mem' := by
    rintro x y ⟨s₁, ⟨h1F, h1F'⟩, uu₁, hu₁, hx⟩ ⟨s₂, ⟨h2F, h2F'⟩, uu₂, hu₂, hy⟩
    refine ⟨s₂ * s₁, ⟨Formalism.L2.SG.Pf.nlamPf_mul h2F h1F, Formalism.L2.SG.Pf.nlamPf_mul h2F' h1F'⟩, uu₂ * uu₁,
      act_mul _ _ _ _ _ hu₂ hu₁, ?_⟩
    have hLL : L * L⁻¹ = 1 := Matrix.mul_nonsing_inv _ (by rw [Formalism.L2.SG.Pf.StabilizerIndexVolumes.lo_det hL]; exact isUnit_one)
    rw [Units.val_mul, hx, hy, Matrix.conjTranspose_mul]
    calc L⁻¹ * uu₁.conjTranspose * L * (L⁻¹ * uu₂.conjTranspose * L) =
        L⁻¹ * uu₁.conjTranspose * (L * L⁻¹) * uu₂.conjTranspose * L := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hLL, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  inv_mem' := by
    rintro x ⟨s, ⟨hF, hF'⟩, uu, hu, hx⟩

    obtain ⟨⟨⟨hiso, _⟩, hf1, hf2⟩, _⟩ := And.intro hF hF'
    obtain ⟨uu0, huu0, hu0⟩ := Formalism.L2.SG.Pf.StabilizerIndexVolumes.tri_exists F0 s hf1 hf2
    have heq : uu = uu0 :=
      Formalism.L2.SG.Pf.StabilizerIndexVolumes.coef_unique (Formalism.L2.SG.Pf.StabilizerIndexVolumes.frame_indep F0 hT0) (fun b => s (F0.fvec b)) uu uu0 hu hu0
    subst heq
    refine ⟨s⁻¹, ⟨Formalism.L2.SG.Pf.nlamPf_inv hF, Formalism.L2.SG.Pf.nlamPf_inv hF'⟩, uu⁻¹, act_inv' _ _ _ huu0 hu, ?_⟩
    have hLd : IsUnit L.det := by rw [Formalism.L2.SG.Pf.StabilizerIndexVolumes.lo_det hL]; exact isUnit_one
    have hUd : IsUnit uu.conjTranspose.det := by
      rw [Formalism.L2.SG.Pf.StabilizerIndexVolumes.lo_det (Formalism.L2.SG.Pf.StabilizerIndexVolumes.lo_conjT huu0)]; exact isUnit_one
    rw [Matrix.coe_units_inv, hx, Matrix.conjTranspose_nonsing_inv]
    refine Matrix.inv_eq_left_inv ?_
    calc L⁻¹ * (uu.conjTranspose)⁻¹ * L * (L⁻¹ * uu.conjTranspose * L) =
        L⁻¹ * ((uu.conjTranspose)⁻¹ * (L * L⁻¹) * uu.conjTranspose) * L := by simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [Matrix.mul_nonsing_inv _ hLd, Matrix.mul_one, Matrix.nonsing_inv_mul _ hUd, Matrix.mul_one,
          Matrix.nonsing_inv_mul _ hLd]

theorem mem_stabAut_iff (t : Term D u u' F0 what₂) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (L : MatR D)
    (hL : Formalism.MainNotions.S.IsLoUni L) (hT0 : ((Tu D u : ℕ) : D.host.E) ≠ 0) (a : GLR D) :
    a ∈ stabAut D u u' F0 what₂ t F' L ↔ a ∈ stabAutSet D u u' F0 what₂ t F' L := by
  have e : stabAut D u u' F0 what₂ t F' L = stabAutG u u' F0 what₂ t F' L hL hT0 :=
    Subgroup.closure_eq (stabAutG u u' F0 what₂ t F' L hL hT0)
  rw [e]
  rfl

end Formalism.L2.SG.Pf.ZsVolFib

end
end

noncomputable section

namespace Formalism.L2.SG.Pf.ZsVolFib

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.PairVal Matrix
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

theorem mem_orth_of {T : D.host.E} (F : FlagG (VS D) D.R.rS T) (x : (VS D).V) (hx : ∀ i, (VS D).hT (F.e i) x = 0) :
    x ∈ orth (VS D) F.X := by
  unfold orth
  refine Submodule.mem_iInf _ |>.2 fun y => Submodule.mem_iInf _ |>.2 fun hy => ?_
  rw [LinearMap.mem_ker]
  induction hy using Submodule.span_induction with
  | mem z hz => obtain ⟨i, rfl⟩ := hz; exact hx i
  | zero => simp
  | add y z _ _ hy hz => rw [map_add (f := _), LinearMap.add_apply, hy, hz, add_zero]
  | smul c y _ hy => rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hy, smul_zero]

theorem orth_e {T : D.host.E} (F : FlagG (VS D) D.R.rS T) (x : (VS D).V) (hx : x ∈ orth (VS D) F.X) (i : Fin D.R.rS) :
    (VS D).hT (F.e i) x = 0 := by
  unfold orth at hx
  have h := (Submodule.mem_iInf _ |>.1 hx) (F.e i)
  have h2 := (Submodule.mem_iInf _ |>.1 h) (Submodule.subset_span ⟨i, rfl⟩)
  exact LinearMap.mem_ker.1 h2

theorem img_quot (L a₁ a₂ : MatR D) (hL : IsUnit L.det) (ha₁ : IsUnit a₁.det) (x₁ x₂ : GLR D)
    (hx₁ : (x₁ : MatR D) = L⁻¹ * a₁ * L) (hx₂ : (x₂ : MatR D) = L⁻¹ * a₂ * L) :
    ((x₁⁻¹ * x₂ : GLR D) : MatR D) = L⁻¹ * (a₂.conjTranspose * (a₁.conjTranspose)⁻¹).conjTranspose * L := by
  have hinv : ((x₁⁻¹ : GLR D) : MatR D) = L⁻¹ * a₁⁻¹ * L := by
    rw [Matrix.coe_units_inv, hx₁]
    refine Matrix.inv_eq_left_inv ?_
    calc L⁻¹ * a₁⁻¹ * L * (L⁻¹ * a₁ * L) = L⁻¹ * (a₁⁻¹ * (L * L⁻¹) * a₁) * L := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [Matrix.mul_nonsing_inv _ hL, Matrix.mul_one, Matrix.nonsing_inv_mul _ ha₁, Matrix.mul_one,
          Matrix.nonsing_inv_mul _ hL]
  rw [Units.val_mul, hinv, hx₂, Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv,
    Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_conjTranspose]
  calc L⁻¹ * a₁⁻¹ * L * (L⁻¹ * a₂ * L) = L⁻¹ * a₁⁻¹ * (L * L⁻¹) * a₂ * L := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [Matrix.mul_nonsing_inv _ hL, Matrix.mul_one]; simp only [Matrix.mul_assoc]

theorem act_quot (f : Fin (D.R.rS + 1) → (VS D).V) (t m₁ m₂ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (V₁ V₂ : MatR D)
    (hV₁ : IsUpUni V₁) (h₁ : ∀ b, m₁ (f b) = ∑ c, V₁ c b • f c) (h₂ : ∀ b, m₂ (f b) = ∑ c, V₂ c b • f c)
    (ht : ∀ b, t (m₁ (f b)) = m₂ (f b)) (b : Fin (D.R.rS + 1)) : t (f b) = ∑ c, (V₂ * V₁⁻¹) c b • f c := by
  have e : t = t * m₁ * m₁⁻¹ := (mul_inv_cancel_right t m₁).symm
  rw [e]
  exact act_mul f (t * m₁) m₁⁻¹ V₂ V₁⁻¹ (fun b => by show t (m₁ (f b)) = _; rw [ht, h₂]) (act_inv' f m₁ V₁ hV₁ h₁) b

end Formalism.L2.SG.Pf.ZsVolFib

end
