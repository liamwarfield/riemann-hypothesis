module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.DetAddCor
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.CoordLHolds

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.MemSpanOfSharpG
noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
variable {r : ℕ}

def GoodG (g : SplitG M.L) (t : Term V M r) : Prop :=
  M.split = some g ∧ Formalism.MainNotions.ThinScalesBound.FrameK H t.f t.T ∧ Formalism.MainNotions.ThinScalesBound.FrameK H t.f' t.T' ∧
    IsUnit (H.Dl t.f t.f' (r + 1)) ∧ IsUnit (gramH H (H.MMfam t)).det

theorem q_ne (g : SplitG M.L) : (g.q : F) ≠ 0 := by
  intro h
  exact g.q_irr.ne_zero (by exact_mod_cast h)

theorem qi_mul_q (g : SplitG M.L) :
    algebraMap F E ((g.q : F)⁻¹) * algebraMap F E (g.q : F) = 1 := by
  rw [← map_mul, inv_mul_cancel₀ (q_ne g), map_one]

theorem cj_alg (a : F) : M.L.cj (algebraMap F E a) = algebraMap F E a := M.L.cj.commutes a

theorem mmfam_some {g : SplitG M.L} (hs : M.split = some g) (t : Term V M r) :
    H.MMfam t = Sum.elim t.f (fun a => algebraMap F E ((g.q : F)⁻¹) • (t.f' a - t.f a)) := by
  simp only [HermSp.MMfam, hs]

theorem h_sub_right (x y y' : V) : H.h x (y - y') = H.h x y - H.h x y' := by
  have h1 : H.h (y - y') x = H.h y x - H.h y' x := by
    have h2 := H.h_add_left (y - y') y' x
    rw [sub_add_cancel] at h2
    rw [h2]
    ring
  rw [H.h_herm (y - y') x, h1, map_sub, ← H.h_herm, ← H.h_herm]

theorem gramH_eqG {g : SplitG M.L} {t : Term V M r} (hg : GoodG H g t) :
    gramH H (H.MMfam t) = gramG (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) (H.Zhat t.f t.f')
      (algebraMap F E t.T) (algebraMap F E t.T') := by
  obtain ⟨hs, hF, hF', -, -⟩ := hg
  have hff : ∀ a b, H.h (t.f a) (t.f b) = cor r a b (-algebraMap F E t.T) := by
    intro a b
    unfold cor
    split_ifs with h
    · rw [h.1, h.2]
      exact hF.2
    · exact hF.1 a b (by tauto)
  have hf'f' : ∀ a b, H.h (t.f' a) (t.f' b) = cor r a b (-algebraMap F E t.T') := by
    intro a b
    unfold cor
    split_ifs with h
    · rw [h.1, h.2]
      exact hF'.2
    · exact hF'.1 a b (by tauto)
  have hZ : ∀ a b, H.Zhat t.f t.f' a b = H.h (t.f' b) (t.f a) := fun a b => rfl
  have hZc : ∀ a b, (M.L.cj : E →+* E) (H.Zhat t.f t.f' a b) = H.h (t.f a) (t.f' b) := fun a b => by
    show M.L.cj (H.Zhat t.f t.f' a b) = _
    rw [hZ, ← H.h_herm]
  have hsr : ∀ (c : E) (x y : V), H.h x (c • y) = M.L.cj c * H.h x y := fun c x y => by
    rw [H.h_herm, H.h_smul_left, map_mul, ← H.h_herm]
  have hsl : ∀ (x y z : V), H.h (x - y) z = H.h x z - H.h y z := fun x y z => by
    have h2 := H.h_add_left (x - y) y z
    rw [sub_add_cancel] at h2
    rw [h2]
    ring
  rw [mmfam_some H hs]
  ext i j
  rcases i with a | a <;> rcases j with b | b
  · simp only [gramH, Matrix.of_apply, Sum.elim_inl, gramG, Matrix.fromBlocks_apply₁₁]
    exact hff a b
  · simp only [gramH, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr, gramG, Matrix.fromBlocks_apply₁₂]
    rw [hsr, cj_alg, h_sub_right, hff, hZc]
    unfold cor
    split_ifs <;> ring
  · simp only [gramH, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr, gramG, Matrix.fromBlocks_apply₂₁]
    rw [H.h_smul_left, hsl, hff, hZ]
    unfold cor
    split_ifs <;> ring
  · simp only [gramH, Matrix.of_apply, Sum.elim_inr, gramG, Matrix.fromBlocks_apply₂₂]
    rw [H.h_smul_left, hsr, cj_alg, hsl, h_sub_right, h_sub_right, hf'f', hff, hZc, hZ]
    unfold cor
    split_ifs <;> ring

theorem gramH_comb {ι : Type} [Fintype ι] (B : Matrix ι ι E) (v : ι → V) :
    gramH H (fun i => ∑ j, B i j • v j) = B * gramH H v * (B.map M.L.cj).transpose := by
  classical
  have hsl : ∀ (s : Finset ι) (f : ι → V) (y : V), H.h (∑ i ∈ s, f i) y = ∑ i ∈ s, H.h (f i) y := by
    intro s f y
    induction s using Finset.induction_on with
    | empty =>
      have h0 := H.h_smul_left 0 0 y
      simpa using h0
    | @insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, H.h_add_left, ih]
  have hsr : ∀ (x : V) (s : Finset ι) (f : ι → V), H.h x (∑ i ∈ s, f i) = ∑ i ∈ s, H.h x (f i) := by
    intro x s f
    set_option synthInstance.maxHeartbeats 100000 in
      rw [H.h_herm (∑ i ∈ s, f i) x, hsl, map_sum]
    simp_rw [← H.h_herm]
  have hsmr : ∀ (a : E) (x y : V), H.h x (a • y) = M.L.cj a * H.h x y := by
    intro a x y
    rw [H.h_herm (a • y) x, H.h_smul_left, map_mul, ← H.h_herm]
  ext i k
  simp only [gramH, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, hsl, H.h_smul_left,
    hsr, hsmr, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun l _ => by ring))

theorem unit_gramH_of {g : SplitG M.L} (hs : M.split = some g) {t : Term V M r}
    (hF : Formalism.MainNotions.ThinScalesBound.FrameK H t.f t.T) (hF' : Formalism.MainNotions.ThinScalesBound.FrameK H t.f' t.T')
    (hD1 : IsUnit (H.Dl t.f t.f' (r + 1))) (hD0 : H.Dl t.f t.f' r = 0) :
    IsUnit (gramH H (H.MMfam t)).det := by
  set qi := algebraMap F E ((g.q : F)⁻¹) with hqi
  let B : Matrix (Ix r) (Ix r) E := Matrix.fromBlocks 1 0 (-qi • (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E))
    (qi • (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E))
  have hfam : H.MMfam t = fun i => ∑ j, B i j • Sum.elim t.f t.f' j := by
    rw [mmfam_some H hs]
    funext i
    rcases i with a | a
    · simp [B, Fintype.sum_sum_type, Matrix.one_apply]
    · simp [B, Fintype.sum_sum_type, Matrix.one_apply, sub_eq_add_neg, add_comm, neg_smul]
      rfl
  have hqu : IsUnit qi := by
    refine ⟨⟨qi, algebraMap F E (g.q : F), qi_mul_q g, ?_⟩, rfl⟩
    rw [mul_comm]; exact qi_mul_q g
  have hB : IsUnit B.det := by
    simp only [B]
    rw [Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, one_mul, Matrix.det_smul, Matrix.det_one, mul_one]
    exact hqu.pow _
  have hV : gramH H (Sum.elim t.f t.f') = gramC (M.L.cj : E →+* E) (H.Zhat t.f t.f')
      (algebraMap F E t.T) (algebraMap F E t.T') := by
    rw [gramC_eq H _ _ _ _ hF hF']
    ext i j; rfl
  have hG := unit_gramC H _ _ _ _ hF hF' hD1 hD0
  rw [hfam, gramH_comb, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hV]
  have hBc : IsUnit (B.map M.L.cj).det := by
    have : (B.map M.L.cj).det = M.L.cj B.det := by
      rw [show (B.map M.L.cj) = (M.L.cj : E →+* E).mapMatrix B from rfl, ← RingHom.map_det]; rfl
    rw [this]; exact hB.map _
  exact (hB.mul hG).mul hBc

theorem unit_gramHG {g : SplitG M.L} {t : Term V M r} (hg : GoodG H g t) :
    IsUnit (gramH H (H.MMfam t)).det := hg.2.2.2.2

theorem relSub_eqG {g : SplitG M.L} {t : Term V M r} (hg : GoodG H g t) :
    relSub H t = relG M.L.O (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) (H.Zhat t.f t.f')
      (algebraMap F E t.T) (algebraMap F E t.T') := by
  have e : ∀ i j, H.h (H.MMfam t i) (H.MMfam t j) = gramG (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹))
      (H.Zhat t.f t.f') (algebraMap F E t.T) (algebraMap F E t.T') i j := by
    intro i j
    rw [← gramH_eqG H hg]
    rfl
  ext y
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, fun j => by rw [hc j]; simp only [e]⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, fun j => by rw [hc j]; simp only [e]⟩

def PsiG {g : SplitG M.L} {t : Term V M r} (hg : GoodG H g t) :
    DDt H t ≃ₗ[M.L.O] DDg M.L.O (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) (H.Zhat t.f t.f')
      (algebraMap F E t.T) (algebraMap F E t.T') :=
  (ddEquiv H t (unit_gramHG H hg)).trans (Submodule.quotEquivOfEq _ _ (relSub_eqG H hg))

theorem PsiG_mk {g : SplitG M.L} {t : Term V M r} (hg : GoodG H g t) (u : ↥(MMsharp H t)) :
    PsiG H hg (ddMk H t u) = Submodule.Quotient.mk (sharpEquiv H t (unit_gramHG H hg) u) := rfl

theorem PsiG_symm_mk {g : SplitG M.L} {t : Term V M r} (hg : GoodG H g t) (Y : Ix r → M.L.O) :
    (PsiG H hg).symm (Submodule.Quotient.mk Y) =
      ddMk H t ((sharpEquiv H t (unit_gramHG H hg)).symm Y) := by
  rw [LinearEquiv.symm_apply_eq, PsiG_mk, LinearEquiv.apply_symm_apply]

theorem h_eq_formG {g : SplitG M.L} {t : Term V M r} (hg : GoodG H g t) (u w : ↥(MMsharp H t)) :
    H.h u w = formG M.L.O (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) (H.Zhat t.f t.f')
      (algebraMap F E t.T) (algebraMap F E t.T') (sharpEquiv H t (unit_gramHG H hg) u)
      (sharpEquiv H t (unit_gramHG H hg) w) := by
  rw [h_eq_form H (H.MMfam t) (unit_gramHG H hg) u w ((mem_MMsharp_iff H t u).1 u.2).1]
  unfold formG
  rw [← gramH_eqG H hg]
  simp only [sharpEquiv_apply]
  rfl

theorem sharpG_inl {g : SplitG M.L} {t : Term V M r} (hg : GoodG H g t) (u : ↥(MMsharp H t))
    (a : Fin (r + 1)) : (sharpEquiv H t (unit_gramHG H hg) u (Sum.inl a) : E) = H.h u (t.f a) := by
  rw [sharpEquiv_apply, mmfam_some H hg.1]
  rfl

theorem sharpG_inr {g : SplitG M.L} {t : Term V M r} (hg : GoodG H g t) (u : ↥(MMsharp H t))
    (a : Fin (r + 1)) : (sharpEquiv H t (unit_gramHG H hg) u (Sum.inr a) : E) =
      algebraMap F E ((g.q : F)⁻¹) * (H.h u (t.f' a) - H.h u (t.f a)) := by
  rw [sharpEquiv_apply, mmfam_some H hg.1]
  simp only [Sum.elim_inr]
  rw [H.h_herm, H.h_smul_left, map_mul, ← H.h_herm, cj_alg, h_sub_right]

theorem sharpG_f' {g : SplitG M.L} {t : Term V M r} (hg : GoodG H g t) (u : ↥(MMsharp H t))
    (a : Fin (r + 1)) : H.h u (t.f' a) = (sharpEquiv H t (unit_gramHG H hg) u (Sum.inl a) : E) +
      algebraMap F E (g.q : F) * (sharpEquiv H t (unit_gramHG H hg) u (Sum.inr a) : E) := by
  rw [sharpG_inl H hg, sharpG_inr H hg, ← mul_assoc, mul_comm (algebraMap F E (g.q : F)), qi_mul_q g, one_mul]
  ring

theorem mem_span_of_sharpG {g : SplitG M.L} {t : Term V M r} (hg : GoodG H g t) (u : ↥(MMsharp H t)) :
    (u : V) ∈ Submodule.span E (Set.range (Sum.elim t.f t.f')) := by
  have h1 := ((mem_MMsharp_iff H t u).1 u.2).1
  rw [mmfam_some H hg.1] at h1
  refine Submodule.span_le.2 ?_ h1
  rintro _ ⟨i, rfl⟩
  rcases i with a | a
  · exact Submodule.subset_span ⟨Sum.inl a, rfl⟩
  · simp only [Sum.elim_inr]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.subset_span ⟨Sum.inr a, rfl⟩)
      (Submodule.subset_span ⟨Sum.inl a, rfl⟩))

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
end
end

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem idem_mem_O (L : LocE F E) {x : E} (hx : x * x = x) : x ∈ L.O := by
  rw [L.O_def]
  refine ⟨Polynomial.X ^ 2 - Polynomial.X, Polynomial.monic_X_pow_sub (by rw [Polynomial.degree_X]; norm_num), ?_⟩
  simp [Polynomial.eval₂_sub, sq, hx]

theorem mem_O_of_comp {M : Model F E} (g : SplitG M.L) (x : E) (h1 : (g.e x).1 ∈ 𝒪[F])
    (h2 : (g.e x).2 ∈ 𝒪[F]) : x ∈ M.L.O := by
  rw [M.L.O_def]
  have hx : x = ((g.e x).1 : F) • g.e.symm (1, 0) + ((g.e x).2 : F) • g.e.symm (0, 1) := by
    apply g.e.injective
    simp only [map_add (f := _), map_smul, AlgEquiv.apply_symm_apply, Prod.smul_mk, smul_eq_mul, mul_one, mul_zero,
      Prod.mk_add_mk, add_zero, zero_add]
  have hid : ∀ y : F × F, y * y = y → IsIntegral 𝒪[F] (g.e.symm y) := by
    intro y hy
    refine ⟨Polynomial.X ^ 2 - Polynomial.X, Polynomial.monic_X_pow_sub (by simp), ?_⟩
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_X]
    rw [sq, ← map_mul, hy, sub_self]
  have hsc : ∀ (c : F) (hc : c ∈ 𝒪[F]) (y : E), IsIntegral 𝒪[F] y → IsIntegral 𝒪[F] (c • y) := by
    intro c hc y hy
    have e : c • y = algebraMap 𝒪[F] E ⟨c, hc⟩ * y := by
      rw [Algebra.smul_def]
      rfl
    rw [e]
    exact (isIntegral_algebraMap).mul hy
  rw [hx]
  exact (hsc _ h1 _ (hid (1, 0) (by simp))).add (hsc _ h2 _ (hid (0, 1) (by simp)))

theorem comp_of_mem_R {M : Model F E} {g : SplitG M.L} (hs : M.split = some g) {x : E} (hx : x ∈ M.R) :
    (g.e x).1 ∈ 𝒪[F] ∧ (g.e x).2 ∈ 𝒪[F] ∧ ∃ c : 𝒪[F], (g.e x).1 - (g.e x).2 = (g.q : F) * c := by
  unfold Model.R at hx
  simp only [hs, Subring.mem_comap, Subring.mem_map] at hx
  obtain ⟨p, hp, hpe⟩ := hx
  have e1 : (g.e x).1 = (p.1 : F) := by
    have := congrArg Prod.fst hpe
    simpa using this.symm
  have e2 : (g.e x).2 = (p.2 : F) := by
    have := congrArg Prod.snd hpe
    simpa using this.symm
  rw [RingHom.mem_eqLocus] at hp
  simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_fst, RingHom.coe_snd] at hp
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton'] at hp
  obtain ⟨c, hc⟩ := hp
  refine ⟨by rw [e1]; exact p.1.2, by rw [e2]; exact p.2.2, c, ?_⟩
  rw [e1, e2, mul_comm]
  exact_mod_cast hc.symm

variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
variable {r : ℕ}

theorem zz_comp {g : SplitG M.L} (hs : M.split = some g) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (T T' : F) (a b : Fin (r + 1)) :
    g.e (HermSp.ZZplusOf M Z T T' a b) =
      ((g.e (Z a b)).1 / (g.q : F) - (if a = Fin.last r ∧ b = Fin.last r then -T / (g.q : F) else 0),
       -((g.e (Z b a)).2 / (g.q : F)) - (if a = Fin.last r ∧ b = Fin.last r then T' / (g.q : F) else 0)) := by
  unfold HermSp.ZZplusOf
  rw [hs]
  simp only [Matrix.of_apply]
  split_ifs with h <;> simp [map_sub, h]

theorem mmInt_G {g : SplitG M.L} {t : Term V M r} (hg : GoodG H g t) (hT : t.T ∈ 𝒪[F])
    (hTT : ∃ c : 𝒪[F], t.T - t.T' = (g.q : F) ^ 2 * c)
    (hR : ∀ a b, HermSp.ZZplusOf M (H.Zhat t.f t.f') t.T t.T' a b ∈ M.R) : MMInt H t := by
  have hq := q_ne g
  obtain ⟨c0, hc0⟩ := hTT
  have hqO : (g.q : F) ∈ 𝒪[F] := g.q.2
  have hR' := fun a b => (zz_comp hg.1 (H.Zhat t.f t.f') t.T t.T' a b) ▸ comp_of_mem_R hg.1 (hR a b)
  have ecj : ∀ x : E, g.e ((M.L.cj : E →+* E) x) = (g.e x).swap := g.e_cj
  have eal : ∀ x : F, g.e (algebraMap F E x) = (x, x) := fun x => by
    rw [AlgEquiv.commutes]; rfl
  have hgen : ∀ i j, H.h (H.MMfam t i) (H.MMfam t j) ∈ M.L.O := by
    intro i j
    have := congrFun (congrFun (gramH_eqG H hg) i) j
    change H.h (H.MMfam t i) (H.MMfam t j) = _ at this
    rw [this]
    rcases i with a | a <;> rcases j with b | b
    · simp only [gramG, Matrix.fromBlocks_apply₁₁, Matrix.of_apply, cor]
      split_ifs
      · exact M.L.O.neg_mem (Formalism.MainNotions.LocalModelPeriodLattices.algebraMap_mem_O M.L ⟨t.T, hT⟩)
      · exact M.L.O.zero_mem
    · simp only [gramG, Matrix.fromBlocks_apply₁₂, Matrix.of_apply]
      obtain ⟨-, A2, -⟩ := hR' b a
      obtain ⟨A1, -, -⟩ := hR' a b
      apply mem_O_of_comp g
      · by_cases h : a = Fin.last r ∧ b = Fin.last r
        · obtain ⟨rfl, rfl⟩ := h
          simp only [cor, and_self, if_true] at A2 ⊢
          simp only [map_mul, map_add (f := _), ecj, eal, Prod.fst_mul, Prod.fst_add, Prod.fst_swap]
          convert add_mem (neg_mem A2) (mul_mem hqO c0.2) using 1
          field_simp
          linear_combination hc0
        · have h' : ¬(b = Fin.last r ∧ a = Fin.last r) := fun h'' => h ⟨h''.2, h''.1⟩
          simp only [cor, h, h', if_false] at A2 ⊢
          simp only [map_mul, map_add (f := _), ecj, eal, Prod.fst_mul, Prod.fst_add, Prod.fst_swap, map_zero,
            Prod.fst_zero, add_zero]
          convert neg_mem A2 using 1
          field_simp
          ring
      · by_cases h : a = Fin.last r ∧ b = Fin.last r
        · obtain ⟨rfl, rfl⟩ := h
          simp only [cor, and_self, if_true] at A1 ⊢
          simp only [map_mul, map_add (f := _), ecj, eal, Prod.snd_mul, Prod.snd_add, Prod.snd_swap]
          convert A1 using 1
          field_simp
          ring
        · simp only [cor, h, if_false] at A1 ⊢
          simp only [map_mul, map_add (f := _), ecj, eal, Prod.snd_mul, Prod.snd_add, Prod.snd_swap, map_zero,
            Prod.snd_zero, add_zero]
          convert A1 using 1
          field_simp
          ring
    · simp only [gramG, Matrix.fromBlocks_apply₂₁, Matrix.of_apply]
      obtain ⟨-, A2, -⟩ := hR' a b
      obtain ⟨A1, -, -⟩ := hR' b a
      apply mem_O_of_comp g
      · by_cases h : a = Fin.last r ∧ b = Fin.last r
        · obtain ⟨rfl, rfl⟩ := h
          simp only [cor, and_self, if_true] at A1 ⊢
          simp only [map_mul, map_add (f := _), eal, Prod.fst_mul, Prod.fst_add]
          convert A1 using 1
          field_simp
          ring
        · have h' : ¬(b = Fin.last r ∧ a = Fin.last r) := fun h'' => h ⟨h''.2, h''.1⟩
          simp only [cor, h, h', if_false] at A1 ⊢
          simp only [map_mul, map_add (f := _), eal, Prod.fst_mul, Prod.fst_add, map_zero, Prod.fst_zero, add_zero]
          convert A1 using 1
          field_simp
          ring
      · by_cases h : a = Fin.last r ∧ b = Fin.last r
        · obtain ⟨rfl, rfl⟩ := h
          simp only [cor, and_self, if_true] at A2 ⊢
          simp only [map_mul, map_add (f := _), eal, Prod.snd_mul, Prod.snd_add]
          convert add_mem (neg_mem A2) (mul_mem hqO c0.2) using 1
          field_simp
          linear_combination hc0
        · simp only [cor, h, if_false] at A2 ⊢
          simp only [map_mul, map_add (f := _), eal, Prod.snd_mul, Prod.snd_add, map_zero, Prod.snd_zero, add_zero]
          convert neg_mem A2 using 1
          field_simp
          ring
    · simp only [gramG, Matrix.fromBlocks_apply₂₂, Matrix.of_apply]
      obtain ⟨-, -, c, A3⟩ := hR' b a
      obtain ⟨-, -, c', A3'⟩ := hR' a b
      apply mem_O_of_comp g
      · by_cases h : a = Fin.last r ∧ b = Fin.last r
        · obtain ⟨rfl, rfl⟩ := h
          simp only [cor, and_self, if_true] at A3 ⊢
          simp only [map_mul, map_add (f := _), map_sub, map_neg, ecj, eal, Prod.fst_mul, Prod.fst_add,
            Prod.fst_sub, Prod.fst_neg, Prod.fst_swap]
          convert neg_mem c.2 using 1
          field_simp at A3 ⊢
          first | linear_combination A3 | linear_combination -A3 | linear_combination (g.q : F) * A3 | linear_combination -(g.q : F) * A3
        · have h' : ¬(b = Fin.last r ∧ a = Fin.last r) := fun h'' => h ⟨h''.2, h''.1⟩
          simp only [cor, h, h', if_false] at A3 ⊢
          simp only [map_mul, map_add (f := _), map_sub, map_neg, ecj, eal, Prod.fst_mul, Prod.fst_add,
            Prod.fst_sub, Prod.fst_neg, Prod.fst_swap, map_zero, Prod.fst_zero, sub_zero]
          convert neg_mem c.2 using 1
          field_simp at A3 ⊢
          first | linear_combination A3 | linear_combination -A3 | linear_combination (g.q : F) * A3 | linear_combination -(g.q : F) * A3
      · by_cases h : a = Fin.last r ∧ b = Fin.last r
        · obtain ⟨rfl, rfl⟩ := h
          simp only [cor, and_self, if_true] at A3' ⊢
          simp only [map_mul, map_add (f := _), map_sub, map_neg, ecj, eal, Prod.snd_mul, Prod.snd_add,
            Prod.snd_sub, Prod.snd_neg, Prod.snd_swap]
          convert neg_mem c'.2 using 1
          field_simp at A3' ⊢
          first | linear_combination A3' | linear_combination -A3' | linear_combination (g.q : F) * A3' | linear_combination -(g.q : F) * A3'
        · simp only [cor, h, if_false] at A3' ⊢
          simp only [map_mul, map_add (f := _), map_sub, map_neg, ecj, eal, Prod.snd_mul, Prod.snd_add,
            Prod.snd_sub, Prod.snd_neg, Prod.snd_swap, map_zero, Prod.snd_zero, sub_zero]
          convert neg_mem c'.2 using 1
          field_simp at A3' ⊢
          first | linear_combination A3' | linear_combination -A3' | linear_combination (g.q : F) * A3' | linear_combination -(g.q : F) * A3'
  have h1 : ∀ i, ∀ m' ∈ MMo H t, H.h (H.MMfam t i) m' ∈ M.L.O := by
    intro i m' hm'
    unfold MMo at hm'
    induction hm' using Submodule.span_induction with
    | mem x hx => obtain ⟨j, rfl⟩ := hx; exact hgen i j
    | zero => rw [h_zero_right]; exact M.L.O.zero_mem
    | add x y _ _ hx hy => rw [h_add_right]; exact M.L.O.add_mem hx hy
    | smul a x _ hx =>
      rw [Subring.smul_def, h_smul_right]; exact M.L.O.mul_mem (cj_mem_O M.L a.2) hx
  intro m hm m' hm'
  unfold MMo at hm
  induction hm using Submodule.span_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact h1 i m' hm'
  | zero => rw [H.h_zero_left]; exact M.L.O.zero_mem
  | add x y _ _ hx hy => rw [H.h_add_left]; exact M.L.O.add_mem hx hy
  | smul a x _ hx => rw [Subring.smul_def, H.h_smul_left]; exact M.L.O.mul_mem a.2 hx

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
