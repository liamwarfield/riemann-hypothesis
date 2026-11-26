module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.LevelSAllOfHL
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.LeviPartAll

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.HeisenbergParabolicAll
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.UnipotentRadicalActionFormula
noncomputable section

namespace PI.LevelKSplit.W.NCH

open PI.VolSemiDirect.W.PG PI.VolSemiDirect.W.PG.Dat

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}

def Xp (D : Dat A n r) (v : n → A) : Prop := ∀ a, D.h (D.e a) v = 0

def IsWp (D : Dat A n r) (w : n → A) : Prop :=
  (∀ a, D.h (D.e a) w = 0) ∧ ∀ a, D.h (D.f a) w = 0

def pWp (D : Dat A n r) : (n → A) →ₗ[A] (n → A) := LinearMap.id - D.pX - D.pXv

structure Half (D : Dat A n r) (half : A) : Prop where
  two : half + half = 1
  sig : D.σA half = half

def cf (D : Dat A n r) (half : A) (y : Fin r → n → A) (a b : Fin r) : A :=
  -(half * D.h (y b) (y a))

def uv (D : Dat A n r) (half : A) (y : Fin r → n → A) (a : Fin r) : n → A :=
  y a + ∑ b, cf D half y a b • D.e b

def sL (D : Dat A n r) (half : A) (y : Fin r → n → A) : (n → A) →ₗ[A] (n → A) :=
  LinearMap.id + ∑ a, (D.hL (D.e a)).smulRight (uv D half y a) -
    ∑ b, (D.hL (y b)).smulRight (D.e b)

def tV (D : Dat A n r) (half : A) (y : Fin r → n → A) (v : n → A) : n → A :=
  ∑ a, D.h (D.e a) v • uv D half y a - ∑ b, D.h (y b) v • D.e b

private theorem hLap_lemma (D : Dat A n r) (x v : n → A) : D.hL x v = D.h x v := rfl

theorem sL_apply (D : Dat A n r) (half : A) (y : Fin r → n → A) (v : n → A) :
    sL D half y v = v + ∑ a, D.h (D.e a) v • uv D half y a - ∑ b, D.h (y b) v • D.e b := by
  simp only [sL, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.id_apply,
    LinearMap.sum_apply, LinearMap.smulRight_apply, hLap_lemma]

theorem sL_eq (D : Dat A n r) (half : A) (y : Fin r → n → A) (v : n → A) :
    sL D half y v = v + tV D half y v := by
  simp only [sL_apply, tV, add_sub_assoc]

theorem pWp_apply (D : Dat A n r) (v : n → A) : pWp D v = v - D.pX v - D.pXv v := rfl

variable {D : Dat A n r}

private theorem hRadd_lemma_2 (x y y' : n → A) : D.h x (y + y') = D.h x y + D.h x y' := by
  show (D.hL x) (y + y') = (D.hL x) y + (D.hL x) y'
  exact map_add _ _ _

private theorem hRsub_lemma_3 (x y y' : n → A) : D.h x (y - y') = D.h x y - D.h x y' := by
  show (D.hL x) (y - y') = (D.hL x) y - (D.hL x) y'
  exact map_sub _ _ _

private theorem hRsmul_lemma_4 (x y : n → A) (c : A) : D.h x (c • y) = c * D.h x y := by
  show (D.hL x) (c • y) = c * (D.hL x) y
  rw [map_smul, smul_eq_mul]

private theorem hRsum_lemma_5 (x : n → A) (g : Fin r → n → A) :
    D.h x (∑ i, g i) = ∑ i, D.h x (g i) := by
  show (D.hL x) (∑ i, g i) = ∑ i, (D.hL x) (g i)
  exact map_sum _ _ _

private theorem hswap_lemma_6 (H : D.Hyp) (x y : n → A) : D.h y x = D.σA (D.h x y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Dat.h, Formalism.UG.hform, map_sum, map_mul, H.σσ, H.herm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

private theorem hfe_lemma_7 (H : D.Hyp) (a b : Fin r) :
    D.h (D.f a) (D.e b) = if a = b then 1 else 0 := by
  rw [hswap_lemma_6 H (D.e b) (D.f a), H.ef b a]
  by_cases hab : a = b
  · subst hab; simp
  · simp [hab, Ne.symm hab]

private theorem hLsum_lemma_8 (H : D.Hyp) (g : Fin r → n → A) (y : n → A) :
    D.h (∑ i, g i) y = ∑ i, D.h (g i) y := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hswap_lemma_6 H, hRsum_lemma_5, map_sum]
  exact Finset.sum_congr rfl fun i _ => (hswap_lemma_6 H _ _).symm

private theorem hLsub_lemma_9 (H : D.Hyp) (x x' y : n → A) :
    D.h (x - x') y = D.h x y - D.h x' y := by
  rw [hswap_lemma_6 H y (x - x'), hRsub_lemma_3, map_sub, ← hswap_lemma_6 H, ← hswap_lemma_6 H]

private theorem pXap_lemma_10 (v : n → A) : D.pX v = ∑ a, D.h (D.f a) v • D.e a := by
  simp only [Dat.pX, LinearMap.sum_apply, LinearMap.smulRight_apply, hLap_lemma]

private theorem pXvap_lemma_11 (v : n → A) : D.pXv v = ∑ a, D.h (D.e a) v • D.f a := by
  simp only [Dat.pXv, LinearMap.sum_apply, LinearMap.smulRight_apply, hLap_lemma]

theorem h_W_e' (H : D.Hyp) {w : n → A} (hw : IsWp D w) (b : Fin r) : D.h w (D.e b) = 0 := by
  unfold IsWp at hw
  rw [hswap_lemma_6 H, hw.1 b, map_zero]

theorem h_W_f' (H : D.Hyp) {w : n → A} (hw : IsWp D w) (b : Fin r) : D.h w (D.f b) = 0 := by
  unfold IsWp at hw
  rw [hswap_lemma_6 H, hw.2 b, map_zero]

theorem xp_of_span (H : D.Hyp) {x : n → A} (hx : x ∈ Submodule.span A (Set.range D.e)) : Xp D x := by
  rw [Submodule.mem_span_range_iff_exists_fun] at hx
  obtain ⟨c, rfl⟩ := hx
  intro a
  simp [hRsum_lemma_5, hRsmul_lemma_4, H.ee]

theorem h_W_span' (H : D.Hyp) {w : n → A} (hw : IsWp D w) {x : n → A}
    (hx : x ∈ Submodule.span A (Set.range D.e)) : D.h w x = 0 := by
  rw [Submodule.mem_span_range_iff_exists_fun] at hx
  obtain ⟨c, rfl⟩ := hx
  simp [hRsum_lemma_5, hRsmul_lemma_4, h_W_e' H hw]

theorem xp_add {v w : n → A} (hv : Xp D v) (hw : Xp D w) : Xp D (v + w) := by
  intro a
  rw [hRadd_lemma_2, hv a, hw a, add_zero]

theorem xp_sub_pXv (H : D.Hyp) (v : n → A) : Xp D (v - D.pXv v) := by
  intro a
  rw [hRsub_lemma_3, pXvap_lemma_11, hRsum_lemma_5]
  simp [hRsmul_lemma_4, H.ef]

theorem xp_e (H : D.Hyp) (c : Fin r) : Xp D (D.e c) := by
  intro a
  exact H.ee a c

theorem pWp_isWp (H : D.Hyp) (v : n → A) : IsWp D (pWp D v) := by
  unfold IsWp
  refine ⟨fun a => ?_, fun a => ?_⟩ <;>
    simp [pWp_apply, pXap_lemma_10, pXvap_lemma_11, hRsub_lemma_3, hRsum_lemma_5, hRsmul_lemma_4, H.ee, H.ff, H.ef,
      hfe_lemma_7 H]

theorem pWp_of_isWp {w : n → A} (hw : IsWp D w) : pWp D w = w := by
  unfold IsWp at hw
  obtain ⟨h1, h2⟩ := hw
  simp [pWp_apply, pXap_lemma_10, pXvap_lemma_11, h1, h2]

theorem pWp_span (H : D.Hyp) {x : n → A} (hx : x ∈ Submodule.span A (Set.range D.e)) :
    pWp D x = 0 := by
  rw [Submodule.mem_span_range_iff_exists_fun] at hx
  obtain ⟨c, rfl⟩ := hx
  simp [pWp_apply, pXap_lemma_10, pXvap_lemma_11, hRsum_lemma_5, hRsmul_lemma_4, H.ee, hfe_lemma_7 H]

theorem pWp_e (H : D.Hyp) (c : Fin r) : pWp D (D.e c) = 0 := pWp_span H (Submodule.subset_span ⟨c, rfl⟩)

theorem pWp_f (H : D.Hyp) (c : Fin r) : pWp D (D.f c) = 0 := by
  simp [pWp_apply, pXap_lemma_10, pXvap_lemma_11, H.ff, H.ef]

private theorem hy1_lemma_12 {y : Fin r → n → A} (hy : ∀ a, IsWp D (y a)) (a b : Fin r) :
    D.h (D.e b) (y a) = 0 := by
  have h1 := hy a
  unfold IsWp at h1
  exact h1.1 b

private theorem hy2_lemma_13 (H : D.Hyp) {y : Fin r → n → A} (hy : ∀ a, IsWp D (y a)) (a b : Fin r) :
    D.h (y a) (D.e b) = 0 :=
  h_W_e' H (hy a) b

private theorem hy3_lemma_14 (H : D.Hyp) {y : Fin r → n → A} (hy : ∀ a, IsWp D (y a)) (a b : Fin r) :
    D.h (y a) (D.f b) = 0 :=
  h_W_f' H (hy a) b

theorem ext_Xp_f (H : D.Hyp) {Φ Ψ : (n → A) →ₗ[A] (n → A)} (h1 : ∀ v, Xp D v → Φ v = Ψ v)
    (h2 : ∀ a, Φ (D.f a) = Ψ (D.f a)) (v : n → A) : Φ v = Ψ v := by
  have e1 : v = (v - D.pXv v) + D.pXv v := (sub_add_cancel v _).symm
  rw [e1, map_add (f := _), map_add (f := _), h1 _ (xp_sub_pXv H v)]
  congr 1
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [pXvap_lemma_11, map_sum, map_smul, h2]

section Sec

variable (H : D.Hyp) {half : A} {y : Fin r → n → A} (hy : ∀ a, IsWp D (y a))
include H hy

theorem h_e_uv (a c : Fin r) : D.h (D.e c) (uv D half y a) = 0 := by
  simp [uv, hRadd_lemma_2, hRsum_lemma_5, hRsmul_lemma_4, H.ee, hy1_lemma_12 hy]

theorem h_uv_e (a c : Fin r) : D.h (uv D half y a) (D.e c) = 0 := by
  rw [hswap_lemma_6 H, h_e_uv H hy, map_zero]

theorem h_uv_uv (a a' : Fin r) : D.h (uv D half y a) (uv D half y a') = D.h (y a) (y a') := by
  simp [uv, hRadd_lemma_2, hRsum_lemma_5, hRsmul_lemma_4, h_add_left, hLsum_lemma_8 H, h_smul_left, H.ee,
    hy1_lemma_12 hy, hy2_lemma_13 H hy]

theorem sL_e (c : Fin r) : sL D half y (D.e c) = D.e c := by
  simp [sL_apply, H.ee, hy2_lemma_13 H hy]

theorem sL_f (c : Fin r) : sL D half y (D.f c) = D.f c + uv D half y c := by
  simp [sL_apply, H.ef, hy3_lemma_14 H hy]

theorem sL_Xp {v : n → A} (hv : Xp D v) : sL D half y v = v - ∑ b, D.h (y b) v • D.e b := by
  have hv' : ∀ a, D.h (D.e a) v = 0 := hv
  simp [sL_apply, hv']

theorem sL_span {x : n → A} (hx : x ∈ Submodule.span A (Set.range D.e)) : sL D half y x = x := by
  rw [sL_Xp H hy (xp_of_span H hx)]
  have hz : ∀ b, D.h (y b) x = 0 := fun b => h_W_span' H (hy b) hx
  simp [hz]

theorem pWp_sL_f (c : Fin r) : pWp D (sL D half y (D.f c)) = y c := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [sL_f H hy, map_add (f := _), pWp_f H, zero_add, uv, map_add (f := _), pWp_of_isWp (hy c), map_sum]
  simp [pWp_e H]

theorem h_tV_right (x x' : n → A) :
    D.h x (tV D half y x') = ∑ a, D.h (D.e a) x' * D.σA (D.h (y a) x) +
      ∑ a, ∑ b, D.h (D.e a) x' * (cf D half y a b * D.σA (D.h (D.e b) x)) -
      ∑ b, D.h (y b) x' * D.σA (D.h (D.e b) x) := by
  have sw : ∀ z, D.h x z = D.σA (D.h z x) := fun z => hswap_lemma_6 H z x
  simp only [tV, uv, hRsub_lemma_3, hRsum_lemma_5, hRsmul_lemma_4, hRadd_lemma_2]
  simp only [sw, mul_add, Finset.mul_sum, Finset.sum_add_distrib]

theorem h_tV_left (x x' : n → A) :
    D.h (tV D half y x) x' = ∑ a, D.σA (D.h (D.e a) x) * D.h (y a) x' +
      ∑ a, ∑ b, D.σA (D.h (D.e a) x) * (D.σA (cf D half y a b) * D.h (D.e b) x') -
      ∑ b, D.σA (D.h (y b) x) * D.h (D.e b) x' := by
  simp only [tV, uv, hLsub_lemma_9 H, hLsum_lemma_8 H, h_smul_left, h_add_left, mul_add, Finset.mul_sum,
    Finset.sum_add_distrib]

theorem h_tV_tV (x x' : n → A) :
    D.h (tV D half y x) (tV D half y x') =
      ∑ a, ∑ b, D.σA (D.h (D.e a) x) * (D.h (D.e b) x' * D.h (y a) (y b)) := by
  have k1 : ∀ b, D.h (D.e b) (tV D half y x') = 0 := fun b => by
    simp only [tV, hRsub_lemma_3, hRsum_lemma_5, hRsmul_lemma_4, h_e_uv H hy, H.ee, mul_zero,
      Finset.sum_const_zero, sub_self]
  have k2 : ∀ a, D.h (uv D half y a) (tV D half y x') =
      ∑ b, D.h (D.e b) x' * D.h (y a) (y b) := fun a => by
    simp only [tV, hRsub_lemma_3, hRsum_lemma_5, hRsmul_lemma_4, h_uv_uv H hy, h_uv_e H hy, mul_zero,
      Finset.sum_const_zero, sub_zero]
  rw [show tV D half y x = ∑ a, D.h (D.e a) x • uv D half y a - ∑ b, D.h (y b) x • D.e b from rfl]
  simp only [hLsub_lemma_9 H, hLsum_lemma_8 H, h_smul_left, k1, k2, mul_zero, Finset.sum_const_zero,
    sub_zero, Finset.mul_sum]

theorem sL_uni (hh : Half D half) (x x' : n → A) : D.h (sL D half y x) (sL D half y x') = D.h x x' := by
  have e1 := h_tV_right H hy (half := half) x x'
  have e2 := h_tV_left H hy (half := half) x x'
  have e3 := h_tV_tV H hy (half := half) x x'
  rw [sL_eq, sL_eq, h_add_left, hRadd_lemma_2, hRadd_lemma_2, e1, e2, e3]
  have c1 : ∑ a, D.h (D.e a) x' * D.σA (D.h (y a) x) =
      ∑ b, D.σA (D.h (y b) x) * D.h (D.e b) x' :=
    Finset.sum_congr rfl fun a _ => mul_comm _ _
  have c2 : ∑ b, D.h (y b) x' * D.σA (D.h (D.e b) x) =
      ∑ a, D.σA (D.h (D.e a) x) * D.h (y a) x' :=
    Finset.sum_congr rfl fun a _ => mul_comm _ _
  have c3 : (∑ a, ∑ b, D.h (D.e a) x' * (cf D half y a b * D.σA (D.h (D.e b) x))) +
      (∑ a, ∑ b, D.σA (D.h (D.e a) x) * (D.σA (cf D half y a b) * D.h (D.e b) x')) +
      (∑ a, ∑ b, D.σA (D.h (D.e a) x) * (D.h (D.e b) x' * D.h (y a) (y b))) = 0 := by
    rw [Finset.sum_comm (f := fun a b => D.h (D.e a) x' * (cf D half y a b * D.σA (D.h (D.e b) x)))]
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
    simp only [cf, map_neg, map_mul, hh.sig]
    rw [← hswap_lemma_6 H (y b) (y a)]
    linear_combination (-(D.σA (D.h (D.e a) x) * D.h (D.e b) x' * D.h (y a) (y b))) * hh.two
  linear_combination c1 - c2 + c3

end Sec

theorem unipotent_radical_action_formula (H : D.Hyp) {Φ : (n → A) →ₗ[A] (n → A)} (hU : D.Uni Φ) (he : ∀ a, Φ (D.e a) = D.e a)
    (hP : ∀ v, Xp D v → Φ v - v ∈ Submodule.span A (Set.range D.e)) {v : n → A} (hv : Xp D v) :
    Φ v = v - ∑ a, D.h (pWp D (Φ (D.f a))) v • D.e a := by
  have hv' : ∀ a, D.h (D.e a) v = 0 := hv
  have hm := hP v hv
  rw [Submodule.mem_span_range_iff_exists_fun] at hm
  obtain ⟨c, hc⟩ := hm
  have hΦv : Φ v = v + ∑ a, c a • D.e a := by rw [hc]; abel
  have key : ∀ b, c b = -D.h (pWp D (Φ (D.f b))) v := by
    intro b
    have hwe : ∀ a, D.h (Φ (D.f b)) (D.e a) = if b = a then 1 else 0 := by
      intro a
      rw [← he a, hU (D.f b) (D.e a), hfe_lemma_7 H]
    have hew : ∀ a, D.h (D.e a) (Φ (D.f b)) = if a = b then 1 else 0 := by
      intro a
      rw [← he a, hU (D.e a) (D.f b), H.ef]
    have hpXv : D.pXv (Φ (D.f b)) = D.f b := by
      rw [pXvap_lemma_11]
      simp [hew]
    have hpX0 : D.h (D.pX (Φ (D.f b))) v = 0 := by
      rw [pXap_lemma_10, hLsum_lemma_8 H]
      simp [h_smul_left, hv']
    have hw_v : D.h (Φ (D.f b)) v = D.h (D.f b) v + D.h (pWp D (Φ (D.f b))) v := by
      have hdec : Φ (D.f b) = D.pX (Φ (D.f b)) + D.pXv (Φ (D.f b)) + pWp D (Φ (D.f b)) := by
        rw [pWp_apply]; abel
      conv_lhs => rw [hdec]
      rw [h_add_left, h_add_left, hpX0, hpXv, zero_add]
    have hUv := hU (D.f b) v
    rw [hΦv, hRadd_lemma_2, hRsum_lemma_5, hw_v] at hUv
    simp [hRsmul_lemma_4, hwe] at hUv
    linear_combination hUv
  rw [hΦv, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  exact Finset.sum_congr rfl fun a _ => by rw [key a, neg_smul]

def ND (D : Dat A n r) : Prop := ∀ x : n → A, (∀ v, D.h v x = 0) → x = 0

theorem fix_f_mem (H : D.Hyp) (hND : ND D) {Φ : (n → A) →ₗ[A] (n → A)} (hU : D.Uni Φ)
    (hfix : ∀ v, Xp D v → Φ v = v) (a : Fin r) :
    Φ (D.f a) - D.f a ∈ Submodule.span A (Set.range D.e) := by
  obtain ⟨w, hw⟩ : ∃ w, w = Φ (D.f a) - D.f a := ⟨_, rfl⟩
  rw [← hw]
  have hv_w : ∀ v, Xp D v → D.h w v = 0 := by
    intro v hv
    have h1 := hU (D.f a) v
    rw [hfix v hv] at h1
    rw [hw, hLsub_lemma_9 H, h1, sub_self]
  have hew : ∀ b, D.h (D.e b) w = 0 := by
    intro b
    have h1 := hU (D.e b) (D.f a)
    rw [hfix (D.e b) (xp_e H b)] at h1
    rw [hw, hRsub_lemma_3, h1, sub_self]
  have hpXv : D.pXv w = 0 := by
    rw [pXvap_lemma_11]
    simp [hew]
  have hdec : w = D.pX w + pWp D w := by
    rw [pWp_apply, hpXv]; abel
  have hpX0 : ∀ v, Xp D v → D.h (D.pX w) v = 0 := by
    intro v hv
    have hv' : ∀ b, D.h (D.e b) v = 0 := hv
    rw [pXap_lemma_10, hLsum_lemma_8 H]
    simp [h_smul_left, hv']
  have hP0 : pWp D w = 0 := by
    apply hND
    intro u
    have hW := pWp_isWp H w
    unfold IsWp at hW
    obtain ⟨-, hWf⟩ := hW
    have hu : u = (u - D.pXv u) + D.pXv u := (sub_add_cancel u _).symm
    rw [hu, h_add_left]
    have hvX := xp_sub_pXv H u
    have hA : D.h (pWp D w) (u - D.pXv u) = 0 := by
      have := hv_w _ hvX
      rw [hdec, h_add_left, hpX0 _ hvX, zero_add] at this
      exact this
    have hB : D.h (u - D.pXv u) (pWp D w) = 0 := by
      rw [hswap_lemma_6 H, hA, map_zero]
    have hC : D.h (D.pXv u) (pWp D w) = 0 := by
      rw [pXvap_lemma_11, hLsum_lemma_8 H]
      simp [h_smul_left, hWf]
    rw [hB, hC, add_zero]
  rw [hdec, hP0, add_zero, pXap_lemma_10]
  exact sum_mem fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)

end PI.LevelKSplit.W.NCH
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.NCHeisC
noncomputable section

namespace PI.LevelKSplit.W.NCH

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
open scoped TensorProduct

section Cont

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  [TopologicalSpace R] [IsTopologicalRing R] [IsTopologicalRing (R ⊗[F] E)]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ} (P : Frame E M r) (T : F)

theorem continuous_pWpR : Continuous (PI.LevelKSplit.W.NC.pWp R σ J P) := by
  show Continuous fun x => PI.LevelKSplit.W.NC.pWp R σ J P x
  unfold PI.LevelKSplit.W.NC.pWp
  refine (continuous_id.sub ?_).sub ?_ <;>
  refine continuous_finsetSum _ fun a _ => ?_ <;>
  exact (PI.VolSemiDirect.W.Md.continuous_hR _ σ J (hu := continuous_const) (hv := continuous_id)).smul continuous_const

theorem continuous_yH : Continuous (PI.LevelKSplit.W.NC.yH R σ J P) := by
  refine continuous_pi fun a => ?_
  exact (continuous_pWpR P).comp (PI.VolSemiDirect.W.Md.continuous_linear_action _ σ J (hg := continuous_id) (hv := continuous_const))

theorem continuous_sL_apply (half : R ⊗[F] E) {X : Type} [TopologicalSpace X]
    {y : X → Fin r → Fin M → R ⊗[F] E} (hy : Continuous y) (v : Fin M → R ⊗[F] E) :
    Continuous fun x => sL (PI.VolSemiDirect.W.datR R σ J P T) half (y x) v := by
  have hh : ∀ {u w : X → Fin M → R ⊗[F] E}, Continuous u → Continuous w →
      Continuous fun x => (PI.VolSemiDirect.W.datR R σ J P T).h (u x) (w x) :=
    fun hu hw => PI.VolSemiDirect.W.Md.continuous_hR _ σ J (hu := hu) (hv := hw)
  simp only [sL, uv, cf, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply,
    LinearMap.sum_apply, Finset.sum_apply, LinearMap.smulRight_apply, PI.VolSemiDirect.W.PG.Dat.hL,
    LinearMap.coe_mk, AddHom.coe_mk]
  refine (continuous_const.add (continuous_finsetSum _ fun a _ => ?_)).sub
    (continuous_finsetSum _ fun b _ => ?_)
  · exact (hh continuous_const continuous_const).smul (((continuous_apply a).comp hy).add
      (continuous_finsetSum _ fun b _ => ((continuous_const.mul
        (hh ((continuous_apply b).comp hy) ((continuous_apply a).comp hy))).neg).smul continuous_const))
  · exact (hh ((continuous_apply b).comp hy) continuous_const).smul continuous_const

theorem continuous_sLmat (half : R ⊗[F] E) {X : Type} [TopologicalSpace X]
    {y : X → Fin r → Fin M → R ⊗[F] E} (hy : Continuous y) :
    Continuous fun x => LinearMap.toMatrix' (sL (PI.VolSemiDirect.W.datR R σ J P T) half (y x)) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [LinearMap.toMatrix'_apply]
  exact (continuous_apply i).comp (continuous_sL_apply P T half hy _)

end Cont

end PI.LevelKSplit.W.NCH
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.HeisenbergCocycleMemCentre
noncomputable section

namespace PI.LevelKSplit.W.NCH

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub PI.VolSemiDirect.W PI.VolSemiDirect.W.PG
  PI.VolSemiDirect.W.PG.Dat
open scoped TensorProduct Matrix

section Gen

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ} {D : Dat A n r}

theorem fix_span {Φ : (n → A) →ₗ[A] (n → A)} (he : ∀ a, Φ (D.e a) = D.e a) {x : n → A}
    (hx : x ∈ Submodule.span A (Set.range D.e)) : Φ x = x := by
  first
  | exact LinearMap.eqOn_span' (f := Φ) (g := LinearMap.id) (by rintro _ ⟨a, rfl⟩; exact he a) hx
  | (induction hx using Submodule.span_induction with
      | mem y hy => obtain ⟨a, rfl⟩ := hy; exact he a
      | zero => exact map_zero Φ
      | add y z _ _ hy hz => rw [map_add (f := _), hy, hz]
      | smul c y _ hy => rw [map_smul, hy])

def sMat (D : Dat A n r) (half : A) (y : Fin r → n → A) : Matrix n n A :=
  LinearMap.toMatrix' (sL D half y)

end Gen

section R

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ} {P : Frame E M r} {T : F}

theorem spanR_eq :
    spanR (F := F) R P.e Set.univ =
      Submodule.span (R ⊗[F] E) (Set.range (datR R σ J P T).e) := by
  unfold spanR
  rw [Set.image_univ]
  rfl

theorem pWp_eq (x : Fin M → R ⊗[F] E) :
    PI.LevelKSplit.W.NC.pWp R σ J P x = pWp (datR R σ J P T) x := by
  rw [pWp_apply, pX_apply, pXv_apply]
  rfl

theorem yH_eq (g : HA R σ J) (a : Fin r) :
    PI.LevelKSplit.W.NC.yH R σ J P g a =
      pWp (datR R σ J P T) (lin R σ J g ((datR R σ J P T).f a)) :=
  pWp_eq _

theorem uni_lin (g : HA R σ J) : (datR R σ J P T).Uni (lin R σ J g) := fun x y => hR_lin g x y

theorem unipotent_radical_fixes_frame {g : HA R σ J} (hg : g ∈ PI.LevelKSplit.W.NC.LevelUnipotentSubgroup R σ J P) (a : Fin r) :
    lin R σ J g ((datR R σ J P T).e a) = (datR R σ J P T).e a :=
  (mem_stabT R σ J P.e g).1 hg.2 a

theorem N_perp {g : HA R σ J} (hg : g ∈ Nsub R σ J P) (v : Fin M → R ⊗[F] E)
    (hv : Xp (datR R σ J P T) v) :
    lin R σ J g v - v ∈ Submodule.span (R ⊗[F] E) (Set.range (datR R σ J P T).e) := by
  have hg' : UniC R σ J P.e g ∧ ∀ v, InXperp R σ J P v →
      lin R σ J g v - v ∈ spanR (F := F) R P.e Set.univ := hg
  rw [← spanR_eq]
  exact hg'.2 v hv

theorem mem_unipotent_radical_of {g : HA R σ J}
    (he : ∀ a, lin R σ J g ((datR R σ J P T).e a) = (datR R σ J P T).e a)
    (hp : ∀ v, Xp (datR R σ J P T) v →
      lin R σ J g v - v ∈ Submodule.span (R ⊗[F] E) (Set.range (datR R σ J P T).e)) :
    g ∈ PI.LevelKSplit.W.NC.LevelUnipotentSubgroup R σ J P := by
  refine ⟨⟨fun b => ?_, fun v hv => ?_⟩, (mem_stabT R σ J P.e g).2 he⟩
  · have hb : lin R σ J g (ratV (F := F) R (P.e b)) = ratV (F := F) R (P.e b) := he b
    rw [hb, sub_self]
    exact Submodule.zero_mem _
  · rw [spanR_eq (σ := σ) (J := J) (T := T)]
    exact hp v hv

theorem hJi (hJ : IsHermND σ J) : (J⁻¹).map (inclR (F := F) R) * JR R J = 1 := by
  rw [JR, ← Matrix.map_mul, Matrix.nonsing_inv_mul J (isUnit_iff_ne_zero.2 hJ.2)]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem nd_datR (hJ : IsHermND σ J) : ND (datR R σ J P T) := by
  intro x hx
  have hJx : JR R J *ᵥ x = 0 := by
    funext i
    have h1 := hx (Pi.single i (1 : R ⊗[F] E))
    have hs : ∀ k, sigR R σ ((Pi.single i (1 : R ⊗[F] E) : Fin M → R ⊗[F] E) k) =
        (Pi.single i (1 : R ⊗[F] E) : Fin M → R ⊗[F] E) k := fun k => by
      rcases eq_or_ne k i with rfl | hk
      · rw [Pi.single_eq_same, map_one]
      · rw [Pi.single_eq_of_ne hk, map_zero]
    change ∑ k, ∑ j, sigR R σ ((Pi.single i (1 : R ⊗[F] E) : Fin M → R ⊗[F] E) k) * JR R J k j *
      x j = 0 at h1
    simp only [Pi.single_apply, zero_mul] at h1
    simpa [Matrix.mulVec, dotProduct] using h1
  rw [← Matrix.one_mulVec x, ← hJi (R := R) hJ, ← Matrix.mulVec_mulVec, hJx, Matrix.mulVec_zero]

section Sec

variable (hJ : IsHermND σ J) (H : (datR R σ J P T).Hyp) {half : R ⊗[F] E}
  (hh : Half (datR R σ J P T) half)
include hJ H hh

theorem sMat_uj {y : Fin r → Fin M → R ⊗[F] E} (hy : ∀ a, IsWp (datR R σ J P T) (y a)) :
    Formalism.UG.cT (sigR R σ) (sMat (datR R σ J P T) half y) * JR R J * sMat (datR R σ J P T) half y =
      JR R J :=
  PI.LevelKSplit.W.SemiA.uj_of_uni _ _ _ fun x x' => by
    rw [sMat, LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec]
    exact sL_uni H hy hh x x'

theorem sMat_linv {y : Fin r → Fin M → R ⊗[F] E} (hy : ∀ a, IsWp (datR R σ J P T) (y a)) :
    (J⁻¹).map (inclR (F := F) R) * Formalism.UG.cT (sigR R σ) (sMat (datR R σ J P T) half y) * JR R J *
      sMat (datR R σ J P T) half y = 1 := by
  have e : (J⁻¹).map (inclR (F := F) R) * Formalism.UG.cT (sigR R σ) (sMat (datR R σ J P T) half y) *
      JR R J * sMat (datR R σ J P T) half y = (J⁻¹).map (inclR (F := F) R) *
      (Formalism.UG.cT (sigR R σ) (sMat (datR R σ J P T) half y) * JR R J *
        sMat (datR R σ J P T) half y) := by
    simp only [Matrix.mul_assoc]
  rw [e, sMat_uj hJ H hh hy, hJi hJ]

def sU {y : Fin r → Fin M → R ⊗[F] E} (hy : ∀ a, IsWp (datR R σ J P T) (y a)) :
    GL (Fin M) (R ⊗[F] E) where
  val := sMat (datR R σ J P T) half y
  inv := (J⁻¹).map (inclR (F := F) R) * Formalism.UG.cT (sigR R σ) (sMat (datR R σ J P T) half y) *
    JR R J
  val_inv := mul_eq_one_comm.2 (sMat_linv hJ H hh hy)
  inv_val := sMat_linv hJ H hh hy

theorem sU_mem {y : Fin r → Fin M → R ⊗[F] E} (hy : ∀ a, IsWp (datR R σ J P T) (y a)) :
    sU hJ H hh hy ∈ HR R σ J := by
  first
  | exact sMat_uj hJ H hh hy
  | (simp only [HR]; exact sMat_uj hJ H hh hy)
  | (simp [HR, sU]; exact sMat_uj hJ H hh hy)

def sHG {y : Fin r → Fin M → R ⊗[F] E} (hy : ∀ a, IsWp (datR R σ J P T) (y a)) : HA R σ J :=
  ⟨sU hJ H hh hy, sU_mem hJ H hh hy⟩

theorem lin_sHG {y : Fin r → Fin M → R ⊗[F] E} (hy : ∀ a, IsWp (datR R σ J P T) (y a)) :
    lin R σ J (sHG hJ H hh hy) = sL (datR R σ J P T) half y := by
  unfold lin
  simp [sHG, sU, HA.mat, sMat]
  first
  | exact Matrix.toLin'_toMatrix' _
  | exact LinearMap.ext fun x => LinearMap.toMatrix'_mulVec _ x

theorem sHG_mem {y : Fin r → Fin M → R ⊗[F] E} (hy : ∀ a, IsWp (datR R σ J P T) (y a)) :
    sHG hJ H hh hy ∈ PI.LevelKSplit.W.NC.LevelUnipotentSubgroup R σ J P := by
  refine mem_unipotent_radical_of (T := T) (fun a => ?_) (fun v hv => ?_)
  · rw [lin_sHG]
    exact sL_e H hy a
  · rw [lin_sHG, sL_Xp H hy hv, sub_sub_cancel_left]
    exact Submodule.neg_mem _ (Submodule.sum_mem _ fun b _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩))

theorem yH_sHG {y : Fin r → Fin M → R ⊗[F] E} (hy : ∀ a, IsWp (datR R σ J P T) (y a)) (a : Fin r) :
    PI.LevelKSplit.W.NC.yH R σ J P (sHG hJ H hh hy) a = y a := by
  rw [yH_eq (T := T), lin_sHG]
  exact pWp_sL_f H hy a

theorem isWp_yH (g : HA R σ J) (a : Fin r) :
    IsWp (datR R σ J P T) (PI.LevelKSplit.W.NC.yH R σ J P g a) := by
  rw [yH_eq (T := T)]
  exact pWp_isWp H _

theorem N_xp {g : HA R σ J} (hg : g ∈ Nsub R σ J P) {v : Fin M → R ⊗[F] E}
    (hv : Xp (datR R σ J P T) v) : Xp (datR R σ J P T) (lin R σ J g v) := by
  have e : lin R σ J g v = v + (lin R σ J g v - v) := by abel
  rw [e]
  exact xp_add hv (xp_of_span H (N_perp hg v hv))

theorem unipotent_radical_action {g : HA R σ J} (hg : g ∈ PI.LevelKSplit.W.NC.LevelUnipotentSubgroup R σ J P)
    {v : Fin M → R ⊗[F] E} (hv : Xp (datR R σ J P T) v) :
    lin R σ J g v = v - ∑ a, (datR R σ J P T).h (PI.LevelKSplit.W.NC.yH R σ J P g a) v •
      (datR R σ J P T).e a := by
  simp only [yH_eq (T := T)]
  exact unipotent_radical_action_formula H (uni_lin g) (unipotent_radical_fixes_frame hg) (N_perp hg.1) hv

theorem inv_mul_mem_Z {g : HA R σ J} (hg : g ∈ PI.LevelKSplit.W.NC.LevelUnipotentSubgroup R σ J P) :
    (sHG hJ H hh (isWp_yH hJ H hh g))⁻¹ * g ∈ PI.LevelKSplit.W.NC.Zsub R σ J P := by
  refine ⟨(Nsub R σ J P).mul_mem ((Nsub R σ J P).inv_mem (sHG_mem hJ H hh _).1) hg.1,
    fun v hv => ?_⟩
  have e : lin R σ J g v = lin R σ J (sHG hJ H hh (isWp_yH hJ H hh g)) v := by
    rw [unipotent_radical_action hJ H hh hg hv, unipotent_radical_action hJ H hh (sHG_mem hJ H hh _) hv]
    simp only [yH_sHG]
  rw [lin_mul, e, lin_inv_lin]

theorem centre_le_unipotent_radical : PI.LevelKSplit.W.NC.Zsub R σ J P ≤ PI.LevelKSplit.W.NC.LevelUnipotentSubgroup R σ J P :=
  fun z hz => ⟨hz.1, (mem_stabT R σ J P.e z).2 fun a => hz.2 _ (xp_e H a)⟩

theorem Z_fix {z : HA R σ J} (hz : z ∈ PI.LevelKSplit.W.NC.Zsub R σ J P) {v : Fin M → R ⊗[F] E}
    (hv : Xp (datR R σ J P T) v) : lin R σ J z v = v :=
  hz.2 v hv

theorem Z_f {z : HA R σ J} (hz : z ∈ PI.LevelKSplit.W.NC.Zsub R σ J P) (a : Fin r) :
    lin R σ J z ((datR R σ J P T).f a) - (datR R σ J P T).f a ∈
      Submodule.span (R ⊗[F] E) (Set.range (datR R σ J P T).e) :=
  fix_f_mem H (nd_datR hJ) (uni_lin z) (fun v hv => Z_fix hJ H hh hz hv) a

theorem yH_mul_Z {g : HA R σ J} (hg : g ∈ PI.LevelKSplit.W.NC.LevelUnipotentSubgroup R σ J P) {z : HA R σ J}
    (hz : z ∈ PI.LevelKSplit.W.NC.Zsub R σ J P) (a : Fin r) :
    PI.LevelKSplit.W.NC.yH R σ J P (g * z) a = PI.LevelKSplit.W.NC.yH R σ J P g a := by
  rw [yH_eq (T := T), yH_eq (T := T), lin_mul]
  have e : lin R σ J z ((datR R σ J P T).f a) = (datR R σ J P T).f a +
      (lin R σ J z ((datR R σ J P T).f a) - (datR R σ J P T).f a) := by abel
  rw [e, map_add (f := _), fix_span (unipotent_radical_fixes_frame hg) (Z_f hJ H hh hz a), map_add (f := _), pWp_span H (Z_f hJ H hh hz a),
    add_zero]

theorem Z_comm {z : HA R σ J} (hz : z ∈ PI.LevelKSplit.W.NC.Zsub R σ J P) {g : HA R σ J}
    (hg : g ∈ PI.LevelKSplit.W.NC.LevelUnipotentSubgroup R σ J P) : z * g = g * z := by
  apply PI.LevelKSplit.W.SemiA.ext_lin
  intro v
  rw [lin_mul, lin_mul]
  refine ext_Xp_f H (Φ := (lin R σ J z).comp (lin R σ J g)) (Ψ := (lin R σ J g).comp (lin R σ J z))
    (fun v hv => ?_) (fun a => ?_) v
  · simp only [LinearMap.comp_apply]
    rw [Z_fix hJ H hh hz (N_xp hJ H hh hg.1 hv), Z_fix hJ H hh hz hv]
  · simp only [LinearMap.comp_apply]
    have hnf : Xp (datR R σ J P T) (lin R σ J g ((datR R σ J P T).f a) - (datR R σ J P T).f a) := by
      intro b
      have hb : (datR R σ J P T).h ((datR R σ J P T).e b) (lin R σ J g ((datR R σ J P T).f a)) =
          (datR R σ J P T).h ((datR R σ J P T).e b) ((datR R σ J P T).f a) := by
        rw [← uni_lin g ((datR R σ J P T).e b) ((datR R σ J P T).f a), unipotent_radical_fixes_frame hg b]
      rw [h_sub_right, hb, sub_self]
    calc lin R σ J z (lin R σ J g ((datR R σ J P T).f a))
        = lin R σ J z ((datR R σ J P T).f a +
            (lin R σ J g ((datR R σ J P T).f a) - (datR R σ J P T).f a)) := by
          congr 1; abel
      _ = lin R σ J z ((datR R σ J P T).f a) +
            (lin R σ J g ((datR R σ J P T).f a) - (datR R σ J P T).f a) := by
          rw [map_add (f := _), Z_fix hJ H hh hz hnf]
      _ = lin R σ J g ((datR R σ J P T).f a) +
            (lin R σ J z ((datR R σ J P T).f a) - (datR R σ J P T).f a) := by abel
      _ = lin R σ J g ((datR R σ J P T).f a +
            (lin R σ J z ((datR R σ J P T).f a) - (datR R σ J P T).f a)) := by
          rw [map_add (f := _), fix_span (unipotent_radical_fixes_frame hg) (Z_f hJ H hh hz a)]
      _ = lin R σ J g (lin R σ J z ((datR R σ J P T).f a)) := by
          congr 1; abel

theorem heisenberg_cocycle_mem_centre {y y' : Fin r → Fin M → R ⊗[F] E} (hy : ∀ a, IsWp (datR R σ J P T) (y a))
    (hy' : ∀ a, IsWp (datR R σ J P T) (y' a)) (hyy : ∀ a, IsWp (datR R σ J P T) ((y + y') a)) :
    sHG hJ H hh hy * sHG hJ H hh hy' * (sHG hJ H hh hyy)⁻¹ ∈ PI.LevelKSplit.W.NC.Zsub R σ J P := by
  refine ⟨(Nsub R σ J P).mul_mem ((Nsub R σ J P).mul_mem (sHG_mem hJ H hh hy).1
    (sHG_mem hJ H hh hy').1) ((Nsub R σ J P).inv_mem (sHG_mem hJ H hh hyy).1), fun v hv => ?_⟩
  obtain ⟨u, hu, rfl⟩ : ∃ u, Xp (datR R σ J P T) u ∧ lin R σ J (sHG hJ H hh hyy) u = v :=
    ⟨lin R σ J (sHG hJ H hh hyy)⁻¹ v,
      N_xp hJ H hh ((Nsub R σ J P).inv_mem (sHG_mem hJ H hh hyy).1) hv, lin_lin_inv R σ J _ _⟩
  rw [lin_mul, lin_inv_lin, lin_mul]
  simp only [lin_sHG]
  have hs : ∑ b, (datR R σ J P T).h (y' b) u • (datR R σ J P T).e b ∈
      Submodule.span (R ⊗[F] E) (Set.range (datR R σ J P T).e) :=
    Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
  rw [sL_Xp H hy' hu, map_sub, sL_Xp H hy hu, sL_span H hy hs, sL_Xp H hyy hu]
  simp only [Pi.add_apply, h_add_left, add_smul, Finset.sum_add_distrib]
  abel

theorem N_norm_Z {g : HA R σ J} (hg : g ∈ Nsub R σ J P) {z : HA R σ J}
    (hz : z ∈ PI.LevelKSplit.W.NC.Zsub R σ J P) : g * z * g⁻¹ ∈ PI.LevelKSplit.W.NC.Zsub R σ J P :=
  ⟨(Nsub R σ J P).mul_mem ((Nsub R σ J P).mul_mem hg hz.1) ((Nsub R σ J P).inv_mem hg),
    fun v hv => by
      rw [lin_mul, lin_mul, Z_fix hJ H hh hz (N_xp hJ H hh ((Nsub R σ J P).inv_mem hg) hv), lin_lin_inv]⟩

theorem H_e {h : HA R σ J} (hh' : h ∈ Hsub R σ J P) (a : Fin r) :
    lin R σ J h ((datR R σ J P T).e a) = (datR R σ J P T).e a :=
  PI.LevelKSplit.W.SemiA.H_fix_e hh' a

theorem H_f {h : HA R σ J} (hh' : h ∈ Hsub R σ J P) (a : Fin r) :
    lin R σ J h ((datR R σ J P T).f a) = (datR R σ J P T).f a :=
  PI.LevelKSplit.W.SemiA.H_fix_f hh' a

theorem H_he {h : HA R σ J} (hh' : h ∈ Hsub R σ J P) (a : Fin r) (v : Fin M → R ⊗[F] E) :
    (datR R σ J P T).h ((datR R σ J P T).e a) (lin R σ J h v) =
      (datR R σ J P T).h ((datR R σ J P T).e a) v := by
  rw [← uni_lin h ((datR R σ J P T).e a) v, H_e hJ H hh hh' a]

theorem H_hf {h : HA R σ J} (hh' : h ∈ Hsub R σ J P) (a : Fin r) (v : Fin M → R ⊗[F] E) :
    (datR R σ J P T).h ((datR R σ J P T).f a) (lin R σ J h v) =
      (datR R σ J P T).h ((datR R σ J P T).f a) v := by
  rw [← uni_lin h ((datR R σ J P T).f a) v, H_f hJ H hh hh' a]

theorem H_isWp {h : HA R σ J} (hh' : h ∈ Hsub R σ J P) {w : Fin M → R ⊗[F] E}
    (hw : IsWp (datR R σ J P T) w) : IsWp (datR R σ J P T) (lin R σ J h w) :=
  ⟨fun a => by rw [H_he hJ H hh hh', hw.1 a], fun a => by rw [H_hf hJ H hh hh', hw.2 a]⟩

theorem H_conj_sHG {g : HA R σ J} (hg : g ∈ Hsub R σ J P) {y : Fin r → Fin M → R ⊗[F] E}
    (hy : ∀ a, IsWp (datR R σ J P T) (y a))
    (hyh : ∀ a, IsWp (datR R σ J P T) ((fun b => lin R σ J g (y b)) a)) :
    g * sHG hJ H hh hy * g⁻¹ = sHG hJ H hh hyh := by
  apply PI.LevelKSplit.W.SemiA.ext_lin
  intro v
  rw [lin_mul, lin_mul, lin_sHG, lin_sHG, sL_apply, sL_apply]
  have hu : ∀ x x', (datR R σ J P T).h (lin R σ J g x) (lin R σ J g x') =
      (datR R σ J P T).h x x' := uni_lin g
  have e1 : ∀ a, (datR R σ J P T).h ((datR R σ J P T).e a) (lin R σ J g⁻¹ v) =
      (datR R σ J P T).h ((datR R σ J P T).e a) v := fun a => by
    rw [← hu, H_e hJ H hh hg a, lin_lin_inv]
  have e2 : ∀ b, (datR R σ J P T).h (y b) (lin R σ J g⁻¹ v) =
      (datR R σ J P T).h (lin R σ J g (y b)) v := fun b => by
    rw [← hu, lin_lin_inv]
  have luv : ∀ a, lin R σ J g (uv (datR R σ J P T) half y a) =
      uv (datR R σ J P T) half (fun b => lin R σ J g (y b)) a := fun a => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [uv, cf, map_add (f := _), map_sum, map_smul, H_e hJ H hh hg, hu]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_add (f := _), map_sub, map_sum, map_smul, e1, e2, luv, H_e hJ H hh hg, lin_lin_inv]

theorem H_xp {h : HA R σ J} (hh' : h ∈ Hsub R σ J P) {v : Fin M → R ⊗[F] E}
    (hv : Xp (datR R σ J P T) v) : Xp (datR R σ J P T) (lin R σ J h v) :=
  fun a => by rw [H_he hJ H hh hh', hv a]

theorem H_comm_Z {g : HA R σ J} (hg : g ∈ Hsub R σ J P) {z : HA R σ J}
    (hz : z ∈ PI.LevelKSplit.W.NC.Zsub R σ J P) : g * z * g⁻¹ = z := by
  have hgi : g⁻¹ ∈ Hsub R σ J P := (Hsub R σ J P).inv_mem hg
  apply PI.LevelKSplit.W.SemiA.ext_lin
  intro v
  refine ext_Xp_f H (Φ := lin R σ J (g * z * g⁻¹)) (Ψ := lin R σ J z) (fun v hv => ?_)
    (fun a => ?_) v
  · rw [lin_mul, lin_mul, Z_fix hJ H hh hz (H_xp hJ H hh hgi hv), lin_lin_inv, Z_fix hJ H hh hz hv]
  · rw [lin_mul, lin_mul, H_f hJ H hh hgi a]
    have e : lin R σ J z ((datR R σ J P T).f a) = (datR R σ J P T).f a +
        (lin R σ J z ((datR R σ J P T).f a) - (datR R σ J P T).f a) := by abel
    rw [e, map_add (f := _), H_f hJ H hh hg a, fix_span (H_e hJ H hh hg) (Z_f hJ H hh hz a)]

end Sec

end R

end PI.LevelKSplit.W.NCH
end
end

noncomputable section

namespace PI.LevelKSplit.W.NCH

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub PI.VolSemiDirect.W NumberField IsDedekindDomain
open scoped TensorProduct

theorem heisenberg_parabolic (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]
    [FiniteDimensional F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) :
    PI.LevelKSplit.W.NC.HeisP F E σ M J := by
  intro hJ hσσ r P T hP
  have H : (datR (Af F) σ J P T).Hyp := datR_hyp (R := Af F) hσσ hJ hP
  have hh : Half (datR (Af F) σ J P T) (algebraMap F (Af F ⊗[F] E) (1 / 2)) := by
    refine ⟨?_, ?_⟩
    · rw [← map_add (f := _), add_halves, map_one]
    · show (Algebra.TensorProduct.map (AlgHom.id F (Af F)) σ) (algebraMap F (Af F ⊗[F] E) (1 / 2)) =
        algebraMap F (Af F ⊗[F] E) (1 / 2)
      exact AlgHom.commutes _ _
  have hcy : Continuous fun y : Fin r → PI.LevelKSplit.W.NC.Wp (Af F) σ J P =>
      fun a => (y a : Fin M → Af F ⊗[F] E) :=
    continuous_pi fun a => continuous_subtype_val.comp (continuous_apply a)
  refine ⟨fun y => sHG hJ H hh (y := fun a => (y a : Fin M → Af F ⊗[F] E)) (fun a => (y a).2),
    ?_, continuous_yH P, fun y => sHG_mem hJ H hh _, fun g hg => ?_, fun y z hz a => ?_,
    centre_le_unipotent_radical hJ H hh, fun z hz g hg => Z_comm hJ H hh hz hg, fun y y' => ?_,
    fun g hg z hz => N_norm_Z hJ H hh hg hz, fun g hg y => ?_, fun g hg z hz => H_comm_Z hJ H hh hg hz⟩
  · exact Md.continuous_into_HA hJ (continuous_sLmat P T _ hcy)
  · exact ⟨fun a => ⟨_, isWp_yH hJ H hh g a⟩, fun a => rfl, inv_mul_mem_Z hJ H hh hg⟩
  · exact (yH_mul_Z hJ H hh (sHG_mem hJ H hh _) hz a).trans (yH_sHG hJ H hh _ a)
  · exact heisenberg_cocycle_mem_centre hJ H hh (y := fun a => (y a : Fin M → Af F ⊗[F] E))
      (y' := fun a => (y' a : Fin M → Af F ⊗[F] E)) (fun a => (y a).2) (fun a => (y' a).2)
      (fun a => ((y + y') a).2)
  · exact ⟨fun a => ⟨lin (Af F) σ J g (y a), H_isWp hJ H hh hg (y a).2⟩, fun a => rfl,
      H_conj_sHG hJ H hh hg _ _⟩

theorem heisenberg_parabolic_all : PI.LevelKSplit.W.NC.HeisPAll := by
  intro F E _ _ _ _ _ σ hσ M J _
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
  exact heisenberg_parabolic F E σ M J

end PI.LevelKSplit.W.NCH
end
end

theorem level_s_all_split : PI.LevelKSplit.LevelSAll :=
  PI.LevelKSplit.W.Top6.levelSplitting_of_heisenberg_levi PI.LevelKSplit.W.NCH.heisenberg_parabolic_all
    PI.LevelKSplit.W.NCL.levi_part_all
