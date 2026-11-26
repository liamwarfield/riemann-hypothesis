module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.MemInvCoeIdeal

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.SemidefG
noncomputable section

open NumberField Module Formalism.MainNotions.S
open Classical

namespace Formalism.L2.SG.Pf.Cnt.R1

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E) {r : ℕ}

theorem hsw (x y : S.V) : S.hT y x = star (S.hT x y) := (S.herm.eq x y).symm

theorem hsw0 {x y : S.V} (h : S.hT x y = 0) : S.hT y x = 0 := by rw [hsw, h, star_zero]

variable {S}
variable (e y : Fin r → S.V) (z : S.V) (N : ℕ)

structure Dual : Prop where
  ee : ∀ a b, S.hT (e a) (e b) = 0
  yy : ∀ a b, S.hT (y a) (y b) = 0
  ey : ∀ a b, S.hT (e a) (y b) = if a = b then 1 else 0
  ez : ∀ a, S.hT (e a) z = 0
  yz : ∀ a, S.hT (y a) z = 0
  zz : S.hT z z = -(N : E)

def IsW (w : S.V) : Prop := (∀ a, S.hT (e a) w = 0) ∧ (∀ a, S.hT (y a) w = 0) ∧ S.hT z w = 0

variable {e y z N}

theorem Dual.ye (h : Dual e y z N) (a b) : S.hT (y a) (e b) = if b = a then 1 else 0 := by
  rw [hsw, h.ey]; split_ifs <;> simp

theorem real_of (τ : E →+* ℂ) (hτc : ∀ a, τ (star a) = starRingEnd ℂ (τ a)) (w : S.V) :
    τ (S.hT w w) = ((τ (S.hT w w)).re : ℂ) := by
  have h1 : starRingEnd ℂ (τ (S.hT w w)) = τ (S.hT w w) := by
    rw [← hτc, ← hsw]
  have him : (τ (S.hT w w)).im = 0 := Complex.conj_eq_iff_im.1 h1
  exact Complex.ext (by simp) (by simp [him])

theorem semidefG (h : Dual e y z N) (hN : 0 < N) (τ : E →+* ℂ) (hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a))
    {p' : ℕ} (hsig : Formalism.UG.HasSignature (S.gram.map τ) p' (r + 1)) (w : S.V) (hw : IsW e y z w) :
    0 ≤ (τ (S.hT w w)).re := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨hE, hF, hz⟩ := hw
  have hT0 : (0 : ℝ) < N := by exact_mod_cast hN
  let wv : Fin r ⊕ Bool → S.V := Sum.elim (fun a => e a - y a) (fun b => if b then w else z)
  let d : Fin r ⊕ Bool → ℝ := Sum.elim (fun _ => -2) (fun b => if b then (τ (S.hT w w)).re else -(N : ℝ))
  have hoff : ∀ i j, i ≠ j → S.hT (wv i) (wv j) = 0 := by
    intro i j hij
    rcases i with a | b <;> rcases j with a' | b'
    · have ha : a ≠ a' := fun h => hij (by rw [h])
      have ha' : a' ≠ a := fun h => ha h.symm
      simp only [wv, Sum.elim_inl, map_sub, LinearMap.sub_apply, h.ee, h.yy, h.ey, h.ye, if_neg ha, if_neg ha']
      simp
    · cases b'
      · simp only [wv, Sum.elim_inl, Sum.elim_inr, Bool.false_eq_true, if_false, map_sub,
          LinearMap.sub_apply, h.ez, h.yz, sub_zero]
      · simp only [wv, Sum.elim_inl, Sum.elim_inr, if_true, map_sub, LinearMap.sub_apply, hE, hF, sub_zero]
    · cases b
      · simp only [wv, Sum.elim_inl, Sum.elim_inr, Bool.false_eq_true, if_false, map_sub,
          hsw0 S (h.ez a'), hsw0 S (h.yz a'), sub_zero]
      · simp only [wv, Sum.elim_inl, Sum.elim_inr, if_true, map_sub, hsw0 S (hE a'), hsw0 S (hF a'), sub_zero]
    · cases b <;> cases b'
      · exact absurd rfl hij
      · simpa [wv] using hz
      · simpa [wv] using hsw0 S hz
      · exact absurd rfl hij
  have hdiag : ∀ i, τ (S.hT (wv i) (wv i)) = (d i : ℂ) := by
    intro i
    rcases i with a | b
    · simp only [wv, d, Sum.elim_inl, map_sub, LinearMap.sub_apply, h.ee, h.yy, h.ey, h.ye, if_true]
      simp only [map_zero, map_one]
      push_cast; ring
    · cases b
      · simp only [wv, d, Sum.elim_inr, Bool.false_eq_true, if_false, h.zz, map_neg, map_natCast]
        push_cast; ring
      · simp only [wv, d, Sum.elim_inr, if_true]
        exact real_of τ hτ w
  have hneg : ∀ i, d i < 0 := by
    intro i
    rcases i with a | b
    · simp [d]
    · cases b
      · simp only [d, Sum.elim_inr, Bool.false_eq_true, if_false]; linarith
      · simpa [d] using hlt
  have hc := PI.CntNotPosW.card_le_of_negFamily S τ hτ hsig wv d hoff hdiag hneg
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_bool] at hc
  omega

theorem isoZeroG (h : Dual e y z N) (hN : 0 < N) (τ : E →+* ℂ) (hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a))
    (hsemi : ∀ w, IsW e y z w → 0 ≤ (τ (S.hT w w)).re) (w : S.V) (hw : IsW e y z w) (h0 : S.hT w w = 0) :
    w = 0 := by
  obtain ⟨hE, hF, hz⟩ := hw
  have orthW : ∀ v : S.V, IsW e y z v → S.hT w v = 0 := by
    rintro v ⟨hvE, hvF, hvz⟩
    by_contra hx
    set x := S.hT w v with hxdef
    have hτx : τ x ≠ 0 := (map_ne_zero τ).2 hx
    have hNq : 0 < Complex.normSq (τ x) := Complex.normSq_pos.2 hτx
    set v' : S.V := star x • v with hv'
    have hxx : τ (x * star x) = ((Complex.normSq (τ x) : ℝ) : ℂ) := by
      rw [map_mul, hτ, Complex.mul_conj]
    have key : ∀ n : ℕ, 2 * n * Complex.normSq (τ x) ≤ (τ (S.hT v' v')).re := by
      intro n
      set u : S.V := (n : E) • w - v' with hu
      have huW : IsW e y z u := by
        refine ⟨fun a => ?_, fun a => ?_, ?_⟩
        · simp [hu, hv', map_sub, map_smul, hE a, hvE a]
        · simp [hu, hv', map_sub, map_smul, hF a, hvF a]
        · simp [hu, hv', map_sub, map_smul, hz, hvz]
      have hs := hsemi u huW
      have hyw : S.hT v w = star x := by rw [hsw]
      have e1 : S.hT u u = -(2 * (n : E)) * (x * star x) + S.hT v' v' := by
        simp only [hu, map_sub, LinearMap.sub_apply, map_smulₛₗ, LinearMap.smul_apply,
          smul_eq_mul, starRingEnd_apply, star_natCast, h0, hv', star_star, hyw, ← hxdef, RingHom.id_apply]
        ring
      have e2 : (τ (S.hT u u)).re = -(2 * n * Complex.normSq (τ x)) + (τ (S.hT v' v')).re := by
        rw [e1, map_add (f := _), map_mul, hxx, map_neg, map_mul, map_ofNat, map_natCast, Complex.add_re]
        congr 1
        have : -(2 * (n : ℂ)) * ((Complex.normSq (τ x) : ℝ) : ℂ) =
            ((-(2 * n * Complex.normSq (τ x)) : ℝ) : ℂ) := by push_cast; ring
        rw [this, Complex.ofReal_re]
      linarith
    obtain ⟨n, hn⟩ := exists_nat_gt ((τ (S.hT v' v')).re / (2 * Complex.normSq (τ x)))
    have h2 := key n
    rw [div_lt_iff₀ (by positivity)] at hn
    nlinarith
  have hzz : S.hT z z ≠ 0 := by
    rw [h.zz, neg_ne_zero]; exact_mod_cast hN.ne'
  apply S.nondeg.1 w
  intro x
  set xW : S.V := x - ∑ a, (S.hT (y a) x • e a + S.hT (e a) x • y a) - (S.hT z x / S.hT z z) • z with hxW
  have hzE : ∀ a, S.hT z (e a) = 0 := fun a => hsw0 S (h.ez a)
  have hzF : ∀ a, S.hT z (y a) = 0 := fun a => hsw0 S (h.yz a)
  have hWE : ∀ b, S.hT (e b) xW = 0 := by
    intro b
    set_option synthInstance.maxHeartbeats 100000 in
      simp [hxW, map_sub, map_sum, map_add (f := _), map_smul, h.ee, h.ey, h.ez]
  have hWF : ∀ b, S.hT (y b) xW = 0 := by
    intro b
    set_option synthInstance.maxHeartbeats 100000 in
      simp [hxW, map_sub, map_sum, map_add (f := _), map_smul, h.yy, h.ye, h.yz]
  have hWz : S.hT z xW = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [hxW, map_sub, map_sum, map_add (f := _), map_smul, hzE, hzF, hzz]
  have h1 := orthW xW ⟨hWE, hWF, hWz⟩
  have hwE : ∀ a, S.hT w (e a) = 0 := fun a => hsw0 S (hE a)
  have hwF : ∀ a, S.hT w (y a) = 0 := fun a => hsw0 S (hF a)
  have hwz : S.hT w z = 0 := hsw0 S hz
  set_option synthInstance.maxHeartbeats 100000 in
    simpa [hxW, map_sub, map_sum, map_add (f := _), map_smul, hwE, hwF, hwz] using h1

end Gen

end Formalism.L2.SG.Pf.Cnt.R1
end
end

noncomputable section

open NumberField Module Formalism.MainNotions.S
open Classical

namespace Formalism.L2.SG.Pf.Cnt.R1

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E}

theorem surj_pairing {m : ℕ} (f : Fin m → S.V) (hf : LinearIndependent E f) :
    Function.Surjective (LinearMap.pi (fun a => S.hT (f a)) : S.V →ₗ[E] (Fin m → E)) := by
  rw [← LinearMap.range_eq_top]
  by_contra hne
  obtain ⟨φ, hφ0, hφ⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.2 hne) inferInstance
  set c : Fin m → E := fun a => φ (fun j => if a = j then 1 else 0) with hc
  have hφx : ∀ x : Fin m → E, φ x = ∑ a, x a * c a := by
    intro x
    conv_lhs => rw [pi_eq_sum_univ x]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, map_smul, hc]
  have hv : ∀ v : S.V, S.hT (∑ a, star (c a) • f a) v = 0 := by
    intro v
    have h1 : φ ((LinearMap.pi (fun a => S.hT (f a)) : S.V →ₗ[E] (Fin m → E)) v) = 0 := by
      have : (LinearMap.pi (fun a => S.hT (f a)) : S.V →ₗ[E] (Fin m → E)) v ∈
          LinearMap.range (LinearMap.pi (fun a => S.hT (f a)) : S.V →ₗ[E] (Fin m → E)) := ⟨v, rfl⟩
      have h2 := Submodule.mem_map_of_mem (f := φ) this
      exact (Submodule.eq_bot_iff _).1 hφ _ h2
    rw [hφx] at h1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, LinearMap.sum_apply]
    simp only [LinearMap.map_smulₛₗ, starRingEnd_apply, star_star, LinearMap.smul_apply, smul_eq_mul]
    rw [← h1]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [LinearMap.pi_apply, mul_comm]
  have h0 : ∑ a, star (c a) • f a = 0 := S.nondeg.1 _ hv
  have hc0 : ∀ a, c a = 0 := by
    intro a
    have := Fintype.linearIndependent_iff.1 hf _ h0 a
    simpa using this
  apply hφ0
  apply LinearMap.ext
  intro x
  rw [hφx]
  simp [hc0]

variable {r : ℕ}

theorem exists_dual_gen (e : Fin r → S.V) (z : S.V) (N : ℕ) (hN : 0 < N) (hind : LinearIndependent E e)
    (he : ∀ a b, S.hT (e a) (e b) = 0) (hez : ∀ a, S.hT (e a) z = 0) (hzz : S.hT z z = -(N : E)) :
    ∃ y : Fin r → S.V, Dual e y z N := by
  let f : Fin (r + 1) → S.V := Fin.snoc (α := fun _ => S.V) e z
  have hze : ∀ a, S.hT z (e a) = 0 := fun a => hsw0 S (hez a)
  have hzz0 : S.hT z z ≠ 0 := by rw [hzz, neg_ne_zero]; exact_mod_cast hN.ne'
  have hf : LinearIndependent E f := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    rw [Fin.sum_univ_castSucc] at hc
    simp only [f, Fin.snoc_castSucc, Fin.snoc_last] at hc
    have hl : c (Fin.last r) = 0 := by
      have h1 := congrArg (S.hT z) hc
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_add (f := _), map_sum, map_zero] at h1
      simp only [map_smul, smul_eq_mul, hze, mul_zero, Finset.sum_const_zero, zero_add] at h1
      exact (mul_eq_zero.1 h1).resolve_right hzz0
    rw [hl, zero_smul, add_zero] at hc
    have hcs := Fintype.linearIndependent_iff.1 hind _ hc
    intro i
    induction i using Fin.lastCases with
    | last => exact hl
    | cast a => exact hcs a
  have hs := surj_pairing f hf
  choose y0 hy0 using fun a : Fin r => hs (fun j => if j = Fin.castSucc a then (1 : E) else 0)
  have hey0 : ∀ b a, S.hT (e b) (y0 a) = if b = a then 1 else 0 := by
    intro b a
    have := congrFun (hy0 a) (Fin.castSucc b)
    simp only [LinearMap.pi_apply, f, Fin.snoc_castSucc, Fin.castSucc_inj] at this
    exact this
  have hzy0 : ∀ a, S.hT z (y0 a) = 0 := by
    intro a
    have := congrFun (hy0 a) (Fin.last r)
    simp only [LinearMap.pi_apply, f, Fin.snoc_last] at this
    rw [this, if_neg (Fin.castSucc_lt_last a).ne']
  have hy0e : ∀ a d, S.hT (y0 a) (e d) = if d = a then 1 else 0 := by
    intro a d; rw [hsw, hey0]; split_ifs <;> simp
  have hL : ∀ (c : Fin r → E) (v : S.V), S.hT (∑ d, c d • e d) v = ∑ d, star (c d) * S.hT (e d) v := by
    intro c v
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, LinearMap.sum_apply]
    simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply]
  have hR : ∀ (c : Fin r → E) (v : S.V), S.hT v (∑ d, c d • e d) = ∑ d, c d * S.hT v (e d) := by
    intro c v
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, smul_eq_mul]
  set c : Fin r → Fin r → E := fun a d => S.hT (y0 d) (y0 a) / 2 with hc
  set y : Fin r → S.V := fun a => y0 a - ∑ d, c a d • e d with hy
  have hst : ∀ a b, star (S.hT (y0 b) (y0 a)) = S.hT (y0 a) (y0 b) := fun a b => (hsw S _ _).symm
  refine ⟨y, ⟨he, fun a b => ?_, fun a b => ?_, hez, fun a => ?_, hzz⟩⟩
  · have h1 : S.hT (y0 a) (∑ d, c b d • e d) = c b a := by
      rw [hR]; simp [hy0e]
    have h2 : S.hT (∑ d, c a d • e d) (y0 b) = star (c a b) := by
      rw [hL]; simp [hey0]
    have h3 : S.hT (∑ d, c a d • e d) (∑ d, c b d • e d) = 0 := by
      rw [hL]; simp [hR, he]
    simp only [hy, map_sub, LinearMap.sub_apply, h1, h2, h3]
    simp only [hc]
    rw [star_div₀, hst, star_ofNat]
    ring
  · simp only [hy, map_sub, hR, hey0, he, mul_zero, Finset.sum_const_zero, sub_zero]
  · simp only [hy, map_sub, LinearMap.sub_apply, hL, hez, mul_zero, Finset.sum_const_zero, sub_zero]
    rw [hsw, hzy0, star_zero]

def Wsp (e y : Fin r → S.V) (z : S.V) : Submodule E S.V :=
  LinearMap.ker (LinearMap.pi (Sum.elim (Sum.elim (fun a => S.hT (e a)) (fun a => S.hT (y a)))
    (fun _ : Unit => S.hT z)) : S.V →ₗ[E] ((Fin r ⊕ Fin r) ⊕ Unit → E))

theorem mem_Wsp {e y : Fin r → S.V} {z w : S.V} : w ∈ Wsp e y z ↔ IsW e y z w := by
  simp only [Wsp, LinearMap.mem_ker, funext_iff, LinearMap.pi_apply, Pi.zero_apply, Sum.forall,
    Sum.elim_inl, Sum.elim_inr, forall_const, IsW]
  tauto

theorem finrank_Wsp (e y : Fin r → S.V) (z : S.V) :
    finrank E S.V ≤ finrank E (Wsp e y z) + (2 * r + 1) := by
  have h := LinearMap.finrank_range_add_finrank_ker (LinearMap.pi (Sum.elim (Sum.elim (fun a => S.hT (e a))
    (fun a => S.hT (y a))) (fun _ : Unit => S.hT z)) : S.V →ₗ[E] ((Fin r ⊕ Fin r) ⊕ Unit → E))
  have h2 := Submodule.finrank_le (LinearMap.range (LinearMap.pi (Sum.elim (Sum.elim (fun a => S.hT (e a))
    (fun a => S.hT (y a))) (fun _ : Unit => S.hT z)) : S.V →ₗ[E] ((Fin r ⊕ Fin r) ⊕ Unit → E)))
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin, Fintype.card_unit] at h2
  rw [Wsp]
  omega

end Gen

section D7

variable (D : Formalism.BasicNotions.D7)

theorem dual_of_flag {N : ℕ} (hN : 0 < N) (F0 : FlagG (VS D) D.R.rS (N : D.host.E)) :
    ∃ y, Dual F0.e y F0.z N :=
  exists_dual_gen F0.e F0.z N hN F0.e_indep F0.e_iso F0.z_orth F0.z_norm

theorem posW {N : ℕ} (hN : 0 < N) {e y : Fin D.R.rS → (VS D).V} {z : (VS D).V} (h : Dual e y z N)
    (w : (VS D).V) (hw : IsW e y z w) (hw0 : w ≠ 0) (φ : D.host.E →+* ℂ) : 0 < (φ ((VS D).hT w w)).re := by
  have hτ : ∀ τ : D.host.E →+* ℂ, ∀ a, τ (star a) = starRingEnd ℂ (τ a) := fun τ => D.sp.cm.cmUnram.2.1 τ
  have hsemi : ∀ τ : D.host.E →+* ℂ, ∀ v, IsW e y z v → 0 ≤ (τ ((VS D).hT v v)).re := by
    intro τ v hv
    have hs := D.sp.Y_sig 0 τ
    rw [D.sp.baseSpace_signature_eq τ] at hs
    exact semidefG h hN τ (hτ τ) hs v hv
  refine lt_of_le_of_ne (hsemi φ w hw) fun h0 => hw0 ?_
  refine isoZeroG h hN φ (hτ φ) (hsemi φ) w hw ?_
  apply φ.injective
  rw [real_of φ (hτ φ) w, ← h0, Complex.ofReal_zero, map_zero]

theorem two_le_Wsp (e y : Fin D.R.rS → (VS D).V) (z : (VS D).V) : 2 ≤ finrank D.host.E (Wsp e y z) := by
  have hV : finrank D.host.E (VS D).V = D.R.k + D.R.m - 1 := by
    rw [(VS D).rank_eq, D.sp.Y_rank 0 (Nat.zero_le _)]
    simp [Formalism.BasicNotions.Ranks.rankY, Formalism.BasicNotions.Ranks.r]
  have hm2 := D.R.two_le_m
  obtain ⟨j, hj⟩ := D.R.m_even
  have hrS : 2 * D.R.rS + 1 = D.R.m - 1 := by
    unfold Formalism.BasicNotions.Ranks.rS
    rw [hj]
    omega
  have h1 := finrank_Wsp e y z
  rw [hV, hrS] at h1
  have hk := D.R.f_le_k
  have he : 0 < D.R.ord := D.R.ord_pos
  generalize finrank D.host.E (Wsp e y z) = w at h1 ⊢
  omega


variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem exists_W_vec {N : ℕ} (hN : 0 < N) {e y : Fin D.R.rS → (VS D).V} {z : (VS D).V} (h : Dual e y z N)
    (t : D.host.E) (ht : star t = t) (htp : Formalism.HermitianLattices.Ext.L3.TotPos t) :
    ∃ w : (VS D).V, IsW e y z w ∧ (VS D).hT w w = t := by
  let hW : Wsp e y z →ₗ⋆[D.host.E] Wsp e y z →ₗ[D.host.E] D.host.E :=
    ((VS D).hT.comp (Wsp e y z).subtype).compl₂ (Wsp e y z).subtype
  have hs : hW.IsSymm := ⟨fun x x' => (VS D).herm.eq x x'⟩
  have hd : Formalism.HermitianLattices.Ext.L3.IsTotPosDef hW := by
    intro x hx φ
    have hx' : (x : (VS D).V) ≠ 0 := fun h0 => hx (Subtype.ext h0)
    exact posW D hN h x (mem_Wsp.1 x.2) hx' φ
  obtain ⟨x, hx⟩ := Formalism.HermitianLattices.Ext.L3.exists_vec_of_hermRep Formalism.HermitianLattices.Ext.L3.hermRepUnram D.sp.cm.cmUnram hs hd
    (two_le_Wsp D e y z) t ht htp
  exact ⟨x, mem_Wsp.1 x.2, hx⟩

end D7

end Formalism.L2.SG.Pf.Cnt.R1
