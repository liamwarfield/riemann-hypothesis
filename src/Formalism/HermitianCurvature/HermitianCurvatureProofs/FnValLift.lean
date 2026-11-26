module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RaisingCompactSupport

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.ArelStar
open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.WordCorrespondence

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.P.PBH

section core

variable {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] {T : V →ₗ[ℂ] V'}
  {S : Type} [Fintype S] [DecidableEq S]

theorem rel_inv {a b : Pr V} {a' b' : Pr V'} (h : Rel T a a') (hab : a * b = 1) (hba : b * a = 1)
    (hab' : a' * b' = 1) (hba' : b' * a' = 1) : Rel T b b' := by
  have e1 : a.1 * b.1 = 1 := congrArg Prod.fst hab
  have e2 : b'.1 * a'.1 = 1 := congrArg Prod.fst hba'
  have e3 : a.2.unop * b.2.unop = 1 := congrArg (fun x : Pr V => x.2.unop) hba
  have e4 : b'.2.unop * a'.2.unop = 1 := congrArg (fun x : Pr V' => x.2.unop) hab'
  refine ⟨LinearMap.ext fun v => ?_, LinearMap.ext fun v => ?_⟩
  · have i1 : a.1 (b.1 v) = v := by simpa using LinearMap.congr_fun e1 v
    have i2 : b'.1 (a'.1 (T (b.1 v))) = T (b.1 v) := by simpa using LinearMap.congr_fun e2 (T (b.1 v))
    have i3 : a'.1 (T (b.1 v)) = T (a.1 (b.1 v)) := LinearMap.congr_fun h.1 (b.1 v)
    show b'.1 (T v) = T (b.1 v)
    rw [← i2, i3, i1]
  · have i1 : a.2.unop (b.2.unop v) = v := by simpa using LinearMap.congr_fun e3 v
    have i2 : b'.2.unop (a'.2.unop (T (b.2.unop v))) = T (b.2.unop v) := by
      simpa using LinearMap.congr_fun e4 (T (b.2.unop v))
    have i3 : a'.2.unop (T (b.2.unop v)) = T (a.2.unop (b.2.unop v)) := LinearMap.congr_fun h.2 (b.2.unop v)
    show b'.2.unop (T v) = T (b.2.unop v)
    rw [← i2, i3, i1]

theorem arel_star' {M : SlopeTestRemainingChoices S (Pr V)} {M' : SlopeTestRemainingChoices S (Pr V')} (h : ARel T M M') : ARel T (star M) (star M') :=
  fun x y => by
    rw [Matrix.star_apply, Matrix.star_apply]
    exact rel_star (h y x)

theorem arel_pow' {M : SlopeTestRemainingChoices S (Pr V)} {M' : SlopeTestRemainingChoices S (Pr V')} (h : ARel T M M') : ∀ n : ℕ, ARel T (M ^ n) (M' ^ n)
  | 0 => by rw [pow_zero, pow_zero]; exact arel_one
  | n + 1 => by rw [pow_succ, pow_succ]; exact arel_mul (arel_pow' h n) h

theorem brel_of {a b c d : SlopeTestRemainingChoices S (Pr V)} {a' b' c' d' : SlopeTestRemainingChoices S (Pr V')} (h1 : ARel T a a') (h2 : ARel T b b')
    (h3 : ARel T c c') (h4 : ARel T d d') : BRel T !![a, b; c, d] !![a', b'; c', d'] := by
  intro i j
  fin_cases i <;> fin_cases j
  · exact h1
  · exact h2
  · exact h3
  · exact h4

structure Gen {r₀ r₁ : ℕ} (T : V →ₗ[ℂ] V') (L₀ : LevelData (Pr V) r₀) (L : LevelData (Pr V') r₁) : Prop where
  ζ : Rel T L₀.ζ L.ζ
  ζi : Rel T L₀.ζi L.ζi
  ζb : Rel T L₀.ζb L.ζb
  ζbi : Rel T L₀.ζbi L.ζbi
  GG : Rel T L₀.GG L.GG
  GGi : Rel T L₀.GGi L.GGi
  TT : L₀.TT = L.TT

abbrev Corr (T : V →ₗ[ℂ] V') (inv0 : Set ℂ) (f₀ : FrameData S (Pr V)) (f : FrameData S (Pr V')) : Prop :=
  ARel T f₀.F f.F ∧ ARel T f₀.Fi f.Fi ∧ ARel T f₀.c f.c ∧ ARel T f₀.ci f.ci ∧ (∀ Y, ARel T (f₀.x Y) (f.x Y)) ∧
    (∀ Y ∈ inv0, ARel T (f₀.xi Y) (f.xi Y)) ∧ (∀ Y, BRel T (f₀.TT Y) (f.TT Y)) ∧ f₀.N = f.N ∧ f₀.q = f.q ∧
    f₀.inv = f.inv ∧ f₀.inv ⊆ inv0

variable {r₀ r₁ : ℕ} {L₀ : LevelData (Pr V) r₀} {L : LevelData (Pr V') r₁}

theorem l_eq {r : ℕ} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] (L : LevelData A r) (f : FrameData S A)
    (hf : IsFrame L f) (Y : ℂ) (hY : Y ∈ f.inv) (hY1 : Y + 1 ∈ f.inv) :
    f.l L Y = f.xi Y * io L.GGi * f.F * f.TT Y 1 0 * f.Fi := by
  have h := hf.frame_l Y hY hY1
  have hio : (io L.GGi : SlopeTestRemainingChoices S A) * io L.GG = 1 := by simp only [io, ← map_mul, L.GGi_GG, map_one]
  have hx := (hf.x_xi Y hY).2
  calc f.l L Y = (f.xi Y * f.x Y) * f.l L Y * (f.F * f.Fi) := by rw [hx, hf.F_Fi, one_mul, mul_one]
    _ = f.xi Y * ((io L.GGi * io L.GG) * f.x Y * f.l L Y * f.F) * f.Fi := by
      rw [hio]; simp only [one_mul, mul_assoc]
    _ = f.xi Y * io L.GGi * (io L.GG * f.x Y * f.l L Y * f.F) * f.Fi := by simp only [mul_assoc]
    _ = f.xi Y * io L.GGi * f.F * f.TT Y 1 0 * f.Fi := by rw [← h]; simp only [mul_assoc]

theorem l_rel (G : Gen T L₀ L) {inv0 : Set ℂ} {f₀ : FrameData S (Pr V)} {f : FrameData S (Pr V')}
    (hc : Corr T inv0 f₀ f) (hf₀ : IsFrame L₀ f₀) (hf : IsFrame L f) (Y : ℂ) (hY : Y ∈ f₀.inv)
    (hY1 : Y + 1 ∈ f₀.inv) : ARel T (f₀.l L₀ Y) (f.l L Y) := by
  obtain ⟨hF, hFi, -, -, -, hxi, hTT, -, -, hinv, hsub⟩ := hc
  rw [l_eq L₀ f₀ hf₀ Y hY hY1, l_eq L f hf Y (hinv ▸ hY) (hinv ▸ hY1)]
  exact arel_mul (arel_mul (arel_mul (arel_mul (hxi Y (hsub hY)) (arel_io G.GGi)) hF) (hTT Y 1 0)) hFi

theorem m_rel (G : Gen T L₀ L) {inv0 : Set ℂ} {f₀ : FrameData S (Pr V)} {f : FrameData S (Pr V')}
    (hc : Corr T inv0 f₀ f) (hf₀ : IsFrame L₀ f₀) (hf : IsFrame L f) (Y : ℂ) (hY : Y - 1 ∈ f₀.inv)
    (hY1 : Y ∈ f₀.inv) : ARel T (f₀.m L₀ Y) (f.m L Y) := by
  have hl := l_rel G hc hf₀ hf (Y - 1) hY (by rw [sub_add_cancel]; exact hY1)
  obtain ⟨-, -, hc', hci, -, -, -, hN, -, -, -⟩ := hc
  have hwt : ARel T (wt (S := S) L₀) (wt L) := arel_io (rel_mul (rel_mul G.ζ G.ζb) G.GGi)
  have hwti : ARel T (wti (S := S) L₀) (wti L) := arel_io (rel_mul (rel_mul G.GG G.ζi) G.ζbi)
  unfold FrameData.m FrameData.d FrameData.di
  rw [hN]
  exact arel_mul (arel_mul (arel_mul hci (arel_pow' hwti _)) (arel_star' hl)) (arel_mul (arel_pow' hwt _) hc')

theorem corr_plus (G : Gen T L₀ L) {inv0 : Set ℂ} {f₀ : FrameData S (Pr V)} {f : FrameData S (Pr V')}
    (hc : Corr T inv0 f₀ f) (hf₀ : IsFrame L₀ f₀) (hf : IsFrame L f) (a : S) (Ya : ℂ) (h1 : Ya ∈ f₀.inv)
    (h2 : Ya + 1 ∈ f₀.inv) : Corr T inv0 (f₀.plus L₀ a Ya) (f.plus L a Ya) := by
  have hl := l_rel G hc hf₀ hf Ya h1 h2
  obtain ⟨hF, hFi, hc', hci, hx, hxi, hTT, hN, hq, hinv, hsub⟩ := hc
  dsimp only [FrameData.plus]
  refine ⟨?_, ?_, ?_, ?_, fun Y => ?_, fun Y hY => ?_, fun Y => ?_, by rw [hN], by rw [hq], by rw [hinv],
    Set.inter_subset_left.trans hsub⟩
  · exact arel_mul (arel_ins a (brel_mul (brel_of (arel_io G.ζi) arel_zero arel_zero (arel_io G.ζbi))
      (brel_of arel_one arel_zero (arel_mul (arel_io G.GG) hl) (arel_io G.GG)))) hF
  · exact arel_mul hFi (arel_ins a (brel_mul (brel_of arel_one arel_zero (arel_neg hl) (arel_io G.GGi))
      (brel_of (arel_io G.ζ) arel_zero arel_zero (arel_io G.ζb))))
  · rw [hq]
    exact arel_mul hc' (arel_ins a (brel_of (arel_smul _ (hxi _ (hsub h2))) arel_zero arel_zero (hx Ya)))
  · rw [hq]
    exact arel_mul hci (arel_ins a (brel_of (arel_smul _ (hx _)) arel_zero arel_zero (hxi _ (hsub h1))))
  · exact arel_mul (hx Y) (arel_ins a (brel_of (arel_smul _ arel_one) arel_zero arel_zero arel_one))
  · exact arel_mul (hxi Y hY) (arel_ins a (brel_of (arel_smul _ arel_one) arel_zero arel_zero arel_one))
  · exact brel_mul (hTT Y) (block_relation_height a _)

theorem corr_minus (G : Gen T L₀ L) {inv0 : Set ℂ} {f₀ : FrameData S (Pr V)} {f : FrameData S (Pr V')}
    (hc : Corr T inv0 f₀ f) (hf₀ : IsFrame L₀ f₀) (hf : IsFrame L f) (b : S) (Yb : ℂ) (h1 : Yb ∈ f₀.inv)
    (h0 : Yb - 1 ∈ f₀.inv) : Corr T inv0 (f₀.minus L₀ b Yb) (f.minus L b Yb) := by
  have hm := m_rel G hc hf₀ hf Yb h0 h1
  obtain ⟨hF, hFi, hc', hci, hx, hxi, hTT, hN, hq, hinv, hsub⟩ := hc
  dsimp only [FrameData.minus]
  refine ⟨?_, ?_, ?_, ?_, fun Y => ?_, fun Y hY => ?_, fun Y => ?_, by rw [hN], by rw [hq], by rw [hinv],
    Set.inter_subset_left.trans hsub⟩
  · exact arel_mul (arel_ins b (brel_mul (brel_of (arel_io G.ζbi) arel_zero arel_zero (arel_io G.ζi))
      (brel_of arel_one arel_zero (arel_mul (arel_io G.GG) hm) (arel_io G.GG)))) hF
  · exact arel_mul hFi (arel_ins b (brel_mul (brel_of arel_one arel_zero (arel_neg hm) (arel_io G.GGi))
      (brel_of (arel_io G.ζb) arel_zero arel_zero (arel_io G.ζ))))
  · rw [hq]
    exact arel_mul hc' (arel_ins b (brel_of (arel_smul _ (hxi _ (hsub h0))) arel_zero arel_zero (hx Yb)))
  · rw [hq]
    exact arel_mul hci (arel_ins b (brel_of (arel_smul _ (hx _)) arel_zero arel_zero (hxi _ (hsub h1))))
  · exact arel_mul (hx Y) (arel_ins b (brel_of (arel_smul _ arel_one) arel_zero arel_zero arel_one))
  · exact arel_mul (hxi Y hY) (arel_ins b (brel_of (arel_smul _ arel_one) arel_zero arel_zero arel_one))
  · exact brel_mul (block_relation_twisted_height b _) (hTT Y)

variable {st₀ : Start (Pr V)} {st : Start (Pr V')}

theorem x_rel (G : Gen T L₀ L) (hQ : ∀ Y, MRel T (st₀.QQ Y) (st.QQ Y)) (hs₀ : IsLevelStart L₀ st₀)
    (hs : IsLevelStart L st) (Y : ℂ) : Rel T (st₀.x Y) (st.x Y) := by
  have e₀ : st₀.x Y = L₀.GGi * st₀.QQ Y 1 1 := by rw [hs₀.tau, ← mul_assoc, L₀.GGi_GG, one_mul]
  have e : st.x Y = L.GGi * st.QQ Y 1 1 := by rw [hs.tau, ← mul_assoc, L.GGi_GG, one_mul]
  rw [e₀, e]
  exact rel_mul G.GGi (hQ Y 1 1)

theorem corr_word (G : Gen T L₀ L) (hQ : ∀ Y, MRel T (st₀.QQ Y) (st.QQ Y)) (hq : st₀.q = st.q)
    (hinv : st₀.inv = st.inv) (hL₀ : IsStarLevel L₀) (hL : IsStarLevel L) (hs₀ : IsLevelStart L₀ st₀)
    (hs : IsLevelStart L st) :
    ∀ w : List (Letter ℂ S), AdmRec L₀ st₀ w → AdmRec L st w →
      Corr T st₀.inv (ofWord L₀ st₀ w) (ofWord L st w) := by
  intro w
  induction w with
  | nil =>
    intro _ _
    refine ⟨arel_one, arel_one, arel_one, arel_one, fun Y => arel_io (x_rel G hQ hs₀ hs Y), fun Y hY => ?_,
      fun Y => brel_lift0 (hQ Y), rfl, hq, hinv, subset_rfl⟩
    exact arel_io (rel_inv (x_rel G hQ hs₀ hs Y) (hs₀.x_xi Y hY).1 (hs₀.x_xi Y hY).2
      (hs.x_xi Y (hinv ▸ hY)).1 (hs.x_xi Y (hinv ▸ hY)).2)
  | cons l w ih =>
    intro h₀ h
    unfold AdmRec at h₀ h
    obtain ⟨hw₀, -, -, hp0, hp1, hrest⟩ := h₀
    obtain ⟨hw, -⟩ := h
    have hf₀ := Formalism.FourierDecayAlt.P.frame_of_recursive_word (Pr V) S r₀ L₀ st₀ w hL₀ hs₀ hw₀
    have hf := Formalism.FourierDecayAlt.P.frame_of_recursive_word (Pr V') S r₁ L st w hL hs hw
    by_cases hp : l.plus
    · simpa only [ofWord, ite_eq_left hp] using
        corr_plus G (ih hw₀ hw) hf₀ hf l.intersection_update_fsHerm_neg_one l.pt hp0 hp1
    · rw [ite_eq_right hp] at hrest
      simpa only [ofWord, ite_eq_right hp] using
        corr_minus G (ih hw₀ hw) hf₀ hf l.intersection_update_fsHerm_neg_one l.pt hp0 hrest.1

theorem act_frame (G : Gen T L₀ L) (hQ : ∀ Y, MRel T (st₀.QQ Y) (st.QQ Y)) (hq : st₀.q = st.q)
    (hinv : st₀.inv = st.inv) (hL₀ : IsStarLevel L₀) (hL : IsStarLevel L) (hs₀ : IsLevelStart L₀ st₀)
    (hs : IsLevelStart L st) (w : List (Letter ℂ S)) (h₀ : admitted st₀ w) (h : admitted st w) (Ψ : Ix S → V) (e : Ix S) :
    T (∑ b, ((ofWord L₀ st₀ w).F e b).1 (Ψ b)) = ∑ b, ((ofWord L st w).F e b).1 (T (Ψ b)) :=
  act_tr (corr_word G hQ hq hinv hL₀ hL hs₀ hs w
    (Formalism.FourierDecayAlt.P.admissible_rec_of_admissible (Pr V) S r₀ L₀ st₀ w h₀)
    (Formalism.FourierDecayAlt.P.admissible_rec_of_admissible (Pr V') S r₁ L st w h)).1 Ψ e

end core

end Formalism.FourierDecayAlt.P.WordCorrespondence
end
end

open Matrix MeasureTheory
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.WordCorrespondence

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.PBH

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section lift

variable {k i r' : ℕ}

theorem ιLev_apply_lev (g : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) (p q : Fin (2 * r' + k + 1)) :
    ιLev k i r' g ⟨p.val + i, by omega⟩ ⟨q.val + i, by omega⟩ = g p q := by
  have hp := p.isLt
  have hq := q.isLt
  simp only [ιLev]
  rw [dite_eq_left ⟨by omega, by omega⟩, dite_eq_left ⟨by omega, by omega⟩]
  congr 1 <;> ext <;> simp

theorem ιLev_inj' {g g' : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ}
    (h : ιLev k i r' g = ιLev k i r' g') : g = g' := by
  ext p q
  have := congrFun (congrFun h ⟨p.val + i, by omega⟩) ⟨q.val + i, by omega⟩
  rwa [ιLev_apply_lev, ιLev_apply_lev] at this

theorem contDiff_ιLev' : ContDiff ℝ ∞ (ιLev k i r') := by
  refine contDiff_pi.2 fun p => contDiff_pi.2 fun q => ?_
  unfold ιLev
  split_ifs
  · exact (contDiff_apply ℝ (fun _ => ℂ) _).comp (contDiff_apply ℝ (fun _ => (Fin (2 * r' + k + 1) → ℂ)) _)
  all_goals exact contDiff_const

theorem zeta_lift (z z' : Fin (2 * r' + k + 1) → ℂ) (g : Mx k r') :
    zetaL k (i + r') (liftVec k i r' z) (liftVec k i r' z') (Fin.last (i + r')) (ιLev k i r' g) =
      zetaL k r' z z' (Fin.last r') g := by
  unfold zetaL
  rw [fvec_last, fvec_last, fvec_last, fvec_last, PIQnLT.mulVec_liftVec, PIQnLT.herm_liftVec]

theorem tz_lift (z : Fin (2 * r' + k + 1) → ℂ) : Tz k (i + r') (liftVec k i r' z) = Tz k r' z := by
  unfold Tz; rw [PIQnLT.herm_liftVec]

theorem ggl_lift (z z' : Fin (2 * r' + k + 1) → ℂ) (g : Mx k r') :
    GGl k (i + r') (liftVec k i r' z) (liftVec k i r' z') (ιLev k i r' g) = GGl k r' z z' g := by
  unfold GGl; rw [zeta_lift, tz_lift, tz_lift]

theorem fnVal_lift (z z' : Fin (2 * r' + k + 1) → ℂ) (j : Fin 6) (g : Mx k r') :
    fnVal k (i + r') (liftVec k i r' z) (liftVec k i r' z') j (ιLev k i r' g) = fnVal k r' z z' j g := by
  unfold fnVal
  split <;> simp only [zeta_lift, ggl_lift]

theorem glev_lift (hr' : r' = 0) (g : Mx k r') :
    ιLev k i r' g ∈ Glev k (i + r') (Fin.last (i + r')) ↔ g ∈ Glev k r' (Fin.last r') := by
  have hl : (Fin.last (i + r')) = (⟨i, by omega⟩ : Fin (i + r' + 1)) := Fin.ext (by simp; omega)
  have himg := QnGlevImageW.glevImage_of PI.QnLevBasicsW.level_group_homomorphism PI.QnLevBasicsW.level_group_unitary_hermitian k i r'
  have hG : ∀ x : Mx k r', x ∈ Glev k r' (Fin.last r') ↔ x ∈ UH (Hpk k r') := fun x =>
    ⟨fun h => h.1, fun h => ⟨h, fun a _ => absurd a.isLt (by omega)⟩⟩
  rw [hl, himg, hG]
  constructor
  · rintro ⟨g0, hg0, e⟩
    rwa [← ιLev_inj' e]
  · intro hg
    exact ⟨g, hg, rfl⟩

theorem domR_lift (hr' : r' = 0) {c : Fin (i + r') → ℂ} (hc : c ∈ OmX (i + r')) (zs zs' : Fin (2 * r' + k + 1) → ℂ)
    (c' : Fin r' → ℂ) (g : Mx k r') :
    (c, ιLev k i r' g) ∈ DomR k (i + r') (liftVec k i r' zs) (liftVec k i r' zs') ↔ (c', g) ∈ DomR k r' zs zs' := by
  show (c ∈ OmX (i + r') ∧ ιLev k i r' g ∈ Glev k (i + r') (Fin.last (i + r')) ∧
      0 < GGl k (i + r') (liftVec k i r' zs) (liftVec k i r' zs') (ιLev k i r' g)) ↔
    (c' ∈ OmX r' ∧ g ∈ Glev k r' (Fin.last r') ∧ 0 < GGl k r' zs zs' g)
  rw [glev_lift hr', ggl_lift]
  exact ⟨fun h => ⟨fun l => absurd l.isLt (by omega), h.2⟩, fun h => ⟨hc, h.2⟩⟩

def rsF {E : Type*} (c : Fin (i + r') → ℂ) (Φ : Fn k (i + r') E) : Fn k r' E := fun _ g => Φ c (ιLev k i r' g)

end lift

section rs

variable {k i r' : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem rs_mem (hr' : r' = 0) {c : Fin (i + r') → ℂ} (hc : c ∈ OmX (i + r')) {zs zs' : Fin (2 * r' + k + 1) → ℂ}
    {π : Mx k (i + r') → (Wp →L[ℂ] Wp)} {π' : Mx k (i + r') → (Wq →L[ℂ] Wq)} {Φ : Fn k (i + r') (Wq →L[ℂ] Wp)}
    (hΦ : Φ ∈ RadSp k (i + r') (liftVec k i r' zs) (liftVec k i r' zs') π π') :
    rsF c Φ ∈ RadSp k r' zs zs' (fun y => π (ιLev k i r' y)) (fun y => π' (ιLev k i r' y)) := by
  obtain ⟨h0, hs, he⟩ := hΦ
  refine ⟨fun x hx => h0 _ fun h => hx ((domR_lift hr' hc zs zs' x.1 x.2).1 h), fun x₀ hx₀ => ?_,
    fun x hx h hh h' hh' => ?_⟩
  · obtain ⟨U, F, hU, hxU, hF, hΦF⟩ := hs _ ((domR_lift hr' hc zs zs' x₀.1 x₀.2).2 hx₀)
    let e : (Fin r' → ℂ) × Mx k r' → (Fin (i + r') → ℂ) × Mx k (i + r') := fun x => (c, ιLev k i r' x.2)
    have he_c : ContDiff ℝ ∞ e := contDiff_const.prodMk (contDiff_ιLev'.comp contDiff_snd)
    refine ⟨e ⁻¹' U, F ∘ e, hU.preimage he_c.continuous, hxU, hF.comp he_c.contDiffOn (fun x hx => hx),
      fun x hx hg => ?_⟩
    exact hΦF (e x) hx ((glev_lift hr' x.2).2 hg)
  · have hx' := (domR_lift hr' hc zs zs' x.1 x.2).2 hx
    show Φ c (ιLev k i r' (h * x.2 * h')) = _
    rw [(PI.QnLevBasicsW.level_group_homomorphism k i r').2, (PI.QnLevBasicsW.level_group_homomorphism k i r').2]
    exact he _ hx' _ (PI.QnLevBasicsW.level_group_unitary_weyl k i r' zs h hh) _ (PI.QnLevBasicsW.level_group_unitary_weyl k i r' zs' h' hh')

def rsL (hr' : r' = 0) {c : Fin (i + r') → ℂ} (hc : c ∈ OmX (i + r')) (zs zs' : Fin (2 * r' + k + 1) → ℂ)
    (π : Mx k (i + r') → (Wp →L[ℂ] Wp)) (π' : Mx k (i + r') → (Wq →L[ℂ] Wq)) :
    RadSp k (i + r') (liftVec k i r' zs) (liftVec k i r' zs') π π' →ₗ[ℂ]
      RadSp k r' zs zs' (fun y => π (ιLev k i r' y)) (fun y => π' (ιLev k i r' y)) where
  toFun Φ := ⟨rsF c (Φ : Fn k (i + r') (Wq →L[ℂ] Wp)), rs_mem hr' hc Φ.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (hr' : r' = 0) {c : Fin (i + r') → ℂ} (hc : c ∈ OmX (i + r')) {zs zs' : Fin (2 * r' + k + 1) → ℂ}
  {π : Mx k (i + r') → (Wp →L[ℂ] Wp)} {π' : Mx k (i + r') → (Wq →L[ℂ] Wq)}

theorem t_rs (X₀ : ActualOps k (i + r') (liftVec k i r' zs) (liftVec k i r' zs') π π')
    (X : ActualOps k r' zs zs' (fun y => π (ιLev k i r' y)) (fun y => π' (ιLev k i r' y))) (Y : ℂ) (a b : Fin 2)
    (Φ : RadSp k (i + r') (liftVec k i r' zs) (liftVec k i r' zs') π π') :
    X.t Y a b (rsL hr' hc zs zs' π π' Φ) = rsL hr' hc zs zs' π π' (X₀.t Y a b Φ) := by
  apply Subtype.ext
  funext c' g
  by_cases hx : (c', g) ∈ DomR k r' zs zs'
  · have hx' := (domR_lift hr' hc zs zs' c' g).2 hx
    rw [X.t_apply Y a b _ (c', g) hx]
    show _ = (X₀.t Y a b Φ : Fn k (i + r') (Wq →L[ℂ] Wp)) c (ιLev k i r' g)
    rw [X₀.t_apply Y a b Φ (c, ιLev k i r' g) hx']
    have hl : (Fin.last (i + r')) = (⟨i, by omega⟩ : Fin (i + r' + 1)) := Fin.ext (by simp; omega)
    have h0 : (Fin.last r') = (0 : Fin (r' + 1)) := Fin.ext (by simp; omega)
    rw [hl, h0]
    exact (Formalism.FourierDecayAlt.P.level_transfer _ k i r' zs zs' Y a b ((Φ : Fn k (i + r') (Wq →L[ℂ] Wp)) c) g
      hx.2.1.1).symm
  · rw [(X.t Y a b (rsL hr' hc zs zs' π π' Φ)).2.1 (c', g) hx]
    exact ((X₀.t Y a b Φ).2.1 _ (fun h => hx ((domR_lift hr' hc zs zs' c' g).1 h))).symm

theorem fn_rs (X₀ : ActualOps k (i + r') (liftVec k i r' zs) (liftVec k i r' zs') π π')
    (X : ActualOps k r' zs zs' (fun y => π (ιLev k i r' y)) (fun y => π' (ιLev k i r' y))) (j : Fin 6)
    (Φ : RadSp k (i + r') (liftVec k i r' zs) (liftVec k i r' zs') π π') :
    X.fn j (rsL hr' hc zs zs' π π' Φ) = rsL hr' hc zs zs' π π' (X₀.fn j Φ) := by
  apply Subtype.ext
  funext c' g
  by_cases hx : (c', g) ∈ DomR k r' zs zs'
  · have hx' := (domR_lift hr' hc zs zs' c' g).2 hx
    rw [X.fn_apply j _ (c', g) hx]
    show _ = (X₀.fn j Φ : Fn k (i + r') (Wq →L[ℂ] Wp)) c (ιLev k i r' g)
    rw [X₀.fn_apply j Φ (c, ιLev k i r' g) hx', fnVal_lift]
    rfl
  · rw [(X.fn j (rsL hr' hc zs zs' π π' Φ)).2.1 (c', g) hx]
    exact ((X₀.fn j Φ).2.1 _ (fun h => hx ((domR_lift hr' hc zs zs' c' g).1 h))).symm

end rs

end Formalism.FourierDecayAlt.P.WordCorrespondence
