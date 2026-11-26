module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.UnitCons

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.TwistC
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NatMulMem
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SgmPinvEq
noncomputable section

open scoped Classical

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.PairVal Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.PtCell Formalism.L2.SG.RealObj
  Formalism.L2.SG.Pf.BlockPermutation Formalism.L2.SG.Pf.StabIntSh

namespace Formalism.L2.SG.Pf.StabIntLat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (w : Point D.host.E (D.R.rS + 1))

theorem qbar_qbar (q : FreeE w) : qbar w (qbar w q) = q := by
  apply Subtype.ext
  simp only [qbar, pinv_pinv]

theorem hgt_qbar (q : FreeE w) : hgt w (qbar w q) = hgt w q := by
  unfold hgt qbar
  have h1 := pinv_add w q.1.1 q.1.2 q.2.2
  have h2 : q.1.1.val < q.1.2.val := q.2.1
  simp only
  omega

theorem sgm_pinv_eq (a c : Fin (D.R.rS + 1)) (hs : blkOf w.1 a.val = blkOf w.1 c.val) :
    sgm (pinv w c) (pinv w a) = (sgm a c : D.host.E) := by
  have h := sgm_pinv w a c hs
  rcases sgm_cases a c with e | e
  · rw [e, one_mul] at h; rw [h, e]
  · rw [e] at h ⊢; linear_combination -h

theorem sgq_qbar (q : FreeE w) : sgq w (qbar w q) = sgq w q :=
  sgm_pinv_eq w q.1.1 q.1.2 q.2.2

theorem Xinv_q (y : FreeE w → D.host.E) (q : FreeE w) :
    (Xmat w y)⁻¹ q.1.1 q.1.2 = cf w y q - y q := by
  have h := inv_diff (Xmat_upU w y) (Xmat_upU w (trunc w y (hgt w q))) q.2.1 (fun i j hij hh => by
    by_cases hb : i < j ∧ blkOf w.1 i.val = blkOf w.1 j.val
    · simp only [Xmat, ne_of_lt hij, if_false, dif_pos hb, trunc]
      rw [if_pos (show hgt w ⟨(i, j), hb⟩ < hgt w q from hh)]
    · simp only [Xmat, ne_of_lt hij, if_false, dif_neg hb])
  rw [Xmat_q, Xmat_q] at h
  have h0 : trunc w y (hgt w q) q = 0 := by unfold trunc; rw [if_neg (lt_irrefl _)]
  rw [h0] at h
  unfold cf
  linear_combination h

theorem cf_mem (y : FreeE w → D.host.E) (q : FreeE w)
    (hy : ∀ p, hgt w p < hgt w q → y p ∈ ddPow D (hgt w p)) : cf w y q ∈ ddPow D (hgt w q) := by
  unfold cf
  refine grD_inv (Xmat_upU w _) (Xmat_grD w _ fun p => ?_) q.1.1 q.1.2 (le_of_lt q.2.1)
  unfold trunc
  split_ifs with h
  · exact hy p h
  · exact FractionalIdeal.zero_mem _

theorem E_q (y : FreeE w → D.host.E) (q : FreeE w) :
    (Xmat w y - Psi w (Xmat w y)⁻¹) q.1.1 q.1.2 =
      y q - sgq w q * D.conjF (cf w y (qbar w q) - y (qbar w q)) := by
  rw [Matrix.sub_apply, Xmat_q]
  have h := Xinv_q w y (qbar w q)
  simp only [Psi]
  rw [show (Xmat w y)⁻¹ (pinv w q.1.2) (pinv w q.1.1) = cf w y (qbar w q) - y (qbar w q) from h]
  rfl

theorem condX_third (X : MatR D) (a c : Fin (D.R.rS + 1)) (hs : blkOf w.1 a.val = blkOf w.1 c.val) :
    X (pinv w c) (pinv w a) - D.conjF (bt D X⁻¹ a c) = (X - Psi w X⁻¹) (pinv w c) (pinv w a) := by
  rw [Matrix.sub_apply]
  simp only [Psi, pinv_pinv]
  rw [sgm_pinv_eq w a c hs]
  simp only [bt, sgm, map_mul, map_pow, map_neg, map_one]
  ring

theorem bt_mem {X : MatR D} (hG : GrD X) (a c : Fin (D.R.rS + 1)) (hac : a < c) :
    bt D X a c ∈ ddPow D (c.val - a.val) := by
  have h := hG a c (le_of_lt hac)
  rw [show bt D X a c = sgm a c * X a c by simp only [bt, sgm]; ring]
  rcases sgm_cases a c with e | e
  · rw [e, one_mul]; exact h
  · rw [e, neg_one_mul]; exact (ddPow D _ : Submodule (𝓞 D.host.E) D.host.E).neg_mem h

theorem condX_iff (y : FreeE w → D.host.E) :
    CondX w (Xmat w y) ↔ (∀ q, y q ∈ ddPow D (hgt w q)) ∧
      ∀ q, (Xmat w y - Psi w (Xmat w y)⁻¹) q.1.1 q.1.2 ∈ qdPow D (hgt w q) := by
  constructor
  · intro h
    have hy : ∀ q, y q ∈ ddPow D (hgt w q) := by
      intro q
      obtain ⟨h1, -, -⟩ := h (qbar w q).1.1 (qbar w q).1.2 (qbar w q).2.1 (qbar w q).2.2
      have e := hgt_qbar w q
      unfold hgt at e
      simp only [qbar, pinv_pinv] at h1 e
      rw [e, Xmat_q] at h1
      exact h1
    refine ⟨hy, fun q => ?_⟩
    obtain ⟨-, -, h3⟩ := h (qbar w q).1.1 (qbar w q).1.2 (qbar w q).2.1 (qbar w q).2.2
    rw [condX_third w _ _ _ (qbar w q).2.2] at h3
    have e := hgt_qbar w q
    unfold hgt at e
    simp only [qbar, pinv_pinv] at h3 e
    rw [e] at h3
    exact h3
  · rintro ⟨hy, hE⟩ a c hac hs
    have hG := grD_inv (Xmat_upU w y) (Xmat_grD w y hy)
    set p : FreeE w := qbar w ⟨(a, c), hac, hs⟩ with hp
    have hpe : hgt w p = c.val - a.val := hgt_qbar w _
    have hp1 : Xmat w y (pinv w c) (pinv w a) = y p := Xmat_q w y p
    refine ⟨?_, bt_mem hG a c hac, ?_⟩
    · rw [hp1, ← hpe]; exact hy p
    · rw [condX_third w _ a c hs, ← hpe]; exact hE p

end Formalism.L2.SG.Pf.StabIntLat
end
end

noncomputable section

open scoped Classical

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.PairVal Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.PtCell Formalism.L2.SG.RealObj
  Formalism.L2.SG.Pf.BlockPermutation Formalism.L2.SG.Pf.StabIntSh

namespace Formalism.L2.SG.Pf.StabIntLat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (w : Point D.host.E (D.R.rS + 1))

theorem upper_qbar {q : FreeE w} (hu : upperM w q) : ¬ selfP w (qbar w q) ∧ ¬ upperM w (qbar w q) := by
  unfold selfP upperM at *
  rw [qbar_qbar]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have : qbar w q = q := h.symm
    rw [this] at hu; exact lt_irrefl _ hu
  · exact lt_asymm hu h

theorem lower_qbar {q : FreeE w} (hs : ¬ selfP w q) (hu : ¬ upperM w q) : upperM w (qbar w q) := by
  unfold selfP upperM at *
  rw [qbar_qbar]
  rcases lt_or_eq_of_le (not_lt.1 hu) with h | h
  · exact h
  · exfalso; apply hs
    apply Subtype.ext
    have h2 : pinv w q.1.2 = q.1.1 := h.symm
    have h3 : q.1.2 = pinv w q.1.1 := by rw [← h2, pinv_pinv]
    simp only [qbar]
    rw [h2, ← h3]

theorem hgt_le (q : FreeE w) : hgt w q ≤ D.R.rS := by
  unfold hgt; have := q.1.2.isLt; omega

section Main

variable (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (hA : ∀ q, Agree δ M q)

theorem sgq_cases (q : FreeE w) : sgq w q = (1 : D.host.E) ∨ sgq w q = -1 := sgm_cases q.1.1 q.1.2

theorem sgq_sq (q : FreeE w) : sgq w q * sgq w q = (1 : D.host.E) := by
  rcases sgq_cases w q with e | e <;> rw [e] <;> ring

include hA in
theorem sg_dd {h : ℕ} (hk : h ≤ D.R.rS) (q : FreeE w) {x : D.host.E} (hx : x ∈ ddPow D h) :
    sgq w q * D.conjF x ∈ ddPow D h := by
  have := dd_conj δ M hA hk hx
  rcases sgq_cases w q with e | e
  · rw [e, one_mul]; exact this
  · rw [e, neg_one_mul]; exact (ddPow D h : Submodule (𝓞 D.host.E) D.host.E).neg_mem this

include hA in
theorem sg_qd {h : ℕ} (hk : h ≤ D.R.rS) (q : FreeE w) {x : D.host.E} (hx : x ∈ qdPow D h) :
    sgq w q * D.conjF x ∈ qdPow D h := by
  have := qd_conj δ M hA hk hx
  rcases sgq_cases w q with e | e
  · rw [e, one_mul]; exact this
  · rw [e, neg_one_mul]; exact (qdPow D h : Submodule (𝓞 D.host.E) D.host.E).neg_mem this

theorem gS_mul_qd (h : ℕ) {x : D.host.E} (hx : x ∈ ddPow D h) : ((gS D : ℕ) : D.host.E) * x ∈ qdPow D h := by
  rw [qdPow_mem_iff, mul_div_cancel_left₀ _ gS_ne]; exact hx

theorem nat_mul_mem (I : FI D) (m : ℕ) {x : D.host.E} (hx : x ∈ I) : (m : D.host.E) * x ∈ I := by
  rw [← nsmul_eq_mul]; exact (I : Submodule (𝓞 D.host.E) D.host.E).toAddSubmonoid.nsmul_mem hx m

theorem self_id (s y c E : D.host.E) (m : ℕ) (hs : s * s = 1) (hsc : D.conjF s = s)
    (hE : E = y - s * D.conjF (c - y)) :
    (y - (m : D.host.E) * c) + s * D.conjF (y - (m : D.host.E) * c) =
      E + (s * D.conjF E - E) - (m : D.host.E) * (s * D.conjF E - E) + (1 - 2 * (m : D.host.E)) * c := by
  subst hE
  simp only [map_sub, map_mul, map_natCast, Formalism.MainNotions.BridgeLemma.conjF_inv, hsc]
  linear_combination (1 - (m : D.host.E)) * (c - y) * hs

end Main

end Formalism.L2.SG.Pf.StabIntLat
end
end

noncomputable section

open scoped Classical

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.PairVal Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.PtCell Formalism.L2.SG.RealObj
  Formalism.L2.SG.Pf.BlockPermutation Formalism.L2.SG.Pf.StabIntSh

namespace Formalism.L2.SG.Pf.StabIntLat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem twistC : TwistC D := by
  intro δ M hA hodd w y
  have hm : 2 * mOdd D = gS D + 1 := by unfold mOdd; obtain ⟨k, hk⟩ := hodd; omega
  have hm' : (1 : D.host.E) - 2 * (mOdd D : D.host.E) = -((gS D : ℕ) : D.host.E) := by
    have : ((2 * mOdd D : ℕ) : D.host.E) = ((gS D + 1 : ℕ) : D.host.E) := by rw [hm]
    push_cast at this; linear_combination -this
  have hEq := E_q w y
  have hτs : ∀ q, selfP w q → τA w q y = (mOdd D : D.host.E) * cf w y q := fun q h => by simp [τA, h]
  have hτu : ∀ q, ¬ selfP w q → upperM w q →
      τA w q y = sgq w (qbar w q) * D.conjF (-(y (qbar w q)) + cf w y (qbar w q)) := fun q h1 h2 => by
    simp [τA, h1, h2]
  have hτl : ∀ q, ¬ selfP w q → ¬ upperM w q → τA w q y = 0 := fun q h1 h2 => by simp [τA, h1, h2]
  have hΛs : ∀ q, selfP w q → ∀ z, z ∈ Λq w q ↔
      z ∈ ddPow D (hgt w q) ∧ z + sgq w q * D.conjF z ∈ qdPow D (hgt w q) := fun q h z => by
    simp only [Λq, h, if_true]; rfl
  have hΛu : ∀ q, ¬ selfP w q → upperM w q → ∀ z, z ∈ Λq w q ↔ z ∈ qdPow D (hgt w q) := fun q h1 h2 z => by
    simp only [Λq, Iq, h1, h2, if_false, not_true_eq_false, or_self]; rfl
  have hΛl : ∀ q, ¬ selfP w q → ¬ upperM w q → ∀ z, z ∈ Λq w q ↔ z ∈ ddPow D (hgt w q) := fun q h1 h2 z => by
    simp only [Λq, Iq, h1, h2, if_false, not_false_eq_true, or_true, if_true]; rfl
  have hup : ∀ q, ¬ selfP w q → upperM w q →
      y q - τA w q y = (Xmat w y - Psi w (Xmat w y)⁻¹) q.1.1 q.1.2 := by
    intro q h1 h2
    rw [hτu q h1 h2, hEq, sgq_qbar, neg_add_eq_sub]
  have hsq : ∀ q, ¬ selfP w q → ¬ selfP w (qbar w q) := fun q h1 h => h1 (by
    unfold selfP at h ⊢; rw [qbar_qbar] at h; exact h.symm)
  have hgc : ∀ q, (1 - 2 * (mOdd D : D.host.E)) * cf w y q ∈ qdPow D (hgt w q) ∨
      ¬ (cf w y q ∈ ddPow D (hgt w q)) := fun q => by
    by_cases hc : cf w y q ∈ ddPow D (hgt w q)
    · left; rw [hm', neg_mul]; exact (qdPow D _ : Submodule (𝓞 D.host.E) D.host.E).neg_mem (gS_mul_qd _ hc)
    · right; exact hc
  rw [condX_iff]
  constructor
  · rintro ⟨hy, hE⟩ q
    by_cases h1 : selfP w q
    · rw [hτs q h1, hΛs q h1]
      have hc := cf_mem w y q (fun p _ => hy p)
      refine ⟨(ddPow D _ : Submodule (𝓞 D.host.E) D.host.E).sub_mem (hy q) (nat_mul_mem _ (mOdd D) hc), ?_⟩
      have hqq : qbar w q = q := h1
      have hEq' := hEq q
      rw [hqq] at hEq'
      rw [self_id (sgq w q) (y q) (cf w y q) _ (mOdd D) (sgq_sq w q) (sgq_conj w q) hEq']
      have e1 := hE q
      have e2 : sgq w q * D.conjF ((Xmat w y - Psi w (Xmat w y)⁻¹) q.1.1 q.1.2) -
          (Xmat w y - Psi w (Xmat w y)⁻¹) q.1.1 q.1.2 ∈ qdPow D (hgt w q) :=
        (qdPow D _ : Submodule (𝓞 D.host.E) D.host.E).sub_mem (sg_qd w δ M hA (hgt_le w q) q e1) e1
      have e3 : (1 - 2 * (mOdd D : D.host.E)) * cf w y q ∈ qdPow D (hgt w q) := by
        rcases hgc q with h | h
        · exact h
        · exact absurd hc h
      exact (qdPow D _ : Submodule (𝓞 D.host.E) D.host.E).add_mem
        ((qdPow D _ : Submodule (𝓞 D.host.E) D.host.E).sub_mem
          ((qdPow D _ : Submodule (𝓞 D.host.E) D.host.E).add_mem e1 e2) (nat_mul_mem _ (mOdd D) e2)) e3
    · by_cases h2 : upperM w q
      · rw [hΛu q h1 h2, hup q h1 h2]; exact hE q
      · rw [hτl q h1 h2, sub_zero, hΛl q h1 h2]; exact hy q
  · intro ht
    have hy : ∀ q, y q ∈ ddPow D (hgt w q) := by
      have key : ∀ n, ∀ q, hgt w q = n → y q ∈ ddPow D (hgt w q) := by
        intro n
        induction n using Nat.strong_induction_on with
        | _ n ih =>
          intro q hq
          have hlow : ∀ p, hgt w p < hgt w q → y p ∈ ddPow D (hgt w p) := fun p hp => ih _ (hq ▸ hp) p rfl
          by_cases h1 : selfP w q
          · have h3 := (hΛs q h1 _).1 (ht q)
            rw [hτs q h1] at h3
            have hc := cf_mem w y q hlow
            have := (ddPow D _ : Submodule (𝓞 D.host.E) D.host.E).add_mem h3.1 (nat_mul_mem _ (mOdd D) hc)
            rwa [sub_add_cancel] at this
          · by_cases h2 : upperM w q
            · have h3 := (hΛu q h1 h2 _).1 (ht q)
              rw [hτu q h1 h2] at h3
              obtain ⟨hp1, hp2⟩ := upper_qbar w h2
              have hyp : y (qbar w q) ∈ ddPow D (hgt w (qbar w q)) := by
                have := (hΛl _ hp1 hp2 _).1 (ht (qbar w q))
                rwa [hτl _ hp1 hp2, sub_zero] at this
              rw [hgt_qbar] at hyp
              have hcp := cf_mem w y (qbar w q) (fun p hp => hlow p (by rwa [hgt_qbar] at hp))
              rw [hgt_qbar] at hcp
              have hτ := sg_dd w δ M hA (hgt_le w q) (qbar w q)
                ((ddPow D _ : Submodule (𝓞 D.host.E) D.host.E).add_mem
                  ((ddPow D _ : Submodule (𝓞 D.host.E) D.host.E).neg_mem hyp) hcp)
              have := (ddPow D _ : Submodule (𝓞 D.host.E) D.host.E).add_mem (qd_le_dd _ h3) hτ
              rwa [sub_add_cancel] at this
            · have := (hΛl q h1 h2 _).1 (ht q)
              rwa [hτl q h1 h2, sub_zero] at this
      exact fun q => key _ q rfl
    have hG := Xmat_grD w y hy
    refine ⟨hy, ?_⟩
    have hB2 : IsBlockDiagonalMatrix w (Xmat w y - Psi w (Xmat w y)⁻¹) := fun a c h => by
      rw [Matrix.sub_apply, Xmat_blk w y a c h,
        Psi_blk w (blk_inv w (Xmat_upU w y) (Xmat_blk w y)) a c h, sub_self]
    have key2 : ∀ n, ∀ q, hgt w q = n →
        (Xmat w y - Psi w (Xmat w y)⁻¹) q.1.1 q.1.2 ∈ qdPow D (hgt w q) := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        intro q hq
        have hU := unitCons w δ M hA (Xmat_upU w y) (Xmat_blk w y) hG q.2.1 (fun i j hij hh => by
          by_cases hb : blkOf w.1 i.val = blkOf w.1 j.val
          · exact ih _ (by rw [← hq]; exact hh) ⟨(i, j), hij, hb⟩ rfl
          · rw [hB2 i j hb]; exact FractionalIdeal.zero_mem _)
        have hPsiq : Psi w (Xmat w y - Psi w (Xmat w y)⁻¹) q.1.1 q.1.2 = sgq w q *
            D.conjF ((Xmat w y - Psi w (Xmat w y)⁻¹) (qbar w q).1.1 (qbar w q).1.2) := rfl
        rw [hPsiq] at hU
        by_cases h1 : selfP w q
        · have hqq : qbar w q = q := h1
          rw [hqq] at hU
          have hT := ((hΛs q h1 _).1 (ht q)).2
          rw [hτs q h1] at hT
          have hEq' := hEq q
          rw [hqq] at hEq'
          rw [self_id (sgq w q) (y q) (cf w y q) _ (mOdd D) (sgq_sq w q) (sgq_conj w q) hEq'] at hT
          have hc := cf_mem w y q (fun p _ => hy p)
          have e3 : (1 - 2 * (mOdd D : D.host.E)) * cf w y q ∈ qdPow D (hgt w q) := by
            rcases hgc q with h | h
            · exact h
            · exact absurd hc h
          set Ee := (Xmat w y - Psi w (Xmat w y)⁻¹) q.1.1 q.1.2 with hEe
          have h5 := (qdPow D (hgt w q) : Submodule (𝓞 D.host.E) D.host.E).sub_mem
            ((qdPow D (hgt w q) : Submodule (𝓞 D.host.E) D.host.E).add_mem
              ((qdPow D (hgt w q) : Submodule (𝓞 D.host.E) D.host.E).sub_mem hT e3) (nat_mul_mem _ (mOdd D) hU)) hU
          have eq : Ee + (sgq w q * D.conjF Ee - Ee) - (mOdd D : D.host.E) * (sgq w q * D.conjF Ee - Ee) +
              (1 - 2 * (mOdd D : D.host.E)) * cf w y q - (1 - 2 * (mOdd D : D.host.E)) * cf w y q +
              (mOdd D : D.host.E) * (sgq w q * D.conjF Ee - Ee) - (sgq w q * D.conjF Ee - Ee) = Ee := by ring
          rw [eq] at h5
          exact h5
        · by_cases h2 : upperM w q
          · rw [← hup q h1 h2]; exact (hΛu q h1 h2 _).1 (ht q)
          · have hpu := lower_qbar w h1 h2
            have hps := hsq q h1
            have hEp : (Xmat w y - Psi w (Xmat w y)⁻¹) (qbar w q).1.1 (qbar w q).1.2 ∈
                qdPow D (hgt w (qbar w q)) := by
              rw [← hup _ hps hpu]; exact (hΛu _ hps hpu _).1 (ht _)
            rw [hgt_qbar] at hEp
            have hs := sg_qd w δ M hA (hgt_le w q) q hEp
            have := (qdPow D _ : Submodule (𝓞 D.host.E) D.host.E).sub_mem hs hU
            rwa [sub_sub_cancel] at this
    exact fun q => key2 _ q rfl

end Formalism.L2.SG.Pf.StabIntLat
end
end

noncomputable section

open scoped Classical

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.PairVal Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.PtCell Formalism.L2.SG.RealObj
  Formalism.L2.SG.Pf.BlockPermutation Formalism.L2.SG.Pf.StabIntSh

namespace Formalism.L2.SG.Pf.StabIntLat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (w : Point D.host.E (D.R.rS + 1))

def coordX (X : MatR D) : FreeE w → D.host.E := fun q => X q.1.1 q.1.2

theorem Xmat_coordX {X : MatR D} (hU : UpU X) (hB : IsBlockDiagonalMatrix w X) : Xmat w (coordX w X) = X := by
  funext a c
  by_cases h : a = c
  · subst h; simp [Xmat, (hU a a).2 rfl]
  · simp only [Xmat, h, if_false]
    by_cases h2 : a < c ∧ blkOf w.1 a.val = blkOf w.1 c.val
    · rw [dite_eq_left h2]; rfl
    · rw [dite_eq_right h2]
      by_cases h3 : a < c
      · exact (hB a c (fun e => h2 ⟨h3, e⟩)).symm
      · exact ((hU a c).1 (lt_of_le_of_ne (not_lt.1 h3) (Ne.symm h))).symm

theorem coordX_Xmat (y : FreeE w → D.host.E) : coordX w (Xmat w y) = y := by
  funext q; exact Xmat_q w y q

theorem mem_stabInt_iff_twist (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (hA : ∀ p, Agree δ M p) (hodd : Odd (gS D))
    (u u' : D.what₂.Word) (β : GLR D) (hβ : IsLoUni (β : MatR D)) {b : MatR D} (hb : IsUpUni b)
    (hW : (β : MatR D) * ptMat w * b = ptMat w) :
    β ∈ stabInt D u u' δ M w ↔
      ∀ q, coordX w ((ptMat w)⁻¹ * (β : MatR D) * ptMat w) q -
        τA w q (coordX w ((ptMat w)⁻¹ * (β : MatR D) * ptMat w)) ∈ Λq w q := by
  obtain ⟨-, hU, hB⟩ := X_of_st w hβ hb hW
  rw [mem_stabInt_iff_X δ M hA u u' w β hβ hb hW, ← Xmat_coordX w hU hB, coordX_Xmat]
  exact twistC δ M hA hodd w _

theorem exists_of_coord (y : FreeE w → D.host.E) :
    ∃ β : GLR D, IsLoUni (β : MatR D) ∧ IsUpUni (Xmat w y)⁻¹ ∧
      (β : MatR D) * ptMat w * (Xmat w y)⁻¹ = ptMat w ∧ (ptMat w)⁻¹ * (β : MatR D) * ptMat w = Xmat w y := by
  obtain ⟨hlo, hXi, hW, hdet⟩ := st_of_X w (Xmat_upU w y) (Xmat_blk w y)
  set B := ptMat w * Xmat w y * (ptMat w)⁻¹
  have hd : IsUnit B.det := by rw [hdet]; exact isUnit_one
  refine ⟨⟨B, B⁻¹, Matrix.mul_nonsing_inv B hd, Matrix.nonsing_inv_mul B hd⟩, hlo, hXi, hW, ?_⟩
  have hu := ptMat_isUnit w
  show (ptMat w)⁻¹ * (ptMat w * Xmat w y * (ptMat w)⁻¹) * ptMat w = Xmat w y
  rw [show (ptMat w)⁻¹ * (ptMat w * Xmat w y * (ptMat w)⁻¹) * ptMat w =
      ((ptMat w)⁻¹ * ptMat w) * Xmat w y * ((ptMat w)⁻¹ * ptMat w) by simp only [Matrix.mul_assoc],
    Matrix.nonsing_inv_mul _ hu, Matrix.one_mul, Matrix.mul_one]

theorem hpr_lt {p q : FreeE w} (h : hgt w q < hgt w p) : hpr w q < hpr w p := by
  unfold hpr; split_ifs <;> omega

theorem trunc_eq {y y' : FreeE w → D.host.E} (q : FreeE w) (h : ∀ p, hpr w p < hpr w q → y p = y' p) :
    trunc w y (hgt w q) = trunc w y' (hgt w q) := by
  funext p
  unfold trunc
  split_ifs with hp
  · exact h p (hpr_lt w hp)
  · rfl

theorem τA_lowdep (q : FreeE w) {y y' : FreeE w → D.host.E} (h : ∀ p, hpr w p < hpr w q → y p = y' p) :
    τA w q y = τA w q y' := by
  unfold τA
  by_cases h1 : selfP w q
  · simp only [h1, if_true, cf, trunc_eq w q h]
  · by_cases h2 : upperM w q
    · obtain ⟨hp1, hp2⟩ := upper_qbar w h2
      have hlt : hpr w (qbar w q) < hpr w q := by
        unfold hpr; rw [hgt_qbar]; simp only [h2, hp2, if_true, if_false]; omega
      have hc : cf w y (qbar w q) = cf w y' (qbar w q) := by
        unfold cf
        rw [trunc_eq w (qbar w q) (fun p hp => h p (lt_trans hp hlt))]
      simp only [h1, h2, if_false, if_true, h _ hlt, hc]
    · simp only [h1, h2, if_false]

end Formalism.L2.SG.Pf.StabIntLat
