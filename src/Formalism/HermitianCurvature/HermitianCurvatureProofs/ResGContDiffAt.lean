module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapRWordsOfParts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RaisingCompactSupport
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.GroupEquationsPostHolds

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.ResGContDiffAt
open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBN.MC

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
open scoped ContDiff

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section cell

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]


open Classical in
def resW (h : Mx k r → V) (g : Mx k r) : (Fin r → ℂ) → V :=
  fun c' => if c' ∈ OmX r then resG k r (Fin.last r) h c' g else 0

theorem resG_contDiffAt (Bs : B.RealPlaceData k r Wp Wq) {h : Mx k r → V}
    (hh : SmoothLev k r 0 (OmPlus k r Bs.z Bs.z') h) {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r))
    (hG : 0 < GGl k r Bs.z Bs.z' g) {c₀ : Fin r → ℂ} (hc₀ : c₀ ∈ OmX r) :
    ContDiffAt ℝ ∞ (fun c' => resG k r (Fin.last r) h c' g) c₀ := by
  have hsf := Formalism.FourierDecayAlt.P5.Rad.sf_resG hh
  obtain ⟨U, F, hU, hxU, hF, hE⟩ := hsf (c₀, g)
    ⟨hc₀, Formalism.FourierDecayAlt.P5.Rad.wCell_mem_omPlus Bs.z_mem Bs.z'_mem hc₀ hg hG⟩ hg
  have hpre : IsOpen ((fun c : Fin r → ℂ => (c, g)) ⁻¹' U) := hU.preimage (by fun_prop)
  have hmem : c₀ ∈ (fun c : Fin r → ℂ => (c, g)) ⁻¹' U := hxU
  have hcd : ContDiffAt ℝ ∞ (fun c : Fin r → ℂ => F (c, g)) c₀ := by
    have h1 : ContDiffOn ℝ ∞ (fun c : Fin r → ℂ => F (c, g)) ((fun c : Fin r → ℂ => (c, g)) ⁻¹' U) :=
      hF.comp (by fun_prop : ContDiff ℝ ∞ (fun c : Fin r → ℂ => (c, g))).contDiffOn (fun c hc => hc)
    exact h1.contDiffAt (hpre.mem_nhds hmem)
  refine hcd.congr_of_eventuallyEq ?_
  filter_upwards [hpre.mem_nhds hmem] with c hc
  exact hE (c, g) hc hg

theorem resG_wsm (Bs : B.RealPlaceData k r Wp Wq) {h : Mx k r → V} (hh : SmoothLev k r 0 (OmPlus k r Bs.z Bs.z') h)
    {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r)) (hG : 0 < GGl k r Bs.z Bs.z' g) :
    resW h g ∈ WSm r V := by
  refine ⟨?_, fun x hx => by simp [resW, hx]⟩
  intro c hc
  have h1 := (resG_contDiffAt Bs hh hg hG hc).contDiffWithinAt (s := OmX r)
  refine h1.congr (fun c' hc' => by simp [resW, hc']) (by simp [resW, hc])

theorem wsm_resG_eq (h : Mx k r → V) (g : Mx k r) {c : Fin r → ℂ} (hc : c ∈ OmX r) :
    resW h g c = resG k r (Fin.last r) h c g := by
  simp [resW, hc]

theorem cell_diff (Bs : B.RealPlaceData k r Wp Wq) {h : Mx k r → V} (hh : SmoothLev k r 0 (OmPlus k r Bs.z Bs.z') h)
    {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r)) (hG : 0 < GGl k r Bs.z Bs.z' g) {c : Fin r → ℂ}
    (hc : c ∈ OmX r) : DifferentiableAt ℝ (fun c' => h (wCell k r (Fin.last r) c' * g)) c := by
  have hgl : ∀ c' ∈ OmX r, wCell k r (Fin.last r) c' * g ∈ Glev k r 0 := fun c' hc' =>
    Formalism.FourierDecayAlt.P.Qx3.glev_mul (Formalism.FourierDecayAlt.P.Qx3.wlist_glev hc' _) (Formalism.FourierDecayAlt.P.Qx3.glev_mono (Fin.zero_le _) hg)
  obtain ⟨U, F, hU, hgU, hF, hE⟩ := hh (wCell k r (Fin.last r) c * g)
    ⟨hgl c hc, Formalism.FourierDecayAlt.P5.Rad.wCell_mem_omPlus Bs.z_mem Bs.z'_mem hc hg hG⟩
  have hw : ContDiffOn ℝ ∞ (fun c' : Fin r → ℂ => wCell k r (Fin.last r) c' * g) (OmX r) :=
    Formalism.FourierDecayAlt.P.Qx3.cdo_mul (Formalism.FourierDecayAlt.P.Qx3.wlist_smooth _) contDiffOn_const
  have hwc : ContinuousAt (fun c' : Fin r → ℂ => wCell k r (Fin.last r) c' * g) c :=
    (hw.continuousOn).continuousAt ((Formalism.FourierDecayAlt.P.Qx3.isOpen_OmX r).mem_nhds hc)
  have hd : DifferentiableAt ℝ (fun c' => F (wCell k r (Fin.last r) c' * g)) c := by
    have hFd : DifferentiableAt ℝ F (wCell k r (Fin.last r) c * g) :=
      (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hgU)
    have hwd : DifferentiableAt ℝ (fun c' : Fin r → ℂ => wCell k r (Fin.last r) c' * g) c :=
      (hw.differentiableOn (by simp)).differentiableAt ((Formalism.FourierDecayAlt.P.Qx3.isOpen_OmX r).mem_nhds hc)
    exact hFd.comp c hwd
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [(Formalism.FourierDecayAlt.P.Qx3.isOpen_OmX r).mem_nhds hc, hwc.preimage_mem_nhds (hU.mem_nhds hgU)]
    with c' h1 h2
  exact hE _ h2 (hgl c' h1)

end cell

section chain

variable {r : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem wsm_sub {f g : (Fin r → ℂ) → V} (hf : f ∈ WSm r V) (hg : g ∈ WSm r V) : f - g ∈ WSm r V :=
  (WSm r V).sub_mem hf hg

theorem opL_mem (l : Fin r) (i : Fin 6) {f : (Fin r → ℂ) → V} (hf : f ∈ WSm r V) : opL l i f ∈ WSm r V :=
  preserved_operators_holds r V l i f hf

theorem opL_sub (l : Fin r) (i : Fin 6) {f g : (Fin r → ℂ) → V} (hf : f ∈ WSm r V) (hg : g ∈ WSm r V) :
    opL l i (f - g) = opL l i f - opL l i g := by
  have hng : (-1 : ℂ) • g ∈ WSm r V := (WSm r V).smul_mem _ hg
  have e : f - g = f + (-1 : ℂ) • g := by rw [neg_one_smul, sub_eq_add_neg]
  rw [e, (linear_operators_holds r V l i f _ 1 hf hng).1, (linear_operators_holds r V l i g g (-1) hg hg).2, neg_one_smul,
    sub_eq_add_neg]

theorem opL_add (l : Fin r) (i : Fin 6) {f g : (Fin r → ℂ) → V} (hf : f ∈ WSm r V) (hg : g ∈ WSm r V) :
    opL l i (f + g) = opL l i f + opL l i g :=
  (linear_operators_holds r V l i f g 1 hf hg).1

theorem opL_smul (l : Fin r) (i : Fin 6) {f : (Fin r → ℂ) → V} (hf : f ∈ WSm r V) (a : ℂ) :
    opL l i (a • f) = a • opL l i f :=
  (linear_operators_holds r V l i f f a hf hf).2

theorem pOp_zero (l : Fin r) : pOp l (fun _ : Fin r → ℂ => (0 : V)) = fun _ => 0 := by
  funext x; unfold pOp wirt; split_ifs <;> simp

theorem vAB_mem (y : ℂ) : ∀ (i : ℕ) {G : (Fin r → ℂ) → V}, G ∈ WSm r V →
    (vAB r y i).1 G ∈ WSm r V ∧ (vAB r y i).2 G ∈ WSm r V := by
  intro i
  induction i with
  | zero =>
    intro G hG
    exact ⟨hG, (WSm r V).zero_mem⟩
  | succ i ih =>
    intro G hG
    obtain ⟨hA, hB⟩ := ih hG
    by_cases hi : i < r
    · simp only [vAB, dite_eq_left hi]
      refine ⟨wsm_sub ((WSm r V).add_mem ((WSm r V).smul_mem y hA) (opL_mem ⟨i, hi⟩ 0 hA))
        (opL_mem ⟨i, hi⟩ 1 hB), opL_mem ⟨i, hi⟩ 2 hA⟩
    · simp only [vAB, dite_eq_right hi]
      exact ⟨hA, hB⟩

theorem vAB_lin (y : ℂ) : ∀ (i : ℕ) {G₁ G₂ : (Fin r → ℂ) → V}, G₁ ∈ WSm r V → G₂ ∈ WSm r V → ∀ s : ℂ,
    (vAB r y i).1 (G₁ + s • G₂) = (vAB r y i).1 G₁ + s • (vAB r y i).1 G₂ ∧
      (vAB r y i).2 (G₁ + s • G₂) = (vAB r y i).2 G₁ + s • (vAB r y i).2 G₂ := by
  intro i
  induction i with
  | zero =>
    intro G₁ G₂ _ _ s
    exact ⟨rfl, by show (0 : (Fin r → ℂ) → V) = 0 + s • 0; simp⟩
  | succ i ih =>
    intro G₁ G₂ h₁ h₂ s
    obtain ⟨ih1, ih2⟩ := ih h₁ h₂ s
    obtain ⟨hA₁, hB₁⟩ := vAB_mem y i h₁
    obtain ⟨hA₂, hB₂⟩ := vAB_mem y i h₂
    have hsA := (WSm r V).smul_mem s hA₂
    have hsB := (WSm r V).smul_mem s hB₂
    by_cases hi : i < r
    · simp only [vAB, dite_eq_left hi]
      rw [ih1, ih2]
      refine ⟨?_, ?_⟩
      · have e1 : pOp ⟨i, hi⟩ ((vAB r y i).1 G₁ + s • (vAB r y i).1 G₂) =
            pOp ⟨i, hi⟩ ((vAB r y i).1 G₁) + s • pOp ⟨i, hi⟩ ((vAB r y i).1 G₂) := by
          rw [show pOp ⟨i, hi⟩ = opL ⟨i, hi⟩ 0 from rfl, opL_add _ _ hA₁ hsA, opL_smul _ _ hA₂]
        have e2 : cOp ⟨i, hi⟩ ((vAB r y i).2 G₁ + s • (vAB r y i).2 G₂) =
            cOp ⟨i, hi⟩ ((vAB r y i).2 G₁) + s • cOp ⟨i, hi⟩ ((vAB r y i).2 G₂) := by
          rw [show cOp ⟨i, hi⟩ = opL ⟨i, hi⟩ 1 from rfl, opL_add _ _ hB₁ hsB, opL_smul _ _ hB₂]
        rw [e1, e2]
        funext x
        simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_add, smul_sub]
        rw [smul_comm y s]
        abel
      · rw [show ciOp ⟨i, hi⟩ = opL ⟨i, hi⟩ 2 from rfl, opL_add _ _ hA₁ hsA, opL_smul _ _ hA₂]
    · simp only [vAB, dite_eq_right hi]
      exact ⟨ih1, ih2⟩

theorem vAB_comm (y : ℂ) (j : Fin r) : ∀ (i : ℕ), i ≤ j.val → ∀ {G : (Fin r → ℂ) → V}, G ∈ WSm r V →
    (vAB r y i).1 G ∈ WSm r V ∧ (vAB r y i).2 G ∈ WSm r V ∧
      (vAB r y i).1 (pOp j G) = pOp j ((vAB r y i).1 G) ∧ (vAB r y i).2 (pOp j G) = pOp j ((vAB r y i).2 G) := by
  intro i
  induction i with
  | zero =>
    intro _ G hG
    exact ⟨hG, (WSm r V).zero_mem, rfl, by simp only [vAB]; exact (pOp_zero j).symm⟩
  | succ i ih =>
    intro hij G hG
    obtain ⟨hA, hB, c1, c2⟩ := ih (by omega) hG
    have hpG : pOp j G ∈ WSm r V := opL_mem j 0 hG
    have hi : i < r := by have := j.isLt; omega
    have hne : (⟨i, hi⟩ : Fin r) ≠ j := by intro h; rw [← h] at hij; simp at hij
    obtain ⟨hm1, hm2⟩ := vAB_mem y (i + 1) hG
    refine ⟨hm1, hm2, ?_, ?_⟩
    · simp only [vAB, dite_eq_left hi]
      rw [c1, c2]
      have hpA : pOp ⟨i, hi⟩ ((vAB r y i).1 G) ∈ WSm r V := opL_mem _ 0 hA
      have hcB : cOp ⟨i, hi⟩ ((vAB r y i).2 G) ∈ WSm r V := opL_mem _ 1 hB
      have hyA : y • (vAB r y i).1 G ∈ WSm r V := (WSm r V).smul_mem y hA
      rw [show pOp j = opL j 0 from rfl, opL_sub _ _ ((WSm r V).add_mem hyA hpA) hcB,
        opL_add _ _ hyA hpA, opL_smul _ _ hA]
      have k1 : opL j 0 (pOp ⟨i, hi⟩ ((vAB r y i).1 G)) = pOp ⟨i, hi⟩ (opL j 0 ((vAB r y i).1 G)) :=
        (commuting_functional_holds r V j ⟨i, hi⟩ 0 0 _ hA (Or.inl (Ne.symm hne)))
      have k2 : opL j 0 (cOp ⟨i, hi⟩ ((vAB r y i).2 G)) = cOp ⟨i, hi⟩ (opL j 0 ((vAB r y i).2 G)) :=
        (commuting_functional_holds r V j ⟨i, hi⟩ 0 1 _ hB (Or.inl (Ne.symm hne)))
      rw [k1, k2]
    · simp only [vAB, dite_eq_left hi]
      rw [c1]
      exact (commuting_functional_holds r V j ⟨i, hi⟩ 0 2 _ hA (Or.inl (Ne.symm hne))).symm

end chain

end Formalism.FourierDecayAlt.P.PBN.MC
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDACapTodaVCoef
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace TVCoefPf

variable {k r : ℕ}

theorem castLE_self (h : r ≤ r) (a : Fin r) : Fin.castLE h a = a := Fin.ext rfl

theorem esI_inj (a b : Fin r) : esI k r a = esI k r b ↔ a = b := by
  have := a.isLt
  have := b.isLt
  constructor
  · intro h
    apply Fin.ext
    have h' := congrArg Fin.val h
    simp only [esI] at h'
    omega
  · intro h; rw [h]

theorem keyS_esI (a : Fin r) : C3.keyS k r (esI k r a) = a.val := by
  have := a.isLt
  unfold C3.keyS esI
  simp only
  split_ifs with h <;> omega

theorem w1_mulVec_bvec_esI (l : Fin r) (s : ℂ) : Q.w1 k r l s *ᵥ bvec (esI k r l) = (star s)⁻¹ • bvec (eI k r l) := by
  funext p
  simp only [bvec, Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_apply, Pi.smul_apply, smul_eq_mul]
  rw [Formalism.FourierDecayAlt.P.Qx3.w1_apply, Formalism.FourierDecayAlt.P.Qx3.sw_es, Formalism.FourierDecayAlt.P.Qx3.dd_es]
  split_ifs <;> simp

theorem ne_of_ne {a b : Fin r} (hab : ¬ a = b) {q : Fin (2 * r + k + 1)} (hq : q = eI k r a ∨ q = esI k r a) :
    q ≠ eI k r b ∧ q ≠ esI k r b := by
  have h1 : a.val ≠ b.val := fun h => hab (Fin.ext h)
  have := a.isLt
  have := b.isLt
  rcases hq with rfl | rfl
  · constructor <;> intro h <;> have h' := congrArg Fin.val h <;> simp only [eI, esI] at h' <;> omega
  · constructor <;> intro h <;> have h' := congrArg Fin.val h <;> simp only [eI, esI] at h' <;> omega

theorem wlist_fix (c : Fin r → ℂ) (a : Fin r) {q : Fin (2 * r + k + 1)} (hq : q = eI k r a ∨ q = esI k r a) :
    ∀ L : List (Fin r), a ∉ L → (L.map fun b => Q.w1 k r b (c b)).prod *ᵥ bvec q = bvec q := by
  intro L
  induction L with
  | nil => intro _; simp
  | cons b L ih =>
    intro ha
    rw [List.mem_cons, not_or] at ha
    rw [List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec, ih ha.2]
    obtain ⟨h1, h2⟩ := ne_of_ne ha.1 hq
    exact Formalism.FourierDecayAlt.P.Qx3.reflection_fixes_basis_vector b (c b) h1 h2

theorem wlist_main {c : Fin r → ℂ} (hc : c ∈ OmX r) (a : Fin r) :
    ∀ L : List (Fin r), L.Nodup → a ∈ L →
      (L.map fun b => Q.w1 k r b (c b)).prod *ᵥ (star (c a) • bvec (esI k r a)) = bvec (eI k r a) := by
  have hc' : ∀ l, c l ≠ 0 := hc
  intro L
  induction L with
  | nil => intro _ h; simp at h
  | cons b L ih =>
    intro hnd ha
    rw [List.nodup_cons] at hnd
    rw [List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec]
    by_cases hab : b = a
    · subst hab
      rw [Matrix.mulVec_smul, wlist_fix c b (Or.inr rfl) L hnd.1, Matrix.mulVec_smul, w1_mulVec_bvec_esI, smul_smul,
        mul_inv_cancel₀ (star_ne_zero.2 (hc' b)), one_smul]
    · have haL : a ∈ L := by
        rcases List.mem_cons.1 ha with h | h
        · exact absurd h.symm hab
        · exact h
      rw [ih hnd.2 haL]
      obtain ⟨h1, h2⟩ := ne_of_ne (fun h => hab h.symm) (Or.inl rfl)
      exact Formalism.FourierDecayAlt.P.Qx3.reflection_fixes_basis_vector b (c b) h1 h2

theorem wcell_es {c : Fin r → ℂ} (hc : c ∈ OmX r) (a : Fin r) :
    Q.wCell k r (Fin.last r) c *ᵥ (star (c a) • bvec (esI k r a)) = bvec (eI k r a) := by
  unfold Q.wCell
  refine wlist_main hc a _ ((List.nodup_finRange r).filter _) ?_
  rw [List.mem_filter]
  exact ⟨List.mem_finRange a, by simp⟩

theorem inv_e {c : Fin r → ℂ} (hc : c ∈ OmX r) {g : Q.Mx k r} (hg : g ∈ Q.Glev k r (Fin.last r)) (a : Fin r) :
    (Q.wCell k r (Fin.last r) c * g)⁻¹ *ᵥ bvec (eI k r a) = star (c a) • bvec (esI k r a) := by
  have hW : Q.wCell k r (Fin.last r) c ∈ Q.Glev k r 0 := Formalism.FourierDecayAlt.P.Qx3.wlist_glev hc _
  have hu : IsUnit (Q.wCell k r (Fin.last r) c * g).det := by
    rw [Matrix.det_mul]
    exact (Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hW.1).mul (Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hg.1)
  have ha : a.val < (Fin.last r).val := by rw [Fin.val_last]; exact a.isLt
  have hv : (Q.wCell k r (Fin.last r) c * g) *ᵥ (star (c a) • bvec (esI k r a)) = bvec (eI k r a) := by
    rw [← Matrix.mulVec_mulVec, Matrix.mulVec_smul, (hg.2 a ha).2]
    exact wcell_es hc a
  rw [← hv, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]

theorem det_entry {c : Fin r → ℂ} (hc : c ∈ OmX r) {g : Q.Mx k r} (hg : g ∈ Q.Glev k r (Fin.last r))
    (B : Fin r → Fin (2 * r + k + 1)) :
    (Matrix.of fun a l : Fin r =>
        ((Q.wCell k r (Fin.last r) c * g)⁻¹ *ᵥ bvec (eI k r (Fin.castLE le_rfl a))) (B l)) =
      Matrix.of fun a l : Fin r => star (c a) * (if B l = esI k r a then (1 : ℂ) else 0) := by
  ext a l
  simp only [Matrix.of_apply]
  rw [castLE_self, inv_e hc hg a]
  simp [bvec, Pi.single_apply]

theorem sm_ge {n : ℕ} {τ : Fin n → Fin n} (h : StrictMono τ) : ∀ m (j : Fin n), j.val = m → m ≤ (τ j).val := by
  intro m
  induction m with
  | zero => intro j _; omega
  | succ m ih =>
    intro j hj
    have hm : m < n := by have := j.isLt; omega
    have h1 := ih ⟨m, hm⟩ rfl
    have h2 : τ ⟨m, hm⟩ < τ j := h (by rw [Fin.lt_def]; simp only; omega)
    rw [Fin.lt_def] at h2
    omega

theorem sm_eq_id {n : ℕ} {τ : Fin n → Fin n} (h : StrictMono τ) : τ = id := by
  have hρ : StrictMono fun j : Fin n => Fin.rev (τ (Fin.rev j)) := by
    intro a b hab
    rw [Fin.rev_lt_rev]
    exact h (Fin.rev_lt_rev.2 hab)
  funext j
  apply Fin.ext
  have e1 := sm_ge h j.val j rfl
  have e2 := sm_ge hρ (Fin.rev j).val (Fin.rev j) rfl
  simp only [Fin.rev_rev, Fin.val_rev] at e2
  have := j.isLt
  have := (τ j).isLt
  simp only [id]
  omega

theorem det_zero {c : Fin r → ℂ} (hc : c ∈ OmX r) {g : Q.Mx k r} (hg : g ∈ Q.Glev k r (Fin.last r))
    (B : Fin r → Fin (2 * r + k + 1)) (hm : StrictMono fun l => C3.keyS k r (B l)) (hB : B ≠ C3.sR k r r le_rfl) :
    (Matrix.of fun a l : Fin r =>
        ((Q.wCell k r (Fin.last r) c * g)⁻¹ *ᵥ bvec (eI k r (Fin.castLE le_rfl a))) (B l)).det = 0 := by
  rw [det_entry hc hg B]
  by_cases hcol : ∃ l, ∀ a, B l ≠ esI k r a
  · obtain ⟨l, hl⟩ := hcol
    exact Matrix.det_eq_zero_of_column_eq_zero l (fun a => by simp [hl a])
  · push Not at hcol
    choose τ hτ using hcol
    have hτm : StrictMono τ := by
      intro a b hab
      have := hm hab
      simp only [hτ, keyS_esI] at this
      exact Fin.lt_def.2 this
    have hid := sm_eq_id hτm
    exact absurd (funext fun l => by rw [hτ l, hid]; rfl) hB

theorem det_sR {c : Fin r → ℂ} (hc : c ∈ OmX r) {g : Q.Mx k r} (hg : g ∈ Q.Glev k r (Fin.last r)) :
    (Matrix.of fun a l : Fin r =>
        ((Q.wCell k r (Fin.last r) c * g)⁻¹ *ᵥ bvec (eI k r (Fin.castLE le_rfl a))) (C3.sR k r r le_rfl l)).det =
      drbF r c := by
  rw [det_entry hc hg]
  have e : (Matrix.of fun a l : Fin r => star (c a) * (if C3.sR k r r le_rfl l = esI k r a then (1 : ℂ) else 0)) =
      Matrix.diagonal fun a => star (c a) := by
    ext a l
    simp only [Matrix.of_apply, Matrix.diagonal_apply, C3.sR, castLE_self, esI_inj]
    by_cases h : a = l
    · subst h; simp
    · simp [h, Ne.symm h]
  rw [e, Matrix.det_diagonal]
  simp [drbF, map_prod]

theorem colsVm_eq : colsVm k r r = C3.sR k r r le_rfl ∘ Fin.revPerm := by
  funext j
  apply Fin.ext
  have := j.isLt
  simp [colsVm, C3.sR, esI, Fin.val_rev]
  omega

theorem kv_rev {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {x : Q.Mx k r} (hx : x ∈ B.GV k r)
    {J : Q.Mx k r → E} (hloc : Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.Loc ((r : ℕ) : ℕ∞) J x) (w : ℂ) :
    kvM k r r w J x = qminorOp (Q.EH k r) (C3.sR k r r le_rfl) (C3.sR k r r le_rfl) w J x := by
  unfold kvM
  rw [colsVm_eq, Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion.skewRow, Formalism.FourierDecayAlt.P.FourTermExpansion.skewCol (C3.sR k r r le_rfl) w J x hx hloc, smul_smul,
    ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one, one_smul]

theorem coef_gen {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {c : Fin r → ℂ} (hc : c ∈ OmX r)
    {g : Q.Mx k r} (hg : g ∈ Q.Glev k r (Fin.last r)) (hx : Q.wCell k r (Fin.last r) c * g ∈ B.GV k r)
    {J : Q.Mx k r → E} (hloc : Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.Loc ((r : ℕ) : ℕ∞) J (Q.wCell k r (Fin.last r) c * g)) (y : ℂ) :
    capAv k r y J (Q.wCell k r (Fin.last r) c * g) =
      drbF r c • kvM k r r (kvTop k r y) J (Q.wCell k r (Fin.last r) c * g) := by
  rw [kv_rev hx hloc, ← det_sR hc hg]
  simp only [capAv, C3.AAvop]
  rw [Fintype.sum_eq_single (C3.sR k r r le_rfl)]
  · have hmono : StrictMono fun l => C3.keyS k r (C3.sR k r r le_rfl l) := by
      intro a b hab
      simp only [C3.sR, castLE_self, keyS_esI]
      exact hab
    rw [if_pos hmono]
    rfl
  · intro B hB
    split_ifs with hm
    · rw [det_zero hc hg B hm hB, zero_smul]
    · rfl

end TVCoefPf

theorem toda_coefficient_holds : TVCoef := by
  intro Wp Wq _ _ _ _ _ _ P Bs hpl hk y J hJ c hc g hg hcg
  obtain ⟨hGV, hCk⟩ := capa_J_ck P Bs hJ hc hg hcg ((P.r : ℕ) : ℕ∞)
  exact TVCoefPf.coef_gen hc hg hGV (hCk _ (Set.mem_singleton _)) y

end

end Formalism.FourierDecayAlt.P.CutMP
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.RatioBound
namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

section pj

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}
  (p : KB.Pl P Wp Wq) (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter) (ys : List ℝ) {ε : ℝ}

theorem pj_sl (x₁ x₂ : Wd.Ix (Fin (KB.plusW ys w).length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp))
    (y : Wd.Ix (Fin (KB.minusW ys w).length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) (c : ℂ)
    (h₁ : NV (p.T.bs j) ε x₁) (h₂ : NV (p.T.bs j) ε x₂) (hy : NV (p.T.bs j) ε y) :
    KB.pairJ (p.form j hj w) ys (x₁ + c • x₂) y =
      KB.pairJ (p.form j hj w) ys x₁ y + c * KB.pairJ (p.form j hj w) ys x₂ y :=
  PBG.pairJ_sesq_left P p.T (M.sgn P p.l0) ⟨j, by omega⟩ w ys x₁ x₂ y c (PBG.decV_of_nice h₁)
    (PBG.decV_of_nice h₂) (PBG.decV_of_nice hy)

theorem pj_sr (x : Wd.Ix (Fin (KB.plusW ys w).length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp))
    (y₁ y₂ : Wd.Ix (Fin (KB.minusW ys w).length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) (c : ℂ)
    (hx : NV (p.T.bs j) ε x) (h₁ : NV (p.T.bs j) ε y₁) (h₂ : NV (p.T.bs j) ε y₂) :
    KB.pairJ (p.form j hj w) ys x (y₁ + c • y₂) =
      KB.pairJ (p.form j hj w) ys x y₁ + conj c * KB.pairJ (p.form j hj w) ys x y₂ :=
  PBG.pairJ_sesq_right P p.T (M.sgn P p.l0) ⟨j, by omega⟩ w ys x y₁ y₂ c (PBG.decV_of_nice hx)
    (PBG.decV_of_nice h₁) (PBG.decV_of_nice h₂)

theorem pj_zero_l (y : Wd.Ix (Fin (KB.minusW ys w).length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp))
    (hy : NV (p.T.bs j) ε y) : KB.pairJ (p.form j hj w) ys 0 y = 0 := by
  have h := pj_sl p j hj w ys 0 0 y 1 nv_zero nv_zero hy
  simp only [one_smul, add_zero, one_mul] at h
  linear_combination -h

theorem pj_zero_r (x : Wd.Ix (Fin (KB.plusW ys w).length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp))
    (hx : NV (p.T.bs j) ε x) : KB.pairJ (p.form j hj w) ys x 0 = 0 := by
  have h := pj_sr p j hj w ys x 0 0 1 hx nv_zero nv_zero
  simp only [one_smul, add_zero, map_one, one_mul] at h
  linear_combination -h

theorem pj_smul (x : Wd.Ix (Fin (KB.plusW ys w).length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp))
    (y : Wd.Ix (Fin (KB.minusW ys w).length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) (c d : ℂ)
    (hx : NV (p.T.bs j) ε x) (hy : NV (p.T.bs j) ε y) :
    KB.pairJ (p.form j hj w) ys (c • x) (d • y) = c * conj d * KB.pairJ (p.form j hj w) ys x y := by
  have h1 := pj_sl p j hj w ys 0 x (d • y) c nv_zero hx (nv_smul d hy)
  have h2 := pj_sr p j hj w ys x 0 y d hx nv_zero hy
  rw [zero_add, pj_zero_l p j hj w ys _ (nv_smul d hy), zero_add] at h1
  rw [zero_add, pj_zero_r p j hj w ys x hx, zero_add] at h2
  rw [h1, h2]; ring

end pj

section deg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
  {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
  {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}

theorem uB_pos (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (v : Fin S.f) (ε : ℝ) (j : ℕ)
    (hj : j ≤ S.G.r) (w : List C.Letter) (h : C.LPt) (hh : D.IsLocPt h j) :
    uB S p F v ε j hj w h = (((√(nnS S h) / bS S h : ℝ) : ℂ)) •
      KB.slv (p v).T (F v ε) j hj w (stdS S h) ((stdS_size S h).trans hh.2) := by
  unfold uB; rw [dite_eq_left hh]

theorem uB_neg (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (v : Fin S.f) (ε : ℝ) (j : ℕ)
    (hj : j ≤ S.G.r) (w : List C.Letter) (h : C.LPt) (hh : ¬ D.IsLocPt h j) : uB S p F v ε j hj w h = 0 := by
  unfold uB; rw [dite_eq_right hh]

theorem waveG_smul' {k ρ : ℕ} {Wp' Wq' : Type} [NormedAddCommGroup Wp'] [InnerProductSpace ℂ Wp']
    [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] (Bs : B.RealPlaceData k ρ Wp' Wq') (s : ℂ) (w : List C.Letter)
    (x : Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq' →L[ℂ] Wp')) (c : ℂ) :
    KB.waveG Bs s w (c • x) = c • KB.waveG Bs s w x := by
  have := PBG.waveG_add_smul Bs s w 0 x c
  rwa [zero_add, PBG.waveG_zero, zero_add] at this

theorem deg_uB (hDW : KB.DegWave) (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (hF : ∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (F v ε)) (v : Fin S.f) (ε : ℝ) (hε : 0 < ε) (j : ℕ)
    (hj : j ≤ S.G.r) (a : List C.Letter) (K : ℕ) (grid : Fin K → Fin (2 * j + 1) → ℝ)
    (hinj : ∀ b, Function.Injective (grid b)) (s : ℂ) (h h' : C.LPt) :
    s ^ K * (p v).form j hj a (KB.waveG ((p v).T.bs j) s a (uB S p F v ε j hj a h)) (uB S p F v ε j hj a h') =
      ∑ n : Fin K → Fin (2 * j + 1), ((∏ b, F7.lagCo (grid b) (n b) : ℝ) : ℂ) *
        KB.pairJ ((p v).form j hj a) (List.ofFn fun b => grid b (n b))
          (KB.waveG ((p v).T.bs j) s _ (uB S p F v ε j hj (KB.plusW (List.ofFn fun b => grid b (n b)) a) h))
          (uB S p F v ε j hj (KB.minusW (List.ofFn fun b => grid b (n b)) a) h') := by
  have hgpos := g_pos_of_built hB
  by_cases hloc : D.IsLocPt h j ∧ D.IsLocPt h' j
  · obtain ⟨hh, hh'⟩ := hloc
    have hH : D.IsLocPt (stdS S h) j := (PBD.isLocPt_toStd_iff _ _ hgpos h 1 j).2 hh
    have hH' : D.IsLocPt (stdS S h') j := (PBD.isLocPt_toStd_iff _ _ hgpos h' 1 j).2 hh'
    have hdeg := hDW (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (p v) (F v ε) j hj a (stdS S h) (stdS S h') hH hH' K
      grid s LinearMap.id (fun ε x hx => hx) (hF v ε hε) hinj
    simp only [LinearMap.id_apply, onOld_id] at hdeg
    set Dh : ℂ := (((√(nnS S h) / bS S h : ℝ) : ℂ)) with hDh
    set Dh' : ℂ := (((√(nnS S h') / bS S h' : ℝ) : ℂ)) with hDh'
    rw [uB_pos S p F v ε j hj a h hh, uB_pos S p F v ε j hj a h' hh', waveG_smul']
    obtain ⟨ε2, hε2, hs, hs'⟩ := nv_pair (slv_nv (p v) (hF v ε hε) j hj a (stdS S h) hH)
      (slv_nv (p v) (hF v ε hε) j hj a (stdS S h') hH')
    have hws := PBFV.waveG_nice ((p v).T.bs j) ε2 s a _ hs
    rw [form_smul_l (p v) j hj a _ _ _ hws (nv_smul _ hs'), form_smul_r (p v) j hj a _ _ _ hws hs']
    have hL : s ^ K * (Dh * (conj Dh' * (p v).form j hj a (KB.waveG ((p v).T.bs j) s a
        (KB.slv (p v).T (F v ε) j hj a (stdS S h) ((stdS_size S h).trans hh.2)))
        (KB.slv (p v).T (F v ε) j hj a (stdS S h') ((stdS_size S h').trans hh'.2)))) =
        Dh * conj Dh' * (s ^ K * (p v).form j hj a (KB.waveG ((p v).T.bs j) s a
        (KB.slv (p v).T (F v ε) j hj a (stdS S h) hH.2)) (KB.slv (p v).T (F v ε) j hj a (stdS S h') hH'.2)) := by
      ring
    rw [hL, hdeg, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    set ys := List.ofFn fun b => grid b (n b) with hys
    obtain ⟨ε3, hε3, hp, hm⟩ := nv_pair (slv_nv (p v) (hF v ε hε) j hj (KB.plusW ys a) (stdS S h) hH)
      (slv_nv (p v) (hF v ε hε) j hj (KB.minusW ys a) (stdS S h') hH')
    have hwp := PBFV.waveG_nice ((p v).T.bs j) ε3 s _ _ hp
    rw [uB_pos S p F v ε j hj (KB.plusW ys a) h hh, uB_pos S p F v ε j hj (KB.minusW ys a) h' hh', waveG_smul',
      pj_smul (p v) j hj a ys _ _ _ _ hwp hm]
    ring
  · have h0 : uB S p F v ε j hj a h = 0 ∨ uB S p F v ε j hj a h' = 0 := by
      by_cases hh : D.IsLocPt h j
      · exact Or.inr (uB_neg S p F v ε j hj a h' fun hh' => hloc ⟨hh, hh'⟩)
      · exact Or.inl (uB_neg S p F v ε j hj a h hh)
    obtain ⟨ε1, hε1, hx, hx'⟩ := nv_pair (uB_nv hB F hF v ε hε j hj a h) (uB_nv hB F hF v ε hε j hj a h')
    have hwx := PBFV.waveG_nice ((p v).T.bs j) ε1 s a _ hx
    have lhs0 : (p v).form j hj a (KB.waveG ((p v).T.bs j) s a (uB S p F v ε j hj a h)) (uB S p F v ε j hj a h') = 0 := by
      rcases h0 with h0 | h0
      · rw [h0, PBG.waveG_zero, form_zero_l (p v) j hj a _ hx']
      · rw [h0, form_zero_r (p v) j hj a _ hwx]
    rw [lhs0, mul_zero]
    symm
    refine Finset.sum_eq_zero fun n _ => ?_
    set ys := List.ofFn fun b => grid b (n b) with hys
    obtain ⟨ε3, hε3, hp, hm⟩ := nv_pair (uB_nv hB F hF v ε hε j hj (KB.plusW ys a) h)
      (uB_nv hB F hF v ε hε j hj (KB.minusW ys a) h')
    have hwp := PBFV.waveG_nice ((p v).T.bs j) ε3 s _ _ hp
    by_cases hh : D.IsLocPt h j
    · rw [uB_neg S p F v ε j hj (KB.minusW ys a) h' fun hh' => hloc ⟨hh, hh'⟩, pj_zero_r (p v) j hj a ys _ hwp, mul_zero]
    · rw [uB_neg S p F v ε j hj (KB.plusW ys a) h hh, PBG.waveG_zero, pj_zero_l (p v) j hj a ys _ hm, mul_zero]

end deg

section kern

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
  {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
  {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}

theorem gam_pos (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) (j : ℕ) : 0 < ΓS S j := by
  have hgpos := g_pos_of_built hB
  have hrd := PBD.rd_pos' E
  unfold ΓS
  exact PBD.gamLev_pos _ _ _ _ (by unfold D.kapG; positivity) (by unfold D.deG; positivity) _

def uY (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (v : Fin S.f) (ε : ℝ) (j : ℕ)
    (hj : j ≤ S.G.r) (w : List C.Letter) (Y : Finset C.LPt) (h : C.LPt) :
    Wd.Ix (Fin w.length) → B.Mat S.G.k (S.G.r - j) → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)) :=
  if h ∈ Y then uB S p F v ε j hj w h else 0

theorem uY_mem (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (v : Fin S.f) (ε : ℝ) (j : ℕ)
    (hj : j ≤ S.G.r) (w : List C.Letter) (Y : Finset C.LPt) (h : C.LPt) (hh : h ∈ Y) :
    uY S p F v ε j hj w Y h = uB S p F v ε j hj w h := by
  unfold uY; rw [if_pos hh]

theorem blockPSD_congr {α : Type} {Y : Finset α} {a a' b b' w w' : α → α → ℂ}
    (ha : ∀ x ∈ Y, ∀ y ∈ Y, a x y = a' x y) (hw : ∀ x ∈ Y, ∀ y ∈ Y, w x y = w' x y)
    (hb : ∀ x ∈ Y, ∀ y ∈ Y, b x y = b' x y) (h : KB.BlockPSD Y Y a w b) : KB.BlockPSD Y Y a' w' b' := by
  rw [PBA.blockPSD_iff] at h ⊢
  refine psd_congr (fun x hx y hy => ?_) h
  cases x with
  | inl x =>
    cases y with
    | inl y => exact ha x (Finset.inl_mem_disjSum.1 hx) y (Finset.inl_mem_disjSum.1 hy)
    | inr y => exact hw x (Finset.inl_mem_disjSum.1 hx) y (Finset.inr_mem_disjSum.1 hy)
  | inr x =>
    cases y with
    | inl y =>
      show conj (w y x) = conj (w' y x)
      rw [hw y (Finset.inl_mem_disjSum.1 hy) x (Finset.inr_mem_disjSum.1 hx)]
    | inr y => exact hb x (Finset.inr_mem_disjSum.1 hx) y (Finset.inr_mem_disjSum.1 hy)

end kern

theorem lam_div_theta {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ) (hinj : ∀ b, Function.Injective (grid b))
    (n : Fin K → Fin (d + 1)) :
    0 < F7.thGrid grid n ∧
      |∏ b, F7.lagCo (grid b) (n b)| / F7.thGrid grid n = ∏ b, ∑ i, |F7.lagCo (grid b) i| := by
  have hs : ∀ b, 0 < ∑ i, |F7.lagCo (grid b) i| := fun b =>
    lt_of_lt_of_le (abs_pos.2 (PBD.lagCo_ne_zero _ (hinj b) (n b)))
      (Finset.single_le_sum (f := fun i => |F7.lagCo (grid b) i|) (fun i _ => abs_nonneg _) (Finset.mem_univ _))
  have hl : ∀ b, 0 < |F7.lagCo (grid b) (n b)| := fun b => abs_pos.2 (PBD.lagCo_ne_zero _ (hinj b) (n b))
  have hth : 0 < F7.thGrid grid n := Finset.prod_pos fun b _ => div_pos (hl b) (hs b)
  refine ⟨hth, ?_⟩
  unfold F7.thGrid
  rw [Finset.abs_prod, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun b _ => ?_
  field_simp [(hl b).ne', (hs b).ne']

theorem ratio_bound {K : ℕ} (ys : Fin K → ℝ) (Pv qv : ℝ → ℝ) (Λ T Γ sa B Xc : ℝ) (hΓ : 0 < Γ) (hsa : 0 < sa)
    (hq : ∀ b, 0 < qv (ys b)) (hP : ∀ b, Pv (ys b) ≠ 0) (hP' : ∀ b, Pv (ys b + 1) ≠ 0)
    (hnode : ∀ b, |Pv (ys b) * Pv (ys b + 1)| / qv (ys b) ≤ B ^ 2) (hΛ : 0 ≤ Λ) (hT : 0 ≤ T) (hB0 : 0 ≤ B)
    (hX : Λ * T ^ K * B ^ K ≤ Xc ^ K) :
    (Λ * T ^ K * (1 / (Γ * sa))) ^ 2 / ((∏ b, qv (ys b)) * (1 / (Γ * ((∏ b, |Pv (ys b)|) * sa))) *
      (1 / (Γ * ((∏ b, |Pv (ys b + 1)|) * sa)))) ≤ (Xc ^ K) ^ 2 := by
  have hQ : 0 < ∏ b, qv (ys b) := Finset.prod_pos fun b _ => hq b
  have hPp : 0 < ∏ b, |Pv (ys b)| := Finset.prod_pos fun b _ => abs_pos.2 (hP b)
  have hPm : 0 < ∏ b, |Pv (ys b + 1)| := Finset.prod_pos fun b _ => abs_pos.2 (hP' b)
  have e : (Λ * T ^ K * (1 / (Γ * sa))) ^ 2 / ((∏ b, qv (ys b)) * (1 / (Γ * ((∏ b, |Pv (ys b)|) * sa))) *
      (1 / (Γ * ((∏ b, |Pv (ys b + 1)|) * sa)))) =
      (Λ * T ^ K) ^ 2 * ∏ b, (|Pv (ys b) * Pv (ys b + 1)| / qv (ys b)) := by
    rw [Finset.prod_div_distrib]
    simp only [abs_mul, Finset.prod_mul_distrib]
    field_simp
  rw [e]
  have hprod : ∏ b, (|Pv (ys b) * Pv (ys b + 1)| / qv (ys b)) ≤ (B ^ 2) ^ K := by
    calc ∏ b, (|Pv (ys b) * Pv (ys b + 1)| / qv (ys b)) ≤ ∏ _b : Fin K, B ^ 2 :=
          Finset.prod_le_prod₀ (fun b _ => div_nonneg (abs_nonneg _) (hq b).le) fun b _ => hnode b
      _ = (B ^ 2) ^ K := by simp
  have h0 : 0 ≤ Λ * T ^ K * B ^ K := by positivity
  calc (Λ * T ^ K) ^ 2 * ∏ b, (|Pv (ys b) * Pv (ys b + 1)| / qv (ys b)) ≤ (Λ * T ^ K) ^ 2 * (B ^ 2) ^ K :=
        mul_le_mul_of_nonneg_left hprod (sq_nonneg _)
    _ = (Λ * T ^ K * B ^ K) ^ 2 := by ring
    _ ≤ (Xc ^ K) ^ 2 := pow_le_pow_left₀ h0 hX 2

end

end Formalism.FourierDecayAlt.P.PBL
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.DerivativeLocalRepresentative
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff Topology

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem derivative_local_representative : RdVRep := by
  intro k r E _ _ X U F f hX hU hc he h hh hhG
  have hc' : ContDiffOn ℝ (((1 : ℕ∞) : WithTop ℕ∞)) F U := by exact_mod_cast hc
  refine ⟨LieDecompositionLocal.rdV_eq_fderiv (m := 1) le_rfl hU hh hhG hc' he hX, ?_⟩
  have hd : DifferentiableAt ℝ F h :=
    (hc.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hh)
  have hloc : Q.LdV X f h = Q.LdV X F h := by
    show deriv (fun t : ℝ => f (NormedSpace.exp ((t : ℂ) • X) * h)) 0 =
      deriv (fun t : ℝ => F (NormedSpace.exp ((t : ℂ) • X) * h)) 0
    apply Filter.EventuallyEq.deriv_eq
    have hcont : Continuous (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) * h) := by
      have h1 := (gpMulR h).continuous.comp (B5.curve_contDiff (1 : B.Mat k r) X).continuous
      refine h1.congr fun t => ?_
      simp [gpMulR_apply]
    have hev : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), NormedSpace.exp ((t : ℂ) • X) * h ∈ U := by
      apply hcont.continuousAt.preimage_mem_nhds
      have h0 : NormedSpace.exp (((0 : ℝ) : ℂ) • X) * h = h := by simp
      rw [h0]
      exact hU.mem_nhds hh
    filter_upwards [hev] with t ht
    exact he _ ht (WeylGroupFacts.uh_mul (B5.exp_mem hX t) hhG)
  rw [hloc]
  exact gp_ldV X h F hd

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.ExponentialDegreeHolds
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

theorem exponential_degree_holds : FExpDeg := by
  intro k r gens
  induction gens with
  | nil =>
    intro _ t ht
    simp only [fexp, List.mem_singleton] at ht
    subst ht
    simp
  | cons gn gs ih =>
    intro hdeg t ht
    have hgn : gn.1.natDegree ≤ 1 := hdeg gn (by simp)
    have ih' := ih (fun g hg => hdeg g (List.mem_cons_of_mem _ hg))
    simp only [fexp, List.mem_append, List.mem_map, List.mem_flatMap] at ht
    rcases ht with ⟨t', ht', rfl⟩ | ⟨dX, hdX, t', ht', rfl⟩
    · obtain ⟨h1, h2⟩ := ih' t' ht'
      refine ⟨?_, ?_⟩
      · have := Polynomial.natDegree_mul_le (p := gn.1) (q := t'.1)
        simp only [List.length_cons]
        omega
      · intro X hX
        obtain ⟨g, hg, d, hd⟩ := h2 X hX
        exact ⟨g, List.mem_cons_of_mem _ hg, d, hd⟩
    · obtain ⟨h1, h2⟩ := ih' t' ht'
      refine ⟨?_, ?_⟩
      · have := Polynomial.natDegree_C_mul_le dX.1 t'.1
        simp only [List.length_cons]
        omega
      · intro X hX
        rcases List.mem_cons.1 hX with rfl | hX
        · exact ⟨gn, by simp, dX.1, hdX⟩
        · obtain ⟨g, hg, d, hd⟩ := h2 X hX
          exact ⟨g, List.mem_cons_of_mem _ hg, d, hd⟩

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.ExponentialSymbolHolds
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

namespace ExponentialSymbolLetters

variable {k r : ℕ} (τ : B.Mat k r → ℂ) (u s : ℂ)

def phi (t : Polynomial ℂ × List (B.Mat k r)) : ℂ := t.1.eval u * s ^ t.2.length * (t.2.map τ).prod

theorem head (p : Polynomial ℂ) (l : List (Polynomial ℂ × List (B.Mat k r))) :
    ((l.map fun t => (p * t.1, t.2)).map (phi τ u s)).sum = p.eval u * (l.map (phi τ u s)).sum := by
  rw [List.map_map, ← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro t _
  simp only [Function.comp_apply, phi, Polynomial.eval_mul]
  ring

theorem letter (d : ℂ) (X : B.Mat k r) (l : List (Polynomial ℂ × List (B.Mat k r))) :
    ((l.map fun t => (Polynomial.C d * t.1, X :: t.2)).map (phi τ u s)).sum =
      (d * s * τ X) * (l.map (phi τ u s)).sum := by
  rw [List.map_map, ← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro t _
  simp only [Function.comp_apply, phi, Polynomial.eval_mul, Polynomial.eval_C, List.length_cons, pow_succ,
    List.map_cons, List.prod_cons]
  ring

theorem letters (L : List (ℂ × B.Mat k r)) (l : List (Polynomial ℂ × List (B.Mat k r))) :
    ((L.flatMap fun dX => l.map fun t => (Polynomial.C dX.1 * t.1, dX.2 :: t.2)).map (phi τ u s)).sum =
      s * (L.map fun dX => dX.1 * τ dX.2).sum * (l.map (phi τ u s)).sum := by
  induction L with
  | nil => simp
  | cons dX L ih =>
    rw [List.flatMap_cons, List.map_append, List.sum_append, letter, ih, List.map_cons, List.sum_cons]
    ring

theorem all (gs : List (GenW k r)) : ((fexp gs).map (phi τ u s)).sum =
    (gs.map fun gn => gn.1.eval u + s * (gn.2.map fun dX => dX.1 * τ dX.2).sum).prod := by
  induction gs with
  | nil => simp [fexp, phi]
  | cons gn gs ih =>
    rw [fexp, List.map_append, List.sum_append, head, letters, List.map_cons, List.prod_cons, ← ih]
    ring

end ExponentialSymbolLetters

theorem exponential_symbol_holds : FExpSymb := by
  intro k r gens τ u s
  exact ExponentialSymbolLetters.all τ u s gens

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end
