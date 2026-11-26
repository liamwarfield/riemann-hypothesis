module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddKapNrmW
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddSSnChainPf

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadJ
open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.LevelPointCoordinates

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

def mLev (P : M.Par) (j : ℕ) (hj : j + 1 ≤ P.r) (τ : ℂ) (γ : B.Mat P.k (P.r - (j + 1))) : B.Mat P.k (P.r - j) :=
  D.castM (by omega : 1 + (P.r - (j + 1)) = P.r - j) (U.mMap P.k 1 (P.r - (j + 1)) (Matrix.of fun _ _ => τ) γ)

def kapJ (P : M.Par) (j : ℕ) : ℂ := ((P.r - j : ℕ) : ℂ) + (P.k : ℂ) / 2

def HeadJ : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F)
    (j : ℕ) (hj : j + 1 ≤ P.r) (w : List C.Letter) (h : C.LPt) (hh : D.IsLocPt h j)
    (γ : B.Mat P.k (P.r - (j + 1))),
    KB.CptCoef p.T.base F → KB.CutWord P p.l0 w → γ ∈ B.GV P.k (P.r - (j + 1)) →
    γ ∈ Q.OmPlus P.k (P.r - (j + 1)) (p.T.bs (j + 1)).z (p.T.bs (j + 1)).z' →
    ∀ φ : Wd.Ix (Fin w.length) → V1 (Wq →L[ℂ] Wp),
    (∀ e τ, τ ≠ 0 → (φ e).1 τ = B.JF (p.T.bs j) (KB.slv p.T F j (by omega) w h hh.2 e) (mLev P j hj τ γ)) →
    ∀ (t : ℂ) (ht : D.IsLocPt (h ++ [(1, t)]) (j + 1)) (e : Wd.Ix (Fin w.length)),
      B.JF (p.T.bs (j + 1)) (KB.slv p.T F (j + 1) hj w (h ++ [(1, t)]) ht.2 e) γ =
        (oneBT (kapJ P j) (D.positionted w) φ e).1 t

end Formalism.FourierDecayAlt.P.LevelPointCoordinates
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDACapTodaVGrp
open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.TVG

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.Qx5 Formalism.FourierDecayAlt.P.Qx2 Formalism.FourierDecayAlt.P.PBN Formalism.FourierDecayAlt.P.PBN.MC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section loc

variable {r : ℕ} {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem pbOp_locO (l : Fin r) {f₁ f₂ : (Fin r → ℂ) → X} (h : ∀ c ∈ OmX r, f₁ c = f₂ c) {c : Fin r → ℂ}
    (hc : c ∈ OmX r) : pbOp l f₁ c = pbOp l f₂ c := by
  have hev : f₁ =ᶠ[nhds c] f₂ := by
    filter_upwards [(Formalism.FourierDecayAlt.P.Qx3.isOpen_OmX r).mem_nhds hc] with c' hc' using h c' hc'
  simp only [pbOp, wirtBar, if_pos hc, hev.fderiv_eq]

theorem pbN_locO (i : ℕ) {f₁ f₂ : (Fin r → ℂ) → X} (h : ∀ c ∈ OmX r, f₁ c = f₂ c) {c : Fin r → ℂ}
    (hc : c ∈ OmX r) : pbN r i f₁ c = pbN r i f₂ c := by
  unfold pbN
  split_ifs with hi
  · exact pbOp_locO _ h hc
  · rfl

theorem iteratedOperator_eqOn_of_eqOn (w : ℂ) : ∀ (m : ℕ) (f₁ f₂ : (Fin r → ℂ) → X), (∀ c ∈ OmX r, f₁ c = f₂ c) →
    ∀ c ∈ OmX r, (kvP r w m).1 f₁ c = (kvP r w m).1 f₂ c ∧ (kvP r w m).2 f₁ c = (kvP r w m).2 f₂ c
  | 0, f₁, f₂, h, c, hc => ⟨h c hc, rfl⟩
  | m + 1, f₁, f₂, h, c, hc => by
    have hin : ∀ c' ∈ OmX r, (w - (m : ℂ)) • f₁ c' - pbN r (r - m - 1) f₁ c' =
        (w - (m : ℂ)) • f₂ c' - pbN r (r - m - 1) f₂ c' := fun c' hc' => by
      rw [h c' hc', pbN_locO _ h hc']
    have ih1 := iteratedOperator_eqOn_of_eqOn w m _ _ hin
    have ih2 := iteratedOperator_eqOn_of_eqOn w m f₁ f₂ h
    simp only [kvP.eq_2, Pi.sub_apply]
    refine ⟨?_, (ih2 c hc).1⟩
    rw [(ih1 c hc).1]
    congr 1
    unfold cbN cbiN
    split_ifs <;> simp [cbOp, cbiOp, (ih2 c hc).2]

theorem kvC_loc (w : ℂ) (m : ℕ) (f₁ f₂ : (Fin r → ℂ) → X) (h : ∀ c ∈ OmX r, f₁ c = f₂ c) {c : Fin r → ℂ}
    (hc : c ∈ OmX r) : kvC r w m f₁ c = kvC r w m f₂ c := (iteratedOperator_eqOn_of_eqOn w m f₁ f₂ h c hc).1

theorem kvC_one (w : ℂ) (f : (Fin r → ℂ) → X) (hr : 1 ≤ r) (c : Fin r → ℂ) :
    kvC r w 1 f c = w • f c - pbOp ⟨r - 1, by omega⟩ f c := by
  show (w - ((0 : ℕ) : ℂ)) • f c - pbN r (r - 0 - 1) f c - cbN r (r - 0) (cbiN r (r - 0 - 1) (fun _ => 0)) c = _
  have h1 : r - 0 - 1 = r - 1 := by omega
  simp only [Nat.cast_zero, sub_zero, Nat.sub_zero]
  unfold pbN cbN
  rw [dite_eq_left (by omega), dite_eq_right (lt_irrefl r)]
  simp

theorem kvC_two (w : ℂ) (m : ℕ) (f : (Fin r → ℂ) → X) (c : Fin r → ℂ) :
    kvC r w (m + 2) f c = kvC r w (m + 1) (fun c => (w - ((m + 1 : ℕ) : ℂ)) • f c - pbN r (r - (m + 1) - 1) f c) c -
      cbN r (r - (m + 1)) (cbiN r (r - (m + 1) - 1) (kvC r w m f)) c := rfl

end loc

section alg

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set (Mx k r)}

abbrev TorV (hD : IsOpen D) (j : ℕ) : Subalgebra ℂ (SA E hD) :=
  Algebra.adjoin ℂ {x | ∃ l : Fin r, l.val < j ∧ x = EA hD (esI k r l) (esI k r l)}

theorem comm_TorV (hD : IsOpen D) (j : ℕ) (p q : Fin (2 * r + k + 1))
    (hp : ∀ l : Fin r, l.val < j → p ≠ esI k r l) (hq : ∀ l : Fin r, l.val < j → q ≠ esI k r l) (P : SA E hD)
    (hP : P ∈ TorV hD j) : Commute (EA hD p q) P := by
  induction hP using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    have h := EA_gl (E := E) hD p q (esI k r l) (esI k r l)
    rw [if_neg (hq l hl), if_neg (fun e => hp l hl e.symm), sub_zero] at h
    exact sub_eq_zero.1 h
  | algebraMap c => exact Algebra.commute_algebraMap_right c _
  | add y₁ y₂ _ _ h₁ h₂ => exact h₁.add_right h₂
  | mul y₁ y₂ _ _ h₁ h₂ => exact h₁.mul_right h₂

theorem TorV_mono (hD : IsOpen D) {j j' : ℕ} (h : j ≤ j') : TorV (E := E) hD j ≤ TorV hD j' := Algebra.adjoin_mono fun x ⟨l, hl, hx⟩ => ⟨l, lt_of_lt_of_le hl h, hx⟩

theorem EAs_mem_TorV (hD : IsOpen D) (l : Fin r) {j : ℕ} (h : l.val < j) :
    EA (E := E) hD (esI k r l) (esI k r l) ∈ TorV hD j := Algebra.subset_adjoin ⟨l, h, rfl⟩

theorem esI_ne {a b : Fin r} (h : a.val ≠ b.val) : esI k r a ≠ esI k r b := by
  intro h'
  have h2 := congrArg Fin.val h'
  simp only [esI] at h2
  have ha := a.isLt
  have hb := b.isLt
  omega

theorem root_action_on_truncated_vector (hD : IsOpen D) (z' : Fin (2 * r + k + 1) → ℂ) (hz' : inWb k r z') (hRR : RightRuleEv)
    {f : Mx k r → E} (hf : SmoothLev k r 0 D f) (hRf : RightEq k r z' 0 D f) (a b : Fin r) (hab : b.val < a.val) :
    ((EA hD (esI k r a) (esI k r b) : SA E hD) : Module.End ℂ (VS k r 0 D E)) ⟨cut k r 0 D f, cut_mem hD hf⟩ =
      (if a.val = b.val + 1 then (1 : ℂ) else 0) • ⟨cut k r 0 D f, cut_mem hD hf⟩ := by
  apply Subtype.ext
  funext g
  by_cases hg : g ∈ Glev k r 0 ∩ D
  · rw [EA_val, ev_E hD _ _ _ hg]
    have hloc := (good_eh (E := E) hD (cI (esI k r a)) (cI (esI k r b))).loc (cut k r 0 D f) f
      (fun x hx => cut_of_mem f hx) g hg
    simp only [posL_cI] at hloc
    rw [posL_cI, posL_cI]
    show EH k r (esI k r a) (esI k r b) (cut k r 0 D f) g = (if a.val = b.val + 1 then (1 : ℂ) else 0) • cut k r 0 D f g
    rw [hloc, hRR E k r z' D f hz' hD hf hRf g hg a b hab, cut_of_mem f hg]
  · show ((Eh hD (cI (esI k r a)) (cI (esI k r b)) ⟨cut k r 0 D f, cut_mem hD hf⟩ : VS k r 0 D E) : Mx k r → E) g =
      (if a.val = b.val + 1 then (1 : ℂ) else 0) • cut k r 0 D f g
    rw [(Eh hD (cI (esI k r a)) (cI (esI k r b)) ⟨cut k r 0 D f, cut_mem hD hf⟩).2.2 g hg,
      show cut k r 0 D f g = 0 from Set.indicator_of_notMem hg f, smul_zero]

theorem la_torus (hD : IsOpen D) (hTC : TorusCellv) (v₀ : VS k r 0 D E) (g₀ : Mx k r)
    (hg₀ : g₀ ∈ Glev k r (Fin.last r)) (hcell : ∀ c ∈ OmX r, wCell k r (Fin.last r) c * g₀ ∈ Glev k r 0 ∩ D)
    (l : Fin r) (w' : ℂ) (x : SA E hD) (c : Fin r → ℂ) (hc : c ∈ OmX r) :
    La hD v₀ (wCell k r (Fin.last r) c * g₀) (Tm (EA hD) w' (esI k r l) (esI k r l) * x) =
      w' • La hD v₀ (wCell k r (Fin.last r) c * g₀) x -
        pbOp l (fun c' => La hD v₀ (wCell k r (Fin.last r) c' * g₀) x) c := by
  have hγ := hcell c hc
  rw [La_apply, La_apply]
  simp only [Tm, Subalgebra.coe_mul, Subalgebra.coe_add, Module.End.mul_apply, LinearMap.add_apply, EA_val,
    Submodule.coe_add, Pi.add_apply, ite_true, Subalgebra.coe_algebraMap, Module.algebraMap_end_apply,
    Submodule.coe_smul, Pi.smul_apply]
  rw [ev_E hD _ _ _ hγ, posL_cI, hTC E k r D _ hD ((x : Module.End ℂ (VS k r 0 D E)) v₀).2.1 c hc g₀ hg₀ hγ.2 l,
    sub_eq_add_neg]
  rfl

end alg

section claim

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set (Mx k r)}

theorem claimV (hRR : RightRuleEv) (hLR : LeftRuleCellv) (hTC : TorusCellv) (hCh : MirrorChainExpansion)
    (hD : IsOpen D) (v₀ : VS k r 0 D E) (g₀ : Mx k r) (w : ℂ)
    (z z' : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hz' : inWb k r z')
    (hN : ∀ g ∈ Glev k r 0 ∩ D, ∀ n ∈ Nlev k r 0, n * g ∈ D)
    {f : Mx k r → E} (hf : SmoothLev k r 0 D f) (hLf : LeftEq k r z 0 D f) (hRf : RightEq k r z' 0 D f)
    (hv : v₀ = ⟨cut k r 0 D f, cut_mem hD hf⟩) (hg₀ : g₀ ∈ Glev k r (Fin.last r))
    (hcell : ∀ c ∈ OmX r, wCell k r (Fin.last r) c * g₀ ∈ Glev k r 0 ∩ D) :
    ∀ (m : ℕ), m ≤ r → ∀ P ∈ TorV hD (r - m), ∀ c ∈ OmX r,
      La hD v₀ (wCell k r (Fin.last r) c * g₀) (qminor (EA hD) (colsVm k r m) (colsVm k r m) w * P) =
        kvC r w m (fun c' => La hD v₀ (wCell k r (Fin.last r) c' * g₀) P) c := by
  have hLv : LeftEq k r z 0 D (v₀ : Mx k r → E) := by rw [hv]; exact leftEq_cut z hN hLf
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro hm P hP c hc
  rcases m with _ | _ | m
  · rw [MC.qminor_zero, one_mul]
    rfl
  · rw [MC.qminor_one]
    have hx0 : colsVm k r 1 0 = esI k r ⟨r - 1, by omega⟩ := by
      ext
      simp only [colsVm, esI, Fin.val_zero]
      omega
    rw [hx0, la_torus hD hTC v₀ g₀ hg₀ hcell ⟨r - 1, by omega⟩ w P c hc, kvC_one w _ hm c]
  · have hm2 : m + 2 ≤ r := hm
    have hP1 : P ∈ TorV hD (r - (m + 1)) := TorV_mono hD (by omega) hP
    have hP0 : P ∈ TorV hD (r - m) := TorV_mono hD (by omega) hP
    set ρ : ℂ := star (c ⟨r - m - 1, by omega⟩) / star (c ⟨r - m - 2, by omega⟩) with hρ
    set LaP : SA E hD →ₗ[ℂ] E := (La hD v₀ (wCell k r (Fin.last r) c * g₀)).comp (LinearMap.mulRight ℂ P) with hLaP
    have hLaP_apply : ∀ x, LaP x = La hD v₀ (wCell k r (Fin.last r) c * g₀) (x * P) := fun x => rfl
    have hnot : ∀ a : Fin r, r - m - 2 ≤ a.val → ∀ l' : Fin r, l'.val < r - (m + 2) → esI k r a ≠ esI k r l' :=
      fun a ha l' hl' => esI_ne (by omega)
    have hR0 : ∀ (x : SA E hD) (a : Fin r), r - m - 1 < a.val →
        LaP (x * EA hD (esI k r a) (esI k r ⟨r - m - 2, by omega⟩)) = 0 := by
      intro x a ha
      rw [hLaP_apply, mul_assoc, (comm_TorV hD (r - (m + 2)) _ _ (hnot a (by omega))
        (hnot ⟨r - m - 2, by omega⟩ le_rfl) P hP).eq, ← mul_assoc, La_apply, Subalgebra.coe_mul, Module.End.mul_apply]
      conv_lhs => rw [hv]
      rw [root_action_on_truncated_vector hD z' hz' hRR hf hRf a ⟨r - m - 2, by omega⟩ (by simp only; omega), if_neg (by simp only; omega),
        zero_smul, map_zero]
      rfl
    have hR1 : ∀ x : SA E hD,
        LaP (x * EA hD (esI k r ⟨r - m - 1, by omega⟩) (esI k r ⟨r - m - 2, by omega⟩)) = LaP x := by
      intro x
      rw [hLaP_apply, hLaP_apply, mul_assoc, (comm_TorV hD (r - (m + 2)) _ _ (hnot ⟨r - m - 1, by omega⟩ (by simp only; omega))
        (hnot ⟨r - m - 2, by omega⟩ le_rfl) P hP).eq, ← mul_assoc, La_apply, La_apply, Subalgebra.coe_mul,
        Module.End.mul_apply]
      conv_lhs => rw [hv]
      rw [root_action_on_truncated_vector hD z' hz' hRR hf hRf ⟨r - m - 1, by omega⟩ ⟨r - m - 2, by omega⟩ (by simp only; omega),
        if_pos (by simp only; omega), one_smul, ← hv]
    have hL : ∀ (x : SA E hD) (b : Fin r), r - m - 2 < b.val →
        LaP (EA hD (esI k r ⟨r - m - 2, by omega⟩) (esI k r b) * x) =
          (if b.val = r - m - 1 then ρ else 0) • LaP x := by
      intro x b hb
      rw [hLaP_apply, hLaP_apply, mul_assoc, La_apply, La_apply, Subalgebra.coe_mul, Module.End.mul_apply, EA_val,
        ev_E hD _ _ _ (hcell c hc), posL_cI, posL_cI]
      have hsm := (((x * P : SA E hD) : Module.End ℂ (VS k r 0 D E)) v₀).2.1
      have hle := leftEq_SA hD z hN (x * P) v₀ hLv
      rw [hLR E k r z D _ hz hD hN hsm hle c hc g₀ hg₀ (hcell c hc).2 b ⟨r - m - 2, by omega⟩ (by simp only; omega)]
      congr 1
      by_cases hbm : b.val = r - m - 1
      · have hb' : b = ⟨r - m - 1, by omega⟩ := Fin.ext hbm
        rw [if_pos (by simp only; omega), if_pos hbm, hρ, congrArg c hb']
      · rw [if_neg (by simp only; omega), if_neg hbm]
    have hX := hCh (SA E hD) E k r (EA (E := E) hD) LaP ρ (EA_gl (E := E) hD) m hm2 w hR0 hR1 hL
    set T := Tm (EA (E := E) hD) (w - ((m + 1 : ℕ) : ℂ)) (esI k r ⟨r - m - 2, by omega⟩)
      (esI k r ⟨r - m - 2, by omega⟩) with hT
    have hTmem : T ∈ TorV hD (r - (m + 1)) := by
      rw [hT]
      unfold Tm
      rw [if_pos rfl]
      exact Subalgebra.add_mem _ (Subalgebra.algebraMap_mem _ _) (EAs_mem_TorV hD ⟨r - m - 2, by omega⟩ (by simp only; omega))
    have hTP : T * P ∈ TorV hD (r - (m + 1)) := Subalgebra.mul_mem _ hTmem hP1
    have ih1 := ih (m + 1) (by omega) (by omega) (T * P) hTP c hc
    have ih0 := ih m (by omega) (by omega) P hP0 c hc
    rw [hLaP_apply, hLaP_apply, hLaP_apply, mul_assoc] at hX
    rw [hX, ih1, ih0, kvC_two]
    have hloc := kvC_loc w (m + 1) (fun c' => La hD v₀ (wCell k r (Fin.last r) c' * g₀) (T * P))
      (fun c' => (w - ((m + 1 : ℕ) : ℂ)) • La hD v₀ (wCell k r (Fin.last r) c' * g₀) P -
        pbN r (r - (m + 1) - 1) (fun c'' => La hD v₀ (wCell k r (Fin.last r) c'' * g₀) P) c')
      (fun c' hc' => by
        rw [hT, la_torus hD hTC v₀ g₀ hg₀ hcell ⟨r - m - 2, by omega⟩ _ P c' hc']
        unfold pbN
        rw [dite_eq_left (by omega)]
        have e : (⟨r - (m + 1) - 1, by omega⟩ : Fin r) = ⟨r - m - 2, by omega⟩ := Fin.ext (by simp only; omega)
        rw [e]) hc
    rw [hloc]
    congr 1
    unfold cbN cbiN
    rw [dite_eq_left (by omega), dite_eq_left (by omega)]
    have e1 : (⟨r - (m + 1), by omega⟩ : Fin r) = ⟨r - m - 1, by omega⟩ := Fin.ext (by simp only; omega)
    have e2 : (⟨r - (m + 1) - 1, by omega⟩ : Fin r) = ⟨r - m - 2, by omega⟩ := Fin.ext (by simp only; omega)
    rw [e1, e2]
    simp only [cbOp, cbiOp, hρ, div_eq_mul_inv, mul_smul]

end claim

end Formalism.FourierDecayAlt.P.CutMP.TVG
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDACapTodaVRules
open Matrix
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.TVG

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.Qx3 Formalism.FourierDecayAlt.P.WeylCellAction

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section diff

variable {r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem pbOp_line {F₁ F₂ : (Fin r → ℂ) → E} {c : Fin r → ℂ} (l : Fin r) (h₁ : DifferentiableAt ℝ F₁ c)
    (h₂ : DifferentiableAt ℝ F₂ c) (h : ∀ c' : Fin r → ℂ, (∀ a, a ≠ l → c' a = c a) → F₁ c' = F₂ c') :
    pbOp l F₁ c = pbOp l F₂ c := by
  have hv : ∀ w : ℂ, fderiv ℝ F₁ c (Pi.single l w) = fderiv ℝ F₂ c (Pi.single l w) := fun w =>
    fderiv_line h₁ h₂ fun t => h _ fun a ha => by simp [ha]
  simp only [pbOp, wirtBar, hv]

end diff

theorem mirror_right_rule_holds : RightRuleEv := by
  intro E _ _ k r z' D f hz' hD hS hR g hg a b hab
  have ha := a.isLt
  have hc : Continuous fun x : Mx k r => g * x := cont_lmul g
  have hD' : IsOpen {x : Mx k r | g * x ∈ D} := hD.preimage hc
  have hS' : SmoothLev k r b.castSucc {x | g * x ∈ D} (fun x => f (g * x)) :=
    smooth_left g (fun x hx => glev0 hg.1 hx) hS
  have hR' : RightEq k r z' b.castSucc {x | g * x ∈ D} (fun x => f (g * x)) := by
    intro x hx n hn
    have := hR (g * x) ⟨glev0 hg.1 hx.1, hx.2⟩ n (nlev_mono (zero_le' _) hn)
    simpa [Matrix.mul_assoc] using this
  have h1 : (1 : Mx k r) ∈ Glev k r b.castSucc ∩ {x | g * x ∈ D} :=
    ⟨glev_one _, by simpa using hg.2⟩
  have hrule := (Formalism.FourierDecayAlt.P.right_action_rule E k r z' b {x | g * x ∈ D} (fun x => f (g * x)) hz' hD' hS' hR'
    1 h1).2.1
  have hjlt : 2 * r + k - a.val - b.val - 1 < mdim k r b.succ := by simp [mdim]; omega
  have hpos : posL k r b.succ ⟨2 * r + k - a.val - b.val - 1, hjlt⟩ = esI k r a := by
    simp [posL, esI, Fin.ext_iff]; omega
  have h := hrule ⟨2 * r + k - a.val - b.val - 1, hjlt⟩
  rw [hpos, eH_left, Matrix.mul_one] at h
  rw [h]
  congr 1
  simp only [xbv, fvec, hpos, Fin.val_succ]
  rw [dif_pos (show b.val + 1 < r by omega)]
  rw [Formalism.FourierDecayAlt.P.SignAntidiagonal.herm_bvec_eI]
  by_cases hh : a.val = b.val + 1
  · simp [hh, bvec, esI]
  · rw [if_neg hh]
    simp only [bvec, Pi.single_apply, esI, Fin.ext_iff]
    rw [if_neg (by omega)]

theorem mirror_torus_cell_holds : TorusCellv := by
  intro E _ _ k r D f hD hS c hc g hg hWD l
  have hcne : ∀ a, c a ≠ 0 := hc
  have hl := l.isLt
  have hW0 : wCell k r l.castSucc c ∈ Glev k r 0 := wlist_glev hc _
  have htail : ∀ n : ℕ, ∀ i : Fin (r + 1), i.val = l.val + 1 + n →
      ∃ T : Mx k r, T ∈ Glev k r l.succ ∧
        ∀ c' : Fin r → ℂ, (∀ a : Fin r, l.val < a.val → c' a = c a) →
          wCell k r i c' = wCell k r l.succ c' * T := by
    intro n
    induction n with
    | zero =>
      intro i hi
      have : i = l.succ := Fin.ext (by simpa using hi)
      subst i
      exact ⟨1, glev_one _, fun _ _ => by simp⟩
    | succ n ih =>
      intro i hi
      let j : Fin r := ⟨l.val + 1 + n, by have := i.isLt; omega⟩
      rw [show i = j.succ from Fin.ext (by simpa [j, Nat.add_assoc] using hi)]
      obtain ⟨T, hTG, hTc⟩ := ih j.castSucc (by simp [j])
      have hlj : l.val < j.val := by simp [j]; omega
      refine ⟨T * w1 k r j (c j), glev_mul hTG ?_, ?_⟩
      · exact glev_mono (by simpa [Fin.le_def] using hlj)
          (Formalism.FourierDecayAlt.P.weyl_level_element_properties k r j (c j) (hcne j)).1
      · intro c' hc'
        rw [Formalism.FourierDecayAlt.P.Qx6.wCell_succ, hTc c' hc', hc' j hlj, Matrix.mul_assoc]
  obtain ⟨T, hTG, hTc⟩ := htail (r - l.val - 1) (Fin.last r) (by simp; omega)
  have hT := hTc c (fun _ _ => rfl)
  have hg₁ : T * g ∈ Glev k r l.succ := glev_mul hTG (glev_mono (Fin.le_last _) hg)
  have hsplit : wCell k r (Fin.last r) c * g = wCell k r l.castSucc c * (w1 k r l (c l) * (T * g)) := by
    simp only [hT, Formalism.FourierDecayAlt.P.Qx6.wCell_succ, Matrix.mul_assoc]
  have hWx : ∀ x ∈ Glev k r l.castSucc, wCell k r l.castSucc c * x ∈ Glev k r 0 := fun x hx => glev0 hW0 hx
  have hS' := smooth_left (E := E) (f := f) (D := D) (wCell k r l.castSucc c) hWx hS
  have hD' : IsOpen {x : Mx k r | wCell k r l.castSucc c * x ∈ D} := hD.preimage (cont_lmul _)
  have hpt : w1 k r l (c l) * (T * g) ∈ {x | wCell k r l.castSucc c * x ∈ D} := by
    show _ ∈ D
    rw [← hsplit]; exact hWD
  have hrule := (Formalism.FourierDecayAlt.P.torus_action_rule E k r l {x | wCell k r l.castSucc c * x ∈ D}
    (fun x => f (wCell k r l.castSucc c * x)) hD' hS' c hc (T * g) hg₁ hpt).2
  rw [eH_left, ← hsplit] at hrule
  rw [hrule]
  have hd₂ : DifferentiableAt ℝ (fun c' => f (wCell k r (Fin.last r) c' * g)) c := by
    refine diff_comp hS (φ := fun c' => wCell k r (Fin.last r) c' * g)
      (cdo_mul (wlist_smooth _) contDiffOn_const)
      (fun _ hc' => glev_mul (wlist_glev hc' _) (glev_mono (zero_le' _) hg)) hc hWD
  have hd₁ : DifferentiableAt ℝ (fun c' => f (wCell k r l.castSucc c * (w1 k r l (c' l) * (T * g)))) c := by
    refine diff_comp hS (φ := fun c' => wCell k r l.castSucc c * (w1 k r l (c' l) * (T * g)))
      (Formalism.FourierDecayAlt.P.Qx6.cd_matmul contDiffOn_const
        (Formalism.FourierDecayAlt.P.Qx6.cd_matmul (Formalism.FourierDecayAlt.P.Qx6.contDiffOn_weyl_cell l) contDiffOn_const)) (fun c' hc' => ?_) hc ?_
    · refine glev_mul hW0 (glev_mul (glev_mono (zero_le' _) (Formalism.FourierDecayAlt.P.weyl_level_element_properties k r l (c' l) (hc' l)).1)
        (glev_mono (zero_le' _) hg₁))
    · rw [← hsplit]; exact hWD
  congr 1
  refine pbOp_line l hd₁ hd₂ fun c' hc' => ?_
  have hlow : wCell k r l.castSucc c' = wCell k r l.castSucc c :=
    Formalism.FourierDecayAlt.P.Qx6.wCell_congr fun a ha => hc' a (fun h => by subst h; simp at ha)
  have hup := hTc c' fun a ha => hc' a (fun h => by subst h; omega)
  show f (wCell k r l.castSucc c * (w1 k r l (c' l) * (T * g))) = f (wCell k r (Fin.last r) c' * g)
  rw [hup, Formalism.FourierDecayAlt.P.Qx6.wCell_succ, hlow, Matrix.mul_assoc, Matrix.mul_assoc]

theorem herm_smul_right' {k r : ℕ} (v w : Fin (2 * r + k + 1) → ℂ) (s : ℂ) :
    herm (Hpk k r) v (s • w) = star s * herm (Hpk k r) v w := by
  unfold herm
  rw [star_smul, smul_dotProduct, smul_eq_mul]

theorem mirror_left_rule_cell_holds : LeftRuleCellv := by
  intro E _ _ k r z D f hz hD hDN hS hL c hc g hg hWD a b hba
  have ha := a.isLt
  have hcne : ∀ l, c l ≠ 0 := hc
  have hW0 : wCell k r b.castSucc c ∈ Glev k r 0 := wlist_glev hc _
  have hWcomm (n : Mx k r) (hn : n ∈ Glev k r b.castSucc) :
      wCell k r b.castSucc c * n = n * wCell k r b.castSucc c :=
    wlist_comm b.castSucc c _ (fun _ ha => of_decide_eq_true (List.mem_filter.mp ha).2) hn
  have htail : ∀ n : ℕ, ∀ i : Fin (r + 1), i.val = b.val + 1 + n →
      ∃ T : Mx k r, wCell k r i c = wCell k r b.succ c * T ∧ T ∈ Glev k r b.succ ∧
        (∀ a : Fin r, b.val < a.val →
          T *ᵥ bvec (eI k r a) = if a.val < i.val then c a • bvec (esI k r a) else bvec (eI k r a)) ∧
        (∀ a : Fin r, i.val ≤ a.val → T *ᵥ bvec (esI k r a) = bvec (esI k r a)) := by
    intro n
    induction n with
    | zero =>
      intro i hi
      have : i = b.succ := Fin.ext (by simpa using hi)
      subst i
      refine ⟨1, by simp, glev_one _, fun a ha => ?_, fun _ _ => by simp⟩
      rw [ite_eq_right (by simp; omega), Matrix.one_mulVec]
    | succ n ih =>
      intro i hi
      let j : Fin r := ⟨b.val + 1 + n, by have := i.isLt; omega⟩
      rw [show i = j.succ from Fin.ext (by simpa [j, Nat.add_assoc] using hi)]
      obtain ⟨T, hT, hTG, hTe, hTs⟩ := ih j.castSucc (by simp [j])
      have hbj : b.val + 1 ≤ j.val := by simp [j]
      refine ⟨T * w1 k r j (c j), ?_, glev_mul hTG ?_, ?_, ?_⟩
      · rw [Formalism.FourierDecayAlt.P.Qx6.wCell_succ, hT, Matrix.mul_assoc]
      · exact glev_mono (by simpa [Fin.le_def] using hbj)
          (Formalism.FourierDecayAlt.P.weyl_level_element_properties k r j (c j) (hcne j)).1
      · intro a ha
        rw [← Matrix.mulVec_mulVec, weyl_cell_mulVec_basis]
        by_cases haj : a = j
        · subst a
          rw [sw_e, dd_e, Matrix.mulVec_smul, hTs _ (by simp), ite_eq_left (by simp)]
        · have hne : a.val ≠ j.val := fun h => haj (Fin.ext h)
          have h₁ : eI k r a ≠ eI k r j := by simpa [eI, Fin.ext_iff] using hne
          have h₂ : eI k r a ≠ esI k r j := by simp [eI, esI, Fin.ext_iff]; have := j.isLt; omega
          have hlt : a.val < j.castSucc.val ↔ a.val < j.succ.val := by simp; omega
          rw [sw_o j h₁ h₂, dd_o j _ h₁ h₂, one_smul, hTe a ha]
          simp only [hlt]
      · intro a ha
        have h₁ : esI k r a ≠ eI k r j := by simp [eI, esI, Fin.ext_iff]; have := a.isLt; omega
        have h₂ : esI k r a ≠ esI k r j := by
          have ha' := a.isLt
          have hja : j.val < a.val := ha
          intro h
          have hv := congrArg Fin.val h
          change 2 * r + k - a.val = 2 * r + k - j.val at hv
          omega
        rw [← Matrix.mulVec_mulVec, weyl_cell_mulVec_basis, sw_o j h₁ h₂, dd_o j _ h₁ h₂, one_smul,
          hTs a (by simp at ha ⊢; omega)]
  obtain ⟨T, hT, hTG, hTe, -⟩ := htail (r - b.val - 1) (Fin.last r) (by simp; omega)
  have hg₁ : T * g ∈ Glev k r b.succ := glev_mul hTG (glev_mono (Fin.le_last _) hg)
  have hsplit : wCell k r (Fin.last r) c * g = wCell k r b.castSucc c * (w1 k r b (c b) * (T * g)) := by
    simp only [hT, Formalism.FourierDecayAlt.P.Qx6.wCell_succ, Matrix.mul_assoc]
  have hWx : ∀ x ∈ Glev k r b.castSucc, wCell k r b.castSucc c * x ∈ Glev k r 0 := fun x hx => glev0 hW0 hx
  have hS' := smooth_left (E := E) (f := f) (D := D) (wCell k r b.castSucc c) hWx hS
  have hcont : Continuous fun x : Mx k r => wCell k r b.castSucc c * x := cont_lmul _
  have hD' : IsOpen {x : Mx k r | wCell k r b.castSucc c * x ∈ D} := hD.preimage hcont
  have hN' : ∀ x ∈ Glev k r b.castSucc ∩ {x | wCell k r b.castSucc c * x ∈ D}, ∀ n ∈ Nlev k r b.castSucc,
      n * x ∈ {x | wCell k r b.castSucc c * x ∈ D} := by
    intro x hx n hn
    show wCell k r b.castSucc c * (n * x) ∈ D
    rw [← Matrix.mul_assoc, hWcomm n hn.2, Matrix.mul_assoc]
    exact hDN _ ⟨hWx x hx.1, hx.2⟩ n (nlev_mono (zero_le' _) hn)
  have hL' : LeftEq k r z b.castSucc {x | wCell k r b.castSucc c * x ∈ D} (fun x => f (wCell k r b.castSucc c * x)) := by
    intro x hx n hn
    show f (wCell k r b.castSucc c * (n * x)) = _ • f (wCell k r b.castSucc c * x)
    rw [← Matrix.mul_assoc, hWcomm n hn.2, Matrix.mul_assoc]
    exact hL _ ⟨hWx x hx.1, hx.2⟩ n (nlev_mono (zero_le' _) hn)
  have hpt : w1 k r b (c b) * (T * g) ∈ {x | wCell k r b.castSucc c * x ∈ D} := by
    show _ ∈ D
    rw [← hsplit]; exact hWD
  have hrule := (Formalism.FourierDecayAlt.P.left_action_rule E k r z b {x | wCell k r b.castSucc c * x ∈ D}
    (fun x => f (wCell k r b.castSucc c * x)) hz hD' hS' hN' hL' (c b) (hcne b) (T * g) hg₁ hpt).2.1
  have hjlt : 2 * r + k - a.val - b.val - 1 < mdim k r b.succ := by simp [mdim]; omega
  have hpos : posL k r b.succ ⟨2 * r + k - a.val - b.val - 1, hjlt⟩ = esI k r a := by
    simp [posL, esI, Fin.ext_iff]; omega
  have h := hrule ⟨2 * r + k - a.val - b.val - 1, hjlt⟩
  rw [hpos, eH_left, ← hsplit] at h
  rw [h]
  congr 1
  have hb1 : (b.succ : Fin (r + 1)).val < r := by simp; omega
  have hga : g *ᵥ bvec (eI k r a) = bvec (eI k r a) := (hg.2 a (by simp)).1
  have hTa := hTe a hba
  rw [if_pos (by simp)] at hTa
  have hU : T * g ∈ UH (Hpk k r) := hg₁.1
  have key : ((T * g)⁻¹ *ᵥ bvec (eI k r ⟨b.val + 1, by omega⟩)) (esI k r a) =
      if a.val = b.val + 1 then star (c a) else 0 := by
    rw [← Formalism.FourierDecayAlt.P.SignAntidiagonal.herm_bvec_eI ((T * g)⁻¹ *ᵥ bvec (eI k r ⟨b.val + 1, by omega⟩)) a,
      ← Formalism.FourierDecayAlt.P.Qx2.herm_uh hU, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hU), Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hga, hTa,
      herm_smul_right', ← Formalism.FourierDecayAlt.P.Qx2.herm_star, Formalism.FourierDecayAlt.P.SignAntidiagonal.herm_bvec_eI]
    by_cases hh : a.val = b.val + 1
    · rw [if_pos hh]
      have : (bvec (esI k r a) : Fin (2 * r + k + 1) → ℂ) (esI k r ⟨b.val + 1, by omega⟩) = 1 := by
        simp [bvec, esI, hh]
      rw [this, star_one, mul_one]
    · rw [if_neg hh]
      have : (bvec (esI k r a) : Fin (2 * r + k + 1) → ℂ) (esI k r ⟨b.val + 1, by omega⟩) = 0 := by
        simp only [bvec, Pi.single_apply, esI, Fin.ext_iff]
        rw [if_neg (by omega)]
      rw [this, star_zero, mul_zero]
  have hy : yv k r z b.succ (T * g) ⟨2 * r + k - a.val - b.val - 1, hjlt⟩ =
      if a.val = b.val + 1 then star (c a) else 0 := by
    simp only [yv, hpos, fvec, dif_pos hb1]
    exact key
  rw [hy]
  by_cases hh : a.val = b.val + 1
  · rw [if_pos hh, if_pos hh, div_eq_inv_mul]
  · rw [if_neg hh, if_neg hh, mul_zero]

end Formalism.FourierDecayAlt.P.CutMP.TVG
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddKapShared
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddKapFinal
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddKapAsm
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA

open NumberField Formalism.FourierDecayAlt.P.CutMP

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem jABddKapQQ_of_kapRealiser (hR : KapRealiser) : JABddKapQQ := by
  obtain ⟨K, hK, hR⟩ := hR
  refine ⟨K, hK, ?_⟩
  intro Cc Cb hCc hCb E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e L hFr hGa hQQ hL b hb
  obtain ⟨κ, rfl⟩ := hb
  obtain ⟨c, ca, hadj, hc, hca, he, hea, hbc, hbca, hbig⟩ :=
    hR Cc Cb hCc hCb E Wp Wq S T f χ ν' m₀ top A₀ hB v e hFr hGa hQQ κ
  refine ⟨SSn.orderZeroDifferentialOperator S v c ca hadj, SSn.order_zero_operator_order, ⟨?_, ?_⟩, ?_, fun J hJ => ⟨?_, ?_, ?_⟩⟩
  · intro Tm hTm
    simp only [SSn.orderZeroDifferentialOperator, List.mem_singleton] at hTm
    subst hTm
    exact ⟨hc, hca⟩
  · intro p hp f' _ g hg
    rw [SSn.order_zero_operator_apply, SSn.order_zero_operator_apply]
    exact he p hp g hg.1 _
  · intro Tm hTm ε hε m
    simp only [SSn.orderZeroDifferentialOperator, List.mem_singleton] at hTm
    subst hTm
    obtain ⟨C1, h1⟩ := hbc ε hε m
    obtain ⟨C2, h2⟩ := hbca ε hε m
    refine ⟨max C1 C2, fun u w hu hw hl g hg hG => ⟨?_, ?_⟩⟩
    · have hpow : 0 ≤ B.gN g ^ (Cb * ((S.G.r : ℝ) + 1) * m) := Real.rpow_nonneg (Real.sqrt_nonneg _) _
      rw [zero_add]
      exact (h1 u w hu hw hl g hg hG).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hpow)
    · have hpow : 0 ≤ B.gN g ^ (Cb * ((S.G.r : ℝ) + 1) * m) := Real.rpow_nonneg (Real.sqrt_nonneg _) _
      rw [zero_add]
      exact (h2 u w hu hw hl g hg hG).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hpow)
  · rw [SSn.order_zero_operator_apply]; exact SSn.equivariant_coefficient_preserves_forms hc he hJ
  · rw [SSn.order_zero_operator_adjoint]; exact SSn.equivariant_coefficient_preserves_forms hca hea hJ
  · rw [SSn.order_zero_operator_apply]
    exact trJ_kap_of_bigCell S T v e κ c hbig J

theorem jABddKapQQ_of_typeProj (hB : DatumBd) (hG : SSn.SSnGeom) (hP : TypeProj) : JABddKapQQ :=
  jABddKapQQ_of_kapRealiser (kapRealiser_of_typeProj hB hG hP)

end

end Formalism.FourierDecayAlt.P.CutMP.JA
end

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA

theorem datum_bound_holds : DatumBd := datumBd_of_chain SSn.ChainPf.chain_bound_holds

theorem jABddKapQQ_of_leaves (hG : SSn.SSnGeom) (hP : TypeProj) : JABddKapQQ :=
  jABddKapQQ_of_typeProj datum_bound_holds hG hP

theorem jABddKapQQ_of_cut (hG : SSn.SSnGeom) (hPE : PRho.PRhoExists) (hGL : PRho.GaugeLines)
    (hDU : SSn.Rep.DatumUnit) (hNW : NrmWFacts) : JABddKapQQ :=
  jABddKapQQ_of_leaves hG (typeProj_of hPE hGL hDU hNW)

end Formalism.FourierDecayAlt.P.CutMP.JA
end

namespace Formalism.FourierDecayAlt.P.CutMP.JA

theorem jABddKapQQ_of_shared (hG : SSn.SSnGeom) (hPE : PRho.PRhoExists) (hGL : PRho.GaugeLines)
    (hDU : SSn.Rep.DatumUnit) : JABddKapQQ :=
  jABddKapQQ_of_cut hG hPE hGL hDU weighted_norm_facts_hold

end Formalism.FourierDecayAlt.P.CutMP.JA
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepAsm
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem conj_phD_sq {r : ℕ} {c : Fin r → ℂ} (hc : ∀ a, c a ≠ 0) :
    (conj (SSn.phD c)) ^ 2 = (∏ i, conj (c i)) * ∏ i, (c i)⁻¹ := by
  have hP : (∏ i, c i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => hc a
  rw [← map_prod, Finset.prod_inv_distrib]
  unfold SSn.phD
  set D := ∏ i, c i with hD
  have hn : ((‖D‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hP
  have hnn : ((‖D‖ : ℝ) : ℂ) ^ 2 = D * conj D := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  rw [map_div₀, Complex.conj_ofReal, div_pow, hnn]
  field_simp

section gen

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem cd_comp {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {U V W : Type} [NormedAddCommGroup U]
    [NormedSpace ℂ U] [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
    {n : WithTop ℕ∞} {g : X → V →L[ℂ] W} {f : X → U →L[ℂ] V} (hg : ContDiff ℝ n g) (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (fun x => (g x).comp (f x)) :=
  ((ContinuousLinearMap.compL ℂ U V W).bilinearRestrictScalars ℝ).isBoundedBilinearMap.contDiff.comp (hg.prodMk hf)

theorem hsVec_zero' : B.hsVec (0 : Wq →L[ℂ] Wp) = 0 := by
  unfold B.hsVec; ext i; simp

theorem hsInner_zero_l (B' : Wq →L[ℂ] Wp) : B.hsInner (0 : Wq →L[ℂ] Wp) B' = 0 := by
  unfold B.hsInner; rw [hsVec_zero', inner_zero_right]

theorem hsInner_zero_r (A : Wq →L[ℂ] Wp) : B.hsInner A (0 : Wq →L[ℂ] Wp) = 0 := by
  unfold B.hsInner; rw [hsVec_zero', inner_zero_left]

theorem inner_hs_smul (c : ℂ) (A B' : Wq →L[ℂ] Wp) :
    inner ℂ (B.hsVec A) (B.hsVec (c • B')) = c * inner ℂ (B.hsVec A) (B.hsVec B') := by
  rw [Formalism.FourierDecayAlt.P.JCTx2.hsVec_smul', inner_smul_right]

theorem mat_gen {Ty : Type} [Fintype Ty] [DecidableEq Ty] (Qd : Ty → (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp))
    (T0 : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) (c : Ty → Ty → ℂ) (e : Ty → (Wq →L[ℂ] Wp))
    (hQadj : ∀ σ A B', B.hsInner (Qd σ A) B' = B.hsInner A (Qd σ B'))
    (hline : ∀ σ ρ, Qd σ (e ρ) = if σ = ρ then e ρ else 0) (π ρ : Ty) :
    B.hsInner (∑ π', ∑ ρ', c π' ρ' • Qd ρ' (T0 (Qd π' (e π)))) (e ρ) = c π ρ * B.hsInner (T0 (e π)) (e ρ) := by
  rw [kap_hsInner_sum_left, Finset.sum_eq_single π]
  · rw [kap_hsInner_sum_left, Finset.sum_eq_single ρ]
    · rw [kap_hsInner_smul_left, hQadj, hline π π, hline ρ ρ, if_pos rfl, if_pos rfl]
    · intro ρ' _ hne
      rw [kap_hsInner_smul_left, hQadj, hline ρ' ρ, if_neg hne, hsInner_zero_r, mul_zero]
    · intro h; exact absurd (Finset.mem_univ ρ) h
  · intro π' _ hne
    rw [hline π' π, if_neg hne, map_zero]
    simp only [map_zero, smul_zero, Finset.sum_const_zero]
    exact hsInner_zero_l _
  · intro h; exact absurd (Finset.mem_univ π) h

theorem mat_gen' {Ty : Type} [Fintype Ty] [DecidableEq Ty] (Qd : Ty → (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp))
    (T0 : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) (c : Ty → Ty → ℂ) (e : Ty → (Wq →L[ℂ] Wp))
    (hQadj : ∀ σ A B', B.hsInner (Qd σ A) B' = B.hsInner A (Qd σ B'))
    (hline : ∀ σ ρ, Qd σ (e ρ) = if σ = ρ then e ρ else 0) (π ρ : Ty) :
    inner ℂ (B.hsVec (e ρ)) (B.hsVec ((∑ π', ∑ ρ', c π' ρ' • (Qd ρ').comp (T0.comp (Qd π'))) (e π))) =
      c π ρ * inner ℂ (B.hsVec (e ρ)) (B.hsVec (T0 (e π))) := by
  have h := mat_gen Qd T0 c e hQadj hline π ρ
  unfold B.hsInner at h
  rw [← h]
  congr 2
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    ContinuousLinearMap.comp_apply]

theorem sandw_apply (A : Wp →L[ℂ] Wp) (B' : Wq →L[ℂ] Wq) (X : Wq →L[ℂ] Wp) : sandw A B' X = A.comp (X.comp B') := rfl

end gen

theorem ssnRep_of (hTP : TypeProj) (hTF : ThtFacts) (hTG : ThtGaugeConst) : SSnRep := by
  obtain ⟨K, hK, hTP⟩ := hTP
  refine ⟨K, hK, ?_⟩
  intro Cc hCc E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e hFr hGa hQQ l hl
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  have hk : 2 ≤ S.G.k := by
    have := (Finset.mem_Icc.1 hl)
    have h2 : (D.parOf S v).k = S.G.k := rfl
    omega
  obtain ⟨Qp, hQs, hQadj, hQeq, hQline⟩ := hTP Cc hCc E Wp Wq S T f χ ν' m₀ top A₀ hB v e hFr hGa hQQ
  obtain ⟨Bw, hBw⟩ := Formalism.FourierDecayAlt.P.Qx8.frame_exists (T v).base.z_mem (T v).base.T_pos
  obtain ⟨Bw', hBw'⟩ := Formalism.FourierDecayAlt.P.Qx8.frame_exists (T v).base.z'_mem (T v).base.T'_pos
  obtain ⟨hc, hca, hadj, heqv, hph⟩ := hTF (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (T v).base hPl Bw Bw' hBw hBw'
  obtain ⟨κ, hκ⟩ := hTG Cc E Wp Wq S T f χ ν' m₀ top A₀ v e ⟨hB, hFr, hGa, hQQ⟩ hk l hl Bw Bw' hBw hBw'
  classical
  set th := tht S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' Bw Bw' with hth
  set thA := thtA S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' Bw Bw' with hthA
  refine ⟨fun a a' ι => ∑ π, ∑ ρ, (if M.Up (D.parOf S v) l π ρ then κ π else 0) •
      (Qp ρ a).comp ((th a a' ι).comp (Qp π a)),
    fun a a' ι => ∑ π, ∑ ρ, (if M.Up (D.parOf S v) l π ρ then conj (κ π) else 0) •
      (Qp π a).comp ((thA a a' ι).comp (Qp ρ a)), ?_, ?_, ?_, ?_, ?_⟩
  ·
    refine ContDiff.sum fun π _ => ContDiff.sum fun ρ _ => ContDiff.const_smul _ ?_
    exact cd_comp ((hQs ρ).comp contDiff_fst) (cd_comp hc ((hQs π).comp contDiff_fst))
  · refine ContDiff.sum fun π _ => ContDiff.sum fun ρ _ => ContDiff.const_smul _ ?_
    exact cd_comp ((hQs π).comp contDiff_fst) (cd_comp hca ((hQs ρ).comp contDiff_fst))
  ·
    intro a a' ι A B'
    simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.comp_apply]
    rw [kap_hsInner_sum_left, kap_hsInner_sum_right]
    refine Finset.sum_congr rfl fun π _ => ?_
    rw [kap_hsInner_sum_left, kap_hsInner_sum_right]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [kap_hsInner_smul_left, kap_hsInner_smul_right, hQadj, hadj, hQadj]
    congr 1
    split_ifs <;> simp
  ·
    intro h hh h' hh' a a' ι X
    have hsum : ∀ (F : M.Ty (D.parOf S v) → M.Ty (D.parOf S v) →
        ((Wq (S.pl v) →L[ℂ] Wp (S.pl v)) →L[ℂ] (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))),
        ((T v).base.π h).comp (((∑ π, ∑ ρ, F π ρ) X).comp ((T v).base.π' h'⁻¹)) =
          ∑ π, ∑ ρ, ((T v).base.π h).comp ((F π ρ X).comp ((T v).base.π' h'⁻¹)) := by
      intro F
      have := map_sum (sandw ((T v).base.π h) ((T v).base.π' h'⁻¹)) (fun π => (∑ ρ, F π ρ) X) Finset.univ
      simp only [sandw_apply, ContinuousLinearMap.coe_sum', Finset.sum_apply] at this ⊢
      rw [this]
      refine Finset.sum_congr rfl fun π _ => ?_
      exact map_sum (sandw ((T v).base.π h) ((T v).base.π' h'⁻¹)) (fun ρ => F π ρ X) Finset.univ
    constructor
    · rw [hsum]
      simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.comp_apply]
      refine Finset.sum_congr rfl fun π _ => Finset.sum_congr rfl fun ρ _ => ?_
      rw [hQeq π h hh h' hh' a X, (heqv h hh h' hh' a a' ι _).1, hQeq ρ h hh h' hh' a _]
      split_ifs <;> ext y <;> simp
    · rw [hsum]
      simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.comp_apply]
      refine Finset.sum_congr rfl fun π _ => Finset.sum_congr rfl fun ρ _ => ?_
      rw [hQeq ρ h hh h' hh' a X, (heqv h hh h' hh' a a' ι _).2, hQeq π h hh h' hh' a _]
      split_ifs <;> ext y <;> simp
  ·
    intro q hq ρ π
    have hq1 : ∀ a, q.1 a ≠ 0 := hq.1
    have hζ : (D.parOf S v).TT < Complex.normSq q.2 := hq.2
    have hline := hQline q hq
    refine (mat_gen' (fun σ => Qp σ (SSn.phD q.1 • SSn.nu0 S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec q.2))
      (th (SSn.phD q.1 • SSn.nu0 S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec q.2)
        (conj (SSn.phD q.1) • SSn.nu0' S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec q.2)
        (SSn.io0 S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec q.2))
      (fun π' ρ' => if M.Up (D.parOf S v) l π' ρ' then κ π' else 0) (fun σ => e σ q.2)
      (fun σ => hQadj σ _) hline π ρ).trans ?_
    rw [hph (SSn.phD q.1), ContinuousLinearMap.smul_apply, inner_hs_smul]
    unfold SSn.ssnV
    split_ifs with hup
    · have h1 := hκ q.2 hζ π ρ hup
      rw [← conj_phD_sq hq1]
      linear_combination (conj (SSn.phD q.1)) ^ 2 * h1
    · simp

theorem second_shift_representation_assembly : SSnRepOfCut := fun hPE hGL hTF hDU hTG =>
  ssnRep_of (typeProj_of hPE hGL hDU weighted_norm_facts_hold) hTF hTG

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep
end
