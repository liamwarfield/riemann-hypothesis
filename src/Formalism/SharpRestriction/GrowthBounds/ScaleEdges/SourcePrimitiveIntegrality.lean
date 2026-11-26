module

public import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.WeylDimShift
public import Formalism.LocalToGlobal.GroupLattices.FockModels.FlatModels.LetterWtAnti

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.ScaleEdges.RestCloudXOfY
section -- merged from Formalism.SharpRestriction.GrowthBounds.ScaleEdges.OrdMaxRest
section -- merged from Formalism.SharpRestriction.GrowthBounds.ScaleEdges.RestCloudOfX
section -- merged from Formalism.SharpRestriction.GrowthBounds.ScaleEdges.RemainingWeightVectorCount
noncomputable section

namespace Formalism.MainNotions.Pf14

open Formalism.MainNotions.G Formalism.CountingSumsFrames

theorem dimV_eq (D : Formalism.BasicNotions.D7) (h35 : tableLineDegreeFive.FewBadOrbits D) (Kf : Type) [Field Kf] {n' m : ℕ}
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (hdom : IsDominant lam0) :
    ((dimV Kf lam0 : ℕ) : ℚ) = ∏ s : Fin n', weylDim (m + 1) (lam0 s) := by
  rw [h35 Kf n' m lam0 hdom]
  refine Finset.prod_congr rfl fun s _ => ?_
  have e1 : (∏ i : Fin (m + 1), ∏ j : Fin (m + 1),
      if i < j then (((lamAt lam0 s i : ℤ) : ℚ) - ((lamAt lam0 s j : ℤ) : ℚ) + ((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)) /
        (((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)) else 1) = weylDim (m + 1) (lamAt lam0 s) := by
    unfold weylDim
    refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
    push_cast
    rfl
  rw [e1]
  unfold lamAt
  split_ifs
  · rfl
  · exact weylDim_dual (m + 1) (lam0 s)

def remainingWeightVectorCount {n' m : ℕ} (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (m + 1) → ℤ) : ℚ :=
  (∏ t ∈ TT, weylDim m (fun i : Fin m => lam0 t i.succ)) * ∏ s ∈ TTᶜ, weylDim (m + 1) (lam0 s)

theorem top_count {n' m : ℕ} (hm : 2 ≤ m) {TT : Finset (Fin n')} {aT bT : Fin n' → ℤ} {cpp c0 : ℕ} {a : ℝ} (ha : 0 < a)
    {lam0 : Fin n' → Fin (m + 1) → ℤ} (hW : tableLineDegreeFive.WeightHyp TT aT bT cpp c0 a lam0) (t : Fin n') (ht : t ∈ TT) :
    (1 - ((m + 1 : ℕ) : ℝ) * c0 / a) * (weylDim (m + 1) (lam0 t) : ℝ) ≤
      ((Nat.choose (flatDeg lam0 t + (m + 1) - 1) (m + 1 - 1) : ℕ) : ℝ) *
        (weylDim m (fun i : Fin m => lam0 t i.succ) : ℝ) := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hfd := flatDeg_bounds (by omega) ha.le hW t ht
  obtain ⟨hb, hdom, hw⟩ := hW
  obtain ⟨e0, elast, hc⟩ := (hb t).1 ht
  obtain ⟨_, _, hb0, hbc⟩ := hw t ht
  have hanti := hdom t
  set mu : Fin (m' + 1) → ℤ := fun i => lam0 t i.succ + bT t with hmu
  have hmuA : Antitone mu := by
    intro i j hij
    have := hanti (Fin.succ_le_succ_iff.2 hij)
    simp only [hmu]
    omega
  have hmuB : ∀ i, 0 ≤ mu i ∧ mu i ≤ c0 := by
    intro i
    constructor
    · have := hanti (Fin.le_last i.succ)
      simp only [hmu]
      omega
    · simp only [hmu]
      by_cases hi : i.succ.val < m' + 1
      · have := hc i.succ (by simp) hi
        have h2 := abs_le.1 this
        omega
      · have : i.succ = Fin.last (m' + 1) := by
          apply Fin.ext
          have := i.succ.isLt
          simp only [Fin.val_last]
          omega
        rw [this, elast]
        omega
  have h01 : lam0 t 1 ≤ lam0 t 0 := hanti (Fin.zero_le _)
  have hs0 : (Fin.succ (0 : Fin (m' + 1))) = (1 : Fin (m' + 1 + 1)) := rfl
  have hcons : (fun i => lam0 t i + bT t) = (Fin.cons ((flatDeg lam0 t : ℤ) + mu 0) mu : Fin (m' + 2) → ℤ) := by
    funext i
    refine Fin.cases ?_ (fun i' => ?_) i
    · simp only [Fin.cons_zero, hmu, hs0]
      unfold flatDeg
      rw [Int.toNat_of_nonneg (by omega)]
      ring
    · simp only [Fin.cons_succ, hmu]
  have h1 := weylDim_cons_le_choose_mul m' mu (flatDeg lam0 t) c0 a ha hmuA hmuB hfd.1
  rw [← hcons, weylDim_shift, weylDim_shift] at h1
  have e1 : ((m' + 1 + 1 : ℕ) : ℝ) = (m' : ℝ) + 2 := by push_cast; ring
  have e2 : flatDeg lam0 t + (m' + 1 + 1) - 1 = flatDeg lam0 t + m' + 1 := by omega
  have e3 : m' + 1 + 1 - 1 = m' + 1 := by omega
  rw [e1, e2, e3]
  exact h1

theorem count_of_exact (D : Formalism.BasicNotions.D7) (h35 : tableLineDegreeFive.FewBadOrbits D) {C : ℝ} (hC : 2 ≤ C) {p n' m r : ℕ}
    {TT : Finset (Fin n')} {L₁ L₂ : ℕ} {de h x : ℝ} {lam0 : Fin n' → Fin (m + 1) → ℤ} {aT bT : Fin n' → ℤ} {a Y : ℝ}
    {cpp c0 Dp cStar : ℕ} (H : Hyps C p n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar)
    (Kf : Type) [Field Kf] (n2 : ℕ) (hn2 : (n2 : ℚ) = remainingWeightVectorCount TT lam0) :
    (1 - ((m + 1 : ℕ) : ℝ) * c0 / a) ^ TT.card * (dimV Kf lam0 : ℝ) ≤
      (∏ t ∈ TT, ((Nat.choose (flatDeg lam0 t + (m + 1) - 1) (m + 1 - 1) : ℕ) : ℝ)) * n2 := by
  have hB := hyps_basic (C := C) (by linarith) H
  have hk := rank_mul_conductor_div_le_one hC H
  have hW : tableLineDegreeFive.WeightHyp TT aT bT cpp c0 a lam0 := H.2.2.2.2.1
  have hdom : IsDominant lam0 := hW.2.1
  have ha : 0 < a := by linarith [hB.two_le_a]
  have hd : (dimV Kf lam0 : ℝ) = (∏ t ∈ TT, (weylDim (m + 1) (lam0 t) : ℝ)) * ∏ s ∈ TTᶜ, (weylDim (m + 1) (lam0 s) : ℝ) := by
    have h1 := dimV_eq D h35 Kf lam0 hdom
    have h2 : ((dimV Kf lam0 : ℕ) : ℝ) = (((dimV Kf lam0 : ℕ) : ℚ) : ℝ) := by push_cast; rfl
    rw [h2, h1, ← Finset.prod_mul_prod_compl TT]
    push_cast
    rfl
  have hn : (n2 : ℝ) = (∏ t ∈ TT, (weylDim m (fun i : Fin m => lam0 t i.succ) : ℝ)) *
      ∏ s ∈ TTᶜ, (weylDim (m + 1) (lam0 s) : ℝ) := by
    have h2 : (n2 : ℝ) = ((n2 : ℚ) : ℝ) := by push_cast; rfl
    rw [h2, hn2]
    unfold remainingWeightVectorCount
    push_cast
    rfl
  have hS : 0 ≤ ∏ s ∈ TTᶜ, (weylDim (m + 1) (lam0 s) : ℝ) := by
    refine Finset.prod_nonneg fun s _ => ?_
    exact_mod_cast (gram_weylDim_pos (m + 1) (lam0 s) (hdom s)).le
  have hT : ∏ t ∈ TT, ((1 - ((m + 1 : ℕ) : ℝ) * c0 / a) * (weylDim (m + 1) (lam0 t) : ℝ)) ≤
      ∏ t ∈ TT, (((Nat.choose (flatDeg lam0 t + (m + 1) - 1) (m + 1 - 1) : ℕ) : ℝ) *
        (weylDim m (fun i : Fin m => lam0 t i.succ) : ℝ)) := by
    refine Finset.prod_le_prod₀ (fun t _ => ?_) fun t ht => top_count (by have := hB.m_ge; omega) ha hW t ht
    refine mul_nonneg (by linarith) ?_
    exact_mod_cast (gram_weylDim_pos (m + 1) (lam0 t) (hdom t)).le
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const] at hT
  rw [hd, hn]
  have := mul_le_mul_of_nonneg_right hT hS
  calc _ = (1 - ((m + 1 : ℕ) : ℝ) * c0 / a) ^ TT.card * (∏ t ∈ TT, (weylDim (m + 1) (lam0 t) : ℝ)) *
        ∏ s ∈ TTᶜ, (weylDim (m + 1) (lam0 s) : ℝ) := by ring
    _ ≤ _ := this
    _ = _ := by ring

end Formalism.MainNotions.Pf14
end
end

noncomputable section

namespace Formalism.MainNotions.Pf14

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning MvPolynomial

def CloudAtX (p n' : ℕ) [Fact p.Prime] [NeZero n'] {W Qq O Kf : Type} [CommRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf] [Algebra (WF p n') O]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (w : O) (φ : WF p n' ≃+* W) {m r : ℕ}
    (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (m + 1) → ℤ) (cStar : ℕ) (bS bT bD : ℝ)
    (e : Edge W Qq (m + 1)) (h : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) {nb : ℕ}
    (FsB : Fin nb → ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O)) : Prop :=
  ∃ Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O) ≃ₗ[O]
      ↥(Vsp Kf (flW (m := m) (dT TT lam0))),
    IsFlatIdent ι σ w φ r (dT TT lam0) (flW (dT TT lam0)) (vecE n') h Θ ∧
    ∃ (n2 oS tT D1 : ℕ) (sh : Fin n2 → Vsp Kf (restW TT lam0)),
      (oS : ℝ) ≤ bS ∧ (tT : ℝ) ≤ bT ∧ (D1 : ℝ) ≤ bD ∧
      (∀ i, sh i ∈ Re p ι σ w r (restW TT lam0) e ∧
        sh i ∈ scale (algebraMap O Kf w ^ (-(oS : ℤ))) (HL (O := O) ι σ (restW TT lam0) e.src)) ∧
      ((n2 : ℕ) : ℚ) = remainingWeightVectorCount TT lam0 ∧
      ∀ S : Fin nb × Fin n2 → Vsp Kf lam0,
        (∀ b i, ((S (b, i) : Vsp Kf lam0) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) =
          ((Θ (FsB b) : Vsp Kf (flW (m := m) (dT TT lam0))) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) *
            ((sh i : Vsp Kf (restW TT lam0)) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf)) →
        ∀ c : Fin nb × Fin n2 → O, (∃ x, IsUnit (c x)) →
          ∃ G : Module.Dual Kf (Vsp Kf lam0),
            G ∈ scale (algebraMap O Kf w ^ (-(tT : ℤ))) (dualLat O Kf (HL (O := O) ι σ lam0 e.tgt)) ∧
            G ∈ Re' p ι σ w r lam0 e ∧
            (∀ e' : Edge W Qq (m + 1), IsEdge p n' r e' → e'.tgt = e.tgt → e' ≠ e →
              G ∈ scale (algebraMap O Kf w ^ (cStar : ℤ)) (Re' p ι σ w r lam0 e')) ∧
            ValLe (p : O) D1 (be p r lam0 (∑ x, c x • S x) G)

def CloudStepX (C Ct0 CD1 CLa : ℝ) : Prop :=
  ∀ (p : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O)
    (n' m r : ℕ) [Fact p.Prime] [NeZero n'] (TT : Finset (Fin n')) (L₁ L₂ : ℕ) (de h x : ℝ)
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (aT bT : Fin n' → ℤ) (a Y : ℝ) (cpp c0 Dp cStar : ℕ),
    UnramifiedQuadraticSetting p n' W Qq O Kf ι σ j w →
    Hyps C p n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar →
    ∀ φ : WF p n' ≃+* W, IsWittIdent σ φ →
    ∀ (K : ℕ) [NeZero r] [NeZero K] (hk : m + 1 = r + K) (hrk : r ≤ m + 1),
    ∀ F : Frames n' r, FramesOK TT L₁ L₂ (orbitWindowCount r de h x) (goodG' r de h x) F →
    ∀ E' : Fin n' → ℕ,
      (∀ t ∈ F.TT, E' t ≤ E0 p r (r + K) (orbitWindowCount r de h x) (goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar) ∧
        E' t ≤ flatDeg lam0 t) →
    ∀ (nb : ℕ) (B : Fin nb → RRing O n' (r + K)),
      (∀ i, B i ∈ Gen O p K F
        (symbolSpaces CLa p n' O r K F (flatDeg lam0) L₁ (min (orbitWindowCount r de h x) (2 * TT.card))
          (mStar p F (r + K) (orbitWindowCount r de h x) (p ^ goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar)) a Y)
        (G2d F (flatDeg lam0) E')) →
      LinearIndependent O B → (∃ T : Submodule O (RRing O n' (r + K)), IsCompl (Submodule.span O (Set.range B)) T) →
    ∀ e : Edge W Qq (m + 1), IsEdge p n' r e → e.tgt = colSpan W (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) →
    ∀ (hm : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n')),
      IsUnit hm.det → IsGLW g → IsEdgeBasis p r e (hm * ((matQ φ g)⁻¹).transpose) →
    letI : Algebra (WF p n') O := algOfIdent j φ
    ∀ FsB : Fin nb → ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O),
      (∀ b, subst p n' O w n' r g (FsB b : MvPolynomial (TV n' (m + 1)) (KK O)) =
        symB p n' O w hk hrk F g (cPrime n' r TT.card c0 cpp cStar) (p ^ goodG' r de h x) (B b)) →
      CloudAtX p n' ι σ w φ (r := r) TT lam0 cStar (om r TT.card n' c0 cpp)
        (t0 C Ct0 p TT.card (orbitWindowCount r de h x) L₁ (goodG' r de h x) (m + 1) a + (TT.card : ℝ) * c0 +
          om r TT.card n' c0 cpp)
        (CD1 * (TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a) e hm FsB

def RestCloudX (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 : ℝ) : Prop :=
  tableLineDegreeFive.admitted D CLa Ck Crk Cdeg → SourceCleaning.aux₃ D CLa' CD Csz → PlaneGramData.aux₃ D CH CE C6 C18 →
    ∃ Ct0 CD1 C₁ : ℝ, 0 < Ct0 ∧ 0 < CD1 ∧ 0 < C₁ ∧ ∀ C : ℝ, C₁ ≤ C → CloudStepX C Ct0 CD1 CLa

theorem restCloud_of_X (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 : ℝ)
    (hX : RestCloudX D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18) :
    RestCloud D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 := by
  intro hA h14a h14b
  obtain ⟨Ct0, CD1, C₁, h0, h1, h2, hS⟩ := hX hA h14a h14b
  have h35 : tableLineDegreeFive.FewBadOrbits D := hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨Ct0, CD1, max C₁ 2, h0, h1, lt_of_lt_of_le h2 (le_max_left _ _), ?_⟩
  intro C hC p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r _ _ TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H φ hφ K
    _ _ hk hrk F hF E' hE' nb B hB hli hc e he htgt hm g hhm hg hbasis FsB hFsB
  obtain ⟨Θ, hΘ, n2, oS, tT, D1, sh, a1, a2, a3, a4, a5, a6⟩ :=
    hS C (le_trans (le_max_left _ _) hC) p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H
      φ hφ K hk hrk F hF E' hE' nb B hB hli hc e he htgt hm g hhm hg hbasis FsB hFsB
  exact ⟨Θ, hΘ, n2, oS, tT, D1, sh, a1, a2, a3, a4,
    count_of_exact D h35 (le_trans (le_max_right _ _) hC) H Kf n2 a5, a6⟩

end Formalism.MainNotions.Pf14
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.ScaleEdges.EdgeLatticeAdaptedBasis
open MvPolynomial

noncomputable section

namespace Formalism.MainNotions.Pf14

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.G.LatticeSystems Formalism.L2.G.Model

def ordMax {n' m : ℕ} (r : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ) : ℤ :=
  ∑ s : Fin n', ∑ a : Fin (m + 1) with a.val < r, (lamAt lam0 s a - lamAt lam0 s (Fin.last m))

theorem pos_basisO (O Kf : Type) [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf]
    (hinj : Function.Injective (algebraMap O Kf)) (m r : ℕ) (lam : Fin (m + 1) → ℤ) (hlam : Antitone lam)
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (hg : IsUnit g.det) :
    ∃ (X : ↥(ssIdx (m + 1) (m + 1) (nuOf lam)) → MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf)
      (π : ↥(ssIdx (m + 1) (m + 1) (nuOf lam)) → ℤ),
      LinearIndependent Kf X ∧ Submodule.span Kf (Set.range X) = dualWeyl Kf (m + 1) (m + 1) (nuOf lam) ∧
      (∀ i, π i ≤ ∑ a : Fin (m + 1) with a.val < r, lam a) ∧
      (∀ i, ((Finset.univ.filter fun a : Fin (m + 1) => a.val < r).card : ℤ) * lam (Fin.last m) ≤ π i) ∧
      ∀ c : Kf, c ≠ 0 → Submodule.span O (Set.range fun i => c ^ π i • X i) =
        nablaLTw O Kf m lam (g * lb_D (m + 1) r c) := by
  classical
  obtain ⟨b, hb, hbd⟩ := Formalism.MainNotions.G.LatticeSystems.lb_basis O (m + 1) (m + 1) (nuOf lam)
  obtain ⟨hKi, hKs⟩ := nablaLKBasis O Kf hinj (m + 1) (m + 1) (nuOf lam) b _ hb g hg
  have hdet0 : g.det ≠ 0 := hg.ne_zero
  set ll := lam (Fin.last m) with hll
  set S := Finset.univ.filter fun a : Fin (m + 1) => a.val < r with hS
  set f := fun i : ↥(ssIdx (m + 1) (m + 1) (nuOf lam)) => rowAct Kf g⁻¹ (map (algebraMap O Kf) (b i)) with hf
  have hdg0 : g.det ^ (-ll) ≠ 0 := zpow_ne_zero _ hdet0
  refine ⟨fun i => g.det ^ (-ll) • f i,
    fun i => ((∑ a ∈ S, rowWt i.1 a : ℕ) : ℤ) + (S.card : ℤ) * ll, ?_, ?_, ?_, ?_, ?_⟩
  · exact hKi.units_smul (fun _ => Units.mk0 (g.det ^ (-ll)) hdg0)
  · rw [← Set.smul_set_range, Submodule.span_smul_eq_of_isUnit _ _ (Ne.isUnit hdg0)]
    exact hKs
  · intro i
    have h1 := hbd i r
    have h2 : ((∑ a ∈ S, rowWt i.1 a : ℕ) : ℤ) ≤ ∑ a ∈ S, (lam a - ll) := by
      calc ((∑ a ∈ S, rowWt i.1 a : ℕ) : ℤ) ≤ ((∑ a ∈ S, nuOf lam a : ℕ) : ℤ) := by exact_mod_cast h1
        _ = ∑ a ∈ S, (lam a - ll) := by
          push_cast
          refine Finset.sum_congr rfl fun a _ => ?_
          have : ll ≤ lam a := hlam (Fin.le_last a)
          simp only [nuOf]
          omega
    have h3 : ∑ a ∈ S, (lam a - ll) = ∑ a ∈ S, lam a - (S.card : ℤ) * ll := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    linarith
  · intro i
    have : (0 : ℤ) ≤ ((∑ a ∈ S, rowWt i.1 a : ℕ) : ℤ) := Int.natCast_nonneg _
    linarith
  · intro c hc
    have ht : ∀ a : Fin (m + 1), (if a.val < r then c⁻¹ else 1) ≠ 0 := by
      intro a; split_ifs <;> simp [hc]
    obtain ⟨-, hD⟩ := nablaLDiag O Kf hinj (m + 1) (m + 1) (nuOf lam) b _ hb g _ hg ht
    have hgD : g * lb_D (m + 1) r c =
        g * Matrix.diagonal (fun a : Fin (m + 1) => if a.val < r then c⁻¹ else 1) := rfl
    rw [nablaLTw, hgD]
    change _ = Submodule.map _ (nablaL O Kf (m + 1) (m + 1) (nuOf lam) _)
    rw [← hD, Submodule.map_span, ← Set.range_comp]
    congr 2
    funext i
    have hprod : (∏ a, (if a.val < r then c⁻¹ else 1) ^ rowWt i.1 a)⁻¹ = c ^ (∑ a ∈ S, rowWt i.1 a) := by
      simp_rw [ite_pow, one_pow]
      rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_pow_eq_pow_sum, inv_pow, inv_inv]
    have hdet : (g * Matrix.diagonal fun a : Fin (m + 1) => if a.val < r then c⁻¹ else 1).det =
        g.det * c⁻¹ ^ S.card := by
      rw [Matrix.det_mul, Matrix.det_diagonal, Finset.prod_ite, Finset.prod_const_one, mul_one,
        Finset.prod_const]
    have hpw : (c⁻¹ ^ S.card) ^ (-ll) = c ^ ((S.card : ℤ) * ll) := by
      rw [inv_pow, inv_zpow', ← zpow_natCast, ← zpow_mul]
      ring_nf
    simp only [Function.comp_apply]
    rw [hdet, ← hll, hprod]
    simp only [LinearMap.restrictScalars_apply, LinearMap.lsmul_apply, smul_smul]
    congr 1
    rw [mul_zpow, hpw, zpow_add₀ hc, zpow_natCast]
    ring

theorem ten_basisO (O Kf : Type) [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf] [IsFractionRing O Kf]
    {n' m : ℕ} (r : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ) (hd : IsDominant lam0)
    (gs : Fin n' → Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (hgs : ∀ s, IsUnit (gs s).det) :
    ∃ (I : Type) (_ : Finite I) (x : Module.Basis I Kf (Vsp Kf lam0)) (π : I → ℤ),
      (∀ i, π i ≤ Ar r lam0) ∧ (∀ i, Ar r lam0 - π i ≤ ordMax r lam0) ∧
      ∀ c : Kf, c ≠ 0 → Submodule.span O (Set.range fun i => c ^ π i • x i) =
        toV lam0 (Hten O lam0 fun s => colSpan O (gs s * lb_D (m + 1) r c)) := by
  classical
  have hinj : Function.Injective (algebraMap O Kf) := IsFractionRing.injective O Kf
  have hinj' : Function.Injective fun a : O => a • (1 : Kf) := by
    have : (fun a : O => a • (1 : Kf)) = algebraMap O Kf :=
      funext fun a => (Algebra.algebraMap_eq_smul_one a).symm
    rw [this]; exact hinj
  have hA : ∀ s, Antitone (lamAt lam0 s) := kp_lamAt_antitone lam0 hd
  have hI := Formalism.MainNotions.G.LatticeSystems.la_indep (O := O) (Kf := Kf) hinj
  have hpos := fun s => pos_basisO O Kf hinj m r (lamAt lam0 s) (hA s) (gs s) (hgs s)
  choose X π hXi hXs hup hlo hspan using hpos
  have : ∀ s, Finite ↥(ssIdx (m + 1) (m + 1) (nuOf (lamAt lam0 s))) :=
    fun s => (sSIdxFinite _ _ _).to_subtype
  have : ∀ s, Fintype ↥(ssIdx (m + 1) (m + 1) (nuOf (lamAt lam0 s))) := fun s => Fintype.ofFinite _
  have : IsFractionRing Kf Kf := jr_KK Kf
  set P : (∀ s : Fin n', ↥(ssIdx (m + 1) (m + 1) (nuOf (lamAt lam0 s)))) →
      MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf :=
    fun i => ∏ s, blockEmb Kf s (X s (i s)) with hP
  obtain ⟨hPi, hPs⟩ := tensorBasis Kf Kf (Fin n') (m + 1) (m + 1) _ _ X hXi hXs
  have hV : Vsp Kf lam0 = Submodule.span Kf (Set.range P) := by
    rw [hPs]
    simp only [Vsp, hA, ↓reduceIte]
  have hmem : ∀ i, P i ∈ Vsp Kf lam0 := fun i => hV ▸ Submodule.subset_span ⟨i, rfl⟩
  set y : (∀ s : Fin n', ↥(ssIdx (m + 1) (m + 1) (nuOf (lamAt lam0 s)))) → Vsp Kf lam0 :=
    fun i => ⟨P i, hmem i⟩ with hy
  have hyi : LinearIndependent Kf y := LinearIndependent.of_comp (Vsp Kf lam0).subtype hPi
  have hys : Submodule.span Kf (Set.range y) = ⊤ := by
    rw [eq_top_iff, ← comap_span_coe (O := Kf) (Kf := Kf) (Vsp Kf lam0) y]
    intro v _
    rw [Submodule.mem_comap]
    have hv : (v : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) ∈ Submodule.span Kf (Set.range P) :=
      hV ▸ v.2
    exact hv
  refine ⟨_, inferInstance, Module.Basis.mk hyi hys.symm.le, fun i => ∑ s, π s (i s), ?_, ?_, ?_⟩
  · intro i
    unfold Ar
    exact Finset.sum_le_sum fun s _ => hup s (i s)
  · intro i
    unfold Ar ordMax
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun s _ => ?_
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    linarith [hlo s (i s)]
  · intro c hc
    have hdet : ∀ s, IsUnit (gs s * lb_D (m + 1) r c).det := fun s => by
      rw [Matrix.det_mul]; exact (hgs s).mul (lb_D_det _ _ _ hc)
    have hli : ∀ s, LinearIndependent O fun j => c ^ π s j • X s j := fun s =>
      ((hXi s).units_smul fun j => Units.mk0 (c ^ π s j) (zpow_ne_zero _ hc)).restrict_scalars hinj'
    obtain ⟨-, hT⟩ := tensorBasis O Kf (Fin n') (m + 1) (m + 1) _
      (fun s => Submodule.span O (Set.range fun j => c ^ π s j • X s j)) (fun s j => c ^ π s j • X s j)
      hli (fun s => rfl)
    have hH : Hten O lam0 (fun s => colSpan O (gs s * lb_D (m + 1) r c)) =
        Submodule.span O (Set.range fun i => c ^ (∑ s, π s (i s)) • P i) := by
      have e1 : (fun s => H0 O m (lamAt lam0 s) (colSpan O (gs s * lb_D (m + 1) r c))) =
          fun s => Submodule.span O (Set.range fun j => c ^ π s j • X s j) := by
        funext s
        rw [H0_eq_twisted_nabla hI m _ (hA s) _ (hdet s), hspan s c hc]
      rw [Hten, e1, ← hT]
      congr 2
      funext i
      simp only [map_smul]
      rw [Finset.prod_smul, lb_zpow_sum c hc]
    rw [toV, hH, ← comap_span_coe (O := O) (Kf := Kf) (Vsp Kf lam0)
      (fun i => c ^ (∑ s, π s (i s)) • (Module.Basis.mk hyi hys.symm.le) i)]
    congr 3
    funext i
    rw [Submodule.coe_smul, Module.Basis.mk_apply]

section
variable {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
  [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}

theorem edge_lattice_adapted_basis (h : HidaSetting p n' W Qq O Kf ι σ j w) (m r : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ)
    (hd : IsDominant lam0) (e : Edge W Qq (m + 1)) (he : IsEdge p n' r e) :
    ∃ (I : Type) (_ : Finite I) (x : Module.Basis I Kf ↥(Vsp Kf lam0)) (π : I → ℤ),
      Submodule.span O (Set.range x) = HL ι σ lam0 e.src ∧
      Submodule.span O (Set.range fun i => ((p : Kf) ^ π i) • x i) = HL ι σ lam0 e.tgt ∧
      Submodule.span O (Set.range fun i => (algebraMap O Kf w ^ π i) • x i) = HLe p ι σ w lam0 e ∧
      (∀ i, 0 ≤ order r lam0 (π i)) ∧ (∀ i, order r lam0 (π i) ≤ ordMax r lam0) ∧
      Submodule.span O (Set.range fun i => (algebraMap O Kf w ^ (-order r lam0 (π i))) • x i) =
        Re p ι σ w r lam0 e ∧
      Submodule.span O (Set.range fun i =>
          (algebraMap O Kf w ^ (-order r lam0 (π i)) * (p : Kf) ^ (-π i)) • x.coord i) =
        Re' p ι σ w r lam0 e := by
  classical
  have hw := w_ne h
  have hp := p_eq h
  have hp0 : (p : Kf) ≠ 0 := by rw [hp]; exact pow_ne_zero 2 hw
  have : IsFractionRing O Kf := h.frac_O
  obtain ⟨gs, hgs, hsrc, hLe, htgt⟩ := edgeLat h m r e he
  obtain ⟨I, hI, x, π, hup, hord, hsp⟩ :=
    ten_basisO O Kf r lam0 hd (fun s : Fin n' => gs s.val) (fun s => hgs s.val)
  have h3 : Submodule.span O (Set.range fun i => (algebraMap O Kf w ^ π i) • x i) = HLe p ι σ w lam0 e := by
    rw [HLe, show (fun s : Fin n' => LeAt p ι σ w s.val e) =
      fun s => colSpan O (gs s.val * lb_D (m + 1) r (algebraMap O Kf w)) from funext fun s => hLe s.val]
    exact hsp _ hw
  refine ⟨I, hI, x, π, ?_, ?_, h3, ?_, ?_, ?_, ?_⟩
  · rw [HL, show (fun s : Fin n' => extO O ι σ s.val e.src) = fun s => colSpan O (gs s.val) from
      funext fun s => hsrc s.val]
    simpa [lb_D_one] using hsp 1 one_ne_zero
  · rw [HL, show (fun s : Fin n' => extO O ι σ s.val e.tgt) =
      fun s => colSpan O (gs s.val * lb_D (m + 1) r (p : Kf)) from
      funext fun s => by rw [htgt, Matrix.mul_assoc, lb_D_sq, hp]]
    exact hsp _ hp0
  · intro i
    unfold order
    linarith [hup i]
  · exact hord
  · rw [Re, ← h3, scale_span]
    congr 2
    funext i
    rw [smul_smul, order, ← zpow_add₀ hw]
    congr 2
    ring
  · rw [Re', ← h3, dualLat_span x _ (fun i => zpow_ne_zero _ hw), scale_span]
    congr 2
    funext i
    rw [smul_smul]
    congr 1
    rw [hp, order, ← zpow_neg, ← zpow_natCast (algebraMap O Kf w) 2, ← zpow_mul, ← zpow_add₀ hw,
      ← zpow_add₀ hw]
    congr 1
    push_cast
    ring

theorem Re_le_scale_HL (h : HidaSetting p n' W Qq O Kf ι σ j w) (m r : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ)
    (hd : IsDominant lam0) (e : Edge W Qq (m + 1)) (he : IsEdge p n' r e) (M : ℕ) (hM : ordMax r lam0 ≤ M) :
    Re p ι σ w r lam0 e ≤ scale (algebraMap O Kf w ^ (-(M : ℤ))) (HL (O := O) ι σ lam0 e.src) := by
  obtain ⟨I, hI, x, π, hsrc, -, -, -, hmax, hRe, -⟩ := edge_lattice_adapted_basis h m r lam0 hd e he
  have hw := w_ne h
  rw [← hRe, ← hsrc, scale_span, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  have hk : 0 ≤ (M : ℤ) - order r lam0 (π i) := by linarith [hmax i]
  obtain ⟨k, hk'⟩ := Int.eq_ofNat_of_zero_le hk
  have he' : (algebraMap O Kf w ^ (-order r lam0 (π i))) • x i =
      (w ^ k) • ((algebraMap O Kf w ^ (-(M : ℤ))) • x i) := by
    rw [← algebraMap_smul Kf (w ^ k), smul_smul, map_pow, ← zpow_natCast, ← zpow_add₀ hw]
    congr 2
    omega
  beta_reduce
  rw [SetLike.mem_coe, he']
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end

end Formalism.MainNotions.Pf14
end
end

noncomputable section

namespace Formalism.MainNotions.Pf14

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning MvPolynomial

theorem ord_pos {n' m : ℕ} (r : ℕ) (lam : Fin n' → Fin (m + 1) → ℤ) (hd : IsDominant lam) (s : Fin n') :
    ∑ a : Fin (m + 1) with a.val < r, (lamAt lam s a - lamAt lam s (Fin.last m)) ≤
      (r : ℤ) * (lam s 0 - lam s (Fin.last m)) := by
  have hsp : 0 ≤ lam s 0 - lam s (Fin.last m) := sub_nonneg.2 (hd s (Fin.zero_le _))
  have hterm : ∀ a : Fin (m + 1), lamAt lam s a - lamAt lam s (Fin.last m) ≤ lam s 0 - lam s (Fin.last m) := by
    intro a
    unfold lamAt
    split_ifs
    · have := hd s (Fin.zero_le a)
      omega
    · have h1 := hd s (Fin.le_last a.rev)
      simp only [Fin.rev_last]
      omega
  have hcard : ((Finset.univ.filter fun a : Fin (m + 1) => a.val < r).card : ℤ) ≤ r := by
    have : (Finset.univ.filter fun a : Fin (m + 1) => a.val < r).card ≤ r := by
      calc (Finset.univ.filter fun a : Fin (m + 1) => a.val < r).card
          ≤ (Finset.range r).card := by
            apply Finset.card_le_card_of_injOn (fun a => a.val)
            · intro a ha
              simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha
              simpa using ha
            · intro a _ b _ hab
              exact Fin.ext hab
        _ = r := Finset.card_range r
    exact_mod_cast this
  calc ∑ a : Fin (m + 1) with a.val < r, (lamAt lam s a - lamAt lam s (Fin.last m))
      ≤ ∑ _a : Fin (m + 1) with _a.val < r, (lam s 0 - lam s (Fin.last m)) := Finset.sum_le_sum fun a _ => hterm a
    _ = ((Finset.univ.filter fun a : Fin (m + 1) => a.val < r).card : ℤ) * (lam s 0 - lam s (Fin.last m)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard hsp

theorem ordMax_rest {n' m : ℕ} (hm : 2 ≤ m) {TT : Finset (Fin n')} {aT bT : Fin n' → ℤ} {cpp c0 : ℕ} {a : ℝ}
    {lam0 : Fin n' → Fin (m + 1) → ℤ} (hW : tableLineDegreeFive.WeightHyp TT aT bT cpp c0 a lam0) (r : ℕ) :
    ordMax r (restW TT lam0) ≤ ((r * TT.card * c0 + 2 * r * n' * cpp : ℕ) : ℤ) := by
  obtain ⟨hb, hdom, hw⟩ := hW
  have hdr := restW_dom (by omega) TT lam0 hdom
  have hl0 : Fin.last m ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  have hv1 : ((1 : Fin (m + 1)) : ℕ) = 1 := by
    rw [Fin.val_one']
    exact Nat.mod_eq_of_lt (by omega)
  have key : ∀ s, restW TT lam0 s 0 - restW TT lam0 s (Fin.last m) ≤
      (if s ∈ TT then (c0 : ℤ) else 0) + 2 * cpp := by
    intro s
    have e1 : restW TT lam0 s (Fin.last m) = lam0 s (Fin.last m) := by
      unfold restW flW
      simp [Pi.single_apply, hl0]
    have e0 : restW TT lam0 s 0 = lam0 s 0 - (dT TT lam0 s : ℤ) := by
      unfold restW flW
      simp
    rw [e0, e1]
    by_cases hs : s ∈ TT
    · obtain ⟨_, elast, hc⟩ := (hb s).1 hs
      obtain ⟨_, _, hb0, hbc⟩ := hw s hs
      have h01 : lam0 s 1 ≤ lam0 s 0 := hdom s (Fin.zero_le _)
      have hc1 := abs_le.1 (hc 1 (by omega) (by omega))
      unfold dT flatDeg
      rw [if_pos hs, if_pos hs, Int.toNat_of_nonneg (by omega), elast]
      omega
    · have h1 := abs_le.1 ((hb s).2 hs 0)
      have h2 := abs_le.1 ((hb s).2 hs (Fin.last m))
      unfold dT
      rw [if_neg hs, if_neg hs]
      push_cast
      omega
  unfold ordMax
  have hr0 : (0 : ℤ) ≤ r := Int.natCast_nonneg _
  calc ∑ s : Fin n', ∑ a : Fin (m + 1) with a.val < r,
        (lamAt (restW TT lam0) s a - lamAt (restW TT lam0) s (Fin.last m))
      ≤ ∑ s : Fin n', (r : ℤ) * ((if s ∈ TT then (c0 : ℤ) else 0) + 2 * cpp) :=
        Finset.sum_le_sum fun s _ => le_trans (ord_pos r _ hdr s) (mul_le_mul_of_nonneg_left (key s) hr0)
    _ = ((r * TT.card * c0 + 2 * r * n' * cpp : ℕ) : ℤ) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        push_cast
        simp only [nsmul_eq_mul]
        ring

end Formalism.MainNotions.Pf14
end
end

noncomputable section

namespace Formalism.MainNotions.Pf14

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning MvPolynomial

def CloudAtY (p n' : ℕ) [Fact p.Prime] [NeZero n'] {W Qq O Kf : Type} [CommRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf] [Algebra (WF p n') O]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (w : O) (φ : WF p n' ≃+* W) {m r : ℕ}
    (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (m + 1) → ℤ) (cStar : ℕ) (bT bD : ℝ)
    (e : Edge W Qq (m + 1)) (h : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) {nb : ℕ}
    (FsB : Fin nb → ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O)) : Prop :=
  ∃ Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O) ≃ₗ[O]
      ↥(Vsp Kf (flW (m := m) (dT TT lam0))),
    IsFlatIdent ι σ w φ r (dT TT lam0) (flW (dT TT lam0)) (vecE n') h Θ ∧
    ∃ (n2 tT D1 : ℕ) (sh : Fin n2 → Vsp Kf (restW TT lam0)),
      (tT : ℝ) ≤ bT ∧ (D1 : ℝ) ≤ bD ∧
      (∀ i, sh i ∈ Re p ι σ w r (restW TT lam0) e) ∧
      ((n2 : ℕ) : ℚ) = remainingWeightVectorCount TT lam0 ∧
      ∀ S : Fin nb × Fin n2 → Vsp Kf lam0,
        (∀ b i, ((S (b, i) : Vsp Kf lam0) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) =
          ((Θ (FsB b) : Vsp Kf (flW (m := m) (dT TT lam0))) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) *
            ((sh i : Vsp Kf (restW TT lam0)) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf)) →
        ∀ c : Fin nb × Fin n2 → O, (∃ x, IsUnit (c x)) →
          ∃ G : Module.Dual Kf (Vsp Kf lam0),
            G ∈ scale (algebraMap O Kf w ^ (-(tT : ℤ))) (dualLat O Kf (HL (O := O) ι σ lam0 e.tgt)) ∧
            G ∈ Re' p ι σ w r lam0 e ∧
            (∀ e' : Edge W Qq (m + 1), IsEdge p n' r e' → e'.tgt = e.tgt → e' ≠ e →
              G ∈ scale (algebraMap O Kf w ^ (cStar : ℤ)) (Re' p ι σ w r lam0 e')) ∧
            ValLe (p : O) D1 (be p r lam0 (∑ x, c x • S x) G)

def CloudStepY (C Ct0 CD1 CLa : ℝ) : Prop :=
  ∀ (p : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O)
    (n' m r : ℕ) [Fact p.Prime] [NeZero n'] (TT : Finset (Fin n')) (L₁ L₂ : ℕ) (de h x : ℝ)
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (aT bT : Fin n' → ℤ) (a Y : ℝ) (cpp c0 Dp cStar : ℕ),
    UnramifiedQuadraticSetting p n' W Qq O Kf ι σ j w →
    Hyps C p n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar →
    ∀ φ : WF p n' ≃+* W, IsWittIdent σ φ →
    ∀ (K : ℕ) [NeZero r] [NeZero K] (hk : m + 1 = r + K) (hrk : r ≤ m + 1),
    ∀ F : Frames n' r, FramesOK TT L₁ L₂ (orbitWindowCount r de h x) (goodG' r de h x) F →
    ∀ E' : Fin n' → ℕ,
      (∀ t ∈ F.TT, E' t ≤ E0 p r (r + K) (orbitWindowCount r de h x) (goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar) ∧
        E' t ≤ flatDeg lam0 t) →
    ∀ (nb : ℕ) (B : Fin nb → RRing O n' (r + K)),
      (∀ i, B i ∈ Gen O p K F
        (symbolSpaces CLa p n' O r K F (flatDeg lam0) L₁ (min (orbitWindowCount r de h x) (2 * TT.card))
          (mStar p F (r + K) (orbitWindowCount r de h x) (p ^ goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar)) a Y)
        (G2d F (flatDeg lam0) E')) →
      LinearIndependent O B → (∃ T : Submodule O (RRing O n' (r + K)), IsCompl (Submodule.span O (Set.range B)) T) →
    ∀ e : Edge W Qq (m + 1), IsEdge p n' r e → e.tgt = colSpan W (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) →
    ∀ (hm : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n')),
      IsUnit hm.det → IsGLW g → IsEdgeBasis p r e (hm * ((matQ φ g)⁻¹).transpose) →
    letI : Algebra (WF p n') O := algOfIdent j φ
    ∀ FsB : Fin nb → ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O),
      (∀ b, subst p n' O w n' r g (FsB b : MvPolynomial (TV n' (m + 1)) (KK O)) =
        symB p n' O w hk hrk F g (cPrime n' r TT.card c0 cpp cStar) (p ^ goodG' r de h x) (B b)) →
      CloudAtY p n' ι σ w φ (r := r) TT lam0 cStar
        (t0 C Ct0 p TT.card (orbitWindowCount r de h x) L₁ (goodG' r de h x) (m + 1) a + (TT.card : ℝ) * c0 +
          om r TT.card n' c0 cpp)
        (CD1 * (TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a) e hm FsB

def RestCloudY (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 : ℝ) : Prop :=
  tableLineDegreeFive.admitted D CLa Ck Crk Cdeg → SourceCleaning.aux₃ D CLa' CD Csz → PlaneGramData.aux₃ D CH CE C6 C18 →
    ∃ Ct0 CD1 C₁ : ℝ, 0 < Ct0 ∧ 0 < CD1 ∧ 0 < C₁ ∧ ∀ C : ℝ, C₁ ≤ C → CloudStepY C Ct0 CD1 CLa

theorem restCloudX_of_Y (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 : ℝ)
    (hY : RestCloudY D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18) :
    RestCloudX D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 := by
  intro hA h14a h14b
  obtain ⟨Ct0, CD1, C₁, h0, h1, h2, hS⟩ := hY hA h14a h14b
  refine ⟨Ct0, CD1, max C₁ 1, h0, h1, lt_of_lt_of_le h2 (le_max_left _ _), ?_⟩
  intro C hC p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r _ _ TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H φ hφ K
    _ _ hk hrk F hF E' hE' nb B hB hli hc e he htgt hm g hhm hg hbasis FsB hFsB
  obtain ⟨Θ, hΘ, n2, tT, D1, sh, a2, a3, a4, a5, a6⟩ :=
    hS C (le_trans (le_max_left _ _) hC) p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H
      φ hφ K hk hrk F hF E' hE' nb B hB hli hc e he htgt hm g hhm hg hbasis FsB hFsB
  have hBs := hyps_basic (C := C) (le_trans (le_max_right _ _) hC) H
  have hW : tableLineDegreeFive.WeightHyp TT aT bT cpp c0 a lam0 := H.2.2.2.2.1
  have hm2 : 2 ≤ m := by have := hBs.m_ge; omega
  refine ⟨Θ, hΘ, n2, r * TT.card * c0 + 2 * r * n' * cpp, tT, D1, sh, ?_, a2, a3, fun i => ⟨a4 i, ?_⟩, a5, a6⟩
  · unfold om
    push_cast
    exact le_refl _
  · exact Re_le_scale_HL hSet.1 m r (restW TT lam0) (restW_dom (by omega) TT lam0 hW.2.1) e he _
      (ordMax_rest hm2 hW r) (a4 i)

end Formalism.MainNotions.Pf14
end
end

noncomputable section

namespace Formalism.MainNotions.Pf14

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning MvPolynomial
open Formalism.MainNotions.G.LatticeSystems (la_tw la_tw_det)
open Formalism.L2.G.Model (thF)

def IsTrueTheta {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O} (hS : HidaSetting p n' W Qq O Kf ι σ j w) {m : ℕ}
    (d : Fin n' → ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ) (vec : Fin n' → Bool)
    (h : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq)
    (Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O) ≃ₗ[O] ↥(Vsp Kf lam0)) : Prop :=
  ∀ F, ((Θ F : ↥(Vsp Kf lam0)) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) =
    thF hS m vec (fun x => la_tw ι σ x.val h) F.1

theorem theta_exists (p n' : ℕ) [Fact p.Prime] (W Qq O Kf : Type) [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Field Kf] [Algebra O Kf] (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O)
    (hS : HidaSetting p n' W Qq O Kf ι σ j w) (φ : WF p n' ≃+* W) (hφ : IsWittIdent σ φ)
    (m r : ℕ) (vec : Fin n' → Bool) (d : Fin n' → ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ)
    (hr1 : 1 ≤ r) (hr2 : r < m + 1) (hfl : IsFlat vec d lam0)
    (h : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (hh : IsUnit h.det) :
    letI : Algebra (WF p n') O := algOfIdent j φ
    ∃ Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O) ≃ₗ[O] ↥(Vsp Kf lam0),
      IsFlatIdent ι σ w φ r d lam0 vec h Θ ∧ IsTrueTheta hS d lam0 vec h Θ := by
  open Formalism.L2.G.Model in
  letI : Algebra (WF p n') O := algOfIdent j φ
  have hw := w_ne hS
  have hm : 1 ≤ m := by omega
  have hlam := flat_lam vec d lam0 hfl
  have hV : VS Kf m vec d = Vsp Kf lam0 := by
    unfold VS Vsp
    congr 1
    funext s
    rw [hlam s, if_pos (letterWt_anti _ _ _)]
  obtain ⟨Θ0, hΘ0⟩ := gen_equiv hS m hm vec d (fun x => la_tw ι σ x.val h) (fun x => la_tw_det _ _ _ _ hh)
  let Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O) ≃ₗ[O] ↥(Vsp Kf lam0) :=
    Θ0.trans ((LinearEquiv.ofEq _ _ hV).restrictScalars O)
  have hΘ : ∀ F, ((Θ F : ↥(Vsp Kf lam0)) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) =
      thF hS m vec (fun x => la_tw ι σ x.val h) F.1 := fun F => hΘ0 F
  have hH : ∀ Λ : Fin n' → Submodule O (Fin (m + 1) → Kf), Hten O lam0 Λ =
      tensorLat O Kf (fun x => H0 O m (letterWt m (d x) (vec x)) (Λ x)) := by
    intro Λ
    unfold Hten
    congr 1
    funext s
    rw [hlam s]
  refine ⟨Θ, ⟨?_, ?_⟩, hΘ⟩
  · intro F
    rw [gen_A hS m hm vec d (fun x => la_tw ι σ x.val h) (fun x => la_tw_det _ _ _ _ hh) F.1 F.2, ← hΘ F,
      ← tensor_lattice_twist_eq hS m vec d (fun x => x) h hh, ← hH]
    rfl
  · intro g hg e he F i
    have h1 : InWjRg p n' O w r (flatLetters vec) g F.1 i ↔
        ∃ y ∈ tensorLat O Kf (fun s : Fin n' => nablaLTw O Kf m (letterWt m (d s) (vec s))
            (Mx ι σ w φ r (fun x : Fin n' => x) h g s)),
          thF hS m vec (fun x => la_tw ι σ x.val h) F.1 =
            (algebraMap O Kf w ^ ((i : ℤ) - (Avec vec d : ℤ))) • y :=
      gen_R hS φ hφ m hm r (flatLetters vec) (fun x => x) (fun _ => rfl) d h hh g hg F.1 F.2 i
    rw [h1, ← hΘ F, ← tens_Le hS φ m r vec d (fun x => x) h hh g hg e he, ← hH]
    have h2 := mem_scale2 (O := O) (Vsp Kf lam0)
      (Hten O lam0 fun s => LeAt p ι σ w s.val e) (algebraMap O Kf w ^ (i : ℤ))
      (algebraMap O Kf w ^ (-Ar r lam0)) (zpow_ne_zero _ hw) (zpow_ne_zero _ hw) (Θ F)
    have e1 : algebraMap O Kf w ^ (i : ℤ) * algebraMap O Kf w ^ (-Ar r lam0) = algebraMap O Kf w ^
        ((i : ℤ) - (Avec vec d : ℤ)) := by
      rw [← zpow_add₀ hw, ← sub_eq_add_neg, flat_Ar r hr1 hr2 vec d lam0 hfl]
    rw [e1] at h2
    exact h2.symm

section At

variable (p n' : ℕ) {W Qq O Kf : Type} [CommRing W] [Field Qq] [Algebra W Qq] [CommRing O] [IsDomain O] [Field Kf]
  [Algebra O Kf] (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (w : O) {m : ℕ} (r : ℕ) (TT : Finset (Fin n'))
  (lam0 : Fin n' → Fin (m + 1) → ℤ)

def PrimAt (e : Edge W Qq (m + 1)) {nb : ℕ}
    (FsB : Fin nb → ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O))
    (Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O) ≃ₗ[O]
      ↥(Vsp Kf (flW (m := m) (dT TT lam0)))) : Prop :=
  ∃ (n2 : ℕ) (sh : Fin n2 → Vsp Kf (restW TT lam0)),
    (∀ i, sh i ∈ Re p ι σ w r (restW TT lam0) e) ∧ ((n2 : ℕ) : ℚ) = remainingWeightVectorCount TT lam0 ∧
      ∀ S : Fin nb × Fin n2 → Vsp Kf lam0,
        (∀ b i, ((S (b, i) : Vsp Kf lam0) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) =
          ((Θ (FsB b) : Vsp Kf (flW (m := m) (dT TT lam0))) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) *
            ((sh i : Vsp Kf (restW TT lam0)) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf)) →
        ∀ c : Fin nb × Fin n2 → O, (∃ x, IsUnit (c x)) →
          (∑ x, c x • S x) ∉ scale (algebraMap O Kf w ^ (1 : ℤ)) (Re p ι σ w r lam0 e)

def TestAt (cStar : ℕ) (bT bD : ℝ) (e : Edge W Qq (m + 1)) {nb : ℕ}
    (FsB : Fin nb → ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O))
    (Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O) ≃ₗ[O]
      ↥(Vsp Kf (flW (m := m) (dT TT lam0)))) : Prop :=
  ∃ tT D1 : ℕ, (tT : ℝ) ≤ bT ∧ (D1 : ℝ) ≤ bD ∧
    ∀ (n2 : ℕ) (sh : Fin n2 → Vsp Kf (restW TT lam0)), (∀ i, sh i ∈ Re p ι σ w r (restW TT lam0) e) →
      ∀ S : Fin nb × Fin n2 → Vsp Kf lam0,
        (∀ b i, ((S (b, i) : Vsp Kf lam0) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) =
          ((Θ (FsB b) : Vsp Kf (flW (m := m) (dT TT lam0))) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) *
            ((sh i : Vsp Kf (restW TT lam0)) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf)) →
        ∀ c : Fin nb × Fin n2 → O,
          (∑ x, c x • S x) ∉ scale (algebraMap O Kf w ^ (1 : ℤ)) (Re p ι σ w r lam0 e) →
          ∃ G : Module.Dual Kf (Vsp Kf lam0),
            G ∈ scale (algebraMap O Kf w ^ (-(tT : ℤ))) (dualLat O Kf (HL (O := O) ι σ lam0 e.tgt)) ∧
            G ∈ Re' p ι σ w r lam0 e ∧
            (∀ e' : Edge W Qq (m + 1), IsEdge p n' r e' → e'.tgt = e.tgt → e' ≠ e →
              G ∈ scale (algebraMap O Kf w ^ (cStar : ℤ)) (Re' p ι σ w r lam0 e')) ∧
            ValLe (p : O) D1 (be p r lam0 (∑ x, c x • S x) G)

end At

def PrimStep (C CLa : ℝ) : Prop :=
  ∀ (p : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O)
    (n' m r : ℕ) [Fact p.Prime] [NeZero n'] (TT : Finset (Fin n')) (L₁ L₂ : ℕ) (de h x : ℝ)
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (aT bT : Fin n' → ℤ) (a Y : ℝ) (cpp c0 Dp cStar : ℕ),
    ∀ hSet : UnramifiedQuadraticSetting p n' W Qq O Kf ι σ j w,
    Hyps C p n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar →
    ∀ φ : WF p n' ≃+* W, IsWittIdent σ φ →
    ∀ (K : ℕ) [NeZero r] [NeZero K] (hk : m + 1 = r + K) (hrk : r ≤ m + 1),
    ∀ F : Frames n' r, FramesOK TT L₁ L₂ (orbitWindowCount r de h x) (goodG' r de h x) F →
    ∀ E' : Fin n' → ℕ,
      (∀ t ∈ F.TT, E' t ≤ E0 p r (r + K) (orbitWindowCount r de h x) (goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar) ∧
        E' t ≤ flatDeg lam0 t) →
    ∀ (nb : ℕ) (B : Fin nb → RRing O n' (r + K)),
      (∀ i, B i ∈ Gen O p K F
        (symbolSpaces CLa p n' O r K F (flatDeg lam0) L₁ (min (orbitWindowCount r de h x) (2 * TT.card))
          (mStar p F (r + K) (orbitWindowCount r de h x) (p ^ goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar)) a Y)
        (G2d F (flatDeg lam0) E')) →
      LinearIndependent O B → (∃ T : Submodule O (RRing O n' (r + K)), IsCompl (Submodule.span O (Set.range B)) T) →
    ∀ e : Edge W Qq (m + 1), IsEdge p n' r e → e.tgt = colSpan W (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) →
    ∀ (hm : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n')),
      IsUnit hm.det → IsGLW g → IsEdgeBasis p r e (hm * ((matQ φ g)⁻¹).transpose) →
    letI : Algebra (WF p n') O := algOfIdent j φ
    ∀ FsB : Fin nb → ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O),
      (∀ b, subst p n' O w n' r g (FsB b : MvPolynomial (TV n' (m + 1)) (KK O)) =
        symB p n' O w hk hrk F g (cPrime n' r TT.card c0 cpp cStar) (p ^ goodG' r de h x) (B b)) →
      ∀ Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O) ≃ₗ[O]
      ↥(Vsp Kf (flW (m := m) (dT TT lam0))),
        IsTrueTheta hSet.1 (dT TT lam0) (flW (dT TT lam0)) (vecE n') hm Θ →
        PrimAt p n' ι σ w r TT lam0 e FsB Θ

def TestStep (C Ct0 CD1 CLa : ℝ) : Prop :=
  ∀ (p : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O)
    (n' m r : ℕ) [Fact p.Prime] [NeZero n'] (TT : Finset (Fin n')) (L₁ L₂ : ℕ) (de h x : ℝ)
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (aT bT : Fin n' → ℤ) (a Y : ℝ) (cpp c0 Dp cStar : ℕ),
    ∀ hSet : UnramifiedQuadraticSetting p n' W Qq O Kf ι σ j w,
    Hyps C p n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar →
    ∀ φ : WF p n' ≃+* W, IsWittIdent σ φ →
    ∀ (K : ℕ) [NeZero r] [NeZero K] (hk : m + 1 = r + K) (hrk : r ≤ m + 1),
    ∀ F : Frames n' r, FramesOK TT L₁ L₂ (orbitWindowCount r de h x) (goodG' r de h x) F →
    ∀ E' : Fin n' → ℕ,
      (∀ t ∈ F.TT, E' t ≤ E0 p r (r + K) (orbitWindowCount r de h x) (goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar) ∧
        E' t ≤ flatDeg lam0 t) →
    ∀ (nb : ℕ) (B : Fin nb → RRing O n' (r + K)),
      (∀ i, B i ∈ Gen O p K F
        (symbolSpaces CLa p n' O r K F (flatDeg lam0) L₁ (min (orbitWindowCount r de h x) (2 * TT.card))
          (mStar p F (r + K) (orbitWindowCount r de h x) (p ^ goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar)) a Y)
        (G2d F (flatDeg lam0) E')) →
      LinearIndependent O B → (∃ T : Submodule O (RRing O n' (r + K)), IsCompl (Submodule.span O (Set.range B)) T) →
    ∀ e : Edge W Qq (m + 1), IsEdge p n' r e → e.tgt = colSpan W (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) →
    ∀ (hm : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n')),
      IsUnit hm.det → IsGLW g → IsEdgeBasis p r e (hm * ((matQ φ g)⁻¹).transpose) →
    letI : Algebra (WF p n') O := algOfIdent j φ
    ∀ FsB : Fin nb → ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O),
      (∀ b, subst p n' O w n' r g (FsB b : MvPolynomial (TV n' (m + 1)) (KK O)) =
        symB p n' O w hk hrk F g (cPrime n' r TT.card c0 cpp cStar) (p ^ goodG' r de h x) (B b)) →
      ∀ Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O) ≃ₗ[O]
      ↥(Vsp Kf (flW (m := m) (dT TT lam0))),
        IsTrueTheta hSet.1 (dT TT lam0) (flW (dT TT lam0)) (vecE n') hm Θ →
        TestAt p n' ι σ w r TT lam0 cStar
          (t0 C Ct0 p TT.card (orbitWindowCount r de h x) L₁ (goodG' r de h x) (m + 1) a + (TT.card : ℝ) * c0 +
            om r TT.card n' c0 cpp)
          (CD1 * (TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a) e FsB Θ

def SourcePrimitiveIntegrality (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) : Prop :=
  tableLineDegreeFive.admitted D CLa Ck Crk Cdeg → ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ C : ℝ, C₁ ≤ C → PrimStep C CLa

def RemainingInputsAfter (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 : ℝ) : Prop :=
  tableLineDegreeFive.admitted D CLa Ck Crk Cdeg → SourceCleaning.aux₃ D CLa' CD Csz → PlaneGramData.aux₃ D CH CE C6 C18 →
    ∃ Ct0 CD1 C₁ : ℝ, 0 < Ct0 ∧ 0 < CD1 ∧ 0 < C₁ ∧ ∀ C : ℝ, C₁ ≤ C → TestStep C Ct0 CD1 CLa

private lemma isFlat_flW_lemma {n' m : ℕ} (d : Fin n' → ℕ) : IsFlat (m := m) (vecE n') d (flW d) := by
  intro s
  by_cases hs : Even s.val
  · simp [lamAt, vecE, flW, hs]
  · funext i
    by_cases hi : i = Fin.last m
    · subst hi
      simp [lamAt, vecE, flW, hs, Pi.single_apply]
    · have hr : i.rev ≠ 0 := by
        intro h0
        apply hi
        rw [← Fin.rev_rev i, h0, Fin.rev_zero]
      simp [lamAt, vecE, flW, hs, Pi.single_apply, hi, hr]

theorem restCloudY_of (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 : ℝ)
    (h6a : SourcePrimitiveIntegrality D CLa Ck Crk Cdeg) (h6b : RemainingInputsAfter D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18) :
    RestCloudY D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 := by
  unfold RestCloudY
  intro hA h14a h14b
  obtain ⟨C₁a, hC₁a, hPa⟩ := h6a hA
  obtain ⟨Ct0, CD1, C₁b, hCt0, hCD1, hC₁b, hPb⟩ := h6b hA h14a h14b
  refine ⟨Ct0, CD1, max C₁a C₁b, hCt0, hCD1, lt_max_of_lt_left hC₁a, fun C hC => ?_⟩
  have hPrim := hPa C (le_trans (le_max_left _ _) hC)
  have hTest := hPb C (le_trans (le_max_right _ _) hC)
  unfold CloudStepY
  intro p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r _ _ TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar
    hSet hHyps φ hφ K _ _ hk hrk F hF E' hE' nb B hB hLI hT e he het hm g hmdet hg heb
  intro FsB hFsB
  have hr1 : 1 ≤ r := Nat.one_le_iff_ne_zero.2 (NeZero.ne r)
  have hr2 : r < m + 1 := by
    have := NeZero.ne K
    omega
  obtain ⟨Θ, hΘ1, hΘ2⟩ := theta_exists p n' W Qq O Kf ι σ j w hSet.1 φ hφ m r (vecE n') (dT TT lam0)
    (flW (dT TT lam0)) hr1 hr2 (isFlat_flW_lemma (dT TT lam0)) hm hmdet
  obtain ⟨n2, sh, hsh, hn2, hprim⟩ := hPrim p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y
    cpp c0 Dp cStar hSet hHyps φ hφ K hk hrk F hF E' hE' nb B hB hLI hT e he het hm g hmdet hg heb
    FsB hFsB Θ hΘ2
  obtain ⟨tT, D1, htT, hD1, htest⟩ := hTest p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y
    cpp c0 Dp cStar hSet hHyps φ hφ K hk hrk F hF E' hE' nb B hB hLI hT e he het hm g hmdet hg heb
    FsB hFsB Θ hΘ2
  unfold CloudAtY
  exact ⟨Θ, hΘ1, n2, tT, D1, sh, htT, hD1, hsh, hn2,
    fun S hS c hc => htest n2 sh hsh S hS c (hprim S hS c hc)⟩

end Formalism.MainNotions.Pf14
