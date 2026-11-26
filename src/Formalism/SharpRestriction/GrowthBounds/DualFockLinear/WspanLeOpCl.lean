module

public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.FockRLinDual

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.DualFockLinear.RestNDOfAdm
section -- merged from Formalism.SharpRestriction.GrowthBounds.DualFockLinear.NormalDegreeZeroMul
section -- merged from Formalism.SharpRestriction.GrowthBounds.DualFockLinear.NormDegUniv
section -- merged from Formalism.SharpRestriction.GrowthBounds.DualFockLinear.Lemma4ElementZero
noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14

theorem lemma4_element_normal_degree {p n' r : ℕ} [NeZero n'] {K : ℕ} [NeZero r] [NeZero K] {O : Type} [CommRing O] [IsDomain O]
    {Fr : Frames n' r} {N₁ G' cP : ℕ} {deg : Fin n' → ℕ} {Y : ℝ} {k : ℕ} (hk : k = r + K) {o : ℕ}
    {sig : MvPolynomial (TV n' k) (KK O)} (hs : OneSidedLemma4Element p K O Fr N₁ G' cP deg Y hk o sig) :
    ∀ mm ∈ sig.support, normDeg r mm = o := by
  subst hk
  obtain ⟨n, obd, xi, dd, mon, -, -, -, -, h5, rfl⟩ := hs
  have hren : rename (castVK (n' := n') (rfl : r + K = r + K)) (monPh O K p Fr mon xi) = monPh O K p Fr mon xi := by
    have : (castVK (n' := n') (rfl : r + K = r + K)) = id := by
      funext v
      rfl
    rw [this, rename_id_apply]
  rw [hren]
  intro mm hmm
  exact h5 mm (support_map_subset _ _ hmm)

theorem lemma4_element_zero {p n' r : ℕ} (hp : 0 < p) [NeZero n'] {K : ℕ} [NeZero r] [NeZero K] {O : Type} [CommRing O] [IsDomain O]
    (Fr : Frames n' r) (N₁ G' cP : ℕ) (deg : Fin n' → ℕ) (Y : ℝ) {k : ℕ} (hk : k = r + K) (o : ℕ) :
    OneSidedLemma4Element p K O Fr N₁ G' cP deg Y hk o (0 : MvPolynomial (TV n' k) (KK O)) := by
  refine ⟨0, fun _ _ => 0, fun i => i.elim0, fun _ _ => 0, 0, fun i => i.elim0, ?_, ?_, ?_, ?_, ?_⟩
  · intro j _ x _ _
    have : 0 ≤ levDeg p Fr deg j x := by
      unfold levDeg
      positivity
    push_cast
    linarith
  · intro j x _ _ c
    simpa using Nat.pow_pos hp
  · intro v hv
    simp at hv
  · intro mm hmm
    simp [monPh] at hmm
  · simp [monPh]

section At

variable (p n' : ℕ) [Fact p.Prime] [NeZero n'] {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
  [Field Qq] [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf]
  [Algebra O Kf] [Algebra (WF p n') O] (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) {j : W →+* O} (w : O) {m : ℕ} (r : ℕ)
  (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (m + 1) → ℤ)

def XiAtN (K : ℕ) [NeZero r] [NeZero K] (hk : m + 1 = r + K) (Fr : Frames n' r) (N₁ G' : ℕ) (Y : ℝ)
    (c0 cP κ : ℕ) (bD : ℝ) (e : Edge W Qq (m + 1)) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n')) {nb : ℕ}
    (FsB : Fin nb → ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O))
    (Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O) ≃ₗ[O]
      ↥(Vsp Kf (flW (m := m) (dT TT lam0)))) : Prop :=
  ∃ DX : ℕ, (DX : ℝ) ≤ bD ∧
    ∀ F1 : ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O),
      (F1 : MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) ∈ SgOp n' TT lam0 c0 FsB →
      Θ F1 ∈ Re p ι σ w r (flW (dT TT lam0)) e →
      Θ F1 ∉ scale (algebraMap O Kf w ^ (1 : ℤ)) (Re p ι σ w r (flW (dT TT lam0)) e) →
      ∃ (nq : ℕ) (o : Fin nq → ℕ) (sig : Fin nq → MvPolynomial (TV n' (m + 1)) (KK O)),
        (∀ q, HasMultideg (sig q) (dT TT lam0) ∧
          OneSidedLemma4Element p K O Fr N₁ G' cP (flatDeg lam0) Y hk (o q) (sig q)) ∧
        ValLe (Kf := KK O) (p : O) DX
          ((p : KK O) ^ κ * fock (subst p n' O w n' r g (F1 : MvPolynomial (TV n' (m + 1)) (KK O))) (∑ q, sig q) /
            (((∏ s, (dT TT lam0 s).factorial : ℕ) : ℕ) : KK O))

def NDAt (c0 : ℕ) (bT : ℝ) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n')) {nb : ℕ}
    (FsB : Fin nb → ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O)) : Prop :=
  ∃ tF : ℕ, (tF : ℝ) ≤ bT ∧ ∀ f ∈ SgOp n' TT lam0 c0 FsB,
    ∀ mm ∈ (subst p n' O w n' r g f).support, normDeg r mm ≤ tF

variable {p n' ι σ w r TT lam0}

theorem xiAt_of {K : ℕ} [NeZero r] [NeZero K] {hk : m + 1 = r + K} {Fr : Frames n' r} {N₁ G' : ℕ} {Y : ℝ}
    {c0 cP κ : ℕ} {bT bD : ℝ} {e : Edge W Qq (m + 1)} {g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n')} {nb : ℕ}
    {FsB : Fin nb → ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O)}
    {Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O) ≃ₗ[O]
      ↥(Vsp Kf (flW (m := m) (dT TT lam0)))}
    (hN : XiAtN p n' ι σ w r TT lam0 K hk Fr N₁ G' Y c0 cP κ bD e g FsB Θ)
    (hD : NDAt p n' w r TT lam0 c0 bT g FsB) :
    XiAt p n' ι σ w r TT lam0 K hk Fr N₁ G' Y c0 cP κ bT bD e g FsB Θ := by
  obtain ⟨DX, hDX, hN⟩ := hN
  obtain ⟨tF, htF, hD⟩ := hD
  refine ⟨tF, DX, htF, hDX, fun F1 h1 h2 h3 => ?_⟩
  obtain ⟨nq, o, sig, hs, hv⟩ := hN F1 h1 h2 h3
  refine ⟨nq, fun q => if o q ≤ tF then o q else 0, fun q => if o q ≤ tF then sig q else 0, fun q => ?_, ?_⟩
  · by_cases hq : o q ≤ tF
    · simp only [ite_eq_left hq]
      exact ⟨hq, (hs q).1, (hs q).2⟩
    · simp only [ite_eq_right hq]
      exact ⟨Nat.zero_le _, Submodule.zero_mem _, lemma4_element_zero (Fact.out : p.Prime).pos Fr N₁ G' cP _ Y hk 0⟩
  · have e1 : fock (subst p n' O w n' r g (F1 : MvPolynomial (TV n' (m + 1)) (KK O)))
        (∑ q, if o q ≤ tF then sig q else 0) =
        fock (subst p n' O w n' r g (F1 : MvPolynomial (TV n' (m + 1)) (KK O))) (∑ q, sig q) := by
      unfold fock
      refine Finset.sum_congr rfl fun mm hmm => ?_
      congr 2
      rw [coeff_sum, coeff_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      by_cases hq : o q ≤ tF
      · rw [ite_eq_left hq]
      · rw [ite_eq_right hq]
        change 0 = _
        by_contra hne
        have h4 : mm ∈ (sig q).support := mem_support_iff.2 (Ne.symm hne)
        have h5 := lemma4_element_normal_degree hk (hs q).2 mm h4
        have h6 := hD _ h1 mm hmm
        omega
    rw [e1]
    exact hv

end At

def XiStepN (C CD CLa : ℝ) : Prop :=
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
        XiAtN p n' ι σ w r TT lam0 K hk F (orbitWindowCount r de h x) (goodG' r de h x) Y c0 (cPrime n' r TT.card c0 cpp cStar)
          (kapFl p (m + 1) (dT TT lam0))
          (CD * (TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a) e g FsB Θ

def NDStep (C Ct0 CLa : ℝ) : Prop :=
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
        NDAt p n' w r TT lam0 c0
          (t0 C Ct0 p TT.card (orbitWindowCount r de h x) L₁ (goodG' r de h x) (m + 1) a + (TT.card : ℝ) * c0) g FsB

def RestXiN (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CH CE C6 C18 : ℝ) : Prop :=
  tableLineDegreeFive.admitted D CLa Ck Crk Cdeg → PlaneGramData.aux₃ D CH CE C6 C18 →
    ∃ CDf C₁ : ℝ, 0 < CDf ∧ 0 < C₁ ∧ ∀ C : ℝ, C₁ ≤ C → XiStepN C CDf CLa

def RestND (CLa : ℝ) : Prop :=
  ∃ Ct0 C₁ : ℝ, 0 < Ct0 ∧ 0 < C₁ ∧ ∀ C : ℝ, C₁ ≤ C → NDStep C Ct0 CLa

theorem restXi_of (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CH CE C6 C18 : ℝ)
    (hN : RestXiN D CLa Ck Crk Cdeg CH CE C6 C18) (hD : RestND CLa) : RestXi D CLa Ck Crk Cdeg CH CE C6 C18 := by
  intro hA h14b
  obtain ⟨CDf, C₂, h1, hC2, hN⟩ := hN hA h14b
  obtain ⟨Ct0, C₃, h0, hC3, hD⟩ := hD
  refine ⟨Ct0, CDf, max C₂ C₃, h0, h1, lt_of_lt_of_le hC2 (le_max_left _ _), ?_⟩
  intro C hCC p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r _ _ TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H φ hφ K
    _ _ hk hrk F hFr E' hE' nb B hB hli hc e he htgt hm g hhm hg hbasis
  let : Algebra (WF p n') O := algOfIdent j φ
  intro FsB hFsB Θ hΘ
  exact xiAt_of
    (hN C (le_trans (le_max_left _ _) hCC) p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y
      cpp c0 Dp cStar hSet H φ hφ K hk hrk F hFr E' hE' nb B hB hli hc e he htgt hm g hhm hg hbasis FsB hFsB Θ hΘ)
    (hD C (le_trans (le_max_right _ _) hCC) p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y
      cpp c0 Dp cStar hSet H φ hφ K hk hrk F hFr E' hE' nb B hB hli hc e he htgt hm g hhm hg hbasis FsB hFsB Θ hΘ)

end Formalism.MainNotions.TestSideCounting
end
end

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14
open Formalism.L2.G.Model (Lin)

section ND

variable {R : Type} [CommRing R] {n' k : ℕ}

theorem normDeg_univ (r : ℕ) (m : TV n' k →₀ ℕ) :
    normDeg r m = ∑ v : TV n' k, if IsNormal r v then m v else 0 := by
  unfold normDeg
  apply Finset.sum_subset (Finset.subset_univ _)
  intro v _ hv
  rw [Finsupp.notMem_support_iff] at hv
  simp [hv]

theorem normDeg_add (r : ℕ) (m m' : TV n' k →₀ ℕ) : normDeg r (m + m') = normDeg r m + normDeg r m' := by
  simp only [normDeg_univ, Finsupp.coe_add, Pi.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  split_ifs <;> simp

def NDsub (R : Type) [CommRing R] (n' k r T : ℕ) : Submodule R (MvPolynomial (TV n' k) R) :=
  restrictSupport R {mm | normDeg r mm ≤ T}

theorem mem_NDsub {r T : ℕ} {P : MvPolynomial (TV n' k) R} :
    P ∈ NDsub R n' k r T ↔ ∀ mm ∈ P.support, normDeg r mm ≤ T := by
  show P ∈ restrictSupport R {mm | normDeg r mm ≤ T} ↔ _
  exact ⟨fun h mm hm => h hm, fun h mm hm => h mm hm⟩

theorem NDsub_mono {r T T' : ℕ} (h : T ≤ T') : NDsub R n' k r T ≤ NDsub R n' k r T' := by
  intro P hP
  rw [mem_NDsub] at hP ⊢
  intro mm hm
  exact (hP mm hm).trans h

theorem nd_move (r : ℕ) (mm : TV n' k →₀ ℕ) (v v' : TV n' k) :
    normDeg r (Finsupp.single v 1 + (mm - Finsupp.single v' 1)) ≤ normDeg r mm + 1 := by
  rw [normDeg_add]
  have h1 : normDeg r (Finsupp.single v 1 : TV n' k →₀ ℕ) ≤ 1 := by
    rw [normDeg_univ]
    calc ∑ w : TV n' k, (if IsNormal r w then (Finsupp.single v 1 : TV n' k →₀ ℕ) w else 0)
        ≤ ∑ w : TV n' k, (Finsupp.single v 1 : TV n' k →₀ ℕ) w :=
          Finset.sum_le_sum fun w _ => by split_ifs <;> simp
      _ = 1 := by simp [Finsupp.single_apply]
  have h2 : normDeg r (mm - Finsupp.single v' 1) ≤ normDeg r mm := by
    rw [normDeg_univ, normDeg_univ]
    apply Finset.sum_le_sum
    intro w _
    split_ifs
    · simp only [Finsupp.tsub_apply]
      exact tsub_le_self
    · exact le_rfl
  omega

theorem nd_op (r T : ℕ) (v v' : TV n' k) {P : MvPolynomial (TV n' k) R} (hP : P ∈ NDsub R n' k r T) :
    X v * pderiv v' P ∈ NDsub R n' k r (T + 1) := by
  rw [mem_NDsub] at hP
  set_option synthInstance.maxHeartbeats 100000 in
    rw [P.as_sum, map_sum, Finset.mul_sum]
  refine Submodule.sum_mem _ fun mm hmm => ?_
  rw [pderiv_monomial, ← pow_one (X v), ← monomial_single_add, mem_NDsub]
  intro mm' hmm'
  rw [Finset.mem_singleton.mp (support_monomial_subset hmm')]
  exact (nd_move r mm v v').trans (Nat.add_le_add_right (hP mm hmm) 1)

theorem nd_mul {r T T' : ℕ} {P Q : MvPolynomial (TV n' k) R} (hP : P ∈ NDsub R n' k r T) (hQ : Q ∈ NDsub R n' k r T') :
    P * Q ∈ NDsub R n' k r (T + T') := by
  rw [mem_NDsub] at *
  intro mm hmm
  have h1 := support_mul P Q hmm
  rw [Finset.mem_add] at h1
  obtain ⟨a, ha, b, hb, rfl⟩ := h1
  rw [normDeg_add]
  exact Nat.add_le_add (hP a ha) (hQ b hb)

theorem Lin_pderiv (N N' : Fin n' → Matrix (Fin k) (Fin k) R) (h : ∀ s, N s * N' s = 1) (s : Fin n') (b : Fin k)
    (f : MvPolynomial (Fin n' × Fin k) R) :
    Lin N (pderiv (s, b) f) = ∑ c, N' s c b • pderiv (s, c) (Lin N f) := by
  simp only [Lin_chain, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul]
  have hm : ∀ a, ∑ c, N' s c b * N s a c = (1 : Matrix (Fin k) (Fin k) R) a b := by
    intro a
    rw [← h s, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun c _ => mul_comm _ _
  simp [hm, Matrix.one_apply]

theorem nd_Lin_op (N N' : Fin n' → Matrix (Fin k) (Fin k) R) (h : ∀ s, N s * N' s = 1) (r T : ℕ) (s : Fin n')
    (a b : Fin k) {f : MvPolynomial (Fin n' × Fin k) R} (hf : Lin N f ∈ NDsub R n' k r T) :
    Lin N (X (s, a) * pderiv (s, b) f) ∈ NDsub R n' k r (T + 1) := by
  rw [map_mul, Lin_X, Lin_pderiv N N' h, Finset.sum_mul]
  refine Submodule.sum_mem _ fun b' _ => ?_
  rw [Finset.mul_sum]
  refine Submodule.sum_mem _ fun c _ => ?_
  rw [mul_smul_comm, mul_assoc, ← smul_eq_C_mul]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (nd_op r T _ _ hf))

theorem nd_word (N N' : Fin n' → Matrix (Fin k) (Fin k) R) (h : ∀ s, N s * N' s = 1) (r T : ℕ)
    {f : MvPolynomial (Fin n' × Fin k) R} (hf : Lin N f ∈ NDsub R n' k r T) :
    ∀ l : List (Fin n' × (Fin k × Fin k)), Lin N (opWord l f) ∈ NDsub R n' k r (T + l.length) := by
  intro l
  induction l with
  | nil => exact hf
  | cons y l ih =>
    show Lin N (X (y.1, y.2.1) * pderiv (y.1, y.2.2) (opWord l f)) ∈ NDsub R n' k r (T + (l.length + 1))
    rw [← Nat.add_assoc]
    exact nd_Lin_op N N' h r (T + l.length) y.1 y.2.1 y.2.2 ih

theorem word_length {τ : Type} (TT : Finset (Fin n')) (c : ℕ) :
    ∀ l : List (Fin n' × τ), (∀ z ∈ l, z.1 ∈ TT) → (∀ s, (l.filter fun z => z.1 = s).length ≤ c) →
      l.length ≤ TT.card * c := by
  intro l hl hc
  have key : ∀ l : List (Fin n' × τ), (∀ z ∈ l, z.1 ∈ TT) →
      l.length = ∑ s ∈ TT, (l.filter fun z => z.1 = s).length := by
    intro l hl
    induction l with
    | nil => simp
    | cons z l ih =>
      have e : ∀ s, ((z :: l).filter fun w => w.1 = s).length =
          (l.filter fun w => w.1 = s).length + if z.1 = s then 1 else 0 := by
        intro s
        by_cases hs : z.1 = s <;> simp [List.filter_cons, hs]
      rw [List.length_cons, ih (fun w hw => hl w (List.mem_cons_of_mem _ hw)),
        Finset.sum_congr rfl (fun s _ => e s), Finset.sum_add_distrib, Finset.sum_ite_eq]
      simp [hl z (by simp)]
  rw [key l hl]
  calc ∑ s ∈ TT, (l.filter fun z => z.1 = s).length ≤ ∑ s ∈ TT, c := Finset.sum_le_sum fun s _ => hc s
    _ = TT.card * c := by rw [Finset.sum_const, smul_eq_mul]

theorem nd_OpCl (N N' : Fin n' → Matrix (Fin k) (Fin k) R) (h : ∀ s, N s * N' s = 1) (r T : ℕ) (TT : Finset (Fin n'))
    (c : ℕ) (M : Submodule R (MvPolynomial (Fin n' × Fin k) R)) (hM : ∀ f ∈ M, Lin N f ∈ NDsub R n' k r T) :
    ∀ f ∈ OpCl TT c M, Lin N f ∈ NDsub R n' k r (T + TT.card * c) := by
  intro f hf
  unfold OpCl at hf
  induction hf using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨f0, hf0, l, h1, h2, rfl⟩ := hy
    exact NDsub_mono (Nat.add_le_add_left (word_length TT c l h1 h2) T) (nd_word N N' h r T (hM f0 hf0) l)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

end ND

end Formalism.MainNotions.TestSideCounting
end
end

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.G.WittFrameLocaliserOrders
open Formalism.L2.G.Model (Lin)

section Zero

variable {R : Type} [CommRing R] {n' k : ℕ}

theorem normal_degree_zero_one (r : ℕ) : (1 : MvPolynomial (TV n' k) R) ∈ NDsub R n' k r 0 := by
  rw [NDsub, MvPolynomial.mem_restrictSupport_iff]
  intro m hm
  have hm0 : m = 0 := by
    by_contra hne
    rw [Finset.mem_coe, MvPolynomial.mem_support_iff, MvPolynomial.coeff_one, if_neg (Ne.symm hne)] at hm
    exact hm rfl
  subst hm0
  simp [normDeg]

private lemma normDeg_add' {r : ℕ} (a b : TV n' k →₀ ℕ) : normDeg r (a + b) = normDeg r a + normDeg r b := by
  classical
  unfold normDeg
  exact Finsupp.sum_add_index' (h := fun v c => if IsNormal r v then c else 0) (fun v => by simp)
    (fun v c₁ c₂ => by split_ifs <;> simp)

theorem normal_degree_zero_mul {r : ℕ} {P Q : MvPolynomial (TV n' k) R} (hP : P ∈ NDsub R n' k r 0) (hQ : Q ∈ NDsub R n' k r 0) :
    P * Q ∈ NDsub R n' k r 0 := by
  rw [NDsub, MvPolynomial.mem_restrictSupport_iff] at hP hQ ⊢
  intro m hm
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul P Q hm)
  have h1 := hP ha
  have h2 := hQ hb
  simp only [Set.mem_setOf_eq, nonpos_iff_eq_zero] at h1 h2 ⊢
  simp [normDeg_add', h1, h2]

theorem normal_degree_zero_pow {r : ℕ} {P : MvPolynomial (TV n' k) R} (hP : P ∈ NDsub R n' k r 0) (n : ℕ) :
    P ^ n ∈ NDsub R n' k r 0 := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact normal_degree_zero_one r
  | succ n ih =>
    rw [pow_succ]
    exact normal_degree_zero_mul ih hP

theorem normal_degree_zero_prod {r : ℕ} {α : Type} (s : Finset α) (f : α → MvPolynomial (TV n' k) R)
    (h : ∀ i ∈ s, f i ∈ NDsub R n' k r 0) : ∏ i ∈ s, f i ∈ NDsub R n' k r 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty]
    exact normal_degree_zero_one r
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact normal_degree_zero_mul (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem normal_degree_zero_X_abnormal {r : ℕ} (v : TV n' k) (hv : ¬ IsNormal r v) : (X v : MvPolynomial (TV n' k) R) ∈ NDsub R n' k r 0 := by
  rw [NDsub, MvPolynomial.mem_restrictSupport_iff]
  intro m hm
  have hm' : m ∈ ({Finsupp.single v 1} : Finset (TV n' k →₀ ℕ)) :=
    MvPolynomial.support_monomial_subset (R := R) hm
  rw [Finset.mem_singleton] at hm'
  subst hm'
  show normDeg r (Finsupp.single v 1) ≤ 0
  unfold normDeg
  rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton, if_neg hv]

theorem normal_degree_zero_det_pmat {r : ℕ} (hrk : r ≤ k) (A : Fin r → Fin n') (P : Fin r → ℕ) (hA : ∀ l, Even (A l).val) :
    (pmat R hrk A P).det ∈ NDsub R n' k r 0 := by
  rw [Matrix.det_apply]
  refine Submodule.sum_mem _ fun σ _ => ?_
  rw [Units.smul_def]
  refine zsmul_mem ?_ _
  refine normal_degree_zero_prod _ _ fun i _ => ?_
  refine normal_degree_zero_pow ?_ _
  refine normal_degree_zero_X_abnormal _ ?_
  intro hN
  unfold IsNormal at hN
  rw [if_pos (hA _)] at hN
  simp only [Fin.coe_castLE] at hN
  omega

theorem fixed_symbol_normal_degree_zero (p : ℕ) [NeZero n'] {r : ℕ} (F : Frames n' r) {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁) (hn : Even n')
    (hr : 1 ≤ r) (hrk : r ≤ k) (c' Q : ℕ) : SPR R p F hrk c' Q ∈ NDsub R n' k r 0 := by
  have h1 : ∀ j : ℤ, (pmat R hrk (fun l => posOf n' (F.fr j l.val))
      (fun l => p ^ (zF F j - F.fr j l.val).toNat)).det ∈ NDsub R n' k r 0 := fun j =>
    normal_degree_zero_det_pmat hrk _ _ fun l => (posOf_even hn _).2 (hV.2.2.2.2.1 j l.val l.isLt).2
  have h2 : ∀ s : ℤ, (pmat R hrk (fun l => posOf n' (Arow F s l.val))
      (fun l => p ^ (s - Arow F s l.val).toNat)).det ∈ NDsub R n' k r 0 := fun s =>
    normal_degree_zero_det_pmat hrk _ _ fun l => (posOf_even hn _).2 (window_holds_even_tops n' r F L₁ N₁ hV hn hr s l.val l.isLt).1
  unfold SPR
  exact normal_degree_zero_mul (normal_degree_zero_mul (normal_degree_zero_pow (normal_degree_zero_prod _ _ fun j _ => normal_degree_zero_pow (h1 _) _) _)
    (normal_degree_zero_prod _ _ fun j _ => normal_degree_zero_pow (h1 _) _)) (normal_degree_zero_prod _ _ fun s _ => normal_degree_zero_pow (h2 _) _)

theorem nd_map {R' : Type} [CommRing R'] (f : R →+* R') {r T : ℕ} {P : MvPolynomial (TV n' k) R}
    (hP : P ∈ NDsub R n' k r T) : map f P ∈ NDsub R' n' k r T := by
  rw [NDsub, MvPolynomial.mem_restrictSupport_iff] at hP ⊢
  exact fun m hm => hP (MvPolynomial.support_map_subset f P hm)

theorem nd_rename {r K : ℕ} (hk : k = r + K) {T : ℕ} {P : MvPolynomial (Fin n' × Fin (r + K)) R}
    (hP : ∀ mm ∈ P.support, vsDeg mm ≤ T) : rename (castVK (n' := n') hk) P ∈ NDsub R n' k r T := by
  classical
  rw [NDsub, MvPolynomial.mem_restrictSupport_iff]
  intro m hm
  have hinj : Function.Injective (castVK (n' := n') hk) := by
    intro x y hxy
    simp only [castVK, Prod.mk.injEq] at hxy
    exact Prod.ext hxy.1 (Fin.cast_injective _ hxy.2)
  rw [Finset.mem_coe, MvPolynomial.support_rename_of_injective hinj, Finset.mem_image] at hm
  obtain ⟨mm, hmm, rfl⟩ := hm
  have key : normDeg r (Finsupp.mapDomain (castVK hk) mm) = vsDeg mm := by
    unfold normDeg vsDeg
    rw [show (∑ v ∈ (Finsupp.mapDomain (castVK hk) mm).support,
        if IsNormal r v then (Finsupp.mapDomain (castVK hk) mm) v else 0) =
        (Finsupp.mapDomain (castVK hk) mm).sum (fun v c => if IsNormal r v then c else 0) from rfl]
    rw [Finsupp.sum_mapDomain_index (fun _ => by simp) (fun _ _ _ => by split_ifs <;> simp),
      Finsupp.sum_fintype _ _ (fun _ => by simp), Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Fin.sum_univ_add]
    by_cases ht : Even t.val
    · rw [if_pos ht]
      simp [IsNormal, castVK, ht]
    · rw [if_neg ht]
      simp [IsNormal, castVK, ht]
  rw [Set.mem_setOf_eq, key]
  exact hP mm hmm

end Zero

section Sub

variable (p n' : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [Algebra (WF p n') O] (w : O) (r : ℕ) {k : ℕ}
  (g : Matrix (Fin k) (Fin k) (WF p n'))

def Nsub (s : Fin n') : Matrix (Fin k) (Fin k) (KK O) := fun a b =>
  if Even s.val then (if r ≤ b.val then algebraMap O (KK O) w else 1) * (sigMat p n' O g (s.val : ℤ))⁻¹ b a
  else (if b.val < r then algebraMap O (KK O) w else 1) * sigMat p n' O g (s.val : ℤ) a b

def NsubInv (s : Fin n') : Matrix (Fin k) (Fin k) (KK O) := fun b c =>
  if Even s.val then (if r ≤ b.val then (algebraMap O (KK O) w)⁻¹ else 1) * sigMat p n' O g (s.val : ℤ) c b
  else (if b.val < r then (algebraMap O (KK O) w)⁻¹ else 1) * (sigMat p n' O g (s.val : ℤ))⁻¹ b c

theorem subst_eq_Lin (f : MvPolynomial (TV n' k) (KK O)) :
    subst p n' O w n' r g f = Lin (Nsub p n' O w r g) f := by
  have key : subst p n' O w n' r g = Lin (Nsub p n' O w r g) := by
    apply MvPolynomial.algHom_ext
    intro v
    unfold subst liftSubst Lin
    rw [aeval_X, aeval_X]
    by_cases hs : Even v.1.val
    · simp only [LLT, hs, decide_true, if_true, Nsub]
      refine Finset.sum_congr rfl fun b _ => ?_
      split_ifs
      · rw [C_mul]; ring
      · rw [one_mul]; ring
    · simp only [LLT, hs, decide_false, Bool.false_eq_true, if_false, Nsub]
      refine Finset.sum_congr rfl fun b _ => ?_
      split_ifs
      · rw [C_mul]; ring
      · rw [one_mul]; ring
  rw [key]

variable {g}

theorem Nsub_mul (hw : algebraMap O (KK O) w ≠ 0) (hg : IsGLW g) (s : Fin n') :
    Nsub p n' O w r g s * NsubInv p n' O w r g s = 1 := by
  ext a c
  simp only [Matrix.mul_apply, Nsub, NsubInv, Matrix.one_apply]
  set σ := sigMat p n' O g (s.val : ℤ) with hσdef
  have hσ : IsUnit σ.det := by
    let φ : WF p n' →+* KK O := (algebraMap O (KK O)).comp ((algebraMap (WF p n') O).comp (sigPow p n' (s.val : ℤ)))
    have h1 : σ = φ.mapMatrix g := by
      ext i j
      rfl
    rw [h1, ← RingHom.map_det]
    exact hg.map φ
  by_cases hs : Even s.val
  · simp only [if_pos hs]
    have h2 : ∀ b : Fin k, (if r ≤ b.val then algebraMap O (KK O) w else 1) * σ⁻¹ b a *
        ((if r ≤ b.val then (algebraMap O (KK O) w)⁻¹ else 1) * σ c b) = σ c b * σ⁻¹ b a := by
      intro b
      split_ifs
      · field_simp
      · ring
    simp_rw [h2]
    rw [← Matrix.mul_apply, Matrix.mul_nonsing_inv _ hσ, Matrix.one_apply]
    simp [eq_comm]
  · simp only [if_neg hs]
    have h2 : ∀ b : Fin k, (if b.val < r then algebraMap O (KK O) w else 1) * σ a b *
        ((if b.val < r then (algebraMap O (KK O) w)⁻¹ else 1) * σ⁻¹ b c) = σ a b * σ⁻¹ b c := by
      intro b
      split_ifs
      · field_simp
      · ring
    simp_rw [h2]
    rw [← Matrix.mul_apply, Matrix.mul_nonsing_inv _ hσ, Matrix.one_apply]

end Sub

end Formalism.MainNotions.TestSideCounting
end
end

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.G.WittFrameLocaliserOrders
open Formalism.L2.G.Model (Lin)


set_option maxHeartbeats 1000000 in
theorem restND_of_adm (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) (hA : tableLineDegreeFive.admitted D CLa Ck Crk Cdeg) : RestND CLa := by
  have h26 : Formalism.MainNotions.SelectionLemmas.Conclusion2 D CLa Ck Crk Cdeg := hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨Cg, hCg1, hg2⟩ := symbol_space_at D CLa Ck Crk Cdeg h26
  refine ⟨max 1 |Cdeg|, max Cg |CLa|, lt_of_lt_of_le one_pos (le_max_left _ _),
    lt_of_lt_of_le (by linarith) (le_max_left _ _), ?_⟩
  intro C hC p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r _ _ TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H φ hφ K
    _ _ hk hrk F hF E' hE' nb B hB hli hc e he htgt hm g hhm hg hbasis
  have c1 : Cg ≤ C := le_trans (le_max_left _ _) hC
  have c5 : |CLa| ≤ C := le_trans (le_max_right _ _) hC
  have hBa := hyps_basic (C := C) (by linarith) H
  have ha1 : (1 : ℝ) ≤ a := by linarith [hBa.two_le_a]
  have hr2 : 2 ≤ r := H.2.1
  have hn : Even n' := hSet.1.even
  have hTT := hF.1
  subst hTT
  letI : Algebra (WF p n') O := algOfIdent j φ
  intro FsB hFsB Θ hΘ
  obtain ⟨-, hdeg⟩ := hg2 C c1 p W Qq O Kf ι σ j w n' m r F.TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H K hk F hF
    E' (fun t ht => (hE' t ht).1)
  set X : ℝ := Cdeg * (F.TT.card : ℝ) *
    (CLa * ((min (orbitWindowCount r de h x) (2 * F.TT.card) : ℕ) : ℝ) ^ 2 * Real.log a * a / ((p : ℝ) * ((r + K : ℕ) : ℝ)) +
      a * (p : ℝ) ^ (-(L₁ : ℤ)) + ((r + K : ℕ) : ℝ) * (p : ℝ) ^ goodG' r de h x) with hX
  have hT : ∀ i, ∀ mm ∈ (B i).support, vsDeg mm ≤ ⌊X⌋₊ := fun i mm hmm =>
    Nat.le_floor (hdeg (B i) (Submodule.subset_span (hB i)) mm hmm)
  have hXt : X ≤ t0 C (max 1 |Cdeg|) p F.TT.card (orbitWindowCount r de h x) L₁ (goodG' r de h x) (m + 1) a := by
    have e1 : t0 C (max 1 |Cdeg|) p F.TT.card (orbitWindowCount r de h x) L₁ (goodG' r de h x) (m + 1) a =
        t0 C (max 1 |Cdeg|) p F.TT.card (orbitWindowCount r de h x) L₁ (goodG' r de h x) (r + K) a := by rw [hk]
    rw [e1]
    exact level_lower_bound_terms Cdeg CLa C (max 1 |Cdeg|) (le_max_right _ _) c5 p F.TT.card (orbitWindowCount r de h x)
      (min (orbitWindowCount r de h x) (2 * F.TT.card)) L₁ (goodG' r de h x) (r + K) (min_le_left _ _)
      (by have := H.1; omega) (by omega) a ha1
  have ht0 : 0 ≤ t0 C (max 1 |Cdeg|) p F.TT.card (orbitWindowCount r de h x) L₁ (goodG' r de h x) (m + 1) a :=
    initial_level_nonneg (le_trans (abs_nonneg _) c5) (le_trans zero_le_one (le_max_left _ _)) _ _ _ _ _ _ ha1
  have hfl : ((⌊X⌋₊ : ℕ) : ℝ) ≤ t0 C (max 1 |Cdeg|) p F.TT.card (orbitWindowCount r de h x) L₁ (goodG' r de h x) (m + 1) a := by
    by_cases hX0 : 0 ≤ X
    · exact le_trans (Nat.floor_le hX0) hXt
    · rw [Nat.floor_of_nonpos (le_of_lt (not_le.1 hX0))]
      simpa using ht0
  have hw : algebraMap O (KK O) w ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O (KK O))).2 hSet.2.1.ne_zero
  have hbase : ∀ b, subst p n' O w n' r g (FsB b : MvPolynomial (TV n' (m + 1)) (KK O)) ∈
      NDsub (KK O) n' (m + 1) r ⌊X⌋₊ := by
    intro b
    rw [hFsB b]
    unfold symB toK
    rw [subst_SPtrue w F hF.2.1 hn (by omega) hrk hg]
    have h1 := nd_mul (nd_map (algebraMap O (KK O)) (nd_rename (n' := n') (R := O) hk (hT b)))
      (nd_map (algebraMap O (KK O)) (fixed_symbol_normal_degree_zero (R := O) p F hF.2.1 hn (by omega) hrk
        (cPrime n' r F.TT.card c0 cpp cStar) (p ^ goodG' r de h x)))
    rw [add_zero] at h1
    exact h1
  refine ⟨⌊X⌋₊ + F.TT.card * c0, ?_, ?_⟩
  · push_cast
    linarith
  · intro f hf mm hmm
    rw [subst_eq_Lin] at hmm
    refine mem_NDsub.1 (nd_OpCl (Nsub p n' O w r g) (NsubInv p n' O w r g) (Nsub_mul p n' O w r hw hg) r ⌊X⌋₊ F.TT c0 _
      ?_ f hf) mm hmm
    intro f0 hf0
    induction hf0 using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, rfl⟩ := hy
      rw [← subst_eq_Lin]
      exact hbase b
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem restXi_of_N (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CH CE C6 C18 : ℝ)
    (hN : RestXiN D CLa Ck Crk Cdeg CH CE C6 C18) : RestXi D CLa Ck Crk Cdeg CH CE C6 C18 :=
  fun hA h14b => restXi_of D CLa Ck Crk Cdeg CH CE C6 C18 hN (restND_of_adm D CLa Ck Crk Cdeg hA) hA h14b

end Formalism.MainNotions.TestSideCounting
end
end

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14
open Formalism.L2.G.Model (Lin)

section Words

variable {R : Type} [CommRing R] {n' k : ℕ}

def WSpan (l : List (Fin n' × (Fin k × Fin k))) (h : MvPolynomial (Fin n' × Fin k) R) :
    Submodule R (MvPolynomial (Fin n' × Fin k) R) :=
  Submodule.span R {y | ∃ l' : List (Fin n' × (Fin k × Fin k)), l'.map Prod.fst = l.map Prod.fst ∧ y = opWord l' h}

theorem wspan_op (l : List (Fin n' × (Fin k × Fin k))) (h : MvPolynomial (Fin n' × Fin k) R) (s : Fin n')
    (x : Fin k × Fin k) (c c' : Fin k) {z : MvPolynomial (Fin n' × Fin k) R} (hz : z ∈ WSpan l h) :
    X (s, c) * pderiv (s, c') z ∈ WSpan ((s, x) :: l) h := by
  unfold WSpan at hz ⊢
  induction hz using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l', hl', rfl⟩ := hy
    exact Submodule.subset_span ⟨(s, (c, c')) :: l', by simp [hl'], rfl⟩
  | zero => simp
  | add a b _ _ ha hb =>
    rw [map_add (f := _), mul_add]
    exact Submodule.add_mem _ ha hb
  | smul a y _ hy =>
    rw [Derivation.map_smul, mul_smul_comm]
    exact Submodule.smul_mem _ a hy

theorem Lin_word (N N' : Fin n' → Matrix (Fin k) (Fin k) R) (h : ∀ s, N s * N' s = 1)
    (f : MvPolynomial (Fin n' × Fin k) R) :
    ∀ l : List (Fin n' × (Fin k × Fin k)), Lin N (opWord l f) ∈ WSpan l (Lin N f) := by
  intro l
  induction l with
  | nil => exact Submodule.subset_span ⟨[], rfl, rfl⟩
  | cons y l ih =>
    obtain ⟨s, a, b⟩ := y
    show Lin N (X (s, a) * pderiv (s, b) (opWord l f)) ∈ _
    rw [map_mul, Lin_X, Lin_pderiv N N' h, Finset.sum_mul]
    refine Submodule.sum_mem _ fun b' _ => ?_
    rw [Finset.mul_sum]
    refine Submodule.sum_mem _ fun c _ => ?_
    rw [mul_smul_comm, MvPolynomial.C_mul', smul_mul_assoc]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (wspan_op l _ s (a, b) b' c ih))

theorem wspan_le_OpCl (TT : Finset (Fin n')) (c : ℕ) (M : Submodule R (MvPolynomial (Fin n' × Fin k) R))
    (l : List (Fin n' × (Fin k × Fin k))) (h1 : ∀ z ∈ l, z.1 ∈ TT) (h2 : ∀ s, (l.filter fun z => z.1 = s).length ≤ c)
    {h : MvPolynomial (Fin n' × Fin k) R} (hh : h ∈ M) : WSpan l h ≤ OpCl TT c M := by
  rw [WSpan, Submodule.span_le]
  rintro y ⟨l', hl', rfl⟩
  refine Submodule.subset_span ⟨h, hh, l', ?_, ?_, rfl⟩
  · intro z hz
    have hz' : z.1 ∈ l.map Prod.fst := hl' ▸ List.mem_map_of_mem hz
    obtain ⟨z', hz'', e⟩ := List.mem_map.1 hz'
    exact e ▸ h1 z' hz''
  · intro s
    have e : ∀ L : List (Fin n' × (Fin k × Fin k)), (L.filter fun z => decide (z.1 = s)).length =
        ((L.map Prod.fst).filter fun t => decide (t = s)).length := by
      intro L
      rw [List.filter_map, List.length_map]
      rfl
    rw [e, hl', ← e]
    exact h2 s

theorem Lin_OpCl (N N' : Fin n' → Matrix (Fin k) (Fin k) R) (h : ∀ s, N s * N' s = 1) (TT : Finset (Fin n')) (c : ℕ)
    (M M' : Submodule R (MvPolynomial (Fin n' × Fin k) R)) (hM : ∀ f ∈ M, Lin N f ∈ M') :
    ∀ f ∈ OpCl TT c M, Lin N f ∈ OpCl TT c M' := by
  intro f hf
  unfold OpCl at hf
  induction hf using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨f0, hf0, l, h1, h2, rfl⟩ := hy
    exact wspan_le_OpCl TT c M' l h1 h2 (hM f0 hf0) (Lin_word N N' h f0 l)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

end Words

end Formalism.MainNotions.TestSideCounting
