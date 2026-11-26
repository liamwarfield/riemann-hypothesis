module

public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.RestDimBCProved

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.BejjSmulLeft
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.GM.ProjS

section Gen

variable (p : ℕ) [Fact p.Prime] {V : Type} [AddCommGroup V] [Module ℚ_[p] V] [Module ℤ_[p] V]

theorem gc_bdd_gen (be : V → V → ℚ_[p]) (hsm : ∀ (c : ℚ_[p]) u v, be (c • u) v = c * be u v)
    (hsum : ∀ (n : ℕ) (s : Finset (Fin n)) (f : Fin n → V) v, be (∑ i ∈ s, f i) v = ∑ i ∈ s, be (f i) v)
    (L : Submodule ℤ_[p] V) (W : Submodule ℚ_[p] V) [FiniteDimensional ℚ_[p] W] (hLW : ∀ x ∈ L, x ∈ W) (D : ℤ) :
    BddAbove {n | ∃ x y : Fin n → V, (∀ i, x i ∈ L) ∧ (∀ i, y i ∈ L) ∧
      ∀ i k, be (x i) (y k) = if i = k then (p : ℚ_[p]) ^ D else 0} := by
  refine ⟨Module.finrank ℚ_[p] W, ?_⟩
  rintro n ⟨x, y, hx, hy, hxy⟩
  have hpD : (p : ℚ_[p]) ^ D ≠ 0 :=
    zpow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  have hz : ∀ v, be 0 v = 0 := by
    intro v
    simpa using hsm 0 0 v

  let x' : Fin n → W := fun i => ⟨x i, hLW _ (hx i)⟩
  have hli : LinearIndependent ℚ_[p] x' := by
    rw [linearIndependent_iff']
    intro s g hg i hi
    have hg' : ∑ j ∈ s, g j • x j = 0 := by
      have := congrArg Subtype.val hg
      simpa [x'] using this
    have h1 := congrArg (fun u => be u (y i)) hg'
    rw [hsum n s (fun j => g j • x j) (y i), hz] at h1
    simp only [hsm, hxy] at h1
    rw [Finset.sum_eq_single i] at h1
    · simpa [hpD] using h1
    · intro j _ hj
      simp [hj]
    · intro h
      exact absurd hi h
  simpa using hli.fintype_card_le_finrank

theorem bad_le_sub (be : V → V → ℚ_[p]) (L L₁ : Submodule ℤ_[p] V) (hle : L₁ ≤ L) (D : ℤ) (n₁ : ℕ)
    (hn : Module.finrank ℤ_[p] L₁ = n₁)
    (hb : BddAbove {n | ∃ x y : Fin n → V, (∀ i, x i ∈ L) ∧ (∀ i, y i ∈ L) ∧
      ∀ i k, be (x i) (y k) = if i = k then (p : ℚ_[p]) ^ D else 0}) :
    Formalism.GM.M.bad p be L D ≤ (Module.finrank ℤ_[p] L - n₁) + Formalism.GM.M.bad p be L₁ D := by
  have hgc : Formalism.GM.M.goodCount p be L₁ D ≤ Formalism.GM.M.goodCount p be L D := by
    unfold Formalism.GM.M.goodCount
    apply csSup_le_csSup hb
    · exact ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
    · rintro n ⟨x, y, hx, hy, h⟩
      exact ⟨x, y, fun i => hle (hx i), fun i => hle (hy i), h⟩
  unfold Formalism.GM.M.bad
  rw [hn]
  omega

end Gen

section Level

variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (G : Formalism.GM.M.BlockData N)

private theorem fockK_eq_lemma {k σ : Type} [Field k] (F G : MvPolynomial σ k) (s : Finset (σ →₀ ℕ))
    (hs : F.support ⊆ s) :
    Formalism.GM.M.fockK F G = ∑ m ∈ s, F.coeff m * G.coeff m * (m.prod fun _ j => (j.factorial : k)) := by
  unfold Formalism.GM.M.fockK
  apply Finset.sum_subset hs
  intro m _ hm
  have h0 : F.coeff m = 0 := by simpa using hm
  rw [h0, zero_mul, zero_mul]

theorem bejj_smul_left (j : Fin G.T.t → ℕ) (jp : ℕ) (c : ℚ_[p]) (u v : MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p]) :
    bejj p (r := r) G j jp (c • u) v = c * bejj p (r := r) G j jp u v := by
  unfold bejj
  rw [map_smul, fockK_eq_lemma _ v _ MvPolynomial.support_smul]
  unfold Formalism.GM.M.fockK
  rw [mul_div_assoc', Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  ring

theorem bejj_sum_left (j : Fin G.T.t → ℕ) (jp : ℕ) {ι : Type} (s : Finset ι)
    (f : ι → MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p]) (v : MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p]) :
    bejj p (r := r) G j jp (∑ i ∈ s, f i) v = ∑ i ∈ s, bejj p (r := r) G j jp (f i) v := by
  classical
  unfold bejj
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, ← Finset.sum_div]
  congr 1
  set S := (∑ i ∈ s, G.phiAll p (r := r) j jp (f i)).support ∪
    s.biUnion (fun i => (G.phiAll p (r := r) j jp (f i)).support) with hS
  rw [fockK_eq_lemma _ v S Finset.subset_union_left]
  rw [Finset.sum_congr rfl (fun i hi => fockK_eq_lemma (G.phiAll p (r := r) j jp (f i)) v S
    ((Finset.subset_biUnion_of_mem (fun i => (G.phiAll p (r := r) j jp (f i)).support) hi).trans
      Finset.subset_union_right))]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [MvPolynomial.coeff_sum, Finset.sum_mul, Finset.sum_mul]

theorem bejj_bdd (j : Fin G.T.t → ℕ) (jp : ℕ) (D : ℤ) :
    BddAbove {n | ∃ x y : Fin n → MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p],
      (∀ i, x i ∈ Ljj p (r := r) G j jp) ∧ (∀ i, y i ∈ Ljj p (r := r) G j jp) ∧
      ∀ i k, bejj p (r := r) G j jp (x i) (y k) = if i = k then (p : ℚ_[p]) ^ D else 0} := by
  obtain ⟨W, hW, hLW⟩ := exists_fd_Ljj p (r := r) G j jp
  haveI := hW
  exact gc_bdd_gen p (bejj p (r := r) G j jp) (bejj_smul_left p G j jp)
    (fun n s f v => bejj_sum_left p G j jp s f v) (Ljj p (r := r) G j jp) W hLW D

end Level

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

def RestOrth (CM : ℝ) : Prop :=
  ∀ dl ∈ CountingStatementReduction.clSet C0 CE1 CE2 X, ∀ aTop ∈ cbox C0 CE1 CE2 X dl, ∀ x ∈ idx C0 CE1 CE2 X dl aTop,
    ∃ (n₁ : ℕ) (e : Fin n₁ → MvPolynomial (Formalism.GM.M.BVar (2 * X.s + 1) X.r (gB C0 CE1 CE2 X aTop 0 x.1).T.t) ℚ_[X.p]),
      (∀ a, e a ∈ Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2) ∧ LinearIndependent ℤ_[X.p] e ∧
      (∀ a b, a ≠ b → bePhi X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2 (e a) (e b) = 0) ∧
      (∀ a, bePhi X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2 (e a) (e a) ≠ 0 ∧
        (bePhi X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2 (e a) (e a)).valuation ≤
          ⌊D1r C0 CE1 CE2 X CM⌋) ∧
      n₁ ≤ Module.finrank ℤ_[X.p] (Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2) ∧
      Module.finrank ℤ_[X.p] (Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2) ≤
        n₁ + Formalism.GM.M.bad X.p (bePhi X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2)
          (Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2) ⌊D1r C0 CE1 CE2 X CM⌋

def RestWin (CM : ℝ) : Prop :=
  ∀ dl ∈ CountingStatementReduction.clSet C0 CE1 CE2 X, ∀ aTop ∈ cbox C0 CE1 CE2 X dl, ∀ x ∈ idx C0 CE1 CE2 X dl aTop,
    ∀ (n₁ : ℕ) (e : Fin n₁ → MvPolynomial (Formalism.GM.M.BVar (2 * X.s + 1) X.r (gB C0 CE1 CE2 X aTop 0 x.1).T.t) ℚ_[X.p]),
      (∀ a, e a ∈ Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2) → LinearIndependent ℤ_[X.p] e →
      (∀ a b, a ≠ b → bePhi X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2 (e a) (e b) = 0) →
      (∀ a, bePhi X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2 (e a) (e a) ≠ 0 ∧
        (bePhi X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2 (e a) (e a)).valuation ≤
          ⌊D1r C0 CE1 CE2 X CM⌋) →
      (∑ aPlus ∈ X.winA, (Formalism.GM.M.bad X.p (bejj X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus x.1) x.2.1 x.2.2)
          (Submodule.span ℤ_[X.p] (Set.range e)) ⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋ : ℝ)) ≤
        (X.winA.card : ℝ) * (5 / X.L.Y * n₁)

variable {C0 CE1 CE2 X}

theorem restPlusB_of (CM : ℝ) (hY : 0 < X.L.Y) (hO : RestOrth C0 CE1 CE2 X CM) (hW : RestWin C0 CE1 CE2 X CM) :
    RestPlusB C0 CE1 CE2 X CM := by
  intro dl hdl aTop haTop x hx
  obtain ⟨n₁, e, he, hli, horth, hval, hn1, hrk⟩ := hO dl hdl aTop haTop x hx
  have hwin := hW dl hdl aTop haTop x hx n₁ e he hli horth hval
  have hspan : Submodule.span ℤ_[X.p] (Set.range e) ≤
      Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2 :=
    Submodule.span_le.2 (by
      rintro _ ⟨a, rfl⟩
      exact he a)
  have hrank : Module.finrank ℤ_[X.p] (Submodule.span ℤ_[X.p] (Set.range e)) = n₁ := by
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  have hstep : ∀ aPlus ∈ X.winA, (bLvl C0 CE1 CE2 X aTop aPlus x.1 x.2 ⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋ : ℝ) ≤
      ((Module.finrank ℤ_[X.p] (Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2) - n₁ : ℕ) : ℝ) +
        (Formalism.GM.M.bad X.p (bejj X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus x.1) x.2.1 x.2.2)
          (Submodule.span ℤ_[X.p] (Set.range e)) ⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋ : ℝ) := by
    intro aPlus _
    have h := bad_le_sub X.p (bejj X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus x.1) x.2.1 x.2.2)
      (Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus x.1) x.2.1 x.2.2)
      (Submodule.span ℤ_[X.p] (Set.range e)) hspan ⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋ n₁ hrank
      (bejj_bdd X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus x.1) x.2.1 x.2.2 _)
    have h' : bLvl C0 CE1 CE2 X aTop aPlus x.1 x.2 ⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋ ≤
        (Module.finrank ℤ_[X.p] (Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2) - n₁) +
          Formalism.GM.M.bad X.p (bejj X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus x.1) x.2.1 x.2.2)
            (Submodule.span ℤ_[X.p] (Set.range e)) ⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋ := h
    exact_mod_cast h'
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  have h1 : ((Module.finrank ℤ_[X.p] (Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2) - n₁ : ℕ) : ℝ) ≤
      (Formalism.GM.M.bad X.p (bePhi X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2)
        (Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2) ⌊D1r C0 CE1 CE2 X CM⌋ : ℝ) := by
    exact_mod_cast (by omega)
  have hc : (0 : ℝ) ≤ 5 / X.L.Y := div_nonneg (by norm_num) hY.le
  have h2 : 5 / X.L.Y * (n₁ : ℝ) ≤ 5 / X.L.Y *
      (Module.finrank ℤ_[X.p] (Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2) : ℝ) :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast hn1) hc
  have hcard : (0 : ℝ) ≤ (X.winA.card : ℝ) := Nat.cast_nonneg _
  have h3 := mul_le_mul_of_nonneg_left h1 hcard
  have h4 := mul_le_mul_of_nonneg_left h2 hcard
  nlinarith [hwin, h3, h4]

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.BlockValuationOverZpHolds
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

theorem loss_num (s t r Λ L1 U k0 : ℝ) (ht0 : 0 ≤ t) (hts : t ≤ s) (hr : 4 ≤ r) (hΛ : 1 ≤ Λ) (hL0 : 0 ≤ L1)
    (hL : L1 ≤ Λ) (hU : U ≤ (t + 1) * ((r + 1) * (Λ + 1) + 1)) (hk : 0 ≤ k0) :
    ((((2 * s + 1) + 1) * r + (t + 1) * 2) + (t + 1)) * L1 + 2 * U ≤ 10 * (s + 1) * (r + 1) * Λ + k0 := by
  have hs0 : 0 ≤ s := le_trans ht0 hts
  have hA : 0 ≤ (((2 * s + 1) + 1) * r + (t + 1) * 2) + (t + 1) := by nlinarith
  have e1 : ((((2 * s + 1) + 1) * r + (t + 1) * 2) + (t + 1)) * L1 ≤
      ((2 * s + 2) * r + 3 * (s + 1)) * Λ := by
    calc ((((2 * s + 1) + 1) * r + (t + 1) * 2) + (t + 1)) * L1
        ≤ ((((2 * s + 1) + 1) * r + (t + 1) * 2) + (t + 1)) * Λ := mul_le_mul_of_nonneg_left hL hA
      _ ≤ ((2 * s + 2) * r + 3 * (s + 1)) * Λ := by nlinarith
  have e2 : U ≤ (s + 1) * ((r + 1) * (Λ + 1) + 1) := by
    have : 0 ≤ (r + 1) * (Λ + 1) + 1 := by nlinarith
    nlinarith
  have e3 : (s + 1) * ((r + 1) * (Λ + 1) + 1) ≤ (s + 1) * ((2 * r + 3) * Λ) := by
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    nlinarith
  nlinarith

section Inst

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

theorem restValNum_proved {CYb Cde Ck CD Cb Cc : ℝ} (hCYb : 1 ≤ CYb) (hCE1 : 0 ≤ CE1) (hCE2 : 0 ≤ CE2)
    (hH : flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X) : RestValNum C0 CE1 CE2 X := by
  classical
  intro aTop hT aPlus hP b hK l hl j' jp' hl' μ hw
  obtain ⟨hA1, h2, h3, h4, h5⟩ := gB_deg_le C0 CE1 CE2 X hCYb hCE1 hCE2 hH aTop hT aPlus hP b hK
  have hF := hiFacts C0 CYb Cde Ck CD Cb Cc X hCYb hH
  have hlok : (gB C0 CE1 CE2 X aTop aPlus b).LevelOK l.1 l.2 := (Finset.mem_filter.1 hl).2
  have hv := val_gen X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b) (gB_blockOK C0 CE1 CE2 X aTop aPlus b) (aBig X)
    h2 h3 h4 h5 l.1 l.2 hlok j' jp' hl' μ hw
  have hvR : (padicValNat X.p (lvC (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b) l.1 l.2 *
      degFact (gB C0 CE1 CE2 X aTop aPlus b) l.1 l.2) : ℝ) ≤
      (padicValNat X.p (μ.prod fun _ k => k.factorial) : ℝ) +
        (((((2 * (X.s : ℝ) + 1) + 1) * (X.r : ℝ) + (((X.S C0 CE1 CE2).t : ℝ) + 1) * 2) +
          (((X.S C0 CE1 CE2).t : ℝ) + 1)) * (Nat.log X.p (8 * aBig X + X.r) : ℝ)) := by
    have := (Nat.cast_le (α := ℝ)).2 hv
    push_cast at this
    exact this

  have hmR : (4 : ℝ) ≤ (X.r : ℝ) := by exact_mod_cast hF.m4
  have hp25 : (25 : ℝ) ≤ (X.p : ℝ) := by nlinarith [hF.p_ge]
  have hp1 : (1 : ℝ) < (X.p : ℝ) := by linarith
  have hs0 : (0 : ℝ) ≤ (X.s : ℝ) := Nat.cast_nonneg _
  have ha1 : (1 : ℝ) ≤ (X.L.a : ℝ) := hF.a1
  have hsm : 2 * (X.s : ℝ) + 2 ≤ (X.r : ℝ) := by exact_mod_cast hF.s_le
  have hsp : 3 * (X.s : ℝ) + 2 ≤ (X.p : ℝ) := by nlinarith [hF.p_ge]
  have hbase : (0 : ℝ) < 8 * (X.L.a : ℝ) + (X.r : ℝ) := by linarith
  have hΛ : 1 ≤ lgA X.p X.L.a X.r := by
    unfold lgA
    have : 0 ≤ Real.logb X.p (8 * (X.L.a : ℝ) + (X.r : ℝ)) := Real.logb_nonneg hp1 (by linarith)
    linarith
  have hbig : Real.logb X.p (8 * (aBig X : ℝ) + (X.r : ℝ)) ≤ lgA X.p X.L.a X.r := by
    have e1 : 8 * (aBig X : ℝ) + (X.r : ℝ) ≤ (3 * (X.s : ℝ) + 2) * (8 * (X.L.a : ℝ) + (X.r : ℝ)) := by
      unfold aBig; push_cast; nlinarith
    have e0 : (0 : ℝ) < 8 * (aBig X : ℝ) + (X.r : ℝ) := by
      have : (0 : ℝ) ≤ (aBig X : ℝ) := Nat.cast_nonneg _
      linarith
    have e2 := Real.logb_le_logb_of_le hp1 e0 e1
    rw [Real.logb_mul (by linarith) hbase.ne'] at e2
    have e3 : Real.logb X.p (3 * (X.s : ℝ) + 2) ≤ 1 := by
      rw [Real.logb_le_iff_le_rpow hp1 (by linarith), Real.rpow_one]
      exact hsp
    unfold lgA
    linarith
  have hL1 : (Nat.log X.p (8 * aBig X + X.r) : ℝ) ≤ lgA X.p X.L.a X.r := by
    have := Real.natLog_le_logb (8 * aBig X + X.r) X.p
    push_cast at this
    exact this.trans hbig
  have hU : (expU X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b) (aBig X) : ℝ) ≤
      (((X.S C0 CE1 CE2).t : ℝ) + 1) * (((X.r : ℝ) + 1) * (lgA X.p X.L.a X.r + 1) + 1) := by
    have e1 : (expU X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b) (aBig X) : ℝ) =
        (((X.S C0 CE1 CE2).t : ℝ) + 1) * (⌈((X.r : ℝ) + 1) * Formalism.GM.lgV2 X.p (aBig X) X.r⌉₊ : ℝ) := by
      unfold expU
      push_cast
      rfl
    rw [e1]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have e2 : Formalism.GM.lgV2 X.p (aBig X) X.r ≤ lgA X.p X.L.a X.r + 1 := by
      unfold Formalism.GM.lgV2
      linarith
    have e3 : 0 ≤ Formalism.GM.lgV2 X.p (aBig X) X.r := by
      unfold Formalism.GM.lgV2
      have : 0 ≤ Real.logb X.p (8 * (aBig X : ℝ) + (X.r : ℝ)) := by
        apply Real.logb_nonneg hp1
        have : (0 : ℝ) ≤ (aBig X : ℝ) := Nat.cast_nonneg _
        linarith
      linarith
    have e4 := (Nat.ceil_lt_add_one (show 0 ≤ ((X.r : ℝ) + 1) * Formalism.GM.lgV2 X.p (aBig X) X.r by positivity)).le
    refine e4.trans ?_
    have : ((X.r : ℝ) + 1) * Formalism.GM.lgV2 X.p (aBig X) X.r ≤ ((X.r : ℝ) + 1) * (lgA X.p X.L.a X.r + 1) :=
      mul_le_mul_of_nonneg_left e2 (by positivity)
    linarith
  have hk0 : 0 ≤ kappaZeroExponent X.p X.L.a X.Nt X.r := by
    unfold kappaZeroExponent
    have : 0 ≤ Real.logb X.p (X.L.a : ℝ) := Real.logb_nonneg hp1 ha1
    positivity
  have hts : ((X.S C0 CE1 CE2).t : ℝ) ≤ (X.s : ℝ) := by
    have : (X.S C0 CE1 CE2).t ≤ X.s := Nat.sub_le _ _
    exact_mod_cast this
  have hfin := loss_num (X.s : ℝ) ((X.S C0 CE1 CE2).t : ℝ) (X.r : ℝ) (lgA X.p X.L.a X.r)
    (Nat.log X.p (8 * aBig X + X.r) : ℝ) (expU X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b) (aBig X) : ℝ)
    (kappaZeroExponent X.p X.L.a X.Nt X.r) (Nat.cast_nonneg _) hts hmR hΛ (Nat.cast_nonneg _) hL1 hU hk0
  unfold levelPassageLoss
  linarith

theorem block_valuation_over_Zp_holds {CYb Cde Ck CD Cb Cc : ℝ} (hCYb : 1 ≤ CYb) (hCE1 : 0 ≤ CE1) (hCE2 : 0 ≤ CE2)
    (hH : flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X) : BlockBoundIntegers C0 CE1 CE2 X :=
  block_valuation_Zp_of_numeric_bound C0 CE1 CE2 X hCYb hCE1 hCE2 hH (restValNum_proved C0 CE1 CE2 X hCYb hCE1 hCE2 hH)

end Inst

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.RestDecompProved
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G

def cmap {K L σ : Type} [CommRing K] [CommRing L] (f : K →+ L) (y : MvPolynomial σ K) : MvPolynomial σ L :=
  ∑ m ∈ y.support, monomial m (f (y.coeff m))

def RestFunY : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] (p : ℕ) [Fact p.Prime] (ι : ℚ_[p] →+* KK O) (N r : ℕ) [NeZero r]
    (LL : ChainLetters N) (q : ℕ) (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (f : KK O →+ ℚ_[p]),
    (∀ (a : ℚ_[p]) (x : KK O), f (ι a * x) = a * f x) →
    ∀ y ∈ Yjt (KK O) (r := r) LL J M, cmap f y ∈ Formalism.GM.M.Y p (r := r) (Formalism.MainNotions.G.SymmetricFormBlocks.gmL LL) J M

def RestDecomp : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] (p : ℕ) [Fact p.Prime] (ι : ℚ_[p] →+* KK O) (σ : Type)
    (y : MvPolynomial σ (KK O)),
    ∃ (n : ℕ) (b : Fin n → KK O) (f : Fin n → (KK O →+ ℚ_[p])),
      (∀ k (a : ℚ_[p]) (x : KK O), f k (ι a * x) = a * f k x) ∧
      y = ∑ k, b k • map ι (cmap (f k) y)

def RestClear : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero r] (LL : Formalism.GM.M.Letters N) (q : ℕ) (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ), ∀ F ∈ Formalism.GM.M.Y p (r := r) LL J M,
      ∃ e : ℕ, ((p : ℚ_[p]) ^ e) • F ∈ Formalism.GM.M.YZ p (r := r) LL J M

theorem restClear_proved : RestClear := by
  intro p _ N r _ LL q J M F hF
  classical
  obtain ⟨e, he⟩ : ∃ e : ℕ, ∀ m, ‖(p : ℚ_[p]) ^ e * F.coeff m‖ ≤ 1 := by
    set B : ℝ := ∑ m ∈ F.support, ‖F.coeff m‖ with hB
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    obtain ⟨e, he⟩ := pow_unbounded_of_one_lt B hp1
    refine ⟨e, fun m => ?_⟩
    rw [norm_mul, Padic.norm_p_pow]
    have hcm : ‖F.coeff m‖ ≤ B := by
      by_cases hm : m ∈ F.support
      · exact Finset.single_le_sum (f := fun m => ‖F.coeff m‖) (fun _ _ => norm_nonneg _) hm
      · rw [MvPolynomial.notMem_support_iff.1 hm, norm_zero]
        exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    have hp0 : (0 : ℝ) < (p : ℝ) ^ e := by positivity
    rw [zpow_neg, zpow_natCast, inv_mul_le_iff₀ hp0, mul_one]
    linarith
  refine ⟨e, ?_⟩
  have hY : ((p : ℚ_[p]) ^ e) • F ∈ Formalism.GM.M.Y p (r := r) LL J M := Submodule.smul_mem _ _ hF
  have hPol : ((p : ℚ_[p]) ^ e) • F ∈ Formalism.GM.M.Pol p r LL := (Submodule.mem_inf.1 hY).1
  have hInt : ((p : ℚ_[p]) ^ e) • F ∈ Formalism.GM.M.IntPol p (Fin N × Fin r) := by
    have hr : ((p : ℚ_[p]) ^ e) • F ∈ Set.range (MvPolynomial.map (algebraMap ℤ_[p] ℚ_[p])) := by
      rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
      intro c hc
      obtain ⟨m, -, rfl⟩ : ∃ m ∈ (((p : ℚ_[p]) ^ e) • F).support, c = (((p : ℚ_[p]) ^ e) • F).coeff m := by
        simpa [MvPolynomial.coeffs, eq_comm] using hc
      rw [MvPolynomial.coeff_smul, smul_eq_mul]
      exact ⟨⟨_, he m⟩, rfl⟩
    obtain ⟨G, hG⟩ := hr
    exact ⟨G, hG⟩
  exact Submodule.mem_inf.2 ⟨hY, Submodule.mem_inf.2 ⟨hPol, hInt⟩⟩

theorem restYbc_of (hF : RestFunY) (hD : RestDecomp) (hC : RestClear) : RestYbc := by
  intro O _ _ p _ ι N r _ LL q J M y hy
  have hyK : y ∈ Yjt (KK O) (r := r) LL J M := hy.1
  obtain ⟨n, b, f, hf, hdec⟩ := hD O p ι _ y
  rw [hdec]
  refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_
  have h1 := hF O p ι N r LL q J M (f k) (hf k) y hyK
  obtain ⟨e, he⟩ := hC p N r (gmL LL) q J M _ h1
  have hp0 : ((p : ℚ_[p]) ^ e) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  have e1 : map ι (cmap (f k) y) = (ι ((p : ℚ_[p]) ^ e))⁻¹ • map ι (((p : ℚ_[p]) ^ e) • cmap (f k) y) := by
    rw [MvPolynomial.smul_eq_C_mul (a := (ι ((p : ℚ_[p]) ^ e))⁻¹), MvPolynomial.smul_eq_C_mul (a := (p : ℚ_[p]) ^ e), map_mul,
      map_C, ← mul_assoc, ← C_mul, inv_mul_cancel₀ ((map_ne_zero ι).2 hp0), C_1, one_mul]
  rw [e1]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, he, rfl⟩)

theorem coeff_cmap {K L σ : Type} [CommRing K] [CommRing L] (f : K →+ L) (y : MvPolynomial σ K) (m : σ →₀ ℕ) :
    AddMonoidAlgebra.coeff (cmap f y) m = f (y.coeff m) := by
  classical
  unfold cmap
  rw [coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [MvPolynomial.notMem_support_iff.1 h, map_zero]

theorem restDecomp_proved : RestDecomp := by
  intro O _ _ p _ ι σ y
  classical
  letI : Algebra ℚ_[p] (KK O) := ι.toAlgebra
  let V : Submodule ℚ_[p] (KK O) := Submodule.span ℚ_[p] (y.coeffs : Set (KK O))
  let bV := Module.finBasis ℚ_[p] V
  obtain ⟨rV, hrV⟩ := LinearMap.exists_leftInverse_of_injective V.subtype V.ker_subtype
  refine ⟨Module.finrank ℚ_[p] V, fun k => (bV k : KK O),
    fun k => ((bV.coord k).comp rV).toAddMonoidHom, ?_, ?_⟩
  · intro k a x
    have hx : ι a * x = a • x := by rw [Algebra.smul_def]; rfl
    show ((bV.coord k).comp rV) (ι a * x) = a * ((bV.coord k).comp rV) x
    rw [hx, map_smul, smul_eq_mul]
  · ext m
    have hc : y.coeff m ∈ V := by
      by_cases h0 : y.coeff m = 0
      · rw [h0]; exact V.zero_mem
      · exact Submodule.subset_span (MvPolynomial.coeff_mem_coeffs _ h0)
    have hrc : rV (y.coeff m) = ⟨y.coeff m, hc⟩ := by
      have := LinearMap.congr_fun hrV ⟨y.coeff m, hc⟩
      simpa using this
    rw [MvPolynomial.coeff_sum]
    simp only [MvPolynomial.coeff_smul, MvPolynomial.coeff_map, coeff_cmap, smul_eq_mul]
    have hsum := congrArg Subtype.val (bV.sum_repr ⟨y.coeff m, hc⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hsum
    conv_lhs => rw [← hsum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    show (bV.repr ⟨y.coeff m, hc⟩ k) • (bV k : KK O) = (bV k : KK O) * ι ((bV.coord k) (rV (y.coeff m)))
    rw [hrc, Module.Basis.coord_apply, Algebra.smul_def, mul_comm]
    rfl

theorem restYbc_of_funY (hF : RestFunY) : RestYbc := restYbc_of hF restDecomp_proved restClear_proved

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.MemLevelsIff
section -- merged from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.FinrankSpanImageLe
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.G.CountingStatementReduction

section Dim

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem xi_span (ι : ℚ_[p] →+* KK O) {N r t b : ℕ} (g : MvPolynomial (BVar N r t) (KK O))
    (hg : g ∈ XiPolZ O N r t b) :
    g ∈ Submodule.span (KK O) (map ι '' (Formalism.GM.M.XiPolZ p N r t b : Set (MvPolynomial (Formalism.GM.M.BVar N r t) ℚ_[p]))) := by
  classical
  rw [g.as_sum]
  refine Submodule.sum_mem _ fun μ hμ => ?_
  have hsupp := ((mem_restrictSupport_iff _).1 hg.1) (Finset.mem_coe.2 hμ)
  have h1 : monomial μ (1 : ℚ_[p]) ∈ Formalism.GM.M.XiPolZ p N r t b := by
    refine ⟨?_, ⟨monomial μ 1, by simp⟩⟩
    show monomial μ (1 : ℚ_[p]) ∈ restrictSupport ℚ_[p] _
    rw [mem_restrictSupport_iff]
    intro m hm
    have : m = μ := by
      have := support_monomial_subset hm
      simpa using this
    rw [this]
    exact hsupp
  have h2 : monomial μ (g.coeff μ) = g.coeff μ • map ι (monomial μ (1 : ℚ_[p])) := by
    rw [map_monomial, map_one, smul_monomial, smul_eq_mul, mul_one]
  rw [h2]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, h1, rfl⟩)

theorem finrank_span_image_le (ι : ℚ_[p] →+* KK O) {V₁ V₂ : Type} [AddCommGroup V₁] [Module ℚ_[p] V₁]
    [AddCommGroup V₂] [Module (KK O) V₂] (f : V₁ → V₂) (hadd : ∀ u v, f (u + v) = f u + f v)
    (hsm : ∀ (c : ℚ_[p]) u, f (c • u) = ι c • f u) (W : Submodule ℚ_[p] V₁) [FiniteDimensional ℚ_[p] W] :
    Module.finrank (KK O) (Submodule.span (KK O) (f '' (W : Set V₁))) ≤ Module.finrank ℚ_[p] W := by
  classical
  set bW := Module.finBasis ℚ_[p] W
  have h0 : f 0 = 0 := by
    have := hsm 0 0
    rwa [zero_smul, map_zero, zero_smul] at this
  have hsum : ∀ (s : Finset (Fin (Module.finrank ℚ_[p] W))) (c : Fin (Module.finrank ℚ_[p] W) → ℚ_[p]),
      f (∑ i ∈ s, c i • (bW i : V₁)) = ∑ i ∈ s, ι (c i) • f (bW i) := by
    intro s c
    induction s using Finset.induction_on with
    | empty => simp [h0]
    | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, hadd, hsm, ih]
  have hle : Submodule.span (KK O) (f '' (W : Set V₁)) ≤
      Submodule.span (KK O) (Set.range fun i => f (bW i)) := by
    rw [Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    have hw' : (⟨w, hw⟩ : W) = ∑ i, (bW.repr ⟨w, hw⟩ i) • bW i := (bW.sum_repr _).symm
    have hw'' : w = ∑ i, (bW.repr ⟨w, hw⟩ i) • (bW i : V₁) := by
      have h3 := congrArg (Submodule.subtype W) hw'
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum] at h3
      simpa only [Submodule.subtype_apply, map_smul] using h3
    rw [hw'', hsum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  haveI : FiniteDimensional (KK O) (Submodule.span (KK O) (Set.range fun i => f (bW i))) :=
    FiniteDimensional.span_of_finite (KK O) (Set.finite_range _)
  calc Module.finrank (KK O) (Submodule.span (KK O) (f '' (W : Set V₁)))
      ≤ Module.finrank (KK O) (Submodule.span (KK O) (Set.range fun i => f (bW i))) := Submodule.finrank_mono hle
    _ ≤ Fintype.card (Fin (Module.finrank ℚ_[p] W)) := finrank_range_le_card _
    _ = Module.finrank ℚ_[p] W := Fintype.card_fin _

theorem finrank_biSup_le {K V ι : Type} [Field K] [AddCommGroup V] [Module K V] (U : ι → Submodule K V)
    (s : Finset ι) (hU : ∀ i ∈ s, FiniteDimensional K (U i)) :
    FiniteDimensional K (⨆ i ∈ s, U i : Submodule K V) ∧
      Module.finrank K (⨆ i ∈ s, U i : Submodule K V) ≤ ∑ i ∈ s, Module.finrank K (U i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [show (⨆ i ∈ (∅ : Finset ι), U i) = (⊥ : Submodule K V) by simp]
    exact ⟨inferInstance, by simp⟩
  | insert a s ha ih =>
    obtain ⟨h1, h2⟩ := ih fun i hi => hU i (Finset.mem_insert_of_mem hi)
    have ha' := hU a (Finset.mem_insert_self a s)
    rw [Finset.iSup_insert, Finset.sum_insert ha]
    refine ⟨Submodule.finiteDimensional_sup _ _, ?_⟩
    exact (Submodule.finrank_add_le_finrank_add_finrank _ _).trans (Nat.add_le_add_left h2 _)

end Dim

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

theorem mem_levels_iff' {N : ℕ} (G : Formalism.GM.M.BlockData N) (x : (Fin G.T.t → ℕ) × ℕ) :
    x ∈ levels G ↔ G.LevelOK x.1 x.2 := by
  unfold levels
  simp only [Finset.mem_filter, Finset.mem_product, Fintype.mem_piFinset, Finset.mem_range]
  refine ⟨fun h => h.2, fun h => ⟨⟨fun i => ?_, ?_⟩, h⟩⟩
  · have hle := Finset.single_le_sum (s := Finset.univ) (f := fun a => G.LL.deg a)
      (fun a _ => Nat.zero_le _) (Finset.mem_univ (⟨min (G.T.pos i) (N - 1), by
        rcases Nat.eq_zero_or_pos N with h0 | h0
        · exact absurd G.uPos.2 (by omega)
        · omega⟩ : Fin N))
    have h1 := (h.1 i).1
    omega
  · have h2 := h.2
    have h3 := min_le_right (G.LL.deg G.uPos) G.B
    omega

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

def RestBClvl : Prop :=
  ∀ aTop ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA), ∀ aPlus ∈ X.winA,
    ∀ b, Kept X.p X.r (X.S C0 CE1 CE2) aTop b → ∀ l ∈ lv C0 CE1 CE2 X aTop b,
      Module.finrank (KK X.O) (Submodule.span (KK X.O)
        ((blockData X.p (X.S C0 CE1 CE2) aTop aPlus X.m b).gens X.O (r := X.r) l.1 l.2)) ≤
      Module.finrank ℤ_[X.p] (Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b) l.1 l.2)

theorem restBCdim_of (h : RestBClvl C0 CE1 CE2 X) : RestBCdim C0 CE1 CE2 X := by
  intro aTop hT aPlus hP b hk
  rw [finrank_blockLat X.O X.p X.r (Formalism.MainNotions.G.GLWeightTheory.valuation_properties_hold X.std.1.prime X.setting) (X.S C0 CE1 CE2) aTop aPlus X.m b]
  unfold blockRank
  simp only
  set D := blockData X.p (X.S C0 CE1 CE2) aTop aPlus X.m b with hD
  have hU : Submodule.span (KK X.O) ((D.SSZ X.O (r := X.r) : Submodule X.O _) :
        Set (MvPolynomial (BVar (2 * X.s + 1) X.r D.T.t) (KK X.O))) ≤
      ⨆ l ∈ lv C0 CE1 CE2 X aTop b, Submodule.span (KK X.O) (D.gens X.O (r := X.r) l.1 l.2) := by
    rw [Submodule.span_le]
    intro x hx
    have hx' : x ∈ Submodule.span X.O (⋃ (j : Fin D.T.t → ℕ) (jp : ℕ) (_ : D.LevelOK j jp), D.gens X.O (r := X.r) j jp) := hx
    refine Submodule.span_induction (p := fun x _ => x ∈ ⨆ l ∈ lv C0 CE1 CE2 X aTop b,
        Submodule.span (KK X.O) (D.gens X.O (r := X.r) l.1 l.2)) ?_ ?_ ?_ ?_ hx'
    · intro y hy
      simp only [Set.mem_iUnion] at hy
      obtain ⟨j, jp, hl, hy⟩ := hy
      have hmem : ((j, jp) : Lv C0 CE1 CE2 X) ∈ lv C0 CE1 CE2 X aTop b := by
        exact (mem_levels_iff' (gB C0 CE1 CE2 X aTop 0 b) (j, jp)).2 hl
      exact (le_iSup₂ (f := fun (l : Lv C0 CE1 CE2 X) (_ : l ∈ lv C0 CE1 CE2 X aTop b) =>
        Submodule.span (KK X.O) (D.gens X.O (r := X.r) l.1 l.2)) (j, jp) hmem) (Submodule.subset_span hy)
    · exact Submodule.zero_mem _
    · intro x y _ _ hx hy
      exact Submodule.add_mem _ hx hy
    · intro a x _ hx
      rw [algebra_compatible_smul (KK X.O) a x]
      exact Submodule.smul_mem _ _ hx
  have := span_SSZ_finite (O := X.O) (r := X.r) D
  have hfd : ∀ l ∈ lv C0 CE1 CE2 X aTop b,
      FiniteDimensional (KK X.O) (Submodule.span (KK X.O) (D.gens X.O (r := X.r) l.1 l.2)) := by
    intro l hl
    have hsub : Submodule.span (KK X.O) (D.gens X.O (r := X.r) l.1 l.2) ≤
        Submodule.span (KK X.O) ((D.SSZ X.O (r := X.r) : Submodule X.O _) :
          Set (MvPolynomial (BVar (2 * X.s + 1) X.r D.T.t) (KK X.O))) := by
      apply Submodule.span_mono
      intro y hy
      apply Submodule.subset_span
      refine Set.mem_iUnion.2 ⟨l.1, Set.mem_iUnion.2 ⟨l.2, Set.mem_iUnion.2 ⟨?_, hy⟩⟩⟩
      exact (mem_levels_iff' (gB C0 CE1 CE2 X aTop 0 b) l).1 hl
    exact Submodule.finiteDimensional_of_le hsub
  obtain ⟨hfd2, hle⟩ := finrank_biSup_le (fun l : Lv C0 CE1 CE2 X =>
    Submodule.span (KK X.O) (D.gens X.O (r := X.r) l.1 l.2)) (lv C0 CE1 CE2 X aTop b) hfd
  calc Module.finrank (KK X.O) (Submodule.span (KK X.O) ((D.SSZ X.O (r := X.r) : Submodule X.O _) :
          Set (MvPolynomial (BVar (2 * X.s + 1) X.r D.T.t) (KK X.O))))
      ≤ Module.finrank (KK X.O) (⨆ l ∈ lv C0 CE1 CE2 X aTop b,
          Submodule.span (KK X.O) (D.gens X.O (r := X.r) l.1 l.2) : Submodule (KK X.O) _) :=
        Submodule.finrank_mono hU
    _ ≤ ∑ l ∈ lv C0 CE1 CE2 X aTop b, Module.finrank (KK X.O) (Submodule.span (KK X.O) (D.gens X.O (r := X.r) l.1 l.2)) :=
        hle
    _ ≤ ∑ l ∈ lv C0 CE1 CE2 X aTop b,
          Module.finrank ℤ_[X.p] (Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b) l.1 l.2) :=
        Finset.sum_le_sum fun l hl => h aTop hT aPlus hP b hk l hl

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end
