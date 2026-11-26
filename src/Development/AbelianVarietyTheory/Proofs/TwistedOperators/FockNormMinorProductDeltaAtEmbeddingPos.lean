module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockNormMinorProductDeltaAtEmbeddingPos
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockNormMinorProductDeltaAtEmbeddingPos
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockDelta

variable {D : D7}

theorem minor_ne_zero {m n : ℕ} (τ : D.what₂.Tau) (a b k : ℕ) (ha : a + k ≤ m) (hb : b + k ≤ n) :
    (Matrix.of fun α β : Fin k =>
      (varF τ (a + (β : ℕ)) (b + (α : ℕ)) : MvPolynomial (FVar D m n) ℂ)).det ≠ 0 := by
  intro h
  have hev := congrArg (MvPolynomial.eval fun y : FVar D m n =>
    if (y.2.1 : ℕ) + b = (y.2.2 : ℕ) + a then (1 : ℂ) else 0) h
  rw [RingHom.map_det, map_zero] at hev
  have hI : (MvPolynomial.eval fun y : FVar D m n =>
      if (y.2.1 : ℕ) + b = (y.2.2 : ℕ) + a then (1 : ℂ) else 0).mapMatrix
      (Matrix.of fun α β : Fin k => (varF τ (a + (β : ℕ)) (b + (α : ℕ)) : MvPolynomial (FVar D m n) ℂ)) = 1 := by
    ext α β
    have hα := α.isLt
    have hβ := β.isLt
    have hc : a + (β : ℕ) < m ∧ b + (α : ℕ) < n := ⟨by omega, by omega⟩
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.one_apply]
    unfold varF
    rw [dite_eq_left hc, MvPolynomial.eval_X]
    dsimp only
    split_ifs with h1 h2 h2
    · rfl
    · exact (h2 (Fin.ext (by omega))).elim
    · exact (h1 (by subst h2; omega)).elim
    · rfl
  rw [hI, Matrix.det_one] at hev
  exact one_ne_zero hev

theorem minorPlus_ne_zero {m n : ℕ} (τ : D.what₂.Tau) (k : ℕ) (hm : k ≤ m) (hn : k ≤ n) :
    (minorPlus τ k : MvPolynomial (FVar D m n) ℂ) ≠ 0 := by
  unfold minorPlus
  have h := minor_ne_zero (D := D) (m := m) (n := n) τ 0 0 k (by omega) (by omega)
  simpa only [zero_add] using h

theorem minorMinus_ne_zero {m n : ℕ} (τ : D.what₂.Tau) (p k : ℕ) (hm : p + k ≤ m) (hn : k ≤ n) :
    (minorMinus τ p k : MvPolynomial (FVar D m n) ℂ) ≠ 0 := by
  unfold minorMinus
  exact minor_ne_zero τ p (n - k) k hm (by omega)

theorem deltaAt_ne_zero {m n : ℕ} (τ : D.what₂.Tau) (p : ℕ) (ap : ℕ → ℕ) (q : ℕ) (am : ℕ → ℕ)
    (hpq : p + q ≤ m) (hmn : m ≤ n) :
    (deltaAt τ p ap q am : MvPolynomial (FVar D m n) ℂ) ≠ 0 := by
  unfold deltaAt
  refine mul_ne_zero ?_ ?_
  · refine Finset.prod_ne_zero_iff.mpr fun i hi => pow_ne_zero _ (minorPlus_ne_zero τ (i + 1) ?_ ?_)
    · have := Finset.mem_range.mp hi
      omega
    · have := Finset.mem_range.mp hi
      omega
  · refine Finset.prod_ne_zero_iff.mpr fun i hi => pow_ne_zero _ (minorMinus_ne_zero τ p (i + 1) ?_ ?_)
    · have := Finset.mem_range.mp hi
      omega
    · have := Finset.mem_range.mp hi
      omega

theorem delta_ne_zero {m n : ℕ} (p q : D.what₂.Tau → ℕ) (ap am : D.what₂.Tau → ℕ → ℕ)
    (hpq : ∀ τ, p τ + q τ ≤ m) (hmn : m ≤ n) :
    (delta p q ap am : MvPolynomial (FVar D m n) ℂ) ≠ 0 := by
  unfold delta
  exact Finset.prod_ne_zero_iff.mpr fun τ _ => deltaAt_ne_zero τ _ _ _ _ (hpq τ) hmn

theorem fock_self_pos {σ : Type*} (P : MvPolynomial σ ℂ) (hP : P ≠ 0) :
    ∃ a : ℝ, 0 < a ∧ Formalism.E.fock P P = (a : ℂ) := by
  refine ⟨∑ m ∈ P.support, Complex.normSq (P.coeff m) * (Formalism.A.mfact m : ℝ), ?_, ?_⟩
  · refine Finset.sum_pos (fun m hm => mul_pos ?_ ?_) ?_
    · exact Complex.normSq_pos.mpr (MvPolynomial.mem_support_iff.mp hm)
    · unfold Formalism.A.mfact
      exact Nat.cast_pos.mpr (Finset.prod_pos fun i _ => Nat.factorial_pos _)
    · exact Finset.nonempty_iff_ne_empty.mpr fun he => hP (MvPolynomial.support_eq_empty.mp he)
  · unfold Formalism.E.fock
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Complex.ofReal_mul, Complex.star_def, Complex.mul_conj, Complex.ofReal_natCast]

end GlobalTheory.FockDelta


open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues in
theorem GlobalTheory.FockDelta.fock_deltaAtEmb_pos :
    ∀ (D : D7) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), ∃ a : ℝ, 0 < a ∧
      Formalism.E.fock (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.deltaAtEmb D i σ) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.deltaAtEmb D i σ) = (a : ℂ) := by
  intro D i σ
  apply GlobalTheory.FockDelta.fock_self_pos
  unfold GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.deltaAtEmb
  have hi := i.isLt
  have hW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (by omega) (by omega)
  apply GlobalTheory.FockDelta.delta_ne_zero
  · intro ρ
    exact le_of_eq (Formalism.BasicNotions.sig_sum _ (D.sp.W_sig _) _)
  · rw [hW]
    exact r_le_V i
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockNormMinorProductDeltaAtEmbeddingPosStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockNorm_minorProductDeltaAtEmbedding_pos : ∀ (D : D7) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), ∃ a : ℝ, 0 < a ∧ Formalism.E.fock (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.deltaAtEmb D i σ) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.deltaAtEmb D i σ) = (a : ℂ) := by
  first | exact @GlobalTheory.FockDelta.fock_deltaAtEmb_pos | exact GlobalTheory.FockDelta.fock_deltaAtEmb_pos | (intros; apply GlobalTheory.FockDelta.fock_deltaAtEmb_pos <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftTwistsByLevelCharacter
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowClassSum

section Generic

open Formalism.IndefR.Bridge

variable {G Γ W : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  {ι : Γ →* G} {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ}

theorem card_stab (γ : Γ) (h : G) (k : J) :
    Nat.card (stab ι J (ι γ * h * k)) = Nat.card (stab ι J h) := by
  refine Nat.card_congr (Equiv.subtypeEquiv (MulAut.conj γ⁻¹).toEquiv fun δ => ?_)
  have e : (ι γ * h * k)⁻¹ * ι δ * (ι γ * h * k) =
      (k : G)⁻¹ * (h⁻¹ * ι ((MulAut.conj γ⁻¹).toEquiv δ) * h) * k := by
    simp [mul_assoc]
  rw [mem_stab, mem_stab, e, J.mul_mem_cancel_right k.2, J.mul_mem_cancel_left (J.inv_mem k.2)]

theorem adInner_indep (hρ : ∀ γ x x', inner ℂ (ρ γ x) (ρ γ x') = inner ℂ x x') (hχ : ∀ k, ‖(χ k : ℂ)‖ = 1)
    {I : Type} [Fintype I] {y y' : I → G} (hy : IsReps ι J y) (hy' : IsReps ι J y')
    {F F' : G → W} (hF : F ∈ AdForms ι ρ J χ) (hF' : F' ∈ AdForms ι ρ J χ) :
    adInner ι J y' F F' = adInner ι J y F F' := by
  choose s γ k hs using fun i => (hy (y' i)).exists
  have hinj : Function.Injective s := by
    intro i j hij
    refine (hy' (y' i)).unique ⟨1, 1, by simp⟩ ⟨γ i * (γ j)⁻¹, (k j)⁻¹ * k i, ?_⟩
    rw [hs i, hs j, hij]
    simp [mul_assoc]
  unfold adInner
  refine Fintype.sum_bijective s (Finite.injective_iff_bijective.1 hinj) _ _ fun i => ?_
  rw [hs i, card_stab, hF, hF', inner_smul_left, inner_smul_right, ← mul_assoc (starRingEnd ℂ _),
    Complex.conj_mul', hχ, hρ]
  simp

variable {Q : Subgroup G} {ch : Q →* ℂˣ}

theorem reductionGroupAction_mem_adelicForms (hJ : J ≤ Q) (hn : ∀ κ ∈ Q, ∀ k ∈ J, κ⁻¹ * k * κ ∈ J) (hch : ∀ k : J, ch ⟨k, hJ k.2⟩ = χ k)
    (κ : Q) {F : G → W} (hF : F ∈ AdForms ι ρ J χ) : g0Act ch κ F ∈ AdForms ι ρ J χ := by
  intro γ h k
  have hk := hn κ κ.2 k k.2
  have e : ι γ * h * k * κ = ι γ * (h * κ) * ((⟨_, hk⟩ : J) : G) := by simp [mul_assoc]
  have e2 : χ ⟨_, hk⟩ = χ k := by
    rw [← hch, ← hch]
    have : (⟨_, hJ hk⟩ : Q) = κ⁻¹ * ⟨k, hJ k.2⟩ * κ := rfl
    rw [this, map_mul, map_mul, map_inv, mul_right_comm, inv_mul_cancel, one_mul]
  unfold g0Act
  rw [e, hF, e2, map_smul, smul_comm]

theorem adInner_g0Act (hρ : ∀ γ x x', inner ℂ (ρ γ x) (ρ γ x') = inner ℂ x x') (hχ : ∀ k, ‖(χ k : ℂ)‖ = 1)
    (hn : ∀ κ ∈ Q, ∀ k ∈ J, κ⁻¹ * k * κ ∈ J) (κ : Q) (hκ : ‖(ch κ : ℂ)‖ = 1)
    {I : Type} [Fintype I] {y : I → G} (hy : IsReps ι J y)
    {F F' : G → W} (hF : F ∈ AdForms ι ρ J χ) (hF' : F' ∈ AdForms ι ρ J χ) :
    adInner ι J y (g0Act ch κ F) (g0Act ch κ F') = adInner ι J y F F' := by
  have hn' : ∀ k ∈ J, (κ : G) * k * (κ : G)⁻¹ ∈ J := fun k hk => by
    simpa using hn _ (Q.inv_mem κ.2) k hk
  have hy' : IsReps ι J fun i => y i * κ := by
    intro h
    refine (existsUnique_congr fun i => ?_).1 (hy (h * (κ : G)⁻¹))
    constructor
    · rintro ⟨γ, k, e⟩
      refine ⟨γ, ⟨_, hn κ κ.2 k k.2⟩, ?_⟩
      rw [mul_inv_eq_iff_eq_mul] at e
      rw [e]; simp [mul_assoc]
    · rintro ⟨γ, k, e⟩
      refine ⟨γ, ⟨_, hn' k k.2⟩, ?_⟩
      rw [e]; simp [mul_assoc]
  rw [← adInner_indep hρ hχ hy hy' hF hF']
  unfold adInner g0Act
  refine Finset.sum_congr rfl fun i _ => ?_
  have hs : stab ι J (y i * κ) = stab ι J (y i) := by
    ext δ
    rw [mem_stab, mem_stab]
    constructor
    · intro h
      simpa [mul_assoc] using hn' _ h
    · intro h
      simpa [mul_assoc] using hn κ κ.2 _ h
  rw [hs, inner_smul_left, inner_smul_right, ← mul_assoc (starRingEnd ℂ _), Complex.conj_mul',
    Units.val_inv_eq_inv_val, norm_inv, hκ]
  simp

theorem exists_g0Act (hρ : ∀ γ x x', inner ℂ (ρ γ x) (ρ γ x') = inner ℂ x x') (hn1 : ∀ q, ‖(ch q : ℂ)‖ = 1)
    (hJ : J ≤ Q) (hn : ∀ κ ∈ Q, ∀ k ∈ J, κ⁻¹ * k * κ ∈ J) (hch : ∀ k : J, ch ⟨k, hJ k.2⟩ = χ k)
    {I : Type} [Fintype I] {y : I → G} (hy : IsReps ι J y) (M : Links.HMod (G → W))
    (hM : M.Is (AdForms ι ρ J χ) (adInner ι J y)) (κ : Q) (x : M.H) :
    ∃ x' : M.H, M.e x' = g0Act ch κ (M.e x) ∧ ‖x'‖ = ‖x‖ := by
  obtain ⟨-, hr, hi⟩ := hM
  have hχ : ∀ k, ‖(χ k : ℂ)‖ = 1 := fun k => by
    rw [← hch]; exact hn1 _
  have hx : M.e x ∈ AdForms ι ρ J χ := by
    rw [← hr]; exact ⟨x, rfl⟩
  have hm := reductionGroupAction_mem_adelicForms hJ hn hch κ hx
  rw [← hr] at hm
  obtain ⟨x', hx'⟩ := hm
  refine ⟨x', hx', ?_⟩
  have e : inner ℂ x' x' = inner ℂ x x := by
    rw [hi, hi, hx']
    exact adInner_g0Act hρ hχ hn κ (hn1 _) hy hx hx
  rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ _ _ _ _ x, e]

theorem twistedTranslate_apply_eq_inv_smul {a : G} (ha : a ∈ Q) (F : G → W) (h : G) {z : ℂ} (hz : ((ch ⟨a, ha⟩ : ℂˣ) : ℂ) = z) :
    g0Act ch ⟨a, ha⟩ F h = z⁻¹ • F (h * a) := by
  rw [← hz, ← Units.val_inv_eq_inv_val]
  rfl

end Generic

variable {D : D7}

theorem norm_levFn_flagL (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (x : GL (Fin V.rank) (Lev.EAf D)) : ‖((levFn β (flagL L) x : ℂˣ) : ℂ)‖ = 1 := by
  have h2 : Formalism.L2.DIV.ext1 (flagL L).P.H (flagL L).P.chi (Formalism.L2.DIV.rTup β (flagL L) x) = 1 :=
    subgroupCharExtension_one_apply _ _
  unfold Formalism.L2.DIV.levFn
  rw [h2, one_mul, Units.val_mul, norm_mul, Units.coe_prod, Units.coe_prod, norm_prod, norm_prod,
    Finset.prod_eq_one, Finset.prod_eq_one, one_mul]
  · intro PP _
    exact norm_residueChar_eq_one PP _ _
  · intro PP _
    rw [Units.coe_prod, norm_prod]
    exact Finset.prod_eq_one fun c _ => norm_residueChar_eq_one PP _ _

theorem conj_mem_flag1L (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    {a b : GL (Fin V.rank) (Lev.EAf D)} (ha : a ∈ lev D.sp.cm V.gram β (flagL L))
    (hb : b ∈ lev D.sp.cm V.gram β (flag1L L)) : a⁻¹ * b * a ∈ lev D.sp.cm V.gram β (flag1L L) := by
  have h1 : a ∈ parLev D.sp.cm V.gram β L := ha.1
  have h2 : b ∈ parLev D.sp.cm V.gram β L := hb.1
  have h3 : rTup β L b = 1 := Subgroup.mem_bot.1 hb.2
  have h4 : a⁻¹ * b ∈ parLev D.sp.cm V.gram β L := Subgroup.mul_mem _ (Subgroup.inv_mem _ h1) h2
  have h5 : rTup β L (a⁻¹ * b * a) = 1 := by
    rw [rTup_mul h4 h1, rTup_mul (Subgroup.inv_mem _ h1) h2, rTup_inv h1, h3, mul_one, inv_mul_cancel]
  exact ⟨Subgroup.mul_mem _ h4 h1, Subgroup.mem_bot.2 h5⟩

theorem levEnv_normal (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) :
    ∀ κ ∈ (levEnv V β L).Q, ∀ k ∈ (levEnv V β L).J, κ⁻¹ * k * κ ∈ (levEnv V β L).J := by
  intro κ hκ k hk
  have h := conj_mem_flag1L V β L (a := Formalism.UG.bc (swapAE D) κ.1) (b := Formalism.UG.bc (swapAE D) k.1) hκ hk
  rw [← map_inv, ← map_mul, ← map_mul] at h
  exact h

theorem levEnv_ch (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (q : (levEnv V β L).Q) : (levEnv V β L).ch q = levFn β (flagL L) (Formalism.UG.bc (swapAE D) q.1.1) := rfl

theorem mem_levEnv_Q {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank}
    {g0 : G0 L.Pg L.r} {κ : GA D V} (hκ : IsLevelLift V β L g0 κ) :
    (finHom V).rangeRestrict κ ∈ (levEnv V β L).Q := by
  have h : finE V κ ∈ lev D.sp.cm V.gram β (flagL L) := ⟨hκ.2.1, Subgroup.mem_top _⟩
  exact h

theorem levEnv_ch_lift {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank}
    {κ : GA D V} (hq : (finHom V).rangeRestrict κ ∈ (levEnv V β L).Q) :
    (((levEnv V β L).ch ⟨_, hq⟩ : ℂˣ) : ℂ) = levChi V β (flagL L) κ := by
  rw [levEnv_ch]
  rfl

theorem exists_translate (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (c : CoefA V) (hc : c.Is) (M : HMod (Bridge.Gf V → c.W)) {I : Type} [Fintype I] (y : I → Bridge.Gf V)
    (hy : Bridge.IsReps (Bridge.ratF V) (levEnv V β L).J y)
    (hM : M.Is (Bridge.AdForms (Bridge.ratF V) c.coef.ρ (levEnv V β L).J (levEnv V β L).χ)
      (Bridge.adInner (Bridge.ratF V) (levEnv V β L).J y))
    (g0 : G0 L.Pg L.r) (κ : GA D V) (hκ : IsLevelLift V β L g0 κ) (x : M.H) :
    ∃ x' : M.H, (∀ h, M.e x' h = (levChi V β (flagL L) κ)⁻¹ • M.e x (h * (finHom V).rangeRestrict κ)) ∧
      ‖x'‖ = ‖x‖ := by
  have hq := mem_levEnv_Q hκ
  have hch : ∀ q, ‖(((levEnv V β L).ch q : ℂˣ) : ℂ)‖ = 1 := fun q => by
    rw [levEnv_ch]; exact norm_levFn_flagL V β L _
  have hρ : ∀ (γ : GQ V) (u u' : c.W),
      inner ℂ ((c.ρ.comp (GQ V).subtype) γ u) ((c.ρ.comp (GQ V).subtype) γ u') = inner ℂ u u' :=
    fun γ u u' => hc.2.1 γ.1 u u'
  have key : ∃ x' : M.H, M.e x' = Bridge.g0Act (levEnv V β L).ch ⟨_, hq⟩ (M.e x) ∧ ‖x'‖ = ‖x‖ :=
    exists_g0Act (W := c.coef.W) (ι := Bridge.ratF V) (ρ := c.coef.ρ) (χ := (levEnv V β L).χ)
      (ch := (levEnv V β L).ch) hρ hch (levEnv V β L).J_le (levEnv_normal V β L) (levEnv V β L).ch_J hy M hM ⟨_, hq⟩ x
  obtain ⟨x', hx', hn⟩ := key
  refine ⟨x', fun h => ?_, hn⟩
  refine Eq.trans ?_ (twistedTranslate_apply_eq_inv_smul (ch := (levEnv V β L).ch) hq (M.e x) h (levEnv_ch_lift hq))
  exact congrFun hx' h

end GlobalTheory.RowClassSum

namespace GlobalTheory

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergQuotientOpSumVacuumCommensurableSelfDu
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergVacuumUniqueOfSelfDual
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergVacuumUniqueOfSelfDual
open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SphTheta

theorem vacuum_unique_of_selfDual {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]
    {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} (h : IsHeis σ w γ W) (Λ : Submodule R X)
    (hΛ : SelfDual γ Λ) (s : M) (hs : s ≠ 0) (hfix : Fixes W Λ s)
    (hspan : Submodule.span ℂ (Set.range fun x => W x s) = ⊤) (v : M) (hv : Fixes W Λ v) : ∃ c : ℂ, v = c • s := by
  have key : ∀ z : X, W z s = (γ (w • (Quotient.out (Submodule.Quotient.mk z : X ⧸ Λ) : X))
      (z - Quotient.out (Submodule.Quotient.mk z : X ⧸ Λ)))⁻¹ • W (Quotient.out (Submodule.Quotient.mk z : X ⧸ Λ)) s := by
    intro z
    set t : X := Quotient.out (Submodule.Quotient.mk z : X ⧸ Λ) with ht
    have hmem : z - t ∈ Λ := by
      rw [← Submodule.Quotient.eq]
      exact (Quotient.out_eq (Submodule.Quotient.mk z : X ⧸ Λ)).symm
    have h1 := h.comp t (z - t) s
    rw [hfix _ hmem, add_sub_cancel] at h1
    rw [h1, smul_smul, inv_mul_cancel₀ (h.ne_zero _ _), one_smul]
  have hli : LinearIndependent ℂ (fun q : X ⧸ Λ => W (Quotient.out q) s) := by
    refine linearIndependent_of_simultaneous_eigen _ (fun q (a : Λ) => γ a (Quotient.out q)) (fun a : Λ => W a) ?_ ?_ ?_
    · intro q q' hq
      have hm : (Quotient.out q : X) - Quotient.out q' ∈ Λ := by
        rw [hΛ]
        intro a ha
        apply h.swap_eq_one
        have h1 : γ a (Quotient.out q) = γ a (Quotient.out q') := congrFun hq ⟨a, ha⟩
        rw [sub_eq_add_neg, h.add_right, h.neg_right, h1, mul_inv_cancel₀ (h.ne_zero _ _)]
      rw [← Submodule.Quotient.eq] at hm
      have e1 : (Submodule.Quotient.mk (Quotient.out q) : X ⧸ Λ) = q := Quotient.out_eq q
      have e2 : (Submodule.Quotient.mk (Quotient.out q') : X ⧸ Λ) = q' := Quotient.out_eq q'
      rw [← e1, ← e2, hm]
    · intro a q
      rw [h.comm, hfix a a.2]
    · intro q h0
      have h1 := h.neg_comp (Quotient.out q) s
      rw [h0, map_zero] at h1
      exact hs ((smul_eq_zero.1 h1.symm).resolve_left (h.ne_zero _ _))
  have hsp : ⊤ ≤ Submodule.span ℂ (Set.range fun q : X ⧸ Λ => W (Quotient.out q) s) := by
    rw [← hspan, Submodule.span_le]
    rintro _ ⟨z, rfl⟩
    show W z s ∈ _
    rw [key z]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  let b := Module.Basis.mk hli hsp
  have hb : ∀ q, b q = W (Quotient.out q) s := fun q => Module.Basis.mk_apply hli hsp q
  have hcoord : ∀ a ∈ Λ, ∀ q x, b.coord q (W a x) = γ a (Quotient.out q) * b.coord q x := by
    intro a ha q x
    have e : (b.coord q).comp (W a) = γ a (Quotient.out q) • b.coord q := by
      refine b.ext fun q' => ?_
      rw [LinearMap.comp_apply, hb, h.comm, hfix a ha, ← hb, LinearMap.smul_apply, map_smul, smul_eq_mul]
      simp only [Module.Basis.coord_apply, Module.Basis.repr_self, smul_eq_mul, Finsupp.single_apply]
      split_ifs with hq
      · rw [hq]
      · simp
    exact LinearMap.congr_fun e x
  have h0 : (Quotient.out (0 : X ⧸ Λ) : X) ∈ Λ :=
    (Submodule.Quotient.mk_eq_zero Λ).1 (Quotient.out_eq (0 : X ⧸ Λ))
  have hb0 : b 0 = s := by rw [hb, hfix _ h0]
  have hvan : ∀ q : X ⧸ Λ, q ≠ 0 → b.repr v q = 0 := by
    intro q hq
    have hn : (Quotient.out q : X) ∉ Λ := fun hm => hq (by
      have e1 : (Submodule.Quotient.mk (Quotient.out q) : X ⧸ Λ) = q := Quotient.out_eq q
      rw [← e1]; exact (Submodule.Quotient.mk_eq_zero Λ).2 hm)
    rw [hΛ] at hn
    push_neg at hn
    obtain ⟨a, ha, hne⟩ := hn
    have hne' : γ a (Quotient.out q) ≠ 1 := fun e => hne (h.swap_eq_one e)
    have e := hcoord a ha q v
    rw [hv a ha, Module.Basis.coord_apply] at e
    have e2 : (γ a (Quotient.out q) - 1) * b.repr v q = 0 := by rw [sub_mul, ← e]; ring
    exact (mul_eq_zero.1 e2).resolve_left (sub_ne_zero.2 hne')
  refine ⟨b.repr v 0, b.ext_elem fun q => ?_⟩
  rw [map_smul, ← hb0, b.repr_self, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
  by_cases hq : (0 : X ⧸ Λ) = q
  · subst hq; simp
  · rw [if_neg hq, mul_zero, hvan q (Ne.symm hq)]

end GlobalTheory.SphTheta

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergVacuumUniqueOfSelfDualStatement
open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergVacuum_unique_of_selfDual : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ Λ : Submodule R X, SelfDual γ Λ → ∀ s : M, s ≠ 0 → Fixes W Λ s → Submodule.span ℂ (Set.range fun x => W x s) = ⊤ → ∀ v, Fixes W Λ v → ∃ c : ℂ, v = c • s := by
  first | exact @GlobalTheory.SphTheta.vacuum_unique_of_selfDual | exact GlobalTheory.SphTheta.vacuum_unique_of_selfDual | (intros; apply GlobalTheory.SphTheta.vacuum_unique_of_selfDual <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergQuotientOpSumVacuumCommensurableSelfDu
open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

namespace GlobalTheory.SphTheta

theorem sumOp_vec_zero {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]
    (W : X → M →ₗ[ℂ] M) (A B : Submodule R X) : sumOp W A B 0 = 0 := by
  unfold sumOp; simp

theorem form_translate_vacuum {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]
    {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} (h : IsHeis σ w γ W) {Λ : Submodule R X}
    (hΛ : SelfDual γ Λ) {s : M} (hs : Fixes W Λ s) (e : M →ₗ[ℂ] ℂ) (he : ∀ a ∈ Λ, ∀ v, e (W a v) = e v) (x : X) :
    e (W x s) = if x ∈ Λ then e s else 0 := by
  split_ifs with hx
  · rw [hs x hx]
  · obtain ⟨a, ha, hne⟩ : ∃ a ∈ Λ, γ x a ≠ 1 := by
      by_contra hc
      push_neg at hc
      exact hx ((hΛ x).2 hc)
    have h1 : e (W x s) = γ a x * e (W x s) := by
      conv_lhs => rw [← he a ha (W x s)]
      rw [h.comm a x s, hs a ha, map_smul, smul_eq_mul]
    have h2 : γ a x ≠ 1 := by
      rw [h.swap x a]
      intro h3
      exact hne (inv_eq_one.1 h3)
    have h3 : (1 - γ a x) * e (W x s) = 0 := by rw [sub_mul, one_mul, ← h1, sub_self]
    exact (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 (Ne.symm h2))

theorem sumOp_vacuum_lift : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ Λ : Submodule R X, SelfDual γ Λ → ∀ s : M, s ≠ 0 → Fixes W Λ s → Submodule.span ℂ (Set.range fun x => W x s) = ⊤ → ∀ Λ' : Submodule R X, SelfDual γ Λ' → idx Λ Λ' ≠ 0 → (sumOp W Λ Λ' s ≠ 0 ∧ Fixes W Λ' (sumOp W Λ Λ' s) ∧ Submodule.span ℂ (Set.range fun x => W x (sumOp W Λ Λ' s)) = ⊤) ∧ ∀ e : M →ₗ[ℂ] ℂ, e s = 1 → (∀ a ∈ Λ, ∀ v, e (W a v) = e v) → ∀ v, Fixes W Λ' v → v = e v • sumOp W Λ Λ' s := by
  intro R X M _ _ _ _ _ σ w γ W h Λ hΛ s hs0 hs hspan Λ' hΛ' hidx
  obtain ⟨hidx', hss⟩ := sumOp_sumOp_eq_idx_smul h Λ Λ' hΛ hΛ' hidx
  obtain ⟨⟨n, f, hf, ht⟩, hfix, -⟩ := (sumOp_transversal h Λ Λ' hΛ').2.1 hidx
  have hs'fix : Fixes W Λ' (sumOp W Λ Λ' s) := hfix s hs
  have hback := hss s hs
  have hidxC : (idx Λ Λ' : ℂ) ≠ 0 := by exact_mod_cast hidx
  have hne : sumOp W Λ Λ' s ≠ 0 := by
    intro h0
    rw [h0, sumOp_vec_zero] at hback
    exact hs0 ((smul_eq_zero.1 hback.symm).resolve_left hidxC)
  have hidx2 : idx Λ' Λ ≠ 0 := by rw [hidx']; exact hidx
  obtain ⟨⟨m, g, hg, hgt⟩, -, -⟩ := (sumOp_transversal h Λ' Λ hΛ).2.1 hidx2
  have hsum := ((sumOp_transversal h Λ' Λ hΛ).1 _ hs'fix (Fin m) g hg hgt).1
  have hsE : s = ((idx Λ Λ' : ℂ))⁻¹ • ∑ i, W (g i) (sumOp W Λ Λ' s) := by
    rw [← hsum, hback, smul_smul, inv_mul_cancel₀ hidxC, one_smul]
  have hmem : ∀ x, W x s ∈ Submodule.span ℂ (Set.range fun y => W y (sumOp W Λ Λ' s)) := by
    intro x
    set_option synthInstance.maxHeartbeats 100000 in
      rw [congrArg (W x) hsE, map_smul, map_sum]
    refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ => ?_)
    rw [h.comp]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  have hspan' : Submodule.span ℂ (Set.range fun y => W y (sumOp W Λ Λ' s)) = ⊤ := by
    rw [eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact hmem x
  refine ⟨⟨hne, hs'fix, hspan'⟩, fun e he1 he v hv => ?_⟩
  obtain ⟨c, rfl⟩ := GlobalTheory.T.heisenbergVacuum_unique_of_selfDual h Λ' hΛ' _ hne hs'fix hspan' v hv
  have hes' : e (sumOp W Λ Λ' s) = 1 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [((sumOp_transversal h Λ Λ' hΛ').1 s hs (Fin n) f hf ht).1, map_sum]
    simp only [form_translate_vacuum h hΛ hs e he, he1]
    obtain ⟨i0, hi0, huniq⟩ := ht 0 Λ'.zero_mem
    rw [Finset.sum_eq_single i0]
    · rw [if_pos (by simpa using hi0)]
    · intro j _ hj
      rw [if_neg]
      intro hjΛ
      exact hj (huniq j (by simpa using hjΛ))
    · simp
  rw [map_smul, hes', smul_eq_mul, mul_one]

end GlobalTheory.SphTheta
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergQuotientOpSumVacuumCommensurableSelfDuStatement
open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergQuotientOpSum_vacuum_commensurable_selfDualLattice : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ Λ : Submodule R X, SelfDual γ Λ → ∀ s : M, s ≠ 0 → Fixes W Λ s → Submodule.span ℂ (Set.range fun x => W x s) = ⊤ → ∀ Λ' : Submodule R X, SelfDual γ Λ' → idx Λ Λ' ≠ 0 → (sumOp W Λ Λ' s ≠ 0 ∧ Fixes W Λ' (sumOp W Λ Λ' s) ∧ Submodule.span ℂ (Set.range fun x => W x (sumOp W Λ Λ' s)) = ⊤) ∧ ∀ e : M →ₗ[ℂ] ℂ, e s = 1 → (∀ a ∈ Λ, ∀ v, e (W a v) = e v) → ∀ v, Fixes W Λ' v → v = e v • sumOp W Λ Λ' s := by
  first | exact @GlobalTheory.SphTheta.sumOp_vacuum_lift | exact GlobalTheory.SphTheta.sumOp_vacuum_lift | (intros; apply GlobalTheory.SphTheta.sumOp_vacuum_lift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CardMulFinrankSubgroupEigenspaceOfTraceVanishes
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CardMulFinrankSubgroupEigenspaceOfTraceVanishes
noncomputable section

namespace GlobalTheory.DefFree

theorem isProj_eig_average {G M : Type} [Group G] [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M)
    (P : Subgroup G) [Fintype P] (χ : P →* ℂˣ) :
    LinearMap.IsProj (GlobalTheory.DefFree.eig ρ P fun g => ((χ g : ℂˣ) : ℂ))
      ((Fintype.card P : ℂ)⁻¹ • ∑ g : P, (((χ g)⁻¹ : ℂˣ) : ℂ) • (ρ g : M →ₗ[ℂ] M)) := by
  classical
  have hcard : (Fintype.card P : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have happ : ∀ x : M, ((Fintype.card P : ℂ)⁻¹ • ∑ g : P, (((χ g)⁻¹ : ℂˣ) : ℂ) • (ρ g : M →ₗ[ℂ] M)) x
      = (Fintype.card P : ℂ)⁻¹ • ∑ g : P, (((χ g)⁻¹ : ℂˣ) : ℂ) • ρ g x := by
    intro x
    simp only [LinearMap.smul_apply, LinearMap.sum_apply]
  refine ⟨fun x => ?_, fun x hx => ?_⟩
  ·
    rw [happ, mem_eig]
    intro h
    have hsum : ρ h (∑ g : P, (((χ g)⁻¹ : ℂˣ) : ℂ) • ρ g x)
        = ((χ h : ℂˣ) : ℂ) • ∑ g : P, (((χ g)⁻¹ : ℂˣ) : ℂ) • ρ g x := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.smul_sum]
      refine Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun g => ?_
      have hc : ((χ h : ℂˣ) : ℂ) * (((χ (h * g))⁻¹ : ℂˣ) : ℂ) = (((χ g)⁻¹ : ℂˣ) : ℂ) := by
        rw [← Units.val_mul, map_mul, mul_inv, mul_inv_cancel_left]
      show ρ h ((((χ g)⁻¹ : ℂˣ) : ℂ) • ρ g x)
        = ((χ h : ℂˣ) : ℂ) • ((((χ (h * g))⁻¹ : ℂˣ) : ℂ) • ρ ((h * g : P) : G) x)
      rw [smul_smul, hc, map_smul, Subgroup.coe_mul, map_mul, Module.End.mul_apply]
    show ρ h (_ • _) = ((χ h : ℂˣ) : ℂ) • (_ • _)
    rw [map_smul, hsum, smul_comm]
  ·
    have hx' : ∀ g : P, ρ g x = ((χ g : ℂˣ) : ℂ) • x := fun g => (mem_eig.mp hx) g
    have hterm : ∀ g : P, (((χ g)⁻¹ : ℂˣ) : ℂ) • ρ g x = x := fun g => by
      rw [hx' g, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
    rw [happ]
    simp only [hterm, Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hcard, one_smul]

theorem card_mul_finrank_eig (G M : Type) [Group G] [Finite G] [AddCommGroup M] [Module ℂ M]
    [FiniteDimensional ℂ M] (ρ : Representation ℂ G M) (P : Subgroup G) (χ : P →* ℂˣ)
    (h : ∀ g ∈ P, g ≠ 1 → LinearMap.trace ℂ M (ρ g) = 0) :
    Nat.card P * Module.finrank ℂ (GlobalTheory.DefFree.eig ρ P fun g => ((χ g : ℂˣ) : ℂ)) = Module.finrank ℂ M := by
  classical
  haveI : Fintype P := Fintype.ofFinite P
  have htr := (isProj_eig_average ρ P χ).trace
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_smul, map_sum, smul_eq_mul] at htr
  simp only [map_smul, smul_eq_mul] at htr

  rw [Finset.sum_eq_single (1 : P) (fun g _ hg => by
      rw [h g g.2 (fun h1 => hg (Subtype.ext h1)), mul_zero])
    (fun h1 => absurd (Finset.mem_univ _) h1)] at htr
  rw [map_one, inv_one, Units.val_one, one_mul, OneMemClass.coe_one, map_one,
    LinearMap.trace_one] at htr
  have hcard : (Fintype.card P : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [Nat.card_eq_fintype_card]
  have key : (Fintype.card P : ℂ) * (Module.finrank ℂ (GlobalTheory.DefFree.eig ρ P fun g => ((χ g : ℂˣ) : ℂ)) : ℂ)
      = (Module.finrank ℂ M : ℂ) := by
    rw [← htr, ← mul_assoc, mul_inv_cancel₀ hcard, one_mul]
  exact_mod_cast key

end GlobalTheory.DefFree

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CardMulFinrankSubgroupEigenspaceOfTraceVanishesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_mul_finrank_subgroupEigenspace_of_trace_vanishes : ∀ (G M : Type) [Group G] [Finite G] [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ρ : Representation ℂ G M) (P : Subgroup G) (χ : P →* ℂˣ), (∀ g ∈ P, g ≠ 1 → LinearMap.trace ℂ M (ρ g) = 0) → Nat.card P * Module.finrank ℂ (eig ρ P fun g => ((χ g : ℂˣ) : ℂ)) = Module.finrank ℂ M := by
  first | exact @GlobalTheory.DefFree.card_mul_finrank_eig | exact GlobalTheory.DefFree.card_mul_finrank_eig | (intros; apply GlobalTheory.DefFree.card_mul_finrank_eig <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypePrimeLargeAndOneModSixteenQD
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypePrimeLargeAndOneModSixteenQD
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TypePrimeSize

theorem k_pow_le_g {D : D7} {L : SizeData₂ D} (P : ParameterChoice' D L) (i : Fin 2) : D.R.k ^ 8 ≤ D.host.g i := by
  obtain ⟨Y, h1, -, -, h4⟩ := P.g_Y
  have hL : 0 ≤ L.sc.L := by
    unfold Scale.L; exact Real.rpow_nonneg (by linarith [L.sc.one_lt_alt]) _
  have hb : 1 ≤ L.sc.b := by unfold Scale.b; exact Real.one_le_exp hL
  have hk : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
  have h2 : (D.R.k : ℝ) ≤ D.R.k * L.sc.b := le_mul_of_one_le_right hk hb
  have h3 : (D.R.k : ℝ) ^ 8 ≤ (D.R.k * L.sc.b) ^ 8 := pow_le_pow_left₀ hk h2 8
  have : (D.R.k : ℝ) ^ 8 ≤ D.host.g i := h3.trans (h1.trans (h4 i).1)
  exact_mod_cast this

theorem typePrime_large_and_ok : ∀ (D : D7) (L : SizeData₂ D), ParameterChoice' D L → ∀ k : Fin 2,
    Module.finrank ℚ D.host.E * D.R.r + 1 < D.host.g k ∧
      GlobalTheory.BadShare.PrimeOK (D.host.g k) D.host.q D.host.d := by
  intro D L P i
  have hg := k_pow_le_g P i
  have hE : Module.finrank ℚ D.host.E = 4 * D.R.ord := D.host.finrank_cmField
  have he := D.host.two_le_e
  have h4 : 2 ^ 2 ≤ 2 ^ D.R.e := Nat.pow_le_pow_right (by norm_num) he
  have hf := D.R.f_le_k
  have hfo : D.R.f = 2 * D.R.ord := rfl
  have ho : 2 ^ D.R.e ≤ D.R.ord := Nat.le_of_dvd D.R.ord_pos D.R.toFrame.two_pow_dvd_ord
  have hm := D.R.m_add_three_le_k
  have hm2 := D.R.two_le_m
  have ht := D.R.rank_add_five_le
  have hk8 : 8 ≤ D.R.k := by omega
  have hr : D.R.r ≤ 2 * D.R.k := by unfold Ranks.r; omega
  have hr1 : 1 ≤ D.R.r := by unfold Ranks.r; omega
  have hE' : Module.finrank ℚ D.host.E ≤ 2 * D.R.k := by
    have h2f : D.R.f = 2 * D.R.ord := rfl
    have hfk : D.R.f ≤ D.R.k := hf
    omega
  have hk6 : 8 ^ 6 ≤ D.R.k ^ 6 := Nat.pow_le_pow_left hk8 6
  have hk2 : 8 ^ 2 ≤ D.R.k ^ 2 := Nat.pow_le_pow_left hk8 2
  have hpow : 8 ^ 6 * D.R.k ^ 2 ≤ D.R.k ^ 8 := by
    calc 8 ^ 6 * D.R.k ^ 2 ≤ D.R.k ^ 6 * D.R.k ^ 2 := Nat.mul_le_mul_right _ hk6
      _ = D.R.k ^ 8 := by ring
  have hprod : Module.finrank ℚ D.host.E * D.R.r ≤ 4 * D.R.k ^ 2 := by
    calc Module.finrank ℚ D.host.E * D.R.r ≤ (2 * D.R.k) * (2 * D.R.k) := Nat.mul_le_mul hE' hr
      _ = 4 * D.R.k ^ 2 := by ring
  obtain ⟨hq, hd, hq8, hd16, -⟩ := D.host.hyp
  have hb := D.host.qd_big.1
  refine ⟨by omega, hq, hd, by omega, by omega, by omega, ?_, ?_, by omega⟩
  · have h1 : 5 * 1 ≤ D.R.t * D.R.r := Nat.mul_le_mul (by omega) hr1
    have h2 : 4 * D.R.t * D.R.r = 4 * (D.R.t * D.R.r) := by ring
    exact le_max_of_le_left (by omega)
  · have hc := D.ntypes.g_cond i
    have hdvd : 16 * D.host.q * D.host.d ∣ D.host.QS * D.host.q * D.host.d := by
      have h16 : 16 ∣ D.host.QS := (pow_dvd_pow 2 (by omega : 4 ≤ D.R.e + 2)).trans D.host.tower_dvd
      exact Nat.mul_dvd_mul_right (Nat.mul_dvd_mul_right h16 _) _
    refine hdvd.trans ⟨D.host.g i / (D.host.QS * D.host.q * D.host.d), ?_⟩
    have := Nat.div_add_mod (D.host.g i) (D.host.QS * D.host.q * D.host.d)
    omega

end GlobalTheory.TypePrimeSize
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypePrimeLargeAndOneModSixteenQDStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.typePrime_large_and_one_mod_sixteen_q_d : ∀ (D : D7) (L : SizeData₂ D), ParameterChoice' D L → ∀ k : Fin 2, Module.finrank ℚ D.host.E * D.R.r + 1 < D.host.g k ∧ GlobalTheory.BadShare.PrimeOK (D.host.g k) D.host.q D.host.d := by
  first | exact @GlobalTheory.TypePrimeSize.typePrime_large_and_ok | exact GlobalTheory.TypePrimeSize.typePrime_large_and_ok | (intros; apply GlobalTheory.TypePrimeSize.typePrime_large_and_ok <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinrankEqCardMulAndTraceEqZeroOfFreeValuesStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinrankEqCardMulAndTraceEqZeroOfFreeValues
namespace GlobalTheory

theorem trace_eq_zero_of_coord_move {X W : Type} [Fintype X] [DecidableEq X] [AddCommGroup W]
    [Module ℂ W] [FiniteDimensional ℂ W] (π : X → X) (hπ : ∀ c, π c ≠ c)
    (φ : X → Module.End ℂ W) (M : Module.End ℂ (X → W)) (hM : ∀ f c, M f c = φ c (f (π c))) :
    LinearMap.trace ℂ (X → W) M = 0 := by
  classical

  let b := Pi.basis (fun _ : X => Module.finBasis ℂ W)
  rw [LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, Pi.basis_repr, Pi.basis_apply, hM,
    Pi.single_eq_of_ne (hπ i.1), map_zero, map_zero, Finsupp.zero_apply]

theorem finrank_eq_card_mul_and_trace_eq_zero_of_free_values :
    ∀ (Y X B W : Type) [Finite X] [AddCommGroup B] [Module ℂ B] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (cls : Y → X) (ev : Y → (B →ₗ[ℂ] W)) (S : Submodule ℂ B), Function.Surjective cls → (∀ T : B, (∀ h, ev h T = 0) → T = 0) → (∀ h h', cls h = cls h' → ∃ φ : Module.End ℂ W, ∀ T ∈ S, ev h' T = φ (ev h T)) → (∀ h (ℓ : W), ∃ T ∈ S, ev h T = ℓ ∧ ∀ h', cls h' ≠ cls h → ev h' T = 0) → FiniteDimensional ℂ S ∧ Module.finrank ℂ S = Nat.card X * Module.finrank ℂ W ∧ ∀ (H : Type) [AddCommGroup H] [Module ℂ H] (e : H →ₗ[ℂ] B), Function.Injective e → LinearMap.range e = S → ∀ (A : Module.End ℂ H) (t : Y → Y), (∀ x h, ev h (e (A x)) = ev (t h) (e x)) → (∀ h, cls (t h) ≠ cls h) → LinearMap.trace ℂ H A = 0 := by
  intro Y X B W _ _ _ _ _ _ cls ev S hcls hinj hcls_eq hfree
  classical
  haveI : Fintype X := Fintype.ofFinite X

  obtain ⟨s, hs⟩ : ∃ s : X → Y, ∀ x, cls (s x) = x :=
    ⟨fun x => (hcls x).choose, fun x => (hcls x).choose_spec⟩

  let Φ : S →ₗ[ℂ] (X → W) := LinearMap.pi (fun x => (ev (s x)).comp S.subtype)
  have hΦ : ∀ (T : S) x, Φ T x = ev (s x) T := fun _ _ => rfl
  have hzero : ∀ T ∈ S, (∀ x, ev (s x) T = 0) → T = 0 := by
    intro T hT h0
    apply hinj
    intro h
    obtain ⟨φ, hφ⟩ := hcls_eq (s (cls h)) h (hs _)
    rw [hφ T hT, h0, map_zero]
  have hΦinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro T hT
    refine Subtype.ext (hzero T T.2 (fun x => ?_))
    have hx := congrFun hT x
    rw [hΦ] at hx
    exact hx
  have hΦsurj : Function.Surjective Φ := by
    intro g
    choose T hTS hTg hT0 using fun x => hfree (s x) (g x)
    refine ⟨⟨∑ x, T x, Submodule.sum_mem _ (fun x _ => hTS x)⟩, ?_⟩
    funext y
    show ev (s y) (∑ x, T x) = g y
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_eq_single y]
    · exact hTg y
    · intro x _ hxy
      apply hT0
      rw [hs, hs]
      exact Ne.symm hxy
    · intro h
      exact absurd (Finset.mem_univ y) h
  let Ψ : S ≃ₗ[ℂ] (X → W) := LinearEquiv.ofBijective Φ ⟨hΦinj, hΦsurj⟩
  have hfd : FiniteDimensional ℂ S := LinearEquiv.finiteDimensional Ψ.symm
  refine ⟨hfd, ?_, ?_⟩
  · rw [Ψ.finrank_eq, Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul,
      Nat.card_eq_fintype_card]
  · intro H _ _ e he hrange A t hA ht

    let eS : H ≃ₗ[ℂ] S := (LinearEquiv.ofInjective e he).trans (LinearEquiv.ofEq _ _ hrange)
    let Θ : H ≃ₗ[ℂ] (X → W) := eS.trans Ψ
    have hΘ : ∀ x c, Θ x c = ev (s c) (e x) := fun _ _ => rfl
    haveI : FiniteDimensional ℂ H := LinearEquiv.finiteDimensional Θ.symm
    rw [← LinearMap.trace_conj' A Θ]
    choose φ hφ using fun c => hcls_eq (s (cls (t (s c)))) (t (s c)) (hs _)
    refine trace_eq_zero_of_coord_move (fun c => cls (t (s c)))
      (fun c => by have h := ht (s c); rwa [hs] at h) φ _ ?_
    intro g c
    obtain ⟨x, rfl⟩ := Θ.surjective g
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply, hΘ, hΘ, hA]
    have hmem : e x ∈ S := by
      rw [← hrange]
      exact LinearMap.mem_range_self e x
    exact hφ c (e x) hmem

end GlobalTheory
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_eq_card_mul_and_trace_eq_zero_of_free_values_alt : ∀ (Y X B W : Type) [Finite X] [AddCommGroup B] [Module ℂ B] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (cls : Y → X) (ev : Y → (B →ₗ[ℂ] W)) (S : Submodule ℂ B), Function.Surjective cls → (∀ T : B, (∀ h, ev h T = 0) → T = 0) → (∀ h h', cls h = cls h' → ∃ φ : Module.End ℂ W, ∀ T ∈ S, ev h' T = φ (ev h T)) → (∀ h (ℓ : W), ∃ T ∈ S, ev h T = ℓ ∧ ∀ h', cls h' ≠ cls h → ev h' T = 0) → FiniteDimensional ℂ S ∧ Module.finrank ℂ S = Nat.card X * Module.finrank ℂ W ∧ ∀ (H : Type) [AddCommGroup H] [Module ℂ H] (e : H →ₗ[ℂ] B), Function.Injective e → LinearMap.range e = S → ∀ (A : Module.End ℂ H) (t : Y → Y), (∀ x h, ev h (e (A x)) = ev (t h) (e x)) → (∀ h, cls (t h) ≠ cls h) → LinearMap.trace ℂ H A = 0 := by
  first | exact @GlobalTheory.finrank_eq_card_mul_and_trace_eq_zero_of_free_values | exact GlobalTheory.finrank_eq_card_mul_and_trace_eq_zero_of_free_values | (intros; apply GlobalTheory.finrank_eq_card_mul_and_trace_eq_zero_of_free_values <;> assumption)
end
