module

public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsSmulPtSmulPt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NabValPullbackMonomial
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsGoodReductionAlgebraicWeierstrassModel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPowMulEqOne
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaFinOrd

theorem exists_pow_mul_eq_one {F A : Type} [Field F] [Ring A] [Algebra F A] (U W : A) (e : F)
    (h : U * W = e • (W * U)) {M M' : ℕ} (hM : 1 ≤ M) (hM' : 1 ≤ M') (hU : U ^ M = 1) (hW : W ^ M' = 1) :
    ∃ n, 1 ≤ n ∧ (U * W) ^ n = 1 := by
  have h₁ : ∀ i : ℕ, U ^ i * W = e ^ i • (W * U ^ i) := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ', _root_.mul_assoc, ih, mul_smul_comm, ← _root_.mul_assoc, h, smul_mul_assoc, smul_smul,
        _root_.mul_assoc, pow_succ e]
  have h₂ : ∀ n : ℕ, ∃ t : ℕ, (U * W) ^ n = e ^ t • (W ^ n * U ^ n) := by
    intro n
    induction n with
    | zero => exact ⟨0, by simp⟩
    | succ n ih =>
      obtain ⟨t, ht⟩ := ih
      refine ⟨t + (n + 1), ?_⟩
      rw [pow_succ, ht, smul_mul_assoc, _root_.mul_assoc, ← _root_.mul_assoc (U ^ n), ← pow_succ, h₁,
        mul_smul_comm, smul_smul, ← pow_add, ← _root_.mul_assoc, ← pow_succ]
  have h₃ : e ^ M • (1 : A) = 1 := by
    have a := h₁ M
    rw [hU, _root_.one_mul, _root_.mul_one] at a
    obtain ⟨m, rfl⟩ : ∃ m, M' = m + 1 := ⟨M' - 1, by omega⟩
    have b : W ^ m * W = W ^ m * (e ^ M • W) := congrArg _ a
    rw [mul_smul_comm, ← pow_succ, hW] at b
    exact b.symm
  obtain ⟨t, ht⟩ := h₂ (M * M')
  refine ⟨M * M' * M, Nat.one_le_iff_ne_zero.2 (by positivity), ?_⟩
  rw [pow_mul U, hU, one_pow, mul_comm M M', pow_mul W, hW, one_pow, _root_.mul_one] at ht
  rw [mul_comm M M', pow_mul, ht, smul_pow, one_pow, ← pow_mul, mul_comm t M, pow_mul]
  have := congrArg (· ^ t) h₃
  simpa only [smul_pow, one_pow] using this

theorem isAdd_symm {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] {g g' g'' : GtPtF D F} (h : g.IsAdd g' g'') : g'.IsAdd g g'' := by
  rw [isAdd_iff] at h ⊢
  refine ⟨h.1.trans (mul_comm _ _), fun χ y J hJ => ?_⟩
  have C : ∀ x a b, th D (T := TF (R := R) F) y J x a b =
      th D (T := TF (R := R) F) y J x b a := by
    intro x a b
    have := (val_corr hJ D.cub.cubeSymmetric_swap_last (lift x (lift a b)).left).trans
      (val_cub D.cub (lift x (lift a b)) hJ _ _ _)
    refine Eq.trans this ?_
    congr 1 <;> simp [x3]
  rw [C, h.2 χ y J hJ, mul_comm]

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]

theorem exists_scalar (hG : GlobalFnsSt) {k : ℕ} (p : QkPt D.toPre F k)
    (w w' : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε k)))
    (hw : w.IsGen) (hw' : w'.IsGen) (Φ Φ' : Fam D.toPre F k →ₗ[F] Fam D.toPre F k)
    (hΦ : ∀ s, PhiRel D.toPre F k p w s (Φ s)) (hΦ' : ∀ s, PhiRel D.toPre F k p w' s (Φ' s)) :
    ∃ c : F, Φ = c • Φ' := by
  obtain ⟨c, -, hc⟩ := TWM.exists_ratio (F := F) D.toPre.P.isLB w hw w' hw' (fun _ _ _ => rfl)
  refine ⟨c, LinearMap.ext fun s => ?_⟩
  refine phi_unique p w ((phiRel_iff hG p w hw _ _).1 (hΦ s)) ?_
  intro a β hβ T ρ z J hJ
  have h1 := (phiRel_iff hG p w' hw' s (Φ' s)).1 (hΦ' s) a β hβ T ρ z J hJ
  have h2 := hc _ (ρ ≫ fst (TF (R := V) F) D.toPre.P.A).left z J hJ
  rw [LinearMap.smul_apply, sval_smul c (Φ' s) β ρ.left z hJ, h1, val_mul hJ, val_mul hJ]
  simp only [Units.val_mul]
  have alg : ∀ {S : Type} [CommRing S] (g a u x y y' : S), y = g * y' →
      g * (a * (u * (x * y'))) = a * (u * (x * y)) := fun g a u x y y' h => by rw [h]; ring
  exact alg _ _ _ _ _ _ h2

theorem finOrd_iff {k : ℕ} (p : QkPt D.toPre F k)
    (w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε k))) (ζ : F)
    (Φ : Fam D.toPre F k →ₗ[F] Fam D.toPre F k) (hΦ : ∀ s t, PhiRel D.toPre F k p w s t ↔ t = Φ s) :
    FinOrd D F k p w ζ ↔ ∃ M : ℕ, 1 ≤ M ∧ ((ζ • Φ : Module.End F (Fam D.toPre F k)) ^ M) = 1 := by
  constructor
  · rintro ⟨M, hM, H⟩
    refine ⟨M, hM, LinearMap.ext fun s => ?_⟩
    have := H (fun i => ((ζ • Φ : Module.End F (Fam D.toPre F k)) ^ (i : ℕ)) s)
      (fun i => Φ (((ζ • Φ : Module.End F (Fam D.toPre F k)) ^ (i : ℕ)) s)) (fun i => ⟨(hΦ _ _).2 rfl, by
        rw [DVR.isSmul_iff, Fin.val_succ, pow_succ', Module.End.mul_apply, LinearMap.smul_apply]⟩)
    exact fam_ext this
  · rintro ⟨M, hM, hpow⟩
    refine ⟨M, hM, fun ss ts H α j => ?_⟩
    have hstep : ∀ i : Fin M, ss i.succ = (ζ • Φ) (ss i.castSucc) := by
      intro i
      obtain ⟨h1, h2⟩ := H i
      rw [hΦ] at h1
      rw [DVR.isSmul_iff] at h2
      rw [h2, h1, LinearMap.smul_apply]
    have hall : ∀ i : ℕ, ∀ hi : i < M + 1,
        ss ⟨i, hi⟩ = ((ζ • Φ : Module.End F (Fam D.toPre F k)) ^ i) (ss 0) := by
      intro i
      induction i with
      | zero => intro _; rfl
      | succ i ih =>
        intro hi
        rw [pow_succ', Module.End.mul_apply, ← ih (by omega)]
        exact hstep ⟨i, by omega⟩
    have hlast : ss (Fin.last M) = ss 0 := by
      rw [show Fin.last M = ⟨M, Nat.lt_succ_self M⟩ from rfl, hall M (Nat.lt_succ_self M), hpow]
      rfl
    rw [hlast]

theorem exists_pow_scalar (hG : GlobalFnsSt) {k : ℕ} (hk : 1 ≤ k) (p : QkPt D.toPre F k)
    (w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε k))) (hw : w.IsGen)
    (Φ : Module.End F (Fam D.toPre F k)) (hΦ : ∀ s t, PhiRel D.toPre F k p w s t ↔ t = Φ s) :
    ∃ c : F, Φ ^ k = c • 1 := by
  obtain ⟨c, -, hc⟩ := phiPow_of_globalFns hG V _ D F k hk p w hw
  refine ⟨c, LinearMap.ext fun s => ?_⟩
  have := hc (fun i => (Φ ^ (i : ℕ)) s) (fun i => (hΦ _ _).2 (by
    rw [Fin.val_succ, pow_succ', Module.End.mul_apply]; rfl))
  rw [DVR.isSmul_iff] at this
  exact this

end GlobalTheory.ThetaFinOrd

namespace GlobalTheory


open ThetaFinOrd in
theorem finOrd_criteria : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k → (∀ (p : QkPt D.toPre F k) (w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε k))), w.IsGen → ∀ (ζ : F) (Φ : Fam D.toPre F k →ₗ[F] Fam D.toPre F k), (∀ s t, PhiRel D.toPre F k p w s t ↔ t = Φ s) → ∀ (s : Fam D.toPre F k) (M : ℕ), s ≠ 0 → 1 ≤ M → ((ζ • Φ) ^ M) s = s → FinOrd D F k p w ζ) ∧ ∀ (p p₁ p₂ : QkPt D.toPre F k), p₂.y = p.y + p₁.y → p.g.IsAdd p₁.g p₂.g → ∀ (w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε k))) (w₁ : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p₁.g.b) (DegPre.lineε k))) (w₂ : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p₂.g.b) (DegPre.lineε k))), w.IsGen → w₁.IsGen → w₂.IsGen → (∀ s t t' : Fam D.toPre F k, PhiRel D.toPre F k p₁ w₁ s t → PhiRel D.toPre F k p w t t' → PhiRel D.toPre F k p₂ w₂ s t') → ∀ ζ ζ₁ : F, FinOrd D F k p w ζ → FinOrd D F k p₁ w₁ ζ₁ → FinOrd D F k p₂ w₂ (ζ * ζ₁) := by
  intro hL V _ _ _ D F _ _ k hk
  have hG := hL.globalFns
  refine ⟨fun p w hw ζ Φ hΦ s M hs hM hfix => ?_, fun p p₁ p₂ hy hg w w₁ w₂ hw hw₁ hw₂ hc ζ ζ₁ h h₁ => ?_⟩
  · obtain ⟨c, hc⟩ := exists_pow_scalar hG hk p w hw Φ hΦ
    have e : ((ζ • Φ : Module.End F (Fam D.toPre F k)) ^ M) ^ k = ((ζ ^ k * c) ^ M) • 1 := by
      rw [← pow_mul, mul_comm M k, pow_mul, smul_pow, hc, smul_smul, smul_pow, one_pow]
    have f : ∀ n : ℕ, (((ζ • Φ : Module.End F (Fam D.toPre F k)) ^ M) ^ n) s = s := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => rw [pow_succ, Module.End.mul_apply, hfix, ih]
    have g := f k
    rw [e, LinearMap.smul_apply, Module.End.one_apply] at g
    have g' : (ζ ^ k * c) ^ M = 1 := by
      have : ((ζ ^ k * c) ^ M - 1) • s = 0 := by rw [sub_smul, g, one_smul, sub_self]
      exact sub_eq_zero.1 ((smul_eq_zero.1 this).resolve_right hs)
    refine (finOrd_iff p w ζ Φ hΦ).2 ⟨M * k, Nat.one_le_iff_ne_zero.2 (by positivity), ?_⟩
    rw [pow_mul, e, g', one_smul]
  · obtain ⟨Φ, hΦ⟩ := phiFun_of_globalFns hG V _ D F k hk p w hw
    obtain ⟨Φ₁, hΦ₁⟩ := phiFun_of_globalFns hG V _ D F k hk p₁ w₁ hw₁
    obtain ⟨Φ₂, hΦ₂⟩ := phiFun_of_globalFns hG V _ D F k hk p₂ w₂ hw₂
    obtain ⟨w', hw', hc'⟩ := ThetaMul.phi_mul_core hG p₁ p p₂ (hy.trans (add_comm _ _)) (isAdd_symm hg)
      w₁ w hw₁ hw
    have e₂ : Φ₂ = (Φ * Φ₁ : Module.End F (Fam D.toPre F k)) := LinearMap.ext fun s =>
      ((hΦ₂ _ _).1 (hc s _ _ ((hΦ₁ _ _).2 rfl) ((hΦ _ _).2 rfl))).symm
    obtain ⟨e, he⟩ := exists_scalar hG p₂ w₂ w' hw₂ hw' Φ₂ (Φ₁ * Φ : Module.End F (Fam D.toPre F k))
      (fun s => (hΦ₂ _ _).2 rfl) (fun s => hc' s _ _ ((hΦ _ _).2 rfl) ((hΦ₁ _ _).2 rfl))
    obtain ⟨M, hM, hU⟩ := (finOrd_iff p w ζ Φ hΦ).1 h
    obtain ⟨M', hM', hW⟩ := (finOrd_iff p₁ w₁ ζ₁ Φ₁ hΦ₁).1 h₁
    have m : (ζ • Φ : Module.End F (Fam D.toPre F k)) * (ζ₁ • Φ₁ : Module.End F (Fam D.toPre F k)) =
        (ζ * ζ₁) • Φ₂ := by
      rw [e₂, smul_mul_smul_comm]
    obtain ⟨n, hn, hp⟩ := exists_pow_mul_eq_one (F := F) (A := Module.End F (Fam D.toPre F k)) (ζ • Φ) (ζ₁ • Φ₁) e
      (by rw [m, he, smul_mul_smul_comm, smul_comm, mul_comm ζ₁ ζ]) hM hM' hU hW
    rw [m] at hp
    exact (finOrd_iff p₂ w₂ _ Φ₂ hΦ₂).2 ⟨n, hn, hp⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FamilySetupCayleyBound
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselCayleySideBound
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselCayleySideBound
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.MomentPointwise

theorem sum_sq_eq_trace {n : Type} [Fintype n] (A : Matrix n n ℂ) :
    ((∑ i, ∑ j, ‖A i j‖ ^ 2 : ℝ) : ℂ) = (Aᴴ * A).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]
  push_cast
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.conj_mul']

theorem sum_sq_conj {n : Type} [Fintype n] [DecidableEq n] (Q X : Matrix n n ℂ)
    (hQ : Q ∈ Matrix.unitaryGroup n ℂ) :
    ∑ i, ∑ j, ‖(Q * X * Q⁻¹) i j‖ ^ 2 = ∑ i, ∑ j, ‖X i j‖ ^ 2 := by
  have h1 : Qᴴ * Q = 1 := Matrix.mem_unitaryGroup_iff'.1 hQ
  have hinv : Q⁻¹ = Qᴴ := Matrix.inv_eq_left_inv h1
  apply Complex.ofReal_injective
  rw [sum_sq_eq_trace, sum_sq_eq_trace, hinv]
  have : (Q * X * Qᴴ)ᴴ * (Q * X * Qᴴ) = Q * (Xᴴ * X * Qᴴ) := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Qᴴ Q, h1, Matrix.one_mul]
  rw [this, Matrix.trace_mul_comm, Matrix.mul_assoc, h1, Matrix.mul_one]

theorem exp_mem {k r : ℕ} {X : Mx k r} (hX : PI.UpqRep.InLieHpk k r X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ GG k r := by
  refine CCRuleCW.exp_mem_UH (Formalism.QuantumDeterminants.Hpk k r) _ ?_
  have hL : Xᴴ * Formalism.QuantumDeterminants.Hpk k r + Formalism.QuantumDeterminants.Hpk k r * X = 0 := hX
  rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul,
      Matrix.mul_smul, ← smul_add, hL, smul_zero]

theorem one_mem_UW (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : (1 : Mx k r) ∈ Formalism.QuantumDeterminants.UWset k r z := by
  refine ⟨?_, fun a => ⟨Matrix.one_mulVec _, Matrix.one_mulVec _⟩, Matrix.one_mulVec _⟩
  show (1 : Mx k r)ᴴ * Formalism.QuantumDeterminants.Hpk k r * 1 = Formalism.QuantumDeterminants.Hpk k r
  simp

theorem pointwise : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (l : R.H → Wp) (Q : Mx k r) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub), R.IsDS ε mu → SideG k r z π u μW μN μG νq → IsBes R z π l → PI.UpqRep.IsCayleyU k r ε Q → R.IsE Q E → ∀ g ∈ GG k r, ∀ (a : Fin r) (w : R.smSub), (lenA k r z g a.succ / lenA k r z g a.castSucc) ^ 2 * ‖l (R.σ g w)‖ ^ 2 ≤ ∑ c, ∑ e, ‖l (R.σ g (E c e w))‖ ^ 2 := by
  intro hK k r ε mu R Wp _ _ _ _ z π u μW μN μG νq l Q E hR hS hl hQ hE g hg a w
  obtain ⟨hz, hT, ⟨u₀, hπ⟩, -⟩ := hS
  have hπ1 : π 1 = 1 := (Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.piW_facts hT hπ).1
  obtain ⟨hmul, -, -, hsm, -⟩ := GlobalTheory.T.discreteSeries_unitary_smooth_basic hK k r ε mu R hR
  obtain ⟨hact, -, -, hcomp⟩ := GlobalTheory.T.smooth_maps_closure hK k r ε mu mu mu R R R hR hR hR
  obtain ⟨X, hX, hXn, hXt⟩ := GlobalTheory.T.exists_lie_unitary_element_simple_root k r z hz hT g hg a
  obtain ⟨-, -, hexp⟩ := GlobalTheory.T.derivedAction_expand_matrixUnits hK k r ε mu R hR Q E hQ.1.1 hE
  obtain ⟨ladd, lsmul, leq, lcont⟩ := hl
  have hla : 0 ≤ lenA k r z g a.castSucc := Metric.infDist_nonneg
  have hla1 : 0 ≤ lenA k r z g a.succ := Metric.infDist_nonneg
  rcases hla.eq_or_lt with h0 | hpos
  · rw [← h0]
    simp only [div_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
    positivity
  set L := lenA k r z g a.succ with hL
  have badd : ∀ v ∈ R.sm, ∀ v' ∈ R.sm, l (R.σ g (v + v')) = l (R.σ g v) + l (R.σ g v') := by
    intro v hv v' hv'
    rw [map_add (f := _)]; exact ladd _ (hsm g hg v hv) _ (hsm g hg v' hv')
  have bsmul : ∀ (c : ℂ), ∀ v ∈ R.sm, l (R.σ g (c • v)) = c • l (R.σ g v) := by
    intro c v hv
    rw [map_smul]; exact lsmul _ _ (hsm g hg v hv)
  have hder := (GlobalTheory.T.frechetContinuous_continuousOn_orbit_hasDerivAt hK k r ε mu R hR Wp (fun v => l (R.σ g v)) badd bsmul
    (hcomp Wp _ l (hact g hg) lcont) w w.2).2 X hX
  have hfun : (fun t : ℝ => l (R.σ g (R.σ (NormedSpace.exp ((t : ℂ) • X)) w))) =
      fun t : ℝ => Complex.exp (-(2 * (L : ℂ) * (t : ℂ)) * Complex.I) • l (R.σ g w) := by
    funext t
    obtain ⟨m, hm, hgm, hψ⟩ := hXt t
    rw [← hmul g hg _ (exp_mem hX t), hgm, hmul m hm.1 g hg, ← hψ]
    have := leq 1 (one_mem_UW k r z) m hm _ (hsm g hg w w.2)
    rw [Matrix.one_mul, hπ1] at this
    exact this
  have hd2 : HasDerivAt (fun t : ℝ => Complex.exp (-(2 * (L : ℂ) * (t : ℂ)) * Complex.I) • l (R.σ g w))
      ((-(2 * (L : ℂ)) * Complex.I) • l (R.σ g w)) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => -(2 * (L : ℂ) * (t : ℂ)) * Complex.I) (-(2 * (L : ℂ)) * Complex.I) 0 := by
      have := (((Complex.ofRealCLM.hasDerivAt (x := 0)).const_mul (2 * (L : ℂ))).neg).mul_const Complex.I
      simpa using this
    have h2 := h1.cexp.smul_const (l (R.σ g w))
    simpa using h2
  rw [hfun] at hder
  have heq := hd2.unique hder
  let B : R.smSub →ₗ[ℂ] Wp :=
    { toFun := fun v => l (R.σ g v)
      map_add' := fun v v' => badd v v.2 v' v'.2
      map_smul' := fun c v => bsmul c v v.2 }
  have hsum : l (R.σ g (PI.UpqRep.dsig (k := k) (r := r) R.σ X w)) =
      ∑ p : Fin (2 * r + k + 1) × Fin (2 * r + k + 1), (Q * X * Q⁻¹) p.1 p.2 • l (R.σ g (E p.1 p.2 w)) := by
    have h1 : B (∑ c, ∑ e, (Q * X * Q⁻¹) c e • E c e w) = ∑ c, ∑ e, (Q * X * Q⁻¹) c e • B (E c e w) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul]
    rw [Fintype.sum_prod_type, hexp X hX w]
    refine Eq.trans ?_ h1
    show _ = l (R.σ g ((∑ c, ∑ e, (Q * X * Q⁻¹) c e • E c e w : R.smSub) : R.H))
    simp only [Submodule.coe_sum, Submodule.coe_smul]
  have key := Formalism.HermitianLatticeCounting.P.majorant_cauchy_schwarz_holds Wp (Fin (2 * r + k + 1) × Fin (2 * r + k + 1))
    (fun p => (Q * X * Q⁻¹) p.1 p.2) (fun p => l (R.σ g (E p.1 p.2 w))) (l (R.σ g w))
    (-(2 * (L : ℂ)) * Complex.I) 1 _ L hpos (by simp [abs_of_nonneg hla1]) (heq.trans hsum)
    (by rw [Fintype.sum_prod_type, sum_sq_conj Q X hQ.2]; exact hXn)
  rw [Fintype.sum_prod_type, one_mul] at key
  exact key

end GlobalTheory.MomentPointwise
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselCayleySideBoundStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bessel_cayley_side_bound : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (l : R.H → Wp) (Q : Mx k r) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub), R.IsDS ε mu → SideG k r z π u μW μN μG νq → IsBes R z π l → PI.UpqRep.IsCayleyU k r ε Q → R.IsE Q E → ∀ g ∈ GG k r, ∀ (a : Fin r) (w : R.smSub), (lenA k r z g a.succ / lenA k r z g a.castSucc) ^ 2 * ‖l (R.σ g w)‖ ^ 2 ≤ ∑ c, ∑ e, ‖l (R.σ g (E c e w))‖ ^ 2 := by
  first | exact @GlobalTheory.MomentPointwise.pointwise | exact GlobalTheory.MomentPointwise.pointwise | (intros; apply GlobalTheory.MomentPointwise.pointwise <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FamilySetupCayleyBound
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.RatioMoment

theorem iterate_bound {X M ι : Type} [MeasurableSpace X] [NormedAddCommGroup M] [Fintype ι] (μ : Measure X)
    (κ : X → ℝ) (f : M → X → ℝ) (T : ι → ι → M → M) (L : ℕ → M → Prop) (N : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hκ : AEMeasurable κ μ) (hf : ∀ w, AEMeasurable (f w) μ) (hf0 : ∀ w x, 0 ≤ f w x)
    (hpt : ∀ᵐ x ∂μ, ∀ w, κ x ^ 2 * f w x ≤ ∑ c, ∑ e, f (T c e w) x)
    (hL : ∀ j w, L j w → ∀ c e, L (j + 2) (T c e w))
    (hs : ∀ j w, j ≤ N → L j w → ∑ c, ∑ e, ‖T c e w‖ ^ 2 ≤ B ^ 2 * ‖w‖ ^ 2)
    (h0 : ∀ w, ∫⁻ x, ENNReal.ofReal (1 * f w x) ∂μ ≤ ENNReal.ofReal (‖w‖ ^ 2)) :
    ∀ q j, j + 2 * q ≤ N → ∀ w, L j w →
      ∫⁻ x, ENNReal.ofReal (κ x ^ (2 * q) * f w x) ∂μ ≤ ENNReal.ofReal (B ^ (2 * q) * ‖w‖ ^ 2) := by
  intro q
  induction q with
  | zero => intro j _ w _; simpa using h0 w
  | succ q ih =>
    intro j hj w hw
    have hk0 : ∀ x, 0 ≤ κ x ^ (2 * q) := fun x => by rw [pow_mul]; positivity
    have hm : ∀ v, AEMeasurable (fun x => ENNReal.ofReal (κ x ^ (2 * q) * f v x)) μ := fun v =>
      ((hκ.pow_const _).mul (hf v)).ennreal_ofReal
    calc ∫⁻ x, ENNReal.ofReal (κ x ^ (2 * (q + 1)) * f w x) ∂μ
        ≤ ∫⁻ x, ∑ c, ∑ e, ENNReal.ofReal (κ x ^ (2 * q) * f (T c e w) x) ∂μ := by
          refine lintegral_mono_ae ?_
          filter_upwards [hpt] with x hx
          have h1 : κ x ^ (2 * (q + 1)) * f w x ≤ ∑ c, ∑ e, κ x ^ (2 * q) * f (T c e w) x := by
            have := mul_le_mul_of_nonneg_left (hx w) (hk0 x)
            simp only [Finset.mul_sum] at this
            calc κ x ^ (2 * (q + 1)) * f w x = κ x ^ (2 * q) * (κ x ^ 2 * f w x) := by ring
              _ ≤ _ := this
          refine (ENNReal.ofReal_le_ofReal h1).trans (le_of_eq ?_)
          rw [ENNReal.ofReal_sum_of_nonneg
            (fun c _ => Finset.sum_nonneg fun e _ => mul_nonneg (hk0 x) (hf0 _ x))]
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [ENNReal.ofReal_sum_of_nonneg (fun e _ => mul_nonneg (hk0 x) (hf0 _ x))]
      _ = ∑ c, ∑ e, ∫⁻ x, ENNReal.ofReal (κ x ^ (2 * q) * f (T c e w) x) ∂μ := by
          rw [lintegral_finsetSum' _ (fun c _ => Finset.aemeasurable_fun_sum _ fun e _ => hm _)]
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [lintegral_finsetSum' _ (fun e _ => hm _)]
      _ ≤ ∑ c, ∑ e, ENNReal.ofReal (B ^ (2 * q) * ‖T c e w‖ ^ 2) :=
          Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun e _ =>
            ih (j + 2) (by omega) _ (hL j w hw c e)
      _ = ENNReal.ofReal (∑ c, ∑ e, B ^ (2 * q) * ‖T c e w‖ ^ 2) := by
          rw [ENNReal.ofReal_sum_of_nonneg
            (fun c _ => Finset.sum_nonneg fun e _ => by positivity)]
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [ENNReal.ofReal_sum_of_nonneg (fun e _ => by positivity)]
      _ ≤ ENNReal.ofReal (B ^ (2 * (q + 1)) * ‖w‖ ^ 2) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have := mul_le_mul_of_nonneg_left (hs j w (by omega) hw) (pow_nonneg hB (2 * q))
          simp only [Finset.mul_sum] at this
          calc _ ≤ _ := this
            _ = _ := by ring

theorem ratio_moment : Hyps → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (l : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ) (Q : Mx k r) (E : ∀ ν, Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ (R ν).smSub), Setup lam u b bv ga h q0 z π μW μN μG νq R l dg → PI.UpqRep.IsCayleyU k r (PI.BesselPeriodGGP.eps48 k r) Q → (∀ ν, n1 ν ≤ q0 → (R ν).IsE Q (E ν) ∧ Formalism.REAL.GlRel (E ν)) → ∀ ν, n1 ν ≤ q0 → ∀ (j q : ℕ), j + 2 * q ≤ 4 * (2 * r + k + 1) ^ 2 → ∀ (a : Fin r) (w : (R ν).smSub), Lev (PI.BesselPeriodGGP.eps48 k r) (E ν) (fun a => lam a + ((ν : Fin (2 * r + k + 1) → ℤ) a : ℝ)) j w → ∫⁻ x, ENNReal.ofReal ((lenA k r z (Matrix.of x) a.succ / lenA k r z (Matrix.of x) a.castSucc) ^ (2 * q) * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal ((b ^ 2) ^ (2 * q) * ‖w‖ ^ 2) := by
  intro hH k r Wp _ _ _ _ lam u b bv ga h q0 z π μW μN μG νq R l dg Q E hS hQ hE ν hν j q hjq a w hw
  have hK : PI.KFinSmooth := hH.1.2.2.1
  have hmass := (GlobalTheory.T.bessel_functional_l2_bound_and_isometry hH k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg hS ν hν).1
  obtain ⟨hNum, hFam, hG, hSF⟩ := hS
  have hDS := hFam ν hν
  obtain ⟨hBe, hdg, -⟩ := hSF ν hν
  obtain ⟨hae, -, hlen, hl⟩ := GlobalTheory.T.quotientMeasure_ae_mem_and_measurable_besselModel hK k r _ _ (R ν) Wp z π u μW μN μG νq hDS hG
  have hMod := GlobalTheory.T.cayley_endomorphisms_modular hH k r _ _ (R ν) hNum.1 hDS Q (E ν) hQ (hE ν hν).1
  obtain ⟨⟨hbv, -⟩, hsh⟩ := GlobalTheory.NumFam.num_fam k r lam u b bv ga h q0 hNum
  have hShape := (hsh ν hν).2.1
  refine iterate_bound νq
    (fun x => lenA k r z (Matrix.of x) a.succ / lenA k r z (Matrix.of x) a.castSucc)
    (fun (v : (R ν).smSub) x => dg ν * ‖l ν ((R ν).σ (Matrix.of x) v)‖ ^ 2) (fun c e v => E ν c e v)
    (Lev (PI.BesselPeriodGGP.eps48 k r) (E ν) (fun a => lam a + (ν a : ℝ)))
    (4 * (2 * r + k + 1) ^ 2) (b ^ 2) (by positivity) ((hlen _).div (hlen _))
    (fun v => (((hl (l ν) hBe.1 v v.2).norm.aemeasurable).pow_const 2).const_mul _)
    (fun v x => by positivity) ?_
    (fun i v hv c e => GlobalTheory.lev_E_add_two _ _ _ _ _ i v hMod.1 hMod.2.1 hv c e)
    (fun i v hi hv => ?_) (fun v => hmass v v.2) q j hjq w hw
  · filter_upwards [hae] with x hx v
    have h1 := mul_le_mul_of_nonneg_left
      (GlobalTheory.T.bessel_cayley_side_bound hK k r _ _ (R ν) Wp z π u μW μN μG νq (l ν) Q (E ν) hDS hG hBe.1 hQ (hE ν hν).1
        _ hx a v) hdg.le
    simp only [Finset.mul_sum] at h1
    calc _ = _ := by ring
      _ ≤ _ := h1
  · have h1 := GlobalTheory.T.unitaryGlModule_level_sum_norm_sq_le _ _ _ _ _ k i bv b v hMod hShape hbv hi hv
    calc _ ≤ _ := h1
      _ = _ := by ring

end GlobalTheory.RatioMoment
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FamilySetupCayleyBoundStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.family_setup_cayley_bound : Hyps → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (l : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ) (Q : Mx k r) (E : ∀ ν, Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ (R ν).smSub), Setup lam u b bv ga h q0 z π μW μN μG νq R l dg → PI.UpqRep.IsCayleyU k r (PI.BesselPeriodGGP.eps48 k r) Q → (∀ ν, n1 ν ≤ q0 → (R ν).IsE Q (E ν) ∧ Formalism.REAL.GlRel (E ν)) → ∀ ν, n1 ν ≤ q0 → ∀ (j q : ℕ), j + 2 * q ≤ 4 * (2 * r + k + 1) ^ 2 → ∀ (a : Fin r) (w : (R ν).smSub), Lev (PI.BesselPeriodGGP.eps48 k r) (E ν) (fun a => lam a + ((ν : Fin (2 * r + k + 1) → ℤ) a : ℝ)) j w → ∫⁻ x, ENNReal.ofReal ((lenA k r z (Matrix.of x) a.succ / lenA k r z (Matrix.of x) a.castSucc) ^ (2 * q) * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal ((b ^ 2) ^ (2 * q) * ‖w‖ ^ 2) := by
  first | exact @GlobalTheory.RatioMoment.ratio_moment | exact GlobalTheory.RatioMoment.ratio_moment | (intros; apply GlobalTheory.RatioMoment.ratio_moment <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsPointOfIffThick
noncomputable section

namespace GlobalTheory.TorusModel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.FormalPoint GlobalTheory.AdicColimit
open scoped CategoryTheory.Obj

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
  {T T' : Over (Spec (CommRingCat.of R))}

variable {U} in
theorem hasCoords_pull {e : ℕ} {k : T' ⟶ T} {g : GtPt D.toPre T} {g' : GtPt D.toPre T'}
    (h : GtPt.IsPull k.left g g') {Z : Scheme.{0}} {r : Z ⟶ T'.left} {y : Z ⟶ (thickObj R I e G).left} :
    HasCoords U e g (r ≫ k.left) y ↔ HasCoords U e g' r y := by
  rw [hasCoords_iff, hasCoords_iff, h.1, Category.assoc]
  refine and_congr Iff.rfl (forall_congr' fun χ => forall_congr' fun z => forall_congr' fun J =>
    forall_congr' fun hJ => ?_)
  rw [(val_corr hJ (h.2 χ) r).trans (val_pull hJ _ _ _)]

variable {U} in
theorem eq_of_hasCoords {e : ℕ} {g g' : GtPt D.toPre T} {y : T.left ⟶ (thickObj R I e G).left}
    (h : HasCoords U e g (𝟙 _) y) (h' : HasCoords U e g' (𝟙 _) y) : g = g' := by
  rw [hasCoords_iff, Category.id_comp] at h h'
  exact pt_ext (Over.OverMorphism.ext (h.1.symm.trans h'.1)) fun χ z J hJ => (h.2 χ z J hJ).symm.trans (h'.2 χ z J hJ)

theorem isPointOf_iff_thick (g : GtPt D.toPre T) (x : T ⟶ G) :
    IsPointOf U g x ↔ ∀ e, HasCoords U e g (thickι I e T) (thickHom I e x) := by
  refine ⟨fun h e => h e _ _ _ (thickHom_ι I e x), fun h e Z r y hy => ?_⟩
  have w : r ≫ T.hom = (y ≫ (thickObj R I e G).hom) ≫ thick R I e := by
    rw [← Over.w x, ← Category.assoc, ← hy, Category.assoc, Over.w (fstG I e G), Category.assoc]; rfl
  obtain ⟨l, rfl⟩ : ∃ l, l ≫ thickι I e T = r := ⟨pullback.lift r _ w, pullback.lift_fst _ _ _⟩
  obtain rfl : y = l ≫ thickHom I e x := by
    rw [← cancel_mono (thickι I e G), Category.assoc, thickHom_ι]
    exact hy.trans (Category.assoc _ _ _)
  exact (h e).comp l

theorem existsUnique_point (hT : IsAdicColimit I T) (g : GtPt D.toPre T) : ∃! x : T ⟶ G, IsPointOf U g x := by
  choose y hy using fun e =>
    exists_hasCoords U e g (thickι I e T) (thickObj R I e T).hom pullback.condition.symm
  refine existsUnique_of_exists_of_unique ?_ fun x x' h h' => Over.OverMorphism.ext (hT.hom_ext fun e =>
    (h.comp_fstG_eq (hy e)).symm.trans (h'.comp_fstG_eq (hy e)))
  obtain ⟨x, hx, -⟩ := hT G.left (fun e => y e ≫ thickι I e G) fun e => by
    have h₁ := (hy (e + 1)).comp (thickMap R I e T)
    rw [thickMap_ι] at h₁
    rw [← Category.assoc, h₁.unique (hy e).succ, Category.assoc, thickMap_ι]
  have hw : x ≫ G.hom = T.hom := hT.hom_ext fun e => by
    have h₁ : thickι I e G ≫ G.hom = (U.gt e).pG.left ≫ D.toPre.P.A.hom :=
      (Over.w (fstG I e G)).trans (Over.w (U.gt e).pG).symm
    rw [reassoc_of% hx e, h₁, reassoc_of% (hy e).1, Over.w]
  refine ⟨Over.homMk x hw, (isPointOf_iff_thick U g _).2 fun e => ?_⟩
  have : thickHom I e (Over.homMk x hw : T ⟶ G) = y e := by
    rw [← cancel_mono (thickι I e G), thickHom_ι]
    exact hx e
  rw [this]
  exact hy e

variable {H : Over (Spec (CommRingCat.of R))} [GrpObj H] {Φ : ∀ T, (T ⟶ H) ≃ GtPt D.toPre T}

theorem existsUnique_lift (hΦ : Represents Φ) (hT : IsAdicColimit I T) (x : T ⟶ G) :
    ∃! w : T ⟶ H, IsPointOf U (Φ T w) x := by
  have pl : ∀ (e : ℕ) (w : T ⟶ H), HasCoords U e (Φ T w) (thickι I e T) (thickHom I e x) ↔
      HasCoords U e (Φ _ (fstG I e T ≫ w)) (𝟙 _) (thickHom I e x) := fun e w => by
    rw [← hasCoords_pull (hΦ.1 _ _ (fstG I e T) w), Category.id_comp]; rfl
  refine existsUnique_of_exists_of_unique ?_ fun w w' h h' => Over.OverMorphism.ext (hT.hom_ext fun e =>
    congrArg (·.left) ((Φ _).injective (eq_of_hasCoords ((pl e w).1 ((isPointOf_iff_thick U _ x).1 h e))
      ((pl e w').1 ((isPointOf_iff_thick U _ x).1 h' e)))))
  have ex : ∀ e, ∃ w : (Over.map (thick R I e)).obj (thickObj R I e T) ⟶ H,
      HasCoords U e (Φ _ w) (𝟙 _) (thickHom I e x) := fun e => by
    obtain ⟨ξ, hξ⟩ := TorusCoord.exists_isPointOf (U.gt e) (T := (Over.map (thick R I e)).obj (thickObj R I e T))
      (thickHom I e x) (by rw [← Category.assoc, Over.w]; rfl)
    refine ⟨(Φ _).symm ξ, ?_⟩
    rw [Equiv.apply_symm_apply, hasCoords_iff]
    refine ⟨hξ.1.symm.trans (Category.id_comp _).symm, fun χ z J hJ => ?_⟩
    have := (val_corr hJ (hξ.2 χ) (𝟙 _)).trans (val_pull hJ _ _ _)
    rw [Category.id_comp] at this
    exact this.symm
  choose w hw using ex
  obtain ⟨v, hv, -⟩ := hT H.left (fun e => (w e).left) fun e => by
    let m : (Over.map (thick R I e)).obj (thickObj R I e T) ⟶
        (Over.map (thick R I (e + 1))).obj (thickObj R I (e + 1) T) := Over.homMk (thickMap R I e T)
      (((congrArg (thickMap R I e T ≫ ·) (Over.w (fstG I (e + 1) T)).symm).trans
        (thickMap_ι_assoc I e T T.hom)).trans (Over.w (fstG I e T)))
    have h₁ := (hw (e + 1)).comp (thickMap R I e T)
    rw [thickMap_thickHom, Category.comp_id, ← Category.id_comp (thickMap R I e T)] at h₁
    have h₂ := (hasCoords_pull (hΦ.1 _ _ m (w (e + 1)))).1 h₁
    exact congrArg (·.left) ((Φ _).injective (eq_of_hasCoords h₂ (hw e).succ))
  have hv' : v ≫ H.hom = T.hom := hT.hom_ext fun e => by
    rw [reassoc_of% hv e, Over.w]
    exact (Over.w (fstG I e T)).symm
  refine ⟨Over.homMk v hv', (isPointOf_iff_thick U _ x).2 fun e => (pl e _).2 ?_⟩
  have : fstG I e T ≫ (Over.homMk v hv' : T ⟶ H) = w e := Over.OverMorphism.ext (hv e)
  rw [this]
  exact hw e

theorem exists_mulEquiv (hG : GlobalFnsSt) (hΦ : Represents Φ) :
    ∃ J : ∀ T, IsAdicColimit I T → ((T ⟶ H) ≃* (T ⟶ G)),
      ∀ T hT w x, J T hT w = x ↔ IsPointOf U (Φ T w) x := by
  choose j hj hu using fun T (hT : IsAdicColimit I T) (w : T ⟶ H) => existsUnique_point U hT (Φ T w)
  have bij : ∀ T hT, Function.Bijective (j T hT) := fun T hT => (Function.bijective_iff_existsUnique _).2 fun x =>
    (existsUnique_congr fun w => ⟨fun h => (hu T hT w x h).symm, fun h => h ▸ hj T hT w⟩).1
      (existsUnique_lift U hΦ hT x)
  exact ⟨fun T hT => MulEquiv.mk' (Equiv.ofBijective _ (bij T hT)) fun w w' =>
      (hu T hT _ _ ((hj T hT w).mul hG (hj T hT w') (hΦ.2 T w w'))).symm,
    fun T hT w x => ⟨fun h => h ▸ hj T hT w, fun h => (hu T hT w x h).symm⟩⟩

end GlobalTheory.TorusModel
end
end
