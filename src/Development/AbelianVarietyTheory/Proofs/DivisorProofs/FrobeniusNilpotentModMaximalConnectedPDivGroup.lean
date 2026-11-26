module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelOneDefectsIndependentModMaximal

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmLevelOneDefectFrobeniusPow
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmLevelOneDefectFrobeniusPow
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrobPowDefect

theorem adicComplete_ring {O A : Type} [CommRing O] [CommRing A] [Algebra O A]
    (p : ℕ) [h : IsAdicComplete (Ideal.span {(p : O)}) A] :
    IsAdicComplete (Ideal.span {(p : A)}) A := by
  have key : ∀ (n : ℕ) (x : A), x ∈ (Ideal.span {(p : A)} ^ n • ⊤ : Submodule A A) ↔
      x ∈ (Ideal.span {(p : O)} ^ n • ⊤ : Submodule O A) := by
    intro n x
    rw [GlobalTheory.mem_span_singleton_pow_smul_top_iff_exists, GlobalTheory.mem_span_singleton_pow_smul_top_iff_exists]
    simp [Algebra.smul_def]
  exact
    { haus' := fun x hx => IsHausdorff.haus h.toIsHausdorff x fun n =>
        SModEq.sub_mem.2 ((key n _).1 (SModEq.sub_mem.1 (hx n)))
      prec' := fun f hf => by
        obtain ⟨L, hL⟩ := IsPrecomplete.prec h.toIsPrecomplete (f := f) fun {m n} hmn =>
          SModEq.sub_mem.2 ((key _ _).1 (SModEq.sub_mem.1 (hf hmn)))
        exact ⟨L, fun n => SModEq.sub_mem.2 ((key _ _).2 (SModEq.sub_mem.1 (hL n)))⟩ }

theorem pow_sub_expand_mem (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] (t : B →+* B)
    (ht : ∀ b, (p : B) ∣ t b - b ^ p) (hu : ¬IsUnit (p : B)) {τ : Type} (w : MvPowerSeries τ B)
    (α : τ →₀ ℕ) :
    coeff α (w ^ p - expand p (Fact.out : p.Prime).ne_zero (map t w)) ∈
      Ideal.span {(p : B)} := by
  set I : Ideal B := Ideal.span {(p : B)}
  haveI : CharP (B ⧸ I) p := CharP.quotient B p (by simpa [mem_nonunits_iff] using hu)
  haveI : ExpChar (B ⧸ I) p := ExpChar.prime Fact.out
  have hw : map (Ideal.Quotient.mk I) (map t w) =
      map (frobenius (B ⧸ I) p) (map (Ideal.Quotient.mk I) w) := by
    ext n
    simp only [coeff_map, frobenius_def]
    rw [← map_pow, Ideal.Quotient.eq, Ideal.mem_span_singleton]
    exact ht _
  have key : map (Ideal.Quotient.mk I)
      (w ^ p - expand p (Fact.out : p.Prime).ne_zero (map t w)) = 0 := by
    rw [map_sub, map_pow, map_expand, hw, ← map_expand, map_frobenius_expand, sub_self]
  have := congrArg (coeff α) key
  rwa [coeff_map, map_zero, Ideal.Quotient.eq_zero_iff_mem] at this

theorem exists_eq_p_mul {B : Type} [CommRing B] (p : ℕ) {τ : Type} (w : MvPowerSeries τ B)
    (hw : ∀ α, coeff α w ∈ Ideal.span {(p : B)}) :
    ∃ w' : MvPowerSeries τ B, w = (p : MvPowerSeries τ B) * w' := by
  have h : ∀ α, ∃ b, coeff α w = (p : B) * b := fun α => Ideal.mem_span_singleton'.1 (hw α) |>.imp
    fun b hb => by rw [← hb, mul_comm]
  choose e he using h
  let w' : MvPowerSeries τ B := e
  refine ⟨w', ?_⟩
  ext α
  rw [← map_natCast (C (σ := τ) (R := B)) p, coeff_C_mul]
  exact he α

end GlobalTheory.FrobPowDefect

namespace GlobalTheory.FrobPowDefect

theorem ev_one_subst_nmul (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] (hv : v.Integers O) (G : PDivGroup p O)
    (d : ℕ) (c : QLog.Chart G d) (s : MvPowerSeries (Fin d) O) (hs : constantCoeff s = 0) :
    c.ev 1 (subst (nmul c.μ p) s) = 0 := by
  haveI : IsAdicComplete (Ideal.span {(p : O)}) (G.A 1) :=
    GlobalTheory.isAdicComplete_of_finite_projective _ _
  haveI : IsAdicComplete (Ideal.span {(p : G.A 1)}) (G.A 1) := adicComplete_ring (O := O) p
  have hT := (GlobalTheory.CEval.continuous_eval p O (G.A 1) (Fin d) (c.x 1) (c.nil 1)).2
    (c.ev 1) (c.isEval 1)
  let E' : MvPowerSeries (Fin d) O →ₐ[O] G.A 1 :=
    { (algebraMap O (G.A 1)).comp (constantCoeff : MvPowerSeries (Fin d) O →+* O) with
      commutes' := fun r => by
        show algebraMap O (G.A 1) (constantCoeff (algebraMap O (MvPowerSeries (Fin d) O) r)) = _
        rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, constantCoeff_C] }
  have hE'apply : ∀ f, E' f = algebraMap O (G.A 1) (constantCoeff f) := fun _ => rfl
  have hu : ∀ j, constantCoeff (nmul c.μ p j) = 0 :=
    GlobalTheory.MapNMul.cc_nmul c.μ (fun j => c.isLaw.const j) p
  have hpt : ∀ j, c.ev 1 (nmul c.μ p j) = 0 := fun j => by
    have h1 := G.mulBy_pow_self 1 (c.x 1 j)
    rw [pow_one] at h1
    rw [GlobalTheory.T.pDivGroupFormalChart_ev_natMultiple_eq_convPower p C v O hv G d c 1 p j, h1, c.aug 1 j, map_zero]
  have hE' : IsEval p (fun j => c.ev 1 (nmul c.μ p j)) E' := by
    constructor
    · intro j
      show _ = c.ev 1 (nmul c.μ p j)
      rw [hE'apply, constantCoeff_X, map_zero, hpt]
    · intro m
      refine ⟨1, fun f hf => ?_⟩
      have h0 : constantCoeff f = 0 := by
        rw [← coeff_zero_eq_constantCoeff_apply]
        exact hf 0 (by simp)
      rw [hE'apply, h0, map_zero]
      exact dvd_zero _
  rw [hT.1 (Fin d) (nmul c.μ p) E' hu hE' s, hE'apply, hs, map_zero]

end GlobalTheory.FrobPowDefect

namespace GlobalTheory.FrobPowDefect

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q]

theorem frob_eq_expand' (p : ℕ) (hp : p ≠ 0) {σ : Type} (s : Q →+* Q) (f : MvPowerSeries σ Q) :
    frob p s f = expand p hp (map s f) := by
  simp only [frob, expand, substAlgHom_apply]

theorem defect_frob (p : ℕ) (hp : p ≠ 0) (t : B →+* B) (s : Q →+* Q)
    (hs : ∀ b, s (algebraMap B Q b) = algebraMap B Q (t b)) {d : ℕ}
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B) (h0 : ∀ i, constantCoeff (nmul μ p i) = 0)
    (f : MvPowerSeries (Fin d) Q) :
    defect μ p (frob p s f) = expand p hp (map s (defect μ p f)) +
      (subst (up Q fun i => expand p hp (map t (nmul μ p i))) (map s f) -
        subst (up Q fun i => nmul μ p i ^ p) (map s f)) := by
  have hU : HasSubst (up Q (nmul μ p)) := hasSubst_of_constantCoeff_zero fun i => by
    simp [up, constantCoeff_map, h0]
  have hV : HasSubst (up Q fun i => map t (nmul μ p i)) := hasSubst_of_constantCoeff_zero fun i => by
    simp [up, constantCoeff_map, h0]
  have hXp : HasSubst (fun i : Fin d => (X i : MvPowerSeries (Fin d) Q) ^ p) := HasSubst.X_pow hp
  have hexp : ∀ (g : MvPowerSeries (Fin d) Q), expand p hp g = subst (fun i => X i ^ p) g :=
    fun g => by simp only [expand, substAlgHom_apply]
  have e1 : subst (up Q (nmul μ p)) (expand p hp (map s f)) =
      subst (up Q fun i => nmul μ p i ^ p) (map s f) := by
    rw [hexp, subst_comp_subst_apply hXp hU]
    congr 1
    funext i
    rw [subst_pow hU, subst_X hU]
    simp [up, map_pow]
  have hmapU : (fun i => map s (up Q (nmul μ p) i)) = up Q (fun i => map t (nmul μ p i)) := by
    funext i; ext n; simp [up, coeff_map, hs]
  have m1 : map s (subst (up Q (nmul μ p)) f) = subst (up Q fun i => map t (nmul μ p i)) (map s f) := by
    rw [map_subst hU, hmapU]
  have x1 : expand p hp (subst (up Q fun i => map t (nmul μ p i)) (map s f)) =
      subst (up Q fun i => expand p hp (map t (nmul μ p i))) (map s f) := by
    rw [expand_subst p hp hV]; congr 1; funext i; simp [up, map_expand]
  have hsm : map s ((p : Q) • f) = (p : Q) • map s f := by
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, map_nsmul]
  rw [frob_eq_expand' p hp, defect, defect, e1, map_sub, hsm, m1, map_sub, map_smul, x1]
  abel

end GlobalTheory.FrobPowDefect

namespace GlobalTheory.FrobPowDefect

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q]

theorem defect_sub {d : ℕ} (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B) (n : ℕ)
    (h0 : ∀ i, constantCoeff (nmul μ n i) = 0) (f g : MvPowerSeries (Fin d) Q) :
    defect μ n (f - g) = defect μ n f - defect μ n g := by
  have hU : HasSubst (up Q (nmul μ n)) := hasSubst_of_constantCoeff_zero fun i => by
    simp [up, constantCoeff_map, h0]
  unfold defect
  rw [← coe_substAlgHom hU, map_sub, smul_sub]
  abel

theorem defect_map {d : ℕ} (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B) (n : ℕ)
    (h0 : ∀ i, constantCoeff (nmul μ n i) = 0) (h : MvPowerSeries (Fin d) B) :
    defect μ n (map (algebraMap B Q) h) =
      map (algebraMap B Q) ((n : B) • h - subst (nmul μ n) h) := by
  have hU : HasSubst (nmul μ n) := hasSubst_of_constantCoeff_zero h0
  unfold defect
  rw [map_sub, map_subst hU]
  congr 1
  rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, map_nsmul]

end GlobalTheory.FrobPowDefect

namespace GlobalTheory.QLog


open GlobalTheory.FrobPowDefect in
theorem defect_frob_pow : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (f g : MvPowerSeries (Fin d) F.Q) (a b : MvPowerSeries (Fin d) F.B), QL μ' ⊤ f → QL μ' ⊤ g → In (⊤ : Ideal F.B) (frob p F.s f - g) → map (algebraMap F.B F.Q) a = defect μ' p f → map (algebraMap F.B F.Q) b = defect μ' p g → c.ev 1 (map F.θ b) - c.ev 1 (map F.θ a) ^ p ∈ Ideal.span (algebraMap O (G.A 1) '' {o | ¬IsUnit o}) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F G d c μ' hμ hθμ f g a b hf hg hfg ha hb
  have hpp : p.Prime := Fact.out
  have hp : p ≠ 0 := hpp.ne_zero
  have hnu : ¬IsUnit (p : O) := Fact.out
  have huB : ¬IsUnit (p : F.B) := fun h => hnu (by simpa using h.map F.θ)
  have hinj : ∀ x y : MvPowerSeries (Fin d) F.B,
      map (algebraMap F.B F.Q) x = map (algebraMap F.B F.Q) y → x = y := fun x y h => by
    ext α
    exact F.frame.inj (by simpa [coeff_map] using congrArg (coeff α) h)
  have hc : ∀ i, constantCoeff (nmul μ' p i) = 0 := GlobalTheory.MapNMul.cc_nmul μ' hμ.const p

  choose e _ he using hfg
  let h₀ : MvPowerSeries (Fin d) F.B := e
  have hh₀ : map (algebraMap F.B F.Q) h₀ = frob p F.s f - g := by
    ext α; rw [coeff_map]; exact (he α).symm
  have hh₀c : constantCoeff h₀ = 0 := by
    apply F.frame.inj
    have h1 := congrArg constantCoeff hh₀
    rw [constantCoeff_map] at h1
    rw [h1, map_zero, map_sub, hg.1, frob_eq_expand' p hp, constantCoeff_expand, constantCoeff_map,
      hf.1, map_zero, sub_zero]

  have hJ : ∀ x ∈ Ideal.span {(p : F.B)}, ∃ y ∈ Ideal.span {(p : F.B)}, x ^ p = p * y := by
    intro x hx
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    have e' : (p : F.B) ^ p = p * p ^ (p - 1) := by
      rw [← pow_succ']; congr 1; have := hpp.one_lt; omega
    refine ⟨(p : F.B) ^ (p - 1) * r ^ p, Ideal.mul_mem_right _ _
      (Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) _ (by have := hpp.one_lt; omega)), ?_⟩
    rw [mul_pow, e']; ring
  have hD : DIn (⊤ : Ideal F.B) (map F.s f) := by
    have h := GlobalTheory.T.divided_in_of_quasi_logarithm p F.B O F.Q F.θ F.frame d μ' hμ ⊤ f hf
    intro α i
    obtain ⟨r, _, e'⟩ := h α i
    exact ⟨F.σ r, trivial, by rw [coeff_map, ← map_natCast F.s, ← map_mul, e', F.s_alg]⟩
  have hK := GlobalTheory.KatzCongr.subst_sub_in p F.B O F.Q F.θ F.frame _ hJ (Fin d) (Fin d) ⊤ (map F.s f)
    (fun i => nmul μ' p i ^ p) (fun i => expand p hp (map F.σ (nmul μ' p i))) hD
    (fun i => by rw [map_pow, hc i, zero_pow hp])
    (fun i => by rw [constantCoeff_expand, constantCoeff_map, hc i, map_zero])
    (fun i α => pow_sub_expand_mem p F.σ F.σ_pow huB (nmul μ' p i) α)
  rw [Ideal.mul_top] at hK
  choose k hkJ hk using hK
  let kB : MvPowerSeries (Fin d) F.B := k
  have hkB : map (algebraMap F.B F.Q) kB =
      subst (up F.Q fun i => nmul μ' p i ^ p) (map F.s f) -
        subst (up F.Q fun i => expand p hp (map F.σ (nmul μ' p i))) (map F.s f) := by
    ext α; rw [coeff_map]; exact (hk α).symm

  have hg' : g = frob p F.s f - map (algebraMap F.B F.Q) h₀ := by rw [hh₀]; abel
  have hfa : expand p hp (map F.s (defect μ' p f)) =
      map (algebraMap F.B F.Q) (expand p hp (map F.σ a)) := by
    rw [← ha, map_expand, map_map, map_map,
      show F.s.comp (algebraMap F.B F.Q) = (algebraMap F.B F.Q).comp F.σ from RingHom.ext F.s_alg]
  have heq : map (algebraMap F.B F.Q) b = map (algebraMap F.B F.Q)
      (expand p hp (map F.σ a) - kB - ((p : F.B) • h₀ - subst (nmul μ' p) h₀)) := by
    rw [hb, hg', defect_sub μ' p hc, defect_frob p hp F.σ F.s F.s_alg μ' hc f, defect_map μ' p hc,
      hfa]
    simp only [map_sub, hkB]
    abel
  have hbeq := hinj _ _ heq
  set T := subst (nmul μ' p) h₀ with hT
  have hW : ∀ α, coeff α (b - a ^ p - T) ∈ Ideal.span {(p : F.B)} := by
    intro α
    have e' : b - a ^ p - T = -(a ^ p - expand p hp (map F.σ a)) - kB - (p : F.B) • h₀ := by
      rw [hbeq]; abel
    rw [e']
    simp only [map_sub, map_neg, coeff_smul, smul_eq_mul]
    refine sub_mem (sub_mem (neg_mem (pow_sub_expand_mem p F.σ F.σ_pow huB a α)) (hkJ α)) ?_
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  obtain ⟨w', hw'⟩ := exists_eq_p_mul p _ hW
  have hT0 : c.ev 1 (map F.θ T) = 0 := by
    have hs : HasSubst (nmul μ' p) := hasSubst_of_constantCoeff_zero hc
    have hm : (fun i => map F.θ (nmul μ' p i)) = nmul c.μ p := by
      funext i
      rw [GlobalTheory.MapNMul.map_nmul F.B O F.θ d μ' hμ.const p i]
      congr 1
      funext j
      exact hθμ j
    rw [hT, map_subst hs, hm]
    exact ev_one_subst_nmul p C v O hv G d c _ (by rw [constantCoeff_map, hh₀c, map_zero])
  have key : b = a ^ p + T + (p : MvPowerSeries (Fin d) F.B) * w' := by
    linear_combination hw'
  rw [key]
  simp only [map_add (f := _), map_mul, map_pow, map_natCast]
  rw [hT0]
  have e' : c.ev 1 (map F.θ a) ^ p + 0 + (p : G.A 1) * c.ev 1 (map F.θ w') -
      c.ev 1 (map F.θ a) ^ p = algebraMap O (G.A 1) (p : O) * c.ev 1 (map F.θ w') := by
    rw [map_natCast]; ring
  rw [e']
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨p, hnu, rfl⟩)

end GlobalTheory.QLog
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmLevelOneDefectFrobeniusPowStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasiLogarithm_levelOne_defect_frobenius_pow : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (f g : MvPowerSeries (Fin d) F.Q) (a b : MvPowerSeries (Fin d) F.B), QL μ' ⊤ f → QL μ' ⊤ g → In (⊤ : Ideal F.B) (frob p F.s f - g) → map (algebraMap F.B F.Q) a = defect μ' p f → map (algebraMap F.B F.Q) b = defect μ' p g → c.ev 1 (map F.θ b) - c.ev 1 (map F.θ a) ^ p ∈ Ideal.span (algebraMap O (G.A 1) '' {o | ¬IsUnit o}) := by
  first | exact @GlobalTheory.QLog.defect_frob_pow | exact GlobalTheory.QLog.defect_frob_pow | (intros; apply GlobalTheory.QLog.defect_frob_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffQuasiLogarithmMultiplicationDefect
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffQuasiLogarithmMultiplicationDefect
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.QLogDefect

theorem constantCoeff_defect : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ f : MvPowerSeries (Fin d) Q, QL μ ⊤ f → ∀ n : ℕ, constantCoeff (defect μ n f) = 0 := by
  intro p _ B O Q _ _ _ _ θ _ d μ hμ f hf n
  have hU : ∀ j, constantCoeff (up Q (nmul μ n) j) = 0 := by
    intro j
    simp only [up]
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      constantCoeff_nmul hμ.const n j, map_zero]
  unfold defect
  rw [map_sub, constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hU) hU hf.1, sub_zero]
  simp [hf.1]

end GlobalTheory.QLogDefect
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffQuasiLogarithmMultiplicationDefectStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constantCoeff_quasiLogarithmMultiplicationDefect : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ f : MvPowerSeries (Fin d) Q, QL μ ⊤ f → ∀ n : ℕ, constantCoeff (defect μ n f) = 0 := by
  first | exact @GlobalTheory.QLogDefect.constantCoeff_defect | exact GlobalTheory.QLogDefect.constantCoeff_defect | (intros; apply GlobalTheory.QLogDefect.constantCoeff_defect <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesFrobeniusTwistLinearCombinationModInt
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesFrobeniusTwistLinearCombinationModInt
set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.FrobStep

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q]

theorem frob_eq_comp (p : ℕ) (hp : p ≠ 0) {σ : Type} (s : Q →+* Q) (f : MvPowerSeries σ Q) :
    frob p s f = ((substAlgHom (R := Q) (S := Q) (HasSubst.X_pow (σ := σ) (S := Q) hp)).toRingHom.comp
      (MvPowerSeries.map s)) f := by
  simp [frob]

theorem frob_smul (p : ℕ) (hp : p ≠ 0) {σ : Type} (τ : B →+* B) (s : Q →+* Q)
    (hs : ∀ b, s (algebraMap B Q b) = algebraMap B Q (τ b)) (b : B) (f : MvPowerSeries σ Q) :
    frob p s (algebraMap B Q b • f) = algebraMap B Q (τ b) • frob p s f := by
  unfold frob
  rw [smul_eq_C_mul, map_mul, map_C, hs, ← smul_eq_C_mul,
    subst_smul (HasSubst.X_pow (σ := σ) (S := Q) hp)]

theorem frob_comb (p : ℕ) (hp : p ≠ 0) {σ : Type} (τ : B →+* B) (s : Q →+* Q)
    (hs : ∀ b, s (algebraMap B Q b) = algebraMap B Q (τ b)) {ι : Type} [Fintype ι]
    (w : ι → B) (e : ι → MvPowerSeries σ Q) :
    frob p s (comb w e) = ∑ i, algebraMap B Q (τ (w i)) • frob p s (e i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [comb, frob_eq_comp p hp, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← frob_eq_comp p hp, frob_smul p hp τ s hs]

theorem in_top_sum_smul {σ : Type} {ι : Type} [Fintype ι] (c : ι → B)
    (g : ι → MvPowerSeries σ Q) (h : ∀ i, In (⊤ : Ideal B) (g i)) :
    In (⊤ : Ideal B) (∑ i, algebraMap B Q (c i) • g i) := by
  intro α
  choose b _ hb using fun i => h i α
  refine ⟨∑ i, c i * b i, Submodule.mem_top, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coeff_smul, hb, map_mul]

theorem comb_mulVec {σ : Type} {ι : Type} [Fintype ι] (M : Matrix ι ι B) (v : ι → B)
    (e : ι → MvPowerSeries σ Q) :
    comb (M.mulVec v) e = ∑ i, algebraMap B Q (v i) • comb (fun l => M l i) e := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [comb, Matrix.mulVec, dotProduct, map_sum, Finset.sum_smul, Finset.smul_sum, smul_smul,
    ← map_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
  rw [mul_comm]

theorem frob_comb_step : ∀ (p : ℕ) [Fact p.Prime] (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q]
    (σ : B →+* B) (s : Q →+* Q), (∀ b, s (algebraMap B Q b) = algebraMap B Q (σ b)) →
    ∀ (d : ℕ) (ι : Type) [Fintype ι] (e : ι → MvPowerSeries (Fin d) Q) (M : Matrix ι ι B),
    (∀ i, In (⊤ : Ideal B) (frob p s (e i) - comb (fun l => M l i) e)) →
    ∀ w : ι → B, In (⊤ : Ideal B) (frob p s (comb w e) - comb (M.mulVec fun j => σ (w j)) e) := by
  intro p hp B Q _ _ _ σ s hs d ι _ e M hM w
  have hp0 : p ≠ 0 := hp.out.ne_zero
  have key : frob p s (comb w e) - comb (M.mulVec fun j => σ (w j)) e =
      ∑ i, algebraMap B Q (σ (w i)) • (frob p s (e i) - comb (fun l => M l i) e) := by
    rw [frob_comb p hp0 σ s hs, comb_mulVec]
    simp only [smul_sub, Finset.sum_sub_distrib]
  rw [key]
  exact in_top_sum_smul _ _ hM

end GlobalTheory.FrobStep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesFrobeniusTwistLinearCombinationModIntStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.powerSeriesFrobeniusTwist_linearCombination_mod_integral : ∀ (p : ℕ) [Fact p.Prime] (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] (σ : B →+* B) (s : Q →+* Q), (∀ b, s (algebraMap B Q b) = algebraMap B Q (σ b)) → ∀ (d : ℕ) (ι : Type) [Fintype ι] (e : ι → MvPowerSeries (Fin d) Q) (M : Matrix ι ι B), (∀ i, In (⊤ : Ideal B) (frob p s (e i) - comb (fun l => M l i) e)) → ∀ w : ι → B, In (⊤ : Ideal B) (frob p s (comb w e) - comb (M.mulVec fun j => σ (w j)) e) := by
  first | exact @GlobalTheory.FrobStep.frob_comb_step | exact GlobalTheory.FrobStep.frob_comb_step | (intros; apply GlobalTheory.FrobStep.frob_comb_step <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQuasiLogarithmModIdealTopLinearCombination
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQuasiLogarithmModIdealTopLinearCombination
set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.QLog

theorem ql_comb_top : ∀ (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O) (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ (ι : Type) [Fintype ι] (e : ι → MvPowerSeries (Fin d) Q), (∀ i, QL μ ⊤ (e i)) → ∀ w : ι → B, QL μ ⊤ (comb w e) := by
  intro B O Q _ _ _ _ θ d μ hμ ι _ e he w
  have hc : ∀ i, constantCoeff (up Q μ i) = 0 := by
    intro i
    simp [up, hμ.const i]
  have hzero : QL μ ⊤ (0 : MvPowerSeries (Fin d) Q) := by
    refine ⟨by simp, fun i => ⟨0, Submodule.mem_top, by simp [lin]⟩, fun α => ⟨0, Submodule.mem_top, ?_⟩⟩
    have := formalCoboundary_smul hc (0 : Q) 0
    rw [zero_smul, zero_smul] at this
    rw [this]; simp
  have hadd : ∀ f g : MvPowerSeries (Fin d) Q, QL μ ⊤ f → QL μ ⊤ g → QL μ ⊤ (f + g) := by
    rintro f g ⟨hf0, hf1, hf2⟩ ⟨hg0, hg1, hg2⟩
    refine ⟨by simp [hf0, hg0], fun i => ?_, fun α => ?_⟩
    · obtain ⟨a, -, ha⟩ := hf1 i
      obtain ⟨b, -, hb⟩ := hg1 i
      exact ⟨a + b, Submodule.mem_top, by simp only [lin, map_add (f := _)] at ha hb ⊢; rw [ha, hb]⟩
    · obtain ⟨a, -, ha⟩ := hf2 α
      obtain ⟨b, -, hb⟩ := hg2 α
      exact ⟨a + b, Submodule.mem_top, by rw [formalCoboundary_add hc, map_add (f := _), ha, hb, map_add (f := _)]⟩
  have hsmul : ∀ (c : B) (f : MvPowerSeries (Fin d) Q), QL μ ⊤ f → QL μ ⊤ (algebraMap B Q c • f) := by
    rintro c f ⟨hf0, hf1, hf2⟩
    refine ⟨by simp [hf0], fun i => ?_, fun α => ?_⟩
    · obtain ⟨a, -, ha⟩ := hf1 i
      refine ⟨c * a, Submodule.mem_top, ?_⟩
      simp only [lin, map_smul, smul_eq_mul] at ha ⊢
      rw [ha, map_mul]
    · obtain ⟨a, -, ha⟩ := hf2 α
      refine ⟨c * a, Submodule.mem_top, ?_⟩
      rw [formalCoboundary_smul hc, map_smul, smul_eq_mul, ha, map_mul]
  unfold comb
  exact Finset.sum_induction _ (QL μ ⊤) hadd hzero fun i _ => hsmul (w i) (e i) (he i)

end GlobalTheory.QLog
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQuasiLogarithmModIdealTopLinearCombinationStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isQuasiLogarithmModIdeal_top_linearCombination : ∀ (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O) (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ (ι : Type) [Fintype ι] (e : ι → MvPowerSeries (Fin d) Q), (∀ i, QL μ ⊤ (e i)) → ∀ w : ι → B, QL μ ⊤ (comb w e) := by
  first | exact @GlobalTheory.QLog.ql_comb_top | exact GlobalTheory.QLog.ql_comb_top | (intros; apply GlobalTheory.QLog.ql_comb_top <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPDivGroupChartLevelOneNilpotentModP
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPDivGroupChartLevelOneNilpotentModP
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.AugNil

theorem aeval_mem_span {A R : Type} [CommRing A] [CommRing R] [Algebra R A] {d : ℕ}
    (x : Fin d → A) (P : MvPolynomial (Fin d) R) (h0 : MvPolynomial.constantCoeff P = 0) :
    MvPolynomial.aeval x P ∈ Ideal.span (Set.range x) := by
  classical
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  refine Ideal.sum_mem _ fun m hm => ?_
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact (MvPolynomial.mem_support_iff.1 hm) (by rwa [MvPolynomial.constantCoeff_eq] at h0)
  obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hm0 (Finsupp.ext h)
  refine Ideal.mul_mem_left _ _ ?_
  have hdvd : x i ∣ ∏ j ∈ m.support, x j ^ m j :=
    (dvd_pow_self (x i) hi).trans (Finset.dvd_prod_of_mem _ (Finsupp.mem_support_iff.2 hi))
  obtain ⟨c, hc⟩ := hdvd
  rw [hc]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)

theorem dvd_pow_of_mem_span {A : Type} [CommRing A] {d : ℕ} (x : Fin d → A) (p : A) (N₀ : ℕ)
    (hx : ∀ i, p ∣ x i ^ N₀) (a : A) (ha : a ∈ Ideal.span (Set.range x)) :
    p ∣ a ^ (d * N₀ + 1) := by
  obtain ⟨r, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun A).1 ha
  have h := Ideal.sum_pow_mem_span_pow Finset.univ (fun i => r i • x i) N₀
  rw [Finset.card_univ, Fintype.card_fin] at h
  rw [← Ideal.mem_span_singleton]
  refine Ideal.span_le.2 ?_ h
  rintro _ ⟨i, -, rfl⟩
  rw [SetLike.mem_coe, Ideal.mem_span_singleton]
  simp only [smul_eq_mul, mul_pow]
  exact Dvd.dvd.mul_left ((hx i).trans (pow_dvd_pow _ (Nat.le_succ _))) _

theorem aug_nil : ∀ (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ)
    (c : QLog.Chart G d), ∃ N : ℕ, ∀ f : MvPowerSeries (Fin d) O, constantCoeff f = 0 →
      (p : G.A 1) ∣ c.ev 1 f ^ N := by
  intro p O _ G d c
  classical
  choose Ni hNi using c.nil 1
  let N₀ := Finset.univ.sup Ni
  have hx : ∀ i, (p : G.A 1) ∣ c.x 1 i ^ N₀ := fun i =>
    (hNi i).trans (pow_dvd_pow _ (Finset.le_sup (Finset.mem_univ i)))
  obtain ⟨N₁, hN₁⟩ := (c.isEval 1).2 1
  refine ⟨d * N₀ + 1, fun f hf => ?_⟩
  set P := trunc' O (Finsupp.equivFunOnFinite.symm fun _ => N₁) f with hPdef
  have hR : (p : G.A 1) ∣ c.ev 1 (f - (P : MvPowerSeries (Fin d) O)) := by
    have h := hN₁ (f - P) (fun α hα => ?_)
    · simpa using h
    rw [map_sub, MvPolynomial.coeff_coe, coeff_trunc', if_pos, sub_self]
    intro i
    have : α i ≤ α.degree := by
      rw [Finsupp.degree]
      by_cases hi : α i = 0
      · rw [hi]; exact Nat.zero_le _
      · exact Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finsupp.mem_support_iff.2 hi)
    simpa using this.trans hα.le
  have hP : c.ev 1 (P : MvPowerSeries (Fin d) O) = MvPolynomial.aeval (c.x 1) P := by
    have : (c.ev 1).comp (MvPolynomial.coeToMvPowerSeries.algHom O) = MvPolynomial.aeval (c.x 1) :=
      MvPolynomial.algHom_ext fun i => by simp [(c.isEval 1).1 i]
    exact congrArg (fun φ => φ P) this
  have hP0 : MvPolynomial.constantCoeff P = 0 := by
    rw [MvPolynomial.constantCoeff_eq, hPdef, coeff_trunc', if_pos (zero_le')]
    simpa using hf
  have ha := dvd_pow_of_mem_span (c.x 1) (p : G.A 1) N₀ hx _ (aeval_mem_span (c.x 1) P hP0)
  rw [← hP] at ha
  have hsub := sub_dvd_pow_sub_pow (c.ev 1 f) (c.ev 1 P) (d * N₀ + 1)
  rw [← map_sub] at hsub
  simpa using dvd_add (hR.trans hsub) ha

end GlobalTheory.AugNil
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPDivGroupChartLevelOneNilpotentModPStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pDivGroupChart_level_one_nilpotent_mod_p : ∀ (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∃ N : ℕ, ∀ f : MvPowerSeries (Fin d) O, constantCoeff f = 0 → (p : G.A 1) ∣ c.ev 1 f ^ N := by
  first | exact @GlobalTheory.AugNil.aug_nil | exact GlobalTheory.AugNil.aug_nil | (intros; apply GlobalTheory.AugNil.aug_nil <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusNilpotentModMaximalConnectedPDivGroup
set_option autoImplicit false

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.QLog

theorem isNil_frobenius_chart : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q), IsBasis μ' e → IsAdapted F.θ μ' e → ∀ U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B, (∀ i, In (⊤ : Ideal F.B) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e)) → IsNil F.θ F.σ (U * blk d k (p : F.B) 1) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F G d c μ' hlift hmap k e hbas hadp U hU
  set M := U * blk d k (p : F.B) 1 with hM
  let T : (Fin d ⊕ Fin k → F.B) → (Fin d ⊕ Fin k → F.B) := fun w => M.mulVec fun j => F.σ (w j)
  have hp : ¬IsUnit (p : O) := Fact.out
  have hθp : F.θ (p : F.B) = (p : O) := map_natCast _ _
  have nu_iff : ∀ x : O, ¬IsUnit x ↔ v (algebraMap O C x) < 1 := fun x => by
    rw [hv.isUnit_iff_valuation_eq_one]
    exact ⟨fun h => lt_of_le_of_ne (hv.map_le_one x) h, fun h => h.ne⟩
  have nu_add : ∀ x y : O, ¬IsUnit x → ¬IsUnit y → ¬IsUnit (x + y) := by
    intro x y hx hy
    rw [nu_iff] at hx hy ⊢
    rw [map_add (f := _)]
    exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hx hy)
  have nu_sum : ∀ (s : Finset (Fin d ⊕ Fin k)) (f : Fin d ⊕ Fin k → O),
      (∀ i ∈ s, ¬IsUnit (f i)) → ¬IsUnit (∑ i ∈ s, f i) := by
    intro s f hf
    induction s using Finset.induction_on with
    | empty => simpa using not_isUnit_zero
    | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact nu_add _ _ (hf a (Finset.mem_insert_self _ _))
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))
  have stepA : ∀ w : Fin d ⊕ Fin k → F.B, (∀ j, ¬IsUnit (F.θ (w (Sum.inr j)))) →
      ∀ i, ¬IsUnit (F.θ (T w i)) := by
    intro w hw i
    show ¬IsUnit (F.θ (∑ l, M i l * F.σ (w l)))
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    apply nu_sum
    intro l _
    rw [hM, blk, Matrix.mul_diagonal]
    cases l with
    | inl l =>
      simp only [Sum.elim_inl, map_mul, hθp]
      exact fun h => hp (isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left h))
    | inr j =>
      simp only [Sum.elim_inr, mul_one, map_mul]
      obtain ⟨c', hc'⟩ := F.σ_pow (w (Sum.inr j))
      have hs : F.θ (F.σ (w (Sum.inr j))) = F.θ (w (Sum.inr j)) ^ p + p * F.θ c' := by
        have := congrArg F.θ hc'
        rw [map_sub, map_mul, map_pow, hθp] at this
        linear_combination this
      rw [hs]
      refine fun h => nu_add _ _ ?_ ?_ (isUnit_of_mul_isUnit_right h)
      · exact fun h' => hw j ((isUnit_pow_iff (Fact.out : p.Prime).ne_zero).1 h')
      · exact fun h' => hp (isUnit_of_mul_isUnit_left h')
  have hQL : ∀ w : Fin d ⊕ Fin k → F.B, QL μ' ⊤ (comb w e) := fun w => GlobalTheory.T.isQuasiLogarithmModIdeal_top_linearCombination _ _ _ F.θ d μ' hlift _ e hbas.1 w
  have hstep : ∀ w : Fin d ⊕ Fin k → F.B, In (⊤ : Ideal F.B) (frob p F.s (comb w e) - comb (T w) e) :=
    fun w => GlobalTheory.T.powerSeriesFrobeniusTwist_linearCombination_mod_integral p F.B F.Q F.σ F.s F.s_alg d _ e M hU w
  have hlf : ∀ w : Fin d ⊕ Fin k → F.B, ∃ a : MvPowerSeries (Fin d) F.B,
      map (algebraMap F.B F.Q) a = defect μ' p (comb w e) := by
    intro w
    have h := (QLogDefect.main p F.B O F.Q F.θ F.frame d μ' hlift ⊤ _ (hQL w) p).1
    choose b _ hb using h
    refine ⟨(fun α => b α : MvPowerSeries (Fin d) F.B), MvPowerSeries.ext fun α => ?_⟩
    exact (hb α).symm
  choose A hA using hlf
  let δ : (Fin d ⊕ Fin k → F.B) → G.A 1 := fun w => c.ev 1 (map F.θ (A w))
  set I := Ideal.span (algebraMap O (G.A 1) '' {o | ¬IsUnit o}) with hI
  have hδstep : ∀ w : Fin d ⊕ Fin k → F.B, δ (T w) - δ w ^ p ∈ I := fun w =>
    GlobalTheory.T.quasiLogarithm_levelOne_defect_frobenius_pow p C v O hv ε hε F G d c μ' hlift hmap _ _ _ _ (hQL w) (hQL (T w)) (hstep w) (hA w) (hA (T w))
  have hδit : ∀ n w, δ (T^[n] w) - δ w ^ (p ^ n) ∈ I := by
    intro n
    induction n with
    | zero => intro w; simp
    | succ n ih =>
      intro w
      rw [Function.iterate_succ_apply', pow_succ, pow_mul]
      have h1 := hδstep (T^[n] w)
      have h2 : δ (T^[n] w) ^ p - (δ w ^ p ^ n) ^ p ∈ I :=
        I.mem_of_dvd (sub_dvd_pow_sub_pow _ _ p) (ih w)
      have := I.add_mem h1 h2
      rwa [sub_add_sub_cancel] at this
  have hconst : ∀ w : Fin d ⊕ Fin k → F.B, constantCoeff (map F.θ (A w)) = 0 := by
    intro w
    have h0 := GlobalTheory.T.constantCoeff_quasiLogarithmMultiplicationDefect p F.B O F.Q F.θ F.frame d μ' hlift _ (hQL w) p
    rw [← hA w, MvPowerSeries.constantCoeff_map] at h0
    have h2 : constantCoeff (A w) = 0 := F.frame.inj (by rw [h0, map_zero])
    rw [MvPowerSeries.constantCoeff_map, h2, map_zero]
  obtain ⟨N0, hN0⟩ := GlobalTheory.T.exists_pDivGroupChart_level_one_nilpotent_mod_p p O G d c
  have hsmallp : ∀ x : G.A 1, (p : G.A 1) ∣ x → x ∈ I := by
    rintro x ⟨y, rfl⟩
    apply I.mul_mem_right
    apply Ideal.subset_span
    exact ⟨(p : O), hp, map_natCast _ _⟩
  have hδ0 : ∀ w : Fin d ⊕ Fin k → F.B, δ w ^ (p ^ N0) ∈ I := by
    intro w
    apply hsmallp
    have hle : N0 ≤ p ^ N0 := (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le
    rw [← Nat.sub_add_cancel hle, pow_add]
    exact Dvd.dvd.mul_left (hN0 _ (hconst w)) _
  refine ⟨N0 + 1, fun w i => ?_⟩
  rw [Function.iterate_succ_apply']
  apply stepA
  intro j
  apply GlobalTheory.T.levelOne_defects_independent_mod_maximal p C v O hv ε hε F G d c μ' hlift hmap k e hbas hadp _ (A _) (hA _)
  have := I.add_mem (hδit N0 w) (hδ0 w)
  rwa [sub_add_cancel] at this

end GlobalTheory.QLog
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusNilpotentModMaximalConnectedPDivGroupStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_nilpotent_mod_maximal_connected_pDivGroup : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q), IsBasis μ' e → IsAdapted F.θ μ' e → ∀ U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B, (∀ i, In (⊤ : Ideal F.B) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e)) → IsNil F.θ F.σ (U * blk d k (p : F.B) 1) := by
  first | exact @GlobalTheory.QLog.isNil_frobenius_chart | exact GlobalTheory.QLog.isNil_frobenius_chart | (intros; apply GlobalTheory.QLog.isNil_frobenius_chart <;> assumption)
end
