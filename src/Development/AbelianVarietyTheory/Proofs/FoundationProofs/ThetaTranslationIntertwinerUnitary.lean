module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralDensEqZero
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLine
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LineDerivListCompForm

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslationIntertwinerUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslationIntertwinerUnitary
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ThetaInter

open Formalism.L2.Th1.H

def sesqOf (D : D7) (T : Tor D) (N N' : ℕ) : Sesq (VC D N N') :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun z w => Hf D T z w)
    (by intro a b c; simp only [Hf, Pi.add_apply, add_mul, Finset.sum_add_distrib, add_div])
    (by
      intro c a b
      simp only [Hf, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc, ← Finset.mul_sum, mul_div_assoc])
    (by intro a b c; simp only [Hf, Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib, add_div])
    (by
      intro c a b
      simp only [Hf, Pi.smul_apply, smul_eq_mul, map_mul, mul_left_comm _ (starRingEnd ℂ c), ← Finset.mul_sum,
        mul_div_assoc])

theorem isHerm_sesqOf (D : D7) (T : Tor D) (N N' : ℕ) : IsHerm (sesqOf D T N N') := by
  intro x y
  change Hf D T y x = starRingEnd ℂ (Hf D T x y)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Hf, map_div₀, map_sum, map_mul, Complex.conj_ofReal, Complex.conj_conj, mul_comm]

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ}

theorem lam_mul_mem (a : 𝓞 D.host.K) {w : ℂ} (hw : w ∈ lamOf D cc δ) :
    D.host.φ₀ (((a : D.host.K) : D.host.E)) * w ∈ lamOf D cc δ := by
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨c, hc, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨a * c, cc.mul_mem_left a hc, ?_⟩
    push_cast
    rw [map_mul]
    ring
  | zero => simp
  | add a b _ _ ha hb => rw [mul_add]; exact AddSubgroup.add_mem _ ha hb
  | neg a _ ha => rw [mul_neg]; exact AddSubgroup.neg_mem _ ha

theorem klat_gen {A : AddSubgroup (VC D N N')} (hA : KLat D (tor0 D cc δ) A) :
    ∃ S : Set (Matrix (Fin N') (Fin N) D.host.E), Submodule.span D.host.K S = ⊤ ∧
      A = AddSubgroup.closure {z | ∃ w ∈ lamOf D cc δ, ∃ B ∈ S, z = w • embV D (tor0 D cc δ) B} := by
  rcases hA with ⟨r, b, hb, rfl⟩ | ⟨L, L', hL, hL', rfl⟩
  · refine ⟨Set.range b, hb.2, ?_⟩
    unfold LaB
    congr 1
    ext z
    simp [tor0]
  · refine ⟨YYl D L L', ?_, rfl⟩
    obtain ⟨r, y, y', hy, -, h⟩ := GlobalTheory.HomDual.exists_dual_family_hom D (GlobalTheory.exists_trace_dual_family_halfDifferent D) N N' L L' hL hL'
    rw [eq_top_iff]
    intro x _
    rw [h x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (hy i))

theorem klat_smul_mem {A : AddSubgroup (VC D N N')} (hA : KLat D (tor0 D cc δ) A) (a : 𝓞 D.host.K)
    {x : VC D N N'} (hx : x ∈ A) : D.host.φ₀ (((a : D.host.K) : D.host.E)) • x ∈ A := by
  obtain ⟨S, -, rfl⟩ := klat_gen hA
  induction hx using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨w, hw, B, hB, rfl⟩ := hw
    exact AddSubgroup.subset_closure ⟨_, lam_mul_mem a hw, B, hB, smul_smul _ _ _⟩
  | zero => simp
  | add a b _ _ ha hb => rw [smul_add]; exact AddSubgroup.add_mem _ ha hb
  | neg a _ ha => rw [smul_neg]; exact AddSubgroup.neg_mem _ ha

theorem embV_smul (h : GL3Theta.InducedCMType D) (k : D.host.K) (B : Matrix (Fin N') (Fin N) D.host.E) :
    embV D (tor0 D cc δ) (k • B) = D.host.φ₀ (k : D.host.E) • embV D (tor0 D cc δ) B := by
  funext τ i j
  change embT D τ ((k : D.host.E) * B i j) = D.host.φ₀ (k : D.host.E) * embT D τ (B i j)
  rw [map_mul, h τ k]

theorem embV_add (B B' : Matrix (Fin N') (Fin N) D.host.E) :
    embV D (tor0 D cc δ) (B + B') = embV D (tor0 D cc δ) B + embV D (tor0 D cc δ) B' := by
  funext τ i j
  exact map_add (embT D τ) _ _

theorem embV_zero : embV D (tor0 D cc δ) (0 : Matrix (Fin N') (Fin N) D.host.E) = 0 := by
  funext τ i j
  exact map_zero (embT D τ)

theorem klat_rat (h : GL3Theta.InducedCMType D) {A : AddSubgroup (VC D N N')} (hA : KLat D (tor0 D cc δ) A)
    {x : VC D N N'} (hx : x ∈ A) : ∃ B, x = δ • embV D (tor0 D cc δ) B := by
  obtain ⟨S, -, rfl⟩ := klat_gen hA
  have hl : ∀ w ∈ lamOf D cc δ, ∃ k : D.host.K, w = δ * D.host.φ₀ (k : D.host.E) := by
    intro w hw
    induction hw using AddSubgroup.closure_induction with
    | mem w hw => obtain ⟨c, -, rfl⟩ := hw; exact ⟨c, rfl⟩
    | zero => exact ⟨0, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨k, rfl⟩ := ha
      obtain ⟨k', rfl⟩ := hb
      exact ⟨k + k', by simp [mul_add]⟩
    | neg a _ ha =>
      obtain ⟨k, rfl⟩ := ha
      exact ⟨-k, by simp⟩
  induction hx using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨w, hw, B, -, rfl⟩ := hw
    obtain ⟨k, rfl⟩ := hl w hw
    exact ⟨k • B, by rw [embV_smul h, smul_smul]⟩
  | zero => exact ⟨0, by rw [embV_zero, smul_zero]⟩
  | add a b _ _ ha hb =>
    obtain ⟨B, rfl⟩ := ha
    obtain ⟨B', rfl⟩ := hb
    exact ⟨B + B', by rw [embV_add, smul_add]⟩
  | neg a _ ha =>
    obtain ⟨B, rfl⟩ := ha
    exact ⟨(-1 : D.host.K) • B, by rw [embV_smul h]; simp⟩

theorem klat_mul_mem (h : GL3Theta.InducedCMType D) (hcc : cc ≠ ⊥) {A : AddSubgroup (VC D N N')}
    (hA : KLat D (tor0 D cc δ) A) (B : Matrix (Fin N') (Fin N) D.host.E) :
    ∃ m : ℕ, 0 < m ∧ m • (δ • embV D (tor0 D cc δ) B) ∈ A := by
  have hA' := hA
  obtain ⟨S, hS, hAS⟩ := klat_gen hA'
  have hB : B ∈ Submodule.span D.host.K S := hS ▸ Submodule.mem_top
  induction hB using Submodule.span_induction with
  | mem B hB =>
    refine ⟨Ideal.absNorm cc, Nat.pos_of_ne_zero (fun e => hcc (Ideal.absNorm_eq_zero_iff.1 e)), ?_⟩
    rw [hAS]
    refine AddSubgroup.subset_closure ⟨(Ideal.absNorm cc : ℂ) * δ,
      AddSubgroup.subset_closure ⟨_, Ideal.absNorm_mem cc, by simp [mul_comm]⟩, B, hB, ?_⟩
    rw [← smul_smul, Nat.cast_smul_eq_nsmul]
  | zero => exact ⟨1, one_pos, by simp [embV_zero]⟩
  | add a b _ _ ha hb =>
    obtain ⟨m, hm, ha⟩ := ha
    obtain ⟨n, hn, hb⟩ := hb
    refine ⟨m * n, by positivity, ?_⟩
    rw [embV_add, smul_add, smul_add]
    refine A.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact A.nsmul_mem ha _
    · rw [mul_smul]; exact A.nsmul_mem hb _
  | smul k B _ hB =>
    obtain ⟨m, hm, hB⟩ := hB
    obtain ⟨n, hn, hk⟩ := exists_integral_multiples ℤ ℚ ({k} : Finset D.host.K)
    have hk' : IsIntegral ℤ (n.natAbs • k) := by
      have := hk k (Finset.mem_singleton_self k)
      rcases Int.natAbs_eq n with e | e
      · rw [e] at this; simpa using this
      · rw [e] at this; simpa using this.neg
    refine ⟨m * n.natAbs, Nat.mul_pos hm (Int.natAbs_pos.2 hn), ?_⟩
    convert klat_smul_mem hA ⟨_, hk'⟩ hB using 1
    rw [embV_smul h]
    simp only [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    congr 1
    change _ = D.host.φ₀ ((n.natAbs • k : D.host.K) : D.host.E) * _
    simp
    ring

theorem klat_finite (h : GL3Theta.InducedCMType D) (hcc : cc ≠ ⊥) {A₁ A₂ : AddSubgroup (VC D N N')}
    (h₁ : KLat D (tor0 D cc δ) A₁) (h₂ : KLat D (tor0 D cc δ) A₂) (hfg : A₂.FG) :
    Finite (A₂ ⧸ A₁.addSubgroupOf A₂) :=
  finite_quot hfg fun x hx => by
    obtain ⟨B, rfl⟩ := klat_rat h h₂ hx
    exact klat_mul_mem h hcc h₁ B

theorem klat_facts (hc : Crv D cc δ) {A : AddSubgroup (VC D N N')} (hA : KLat D (tor0 D cc δ) A) :
    A.FG ∧ Submodule.span ℝ (A : Set (VC D N N')) = ⊤ ∧ IsSelfDual (sesqOf D (tor0 D cc δ) N N') A ∧
      IsSemiChar (sesqOf D (tor0 D cc δ) N N') A (al D (tor0 D cc δ)) := by
  obtain ⟨-, -, h1, h2, h3, h4, h5⟩ := GlobalTheory.ThetaLine.theta_line D (GlobalTheory.InducedType.induced_type D).1 cc δ hc N N' A hA
  refine ⟨h3, h4, le_antisymm h2 h1, ?_⟩
  obtain ⟨a, ha⟩ := GlobalTheory.NormSum.exists_integer_map_eq_w0 D
  refine isSemiChar_round (isHerm_sesqOf D _ N N') (Real.sqrt D.host.d) h1 (fun x hx => ?_) h5
  have := klat_smul_mem hA a hx
  rwa [ha] at this

end GlobalTheory.ThetaInter


open GlobalTheory.ThetaInter in
theorem GlobalTheory.theta_translation_intertwiner_unitary : ∀ D : D7, IntertwinerUnitary D := by
  intro D cc δ hc N N' A₁ A₂ h₁ h₂ th hth
  obtain ⟨f₁, s₁, d₁, c₁⟩ := klat_facts hc h₁
  obtain ⟨f₂, s₂, d₂, c₂⟩ := klat_facts hc h₂
  have hH := isHerm_sesqOf D (tor0 D cc δ) N N'
  have hψ := (GlobalTheory.InducedType.induced_type D).1.1
  have := klat_finite hψ hc.1.1 h₁ h₂ f₂
  have := klat_finite hψ hc.1.1 h₂ h₁ f₁
  have : (MeasureTheory.volume : MeasureTheory.Measure (Fin N' → Fin N → ℂ)).IsAddHaarMeasure :=
    MeasureTheory.Measure.pi.isAddHaarMeasure _
  have : (MeasureTheory.volume : MeasureTheory.Measure (VC D N N')).IsAddHaarMeasure :=
    MeasureTheory.Measure.pi.isAddHaarMeasure _
  have t₁ := discrete_of_selfDual hH d₁ f₁
  have t₂ := discrete_of_selfDual hH d₂ f₂
  have hF : th ∈ Formalism.L2.Th1.H.fixedBy (sesqOf D (tor0 D cc δ) N N') (al D (tor0 D cc δ)) A₁ := hth.2
  exact ⟨fun x => mean_opU MeasureTheory.volume hH t₁ s₁ c₁ hth.1.continuous hF x,
    ⟨differentiable_inter (H := sesqOf D (tor0 D cc δ) N N') (α := al D (tor0 D cc δ)) A₁ A₂ hth.1,
      inter_mem_fixedBy hH c₁ d₂ c₂ hF⟩,
    mean_inter MeasureTheory.volume hH t₁ s₁ t₂ s₂ d₁ c₁ d₂ c₂ hth.1 hF,
    inter_inter hH d₁ d₂ c₁ hF⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslationIntertwinerUnitaryStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intertwinerUnitary_all : ∀ D : D7, IntertwinerUnitary D := by
  first | exact @GlobalTheory.theta_translation_intertwiner_unitary | exact GlobalTheory.theta_translation_intertwiner_unitary | (intros; apply GlobalTheory.theta_translation_intertwiner_unitary <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfIdem
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Pointwise

namespace GlobalTheory.NormSum.VacMove

theorem conj_conj (D : D7) (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  apply D.host.φ₀.injective
  rw [D.host.toHostAx.conjE_apply, D.host.toHostAx.conjE_apply]
  simp

theorem sgA_sgA (D : D7) (y : AE D) : sgA D (sgA D y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [sgA, Formalism.UG.sigR, conj_conj]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem sgA_mem (D : D7) {s : AE D} (hs : s ∈ OhE D) : sgA D s ∈ OhE D :=
  Formalism.UG.P.csDual_sig_mem _ hs

theorem inc_int (D : D7) (b : 𝓞 D.host.E) : inc D (b : D.host.E) ∈ OhE D :=
  Formalism.UG.P.adelstab_incl_int (F := ℚ) b

theorem inc_dvd (D : D7) {N : ℕ} {b : 𝓞 D.host.E} (h : (N : 𝓞 D.host.E) ∣ b) :
    ∃ w ∈ OhE D, inc D (b : D.host.E) = (N : AE D) * w := by
  obtain ⟨c, rfl⟩ := h
  refine ⟨_, inc_int D c, ?_⟩
  rw [← map_natCast (inc D), ← map_mul]
  simp

theorem exists_nat_denom (D : D7) (y : AE D) : ∃ n : ℕ, 0 < n ∧ (n : AE D) * y ∈ OhE D :=
  (GlobalTheory.T.cmFiniteAdele_strong_approx_mod_adelicIdeal D ⊤ top_ne_bot).2.1 y

theorem zeroAt_mul (D : D7) {q : ℕ} (hq : q.Prime) {x : AE D} (hx : ZeroAt D q x) (y : AE D) :
    ZeroAt D q (x * y) := by
  intro k
  obtain ⟨n, hn, hy⟩ := exists_nat_denom D y
  obtain ⟨a, n', hn', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' q hq.ne_one
  obtain ⟨m, hm, hmq, s, hs, h⟩ := hx (k + a)
  refine ⟨m * n', Nat.mul_pos hm (Nat.pos_of_ne_zero (by rintro rfl; simp at hn')),
    Nat.Coprime.mul_left hmq ((Nat.Prime.coprime_iff_not_dvd hq).2 hn').symm, _, mul_mem hs hy, ?_⟩
  push_cast
  linear_combination (n' : AE D) * y * h

theorem exists_half_idem (D : D7) : ∃ ε ∈ OhE D, ε * ε = ε ∧ ε * sgA D ε = 0 ∧ ∀ q : ℕ, q.Prime →
    (InertQ D q → ZeroAt D q (ε + sgA D ε)) ∧ (¬ InertQ D q → ZeroAt D q (1 - (ε + sgA D ε))) := by
  obtain ⟨e, h1, h2, h3⟩ := GlobalTheory.T.exists_cm_idempotents_select_conjugate_primes D
  obtain ⟨hsep, hcpl⟩ := GlobalTheory.T.cmFiniteAdele_integral_separated_complete D
  have hc : ∀ b : 𝓞 D.host.E, inc D ((D.host.conj • b : 𝓞 D.host.E) : D.host.E) = sgA D (inc D b) := by
    intro b
    rw [GlobalTheory.NormSum.PtsMem.sgA_inc]; rfl
  obtain ⟨ε, hε, h⟩ := hcpl (fun N => inc D (e N : D.host.E)) (fun N => inc_int D _) (by
    intro N m hN hm
    obtain ⟨w, hw, h⟩ := inc_dvd D (h1 N m hN hm)
    refine ⟨w, hw, ?_⟩
    rw [← h]; simp)
  refine ⟨ε, hε, ?_, ?_, fun q hq => ⟨fun hi k => ?_, fun hi k => ?_⟩⟩
  · rw [← sub_eq_zero]
    refine hsep _ fun N hN => ?_
    obtain ⟨w, hw, hh⟩ := h N hN
    obtain ⟨v, hv, hh'⟩ := inc_dvd D (h2 N hN).1
    have hh'' : inc D (e N : D.host.E) * inc D (e N : D.host.E) - inc D (e N : D.host.E) = N * v := by
      rw [← hh']; simp
    refine ⟨v + (2 * inc D (e N : D.host.E) * w + N * w * w - w), ?_, ?_⟩
    · exact add_mem hv (sub_mem (add_mem (mul_mem (mul_mem (ofNat_mem _ 2) (inc_int D _)) hw)
        (mul_mem (mul_mem (natCast_mem _ _) hw) hw)) hw)
    · rw [hh]; linear_combination hh''
  · refine hsep _ fun N hN => ?_
    obtain ⟨w, hw, hh⟩ := h N hN
    obtain ⟨v, hv, hh'⟩ := inc_dvd D (h2 N hN).2
    have hh'' : inc D (e N : D.host.E) * sgA D (inc D (e N : D.host.E)) = N * v := by
      rw [← hh', ← hc]; simp
    refine ⟨v + (inc D (e N : D.host.E) * sgA D w + w * sgA D (inc D (e N : D.host.E)) + N * w * sgA D w), ?_, ?_⟩
    · exact add_mem hv (add_mem (add_mem (mul_mem (inc_int D _) (sgA_mem D hw))
        (mul_mem hw (sgA_mem D (inc_int D _)))) (mul_mem (mul_mem (natCast_mem _ _) hw) (sgA_mem D hw)))
    · rw [hh, map_add (f := _), map_mul, map_natCast]; linear_combination hh''
  · obtain ⟨w, hw, hh⟩ := h (q ^ k) (pow_pos hq.pos k)
    obtain ⟨v, hv, hh'⟩ := inc_dvd D ((h3 q k hq).1 hi)
    have hh'' : inc D (e (q ^ k) : D.host.E) + sgA D (inc D (e (q ^ k) : D.host.E)) = (q ^ k : ℕ) * v := by
      rw [← hh', ← hc]; simp
    refine ⟨1, one_pos, by simp, v + (w + sgA D w), add_mem hv (add_mem hw (sgA_mem D hw)), ?_⟩
    rw [hh, map_add (f := _), map_mul, map_natCast]
    push_cast at hh'' ⊢
    linear_combination hh''
  · obtain ⟨w, hw, hh⟩ := h (q ^ k) (pow_pos hq.pos k)
    obtain ⟨v, hv, hh'⟩ := inc_dvd D ((h3 q k hq).2 hi)
    have hh'' : 1 - (inc D (e (q ^ k) : D.host.E) + sgA D (inc D (e (q ^ k) : D.host.E))) = (q ^ k : ℕ) * v := by
      rw [← hh', ← hc]; simp
    refine ⟨1, one_pos, by simp, v - (w + sgA D w), sub_mem hv (add_mem hw (sgA_mem D hw)), ?_⟩
    rw [hh, map_add (f := _), map_mul, map_natCast]
    push_cast at hh'' ⊢
    linear_combination hh''

theorem exists_splitComp (D : D7) (u : (AE D)ˣ) (hu : (u : AE D) * sgA D u = 1) :
    ∃ z x : (AE D)ˣ, SplitComp D u z ∧ x = z * sgU D x ∧ ((u : AE D) ∈ OhE D → IntU D x) := by
  obtain ⟨ε, hε, h1, h2, h3⟩ := exists_half_idem D
  have h1' : sgA D ε * sgA D ε = sgA D ε := by rw [← map_mul, h1]
  set η := sgA D ε with hη
  set v := sgA D u with hv
  have hz : ((1 - (ε + η)) + (ε + η) * u) * ((1 - (ε + η)) + (ε + η) * v) = 1 := by
    linear_combination (1 - u - v + u * v) * (h1 + h1' + 2 * h2) + (ε + η) * hu
  have hx : ((1 - η) + η * u) * ((1 - η) + η * v) = 1 := by
    linear_combination (1 - u - v + u * v) * h1' + η * hu
  refine ⟨⟨_, _, hz, by rw [mul_comm, hz]⟩, ⟨_, _, hx, by rw [mul_comm, hx]⟩, fun q hq => ⟨fun hi => ?_, fun hi => ?_⟩,
    ?_, fun hO => ⟨?_, ?_⟩⟩
  · convert zeroAt_mul D hq ((h3 q hq).1 hi) (u - 1) using 1
    simp only; ring
  · convert zeroAt_mul D hq ((h3 q hq).2 hi) (1 - u) using 1
    simp only; ring
  · ext
    change (1 - η) + η * u = ((1 - (ε + η)) + (ε + η) * u) * sgA D ((1 - η) + η * u)
    rw [map_add (f := _), map_mul, map_sub, map_one, hη, sgA_sgA, ← hη, ← hv]
    linear_combination (-(1 - u - v + u * v)) * (h1 + h2) - ε * hu
  · exact add_mem (sub_mem (one_mem _) (sgA_mem D hε)) (mul_mem (sgA_mem D hε) hO)
  · exact add_mem (sub_mem (one_mem _) (sgA_mem D hε)) (mul_mem (sgA_mem D hε) (sgA_mem D hO))

theorem det_norm (D : D7) {N : ℕ} (g : GA D N) :
    ((Matrix.GeneralLinearGroup.det (g : GL (Fin N) (AE D)) : (AE D)ˣ) : AE D) *
      sgA D ((Matrix.GeneralLinearGroup.det (g : GL (Fin N) (AE D)) : (AE D)ˣ) : AE D) = 1 := by
  have h := congrArg Matrix.det ((GlobalTheory.NormSum.PtsMem.mem_GA D _).1 g.2)
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
  rw [Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det, mul_comm]
  exact h

theorem det_int (D : D7) {N : ℕ} (g : GL (Fin N) (AE D)) (hg : IntG D g) :
    ((Matrix.GeneralLinearGroup.det g : (AE D)ˣ) : AE D) ∈ OhE D := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_apply']
  exact sum_mem fun σ _ => mul_mem (intCast_mem _ _) (prod_mem fun i _ => (hg _ _).1)

end GlobalTheory.NormSum.VacMove
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryDoubleCosetClassesFiniteCardLe
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryDoubleCosetClassesFiniteCardLe
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.NormSum

theorem doubleCoset_surj_of_le {G : Type*} [Group G] (H K J : Subgroup G) :
    Function.Surjective (fun p : DoubleCoset.Quotient (H : Set G) (K : Set G) × (K ⧸ J.subgroupOf K) =>
      DoubleCoset.mk H J (p.1.out * (p.2.out : G))) := by
  intro c
  obtain ⟨h, hh, k, hk, e⟩ := DoubleCoset.mk_out_eq_mul H K c.out
  refine ⟨(DoubleCoset.mk H K c.out, QuotientGroup.mk (⟨k⁻¹, K.inv_mem hk⟩ : K)), ?_⟩
  obtain ⟨j, hj⟩ := QuotientGroup.mk_out_eq_mul (J.subgroupOf K) (⟨k⁻¹, K.inv_mem hk⟩ : K)
  have hjJ : ((j : K) : G) ∈ J := Subgroup.mem_subgroupOf.mp j.2
  simp only
  rw [hj, e]
  conv_rhs => rw [← DoubleCoset.out_eq' c]
  rw [eq_comm, DoubleCoset.eq]
  refine ⟨h, hh, _, hjJ, ?_⟩
  simp [mul_assoc]

theorem doubleCoset_card_le {G : Type*} [Group G] (H K J : Subgroup G)
    [Finite (DoubleCoset.Quotient (H : Set G) (K : Set G))] (hJ : J.relIndex K ≠ 0) :
    Finite (DoubleCoset.Quotient (H : Set G) (J : Set G)) ∧
      Nat.card (DoubleCoset.Quotient (H : Set G) (J : Set G)) ≤
        Nat.card (DoubleCoset.Quotient (H : Set G) (K : Set G)) * J.relIndex K := by
  have : Finite (K ⧸ J.subgroupOf K) := Nat.finite_of_card_ne_zero hJ
  refine ⟨Finite.of_surjective _ (doubleCoset_surj_of_le H K J), ?_⟩
  have := Nat.card_le_card_of_surjective _ (doubleCoset_surj_of_le H K J)
  rwa [Nat.card_prod] at this

theorem cls_finite_card_le : ∀ (D : D7) (N : ℕ), Finite (Cls D N (intG D N)) ∧ (Nat.card (Cls D N (intG D N)) : ℝ) ≤ (12 * (fF D : ℝ) ^ 2 * (N : ℝ) ^ 4 * D.host.rdE ^ 2) ^ (6 * fF D * N ^ 2) ∧ ∀ J : Subgroup (GA D N), J ≤ intG D N → J.relIndex (intG D N) ≠ 0 → Finite (Cls D N J) ∧ Nat.card (Cls D N J) ≤ Nat.card (Cls D N (intG D N)) * J.relIndex (intG D N) := by
  intro D N
  have hcm : IsCMField D.host.E := D.host.isCMField_hostE
  have hconj : ∀ x : D.host.E, IsCMField.complexConj D.host.E x = D.host.conj x := by
    intro x
    apply D.host.φ₀.injective
    have h1 := IsCMField.complexEmbedding_complexConj D.host.E D.host.φ₀ x
    have h2 := D.host.conjE_apply D.host.φ₀ x
    exact h1.trans h2.symm
  have hfr : Module.finrank ℚ D.host.E = 2 * fF D := by
    rw [D.host.finrank_cmField, fF, Formalism.BasicNotions.Ranks.f, Formalism.BasicNotions.Ranks.n]
    ring
  obtain ⟨R, hR, hcov⟩ := GlobalTheory.exists_finset_selfDual_classes_rootDiscr D.host.E N
  obtain ⟨hrat, -, hex, -, -⟩ := GlobalTheory.NormSum.mem_ratG_intG D N
  obtain ⟨Lt, hSD, -, hLt, hmv, -⟩ := GlobalTheory.T.Lt_eq_iff_inv_mul_mem_intG_and_transport D N
  have key : ∀ g : GA D N, ∃ L₀ ∈ R, ∃ h ∈ ratG D N, Lt (h⁻¹ * g) = L₀ := by
    intro g
    obtain ⟨h1, h2, h3⟩ := (hSD g).2
    obtain ⟨L₀, hL₀, γ, hγ, hx⟩ := hcov (Lt g) h1 h2 (by
      intro y
      rw [h3 y]
      refine forall_congr' fun x => forall_congr' fun _ => ?_
      constructor
      · rintro ⟨z, hz⟩
        have hz' : (z : D.host.E) = ∑ i, IsCMField.complexConj D.host.E (x i) * y i := hz
        rw [← hz']
        exact z.isIntegral_coe
      · intro hz
        exact ⟨⟨_, hz⟩, rfl⟩)
    have hm : γ.map (IsCMField.complexConj D.host.E) = γ.map D.host.conj := by
      ext i j
      simp only [Matrix.map_apply, hconj]
    rw [hm] at hγ
    obtain ⟨h, hh⟩ := hex γ hγ
    refine ⟨L₀, hL₀, h, (hrat h).2 ⟨γ, hh⟩, ?_⟩
    ext x
    rw [hmv h (h⁻¹ * g) γ hh x, mul_inv_cancel_left, hx]
  choose L₀ hL₀ h hh hL using key
  let f : Cls D N (intG D N) → R := fun c => ⟨L₀ c.out, hL₀ _⟩
  have hf : Function.Injective f := by
    intro c c' e
    have e' : L₀ c.out = L₀ c'.out := congrArg Subtype.val e
    rw [← hL, ← hL, hLt] at e'
    rw [← DoubleCoset.out_eq' c, ← DoubleCoset.out_eq' c', DoubleCoset.eq]
    refine ⟨h c'.out * (h c.out)⁻¹, Subgroup.mul_mem _ (hh _) (Subgroup.inv_mem _ (hh _)), _, e', ?_⟩
    group
  have hfin : Finite (Cls D N (intG D N)) := Finite.of_injective f hf
  refine ⟨hfin, ?_, fun J _ hJ => doubleCoset_card_le _ _ J hJ⟩
  have hc : Nat.card (Cls D N (intG D N)) ≤ R.card := by
    have := Nat.card_le_card_of_injective f hf
    simpa using this
  refine le_trans (by exact_mod_cast hc) (hR.trans (le_of_eq ?_))
  have hrd : |(discr D.host.E : ℝ)| ^ ((1 : ℝ) / (Module.finrank ℚ D.host.E : ℝ)) = D.host.rdE := rfl
  rw [hrd, hfr]
  have : 3 * (2 * fF D) * N ^ 2 = 6 * fF D * N ^ 2 := by ring
  rw [this]
  congr 1
  push_cast
  ring

end GlobalTheory.NormSum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryDoubleCosetClassesFiniteCardLeStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryDoubleCosetClasses_finite_card_le : ∀ (D : D7) (N : ℕ), Finite (Cls D N (intG D N)) ∧ (Nat.card (Cls D N (intG D N)) : ℝ) ≤ (12 * (fF D : ℝ) ^ 2 * (N : ℝ) ^ 4 * D.host.rdE ^ 2) ^ (6 * fF D * N ^ 2) ∧ ∀ J : Subgroup (GA D N), J ≤ intG D N → J.relIndex (intG D N) ≠ 0 → Finite (Cls D N J) ∧ Nat.card (Cls D N J) ≤ Nat.card (Cls D N (intG D N)) * J.relIndex (intG D N) := by
  first | exact @GlobalTheory.NormSum.cls_finite_card_le | exact GlobalTheory.NormSum.cls_finite_card_le | (intros; apply GlobalTheory.NormSum.cls_finite_card_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TaylorSeriesInParameterRescaleOfAlgebraic
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

namespace GlobalTheory.SerTransport

open PowerSeries

theorem taylorCoeff_add_entire {F G : ℂ → ℂ} (hF : Differentiable ℂ F) (hG : Differentiable ℂ G) (n : ℕ) :
    coef1 (fun z => F z + G z) n = coef1 F n + coef1 G n := by
  simp only [coef1]
  rw [iteratedDeriv_fun_add hF.contDiff.contDiffAt hG.contDiff.contDiffAt, add_div]

theorem taylorCoeff_mul_entire {F G : ℂ → ℂ} (hF : Differentiable ℂ F) (hG : Differentiable ℂ G) (n : ℕ) :
    coef1 (fun z => F z * G z) n =
      ∑ q ∈ Finset.HasAntidiagonal.antidiagonal n, coef1 F q.1 * coef1 G q.2 := by
  simp only [coef1]
  rw [iteratedDeriv_fun_mul hF.contDiff.contDiffAt hG.contDiff.contDiffAt,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have e : ((n.choose i : ℕ) : ℂ) * (i.factorial : ℂ) * ((n - i).factorial : ℂ) = n.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi'
  have h1 : (i.factorial : ℂ) ≠ 0 := by exact_mod_cast i.factorial_ne_zero
  have h2 : ((n - i).factorial : ℂ) ≠ 0 := by exact_mod_cast (n - i).factorial_ne_zero
  have h3 : ((n.choose i : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hi').ne'
  rw [← e]
  field_simp

theorem taylorCoeff_const_function (c : ℂ) (n : ℕ) : coef1 (fun _ => c) n = if n = 0 then c else 0 := by
  simp only [coef1, iteratedDeriv_const]
  split_ifs with h
  · simp [h]
  · simp

theorem taylorCoeff_zero_eq_value (F : ℂ → ℂ) : coef1 F 0 = F 0 := by simp [coef1]

theorem taylorCoeff_scale_entire {F : ℂ → ℂ} (hF : Differentiable ℂ F) (β : ℂ) (n : ℕ) :
    coef1 (fun z => F (β * z)) n = β ^ n * coef1 F n := by
  simp only [coef1]
  rw [iteratedDeriv_comp_const_mul hF.contDiff]
  simp [mul_div_assoc]

variable {p : ℕ} [Fact p.Prime]

theorem lamC_coe (lam : Qbar →+* ℂ_[p]) (x : Qbar) : lamC lam (x : ℂ) = lam x := by
  simp [lamC]

theorem coeff_padicTransportSeries (lam : Qbar →+* ℂ_[p]) (F : ℂ → ℂ) (n : ℕ) :
    coeff n (GL3Theta.ser1 lam F) = lamC lam (coef1 F n) := by
  simp [GL3Theta.ser1, coef1]

theorem exists_coef {F : ℂ → ℂ} (hF : AlgEnt F) : ∃ a : ℕ → Qbar, ∀ n, coef1 F n = a n :=
  ⟨fun n => ⟨_, hF.2 n⟩, fun _ => rfl⟩

theorem padicTransportSeries_add (lam : Qbar →+* ℂ_[p]) {F G : ℂ → ℂ} (hF : AlgEnt F) (hG : AlgEnt G) :
    AlgEnt (fun z => F z + G z) ∧
      GL3Theta.ser1 lam (fun z => F z + G z) = GL3Theta.ser1 lam F + GL3Theta.ser1 lam G := by
  obtain ⟨a, ha⟩ := exists_coef hF
  obtain ⟨b, hb⟩ := exists_coef hG
  have e : ∀ n, coef1 (fun z => F z + G z) n = ((a n + b n : Qbar) : ℂ) := fun n => by
    rw [taylorCoeff_add_entire hF.1 hG.1, ha, hb]; rfl
  refine ⟨⟨hF.1.add hG.1, fun n => e n ▸ Subtype.property _⟩, ?_⟩
  ext n
  simp only [map_add (f := _), coeff_padicTransportSeries, e, ha, hb, lamC_coe]

theorem padicTransportSeries_mul (lam : Qbar →+* ℂ_[p]) {F G : ℂ → ℂ} (hF : AlgEnt F) (hG : AlgEnt G) :
    AlgEnt (fun z => F z * G z) ∧
      GL3Theta.ser1 lam (fun z => F z * G z) = GL3Theta.ser1 lam F * GL3Theta.ser1 lam G := by
  obtain ⟨a, ha⟩ := exists_coef hF
  obtain ⟨b, hb⟩ := exists_coef hG
  have e : ∀ n, coef1 (fun z => F z * G z) n =
      ((∑ q ∈ Finset.HasAntidiagonal.antidiagonal n, a q.1 * b q.2 : Qbar) : ℂ) := fun n => by
    rw [taylorCoeff_mul_entire hF.1 hG.1]
    simp [ha, hb]
  refine ⟨⟨hF.1.mul hG.1, fun n => e n ▸ Subtype.property _⟩, ?_⟩
  ext n
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [coeff_mul, coeff_padicTransportSeries, e, ha, hb, lamC_coe, map_sum, map_mul]

theorem padicTransportSeries_const (lam : Qbar →+* ℂ_[p]) {c : ℂ} (hc : c ∈ Qbar) :
    AlgEnt (fun _ => c) ∧ GL3Theta.ser1 lam (fun _ => c) = C (lamC lam c) := by
  refine ⟨⟨differentiable_const c, fun n => ?_⟩, ?_⟩
  · rw [taylorCoeff_const_function]
    split_ifs
    exacts [hc, zero_mem _]
  · ext n
    rw [coeff_padicTransportSeries, taylorCoeff_const_function, coeff_C]
    split_ifs
    · rfl
    · exact (lamC_coe lam 0).trans (map_zero lam)

theorem taylorSeriesInParameter_rescale_of_algebraic (lam : Qbar →+* ℂ_[p]) {F : ℂ → ℂ} (hF : AlgEnt F) {β : ℂ} (hβ : β ∈ Qbar) :
    AlgEnt (fun z => F (β * z)) ∧
      GL3Theta.ser1 lam (fun z => F (β * z)) = rescale (lamC lam β) (GL3Theta.ser1 lam F) := by
  obtain ⟨a, ha⟩ := exists_coef hF
  obtain ⟨b, rfl⟩ : ∃ b : Qbar, (b : ℂ) = β := ⟨⟨β, hβ⟩, rfl⟩
  have e : ∀ n, coef1 (fun z => F (b * z)) n = ((b ^ n * a n : Qbar) : ℂ) := fun n => by
    rw [taylorCoeff_scale_entire hF.1, ha]
    simp
  refine ⟨⟨hF.1.comp (by fun_prop), fun n => e n ▸ Subtype.property _⟩, ?_⟩
  ext n
  simp only [coeff_rescale, coeff_padicTransportSeries, e, ha, lamC_coe, map_pow, map_mul]

theorem const_subst {a : PowerSeries ℂ_[p]} (ha : constantCoeff a = 0) (f : PowerSeries ℂ_[p]) :
    constantCoeff (f.subst a : PowerSeries ℂ_[p]) = constantCoeff f := by
  have hs := HasSubst.of_constantCoeff_zero' ha
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_subst' hs, finsum_eq_single _ 0]
  · simp
  · intro k hk
    simp [ha, hk]

theorem one_subst {a : PowerSeries ℂ_[p]} (ha : constantCoeff a = 0) (f : PowerSeries ℂ_[p]) :
    coeff 1 (f.subst a : PowerSeries ℂ_[p]) = coeff 1 f * coeff 1 a := by
  have hs := HasSubst.of_constantCoeff_zero' ha
  have e := congrArg constantCoeff (derivative_subst (f := f) hs)
  rw [map_mul, const_subst ha] at e
  simpa [← coeff_zero_eq_constantCoeff_apply, coeff_derivative] using e

variable (g : GL3Theta.G1 p)

theorem const_l : constantCoeff g.l = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  simp [GL3Theta.G1.l, flog]

theorem const_Cl (c : ℂ_[p]) : constantCoeff (C c * g.l) = 0 := by
  rw [map_mul, const_l, mul_zero]

theorem atU_eq (F : ℂ → ℂ) : g.atU F =
    subst (C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * g.l : PowerSeries ℂ_[p]) (GL3Theta.ser1 g.lam F) := rfl

theorem mulBy_X (c : ℂ_[p]) : (g.mulBy c (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p]) =
    subst (C c * g.l : PowerSeries ℂ_[p]) g.ex := by
  have : g.lg (GL3Theta.Xv ()) = g.l := X_subst g.l
  rw [GL3Theta.G1.mulBy, this]
  rfl

theorem transport : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p), (∀ F G : ℂ → ℂ, AlgEnt F → AlgEnt G → (AlgEnt (fun z => F z * G z) ∧ g.atU (fun z => F z * G z) = g.atU F * g.atU G) ∧ (AlgEnt (fun z => F z + G z) ∧ g.atU (fun z => F z + G z) = g.atU F + g.atU G)) ∧ (∀ c ∈ Qbar, AlgEnt (fun _ => c) ∧ g.atU (fun _ => c) = PowerSeries.C (lamC g.lam c)) ∧ (∀ F : ℂ → ℂ, AlgEnt F → F 0 ∈ Qbar ∧ PowerSeries.constantCoeff (g.atU F) = lamC g.lam (F 0)) ∧ (g.Ok → ∀ β ∈ Qbar, ∃ h : PowerSeries ℂ_[p], h = (g.mulBy (lamC g.lam β) (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p]) ∧ PowerSeries.constantCoeff h = 0 ∧ PowerSeries.coeff 1 h = lamC g.lam β ∧ ∀ F : ℂ → ℂ, AlgEnt F → AlgEnt (fun z => F (β * z)) ∧ g.atU (fun z => F (β * z)) = PowerSeries.subst h (g.atU F)) := by
  intro p _ g
  have hs := HasSubst.of_constantCoeff_zero' (const_Cl g ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]))
  refine ⟨fun F G hF hG => ⟨⟨(padicTransportSeries_mul g.lam hF hG).1, ?_⟩, (padicTransportSeries_add g.lam hF hG).1, ?_⟩,
    fun c hc => ⟨(padicTransportSeries_const g.lam hc).1, ?_⟩, fun F hF => ⟨taylorCoeff_zero_eq_value F ▸ hF.2 0, ?_⟩, fun hg β hβ => ?_⟩
  · simp only [atU_eq, (padicTransportSeries_mul g.lam hF hG).2, subst_mul hs]
  · simp only [atU_eq, (padicTransportSeries_add g.lam hF hG).2, subst_add hs]
  · rw [atU_eq, (padicTransportSeries_const g.lam hc).2, subst_C]; rfl
  · rw [atU_eq, const_subst (const_Cl g _), ← coeff_zero_eq_constantCoeff_apply, coeff_padicTransportSeries, taylorCoeff_zero_eq_value]
  · set b := lamC g.lam β with hb
    have hbl := HasSubst.of_constantCoeff_zero' (const_Cl g b)
    have he := HasSubst.of_constantCoeff_zero' hg.2.2.1
    have h0 : constantCoeff (subst (C b * g.l : PowerSeries ℂ_[p]) g.ex : PowerSeries ℂ_[p]) = 0 := by
      rw [const_subst (const_Cl g b), hg.2.2.1]
    have hh := HasSubst.of_constantCoeff_zero' h0
    refine ⟨subst (C b * g.l : PowerSeries ℂ_[p]) g.ex, (mulBy_X g b).symm, h0, ?_, fun F hF =>
      ⟨(taylorSeriesInParameter_rescale_of_algebraic g.lam hF hβ).1, ?_⟩⟩
    · have e := congrArg (coeff 1) hg.2.2.2
      rw [one_subst hg.2.2.1, coeff_one_X] at e
      rw [one_subst (const_Cl g b), coeff_C_mul]
      linear_combination b * e
    · have e : subst (subst (C b * g.l : PowerSeries ℂ_[p]) g.ex : PowerSeries ℂ_[p]) g.l = C b * g.l := by
        rw [← subst_comp_subst_apply he hbl, hg.2.2.2, subst_X hbl]
      rw [atU_eq, atU_eq, (taylorSeriesInParameter_rescale_of_algebraic g.lam hF hβ).2, rescale_eq_subst,
        subst_comp_subst_apply (HasSubst.smul_X' _) hs, subst_comp_subst_apply hs hh,
        subst_smul hs, subst_X hs, subst_mul hh, e, subst_C]
      congr 1
      rw [smul_eq_C_mul]
      exact mul_left_comm _ _ _

end GlobalTheory.SerTransport
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicComplexIntegralBoundedSeriesLaws
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicComplexIntegralBoundedSeriesLaws
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

noncomputable section

namespace GlobalTheory.EvenTheta.SerRing

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

theorem norm_sub_le_max' (x y : K) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  have := IsUltrametricDist.norm_add_le_max x (-y)
  rwa [norm_neg, ← sub_eq_add_neg] at this

theorem norm_finsum_le {ι : Type*} (F : ι → K) {B : ℝ} (hB : 0 ≤ B) (h : ∀ i, ‖F i‖ ≤ B) :
    ‖∑ᶠ i, F i‖ ≤ B := by
  refine finsum_induction (p := fun x => ‖x‖ ≤ B) (by simpa using hB) (fun x y hx hy => ?_) h
  exact (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)

theorem norm_coeff_mul_le (f g : PowerSeries K) (A B : ℝ) (hf : ∀ n, ‖PowerSeries.coeff n f‖ ≤ A)
    (hg : ∀ n, ‖PowerSeries.coeff n g‖ ≤ B) (n : ℕ) : ‖PowerSeries.coeff n (f * g)‖ ≤ A * B := by
  have hA : 0 ≤ A := (norm_nonneg _).trans (hf 0)
  have hB : 0 ≤ B := (norm_nonneg _).trans (hg 0)
  rw [PowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hA hB) fun x _ => ?_
  rw [norm_mul]
  exact mul_le_mul (hf _) (hg _) (norm_nonneg _) hA

theorem norm_coeff_add_le (f g : PowerSeries K) (A B : ℝ) (hf : ∀ n, ‖PowerSeries.coeff n f‖ ≤ A)
    (hg : ∀ n, ‖PowerSeries.coeff n g‖ ≤ B) (n : ℕ) : ‖PowerSeries.coeff n (f + g)‖ ≤ max A B := by
  rw [map_add (f := _)]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max (hf n) (hg n))

theorem norm_coeff_sub_le (f g : PowerSeries K) (A B : ℝ) (hf : ∀ n, ‖PowerSeries.coeff n f‖ ≤ A)
    (hg : ∀ n, ‖PowerSeries.coeff n g‖ ≤ B) (n : ℕ) : ‖PowerSeries.coeff n (f - g)‖ ≤ max A B := by
  rw [map_sub]
  exact (norm_sub_le_max' _ _).trans (max_le_max (hf n) (hg n))

theorem norm_coeff_C_le (c : K) (n : ℕ) : ‖PowerSeries.coeff n (PowerSeries.C c)‖ ≤ ‖c‖ := by
  rw [PowerSeries.coeff_C]
  split_ifs <;> simp

theorem intSer_mul {f g : PowerSeries K} (hf : IntSer f) (hg : IntSer g) : IntSer (f * g) := fun n => by
  simpa using norm_coeff_mul_le f g 1 1 hf hg n

theorem intSer_pow {f : PowerSeries K} (hf : IntSer f) (d : ℕ) : IntSer (f ^ d) := by
  induction d with
  | zero => intro n; simpa using norm_coeff_C_le (1 : K) n
  | succ d ih => rw [pow_succ]; exact intSer_mul ih hf

theorem intSer_inv {f : PowerSeries K} (hf : IntSer f) (h0 : ‖PowerSeries.constantCoeff f‖ = 1) :
    IntSer f⁻¹ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [PowerSeries.coeff_inv]
    split_ifs with hn
    · simp [h0]
    · rw [norm_mul, norm_neg, norm_inv, h0, inv_one, one_mul]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun x _ => ?_
      split_ifs with hx
      · rw [norm_mul]
        exact mul_le_one₀ (hf _) (norm_nonneg _) (ih _ hx)
      · simp

theorem norm_coeff_subst_le (f h : PowerSeries K) (B : ℝ) (hf : ∀ n, ‖PowerSeries.coeff n f‖ ≤ B)
    (hh : IntSer h) (h0 : PowerSeries.constantCoeff h = 0) (n : ℕ) :
    ‖PowerSeries.coeff n (PowerSeries.subst h f : PowerSeries K)‖ ≤ B := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (hf 0)
  rw [PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero' h0)]
  refine norm_finsum_le _ hB fun d => ?_
  rw [smul_eq_mul, norm_mul]
  simpa using mul_le_mul (hf d) (intSer_pow hh d n) (norm_nonneg _) hB

theorem series_ring_laws : ∀ (p : ℕ) [Fact p.Prime], (∀ f g : PowerSeries ℂ_[p], IntSer f → IntSer g → IntSer (f + g) ∧ IntSer (f - g) ∧ IntSer (f * g)) ∧ (∀ f g : PowerSeries ℂ_[p], BddSer f → BddSer g → BddSer (f + g) ∧ BddSer (f - g) ∧ BddSer (f * g)) ∧ (∀ c : ℂ_[p], BddSer (PowerSeries.C c) ∧ (‖c‖ ≤ 1 → IntSer (PowerSeries.C c))) ∧ IntSer (PowerSeries.X : PowerSeries ℂ_[p]) ∧ (∀ f : PowerSeries ℂ_[p], IntSer f → ‖PowerSeries.constantCoeff f‖ = 1 → IntSer f⁻¹) ∧ (∀ (f h : PowerSeries ℂ_[p]) (B : ℝ), (∀ n, ‖PowerSeries.coeff n f‖ ≤ B) → IntSer h → PowerSeries.constantCoeff h = 0 → ∀ n, ‖PowerSeries.coeff n (PowerSeries.subst h f : PowerSeries ℂ_[p])‖ ≤ B) ∧ ∀ (f g : PowerSeries ℂ_[p]) (A B : ℝ), (∀ n, ‖PowerSeries.coeff n f‖ ≤ A) → (∀ n, ‖PowerSeries.coeff n g‖ ≤ B) → ∀ n, ‖PowerSeries.coeff n (f * g)‖ ≤ A * B := by
  intro p _
  refine ⟨fun f g hf hg => ⟨fun n => ?_, fun n => ?_, intSer_mul hf hg⟩,
    fun f g ⟨A, hf⟩ ⟨B, hg⟩ => ⟨⟨_, norm_coeff_add_le f g A B hf hg⟩, ⟨_, norm_coeff_sub_le f g A B hf hg⟩,
      ⟨_, norm_coeff_mul_le f g A B hf hg⟩⟩,
    fun c => ⟨⟨_, norm_coeff_C_le c⟩, fun hc n => (norm_coeff_C_le c n).trans hc⟩, fun n => ?_,
    fun f => intSer_inv, norm_coeff_subst_le, norm_coeff_mul_le⟩
  · simpa using norm_coeff_add_le f g 1 1 hf hg n
  · simpa using norm_coeff_sub_le f g 1 1 hf hg n
  · rw [PowerSeries.coeff_X]
    split_ifs <;> simp

end GlobalTheory.EvenTheta.SerRing
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicComplexIntegralBoundedSeriesLawsStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padicComplex_integral_bounded_series_laws : ∀ (p : ℕ) [Fact p.Prime], (∀ f g : PowerSeries ℂ_[p], IntSer f → IntSer g → IntSer (f + g) ∧ IntSer (f - g) ∧ IntSer (f * g)) ∧ (∀ f g : PowerSeries ℂ_[p], BddSer f → BddSer g → BddSer (f + g) ∧ BddSer (f - g) ∧ BddSer (f * g)) ∧ (∀ c : ℂ_[p], BddSer (PowerSeries.C c) ∧ (‖c‖ ≤ 1 → IntSer (PowerSeries.C c))) ∧ IntSer (PowerSeries.X : PowerSeries ℂ_[p]) ∧ (∀ f : PowerSeries ℂ_[p], IntSer f → ‖PowerSeries.constantCoeff f‖ = 1 → IntSer f⁻¹) ∧ (∀ (f h : PowerSeries ℂ_[p]) (B : ℝ), (∀ n, ‖PowerSeries.coeff n f‖ ≤ B) → IntSer h → PowerSeries.constantCoeff h = 0 → ∀ n, ‖PowerSeries.coeff n (PowerSeries.subst h f : PowerSeries ℂ_[p])‖ ≤ B) ∧ ∀ (f g : PowerSeries ℂ_[p]) (A B : ℝ), (∀ n, ‖PowerSeries.coeff n f‖ ≤ A) → (∀ n, ‖PowerSeries.coeff n g‖ ≤ B) → ∀ n, ‖PowerSeries.coeff n (f * g)‖ ≤ A * B := by
  first | exact @GlobalTheory.EvenTheta.SerRing.series_ring_laws | exact GlobalTheory.EvenTheta.SerRing.series_ring_laws | (intros; apply GlobalTheory.EvenTheta.SerRing.series_ring_laws <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompletedStandardAdelicLatticeProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompletedStandardAdelicLatticeProperties
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators Pointwise

namespace GlobalTheory.CompletedLattice

variable (D : D7)

theorem moves_one (N : ℕ) : Moves D ((1 : GA D N) : GL (Fin N) (AE D)) (stdL D N) := by
  obtain ⟨Lt, h1, h2, -⟩ := GlobalTheory.NormSum.exists_lattice_of_adelic_point D N
  rw [← h2]
  exact (h1 1).1

theorem pt_injective (cc : Ideal (𝓞 D.host.K)) {δ : ℂ} (hδ : δ ≠ 0) {N N' : ℕ}
    {z z' : Matrix (Fin N') (Fin N) D.host.E}
    (h : pt D (tor0 D cc δ) δ z = pt D (tor0 D cc δ) δ z') : z = z' := by
  obtain ⟨τ⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm 1⟩
  refine Matrix.ext fun i j => ?_
  have h1 : δ * embT D τ (z i j) = δ * embT D τ (z' i j) := congrFun (congrFun (congrFun h τ) i) j
  exact (embT D τ).injective (mul_left_cancel₀ hδ h1)

theorem exists_mul_IhE_mem (cc : Ideal (𝓞 D.host.K)) :
    ∃ m : ℕ, 0 < m ∧ ∀ y ∈ IhE D cc, (m : AE D) * y ∈ OhE D := by
  have hb : D.host.𝔟 ≠ ⊥ := by
    intro h
    have h1 := D.host.𝔟_spec.1
    rw [h, Ideal.bot_mul] at h1
    exact differentIdeal_ne_bot h1
  have hB : ((D.host.𝔟 : Ideal (𝓞 D.host.E)) :
      FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 := by
    rwa [Ne, FractionalIdeal.coeIdeal_eq_zero]
  refine ⟨Ideal.absNorm D.host.𝔟, Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff]), fun y hy => ?_⟩
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨c, -, a, ha, s, hs, rfl⟩ := hy
    rw [FractionalIdeal.mem_coe] at ha
    unfold Host.AA0 at ha
    rw [FractionalIdeal.mem_inv_iff hB] at ha
    have h1 := ha _ (FractionalIdeal.mem_coeIdeal_of_mem _ (Ideal.absNorm_mem D.host.𝔟))
    obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).1 h1
    rw [map_natCast] at hr
    have h2 : inc D (r : D.host.E) ∈ OhE D := (AdLattice.incl_mem_iff (F := ℚ) _).2 ⟨r, rfl⟩
    have h3 : inc D ((c : D.host.K) : D.host.E) ∈ OhE D :=
      (AdLattice.incl_mem_iff (F := ℚ) _).2 ⟨algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c, rfl⟩
    have h4 : (Ideal.absNorm D.host.𝔟 : AE D) * (inc D ((((c : D.host.K) : D.host.E)) * a) * s) =
        inc D ((c : D.host.K) : D.host.E) * (inc D (r : D.host.E) * s) := by
      have : (r : D.host.E) = a * (Ideal.absNorm D.host.𝔟 : D.host.E) := hr
      rw [this, map_mul, map_mul, map_natCast]
      ring
    rw [h4]
    exact mul_mem h3 (mul_mem h2 hs)
  | zero => rw [mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [mul_neg]; exact neg_mem hx

theorem completed_lattice : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ), (∀ z : Matrix (Fin N') (Fin N) D.host.E, z.map (inc D) ∈ latA D cc N N' ↔ pt D (tor0 D cc δ) δ z ∈ La0 D (tor0 D cc δ) N N') ∧ (∀ x ∈ La0 D (tor0 D cc δ) N N', ∃ z, x = pt D (tor0 D cc δ) δ z) ∧ (∀ (ζ : XA D N N') (m : ℕ), 0 < m → ∃ z : Matrix (Fin N') (Fin N) D.host.E, ∃ a ∈ latA D cc N N', z.map (inc D) = ζ + m • a) ∧ (∀ ζ : XA D N N', ∃ m : ℕ, 0 < m ∧ m • ζ ∈ latA D cc N N') ∧ (∃ m : ℕ, 0 < m ∧ ∀ y ∈ IhE D cc, (m : AE D) * y ∈ OhE D) ∧ (∃ m : ℕ, 0 < m ∧ ∀ s ∈ OhE D, (m : AE D) * s ∈ IhE D cc) := by
  intro D hg cc δ hc N N'
  have hcc : cc ≠ ⊥ := hc.1.1
  have hδ : δ ≠ 0 := (GlobalTheory.CurveLattice.lattice_of_curve D hg cc δ hc).2.1
  have hn : 0 < Ideal.absNorm cc := Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
  have hA := GlobalTheory.NormSum.exists_pt_of_mem_La_moved D hg cc δ hcc N N' 1 1 _ _ (moves_one D N) (moves_one D N')
  have hB := GlobalTheory.NormSum.pt_mem_La_of_adelic D hg cc δ hcc N N' 1 1 _ _ (moves_one D N) (moves_one D N')
  simp only [OneMemClass.coe_one, inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one] at hA hB
  refine ⟨fun z => ⟨fun h => hB z h, fun h => ?_⟩, fun x hx => ?_, fun ζ m hm => ?_, fun ζ => ?_,
    exists_mul_IhE_mem D cc, _, hn, GlobalTheory.AdelicApprox.absNorm_mul_mem_IhE D cc⟩
  · obtain ⟨z', h1, h2⟩ := hA _ h
    rw [pt_injective D cc hδ h1]
    exact h2
  · obtain ⟨z, h1, -⟩ := hA x hx
    exact ⟨z, h1⟩
  · choose e t ht h using fun (i : Fin N') (j : Fin N) => (GlobalTheory.AdelicApprox.approx_mod_ideal D cc hcc).1 (ζ i j) m hm
    refine ⟨Matrix.of e, Matrix.of t, ht, ?_⟩
    ext i j
    rw [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, nsmul_eq_mul, Matrix.of_apply, Matrix.of_apply, ← h]
    ring
  · choose n hn0 h using fun k : Fin N' × Fin N => GlobalTheory.AdelicApprox.exists_denom D (ζ k.1 k.2)
    refine ⟨Ideal.absNorm cc * ∏ k, n k, Nat.mul_pos hn (Finset.prod_pos fun k _ => hn0 k), fun i j => ?_⟩
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem n (Finset.mem_univ (i, j))
    have h1 := GlobalTheory.AdelicApprox.absNorm_mul_mem_IhE D cc _ (mul_mem (natCast_mem (OhE D) c) (h (i, j)))
    rw [Matrix.smul_apply, nsmul_eq_mul, hc]
    convert h1 using 1
    push_cast
    ring

end GlobalTheory.CompletedLattice
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompletedStandardAdelicLatticePropertiesStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completedStandardAdelicLattice_properties : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ), (∀ z : Matrix (Fin N') (Fin N) D.host.E, z.map (inc D) ∈ latA D cc N N' ↔ pt D (tor0 D cc δ) δ z ∈ La0 D (tor0 D cc δ) N N') ∧ (∀ x ∈ La0 D (tor0 D cc δ) N N', ∃ z, x = pt D (tor0 D cc δ) δ z) ∧ (∀ (ζ : XA D N N') (m : ℕ), 0 < m → ∃ z : Matrix (Fin N') (Fin N) D.host.E, ∃ a ∈ latA D cc N N', z.map (inc D) = ζ + m • a) ∧ (∀ ζ : XA D N N', ∃ m : ℕ, 0 < m ∧ m • ζ ∈ latA D cc N N') ∧ (∃ m : ℕ, 0 < m ∧ ∀ y ∈ IhE D cc, (m : AE D) * y ∈ OhE D) ∧ (∃ m : ℕ, 0 < m ∧ ∀ s ∈ OhE D, (m : AE D) * s ∈ IhE D cc) := by
  first | exact @GlobalTheory.CompletedLattice.completed_lattice | exact GlobalTheory.CompletedLattice.completed_lattice | (intros; apply GlobalTheory.CompletedLattice.completed_lattice <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SqThD
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ThetaTransl

def sqThD (Λ : AddSubgroup ℂ) (v z : ℂ) : ℂ :=
  sgStar Λ z * deriv (GlobalTheory.EvenTheta.sqTh Λ v) z - 2 * deriv (sgStar Λ) z * GlobalTheory.EvenTheta.sqTh Λ v z

end GlobalTheory.ThetaTransl
end
end
