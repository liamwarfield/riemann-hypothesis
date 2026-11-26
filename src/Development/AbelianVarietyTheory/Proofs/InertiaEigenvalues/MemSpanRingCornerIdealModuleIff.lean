module

public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscToDiscInjectiveOfAdicBasis
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisFrobeniusMatrixEqZeroOfDvd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinAinfDiscIsDomainNormBounds
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHwFonCmpTies

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
noncomputable section

namespace GlobalTheory.SpanRing

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices

variable {Γ X A : Type} [Group Γ] [CommRing A] {n : ℕ}
  (T : Subalgebra A (X → A)) (rep : X → (Γ →* GL (Fin n) A))

def gens : Set (X → Matrix (Fin n) (Fin n) A) :=
  {a | ∃ f ∈ T, ∃ h : Γ, a = fun x => f x • mat (rep x) h}

theorem inRing_iff_mem_span (a : X → Matrix (Fin n) (Fin n) A) :
    InRing T rep a ↔ a ∈ Submodule.span A (gens T rep) := by
  constructor
  · rintro ⟨m, f, h, hf, rfl⟩
    exact Submodule.sum_mem _ fun k _ => Submodule.subset_span ⟨f k, hf k, h k, rfl⟩
  · intro ha
    obtain ⟨m, c, g, rfl⟩ := Submodule.mem_span_set'.1 ha
    choose f hf h hh using fun k => (g k).2
    refine ⟨m, fun k => c k • f k, h, fun k => T.smul_mem (hf k) _, ?_⟩
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hh k]
    funext x
    simp [mul_smul]

def ringR : Subalgebra A (X → Matrix (Fin n) (Fin n) A) :=
  (Submodule.span A (gens T rep)).toSubalgebra
    (Submodule.subset_span ⟨1, T.one_mem, 1, by funext x; simp [mat]⟩) (by
      intro a b ha hb
      have : Submodule.span A (gens T rep) * Submodule.span A (gens T rep) ≤
          Submodule.span A (gens T rep) := by
        rw [Submodule.span_mul_span]
        apply Submodule.span_mono
        rintro _ ⟨_, ⟨f, hf, h, rfl⟩, _, ⟨f', hf', h', rfl⟩, rfl⟩
        refine ⟨f * f', T.mul_mem hf hf', h * h', ?_⟩
        funext x
        simp [mat, mul_smul, smul_comm (f x) (f' x)]
      exact this (Submodule.mul_mem_mul ha hb))

theorem _root_.GlobalTheory.SpanRing.mem_ringR (a : X → Matrix (Fin n) (Fin n) A) :
    a ∈ _root_.GlobalTheory.SpanRing.ringR T rep ↔ _root_.GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.InRing T rep a := by
  show a ∈ Submodule.span A (_root_.GlobalTheory.SpanRing.gens T rep) ↔ _
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.InRing
  rw [Submodule.mem_span_set']
  constructor
  · rintro ⟨m, c, g, rfl⟩
    choose F hF h hg using fun k => (g k).2
    refine ⟨m, fun k => c k • F k, h, fun k => T.smul_mem (hF k) (c k), ?_⟩
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hg k]
    funext x
    simp [mul_smul]
  · rintro ⟨m, F, h, hF, rfl⟩
    exact ⟨m, fun _ => 1, fun k => ⟨_, F k, hF k, h k, rfl⟩, by simp⟩

variable {T rep}

theorem _root_.GlobalTheory.SpanRing.inRing_one : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.InRing T rep 1 :=
  (_root_.GlobalTheory.SpanRing.mem_ringR T rep _).1 (_root_.GlobalTheory.SpanRing.ringR T rep).one_mem

theorem _root_.GlobalTheory.SpanRing.inRing_add {a b : X → Matrix (Fin n) (Fin n) A}
    (ha : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.InRing T rep a) (hb : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.InRing T rep b) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.InRing T rep (a + b) :=
  (_root_.GlobalTheory.SpanRing.mem_ringR T rep _).1
    (add_mem ((_root_.GlobalTheory.SpanRing.mem_ringR T rep _).2 ha)
      ((_root_.GlobalTheory.SpanRing.mem_ringR T rep _).2 hb))

theorem _root_.GlobalTheory.SpanRing.inRing_sub {a b : X → Matrix (Fin n) (Fin n) A}
    (ha : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.InRing T rep a) (hb : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.InRing T rep b) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.InRing T rep (a - b) :=
  (_root_.GlobalTheory.SpanRing.mem_ringR T rep _).1
    (sub_mem ((_root_.GlobalTheory.SpanRing.mem_ringR T rep _).2 ha)
      ((_root_.GlobalTheory.SpanRing.mem_ringR T rep _).2 hb))

theorem _root_.GlobalTheory.SpanRing.inRing_mul {a b : X → Matrix (Fin n) (Fin n) A}
    (ha : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.InRing T rep a) (hb : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.InRing T rep b) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.InRing T rep (a * b) :=
  (_root_.GlobalTheory.SpanRing.mem_ringR T rep _).1
    (mul_mem ((_root_.GlobalTheory.SpanRing.mem_ringR T rep _).2 ha)
      ((_root_.GlobalTheory.SpanRing.mem_ringR T rep _).2 hb))

theorem _root_.GlobalTheory.SpanRing.inRing_smul (c : A) {a : X → Matrix (Fin n) (Fin n) A}
    (ha : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.InRing T rep a) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.InRing T rep (c • a) :=
  (_root_.GlobalTheory.SpanRing.mem_ringR T rep _).1
    (Subalgebra.smul_mem _ ((_root_.GlobalTheory.SpanRing.mem_ringR T rep _).2 ha) c)

theorem _root_.GlobalTheory.SpanRing.inRing_sum {ι : Type} (s : Finset ι)
    {a : ι → X → Matrix (Fin n) (Fin n) A}
    (ha : ∀ k ∈ s, _root_.GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.InRing T rep (a k)) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.InRing T rep (∑ k ∈ s, a k) :=
  (_root_.GlobalTheory.SpanRing.mem_ringR T rep _).1
    (Subalgebra.sum_mem _ fun k hk =>
      (_root_.GlobalTheory.SpanRing.mem_ringR T rep _).2 (ha k hk))

theorem _root_.GlobalTheory.SpanRing.inRing_mat (h : Γ) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.InRing T rep (fun x => _root_.GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat (rep x) h) :=
  (_root_.GlobalTheory.SpanRing.mem_ringR T rep _).1
    (Submodule.subset_span ⟨1, T.one_mem, h, by funext x; simp⟩)

theorem _root_.GlobalTheory.SpanRing.eval_mem_span {a : X → Matrix (Fin n) (Fin n) A}
    (ha : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.InRing T rep a) (x : X) :
    a x ∈ Submodule.span A (Set.range (_root_.GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat (rep x))) := by
  obtain ⟨m, f, h, hf, rfl⟩ := ha
  simp only [Finset.sum_apply]
  exact Submodule.sum_mem _ fun k _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨h k, rfl⟩)

theorem _root_.GlobalTheory.SpanRing.exists_inRing_eval (x : X) {M : Matrix (Fin n) (Fin n) A}
    (hM : M ∈ Submodule.span A (Set.range (_root_.GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat (rep x)))) :
    ∃ a, _root_.GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.InRing T rep a ∧ a x = M := by
  induction hM using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨g, rfl⟩ := hy
    exact ⟨_, _root_.GlobalTheory.SpanRing.inRing_mat g, rfl⟩
  | zero =>
    exact ⟨0, (_root_.GlobalTheory.SpanRing.mem_ringR T rep _).1
      (_root_.GlobalTheory.SpanRing.ringR T rep).zero_mem, rfl⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hax⟩ := hy
    obtain ⟨b, hb, hbx⟩ := hz
    exact ⟨a + b, _root_.GlobalTheory.SpanRing.inRing_add ha hb, by simp [hax, hbx]⟩
  | smul c y _ hy =>
    obtain ⟨a, ha, hax⟩ := hy
    exact ⟨c • a, _root_.GlobalTheory.SpanRing.inRing_smul c ha, by simp [hax]⟩

variable (T rep)

def spanRingCornerIdealModule (π : X) (e : X → Matrix (Fin n) (Fin n) A) : Submodule A (X → Matrix (Fin n) (Fin n) A) :=
  Submodule.span A {s | ∃ j ∈ T, j π = 0 ∧ ∃ a, InRing T rep a ∧ s = fun x => j x • (e x * a x * e x)}

theorem _root_.GlobalTheory.SpanRing.mem_spanRingCornerIdealModule_iff (π : X) (e s : X → Matrix (Fin n) (Fin n) A) :
    s ∈ _root_.GlobalTheory.SpanRing.spanRingCornerIdealModule T rep π e ↔ _root_.GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.InMatrixCongruenceModule T rep π e s := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.InMatrixCongruenceModule
  rw [_root_.GlobalTheory.SpanRing.spanRingCornerIdealModule, Submodule.mem_span_set']
  constructor
  · rintro ⟨m, c, g, rfl⟩
    choose J hJ hJπ a ha hg using fun k => (g k).2
    refine ⟨m, fun k => c k • J k, a,
      fun k => ⟨T.smul_mem (hJ k) (c k), by simp [hJπ k], ha k⟩, ?_⟩
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hg k]
    funext x
    simp [mul_smul]
  · rintro ⟨m, J, a, h, rfl⟩
    exact ⟨m, fun _ => 1,
      fun k => ⟨_, J k, (h k).1, (h k).2.1, a k, (h k).2.2, rfl⟩, by simp⟩

variable {T rep}

theorem _root_.GlobalTheory.SpanRing.InMatrixCongruenceModule.eval_eq_zero {π : X}
    {e s : X → Matrix (Fin n) (Fin n) A} (hs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.InMatrixCongruenceModule T rep π e s) :
    s π = 0 := by
  obtain ⟨m, j, a, h, rfl⟩ := hs
  simp only [Finset.sum_apply]
  exact Finset.sum_eq_zero fun k _ => by simp [(h k).2.1]

private theorem inRing_pointwise_smul_of_mem {f : X → A} (hf : f ∈ T)
    {b : X → Matrix (Fin n) (Fin n) A} (hb : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.InRing T rep b) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.InRing T rep (fun x => f x • b x) := by
  have h1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.InRing T rep
      (fun x => f x • _root_.GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat (rep x) 1) :=
    (_root_.GlobalTheory.SpanRing.mem_ringR T rep _).1
      (Submodule.subset_span ⟨f, hf, 1, rfl⟩)
  convert _root_.GlobalTheory.SpanRing.inRing_mul h1 hb using 1
  funext x
  simp [_root_.GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat, smul_mul_assoc]

theorem _root_.GlobalTheory.SpanRing.InMatrixCongruenceModule.inRing {π : X}
    {e s : X → Matrix (Fin n) (Fin n) A} (he : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.InRing T rep e)
    (hs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.InMatrixCongruenceModule T rep π e s) : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.InRing T rep s := by
  obtain ⟨m, j, a, h, rfl⟩ := hs
  refine _root_.GlobalTheory.SpanRing.inRing_sum Finset.univ fun k _ => ?_
  exact inRing_pointwise_smul_of_mem (h k).1
    (_root_.GlobalTheory.SpanRing.inRing_mul (_root_.GlobalTheory.SpanRing.inRing_mul he (h k).2.2) he)

theorem _root_.GlobalTheory.SpanRing.InMatrixCongruenceModule.corner {π : X}
    {e s : X → Matrix (Fin n) (Fin n) A} (he : e * e = e)
    (hs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.InMatrixCongruenceModule T rep π e s) (x : X) :
    e x * s x = s x ∧ s x * e x = s x := by
  have hex : e x * e x = e x := congrFun he x
  obtain ⟨m, j, a, h, rfl⟩ := hs
  simp only [Finset.sum_apply]
  constructor
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [mul_smul_comm, ← mul_assoc, hex]
  · rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [smul_mul_assoc, mul_assoc, hex]

end GlobalTheory.SpanRing

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowLeSpan
open GlobalTheory.IndefiniteRowSideFullHecke.BlockRepresentationsSemisimple Formalism.BasicNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual

namespace GlobalTheory.CoeffEmbedding

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (i : N.Loc)

theorem exists_norm_le : ∃ C : ℝ, ∀ b : N.O i, ‖iotaOQ N A i b‖ ≤ C := by

  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℤ_[N.l i] (N.O i)).FG)
  refine ⟨∑ a ∈ s, ‖iotaOQ N A i a‖, fun b => ?_⟩
  have hb : b ∈ Submodule.span ℤ_[N.l i] (s : Set (N.O i)) := hs ▸ Submodule.mem_top
  obtain ⟨c, -, rfl⟩ := Submodule.mem_span_finset.1 hb
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  have hz : iotaOQ N A i (algebraMap ℤ_[N.l i] (N.O i) (c a)) =
      algebraMap ℚ_[N.l i] (Qbar (N.l i)) (c a : ℚ_[N.l i]) := A.iotaQ_alg i (c a)
  rw [Algebra.smul_def, map_mul, norm_mul, hz]
  have h1 : ‖algebraMap ℚ_[N.l i] (Qbar (N.l i)) (c a : ℚ_[N.l i])‖ ≤ 1 := by
    have he : ‖algebraMap ℚ_[N.l i] (Qbar (N.l i)) (c a : ℚ_[N.l i])‖ = ‖(c a : ℚ_[N.l i])‖ :=
      PadicAlgCl.norm_extends (p := N.l i) _
    rw [he, ← PadicInt.norm_def]
    exact PadicInt.norm_le_one _
  exact mul_le_of_le_one_left (norm_nonneg _) h1

include A in
theorem exists_pow_le_span : ∃ e : ℕ, IsLocalRing.maximalIdeal (N.O i) ^ e ≤
    Ideal.span {((N.l i : ℕ) : N.O i)} := by

  have hl : ((N.l i : ℕ) : N.O i) ≠ 0 := by
    intro h
    have h' := congrArg (iotaOQ N A i) h
    rw [map_natCast, map_zero] at h'
    exact (Nat.cast_ne_zero.2 (Fact.out : (N.l i).Prime).ne_zero) h'
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (N.O i)
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
    (s := Ideal.span {((N.l i : ℕ) : N.O i)}) (by rwa [Ne, Ideal.span_singleton_eq_bot]) hϖ
  refine ⟨n, ?_⟩
  rw [hn, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]

theorem continuous_iotaOQ : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂)
    (A : NAut N) (i : N.Loc), Continuous (iotaOQ N A i) := by
  intro R H what₂ N A i

  obtain ⟨C, hC⟩ := exists_norm_le N A i
  obtain ⟨e, he⟩ := exists_pow_le_span N A i
  refine continuous_of_continuousAt_zero (iotaOQ N A i) ?_
  rw [ContinuousAt, map_zero, Metric.nhds_basis_ball.tendsto_right_iff]
  intro ε hε
  set q : ℝ := ‖((N.l i : ℕ) : Qbar (N.l i))‖ with hq
  have hq1 : q < 1 := by
    have he : ‖algebraMap ℚ_[N.l i] (Qbar (N.l i)) ((N.l i : ℕ) : ℚ_[N.l i])‖ =
        ‖((N.l i : ℕ) : ℚ_[N.l i])‖ := PadicAlgCl.norm_extends (p := N.l i) _
    rw [map_natCast] at he
    rw [hq, he]
    exact Padic.norm_p_lt_one
  have hq0 : 0 ≤ q := norm_nonneg _
  have hC1 : 0 < |C| + 1 := by positivity
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hε hC1) hq1
  obtain ⟨hopen, -⟩ := isAdic_iff.mp (N.O_adic i)
  filter_upwards [(hopen (e * k)).mem_nhds (Ideal.zero_mem _)] with x hx
  have hx' : x ∈ Ideal.span {((N.l i : ℕ) : N.O i) ^ k} := by
    rw [← Ideal.span_singleton_pow, pow_mul] at *
    exact Ideal.pow_right_mono he k hx
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 hx'
  rw [Metric.mem_ball, dist_zero_right, map_mul, map_pow, map_natCast, norm_mul, norm_pow, ← hq]
  calc ‖iotaOQ N A i b‖ * q ^ k ≤ (|C| + 1) * q ^ k :=
        mul_le_mul_of_nonneg_right ((hC b).trans (by linarith [le_abs_self C])) (pow_nonneg hq0 k)
    _ < (|C| + 1) * (ε / (|C| + 1)) := mul_lt_mul_of_pos_left hk hC1
    _ = ε := by field_simp

end GlobalTheory.CoeffEmbedding
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPeriodIsUnitWittTiltAndNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPeriodIsUnitWittTiltAndNeZero
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

noncomputable section

namespace GlobalTheory.BSP

theorem ne_one_of_isEps {l : ℕ} [hl : Fact l.Prime] {ε : OCb l} (hε : GlobalTheory.MemLoc.IsEps ε) : ε ≠ 1 := by
  rintro rfl
  exact hε.2 (by simp)

theorem coeff_zero_ne_zero_of_isPer {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K) {τ : Ainf l}
    (hτ : bk.IsPer τ) : τ.coeff 0 ≠ 0 := by
  obtain ⟨-, ε, η, hε, hφ⟩ := hτ
  intro h
  have h1 := congrArg (WittVector.constantCoeff (p := l) (R := OCb l)) hφ
  simp only [map_mul, map_sub, map_one, WittVector.constantCoeff_apply, WittVector.coeff_frobenius_charP,
    WittVector.teichmuller_coeff_zero, h] at h1
  rw [zero_pow hl.out.ne_zero] at h1
  have hη : (η : Ainf l).coeff 0 ≠ 0 := by
    have := η.isUnit.map (WittVector.constantCoeff (p := l) (R := OCb l))
    rw [WittVector.constantCoeff_apply] at this
    exact this.ne_zero
  exact mul_ne_zero hη (sub_ne_zero.2 (ne_one_of_isEps hε)) h1.symm

theorem ρ₀_pos_lt_one {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K) : 0 < bk.ρ₀ ∧ bk.ρ₀ < 1 := by
  have hl1 : (1 : ℝ≥0) < (l : ℝ≥0) := by exact_mod_cast hl.out.one_lt
  have he : (0 : ℝ) < 1 / (bk.Ep.natDegree : ℝ) := one_div_pos.2 (Nat.cast_pos.2 bk.deg_pos)
  exact ⟨NNReal.rpow_pos (zero_lt_one.trans hl1), NNReal.rpow_lt_one_of_one_lt_of_neg hl1 (neg_neg_of_pos he)⟩

theorem isUnit_inclW_of_isPer : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ →
    IsUnit (inclW l τ) ∧ bk.iA τ ≠ 0 ∧ τ ≠ 0 ∧ ∀ g : GQ l, IsUnit (inclW l (Per.σA g τ)) := by
  intro l _ K bk τ hτ
  have h0 := coeff_zero_ne_zero_of_isPer bk hτ
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    exact h0 (WittVector.zero_coeff _ _ _)
  have hU : IsUnit (inclW l τ) := by
    refine WittVector.isUnit_of_coeff_zero_ne_zero _ ?_
    rw [inclW, WittVector.map_coeff]
    exact (map_ne_zero_iff _ (IsFractionRing.injective (OCb l) (Cb l))).2 h0
  obtain ⟨ι, ⟨tb⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  have hinj := (GlobalTheory.T.closedDisc_toDisc_injective_of_adicBasis l K bk (Ainf l) bk.ev ι tb bk.ρ₀ (ρ₀_pos_lt_one bk).1 (ρ₀_pos_lt_one bk).2).1
  refine ⟨hU, fun h => hτ0 (hinj (h.trans (map_zero _).symm)), hτ0, fun g => ?_⟩
  rw [← galW_inclW]
  exact hU.map (galW l g)

end GlobalTheory.BSP
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPeriodIsUnitWittTiltAndNeZeroStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_period_isUnit_wittTilt_and_ne_zero : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → IsUnit (inclW l τ) ∧ bk.iA τ ≠ 0 ∧ τ ≠ 0 ∧ ∀ g : GQ l, IsUnit (inclW l (Per.σA g τ)) := by
  first | exact @GlobalTheory.BSP.isUnit_inclW_of_isPer | exact GlobalTheory.BSP.isUnit_inclW_of_isPer | (intros; apply GlobalTheory.BSP.isUnit_inclW_of_isPer <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsOpenAdelicUnipotentTimesIntegralOutsideSet
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsOpenAdelicUnipotentTimesIntegralOutsideSet
open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal

namespace GlobalTheory.CellDec
variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem mem_GLint_iff_entries_cell {K : Type} [Field K] {O : Subring K} {x : GL (Fin n) K} :
    x ∈ GLint (Fin n) O ↔ (∀ i j, x.1 i j ∈ O) ∧ ∀ i j, (x⁻¹).1 i j ∈ O := by
  refine ⟨?_, fun h => ⟨⟨Matrix.of fun i j => ⟨_, h.1 i j⟩, Matrix.of fun i j => ⟨_, h.2 i j⟩, ?_, ?_⟩, rfl⟩⟩
  · rintro ⟨y, rfl⟩
    exact ⟨fun i j => (y.1 i j).2, fun i j => ((y⁻¹).1 i j).2⟩
  · refine Matrix.map_injective O.subtype_injective ?_
    simp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.mul_inv
  · refine Matrix.map_injective O.subtype_injective ?_
    simp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.inv_mul

theorem isOpen_intAway (S : Finset (HeightOneSpectrum (𝓞 E))) :
    IsOpen {f : Af E | ∀ v, v ∉ S → f v ∈ v.adicCompletionIntegers E} := by
  refine RestrictedProduct.isOpen_forall_imp_mem (fun v => ?_)
  have h : (v.adicCompletionIntegers E : Set (v.adicCompletion E)) =
      ((Valued.v : Valuation (v.adicCompletion E) _).integer : Set (v.adicCompletion E)) := by
    ext x
    simp only [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers, Valuation.mem_integer_iff]
  rw [h]
  exact Valued.isOpen_integer _

theorem isOpen_US (S : Finset (HeightOneSpectrum (𝓞 E))) : IsOpen (US E n S : Set (GA E n)) := by
  set A := {f : Af E | ∀ v, v ∉ S → f v ∈ v.adicCompletionIntegers E}
  have e : (US E n S : Set (GA E n)) =
      ⋂ i : Fin n, ⋂ j : Fin n, ((fun g : GA E n => ((g : Matrix (Fin n) (Fin n) (Ad E)) i j).2) ⁻¹' A ∩
        (fun g : GA E n => (((g⁻¹ : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) i j).2) ⁻¹' A) := by
    ext g
    simp only [SetLike.mem_coe, US, Subgroup.mem_iInf, Subgroup.mem_comap, Set.mem_iInter, Set.mem_inter_iff,
      Set.mem_preimage, A, Set.mem_setOf_eq, GlobalTheory.LFun.KGL, mem_GLint_iff_entries_cell, ← map_inv]
    constructor
    · intro h i j
      exact ⟨fun v hv => (h v hv).1 i j, fun v hv => (h v hv).2 i j⟩
    · intro h v hv
      exact ⟨fun i j => (h i j).1 v hv, fun i j => (h i j).2 v hv⟩
  rw [e]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => IsOpen.inter ?_ ?_
  · exact (isOpen_intAway S).preimage
      (continuous_snd.comp ((Units.continuous_val (M := Matrix (Fin n) (Fin n) (Ad E))).matrix_elem i j))
  · exact (isOpen_intAway S).preimage
      (continuous_snd.comp ((Units.continuous_coe_inv (M := Matrix (Fin n) (Fin n) (Ad E))).matrix_elem i j))

theorem isOpen_adelicUnipotentTimesIntegralOutsideSet : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))),
    IsOpen (GlobalTheory.CellDec.C0 E n S) := by
  intro E _ _ n S
  have e : C0 E n S = ⋃ u ∈ (NA E n : Set (GA E n)), (fun k => u * k) '' (US E n S : Set (GA E n)) := by
    ext g
    simp only [C0, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_image, SetLike.mem_coe, exists_prop]
    constructor
    · rintro ⟨u, hu, k, hk, rfl⟩; exact ⟨u, hu, k, hk, rfl⟩
    · rintro ⟨u, hu, k, hk, rfl⟩; exact ⟨u, hu, k, hk, rfl⟩
  rw [e]
  exact isOpen_biUnion fun u _ => isOpenMap_mul_left u _ (isOpen_US S)

end GlobalTheory.CellDec
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsOpenAdelicUnipotentTimesIntegralOutsideSetStatement
open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_C0 : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))),
    IsOpen (GlobalTheory.CellDec.C0 E n S) := by
  first | exact @GlobalTheory.CellDec.isOpen_adelicUnipotentTimesIntegralOutsideSet | exact GlobalTheory.CellDec.isOpen_adelicUnipotentTimesIntegralOutsideSet | (intros; apply GlobalTheory.CellDec.isOpen_adelicUnipotentTimesIntegralOutsideSet <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SecondClosedOfFirstClosed
section -- merged from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BlockHodgeTateJumps
noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.IndefiniteRowSideFullHecke.BlockHodgeTateJumps

section Jumps

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (σ : Representation LL G V)

end Jumps

def blockJumps (t : ℕ) : Multiset ℤ := (Finset.Ico (0 : ℤ) (t : ℤ)).val

def SplitsAs {k Γ : Type} [Field k] [Group Γ] {n r t : ℕ} (M : Γ →* Matrix (Fin n) (Fin n) k)
    (P : Γ →* Matrix (Fin r) (Fin r) k) (χ : Fin t → Γ → k) : Prop :=
  ∃ e : (Fin n → k) ≃ₗ[k] ((Fin r → k) × (Fin t → k)), ∀ (g : Γ) (u : Fin n → k),
    e ((M g).mulVec u) = ((P g).mulVec (e u).1, fun c => χ c g * (e u).2 c)

section HidaSetting

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc)
  (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i))) (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i)))

def BlockSplit (π : N.X i) : Prop :=
  SplitsAs (mapM (toK N i) (rO N i r π)) (mapM (toK N i) (rhoO N i ρ π))
    (fun (c : Fin R.t) g => toK N i ((N.chi i ((c : ℕ) + 1) g : (N.O i)ˣ) : N.O i))

def HidaSetting (π : N.X i) : Prop :=
  GoodR N i r ∧ π ∈ N.Z i ∧
    Continuous (fun g => ((ρ π g : GL (Fin R.r) (N.O i)) : Matrix (Fin R.r) (Fin R.r) (N.O i))) ∧
    BlockSplit N i r ρ π

variable {N} (L : LocTheory) (nbr : Br.NBr N)

end HidaSetting

end GlobalTheory.IndefiniteRowSideFullHecke.BlockHodgeTateJumps

end
end

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.BlockJumpsCompare

section Continuity

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
  [IsTopologicalRing O] {X : Type} [TopologicalSpace X]

theorem continuous_of_mul (had : IsAdic (IsLocalRing.maximalIdeal O)) {d : O} (hd : d ≠ 0) {f : X → O}
    (h : Continuous fun x => d * f x) : Continuous f := by
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd hp
  have hm : ∀ (n : ℕ) (y : O), y ∈ (IsLocalRing.maximalIdeal O) ^ n ↔ p ^ n ∣ y := by
    intro n y
    rw [hp.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  rw [continuous_iff_continuousAt]
  intro x₀
  have h0 : Filter.Tendsto (fun x => (u : O) * p ^ k * (f x - f x₀)) (nhds x₀) (nhds 0) := by
    have := (h.sub (continuous_const (y := (u : O) * p ^ k * f x₀))).tendsto x₀
    simpa [mul_sub, Pi.sub_def] using this
  have h1 : Filter.Tendsto (fun x => f x - f x₀) (nhds x₀) (nhds 0) := by
    rw [had.hasBasis_nhds_zero.tendsto_right_iff] at h0 ⊢
    intro n _
    filter_upwards [h0 (k + n) trivial] with x hx
    have hx' := (hm _ _).1 hx
    refine (hm _ _).2 ?_
    rw [pow_add, mul_assoc, Units.dvd_mul_left] at hx'
    exact (mul_dvd_mul_iff_left (pow_ne_zero k hp.ne_zero)).1 hx'
  simpa [ContinuousAt] using h1.add_const (f x₀)

theorem continuous_of_comb (had : IsAdic (IsLocalRing.maximalIdeal O)) {ι : Type} [Fintype ι]
    (c : ι → FractionRing O) {h : ι → X → O} (hh : ∀ j, Continuous (h j)) {f : X → O}
    (hf : ∀ x, algebraMap O (FractionRing O) (f x) =
      ∑ j, c j * algebraMap O (FractionRing O) (h j x)) : Continuous f := by
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) c
  choose a ha using hd
  refine continuous_of_mul had (nonZeroDivisors.ne_zero d.2) ?_
  have : (fun x => (d : O) * f x) = fun x => ∑ j, a j * h j x := by
    funext x
    apply IsFractionRing.injective O (FractionRing O)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_mul, map_sum, hf, ha, Finset.mul_sum, Algebra.smul_def, mul_assoc]
  rw [this]
  exact continuous_finsetSum _ fun j _ => continuous_const.mul (hh j)

theorem continuous_of_splitsAs (had : IsAdic (IsLocalRing.maximalIdeal O)) {Γ : Type} [Group Γ]
    [TopologicalSpace Γ] {n r t : ℕ} {M : Γ →* Matrix (Fin n) (Fin n) O}
    {P : Γ →* Matrix (Fin r) (Fin r) O} {χ : Fin t → Γ → FractionRing O}
    (hs : GlobalTheory.IndefiniteRowSideFullHecke.BlockHodgeTateJumps.SplitsAs (mapM (algebraMap O (FractionRing O)) M)
      (mapM (algebraMap O (FractionRing O)) P) χ)
    (hM : Continuous fun g => M g) : Continuous fun g => P g := by
  obtain ⟨e, he⟩ := hs
  refine continuous_matrix fun a b => ?_
  set u : Fin n → FractionRing O := e.symm (Pi.single b 1, 0) with hu
  refine continuous_of_comb had
    (fun jk : Fin n × Fin n => (e (Pi.single jk.1 1)).1 a * u jk.2)
    (h := fun jk g => M g jk.1 jk.2) (fun jk => hM.matrix_elem jk.1 jk.2) fun g => ?_
  have h1 := congrFun (congrArg Prod.fst (he g u)) a
  have h2 : ∀ v : Fin n → FractionRing O, (e v).1 a = ∑ j, (e (Pi.single j 1)).1 a * v j := by
    intro v
    conv_lhs => rw [pi_eq_sum_univ' v]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, Prod.fst_sum, Finset.sum_apply, mul_comm]
  rw [h2] at h1
  simp only [hu, LinearEquiv.apply_symm_apply, Matrix.mulVec_single_one] at h1
  rw [← hu] at h1
  rw [Fintype.sum_prod_type]
  refine Eq.trans ?_ (h1.symm.trans ?_)
  · rfl
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    change _ * (algebraMap O (FractionRing O) (M g j k) * u k) = _
    ring

end Continuity

section Glob

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc)
  (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i))) (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i)))

theorem blockSum_iff (π : N.X i) :
    GlobalTheory.IndefiniteRowSideFullHecke.BlockJumpCount.IsBlockSum N i r ρ π ↔ GlobalTheory.IndefiniteRowSideFullHecke.BlockHodgeTateJumps.BlockSplit N i r ρ π := Iff.rfl

theorem continuous_rho (π : N.X i) (hr : IsHeckeGalois N i π (r π))
    (hs : GlobalTheory.IndefiniteRowSideFullHecke.BlockJumpCount.IsBlockSum N i r ρ π) :
    Continuous (fun g => ((ρ π g : GL (Fin R.r) (N.O i)) : Matrix (Fin R.r) (Fin R.r) (N.O i))) :=
  continuous_of_splitsAs (M := rO N i r π) (P := rhoO N i ρ π) (N.O_adic i)
    ((blockSum_iff N i r ρ π).1 hs) hr.1

end Glob

end GlobalTheory.BlockJumpsCompare

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlaceOfOverTypePrime
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlaceOfOverTypePrime
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf
open scoped Pointwise

namespace GlobalTheory.TypeSplit

theorem main : ∀ (D : D7) (k : Fin 2), ∀ w ∈ placesOver D.host.E (D.host.g k), IsSplitPl D.host w := by
  intro D k w hw
  haveI : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  have hP := (GlobalTheory.Mem.Chr.splitsC_place (p := D.host.g k) (D.host.g_prime k) (D.nd.g_split k) w hw).2.2
  by_contra hn
  have hle : ∀ x ∈ w.asIdeal, D.host.conj • x ∈ w.asIdeal := by
    intro x hx
    by_contra hy
    refine hn ⟨x, hx, fun y e hy' => hy ?_⟩
    have : y = D.host.conj • x := Subtype.ext e
    rwa [← this]
  refine GlobalTheory.TypePlace.conj_ne_one D.host (hP _ ?_)
  have h1 : D.host.conj • w.asIdeal ≤ w.asIdeal := by
    intro y hy
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hy
    simpa using hle _ hy
  have hm : (D.host.conj • w.asIdeal).IsMaximal :=
    Ideal.map_isMaximal_of_equiv (MulSemiringAction.toRingEquiv _ (𝓞 D.host.E) D.host.conj) (hp := w.isMaximal)
  exact hm.eq_of_le w.isMaximal.ne_top h1

end GlobalTheory.TypeSplit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlaceOfOverTypePrimeStatement
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSplitPlace_of_over_type_prime : ∀ (D : D7) (k : Fin 2), ∀ w ∈ placesOver D.host.E (D.host.g k), IsSplitPl D.host w := by
  first | exact @GlobalTheory.TypeSplit.main | exact GlobalTheory.TypeSplit.main | (intros; apply GlobalTheory.TypeSplit.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineDiscPeriodsFrobeniusEqMul
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineDiscPeriodsFrobeniusEqMul
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

noncomputable section

namespace GlobalTheory.BSP

theorem mul_comm_of_mul_eq_smul_one {R : Type} [CommRing R] [IsDomain R] {n : Type} [Fintype n] [DecidableEq n]
    (A B : Matrix n n R) (c : R) (hc : c ≠ 0) (h : A * B = c • (1 : Matrix n n R)) :
    B * A = c • (1 : Matrix n n R) := by
  have hdet : B.det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det h
    rw [Matrix.det_mul, h0, mul_zero, Matrix.det_smul, Matrix.det_one, mul_one] at h1
    exact pow_ne_zero _ hc h1.symm
  have h2 : (B * A - c • (1 : Matrix n n R)) * B = 0 := by
    rw [Matrix.sub_mul, Matrix.mul_assoc, h, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul,
      sub_self]
  have h3 : B.det • (B * A - c • (1 : Matrix n n R)) = 0 := by
    have := congrArg (· * B.adjugate) h2
    simp only [Matrix.zero_mul] at this
    rw [Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one] at this
    exact this
  have h4 : B * A - c • (1 : Matrix n n R) = 0 := by
    ext i j
    have := congrFun (congrFun h3 i) j
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at this
    simpa using (mul_eq_zero.1 this).resolve_left hdet
  exact sub_eq_zero.1 h4

variable {l : ℕ} [hl : Fact l.Prime]

theorem BK.ρ₀_pos_lt_one {K : FinExt l} (bk : BK K) : 0 < bk.ρ₀ ∧ bk.ρ₀ < 1 := by
  have hl1 : (1 : ℝ≥0) < (l : ℝ≥0) := by exact_mod_cast hl.out.one_lt
  have he : (0 : ℝ) < (bk.Ep.natDegree : ℝ) := by exact_mod_cast bk.deg_pos
  refine ⟨NNReal.rpow_pos (zero_lt_one.trans hl1), NNReal.rpow_lt_one_of_one_lt_of_neg hl1 ?_⟩
  have : (0 : ℝ) < 1 / (bk.Ep.natDegree : ℝ) := by positivity
  linarith

theorem BK.frobenius_ev_E_ne_zero {K : FinExt l} (bk : BK K) {τ : Ainf l} (hτ : bk.IsPer τ) :
    WittVector.frobenius (bk.ev bk.E) ≠ 0 := by
  intro h0
  obtain ⟨h1, ε, η, hε, hφ⟩ := hτ
  have hε1 : ε ≠ 1 := by
    rintro rfl
    obtain ⟨-, hu⟩ := hε
    exact hu (by rw [map_one]; simp)
  have hc0 : τ.coeff 0 ≠ 0 := by
    intro h0
    have h1 := congrArg (fun x => WittVector.constantCoeff x) hφ
    change (WittVector.frobenius τ).coeff 0 = _ at h1
    rw [WittVector.coeff_frobenius_charP, h0, zero_pow (Fact.out : l.Prime).ne_zero, map_mul, map_sub, map_one] at h1
    change 0 = WittVector.constantCoeff (η : Ainf l) * ((WittVector.teichmuller l ε).coeff 0 - 1) at h1
    rw [WittVector.teichmuller_coeff_zero] at h1
    have hη : IsUnit (WittVector.constantCoeff (η : Ainf l)) := η.isUnit.map _
    rcases mul_eq_zero.1 h1.symm with h | h
    · exact hη.ne_zero h
    · exact hε1 (sub_eq_zero.1 h)
  have h2 := congrArg WittVector.frobenius h1
  rw [map_mul, h0, zero_mul] at h2
  have h3 := congrArg (fun x : Ainf l => x.coeff 0) h2
  simp only [WittVector.coeff_frobenius_charP, WittVector.zero_coeff] at h3
  exact hc0 (pow_eq_zero_iff (Fact.out : l.Prime).ne_zero |>.1 (pow_eq_zero_iff (Fact.out : l.Prime).ne_zero |>.1 h3))

theorem Seed.crystallineDiscPeriods_frobenius_eq_mul : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ)
    (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ),
    ∀ Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) WittVector.frobenius Φ →
      ((l : bk.DA bk.ρ₀) ^ (s.c₁ + s.c₂) * bk.iS (frobS l bk.a bk.E) ^ s.N) • s.W.map Φ =
        s.W * (s.X' * s.F.map (C : Wq l bk.a →+* bk.S) * s.X.map (frobS l bk.a)).map bk.iS := by
  intro l _ K bk τ hτ d ρ _ s Φ hΦ
  obtain ⟨h0, h1⟩ := bk.ρ₀_pos_lt_one
  haveI : IsDomain (bk.DA bk.ρ₀) := (GlobalTheory.T.breuilKisin_ainfDisc_isDomain_norm_bounds l K bk bk.ρ₀ h0 h1).1
  obtain ⟨ι, ⟨tb⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  have hinj : Function.Injective bk.iA := (GlobalTheory.T.closedDisc_toDisc_injective_of_adicBasis l K bk (Ainf l) bk.ev ι tb bk.ρ₀ h0 h1).1
  have hΦS : ∀ x, Φ (bk.iS x) = bk.iS (frobS l bk.a x) := fun x => by
    change Φ (bk.iA (bk.ev x)) = bk.iA (bk.ev (frobS l bk.a x))
    rw [hΦ.ext, bk.ev_frob]
  have he : bk.iS (frobS l bk.a bk.E) ≠ 0 := by
    change bk.iA (bk.ev (frobS l bk.a bk.E)) ≠ 0
    rw [bk.ev_frob, ← map_zero bk.iA]
    exact fun h => bk.frobenius_ev_E_ne_zero hτ (hinj h)
  have hL0 : (l : bk.DA bk.ρ₀) ≠ 0 := fun h =>
    WittVector.p_nonzero l (OCb l) (hinj (by rw [map_natCast, map_zero]; exact h))
  have hQP : s.X.map (bk.iS.comp (frobS l bk.a)) * s.X'.map (bk.iS.comp (frobS l bk.a)) =
      ((l : bk.DA bk.ρ₀) ^ s.c₂ * bk.iS (frobS l bk.a bk.E) ^ (2 * s.N)) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)) := by
    rw [← Matrix.map_mul, s.X_mul, Matrix.map_smul' _ _ _ (map_mul _), Matrix.map_one _ (map_zero _) (map_one _)]
    simp only [RingHom.comp_apply, map_mul, map_pow, map_natCast]
  have hc : (l : bk.DA bk.ρ₀) ^ s.c₂ * bk.iS (frobS l bk.a bk.E) ^ (2 * s.N) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hL0) (pow_ne_zero _ he)
  have hPQ := mul_comm_of_mul_eq_smul_one _ _ _ hc hQP
  have hA : (s.X'.map bk.iS).map Φ = s.X'.map (bk.iS.comp (frobS l bk.a)) := by
    rw [Matrix.map_map]; congr 1; funext x; exact hΦS x
  have hF : (s.F.map (C : Wq l bk.a →+* bk.S)).map bk.iS = s.F.map (bk.iS.comp C) := by
    rw [Matrix.map_map]; rfl
  have hX : (s.X.map (frobS l bk.a)).map bk.iS = s.X.map (bk.iS.comp (frobS l bk.a)) := by
    rw [Matrix.map_map]; rfl
  have h2 := congrArg (· * s.X.map (bk.iS.comp (frobS l bk.a))) (s.φ Φ hΦ)
  simp only [Matrix.map_mul, hA] at h2
  rw [Matrix.smul_mul, Matrix.mul_assoc (s.W.map Φ), hPQ, Matrix.mul_smul, Matrix.mul_one, smul_smul] at h2
  rw [Matrix.map_mul, Matrix.map_mul, hF, hX]
  refine smul_right_injective (Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)) (pow_ne_zero s.N he) ?_
  dsimp only
  calc bk.iS (frobS l bk.a bk.E) ^ s.N • (((l : bk.DA bk.ρ₀) ^ (s.c₁ + s.c₂) * bk.iS (frobS l bk.a bk.E) ^ s.N) •
        s.W.map Φ)
      = ((l : bk.DA bk.ρ₀) ^ s.c₁ * ((l : bk.DA bk.ρ₀) ^ s.c₂ * bk.iS (frobS l bk.a bk.E) ^ (2 * s.N))) •
        s.W.map Φ := by rw [smul_smul]; congr 1; ring
    _ = _ := h2
    _ = _ := by rw [Matrix.smul_mul]; simp only [Matrix.mul_assoc]

end GlobalTheory.BSP
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineDiscPeriodsFrobeniusEqMulStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discPeriods_map_frobenius_eq_mul : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ), ∀ Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) WittVector.frobenius Φ → ((l : bk.DA bk.ρ₀) ^ (s.c₁ + s.c₂) * bk.iS (frobS l bk.a bk.E) ^ s.N) • s.W.map Φ = s.W * (s.X' * s.F.map (C : Wq l bk.a →+* bk.S) * s.X.map (frobS l bk.a)).map bk.iS := by
  first | exact @GlobalTheory.BSP.Seed.crystallineDiscPeriods_frobenius_eq_mul | exact GlobalTheory.BSP.Seed.crystallineDiscPeriods_frobenius_eq_mul | (intros; apply GlobalTheory.BSP.Seed.crystallineDiscPeriods_frobenius_eq_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HostRamificationIdxEqOne
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.TripleGal

theorem host_ramificationIdx_eq_one :
    ∀ (D : D7) (p : ℕ), p.Prime → p ∉ D.host.small → p ≠ D.host.q → p ≠ D.host.d → ∀ P ∈ placesOver D.host.E p, P.asIdeal.ramificationIdx ℤ = 1 :=
  fun D _ hp h2 hq hd P hP => GlobalTheory.HubLoc.ramIdx_eq_one D.host hp (UpperTheory.Small.not_dvd_condN D.host hp h2 hq hd) P hP

end GlobalTheory.TripleGal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWachFunctorComparisonOfBhattScholze
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWachFunctorComparisonOfBhattScholze
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.HWL

theorem exists_hw_fon_cmp_of_integral : GlobalTheory.Published.BhattScholzeIntegral →
    ∀ D : D7, ∃ (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), Nonempty (CmpOf D.loc D.locA HW F) := by
  intro hI D
  obtain ⟨H, F, hC, -⟩ := exists_hw_fon_cmp_ties (GlobalTheory.T.bhattScholze_coefficients_of_padicInt_lattices hI) D.loc D.locA D.locT
  exact ⟨H, F, hC⟩

end GlobalTheory.HWL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWachFunctorComparisonOfBhattScholzeStatement
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_wachFunctor_comparison_of_bhattScholze : GlobalTheory.Published.BhattScholzeIntegral → ∀ D : D7, ∃ (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), Nonempty (CmpOf D.loc D.locA HW F) := by
  first | exact @GlobalTheory.HWL.exists_hw_fon_cmp_of_integral | exact GlobalTheory.HWL.exists_hw_fon_cmp_of_integral | (intros; apply GlobalTheory.HWL.exists_hw_fon_cmp_of_integral <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsOrientedPrismUniformizerFrameBreuilKisinHomStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOrientedPrismUniformizerFrame_breuilKisinHom : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K)) (f : Hom bk.prism B),
    IsFrame bk B (BK.hf (bk := bk) f bk.E) (BK.hf (bk := bk) f X) := by
  intro l _ K bk B f
  have hI : bk.prism.I.map f.f = B.I :=
    GlobalTheory.T.prism_hom_map_ideal_eq l _ bk.prism B f
  refine ⟨hI.symm.trans ?_, ?_⟩
  · change (Ideal.span {bk.E}).map (BK.hf (bk := bk) f) = _
    rw [Ideal.map_span, Set.image_singleton]
  · apply f.f_str
    change Ideal.Quotient.mk (Ideal.span {bk.E}) X = bk.str.toRingHom (bk.str.symm _)
    simp
end
