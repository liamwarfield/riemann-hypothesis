module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointPicardClassEqTranslateOfTrivialLambda

@[expose] public section

attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL
attribute [local instance 10000] GlobalTheory.SplitWeil.matrixMeasurableSpace

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShellSumEquivariantNonzero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaIntegralShellsVanishBeyondPeriodRamifiedStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaIntegralShellsVanishBeyondPeriodRamified
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnCartanDoubleCosetShellIntegrand
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnCartanDoubleCosetShellIntegrand
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instMeasMat
open GlobalTheory.IndefiniteRowSideFullHecke.ScaledIntegerPeriodic

namespace GlobalTheory.ShellInt

theorem integrableOn_shell : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ϖ : kˣ) (ν : kˣ →* ℂˣ) (e : ℕ), CondLE ϖ e ν →
    ∀ (a : ℕ) (μ : Measure (GL (Fin a) k)) [μ.IsHaarMeasure] (φ : Matrix (Fin a) (Fin a) k → ℂ),
      φ ∈ SB (Matrix (Fin a) (Fin a) k) → ∀ (n : Fin a → ℤ) (z : ℂ),
        IntegrableOn (fun g : GL (Fin a) k => φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z) (shellSet ϖ n) μ := by
  intro k _ _ _ _ _ _ ϖ ν e hν a μ _ φ hφ n z
  have hcomp : IsCompact (shellSet ϖ n : Set (GL (Fin a) k)) :=
    (isCompact_KO.mul isCompact_singleton).mul isCompact_KO
  let χ : GL (Fin a) k →* ℂ :=
    { toFun := fun g => (ν (gdet g) : ℂ) * apow (gdet g) z
      map_one' := by simp
      map_mul' := fun g h => by simp only [gdet_mul, map_mul, Units.val_mul, apow_mul]; ring }
  have hχ1 : ∀ g ∈ detCong (ϖ ^ e) (Fin a), χ g = 1 := by
    intro g hg
    have h1 : ν (gdet g) = 1 := hν _ hg.2
    have h2 : apow (gdet g) z = 1 := apow_of_valuation_eq_one (valuation_gdet_of_mem_KO hg.1) z
    simp [χ, h1, h2]
  have hχc : Continuous χ := by
    refine continuous_of_continuousAt_one χ ?_
    have hev : (fun _ => (1 : ℂ)) =ᶠ[nhds (1 : GL (Fin a) k)] χ := by
      filter_upwards [(isOpen_detCong (ϖ ^ e) (Fin a)).mem_nhds (one_mem _)] with g hg
      exact (hχ1 g hg).symm
    have := (continuousAt_const (x := (1 : GL (Fin a) k)) (y := (1 : ℂ))).congr hev
    simpa using this
  have hcont : Continuous (fun g : GL (Fin a) k => φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z) := by
    have h := (hφ.1.continuous.comp Units.continuous_val).mul hχc
    refine h.congr fun g => ?_
    simp [χ, mul_assoc]
  exact hcont.continuousOn.integrableOn_compact hcomp

end GlobalTheory.ShellInt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnCartanDoubleCosetShellIntegrandStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instMeasMat
open GlobalTheory.IndefiniteRowSideFullHecke.ScaledIntegerPeriodic

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrableOn_cartanDoubleCoset_shellIntegrand : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ϖ : kˣ) (ν : kˣ →* ℂˣ) (e : ℕ), CondLE ϖ e ν →
    ∀ (a : ℕ) (μ : Measure (GL (Fin a) k)) [μ.IsHaarMeasure] (φ : Matrix (Fin a) (Fin a) k → ℂ),
      φ ∈ SB (Matrix (Fin a) (Fin a) k) → ∀ (n : Fin a → ℤ) (z : ℂ),
        IntegrableOn (fun g : GL (Fin a) k => φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z) (shellSet ϖ n) μ := by
  first | exact @GlobalTheory.ShellInt.integrableOn_shell | exact GlobalTheory.ShellInt.integrableOn_shell | (intros; apply GlobalTheory.ShellInt.integrableOn_shell <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetIntegralLeftCosetShellIntegrandEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetIntegralLeftCosetShellIntegrandEqZero
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instMeasMat
open GlobalTheory.IndefiniteRowSideFullHecke.ScaledIntegerPeriodic

noncomputable section

namespace GlobalTheory.ShellPiece

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem val_le_one_of_mem {t : k} (h : t ∈ 𝒪[k]) : valuation k t ≤ 1 := h

theorem diagGL_mem_KO {a : ℕ} (c : Fin a → kˣ) (hc : ∀ j, valuation k (c j : k) = 1) :
    diagGL c ∈ KO k (Fin a) := by
  rw [mem_KO_iff]
  refine ⟨fun r s => ?_, fun r s => ?_⟩
  · show valuation k ((diagGL c).val r s) ≤ 1
    rw [diagGL_val, diagonal_apply]
    split_ifs
    · exact (hc r).le
    · simp
  · show valuation k (((diagGL c)⁻¹ : GL (Fin a) k).val r s) ≤ 1
    rw [show ((diagGL c)⁻¹ : GL (Fin a) k).val = diagonal fun j => (((c j)⁻¹ : kˣ) : k) from rfl, diagonal_apply]
    split_ifs
    · simp [hc r]
    · simp

end GlobalTheory.ShellPiece


open GlobalTheory.ShellPiece in
theorem GlobalTheory.ShellPiece.setIntegral_coset_eq_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ϖ : kˣ), IsUnif ϖ → ∀ (ν : kˣ →* ℂˣ) (a : ℕ) (μ : Measure (GL (Fin a) k))
    [μ.IsHaarMeasure] (φ : Matrix (Fin a) (Fin a) k → ℂ) (M : ℤ), IsPeriodic ϖ M φ →
    ∀ (n : Fin a → ℤ) (i : Fin a), M ≤ n i → ∀ u : kˣ, valuation k (u : k) = 1 → ν u ≠ 1 →
    ∀ x ∈ KO k (Fin a), ∀ z : ℂ,
      ∫ g in {g : GL (Fin a) k | (x * diagGL (fun i => ϖ ^ n i))⁻¹ * g ∈ KO k (Fin a)},
        φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z ∂μ = 0 := by
  intro k _ _ _ _ _ _ ϖ hϖ ν a μ _ φ M hφ n i hi u hu hν x hx z
  set d : GL (Fin a) k := diagGL (fun j => ϖ ^ n j) with hd
  set D : GL (Fin a) k := diagGL (Pi.mulSingle i u) with hD
  have hDK : D ∈ KO k (Fin a) := diagGL_mem_KO _ fun j => by
    by_cases h : j = i
    · subst h; simpa using hu
    · simp [Pi.mulSingle_eq_of_ne h]
  have hcomm : Commute d D := Units.ext (by simp [hd, hD, diagonal_mul_diagonal, mul_comm])
  set k0 := x * D * x⁻¹ with hk0
  have hk0K : k0 ∈ KO k (Fin a) := mul_mem (mul_mem hx hDK) (inv_mem hx)
  set S := {g : GL (Fin a) k | (x * d)⁻¹ * g ∈ KO k (Fin a)} with hS
  have key : ∀ g, (x * d)⁻¹ * (k0 * g) = D * ((x * d)⁻¹ * g) := fun g => by
    have h1 : d⁻¹ * D = D * d⁻¹ := (hcomm.inv_left).eq
    calc (x * d)⁻¹ * (k0 * g) = d⁻¹ * D * (x⁻¹ * g) := by rw [hk0]; group
      _ = D * d⁻¹ * (x⁻¹ * g) := by rw [h1]
      _ = D * ((x * d)⁻¹ * g) := by group
  have hpre : (fun g => k0 * g) ⁻¹' S = S := by
    ext g
    simp only [Set.mem_preimage, hS, Set.mem_setOf_eq, key]
    exact Subgroup.mul_mem_cancel_left _ hDK
  have hdetD : gdet D = u := by
    rw [hD, gdet, det_diagGL]
    simp
  have hdetk0 : gdet k0 = u := by
    rw [hk0, gdet_mul, gdet_mul, hdetD, mul_comm (gdet x), mul_assoc, ← gdet_mul, mul_inv_cancel]
    simp

  have hϖ1 : valuation k (ϖ : k) ≤ 1 := hϖ.mem
  have hpow : valuation k ((ϖ ^ n i : kˣ) : k) ≤ valuation k ((ϖ ^ M : kˣ) : k) := by
    have e : ϖ ^ n i = ϖ ^ M * ϖ ^ (n i - M).toNat := by
      rw [← zpow_natCast, Int.toNat_of_nonneg (by omega), ← _root_.zpow_add]; congr 1; ring
    rw [e, Units.val_mul, map_mul, Units.val_pow_eq_pow_val, map_pow]
    exact mul_le_of_le_one_right' (pow_le_one₀ zero_le hϖ1)
  have hu1 : valuation k ((u : k) - 1) ≤ 1 :=
    ((valuation k).map_sub _ _).trans (max_le hu.le (by simp))
  have hZ : ∀ y ∈ KO k (Fin a), x.val * ((D.val - 1) * d.val) * y.val ∈ scaledInt ϖ a M := by
    intro y hy r s
    have e1 : (D.val - 1) * d.val = diagonal fun j => ((((Pi.mulSingle i u : Fin a → kˣ) j : kˣ) : k) - 1) * ((ϖ ^ n j : kˣ) : k) := by
      rw [hD, hd, diagGL_val, diagGL_val]
      ext p q
      by_cases hpq : p = q
      · subst hpq; simp [Matrix.mul_apply, diagonal_apply, Matrix.sub_apply, Matrix.one_apply]
      · simp [Matrix.mul_apply, diagonal_apply, Matrix.sub_apply, Matrix.one_apply, hpq]
    rw [e1, Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [mul_diagonal, Pi.mulSingle_eq_same, map_mul, map_mul, map_mul]
      have hx1 := val_le_one_of_mem ((mem_KO_iff x).1 hx |>.1 r i)
      have hy1 := val_le_one_of_mem ((mem_KO_iff y).1 hy |>.1 i s)
      calc _ ≤ 1 * (1 * valuation k ((ϖ ^ n i : kˣ) : k)) * 1 := by gcongr
        _ ≤ _ := by simpa using hpow
    · intro j _ hj
      simp [mul_diagonal, Pi.mulSingle_eq_of_ne hj]
    · simp
  have hF : ∀ g ∈ S, φ (k0 * g).val * (ν (gdet (k0 * g)) : ℂ) * apow (gdet (k0 * g)) z =
      (ν u : ℂ) * (φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z) := by
    intro g hg
    set y := (x * d)⁻¹ * g with hy
    have hyK : y ∈ KO k (Fin a) := hg
    have hg' : g = x * d * y := by rw [hy]; group
    have hv : (k0 * g).val = g.val + x.val * ((D.val - 1) * d.val) * y.val := by
      have : k0 * g = x * D * d * y := by rw [hg', hk0]; group
      rw [this, hg']
      simp only [Units.val_mul]
      noncomm_ring
    rw [hv, hφ _ _ (hZ y hyK), gdet_mul, hdetk0, map_mul, Units.val_mul, apow_mul,
      apow_of_valuation_eq_one hu]
    ring
  have hSm : MeasurableSet S :=
    (isOpen_KO.preimage (continuous_const.mul continuous_id)).measurableSet
  have h := (measurePreserving_mul_left μ k0).setIntegral_preimage_emb (measurableEmbedding_mulLeft k0)
    (fun g : GL (Fin a) k => φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z) S
  rw [hpre, setIntegral_congr_fun hSm (fun g hg => hF g hg), integral_const_mul] at h
  have hne : (ν u : ℂ) - 1 ≠ 0 := sub_ne_zero.2 fun e => hν (Units.val_eq_one.1 e)
  have h2 : ((ν u : ℂ) - 1) * ∫ g in S, φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z ∂μ = 0 := by
    rw [sub_mul, h]; ring
  exact (mul_eq_zero.1 h2).resolve_left hne

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetIntegralLeftCosetShellIntegrandEqZeroStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instMeasMat
open GlobalTheory.IndefiniteRowSideFullHecke.ScaledIntegerPeriodic

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.setIntegral_leftCoset_shellIntegrand_eq_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ϖ : kˣ), IsUnif ϖ → ∀ (ν : kˣ →* ℂˣ) (a : ℕ) (μ : Measure (GL (Fin a) k))
    [μ.IsHaarMeasure] (φ : Matrix (Fin a) (Fin a) k → ℂ) (M : ℤ), IsPeriodic ϖ M φ →
    ∀ (n : Fin a → ℤ) (i : Fin a), M ≤ n i → ∀ u : kˣ, valuation k (u : k) = 1 → ν u ≠ 1 →
    ∀ x ∈ KO k (Fin a), ∀ z : ℂ,
      ∫ g in {g : GL (Fin a) k | (x * diagGL (fun i => ϖ ^ n i))⁻¹ * g ∈ KO k (Fin a)},
        φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z ∂μ = 0 := by
  first | exact @GlobalTheory.ShellPiece.setIntegral_coset_eq_zero | exact GlobalTheory.ShellPiece.setIntegral_coset_eq_zero | (intros; apply GlobalTheory.ShellPiece.setIntegral_coset_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanDoubleCosetFiniteDisjointLeftCosets
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanDoubleCosetFiniteDisjointLeftCosets
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instMeasMat
open GlobalTheory.IndefiniteRowSideFullHecke.ScaledIntegerPeriodic

namespace GlobalTheory.ShellCosets

theorem piece_eq_of_mem {G : Type*} [Group G] (K : Subgroup G) {c c' g : G}
    (h1 : c⁻¹ * g ∈ K) (h2 : c'⁻¹ * g ∈ K) :
    {h : G | c⁻¹ * h ∈ K} = {h : G | c'⁻¹ * h ∈ K} := by
  ext h
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hh
    have := K.mul_mem (K.mul_mem h2 (K.inv_mem h1)) hh
    simpa [mul_assoc] using this
  · intro hh
    have := K.mul_mem (K.mul_mem h1 (K.inv_mem h2)) hh
    simpa [mul_assoc] using this

theorem shell_cosets : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ϖ : kˣ) (a : ℕ) (n : Fin a → ℤ), ∃ t : Finset (GL (Fin a) k), (∀ x ∈ t, x ∈ KO k (Fin a)) ∧
      shellSet ϖ n = ⋃ x ∈ t, {g : GL (Fin a) k | (x * diagGL (fun i => ϖ ^ n i))⁻¹ * g ∈ KO k (Fin a)} ∧
      (t : Set (GL (Fin a) k)).PairwiseDisjoint
        (fun x => {g : GL (Fin a) k | (x * diagGL (fun i => ϖ ^ n i))⁻¹ * g ∈ KO k (Fin a)}) := by
  intro k _ _ _ _ ϖ a n
  classical
  set d : GL (Fin a) k := diagGL (fun i => ϖ ^ n i) with hd
  set K := KO k (Fin a) with hK
  set P : GL (Fin a) k → Set (GL (Fin a) k) := fun x => {g | (x * d)⁻¹ * g ∈ K} with hP
  have hPo : ∀ x, IsOpen (P x) := fun x =>
    (GlobalTheory.SplitFlip.isOpen_KO (k := k) (n := Fin a)).preimage (continuous_const_mul _)
  have hsub : ∀ x ∈ K, P x ⊆ shellSet ϖ n := by
    intro x hx g hg
    rw [mem_shellSet]
    exact ⟨x, hx, _, hg, by rw [← hd]; group⟩
  have himg : shellSet ϖ n = (fun p : GL (Fin a) k × GL (Fin a) k => p.1 * d * p.2) '' ((K : Set _) ×ˢ (K : Set _)) := by
    ext g
    rw [mem_shellSet]
    constructor
    · rintro ⟨x, hx, y, hy, rfl⟩; exact ⟨(x, y), ⟨hx, hy⟩, rfl⟩
    · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩; exact ⟨x, hx, y, hy, rfl⟩
  have hcomp : IsCompact (shellSet ϖ n) := by
    rw [himg]
    exact (GlobalTheory.SplitFlip.isCompact_KO.prod GlobalTheory.SplitFlip.isCompact_KO).image (by fun_prop)
  have hcov : shellSet ϖ n ⊆ ⋃ x : K, P x := by
    intro g hg
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_shellSet.mp hg
    refine Set.mem_iUnion.mpr ⟨⟨x, hx⟩, ?_⟩
    show (x * d)⁻¹ * (x * (diagGL fun i => ϖ ^ n i) * y) ∈ K
    rw [← hd]
    convert hy using 1
    group
  obtain ⟨s, hs⟩ := hcomp.elim_finite_subcover (fun x : K => P x) (fun x => hPo x) hcov
  let s' : Finset (GL (Fin a) k) := s.image Subtype.val
  have hs'K : ∀ x ∈ s', x ∈ K := by
    intro x hx; obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hx; exact y.2
  let r : Set (GL (Fin a) k) → GL (Fin a) k := Function.invFunOn P (s' : Set _)
  let t : Finset (GL (Fin a) k) := (s'.image P).image r
  have hr : ∀ x ∈ s', r (P x) ∈ s' ∧ P (r (P x)) = P x := fun x hx =>
    ⟨Function.invFunOn_mem ⟨x, hx, rfl⟩, Function.invFunOn_eq ⟨x, hx, rfl⟩⟩
  have ht : ∀ y ∈ t, ∃ x ∈ s', y = r (P x) := by
    intro y hy
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hQ
    exact ⟨x, hx, rfl⟩
  refine ⟨t, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := ht y hy
    exact hs'K _ (hr x hx).1
  · apply Set.Subset.antisymm
    · intro g hg
      obtain ⟨x, hxs, hgx⟩ := Set.mem_iUnion₂.mp (hs hg)
      have hx' : (x : GL (Fin a) k) ∈ s' := Finset.mem_image_of_mem _ hxs
      refine Set.mem_iUnion₂.mpr ⟨r (P x), Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hx'), ?_⟩
      show g ∈ P (r (P x))
      rw [(hr _ hx').2]; exact hgx
    · intro g hg
      obtain ⟨y, hy, hgy⟩ := Set.mem_iUnion₂.mp hg
      obtain ⟨x, hx, rfl⟩ := ht y hy
      exact hsub _ (hs'K _ (hr x hx).1) hgy
  · intro y hy y' hy' hne
    obtain ⟨x, hx, rfl⟩ := ht y hy
    obtain ⟨x', hx', rfl⟩ := ht y' hy'
    rw [Function.onFun, Set.disjoint_left]
    intro g hg hg'
    apply hne
    have := piece_eq_of_mem K hg hg'
    change P (r (P x)) = P (r (P x')) at this
    rw [(hr x hx).2, (hr x' hx').2] at this
    rw [this]

end GlobalTheory.ShellCosets
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanDoubleCosetFiniteDisjointLeftCosetsStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instMeasMat
open GlobalTheory.IndefiniteRowSideFullHecke.ScaledIntegerPeriodic

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cartanDoubleCoset_finite_disjoint_leftCosets : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ϖ : kˣ) (a : ℕ) (n : Fin a → ℤ), ∃ t : Finset (GL (Fin a) k), (∀ x ∈ t, x ∈ KO k (Fin a)) ∧
      shellSet ϖ n = ⋃ x ∈ t, {g : GL (Fin a) k | (x * diagGL (fun i => ϖ ^ n i))⁻¹ * g ∈ KO k (Fin a)} ∧
      (t : Set (GL (Fin a) k)).PairwiseDisjoint
        (fun x => {g : GL (Fin a) k | (x * diagGL (fun i => ϖ ^ n i))⁻¹ * g ∈ KO k (Fin a)}) := by
  first | exact @GlobalTheory.ShellCosets.shell_cosets | exact GlobalTheory.ShellCosets.shell_cosets | (intros; apply GlobalTheory.ShellCosets.shell_cosets <;> assumption)
end
end

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instMeasMat

noncomputable section
namespace GlobalTheory.ShellVan
open GlobalTheory.IndefiniteRowSideFullHecke.ScaledIntegerPeriodic

theorem valuation_unif_zpow {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {ϖ : kˣ} (hϖ : IsUnif ϖ) (m : ℤ) : valuation k ((ϖ ^ m : kˣ) : k) = uniformizer k ^ m := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hϖ]

theorem shell_eq_zero_of_support : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ϖ : kˣ), IsUnif ϖ → ∀ (ν : kˣ →* ℂˣ) (a : ℕ) (μ : Measure (GL (Fin a) k))
    (φ : Matrix (Fin a) (Fin a) k → ℂ) (M' : ℕ), Function.support φ ⊆ scaledInt ϖ a (-(M' : ℤ)) →
    ∀ n : Fin a → ℤ, ¬ (∀ i, -(M' : ℤ) ≤ n i) → ∀ z : ℂ, shell μ ϖ ν z φ n = 0 := by
  intro k _ _ _ _ _ _ ϖ hϖ ν a μ φ M' hS n hn z
  push_neg at hn
  obtain ⟨i, hi⟩ := hn
  rw [shell]
  refine setIntegral_eq_zero_of_forall_eq_zero fun g hg => ?_
  obtain ⟨x, hx, y, hy, rfl⟩ := mem_shellSet.1 hg
  suffices h : φ (x * diagGL (fun i => ϖ ^ n i) * y).val = 0 by rw [h, zero_mul, zero_mul]
  by_contra hne
  have hmem := hS hne
  have hd : (diagGL (fun i => ϖ ^ n i)).val =
      (x⁻¹).val * (x * diagGL (fun i => ϖ ^ n i) * y).val * (y⁻¹).val := by
    rw [← Units.val_mul, ← Units.val_mul]
    congr 1
    group
  have hx' := ((mem_KO_iff x).1 hx).2
  have hy' := ((mem_KO_iff y).1 hy).2
  have bound : ∀ r s, valuation k ((diagGL (fun i => ϖ ^ n i)).val r s) ≤
      valuation k (((ϖ ^ (-(M' : ℤ)) : kˣ) : k)) := by
    intro r s
    rw [hd, Matrix.mul_apply]
    refine Valuation.map_sum_le _ fun t _ => ?_
    rw [map_mul, Matrix.mul_apply]
    calc _ ≤ valuation k (((ϖ ^ (-(M' : ℤ)) : kˣ) : k)) * 1 :=
          mul_le_mul' (Valuation.map_sum_le _ fun q _ => by
            rw [map_mul]
            exact (mul_le_of_le_one_left' ((Valuation.mem_integer_iff _ _).1 (hx' r q))).trans (hmem q t))
            ((Valuation.mem_integer_iff _ _).1 (hy' t s))
      _ = _ := mul_one _
  have h1 := bound i i
  simp only [diagGL_val, diagonal_apply_eq] at h1
  rw [valuation_unif_zpow hϖ, valuation_unif_zpow hϖ] at h1
  have hu0 : (0 : ValueGroupWithZero k) < uniformizer k := zero_lt_iff.2 uniformizer_ne_zero
  have h2 := (zpow_le_zpow_iff_right_of_lt_one₀ hu0 uniformizer_lt_one).1 h1
  omega

theorem shell_lemma : ShellLemma := by
  intro k _ _ _ _ _ _ ϖ hϖ ν e hram hcond a μ hμ φ hφ
  have : μ.IsHaarMeasure := hμ
  have hint := GlobalTheory.T.integrableOn_cartanDoubleCoset_shellIntegrand k ϖ ν e hcond a μ φ hφ
  have h2 : ∀ M : ℤ, IsPeriodic ϖ M φ → ∀ n : Fin a → ℤ, (∃ i, M ≤ n i) → ∀ z : ℂ, shell μ ϖ ν z φ n = 0 := by
    rintro M hM n ⟨i, hi⟩ z
    obtain ⟨u, hu1, hu2⟩ : ∃ u : kˣ, valuation k (u : k) = 1 ∧ ν u ≠ 1 := by
      by_contra h
      push_neg at h
      exact hram h
    obtain ⟨t, htK, heq, hdisj⟩ := GlobalTheory.T.cartanDoubleCoset_finite_disjoint_leftCosets k ϖ a n
    rw [shell, heq, integral_biUnion_finset t]
    · exact Finset.sum_eq_zero fun x hx =>
        GlobalTheory.T.setIntegral_leftCoset_shellIntegrand_eq_zero k ϖ hϖ ν a μ φ M hM n i hi u hu1 hu2 x (htK x hx) z
    · intro x _
      exact (isOpen_KO.preimage (continuous_const.mul continuous_id)).measurableSet
    · exact hdisj
    · intro x hx
      refine (hint n z).mono_set ?_
      rw [heq]
      exact Set.subset_biUnion_of_mem (u := fun x => {g : GL (Fin a) k | (x * diagGL (fun i => ϖ ^ n i))⁻¹ * g ∈ KO k (Fin a)}) hx
  have h3 := shell_eq_zero_of_support k ϖ hϖ ν a μ φ
  refine ⟨hint, h2, h3, ?_⟩
  obtain ⟨N, M, hN, hM⟩ := GlobalTheory.SBUniform.exists_bound_period k (Fin a) φ hφ
  have hP : IsPeriodic ϖ (M : ℤ) φ := fun X Z hZ => hM X Z fun i j => by
    have := hZ i j
    rwa [valuation_unif_zpow hϖ] at this
  have hS : Function.support φ ⊆ scaledInt ϖ a (-(N : ℤ)) := fun X hX i j => by
    rw [valuation_unif_zpow hϖ]
    exact hN X hX i j
  refine ((Set.Finite.pi (t := fun _ : Fin a => Set.Ico (-(N : ℤ)) M) fun _ => Set.finite_Ico _ _).preimage
    Subtype.val_injective.injOn).subset ?_
  rintro ⟨n, hn⟩ ⟨z, hz⟩ i -
  refine ⟨?_, ?_⟩
  · by_contra h
    exact hz (h3 N hS n (fun h' => h (h' i)) z)
  · by_contra h
    exact hz (h2 M hP n ⟨i, not_lt.1 h⟩ z)

end GlobalTheory.ShellVan
end
end

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zetaIntegralShells_vanish_beyondPeriod_ramified : GlobalTheory.IndefiniteRowSideFullHecke.ScaledIntegerPeriodic.ShellLemma := by
  first | exact @GlobalTheory.ShellVan.shell_lemma | exact GlobalTheory.ShellVan.shell_lemma | (intros; apply GlobalTheory.ShellVan.shell_lemma <;> assumption)
end

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

noncomputable section
namespace GlobalTheory.ShellSumEqv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_unique_shell {ϖ : kˣ} (hϖ : IsUnif ϖ) {a : ℕ} (g : GL (Fin a) k) :
    ∃! m : {m : Fin a → ℤ // Antitone m}, g ∈ shellSet ϖ m.1 := by
  obtain ⟨m, hm, x, hx, y, hy, e⟩ := GlobalTheory.SortedCartan.cartan_antitone k a ϖ hϖ g
  have ht : ∀ m : Fin a → ℤ, GlobalTheory.GLDoubling.torusElt k (Fin a) ϖ m = diagGL fun i => ϖ ^ m i :=
    fun m => Units.ext (by rw [GlobalTheory.GLDoubling.val_torusElt, diagGL_val]; simp [Units.val_zpow_eq_zpow_val])
  refine ⟨⟨m, hm⟩, mem_shellSet.2 ⟨x, hx, y, hy, by rw [e, ht]⟩, ?_⟩
  rintro ⟨m', hm'⟩ hmem
  obtain ⟨x', hx', y', hy', e'⟩ := mem_shellSet.1 hmem
  have E : (x'⁻¹ * x) * diagGL (fun i => ϖ ^ m i) * (y * y'⁻¹) = diagGL fun i => ϖ ^ m' i := by
    have h1 : x * diagGL (fun i => ϖ ^ m i) * y = x' * diagGL (fun i => ϖ ^ m' i) * y' := by
      rw [← ht, ← e]; exact e'
    calc _ = x'⁻¹ * (x * diagGL (fun i => ϖ ^ m i) * y) * y'⁻¹ := by group
      _ = _ := by rw [h1]; group
  have E' := congrArg Units.val E
  simp only [Units.val_mul, diagGL_val, Units.val_zpow_eq_zpow_val] at E'
  exact Subtype.ext (Formalism.UG.P.cartan_unique_gen 𝒪[k] (valuation k) (fun _ => Iff.rfl) (ϖ : k) ϖ.ne_zero
    (hϖ ▸ uniformizer_lt_one) m m' hm hm' (x'⁻¹ * x) (mul_mem (inv_mem hx') hx) (y * y'⁻¹)
    (mul_mem hy (inv_mem hy')) (by simpa only [Units.val_mul] using E')).symm

theorem isOpen_shellSet (ϖ : kˣ) {a : ℕ} (m : Fin a → ℤ) : IsOpen (shellSet ϖ m : Set (GL (Fin a) k)) := by
  have : shellSet ϖ m = ⋃ x ∈ (KO k (Fin a) : Set (GL (Fin a) k)),
      (fun g => (x * diagGL (fun i => ϖ ^ m i))⁻¹ * g) ⁻¹' (KO k (Fin a) : Set _) := by
    ext g
    simp only [mem_shellSet, Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe, exists_prop]
    constructor
    · rintro ⟨x, hx, y, hy, rfl⟩
      exact ⟨x, hx, by simpa [mul_assoc] using hy⟩
    · rintro ⟨x, hx, hy⟩
      exact ⟨x, hx, _, hy, by group⟩
  rw [this]
  exact isOpen_biUnion fun x _ => isOpen_KO.preimage (continuous_const.mul continuous_id)

theorem apow_of_mem_shellSet {ϖ : kˣ} {a : ℕ} {m : Fin a → ℤ} {g : GL (Fin a) k} (hg : g ∈ shellSet ϖ m)
    (w : ℂ) : apow (gdet g) w = apow (gdet (diagGL fun i => ϖ ^ m i)) w := by
  obtain ⟨x, hx, y, hy, rfl⟩ := mem_shellSet.1 hg
  rw [gdet_mul, gdet_mul, apow_mul, apow_mul, apow_of_valuation_eq_one (valuation_gdet_of_mem_KO hx),
    apow_of_valuation_eq_one (valuation_gdet_of_mem_KO hy)]
  ring

theorem continuous_char_det {a : ℕ} {ν : kˣ →* ℂˣ} (hν : IsSmU ν) :
    Continuous fun g : GL (Fin a) k => ((ν (gdet g) : ℂˣ) : ℂ) := by
  set χ : GL (Fin a) k →* ℂˣ := ν.comp Matrix.GeneralLinearGroup.det with hχd
  have hcd : Continuous (Matrix.GeneralLinearGroup.det : GL (Fin a) k → kˣ) :=
    Units.continuous_iff.2 ⟨Units.continuous_val.matrix_det, Units.continuous_coe_inv.matrix_det⟩
  have hχ : IsOpen (χ.ker : Set (GL (Fin a) k)) := hν.1.preimage hcd
  refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_eventually_eq _).mpr fun g0 => ?_)
  have hn : (fun g => g0⁻¹ * g) ⁻¹' (χ.ker : Set (GL (Fin a) k)) ∈ nhds g0 :=
    (hχ.preimage (continuous_const.mul continuous_id)).mem_nhds (by simp)
  filter_upwards [hn] with g hg
  have hg' : χ (g0⁻¹ * g) = 1 := hg
  have e : χ g = χ g0 := by
    have := congrArg (χ g0 * ·) hg'
    simp only [← map_mul, mul_inv_cancel_left, mul_one] at this
    exact this
  exact congrArg (fun u : ℂˣ => (u : ℂ)) e

variable [MeasurableSpace k] [BorelSpace k]

theorem exists_integrable {a : ℕ} {ν : kˣ →* ℂˣ} (hν : IsSmU ν) {φ : Matrix (Fin a) (Fin a) k → ℂ}
    (hφ : φ ∈ SB (Matrix (Fin a) (Fin a) k)) : ∃ B : ℝ, ∀ w : ℂ, B < w.re →
      Integrable (fun g : GL (Fin a) k => φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) w)
        (haarVol (KO k (Fin a))) := by
  obtain ⟨b, hb⟩ := GlobalTheory.ZetaConvergence.integrable_zetaIntegrand k Measure.addHaar (Fin a)
    (fun g => ((ν (gdet g) : ℂˣ) : ℂ)) 0 (continuous_char_det hν)
    (fun N => ⟨1, fun g _ => by simp [hν.2]⟩) φ hφ
  refine ⟨b + ((a : ℝ) - 1) / 2, fun w hw => ?_⟩
  have h1 := hb (w - ((a : ℂ) - 1) / 2) (by
    have : (((a : ℂ) - 1) / 2).re = ((a : ℝ) - 1) / 2 := by simp
    rw [Complex.sub_re, this]; linarith)
  have hfun : GlobalTheory.InertSupp.zetaIntegrand φ (fun g => ((ν (gdet g) : ℂˣ) : ℂ)) (w - ((a : ℂ) - 1) / 2) =
      fun g : GL (Fin a) k => φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) w := by
    funext g
    simp [GlobalTheory.InertSupp.zetaIntegrand, GlobalTheory.SmGL.val_absPow, apow]
  rw [hfun] at h1
  haveI := isHaarMeasure_volGL (k := k) (n := Fin a) Measure.addHaar
  rw [Measure.isMulLeftInvariant_eq_smul (haarVol (KO k (Fin a))) (volGL Measure.addHaar (Fin a))]
  exact h1.smul_measure_nnreal

section Shells
variable {ϖ : kˣ} {ν : kˣ →* ℂˣ} {e : ℕ}

theorem finite_shells (hϖ : IsUnif ϖ) (hram : ¬ IsUnram ν) (hcond : CondLE ϖ e ν) {a : ℕ}
    {φ : Matrix (Fin a) (Fin a) k → ℂ} (hφ : φ ∈ SB (Matrix (Fin a) (Fin a) k)) :
    {m : {m : Fin a → ℤ // Antitone m} | ∃ z : ℂ, shell (haarVol (KO k (Fin a))) ϖ ν z φ m.1 ≠ 0}.Finite :=
  (GlobalTheory.T.zetaIntegralShells_vanish_beyondPeriod_ramified k ϖ hϖ ν e hram hcond a (haarVol (KO k (Fin a))) φ hφ).2.2.2

theorem integrableOn_shell (hϖ : IsUnif ϖ) (hram : ¬ IsUnram ν) (hcond : CondLE ϖ e ν) {a : ℕ}
    {φ : Matrix (Fin a) (Fin a) k → ℂ} (hφ : φ ∈ SB (Matrix (Fin a) (Fin a) k)) (m : Fin a → ℤ) (w : ℂ) :
    IntegrableOn (fun g : GL (Fin a) k => φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) w) (shellSet ϖ m)
      (haarVol (KO k (Fin a))) :=
  (GlobalTheory.T.zetaIntegralShells_vanish_beyondPeriod_ramified k ϖ hϖ ν e hram hcond a (haarVol (KO k (Fin a))) φ hφ).1 m w

theorem support_finite (hϖ : IsUnif ϖ) (hram : ¬ IsUnram ν) (hcond : CondLE ϖ e ν) {a : ℕ}
    {φ : Matrix (Fin a) (Fin a) k → ℂ} (hφ : φ ∈ SB (Matrix (Fin a) (Fin a) k)) (w : ℂ) :
    (Function.support fun m : {m : Fin a → ℤ // Antitone m} =>
      shell (haarVol (KO k (Fin a))) ϖ ν w φ m.1).Finite :=
  (finite_shells hϖ hram hcond hφ).subset fun m hm => ⟨w, hm⟩

theorem integral_eq_shellSum (hϖ : IsUnif ϖ) (hram : ¬ IsUnram ν) (hcond : CondLE ϖ e ν) {a : ℕ}
    {φ : Matrix (Fin a) (Fin a) k → ℂ} (hφ : φ ∈ SB (Matrix (Fin a) (Fin a) k)) {w : ℂ}
    (hint : Integrable (fun g : GL (Fin a) k => φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) w)
      (haarVol (KO k (Fin a)))) :
    ∫ g, φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) w ∂(haarVol (KO k (Fin a))) =
      shellSum (haarVol (KO k (Fin a))) ϖ ν w φ := by
  set S : {m : Fin a → ℤ // Antitone m} → Set (GL (Fin a) k) := fun m => shellSet ϖ m.1 with hS
  have hU : ⋃ m, S m = Set.univ :=
    Set.eq_univ_of_forall fun g => Set.mem_iUnion.2 (exists_unique_shell hϖ g).exists
  have hd : Pairwise (Function.onFun Disjoint S) := fun m m' hne =>
    Set.disjoint_left.2 fun g h1 h2 => hne ((exists_unique_shell hϖ g).unique h1 h2)
  haveI : BorelSpace (GL (Fin a) k) := borel_GL
  have hm : ∀ m, MeasurableSet (S m) := fun m => (isOpen_shellSet ϖ m.1).measurableSet
  calc _ = ∫ g in ⋃ m, S m, φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) w ∂(haarVol (KO k (Fin a))) := by
        rw [hU, Measure.restrict_univ]
    _ = ∑' m, ∫ g in S m, φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) w ∂(haarVol (KO k (Fin a))) :=
        integral_iUnion hm hd hint.integrableOn
    _ = ∑ᶠ m, ∫ g in S m, φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) w ∂(haarVol (KO k (Fin a))) :=
        tsum_eq_finsum (support_finite hϖ hram hcond hφ w)
    _ = _ := rfl

theorem shell_eq_mul [BorelSpace k] {a : ℕ} (μ : Measure (GL (Fin a) k)) (φ : Matrix (Fin a) (Fin a) k → ℂ) (m : Fin a → ℤ)
    (w : ℂ) : shell μ ϖ ν w φ m = (∫ g in shellSet ϖ m, φ g.val * (ν (gdet g) : ℂ) ∂μ) *
      apow (gdet (diagGL fun i => ϖ ^ m i)) w := by
  unfold shell
  rw [← integral_mul_const]
  haveI : BorelSpace (GL (Fin a) k) := borel_GL
  exact setIntegral_congr_fun (isOpen_shellSet ϖ m).measurableSet fun g hg => by
    simp only [apow_of_mem_shellSet hg]

theorem differentiable_shellSum (hϖ : IsUnif ϖ) (hram : ¬ IsUnram ν) (hcond : CondLE ϖ e ν) {a : ℕ}
    {φ : Matrix (Fin a) (Fin a) k → ℂ} (hφ : φ ∈ SB (Matrix (Fin a) (Fin a) k)) :
    Differentiable ℂ fun w => shellSum (haarVol (KO k (Fin a))) ϖ ν w φ := by
  set F := (finite_shells hϖ hram hcond hφ).toFinset
  have h : (fun w => shellSum (haarVol (KO k (Fin a))) ϖ ν w φ) =
      fun w => ∑ m ∈ F, shell (haarVol (KO k (Fin a))) ϖ ν w φ m.1 := by
    funext w
    refine finsum_eq_sum_of_support_subset _ fun m hm => ?_
    simpa [F] using (⟨w, hm⟩ : ∃ z : ℂ, shell (haarVol (KO k (Fin a))) ϖ ν z φ m.1 ≠ 0)
  rw [h]
  refine Differentiable.fun_sum fun m _ => ?_
  show Differentiable ℂ fun w => shell (haarVol (KO k (Fin a))) ϖ ν w φ m.1
  rw [funext fun w => shell_eq_mul (ϖ := ϖ) (ν := ν) (haarVol (KO k (Fin a))) φ m.1 w]
  refine Differentiable.const_mul ?_ _
  have hp := nabs_pos' (gdet (diagGL fun i => ϖ ^ m.1 i))
  exact differentiable_id.const_cpow (Or.inl (by exact_mod_cast hp.ne'))

end Shells

section Main
variable {ϖ : kˣ} {ν : kˣ →* ℂˣ} {e : ℕ}

theorem differentiable_apow (x : kˣ) : Differentiable ℂ fun w => apow x w := by
  have hp := nabs_pos' x
  unfold apow
  exact differentiable_id.const_cpow (Or.inl (by exact_mod_cast hp.ne'))

theorem shellSum_add (hϖ : IsUnif ϖ) (hram : ¬ IsUnram ν) (hcond : CondLE ϖ e ν) {a : ℕ}
    {φ φ' : Matrix (Fin a) (Fin a) k → ℂ} (hφ : φ ∈ SB (Matrix (Fin a) (Fin a) k))
    (hφ' : φ' ∈ SB (Matrix (Fin a) (Fin a) k)) (w : ℂ) :
    shellSum (haarVol (KO k (Fin a))) ϖ ν w (φ + φ') =
      shellSum (haarVol (KO k (Fin a))) ϖ ν w φ + shellSum (haarVol (KO k (Fin a))) ϖ ν w φ' := by
  unfold shellSum
  rw [← finsum_add_distrib (support_finite hϖ hram hcond hφ w) (support_finite hϖ hram hcond hφ' w)]
  refine finsum_congr fun m => ?_
  unfold shell
  rw [← integral_add (integrableOn_shell hϖ hram hcond hφ m.1 w) (integrableOn_shell hϖ hram hcond hφ' m.1 w)]
  congr 1
  funext g
  simp only [Pi.add_apply]
  ring

theorem shellSum_eqv (hϖ : IsUnif ϖ) (hν : IsSmU ν) (hram : ¬ IsUnram ν) (hcond : CondLE ϖ e ν) {a : ℕ}
    (g₁ g₂ : GL (Fin a) k) {φ : Matrix (Fin a) (Fin a) k → ℂ} (hφ : φ ∈ SB (Matrix (Fin a) (Fin a) k)) (z : ℂ) :
    (ν (gdet g₁ * gdet g₂) : ℂ) * apow (gdet g₁ * gdet g₂) z *
      shellSum (haarVol (KO k (Fin a))) ϖ ν z (fun X => φ (g₁.val * X * g₂.val)) =
      shellSum (haarVol (KO k (Fin a))) ϖ ν z φ := by
  have hφ' := comp_mul_mem_SB g₁ g₂ hφ
  obtain ⟨B₁, h₁⟩ := exists_integrable hν hφ
  obtain ⟨B₂, h₂⟩ := exists_integrable hν hφ'
  set B := max (max B₁ B₂) ((a : ℝ) - 1) with hB
  have hL : Differentiable ℂ fun w => (ν (gdet g₁ * gdet g₂) : ℂ) * apow (gdet g₁ * gdet g₂) w *
      shellSum (haarVol (KO k (Fin a))) ϖ ν w (fun X => φ (g₁.val * X * g₂.val)) :=
    ((differentiable_apow _).const_mul _).mul (differentiable_shellSum hϖ hram hcond hφ')
  have hR := differentiable_shellSum hϖ hram hcond hφ
  have ho : IsOpen {w : ℂ | B < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hE := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (fun w _ => hL.analyticAt w)
    (fun w _ => hR.analyticAt w) isPreconnected_univ (Set.mem_univ (((B + 1 : ℝ)) : ℂ)) (by
      filter_upwards [ho.mem_nhds (show B < (((B + 1 : ℝ)) : ℂ).re by simp)] with w hw
      have hw : B < w.re := hw
      have hB1 : B₁ < w.re := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hw
      have hB2 : B₂ < w.re := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hw
      have hB3 : (a : ℝ) - 1 < w.re := lt_of_le_of_lt (le_max_right _ _) hw
      rw [← integral_eq_shellSum hϖ hram hcond hφ (h₁ w hB1),
        ← integral_eq_shellSum hϖ hram hcond hφ' (h₂ w hB2)]
      exact (GlobalTheory.T.zeta_integral_equivariant_nonzero k a ν w hν hB3).1.2.2 g₁ g₂ φ hφ)
  exact hE (Set.mem_univ z)

theorem exists_ne_zero (hϖ : IsUnif ϖ) (hcond : CondLE ϖ e ν) {a : ℕ} (z : ℂ) :
    ∃ φ ∈ SB (Matrix (Fin a) (Fin a) k), shellSum (haarVol (KO k (Fin a))) ϖ ν z φ ≠ 0 := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  haveI : BorelSpace (GL (Fin a) k) := borel_GL
  set D := detCong (ϖ ^ e) (Fin a) with hDdef
  have hDo : IsOpen (D : Set (GL (Fin a) k)) := isOpen_detCong _ _
  have hDc : IsClosed (D : Set (GL (Fin a) k)) := D.isClosed_of_isOpen hDo
  have hDK : (D : Set (GL (Fin a) k)) ⊆ KO k (Fin a) := fun g hg => hg.1
  have hDk : IsCompact (D : Set (GL (Fin a) k)) := isCompact_KO.of_isClosed_subset hDc hDK
  have hoe : Topology.IsOpenEmbedding (fun g : GL (Fin a) k => g.val) := by
    refine ⟨isEmbedding_val_GL, ?_⟩
    have : Set.range (fun g : GL (Fin a) k => g.val) = {x : Matrix (Fin a) (Fin a) k | x.det ≠ 0} := by
      ext x
      simp only [Set.mem_range, Set.mem_setOf_eq]
      rw [← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det]
      rfl
    rw [this]
    exact isOpen_ne_fun (continuous_id.matrix_det) continuous_const
  set T : Set (Matrix (Fin a) (Fin a) k) := (fun g : GL (Fin a) k => g.val) '' D with hTdef
  have hTk : IsCompact T := hDk.image hoe.continuous
  have hTo : IsOpen T := hoe.isOpenMap _ hDo
  have hT : ∀ g : GL (Fin a) k, g.val ∈ T ↔ g ∈ D := fun g =>
    ⟨by rintro ⟨g', hg', h⟩; exact (Units.ext h : g' = g) ▸ hg', fun h => ⟨g, h, rfl⟩⟩
  have hSB : T.indicator (1 : Matrix (Fin a) (Fin a) k → ℂ) ∈ SB (Matrix (Fin a) (Fin a) k) :=
    ⟨(LocallyConstant.indicator (1 : LocallyConstant _ ℂ) ⟨hTk.isClosed, hTo⟩).isLocallyConstant,
      HasCompactSupport.intro hTk fun x hx => Set.indicator_of_notMem hx _⟩
  refine ⟨_, hSB, ?_⟩
  have h0 : ∀ m : {m : Fin a → ℤ // Antitone m}, m ≠ ⟨0, antitone_const⟩ →
      shell (haarVol (KO k (Fin a))) ϖ ν z (T.indicator 1) m.1 = 0 := by
    intro m hm
    unfold shell
    refine setIntegral_eq_zero_of_forall_eq_zero fun g hg => ?_
    have hgT : g.val ∉ T := fun h => hm ((exists_unique_shell hϖ g).unique hg
      (show g ∈ shellSet ϖ (0 : Fin a → ℤ) by rw [shellSet_zero]; exact hDK ((hT g).1 h)))
    simp [Set.indicator_of_notMem hgT]
  rw [shellSum, finsum_eq_single _ ⟨0, antitone_const⟩ h0]
  show shell (haarVol (KO k (Fin a))) ϖ ν z (T.indicator 1) (0 : Fin a → ℤ) ≠ 0
  unfold shell
  rw [shellSet_zero]
  have hval : ∫ g in (KO k (Fin a) : Set (GL (Fin a) k)),
      T.indicator 1 g.val * (ν (gdet g) : ℂ) * apow (gdet g) z ∂(haarVol (KO k (Fin a))) =
      ∫ g in (KO k (Fin a) : Set (GL (Fin a) k)), (D : Set (GL (Fin a) k)).indicator (fun _ => (1 : ℂ)) g
        ∂(haarVol (KO k (Fin a))) := by
    refine setIntegral_congr_fun isOpen_KO.measurableSet fun g hg => ?_
    by_cases hgD : g ∈ D
    · rw [Set.indicator_of_mem ((hT g).2 hgD), Set.indicator_of_mem hgD,
        apow_of_valuation_eq_one (valuation_gdet_of_mem_KO hg), hcond (gdet g) hgD.2]
      simp
    · rw [Set.indicator_of_notMem (fun h => hgD ((hT g).1 h)), Set.indicator_of_notMem hgD]
      simp
  rw [hval]
  have hmD : MeasurableSet (D : Set (GL (Fin a) k)) := hDo.measurableSet
  erw [integral_indicator hmD, Measure.restrict_restrict hmD, setIntegral_const, Set.inter_eq_left.2 hDK]
  have hpos : haarVol (KO k (Fin a)) (D : Set (GL (Fin a) k)) ≠ 0 := (hDo.measure_pos _ ⟨1, one_mem D⟩).ne'
  have hfin : haarVol (KO k (Fin a)) (D : Set (GL (Fin a) k)) ≠ ⊤ := hDk.measure_lt_top.ne
  simp only [Measure.real]
  rw [Complex.real_smul, mul_one, Complex.ofReal_ne_zero]
  exact (ENNReal.toReal_pos hpos hfin).ne'

theorem shellSum_isEqv_and_ne_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ϖ : kˣ) (n e : ℕ) (ν : kˣ →* ℂˣ) (z : ℂ),
    IsUnif ϖ → IsSmU ν → ¬ IsUnram ν → CondLE ϖ e ν →
    IsEqv ν z (shellSum (haarVol (KO k (Fin n))) ϖ ν z) ∧
    ∃ φ ∈ SB (Matrix (Fin n) (Fin n) k), shellSum (haarVol (KO k (Fin n))) ϖ ν z φ ≠ 0 := by
  intro k _ _ _ _ _ _ ϖ n e ν z hϖ hν hram hcond
  refine ⟨⟨fun φ hφ φ' hφ' => shellSum_add hϖ hram hcond hφ hφ' z, fun c φ _ => ?_,
    fun g₁ g₂ φ hφ => shellSum_eqv hϖ hν hram hcond g₁ g₂ hφ z⟩, exists_ne_zero hϖ hcond z⟩
  exact shellSum_smul _ ϖ ν z c φ

end Main

end GlobalTheory.ShellSumEqv
end
end

section -- merged from Development.AutomorphicArithmetic.DivisorFrames.SetIntegralMemAddSubgroupOfOpenSubgroupInvariant
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip
open scoped Pointwise

theorem UpperTheory.setIntegral_mem_addSubgroup_of_openSubgroup_invariant :
    ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulRightInvariant] (J : Subgroup G), IsOpen (J : Set G) → μ (J : Set G) = 1 → ∀ S : Set G, IsCompact S → (∀ j ∈ J, ∀ g ∈ S, j * g ∈ S) → ∀ f : G → ℂ, (∀ j ∈ J, ∀ g, f (j * g) = f g) → ∀ M : AddSubgroup ℂ, (∀ g ∈ S, f g ∈ M) → ∫ g in S, f g ∂μ ∈ M := by
  intro G _ _ _ _ _ μ _ J hJ hμ S hS hSJ f hf M hM
  classical
  let C : G → Set G := fun a => (fun x => x * a⁻¹) ⁻¹' (J : Set G)
  have hCo : ∀ a, IsOpen (C a) := fun a => hJ.preimage (continuous_id.mul continuous_const)
  have hCμ : ∀ a, μ (C a) = 1 := fun a => by
    simp only [C]; rw [measure_preimage_mul_right, hμ]
  have hCf : ∀ a, Set.EqOn f (fun _ => f a) (C a) := fun a x hx => by
    have := hf (x * a⁻¹) hx a
    rw [inv_mul_cancel_right] at this
    exact this
  have hCi : ∀ a, IntegrableOn f (C a) μ := fun a => by
    refine IntegrableOn.congr_fun ?_ (hCf a).symm (hCo a).measurableSet
    exact integrableOn_const (by rw [hCμ]; simp)
  have hCint : ∀ a, ∫ g in C a, f g ∂μ = f a := fun a => by
    rw [setIntegral_congr_fun (hCo a).measurableSet (hCf a), setIntegral_const]
    simp [Measure.real, hCμ]
  have key : ∀ t : Finset G, (∀ g ∈ t, f g ∈ M) →
      IntegrableOn f (⋃ g ∈ t, C g) μ ∧ ∫ g in ⋃ g ∈ t, C g, f g ∂μ ∈ M := by
    intro t
    induction t using Finset.induction_on with
    | empty => intro _; simp
    | insert a t ha ih =>
      intro h
      obtain ⟨h1, h2⟩ := ih fun g hg => h g (Finset.mem_insert_of_mem hg)
      rw [Finset.set_biUnion_insert]
      refine ⟨(hCi a).union h1, ?_⟩
      by_cases hd : Disjoint (C a) (⋃ g ∈ t, C g)
      · rw [setIntegral_union hd
          (isOpen_biUnion fun g _ => hCo g).measurableSet (hCi a) h1, hCint]
        exact M.add_mem (h a (Finset.mem_insert_self _ _)) h2
      · rw [Set.not_disjoint_iff] at hd
        obtain ⟨x, hx1, hx2⟩ := hd
        simp only [Set.mem_iUnion] at hx2
        obtain ⟨b, hb, hxb⟩ := hx2
        have hsub : C a ⊆ ⋃ g ∈ t, C g := by
          intro y hy
          simp only [Set.mem_iUnion]
          refine ⟨b, hb, ?_⟩
          have := J.mul_mem (J.mul_mem hy (J.inv_mem hx1)) hxb
          show y * b⁻¹ ∈ (J : Set G)
          simpa [mul_assoc] using this
        rw [Set.union_eq_self_of_subset_left hsub]
        exact h2
  obtain ⟨t, ht, hcov⟩ := hS.elim_nhds_subcover C (fun x _ => (hCo x).mem_nhds (by
    show x * x⁻¹ ∈ (J : Set G)
    simp))
  have hEq : S = ⋃ g ∈ t, C g := by
    refine Set.Subset.antisymm hcov ?_
    intro y hy
    simp only [Set.mem_iUnion] at hy
    obtain ⟨b, hb, hyb⟩ := hy
    have := hSJ _ hyb b (ht b hb)
    simpa using this
  rw [hEq]
  exact (key t fun g hg => hM g (ht g hg)).2
end

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip
open scoped Pointwise

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instMeasMat

section SlopeTestRemainingChoices
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem isCompact_scaledInt (ϖ : kˣ) (n : ℕ) (m : ℤ) :
    IsCompact (GlobalTheory.IndefiniteRowSideFullHecke.ScaledIntegerPeriodic.scaledInt ϖ n m) := by
  have h := (isCompact_intMatrix (k := k) (m := Fin n) (n := Fin n)).image
    (f := fun A : Matrix (Fin n) (Fin n) k => ((ϖ ^ m : kˣ) : k) • A) (by fun_prop)
  convert h using 1
  have h0 : valuation k ((ϖ ^ m : kˣ) : k) ≠ 0 := (Valuation.ne_zero_iff _).2 (Units.ne_zero _)
  ext Z
  constructor
  · intro hZ
    refine ⟨(((ϖ ^ m)⁻¹ : kˣ) : k) • Z, fun i j => ?_, ?_⟩
    · rw [Valuation.mem_integer_iff, Matrix.smul_apply, smul_eq_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀]
      exact inv_mul_le_one_of_le₀ (hZ i j) zero_le
    · simp only [smul_smul, Units.mul_inv, one_smul]
  · rintro ⟨A, hA, rfl⟩ i j
    simp only [Matrix.smul_apply, smul_eq_mul, map_mul]
    exact mul_le_of_le_one_right' ((Valuation.mem_integer_iff _ _).1 (hA i j))

private theorem mem_SB_of_periodic (ϖ : kˣ) {n : ℕ} (m : ℤ) (φ : Matrix (Fin n) (Fin n) k → ℂ)
    (hS : Function.support φ ⊆ GlobalTheory.IndefiniteRowSideFullHecke.ScaledIntegerPeriodic.scaledInt ϖ n m) (hP : GlobalTheory.IndefiniteRowSideFullHecke.ScaledIntegerPeriodic.IsPeriodic ϖ 0 φ) :
    φ ∈ SB (Matrix (Fin n) (Fin n) k) := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  refine ⟨(IsLocallyConstant.iff_eventually_eq _).mpr fun X => ?_,
    HasCompactSupport.intro (isCompact_scaledInt ϖ n m) fun x hx => ?_⟩
  · have hn : (fun Y => Y - X) ⁻¹' {A : Matrix (Fin n) (Fin n) k | ∀ i j, A i j ∈ 𝒪[k]} ∈ nhds X :=
      (isOpen_intMatrix.preimage (continuous_id.sub continuous_const)).mem_nhds (by
        intro i j; simp)
    filter_upwards [hn] with Y hY
    have := hP X (Y - X) (fun i j => by
      simpa using (Valuation.mem_integer_iff _ _).1 (hY i j))
    simpa using this
  · by_contra h
    exact hx (hS h)

private theorem isCompact_shellSet' (ϖ : kˣ) {n : ℕ} (m : Fin n → ℤ) :
    IsCompact (shellSet ϖ m : Set (GL (Fin n) k)) := by
  have h := ((isCompact_KO (k := k) (n := Fin n)).prod (isCompact_KO (k := k) (n := Fin n))).image
    (f := fun p : GL (Fin n) k × GL (Fin n) k => p.1 * (diagGL fun i => ϖ ^ m i) * p.2) (by fun_prop)
  convert h using 1
  ext g
  rw [mem_shellSet]
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact ⟨(x, y), ⟨hx, hy⟩, rfl⟩
  · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
    exact ⟨x, hx, y, hy, rfl⟩

end SlopeTestRemainingChoices

theorem UpperTheory.integral_mem_addSubgroup_of_ramified_twisted_invariant :
    ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {n : ℕ} (μ : Measure (GL (Fin n) k)) [μ.IsHaarMeasure] (J : Subgroup (GL (Fin n) k)), IsOpen (J : Set (GL (Fin n) k)) → J ≤ KO k (Fin n) → μ (J : Set (GL (Fin n) k)) = 1 → ∀ (ϖ : kˣ) (ν : kˣ →* ℂˣ) (e : ℕ), IsUnif ϖ → ¬ IsUnram ν → CondLE ϖ e ν → ∀ (z : ℂ) (φ : Matrix (Fin n) (Fin n) k → ℂ) (a : ℕ), Function.support φ ⊆ GlobalTheory.IndefiniteRowSideFullHecke.ScaledIntegerPeriodic.scaledInt ϖ n (-(a : ℤ)) → GlobalTheory.IndefiniteRowSideFullHecke.ScaledIntegerPeriodic.IsPeriodic ϖ 0 φ → (∀ j ∈ J, ∀ g : GL (Fin n) k, φ (j.val * g.val) * (ν (gdet j) : ℂ) = φ g.val) → ∀ M : AddSubgroup ℂ, (∀ m : Fin n → ℤ, (∀ i, -(a : ℤ) ≤ m i ∧ m i < 0) → ∀ g ∈ shellSet ϖ m, φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z ∈ M) → ∫ g, φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z ∂μ ∈ M := by
  intro k _ _ _ _ _ _ n μ _ J hJo hJK hJμ ϖ ν e hϖ hram hcond z φ a hS hP hinv M hM
  by_cases hint : Integrable (fun g : GL (Fin n) k => φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z) μ
  swap
  · rw [integral_undef hint]; exact M.zero_mem
  have hφ := mem_SB_of_periodic ϖ _ φ hS hP
  obtain ⟨-, h2, h3, h4⟩ := GlobalTheory.T.zetaIntegralShells_vanish_beyondPeriod_ramified k ϖ hϖ ν e hram hcond n μ φ hφ
  haveI : BorelSpace (GL (Fin n) k) := borel_GL
  haveI : μ.IsMulRightInvariant := isMulRightInvariant_of_haar μ
  have hsh : ∀ m : Fin n → ℤ, shell μ ϖ ν z φ m ∈ M := by
    intro m
    by_cases hm : ∀ i, -(a : ℤ) ≤ m i ∧ m i < 0
    · refine UpperTheory.setIntegral_mem_addSubgroup_of_openSubgroup_invariant μ J hJo hJμ (shellSet ϖ m) (isCompact_shellSet' ϖ m) ?_
        (fun g : GL (Fin n) k => φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z) ?_ M (hM m hm)
      · intro j hj g hg
        obtain ⟨x, hx, y, hy, rfl⟩ := mem_shellSet.1 hg
        exact mem_shellSet.2 ⟨j * x, mul_mem (hJK hj) hx, y, hy, by simp only [mul_assoc]⟩
      · intro j hj g
        simp only [gdet_mul, apow_mul, map_mul, Units.val_mul,
          apow_of_valuation_eq_one (valuation_gdet_of_mem_KO (hJK hj)), one_mul]
        rw [← hinv j hj g]
        ring
    · by_cases hm' : ∀ i, -(a : ℤ) ≤ m i
      · have : ∃ i, (0 : ℤ) ≤ m i := by
          by_contra h
          push_neg at h
          exact hm fun i => ⟨hm' i, h i⟩
        rw [h2 0 hP m this z]; exact M.zero_mem
      · rw [h3 a hS m hm' z]; exact M.zero_mem
  set S : {m : Fin n → ℤ // Antitone m} → Set (GL (Fin n) k) := fun m => shellSet ϖ m.1 with hSdef
  have hU : ⋃ m, S m = Set.univ :=
    Set.eq_univ_of_forall fun g => Set.mem_iUnion.2 (GlobalTheory.ShellSumEqv.exists_unique_shell hϖ g).exists
  have hd : Pairwise (Function.onFun Disjoint S) := fun m m' hne =>
    Set.disjoint_left.2 fun g h1 h2 => hne ((GlobalTheory.ShellSumEqv.exists_unique_shell hϖ g).unique h1 h2)
  have hm : ∀ m, MeasurableSet (S m) := fun m => (GlobalTheory.ShellSumEqv.isOpen_shellSet ϖ m.1).measurableSet
  have hfin : (Function.support fun m : {m : Fin n → ℤ // Antitone m} => shell μ ϖ ν z φ m.1).Finite :=
    h4.subset fun m hm => ⟨z, hm⟩
  have key : ∫ g, φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z ∂μ =
      ∑ m ∈ hfin.toFinset, shell μ ϖ ν z φ m.1 :=
    calc _ = ∫ g in ⋃ m, S m, φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z ∂μ := by
          rw [hU, Measure.restrict_univ]
      _ = ∑' m, ∫ g in S m, φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z ∂μ :=
          integral_iUnion hm hd hint.integrableOn
      _ = ∑ᶠ m : {m : Fin n → ℤ // Antitone m}, shell μ ϖ ν z φ m.1 := tsum_eq_finsum hfin
      _ = _ := finsum_eq_sum _ hfin
  rw [key]
  exact sum_mem fun m _ => hsh m.1
