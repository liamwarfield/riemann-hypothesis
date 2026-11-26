module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EventuallyExtUnramTwoNotMem
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSelfDualLatticeAtPlaceComapUnitarySupported
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleLiftPeriodRankZeroFubiniCompactQuotient
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RderMemAutFormsCuspForms

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RightDerivativeSmoothCuspidalSameLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RightDerivativeSmoothCuspidalSameLevel
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta MeasureTheory NumberField Matrix GlobalTheory.CuspGeo
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Mem.Th GlobalTheory.Cusp GlobalTheory.Mem.AutSpace GlobalTheory.Mem.RealTranslate
open scoped TensorProduct Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CuspStab

theorem rder_stab : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (U : Subgroup (GA D V)) (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ), X ∈ lieAt V τ → ∀ (A : ℕ) (φ : GA D V → ℂ), IsAutFun V φ → (∀ k ∈ U, k ∈ GfC V → ∀ g, φ (g * k) = φ g) → SmoothW θ V φ → (∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) → GlobalTheory.Grow.ModGrowthExp V A (l.foldr (fun p f => Rder θ V p.1 p.2 f) φ)) → IsCuspFun V φ → IsAutFun V (Rder θ V τ X φ) ∧ (∀ k ∈ U, k ∈ GfC V → ∀ g, Rder θ V τ X φ (g * k) = Rder θ V τ X φ g) ∧ SmoothW θ V (Rder θ V τ X φ) ∧ (∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) → GlobalTheory.Grow.ModGrowthExp V A (l.foldr (fun p f => Rder θ V p.1 p.2 f) (Rder θ V τ X φ))) ∧ IsCuspFun V (Rder θ V τ X φ) := by
  intro D θ hθ V U τ X hX A φ ha hU hs hg hc
  have hs' : φ ∈ SmFun θ V := hs
  have inv : ∀ k, k ∈ GfC V → (∀ g, φ (g * k) = φ g) → ∀ g, Rder θ V τ X φ (g * k) = Rder θ V τ X φ g := by
    intro k hk e g
    have := congrFun (GlobalTheory.Mem.FinTranslate.Rder_rTr (θ := θ) hk τ X φ) g
    rw [show rTr V k φ = φ from funext e] at this
    exact this.symm
  have hcont : Continuous (Rder θ V τ X φ) := by
    refine GlobalTheory.Size.continuous_Rder_of_growth hθ hs' ha.cont hX (A := A) ?_
    simpa using hg [(τ, X), (τ, X)] (by simp [hX])
  have ha' : IsAutFun V (Rder θ V τ X φ) :=
    { left := fun γ hγ => GlobalTheory.Mem.Lift.Rder_left (ha.left γ hγ) τ X
      level := by
        obtain ⟨U₀, hU₀, e⟩ := ha.level
        exact ⟨U₀, hU₀, fun k hk hf => inv k hf (e k hk hf)⟩
      cont := hcont }
  refine ⟨ha', fun k hk hf => inv k hf (hU k hk hf), Rder_mem hs' hX, fun l hl => ?_, ?_⟩
  · have := hg (l ++ [(τ, X)]) (by
      intro p hp
      rcases List.mem_append.1 hp with h | h
      · exact hl p h
      · rw [List.mem_singleton.1 h]; exact hX)
    simpa only [List.foldr_append, List.foldr_cons, List.foldr_nil] using this
  · refine (isCuspFun_iff ha'.left).2 fun W hW => funext fun x => ?_
    have h0 : constTermOn (GQ V) (NA (.single hW)) φ = 0 := (isCuspFun_iff ha.left).1 hc W hW
    have := GlobalTheory.CuspLie.hasDerivAt_constTermOn (cocompact_single hW) ha.left ha.cont ha'.left ha'.cont
      (GlobalTheory.Mem.Lift.continuous_oneP hθ hX)
      (GlobalTheory.Mem.Lift.hasDerivAt_oneP hθ hX (GlobalTheory.Mem.Lift.hasDerivAt_Rder hs' hX)) x
    rw [h0, GlobalTheory.Mem.Lift.oneP_zero hθ, mul_one] at this
    exact this.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ))

end GlobalTheory.CuspStab

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RightDerivativeSmoothCuspidalSameLevelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta MeasureTheory NumberField Matrix GlobalTheory.CuspGeo
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rightDerivative_smoothCuspidal_same_level : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (U : Subgroup (GA D V)) (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ), X ∈ lieAt V τ → ∀ (A : ℕ) (φ : GA D V → ℂ), IsAutFun V φ → (∀ k ∈ U, k ∈ GfC V → ∀ g, φ (g * k) = φ g) → SmoothW θ V φ → (∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) → GlobalTheory.Grow.ModGrowthExp V A (l.foldr (fun p f => Rder θ V p.1 p.2 f) φ)) → IsCuspFun V φ → IsAutFun V (Rder θ V τ X φ) ∧ (∀ k ∈ U, k ∈ GfC V → ∀ g, Rder θ V τ X φ (g * k) = Rder θ V τ X φ g) ∧ SmoothW θ V (Rder θ V τ X φ) ∧ (∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) → GlobalTheory.Grow.ModGrowthExp V A (l.foldr (fun p f => Rder θ V p.1 p.2 f) (Rder θ V τ X φ))) ∧ IsCuspFun V (Rder θ V τ X φ) := by
  first | exact @GlobalTheory.CuspStab.rder_stab | exact GlobalTheory.CuspStab.rder_stab | (intros; apply GlobalTheory.CuspStab.rder_stab <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IteratedGainRapidDecay
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IteratedGainRapidDecay
open Finset

namespace GlobalTheory.IterGain

noncomputable def words {ι : Type} [DecidableEq ι] (B : Finset ι) : ℕ → Finset (List ι)
  | 0 => {[]}
  | k + 1 => insert [] ((words B k ×ˢ B).image (fun p => p.1 ++ [p.2]))

theorem nil_mem {ι : Type} [DecidableEq ι] (B : Finset ι) (k : ℕ) : [] ∈ words B k := by
  cases k <;> simp [words]

theorem append_mem {ι : Type} [DecidableEq ι] {B : Finset ι} {k : ℕ} {l : List ι} {i : ι}
    (hl : l ∈ words B k) (hi : i ∈ B) : l ++ [i] ∈ words B (k + 1) := by
  simp only [words, mem_insert, mem_image, mem_product, Prod.exists]
  exact Or.inr ⟨l, i, ⟨hl, hi⟩, rfl⟩

theorem mem_letters {ι : Type} [DecidableEq ι] (B : Finset ι) :
    ∀ (k : ℕ), ∀ l ∈ words B k, ∀ i ∈ l, i ∈ B := by
  intro k
  induction k with
  | zero => intro l hl i hi; simp [words] at hl; subst hl; simp at hi
  | succ k ih =>
    intro l hl i hi
    simp only [words, mem_insert, mem_image, mem_product, Prod.exists] at hl
    rcases hl with rfl | ⟨l', j, ⟨hl', hj⟩, rfl⟩
    · simp at hi
    · rcases List.mem_append.1 hi with h | h
      · exact ih l' hl' i h
      · simp at h; subst h; exact hj

theorem root_le {x y : ℝ} {m : ℕ} (hm : m ≠ 0) (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x ^ m ≤ y ^ m) :
    x ≤ y := (pow_le_pow_iff_left₀ hx hy hm).1 h

theorem step {G ι : Type} [DecidableEq ι] (B : Finset ι) (q : G → ℝ) (𝓒 : Set (G → ℂ))
    (Dr : ι → (G → ℂ) → G → ℂ) (m : ℕ) (C δ₀ K : ℝ) (Q : G → ℝ) (A : ℕ)
    (hm : m ≠ 0) (hδ₀ : 0 < δ₀) (hC : 1 ≤ C) (hK : 1 ≤ K) (hKm : K ^ m = C)
    (hq : ∀ g, 1 ≤ q g) (hQ1 : ∀ g, 1 ≤ Q g) (hQm : ∀ g, Q g ^ m = q g)
    (hcl : ∀ ψ ∈ 𝓒, ∀ i ∈ B, Dr i ψ ∈ 𝓒)
    (hgain : ∀ g, ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ q g * δ ^ m ≤ C ∧ (δ₀ ≤ δ ∨ ∃ Ω : Set G,
      (∀ w ∈ Ω, q w ≤ C * q g ∧ q g ≤ C * q w) ∧ ∀ ψ ∈ 𝓒, ∀ c : ι → ℝ,
        (∀ i ∈ B, 0 ≤ c i ∧ ∀ w ∈ Ω, ‖Dr i ψ w‖ ≤ c i) → ‖ψ g‖ ≤ C * δ * ∑ i ∈ B, c i))
    (k : ℕ) : ∃ Ck : ℝ, 0 ≤ Ck ∧ ∀ ψ ∈ 𝓒, ∀ c : List ι → ℝ, (∀ l ∈ words B k, 0 ≤ c l) →
      (∀ l ∈ words B k, ∀ g, ‖l.foldr Dr ψ g‖ ≤ c l * q g ^ A) →
      ∀ g, ‖ψ g‖ * Q g ^ k ≤ Ck * q g ^ A * ∑ l ∈ words B k, c l := by
  induction k with
  | zero =>
    refine ⟨1, zero_le_one, ?_⟩
    intro ψ _ c _ hc g
    have h := hc [] (nil_mem B 0) g
    simp only [List.foldr_nil] at h
    simp [words]
    linarith
  | succ k ih =>
    obtain ⟨Ck, hCk0, hCk⟩ := ih
    have hK0 : 0 ≤ K := by linarith
    have hC0 : 0 ≤ C := by linarith
    have hQ0 : ∀ g, 0 ≤ Q g := fun g => by linarith [hQ1 g]
    have hq0 : ∀ g, 0 ≤ q g := fun g => by linarith [hq g]
    set M := K / δ₀ with hM
    have hM0 : 0 ≤ M := div_nonneg hK0 hδ₀.le
    set X1 := M ^ (k + 1)
    set X2 := C * K ^ (k + 1) * Ck * C ^ A * ((B.card : ℝ) * ((words B k).card : ℝ))
    have hX1 : 0 ≤ X1 := pow_nonneg hM0 _
    have hX2 : 0 ≤ X2 := by positivity
    refine ⟨X1 + X2, add_nonneg hX1 hX2, ?_⟩
    intro ψ hψ c hc0 hc g
    set T := ∑ l ∈ words B (k + 1), c l with hT
    have hT0 : 0 ≤ T := sum_nonneg hc0
    have hqA : 0 ≤ q g ^ A := pow_nonneg (hq0 g) _
    obtain ⟨δ, hδ, _, hδq, hcase⟩ := hgain g
    have hδQ : δ * Q g ≤ K := by
      apply root_le hm (mul_nonneg hδ.le (hQ0 g)) hK0
      rw [mul_pow, hQm, hKm]; linarith [mul_comm (q g) (δ ^ m)]
    have hQgw : ∀ w, q g ≤ C * q w → Q g ≤ K * Q w := by
      intro w hw
      apply root_le hm (hQ0 g) (mul_nonneg hK0 (hQ0 w))
      rw [mul_pow, hQm, hKm, hQm]; exact hw
    suffices h : ‖ψ g‖ * Q g ^ (k + 1) ≤ X1 * q g ^ A * T ∨
        ‖ψ g‖ * Q g ^ (k + 1) ≤ X2 * q g ^ A * T by
      have e1 : 0 ≤ X1 * q g ^ A * T := by positivity
      have e2 : 0 ≤ X2 * q g ^ A * T := mul_nonneg (mul_nonneg hX2 hqA) hT0
      rcases h with h | h <;> nlinarith
    rcases hcase with hδ0 | ⟨Ω, hΩ, hbound⟩
    · left
      have hQM : Q g ≤ M := by
        rw [hM, le_div_iff₀ hδ₀]; nlinarith [hQ0 g]
      have h0 : ‖ψ g‖ ≤ c [] * q g ^ A := by simpa using hc [] (nil_mem B _) g
      have hcT : c [] ≤ T := single_le_sum (f := c) (fun l hl => hc0 l hl) (nil_mem B _)
      have hQk : Q g ^ (k + 1) ≤ X1 := pow_le_pow_left₀ (hQ0 g) hQM _
      calc ‖ψ g‖ * Q g ^ (k + 1) ≤ (c [] * q g ^ A) * X1 :=
            mul_le_mul h0 hQk (pow_nonneg (hQ0 g) _) (by nlinarith [norm_nonneg (ψ g)])
        _ ≤ (T * q g ^ A) * X1 := by gcongr
        _ = X1 * q g ^ A * T := by ring
    · right
      set S : ι → ℝ := fun i => ∑ l ∈ words B k, c (l ++ [i]) with hS
      have hS0 : ∀ i ∈ B, 0 ≤ S i := fun i hi =>
        sum_nonneg (fun l hl => hc0 _ (append_mem hl hi))
      have hQgk : 0 < Q g ^ k := pow_pos (by linarith [hQ1 g]) _
      set P := K ^ k * Ck * C ^ A * q g ^ A with hP
      have hP0 : 0 ≤ P := by positivity
      set ci : ι → ℝ := fun i => P * S i / Q g ^ k with hci
      have hDr : ∀ i ∈ B, 0 ≤ ci i ∧ ∀ w ∈ Ω, ‖Dr i ψ w‖ ≤ ci i := by
        intro i hi
        refine ⟨div_nonneg (mul_nonneg hP0 (hS0 i hi)) hQgk.le, ?_⟩
        intro w hw
        have hb := hCk (Dr i ψ) (hcl ψ hψ i hi) (fun l => c (l ++ [i]))
          (fun l hl => hc0 _ (append_mem hl hi))
          (fun l hl g' => by
            have := hc (l ++ [i]) (append_mem hl hi) g'
            simpa [List.foldr_append] using this) w
        have h1 : Q g ^ k ≤ K ^ k * Q w ^ k := by
          rw [← mul_pow]; exact pow_le_pow_left₀ (hQ0 g) (hQgw w (hΩ w hw).2) k
        have h2 : q w ^ A ≤ C ^ A * q g ^ A := by
          rw [← mul_pow]; exact pow_le_pow_left₀ (hq0 w) (hΩ w hw).1 A
        rw [hci, le_div_iff₀ hQgk]
        calc ‖Dr i ψ w‖ * Q g ^ k ≤ ‖Dr i ψ w‖ * (K ^ k * Q w ^ k) :=
              mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
          _ = K ^ k * (‖Dr i ψ w‖ * Q w ^ k) := by ring
          _ ≤ K ^ k * (Ck * q w ^ A * S i) :=
              mul_le_mul_of_nonneg_left hb (pow_nonneg hK0 _)
          _ ≤ K ^ k * (Ck * (C ^ A * q g ^ A) * S i) := by
              apply mul_le_mul_of_nonneg_left _ (pow_nonneg hK0 _)
              apply mul_le_mul_of_nonneg_right _ (hS0 i hi)
              exact mul_le_mul_of_nonneg_left h2 hCk0
          _ = P * S i := by rw [hP]; ring
      have hmain := hbound ψ hψ ci hDr
      have hsum : ∑ i ∈ B, ci i = P * (∑ i ∈ B, S i) / Q g ^ k := by
        rw [hci]; simp only; rw [← Finset.sum_div, ← Finset.mul_sum]
      have hSsum : ∑ i ∈ B, S i ≤ (B.card : ℝ) * ((words B k).card : ℝ) * T := by
        calc ∑ i ∈ B, S i ≤ ∑ i ∈ B, ∑ l ∈ words B k, T :=
              sum_le_sum (fun i hi => sum_le_sum (fun l hl =>
                single_le_sum (f := c) (fun l hl => hc0 l hl) (append_mem hl hi)))
          _ = (B.card : ℝ) * ((words B k).card : ℝ) * T := by
              simp [sum_const, nsmul_eq_mul]; ring
      have hSum0 : 0 ≤ ∑ i ∈ B, S i := sum_nonneg hS0
      calc ‖ψ g‖ * Q g ^ (k + 1) ≤ (C * δ * ∑ i ∈ B, ci i) * Q g ^ (k + 1) :=
            mul_le_mul_of_nonneg_right hmain (pow_nonneg (hQ0 g) _)
        _ = C * (δ * Q g) * (P * ∑ i ∈ B, S i) := by
            rw [hsum]; field_simp; ring
        _ ≤ C * K * (P * ((B.card : ℝ) * ((words B k).card : ℝ) * T)) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_left hδQ hC0)
              (mul_le_mul_of_nonneg_left hSsum hP0) (mul_nonneg hP0 hSum0) (mul_nonneg hC0 hK0)
        _ = X2 * q g ^ A * T := by rw [hP]; ring

end GlobalTheory.IterGain

namespace GlobalTheory


open GlobalTheory.IterGain in
theorem iterated_gain_rapid_decay : ∀ (G ι : Type) (B : Finset ι) (q : G → ℝ) (𝓒 : Set (G → ℂ))
    (Dr : ι → (G → ℂ) → G → ℂ) (b : ℕ) (C δ₀ : ℝ), 0 < δ₀ → (∀ g, 1 ≤ q g) →
    (∀ ψ ∈ 𝓒, ∀ i ∈ B, Dr i ψ ∈ 𝓒) →
    (∀ g, ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ q g * δ ^ b ≤ C ∧ (δ₀ ≤ δ ∨ ∃ Ω : Set G,
      (∀ w ∈ Ω, q w ≤ C * q g ∧ q g ≤ C * q w) ∧ ∀ ψ ∈ 𝓒, ∀ c : ι → ℝ,
        (∀ i ∈ B, 0 ≤ c i ∧ ∀ w ∈ Ω, ‖Dr i ψ w‖ ≤ c i) → ‖ψ g‖ ≤ C * δ * ∑ i ∈ B, c i)) →
    ∀ A N : ℕ, ∃ (L : Finset (List ι)) (C' : ℝ), (∀ l ∈ L, ∀ i ∈ l, i ∈ B) ∧
      ∀ ψ ∈ 𝓒, ∀ c : List ι → ℝ, (∀ l ∈ L, ∀ g, ‖l.foldr Dr ψ g‖ ≤ c l * q g ^ A) →
        ∀ g, ‖ψ g‖ * q g ^ N ≤ C' * ∑ l ∈ L, c l := by
  intro G ι B q 𝓒 Dr b C δ₀ hδ₀ hq hcl hgain A N
  classical
  set m := b + 1 with hmdef
  have hm : m ≠ 0 := Nat.succ_ne_zero b
  set C1 := max C 1 with hC1
  have hC1 : 1 ≤ C1 := le_max_right _ _
  have hCC1 : C ≤ C1 := le_max_left _ _
  have hq0 : ∀ g, 0 ≤ q g := fun g => by linarith [hq g]
  have hgain' : ∀ g, ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ q g * δ ^ m ≤ C1 ∧ (δ₀ ≤ δ ∨ ∃ Ω : Set G,
      (∀ w ∈ Ω, q w ≤ C1 * q g ∧ q g ≤ C1 * q w) ∧ ∀ ψ ∈ 𝓒, ∀ c : ι → ℝ,
        (∀ i ∈ B, 0 ≤ c i ∧ ∀ w ∈ Ω, ‖Dr i ψ w‖ ≤ c i) → ‖ψ g‖ ≤ C1 * δ * ∑ i ∈ B, c i) := by
    intro g
    obtain ⟨δ, hδ, hδ1, hqδ, hcase⟩ := hgain g
    refine ⟨δ, hδ, hδ1, ?_, ?_⟩
    · have h1 : q g * δ ^ m ≤ q g * δ ^ b := by
        rw [hmdef, pow_succ, ← mul_assoc]
        exact mul_le_of_le_one_right (mul_nonneg (hq0 g) (pow_nonneg hδ.le _)) hδ1
      linarith
    · rcases hcase with h | ⟨Ω, hΩ, hbd⟩
      · exact Or.inl h
      · refine Or.inr ⟨Ω, fun w hw => ⟨?_, ?_⟩, ?_⟩
        · exact (hΩ w hw).1.trans (mul_le_mul_of_nonneg_right hCC1 (hq0 g))
        · exact (hΩ w hw).2.trans (mul_le_mul_of_nonneg_right hCC1 (hq0 w))
        · intro ψ hψ c hc
          have hs : 0 ≤ ∑ i ∈ B, c i := sum_nonneg (fun i hi => (hc i hi).1)
          exact (hbd ψ hψ c hc).trans
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCC1 hδ.le) hs)
  set K : ℝ := C1 ^ ((m : ℝ)⁻¹) with hK
  set Q : G → ℝ := fun g => q g ^ ((m : ℝ)⁻¹) with hQ
  have hKm : K ^ m = C1 := Real.rpow_inv_natCast_pow (by linarith) hm
  have hK1 : 1 ≤ K := Real.one_le_rpow hC1 (by positivity)
  have hQm : ∀ g, Q g ^ m = q g := fun g => Real.rpow_inv_natCast_pow (hq0 g) hm
  have hQ1 : ∀ g, 1 ≤ Q g := fun g => Real.one_le_rpow (hq g) (by positivity)
  obtain ⟨Ck, _, hCk⟩ := step B q 𝓒 Dr m C1 δ₀ K Q A hm hδ₀ hC1 hK1 hKm hq hQ1 hQm hcl hgain'
    (m * (A + N))
  refine ⟨words B (m * (A + N)), Ck, mem_letters B _, ?_⟩
  intro ψ hψ c hc g
  have hqA : 0 < q g ^ A := pow_pos (by linarith [hq g]) _
  have hc0 : ∀ l ∈ words B (m * (A + N)), 0 ≤ c l := by
    intro l hl
    by_contra h
    push_neg at h
    have h1 := hc l hl g
    have h2 : c l * q g ^ A < 0 := mul_neg_of_neg_of_pos h hqA
    linarith [norm_nonneg (List.foldr Dr ψ l g)]
  have h := hCk ψ hψ c hc0 hc g
  rw [pow_mul, hQm, pow_add] at h
  have h' : q g ^ A * (‖ψ g‖ * q g ^ N) ≤ q g ^ A * (Ck * ∑ l ∈ words B (m * (A + N)), c l) := by
    linarith
  exact le_of_mul_le_mul_left h' hqA

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IteratedGainRapidDecayStatement
open Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rapid_decay_of_iterated_gain : ∀ (G ι : Type) (B : Finset ι) (q : G → ℝ) (𝓒 : Set (G → ℂ)) (Dr : ι → (G → ℂ) → G → ℂ) (b : ℕ) (C δ₀ : ℝ), 0 < δ₀ → (∀ g, 1 ≤ q g) → (∀ ψ ∈ 𝓒, ∀ i ∈ B, Dr i ψ ∈ 𝓒) → (∀ g, ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ q g * δ ^ b ≤ C ∧ (δ₀ ≤ δ ∨ ∃ Ω : Set G, (∀ w ∈ Ω, q w ≤ C * q g ∧ q g ≤ C * q w) ∧ ∀ ψ ∈ 𝓒, ∀ c : ι → ℝ, (∀ i ∈ B, 0 ≤ c i ∧ ∀ w ∈ Ω, ‖Dr i ψ w‖ ≤ c i) → ‖ψ g‖ ≤ C * δ * ∑ i ∈ B, c i)) → ∀ A N : ℕ, ∃ (L : Finset (List ι)) (C' : ℝ), (∀ l ∈ L, ∀ i ∈ l, i ∈ B) ∧ ∀ ψ ∈ 𝓒, ∀ c : List ι → ℝ, (∀ l ∈ L, ∀ g, ‖l.foldr Dr ψ g‖ ≤ c l * q g ^ A) → ∀ g, ‖ψ g‖ * q g ^ N ≤ C' * ∑ l ∈ L, c l := by
  first | exact @GlobalTheory.iterated_gain_rapid_decay | exact GlobalTheory.iterated_gain_rapid_decay | (intros; apply GlobalTheory.iterated_gain_rapid_decay <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspidalModerateGrowthRapidDecay
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta MeasureTheory NumberField Matrix GlobalTheory.CuspGeo
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CuspGeo

theorem closeR_mono {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}
    {u : GA D V} {a a' : ℝ} (h : CloseR θ V u a) (hle : a ≤ a') : CloseR θ V u a' :=
  ⟨h.1, fun τ i j => (h.2 τ i j).trans hle⟩

theorem cuspDecayBound : GlobalTheory.Published.CuspDecayBound := by
  intro D θ hθ V U hU A N
  let Dr : D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ → (GA D V → ℂ) → GA D V → ℂ :=
    fun p f => Rder θ V p.1 p.2 f
  let 𝓒 : Set (GA D V → ℂ) := {φ | IsAutFun V φ ∧ (∀ k ∈ U, k ∈ GfC V → ∀ g, φ (g * k) = φ g) ∧ SmoothW θ V φ ∧
    (∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) →
      GlobalTheory.Grow.ModGrowthExp V A (l.foldr Dr φ)) ∧ IsCuspFun V φ}
  obtain ⟨B, Ω₀, Cm, δ₁, hB, hΩ₀, hδ₁, hCm, hmv⟩ := GlobalTheory.T.meanValue_ineq_rightTranslate_realPoint_near_one D θ hθ V
  obtain ⟨b, Cn, δn, hδn, hnear⟩ := GlobalTheory.T.adelicUnitary_every_point_has_cusp_scale D θ hθ V U hU
  obtain ⟨H, hH⟩ := GlobalTheory.Grow.exists_height_le_of_isCompact V hΩ₀
  have hstab : ∀ ψ ∈ 𝓒, ∀ i ∈ B, Dr i ψ ∈ 𝓒 := by
    rintro ψ ⟨ha, hlev, hs, hg, hc⟩ i hi
    exact GlobalTheory.T.rightDerivative_smoothCuspidal_same_level D θ hθ V U i.1 i.2 (hB i hi) A ψ ha hlev hs hg hc
  have hwords : ∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ i ∈ l, i ∈ B) →
      ∀ ψ ∈ 𝓒, l.foldr Dr ψ ∈ 𝓒 := by
    intro l
    induction l with
    | nil => intro _ ψ hψ; exact hψ
    | cons a l ih =>
      intro hl ψ hψ
      exact hstab _ (ih (fun i hi => hl i (List.mem_cons_of_mem _ hi)) ψ hψ) a (hl a List.mem_cons_self)
  set Cn' := max Cn 0 with hCn'
  have hCn'0 : 0 ≤ Cn' := le_max_right _ _
  set δ₀ := min δn (δ₁ / (Cn' + 1)) with hδ₀
  have hδ₀pos : 0 < δ₀ := lt_min hδn (div_pos hδ₁ (by linarith))
  set K := max (max Cn (Cm * Cn')) (max H 1) with hK
  have hK1 : Cn ≤ K := (le_max_left _ _).trans (le_max_left _ _)
  have hK2 : Cm * Cn' ≤ K := (le_max_right _ _).trans (le_max_left _ _)
  have hK3 : H ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hstep : ∀ g, ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ GlobalTheory.Grow.quotHeight V g * δ ^ b ≤ K ∧ (δ₀ ≤ δ ∨
      ∃ Ω : Set (GA D V), (∀ w ∈ Ω, GlobalTheory.Grow.quotHeight V w ≤ K * GlobalTheory.Grow.quotHeight V g ∧
        GlobalTheory.Grow.quotHeight V g ≤ K * GlobalTheory.Grow.quotHeight V w) ∧
      ∀ ψ ∈ 𝓒, ∀ c : D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ → ℝ,
        (∀ i ∈ B, 0 ≤ c i ∧ ∀ w ∈ Ω, ‖Dr i ψ w‖ ≤ c i) → ‖ψ g‖ ≤ K * δ * ∑ i ∈ B, c i) := by
    intro g
    obtain ⟨δ, hδ0, hδ1, hq, hcase⟩ := hnear g
    refine ⟨δ, hδ0, hδ1, hq.trans hK1, ?_⟩
    by_cases hδ : δ₀ ≤ δ
    · exact Or.inl hδ
    right
    push_neg at hδ
    have hδn' : ¬ δn ≤ δ := fun h => absurd (hδ.trans_le (min_le_left _ _)) (not_lt.2 h)
    obtain ⟨r, C₀, hC₀, hN⟩ := hcase.resolve_left hδn'
    have hsmall : Cn' * δ ≤ δ₁ := by
      have h1 : δ < δ₁ / (Cn' + 1) := hδ.trans_le (min_le_right _ _)
      rw [lt_div_iff₀ (by linarith)] at h1
      nlinarith
    refine ⟨(g * ·) '' Ω₀, ?_, ?_⟩
    · rintro _ ⟨w, hw, rfl⟩
      have hq0 := GlobalTheory.Grow.one_le_quotHeight V g
      have hq1 := GlobalTheory.Grow.one_le_quotHeight V (g * w)
      have hw1 := hH w hw
      constructor
      · calc GlobalTheory.Grow.quotHeight V (g * w) ≤ GlobalTheory.Grow.quotHeight V g * GlobalTheory.Grow.height V w :=
              GlobalTheory.Grow.quotHeight_mul_le V g w
          _ ≤ GlobalTheory.Grow.quotHeight V g * K := mul_le_mul_of_nonneg_left (hw1.trans hK3) (by linarith)
          _ = K * GlobalTheory.Grow.quotHeight V g := mul_comm _ _
      · calc GlobalTheory.Grow.quotHeight V g = GlobalTheory.Grow.quotHeight V (g * w * w⁻¹) := by rw [mul_inv_cancel_right]
          _ ≤ GlobalTheory.Grow.quotHeight V (g * w) * GlobalTheory.Grow.height V w⁻¹ := GlobalTheory.Grow.quotHeight_mul_le V _ _
          _ ≤ GlobalTheory.Grow.quotHeight V (g * w) * K := by
              rw [GlobalTheory.Grow.height_inv]; exact mul_le_mul_of_nonneg_left (hw1.trans hK3) (by linarith)
          _ = K * GlobalTheory.Grow.quotHeight V (g * w) := mul_comm _ _
    · rintro ψ ⟨ha, hlev, hs, hg, hc⟩ c hc'
      have hsum : 0 ≤ ∑ i ∈ B, c i := Finset.sum_nonneg fun i hi => (hc' i hi).1
      have hmain : ‖ψ g‖ ≤ Cm * (Cn' * δ) * ∑ p ∈ B, c p := by
        refine GlobalTheory.T.norm_le_of_cuspidal_variation_unipotentRadical D V ψ ha hc r C₀ hC₀ g _ fun m hm => ?_
        obtain ⟨γ, hγ, u, k, hu, hkU, hkf, hmg⟩ := hN m hm
        have hval : ψ (m * g) = ψ (g * u) := by
          rw [hmg, show γ * g * u * k = γ * (g * u) * k by group, hlev k hkU hkf, ha.left γ hγ]
        rw [hval]
        refine hmv ψ hs g u (Cn' * δ) (mul_nonneg hCn'0 hδ0.le) hsmall
          (closeR_mono hu (mul_le_mul_of_nonneg_right (le_max_left _ _) hδ0.le)) c fun p hp w hw => ?_
        exact (hc' p hp).2 _ ⟨w, hw, rfl⟩
      refine hmain.trans ?_
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK2 hδ0.le) hsum
  obtain ⟨L, C', hLB, hL⟩ := GlobalTheory.T.exists_rapid_decay_of_iterated_gain (GA D V) (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ) B
    (GlobalTheory.Grow.quotHeight V) 𝓒 Dr b K δ₀ hδ₀pos (GlobalTheory.Grow.one_le_quotHeight V) hstab hstep A N
  refine ⟨L, C' * 2 ^ A, fun l hl p hp => hB p (hLB l hl p hp), ?_⟩
  intro φ ha hlev hs hg hc c hcl g
  have hφ : φ ∈ 𝓒 := ⟨ha, hlev, hs, hg, hc⟩
  have h := hL φ hφ (fun l => c l * 2 ^ A) (fun l hl g' =>
    GlobalTheory.Grow.norm_le_quotHeight_pow (hwords l (hLB l hl) φ hφ).1.left (hcl l hl) g') g
  refine h.trans (le_of_eq ?_)
  rw [← Finset.sum_mul]
  ring

end GlobalTheory.CuspGeo
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspidalModerateGrowthRapidDecayStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta MeasureTheory NumberField Matrix GlobalTheory.CuspGeo
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_moderateGrowth_rapidDecay : GlobalTheory.Published.CuspDecayBound := by
  first | exact @GlobalTheory.CuspGeo.cuspDecayBound | exact GlobalTheory.CuspGeo.cuspDecayBound | (intros; apply GlobalTheory.CuspGeo.cuspDecayBound <;> assumption)
end
