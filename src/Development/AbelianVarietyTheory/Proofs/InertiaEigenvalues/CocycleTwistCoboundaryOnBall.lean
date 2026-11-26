module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicTateMaximalIdealKillsFirstCohomology
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorsionCoinvariantsTwistedCyclotomicGenerator

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocycleVanishingOnFixingSubgroupDeterminedByGene
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocycleVanishingOnFixingSubgroupDeterminedByGene
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc Filter Topology

namespace GlobalTheory.Cyc.Procyclic

section Abstract

variable {Γ X : Type} [Group Γ] [NormedAddCommGroup X]

def psum (A : Γ → X →+ X) (g : Γ) (w : X) (n : ℕ) : X := (fun x => w + A g x)^[n] 0

variable {G : Subgroup Γ} {A : Γ → X →+ X} {g : Γ} {w : X}

omit [Group Γ] in
theorem psum_zero : psum A g w 0 = 0 := rfl

omit [Group Γ] in
theorem psum_succ (n : ℕ) : psum A g w (n + 1) = w + A g (psum A g w n) :=
  Function.iterate_succ_apply' _ _ _

theorem psum_add (hg : g ∈ G) (hone : ∀ y, A 1 y = y)
    (hmul : ∀ σ ∈ G, ∀ τ ∈ G, ∀ y, A (σ * τ) y = A σ (A τ y)) (a b : ℕ) :
    psum A g w (a + b) = psum A g w a + A (g ^ a) (psum A g w b) := by
  induction a with
  | zero => simp [psum_zero, hone]
  | succ a ih =>
    rw [Nat.add_right_comm, psum_succ, psum_succ, ih, map_add (f := _), pow_succ', hmul _ hg _ (pow_mem hg a),
      add_assoc]

omit [Group Γ] in
theorem psum_mem {M : AddSubgroup X} (hw : w ∈ M) (hM : ∀ y ∈ M, A g y ∈ M) (n : ℕ) :
    psum A g w n ∈ M := by
  induction n with
  | zero => exact M.zero_mem
  | succ n ih => rw [psum_succ]; exact M.add_mem hw (hM _ ih)

variable [IsUltrametricDist X]

omit [Group Γ] in
theorem norm_psum_le (hn : ∀ y, ‖A g y‖ ≤ ‖y‖) (n : ℕ) : ‖psum A g w n‖ ≤ ‖w‖ := by
  induction n with
  | zero => simp [psum_zero]
  | succ n ih =>
    rw [psum_succ]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le le_rfl ((hn _).trans ih))

theorem norm_move_psum_le (hg : g ∈ G)
    (hmul : ∀ σ ∈ G, ∀ τ ∈ G, ∀ y, A (σ * τ) y = A σ (A τ y)) (hn : ∀ y, ‖A g y‖ ≤ ‖y‖)
    (q n : ℕ) : ‖A (g ^ q) (psum A g w n) - psum A g w n‖ ≤ ‖A (g ^ q) w - w‖ := by
  induction n with
  | zero => simp [psum_zero]
  | succ n ih =>
    have h : A (g ^ q) (psum A g w (n + 1)) - psum A g w (n + 1)
        = (A (g ^ q) w - w) + A g (A (g ^ q) (psum A g w n) - psum A g w n) := by
      rw [psum_succ, map_add (f := _), map_sub, ← hmul _ (pow_mem hg q) _ hg, ← hmul _ hg _ (pow_mem hg q),
        ← pow_succ, ← pow_succ']
      abel
    rw [h]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le le_rfl ((hn _).trans ih))

theorem norm_psum_mul_sub_le (hg : g ∈ G) (hone : ∀ y, A 1 y = y)
    (hmul : ∀ σ ∈ G, ∀ τ ∈ G, ∀ y, A (σ * τ) y = A σ (A τ y)) (hn : ∀ y, ‖A g y‖ ≤ ‖y‖)
    (q t : ℕ) : ‖psum A g w (q * t) - t • psum A g w q‖ ≤ ‖A (g ^ q) w - w‖ := by
  induction t with
  | zero => simp [psum_zero]
  | succ t ih =>
    have h : psum A g w (q * (t + 1)) - (t + 1) • psum A g w q
        = (A (g ^ q) (psum A g w (q * t)) - psum A g w (q * t))
          + (psum A g w (q * t) - t • psum A g w q) := by
      rw [mul_add, mul_one, add_comm (q * t) q, psum_add hg hone hmul, succ_nsmul]
      abel
    rw [h]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le (norm_move_psum_le hg hmul hn _ _) ih)

theorem exists_norm_psum_sub_le (p : ℕ) (hg : g ∈ G) (hone : ∀ y, A 1 y = y)
    (hmul : ∀ σ ∈ G, ∀ τ ∈ G, ∀ y, A (σ * τ) y = A σ (A τ y))
    (hn : ∀ σ ∈ G, ∀ y, ‖A σ y‖ ≤ ‖y‖)
    (hD : ∀ ε > 0, ∃ k : ℕ, ‖A (g ^ p ^ k) w - w‖ ≤ ε)
    (hp : ∀ ε > 0, ∃ s : ℕ, ∀ y : X, ‖y‖ ≤ ‖w‖ → ‖p ^ s • y‖ ≤ ε) (ε : ℝ) (hε : 0 < ε) :
    ∃ k : ℕ, ∀ a d : ℕ, p ^ k ∣ d → ‖psum A g w (a + d) - psum A g w a‖ ≤ ε := by
  obtain ⟨k, hk⟩ := hD ε hε
  obtain ⟨s, hs⟩ := hp ε hε
  refine ⟨k + s, ?_⟩
  rintro a _ ⟨t, rfl⟩
  rw [psum_add hg hone hmul, add_sub_cancel_left]
  refine (hn _ (pow_mem hg a) _).trans ?_
  have h : psum A g w (p ^ (k + s) * t)
      = (psum A g w (p ^ k * (p ^ s * t)) - (p ^ s * t) • psum A g w (p ^ k))
        + p ^ s • (t • psum A g w (p ^ k)) := by
    rw [pow_add, mul_assoc, smul_smul]; abel
  rw [h]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le ((norm_psum_mul_sub_le hg hone hmul (hn g hg) _ _).trans hk) (hs _ ?_))
  exact (IsUltrametricDist.norm_nsmul_le _ _).trans (norm_psum_le (hn g hg) _)

variable [TopologicalSpace Γ]

omit [IsUltrametricDist X] in
theorem eqOn_of_dense {H : Subgroup Γ} (hg : g ∈ G) (hHG : H ≤ G)
    (hd : (G : Set Γ) ⊆ closure {x | ∃ h ∈ H, ∃ a : ℕ, x = h * g ^ a}) {f₁ f₂ : Γ → X}
    (h₁ : ContinuousOn f₁ G) (h₂ : ContinuousOn f₂ G)
    (h : ∀ h ∈ H, ∀ a : ℕ, f₁ (h * g ^ a) = f₂ (h * g ^ a)) : ∀ σ ∈ G, f₁ σ = f₂ σ := by
  refine Set.EqOn.of_subset_closure (s := {x | ∃ h ∈ H, ∃ a : ℕ, x = h * g ^ a}) ?_ h₁ h₂ ?_ hd
  · rintro _ ⟨x, hx, a, rfl⟩
    exact h x hx a
  · rintro _ ⟨x, hx, a, rfl⟩
    exact G.mul_mem (hHG hx) (pow_mem hg a)


omit [IsUltrametricDist X] [TopologicalSpace Γ] in
theorem exists_extension [CompleteSpace X] (Gn : ℕ → Subgroup Γ) (hanti : Antitone Gn)
    (hcos : ∀ σ ∈ G, ∀ n, ∃ a : ℕ, σ * (g ^ a)⁻¹ ∈ Gn n) (S : ℕ → X)
    (hS : ∀ ε > 0, ∃ N, ∀ a b : ℕ, g ^ a * (g ^ b)⁻¹ ∈ Gn N → ‖S a - S b‖ ≤ ε) :
    ∃ c : Γ → X, ∀ ε > 0, ∃ N, ∀ σ ∈ G, ∀ a : ℕ, σ * (g ^ a)⁻¹ ∈ Gn N → ‖c σ - S a‖ ≤ ε := by
  choose! e he using hcos
  have key : ∀ {N : ℕ} {σ : Γ} {a b : ℕ}, σ * (g ^ a)⁻¹ ∈ Gn N → σ * (g ^ b)⁻¹ ∈ Gn N →
      g ^ a * (g ^ b)⁻¹ ∈ Gn N := by
    intro N σ a b ha hb
    have := (Gn N).mul_mem ((Gn N).inv_mem ha) hb
    simpa [mul_assoc] using this
  have hc : ∀ σ ∈ G, ∃ y, Tendsto (fun n => S (e σ n)) atTop (𝓝 y) := by
    intro σ hσ
    refine cauchySeq_tendsto_of_complete (Metric.cauchySeq_iff.2 fun ε hε => ?_)
    obtain ⟨N, hN⟩ := hS (ε / 2) (half_pos hε)
    refine ⟨N, fun m hm n hn => ?_⟩
    rw [dist_eq_norm]
    exact (hN _ _ (key (hanti hm (he σ hσ m)) (hanti hn (he σ hσ n)))).trans_lt (half_lt_self hε)
  choose! c hc using hc
  refine ⟨c, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := hS ε hε
  refine ⟨N, fun σ hσ a ha => ?_⟩
  refine le_of_tendsto ((hc σ hσ).sub_const (S a)).norm ?_
  filter_upwards [eventually_ge_atTop N] with n hn
  exact hN _ _ (key (hanti hn (he σ hσ n)) ha)

theorem exists_cocycle [CompleteSpace X] [ContinuousMul Γ] {H : Subgroup Γ} (p : ℕ)
    (Gn : ℕ → Subgroup Γ) (hanti : Antitone Gn) (M : AddSubgroup X) (hMc : IsClosed (M : Set X))
    (hg : g ∈ G) (hw : w ∈ M) (hHG : H ≤ G) (hHn : ∀ n, H ≤ Gn n)
    (hnorm : ∀ σ ∈ G, ∀ h ∈ H, σ * h * σ⁻¹ ∈ H) (hone : ∀ y, A 1 y = y)
    (hmul : ∀ σ ∈ G, ∀ τ ∈ G, ∀ y, A (σ * τ) y = A σ (A τ y))
    (hn : ∀ σ ∈ G, ∀ y, ‖A σ y‖ ≤ ‖y‖) (hcont : ∀ y, ContinuousOn (fun σ => A σ y) G)
    (hAM : ∀ σ ∈ G, ∀ y ∈ M, A σ y ∈ M) (hHM : ∀ h ∈ H, ∀ y ∈ M, A h y = y)
    (hopen : ∀ N, ∀ σ ∈ G, ∀ᶠ τ in 𝓝[G] σ, τ * σ⁻¹ ∈ Gn N)
    (hcos : ∀ σ ∈ G, ∀ n, ∃ a : ℕ, σ * (g ^ a)⁻¹ ∈ Gn n)
    (hd : (G : Set Γ) ⊆ closure {x | ∃ h ∈ H, ∃ a : ℕ, x = h * g ^ a})
    (hdvd : ∀ k, ∃ N, ∀ d : ℕ, g ^ d ∈ Gn N → p ^ k ∣ d)
    (hD : ∀ ε > 0, ∃ k : ℕ, ‖A (g ^ p ^ k) w - w‖ ≤ ε)
    (hp : ∀ ε > 0, ∃ s : ℕ, ∀ y : X, ‖y‖ ≤ ‖w‖ → ‖p ^ s • y‖ ≤ ε) :
    ∃ c : Γ → X, ContinuousOn c G ∧ (∀ σ ∈ G, c σ ∈ M) ∧
      (∀ σ ∈ G, ∀ τ ∈ G, c (σ * τ) = c σ + A σ (c τ)) ∧ (∀ h ∈ H, c h = 0) ∧ c g = w := by
  have hS : ∀ ε > 0, ∃ N, ∀ a b : ℕ, g ^ a * (g ^ b)⁻¹ ∈ Gn N →
      ‖psum A g w a - psum A g w b‖ ≤ ε := by
    intro ε hε
    obtain ⟨k, hk⟩ := exists_norm_psum_sub_le p hg hone hmul hn hD hp ε hε
    obtain ⟨N, hN⟩ := hdvd k
    have h1 : ∀ a b : ℕ, b ≤ a → g ^ a * (g ^ b)⁻¹ ∈ Gn N →
        ‖psum A g w a - psum A g w b‖ ≤ ε := by
      intro a b hab h
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
      refine hk _ _ (hN d ?_)
      rwa [add_comm, pow_add, mul_inv_cancel_right] at h
    refine ⟨N, fun a b h => ?_⟩
    rcases le_total b a with hab | hab
    · exact h1 a b hab h
    · rw [norm_sub_rev]
      refine h1 b a hab ?_
      simpa using (Gn N).inv_mem h
  obtain ⟨c, hc⟩ := exists_extension Gn hanti hcos _ hS
  have hval : ∀ h ∈ H, ∀ a : ℕ, c (h * g ^ a) = psum A g w a := by
    intro h hh a
    rw [← sub_eq_zero, ← norm_le_zero_iff]
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨N, hN⟩ := hc ε hε
    rw [zero_add]
    refine hN _ (G.mul_mem (hHG hh) (pow_mem hg a)) a ?_
    rw [mul_inv_cancel_right]
    exact hHn N hh
  have hcc : ContinuousOn c G := by
    intro σ hσ
    rw [ContinuousWithinAt, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨N, hN⟩ := hc (ε / 2) (half_pos hε)
    obtain ⟨a, ha⟩ := hcos σ hσ N
    filter_upwards [hopen N σ hσ, self_mem_nhdsWithin] with τ hτ hτG
    have h1 : τ * (g ^ a)⁻¹ ∈ Gn N := by
      have := (Gn N).mul_mem hτ ha
      simpa [mul_assoc] using this
    have h2 : c τ - c σ = (c τ - psum A g w a) + -(c σ - psum A g w a) := by abel
    rw [dist_eq_norm, h2]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
    · exact (hN τ hτG a h1).trans_lt (half_lt_self hε)
    · rw [norm_neg]; exact (hN σ hσ a ha).trans_lt (half_lt_self hε)
  have hSM : ∀ n, psum A g w n ∈ M := psum_mem hw (hAM g hg)
  have hcM : ∀ σ ∈ G, c σ ∈ M := by
    intro σ hσ
    change c σ ∈ (M : Set X)
    rw [← hMc.closure_eq, Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hc (ε / 2) (half_pos hε)
    obtain ⟨a, ha⟩ := hcos σ hσ N
    exact ⟨_, hSM a, by rw [dist_eq_norm]; exact (hN σ hσ a ha).trans_lt (half_lt_self hε)⟩
  have hAc : ∀ σ ∈ G, Continuous (A σ) := fun σ hσ =>
    AddMonoidHomClass.continuous_of_bound (A σ) 1 (fun y => by rw [one_mul]; exact hn σ hσ y)
  refine ⟨c, hcc, hcM, ?_, fun h hh => ?_, ?_⟩
  · have hconj : ∀ h ∈ H, ∀ a : ℕ, ∀ τ ∈ G, c (h * g ^ a * τ) = c (h * g ^ a) + A (h * g ^ a) (c τ) := by
      intro h hh a
      have hσ : h * g ^ a ∈ G := G.mul_mem (hHG hh) (pow_mem hg a)
      refine eqOn_of_dense hg hHG hd (f₁ := fun τ => c (h * g ^ a * τ))
        (f₂ := fun τ => c (h * g ^ a) + A (h * g ^ a) (c τ)) ?_ ?_ fun h' hh' b => ?_
      · exact hcc.comp (continuous_const_mul _).continuousOn fun x hx => G.mul_mem hσ hx
      · exact continuousOn_const.add ((hAc _ hσ).comp_continuousOn hcc)
      · have h1 : h * g ^ a * (h' * g ^ b) = (h * (g ^ a * h' * (g ^ a)⁻¹)) * g ^ (a + b) := by
          rw [pow_add]; group
        rw [h1, hval _ (H.mul_mem hh (hnorm _ (pow_mem hg a) _ hh')), hval h hh, hval h' hh',
          hmul _ (hHG hh) _ (pow_mem hg a), hHM h hh _ (hAM _ (pow_mem hg a) _ (hSM b)),
          psum_add hg hone hmul]
    intro σ hσ τ hτ
    refine eqOn_of_dense hg hHG hd (f₁ := fun σ => c (σ * τ)) (f₂ := fun σ => c σ + A σ (c τ))
      ?_ (hcc.add (hcont _)) (fun h hh a => hconj h hh a τ hτ) σ hσ
    exact hcc.comp (continuous_mul_const τ).continuousOn fun x hx => G.mul_mem hx hτ
  · simpa [psum] using hval h hh 0
  · simpa [psum] using hval 1 H.one_mem 1

end Abstract

variable {l : ℕ} [Fact l.Prime]

def intSub (F : IntermediateField ℚ_[l] (Om l)) : Subring (PadicComplex l) where
  carrier := intC F
  mul_mem' := by
    rintro _ _ ⟨⟨x, hx, rfl⟩, hx1⟩ ⟨⟨y, hy, rfl⟩, hy1⟩
    refine ⟨⟨x * y, F.mul_mem hx hy, UniformSpace.Completion.coe_mul _ _⟩, ?_⟩
    rw [norm_mul]; exact mul_le_one₀ hx1 (norm_nonneg _) hy1
  one_mem' := ⟨⟨1, F.one_mem, UniformSpace.Completion.coe_one _⟩, norm_one.le⟩
  add_mem' := by
    rintro _ _ ⟨⟨x, hx, rfl⟩, hx1⟩ ⟨⟨y, hy, rfl⟩, hy1⟩
    exact ⟨⟨x + y, F.add_mem hx hy, UniformSpace.Completion.coe_add _ _⟩,
      (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx1 hy1)⟩
  zero_mem' := ⟨⟨0, F.zero_mem, UniformSpace.Completion.coe_zero⟩, by simp⟩
  neg_mem' := by
    rintro _ ⟨⟨x, hx, rfl⟩, hx1⟩
    exact ⟨⟨-x, F.neg_mem hx, UniformSpace.Completion.coe_neg _⟩, by rwa [norm_neg]⟩

def ohatSub (K : FinExt l) : Subring (PadicComplex l) := (intSub (Kinf K)).topologicalClosure

theorem mem_ohatSub (K : FinExt l) (y : PadicComplex l) : y ∈ ohatSub K ↔ y ∈ Ohat K := Iff.rfl

theorem algebraMap_eq_coe (x : ℚ_[l]) :
    algebraMap ℚ_[l] (PadicComplex l) x = ((algebraMap ℚ_[l] (Om l) x : Om l) : PadicComplex l) := by
  rw [IsScalarTower.algebraMap_apply ℚ_[l] (Om l) (PadicComplex l)]
  rfl

variable {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} {χ : GQ l →* ℚ_[l]ˣ}

theorem continuous_act (h : IsActC act) (σ : GQ l) : Continuous (act σ) :=
  AddMonoidHomClass.continuous_of_bound (act σ) 1 fun y => by rw [one_mul, h.2]

theorem conj_mem_Hinf (hχ : IsCyc χ) (K : FinExt l) {m : ℕ} {σ : GQ l} (hσ : σ ∈ Gj K m)
    {h : GQ l} (hh : h ∈ Hinf K) : σ * h * σ⁻¹ ∈ Hinf K := by
  obtain ⟨-, -, hG⟩ := cyc_basic l χ hχ
  have hσ0 := cyclotomicTowerLevelGaloisSubgroup_le_fixingSubgroup_base K m hσ
  have hh0 := cyclotomicTowerLevelGaloisSubgroup_le_fixingSubgroup_base K m (AlmostTrace.Hinf_le_Gj K m hh)
  refine (hG K _ (mul_mem (mul_mem hσ0 hh0) (inv_mem hσ0))).2.2 ?_
  rw [map_mul, map_mul, (hG K h hh0).2.1 hh, map_inv, mul_one, mul_inv_cancel]

theorem act_mem_Ohat (hact : IsActC act) (hχ : IsCyc χ) (K : FinExt l) {m : ℕ} {σ : GQ l}
    (hσ : σ ∈ Gj K m) {y : PadicComplex l} (hy : y ∈ Ohat K) : act σ y ∈ Ohat K := by
  refine map_mem_closure (continuous_act hact σ) hy ?_
  rintro _ ⟨⟨x, hx, rfl⟩, hx1⟩
  refine ⟨⟨σ x, ?_, (hact.1 σ x).symm⟩, by rwa [hact.2]⟩
  change σ x ∈ Kinf K
  rw [← InfiniteGalois.fixedField_fixingSubgroup (Kinf K), IntermediateField.mem_fixedField_iff]
  intro h hh
  have h1 : (σ⁻¹ * h * σ⁻¹⁻¹) x = x := conj_mem_Hinf hχ K (inv_mem hσ) hh ⟨x, hx⟩
  conv_rhs => rw [← h1]
  rw [← AlgEquiv.mul_apply, ← AlgEquiv.mul_apply]
  congr 1
  group

theorem act_eq_of_mem_intC (hact : IsActC act) {F : IntermediateField ℚ_[l] (Om l)} {σ : GQ l}
    (hσ : σ ∈ F.fixingSubgroup) {y : PadicComplex l} (hy : y ∈ intC F) : act σ y = y := by
  obtain ⟨⟨x, hx, rfl⟩, -⟩ := hy
  have : σ x = x := hσ ⟨x, hx⟩
  rw [hact.1, this]

theorem act_eq_of_mem_Ohat (hact : IsActC act) (K : FinExt l) {h : GQ l} (hh : h ∈ Hinf K)
    {y : PadicComplex l} (hy : y ∈ Ohat K) : act h y = y :=
  (isClosed_eq (continuous_act hact h) continuous_id).closure_subset_iff.2
    (fun _ hz => act_eq_of_mem_intC hact hh hz) hy

theorem chiC_mem_intC (hχ : IsCyc χ) (F : IntermediateField ℚ_[l] (Om l)) (i : ℤ) (σ : GQ l) :
    chiC χ i σ ∈ intC F := by
  refine ⟨⟨_, F.algebraMap_mem _, (algebraMap_eq_coe _).symm⟩, ?_⟩
  rw [chiC, norm_algebraMap', Units.val_zpow_eq_zpow_val, norm_zpow, (cyc_basic l χ hχ).1, one_zpow]

theorem continuous_chiC (hχ : IsCyc χ) (i : ℤ) : Continuous (chiC χ i) := by
  unfold chiC
  refine (continuous_algebraMap _ _).comp ?_
  simp only [Units.val_zpow_eq_zpow_val]
  exact (cyc_basic l χ hχ).2.1.zpow₀ i fun σ => Or.inl (Units.ne_zero _)

def twHom (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ) (i : ℤ) {r : ℕ}
    (U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)) (σ : GQ l) :
    (Fin r → PadicComplex l) →+ (Fin r → PadicComplex l) :=
  AddMonoidHom.mk' (twAct act χ i U σ) fun x y => by
    ext a
    simp [twAct, Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib]

theorem twHom_apply (i : ℤ) {r : ℕ} (U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l))
    (σ : GQ l) (y : Fin r → PadicComplex l) (a : Fin r) :
    twHom act χ i U σ y a = chiC χ i σ * ∑ b, U σ a b * act σ (y b) := rfl

variable {K : FinExt l} {m r : ℕ} {U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)} {g : GQ l}

theorem twHom_mul (hact : IsActC act) (hχ : IsCyc χ) (hF : Frame χ K m U g) (i : ℤ) :
    ∀ σ ∈ Gj K m, ∀ τ ∈ Gj K m, ∀ y,
      twHom act χ i U (σ * τ) y = twHom act χ i U σ (twHom act χ i U τ y) := by
  intro σ hσ τ hτ y
  ext a
  have h1 : chiC χ i (σ * τ) = chiC χ i σ * chiC χ i τ := by
    simp only [chiC, map_mul, mul_zpow, Units.val_mul]
  have h2 : act σ (chiC χ i τ) = chiC χ i τ :=
    act_eq_of_mem_intC hact hσ (chiC_mem_intC hχ (Ks K m) i τ)
  have h3 : ∀ a b, act σ (U τ a b) = U τ a b := fun a b =>
    act_eq_of_mem_intC hact hσ (hF.2.2.1 τ hτ a b)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [twHom_apply, h1, hF.2.2.2.1 σ hσ τ hτ, Matrix.mul_apply, map_mul, map_sum, h2, h3,
    RingAut.mul_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
  ring

theorem twHom_of_mem_Hinf (hχ : IsCyc χ) (hF : Frame χ K m U g) (i : ℤ) {h : GQ l}
    (hh : h ∈ Hinf K) (y : Fin r → PadicComplex l) (a : Fin r) :
    twHom act χ i U h y a = act h (y a) := by
  have hh0 := cyclotomicTowerLevelGaloisSubgroup_le_fixingSubgroup_base K m (AlmostTrace.Hinf_le_Gj K m hh)
  rw [twHom_apply, chiC, ((cyc_basic l χ hχ).2.2 K h hh0).2.1 hh, hF.2.2.2.2.1 h hh]
  simp [Matrix.one_apply]

theorem norm_twHom_le (hact : IsActC act) (hχ : IsCyc χ) (hF : Frame χ K m U g) (i : ℤ) :
    ∀ σ ∈ Gj K m, ∀ y, ‖twHom act χ i U σ y‖ ≤ ‖y‖ := by
  intro σ hσ y
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun a => ?_
  rw [twHom_apply, norm_mul]
  refine (mul_le_of_le_one_left (norm_nonneg _) (chiC_mem_intC hχ (Ks K m) i σ).2).trans ?_
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun b _ => ?_
  rw [norm_mul, hact.2]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hF.2.2.1 σ hσ a b).2).trans (norm_le_pi_norm y b)

theorem continuousOn_twHom (hact : IsActC act) (hχ : IsCyc χ) (hF : Frame χ K m U g) (i : ℤ)
    (y : Fin r → PadicComplex l) : ContinuousOn (fun σ => twHom act χ i U σ y) (Gj K m) := by
  refine continuousOn_pi.2 fun a => ?_
  simp only [twHom_apply]
  exact (continuous_chiC hχ i).continuousOn.mul (continuousOn_finsetSum _ fun b _ =>
    (hF.2.1 a b).mul (IsActC.continuous_orbit l act hact _).continuousOn)

theorem procyclic : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ (m r : ℕ), Lev l m → ∀ (U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)) (g : GQ l), Frame χ K m U g → ∀ i : ℤ, (∀ c : GQ l → Fin r → PadicComplex l, CocOn (Gj K m) (twAct act χ i U) Set.univ c → (∀ h ∈ Hinf K, c h = 0) → c g = 0 → ∀ σ ∈ Gj K m, c σ = 0) ∧ ∀ w : Fin r → PadicComplex l, (∀ a, w a ∈ Ohat K) → ∃ c : GQ l → Fin r → PadicComplex l, CocOn (Gj K m) (twAct act χ i U) {y | ∀ a, y a ∈ Ohat K} c ∧ (∀ h ∈ Hinf K, c h = 0) ∧ c g = w := by
  intro l _ act χ hact hχ K m r hm U g hF i
  have hl : l.Prime := Fact.out
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  obtain ⟨hχ1, hχc, hG⟩ := cyc_basic l χ hχ
  obtain ⟨hpow, hcos, hd⟩ := (gen_dense l act χ hact hχ K m hm).2 g hF.1
  have hg : g ∈ Gj K m := hF.1.1
  have hHG := AlmostTrace.Hinf_le_Gj K
  have hanti : Antitone (Gj K) := fun a b hab σ hσ x =>
    hσ ⟨x.1, AlmostTrace.Ks_mono K hab x.2⟩
  refine ⟨fun c hc hcH hcg => ?_, fun w hw => ?_⟩
  · have hz : ∀ σ, twAct act χ i U σ 0 = 0 := fun σ => (twHom act χ i U σ).map_zero
    have hp : ∀ a : ℕ, c (g ^ a) = 0 := by
      intro a
      induction a with
      | zero => exact hcH _ (by rw [pow_zero]; exact one_mem _)
      | succ a ih => rw [pow_succ, hc.2.2 _ (pow_mem hg a) _ hg, ih, hcg, hz, add_zero]
    refine eqOn_of_dense hg (hHG m) hd (f₂ := fun _ => 0) hc.1 continuousOn_const fun h hh a => ?_
    rw [hc.2.2 _ (hHG m hh) _ (pow_mem hg a), hp, hcH h hh, hz, add_zero]
  · let M : AddSubgroup (Fin r → PadicComplex l) :=
      AddSubgroup.pi Set.univ fun _ => (ohatSub K).toAddSubgroup
    have hM : ∀ y, y ∈ M ↔ ∀ a, y a ∈ Ohat K := fun y => by
      simp only [M, AddSubgroup.mem_pi, Set.mem_univ, true_imp_iff]; rfl
    have hHM : ∀ h ∈ Hinf K, ∀ y ∈ M, twHom act χ i U h y = y := by
      intro h hh y hy
      ext a
      rw [twHom_of_mem_Hinf hχ hF i hh, act_eq_of_mem_Ohat hact K hh ((hM y).1 hy a)]
    have hsub : ∀ y ∈ intC (Ks K m), y ∈ ohatSub K := by
      rintro _ ⟨⟨x, hx, rfl⟩, h1⟩
      exact subset_closure ⟨⟨x, AlmostTrace.Ks_le_Kinf K m hx, rfl⟩, h1⟩
    have hopen : ∀ N, ∀ σ ∈ Gj K m, ∀ᶠ τ in 𝓝[Gj K m] σ, τ * σ⁻¹ ∈ Gj K N := by
      intro N σ hσ
      have h1 : Continuous fun τ : GQ l => ‖(χ (τ * σ⁻¹) : ℚ_[l]) - 1‖ :=
        ((hχc.comp (continuous_mul_const _)).sub continuous_const).norm
      have h2 : ∀ᶠ τ in 𝓝 σ, ‖(χ (τ * σ⁻¹) : ℚ_[l]) - 1‖ < (l : ℝ) ^ (-(N : ℤ)) :=
        h1.continuousAt.eventually_lt continuousAt_const (by simpa using zpow_pos hl0 (N : ℤ))
      filter_upwards [mem_nhdsWithin_of_mem_nhds h2, self_mem_nhdsWithin] with τ h3 hτ
      exact ((hG K _ (cyclotomicTowerLevelGaloisSubgroup_le_fixingSubgroup_base K m (mul_mem hτ (inv_mem hσ)))).1 N).2 h3.le
    refine (exists_cocycle (A := twHom act χ i U) (H := Hinf K) l (Gj K)
      hanti M ?_ hg ((hM w).2 hw) (hHG m) hHG (fun σ hσ h hh => conj_mem_Hinf hχ K hσ hh) ?_
      (twHom_mul hact hχ hF i) (norm_twHom_le hact hχ hF i) (continuousOn_twHom hact hχ hF i) ?_
      hHM hopen hcos hd ?_ ?_ ?_).imp
      fun c ⟨h1, h2, h3, h4, h5⟩ => ⟨⟨h1, fun σ hσ => (hM _).1 (h2 σ hσ), h3⟩, h4, h5⟩
    · exact isClosed_set_pi fun _ _ => isClosed_closure
    · intro y
      ext a
      rw [twHom_of_mem_Hinf hχ hF i (one_mem _), map_one]; rfl
    · intro σ hσ y hy
      refine (hM _).2 fun a => (mem_ohatSub K _).1 ?_
      rw [twHom_apply]
      exact mul_mem (hsub _ (chiC_mem_intC hχ _ i σ)) (sum_mem fun b _ =>
        mul_mem (hsub _ (hF.2.2.1 σ hσ a b)) (act_mem_Ohat hact hχ K hσ ((hM y).1 hy b)))
    · intro k
      refine ⟨m + k, fun d hdm => ?_⟩
      rcases eq_or_ne d 0 with rfl | hd0
      · exact dvd_zero _
      have e1 := ((hG K _ (cyclotomicTowerLevelGaloisSubgroup_le_fixingSubgroup_base K _ hdm)).1 _).1 hdm
      have e2 := LiftExp.norm_zpow_sub_one l m hm _ hF.1.2 (d : ℤ) (by exact_mod_cast hd0)
      rw [zpow_natCast, padicValInt.of_nat] at e2
      rw [map_pow, Units.val_pow_eq_pow_val, e2, zpow_le_zpow_iff_right₀ hl1] at e1
      refine ((by simpa only [_root_.Nat.padicValNat_def] using @_root_.multiplicity_dvd_iff_le : ∀ {p : _root_.Nat} [hp : _root_.Fact (_root_.Nat.Prime p)] {a n : _root_.Nat} (ha : a ≠ 0), p ^ n ∣ a ↔ n ≤ _root_.padicValNat p a) hd0).2 ?_
      rw [_root_.Nat.padicValNat_def]
      omega
    · intro ε hε
      have hc := (continuousOn_twHom hact hχ hF i w).sub (continuousOn_const (c := w))
      obtain ⟨V, hV, hVe⟩ := (continuousOn_iff'.1 hc) _ (Metric.isOpen_ball (x := 0) (ε := ε))
      have hHV : (Hinf K : Set (GQ l)) ⊆ V := by
        intro h hh
        have : h ∈ V ∩ Gj K m := by
          rw [← hVe]
          refine ⟨?_, hHG m hh⟩
          simp [hHM h hh w ((hM w).2 hw), hε]
        exact this.1
      obtain ⟨k, hk⟩ := AlmostTrace.exists_Gj_subset K hV hHV
      refine ⟨k, ?_⟩
      have : g ^ l ^ k ∈ V ∩ Gj K m := ⟨hk (m + k) (by omega) (hpow k).1, pow_mem hg _⟩
      rw [← hVe] at this
      exact (mem_ball_zero_iff.1 this.1).le
    · intro ε hε
      obtain ⟨s, hs⟩ := exists_pow_lt_of_lt_one (div_pos hε (by positivity : 0 < ‖w‖ + 1))
        (inv_lt_one_of_one_lt₀ hl1)
      refine ⟨s, fun y hy => ?_⟩
      have hn : ‖(l : PadicComplex l)‖ = (l : ℝ)⁻¹ := by
        rw [← map_natCast (algebraMap ℚ_[l] (PadicComplex l)), norm_algebraMap', Padic.norm_p]
      rw [← Nat.cast_smul_eq_nsmul (PadicComplex l), norm_smul, Nat.cast_pow, norm_pow, hn]
      rw [lt_div_iff₀ (by positivity)] at hs
      exact (mul_le_mul_of_nonneg_left (by linarith) (by positivity)).trans hs.le

end GlobalTheory.Cyc.Procyclic
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocycleVanishingOnFixingSubgroupDeterminedByGeneStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cocycle_vanishing_on_fixingSubgroup_determined_by_generator : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ (m r : ℕ), Lev l m → ∀ (U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)) (g : GQ l), Frame χ K m U g → ∀ i : ℤ, (∀ c : GQ l → Fin r → PadicComplex l, CocOn (Gj K m) (twAct act χ i U) Set.univ c → (∀ h ∈ Hinf K, c h = 0) → c g = 0 → ∀ σ ∈ Gj K m, c σ = 0) ∧ ∀ w : Fin r → PadicComplex l, (∀ a, w a ∈ Ohat K) → ∃ c : GQ l → Fin r → PadicComplex l, CocOn (Gj K m) (twAct act χ i U) {y | ∀ a, y a ∈ Ohat K} c ∧ (∀ h ∈ Hinf K, c h = 0) ∧ c g = w := by
  first | exact @GlobalTheory.Cyc.Procyclic.procyclic | exact GlobalTheory.Cyc.Procyclic.procyclic | (intros; apply GlobalTheory.Cyc.Procyclic.procyclic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocycleTwistCoboundaryOnBall
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.Cyc.FrameTorsion

section Basic

variable {l : ℕ} [Fact l.Prime]

theorem ks_le_kinf (K : FinExt l) (s : ℕ) : Ks K s ≤ Kinf K := by
  unfold Ks Kinf
  refine sup_le_sup_left ?_ _
  exact IntermediateField.adjoin.mono _ _ _ (fun x hx => ⟨s, hx⟩)

theorem hinf_le_gj (K : FinExt l) (s : ℕ) : Hinf K ≤ Gj K s := by
  intro g hg
  rw [Hinf, IntermediateField.mem_fixingSubgroup_iff] at hg
  rw [Gj, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  exact hg x (ks_le_kinf K s hx)

theorem gj_le (K : FinExt l) (s : ℕ) : Gj K s ≤ (K0 K).fixingSubgroup := by
  intro g hg
  rw [Gj, IntermediateField.mem_fixingSubgroup_iff] at hg
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  apply hg x
  unfold Ks
  exact (le_sup_left : K0 K ≤ _) hx

theorem act_inC {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} (ha : IsActC act)
    {F : IntermediateField ℚ_[l] (Om l)} {g : GQ l} (hg : g ∈ F.fixingSubgroup)
    {y : PadicComplex l} (hy : y ∈ inC F) : act g y = y := by
  obtain ⟨x, hxF, rfl⟩ := hy
  rw [ha.1 g x]
  congr 1
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg x hxF

theorem algebraMap_eq (q : ℚ_[l]) :
    algebraMap ℚ_[l] (PadicComplex l) q = ((algebraMap ℚ_[l] (Om l) q : Om l) : PadicComplex l) := IsScalarTower.algebraMap_apply ℚ_[l] (Om l) (PadicComplex l) q

theorem act_algebraMap {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} (ha : IsActC act)
    (g : GQ l) (q : ℚ_[l]) :
    act g (algebraMap ℚ_[l] (PadicComplex l) q) = algebraMap ℚ_[l] (PadicComplex l) q := by
  rw [algebraMap_eq, ha.1 g, AlgEquiv.commutes]

theorem norm_algebraMap (q : ℚ_[l]) : ‖algebraMap ℚ_[l] (PadicComplex l) q‖ = ‖q‖ := by
  rw [algebraMap_eq, PadicComplex.norm_extends, PadicAlgCl.norm_extends]

theorem continuous_algMap : Continuous (algebraMap ℚ_[l] (PadicComplex l)) := by
  have hiso : Isometry (algebraMap ℚ_[l] (PadicComplex l)) :=
    AddMonoidHomClass.isometry_of_norm (algebraMap ℚ_[l] (PadicComplex l)) norm_algebraMap
  exact hiso.continuous

theorem chiC_mul (χ : GQ l →* ℚ_[l]ˣ) (j : ℤ) (g h : GQ l) :
    chiC χ j (g * h) = chiC χ j g * chiC χ j h := by
  simp only [chiC, map_mul, mul_zpow, Units.val_mul]

theorem norm_l_lt : ‖(l : PadicComplex l)‖ < 1 := by
  have h1 : (l : PadicComplex l) = algebraMap ℚ_[l] (PadicComplex l) (l : ℚ_[l]) := (map_natCast _ l).symm
  rw [h1, norm_algebraMap]
  exact Padic.norm_p_lt_one

theorem ohat_norm (K : FinExt l) {y : PadicComplex l} (hy : y ∈ Ohat K) : ‖y‖ ≤ 1 := by
  have hcl : IsClosed {y : PadicComplex l | ‖y‖ ≤ 1} := isClosed_le continuous_norm continuous_const
  exact closure_minimal (by exact fun z hz => hz.2) hcl hy

theorem norm_chiC {χ : GQ l →* ℚ_[l]ˣ} (hχ : IsCyc χ) (j : ℤ) (g : GQ l) : ‖chiC χ j g‖ = 1 := by
  rw [chiC, norm_algebraMap, Units.val_zpow_eq_zpow_val, norm_zpow, IsCyc.norm_eq_one hχ g, one_zpow]

theorem continuous_chiC {χ : GQ l →* ℚ_[l]ˣ} (hχ : IsCyc χ) (j : ℤ) : Continuous (chiC χ j) := by
  have h0 : Continuous (fun g : GQ l => ((χ g : ℚ_[l])) ^ j) :=
    (IsCyc.continuous hχ).zpow₀ j (fun g => Or.inl (χ g).ne_zero)
  have h1 : chiC χ j = fun g => algebraMap ℚ_[l] (PadicComplex l) ((χ g : ℚ_[l]) ^ j) := by
    funext g
    rw [chiC, Units.val_zpow_eq_zpow_val]
  rw [h1]
  exact continuous_algMap.comp h0

theorem chi_hinf {χ : GQ l →* ℚ_[l]ˣ} (hχ : IsCyc χ) (K : FinExt l) {h : GQ l} (hh : h ∈ Hinf K) :
    χ h = 1 := by
  have hK0 : h ∈ (K0 K).fixingSubgroup := gj_le K 0 (hinf_le_gj K 0 hh)
  exact ((cyc_basic l χ hχ).2.2 K h hK0).2.1 hh

theorem chiC_hinf {χ : GQ l →* ℚ_[l]ˣ} (hχ : IsCyc χ) (K : FinExt l) (j : ℤ) {h : GQ l}
    (hh : h ∈ Hinf K) : chiC χ j h = 1 := by
  rw [chiC, chi_hinf hχ K hh, one_zpow, Units.val_one, map_one]

theorem conj_hinf {χ : GQ l →* ℚ_[l]ˣ} (hχ : IsCyc χ) (K : FinExt l) (s : ℕ) {g h : GQ l}
    (hg : g ∈ Gj K s) (hh : h ∈ Hinf K) : g⁻¹ * h * g ∈ Hinf K := by
  have hg0 : g ∈ (K0 K).fixingSubgroup := gj_le K s hg
  have hh0 : h ∈ (K0 K).fixingSubgroup := gj_le K 0 (hinf_le_gj K 0 hh)
  have hx0 : g⁻¹ * h * g ∈ (K0 K).fixingSubgroup :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hg0) hh0) hg0
  rw [((cyc_basic l χ hχ).2.2 K _ hx0).2]
  rw [map_mul, map_mul, chi_hinf hχ K hh, mul_one, map_inv, inv_mul_cancel]

end Basic

variable {l : ℕ} [Fact l.Prime] {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)}
  {χ : GQ l →* ℚ_[l]ˣ} {r : ℕ} {U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)} {i : ℤ}

theorem tw_add (σ : GQ l) (x y : Fin r → PadicComplex l) :
    twAct act χ i U σ (x + y) = twAct act χ i U σ x + twAct act χ i U σ y := by
  have hv : (fun a => act σ ((x + y) a)) = (fun a => act σ (x a)) + (fun a => act σ (y a)) := by
    funext a
    simp only [Pi.add_apply, map_add (f := _)]
  simp only [twAct, hv, Matrix.mulVec_add, smul_add]

theorem tw_sub (σ : GQ l) (x y : Fin r → PadicComplex l) :
    twAct act χ i U σ (x - y) = twAct act χ i U σ x - twAct act χ i U σ y := by
  have hv : (fun a => act σ ((x - y) a)) = (fun a => act σ (x a)) - (fun a => act σ (y a)) := by
    funext a
    simp only [Pi.sub_apply, map_sub]
  simp only [twAct, hv, Matrix.mulVec_sub, smul_sub]

theorem tw_zero (σ : GQ l) : twAct act χ i U σ 0 = 0 := by
  have hv : (fun a => act σ ((0 : Fin r → PadicComplex l) a)) = 0 := by
    funext a
    simp only [Pi.zero_apply, map_zero]
  simp only [twAct, hv, Matrix.mulVec_zero, smul_zero]

theorem tw_pow (σ : GQ l) (n : ℕ) (x : Fin r → PadicComplex l) :
    twAct act χ i U σ ((l : PadicComplex l) ^ n • x)
      = (l : PadicComplex l) ^ n • twAct act χ i U σ x := by
  have hl : ∀ z : PadicComplex l, act σ ((l : PadicComplex l) ^ n * z) = (l : PadicComplex l) ^ n * act σ z := by
    intro z
    rw [map_mul, map_pow, map_natCast]
  have hv : (fun a => act σ (((l : PadicComplex l) ^ n • x) a)) = (l : PadicComplex l) ^ n • (fun a => act σ (x a)) := by
    funext a
    simp only [Pi.smul_apply, smul_eq_mul, hl]
  simp only [twAct, hv, Matrix.mulVec_smul, smul_comm (chiC χ i σ)]

theorem ball_add {x y : Fin r → PadicComplex l} (hx : x ∈ ball l r) (hy : y ∈ ball l r) :
    x + y ∈ ball l r := by
  intro a
  calc ‖(x + y) a‖ = ‖x a + y a‖ := rfl
    _ ≤ max ‖x a‖ ‖y a‖ := IsUltrametricDist.norm_add_le_max _ _
    _ ≤ 1 := max_le (hx a) (hy a)

theorem ball_sub {x y : Fin r → PadicComplex l} (hx : x ∈ ball l r) (hy : y ∈ ball l r) :
    x - y ∈ ball l r := by
  intro a
  calc ‖(x - y) a‖ = ‖x a + -y a‖ := by rw [Pi.sub_apply, sub_eq_add_neg]
    _ ≤ max ‖x a‖ ‖-y a‖ := IsUltrametricDist.norm_add_le_max _ _
    _ = max ‖x a‖ ‖y a‖ := by rw [norm_neg]
    _ ≤ 1 := max_le (hx a) (hy a)

theorem ball_pow (n : ℕ) {x : Fin r → PadicComplex l} (hx : x ∈ ball l r) :
    (l : PadicComplex l) ^ n • x ∈ ball l r := by
  intro a
  have hl1 : ‖(l : PadicComplex l)‖ ≤ 1 := le_of_lt norm_l_lt
  calc ‖((l : PadicComplex l) ^ n • x) a‖ = ‖(l : PadicComplex l)‖ ^ n * ‖x a‖ := by
        rw [Pi.smul_apply, smul_eq_mul, norm_mul, norm_pow]
    _ ≤ 1 * 1 := mul_le_mul (pow_le_one₀ (norm_nonneg _) hl1) (hx a) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

variable {K : FinExt l} {m : ℕ} {g : GQ l}

theorem tw_ball (ha : IsActC act) (hχ : IsCyc χ) (hU : Frame χ K m U g) {σ : GQ l}
    (hσ : σ ∈ Gj K m) {x : Fin r → PadicComplex l} (hx : x ∈ ball l r) :
    twAct act χ i U σ x ∈ ball l r := by
  intro a
  have hU1 : ∀ b, ‖U σ a b‖ ≤ 1 := fun b => (hU.2.2.1 σ hσ a b).2
  have hs : ‖∑ b, U σ a b * act σ (x b)‖ ≤ 1 := by
    refine Finset.sum_induction _ (fun z : PadicComplex l => ‖z‖ ≤ 1) ?_ ?_ ?_
    · intro u v hu hv
      exact (IsUltrametricDist.norm_add_le_max u v).trans (max_le hu hv)
    · rw [norm_zero]
      exact zero_le_one
    · intro b _
      rw [norm_mul, ha.2]
      exact mul_le_one₀ (hU1 b) (norm_nonneg _) (hx b)
  have e : twAct act χ i U σ x a = chiC χ i σ * ∑ b, U σ a b * act σ (x b) := by
    simp only [twAct, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
  rw [e, norm_mul, norm_chiC hχ, one_mul]
  exact hs

theorem tw_hinf (hχ : IsCyc χ) (hU : Frame χ K m U g) {h : GQ l} (hh : h ∈ Hinf K)
    (x : Fin r → PadicComplex l) : twAct act χ i U h x = fun a => act h (x a) := by
  have hU1 : U h = 1 := hU.2.2.2.2.1 h hh
  rw [twAct, hU1, Matrix.one_mulVec, chiC_hinf hχ K i hh, one_smul]

theorem tw_mul (ha : IsActC act) (hU : Frame χ K m U g) {σ τ : GQ l} (hσ : σ ∈ Gj K m)
    (hτ : τ ∈ Gj K m) (x : Fin r → PadicComplex l) :
    twAct act χ i U (σ * τ) x = twAct act χ i U σ (twAct act χ i U τ x) := by
  have hσF : σ ∈ (Ks K m).fixingSubgroup := hσ
  have hfix : ∀ a b, act σ (U τ a b) = U τ a b := fun a b => act_inC ha hσF (hU.2.2.1 τ hτ a b).1
  have hc : act σ (chiC χ i τ) = chiC χ i τ := act_algebraMap ha σ _
  have hv : (fun a => act σ (twAct act χ i U τ x a))
      = chiC χ i τ • (U τ).mulVec (fun b => act σ (act τ (x b))) := by
    funext a
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [twAct, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, map_mul, map_sum, hfix, hc]
  have hστ : (fun b => act (σ * τ) (x b)) = fun b => act σ (act τ (x b)) := by
    funext b
    rw [map_mul]
    rfl
  show chiC χ i (σ * τ) • (U (σ * τ)).mulVec (fun b => act (σ * τ) (x b))
    = chiC χ i σ • (U σ).mulVec (fun a => act σ (twAct act χ i U τ x a))
  rw [hv, hστ, chiC_mul, hU.2.2.2.1 σ hσ τ hτ, Matrix.mulVec_smul, ← Matrix.mulVec_mulVec, smul_smul]

theorem tw_cont (ha : IsActC act) (hχ : IsCyc χ) (hU : Frame χ K m U g)
    (x : Fin r → PadicComplex l) : ContinuousOn (fun σ => twAct act χ i U σ x) (Gj K m) := by
  apply continuousOn_pi.2
  intro a
  have h1 : ∀ b, ContinuousOn (fun σ => U σ a b * act σ (x b)) (Gj K m) :=
    fun b => (hU.2.1 a b).mul (IsActC.continuous_orbit l act ha (x b)).continuousOn
  have h2 : ContinuousOn (fun σ => ∑ b, U σ a b * act σ (x b)) (Gj K m) :=
    continuousOn_finsetSum _ (fun b _ => h1 b)
  have h3 : ContinuousOn (fun σ => chiC χ i σ * ∑ b, U σ a b * act σ (x b)) (Gj K m) :=
    (continuous_chiC hχ i).continuousOn.mul h2
  refine h3.congr ?_
  intro σ _
  simp only [twAct, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]

theorem modify (ha : IsActC act) (hχ : IsCyc χ) (hU : Frame χ K m U g) (n : ℕ)
    {c : GQ l → Fin r → PadicComplex l} (hc : CocOn (Gj K m) (twAct act χ i U) (ball l r) c)
    {x : Fin r → PadicComplex l} (hx : x ∈ ball l r) :
    CocOn (Gj K m) (twAct act χ i U) (ball l r)
      (fun σ => (l : PadicComplex l) ^ n • c σ - (twAct act χ i U σ x - x)) := by
  obtain ⟨hcont, hmem, hcoc⟩ := hc
  refine ⟨?_, ?_, ?_⟩
  · have h1 : ContinuousOn (fun σ => ((l : PadicComplex l) ^ n) • c σ) (Gj K m) :=
      (continuousOn_const (c := (l : PadicComplex l) ^ n)).smul hcont
    exact h1.sub ((tw_cont ha hχ hU x).sub continuousOn_const)
  · intro σ hσ
    exact ball_sub (ball_pow n (hmem σ hσ)) (ball_sub (tw_ball ha hχ hU hσ hx) hx)
  · intro σ hσ τ hτ
    simp only
    rw [hcoc σ hσ τ hτ, tw_mul ha hU hσ hτ, tw_sub, tw_sub, tw_pow, smul_add]
    abel

theorem torsion_killed : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ (m r : ℕ), Lev l m → ∀ (U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)) (g : GQ l), Frame χ K m U g → ∀ J : Finset ℤ, HTBasis act χ (Gj K m) U (J : Set ℤ) → ∀ (i : ℤ) (c : GQ l → Fin r → PadicComplex l) (k : ℕ), CocOn (Gj K m) (twAct act χ i U) (ball l r) c → CobOn (Gj K m) (twAct act χ i U) (ball l r) (fun σ => (l : PadicComplex l) ^ k • c σ) → CobOn (Gj K m) (twAct act χ i U) (ball l r) (fun σ => (l : PadicComplex l) ^ (1 + max 1 (∑ u ∈ J.erase i, (m + padicValInt l (u - i)))) • c σ) := by
  intro l hl act χ ha hχ K m r hm U g hU J hJ i c k hc hk
  set N : ℕ := max 1 (∑ u ∈ J.erase i, (m + padicValInt l (u - i))) with hN
  have hHG : ∀ h ∈ Hinf K, h ∈ Gj K m := fun h hh => hinf_le_gj K m hh
  have hgG : g ∈ Gj K m := hU.1.1

  have hHc : CocOn (Hinf K) (fun h y a => act h (y a)) (ball l r) c := by
    refine ⟨hc.1.mono (fun h hh => hHG h hh), fun h hh => hc.2.1 h (hHG h hh), ?_⟩
    intro h hh h' hh'
    rw [hc.2.2 h (hHG h hh) h' (hHG h' hh'), tw_hinf hχ hU hh]

  have hlC : (l : PadicComplex l) ∈ inC (Kinf K) :=
    ⟨algebraMap ℚ_[l] (Om l) (l : ℚ_[l]), IntermediateField.algebraMap_mem _ _,
      (algebraMap_eq (l := l) (l : ℚ_[l])).symm.trans (map_natCast _ l)⟩
  obtain ⟨x1, hx1, hx1e⟩ := GlobalTheory.T.cyclotomic_tate_maximalIdeal_kills_first_cohomology l act ha K r (l : PadicComplex l) hlC norm_l_lt c hHc

  obtain ⟨c1, hc1def⟩ : ∃ c1 : GQ l → Fin r → PadicComplex l,
      c1 = fun σ => (l : PadicComplex l) ^ 1 • c σ - (twAct act χ i U σ x1 - x1) := ⟨_, rfl⟩
  have hc1 : CocOn (Gj K m) (twAct act χ i U) (ball l r) c1 := by
    rw [hc1def]
    exact modify ha hχ hU 1 hc hx1
  have hc1H : ∀ h ∈ Hinf K, c1 h = 0 := by
    intro h hh
    have e := hx1e h hh
    simp only at e
    simp only [hc1def, pow_one, e, tw_hinf hχ hU hh]
    exact sub_self _

  have hw : ∀ a, c1 g a ∈ Ohat K := by
    intro a
    refine (GlobalTheory.T.cyclotomicTower_fixed_iff_mem_completedIntegers l act ha K (c1 g a) (hc1.2.1 g hgG a)).1 ?_
    intro h hh
    have hh' : g⁻¹ * h * g ∈ Hinf K := conj_hinf hχ K m hgG hh
    have e1 : c1 (g * (g⁻¹ * h * g)) = c1 g := by
      rw [hc1.2.2 g hgG _ (hHG _ hh'), hc1H _ hh', tw_zero, add_zero]
    have e2 : c1 (g * (g⁻¹ * h * g)) = fun a => act h (c1 g a) := by
      have e3 : g * (g⁻¹ * h * g) = h * g := by group
      rw [e3, hc1.2.2 h (hHG h hh) g hgG, hc1H h hh, zero_add, tw_hinf hχ hU hh]
    exact congrFun (e2.symm.trans e1) a

  obtain ⟨x0, hx0, hx0e⟩ := hk
  obtain ⟨x2, hx2def⟩ : ∃ x2 : Fin r → PadicComplex l,
      x2 = (l : PadicComplex l) ^ 1 • x0 - (l : PadicComplex l) ^ k • x1 := ⟨_, rfl⟩
  have hx2b : x2 ∈ ball l r := by
    rw [hx2def]
    exact ball_sub (ball_pow 1 hx0) (ball_pow k hx1)
  have hcob1 : ∀ σ ∈ Gj K m, (l : PadicComplex l) ^ k • c1 σ = twAct act χ i U σ x2 - x2 := by
    intro σ hσ
    have e := hx0e σ hσ
    simp only at e
    simp only [hc1def, hx2def]
    rw [tw_sub, tw_pow, tw_pow, smul_sub, smul_sub, smul_comm ((l : PadicComplex l) ^ k) ((l : PadicComplex l) ^ 1) (c σ), e, smul_sub]
    abel
  have hx2O : ∀ a, x2 a ∈ Ohat K := by
    intro a
    refine (GlobalTheory.T.cyclotomicTower_fixed_iff_mem_completedIntegers l act ha K (x2 a) (hx2b a)).1 ?_
    intro h hh
    have e := hcob1 h (hHG h hh)
    rw [hc1H h hh, smul_zero, tw_hinf hχ hU hh] at e
    have e' := congrFun e a
    simp only [Pi.zero_apply, Pi.sub_apply] at e'
    exact sub_eq_zero.1 e'.symm

  obtain ⟨y, hyO, hye⟩ := GlobalTheory.T.torsion_coinvariants_twistedCyclotomicGenerator l act χ ha hχ K m r hm U g hU J hJ i (c1 g) x2 k hw hx2O
    (hcob1 g hgG).symm
  rw [← hN] at hye
  have hyb : y ∈ ball l r := fun a => ohat_norm K (hyO a)
  have hyfix : ∀ h ∈ Hinf K, twAct act χ i U h y = y := by
    intro h hh
    rw [tw_hinf hχ hU hh]
    funext a
    exact (GlobalTheory.T.cyclotomicTower_fixed_iff_mem_completedIntegers l act ha K (y a) (hyb a)).2 (hyO a) h hh

  obtain ⟨d, hddef⟩ : ∃ d : GQ l → Fin r → PadicComplex l,
      d = fun σ => (l : PadicComplex l) ^ N • c1 σ - (twAct act χ i U σ y - y) := ⟨_, rfl⟩
  have hd : CocOn (Gj K m) (twAct act χ i U) (ball l r) d := by
    rw [hddef]
    exact modify ha hχ hU N hc1 hyb
  have hdU : CocOn (Gj K m) (twAct act χ i U) Set.univ d := ⟨hd.1, fun _ _ => Set.mem_univ _, hd.2.2⟩
  have hdH : ∀ h ∈ Hinf K, d h = 0 := by
    intro h hh
    simp only [hddef, hc1H h hh, hyfix h hh, smul_zero, sub_self]
  have hdg : d g = 0 := by
    simp only [hddef]
    rw [hye, sub_self]
  have hd0 := (GlobalTheory.T.cocycle_vanishing_on_fixingSubgroup_determined_by_generator l act χ ha hχ K m r hm U g hU i).1 d hdU hdH hdg

  refine ⟨y + (l : PadicComplex l) ^ N • x1, ball_add hyb (ball_pow N hx1), ?_⟩
  intro σ hσ
  have e1 := hd0 σ hσ
  simp only [hddef, hc1def] at e1
  rw [smul_sub, smul_sub] at e1
  have e2 := sub_eq_zero.1 e1
  have key : (l : PadicComplex l) ^ N • (l : PadicComplex l) ^ 1 • c σ
      = (twAct act χ i U σ y - y)
        + ((l : PadicComplex l) ^ N • twAct act χ i U σ x1 - (l : PadicComplex l) ^ N • x1) := by
    rw [← e2]
    abel
  simp only
  rw [tw_add, tw_pow, pow_add, mul_smul, smul_comm ((l : PadicComplex l) ^ 1) ((l : PadicComplex l) ^ N) (c σ), key]
  abel

end GlobalTheory.Cyc.FrameTorsion
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocycleTwistCoboundaryOnBallStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cocycle_twist_coboundary_on_ball : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ (m r : ℕ), Lev l m → ∀ (U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)) (g : GQ l), Frame χ K m U g → ∀ J : Finset ℤ, HTBasis act χ (Gj K m) U (J : Set ℤ) → ∀ (i : ℤ) (c : GQ l → Fin r → PadicComplex l) (k : ℕ), CocOn (Gj K m) (twAct act χ i U) (ball l r) c → CobOn (Gj K m) (twAct act χ i U) (ball l r) (fun σ => (l : PadicComplex l) ^ k • c σ) → CobOn (Gj K m) (twAct act χ i U) (ball l r) (fun σ => (l : PadicComplex l) ^ (1 + max 1 (∑ u ∈ J.erase i, (m + padicValInt l (u - i)))) • c σ) := by
  first | exact @GlobalTheory.Cyc.FrameTorsion.torsion_killed | exact GlobalTheory.Cyc.FrameTorsion.torsion_killed | (intros; apply GlobalTheory.Cyc.FrameTorsion.torsion_killed <;> assumption)
end
