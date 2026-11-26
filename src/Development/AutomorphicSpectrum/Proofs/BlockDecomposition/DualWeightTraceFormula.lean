module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCompactLieAction
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsHighestWeightHermitianDerivation
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HighestWeightTensorDecomposition
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeUnitaryAction

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsHighestWeightInInvariantSubmodule
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsHighestWeightInInvariantSubmodule
noncomputable section

open Matrix Finset
open scoped InnerProductSpace

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG

namespace GlobalTheory.CompanionTheory.RealCountG.HwStable

variable {n : ℕ}

theorem weight_shift_real {V : Type} [AddCommGroup V] [Module ℂ V] {K : Fin n → Fin n → Module.End ℂ V}
    (hg : Formalism.REAL.GlRel K) (μ : Fin n → ℝ) {v : V}
    (hv : ∀ c, K c c v = ((μ c : ℝ) : ℂ) • v) {a b : Fin n} (hab : a ≠ b) (c : Fin n) :
    K c c (K a b v) =
      ((μ c + (if c = a then 1 else 0) - (if c = b then 1 else 0) : ℝ) : ℂ) • K a b v := by
  have e : K c c (K a b v) = K a b (K c c v) +
      ((if c = a then K c b else 0) - (if b = c then K a c else 0)) v := by
    rw [← hg c c a b]
    simp [Module.End.mul_apply]
  rw [e, hv c, map_smul]
  by_cases h1 : c = a
  · subst h1
    have h2 : ¬ b = c := fun h => hab h.symm
    have h3 : ¬ c = b := hab
    simp only [↓reduceIte, h2, h3, LinearMap.sub_apply, LinearMap.zero_apply]
    push_cast
    module
  · by_cases h2 : c = b
    · subst h2
      simp only [↓reduceIte, h1, LinearMap.sub_apply, LinearMap.zero_apply]
      push_cast
      module
    · have h3 : ¬ b = c := fun h => h2 h.symm
      simp only [↓reduceIte, h1, h2, h3, sub_zero, LinearMap.zero_apply, add_zero]

section Main

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  {G : Fin n → Fin n → Module.End ℂ H} {N : Submodule ℂ H}

def diagOn (G : Fin n → Fin n → Module.End ℂ H) (N : Submodule ℂ H)
    (hst : ∀ a b, ∀ w ∈ N, G a b w ∈ N) (c : Fin n) : Module.End ℂ N :=
  (G c c).restrict (hst c c)

theorem diagOn_symm (hs : ∀ a b (x y : H), ⟪G a b x, y⟫_ℂ = ⟪x, G b a y⟫_ℂ)
    (hst : ∀ a b, ∀ w ∈ N, G a b w ∈ N) (c : Fin n) : (diagOn G N hst c).IsSymmetric := by
  intro x y
  exact hs c c x.1 y.1

theorem diag_commute (hg : Formalism.REAL.GlRel G) (i j : Fin n) : Commute (G i i) (G j j) := by
  have h := hg i i j j
  by_cases hij : i = j
  · subst hij
    exact Commute.refl _
  · have h' : ¬ j = i := fun h => hij h.symm
    rw [if_neg hij, if_neg h', sub_zero] at h
    exact sub_eq_zero.1 h

theorem diagOn_commute (hg : Formalism.REAL.GlRel G) (hst : ∀ a b, ∀ w ∈ N, G a b w ∈ N) (i j : Fin n) :
    Commute (diagOn G N hst i) (diagOn G N hst j) := by
  have h : G i i * G j j = G j j * G i i := diag_commute hg i j
  show diagOn G N hst i * diagOn G N hst j = diagOn G N hst j * diagOn G N hst i
  ext x
  have := congrArg (fun f : Module.End ℂ H => f x.1) h
  simpa [diagOn, Module.End.mul_apply] using this

def wts (G : Fin n → Fin n → Module.End ℂ H) (N : Submodule ℂ H) : Set (Fin n → ℝ) :=
  {μ | ∃ v ∈ N, v ≠ 0 ∧ ∀ c, G c c v = ((μ c : ℝ) : ℂ) • v}

theorem wts_nonempty (hg : Formalism.REAL.GlRel G) (hs : ∀ a b (x y : H), ⟪G a b x, y⟫_ℂ = ⟪x, G b a y⟫_ℂ)
    (hN : N ≠ ⊥) (hst : ∀ a b, ∀ w ∈ N, G a b w ∈ N) : (wts G N).Nonempty := by
  have htop := LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute (fun c => diagOn_symm hs hst c)
    (fun i j _ => diagOn_commute hg hst i j)
  haveI : Nontrivial N := Submodule.nontrivial_iff_ne_bot.2 hN
  obtain ⟨χ, hχ⟩ : ∃ χ : Fin n → ℂ, (⨅ c, Module.End.eigenspace (diagOn G N hst c) (χ c)) ≠ ⊥ := by
    by_contra hcon
    push_neg at hcon
    rw [iSup_congr hcon, iSup_bot] at htop
    exact bot_ne_top htop
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hχ
  have hev : ∀ c, diagOn G N hst c x = χ c • x := fun c =>
    Module.End.mem_eigenspace_iff.1 ((Submodule.mem_iInf _).1 hx c)
  have hre : ∀ c, (((χ c).re : ℝ) : ℂ) = χ c := fun c => by
    have hE : Module.End.HasEigenvalue (diagOn G N hst c) (χ c) :=
      Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 (hev c), hx0⟩
    exact Complex.conj_eq_iff_re.1 ((diagOn_symm hs hst c).conj_eigenvalue_eq_self hE)
  refine ⟨fun c => (χ c).re, x.1, x.2, fun h => hx0 (Subtype.ext h), fun c => ?_⟩
  rw [hre c]
  exact congrArg Subtype.val (hev c)

theorem wts_finite (hst : ∀ a b, ∀ w ∈ N, G a b w ∈ N) : (wts G N).Finite := by
  have hfa : ∀ a, Set.Finite {r : ℝ | Module.End.HasEigenvalue (diagOn G N hst a) ((r : ℝ) : ℂ)} := fun a =>
    (Module.End.finite_hasEigenvalue _).preimage (Function.Injective.injOn Complex.ofReal_injective)
  refine (Set.Finite.pi' hfa).subset ?_
  rintro μ ⟨v, hv, h0, hw⟩ a
  exact Module.End.hasEigenvalue_of_hasEigenvector (x := (⟨v, hv⟩ : N))
    ⟨Module.End.mem_eigenspace_iff.2 (Subtype.ext (hw a)), fun h => h0 (congrArg Subtype.val h)⟩

end Main

theorem exists_highest_of_stable : ∀ {n : ℕ} (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] (G : Fin n → Fin n → Module.End ℂ H), Formalism.REAL.GlRel G →
    (∀ a b (x y : H), ⟪G a b x, y⟫_ℂ = ⟪x, G b a y⟫_ℂ) → ∀ N : Submodule ℂ H, N ≠ ⊥ →
    (∀ a b, ∀ w ∈ N, G a b w ∈ N) →
    ∃ (μ : Fin n → ℝ) (v : H), v ∈ N ∧ v ≠ 0 ∧ Formalism.REAL.KHighest (fun _ => true) G μ v := by
  intro n H _ _ _ G hg hs N hN hst
  have hfin := wts_finite hst
  obtain ⟨μ, hμ, hmax⟩ := hfin.toFinset.exists_max_image (fun ν => toLex ν)
    (by simpa using wts_nonempty hg hs hN hst)
  obtain ⟨v, hvN, hv0, hw⟩ := hfin.mem_toFinset.1 hμ
  refine ⟨μ, v, hvN, hv0, hw, fun a b hab _ => ?_⟩
  by_contra hne
  let μ' : Fin n → ℝ := fun c => μ c + (if c = a then 1 else 0) - (if c = b then 1 else 0)
  have hlt : toLex μ < toLex μ' := by
    refine ⟨a, fun j hj => ?_, ?_⟩
    · have h1 : j ≠ a := ne_of_lt hj
      have h2 : j ≠ b := ne_of_lt (lt_trans hj hab)
      show μ j = μ j + (if j = a then 1 else 0) - (if j = b then 1 else 0)
      simp [h1, h2]
    · show μ a < μ a + (if a = a then 1 else 0) - (if a = b then 1 else 0)
      simp [ne_of_lt hab]
  have hin : μ' ∈ wts G N :=
    ⟨G a b v, hst a b v hvN, hne, fun c => weight_shift_real hg μ hw (ne_of_lt hab) c⟩
  exact not_le.2 hlt (hmax μ' (hfin.mem_toFinset.2 hin))

end GlobalTheory.CompanionTheory.RealCountG.HwStable
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsHighestWeightInInvariantSubmoduleStatement
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_highest_weight_in_invariant_submodule : ∀ {n : ℕ} (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (G : Fin n → Fin n → Module.End ℂ H), Formalism.REAL.GlRel G → (∀ a b (x y : H), ⟪G a b x, y⟫_ℂ = ⟪x, G b a y⟫_ℂ) → ∀ N : Submodule ℂ H, N ≠ ⊥ → (∀ a b, ∀ w ∈ N, G a b w ∈ N) → ∃ (μ : Fin n → ℝ) (v : H), v ∈ N ∧ v ≠ 0 ∧ Formalism.REAL.KHighest (fun _ => true) G μ v := by
  first | exact @GlobalTheory.CompanionTheory.RealCountG.HwStable.exists_highest_of_stable | exact GlobalTheory.CompanionTheory.RealCountG.HwStable.exists_highest_of_stable | (intros; apply GlobalTheory.CompanionTheory.RealCountG.HwStable.exists_highest_of_stable <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntertwinerEqZeroOfVanishOnHighest
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntertwinerEqZeroOfVanishOnHighest
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG

namespace GlobalTheory.CompanionTheory.RealCountG

theorem intertwiner_eq_zero_of_highest {n : ℕ} (H V : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [AddCommGroup V] [Module ℂ V]
    (G : Fin n → Fin n → Module.End ℂ H) (D : Fin n → Fin n → Module.End ℂ V)
    (hrel : Formalism.REAL.GlRel G)
    (hadj : ∀ a b (x y : H), ⟪G a b x, y⟫_ℂ = ⟪x, G b a y⟫_ℂ)
    (R : H →ₗ[ℂ] V) (hR : ∀ a b w, R (G a b w) = D a b (R w))
    (hhigh : ∀ (μ : Fin n → ℝ) (v : H), Formalism.REAL.KHighest (fun _ => true) G μ v → R v = 0) :
    R = 0 := by
  by_contra hne
  have hKtop : LinearMap.ker R ≠ ⊤ := fun h => hne (LinearMap.ker_eq_top.mp h)
  have hN : (LinearMap.ker R)ᗮ ≠ ⊥ := fun h =>
    hKtop ((Submodule.orthogonal_eq_bot_iff).mp h)
  have hstable : ∀ a b, ∀ w ∈ (LinearMap.ker R)ᗮ, G a b w ∈ (LinearMap.ker R)ᗮ := by
    intro a b w hw
    rw [Submodule.mem_orthogonal]
    intro u hu
    have hu' : G b a u ∈ LinearMap.ker R := by
      rw [LinearMap.mem_ker] at hu ⊢
      rw [hR, hu, map_zero]
    rw [← hadj]
    exact (Submodule.mem_orthogonal _ _).mp hw _ hu'
  obtain ⟨μ, v, hvN, hv0, hk⟩ := GlobalTheory.T.exists_highest_weight_in_invariant_submodule H G hrel hadj _ hN hstable
  have hvK : v ∈ LinearMap.ker R := hhigh μ v hk
  exact hv0 (inner_self_eq_zero.mp ((Submodule.mem_orthogonal _ _).mp hvN v hvK))

end GlobalTheory.CompanionTheory.RealCountG
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntertwinerEqZeroOfVanishOnHighestStatement
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intertwiner_eq_zero_of_vanish_on_highest : ∀ {n : ℕ} (H V : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [AddCommGroup V] [Module ℂ V] (G : Fin n → Fin n → Module.End ℂ H) (D : Fin n → Fin n → Module.End ℂ V), Formalism.REAL.GlRel G → (∀ a b (x y : H), ⟪G a b x, y⟫_ℂ = ⟪x, G b a y⟫_ℂ) → ∀ R : H →ₗ[ℂ] V, (∀ a b w, R (G a b w) = D a b (R w)) → (∀ (μ : Fin n → ℝ) (v : H), Formalism.REAL.KHighest (fun _ => true) G μ v → R v = 0) → R = 0 := by
  first | exact @GlobalTheory.CompanionTheory.RealCountG.intertwiner_eq_zero_of_highest | exact GlobalTheory.CompanionTheory.RealCountG.intertwiner_eq_zero_of_highest | (intros; apply GlobalTheory.CompanionTheory.RealCountG.intertwiner_eq_zero_of_highest <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HighestWeightIntegralOfUnitary
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HighestWeightIntegralOfUnitary
noncomputable section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG

namespace GlobalTheory.CompanionTheory.RealCountG.Isotypic

variable {n : ℕ}

theorem exists_map_out (H L : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    [NormedAddCommGroup L] [InnerProductSpace ℂ L] [FiniteDimensional ℂ L]
    (G : Fin n → Fin n → Module.End ℂ H) (K : Fin n → Fin n → Module.End ℂ L) (μ : Fin n → ℝ)
    (hG : Formalism.REAL.GlRel G) (hK : Formalism.REAL.GlRel K)
    (hGs : ∀ a b (x y : H), ⟪G a b x, y⟫_ℂ = ⟪x, G b a y⟫_ℂ)
    (hKs : ∀ a b (x y : L), ⟪K a b x, y⟫_ℂ = ⟪x, K b a y⟫_ℂ)
    (v : L) (hv0 : v ≠ 0) (hv : Formalism.REAL.KHighest (fun _ => true) K μ v)
    (d : H) (hd : Formalism.REAL.KHighest (fun _ => true) G μ d) :
    ∃ T : L →ₗ[ℂ] H, T v = d ∧ ∀ a b w, T (K a b w) = G a b (T w) := by
  have hsp : ∀ x ∈ Submodule.span ℂ {v}, Formalism.REAL.KHighest (fun _ => true) K μ x := by
    intro x hx
    have hvm : v ∈ hwOf K μ := hv
    have : x ∈ hwOf K μ := (Submodule.span_singleton_le_iff_mem v (hwOf K μ)).2 hvm hx
    exact this
  let f : (Submodule.span ℂ {v}) →ₗ[ℂ] H :=
    ((innerₛₗ ℂ v).comp (Submodule.subtype _)).smulRight ((⟪v, v⟫_ℂ)⁻¹ • d)
  have hf : ∀ x, Formalism.REAL.KHighest (fun _ => true) G μ (f x) := by
    intro x
    have hdm : d ∈ hwOf G μ := hd
    have : f x ∈ hwOf G μ := by
      simp only [f, LinearMap.smulRight_apply]
      exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hdm)
    exact this
  obtain ⟨T, hT, hi⟩ := GlobalTheory.T.highest_weight_tensor_decomposition L H K G μ hK hG hKs hGs (Submodule.span ℂ {v}) hsp f hf
  refine ⟨T, ?_, hi⟩
  have hvv : ⟪v, v⟫_ℂ ≠ 0 := inner_self_ne_zero.2 hv0
  have := hT ⟨v, Submodule.mem_span_singleton_self v⟩
  simp only at this
  rw [this]
  simp only [f, LinearMap.smulRight_apply, LinearMap.comp_apply, Submodule.subtype_apply, innerₛₗ_apply_apply]
  rw [smul_smul, mul_inv_cancel₀ hvv, one_smul]

theorem exists_map_in (H L : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    [NormedAddCommGroup L] [InnerProductSpace ℂ L]
    (G : Fin n → Fin n → Module.End ℂ H) (K : Fin n → Fin n → Module.End ℂ L) (μ : Fin n → ℝ)
    (hG : Formalism.REAL.GlRel G) (hK : Formalism.REAL.GlRel K)
    (hGs : ∀ a b (x y : H), ⟪G a b x, y⟫_ℂ = ⟪x, G b a y⟫_ℂ)
    (hKs : ∀ a b (x y : L), ⟪K a b x, y⟫_ℂ = ⟪x, K b a y⟫_ℂ)
    (v : L) (hv : Formalism.REAL.KHighest (fun _ => true) K μ v)
    (D : Submodule ℂ H) (hD : ∀ x ∈ D, Formalism.REAL.KHighest (fun _ => true) G μ x) (φ : D →ₗ[ℂ] ℂ) :
    ∃ P : H →ₗ[ℂ] L, (∀ d : D, P d = φ d • v) ∧ ∀ a b w, P (G a b w) = K a b (P w) := by
  have hf : ∀ x, Formalism.REAL.KHighest (fun _ => true) K μ (φ.smulRight v x) := by
    intro x
    have hvm : v ∈ hwOf K μ := hv
    have : φ.smulRight v x ∈ hwOf K μ := by
      simp only [LinearMap.smulRight_apply]
      exact Submodule.smul_mem _ _ hvm
    exact this
  obtain ⟨P, hP, hi⟩ := GlobalTheory.T.highest_weight_tensor_decomposition H L G K μ hG hK hGs hKs D hD (φ.smulRight v) hf
  exact ⟨P, fun d => by rw [hP d, LinearMap.smulRight_apply], hi⟩

theorem eq_smul_id_of_apply (L : Type) [NormedAddCommGroup L] [InnerProductSpace ℂ L] [FiniteDimensional ℂ L]
    (K : Fin n → Fin n → Module.End ℂ L) (hK : Formalism.REAL.GlRel K)
    (hKs : ∀ a b (x y : L), ⟪K a b x, y⟫_ℂ = ⟪x, K b a y⟫_ℂ) (v : L)
    (huniq : ∀ w : L, (∀ a b, a < b → K a b w = 0) → ∃ c : ℂ, w = c • v)
    (R : L →ₗ[ℂ] L) (hR : ∀ a b w, R (K a b w) = K a b (R w)) (r : ℂ) (hr : R v = r • v) :
    R = r • LinearMap.id := by
  have h0 := GlobalTheory.T.intertwiner_eq_zero_of_vanish_on_highest L L K K hK hKs (R - r • LinearMap.id)
    (fun a b w => by simp [hR, map_smul]) (fun μ w hw => by
      obtain ⟨c, rfl⟩ := huniq w (fun a b hab => hw.2 a b hab rfl)
      simp [hr, smul_comm c r])
  exact sub_eq_zero.1 h0

theorem map_highest_eq_zero {H L : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup L] [Module ℂ L]
    (G : Fin n → Fin n → Module.End ℂ H) (K : Fin n → Fin n → Module.End ℂ L) (μ μ' : Fin n → ℝ)
    (v : L) (hv0 : v ≠ 0) (hv : Formalism.REAL.KHighest (fun _ => true) K μ' v)
    (huniq : ∀ w : L, (∀ a b, a < b → K a b w = 0) → ∃ c : ℂ, w = c • v)
    (P : H →ₗ[ℂ] L) (hP : ∀ a b w, P (G a b w) = K a b (P w))
    (hne : μ ≠ μ') (w : H) (hw : Formalism.REAL.KHighest (fun _ => true) G μ w) : P w = 0 := by
  obtain ⟨c, hc⟩ := huniq (P w) (fun a b hab => by rw [← hP, hw.2 a b hab rfl, map_zero])
  by_contra hne0
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hne0 (by simpa using hc)
  apply hne
  funext a
  have h1 : K a a (P w) = (μ a : ℂ) • P w := by rw [← hP, hw.1 a, map_smul]
  rw [hc, map_smul, hv.1 a, smul_comm] at h1
  have h2 : ((μ' a : ℂ) - (μ a : ℂ)) • (c • v) = 0 := by rw [sub_smul, h1, sub_self]
  have h3 : (μ' a : ℂ) - (μ a : ℂ) = 0 := by
    rcases smul_eq_zero.1 h2 with h | h
    · exact h
    · exact absurd h (smul_ne_zero hc0 hv0)
  have h4 : (μ' a : ℂ) = (μ a : ℂ) := sub_eq_zero.1 h3
  exact (Complex.ofReal_injective h4).symm

theorem map_mem_hwOf {H : Type} [AddCommGroup H] [Module ℂ H]
    (G : Fin n → Fin n → Module.End ℂ H) (μ : Fin n → ℝ) (S : H →ₗ[ℂ] H)
    (hS : ∀ a b w, S (G a b w) = G a b (S w)) (x : H) (hx : x ∈ hwOf G μ) : S x ∈ hwOf G μ :=
  ⟨fun a => by rw [← hS, hx.1 a, map_smul],
    fun a b hab he => by rw [← hS, hx.2 a b hab he, map_zero]⟩

theorem exists_isotypic_projection {n : ℕ} (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] (ρ : Matrix.unitaryGroup (Fin n) ℂ →* (H →L[ℂ] H))
    (G : Fin n → Fin n → Module.End ℂ H) (ν : Fin n → ℤ) :
    Formalism.REAL.GlRel G → (∀ a b (x y : H), ⟪G a b x, y⟫_ℂ = ⟪x, G b a y⟫_ℂ) →
    (∀ (X : Matrix (Fin n) (Fin n) ℂ) (γ : ℝ → Matrix.unitaryGroup (Fin n) ℂ), Xᴴ = -X →
      (∀ t : ℝ, (γ t).1 = NormedSpace.exp ((t : ℂ) • X)) →
      ∀ w : H, HasDerivAt (fun t : ℝ => ρ (γ t) w) (∑ a, ∑ b, X a b • G a b w) 0) →
    Antitone ν →
    ∃ p : H →ₗ[ℂ] H, (∀ a b w, p (G a b w) = G a b (p w)) ∧ (∀ v ∈ hwOf G (wtR ν), p v = v) ∧
      (∀ (μ : Fin n → ℝ) (v : H), μ ≠ wtR ν → Formalism.REAL.KHighest (fun _ => true) G μ v → p v = 0) ∧
      ∀ S : H →ₗ[ℂ] H, (∀ a b w, S (G a b w) = G a b (S w)) →
        ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (z : Fin n → ℂ), k.1 = diagonal z → Function.Injective z →
          LinearMap.trace ℂ H ((ρ k : H →ₗ[ℂ] H) ∘ₗ S ∘ₗ p) = trOn (hwOf G (wtR ν)) S * weylChar ν z := by
  intro hG hGs hder hν
  obtain ⟨L, _, _, _, σ, K, v, hK, hKs, hσ, hv0, hv, huniq, htr⟩ := GlobalTheory.T.exists_highest_weight_hermitian_derivation ν hν
  have hD : ∀ x ∈ hwOf G (wtR ν), Formalism.REAL.KHighest (fun _ => true) G (wtR ν) x := fun x hx => hx
  let b := Module.finBasis ℂ (hwOf G (wtR ν))
  have ex1 : ∀ j, ∃ T : L →ₗ[ℂ] H, T v = (b j : H) ∧ ∀ a c w, T (K a c w) = G a c (T w) := fun j =>
    exists_map_out H L G K (wtR ν) hG hK hGs hKs v hv0 hv (b j : H) (b j).2
  choose T hTv hTi using ex1
  have ex2 : ∀ j, ∃ P : H →ₗ[ℂ] L, (∀ d : hwOf G (wtR ν), P d = b.coord j d • v) ∧
      ∀ a c w, P (G a c w) = K a c (P w) := fun j =>
    exists_map_in H L G K (wtR ν) hG hK hGs hKs v hv _ hD (b.coord j)
  choose P hPd hPi using ex2
  have hPk : ∀ j k w, P j (ρ k w) = σ k (P j w) := fun j =>
    GlobalTheory.T.derivative_unitary_action H L ρ G hder σ K hσ hKs (P j) (hPi j)
  have hp : ∀ w, (∑ j, T j ∘ₗ P j) w = ∑ j, T j (P j w) := fun w => by
    simp [LinearMap.sum_apply]
  refine ⟨∑ j, T j ∘ₗ P j, ?_, ?_, ?_, ?_⟩
  · intro a c w
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hp, hp, map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [hPi, hTi]
  · intro d hd
    rw [hp]
    have h1 : ∀ j, T j (P j d) = b.coord j ⟨d, hd⟩ • (b j : H) := fun j => by
      have := hPd j ⟨d, hd⟩
      simp only at this
      rw [this, map_smul, hTv]
    simp only [h1]
    have h2 : ∑ j, b.coord j ⟨d, hd⟩ • b j = ⟨d, hd⟩ := b.sum_repr _
    calc ∑ j, b.coord j ⟨d, hd⟩ • (b j : H)
        = ((∑ j, b.coord j ⟨d, hd⟩ • b j : hwOf G (wtR ν)) : H) := by
          simp only [Submodule.coe_sum, Submodule.coe_smul]
      _ = d := by rw [h2]
  · intro μ w hne hw
    rw [hp]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [map_highest_eq_zero G K μ (wtR ν) v hv0 hv huniq (P j) (hPi j) hne w hw, map_zero]
  · intro S hS k z hk hz
    have hSD : ∀ x ∈ hwOf G (wtR ν), S x ∈ hwOf G (wtR ν) := map_mem_hwOf G (wtR ν) S hS
    have hj : ∀ j, LinearMap.trace ℂ H ((ρ k : H →ₗ[ℂ] H) ∘ₗ S ∘ₗ (T j ∘ₗ P j)) =
        b.coord j ⟨S (b j), hSD _ (b j).2⟩ * weylChar ν z := by
      intro j
      have hR : P j ∘ₗ S ∘ₗ T j = b.coord j ⟨S (b j), hSD _ (b j).2⟩ • LinearMap.id := by
        refine eq_smul_id_of_apply L K hK hKs v huniq _ (fun a c w => ?_) _ ?_
        · simp only [LinearMap.comp_apply]
          rw [hTi, hS, hPi]
        · simp only [LinearMap.comp_apply]
          rw [hTv]
          exact hPd j ⟨S (b j), hSD _ (b j).2⟩
      have e1 : (ρ k : H →ₗ[ℂ] H) ∘ₗ S ∘ₗ (T j ∘ₗ P j) = ((ρ k : H →ₗ[ℂ] H) ∘ₗ S ∘ₗ T j) ∘ₗ P j := rfl
      have e2 : P j ∘ₗ ((ρ k : H →ₗ[ℂ] H) ∘ₗ S ∘ₗ T j) = σ k ∘ₗ (P j ∘ₗ S ∘ₗ T j) := by
        ext w
        simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
        exact hPk j k _
      rw [e1, LinearMap.trace_comp_comm', e2, hR, LinearMap.comp_smul, LinearMap.comp_id, map_smul,
        htr k z hk hz, smul_eq_mul]
    have hsum : (ρ k : H →ₗ[ℂ] H) ∘ₗ S ∘ₗ (∑ j, T j ∘ₗ P j) =
        ∑ j, (ρ k : H →ₗ[ℂ] H) ∘ₗ S ∘ₗ (T j ∘ₗ P j) := by
      ext w
      set_option synthInstance.maxHeartbeats 100000 in
        simp [LinearMap.sum_apply, map_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hsum, map_sum, Finset.sum_congr rfl fun j _ => hj j, ← Finset.sum_mul]
    congr 1
    unfold trOn
    rw [dite_eq_left hSD, LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
    rfl

end GlobalTheory.CompanionTheory.RealCountG.Isotypic
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HighestWeightIntegralOfUnitaryStatement
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG
theorem _root_.GlobalTheory.T.highest_weight_integral_of_unitary : ∀ {n : ℕ} (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (ρ : Matrix.unitaryGroup (Fin n) ℂ →* (H →L[ℂ] H)) (G : Fin n → Fin n → Module.End ℂ H) (ν : Fin n → ℤ), Formalism.REAL.GlRel G → (∀ a b (x y : H), ⟪G a b x, y⟫_ℂ = ⟪x, G b a y⟫_ℂ) → (∀ (X : Matrix (Fin n) (Fin n) ℂ) (γ : ℝ → Matrix.unitaryGroup (Fin n) ℂ), Xᴴ = -X → (∀ t : ℝ, (γ t).1 = NormedSpace.exp ((t : ℂ) • X)) → ∀ w : H, HasDerivAt (fun t : ℝ => ρ (γ t) w) (∑ a, ∑ b, X a b • G a b w) 0) → Antitone ν → ∃ p : H →ₗ[ℂ] H, (∀ a b w, p (G a b w) = G a b (p w)) ∧ (∀ v ∈ hwOf G (wtR ν), p v = v) ∧ (∀ (μ : Fin n → ℝ) (v : H), μ ≠ wtR ν → Formalism.REAL.KHighest (fun _ => true) G μ v → p v = 0) ∧ ∀ S : H →ₗ[ℂ] H, (∀ a b w, S (G a b w) = G a b (S w)) → ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (z : Fin n → ℂ), k.1 = diagonal z → Function.Injective z → LinearMap.trace ℂ H ((ρ k : H →ₗ[ℂ] H) ∘ₗ S ∘ₗ p) = trOn (hwOf G (wtR ν)) S * weylChar ν z := by
  exact @GlobalTheory.CompanionTheory.RealCountG.Isotypic.exists_isotypic_projection
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HighestWeightOfUnitaryDerivative
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HighestWeightOfUnitaryDerivative
noncomputable section

open Matrix Finset
open scoped InnerProductSpace

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG GlobalTheory.CompanionTheory.RealCount.InjHw

namespace GlobalTheory.CompanionTheory.RealCountG.WtInt

variable {n : ℕ}

theorem expU_add (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) (s t : ℝ) :
    expU X hX (s + t) = expU X hX s * expU X hX t := by
  apply Subtype.ext
  show NormedSpace.exp (((s + t : ℝ) : ℂ) • X) = NormedSpace.exp ((s : ℂ) • X) * NormedSpace.exp ((t : ℂ) • X)
  rw [Complex.ofReal_add, add_smul, Matrix.exp_add_of_commute]
  exact ((Commute.refl X).smul_left _).smul_right _

theorem expU_two_pi (a : Fin n) (hX : (Matrix.single a a Complex.I)ᴴ = -(Matrix.single a a Complex.I)) :
    expU (Matrix.single a a Complex.I) hX (2 * Real.pi) = 1 := by
  apply Subtype.ext
  show NormedSpace.exp (((2 * Real.pi : ℝ) : ℂ) • (Matrix.single a a Complex.I : Matrix (Fin n) (Fin n) ℂ)) = 1
  have e : (((2 * Real.pi : ℝ) : ℂ)) • (Matrix.single a a Complex.I : Matrix (Fin n) (Fin n) ℂ) =
      diagonal (fun c => if c = a then ((2 * Real.pi : ℝ) : ℂ) * Complex.I else 0) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      by_cases hc : i = a
      · subst hc
        simp
      · simp [Matrix.single_apply, hc, Ne.symm hc]
    · rw [Matrix.diagonal_apply_ne _ hij, Matrix.smul_apply, Matrix.single_apply,
        if_neg (fun hh => hij (hh.1.symm.trans hh.2)), smul_zero]
  rw [e, Matrix.exp_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext c
  have hh : NormedSpace.exp (fun c => if c = a then ((2 * Real.pi : ℝ) : ℂ) * Complex.I else 0) c =
      if c = a then Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I) else 1 := by
    split_ifs with hc <;> simp [hc, Complex.exp_eq_exp_ℂ]
  rw [hh]
  have h2 : Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I) = 1 := by
    push_cast
    exact Complex.exp_two_pi_mul_I
  rw [h2]
  simp

theorem eigen_int (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ρ : Matrix.unitaryGroup (Fin n) ℂ →* (H →L[ℂ] H)) (G : Fin n → Fin n → Module.End ℂ H)
    (hd : ∀ (X : Matrix (Fin n) (Fin n) ℂ) (γ : ℝ → Matrix.unitaryGroup (Fin n) ℂ), Xᴴ = -X →
      (∀ t : ℝ, (γ t).1 = NormedSpace.exp ((t : ℂ) • X)) → ∀ w : H,
      HasDerivAt (fun t : ℝ => ρ (γ t) w) (∑ a, ∑ b, X a b • G a b w) 0)
    (a : Fin n) (r : ℝ) {v : H} (hv : v ≠ 0) (hr : G a a v = (r : ℂ) • v) : ∃ m : ℤ, r = m := by
  have hX : (Matrix.single a a Complex.I)ᴴ = -(Matrix.single a a Complex.I) := by
    rw [single_conjT, Complex.star_def, Complex.conj_I, single_negI]
  set X : Matrix (Fin n) (Fin n) ℂ := Matrix.single a a Complex.I with hXdef
  set φ : ℝ → H := fun s => ρ (expU X hX s) v with hφ
  have hd0 : HasDerivAt φ ((Complex.I * r) • v) 0 := by
    have := hd X (expU X hX) hX (fun _ => rfl) v
    have e := sum_single (Kf := G) v a a Complex.I
    rw [← hXdef] at e
    rw [e, hr, smul_smul] at this
    exact this
  have hstep : ∀ s, HasDerivAt φ ((Complex.I * r) • φ s) s := by
    intro s
    let L : H →L[ℝ] H := (ρ (expU X hX s)).restrictScalars ℝ
    have hL : ∀ y, L y = ρ (expU X hX s) y := fun _ => rfl
    have h1 : HasDerivAt (fun t => L (φ t)) (L ((Complex.I * r) • v)) 0 :=
      L.hasFDerivAt.comp_hasDerivAt 0 hd0
    have h2 : HasDerivAt (fun t => L (φ t)) (L ((Complex.I * r) • v)) (s - s) := by
      rwa [sub_self]
    have h3 := h2.comp_sub_const s s
    have e : (fun t => L (φ (t - s))) = φ := by
      funext t
      have : expU X hX t = expU X hX s * expU X hX (t - s) := by
        rw [← expU_add]
        congr 1
        ring
      simp only [hL, hφ, this, map_mul, ContinuousLinearMap.mul_apply]
    rw [e] at h3
    have e2 : L ((Complex.I * r) • v) = (Complex.I * r) • φ s := by
      rw [hL, map_smul]
    rwa [e2] at h3
  set ψ : ℝ → H := fun s => Complex.exp ((s : ℂ) * (-(Complex.I * r))) • φ s with hψ
  have hψd : ∀ s, HasDerivAt ψ 0 s := by
    intro s
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * (-(Complex.I * r))) (-(Complex.I * r)) s := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := s)).mul_const (-(Complex.I * (r : ℂ)))
    have h2 := h1.cexp
    have h3 := h2.smul (hstep s)
    have : Complex.exp ((s : ℂ) * (-(Complex.I * r))) • (Complex.I * r) • φ s +
        (Complex.exp ((s : ℂ) * (-(Complex.I * r))) * -(Complex.I * r)) • φ s = 0 := by
      rw [smul_smul, ← add_smul]
      simp
    rw [this] at h3
    exact h3
  have hconst : ψ (2 * Real.pi) = ψ 0 :=
    is_const_of_deriv_eq_zero (fun s => (hψd s).differentiableAt) (fun s => (hψd s).deriv) _ _
  have h0 : φ 0 = v := by
    have : expU X hX 0 = 1 := by
      apply Subtype.ext
      show NormedSpace.exp (((0 : ℝ) : ℂ) • X) = 1
      simp
    simp [hφ, this]
  have h2π : φ (2 * Real.pi) = v := by
    show ρ (expU X hX (2 * Real.pi)) v = v
    rw [show expU X hX (2 * Real.pi) = 1 from expU_two_pi a hX, map_one]
    rfl
  have hE : Complex.exp (((2 * Real.pi : ℝ) : ℂ) * (-(Complex.I * r))) • v = v := by
    have b : ψ 0 = v := by simp [hψ, h0]
    have a' : ψ (2 * Real.pi) = Complex.exp (((2 * Real.pi : ℝ) : ℂ) * (-(Complex.I * r))) • v := by
      show Complex.exp (((2 * Real.pi : ℝ) : ℂ) * (-(Complex.I * r))) • φ (2 * Real.pi) = _
      rw [h2π]
    rw [← a', hconst, b]
  have hE1 : Complex.exp (((2 * Real.pi : ℝ) : ℂ) * (-(Complex.I * r))) = 1 := by
    have : (Complex.exp (((2 * Real.pi : ℝ) : ℂ) * (-(Complex.I * r))) - 1) • v = 0 := by
      rw [sub_smul, hE, one_smul, sub_self]
    rcases smul_eq_zero.1 this with h' | h'
    · exact sub_eq_zero.1 h'
    · exact absurd h' hv
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.1 hE1
  refine ⟨-m, ?_⟩
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h5 : (r : ℂ) = ((-m : ℤ) : ℂ) := by
    push_cast at hm ⊢
    have h6 : (2 * (Real.pi : ℂ) * Complex.I) * ((r : ℂ) + m) = 0 := by
      linear_combination -hm
    have h7 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      simp [hpi, Complex.I_ne_zero]
    have := (mul_eq_zero.1 h6).resolve_left h7
    linear_combination this
  exact_mod_cast h5

theorem weight_integral : ∀ {n : ℕ} (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (ρ : Matrix.unitaryGroup (Fin n) ℂ →* (H →L[ℂ] H)) (G : Fin n → Fin n → Module.End ℂ H), (∀ (X : Matrix (Fin n) (Fin n) ℂ) (γ : ℝ → Matrix.unitaryGroup (Fin n) ℂ), Xᴴ = -X → (∀ t : ℝ, (γ t).1 = NormedSpace.exp ((t : ℂ) • X)) → ∀ w : H, HasDerivAt (fun t : ℝ => ρ (γ t) w) (∑ a, ∑ b, X a b • G a b w) 0) → ∀ (μ : Fin n → ℝ) (v : H), v ≠ 0 → Formalism.REAL.IsWeight G μ v → ∃ ν : Fin n → ℤ, μ = wtR ν := by
  intro n H _ _ _ ρ G hd μ v hv hw
  choose ν hν using fun a => eigen_int H ρ G hd a (μ a) hv (hw a)
  exact ⟨ν, funext hν⟩

end GlobalTheory.CompanionTheory.RealCountG.WtInt
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HighestWeightOfUnitaryDerivativeStatement
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.highest_weight_of_unitary_derivative : ∀ {n : ℕ} (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (ρ : Matrix.unitaryGroup (Fin n) ℂ →* (H →L[ℂ] H)) (G : Fin n → Fin n → Module.End ℂ H), (∀ (X : Matrix (Fin n) (Fin n) ℂ) (γ : ℝ → Matrix.unitaryGroup (Fin n) ℂ), Xᴴ = -X → (∀ t : ℝ, (γ t).1 = NormedSpace.exp ((t : ℂ) • X)) → ∀ w : H, HasDerivAt (fun t : ℝ => ρ (γ t) w) (∑ a, ∑ b, X a b • G a b w) 0) → ∀ (μ : Fin n → ℝ) (v : H), v ≠ 0 → Formalism.REAL.IsWeight G μ v → ∃ ν : Fin n → ℤ, μ = wtR ν := by
  first | exact @GlobalTheory.CompanionTheory.RealCountG.WtInt.weight_integral | exact GlobalTheory.CompanionTheory.RealCountG.WtInt.weight_integral | (intros; apply GlobalTheory.CompanionTheory.RealCountG.WtInt.weight_integral <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualWeightTraceFormula
noncomputable section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG

namespace GlobalTheory.CompanionTheory.RealCountG.CharDec

variable {n : ℕ}

theorem core (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (ρ : Matrix.unitaryGroup (Fin n) ℂ →* (H →L[ℂ] H)) (G : Fin n → Fin n → Module.End ℂ H)
    (hg : Formalism.REAL.GlRel G) (hh : ∀ a b (x y : H), ⟪G a b x, y⟫_ℂ = ⟪x, G b a y⟫_ℂ)
    (hd : ∀ (X : Matrix (Fin n) (Fin n) ℂ) (γ : ℝ → Matrix.unitaryGroup (Fin n) ℂ), Xᴴ = -X →
      (∀ t : ℝ, (γ t).1 = NormedSpace.exp ((t : ℂ) • X)) → ∀ w : H,
        HasDerivAt (fun t : ℝ => ρ (γ t) w) (∑ a, ∑ b, X a b • G a b w) 0) :
    ∃ F : Finset (Fin n → ℤ), (∀ ν ∈ F, Antitone ν) ∧ (∀ ν : Fin n → ℤ, Antitone ν → ν ∉ F → hwOf G (wtR ν) = ⊥) ∧
      ∀ S : H →ₗ[ℂ] H, (∀ a b w, S (G a b w) = G a b (S w)) →
        ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (z : Fin n → ℂ), k.1 = diagonal z → Function.Injective z →
          LinearMap.trace ℂ H ((ρ k : H →ₗ[ℂ] H) ∘ₗ S) = ∑ ν ∈ F, trOn (hwOf G (wtR ν)) S * weylChar ν z := by
  classical
  have hp : ∀ ν : Fin n → ℤ, Antitone ν → ∃ p : H →ₗ[ℂ] H, (∀ a b w, p (G a b w) = G a b (p w)) ∧
      (∀ v ∈ hwOf G (wtR ν), p v = v) ∧
      (∀ (μ : Fin n → ℝ) (v : H), μ ≠ wtR ν → Formalism.REAL.KHighest (fun _ => true) G μ v → p v = 0) ∧
      ∀ S : H →ₗ[ℂ] H, (∀ a b w, S (G a b w) = G a b (S w)) →
        ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (z : Fin n → ℂ), k.1 = diagonal z → Function.Injective z →
          LinearMap.trace ℂ H ((ρ k : H →ₗ[ℂ] H) ∘ₗ S ∘ₗ p) = trOn (hwOf G (wtR ν)) S * weylChar ν z :=
    fun ν hν => GlobalTheory.T.highest_weight_integral_of_unitary H ρ G ν hg hh hd hν
  choose! p hpG hpid hpkill hptr using hp
  obtain ⟨Fs, hFs⟩ : ∃ Fs : Set (Fin n → ℤ), ∀ ν, ν ∈ Fs ↔ Antitone ν ∧ hwOf G (wtR ν) ≠ ⊥ :=
    ⟨{ν | Antitone ν ∧ hwOf G (wtR ν) ≠ ⊥}, fun ν => Iff.rfl⟩
  have hfin : Fs.Finite := by
    have hv : ∀ ν ∈ Fs, ∃ v ∈ hwOf G (wtR ν), v ≠ 0 := fun ν hν =>
      Submodule.exists_mem_ne_zero_of_ne_bot ((hFs ν).1 hν).2
    choose! v hvmem hvne using hv
    have hli : LinearIndependent ℂ (fun ν : Fs => v ν) := by
      rw [linearIndependent_iff']
      intro s g hs i hi
      have hia : Antitone (i : Fin n → ℤ) := ((hFs i).1 i.2).1
      have h1 := congrArg (p i) hs
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_zero, Finset.sum_eq_single i] at h1
      · rw [map_smul, hpid i hia (v i) (hvmem i i.2)] at h1
        exact (smul_eq_zero.mp h1).resolve_right (hvne i i.2)
      · intro j _ hji
        rw [map_smul, hpkill i hia (wtR j) (v j) (fun heq => hji (Subtype.ext (wtR_injective heq)))
          (hvmem j j.2), smul_zero]
      · intro hi'
        exact absurd hi hi'
    exact Set.finite_coe_iff.mp hli.finite
  have hF : ∀ ν, ν ∈ hfin.toFinset ↔ Antitone ν ∧ hwOf G (wtR ν) ≠ ⊥ := fun ν => by
    rw [Set.Finite.mem_toFinset, hFs]
  have hcomm : ∀ a b w, (LinearMap.id - ∑ ν ∈ hfin.toFinset, p ν : H →ₗ[ℂ] H) (G a b w) =
      G a b ((LinearMap.id - ∑ ν ∈ hfin.toFinset, p ν : H →ₗ[ℂ] H) w) := by
    intro a b w
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.sum_apply, map_sub, map_sum]
    congr 1
    exact Finset.sum_congr rfl fun ν hν => hpG ν ((hF ν).1 hν).1 a b w
  have hhigh : ∀ (μ : Fin n → ℝ) (v : H), Formalism.REAL.KHighest (fun _ => true) G μ v →
      (LinearMap.id - ∑ ν ∈ hfin.toFinset, p ν : H →ₗ[ℂ] H) v = 0 := by
    intro μ v hK
    by_cases hv0 : v = 0
    · rw [hv0, map_zero]
    obtain ⟨ν₀, rfl⟩ := GlobalTheory.T.highest_weight_of_unitary_derivative H ρ G hd μ v hv0 hK.1
    have hanti : Antitone ν₀ := by
      have h := GlobalTheory.T.highest_weight_antitone_alt H G ⊤ (wtR ν₀) v hg inferInstance (fun _ _ _ _ => Submodule.mem_top)
        Submodule.mem_top hv0 hK
      intro i j hij
      have := h hij
      simp only [wtR] at this
      exact_mod_cast this
    have hmem : v ∈ hwOf G (wtR ν₀) := hK
    have hin : ν₀ ∈ hfin.toFinset := (hF ν₀).2 ⟨hanti, fun hbot => hv0 (by
      rw [hbot] at hmem
      exact (Submodule.mem_bot ℂ).1 hmem)⟩
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.sum_apply]
    rw [Finset.sum_eq_single ν₀, hpid ν₀ hanti v hmem, sub_self]
    · intro ν hν hne
      exact hpkill ν ((hF ν).1 hν).1 (wtR ν₀) v (fun heq => hne (wtR_injective heq).symm) hK
    · intro h
      exact absurd hin h
  have hsum : ∑ ν ∈ hfin.toFinset, p ν = LinearMap.id :=
    (sub_eq_zero.mp (GlobalTheory.T.intertwiner_eq_zero_of_vanish_on_highest H H G G hg hh _ hcomm hhigh)).symm
  refine ⟨hfin.toFinset, fun ν hν => ((hF ν).1 hν).1, fun ν hν hνF => ?_, ?_⟩
  · by_contra hne
    exact hνF ((hF ν).2 ⟨hν, hne⟩)
  · intro S hS k z hk hz
    calc LinearMap.trace ℂ H ((ρ k : H →ₗ[ℂ] H) ∘ₗ S)
        = LinearMap.trace ℂ H ((ρ k : H →ₗ[ℂ] H) ∘ₗ S ∘ₗ ∑ ν ∈ hfin.toFinset, p ν) := by
          rw [hsum, LinearMap.comp_id]
      _ = ∑ ν ∈ hfin.toFinset, LinearMap.trace ℂ H ((ρ k : H →ₗ[ℂ] H) ∘ₗ S ∘ₗ p ν) := by
          set_option synthInstance.maxHeartbeats 100000 in
            rw [← map_sum]
          congr 1
          ext w
          set_option synthInstance.maxHeartbeats 100000 in
            simp [LinearMap.sum_apply, map_sum]
      _ = _ := Finset.sum_congr rfl fun ν hν => hptr ν ((hF ν).1 hν).1 S hS k z hk hz

theorem sum_single' {M : Type*} [AddCommGroup M] [Module ℂ M] (x : Fin n → Fin n → M) (a b : Fin n) (c : ℂ) :
    ∑ i, ∑ j, (Matrix.single a b c : Matrix (Fin n) (Fin n) ℂ) i j • x i j = c • x a b := by
  classical
  rw [Finset.sum_eq_single a (fun i _ hi => Finset.sum_eq_zero fun j _ => by
        simp [Ne.symm hi]) (by simp),
      Finset.sum_eq_single b (fun j _ hj => by simp [Ne.symm hj]) (by simp)]
  simp

theorem eq_zero_of_skew {M : Type*} [AddCommGroup M] [Module ℂ M] (x : Fin n → Fin n → M)
    (h : ∀ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ = -X → ∑ i, ∑ j, X i j • x i j = 0) (a b : Fin n) : x a b = 0 := by
  have h1 := h (Matrix.single a b 1 - Matrix.single b a 1) (by
    rw [Matrix.conjTranspose_sub, GlobalTheory.CompanionTheory.RealCount.InjHw.single_conjT, GlobalTheory.CompanionTheory.RealCount.InjHw.single_conjT,
      star_one, neg_sub])
  have h2 := h (Matrix.single a b Complex.I + Matrix.single b a Complex.I) (by
    rw [Matrix.conjTranspose_add, GlobalTheory.CompanionTheory.RealCount.InjHw.single_conjT, GlobalTheory.CompanionTheory.RealCount.InjHw.single_conjT,
      Complex.star_def, Complex.conj_I, GlobalTheory.CompanionTheory.RealCount.InjHw.single_negI, GlobalTheory.CompanionTheory.RealCount.InjHw.single_negI,
      neg_add, add_comm])
  simp only [Matrix.sub_apply, Matrix.add_apply, sub_smul, add_smul, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, sum_single', one_smul] at h1 h2
  rw [sub_eq_zero] at h1
  rw [← h1, ← two_smul ℂ, smul_smul] at h2
  exact (smul_eq_zero.mp h2).resolve_left (mul_ne_zero two_ne_zero Complex.I_ne_zero)

theorem trOn_transport {M N : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] (e : M ≃ₗ[ℂ] N)
    (D : Submodule ℂ M) (D' : Submodule ℂ N) (hD : ∀ x, x ∈ D ↔ e x ∈ D') (f : M →ₗ[ℂ] M) (g : N →ₗ[ℂ] N)
    (hfg : ∀ x, e (f x) = g (e x)) (hf : ∀ x ∈ D, f x ∈ D) : trOn D f = trOn D' g := by
  have hg : ∀ y ∈ D', g y ∈ D' := by
    intro y hy
    have hx : e.symm y ∈ D := (hD _).2 (by simpa using hy)
    have := (hD _).1 (hf _ hx)
    rwa [hfg, LinearEquiv.apply_symm_apply] at this
  have hmap : D.map (e : M →ₗ[ℂ] N) = D' := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hD x).1 hx
    · intro hy
      exact ⟨e.symm y, (hD _).2 (by simpa using hy), by simp⟩
  delta trOn
  rw [dite_eq_left hf, dite_eq_left hg, ← LinearMap.trace_conj' (f.restrict hf) (e.ofSubmodules D D' hmap)]
  congr 1
  ext y
  simp [LinearEquiv.conj_apply, hfg]

theorem main : ∀ {n : ℕ} (E : KMod n) (T : E.V →L[ℂ] E.V), (∀ k, T * E.ρ k = E.ρ k * T) →
    ∀ G : Fin n → Fin n → Module.End ℂ (E.V →L[ℂ] ℂ), IsDualFam E G →
    ∃ F : Finset (Fin n → ℤ), (∀ ν ∈ F, Antitone ν) ∧ (∀ ν : Fin n → ℤ, Antitone ν → ν ∉ F → hwOf G (wtR ν) = ⊥) ∧
      ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (z : Fin n → ℂ), k.1 = diagonal z → Function.Injective z →
        LinearMap.trace ℂ (E.V →L[ℂ] ℂ) (dualT E (E.ρ k⁻¹ * T) : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)) =
          ∑ ν ∈ F, trOn (hwOf G (wtR ν)) (dualT E T : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)) * weylChar ν z := by
  intro n E T hT G hG
  obtain ⟨e, ρ', hρc, hρn, he⟩ := GlobalTheory.T.unitary_euclidean_model E
  obtain ⟨G', hg', hh', hd'⟩ :=
    GlobalTheory.T.exists_compact_lie_action (EuclideanSpace ℂ (Fin (Module.finrank ℂ E.V))) ρ' hρc hρn
  have : FiniteDimensional ℂ (E.V →L[ℂ] ℂ) := LinearEquiv.finiteDimensional e.symm
  have hint : ∀ a b ξ, e (G a b ξ) = G' a b (e ξ) := by
    intro a b ξ
    have hx : ∀ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ = -X →
        ∑ i, ∑ j, X i j • (e (G i j ξ) - G' i j (e ξ)) = 0 := by
      intro X hX
      obtain ⟨γ, hγ⟩ : ∃ γ : ℝ → Matrix.unitaryGroup (Fin n) ℂ,
          ∀ t : ℝ, (γ t).1 = NormedSpace.exp ((t : ℂ) • X) :=
        ⟨GlobalTheory.CompanionTheory.RealCount.InjHw.expU X hX, fun t => rfl⟩
      have h1 := hG.2 X γ hX hγ ξ
      have h2 := hd' X γ hX hγ (e ξ)
      have h3 : HasDerivAt (fun t : ℝ => e (ξ ∘L E.ρ (γ t)⁻¹)) (e (∑ a, ∑ b, X a b • G a b ξ)) 0 := by
        exact (e.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
          (0 : ℝ) h1
      have h4 : (fun t : ℝ => e (ξ ∘L E.ρ (γ t)⁻¹)) = fun t => ρ' (γ t) (e ξ) := funext fun t => he (γ t) ξ
      rw [h4] at h3
      have h5 := h3.unique h2
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul] at h5
      simp only [smul_sub, Finset.sum_sub_distrib]
      rw [h5, sub_self]
    exact sub_eq_zero.mp (eq_zero_of_skew (fun i j => e (G i j ξ) - G' i j (e ξ)) hx a b)
  have hint2 : ∀ a b w, e.symm (G' a b w) = G a b (e.symm w) := fun a b w =>
    e.injective (by rw [hint, e.apply_symm_apply, e.apply_symm_apply])
  have hcommT : ∀ a b ξ, dualT E T (G a b ξ) = G a b (dualT E T ξ) := GlobalTheory.T.dual_operator_commutes_lie E T hT G hG
  obtain ⟨S', hS'⟩ : ∃ S' : EuclideanSpace ℂ (Fin (Module.finrank ℂ E.V)) →ₗ[ℂ]
      EuclideanSpace ℂ (Fin (Module.finrank ℂ E.V)), ∀ w, S' w = e (dualT E T (e.symm w)) :=
    ⟨e.conj (dualT E T : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)), fun w => by simp [LinearEquiv.conj_apply]⟩
  have hS'comm : ∀ a b w, S' (G' a b w) = G' a b (S' w) := by
    intro a b w
    rw [hS', hS', hint2, hcommT, hint]
  have hmem : ∀ (μ : Fin n → ℝ) (v : E.V →L[ℂ] ℂ), v ∈ hwOf G μ ↔ e v ∈ hwOf G' μ := by
    intro μ v
    change Formalism.REAL.KHighest (fun _ => true) G μ v ↔ Formalism.REAL.KHighest (fun _ => true) G' μ (e v)
    unfold Formalism.REAL.KHighest Formalism.REAL.IsWeight
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun a => by rw [← hint, h1 a, map_smul], fun a b hab hε => by rw [← hint, h2 a b hab hε, map_zero]⟩
    · rintro ⟨h1, h2⟩
      refine ⟨fun a => e.injective ?_, fun a b hab hε => e.injective ?_⟩
      · rw [hint, h1 a, map_smul]
      · rw [hint, h2 a b hab hε, map_zero]
  have hpres : ∀ μ : Fin n → ℝ, ∀ x ∈ hwOf G μ, dualT E T x ∈ hwOf G μ := by
    intro μ x hx
    change Formalism.REAL.KHighest (fun _ => true) G μ x at hx
    change Formalism.REAL.KHighest (fun _ => true) G μ (dualT E T x)
    unfold Formalism.REAL.KHighest Formalism.REAL.IsWeight at hx ⊢
    exact ⟨fun a => by rw [← hcommT, hx.1 a, map_smul],
      fun a b hab hε => by rw [← hcommT, hx.2 a b hab hε, map_zero]⟩
  have hfg : ∀ x, e ((dualT E T : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)) x) = S' (e x) := fun x => by
    simp [hS']
  obtain ⟨F, hFa, hFbot, htr⟩ := core _ ρ' G' hg' hh' hd'
  refine ⟨F, hFa, fun ν hν hνF => ?_, ?_⟩
  · rw [eq_bot_iff]
    intro v hv
    have h' : e v ∈ hwOf G' (wtR ν) := (hmem _ v).1 hv
    rw [hFbot ν hν hνF, Submodule.mem_bot] at h'
    exact (Submodule.mem_bot ℂ).2 (e.map_eq_zero_iff.mp h')
  · intro k z hk hz
    have hconj : e.conj (dualT E (E.ρ k⁻¹ * T) : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)) =
        (ρ' k : _ →ₗ[ℂ] _) ∘ₗ S' := by
      apply LinearMap.ext
      intro w
      rw [LinearMap.comp_apply, hS', ContinuousLinearMap.coe_coe, ← he]
      show e (dualT E (E.ρ k⁻¹ * T) (e.symm w)) = _
      congr 1
      simp only [dualT, ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply]
      rw [← hT k⁻¹, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc]
    rw [← LinearMap.trace_conj' (dualT E (E.ρ k⁻¹ * T) : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)) e, hconj,
      htr S' hS'comm k z hk hz]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [trOn_transport e (hwOf G (wtR ν)) (hwOf G' (wtR ν)) (hmem _) _ S' hfg (hpres _)]

end GlobalTheory.CompanionTheory.RealCountG.CharDec
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualWeightTraceFormulaStatement
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG
theorem _root_.GlobalTheory.T.dual_weight_trace_formula : ∀ {n : ℕ} (E : KMod n) (T : E.V →L[ℂ] E.V), (∀ k, T * E.ρ k = E.ρ k * T) → ∀ G : Fin n → Fin n → Module.End ℂ (E.V →L[ℂ] ℂ), IsDualFam E G → ∃ F : Finset (Fin n → ℤ), (∀ ν ∈ F, Antitone ν) ∧ (∀ ν : Fin n → ℤ, Antitone ν → ν ∉ F → hwOf G (wtR ν) = ⊥) ∧ ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (z : Fin n → ℂ), k.1 = diagonal z → Function.Injective z → LinearMap.trace ℂ (E.V →L[ℂ] ℂ) (dualT E (E.ρ k⁻¹ * T) : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)) = ∑ ν ∈ F, trOn (hwOf G (wtR ν)) (dualT E T : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)) * weylChar ν z :=
  @GlobalTheory.CompanionTheory.RealCountG.CharDec.main
end
