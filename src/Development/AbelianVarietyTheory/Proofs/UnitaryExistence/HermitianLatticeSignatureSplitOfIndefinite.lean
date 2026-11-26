module

public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsUnf
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCoprimeScaledIsometrySameSignature

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUnitaryConjSplitLatticeOfLocal
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUnitaryConjSplitLatticeOfLocal
open NumberField Matrix

namespace GlobalTheory.UTrans

def awayLoc {V : Type} [AddCommGroup V] (L : AddSubgroup V) (b : ℕ) : AddSubgroup V where
  carrier := {v | ∃ K : ℕ, K.Coprime b ∧ K • v ∈ L}
  zero_mem' := ⟨1, by simp, by simp⟩
  add_mem' := by
    rintro v w ⟨K, hK, hv⟩ ⟨K', hK', hw⟩
    refine ⟨K * K', Nat.Coprime.mul_left hK hK', ?_⟩
    have : (K * K') • (v + w) = K' • K • v + K • K' • w := by module
    rw [this]
    exact add_mem (nsmul_mem hv _) (nsmul_mem hw _)
  neg_mem' := by
    rintro v ⟨K, hK, hv⟩
    exact ⟨K, hK, by simpa using hv⟩

theorem mem_of_coprime_nsmul {V : Type} [AddCommGroup V] (L : AddSubgroup V) {K M : ℕ} (h : K.Coprime M) {v : V}
    (h1 : K • v ∈ L) (h2 : M • v ∈ L) : v ∈ L := by
  obtain ⟨a, c, hac⟩ := Nat.isCoprime_iff_coprime.2 h
  have : v = a • K • v + c • M • v := by
    rw [← natCast_zsmul, ← natCast_zsmul, smul_smul, smul_smul, ← add_smul, hac, one_smul]
  rw [this]
  exact add_mem (zsmul_mem h1 _) (zsmul_mem h2 _)

theorem awayLoc_of_nsmul {V : Type} [AddCommGroup V] (L : AddSubgroup V) {b K : ℕ} (hK : K.Coprime b) {v : V}
    (h : K • v ∈ awayLoc L b) : v ∈ awayLoc L b := by
  obtain ⟨K', hK', h⟩ := h
  exact ⟨K' * K, Nat.Coprime.mul_left hK' hK, by rwa [mul_smul]⟩

theorem le_awayLoc {V : Type} [AddCommGroup V] (L : AddSubgroup V) (b : ℕ) {v : V} (h : v ∈ L) :
    v ∈ awayLoc L b := ⟨1, by simp, by simpa using h⟩

theorem awayLoc_map {V : Type} [AddCommGroup V] (L : AddSubgroup V) (b : ℕ) (f : V → V)
    (hf : ∀ (K : ℕ) v, f (K • v) = K • f v) (h : ∀ v ∈ L, f v ∈ awayLoc L b) :
    ∀ v ∈ awayLoc L b, f v ∈ awayLoc L b := by
  rintro v ⟨K, hK, hv⟩
  exact awayLoc_of_nsmul L hK (hf K v ▸ h _ hv)

theorem exists_isU_conj_mem : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), Module.finrank F E = 2 → GlobalTheory.UTrans.IsHerm (c : E →+* E) G → (∃ z : Fin n → E, z ≠ 0 ∧ GlobalTheory.UTrans.hf (c : E →+* E) G z z = 0) → ∀ L L₀ : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∀ (π γ₀ : Matrix (Fin n) (Fin n) E) (x : Fin n → E) (b k : ℕ), π * π = π → (∀ v w, GlobalTheory.UTrans.hf (c : E →+* E) G (π.mulVec v) w = GlobalTheory.UTrans.hf (c : E →+* E) G v (π.mulVec w)) → π.mulVec x = x → GlobalTheory.UTrans.hf (c : E →+* E) G x x ≠ 0 → (∀ v ∈ L₀, π.mulVec v ∈ L₀) → 0 < b → (∀ v ∈ L, b • v ∈ L₀) → (∀ v ∈ L₀, b • v ∈ L) → GlobalTheory.UTrans.IsU (c : E →+* E) G γ₀ → k.Coprime b → (∀ v ∈ L, k • γ₀.mulVec v ∈ L₀) → (∀ v ∈ L₀, k • γ₀⁻¹.mulVec v ∈ L) → ∃ γ : Matrix (Fin n) (Fin n) E, GlobalTheory.UTrans.IsU (c : E →+* E) G γ ∧ ∀ v ∈ L, (γ⁻¹ * π * γ).mulVec v ∈ L := by
  intro F E _ _ _ _ _ c n G hFE hG hz L L₀ hL hsp π γ₀ x b k _ hsa hx hxx hπ hb hb1 hb2 hγ hk hk1 hk2
  obtain ⟨m, hm, hγm⟩ := (GlobalTheory.UTrans.isU_eq_tv_mul_tvGen F E c n G hG hz γ₀ hγ).1 x hxx
  obtain ⟨hN1, hN2⟩ := GlobalTheory.UTrans.tvGen_normal E n (c : E →+* E) G hG
  have hC := GlobalTheory.UTrans.Calc.calculus E n (c : E →+* E) G hG.invol hG.herm
  set s := tv (c : E →+* E) G x ((γ₀.det - 1) / hf (c : E →+* E) G x x) with hs
  have hsπ : s * π = π * s := by
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro v
    simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, hs, hC.2.1, Matrix.mulVec_add, Matrix.mulVec_smul,
      hsa, hx]
  have hγd : IsUnit γ₀.det := by
    refine IsUnit.mk0 _ fun h => ?_
    have := (hN1 γ₀ hγ).1
    simp [h] at this
  obtain ⟨-, hmd, hmi, -⟩ := hN2 m hm
  have hmu : IsUnit m.det := by simp [hmd]
  have hsu : IsUnit s.det := by
    rw [hγm, Matrix.det_mul, hmd, mul_one] at hγd
    exact hγd
  have hP : γ₀⁻¹ * π * γ₀ = m⁻¹ * π * m := by
    rw [hγm, Matrix.mul_inv_rev]
    calc m⁻¹ * s⁻¹ * π * (s * m) = m⁻¹ * (s⁻¹ * (π * s)) * m := by simp only [Matrix.mul_assoc]
      _ = m⁻¹ * π * m := by rw [← hsπ, Matrix.nonsing_inv_mul_cancel_left _ _ hsu]
  set A := L.toAddSubgroup with hA
  have hPL : ∀ v ∈ awayLoc A b, (m⁻¹ * π * m) *ᵥ v ∈ awayLoc A b := by
    refine awayLoc_map A b _ (fun K v => Matrix.mulVec_smul _ _ _) fun v hv => ⟨k * k, Nat.Coprime.mul_left hk hk, ?_⟩
    have := hk2 _ (hπ _ (hk1 v hv))
    rw [Matrix.mulVec_smul, Matrix.mulVec_smul, smul_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hP] at this
    exact this
  have hden : ∀ p ∈ TvGen (c : E →+* E) G, ∃ e : ℕ, ∀ v ∈ awayLoc A b, b ^ e • (p *ᵥ v) ∈ awayLoc A b := by
    intro p hp
    obtain ⟨q, -, k₀, e₀, hk₀, H₀⟩ := tvGen_adjust F E c n G hFE hG L hL hsp p hp b hb 0
    refine ⟨e₀, awayLoc_map A b _ (fun K v => by rw [Matrix.mulVec_smul, smul_comm]) fun v hv => ⟨k₀, hk₀, ?_⟩⟩
    obtain ⟨⟨w, hw, h1⟩, h2, -⟩ := H₀ v hv
    have : k₀ • b ^ e₀ • (p *ᵥ v) = k₀ • b ^ e₀ • (q *ᵥ v) - b ^ e₀ • (b ^ 0 • w) := by
      rw [← h1]; module
    rw [this]
    exact sub_mem (nsmul_mem h2 _) (nsmul_mem (nsmul_mem hw _) _)
  obtain ⟨e₁, he₁⟩ := hden _ hmi
  obtain ⟨q, hq, k', e, hk', H⟩ := tvGen_adjust F E c n G hFE hG L hL hsp m hm b hb (e₁ + 1)
  obtain ⟨hqU, hqd, hqi, -⟩ := hN2 q hq
  have hqu : IsUnit q.det := by simp [hqd]
  have hbE : (b : E) ≠ 0 := Nat.cast_ne_zero.2 hb.ne'

  have hδ : ∀ v ∈ awayLoc A b, ∃ w ∈ awayLoc A b, (m⁻¹ * q) *ᵥ v = v + b • w := by
    have h1 : ∀ v ∈ awayLoc A b, (b : E)⁻¹ • ((m⁻¹ * q) *ᵥ v - v) ∈ awayLoc A b := by
      refine awayLoc_map A b _ (fun K v => by rw [Matrix.mulVec_smul, ← smul_sub, smul_comm]) fun v hv => ?_
      obtain ⟨⟨w, hw, h1⟩, -⟩ := H v hv
      apply awayLoc_of_nsmul A hk'
      have h2 := congrArg (fun u => m⁻¹ *ᵥ u) h1
      simp only [Matrix.mulVec_smul, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hmu,
        Matrix.one_mulVec] at h2
      rw [smul_comm, h2, pow_succ', mul_smul, ← Nat.cast_smul_eq_nsmul E b, smul_smul, inv_mul_cancel₀ hbE, one_smul]
      exact he₁ _ (le_awayLoc A b hw)
    intro v hv
    refine ⟨_, h1 v hv, ?_⟩
    rw [← Nat.cast_smul_eq_nsmul E b, smul_smul, mul_inv_cancel₀ hbE, one_smul]
    abel
  have hu : ∀ v ∈ awayLoc A b, (q⁻¹ * m) *ᵥ v ∈ awayLoc A b := by
    obtain ⟨r, hr⟩ := hden _ (mul_mem hqi hm)
    induction r with
    | zero => simpa using hr
    | succ r ih =>
      refine ih fun v hv => ?_
      obtain ⟨w, hw, h1⟩ := hδ v hv
      have h2 := congrArg (fun u => (q⁻¹ * m) *ᵥ u) h1
      have h3 : q⁻¹ * m * (m⁻¹ * q) = 1 := by
        rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hmu, Matrix.nonsing_inv_mul _ hqu]
      simp only [Matrix.mulVec_mulVec, h3, Matrix.one_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul] at h2
      have h4 : b ^ r • ((q⁻¹ * m) *ᵥ v) = b ^ r • v - b ^ (r + 1) • ((q⁻¹ * m) *ᵥ w) := by
        rw [eq_sub_iff_add_eq, pow_succ, mul_smul, ← smul_add, ← h2]
      rw [h4]
      exact sub_mem (nsmul_mem hv _) (hr w hw)
  refine ⟨q, hqU, fun v hv => ?_⟩
  have hQ : q⁻¹ * π * q = (q⁻¹ * m) * ((m⁻¹ * π * m) * (m⁻¹ * q)) := by
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hmu]
  have h1 : (q⁻¹ * π * q) *ᵥ v ∈ awayLoc A b := by
    rw [hQ, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec v (m⁻¹ * π * m)]
    apply hu
    apply hPL
    obtain ⟨w, hw, h⟩ := hδ v (le_awayLoc A b hv)
    rw [h]
    exact add_mem (le_awayLoc A b hv) (nsmul_mem hw _)
  obtain ⟨K, hK, h1⟩ := h1
  have h2 := (H _ (hb2 _ (hπ _ (hb1 _ (H v hv).2.1)))).2.2
  simp only [Matrix.mulVec_smul, Matrix.mulVec_mulVec, smul_smul, ← Matrix.mul_assoc] at h2
  refine mem_of_coprime_nsmul A ?_ h1 h2
  repeat' apply Nat.Coprime.mul_right
  all_goals first | exact hK | exact hK.pow_right _

end GlobalTheory.UTrans
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUnitaryConjSplitLatticeOfLocalStatement
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_conj_split_lattice_of_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), Module.finrank F E = 2 → GlobalTheory.UTrans.IsHerm (c : E →+* E) G → (∃ z : Fin n → E, z ≠ 0 ∧ GlobalTheory.UTrans.hf (c : E →+* E) G z z = 0) → ∀ L L₀ : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∀ (π γ₀ : Matrix (Fin n) (Fin n) E) (x : Fin n → E) (b k : ℕ), π * π = π → (∀ v w, GlobalTheory.UTrans.hf (c : E →+* E) G (π.mulVec v) w = GlobalTheory.UTrans.hf (c : E →+* E) G v (π.mulVec w)) → π.mulVec x = x → GlobalTheory.UTrans.hf (c : E →+* E) G x x ≠ 0 → (∀ v ∈ L₀, π.mulVec v ∈ L₀) → 0 < b → (∀ v ∈ L, b • v ∈ L₀) → (∀ v ∈ L₀, b • v ∈ L) → GlobalTheory.UTrans.IsU (c : E →+* E) G γ₀ → k.Coprime b → (∀ v ∈ L, k • γ₀.mulVec v ∈ L₀) → (∀ v ∈ L₀, k • γ₀⁻¹.mulVec v ∈ L) → ∃ γ : Matrix (Fin n) (Fin n) E, GlobalTheory.UTrans.IsU (c : E →+* E) G γ ∧ ∀ v ∈ L, (γ⁻¹ * π * γ).mulVec v ∈ L := by
  first | exact @GlobalTheory.UTrans.exists_isU_conj_mem | exact GlobalTheory.UTrans.exists_isU_conj_mem | (intros; apply GlobalTheory.UTrans.exists_isU_conj_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HermitianLatticeSignatureSplitOfIndefinite
open NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompRat GlobalTheory.HermModel
open scoped nonZeroDivisors

namespace GlobalTheory.SplitGenus

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}


omit [IsCMField E] in
theorem exists_matrix {M : Type} [AddCommGroup M] [Module (𝓞 E) M] (φ ψ : M →ₗ[𝓞 E] (Fin r → E))
    (hf : Function.Injective φ) (hspan : Submodule.span E (Set.range φ) = ⊤) :
    ∃ A : Matrix (Fin r) (Fin r) E, ∀ x, A *ᵥ φ x = ψ x := by
  haveI : IsLocalizedModule (𝓞 E)⁰ φ :=
    { map_units := fun s => (isLocalizedModule_id (𝓞 E)⁰ (Fin r → E) E).map_units s
      surj := fun v => by
        have hv : v ∈ Submodule.span E (Set.range φ) := by rw [hspan]; trivial
        obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (𝓞 E)⁰ E _ v hv
        rw [← LinearMap.coe_range, Submodule.span_eq] at ht
        obtain ⟨m, hm⟩ := ht
        exact ⟨(m, t), hm.symm⟩
      exists_of_eq := fun h => ⟨1, by rw [hf h]⟩ }
  let g := IsLocalizedModule.lift (𝓞 E)⁰ φ ψ
    (fun s => (isLocalizedModule_id (𝓞 E)⁰ (Fin r → E) E).map_units s)
  refine ⟨LinearMap.toMatrix' (g.extendScalarsOfIsLocalization (𝓞 E)⁰ E), fun x => ?_⟩
  rw [LinearMap.toMatrix'_mulVec]
  exact IsLocalizedModule.lift_apply (𝓞 E)⁰ φ ψ
    (fun s => (isLocalizedModule_id (𝓞 E)⁰ (Fin r → E) E).map_units s) x

theorem herm_add_left (G : Matrix (Fin r) (Fin r) E) (x x' y : Fin r → E) :
    FD.herm G (x + x') y = FD.herm G x y + FD.herm G x' y := by
  simp [FD.herm, add_mul, Finset.sum_add_distrib]

theorem herm_zero_left (G : Matrix (Fin r) (Fin r) E) (x : Fin r → E) : FD.herm G 0 x = 0 := by
  simp [FD.herm]

theorem herm_ext (G A B C D : Matrix (Fin r) (Fin r) E) {S : Set (Fin r → E)} (hS : Submodule.span E S = ⊤)
    (h : ∀ x ∈ S, ∀ y ∈ S, FD.herm G (A *ᵥ x) (B *ᵥ y) = FD.herm G (C *ᵥ x) (D *ᵥ y)) (x y : Fin r → E) :
    FD.herm G (A *ᵥ x) (B *ᵥ y) = FD.herm G (C *ᵥ x) (D *ᵥ y) := by
  have hx : x ∈ Submodule.span E S := hS ▸ Submodule.mem_top
  have hy : y ∈ Submodule.span E S := hS ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | zero => simp only [mulVec_zero, herm_zero_left]
  | add a b _ _ ha hb => simp only [mulVec_add, herm_add_left, ha, hb]
  | smul c a _ ha => simp only [mulVec_smul, herm_smul_left, ha]
  | mem x hx =>
    induction hy using Submodule.span_induction with
    | zero => simp only [mulVec_zero, herm_zero_right]
    | add a b _ _ ha hb => simp only [mulVec_add, herm_add_right, ha, hb]
    | smul c a _ ha => simp only [mulVec_smul, herm_smul_right, ha]
    | mem y hy => exact h x hx y hy

theorem herm_eq_of_trace (G : Matrix (Fin r) (Fin r) E) {ξ : E} (hξ : ξ ≠ 0) {u v u' v' : Fin r → E}
    (h : ∀ a : 𝓞 E, Algebra.trace ℚ E (ξ * FD.herm G (a • u) v) = Algebra.trace ℚ E (ξ * FD.herm G (a • u') v')) :
    FD.herm G u v = FD.herm G u' v' := by
  have : ξ * (FD.herm G u v - FD.herm G u' v') = 0 := eq_zero_of_trace_mul_integer fun a => by
    have h1 := h a
    rw [show a • u = (a : E) • u from rfl, show a • u' = (a : E) • u' from rfl, herm_smul_left,
      herm_smul_left] at h1
    rw [← sub_eq_zero, ← map_sub] at h1
    rw [← h1]
    congr 1
    ring
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hξ)

theorem trace_nsmul (G : Matrix (Fin r) (Fin r) E) (ξ : E) (N : ℕ) (u v : Fin r → E) :
    Algebra.trace ℚ E (ξ * FD.herm G ((N : E) • u) ((N : E) • v)) =
      (N : ℚ) ^ 2 * Algebra.trace ℚ E (ξ * FD.herm G u v) := by
  rw [herm_smul_left, herm_smul_right]
  have hc : FD.cc (N : E) = N := by simp [FD.cc]
  have h3 : ξ * ((N : E) * (FD.herm G u v * FD.cc (N : E))) = ((N : ℚ) ^ 2) • (ξ * FD.herm G u v) := by
    rw [hc, Algebra.smul_def]
    simp only [map_pow, map_natCast]
    ring
  rw [h3, map_smul, smul_eq_mul]


omit [IsCMField E] in
theorem denseRange_emb [_root_.NumberField.IsTotallyComplex E] (τ : E →+* ℂ) : DenseRange τ := by
  have hn : ¬ ComplexEmbedding.IsReal τ := IsTotallyComplex.complexEmbedding_not_isReal τ
  obtain ⟨x, hx⟩ : ∃ x, (τ x).im ≠ 0 := by
    by_contra h
    push Not at h
    exact hn (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => Complex.conj_eq_iff_im.2 (h x)))
  let f : ℝ × ℝ → ℂ := fun p => (p.1 : ℂ) + (p.2 : ℂ) * τ x
  have hf : Continuous f := by fun_prop
  have hs : Function.Surjective f := fun z =>
    ⟨(z.re - z.im / (τ x).im * (τ x).re, z.im / (τ x).im), by
      apply Complex.ext
      · simp [f, -Complex.ofReal_div]
      · simp [f, -Complex.ofReal_div, hx]⟩
  have hd : DenseRange (f ∘ Prod.map ((↑) : ℚ → ℝ) ((↑) : ℚ → ℝ)) :=
    hs.denseRange.comp (Rat.denseRange_cast.prodMap Rat.denseRange_cast) hf
  refine Dense.mono ?_ hd
  rintro _ ⟨p, rfl⟩
  exact ⟨(p.1 : E) + (p.2 : E) * x, by simp [f]⟩

theorem exists_rat (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) {U : Set ℝ} (hU : IsOpen U) (u : Fin r → ℂ)
    (hu : (FD.hermC τ G u u).re ∈ U) : ∃ x, (τ (FD.herm G x x)).re ∈ U := by
  have hd : DenseRange (Pi.map fun _ : Fin r => (τ : E → ℂ)) := DenseRange.piMap fun _ => denseRange_emb τ
  have hc : Continuous fun u : Fin r → ℂ => (FD.hermC τ G u u).re := by
    unfold FD.hermC
    fun_prop
  obtain ⟨x, hx⟩ := hd.exists_mem_open (hU.preimage hc) ⟨u, hu⟩
  refine ⟨x, ?_⟩
  have : τ (FD.herm G x x) = FD.hermC τ G (τ ∘ x) (τ ∘ x) := by
    simp [FD.herm, FD.hermC, FD.cc, IsCMField.complexEmbedding_complexConj]
  rw [this]; exact hx

theorem both_signs (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) {p : ℕ} (h0 : 0 < p) (h1 : p < r)
    (h : ∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧
      FD.gram τ G Q = Matrix.diagonal fun a : Fin r => ((FD.sgn p (a : ℕ) : ℝ) : ℂ)) :
    (∃ x, 0 < (τ (FD.herm G x x)).re) ∧ ∃ y, (τ (FD.herm G y y)).re < 0 := by
  obtain ⟨P, -, hP⟩ := h
  constructor
  · have e := congrFun (congrFun hP ⟨0, h0.trans h1⟩) ⟨0, h0.trans h1⟩
    refine exists_rat τ G (U := Set.Ioi 0) isOpen_Ioi (FD.col P ⟨0, h0.trans h1⟩) ?_
    change FD.hermC τ G _ _ = _ at e
    rw [Set.mem_Ioi, e]
    simp [FD.sgn, h0]
  · have e := congrFun (congrFun hP ⟨p, h1⟩) ⟨p, h1⟩
    refine exists_rat τ G (U := Set.Iio 0) isOpen_Iio (FD.col P ⟨p, h1⟩) ?_
    change FD.hermC τ G _ _ = _ at e
    rw [Set.mem_Iio, e]
    simp [FD.sgn]

variable {H : Host E}

theorem indefinite (D : Datum H) (hp : 1 ≤ D.p) (hq : 1 ≤ D.q) (G : Matrix (Fin r) (Fin r) E)
    (φ : D.La →ₗ[𝓞 E] (Fin r → E))
    (hM : Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, FD.cc (G a b) = G b a) ∧ G.det ≠ 0 ∧
      ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E ((H.rt : E) * FD.herm G (φ x) (φ y))) (τ : E →+* ℂ) :
    (∃ x, 0 < (τ (FD.herm G x x)).re) ∧ ∃ y, (τ (FD.herm G y y)).re < 0 := by
  have hξ := GlobalTheory.OneSpace.cc_rt H
  have hr := (rank_integral_selfDual E H D r _ G φ hξ hM).1
  have key : ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 →
      (∃ x, 0 < (τ (FD.herm G x x)).re) ∧ ∃ y, (τ (FD.herm G y y)).re < 0 := by
    intro τ hτ
    have s := GlobalTheory.T.signature_hermitian_model_of_datum E H D r _ G φ hξ hM τ hτ
    rcases lt_or_gt_of_ne (GlobalTheory.OneSpace.im_ne τ hξ (GlobalTheory.OneSpace.rt_ne H)) with h | h
    · exact both_signs τ G (by omega) (by omega) (s.2 h)
    · exact both_signs τ G (by omega) (by omega) (s.1 h)
  have h1 : τ (H.rt : E) ^ 2 = H.rt0 ^ 2 := by rw [GlobalTheory.OneSpace.emb_rt_sq, H.sqrt_neg_disc_sq]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
  · exact key τ h
  · have := key (ComplexEmbedding.conjugate τ) (by
      rw [ComplexEmbedding.conjugate_coe_eq, GlobalTheory.OneSpace.conj_of_sq H.d_prime.pos (GlobalTheory.OneSpace.emb_rt_sq H τ), h,
        neg_neg])
    simpa only [ComplexEmbedding.conjugate_coe_eq, Complex.conj_re] using this

theorem split_of_scaled (D D₀ : Datum H) (hp : D₀.p = D.p) (hq : D₀.q = D.q) (Lp Lm : Submodule (𝓞 E) D₀.La)
    (ho : ∀ a ∈ Lp, ∀ b ∈ Lm, D₀.EF a b = 0) (rp : Module.finrank (𝓞 E) Lp = D₀.p)
    (rm : Module.finrank (𝓞 E) Lm = D₀.q) (sp : ∀ a ∈ Lp, a ≠ 0 → 0 < H.rt0.im * D₀.EF (H.rt • a) a)
    (sm : ∀ a ∈ Lm, a ≠ 0 → H.rt0.im * D₀.EF (H.rt • a) a < 0) (N : ℕ) (hN : 0 < N) (g : D.La →ₗ[𝓞 E] D₀.La)
    (hg : Function.Injective g) (hE : ∀ x y, D₀.EF (g x) (g y) = (N : ℤ) ^ 2 * D.EF x y)
    (hs : ∀ x, ∃ a, g a ∈ Lp ∧ g (x - a) ∈ Lm) : SplitLat D := by
  have := D.fin
  have := D₀.fin
  have htop : Lp.comap g ⊔ Lm.comap g = ⊤ := by
    refine top_le_iff.1 fun x _ => ?_
    obtain ⟨a, ha, hb⟩ := hs x
    exact Submodule.mem_sup.2 ⟨a, ha, x - a, hb, add_sub_cancel _ _⟩
  have le : ∀ L : Submodule (𝓞 E) D₀.La, Module.finrank (𝓞 E) (L.comap g) ≤ Module.finrank (𝓞 E) L := fun L =>
    LinearMap.finrank_le_finrank_of_injective (f := g.restrict (p := L.comap g) (q := L) fun _ h => h)
      fun a b h => Subtype.ext (hg (congrArg Subtype.val h))
  have h1 := Submodule.rank_add_le_rank_add_rank (Lp.comap g) (Lm.comap g)
  rw [htop, rank_top, ← Module.finrank_eq_rank, ← Module.finrank_eq_rank, ← Module.finrank_eq_rank, D.rank] at h1
  have h2 : D.p + D.q ≤ Module.finrank (𝓞 E) (Lp.comap g) + Module.finrank (𝓞 E) (Lm.comap g) := by
    exact_mod_cast h1
  have h3 := le Lp
  have h4 := le Lm
  have hN' : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
  have e : ∀ a, H.rt0.im * D₀.EF (H.rt • g a) (g a) = (N : ℝ) ^ 2 * (H.rt0.im * D.EF (H.rt • a) a) := fun a => by
    rw [← map_smul, hE]
    push_cast
    ring
  refine ⟨Lp.comap g, Lm.comap g, htop, fun a ha b hb => ?_, by omega, by omega, fun a ha h0 => ?_,
    fun a ha h0 => ?_⟩
  · have := ho _ ha _ hb
    rw [hE] at this
    exact (mul_eq_zero.1 this).resolve_left (by positivity)
  · have := sp _ ha fun h => h0 (hg (h.trans (map_zero g).symm))
    rw [e] at this
    exact (mul_pos_iff_of_pos_left hN').1 this
  · have := sm _ ha fun h => h0 (hg (h.trans (map_zero g).symm))
    rw [e] at this
    by_contra hh
    exact absurd this (not_lt.2 (mul_nonneg hN'.le (not_lt.1 hh)))

theorem isUnit_det {G γ : Matrix (Fin r) (Fin r) E} (hG : G.det ≠ 0)
    (h : ∀ x y, FD.herm G (γ *ᵥ x) (γ *ᵥ y) = FD.herm G x y) : IsUnit γ.det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  obtain ⟨v, hv, e⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  exact hv (eq_zero_of_herm_eq_zero hG fun u => by rw [← h, e, herm_zero_left])

theorem exists_scaled_map {M M₀ : Type} [AddCommGroup M] [Module (𝓞 E) M] [Module.Finite (𝓞 E) M]
    [AddCommGroup M₀] [Module (𝓞 E) M₀] (φ : M →ₗ[𝓞 E] (Fin r → E)) (φ₀ : M₀ →ₗ[𝓞 E] (Fin r → E))
    (hinj : Function.Injective φ₀) (hspan : Submodule.span E (Set.range φ₀) = ⊤) :
    ∃ (N : ℕ) (g : M →ₗ[𝓞 E] M₀), 0 < N ∧ ∀ x, φ₀ (g x) = (N : E) • φ x := by
  obtain ⟨N, hN, hmem⟩ := GlobalTheory.SelfDualIsom.exists_nat_smul_mem φ φ₀ hspan
  refine ⟨N, (LinearEquiv.ofInjective φ₀ hinj).symm.toLinearMap ∘ₗ ((N : 𝓞 E) • φ).codRestrict _ hmem, hN,
    fun x => ?_⟩
  have h1 := LinearEquiv.ofInjective_symm_apply φ₀ (h := hinj) (((N : 𝓞 E) • φ).codRestrict _ hmem x)
  refine h1.trans ?_
  show (N : 𝓞 E) • φ x = _
  rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]

theorem exists_projector (D₀ : Datum H) (G : Matrix (Fin r) (Fin r) E) (φ₀ : D₀.La →ₗ[𝓞 E] (Fin r → E))
    (hinj : Function.Injective φ₀) (hspan : Submodule.span E (Set.range φ₀) = ⊤)
    (hG : ∀ a b, FD.cc (G a b) = G b a)
    (hEF : ∀ x y, ((D₀.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E ((H.rt : E) * FD.herm G (φ₀ x) (φ₀ y)))
    (Lp Lm : Submodule (𝓞 E) D₀.La) (hc : IsCompl Lp Lm) (ho : ∀ a ∈ Lp, ∀ b ∈ Lm, D₀.EF a b = 0) :
    ∃ π : Matrix (Fin r) (Fin r) E, π * π = π ∧ (∀ v w, FD.herm G (π *ᵥ v) w = FD.herm G v (π *ᵥ w)) ∧
      (∀ y, π *ᵥ φ₀ y ∈ LinearMap.range φ₀) ∧ (∀ y, π *ᵥ φ₀ y = φ₀ y ↔ y ∈ Lp) ∧
      ∀ y, π *ᵥ φ₀ y = 0 → y ∈ Lm := by
  let P : D₀.La →ₗ[𝓞 E] D₀.La := Lp.subtype ∘ₗ Lp.linearProjOfIsCompl Lm hc
  have hP1 : ∀ y, P y ∈ Lp := fun y => (Lp.linearProjOfIsCompl Lm hc y).2
  have hP2 : ∀ y ∈ Lp, P y = y := fun y hy => congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hc ⟨y, hy⟩)
  have hP3 : ∀ y, P y = 0 ↔ y ∈ Lm := fun y => by
    rw [← Submodule.linearProjOfIsCompl_apply_eq_zero_iff hc]
    exact Submodule.coe_eq_zero
  have hP4 : ∀ y, y - P y ∈ Lm := fun y => by rw [← hP3, map_sub, hP2 _ (hP1 y), sub_self]
  obtain ⟨π, hπ⟩ := exists_matrix φ₀ (φ₀ ∘ₗ P) hinj hspan
  have hπ' : ∀ y, π *ᵥ φ₀ y = φ₀ (P y) := hπ
  have o1 : ∀ a ∈ Lp, ∀ b ∈ Lm, FD.herm G (φ₀ a) (φ₀ b) = 0 := fun a ha b hb => by
    rw [← herm_zero_left G (φ₀ b)]
    refine herm_eq_of_trace G (GlobalTheory.OneSpace.rt_ne H) fun s => ?_
    rw [← map_smul, ← hEF, ho _ (Lp.smul_mem s ha) b hb, smul_zero, herm_zero_left]
    simp
  have o2 : ∀ a ∈ Lp, ∀ b ∈ Lm, FD.herm G (φ₀ b) (φ₀ a) = 0 := fun a ha b hb => by
    have := GlobalTheory.UTrans.Calc.hf_conj (IsCMField.complexConj E : E →+* E) G
      (fun a => IsCMField.complexConj_apply_apply E a) hG (φ₀ a) (φ₀ b)
    refine this.symm.trans ?_
    rw [show GlobalTheory.UTrans.hf (IsCMField.complexConj E : E →+* E) G (φ₀ a) (φ₀ b) = 0 from o1 a ha b hb, map_zero]
  refine ⟨π, ?_, fun v w => ?_, fun y => ⟨_, (hπ' y).symm⟩, fun y => ⟨fun h => ?_, fun h => ?_⟩, fun y h => ?_⟩
  · apply Matrix.toLin'.injective
    refine LinearMap.ext_on_range hspan fun y => ?_
    rw [toLin'_apply, toLin'_apply, ← mulVec_mulVec, hπ', hπ', hP2 _ (hP1 y)]
  · have := herm_ext G π 1 1 π hspan (by
      rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
      rw [one_mulVec, one_mulVec, hπ', hπ']
      have e1 : FD.herm G (φ₀ (P x)) (φ₀ y) = FD.herm G (φ₀ (P x)) (φ₀ (P y)) := by
        conv_lhs => rw [← add_sub_cancel (P y) y, map_add (f := _), herm_add_right, o1 _ (hP1 x) _ (hP4 y), add_zero]
      have e2 : FD.herm G (φ₀ x) (φ₀ (P y)) = FD.herm G (φ₀ (P x)) (φ₀ (P y)) := by
        conv_lhs => rw [← add_sub_cancel (P x) x, map_add (f := _), herm_add_left, o2 _ (hP1 y) _ (hP4 x), add_zero]
      rw [e1, e2]) v w
    rwa [one_mulVec, one_mulVec] at this
  · rw [hπ'] at h
    rw [← hinj h]
    exact hP1 y
  · rw [hπ', hP2 y h]
  · rw [hπ', ← map_zero φ₀] at h
    exact (hP3 y).1 (hinj h)

theorem splitLat_of_indefinite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), (∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0) → 3 ≤ D.p + D.q → 1 ≤ D.p → 1 ≤ D.q → SplitLat D := by
  intro E _ _ _ H D h1 h3 hp hq
  obtain ⟨D₀, ep, eq, Lp, Lm, htop, ho, rp, rm, sp, sm⟩ := GlobalTheory.T.exists_splitLattice_datum_every_signature E H D.p D.q h1
  have := D.fin
  have := D₀.fin
  have hξ := GlobalTheory.OneSpace.cc_rt H
  have hξ0 := GlobalTheory.OneSpace.rt_ne H
  obtain ⟨G, φ₀, hM₀⟩ := GlobalTheory.exists_herm_coord_of_datum E H D₀ (H.rt : E) hξ hξ0 (D.p + D.q) (by rw [ep, eq])
  obtain ⟨φ, hM⟩ := GlobalTheory.model_in_same_space (GlobalTheory.LocalQuad.landherrSt_of_hasseNormSt GlobalTheory.QNorm.hasseNormSt)
    GlobalTheory.QNorm.hasseNormSt E H D₀ D _ (H.rt : E) G φ₀ ep.symm eq.symm hξ hM₀
  have hind := indefinite D hp hq G φ hM
  obtain ⟨-, hfg, -, hdual⟩ := rank_integral_selfDual E H D _ _ G φ hξ hM
  obtain ⟨inj₀, span₀, hG, hdet, hEF₀⟩ := hM₀
  obtain ⟨inj, span, -, -, hEF⟩ := hM
  have hc : IsCompl Lp Lm := by
    refine ⟨Submodule.disjoint_def.2 fun a ha hb => ?_, codisjoint_iff.2 htop⟩
    by_contra h0
    exact lt_asymm (sp a ha h0) (sm a hb h0)
  obtain ⟨π, π1, π2, π3, π4, π5⟩ := exists_projector D₀ G φ₀ inj₀ span₀ hG hEF₀ Lp Lm hc ho
  have hh : GlobalTheory.UTrans.IsHerm (IsCMField.complexConj E : E →+* E) G := by
    refine ⟨fun a => IsCMField.complexConj_apply_apply E a, ⟨(H.rt : E), fun h => hξ0 ?_⟩, hG, hdet⟩
    have h2 : (H.rt : E) = -(H.rt : E) := h.symm.trans hξ
    linear_combination (1 / 2 : E) * h2
  have hz := GlobalTheory.UTrans.exists_isotropic_of_indefinite E _ _ G (fun _ => rfl) hh h3 hind
  have : Nontrivial Lp := Module.nontrivial_of_finrank_pos (R := 𝓞 E) (by omega)
  obtain ⟨⟨a, ha⟩, ha0⟩ := exists_ne (0 : Lp)
  have hxx : FD.herm G (φ₀ a) (φ₀ a) ≠ 0 := by
    intro h
    have h5 := sp a ha fun h => ha0 (Subtype.ext h)
    have h6 := hEF₀ (H.rt • a) a
    rw [map_smul φ₀, show H.rt • φ₀ a = (H.rt : E) • φ₀ a from rfl, herm_smul_left, h, mul_zero, mul_zero,
      map_zero] at h6
    have h7 : D₀.EF (H.rt • a) a = 0 := by exact_mod_cast h6
    rw [h7] at h5
    simp at h5
  obtain ⟨b₁, hb₁, m₁⟩ := GlobalTheory.SelfDualIsom.exists_nat_smul_mem φ φ₀ span₀
  obtain ⟨b₂, hb₂, m₂⟩ := GlobalTheory.SelfDualIsom.exists_nat_smul_mem φ₀ φ span
  obtain ⟨k, f, hk, hf⟩ := GlobalTheory.T.exists_coprime_scaled_isometry_same_signature E H D D₀ ep eq (2 * b₁ * b₂) (by positivity)
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [Nat.coprime_zero_left] at hk
    rw [mul_assoc] at hk
    omega
  have hkE : (k : E) ≠ 0 := by exact_mod_cast hk0
  have hkQ : (k : ℚ) ^ 2 ≠ 0 := by positivity
  obtain ⟨A, hA⟩ := exists_matrix φ (φ₀ ∘ₗ f) inj span
  have hA' : ∀ x, (k : E) • (((k : E)⁻¹ • A) *ᵥ φ x) = φ₀ (f x) := fun x => by
    rw [smul_mulVec, smul_smul, mul_inv_cancel₀ hkE, one_smul]
    exact hA x
  generalize (k : E)⁻¹ • A = γ₀ at hA'
  have hU₀ : ∀ x y, FD.herm G (γ₀ *ᵥ x) (γ₀ *ᵥ y) = FD.herm G x y := fun x y => by
    have := herm_ext G γ₀ γ₀ 1 1 span (by
      rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
      rw [one_mulVec, one_mulVec]
      refine herm_eq_of_trace G hξ0 fun s => ?_
      rw [show s • γ₀ *ᵥ φ x = (s : E) • γ₀ *ᵥ φ x from rfl, ← mulVec_smul,
        show (s : E) • φ x = s • φ x from rfl, ← map_smul]
      apply mul_left_cancel₀ hkQ
      rw [← trace_nsmul, hA', hA', ← hEF₀, ← hEF, hf]
      push_cast
      rfl) x y
    rwa [one_mulVec, one_mulVec] at this
  have hd₀ := isUnit_det hdet hU₀
  obtain ⟨γ, hU, hγ⟩ := GlobalTheory.T.exists_unitary_conj_split_lattice_of_local (maximalRealSubfield E) E (IsCMField.complexConj E) _ G
    (Algebra.IsQuadraticExtension.finrank_eq_two _ _) hh hz (LinearMap.range φ) (LinearMap.range φ₀) hfg span
    π γ₀ (φ₀ a) (2 * b₁ * b₂) k π1 π2 ((π4 a).2 ha) hxx (by rintro _ ⟨y, rfl⟩; exact π3 y) (by positivity)
    (by
      rintro _ ⟨x, rfl⟩
      rw [mul_right_comm, mul_smul, ← Nat.cast_smul_eq_nsmul (𝓞 E) b₁]
      exact nsmul_mem (m₁ x) _)
    (by
      rintro _ ⟨x, rfl⟩
      rw [mul_smul, ← Nat.cast_smul_eq_nsmul (𝓞 E) b₂]
      exact nsmul_mem (m₂ x) _)
    hU₀ hk
    (by
      rintro _ ⟨x, rfl⟩
      rw [← Nat.cast_smul_eq_nsmul E, hA']
      exact ⟨_, rfl⟩)
    (by
      rintro _ ⟨y, rfl⟩
      refine (hdual _).1 fun x => ⟨D₀.EF y (f x), ?_⟩
      rw [hEF₀, ← hA', ← Nat.cast_smul_eq_nsmul E, herm_smul_left, herm_smul_right, ← hU₀ (γ₀⁻¹ *ᵥ φ₀ y),
        mulVec_mulVec, mul_nonsing_inv _ hd₀, one_mulVec, show FD.cc (k : E) = k by simp [FD.cc], mul_comm (k : E)])
  have hU' : ∀ x y, FD.herm G (γ *ᵥ x) (γ *ᵥ y) = FD.herm G x y := hU
  have hd := isUnit_det hdet hU'
  obtain ⟨N, g, hN, hg⟩ := exists_scaled_map ((Matrix.toLin' γ).restrictScalars (𝓞 E) ∘ₗ φ) φ₀ inj₀ span₀
  have hg' : ∀ x, φ₀ (g x) = (N : E) • γ *ᵥ φ x := hg
  have hE : ∀ x y, D₀.EF (g x) (g y) = (N : ℤ) ^ 2 * D.EF x y := fun x y => by
    have := hEF₀ (g x) (g y)
    rw [hg', hg', trace_nsmul, hU', ← hEF] at this
    exact_mod_cast this
  refine split_of_scaled D D₀ ep eq Lp Lm ho rp rm sp sm N hN g ?_ hE fun x => ?_
  · refine (injective_iff_map_eq_zero g).2 fun x hx => D.unimod.1 ?_
    ext y
    have := hE x y
    rw [hx, map_zero, LinearMap.zero_apply] at this
    rw [map_zero, LinearMap.zero_apply]
    exact (mul_eq_zero.1 this.symm).resolve_left (by positivity)
  · obtain ⟨c, hc⟩ := hγ _ ⟨x, rfl⟩
    have e : γ *ᵥ φ c = π *ᵥ (γ *ᵥ φ x) := by
      rw [hc, mulVec_mulVec, mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv _ hd,
        Matrix.one_mul]
    have e2 : π *ᵥ (γ *ᵥ φ c) = γ *ᵥ φ c := by rw [e, mulVec_mulVec, π1]
    refine ⟨c, (π4 _).1 ?_, π5 _ ?_⟩
    · rw [hg', mulVec_smul, e2]
    · rw [hg', mulVec_smul, map_sub, mulVec_sub, mulVec_sub, e2, e, sub_self, smul_zero]

end GlobalTheory.SplitGenus
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HermitianLatticeSignatureSplitOfIndefiniteStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianLatticeSignatureSplit_of_indefinite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), (∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0) → 3 ≤ D.p + D.q → 1 ≤ D.p → 1 ≤ D.q → SplitLat D := by
  first | exact @GlobalTheory.SplitGenus.splitLat_of_indefinite | exact GlobalTheory.SplitGenus.splitLat_of_indefinite | (intros; apply GlobalTheory.SplitGenus.splitLat_of_indefinite <;> assumption)
end
