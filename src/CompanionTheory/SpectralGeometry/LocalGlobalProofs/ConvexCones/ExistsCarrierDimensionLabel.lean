module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPosRatMultipleOfPosRealMultipleIntForm
public import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean

@[expose] public section

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.CellFaceOfFaceCut
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.CellFaceOfFaceCut
set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.CarDim GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.CellFaces

variable {O : Type} [CommRing O] {bar : O → O} {ψ : InvFun O}
  {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]


omit [Module O X] [Module.Finite O X] in
theorem apply_eq_sum_of_toReal {m : ℕ} {β : LinearMap.BilinForm ℤ X} {u : Fin m → LinearMap.BilinForm ℤ X}
    {c : Fin m → ℝ} (hβ : toReal β = ∑ i, c i • toReal (u i)) (F : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) :
    (F β : ℝ) = ∑ i, c i * (F (u i) : ℝ) := by
  have hpt : ∀ a b : X, ((β a b : ℤ) : ℝ) = ∑ i, c i * ((u i a b : ℤ) : ℝ) := by
    intro a b
    have := congrArg (fun B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ => B a b) hβ
    simpa [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply] using this
  have hπ : ∀ (π : ℝ →ₗ[ℚ] ℚ) (x : ℝ) (n : ℤ), π (x * (n : ℝ)) = π x * (n : ℚ) := by
    intro π x n
    rw [mul_comm, ← zsmul_eq_mul, map_zsmul, zsmul_eq_mul, mul_comm]
  have hrat : ∀ π : ℝ →ₗ[ℚ] ℚ, π 1 * (F β : ℚ) = ∑ i, π (c i) * (F (u i) : ℚ) := by
    intro π
    have hq : ∀ a b : X, π 1 * ((β a b : ℤ) : ℚ) = ∑ i, π (c i) * ((u i a b : ℤ) : ℚ) := by
      intro a b
      have h1 := congrArg π (hpt a b)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← one_mul ((β a b : ℤ) : ℝ), hπ, map_sum] at h1
      simpa only [hπ] using h1
    obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors ℤ)
      (Finset.univ : Finset (Option (Fin m))) (fun o : Option (Fin m) => o.elim (π 1) (fun i => π (c i)))
    choose z hz using fun o => hb o (Finset.mem_univ o)
    have hz' : ∀ o, ((z o : ℤ) : ℚ) = ((b : ℤ) : ℚ) * o.elim (π 1) (fun i => π (c i)) := by
      intro o
      simpa [zsmul_eq_mul] using hz o
    have hint : z none • β = ∑ i, z (some i) • u i := by
      ext x y
      apply Int.cast_injective (α := ℚ)
      simp only [LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul, Int.cast_mul, Int.cast_sum, hz',
        Option.elim_none, Option.elim_some]
      rw [mul_assoc, hq x y, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    have h2 := congrArg (fun β => ((F β : ℤ) : ℚ)) hint
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_zsmul, map_sum, smul_eq_mul, Int.cast_mul, Int.cast_sum, hz', Option.elim_none,
      Option.elim_some] at h2
    have hb0 : ((b : ℤ) : ℚ) ≠ 0 := by exact_mod_cast nonZeroDivisors.ne_zero b.2
    apply mul_left_cancel₀ hb0
    rw [Finset.mul_sum, ← mul_assoc, h2]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hr : ∑ i, c i * (F (u i) : ℝ) - (F β : ℝ) = 0 := by
    refine (Module.forall_dual_apply_eq_zero_iff ℚ _).mp fun π => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_sum, ← one_mul ((F β : ℤ) : ℝ), hπ]
    simp only [hπ]
    rw [← hrat π]
    ring
  linarith

theorem est_at {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} {N : ℕ} {ℓ h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ}
    (hstr : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → N * ψ.evalZ β = ℓ β →
      ∃ (k : ℕ) (c : Fin m → ℕ), 0 < k ∧ k • β = ∑ i, c i • γ i)
    (hle : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → N * ψ.evalZ β ≤ ℓ β)
    (hγ : ∀ j, 0 ≤ h (γ j)) {C : ℕ} (hC : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → -(h β : ℝ) ≤ C * ℓ β)
    {u : LinearMap.BilinForm ℤ X} (hu : u ∈ balForms bar X) (hp : ∀ y, 0 ≤ u y y) (n : ℤ) (hn : ψ.evalZ u = n)
    {B0 L : ℝ} (hb : N * ψ.evalZ u ≤ B0) (hB0 : 0 ≤ B0) (hL : C * (B0 + 1) + C ≤ L) :
    L * (N * ψ.evalZ u) ≤ L * ℓ u + h u := by
  have hle' := hle u hu hp
  have hhC := hC u hu hp
  rw [hn] at hle' hb ⊢
  have hleZ : (N : ℤ) * n ≤ ℓ u := by exact_mod_cast hle'
  have hC0 : (0 : ℝ) ≤ C := Nat.cast_nonneg C
  rcases hleZ.lt_or_eq with hlt | heq
  · have h1 : ((N : ℤ) * n + 1 : ℤ) ≤ ℓ u := hlt
    have h1R : (N : ℝ) * n + 1 ≤ (ℓ u : ℝ) := by exact_mod_cast h1
    have hLC : (C : ℝ) * (B0 + 1) ≤ L - C := by linarith
    have hLC0 : (0 : ℝ) ≤ L - C := le_trans (mul_nonneg hC0 (by linarith)) hLC
    have k1 : (L - C) * 1 ≤ (L - C) * ((ℓ u : ℝ) - N * n) :=
      mul_le_mul_of_nonneg_left (by linarith) hLC0
    have k2 : (C : ℝ) * (N * n) ≤ C * B0 := mul_le_mul_of_nonneg_left hb hC0
    nlinarith [k1, k2, hhC, hLC]
  · have heqR : (N : ℝ) * ψ.evalZ u = ℓ u := by rw [hn]; exact_mod_cast heq
    obtain ⟨k, c, hk, hkc⟩ := hstr u hu hp heqR
    have hsum : (k : ℤ) * h u = ∑ i, (c i : ℤ) * h (γ i) := by
      have := congrArg h hkc
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [map_nsmul, map_sum, nsmul_eq_mul] using this
    have hnn : 0 ≤ ∑ i, (c i : ℤ) * h (γ i) :=
      Finset.sum_nonneg fun i _ => mul_nonneg (Int.natCast_nonneg _) (hγ i)
    have hhu : 0 ≤ h u := by
      by_contra hneg
      have : (k : ℤ) * h u < 0 := mul_neg_of_pos_of_neg (by exact_mod_cast hk) (not_le.mp hneg)
      linarith
    have hhuR : (0 : ℝ) ≤ h u := by exact_mod_cast hhu
    have hℓR : ((ℓ u : ℤ) : ℝ) = (N : ℝ) * n := by exact_mod_cast heq.symm
    rw [hℓR]
    linarith

theorem isCell_comp : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (ψ : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X], IsPolyFanOn bar ψ X → GlobalTheory.PolFan.Dominates bar X → ∀ (m m' : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsCell bar ψ γ → IsFaceCut γ s h → IsCell bar ψ (fun i => γ (s i)) := by
  intro O _ _ _ _ bar _ ψ X _ _ _ hfan hdom m m' γ s h hcell hface
  obtain ⟨hmem, hnn, hlin, hstrict⟩ := hcell
  obtain ⟨N, ℓ, hN, hℓγ, hle, hstr⟩ := hstrict
  obtain ⟨hh0, hhz⟩ := hface
  have reidx : ∀ (c' : Fin m' → ℝ) (f : Fin m → ℝ),
      ∑ j, Function.extend s c' 0 j * f j = ∑ i, c' i * f (s i) := by
    intro c' f
    refine ((Finset.sum_subset (Finset.subset_univ (Finset.univ.map s)) fun j _ hj => ?_).symm.trans
      (Finset.sum_map Finset.univ s (fun j => Function.extend s c' 0 j * f j))).trans ?_
    · rw [Function.extend_apply' _ _ _ (by simpa using hj), Pi.zero_apply, zero_mul]
    · exact Finset.sum_congr rfl fun i _ => by rw [s.injective.extend_apply]
  have hext_nn : ∀ c' : Fin m' → ℝ, (∀ i, 0 ≤ c' i) → ∀ j, 0 ≤ Function.extend s c' 0 j := by
    intro c' hc' j
    by_cases hj : ∃ i, s i = j
    · obtain ⟨i, rfl⟩ := hj
      rw [s.injective.extend_apply]
      exact hc' i
    · rw [Function.extend_apply' _ _ _ hj]
      exact le_refl _
  have hlin' : ψ.LinearOn (fun i => γ (s i)) := by
    intro c' hc'
    have hl := hlin (Function.extend s c' 0) (hext_nn c' hc')
    show ψ.eval X (fun a b => ∑ i, c' i * ((γ (s i) a b : ℤ) : ℝ)) = ∑ i, c' i * ψ.evalZ (γ (s i))
    have e1 : (fun a b => ∑ i, c' i * ((γ (s i) a b : ℤ) : ℝ)) =
        (fun a b => ∑ j, Function.extend s c' 0 j * ((γ j a b : ℤ) : ℝ)) := by
      funext a b
      rw [reidx c' (fun j => ((γ j a b : ℤ) : ℝ))]
    rw [e1, hl, reidx c' (fun j => ψ.evalZ (γ j))]
  have hpos : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → β ≠ 0 → 0 < ℓ β := by
    intro β hβ hp hne
    have h1 := hle β hβ hp
    have h2 := hfan.pos β hβ hp hne
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    have : (0 : ℝ) < ℓ β := lt_of_lt_of_le (mul_pos hNR h2) h1
    exact_mod_cast this
  obtain ⟨C, hC⟩ := hdom ℓ (-h) hpos
  have hCR : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → -(h β : ℝ) ≤ C * ℓ β := by
    intro β hβ hp
    have := hC β hβ hp
    rw [LinearMap.neg_apply] at this
    exact_mod_cast this
  obtain ⟨S, hSfin, hcov⟩ := hfan.finite
  set B0 : ℝ := ∑ x ∈ hSfin.toFinset, |(N : ℝ) * ψ.evalZ x| with hB0def
  have hB0 : 0 ≤ B0 := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hB0ge : ∀ x ∈ S, (N : ℝ) * ψ.evalZ x ≤ B0 := fun x hx =>
    (le_abs_self _).trans (Finset.single_le_sum (f := fun x => |(N : ℝ) * ψ.evalZ x|)
      (fun _ _ => abs_nonneg _) (hSfin.mem_toFinset.mpr hx))
  have key : ∀ L : ℝ, (C : ℝ) * (B0 + 1) + C ≤ L → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) →
      L * (N * ψ.evalZ β) ≤ L * ℓ β + h β := by
    intro L hL β hβ hp
    have hB : toReal β ∈ psdCone (bar := bar) (X := X) := by
      have := GlobalTheory.PolFan.ConeSub.sum_smul_toReal_mem_psdCone O bar X 1 (fun _ => β) (fun _ => 1)
        (fun _ => hβ) (fun _ => hp) (fun _ => zero_le_one)
      simpa using this
    obtain ⟨e, k, γ', c, hcell', hS', hc', heq⟩ := hcov _ hB
    have hsurj : Function.Surjective (e.symm : X →ₗ[O] X) := fun x => ⟨e x, by simp⟩
    have hcellu : IsCell bar ψ (fun i => pull (e.symm : X →ₗ[O] X) (γ' i)) := isCell_pull_equiv hcell' e.symm
    have hpt : ∀ a b : X, ((β a b : ℤ) : ℝ) = ∑ i, c i * ((pull (e.symm : X →ₗ[O] X) (γ' i) a b : ℤ) : ℝ) := by
      intro a b
      have := congrArg (fun B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ => B (e.symm a) (e.symm b)) heq
      simpa [pullR, pull_apply, toReal_apply, LinearMap.sum_apply] using this
    have hrel : toReal β = ∑ i, c i • toReal (pull (e.symm : X →ₗ[O] X) (γ' i)) := by
      ext a b
      simpa [toReal_apply, LinearMap.sum_apply] using hpt a b
    have hℓ := apply_eq_sum_of_toReal hrel ℓ
    have hh := apply_eq_sum_of_toReal hrel h
    have hφ : ψ.evalZ β = ∑ i, c i * ψ.evalZ (pull (e.symm : X →ₗ[O] X) (γ' i)) := by
      rw [← hcellu.linear c hc']
      show ψ.eval X (fun a b => ((β a b : ℤ) : ℝ)) = _
      congr 1
      funext a b
      exact hpt a b
    have hest : ∀ i, L * (N * ψ.evalZ (pull (e.symm : X →ₗ[O] X) (γ' i))) ≤
        L * ℓ (pull (e.symm : X →ₗ[O] X) (γ' i)) + h (pull (e.symm : X →ₗ[O] X) (γ' i)) := by
      intro i
      obtain ⟨n, hn⟩ := hfan.integral _ (hcellu.mem i) (hcellu.nonneg i)
      have hbi : (N : ℝ) * ψ.evalZ (pull (e.symm : X →ₗ[O] X) (γ' i)) ≤ B0 := by
        rw [evalZ_pull ψ hsurj]
        exact hB0ge _ (hS' i)
      exact est_at (bar := bar) hstr hle hh0 hCR (hcellu.mem i) (hcellu.nonneg i) n hn hbi hB0 hL
    calc L * (N * ψ.evalZ β)
        = ∑ i, c i * (L * (N * ψ.evalZ (pull (e.symm : X →ₗ[O] X) (γ' i)))) := by
          rw [hφ, Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ ≤ ∑ i, c i * (L * ℓ (pull (e.symm : X →ₗ[O] X) (γ' i)) + h (pull (e.symm : X →ₗ[O] X) (γ' i))) :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hest i) (hc' i)
      _ = L * ℓ β + h β := by
          rw [hℓ, hh, Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ => by ring
  have hL0 := Nat.le_ceil ((C : ℝ) * (B0 + 1) + C)
  set L0 : ℕ := ⌈(C : ℝ) * (B0 + 1) + C⌉₊ with hL0def
  have reidxN : ∀ c : Fin m → ℕ, (∀ j, j ∉ Set.range s → c j = 0) →
      ∑ j, c j • γ j = ∑ i, c (s i) • γ (s i) := by
    intro c hc
    exact (Finset.sum_subset (Finset.subset_univ (Finset.univ.map s)) fun j _ hj => by
      rw [hc j (by simpa using hj), zero_smul]).symm.trans (Finset.sum_map Finset.univ s (fun j => c j • γ j))
  refine ⟨fun i => hmem (s i), fun i => hnn (s i), hlin', ?_⟩
  unfold GlobalTheory.PolFan.IsStrict
  refine ⟨(L0 + 1) * N, ((L0 + 1 : ℕ) : ℤ) • ℓ + h, Nat.mul_pos (Nat.succ_pos _) hN, ?_, ?_, ?_⟩
  · intro i
    have hz : h (γ (s i)) = 0 := (hhz (s i)).mpr ⟨i, rfl⟩
    simp only [LinearMap.add_apply, LinearMap.smul_apply, hz, add_zero, smul_eq_mul]
    push_cast
    rw [hℓγ (s i)]
    ring
  · intro β hβ hp
    have hA := key ((L0 + 1 : ℕ) : ℝ) (by push_cast; linarith) β hβ hp
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    push_cast at hA ⊢
    nlinarith [hA]
  · intro β hβ hp heqβ
    have hA := key ((L0 + 1 : ℕ) : ℝ) (by push_cast; linarith) β hβ hp
    have hB := key (L0 : ℝ) hL0 β hβ hp
    have hle' := hle β hβ hp
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at heqβ
    push_cast at heqβ hA
    have hd : (N : ℝ) * ψ.evalZ β = ℓ β := by nlinarith [hB, heqβ, hle']
    have hh0β : (h β : ℝ) = 0 := by nlinarith [hB, heqβ, hd]
    obtain ⟨k, c, hk, hkc⟩ := hstr β hβ hp hd
    have hsum : (k : ℤ) * h β = ∑ j, (c j : ℤ) * h (γ j) := by
      have := congrArg h hkc
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [map_nsmul, map_sum, nsmul_eq_mul] using this
    have hhβ : h β = 0 := by exact_mod_cast hh0β
    rw [hhβ, mul_zero] at hsum
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => mul_nonneg (Int.natCast_nonneg (c j)) (hh0 j))).mp hsum.symm
    have hc0 : ∀ j, j ∉ Set.range s → c j = 0 := by
      intro j hj
      have h2 : h (γ j) ≠ 0 := fun h0 => hj ((hhz j).mp h0)
      rcases mul_eq_zero.mp (hterm j (Finset.mem_univ j)) with h3 | h3
      · exact_mod_cast h3
      · exact absurd h3 h2
    exact ⟨k, fun i => c (s i), hk, hkc.trans (reidxN c hc0)⟩

end GlobalTheory.CompanionTheory.Ar.Fan.CellFaces
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.CellFaceOfFaceCutStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.CarDim GlobalTheory.CompanionTheory.Ar.Fan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cell_face_of_face_cut : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (ψ : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X], IsPolyFanOn bar ψ X → GlobalTheory.PolFan.Dominates bar X → ∀ (m m' : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsCell bar ψ γ → IsFaceCut γ s h → IsCell bar ψ (fun i => γ (s i)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.CellFaces.isCell_comp | exact GlobalTheory.CompanionTheory.Ar.Fan.CellFaces.isCell_comp | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.CellFaces.isCell_comp <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.CellOfQuotientCell
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.CellOfQuotientCell
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.CarDim GlobalTheory.CompanionTheory.Ar.Fan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fan.QuotientCell

theorem projective_quot_orad (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (X : Type)
    [AddCommGroup X] [Module O X] [Module.Finite O X] (β : LinearMap.BilinForm ℤ X) :
    Module.Projective O (X ⧸ (orad β : Submodule O X)) := by
  classical
  have hZ : ∀ n : ℤ, n ≠ 0 → ∀ y : X, n • y ∈ (orad β : Submodule O X) → y ∈ (orad β : Submodule O X) :=
    fun n hn y hy a z => by
      have h := hy a z
      rw [smul_comm, map_zsmul, LinearMap.smul_apply, smul_eq_mul] at h
      exact (mul_eq_zero.1 h).resolve_left hn
  have hO : ∀ a : O, a ≠ 0 → ∀ y : X, a • y ∈ (orad β : Submodule O X) → y ∈ (orad β : Submodule O X) := by
    intro a ha y hy
    have hne : (Ideal.span {a}).comap (algebraMap ℤ O) ≠ ⊥ :=
      Ideal.comap_ne_bot_of_integral_mem ha (Ideal.mem_span_singleton_self a) (Algebra.IsIntegral.isIntegral a)
    obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    obtain ⟨a', ha'⟩ := Ideal.mem_span_singleton'.1 (Ideal.mem_comap.1 hn)
    refine hZ n hn0 y fun b z => ?_
    have h := hy (b * a') z
    rw [mul_smul, smul_smul a' a y, ha', algebraMap_int_eq, eq_intCast, Int.cast_smul_eq_zsmul] at h
    exact h
  have htor : Submodule.torsion O (X ⧸ (orad β : Submodule O X)) = ⊥ := by
    refine (Submodule.eq_bot_iff _).2 fun u hu => ?_
    obtain ⟨⟨a, ha⟩, hau⟩ := (Submodule.mem_torsion_iff u).1 hu
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    rw [Submonoid.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hau
    rw [Submodule.Quotient.mk_eq_zero]
    exact hO a (nonZeroDivisors.ne_zero ha) y hau
  have : Module.Flat O (X ⧸ (orad β : Submodule O X)) := IsDedekindDomain.flat_iff_torsion_eq_bot.2 htor
  have : Module.FinitePresentation O (X ⧸ (orad β : Submodule O X)) := Module.finitePresentation_of_finite _ _
  exact Module.Flat.projective_of_finitePresentation

theorem cell_of_quot_cell : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (ψ : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], IsPolyFanOn bar ψ X → (∀ (m m' : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsCell bar ψ γ → IsFaceCut γ s h → IsCell bar ψ (fun i => γ (s i))) → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → ∀ (m' : ℕ) (δ : Fin m' → LinearMap.BilinForm ℤ (X ⧸ (orad β : Submodule O X))), IsCell bar ψ δ → InRCone (fun i => pull (orad β : Submodule O X).mkQ (δ i)) β → ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ ∧ InRCone γ β ∧ genRank γ ≤ genRank δ := by
  intro O _ _ _ _ bar hCM ψ X _ _ _ _ hfan hface β hβ hp m' δ hδ hin
  classical
  have : Module.Projective O (X ⧸ (orad (O := O) β)) := projective_quot_orad O X β
  obtain ⟨t, ht⟩ := Module.projective_lifting_property (orad (O := O) β).mkQ LinearMap.id (orad (O := O) β).mkQ_surjective
  have htt : ∀ u, (orad (O := O) β).mkQ (t u) = u := fun u => LinearMap.congr_fun ht u
  have htt' : ∀ u, (Submodule.Quotient.mk (t u) : X ⧸ (orad (O := O) β)) = u := htt
  have hπ : Function.Surjective (orad (O := O) β).mkQ := (orad (O := O) β).mkQ_surjective

  have desc : ∀ β' : LinearMap.BilinForm ℤ X, β' ∈ balForms bar X → (∀ k ∈ (orad (O := O) β), ∀ y, β' k y = 0) →
      pull (orad (O := O) β).mkQ (pull t β') = β' := by
    intro β' hb hv
    refine LinearMap.ext₂ fun a b => ?_
    have ha : a - t ((orad (O := O) β).mkQ a) ∈ (orad (O := O) β) := by
      rw [← Submodule.Quotient.mk_eq_zero (orad (O := O) β), ← Submodule.mkQ_apply, map_sub, htt, sub_self]
    have hb' : b - t ((orad (O := O) β).mkQ b) ∈ (orad (O := O) β) := by
      rw [← Submodule.Quotient.mk_eq_zero (orad (O := O) β), ← Submodule.mkQ_apply, map_sub, htt, sub_self]
    have e1 := hv _ ha b
    have e2 := hv _ hb' (t ((orad (O := O) β).mkQ a))
    rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at e1 e2
    rw [pull_apply, pull_apply, hb.1 (t _) (t _), ← e2, hb.1 b (t ((orad (O := O) β).mkQ a)), ← e1]
  have hbK : ∀ k ∈ (orad (O := O) β), ∀ y, β k y = 0 := fun k hk y => by simpa using (mem_orad.1 hk) 1 y

  have hmem : toReal β ∈ psdCone (bar := bar) (X := X) := by
    have := ConeSub.sum_smul_toReal_mem_psdCone O bar X 1 ![β] ![1] (fun i => by fin_cases i; exact hβ)
      (fun i y => by fin_cases i; exact hp y) (fun i => by fin_cases i; norm_num)
    simpa using this
  obtain ⟨S, -, hS⟩ := hfan.finite
  obtain ⟨e, m, γ, d, hγ, -, hd, he⟩ := hS _ hmem
  set σ : Fin m → LinearMap.BilinForm ℤ X := fun i => pull e.symm.toLinearMap (γ i) with hσdef
  have hσ : IsCell bar ψ σ := isCell_pull_equiv hγ e.symm
  have hβσ : toReal β = ∑ i, d i • toReal (σ i) := LinearMap.ext₂ fun a b => by
    have := LinearMap.congr_fun₂ he (e.symm a) (e.symm b)
    simpa [LinearMap.sum_apply, hσdef] using this

  obtain ⟨Nδ, ℓδ, hNδ, hℓδ1, hℓδ2, hℓδ3⟩ := hδ.strict
  obtain ⟨Nσ, ℓσ, hNσ, hℓσ1, hℓσ2, hℓσ3⟩ := hσ.strict
  obtain ⟨hK, hKt⟩ := exists_radical_test bar (orad (O := O) β)
  let g : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ := (Nσ : ℤ) • (ℓδ ∘ₗ pullLin t) - (Nδ : ℤ) • ℓσ
  have hg : ∀ β', g β' = Nσ * ℓδ (pull t β') - Nδ * ℓσ β' := fun β' => by simp [g]
  set M : ℤ := ∑ j, |g (σ j)| + 1 with hM
  have hMj : ∀ j, |g (σ j)| < M := fun j => by
    have := Finset.single_le_sum (f := fun j => |g (σ j)|) (fun j _ => abs_nonneg _) (Finset.mem_univ j)
    linarith
  let hh : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ := g + M • hK
  have hhv : ∀ β', hh β' = g β' + M * hK β' := fun β' => by simp [hh]
  have factA : ∀ j, hK (σ j) = 0 →
      (g (σ j) : ℝ) = Nσ * ((ℓδ (pull t (σ j)) : ℝ) - Nδ * ψ.evalZ (pull t (σ j))) := by
    intro j hj
    have hv := (hKt _ (hσ.mem j) (hσ.nonneg j)).2.1 hj
    have e1 : ψ.evalZ (σ j) = ψ.evalZ (pull t (σ j)) := by
      rw [← evalZ_pull ψ hπ (pull t (σ j)), desc _ (hσ.mem j) hv]
    rw [hg]
    push_cast
    rw [hℓσ1 j, e1]
    ring
  have hpos : ∀ j, hK (σ j) ≠ 0 → 0 < hh (σ j) := by
    intro j hj
    rw [hhv]
    have h0 := (hKt _ (hσ.mem j) (hσ.nonneg j)).1
    have h1 : 1 ≤ hK (σ j) := by omega
    have h2 := hMj j
    have hM0 : 0 ≤ M := (abs_nonneg _).trans h2.le
    have h3 := mul_le_mul_of_nonneg_left h1 hM0
    have h4 := neg_abs_le (g (σ j))
    linarith
  have hnn : ∀ j, 0 ≤ hh (σ j) := by
    intro j
    by_cases hj : hK (σ j) = 0
    · rw [hhv, hj, mul_zero, add_zero]
      have hA := factA j hj
      have h2 := hℓδ2 (pull t (σ j)) (pull_mem t (hσ.mem j)) (fun y => hσ.nonneg j _)
      have h3 : (0 : ℝ) ≤ g (σ j) := by
        rw [hA]
        exact mul_nonneg (Nat.cast_nonneg _) (by linarith)
      exact_mod_cast h3
    · exact (hpos j hj).le

  set F : Finset (Fin m) := Finset.univ.filter fun j => hh (σ j) = 0 with hF
  let s : Fin F.card ↪ Fin m := (F.orderEmbOfFin rfl).toEmbedding
  have hs : ∀ j, j ∈ Set.range s ↔ hh (σ j) = 0 := fun j => by
    have : Set.range s = (F : Set (Fin m)) := Finset.range_orderEmbOfFin F rfl
    rw [this]
    simp [hF]
  have hcut : IsFaceCut σ s hh := ⟨hnn, fun j => (hs j).symm⟩
  have hσs : IsCell bar ψ (fun i => σ (s i)) := hface m F.card σ s hh hσ hcut

  have hKb : hK β = 0 := (hKt β hβ hp).2.2 hbK
  have hψβ : ψ.evalZ β = ψ.evalZ (pull t β) := by
    rw [← evalZ_pull ψ hπ (pull t β), desc β hβ hbK]
  obtain ⟨c, hc, hcβ⟩ := hin
  have hcβ1 : toReal (pull t β) = ∑ i, c i • toReal (δ i) := LinearMap.ext₂ fun a b => by
    have := LinearMap.congr_fun₂ hcβ (t a) (t b)
    simpa [LinearMap.sum_apply, htt, htt'] using this
  have hgβ : g β = 0 := by
    have e1 := intLin_eq_of_inCone ψ hσ.linear hℓσ1 hd hβσ
    have e2 := intLin_eq_of_inCone ψ hδ.linear hℓδ1 hc hcβ1
    have : (g β : ℝ) = 0 := by
      rw [hg]
      push_cast
      rw [e1, e2, hψβ]
      ring
    exact_mod_cast this
  have hhβ : hh β = 0 := by rw [hhv, hgβ, hKb]; simp
  have hsum := intLin_eq_sum_of_toReal σ d β hh hβσ
  rw [hhβ, Int.cast_zero] at hsum
  have hzero : ∀ j, d j * (hh (σ j) : ℝ) = 0 := by
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_nonneg (hd j) (by exact_mod_cast hnn j))).1 hsum.symm
    exact fun j => this j (Finset.mem_univ j)
  have hdz : ∀ j, j ∉ Set.range s → d j = 0 := fun j hj => by
    have h0 : (hh (σ j) : ℝ) ≠ 0 := by exact_mod_cast fun h => hj ((hs j).2 h)
    exact (mul_eq_zero.1 (hzero j)).resolve_right h0
  have hcone : InRCone (fun i => σ (s i)) β := by
    refine ⟨fun i => d (s i), fun i => hd _, ?_⟩
    rw [hβσ]
    exact (Fintype.sum_of_injective s s.injective _ _ (fun j hj => by rw [hdz j hj, zero_smul]) fun i => rfl).symm

  have hspan : ∀ i, ∃ k : ℕ, 0 < k ∧ k • σ (s i) ∈ Submodule.span ℤ (Set.range fun i => pull (orad (O := O) β).mkQ (δ i)) := by
    intro i
    have hj0 : hh (σ (s i)) = 0 := (hs (s i)).1 ⟨i, rfl⟩
    have hKj : hK (σ (s i)) = 0 := by
      by_contra hne
      exact (hpos _ hne).ne' hj0
    have hgj : g (σ (s i)) = 0 := by
      rw [hhv, hKj, mul_zero, add_zero] at hj0
      exact hj0
    have hA := factA _ hKj
    rw [hgj, Int.cast_zero] at hA
    have heq : (Nδ : ℝ) * ψ.evalZ (pull t (σ (s i))) = ℓδ (pull t (σ (s i))) := by
      have hN : (Nσ : ℝ) ≠ 0 := by exact_mod_cast hNσ.ne'
      have := (mul_eq_zero.1 hA.symm).resolve_left hN
      linarith
    obtain ⟨k, c', hk, hkc⟩ := hℓδ3 _ (pull_mem t (hσ.mem (s i))) (fun y => hσ.nonneg (s i) _) heq
    refine ⟨k, hk, ?_⟩
    have hv := (hKt _ (hσ.mem (s i)) (hσ.nonneg (s i))).2.1 hKj
    have e3 : k • σ (s i) = ∑ l, c' l • pull (orad (O := O) β).mkQ (δ l) := by
      have e := congrArg (pullLin (orad (O := O) β).mkQ) hkc
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_nsmul, map_sum, pullLin_apply] at e
      rw [desc _ (hσ.mem (s i)) hv] at e
      exact e
    rw [e3]
    exact Submodule.sum_mem _ fun l _ => nsmul_mem (Submodule.subset_span (Set.mem_range_self l)) _
  refine ⟨F.card, fun i => σ (s i), hσs, hcone, ?_⟩
  calc genRank (fun i => σ (s i)) ≤ genRank (fun i => pull (orad (O := O) β).mkQ (δ i)) :=
        genRank_le_of_smul_mem_span _ _ hspan
    _ = genRank δ := genRank_pull hπ δ

end GlobalTheory.CompanionTheory.Ar.Fan.QuotientCell
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.CellOfQuotientCellStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.CarDim GlobalTheory.CompanionTheory.Ar.Fan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cell_of_quotient_cell : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (ψ : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], IsPolyFanOn bar ψ X → (∀ (m m' : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsCell bar ψ γ → IsFaceCut γ s h → IsCell bar ψ (fun i => γ (s i))) → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → ∀ (m' : ℕ) (δ : Fin m' → LinearMap.BilinForm ℤ (X ⧸ (orad β : Submodule O X))), IsCell bar ψ δ → InRCone (fun i => pull (orad β : Submodule O X).mkQ (δ i)) β → ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ ∧ InRCone γ β ∧ genRank γ ≤ genRank δ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.QuotientCell.cell_of_quot_cell | exact GlobalTheory.CompanionTheory.Ar.Fan.QuotientCell.cell_of_quot_cell | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.QuotientCell.cell_of_quot_cell <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.CellOfQuotientRadicalCone
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.CellOfQuotientRadicalCone
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.CarDim GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.QuotientCellRadical

theorem exists_cell_quot_orad_of_inRCone : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (ψ : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X], (∀ (m m' : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsCell bar ψ γ → IsFaceCut γ s h → IsCell bar ψ (fun i => γ (s i))) → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ → InRCone γ β → ∃ (m' : ℕ) (δ : Fin m' → LinearMap.BilinForm ℤ (X ⧸ (orad β : Submodule O X))), IsCell bar ψ δ ∧ InRCone (fun i => pull (orad β : Submodule O X).mkQ (δ i)) β ∧ genRank δ ≤ genRank γ := by
  intro O _ _ _ _ bar _hCM ψ X _ _ _ hface β _hβ _hβpsd m γ hcell hcone
  classical
  have mem_bal : ∀ {Y : Type} [AddCommGroup Y] [Module O Y] (f : LinearMap.BilinForm ℤ Y),
      f ∈ GlobalTheory.PolFan.balForms bar Y ↔
        ((∀ y z, f y z = f z y) ∧ ∀ (a : O) (y z : Y), f (a • y) z = f y (bar a • z)) :=
    fun _ => Iff.rfl
  have psd_zero : ∀ f : LinearMap.BilinForm ℤ X, f ∈ GlobalTheory.PolFan.balForms bar X →
      (∀ y, 0 ≤ f y y) → ∀ x, f x x = 0 → ∀ y, f x y = 0 := by
    intro f hf hfp x hx y
    have hsym : f y x = f x y := ((mem_bal f).1 hf).1 y x
    by_contra hne
    have expand : ∀ n : ℤ, f (n • x + y) (n • x + y) =
        n * n * f x x + n * f x y + n * f y x + f y y := by
      intro n
      simp only [map_add (f := _), map_zsmul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
      ring
    have key := hfp ((-(f y y + 1) * f x y) • x + y)
    rw [expand, hx, hsym] at key
    have h1 : 0 < f x y * f x y := mul_self_pos.2 hne
    have h2 : 1 ≤ f x y * f x y := by simpa using Int.add_one_le_iff.2 h1
    have h0 := hfp y
    nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ f y y + 1) (by linarith : (0:ℤ) ≤ f x y * f x y - 1)]
  obtain ⟨c, hc0, hcsum⟩ := hcone
  have hval : ∀ x y, ((β x y : ℤ) : ℝ) = ∑ i, c i * ((γ i x y : ℤ) : ℝ) := by
    intro x y
    have := congrArg (fun L : X →ₗ[ℤ] X →ₗ[ℤ] ℝ => L x y) hcsum
    simpa [GlobalTheory.PolFan.toReal] using this
  set K : Submodule O X := GlobalTheory.PolFan.CarDim.orad β with hK
  have hKβ : ∀ x ∈ K, β x x = 0 := by
    intro x hx
    have := (GlobalTheory.PolFan.CarDim.mem_orad (O := O)).1 hx 1 x
    simpa using this
  let P : Fin m → Prop := fun j => ∀ x ∈ K, ∀ y, γ j x y = 0
  have hpos : ∀ j, 0 < c j → P j := by
    intro j hcj x hx
    apply psd_zero (γ j) (hcell.mem j) (hcell.nonneg j) x
    have hsum : ∑ i, c i * ((γ i x x : ℤ) : ℝ) = 0 := by
      rw [← hval, hKβ x hx]
      simp
    have hnn : ∀ i ∈ Finset.univ, 0 ≤ c i * ((γ i x x : ℤ) : ℝ) := fun i _ =>
      mul_nonneg (hc0 i) (by exact_mod_cast hcell.nonneg i x)
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum j (Finset.mem_univ j)
    rcases mul_eq_zero.1 hz with h | h
    · exact absurd h hcj.ne'
    · exact_mod_cast h
  have hw : ∀ j, ∃ x ∈ K, (¬ P j → 0 < γ j x x) := by
    intro j
    by_cases hj : P j
    · exact ⟨0, K.zero_mem, fun h => absurd hj h⟩
    · simp only [P, not_forall] at hj
      obtain ⟨x, hx, y, hxy⟩ := hj
      refine ⟨x, hx, fun _ => ?_⟩
      rcases (hcell.nonneg j x).lt_or_eq with h | h
      · exact h
      · exact absurd (psd_zero (γ j) (hcell.mem j) (hcell.nonneg j) x h.symm y) hxy
  choose w hwK hwpos using hw
  let h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ :=
    { toFun := fun f => ∑ j, f (w j) (w j)
      map_add' := fun f g => by simp [Finset.sum_add_distrib]
      map_smul' := fun a f => by simp [Finset.mul_sum] }
  have hh : ∀ f, h f = ∑ j, f (w j) (w j) := fun _ => rfl
  let T : Finset (Fin m) := Finset.univ.filter P
  let s : Fin T.card ↪ Fin m := (T.orderEmbOfFin rfl).toEmbedding
  have hsT : ∀ j, j ∈ Set.range s ↔ P j := by
    intro j
    have hr : Set.range s = (T : Set (Fin m)) := Finset.range_orderEmbOfFin T rfl
    rw [hr]
    simp [T]
  have hPs : ∀ i, P (s i) := fun i => (hsT (s i)).1 ⟨i, rfl⟩
  have hfc : GlobalTheory.PolFan.IsFaceCut γ s h := by
    refine ⟨fun j => ?_, fun j => ?_⟩
    · rw [hh]
      exact Finset.sum_nonneg fun i _ => hcell.nonneg j (w i)
    · rw [hsT, hh]
      constructor
      · intro h0
        by_contra hj
        have hnn : ∀ i ∈ Finset.univ, 0 ≤ γ j (w i) (w i) := fun i _ => hcell.nonneg j (w i)
        have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h0 j (Finset.mem_univ j)
        exact (hwpos j hj).ne' this
      · intro hj
        exact Finset.sum_eq_zero fun i _ => hj (w i) (hwK i) (w i)
  have hcell' := hface m T.card γ s h hcell hfc
  have hvanl : ∀ i, ∀ x ∈ K, ∀ y, γ (s i) x y = 0 := fun i => hPs i
  have hvanr : ∀ i, ∀ x y, y ∈ K → γ (s i) x y = 0 := by
    intro i x y hy
    rw [((mem_bal _).1 (hcell.mem (s i))).1 x y]
    exact hPs i y hy x
  choose δ hδ using fun i =>
    GlobalTheory.PolFan.CarDim.exists_pull_mkQ_eq_of_vanish K (γ (s i)) (hvanl i) (hvanr i)
  have hr : Function.Surjective K.mkQ := K.mkQ_surjective
  have hδap : ∀ i x y, δ i (K.mkQ x) (K.mkQ y) = γ (s i) x y := by
    intro i x y
    rw [← hδ i]
    rfl
  have heZ : ∀ f : LinearMap.BilinForm ℤ (X ⧸ K),
      ψ.evalZ (GlobalTheory.PolFan.pull K.mkQ f) = ψ.evalZ f := by
    intro f
    exact ψ.eval_comp hr (fun a b => ((f a b : ℤ) : ℝ))
  have hpullbal : ∀ f ∈ GlobalTheory.PolFan.balForms bar (X ⧸ K),
      GlobalTheory.PolFan.pull K.mkQ f ∈ GlobalTheory.PolFan.balForms bar X := by
    intro f hf
    obtain ⟨hs, hb⟩ := (mem_bal f).1 hf
    refine (mem_bal _).2 ⟨fun y z => hs (K.mkQ y) (K.mkQ z), fun a y z => ?_⟩
    show f (K.mkQ (a • y)) (K.mkQ z) = f (K.mkQ y) (K.mkQ (bar a • z))
    rw [LinearMap.map_smul, LinearMap.map_smul]
    exact hb a (K.mkQ y) (K.mkQ z)
  have hpullpsd : ∀ f : LinearMap.BilinForm ℤ (X ⧸ K), (∀ q, 0 ≤ f q q) →
      ∀ y, 0 ≤ GlobalTheory.PolFan.pull K.mkQ f y y :=
    fun f hf y => hf (K.mkQ y)
  have hfun : (fun i => GlobalTheory.PolFan.pull K.mkQ (δ i)) = fun i => γ (s i) := funext hδ
  refine ⟨T.card, δ, ?_, ?_, ?_⟩
  · refine ⟨fun i => ?_, fun i q => ?_, ?_, ?_⟩
    · refine (mem_bal _).2 ⟨fun a b => ?_, fun a u v => ?_⟩
      · obtain ⟨x, rfl⟩ := hr a
        obtain ⟨y, rfl⟩ := hr b
        rw [hδap, hδap]
        exact ((mem_bal _).1 (hcell.mem (s i))).1 x y
      · obtain ⟨x, rfl⟩ := hr u
        obtain ⟨y, rfl⟩ := hr v
        rw [← LinearMap.map_smul, ← LinearMap.map_smul, hδap, hδap]
        exact ((mem_bal _).1 (hcell.mem (s i))).2 a x y
    · obtain ⟨y, rfl⟩ := hr q
      rw [hδap]
      exact hcell.nonneg (s i) y
    · intro c hc
      have key := hcell'.linear.eval_eq_sum (X₁ := X ⧸ K) hr
        (B := fun a b => ∑ i, c i * ((δ i a b : ℤ) : ℝ)) hc (fun a b => by simp only [hδap])
      rw [key]
      refine Finset.sum_congr rfl fun i _ => ?_
      show c i * ψ.evalZ (γ (s i)) = c i * ψ.evalZ (δ i)
      rw [← hδ i, heZ]
    · obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hcell'.strict
      refine ⟨N, ℓ.comp (GlobalTheory.PolFan.CarDim.pullLin K.mkQ), hN, fun i => ?_,
        fun β' hb hp => ?_, fun β' hb hp heq => ?_⟩
      · have h1i : ((ℓ (γ (s i)) : ℤ) : ℝ) = (N : ℝ) * ψ.evalZ (γ (s i)) := h1 i
        rw [LinearMap.comp_apply, GlobalTheory.PolFan.CarDim.pullLin_apply, hδ i, h1i, ← hδ i, heZ]
      · rw [LinearMap.comp_apply, GlobalTheory.PolFan.CarDim.pullLin_apply, ← heZ]
        exact h2 _ (hpullbal β' hb) (hpullpsd β' hp)
      · rw [LinearMap.comp_apply, GlobalTheory.PolFan.CarDim.pullLin_apply, ← heZ] at heq
        obtain ⟨k, c', hk, hkc⟩ := h3 _ (hpullbal β' hb) (hpullpsd β' hp) heq
        refine ⟨k, c', hk, ?_⟩
        have hkc' : k • GlobalTheory.PolFan.pull K.mkQ β' = ∑ i, c' i • γ (s i) := hkc
        apply GlobalTheory.PolFan.CarDim.pullLin_injective hr
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_nsmul, map_zsmul, LinearMap.map_smul_of_tower, map_sum,
          GlobalTheory.PolFan.CarDim.pullLin_apply]
        rw [hkc']
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hδ i]
  · rw [hfun]
    simp only [GlobalTheory.PolFan.InRCone]
    refine ⟨fun i => c (s i), fun i => hc0 _, ?_⟩
    rw [hcsum]
    have hmap : Finset.univ.map s = T := Finset.map_orderEmbOfFin_univ T rfl
    have e1 : (∑ i, c (s i) • GlobalTheory.PolFan.toReal (γ (s i))) =
        ∑ j ∈ T, c j • GlobalTheory.PolFan.toReal (γ j) := by
      exact (Finset.sum_map Finset.univ s (fun j => c j • GlobalTheory.PolFan.toReal (γ j))).symm.trans
        (by rw [hmap])
    rw [e1]
    symm
    apply Finset.sum_filter_of_ne
    intro j _ hne
    by_contra hj
    apply hne
    have hcj : c j = 0 := by
      rcases (hc0 j).lt_or_eq with h' | h'
      · exact absurd (hpos j h') hj
      · exact h'.symm
    rw [hcj, zero_smul]
  · rw [← GlobalTheory.PolFan.CarDim.genRank_pull hr δ, hfun]
    unfold GlobalTheory.PolFan.genRank
    haveI : Module.Finite ℤ (Submodule.span ℤ (Set.range γ)) :=
      Module.Finite.span_of_finite ℤ (Set.finite_range γ)
    exact Submodule.finrank_mono
      (Submodule.span_mono (Set.range_comp_subset_range s γ))

end GlobalTheory.CompanionTheory.Ar.Fan.QuotientCellRadical
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.CellOfQuotientRadicalConeStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.CarDim GlobalTheory.CompanionTheory.Ar.Fan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cell_of_quotient_radical_cone : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (ψ : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X], (∀ (m m' : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsCell bar ψ γ → IsFaceCut γ s h → IsCell bar ψ (fun i => γ (s i))) → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ → InRCone γ β → ∃ (m' : ℕ) (δ : Fin m' → LinearMap.BilinForm ℤ (X ⧸ (orad β : Submodule O X))), IsCell bar ψ δ ∧ InRCone (fun i => pull (orad β : Submodule O X).mkQ (δ i)) β ∧ genRank δ ≤ genRank γ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.QuotientCellRadical.exists_cell_quot_orad_of_inRCone | exact GlobalTheory.CompanionTheory.Ar.Fan.QuotientCellRadical.exists_cell_quot_orad_of_inRCone | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.QuotientCellRadical.exists_cell_quot_orad_of_inRCone <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.CarrierFunctionTwistedGalois
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.CarrierFunctionTwistedGalois
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.CarDim GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.TwistedCarrierFunction

theorem twEval_of_isTwG {O : Type} [CommRing O] {w0 : O} {ψ : InvFun O}
    (htw : IsTwG w0 ψ) {σ : O ≃+* O} (hσ : σ w0 = w0) : Tw.TwEval σ ψ := by
  intro Y Y' _ _ _ _ _ _ τ hτ B
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin' O Y
  have hsy : ∀ (a : O) (y : Y), τ.symm (σ a • y) = a • τ.symm y := fun a y => by
    apply τ.injective
    rw [hτ, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  let s' : (Fin n → O) →ₗ[O] Y' :=
    { toFun := fun x => τ.symm (s fun i => σ (x i))
      map_add' := fun x x' => by
        have : (fun i => σ ((x + x') i)) = (fun i => σ (x i)) + fun i => σ (x' i) := by ext i; simp
        rw [this, map_add (f := _), map_add (f := _)]
      map_smul' := fun c x => by
        have : (fun i => σ ((c • x) i)) = σ c • fun i => σ (x i) := by ext i; simp
        rw [this, map_smul, hsy]
        rfl }
  have hs' : Function.Surjective s' := fun y => by
    obtain ⟨x, hx⟩ := hs (τ y)
    refine ⟨fun i => σ.symm (x i), ?_⟩
    show τ.symm (s fun i => σ (σ.symm (x i))) = y
    simp only [RingEquiv.apply_symm_apply]
    rw [hx, AddEquiv.symm_apply_apply]
  rw [ψ.eval_eq hs', ψ.eval_eq hs]
  have := htw σ hσ n fun a b => B (s a) (s b)
  simpa [s'] using this

theorem isTwG_carFun : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O)
    (w0 : O), CMOrd O bar → ∀ (ψ : InvFun O), IsTwG w0 ψ → IsTwG w0 (carFun bar ψ) := by
  intro O _ _ _ _ bar w0 hb ψ htw σ hσ n B
  have hc : ∀ a, σ (bar a) = bar (σ a) := hb.comm σ
  have hev : Tw.TwEval σ ψ := twEval_of_isTwG htw hσ
  let τ : (Fin n → O) ≃+ (Fin n → O) := AddEquiv.piCongrRight fun _ => σ.toAddEquiv
  have hτ : ∀ (a : O) (y : Fin n → O), τ (a • y) = σ a • τ y := fun a y => by ext i; simp [τ]
  have hτs := Tw.symm_smul hτ
  have hcs := Tw.symm_comm hc
  show (carFun bar ψ).toFun n (fun a b => B (τ a) (τ b)) = (carFun bar ψ).toFun n B
  dsimp only [carFun]
  by_cases h : ∃ β : LinearMap.BilinForm ℤ (Fin n → O), β ∈ balForms bar (Fin n → O) ∧ (∀ y, 0 ≤ β y y) ∧
      ∀ a b, B a b = β a b
  · have h' : ∃ β : LinearMap.BilinForm ℤ (Fin n → O), β ∈ balForms bar (Fin n → O) ∧ (∀ y, 0 ≤ β y y) ∧
        ∀ a b, B (τ a) (τ b) = β a b :=
      ⟨Tw.pullA τ h.choose, Tw.pullA_mem hc hτ h.choose_spec.1, fun y => h.choose_spec.2.1 _,
        fun a b => h.choose_spec.2.2 _ _⟩
    rw [dite_eq_left h, dite_eq_left h']
    have e : h'.choose = Tw.pullA τ h.choose := LinearMap.ext₂ fun a b => by
      have h1 := h'.choose_spec.2.2 a b
      have h2 := h.choose_spec.2.2 (τ a) (τ b)
      rw [Tw.pullA_apply]
      exact_mod_cast h1.symm.trans h2
    rw [e]
    unfold cdimQ
    congr 2
    refine (Set.Subset.antisymm ?_ (Tw.cdimSet_subset hc hev hτ _))
    have := Tw.cdimSet_subset (bar := bar) (ψ := ψ) hcs hev.symm hτs (Tw.pullA τ h.choose)
    rwa [Tw.pullA_symm_pullA] at this
  · have h' : ¬ ∃ β : LinearMap.BilinForm ℤ (Fin n → O), β ∈ balForms bar (Fin n → O) ∧ (∀ y, 0 ≤ β y y) ∧
        ∀ a b, B (τ a) (τ b) = β a b := by
      rintro ⟨β, h1, h2, h3⟩
      refine h ⟨Tw.pullA τ.symm β, Tw.pullA_mem hcs hτs h1, fun y => h2 _, fun a b => ?_⟩
      rw [Tw.pullA_apply, ← h3, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
    rw [dite_eq_right h, dite_eq_right h']

end GlobalTheory.CompanionTheory.Ar.Fan.TwistedCarrierFunction
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.CarrierFunctionTwistedGaloisStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.CarDim GlobalTheory.CompanionTheory.Ar.Fan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.carrier_function_twisted_galois : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ (ψ : InvFun O), IsTwG w0 ψ → IsTwG w0 (carFun bar ψ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.TwistedCarrierFunction.isTwG_carFun | exact GlobalTheory.CompanionTheory.Ar.Fan.TwistedCarrierFunction.isTwG_carFun | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.TwistedCarrierFunction.isTwG_carFun <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsCarrierDimensionLabel
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.CarDim GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.CarrierDimension

theorem exists_cell {O : Type} [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] {bar : O → O}
    {ψ : InvFun O} {X : Type}
    [AddCommGroup X] [Module O X] [Module.Finite O X] (hfan : IsPolyFanOn bar ψ X)
    {β : LinearMap.BilinForm ℤ X} (hβ : β ∈ balForms bar X) (hp : ∀ y, 0 ≤ β y y) :
    ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ ∧ InRCone γ β := by
  have hmem : toReal β ∈ psdCone (bar := bar) (X := X) := by
    have := ConeSub.sum_smul_toReal_mem_psdCone O bar X 1 ![β] ![1] (fun i => by fin_cases i; exact hβ)
      (fun i y => by fin_cases i; exact hp y) (fun i => by fin_cases i; norm_num)
    simpa using this
  obtain ⟨S, -, hS⟩ := hfan.finite
  obtain ⟨e, m, γ, c, hγ, -, hc, he⟩ := hS _ hmem
  refine ⟨m, fun i => pull e.symm.toLinearMap (γ i), isCell_pull_equiv hγ e.symm, c, hc, LinearMap.ext₂ fun a b => ?_⟩
  have := LinearMap.congr_fun₂ he (e.symm a) (e.symm b)
  simpa [LinearMap.sum_apply] using this

theorem exists_isCarrierDim : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ (q : ℕ) (ψ : InvFun O), (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], GlobalTheory.PolFan.Dominates bar X) → IsPolyFan bar q ψ → IsTwG w0 ψ → ∃ lab : InvFun O, IsTwG w0 lab ∧ IsCarrierDim bar q ψ lab := by
  intro O _ _ _ _ bar w0 hb q ψ hD hψ htw
  refine ⟨carFun bar ψ, GlobalTheory.T.carrier_function_twisted_galois O bar w0 hb ψ htw, ?_⟩
  intro X _ _ _ _ hX β hβ hp
  have hfan := hψ X hX
  have hface := GlobalTheory.T.cell_face_of_face_cut O bar hb ψ X hfan (hD X)
  rw [evalZ_carFun hβ hp]
  congr 1
  obtain ⟨m₀, γ₀, hγ₀, hin₀⟩ := exists_cell hfan hβ hp
  have hne : {k : ℕ | ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ ∧ InRCone γ β ∧
      genRank γ = k}.Nonempty := ⟨_, m₀, γ₀, hγ₀, hin₀, rfl⟩
  apply le_antisymm
  · obtain ⟨m, γ, h1, h2, h3⟩ := Nat.sInf_mem hne
    obtain ⟨m', δ, k1, k2, k3⟩ := GlobalTheory.T.cell_of_quotient_radical_cone O bar hb ψ X hface β hβ hp m γ h1 h2
    exact (Nat.sInf_le (show genRank δ ∈ cdimSet bar ψ X (orad β) β from ⟨m', δ, k1, k2, rfl⟩)).trans (k3.trans h3.le)
  · have hne' : (cdimSet bar ψ X (orad β) β).Nonempty := by
      obtain ⟨m', δ, k1, k2, -⟩ := GlobalTheory.T.cell_of_quotient_radical_cone O bar hb ψ X hface β hβ hp m₀ γ₀ hγ₀ hin₀
      exact ⟨_, m', δ, k1, k2, rfl⟩
    obtain ⟨m', δ, h1, h2, h3⟩ := Nat.sInf_mem hne'
    obtain ⟨m, γ, k1, k2, k3⟩ := GlobalTheory.T.cell_of_quotient_cell O bar hb ψ X hfan hface β hβ hp m' δ h1 h2
    unfold cdimQ
    rw [← h3]
    exact (Nat.sInf_le (show genRank γ ∈ {k : ℕ | ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ ∧
      InRCone γ β ∧ genRank γ = k} from ⟨m, γ, k1, k2, rfl⟩)).trans k3

end GlobalTheory.CompanionTheory.Ar.Fan.CarrierDimension
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsCarrierDimensionLabelStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan
theorem _root_.GlobalTheory.T.exists_carrier_dimension_label : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ (q : ℕ) (ψ : InvFun O), (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], GlobalTheory.PolFan.Dominates bar X) → IsPolyFan bar q ψ → IsTwG w0 ψ → ∃ lab : InvFun O, IsTwG w0 lab ∧ IsCarrierDim bar q ψ lab := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.CarrierDimension.exists_isCarrierDim | exact GlobalTheory.CompanionTheory.Ar.Fan.CarrierDimension.exists_isCarrierDim | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.CarrierDimension.exists_isCarrierDim <;> assumption)
end
