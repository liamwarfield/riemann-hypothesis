module

public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.HodgeTateNormComparison
public import Development.WeilBound.CoreStatements.HodgeTatePoints.HcptgenChart

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.FlagbLoc
section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.FlagbAlg
noncomputable section

namespace PositivityTheory.HtPt.Flagb

open GlobalTheory.CompanionTheory.Ar

section Glue

variable {A Ω W : Type} [CommRing A] [Field Ω] [Algebra A Ω] [AddCommGroup W] [Module Ω W] [Module A W]
  [IsScalarTower A Ω W]

theorem one_mem_of_max (I : Ideal A) (h : ∀ m : Ideal A, m.IsMaximal → ∃ s ∈ I, s ∉ m) : (1 : A) ∈ I := by
  by_contra h1
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal I ((Ideal.ne_top_iff_one I).2 h1)
  obtain ⟨s, hs, hs'⟩ := h m hm
  exact hs' (hle hs)

theorem map_smul_alg (φ : W →ₗ[Ω] Ω) (a : A) (w : W) : φ (a • w) = algebraMap A Ω a * φ w := by
  rw [← algebraMap_smul Ω a w, map_smul, smul_eq_mul]

theorem exists_basis (hinj : Function.Injective (algebraMap A Ω)) (N : Submodule A W) {r : ℕ}
    (φ : Fin r → W →ₗ[Ω] Ω) (t : Fin r → Ω) (ht : ∀ i, t i ≠ 0)
    (hφ : ∀ w ∈ N, (∀ j, φ j w = 0) → w = 0)
    (ha : ∀ m : Ideal A, m.IsMaximal → ∀ i, ∃ s ∉ m, ∃ n ∈ N, (∀ j < i, φ j n = 0) ∧ φ i n = algebraMap A Ω s * t i)
    (hb : ∀ m : Ideal A, m.IsMaximal → ∀ i, ∀ n ∈ N, (∀ j < i, φ j n = 0) →
      ∃ s ∉ m, ∃ a : A, algebraMap A Ω s * φ i n = algebraMap A Ω a * t i) :
    ∃ b : Module.Basis (Fin r) A N, ∀ i, (∀ j < i, φ j (b i) = 0) ∧ φ i (b i) = t i := by
  have h1 : ∀ i, ∃ n ∈ N, (∀ j < i, φ j n = 0) ∧ φ i n = t i := by
    intro i
    let I : Ideal A :=
      { carrier := {s | ∃ n ∈ N, (∀ j < i, φ j n = 0) ∧ φ i n = algebraMap A Ω s * t i}
        add_mem' := by
          rintro a b ⟨n, hn, h0, h⟩ ⟨n', hn', h0', h'⟩
          refine ⟨n + n', N.add_mem hn hn', fun j hj => by rw [map_add (f := _), h0 j hj, h0' j hj, add_zero], ?_⟩
          rw [map_add (f := _), map_add (f := _), h, h', add_mul]
        zero_mem' := ⟨0, N.zero_mem, fun j _ => map_zero _, by simp⟩
        smul_mem' := by
          rintro c a ⟨n, hn, h0, h⟩
          refine ⟨c • n, N.smul_mem c hn, fun j hj => by rw [map_smul_alg, h0 j hj, mul_zero], ?_⟩
          rw [map_smul_alg, h, smul_eq_mul, map_mul, mul_assoc] }
    have := one_mem_of_max I fun m hm => by
      obtain ⟨s, hs, h⟩ := ha m hm i
      exact ⟨s, h, hs⟩
    obtain ⟨n, hn, h0, h⟩ := this
    exact ⟨n, hn, h0, by simpa using h⟩
  have h2 : ∀ i, ∀ n ∈ N, (∀ j < i, φ j n = 0) → ∃ a : A, φ i n = algebraMap A Ω a * t i := by
    intro i n hn h0
    let I : Ideal A :=
      { carrier := {s | ∃ a : A, algebraMap A Ω s * φ i n = algebraMap A Ω a * t i}
        add_mem' := by
          rintro a b ⟨x, h⟩ ⟨y, h'⟩
          exact ⟨x + y, by rw [map_add (f := _), map_add (f := _), add_mul, add_mul, h, h']⟩
        zero_mem' := ⟨0, by simp⟩
        smul_mem' := by
          rintro c a ⟨x, h⟩
          exact ⟨c * x, by rw [smul_eq_mul, map_mul, map_mul, mul_assoc, h, mul_assoc]⟩ }
    have := one_mem_of_max I fun m hm => by
      obtain ⟨s, hs, h⟩ := hb m hm i n hn h0
      exact ⟨s, h, hs⟩
    obtain ⟨a, h⟩ := this
    exact ⟨a, by simpa using h⟩
  choose n hn hn0 hnt using h1
  let n' : Fin r → N := fun i => ⟨n i, hn i⟩
  have hli : LinearIndependent A n' := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have hg' : ∑ j, g j • n j = 0 := by simpa [n'] using congrArg Subtype.val hg
    induction i using WellFoundedLT.induction with
    | _ i ih =>
      have := congrArg (φ i) hg'
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_zero, Finset.sum_eq_single i] at this
      · rw [map_smul_alg, hnt] at this
        exact hinj (by rw [map_zero]; exact (mul_eq_zero.1 this).resolve_right (ht i))
      · intro j _ hj
        rcases lt_or_gt_of_ne hj with h | h
        · rw [ih j h, zero_smul, map_zero]
        · rw [map_smul_alg, hn0 j i h, mul_zero]
      · simp
  have hsp : ∀ k : ℕ, ∀ x : N, (∀ j : Fin r, (j : ℕ) + k < r → φ j x = 0) → x ∈ Submodule.span A (Set.range n') := by
    intro k
    induction k with
    | zero =>
      intro x hx
      have : x = 0 := Subtype.ext (hφ x x.2 fun j => hx j (by simp))
      rw [this]; exact Submodule.zero_mem _
    | succ k ih =>
      intro x hx
      by_cases hk : k < r
      · let i : Fin r := ⟨r - k - 1, by omega⟩
        have hi : (i : ℕ) = r - k - 1 := rfl
        have h0 : ∀ j < i, φ j x = 0 := fun j hj => hx j (by have : (j : ℕ) < i := hj; omega)
        obtain ⟨a, ha⟩ := h2 i x x.2 h0
        have := ih (x - a • n' i) fun j hj => by
          have hji : j ≤ i := by show (j : ℕ) ≤ i; omega
          show φ j ((x : W) - a • n i) = 0
          rw [map_sub, map_smul_alg]
          rcases hji.lt_or_eq with h | h
          · rw [h0 j h, hn0 i j h, mul_zero, sub_zero]
          · rw [h, ha, hnt, sub_self]
        have h3 := Submodule.add_mem _ this (Submodule.smul_mem _ a (Submodule.subset_span ⟨i, rfl⟩ :
          n' i ∈ Submodule.span A (Set.range n')))
        rwa [sub_add_cancel] at h3
      · exact ih x fun j hj => by omega
  refine ⟨Module.Basis.mk hli fun x _ => hsp r x fun j hj => by omega, fun i => ?_⟩
  rw [Module.Basis.mk_apply]
  exact ⟨hn0 i, hnt i⟩

theorem exists_smul_mem (m : Ideal A) [hm : m.IsPrime] (R : Subring Ω)
    (hR : ∀ x ∈ R, ∃ s ∉ m, ∃ a : A, algebraMap A Ω s * x = algebraMap A Ω a) (N : Submodule A W) (w : W)
    (hw : w ∈ Submodule.span R (N : Set W)) : ∃ s ∉ m, s • w ∈ N := by
  have h1 : (1 : A) ∉ m := (Ideal.ne_top_iff_one m).1 hm.ne_top
  induction hw using Submodule.span_induction with
  | mem x hx => exact ⟨1, h1, by rwa [one_smul]⟩
  | zero => exact ⟨1, h1, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, hs, hx⟩ := hx
    obtain ⟨u, hu, hy⟩ := hy
    refine ⟨s * u, fun h => (hm.mem_or_mem h).elim hs hu, ?_⟩
    rw [smul_add]
    refine N.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact N.smul_mem _ hx
    · rw [mul_smul]; exact N.smul_mem _ hy
  | smul c x _ hx =>
    obtain ⟨s, hs, hx⟩ := hx
    obtain ⟨u, hu, a, ha⟩ := hR c c.2
    refine ⟨u * s, fun h => (hm.mem_or_mem h).elim hu hs, ?_⟩
    have : (u * s) • c • x = a • s • x := by
      show (u * s) • (c : Ω) • x = _
      rw [← algebraMap_smul Ω (u * s), ← algebraMap_smul Ω a, ← algebraMap_smul Ω s, smul_smul, smul_smul, ← ha,
        map_mul]
      congr 1; ring
    rw [this]; exact N.smul_mem _ hx

end Glue

section Frames

variable {o Ω L : Type} [CommRing o] [Field Ω] [Algebra o Ω] {A : Subalgebra o Ω} [AddCommGroup L] [Module Ω L]

theorem vanish_step {r : ℕ} (b : Fin r → L) (i : ℕ) (w : Module.Dual Ω L) :
    (∀ e ∈ flagStep Ω b i, w e = 0) ↔ ∀ j : Fin r, (j : ℕ) < i → w (b j) = 0 := by
  refine ⟨fun h j hj => h _ (Submodule.subset_span ⟨j, hj, rfl⟩), fun h e he => ?_⟩
  have : flagStep Ω b i ≤ LinearMap.ker w := Submodule.span_le.2 (by rintro _ ⟨j, hj, rfl⟩; exact h j hj)
  exact this he

theorem flagStep_top {r : ℕ} (b : Fin r → L) : flagStep Ω b r = Submodule.span Ω (Set.range b) := by
  unfold flagStep
  congr 1
  ext x
  simp

def LocFrame (m : Ideal A) (P : L →ₗ[Ω] L) {r : ℕ} (b₀ : Fin r → L) (N : Submodule A (Module.Dual Ω L)) (d : Ω)
    (g : Fin r → Ω) : Prop :=
  ∃ R : Subring Ω, (∀ x ∈ R, ∃ s ∉ m, ∃ a : A, algebraMap A Ω s * x = algebraMap A Ω a) ∧
    ∃ b : Fin r → L, LinearIndependent Ω b ∧ (∀ i, flagStep Ω b i = flagStep Ω b₀ i) ∧
      (∀ i : Fin r, ∃ τ : Ω, b i - τ • b₀ i ∈ flagStep Ω b₀ i ∧ τ / g i ∈ R ∧ g i / τ ∈ R ∧ τ ≠ 0) ∧
      (∀ w ∈ N, ∀ i, d * w (b i) ∈ R) ∧
      ∀ w : Module.Dual Ω L, w ∘ₗ P = w → (∀ i, d * w (b i) ∈ R) → ∃ s ∉ m, s • w ∈ N

theorem exists_basis_frames (P : L →ₗ[Ω] L) {r : ℕ} (b₀ : Fin r → L)
    (hP : ∀ e, P e ∈ Submodule.span Ω (Set.range b₀)) (hP' : ∀ e ∈ Submodule.span Ω (Set.range b₀), P e = e)
    (N : Submodule A (Module.Dual Ω L)) (hN : ∀ w ∈ N, w ∘ₗ P = w) (d : Ω) (hd : d ≠ 0) (g : Fin r → Ω)
    (hg : ∀ i, g i ≠ 0) (h : ∀ m : Ideal A, m.IsMaximal → LocFrame m P b₀ N d g) :
    ∃ n : Module.Basis (Fin r) A N, ∀ i, (∀ j < i, (n i).1 (b₀ j) = 0) ∧ (n i).1 (b₀ i) = (d * g i)⁻¹ := by
  refine exists_basis (Ω := Ω) Subtype.val_injective N (fun j => Module.Dual.eval Ω L (b₀ j)) (fun i => (d * g i)⁻¹)
    (fun i => inv_ne_zero (mul_ne_zero hd (hg i))) ?_ ?_ ?_
  · intro w hw h0
    rw [← hN w hw]
    ext e
    have := (vanish_step b₀ r w).2 (fun j _ => h0 j) (P e) (by rw [flagStep_top]; exact hP e)
    simpa using this
  · intro m hm i
    obtain ⟨R, hR, b, hb, hF, hτ, -, h2⟩ := h m hm
    obtain ⟨τ, hτ, h3, -, hτ0⟩ := hτ i
    obtain ⟨φ, h1, h0⟩ := FlagGrGen.exists_coord hb i
    have hbP : ∀ j, P (b j) = b j := fun j => hP' _ (by
      rw [← flagStep_top, ← hF, flagStep_top]; exact Submodule.subset_span ⟨j, rfl⟩)
    have hPP : P ∘ₗ P = P := LinearMap.ext fun e => hP' _ (hP e)
    let w : Module.Dual Ω L := (d⁻¹ * (τ / g i)) • (φ ∘ₗ P)
    have hw : ∀ j, w (b j) = d⁻¹ * (τ / g i) * φ (b j) := fun j => by simp [w, hbP]
    obtain ⟨s, hs, hsw⟩ := h2 w (by rw [LinearMap.smul_comp, LinearMap.comp_assoc, hPP]) fun j => by
      rw [hw]
      by_cases hj : j = i
      · rw [hj, h1, mul_one, mul_inv_cancel_left₀ hd]; exact h3
      · rw [h0 j hj, mul_zero, mul_zero]; exact R.zero_mem
    have hv : ∀ e ∈ flagStep Ω b₀ i, w e = 0 := by
      rw [← hF, vanish_step]
      intro j hj
      rw [hw, h0 j (fun e => by simp [e] at hj), mul_zero]
    refine ⟨s, hs, s • w, hsw, fun j hj => ?_, ?_⟩
    · refine (map_smul_alg _ s w).trans ?_
      rw [Module.Dual.eval_apply, (vanish_step b₀ i w).1 hv j hj, mul_zero]
    · refine (map_smul_alg _ s w).trans ?_
      rw [Module.Dual.eval_apply]
      congr 1
      have := hv _ hτ
      rw [map_sub, map_smul, hw, h1, smul_eq_mul, sub_eq_zero] at this
      have hg' := hg i
      apply mul_left_cancel₀ hτ0
      rw [← this]; field_simp
  · intro m hm i n hn h0
    obtain ⟨R, hR, b, hb, hF, hτ, h1, -⟩ := h m hm
    obtain ⟨τ, hτ, -, h3, hτ0⟩ := hτ i
    have hv := (vanish_step b₀ i n).2 (fun j hj => h0 j hj) _ hτ
    rw [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at hv
    obtain ⟨s, hs, a, ha⟩ := hR _ (R.mul_mem (h1 n hn i) h3)
    refine ⟨s, hs, a, ?_⟩
    have hg' := hg i
    rw [← ha, hv, Module.Dual.eval_apply]
    field_simp

theorem shape_M (P : L →ₗ[Ω] L) {r : ℕ} (b₀ : Fin r → L) (hb₀ : LinearIndependent Ω b₀)
    (hP : ∀ e, P e ∈ Submodule.span Ω (Set.range b₀))
    (e : Fin r → Ω) (he : ∀ a, e a ≠ 0) :
    ∃ wM : Fin r → Module.Dual Ω L, ∀ (A : Subalgebra o Ω) (N : Submodule A (Module.Dual Ω L)), (∀ w ∈ N, w ∘ₗ P = w) →
      ∀ (c : Fin r → Ω) (n : Module.Basis (Fin r) A N),
        (∀ i, (∀ j < i, (n i).1 (b₀ j) = 0) ∧ (n i).1 (b₀ i) = c i.rev * e i.rev) →
        ∃ bM : Module.Basis (Fin r) A N, ∀ a, ∃ cf : Fin r → Ω, (∀ a', a < a' → cf a' = 0) ∧ cf a = c a ∧
          (bM a).1 = ∑ a', cf a' • wM a' := by
  choose φ h1 h0 using fun i => FlagGrGen.exists_coord hb₀ i
  refine ⟨fun a => e a • (φ a.rev ∘ₗ P), fun A N hN c n hn => ⟨n.reindex Fin.revPerm, fun a => ?_⟩⟩
  refine ⟨fun a' => (n a.rev).1 (b₀ a'.rev) / e a', fun a' h => ?_, ?_, ?_⟩
  · show _ / _ = _
    rw [(hn a.rev).1 _ (Fin.rev_lt_rev.2 h), zero_div]
  · show _ / _ = _
    rw [(hn a.rev).2, Fin.rev_rev, mul_div_cancel_right₀ _ (he a)]
  · rw [Module.Basis.reindex_apply]
    show (n a.rev).1 = _
    set w := (n a.rev).1
    have hw : w ∘ₗ P = w := hN w (n a.rev).2
    have key : ∀ x ∈ Submodule.span Ω (Set.range b₀), w x = ∑ a' : Fin r, w (b₀ a'.rev) * φ a'.rev x := by
      intro x hx
      have : Submodule.span Ω (Set.range b₀) ≤ LinearMap.ker (w - ∑ a' : Fin r, w (b₀ a'.rev) • φ a'.rev) := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨j, rfl⟩
        show (w - ∑ a' : Fin r, w (b₀ a'.rev) • φ a'.rev) (b₀ j) = 0
        rw [LinearMap.sub_apply, LinearMap.sum_apply, Finset.sum_eq_single j.rev]
        · simp [h1]
        · intro k _ hk
          rw [LinearMap.smul_apply, h0 k.rev j (by rintro rfl; simp at hk), smul_zero]
        · simp
      have h := this hx
      simpa [sub_eq_zero] using h
    ext x
    rw [← hw, LinearMap.comp_apply, hw, key _ (hP x), LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun a' _ => ?_
    have := he a'
    simp only [LinearMap.smul_apply, smul_eq_mul, LinearMap.comp_apply]
    field_simp

theorem shape_alt {r : ℕ} (b₀ : Fin r → L) (e : Fin r → Ω) (he : ∀ a, e a ≠ 0)
    (N : Submodule A (Module.Dual Ω L)) (c : Fin r → Ω) (hc : ∀ a, c a ≠ 0) (n : Module.Basis (Fin r) A N)
    (hn : ∀ i, (∀ j < i, (n i).1 (b₀ j) = 0) ∧ (n i).1 (b₀ i) = (c i * e i)⁻¹) :
    ∃ bW : Module.Basis (Fin r) A (Module.Dual A N), ∀ a, ∃ cf : Fin r → Ω, (∀ a', a < a' → cf a' = 0) ∧
      cf a = c a ∧ ∀ z : N, algebraMap A Ω (bW a z) = ∑ a', cf a' * Module.Dual.eval Ω L (e a' • b₀ a') z.1 := by
  classical
  let U : Matrix (Fin r) (Fin r) Ω := fun i j => (n i).1 (b₀ j)
  have hU : U.BlockTriangular id := fun i j h => (hn i).1 j h
  have hdet : U.det ≠ 0 := by
    rw [Matrix.det_of_isUpperTriangular hU]
    exact Finset.prod_ne_zero_iff.2 fun i _ => by
      show (n i).1 (b₀ i) ≠ 0
      rw [(hn i).2]; exact inv_ne_zero (mul_ne_zero (hc i) (he i))
  letI := U.invertibleOfIsUnitDet (IsUnit.mk0 _ hdet)
  have hU' : U⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hU
  have hmul : U * U⁻¹ = 1 := Matrix.mul_nonsing_inv U (IsUnit.mk0 _ hdet)
  refine ⟨n.dualBasis, fun a => ⟨fun a' => U⁻¹ a' a / e a', fun a' h => ?_, ?_, fun z => ?_⟩⟩
  · show _ / _ = _
    rw [hU' (show id a < id a' from h), zero_div]
  · have := congrFun (congrFun hmul a) a
    rw [Matrix.mul_apply, Finset.sum_eq_single a, Matrix.one_apply_eq] at this
    · have h2 : U a a = (c a * e a)⁻¹ := (hn a).2
      rw [h2] at this
      have h3 := hc a
      have h4 := he a
      show _ / _ = _
      field_simp at this ⊢
      linear_combination this
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with h | h
      · rw [hU (show id k < id a from h), zero_mul]
      · rw [hU' (show id a < id k from h), mul_zero]
    · simp
  · have hz : (z : Module.Dual Ω L) = ∑ i, n.repr z i • (n i).1 := by
      have := congrArg N.subtype (n.sum_repr z)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum] at this
      exact this.symm
    rw [Module.Basis.dualBasis_apply, hz]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, Finset.mul_sum]
    simp only [fun a' i => map_smul_alg (Module.Dual.eval Ω L (e a' • b₀ a')) (n.repr z i) (n i).1]
    rw [Finset.sum_comm]
    have : ∀ i, ∑ a', U⁻¹ a' a / e a' * (algebraMap A Ω (n.repr z i) * Module.Dual.eval Ω L (e a' • b₀ a') (n i).1) =
        algebraMap A Ω (n.repr z i) * (U * U⁻¹) i a := by
      intro i
      rw [Matrix.mul_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a' _ => ?_
      have := he a'
      rw [Module.Dual.eval_apply, map_smul, smul_eq_mul]
      change _ = _ * ((n i).1 (b₀ a') * _)
      field_simp
    rw [Finset.sum_congr rfl fun i _ => this i, hmul]
    simp [Matrix.one_apply]

end Frames

end PositivityTheory.HtPt.Flagb
end
end

noncomputable section

namespace PositivityTheory.HtPt.Flagb

open AlgebraicGeometry CategoryTheory NumberField GlobalTheory.CompanionTheory.Ar

variable {Ω L : Type} [Field Ω] [AddCommGroup L] [Module Ω L]

theorem exists_lead {r : ℕ} (b₀ b : Fin r → L) (hF : ∀ i, flagStep Ω b i = flagStep Ω b₀ i) (i : Fin r) :
    ∃ τ : Ω, b i - τ • b₀ i ∈ flagStep Ω b₀ i := by
  have h1 : b i ∈ flagStep Ω b₀ (i + 1) := by
    rw [← hF]; exact Submodule.subset_span ⟨i, by simp, rfl⟩
  have h2 : b₀ '' {k | (k : ℕ) < i + 1} = insert (b₀ i) (b₀ '' {k | (k : ℕ) < i}) := by
    rw [← Set.image_insert_eq]
    congr 1
    ext k
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Fin.ext_iff]
    omega
  unfold flagStep at h1
  rw [h2, Submodule.mem_span_insert] at h1
  obtain ⟨a, z, hz, h⟩ := h1
  exact ⟨a, by rw [h, add_sub_cancel_left]; exact hz⟩

theorem div_mem_of_span (R : Subring Ω) {a c : Ω} (h : a ∈ Submodule.span R {c}) : a / c ∈ R := by
  obtain ⟨u, rfl⟩ := Submodule.mem_span_singleton.1 h
  by_cases hc : c = 0
  · simp [hc]
  · show (u : Ω) * c / c ∈ R
    rw [mul_div_cancel_right₀ _ hc]; exact u.2

theorem tens_gen {X : Scheme.{0}} {ξ : Spec (CommRingCat.of Ω) ⟶ X} (Λ : Lat ξ Ω) (q : Cpt ξ) (ε : ℤ)
    (hε : ε = 1 ∨ ε = -1) (τ c : Ω) (h : Λ.IsGenAt q τ)
    (hc : Lat.tens (fun _ : Unit => Λ) (fun _ => ε) q = Submodule.span (regAt ξ q) {c}) :
    τ ^ ε / c ∈ regAt ξ q ∧ c / τ ^ ε ∈ regAt ξ q := by
  constructor
  · refine div_mem_of_span _ ?_
    rw [← hc]
    exact Submodule.subset_span ⟨fun _ => τ, fun _ => h, by simp⟩
  · refine div_mem_of_span _ ?_
    have : Lat.tens (fun _ : Unit => Λ) (fun _ => ε) q ≤ Submodule.span (regAt ξ q) {τ ^ ε} := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨s, hs, rfl⟩
      replace hs : ∀ i, Λ.IsGenAt q (s i) := hs
      have h1 : s () / τ ∈ regAt ξ q := div_mem_of_span _ (by
        rw [← h.2, (hs ()).2]; exact Submodule.mem_span_singleton_self _)
      have h2 : τ / s () ∈ regAt ξ q := div_mem_of_span _ (by
        rw [← (hs ()).2, h.2]; exact Submodule.mem_span_singleton_self _)
      have h3 := h.1
      have h4 := (hs ()).1
      rcases hε with rfl | rfl
      · refine Submodule.mem_span_singleton.2 ⟨⟨_, h1⟩, ?_⟩
        show s () / τ * τ ^ (1 : ℤ) = _
        simp [h3]
      · refine Submodule.mem_span_singleton.2 ⟨⟨_, h2⟩, ?_⟩
        show τ / s () * τ ^ (-1 : ℤ) = _
        simp
        field_simp
    exact this (hc ▸ Submodule.mem_span_singleton_self _)

theorem mem_span_of_dual {V : Type} [AddCommGroup V] [Module Ω V] [FiniteDimensional Ω V] (R : Subring Ω) {r : ℕ}
    (f : Fin r → Module.Dual Ω V) (hf : LinearIndependent Ω f) (hs : Submodule.span Ω (Set.range f) = ⊤)
    (u : Module.Dual Ω V) (hu : ∀ e : V, (∀ j, f j e ∈ R) → u e ∈ R) : u ∈ Submodule.span R (Set.range f) := by
  classical
  let B : Module.Basis (Fin r) Ω (Module.Dual Ω V) := Module.Basis.mk hf hs.ge
  have hB : ∀ j, B j = f j := fun j => Module.Basis.mk_apply _ _ j
  have h1 : ∀ j, B.repr u j ∈ R := by
    intro j
    have h2 : ∀ w : Module.Dual Ω V, w ((Module.evalEquiv Ω V).symm (B.coord j)) = B.repr w j := fun w => by
      rw [Module.apply_evalEquiv_symm_apply]; rfl
    rw [← h2]
    refine hu _ fun i => ?_
    rw [h2, ← hB, B.repr_self, Finsupp.single_apply]
    split_ifs
    · exact R.one_mem
    · exact R.zero_mem
  rw [← B.sum_repr u]
  refine Submodule.sum_mem _ fun j _ => ?_
  exact Submodule.smul_mem (Submodule.span R (Set.range f)) (⟨_, h1 j⟩ : R) (Submodule.subset_span ⟨j, (hB j).symm⟩)

theorem apply_mem_of_span (R : Subring Ω) (w : Module.Dual Ω L) (s : Set L) (h : ∀ x ∈ s, w x ∈ R) (e : L)
    (he : e ∈ Submodule.span R s) : w e ∈ R := by
  induction he using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => rw [map_zero]; exact R.zero_mem
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx =>
    have : w (c • x) = (c : Ω) * w x := map_smul w (c : Ω) x
    rw [this]; exact mul_mem c.2 hx

theorem exists_nat_diff {E : Type} [Field E] [NumberField E] (x : E) :
    ∃ n : ℕ, n ≠ 0 ∧ ∃ δ ∈ differentIdeal ℤ (𝓞 E), (δ : E) = n * x := by
  obtain ⟨y, hy, hi⟩ := (show IsAlgebraic ℤ x from
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic x)).exists_integral_multiple
  obtain ⟨z, hz⟩ : ∃ z : 𝓞 E, algebraMap (𝓞 E) E z = y * x := ⟨⟨y • x, hi⟩, by rw [← zsmul_eq_mul]; rfl⟩
  have hN := Ideal.absNorm_mem (differentIdeal ℤ (𝓞 E))
  have hN0 : Ideal.absNorm (differentIdeal ℤ (𝓞 E)) ≠ 0 := fun h =>
    differentIdeal_ne_bot (A := ℤ) (B := 𝓞 E) (Ideal.absNorm_eq_zero_iff.1 h)
  refine ⟨Ideal.absNorm (differentIdeal ℤ (𝓞 E)) * y.natAbs ^ 2, mul_ne_zero hN0 (pow_ne_zero _ (by simpa using hy)),
    _, Ideal.mul_mem_right ((y : 𝓞 E) * z) _ hN, ?_⟩
  have : ((y.natAbs ^ 2 : ℕ) : E) = (y : E) * y := by
    rw [← Int.cast_natCast, Nat.cast_pow, Int.natAbs_sq, Int.cast_pow, sq]
  rw [Nat.cast_mul, this]
  simp only [map_mul, map_natCast, map_intCast]
  rw [hz]; ring

end PositivityTheory.HtPt.Flagb
end
end

noncomputable section

namespace PositivityTheory.HtPt.Flagb

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

section Label

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S y)

def prj (σ' : E →+* Ω) : 𝔐.Li →ₗ[Ω] 𝔐.Li := eigProj (𝔐.ρ.comp (H.bar : 𝓞 E →+* 𝓞 E)) σ'

variable {𝔐}

theorem mem_Vgen {s : CMType H ⊕ CMType H} {σ' : E →+* Ω} (hσ : ∀ a : 𝓞 E, σ' a = 𝔐.emb s (H.bar a)) (x : 𝔐.Li) :
    x ∈ HT.eigSp (𝔐.ρ.comp (H.bar : 𝓞 E →+* 𝓞 E)) σ' ↔ x ∈ 𝔐.Vgen s := by
  rw [LatBasic.mem_eigSp]
  simp only [HodgeCpt.Vgen, GlobalTheory.CompanionTheory.Ar.eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero, hσ]
  refine ⟨fun h a => ?_, fun h a => h _⟩
  obtain ⟨a, rfl⟩ := H.bar.surjective a
  exact h a

theorem prj_mem {s : CMType H ⊕ CMType H} {σ' : E →+* Ω} (hσ : ∀ a : 𝓞 E, σ' a = 𝔐.emb s (H.bar a)) (x : 𝔐.Li) :
    prj 𝔐 σ' x ∈ 𝔐.Vgen s := (mem_Vgen hσ _).1 (LatBasic.eigProj_mem _ _ x)

theorem prj_of_mem {s : CMType H ⊕ CMType H} {σ' : E →+* Ω} (hσ : ∀ a : 𝓞 E, σ' a = 𝔐.emb s (H.bar a))
    {x : 𝔐.Li} (hx : x ∈ 𝔐.Vgen s) : prj 𝔐 σ' x = x := LatBasic.eigProj_of_mem ((mem_Vgen hσ _).2 hx)

theorem eigProj_eq_comp (ρΩ : 𝓞 E →+* Module.End Ω (Module.Dual Ω 𝔐.Li))
    (h : ∀ (a : 𝓞 E) (w : Module.Dual Ω 𝔐.Li), ρΩ a w = w ∘ₗ 𝔐.ρ (H.bar a)) (σ' : E →+* Ω)
    (w : Module.Dual Ω 𝔐.Li) : eigProj ρΩ σ' w = w ∘ₗ prj 𝔐 σ' := by
  ext x
  simp [eigProj, prj, h, LinearMap.sum_apply]

theorem span_flag (Fl : 𝔐.Flag) (s : CMType H ⊕ CMType H) :
    Submodule.span Ω (Set.range (Fl.b s)) = 𝔐.Vgen s := by
  let q : Cpt 𝔐.ξ := ⟨genPt 𝔐.ξ, specializes_rfl⟩
  obtain ⟨U, hU, b, hF, hb⟩ := Fl.sub s q trivial
  obtain ⟨U', hU', b', hV, hb'⟩ := 𝔐.vb s q trivial
  have h1 := (hb q trivial hU).2
  have h2 : 𝔐.V s q = _ := (hb' q trivial hU').2
  have h3 := congrArg (fun N : Submodule (regAt 𝔐.ξ q) 𝔐.Li => Submodule.span Ω (N : Set 𝔐.Li)) (h1.symm.trans h2)
  simp only [Submodule.span_span_of_tower] at h3
  rw [← flagStep_top, ← hF, flagStep_top, h3]
  exact hV

theorem li_flag (Fl : 𝔐.Flag) (s : CMType H ⊕ CMType H) : LinearIndependent Ω (Fl.b s) := by
  obtain ⟨_, _, -, -, -, h, -⟩ := Fl.generic
  exact h s

theorem charZero (𝔐 : HodgeCpt Y S y) : CharZero Ω :=
  (RingHom.charZero_iff 𝔐.cst.injective).1 inferInstance

variable {p : ℕ} {o : Type} [CommRing o] [Algebra o Ω]

theorem chart_le (hp : p.Prime)
    (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω))
    {t : ∀ k, J k} {q : Cpt 𝔐.ξ} (hq : InChart 𝔐.ξ (mseg y) t q) (hz : OverZp 𝔐 p q) (a : Ω)
    (ha : a ∈ chartRing o (mseg y) t) : a ∈ regAt 𝔐.ξ q := by
  induction ha using Algebra.adjoin_induction with
  | mem x hx => obtain ⟨j, rfl⟩ := hx; exact hq.2 j
  | algebraMap r =>
    obtain ⟨a, b, hb, h⟩ := (ho _).1 ⟨r, rfl⟩
    have hu := unitAt_nat q b (by rintro rfl; exact hb (dvd_zero _)) fun r hr hd => by
      by_contra hn
      exact hb (hz r hr hn ▸ hd)
    rw [h, div_eq_mul_inv]
    exact mul_mem (intCast_mem _ a) hu.2.2
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy => exact mul_mem hx hy

theorem exists_pt (hp : p.Prime)
    (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω))
    {t : ∀ k, J k} (ht : mseg y t ≠ 0) (m : Ideal (chartRing o (mseg y) t)) [hm : m.IsPrime] :
    ∃ q : Cpt 𝔐.ξ, InChart 𝔐.ξ (mseg y) t q ∧ OverZp 𝔐 p q ∧
      ∀ z ∈ regAt 𝔐.ξ q, ∃ s ∉ m, ∃ a : chartRing o (mseg y) t, (s : Ω) * z = a := by
  haveI := charZero 𝔐
  obtain ⟨q, h1, h2, h3⟩ := exists_point (x := mseg y) 𝔐.tie t ht (chartRing o (mseg y) t)
    (fun j => Algebra.subset_adjoin ⟨j, rfl⟩) m
  refine ⟨q, h1, fun r hr hf => ?_, h2⟩
  by_contra hne
  refine hf (h3 r fun hrm => ?_)
  obtain ⟨u, hu⟩ := (ho ((1 : ℤ) / (r : Ω))).2 ⟨1, r, fun h => hne ((Nat.prime_dvd_prime_iff_eq hp hr).1 h).symm, rfl⟩
  have : algebraMap o (chartRing o (mseg y) t) u * r = 1 := by
    apply Subtype.ext
    have hr0 : (r : Ω) ≠ 0 := Nat.cast_ne_zero.2 hr.ne_zero
    show algebraMap o Ω u * ((r : chartRing o (mseg y) t) : Ω) = 1
    rw [hu]
    simp [hr0]
  exact hm.ne_top ((Ideal.eq_top_iff_one m).2 (this ▸ m.mul_mem_left _ hrm))

theorem locFrame [Fact p.Prime] (hpS : p ∈ S)
    (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω))
    {Dc : ∀ s : {s : ∀ k, J k // mseg y s ≠ 0},
      HTChart (chartRing o (mseg y) s.1) Ω (cmConj E) p (𝔐.R p) (D.p + D.q) (Module.Dual Ω 𝔐.Li)}
    (hD : IsHTFamily 𝔐 p o Dc) (hfree : HTFree 𝔐 p) (Fl : 𝔐.Flag) (t : {s : ∀ k, J k // mseg y s ≠ 0})
    (s : CMType H ⊕ CMType H) (σ' : E →+* Ω) (hσ : ∀ a : 𝓞 E, σ' a = 𝔐.emb s (H.bar a)) (d : Ω) (hd : d ≠ 0)
    (g : Fin (labelRk D s) → Ω)
    (hfib : ∀ q, InChart 𝔐.ξ (mseg y) t.1 q → OverZp 𝔐 p q → ∀ e, e ∈ 𝔐.HT p s q ↔
      d • e ∈ 𝔐.M.htDual 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb s) q)
    (hoff : ∀ q, InChart 𝔐.ξ (mseg y) t.1 q → OverZp 𝔐 p q → ¬ InFibre 𝔐.ξ p q →
      unitAt 𝔐.ξ q d ∧ ∀ x : E, σ' x ∈ regAt 𝔐.ξ q)
    (hg : ∀ q, InChart 𝔐.ξ (mseg y) t.1 q → ∀ i τ, ((𝔐.V s).gr (Fl.b s) i).IsGenAt q τ →
      τ / g i ∈ regAt 𝔐.ξ q ∧ g i / τ ∈ regAt 𝔐.ξ q)
    (m : Ideal (chartRing o (mseg y) t.1)) (hm : m.IsMaximal) :
    LocFrame m (prj 𝔐 σ') (Fl.b s) ((Dc t).omHT σ') d g := by
  have hp : p.Prime := Fact.out
  obtain ⟨q, hq, hz, hR⟩ := exists_pt (𝔐 := 𝔐) hp ho t.2 m
  obtain ⟨U, hU, b, hF, hb⟩ := Fl.sub s q trivial
  have hb := hb q trivial hU
  have hbV : ∀ i, b i ∈ 𝔐.V s q := fun i => by rw [hb.2]; exact Submodule.subset_span ⟨i, rfl⟩
  have hbG : ∀ i, b i ∈ 𝔐.Vgen s := fun i => by
    rw [← span_flag Fl s, ← flagStep_top, ← hF, flagStep_top]; exact Submodule.subset_span ⟨i, rfl⟩
  have key : (∀ w ∈ (Dc t).om', ∀ i, d * w (b i) ∈ regAt 𝔐.ξ q) ∧
      ∀ w : Module.Dual Ω 𝔐.Li, w ∘ₗ prj 𝔐 σ' = w → (∀ i, d * w (b i) ∈ regAt 𝔐.ξ q) →
        ∃ w₀ ∈ Submodule.span (regAt 𝔐.ξ q) ((Dc t).om' : Set (Module.Dual Ω 𝔐.Li)), w₀ ∘ₗ prj 𝔐 σ' = w := by
    by_cases hf : InFibre 𝔐.ξ p q
    · have hV : 𝔐.V s q = 𝔐.HT p s q :=
        Lat.patch_of_unique S _ _ hpS hf fun p' hp' h => hz p' (𝔐.S_prime p' hp') h
      have hom := hD.om'_loc t q hq hf
      constructor
      · intro w hw i
        have h1 := (hfib q hq hz _).1 (hV ▸ hbV i)
        have h2 := ((𝔐.M.mem_htDual_iff _ _ _ _ q _).1 h1).2 w (by
          show w ∈ omP 𝔐 p q
          rw [hom]; exact Submodule.subset_span hw)
        simpa using h2
      · intro w hw hreg
        obtain ⟨U', hU', f, hfs, hf'⟩ := hfree.2 s q hf
        have hf' := hf' q hf hU'
        haveI : FiniteDimensional Ω (𝔐.Vgen s) := by
          rw [← span_flag Fl s]; exact FiniteDimensional.span_of_finite Ω (Set.finite_range _)
        have h1 := mem_span_of_dual (regAt 𝔐.ξ q) f hf'.1 hfs ((𝔐.Vgen s).dualRestrict w) fun e he => by
          have h2 : (e : 𝔐.Li) ∈ 𝔐.M.htDual 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb s) q := by
            refine (𝔐.M.mem_htDual_iff _ _ _ _ q _).2 ⟨e.2, fun w' hw' => ?_⟩
            have h3 : (𝔐.Vgen s).dualRestrict w' ∈ Submodule.span (regAt 𝔐.ξ q) (Set.range f) := by
              rw [← hf'.2]; exact ⟨w', hw', rfl⟩
            exact apply_mem_of_span (regAt 𝔐.ξ q) (Module.Dual.eval Ω _ e) _ (by rintro _ ⟨j, rfl⟩; exact he j) _ h3
          have h4 : d⁻¹ • (e : 𝔐.Li) ∈ 𝔐.V s q := by
            rw [hV, hfib q hq hz, smul_smul, mul_inv_cancel₀ hd, one_smul]; exact h2
          rw [hb.2] at h4
          have h5 := apply_mem_of_span (regAt 𝔐.ξ q) (d • w) _ (by rintro _ ⟨j, rfl⟩; exact hreg j) _ h4
          simpa [inv_mul_cancel_left₀ hd] using h5
        rw [← hf'.2] at h1
        obtain ⟨w₀, hw₀, h2⟩ := h1
        refine ⟨w₀, hom ▸ hw₀, ?_⟩
        rw [← hw]
        ext x
        exact LinearMap.congr_fun h2 ⟨_, prj_mem hσ x⟩
    · have hV : 𝔐.V s q = 𝔐.dR s q :=
        Lat.patch_of_not S _ _ fun p' hp' h => hf (hz p' (𝔐.S_prime p' hp') h ▸ h)
      obtain ⟨hdu, hσR⟩ := hoff q hq hz hf
      have hom := hD.om_loc t q hq hz
      have hpu : unitAt 𝔐.ξ q (p : Ω) := not_not.1 hf
      constructor
      · intro w hw i
        have h1 : (Dc t).om' ≤ (Dc t).om := sup_le (Submodule.span_le.2 (by rintro _ ⟨x, rfl⟩; exact (Dc t).h_mem x))
          (by rintro _ ⟨x, hx, rfl⟩; exact (Dc t).om.smul_mem _ hx)
        have h2 : w ∈ 𝔐.M.omLat q := by rw [hom]; exact Submodule.subset_span (h1 hw)
        exact mul_mem hdu.2.1 (h2 _ (hV ▸ hbV i : b i ∈ 𝔐.dR s q).1)
      · intro w hw hreg
        refine ⟨w, ?_, hw⟩
        have h1 : w ∈ 𝔐.M.omLat q := by
          intro e he
          have h2 : prj 𝔐 σ' e ∈ 𝔐.V s q := by
            rw [hV]
            refine ⟨?_, prj_mem hσ e⟩
            simp only [prj, eigProj, LinearMap.sum_apply, LinearMap.smul_apply]
            refine Submodule.sum_mem _ fun k _ => ?_
            haveI := 𝔐.t.act.hom (H.bar (RingOfIntegers.basis E k))
            exact Submodule.smul_mem (𝔐.M.lat q) (⟨_, hσR _⟩ : regAt 𝔐.ξ q)
              (lat_stable 𝔐.M _ _ (𝔐.act (H.bar (RingOfIntegers.basis E k))) q e he)
          rw [hb.2] at h2
          rw [← hw]
          refine apply_mem_of_span (regAt 𝔐.ξ q) w _ ?_ _ h2
          rintro _ ⟨j, rfl⟩
          have := mul_mem hdu.2.2 (hreg j)
          rwa [inv_mul_cancel_left₀ hd] at this
        rw [hom] at h1
        refine Submodule.span_le.2 ?_ h1
        intro x hx
        have h3 : ((p : chartRing o (mseg y) t.1) ^ 𝔐.R p) • x ∈ (Dc t).om' :=
          Submodule.mem_sup_right ⟨x, hx, rfl⟩
        have h4 := Submodule.smul_mem (Submodule.span (regAt 𝔐.ξ q) ((Dc t).om' : Set (Module.Dual Ω 𝔐.Li)))
          (⟨_, pow_mem hpu.2.2 (𝔐.R p)⟩ : regAt 𝔐.ξ q) (Submodule.subset_span h3)
        have h5 : ((p : Ω)⁻¹ ^ 𝔐.R p) • (((p : chartRing o (mseg y) t.1) ^ 𝔐.R p : chartRing o (mseg y) t.1) : Ω) • x
            = x := by
          rw [smul_smul]
          simp [hpu.1]
        exact h5 ▸ h4
  have hP := eigProj_eq_comp (Dc t).ρΩ (hD.act t) σ'
  refine ⟨regAt 𝔐.ξ q, hR, b, hb.1, hF, fun i => ?_, ?_, fun w hw hreg => ?_⟩
  · obtain ⟨τ, hτ⟩ := exists_lead (Fl.b s) b hF i
    have h1 := FlagGrGen.gr_isGenAt _ _ _ _ (𝔐.V s) _ (Fl.b s) b q i τ (li_flag Fl s) hF hb hτ
    exact ⟨τ, hτ, (hg q hq i τ h1).1, (hg q hq i τ h1).2, h1.1⟩
  · rintro _ ⟨w, hw, rfl⟩ i
    show d * eigProj (Dc t).ρΩ σ' w (b i) ∈ _
    rw [hP, LinearMap.comp_apply, prj_of_mem hσ (hbG i)]
    exact key.1 w hw i
  · obtain ⟨w₀, h0, rfl⟩ := key.2 w hw hreg
    refine exists_smul_mem m (regAt 𝔐.ξ q) hR _ _ ?_
    rw [← hP]
    clear hw hreg
    induction h0 using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul c x _ hx =>
      have : eigProj (Dc t).ρΩ σ' (c • x) = c • eigProj (Dc t).ρΩ σ' x := map_smul _ (c : Ω) x
      rw [this]; exact Submodule.smul_mem _ c hx

theorem label_basis [Fact p.Prime] (hpS : p ∈ S)
    (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω))
    {Dc : ∀ s : {s : ∀ k, J k // mseg y s ≠ 0},
      HTChart (chartRing o (mseg y) s.1) Ω (cmConj E) p (𝔐.R p) (D.p + D.q) (Module.Dual Ω 𝔐.Li)}
    (hD : IsHTFamily 𝔐 p o Dc) (hfree : HTFree 𝔐 p) (Fl : 𝔐.Flag) (t : {s : ∀ k, J k // mseg y s ≠ 0})
    (s : CMType H ⊕ CMType H) (σ' : E →+* Ω) (hσ : ∀ a : 𝓞 E, σ' a = 𝔐.emb s (H.bar a)) (d : Ω) (hd : d ≠ 0)
    (g : Fin (labelRk D s) → Ω) (hg0 : ∀ i, g i ≠ 0)
    (hfib : ∀ q, InChart 𝔐.ξ (mseg y) t.1 q → OverZp 𝔐 p q → ∀ e, e ∈ 𝔐.HT p s q ↔
      d • e ∈ 𝔐.M.htDual 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb s) q)
    (hoff : ∀ q, InChart 𝔐.ξ (mseg y) t.1 q → OverZp 𝔐 p q → ¬ InFibre 𝔐.ξ p q →
      unitAt 𝔐.ξ q d ∧ ∀ x : E, σ' x ∈ regAt 𝔐.ξ q)
    (hg : ∀ q, InChart 𝔐.ξ (mseg y) t.1 q → ∀ i τ, ((𝔐.V s).gr (Fl.b s) i).IsGenAt q τ →
      τ / g i ∈ regAt 𝔐.ξ q ∧ g i / τ ∈ regAt 𝔐.ξ q) :
    ∃ n : Module.Basis (Fin (labelRk D s)) (chartRing o (mseg y) t.1) ((Dc t).omHT σ'),
      ∀ i, (∀ j < i, (n i).1 (Fl.b s j) = 0) ∧ (n i).1 (Fl.b s i) = (d * g i)⁻¹ := by
  refine exists_basis_frames (prj 𝔐 σ') (Fl.b s) (fun e => span_flag Fl s ▸ prj_mem hσ e)
    (fun e he => prj_of_mem hσ (span_flag Fl s ▸ he)) _ ?_ d hd g hg0
    (locFrame hpS ho hD hfree Fl t s σ' hσ d hd g hfib hoff hg)
  rintro _ ⟨w, -, rfl⟩
  show eigProj (Dc t).ρΩ σ' w ∘ₗ _ = eigProj (Dc t).ρΩ σ' w
  rw [eigProj_eq_comp (Dc t).ρΩ (hD.act t) σ']
  ext x
  simp only [LinearMap.comp_apply, prj_of_mem hσ (prj_mem hσ x)]

theorem omHT_comp {Dc : ∀ s : {s : ∀ k, J k // mseg y s ≠ 0},
      HTChart (chartRing o (mseg y) s.1) Ω (cmConj E) p (𝔐.R p) (D.p + D.q) (Module.Dual Ω 𝔐.Li)}
    (hD : IsHTFamily 𝔐 p o Dc) (t : {s : ∀ k, J k // mseg y s ≠ 0})
    {s : CMType H ⊕ CMType H} {σ' : E →+* Ω} (hσ : ∀ a : 𝓞 E, σ' a = 𝔐.emb s (H.bar a)) :
    ∀ w ∈ (Dc t).omHT σ', w ∘ₗ prj 𝔐 σ' = w := by
  rintro _ ⟨w, -, rfl⟩
  show eigProj (Dc t).ρΩ σ' w ∘ₗ _ = eigProj (Dc t).ρΩ σ' w
  rw [eigProj_eq_comp (Dc t).ρΩ (hD.act t) σ']
  ext x
  simp only [LinearMap.comp_apply, prj_of_mem hσ (prj_mem hσ x)]

theorem diff_facts {A : Subalgebra o Ω} {σ : E →+* Ω} {ds : A} (h : GeneratesDiff σ ds) :
    (∀ δ ∈ differentIdeal ℤ (𝓞 E), ∃ a : A, σ δ = a * ds) ∧ (ds : Ω) ≠ 0 ∧
      (ds : Ω) ∈ Submodule.span A {y : Ω | ∃ x ∈ differentIdeal ℤ (𝓞 E), y = σ (x : E)} := by
  have h1 : ∀ δ ∈ differentIdeal ℤ (𝓞 E), ∃ a : A, σ δ = a * ds := by
    intro δ hδ
    have : σ δ ∈ Submodule.span A {algebraMap A Ω ds} := by
      rw [h]; exact Submodule.subset_span ⟨δ, hδ, rfl⟩
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 this
    exact ⟨a, ha.symm⟩
  refine ⟨h1, fun h0 => ?_, ?_⟩
  · obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 E))
    obtain ⟨a, ha⟩ := h1 x hx
    rw [h0, mul_zero, map_eq_zero] at ha
    exact hx0 (by exact_mod_cast ha)
  · rw [← h]; exact Submodule.mem_span_singleton_self _

theorem off_facts {A : Subalgebra o Ω} {σ : E →+* Ω} {ds : A} (h : GeneratesDiff σ ds) {q : Cpt 𝔐.ξ}
    (hA : ∀ a ∈ A, a ∈ regAt 𝔐.ξ q) (hz : OverZp 𝔐 p q) (hf : ¬ InFibre 𝔐.ξ p q) :
    unitAt 𝔐.ξ q (ds : Ω) ∧ ∀ x : E, σ x ∈ regAt 𝔐.ξ q := by
  obtain ⟨h1, h0, -⟩ := diff_facts h
  have key : ∀ x : E, ∃ u ∈ regAt 𝔐.ξ q, σ x = u * ds := by
    intro x
    obtain ⟨n, hn, δ, hδ, hx⟩ := exists_nat_diff x
    obtain ⟨a, ha⟩ := h1 δ hδ
    have hu := unitAt_nat q n hn fun r hr _ => by
      by_contra hr'
      exact hf (hz r hr hr' ▸ hr')
    refine ⟨(n : Ω)⁻¹ * a, mul_mem hu.2.2 (hA _ a.2), ?_⟩
    rw [_root_.mul_assoc, ← ha, hx, map_mul, map_natCast, inv_mul_cancel_left₀ hu.1]
  refine ⟨⟨h0, hA _ ds.2, ?_⟩, fun x => ?_⟩
  · obtain ⟨u, hu, h2⟩ := key 1
    rw [map_one] at h2
    rwa [← eq_inv_of_mul_eq_one_left h2.symm]
  · obtain ⟨u, hu, h2⟩ := key x
    rw [h2]; exact mul_mem hu (hA _ ds.2)

theorem mem_htW {A : Subalgebra o Ω} {σ : E →+* Ω} {ds : A} (h : GeneratesDiff σ ds) {q : Cpt 𝔐.ξ}
    (hA : ∀ a ∈ A, a ∈ regAt 𝔐.ξ q) (σ₀ : 𝓞 E →+* Ω) (hσ : ∀ a : 𝓞 E, σ (a : E) = σ₀ a) (n : ℕ) (e : 𝔐.Li) :
    e ∈ 𝔐.M.htW 𝔐.t.PP.L n 𝔐.ρ σ₀ (differentIdeal ℤ (𝓞 E)) q ↔
      (ds : Ω) • e ∈ 𝔐.M.htDual 𝔐.t.PP.L n 𝔐.ρ σ₀ q := by
  obtain ⟨h1, h0, h2⟩ := diff_facts h
  constructor
  · intro he
    induction he using Submodule.span_induction with
    | mem x hx =>
      generalize (ds : Ω) = z at h2
      induction h2 using Submodule.span_induction with
      | mem u hu => obtain ⟨δ, hδ, rfl⟩ := hu; rw [hσ]; exact hx.2 δ hδ
      | zero => rw [zero_smul]; exact zero_mem _
      | add u v _ _ hu hv => rw [add_smul]; exact add_mem hu hv
      | smul a u _ hu =>
        have : (a • u) • x = (⟨a, hA _ a.2⟩ : regAt 𝔐.ξ q) • u • x := mul_smul (a : Ω) u x
        rw [this]; exact Submodule.smul_mem _ _ hu
    | zero => rw [smul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | smul a x _ hx =>
      have : (ds : Ω) • a • x = a • (ds : Ω) • x := smul_comm (ds : Ω) (a : Ω) x
      rw [this]; exact Submodule.smul_mem _ _ hx
  · intro he
    refine Submodule.subset_span ⟨?_, fun δ hδ => ?_⟩
    · have := (GlobalTheory.CompanionTheory.Ar.eigSp 𝔐.ρ σ₀).smul_mem (ds : Ω)⁻¹ (𝔐.M.mem_eigSp_of_mem_htDual _ _ _ _ he)
      rwa [smul_smul, inv_mul_cancel₀ h0, one_smul] at this
    · obtain ⟨a, ha⟩ := h1 δ hδ
      rw [← hσ, ha, mul_smul]
      exact Submodule.smul_mem _ (⟨a, hA _ a.2⟩ : regAt 𝔐.ξ q) he

theorem chartMon_ne_zero {t : ∀ k, J k} (ht : mseg y t ≠ 0) (a : K → ℤ) : chartMon y t a ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun k hk => zpow_ne_zero _ (Finset.prod_ne_zero_iff.1 ht k hk)

theorem rootIdx_left (τ : CMType H) (a : Fin D.p) :
    HodgeCpt.rootIdx D (τ, Fin.castAdd D.q a) = ⟨.inl τ, a⟩ := dif_pos a.2

theorem rootIdx_right (τ : CMType H) (a : Fin D.q) :
    HodgeCpt.rootIdx D (τ, Fin.natAdd D.p a.rev) = ⟨.inr τ, a⟩ := by
  unfold HodgeCpt.rootIdx
  rw [dite_eq_right (by simp)]
  congr 1
  apply Fin.ext
  have := a.2
  simp only [Fin.val_natAdd, Fin.val_rev]
  omega

end Label

theorem chart_flag_bases : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime] (hpS : p ∈ S) (o : Type) [CommRing o] [Algebra o Ω] (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω)) (Dc : ∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, HTChart (chartRing o (mseg y) s.1) Ω (cmConj E) p (𝔐.R p) (D.p + D.q) (Module.Dual Ω 𝔐.Li)) (Fl : 𝔐.Flag) (xdeg : CMType H × Fin (D.p + D.q) → K → ℤ) (e : CMType H × Fin (D.p + D.q) → Ω) (τ : CMType H) (σ : E →+* Ω) (d : Ω), IsHTFamily 𝔐 p o Dc → HTFree 𝔐 p → Fl.RootLines xdeg e → (∀ a : 𝓞 E, σ (a : E) = 𝔐.emb (Sum.inl τ) a) → (∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, ∃ ds : chartRing o (mseg y) s.1, (ds : Ω) = d ∧ GeneratesDiff σ ds) → ∃ (wW : Fin D.p → Module.Dual Ω (Module.Dual Ω 𝔐.Li)) (wM : Fin D.q → Module.Dual Ω 𝔐.Li), ∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, ∃ (bW : Module.Basis (Fin D.p) (chartRing o (mseg y) s.1) (Module.Dual (chartRing o (mseg y) s.1) ((Dc s).omHT (σ.comp (cmConj E).toRingHom)))) (bM : Module.Basis (Fin D.q) (chartRing o (mseg y) s.1) ((Dc s).omHT σ)), (∀ a : Fin D.p, ∃ cf : Fin D.p → Ω, (∀ a', a < a' → cf a' = 0) ∧ cf a = chartMon y s.1 (xdeg (τ, Fin.castAdd D.q a)) ∧ ∀ z : (Dc s).omHT (σ.comp (cmConj E).toRingHom), (bW a z).1 = ∑ a', cf a' * wW a' z.1) ∧ ∀ a : Fin D.q, ∃ cf : Fin D.q → Ω, (∀ a', a < a' → cf a' = 0) ∧ cf a = chartMon y s.1 (xdeg (τ, Fin.natAdd D.p a)) ∧ (bM a).1 = ∑ a', cf a' • wM a' := by
  intro E _ _ _ H D l Xo c O _ β Y S Ω _ K _ J _ y 𝔐 p hp hpS o _ _ ho Dc Fl xdeg e τ σ d hD hfree hroot hσ hdiff
  have he : ∀ r, e r ≠ 0 := fun r => (hroot r).1
  have hbb : ∀ a : 𝓞 E, H.bar (H.bar a) = a := fun a => by
    apply Subtype.ext
    show ((H.bar (H.bar a) : 𝓞 E) : E) = a
    rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]
  have hσM : ∀ a : 𝓞 E, σ a = 𝔐.emb (.inr τ) (H.bar a) := fun a => by
    rw [hσ]
    show _ = 𝔐.emb (.inl τ) (H.bar (H.bar a))
    rw [hbb]
  have hσW : ∀ a : 𝓞 E, σ.comp (cmConj E).toRingHom a = 𝔐.emb (.inl τ) (H.bar a) := fun a => by
    rw [← hσ, H.bar_eq]; rfl
  obtain ⟨wM, hwM⟩ := shape_M (o := o) (r := D.q) (prj 𝔐 σ) (Fl.b (.inr τ)) (li_flag Fl _)
    (fun x => by have := prj_mem hσM x; rw [← span_flag Fl] at this; exact this)
    (fun a => e (τ, Fin.natAdd D.p a)) (fun a => he _)
  refine ⟨fun a => Module.Dual.eval Ω _ ((d * e (τ, Fin.castAdd D.q a)) • Fl.b (.inl τ) a), wM, fun t => ?_⟩
  obtain ⟨ds, rfl, hds⟩ := hdiff t
  have hd0 := (diff_facts hds).2.1
  have hm := fun r => chartMon_ne_zero t.2 (xdeg r)
  obtain ⟨nW, hnW⟩ := label_basis hpS ho hD hfree Fl t (.inl τ) _ hσW ds hd0
    (fun a : Fin D.p => chartMon y t.1 (xdeg (τ, Fin.castAdd D.q a)) * e (τ, Fin.castAdd D.q a))
    (fun a => mul_ne_zero (hm _) (he _))
    (fun q hq hz x => mem_htW hds (chart_le hp.out ho hq hz) _ hσ _ x)
    (fun q hq hz hf => ⟨(off_facts hds (chart_le hp.out ho hq hz) hz hf).1,
      fun x => (off_facts hds (chart_le hp.out ho hq hz) hz hf).2 _⟩)
    (fun q hq (a : Fin D.p) u hu => by
      have h1 := (hroot (τ, Fin.castAdd D.q a)).2 q trivial t.1 hq
      have h2 : HodgeCpt.rootSgn D (τ, Fin.castAdd D.q a) = 1 := if_pos a.2
      unfold HodgeCpt.Flag.rootLat at h1
      rw [rootIdx_left, h2] at h1
      have h3 := tens_gen _ q 1 (Or.inl rfl) u _ hu h1
      rw [zpow_one] at h3
      exact h3)
  obtain ⟨nM, hnM⟩ := label_basis hpS ho hD hfree Fl t (.inr τ) _ hσM 1 one_ne_zero
    (fun a : Fin D.q => (chartMon y t.1 (xdeg (τ, Fin.natAdd D.p a.rev)) * e (τ, Fin.natAdd D.p a.rev))⁻¹)
    (fun a => inv_ne_zero (mul_ne_zero (hm _) (he _)))
    (fun q hq hz x => by rw [one_smul]; rfl)
    (fun q hq hz hf => ⟨⟨one_ne_zero, one_mem _, by rw [inv_one]; exact one_mem _⟩,
      (off_facts hds (chart_le hp.out ho hq hz) hz hf).2⟩)
    (fun q hq (a : Fin D.q) u hu => by
      have h1 := (hroot (τ, Fin.natAdd D.p a.rev)).2 q trivial t.1 hq
      have h2 : HodgeCpt.rootSgn D (τ, Fin.natAdd D.p a.rev) = -1 := if_neg (by simp)
      unfold HodgeCpt.Flag.rootLat at h1
      rw [rootIdx_right, h2] at h1
      have h3 := tens_gen _ q (-1) (Or.inr rfl) u _ hu h1
      rw [zpow_neg_one] at h3
      have e1 : ∀ x : Ω, u / x⁻¹ = x / u⁻¹ := fun x => by rw [div_inv_eq_mul, div_inv_eq_mul, mul_comm]
      have e2 : ∀ x : Ω, x⁻¹ / u = u⁻¹ / x := fun x => by rw [div_eq_mul_inv, div_eq_mul_inv, mul_comm]
      rw [e1, e2]
      exact ⟨h3.2, h3.1⟩)
  obtain ⟨bW, hbW⟩ := shape_alt (r := D.p) (Fl.b (.inl τ)) (fun a => ds * e (τ, Fin.castAdd D.q a))
    (fun a => mul_ne_zero hd0 (he _)) _ (fun a => chartMon y t.1 (xdeg (τ, Fin.castAdd D.q a))) (fun a => hm _) nW
    (fun i => ⟨(hnW i).1, (hnW i).2.trans (by rw [mul_left_comm])⟩)
  obtain ⟨bM, hbM⟩ := hwM _ _ (omHT_comp hD t hσM) (fun a => chartMon y t.1 (xdeg (τ, Fin.natAdd D.p a))) nM
    (fun i => ⟨(hnM i).1, (hnM i).2.trans (by rw [_root_.one_mul, inv_inv])⟩)
  exact ⟨bW, bM, hbW, hbM⟩

end PositivityTheory.HtPt.Flagb
