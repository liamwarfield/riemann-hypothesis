module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.PhiSub
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MSpBasis

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IntertwinerIso
open Polynomial Matrix IsLocalRing TensorProduct

theorem UpperTheory.V.AlgebraTools.intertwiner_iso :
    ∀ {F Γ : Type} [Field F] {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (ρ : Γ → Matrix m m F) (ρ' : Γ → Matrix n n F), Submodule.span F (Set.range ρ) = ⊤ → Submodule.span F (Set.range ρ') = ⊤ → (∀ V : Matrix m n F, (∀ g, ρ g * V = V * ρ' g) → V ≠ 0 → ∃ V' : Matrix n m F, V * V' = 1 ∧ V' * V = 1) ∧ ∀ V : Matrix m m F, (∀ g, ρ g * V = V * ρ g) → ∃ c : F, V = c • (1 : Matrix m m F) := by
  intro F Γ _ m n _ _ _ _ ρ ρ' hρ hρ'
  refine ⟨fun V hV hV0 => ?_, fun V hV => ?_⟩
  · have hR : ∀ A : Matrix m m F, ∃ C : Matrix n n F, A * V = V * C := by
      intro A
      have hA : A ∈ Submodule.span F (Set.range ρ) := by rw [hρ]; exact Submodule.mem_top
      induction hA using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨g, rfl⟩ := hx
        exact ⟨ρ' g, hV g⟩
      | zero => exact ⟨0, by rw [Matrix.zero_mul, Matrix.mul_zero]⟩
      | add x y _ _ hx hy =>
        obtain ⟨C, hC⟩ := hx
        obtain ⟨D, hD⟩ := hy
        exact ⟨C + D, by rw [Matrix.add_mul, Matrix.mul_add, hC, hD]⟩
      | smul a x _ hx =>
        obtain ⟨C, hC⟩ := hx
        exact ⟨a • C, by rw [Matrix.smul_mul, hC, Matrix.mul_smul]⟩
    have hL : ∀ B : Matrix n n F, ∃ A : Matrix m m F, V * B = A * V := by
      intro B
      have hB : B ∈ Submodule.span F (Set.range ρ') := by rw [hρ']; exact Submodule.mem_top
      induction hB using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨g, rfl⟩ := hx
        exact ⟨ρ g, (hV g).symm⟩
      | zero => exact ⟨0, by rw [Matrix.zero_mul, Matrix.mul_zero]⟩
      | add x y _ _ hx hy =>
        obtain ⟨C, hC⟩ := hx
        obtain ⟨D, hD⟩ := hy
        exact ⟨C + D, by rw [Matrix.add_mul, Matrix.mul_add, hC, hD]⟩
      | smul a x _ hx =>
        obtain ⟨C, hC⟩ := hx
        exact ⟨a • C, by rw [Matrix.smul_mul, ← hC, Matrix.mul_smul]⟩
    have inj : Function.Injective (Matrix.toLin' V) := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro x hx
      rw [Matrix.toLin'_apply] at hx
      by_contra hne
      obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
      have hj' : x j ≠ 0 := by simpa using hj
      apply hV0
      ext i k
      obtain ⟨A, hA⟩ := hL (Matrix.single k j (x j)⁻¹)
      have h1 : V *ᵥ (Matrix.single k j (x j)⁻¹ *ᵥ x) = 0 := by
        rw [Matrix.mulVec_mulVec, hA, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]
      rw [Matrix.single_mulVec, inv_mul_cancel₀ hj'] at h1
      have h2 := congrFun h1 i
      change (V *ᵥ Pi.single k 1) i = 0 at h2
      rw [Matrix.mulVec_single_one] at h2
      simpa using h2
    have surj : Function.Surjective (Matrix.toLin' V) := by
      obtain ⟨i0, k0, h0⟩ : ∃ i k, V i k ≠ 0 := by
        by_contra h
        push_neg at h
        exact hV0 (Matrix.ext fun i k => by simp [h i k])
      intro y
      let A : Matrix m m F := Matrix.of fun i a => if a = i0 then y i * (V i0 k0)⁻¹ else 0
      obtain ⟨C, hC⟩ := hR A
      refine ⟨C *ᵥ Pi.single k0 1, ?_⟩
      rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← hC, ← Matrix.mulVec_mulVec,
        Matrix.mulVec_single_one]
      funext i
      simp [A, Matrix.mulVec, dotProduct, ite_mul, h0]
    let e := LinearEquiv.ofBijective (Matrix.toLin' V) ⟨inj, surj⟩
    have he1 : Matrix.toLin' V ∘ₗ (e.symm : (m → F) →ₗ[F] (n → F)) = LinearMap.id :=
      LinearMap.ext fun y => e.apply_symm_apply y
    have he2 : (e.symm : (m → F) →ₗ[F] (n → F)) ∘ₗ Matrix.toLin' V = LinearMap.id :=
      LinearMap.ext fun y => e.symm_apply_apply y
    refine ⟨LinearMap.toMatrix' (e.symm : (m → F) →ₗ[F] (n → F)), ?_, ?_⟩
    · have h := LinearMap.toMatrix'_comp (Matrix.toLin' V) (e.symm : (m → F) →ₗ[F] (n → F))
      rw [he1, LinearMap.toMatrix'_id, LinearMap.toMatrix'_toLin'] at h
      exact h.symm
    · have h := LinearMap.toMatrix'_comp (e.symm : (m → F) →ₗ[F] (n → F)) (Matrix.toLin' V)
      rw [he2, LinearMap.toMatrix'_id, LinearMap.toMatrix'_toLin'] at h
      exact h.symm
  · have hC : ∀ A : Matrix m m F, Commute A V := by
      intro A
      have hA : A ∈ Submodule.span F (Set.range ρ) := by rw [hρ]; exact Submodule.mem_top
      induction hA using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨g, rfl⟩ := hx
        exact hV g
      | zero => exact Commute.zero_left V
      | add x y _ _ hx hy => exact hx.add_left hy
      | smul a x _ hx => exact hx.smul_left a
    obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_of_commute_single (fun i j _ => hC _)
    refine ⟨c, ?_⟩
    rw [← hc]
    ext i j
    simp [Matrix.one_apply, Matrix.diagonal_apply]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DensityProd
open Polynomial Matrix IsLocalRing TensorProduct

private theorem sum_matrix_single_diag_one_eq_one {F : Type} [Field F] {n : Type} [Fintype n] [DecidableEq n] :
    ∑ i : n, Matrix.single i i (1 : F) = 1 := by
  ext u v
  by_cases h : u = v
  · subst h
    simp [Matrix.sum_apply, Matrix.single_apply, Matrix.one_apply]
  · simp [Matrix.sum_apply, Matrix.single_apply, Matrix.one_apply, h]
    have he : (Finset.univ.filter fun w : n => w = u ∧ w = v) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      rintro w - ⟨rfl, rfl⟩
      exact h rfl
    rw [he]
    simp

private theorem intertwiner_of_ker {F : Type} [Field F] {σ : Type} (d : σ → Type)
    [∀ s, Fintype (d s)] [∀ s, DecidableEq (d s)] [∀ s, Nonempty (d s)]
    (S : Subalgebra F (∀ s, Matrix (d s) (d s) F)) (s t : σ)
    (ht : ∀ B : Matrix (d t) (d t) F, ∃ x ∈ S, x t = B)
    (hk : ∀ x ∈ S, x t = 0 → x s = 0) :
    ∃ V : Matrix (d s) (d t) F, V ≠ 0 ∧ ∀ x ∈ S, x s * V = V * x t := by
  have key : ∀ x ∈ S, ∀ y ∈ S, x t = y t → x s = y s := by
    intro x hx y hy h
    have := hk (x - y) (S.sub_mem hx hy) (by rw [Pi.sub_apply, h, sub_self])
    rw [Pi.sub_apply, sub_eq_zero] at this
    exact this
  obtain ⟨i0⟩ := (inferInstance : Nonempty (d t))
  choose xx hxS hxt using fun j => ht (Matrix.single j i0 (1 : F))
  choose z hzS hzt using fun j => ht (Matrix.single i0 j (1 : F))
  have hne : xx i0 s ≠ 0 := by
    intro h0
    have hx0 : ∀ j, xx j s = 0 := by
      intro j
      have := key (xx j * xx i0) (S.mul_mem (hxS j) (hxS i0)) (xx j) (hxS j)
        (by rw [Pi.mul_apply, hxt, hxt, Matrix.single_mul_single_same, one_mul])
      rw [← this, Pi.mul_apply, h0, mul_zero]
    have h1 := key (∑ j, xx j * z j) (Subalgebra.sum_mem _ fun j _ => S.mul_mem (hxS j) (hzS j)) 1 S.one_mem
      (by
        rw [Finset.sum_apply]
        simp only [Pi.mul_apply, hxt, hzt, Matrix.single_mul_single_same, one_mul, Pi.one_apply]
        exact sum_matrix_single_diag_one_eq_one)
    rw [Finset.sum_apply] at h1
    simp only [Pi.mul_apply, hx0, zero_mul, Finset.sum_const_zero, Pi.one_apply] at h1
    exact zero_ne_one h1
  obtain ⟨a, b, hab⟩ : ∃ a b, xx i0 s a b ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (Matrix.ext h)
  refine ⟨Matrix.of fun u j => xx j s u b, ?_, ?_⟩
  · intro hV
    apply hab
    have := congrFun (congrFun hV a) i0
    simpa using this
  · intro x hx
    ext u k
    have e := key (x * xx k) (S.mul_mem hx (hxS k)) (∑ j, x t j k • xx j)
      (Subalgebra.sum_mem _ fun j _ => S.smul_mem (hxS j) _) (by
        rw [Pi.mul_apply, hxt, Finset.sum_apply]
        simp only [Pi.smul_apply, hxt]
        ext p q
        by_cases hq : i0 = q <;> simp [Matrix.mul_apply, Matrix.sum_apply, Matrix.single_apply, hq])
    have e2 := congrFun (congrFun e u) b
    simp only [Pi.mul_apply, Finset.sum_apply, Matrix.sum_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.mul_apply] at e2
    simp only [Matrix.mul_apply, Matrix.of_apply]
    rw [e2]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _

private theorem separate {F : Type} [Field F] {σ : Type} (d : σ → Type)
    [∀ s, Fintype (d s)] [∀ s, DecidableEq (d s)] [∀ s, Nonempty (d s)]
    (S : Subalgebra F (∀ s, Matrix (d s) (d s) F)) (s t : σ)
    (hs : ∀ B : Matrix (d s) (d s) F, ∃ x ∈ S, x s = B)
    (hk : ∃ x ∈ S, x t = 0 ∧ x s ≠ 0) : ∃ x ∈ S, x t = 0 ∧ x s = 1 := by
  obtain ⟨x, hxS, hxt, hxs⟩ := hk
  obtain ⟨a, b, hab⟩ : ∃ a b, x s a b ≠ 0 := by
    by_contra h
    push_neg at h
    exact hxs (Matrix.ext h)
  choose p hpS hps using fun i => hs (Matrix.single i a (x s a b)⁻¹)
  choose q hqS hqs using fun i => hs (Matrix.single b i (1 : F))
  refine ⟨∑ i, p i * x * q i, ?_, ?_, ?_⟩
  · exact Subalgebra.sum_mem _ fun i _ => S.mul_mem (S.mul_mem (hpS i) hxS) (hqS i)
  · rw [Finset.sum_apply]
    simp [Pi.mul_apply, hxt]
  · rw [Finset.sum_apply]
    simp only [Pi.mul_apply, hps, hqs, Matrix.single_mul_mul_single, inv_mul_cancel₀ hab, one_mul]
    ext u v
    by_cases h : u = v
    · subst h
      simp [Matrix.sum_apply, Matrix.single_apply, Matrix.one_apply]
    · simp [Matrix.sum_apply, Matrix.single_apply, Matrix.one_apply, h]
      have he : (Finset.univ.filter fun w : d s => w = u ∧ w = v) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        rintro w - ⟨rfl, rfl⟩
        exact h rfl
      rw [he]
      simp

theorem UpperTheory.V.AlgebraTools.density_prod :
    ∀ {F Γ : Type} [Field F] [Monoid Γ] {σ : Type} [Fintype σ] [DecidableEq σ] (d : σ → Type) [∀ s, Fintype (d s)] [∀ s, DecidableEq (d s)] [∀ s, Nonempty (d s)] (ρ : ∀ s, Γ →* Matrix (d s) (d s) F), (∀ s, Submodule.span F (Set.range (ρ s)) = ⊤) → (∀ s t, s ≠ t → ∀ V : Matrix (d s) (d t) F, (∀ g, ρ s g * V = V * ρ t g) → V = 0) → Submodule.span F (Set.range fun g => (fun s => ρ s g : ∀ s, Matrix (d s) (d s) F)) = ⊤ := by
  intro F Γ _ _ σ _ _ d _ _ _ ρ hspan hint
  let φ : Γ →* ((s : σ) → Matrix (d s) (d s) F) :=
    { toFun := fun g s => ρ s g
      map_one' := funext fun s => map_one (ρ s)
      map_mul' := fun g h => funext fun s => map_mul (ρ s) g h }
  obtain ⟨S, hSdef⟩ : ∃ S : Subalgebra F ((s : σ) → Matrix (d s) (d s) F),
      S = Algebra.adjoin F (Set.range fun g => (fun s => ρ s g : ∀ s, Matrix (d s) (d s) F)) := ⟨_, rfl⟩
  have hmem : ∀ g, (fun s => ρ s g : ∀ s, Matrix (d s) (d s) F) ∈ S := by
    intro g
    rw [hSdef]
    exact Algebra.subset_adjoin ⟨g, rfl⟩
  have hsurj : ∀ s (B : Matrix (d s) (d s) F), ∃ x ∈ S, x s = B := by
    intro s B
    have hB : B ∈ Submodule.span F (Set.range (ρ s)) := by
      rw [hspan s]
      exact Submodule.mem_top
    induction hB using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨g, rfl⟩ := hy
      exact ⟨_, hmem g, rfl⟩
    | zero => exact ⟨0, S.zero_mem, rfl⟩
    | add y z _ _ hy hz =>
      obtain ⟨x1, h1, e1⟩ := hy
      obtain ⟨x2, h2, e2⟩ := hz
      exact ⟨x1 + x2, S.add_mem h1 h2, by rw [Pi.add_apply, e1, e2]⟩
    | smul c y _ hy =>
      obtain ⟨x1, h1, e1⟩ := hy
      exact ⟨c • x1, S.smul_mem h1 c, by rw [Pi.smul_apply, e1]⟩
  have hsep : ∀ s t, s ≠ t → ∃ x ∈ S, x t = 0 ∧ x s = 1 := by
    intro s t hst
    apply separate d S s t (hsurj s)
    by_contra hno
    push_neg at hno
    obtain ⟨V, hV0, hV⟩ := intertwiner_of_ker d S s t (hsurj t) hno
    exact hV0 (hint s t hst V fun g => hV _ (hmem g))
  have he : ∀ s, ∃ e ∈ S, e s = 1 ∧ ∀ t, t ≠ s → e t = 0 := by
    intro s
    have hT : ∀ T : Finset σ, s ∉ T → ∃ e ∈ S, e s = 1 ∧ ∀ t ∈ T, e t = 0 := by
      intro T
      induction T using Finset.induction_on with
      | empty =>
        intro _
        exact ⟨1, S.one_mem, rfl, by simp⟩
      | @insert t T htT ih =>
        intro hs
        rw [Finset.mem_insert, not_or] at hs
        obtain ⟨e, heS, hes, het⟩ := ih hs.2
        obtain ⟨y, hyS, hyt, hys⟩ := hsep s t hs.1
        refine ⟨e * y, S.mul_mem heS hyS, by rw [Pi.mul_apply, hes, hys, one_mul], ?_⟩
        intro u hu
        rw [Finset.mem_insert] at hu
        rcases hu with rfl | hu
        · rw [Pi.mul_apply, hyt, mul_zero]
        · rw [Pi.mul_apply, het u hu, zero_mul]
    obtain ⟨e, heS, hes, het⟩ := hT (Finset.univ.erase s) (by simp)
    exact ⟨e, heS, hes, fun t ht => het t (by simp [ht])⟩
  have htop : S = ⊤ := by
    rw [eq_top_iff]
    intro Y _
    choose e heS hes het using he
    choose zz hzS hzs using fun s => hsurj s (Y s)
    have hY : Y = ∑ s, zz s * e s := by
      funext u
      rw [Finset.sum_apply, Finset.sum_eq_single u]
      · rw [Pi.mul_apply, hzs, hes, mul_one]
      · intro b _ hb
        rw [Pi.mul_apply, het b u hb.symm, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ u) h
    rw [hY]
    exact Subalgebra.sum_mem _ fun s _ => S.mul_mem (hzS s) (heS s)
  have h2 : Submodule.span F (Set.range fun g => (fun s => ρ s g : ∀ s, Matrix (d s) (d s) F)) =
      Subalgebra.toSubmodule S := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      exact hmem g
    · rw [hSdef, Algebra.adjoin_eq_span, Submodule.span_le]
      intro x hx
      have hx' : x ∈ MonoidHom.mrange φ :=
        (Submonoid.closure_le.mpr (by rintro _ ⟨g, rfl⟩; exact MonoidHom.mem_mrange.mpr ⟨g, rfl⟩)) hx
      obtain ⟨g, rfl⟩ := MonoidHom.mem_mrange.mp hx'
      exact Submodule.subset_span ⟨g, rfl⟩
  rw [h2, htop]
  simp
end

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem finSumFinEquiv_inl_lt_and_inr_not_lt {n a b : ℕ} (hn : n = a + b) (i : Fin n) :
    (∀ p, ((finCongr hn).trans finSumFinEquiv.symm) i = Sum.inl p → (i : ℕ) < a) ∧
    (∀ p, ((finCongr hn).trans finSumFinEquiv.symm) i = Sum.inr p → ¬ (i : ℕ) < a) := by
  constructor
  · intro p hp
    have h := congrArg (fun s => ((finCongr hn).trans finSumFinEquiv.symm).symm s) hp
    simp only [Equiv.symm_apply_apply] at h
    subst h
    simp
  · intro p hp
    have h := congrArg (fun s => ((finCongr hn).trans finSumFinEquiv.symm).symm s) hp
    simp only [Equiv.symm_apply_apply] at h
    subst h
    simp

private theorem submatrix_mem_ev_of_offDiag_blocks_zero {R : Type} [CommRing R] {n a b : ℕ} (hn : n = a + b)
    (Z : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) R)
    (h12 : ∀ i j, Z (Sum.inl i) (Sum.inr j) = 0) (h21 : ∀ i j, Z (Sum.inr i) (Sum.inl j) = 0) :
    Z.submatrix ((finCongr hn).trans finSumFinEquiv.symm) ((finCongr hn).trans finSumFinEquiv.symm)
      ∈ Ev R R n a := by
  simp only [Ev, blkMat, Submodule.mem_top, implies_true, Submodule.mem_bot, true_and, Submodule.mem_mk,
    AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_ofPred_eq]
  intro i j hij
  simp only [Matrix.submatrix_apply]
  rcases hi : ((finCongr hn).trans finSumFinEquiv.symm) i with p | p <;>
    rcases hj : ((finCongr hn).trans finSumFinEquiv.symm) j with q | q
  · exact absurd (iff_of_true ((finSumFinEquiv_inl_lt_and_inr_not_lt hn i).1 p hi) ((finSumFinEquiv_inl_lt_and_inr_not_lt hn j).1 q hj)) hij
  · exact h12 p q
  · exact h21 p q
  · exact absurd (iff_of_false ((finSumFinEquiv_inl_lt_and_inr_not_lt hn i).2 p hi) ((finSumFinEquiv_inl_lt_and_inr_not_lt hn j).2 q hj)) hij

private theorem intertwiner_eq_zero_of_span_eq_univ_of_reverse_zero {K Γ : Type} [Field K] {a b : ℕ} (ha : 1 ≤ a)
    (ρ₁ : Γ → Matrix (Fin a) (Fin a) K) (ρ₂ : Γ → Matrix (Fin b) (Fin b) K)
    (s₁ : Submodule.span K (Set.range ρ₁) = ⊤) (s₂ : Submodule.span K (Set.range ρ₂) = ⊤)
    (i₂₁ : ∀ M : Matrix (Fin b) (Fin a) K, (∀ g, M * ρ₁ g = ρ₂ g * M) → M = 0)
    (V : Matrix (Fin a) (Fin b) K) (hV : ∀ g, ρ₁ g * V = V * ρ₂ g) : V = 0 := by
  by_contra hne
  obtain ⟨W, hVW, hWV⟩ := (UpperTheory.V.AlgebraTools.intertwiner_iso ρ₁ ρ₂ s₁ s₂).1 V hV hne
  have hW : W = 0 := by
    apply i₂₁
    intro g
    calc W * ρ₁ g = W * ρ₁ g * (V * W) := by rw [hVW, Matrix.mul_one]
      _ = W * (ρ₁ g * V) * W := by simp only [Matrix.mul_assoc]
      _ = W * (V * ρ₂ g) * W := by rw [hV g]
      _ = (W * V) * ρ₂ g * W := by simp only [Matrix.mul_assoc]
      _ = ρ₂ g * W := by rw [hWV, Matrix.one_mul]
  rw [hW, Matrix.mul_zero] at hVW
  have := congrFun (congrFun hVW ⟨0, ha⟩) ⟨0, ha⟩
  simp at this

private theorem span_range_fromBlocks_submatrix_eq_ev {K Γ : Type} [Field K] [Monoid Γ] {n a b : ℕ} (hn : n = a + b)
    (ha : 1 ≤ a) (hb : 1 ≤ b)
    (ρ₁ : Γ →* Matrix (Fin a) (Fin a) K) (ρ₂ : Γ →* Matrix (Fin b) (Fin b) K)
    (s₁ : Submodule.span K (Set.range ρ₁) = ⊤) (s₂ : Submodule.span K (Set.range ρ₂) = ⊤)
    (i₁₂ : ∀ V : Matrix (Fin a) (Fin b) K, (∀ g, ρ₁ g * V = V * ρ₂ g) → V = 0)
    (i₂₁ : ∀ V : Matrix (Fin b) (Fin a) K, (∀ g, ρ₂ g * V = V * ρ₁ g) → V = 0) :
    Submodule.span K (Set.range fun g => (Matrix.fromBlocks (ρ₁ g) 0 0 (ρ₂ g)).submatrix
      ((finCongr hn).trans finSumFinEquiv.symm) ((finCongr hn).trans finSumFinEquiv.symm)) = Ev K K n a := by
  set τ := (finCongr hn).trans finSumFinEquiv.symm with hτ
  haveI i3 : ∀ s : Bool, Nonempty (Fin (cond s a b)) := fun s => by
    cases s
    · exact ⟨⟨0, hb⟩⟩
    · exact ⟨⟨0, ha⟩⟩
  let ρ : (s : Bool) → Γ →* Matrix (Fin (cond s a b)) (Fin (cond s a b)) K := fun s => match s with
    | false => ρ₂
    | true => ρ₁
  have hspan : ∀ s, Submodule.span K (Set.range (ρ s)) = ⊤ := by
    intro s
    cases s
    · exact s₂
    · exact s₁
  have hint : ∀ s t, s ≠ t → ∀ V : Matrix (Fin (cond s a b)) (Fin (cond t a b)) K, (∀ g, ρ s g * V = V * ρ t g) → V = 0 := by
    intro s t hst
    cases s <;> cases t
    · exact absurd rfl hst
    · exact i₂₁
    · exact i₁₂
    · exact absurd rfl hst
  have hD := UpperTheory.V.AlgebraTools.density_prod (fun s : Bool => Fin (cond s a b)) ρ hspan hint
  let L : ((s : Bool) → Matrix (Fin (cond s a b)) (Fin (cond s a b)) K) →ₗ[K] Matrix (Fin n) (Fin n) K :=
    { toFun := fun f => (Matrix.fromBlocks (f true) 0 0 (f false)).submatrix τ τ
      map_add' := by
        intro f h
        ext i j
        simp only [Matrix.submatrix_apply, Pi.add_apply, Matrix.add_apply]
        rcases τ i with p | p <;> rcases τ j with q | q <;> simp [Matrix.fromBlocks]
      map_smul' := by
        intro c f
        ext i j
        simp only [Matrix.submatrix_apply, Pi.smul_apply, Matrix.smul_apply, RingHom.id_apply]
        rcases τ i with p | p <;> rcases τ j with q | q <;> simp [Matrix.fromBlocks] }
  have hrange : (Set.range fun g => (Matrix.fromBlocks (ρ₁ g) 0 0 (ρ₂ g)).submatrix τ τ) =
      L '' Set.range (fun g s => ρ s g) := by
    rw [← Set.range_comp]
    rfl
  rw [hrange, Submodule.span_image, hD, Submodule.map_top]
  ext M
  constructor
  · rintro ⟨f, rfl⟩
    apply submatrix_mem_ev_of_offDiag_blocks_zero hn
    · intro i j
      simp [Matrix.fromBlocks]
    · intro i j
      simp [Matrix.fromBlocks]
  · intro hM
    have hM' := hM
    simp only [Ev, blkMat, Submodule.mem_top, implies_true, Submodule.mem_bot, true_and, Submodule.mem_mk,
      AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_ofPred_eq] at hM'
    let Z := M.submatrix τ.symm τ.symm
    let f : (s : Bool) → Matrix (Fin (cond s a b)) (Fin (cond s a b)) K := fun s => match s with
      | false => Z.toBlocks₂₂
      | true => Z.toBlocks₁₁
    refine ⟨f, ?_⟩
    ext i j
    show (Matrix.fromBlocks Z.toBlocks₁₁ 0 0 Z.toBlocks₂₂) (τ i) (τ j) = M i j
    rcases hi : τ i with p | p <;> rcases hj : τ j with q | q
    · rw [Matrix.fromBlocks_apply₁₁]
      simp only [Z, Matrix.toBlocks₁₁, Matrix.of_apply, Matrix.submatrix_apply]
      rw [← hi, ← hj, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    · have := hM' i j (fun h => ((finSumFinEquiv_inl_lt_and_inr_not_lt hn j).2 q hj) (h.1 ((finSumFinEquiv_inl_lt_and_inr_not_lt hn i).1 p hi)))
      simp [this]
    · have := hM' i j (fun h => ((finSumFinEquiv_inl_lt_and_inr_not_lt hn i).2 p hi) (h.2 ((finSumFinEquiv_inl_lt_and_inr_not_lt hn j).1 q hj)))
      simp [this]
    · rw [Matrix.fromBlocks_apply₂₂]
      simp only [Z, Matrix.toBlocks₂₂, Matrix.of_apply, Matrix.submatrix_apply]
      rw [← hi, ← hj, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

private theorem exists_perm_matrix_conj_and_transpose_eq_submatrix {R : Type} [CommRing R] {n : ℕ} (π : Fin n ≃ Fin n) :
    ∃ T : GL (Fin n) R, ∀ M : Matrix (Fin n) (Fin n) R,
      (T : Matrix (Fin n) (Fin n) R) * M * ((T⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = M.submatrix π π ∧
      ((T⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)ᵀ * M * ((T⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)
        = M.submatrix π π := by
  have hAM : ∀ M : Matrix (Fin n) (Fin n) R, (1 : Matrix (Fin n) (Fin n) R).submatrix π id * M = M.submatrix π id := by
    intro M
    ext i j
    simp [Matrix.mul_apply, Matrix.one_apply]
  have hMB : ∀ M : Matrix (Fin n) (Fin n) R, M * (1 : Matrix (Fin n) (Fin n) R).submatrix id π = M.submatrix id π := by
    intro M
    ext i j
    simp [Matrix.mul_apply, Matrix.one_apply]
  have hAB : (1 : Matrix (Fin n) (Fin n) R).submatrix π id * (1 : Matrix (Fin n) (Fin n) R).submatrix id π = 1 := by
    rw [hAM]
    ext i j
    simp [Matrix.one_apply]
  have hBA : (1 : Matrix (Fin n) (Fin n) R).submatrix id π * (1 : Matrix (Fin n) (Fin n) R).submatrix π id = 1 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.one_apply, id]
    rw [Equiv.sum_comp π (fun k => (if i = k then (1 : R) else 0) * (if k = j then 1 else 0))]
    simp
  refine ⟨⟨(1 : Matrix (Fin n) (Fin n) R).submatrix π id, (1 : Matrix (Fin n) (Fin n) R).submatrix id π, hAB, hBA⟩, ?_⟩
  intro M
  have hinv : (((⟨(1 : Matrix (Fin n) (Fin n) R).submatrix π id, (1 : Matrix (Fin n) (Fin n) R).submatrix id π, hAB, hBA⟩ :
      GL (Fin n) R)⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = (1 : Matrix (Fin n) (Fin n) R).submatrix id π := rfl
  have htr : ((1 : Matrix (Fin n) (Fin n) R).submatrix id π)ᵀ = (1 : Matrix (Fin n) (Fin n) R).submatrix π id := by
    rw [Matrix.transpose_submatrix, Matrix.transpose_one]
  rw [hinv, htr]
  refine ⟨?_, ?_⟩
  · show (1 : Matrix (Fin n) (Fin n) R).submatrix π id * M * (1 : Matrix (Fin n) (Fin n) R).submatrix id π = _
    rw [hAM, hMB]
    rfl
  · rw [hAM, hMB]
    rfl

private theorem intertwiner_eq_zero_of_map_intertwiner_eq_zero {K L Γ : Type} [Field K] [Field L] (f : K →+* L) {m k : Type} [Fintype m]
    [Fintype k] [DecidableEq m] [DecidableEq k] (ρ₁ : Γ → Matrix m m K) (ρ₂ : Γ → Matrix k k K)
    (hL : ∀ V : Matrix m k L, (∀ g, (ρ₁ g).map f * V = V * (ρ₂ g).map f) → V = 0)
    (V : Matrix m k K) (hV : ∀ g, ρ₁ g * V = V * ρ₂ g) : V = 0 := by
  have h0 := hL (V.map f) (by
    intro g
    rw [← Matrix.map_mul, ← Matrix.map_mul, hV g])
  ext i j
  have := congrFun (congrFun h0 i) j
  simpa using this

private theorem reindex_transpose_mul_mul {R : Type} [CommRing R] {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (X Y W : Matrix (Fin n) (Fin n) R) :
    Matrix.reindex e e (Xᵀ * Y * W) = (Matrix.reindex e e X)ᵀ * Matrix.reindex e e Y * Matrix.reindex e e W := by
  simp only [Matrix.reindex_apply, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv]

private theorem rh_mul_pi_mul_z_eq_pi_mul_z_mul_s {K : Type} [CommRing K] {a b : ℕ} (A Ai P Pi Rh : Matrix (Fin a) (Fin a) K)
    (S : Matrix (Fin b) (Fin b) K) (Z : Matrix (Fin a) (Fin b) K) (hAAi : A * Ai = 1) (hPiP : Pi * P = 1)
    (hPPi : P * Pi = 1) (hf : Aᵀ * P * Rh = P) (hz : Aᵀ * Z * S = Z) : Rh * (Pi * Z) = (Pi * Z) * S := by
  have hT : Aiᵀ * Aᵀ = 1 := by rw [← Matrix.transpose_mul, hAAi, Matrix.transpose_one]
  have h1 : P * Rh = Aiᵀ * P := by
    calc P * Rh = (Aiᵀ * Aᵀ) * P * Rh := by rw [hT, Matrix.one_mul]
      _ = Aiᵀ * (Aᵀ * P * Rh) := by simp only [Matrix.mul_assoc]
      _ = Aiᵀ * P := by rw [hf]
  have h2 : Rh = Pi * (Aiᵀ * P) := by
    calc Rh = (Pi * P) * Rh := by rw [hPiP, Matrix.one_mul]
      _ = Pi * (P * Rh) := by rw [Matrix.mul_assoc]
      _ = Pi * (Aiᵀ * P) := by rw [h1]
  calc Rh * (Pi * Z) = Pi * Aiᵀ * (P * Pi) * Z := by rw [h2]; simp only [Matrix.mul_assoc]
    _ = Pi * Aiᵀ * Z := by rw [hPPi, Matrix.mul_one]
    _ = Pi * Aiᵀ * (Aᵀ * Z * S) := by rw [hz]
    _ = Pi * (Aiᵀ * Aᵀ) * Z * S := by simp only [Matrix.mul_assoc]
    _ = (Pi * Z) * S := by rw [hT, Matrix.mul_one]

private theorem eps_eq_one_of_mem_G' {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    (R : Type) [CommRing R] [Algebra O R] (g : F.G₀) (hg : g ∈ F.G') : F.eps O R g = 1 := by
  have h : F.ε (g : _) = 1 := by
    simpa only [GFrame.G', MonoidHom.mem_ker, MonoidHom.coe_comp, Subgroup.coe_subtype, Function.comp_apply] using hg
  ext
  simp only [GFrame.eps, MonoidHom.coe_comp, Subgroup.coe_subtype, Function.comp_apply, Units.coe_map,
    MonoidHom.coe_coe, RingHom.coe_comp]
  rw [h]
  simp

private theorem conj_mem_G'_and_conj_conj_eq_of_mem_G' {l : ℕ} [Fact l.Prime] (F : GFrame l) (g : F.G₀) (hg : g ∈ F.G') :
    F.conj g ∈ F.G' ∧ F.conj (F.conj g) = g := by
  have hc : F.c⁻¹ = F.c := inv_eq_of_mul_eq_one_left F.c_sq
  constructor
  · simp only [GFrame.G', MonoidHom.mem_ker, MonoidHom.coe_comp, Subgroup.coe_subtype, Function.comp_apply] at hg ⊢
    simp only [GFrame.conj, MonoidHom.coe_mk, OneHom.coe_mk]
    rw [map_mul, map_mul, hg, mul_one, map_inv, mul_inv_cancel]
  · apply Subtype.ext
    simp only [GFrame.conj, MonoidHom.coe_mk, OneHom.coe_mk]
    rw [hc]
    have h2 : F.c * (F.c * (g : _) * F.c) * F.c = (F.c * F.c) * (g : _) * (F.c * F.c) := by group
    rw [h2, F.c_sq, one_mul, mul_one]

private theorem mem_ev_self_self {R : Type} [CommRing R] (n : ℕ) (M : Matrix (Fin n) (Fin n) R) : M ∈ Ev R R n n := by
  simp only [Ev, blkMat, Submodule.mem_top, implies_true, Submodule.mem_bot, true_and, Submodule.mem_mk,
    AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_ofPred_eq]
  intro i j h
  exact absurd (iff_of_true i.2 j.2) h

theorem UpperTheory.V.Pa.Det.blockForm :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ} {r : Resid F O n} (x : Point r), 0 < n → x.TypeI ∨ x.TypeE → ∃ (a : ℕ) (Q : GL (Fin n) x.Fr), 1 ≤ a ∧ a ≤ n ∧ (x.TypeI → a = n) ∧ (∀ g, ((Q * x.ρF g * Q⁻¹ : GL (Fin n) x.Fr) : Matrix (Fin n) (Fin n) x.Fr) ∈ Ev x.Fr x.Fr n a) ∧ Submodule.span x.Fr ((fun g => ((Q * x.ρF g * Q⁻¹ : GL (Fin n) x.Fr) : Matrix (Fin n) (Fin n) x.Fr)) '' (F.G' : Set F.G₀)) = Ev x.Fr x.Fr n a ∧ ((Q⁻¹ : GL (Fin n) x.Fr) : Matrix (Fin n) (Fin n) x.Fr)ᵀ * (x.P : Matrix (Fin n) (Fin n) x.A).map (algebraMap x.A x.Fr) * ((Q⁻¹ : GL (Fin n) x.Fr) : Matrix (Fin n) (Fin n) x.Fr) ∈ Ev x.Fr x.Fr n a := by
  intro l _ F O _ _ _ n r x hn hx
  have hρF : ∀ g, ((x.ρF g : GL (Fin n) x.Fr) : Matrix (Fin n) (Fin n) x.Fr) =
      ((x.ρ g : GL (Fin n) x.A) : Matrix (Fin n) (Fin n) x.A).map (algebraMap x.A x.Fr) := by
    intro g
    simp only [Point.ρF, MonoidHom.coe_comp, Function.comp_apply, GeneralLinearGroup.val_map_apply]
  have hpush : ∀ {k : ℕ} (ρ : F.G₀ →* GL (Fin k) x.Fr) (g : F.G₀),
      mat (pushRep (algebraMap x.Fr x.Fb) ρ) g = (mat ρ g).map (algebraMap x.Fr x.Fb) := by
    intro k ρ g
    simp only [mat, pushRep, MonoidHom.coe_comp, Function.comp_apply, Units.coeHom_apply,
      GeneralLinearGroup.val_map_apply]
  have hspanFb : ∀ {k : ℕ} (ρ : F.G₀ →* GL (Fin k) x.Fr),
      UpperTheory.V.U3.MatIrr F.G' ⇑(mat (pushRep (algebraMap x.Fr x.Fb) ρ)) →
      Submodule.span x.Fb (Set.range ((mat (pushRep (algebraMap x.Fr x.Fb) ρ)).comp F.G'.subtype)) = ⊤ := by
    intro k ρ hirr
    refine ((UpperTheory.V.AlgebraTools.irred_iff_span (RingHom.id x.Fb) ((mat (pushRep (algebraMap x.Fr x.Fb) ρ)).comp F.G'.subtype)).1.1) ?_
    intro N hN
    apply hirr N
    intro g hg v hv
    exact hN ⟨g, hg⟩ v hv
  by_cases hI : x.TypeI
  · refine ⟨n, 1, hn, le_refl n, fun _ => rfl, fun g => mem_ev_self_self n _, ?_, mem_ev_self_self n _⟩
    simp only [one_mul, inv_one, mul_one]
    rw [Set.image_eq_range]
    have hmem : ∀ i : (F.G' : Set F.G₀), ((x.ρF i : GL (Fin n) x.Fr) : Matrix (Fin n) (Fin n) x.Fr) ∈ Ev x.Fr x.Fr n n :=
      fun i => mem_ev_self_self n _
    rw [Det.spanDesc (algebraMap x.Fr x.Fb) _ hmem]
    have h1 := hspanFb x.ρF hI
    have h2 : (Set.range fun i : (F.G' : Set F.G₀) =>
        ((x.ρF i : GL (Fin n) x.Fr) : Matrix (Fin n) (Fin n) x.Fr).map (algebraMap x.Fr x.Fb)) =
        Set.range ((mat (pushRep (algebraMap x.Fr x.Fb) x.ρF)).comp F.G'.subtype) := by
      ext M
      simp only [Set.mem_range, MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype, hpush]
      rfl
    rw [h2, h1]
    exact (eq_top_iff.2 (fun M _ => mem_ev_self_self n M)).symm

  · have hE : x.TypeE := hx.resolve_left hI
    unfold Point.TypeE at hE
    obtain ⟨a, b, ha, hb, e, Q, r₁, r₂, hQ, ⟨P₁, hP₁⟩, ⟨P₂, hP₂⟩, i₁, i₂, hint⟩ := hE
    have hnab : n = a + b := by simpa using Fintype.card_congr e
    obtain ⟨T, hT⟩ := exists_perm_matrix_conj_and_transpose_eq_submatrix (R := x.Fr) (((finCongr hnab).trans finSumFinEquiv.symm).trans e.symm)
    have hsub : ∀ X : Matrix (Fin n) (Fin n) x.Fr,
        X.submatrix (((finCongr hnab).trans finSumFinEquiv.symm).trans e.symm)
          (((finCongr hnab).trans finSumFinEquiv.symm).trans e.symm)
          = (Matrix.reindex e e X).submatrix ((finCongr hnab).trans finSumFinEquiv.symm)
            ((finCongr hnab).trans finSumFinEquiv.symm) := by
      intro X
      rw [Matrix.reindex_apply, Matrix.submatrix_submatrix]
      rfl
    have hN : ∀ g, (((T * Q) * x.ρF g * (T * Q)⁻¹ : GL (Fin n) x.Fr) : Matrix (Fin n) (Fin n) x.Fr) =
        (Matrix.fromBlocks (mat r₁ g) 0 0 (mat r₂ g)).submatrix ((finCongr hnab).trans finSumFinEquiv.symm)
          ((finCongr hnab).trans finSumFinEquiv.symm) := by
      intro g
      have h1 : (T * Q) * x.ρF g * (T * Q)⁻¹ = T * (Q * x.ρF g * Q⁻¹) * T⁻¹ := by group
      rw [h1, Units.val_mul, Units.val_mul, (hT _).1, hsub, hQ g]
    have hmemAll : ∀ g, (((T * Q) * x.ρF g * (T * Q)⁻¹ : GL (Fin n) x.Fr) : Matrix (Fin n) (Fin n) x.Fr)
        ∈ Ev x.Fr x.Fr n a := by
      intro g
      rw [hN]
      apply submatrix_mem_ev_of_offDiag_blocks_zero hnab
      · intro i j
        simp
      · intro i j
        simp
    let ρ₁' := (mat (pushRep (algebraMap x.Fr x.Fb) r₁)).comp F.G'.subtype
    let ρ₂' := (mat (pushRep (algebraMap x.Fr x.Fb) r₂)).comp F.G'.subtype
    have s₁ := hspanFb r₁ i₁
    have s₂ := hspanFb r₂ i₂
    have i₂₁' : ∀ V : Matrix (Fin b) (Fin a) x.Fb, (∀ g, ρ₂' g * V = V * ρ₁' g) → V = 0 :=
      fun V hV => hint V (fun g hg => (hV ⟨g, hg⟩).symm)
    have i₁₂' : ∀ V : Matrix (Fin a) (Fin b) x.Fb, (∀ g, ρ₁' g * V = V * ρ₂' g) → V = 0 :=
      fun V hV => intertwiner_eq_zero_of_span_eq_univ_of_reverse_zero ha ⇑ρ₁' ⇑ρ₂' s₁ s₂ (fun M hM => hint M (fun g hg => hM ⟨g, hg⟩)) V hV
    refine ⟨a, T * Q, ha, by omega, fun h => absurd h hI, hmemAll, ?_, ?_⟩
    · rw [Set.image_eq_range]
      have hmem : ∀ i : (F.G' : Set F.G₀), (((T * Q) * x.ρF i * (T * Q)⁻¹ : GL (Fin n) x.Fr) :
          Matrix (Fin n) (Fin n) x.Fr) ∈ Ev x.Fr x.Fr n a := fun i => hmemAll i
      rw [Det.spanDesc (algebraMap x.Fr x.Fb) _ hmem]
      have h2 : (Set.range fun i : (F.G' : Set F.G₀) => ((((T * Q) * x.ρF i * (T * Q)⁻¹ : GL (Fin n) x.Fr) :
          Matrix (Fin n) (Fin n) x.Fr)).map (algebraMap x.Fr x.Fb)) =
          Set.range fun g : F.G' => (Matrix.fromBlocks (ρ₁' g) 0 0 (ρ₂' g)).submatrix
            ((finCongr hnab).trans finSumFinEquiv.symm) ((finCongr hnab).trans finSumFinEquiv.symm) := by
        congr 1
        funext g
        rw [hN, ← Matrix.submatrix_map, Matrix.fromBlocks_map]
        simp only [ρ₁', ρ₂', MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype, hpush,
          Matrix.map_zero _ (map_zero (algebraMap x.Fr x.Fb))]
      rw [h2]
      exact span_range_fromBlocks_submatrix_eq_ev hnab ha hb ρ₁' ρ₂' s₁ s₂ i₁₂' i₂₁'
    · have hρcoe : ∀ g, mat x.ρF g = ((x.ρ g : GL (Fin n) x.A) : Matrix (Fin n) (Fin n) x.A).map (algebraMap x.A x.Fr) :=
        fun g => hρF g
      have hform : ∀ g ∈ F.G', (mat x.ρF g)ᵀ * (x.P : Matrix (Fin n) (Fin n) x.A).map (algebraMap x.A x.Fr) *
          mat x.ρF (F.conj g) = (x.P : Matrix (Fin n) (Fin n) x.A).map (algebraMap x.A x.Fr) := by
        intro g hg
        have hf := x.form
        unfold GFrame.IsForm at hf
        have h0 := hf g
        rw [eps_eq_one_of_mem_G' F O _ g hg, _root_.one_zpow, Units.val_one, one_smul] at h0
        rw [hρcoe, hρcoe, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul]
        exact congrArg (fun M => M.map (algebraMap x.A x.Fr)) h0
      set Pm := (x.P : Matrix (Fin n) (Fin n) x.A).map (algebraMap x.A x.Fr) with hPm
      set W := ((Q⁻¹ : GL (Fin n) x.Fr) : Matrix (Fin n) (Fin n) x.Fr)ᵀ * Pm *
        ((Q⁻¹ : GL (Fin n) x.Fr) : Matrix (Fin n) (Fin n) x.Fr) with hW
      have hqq : ((Q⁻¹ : GL (Fin n) x.Fr) : Matrix (Fin n) (Fin n) x.Fr) * (Q : Matrix (Fin n) (Fin n) x.Fr) = 1 := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      have hqqT : (Q : Matrix (Fin n) (Fin n) x.Fr)ᵀ * ((Q⁻¹ : GL (Fin n) x.Fr) : Matrix (Fin n) (Fin n) x.Fr)ᵀ = 1 := by
        rw [← Matrix.transpose_mul, hqq, Matrix.transpose_one]
      have hWeq : ∀ g ∈ F.G', ((Q * x.ρF g * Q⁻¹ : GL (Fin n) x.Fr) : Matrix (Fin n) (Fin n) x.Fr)ᵀ * W *
          ((Q * x.ρF (F.conj g) * Q⁻¹ : GL (Fin n) x.Fr) : Matrix (Fin n) (Fin n) x.Fr) = W := by
        intro g hg
        have hf := hform g hg
        simp only [Units.val_mul]
        calc ((Q : Matrix (Fin n) (Fin n) x.Fr) * (x.ρF g : Matrix (Fin n) (Fin n) x.Fr) *
              ((Q⁻¹ : GL (Fin n) x.Fr) : Matrix (Fin n) (Fin n) x.Fr))ᵀ * W *
              ((Q : Matrix (Fin n) (Fin n) x.Fr) * (x.ρF (F.conj g) : Matrix (Fin n) (Fin n) x.Fr) *
              ((Q⁻¹ : GL (Fin n) x.Fr) : Matrix (Fin n) (Fin n) x.Fr))
            = ((Q⁻¹ : GL (Fin n) x.Fr) : Matrix (Fin n) (Fin n) x.Fr)ᵀ * (x.ρF g : Matrix (Fin n) (Fin n) x.Fr)ᵀ *
              ((Q : Matrix (Fin n) (Fin n) x.Fr)ᵀ * ((Q⁻¹ : GL (Fin n) x.Fr) : Matrix (Fin n) (Fin n) x.Fr)ᵀ) * Pm *
              (((Q⁻¹ : GL (Fin n) x.Fr) : Matrix (Fin n) (Fin n) x.Fr) * (Q : Matrix (Fin n) (Fin n) x.Fr)) *
              (x.ρF (F.conj g) : Matrix (Fin n) (Fin n) x.Fr) * ((Q⁻¹ : GL (Fin n) x.Fr) : Matrix (Fin n) (Fin n) x.Fr) := by
              simp only [hW, Matrix.transpose_mul, Matrix.mul_assoc]
          _ = ((Q⁻¹ : GL (Fin n) x.Fr) : Matrix (Fin n) (Fin n) x.Fr)ᵀ *
              ((mat x.ρF g)ᵀ * Pm * mat x.ρF (F.conj g)) * ((Q⁻¹ : GL (Fin n) x.Fr) : Matrix (Fin n) (Fin n) x.Fr) := by
              rw [hqqT, hqq]
              simp only [Matrix.mul_one, Matrix.mul_assoc]
              rfl
          _ = W := by rw [hf]
      set Z := Matrix.reindex e e W with hZ
      have hZeq : ∀ g ∈ F.G', (mat r₁ g)ᵀ * Z.toBlocks₁₂ * mat r₂ (F.conj g) = Z.toBlocks₁₂ ∧
          (mat r₂ g)ᵀ * Z.toBlocks₂₁ * mat r₁ (F.conj g) = Z.toBlocks₂₁ := by
        intro g hg
        have h0 := congrArg (Matrix.reindex e e) (hWeq g hg)
        rw [reindex_transpose_mul_mul, hQ g, hQ (F.conj g)] at h0
        rw [← hZ] at h0
        rw [← Matrix.fromBlocks_toBlocks Z] at h0
        simp only [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj,
          Matrix.transpose_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add] at h0
        exact ⟨h0.2.1, h0.2.2.1⟩
      have hmatinv : ∀ {k : ℕ} (ρ : F.G₀ →* GL (Fin k) x.Fr) (g : F.G₀), mat ρ g * mat ρ g⁻¹ = 1 := by
        intro k ρ g
        rw [← map_mul, mul_inv_cancel, map_one]
      have hfm : ∀ {k : ℕ} (ρ : F.G₀ →* GL (Fin k) x.Fr) (Pk : GL (Fin k) x.Fr), F.IsForm O n ρ Pk → ∀ g ∈ F.G',
          (mat ρ g)ᵀ * (Pk : Matrix (Fin k) (Fin k) x.Fr) * mat ρ (F.conj g) = Pk := by
        intro k ρ Pk h g hg
        unfold GFrame.IsForm at h
        have h0 := h g
        rw [eps_eq_one_of_mem_G' F O _ g hg, _root_.one_zpow, Units.val_one, one_smul] at h0
        exact h0
      have hPP : ∀ {k : ℕ} (Pk : GL (Fin k) x.Fr),
          ((Pk⁻¹ : GL (Fin k) x.Fr) : Matrix (Fin k) (Fin k) x.Fr) * Pk = 1 ∧
          (Pk : Matrix (Fin k) (Fin k) x.Fr) * ((Pk⁻¹ : GL (Fin k) x.Fr) : Matrix (Fin k) (Fin k) x.Fr) = 1 := by
        intro k Pk
        constructor
        · rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
        · rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      have h12 : Z.toBlocks₁₂ = 0 := by
        have hV : ∀ h : F.G', mat r₁ h * (((P₁⁻¹ : GL (Fin a) x.Fr) : Matrix (Fin a) (Fin a) x.Fr) * Z.toBlocks₁₂) =
            (((P₁⁻¹ : GL (Fin a) x.Fr) : Matrix (Fin a) (Fin a) x.Fr) * Z.toBlocks₁₂) * mat r₂ h := by
          intro h
          obtain ⟨hc, hcc⟩ := conj_mem_G'_and_conj_conj_eq_of_mem_G' F h h.2
          have h3 := rh_mul_pi_mul_z_eq_pi_mul_z_mul_s (mat r₁ (F.conj h)) (mat r₁ (F.conj h)⁻¹) (P₁ : Matrix (Fin a) (Fin a) x.Fr) _
            (mat r₁ (F.conj (F.conj h))) (mat r₂ (F.conj (F.conj h))) Z.toBlocks₁₂ (hmatinv r₁ _) (hPP P₁).1
            (hPP P₁).2 (hfm r₁ P₁ hP₁ _ hc) (hZeq _ hc).1
          rw [hcc] at h3
          exact h3
        have h0 := intertwiner_eq_zero_of_map_intertwiner_eq_zero (algebraMap x.Fr x.Fb) (fun h : F.G' => mat r₁ h) (fun h : F.G' => mat r₂ h)
          (fun V hV' => i₁₂' V (fun g => by simpa [ρ₁', ρ₂', hpush] using hV' g)) _ hV
        calc Z.toBlocks₁₂ = (P₁ : Matrix (Fin a) (Fin a) x.Fr) *
              (((P₁⁻¹ : GL (Fin a) x.Fr) : Matrix (Fin a) (Fin a) x.Fr) * Z.toBlocks₁₂) := by
              rw [← Matrix.mul_assoc, (hPP P₁).2, Matrix.one_mul]
          _ = 0 := by rw [h0, Matrix.mul_zero]
      have h21 : Z.toBlocks₂₁ = 0 := by
        have hV : ∀ h : F.G', mat r₂ h * (((P₂⁻¹ : GL (Fin b) x.Fr) : Matrix (Fin b) (Fin b) x.Fr) * Z.toBlocks₂₁) =
            (((P₂⁻¹ : GL (Fin b) x.Fr) : Matrix (Fin b) (Fin b) x.Fr) * Z.toBlocks₂₁) * mat r₁ h := by
          intro h
          obtain ⟨hc, hcc⟩ := conj_mem_G'_and_conj_conj_eq_of_mem_G' F h h.2
          have h3 := rh_mul_pi_mul_z_eq_pi_mul_z_mul_s (mat r₂ (F.conj h)) (mat r₂ (F.conj h)⁻¹) (P₂ : Matrix (Fin b) (Fin b) x.Fr) _
            (mat r₂ (F.conj (F.conj h))) (mat r₁ (F.conj (F.conj h))) Z.toBlocks₂₁ (hmatinv r₂ _) (hPP P₂).1
            (hPP P₂).2 (hfm r₂ P₂ hP₂ _ hc) (hZeq _ hc).2
          rw [hcc] at h3
          exact h3
        have h0 := intertwiner_eq_zero_of_map_intertwiner_eq_zero (algebraMap x.Fr x.Fb) (fun h : F.G' => mat r₂ h) (fun h : F.G' => mat r₁ h)
          (fun V hV' => i₂₁' V (fun g => by simpa [ρ₁', ρ₂', hpush] using hV' g)) _ hV
        calc Z.toBlocks₂₁ = (P₂ : Matrix (Fin b) (Fin b) x.Fr) *
              (((P₂⁻¹ : GL (Fin b) x.Fr) : Matrix (Fin b) (Fin b) x.Fr) * Z.toBlocks₂₁) := by
              rw [← Matrix.mul_assoc, (hPP P₂).2, Matrix.one_mul]
          _ = 0 := by rw [h0, Matrix.mul_zero]
      have hgoal : (((T * Q)⁻¹ : GL (Fin n) x.Fr) : Matrix (Fin n) (Fin n) x.Fr)ᵀ * Pm *
          (((T * Q)⁻¹ : GL (Fin n) x.Fr) : Matrix (Fin n) (Fin n) x.Fr) =
          W.submatrix (((finCongr hnab).trans finSumFinEquiv.symm).trans e.symm)
            (((finCongr hnab).trans finSumFinEquiv.symm).trans e.symm) := by
        rw [_root_.mul_inv_rev, Units.val_mul, Matrix.transpose_mul, ← (hT W).2, hW]
        simp only [Matrix.mul_assoc]
      rw [hgoal, hsub]
      apply submatrix_mem_ev_of_offDiag_blocks_zero hnab
      · intro i j
        have := congrFun (congrFun h12 i) j
        exact this
      · intro i j
        have := congrFun (congrFun h21 i) j
        exact this
