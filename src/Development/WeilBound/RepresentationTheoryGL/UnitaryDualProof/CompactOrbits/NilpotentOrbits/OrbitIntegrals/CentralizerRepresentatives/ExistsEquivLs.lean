module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.CentralizerRepresentatives.IsChain

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.CentralizerRepresentatives.ExistsEquivLs
noncomputable section

open Matrix

namespace PositivityTheory.RgUd.T.Nil.Orb.BReps

variable {k : Type} [Field k] {n : ℕ}

variable {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {M : Type} [Fintype M] {L : M → Type}
    [∀ m, Fintype (L m)] {R : Z → (m : M) → L m → L m → k} {o : (m : M) → L m → k}

theorem Frame.card_index {N : Matrix (Fin n) (Fin n) k} {v : Fin n → k} (F : Frame Z M L R o N v) :
    Fintype.card (Σ m, L m × (Σ a : F.ι m, Fin (F.l m a))) = n := by
  rw [← Module.finrank_eq_card_basis F.β, Module.finrank_fin_fun]

theorem Frame.l_le [∀ m, Nonempty (L m)] {N : Matrix (Fin n) (Fin n) k} {v : Fin n → k}
    (F : Frame Z M L R o N v) (m : M) (a : F.ι m) : F.l m a ≤ n := by
  obtain ⟨p⟩ := (inferInstance : Nonempty (L m))
  have hinj : Function.Injective (fun i : Fin (F.l m a) =>
      (⟨m, (p, ⟨a, i⟩)⟩ : Σ m, L m × (Σ a : F.ι m, Fin (F.l m a)))) := by
    intro i j h
    have h1 := sigma_mk_injective h
    have h2 := sigma_mk_injective (Prod.ext_iff.mp h1).2
    exact h2
  have := Fintype.card_le_of_injective _ hinj
  rw [Fintype.card_fin, F.card_index] at this
  exact this

theorem Frame.card_le [∀ m, Nonempty (L m)] {N : Matrix (Fin n) (Fin n) k} {v : Fin n → k}
    (F : Frame Z M L R o N v) (m : M) : Nat.card (F.ι m) ≤ n := by
  obtain ⟨p⟩ := (inferInstance : Nonempty (L m))
  have hinj : Function.Injective (fun a : F.ι m =>
      (⟨m, (p, ⟨a, ⟨0, F.hl m a⟩⟩)⟩ : Σ m, L m × (Σ a : F.ι m, Fin (F.l m a)))) := by
    intro a b h
    have h1 := sigma_mk_injective h
    have h2 := (Prod.ext_iff.mp h1).2
    exact congrArg Sigma.fst h2
  have := Fintype.card_le_of_injective _ hinj
  rw [F.card_index] at this
  rw [Nat.card_eq_fintype_card]
  exact this

theorem exists_equiv_ls [∀ m, Nonempty (L m)] {N₁ N₂ : Matrix (Fin n) (Fin n) k} {v₁ v₂ : Fin n → k}
    (F₁ : Frame Z M L R o N₁ v₁) (F₂ : Frame Z M L R o N₂ v₂)
    (h : ∀ m (ℓ σ : ℕ), ℓ ≤ n → σ ≤ n → Nat.card {a : F₁.ι m // F₁.l m a = ℓ ∧ F₁.s m a = σ} =
      Nat.card {a : F₂.ι m // F₂.l m a = ℓ ∧ F₂.s m a = σ}) (m : M) :
    ∃ e : F₁.ι m ≃ F₂.ι m, ∀ a, F₂.l m (e a) = F₁.l m a ∧ F₂.s m (e a) = F₁.s m a := by
  have hf : ∀ c : ℕ × ℕ, Nonempty ({a : F₁.ι m // (F₁.l m a, F₁.s m a) = c} ≃
      {b : F₂.ι m // (F₂.l m b, F₂.s m b) = c}) := by
    intro c
    rw [← Finite.card_eq]
    by_cases hc : c.1 ≤ n ∧ c.2 ≤ n
    · have e1 : {a : F₁.ι m // (F₁.l m a, F₁.s m a) = c} ≃ {a : F₁.ι m // F₁.l m a = c.1 ∧ F₁.s m a = c.2} :=
        Equiv.subtypeEquivRight (fun a => Prod.ext_iff)
      have e2 : {a : F₂.ι m // (F₂.l m a, F₂.s m a) = c} ≃ {a : F₂.ι m // F₂.l m a = c.1 ∧ F₂.s m a = c.2} :=
        Equiv.subtypeEquivRight (fun a => Prod.ext_iff)
      rw [Nat.card_congr e1, Nat.card_congr e2]
      exact h m c.1 c.2 hc.1 hc.2
    · have hE1 : IsEmpty {a : F₁.ι m // (F₁.l m a, F₁.s m a) = c} := by
        refine ⟨fun ⟨a, ha⟩ => hc ?_⟩
        rw [← ha]
        exact ⟨F₁.l_le m a, (F₁.hs m a).trans (F₁.l_le m a)⟩
      have hE2 : IsEmpty {a : F₂.ι m // (F₂.l m a, F₂.s m a) = c} := by
        refine ⟨fun ⟨a, ha⟩ => hc ?_⟩
        rw [← ha]
        exact ⟨F₂.l_le m a, (F₂.hs m a).trans (F₂.l_le m a)⟩
      rw [Nat.card_of_isEmpty, Nat.card_of_isEmpty]
  let e := fun c => (hf c).some
  refine ⟨Equiv.ofFiberEquiv (fun c => e c), fun a => ?_⟩
  have := Equiv.ofFiberEquiv_map (f := fun a => (F₁.l m a, F₁.s m a)) (g := fun b => (F₂.l m b, F₂.s m b))
    (fun c => e c) a
  exact Prod.ext_iff.mp this

theorem conj_of_frames [∀ m, Nonempty (L m)] {N₁ N₂ : Matrix (Fin n) (Fin n) k} {v₁ v₂ : Fin n → k}
    (F₁ : Frame Z M L R o N₁ v₁) (F₂ : Frame Z M L R o N₂ v₂)
    (h : ∀ m (ℓ σ : ℕ), ℓ ≤ n → σ ≤ n → Nat.card {a : F₁.ι m // F₁.l m a = ℓ ∧ F₁.s m a = σ} =
      Nat.card {a : F₂.ι m // F₂.l m a = ℓ ∧ F₂.s m a = σ}) :
    ∃ g : GL (Fin n) k, (∀ a ∈ Z, a * g.val = g.val * a) ∧ g.val * N₁ = N₂ * g.val ∧ g.val *ᵥ v₁ = v₂ := by
  choose σ hσ using exists_equiv_ls F₁ F₂ h
  let ψ : ∀ m, (Σ a : F₁.ι m, Fin (F₁.l m a)) ≃ (Σ b : F₂.ι m, Fin (F₂.l m b)) := fun m =>
    Equiv.sigmaCongr (σ m) (fun a => finCongr (hσ m a).1.symm)
  have hψ : ∀ m (a : F₁.ι m) (i : Fin (F₁.l m a)), ψ m ⟨a, i⟩ = ⟨σ m a, Fin.cast (hσ m a).1.symm i⟩ := by
    intro m a i
    rfl
  let Φ : (Σ m, L m × (Σ a : F₁.ι m, Fin (F₁.l m a))) ≃ (Σ m, L m × (Σ b : F₂.ι m, Fin (F₂.l m b))) :=
    Equiv.sigmaCongrRight (fun m => Equiv.prodCongr (Equiv.refl _) (ψ m))
  have hΦ : ∀ m (p : L m) j, Φ ⟨m, (p, j)⟩ = ⟨m, (p, ψ m j)⟩ := fun m p j => rfl
  let g : (Fin n → k) ≃ₗ[k] (Fin n → k) := F₁.β.equiv F₂.β Φ
  have hg : ∀ j, g (F₁.β j) = F₂.β (Φ j) := fun j => Module.Basis.equiv_apply _ _ _ _
  let G : GL (Fin n) k := ⟨LinearMap.toMatrix' (g : (Fin n → k) →ₗ[k] (Fin n → k)),
    LinearMap.toMatrix' (g.symm : (Fin n → k) →ₗ[k] (Fin n → k)),
    by rw [← LinearMap.toMatrix'_comp]; convert LinearMap.toMatrix'_id; ext x; simp,
    by rw [← LinearMap.toMatrix'_comp]; convert LinearMap.toMatrix'_id; ext x; simp⟩
  have hGv : ∀ x, G.val *ᵥ x = g x := fun x => LinearMap.toMatrix'_mulVec _ x

  have hext : ∀ X Y : Matrix (Fin n) (Fin n) k, (∀ j, X *ᵥ F₁.β j = Y *ᵥ F₁.β j) → X = Y := by
    intro X Y hXY
    apply Matrix.toLin'.injective
    apply F₁.β.ext
    intro j
    simp only [Matrix.toLin'_apply]
    exact hXY j
  refine ⟨G, ?_, ?_, ?_⟩
  · intro a ha
    apply hext
    rintro ⟨m, p, j⟩
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hGv, hg, hΦ]
    have h1 := F₂.hZ ⟨a, ha⟩ m p (ψ m j)
    have h2 := F₁.hZ ⟨a, ha⟩ m p j
    simp only at h1 h2
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h1, h2, hGv, map_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [map_smul, hg, hΦ]
  · apply hext
    rintro ⟨m, p, a, i⟩
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, F₁.hN]
    simp only [hGv]
    rw [hg, hΦ, hψ, F₂.hN]
    simp only [Fin.val_cast]
    by_cases hi : (i : ℕ) + 1 < F₁.l m a
    · have hi2 : (i : ℕ) + 1 < F₂.l m (σ m a) := by rw [(hσ m a).1]; exact hi
      rw [dite_eq_left hi, dite_eq_left hi2, hg, hΦ, hψ]
      rfl
    · have hi2 : ¬ (i : ℕ) + 1 < F₂.l m (σ m a) := by rw [(hσ m a).1]; exact hi
      rw [dite_eq_right hi, dite_eq_right hi2, map_zero]
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [hGv, F₁.hv, F₂.hv, map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, ← Equiv.sum_comp (σ m)]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases ha : F₁.s m a < F₁.l m a
    · have ha2 : F₂.s m (σ m a) < F₂.l m (σ m a) := by rw [(hσ m a).1, (hσ m a).2]; exact ha
      rw [dite_eq_left ha, dite_eq_left ha2, map_smul, hg, hΦ, hψ]
      have hc : (Fin.cast (hσ m a).1.symm ⟨F₁.s m a, ha⟩ : Fin (F₂.l m (σ m a))) = ⟨F₂.s m (σ m a), ha2⟩ :=
        Fin.ext (by simp [(hσ m a).2])
      rw [hc]
    · have ha2 : ¬ F₂.s m (σ m a) < F₂.l m (σ m a) := by rw [(hσ m a).1, (hσ m a).2]; exact ha
      rw [dite_eq_right ha, dite_eq_right ha2, map_zero]

end PositivityTheory.RgUd.T.Nil.Orb.BReps
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.CentralizerRepresentatives.GradeColMatMulVec
noncomputable section

open Matrix Submodule

namespace PositivityTheory.RgUd.T.Nil.Orb.BReps

variable {k : Type} [Field k] {n : ℕ}

def gradeColMat (b : Module.Basis (Fin n) k (Fin n → k)) : Matrix (Fin n) (Fin n) k :=
  (Pi.basisFun k (Fin n)).toMatrix b

def gradeRowMat (b : Module.Basis (Fin n) k (Fin n → k)) : Matrix (Fin n) (Fin n) k :=
  b.toMatrix (Pi.basisFun k (Fin n))

def gradeBasisGL (b : Module.Basis (Fin n) k (Fin n → k)) : GL (Fin n) k :=
  ⟨gradeColMat b, gradeRowMat b, Module.Basis.toMatrix_mul_toMatrix_flip _ _, Module.Basis.toMatrix_mul_toMatrix_flip _ _⟩

theorem gradeColMat_mulVec (b : Module.Basis (Fin n) k (Fin n → k)) (u : Fin n → k) :
    gradeColMat b *ᵥ u = ∑ i, u i • b i := by
  ext r
  simp [gradeColMat, Matrix.mulVec, dotProduct, Module.Basis.toMatrix_apply, Finset.sum_apply, mul_comm]

theorem grade_mat_ext {ι : Type} (b : Module.Basis ι k (Fin n → k)) (X Y : Matrix (Fin n) (Fin n) k)
    (h : ∀ i, X *ᵥ b i = Y *ᵥ b i) : X = Y := by
  apply Matrix.toLin'.injective
  exact b.ext fun i => by simpa [Matrix.toLin'_apply] using h i

theorem grade_eig {ι : Type} (b : Module.Basis ι k (Fin n → k)) (g : Matrix (Fin n) (Fin n) k) (d : ι → k)
    (hg : ∀ i, g *ᵥ b i = d i • b i) (S : Set ι) (c : k) (hS : ∀ i ∈ S, d i = c) (y : Fin n → k)
    (hy : y ∈ span k (b '' S)) : g *ᵥ y = c • y := by
  let f : (Fin n → k) →ₗ[k] (Fin n → k) := Matrix.toLin' g - c • LinearMap.id
  have hle : span k (b '' S) ≤ LinearMap.ker f := by
    rw [span_le]
    rintro _ ⟨i, hi, rfl⟩
    simp [f, Matrix.toLin'_apply, hg, hS i hi]
  have := hle hy
  simp only [LinearMap.mem_ker, f, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    Matrix.toLin'_apply] at this
  exact sub_eq_zero.mp this

theorem grade_fin (b : Module.Basis (Fin n) k (Fin n → k)) (w : Fin n → ℤ)
    (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (N : Matrix (Fin n) (Fin n) k) (v : Fin n → k)
    (hZ : ∀ z ∈ Z, ∀ j, z *ᵥ b j ∈ span k (b '' {j' | w j' = w j}))
    (hN : ∀ j, N *ᵥ b j ∈ span k (b '' {j' | w j' = w j + 1}))
    (hv : v ∈ span k (b '' {j | w j = 0}))
    (hA : ∀ a : Matrix (Fin n) (Fin n) k, (∀ z ∈ Z, z * a = a * z) → a * N = N * a →
      ∀ j, w j < 0 → b.repr (a *ᵥ v) j = 0) :
    (∀ t : kˣ,
        let g : Matrix (Fin n) (Fin n) k :=
          (gradeBasisGL b).val * diagonal (fun i => ((t ^ w i : kˣ) : k)) * (gradeBasisGL b)⁻¹.val
        (∀ a ∈ Z, a * g = g * a) ∧ g * N = (t : k) • (N * g) ∧ g *ᵥ v = v) ∧
      ∀ a : Matrix (Fin n) (Fin n) k, (∀ z ∈ Z, z * a = a * z) → a * N = N * a →
        ∃ u : Fin n → k, a *ᵥ v = (gradeBasisGL b).val *ᵥ u ∧ ∀ i, w i < 0 → u i = 0 := by
  classical
  refine ⟨fun t => ?_, fun a ha haN => ?_⟩
  · intro g
    have hrow : ∀ j, gradeRowMat b *ᵥ b j = Pi.single j 1 := by
      intro j
      have h1 : gradeColMat b *ᵥ Pi.single j 1 = b j := by
        rw [gradeColMat_mulVec]
        simp [Pi.single_apply]
      rw [← h1, Matrix.mulVec_mulVec]
      show (b.toMatrix (Pi.basisFun k (Fin n)) * (Pi.basisFun k (Fin n)).toMatrix b) *ᵥ _ = _
      rw [Module.Basis.toMatrix_mul_toMatrix_flip, Matrix.one_mulVec]
    have hgdef : g = gradeColMat b * diagonal (fun i => ((t ^ w i : kˣ) : k)) * gradeRowMat b := rfl
    clear_value g
    have hg : ∀ j, g *ᵥ b j = ((t ^ w j : kˣ) : k) • b j := by
      intro j
      rw [hgdef, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hrow, gradeColMat_mulVec]
      simp [Matrix.mulVec_diagonal, Pi.single_apply]
    refine ⟨fun a ha => ?_, ?_, ?_⟩
    · apply grade_mat_ext b
      intro j
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hg, Matrix.mulVec_smul]
      rw [grade_eig b g (fun i => ((t ^ w i : kˣ) : k)) hg {j' | w j' = w j} _ (fun i hi => by rw [hi]) _ (hZ a ha j)]
    · apply grade_mat_ext b
      intro j
      rw [← Matrix.mulVec_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, hg, Matrix.mulVec_smul,
        grade_eig b g (fun i => ((t ^ w i : kˣ) : k)) hg {j' | w j' = w j + 1} (((t ^ (w j + 1) : kˣ) : k))
          (fun i hi => by rw [hi]) _ (hN j), smul_smul, _root_.zpow_add_one, Units.val_mul, Units.val_zpow_eq_zpow_val,
        mul_comm]
    · rw [grade_eig b g (fun i => ((t ^ w i : kˣ) : k)) hg {j | w j = 0} 1 (fun i hi => by rw [hi]; simp) v hv, one_smul]
  · refine ⟨⇑(b.repr (a *ᵥ v)), ?_, fun i hi => hA a ha haN i hi⟩
    simp only [gradeBasisGL]
    rw [gradeColMat_mulVec, b.sum_repr]

theorem grade_of_basis {κ : Type} [Fintype κ] (β : Module.Basis κ k (Fin n → k)) (ω : κ → ℤ)
    (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (N : Matrix (Fin n) (Fin n) k) (v : Fin n → k)
    (hZ : ∀ z ∈ Z, ∀ j, z *ᵥ β j ∈ span k (β '' {j' | ω j' = ω j}))
    (hN : ∀ j, N *ᵥ β j ∈ span k (β '' {j' | ω j' = ω j + 1}))
    (hv : v ∈ span k (β '' {j | ω j = 0}))
    (hA : ∀ a : Matrix (Fin n) (Fin n) k, (∀ z ∈ Z, z * a = a * z) → a * N = N * a →
      ∀ j, ω j < 0 → β.repr (a *ᵥ v) j = 0) :
    ∃ (P : GL (Fin n) k) (w : Fin n → ℤ), (∀ t : kˣ,
        let g : Matrix (Fin n) (Fin n) k := P.val * diagonal (fun i => ((t ^ w i : kˣ) : k)) * P⁻¹.val
        (∀ a ∈ Z, a * g = g * a) ∧ g * N = (t : k) • (N * g) ∧ g *ᵥ v = v) ∧
      ∀ a : Matrix (Fin n) (Fin n) k, (∀ z ∈ Z, z * a = a * z) → a * N = N * a →
        ∃ u : Fin n → k, a *ᵥ v = P.val *ᵥ u ∧ ∀ i, w i < 0 → u i = 0 := by
  have hcard : Fintype.card κ = n := by
    rw [← Module.finrank_eq_card_basis β, Module.finrank_fin_fun]
  let e : κ ≃ Fin n := Fintype.equivFinOfCardEq hcard
  let b := β.reindex e
  let w : Fin n → ℤ := fun i => ω (e.symm i)
  have hb : ∀ j, β j = b (e j) := fun j => by simp [b]
  have himg : ∀ c : ℤ, β '' {j | ω j = c} = b '' {i | w i = c} := by
    intro c
    ext y
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨e j, by simpa [w] using hj, (hb j).symm⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨e.symm i, hi, by simp [b]⟩
  refine ⟨gradeBasisGL b, w, grade_fin b w Z N v ?_ ?_ ?_ ?_⟩
  · intro z hz i
    have := hZ z hz (e.symm i)
    rw [himg] at this
    simpa [b, w] using this
  · intro i
    have := hN (e.symm i)
    rw [himg] at this
    simpa [b, w] using this
  · rw [← himg]; exact hv
  · intro a ha haN i hi
    have := hA a ha haN (e.symm i) hi
    simpa [b] using this

theorem grade_of_frame {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {M : Type} [Fintype M] {L : M → Type}
    [∀ m, Fintype (L m)] {R : Z → (m : M) → L m → L m → k} {o : (m : M) → L m → k}
    {N : Matrix (Fin n) (Fin n) k} {v : Fin n → k} (F : Frame Z M L R o N v) :
    ∃ (P : GL (Fin n) k) (w : Fin n → ℤ), (∀ t : kˣ,
        let g : Matrix (Fin n) (Fin n) k := P.val * diagonal (fun i => ((t ^ w i : kˣ) : k)) * P⁻¹.val
        (∀ a ∈ Z, a * g = g * a) ∧ g * N = (t : k) • (N * g) ∧ g *ᵥ v = v) ∧
      ∀ a : Matrix (Fin n) (Fin n) k, (∀ z ∈ Z, z * a = a * z) → a * N = N * a →
        ∃ u : Fin n → k, a *ᵥ v = P.val *ᵥ u ∧ ∀ i, w i < 0 → u i = 0 := by
  let ω : (Σ m, L m × (Σ a : F.ι m, Fin (F.l m a))) → ℤ := fun j => ((j.2.2.2 : ℕ) : ℤ) - (F.s j.1 j.2.2.1 : ℤ)
  apply grade_of_basis F.β ω Z N v
  · rintro z hz ⟨m, p, jj⟩
    rw [show (z : Matrix (Fin n) (Fin n) k) = ((⟨z, hz⟩ : Z) : Matrix (Fin n) (Fin n) k) from rfl, F.hZ]
    refine sum_mem fun q _ => smul_mem _ _ (subset_span ⟨⟨m, q, jj⟩, rfl, rfl⟩)
  · rintro ⟨m, p, a, i⟩
    rw [F.hN]
    split_ifs with h
    · exact subset_span ⟨_, by simp only [Set.mem_ofPred_eq, ω]; push_cast; ring, rfl⟩
    · exact zero_mem _
  · suffices h : (∑ m, ∑ p, ∑ a, if h : F.s m a < F.l m a then o m p • F.β ⟨m, (p, ⟨a, ⟨F.s m a, h⟩⟩)⟩ else 0) ∈
        span k (F.β '' {j | ω j = 0}) by rw [← F.hv] at h; exact h
    refine sum_mem fun m _ => sum_mem fun p _ => sum_mem fun a _ => ?_
    split_ifs with h
    · exact smul_mem _ _ (subset_span ⟨_, by simp [ω], rfl⟩)
    · exact zero_mem _
  · rintro A hA hAN ⟨m, p, a, i⟩ hi
    exact F.hA A hA hAN m p a i (by simp only [ω] at hi; omega)

end PositivityTheory.RgUd.T.Nil.Orb.BReps
end
end
