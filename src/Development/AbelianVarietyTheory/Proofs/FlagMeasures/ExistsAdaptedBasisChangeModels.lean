module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointRationalEquivariance
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoefExtendsHolomorphically
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LieAlgebraBesselModelMiddleUnitaryEntries

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdaptedBasisChangeModels
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdaptedBasisChangeModels
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

noncomputable section

namespace GlobalTheory.AdaptedMove

private theorem lamX_eq_of_snd_eq (I : AutInst) {p q : I.GA} (h : p.2 = q.2) : lamX I p = lamX I q := by
  unfold lamX
  rw [h]

private theorem GL_mulVec_injective {K : Type} [Field K] {m : ℕ} (g : GL (Fin m) K) {u v : Fin m → K}
    (h : (g : Matrix (Fin m) (Fin m) K) *ᵥ u = (g : Matrix (Fin m) (Fin m) K) *ᵥ v) : u = v := by
  have h' := congrArg (fun w => ((g⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ w) h
  simpa [Matrix.mulVec_mulVec] using h'

theorem lamX_move (I : AutInst) (x x' : I.Gf) (h : ∃ γ ∈ I.GFset, ∃ k ∈ I.Kset, γ.2 * x = x' * k) :
    ∃ g : GL (Fin I.n) I.E, g ∈ Formalism.UG.UJ (starRingEnd I.E) I.J ∧
      ∀ y, (g : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ y ∈ lamX I (1, x') ↔ y ∈ lamX I (1, x) := by
  obtain ⟨γ, hγ, k, hk, hx⟩ := h
  obtain ⟨g, hgU, -, hgf⟩ := hγ
  refine ⟨g, hgU, fun y => ?_⟩
  have h1 : lamX I (γ * (1, x)) = lamX I (1, x') := by
    have e1 : lamX I (γ * (1, x)) = lamX I ((1, x') * (1, k)) :=
      lamX_eq_of_snd_eq I (by simp [hx])
    rw [e1]
    exact (GlobalTheory.PointEquivariance.lamX_mul_eq_iff I (1, x') (1, k)).1 hk
  have h2 := GlobalTheory.PointEquivariance.lamX_rat I (1, x) γ g hgf
  rw [h1, GlobalTheory.PointEquivariance.ratIso_apply] at h2
  rw [h2, Submodule.mem_map]
  constructor
  · rintro ⟨z, hz, hzy⟩
    have hzy' : (g : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ z = (g : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ y := by
      simpa using hzy
    rwa [← GL_mulVec_injective g hzy']
  · intro hy
    exact ⟨y, hy, by simp⟩

theorem isLattice_move {E : Type} [Field E] [NumberField E] {m : ℕ} (Λ Λ' : Submodule (𝓞 E) (Fin m → E))
    (γ : GL (Fin m) E) (h : ∀ y, (γ : Matrix (Fin m) (Fin m) E) *ᵥ y ∈ Λ' ↔ y ∈ Λ)
    (hΛ : Submodule.IsFullLattice E Λ) : Submodule.IsFullLattice E Λ' := by
  have hmap : Λ' = Λ.map ((Matrix.toLin' (γ : Matrix (Fin m) (Fin m) E)).restrictScalars (𝓞 E)) := by
    ext z
    simp only [Submodule.mem_map, LinearMap.coe_restrictScalars, Matrix.toLin'_apply]
    constructor
    · intro hz
      refine ⟨((γ⁻¹ : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) *ᵥ z, (h _).1 ?_, ?_⟩
      · simpa [Matrix.mulVec_mulVec] using hz
      · simp [Matrix.mulVec_mulVec]
    · rintro ⟨y, hy, rfl⟩
      exact (h y).2 hy
  have hspan : Submodule.span E (Λ : Set (Fin m → E)) ≤
      (Submodule.span E (Λ' : Set (Fin m → E))).comap
        (Matrix.toLin' (γ : Matrix (Fin m) (Fin m) E)) := by
    apply Submodule.span_le.mpr
    intro y hy
    exact Submodule.subset_span ((h y).2 hy)
  rw [hΛ.span_eq_top] at hspan
  refine { toIsLattice := ?_, span_eq_top := ?_ }
  · rw [hmap]
    exact Submodule.IsLattice.of_fg E (hΛ.fg.map _)
  · apply top_unique
    intro z _
    have hz := hspan (show ((γ⁻¹ : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) *ᵥ z ∈ ⊤ from trivial)
    simpa [Matrix.toLin'_apply, Matrix.mulVec_mulVec] using hz

theorem gram_mul {E : Type} [CommRing E] [StarRing E] {n p q : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (A : Matrix (Fin n) (Fin p) E) (B : Matrix (Fin n) (Fin q) E) (P : Matrix (Fin p) (Fin p) E)
    (Q : Matrix (Fin q) (Fin q) E) : (A * P)ᴴ * J * (B * Q) = Pᴴ * (Aᴴ * J * B) * Q := by
  rw [Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

private theorem star_dotProduct_conjTranspose_mulVec {K : Type} [Field K] [StarRing K] {m : ℕ} (N : Matrix (Fin m) (Fin m) K)
    (t u : Fin m → K) : star t ⬝ᵥ (Nᴴ *ᵥ u) = star (N *ᵥ t) ⬝ᵥ u := by
  rw [Matrix.dotProduct_mulVec, Matrix.star_mulVec]

private theorem map_mulVec_eq_mulVec_map {K₀ K : Type} [Field K₀] [Field K] {m : ℕ} (e : K₀ ≃+* K)
    (g : Matrix (Fin m) (Fin m) K₀) (y : Fin m → K₀) :
    (fun l => e ((g *ᵥ y) l)) = g.map e *ᵥ fun l => e (y l) := by
  ext l
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem adapted_move : ∀ (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (Λ : ∀ i, Submodule (𝓞 I.E) (Fin (j i) → I.E)) (x₀ : I₀.Gf) (T T' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E) (T₀ : Matrix (Fin I.n) (Fin I₀.n) I.E), (∀ i, 1 ≤ j i) → IsAdapted I I₀ e xf j S Λ x₀ T T' T₀ → ∀ (Λ' : ∀ i, Submodule (𝓞 I.E) (Fin (j i) → I.E)) (x₀' : I₀.Gf), (∀ i, ∃ γ : GL (Fin (j i)) I.E, ∀ y, (γ : Matrix (Fin (j i)) (Fin (j i)) I.E) *ᵥ y ∈ Λ' i ↔ y ∈ Λ i) → (∃ γ ∈ I₀.GFset, ∃ k ∈ I₀.Kset, γ.2 * x₀ = x₀' * k) → ∃ U U' U₀, IsAdapted I I₀ e xf j S Λ' x₀' U U' U₀ := by
  intro I I₀ e xf a j S Λ x₀ T T' T₀ _ hA Λ' x₀' hΛ hx
  obtain ⟨he, hn, hlat, hiso, hdual, h0, hlam, hS⟩ := hA
  choose γ hγ using hΛ
  obtain ⟨g₀, hg₀, hg₀m⟩ := lamX_move I₀ x₀ x₀' hx
  have hinv : Formalism.UG.cT (starRingEnd I₀.E) ((g₀⁻¹ : GL (Fin I₀.n) I₀.E).val) * I₀.J *
      (g₀⁻¹ : GL (Fin I₀.n) I₀.E).val = I₀.J := (Formalism.UG.UJ _ _).inv_mem hg₀
  have hcT : Formalism.UG.cT (starRingEnd I₀.E) ((g₀⁻¹ : GL (Fin I₀.n) I₀.E).val) =
      ((g₀⁻¹ : GL (Fin I₀.n) I₀.E).val)ᴴ := by
    ext r s
    simp only [Formalism.UG.cT, Matrix.conjTranspose_apply, Matrix.transpose_apply, Matrix.map_apply,
      starRingEnd_apply]
  rw [hcT] at hinv
  have hc : ∀ i, ((γ i).val)ᴴ * (((γ i)⁻¹).val)ᴴ = 1 := by
    intro i
    rw [← Matrix.conjTranspose_mul, Units.inv_mul, Matrix.conjTranspose_one]
  have hG1 : ((g₀⁻¹ : GL (Fin I₀.n) I₀.E).val).map e * (g₀.val).map e = 1 := by
    have h1 : ((g₀⁻¹ : GL (Fin I₀.n) I₀.E).val * g₀.val).map e = 1 := by
      rw [Units.inv_mul]
      exact Matrix.map_one _ (map_zero e) (map_one e)
    rw [← h1]
    ext r s
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.map_apply, Matrix.mul_apply, map_sum, map_mul]
  refine ⟨fun i => T i * ((γ i)⁻¹).val, fun i => T' i * ((γ i).val)ᴴ,
    T₀ * ((g₀⁻¹ : GL (Fin I₀.n) I₀.E).val).map e, he, hn,
    fun i => isLattice_move (Λ i) (Λ' i) (γ i) (hγ i) (hlat i), ?_, ?_, ?_, ?_, ?_⟩
  · intro i k
    obtain ⟨h1, h2, h3⟩ := hiso i k
    refine ⟨?_, ?_, fun hik => ?_⟩
    · rw [gram_mul, h1, Matrix.mul_zero, Matrix.zero_mul]
    · rw [gram_mul, h2, Matrix.mul_zero, Matrix.zero_mul]
    · rw [gram_mul, h3 hik, Matrix.mul_zero, Matrix.zero_mul]
  · intro i
    obtain ⟨h1, h2, h3⟩ := hdual i
    refine ⟨?_, ?_, ?_⟩
    · rw [gram_mul, h1, Matrix.mul_one, ← Matrix.conjTranspose_mul, Units.mul_inv,
        Matrix.conjTranspose_one]
    · rw [gram_mul, h2, Matrix.mul_zero, Matrix.zero_mul]
    · rw [gram_mul, h3, Matrix.mul_zero, Matrix.zero_mul]
  · rw [gram_mul, h0]
    have key : (((g₀⁻¹ : GL (Fin I₀.n) I₀.E).val).map e)ᴴ * I₀.J.map e *
        ((g₀⁻¹ : GL (Fin I₀.n) I₀.E).val).map e =
        (((g₀⁻¹ : GL (Fin I₀.n) I₀.E).val)ᴴ * I₀.J * (g₀⁻¹ : GL (Fin I₀.n) I₀.E).val).map e := by
      ext r s
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, map_sum, map_mul, he]
    rw [key, hinv]
  · intro z
    rw [hlam z]
    constructor
    · rintro ⟨u, u', y, hu, hu', hy, rfl⟩
      refine ⟨fun i => (γ i).val *ᵥ u i, fun i => (((γ i)⁻¹).val)ᴴ *ᵥ u' i, g₀.val *ᵥ y,
        fun i => (hγ i _).2 (hu i), fun i t ht => ?_, (hg₀m y).2 hy, ?_⟩
      · have ht' : ((γ i)⁻¹).val *ᵥ t ∈ Λ i := (hγ i _).1 (by simpa [Matrix.mulVec_mulVec] using ht)
        rw [star_dotProduct_conjTranspose_mulVec]
        exact hu' i _ ht'
      · simp only [Matrix.mulVec_mulVec, map_mulVec_eq_mulVec_map, Matrix.mul_assoc, Units.inv_mul, hc, hG1,
          Matrix.mul_one]
    · rintro ⟨w, w', y', hw, hw', hy', rfl⟩
      refine ⟨fun i => ((γ i)⁻¹).val *ᵥ w i, fun i => ((γ i).val)ᴴ *ᵥ w' i,
        (g₀⁻¹ : GL (Fin I₀.n) I₀.E).val *ᵥ y', fun i => (hγ i _).1 ?_, fun i t ht => ?_,
        (hg₀m _).1 ?_, ?_⟩
      · simpa [Matrix.mulVec_mulVec] using hw i
      · rw [star_dotProduct_conjTranspose_mulVec]
        exact hw' i _ ((hγ i t).2 ht)
      · simpa [Matrix.mulVec_mulVec] using hy'
      · simp only [Matrix.mulVec_mulVec, map_mulVec_eq_mulVec_map]
  · intro k z
    rw [hS k z]
    constructor
    · rintro ⟨u, hu, hz, rfl⟩
      refine ⟨fun i => (γ i).val *ᵥ u i, fun i => (hγ i _).2 (hu i), fun i hi => ?_, ?_⟩
      · simp [hz i hi]
      · simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
    · rintro ⟨w, hw, hz, rfl⟩
      refine ⟨fun i => ((γ i)⁻¹).val *ᵥ w i, fun i => (hγ i _).1 ?_, fun i hi => ?_, ?_⟩
      · simpa [Matrix.mulVec_mulVec] using hw i
      · simp [hz i hi]
      · simp only [Matrix.mulVec_mulVec]

end GlobalTheory.AdaptedMove
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdaptedBasisChangeModelsStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adapted_basis_change_models : ∀ (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (Λ : ∀ i, Submodule (𝓞 I.E) (Fin (j i) → I.E)) (x₀ : I₀.Gf) (T T' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E) (T₀ : Matrix (Fin I.n) (Fin I₀.n) I.E), (∀ i, 1 ≤ j i) → IsAdapted I I₀ e xf j S Λ x₀ T T' T₀ → ∀ (Λ' : ∀ i, Submodule (𝓞 I.E) (Fin (j i) → I.E)) (x₀' : I₀.Gf), (∀ i, ∃ γ : GL (Fin (j i)) I.E, ∀ y, (γ : Matrix (Fin (j i)) (Fin (j i)) I.E) *ᵥ y ∈ Λ' i ↔ y ∈ Λ i) → (∃ γ ∈ I₀.GFset, ∃ k ∈ I₀.Kset, γ.2 * x₀ = x₀' * k) → ∃ U U' U₀, IsAdapted I I₀ e xf j S Λ' x₀' U U' U₀ := by
  first | exact @GlobalTheory.AdaptedMove.adapted_move | exact GlobalTheory.AdaptedMove.adapted_move | (intros; apply GlobalTheory.AdaptedMove.adapted_move <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagsConjugateOfSameAdaptedModels
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagsConjugateOfSameAdaptedModels
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.FlagConj

section Linear

variable {E : Type} [Field E] [StarRing E] {n : ℕ}

theorem exists_unitary_of_gram {κ : Type} [Fintype κ] [DecidableEq κ] (hκ : Fintype.card κ = n)
    (J : Matrix (Fin n) (Fin n) E) (B B' : Matrix (Fin n) κ E) (G G' : Matrix κ κ E) (hG : G' * G = 1)
    (hB : Bᴴ * J * B = G) (hB' : B'ᴴ * J * B' = G) :
    ∃ γ : GL (Fin n) E, (γ : Matrix (Fin n) (Fin n) E)ᴴ * J * γ = J ∧ (γ : Matrix (Fin n) (Fin n) E) * B = B' := by
  have e : κ ≃ Fin n := Fintype.equivFinOfCardEq hκ
  have h1 : G' * Bᴴ * J * B = 1 := by rw [← hG, ← hB]; simp only [Matrix.mul_assoc]
  have h2 : G' * B'ᴴ * J * B' = 1 := by rw [← hG, ← hB']; simp only [Matrix.mul_assoc]
  generalize G' * Bᴴ * J = C at h1
  generalize G' * B'ᴴ * J = C' at h2
  have h3 : B * C = 1 := (Matrix.mul_eq_one_comm_of_equiv e).1 h1
  have h4 : B' * C' = 1 := (Matrix.mul_eq_one_comm_of_equiv e).1 h2
  refine ⟨⟨B' * C, B * C', ?_, ?_⟩, ?_, ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc C, h1, Matrix.one_mul, h4]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc C', h2, Matrix.one_mul, h3]
  · change (B' * C)ᴴ * J * (B' * C) = J
    calc (B' * C)ᴴ * J * (B' * C) = Cᴴ * (B'ᴴ * J * B') * C := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (B * C)ᴴ * J * (B * C) := by
          rw [hB', ← hB]
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = J := by rw [h3, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  · change B' * C * B = B'
    rw [Matrix.mul_assoc, h1, Matrix.mul_one]

def cat {a : ℕ} {j : Fin a → ℕ} (T : ∀ i, Matrix (Fin n) (Fin (j i)) E) :
    Matrix (Fin n) (Σ i, Fin (j i)) E := Matrix.of fun r p => T p.1 r p.2

theorem gram_adapted {a m : ℕ} {j : Fin a → ℕ} (J : Matrix (Fin n) (Fin n) E) (hJ : Jᴴ = J)
    (J₀ : Matrix (Fin m) (Fin m) E) (T T' : ∀ i, Matrix (Fin n) (Fin (j i)) E) (T₀ : Matrix (Fin n) (Fin m) E)
    (h1 : ∀ i k, (T i)ᴴ * J * T k = 0 ∧ (T' i)ᴴ * J * T' k = 0 ∧ (i ≠ k → (T i)ᴴ * J * T' k = 0))
    (h2 : ∀ i, (T i)ᴴ * J * T' i = 1 ∧ (T i)ᴴ * J * T₀ = 0 ∧ (T' i)ᴴ * J * T₀ = 0)
    (h3 : T₀ᴴ * J * T₀ = J₀) :
    (fromCols (fromCols (cat T) (cat T')) T₀)ᴴ * J * fromCols (fromCols (cat T) (cat T')) T₀ =
      fromBlocks (fromBlocks 0 1 1 0) 0 0 J₀ := by
  have sw : ∀ {α β : Type} (A : Matrix (Fin n) α E) (B : Matrix (Fin n) β E),
      Bᴴ * J * A = (Aᴴ * J * B)ᴴ := by
    intro α β A B
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJ, Matrix.mul_assoc]
  have a11 : (cat T)ᴴ * J * cat T = 0 := by
    ext ⟨i, s⟩ ⟨k, t⟩
    exact congrFun (congrFun (h1 i k).1 s) t
  have a22 : (cat T')ᴴ * J * cat T' = 0 := by
    ext ⟨i, s⟩ ⟨k, t⟩
    exact congrFun (congrFun (h1 i k).2.1 s) t
  have a12 : (cat T)ᴴ * J * cat T' = 1 := by
    ext ⟨i, s⟩ ⟨k, t⟩
    by_cases h : i = k
    · subst h
      refine (congrFun (congrFun (h2 i).1 s) t).trans ?_
      simp [Matrix.one_apply]
    · refine (congrFun (congrFun ((h1 i k).2.2 h) s) t).trans ?_
      simp [Matrix.one_apply, h]
  have a13 : (cat T)ᴴ * J * T₀ = 0 := by
    ext ⟨i, s⟩ t
    exact congrFun (congrFun (h2 i).2.1 s) t
  have a23 : (cat T')ᴴ * J * T₀ = 0 := by
    ext ⟨i, s⟩ t
    exact congrFun (congrFun (h2 i).2.2 s) t
  have a21 : (cat T')ᴴ * J * cat T = 1 := by rw [sw, a12, Matrix.conjTranspose_one]
  have a31 : T₀ᴴ * J * cat T = 0 := by rw [sw, a13, Matrix.conjTranspose_zero]
  have a32 : T₀ᴴ * J * cat T' = 0 := by rw [sw, a23, Matrix.conjTranspose_zero]
  ext ((p | p) | p) ((q | q) | q)
  · exact congrFun (congrFun a11 p) q
  · exact congrFun (congrFun a12 p) q
  · exact congrFun (congrFun a13 p) q
  · exact congrFun (congrFun a21 p) q
  · exact congrFun (congrFun a22 p) q
  · exact congrFun (congrFun a23 p) q
  · exact congrFun (congrFun a31 p) q
  · exact congrFun (congrFun a32 p) q
  · exact congrFun (congrFun h3 p) q

theorem exists_unitary_adapted {a m : ℕ} {j : Fin a → ℕ} (hn : n = m + 2 * ∑ i, j i)
    (J : Matrix (Fin n) (Fin n) E) (hJ : Jᴴ = J) (J₀ : Matrix (Fin m) (Fin m) E) (hJ₀ : J₀.det ≠ 0)
    (T T' U U' : ∀ i, Matrix (Fin n) (Fin (j i)) E) (T₀ U₀ : Matrix (Fin n) (Fin m) E)
    (h1 : ∀ i k, (T i)ᴴ * J * T k = 0 ∧ (T' i)ᴴ * J * T' k = 0 ∧ (i ≠ k → (T i)ᴴ * J * T' k = 0))
    (h2 : ∀ i, (T i)ᴴ * J * T' i = 1 ∧ (T i)ᴴ * J * T₀ = 0 ∧ (T' i)ᴴ * J * T₀ = 0)
    (h3 : T₀ᴴ * J * T₀ = J₀)
    (g1 : ∀ i k, (U i)ᴴ * J * U k = 0 ∧ (U' i)ᴴ * J * U' k = 0 ∧ (i ≠ k → (U i)ᴴ * J * U' k = 0))
    (g2 : ∀ i, (U i)ᴴ * J * U' i = 1 ∧ (U i)ᴴ * J * U₀ = 0 ∧ (U' i)ᴴ * J * U₀ = 0)
    (g3 : U₀ᴴ * J * U₀ = J₀) :
    ∃ γ : GL (Fin n) E, (γ : Matrix (Fin n) (Fin n) E)ᴴ * J * γ = J ∧
      (∀ i, (γ : Matrix (Fin n) (Fin n) E) * T i = U i) ∧ (∀ i, (γ : Matrix (Fin n) (Fin n) E) * T' i = U' i) ∧
      (γ : Matrix (Fin n) (Fin n) E) * T₀ = U₀ := by
  obtain ⟨γ, hγ, hB⟩ := exists_unitary_of_gram
    (κ := ((Σ i, Fin (j i)) ⊕ (Σ i, Fin (j i))) ⊕ Fin m) (by simp [hn]; ring) J _ _ _
    (fromBlocks (fromBlocks 0 1 1 0) 0 0 J₀⁻¹)
    (by simp [Matrix.fromBlocks_multiply, Matrix.nonsing_inv_mul _ (Ne.isUnit hJ₀)])
    (gram_adapted J hJ J₀ T T' T₀ h1 h2 h3) (gram_adapted J hJ J₀ U U' U₀ g1 g2 g3)
  refine ⟨γ, hγ, fun i => ?_, fun i => ?_, ?_⟩
  · ext r s
    exact congrFun (congrFun hB r) (Sum.inl (Sum.inl ⟨i, s⟩))
  · ext r s
    exact congrFun (congrFun hB r) (Sum.inl (Sum.inr ⟨i, s⟩))
  · ext r s
    exact congrFun (congrFun hB r) (Sum.inr s)

end Linear

theorem unitary_map {E A : Type} [CommRing E] [CommRing A] {n : ℕ} (σ : E →+* E) (s : A →+* A) (φ : E →+* A)
    (h : ∀ e, s (φ e) = φ (σ e)) (J g : Matrix (Fin n) (Fin n) E) (hg : Formalism.UG.cT σ g * J * g = J) :
    Formalism.UG.cT s (g.map φ) * J.map φ * g.map φ = J.map φ := by
  have e : Formalism.UG.cT s (g.map φ) = (Formalism.UG.cT σ g).map φ := by
    ext i k
    simp [Formalism.UG.cT, h]
  rw [e, ← Matrix.map_mul, ← Matrix.map_mul, hg]

theorem exists_point (I : AutInst) (γ : GL (Fin I.n) I.E) (hγ : γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J) :
    ∃ a : I.GA,
      (∀ v, uMat (a.1 v) = (I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v) ∧
      I.fmat a.2 = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)) := by
  have hφ : ∀ v e, starRingEnd ℂ (I.φ v e) = I.φ v (starRingEnd I.E e) :=
    fun v e => (I.cm.cmUnram.2.1 (I.φ v) e).symm
  have hf : ∀ e, Formalism.UG.sigR I.cm.sig (Af I.F) (Formalism.UG.inclE (F := I.F) (Af I.F) e) =
      Formalism.UG.inclE (F := I.F) (Af I.F) (starRingEnd I.E e) := by
    intro e
    simp [Formalism.UG.sigR, Formalism.UG.inclE]
    rfl
  have hPP : ∀ v, I.P v * (I.P v)⁻¹ = 1 := fun v =>
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v))
  let u : ∀ v : InfinitePlace I.F, (Matrix (Fin I.n) (Fin I.n) ℂ)ˣ := fun v =>
    (I.P_unit v).unit⁻¹ * Formalism.UG.bc (I.φ v) γ * (I.P_unit v).unit
  have hu : ∀ v, (u v : Matrix (Fin I.n) (Fin I.n) ℂ) =
      (I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v := by
    intro v
    simp only [u, Units.val_mul, Matrix.coe_units_inv, IsUnit.unit_spec]
    rfl
  have hPu : ∀ v, I.P v * (u v : Matrix (Fin I.n) (Fin I.n) ℂ) =
      (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v := by
    intro v
    rw [hu, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPP, Matrix.one_mul]
  have hU : ∀ v, u v ∈ Formalism.REAL.UJ (I.ε v) := by
    intro v
    change (u v : Matrix (Fin I.n) (Fin I.n) ℂ)ᴴ * Formalism.REAL.Jm (I.ε v) *
      (u v : Matrix (Fin I.n) (Fin I.n) ℂ) = Formalism.REAL.Jm (I.ε v)
    have h := unitary_map _ _ (I.φ v) (hφ v) I.J _ hγ
    have hc : Formalism.UG.cT (starRingEnd ℂ) ((γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v)) =
        ((γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v))ᴴ := by
      ext i j
      simp [Formalism.UG.cT]
    rw [hc] at h
    rw [← I.P_spec v]
    calc (u v : Matrix (Fin I.n) (Fin I.n) ℂ)ᴴ * ((I.P v)ᴴ * I.J.map (I.φ v) * I.P v) *
          (u v : Matrix (Fin I.n) (Fin I.n) ℂ)
        = (I.P v * (u v : Matrix (Fin I.n) (Fin I.n) ℂ))ᴴ * I.J.map (I.φ v) *
          (I.P v * (u v : Matrix (Fin I.n) (Fin I.n) ℂ)) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (I.P v)ᴴ * (((γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v))ᴴ * I.J.map (I.φ v) *
          (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v)) * I.P v := by
          rw [hPu]
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [h]
  have hF : Formalism.UG.bc (Formalism.UG.inclE (F := I.F) (Af I.F)) γ ∈ Formalism.UG.UPts I.cm.sig I.J (Af I.F) :=
    unitary_map _ _ _ hf I.J _ hγ
  exact ⟨(fun v => ⟨u v, hU v⟩, ⟨_, hF⟩), hu, rfl⟩

theorem mem_ratIso (I : AutInst) (γ : GL (Fin I.n) I.E) (N : Submodule (𝓞 I.E) (Fin I.n → I.E))
    (z : Fin I.n → I.E) :
    z ∈ GlobalTheory.PointEquivariance.ratIso I γ N ↔ ∃ y ∈ N, (γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ y = z := Iff.rfl

theorem conjugate_of_isAdapted : ∀ (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (Λ : ∀ i, Submodule (𝓞 I.E) (Fin (j i) → I.E)) (x₀ : I₀.Gf) (T T' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E) (T₀ : Matrix (Fin I.n) (Fin I₀.n) I.E), (∀ i, 1 ≤ j i) → IsAdapted I I₀ e xf j S Λ x₀ T T' T₀ → ∀ (xf' : I.Gf) (S' : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (U U' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E) (U₀ : Matrix (Fin I.n) (Fin I₀.n) I.E), IsAdapted I I₀ e xf' j S' Λ x₀ U U' U₀ → ∃ γ ∈ I.GFset, ∃ k ∈ I.Kset, γ.2 * xf = xf' * k ∧ ∀ g : I.Ginf, sizesAt I xf' S' (γ.1 * g) = sizesAt I xf S g := by
  intro I I₀ e xf a j S Λ x₀ T T' T₀ _ ⟨_, hn, _, h1, h2, h3, h4, h5⟩ xf' S' U U' U₀ ⟨_, _, _, g1, g2, g3, g4, g5⟩
  have hcT : ∀ M : Matrix (Fin I.n) (Fin I.n) I.E, Formalism.UG.cT (starRingEnd I.E) M = Mᴴ := fun M => rfl
  have hJ : I.Jᴴ = I.J := (hcT _).symm.trans I.J_herm
  have hJ₀ : (I₀.J.map e).det ≠ 0 := by
    have := RingHom.map_det (e : I₀.E →+* I.E) I₀.J
    change e _ = (I₀.J.map e).det at this
    rw [← this]
    exact (map_ne_zero e).2 I₀.J_det
  obtain ⟨γ, hγ, c1, c2, c3⟩ := exists_unitary_adapted hn I.J hJ _ hJ₀ T T' U U' T₀ U₀ h1 h2 h3 g1 g2 g3
  have hγ' : γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J := hγ
  obtain ⟨c, hc1, hc2⟩ := exists_point I γ hγ'
  have d1 : ∀ u : ∀ i, Fin (j i) → I.E,
      (γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ ∑ i, T i *ᵥ u i = ∑ i, U i *ᵥ u i := by
    intro u
    simp only [Matrix.mulVec_sum, Matrix.mulVec_mulVec, c1]
  have d2 : ∀ u : ∀ i, Fin (j i) → I.E,
      (γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ ∑ i, T' i *ᵥ u i = ∑ i, U' i *ᵥ u i := by
    intro u
    simp only [Matrix.mulVec_sum, Matrix.mulVec_mulVec, c2]
  have hS : ∀ k, S' k = GlobalTheory.PointEquivariance.ratIso I γ (S k) := by
    intro k
    ext z
    rw [g5, mem_ratIso]
    constructor
    · rintro ⟨u, p1, p2, rfl⟩
      exact ⟨_, (h5 k _).2 ⟨u, p1, p2, rfl⟩, d1 u⟩
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨u, p1, p2, rfl⟩ := (h5 k y).1 hy
      exact ⟨u, p1, p2, d1 u⟩
  have hL : lamX I (c * (1, xf)) = lamX I (1, xf') := by
    rw [GlobalTheory.PointEquivariance.lamX_rat I _ c γ hc2]
    ext z
    rw [g4, mem_ratIso]
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨u, u', w, p1, p2, p3, rfl⟩ := (h4 y).1 hy
      refine ⟨u, u', w, p1, p2, p3, ?_⟩
      rw [Matrix.mulVec_add, Matrix.mulVec_add, d1, d2, Matrix.mulVec_mulVec, c3]
    · rintro ⟨u, u', w, p1, p2, p3, rfl⟩
      refine ⟨_, (h4 _).2 ⟨u, u', w, p1, p2, p3, rfl⟩, ?_⟩
      rw [Matrix.mulVec_add, Matrix.mulVec_add, d1, d2, Matrix.mulVec_mulVec, c3]
  refine ⟨c, ⟨γ, hγ', hc1, hc2⟩, xf'⁻¹ * (c.2 * xf), ?_, (mul_inv_cancel_left _ _).symm, fun g => ?_⟩
  · have := (GlobalTheory.PointEquivariance.lamX_mul_eq_iff I (1, xf') (((1, xf') : I.GA)⁻¹ * (c * (1, xf)))).2
      (by rw [mul_inv_cancel_left, hL])
    exact this
  · funext i
    have hfr : frm I (c.1 * g, xf') = frm I (c * (g, xf)) := rfl
    unfold sizesAt
    rw [hfr, hS, hS]
    exact GlobalTheory.PointEquivariance.sizeQ_eq _ _ _ _ (GlobalTheory.PointEquivariance.zl_ratIso I (g, xf) c γ hc1)
      (GlobalTheory.PointEquivariance.rkK_ratIso I γ) _ _

end GlobalTheory.FlagConj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagsConjugateOfSameAdaptedModelsStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flags_conjugate_of_same_adapted_models : ∀ (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (Λ : ∀ i, Submodule (𝓞 I.E) (Fin (j i) → I.E)) (x₀ : I₀.Gf) (T T' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E) (T₀ : Matrix (Fin I.n) (Fin I₀.n) I.E), (∀ i, 1 ≤ j i) → IsAdapted I I₀ e xf j S Λ x₀ T T' T₀ → ∀ (xf' : I.Gf) (S' : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (U U' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E) (U₀ : Matrix (Fin I.n) (Fin I₀.n) I.E), IsAdapted I I₀ e xf' j S' Λ x₀ U U' U₀ → ∃ γ ∈ I.GFset, ∃ k ∈ I.Kset, γ.2 * xf = xf' * k ∧ ∀ g : I.Ginf, sizesAt I xf' S' (γ.1 * g) = sizesAt I xf S g := by
  first | exact @GlobalTheory.FlagConj.conjugate_of_isAdapted | exact GlobalTheory.FlagConj.conjugate_of_isAdapted | (intros; apply GlobalTheory.FlagConj.conjugate_of_isAdapted <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeOneSideUnfolding
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeOneSideUnfolding
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.OnePiece

variable {k r : ℕ}

theorem continuous_conj (a : Mat k r) : Continuous (conjM a : Mt k r → Mt k r) := by
  unfold conjM
  exact (continuous_const.matrix_mul continuous_id.matrixOf).matrix_mul continuous_const

def grp (k r : ℕ) : Set (Mt k r) := {x | Matrix.of x ∈ GG k r}

theorem measurableSet_grp : MeasurableSet (grp k r) := by
  have hc : Continuous fun x : Mt k r => (Matrix.of x : Mat k r)ᴴ * Hpk k r * Matrix.of x :=
    (continuous_id.matrixOf.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id.matrixOf
  exact (isClosed_eq hc continuous_const).measurableSet

private theorem continuous_matrix_of : Continuous fun x : Mt k r => (Matrix.of x : Mat k r) :=
  continuous_id.matrixOf

theorem measurable_indicator_grp {f : Mat k r → ℝ≥0∞} (hf : ContinuousOn f (GG k r)) :
    Measurable ((grp k r).indicator fun x => f (Matrix.of x)) := by
  classical
  rw [← Set.piecewise_eq_indicator]
  exact ContinuousOn.measurable_piecewise
    (hf.comp continuous_matrix_of.continuousOn fun _ hx => hx) continuousOn_const measurableSet_grp

theorem mem_GG_of_mul {s x : Mat k r} (hs : s ∈ GG k r) (h : s * x ∈ GG k r) : x ∈ GG k r := by
  have hs' : sᴴ * Hpk k r * s = Hpk k r := hs
  have h' : (s * x)ᴴ * Hpk k r * (s * x) = Hpk k r := h
  show xᴴ * Hpk k r * x = Hpk k r
  calc xᴴ * Hpk k r * x = xᴴ * (sᴴ * Hpk k r * s) * x := by rw [hs']
    _ = (s * x)ᴴ * Hpk k r * (s * x) := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Hpk k r := h'

theorem continuousOn_sq {X E : Type} [TopologicalSpace X] [NormedAddCommGroup E] {g : X → E} {s : Set X}
    (hg : ContinuousOn g s) : ContinuousOn (fun x => (‖g x‖₊ : ℝ≥0∞) ^ 2) s :=
  ((ENNReal.continuous_pow 2).comp (ENNReal.continuous_coe.comp continuous_nnnorm)).comp_continuousOn hg

private theorem mul_mem_UH_Hpk' {a b : Mat k r} (ha : a ∈ GG k r) (hb : b ∈ GG k r) : a * b ∈ GG k r := by
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have hb' : bᴴ * Hpk k r * b = Hpk k r := hb
  show (a * b)ᴴ * Hpk k r * (a * b) = Hpk k r
  calc (a * b)ᴴ * Hpk k r * (a * b) = bᴴ * (aᴴ * Hpk k r * a) * b := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [ha', hb']

private theorem aemeasurable_comp_of_continuousOn_closed {S : Set (Mat k r)} (hS : IsClosed S) {μ : Measure (Mt k r)}
    (hμ : μ {x | Matrix.of x ∉ S} = 0) {g : Mat k r → ℝ≥0∞} (hg : ContinuousOn g S) :
    AEMeasurable (fun x => g (Matrix.of x)) μ := by
  classical
  have hm : MeasurableSet {x : Mt k r | Matrix.of x ∈ S} :=
    (hS.preimage continuous_matrix_of).measurableSet
  have h1 : Measurable ({x : Mt k r | Matrix.of x ∈ S}.piecewise (fun x => g (Matrix.of x)) 0) :=
    ContinuousOn.measurable_piecewise (hg.comp continuous_matrix_of.continuousOn fun _ hx => hx)
      continuousOn_const hm
  have hae : ∀ᵐ x ∂μ, Matrix.of x ∈ S := by rw [ae_iff]; exact hμ
  refine h1.aemeasurable.congr ?_
  filter_upwards [hae] with x hx
  exact Set.piecewise_eq_of_mem _ _ _ hx

private theorem ofReal_one_sq_mul_norm_sq_div {E : Type} [NormedAddCommGroup E] (v : E) (d : ℕ) (hd : 0 < d) :
    ENNReal.ofReal ((1 : ℝ) ^ 2 * ‖v‖ ^ 2 / d) = (d : ℝ≥0∞)⁻¹ * (‖v‖₊ : ℝ≥0∞) ^ 2 := by
  have hd' : (0 : ℝ) < d := Nat.cast_pos.2 hd
  rw [one_pow, one_mul, div_eq_inv_mul, ENNReal.ofReal_mul (inv_nonneg.2 hd'.le),
    ENNReal.ofReal_inv_of_pos hd', ENNReal.ofReal_natCast, ← coe_nnnorm v, ← NNReal.coe_pow,
    ENNReal.ofReal_coe_nnreal, ENNReal.coe_pow]

theorem one_piece : ∀ (k r : ℕ) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (z : (Fin (2 * r + k + 1) → ℂ)) (π : Mat k r → (Wp →L[ℂ] Wp)) (ψ : Mat k r → ℂ) (μG μW μN νS : Measure (Mt k r)) (Φ : Mat k r → Wp) (c : ℝ), OneSide z π ψ μG μW μN νS Φ c → ∀ (f : Mt k r → ℝ≥0∞) (Q : Set (Mt k r)) (Vol : ℝ≥0∞), Measurable f → MeasurableSet Q → (∀ s ∈ Sset k r z, ∀ x, Matrix.of x ∈ GG k r → (lmulM s x ∈ Q ↔ x ∈ Q)) → (∀ g ∈ GG k r, ∫⁻ n, f (rmulM g n) ∂μN ≤ Vol) → ∀ w : Wp, ‖w‖ = 1 → ∫⁻ x in Q, f x * (‖⟪w, Φ (Matrix.of x)⟫_ℂ‖₊ : ℝ≥0∞) ^ 2 ∂μG ≤ Vol * (Module.finrank ℂ Wp : ℝ≥0∞)⁻¹ * ∫⁻ x in Q, (‖Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂νS := by
  intro k r Wp _ _ _ z π ψ μG μW μN νS Φ c hOS f Q Vol hf hQ hQinv hVol w hw
  obtain ⟨hz, hT, hnt, hU, hI, hG, hW, hW1, hN, hQm, hψ, hE, hΦ, -, -⟩ := hOS
  haveI := hnt
  have hd : 0 < Module.finrank ℂ Wp := Module.finrank_pos
  have hinC : Continuous fun v : Wp => ⟪w, v⟫_ℂ := continuous_const.inner continuous_id
  set A : Mt k r → ℝ≥0∞ := (grp k r).indicator fun y => (‖⟪w, Φ (Matrix.of y)⟫_ℂ‖₊ : ℝ≥0∞) ^ 2
    with hAdef
  set B : Mt k r → ℝ≥0∞ := (grp k r).indicator fun y => (‖Φ (Matrix.of y)‖₊ : ℝ≥0∞) ^ 2
    with hBdef
  have hAm : Measurable A :=
    measurable_indicator_grp (f := fun g => (‖⟪w, Φ g⟫_ℂ‖₊ : ℝ≥0∞) ^ 2)
      (continuousOn_sq (hinC.comp_continuousOn hΦ))
  have hBm : Measurable B :=
    measurable_indicator_grp (f := fun g => (‖Φ g‖₊ : ℝ≥0∞) ^ 2) (continuousOn_sq hΦ)
  set F : Mt k r → ℝ≥0∞ := Q.indicator fun y => f y * A y with hFdef
  have hFm : Measurable F := (hf.mul hAm).indicator hQ
  have haeG : ∀ᵐ x ∂μG, Matrix.of x ∈ GG k r := by rw [ae_iff]; exact hG.2.2.1
  have haeW : ∀ᵐ h ∂μW, Matrix.of h ∈ UWset k r z := by rw [ae_iff]; exact hW.2.2.1
  have haeN : ∀ᵐ n ∂μN, Matrix.of n ∈ Nset k r := by rw [ae_iff]; exact hN.2.2.1

  have step1 : ∫⁻ x in Q, f x * (‖⟪w, Φ (Matrix.of x)⟫_ℂ‖₊ : ℝ≥0∞) ^ 2 ∂μG = ∫⁻ x, F x ∂μG := by
    rw [← lintegral_indicator hQ]
    refine lintegral_congr_ae ?_
    filter_upwards [haeG] with x hx
    have hxg : x ∈ grp k r := hx
    by_cases hxQ : x ∈ Q
    · rw [hFdef, hAdef]
      simp only [Set.indicator_of_mem hxQ, Set.indicator_of_mem hxg]
    · rw [hFdef]
      simp only [Set.indicator_of_notMem hxQ]

  have inner_le : ∀ x : Mt k r,
      ∫⁻ s, F (fun i j => (Matrix.of s * Matrix.of x) i j) ∂(muProd μW μN) ≤
        Vol * (Module.finrank ℂ Wp : ℝ≥0∞)⁻¹ * Q.indicator B x := by
    intro x
    have hit : ∫⁻ s, F (fun i j => (Matrix.of s * Matrix.of x) i j) ∂(muProd μW μN) ≤
        ∫⁻ h, ∫⁻ n, F (lmulM (Matrix.of h * Matrix.of n) x) ∂μN ∂μW :=
      calc ∫⁻ s, F (fun i j => (Matrix.of s * Matrix.of x) i j) ∂(muProd μW μN)
          ≤ ∫⁻ p, F (lmulM (Matrix.of p.1 * Matrix.of p.2) x) ∂(μW.prod μN) := by
            apply lintegral_map_le
            have hc : Continuous (fun p : Mt k r × Mt k r => lmulM (Matrix.of p.1) p.2) := by
              exact continuous_fst.matrixOf.matrix_mul continuous_snd.matrixOf
            exact hc.measurable.aemeasurable
        _ ≤ ∫⁻ h, ∫⁻ n, F (lmulM (Matrix.of h * Matrix.of n) x) ∂μN ∂μW := lintegral_prod_le _
    refine hit.trans ?_
    have zero_case : (∀ h : Mt k r, Matrix.of h ∈ UWset k r z → ∀ n : Mt k r,
        Matrix.of n ∈ Nset k r → F (lmulM (Matrix.of h * Matrix.of n) x) = 0) →
        ∫⁻ h, ∫⁻ n, F (lmulM (Matrix.of h * Matrix.of n) x) ∂μN ∂μW ≤
          Vol * (Module.finrank ℂ Wp : ℝ≥0∞)⁻¹ * Q.indicator B x := by
      intro h0
      refine le_trans ?_ (zero_le ..)
      calc ∫⁻ h, ∫⁻ n, F (lmulM (Matrix.of h * Matrix.of n) x) ∂μN ∂μW
          ≤ ∫⁻ _h, (0 : ℝ≥0∞) ∂μW := by
            refine lintegral_mono_ae ?_
            filter_upwards [haeW] with h hh
            calc ∫⁻ n, F (lmulM (Matrix.of h * Matrix.of n) x) ∂μN ≤ ∫⁻ _n, (0 : ℝ≥0∞) ∂μN := by
                  refine lintegral_mono_ae ?_
                  filter_upwards [haeN] with n hn
                  exact (h0 h hh n hn).le
              _ = 0 := lintegral_zero
        _ = 0 := lintegral_zero
    by_cases hxg : x ∈ grp k r
    · by_cases hxQ : x ∈ Q
      · have hB : Q.indicator B x = (‖Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 := by
          rw [hBdef]
          simp only [Set.indicator_of_mem hxQ, Set.indicator_of_mem hxg]
        have hmain : ∀ h : Mt k r, Matrix.of h ∈ UWset k r z → ∀ n : Mt k r,
            Matrix.of n ∈ Nset k r → F (lmulM (Matrix.of h * Matrix.of n) x) =
              f (lmulM (Matrix.of h * Matrix.of n) x) *
                (‖⟪w, π (Matrix.of h) (Φ (Matrix.of x))⟫_ℂ‖₊ : ℝ≥0∞) ^ 2 := by
          intro h hh n hn
          have hs : Matrix.of h * Matrix.of n ∈ Sset k r z := by
            show ∃ h' ∈ UWset k r z, ∃ m ∈ Nset k r, Matrix.of h * Matrix.of n = h' * m
            exact ⟨_, hh, _, hn, rfl⟩
          have hSQ : lmulM (Matrix.of h * Matrix.of n) x ∈ Q := (hQinv _ hs x hxg).2 hxQ
          have hSG : lmulM (Matrix.of h * Matrix.of n) x ∈ grp k r :=
            mul_mem_UH_Hpk' (mul_mem_UH_Hpk' hh.1 hn.1) hxg
          have hΦS : Φ (Matrix.of (lmulM (Matrix.of h * Matrix.of n) x)) =
              ψ (Matrix.of n) • π (Matrix.of h) (Φ (Matrix.of x)) := hE _ hh _ hn _ hxg
          have hψ1 : ‖ψ (Matrix.of n)‖₊ = 1 := by ext; simpa using hψ _ hn
          rw [hFdef, hAdef]
          simp only [Set.indicator_of_mem hSQ, Set.indicator_of_mem hSG, hΦS, inner_smul_right,
            nnnorm_mul, hψ1, one_mul]
        have hfib : ∀ h : Mt k r, Matrix.of h ∈ UWset k r z →
            ∫⁻ n, f (lmulM (Matrix.of h * Matrix.of n) x) ∂μN ≤ Vol := by
          intro h hh
          have hdet : IsUnit (Matrix.of h : Mat k r).det := isUnit_det_of_mem_GG hh.1
          have key : ∀ n : Mt k r, lmulM (Matrix.of h * Matrix.of n) x =
              rmulM (Matrix.of h * Matrix.of x) (conjM (Matrix.of h) n) := by
            intro n
            show (Matrix.of h * Matrix.of n * Matrix.of x : Mat k r) =
              Matrix.of h * Matrix.of n * (Matrix.of h)⁻¹ * (Matrix.of h * Matrix.of x)
            rw [Matrix.mul_assoc (Matrix.of h * Matrix.of n) (Matrix.of h)⁻¹,
              ← Matrix.mul_assoc (Matrix.of h)⁻¹, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]
          have hrc : Continuous (rmulM (Matrix.of h * Matrix.of x) : Mt k r → Mt k r) := by
            unfold rmulM
            exact continuous_matrix_of.matrix_mul continuous_const
          have hinv : μN.map (conjM (Matrix.of h)) = μN :=
            ((GlobalTheory.T.unimodular_besselSubgroups_UW_N k r z hz hT μN).2.1 hN).2 _ hh
          calc ∫⁻ n, f (lmulM (Matrix.of h * Matrix.of n) x) ∂μN
              = ∫⁻ n, f (rmulM (Matrix.of h * Matrix.of x) (conjM (Matrix.of h) n)) ∂μN :=
                lintegral_congr fun n => congrArg f (key n)
            _ = ∫⁻ n, f (rmulM (Matrix.of h * Matrix.of x) n) ∂(μN.map (conjM (Matrix.of h))) :=
                (lintegral_map (hf.comp hrc.measurable) (continuous_conj _).measurable).symm
            _ = ∫⁻ n, f (rmulM (Matrix.of h * Matrix.of x) n) ∂μN := by rw [hinv]
            _ ≤ Vol := hVol _ (mul_mem_UH_Hpk' hh.1 hxg)
        have hAEM : AEMeasurable (fun h : Mt k r =>
            (‖⟪w, π (Matrix.of h) (Φ (Matrix.of x))⟫_ℂ‖₊ : ℝ≥0∞) ^ 2) μW :=
          aemeasurable_comp_of_continuousOn_closed (isClosedSub_UWset z).2.1 hW.2.2.1
            (g := fun g => (‖⟪w, π g (Φ (Matrix.of x))⟫_ℂ‖₊ : ℝ≥0∞) ^ 2)
            (continuousOn_sq (hinC.comp_continuousOn (hU.2.2 (Φ (Matrix.of x)))))
        calc ∫⁻ h, ∫⁻ n, F (lmulM (Matrix.of h * Matrix.of n) x) ∂μN ∂μW
            ≤ ∫⁻ h, Vol * (‖⟪w, π (Matrix.of h) (Φ (Matrix.of x))⟫_ℂ‖₊ : ℝ≥0∞) ^ 2 ∂μW := by
              refine lintegral_mono_ae ?_
              filter_upwards [haeW] with h hh
              calc ∫⁻ n, F (lmulM (Matrix.of h * Matrix.of n) x) ∂μN
                  = ∫⁻ n, f (lmulM (Matrix.of h * Matrix.of n) x) *
                      (‖⟪w, π (Matrix.of h) (Φ (Matrix.of x))⟫_ℂ‖₊ : ℝ≥0∞) ^ 2 ∂μN := by
                    refine lintegral_congr_ae ?_
                    filter_upwards [haeN] with n hn
                    exact hmain h hh n hn
                _ = (∫⁻ n, f (lmulM (Matrix.of h * Matrix.of n) x) ∂μN) *
                      (‖⟪w, π (Matrix.of h) (Φ (Matrix.of x))⟫_ℂ‖₊ : ℝ≥0∞) ^ 2 :=
                    lintegral_mul_const' _ _ (ENNReal.pow_ne_top ENNReal.coe_ne_top)
                _ ≤ Vol * (‖⟪w, π (Matrix.of h) (Φ (Matrix.of x))⟫_ℂ‖₊ : ℝ≥0∞) ^ 2 :=
                    mul_le_mul_of_nonneg_right (hfib h hh) (zero_le ..)
          _ = Vol * ∫⁻ h, (‖⟪w, π (Matrix.of h) (Φ (Matrix.of x))⟫_ℂ‖₊ : ℝ≥0∞) ^ 2 ∂μW :=
              lintegral_const_mul'' _ hAEM
          _ = Vol * ENNReal.ofReal (‖w‖ ^ 2 * ‖Φ (Matrix.of x)‖ ^ 2 / Module.finrank ℂ Wp) := by
              rw [(GlobalTheory.T.hcTypeW_irreducible_and_schur_average k r z π hz hT).2 μW hU hI hW hW1 w (Φ (Matrix.of x))]
          _ = Vol * (Module.finrank ℂ Wp : ℝ≥0∞)⁻¹ * Q.indicator B x := by
              rw [hB, hw, ofReal_one_sq_mul_norm_sq_div _ _ hd, mul_assoc]
      · refine zero_case fun h hh n hn => ?_
        have hs : Matrix.of h * Matrix.of n ∈ Sset k r z := by
          show ∃ h' ∈ UWset k r z, ∃ m ∈ Nset k r, Matrix.of h * Matrix.of n = h' * m
          exact ⟨_, hh, _, hn, rfl⟩
        have hSQ : lmulM (Matrix.of h * Matrix.of n) x ∉ Q := fun h' => hxQ ((hQinv _ hs x hxg).1 h')
        rw [hFdef]
        simp only [Set.indicator_of_notMem hSQ]
    · refine zero_case fun h hh n hn => ?_
      have hS : lmulM (Matrix.of h * Matrix.of n) x ∉ grp k r := fun hS =>
        hxg (mem_GG_of_mul (s := Matrix.of h * Matrix.of n) (x := Matrix.of x)
          (mul_mem_UH_Hpk' hh.1 hn.1) hS)
      rw [hFdef, hAdef]
      by_cases hSQ : lmulM (Matrix.of h * Matrix.of n) x ∈ Q
      · simp only [Set.indicator_of_mem hSQ, Set.indicator_of_notMem hS, mul_zero]
      · simp only [Set.indicator_of_notMem hSQ]
  calc ∫⁻ x in Q, f x * (‖⟪w, Φ (Matrix.of x)⟫_ℂ‖₊ : ℝ≥0∞) ^ 2 ∂μG = ∫⁻ x, F x ∂μG := step1
    _ = ∫⁻ x, ∫⁻ s, F (fun i j => (Matrix.of s * Matrix.of x) i j) ∂(muProd μW μN) ∂νS := hQm F hFm
    _ ≤ ∫⁻ x, Vol * (Module.finrank ℂ Wp : ℝ≥0∞)⁻¹ * Q.indicator B x ∂νS := lintegral_mono inner_le
    _ = Vol * (Module.finrank ℂ Wp : ℝ≥0∞)⁻¹ * ∫⁻ x, Q.indicator B x ∂νS :=
        lintegral_const_mul _ (hBm.indicator hQ)
    _ = Vol * (Module.finrank ℂ Wp : ℝ≥0∞)⁻¹ * ∫⁻ x in Q, B x ∂νS := by rw [lintegral_indicator hQ]
    _ ≤ Vol * (Module.finrank ℂ Wp : ℝ≥0∞)⁻¹ * ∫⁻ x in Q, (‖Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂νS :=
        mul_le_mul_of_nonneg_left (lintegral_mono fun x => Set.indicator_le_self _ _ x) (zero_le ..)

end GlobalTheory.Amp.OnePiece
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeOneSideUnfoldingStatement
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.amplitude_one_side_unfolding : ∀ (k r : ℕ) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (z : (Fin (2 * r + k + 1) → ℂ)) (π : Mat k r → (Wp →L[ℂ] Wp)) (ψ : Mat k r → ℂ) (μG μW μN νS : Measure (Mt k r)) (Φ : Mat k r → Wp) (c : ℝ), OneSide z π ψ μG μW μN νS Φ c → ∀ (f : Mt k r → ℝ≥0∞) (Q : Set (Mt k r)) (Vol : ℝ≥0∞), Measurable f → MeasurableSet Q → (∀ s ∈ Sset k r z, ∀ x, Matrix.of x ∈ GG k r → (lmulM s x ∈ Q ↔ x ∈ Q)) → (∀ g ∈ GG k r, ∫⁻ n, f (rmulM g n) ∂μN ≤ Vol) → ∀ w : Wp, ‖w‖ = 1 → ∫⁻ x in Q, f x * (‖⟪w, Φ (Matrix.of x)⟫_ℂ‖₊ : ℝ≥0∞) ^ 2 ∂μG ≤ Vol * (Module.finrank ℂ Wp : ℝ≥0∞)⁻¹ * ∫⁻ x in Q, (‖Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂νS := by
  first | exact @GlobalTheory.Amp.OnePiece.one_piece | exact GlobalTheory.Amp.OnePiece.one_piece | (intros; apply GlobalTheory.Amp.OnePiece.one_piece <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsContinuousLimitUniformCauchy
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsContinuousLimitUniformCauchy
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.SgInf.RegLimit

theorem sq_le_four (a e b : ENNReal) (h : a ≤ e + b) : a ^ 2 ≤ 4 * (e ^ 2 + b ^ 2) := by
  have h1 : e + b ≤ 2 * max e b := by
    rw [two_mul]; exact add_le_add (le_max_left _ _) (le_max_right _ _)
  have h2 : max e b ^ 2 ≤ e ^ 2 + b ^ 2 := by
    rcases le_total e b with h | h
    · rw [max_eq_right h]; exact le_add_self
    · rw [max_eq_left h]; exact le_self_add
  calc a ^ 2 ≤ (2 * max e b) ^ 2 := pow_le_pow_left₀ zero_le (h.trans h1) 2
    _ = 4 * max e b ^ 2 := by rw [mul_pow]; norm_num
    _ ≤ 4 * (e ^ 2 + b ^ 2) := by gcongr

theorem exists_continuous_limit : ∀ (k r : ℕ) (μ : Measure (Mt k r)), IsHaarOn (GG k r) μ → ∀ {Wp : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [CompleteSpace Wp] (f : ℕ → Mat k r → Wp) (g : Mt k r → Wp), (∀ j, ContinuousOn (f j) (GG k r)) → (∀ Q : Set (Mt k r), IsCompact Q → AEStronglyMeasurable g (μ.restrict Q)) → (∀ Q : Set (Mt k r), IsCompact Q → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ j ≥ N, ∀ l ≥ N, ∀ x ∈ Q, Matrix.of x ∈ GG k r → ‖f j (Matrix.of x) - f l (Matrix.of x)‖ ≤ ε) → (∀ Q : Set (Mt k r), IsCompact Q → Filter.Tendsto (fun j : ℕ => ∫⁻ x in Q, (‖f j (Matrix.of x) - g x‖₊ : ENNReal) ^ 2 ∂μ) Filter.atTop (nhds 0)) → ∃ F : Mat k r → Wp, ContinuousOn F (GG k r) ∧ ((fun x : Mt k r => F (Matrix.of x)) =ᵐ[μ] g) ∧ ∀ x ∈ GG k r, Filter.Tendsto (fun j : ℕ => f j x) Filter.atTop (nhds (F x)) := by
  intro k r μ hμ Wp _ _ _ f g hf hg hC hL
  set T : Set (Mt k r) → Set (Mat k r) := fun Q => GG k r ∩ {y | Matrix.of.symm y ∈ Q} with hT
  have hUC : ∀ Q : Set (Mt k r), IsCompact Q → UniformCauchySeqOn f Filter.atTop (T Q) := by
    intro Q hQ
    refine Metric.uniformCauchySeqOn_iff.2 fun ε hε => ?_
    obtain ⟨N, hN⟩ := hC Q hQ (ε / 2) (half_pos hε)
    refine ⟨N, fun m hm n hn y hy => ?_⟩
    have := hN m hm n hn (Matrix.of.symm y) hy.2 (by rw [Matrix.of.apply_symm_apply]; exact hy.1)
    simp only [Equiv.apply_symm_apply] at this
    rw [dist_eq_norm]; linarith
  set F : Mat k r → Wp := fun y => Filter.limUnder Filter.atTop (fun j => f j y) with hFdef
  have hF : ∀ y ∈ GG k r, Filter.Tendsto (fun j => f j y) Filter.atTop (nhds (F y)) := by
    intro y hy
    have hc := (hUC {Matrix.of.symm y} isCompact_singleton).cauchySeq
      (show y ∈ T {Matrix.of.symm y} from ⟨hy, rfl⟩)
    obtain ⟨L, hL'⟩ := cauchySeq_tendsto_of_complete hc
    exact tendsto_nhds_limUnder ⟨L, hL'⟩
  have hU : ∀ Q : Set (Mt k r), IsCompact Q → TendstoUniformlyOn f F Filter.atTop (T Q) :=
    fun Q hQ => (hUC Q hQ).tendstoUniformlyOn_of_tendsto (fun y hy => hF y hy.1)
  have hsymm : Continuous (fun y : Mat k r => (Matrix.of.symm y : Mt k r)) := continuous_id
  have hof : Continuous (fun x : Mt k r => (Matrix.of x : Mat k r)) := continuous_id
  have hFc : ContinuousOn F (GG k r) := by
    intro x hx
    set Q : Set (Mt k r) := Metric.closedBall (Matrix.of.symm x) 1
    have hQ : IsCompact Q := isCompact_closedBall _ _
    have h1 : ContinuousOn F (T Q) :=
      (hU Q hQ).continuousOn (Filter.Eventually.of_forall (f := Filter.atTop) fun j => (hf j).mono Set.inter_subset_left).frequently
    have hxT : x ∈ T Q := ⟨hx, show (Matrix.of.symm x : Mt k r) ∈ Q from Metric.mem_closedBall_self (x := (Matrix.of.symm x : Mt k r)) zero_le_one⟩
    refine (h1 x hxT).mono_of_mem_nhdsWithin ?_
    exact inter_mem_nhdsWithin _ (hsymm.continuousAt.preimage_mem_nhds
      (Metric.closedBall_mem_nhds _ zero_lt_one))

  have hGcl : IsClosed {x : Mt k r | Matrix.of x ∈ GG k r} := (gg_closedSub k r).2.1.preimage hof
  have hGae : ∀ᵐ x ∂μ, Matrix.of x ∈ GG k r := ae_iff.2 hμ.2.2.1
  have hFm : AEStronglyMeasurable (fun x : Mt k r => F (Matrix.of x)) μ := by
    have h1 : ContinuousOn (fun x : Mt k r => F (Matrix.of x)) {x : Mt k r | Matrix.of x ∈ GG k r} :=
      hFc.comp hof.continuousOn (fun x hx => hx)
    have h2 := h1.aestronglyMeasurable (μ := μ) hGcl.measurableSet
    rwa [Measure.restrict_eq_self_of_ae_mem (s := {x : Mt k r | Matrix.of x ∈ GG k r}) hGae] at h2
  have hQae : ∀ Q : Set (Mt k r), IsCompact Q → MeasurableSet Q →
      ∀ᵐ x ∂(μ.restrict Q), F (Matrix.of x) = g x := by
    intro Q hQ hQm
    have hQfin : μ Q ≠ ⊤ := (haar_compact_lt_top hμ hQ).ne
    set a : Mt k r → ENNReal := fun x => (‖F (Matrix.of x) - g x‖₊ : ENNReal) ^ 2 with ha
    have hbound : ∀ n : ℕ, ∫⁻ x in Q, a x ∂μ ≤
        4 * (ENNReal.ofReal (1 / ((n : ℝ) + 1)) ^ 2 * μ Q + ENNReal.ofReal (1 / ((n : ℝ) + 1))) := by
      intro n
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      have e1 := Metric.tendstoUniformlyOn_iff.1 (hU Q hQ) _ hpos
      have e2 := ENNReal.tendsto_nhds_zero.1 (hL Q hQ) _ (ENNReal.ofReal_pos.2 hpos)
      obtain ⟨j, hj1, hj2⟩ := (e1.and e2).exists
      calc ∫⁻ x in Q, a x ∂μ
          ≤ ∫⁻ x in Q, 4 * (ENNReal.ofReal (1 / ((n : ℝ) + 1)) ^ 2 +
              (‖f j (Matrix.of x) - g x‖₊ : ENNReal) ^ 2) ∂μ := by
            refine lintegral_mono_ae ?_
            filter_upwards [ae_restrict_mem hQm, ae_restrict_of_ae hGae] with x hxQ hxG
            apply sq_le_four
            have hd := hj1 (Matrix.of x) ⟨hxG, by simpa using hxQ⟩
            have htri : ‖F (Matrix.of x) - g x‖₊ ≤
                ‖F (Matrix.of x) - f j (Matrix.of x)‖₊ + ‖f j (Matrix.of x) - g x‖₊ := by
              have : F (Matrix.of x) - g x = (F (Matrix.of x) - f j (Matrix.of x)) + (f j (Matrix.of x) - g x) := by
                abel
              rw [this]; exact nnnorm_add_le _ _
            calc (‖F (Matrix.of x) - g x‖₊ : ENNReal)
                ≤ (‖F (Matrix.of x) - f j (Matrix.of x)‖₊ : ENNReal) + ‖f j (Matrix.of x) - g x‖₊ := by
                  rw [← ENNReal.coe_add]; exact ENNReal.coe_le_coe.2 htri
              _ ≤ ENNReal.ofReal (1 / ((n : ℝ) + 1)) + ‖f j (Matrix.of x) - g x‖₊ := by
                  gcongr
                  exact ENNReal.coe_le_coe.2 ((Real.le_toNNReal_iff_coe_le hpos.le).2
                    (by rw [coe_nnnorm, ← dist_eq_norm]; exact hd.le))
        _ = 4 * (ENNReal.ofReal (1 / ((n : ℝ) + 1)) ^ 2 * μ Q +
              ∫⁻ x in Q, (‖f j (Matrix.of x) - g x‖₊ : ENNReal) ^ 2 ∂μ) := by
            rw [lintegral_const_mul' _ _ (by norm_num), lintegral_add_left measurable_const,
              lintegral_const, Measure.restrict_apply_univ]
        _ ≤ _ := by gcongr
    have ht : Filter.Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1))) Filter.atTop (nhds 0) := by
      simpa using ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
    have ht2 : Filter.Tendsto (fun n : ℕ => 4 * (ENNReal.ofReal (1 / ((n : ℝ) + 1)) ^ 2 * μ Q +
        ENNReal.ofReal (1 / ((n : ℝ) + 1)))) Filter.atTop (nhds 0) := by
      have := ENNReal.Tendsto.const_mul ((ENNReal.Tendsto.mul_const (ENNReal.Tendsto.pow (n := 2) ht)
        (Or.inr hQfin)).add ht) (a := (4 : ENNReal)) (Or.inr (by norm_num))
      simpa using this
    have hzero : ∫⁻ x in Q, a x ∂μ = 0 := le_antisymm (ge_of_tendsto' ht2 hbound) (zero_le)
    have hm : AEStronglyMeasurable (fun x => F (Matrix.of x) - g x) (μ.restrict Q) :=
      hFm.restrict.sub (hg Q hQ)
    have hae := (lintegral_eq_zero_iff' (hm.nnnorm.aemeasurable.coe_nnreal_ennreal.pow_const 2)).1 hzero
    filter_upwards [hae] with x hx
    simpa [ha, sub_eq_zero] using hx
  refine ⟨F, hFc, ?_, hF⟩
  have hall : ∀ n : ℕ, ∀ᵐ x ∂(μ.restrict (Metric.closedBall (0 : Mt k r) n)), F (Matrix.of x) = g x :=
    fun n => hQae _ (isCompact_closedBall _ _) Metric.isClosed_closedBall.measurableSet
  have := (ae_restrict_iUnion_iff _ _).2 hall
  rwa [Metric.iUnion_closedBall_nat, Measure.restrict_univ] at this

end GlobalTheory.SgInf.RegLimit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsContinuousLimitUniformCauchyStatement
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_limit_uniformCauchy : ∀ (k r : ℕ) (μ : Measure (Mt k r)), IsHaarOn (GG k r) μ → ∀ {Wp : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [CompleteSpace Wp] (f : ℕ → Mat k r → Wp) (g : Mt k r → Wp), (∀ j, ContinuousOn (f j) (GG k r)) → (∀ Q : Set (Mt k r), IsCompact Q → AEStronglyMeasurable g (μ.restrict Q)) → (∀ Q : Set (Mt k r), IsCompact Q → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ j ≥ N, ∀ l ≥ N, ∀ x ∈ Q, Matrix.of x ∈ GG k r → ‖f j (Matrix.of x) - f l (Matrix.of x)‖ ≤ ε) → (∀ Q : Set (Mt k r), IsCompact Q → Filter.Tendsto (fun j : ℕ => ∫⁻ x in Q, (‖f j (Matrix.of x) - g x‖₊ : ENNReal) ^ 2 ∂μ) Filter.atTop (nhds 0)) → ∃ F : Mat k r → Wp, ContinuousOn F (GG k r) ∧ ((fun x : Mt k r => F (Matrix.of x)) =ᵐ[μ] g) ∧ ∀ x ∈ GG k r, Filter.Tendsto (fun j : ℕ => f j x) Filter.atTop (nhds (F x)) := by
  first | exact @GlobalTheory.SgInf.RegLimit.exists_continuous_limit | exact GlobalTheory.SgInf.RegLimit.exists_continuous_limit | (intros; apply GlobalTheory.SgInf.RegLimit.exists_continuous_limit <;> assumption)
end
end
