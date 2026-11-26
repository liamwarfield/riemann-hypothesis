module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ComplementaryBlockUnitaryForms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdaptedBasisChangeModels
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsoPartStable
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GradedPieceSizesUnipotentLeviCompactMove

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRationalFlagBlockFixingLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRationalFlagBlockFixingLattice
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

noncomputable section

namespace GlobalTheory.LeviRat

open GlobalTheory.AdaptedMove GlobalTheory.FlagConj GlobalTheory.PointEquivariance

theorem mem_conj_iff (I : AutInst) (x : I.Gf) (c : I.GA) (γ : GL (Fin I.n) I.E)
    (hc : I.fmat c.2 = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F))) :
    x⁻¹ * c.2 * x ∈ I.Kset ↔ ratIso I γ (lamX I (1, x)) = lamX I (1, x) := by
  have hk := GlobalTheory.PointEquivariance.lamX_mul_eq_iff I ((1 : I.Ginf), x) (((1 : I.Ginf), x)⁻¹ * c * ((1 : I.Ginf), x))
  have hcx : ((1 : I.Ginf), x) * (((1 : I.Ginf), x)⁻¹ * c * ((1 : I.Ginf), x)) = c * ((1 : I.Ginf), x) := by
    group
  rw [hcx, GlobalTheory.PointEquivariance.lamX_rat I ((1 : I.Ginf), x) c γ hc] at hk
  exact hk

private theorem mem_UJ_iff_flag_measures {E : Type} [Field E] [StarRing E] {m : ℕ} (J : Matrix (Fin m) (Fin m) E)
    (g : GL (Fin m) E) :
    g ∈ Formalism.UG.UJ (starRingEnd E) J ↔ (g : Matrix (Fin m) (Fin m) E)ᴴ * J * g = J := by
  have key : ((g : Matrix (Fin m) (Fin m) E).map (starRingEnd E))ᵀ = (g : Matrix (Fin m) (Fin m) E)ᴴ := by
    ext r s
    simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply, Matrix.map_apply]
    rfl
  show ((g : Matrix (Fin m) (Fin m) E).map (starRingEnd E))ᵀ * J * g = J ↔ _
  rw [key]

private theorem inv_mul_eq_mul_inv_of_mul_eq_mul {R : Type} [CommRing R] {m p : ℕ} (G G' : Matrix (Fin m) (Fin m) R)
    (C C' : Matrix (Fin p) (Fin p) R) (X : Matrix (Fin m) (Fin p) R) (hG : G' * G = 1) (hC : C * C' = 1)
    (h : G * X = X * C) : G' * X = X * C' := by
  calc G' * X = G' * (X * C) * C' := by rw [Matrix.mul_assoc, Matrix.mul_assoc, hC, Matrix.mul_one]
    _ = X * C' := by rw [← h, ← Matrix.mul_assoc, hG, Matrix.one_mul]

private theorem lat_mulVec_lemma_3 (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (xf : I.Gf) {a : ℕ} (j : Fin a → ℕ)
    (Λ : ∀ i, Submodule (𝓞 I.E) (Fin (j i) → I.E)) (x₀ : I₀.Gf)
    (T T' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E) (T₀ : Matrix (Fin I.n) (Fin I₀.n) I.E)
    (hlat : ∀ z, z ∈ lamX I (1, xf) ↔ ∃ (u u' : ∀ i, Fin (j i) → I.E) (y : Fin I₀.n → I₀.E), (∀ i, u i ∈ Λ i) ∧
      (∀ i, ∀ t ∈ Λ i, star t ⬝ᵥ u' i ∈ (algebraMap (𝓞 I.E) I.E).range) ∧ y ∈ lamX I₀ (1, x₀) ∧
      z = ∑ i, T i *ᵥ u i + ∑ i, T' i *ᵥ u' i + T₀ *ᵥ fun l => e (y l))
    (G : Matrix (Fin I.n) (Fin I.n) I.E) (c A : ∀ i, Matrix (Fin (j i)) (Fin (j i)) I.E)
    (d : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E)
    (hc : ∀ i, ∀ u ∈ Λ i, c i *ᵥ u ∈ Λ i) (hA : ∀ i, ∀ u ∈ Λ i, A i *ᵥ u ∈ Λ i)
    (hd : ∀ y ∈ lamX I₀ (1, x₀), d *ᵥ y ∈ lamX I₀ (1, x₀))
    (hT : ∀ i, G * T i = T i * c i) (hT' : ∀ i, G * T' i = T' i * (A i)ᴴ) (h₀ : G * T₀ = T₀ * d.map e) :
    ∀ z ∈ lamX I (1, xf), G *ᵥ z ∈ lamX I (1, xf) := by
  intro z hz
  obtain ⟨u, u', y, hu, hu', hy, rfl⟩ := (hlat z).1 hz
  refine (hlat _).2 ⟨fun i => c i *ᵥ u i, fun i => (A i)ᴴ *ᵥ u' i, d *ᵥ y, fun i => hc i _ (hu i), ?_, hd y hy, ?_⟩
  · intro i t ht
    rw [Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
    exact hu' i _ (hA i t ht)
  · beta_reduce
    rw [Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_sum, Matrix.mulVec_sum]
    congr 1
    · congr 1
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [Matrix.mulVec_mulVec, hT i, ← Matrix.mulVec_mulVec]
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [Matrix.mulVec_mulVec, hT' i, ← Matrix.mulVec_mulVec]
    · rw [Matrix.mulVec_mulVec, h₀, ← Matrix.mulVec_mulVec]
      congr 1
      funext l
      exact (RingHom.map_mulVec (e : I₀.E →+* I.E) d y l).symm

theorem exists_rat_block : ∀ (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (Λ : ∀ i, Submodule (𝓞 I.E) (Fin (j i) → I.E)) (x₀ : I₀.Gf) (T T' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E) (T₀ : Matrix (Fin I.n) (Fin I₀.n) I.E), IsAdapted I I₀ e xf j S Λ x₀ T T' T₀ → ∀ γ : ∀ i, GL (Fin (j i)) I.E, (∀ i y, (γ i : Matrix (Fin (j i)) (Fin (j i)) I.E) *ᵥ y ∈ Λ i ↔ y ∈ Λ i) → ∀ g₀ ∈ latGroup I₀ x₀, ∃ g ∈ latGroup I xf, ∃ (Γ : Matrix (Fin I.n) (Fin I.n) I.E) (γ₀ : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E), (∀ v, uMat (g v) = (I.P v)⁻¹ * Γ.map (I.φ v) * I.P v) ∧ (∀ v, uMat (g₀ v) = (I₀.P v)⁻¹ * γ₀.map (I₀.φ v) * I₀.P v) ∧ (∀ i, Γ * T i = T i * (γ i : Matrix (Fin (j i)) (Fin (j i)) I.E)) ∧ Γ * T₀ = T₀ * γ₀.map e := by
  intro I I₀ e xf a j S Λ x₀ T T' T₀ hAd γ hγ g₀ hg₀
  obtain ⟨he, hn, -, h1, h2, h3, hlat, -⟩ := hAd
  obtain ⟨c₀, ⟨δ, hδU, hδP, hδf⟩, rfl, hc₀K⟩ := hg₀
  have hδL := (mem_conj_iff I₀ x₀ c₀ δ hδf).1 hc₀K
  have hJ : I.Jᴴ = I.J := by
    have hH : (I.J.map (starRingEnd I.E))ᵀ = I.J := I.J_herm
    ext r s
    have := congrArg (fun M => M r s) hH
    simp only [Matrix.transpose_apply, Matrix.map_apply] at this
    rw [Matrix.conjTranspose_apply, ← this]
    rfl
  have hJ₀ : (I₀.J.map e).det ≠ 0 := by
    intro h
    apply I₀.J_det
    have h' : (e : I₀.E →+* I.E) I₀.J.det = 0 := by
      rw [RingHom.map_det]
      exact h
    simpa using h'
  have hsemi : Function.Semiconj e star star := he
  have hδU' := (mem_UJ_iff_flag_measures I₀.J δ).1 hδU
  obtain ⟨U, hU⟩ : ∃ U : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E,
      ∀ i, U i = T i * (γ i : Matrix (Fin (j i)) (Fin (j i)) I.E) := ⟨_, fun _ => rfl⟩
  obtain ⟨U', hU'⟩ : ∃ U' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E,
      ∀ i, U' i = T' i * (((γ i)⁻¹ : GL (Fin (j i)) I.E) : Matrix (Fin (j i)) (Fin (j i)) I.E)ᴴ :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨U₀, hU₀⟩ : ∃ U₀ : Matrix (Fin I.n) (Fin I₀.n) I.E,
      U₀ = T₀ * (δ : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E).map e := ⟨_, rfl⟩
  have g1 : ∀ i k, (U i)ᴴ * I.J * U k = 0 ∧ (U' i)ᴴ * I.J * U' k = 0 ∧
      (i ≠ k → (U i)ᴴ * I.J * U' k = 0) := by
    intro i k
    obtain ⟨a1, a2, a3⟩ := h1 i k
    refine ⟨?_, ?_, fun hik => ?_⟩
    · rw [hU, hU, GlobalTheory.AdaptedMove.gram_mul, a1, Matrix.mul_zero, Matrix.zero_mul]
    · rw [hU', hU', GlobalTheory.AdaptedMove.gram_mul, a2, Matrix.mul_zero, Matrix.zero_mul]
    · rw [hU, hU', GlobalTheory.AdaptedMove.gram_mul, a3 hik, Matrix.mul_zero, Matrix.zero_mul]
  have g2 : ∀ i, (U i)ᴴ * I.J * U' i = 1 ∧ (U i)ᴴ * I.J * U₀ = 0 ∧ (U' i)ᴴ * I.J * U₀ = 0 := by
    intro i
    obtain ⟨b1, b2, b3⟩ := h2 i
    refine ⟨?_, ?_, ?_⟩
    · rw [hU, hU', GlobalTheory.AdaptedMove.gram_mul, b1, Matrix.mul_one, ← Matrix.conjTranspose_mul, Units.inv_mul,
        Matrix.conjTranspose_one]
    · rw [hU, hU₀, GlobalTheory.AdaptedMove.gram_mul, b2, Matrix.mul_zero, Matrix.zero_mul]
    · rw [hU', hU₀, GlobalTheory.AdaptedMove.gram_mul, b3, Matrix.mul_zero, Matrix.zero_mul]
  have g3 : U₀ᴴ * I.J * U₀ = I₀.J.map e := by
    rw [hU₀, GlobalTheory.AdaptedMove.gram_mul, h3, ← Matrix.conjTranspose_map _ hsemi]
    calc ((δ : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E)ᴴ).map e * I₀.J.map e * (δ : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E).map e
        = ((δ : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E)ᴴ * I₀.J * δ).map (e : I₀.E →+* I.E) := by
          rw [Matrix.map_mul, Matrix.map_mul]
          rfl
      _ = I₀.J.map e := by
          rw [hδU']
          rfl
  obtain ⟨Γ, hΓJ, hΓT, hΓT', hΓ₀⟩ :=
    GlobalTheory.FlagConj.exists_unitary_adapted hn I.J hJ (I₀.J.map e) hJ₀ T T' U U' T₀ U₀ h1 h2 h3 g1 g2 g3
  have hΓU : Γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J := (mem_UJ_iff_flag_measures I.J Γ).2 hΓJ
  obtain ⟨c, hc1, hc2⟩ := GlobalTheory.FlagConj.exists_point I Γ hΓU
  have hγf : ∀ i, ∀ u ∈ Λ i, (γ i : Matrix (Fin (j i)) (Fin (j i)) I.E) *ᵥ u ∈ Λ i :=
    fun i u hu => (hγ i u).2 hu
  have hγb : ∀ i, ∀ u ∈ Λ i, (((γ i)⁻¹ : GL (Fin (j i)) I.E) : Matrix (Fin (j i)) (Fin (j i)) I.E) *ᵥ u ∈ Λ i := by
    intro i u hu
    apply (hγ i _).1
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    exact hu
  have hδf' : ∀ y ∈ lamX I₀ (1, x₀), (δ : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E) *ᵥ y ∈ lamX I₀ (1, x₀) := by
    intro y hy
    rw [← hδL, GlobalTheory.FlagConj.mem_ratIso]
    exact ⟨y, hy, rfl⟩
  have hδb : ∀ y ∈ lamX I₀ (1, x₀),
      ((δ⁻¹ : GL (Fin I₀.n) I₀.E) : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E) *ᵥ y ∈ lamX I₀ (1, x₀) := by
    intro y hy
    rw [← hδL, GlobalTheory.FlagConj.mem_ratIso] at hy
    obtain ⟨y', hy', rfl⟩ := hy
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    exact hy'
  have hT : ∀ i, (Γ : Matrix (Fin I.n) (Fin I.n) I.E) * T i = T i * (γ i : Matrix (Fin (j i)) (Fin (j i)) I.E) :=
    fun i => (hΓT i).trans (hU i)
  have hT' : ∀ i, (Γ : Matrix (Fin I.n) (Fin I.n) I.E) * T' i =
      T' i * (((γ i)⁻¹ : GL (Fin (j i)) I.E) : Matrix (Fin (j i)) (Fin (j i)) I.E)ᴴ :=
    fun i => (hΓT' i).trans (hU' i)
  have hT₀ : (Γ : Matrix (Fin I.n) (Fin I.n) I.E) * T₀ = T₀ * (δ : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E).map e :=
    hΓ₀.trans hU₀
  have hΓi : (((Γ⁻¹ : GL (Fin I.n) I.E)) : Matrix (Fin I.n) (Fin I.n) I.E) * Γ = 1 := Units.inv_mul Γ
  have hTb : ∀ i, (((Γ⁻¹ : GL (Fin I.n) I.E)) : Matrix (Fin I.n) (Fin I.n) I.E) * T i =
      T i * (((γ i)⁻¹ : GL (Fin (j i)) I.E) : Matrix (Fin (j i)) (Fin (j i)) I.E) :=
    fun i => inv_mul_eq_mul_inv_of_mul_eq_mul _ _ _ _ _ hΓi (Units.mul_inv (γ i)) (hT i)
  have hT'b : ∀ i, (((Γ⁻¹ : GL (Fin I.n) I.E)) : Matrix (Fin I.n) (Fin I.n) I.E) * T' i =
      T' i * (γ i : Matrix (Fin (j i)) (Fin (j i)) I.E)ᴴ := by
    intro i
    refine inv_mul_eq_mul_inv_of_mul_eq_mul _ _ _ _ _ hΓi ?_ (hT' i)
    rw [← Matrix.conjTranspose_mul, Units.mul_inv, Matrix.conjTranspose_one]
  have hT₀b : (((Γ⁻¹ : GL (Fin I.n) I.E)) : Matrix (Fin I.n) (Fin I.n) I.E) * T₀ =
      T₀ * (((δ⁻¹ : GL (Fin I₀.n) I₀.E)) : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E).map e := by
    refine inv_mul_eq_mul_inv_of_mul_eq_mul _ _ _ _ _ hΓi ?_ hT₀
    have hm : (δ : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E).map e *
        (((δ⁻¹ : GL (Fin I₀.n) I₀.E)) : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E).map e =
        ((δ : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E) *
          (((δ⁻¹ : GL (Fin I₀.n) I₀.E)) : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E)).map (e : I₀.E →+* I.E) :=
      (Matrix.map_mul).symm
    rw [hm, Units.mul_inv]
    exact Matrix.map_one _ (map_zero e) (map_one e)
  have hfw := lat_mulVec_lemma_3 I I₀ e xf j Λ x₀ T T' T₀ hlat Γ
    (fun i => (γ i : Matrix (Fin (j i)) (Fin (j i)) I.E))
    (fun i => (((γ i)⁻¹ : GL (Fin (j i)) I.E) : Matrix (Fin (j i)) (Fin (j i)) I.E)) δ hγf hγb hδf' hT hT' hT₀
  have hbw := lat_mulVec_lemma_3 I I₀ e xf j Λ x₀ T T' T₀ hlat (((Γ⁻¹ : GL (Fin I.n) I.E)) : Matrix (Fin I.n) (Fin I.n) I.E)
    (fun i => (((γ i)⁻¹ : GL (Fin (j i)) I.E) : Matrix (Fin (j i)) (Fin (j i)) I.E))
    (fun i => (γ i : Matrix (Fin (j i)) (Fin (j i)) I.E))
    (((δ⁻¹ : GL (Fin I₀.n) I₀.E)) : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E) hγb hγf hδb hTb hT'b hT₀b
  have hLat : ratIso I Γ (lamX I (1, xf)) = lamX I (1, xf) := by
    ext z
    rw [GlobalTheory.FlagConj.mem_ratIso]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hfw y hy
    · intro hz
      refine ⟨(((Γ⁻¹ : GL (Fin I.n) I.E)) : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ z, hbw z hz, ?_⟩
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  exact ⟨c.1, ⟨c, ⟨Γ, hΓU, hc1, hc2⟩, rfl, (mem_conj_iff I xf c Γ hc2).2 hLat⟩,
    (Γ : Matrix (Fin I.n) (Fin I.n) I.E), (δ : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E), hc1, hδP, hT, hT₀⟩

end GlobalTheory.LeviRat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRationalFlagBlockFixingLatticeStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_flag_block_fixing_lattice : ∀ (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (Λ : ∀ i, Submodule (𝓞 I.E) (Fin (j i) → I.E)) (x₀ : I₀.Gf) (T T' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E) (T₀ : Matrix (Fin I.n) (Fin I₀.n) I.E), IsAdapted I I₀ e xf j S Λ x₀ T T' T₀ → ∀ γ : ∀ i, GL (Fin (j i)) I.E, (∀ i y, (γ i : Matrix (Fin (j i)) (Fin (j i)) I.E) *ᵥ y ∈ Λ i ↔ y ∈ Λ i) → ∀ g₀ ∈ latGroup I₀ x₀, ∃ g ∈ latGroup I xf, ∃ (Γ : Matrix (Fin I.n) (Fin I.n) I.E) (γ₀ : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E), (∀ v, uMat (g v) = (I.P v)⁻¹ * Γ.map (I.φ v) * I.P v) ∧ (∀ v, uMat (g₀ v) = (I₀.P v)⁻¹ * γ₀.map (I₀.φ v) * I₀.P v) ∧ (∀ i, Γ * T i = T i * (γ i : Matrix (Fin (j i)) (Fin (j i)) I.E)) ∧ Γ * T₀ = T₀ * γ₀.map e := by
  first | exact @GlobalTheory.LeviRat.exists_rat_block | exact GlobalTheory.LeviRat.exists_rat_block | (intros; apply GlobalTheory.LeviRat.exists_rat_block <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingRearrangePiProdMeasures
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingRearrangePiProdMeasures
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

namespace GlobalTheory.LeviIso

theorem measurePreserving_rearrange (V V' V'' : Type) [Fintype V] [Fintype V'] [Fintype V''] (β : V ≃ V')
    (σ : V ≃ V'') (a : ℕ) (X : Fin a → Type) [∀ i, MeasurableSpace (X i)] (Y : V'' → Type)
    [∀ w, MeasurableSpace (Y w)] (m : ∀ i, Measure (X i)) [∀ i, SigmaFinite (m i)] (ν : ∀ w, Measure (Y w))
    [∀ w, SigmaFinite (ν w)] (b : Fin a → ℝ) (c : V'' → ℝ) (hb : ∀ i, 0 ≤ b i) (hc : ∀ w, 0 ≤ c w) :
    MeasurePreserving
      (fun (z : (∀ i, V' → X i) × (∀ w, Y w)) (v : V) => ((fun i => z.1 i (β v)), z.2 (σ v)))
      (((∏ i, ENNReal.ofReal (b i ^ Fintype.card V)) * ENNReal.ofReal (∏ w, c w)) •
        (Measure.pi fun i => Measure.pi fun _ : V' => m i).prod (Measure.pi ν))
      (Measure.pi fun v : V => (Measure.pi fun i => ENNReal.ofReal (b i) • m i).prod
        (ENNReal.ofReal (c (σ v)) • ν (σ v))) := by
  have hm : Measurable
      (fun (z : (∀ i, V' → X i) × (∀ w, Y w)) (v : V) => ((fun i => z.1 i (β v)), z.2 (σ v))) := by
    fun_prop
  refine ⟨hm, ?_⟩
  refine (Measure.pi_eq_generateFrom
    (C := fun v => Set.image2 (· ×ˢ ·)
      (Set.pi Set.univ '' Set.pi Set.univ fun i => {s : Set (X i) | MeasurableSet s})
      {s : Set (Y (σ v)) | MeasurableSet s})
    (fun v => (generateFrom_eq_prod generateFrom_pi MeasurableSpace.generateFrom_measurableSet
      (IsCountablySpanning.pi fun _ => isCountablySpanning_measurableSet)
      isCountablySpanning_measurableSet))
    (fun _ => isPiSystem_pi.prod MeasurableSpace.isPiSystem_measurableSet)
    (fun v => (Measure.FiniteSpanningSetsIn.pi fun i =>
      (ENNReal.ofReal (b i) • m i).toFiniteSpanningSetsIn).prod
        (ENNReal.ofReal (c (σ v)) • ν (σ v)).toFiniteSpanningSetsIn) ?_).symm
  intro s hs
  choose t' ht' u hu hst using hs
  choose t ht htt using ht'
  have htm : ∀ v i, MeasurableSet (t v i) := fun v i => ht v i (Set.mem_univ _)
  have hs' : ∀ v, s v = (Set.pi Set.univ (t v)) ×ˢ u v := fun v => by rw [← hst v, htt v]
  have hsm : MeasurableSet (Set.pi Set.univ s) := by
    refine MeasurableSet.univ_pi fun v => ?_
    rw [hs' v]
    exact (MeasurableSet.univ_pi fun i => htm v i).prod (hu v)
  obtain ⟨u', hu'⟩ : ∃ u' : ∀ w, Set (Y w), ∀ v, u' (σ v) = u v :=
    ⟨Equiv.piCongrLeft (fun w => Set (Y w)) σ u, fun v => Equiv.piCongrLeft_apply_apply _ _ _ _⟩
  rw [Measure.map_apply hm hsm]
  have hpre : (fun (z : (∀ i, V' → X i) × (∀ w, Y w)) (v : V) => ((fun i => z.1 i (β v)), z.2 (σ v))) ⁻¹'
      Set.pi Set.univ s =
      (Set.pi Set.univ fun i => Set.pi Set.univ fun v' => t (β.symm v') i) ×ˢ Set.pi Set.univ u' := by
    ext z
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, hs', Set.mem_prod, forall_and]
    refine and_congr ?_ ?_
    · rw [forall_comm]
      refine forall_congr' fun i => ?_
      rw [← β.forall_congr_right]
      simp only [Equiv.symm_apply_apply]
    · rw [← σ.forall_congr_right]
      simp only [hu']
  rw [hpre, Measure.smul_apply, Measure.prod_prod]
  simp only [hs', Measure.prod_prod, Measure.pi_pi, Measure.smul_apply, smul_eq_mul,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  have h1 : ∏ i, ∏ v', m i (t (β.symm v') i) = ∏ v, ∏ i, m i (t v i) := by
    rw [Finset.prod_comm]
    exact β.symm.prod_comp fun v => ∏ i, m i (t v i)
  have h2 : ∏ w, ν w (u' w) = ∏ v, ν (σ v) (u v) := by
    rw [← σ.prod_comp]
    simp only [hu']
  have h3 : ENNReal.ofReal (∏ w, c w) = ∏ v, ENNReal.ofReal (c (σ v)) := by
    rw [ENNReal.ofReal_prod_of_nonneg fun w _ => hc w, ← σ.prod_comp]
  have h4 : ∏ i, ENNReal.ofReal (b i ^ Fintype.card V) = (∏ i, ENNReal.ofReal (b i)) ^ Fintype.card V := by
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl fun i _ => ENNReal.ofReal_pow (hb i) _
  rw [h1, h2, h3, h4]
  ring

end GlobalTheory.LeviIso
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingRearrangePiProdMeasuresStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurePreserving_rearrange_pi_prod_measures : ∀ (V V' V'' : Type) [Fintype V] [Fintype V'] [Fintype V''] (β : V ≃ V') (σ : V ≃ V'') (a : ℕ) (X : Fin a → Type) [∀ i, MeasurableSpace (X i)] (Y : V'' → Type) [∀ w, MeasurableSpace (Y w)] (m : ∀ i, Measure (X i)) [∀ i, SigmaFinite (m i)] (ν : ∀ w, Measure (Y w)) [∀ w, SigmaFinite (ν w)] (b : Fin a → ℝ) (c : V'' → ℝ), (∀ i, 0 ≤ b i) → (∀ w, 0 ≤ c w) → MeasurePreserving (fun (z : (∀ i, V' → X i) × (∀ w, Y w)) (v : V) => ((fun i => z.1 i (β v)), z.2 (σ v))) (((∏ i, ENNReal.ofReal (b i ^ Fintype.card V)) * ENNReal.ofReal (∏ w, c w)) • (Measure.pi fun i => Measure.pi fun _ : V' => m i).prod (Measure.pi ν)) (Measure.pi fun v : V => (Measure.pi fun i => ENNReal.ofReal (b i) • m i).prod (ENNReal.ofReal (c (σ v)) • ν (σ v))) := by
  first | exact @GlobalTheory.LeviIso.measurePreserving_rearrange | exact GlobalTheory.LeviIso.measurePreserving_rearrange | (intros; apply GlobalTheory.LeviIso.measurePreserving_rearrange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InfiniteGLHaarMeasureEqPiLocal
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InfiniteGLHaarMeasureEqPiLocal
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso
open scoped ENNReal

noncomputable section

namespace GlobalTheory.HaarPi

theorem lintegral_pi_fin {E : Type*} [MeasurableSpace E] (n : ℕ) (μ : Measure E) [SigmaFinite μ]
    (f : Fin n → E → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : Fin n → E, ∏ i, f i (x i) ∂(Measure.pi fun _ => μ) = ∏ i, ∫⁻ t, f i t ∂μ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).symm
    rw [← hp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
    have hrw : ∀ z : E × (Fin n → E),
        ∏ i, f i ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E) 0).symm z i) =
          f 0 z.1 * ∏ i : Fin n, f i.succ (z.2 i) := by
      intro z
      rw [Fin.prod_univ_succ]
      simp [MeasurableEquiv.piFinSuccAbove_symm_apply]
    simp_rw [hrw]
    rw [lintegral_prod_mul (f := f 0) (g := fun y : Fin n → E => ∏ i : Fin n, f i.succ (y i))
      (hf 0).aemeasurable, ih (fun i => f i.succ) (fun i => hf i.succ),
      Fin.prod_univ_succ]
    · exact (Finset.measurable_prod _ fun i _ =>
        (hf i.succ).comp (measurable_pi_apply i)).aemeasurable

theorem lintegral_pi_prod {ι E : Type*} [Fintype ι] [MeasurableSpace E] (μ : Measure E) [SigmaFinite μ]
    (f : ι → E → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : ι → E, ∏ i, f i (x i) ∂(Measure.pi fun _ => μ) = ∏ i, ∫⁻ t, f i t ∂μ := by
  set e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have hp := measurePreserving_piCongrLeft (fun _ : ι => μ) e
  rw [← hp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
  have hrw : ∀ y : Fin (Fintype.card ι) → E,
      ∏ i, f i (MeasurableEquiv.piCongrLeft (fun _ : ι => E) e y i) = ∏ k, f (e k) (y k) := by
    intro y
    rw [← e.prod_comp]
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  simp_rw [hrw]
  rw [lintegral_pi_fin _ μ (fun k => f (e k)) (fun k => hf (e k))]
  exact e.prod_comp (fun i => ∫⁻ t, f i t ∂μ)

theorem pi_withDensity {ι E : Type*} [Fintype ι] [MeasurableSpace E] (μ : Measure E) [SigmaFinite μ]
    (f : E → ℝ≥0∞) (hf : Measurable f) [SigmaFinite (μ.withDensity f)] :
    (Measure.pi fun _ : ι => μ.withDensity f) =
      (Measure.pi fun _ : ι => μ).withDensity fun x => ∏ i, f (x i) := by
  refine Measure.pi_eq (μ := fun _ : ι => μ.withDensity f) fun s hs => ?_
  have hind : ∀ x : ι → E, (Set.univ.pi s).indicator (fun x => ∏ i, f (x i)) x =
      ∏ i, (s i).indicator f (x i) := by
    intro x
    by_cases hx : x ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hx]
      exact Finset.prod_congr rfl fun i _ =>
        (Set.indicator_of_mem (Set.mem_univ_pi.1 hx i) f).symm
    · rw [Set.indicator_of_notMem hx]
      simp only [Set.mem_univ_pi, not_forall] at hx
      obtain ⟨i, hi⟩ := hx
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi f)).symm
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  simp_rw [hind]
  rw [lintegral_pi_prod μ (fun i => (s i).indicator f) (fun i => hf.indicator (hs i))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [lintegral_indicator (hs i), withDensity_apply _ (hs i)]

theorem haarGL_eq_pi : ∀ (E : Type) [Field E] [NumberField E] (j : ℕ), haarGL E j = (Measure.pi fun _ : InfinitePlace E => haarLoc j : Measure (InfinitePlace E → Fin j → Fin j → ℂ)) := by
  intro E _ _ j
  set F : (Fin j → Fin j → ℂ) → ℝ≥0∞ := fun x => ENNReal.ofReal ((‖(Matrix.of x).det‖ ^ 2)⁻¹ ^ j)
  have hF : Measurable F := by
    have hc : Continuous fun x : Fin j → Fin j → ℂ => (Matrix.of x).det := continuous_id.matrix_det
    exact ENNReal.measurable_ofReal.comp
      (((hc.norm.pow 2).measurable.inv).pow_const j)
  have : SigmaFinite ((volume : Measure (Fin j → Fin j → ℂ)).withDensity F) :=
    inferInstanceAs (SigmaFinite (haarLoc j))
  have hloc : haarLoc j = (volume : Measure (Fin j → Fin j → ℂ)).withDensity F := rfl
  simp only [hloc]
  rw [pi_withDensity (ι := InfinitePlace E) volume F hF, ← volume_pi, haarGL]
  congr 1
  funext x
  rw [← ENNReal.ofReal_prod_of_nonneg fun w _ => by positivity]
  congr 1
  unfold MatInf at x
  unfold detNorm
  rw [← Finset.prod_inv_distrib, ← Finset.prod_pow]

end GlobalTheory.HaarPi
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InfiniteGLHaarMeasureEqPiLocalStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.infiniteGLHaarMeasure_eq_pi_local : ∀ (E : Type) [Field E] [NumberField E] (j : ℕ), haarGL E j = (Measure.pi fun _ : InfinitePlace E => haarLoc j : Measure (InfinitePlace E → Fin j → Fin j → ℂ)) := by
  first | exact @GlobalTheory.HaarPi.haarGL_eq_pi | exact GlobalTheory.HaarPi.haarGL_eq_pi | (intros; apply GlobalTheory.HaarPi.haarGL_eq_pi <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPlacesMatchIsomorphicCMInstances
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPlacesMatchIsomorphicCMInstances
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

namespace GlobalTheory.LeviIso.Places

noncomputable def placeEquiv (I : AutInst) : InfinitePlace I.F ≃ InfinitePlace I.E :=
  (Equiv.ofBijective _ (GlobalTheory.Count.FrameMajorant.comap_bijective I)).symm

theorem placeEquiv_apply (I : AutInst) (v : InfinitePlace I.F) :
    placeEquiv I v = InfinitePlace.mk (I.φ v) := by
  have h : (I.φ v).comp (algebraMap I.F I.E) = v.embedding := RingHom.ext (I.φ_over v)
  rw [placeEquiv, Equiv.symm_apply_eq]
  show v = (InfinitePlace.mk (I.φ v)).comap (algebraMap I.F I.E)
  rw [InfinitePlace.comap_mk, h, InfinitePlace.mk_embedding]

noncomputable def comapEquiv {K L : Type} [Field K] [Field L] (e : K ≃+* L) :
    InfinitePlace L ≃ InfinitePlace K where
  toFun w := w.comap (e : K →+* L)
  invFun w := w.comap (e.symm : L →+* K)
  left_inv w := by
    beta_reduce; rw [← InfinitePlace.comap_comp]; simp [InfinitePlace.comap_id]
  right_inv w := by
    beta_reduce; rw [← InfinitePlace.comap_comp]; simp [InfinitePlace.comap_id]

theorem exists_twist {K : Type} [Field K] (φ ψ : K →+* ℂ)
    (h : InfinitePlace.mk φ = InfinitePlace.mk ψ) :
    ∃ τ : ℂ →+* ℂ, (τ = RingHom.id ℂ ∨ τ = starRingEnd ℂ) ∧ ∀ y, φ y = τ (ψ y) := by
  rcases InfinitePlace.mk_eq_iff.mp h with h' | h'
  · exact ⟨RingHom.id ℂ, Or.inl rfl, fun y => by rw [h', RingHom.id_apply]⟩
  · refine ⟨starRingEnd ℂ, Or.inr rfl, fun y => ?_⟩
    rw [← h', ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]

theorem places_match : ∀ (I I₀ : AutInst) (e : I₀.E ≃+* I.E), (∀ y, e (star y) = star (e y)) → ∃ (β : InfinitePlace I.F ≃ InfinitePlace I.E) (σ : InfinitePlace I.F ≃ InfinitePlace I₀.F) (τ τ₀ : InfinitePlace I.F → (ℂ →+* ℂ)), (∀ v, τ v = RingHom.id ℂ ∨ τ v = starRingEnd ℂ) ∧ (∀ v, τ₀ v = RingHom.id ℂ ∨ τ₀ v = starRingEnd ℂ) ∧ (∀ v y, I.φ v y = τ v ((β v).embedding y)) ∧ ∀ v y, I.φ v (e y) = τ₀ v (I₀.φ (σ v) y) := by
  intro I I₀ e _

  let σ : InfinitePlace I.F ≃ InfinitePlace I₀.F :=
    (placeEquiv I).trans ((comapEquiv e).trans (placeEquiv I₀).symm)
  have h1 : ∀ v : InfinitePlace I.F, ∃ τ : ℂ →+* ℂ, (τ = RingHom.id ℂ ∨ τ = starRingEnd ℂ) ∧
      ∀ y, I.φ v y = τ ((placeEquiv I v).embedding y) := fun v =>
    exists_twist _ _ (by rw [InfinitePlace.mk_embedding, placeEquiv_apply])
  have h2 : ∀ v : InfinitePlace I.F, ∃ τ : ℂ →+* ℂ, (τ = RingHom.id ℂ ∨ τ = starRingEnd ℂ) ∧
      ∀ y, I.φ v (e y) = τ (I₀.φ (σ v) y) := by
    intro v
    refine exists_twist ((I.φ v).comp (e : I₀.E →+* I.E)) (I₀.φ (σ v)) ?_
    rw [← placeEquiv_apply]
    simp only [σ, Equiv.trans_apply, Equiv.apply_symm_apply]
    rw [placeEquiv_apply]
    show _ = (InfinitePlace.mk (I.φ v)).comap (e : I₀.E →+* I.E)
    rw [InfinitePlace.comap_mk]
  choose τ hτ using h1
  choose τ₀ hτ₀ using h2
  exact ⟨placeEquiv I, σ, τ, τ₀, fun v => (hτ v).1, fun v => (hτ₀ v).1, fun v => (hτ v).2,
    fun v => (hτ₀ v).2⟩

end GlobalTheory.LeviIso.Places
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPlacesMatchIsomorphicCMInstancesStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realPlaces_match_isomorphic_CM_instances : ∀ (I I₀ : AutInst) (e : I₀.E ≃+* I.E), (∀ y, e (star y) = star (e y)) → ∃ (β : InfinitePlace I.F ≃ InfinitePlace I.E) (σ : InfinitePlace I.F ≃ InfinitePlace I₀.F) (τ τ₀ : InfinitePlace I.F → (ℂ →+* ℂ)), (∀ v, τ v = RingHom.id ℂ ∨ τ v = starRingEnd ℂ) ∧ (∀ v, τ₀ v = RingHom.id ℂ ∨ τ₀ v = starRingEnd ℂ) ∧ (∀ v y, I.φ v y = τ v ((β v).embedding y)) ∧ ∀ v y, I.φ v (e y) = τ₀ v (I₀.φ (σ v) y) := by
  first | exact @GlobalTheory.LeviIso.Places.places_match | exact GlobalTheory.LeviIso.Places.places_match | (intros; apply GlobalTheory.LeviIso.Places.places_match <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnBlocksSpanFlagFlagAdaptedLatticeBasis
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnBlocksSpanFlagFlagAdaptedLatticeBasis
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

namespace GlobalTheory.LeviIso

theorem eq_top_of_map_lattice_mem {E : Type} [Field E] [NumberField E] (φ : E →+* ℂ) {m : ℕ}
    (Λ : Submodule (𝓞 E) (Fin m → E)) (hΛ : Submodule.span E (Λ : Set (Fin m → E)) = ⊤)
    (W : Submodule ℂ (Fin m → ℂ)) (h : ∀ t ∈ Λ, (fun l => φ (t l)) ∈ W) : W = ⊤ := by

  have hall : ∀ x : Fin m → E, (fun l => φ (x l)) ∈ W := by
    intro x
    have hx : x ∈ Submodule.span E (Λ : Set (Fin m → E)) := by rw [hΛ]; trivial
    induction hx using Submodule.span_induction with
    | mem t ht => exact h t ht
    | zero =>
      have e1 : (fun l => φ ((0 : Fin m → E) l)) = 0 := by
        funext l; simp
      rw [e1]; exact W.zero_mem
    | add x y _ _ hx hy =>
      have e1 : (fun l => φ ((x + y) l)) = (fun l => φ (x l)) + (fun l => φ (y l)) := by
        funext l; simp
      rw [e1]; exact W.add_mem hx hy
    | smul c x _ hx =>
      have e1 : (fun l => φ ((c • x) l)) = φ c • (fun l => φ (x l)) := by
        funext l; simp
      rw [e1]; exact W.smul_mem _ hx

  have key : ∀ l, (Pi.single l (1 : ℂ) : Fin m → ℂ) ∈ W := by
    intro l
    convert hall (Pi.single l 1) using 1
    funext l'
    by_cases hl : l' = l
    · subst hl; simp
    · simp [hl]
  rw [eq_top_iff]
  intro w _
  have hw : w = ∑ l, w l • (Pi.single l (1 : ℂ) : Fin m → ℂ) := by
    funext l'; simp [Finset.sum_apply, Pi.single_apply]
  rw [hw]
  exact W.sum_mem fun l _ => W.smul_mem _ (key l)

theorem spansFlag_flagAt : ∀ (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (Λ : ∀ i, Submodule (𝓞 I.E) (Fin (j i) → I.E)) (x₀ : I₀.Gf) (T T' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E) (T₀ : Matrix (Fin I.n) (Fin I₀.n) I.E), IsAdapted I I₀ e xf j S Λ x₀ T T' T₀ → ∀ v, SpansFlag (fun i => (I.P v)⁻¹ * (T i).map (I.φ v)) (flagAt I S v) := by
  intro I I₀ e xf a j S Λ x₀ T T' T₀ hA v k y
  obtain ⟨-, -, -, hiso, hpair, -, hlam, hS⟩ := hA

  have hspan (i : Fin a) : Submodule.span I.E (Λ i : Set (Fin (j i) → I.E)) = ⊤ := by
    -- The dual frame projects the ambient lattice onto the i-th coordinate block.
    let p := ((T' i)ᴴ * I.J).mulVecLin
    have hJ : I.Jᴴ = I.J := by
      ext r s
      simpa [Formalism.UG.cT, starRingEnd_apply] using congrFun (congrFun I.J_herm r) s
    have hswap (b : Fin a) : (T' i)ᴴ * I.J * T b = ((T b)ᴴ * I.J * T' i)ᴴ := by
      simp [hJ, Matrix.mul_assoc]
    have hpT (x : Fin (j i) → I.E) : p (T i *ᵥ x) = x := by
      simp only [p, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
      rw [hswap, (hpair i).1, Matrix.conjTranspose_one, Matrix.one_mulVec]
    have hple : Submodule.span I.E (lamX I (1, xf) : Set (Fin I.n → I.E)) ≤
        (Submodule.span I.E (Λ i : Set (Fin (j i) → I.E))).comap p := by
      refine Submodule.span_le.2 fun z hz => ?_
      obtain ⟨u, u', z₀, hu, -, -, rfl⟩ := (hlam z).1 hz
      have hsum : p (∑ b, T b *ᵥ u b) = u i := by
        rw [map_sum, Finset.sum_eq_single i, hpT]
        · intro b _ hbi
          simp only [p, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
          rw [hswap, (hiso b i).2.2 hbi, Matrix.conjTranspose_zero, Matrix.zero_mulVec]
        · simp
      have hsum' : p (∑ b, T' b *ᵥ u' b) = 0 := by
        rw [map_sum]
        refine Finset.sum_eq_zero fun b _ => ?_
        simp only [p, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
        rw [(hiso i b).2.1, Matrix.zero_mulVec]
      have hp₀ (x : Fin I₀.n → I.E) : p (T₀ *ᵥ x) = 0 := by
        simp only [p, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
        rw [(hpair i).2.2, Matrix.zero_mulVec]
      change p _ ∈ Submodule.span I.E (Λ i : Set (Fin (j i) → I.E))
      rw [map_add, map_add, hsum, hsum', hp₀, add_zero, add_zero]
      exact Submodule.subset_span (hu i)
    rw [(GlobalTheory.PointLattice.lamX_selfDual I (1, xf)).2.2.1] at hple
    refine eq_top_iff.2 fun x _ => ?_
    have hx := hple (Submodule.mem_top (x := T i *ᵥ x))
    rwa [Submodule.mem_comap, hpT] at hx

  have himg : ∀ u : ∀ i, Fin (j i) → I.E,
      ((I.P v)⁻¹ *ᵥ fun l => I.φ v ((∑ i, T i *ᵥ u i) l)) =
        ∑ i, ((I.P v)⁻¹ * (T i).map (I.φ v)) *ᵥ (fun l => I.φ v (u i l)) := by
    intro u
    have e1 : (fun l => I.φ v ((∑ i, T i *ᵥ u i) l)) =
        ∑ i, (T i).map (I.φ v) *ᵥ (fun l => I.φ v (u i l)) := by
      funext l
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Finset.sum_apply, map_sum, RingHom.map_mulVec, Function.comp_def]
    rw [e1, Matrix.mulVec_sum]
    exact Finset.sum_congr rfl fun i _ => Matrix.mulVec_mulVec _ _ _
  constructor
  · intro hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, hz, rfl⟩ := hx
      obtain ⟨u, -, hk, rfl⟩ := (hS k z).1 hz
      refine ⟨fun i l => I.φ v (u i l), fun i hi => ?_, himg u⟩
      funext l
      simp [hk i hi]
    | zero => exact ⟨0, fun _ _ => rfl, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨u, hu, rfl⟩ := hx
      obtain ⟨u', hu', rfl⟩ := hy
      refine ⟨u + u', fun i hi => by simp [hu i hi, hu' i hi], ?_⟩
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => (Matrix.mulVec_add _ _ _).symm
    | smul c x _ hx =>
      obtain ⟨u, hu, rfl⟩ := hx
      refine ⟨c • u, fun i hi => by simp [hu i hi], ?_⟩
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => (Matrix.mulVec_smul _ _ _).symm
  · rintro ⟨u, hu, rfl⟩
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hik : i.castSucc < k
    · have htop := eq_top_of_map_lattice_mem (I.φ v) (Λ i) (hspan i)
        ((flagAt I S v k).comap (Matrix.mulVecLin ((I.P v)⁻¹ * (T i).map (I.φ v)))) (by
          intro t ht
          rw [Submodule.mem_comap, Matrix.mulVecLin_apply]
          let w : ∀ i', Fin (j i') → I.E := Pi.single i t
          have hw1 : ∀ i', w i' ∈ Λ i' := by
            intro i'
            by_cases h' : i' = i
            · subst h'; simpa [w] using ht
            · simp [w, Pi.single_eq_of_ne h']
          have hw2 : ∀ i' : Fin a, ¬ i'.castSucc < k → w i' = 0 := by
            intro i' hi'
            have h' : i' ≠ i := by rintro rfl; exact hi' hik
            simp [w, Pi.single_eq_of_ne h']
          have hz : (∑ i', T i' *ᵥ w i') ∈ S k := (hS k _).2 ⟨w, hw1, hw2, rfl⟩
          have hmem := Submodule.subset_span (R := ℂ) (Set.mem_image_of_mem
            (fun y : Fin I.n → I.E => (I.P v)⁻¹ *ᵥ fun l => I.φ v (y l)) hz)
          have hsum := himg w
          rw [hsum, Finset.sum_eq_single i] at hmem
          · simp [w] at hmem
            exact hmem
          · intro i' _ h'
            simp [w, Pi.single_eq_of_ne h']
            exact Matrix.mulVec_zero _
          · simp)
      have : u i ∈ (flagAt I S v k).comap (Matrix.mulVecLin ((I.P v)⁻¹ * (T i).map (I.φ v))) := by
        rw [htop]; trivial
      simpa [Submodule.mem_comap, Matrix.mulVecLin_apply] using this
    · simp [hu i hik]

end GlobalTheory.LeviIso
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnBlocksSpanFlagFlagAdaptedLatticeBasisStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnBlocksSpanFlag_flagAdaptedLatticeBasis : ∀ (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (Λ : ∀ i, Submodule (𝓞 I.E) (Fin (j i) → I.E)) (x₀ : I₀.Gf) (T T' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E) (T₀ : Matrix (Fin I.n) (Fin I₀.n) I.E), IsAdapted I I₀ e xf j S Λ x₀ T T' T₀ → ∀ v, SpansFlag (fun i => (I.P v)⁻¹ * (T i).map (I.φ v)) (flagAt I S v) := by
  first | exact @GlobalTheory.LeviIso.spansFlag_flagAt | exact GlobalTheory.LeviIso.spansFlag_flagAt | (intros; apply GlobalTheory.LeviIso.spansFlag_flagAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SizeQSaturatedIsotropicFlagPos
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SizeQSaturatedIsotropicFlagPos
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

namespace GlobalTheory.LeviIso

theorem satIn_of_trace (I : AutInst) (x : I.GA) (S : Submodule (𝓞 I.E) (Fin I.n → I.E))
    (h : ∀ y, y ∈ S ↔ y ∈ lamX I x ∧ y ∈ Submodule.span I.E (S : Set (Fin I.n → I.E))) :
    GlobalTheory.IndefiniteRowSideFullHecke.SaturatedPerpDuality.SatIn I x S := by
  have := GlobalTheory.StepDualityCompare.totallyComplex I

  obtain ⟨q, hq⟩ := Submodule.exists_isCompl (Submodule.span I.E (S : Set (Fin I.n → I.E)))
  let φ : (Fin I.n → I.E) →ₗ[I.E] (Fin I.n → I.E) := q.subtype ∘ₗ Submodule.linearProjOfIsCompl q _ hq.symm
  have hker : LinearMap.ker φ = Submodule.span I.E (S : Set (Fin I.n → I.E)) := by
    rw [LinearMap.ker_comp_of_ker_eq_bot _ q.ker_subtype]
    exact Submodule.linearProjOfIsCompl_ker _
  have hX : ∀ v, IsUnit (frm I x v).det := GlobalTheory.StepDualityCompare.frm_det I x
  have hfg : (lamX I x).FG := (GlobalTheory.PointLattice.lamX_selfDual I x).2.1

  have hsat := (Formalism.HN.htImage I.E (Fin I.n → I.E) (Fin I.n) (Fin I.n → I.E) (Fin I.n) (bas I) (frm I x)
    (bas I) (frm I x) hX hX φ (lamX I x) hfg).1
  have hS : lamX I x ⊓ (LinearMap.ker φ).restrictScalars (𝓞 I.E) = S := by
    ext y
    rw [hker, Submodule.mem_inf, Submodule.restrictScalars_mem, h]
  rw [hS] at hsat
  exact hsat

theorem sizeQ_flag_pos : ∀ (I : AutInst) (x : I.GA) (a : ℕ) (j : Fin a → ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)), IsSatFlag I (lamX I x) j S → ∀ i : Fin a, 0 < Formalism.HN.sizeQ (bas I) (frm I x) (S i.succ) (S i.castSucc) := by
  intro I x a j S hS i
  obtain ⟨-, hmono, -, htr, -⟩ := hS
  have hfg : (lamX I x).FG := (GlobalTheory.PointLattice.lamX_selfDual I x).2.1

  have hsat : GlobalTheory.IndefiniteRowSideFullHecke.SaturatedPerpDuality.SatIn I x (S i.castSucc) := satIn_of_trace I x _ (htr i.castSucc)
  have hle : S i.succ ≤ lamX I x := fun y hy => ((htr i.succ y).1 hy).1
  have hmn : S i.castSucc ≤ S i.succ := hmono (Fin.castSucc_le_succ i)
  have hpos := GlobalTheory.StepDualityCompare.htQ_pos I x hfg _ _ hsat hle hmn
  unfold Formalism.HN.sizeQ
  exact Real.rpow_pos_of_pos hpos _

end GlobalTheory.LeviIso
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SizeQSaturatedIsotropicFlagPosStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sizeQ_saturatedIsotropicFlag_pos : ∀ (I : AutInst) (x : I.GA) (a : ℕ) (j : Fin a → ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)), IsSatFlag I (lamX I x) j S → ∀ i : Fin a, 0 < Formalism.HN.sizeQ (bas I) (frm I x) (S i.succ) (S i.castSucc) := by
  first | exact @GlobalTheory.LeviIso.sizeQ_flag_pos | exact GlobalTheory.LeviIso.sizeQ_flag_pos | (intros; apply GlobalTheory.LeviIso.sizeQ_flag_pos <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagLeviRealPlacesProductMeasure
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase
open Formalism.REAL (Jm UJ muG)

noncomputable section

namespace GlobalTheory.LeviIso

theorem detNorm_pos_iff {E : Type} [Field E] [NumberField E] {j : ℕ} (x : MatInf E j) :
    0 < detNorm E j x ↔ ∀ w, (Matrix.of (x w)).det ≠ 0 := by
  unfold detNorm
  constructor
  · intro h w hw
    rw [Finset.prod_eq_zero (Finset.mem_univ w) (by rw [hw]; simp)] at h
    exact lt_irrefl _ h
  · intro h
    exact Finset.prod_pos fun w _ => pow_pos (norm_pos_iff.2 (h w)) 2

theorem gram_place (I : AutInst) (v : InfinitePlace I.F) {p q : Type} (X : Matrix (Fin I.n) p I.E)
    (Y : Matrix (Fin I.n) q I.E) :
    ((I.P v)⁻¹ * X.map (I.φ v))ᴴ * Jm (I.ε v) * ((I.P v)⁻¹ * Y.map (I.φ v)) = (Xᴴ * I.J * Y).map (I.φ v) := by
  have hP : I.P v * (I.P v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v))
  have hX : (X.map (I.φ v))ᴴ = Xᴴ.map (I.φ v) := by
    ext r s
    exact (I.cm.cmUnram.2.1 (I.φ v) (X s r)).symm
  rw [← I.P_spec v, Matrix.map_mul, Matrix.map_mul, ← hX]
  calc _ = (I.P v * (I.P v)⁻¹ * X.map (I.φ v))ᴴ * I.J.map (I.φ v) * (I.P v * (I.P v)⁻¹ * Y.map (I.φ v)) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [hP, Matrix.one_mul, Matrix.one_mul]

theorem conjT_map {τ : ℂ →+* ℂ} (hτ : τ = RingHom.id ℂ ∨ τ = starRingEnd ℂ) {p q : Type} (X : Matrix p q ℂ) :
    (X.map τ)ᴴ = Xᴴ.map τ := by
  rcases hτ with rfl | rfl <;> ext r s <;> simp

theorem Jm_map {n : ℕ} (ε : Fin n → Bool) (τ : ℂ →+* ℂ) : (Jm ε).map τ = Jm ε := by
  ext r s
  simp only [Jm, Matrix.map_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem inv_map {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P) (τ : ℂ →+* ℂ) :
    P.map τ * P⁻¹.map τ = 1 := by
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)]
  simp

theorem exists_charts (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ)
    (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (Λ : ∀ i, Submodule (𝓞 I.E) (Fin (j i) → I.E))
    (x₀ : I₀.Gf) (T T' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E) (T₀ : Matrix (Fin I.n) (Fin I₀.n) I.E)
    (hj : ∀ i, 1 ≤ j i) (h : IsAdapted I I₀ e xf j S Λ x₀ T T' T₀) (v : InfinitePlace I.F)
    (v₀ : InfinitePlace I₀.F) (τ τ₀ : ℂ →+* ℂ) (hτ : τ = RingHom.id ℂ ∨ τ = starRingEnd ℂ)
    (hτ₀ : τ₀ = RingHom.id ℂ ∨ τ₀ = starRingEnd ℂ) (hv : ∀ y, I.φ v (e y) = τ₀ (I₀.φ v₀ y)) :
    ∃ θ, IsLeviChart (I.ε v) (I₀.ε v₀) (flagAt I S v) (fun i => (I.P v)⁻¹ * (T i).map (I.φ v))
      ((I.P v)⁻¹ * T₀.map (I.φ v) * (I₀.P v₀).map τ₀) τ τ₀ θ := by
  have hsat := GlobalTheory.T.isSaturatedIsotropicFlag_of_adaptedBasis I I₀ e xf a j S Λ x₀ T T' T₀ hj h
  have hsp := GlobalTheory.T.columnBlocksSpanFlag_flagAdaptedLatticeBasis I I₀ e xf a j S Λ x₀ T T' T₀ h v
  obtain ⟨-, hn, -, h1, h2, h3, -, -⟩ := h
  have hJ : I.Jᴴ = I.J := I.J_herm
  have sw : ∀ i k, (T' i)ᴴ * I.J * T k = ((T k)ᴴ * I.J * T' i)ᴴ := by
    intro i k
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJ, Matrix.mul_assoc]
  refine GlobalTheory.T.complementary_block_unitary_forms _ _ a j _ _ _ _ (fun i => ((I.P v)⁻¹ * (T' i).map (I.φ v))ᴴ * Jm (I.ε v)) _ τ τ₀ hτ hτ₀ hn
    (fun i => ?_) (fun i k hik => ?_) (fun i k => ?_) (fun i => ?_) ?_ hsp (GlobalTheory.T.isTotallyIsotropicFlag_complexified_saturatedFlag I _ a j S hsat v)
  · rw [gram_place, sw, (h2 i).1]
    simp
  · rw [gram_place, sw, (h1 k i).2.2 hik.symm]
    simp
  · rw [gram_place, (h1 i k).1]
    simp
  · rw [← Matrix.mul_assoc, gram_place, (h2 i).2.1]
    simp
  · have e1 : (I₀.J.map e).map (I.φ v) = (I₀.J.map (I₀.φ v₀)).map τ₀ := by
      ext r s
      exact hv _
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (Jm _),
      ← Matrix.mul_assoc _ _ ((I₀.P v₀).map τ₀), ← Matrix.mul_assoc _ (Jm _), gram_place, h3, e1,
      conjT_map hτ₀, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.mul_assoc, I₀.P_spec, Jm_map]

theorem size_solve {f k : ℕ} (hf : 1 ≤ f) (hk : 1 ≤ k) {s t D : ℝ} (hs : 0 < s) (ht : 0 < t) (hD : 0 < D)
    (h : t ^ f = s ^ f * D ^ (-(1 : ℝ) / (2 * k))) :
    t = (D / s ^ (2 * f * k)) ^ (-(1 / (2 * (f : ℝ) * k))) := by
  have hf' : (f : ℝ) ≠ 0 := by positivity
  have hk' : (k : ℝ) ≠ 0 := by positivity
  have h1 := congrArg Real.log h
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_rpow hD] at h1
  apply Real.log_injOn_pos ht (Real.rpow_pos_of_pos (by positivity) _)
  rw [Real.log_rpow (by positivity), Real.log_div hD.ne' (by positivity), Real.log_pow]
  push_cast
  field_simp
  field_simp at h1
  linarith

theorem ae_detNorm_pos (E : Type) [Field E] [NumberField E] {a : ℕ} (j : Fin a → ℕ) :
    ∀ᵐ z ∂(Measure.pi fun i => haarGL E (j i)), ∀ i, 0 < detNorm E (j i) (z i) := by
  have hσ : ∀ i, SigmaFinite (haarGL E (j i)) := fun i => by
    rw [GlobalTheory.T.infiniteGLHaarMeasure_eq_pi_local]
    exact inferInstanceAs (SigmaFinite (Measure.pi fun _ : InfinitePlace E => haarLoc (j i)))
  have h1 : ∀ i, ∀ᵐ x ∂(haarGL E (j i)), 0 < detNorm E (j i) x := by
    intro i
    rw [GlobalTheory.T.infiniteGLHaarMeasure_eq_pi_local]
    have h2 : ∀ᵐ x ∂(Measure.pi fun _ : InfinitePlace E => haarLoc (j i)), ∀ w, (Matrix.of (x w)).det ≠ 0 := by
      refine ae_all_iff.2 fun w => ?_
      have h3 : ∀ᵐ y ∂(haarLoc (j i)), (Matrix.of y).det ≠ 0 := by
        rw [ae_iff]
        simpa using (GlobalTheory.T.haarComplexGLMatrices_conj_and_singular_null (j i)).2
      exact (Measure.quasiMeasurePreserving_eval (fun _ : InfinitePlace E => haarLoc (j i)) w).ae h3
    exact h2.mono fun x hx => (detNorm_pos_iff x).2 hx
  exact ae_all_iff.2 fun i => (Measure.quasiMeasurePreserving_eval (fun i => haarGL E (j i)) i).ae (h1 i)

theorem levi_product : ∀ (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (Λ : ∀ i, Submodule (𝓞 I.E) (Fin (j i) → I.E)) (x₀ : I₀.Gf) (T T' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E) (T₀ : Matrix (Fin I.n) (Fin I₀.n) I.E), (∀ i, 1 ≤ j i) → IsAdapted I I₀ e xf j S Λ x₀ T T' T₀ → ∀ (μM : ∀ v, Measure (Formalism.REAL.UJ (I.ε v))) [∀ v, SigmaFinite (μM v)] (c₀ : InfinitePlace I₀.F → ℝ), (∀ v, IsGaugeSub (flagM (I.ε v) (flagAt I S v)) ((I.n - 2 * ∑ i, j i) ^ 2 + 2 * ∑ i, j i ^ 2) (μM v)) → IsGaugeAll I₀ c₀ → ∃ (Θ : (∀ i, MatInf I.E (j i)) × I₀.Ginf → I.Ginf) (κ : Fin a → ℝ), Measurable Θ ∧ (∀ i, 0 < κ i) ∧ (∀ m : I.Ginf, (∀ v, m v ∈ flagM (I.ε v) (flagAt I S v)) ↔ ∃ z : ((∀ i, MatInf I.E (j i)) × I₀.Ginf), (∀ i, 0 < detNorm I.E (j i) (z.1 i)) ∧ Θ z = m) ∧ (∀ z z' : ((∀ i, MatInf I.E (j i)) × I₀.Ginf), (∀ i, z.1 i ∈ autGL I.E (j i) (Λ i)) → z.2 ∈ latGroup I₀ x₀ → (∀ i, 0 < detNorm I.E (j i) (z'.1 i)) → ∃ γ ∈ leviGroup I xf S, γ * Θ z' = Θ (fun i => z.1 i * z'.1 i, z.2 * z'.2)) ∧ (∀ z : ((∀ i, MatInf I.E (j i)) × I₀.Ginf), (∀ i, 0 < detNorm I.E (j i) (z.1 i)) → ∀ i, sizesAt I xf S (Θ z) i = (detNorm I.E (j i) (z.1 i) / κ i) ^ (-(1 / (2 * (I.f : ℝ) * j i)))) ∧ (∀ z z' : ((∀ i, MatInf I.E (j i)) × I₀.Ginf), (∀ i, 0 < detNorm I.E (j i) (z.1 i)) → (∀ i, 0 < detNorm I.E (j i) (z'.1 i)) → Θ z = Θ z' → z = z') ∧ ∀ φ : I.Ginf → ENNReal, Measurable φ → ∫⁻ m, φ m ∂(Measure.pi μM) = (∏ i, ENNReal.ofReal (2 ^ (I.f * j i ^ 2))) * ENNReal.ofReal (∏ v, c₀ v) * ∫⁻ z₁ in {z₁ | ∀ i, 0 < detNorm I.E (j i) (z₁ i)}, ∫⁻ z₂, φ (Θ (z₁, z₂)) ∂(Measure.pi fun v => Formalism.REAL.muG (I₀.ε v)) ∂(Measure.pi fun i => haarGL I.E (j i)) := by
  intro I I₀ e xf a j S Λ x₀ T T' T₀ hj h μM _ c₀ hμ hc₀
  have hsat := GlobalTheory.T.isSaturatedIsotropicFlag_of_adaptedBasis I I₀ e xf a j S Λ x₀ T T' T₀ hj h
  obtain ⟨β, σ, τ, τ₀, hτ, hτ₀, hβ, hσ⟩ := GlobalTheory.T.realPlaces_match_isomorphic_CM_instances I I₀ e h.1
  choose θ hθ using fun v => exists_charts I I₀ e xf a j S Λ x₀ T T' T₀ hj h v (σ v) (τ v) (τ₀ v) (hτ v) (hτ₀ v)
    (hσ v)
  have hcard : Fintype.card (InfinitePlace I.F) = I.f := GlobalTheory.Count.FrameMajorant.card_places I
  have hf : 1 ≤ I.f := Module.finrank_pos
  let R : (∀ i, MatInf I.E (j i)) × I₀.Ginf →
      ∀ v : InfinitePlace I.F, (∀ i, Fin (j i) → Fin (j i) → ℂ) × UJ (I₀.ε (σ v)) :=
    fun z v => (fun i => z.1 i (β v), z.2 (σ v))
  have hR := GlobalTheory.T.measurePreserving_rearrange_pi_prod_measures _ _ _ β σ a (fun i => Fin (j i) → Fin (j i) → ℂ) (fun w => UJ (I₀.ε w))
    (fun i => haarLoc (j i)) (fun w => muG (I₀.ε w)) (fun i => 2 ^ (j i ^ 2)) c₀ (fun i => by positivity)
    (fun w => ((GlobalTheory.T.riemannianHaarGauge_whole_group _ _).1 _ (hc₀ w)).1.le)
  have hRm : Measurable R := hR.measurable
  have hΘ : Measurable fun (z : (∀ i, MatInf I.E (j i)) × I₀.Ginf) v => θ v (R z v) :=
    Measurable.of_eval fun v => (hθ v).1.comp ((measurable_pi_apply v).comp hRm)
  have hdet : ∀ z : (∀ i, MatInf I.E (j i)) × I₀.Ginf, (∀ i, 0 < detNorm I.E (j i) (z.1 i)) →
      ∀ v i, (Matrix.of ((R z v).1 i)).det ≠ 0 := fun z hz v i => (detNorm_pos_iff _).1 (hz i) (β v)
  have hM : ∀ z : (∀ i, MatInf I.E (j i)) × I₀.Ginf, (∀ i, 0 < detNorm I.E (j i) (z.1 i)) →
      ∀ v, θ v (R z v) ∈ flagM (I.ε v) (flagAt I S v) := fun z hz v =>
    ((hθ v).2.1 _).2 ⟨R z v, hdet z hz v, rfl⟩
  have hpos := fun g : I.Ginf => GlobalTheory.T.sizeQ_saturatedIsotropicFlag_pos I (g, xf) a j S hsat
  refine ⟨fun z v => θ v (R z v), fun i => sizesAt I xf S 1 i ^ (2 * I.f * j i), hΘ,
    fun i => pow_pos (hpos 1 i) _, fun m => ⟨fun hm => ?_, ?_⟩, fun z z' hz1 hz2 hz' => ?_, fun z hz i => ?_,
    fun z z' hz hz' hzz => ?_, fun φ hφ => ?_⟩
  · choose y hy1 hy2 using fun v => ((hθ v).2.1 (m v)).1 (hm v)
    refine ⟨(fun i w => (y (β.symm w)).1 i, Equiv.piCongrLeft (fun w => UJ (I₀.ε w)) σ fun v => (y v).2),
      fun i => (detNorm_pos_iff _).2 fun w => hy1 _ i, funext fun v => ?_⟩
    rw [← hy2 v]
    refine congrArg (θ v) (Prod.ext (funext fun i => ?_) ?_)
    · exact congrArg (fun u => (y u).1 i) (β.symm_apply_apply v)
    · exact Equiv.piCongrLeft_apply_apply (fun w => UJ (I₀.ε w)) σ (fun v => (y v).2) v
  · rintro ⟨z, hz, rfl⟩
    exact hM z hz
  · choose γ hγ1 hγ2 using hz1
    obtain ⟨g, hg, Γ, γ₀, g1, g2, g3, g4⟩ := GlobalTheory.T.exists_rational_flag_block_fixing_lattice I I₀ e xf a j S Λ x₀ T T' T₀ h γ hγ1 z.2 hz2
    have hz : ∀ i, 0 < detNorm I.E (j i) (z.1 i) := by
      intro i
      refine (detNorm_pos_iff _).2 fun w => ?_
      have : Matrix.of (z.1 i w) = (γ i : Matrix (Fin (j i)) (Fin (j i)) I.E).map w.embedding := by
        ext r s
        exact hγ2 i w r s
      rw [this]
      exact ((Matrix.isUnit_iff_isUnit_det _).1 ((γ i).isUnit.map w.embedding.mapMatrix)).ne_zero
    have hP : ∀ v, I.P v * (I.P v)⁻¹ = 1 := fun v =>
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v))
    have hact : ∀ (v) {p : Type} (X : Matrix (Fin I.n) p I.E),
        uMat (g v) * ((I.P v)⁻¹ * X.map (I.φ v)) = (I.P v)⁻¹ * (Γ * X).map (I.φ v) := by
      intro v p X
      rw [g1, Matrix.mul_assoc, ← Matrix.mul_assoc (I.P v), hP, Matrix.one_mul, Matrix.map_mul, Matrix.mul_assoc]
    have hA : ∀ v i, uMat (g v) * ((I.P v)⁻¹ * (T i).map (I.φ v)) =
        (I.P v)⁻¹ * (T i).map (I.φ v) * (Matrix.of ((R z v).1 i)).map (τ v) := by
      intro v i
      rw [hact, g3, Matrix.map_mul, Matrix.mul_assoc]
      congr 2
      ext r s
      exact (hβ v _).trans (congrArg (τ v) (hγ2 i (β v) r s).symm)
    have hA₀ : ∀ v, uMat (g v) * ((I.P v)⁻¹ * T₀.map (I.φ v) * (I₀.P (σ v)).map (τ₀ v)) =
        (I.P v)⁻¹ * T₀.map (I.φ v) * (I₀.P (σ v)).map (τ₀ v) * (uMat (R z v).2).map (τ₀ v) := by
      intro v
      have e1 : (γ₀.map e).map (I.φ v) = (γ₀.map (I₀.φ (σ v))).map (τ₀ v) := by
        ext r s
        exact hσ v _
      have e2 : uMat (R z v).2 = _ := g2 (σ v)
      rw [← Matrix.mul_assoc, hact, g4, Matrix.map_mul, e1, e2, Matrix.map_mul, Matrix.map_mul,
        Matrix.mul_assoc _ ((I₀.P (σ v)).map (τ₀ v)), ← Matrix.mul_assoc ((I₀.P (σ v)).map (τ₀ v)),
        ← Matrix.mul_assoc ((I₀.P (σ v)).map (τ₀ v)), inv_map _ (I₀.P_unit _), Matrix.one_mul]
      simp only [Matrix.mul_assoc]
    refine ⟨fun v => θ v (R z v), ⟨hM z hz, g, ⟨hg, fun v k y hy => ?_⟩, g * (fun v => θ v (R z v))⁻¹,
      fun v => ((hθ v).2.2.2.1 (R z v) (hdet z hz v)).2 (g v) (hA v) (hA₀ v), (inv_mul_cancel_right _ _).symm⟩,
      funext fun v => ((hθ v).2.2.1 (R z v) (R z' v) (hdet z hz v) (hdet z' hz' v)).1⟩
    have hsp := GlobalTheory.T.columnBlocksSpanFlag_flagAdaptedLatticeBasis I I₀ e xf a j S Λ x₀ T T' T₀ h v
    obtain ⟨u, hu, rfl⟩ := (hsp k y).1 hy
    refine (hsp k _).2 ⟨fun i => (Matrix.of ((R z v).1 i)).map (τ v) *ᵥ u i, fun i hi => ?_, ?_⟩
    · simp only [hu i hi, Matrix.mulVec_zero]
    · simp only [Matrix.mulVec_sum, Matrix.mulVec_mulVec, hA]
  · have h0 : ∀ v, uMat ((1 : I.Ginf) v) = 1 := fun v => rfl
    have h1 := GlobalTheory.T.gradedPieceSizes_unipotent_levi_compact_move I xf a j hj S hsat 1 (fun v => θ v (R z v)) 1
      (fun v => ⟨fun i y _ => by rw [h0]; simp, fun y _ => by rw [h0]; simp⟩) (hM z hz)
      (fun v => show (uMat ((1 : I.Ginf) v))ᴴ * uMat ((1 : I.Ginf) v) = 1 by rw [h0]; simp) i
    rw [one_mul, mul_one] at h1
    refine size_solve hf (hj i) (hpos 1 i) (hpos _ i) (hz i) (h1.trans ?_)
    congr 1
    simp only [fun v => ((hθ v).2.2.2.1 (R z v) (hdet z hz v)).1 i]
    have hj' : (j i : ℝ) ≠ 0 := by have := hj i; positivity
    rw [detNorm, ← Real.finsetProd_rpow _ _ (fun w _ => by positivity)]
    refine Fintype.prod_equiv β _ _ fun v => ?_
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
    congr 1
    push_cast
    field_simp
  · have h1 : ∀ v, R z v = R z' v := fun v =>
      ((hθ v).2.2.1 (R z v) (R z' v) (hdet z hz v) (hdet z' hz' v)).2 (congrFun hzz v)
    refine Prod.ext (funext fun i => funext fun w => ?_) (funext fun w => ?_)
    · obtain ⟨v, rfl⟩ := β.surjective w
      exact congrFun (congrArg Prod.fst (h1 v)) i
    · obtain ⟨v, rfl⟩ := σ.surjective w
      exact congrArg Prod.snd (h1 v)
  · have hd : I.n - 2 * ∑ i, j i = I₀.n := by rw [h.2.1]; omega
    rw [hd] at hμ
    have h1 := funext fun v => (hθ v).2.2.2.2 (μM v) (c₀ (σ v)) (hμ v) (hc₀ (σ v))
    have h2 := measurePreserving_pi _ μM (f := θ) fun v => ⟨(hθ v).1, (congrFun h1 v).symm⟩
    have h3 := (h2.comp hR).lintegral_comp hφ
    have h4 : (Measure.pi fun i => haarGL I.E (j i)).restrict {z₁ | ∀ i, 0 < detNorm I.E (j i) (z₁ i)} =
        Measure.pi fun i => haarGL I.E (j i) := Measure.restrict_eq_self_of_ae_mem (ae_detNorm_pos I.E j)
    rw [← h3, lintegral_smul_measure, h4, smul_eq_mul, hcard]
    simp only [GlobalTheory.T.infiniteGLHaarMeasure_eq_pi_local]
    congr 1
    · simp only [← pow_mul, mul_comm]
    · exact lintegral_prod _ (hφ.comp hΘ).aemeasurable

end GlobalTheory.LeviIso
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagLeviRealPlacesProductMeasureStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagLevi_realPlaces_product_measure : ∀ (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (Λ : ∀ i, Submodule (𝓞 I.E) (Fin (j i) → I.E)) (x₀ : I₀.Gf) (T T' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E) (T₀ : Matrix (Fin I.n) (Fin I₀.n) I.E), (∀ i, 1 ≤ j i) → IsAdapted I I₀ e xf j S Λ x₀ T T' T₀ → ∀ (μM : ∀ v, Measure (Formalism.REAL.UJ (I.ε v))) [∀ v, SigmaFinite (μM v)] (c₀ : InfinitePlace I₀.F → ℝ), (∀ v, IsGaugeSub (flagM (I.ε v) (flagAt I S v)) ((I.n - 2 * ∑ i, j i) ^ 2 + 2 * ∑ i, j i ^ 2) (μM v)) → IsGaugeAll I₀ c₀ → ∃ (Θ : (∀ i, MatInf I.E (j i)) × I₀.Ginf → I.Ginf) (κ : Fin a → ℝ), Measurable Θ ∧ (∀ i, 0 < κ i) ∧ (∀ m : I.Ginf, (∀ v, m v ∈ flagM (I.ε v) (flagAt I S v)) ↔ ∃ z : ((∀ i, MatInf I.E (j i)) × I₀.Ginf), (∀ i, 0 < detNorm I.E (j i) (z.1 i)) ∧ Θ z = m) ∧ (∀ z z' : ((∀ i, MatInf I.E (j i)) × I₀.Ginf), (∀ i, z.1 i ∈ autGL I.E (j i) (Λ i)) → z.2 ∈ latGroup I₀ x₀ → (∀ i, 0 < detNorm I.E (j i) (z'.1 i)) → ∃ γ ∈ leviGroup I xf S, γ * Θ z' = Θ (fun i => z.1 i * z'.1 i, z.2 * z'.2)) ∧ (∀ z : ((∀ i, MatInf I.E (j i)) × I₀.Ginf), (∀ i, 0 < detNorm I.E (j i) (z.1 i)) → ∀ i, sizesAt I xf S (Θ z) i = (detNorm I.E (j i) (z.1 i) / κ i) ^ (-(1 / (2 * (I.f : ℝ) * j i)))) ∧ (∀ z z' : ((∀ i, MatInf I.E (j i)) × I₀.Ginf), (∀ i, 0 < detNorm I.E (j i) (z.1 i)) → (∀ i, 0 < detNorm I.E (j i) (z'.1 i)) → Θ z = Θ z' → z = z') ∧ ∀ φ : I.Ginf → ENNReal, Measurable φ → ∫⁻ m, φ m ∂(Measure.pi μM) = (∏ i, ENNReal.ofReal (2 ^ (I.f * j i ^ 2))) * ENNReal.ofReal (∏ v, c₀ v) * ∫⁻ z₁ in {z₁ | ∀ i, 0 < detNorm I.E (j i) (z₁ i)}, ∫⁻ z₂, φ (Θ (z₁, z₂)) ∂(Measure.pi fun v => Formalism.REAL.muG (I₀.ε v)) ∂(Measure.pi fun i => haarGL I.E (j i)) := by
  first | exact @GlobalTheory.LeviIso.levi_product | exact GlobalTheory.LeviIso.levi_product | (intros; apply GlobalTheory.LeviIso.levi_product <;> assumption)
end
