module

public import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGap
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.IwaCore
public import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam

@[expose] public section

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.WordLengthBoundOfLinear
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.WordLengthBoundOfLinear
open Matrix Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm CompanionTheory.Bmu

noncomputable section

namespace GlobalTheory.CompanionTheory.BmuWordBd

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def lieSub {n : ℕ} (Hm : Mat n) : Submodule ℝ (Mat n) where
  carrier := {X | Lie Hm X}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, Lie] at *
    rw [conjTranspose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, ha, hb, add_zero]
  zero_mem' := by simp [Lie]
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_ofPred_eq, Lie] at *
    rw [conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, ha, smul_zero]

theorem exists_basis_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (S : Submodule ℝ E) :
    ∃ (N : ℕ) (b : Fin N → E) (κ : ℝ), 0 ≤ κ ∧ (∀ i, b i ∈ S) ∧
      ∀ X, X ∈ S → ∃ c : Fin N → ℝ, X = ∑ i, c i • b i ∧ ∀ i, |c i| ≤ κ * ‖X‖ := by
  let bS := Module.finBasis ℝ S
  let L : Fin (Module.finrank ℝ S) → (S →L[ℝ] ℝ) := fun i => LinearMap.toContinuousLinearMap (bS.coord i)
  refine ⟨Module.finrank ℝ S, fun i => (bS i : E), ∑ i, ‖L i‖,
    Finset.sum_nonneg (fun i _ => norm_nonneg _), fun i => (bS i).2, ?_⟩
  intro X hX
  refine ⟨fun i => bS.repr ⟨X, hX⟩ i, ?_, ?_⟩
  · calc X = ((⟨X, hX⟩ : S) : E) := rfl
      _ = ((∑ i, bS.repr ⟨X, hX⟩ i • bS i : S) : E) := by rw [bS.sum_repr]
      _ = ∑ i, bS.repr ⟨X, hX⟩ i • (bS i : E) := by simp only [Submodule.coe_sum, Submodule.coe_smul]
  · intro i
    have h1 : |bS.repr ⟨X, hX⟩ i| ≤ ‖L i‖ * ‖X‖ := by
      have := (L i).le_opNorm ⟨X, hX⟩
      simpa [L, Real.norm_eq_abs] using this
    have h2 : ‖L i‖ ≤ ∑ j, ‖L j‖ := Finset.single_le_sum (fun j _ => norm_nonneg (L j)) (Finset.mem_univ i)
    exact h1.trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))

theorem exists_basis {n : ℕ} (Hm : Mat n) :
    ∃ (N : ℕ) (b : Fin N → Mat n) (κ : ℝ), 0 ≤ κ ∧ (∀ i, Lie Hm (b i)) ∧
      ∀ X, Lie Hm X → ∃ c : Fin N → ℝ, X = ∑ i, c i • b i ∧ ∀ i, |c i| ≤ κ * ‖X‖ := by
  obtain ⟨N, b, κ, hκ, hb, hX⟩ := exists_basis_sub (lieSub Hm)
  exact ⟨N, b, κ, hκ, hb, fun X hXL => hX X hXL⟩

theorem dsW_sum {n : ℕ} {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] {G : Set (Mat n)}
    {σ : Mat n → (H →L[ℂ] H)} (h : RepOn G σ) {ι : Type*} (s : Finset ι) (v : ι → H)
    (hv : ∀ i, IsSm G σ (v i)) {W : List (Mat n)} (hW : LieW G W) :
    IsSm G σ (∑ i ∈ s, v i) ∧ dsW σ W (∑ i ∈ s, v i) = ∑ i ∈ s, dsW σ W (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ⟨IsSm.zero, by simpa using dsW_smul h (IsSm.zero (G := G) (σ := σ)) (0 : ℂ) hW⟩
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact ⟨(hv a).add ih.1, by rw [dsW_add h (hv a) ih.1 hW, ih.2]⟩

private theorem ex_mem_UH_of_lie {n : ℕ} {Hm X : Mat n} (hsq : Hm * Hm = 1) (hX : Lie Hm X) (t : ℝ) :
    ex X t ∈ Formalism.QuantumDeterminants.UH Hm := by
  have hinv : Hm⁻¹ = Hm := Matrix.inv_eq_right_inv hsq
  have hU : IsUnit Hm := ⟨⟨Hm, Hm, hsq, hsq⟩, rfl⟩
  have h1 : Xᴴ * Hm = -(Hm * X) := eq_neg_of_add_eq_zero_left hX
  have hXH : Xᴴ = Hm * (-X) * Hm := by
    calc Xᴴ = Xᴴ * Hm * Hm := by rw [mul_assoc, hsq, mul_one]
      _ = Hm * (-X) * Hm := by rw [h1, Matrix.mul_neg]
  have hconj : ((t : ℂ) • X)ᴴ = Hm * (-((t : ℂ) • X)) * Hm⁻¹ := by
    rw [Matrix.conjTranspose_smul, hXH, hinv]
    simp [Matrix.mul_smul, Matrix.smul_mul, Complex.conj_ofReal]
  show (NormedSpace.exp ((t : ℂ) • X))ᴴ * Hm * NormedSpace.exp ((t : ℂ) • X) = Hm
  rw [← Matrix.exp_conjTranspose, hconj, Matrix.exp_conj _ _ hU, hinv, mul_assoc (Hm * _) Hm Hm, hsq,
    mul_one, mul_assoc, ← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl ((t : ℂ) • X))),
    neg_add_cancel, NormedSpace.exp_zero, mul_one]

private theorem dsW_append' {n : ℕ} {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (σ : Mat n → (H →L[ℂ] H)) (P W : List (Mat n)) (v : H) :
    dsW σ (P ++ W) v = dsW σ P (dsW σ W v) := by
  show List.foldr (ds σ) v (P ++ W) = List.foldr (ds σ) (List.foldr (ds σ) v W) P
  exact List.foldr_append

theorem wordBd_of_dsLin : DsLin → WordBd := by
  intro hD
  unfold WordBd
  intro n Hm H _ _ _ σ hU w hw m
  have hrep : RepOn (Formalism.QuantumDeterminants.UH Hm) σ := hU.rep
  have hsq : Hm * Hm = 1 := hU.sq
  have hlie : ∀ W : List (Mat n), LieWd Hm W → LieW (Formalism.QuantumDeterminants.UH Hm) W :=
    fun W hW X hX t => ex_mem_UH_of_lie hsq (hW X hX) t
  obtain ⟨N, b, κ, hκ, hb, hc⟩ := exists_basis Hm
  have hexp : ∀ v, IsSm (Formalism.QuantumDeterminants.UH Hm) σ v → ∀ X, Lie Hm X →
      ∃ c : Fin N → ℝ, (∀ i, |c i| ≤ κ * ‖X‖) ∧ ds σ X v = ∑ i, (c i : ℂ) • ds σ (b i) v := by
    intro v hv X hX
    obtain ⟨Λ, hΛ⟩ := hD n Hm H σ hU v hv
    obtain ⟨c, hXc, hcb⟩ := hc X hX
    refine ⟨c, hcb, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hΛ X hX, hXc, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, ← hΛ (b i) (hb i), Complex.coe_smul]
  have hlb : ∀ i, LieWd Hm [b i] := by
    intro i Y hY
    rw [List.mem_singleton] at hY
    subst hY
    exact hb i
  have key : ∀ k : ℕ, ∀ P : List (Mat n), LieWd Hm P → ∃ C : ℝ, 0 ≤ C ∧
      ∀ W : List (Mat n), LieWd Hm W → W.length ≤ k →
        ‖dsW σ (P ++ W) w‖ ≤ C * (W.map (fun X => ‖X‖)).prod := by
    intro k
    induction k with
    | zero =>
      intro P _
      refine ⟨‖dsW σ P w‖, norm_nonneg _, fun W _ hW => ?_⟩
      have hW0 : W = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hW)
      subst hW0
      simp
    | succ k ih =>
      intro P hP
      have hPb : ∀ i, LieWd Hm (P ++ [b i]) := by
        intro i Y hY
        rcases List.mem_append.1 hY with h | h
        · exact hP Y h
        · exact hlb i Y h
      choose C hC0 hC using fun i : Fin N => ih (P ++ [b i]) (hPb i)
      refine ⟨max ‖dsW σ P w‖ (κ * ∑ i, C i), le_max_of_le_left (norm_nonneg _), ?_⟩
      intro W hW hlen
      cases W with
      | nil =>
        simp only [List.append_nil, List.map_nil, List.prod_nil, mul_one]
        exact le_max_left _ _
      | cons X W' =>
        have hX : Lie Hm X := hW X List.mem_cons_self
        have hW' : LieWd Hm W' := fun Y hY => hW Y (List.mem_cons_of_mem _ hY)
        have hlen' : W'.length ≤ k := by simpa using hlen
        have hv : IsSm (Formalism.QuantumDeterminants.UH Hm) σ (dsW σ W' w) := hw.dsW hrep (hlie W' hW')
        obtain ⟨c, hcb, hds⟩ := hexp _ hv X hX
        have hsm : ∀ i, IsSm (Formalism.QuantumDeterminants.UH Hm) σ (ds σ (b i) (dsW σ W' w)) :=
          fun i => hv.dsW hrep (hlie [b i] (hlb i))
        have heq : dsW σ (P ++ X :: W') w = ∑ i, (c i : ℂ) • dsW σ ((P ++ [b i]) ++ W') w := by
          rw [dsW_append', dsW_cons, hds,
            (dsW_sum hrep Finset.univ _ (fun i => (hsm i).smul (c i : ℂ)) (hlie P hP)).2]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [dsW_smul hrep (hsm i) _ (hlie P hP), dsW_append', dsW_append']
          rfl
        have hprod : 0 ≤ (W'.map (fun X => ‖X‖)).prod :=
          List.prod_nonneg (fun a ha => by
            obtain ⟨Y, _, rfl⟩ := List.mem_map.1 ha
            exact norm_nonneg _)
        simp only [List.map_cons, List.prod_cons]
        rw [heq]
        calc ‖∑ i, (c i : ℂ) • dsW σ ((P ++ [b i]) ++ W') w‖
            ≤ ∑ i, ‖(c i : ℂ) • dsW σ ((P ++ [b i]) ++ W') w‖ := norm_sum_le _ _
          _ ≤ ∑ i, (κ * ‖X‖) * (C i * (W'.map (fun X => ‖X‖)).prod) := by
              refine Finset.sum_le_sum fun i _ => ?_
              rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
              exact mul_le_mul (hcb i) (hC i W' hW' hlen') (norm_nonneg _)
                (mul_nonneg hκ (norm_nonneg _))
          _ = (κ * ∑ i, C i) * (‖X‖ * (W'.map (fun X => ‖X‖)).prod) := by
              rw [Finset.mul_sum, Finset.sum_mul]
              refine Finset.sum_congr rfl fun i _ => ?_
              ring
          _ ≤ max ‖dsW σ P w‖ (κ * ∑ i, C i) * (‖X‖ * (W'.map (fun X => ‖X‖)).prod) :=
              mul_le_mul_of_nonneg_right (le_max_right _ _) (mul_nonneg (norm_nonneg _) hprod)
  obtain ⟨C, hC0, hC⟩ := key m [] (fun X hX => absurd hX List.not_mem_nil)
  exact ⟨C, hC0, fun W hW hlen => by simpa using hC W hW hlen⟩

end GlobalTheory.CompanionTheory.BmuWordBd
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.WordLengthBoundOfLinearStatement
open CompanionTheory.Bmu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.word_length_bound_of_linear : DsLin → WordBd := by
  first | exact @GlobalTheory.CompanionTheory.BmuWordBd.wordBd_of_dsLin | exact GlobalTheory.CompanionTheory.BmuWordBd.wordBd_of_dsLin | (intros; apply GlobalTheory.CompanionTheory.BmuWordBd.wordBd_of_dsLin <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IwasawaDecomposition
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IwasawaDecomposition
noncomputable section

namespace GlobalTheory.CompanionTheory.BmuIwa

open Matrix CompanionTheory.Bmu CompanionTheory.D.gk.admitted.CholeskyDecomposition Formalism.QuantumDeterminants
open scoped ComplexOrder MatrixOrder

theorem adapted_dec_one {n : ℕ} {p : Fin n → Fin n} {b : Fin n → ℤ} {c : Fin n → ℂ} (h : Adapted p b c)
    (g : Matrix (Fin n) (Fin n) ℂ) (hg : gᴴ * dp p 0 c * g = dp p 0 c) :
    ∃ k B : Matrix (Fin n) (Fin n) ℂ, kᴴ * k = 1 ∧ kᴴ * dp p 0 c * k = dp p 0 c ∧
      Bᴴ * dp p 0 c * B = dp p 0 c ∧ g = k * B ∧ B.BlockTriangular id := by
  set A := dp p 0 c with hAdef
  have hA : A * A = 1 := h.mul_self
  have hAH : Aᴴ = A := h.herm
  have hg' : g * A * gᴴ = A := flip hA hg
  have hgu : IsUnit g := by
    refine ⟨⟨g, A * gᴴ * A, ?_, ?_⟩, rfl⟩
    · calc g * (A * gᴴ * A) = (g * A * gᴴ) * A := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hg', hA]
    · calc (A * gᴴ * A) * g = A * (gᴴ * A * g) := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hg, hA]
  obtain ⟨B, a, hB, ha, hBd, hBS⟩ :=
    exists_cholesky (PosDef.conjTranspose_mul_self g (mulVec_injective_of_isUnit hgu))
  have hBdet : IsUnit B.det := by
    rw [det_of_isUpperTriangular hB]
    exact IsUnit.mk0 _ (Finset.prod_ne_zero_iff.2 fun i _ => by
      rw [hBd i]; exact RCLike.ofReal_ne_zero.2 (ha i).ne')
  have hBi : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul _ hBdet
  have hBi' : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv _ hBdet
  have hBiH : B⁻¹ᴴ * Bᴴ = 1 := by rw [← conjTranspose_mul, hBi', conjTranspose_one]

  have hS : Bᴴ * B * A * (Bᴴ * B) = A := by
    rw [hBS]
    calc gᴴ * g * A * (gᴴ * g) = gᴴ * (g * A * gᴴ) * g := by simp only [Matrix.mul_assoc]
      _ = A := by rw [hg', hg]
  have hS1 : A * (Bᴴ * B) * A * Bᴴ * B = 1 := by
    calc A * (Bᴴ * B) * A * Bᴴ * B = A * (Bᴴ * B * A * (Bᴴ * B)) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hS, hA]
  have hu : B * (A * (Bᴴ * B) * A * Bᴴ) = 1 := mul_eq_one_comm.1 hS1
  have hw : (B * (A * Bᴴ * A))ᴴ * (B * (A * Bᴴ * A)) = 1 := by
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, hAH]
    calc A * (B * A) * Bᴴ * (B * (A * Bᴴ * A)) = A * (B * (A * (Bᴴ * B) * A * Bᴴ)) * A := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hu, Matrix.mul_one, hA]
  have hw1 : B * (A * Bᴴ * A) = 1 :=
    eq_one_of_posSemidef hw (h.posSemidef hB ha hBd fun i j hij =>
      eq_zero_of_unitary_blockTriangular hw ((h.tri hB).mul (h.conj_tri hB)) hij)
  have hw2 : (A * Bᴴ * A) * B = 1 := mul_eq_one_comm.1 hw1
  have hBA : Bᴴ * A * B = A := by
    calc Bᴴ * A * B = (A * A) * (Bᴴ * A * B) := by rw [hA, Matrix.one_mul]
      _ = A * ((A * Bᴴ * A) * B) := by simp only [Matrix.mul_assoc]
      _ = A := by rw [hw2, Matrix.mul_one]
  refine ⟨g * B⁻¹, B, ?_, ?_, hBA, ?_, hB⟩
  · rw [conjTranspose_mul]
    calc B⁻¹ᴴ * gᴴ * (g * B⁻¹) = B⁻¹ᴴ * (gᴴ * g) * B⁻¹ := by simp only [Matrix.mul_assoc]
      _ = (B⁻¹ᴴ * Bᴴ) * (B * B⁻¹) := by rw [← hBS]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hBiH, hBi', Matrix.one_mul]
  · rw [conjTranspose_mul]
    calc B⁻¹ᴴ * gᴴ * A * (g * B⁻¹) = B⁻¹ᴴ * (gᴴ * A * g) * B⁻¹ := by simp only [Matrix.mul_assoc]
      _ = B⁻¹ᴴ * (Bᴴ * A * B) * B⁻¹ := by rw [hg, hBA]
      _ = (B⁻¹ᴴ * Bᴴ) * A * (B * B⁻¹) := by simp only [Matrix.mul_assoc]
      _ = A := by rw [hBiH, hBi', Matrix.one_mul, Matrix.mul_one]
  · rw [Matrix.mul_assoc, hBi, Matrix.mul_one]

theorem conj_mem {n : ℕ} {A g : Matrix (Fin n) (Fin n) ℂ} (hA : A * A = 1) (hAH : Aᴴ = A)
    (hg : gᴴ * A * g = A) : (A * gᴴ * A)ᴴ * A * (A * gᴴ * A) = A := by
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, hAH]
  calc A * (g * A) * A * (A * gᴴ * A) = A * (g * (A * A) * A * gᴴ) * A := by simp only [Matrix.mul_assoc]
    _ = A := by rw [hA, Matrix.mul_one, CompanionTheory.D.gk.admitted.CholeskyDecomposition.flip hA hg, hA, Matrix.one_mul]

theorem conj_mul {n : ℕ} {A g : Matrix (Fin n) (Fin n) ℂ} (hA : A * A = 1)
    (hg : gᴴ * A * g = A) : (A * gᴴ * A) * g = 1 := by
  calc (A * gᴴ * A) * g = A * (gᴴ * A * g) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg, hA]

theorem adapted_dec_left {n : ℕ} {p : Fin n → Fin n} {b : Fin n → ℤ} {c : Fin n → ℂ} (h : Adapted p b c)
    (x : Matrix (Fin n) (Fin n) ℂ) (hx : xᴴ * dp p 0 c * x = dp p 0 c) :
    ∃ s κ : Matrix (Fin n) (Fin n) ℂ, sᴴ * dp p 0 c * s = dp p 0 c ∧ κᴴ * dp p 0 c * κ = dp p 0 c ∧
      s.BlockTriangular id ∧ κᴴ * κ = 1 ∧ x = s * κ := by
  have hA := h.mul_self
  have hAH := h.herm
  obtain ⟨k, B, hk, hkA, hBA, hg, hB⟩ := adapted_dec_one h _ (conj_mem hA hAH hx)
  set A := dp p 0 c
  have hBl := conj_mul hA hBA
  have hk' : k * kᴴ = 1 := mul_eq_one_comm.1 hk
  refine ⟨A * Bᴴ * A, kᴴ, conj_mem hA hAH hBA, ?_, ?_, ?_, ?_⟩
  · rw [conjTranspose_conjTranspose]; exact CompanionTheory.D.gk.admitted.CholeskyDecomposition.flip hA hkA
  · let _ : Invertible B := invertibleOfLeftInverse B _ hBl
    rw [← inv_eq_left_inv hBl]
    exact blockTriangular_inv_of_blockTriangular hB
  · rw [conjTranspose_conjTranspose]; exact hk'
  · have h1 : k * B * x = 1 := by rw [← hg]; exact conj_mul hA hx
    calc x = (A * Bᴴ * A * B) * x := by rw [hBl, Matrix.one_mul]
      _ = A * Bᴴ * A * ((kᴴ * k) * B * x) := by rw [hk, Matrix.one_mul]; simp only [Matrix.mul_assoc]
      _ = A * Bᴴ * A * kᴴ * (k * B * x) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, Matrix.mul_one]

def pq (k r : ℕ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) := if outer k r i then i.rev else i

def bq (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℤ := if outer k r i then 2 * (i.val : ℤ) - (2 * r + k) else 0

theorem pq_val (k r : ℕ) (i : Fin (2 * r + k + 1)) :
    (pq k r i).val = if i.val ≤ r ∨ r + k ≤ i.val then 2 * r + k - i.val else i.val := by
  unfold pq
  by_cases h : outer k r i
  · rw [if_pos h, if_pos (show i.val ≤ r ∨ r + k ≤ i.val from h), Fin.val_rev]; omega
  · rw [if_neg h, if_neg (show ¬ (i.val ≤ r ∨ r + k ≤ i.val) from h)]

theorem bq_eq (k r : ℕ) (i : Fin (2 * r + k + 1)) :
    bq k r i = if i.val ≤ r ∨ r + k ≤ i.val then 2 * (i.val : ℤ) - (2 * r + k) else 0 := by
  unfold bq
  by_cases h : outer k r i
  · rw [if_pos h, if_pos (show i.val ≤ r ∨ r + k ≤ i.val from h)]
  · rw [if_neg h, if_neg (show ¬ (i.val ≤ r ∨ r + k ≤ i.val) from h)]

theorem adapted_pq (k r : ℕ) : Adapted (pq k r) (bq k r) (fun _ => 1) := by
  constructor
  · intro i
    apply Fin.ext
    have := i.2
    rw [pq_val, pq_val]
    split_ifs <;> omega
  · intro i j hij
    have h : i.val ≤ j.val := hij
    rw [bq_eq, bq_eq]
    split_ifs <;> omega
  · intro i
    have := i.2
    rw [bq_eq, bq_eq, pq_val]
    split_ifs <;> omega
  · intro i hi
    apply Fin.ext
    have := i.2
    rw [bq_eq] at hi
    rw [pq_val]
    split_ifs at hi ⊢ <;> omega
  · intro i j hi hij
    apply Fin.ext
    rw [bq_eq] at hi
    rw [bq_eq, bq_eq] at hij
    split_ifs at hi hij <;> omega
  · intro i
    simp
  · intro i
    simp
  · intros
    rfl
  · intros
    rfl

theorem Hq_eq_dp (k r : ℕ) : Hq k r = dp (pq k r) 0 (fun _ => 1) := by
  ext i j
  have hi := i.2
  have hj := j.2
  simp only [Hq, dp, Matrix.of_apply, Pi.zero_apply, ite_self, zero_add, Fin.ext_iff, pq_val]
  by_cases h : outer k r i
  · rw [if_pos h, if_pos (show i.val ≤ r ∨ r + k ≤ i.val from h)]
    exact if_congr (by omega) rfl rfl
  · rw [if_neg h, if_neg (show ¬ (i.val ≤ r ∨ r + k ≤ i.val) from h)]
    exact if_congr eq_comm rfl rfl

theorem iwaQ : IwaQ := by
  intro k r _ x hx
  have hx' : xᴴ * Hq k r * x = Hq k r := hx
  rw [Hq_eq_dp] at hx'
  obtain ⟨s, κ, hs, hκ, h1, h2, h3⟩ := adapted_dec_left (adapted_pq k r) x hx'
  rw [← Hq_eq_dp] at hs hκ
  exact ⟨s, hs, κ, hκ, h1, h2, h3⟩

end GlobalTheory.CompanionTheory.BmuIwa
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IwasawaDecompositionStatement
open CompanionTheory.Bmu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.IwasawaDecomposition : IwaQ := by
  first | exact @GlobalTheory.CompanionTheory.BmuIwa.iwaQ | exact GlobalTheory.CompanionTheory.BmuIwa.iwaQ | (intros; apply GlobalTheory.CompanionTheory.BmuIwa.iwaQ <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExteriorIntegrality
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExteriorIntegrality
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker

namespace GlobalTheory.CompanionTheory.WedgeEmb

variable {n m : ℕ}

def er (I : BranchingSupport.Sub n (m + 1)) (j : Fin (m + 1)) : BranchingSupport.Sub n m :=
  ⟨I.1.erase (I.1.orderEmbOfFin I.2 j), by
    rw [Finset.card_erase_of_mem (Finset.orderEmbOfFin_mem _ _ _), I.2]; rfl⟩

theorem er_emb (I : BranchingSupport.Sub n (m + 1)) (j : Fin (m + 1)) :
    ⇑((er I j).1.orderEmbOfFin (er I j).2) = fun a => I.1.orderEmbOfFin I.2 (j.succAbove a) := by
  symm
  apply Finset.orderEmbOfFin_unique
  · intro a
    show _ ∈ I.1.erase _
    rw [Finset.mem_erase]
    exact ⟨fun h => Fin.succAbove_ne j a ((I.1.orderEmbOfFin I.2).injective h), Finset.orderEmbOfFin_mem _ _ _⟩
  · exact (I.1.orderEmbOfFin I.2).strictMono.comp (Fin.strictMono_succAbove j)

theorem exists_emb (I : BranchingSupport.Sub n (m + 1)) {t : Fin n} (ht : t ∈ I.1) : ∃ j, I.1.orderEmbOfFin I.2 j = t := by
  have h : t ∈ Set.range (I.1.orderEmbOfFin I.2) := by
    rw [Finset.range_orderEmbOfFin]
    exact ht
  exact h

theorem er_card (I : BranchingSupport.Sub n (m + 1)) (j : Fin (m + 1)) :
    ((er I j).1.filter fun a => a < I.1.orderEmbOfFin I.2 j).card = j := by
  have key : ((er I j).1.filter fun a => a < I.1.orderEmbOfFin I.2 j) =
      (Finset.Iio j).map (I.1.orderEmbOfFin I.2).toEmbedding := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_Iio, RelEmbedding.coe_toEmbedding]
    constructor
    · rintro ⟨ha, hlt⟩
      have ha' : a ∈ I.1 := Finset.mem_of_mem_erase ha
      obtain ⟨i, rfl⟩ := exists_emb I ha'
      exact ⟨i, (I.1.orderEmbOfFin I.2).lt_iff_lt.mp hlt, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      have hlt := (I.1.orderEmbOfFin I.2).lt_iff_lt.mpr hi
      exact ⟨Finset.mem_erase.mpr ⟨hlt.ne, Finset.orderEmbOfFin_mem _ _ _⟩, hlt⟩
  rw [key, Finset.card_map, Fin.card_Iio]

theorem jW_er (I I' : BranchingSupport.Sub n (m + 1)) (j : Fin (m + 1)) :
    jW n m (er I j, I.1.orderEmbOfFin I.2 j) I' = if I' = I then (-1) ^ (j : ℕ) else 0 := by
  have h1 : I.1.orderEmbOfFin I.2 j ∉ (er I j).1 := by simp [er]
  have h2 : insert (I.1.orderEmbOfFin I.2 j) (er I j).1 = I.1 :=
    Finset.insert_erase (Finset.orderEmbOfFin_mem _ _ _)
  simp only [jW, h1, not_false_eq_true, true_and, h2, er_card]
  by_cases hI : I' = I
  · subst hI
    simp
  · rw [if_neg (fun h => hI (Subtype.ext h)), if_neg hI]

theorem jW_ne (p : BranchingSupport.Sub n m × Fin n) (I : BranchingSupport.Sub n (m + 1)) (h : jW n m p I ≠ 0) :
    ∃ j, (er I j, I.1.orderEmbOfFin I.2 j) = p := by
  obtain ⟨J, t⟩ := p
  simp only [jW] at h
  by_cases hc : t ∉ J.1 ∧ I.1 = insert t J.1
  · have htI : t ∈ I.1 := by
      rw [hc.2]
      exact Finset.mem_insert_self t J.1
    obtain ⟨j, hj⟩ := exists_emb I htI
    refine ⟨j, ?_⟩
    rw [hj]
    refine Prod.ext ?_ rfl
    apply Subtype.ext
    show I.1.erase (I.1.orderEmbOfFin I.2 j) = J.1
    rw [hj, hc.2, Finset.erase_insert hc.1]
  · exact (h (if_neg hc)).elim

theorem sum_jW (F : BranchingSupport.Sub n m × Fin n → ℂ) (I : BranchingSupport.Sub n (m + 1)) :
    ∑ p, F p * jW n m p I = ∑ j : Fin (m + 1), (-1) ^ (j : ℕ) * F (er I j, I.1.orderEmbOfFin I.2 j) := by
  have hq : Function.Injective (fun j : Fin (m + 1) => (er I j, I.1.orderEmbOfFin I.2 j)) :=
    fun a b hab => (I.1.orderEmbOfFin I.2).injective (congrArg Prod.snd hab)
  rw [← Finset.sum_subset (Finset.subset_univ
    (Finset.univ.image (fun j : Fin (m + 1) => (er I j, I.1.orderEmbOfFin I.2 j)))) ?_]
  · rw [Finset.sum_image (fun a _ b _ hab => hq hab)]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [jW_er, if_pos rfl, mul_comm]
  · intro p _ hp
    by_contra hne
    obtain ⟨j, hj⟩ := jW_ne p I (right_ne_zero_of_mul hne)
    exact hp (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩)

theorem laplace (g : Matrix (Fin n) (Fin n) ℂ) (r : Fin (m + 1) → Fin n) (i : Fin (m + 1))
    (J : BranchingSupport.Sub n m) (hJ : ⇑(J.1.orderEmbOfFin J.2) = fun a => r (i.succAbove a)) (I : BranchingSupport.Sub n (m + 1)) :
    ((cmp m g ⊗ₖ g) * jW n m) (J, r i) I =
      (-1) ^ (i : ℕ) * (g.submatrix r (I.1.orderEmbOfFin I.2)).det := by
  rw [Matrix.mul_apply]
  simp only [Matrix.kroneckerMap_apply]
  have hs := sum_jW (fun p => cmp m g J p.1 * g (r i) p.2) I
  simp only at hs
  rw [hs, Matrix.det_succ_row _ i, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hd : cmp m g J (er I j) =
      ((g.submatrix r ⇑(I.1.orderEmbOfFin I.2)).submatrix i.succAbove j.succAbove).det := by
    unfold BranchingSupport.cmp
    rw [hJ, er_emb]
    rfl
  have h2 : ((-1 : ℂ)) ^ (i : ℕ) * (-1) ^ (i : ℕ) = 1 := by
    rw [← mul_pow]
    norm_num
  rw [hd, Matrix.submatrix_apply, pow_add]
  generalize ((g.submatrix r ⇑(I.1.orderEmbOfFin I.2)).submatrix i.succAbove j.succAbove).det = d
  generalize g (r i) (I.1.orderEmbOfFin I.2 j) = x
  linear_combination (-(-1 : ℂ) ^ (j : ℕ) * d * x) * h2

theorem first (g : Matrix (Fin n) (Fin n) ℂ) : jW n m * cmp (m + 1) g = (cmp m g ⊗ₖ g) * jW n m := by
  ext ⟨J, t⟩ I
  by_cases ht : t ∈ J.1
  · have hL : (jW n m * cmp (m + 1) g) (J, t) I = 0 := by
      rw [Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro I'' _
      simp only [jW, ht, not_true_eq_false, false_and, if_false, zero_mul]
    have hl := laplace g (Fin.cons t ⇑(J.1.orderEmbOfFin J.2)) 0 J (by
      funext a
      simp only [Fin.succAbove_zero, Fin.cons_succ]) I
    rw [Fin.cons_zero] at hl
    rw [hL, hl]
    have hr : t ∈ Set.range (J.1.orderEmbOfFin J.2) := by
      rw [Finset.range_orderEmbOfFin]
      exact ht
    obtain ⟨a, ha⟩ := hr
    rw [Matrix.det_zero_of_row_eq (i := (0 : Fin (m + 1))) (j := a.succ) (Fin.succ_ne_zero a).symm ?_, mul_zero]
    funext c
    simp only [Matrix.submatrix_apply, Fin.cons_zero, Fin.cons_succ, ha]
  · let K : BranchingSupport.Sub n (m + 1) := ⟨insert t J.1, by simp [ht, J.2]⟩
    obtain ⟨i, hi⟩ := exists_emb K (Finset.mem_insert_self t J.1)
    have hJK : er K i = J := by
      apply Subtype.ext
      show K.1.erase (K.1.orderEmbOfFin K.2 i) = J.1
      rw [hi]
      exact Finset.erase_insert ht
    have hl := laplace g ⇑(K.1.orderEmbOfFin K.2) i J (by rw [← hJK]; exact er_emb K i) I
    rw [hi] at hl
    rw [hl, Matrix.mul_apply, Finset.sum_eq_single K]
    · have hp : ((J, t) : BranchingSupport.Sub n m × Fin n) = (er K i, K.1.orderEmbOfFin K.2 i) := by
        rw [hJK, hi]
      rw [hp, jW_er, if_pos rfl]
      rfl
    · intro I'' _ hne
      simp only [jW]
      rw [if_neg (fun h => hne (Subtype.ext h.2)), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ K) h

theorem cmp_tr (l : ℕ) (g : Matrix (Fin n) (Fin n) ℂ) : BranchingSupport.cmp l gᵀ = (BranchingSupport.cmp l g)ᵀ := by
  ext I J
  simp only [BranchingSupport.cmp, Matrix.transpose_apply]
  rw [← Matrix.det_transpose, Matrix.transpose_submatrix, Matrix.transpose_transpose]

theorem third : (jW n m)ᵀ * jW n m = ((m : ℂ) + 1) • (1 : Matrix (BranchingSupport.Sub n (m + 1)) (BranchingSupport.Sub n (m + 1)) ℂ) := by
  have h1 : ∀ j : Fin (m + 1), ((-1 : ℂ)) ^ (j : ℕ) * (-1) ^ (j : ℕ) = 1 := fun j => by
    rw [← mul_pow]
    norm_num
  ext I I'
  rw [Matrix.mul_apply]
  show ∑ p, jW n m p I * jW n m p I' = _
  have hs := sum_jW (fun p => jW n m p I') I
  rw [Finset.sum_congr rfl (fun p _ => mul_comm (jW n m p I) (jW n m p I')), hs]
  simp only [jW_er]
  by_cases h : I' = I
  · subst h
    have hc : ∀ j : Fin (m + 1), ((-1 : ℂ)) ^ (j : ℕ) * (if I' = I' then (-1) ^ (j : ℕ) else 0) = 1 :=
      fun j => by rw [if_pos rfl, h1]
    rw [Finset.sum_congr rfl (fun j _ => hc j), Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    norm_num
  · simp only [if_neg h, mul_zero, Finset.sum_const_zero, Matrix.smul_apply,
      Matrix.one_apply_ne (Ne.symm h), smul_zero]

theorem wedgeInt : WedgeInt := by
  intro n m
  refine ⟨fun g => ⟨first g, ?_⟩, third⟩
  have h := congrArg Matrix.transpose (first (n := n) (m := m) gᵀ)
  simp only [Matrix.transpose_mul, cmp_tr, Matrix.transpose_transpose,
    Matrix.kroneckerMap_transpose] at h
  exact h.symm

end GlobalTheory.CompanionTheory.WedgeEmb
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExteriorIntegralityStatement
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ExteriorIntegrality : WedgeInt := by
  first | exact @GlobalTheory.CompanionTheory.WedgeEmb.wedgeInt | exact GlobalTheory.CompanionTheory.WedgeEmb.wedgeInt | (intros; apply GlobalTheory.CompanionTheory.WedgeEmb.wedgeInt <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ReductionOfDerivedSeries
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ReductionOfDerivedSeries
open Matrix MeasureTheory Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm CompanionTheory.Bmu
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.BmuReduce

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem contDiff_of_smOn_univ {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V]
    [NormedSpace ℝ V] {f : E → V} (hf : SmOn Set.univ f) : ContDiff ℝ ∞ f := by
  rw [contDiff_iff_contDiffAt]
  intro a
  obtain ⟨U, F, hU, haU, hF, hfF⟩ := hf a (Set.mem_univ a)
  refine (hF.contDiffAt (hU.mem_nhds haU)).congr_of_eventuallyEq ?_
  filter_upwards [hU.mem_nhds haU] with g hg
  exact hfF g hg (Set.mem_univ g)

theorem cut_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {U : Set E} (hU : IsOpen U) {φ a : E → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ U) (ha : ContDiffOn ℝ ∞ a U) :
    ContDiff ℝ ∞ (fun t => φ t * a t) ∧ HasCompactSupport (fun t => φ t * a t) ∧
      tsupport (fun t => φ t * a t) ⊆ U := by
  have h1 : tsupport (fun t => φ t * a t) ⊆ U := (tsupport_mul_subset_left (f := φ) (g := a)).trans hs
  refine ⟨contDiff_iff_contDiffAt.2 fun x => ?_, hc.mul_right, h1⟩
  by_cases hx : x ∈ tsupport (fun t => φ t * a t)
  · exact hφ.contDiffAt.mul (ha.contDiffAt (hU.mem_nhds (h1 hx)))
  · exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.1 hx)

theorem cut_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {U : Set E} {φ : E → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ U) (v : E) :
    ContDiff ℝ ∞ (fun t => fderiv ℝ φ t v) ∧ HasCompactSupport (fun t => fderiv ℝ φ t v) ∧
      tsupport (fun t => fderiv ℝ φ t v) ⊆ U :=
  ⟨(hφ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const, hc.fderiv_apply ℝ v,
    (tsupport_fderiv_apply_subset ℝ v).trans hs⟩

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {G : Set (Mat n)} {σ : Mat n → (H →L[ℂ] H)}

theorem contDiff_orbit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (h : RepOn G σ) {w : H}
    (hw : IsSm G σ w) {W : List (Mat n)} (hW : LieW G W) {s : E → Mat n} (hs : ContDiff ℝ ∞ s)
    (hm : ∀ t, s t ∈ G) : ContDiff ℝ ∞ (fun t => dsW σ W (σ (s t) w)) := by
  have h1 := SmOn.comp (smOn_dsW h (u := fun x => σ x w) (hw.smOn_mul h) hW)
    (φ := fun t : E => ((1 : Mat n), s t)) (B := Set.univ) (contDiff_const.prodMk hs)
    fun t _ => ⟨h.one_mem, hm t⟩
  refine contDiff_of_smOn_univ (h1.congr fun x _ => ?_)
  simp [h.map_one]

theorem dsW_sum (h : RepOn G σ) {W : List (Mat n)} (hW : LieW G W) {ι : Type*} (c : ι → ℂ) (v : ι → H)
    (hv : ∀ i, IsSm G σ (v i)) (S : Finset ι) :
    IsSm G σ (∑ i ∈ S, c i • v i) ∧ dsW σ W (∑ i ∈ S, c i • v i) = ∑ i ∈ S, c i • dsW σ W (v i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨by simpa using IsSm.zero, ?_⟩
    have := dsW_smul h (IsSm.zero (G := G) (σ := σ)) (0 : ℂ) hW
    simpa using this
  | insert i S hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact ⟨((hv i).smul _).add ih.1, by rw [dsW_add h ((hv i).smul _) ih.1 hW, dsW_smul h (hv i) _ hW, ih.2]⟩

theorem lieW_of {Hm : Mat n} {W : List (Mat n)} (hW : LieWd Hm W) : LieW (UH Hm) W :=
  fun X hX t => ex_mem_of_lie (hW X hX) t

theorem isSm_ds {Hm : Mat n} (h : RepOn (UH Hm) σ) {X : Mat n} (hX : Lie Hm X) {u : H} (hu : IsSm (UH Hm) σ u) :
    IsSm (UH Hm) σ (ds σ X u) :=
  hu.dsW h (W := [X]) (lieW_of fun Y hY => by rw [List.mem_singleton.1 hY]; exact hX)

theorem dsW_append (W W' : List (Mat n)) (v : H) : dsW σ (W ++ W') v = dsW σ W (dsW σ W' v) :=
  List.foldr_append

theorem last_letter [CompleteSpace H] (hlin : DsLin) (had : DsAd) {Hm : Mat n} (hσ : URep Hm σ)
    {W : List (Mat n)} (hW : LieWd Hm W) {Y y : Mat n} (hY : Lie Hm Y) (hy : y ∈ UH Hm) {d e : ℕ}
    {Z : Fin d → Mat n} {Q : Fin e → Mat n} (hZ : ∀ j, Lie Hm (Z j)) (hQ : ∀ i, Lie Hm (Q i))
    {a : Fin d → ℝ} {b : Fin e → ℝ} (hab : y⁻¹ * Y * y = ∑ j, (a j : ℂ) • Z j + ∑ i, (b i : ℂ) • Q i)
    {u : H} (hu : IsSm (UH Hm) σ u) :
    dsW σ (W ++ [Y]) (σ y u) =
      ∑ j, a j • dsW σ W (σ y (ds σ (Z j) u)) + ∑ i, b i • dsW σ W (σ y (ds σ (Q i) u)) := by
  obtain ⟨h1, h2⟩ := had n Hm H σ hσ y hy [Y] (fun X hX => by rw [List.mem_singleton.1 hX]; exact hY)
  obtain ⟨Λ, hΛ⟩ := hlin n Hm H σ hσ u hu
  have h3 : Lie Hm (y⁻¹ * Y * y) := h1 _ (by simp)
  have h4 : ds σ (y⁻¹ * Y * y) u = ∑ j, (a j : ℂ) • ds σ (Z j) u + ∑ i, (b i : ℂ) • ds σ (Q i) u := by
    rw [hΛ _ h3, hab]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Complex.coe_smul, map_add (f := _), map_sum, map_smul, hΛ _ (hZ _), hΛ _ (hQ _)]
  have h5 : dsW σ [Y] (σ y u) =
      ∑ j, (a j : ℂ) • σ y (ds σ (Z j) u) + ∑ i, (b i : ℂ) • σ y (ds σ (Q i) u) := by
    rw [h2 u hu]
    change σ y (ds σ (y⁻¹ * Y * y) u) = _
    rw [h4]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_add (f := _), map_sum, map_smul]
  have hA := dsW_sum hσ.rep (lieW_of hW) (fun j => (a j : ℂ)) (fun j => σ y (ds σ (Z j) u))
    (fun j => (isSm_ds hσ.rep (hZ j) hu).apply hσ.rep hy) Finset.univ
  have hB := dsW_sum hσ.rep (lieW_of hW) (fun j => (b j : ℂ)) (fun j => σ y (ds σ (Q j) u))
    (fun j => (isSm_ds hσ.rep (hQ j) hu).apply hσ.rep hy) Finset.univ
  rw [dsW_append, h5, dsW_add hσ.rep hA.1 hB.1 (lieW_of hW), hA.2, hB.2]
  simp only [Complex.coe_smul]

theorem fderiv_orbit [CompleteSpace H] (hder : DsDer) {Hm : Mat n} (hσ : URep Hm σ)
    {W : List (Mat n)} (hW : LieWd Hm W) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : E → Mat n}
    (hs : ContDiff ℝ ∞ s) (hm : ∀ t, s t ∈ UH Hm) {t v : E} {Z : Mat n} (hZ : Lie Hm Z)
    (hfl : ∀ τ : ℝ, s (t + τ • v) = s t * ex Z τ) {u : H} (hu : IsSm (UH Hm) σ u) :
    fderiv ℝ (fun t => dsW σ W (σ (s t) u)) t v = dsW σ W (σ (s t) (ds σ Z u)) := by
  have h1 := contDiff_orbit hσ.rep hu (lieW_of hW) hs hm
  have h2 : HasLineDerivAt ℝ (fun t => dsW σ W (σ (s t) u)) (fderiv ℝ (fun t => dsW σ W (σ (s t) u)) t v) t v :=
    (h1.differentiable (by simp) t).hasFDerivAt.hasLineDerivAt v
  have h3 : HasLineDerivAt ℝ (fun t => dsW σ W (σ (s t) u)) (dsW σ W (σ (s t) (ds σ Z u))) t v := by
    unfold HasLineDerivAt
    simp only [hfl]
    exact hder n Hm H σ hσ W hW (s t) (hm t) Z hZ u hu
  exact h2.unique h3

theorem integrable_cut {d : ℕ} {ψ : (Fin d → ℝ) → ℝ} (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    {f : (Fin d → ℝ) → H} (hf : Continuous f) : Integrable (fun t => ψ t • f t) :=
  (hψ.smul hf).integrable_of_hasCompactSupport hc.smul_right

theorem parts {d : ℕ} {ψ : (Fin d → ℝ) → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    {f : (Fin d → ℝ) → H} (hf : ContDiff ℝ ∞ f) (v : Fin d → ℝ) :
    ∫ t, ψ t • fderiv ℝ f t v = - ∫ t, fderiv ℝ ψ t v • f t := by
  obtain ⟨h1, h2, -⟩ := cut_fderiv hψ hc (Set.subset_univ _) v
  refine integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable (integrable_cut h1.continuous h2 hf.continuous)
    (integrable_cut hψ.continuous hc ((hf.continuous_fderiv (by simp)).clm_apply continuous_const))
    (integrable_cut hψ.continuous hc hf.continuous) (fun x _ => hψ.differentiable (by simp) x)
    (fun x _ => hf.differentiable (by simp) x)

theorem reduce : DsLin → DsAd → DsDer → Reduce := by
  intro hlin had hder n Hm H _ _ _ σ hσ d e Q s U hch W
  simp only [Complex.coe_smul]
  induction W using List.reverseRecOn with
  | nil =>
    intro _ φ hφ hc _
    refine ⟨∫ t, ‖φ t‖, integral_nonneg fun t => norm_nonneg _, fun u _ R hR => ?_⟩
    have hu : ‖u‖ ≤ R := hR [] le_rfl
    refine (norm_integral_le_integral_norm _).trans ?_
    have : ∀ t, ‖φ t • dsW σ [] (σ (s t) u)‖ = ‖φ t‖ * ‖u‖ := fun t => by
      rw [norm_smul]
      exact congrArg _ (hσ.iso _ (hch.mem t) u)
    simp only [this]
    rw [integral_mul_const]
    exact mul_le_mul_of_nonneg_left hu (integral_nonneg fun t => norm_nonneg _)
  | append_singleton W Y ih =>
    intro hWY φ hφ hc hs
    have hW : LieWd Hm W := fun X hX => hWY X (List.mem_append_left _ hX)
    have hY : Lie Hm Y := hWY Y (by simp)
    obtain ⟨Z, hZ, hfl, hsp⟩ := hch.flow
    obtain ⟨a, b, ha, hb, hab⟩ := hsp Y hY
    have hA := fun j => cut_mul hch.isOpen hφ hc hs (ha j)
    have hB := fun i => cut_mul hch.isOpen hφ hc hs (hb i)
    have hA' := fun j => cut_fderiv (hA j).1 (hA j).2.1 (hA j).2.2 (Pi.single j 1)
    choose C hC0 hC using fun j => ih hW _ (hA' j).1 (hA' j).2.1 (hA' j).2.2
    choose D hD0 hD using fun i => ih hW _ (hB i).1 (hB i).2.1 (hB i).2.2
    refine ⟨∑ j, C j + ∑ i, D i, add_nonneg (Finset.sum_nonneg fun j _ => hC0 j)
      (Finset.sum_nonneg fun j _ => hD0 j), fun u hu R hR => ?_⟩
    have hf := contDiff_orbit hσ.rep hu (lieW_of hW) hch.smooth hch.mem
    have hg := fun i => contDiff_orbit hσ.rep (isSm_ds hσ.rep (hch.lieQ i) hu) (lieW_of hW) hch.smooth hch.mem
    have hpt : ∀ t, φ t • dsW σ (W ++ [Y]) (σ (s t) u) =
        ∑ j, (φ t * a j t) • fderiv ℝ (fun t => dsW σ W (σ (s t) u)) t (Pi.single j 1) +
          ∑ i, (φ t * b i t) • dsW σ W (σ (s t) (ds σ (Q i) u)) := fun t => by
      by_cases ht : t ∈ tsupport φ
      · rw [last_letter hlin had hσ hW hY (hch.mem t) (fun j => hZ j t) hch.lieQ (hab t (hs ht)) hu]
        simp only [fun j => fderiv_orbit hder hσ hW hch.smooth hch.mem (hZ j t) (hfl j t) hu,
          smul_add, Finset.smul_sum, smul_smul]
      · simp [image_eq_zero_of_notMem_tsupport ht]
    have iA : ∀ j, Integrable fun t =>
        (φ t * a j t) • fderiv ℝ (fun t => dsW σ W (σ (s t) u)) t (Pi.single j 1) := fun j =>
      integrable_cut (hA j).1.continuous (hA j).2.1
        ((hf.continuous_fderiv (by simp)).clm_apply continuous_const)
    have iB : ∀ i, Integrable fun t => (φ t * b i t) • dsW σ W (σ (s t) (ds σ (Q i) u)) := fun i =>
      integrable_cut (hB i).1.continuous (hB i).2.1 (hg i).continuous
    simp only [hpt]
    rw [integral_add (MeasureTheory.integrable_finsetSum _ fun j _ => iA j) (MeasureTheory.integrable_finsetSum _ fun j _ => iB j),
      MeasureTheory.integral_finsetSum _ fun j _ => iA j, MeasureTheory.integral_finsetSum _ fun j _ => iB j, add_mul, Finset.sum_mul,
      Finset.sum_mul]
    refine (norm_add_le _ _).trans (add_le_add ((norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_))
      ((norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)))
    · rw [parts (hA j).1 (hA j).2.1 hf, norm_neg]
      exact hC j u hu R fun P hP => hR P (by simp; omega)
    · refine hD i _ (isSm_ds hσ.rep (hch.lieQ i) hu) R fun P hP => ?_
      have := hR (P ++ [i]) (by simp; omega)
      rwa [List.map_append, dsW_append] at this

end GlobalTheory.CompanionTheory.BmuReduce

end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ReductionOfDerivedSeriesStatement
open CompanionTheory.Bmu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reduction_of_derived_series : DsLin → DsAd → DsDer → Reduce := by
  first | exact @GlobalTheory.CompanionTheory.BmuReduce.reduce | exact GlobalTheory.CompanionTheory.BmuReduce.reduce | (intros; apply GlobalTheory.CompanionTheory.BmuReduce.reduce <;> assumption)
end
end
