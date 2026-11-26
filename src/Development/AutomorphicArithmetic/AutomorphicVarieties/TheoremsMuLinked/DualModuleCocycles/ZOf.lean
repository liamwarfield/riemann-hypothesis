module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.StarFacts

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.ZOf
open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

theorem UpperTheory.V.Th.Coc.zOf :
    ∀ {l : ℕ} [Fact l.Prime] (F : GFrame l) {O R X : Type} [CommRing O] [CommRing R] [Algebra O R] [CommRing X] [Algebra O X] {n : ℕ} [Algebra ℤ_[l] O] (x : R →ₐ[O] O) (δ : R →ₗ[O] X) (ρ : F.G₀ →* GL (Fin n) O) (P : GL (Fin n) O) (τ : MonoidAlgebra R F.G₀ → R) (c : O) (d : MonoidAlgebra R F.G₀ →+ Matrix (Fin n) (Fin n) X) (z : F.G₀ → Matrix (Fin n) (Fin n) X), IsDer x δ → F.IsForm O n ρ P → IsLift x δ (repR x (mat ρ)) τ c d → (∀ a, bar X (P : Matrix (Fin n) (Fin n) O) * d (F.star O R n a) = (d a)ᵀ * bar X (P : Matrix (Fin n) (Fin n) O)) → (∀ g, z g = d (MonoidAlgebra.single g 1) * bar X (mat ρ g⁻¹)) → d 1 = 0 ∧ (∀ g g', z (g * g') = z g + bar X (mat ρ g) * z g' * bar X (mat ρ g⁻¹)) ∧ (∀ g, bar X (P : Matrix (Fin n) (Fin n) O) * z (F.conj g) = -((z g)ᵀ * bar X (P : Matrix (Fin n) (Fin n) O))) ∧ ∀ g, (z g * bar X (mat ρ g)).trace = c • δ (τ (MonoidAlgebra.single g 1)) := by
  intro l _ F O R X _ _ _ _ _ n _ x δ ρ P τ c d z hδ hF hL hst hz
  have bmul : ∀ A B : Matrix (Fin n) (Fin n) O, bar X (A * B) = bar X A * bar X B := fun A B => Matrix.map_mul
  have bone : bar X (1 : Matrix (Fin n) (Fin n) O) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have bsm : ∀ (e : O) (A : Matrix (Fin n) (Fin n) O), bar X (e • A) = e • bar X A := by
    intro e A
    ext i j
    show algebraMap O X (e * A i j) = e • algebraMap O X (A i j)
    rw [map_mul, Algebra.smul_def]
  have rmul : ∀ g g', bar X (mat ρ (g * g')) = bar X (mat ρ g) * bar X (mat ρ g') := by
    intro g g'
    rw [map_mul, bmul]
  have rinv : ∀ g, bar X (mat ρ g⁻¹) * bar X (mat ρ g) = 1 := by
    intro g
    rw [← rmul, inv_mul_cancel, map_one, bone]
  have rinv' : ∀ g, bar X (mat ρ g) * bar X (mat ρ g⁻¹) = 1 := by
    intro g
    rw [← rmul, mul_inv_cancel, map_one, bone]
  have d1 : d 1 = 0 := by
    have h := hL.mul 1 1
    rw [mul_one, map_one (repR x (mat ρ)), bone, mul_one, one_mul] at h
    exact left_eq_add.mp h
  have δ1 : δ 1 = 0 := by
    have h := hδ 1 1
    rw [mul_one, map_one x, one_smul] at h
    exact left_eq_add.mp h
  have δa : ∀ e : O, δ (algebraMap O R e) = 0 := by
    intro e
    rw [Algebra.algebraMap_eq_smul_one, map_smul, δ1, smul_zero]
  have dmul : ∀ g g', d (MonoidAlgebra.single (g * g') 1) =
      d (MonoidAlgebra.single g 1) * bar X (mat ρ g') + bar X (mat ρ g) * d (MonoidAlgebra.single g' 1) := by
    intro g g'
    have h := hL.mul (MonoidAlgebra.single g 1) (MonoidAlgebra.single g' 1)
    rw [MonoidAlgebra.single_mul_single, mul_one, repR_single, repR_single, map_one, one_smul, one_smul] at h
    exact h
  have hd : ∀ g, d (MonoidAlgebra.single g 1) = z g * bar X (mat ρ g) := by
    intro g
    rw [hz, mul_assoc, rinv, mul_one]
  have dinv : ∀ g, d (MonoidAlgebra.single g⁻¹ 1) = -(bar X (mat ρ g⁻¹) * z g) := by
    intro g
    have h := dmul g⁻¹ g
    rw [inv_mul_cancel, ← MonoidAlgebra.one_def, d1] at h
    have h2 := congrArg (· * bar X (mat ρ g⁻¹)) h
    simp only [zero_mul, add_mul, mul_assoc, rinv', mul_one] at h2
    rw [hz]
    exact eq_neg_of_add_eq_zero_left h2.symm
  refine ⟨d1, ?_, ?_, ?_⟩
  · intro g g'
    rw [hz (g * g'), dmul, _root_.mul_inv_rev, rmul, hz g, hz g', add_mul]
    simp only [mul_assoc]
    rw [← mul_assoc (bar X (mat ρ g')), rinv', one_mul]
  · intro g
    have h := hst (MonoidAlgebra.single g 1)
    rw [(starFacts F (O := O) (R := R) (n := n)).2.2.2.2.1 g] at h
    have hf := congrArg (bar X) (hF g)
    generalize ((F.eps O O g ^ (1 - (n : ℤ)) : Oˣ) : O) = e at h hf
    have hs : (MonoidAlgebra.single (F.conj g)⁻¹ (algebraMap O R e) : MonoidAlgebra R F.G₀) =
        algebraMap O R e • MonoidAlgebra.single (F.conj g)⁻¹ 1 := by
      rw [MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
    rw [hs, hL.smul, δa, smul_zero, zero_smul, add_zero, AlgHom.commutes, dinv, hd, transpose_mul] at h
    rw [bmul, bmul, bsm] at hf
    have ht : bar X (mat ρ g)ᵀ = (bar X (mat ρ g))ᵀ := rfl
    rw [ht] at hf
    have hf2 : (bar X (mat ρ g))ᵀ * bar X (P : Matrix (Fin n) (Fin n) O) =
        e • (bar X (P : Matrix (Fin n) (Fin n) O) * bar X (mat ρ (F.conj g)⁻¹)) := by
      rw [← smul_mul_assoc, ← hf, mul_assoc, rinv', mul_one]
    have h3 : (bar X (mat ρ g))ᵀ * (bar X (P : Matrix (Fin n) (Fin n) O) * z (F.conj g)) =
        (bar X (mat ρ g))ᵀ * -((z g)ᵀ * bar X (P : Matrix (Fin n) (Fin n) O)) := by
      rw [mul_neg, ← mul_assoc, ← mul_assoc, ← h, hf2]
      simp [mul_assoc]
    have h4 : (bar X (mat ρ g⁻¹))ᵀ * (bar X (mat ρ g))ᵀ = 1 := by
      rw [← transpose_mul, rinv', transpose_one]
    have h5 := congrArg ((bar X (mat ρ g⁻¹))ᵀ * ·) h3
    simp only [← mul_assoc _ (bar X (mat ρ g))ᵀ, h4, one_mul] at h5
    exact h5
  · intro g
    rw [← hd, hL.tr]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.Polar
open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

theorem UpperTheory.V.Th.Coc.polar :
    ∀ {l : ℕ} [Fact l.Prime] (F : GFrame l) {O R X : Type} [CommRing O] [CommRing R] [Algebra O R] [CommRing X] [Algebra O X] {n : ℕ} [Algebra ℤ_[l] O] (x : R →ₐ[O] O) (δ : R →ₗ[O] X) (ρ : F.G₀ →* GL (Fin n) O) (P : GL (Fin n) O) (t : MonoidAlgebra R F.G₀ →ₗ[R] R) (c : O) (d : MonoidAlgebra R F.G₀ →+ Matrix (Fin n) (Fin n) X), ((P : Matrix (Fin n) (Fin n) O)ᵀ = P ∨ (P : Matrix (Fin n) (Fin n) O)ᵀ = -P) → F.IsForm O n ρ P → (∀ g, t (F.star O R n (MonoidAlgebra.single g 1)) = t (MonoidAlgebra.single g 1)) → IsLift x δ (repR x (mat ρ)) t c d → ∃ d' : MonoidAlgebra R F.G₀ →+ Matrix (Fin n) (Fin n) X, IsLift x δ (repR x (mat ρ)) t (2 * c) d' ∧ ∀ a, bar X (P : Matrix (Fin n) (Fin n) O) * d' (F.star O R n a) = (d' a)ᵀ * bar X (P : Matrix (Fin n) (Fin n) O) := by
  intro l _ F O R X _ _ _ _ _ n _ x δ ρ P t c d hP hF ht hd
  obtain ⟨hsm, hsa, hsr, hss, -, hsρ⟩ := starFacts F (O := O) (R := R) (n := n)
  have hρs := hsρ x ρ P hF
  obtain ⟨ε, hεε, hPt⟩ : ∃ ε : O, ε * ε = 1 ∧
      (P : Matrix (Fin n) (Fin n) O)ᵀ = ε • (P : Matrix (Fin n) (Fin n) O) := by
    rcases hP with h | h
    · exact ⟨1, one_mul 1, by rw [h, one_smul]⟩
    · exact ⟨-1, by ring, by rw [h, neg_one_smul]⟩
  have hmap : ∀ A B : Matrix (Fin n) (Fin n) O, bar X (A * B) = bar X A * bar X B :=
    fun A B => Matrix.map_mul
  set Pb := bar X (P : Matrix (Fin n) (Fin n) O) with hPb
  set Q := bar X ((P⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) with hQ
  set e : X := algebraMap O X ε with he
  have hQP : Q * Pb = 1 := by
    rw [hQ, hPb, ← hmap, Units.inv_mul]
    simp [bar]
  have hPQ : Pb * Q = 1 := by
    rw [hQ, hPb, ← hmap, Units.mul_inv]
    simp [bar]
  have hQP' : ∀ M, Q * (Pb * M) = M := fun M => by rw [← Matrix.mul_assoc, hQP, Matrix.one_mul]
  have hPQ' : ∀ M, Pb * (Q * M) = M := fun M => by rw [← Matrix.mul_assoc, hPQ, Matrix.one_mul]
  have hee : e * e = 1 := by rw [he, ← map_mul, hεε, map_one]
  have hPbt : Pbᵀ = e • Pb := by
    ext i j
    have h := congrFun (congrFun hPt i) j
    simp only [Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul] at h
    simp [hPb, bar, Matrix.transpose_apply, h, map_mul, he]
  have hQt : Qᵀ = e • Q := by
    have h0 : e • (Pb * Qᵀ) = 1 := by
      rw [← Matrix.smul_mul, ← hPbt, ← Matrix.transpose_mul, hQP, Matrix.transpose_one]
    have h1 : Pb * Qᵀ = e • 1 := by
      calc Pb * Qᵀ = (e * e) • (Pb * Qᵀ) := by rw [hee, one_smul]
        _ = e • 1 := by rw [mul_smul, h0]
    calc Qᵀ = Q * (Pb * Qᵀ) := by rw [hQP']
      _ = e • Q := by rw [h1, Matrix.mul_smul, Matrix.mul_one]
  have hρ : ∀ a, bar X (repR x (mat ρ) (F.star O R n a)) =
      Q * (bar X (repR x (mat ρ) a))ᵀ * Pb := by
    intro a
    rw [hρs, hmap, hmap]
    rfl
  have hρT : ∀ a, (bar X (repR x (mat ρ) (F.star O R n a)))ᵀ =
      Pb * bar X (repR x (mat ρ) a) * Q := by
    intro a
    rw [hρ, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hPbt, hQt]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hee, one_smul, Matrix.mul_assoc]
  let eD : MonoidAlgebra R F.G₀ →+ Matrix (Fin n) (Fin n) X :=
    AddMonoidHom.mk' (fun a => Q * (d (F.star O R n a))ᵀ * Pb) (by
      intro a b
      simp only [hsa, map_add (f := _), Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul])
  have heD : ∀ a, eD a = Q * (d (F.star O R n a))ᵀ * Pb := fun a => rfl
  have h0 : F.star O R n 0 = 0 := by simpa using hsr 0 0
  have htS : ∀ a, t (F.star O R n a) = t a := by
    intro a
    induction a using MonoidAlgebra.induction_linear with
    | zero => rw [h0]
    | add a b ha hb => rw [hsa, map_add (f := _), map_add (f := _), ha, hb]
    | single g r =>
      have hs : (MonoidAlgebra.single g r : MonoidAlgebra R F.G₀) = r • MonoidAlgebra.single g 1 := by
        rw [MonoidAlgebra.smul_single', mul_one]
      rw [hs, hsr, map_smul, map_smul, ht]
  refine ⟨d + eD, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro a b
    simp only [AddMonoidHom.add_apply, heD, hd.mul, hsm, Matrix.transpose_add, Matrix.transpose_mul,
      hρT, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, hQP', hQP, Matrix.mul_one]
    abel
  · intro r a
    simp only [AddMonoidHom.add_apply, heD, hd.smul, hsr, Matrix.transpose_add, Matrix.transpose_smul,
      hρT, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, hQP',
      hQP, Matrix.mul_one, smul_add, two_mul, add_smul]
    abel
  · intro a
    rw [AddMonoidHom.add_apply, Matrix.trace_add, hd.tr, heD, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
      hPQ, Matrix.one_mul, Matrix.trace_transpose, hd.tr, htS, two_mul, add_smul]
  · intro a
    simp only [AddMonoidHom.add_apply, heD, hss, Matrix.transpose_add, Matrix.transpose_mul,
      Matrix.transpose_transpose, hPbt, hQt, Matrix.mul_add, Matrix.add_mul, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, hee, one_smul, Matrix.mul_assoc, hPQ', hPQ, hQP, hQP', Matrix.mul_one]
    abel
end
