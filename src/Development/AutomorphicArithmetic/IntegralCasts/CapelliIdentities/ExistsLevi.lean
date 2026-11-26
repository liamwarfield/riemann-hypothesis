module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsHermRingRat

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HermitianProjectionEq
theorem UpperTheory.hermitian_projection_eq :
    ∀ {S : Type} [CommRing S] {n r : ℕ}
        (g P m : Matrix (Fin n) (Fin n) S) (X Y : Matrix (Fin n) (Fin r) S)
        (B C : Matrix (Fin r) (Fin r) S) (Xd Yd : Matrix (Fin r) (Fin n) S) (d e : Fin r → S),
        Xd * X = 0 → Yd * Y = 0 → Xd * Y = 1 → Yd * X = 1 →
        B.BlockTriangular id → g * X = X * B → Xd * g = C * Xd →
        (∀ i, d i = B i i) → (∀ i, IsUnit (d i)) →
        P = 1 - X * Yd - Y * Xd →
        m = (X * Matrix.diagonal d) * Yd + (Y * Matrix.diagonal e) * Xd + P * g * P →
        IsUnit m.det →
        (∃ B' : Matrix (Fin r) (Fin r) S, B'.BlockTriangular id ∧ (∀ i, B' i i = 1) ∧
            m⁻¹ * g * X = X * B') ∧
          ∀ z : Fin n → S, Xd.mulVec z = 0 →
            ∃ a : Fin r → S, (m⁻¹ * g - 1).mulVec z = X.mulVec a := by
  intro S _ n r g P m X Y B C Xd Yd d e hXdX hYdY hXdY hYdX hB hgX hXdg hd hu hP hm hdet
  have hmm : m⁻¹ * m = 1 := Matrix.nonsing_inv_mul m hdet
  obtain ⟨f, hf⟩ : ∃ f : Fin r → S, ∀ i, f i * d i = 1 :=
    ⟨fun i => (((hu i).unit⁻¹ : Sˣ) : S), fun i => (hu i).val_inv_mul⟩
  have hDF : Matrix.diagonal d * Matrix.diagonal f = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [mul_comm]
    exact hf i
  have hPX : P * X = 0 := by
    rw [hP, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc X, Matrix.mul_assoc Y, hYdX, hXdX,
      Matrix.mul_one, Matrix.mul_zero, sub_self, sub_zero]
  have hmX : m * X = X * Matrix.diagonal d := by
    rw [hm, Matrix.add_mul, Matrix.add_mul, Matrix.mul_assoc _ Yd, Matrix.mul_assoc _ Xd, hYdX, hXdX,
      Matrix.mul_assoc _ P, hPX, Matrix.mul_one, Matrix.mul_zero, Matrix.mul_zero, add_zero,
      add_zero]
  have hinvX : m⁻¹ * X = X * Matrix.diagonal f := by
    calc m⁻¹ * X = m⁻¹ * (X * (Matrix.diagonal d * Matrix.diagonal f)) := by
          rw [hDF, Matrix.mul_one]
      _ = (m⁻¹ * m) * (X * Matrix.diagonal f) := by
          rw [← Matrix.mul_assoc X, ← hmX, Matrix.mul_assoc m, Matrix.mul_assoc m⁻¹]
      _ = X * Matrix.diagonal f := by rw [hmm, Matrix.one_mul]
  have hPgX : P * g * X = 0 := by
    rw [Matrix.mul_assoc, hgX, ← Matrix.mul_assoc, hPX, Matrix.zero_mul]
  have hPg : P * g = g - X * (Yd * g) - Y * C * Xd := by
    rw [hP, sub_mul, sub_mul, Matrix.one_mul, Matrix.mul_assoc X, Matrix.mul_assoc Y, hXdg,
      Matrix.mul_assoc Y]
  have hPgP : P * g * P = P * g - P * g * Y * Xd := by
    have h0 : P * g * P = P * g * (1 - X * Yd - Y * Xd) := by rw [← hP]
    rw [h0, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc _ X, hPgX,
      Matrix.zero_mul, sub_zero, ← Matrix.mul_assoc _ Y]
  have hid : g - m = X * (Yd * g - Matrix.diagonal d * Yd)
      + (Y * C - Y * Matrix.diagonal e + P * g * Y) * Xd := by
    rw [hm, hPgP, hPg]
    simp only [Matrix.mul_sub, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc]
    abel
  refine ⟨⟨Matrix.diagonal f * B, ?_, ?_, ?_⟩, ?_⟩
  · intro i j hij
    rw [Matrix.diagonal_mul, hB hij, mul_zero]
  · intro i
    rw [Matrix.diagonal_mul, ← hd i]
    exact hf i
  · rw [Matrix.mul_assoc, hgX, ← Matrix.mul_assoc, hinvX, Matrix.mul_assoc]
  · intro z hz
    refine ⟨(Matrix.diagonal f * (Yd * g - Matrix.diagonal d * Yd)).mulVec z, ?_⟩
    have h1 : m⁻¹ * g - 1 = (X * Matrix.diagonal f) * (Yd * g - Matrix.diagonal d * Yd)
        + m⁻¹ * (Y * C - Y * Matrix.diagonal e + P * g * Y) * Xd := by
      calc m⁻¹ * g - 1 = m⁻¹ * (g - m) := by rw [Matrix.mul_sub, hmm]
        _ = _ := by
          rw [hid, Matrix.mul_add, ← Matrix.mul_assoc, hinvX, ← Matrix.mul_assoc]
    rw [h1, Matrix.add_mulVec, ← Matrix.mulVec_mulVec z _ Xd, hz, Matrix.mulVec_zero, add_zero,
      Matrix.mul_assoc X, Matrix.mulVec_mulVec]
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HermitianBlockDiagonal
private lemma ad_mul {S : Type} [CommRing S] (τ : S →+* S) {a b c : ℕ}
    (A : Matrix (Fin a) (Fin b) S) (B : Matrix (Fin b) (Fin c) S) :
    ((A * B).map τ).transpose = (B.map τ).transpose * (A.map τ).transpose := by
  rw [Matrix.map_mul, Matrix.transpose_mul]

private lemma ad_add {S : Type} [CommRing S] (τ : S →+* S) {a b : ℕ}
    (A B : Matrix (Fin a) (Fin b) S) :
    ((A + B).map τ).transpose = (A.map τ).transpose + (B.map τ).transpose := by
  ext i j
  simp

private lemma ad_ad {S : Type} [CommRing S] (τ : S →+* S) (hτ : ∀ x, τ (τ x) = x) {a b : ℕ}
    (A : Matrix (Fin a) (Fin b) S) :
    (((A.map τ).transpose).map τ).transpose = A := by
  ext i j
  simp [hτ]

private lemma ad_one {S : Type} [CommRing S] (τ : S →+* S) {a : ℕ} :
    (((1 : Matrix (Fin a) (Fin a) S)).map τ).transpose = 1 := by
  rw [Matrix.map_one τ (map_zero τ) (map_one τ), Matrix.transpose_one]

private lemma ad_diag_mul {S : Type} [CommRing S] (τ : S →+* S) {r : ℕ} (u v : Fin r → S)
    (h : ∀ i, τ (u i) * v i = 1) :
    ((Matrix.diagonal u).map τ).transpose * Matrix.diagonal v = 1 := by
  rw [Matrix.diagonal_map (map_zero τ), Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  exact h i

theorem UpperTheory.hermitian_block_diagonal :
    ∀ {S : Type} [CommRing S] (τ : S →+* S), (∀ x, τ (τ x) = x) → ∀ {n r : ℕ}
        (J g P m : Matrix (Fin n) (Fin n) S) (X Y : Matrix (Fin n) (Fin r) S)
        (C : Matrix (Fin r) (Fin r) S) (Xd Yd : Matrix (Fin r) (Fin n) S) (d e : Fin r → S),
        (J.map τ).transpose = J → IsUnit J.det →
        Xd = (X.map τ).transpose * J → Yd = (Y.map τ).transpose * J →
        Xd * X = 0 → Yd * Y = 0 → Xd * Y = 1 →
        (g.map τ).transpose * J * g = J →
        Xd * g = C * Xd →
        (∀ i, τ (e i) * d i = 1) →
        P = 1 - X * Yd - Y * Xd →
        m = (X * Matrix.diagonal d) * Yd + (Y * Matrix.diagonal e) * Xd + P * g * P →
        IsUnit m.det ∧ (m.map τ).transpose * J * m = J ∧
          m * X = X * Matrix.diagonal d ∧ m * Y = Y * Matrix.diagonal e := by
  intro S _ τ hτ n r J g P m X Y C Xd Yd d e hJ hdet hXd hYd hXX hYY hXY hg hC hde hP hm
  have adXd : (Xd.map τ).transpose = J * X := by rw [hXd, ad_mul, hJ, ad_ad τ hτ]
  have adYd : (Yd.map τ).transpose = J * Y := by rw [hYd, ad_mul, hJ, ad_ad τ hτ]
  have hYX : Yd * X = 1 := by
    have h := congrArg (fun A => (A.map τ).transpose) hXY
    simp only [ad_mul, adXd, ad_one] at h
    rw [hYd, Matrix.mul_assoc, h]
  have hed : ((Matrix.diagonal e).map τ).transpose * Matrix.diagonal d = 1 :=
    ad_diag_mul τ e d hde
  have hdeD : ((Matrix.diagonal d).map τ).transpose * Matrix.diagonal e = 1 :=
    ad_diag_mul τ d e (fun i => by
      have h := congrArg τ (hde i)
      rw [map_mul, hτ, map_one, mul_comm] at h
      exact h)
  have XX : ∀ {k : ℕ} (A : Matrix (Fin r) (Fin k) S), Xd * (X * A) = 0 := fun A => by
    rw [← Matrix.mul_assoc, hXX, Matrix.zero_mul]
  have YY : ∀ {k : ℕ} (A : Matrix (Fin r) (Fin k) S), Yd * (Y * A) = 0 := fun A => by
    rw [← Matrix.mul_assoc, hYY, Matrix.zero_mul]
  have XY : ∀ {k : ℕ} (A : Matrix (Fin r) (Fin k) S), Xd * (Y * A) = A := fun A => by
    rw [← Matrix.mul_assoc, hXY, Matrix.one_mul]
  have YX : ∀ {k : ℕ} (A : Matrix (Fin r) (Fin k) S), Yd * (X * A) = A := fun A => by
    rw [← Matrix.mul_assoc, hYX, Matrix.one_mul]
  have PX : P * X = 0 := by
    rw [hP]
    simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hYX, hXX, Matrix.mul_one,
      Matrix.mul_zero, sub_self, sub_zero]
  have PY : P * Y = 0 := by
    rw [hP]
    simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hYY, hXY, Matrix.mul_one,
      Matrix.mul_zero, sub_zero, sub_self]
  have XdP : Xd * P = 0 := by
    rw [hP]
    simp only [Matrix.mul_sub, Matrix.mul_one, XX, XY, sub_zero, sub_self]
  have YdP : Yd * P = 0 := by
    rw [hP]
    simp only [Matrix.mul_sub, Matrix.mul_one, YX, YY, sub_zero, sub_self]
  have PP : P * P = P := by
    calc P * P = (1 - X * Yd - Y * Xd) * P := by rw [← hP]
      _ = P := by
        simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, YdP, XdP, Matrix.mul_zero,
          sub_zero]
  have PX' : ∀ {k : ℕ} (A : Matrix (Fin r) (Fin k) S), P * (X * A) = 0 := fun A => by
    rw [← Matrix.mul_assoc, PX, Matrix.zero_mul]
  have PY' : ∀ {k : ℕ} (A : Matrix (Fin r) (Fin k) S), P * (Y * A) = 0 := fun A => by
    rw [← Matrix.mul_assoc, PY, Matrix.zero_mul]
  have XdP' : ∀ {k : ℕ} (A : Matrix (Fin n) (Fin k) S), Xd * (P * A) = 0 := fun A => by
    rw [← Matrix.mul_assoc, XdP, Matrix.zero_mul]
  have YdP' : ∀ {k : ℕ} (A : Matrix (Fin n) (Fin k) S), Yd * (P * A) = 0 := fun A => by
    rw [← Matrix.mul_assoc, YdP, Matrix.zero_mul]
  have PP' : ∀ {k : ℕ} (A : Matrix (Fin n) (Fin k) S), P * (P * A) = P * A := fun A => by
    rw [← Matrix.mul_assoc, PP]
  have hed' : ∀ {k : ℕ} (A : Matrix (Fin r) (Fin k) S),
      ((Matrix.diagonal e).map τ).transpose * (Matrix.diagonal d * A) = A := fun A => by
    rw [← Matrix.mul_assoc, hed, Matrix.one_mul]
  have hde' : ∀ {k : ℕ} (A : Matrix (Fin r) (Fin k) S),
      ((Matrix.diagonal d).map τ).transpose * (Matrix.diagonal e * A) = A := fun A => by
    rw [← Matrix.mul_assoc, hdeD, Matrix.one_mul]
  have hmX : m * X = X * Matrix.diagonal d := by
    rw [hm]
    simp only [Matrix.add_mul, Matrix.mul_assoc, hYX, hXX, PX, Matrix.mul_one, Matrix.mul_zero,
      add_zero]
  have hmY : m * Y = Y * Matrix.diagonal e := by
    rw [hm]
    simp only [Matrix.add_mul, Matrix.mul_assoc, hYY, hXY, PY, Matrix.mul_one, Matrix.mul_zero,
      add_zero, zero_add]
  have hPJ : (P.map τ).transpose * J = J * P := by
    have hPe : P + X * Yd + Y * Xd = 1 := by rw [hP]; abel
    have h := congrArg (fun A => (A.map τ).transpose) hPe
    simp only [ad_add, ad_mul, adXd, adYd, ad_one] at h
    have h2 : (P.map τ).transpose = 1 - (J * Y) * (X.map τ).transpose
        - (J * X) * (Y.map τ).transpose := by
      rw [← h]; abel
    rw [h2, hP]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc,
      ← hXd, ← hYd]
    abel
  have hPJ' : ∀ {k : ℕ} (A : Matrix (Fin n) (Fin k) S),
      (P.map τ).transpose * (J * A) = J * (P * A) := fun A => by
    rw [← Matrix.mul_assoc, hPJ, Matrix.mul_assoc]
  have hg' : ∀ {k : ℕ} (A : Matrix (Fin n) (Fin k) S),
      (g.map τ).transpose * (J * (g * A)) = J * A := fun A => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hg]
  have hgX : (g.map τ).transpose * (J * X) = J * (X * (C.map τ).transpose) := by
    have h := congrArg (fun A => (A.map τ).transpose) hC
    simp only [ad_mul, adXd] at h
    rw [h, Matrix.mul_assoc]
  have hgX' : ∀ {k : ℕ} (A : Matrix (Fin r) (Fin k) S),
      (g.map τ).transpose * (J * (X * A)) = J * (X * ((C.map τ).transpose * A)) := fun A => by
    rw [← Matrix.mul_assoc J X A, ← Matrix.mul_assoc, hgX]
    simp only [Matrix.mul_assoc]
  have hC' : ∀ {k : ℕ} (A : Matrix (Fin n) (Fin k) S), Xd * (g * A) = C * (Xd * A) := fun A => by
    rw [← Matrix.mul_assoc, hC, Matrix.mul_assoc]
  have hmid : (g.map τ).transpose * (J * (P * (g * P))) =
      J * P - J * (X * ((C.map τ).transpose * (Yd * (g * P)))) := by
    have hexp : ∀ {k : ℕ} (A : Matrix (Fin n) (Fin k) S),
        P * A = A - X * (Yd * A) - Y * (Xd * A) := fun A => by
      rw [hP]
      simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
    rw [hexp (g * P)]
    simp only [Matrix.mul_sub, hg', hgX', hC', XdP, Matrix.mul_zero, sub_zero]
  have hadm : (m.map τ).transpose =
      (J * Y) * (((Matrix.diagonal d).map τ).transpose * (X.map τ).transpose)
        + (J * X) * (((Matrix.diagonal e).map τ).transpose * (Y.map τ).transpose)
        + (P.map τ).transpose * ((g.map τ).transpose * (P.map τ).transpose) := by
    rw [hm]
    simp only [ad_add, ad_mul, adXd, adYd, Matrix.mul_assoc]
  have hiso : (m.map τ).transpose * J * m = J := by
    have hmJ : (m.map τ).transpose * J =
        J * (Y * (((Matrix.diagonal d).map τ).transpose * Xd))
          + J * (X * (((Matrix.diagonal e).map τ).transpose * Yd))
          + (P.map τ).transpose * ((g.map τ).transpose * (J * P)) := by
      rw [hadm, hXd, hYd]
      simp only [Matrix.add_mul, Matrix.mul_assoc, hPJ]
    rw [hmJ]
    conv_lhs => rw [hm]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, XX, XY, YX, YY, XdP', YdP',
      PX', PY', PP', XdP, YdP, hed', hde', Matrix.mul_zero, add_zero, zero_add, hmid,
      Matrix.mul_sub, hPJ', PP]
    conv_rhs => rw [show J = J * (1 : Matrix (Fin n) (Fin n) S) from (Matrix.mul_one J).symm]
    rw [show (1 : Matrix (Fin n) (Fin n) S) = P + X * Yd + Y * Xd by rw [hP]; abel]
    simp only [Matrix.mul_add]
    abel
  refine ⟨?_, hiso, hmX, hmY⟩
  have h := congrArg Matrix.det hiso
  rw [Matrix.det_mul] at h
  rw [← h] at hdet
  exact isUnit_of_mul_isUnit_right hdet
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HermitianBlockTriangular
theorem UpperTheory.hermitian_block_triangular :
    ∀ {S : Type} [CommRing S] (τ : S →+* S), (∀ x, τ (τ x) = x) → ∀ {n r : ℕ}
        (J g : Matrix (Fin n) (Fin n) S) (X Y : Matrix (Fin n) (Fin r) S)
        (B : Matrix (Fin r) (Fin r) S) (Xd Yd : Matrix (Fin r) (Fin n) S),
        (J.map τ).transpose = J →
        Xd = (X.map τ).transpose * J → Yd = (Y.map τ).transpose * J →
        Xd * Y = 1 →
        (g.map τ).transpose * J * g = J →
        B.BlockTriangular id → g * X = X * B →
        Yd * X = 1 ∧ Yd * g * X = B ∧ Xd * g = (Xd * g * Y) * Xd ∧
          ∀ i, τ ((Xd * g * Y) i i) * B i i = 1 := by
  intro S _ τ hτ n r J g X Y B Xd Yd hJ hXd hYd hXY hg hB hgX
  classical
  have star_mul : ∀ {a b c : ℕ} (P : Matrix (Fin a) (Fin b) S) (Q : Matrix (Fin b) (Fin c) S),
      ((P * Q).map τ).transpose = (Q.map τ).transpose * (P.map τ).transpose := by
    intro a b c P Q
    rw [Matrix.map_mul, Matrix.transpose_mul]
  have star_star : ∀ {a b : ℕ} (P : Matrix (Fin a) (Fin b) S),
      (((P.map τ).transpose).map τ).transpose = P := by
    intro a b P
    ext i j
    simp [hτ]
  have star_one : (((1 : Matrix (Fin r) (Fin r) S)).map τ).transpose = 1 := by
    rw [Matrix.map_one τ (map_zero τ) (map_one τ), Matrix.transpose_one]
  have h1 : Yd * X = 1 := by
    have h := congrArg (fun M : Matrix (Fin r) (Fin r) S => (M.map τ).transpose) hXY
    simp only [star_one] at h
    rw [star_mul, hXd, star_mul, star_star, hJ, ← Matrix.mul_assoc, ← hYd] at h
    exact h
  have h2 : Yd * g * X = B := by
    rw [Matrix.mul_assoc, hgX, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hs : (X.map τ).transpose * (g.map τ).transpose
      = (B.map τ).transpose * (X.map τ).transpose := by
    rw [← star_mul, ← star_mul, hgX]
  have hD : (B.map τ).transpose * (Xd * g) = Xd := by
    calc (B.map τ).transpose * (Xd * g)
        = ((B.map τ).transpose * (X.map τ).transpose) * J * g := by
          rw [hXd]; simp only [Matrix.mul_assoc]
      _ = (X.map τ).transpose * ((g.map τ).transpose * J * g) := by
          rw [← hs]; simp only [Matrix.mul_assoc]
      _ = Xd := by rw [hg, hXd]
  have hC : (B.map τ).transpose * (Xd * g * Y) = 1 := by
    rw [← Matrix.mul_assoc, hD, hXY]
  have hC' : (Xd * g * Y) * (B.map τ).transpose = 1 := mul_eq_one_comm.mp hC
  have h3 : Xd * g = (Xd * g * Y) * Xd := by
    calc Xd * g = ((Xd * g * Y) * (B.map τ).transpose) * (Xd * g) := by
          rw [hC', Matrix.one_mul]
      _ = (Xd * g * Y) * ((B.map τ).transpose * (Xd * g)) := by rw [Matrix.mul_assoc]
      _ = (Xd * g * Y) * Xd := by rw [hD]
  have h4 : ((Xd * g * Y).map τ).transpose * B = 1 := by
    have h := congrArg (fun M : Matrix (Fin r) (Fin r) S => (M.map τ).transpose) hC
    simp only [star_one] at h
    rwa [star_mul, star_star] at h
  refine ⟨h1, h2, h3, fun i => ?_⟩
  letI : Invertible B := invertibleOfLeftInverse B _ h4
  have hinv : (B⁻¹) = ((Xd * g * Y).map τ).transpose := Matrix.inv_eq_left_inv h4
  have htri : (B⁻¹).BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hB
  have h5 := congrFun (congrFun h4 i) i
  rw [Matrix.mul_apply, Finset.sum_eq_single i] at h5
  · simpa only [Matrix.transpose_apply, Matrix.map_apply, Matrix.one_apply_eq] using h5
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with hlt | hgt
    · have : (B⁻¹) i k = 0 := htri hlt
      rw [hinv] at this
      rw [this, zero_mul]
    · have : B k i = 0 := hB hgt
      rw [this, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h
end

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes in
private theorem sigma_sq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨_, _, _, hs⟩ := h
  let t : E →+* ℂ := (IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom
  apply t.injective
  rw [hs, hs, star_star]

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes in
private theorem sigR_sq {F E : Type} [Field F] [Field E] [Algebra F E] (A : Type) [CommRing A] [Algebra F A]
    {σ : E →ₐ[F] E} (h : ∀ x, σ (σ x) = x) (x : TensorProduct F A E) :
    sigR A σ (sigR A σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [sigR, h]
  | add a b ha hb => simp [ha, hb]

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes in
private theorem sigR_incl {F E : Type} [Field F] [Field E] [Algebra F E] (A : Type) [CommRing A] [Algebra F A]
    (σ : E →ₐ[F] E) (e : E) : sigR A σ (inclR A e) = inclR A (σ e) := by
  simp [sigR, inclR]

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes in
private theorem dual_map {F E : Type} [Field F] [Field E] [Algebra F E] (A : Type) [CommRing A] [Algebra F A]
    (σ : E →ₐ[F] E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (X : Matrix (Fin n) (Fin r) E) :
    (Formalism.UG.cT (↑σ : E →+* E) X * J).map (inclR A) =
      ((X.map (inclR A)).map (sigR A σ)).transpose * JR A J := by
  rw [Matrix.map_mul]
  congr 1

theorem UpperTheory.Reformulated.B.Gka3.exists_levi :
    ∀ {F E : Type} [inst : Field F] [inst_1 : NumberField F] [inst_2 : Field E] [inst_3 : NumberField E]
      [inst_4 : Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ}
      {X Y : Matrix (Fin n) (Fin r) E},
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ →
        Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsHermND σ J →
          GlobalTheory.SiegelSet.IsWittFrame σ J X Y →
            ∀ (A : Type) [inst_5 : CommRing A] [inst_6 : Algebra F A] [TopologicalSpace A] (p : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA A σ J)
              (B : Matrix (Fin r) (Fin r) (TensorProduct F A E)),
              B.BlockTriangular id →
                (↑((GlobalTheory.AdelicU.matHom A σ J : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA A σ J → GL (Fin n) (TensorProduct F A E)) p) :
                                 Matrix (Fin n) (Fin n) (TensorProduct F A E)) *
                      X.map (⇑(Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR A) : E → TensorProduct F A E) =
                    X.map (⇑(Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR A) : E → TensorProduct F A E) * B →
                  ∃ (m : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA A σ J),
                    (↑((GlobalTheory.AdelicU.matHom A σ J : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA A σ J → GL (Fin n) (TensorProduct F A E)) m) :
                          Matrix (Fin n) (Fin n) (TensorProduct F A E)) =
                        GlobalTheory.CompanionTheory.KFin.leviMat σ J A X Y
                          (↑((GlobalTheory.AdelicU.matHom A σ J : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA A σ J → GL (Fin n) (TensorProduct F A E)) p) :
                            Matrix (Fin n) (Fin n) (TensorProduct F A E)) ∧
                      (∃ (d : Fin r → TensorProduct F A E),
                          (↑((GlobalTheory.AdelicU.matHom A σ J : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA A σ J → GL (Fin n) (TensorProduct F A E)) m) :
                                Matrix (Fin n) (Fin n) (TensorProduct F A E)) *
                              X.map (⇑(Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR A) : E → TensorProduct F A E) =
                            X.map (⇑(Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR A) : E → TensorProduct F A E) * Matrix.diagonal d) ∧
                        (∃ (d' : Fin r → TensorProduct F A E),
                            (↑((GlobalTheory.AdelicU.matHom A σ J : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA A σ J → GL (Fin n) (TensorProduct F A E))
                                               m) :
                                  Matrix (Fin n) (Fin n) (TensorProduct F A E)) *
                                Y.map (⇑(Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR A) : E → TensorProduct F A E) =
                              Y.map (⇑(Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR A) : E → TensorProduct F A E) * Matrix.diagonal d') ∧
                          (∃ (B' : Matrix (Fin r) (Fin r) (TensorProduct F A E)),
                              B'.BlockTriangular id ∧
                                (∀ (i : Fin r), B' i i = (1 : TensorProduct F A E)) ∧
                                  (↑((GlobalTheory.AdelicU.matHom A σ J :
                                                       Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA A σ J → GL (Fin n) (TensorProduct F A E))
                                                     (m⁻¹ * p)) :
                                        Matrix (Fin n) (Fin n) (TensorProduct F A E)) *
                                      X.map (⇑(Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR A) : E → TensorProduct F A E) =
                                    X.map (⇑(Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR A) : E → TensorProduct F A E) * B') ∧
                            ∀ (z : Fin n → TensorProduct F A E),
                              ((Formalism.UG.cT (↑σ : E →+* E) X * J).map
                                              (⇑(Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR A) : E → TensorProduct F A E)).mulVec
                                          z =
                                  (0 : Fin r → TensorProduct F A E) →
                                ∃ (a : Fin r → TensorProduct F A E),
                                  ((↑((GlobalTheory.AdelicU.matHom A σ J :
                                                           Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA A σ J → GL (Fin n) (TensorProduct F A E))
                                                         (m⁻¹ * p)) :
                                                     Matrix (Fin n) (Fin n) (TensorProduct F A E)) -
                                                   (1 : Matrix (Fin n) (Fin n) (TensorProduct F A E))).mulVec
                                      z =
                                    (X.map (⇑(Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR A) : E → TensorProduct F A E)).mulVec a := by
  intro F E _ _ _ _ _ σ n J r X Y hCM hH hW A _ _ _ p B hB hpX
  obtain ⟨hXX, hYY, hXY, -⟩ := hW
  have hτ := sigR_sq A (sigma_sq hCM)
  let τ := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR A σ
  let ι := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (E := E) A
  let JA := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (F := F) A J
  let Xa := X.map ι
  let Ya := Y.map ι
  let Xd := (Formalism.UG.cT (↑σ : E →+* E) X * J).map ι
  let Yd := (Formalism.UG.cT (↑σ : E →+* E) Y * J).map ι
  let g : Matrix (Fin n) (Fin n) (TensorProduct F A E) := ↑(GlobalTheory.AdelicU.matHom A σ J p)
  have hXd : Xd = (Xa.map τ).transpose * JA := dual_map A σ J X
  have hYd : Yd = (Ya.map τ).transpose * JA := dual_map A σ J Y
  have hJh : (JA.map τ).transpose = JA := by
    ext i j
    simp only [JA, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR, Matrix.transpose_apply, Matrix.map_apply, τ]
    rw [sigR_incl]
    exact congrArg _ (hH.1 i j)
  have hJu : IsUnit JA.det := by
    have h1 : JA.det = ι J.det := (RingHom.map_det ι J).symm
    rw [h1]
    exact (isUnit_iff_ne_zero.mpr hH.2).map ι
  have hXX' : Xd * Xa = 0 := by
    simp only [Xd, Xa]
    rw [← Matrix.map_mul, hXX]
    simp
  have hYY' : Yd * Ya = 0 := by
    simp only [Yd, Ya]
    rw [← Matrix.map_mul, hYY]
    simp
  have hXY' : Xd * Ya = 1 := by
    simp only [Xd, Ya]
    rw [← Matrix.map_mul, hXY]
    simp
  have hgJ : (g.map τ).transpose * JA * g = JA := p.2
  obtain ⟨hYX, hYgX, hXg, hdiag⟩ := UpperTheory.hermitian_block_triangular τ hτ JA g Xa Ya B Xd Yd hJh hXd hYd hXY' hgJ hB hpX
  let d : Fin r → TensorProduct F A E := fun i => (Yd * g * Xa) i i
  let e : Fin r → TensorProduct F A E := fun i => (Xd * g * Ya) i i
  let P := 1 - Xa * Yd - Ya * Xd
  let M := GlobalTheory.CompanionTheory.KFin.leviMat σ J A X Y g
  have hM : M = (Xa * Matrix.diagonal d) * Yd + (Ya * Matrix.diagonal e) * Xd + P * g * P := rfl
  have hdB : ∀ i, d i = B i i := fun i => by simp only [d, hYgX]
  have hde : ∀ i, τ (e i) * d i = 1 := fun i => by rw [hdB]; exact hdiag i
  have hdu : ∀ i, IsUnit (d i) := fun i => IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact hde i)
  obtain ⟨hu, hun, hmX, hmY⟩ := UpperTheory.hermitian_block_diagonal τ hτ JA g P M Xa Ya (Xd * g * Ya) Xd Yd d e hJh hJu hXd hYd
    hXX' hYY' hXY' hgJ hXg hde rfl hM
  obtain ⟨⟨B', hB1, hB2, hB3⟩, hz⟩ := UpperTheory.hermitian_projection_eq g P M Xa Ya B (Xd * g * Ya) Xd Yd d e hXX' hYY' hXY' hYX
    hB hpX hXg hdB hdu rfl hM hu
  let m : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA A σ J := ⟨Matrix.nonsingInvUnit M hu, hun⟩
  have hmv : (↑(GlobalTheory.AdelicU.matHom A σ J m) : Matrix (Fin n) (Fin n) (TensorProduct F A E)) = M := rfl
  have hinv : (↑(GlobalTheory.AdelicU.matHom A σ J (m⁻¹ * p)) : Matrix (Fin n) (Fin n) (TensorProduct F A E)) = M⁻¹ * g := by
    rw [map_mul, map_inv, Units.val_mul, Matrix.coe_units_inv, hmv]
  refine ⟨m, rfl, ⟨d, hmX⟩, ⟨e, hmY⟩, ⟨B', hB1, hB2, ?_⟩, ?_⟩
  · rw [hinv]
    exact hB3
  · intro z hzz
    rw [hinv]
    exact hz z hzz
