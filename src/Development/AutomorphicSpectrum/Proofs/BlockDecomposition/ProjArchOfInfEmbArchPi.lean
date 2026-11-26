module

public import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointQuotMeas

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUnitaryCommuting
open Matrix
open scoped ComplexOrder InnerProductSpace

namespace GlobalTheory.CompanionTheory.WittIwasawa

section Eigen

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

noncomputable def halfProj (T : V →ₗ[ℂ] V) (s : ℂ) : V →ₗ[ℂ] V :=
  (1 / 2 : ℂ) • (LinearMap.id + s • T)

theorem halfProj_apply (T : V →ₗ[ℂ] V) (s : ℂ) (x : V) :
    halfProj T s x = (1 / 2 : ℂ) • (x + s • T x) := rfl

theorem map_halfProj {T : V →ₗ[ℂ] V} (hT2 : ∀ x, T (T x) = x) {s : ℂ} (hs2 : s * s = 1) (x : V) :
    T (halfProj T s x) = s • halfProj T s x := by
  have e : (s * s) • T x = T x := by rw [hs2, one_smul]
  simp only [halfProj_apply, map_smul, map_add (f := _), hT2]
  linear_combination (norm := module) (-1 / 2 : ℂ) • e

theorem halfProj_map {T : V →ₗ[ℂ] V} (hT2 : ∀ x, T (T x) = x) {s : ℂ} (hs2 : s * s = 1) (x : V) :
    halfProj T s (T x) = s • halfProj T s x := by
  have e : (s * s) • T x = T x := by rw [hs2, one_smul]
  simp only [halfProj_apply, hT2]
  linear_combination (norm := module) (-1 / 2 : ℂ) • e

theorem inner_halfProj {T : V →ₗ[ℂ] V} (hT : ∀ x y, ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ)
    (hT2 : ∀ x, T (T x) = x) {s : ℂ} (hs : star s = s) (hs2 : s * s = 1) (x y : V) :
    ⟪halfProj T s x, halfProj T s y⟫_ℂ = (1 / 2 : ℂ) * (⟪x, y⟫_ℂ + s * ⟪x, T y⟫_ℂ) := by
  have hs' : (starRingEnd ℂ) s = s := hs
  simp only [halfProj_apply, inner_smul_left, inner_smul_right, inner_add_left, inner_add_right,
    hs', hT x, hT2, map_div₀, map_one, map_ofNat]
  linear_combination (1 / 4 : ℂ) * ⟪x, y⟫_ℂ * hs2

variable [FiniteDimensional ℂ V]

theorem exists_half {α : Type*} {T : V →ₗ[ℂ] V} (hT : ∀ x y, ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ)
    (hT2 : ∀ x, T (T x) = x) {s : ℂ} (hs : star s = s) (hs2 : s * s = 1) (f g : α → V)
    (h1 : ∀ a b, ⟪f a, f b⟫_ℂ = ⟪g a, g b⟫_ℂ)
    (h2 : ∀ a b, ⟪f a, T (f b)⟫_ℂ = ⟪g a, T (g b)⟫_ℂ) :
    ∃ v : V →ₗ[ℂ] V, (∀ x y, ⟪v x, v y⟫_ℂ = ⟪halfProj T s x, halfProj T s y⟫_ℂ) ∧
      (∀ x, T (v x) = s • v x) ∧ (∀ x, v (T x) = s • v x) ∧
      ∀ a, v (f a) = halfProj T s (g a) := by
  set W : Submodule ℂ V := LinearMap.ker (T - s • LinearMap.id) with hW
  have hmem : ∀ x, halfProj T s x ∈ W := fun x => by
    rw [hW, LinearMap.mem_ker, LinearMap.sub_apply, map_halfProj hT2 hs2]
    simp
  let Q : V →ₗ[ℂ] W := LinearMap.codRestrict W (halfProj T s) hmem
  have hQ : ∀ x, (Q x : V) = halfProj T s x := fun x => rfl
  obtain ⟨w, hw⟩ := Formalism.L2.SG.Pf.Carrier.EnergyPfLoc.exists_linearIsometryEquiv_of_inner_eq
    (fun a => Q (f a)) (fun a => Q (g a)) (fun a b => by
      rw [Submodule.coe_inner, Submodule.coe_inner, hQ, hQ, hQ, hQ,
        inner_halfProj hT hT2 hs hs2, inner_halfProj hT hT2 hs hs2, h1, h2])
  refine ⟨W.subtype ∘ₗ w.toLinearEquiv.toLinearMap ∘ₗ Q, fun x y => ?_, fun x => ?_, fun x => ?_,
    fun a => ?_⟩
  · change ⟪(w (Q x) : V), (w (Q y) : V)⟫_ℂ = _
    rw [← Submodule.coe_inner, LinearIsometryEquiv.inner_map_map, Submodule.coe_inner, hQ, hQ]
  · change T (w (Q x) : V) = s • (w (Q x) : V)
    have := LinearMap.mem_ker.1 (w (Q x)).2
    rw [LinearMap.sub_apply] at this
    simpa [sub_eq_zero] using this
  · have : Q (T x) = s • Q x := Subtype.ext (by
      rw [hQ, Submodule.coe_smul, hQ, halfProj_map hT2 hs2])
    change (w (Q (T x)) : V) = s • (w (Q x) : V)
    rw [this, map_smul, Submodule.coe_smul]
  · change (w (Q (f a)) : V) = _
    rw [hw a, hQ]

theorem exists_commuting_of_gram {α : Type*} (T : V →ₗ[ℂ] V)
    (hT : ∀ x y, ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ) (hT2 : ∀ x, T (T x) = x) (f g : α → V)
    (h1 : ∀ a b, ⟪f a, f b⟫_ℂ = ⟪g a, g b⟫_ℂ)
    (h2 : ∀ a b, ⟪f a, T (f b)⟫_ℂ = ⟪g a, T (g b)⟫_ℂ) :
    ∃ u : V →ₗ[ℂ] V, (∀ x y, ⟪u x, u y⟫_ℂ = ⟪x, y⟫_ℂ) ∧ (∀ x, u (T x) = T (u x)) ∧
      ∀ a, u (f a) = g a := by
  obtain ⟨v, hv1, hv2, hv3, hv4⟩ := exists_half hT hT2 (s := 1) (by simp) (by simp) f g h1 h2
  obtain ⟨w, hw1, hw2, hw3, hw4⟩ := exists_half hT hT2 (s := -1) (by simp) (by simp) f g h1 h2
  have cross : ∀ x y, ⟪v x, w y⟫_ℂ = 0 := fun x y => by
    have e := hT (v x) (w y)
    rw [hv2, hw2, one_smul, inner_smul_right] at e
    have : (2 : ℂ) * ⟪v x, w y⟫_ℂ = 0 := by linear_combination e
    simpa using this
  have cross' : ∀ x y, ⟪w x, v y⟫_ℂ = 0 := fun x y => by
    rw [← inner_conj_symm, cross, map_zero]
  refine ⟨v + w, fun x y => ?_, fun x => ?_, fun a => ?_⟩
  · simp only [LinearMap.add_apply, inner_add_left, inner_add_right, cross, cross', hv1, hw1]
    rw [inner_halfProj hT hT2 (by simp) (by simp), inner_halfProj hT hT2 (by simp) (by simp)]
    ring
  · simp only [LinearMap.add_apply, map_add (f := _), hv2, hv3, hw2, hw3]
  · simp only [LinearMap.add_apply, hv4, hw4, halfProj_apply]
    module

end Eigen

section Columns

variable {n : ℕ} {κ : Type*}

noncomputable def col (A : Matrix (Fin n) κ ℂ) (a : κ) : EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 (fun i => A i a)

theorem gram_col {κ' : Type*} (A : Matrix (Fin n) κ ℂ) (B : Matrix (Fin n) κ' ℂ) (a : κ) (b : κ') :
    (Aᴴ * B) a b = ⟪col A a, col B b⟫_ℂ := by
  simp [col, Matrix.mul_apply, PiLp.inner_apply, mul_comm]

theorem toEuclideanLin_col (M : Matrix (Fin n) (Fin n) ℂ) (A : Matrix (Fin n) κ ℂ) (a : κ) :
    Matrix.toEuclideanLin M (col A a) = col (M * A) a := by
  ext i
  simp [col, Matrix.toLpLin_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct]

theorem col_injective {A B : Matrix (Fin n) κ ℂ} (h : ∀ a, col A a = col B a) : A = B := by
  ext i a
  simpa [col] using congrArg (fun v : EuclideanSpace ℂ (Fin n) => v i) (h a)

end Columns

theorem exists_unitary_commuting {n r : ℕ} (T : Matrix (Fin n) (Fin n) ℂ) (hT : T.IsHermitian)
    (hT2 : T * T = 1) (A A' : Matrix (Fin n) (Fin r) ℂ) (h1 : Aᴴ * A = A'ᴴ * A')
    (h2 : Aᴴ * (T * A) = A'ᴴ * (T * A')) :
    ∃ U : Matrix (Fin n) (Fin n) ℂ, Uᴴ * U = 1 ∧ U * T = T * U ∧ U * A = A' := by
  have hinv : ∀ x, Matrix.toEuclideanLin T (Matrix.toEuclideanLin T x) = x := fun x => by
    have e : ∀ y : EuclideanSpace ℂ (Fin n), y = col (Matrix.of fun i (_ : Unit) => y i) () :=
      fun y => by ext i; simp [col]
    rw [e x, toEuclideanLin_col, toEuclideanLin_col, ← Matrix.mul_assoc, hT2, Matrix.one_mul]
  obtain ⟨u, hu1, hu2, hu3⟩ := exists_commuting_of_gram (Matrix.toEuclideanLin T)
    (fun x y => (Matrix.isSymmetric_toEuclideanLin_iff.mpr hT) x y) hinv (col A) (col A')
    (fun a b => by rw [← gram_col, ← gram_col, h1])
    (fun a b => by rw [toEuclideanLin_col, toEuclideanLin_col, ← gram_col, ← gram_col, h2])
  set U : Matrix (Fin n) (Fin n) ℂ := Matrix.toEuclideanLin.symm u with hUdef
  have hU : ∀ x, u x = Matrix.toEuclideanLin U x := fun x => by simp [hUdef]
  have hcol : ∀ a, col U a = u (col (1 : Matrix (Fin n) (Fin n) ℂ) a) := fun a => by
    rw [hU, toEuclideanLin_col, Matrix.mul_one]
  refine ⟨U, ?_, col_injective fun a => ?_, col_injective fun a => ?_⟩
  · ext a b
    rw [gram_col, hcol, hcol, hu1, ← gram_col]
    simp
  · rw [← toEuclideanLin_col, ← toEuclideanLin_col, ← hU, hcol, ← hu2, toEuclideanLin_col,
      Matrix.mul_one]
  · rw [← toEuclideanLin_col, ← hU, hu3]

theorem exists_mem_K {n r : ℕ} (J P : Matrix (Fin n) (Fin n) ℂ) (X X' : Matrix (Fin n) (Fin r) ℂ)
    (hJ : J.IsHermitian) (hJu : IsUnit J.det) (hP : P.PosDef) (hPJ : P * J⁻¹ * P = J)
    (h1 : Xᴴ * P * X = X'ᴴ * P * X') (h2 : Xᴴ * J * X = X'ᴴ * J * X') :
    ∃ m mi : Matrix (Fin n) (Fin n) ℂ, m * mi = 1 ∧ mi * m = 1 ∧ mᴴ * J * m = J ∧
      mᴴ * P * m = P ∧ m * X = X' := by
  obtain ⟨R, -, hR⟩ := GroundTheory.Automorphic.exists_isUpperTriangular_conjTranspose_mul_self hP
  have hRu : IsUnit R.det := by
    have hd : IsUnit (Rᴴ * R).det := by rw [hR]; exact (Matrix.isUnit_iff_isUnit_det _).1 hP.isUnit
    rw [Matrix.det_mul] at hd
    exact isUnit_of_mul_isUnit_right hd
  have hRi : R⁻¹ * R = 1 := Matrix.nonsing_inv_mul R hRu
  have hRi' : R * R⁻¹ = 1 := Matrix.mul_nonsing_inv R hRu
  have hRiH : (R⁻¹)ᴴ * Rᴴ = 1 := by rw [← conjTranspose_mul, hRi', conjTranspose_one]
  have hJi : J * J⁻¹ = 1 := Matrix.mul_nonsing_inv J hJu
  have hJH : (J⁻¹)ᴴ = J⁻¹ := (hJ.inv).eq
  set T : Matrix (Fin n) (Fin n) ℂ := R * J⁻¹ * Rᴴ with hTdef
  have hTH : T.IsHermitian := by
    simp only [IsHermitian, hTdef, conjTranspose_mul, conjTranspose_conjTranspose, hJH,
      Matrix.mul_assoc]
  have hPW : Rᴴ * (R * (J⁻¹ * P * J⁻¹)) = 1 := by
    rw [← Matrix.mul_assoc, hR, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPJ, hJi]
  have hT2 : T * T = 1 := by
    have := mul_eq_one_comm.1 hPW
    calc T * T = R * J⁻¹ * (Rᴴ * R) * J⁻¹ * Rᴴ := by simp only [hTdef, Matrix.mul_assoc]
      _ = R * (J⁻¹ * P * J⁻¹) * Rᴴ := by rw [hR]; simp only [Matrix.mul_assoc]
      _ = 1 := this
  have hJT : Rᴴ * T * R = J := by
    calc Rᴴ * T * R = (Rᴴ * R) * J⁻¹ * (Rᴴ * R) := by simp only [hTdef, Matrix.mul_assoc]
      _ = J := by rw [hR, hPJ]
  have hgram : ∀ Z : Matrix (Fin n) (Fin r) ℂ, (R * Z)ᴴ * (R * Z) = Zᴴ * P * Z := fun Z => by
    rw [conjTranspose_mul, ← hR]; simp only [Matrix.mul_assoc]
  have hgramT : ∀ Z : Matrix (Fin n) (Fin r) ℂ, (R * Z)ᴴ * (T * (R * Z)) = Zᴴ * J * Z := fun Z => by
    rw [conjTranspose_mul, ← hJT]; simp only [Matrix.mul_assoc]
  obtain ⟨U, hU1, hU2, hU3⟩ := exists_unitary_commuting T hTH hT2 (R * X) (R * X')
    (by rw [hgram, hgram, h1]) (by rw [hgramT, hgramT, h2])
  have hU1' : U * Uᴴ = 1 := mul_eq_one_comm.1 hU1
  have hUT : Uᴴ * T * U = T := by rw [Matrix.mul_assoc, ← hU2, ← Matrix.mul_assoc, hU1, Matrix.one_mul]
  have hconj : ∀ M : Matrix (Fin n) (Fin n) ℂ,
      (R⁻¹ * U * R)ᴴ * (Rᴴ * M * R) * (R⁻¹ * U * R) = Rᴴ * (Uᴴ * M * U) * R := fun M => by
    simp only [conjTranspose_mul, conjTranspose_conjTranspose]
    calc Rᴴ * (Uᴴ * (R⁻¹)ᴴ) * (Rᴴ * M * R) * (R⁻¹ * U * R)
        = Rᴴ * Uᴴ * ((R⁻¹)ᴴ * Rᴴ) * M * (R * R⁻¹) * U * R := by simp only [Matrix.mul_assoc]
      _ = Rᴴ * (Uᴴ * M * U) * R := by rw [hRiH, hRi']; simp only [Matrix.mul_one, Matrix.mul_assoc]
  refine ⟨R⁻¹ * U * R, R⁻¹ * Uᴴ * R, ?_, ?_, ?_, ?_, ?_⟩
  · calc R⁻¹ * U * R * (R⁻¹ * Uᴴ * R) = R⁻¹ * U * (R * R⁻¹) * Uᴴ * R := by
          simp only [Matrix.mul_assoc]
      _ = R⁻¹ * (U * Uᴴ) * R := by rw [hRi']; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = 1 := by rw [hU1', Matrix.mul_one, hRi]
  · calc R⁻¹ * Uᴴ * R * (R⁻¹ * U * R) = R⁻¹ * Uᴴ * (R * R⁻¹) * U * R := by
          simp only [Matrix.mul_assoc]
      _ = R⁻¹ * (Uᴴ * U) * R := by rw [hRi']; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = 1 := by rw [hU1, Matrix.mul_one, hRi]
  · have := hconj T
    rwa [hJT, hUT, hJT] at this
  · have := hconj 1
    rw [Matrix.mul_one, hR, Matrix.mul_one, hU1, Matrix.mul_one, hR] at this
    exact this
  · calc R⁻¹ * U * R * X = R⁻¹ * (U * (R * X)) := by simp only [Matrix.mul_assoc]
      _ = X' := by rw [hU3, ← Matrix.mul_assoc, hRi, Matrix.one_mul]

theorem iwasawa_witt_flag : ∀ (n r : ℕ) (J P : Matrix (Fin n) (Fin n) ℂ)
    (X Y : Matrix (Fin n) (Fin r) ℂ), J.IsHermitian → IsUnit J.det → Xᴴ * J * X = 0 →
    Yᴴ * J * Y = 0 → Xᴴ * J * Y = 1 → P.PosDef → P * J⁻¹ * P = J → P * X = J * Y →
    ∀ g : Matrix (Fin n) (Fin n) ℂ, gᴴ * J * g = J →
    ∃ p k : Matrix (Fin n) (Fin n) ℂ, pᴴ * J * p = J ∧ kᴴ * J * k = J ∧ kᴴ * P * k = P ∧
      g = p * k ∧ ∃ B : Matrix (Fin r) (Fin r) ℂ, B.BlockTriangular id ∧ p * X = X * B := by
  intro n r J P X Y hJ hJu hXX _ hXY hP hPJ hPX g hg
  have hJi : J⁻¹ * J = 1 := Matrix.nonsing_inv_mul J hJu
  have hJH : Jᴴ = J := hJ.eq

  set gi : Matrix (Fin n) (Fin n) ℂ := J⁻¹ * gᴴ * J with hgi
  have hgig : gi * g = 1 := by
    calc gi * g = J⁻¹ * (gᴴ * J * g) := by simp only [hgi, Matrix.mul_assoc]
      _ = 1 := by rw [hg, hJi]
  have hggi : g * gi = 1 := mul_eq_one_comm.1 hgig
  have hgiH : giᴴ * gᴴ = 1 := by rw [← conjTranspose_mul, hggi, conjTranspose_one]
  have hgiJ : giᴴ * J * gi = J := by
    calc giᴴ * J * gi = giᴴ * (gᴴ * J * g) * gi := by rw [hg]
      _ = (giᴴ * gᴴ) * J * (g * gi) := by simp only [Matrix.mul_assoc]
      _ = J := by rw [hgiH, hggi, Matrix.one_mul, Matrix.mul_one]

  set Z : Matrix (Fin n) (Fin r) ℂ := gi * X with hZ
  have hZJ : Zᴴ * J * Z = 0 := by
    calc Zᴴ * J * Z = Xᴴ * (giᴴ * J * gi) * X := by
          simp only [hZ, conjTranspose_mul, Matrix.mul_assoc]
      _ = 0 := by rw [hgiJ, hXX]
  have hYX : Yᴴ * J * X = 1 := by
    have := congrArg conjTranspose hXY
    simpa only [conjTranspose_mul, conjTranspose_conjTranspose, hJH, conjTranspose_one,
      Matrix.mul_assoc] using this
  have hLZ : (Yᴴ * J * g) * Z = 1 := by
    calc (Yᴴ * J * g) * Z = Yᴴ * J * (g * gi) * X := by simp only [hZ, Matrix.mul_assoc]
      _ = 1 := by rw [hggi, Matrix.mul_one, hYX]
  have hZinj : Function.Injective Z.mulVec := fun a b hab => by
    have := congrArg (Matrix.mulVec (Yᴴ * J * g)) hab
    simpa only [Matrix.mulVec_mulVec, hLZ, Matrix.one_mulVec] using this
  have hG : (Zᴴ * P * Z).PosDef := hP.conjTranspose_mul_mul_same hZinj

  obtain ⟨R, hRt, hR⟩ := GroundTheory.Automorphic.exists_isUpperTriangular_conjTranspose_mul_self hG
  have hRu : IsUnit R.det := by
    have hd : IsUnit (Rᴴ * R).det := by rw [hR]; exact (Matrix.isUnit_iff_isUnit_det _).1 hG.isUnit
    rw [Matrix.det_mul] at hd
    exact isUnit_of_mul_isUnit_right hd
  letI := Matrix.invertibleOfIsUnitDet R hRu
  have hBt : (R⁻¹).BlockTriangular id := blockTriangular_inv_of_blockTriangular hRt
  have hRi' : R * R⁻¹ = 1 := Matrix.mul_nonsing_inv R hRu
  have hRiH : (R⁻¹)ᴴ * Rᴴ = 1 := by rw [← conjTranspose_mul, hRi', conjTranspose_one]
  have hX'P : (Z * R⁻¹)ᴴ * P * (Z * R⁻¹) = 1 := by
    calc (Z * R⁻¹)ᴴ * P * (Z * R⁻¹) = (R⁻¹)ᴴ * (Zᴴ * P * Z) * R⁻¹ := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = ((R⁻¹)ᴴ * Rᴴ) * (R * R⁻¹) := by rw [← hR]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hRiH, hRi', Matrix.one_mul]
  have hX'J : (Z * R⁻¹)ᴴ * J * (Z * R⁻¹) = 0 := by
    calc (Z * R⁻¹)ᴴ * J * (Z * R⁻¹) = (R⁻¹)ᴴ * (Zᴴ * J * Z) * R⁻¹ := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = 0 := by rw [hZJ, Matrix.mul_zero, Matrix.zero_mul]
  have hXP : Xᴴ * P * X = 1 := by rw [Matrix.mul_assoc, hPX, ← Matrix.mul_assoc, hXY]
  obtain ⟨m, mi, hm1, _, hmJ, hmP, hmX⟩ := exists_mem_K J P X (Z * R⁻¹) hJ hJu hP hPJ
    (by rw [hXP, hX'P]) (by rw [hXX, hX'J])
  have hmiH : miᴴ * mᴴ = 1 := by rw [← conjTranspose_mul, hm1, conjTranspose_one]
  have hinv : ∀ M : Matrix (Fin n) (Fin n) ℂ, mᴴ * M * m = M → miᴴ * M * mi = M := fun M hM => by
    calc miᴴ * M * mi = miᴴ * (mᴴ * M * m) * mi := by rw [hM]
      _ = (miᴴ * mᴴ) * M * (m * mi) := by simp only [Matrix.mul_assoc]
      _ = M := by rw [hmiH, hm1, Matrix.one_mul, Matrix.mul_one]
  refine ⟨g * m, mi, ?_, hinv J hmJ, hinv P hmP, ?_, R⁻¹, hBt, ?_⟩
  · calc (g * m)ᴴ * J * (g * m) = mᴴ * (gᴴ * J * g) * m := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = J := by rw [hg, hmJ]
  · rw [Matrix.mul_assoc, hm1, Matrix.mul_one]
  · calc g * m * X = g * (m * X) := Matrix.mul_assoc _ _ _
      _ = (g * gi) * X * R⁻¹ := by rw [hmX]; simp only [hZ, Matrix.mul_assoc]
      _ = X * R⁻¹ := by rw [hggi, Matrix.one_mul]

end GlobalTheory.CompanionTheory.WittIwasawa
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqDiagonalOfUpperTriangularOfUnitary
open Matrix
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.RealPlace

theorem eq_diagonal_of_upperTriangular_of_unitary {r : ℕ} (B : Matrix (Fin r) (Fin r) ℂ)
    (hB : B.BlockTriangular id) (hBB : Bᴴ * B = 1) : B = diagonal (fun i => B i i) := by
  have hinv : B⁻¹ = Bᴴ := Matrix.inv_eq_left_inv hBB
  haveI : Invertible B := Matrix.invertibleOfIsUnitDet B (Matrix.isUnit_det_of_left_inverse hBB)
  have hT : B⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hB
  rw [hinv] at hT
  ext i j
  rcases lt_trichotomy i j with h | rfl | h
  · have h1 : Bᴴ j i = 0 := hT h
    rw [Matrix.conjTranspose_apply, star_eq_zero] at h1
    rw [h1, Matrix.diagonal_apply_ne _ (ne_of_lt h)]
  · simp
  · rw [hB h, Matrix.diagonal_apply_ne _ (ne_of_gt h)]

theorem flag_isometry_diagonal_on_frame (n r : ℕ) (J P p : Matrix (Fin n) (Fin n) ℂ)
    (X Y : Matrix (Fin n) (Fin r) ℂ) (hJ : IsUnit J.det) (hXY : Xᴴ * J * Y = 1)
    (_hP : P.PosDef) (_hPJ : P * J⁻¹ * P = J) (hPX : P * X = J * Y)
    (hpJ : pᴴ * J * p = J) (hpP : pᴴ * P * p = P)
    (B : Matrix (Fin r) (Fin r) ℂ) (hB : B.BlockTriangular id) (hpX : p * X = X * B) :
    ∃ d : Fin r → ℂ, p * X = X * diagonal d ∧ p * Y = Y * diagonal d := by
  have hXPX : Xᴴ * P * X = 1 := by
    rw [Matrix.mul_assoc, hPX, ← Matrix.mul_assoc]
    exact hXY
  have hBB : Bᴴ * B = 1 := by
    calc Bᴴ * B = Bᴴ * (Xᴴ * P * X) * B := by rw [hXPX, Matrix.mul_one]
      _ = (X * B)ᴴ * P * (X * B) := by
          rw [Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = (p * X)ᴴ * P * (p * X) := by rw [hpX]
      _ = Xᴴ * (pᴴ * P * p) * X := by
          rw [Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [hpP]
          exact hXPX
  have hBd := eq_diagonal_of_upperTriangular_of_unitary B hB hBB
  obtain ⟨D, hD⟩ : ∃ D : Matrix (Fin r) (Fin r) ℂ, D = diagonal (fun i => B i i) := ⟨_, rfl⟩
  have hBD : B = D := hBd.trans hD.symm
  have hpXD : p * X = X * D := by
    rw [hpX, hBD]
  have hr : pᴴ * (J * p * J⁻¹) = 1 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hpJ, Matrix.mul_nonsing_inv J hJ]
  have hr' : (J * p * J⁻¹) * pᴴ = 1 := mul_eq_one_comm.mp hr
  have key : J * (p * Y) = J * (Y * D) := by
    calc J * (p * Y) = (J * p * J⁻¹) * pᴴ * (J * (p * Y)) := by rw [hr', Matrix.one_mul]
      _ = (J * p * J⁻¹) * (pᴴ * J * p) * Y := by simp only [Matrix.mul_assoc]
      _ = (J * p * J⁻¹) * (J * Y) := by
          rw [hpJ]
          simp only [Matrix.mul_assoc]
      _ = (J * p * J⁻¹) * (pᴴ * P * p * X) := by rw [hpP, hPX]
      _ = (J * p * J⁻¹) * pᴴ * (P * (p * X)) := by simp only [Matrix.mul_assoc]
      _ = (J * p * J⁻¹) * pᴴ * (P * X * D) := by
          rw [hpXD]
          simp only [Matrix.mul_assoc]
      _ = (J * p * J⁻¹) * pᴴ * (J * (Y * D)) := by
          rw [hPX]
          simp only [Matrix.mul_assoc]
      _ = J * (Y * D) := by rw [hr', Matrix.one_mul]
  have hpYD : p * Y = Y * D := by
    calc p * Y = J⁻¹ * (J * (p * Y)) := by
          simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul J hJ, Matrix.one_mul]
      _ = J⁻¹ * (J * (Y * D)) := by rw [key]
      _ = Y * D := by
          simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul J hJ, Matrix.one_mul]
  exact ⟨fun i => B i i, hD ▸ hpXD, hD ▸ hpYD⟩

end GlobalTheory.CompanionTheory.RealPlace
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsAdaptedMajorant
open Matrix
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.WittMajorant

variable {n : ℕ}

private theorem conj_mul (U V D E : Matrix (Fin n) (Fin n) ℂ) (h : V * U = 1) :
    (U * D * V) * (U * E * V) = U * (D * E) * V := by
  calc (U * D * V) * (U * E * V) = U * D * (V * U) * E * V := by
        simp only [Matrix.mul_assoc]
    _ = U * (D * E) * V := by
        rw [h]; simp only [Matrix.mul_one, Matrix.mul_assoc]

theorem exists_abs_sign {R : Matrix (Fin n) (Fin n) ℂ} (hR : R.IsHermitian) :
    ∃ A S : Matrix (Fin n) (Fin n) ℂ,
      A.PosSemidef ∧ A = S * R ∧ A = R * S ∧ S * S * R = R := by
  set U : Matrix (Fin n) (Fin n) ℂ := (hR.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  have hUU : Uᴴ * U = 1 := by
    have := Unitary.star_mul_self_of_mem hR.eigenvectorUnitary.2
    simpa [star_eq_conjTranspose] using this
  have hspec : R = U * diagonal (fun i => ((hR.eigenvalues i : ℝ) : ℂ)) * Uᴴ := by
    have := hR.spectral_theorem
    simpa [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose, Function.comp_def] using this
  set d : Fin n → ℂ := fun i => ((hR.eigenvalues i : ℝ) : ℂ) with hd
  set a : Fin n → ℂ := fun i => ((|hR.eigenvalues i| : ℝ) : ℂ) with ha
  set s : Fin n → ℂ := fun i => (((SignType.sign (hR.eigenvalues i) : SignType) : ℝ) : ℂ) with hs
  have hsd : ∀ i, s i * d i = a i := by
    intro i
    simp only [hs, hd, ha]
    rw [← Complex.ofReal_mul, sign_mul_self]
  have hds : ∀ i, d i * s i = a i := fun i => by rw [mul_comm, hsd]
  have hssd : ∀ i, s i * s i * d i = d i := by
    intro i
    simp only [hs, hd]
    rcases lt_trichotomy (hR.eigenvalues i) 0 with h | h | h
    · simp [sign_neg h]
    · simp [h]
    · simp [sign_pos h]
  refine ⟨U * diagonal a * Uᴴ, U * diagonal s * Uᴴ, ?_, ?_, ?_, ?_⟩
  · have h0 : (diagonal a).PosSemidef := by
      rw [posSemidef_diagonal_iff]
      intro i
      simp only [ha]
      exact_mod_cast abs_nonneg _
    have := h0.conjTranspose_mul_mul_same Uᴴ
    simpa using this
  · conv_rhs => rw [hspec]
    rw [conj_mul _ _ _ _ hUU, diagonal_mul_diagonal]
    simp only [hsd]
  · conv_rhs => rw [hspec]
    rw [conj_mul _ _ _ _ hUU, diagonal_mul_diagonal]
    simp only [hds]
  · conv_lhs => rw [hspec]
    rw [conj_mul _ _ _ _ hUU, conj_mul _ _ _ _ hUU, diagonal_mul_diagonal, diagonal_mul_diagonal]
    simp only [hssd]
    exact hspec.symm

theorem exists_adapted_majorant (n r : ℕ) (J : Matrix (Fin n) (Fin n) ℂ)
    (X Y : Matrix (Fin n) (Fin r) ℂ) (hJ : J.IsHermitian) (hdet : IsUnit J.det)
    (hXX : Xᴴ * J * X = 0) (hYY : Yᴴ * J * Y = 0) (hXY : Xᴴ * J * Y = 1) :
    ∃ P : Matrix (Fin n) (Fin n) ℂ, P.PosDef ∧ P * J⁻¹ * P = J ∧ P * X = J * Y := by
  have hJi : J⁻¹ * J = 1 := nonsing_inv_mul J hdet
  have hJi' : J * J⁻¹ = 1 := mul_nonsing_inv J hdet
  have hYX : Yᴴ * J * X = 1 := by
    have := congrArg conjTranspose hXY
    simpa [conjTranspose_mul, hJ.eq, Matrix.mul_assoc] using this
  have xx : Xᴴ * (J * X) = 0 := by rw [← Matrix.mul_assoc]; exact hXX
  have yy : Yᴴ * (J * Y) = 0 := by rw [← Matrix.mul_assoc]; exact hYY
  have xy : Xᴴ * (J * Y) = 1 := by rw [← Matrix.mul_assoc]; exact hXY
  have yx : Yᴴ * (J * X) = 1 := by rw [← Matrix.mul_assoc]; exact hYX
  set R : Matrix (Fin n) (Fin n) ℂ := J⁻¹ - X * Yᴴ - Y * Xᴴ with hRdef
  have hRh : R.IsHermitian := by
    have hi : (J⁻¹)ᴴ = J⁻¹ := (IsHermitian.inv hJ).eq
    unfold IsHermitian
    rw [hRdef, conjTranspose_sub, conjTranspose_sub, hi, conjTranspose_mul, conjTranspose_mul,
      conjTranspose_conjTranspose, conjTranspose_conjTranspose]
    abel
  have hRX : R * (J * X) = 0 := by
    rw [hRdef, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_assoc X, Matrix.mul_assoc Y, yx, xx,
      ← Matrix.mul_assoc J⁻¹, hJi]
    simp
  have hRY : R * (J * Y) = 0 := by
    rw [hRdef, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_assoc X, Matrix.mul_assoc Y, yy, xy,
      ← Matrix.mul_assoc J⁻¹, hJi]
    simp
  have hRJR : R * (J * R) = R := by
    have e : J * R = 1 - (J * X) * Yᴴ - (J * Y) * Xᴴ := by
      rw [hRdef, Matrix.mul_sub, Matrix.mul_sub, hJi', Matrix.mul_assoc, Matrix.mul_assoc]
    have e1 : R * (J * X * Yᴴ) = (R * (J * X)) * Yᴴ := (Matrix.mul_assoc _ _ _).symm
    have e2 : R * (J * Y * Xᴴ) = (R * (J * Y)) * Xᴴ := (Matrix.mul_assoc _ _ _).symm
    rw [e, Matrix.mul_sub, Matrix.mul_sub, e1, e2, hRX, hRY]
    simp
  obtain ⟨A, S, hA, hAS, hAR, hSSR⟩ := exists_abs_sign hRh
  have hAh : Aᴴ = A := hA.isHermitian.eq
  have hAX : A * (J * X) = 0 := by
    rw [hAS, Matrix.mul_assoc, hRX, Matrix.mul_zero]
  have hAY : A * (J * Y) = 0 := by
    rw [hAS, Matrix.mul_assoc, hRY, Matrix.mul_zero]
  have hXA : Xᴴ * (J * A) = 0 := by
    have := congrArg conjTranspose hAX
    simpa [conjTranspose_mul, hJ.eq, hAh, Matrix.mul_assoc] using this
  have hYA : Yᴴ * (J * A) = 0 := by
    have := congrArg conjTranspose hAY
    simpa [conjTranspose_mul, hJ.eq, hAh, Matrix.mul_assoc] using this
  have hAJA : A * (J * A) = R := by
    calc A * (J * A) = (S * R) * (J * (R * S)) := by rw [← hAS, ← hAR]
      _ = S * (R * (J * R)) * S := by simp only [Matrix.mul_assoc]
      _ = S * (R * S) := by rw [hRJR, Matrix.mul_assoc]
      _ = S * (S * R) := by rw [← hAR, hAS]
      _ = R := by rw [← Matrix.mul_assoc, hSSR]
  set T : Matrix (Fin n) (Fin n) ℂ := X * Xᴴ + Y * Yᴴ + A with hTdef
  have hTX : T * (J * X) = Y := by
    rw [hTdef, Matrix.add_mul, Matrix.add_mul, Matrix.mul_assoc X, Matrix.mul_assoc Y, xx, yx, hAX]
    simp
  have hTY : T * (J * Y) = X := by
    rw [hTdef, Matrix.add_mul, Matrix.add_mul, Matrix.mul_assoc X, Matrix.mul_assoc Y, xy, yy, hAY]
    simp
  have hTA : T * (J * A) = R := by
    rw [hTdef, Matrix.add_mul, Matrix.add_mul, Matrix.mul_assoc X, Matrix.mul_assoc Y, hXA, hYA,
      hAJA]
    simp
  have hTJT : T * (J * T) = J⁻¹ := by
    have e : J * T = (J * X) * Xᴴ + (J * Y) * Yᴴ + J * A := by
      rw [hTdef, Matrix.mul_add, Matrix.mul_add, Matrix.mul_assoc, Matrix.mul_assoc]
    have e1 : T * (J * X * Xᴴ) = (T * (J * X)) * Xᴴ := (Matrix.mul_assoc _ _ _).symm
    have e2 : T * (J * Y * Yᴴ) = (T * (J * Y)) * Yᴴ := (Matrix.mul_assoc _ _ _).symm
    rw [e, Matrix.mul_add, Matrix.mul_add, e1, e2, hTX, hTY, hTA, hRdef]
    abel
  have hTpsd : T.PosSemidef :=
    ((posSemidef_self_mul_conjTranspose X).add (posSemidef_self_mul_conjTranspose Y)).add hA
  have hTunit : IsUnit T := by
    have h1 : T * (J * T * J) = 1 := by
      calc T * (J * T * J) = (T * (J * T)) * J := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hTJT, hJi]
    exact (Matrix.isUnit_iff_isUnit_det T).2 (Matrix.isUnit_det_of_right_inverse h1)
  have hTpd : T.PosDef := hTpsd.posDef_iff_isUnit.2 hTunit
  have hJinj : Function.Injective J.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det J).2 hdet)
  refine ⟨J * T * J, ?_, ?_, ?_⟩
  · have := hTpd.conjTranspose_mul_mul_same hJinj
    rwa [hJ.eq] at this
  · calc J * T * J * J⁻¹ * (J * T * J) = J * (T * (J * T)) * J := by
          have h2 : J * T * J * J⁻¹ = J * T := by
            rw [Matrix.mul_assoc (J * T), hJi', Matrix.mul_one]
          rw [h2]
          simp only [Matrix.mul_assoc]
      _ = J := by rw [hTJT, hJi', Matrix.one_mul]
  · rw [Matrix.mul_assoc, Matrix.mul_assoc, hTX]

end GlobalTheory.CompanionTheory.WittMajorant
end

set_option linter.unusedSectionVars false

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal ComplexOrder

namespace GlobalTheory.CompanionTheory.SiegelArch

theorem isCompact_unitaryFn (n : ℕ) :
    IsCompact {U : Fin n → Fin n → ℂ | (Matrix.of U)ᴴ * Matrix.of U = 1} := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · have hc : Continuous fun U : Fin n → Fin n → ℂ => (Matrix.of U : Matrix (Fin n) (Fin n) ℂ) := continuous_id
    exact isClosed_eq (hc.matrix_conjTranspose.matrix_mul hc) continuous_const
  · refine (Metric.isBounded_closedBall (x := (0 : Fin n → Fin n → ℂ)) (r := 1)).subset fun U hU => ?_
    have hu : (Matrix.of U : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ :=
      Matrix.mem_unitaryGroup_iff'.2 hU
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro j
    exact entry_norm_bound_of_unitary hu i j

open scoped MatrixOrder Matrix.Norms.L2Operator in
theorem exists_factor {n : ℕ} {P : Matrix (Fin n) (Fin n) ℂ} (hP : P.PosSemidef) : ∃ B : Matrix (Fin n) (Fin n) ℂ, P = Bᴴ * B := by
  obtain ⟨y, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hP.nonneg
  exact ⟨y, rfl⟩

theorem isCompact_stabFn {n : ℕ} {P : Matrix (Fin n) (Fin n) ℂ} (hP : P.PosDef) :
    IsCompact {M : Fin n → Fin n → ℂ | (Matrix.of M)ᴴ * P * Matrix.of M = P} := by
  have hdet : P.det ≠ 0 := hP.det_pos.ne'
  obtain ⟨B, rfl⟩ := exists_factor hP.posSemidef
  have hB : IsUnit B.det := isUnit_iff_ne_zero.2 fun h => hdet (by rw [Matrix.det_mul, h, mul_zero])
  have hc : Continuous fun U : Fin n → Fin n → ℂ => (Matrix.of U : Matrix (Fin n) (Fin n) ℂ) := continuous_id
  have hcl : IsClosed {M : Fin n → Fin n → ℂ | (Matrix.of M)ᴴ * (Bᴴ * B) * Matrix.of M = Bᴴ * B} :=
    isClosed_eq ((hc.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul hc) continuous_const
  have hf : Continuous fun U : Fin n → Fin n → ℂ => ((B⁻¹ * Matrix.of U * B : Matrix (Fin n) (Fin n) ℂ) : Fin n → Fin n → ℂ) :=
    (continuous_const.matrix_mul hc).matrix_mul continuous_const
  refine ((isCompact_unitaryFn n).image hf).of_isClosed_subset hcl fun M hM => ?_
  have hM' : (Matrix.of M)ᴴ * (Bᴴ * B) * Matrix.of M = Bᴴ * B := hM
  refine ⟨(B * Matrix.of M * B⁻¹ : Matrix (Fin n) (Fin n) ℂ), ?_, ?_⟩
  · change (B * Matrix.of M * B⁻¹)ᴴ * (B * Matrix.of M * B⁻¹) = 1
    have h1 : (B * Matrix.of M * B⁻¹)ᴴ * (B * Matrix.of M * B⁻¹) =
        (B⁻¹)ᴴ * ((Matrix.of M)ᴴ * (Bᴴ * B) * Matrix.of M) * B⁻¹ := by
      simp only [conjTranspose_mul, Matrix.mul_assoc]
    have h2 : (B⁻¹)ᴴ * (Bᴴ * B) * B⁻¹ = (B * B⁻¹)ᴴ * (B * B⁻¹) := by
      simp only [conjTranspose_mul, Matrix.mul_assoc]
    rw [h1, hM', h2, Matrix.mul_nonsing_inv _ hB]
    simp
  · change B⁻¹ * (B * Matrix.of M * B⁻¹) * B = Matrix.of M
    have : B⁻¹ * (B * Matrix.of M * B⁻¹) * B = (B⁻¹ * B) * Matrix.of M * (B⁻¹ * B) := by
      simp only [Matrix.mul_assoc]
    rw [this, Matrix.nonsing_inv_mul _ hB]
    simp

theorem stab_inv {n : ℕ} {A A' P : Matrix (Fin n) (Fin n) ℂ} (h : A * A' = 1) (hA : Aᴴ * P * A = P) :
    A'ᴴ * P * A' = P := by
  have h1 : (A * A')ᴴ * P * (A * A') = A'ᴴ * (Aᴴ * P * A) * A' := by
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  rw [hA] at h1
  rw [← h1, h]
  simp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ} {w : InfinitePlace F}

theorem conjT_map (hcm : IsCMExt F E σ) (τ : E →+* ℂ) {a b : Type} (M : Matrix a b E) :
    (M.map τ)ᴴ = (cT (σ : E →+* E) M).map τ := by
  ext i j
  simp [cT, conjTranspose_apply, hcm.2.2.2 τ]

theorem cT_conj {a b : Type} (M : Matrix a b ℂ) : cT (starRingEnd ℂ) M = Mᴴ := by
  ext i j
  simp [cT, conjTranspose_apply]

theorem arch_unitary (hcm : IsCMExt F E σ) (τ : EmbOver E w) (y : GArch σ J w) :
    (archMat σ J τ y)ᴴ * J.map τ.1 * archMat σ J τ y = J.map τ.1 := by
  have h : cT (starRingEnd ℂ) (archEquiv J hcm τ y).1.1 * J.map τ.1 * (archEquiv J hcm τ y).1.1 = J.map τ.1 :=
    (archEquiv J hcm τ y).2
  rw [cT_conj] at h
  exact h

theorem det_map_ne (hdet : J.det ≠ 0) (τ : E →+* ℂ) : (J.map τ).det ≠ 0 := by
  have h : (J.map τ).det = τ J.det := (RingHom.map_det τ J).symm
  rw [h]
  exact (map_ne_zero τ).2 hdet

theorem exists_lift (hcm : IsCMExt F E σ) (hdet : J.det ≠ 0) (τ : EmbOver E w) {m : Matrix (Fin n) (Fin n) ℂ}
    (hm : mᴴ * J.map τ.1 * m = J.map τ.1) : ∃ y : GArch σ J w, archMat σ J τ y = m := by
  have hJ := det_map_ne J hdet τ.1
  have hd : m.det ≠ 0 := by
    intro h0
    have h := congrArg Matrix.det hm
    rw [Matrix.det_mul, h0, mul_zero] at h
    exact hJ h.symm
  let u : GL (Fin n) ℂ := Matrix.nonsingInvUnit m (isUnit_iff_ne_zero.2 hd)
  have hu : u ∈ Formalism.UG.UJ (starRingEnd ℂ) (J.map τ.1) := by
    change cT (starRingEnd ℂ) m * J.map τ.1 * m = J.map τ.1
    rw [cT_conj]
    exact hm
  refine ⟨(archEquiv J hcm τ).symm ⟨u, hu⟩, ?_⟩
  rw [GlobalTheory.Orb.archMat_eq_archEquiv J hcm, MulEquiv.apply_symm_apply]
  rfl

theorem archMat_injective (hcm : IsCMExt F E σ) (τ : EmbOver E w) : Function.Injective (archMat σ J τ) :=
  fun a b e => (GlobalTheory.Orb.isEmbedding_archMat J hcm τ).injective (congrArg (fun m i j => m i j) e)


variable (σ) in
def stabAt (τ : EmbOver E w) (P : Matrix (Fin n) (Fin n) ℂ) : Subgroup (GArch σ J w) where
  carrier := {y | (archMat σ J τ y)ᴴ * P * archMat σ J τ y = P}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    have ha' : (archMat σ J τ a)ᴴ * P * archMat σ J τ a = P := ha
    have hb' : (archMat σ J τ b)ᴴ * P * archMat σ J τ b = P := hb
    change (archMat σ J τ (a * b))ᴴ * P * archMat σ J τ (a * b) = P
    have h : (archMat σ J τ (a * b))ᴴ * P * archMat σ J τ (a * b) =
        (archMat σ J τ b)ᴴ * ((archMat σ J τ a)ᴴ * P * archMat σ J τ a) * archMat σ J τ b := by
      simp only [map_mul, conjTranspose_mul, Matrix.mul_assoc]
    rw [h, ha', hb']
  inv_mem' := by
    intro a ha
    exact stab_inv (A := archMat σ J τ a) (by rw [← map_mul, mul_inv_cancel, map_one]) ha

theorem isCompact_stabAt (hcm : IsCMExt F E σ) (hdet : J.det ≠ 0) (τ : EmbOver E w)
    {P : Matrix (Fin n) (Fin n) ℂ} (hP : P.PosDef) : IsCompact (stabAt σ J τ P : Set (GArch σ J w)) := by
  have hemb := GlobalTheory.Orb.isEmbedding_archMat J hcm τ
  rw [hemb.isInducing.isCompact_iff]
  have hc : Continuous fun U : Fin n → Fin n → ℂ => (Matrix.of U : Matrix (Fin n) (Fin n) ℂ) := continuous_id
  have hcl : IsClosed {M : Fin n → Fin n → ℂ | (Matrix.of M)ᴴ * J.map τ.1 * Matrix.of M = J.map τ.1} :=
    isClosed_eq ((hc.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul hc) continuous_const
  have himg : (fun y i j => archMat σ J τ y i j) '' (stabAt σ J τ P : Set (GArch σ J w)) =
      {M : Fin n → Fin n → ℂ | (Matrix.of M)ᴴ * P * Matrix.of M = P} ∩
        {M : Fin n → Fin n → ℂ | (Matrix.of M)ᴴ * J.map τ.1 * Matrix.of M = J.map τ.1} := by
    ext M
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hy, arch_unitary J hcm τ y⟩
    · rintro ⟨h1, h2⟩
      obtain ⟨y, hy⟩ := exists_lift J hcm hdet τ (m := Matrix.of M) h2
      refine ⟨y, ?_, ?_⟩
      · change (archMat σ J τ y)ᴴ * P * archMat σ J τ y = P
        rw [hy]
        exact h1
      · funext i j
        exact congrFun (congrFun hy i) j
  refine himg ▸ (isCompact_stabFn hP).inter_right hcl

def evC (τ : EmbOver E w) : AF F ⊗[F] E →+* ℂ := (infEmb τ).comp (compInf F E w)


variable (F E) in
def finPart : AF F ⊗[F] E →+* Af F ⊗[F] E := (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom

theorem map_evW_fst (w : InfinitePlace F) (z : AF F ⊗[F] E) :
    Algebra.TensorProduct.map (GlobalTheory.AutFunCompare.evW w) (AlgHom.id F E)
      (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) z) = compInf F E w z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a e => rfl

theorem tens_prod_ext {F E A B : Type} [Field F] [Field E] [Algebra F E] [CommRing A] [CommRing B] [Algebra F A]
    [Algebra F B] {z z' : (A × B) ⊗[F] E}
    (a : Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) z =
      Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) z')
    (b : Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) z =
      Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) z') : z = z' := by
  have hz : ∀ z : (A × B) ⊗[F] E, z = LinearMap.rTensor E (LinearMap.inl F A B)
        (Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) z) +
      LinearMap.rTensor E (LinearMap.inr F A B)
        (Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) z) := by
    intro z
    induction z with
    | tmul x y => simp [← TensorProduct.add_tmul]
    | add x y hx hy =>
      simp only [map_add (f := _)]
      rw [add_add_add_comm, ← hx, ← hy]
  rw [hz z, hz z', a, b]

theorem tens_ext (hcm : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) {z z' : AF F ⊗[F] E}
    (h : ∀ w, evC (τ w) z = evC (τ w) z') (h' : finPart F E z = finPart F E z') : z = z' := by
  have h1 : Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) z =
      Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) z' :=
    GlobalTheory.AutFunCompare.infTens_ext fun w => by
      rw [map_evW_fst, map_evW_fst]
      exact (infEmb_bijective hcm (τ w)).1 (h w)
  exact tens_prod_ext (A := Ainf F) (B := Af F) h1 h'

theorem tensMat_ext (hcm : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) {a b : Type}
    {A A' : Matrix a b (AF F ⊗[F] E)} (h : ∀ w, A.map (evC (τ w)) = A'.map (evC (τ w)))
    (h' : A.map (finPart F E) = A'.map (finPart F E)) : A = A' :=
  Matrix.ext fun i j => tens_ext hcm τ (fun w => congrFun (congrFun (h w) i) j) (congrFun (congrFun h' i) j)

theorem map_adMat {a b : Type} (τ : EmbOver E w) (M : Matrix a b E) : (adMat F M).map (evC τ) = M.map τ.1 := by
  ext i j
  change infEmb τ ((1 : w.Completion) ⊗ₜ[F] M i j) = _
  simp

theorem map_adMat_fin {a b : Type} (M : Matrix a b E) :
    (adMat F M).map (finPart F E) = M.map (inclR (F := F) (Af F)) := by
  ext i j
  change ((1 : Af F) ⊗ₜ[F] M i j) = _
  rfl

theorem map_matHom (τ : EmbOver E w) (g : GAd σ J) :
    (matHom _ σ J g).1.map (evC τ) = archMat σ J τ (projArch σ J w g) := rfl

theorem map_matHom_fin {g : GAd σ J} (hg : g ∈ infPts σ J) : (matHom _ σ J g).1.map (finPart F E) = 1 :=
  congrArg Units.val (MonoidHom.mem_ker.1 hg)

theorem frame_coeff (hcm : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) {g : GAd σ J} (hg : g ∈ infPts σ J)
    {Q : Matrix (Fin r) (Fin n) E} {X : Matrix (Fin n) (Fin r) E} (hQ : Q * X = 1)
    (h : ∀ w, ∃ Bw : Matrix (Fin r) (Fin r) ℂ,
      archMat σ J (τ w) (projArch σ J w g) * X.map (τ w).1 = X.map (τ w).1 * Bw) :
    ∃ B : Matrix (Fin r) (Fin r) (AF F ⊗[F] E), (matHom _ σ J g).1 * adMat F X = adMat F X * B ∧
      B.map (finPart F E) = 1 ∧ ∀ w (Bw : Matrix (Fin r) (Fin r) ℂ),
        archMat σ J (τ w) (projArch σ J w g) * X.map (τ w).1 = X.map (τ w).1 * Bw → B.map (evC (τ w)) = Bw := by
  have hinf : ∀ w (Bw : Matrix (Fin r) (Fin r) ℂ),
      archMat σ J (τ w) (projArch σ J w g) * X.map (τ w).1 = X.map (τ w).1 * Bw →
      (adMat F Q * (matHom _ σ J g).1 * adMat F X).map (evC (τ w)) = Bw := by
    intro w Bw hB
    rw [Matrix.map_mul, Matrix.map_mul, map_adMat, map_adMat, map_matHom, Matrix.mul_assoc, hB, ← Matrix.mul_assoc,
      ← Matrix.map_mul, hQ, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
  have hfin : (adMat F Q * (matHom _ σ J g).1 * adMat F X).map (finPart F E) = 1 := by
    rw [Matrix.map_mul, Matrix.map_mul, map_adMat_fin, map_adMat_fin, map_matHom_fin J hg, Matrix.mul_one,
      ← Matrix.map_mul, hQ, Matrix.map_one _ (map_zero _) (map_one _)]
  refine ⟨_, tensMat_ext hcm τ (fun w => ?_) ?_, hfin, hinf⟩
  · obtain ⟨Bw, hB⟩ := h w
    rw [Matrix.map_mul, Matrix.map_mul (L := adMat F X), hinf w Bw hB, map_adMat, map_matHom]
    exact hB
  · rw [Matrix.map_mul, Matrix.map_mul (L := adMat F X), hfin, map_matHom_fin J hg, Matrix.one_mul, Matrix.mul_one]

theorem mem_minPar_of (hcm : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) {g : GAd σ J} (hg : g ∈ infPts σ J)
    {Q : Matrix (Fin r) (Fin n) E} {X : Matrix (Fin n) (Fin r) E} (hQ : Q * X = 1)
    (h : ∀ w, ∃ Bw : Matrix (Fin r) (Fin r) ℂ, Bw.BlockTriangular id ∧
      archMat σ J (τ w) (projArch σ J w g) * X.map (τ w).1 = X.map (τ w).1 * Bw) : g ∈ minPar σ J X := by
  choose Bw ht he using h
  obtain ⟨B, h1, h2, h3⟩ := frame_coeff J hcm τ hg hQ fun w => ⟨Bw w, he w⟩
  refine ⟨B, fun i j hij => ?_, h1⟩
  refine tens_ext hcm τ (fun w => ?_) ?_
  · have := congrFun (congrFun (h3 w (Bw w) (he w)) i) j
    rw [Matrix.map_apply] at this
    rw [this, ht w hij, map_zero]
  · have := congrFun (congrFun h2 i) j
    rw [Matrix.map_apply] at this
    have hne : i ≠ j := fun e => by subst e; exact lt_irrefl _ hij
    rw [this, map_zero, Matrix.one_apply_ne hne]

theorem exists_diag (hcm : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) {g : GAd σ J} (hg : g ∈ infPts σ J)
    {Q : Matrix (Fin r) (Fin n) E} {X : Matrix (Fin n) (Fin r) E} (hQ : Q * X = 1)
    (h : ∀ w, ∃ d : Fin r → ℂ,
      archMat σ J (τ w) (projArch σ J w g) * X.map (τ w).1 = X.map (τ w).1 * diagonal d) :
    ∃ d : Fin r → AF F ⊗[F] E, (matHom _ σ J g).1 * adMat F X = adMat F X * diagonal d := by
  choose d he using h
  obtain ⟨B, h1, h2, h3⟩ := frame_coeff J hcm τ hg hQ fun w => ⟨_, he w⟩
  have hB : B = diagonal fun i => B i i := by
    ext i j
    by_cases e : i = j
    · subst e
      simp
    · rw [Matrix.diagonal_apply_ne _ e]
      refine tens_ext hcm τ (fun w => ?_) ?_
      · have := congrFun (congrFun (h3 w _ (he w)) i) j
        rw [Matrix.map_apply] at this
        rw [this, Matrix.diagonal_apply_ne _ e, map_zero]
      · have := congrFun (congrFun h2 i) j
        rw [Matrix.map_apply] at this
        rw [this, map_zero, Matrix.one_apply_ne e]
  exact ⟨fun i => B i i, by rw [← hB]; exact h1⟩


variable (σ) in
def kInf (τ : ∀ w : InfinitePlace F, EmbOver E w) (P : InfinitePlace F → Matrix (Fin n) (Fin n) ℂ) :
    Subgroup (GAd σ J) :=
  (Subgroup.pi Set.univ fun w => stabAt σ J (τ w) (P w)).map ((ofInf σ J).comp (embArchPi σ J))

theorem ofInf_mem_infPts (y : GInf σ J) : ofInf σ J y ∈ infPts σ J := mem_infPts.2 (by simp)

theorem kInf_le (τ : ∀ w : InfinitePlace F, EmbOver E w) (P : InfinitePlace F → Matrix (Fin n) (Fin n) ℂ) :
    kInf σ J τ P ≤ infPts σ J := by
  rintro _ ⟨x, -, rfl⟩
  exact ofInf_mem_infPts J _

theorem isCompact_kInf (hcm : IsCMExt F E σ) (hdet : J.det ≠ 0) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    {P : InfinitePlace F → Matrix (Fin n) (Fin n) ℂ} (hP : ∀ w, (P w).PosDef) :
    IsCompact (kInf σ J τ P : Set (GAd σ J)) := by
  rw [kInf, Subgroup.coe_map, Subgroup.coe_pi]
  exact (isCompact_univ_pi fun w => isCompact_stabAt J hcm hdet (τ w) (hP w)).image
    ((continuous_ofInf σ J).comp (continuous_embArchPi σ J))

theorem projArch_ofInf_embArchPi (x : ∀ w, GArch σ J w) (w : InfinitePlace F) :
    projArch σ J w (ofInf σ J (embArchPi σ J x)) = x w := by simp

theorem proj_ofInf_eq (y : GInf σ J) (v) : proj σ J v (ofInf σ J y) = 1 := by simp

theorem iwasawa (hcm : IsCMExt F E σ) (hdet : J.det ≠ 0) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    {P : InfinitePlace F → Matrix (Fin n) (Fin n) ℂ} {Q : Matrix (Fin r) (Fin n) E} {X : Matrix (Fin n) (Fin r) E}
    (hQ : Q * X = 1)
    (hiwa : ∀ w, ∀ g : Matrix (Fin n) (Fin n) ℂ, gᴴ * J.map (τ w).1 * g = J.map (τ w).1 →
      ∃ p k : Matrix (Fin n) (Fin n) ℂ, pᴴ * J.map (τ w).1 * p = J.map (τ w).1 ∧
        kᴴ * J.map (τ w).1 * k = J.map (τ w).1 ∧ kᴴ * P w * k = P w ∧ g = p * k ∧
        ∃ B : Matrix (Fin r) (Fin r) ℂ, B.BlockTriangular id ∧ p * X.map (τ w).1 = X.map (τ w).1 * B) :
    ∀ g ∈ infPts σ J, ∃ p ∈ minPar σ J X, p ∈ infPts σ J ∧ ∃ k ∈ kInf σ J τ P, g = p * k := by
  intro g hg
  choose p k hp hk hkP hgpk hB using fun w => hiwa w _ (arch_unitary J hcm (τ w) (projArch σ J w g))
  choose y hy using fun w => exists_lift J hcm hdet (τ w) (hp w)
  choose z hz using fun w => exists_lift J hcm hdet (τ w) (hk w)
  have hfin := mem_infPts_iff_forall.1 hg
  refine ⟨ofInf σ J (embArchPi σ J y), ?_, ofInf_mem_infPts J _, ofInf σ J (embArchPi σ J z), ?_, ?_⟩
  · refine mem_minPar_of J hcm τ (ofInf_mem_infPts J _) hQ fun w => ?_
    obtain ⟨B, ht, he⟩ := hB w
    refine ⟨B, ht, ?_⟩
    rw [projArch_ofInf_embArchPi, hy]
    exact he
  · refine ⟨z, fun w _ => ?_, rfl⟩
    change (archMat σ J (τ w) (z w))ᴴ * P w * archMat σ J (τ w) (z w) = P w
    rw [hz]
    exact hkP w
  · refine GAd_ext σ J (fun w => ?_) fun v => ?_
    · refine archMat_injective J hcm (τ w) ?_
      rw [map_mul, map_mul, projArch_ofInf_embArchPi, projArch_ofInf_embArchPi, hy, hz]
      exact hgpk w
    · rw [map_mul, proj_ofInf_eq, proj_ofInf_eq, mul_one]
      exact hfin v

theorem good (hcm : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    {P : InfinitePlace F → Matrix (Fin n) (Fin n) ℂ} {Q Q' : Matrix (Fin r) (Fin n) E}
    {X Y : Matrix (Fin n) (Fin r) E} (hQ : Q * X = 1) (hQ' : Q' * Y = 1)
    (hgood : ∀ w, ∀ p : Matrix (Fin n) (Fin n) ℂ, pᴴ * J.map (τ w).1 * p = J.map (τ w).1 → pᴴ * P w * p = P w →
      ∀ B : Matrix (Fin r) (Fin r) ℂ, B.BlockTriangular id → p * X.map (τ w).1 = X.map (τ w).1 * B →
      ∃ d : Fin r → ℂ, p * X.map (τ w).1 = X.map (τ w).1 * diagonal d ∧ p * Y.map (τ w).1 = Y.map (τ w).1 * diagonal d) :
    ∀ p ∈ minPar σ J X, p ∈ kInf σ J τ P → p ∈ leviMin σ J X Y := by
  intro p hp hpK
  have hinf := kInf_le J τ P hpK
  obtain ⟨x, hx, hxp⟩ := hpK
  have hproj : ∀ w, projArch σ J w p = x w := fun w => by
    rw [← hxp]
    exact projArch_ofInf_embArchPi J x w
  obtain ⟨B, hBt, hBe⟩ := hp
  have hw : ∀ w, ∃ d : Fin r → ℂ, archMat σ J (τ w) (projArch σ J w p) * X.map (τ w).1 = X.map (τ w).1 * diagonal d ∧
      archMat σ J (τ w) (projArch σ J w p) * Y.map (τ w).1 = Y.map (τ w).1 * diagonal d := by
    intro w
    refine hgood w _ (arch_unitary J hcm (τ w) _) ?_ (B.map (evC (τ w))) (fun i j hij => ?_) ?_
    · rw [hproj]
      exact hx w (Set.mem_univ w)
    · rw [Matrix.map_apply, hBt hij, map_zero]
    · have := congrArg (fun A => A.map (evC (τ w))) hBe
      simp only [Matrix.map_mul, map_adMat, map_matHom] at this
      exact this
  obtain ⟨d, hd⟩ := exists_diag J hcm τ hinf hQ fun w => (hw w).imp fun _ h => h.1
  obtain ⟨d', hd'⟩ := exists_diag J hcm τ hinf hQ' fun w => (hw w).imp fun _ h => h.2
  exact ⟨d, d', hd, hd'⟩

theorem exists_kInf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∃ K : Subgroup (GAd σ J), K ≤ infPts σ J ∧ IsCompact (K : Set (GAd σ J)) ∧ (∀ g ∈ infPts σ J, ∃ p ∈ minPar σ J X, p ∈ infPts σ J ∧ ∃ k ∈ K, g = p * k) ∧ ∀ p ∈ minPar σ J X, p ∈ K → p ∈ leviMin σ J X Y := by
  intro F E _ _ _ _ _ σ hcm n J hJ r X Y hW
  obtain ⟨τ⟩ : Nonempty (∀ w : InfinitePlace F, EmbOver E w) := ⟨fun _ => Classical.arbitrary _⟩
  have hcTJ : cT (σ : E →+* E) J = J := by
    ext i j
    exact hJ.1 i j
  have hher : ∀ w, (J.map (τ w).1).IsHermitian := fun w => by
    rw [Matrix.IsHermitian, conjT_map hcm, hcTJ]
  have hu : ∀ w, IsUnit (J.map (τ w).1).det := fun w => isUnit_iff_ne_zero.2 (det_map_ne J hJ.2 _)
  have hmap : ∀ (w : InfinitePlace F) {A B : Matrix (Fin n) (Fin r) E},
      (A.map (τ w).1)ᴴ * J.map (τ w).1 * B.map (τ w).1 = (cT (σ : E →+* E) A * J * B).map (τ w).1 := fun w {A B} => by
    rw [Matrix.map_mul, Matrix.map_mul, conjT_map hcm]
  have hxx : ∀ w, (X.map (τ w).1)ᴴ * J.map (τ w).1 * X.map (τ w).1 = 0 := fun w => by
    rw [hmap, hW.xx]; simp
  have hyy : ∀ w, (Y.map (τ w).1)ᴴ * J.map (τ w).1 * Y.map (τ w).1 = 0 := fun w => by
    rw [hmap, hW.yy]; simp
  have hxy : ∀ w, (X.map (τ w).1)ᴴ * J.map (τ w).1 * Y.map (τ w).1 = 1 := fun w => by
    rw [hmap, hW.xy, Matrix.map_one _ (map_zero _) (map_one _)]
  have hyx : ∀ w, (Y.map (τ w).1)ᴴ * J.map (τ w).1 * X.map (τ w).1 = 1 := fun w => by
    have h := congrArg conjTranspose (hxy w)
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, (hher w).eq, conjTranspose_one] at h
    rw [Matrix.mul_assoc]
    exact h
  obtain ⟨w₀⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hQ : cT (σ : E →+* E) Y * J * X = 1 := by
    have h : (cT (σ : E →+* E) Y * J * X).map (τ w₀).1 = (1 : Matrix (Fin r) (Fin r) E).map (τ w₀).1 := by
      rw [← hmap, hyx, Matrix.map_one _ (map_zero _) (map_one _)]
    exact Matrix.map_injective (τ w₀).1.injective h
  choose P hPd hPJ hPX using fun w => GlobalTheory.CompanionTheory.WittMajorant.exists_adapted_majorant n r _ _ _ (hher w) (hu w) (hxx w) (hyy w) (hxy w)
  refine ⟨kInf σ J τ P, kInf_le J τ P, isCompact_kInf J hcm hJ.2 τ hPd, ?_, ?_⟩
  · exact iwasawa J hcm hJ.2 τ hQ fun w => GlobalTheory.CompanionTheory.WittIwasawa.iwasawa_witt_flag n r _ _ _ _ (hher w) (hu w) (hxx w) (hyy w) (hxy w) (hPd w) (hPJ w) (hPX w)
  · exact good J hcm τ hQ hW.xy fun w p h1 h2 B hB hpB =>
      GlobalTheory.CompanionTheory.RealPlace.flag_isometry_diagonal_on_frame n r _ _ p _ _ (hu w) (hxy w) (hPd w) (hPJ w) (hPX w) h1 h2 B hB hpB

end GlobalTheory.CompanionTheory.SiegelArch
