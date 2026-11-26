module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DiscriminantNormShapesBis

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DiagQConjTranspose
open NumberField Module Matrix

open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds

noncomputable section

namespace Formalism.L2.SG.Pf.discriminantNormShapes

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds Formalism.HermitianLattices.Ext.L3.reductionMapsOfForms Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G5

def SolveOnto : Prop :=
  ∀ (K F : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [Fact (IsFixF K F)], Formalism.HermitianLatticesTheory.IsCMUnram K →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ (m : ℕ) (a : Fin m → 𝓞 F), (∀ i, a i ≠ 0) →
    ∀ k : ℕ, 2 * vJof 𝔭 a + 1 ≤ k → ∀ Y : udPre K 𝔭 k a,
      ∃ Y' P W Z Z₀ : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k),
        Y' - Y.1 = Z₀ * diagQ K 𝔭 k a ∧ P * diagQ K 𝔭 k a = diagQ K 𝔭 k a * Y' ∧
        Y'ᴴ * diagQ K 𝔭 k a * Y' - diagQ K 𝔭 k a = diagQ K 𝔭 k a * W * diagQ K 𝔭 k a ∧
        W + Pᴴ * Z + Zᴴ * P + Zᴴ * diagQ K 𝔭 k a * Z = 0

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [Fact (IsFixF K F)] {m : ℕ}

private theorem star_algebraMap_ringOfIntegers (x : 𝓞 F) :
    star (algebraMap (𝓞 F) (𝓞 K) x) = algebraMap (𝓞 F) (𝓞 K) x := by
  have h := Formalism.HermitianLattices.Ext.L3.localizedQuotients.star_ι (K := K) (F := F) Fact.out x
  exact FaithfulSMul.algebraMap_injective (𝓞 K) K h

theorem diagQ_conjTranspose (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a : Fin m → 𝓞 F) :
    (diagQ K 𝔭 k a)ᴴ = diagQ K 𝔭 k a := by
  unfold diagQ
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  rw [Pi.star_apply, star_mk, star_algebraMap_ringOfIntegers]

theorem hom_shift {𝔭 : Ideal (𝓞 F)} {k : ℕ} {a : Fin m → 𝓞 F}
    {Y P : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k)}
    (hPY : P * diagQ K 𝔭 k a = diagQ K 𝔭 k a * Y) (Z : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k)) :
    (P + diagQ K 𝔭 k a * Z) * diagQ K 𝔭 k a = diagQ K 𝔭 k a * (Y + Z * diagQ K 𝔭 k a) := by
  rw [Matrix.add_mul, hPY, Matrix.mul_add, Matrix.mul_assoc]

theorem form_shift {𝔭 : Ideal (𝓞 F)} {k : ℕ} {a : Fin m → 𝓞 F}
    {Y P W : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k)}
    (hPY : P * diagQ K 𝔭 k a = diagQ K 𝔭 k a * Y)
    (hW : Yᴴ * diagQ K 𝔭 k a * Y - diagQ K 𝔭 k a = diagQ K 𝔭 k a * W * diagQ K 𝔭 k a)
    (Z : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k)) :
    (Y + Z * diagQ K 𝔭 k a)ᴴ * diagQ K 𝔭 k a * (Y + Z * diagQ K 𝔭 k a) - diagQ K 𝔭 k a =
      diagQ K 𝔭 k a * (W + Pᴴ * Z + Zᴴ * P + Zᴴ * diagQ K 𝔭 k a * Z) * diagQ K 𝔭 k a := by
  have hH := diagQ_conjTranspose (K := K) 𝔭 k a
  have h1 : Yᴴ * diagQ K 𝔭 k a = diagQ K 𝔭 k a * Pᴴ := by
    have h := congrArg Matrix.conjTranspose hPY
    rw [conjTranspose_mul, conjTranspose_mul, hH] at h
    exact h.symm
  calc _ = Yᴴ * diagQ K 𝔭 k a * Y - diagQ K 𝔭 k a + Yᴴ * diagQ K 𝔭 k a * Z * diagQ K 𝔭 k a + diagQ K 𝔭 k a * Zᴴ * (diagQ K 𝔭 k a * Y) +
        diagQ K 𝔭 k a * Zᴴ * diagQ K 𝔭 k a * Z * diagQ K 𝔭 k a := by
        simp only [conjTranspose_add, conjTranspose_mul, hH, Matrix.add_mul, Matrix.mul_add,
          Matrix.mul_assoc]
        abel
    _ = _ := by
        rw [hW, h1, ← hPY]
        simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]

theorem mem_skSet_of_solve {𝔭 : Ideal (𝓞 F)} {k : ℕ} {a : Fin m → 𝓞 F}
    {Y P W Z : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k)}
    (hPY : P * diagQ K 𝔭 k a = diagQ K 𝔭 k a * Y)
    (hW : Yᴴ * diagQ K 𝔭 k a * Y - diagQ K 𝔭 k a = diagQ K 𝔭 k a * W * diagQ K 𝔭 k a)
    (hZ : W + Pᴴ * Z + Zᴴ * P + Zᴴ * diagQ K 𝔭 k a * Z = 0) :
    Y + Z * diagQ K 𝔭 k a ∈ skSet K 𝔭 k a := by
  show (Y + Z * diagQ K 𝔭 k a)ᴴ * diagQ K 𝔭 k a * (Y + Z * diagQ K 𝔭 k a) = diagQ K 𝔭 k a
  have h := form_shift hPY hW Z
  rw [hZ, Matrix.mul_zero, Matrix.zero_mul] at h
  exact sub_eq_zero.mp h

theorem liftOnto_of_solve (hS : SolveOnto) : LiftOnto := by
  intro K F _ _ _ _ _ _ _ hK 𝔭 h𝔭 m a ha k hk Y
  obtain ⟨Y', P, W, Z, Z₀, hY, hPY, hW, hZ⟩ := hS K F hK 𝔭 h𝔭 m a ha k hk Y
  refine ⟨Y' + Z * diagQ K 𝔭 k a, mem_skSet_of_solve hPY hW hZ, Z₀ + Z, ?_⟩
  rw [Matrix.add_mul, ← hY]
  abel

theorem discOnto_of_solve (hU : UDModel) (hS : SolveOnto) : DiscOnto :=
  discOnto_of_lift hU (liftOnto_of_solve hS)

end Formalism.L2.SG.Pf.discriminantNormShapes
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.EntOfMapEqZero
open NumberField Matrix

noncomputable section

namespace Formalism.L2.SG.Pf.discriminantNormShapes

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds Formalism.HermitianLattices.Ext.L3.traceDeterminantCongruences

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {c : Type} [Fintype c] [DecidableEq c]

def Ent (J : Ideal (𝓞 K)) (A : Matrix c c (𝓞 K)) : Prop := ∀ i j, A i j ∈ J

theorem ent_mul {I J : Ideal (𝓞 K)} {A B : Matrix c c (𝓞 K)} (hA : Ent I A) (hB : Ent J B) :
    Ent (I * J) (A * B) := fun i j => by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_mul (hA i k) (hB k j)

theorem ent_mul_left {J : Ideal (𝓞 K)} (A : Matrix c c (𝓞 K)) {B : Matrix c c (𝓞 K)} (hB : Ent J B) :
    Ent J (A * B) := fun i j => by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun k _ => J.mul_mem_left _ (hB k j)

theorem ent_mul_right {J : Ideal (𝓞 K)} {A : Matrix c c (𝓞 K)} (hA : Ent J A) (B : Matrix c c (𝓞 K)) :
    Ent J (A * B) := fun i j => by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun k _ => J.mul_mem_right _ (hA i k)

theorem ent_add {J : Ideal (𝓞 K)} {A B : Matrix c c (𝓞 K)} (hA : Ent J A) (hB : Ent J B) :
    Ent J (A + B) := fun i j => J.add_mem (hA i j) (hB i j)

theorem ent_sub {J : Ideal (𝓞 K)} {A B : Matrix c c (𝓞 K)} (hA : Ent J A) (hB : Ent J B) :
    Ent J (A - B) := fun i j => J.sub_mem (hA i j) (hB i j)

theorem ent_neg {J : Ideal (𝓞 K)} {A : Matrix c c (𝓞 K)} (hA : Ent J A) : Ent J (-A) := fun i j => J.neg_mem (hA i j)

theorem ent_smul {J : Ideal (𝓞 K)} (a : 𝓞 K) {A : Matrix c c (𝓞 K)} (hA : Ent J A) : Ent J (a • A) := fun i j => J.mul_mem_left a (hA i j)

theorem ent_mono {I J : Ideal (𝓞 K)} (hIJ : I ≤ J) {A : Matrix c c (𝓞 K)} (hA : Ent I A) : Ent J A := fun i j => hIJ (hA i j)

theorem ent_conjTranspose (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F)) (k : ℕ) {A : Matrix c c (𝓞 K)}
    (hA : Ent (extP K 𝔭 ^ k) A) : Ent (extP K 𝔭 ^ k) Aᴴ := fun i j => conjO_mem_pow hF 𝔭 k _ (hA j i)

private theorem exists_add_conj_sub_one_mem_extP (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) : ∃ t : 𝓞 K, t + conjO K t - 1 ∈ extP K 𝔭 := by
  by_cases h : ∃ t : 𝓞 K, t + conjO K t ∉ extP K 𝔭
  · obtain ⟨t0, ht0⟩ := h
    have htrace : ∃ a : 𝓞 F, algebraMap (𝓞 F) (𝓞 K) a = t0 + conjO K t0 := by
      let w := t0 + conjO K t0
      have hw : star (w : K) = (w : K) := by
        change star ((t0 : K) + star (t0 : K)) = (t0 : K) + star (t0 : K)
        rw [star_add, star_star, add_comm]
      obtain ⟨f, hf⟩ := (hF (w : K)).mp hw
      have hfIntegral : IsIntegral ℤ f := by
        apply (isIntegral_algebraMap_iff (B := K)).mp
        rw [hf]
        exact RingOfIntegers.isIntegral_coe w
      refine ⟨⟨f, hfIntegral⟩, RingOfIntegers.ext ?_⟩
      exact hf
    obtain ⟨a, ha⟩ := htrace
    have haP : a ∉ 𝔭 := by
      intro haP
      apply ht0
      rw [← ha]
      exact Ideal.mem_map_of_mem _ haP
    obtain ⟨b, c, hc, hbc⟩ := h𝔭.exists_inv haP
    refine ⟨algebraMap (𝓞 F) (𝓞 K) b * t0, ?_⟩
    have hb : conjO K (algebraMap (𝓞 F) (𝓞 K) b) = algebraMap (𝓞 F) (𝓞 K) b := by
      apply RingOfIntegers.ext
      exact (hF (algebraMap F K (b : F))).mpr ⟨(b : F), rfl⟩
    have e1 : algebraMap (𝓞 F) (𝓞 K) b * t0 + conjO K (algebraMap (𝓞 F) (𝓞 K) b * t0) - 1 = algebraMap (𝓞 F) (𝓞 K) (b * a - 1) := by
      rw [map_mul, hb, map_sub, map_mul, map_one, ha]; ring
    have e2 : b * a - 1 = -c := by linear_combination hbc
    rw [e1, e2, map_neg]
    exact (extP K 𝔭).neg_mem (Ideal.mem_map_of_mem _ hc)
  · push_neg at h
    have h1 : (1 : 𝓞 K) ∈ extP K 𝔭 := by
      apply BallB.mem_of_unram hK
      intro θ
      have e : (θ - conjO K θ) * 1 = θ * (1 + conjO K 1) - (θ + conjO K θ) := by
        rw [map_one]; ring
      rw [e]
      exact (extP K 𝔭).sub_mem ((extP K 𝔭).mul_mem_left _ (h 1)) (h θ)
    refine ⟨0, ?_⟩
    simpa using (extP K 𝔭).neg_mem h1

theorem exists_solve_herm (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {H P Q S : Matrix c c (𝓞 K)} (hH : Ent (extP K 𝔭) H)
    (hPQ : Ent (extP K 𝔭) (Pᴴ * Q - 1)) {N : ℕ} (hHh : Ent (extP K 𝔭 ^ N) (Hᴴ - H))
    (hS : Ent (extP K 𝔭 ^ N) (Sᴴ - S)) :
    ∀ j, j ≤ N → ∃ Z : Matrix c c (𝓞 K),
      Ent (extP K 𝔭 ^ j) (S + Pᴴ * Z + Zᴴ * P + Zᴴ * H * Z) := by
  obtain ⟨t, ht⟩ := exists_add_conj_sub_one_mem_extP hK hF h𝔭
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨0, fun _ _ => ?_⟩
    rw [pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top
  | succ j ih =>
    intro hj
    obtain ⟨Z, hZ⟩ := ih (by omega)
    set E := S + Pᴴ * Z + Zᴴ * P + Zᴴ * H * Z with hE
    set Y : Matrix c c (𝓞 K) := -(t • E) with hYdef
    set W := Q * Y with hW
    refine ⟨Z + W, ?_⟩
    have hJ : extP K 𝔭 ^ (j + 1) = extP K 𝔭 * extP K 𝔭 ^ j := pow_succ' _ _
    have hJ' : extP K 𝔭 ^ (j + 1) = extP K 𝔭 ^ j * extP K 𝔭 := pow_succ _ _
    have hY : Ent (extP K 𝔭 ^ j) Y := ent_neg (ent_smul t hZ)
    have hYh : Ent (extP K 𝔭 ^ j) Yᴴ := ent_conjTranspose hF 𝔭 j hY
    have hWj : Ent (extP K 𝔭 ^ j) W := ent_mul_left Q hY
    have hWh : Ent (extP K 𝔭 ^ j) Wᴴ := ent_conjTranspose hF 𝔭 j hWj
    have hPQh : Ent (extP K 𝔭) (Pᴴ * Q - 1)ᴴ := by
      have := ent_conjTranspose hF 𝔭 1 (A := Pᴴ * Q - 1) (by rw [pow_one]; exact hPQ)
      rwa [pow_one] at this
    have hEh : Ent (extP K 𝔭 ^ (j + 1)) (Eᴴ - E) := by
      have e : Eᴴ - E = (Sᴴ - S) + Zᴴ * (Hᴴ - H) * Z := by
        simp only [hE, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
          Matrix.conjTranspose_conjTranspose, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
        abel
      rw [e]
      have hN : extP K 𝔭 ^ N ≤ extP K 𝔭 ^ (j + 1) := Ideal.pow_le_pow_right hj
      exact ent_mono hN (ent_add hS (ent_mul_right (ent_mul_left _ hHh) _))
    have eq1 : S + Pᴴ * (Z + W) + (Z + W)ᴴ * P + (Z + W)ᴴ * H * (Z + W) =
        E + Pᴴ * W + Wᴴ * P + Zᴴ * H * W + Wᴴ * H * Z + Wᴴ * H * W := by
      simp only [Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul]
      rw [hE]
      abel
    have eq2 : Pᴴ * W = (Pᴴ * Q - 1) * Y + Y := by
      rw [hW, ← Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul]
      abel
    have eq3 : Wᴴ * P = Yᴴ * (Pᴴ * Q - 1)ᴴ + Yᴴ := by
      rw [hW, Matrix.conjTranspose_mul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_one, Matrix.mul_sub,
        Matrix.mul_one, Matrix.mul_assoc]
      abel
    have eq4 : E + Y + Yᴴ = (1 - t - star t) • E - star t • (Eᴴ - E) := by
      rw [hYdef, Matrix.conjTranspose_neg, Matrix.conjTranspose_smul]
      simp only [sub_smul, one_smul, smul_sub]
      abel
    have hx : (1 - t - star t) ∈ extP K 𝔭 := by
      have := (extP K 𝔭).neg_mem ht
      convert this using 1
      show 1 - t - conjO K t = -(t + conjO K t - 1)
      ring
    have T1 : Ent (extP K 𝔭 ^ (j + 1)) ((1 - t - star t) • E) := fun a b => by
      rw [hJ]; exact Ideal.mul_mem_mul hx (hZ a b)
    have T2 : Ent (extP K 𝔭 ^ (j + 1)) (star t • (Eᴴ - E)) := ent_smul _ hEh
    have T3 : Ent (extP K 𝔭 ^ (j + 1)) ((Pᴴ * Q - 1) * Y) := by
      rw [hJ]; exact ent_mul hPQ hY
    have T4 : Ent (extP K 𝔭 ^ (j + 1)) (Yᴴ * (Pᴴ * Q - 1)ᴴ) := by
      rw [hJ']; exact ent_mul hYh hPQh
    have T5 : Ent (extP K 𝔭 ^ (j + 1)) (Zᴴ * H * W) := by
      rw [hJ]; exact ent_mul (ent_mul_left Zᴴ hH) hWj
    have FreeQuotientRank : Ent (extP K 𝔭 ^ (j + 1)) (Wᴴ * H * Z) := by
      rw [hJ']; exact ent_mul_right (ent_mul hWh hH) Z
    have T7 : Ent (extP K 𝔭 ^ (j + 1)) (Wᴴ * H * W) := by
      rw [hJ']; exact ent_mul_right (ent_mul hWh hH) W
    have eq5 : E + Pᴴ * W + Wᴴ * P + Zᴴ * H * W + Wᴴ * H * Z + Wᴴ * H * W =
        ((1 - t - star t) • E - star t • (Eᴴ - E)) + (Pᴴ * Q - 1) * Y + Yᴴ * (Pᴴ * Q - 1)ᴴ
          + Zᴴ * H * W + Wᴴ * H * Z + Wᴴ * H * W := by
      rw [eq2, eq3, ← eq4]
      abel
    rw [eq1, eq5]
    exact ent_add (ent_add (ent_add (ent_add (ent_add (ent_sub T1 T2) T3) T4) T5) FreeQuotientRank) T7

variable [Fact (IsFixF K F)]

theorem ent_lift {𝔭 : Ideal (𝓞 F)} {k : ℕ} (hk : 1 ≤ k)
    {A : Matrix c c (𝓞 K)}
    (hA : ∀ i j, Ideal.Quotient.mk (extP K 𝔭 ^ k) (A i j) ∈ (extP K 𝔭).map (Ideal.Quotient.mk (extP K 𝔭 ^ k))) :
    Ent (extP K 𝔭) A := fun i j => by
  obtain ⟨x, hx, hxe⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 (hA i j)
  have h1 : A i j - x ∈ extP K 𝔭 ^ k := by
    rw [← Ideal.Quotient.eq]; exact hxe.symm
  have h2 : extP K 𝔭 ^ k ≤ extP K 𝔭 := by
    calc extP K 𝔭 ^ k ≤ extP K 𝔭 ^ 1 := Ideal.pow_le_pow_right hk
      _ = extP K 𝔭 := pow_one _
  have := (extP K 𝔭).add_mem (h2 h1) hx
  simpa using this

theorem ent_of_map_eq_zero {𝔭 : Ideal (𝓞 F)} {k : ℕ} {A : Matrix c c (𝓞 K)}
    (hA : A.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) = 0) : Ent (extP K 𝔭 ^ k) A := fun i j => by
  have := congrFun (congrFun hA i) j
  simpa [Ideal.Quotient.eq_zero_iff_mem] using this

theorem exists_solve_quot (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {k : ℕ}
    (hk : 1 ≤ k) {H P Q S : Matrix c c (𝓞 K ⧸ extP K 𝔭 ^ k)} (hHh : Hᴴ = H)
    (hH : ∀ i j, H i j ∈ (extP K 𝔭).map (Ideal.Quotient.mk (extP K 𝔭 ^ k)))
    (hPQ : ∀ i j, (Pᴴ * Q - 1) i j ∈ (extP K 𝔭).map (Ideal.Quotient.mk (extP K 𝔭 ^ k)))
    (hS : Sᴴ = S) : ∃ Z, S + Pᴴ * Z + Zᴴ * P + Zᴴ * H * Z = 0 := by
  have hF : IsFixF K F := Fact.out
  obtain ⟨H', rfl⟩ := reductionMapsOfForms.exists_lift 𝔭 k H
  obtain ⟨P', rfl⟩ := reductionMapsOfForms.exists_lift 𝔭 k P
  obtain ⟨Q', rfl⟩ := reductionMapsOfForms.exists_lift 𝔭 k Q
  obtain ⟨S', rfl⟩ := reductionMapsOfForms.exists_lift 𝔭 k S
  have hmap : ∀ A : Matrix c c (𝓞 K), A.map (reductionMapsOfForms.mkk K 𝔭 k) = 0 → Ent (extP K 𝔭 ^ k) A :=
    fun A hA => ent_of_map_eq_zero hA
  have hH' : Ent (extP K 𝔭) H' := ent_lift hk hH
  have hPQ' : Ent (extP K 𝔭) (P'ᴴ * Q' - 1) := by
    apply ent_lift hk
    intro i j
    have e : (P'ᴴ * Q' - 1).map (reductionMapsOfForms.mkk K 𝔭 k) = (P'.map (reductionMapsOfForms.mkk K 𝔭 k))ᴴ * Q'.map (reductionMapsOfForms.mkk K 𝔭 k) - 1 := by
      rw [reductionMapsOfForms.map_conjTranspose, Matrix.map_sub, Matrix.map_mul, Matrix.map_one] <;> simp
    have := hPQ i j
    rw [← e] at this
    exact this
  have hHh' : Ent (extP K 𝔭 ^ k) (H'ᴴ - H') := by
    apply hmap
    rw [Matrix.map_sub, ← reductionMapsOfForms.map_conjTranspose, hHh, sub_self]
    simp
  have hS' : Ent (extP K 𝔭 ^ k) (S'ᴴ - S') := by
    apply hmap
    rw [Matrix.map_sub, ← reductionMapsOfForms.map_conjTranspose, hS, sub_self]
    simp
  obtain ⟨Z', hZ'⟩ := exists_solve_herm hK hF h𝔭 hH' hPQ' hHh' hS' k le_rfl
  refine ⟨Z'.map (reductionMapsOfForms.mkk K 𝔭 k), ?_⟩
  have e : (S' + P'ᴴ * Z' + Z'ᴴ * P' + Z'ᴴ * H' * Z').map (reductionMapsOfForms.mkk K 𝔭 k) =
      S'.map (reductionMapsOfForms.mkk K 𝔭 k) + (P'.map (reductionMapsOfForms.mkk K 𝔭 k))ᴴ * Z'.map (reductionMapsOfForms.mkk K 𝔭 k) +
        (Z'.map (reductionMapsOfForms.mkk K 𝔭 k))ᴴ * P'.map (reductionMapsOfForms.mkk K 𝔭 k) +
        (Z'.map (reductionMapsOfForms.mkk K 𝔭 k))ᴴ * H'.map (reductionMapsOfForms.mkk K 𝔭 k) * Z'.map (reductionMapsOfForms.mkk K 𝔭 k) := by
    simp only [reductionMapsOfForms.map_conjTranspose]
    simp only [← RingHom.mapMatrix_apply, map_add (f := _), map_mul]
  rw [← e]
  ext i j
  show Ideal.Quotient.mk (extP K 𝔭 ^ k) _ = 0
  exact Ideal.Quotient.eq_zero_iff_mem.2 (hZ' i j)

end Formalism.L2.SG.Pf.discriminantNormShapes
end
end

open NumberField Module Matrix

open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds

noncomputable section

namespace Formalism.L2.SG.Pf.discriminantNormShapes

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds Formalism.HermitianLattices.Ext.L3.reductionMapsOfForms Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G5


open Classical in
def eQ (K : Type) {F : Type} [Field K] [Field F] [Algebra F K] {m : ℕ} (𝔭 : Ideal (𝓞 F)) (k : ℕ)
    (a : Fin m → 𝓞 F) : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k) :=
  Matrix.diagonal fun j => if a j ∈ 𝔭 then 1 else 0

def NormOnto : Prop :=
  ∀ (K F : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [Fact (IsFixF K F)], Formalism.HermitianLatticesTheory.IsCMUnram K →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ (m : ℕ) (a : Fin m → 𝓞 F), (∀ i, a i ≠ 0) →
    ∀ k : ℕ, 2 * vJof 𝔭 a + 1 ≤ k → ∀ Y : udPre K 𝔭 k a,
      ∃ Y' P W Z₀ : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k),
        Y' - Y.1 = Z₀ * diagQ K 𝔭 k a ∧ P * diagQ K 𝔭 k a = diagQ K 𝔭 k a * Y' ∧
        Y'ᴴ * diagQ K 𝔭 k a * Y' - diagQ K 𝔭 k a = diagQ K 𝔭 k a * W * diagQ K 𝔭 k a ∧
        Wᴴ = W ∧ eQ K 𝔭 k a * W * eQ K 𝔭 k a = W ∧
        eQ K 𝔭 k a * P = eQ K 𝔭 k a * P * eQ K 𝔭 k a ∧
        P * eQ K 𝔭 k a = eQ K 𝔭 k a * P * eQ K 𝔭 k a ∧ IsUnit P.det

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [Fact (IsFixF K F)] {m : ℕ}

theorem eQ_conjTranspose (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a : Fin m → 𝓞 F) :
    (eQ K 𝔭 k a)ᴴ = eQ K 𝔭 k a := by
  unfold eQ
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext j
  rw [Pi.star_apply]
  split_ifs <;> simp

theorem eQ_mul_diagQ_mul_eQ_mem {𝔭 : Ideal (𝓞 F)} {k : ℕ} (a : Fin m → 𝓞 F) (i j : Fin m) :
    (eQ K 𝔭 k a * diagQ K 𝔭 k a * eQ K 𝔭 k a) i j ∈
      (extP K 𝔭).map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) := by
  unfold eQ diagQ
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply]
  split_ifs with hij hi
  · rw [one_mul, mul_one]
    exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem (algebraMap (𝓞 F) (𝓞 K)) hi)
  · simp
  · exact zero_mem _

theorem solveOnto_of_norm (hN : NormOnto) : SolveOnto := by
  intro K F _ _ _ _ _ _ _ hK 𝔭 h𝔭 m a ha k hk Y
  obtain ⟨Y', P, W, Z₀, hY, hPY, hW, hWh, hEW, hEP1, hEP2, hdet⟩ := hN K F hK 𝔭 h𝔭 m a ha k hk Y
  have hEh := eQ_conjTranspose (K := K) 𝔭 k a
  have hH := diagQ_conjTranspose (K := K) 𝔭 k a

  have h2 : P * eQ K 𝔭 k a = eQ K 𝔭 k a * P := hEP2.trans hEP1.symm
  have h1 : Pᴴ * eQ K 𝔭 k a = eQ K 𝔭 k a * Pᴴ := by
    have h := congrArg Matrix.conjTranspose h2
    rw [conjTranspose_mul, conjTranspose_mul, hEh] at h
    exact h.symm
  have hu : IsUnit (Pᴴ).det := by
    rw [Matrix.det_conjTranspose]
    exact hdet.star

  obtain ⟨Z', hZ'⟩ := exists_solve_quot hK h𝔭 (k := k) (by omega)
    (H := eQ K 𝔭 k a * diagQ K 𝔭 k a * eQ K 𝔭 k a) (P := P) (Q := (Pᴴ)⁻¹) (S := W)
    (by simp only [conjTranspose_mul, hEh, hH, Matrix.mul_assoc])
    (fun i j => eQ_mul_diagQ_mul_eQ_mem a i j)
    (fun i j => by rw [Matrix.mul_nonsing_inv _ hu, sub_self]; simp)
    hWh
  refine ⟨Y', P, W, eQ K 𝔭 k a * Z' * eQ K 𝔭 k a, Z₀, hY, hPY, hW, ?_⟩
  have h2' : ∀ X : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k), X * P * eQ K 𝔭 k a = X * eQ K 𝔭 k a * P :=
    fun X => by rw [Matrix.mul_assoc, h2, ← Matrix.mul_assoc]
  have key : W + Pᴴ * (eQ K 𝔭 k a * Z' * eQ K 𝔭 k a) + (eQ K 𝔭 k a * Z' * eQ K 𝔭 k a)ᴴ * P +
      (eQ K 𝔭 k a * Z' * eQ K 𝔭 k a)ᴴ * diagQ K 𝔭 k a * (eQ K 𝔭 k a * Z' * eQ K 𝔭 k a) =
      eQ K 𝔭 k a * (W + Pᴴ * Z' + Z'ᴴ * P + Z'ᴴ * (eQ K 𝔭 k a * diagQ K 𝔭 k a * eQ K 𝔭 k a) * Z') * eQ K 𝔭 k a := by
    simp only [conjTranspose_mul, hEh, Matrix.mul_add, Matrix.add_mul, ← Matrix.mul_assoc, h2',
      ← h1, hEW] <;> abel
  rw [key, hZ', Matrix.mul_zero, Matrix.zero_mul]

theorem discOnto_of_norm (hU : UDModel) (hN : NormOnto) : DiscOnto :=
  discOnto_of_solve hU (solveOnto_of_norm hN)

end Formalism.L2.SG.Pf.discriminantNormShapes
