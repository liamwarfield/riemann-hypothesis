module

public import Mathlib

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnimodLocStd
noncomputable section
open scoped BigOperators ComplexConjugate

namespace PI.ULS

abbrev Sesq (V : Type*) [AddCommGroup V] [Module ℂ V] := V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ

section General

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

def altE (H : Sesq V) (x y : V) : ℝ := (H x y).im

def dualLat (H : Sesq V) (Λ : AddSubgroup V) : AddSubgroup V where
  carrier := {x | ∀ y ∈ Λ, ∃ m : ℤ, altE H x y = (m : ℝ)}
  zero_mem' := fun y _ => ⟨0, by simp [altE]⟩
  add_mem' := by
    intro a b ha hb y hy
    obtain ⟨m, hm⟩ := ha y hy
    obtain ⟨k, hk⟩ := hb y hy
    exact ⟨m + k, by simp only [altE] at hm hk ⊢; simp [hm, hk]⟩
  neg_mem' := by
    intro a ha y hy
    obtain ⟨m, hm⟩ := ha y hy
    exact ⟨-m, by simp only [altE] at hm ⊢; simp [hm]⟩

def IsSelfDual (H : Sesq V) (Λ : AddSubgroup V) : Prop := dualLat H Λ = Λ

def relIdx (Λ₁ Λ₂ : AddSubgroup V) : ℕ := Λ₁.relIndex Λ₂

def IsIsom {W : Type*} [AddCommGroup W] [Module ℂ W] (H : Sesq V) (H' : Sesq W) (g : V →ₗ[ℂ] W) : Prop :=
  ∀ x y, H' (g x) (g y) = H x y

def imgLat {W : Type*} [AddCommGroup W] [Module ℂ W] (g : V →ₗ[ℂ] W) (Λ : AddSubgroup V) : AddSubgroup W :=
  Λ.map g.toAddMonoidHom

end General

def area (L : PeriodPair) : ℝ := |(conj L.ω₁ * L.ω₂).im|

section Coordinates

variable {n : Type*} [Fintype n]

def matH (h : Matrix n n ℂ) : Sesq (n → ℂ) :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun z w => ∑ i, ∑ j, z i * h i j * conj (w j))
    (by intro a b c; simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib])
    (by intro c a b; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc])
    (by intro a b c; simp only [Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib])
    (by
      intro c a b
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring)

def stdH (L : PeriodPair) (n : Type*) [Fintype n] [DecidableEq n] : Sesq (n → ℂ) :=
  matH (((area L : ℝ) : ℂ)⁻¹ • (1 : Matrix n n ℂ))

def stdLat (L : PeriodPair) (n : Type*) : AddSubgroup (n → ℂ) :=
  AddSubgroup.pi Set.univ fun _ => L.lattice.toAddSubgroup

end Coordinates

def scalePair (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) : PeriodPair where
  ω₁ := c * L.ω₁
  ω₂ := c * L.ω₂
  indep := by
    have h := L.indep
    rw [LinearIndependent.pair_iff] at h ⊢
    intro s t hst
    apply h s t
    have : c * (s • L.ω₁ + t • L.ω₂) = 0 := by
      rw [← hst]; simp only [Complex.real_smul]; ring
    exact (mul_eq_zero.mp this).resolve_left hc

def cmTheta (b : ℤ) (d : ℕ) : ℂ := ((b : ℂ) + Complex.I * ((Real.sqrt d : ℝ) : ℂ)) / 2

def cmPair (a : ℕ) (b : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) : PeriodPair where
  ω₁ := (a : ℂ)
  ω₂ := cmTheta b d
  indep := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
    have him := congrArg Complex.im h
    have hre := congrArg Complex.re h
    simp [cmTheta] at him hre
    have ht : t = 0 := by
      rcases him with h1 | h1
      · exact h1
      · exact absurd h1 (by positivity)
    subst ht
    simp at hre
    refine ⟨?_, rfl⟩
    rcases hre with h1 | h1
    · exact h1
    · exact absurd h1 (by positivity)

def cmL (a : ℕ) (b : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0) : PeriodPair :=
  scalePair (cmPair a b d ha hd) lam hlam

def CmOK (a : ℕ) (b c : ℤ) (d : ℕ) : Prop := 4 * (a : ℤ) * c = b ^ 2 + d ∧ Odd a ∧ d % 8 = 7 ∧ d.Prime

end PI.ULS

namespace PI


open PI.ULS in
def UnimodLocStd : Prop :=
  ∀ (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0), CmOK a b c d →
    ∀ (m : Type) [Fintype m] [DecidableEq m] (Λa : AddSubgroup (m → ℂ)),
      IsSelfDual (stdH (cmL a b d ha hd lam hlam) m) Λa →
      (∀ x ∈ Λa, cmTheta b d • x ∈ Λa) →
      relIdx (stdLat (cmL a b d ha hd lam hlam) m) Λa ≠ 0 →
      relIdx Λa (stdLat (cmL a b d ha hd lam hlam) m) ≠ 0 →
      ∀ l : ℕ, l.Prime → ∃ δ : (m → ℂ) ≃ₗ[ℂ] (m → ℂ),
        IsIsom (stdH (cmL a b d ha hd lam hlam) m) (stdH (cmL a b d ha hd lam hlam) m)
          (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) ∧ (∀ x, δ x = x → x = 0) ∧
        relIdx (stdLat (cmL a b d ha hd lam hlam) m) (imgLat (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa) ≠ 0 ∧
        ¬ l ∣ relIdx (stdLat (cmL a b d ha hd lam hlam) m) (imgLat (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa) ∧
        relIdx (imgLat (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa) (stdLat (cmL a b d ha hd lam hlam) m) ≠ 0

end PI
end
end

section -- merged from Formalism.PeriodIntegrals.UJClassFin
noncomputable section

open Matrix NumberField IsDedekindDomain
open scoped TensorProduct

namespace PI.UJClassFin

section Group

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

def cT (σ : A →+* A) {m p : Type} (M : Matrix m p A) : Matrix p m A := (M.map σ)ᵀ

theorem cT_mul (σ : A →+* A) {m p q : Type} [Fintype p] (M : Matrix m p A) (N : Matrix p q A) :
    cT σ (M * N) = cT σ N * cT σ M := by
  simp [cT, Matrix.map_mul, Matrix.transpose_mul]

theorem cT_one (σ : A →+* A) : cT σ (1 : Matrix n n A) = 1 := by
  unfold cT
  rw [Matrix.map_one σ (map_zero σ) (map_one σ), Matrix.transpose_one]

def UJ (σ : A →+* A) (J : Matrix n n A) : Subgroup (GL n A) where
  carrier := {g | cT σ (g : Matrix n n A) * J * (g : Matrix n n A) = J}
  one_mem' := by simp [cT_one]
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, Units.val_mul] at *
    calc cT σ ((a : Matrix n n A) * (b : Matrix n n A)) * J * ((a : Matrix n n A) * (b : Matrix n n A))
        = cT σ (b : Matrix n n A) * (cT σ (a : Matrix n n A) * J * (a : Matrix n n A)) * (b : Matrix n n A) := by
          rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = J := by rw [ha, hb]
  inv_mem' := by
    intro g hg
    simp only [Set.mem_ofPred_eq] at *
    calc cT σ ((g⁻¹ : GL n A) : Matrix n n A) * J * ((g⁻¹ : GL n A) : Matrix n n A)
        = cT σ ((g⁻¹ : GL n A) : Matrix n n A) * (cT σ (g : Matrix n n A) * J * (g : Matrix n n A))
            * ((g⁻¹ : GL n A) : Matrix n n A) := by rw [hg]
      _ = cT σ ((g : Matrix n n A) * ((g⁻¹ : GL n A) : Matrix n n A)) * J
            * ((g : Matrix n n A) * ((g⁻¹ : GL n A) : Matrix n n A)) := by
          rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = J := by rw [Units.mul_inv, cT_one, Matrix.one_mul, Matrix.mul_one]

def bc {B : Type} [CommRing B] (φ : A →+* B) : GL n A →* GL n B :=
  Units.map (RingHom.mapMatrix φ).toMonoidHom

end Group

def Jpq (p q : ℕ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := Matrix.fromBlocks 1 0 0 (-1)

def HasSignature {n : Type} [Fintype n] [DecidableEq n] (J : Matrix n n ℂ) (p q : ℕ) : Prop :=
  ∃ e : n ≃ Fin p ⊕ Fin q, ∃ P : GL (Fin p ⊕ Fin q) ℂ,
    cT (starRingEnd ℂ) (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * J.reindex e e *
      (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) = Jpq p q

section Adeles

variable (F : Type) [Field F] [NumberField F]

abbrev AF := AdeleRing (𝓞 F) F

abbrev Ainf := InfiniteAdeleRing F

abbrev Af := FiniteAdeleRing (𝓞 F) F

abbrev Fv (v : HeightOneSpectrum (𝓞 F)) := v.adicCompletion F

def sndA : AF F →ₐ[F] Af F := AlgHom.snd F (Ainf F) (Af F)

def evalV (v : HeightOneSpectrum (𝓞 F)) : Af F →ₐ[F] Fv F v where
  toFun a := a v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

end Adeles

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable (R : Type) [CommRing R] [Algebra F R]

def sigR (σ : E →ₐ[F] E) : R ⊗[F] E →+* R ⊗[F] E :=
  (Algebra.TensorProduct.map (AlgHom.id F R) σ).toRingHom

def inclR : E →+* R ⊗[F] E := (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E).toRingHom

def JR {M : ℕ} (J : Matrix (Fin M) (Fin M) E) : Matrix (Fin M) (Fin M) (R ⊗[F] E) :=
  J.map (inclR R)

def HR (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    Subgroup (GL (Fin M) (R ⊗[F] E)) :=
  UJ (sigR R σ) (JR R J)

def HFin (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    Subgroup (GL (Fin M) (R ⊗[F] E)) :=
  (UJ (σ : E →+* E) J).map (bc (inclR R))

def HFinIn (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) : Subgroup (HR R σ J) :=
  (HFin R σ J).subgroupOf (HR R σ J)

def HA (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) : Type := HR R σ J

variable (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

instance : Group (HA R σ J) := inferInstanceAs (Group (HR R σ J))

def HA.mat (h : HA R σ J) : GL (Fin M) (R ⊗[F] E) := let h' : HR R σ J := h; h'.1

end Alg

section Vol

def intAf (F : Type) [Field F] [NumberField F] : Set (Af F) :=
  {a | ∀ v : HeightOneSpectrum (𝓞 F), evalV F v a ∈ v.adicCompletionIntegers F}

def latHat (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] {M : ℕ}
    (L : Set (Fin M → E)) : AddSubgroup (Fin M → Af F ⊗[F] E) :=
  AddSubgroup.closure {y | ∃ a ∈ intAf F, ∃ x ∈ L, y = fun i => a ⊗ₜ[F] x i}

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

def finMat (h : HA (AF F) σ J) : Matrix (Fin M) (Fin M) (Af F ⊗[F] E) :=
  ((HA.mat (AF F) σ J h : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)).map
    (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E))

theorem mapAlg_mul {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
    (φ : A →ₐ[R] B) {n : ℕ} (X Y : Matrix (Fin n) (Fin n) A) : (X * Y).map φ = X.map φ * Y.map φ :=
  Matrix.map_mul (f := φ.toRingHom)

theorem mapAlg_one {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
    (φ : A →ₐ[R] B) {n : ℕ} : (1 : Matrix (Fin n) (Fin n) A).map φ = 1 :=
  Matrix.map_one _ (map_zero φ) (map_one φ)

theorem HA_mat_mul (h h' : HA (AF F) σ J) :
    HA.mat (AF F) σ J (h * h') = HA.mat (AF F) σ J h * HA.mat (AF F) σ J h' :=
  rfl

theorem HA_mat_one : HA.mat (AF F) σ J 1 = 1 := rfl

theorem finMat_mul (h h' : HA (AF F) σ J) : finMat σ J (h * h') = finMat σ J h * finMat σ J h' := by
  unfold finMat
  rw [HA_mat_mul, Units.val_mul]
  exact mapAlg_mul _ _ _

theorem finMat_one : finMat σ J (1 : HA (AF F) σ J) = 1 := by
  unfold finMat
  rw [HA_mat_one, Units.val_one]
  exact mapAlg_one _

def SFin (L : Set (Fin M → E)) : Subgroup (HA (AF F) σ J) where
  carrier := {h | ∀ y, y ∈ latHat F E L ↔ (finMat σ J h).mulVec y ∈ latHat F E L}
  mul_mem' := by
    intro h h' hh hh' y
    rw [finMat_mul, ← Matrix.mulVec_mulVec, hh' y]
    exact hh _
  one_mem' := by intro y; rw [finMat_one, Matrix.one_mulVec]
  inv_mem' := by
    intro h hh y
    have e : (finMat σ J h).mulVec ((finMat σ J h⁻¹).mulVec y) = y := by
      rw [Matrix.mulVec_mulVec, ← finMat_mul, mul_inv_cancel, finMat_one, Matrix.one_mulVec]
    have := hh ((finMat σ J h⁻¹).mulVec y)
    rw [e] at this
    exact this.symm

abbrev GamG : Subgroup (HA (AF F) σ J) := HFinIn (AF F) σ J

end Vol

def UJClassFin : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (L : Set (Fin M → E)),
    (∀ a, σ a = star a) →
    (∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a)) →
    (∀ τ : E →+* ℂ, HasSignature (J.map τ) M 0) →
    (∃ c : 𝓞 F, c ≠ 0 ∧ ∀ x ∈ L, ∀ i, IsIntegral ℤ ((c : F) • x i)) →
    (∃ c : 𝓞 F, c ≠ 0 ∧ ∀ i, ∀ e : E, IsIntegral ℤ e → Pi.single i ((c : F) • e) ∈ L) →
    ∃ (n : ℕ) (g : Fin n → HA (AF F) σ J),
      (∀ x, ∃ i, ∃ γ : GamG σ J, ∃ k : SFin σ J L, x = (γ : HA (AF F) σ J) * g i * k) ∧
      (∀ i j (γ γ' : GamG σ J) (k k' : SFin σ J L),
        (γ : HA (AF F) σ J) * g i * k = (γ' : HA (AF F) σ J) * g j * k' → i = j)

end PI.UJClassFin
end
end

section -- merged from Formalism.PeriodIntegrals.AdCpctDen
namespace PI

open NumberField IsDedekindDomain

def AdCpctDen : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (C : Set (FiniteAdeleRing (𝓞 F) F)), IsCompact C →
    ∃ N : ℕ, 0 < N ∧ ∀ f : F, algebraMap F (FiniteAdeleRing (𝓞 F) F) f ∈ C → IsIntegral ℤ ((N : F) * f)

end PI
end

section -- merged from Formalism.PeriodIntegrals.UnitKron
namespace PI

open Matrix ComplexOrder

def UnitKron : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (c : E →+* E), (∀ (φ : E →+* ℂ) (x : E), φ (c x) = (starRingEnd ℂ) (φ x)) →
  ∀ (k : ℕ) (J γ : Matrix (Fin k) (Fin k) E),
    (∀ φ : E →+* ℂ, (J.map φ).PosDef ∨ (-(J.map φ)).PosDef) →
    (γ.map c)ᵀ * J * γ = J → (∀ i, IsIntegral ℤ (γ.charpoly.coeff i)) →
    ∃ n : ℕ, 0 < n ∧ γ ^ n = 1

end PI
end

section -- merged from Formalism.PeriodIntegrals.ZerosWindowIn
namespace PI

def LBoundRight : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ s : ℂ, 0 < s.re →
    ‖DirichletCharacter.LFunction χ s‖ ≤ 1 + 2 * ((q : ℝ) + 1) * (1 + ‖s‖ / s.re)

def ZetaBoundRight : Prop :=
  ∀ s : ℂ, 0 < s.re → s ≠ 1 → ‖riemannZeta s‖ ≤ 1 + 1 / ‖s - 1‖ + ‖s‖ * (1 + 1 / s.re)

def LInvRight : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ), 1 < s.re →
    ‖DirichletCharacter.LFunction χ s‖⁻¹ ≤ s.re / (s.re - 1)

end PI
end

section -- merged from Formalism.PeriodIntegrals.ExpTri
open Matrix

noncomputable section

namespace PI

def ExpTri : Prop :=
  ∀ (n : ℕ) (X Y Z U : Matrix (Fin n) (Fin n) ℂ), Xᴴ = X → Yᴴ = Y → Zᴴ = Z →
    U ∈ Matrix.unitaryGroup (Fin n) ℂ →
    NormedSpace.exp X * NormedSpace.exp Y = U * NormedSpace.exp Z →
    Real.sqrt (∑ i, ∑ j, ‖Z i j‖ ^ 2) ≤
      Real.sqrt (∑ i, ∑ j, ‖X i j‖ ^ 2) + Real.sqrt (∑ i, ∑ j, ‖Y i j‖ ^ 2)

end PI

end
end

section -- merged from Formalism.PeriodIntegrals.ScGapBig
namespace PI.ScGapBig

def rk48 (k r : ℕ) : ℕ := 2 * r + k + 1

def GapBig (k r : ℕ) (b : Fin (2 * r + 2) → ℝ) : Prop :=
  ∃ t : ℕ, Odd t ∧ rk48 k r + 5 ≤ t ∧ 1801 ≤ rk48 k r + t ∧
    ∀ (j : Fin (2 * r + 2)) (hj : j.val + 1 < 2 * r + 2),
      2 * ((rk48 k r + (2 * r + 2) * t : ℕ) : ℝ) ^ 3 + (t : ℝ) + 3 < b ⟨j.val + 1, hj⟩ - b j

def ScGapBig : Prop :=
  ∀ (k r : ℕ) (b : Fin (2 * r + 2) → ℝ), 1801 ≤ rk48 k r →
    (∀ (j : Fin (2 * r + 2)) (hj : j.val + 1 < 2 * r + 2),
      16 * (rk48 k r : ℝ) ^ 19 ≤ b ⟨j.val + 1, hj⟩ - b j) →
    GapBig k r b

end PI.ScGapBig
end

section -- merged from Formalism.PeriodIntegrals.ZerosWindow
noncomputable section

namespace PI

def ZerosNear {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (t : ℝ) : Set ℂ :=
  {ρ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ 1 ∧ DirichletCharacter.LFunction χ ρ = 0}

def ZerosWindowWith (C : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → ∀ t : ℝ,
    (ZerosNear χ t).Finite ∧
    ∑ᶠ ρ ∈ ZerosNear χ t, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) ≤
      C * Real.log (N * (|t| + 2))

def ZerosWindow : Prop := ∃ C : ℝ, 0 < C ∧ ZerosWindowWith C

end PI
end
end

section -- merged from Formalism.PeriodIntegrals.WeylProd
namespace PI

open Finset

def vandN (x : ℕ → ℝ) (N : ℕ) : ℝ := ∏ i ∈ range N, ∏ j ∈ Ico (i + 1) N, (x i - x j)

noncomputable def dimVN (x : ℕ → ℝ) (N : ℕ) : ℝ := vandN x N / ∏ i ∈ range N, ((i.factorial : ℕ) : ℝ)

def shiftSeq {n : ℕ} (w : Fin n → ℤ) : ℕ → ℝ := fun i => if h : i < n then ((w ⟨i, h⟩ : ℤ) : ℝ) - i else 0

def WeylProd : Prop :=
  ∀ (n : ℕ) (μ w : Fin n → ℤ) (c : ℤ), (∀ t, μ t = w t - c) →
    (((∏ i : Fin n, ∏ j : Fin n,
      if i < j then (((μ i : ℤ) : ℚ) - ((μ j : ℤ) : ℚ) + ((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)) /
        (((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)) else 1 : ℚ)) : ℝ) = dimVN (shiftSeq w) n

end PI
end

section -- merged from Formalism.PeriodIntegrals.CMTraceOnto
noncomputable section

namespace PI

open NumberField

def IsCMUnram (K : Type*) [Field K] [NumberField K] [StarRing K] : Prop :=
  IsTotallyComplex K ∧ (∀ (φ : K →+* ℂ) (a : K), φ (star a) = starRingEnd ℂ (φ a)) ∧
    ∀ P : Ideal (RingOfIntegers K), P.IsMaximal →
      ∃ θ t : RingOfIntegers K, algebraMap (RingOfIntegers K) K t =
        star (algebraMap (RingOfIntegers K) K θ) ∧ θ - t ∉ P

def CMTraceOnto : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K], IsCMUnram K →
    ∀ a : 𝓞 K, star (a : K) = (a : K) → ∃ x y : 𝓞 K, (y : K) = star (x : K) ∧ x + y = a

end PI

end
end

section -- merged from Formalism.PeriodIntegrals.CharIdem
open CategoryTheory

namespace PI.CharIdem

variable {G : Type} [Group G] [Fintype G]

noncomputable def charIdem (V : FDRep ℂ G) : MonoidAlgebra ℂ G :=
  ∑ g : G, MonoidAlgebra.single g (((Module.finrank ℂ V : ℂ) / (Fintype.card G : ℂ)) * V.character g⁻¹)

noncomputable def act (V : FDRep ℂ G) : MonoidAlgebra ℂ G →ₐ[ℂ] Module.End ℂ V :=
  MonoidAlgebra.lift ℂ (Module.End ℂ V) G V.ρ

def CharIdem : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] (V W : FDRep ℂ G), Simple V → Simple W →
    act V (charIdem V) = 1 ∧
    (IsEmpty (V ≅ W) → act W (charIdem V) = 0) ∧
    IsIdempotentElem (charIdem V) ∧
    (∀ x : MonoidAlgebra ℂ G, charIdem V * x = x * charIdem V) ∧
    (IsEmpty (V ≅ W) → charIdem V * charIdem W = 0)

end PI.CharIdem
end

section -- merged from Formalism.PeriodIntegrals.ExplicitFormula
noncomputable section

namespace PI


open Classical in
def psi0 {N : ℕ} (χ : DirichletCharacter ℂ N) (u : ℝ) : ℂ :=
  by
    classical
    exact (∑ n ∈ Finset.Icc 1 ⌊u⌋₊,
      ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod N)) -
      (if χ = 1 then (u : ℂ) else 0)

def ZerosBelow {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (T : ℝ) : Set ℂ :=
  {ρ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T ∧ DirichletCharacter.LFunction χ ρ = 0}

def ExplicitFormulaWith (C : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
    ∀ u T : ℝ, 2 ≤ T → T ≤ u →
      (ZerosBelow χ T).Finite ∧
      ‖psi0 χ u + ∑ᶠ ρ ∈ ZerosBelow χ T,
          (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ ≤
        C * (u * Real.log (N * u * T) ^ 2 / T + Real.log (N * u) +
          ∑ᶠ ρ ∈ ZerosBelow χ 1,
            (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) / ‖ρ‖)

def ExplicitFormula : Prop := ∃ C : ℝ, 0 < C ∧ ExplicitFormulaWith C

end PI
end
end

section -- merged from Formalism.PeriodIntegrals.SSAscent
namespace PI

namespace SSAscent

section Rep

variable {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ}

def IsInv (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)) : Prop :=
  ∀ g, ∀ v ∈ W, (ρ g : Matrix (Fin a) (Fin a) k).mulVec v ∈ W

def IsSSRep (ρ : Γ →* GL (Fin a) k) : Prop :=
  ∀ W, IsInv ρ W → ∃ W', IsInv ρ W' ∧ IsCompl W W'

end Rep

def mapRep {Γ : Type} [Group Γ] {A B : Type} [CommRing A] [CommRing B] {a : ℕ} (f : A →+* B)
    (ρ : Γ →* GL (Fin a) A) : Γ →* GL (Fin a) B :=
  (Units.map (f.mapMatrix : Matrix (Fin a) (Fin a) A →+* Matrix (Fin a) (Fin a) B).toMonoidHom).comp ρ

end SSAscent

open SSAscent

def SSAscent : Prop :=
  ∀ (K L : Type) [Field K] [CharZero K] [Field L] [Algebra K L] (Γ : Type) [Group Γ] (a : ℕ)
    (ρ : Γ →* GL (Fin a) K), IsSSRep ρ → IsSSRep (mapRep (algebraMap K L) ρ)

end PI
end

section -- merged from Formalism.PeriodIntegrals.ExpIntW
noncomputable section

namespace PI

def IsIntP {p : ℕ} [Fact p.Prime] (x : ℂ_[p]) : Prop := ‖x‖ ≤ 1

def IntegralMv {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : Prop :=
  ∀ n, IsIntP (MvPowerSeries.coeff n F)

def expMv {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  fun α => ∑ n ∈ Finset.range ((α.sum fun _ k => k) + 1),
    MvPowerSeries.coeff α (F ^ n) / (n.factorial : ℂ_[p])

def Wp (p : ℕ) [Fact p.Prime] : Subring ℂ_[p] :=
  (Subring.closure {ζ : ℂ_[p] | ∃ n : ℕ, 0 < n ∧ Nat.Coprime n p ∧ ζ ^ n = 1}).topologicalClosure

def InWf {p : ℕ} [Fact p.Prime] (x : ℂ_[p]) : Prop := ∃ k : ℕ, (p : ℂ_[p]) ^ k * x ∈ Wp p

def IntegralW {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : Prop :=
  ∀ n, MvPowerSeries.coeff n F ∈ Wp p

def CoefWf {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : Prop :=
  ∀ n, InWf (MvPowerSeries.coeff n F)

def Simeq {σ : Type*} {p : ℕ} [Fact p.Prime] (f g : MvPowerSeries σ ℂ_[p]) : Prop :=
  MvPowerSeries.constantCoeff (f - g) = 0 ∧ IntegralMv (expMv (f - g))

def SimeqW {σ : Type*} {p : ℕ} [Fact p.Prime] (f g : MvPowerSeries σ ℂ_[p]) : Prop :=
  MvPowerSeries.constantCoeff (f - g) = 0 ∧ IntegralW (expMv (f - g))

def ExpIntW : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (f : MvPowerSeries σ ℂ_[p]), CoefWf f → Simeq f 0 → SimeqW f 0

end PI

end
end

section -- merged from Formalism.PeriodIntegrals.RowLetter
open MvPolynomial

noncomputable section

namespace PI.RL

def genM (R : Type) [CommRing R] (m : ℕ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) (MvPolynomial (Fin (m + 1) × Fin (m + 1)) R) :=
  Matrix.of fun a s => X (a, s)

def Nv (R : Type) [CommRing R] (m : ℕ) (vec : Bool) (c : Fin (m + 1)) :
    MvPolynomial (Fin (m + 1) × Fin (m + 1)) R :=
  if vec then X (c, 0) else (genM R m).adjugate (Fin.last m) c

def theta (R : Type) [CommRing R] (m : ℕ) (vec : Bool) :
    MvPolynomial (Fin (m + 1)) R →ₐ[R] MvPolynomial (Fin (m + 1) × Fin (m + 1)) R :=
  aeval (Nv R m vec)

def Hd (R : Type) [CommRing R] (k d : ℕ) : Submodule R (MvPolynomial (Fin k) R) :=
  restrictSupport R {μ | ∑ c, μ c = d}

def RE (K : Type) [CommRing K] (k : ℕ) (a b : Fin k) (f : MvPolynomial (Fin k × Fin k) K) : MvPolynomial (Fin k × Fin k) K :=
  ∑ t : Fin k, X (a, t) * pderiv (b, t) f

def TE (K : Type) [CommRing K] (k : ℕ) (vec : Bool) (d : ℕ) (a b : Fin k) (f : MvPolynomial (Fin k) K) : MvPolynomial (Fin k) K :=
  if vec then X a * pderiv b f else (if a = b then (d : K) • f else 0) - X b * pderiv a f

end PI.RL

namespace PI

open PI.RL

def RowLetter : Prop :=
  ∀ (K : Type) [Field K] (m : ℕ) (vec : Bool) (d : ℕ) (a b : Fin (m + 1)), ∀ P ∈ Hd K (m + 1) d,
    RE K (m + 1) a b (theta K m vec P) = theta K m vec (TE K (m + 1) vec d a b P)

end PI
end
end

section -- merged from Formalism.PeriodIntegrals.SelfDualLoc
open Matrix NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace PI.SelfDualLoc

section Defs

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

def hform (σ : A →+* A) (J : Matrix n n A) (x y : n → A) : A := ∑ i, ∑ j, σ (x i) * J i j * y j

end Defs

section Points

variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {n : Type} [Fintype n] [DecidableEq n]

def sigR (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R] : E ⊗[F] R →+* E ⊗[F] R :=
  (Algebra.TensorProduct.map σ (AlgHom.id F R)).toRingHom

def inclE (R : Type) [CommRing R] [Algebra F R] : E →+* E ⊗[F] R :=
  Algebra.TensorProduct.includeLeftRingHom

def tensInt (R : Type) [CommRing R] [Algebra F R] (S₁ : Subring E) (S₂ : Subring R) :
    Subring (E ⊗[F] R) :=
  Subring.closure (Set.range (fun x : S₁ => (x : E) ⊗ₜ[F] (1 : R)) ∪
    Set.range (fun y : S₂ => (1 : E) ⊗ₜ[F] (y : R)))

def latS (R : Type) [CommRing R] [Algebra F R] (S : Subring (E ⊗[F] R)) {O : Type} [CommRing O]
    [Algebra O E] (Λ : Submodule O (n → E)) : Submodule S (n → E ⊗[F] R) :=
  Submodule.span S ((fun x : n → E => fun i => inclE (F := F) R (x i)) '' (Λ : Set (n → E)))

end Points

def intOE (E : Type) [Field E] [NumberField E] : Subring E := (algebraMap (𝓞 E) E).range

end PI.SelfDualLoc

namespace PI

open PI.SelfDualLoc in
def SelfDualLoc : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))
    (Lb : Submodule (𝓞 E) (Fin n → E)) (T : ℕ),
    Module.Finite (𝓞 E) Lb →
    (∀ x ∈ Lb, ∀ y ∈ Lb, hform (σ : E →+* E) J x y ∈ intOE E) →
    (∀ y : Fin n → E, (∀ x ∈ Lb, hform (σ : E →+* E) J x y ∈ intOE E) → (T : E) • y ∈ Lb) →
    (T : 𝓞 F) ∉ v.asIdeal →
    ∀ y, y ∈ latS (F := F) (v.adicCompletion F)
        (tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) Lb ↔
      ∀ z ∈ latS (F := F) (v.adicCompletion F)
        (tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) Lb,
        hform (sigR σ (v.adicCompletion F)) (J.map (inclE (F := F) (v.adicCompletion F))) z y ∈
          tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring

end PI
end
end

section -- merged from Formalism.PeriodIntegrals.AddIntG
noncomputable section

open Classical

namespace PI.AddIntG

def IsIntP {p : ℕ} [Fact p.Prime] (x : ℂ_[p]) : Prop := ‖x‖ ≤ 1

def IntegralMv {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : Prop :=
  ∀ n, IsIntP (MvPowerSeries.coeff n F)

def Wp (p : ℕ) [Fact p.Prime] : Subring ℂ_[p] :=
  (Subring.closure {ζ : ℂ_[p] | ∃ n : ℕ, 0 < n ∧ Nat.Coprime n p ∧ ζ ^ n = 1}).topologicalClosure

def IntegralW {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : Prop :=
  ∀ n, MvPowerSeries.coeff n F ∈ Wp p

def dX {A : Type*} [CommRing A] (f : PowerSeries A) : PowerSeries A :=
  PowerSeries.mk fun n => ((n : A) + 1) * PowerSeries.coeff (n + 1) f

def IsWq {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) : Prop :=
  let c := algebraMap ℂ_[p] (PowerSeries ℂ_[p])
  let X := (PowerSeries.X : PowerSeries ℂ_[p])
  wq = 1 + c W.a₁ * X * wq + c W.a₂ * X ^ 2 * wq + c W.a₃ * X ^ 3 * wq ^ 2 +
    c W.a₄ * X ^ 4 * wq ^ 2 + c W.a₆ * X ^ 6 * wq ^ 3

def omegaW {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    PowerSeries ℂ_[p] :=
  let c := algebraMap ℂ_[p] (PowerSeries ℂ_[p])
  let X := (PowerSeries.X : PowerSeries ℂ_[p])
  (-(2 : PowerSeries ℂ_[p]) * wq - X * dX wq) * (wq * (c W.a₁ * X + c W.a₃ * X ^ 3 * wq - 2))⁻¹

def flog {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    PowerSeries ℂ_[p] :=
  PowerSeries.mk fun n => if n = 0 then 0 else PowerSeries.coeff (n - 1) (omegaW W wq) / n

abbrev Xv {p : ℕ} [Fact p.Prime] {σ : Type*} (i : σ) : MvPowerSeries σ ℂ_[p] := MvPowerSeries.X i

def add {p : ℕ} [Fact p.Prime] {σ : Type*} (l ex : PowerSeries ℂ_[p]) (a b : MvPowerSeries σ ℂ_[p]) :
    MvPowerSeries σ ℂ_[p] :=
  PowerSeries.subst (PowerSeries.subst a l + PowerSeries.subst b l) ex

def KeyF : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (S : Subring ℂ_[p]) (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]),
    W.a₁ ∈ S → W.a₂ ∈ S → W.a₃ ∈ S → W.a₄ ∈ S → W.a₆ ∈ S → IsWq W wq →
    ∃ F : MvPowerSeries (Fin 2) ℂ_[p], (∀ n, MvPowerSeries.coeff n F ∈ S) ∧ MvPowerSeries.constantCoeff F = 0 ∧
      PowerSeries.subst F (flog W wq) = PowerSeries.subst (Xv 0) (flog W wq) + PowerSeries.subst (Xv 1) (flog W wq)

def Target : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq ex : PowerSeries ℂ_[p]),
    IsIntP W.a₁ → IsIntP W.a₂ → IsIntP W.a₃ → IsIntP W.a₄ → IsIntP W.a₆ → IsWq W wq →
    PowerSeries.constantCoeff ex = 0 → PowerSeries.subst ex (flog W wq) = PowerSeries.X →
    IntegralMv (add (flog W wq) ex (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) ∧
    ((W.a₁ ∈ Wp p ∧ W.a₂ ∈ Wp p ∧ W.a₃ ∈ Wp p ∧ W.a₄ ∈ Wp p ∧ W.a₆ ∈ Wp p) →
      IntegralW (add (flog W wq) ex (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]))

def Glue : Prop := KeyF → Target

end PI.AddIntG
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryApprox
noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace PI

section Group

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

def UnitaryApproxDefs.cT (σ : A →+* A) {m p : Type} (M : Matrix m p A) : Matrix p m A := (M.map σ)ᵀ

def UnitaryApproxDefs.IsHerm (σ : A →+* A) (J : Matrix n n A) : Prop := UnitaryApproxDefs.cT σ J = J

theorem UnitaryApproxDefs.cT_mul (σ : A →+* A) {m p q : Type} [Fintype p] (M : Matrix m p A) (N : Matrix p q A) :
    UnitaryApproxDefs.cT σ (M * N) = UnitaryApproxDefs.cT σ N * UnitaryApproxDefs.cT σ M := by
  simp [UnitaryApproxDefs.cT, Matrix.map_mul, Matrix.transpose_mul]

theorem UnitaryApproxDefs.cT_one (σ : A →+* A) : UnitaryApproxDefs.cT σ (1 : Matrix n n A) = 1 := by
  unfold UnitaryApproxDefs.cT
  rw [Matrix.map_one σ (map_zero σ) (map_one σ), Matrix.transpose_one]

def UnitaryApproxDefs.UJ (σ : A →+* A) (J : Matrix n n A) : Subgroup (GL n A) where
  carrier := {g | UnitaryApproxDefs.cT σ (g : Matrix n n A) * J * (g : Matrix n n A) = J}
  one_mem' := by simp [UnitaryApproxDefs.cT_one]
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, Units.val_mul] at *
    calc UnitaryApproxDefs.cT σ ((a : Matrix n n A) * (b : Matrix n n A)) * J * ((a : Matrix n n A) * (b : Matrix n n A))
        = UnitaryApproxDefs.cT σ (b : Matrix n n A) * (UnitaryApproxDefs.cT σ (a : Matrix n n A) * J * (a : Matrix n n A)) * (b : Matrix n n A) := by
          rw [UnitaryApproxDefs.cT_mul]; simp only [Matrix.mul_assoc]
      _ = J := by rw [ha, hb]
  inv_mem' := by
    intro g hg
    simp only [Set.mem_ofPred_eq] at *
    calc UnitaryApproxDefs.cT σ ((g⁻¹ : GL n A) : Matrix n n A) * J * ((g⁻¹ : GL n A) : Matrix n n A)
        = UnitaryApproxDefs.cT σ ((g⁻¹ : GL n A) : Matrix n n A) * (UnitaryApproxDefs.cT σ (g : Matrix n n A) * J * (g : Matrix n n A))
            * ((g⁻¹ : GL n A) : Matrix n n A) := by rw [hg]
      _ = UnitaryApproxDefs.cT σ ((g : Matrix n n A) * ((g⁻¹ : GL n A) : Matrix n n A)) * J
            * ((g : Matrix n n A) * ((g⁻¹ : GL n A) : Matrix n n A)) := by
          rw [UnitaryApproxDefs.cT_mul]; simp only [Matrix.mul_assoc]
      _ = J := by rw [Units.mul_inv, UnitaryApproxDefs.cT_one, Matrix.one_mul, Matrix.mul_one]
end Group

section Points

variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {n : Type} [Fintype n] [DecidableEq n]

def UnitaryApproxDefs.sigR (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R] : E ⊗[F] R →+* E ⊗[F] R :=
  (Algebra.TensorProduct.map σ (AlgHom.id F R)).toRingHom

def UnitaryApproxDefs.inclE (R : Type) [CommRing R] [Algebra F R] : E →+* E ⊗[F] R :=
  Algebra.TensorProduct.includeLeftRingHom

def UnitaryApproxDefs.UPts (σ : E →ₐ[F] E) (J : Matrix n n E) (R : Type) [CommRing R] [Algebra F R] :
    Subgroup (GL n (E ⊗[F] R)) := UnitaryApproxDefs.UJ (UnitaryApproxDefs.sigR σ R) (J.map (UnitaryApproxDefs.inclE (F := F) R))

def UnitaryApproxDefs.tensInt (R : Type) [CommRing R] [Algebra F R] (S₁ : Subring E) (S₂ : Subring R) :
    Subring (E ⊗[F] R) :=
  Subring.closure (Set.range (fun x : S₁ => (x : E) ⊗ₜ[F] (1 : R)) ∪
    Set.range (fun y : S₂ => (1 : E) ⊗ₜ[F] (y : R)))

def UnitaryApproxDefs.intOE (E : Type) [Field E] [NumberField E] : Subring E := (algebraMap (𝓞 E) E).range

end Points

end PI

end
end

section -- merged from Formalism.PeriodIntegrals.PrimeCount
noncomputable section

namespace PI

def pr (y : ℝ) : Finset ℕ := (Finset.range (⌊y⌋₊ + 1)).filter Nat.Prime

def PrimeCountBound : Prop := ∀ y : ℝ, 1 < y → ((pr y).card : ℝ) < 1.26 * y / Real.log y

end PI
end
end
