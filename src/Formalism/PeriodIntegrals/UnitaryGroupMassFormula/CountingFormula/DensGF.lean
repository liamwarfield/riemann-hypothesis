module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DensAtGoodOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.ResCharIff
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SplitDensity.FiberCardHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.WeightPositive

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DensGF
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S IsDedekindDomain
open Classical ValuativeRel

def piO {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] (L : Loc.LocE F E) (ϖ : 𝒪[F]) : L.O :=
  ⟨algebraMap F E ϖ, (L.O_def _).2 (by
    rw [show algebraMap F E (ϖ : F) = algebraMap 𝒪[F] E ϖ from
      (IsScalarTower.algebraMap_apply 𝒪[F] F E ϖ).symm]
    exact isIntegral_algebraMap)⟩

def FLocO : Prop :=
  ∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] (L : Loc.LocE F E), IsNonarchimedeanLocalField F → CharZero F →
    (∀ x : E, x ≠ 0 → IsUnit x) → ∀ ϖ : 𝒪[F], Irreducible ϖ →
      (∀ x ∈ L.O, (¬ ∃ z ∈ L.O, x = algebraMap F E ϖ * z) → ∃ y ∈ L.O, x * y = 1) ∧
      (∀ x : E, ∃ c : 𝒪[F], c ≠ 0 ∧ algebraMap F E c * x ∈ L.O) ∧
      (∀ x ∈ L.O, x ≠ 0 → ∃ k : ℕ, ∃ u ∈ L.O, (∃ w ∈ L.O, u * w = 1) ∧ x = algebraMap F E ϖ ^ k * u)

def FResField : Prop :=
  ∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] (L : Loc.LocE F E), IsNonarchimedeanLocalField F → CharZero F →
    (∀ x : E, x ≠ 0 → IsUnit x) → ∀ ϖ : 𝒪[F], Irreducible ϖ →
      (Ideal.span {piO L ϖ}).IsMaximal ∧
      Nat.card (L.O ⧸ Ideal.span {piO L ϖ}) = Nat.card 𝓀[F] ^ 2 ∧
      ∀ x y : L.O, (y : E) = L.cj x →
        Ideal.Quotient.mk (Ideal.span {piO L ϖ}) y =
          Ideal.Quotient.mk (Ideal.span {piO L ϖ}) x ^ Nat.card 𝓀[F]

def FLatBasis : Prop :=
  ∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] [MeasurableSpace E] (M : Loc.Model F E), IsNonarchimedeanLocalField F →
    CharZero F → (∀ x : E, x ≠ 0 → IsUnit x) →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) (Λ : Submodule M.L.O V),
      H.IsSelfDual Λ →
      ∃ b : Fin (Module.finrank E V) → V, (∀ k, b k ∈ Λ) ∧ LinearIndependent E b ∧
        (∀ x ∈ Λ, ∃ c : Fin (Module.finrank E V) → E, (∀ k, c k ∈ M.L.O) ∧ x = ∑ k, c k • b k) ∧
        ∃ Q : Matrix (Fin (Module.finrank E V)) (Fin (Module.finrank E V)) E, (∀ k l, Q k l ∈ M.L.O) ∧
          Q * Matrix.of (fun k l => H.h (b k) (b l)) = 1

end PI.UnitaryGroupMassFormula.CntFormula
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.GoodRDeltaC
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.GoodRDeltaB
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.DeltaB

open Polynomial

variable {R K A : Type} [CommRing R] [Field K] [CommRing A] [Algebra R K] [Algebra K A] [Algebra R A]
  [IsScalarTower R K A]

theorem trace_isIntegral_rank2 (b : Module.Basis (Fin 2) K A) {y : A} (hy : IsIntegral R y) :
    IsIntegral R (Algebra.trace K A y) := by
  classical
  obtain ⟨p, hpm, hp⟩ := hy
  let L := AlgebraicClosure K
  let M : Matrix (Fin 2) (Fin 2) K := Algebra.leftMulMatrix b y
  let M' : Matrix (Fin 2) (Fin 2) L := M.map (algebraMap K L)
  have hpy : Polynomial.aeval y p = 0 := hp
  have hpM : Polynomial.aeval M p = 0 := by
    have h1 := Polynomial.aeval_algHom_apply ((Algebra.leftMulMatrix b).restrictScalars R) y p
    rw [hpy, map_zero] at h1
    exact h1
  have hpM' : Polynomial.aeval M' p = 0 := by
    have h1 := Polynomial.aeval_algHom_apply
      (((Algebra.ofId K L).mapMatrix : Matrix (Fin 2) (Fin 2) K →ₐ[K] Matrix (Fin 2) (Fin 2) L).restrictScalars R) M p
    rw [hpM, map_zero] at h1
    exact h1
  have hroot : ∀ μ ∈ M'.charpoly.roots, IsIntegral R μ := by
    intro μ hμ
    have h1 : μ ∈ spectrum L M' := by
      rw [Matrix.mem_spectrum_iff_isRoot_charpoly]
      exact (Polynomial.mem_roots'.mp hμ).2
    have h2 := spectrum.subset_polynomial_aeval M' (p.map (algebraMap R L)) ⟨μ, h1, rfl⟩
    rw [Polynomial.aeval_map_algebraMap, hpM', spectrum.zero_eq] at h2
    refine ⟨p, hpm, ?_⟩
    have h3 : Polynomial.eval μ (p.map (algebraMap R L)) = 0 := h2
    rwa [Polynomial.eval_map] at h3
  have htr : algebraMap K L (Algebra.trace K A y) = M'.charpoly.roots.sum := by
    rw [Algebra.trace_eq_matrix_trace b y, ← Matrix.trace_eq_sum_roots_charpoly]
    simp [M', M, Matrix.trace, Matrix.map_apply]
  have hint : IsIntegral R (algebraMap K L (Algebra.trace K A y)) := by
    rw [htr]
    exact IsIntegral.multiset_sum hroot
  exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom R K L) (algebraMap K L).injective).mp hint

end PI.UnitaryGroupMassFormula.CntFormula.DeltaB
end
end

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.DeltaC

open NumberField IsDedekindDomain ValuativeRel Formalism.MainNotions.S.Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)}

theorem mem_of_isIntegral_fp (L : LocAt F E sig p) {s : L.Fp} (hs : IsIntegral 𝒪[L.Fp] s) : s ∈ 𝒪[L.Fp] := by
  exact (Valuation.integer.integers (ValuativeRel.valuation L.Fp)).mem_of_integral hs

theorem trace_mem (L : LocAt F E sig p) {y : L.Ep} (hy : y ∈ L.O) : Algebra.trace L.Fp L.Ep y ∈ 𝒪[L.Fp] := by
  haveI := L.free
  haveI := PI.ProdFormulaE.Base.finite L
  let b : Module.Basis (Fin 2) L.Fp L.Ep := Module.finBasisOfFinrankEq L.Fp L.Ep L.rank
  exact mem_of_isIntegral_fp L (DeltaB.trace_isIntegral_rank2 b ((L.O_def y).mp hy))

end PI.UnitaryGroupMassFormula.CntFormula.DeltaC
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.GoodRDet
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.DetGa

open Matrix

section General

variable {R : Type*} [CommRing R] {k : ℕ}

def cornerM (k : ℕ) (s : R) : Matrix (Fin (k + 1)) (Fin (k + 1)) R :=
  Matrix.of fun a b => if a = Fin.last k ∧ b = Fin.last k then s else 0

theorem det_updateRow_last_single (A : Matrix (Fin (k + 1)) (Fin (k + 1)) R) :
    (A.updateRow (Fin.last k) (Pi.single (Fin.last k) 1)).det = (A.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [Matrix.det_succ_row _ (Fin.last k), Finset.sum_eq_single (Fin.last k)]
  · have hs : (A.updateRow (Fin.last k) (Pi.single (Fin.last k) 1)).submatrix (Fin.last k).succAbove
        (Fin.last k).succAbove = A.submatrix Fin.castSucc Fin.castSucc := by
      ext i j
      simp [Fin.succAbove_last, Matrix.updateRow_ne (Fin.castSucc_lt_last i).ne]
    rw [hs]
    simp
  · intro j _ hj
    simp [Pi.single_apply, hj]
  · simp

theorem det_updateRow_last_zero (A : Matrix (Fin (k + 1)) (Fin (k + 1)) R) :
    (A.updateRow (Fin.last k) 0).det = 0 :=
  Matrix.det_eq_zero_of_row_eq_zero (Fin.last k) fun j => by simp

theorem det_N (Z Y : Matrix (Fin (k + 1)) (Fin (k + 1)) R) (s t : R) :
    (Matrix.fromBlocks Z (cornerM k s) (cornerM k t) Y).det =
      Z.det * Y.det - s * t * ((Z.submatrix Fin.castSucc Fin.castSucc).det *
        (Y.submatrix Fin.castSucc Fin.castSucc).det) := by
  set i : Fin (k + 1) ⊕ Fin (k + 1) := Sum.inl (Fin.last k) with hi
  set j : Fin (k + 1) ⊕ Fin (k + 1) := Sum.inr (Fin.last k) with hj
  have hij : i ≠ j := by simp [hi, hj]
  set D0 : Matrix (Fin (k + 1) ⊕ Fin (k + 1)) (Fin (k + 1) ⊕ Fin (k + 1)) R := Matrix.fromBlocks Z 0 0 Y with hD0
  set f : ((Fin (k + 1) ⊕ Fin (k + 1)) → R) → ((Fin (k + 1) ⊕ Fin (k + 1)) → R) → R :=
    fun r1 r2 => ((D0.updateRow i r1).updateRow j r2).det with hf
  have hN : Matrix.fromBlocks Z (cornerM k s) (cornerM k t) Y =
      (D0.updateRow i (D0 i + s • Pi.single j 1)).updateRow j (D0 j + t • Pi.single i 1) := by
    ext (a | a) (b | b) <;>
      by_cases ha : a = Fin.last k <;> by_cases hb : b = Fin.last k <;>
      simp [hD0, hi, hj, cornerM, Matrix.updateRow_apply, Pi.single_apply, ha, hb]

  have hlin2 : ∀ r1 u v : (Fin (k + 1) ⊕ Fin (k + 1)) → R, ∀ c : R,
      f r1 (u + c • v) = f r1 u + c * f r1 v := by
    intro r1 u v c
    simp only [hf, Matrix.det_updateRow_add, Matrix.det_updateRow_smul]

  have hlin1 : ∀ r2 u v : (Fin (k + 1) ⊕ Fin (k + 1)) → R, ∀ c : R,
      f (u + c • v) r2 = f u r2 + c * f v r2 := by
    intro r2 u v c
    simp only [hf]
    rw [Matrix.updateRow_comm _ hij, Matrix.updateRow_comm _ hij, Matrix.updateRow_comm _ hij,
      Matrix.det_updateRow_add, Matrix.det_updateRow_smul]
  have hdet : (Matrix.fromBlocks Z (cornerM k s) (cornerM k t) Y).det =
      f (D0 i + s • Pi.single j 1) (D0 j + t • Pi.single i 1) := by
    rw [hN]

  have h00 : f (D0 i) (D0 j) = Z.det * Y.det := by
    simp only [hf, Matrix.updateRow_eq_self, hD0, Matrix.det_fromBlocks_zero₂₁]
  have h10 : f (Pi.single j 1) (D0 j) = 0 := by
    simp only [hf]
    rw [Matrix.updateRow_comm _ hij, Matrix.updateRow_eq_self]
    have : D0.updateRow i (Pi.single j 1) =
        Matrix.fromBlocks (Z.updateRow (Fin.last k) 0) (cornerM k 1) 0 Y := by
      ext (a | a) (b | b) <;>
        by_cases ha : a = Fin.last k <;> by_cases hb : b = Fin.last k <;>
        simp [hD0, hi, hj, cornerM, Matrix.updateRow_apply, Pi.single_apply, ha, hb]
    rw [this, Matrix.det_fromBlocks_zero₂₁, det_updateRow_last_zero, zero_mul]
  have h01 : f (D0 i) (Pi.single i 1) = 0 := by
    simp only [hf, Matrix.updateRow_eq_self]
    have : D0.updateRow j (Pi.single i 1) =
        Matrix.fromBlocks Z 0 (cornerM k 1) (Y.updateRow (Fin.last k) 0) := by
      ext (a | a) (b | b) <;>
        by_cases ha : a = Fin.last k <;> by_cases hb : b = Fin.last k <;>
        simp [hD0, hi, hj, cornerM, Matrix.updateRow_apply, Pi.single_apply, ha, hb]
    rw [this, Matrix.det_fromBlocks_zero₁₂, det_updateRow_last_zero, mul_zero]
  have h11 : f (Pi.single j 1) (Pi.single i 1) =
      -((Z.submatrix Fin.castSucc Fin.castSucc).det * (Y.submatrix Fin.castSucc Fin.castSucc).det) := by
    simp only [hf]
    have hsw : ((D0.updateRow i (Pi.single j 1)).updateRow j (Pi.single i 1)).submatrix
        (Equiv.swap i j) id =
        Matrix.fromBlocks (Z.updateRow (Fin.last k) (Pi.single (Fin.last k) 1)) 0 0
          (Y.updateRow (Fin.last k) (Pi.single (Fin.last k) 1)) := by
      ext (a | a) (b | b) <;>
        by_cases ha : a = Fin.last k <;> by_cases hb : b = Fin.last k <;>
        simp [hD0, hi, hj, Matrix.updateRow_apply, Pi.single_apply, Equiv.swap_apply_def, ha, hb]
    have h := Matrix.det_permute (Equiv.swap i j) ((D0.updateRow i (Pi.single j 1)).updateRow j (Pi.single i 1))
    rw [hsw, Matrix.det_fromBlocks_zero₂₁, det_updateRow_last_single, det_updateRow_last_single,
      Equiv.Perm.sign_swap hij] at h
    rw [h]
    simp
  rw [hdet, hlin2, hlin1, hlin1, h00, h10, h01, h11]
  ring

end General

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem ga_eq_submatrix (D : Formalism.BasicNotions.D7) (T T' : D.host.E) (Z : MatZ D) :
    Ga T T' Z = (Matrix.fromBlocks Z (cornerM D.R.rS (-T)) (cornerM D.R.rS (-T')) Z.conjTranspose).submatrix id
      (Equiv.sumComm _ _) := by
  ext (a | a) (b | b) <;> simp [Ga, cornerM, Matrix.fromBlocks]

theorem leadMinorE_full (D : Formalism.BasicNotions.D7) (Z : MatZ D) : leadMinorE Z (D.R.rS + 1) = Z.det := by
  unfold leadMinorE
  rw [dite_eq_left le_rfl]
  congr 1

theorem leadMinorE_prev (D : Formalism.BasicNotions.D7) (Z : MatZ D) :
    leadMinorE Z D.R.rS = (Z.submatrix Fin.castSucc Fin.castSucc).det := by
  unfold leadMinorE
  rw [dite_eq_left (Nat.le_succ _)]
  congr 1

theorem det_Ga (D : Formalism.BasicNotions.D7) (T T' : D.host.E) (Z : MatZ D) :
    (Ga T T' Z).det = ((Equiv.Perm.sign (Equiv.sumComm (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1))) : ℤ) : D.host.E) *
      GZ T T' Z := by
  rw [ga_eq_submatrix, Matrix.det_permute', det_N, GZ, leadMinorE_full, leadMinorE_prev,
    Matrix.det_conjTranspose, ← Matrix.conjTranspose_submatrix, Matrix.det_conjTranspose]
  push_cast
  ring

end PI.UnitaryGroupMassFormula.CntFormula.DetGa

namespace PI.UnitaryGroupMassFormula.CntFormula

theorem gram_determinant_ne_zero : DetGaNe := by
  intro D T T' Z hG
  rw [DetGa.det_Ga]
  refine mul_ne_zero ?_ hG
  rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.sumComm (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)))) with h | h <;>
    rw [h] <;> simp

end PI.UnitaryGroupMassFormula.CntFormula
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DensGS
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal IsDedekindDomain
open Classical ValuativeRel

def SplitCount : Prop :=
  ∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] [MeasurableSpace E] (M : Loc.Model F E),
    IsNonarchimedeanLocalField F → CharZero F →
    (∃ e : E ≃ₐ[F] F × F, ∀ x, e (M.L.cj x) = (e x).swap) →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) (Λ : Submodule M.L.O V),
      H.IsSelfDual Λ → ∀ ϖ : 𝒪[F], Irreducible ϖ →
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G₀ : Matrix ι ι E), (∀ a b, G₀ a b ∈ M.L.O) →
        (∀ a b, G₀ b a = M.L.cj (G₀ a b)) → (∃ y ∈ M.L.O, G₀.det * y = 1) →
        Fintype.card ι ≤ Module.finrank E V →
        ∃ (Ph : Matrix (Fin (Module.finrank E V)) (Fin (Module.finrank E V)) 𝓀[F])
          (Gm : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) 𝓀[F]),
          IsUnit Ph.det ∧ Gm.rank = Fintype.card ι ∧
          H.dens ϖ Λ G₀ * (Nat.card 𝓀[F] : ℝ) ^
              ((2 * Module.finrank E V * Fintype.card ι : ℤ) - (Fintype.card ι : ℤ) ^ 2) =
            (Formalism.L2.SG.DensExact.countSplit 𝓀[F] (Module.finrank E V) (Fintype.card ι) Ph Gm : ℝ)

def OSplit : Prop :=
  ∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] (L : Loc.LocE F E), IsNonarchimedeanLocalField F →
    ∀ (e : E ≃ₐ[F] F × F) (x : E), x ∈ L.O ↔ (e x).1 ∈ 𝒪[F] ∧ (e x).2 ∈ 𝒪[F]

def IsSplitCoord {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E} (e : E ≃ₐ[F] F × F)
    {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) (Λ : Submodule M.L.O V) {n : ℕ}
    (π : V ≃+ (Fin n → F) × (Fin n → F)) (Ph : Matrix (Fin n) (Fin n) 𝒪[F]) : Prop :=
  (∀ (a : E) (x : V), π (a • x) = ((e a).1 • (π x).1, (e a).2 • (π x).2)) ∧
  (∀ x : V, x ∈ Λ ↔ (∀ k, (π x).1 k ∈ 𝒪[F]) ∧ ∀ k, (π x).2 k ∈ 𝒪[F]) ∧
  IsUnit Ph.det ∧
  ∀ x y : V, e (H.h x y) =
    (∑ k, ∑ l, (π x).1 k * (Ph k l : F) * (π y).2 l, ∑ k, ∑ l, (π y).1 k * (Ph k l : F) * (π x).2 l)

def CoordData : Prop :=
  ∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] [MeasurableSpace E] (M : Loc.Model F E),
    IsNonarchimedeanLocalField F → CharZero F →
    ∀ (e : E ≃ₐ[F] F × F), (∀ x, e (M.L.cj x) = (e x).swap) →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) (Λ : Submodule M.L.O V),
      H.IsSelfDual Λ →
      ∃ (π : V ≃+ (Fin (Module.finrank E V) → F) × (Fin (Module.finrank E V) → F))
        (Ph : Matrix (Fin (Module.finrank E V)) (Fin (Module.finrank E V)) 𝒪[F]), IsSplitCoord e H Λ π Ph

end PI.UnitaryGroupMassFormula.CntFormula
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.EichLApply
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def InW (D : Formalism.BasicNotions.D7) (y : (VS D).V) : Prop :=
  (∀ a, (VS D).hT (D.sp.hypE a) y = 0) ∧ (∀ a, (VS D).hT (D.sp.hypF a) y = 0) ∧ (VS D).hT D.sp.zm y = 0

theorem hT_star (D : Formalism.BasicNotions.D7) (x y : (VS D).V) : star ((VS D).hT x y) = (VS D).hT y x := by
  have h := (VS D).herm
  first
  | exact h x y
  | exact h.eq x y
  | simpa using h x y
  | simpa using h.eq x y

theorem T_ne (D : Formalism.BasicNotions.D7) : (D.sp.T : D.host.E) ≠ 0 := by
  have h := D.sp.T_prime.ne_zero
  exact_mod_cast h

theorem hZE (D : Formalism.BasicNotions.D7) (i : Fin D.R.rS) : (VS D).hT D.sp.zm (D.sp.hypE i) = 0 := by exact (D.sp.hyp_orthz i).1
theorem hZF (D : Formalism.BasicNotions.D7) (i : Fin D.R.rS) : (VS D).hT D.sp.zm (D.sp.hypF i) = 0 := by exact (D.sp.hyp_orthz i).2
theorem hEZ (D : Formalism.BasicNotions.D7) (i : Fin D.R.rS) : (VS D).hT (D.sp.hypE i) D.sp.zm = 0 := by
  rw [← hT_star D D.sp.zm (D.sp.hypE i), hZE, star_zero]
theorem hFZ (D : Formalism.BasicNotions.D7) (i : Fin D.R.rS) : (VS D).hT (D.sp.hypF i) D.sp.zm = 0 := by
  rw [← hT_star D D.sp.zm (D.sp.hypF i), hZF, star_zero]

def pWL (D : Formalism.BasicNotions.D7) : (VS D).V →ₗ[D.host.E] (VS D).V :=
  LinearMap.id - ∑ a, ((VS D).hT (D.sp.hypF a)).smulRight (D.sp.hypE a)
    - ∑ a, ((VS D).hT (D.sp.hypE a)).smulRight (D.sp.hypF a)
    + ((D.sp.T : D.host.E)⁻¹) • ((VS D).hT D.sp.zm).smulRight D.sp.zm

theorem pW_eq (D : Formalism.BasicNotions.D7) (v : (VS D).V) : pW D v = pWL D v := by
  simp only [pW, pWL, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply,
    LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.smul_apply, smul_smul, div_eq_inv_mul]

theorem pW_sub (D : Formalism.BasicNotions.D7) (u v : (VS D).V) : pW D (u - v) = pW D u - pW D v := by simp only [pW_eq, map_sub]

private theorem hT_hypF_hypE (D : Formalism.BasicNotions.D7) (a i : Fin D.R.rS) :
    (VS D).hT (D.sp.hypF a) (D.sp.hypE i) = if a = i then 1 else 0 := by
  rw [← hT_star D (D.sp.hypE i) (D.sp.hypF a), D.sp.hyp_ef i a]
  by_cases h : a = i
  · subst h
    simp
  · simp [h, Ne.symm h]

theorem inW_pW (D : Formalism.BasicNotions.D7) (v : (VS D).V) : InW D (pW D v) := by
  have hT0 := T_ne D
  unfold InW
  refine ⟨fun b => ?_, fun b => ?_, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · simp [pW, map_sum, D.sp.hyp_ee, D.sp.hyp_ef, hEZ, mul_ite, Finset.sum_ite_eq]
  set_option synthInstance.maxHeartbeats 100000 in
    · simp [pW, map_sum, hT_hypF_hypE, D.sp.hyp_ff, hFZ, mul_ite, Finset.sum_ite_eq']
  set_option synthInstance.maxHeartbeats 100000 in
    · simp [pW, map_sum, hZE, hZF, D.sp.zm_norm, div_mul_cancel₀, hT0]

def eichL (D : Formalism.BasicNotions.D7) (e y : (VS D).V) (c : D.host.E) : (VS D).V →ₗ[D.host.E] (VS D).V :=
  LinearMap.id + ((VS D).hT e).smulRight y - ((VS D).hT y).smulRight e + c • ((VS D).hT e).smulRight e

theorem eichL_apply (D : Formalism.BasicNotions.D7) (e y : (VS D).V) (c : D.host.E) (v : (VS D).V) :
    eichL D e y c v = v + (VS D).hT e v • y - (VS D).hT y v • e + (c * (VS D).hT e v) • e := by
  simp only [eichL, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply,
    LinearMap.smulRight_apply, LinearMap.smul_apply, smul_smul]

theorem eich_inv (D : Formalism.BasicNotions.D7) {e y : (VS D).V} {c : D.host.E} (he : (VS D).hT e e = 0)
    (hey : (VS D).hT e y = 0) (hye : (VS D).hT y e = 0) (hc : c + c + (VS D).hT y y = 0) (v : (VS D).V) :
    eichL D e (-y) c (eichL D e y c v) = v := by
  have h1 : (VS D).hT e (eichL D e y c v) = (VS D).hT e v := by
    simp [eichL_apply, he, hey]
  have h2 : (VS D).hT y (eichL D e y c v) = (VS D).hT y v + (VS D).hT e v * (VS D).hT y y := by
    simp [eichL_apply, hye] <;> ring
  have hc' : (VS D).hT e v * (c + c + (VS D).hT y y) = 0 := by rw [hc, mul_zero]
  rw [eichL_apply D e (-y) c (eichL D e y c v), h1]
  simp only [map_neg, LinearMap.neg_apply, h2]
  rw [eichL_apply D e y c v]
  linear_combination (norm := module) hc' • e

theorem eich_isom (D : Formalism.BasicNotions.D7) {e y : (VS D).V} {c : D.host.E} (he : (VS D).hT e e = 0)
    (hey : (VS D).hT e y = 0) (hye : (VS D).hT y e = 0) (hc : c + star c + (VS D).hT y y = 0)
    (u v : (VS D).V) : (VS D).hT (eichL D e y c u) (eichL D e y c v) = (VS D).hT u v := by
  have hE : ∀ w, (VS D).hT e (eichL D e y c w) = (VS D).hT e w := fun w => by
    simp [eichL_apply, he, hey]
  have hY : ∀ w, (VS D).hT y (eichL D e y c w) = (VS D).hT y w + (VS D).hT e w * (VS D).hT y y := fun w => by
    simp [eichL_apply, hye] <;> ring
  have hU : ∀ w, (VS D).hT u (eichL D e y c w) = (VS D).hT u w + (VS D).hT e w * star ((VS D).hT y u)
      - (VS D).hT y w * star ((VS D).hT e u) + c * (VS D).hT e w * star ((VS D).hT e u) := fun w => by
    rw [hT_star D y u, hT_star D e u]
    simp [eichL_apply] <;> ring
  rw [eichL_apply D e y c u]
  simp only [map_add (f := _), map_sub, map_smulₛₗ, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul, hE, hY, hU, starRingEnd_apply, star_mul']
  linear_combination (star ((VS D).hT e u) * (VS D).hT e v) * hc

end PI.UnitaryGroupMassFormula.CntFormula
end
end
