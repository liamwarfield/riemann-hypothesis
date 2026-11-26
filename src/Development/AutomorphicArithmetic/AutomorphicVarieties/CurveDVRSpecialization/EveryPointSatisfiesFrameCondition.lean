module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SecondThirdPrimeConditionTransferAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RankTwoAutomorphyDescendsFromAbelianCMToRat
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ArithmeticPointClassicality
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShapeFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.ExistsNrep3

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.EveryPointSatisfiesFrameCondition
noncomputable section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af

namespace UpperTheory.V.Pr

instance (priority := high) fieldTorsionFree (L Ω : Type) [Field L] [Field Ω] [Algebra L Ω] : Module.IsTorsionFree L Ω :=
  DivisionSemiring.to_moduleIsTorsionFree

def CoefIs : Prop := ∀ (l : ℕ) [Fact l.Prime] (c : Coef l), Fr.IsCoef l c.O

def CoefEx : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (ka ka' : G L Ω →* (Qbar l)ˣ), Continuous ka → Continuous ka' →
    ∃ c₁ : Coef l, c.O ≤ c₁.O ∧ W.Large L c₁ ∧ (∀ g, (ka g).val ∈ c₁.O) ∧ (∀ g, (ka' g).val ∈ c₁.O) ∧
      ∃ f : ResidueField c.O →+* ResidueField c₁.O, ∀ (a : c.O) (b : c₁.O), a.1 = b.1 → f (residue c.O a) = residue c₁.O b

section

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
  {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* c.Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ}
  {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] {Φ : Fr.Frame l (ResidueField c.O)}


variable (σ M) in
structure IsKa (ι : Qbar l ≃+* ℂ) (n : ℕ) (ka : G L Ω →* (Qbar l)ˣ) : Prop where
  alg : Sd.IsAlgChar ι ka
  conj : ∀ s s' : G L Ω, galEmb ℚ L Ω s' = σ * galEmb ℚ L Ω s * σ⁻¹ → ka s * ka s' = cycBar L Ω l s ^ (1 - (n : ℤ))
  unr : ∀ A : ValuationSubring Ω, ¬ A.valuation (M : Ω) < 1 → ∀ s ∈ Ine (F := L) A, ka s = 1
  ord : ∃ m : ℕ, ¬ l ∣ m ∧ ∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∀ s ∈ Ine (F := L) A, ka s ^ m = 1

structure CReal (k : GalLink η Ψ σ g₁ B M L Φ) (c₁ : Coef l) [Fr.IsCoef l c₁.O]
    (f : ResidueField c.O →+* ResidueField c₁.O) (n : ℕ) (ka : G L Ω →* (Qbar l)ˣ) : Type 1 where
  n23 : n = 2 ∨ n = 3
  C₀ : ℕ
  ok : (Φ.ext f).Ok C₀
  big : (Φ.ext f).Big C₀
  le : c.O ≤ c₁.O
  hf : ∀ (a : c.O) (b : c₁.O), a.1 = b.1 → f (residue c.O a) = residue c₁.O b
  s : W.HidaSetting l L Ω
  V : s.Lev
  hV : V.S' = s.S
  r : W.Resid V.frame c₁.O n
  K : TwLink (Φ.ext f) r
  π_pr : ∀ g, K.π (V.pr g) = k.p0 g
  κ_pr : ∀ g, (K.κ (V.pr g)).val.1 = (ka g).val
  lam_j : ∀ (v : W.Vl l L) (g : Dec (F := L) (s.A v)), (k.j (K.e v) (K.lam v g)).1 = galEmb ℚ L Ω g
  A_pl : ∀ v : W.Vl l L, s.A v = k.pl (K.e v)
  v0 : r.V0ok
  v0M : ¬ (s.A s.v0).valuation (M : Ω) < 1
  B₀ : W.UniversalOrdinaryDeterminantRing r
  S : Fr.Space c₁.O (Φ.ext f) n

def CReal.T {k : GalLink η Ψ σ g₁ B M L Φ} {c₁ : Coef l} [Fr.IsCoef l c₁.O] {f : ResidueField c.O →+* ResidueField c₁.O}
    {n : ℕ} {ka : G L Ω →* (Qbar l)ˣ} (R : CReal k c₁ f n ka) : Setup (Φ.ext f) n :=
  ⟨R.n23, R.C₀, R.ok, R.big, Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero, R.V.frame, R.r, R.K, R.B₀, R.S⟩

end

structure LinkHyp {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (c : Coef l)
    (N e : ℕ) (η : G ℚ Ω →* ℤˣ) (σ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ) : Prop where
  e_pos : 1 ≤ e
  dvd : l * N ∣ M
  M_pos : M ≠ 0
  ram : ∀ B' : ValuationSubring Ω, ¬ Ine (F := ℚ) B' ≤ η.ker → B'.valuation (M : Ω) < 1
  atl : B.valuation (l : Ω) < 1
  cc : Sd.IsCC σ

def KaOf : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : Coef l)
    [CharP (ResidueField c.O) l] (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N)
    (η : G ℚ Ω →* ℤˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ), LinkHyp c N e η σ B M →
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] (Φ : Fr.Frame l (ResidueField c.O))
    (k : GalLink η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B M L Φ), IsKa σ M ι 3 (cycBar L Ω l)⁻¹ ∧
    ∀ (K : Type) [Field K] [NumberField K] [Algebra K Ω], η.ker = galOf ℚ K Ω → ∀ κ : G K Ω →* (Qbar l)ˣ, Sd.IsTwist ι σ κ →
      ∃ ka : G L Ω →* (Qbar l)ˣ, IsKa σ M ι 2 ka ∧ ∀ (s : G L Ω) (s' : G K Ω), galEmb ℚ L Ω s = galEmb ℚ K Ω s' → ka s = κ s'

def CRealEx : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : Coef l)
    [CharP (ResidueField c.O) l] (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N)
    (η : G ℚ Ω →* ℤˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ), LinkHyp c N e η σ B M →
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] (Φ : Fr.Frame l (ResidueField c.O))
    (k : GalLink η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B M L Φ)
    (c₁ : Coef l) [Fr.IsCoef l c₁.O] (f : ResidueField c.O →+* ResidueField c₁.O) (n : ℕ)
    (ka : G L Ω →* (Qbar l)ˣ) (C₀ : ℕ), (n = 2 ∨ n = 3) → Φ.Ok C₀ → Φ.Big C₀ → c.O ≤ c₁.O →
    (∀ (a : c.O) (b : c₁.O), a.1 = b.1 → f (residue c.O a) = residue c₁.O b) → IsKa σ M ι n ka → (∀ g, (ka g).val ∈ c₁.O) →
    Nonempty (CReal k c₁ f n ka)

def DegEq : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : Coef l)
    [CharP (ResidueField c.O) l] (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N)
    (η : G ℚ Ω →* ℤˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ), LinkHyp c N e η σ B M →
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] (Φ : Fr.Frame l (ResidueField c.O))
    (k : GalLink η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B M L Φ), Φ.V → Φ.d = Module.finrank ℚ (W.Lp L) ∧ ¬ ∃ ζ : L, IsPrimitiveRoot ζ l

def EveryPointSatisfiesFrameCondition : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : Coef l)
    [CharP (ResidueField c.O) l] (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N)
    (η : G ℚ Ω →* ℤˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ), LinkHyp c N e η σ B M →
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] (Φ : Fr.Frame l (ResidueField c.O))
    (k : GalLink η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B M L Φ)
    (c₁ : Coef l) [Fr.IsCoef l c₁.O] (f : ResidueField c.O →+* ResidueField c₁.O) (n : ℕ)
    (ka : G L Ω →* (Qbar l)ˣ) (R : CReal k c₁ f n ka) (y : W.Point R.r), y.N4

def FinPtDown : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (c c₁ : Coef l) (f : ResidueField c.O →+* ResidueField c₁.O), c.O ≤ c₁.O →
    (∀ (a : c.O) (b : c₁.O), a.1 = b.1 → f (residue c.O a) = residue c₁.O b) →
    ∀ (Φ : Fr.Frame l (ResidueField c.O)) (n : ℕ), FinPt c₁.O (Φ.ext f) n → FinPt c.O Φ n

def DimOf : Prop :=
  ∀ (O Λ B : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing Λ] [Algebra O Λ] [CommRing B]
    [IsNoetherianRing B] (φ : Λ →+* B) (J : Ideal B) (m : ℕ), Nonempty (Λ ≃ₐ[O] MvPowerSeries (Fin m) O) →
    ((Ideal.Quotient.mk J).comp φ).Finite → (∀ a : Λ, a ≠ 0 → ∀ b : B, φ a * b ∈ J → b ∈ J) →
    ∀ Z ∈ J.minimalPrimes, qdim Z = ((1 + m : ℕ) : WithBot ℕ∞)

end UpperTheory.V.Pr

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.ExistsNrep2
open NumberField IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Aut UpperTheory.V.Pr UpperTheory.V

namespace UpperTheory.V.Pr.LkPt2

open Matrix

section Mat

variable {A : Type} [CommRing A]

private def Bl (X : Matrix (Fin 3) (Fin 3) A) : Prop := X 0 1 = 0 ∧ X 1 0 = 0 ∧ X 1 2 = 0 ∧ X 2 1 = 0

private theorem c00 (X : Matrix (Fin 3) (Fin 3) A) : corner X 0 0 = X 0 0 := rfl
private theorem c01 (X : Matrix (Fin 3) (Fin 3) A) : corner X 0 1 = X 0 2 := rfl
private theorem c10 (X : Matrix (Fin 3) (Fin 3) A) : corner X 1 0 = X 2 0 := rfl
private theorem c11 (X : Matrix (Fin 3) (Fin 3) A) : corner X 1 1 = X 2 2 := rfl

private theorem corner_mul {X : Matrix (Fin 3) (Fin 3) A} (hX : Bl X) (Y : Matrix (Fin 3) (Fin 3) A) :
    corner (X * Y) = corner X * corner Y := by
  obtain ⟨h1, h2, h3, h4⟩ := hX
  ext i j
  fin_cases i <;> fin_cases j <;> simp [c00, c01, c10, c11, Matrix.mul_apply, Fin.sum_univ_three, h1, h4]

private theorem corner_one : corner (1 : Matrix (Fin 3) (Fin 3) A) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [c00, c01, c10, c11]

private theorem corner_sub (X : Matrix (Fin 3) (Fin 3) A) (a : A) :
    corner (X - a • (1 : Matrix (Fin 3) (Fin 3) A)) = corner X - a • (1 : Matrix (Fin 2) (Fin 2) A) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [c00, c01, c10, c11]

private theorem block_sub {X : Matrix (Fin 3) (Fin 3) A} (hX : Bl X) (a : A) :
    Bl (X - a • (1 : Matrix (Fin 3) (Fin 3) A)) := by
  obtain ⟨h1, h2, h3, h4⟩ := hX
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [*]

private theorem corner_J (X : Matrix (Fin 3) (Fin 3) A) :
    corner (Jmat A 3 * Xᵀ * Jmat A 3) = Jmat A 2 * (corner X)ᵀ * Jmat A 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [c00, c01, c10, c11, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, Jmat, Fin.rev]

private theorem ch2 (S : Matrix (Fin 2) (Fin 2) A) (y : A) :
    ((S.trace - y) • (1 : Matrix (Fin 2) (Fin 2) A) - S) * (S - y • 1) = (S - y • 1).det • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two, Matrix.trace_fin_two] <;> ring

private theorem drop_mid {H : Type} [Group H] (σ : H →* Matrix (Fin 2) (Fin 2) A) (ψ : H →* Aˣ) (t : H) (y : A)
    (Z : Matrix (Fin 2) (Fin 2) A) (hu : IsUnit (σ t - y • 1).det)
    (h : ∀ a, (σ a - (ψ a : A) • 1) * ((σ t - y • 1) * Z) = 0) (a : H) : (σ a - (ψ a : A) • 1) * Z = 0 := by
  have e : (σ a - (ψ a : A) • 1) * (((σ t).trace - y) • (1 : Matrix (Fin 2) (Fin 2) A) - σ t) =
      ((σ t).trace - y) • (σ a - (ψ a : A) • 1) - (σ (a * t) - (ψ (a * t) : A) • 1) +
        (ψ a : A) • (σ t - (ψ t : A) • 1) := by
    rw [map_mul, map_mul, Units.val_mul, Matrix.mul_sub, Matrix.sub_mul (σ a) _ (σ t), Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul, Matrix.one_mul, smul_sub (ψ a : A), smul_smul]
    abel
  have e2 : (σ t - y • 1).det • ((σ a - (ψ a : A) • 1) * Z) = 0 := by
    calc _ = (σ a - (ψ a : A) • 1) * ((((σ t).trace - y) • (1 : Matrix (Fin 2) (Fin 2) A) - σ t) * (σ t - y • 1)) * Z := by
          rw [ch2, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
      _ = 0 := by
          rw [← Matrix.mul_assoc, e, Matrix.mul_assoc, Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul,
            h, h, h]
          simp
  exact (hu.smul_eq_zero).1 e2

end Mat

private theorem w_eq (i : Fin 2) : Fr.w 2 i = Fr.w 3 (![0, 2] i) := by fin_cases i <;> rfl

private theorem w_eq' (i : Fin 2) : Fr.w 2 i = wt1 (![0, 2] i) := by fin_cases i <;> rfl

private theorem ne_of {i j : Fin 2} (h : i ≠ j) : (![0, 2] i : Fin 3) ≠ ![0, 2] j := by
  revert h; fin_cases i <;> fin_cases j <;> decide

private theorem ex_block {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {F : Fr.Frame l (ResidueField O)}
    (f3 : ∀ v, ∃ g, F.Ψ (F.loc v g) ^ 2 ≠ 1) {A : Type} [CommRing A] [IsLocalRing A] [Algebra O A]
    [IsLocalHom (algebraMap O A)] (ρ : Fr.NRep F 3 A) (hρ : IsLiftA O ρ) (hb : ∀ g, Bl (ρ.r g)) :
    ∃ ρ' : Fr.NRep F 2 A, IsLiftA O ρ' ∧ (∀ g, ρ'.r g = corner (ρ.r g)) ∧ ∀ v i, ρ'.ψ v i = ρ.ψ v (![0, 2] i) := by
  let σ : F.G0 →* Matrix (Fin 2) (Fin 2) A :=
    { toFun := fun g => corner (ρ.r g)
      map_one' := by rw [map_one, corner_one]
      map_mul' := fun g h => by rw [map_mul, corner_mul (hb g)] }
  have hσ : ∀ g, σ g = corner (ρ.r g) := fun _ => rfl
  refine ⟨⟨σ, fun v i => ρ.ψ v (![0, 2] i), fun g => ?_, fun i j h => ρ.diag _ _ (ne_of h), fun v g => ?_⟩,
    ⟨⟨fun i j => hρ.cont.1 _ _, fun v i => hρ.cont.2 v _⟩, ⟨fun g i => ?_, fun v i g => ?_⟩,
      fun g i j h => hρ.diag g _ _ (ne_of h)⟩, fun _ => rfl, fun _ _ => rfl⟩
  · rw [hσ, hσ, ρ.pol, corner_J]
  · obtain ⟨t, ht⟩ := f3 v
    have hu : IsUnit (σ (F.loc0 v t) - (ρ.ψ v 1 t : A) • (1 : Matrix (Fin 2) (Fin 2) A)).det := by
      rw [← residue_ne_zero_iff_isUnit]
      have a0 := hρ.bar.1 (F.loc0 v t) 0
      have a2 := hρ.bar.1 (F.loc0 v t) 2
      have b1 := hρ.bar.2 v 1 t
      have c0 := hρ.diag (F.loc0 v t) 0 2 (by decide)
      rw [Fr.NRep.map_r] at a0 a2 c0
      rw [Fr.NRep.map_ψ] at b1
      have w0 : Fr.w 3 0 = 1 := rfl
      have w1 : Fr.w 3 1 = 0 := rfl
      have w2 : Fr.w 3 2 = -1 := rfl
      rw [w0, zpow_one] at a0
      rw [w1, zpow_zero, Units.val_one, map_one] at b1
      rw [w2, _root_.zpow_neg_one] at a2
      have hne : F.Ψ (F.loc0 v t : F.Γ) ≠ 1 := fun e => ht (by
        show F.Ψ (F.loc0 v t : F.Γ) ^ 2 = 1
        rw [e, one_pow])
      have key : ∀ u : (ResidueField O)ˣ, u ≠ 1 → ResidueField.map (algebraMap O A) u - 1 ≠ 0 := fun u hu e => by
        rw [sub_eq_zero, ← map_one (ResidueField.map (algebraMap O A))] at e
        exact hu (Units.ext ((ResidueField.map (algebraMap O A)).injective e))
      have : residue A (σ (F.loc0 v t) - (ρ.ψ v 1 t : A) • (1 : Matrix (Fin 2) (Fin 2) A)).det =
          (residue A (ρ.r (F.loc0 v t) 0 0) - residue A (ρ.ψ v 1 t)) *
            (residue A (ρ.r (F.loc0 v t) 2 2) - residue A (ρ.ψ v 1 t)) -
            residue A (ρ.r (F.loc0 v t) 0 2) * residue A (ρ.r (F.loc0 v t) 2 0) := by
        simp [Matrix.det_fin_two, hσ, c00, c01, c10, c11]
      rw [this, a0, a2, b1, c0, zero_mul, sub_zero]
      exact mul_ne_zero (key _ hne) (key _ (inv_ne_one.2 hne))
    have := drop_mid (σ.comp (F.loc0 v)) (ρ.ψ v 0) t (ρ.ψ v 1 t : A)
      (σ (F.loc0 v (g 1)) - (ρ.ψ v 2 (g 1) : A) • 1) hu (fun a => by
        have h := congrArg corner (ρ.ord v ![a, t, g 1])
        simp only [Fr.ordProd, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one] at h
        rw [corner_mul (block_sub (hb _) _), corner_mul (block_sub (hb _) _), corner_sub, corner_sub, corner_sub] at h
        exact h) (g 0)
    simp only [Fr.ordProd, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one]
    exact this
  · rw [w_eq]
    exact hρ.bar.1 g _
  · rw [w_eq]
    exact hρ.bar.2 v _ g

end UpperTheory.V.Pr.LkPt2

open UpperTheory.V.Pr.LkPt2 in
theorem UpperTheory.V.Pr.exists_nrep2 :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ}
      {L : Type} [Field L] [NumberField L] [Algebra L Ω] {Φ : Fr.Frame l (ResidueField O)} (k : GalLink η Ψ σ g₁ B M L Φ) [CharP (ResidueField O) l] {C₀ : ℕ}, Φ.Ok C₀ → l ∣ M → σ * σ = 1 →
    ∀ {A : Type} [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [Algebra O A] [IsLocalHom (algebraMap O A)] (r : G ℚ Ω →* GG (m := 3) (R := A)), OrdPt l η Ψ σ g₁ B r → Block η r → ∃ ρ : Fr.NRep Φ 2 A, IsLiftA O ρ ∧ (∀ s : G L Ω, ρ.r (k.p0 s) = corner (r (Base.galEmb ℚ L Ω s)).mat) ∧
      ∀ v i, ∀ g ∈ Φ.Iv v, (ρ.ψ v i g : A) = algebraMap O A ((Ψ (k.j v g) ^ Fr.w 2 i : Oˣ) : O) := by
  intro Ω _ _ _ l _ O _ _ η Ψ σ g₁ B M L _ _ _ Φ k _ C₀ hok hM hσ A _ _ _ _ _ _ r hr hb
  obtain ⟨ρ, h1, h2, h3⟩ := exists_nrep3 k hok hM hσ r hr
  have hbl : ∀ g, Bl (ρ.r g) := fun g => by
    obtain ⟨u, hu⟩ := k.p_surj g.1
    have hη : η u = 1 := by rw [← k.del, hu]; exact g.2
    have hm : u.1 ∈ (Base.galEmb ℚ L Ω).range := by
      rw [Base.range_galEmb, k.gal]
      exact ⟨u.2, hη⟩
    obtain ⟨s, hs⟩ := hm
    have e : g = k.p0 s := Subtype.ext (hu.symm.trans (congrArg k.p (Subtype.ext hs.symm)))
    rw [e, h2, hs]
    exact ⟨hb _ hη _ _ (by decide), hb _ hη _ _ (by decide), hb _ hη _ _ (by decide), hb _ hη _ _ (by decide)⟩
  obtain ⟨ρ', a1, a2, a3⟩ := ex_block hok.f3 ρ h1 hbl
  refine ⟨ρ', a1, fun s => by rw [a2, h2], fun v i g hg => ?_⟩
  rw [a3, h3 v _ g hg, w_eq']
  rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.FinEndOfFinPt
open NumberField IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Aut UpperTheory.V.Pr UpperTheory.V

theorem UpperTheory.V.Pr.finEnd_of_finPt :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ}
      {L : Type} [Field L] [NumberField L] [Algebra L Ω] {Φ : Fr.Frame l (ResidueField O)} (k : GalLink η Ψ σ g₁ B M L Φ) [CharP (ResidueField O) l] {C₀ : ℕ}, Φ.Ok C₀ → l ∣ M → σ * σ = 1 →
    FinPt O Φ 3 → FinEnd l η Ψ σ g₁ B := by
  intro Ω _ _ _ l _ O _ _ η Ψ σ g₁ B M L _ _ _ Φ k _ C₀ hok hl hσ hF
  haveI : Module.IsTorsionFree L Ω := DivisionSemiring.to_moduleIsTorsionFree
  haveI : IsAlgClosure L Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) L⟩
  have hidx : (Base.galOf ℚ L Ω).index = Module.finrank ℚ L := (Base.galEmbTop ℚ L Ω).2.2
  refine ⟨Base.galOf ℚ L Ω, ⟨by rw [hidx]; exact Module.finrank_pos.ne'⟩, ?_⟩
  intro A _ _ _ h0 r hr g hg _
  haveI : IsNoetherianRing A := PrincipalIdealRing.isNoetherianRing
  let f : ResidueField O →+* A := Ideal.Quotient.lift (maximalIdeal O) (algebraMap O A) h0
  have hf : ∀ a : O, f (residue O a) = algebraMap O A a := fun a => rfl
  letI : Algebra (ResidueField O) A := f.toAlgebra
  haveI : IsScalarTower O (ResidueField O) A := IsScalarTower.of_algebraMap_eq fun a => (hf a).symm
  obtain ⟨ρ, h1, h2, h3⟩ := exists_nrep3 k hok hl hσ r hr
  have hpow : ∀ (s : G ℚ Ω) (n : ℤ), algebraMap O A ((Ψ s ^ n : Oˣ) : O) =
      f ((barChar O Ψ s ^ n : (ResidueField O)ˣ) : ResidueField O) := by
    intro s n
    rw [← hf]
    congr 1
    exact congrArg Units.val (map_zpow (Units.map (residue O).toMonoidHom) (Ψ s) n)
  have key := hF A ρ h1 (by
    intro v i g hg h
    apply Units.ext
    rw [h3 v i g hg, UnitaryThreeInertia.psi, hpow]
    rw [k.j_loc, k.psi] at h
    rw [h]; simp)
  obtain ⟨s, rfl⟩ : ∃ s, Base.galEmb ℚ L Ω s = g := (Base.range_galEmb ℚ L Ω).ge hg
  rw [← h2, key]
  have : ((r0 η Ψ (Base.galEmb ℚ L Ω s)).mat).map (algebraMap O A) = Matrix.diagonal fun i =>
      algebraMap O A ((Ψ (Base.galEmb ℚ L Ω s) ^ wt1 i : Oˣ) : O) := by
    rw [GG.mat, unitaryThreeReflection_left, tor_val, Matrix.diagonal_map (map_zero _)]
  rw [this, Matrix.charpoly_diagonal]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [hpow]
  have h5 : Φ.Ψ (k.p0 s) = barChar O Ψ (Base.galEmb ℚ L Ω s) := k.psi _
  have h6 : Fr.w 3 i = wt1 i := by fin_cases i <;> rfl
  rw [h5, h6]
  rfl
end
