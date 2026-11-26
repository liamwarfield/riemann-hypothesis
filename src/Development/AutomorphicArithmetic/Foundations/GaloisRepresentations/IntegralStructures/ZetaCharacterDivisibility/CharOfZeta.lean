module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PhiOfDivOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PPtChart

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.CharOfZeta
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.Int.Div

variable (E : Type) [Field E] [NumberField E] [IsCMField E]

abbrev cj : Ideles E →* Ideles E := Units.map (conjAd E).toMonoidHom

def quo : Ideles E →* Ideles E := (MonoidHom.id (Ideles E)) / cj E

theorem quo_apply (z : Ideles E) : quo E z = z / cj E z := rfl

def IsZeta (a : ℕ) (ζ : Ideles E →* UA E a) : Prop :=
  ∀ z, ((ζ z : UA E a) : GA E a) = Matrix.GeneralLinearGroup.scalar (Fin a) (quo E z)

def ZetaEx : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ), ∃ ζ : Ideles E →* UA E a, IsZeta E a ζ ∧ Continuous ζ ∧
    (∀ z x, ζ z * x = x * ζ z) ∧ (∀ k : Eˣ, ζ (diagUnits E k) ∈ ratU E a) ∧ ∀ z, cj E z = z → ζ z = 1

def ZetaLoc : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (ζ : Ideles E →* UA E a), IsZeta E a ζ →
    ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → ∀ u : (w.adicCompletion E)ˣ,
      ζ (localIdele E w u) ∈ locU a w ∧ cLoc w (ζ (localIdele E w u)) = Matrix.GeneralLinearGroup.scalar (Fin a) u

def SchurU : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (U : Submodule ℂ (UA E a → ℂ)), IsAutRepU U →
    ∀ z : UA E a, (∀ x, z * x = x * z) → ∃ c : ℂ, ∀ φ ∈ U, RU E a z φ = c • φ

def CharOfZeta : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (U : Submodule ℂ (UA E a → ℂ)), IsAutRepU U →
    ∀ ζ : Ideles E →* UA E a, Continuous ζ → (∀ z x, ζ z * x = x * ζ z) → (∀ k : Eˣ, ζ (diagUnits E k) ∈ ratU E a) →
    (∀ z, ∃ c : ℂ, ∀ φ ∈ U, RU E a (ζ z) φ = c • φ) →
    ∃ χ : HChar E, ∀ z, ∀ φ ∈ U, RU E a (ζ z) φ = ((χ.1 z : ℂˣ) : ℂ) • φ

def AlgOfFix : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (χ : HChar E), (∀ z, cj E z = z → χ.1 z = 1) →
    ∃ n : (E →+* ℂ) → ℤ, IsAlgPos χ n

def SatCent : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin a) (w.adicCompletion E)))
    (B : Multiset ℂˣ), GlobalTheory.LFun.HasSatGL w σ.ρ B → ∃ x : σ.V, x ≠ 0 ∧
      (∀ u : (w.adicCompletion E)ˣ, IsUnitAt w u → σ.ρ (Matrix.GeneralLinearGroup.scalar (Fin a) u) x = x) ∧
      ∀ u : (w.adicCompletion E)ˣ, IsUnifAt w u →
        σ.ρ (Matrix.GeneralLinearGroup.scalar (Fin a) u) x = ((B.prod : ℂˣ) : ℂ) • x

end UpperTheory.Gal.Int.Div

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PRootPin
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.BlockSum (blockRep)
open PositivityTheory.AutomorphicGaloisHodgeTate.Div (DivWCoreLac SenWLac HTLac IsSSMat)
open UpperTheory.Gal.Int.Div

theorem UpperTheory.Gal.Int.Div.rootPin_of :
    RootPin := by
  intro p s m hp hdeg hdvd hprod hgen
  have hspl : p.Splits := IsAlgClosed.splits p
  have hq : rootPol s ^ m ≠ 0 := by
    apply pow_ne_zero
    exact (monic_multiset_prod_of_monic _ _ (fun a _ => monic_X_sub_C a)).ne_zero
  have hle : p.roots ≤ (rootPol s ^ m).roots := Polynomial.roots.le_of_dvd hq hdvd
  have hroots : (rootPol s ^ m).roots = m • s := by
    rw [Polynomial.roots_pow]
    unfold rootPol
    rw [roots_multiset_prod_X_sub_C]
  have hcard : p.roots.card = s.card := by
    rw [splits_iff_card_roots.mp hspl, hdeg]
  have hmem : ∀ x ∈ p.roots, x ∈ s := by
    intro x hx
    have := Multiset.mem_of_le hle hx
    rw [hroots, Multiset.mem_nsmul] at this
    exact this.2
  have heq : p.roots = s := hgen _ hcard hmem hprod
  rw [hspl.eq_prod_roots_of_monic hp, heq]
  rfl
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PDGenMul
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.BlockSum (blockRep)
open PositivityTheory.AutomorphicGaloisHodgeTate.Div (DivWCoreLac SenWLac HTLac IsSSMat)
open UpperTheory.Gal.Int.Div

theorem UpperTheory.Gal.Int.Div.dGenMul_of :
    DGenMul := by
  classical
  intro a q B ha hc hG
  obtain ⟨α, rfl⟩ : ∃ α : Fin a → ℂˣ, Finset.univ.val.map α = B := by
    induction B using Quotient.inductionOn with
    | h l =>
      have hl : l.length = a := hc
      subst hl
      exact ⟨l.get, by rw [Fin.univ_val_map, List.ofFn_get]; rfl⟩
  refine UpperTheory.Gal.crystallineComparison.genMul_of ℂˣ a α ?_
  intro m hs hp
  have hne := hG α rfl
  unfold DGen at hne
  rw [map_mul] at hne
  have h3 := right_ne_zero_of_mul hne
  rw [map_prod] at h3
  have hle : ∀ i, m i < a + 1 := fun i => Nat.lt_succ_of_le
    (hs ▸ Finset.single_le_sum (f := m) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
  have hone : ((1 : Fin (a + 1)) : ℕ) = 1 := by
    rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)]
  by_cases hm : (fun i => (⟨m i, hle i⟩ : Fin (a + 1))) = fun _ => 1
  · intro i
    have h := congrArg Fin.val (congrFun hm i)
    rw [hone] at h
    exact h
  · exfalso
    have hmem : (fun i => (⟨m i, hle i⟩ : Fin (a + 1))) ∈
        (Finset.univ : Finset (Fin a → Fin (a + 1))).filter
          (fun m => (∑ i, (m i : ℕ)) = a ∧ m ≠ fun _ => 1) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs, hm⟩
    refine Finset.prod_ne_zero_iff.mp h3 _ hmem ?_
    have hp' : ∏ i, (α i : ℂ) ^ m i = ∏ i, (α i : ℂ) := by
      have h := congrArg Units.val hp
      simpa [Units.coe_prod] using h
    simpa [map_sub, map_prod, map_pow, MvPolynomial.aeval_X] using sub_eq_zero.mpr hp'
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PIsoMove
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.BlockSum (blockRep)
open PositivityTheory.AutomorphicGaloisHodgeTate.Div (DivWCoreLac SenWLac HTLac IsSSMat)
open UpperTheory.Gal.Int.Div

theorem UpperTheory.Gal.Int.Div.isoMove_of :
    IsoMove := by
  intro Γ k _ _ a d r r' ρ ⟨u, hu⟩
  set U : Matrix (Fin a) (Fin a) k := (u : Matrix (Fin a) (Fin a) k) with hUdef
  set V : Matrix (Fin a) (Fin a) k := ((u⁻¹ : GL (Fin a) k) : Matrix (Fin a) (Fin a) k) with hVdef
  have hVU : V * U = 1 := by
    simp only [hUdef, hVdef]
    exact Units.inv_mul u
  have hUV : U * V = 1 := by
    simp only [hUdef, hVdef]
    exact Units.mul_inv u
  have hr' : ∀ x, (r' x : Matrix (Fin a) (Fin a) k) = U * (r x : Matrix (Fin a) (Fin a) k) * V := by
    intro x
    rw [hu x]
    rfl
  have hVdet : IsUnit V.det := (Matrix.isUnit_iff_isUnit_det V).1 ⟨u⁻¹, rfl⟩
  constructor
  · rintro ⟨A, hA, h⟩
    refine ⟨A * V, ?_, fun g => ?_⟩
    · rw [Matrix.rank_mul_eq_left_of_isUnit_det V A hVdet, hA]
    · rw [hr' g, ← Matrix.mul_assoc, h g]
      calc A * (r g : Matrix (Fin a) (Fin a) k) * V
          = A * (1 * (r g : Matrix (Fin a) (Fin a) k)) * V := by rw [Matrix.one_mul]
        _ = A * V * (U * (r g : Matrix (Fin a) (Fin a) k) * V) := by
            rw [← hVU]; simp only [Matrix.mul_assoc]
  · rintro ⟨m, B, hB, h⟩
    have hk : ∀ X Y : Matrix (Fin a) (Fin a) k,
        Matrix.kronecker (X * Y) (1 : Matrix (Fin m) (Fin m) k)
          = Matrix.kronecker X (1 : Matrix (Fin m) (Fin m) k) * Matrix.kronecker Y (1 : Matrix (Fin m) (Fin m) k) := by
      intro X Y
      have := Matrix.mul_kronecker_mul X Y (1 : Matrix (Fin m) (Fin m) k) (1 : Matrix (Fin m) (Fin m) k)
      simpa using this
    have h1 : Matrix.kronecker (1 : Matrix (Fin a) (Fin a) k) (1 : Matrix (Fin m) (Fin m) k) = 1 :=
      Matrix.one_kronecker_one
    set P := Matrix.kronecker U (1 : Matrix (Fin m) (Fin m) k) with hP
    set Q := Matrix.kronecker V (1 : Matrix (Fin m) (Fin m) k) with hQ
    have hQP : Q * P = 1 := by rw [hQ, hP, ← hk, hVU, h1]
    have hPQ : P * Q = 1 := by rw [hQ, hP, ← hk, hUV, h1]
    have hPdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 ⟨⟨P, Q, hPQ, hQP⟩, rfl⟩
    refine ⟨m, P * B, ?_, fun g => ?_⟩
    · rw [Matrix.rank_mul_eq_right_of_isUnit_det P B hPdet, hB]
    · have hc : Matrix.kronecker (U * (r g : Matrix (Fin a) (Fin a) k) * V) (1 : Matrix (Fin m) (Fin m) k)
          = P * Matrix.kronecker (r g : Matrix (Fin a) (Fin a) k) (1 : Matrix (Fin m) (Fin m) k) * Q := by
        rw [hk, hk]
      rw [hr' g, hc]
      calc P * Matrix.kronecker (r g : Matrix (Fin a) (Fin a) k) (1 : Matrix (Fin m) (Fin m) k) * Q * (P * B)
          = P * Matrix.kronecker (r g : Matrix (Fin a) (Fin a) k) (1 : Matrix (Fin m) (Fin m) k) * ((Q * P) * B) := by
            simp only [Matrix.mul_assoc]
        _ = P * (Matrix.kronecker (r g : Matrix (Fin a) (Fin a) k) (1 : Matrix (Fin m) (Fin m) k) * B) := by
            rw [hQP, Matrix.one_mul, Matrix.mul_assoc]
        _ = P * B * (ρ g : Matrix (Fin d) (Fin d) k) := by
            rw [h g, Matrix.mul_assoc]
end
