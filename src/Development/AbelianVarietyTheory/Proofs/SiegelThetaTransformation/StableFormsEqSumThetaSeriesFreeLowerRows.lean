module

public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelThetaSpan
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaVacuumUnitaryColumnChangeUnitFactor
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsExpansionOfRowHighest
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SumMovedVacuumTranslatesEqFreeRowTestFunction

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaSeriesLowerRowsZeroEqFreeLowerRows
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsCmFieldGeneratorAtPrimesDividing
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsCmFieldGeneratorAtPrimesDividing
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict

theorem exists_span_eq_mul_coprime {R : Type*} [CommRing R] [IsDedekindDomain R]
    (J K : Ideal R) (hJ : J ≠ ⊥) (hK : K ≠ ⊥) :
    ∃ (a : R) (A : Ideal R), a ≠ 0 ∧ Ideal.span {a} = J * A ∧ IsCoprime A K := by
  classical
  have hJK : J * K ≠ ⊥ := mul_ne_zero hJ hK

  obtain ⟨a₀, ha₀⟩ := IsDedekindDomain.exists_sup_span_eq (Ideal.mul_le_inf.trans inf_le_left : J * K ≤ J) hJK
  obtain ⟨b, hbJK, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJK

  have key : ∃ a : R, a ≠ 0 ∧ J * K ⊔ Ideal.span {a} = J := by
    by_cases h0 : a₀ = 0
    · refine ⟨b, hb0, ?_⟩
      have hJKJ : J * K = J := by simpa [h0] using ha₀
      rw [sup_eq_left.mpr (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hbJK)), hJKJ]
    · exact ⟨a₀, h0, ha₀⟩
  obtain ⟨a, ha0, ha⟩ := key
  have haJ : Ideal.span {a} ≤ J := ha ▸ le_sup_right
  obtain ⟨A, hA⟩ := Ideal.dvd_iff_le.mpr haJ
  refine ⟨a, A, ha0, hA, ?_⟩
  rw [Ideal.isCoprime_iff_sup_eq]

  have h1 : J * (K ⊔ A) = J * ⊤ := by
    rw [Ideal.mul_sup, ← hA, ha, Ideal.mul_top]
  rw [sup_comm]
  exact mul_left_cancel₀ hJ h1

theorem exists_generator_at_primes_dividing :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (𝔍 : Ideal (𝓞 E)) (M : ℕ), 𝔍 ≠ ⊥ → 0 < M → ∃ (α : 𝓞 E) (𝔞 : Ideal (𝓞 E)), α ≠ 0 ∧ Ideal.span {α} = 𝔍 * 𝔞 ∧ IsCoprime 𝔞 (Ideal.span {(M : 𝓞 E)}) := by
  intro E _ _ _ 𝔍 M h𝔍 hM
  have hK : Ideal.span {(M : 𝓞 E)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hM.ne'
  exact exists_span_eq_mul_coprime 𝔍 _ h𝔍 hK

end GlobalTheory.Dict
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsCmFieldGeneratorAtPrimesDividingStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cmField_generator_at_primes_dividing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (𝔍 : Ideal (𝓞 E)) (M : ℕ), 𝔍 ≠ ⊥ → 0 < M → ∃ (α : 𝓞 E) (𝔞 : Ideal (𝓞 E)), α ≠ 0 ∧ Ideal.span {α} = 𝔍 * 𝔞 ∧ IsCoprime 𝔞 (Ideal.span {(M : 𝓞 E)}) := by
  first | exact @GlobalTheory.Dict.exists_generator_at_primes_dividing | exact GlobalTheory.Dict.exists_generator_at_primes_dividing | (intros; apply GlobalTheory.Dict.exists_generator_at_primes_dividing <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualLatticeDiagonalUnitaryPatchedStandard
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualLatticeDiagonalUnitaryPatchedStandard
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.Patch

open GlobalTheory.SW.Base

variable {E : Type} [Field E] [NumberField E]

theorem exists_nat_coprime (𝔞 : Ideal (𝓞 E)) (M : ℕ) (h0 : 𝔞 ≠ ⊥)
    (h : IsCoprime 𝔞 (Ideal.span {(M : 𝓞 E)})) : ∃ a : ℕ, 0 < a ∧ a.Coprime M ∧ (a : 𝓞 E) ∈ 𝔞 := by
  have ex : ∃ a : ℕ, 0 < a ∧ (a : 𝓞 E) ∈ 𝔞 :=
    ⟨Ideal.absNorm 𝔞, Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff]), Ideal.absNorm_mem 𝔞⟩
  obtain ⟨ha0, ha⟩ := Nat.find_spec ex
  refine ⟨Nat.find ex, ha0, ?_, ha⟩
  obtain ⟨x, hx, y, hy, hxy⟩ := Ideal.isCoprime_iff_exists.1 h
  obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  obtain ⟨a', ha'⟩ := Nat.gcd_dvd_left (Nat.find ex) M
  obtain ⟨m', hm'⟩ := Nat.gcd_dvd_right (Nat.find ex) M
  set g := Nat.gcd (Nat.find ex) M with hg
  have hpos : 0 < a' := Nat.pos_of_ne_zero (by rintro rfl; omega)
  have hmem : (a' : 𝓞 E) ∈ 𝔞 := by
    have e : (a' : 𝓞 E) = a' * x + (z * m') * (Nat.find ex : ℕ) := by
      have e1 : (M : 𝓞 E) = g * m' := by exact_mod_cast congrArg (Nat.cast : ℕ → 𝓞 E) hm'
      have e2 : ((Nat.find ex : ℕ) : 𝓞 E) = g * a' := by exact_mod_cast congrArg (Nat.cast : ℕ → 𝓞 E) ha'
      rw [e2]
      rw [e1] at hxy
      linear_combination (-(a' : 𝓞 E)) * hxy
    rw [e]
    exact 𝔞.add_mem (𝔞.mul_mem_left _ hx) (𝔞.mul_mem_left _ ha)
  have hle : Nat.find ex ≤ a' := Nat.find_min' ex ⟨hpos, hmem⟩
  have hg0 : 0 < g := Nat.pos_of_ne_zero (by intro h; rw [h] at ha'; omega)
  have : g ≤ 1 := by
    by_contra hc
    have : 2 * a' ≤ g * a' := Nat.mul_le_mul_right _ (by omega)
    omega
  show g = 1
  omega

omit [NumberField E] in
theorem int_congr {x y : E} (h : IsIntegral ℤ x) (e : y = x) : IsIntegral ℤ y := e ▸ h

omit [NumberField E] in
theorem mem_left {J J' : Ideal (𝓞 E)} {j : 𝓞 E} (h : j ∈ J * J') : j ∈ J := (Ideal.mul_le_inf h).1

omit [NumberField E] in
theorem mem_right {J J' : Ideal (𝓞 E)} {j : 𝓞 E} (h : j ∈ J * J') : j ∈ J' := (Ideal.mul_le_inf h).2

variable [IsCMField E] {n : ℕ}

theorem herm_smul_left (c : E) (x y : Fin n → E) : herm 1 (c • x) y = c * herm 1 x y := by
  simp [Base.herm_one, Finset.mul_sum, _root_.mul_assoc]

theorem herm_nat_right (c : ℕ) (x y : Fin n → E) : herm 1 x ((c : E) • y) = c * herm 1 x y := by
  simp [Base.herm_one, Finset.mul_sum, cc, mul_left_comm]

omit [IsCMField E] in
theorem int_of_coprime {a b : ℕ} (h : a.Coprime b) {x : E} (h1 : IsIntegral ℤ ((a : E) * x))
    (h2 : IsIntegral ℤ ((b : E) * x)) : IsIntegral ℤ x := by
  obtain ⟨u, v, huv⟩ : IsCoprime (a : ℤ) (b : ℤ) := Nat.isCoprime_iff_coprime.2 h
  have hbezout : (u : E) * a + (v : E) * b = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → E) huv
  have hx : (u : E) * ((a : E) * x) + (v : E) * ((b : E) * x) = x := by
    rw [← _root_.mul_assoc, ← _root_.mul_assoc, ← add_mul, hbezout, _root_.one_mul]
  rw [← hx]
  exact ((isIntegral_intCast u).mul h1).add ((isIntegral_intCast v).mul h2)

theorem patch {M t : ℕ} (ht : 0 < t) (htM : t.Coprime M) (J J' : Ideal (𝓞 E)) (hJ : (M : 𝓞 E) ∈ J)
    (hJ' : (M : 𝓞 E) ∈ J') (A : Lt E n) (hA : A.FG) (hsd : ∀ x, x ∈ A ↔ ∀ y ∈ A, IsIntegral ℤ (herm 1 x y))
    (h1 : ∀ j ∈ J, ∀ v ∈ A, (j : E) • (t : E) • v ∈ stdL E n)
    (h2 : ∀ j ∈ J', ∀ v ∈ stdL E n, (j : E) • (t : E) • v ∈ A) :
    ∃ C ∈ Vset E n M, (J * J') • A ≤ C ∧ (J * J') • C ≤ A := by
  obtain ⟨hS, hSsd, -⟩ := Base.stdL_mem_Vset (E := E) n M
  have k1 : ∀ v ∈ A, (M : E) • (t : E) • v ∈ stdL E n := fun v hv => by simpa using h1 _ hJ v hv
  have k2 : ∀ v ∈ stdL E n, (M : E) • (t : E) • v ∈ A := fun v hv => by simpa using h2 _ hJ' v hv
  let C : Lt E n :=
    { carrier := {v | (M : E) • v ∈ A ∧ (t : E) • v ∈ stdL E n}
      add_mem' := fun ha hb => ⟨by rw [smul_add]; exact A.add_mem ha.1 hb.1,
        by rw [smul_add]; exact (stdL E n).add_mem ha.2 hb.2⟩
      zero_mem' := ⟨by simp, by simp⟩
      smul_mem' := fun c v hv => ⟨by rw [smul_comm]; exact A.smul_mem c hv.1,
        by rw [smul_comm]; exact (stdL E n).smul_mem c hv.2⟩ }
  have mC : ∀ v, v ∈ C ↔ (M : E) • v ∈ A ∧ (t : E) • v ∈ stdL E n := fun v => Iff.rfl
  have cA : ∀ v ∈ A, (M : E) • v ∈ C := fun v hv =>
    (mC _).2 ⟨nat_smul_mem _ _ (nat_smul_mem _ _ hv), by rw [smul_comm]; exact k1 v hv⟩
  have cS : ∀ v ∈ stdL E n, (t : E) • v ∈ C := fun v hv =>
    (mC _).2 ⟨k2 v hv, nat_smul_mem _ _ (nat_smul_mem _ _ hv)⟩
  refine ⟨C, ⟨?_, fun x => ⟨fun hx y hy => ?_, fun hx => ?_⟩, t, ht, htM, fun v hv => hv.2, cS⟩, ?_, ?_⟩
  · have hle : C ≤ A ⊔ stdL E n := fun v hv =>
      mem_of_coprime _ htM (Submodule.mem_sup_right hv.2) (Submodule.mem_sup_left hv.1)
    haveI := isNoetherian_of_fg_of_noetherian _ (hA.sup hS)
    haveI := isNoetherian_of_le hle
    exact Module.Finite.iff_fg.1 inferInstance
  · have a1 := (hsd _).1 hx.1 _ hy.1
    have a2 := (hSsd _).1 hx.2 _ hy.2
    rw [herm_smul_left, herm_nat_right, ← _root_.mul_assoc, ← Nat.cast_mul] at a1 a2
    exact int_of_coprime (Nat.Coprime.mul_left (htM.mul_right htM) (htM.mul_right htM)) a2 a1
  · refine (mC _).2 ⟨(hsd _).2 fun y hy => ?_, (hSsd _).2 fun y hy => ?_⟩
    · rw [herm_smul_left, ← herm_nat_right]; exact hx _ (cA y hy)
    · rw [herm_smul_left, ← herm_nat_right]; exact hx _ (cS y hy)
  · refine Submodule.smul_le.2 fun j hj v hv => (mC _).2 ⟨nat_smul_mem _ _ (A.smul_mem j hv), ?_⟩
    rw [smul_comm (t : E) j v]; exact h1 j (mem_left hj) v hv
  · refine Submodule.smul_le.2 fun j hj v hv => ?_
    refine mem_of_coprime A (s := t * t) (R := M) (Nat.Coprime.mul_left htM htM) ?_ ?_
    · have := h2 j (mem_right hj) _ ((mC v).1 hv).2
      rw [smul_comm _ j v, Nat.cast_mul, mul_smul]; exact this
    · rw [smul_comm _ j v]; exact A.smul_mem j ((mC v).1 hv).1

theorem cc_mul (x y : E) : cc (x * y) = cc x * cc y := by simp [cc]

theorem moved (d : Fin n → E) (hd : ∀ k, cc (d k) * d k = 1) (Λ : Lt E n) (hfg : Λ.FG)
    (hsd : ∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) :
    ∃ A : Lt E n, A.FG ∧ (∀ x, x ∈ A ↔ ∀ y ∈ A, IsIntegral ℤ (herm 1 x y)) ∧
      ∀ v, v ∈ A ↔ (fun k => cc (d k) * v k) ∈ Λ := by
  let g : (Fin n → E) →ₗ[𝓞 E] (Fin n → E) := (Matrix.mulVecLin (Matrix.diagonal d)).restrictScalars (𝓞 E)
  have hg : ∀ v, g v = fun k => d k * v k := fun v => by
    ext k; simp [g, Matrix.mulVec_diagonal]
  have mA : ∀ v, v ∈ Λ.map g ↔ (fun k => cc (d k) * v k) ∈ Λ := fun v => by
    constructor
    · rintro ⟨w, hw, rfl⟩
      have : (fun k => cc (d k) * g w k) = w := by
        ext k; rw [hg]; simp only; rw [← _root_.mul_assoc, hd, _root_.one_mul]
      rw [this]; exact hw
    · intro hv
      refine ⟨_, hv, ?_⟩
      ext k; rw [hg]; simp only; rw [← _root_.mul_assoc, mul_comm (d k), hd, _root_.one_mul]
  have hh : ∀ x y : Fin n → E, herm 1 (fun k => cc (d k) * x k) y = herm 1 x (g y) := fun x y => by
    rw [hg, Base.herm_one, Base.herm_one]
    exact Finset.sum_congr rfl fun k _ => by rw [cc_mul]; ring
  refine ⟨Λ.map g, hfg.map g, fun x => ?_, mA⟩
  rw [mA, hsd]
  simp only [hh]
  exact ⟨by rintro h _ ⟨y, hy, rfl⟩; exact h y hy, fun h y hy => h _ ⟨y, hy, rfl⟩⟩

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n r M : ℕ) (𝔍 𝔞 : Ideal (𝓞 E)) (α : 𝓞 E), 0 < M → (M : 𝓞 E) ∈ 𝔍 → IsCoprime 𝔍 (conjI 𝔍) → α ≠ 0 → Ideal.span {α} = 𝔍 * 𝔞 → IsCoprime 𝔞 (Ideal.span {(M : 𝓞 E)}) → ∀ h : Matrix (Fin n) (Fin n) E, h = Matrix.diagonal (fun k : Fin n => if (k : ℕ) < r then 1 else cc (α : E) / (α : E)) → ccT h * h = 1 ∧ ∀ Λ ∈ Vset E n M, ∃ Λ' ∈ Vset E n M, ∃ Λ'' ∈ Vset E n 1, Moves h Λ Λ'' ∧ (𝔍 * conjI 𝔍) • Λ'' ≤ Λ' ∧ (𝔍 * conjI 𝔍) • Λ' ≤ Λ'' := by
  intro E _ _ _ n r M 𝔍 𝔞 α hM hMJ _ hα hsp hco h hh
  have hα' : (α : E) ≠ 0 := by exact_mod_cast hα
  have hcα : cc (α : E) ≠ 0 := by simpa [cc] using hα'
  set d : Fin n → E := fun k : Fin n => if (k : ℕ) < r then 1 else cc (α : E) / (α : E) with hdd
  have hcd : ∀ k, cc (d k) = if (k : ℕ) < r then 1 else (α : E) / cc (α : E) := fun k => by
    simp only [hdd]; split_ifs <;> simp [cc]
  have hd : ∀ k, cc (d k) * d k = 1 := fun k => by
    rw [hcd]; simp only [hdd]; split_ifs
    · simp
    · field_simp
  refine ⟨?_, ?_⟩
  · ext i j
    subst hh
    rw [Matrix.mul_diagonal]
    by_cases hij : i = j
    · subst hij; simp [ccT, hd]
    · simp [ccT, Matrix.one_apply, hij, Matrix.diagonal_apply, Ne.symm hij, cc]
  rintro Λ ⟨hfg, hsd, s, hs, hsM, hΛS, hSΛ⟩
  obtain ⟨A, hA, hAsd, mA⟩ := moved d hd Λ hfg hsd
  have h𝔞 : 𝔞 ≠ ⊥ := by
    rintro rfl
    rw [Ideal.mul_bot, Ideal.span_singleton_eq_bot] at hsp
    exact hα hsp
  obtain ⟨a, ha0, haM, ha⟩ := exists_nat_coprime 𝔞 M h𝔞 hco
  have cnat : ∀ k : ℕ, IsIntegral ℤ (k : E) := fun k => by
    simpa using isIntegral_algebraMap (R := ℤ) (A := E) (x := (k : ℤ))
  have q1 : ∀ j ∈ 𝔍, IsIntegral ℤ ((j : E) * a / α) := fun j hj => by
    have : j * a ∈ Ideal.span {α} := hsp ▸ Ideal.mul_mem_mul hj ha
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 this
    have e : (j : E) * a / α = z := by
      rw [div_eq_iff hα']; exact_mod_cast congrArg (fun u : 𝓞 E => (u : E)) hz.symm
    rw [e]; exact z.isIntegral_coe
  have q2 : ∀ j ∈ conjI 𝔍, IsIntegral ℤ ((j : E) * a / cc (α : E)) := fun j hj => by
    induction hj using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, hb, e⟩ := hx
      have := isIntegral_cc (q1 b hb)
      rw [e]; simpa [cc] using this
    | zero => simpa using isIntegral_zero
    | add x y _ _ hx hy =>
      refine int_congr (hx.add hy) ?_
      push_cast; ring
    | smul c x _ hx =>
      refine int_congr (c.isIntegral_coe.mul hx) ?_
      rw [smul_eq_mul]; push_cast; ring
  have p1 : ∀ j ∈ 𝔍, ∀ k, IsIntegral ℤ ((j : E) * a * d k) := fun j hj k => by
    simp only [hdd]; split_ifs
    · rw [_root_.mul_one]; exact j.isIntegral_coe.mul (cnat a)
    · refine int_congr ((q1 j hj).mul (isIntegral_cc α.isIntegral_coe)) ?_
      ring
  have p2 : ∀ j ∈ conjI 𝔍, ∀ k, IsIntegral ℤ ((j : E) * a * cc (d k)) := fun j hj k => by
    rw [hcd]; split_ifs
    · rw [_root_.mul_one]; exact j.isIntegral_coe.mul (cnat a)
    · refine int_congr ((q2 j hj).mul α.isIntegral_coe) ?_
      ring
  have hMJ' : (M : 𝓞 E) ∈ conjI 𝔍 := Ideal.subset_span ⟨M, hMJ, by simp [cc]⟩
  have h1 : ∀ j ∈ 𝔍, ∀ v ∈ A, (j : E) • ((s * a : ℕ) : E) • v ∈ stdL E n := fun j hj v hv => by
    have := (mem_stdL _).1 (hΛS _ ((mA v).1 hv))
    refine (mem_stdL _).2 fun k => ?_
    refine int_congr ((p1 j hj k).mul (this k)) ?_
    simp only [Pi.smul_apply, smul_eq_mul]; push_cast
    linear_combination (-((j : E) * a * s * v k)) * hd k
  have h2 : ∀ j ∈ conjI 𝔍, ∀ v ∈ stdL E n, (j : E) • ((s * a : ℕ) : E) • v ∈ A := fun j hj v hv => by
    have := hSΛ (fun k => (j : E) * a * cc (d k) * v k)
      ((mem_stdL _).2 fun k => (p2 j hj k).mul ((mem_stdL _).1 hv k))
    rw [mA]
    convert this using 1
    ext k
    simp only [Pi.smul_apply, smul_eq_mul]; push_cast; ring
  have ht : 0 < s * a := Nat.mul_pos hs ha0
  obtain ⟨C, hC, c1, c2⟩ := patch ht (Nat.Coprime.mul_left hsM haM) 𝔍 (conjI 𝔍) hMJ hMJ' A hA hAsd h1 h2
  refine ⟨C, hC, A, ⟨hA, hAsd, M * (s * a), Nat.mul_pos hM ht, Nat.coprime_one_right _, fun v hv => ?_,
    fun v hv => ?_⟩, fun v => ?_, c1, c2⟩
  · rw [Nat.cast_mul, mul_smul]; simpa using h1 _ hMJ v hv
  · rw [Nat.cast_mul, mul_smul]; simpa using h2 _ hMJ' v hv
  · rw [mA, hh]
    have : (fun k => cc (d k) * (Matrix.diagonal d *ᵥ v) k) = v := by
      ext k; rw [Matrix.mulVec_diagonal, ← _root_.mul_assoc, hd, _root_.one_mul]
    rw [this]

end GlobalTheory.Dict.Patch
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualLatticeDiagonalUnitaryPatchedStandardStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDual_lattice_diagonal_unitary_patched_standard : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n r M : ℕ) (𝔍 𝔞 : Ideal (𝓞 E)) (α : 𝓞 E), 0 < M → (M : 𝓞 E) ∈ 𝔍 → IsCoprime 𝔍 (conjI 𝔍) → α ≠ 0 → Ideal.span {α} = 𝔍 * 𝔞 → IsCoprime 𝔞 (Ideal.span {(M : 𝓞 E)}) → ∀ h : Matrix (Fin n) (Fin n) E, h = Matrix.diagonal (fun k : Fin n => if (k : ℕ) < r then 1 else cc (α : E) / (α : E)) → ccT h * h = 1 ∧ ∀ Λ ∈ Vset E n M, ∃ Λ' ∈ Vset E n M, ∃ Λ'' ∈ Vset E n 1, Moves h Λ Λ'' ∧ (𝔍 * conjI 𝔍) • Λ'' ≤ Λ' ∧ (𝔍 * conjI 𝔍) • Λ' ≤ Λ'' := by
  first | exact @GlobalTheory.Dict.Patch.main | exact GlobalTheory.Dict.Patch.main | (intros; apply GlobalTheory.Dict.Patch.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaSeriesLowerRowsZeroEqFreeLowerRows
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.DiagFree

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ}

theorem vset_one {M : ℕ} {Λ : Lt E n} (h : Λ ∈ Vset E n M) : Λ ∈ Vset E n 1 := by
  obtain ⟨hfg, hdual, s, hs, -, h1, h2⟩ := h
  exact ⟨hfg, hdual, s, hs, Nat.coprime_one_right s, h1, h2⟩

theorem conjI_mono {P Q : Ideal (𝓞 E)} (h : P ≤ Q) : conjI P ≤ conjI Q := by
  unfold conjI
  exact Ideal.span_mono fun _ ⟨b, hb, e⟩ => ⟨b, h hb, e⟩

theorem isSB_smul (c : ℂ) {φ : TF n g} (h : IsSB φ) : IsSB (c • φ) := by
  obtain ⟨R, hR, h1, h2⟩ := h
  refine ⟨R, hR, fun x hx => h1 x fun h0 => hx ?_, fun x y hy => ?_⟩
  · simp [h0]
  · simp [h2 x y hy]

theorem thA_sum (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) {T : Type} (s : Finset T) (f : T → TF n g) (hf : ∀ i, IsSB (f i)) :
    thA X bas idx (∑ i ∈ s, f i) x = ∑ i ∈ s, thA X bas idx (f i) x := by
  classical
  refine Finset.induction_on s ?_ ?_
  · have h0 := GlobalTheory.SW.UnAct.thA_smul (bas := bas) idx x (0 : ℂ) (0 : TF n g)
    simpa using h0
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      GlobalTheory.SW.UnAct.thA_add idx hs hx (hf a) (GlobalTheory.SW.RecSum.isSB_sum s f hf), ih]

theorem isSB_unitv_projA (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) (hn : Even n) {w : E}
    (hw : IsIntegral ℤ w) (hw' : w + cc w = 1) {L : Lt E r} (hL : SelfD X L) {Λ : Lt E n}
    (hΛ : Λ ∈ Vset E n 1) {φ : TF n g} (hφ : IsSB φ) :
    IsSB (unitv (projA X bas w (tens Λ L) φ)) := by
  unfold unitv projA
  refine isSB_smul _ (isSB_smul _ ?_)
  refine finsum_mem_induction (fun ψ => IsSB ψ) isSB_zero
    (fun a b ha hb => (isSB_algebra_haar_linear ℚ (Fin n) (Fin g) a b ha hb).1) ?_
  rintro _ ⟨y, -, rfl⟩
  exact isSB_smul _ ((heisG_laws E r X g bas idx n hs hn).2.2.2 y φ hφ).1

private theorem thA_finset_sum_smul (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) {T : Type} (s : Finset T) (a : T → ℂ) (ψ : T → TF n g)
    (hψ : ∀ i, IsSB (ψ i)) (z : Fin n → Fin g → ℂ) :
    thA X bas idx (∑ i ∈ s, a i • ψ i) x z = ∑ i ∈ s, a i * thA X bas idx (ψ i) x z := by
  rw [thA_sum idx hs hx s _ (fun i => isSB_smul (a i) (hψ i)), Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [GlobalTheory.SW.UnAct.thA_smul (bas := bas) idx x (a i) (ψ i)]
  rfl

theorem thP_phi_eq_thP_phiF : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ (D : SW.Level X) (hn : r ≤ n) (M : ℕ) (𝔐 𝔍 : Ideal (𝓞 E)), 0 < M → (M : 𝓞 E) ∈ D.𝔪 → D.𝔪 = 𝔐 * 𝔍 → IsCoprime 𝔐 𝔍 → ∀ v₀ : Lt E r → TF n g, (∀ L ∈ D.lats, IsVac X bas D.w (tens (stdL E n) (D.sh L)) (v₀ L)) → ∀ (k : X.Ψ → Fin q0 → ℕ) (k' : X.Ψ → Fin X.p0 → ℕ), ∀ Λ ∈ Vset E n M, ∀ P ∈ Harm.rowHighest ℂ k k', ∃ Λ' ∈ Vset E n M, ∃ P' ∈ Harm.rowHighest ℂ k k', ∀ L ∈ D.lats, ∀ x ∈ X.dom, thP X hr bas idx (D.phi bas hn v₀ L Λ) P x = thP X hr bas idx (phiF bas D 𝔐 hn v₀ L Λ') P' x := by
  intro E _ _ _ r X g q0 hr bas idx n hs hn D hrn M 𝔐 𝔍 hM hMm hsplit hcop v₀ hv₀ k k' Λ hΛ P hP
  have hle : D.𝔪 ≤ 𝔍 := by
    rw [hsplit]
    exact Ideal.mul_le_inf.trans inf_le_right
  have h𝔍 : 𝔍 ≠ ⊥ := by
    intro h0
    apply D.ne_bot
    rw [hsplit, h0, Ideal.mul_bot]
  have hMJ : ((M : ℕ) : 𝓞 E) ∈ 𝔍 := hle hMm
  have hcopJ : IsCoprime 𝔍 (conjI 𝔍) := by
    have h1 := D.cop
    rw [Ideal.isCoprime_iff_sup_eq] at h1 ⊢
    exact top_unique (h1.symm.le.trans (sup_le_sup hle (conjI_mono hle)))
  obtain ⟨α, 𝔞, hα, hspan, hcopa⟩ := GlobalTheory.T.exists_cmField_generator_at_primes_dividing E 𝔍 M h𝔍 hM
  set H : Matrix (Fin n) (Fin n) E :=
    Matrix.diagonal (fun k : Fin n => if (k : ℕ) < r then 1 else cc (α : E) / (α : E)) with hHdef
  obtain ⟨hunit, hmove⟩ := GlobalTheory.T.selfDual_lattice_diagonal_unitary_patched_standard E n r M 𝔍 𝔞 α hM hMJ hcopJ hα hspan hcopa H hHdef
  obtain ⟨Λ', hΛ', Λ'', hΛ'', hmv, hle1, hle2⟩ := hmove Λ hΛ
  obtain ⟨t, ht0, ht⟩ := GlobalTheory.T.sum_moved_vacuum_translates_eq_freeRow_testFunction E r X g bas idx n hs hn D hrn M 𝔐 𝔍 𝔞 α hM hMm hsplit hcop hα
    hspan hcopa v₀ hv₀ H hHdef Λ hΛ Λ' hΛ' Λ'' hΛ'' hmv hle1 hle2
  obtain ⟨t', ht'1, ht'⟩ := GlobalTheory.T.thetaVacuum_unitary_column_change_unit_factor E r X g bas idx n hs hn D.w D.w_int D.w_tr H hunit Λ
    (vset_one hΛ) Λ'' hΛ'' hmv
  obtain ⟨P', hP', hPd⟩ := GlobalTheory.T.exists_rowHighest_harmonic_polyDeriv_unitaryAction E r X g q0 hr bas idx n hs hn H hunit k k' P hP
  have ht'0 : t' ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at ht'1
    exact zero_ne_one ht'1
  refine ⟨Λ', hΛ', (t / t') • P', Submodule.smul_mem _ _ hP', fun L hL x hx => ?_⟩
  have hSh : SelfD X (D.sh L) := ((GlobalTheory.T.level_structure_properties E r X g bas idx n hs hn D hrn).2.2.2.1 L hL).1
  have hv := hv₀ L hL
  have hφ := isSB_unitv_projA idx hs hn D.w_int D.w_tr hSh (vset_one hΛ) hv.1
  have hφ'' := isSB_unitv_projA idx hs hn D.w_int D.w_tr hSh hΛ'' hv.1
  have hheis : ∀ (y : Matrix (Fin n) (Fin r) E) (ψ : TF n g), IsSB ψ → IsSB (heisG X bas y ψ) :=
    fun y ψ hψ => ((heisG_laws E r X g bas idx n hs hn).2.2.2 y ψ hψ).1
  obtain ⟨s, hs1, hs2⟩ := ht L hL
  have hphiF : IsSB (phiF bas D 𝔐 hrn v₀ L Λ') := by
    have h2 : phiF bas D 𝔐 hrn v₀ L Λ' = t⁻¹ • (t • phiF bas D 𝔐 hrn v₀ L Λ') := by
      rw [smul_smul, inv_mul_cancel₀ ht0, one_smul]
    rw [h2, ← hs2]
    exact isSB_smul _ (GlobalTheory.SW.RecSum.isSB_sum s _ fun y => isSB_smul _ (hheis _ _ hφ''))
  have hDphi : IsSB (D.phi bas hrn v₀ L Λ) := by
    rw [hs1]
    exact GlobalTheory.SW.RecSum.isSB_sum s _ fun y => isSB_smul _ (hheis _ _ hφ)
  have key : ∀ z, t * thA X bas idx (phiF bas D 𝔐 hrn v₀ L Λ') x (GlobalTheory.Dict.hAct X idx H z) =
      t' * thA X bas idx (D.phi bas hrn v₀ L Λ) x z := by
    intro z
    have e1 := congrFun (GlobalTheory.SW.UnAct.thA_smul (bas := bas) idx x t (phiF bas D 𝔐 hrn v₀ L Λ'))
      (GlobalTheory.Dict.hAct X idx H z)
    rw [Pi.smul_apply, smul_eq_mul] at e1
    rw [← e1, ← hs2, thA_finset_sum_smul idx hs hx s _ _ (fun y => hheis _ _ hφ''), hs1,
      thA_finset_sum_smul idx hs hx s _ _ (fun y => hheis _ _ hφ), Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [GlobalTheory.T.theta_heisenberg_unitary_column_change E r X g bas idx n hs hn H hunit _ _ hφ hφ'' t' x hx
      (fun z => ht' (D.sh L) hSh (v₀ L) hv x hx z) y z]
    ring
  have hana := (theta_holomorphic_weight E r X g q0 hr bas idx n hs hn k k' _ hphiF P' hP').2.2.2 x hx
  have hdiff := ReciprocityTheory.ChartRestriction.G.I2.contDiff_of_diff (GlobalTheory.SW.ThetaHol.differentiable_thA idx hs hDphi hx)
  have hfun : (fun z => thA X bas idx (phiF bas D 𝔐 hrn v₀ L Λ') x (GlobalTheory.Dict.hAct X idx H z)) =
      (t' / t) • thA X bas idx (D.phi bas hrn v₀ L Λ) x := by
    funext z
    rw [Pi.smul_apply, smul_eq_mul]
    field_simp
    linear_combination key z
  unfold GlobalTheory.SW.thP
  rw [ReciprocityTheory.ChartRestriction.G.I2.polyDeriv_smul, ← hPd _ hana, hfun,
    ReciprocityTheory.ChartRestriction.G.I2.polyDeriv_smul_fun _ _ hdiff]
  field_simp

end GlobalTheory.Dict.DiagFree
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaSeriesLowerRowsZeroEqFreeLowerRowsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSeries_lowerRowsZero_eq_freeLowerRows : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ (D : SW.Level X) (hn : r ≤ n) (M : ℕ) (𝔐 𝔍 : Ideal (𝓞 E)), 0 < M → (M : 𝓞 E) ∈ D.𝔪 → D.𝔪 = 𝔐 * 𝔍 → IsCoprime 𝔐 𝔍 → ∀ v₀ : Lt E r → TF n g, (∀ L ∈ D.lats, IsVac X bas D.w (tens (stdL E n) (D.sh L)) (v₀ L)) → ∀ (k : X.Ψ → Fin q0 → ℕ) (k' : X.Ψ → Fin X.p0 → ℕ), ∀ Λ ∈ Vset E n M, ∀ P ∈ Harm.rowHighest ℂ k k', ∃ Λ' ∈ Vset E n M, ∃ P' ∈ Harm.rowHighest ℂ k k', ∀ L ∈ D.lats, ∀ x ∈ X.dom, thP X hr bas idx (D.phi bas hn v₀ L Λ) P x = thP X hr bas idx (phiF bas D 𝔐 hn v₀ L Λ') P' x := by
  first | exact @GlobalTheory.Dict.DiagFree.thP_phi_eq_thP_phiF | exact GlobalTheory.Dict.DiagFree.thP_phi_eq_thP_phiF | (intros; apply GlobalTheory.Dict.DiagFree.thP_phi_eq_thP_phiF <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.VacuumMultiplierUnitaryCocycle
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.VacuumMultiplierUnitaryCocycle
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict

private lemma mapL_one' {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (L : Lt E r) : mapL (1 : GL (Fin r) E) L = L := by
  unfold mapL
  simp

private lemma mapL_mul' {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (a b : GL (Fin r) E) (L : Lt E r) :
    mapL (a * b) L = mapL a (mapL b L) := by
  unfold mapL
  rw [← Submodule.map_comp]
  congr 1
  refine LinearMap.ext fun v => ?_
  simp [Matrix.mulVec_mulVec]

private lemma smul_left_cancel_of_ip_self_eq_one {n g : ℕ} {v : TF n g} (hv : IsSB v) (h1 : ip v v = 1) {a b : ℂ}
    (h : a • v = b • v) : a = b := by
  have ha := TensVac.ip_smul_left a hv hv
  have hb := TensVac.ip_smul_left b hv hv
  rw [h1, _root_.mul_one] at ha hb
  rw [← ha, ← hb, h]

theorem vac_multiplier_cocycle : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ D : SW.Level X, ∀ v₀ : Lt E r → TF n g, (∀ L ∈ D.lats, IsVac X bas D.w (tens (stdL E n) (D.sh L)) (v₀ L)) → ∀ mu : GL (Fin r) E → Lt E r → ℂ, (∀ ga ∈ D.grp, ∀ L ∈ D.lats, ∀ k : D.J, D.Red (fun i => (ga : Matrix (Fin r) (Fin r) E) *ᵥ D.β i) k → wG X bas idx ga (v₀ L) = (mu ga L * (D.lam k : ℂˣ)) • v₀ (mapL ga L)) → (∀ ga ∈ D.grp, ∀ L ∈ D.lats, ‖mu ga L‖ = 1) ∧ (∀ L ∈ D.lats, mu 1 L = 1) ∧ ∀ ga ∈ D.grp, ∀ ga' ∈ D.grp, ∀ L ∈ D.lats, mu (ga * ga') L = mu ga (mapL ga' L) * mu ga' L := by
  intro E _ _ _ r X g bas idx n hs hn D v₀ hvac mu hmu
  have hsd : SelfD X X.Λ := Lev.selfD_of_sympl hs
  have hlat : ∀ L ∈ D.lats, ∀ ga ∈ D.grp, mapL ga L ∈ D.lats := fun L hL ga hga =>
    Lev.mapL_mem_lats hsd hga hL
  have hred : ∀ ga ∈ D.grp, ∃ k : D.J,
      D.Red (fun i => (ga : Matrix (Fin r) (Fin r) E) *ᵥ D.β i) k := by
    intro ga hga
    obtain ⟨-, k, hk, h⟩ := (Lev.mem_grp ga).mp hga
    exact ⟨⟨k, hk⟩, h⟩
  have hun : ∀ ga ∈ D.grp, IsUn X ga := fun ga hga => ((Lev.mem_grp ga).mp hga).1
  have hvsb : ∀ L ∈ D.lats, IsSB (v₀ L) := by
    intro L hL
    obtain ⟨h, -, -⟩ := hvac L hL
    exact h
  have hvone : ∀ L ∈ D.lats, ip (v₀ L) (v₀ L) = 1 := by
    intro L hL
    obtain ⟨-, h, -⟩ := hvac L hL
    exact h

  have hnorm : ∀ ga ∈ D.grp, ∀ L ∈ D.lats, ‖mu ga L‖ = 1 := by
    intro ga hga L hL
    obtain ⟨k, hk⟩ := hred ga hga
    have hL' := hlat L hL ga hga
    have hip := ((wG_laws E r X g bas idx n hs hn ga (hun ga hga) (v₀ L) (hvsb L hL)).2.2.1
      (v₀ L) (hvsb L hL)).1
    rw [hmu ga hga L hL k hk, hvone L hL,
      TensVac.ip_smul_left _ (hvsb _ hL') (TensVac.sb_smul _ (hvsb _ hL')),
      TensVac.ip_smul_right _ (hvsb _ hL') (hvsb _ hL'), hvone _ hL', _root_.mul_one,
      Complex.mul_conj, Complex.normSq_eq_norm_sq] at hip
    have h2 : ‖mu ga L * ((D.lam k : ℂˣ) : ℂ)‖ ^ 2 = 1 := by exact_mod_cast hip
    rw [norm_mul, Lev.norm_lam k, _root_.mul_one] at h2
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h2

  have hlam : ∀ ga ∈ D.grp, ∀ ga' ∈ D.grp, ∀ k k' k'' : D.J,
      D.Red (fun i => (ga : Matrix (Fin r) (Fin r) E) *ᵥ D.β i) k →
      D.Red (fun i => (ga' : Matrix (Fin r) (Fin r) E) *ᵥ D.β i) k' →
      D.Red (fun i => ((ga * ga' : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ D.β i) k'' →
      ((D.lam k'' : ℂˣ) : ℂ) = (D.lam k : ℂˣ) * (D.lam k' : ℂˣ) := by
    intro ga _ ga' _ k k' k'' hk hk' hk''
    let y0 : Matrix (Fin r) (Fin r) E := Matrix.of fun i => D.β i
    have hy : ∀ M : Matrix (Fin r) (Fin r) E, y0 * Mᵀ = Matrix.of fun i => M *ᵥ D.β i := by
      intro M
      ext i j
      simp [y0, Matrix.mul_apply, Matrix.mulVec, dotProduct, _root_.mul_comm]
    have e1 := Lev.dat_lin (le_refl r) hk'' y0
    have e2 := Lev.dat_lin (le_refl r) hk (y0 * (ga' : Matrix (Fin r) (Fin r) E)ᵀ)
    have e3 := Lev.dat_lin (le_refl r) hk' y0
    have hne : D.dat (le_refl r) (y0 * (ga' : Matrix (Fin r) (Fin r) E)ᵀ) ≠ 0 := by
      rw [hy]
      unfold SW.Level.dat
      split_ifs with hc
      · exact Units.ne_zero _
      · exact absurd ⟨⟨k', hk'⟩, fun j hj => absurd j.isLt (not_lt.mpr hj)⟩ hc
    have hd0 : D.dat (le_refl r) y0 ≠ 0 := by
      intro h0
      apply hne
      rw [e3, h0]
      simp
    have hm : y0 * ((ga * ga' : GL (Fin r) E) : Matrix (Fin r) (Fin r) E)ᵀ =
        y0 * (ga' : Matrix (Fin r) (Fin r) E)ᵀ * (ga : Matrix (Fin r) (Fin r) E)ᵀ := by
      rw [Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc]
    rw [hm, e2, e3] at e1
    apply mul_right_cancel₀ hd0
    rw [← e1]
    ring

  have hcoc : ∀ ga ∈ D.grp, ∀ ga' ∈ D.grp, ∀ L ∈ D.lats,
      mu (ga * ga') L = mu ga (mapL ga' L) * mu ga' L := by
    intro ga hga ga' hga' L hL
    obtain ⟨k, hk⟩ := hred ga hga
    obtain ⟨k', hk'⟩ := hred ga' hga'
    have hgg : ga * ga' ∈ D.grp := Subgroup.mul_mem _ hga hga'
    obtain ⟨k'', hk''⟩ := hred _ hgg
    have hL' := hlat L hL ga' hga'
    have hL'' := hlat _ hL' ga hga
    have hcomp := (wG_laws E r X g bas idx n hs hn ga' (hun ga' hga') (v₀ L)
      (hvsb L hL)).2.2.2.2.2.1 ga (hun ga hga)
    have hsm := (wG_laws E r X g bas idx n hs hn ga (hun ga hga) (v₀ (mapL ga' L))
      (hvsb _ hL')).2.2.2.1 (mu ga' L * ((D.lam k' : ℂˣ) : ℂ))
    rw [hmu _ hgg L hL k'' hk'', hmu ga' hga' L hL k' hk', hsm, hmu ga hga _ hL' k hk, smul_smul,
      mapL_mul'] at hcomp
    have hc := smul_left_cancel_of_ip_self_eq_one (hvsb _ hL'') (hvone _ hL'') hcomp
    rw [hlam ga hga ga' hga' k k' k'' hk hk' hk''] at hc
    have hk0 : ((D.lam k : ℂˣ) : ℂ) * (D.lam k' : ℂˣ) ≠ 0 :=
      mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)
    apply mul_right_cancel₀ hk0
    linear_combination hc
  refine ⟨hnorm, ?_, hcoc⟩

  intro L hL
  have h1 := hcoc 1 (Subgroup.one_mem _) 1 (Subgroup.one_mem _) L hL
  rw [_root_.mul_one, mapL_one'] at h1
  have hn1 := hnorm 1 (Subgroup.one_mem _) L hL
  have hne : mu 1 L ≠ 0 := by
    intro h
    rw [h, norm_zero] at hn1
    exact zero_ne_one hn1
  exact mul_left_cancel₀ hne (h1.symm.trans (_root_.mul_one _).symm)

end GlobalTheory.Dict
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.VacuumMultiplierUnitaryCocycleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuum_multiplier_unitary_cocycle : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ D : SW.Level X, ∀ v₀ : Lt E r → TF n g, (∀ L ∈ D.lats, IsVac X bas D.w (tens (stdL E n) (D.sh L)) (v₀ L)) → ∀ mu : GL (Fin r) E → Lt E r → ℂ, (∀ ga ∈ D.grp, ∀ L ∈ D.lats, ∀ k : D.J, D.Red (fun i => (ga : Matrix (Fin r) (Fin r) E) *ᵥ D.β i) k → wG X bas idx ga (v₀ L) = (mu ga L * (D.lam k : ℂˣ)) • v₀ (mapL ga L)) → (∀ ga ∈ D.grp, ∀ L ∈ D.lats, ‖mu ga L‖ = 1) ∧ (∀ L ∈ D.lats, mu 1 L = 1) ∧ ∀ ga ∈ D.grp, ∀ ga' ∈ D.grp, ∀ L ∈ D.lats, mu (ga * ga') L = mu ga (mapL ga' L) * mu ga' L := by
  first | exact @GlobalTheory.Dict.vac_multiplier_cocycle | exact GlobalTheory.Dict.vac_multiplier_cocycle | (intros; apply GlobalTheory.Dict.vac_multiplier_cocycle <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.StableFormsEqSumThetaSeriesFreeLowerRows
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

private theorem thP_smul' {E : Type} [Field E] [NumberField E] [IsCMField E] {r g q0 n : ℕ}
    (X : Data E r) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ)
    (idx : Fin g ≃ X.Ψ × Fin r) (φ : SW.TF n g) (c : ℂ) (P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n))
    (x : Frame X.Ψ r) : thP X hr bas idx φ (c • P) x = c * thP X hr bas idx φ P x := by
  unfold thP
  by_cases hc : c = 0
  · subst hc
    simp [ReciprocityTheory.ChartRestriction.G.I2.polyDeriv]
  · simp only [ReciprocityTheory.ChartRestriction.G.I2.polyDeriv, MvPolynomial.support_smul_eq hc,
      MvPolynomial.coeff_smul, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => mul_assoc _ _ _

theorem GlobalTheory.Dict.stabForms_eq_sum_thP : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → 4 * (Module.finrank ℚ E * r) + 4 ≤ n → ∀ (D : SW.Level X) (hn : r ≤ n) (M : ℕ) (𝔐 𝔍 : Ideal (𝓞 E)), 0 < M → (M : 𝓞 E) ∈ D.𝔪 → D.𝔪 = 𝔐 * 𝔍 → IsCoprime 𝔐 𝔍 → ∀ v₀ : Lt E r → TF n g, (∀ L ∈ D.lats, IsVac X bas D.w (tens (stdL E n) (D.sh L)) (v₀ L)) → ∀ mu : GL (Fin r) E → Lt E r → ℂ, (∀ ga ∈ D.grp, ∀ L ∈ D.lats, ∀ k : D.J, D.Red (fun i => (ga : Matrix (Fin r) (Fin r) E) *ᵥ D.β i) k → wG X bas idx ga (v₀ L) = (mu ga L * (D.lam k : ℂˣ)) • v₀ (mapL ga L)) → ∀ (k : X.Ψ → Fin q0 → ℕ) (k' : X.Ψ → Fin X.p0 → ℕ) (Jx : Type) [Finite Jx] (L : Jx → Lt E r) (Q : Jx → Frame X.Ψ r → ℂ), (∀ i, L i ∈ D.lats) → (∀ i i', ∀ ga ∈ D.grp, mapL ga (L i) = L i' → i = i') → (∀ i, ∀ ga ∈ D.grp, mapL ga (L i) = L i → mu ga (L i) = 1) → (∀ i, IsStabForm X D.grp (L i) (wtOf X hr k k' n) (Q i)) → ∃ (m : ℕ) (Λ : Fin m → Lt E n) (P : Fin m → Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)), (∀ j, Λ j ∈ Vset E n M ∧ P j ∈ Harm.rowHighest ℂ k k') ∧ ∀ i, ∀ x ∈ X.dom, Q i x = ∑ j, thP X hr bas idx (phiF bas D 𝔐 hn v₀ (L i) (Λ j)) (P j) x := by
  intro E _ _ _ r X g q0 hr bas idx n hS hE hn4 D hn M 𝔐 𝔍 hM hMm hmf hcop v₀ hv mu hmu k k' Jx _ L Q
    hL hinj hfix hQ

  obtain ⟨hnorm, -, hcoc⟩ := GlobalTheory.T.vacuum_multiplier_unitary_cocycle E r X g bas idx n hS hE D v₀ hv mu hmu

  have hsys := GlobalTheory.T.hermitianThetaLevelData_forms_system E r X g bas idx n hS hE hn4 D hn M hM hMm v₀ hv mu hmu

  obtain ⟨F, hF, hFL⟩ := GlobalTheory.T.exists_form_extend_to_all_lattices E r X D.grp D.lats mu (wtOf X hr k k' n) Jx L Q hsys.un
    (fun ga hga L' hL' => ⟨hsys.stab ga hga L' hL', hnorm ga hga L' hL'⟩) hcoc hL hinj hfix hQ

  obtain ⟨m, Λ, P, a, hΛP, hFsum⟩ :=
    GlobalTheory.SW.level_theta_span E r X g q0 hr bas idx n hS hE hn4 D hn M hM hMm v₀ hv mu hmu k k' F hF

  have h97 := fun j => GlobalTheory.T.thetaSeries_lowerRowsZero_eq_freeLowerRows E r X g q0 hr bas idx n hS hE D hn M 𝔐 𝔍 hM hMm hmf hcop v₀ hv
    k k' (Λ j) (hΛP j).1 (P j) (hΛP j).2
  choose Λ' hΛ' P' hP' heq using h97
  refine ⟨m, Λ', fun j => a j • P' j, fun j => ⟨hΛ' j, Submodule.smul_mem _ _ (hP' j)⟩, ?_⟩
  intro i x hx
  rw [← hFL i x hx, hFsum (L i) (hL i) x hx]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [heq j (L i) (hL i) x hx, thP_smul']
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.StableFormsEqSumThetaSeriesFreeLowerRowsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stableForms_eq_sum_thetaSeries_freeLowerRows : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → 4 * (Module.finrank ℚ E * r) + 4 ≤ n → ∀ (D : SW.Level X) (hn : r ≤ n) (M : ℕ) (𝔐 𝔍 : Ideal (𝓞 E)), 0 < M → (M : 𝓞 E) ∈ D.𝔪 → D.𝔪 = 𝔐 * 𝔍 → IsCoprime 𝔐 𝔍 → ∀ v₀ : Lt E r → TF n g, (∀ L ∈ D.lats, IsVac X bas D.w (tens (stdL E n) (D.sh L)) (v₀ L)) → ∀ mu : GL (Fin r) E → Lt E r → ℂ, (∀ ga ∈ D.grp, ∀ L ∈ D.lats, ∀ k : D.J, D.Red (fun i => (ga : Matrix (Fin r) (Fin r) E) *ᵥ D.β i) k → wG X bas idx ga (v₀ L) = (mu ga L * (D.lam k : ℂˣ)) • v₀ (mapL ga L)) → ∀ (k : X.Ψ → Fin q0 → ℕ) (k' : X.Ψ → Fin X.p0 → ℕ) (Jx : Type) [Finite Jx] (L : Jx → Lt E r) (Q : Jx → Frame X.Ψ r → ℂ), (∀ i, L i ∈ D.lats) → (∀ i i', ∀ ga ∈ D.grp, mapL ga (L i) = L i' → i = i') → (∀ i, ∀ ga ∈ D.grp, mapL ga (L i) = L i → mu ga (L i) = 1) → (∀ i, IsStabForm X D.grp (L i) (wtOf X hr k k' n) (Q i)) → ∃ (m : ℕ) (Λ : Fin m → Lt E n) (P : Fin m → Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)), (∀ j, Λ j ∈ Vset E n M ∧ P j ∈ Harm.rowHighest ℂ k k') ∧ ∀ i, ∀ x ∈ X.dom, Q i x = ∑ j, thP X hr bas idx (phiF bas D 𝔐 hn v₀ (L i) (Λ j)) (P j) x := by
  first | exact @GlobalTheory.Dict.stabForms_eq_sum_thP | exact GlobalTheory.Dict.stabForms_eq_sum_thP | (intros; apply GlobalTheory.Dict.stabForms_eq_sum_thP <;> assumption)
end
