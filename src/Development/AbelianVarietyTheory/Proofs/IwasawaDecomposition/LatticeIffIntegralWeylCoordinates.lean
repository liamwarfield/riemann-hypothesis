module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralSpanIffPadicWeylDualLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFormsWeightEqParameterSubRho
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedSourceValueReadInChangedBases

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalBasisChangeIntegralUnitDet
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalBasisChangeIntegralUnitDet
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IntegralityCompare

noncomputable section

namespace GlobalTheory.LocBasisChange

theorem norm_le_one_of_isIntegral_int {C : Type} [NormedField C] [IsUltrametricDist C] {x : C}
    (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  have h : x ∈ (NormedField.valuation (K := C)).integer :=
    (Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral hx.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h

theorem norm_det_le_one {C : Type} [NormedField C] [IsUltrametricDist C] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) C) (h : ∀ a b, ‖M a b‖ ≤ 1) : ‖M.det‖ ≤ 1 := by
  rw [Matrix.det_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun σ _ => ?_
  have hp : ‖∏ i, M (σ i) i‖ ≤ 1 := by
    rw [norm_prod]; exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun i _ => h _ _
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> rw [hs]
  · rwa [one_smul]
  · rwa [Units.neg_smul, one_smul, norm_neg]

theorem norm_natCast_of_not_dvd {p : ℕ} [Fact p.Prime] {s : ℕ} (hs : ¬ p ∣ s) : ‖(s : ℂ_[p])‖ = 1 := by
  rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]), norm_algebraMap', Padic.norm_natCast_eq_one_iff]
  exact (Nat.Prime.coprime_iff_not_dvd Fact.out).2 hs

theorem basis_change : ∀ (D : D7) {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (τ : D.what₂.Tau) {N : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (Bm : GL (Fin N) D.host.E) (Bs : Matrix (Fin N) (Fin N) ℂ_[p]),
    GL3Columns.BasR D lam τ L Bs → Formalism.L2.Forms.IsLocBasis p (L : Set (Fin N → D.host.E)) Bm →
    ∃ g : Matrix (Fin N) (Fin N) ℂ_[p], (∀ a b, ‖g a b‖ ≤ 1) ∧ ‖g.det‖ = 1 ∧
      Bs = (Bm : Matrix (Fin N) (Fin N) D.host.E).map (TaylorLogMetric.tauEmb D lam τ) * g := by
  intro D p _ lam τ N L Bm Bs hR hL
  have hm : ∀ x, TaylorLogMetric.embT D τ x ∈ TaylorLogMetric.Qbar := fun x =>
    mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom (TaylorLogMetric.embT D τ).toRatAlgHom)
  set ρ : D.host.E →+* ℂ_[p] := lam.comp ((TaylorLogMetric.embT D τ).codRestrict TaylorLogMetric.Qbar hm) with hρ
  have hρe : ∀ x, TaylorLogMetric.tauEmb D lam τ x = ρ x := fun x => dif_pos (hm x)
  have hint : ∀ y : 𝓞 D.host.E, ‖ρ (y : D.host.E)‖ ≤ 1 := fun y =>
    norm_le_one_of_isIntegral_int (map_isIntegral_int ρ y.isIntegral_coe)
  have hunit : ∀ s : ℕ, ¬ p ∣ s → ‖ρ (s : D.host.E)‖ = 1 := fun s hs => by
    rw [map_natCast]; exact norm_natCast_of_not_dvd hs
  set Mm : Matrix (Fin N) (Fin N) D.host.E := (Bm : Matrix (Fin N) (Fin N) D.host.E) with hMm
  set Mi : Matrix (Fin N) (Fin N) D.host.E := ((Bm⁻¹ : GL (Fin N) D.host.E) : Matrix (Fin N) (Fin N) D.host.E) with hMi
  have hMMi : Mm * Mi = 1 := Bm.mul_inv
  have hMiM : Mi * Mm = 1 := Bm.inv_mul
  set A : Matrix (Fin N) (Fin N) ℂ_[p] := Mm.map ρ with hA
  set Ai : Matrix (Fin N) (Fin N) ℂ_[p] := Mi.map ρ with hAi
  have hAAi : A * Ai = 1 := by
    simp only [hA, hAi, ← RingHom.mapMatrix_apply, ← map_mul, hMMi, map_one]
  have hAiA : Ai * A = 1 := by
    simp only [hA, hAi, ← RingHom.mapMatrix_apply, ← map_mul, hMiM, map_one]
  set g : Matrix (Fin N) (Fin N) ℂ_[p] := Ai * Bs with hg
  have hBs : Bs = A * g := by rw [hg, ← Matrix.mul_assoc, hAAi, Matrix.one_mul]
  have hgi : ∀ a b, ‖g a b‖ ≤ 1 := by
    intro a b
    obtain ⟨n, r, x, hr, hx, hB⟩ := hR.2.2 b
    have e : g a b = ∑ k, r k * ρ ((Mi *ᵥ x k) a) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hg, Matrix.mul_apply, hB, hρe, hAi, Matrix.map_apply, Matrix.mulVec, dotProduct, map_sum,
        map_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [e]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
    obtain ⟨s, hs, hmem⟩ := (hL (x k)).1 ⟨1, (Fact.out : p.Prime).not_dvd_one, by simpa using hx k⟩
    obtain ⟨z, hz⟩ := hmem a
    have h1 : ‖ρ ((s : D.host.E) * (Mi *ᵥ x k) a)‖ ≤ 1 := by rw [← hz]; exact hint z
    rw [map_mul, norm_mul, hunit s hs, one_mul] at h1
    rw [norm_mul]
    calc ‖r k‖ * ‖ρ ((Mi *ᵥ x k) a)‖ ≤ 1 * 1 := by gcongr; exact hr k
      _ = 1 := one_mul 1
  have hBsu : IsUnit Bs.det := isUnit_iff_ne_zero.2 hR.1
  set h : Matrix (Fin N) (Fin N) ℂ_[p] := Bs⁻¹ * A with hh
  have hgh : g * h = 1 := by
    rw [hg, hh, Matrix.mul_assoc, ← Matrix.mul_assoc Bs, Matrix.mul_nonsing_inv _ hBsu, Matrix.one_mul, hAiA]
  have hhi : ∀ a b, ‖h a b‖ ≤ 1 := by
    intro a b
    set xb : Fin N → D.host.E := fun j => Mm j b with hxb
    have hcol : ∀ a, (Mi *ᵥ xb) a = (1 : Matrix (Fin N) (Fin N) D.host.E) a b := by
      intro a; rw [← hMiM]; rfl
    obtain ⟨s, hs, hmem⟩ := (hL xb).2 ⟨1, (Fact.out : p.Prime).not_dvd_one, fun a => by
      rw [hcol, Nat.cast_one, one_mul, Matrix.one_apply]
      split_ifs
      · exact ⟨1, map_one _⟩
      · exact ⟨0, map_zero _⟩⟩
    have hb := hR.2.1 _ hmem a
    have key : (Bs⁻¹ *ᵥ fun i => TaylorLogMetric.tauEmb D lam τ (((s : D.host.E) • xb) i)) a = ρ s * h a b := by
      simp only [hρe, Pi.smul_apply, smul_eq_mul, map_mul, hh, Matrix.mul_apply, Matrix.mulVec, dotProduct,
        hA, Matrix.map_apply, hxb, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [key, norm_mul, map_natCast, norm_natCast_of_not_dvd hs, one_mul] at hb
    exact hb
  have hd1 := norm_det_le_one g hgi
  have hd2 := norm_det_le_one h hhi
  have hprod : ‖g.det‖ * ‖h.det‖ = 1 := by
    rw [← norm_mul, ← Matrix.det_mul, hgh, Matrix.det_one, norm_one]
  refine ⟨g, hgi, le_antisymm hd1 ?_, ?_⟩
  swap
  · rw [hBs]; congr 1; ext i j; simp only [hA, Matrix.map_apply, hρe]
  calc (1 : ℝ) = ‖g.det‖ * ‖h.det‖ := hprod.symm
    _ ≤ ‖g.det‖ * 1 := by gcongr
    _ = ‖g.det‖ := mul_one _

end GlobalTheory.LocBasisChange

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalBasisChangeIntegralUnitDetStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IntegralityCompare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localBasis_change_integral_unit_det : ∀ (D : D7) {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (τ : D.what₂.Tau) {N : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (Bm : GL (Fin N) D.host.E) (Bs : Matrix (Fin N) (Fin N) ℂ_[p]),
    GL3Columns.BasR D lam τ L Bs → Formalism.L2.Forms.IsLocBasis p (L : Set (Fin N → D.host.E)) Bm →
    ∃ g : Matrix (Fin N) (Fin N) ℂ_[p], (∀ a b, ‖g a b‖ ≤ 1) ∧ ‖g.det‖ = 1 ∧
      Bs = (Bm : Matrix (Fin N) (Fin N) D.host.E).map (TaylorLogMetric.tauEmb D lam τ) * g := by
  first | exact @GlobalTheory.LocBasisChange.basis_change | exact GlobalTheory.LocBasisChange.basis_change | (intros; apply GlobalTheory.LocBasisChange.basis_change <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AutomorphicFormFnInvIffTwistedSubstitutionMem
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AutomorphicFormFnInvIffTwistedSubstitutionMem
noncomputable section

namespace GlobalTheory.IntegralityCompare

open MvPolynomial Formalism.L2.Forms

theorem fnOf_apply_eq {ι : Type} [Fintype ι] {n : ℕ} (G : ι → Matrix (Fin n) (Fin n) ℂ) (s : ι → ℤ)
    (A : ι → Matrix (Fin n) (Fin n) ℂ) (P : MvPolynomial (ι × Fin n × Fin n) ℂ) (y : Frames G) :
    fnOf G s A P y = (∏ τ, (A τ * y.1 τ).det ^ s τ) *
      eval (fun x : ι × Fin n × Fin n => (A x.1 * y.1 x.1) x.2.1 x.2.2) P := rfl

theorem map_mul_map_inv {E ι : Type} [Field E] {n : ℕ} (emb : ι → E →+* ℂ) (M : GL (Fin n) E) (τ : ι) :
    (M : Matrix (Fin n) (Fin n) E).map (emb τ) *
      ((M⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map (emb τ) = 1 := by
  rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]

theorem map_inv_mul_map {E ι : Type} [Field E] {n : ℕ} (emb : ι → E →+* ℂ) (M : GL (Fin n) E) (τ : ι) :
    ((M⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map (emb τ) *
      (M : Matrix (Fin n) (Fin n) E).map (emb τ) = 1 := by
  rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]

theorem det_map_emb {E ι : Type} [Field E] {n : ℕ} (emb : ι → E →+* ℂ) (M : Matrix (Fin n) (Fin n) E) (τ : ι) :
    emb τ M.det = (M.map (emb τ)).det := RingHom.map_det _ _

theorem fnOf_inv_twSub {E ι : Type} [Field E] [Fintype ι] {n : ℕ} (emb : ι → E →+* ℂ) (M : GL (Fin n) E)
    (s : ι → ℤ) (G : ι → Matrix (Fin n) (Fin n) ℂ) (P0 : MvPolynomial (ι × Fin n × Fin n) ℂ) (y : Frames G) :
    fnOf G s (atInf emb ((M⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)) (twSub emb M s P0) y
      = fnOf G s 1 P0 y := by
  rw [fnOf_apply_eq, fnOf_apply_eq]
  have h := eval_twSub emb M s P0
    (fun τ => atInf emb ((M⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ * y.1 τ)
  have hy : ∀ τ, (M : Matrix (Fin n) (Fin n) E).map (emb τ) *
      (atInf emb ((M⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ * y.1 τ) = y.1 τ := by
    intro τ; rw [← Matrix.mul_assoc, atInf, map_mul_map_inv, Matrix.one_mul]
  simp only [hy] at h
  rw [h]
  simp only [Pi.one_apply, Matrix.one_mul]
  rw [← mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [mul_comm, ← mul_zpow, det_map_emb, ← Matrix.det_mul, hy]

theorem exists_det_poly {ι : Type} [Fintype ι] {n : ℕ} :
    ∃ D : MvPolynomial (ι × Fin n × Fin n) ℂ, ∀ x : ι → Matrix (Fin n) (Fin n) ℂ,
      eval (fun k : ι × Fin n × Fin n => x k.1 k.2.1 k.2.2) D = ∏ τ, (x τ).det := by
  refine ⟨∏ τ, Matrix.det (Matrix.of fun a b => (X (τ, a, b) : MvPolynomial (ι × Fin n × Fin n) ℂ)), ?_⟩
  intro x
  rw [map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [RingHom.map_det]
  congr 1
  ext a b
  simp

theorem eq_of_eval_units {ι : Type} [Fintype ι] {n : ℕ} (Q : MvPolynomial (ι × Fin n × Fin n) ℂ)
    (hQ : ∀ x : ι → Matrix (Fin n) (Fin n) ℂ, (∀ τ, IsUnit (x τ).det) →
      eval (fun k : ι × Fin n × Fin n => x k.1 k.2.1 k.2.2) Q = 0) : Q = 0 := by
  obtain ⟨D, hD⟩ := exists_det_poly (ι := ι) (n := n)
  have hQD : Q * D = 0 := by
    apply MvPolynomial.funext
    intro x
    let xm : ι → Matrix (Fin n) (Fin n) ℂ := fun τ a b => x (τ, a, b)
    rw [map_zero, map_mul]
    show eval (fun k : ι × Fin n × Fin n => xm k.1 k.2.1 k.2.2) Q *
      eval (fun k : ι × Fin n × Fin n => xm k.1 k.2.1 k.2.2) D = 0
    rw [hD]
    by_cases hu : ∀ τ, IsUnit (xm τ).det
    · rw [hQ _ hu, zero_mul]
    · push_neg at hu
      obtain ⟨τ, hτ⟩ := hu
      rw [isUnit_iff_ne_zero, not_not] at hτ
      rw [Finset.prod_eq_zero (Finset.mem_univ τ) hτ, mul_zero]
  have hD0 : D ≠ 0 := by
    intro h0
    have := hD (fun _ => 1)
    rw [h0, map_zero] at this
    simp at this
  exact (mul_eq_zero.mp hQD).resolve_right hD0

theorem fnOf_inv_iff_twSub_mem : ∀ {E ι : Type} [Field E] [Fintype ι] {n : ℕ} (emb : ι → E →+* ℂ) (M : GL (Fin n) E) (s : ι → ℤ)
    (G : ι → Matrix (Fin n) (Fin n) ℂ) (P0 : MvPolynomial (ι × Fin n × Fin n) ℂ)
    (S : AddSubgroup (MvPolynomial (ι × Fin n × Fin n) ℂ)) {Yt : Type} (e : Yt ≃ Frames G) (f : Yt → ℂ),
    (∀ z, f z = fnOf G s 1 P0 (e z)) →
    ((∃ P ∈ S, ∀ z, f z = fnOf G s (atInf emb ((M⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)) P (e z)) ↔
      twSub emb M s P0 ∈ S) := by
  intro E ι _ _ n emb M s G P0 S Yt e f hf
  constructor
  · rintro ⟨P, hP, hPf⟩
    have hall : ∀ y : Frames G,
        fnOf G s (atInf emb ((M⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)) P y =
        fnOf G s (atInf emb ((M⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)) (twSub emb M s P0) y := by
      intro y
      obtain ⟨z, rfl⟩ := e.surjective y
      rw [← hPf, hf, fnOf_inv_twSub]
    suffices hPeq : P - twSub emb M s P0 = 0 by
      rw [sub_eq_zero] at hPeq
      rw [← hPeq]; exact hP
    apply eq_of_eval_units
    intro x hx
    have hMu : IsUnit (M : Matrix (Fin n) (Fin n) E).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp M.isUnit
    let y : Frames G := ⟨fun τ => (M : Matrix (Fin n) (Fin n) E).map (emb τ) * x τ, fun τ => by
      rw [Matrix.det_mul, ← det_map_emb]; exact (hMu.map (emb τ)).mul (hx τ)⟩
    have h1 := hall y
    rw [fnOf_apply_eq, fnOf_apply_eq] at h1
    have hAx : ∀ τ, atInf emb ((M⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ * y.1 τ = x τ := by
      intro τ
      show atInf emb ((M⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ *
        ((M : Matrix (Fin n) (Fin n) E).map (emb τ) * x τ) = x τ
      rw [← Matrix.mul_assoc, atInf, map_inv_mul_map, Matrix.one_mul]
    simp only [hAx] at h1
    have hne : (∏ τ, (x τ).det ^ s τ) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun τ _ => zpow_ne_zero _ (hx τ).ne_zero
    rw [map_sub, sub_eq_zero]
    exact mul_left_cancel₀ hne h1
  · intro h
    exact ⟨_, h, fun z => by rw [hf, fnOf_inv_twSub]⟩

end GlobalTheory.IntegralityCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AutomorphicFormFnInvIffTwistedSubstitutionMemStatement
open Formalism.L2.Forms GlobalTheory.IntegralityCompare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.automorphicFormFn_inv_iff_twistedSubstitution_mem : ∀ {E ι : Type} [Field E] [Fintype ι] {n : ℕ} (emb : ι → E →+* ℂ) (M : GL (Fin n) E) (s : ι → ℤ)
    (G : ι → Matrix (Fin n) (Fin n) ℂ) (P0 : MvPolynomial (ι × Fin n × Fin n) ℂ)
    (S : AddSubgroup (MvPolynomial (ι × Fin n × Fin n) ℂ)) {Yt : Type} (e : Yt ≃ Frames G) (f : Yt → ℂ),
    (∀ z, f z = fnOf G s 1 P0 (e z)) →
    ((∃ P ∈ S, ∀ z, f z = fnOf G s (atInf emb ((M⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)) P (e z)) ↔
      twSub emb M s P0 ∈ S) := by
  first | exact @GlobalTheory.IntegralityCompare.fnOf_inv_iff_twSub_mem | exact GlobalTheory.IntegralityCompare.fnOf_inv_iff_twSub_mem | (intros; apply GlobalTheory.IntegralityCompare.fnOf_inv_iff_twSub_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeylLatticeDualInvariantUnit
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeylLatticeDualInvariantUnit
open MvPolynomial

noncomputable section

namespace GlobalTheory.WeylTensorSubst

def drop {n : ℕ} (ν : Fin n → ℕ) (s : Fin n) : ℕ := ν s - Formalism.GradedWeylDivisibility.nuNext ν s

def antiOf {n : ℕ} (ν : Fin n → ℕ) (s : Fin n) : ℕ := ∑ t ∈ Finset.Ici s, drop ν t

theorem antiOf_antitone {n : ℕ} (ν : Fin n → ℕ) : Antitone (antiOf ν) := fun s s' h =>
  Finset.sum_le_sum_of_subset (Finset.Ici_subset_Ici.2 h)

theorem antiOf_eq {n : ℕ} (ν : Fin n → ℕ) (s : Fin n) :
    antiOf ν s = drop ν s + Formalism.GradedWeylDivisibility.nuNext (antiOf ν) s := by
  unfold antiOf
  rw [Finset.Ici_eq_cons_Ioi, Finset.sum_cons]
  congr 1
  unfold Formalism.GradedWeylDivisibility.nuNext
  split_ifs with h
  · congr 1
    ext t
    simp only [Finset.mem_Ioi, Finset.mem_Ici, Fin.lt_def, Fin.le_iff_val_le_val]
    omega
  · have : Finset.Ioi s = ∅ := by
      ext t
      simp only [Finset.mem_Ioi, Finset.notMem_empty, iff_false, Fin.lt_def, not_lt]
      omega
    rw [this, Finset.sum_empty]

theorem hw_antiOf (R : Type) [CommRing R] {n : ℕ} (ν : Fin n → ℕ) :
    Formalism.GradedWeylDivisibility.hw R le_rfl (antiOf ν) = Formalism.GradedWeylDivisibility.hw R le_rfl ν := by
  unfold Formalism.GradedWeylDivisibility.hw
  refine Finset.prod_congr rfl fun s _ => ?_
  have := antiOf_eq ν s
  unfold drop at this
  congr 1
  omega

theorem weyl_eq_antiOf (R : Type) [CommRing R] (N : ℕ) (ν : Fin N → ℕ) :
    WeylLatticeDuality.weyl R N N le_rfl ν = Formalism.GradedWeylDivisibility.weyl R N N le_rfl (antiOf ν) := by
  show Formalism.GradedWeylDivisibility.weyl R N N le_rfl ν = _
  unfold Formalism.GradedWeylDivisibility.weyl
  rw [hw_antiOf]

def ball (p : ℕ) [Fact p.Prime] : Subring ℂ_[p] := GlobalTheory.ClosedBallValuationSubring.closedBallSubring ℂ_[p]

variable {p : ℕ} [Fact p.Prime] {N : ℕ}

def ev (h : MvPolynomial (Fin N × Fin N) ℤ) (y : Matrix (Fin N) (Fin N) ℂ_[p]) : ℂ_[p] :=
  eval (fun k : Fin N × Fin N => y k.1 k.2) (map (Int.castRingHom ℂ_[p]) h)

def Expands (ν : Fin N → ℕ) (φ : Matrix (Fin N) (Fin N) ℂ_[p] → ℂ_[p]) : Prop :=
  ∃ (m : ℕ) (o : Fin m → ℂ_[p]) (h : Fin m → MvPolynomial (Fin N × Fin N) ℤ),
    (∀ j, ‖o j‖ ≤ 1) ∧ (∀ j, h j ∈ WeylLatticeDuality.weyl ℤ N N le_rfl ν) ∧ φ = fun y => ∑ j, o j * ev (h j) y

theorem expands_zero (ν : Fin N → ℕ) : Expands (p := p) ν 0 :=
  ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, fun j => j.elim0, by funext y; simp⟩

theorem expands_add {ν : Fin N → ℕ} {φ ψ : Matrix (Fin N) (Fin N) ℂ_[p] → ℂ_[p]} (hφ : Expands ν φ)
    (hψ : Expands ν ψ) : Expands ν (φ + ψ) := by
  obtain ⟨m, o, h, ho, hh, rfl⟩ := hφ
  obtain ⟨m', o', h', ho', hh', rfl⟩ := hψ
  refine ⟨m + m', Fin.append o o', Fin.append h h', fun j => ?_, fun j => ?_, ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [ho, ho']
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [hh, hh']
  · funext y
    simp [Fin.sum_univ_add]

theorem expands_smul {ν : Fin N → ℕ} {φ : Matrix (Fin N) (Fin N) ℂ_[p] → ℂ_[p]} (c : ℂ_[p]) (hc : ‖c‖ ≤ 1)
    (hφ : Expands ν φ) : Expands ν (fun y => c * φ y) := by
  obtain ⟨m, o, h, ho, hh, rfl⟩ := hφ
  refine ⟨m, fun j => c * o j, h, fun j => ?_, hh, ?_⟩
  · rw [norm_mul]; exact mul_le_one₀ hc (norm_nonneg _) (ho j)
  · funext y
    simp only [Finset.mul_sum, mul_assoc]

theorem expands_rowSubst (ν : Fin N → ℕ) (g : Matrix (Fin N) (Fin N) ℂ_[p]) (hg : ∀ a b, ‖g a b‖ ≤ 1)
    {f : MvPolynomial (Fin N × Fin N) ℤ} (hf : f ∈ WeylLatticeDuality.weyl ℤ N N le_rfl ν) :
    Expands ν (fun y => ev f (g * y)) := by
  let O := ball p
  let M : Matrix (Fin N) (Fin N) O := fun a b => ⟨g a b, hg a b⟩
  have hsub : O.subtype.comp (Int.castRingHom O) = Int.castRingHom ℂ_[p] := RingHom.ext_int _ _
  rw [weyl_eq_antiOf] at hf

  have h1 : map (Int.castRingHom O) f ∈ Formalism.GradedWeylDivisibility.weyl O N N le_rfl (antiOf ν) := by
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, rfl⟩ := hx
      exact Submodule.subset_span ⟨w, by
        beta_reduce
        rw [← Formalism.GradedWeylDivisibility.lclosedeq_hw_map (Int.castRingHom O), Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map]⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul c x _ hx => rw [map_zsmul]; exact zsmul_mem hx c
  have h2 := GlobalTheory.WeylRowAll.rowAct_mem_weyl_square O N (antiOf ν) (antiOf_antitone ν) M _ h1
  have e : (fun y => ev f (g * y)) =
      fun y => eval (fun k : Fin N × Fin N => y k.1 k.2) (map O.subtype (Formalism.GradedWeylDivisibility.rowAct O M (map (Int.castRingHom O) f))) := by
    funext y
    unfold ev
    have : (eval (fun k : Fin N × Fin N => (g * y) k.1 k.2)).comp (map (Int.castRingHom ℂ_[p])) =
        ((eval (fun k : Fin N × Fin N => y k.1 k.2)).comp (map O.subtype)).comp
          ((Formalism.GradedWeylDivisibility.rowAct O M (n := N)).toRingHom.comp (map (Int.castRingHom O))) := by
      refine MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) fun v => ?_
      simp [Formalism.GradedWeylDivisibility.rowAct, Matrix.mul_apply, M, O]
    exact RingHom.congr_fun this f
  rw [e]
  generalize Formalism.GradedWeylDivisibility.rowAct O M (map (Int.castRingHom O) f) = F at h2
  induction h2 using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    refine ⟨1, fun _ => 1, fun _ => Formalism.GradedWeylDivisibility.applyWord ℤ w (Formalism.GradedWeylDivisibility.hw ℤ le_rfl (antiOf ν)), fun _ => by simp,
      fun _ => ?_, ?_⟩
    · rw [weyl_eq_antiOf]; exact Submodule.subset_span ⟨w, rfl⟩
    · funext y
      simp only [Finset.univ_unique, Finset.sum_singleton, one_mul, ev]
      rw [← Formalism.GradedWeylDivisibility.lclosedeq_hw_map (Int.castRingHom O), Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, map_map, hsub]
  | zero =>
    convert expands_zero (p := p) ν using 1
    funext y
    simp
  | add x y _ _ hx hy =>
    have := expands_add hx hy
    convert this using 1
    funext z
    simp
  | smul c x _ hx =>
    have := expands_smul (c : ℂ_[p]) c.2 hx
    convert this using 1
    funext z
    rw [smul_eq_C_mul, map_mul, map_C, eval_mul, eval_C]
    rfl

theorem inv_entry_le {g : Matrix (Fin N) (Fin N) ℂ_[p]} (hg : ∀ a b, ‖g a b‖ ≤ 1) (hd : ‖g.det‖ = 1) (a b : Fin N) :
    ‖g⁻¹ a b‖ ≤ 1 := by
  let O := ball p
  let Mo : Matrix (Fin N) (Fin N) O := fun a b => ⟨g a b, hg a b⟩
  have hM : g = Mo.map O.subtype := by ext a b; rfl
  have hadj : g.adjugate a b = ((Mo.adjugate a b : O) : ℂ_[p]) := by
    have h := RingHom.map_adjugate O.subtype Mo
    rw [hM]
    exact (congrFun (congrFun h a) b).symm
  rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv', norm_mul, norm_inv, hd, inv_one, one_mul,
    hadj]
  exact (Mo.adjugate a b).2

variable {T : Type} [Fintype T]

theorem subst_mem {ν : T → Fin N → ℕ} (g : T → Matrix (Fin N) (Fin N) ℂ_[p]) (c : ℂ_[p]) (hc : ‖c‖ ≤ 1)
    (hg : ∀ τ a b, ‖g τ a b‖ ≤ 1) {F : (T → Matrix (Fin N) (Fin N) ℂ_[p]) → ℂ_[p]}
    (hF : F ∈ WeylLatticeDuality.DelW p T N ν) :
    (fun y => c * F (fun τ => g τ * y τ)) ∈ WeylLatticeDuality.DelW p T N ν := by
  induction hF using AddSubgroup.closure_induction with
  | mem F hF =>
    obtain ⟨r, f, hr, hf, rfl⟩ := hF
    choose m o h ho hh he using fun τ => expands_rowSubst (ν τ) (g τ) (hg τ) (hf τ)
    have hb : ∀ x : ∀ τ, Fin (m τ), ‖c * r * ∏ τ, o τ (x τ)‖ ≤ 1 := fun x => by
      rw [norm_mul, norm_mul, norm_prod]
      exact mul_le_one₀ (mul_le_one₀ hc (norm_nonneg _) hr) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
        (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun τ _ => ho τ _)
    have hgen : ∀ x : ∀ τ, Fin (m τ), (fun y : T → Matrix (Fin N) (Fin N) ℂ_[p] => (c * r * ∏ τ, o τ (x τ)) *
        ∏ τ, eval (fun k : Fin N × Fin N => y τ k.1 k.2) (map (Int.castRingHom ℂ_[p]) (h τ (x τ)))) ∈
        WeylLatticeDuality.DelW p T N ν := fun x =>
      AddSubgroup.subset_closure ⟨c * r * ∏ τ, o τ (x τ), fun τ => h τ (x τ), hb x, fun τ => hh τ _, rfl⟩
    convert AddSubgroup.sum_mem _ (t := Finset.univ) (fun x _ => hgen x) using 1
    funext y
    rw [Finset.sum_apply]
    have e : ∀ τ, eval (fun k : Fin N × Fin N => (g τ * y τ) k.1 k.2) (map (Int.castRingHom ℂ_[p]) (f τ)) =
        ∑ j, o τ j * ev (h τ j) (y τ) := fun τ => congrFun (he τ) (y τ)
    simp only [e]
    classical
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.prod_mul_distrib]
    simp only [ev]
    ring
  | zero =>
    convert zero_mem (WeylLatticeDuality.DelW p T N ν) using 1
    funext y; simp
  | add F G _ _ hF hG =>
    convert add_mem hF hG using 1
    funext y; simp [mul_add]
  | neg F _ hF =>
    convert neg_mem hF using 1
    funext y; simp

theorem subst_mem_iff (p : ℕ) [Fact p.Prime] (T : Type) [Fintype T] (N : ℕ) (ν : T → Fin N → ℕ)
    (g : T → Matrix (Fin N) (Fin N) ℂ_[p]) (c : ℂ_[p]) (F : (T → Matrix (Fin N) (Fin N) ℂ_[p]) → ℂ_[p]) :
    ‖c‖ = 1 → (∀ τ a b, ‖g τ a b‖ ≤ 1) → (∀ τ, ‖(g τ).det‖ = 1) →
    ((fun y => c * F (fun τ => g τ * y τ)) ∈ WeylLatticeDuality.DelW p T N ν ↔ F ∈ WeylLatticeDuality.DelW p T N ν) := by
  intro hc hg hd
  constructor
  · intro h
    have hc0 : c ≠ 0 := fun h0 => by rw [h0, norm_zero] at hc; exact zero_ne_one hc
    have hu : ∀ τ, IsUnit (g τ).det := fun τ => isUnit_iff_ne_zero.2 fun h0 => by
      have := hd τ; rw [h0, norm_zero] at this; exact zero_ne_one this
    have := subst_mem (fun τ => (g τ)⁻¹) c⁻¹ (by rw [norm_inv, hc, inv_one])
      (fun τ => inv_entry_le (hg τ) (hd τ)) h
    convert this using 1
    funext y
    have hy : (fun τ => g τ * ((g τ)⁻¹ * y τ)) = y := by
      funext τ
      exact Matrix.mul_nonsing_inv_cancel_left (g τ) (y τ) (hu τ)
    simp [hy, hc0]
  · exact subst_mem g c hc.le hg

end GlobalTheory.WeylTensorSubst

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeylLatticeDualInvariantUnitStatement
open GlobalTheory.IntegralityCompare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weyl_lattice_dual_invariant_unit : ∀ (p : ℕ) [Fact p.Prime] (T : Type) [Fintype T] (N : ℕ) (ν : T → Fin N → ℕ)
    (g : T → Matrix (Fin N) (Fin N) ℂ_[p]) (c : ℂ_[p]) (F : (T → Matrix (Fin N) (Fin N) ℂ_[p]) → ℂ_[p]),
    ‖c‖ = 1 → (∀ τ a b, ‖g τ a b‖ ≤ 1) → (∀ τ, ‖(g τ).det‖ = 1) →
    ((fun y => c * F (fun τ => g τ * y τ)) ∈ WeylLatticeDuality.DelW p T N ν ↔ F ∈ WeylLatticeDuality.DelW p T N ν) := by
  first | exact @GlobalTheory.WeylTensorSubst.subst_mem_iff | exact GlobalTheory.WeylTensorSubst.subst_mem_iff | (intros; apply GlobalTheory.WeylTensorSubst.subst_mem_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetPowerProductMulMemDelWShiftIff
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetPowerProductMulMemDelWShiftIff
noncomputable section

namespace GlobalTheory.DetShiftWeyl

open MvPolynomial WeylLatticeDuality GlobalTheory.IntegralityCompare

theorem hw_shift (R : Type) [CommRing R] {m : ℕ} (ν : Fin (m + 1) → ℕ) (c : ℕ) :
    hw R (r := m + 1) (n := m + 1) le_rfl (fun s => ν s + c) =
      hw R (r := m + 1) (n := m + 1) le_rfl ν * lpMinor R (r := m + 1) (n := m + 1) (m + 1) le_rfl le_rfl ^ c := by
  unfold hw
  rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc, mul_assoc]
  congr 1
  · apply Finset.prod_congr rfl
    intro s _
    congr 1
    unfold nuNext
    have h : (s.castSucc : Fin (m + 1)).val + 1 < m + 1 := by simp only [Fin.val_castSucc]; omega
    rw [dite_eq_left h, dite_eq_left h]
    dsimp only
    omega
  · have h : ¬ ((Fin.last m : Fin (m + 1)).val + 1 < m + 1) := by simp
    unfold nuNext
    rw [dite_eq_right h, dite_eq_right h]
    dsimp only
    rw [Nat.sub_zero, Nat.sub_zero, pow_add]
    rfl

theorem rowGen_fullMinor (R : Type) [CommRing R] {m : ℕ} (a b : Fin m) (hab : a ≠ b) :
    rowGen R a b (lpMinor R (r := m) (n := m) m le_rfl le_rfl) =
      Polynomial.C (lpMinor R (r := m) (n := m) m le_rfl le_rfl) := by
  unfold lpMinor
  set M : Matrix (Fin m) (Fin m) (MvPolynomial (Fin m × Fin m) R) :=
    Matrix.of fun p q : Fin m => X (Fin.castLE le_rfl p, Fin.castLE le_rfl q) with hMdef
  rw [AlgHom.map_det, RingHom.map_det]
  have hM : (rowGen R a b).mapMatrix M =
      Matrix.updateRow ((Polynomial.C : MvPolynomial (Fin m × Fin m) R →+* _).mapMatrix M) b
        (((Polynomial.C : MvPolynomial (Fin m × Fin m) R →+* _).mapMatrix M) b +
          (Polynomial.X : Polynomial (MvPolynomial (Fin m × Fin m) R)) •
            ((Polynomial.C : MvPolynomial (Fin m × Fin m) R →+* _).mapMatrix M) a) := by
    ext p q
    by_cases hp : p = b
    · subst hp
      simp [hMdef, Matrix.updateRow_apply, rowGen, Fin.castLE_refl]
      try ring
    · simp [hMdef, Matrix.updateRow_apply, rowGen, Fin.castLE_refl, hp]
  rw [hM, Matrix.det_updateRow_add_smul_self _ (Ne.symm hab)]

theorem rowDiv_fullMinor_mul (R : Type) [CommRing R] {m : ℕ} (a b : Fin m) (hab : a ≠ b) (k c : ℕ)
    (f : MvPolynomial (Fin m × Fin m) R) :
    rowDiv R a b k (lpMinor R (r := m) (n := m) m le_rfl le_rfl ^ c * f) =
      lpMinor R (r := m) (n := m) m le_rfl le_rfl ^ c * rowDiv R a b k f := by
  unfold rowDiv
  rw [map_mul, map_pow, rowGen_fullMinor R a b hab, ← Polynomial.C_pow, Polynomial.coeff_C_mul]

theorem rowGen_fullMinor_self (R : Type) [CommRing R] {m : ℕ} (a : Fin m) :
    rowGen R a a (lpMinor R (r := m) (n := m) m le_rfl le_rfl) =
      (1 + Polynomial.X) * Polynomial.C (lpMinor R (r := m) (n := m) m le_rfl le_rfl) := by
  unfold lpMinor
  set M : Matrix (Fin m) (Fin m) (MvPolynomial (Fin m × Fin m) R) :=
    Matrix.of fun p q : Fin m => X (Fin.castLE le_rfl p, Fin.castLE le_rfl q) with hMdef
  rw [AlgHom.map_det, RingHom.map_det]
  have hM : (rowGen R a a).mapMatrix M =
      Matrix.updateRow ((Polynomial.C : MvPolynomial (Fin m × Fin m) R →+* _).mapMatrix M) a
        ((1 + Polynomial.X : Polynomial (MvPolynomial (Fin m × Fin m) R)) •
            ((Polynomial.C : MvPolynomial (Fin m × Fin m) R →+* _).mapMatrix M) a) := by
    refine Matrix.ext fun p q => ?_
    by_cases hp : p = a
    · subst hp
      simp [hMdef, Matrix.updateRow_apply, rowGen, Fin.castLE_refl]
      try ring
    · simp [hMdef, Matrix.updateRow_apply, rowGen, Fin.castLE_refl, hp]
  rw [hM, Matrix.det_updateRow_smul, Matrix.updateRow_eq_self]

theorem rowDiv_fullMinor_mul_self (R : Type) [CommRing R] {m : ℕ} (a : Fin m) (k c : ℕ)
    (f : MvPolynomial (Fin m × Fin m) R) :
    rowDiv R a a k (lpMinor R (r := m) (n := m) m le_rfl le_rfl ^ c * f) =
      lpMinor R (r := m) (n := m) m le_rfl le_rfl ^ c *
        ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k,
          ((c.choose p.1 : ℕ) : MvPolynomial (Fin m × Fin m) R) * rowDiv R a a p.2 f := by
  unfold rowDiv
  rw [map_mul, map_pow, rowGen_fullMinor_self, mul_pow, ← Polynomial.C_pow, mul_comm ((1 + Polynomial.X) ^ c) _,
    mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  rw [add_comm (1 : Polynomial (MvPolynomial (Fin m × Fin m) R)), Polynomial.coeff_X_add_one_pow]

theorem rowDiv_add' (R : Type) [CommRing R] {r n : ℕ} (a b : Fin r) (k : ℕ) (f g : MvPolynomial (Fin r × Fin n) R) :
    rowDiv R a b k (f + g) = rowDiv R a b k f + rowDiv R a b k g := by
  unfold rowDiv
  rw [map_add (f := _), Polynomial.coeff_add]

theorem rowDiv_smul' (R : Type) [CommRing R] {r n : ℕ} (a b : Fin r) (k : ℕ) (t : R)
    (f : MvPolynomial (Fin r × Fin n) R) : rowDiv R a b k (t • f) = t • rowDiv R a b k f := by
  unfold rowDiv
  rw [map_smul, Polynomial.coeff_smul]

theorem rowDiv_zero' (R : Type) [CommRing R] {r n : ℕ} (a b : Fin r) (k : ℕ) :
    rowDiv R a b k (0 : MvPolynomial (Fin r × Fin n) R) = 0 := by
  unfold rowDiv
  rw [map_zero, Polynomial.coeff_zero]

theorem rowDiv_mem (R : Type) [CommRing R] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (a b : Fin r) (k : ℕ)
    (f : MvPolynomial (Fin r × Fin n) R) (hf : f ∈ weyl R r n hn ν) : rowDiv R a b k f ∈ weyl R r n hn ν := by
  unfold weyl at hf ⊢
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    exact Submodule.subset_span ⟨(a, b, k) :: w, rfl⟩
  | zero => rw [rowDiv_zero']; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [rowDiv_add']; exact Submodule.add_mem _ hx hy
  | smul t x _ hx => rw [rowDiv_smul']; exact Submodule.smul_mem _ t hx

theorem weyl_shift_le (R : Type) [CommRing R] {m : ℕ} (ν : Fin (m + 1) → ℕ) (c : ℕ) :
    weyl R (m + 1) (m + 1) le_rfl (fun s => ν s + c) ≤
      (weyl R (m + 1) (m + 1) le_rfl ν).map
        (LinearMap.mulLeft R (lpMinor R (r := m + 1) (n := m + 1) (m + 1) le_rfl le_rfl ^ c)) := by
  set S := (weyl R (m + 1) (m + 1) le_rfl ν).map
    (LinearMap.mulLeft R (lpMinor R (r := m + 1) (n := m + 1) (m + 1) le_rfl le_rfl ^ c)) with hS
  have hstab : ∀ (a b : Fin (m + 1)) (k : ℕ) (x : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R), x ∈ S →
      rowDiv R a b k x ∈ S := by
    intro a b k x hx
    obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.mp hx
    simp only [LinearMap.mulLeft_apply]
    by_cases hab : a = b
    · subst hab
      rw [rowDiv_fullMinor_mul_self]
      refine Submodule.mem_map.mpr ⟨_, ?_, rfl⟩
      refine Submodule.sum_mem _ fun p _ => ?_
      rw [← nsmul_eq_mul]
      exact Submodule.smul_of_tower_mem _ _ (rowDiv_mem R le_rfl ν a a p.2 g hg)
    · rw [rowDiv_fullMinor_mul R a b hab]
      exact Submodule.mem_map.mpr ⟨_, rowDiv_mem R le_rfl ν a b k g hg, rfl⟩
  unfold weyl
  rw [Submodule.span_le]
  rintro _ ⟨w, rfl⟩
  induction w with
  | nil =>
    refine Submodule.mem_map.mpr ⟨hw R le_rfl ν, Submodule.subset_span ⟨[], rfl⟩, ?_⟩
    simp only [LinearMap.mulLeft_apply, applyWord, List.foldr_nil]
    rw [hw_shift, mul_comm]
  | cons x w ih =>
    exact hstab x.1 x.2.1 x.2.2 _ ih

theorem fullMinor_pow_mul_mem (R : Type) [CommRing R] {m : ℕ} (ν : Fin (m + 1) → ℕ) (c : ℕ)
    (g : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R) (hg : g ∈ weyl R (m + 1) (m + 1) le_rfl ν) :
    lpMinor R (r := m + 1) (n := m + 1) (m + 1) le_rfl le_rfl ^ c * g ∈
      weyl R (m + 1) (m + 1) le_rfl (fun s => ν s + c) := by
  set D := lpMinor R (r := m + 1) (n := m + 1) (m + 1) le_rfl le_rfl ^ c with hD
  set W' := weyl R (m + 1) (m + 1) le_rfl (fun s => ν s + c) with hW'
  have key : ∀ w : List (Fin (m + 1) × Fin (m + 1) × ℕ), D * applyWord R w (hw R le_rfl ν) ∈ W' := by
    intro w
    induction w with
    | nil =>
      simp only [applyWord, List.foldr_nil]
      rw [hD, mul_comm, ← hw_shift]
      exact Submodule.subset_span ⟨[], rfl⟩
    | cons x w ih =>
      obtain ⟨a, b, k⟩ := x
      show D * rowDiv R a b k (applyWord R w (hw R le_rfl ν)) ∈ W'
      set g := applyWord R w (hw R le_rfl ν)
      by_cases hab : a = b
      · subst hab
        induction k using Nat.strong_induction_on with
        | _ k ihk =>
          have h1 := rowDiv_fullMinor_mul_self R a k c g
          have hmem : ((0 : ℕ), k) ∈ Finset.HasAntidiagonal.antidiagonal k := by simp
          rw [← Finset.add_sum_erase _ _ hmem] at h1
          simp only [Nat.choose_zero_right, Nat.cast_one, one_mul] at h1
          have h2 : D * rowDiv R a a k g = rowDiv R a a k (D * g) -
              ∑ p ∈ (Finset.HasAntidiagonal.antidiagonal k).erase (0, k),
                D * (((c.choose p.1 : ℕ) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R) * rowDiv R a a p.2 g) := by
            rw [hD, h1, mul_add, Finset.mul_sum]
            ring
          rw [h2]
          refine Submodule.sub_mem _ (rowDiv_mem R le_rfl _ a a k _ ih) ?_
          refine Submodule.sum_mem _ fun p hp => ?_
          have hp2 : p.2 < k := by
            rw [Finset.mem_erase, Finset.HasAntidiagonal.mem_antidiagonal] at hp
            have hne : p.1 ≠ 0 := fun h => hp.1 (Prod.ext h (by simp; omega))
            omega
          rw [mul_left_comm, ← nsmul_eq_mul]
          exact Submodule.smul_of_tower_mem _ _ (ihk p.2 hp2)
      · rw [← rowDiv_fullMinor_mul R a b hab]
        exact rowDiv_mem R le_rfl _ a b k _ ih
  unfold weyl at hg
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    exact key w
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
  | smul t x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ t hx

theorem mem_weyl_shift_iff (N : ℕ) (μ : Fin N → ℕ) (c : ℕ) (f : MvPolynomial (Fin N × Fin N) ℤ) :
    f ∈ weyl ℤ N N le_rfl (fun s => μ s + c) ↔
      ∃ g ∈ weyl ℤ N N le_rfl μ, f = lpMinor ℤ (r := N) (n := N) N le_rfl le_rfl ^ c * g := by
  cases N with
  | zero =>
    have hμ : (fun s : Fin 0 => μ s + c) = μ := funext fun s => s.elim0
    rw [hμ]
    have h1 : lpMinor ℤ (r := 0) (n := 0) 0 le_rfl le_rfl = 1 := by unfold lpMinor; simp
    simp [h1]
  | succ m =>
    constructor
    · intro hf
      obtain ⟨g, hg, hgf⟩ := Submodule.mem_map.mp (weyl_shift_le ℤ μ c hf)
      exact ⟨g, hg, hgf.symm⟩
    · rintro ⟨g, hg, rfl⟩
      exact fullMinor_pow_mul_mem ℤ μ c g hg

theorem eval_fullMinor {K : Type} [CommRing K] (N : ℕ) (Y : Matrix (Fin N) (Fin N) K) :
    MvPolynomial.eval (fun k : Fin N × Fin N => Y k.1 k.2)
      (MvPolynomial.map (Int.castRingHom K) (lpMinor ℤ (r := N) (n := N) N le_rfl le_rfl)) = Y.det := by
  unfold lpMinor
  rw [RingHom.map_det, RingHom.map_det]
  congr 1
  ext i j
  simp [Fin.castLE_refl]

def polFunAdd (K : Type) [CommRing K] (T : Type) (N : ℕ) :
    MvPolynomial (T × Fin N × Fin N) K →+ ((T → Matrix (Fin N) (Fin N) K) → K) where
  toFun := polFun
  map_zero' := by funext y; simp [polFun]
  map_add' := by intro a b; funext y; simp [polFun]

def detMul (K : Type) [CommRing K] {T : Type} [Fintype T] (N : ℕ) (k : T → ℕ) :
    ((T → Matrix (Fin N) (Fin N) K) → K) →+ ((T → Matrix (Fin N) (Fin N) K) → K) :=
  AddMonoidHom.mulLeft (fun y => ∏ τ, (y τ).det ^ k τ)

theorem detMul_apply (K : Type) [CommRing K] {T : Type} [Fintype T] (N : ℕ) (k : T → ℕ)
    (F : (T → Matrix (Fin N) (Fin N) K) → K) (y : T → Matrix (Fin N) (Fin N) K) :
    detMul K N k F y = (∏ τ, (y τ).det ^ k τ) * F y := rfl

theorem delW_le_range (p : ℕ) [Fact p.Prime] (T : Type) [Fintype T] (N : ℕ) (ν : T → Fin N → ℕ) :
    DelW p T N ν ≤ (polFunAdd ℂ_[p] T N).range := by
  unfold DelW
  rw [AddSubgroup.closure_le]
  rintro F ⟨r, f, -, -, rfl⟩
  refine ⟨C r * ∏ τ, rename (fun k : Fin N × Fin N => (τ, k.1, k.2))
    (MvPolynomial.map (Int.castRingHom ℂ_[p]) (f τ)), ?_⟩
  funext y
  simp [polFunAdd, polFun, eval_rename, Function.comp_def]

theorem delW_le_comap (p : ℕ) [Fact p.Prime] (T : Type) [Fintype T] (N : ℕ) (ν : T → Fin N → ℕ) (k : T → ℕ) :
    DelW p T N ν ≤ (DelW p T N (fun τ r => ν τ r + k τ)).comap (detMul ℂ_[p] N k) := by
  unfold DelW
  rw [AddSubgroup.closure_le]
  rintro F ⟨r, f, hr, hf, rfl⟩
  apply AddSubgroup.subset_closure
  refine ⟨r, fun τ => lpMinor ℤ (r := N) (n := N) N le_rfl le_rfl ^ k τ * f τ, hr,
    fun τ => (mem_weyl_shift_iff N (ν τ) (k τ) _).2 ⟨f τ, hf τ, rfl⟩, ?_⟩
  funext y
  simp only [detMul_apply, map_mul, map_pow, eval_fullMinor,
    Finset.prod_mul_distrib]
  ring

theorem delW_shift_le_map (p : ℕ) [Fact p.Prime] (T : Type) [Fintype T] (N : ℕ) (ν : T → Fin N → ℕ) (k : T → ℕ) :
    DelW p T N (fun τ r => ν τ r + k τ) ≤
      (DelW p T N ν ⊓ (polFunAdd ℂ_[p] T N).range).map (detMul ℂ_[p] N k) := by
  conv_lhs => unfold DelW
  rw [AddSubgroup.closure_le]
  rintro F ⟨r, f, hr, hf, rfl⟩
  choose g hg hfg using fun τ => (mem_weyl_shift_iff N (ν τ) (k τ) (f τ)).1 (hf τ)
  have hgen : (fun y : T → Matrix (Fin N) (Fin N) ℂ_[p] => r * ∏ τ, MvPolynomial.eval
      (fun kk : Fin N × Fin N => y τ kk.1 kk.2) (MvPolynomial.map (Int.castRingHom ℂ_[p]) (g τ))) ∈ DelW p T N ν :=
    AddSubgroup.subset_closure ⟨r, g, hr, hg, rfl⟩
  refine AddSubgroup.mem_map.mpr ⟨_, AddSubgroup.mem_inf.mpr ⟨hgen, delW_le_range p T N ν hgen⟩, ?_⟩
  funext y
  simp only [detMul_apply, hfg, map_mul, map_pow, eval_fullMinor,
    Finset.prod_mul_distrib]
  ring

def detPoly (K : Type) [CommRing K] {T : Type} [Fintype T] (N : ℕ) (k : T → ℕ) : MvPolynomial (T × Fin N × Fin N) K :=
  ∏ τ, (Matrix.of fun a b : Fin N => (X (τ, a, b) : MvPolynomial (T × Fin N × Fin N) K)).det ^ k τ

theorem polFun_detPoly (K : Type) [CommRing K] {T : Type} [Fintype T] (N : ℕ) (k : T → ℕ)
    (y : T → Matrix (Fin N) (Fin N) K) : polFun (detPoly K N k) y = ∏ τ, (y τ).det ^ k τ := by
  unfold polFun detPoly
  rw [map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_pow, RingHom.map_det]
  congr 2
  ext a b
  simp

theorem detPoly_ne_zero (K : Type) [CommRing K] [Nontrivial K] {T : Type} [Fintype T] (N : ℕ) (k : T → ℕ) :
    detPoly K N k ≠ 0 := by
  intro h
  have := polFun_detPoly K N k (fun _ => 1)
  rw [h] at this
  simp [polFun] at this

theorem detPow_mul_mem_delW_iff : ∀ (p : ℕ) [Fact p.Prime] (T : Type) [Fintype T] (N : ℕ) (ν : T → Fin N → ℕ)
    (k : T → ℕ) (Φ : MvPolynomial (T × Fin N × Fin N) ℂ_[p]),
    ((fun y => (∏ τ, (y τ).det ^ k τ) * polFun Φ y) ∈ WeylLatticeDuality.DelW p T N (fun τ r => ν τ r + k τ) ↔
      polFun Φ ∈ WeylLatticeDuality.DelW p T N ν) := by
  intro p _ T _ N ν k Φ
  constructor
  · intro h
    obtain ⟨G, hGm, hGe⟩ := AddSubgroup.mem_map.mp (delW_shift_le_map p T N ν k h)
    obtain ⟨hG, hR⟩ := AddSubgroup.mem_inf.mp hGm
    obtain ⟨Ψ, rfl⟩ := AddMonoidHom.mem_range.mp hR
    haveI : Infinite ℂ_[p] := CharZero.infinite _
    have hpoly : detPoly ℂ_[p] N k * Ψ = detPoly ℂ_[p] N k * Φ := by
      apply MvPolynomial.funext
      intro x
      let y : T → Matrix (Fin N) (Fin N) ℂ_[p] := fun τ a b => x (τ, a, b)
      have hy : (∏ τ, (y τ).det ^ k τ) * polFun Ψ y = (∏ τ, (y τ).det ^ k τ) * polFun Φ y := congrFun hGe y
      have h1 := polFun_detPoly ℂ_[p] N k y
      have hm : ∀ A B : MvPolynomial (T × Fin N × Fin N) ℂ_[p], polFun (A * B) y = polFun A y * polFun B y :=
        fun A B => by simp [polFun]
      show polFun (detPoly ℂ_[p] N k * Ψ) y = polFun (detPoly ℂ_[p] N k * Φ) y
      rw [hm, hm, h1, hy]
    have hΨ : Ψ = Φ := mul_left_cancel₀ (detPoly_ne_zero ℂ_[p] N k) hpoly
    subst hΨ
    exact hG
  · intro h
    exact AddSubgroup.mem_comap.mp (delW_le_comap p T N ν k h)

end GlobalTheory.DetShiftWeyl

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetPowerProductMulMemDelWShiftIffStatement
open GlobalTheory.IntegralityCompare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.detPowerProduct_mul_mem_delW_shift_iff : ∀ (p : ℕ) [Fact p.Prime] (T : Type) [Fintype T] (N : ℕ) (ν : T → Fin N → ℕ) (k : T → ℕ)
    (Φ : MvPolynomial (T × Fin N × Fin N) ℂ_[p]),
    ((fun y => (∏ τ, (y τ).det ^ k τ) * polFun Φ y) ∈ WeylLatticeDuality.DelW p T N (fun τ r => ν τ r + k τ) ↔
      polFun Φ ∈ WeylLatticeDuality.DelW p T N ν) := by
  first | exact @GlobalTheory.DetShiftWeyl.detPow_mul_mem_delW_iff | exact GlobalTheory.DetShiftWeyl.detPow_mul_mem_delW_iff | (intros; apply GlobalTheory.DetShiftWeyl.detPow_mul_mem_delW_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeIffIntegralWeylCoordinates
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IntegralityCompare

noncomputable section

namespace GlobalTheory.IntegralityCompare

theorem lift_ratSpan (D : D7) {n : ℕ} (lam : D.what₂.Tau → DomWeight n) (P0 : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ) :
    P0 ∈ Formalism.L2.Forms.RatSpan D lam → ∃ R0 : MvPolynomial (D.what₂.Tau × Fin n × Fin n) D.what₂.LL,
      MvPolynomial.map D.what₂.embLL R0 = P0 := by
  intro h
  have hle : Formalism.L2.Forms.RatSpan D lam ≤ (MvPolynomial.map D.what₂.embLL).toAddMonoidHom.range := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro p ⟨r, f, -, rfl⟩
    refine ⟨MvPolynomial.C r * Formalism.L2.Forms.ten (fun τ => MvPolynomial.map (Int.castRingHom D.what₂.LL) (f τ)), ?_⟩
    have hc : (D.what₂.embLL).comp (Int.castRingHom D.what₂.LL) = Int.castRingHom ℂ := RingHom.ext_int _ _
    simp [Formalism.L2.Forms.ten, map_prod, MvPolynomial.map_map, MvPolynomial.smul_eq_C_mul, MvPolynomial.map_rename, hc]
  obtain ⟨R0, hR0⟩ := hle h
  exact ⟨R0, hR0⟩

theorem lattice_iff_weyl : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z)) (Bs : PlaceMatrixFamily (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → BasOk Pl O Bs → (∀ u a w, LevFree Y u a w → ∀ i, i ≤ B.R.m → ∀ c τ j k, ∃ x : (I.rec7 l Z).what₂.LL, Bs u a w i c τ j k = Pl.iL w x) → ∀ (u : B.Word) (μ : I.ι) (w : (I.rec7 l Z).what₂.places.Pl), LevFree Y u μ w → ∀ (i : ℕ) (hi : i < B.R.m) (eY : (I.chain l u μ).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi.le), I.IdY l Z u μ i hi.le eY → ∀ (c : (I.stp u μ i).Cl) (f : (I.chain l u μ).Y i → ℂ), (∃ P ∈ Formalism.L2.Forms.RatSpan (I.rec7 l Z) ((I.fm l u μ).lam i), ∀ z, f z = fnOf (gramC (gramN (I.rec7 l Z) i hi.le) (embT (I.rec7 l Z))) (shiftOf (lamTG (I.fm l u μ) i)) 1 P (eY z)) → ∀ Bm : GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E, Formalism.L2.Forms.IsLocBasis ((I.rec7 l Z).what₂.places.resChar w) (((I.stp u μ i).rep c).1.1.deco.1.N : Set (Sp B.fields.E (B.R.N i))) Bm →  ∀ v : ValQ O u μ i, evC O u μ i v = f → ((∃ P ∈ Formalism.L2.Forms.IntSpan (I.rec7 l Z) w ((I.fm l u μ).lam i), ∀ z, f z = fnOf (gramC (gramN (I.rec7 l Z) i hi.le) (embT (I.rec7 l Z))) (shiftOf (lamTG (I.fm l u μ) i)) (atInf (embT (I.rec7 l Z)) ((Bm⁻¹ : GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E) : Matrix (Fin ((I.rec7 l Z).R.N i)) (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E)) P (eY z)) ↔ srcFun Pl Bs u μ w i c (secC O u μ i v) ∈ WeylLatticeDuality.DelW ((I.rec7 l Z).what₂.places.resChar w) (I.rec7 l Z).what₂.Tau ((I.rec7 l Z).R.N i) (nuT (I.rec7 l Z) u i)) := by
  intro B X I hOk hPins l Z Y O Pl Bs hQp hStd hBas hEnt u μ w hLev i hi eY hIdY c f hRat Bm hBm v hv
  obtain ⟨P0, hP0, hf⟩ := hRat
  have hL : ∀ τ, GL3Columns.BasR (I.rec7 l Z) (Pl.lam w) τ (((I.stp u μ i).rep c).1.1.deco.1.N) (Bs u μ w i c τ) := by
    intro τ
    have h := hBas u μ w i hi.le c τ
    have e := hStd.lat u μ i c
    exact (congrArg (fun L => GL3Columns.BasR (I.rec7 l Z) (Pl.lam w) τ L (Bs u μ w i c τ)) e).mp h
  choose g hg1 hg2 hg3 using fun τ => GlobalTheory.T.localBasis_change_integral_unit_det _ (Pl.lam w) τ _ Bm _ (hL τ) hBm
  obtain ⟨k, hk1, hk⟩ := GlobalTheory.T.chainStep_weight_arithmetic I hOk hPins l Z u μ i hi
  obtain ⟨R0, hR0⟩ := lift_ratSpan _ _ P0 hP0
  have hsrc := GlobalTheory.T.twistedSourceValue_read_in_changed_bases I hOk hPins l Z Y O Pl Bs hQp hStd hBas hEnt u μ w hLev i hi eY hIdY c f P0 hf R0 hR0 k hk1 Bm g hg3 v hv
  set R := twSubK (Formalism.L2.G.Cmp.tEL (I.rec7 l Z)) Bm (shiftOf (lamTG (I.fm l u μ) i)) R0 with hRdef
  have hR : MvPolynomial.map (I.rec7 l Z).what₂.embLL R = twSub (embT (I.rec7 l Z)) Bm (shiftOf (lamTG (I.fm l u μ) i)) P0 := by
    have h := map_twSubK (Formalism.L2.G.Cmp.tEL (I.rec7 l Z)) Bm (shiftOf (lamTG (I.fm l u μ) i)) R0 (I.rec7 l Z).what₂.embLL
    have h' : MvPolynomial.map (I.rec7 l Z).what₂.embLL R = twSub (fun τ => ((I.rec7 l Z).what₂.embLL).comp (Formalism.L2.G.Cmp.tEL (I.rec7 l Z) τ)) Bm (shiftOf (lamTG (I.fm l u μ) i)) P0 :=
      h.trans (congrArg (twSub _ Bm _) hR0)
    have he : (fun τ => ((I.rec7 l Z).what₂.embLL).comp (Formalism.L2.G.Cmp.tEL (I.rec7 l Z) τ)) = embT (I.rec7 l Z) :=
      funext fun τ => RingHom.ext fun x => Formalism.L2.G.Cmp.tEL_emb _ τ x
    rw [he] at h'
    exact h'
  set c0 := ∏ τ, (g τ).det ^ (-((I.rec7 l Z).chTw u μ).sSharp i τ) with hc0def
  have hc0 : ‖c0‖ = 1 := by
    rw [hc0def, norm_prod]
    exact Finset.prod_eq_one fun τ _ => by rw [norm_zpow, hg2 τ, _root_.one_zpow]
  have hRat' : MvPolynomial.map (I.rec7 l Z).what₂.embLL R ∈ Formalism.L2.Forms.RatSpan (I.rec7 l Z) ((I.fm l u μ).lam i) := by
    rw [hR]; exact GlobalTheory.T.twistedEmbeddingMatrixSubstitution_mem_ratSpan _ _ Bm _ P0 hP0
  have hν : nuT (I.rec7 l Z) u i = fun τ r => (((I.fm l u μ).lam i τ).natW r) + k τ :=
    funext fun τ => funext fun r => hk τ r
  refine (GlobalTheory.T.automorphicFormFn_inv_iff_twistedSubstitution_mem (embT (I.rec7 l Z)) Bm _ _ P0 _ eY f hf).trans ?_
  rw [← hR]
  refine (GlobalTheory.T.integralSpan_iff_padic_weylDualLattice _ Pl w _ R hRat').trans ?_
  rw [hsrc, hν]
  refine Iff.trans ?_ (GlobalTheory.T.weyl_lattice_dual_invariant_unit _ _ _ _ g c0 (fun y => (∏ τ, (y τ).det ^ k τ) * polFun (MvPolynomial.map (Pl.iL w) R) y) hc0 hg1 hg2).symm
  exact (GlobalTheory.T.detPowerProduct_mul_mem_delW_shift_iff _ _ _ _ k _).symm

end GlobalTheory.IntegralityCompare

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeIffIntegralWeylCoordinatesStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_iff_integralWeyl_coordinates : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z)) (Bs : PlaceMatrixFamily (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → BasOk Pl O Bs → (∀ u a w, LevFree Y u a w → ∀ i, i ≤ B.R.m → ∀ c τ j k, ∃ x : (I.rec7 l Z).what₂.LL, Bs u a w i c τ j k = Pl.iL w x) → ∀ (u : B.Word) (μ : I.ι) (w : (I.rec7 l Z).what₂.places.Pl), LevFree Y u μ w → ∀ (i : ℕ) (hi : i < B.R.m) (eY : (I.chain l u μ).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi.le), I.IdY l Z u μ i hi.le eY → ∀ (c : (I.stp u μ i).Cl) (f : (I.chain l u μ).Y i → ℂ), (∃ P ∈ Formalism.L2.Forms.RatSpan (I.rec7 l Z) ((I.fm l u μ).lam i), ∀ z, f z = fnOf (gramC (gramN (I.rec7 l Z) i hi.le) (embT (I.rec7 l Z))) (shiftOf (lamTG (I.fm l u μ) i)) 1 P (eY z)) → ∀ Bm : GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E, Formalism.L2.Forms.IsLocBasis ((I.rec7 l Z).what₂.places.resChar w) (((I.stp u μ i).rep c).1.1.deco.1.N : Set (Sp B.fields.E (B.R.N i))) Bm →  ∀ v : ValQ O u μ i, evC O u μ i v = f → ((∃ P ∈ Formalism.L2.Forms.IntSpan (I.rec7 l Z) w ((I.fm l u μ).lam i), ∀ z, f z = fnOf (gramC (gramN (I.rec7 l Z) i hi.le) (embT (I.rec7 l Z))) (shiftOf (lamTG (I.fm l u μ) i)) (atInf (embT (I.rec7 l Z)) ((Bm⁻¹ : GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E) : Matrix (Fin ((I.rec7 l Z).R.N i)) (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E)) P (eY z)) ↔ srcFun Pl Bs u μ w i c (secC O u μ i v) ∈ WeylLatticeDuality.DelW ((I.rec7 l Z).what₂.places.resChar w) (I.rec7 l Z).what₂.Tau ((I.rec7 l Z).R.N i) (nuT (I.rec7 l Z) u i)) := by
  first | exact @GlobalTheory.IntegralityCompare.lattice_iff_weyl | exact GlobalTheory.IntegralityCompare.lattice_iff_weyl | (intros; apply GlobalTheory.IntegralityCompare.lattice_iff_weyl <;> assumption)
end
