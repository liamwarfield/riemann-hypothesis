module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitsOfModuliPointHaveIsomorphicProportionalLat

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.WitSys
noncomputable section

open NumberField
open GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo
open scoped TensorProduct

namespace UpperTheory.Gal.W2.Wit

variable {p : ℕ} [Fact p.Prime]

theorem actQ_tmul {D : Datum p} (b : D.O) (q : ℚ) (x : D.La) : actQ D b (q ⊗ₜ x) = q ⊗ₜ (b • x) := by
  simp only [actQ, LinearMap.baseChange_tmul]; rfl

theorem actQ_one (D : Datum p) (w : VQ D) : actQ D 1 w = w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul q x => rw [actQ_tmul, one_smul]
  | add u v hu hv => rw [map_add (f := _), hu, hv]

theorem actQ_mul (D : Datum p) (a b : D.O) (w : VQ D) : actQ D (a * b) w = actQ D a (actQ D b w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul q x => rw [actQ_tmul, actQ_tmul, actQ_tmul, mul_smul]
  | add u v hu hv => rw [map_add (f := _), hu, hv, map_add (f := _), map_add (f := _)]

theorem actQ_add (D : Datum p) (a b : D.O) (w : VQ D) : actQ D (a + b) w = actQ D a w + actQ D b w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul q x => rw [actQ_tmul, actQ_tmul, actQ_tmul, add_smul, TensorProduct.tmul_add]
  | add u v hu hv => rw [map_add (f := _), hu, hv, map_add (f := _), map_add (f := _)]; abel

theorem actQ_zero (D : Datum p) (w : VQ D) : actQ D 0 w = 0 := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul q x => rw [actQ_tmul, zero_smul, TensorProduct.tmul_zero]
  | add u v hu hv => rw [map_add (f := _), hu, hv, add_zero]

structure Sys (D : Datum p) where
  T : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D)
  S : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D)
  ST : S * T = 1
  comm : ∀ c : D.O, T * (actQ D c).baseChange (AfP p) = (actQ D c).baseChange (AfP p) * T
  B : LinearMap.BilinForm ℚ (VQ D)
  alt : ∀ u, B u u = 0
  nondeg : ∀ u, (∀ w, B u w = 0) → u = 0
  adj : ∀ (c : D.O) u w, B (actQ D c u) w = B u (actQ D (D.inv c) w)
  M : AddSubgroup (VQ D)
  hM : UpperTheory.Gal.W2.IsPLat D M
  s : ℚ
  s_pos : 0 < s
  perf : ∀ w, w ∈ M ↔ ∀ u ∈ M, (s * B w u).den.Coprime p
  ε : (AfP p)ˣ
  ε_int : IsIntAf (ε : AfP p)
  ε_inv : IsIntAf ((ε⁻¹ : (AfP p)ˣ) : AfP p)
  form : ∀ u w, algebraMap ℚ (AfP p) (s * B u w) =
    (ε : AfP p) * (D.EF.baseChange ℚ).baseChange (AfP p) (T ((1 : AfP p) ⊗ₜ u)) (T ((1 : AfP p) ⊗ₜ w))
  dense : ∀ n : ℕ, 0 < n → ∀ z, ∃ w, ∃ e ∈ LaHat D, z = T ((1 : AfP p) ⊗ₜ w) + n • e

namespace Sys

variable {D : Datum p} (X : Sys D)

def r : VQ D →ₗ[ℚ] AfP p ⊗[ℚ] VQ D :=
  (X.T.restrictScalars ℚ) ∘ₗ (TensorProduct.mk ℚ (AfP p) (VQ D) 1)

theorem r_apply (w : VQ D) : X.r w = X.T ((1 : AfP p) ⊗ₜ w) := rfl

theorem r_act (c : D.O) (w : VQ D) : X.r (actQ D c w) = (actQ D c).baseChange (AfP p) (X.r w) := by
  rw [r_apply, r_apply]
  have h := LinearMap.congr_fun (X.comm c) ((1 : AfP p) ⊗ₜ w)
  rw [Module.End.mul_apply, Module.End.mul_apply, LinearMap.baseChange_tmul] at h
  exact h

def lat : AddSubgroup (VQ D) where
  carrier := {w | w ∈ X.M ∧ X.r w ∈ LaHat D}
  zero_mem' := ⟨zero_mem _, by rw [map_zero]; exact zero_mem _⟩
  add_mem' := fun h h' => ⟨add_mem h.1 h'.1, by rw [map_add]; exact add_mem h.2 h'.2⟩
  neg_mem' := fun h => ⟨neg_mem h.1, by rw [map_neg]; exact neg_mem h.2⟩

theorem mem_lat {w : VQ D} : w ∈ X.lat ↔ w ∈ X.M ∧ X.r w ∈ LaHat D := Iff.rfl

theorem act_mem (c : D.O) {w : VQ D} (hw : w ∈ X.lat) : actQ D c w ∈ X.lat :=
  ⟨X.hM.1 c w hw.1, by rw [r_act]; exact GlobalTheory.AdelicSim.bc_mem D c hw.2⟩

instance : Module D.O X.lat where
  smul c w := ⟨actQ D c w.1, X.act_mem c w.2⟩
  one_smul w := Subtype.ext (actQ_one D w.1)
  mul_smul a b w := Subtype.ext (actQ_mul D a b w.1)
  smul_zero c := Subtype.ext (map_zero (actQ D c))
  smul_add c u v := Subtype.ext (map_add (actQ D c) u.1 v.1)
  add_smul a b w := Subtype.ext (actQ_add D a b w.1)
  zero_smul w := Subtype.ext (actQ_zero D w.1)

theorem coe_smul (c : D.O) (w : X.lat) : ((c • w : X.lat) : VQ D) = actQ D c w := rfl

end Sys

end UpperTheory.Gal.W2.Wit
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PRdForm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem mul_unit_eq_algebraMap_mul {S A : Type*} [Ring S] [CommRing A] [Algebra A S] (xs : S) (x : Sˣ) (b bi : S)
    (t : A) (hb : bi * b = 1) (hx : (x : S) * b * xs = algebraMap A S t) :
    xs * (x : S) = algebraMap A S t * bi := by
  have hc : ∀ y : S, algebraMap A S t * y = y * algebraMap A S t := fun y => Algebra.commutes t y
  have h1 : xs = bi * ((↑x⁻¹ : S) * algebraMap A S t) := by
    rw [← hx, ← _root_.mul_assoc (↑x⁻¹ : S), ← _root_.mul_assoc (↑x⁻¹ : S), Units.inv_mul,
      _root_.one_mul, ← _root_.mul_assoc, hb, _root_.one_mul]
  rw [h1, _root_.mul_assoc, _root_.mul_assoc, hc, ← _root_.mul_assoc (↑x⁻¹ : S), Units.inv_mul,
    _root_.one_mul]
  exact (hc bi).symm

theorem UpperTheory.Gal.W2.rdForm_of :
    UpperTheory.Gal.W2.RdForm := by
  intro p _ D G L B h₁
  obtain ⟨t, ht⟩ := B.trivAf.choose_spec
  have hx : (↑(trivX B) : AfP p ⊗[ℚ] G.C) * inC G (AfP p) ↑B.β *
      MulOpposite.unop ((starT G.star (AfP p)) ↑(trivX B)) = algebraMap (AfP p) _ ↑t := ht
  have key := mul_unit_eq_algebraMap_mul (A := AfP p) _ (trivX B) _ (inC G (AfP p) ↑B.β⁻¹) _
    (by rw [← map_mul, Units.inv_mul, map_one]) hx
  have hsh : sh G (↑B.β⁻¹ : G.C) = ↑B.β⁻¹ := by
    have h : sh G (↑B.β⁻¹ : G.C) * ↑B.β = 1 := by
      rw [← B.sym]
      simp only [sh]
      rw [← MulOpposite.unop_mul, ← map_mul, Units.mul_inv, map_one, MulOpposite.unop_one]
    exact Units.mul_eq_one_iff_eq_inv.mp h
  refine ⟨(h₁⁻¹).1.2 * t, fun u w => ?_⟩
  unfold rd
  rw [actG_form_eq_sim, adj_actOn_afP, ← Module.End.mul_apply, ← map_mul, key, map_mul,
    AlgHom.commutes, Module.End.mul_apply, Module.algebraMap_end_apply]
  simp only [inC, AlgHom.coe_toRingHom, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply]
  rw [actOn_tmul_tmul', TensorProduct.smul_tmul', LinearMap.BilinForm.baseChange_tmul, formB,
    L.adj, hsh, Units.val_mul]
  simp only [smul_eq_mul]
  rw [Algebra.smul_def]
  ring
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PRdDense
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem powerSeries_expansion_image_dense_with_denominator {p : ℕ} [Fact p.Prime] (D : Datum p) (N : ℕ) (hN : 0 < N) (hNp : N.Coprime p)
    (z : AfP p ⊗[ℚ] VQ D) : ∃ (w : VQ D) (e : AfP p ⊗[ℚ] VQ D), e ∈ LaHat D ∧
      z = (1 : AfP p) ⊗ₜ[ℚ] w + N • e := by
  obtain ⟨t, ht0, htc, ht⟩ := DenEnd.exists_coprime_nsmul_mem D z
  obtain ⟨x, e, he, hx⟩ := exists_inAf_add_nsmul_of_mem_laHat p D (t * N) (Nat.mul_pos ht0 hN)
    (Nat.Coprime.mul_left htc hNp) (t • z) ht
  have ht' : (t : ℚ) ≠ 0 := by exact_mod_cast ht0.ne'
  refine ⟨(t : ℚ)⁻¹ • ((1 : ℚ) ⊗ₜ[ℤ] x), e, he, ?_⟩
  have h1 : t • ((1 : AfP p) ⊗ₜ[ℚ] ((t : ℚ)⁻¹ • ((1 : ℚ) ⊗ₜ[ℤ] x))) = inAf D x := by
    rw [inAf, ← Nat.cast_smul_eq_nsmul ℚ, ← TensorProduct.tmul_smul, smul_smul, mul_inv_cancel₀ ht', one_smul]
  have h2 : t • z = t • ((1 : AfP p) ⊗ₜ[ℚ] ((t : ℚ)⁻¹ • ((1 : ℚ) ⊗ₜ[ℤ] x)) + N • e) := by
    rw [hx, smul_add, h1, smul_smul]
  rw [← Nat.cast_smul_eq_nsmul ℚ t, ← Nat.cast_smul_eq_nsmul ℚ t] at h2
  exact smul_right_injective _ ht' h2

theorem UpperTheory.Gal.W2.rdDense_of :
    UpperTheory.Gal.W2.RdDense := by
  intro p _ D G L x h₁ n hn z
  let T : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D) :=
    L.actG h₁⁻¹ * actOn L.rep (AfP p) (x : AfP p ⊗[ℚ] G.C)
  let S : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D) :=
    actOn L.rep (AfP p) ((x⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) * L.actG h₁
  have hTS : T * S = 1 := by
    have e1 : actOn L.rep (AfP p) (x : AfP p ⊗[ℚ] G.C) *
        actOn L.rep (AfP p) ((x⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have e2 : L.actG h₁⁻¹ * L.actG h₁ = 1 := by
      rw [← map_mul, inv_mul_cancel, map_one]
    change (L.actG h₁⁻¹ * actOn L.rep (AfP p) (x : AfP p ⊗[ℚ] G.C)) *
      (actOn L.rep (AfP p) ((x⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) * L.actG h₁) = 1
    rw [_root_.mul_assoc, ← _root_.mul_assoc (actOn L.rep (AfP p) (x : AfP p ⊗[ℚ] G.C)), e1, _root_.one_mul, e2]
  obtain ⟨m, hm0, hmc, hm⟩ := DenEnd.exists_coprime_nsmul_map_mem p D T
  obtain ⟨k, n', hn', hnn⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' p (Fact.out : p.Prime).ne_one
  have hn0 : 0 < n' := Nat.pos_of_ne_zero fun h => hn' (h ▸ dvd_zero p)
  have hnc : n'.Coprime p := ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hn').symm
  obtain ⟨w, e, he, hz⟩ := powerSeries_expansion_image_dense_with_denominator D (n' * m) (Nat.mul_pos hn0 hm0) (Nat.Coprime.mul_left hnc hmc) (S z)
  have hint : IsIntAf (algebraMap ℚ (AfP p) ((p : ℚ)⁻¹ ^ k)) := fun u => by
    rw [map_pow, map_pow]; exact pow_mem (DenEnd.isIntAf_inv u) k
  have hz2 : z = T (S z) := by
    rw [← Module.End.mul_apply, hTS]; rfl
  have hr : rd L x h₁ w = T ((1 : AfP p) ⊗ₜ[ℚ] w) := rfl
  have hp : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  refine ⟨w, algebraMap ℚ (AfP p) ((p : ℚ)⁻¹ ^ k) • (m • T e), DenEnd.smul_mem D hint (hm e he), ?_⟩
  rw [hr, hz2, hz, map_add (f := _), map_nsmul]
  congr 1
  rw [algebraMap_smul, hnn]
  simp only [← Nat.cast_smul_eq_nsmul ℚ, smul_smul]
  congr 1
  have hpk : (p : ℚ) ^ k * ((p : ℚ)⁻¹) ^ k = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hp, one_pow]
  push_cast
  linear_combination (-((n' : ℚ) * m)) * hpk
end
