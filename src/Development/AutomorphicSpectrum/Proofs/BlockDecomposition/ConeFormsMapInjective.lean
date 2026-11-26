module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InOpenOfThickeningMorphism
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeFormsMapInjective
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KaehlerFreeConeRing
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KaehlerFreeConeRing
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.SurjectionOntoH4.FreeOm
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

theorem free_of_formallyEtale (K A B : Type) [CommRing K] [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
    [Algebra A B] [IsScalarTower K A B] [Algebra.FormallyEtale A B] [Module.Free A Ω[A⁄K]] :
    Module.Free B Ω[B⁄K] :=
  (KaehlerDifferential.isBaseChange_of_formallyEtale K A B).free

theorem free_of_bijective {K A B : Type} [CommRing K] [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
    (φ : A →ₐ[K] B) (hφ : Function.Bijective φ) [Module.Free A Ω[A⁄K]] : Module.Free B Ω[B⁄K] := by
  letI : Algebra A B := φ.toRingHom.toAlgebra
  haveI : IsScalarTower K A B := IsScalarTower.of_algHom φ
  haveI : Algebra.FormallyEtale A B :=
    Algebra.FormallyEtale.of_equiv (AlgEquiv.ofBijective (Algebra.ofId A B) hφ)
  exact free_of_formallyEtale K A B

variable {K : Type} [Field K] {n d : ℕ}

theorem free_Bp : Module.Free (Bp K n d) Ω[Bp K n d⁄K] :=
  Module.Free.of_basis (KaehlerDifferential.mvPolynomialBasis K (E n d))

def cS (k : Fin d) (S : Finset (Fin d)) : Gam n d := ∑ j ∈ S, ratE k j

theorem ratE_inl (k j : Fin d) (l : Fin n) : (ratE k j : Gam n d) (Sum.inl l) = 0 := by
  simp [ratE, oneE]

theorem ratE_inr (k j j' : Fin d) :
    (ratE k j : Gam n d) (Sum.inr j') = (if j' = j then 1 else 0) - (if j' = k then 1 else 0) := by
  simp [ratE, oneE, Pi.single_apply]

theorem cS_inl (k : Fin d) (S : Finset (Fin d)) (l : Fin n) : (cS k S : Gam n d) (Sum.inl l) = 0 := by
  simp [cS, Finset.sum_apply, ratE_inl]

theorem cS_inr (k : Fin d) (S : Finset (Fin d)) {j : Fin d} (hj : j ≠ k) :
    (cS k S : Gam n d) (Sum.inr j) = if j ∈ S then 1 else 0 := by
  simp [cS, Finset.sum_apply, ratE_inr, hj]

theorem tdeg_cS (k : Fin d) (S : Finset (Fin d)) : tdeg (cS k S : Gam n d) = 0 := by
  unfold cS tdeg
  simp only [Finset.sum_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun j _ => ?_
  exact ChartBij.tdeg_ratE k j

theorem cS_mem (k : Fin d) (S : Finset (Fin d)) : (cS k S : Gam n d) ∈ (cone {k} : AddSubmonoid (Gam n d)) :=
  AddSubmonoid.sum_mem _ fun j _ => ratE_mem (Finset.mem_singleton_self k) j

theorem neg_cS_mem {k : Fin d} {S : Finset (Fin d)} (hk : k ∈ S) :
    -(cS k S : Gam n d) ∈ (cone S : AddSubmonoid (Gam n d)) := by
  refine ⟨fun l => by simp [cS_inl], fun j hj => ?_, ?_⟩
  · have hne : j ≠ k := fun h => hj (h ▸ hk)
    simp [cS_inr k S hne, hj]
  · have h := tdeg_add (cS k S : Gam n d) (-cS k S)
    rw [add_neg_cancel, tdeg_cS] at h
    have h0 : tdeg (0 : Gam n d) = 0 := by simp [tdeg]
    rw [h0] at h
    linarith

theorem exists_add_nsmul_mem {k : Fin d} {S : Finset (Fin d)} (hk : k ∈ S) (g : Gam n d)
    (hg : g ∈ (cone S : AddSubmonoid (Gam n d))) :
    ∃ N : ℕ, g + N • (cS k S : Gam n d) ∈ (cone {k} : AddSubmonoid (Gam n d)) := by
  refine ⟨∑ j, (g (Sum.inr j)).natAbs, fun l => ?_, fun j hj => ?_, ?_⟩
  · simpa [cS_inl] using hg.1 l
  · have hne : j ≠ k := by simpa using hj
    have hle : (g (Sum.inr j)).natAbs ≤ ∑ j, (g (Sum.inr j)).natAbs :=
      Finset.single_le_sum (f := fun j => (g (Sum.inr j)).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    simp only [Pi.add_apply, Pi.smul_apply, cS_inr k S hne]
    by_cases hS : j ∈ S
    · simp only [hS, if_true, nsmul_eq_mul, mul_one]
      omega
    · simpa [hS] using hg.2.1 j hS
  · rw [tdeg_add]
    have h : tdeg ((∑ j, (g (Sum.inr j)).natAbs) • (cS k S : Gam n d)) = 0 := by
      have hs : ∀ N : ℕ, tdeg (N • (cS k S : Gam n d)) = 0 := fun N => by
        induction N with
        | zero => simp [tdeg]
        | succ N ih => rw [succ_nsmul, tdeg_add, ih, tdeg_cS, add_zero]
      exact hs _
    rw [h, add_zero]
    exact hg.2.2

theorem free_singleton (k : Fin d) : Module.Free (R0 K n d {k}) Ω[R0 K n d {k}⁄K] := by
  haveI : Module.Free (Bp K n d) Ω[Bp K n d⁄K] := free_Bp
  exact free_of_bijective _ (ChartBij.chart_bijective (K := K) (n := n) k)

theorem free_of_mem {k : Fin d} {S : Finset (Fin d)} (hk : k ∈ S) :
    Module.Free (R0 K n d S) Ω[R0 K n d S⁄K] := by
  have hle : (cone {k} : AddSubmonoid (Gam n d)) ≤ cone S :=
    cone_mono (Finset.singleton_subset_iff.2 hk)
  letI : Algebra (R0 K n d {k}) (R0 K n d S) := (incl (K := K) hle).toRingHom.toAlgebra
  haveI : IsScalarTower K (R0 K n d {k}) (R0 K n d S) := IsScalarTower.of_algHom (incl (K := K) hle)
  haveI : IsLocalization.Away (mon K (cS k S) (cS_mem k S)) (R0 K n d S) :=
    Away.isLocalization_away hle (cS k S) (cS_mem k S) (neg_cS_mem hk) fun g hg => exists_add_nsmul_mem hk g hg
  haveI : Algebra.FormallyEtale (R0 K n d {k}) (R0 K n d S) :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers (mon K (cS k S) (cS_mem k S)))
  haveI : Module.Free (R0 K n d {k}) Ω[R0 K n d {k}⁄K] := free_singleton k
  exact free_of_formallyEtale K (R0 K n d {k}) (R0 K n d S)

theorem free_om : ∀ {K : Type} [Field K] {n d : ℕ} (S : Finset (Fin d)),
    Module.Free (R0 K n d S) Ω[R0 K n d S⁄K] := by
  intro K _ n d S
  rcases S.eq_empty_or_nonempty with rfl | ⟨k, hk⟩
  · haveI : Module.Free (Bp K n d) Ω[Bp K n d⁄K] := free_Bp
    exact free_of_bijective _ (PolyBij.poly_bijective (K := K) (n := n) (d := d))
  · exact free_of_mem hk

end GlobalTheory.CompanionTheory.SurjectionOntoH4.FreeOm
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KaehlerFreeConeRingStatement
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kaehler_free_cone_ring : ∀ {K : Type} [Field K] {n d : ℕ} (S : Finset (Fin d)), Module.Free (R0 K n d S) Ω[R0 K n d S⁄K] := by
  first | exact @GlobalTheory.CompanionTheory.SurjectionOntoH4.FreeOm.free_om | exact GlobalTheory.CompanionTheory.SurjectionOntoH4.FreeOm.free_om | (intros; apply GlobalTheory.CompanionTheory.SurjectionOntoH4.FreeOm.free_om <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeFormsMapInjective
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.SurjectionOntoH4.OmlInj
open scoped TensorProduct
open GlobalTheory.TopForm

def allE (n d : ℕ) : Gam n d := ∑ e, oneE e

theorem allE_apply {n d : ℕ} (e : E n d) : allE n d e = 1 := by
  classical
  simp [allE, oneE, Finset.sum_apply, Pi.single_apply]

theorem allE_mem {n d : ℕ} (S : Finset (Fin d)) : allE n d ∈ (cone S : AddSubmonoid (Gam n d)) :=
  sum_mem fun e _ => oneE_mem S e

theorem exists_add_nsmul_mem {n d : ℕ} (S : Finset (Fin d)) (g : Gam n d) :
    ∃ N : ℕ, g + N • allE n d ∈ (cone S : AddSubmonoid (Gam n d)) := by
  refine ⟨(∑ e, |g e|).toNat, ?_⟩
  have hall : ∀ e, 0 ≤ (g + (∑ e, |g e|).toNat • allE n d) e := by
    intro e
    have h1 : |g e| ≤ ∑ e, |g e| :=
      Finset.single_le_sum (f := fun e => |g e|) (fun _ _ => abs_nonneg _) (Finset.mem_univ e)
    have h2 : ((∑ e, |g e|).toNat : ℤ) = ∑ e, |g e| :=
      Int.toNat_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    have h3 := neg_abs_le (g e)
    rw [Pi.add_apply, Pi.smul_apply, allE_apply, nsmul_eq_mul, mul_one, h2]
    linarith
  exact ⟨fun _ => hall _, fun _ _ => hall _, Finset.sum_nonneg fun _ _ => hall _⟩

theorem injective_of_isBaseChange {A B M N : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] [Module.Flat A M] [AddCommGroup N] [Module A N] [Module B N]
    [IsScalarTower A B N] {f : M →ₗ[A] N} (hf : IsBaseChange B f)
    (hinj : Function.Injective (algebraMap A B)) : Function.Injective f := by
  have h2 := Module.Flat.rTensor_preserves_injective_linearMap (M := M) (Algebra.linearMap A B) hinj
  intro x y hxy
  have h3 : (1 : B) ⊗ₜ[A] x = (1 : B) ⊗ₜ[A] y := by
    apply hf.equiv.injective
    simp [IsBaseChange.equiv_tmul, hxy]
  have h4 : (1 : A) ⊗ₜ[A] x = (1 : A) ⊗ₜ[A] y := by
    apply h2
    simpa using h3
  simpa using congrArg (TensorProduct.lid A M) h4

theorem omMap_incl_injective : ∀ {K : Type} [Field K] {n d : ℕ} (S : Finset (Fin d)) (a : ℕ),
    Function.Injective (omMap (K := K) (incl (le_top : (cone S : AddSubmonoid (Gam n d)) ≤ ⊤)) a) := by
  intro K _ n d S a
  letI : Algebra (R0 K n d S) (Lr K n d) :=
    (incl (K := K) (le_top : (cone S : AddSubmonoid (Gam n d)) ≤ ⊤)).toRingHom.toAlgebra
  haveI : IsScalarTower K (R0 K n d S) (Lr K n d) :=
    IsScalarTower.of_algHom (incl (K := K) (le_top : (cone S : AddSubmonoid (Gam n d)) ≤ ⊤))
  haveI hl : IsLocalization.Away (mon K (allE n d) (allE_mem S)) (Lr K n d) :=
    Away.isLocalization_away le_top (allE n d) (allE_mem S) (AddSubmonoid.mem_top _)
      (fun g _ => exists_add_nsmul_mem S g)
  haveI : Algebra.FormallyEtale (R0 K n d S) (Lr K n d) :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers (mon K (allE n d) (allE_mem S)))
  have hb := KaehlerDifferential.isBaseChange_of_formallyEtale K (R0 K n d S) (Lr K n d)
  have hE := GlobalTheory.TopForm.isBaseChange_exteriorPower hb a
  haveI : Module.Free (R0 K n d S) Ω[R0 K n d S⁄K] := GlobalTheory.T.kaehler_free_cone_ring S
  have hinj := injective_of_isBaseChange hE (Away.incl_injective le_top)
  have heq : ∀ ω, omMap (K := K) (incl (le_top : (cone S : AddSubmonoid (Gam n d)) ≤ ⊤)) a ω =
      exteriorPowerMapOver (Lr K n d) a (KaehlerDifferential.map K K (R0 K n d S) (Lr K n d)) ω := by
    intro ω
    have hs : ω ∈ (⊤ : Submodule (R0 K n d S) (Om K (R0 K n d S) a)) := trivial
    rw [← exteriorPower.ιMulti_span] at hs
    induction hs using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨v, rfl⟩ := hx
      rw [omMap_ιMulti, exteriorPowerMapOver_ιMulti]
    | zero => simp
    | add x y _ _ hx hy => simp only [map_add (f := _), hx, hy]
    | smul c x _ hx =>
      rw [omMap_smul, hx, map_smul]
      exact algebraMap_smul (Lr K n d) c _
  intro x y hxy
  exact hinj (by rw [← heq, ← heq, hxy])

end GlobalTheory.CompanionTheory.SurjectionOntoH4.OmlInj
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeFormsMapInjectiveStatement
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cone_forms_map_injective : ∀ {K : Type} [Field K] {n d : ℕ} (S : Finset (Fin d)) (a : ℕ), Function.Injective (omMap (K := K) (incl (le_top : (cone S : AddSubmonoid (Gam n d)) ≤ ⊤)) a) := by
  first | exact @GlobalTheory.CompanionTheory.SurjectionOntoH4.OmlInj.omMap_incl_injective | exact GlobalTheory.CompanionTheory.SurjectionOntoH4.OmlInj.omMap_incl_injective | (intros; apply GlobalTheory.CompanionTheory.SurjectionOntoH4.OmlInj.omMap_incl_injective <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WedgeFunctionalTwoFormNaturality
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.HodgeTwoForm

section Generic

variable {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] {n : ℕ}

theorem sum_pairs {N : Type} [AddCommMonoid N] (g : Fin n → Fin n → N) (hd : ∀ i, g i i = 0) :
    ∑ i, ∑ j, g i j = ∑ i, ∑ j ∈ Finset.Ioi i, (g i j + g j i) := by
  have h1 : ∀ i, ∑ j, g i j = ∑ j ∈ Finset.Ioi i, g i j + ∑ j ∈ Finset.Iio i, g i j := by
    intro i
    have e : (Finset.univ : Finset (Fin n)) = Finset.Ioi i ∪ ({i} ∪ Finset.Iio i) := by
      ext j; simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_Ioi, Finset.mem_singleton,
        Finset.mem_Iio, true_iff]; omega
    rw [e, Finset.sum_union, Finset.sum_union]
    · simp [hd]
    · simp
    · rw [Finset.disjoint_left]; intro j; simp only [Finset.mem_Ioi, Finset.mem_union,
        Finset.mem_singleton, Finset.mem_Iio]; omega
  simp_rw [h1, Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_comm' (by simp)

def L2 (L : Fin n → Module.Dual A M) (i j : Fin n) : ⋀[A]^2 M →ₗ[A] A :=
  exteriorPower.pairingDual A M 2 (exteriorPower.ιMulti A 2 ![L i, L j])

theorem wedge_functional_iota_multi (L : Fin n → Module.Dual A M) (i j : Fin n) (a b : M) :
    L2 L i j (exteriorPower.ιMulti A 2 ![a, b]) = L i a * L j b - L j a * L i b := by
  rw [L2, exteriorPower.pairingDual_ιMulti_ιMulti, Matrix.det_fin_two]
  simp

def wb : M →ₗ[A] M →ₗ[A] ⋀[A]^2 M :=
  LinearMap.mk₂ A (fun a b ↦ exteriorPower.ιMulti A 2 ![a, b])
    (fun _ _ _ ↦ Subtype.ext (by simp [ExteriorAlgebra.ιMulti_apply, add_mul]))
    (fun _ _ _ ↦ Subtype.ext (by simp [ExteriorAlgebra.ιMulti_apply]))
    (fun _ _ _ ↦ Subtype.ext (by simp [ExteriorAlgebra.ιMulti_apply, mul_add]))
    (fun _ _ _ ↦ Subtype.ext (by simp [ExteriorAlgebra.ιMulti_apply]))

theorem wb_apply (a b : M) : wb (A := A) a b = exteriorPower.ιMulti A 2 ![a, b] := rfl

theorem wb_self (a : M) : wb (A := A) a a = 0 :=
  Subtype.ext (by simp [wb_apply, ExteriorAlgebra.ιMulti_apply])

theorem wb_swap (a b : M) : wb (A := A) b a = -wb a b :=
  Subtype.ext (by
    simpa [wb_apply, ExteriorAlgebra.ιMulti_apply] using
      eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap (R := A) b a))

theorem eq_two (v : Fin 2 → M) : v = ![v 0, v 1] := by
  ext i; fin_cases i <;> rfl

theorem wb_expand (e : Fin n → M) (L : Fin n → Module.Dual A M) (h : ∀ x, x = ∑ i, L i x • e i)
    (a b : M) :
    wb (A := A) a b = ∑ i, ∑ j ∈ Finset.Ioi i, (L i a * L j b - L j a * L i b) • wb (A := A) (e i) (e j) := by
  have h1 : wb (A := A) a b = ∑ i, ∑ j, (L i a * L j b) • wb (A := A) (e i) (e j) := by
    conv_lhs => rw [h a, h b]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_smul,
      Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    rw [mul_comm]
  rw [h1, sum_pairs _ (fun i ↦ by rw [wb_self, smul_zero])]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  rw [wb_swap (e i) (e j), sub_smul, smul_neg, sub_eq_add_neg]

theorem expand (e : Fin n → M) (L : Fin n → Module.Dual A M) (h : ∀ x, x = ∑ i, L i x • e i)
    (z : ⋀[A]^2 M) :
    z = ∑ i, ∑ j ∈ Finset.Ioi i, L2 L i j z • wb (A := A) (e i) (e j) := by
  have hz : z ∈ Submodule.span A (Set.range (exteriorPower.ιMulti A 2 (M := M))) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    have e1 : exteriorPower.ιMulti A 2 v = wb (A := A) (v 0) (v 1) := by rw [wb_apply, ← eq_two]
    rw [e1]
    conv_lhs => rw [wb_expand e L h]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    rw [wb_apply (v 0), wedge_functional_iota_multi]
  | zero => simp
  | add x y _ _ hx hy =>
    conv_lhs => rw [hx, hy]
    simp only [map_add (f := _), add_smul, Finset.sum_add_distrib]
  | smul c x _ hx =>
    conv_lhs => rw [hx]
    simp only [map_smul, smul_eq_mul, mul_smul, Finset.smul_sum]

end Generic

section Forms

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

def wedgeAt (T : C) : Glob1 F [⋀^Fin 2]→ₗ[R] Om R (F.obj T) 2 where
  toMultilinearMap := ((exteriorPower.ιMulti (F.obj T) 2 (M := Ω[F.obj T⁄R])).toMultilinearMap.restrictScalars
    R).compLinearMap fun _ ↦ evForm F T
  map_eq_zero_of_eq' v i j hv hij :=
    (exteriorPower.ιMulti (F.obj T) 2 (M := Ω[F.obj T⁄R])).map_eq_zero_of_eq _
      (congrArg (evForm F T) hv) hij

def nu : ⋀[R]^2 (Glob1 F) →ₗ[R] W0 F 2 :=
  LinearMap.pi fun T ↦ exteriorPower.alternatingMapLinearEquiv (wedgeAt F T)

theorem nu_ιMulti (a b : Glob1 F) (T : C) :
    nu F (exteriorPower.ιMulti R 2 ![a, b]) T = wedge R _ (a.1 T) (b.1 T) := by
  rw [wedge_eq_ιMulti]
  change exteriorPower.alternatingMapLinearEquiv (wedgeAt F T) _ = _
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  change exteriorPower.ιMulti (F.obj T) 2 (fun i ↦ evForm F T (![a, b] i)) = _
  congr 1
  ext i; fin_cases i <;> rfl

variable {F}

def Lf (hP : Par F) (l : Module.Dual R (Glob1 F)) (T : C) : Module.Dual (F.obj T) Ω[F.obj T⁄R] :=
  (hP T).lift (Algebra.linearMap R (F.obj T) ∘ₗ l)

theorem Lf_ev (hP : Par F) (l : Module.Dual R (Glob1 F)) (T : C) (x : Glob1 F) :
    Lf hP l T (evForm F T x) = algebraMap R (F.obj T) (l x) :=
  (hP T).lift_eq _ x

theorem form_pullback_evaluation {T T' : C} (φ : T ⟶ T') (x : Glob1 F) : p1 F φ (evForm F T x) = evForm F T' x :=
  (x.2 φ).symm

theorem linear_form_extension_naturality (hP : Par F) (l : Module.Dual R (Glob1 F)) {T T' : C} (φ : T ⟶ T')
    (α : Ω[F.obj T⁄R]) : Lf hP l T' (p1 F φ α) = mp F φ (Lf hP l T α) := by
  refine (hP T).inductionOn α (fun x ↦ ?_) (fun b y hy ↦ ?_) (fun y z hy hz ↦ ?_)
  · rw [form_pullback_evaluation, Lf_ev, Lf_ev, AlgHom.commutes]
  · rw [oneFormsMapOfFunctorMorphism_smul, map_smul, hy, map_smul, smul_eq_mul, smul_eq_mul, map_mul]
  · simp only [map_add (f := _), hy, hz]

theorem Lf_expand (hP : Par F) {n : ℕ} (w : Fin n → Glob1 F) (l : Fin n → Module.Dual R (Glob1 F))
    (h : ∀ x, x = ∑ i, l i x • w i) (T : C) (α : Ω[F.obj T⁄R]) :
    α = ∑ i, Lf hP (l i) T α • evForm F T (w i) := by
  refine (hP T).inductionOn α (fun x ↦ ?_) (fun b y hy ↦ ?_) (fun y z hy hz ↦ ?_)
  · conv_lhs => rw [h x]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Lf_ev, algebraMap_smul]
  · conv_lhs => rw [hy]
    simp only [map_smul, smul_eq_mul, mul_smul, Finset.smul_sum]
  · conv_lhs => rw [hy, hz]
    simp only [map_add (f := _), add_smul, Finset.sum_add_distrib]

theorem wedge_functional_two_form_naturality (hP : Par F) {n : ℕ} (l : Fin n → Module.Dual R (Glob1 F)) (i j : Fin n) {T T' : C}
    (φ : T ⟶ T') (z : Om R (F.obj T) 2) :
    L2 (fun i ↦ Lf hP (l i) T') i j (pOm F 2 φ z) = mp F φ (L2 (fun i ↦ Lf hP (l i) T) i j z) := by
  have hz : z ∈ Submodule.span (F.obj T) (Set.range (exteriorPower.ιMulti (F.obj T) 2 (M := Ω[F.obj T⁄R]))) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    rw [eq_two v, ← wedge_eq_ιMulti, pOm_wedge, wedge_eq_ιMulti, wedge_eq_ιMulti, wedge_functional_iota_multi, wedge_functional_iota_multi]
    simp only [linear_form_extension_naturality, map_sub, map_mul]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add (f := _), hx, hy]
  | smul c x _ hx => simp only [pOm_smul, map_smul, hx, smul_eq_mul, map_mul]

theorem wedge_functional_constant_on_image (hP : Par F) {n : ℕ} (l : Fin n → Module.Dual R (Glob1 F)) (i j : Fin n) (T : C)
    (t : ⋀[R]^2 (Glob1 F)) :
    L2 (fun i ↦ Lf hP (l i) T) i j (nu F t T) = algebraMap R (F.obj T) (L2 l i j t) := by
  have ht : t ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R 2 (M := Glob1 F))) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction ht using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    rw [eq_two v, nu_ιMulti, wedge_eq_ιMulti, wedge_functional_iota_multi, wedge_functional_iota_multi]
    change Lf hP (l i) T (evForm F T _) * Lf hP (l j) T (evForm F T _) -
      Lf hP (l j) T (evForm F T _) * Lf hP (l i) T (evForm F T _) = _
    simp only [Lf_ev, map_sub, map_mul]
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [map_add (f := _), Pi.add_apply, hx, hy]
  | smul c x _ hx =>
    simp only [map_smul, Pi.smul_apply, hx, smul_eq_mul, map_mul]
    rw [← algebraMap_smul (F.obj T) c, map_smul, hx, smul_eq_mul]

end Forms

theorem twoFormCohSt : TwoFormCohSt := by
  intro R _ C _ F ⟨hS, hP, hF, hPr⟩
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R (Glob1 F)
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  let w : Fin n → Glob1 F := fun i ↦ f (Pi.single i 1)
  let l : Fin n → Module.Dual R (Glob1 F) := fun i ↦ LinearMap.proj i ∘ₗ s
  have hdual : ∀ x, x = ∑ i, l i x • w i := by
    intro x
    have h1 : f (s x) = x := LinearMap.congr_fun hs x
    conv_lhs => rw [← h1, pi_eq_sum_univ' (s x)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [w, l, map_sum, map_smul]
  have hexp : ∀ (T : C) (z : Om R (F.obj T) 2), z = ∑ i, ∑ j ∈ Finset.Ioi i,
      L2 (fun i ↦ Lf hP (l i) T) i j z • wedge R _ (evForm F T (w i)) (evForm F T (w j)) := by
    intro T z
    conv_lhs => rw [expand (fun i ↦ evForm F T (w i)) (fun i ↦ Lf hP (l i) T)
      (Lf_expand hP w l hdual T) z]
    simp only [wb_apply, wedge_eq_ιMulti]
  refine ⟨nu F, nu_ιMulti F, ?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro t ht
    have h0 : ∀ i j, L2 l i j t = 0 := by
      intro i j
      apply hS.2
      rw [map_zero]
      funext T
      have := wedge_functional_constant_on_image hP l i j T t
      rw [ht] at this
      simpa using this.symm
    rw [expand w l hdual t]
    simp [h0]
  · intro u hu
    have hc : ∀ i j, ∃ r : R, ∀ T, algebraMap R (F.obj T) r = L2 (fun i ↦ Lf hP (l i) T) i j (u T) := by
      intro i j
      have hz : d0 F (fun T ↦ L2 (fun i ↦ Lf hP (l i) T) i j (u T)) = 0 := by
        funext T T' φ
        rw [amitsur_d0_apply, hu T T' φ, wedge_functional_two_form_naturality, sub_self]
        rfl
      obtain ⟨r, hr⟩ := (hS.1 _).1 hz
      exact ⟨r, fun T ↦ congrFun hr T⟩
    choose r hr using hc
    refine ⟨∑ i, ∑ j ∈ Finset.Ioi i, r i j • wb (A := R) (w i) (w j), ?_⟩
    funext T
    conv_rhs => rw [hexp T (u T)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, wb_apply, nu_ιMulti]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← hr, algebraMap_smul]
    rfl

end GlobalTheory.CompanionTheory.HodgeTwoForm
end
end
